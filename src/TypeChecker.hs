module TypeChecker (
    check,
) where

import AST
import Algebra.Lattice
import Control.Monad.State.Lazy
import Data.Map qualified as M
import StateEither

import Data.List.NonEmpty qualified as NE


elookup :: VarLab -> M.Map VarLab a -> StateEither [String] a
elookup varlab env = case varlab of 
        Left v -> 
            case M.lookup (Left v) env of
            Just t -> return t
            Nothing -> do
                let msg = "Variable " ++ show v ++ " not found in environment"
                modify (++ [msg])
                fail msg
        Right l -> 
            case M.lookup (Right l) env of
            Just t -> return t
            Nothing -> do
                let msg = "Label " ++ show l ++ " not found in environment"
                modify (++ [msg])
                fail msg

sat :: Bool -> String -> StateEither [String] ()
sat True _ = return ()
sat False e = do
    modify (++ [e])
    fail e

trace :: String -> StateEither [String] a -> StateEither [String] a
trace s m = do
    t <- get
    put $ t ++ [s]
    a <- m
    put t
    return a

check :: Env -> LevelT -> Expr -> StateEither [String] LevelTEnv
check env pc expr = case expr of
    (LetInf x e) -> trace ("LetInf: " ++ show expr) $ do
        l :@ eff :|> _ <- check env pc e
        case l of
            t1 :-> (t2 :@ eff') -> do
                sat (pc == LH Low) "NotSat: pc == LH Low"
                return $ LH Low :@ eff :|> M.insert (Left x) (t1 :-> (t2 :@ eff')) env
            RefLH l' -> do
                sat (pc `joinLeq` LH l') "NotSat: pc <= LH l'"
                return $ LH Low :@ (LH l' /\ eff) :|> M.insert (Left x) (RefLH l') env
            Environment l' -> trace ("PC:" ++ show pc ++ " rec: "++ show (Environment l') ++ " Eff: " ++ show eff) $ do
                let recordType = recordChecker (Environment l')
                sat (pc `joinLeq` recordType) "NotSat: pc <= l"
                sat (pc `joinLeq` eff) "NotSat: pc <= t1, TEST"
                return $ LH Low :@ (eff /\ pc) :|> M.insert (Left x) (Environment l') env
            t1 -> do
                sat (t1 `elem` [LH Low, LH High]) "NotSat: t1 `elem` [LH Low, LH High]"
                sat (pc `joinLeq` t1) "NotSat: pc <= t1"
                return $ LH Low :@ (t1 /\ eff) :|> M.insert (Left x) t1 env
    (Let x t1 e) -> trace ("Let: " ++ show expr) $ do
        t2 :@ t3 :|> _ <- check env pc e
        sat (t1 `elem` [LH Low, LH High]) "NotSat: t1 `elem` [LH Low, LH High]"
        sat (t2 `elem` [LH Low, LH High]) "NotSat: t2 `elem` [LH Low, LH High]"
        sat (t2 `joinLeq` t1) "NotSat: t2 <= t1"
        sat (pc `joinLeq` t1) "NotSat: pc <= t1"
        return $ LH Low :@ (t1 /\ t3) :|> M.insert (Left x) t1 env
    (IfThenElse e1 e2 e3) -> trace ("IfThenElse: " ++ show expr) $ do
        l1 :@ eff1 :|> _ <- check env pc e1
        sat (l1 `elem` [LH Low, LH High]) "NotSat: l1 `elem` [LH Low, LH High]"
        let pc' = l1 \/ pc
        l2 :@ eff2 :|> _ <- check env pc' e2
        l3 :@ eff3 :|> _ <- check env pc' e3
        return $ joins [l1, l2, l3] :@ meets [eff1, eff2, eff3] :|> env
    (Seq e1 e2) -> trace ("Seq: " ++ show expr) $ do
        _ :@ eff1 :|> env1 <- check env pc e1
        l2 :@ eff2 :|> env2 <- check env1 pc e2
        return $ l2 :@ (eff1 /\ eff2) :|> env2
    (While e1 e2) -> trace ("While: " ++ show expr) $ do
        l1 :@ eff1 :|> _ <- check env pc e1
        sat (l1 `elem` [LH Low, LH High]) "NotSat: l1 `elem` [LH Low, LH High]"
        let pc' = l1 \/ pc
        _ :@ eff2 :|> _ <- check env pc' e2
        return $ LH Low :@ (eff1 /\ eff2) :|> env
    (For x e1 e2 e3) -> trace ("For: " ++ show expr) $ do
        l1 :@ eff1 :|> _ <- check env pc e1
        sat (l1 `elem` [LH Low, LH High]) "NotSat: l1 `elem` [LH Low, LH High]"
        l2 :@ eff2 :|> _ <- check env pc e2
        sat (l2 `elem` [LH Low, LH High]) "NotSat: l2 `elem` [LH Low, LH High]"
        let pc' = joins [l1, l2, pc]
        _ :@ eff3 :|> _ <- check (M.insert (Left x) pc' env) pc' e3
        return $ LH Low :@ meets [eff1, eff2, eff3] :|> env
    (Var x) -> trace ("Var: " ++ show expr) $ do
        l <- elookup (Left x :: VarLab) env
        return $ l :@ Empty :|> env
    (B _) -> trace ("Bool: " ++ show expr) $ do
        return $ LH Low :@ Empty :|> env
    (N _) -> trace ("Num: " ++ show expr) $ do
        return $ LH Low :@ Empty :|> env
    Unit -> trace ("Unit: " ++ show expr) $ do
        return $ LH Low :@ Empty :|> env
    (Abs x l e) -> trace ("Abs: " ++ show expr) $ do
        l' :@ eff' :|> _ <- check (M.insert (Left x) l env) pc e
        sat (pc `joinLeq` eff') "NotSat: pc <= eff'"
        return $ (l :-> (l' :@ eff')) :@ eff' :|> env
    (App e1 e2) -> trace ("App: " ++ show expr) $ do
        l1 :@ eff1 :|> _ <- check env pc e1
        l2 :@ eff2 :|> _ <- check env pc e2
        case l1 of
            (l1' :-> (l2' :@ eff3)) -> do
                let eff = meets [eff1, eff2, eff3]
                sat (pc `joinLeq` eff) "NotSat: eff >= pc"
                sat (l1' == l2) "NotSat: l1' == l2"
                return $ l2' :@ eff :|> env
            t -> fail $ "App: not a function type: " ++ show t
    (BOA _ e1 e2) -> trace ("BO: " ++ show expr) $ do
        l1 :@ eff1 :|> _ <- check env pc e1
        l2 :@ eff2 :|> _ <- check env pc e2
        sat (l1 `elem` [LH Low, LH High]) "NotSat: l1 `elem` [LH Low, LH High]"
        sat (l2 `elem` [LH Low, LH High]) "NotSat: l2 `elem` [LH Low, LH High]"
        return $ (l1 \/ l2) :@ (eff1 /\ eff2) :|> env
    (BOL _ e1 e2) -> trace ("BO: " ++ show expr) $ do
        l1 :@ eff1 :|> _ <- check env pc e1
        l2 :@ eff2 :|> _ <- check env pc e2
        case l1 of
            LH _ -> do sat (l2 `elem` [LH Low, LH High]) "NotSat: l2 `elem` [LH Low, LH High]"
            Environment _ -> do sat (l2 == Environment env) "NotSat: l2 `elem` [Environment env]"
            RefLH _ -> do  sat (l2 `elem` [RefLH Low, RefLH High]) "NotSat: l2 `elem` [RefLH Low, RefLH High]"
            Empty -> do sat (l2 `elem` [Empty]) "NotSat: l2 `elem` [Empty]"
            _ -> error ("Type of e1 is not valid in logic operation")
        return $ (l1 \/ l2) :@ (eff1 /\ eff2) :|> env
    (Ref e) -> trace ("Ref: " ++ show expr) $ do
        (LH l) :@ eff :|> _ <- check env pc e
        sat (l `elem` [Low, High]) "NotSat: l `elem` [Low, High]"
        return $ RefLH l :@ eff :|> env
    (Deref x) -> trace ("Deref: " ++ show expr) $ do
        (RefLH l) <- elookup (Left x :: VarLab) env
        return $ LH l :@ Empty :|> env
    (Assign x e) -> trace ("Assign: " ++ show expr) $ do
        (RefLH l) <- elookup (Left x :: VarLab) env
        l' :@ eff' :|> _ <- check env pc e
        sat (LH l == l') "NotSat: LH l == l'"
        sat (pc `joinLeq` LH l) "NotSat: pc <= LH l"
        return $ LH Low :@ (LH l /\ eff') :|> env
    (IfThen {}) -> error "IfThen: not implemented"
    (Rec expression) -> trace ("Record: " ++ show (Rec expression)) $ do
        let listFields = NE.toList expression

        let loop gamma eff [] = return (Environment gamma, eff)
            loop gamma eff (Right (label_i, levelt_i, expr_i) : rest) = do
                t_i :@ eff_i :|> _ <- check env pc expr_i
                case t_i of
                    -- If it's a nested record (Environment), wrap it as-is
                    Environment _ -> do
                        error "A record cannot be explicitly typed"

                    -- Otherwise, treat it as a regular value and enforce pc <= t_i
                    _ -> do
                        sat (levelt_i `elem` [LH Low, LH High]) "NotSat: levelt_i `elem` [LH Low, LH High]"
                        sat (t_i`joinLeq` levelt_i) "NotSat levelt_i <= t_i"
                        sat (pc `joinLeq` t_i) $
                            "NotSat pc <= t_i, t_i: " ++ show t_i ++ ", pc: " ++ show pc ++ ", expr: " ++ show expr_i
                        let newGamma = M.insert (Right label_i) levelt_i gamma
                        let newEff = eff_i /\ eff
                        loop newGamma newEff rest
            loop gamma eff (Left (label_i, expr_i) : rest) = do
                t_i :@ eff_i :|> _ <- check env pc expr_i

                case t_i of
                    -- If it's a nested record (Environment), wrap it as-is
                    Environment subEnv -> do
                        let newGamma = M.insert (Right label_i) (Environment subEnv) gamma
                        let newEff = eff_i /\ eff
                        loop newGamma newEff rest

                    -- Otherwise, treat it as a regular value and enforce pc <= t_i
                    _ -> do
                        sat (pc `joinLeq` t_i) $
                            "NotSat pc <= t_i, t_i: " ++ show t_i ++ ", pc: " ++ show pc ++ ", expr: " ++ show expr_i
                        let newGamma = M.insert (Right label_i) t_i gamma
                        let newEff = eff_i /\ eff
                        loop newGamma newEff rest

        (envResult, effResult) <- loop M.empty Empty listFields
        return $ envResult :@ effResult :|> env
    (RecField e l) -> trace ("Record Field: " ++ show e ++ "." ++ show l) $ do
        Environment gamma :@ eff :|> _ <- check env pc e
        
        t <- elookup (Right l :: VarLab) gamma
        trace ("Looked up field '" ++ show l ++ "' with type: " ++ show t) $ do
            sat (pc `joinLeq` eff) "NotSat pc <= eff"
            return $ t :@ eff :|> env

         

    (Proj {}) -> error "Proj: not implemented"
    (Loc _) -> error "Loc: not implemented"
