
module AST where

import Algebra.Lattice
import Data.List (intercalate)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M

-- i don't think env needs locations, at least not for now
-- type Env = M.Map (Either Variable Location) LevelT
-- type Env = M.Map Variable LevelT

type Env = M.Map VarLab LevelT

type VarLab = Either Variable Label

data Expr
    = N Int
    | B Bool
    | Unit
    | Var Variable
    | App Expr Expr
    | Abs Variable LevelT Expr
    | Seq Expr Expr
    | Let Variable LevelT Expr
    | LetInf Variable Expr
    | BO BinOper Expr Expr
    -- Rec Variable --||--
    -- | Rec_Field (Label, Expr)
    | Rec (NE.NonEmpty (Label, Expr))
    | Proj Expr Label
    | IfThenElse Expr Expr Expr
    | IfThen Expr Expr
    | While Expr Expr
    | For Variable Expr Expr Expr
    | Loc Location
    | Ref Expr
    | Deref Variable
    | Assign Variable Expr
    deriving (Eq)

instance Show Expr where
    show (N n) = show n
    show (B b) = show b
    show Unit = "()"
    show (Var x) = show x
    show (App e1 e2) = show e1 ++ "(" ++ show e2 ++ ")"
    show (Abs x t e) = "(\\" ++ show x ++ "." ++ show t ++ "->" ++ show e ++ ")"
    show (Seq e1 e2) = show e1 ++ ";" ++ show e2
    show (Let x t e) = "let " ++ show x ++ "." ++ show t ++ " = " ++ show e
    show (LetInf x e) = "let " ++ show x ++ " = " ++ show e
    show (BO op e1 e2) = "(" ++ show e1 ++ " " ++ show op ++ " " ++ show e2 ++ ")"
    show (Rec fs) = "{" ++ intercalate ", " (NE.toList $ NE.map (\(a, b) -> show a ++ " : " ++ show b) fs) ++ "}"
    show (Proj e l) = show e ++ "." ++ show l
    show (IfThenElse e1 e2 e3) = "(if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3 ++ ")"
    show (IfThen e1 e2) = "(if " ++ show e1 ++ " then " ++ show e2 ++ ")"
    show (While e1 e2) = "(while " ++ show e1 ++ " do " ++ show e2 ++ ")"
    show (For x e1 e2 e3) = "for " ++ show x ++ " in " ++ show e1 ++ " to " ++ show e2 ++ " do " ++ show e3
    show (Loc l) = "<" ++ show l ++ ">"
    show (Ref e) = "*" ++ show e
    show (Deref e) = "!" ++ show e
    show (Assign x e) = show x ++ " := " ++ show e

newtype Variable = V String deriving (Eq, Ord)

instance Show Variable where
    show (V x) = x

newtype Location = L Int deriving (Eq)

instance Show Location where
    show (L l) = show l

data Label
    = LabelS String
    | LabelI Int
    deriving (Eq, Ord)

instance Show Label where
    show (LabelS s) = s
    show (LabelI i) = show i

data BinOper = Add | Sub | Mul | Div | Eq
    deriving (Eq)

instance Show BinOper where
    show Add = "+"
    show Sub = "-"
    show Mul = "*"
    show Div = "/"
    show Eq = "=="

data LowHigh = Low | High deriving (Eq)

instance Show LowHigh where
    show Low = "L"
    show High = "H"

data LevelT
    = LH LowHigh
    | RefLH LowHigh
    | LevelT :@ LevelT
    | LevelT :-> LevelT
    | Empty
    | Environment Env
    -- | RecordEnv (M.Map Label LevelT)
    deriving (Eq)

data LevelTEnv = LevelT :|> Env deriving (Eq, Show)

instance Show LevelT where
    show (LH l) = show l
    show (RefLH l) = "*" ++ show l
    show (l1 :-> l2) = show l1 ++ "->" ++ show l2
    show (l1 :@ l2) = show l1 ++ "@" ++ show l2
    show Empty = "()"
    show (Environment env) = show env 

arity :: LevelT -> Int
arity (_ :-> l2) = 1 + arity l2
arity (l1 :@ l2) = arity l1 + arity l2
arity _ = 0

recordChecker :: LevelT -> LevelT
recordChecker (Environment env) =  
    let types = M.elems env
        loop [] = Empty
        loop (t:ts) = case t of
            LH Low -> LH Low
            Environment subEnv -> 
                case recordChecker (Environment subEnv) of
                    LH Low -> LH Low
                    _      -> loop ts
            _ -> loop ts
    in loop types
recordChecker _ = LH High
   

instance Lattice LevelT where
    (Environment env) \/ (LH Low) = 
        if recordChecker (Environment env) == LH Low
            then LH Low
            else LH High
    (Environment _) \/ (LH High) = LH High
    (LH Low) \/ (Environment env) = 
        if recordChecker (Environment env) == LH Low
            then LH Low
            else LH High
    (LH High) \/ (Environment _) = LH High
    (Environment env1) \/ (Environment env2) = 
        recordChecker (Environment env1) \/ recordChecker (Environment env2)
    (LH Low) \/ (LH Low) = LH Low
    (LH Low) \/ (LH High) = LH High
    (LH High) \/ (LH Low) = LH High
    (LH High) \/ (LH High) = LH High
    abs1@(t1 :-> t1') \/ abs2@(t2 :-> t2') =
        if arity abs1 == arity abs2
            then t1 /\ t2 :-> t1' \/ t2'
            else error $ "Cannot join " ++ show abs1 ++ " and " ++ show abs2
    (_ :@ _) \/ _ = error "Cannot join a effect with a type"
    _ \/ (_ :@ _) = error "Cannot join a effect with a type"
    (_ :-> _) \/ _ = error "Cannot join a function with a type"
    _ \/ (_ :-> _) = error "Cannot join a function with a type"
    Empty \/ _ = Empty
    _ \/ Empty = Empty
    (RefLH Low) \/ (RefLH Low) = RefLH Low
    (RefLH High) \/ (RefLH High) = RefLH High
    (RefLH _) \/ _ = error "Cannot join a reference with a type"
    _ \/ (RefLH _) = error "Cannot join a reference with a type"



    (Environment _) /\ (LH Low) = LH Low
    (Environment env) /\ (LH High) = 
        if recordChecker (Environment env) == LH Low
            then LH Low
            else LH High
    (LH Low) /\ (Environment _) = LH Low
    (LH High) /\ (Environment env) = 
        if recordChecker (Environment env) == LH Low
            then LH Low
            else LH High
    (Environment env) /\ Empty = recordChecker (Environment env)
    Empty /\ (Environment env) = recordChecker (Environment env)
    (Environment env1) /\ (Environment env2) = 
        recordChecker (Environment env1) /\ recordChecker (Environment env2)
    (LH Low) /\ (LH Low) = LH Low
    (LH Low) /\ (LH High) = LH Low
    (LH Low) /\ Empty = LH Low
    (LH High) /\ (LH Low) = LH Low
    (LH High) /\ (LH High) = LH High
    (LH High) /\ Empty = LH High
    Empty /\ l@(LH _) = l
    Empty /\ l@(RefLH _) = l
    Empty /\ Empty = Empty
    Empty /\ abs'@(_ :-> _) = abs'
    abs1@(t1 :-> t1') /\ abs2@(t2 :-> t2') =
        if arity abs1 == arity abs2
            then t1 \/ t2 :-> t1' /\ t2'
            else error $ "Cannot meet " ++ show abs1 ++ " and " ++ show abs2
    abs'@(_ :-> _) /\ Empty = abs'
    (RefLH Low) /\ (RefLH Low) = RefLH Low
    (RefLH High) /\ (RefLH High) = RefLH High
    (RefLH _) /\ _ = error "Cannot meet a reference with a type"
    _ /\ (RefLH _) = error "Cannot meet a reference with a type"
    (_ :@ _) /\ _ = error "Cannot meet a effect with a type"
    _ /\ (_ :@ _) = error "Cannot meet a effect with a type"
    (_ :-> _) /\ _ = error "Cannot meet a function with a type"
    _ /\ (_ :-> _) = error "Cannot meet a function with a type"

instance BoundedMeetSemiLattice LevelT where
    top = Empty

instance BoundedJoinSemiLattice LevelT where
    bottom = LH Low -- technically, there is no bottom, but cant be bothered to use Foldable1
