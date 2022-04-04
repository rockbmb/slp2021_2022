{-# LANGUAGE InstanceSigs #-}
module Core where

import qualified Data.Map   as M
import qualified Data.Maybe as Maybe

import           Data.List (intercalate)

type Z = Integer

type Var = String

data Aexp
    = Num Z
    | Var Var
    | Aexp `Plus` Aexp
    | Aexp `Mul` Aexp
    | Aexp `Minus` Aexp
    deriving Eq

instance Show Aexp where
    show :: Aexp -> String
    show aexp = case aexp of
        Num z -> show z
        Var v -> v
        a1 `Plus` a2 -> show a1 ++ " + " ++ show a2
        a1 `Mul` a2 -> show a1 ++ " * " ++ show a2
        a1 `Minus` a2 -> show a1 ++ " - " ++ show a2

data Bexp
    = T
    | F
    | Aexp `Eq` Aexp
    | Aexp `Le` Aexp
    | Aexp `Lt` Aexp
    | Aexp `Ge` Aexp
    | Not Bexp
    | Bexp `And` Bexp
    | Bexp `Or` Bexp
    deriving Eq

instance Show Bexp where
    show :: Bexp -> String 
    show bexp = "(" ++ helper bexp ++ ")"
        where
            helper bexp = case bexp of
                T -> "true"
                F -> "false"
                ae `Eq` ae' -> show ae ++ " == " ++ show ae'
                ae `Le` ae' -> show ae ++ " <= " ++ show ae'
                ae `Lt` ae' -> show ae ++ " < " ++ show ae'
                ae `Ge` ae' -> show ae ++ " >= " ++ show ae'
                Not be -> "not (" ++ show be ++ ")"
                be `And` be' -> show be ++ " && " ++ show be'
                be `Or` be' -> show be ++ " || " ++ show be'

type State = M.Map Var Z

getSt :: State -> Var -> Z
getSt st var = Maybe.fromMaybe 0 (M.lookup var st)

-- Alínea b) ii)
stUpdate :: State -> Var -> Z -> State
stUpdate st var v = M.insert var v st

showState :: State -> String
showState st =
    let pairs = M.toList st
        helper :: (Var, Z) -> String
        helper (var, num) = var ++ " := " ++ show num
    in intercalate "; " $ map helper pairs

subAexp :: Var -> Aexp -> Aexp -> Aexp
subAexp y a0 a@(Num _) = a
subAexp y a0 (Var x)
    | x == y = a0
    | otherwise = Var x
subAexp y a0 (Plus a1 a2) = Plus (subAexp y a0 a1) (subAexp y a0 a2)
subAexp y a0 (Mul a1 a2) = Mul (subAexp y a0 a1) (subAexp y a0 a2)
subAexp y a0 (Minus a1 a2) = Minus (subAexp y a0 a1) (subAexp y a0 a2)

subBexp :: Var -> Aexp -> Bexp -> Bexp
subBexp y a0 a = case a of
    T -> T
    F -> F
    (Eq a1 a2) -> Eq (subAexp y a0 a1) (subAexp y a0 a2)
    (Le a1 a2) -> Le (subAexp y a0 a1) (subAexp y a0 a2)
    (Lt a1 a2) -> Lt (subAexp y a0 a1) (subAexp y a0 a2)
    (Ge a1 a2) -> Ge (subAexp y a0 a1) (subAexp y a0 a2)
    (Not b1) -> Not (subBexp y a0 b1)
    (And b1 b2) -> And (subBexp y a0 b1) (subBexp y a0 b2)
    (Or b1 b2) -> Or (subBexp y a0 b1) (subBexp y a0 b2)

arithEval :: Aexp -> (State -> Z)
arithEval a st = case a of
    Num n -> n
    Var x -> getSt st x
    Plus a1 a2 -> arithEval a1 st + arithEval a2 st
    Mul a1 a2 -> arithEval a1 st * arithEval a2 st
    Minus a1 a2 -> arithEval a1 st - arithEval a2 st

boolEval :: Bexp -> (State -> Bool)
boolEval b st = case b of
    T -> True
    F -> False
    Eq a1 a2  -> arithEval a1 st == arithEval a2 st
    Le a1 a2  -> arithEval a1 st <= arithEval a2 st
    Lt a1 a2  -> arithEval a1 st < arithEval a2 st
    Ge a1 a2  -> arithEval a1 st >= arithEval a2 st
    Not b1    -> not (boolEval b1 st)
    And b1 b2 -> boolEval b1 st && boolEval b2 st
    Or b1 b2  -> boolEval b1 st || boolEval b2 st

-- Igual ao tipo State, mas com instância de Show legível.
newtype State' = St {
    getState :: State
} deriving Eq

instance Show State' where
    show = showState . getState

data Stm
    = Var `Assign` Aexp
    | Skip
    | Stm `Comp` Stm
    | IfThenElse Bexp Stm Stm
    | WhileDo Bexp Stm
    deriving (Eq)

instance Show Stm where
    show :: Stm -> String
    show stm = case stm of
        Assign v aexp          -> v ++ " := " ++ show aexp
        Skip                   -> show "skip"
        stm1 `Comp` stm2       -> show stm1 ++ "; " ++ show stm2
        IfThenElse b stm1 stm2 -> "if " ++ show b ++ " then " ++ show stm1 ++ " else " ++ show stm2
        WhileDo b stm          -> "while " ++ show b ++ " do " ++ show stm