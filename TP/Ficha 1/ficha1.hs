{-# LANGUAGE InstanceSigs #-}

import qualified Control.Monad.State.Strict as St
import           Control.Monad              (when)

import qualified Data.Map   as M
import qualified Data.Maybe as Maybe
import           Data.List ( intercalate ) 

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

type State = M.Map Var Z

showState :: State -> String
showState st =
    let pairs = M.toList st
        helper :: (Var, Z) -> String
        helper (var, num) = var ++ " := " ++ show num
    in intercalate "; " $ map helper pairs

newtype State' = St {
    getState :: State
}
    deriving Eq

instance Show State' where
    show = showState . getState

getSt :: State -> Var -> Z
getSt st var = Maybe.fromMaybe 0 (M.lookup var st)

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

-- Alínea b) ii)
stUpdate :: State -> Var -> Z -> State
stUpdate st var v = M.insert var v st

-- Alínea b) iii)
evalNS :: State -> Stm -> State
evalNS st (var `Assign` a) =
    let n = arithEval a st
    in stUpdate st var n
evalNS st Skip = st
evalNS st (c1 `Comp` c2) =
    let st' = evalNS st c1
    in evalNS st' c2
evalNS st (IfThenElse b c1 c2)
    | boolEval b st = evalNS st c1
    | otherwise     = evalNS st c2
evalNS st (WhileDo b c)
    | boolEval b st =
        let st' = evalNS st c
        in evalNS st' (WhileDo b c)
    | otherwise     = st

-- Igual a função evalNS, mas com uso da mónade State.
evalNS2 :: State -> Stm -> State
evalNS2 st stm = St.execState (helper stm) st
    where
        helper :: Stm -> St.State State ()
        helper (var `Assign` a) = do
            st <- St.get
            let n = arithEval a st
            St.modify (\s -> stUpdate s var n)
        helper Skip = do
            return ()
        helper (c1 `Comp` c2) = do
            s1 <- helper c1
            helper c2
        helper (IfThenElse b c1 c2) = do
            s <- St.get
            if boolEval b s
                then helper c1
                else helper c2
        helper (WhileDo b c) = do
            s <- St.get
            when (boolEval b s) $ do
                    s' <- helper c
                    helper (WhileDo b c)

-- Ficha 2

stepSOS :: State -> Stm -> Either State (Stm, State)
stepSOS st stm = case stm of
    x `Assign` ae ->
        let n = arithEval ae st
        in Left $ stUpdate st x n
    Skip -> Left st
    stm1 `Comp` stm2 -> case stepSOS st stm1 of
        Left st' -> Right (stm2, st')
        Right (stm1', st') -> Right (stm1' `Comp` stm2, st')
    IfThenElse be stm1 stm2 -> if boolEval be st
        then Right (stm1, st)
        else Right (stm2, st)
    WhileDo be stm' -> Right (IfThenElse be (stm' `Comp` WhileDo be stm') Skip, st)

-- Devolve a transição após o número de passos de execução pedido, se for possível,
-- numa lista com todas as transições que lhe precederam.
nstepsSOS :: State -> Stm -> Integer -> [Either State' (Stm, State')]
nstepsSOS st stm n
    | n <= 0 = []
    | otherwise = case stepSOS st stm of
        Left s -> [Left $ St s]
        Right (stm', st') -> Right (stm', St st') : nstepsSOS st' stm' (n - 1)

-- Imprimir uma configuração numa string legível
-- e.g. mapM_ (putStr . helper) $ nstepsSOS ex1State fact 10
helper :: Either State' (Stm, State') -> String
helper (Left st) = "Left: " ++ show st ++ ";\n"
helper (Right (stm, st)) =
    "Right: " ++
    show stm ++ ";\n" ++
    show st ++ ";\n"

evalSOS :: State -> Stm -> State'
evalSOS st stm = St $ helper (Right (stm, st))
    where helper :: Either State (Stm, State) -> State
          helper (Left st) = st
          helper (Right (stm', st')) =
              case stepSOS st' stm' of
                  Left st''           -> st''
                  Right (stm'', st'') -> helper (Right (stm'', st''))


-- Exemplos de aplicação da ficha 1.

ex1State :: State
ex1State = M.fromList [("n", 3), ("x", 3), ("y", 2)]

swap :: Stm
swap = Comp (Comp c1 c2) c3
    where
        c1 = Assign "n" (Var "x")
        c2 = Assign "x" (Var "y")
        c3 = Assign "y" (Var "n")

minProg :: Stm
minProg = IfThenElse b1 if2 if3
    where b1 = Lt (Var "x") (Var "y")
          b2 = Lt (Var "x") (Var "z")
          b3 = Lt (Var "y") (Var "z")
          if3 = IfThenElse b3 (Assign "m" (Var "y")) (Assign "m" (Var "z"))
          if2 = IfThenElse b2 (Assign "m" (Var "x")) (Assign "m" (Var "z"))

expProg :: Stm
expProg = Comp assgn while
    where
        assgn = Assign "r" (Num 1)
        while = WhileDo bexp whileStm
        bexp = Var "y" `Ge` Num 1
        whileStm = Comp
            (Assign "r" (Mul (Var "r") (Var "x")))
            (Assign "y" (Minus (Var "y") (Num 1)))

fact :: Stm
fact = Comp assgn while
    where
        assgn = Assign "f" (Num 1)
        while = WhileDo bexp whileStm
        bexp = Var "n" `Ge` Num 1
        whileStm = Comp
            (Assign "f" (Mul (Var "f") (Var "n")))
            (Assign "n" (Minus (Var "n") (Num 1)))