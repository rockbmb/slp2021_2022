import qualified Control.Monad.State.Strict as St
import           Control.Monad              (when)


import qualified Data.Map   as M
import qualified Data.Maybe as Maybe

type Z = Integer

type Var = String

data Aexp
    = Num Z
    | Var Var
    | Aexp `Plus` Aexp
    | Aexp `Mul` Aexp
    | Aexp `Minus` Aexp
    deriving (Eq, Show)

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
    deriving (Eq, Show)

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