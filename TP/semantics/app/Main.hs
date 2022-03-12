module Main where

import qualified Data.Map as M

import Core (Stm (..), State, Aexp (..), Bexp (..))
import NaturalSemantics
import StructOpSemantics

main :: IO ()
main = putStrLn "Hello, Haskell!"

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