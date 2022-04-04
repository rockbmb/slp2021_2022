module NaturalSemantics (
    evalNS,
    evalNS2
) where


import qualified Control.Monad.State.Strict as St
import           Control.Monad              (when)

import qualified Data.Map                   as M

import           Core                       (Aexp(..), Var, Z, Bexp(..), State,
                                             Stm (..), arithEval, boolEval, stUpdate )

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