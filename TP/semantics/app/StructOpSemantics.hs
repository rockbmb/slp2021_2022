module StructOpSemantics (
    stepSOS,
    nstepsSOS,
    helperSOS,
    evalSOS
) where

import           Data.List ( intercalate )

import           Core      ( State, Stm(..), State'(St), arithEval, boolEval, stUpdate )

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
-- e.g. mapM_ (putStr . helperSOS) $ nstepsSOS ex1State fact 10
helperSOS :: Either State' (Stm, State') -> String
helperSOS (Left st) = "Left: " ++ show st ++ ";\n"
helperSOS (Right (stm, st)) =
    "Right: " ++
    show stm ++ ";\n" ++
    show st ++ ";\n"

evalSOS :: State -> Stm -> State'
evalSOS st stm = St $ helperSOS (Right (stm, st))
    where helperSOS :: Either State (Stm, State) -> State
          helperSOS (Left st) = st
          helperSOS (Right (stm', st')) =
              case stepSOS st' stm' of
                  Left st''           -> st''
                  Right (stm'', st'') -> helperSOS (Right (stm'', st''))