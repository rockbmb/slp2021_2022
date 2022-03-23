{-# LANGUAGE BangPatterns #-}
module AbstractMachine2 (
    AM2Instr (..),
    EnvStateAM2 (..),

    aexpToAM2Code,
    bexpToAM2Code,

    whileToAM2,
    stepAM2,
    initConfigAM2,
    runStmInAM2
) where

import qualified Control.Monad.State.Strict as St
import qualified Data.Map                   as M

import           Core                       (Aexp (..), Bexp (..), Var, Z, Stm (..), State,
                                             getSt)
import qualified Data.Maybe as Maybe

-- Mapping from variable names to positions in memory.
-- Used during "compilation" of While code to AM1 bytecode.
type Env = M.Map Var Z

type NextAddr = Z

-- Program counter associated with each instruction.
-- Must be positive, starts at 1, each instruction has a unique PC value,
-- and strictly increases by 1 unit with every atomic instruction.
type ProgramCounter = Z

data EnvStateAM2 = EnvSt2 {
    getEnvSt  :: !Env,
    getNxtAdr :: !NextAddr,
    getInstrs :: AM2AnnotatedProgram,
    getNxtPC  :: ProgramCounter
} deriving (Eq)

instance Show EnvStateAM2 where
    show (EnvSt2 env nxtAdr instrs nxtPc) =
        "env: " ++ show env ++ "\n" ++
        "next address: " ++ show nxtAdr ++ "\n" ++
        "instructions (with pc): " ++ show instrs ++ "\n" ++
        "next program counter (pc): " ++ show nxtPc ++ "\n"

getEnv :: Env -> Var -> Z
getEnv environ var = environ M.! var

data AM2Instr
    = PUSH Z
    | ADD
    | MULT
    | SUB
    | TRUE
    | FALSE
    | EQUAL
    | LE
    | GE
    | LTHAN
    | AND
    | OR
    | NEG
    | PUT Z
    | GET Z
    | NOOP
    | LABEL ProgramCounter
    | JUMP ProgramCounter
    | JUMPFALSE ProgramCounter
    deriving (Eq, Show)

type AM2Code = [AM2Instr]

--copyPasteHelper :: AM2Instr -> St.State EnvStateAM2 AM2Code
copyPasteHelper ae ae' instr = do
    -- Careful with the order with which this is done - whichever is done first
    -- puts its code on the stack first, so the second operand has to go first.
    code' <- aexpToAM2Code ae'
    code <- aexpToAM2Code ae
    St.modify' (\(EnvSt2 environ nxtAdr instrs nxtPC) -> EnvSt2 environ nxtAdr (M.insert nxtPC instr instrs) (nxtPC + 1))
    return $ concat [code', code, [instr]]

aexpToAM2Code :: Aexp -> St.State EnvStateAM2 AM2Code
aexpToAM2Code a = case a of
    Num n -> do
        let instr = PUSH n
        St.modify' (\(EnvSt2 environ nxtAdr instrs nxtPC) -> EnvSt2 environ nxtAdr (M.insert nxtPC instr instrs) (nxtPC + 1))
        return [instr]
    Var var -> do
        EnvSt2 environ nxtAdr instrs nxtPC <- St.get
        case M.lookup var environ of
            Nothing  -> do
                let instr = GET nxtAdr
                St.put $ EnvSt2 (M.insert var nxtAdr environ) (nxtAdr + 1) (M.insert nxtPC instr instrs) (nxtPC + 1)
                return [instr]
            Just adr -> do
                let instr = GET adr
                St.put $ EnvSt2 environ nxtAdr (M.insert nxtPC instr instrs) (nxtPC + 1)
                return [instr]
    ae `Plus` ae' -> copyPasteHelper ae ae' ADD
    ae `Mul` ae' -> copyPasteHelper ae ae' MULT
    ae `Minus` ae' -> copyPasteHelper ae ae' SUB

bexpToAM2Code :: Bexp -> St.State EnvStateAM2 AM2Code
bexpToAM2Code b = case b of
    T -> do
        let instr = TRUE
        St.modify' (\(EnvSt2 environ nxtAdr instrs nxtPC) -> EnvSt2 environ nxtAdr (M.insert nxtPC instr instrs) (nxtPC + 1))
        return [instr]
    F -> do
        let instr = FALSE
        St.modify' (\(EnvSt2 environ nxtAdr instrs nxtPC) -> EnvSt2 environ nxtAdr (M.insert nxtPC instr instrs) (nxtPC + 1))
        return [instr]
    ae `Eq` ae' -> copyPasteHelper ae ae' EQUAL
    ae `Le` ae' -> copyPasteHelper ae ae' LE
    ae `Lt` ae' -> copyPasteHelper ae ae' LTHAN
    ae `Ge` ae' -> copyPasteHelper ae ae' GE
    Not be -> do
        code <- bexpToAM2Code be
        let instr = NEG
        St.modify' (\(EnvSt2 environ nxtAdr instrs nxtPC) -> EnvSt2 environ nxtAdr (M.insert nxtPC instr instrs) (nxtPC + 1))
        return $ code ++ [instr]
    be `And` be' -> copyPasteHelper2 be be' AND
    be `Or` be' -> copyPasteHelper2 be be' OR
    where
        copyPasteHelper2 be be' instr = do
            -- Careful with the order with which this is done - whichever is done first
            -- puts its code on the stack first, so the second operand has to go first.
            code' <- bexpToAM2Code be'
            code <- bexpToAM2Code be
            St.modify' (\(EnvSt2 environ nxtAdr instrs nxtPC) -> EnvSt2 environ nxtAdr (M.insert nxtPC instr instrs) (nxtPC + 1))
            return $ concat [code', code, [instr]]

type Stack = [Either Z Bool]

-- Mapping from address positions to the values they contain.
-- Should look like:
-- 0 -> n_1
-- 1 -> n_2
-- 2 -> n_3,
-- ...
-- k -> n_k
-- and so on, where n_i are integers.
type Memory = M.Map Z Z

type AM2Config = (ProgramCounter, AM2Code, Stack, Memory)

type AM2AnnotatedProgram = M.Map ProgramCounter AM2Instr

-- Igual a função evalNS, mas com uso da mónade State.
whileToAM2 :: Stm -> (AM2Code, EnvStateAM2)
whileToAM2 stm = St.runState (helper stm) (EnvSt2 M.empty 0 M.empty 1)
    where
        incrCounter = do
            EnvSt2 e nA is nxtPC <- St.get
            St.put $ EnvSt2 e nA is $ nxtPC + 1
            return nxtPC

        helper :: Stm -> St.State EnvStateAM2 AM2Code
        helper (var `Assign` aexp) = do
            code <- aexpToAM2Code aexp
            EnvSt2 environ nxtAdr instrs nxtPC <- St.get
            case M.lookup var environ of
                Nothing -> do
                    let instr = PUT nxtAdr
                    St.put $ EnvSt2 (M.insert var nxtAdr environ) (nxtAdr + 1) (M.insert nxtPC instr instrs) (nxtPC + 1)
                    return $ code ++ [instr]
                Just n  -> do
                    let instr = PUT n
                    St.put $ EnvSt2 environ nxtAdr (M.insert nxtPC instr instrs) (nxtPC + 1)
                    return $ code ++ [instr]
        helper Skip = do
            let instr = NOOP
            St.modify' (\(EnvSt2 environ nxtAdr instrs nxtPC) -> EnvSt2 environ nxtAdr (M.insert nxtPC instr instrs) (nxtPC + 1))
            return [instr]
        helper (c1 `Comp` c2) = do
            code1 <- helper c1
            code2 <- helper c2
            return $ code1 ++ code2
        -- O código máquina gerado para o comando IfThenElse e para o comando WhileDo
        -- é complexo porque deve primeiro gerar o código dos subcomandos e predicados,
        -- e só depois colocar as instruções de salto e labels - cujo program counter
        -- terá de ser guardado antes da tradução dos subcomandos.
        --
        -- Ver incrCounter.
        helper (IfThenElse b c1 c2) = do
            predCode <- bexpToAM2Code b
            jzProgCounter <- incrCounter
            thenCode <- helper c1
            elseProgCounter <- incrCounter
            elseCode <- helper c2
            afterIfProgCounter <- incrCounter
            let ifJump     = JUMPFALSE elseProgCounter
                elseLabel  = LABEL elseProgCounter
                jumpToRest = JUMP afterIfProgCounter
                restLabel  = LABEL afterIfProgCounter
            EnvSt2 environ nxtAdr instrs _ <- St.get
            let jumps = M.fromList [(jzProgCounter, ifJump), (elseProgCounter, jumpToRest), (afterIfProgCounter, restLabel)]
            -- Incrementa-se o contador de código devido ao LABEL final, que apontará
            -- para o código depois do IfThenElse, se existir.
            St.put $ EnvSt2 environ nxtAdr (instrs `M.union` jumps) (afterIfProgCounter + 1)
            return $ predCode ++ [ifJump] ++ thenCode ++ [jumpToRest] ++ elseCode ++ [restLabel]
        helper (WhileDo b c) = do
            boolTestCounter <- incrCounter
            predCode <- bexpToAM2Code b
            jzProgCounter <- incrCounter
            loopCode <- helper c
            jumpCounter <- incrCounter
            afterWhileCounter <- incrCounter
            let whileLabel = LABEL boolTestCounter
                whileJump  = JUMPFALSE afterWhileCounter
                loopJump   = JUMP boolTestCounter
                restLabel  = LABEL afterWhileCounter
            EnvSt2 environ nxtAdr instrs _ <- St.get
            let jumps = M.fromList [(boolTestCounter, whileLabel), (jzProgCounter, whileJump), (jumpCounter, loopJump), (afterWhileCounter, restLabel)]
            St.put $ EnvSt2 environ nxtAdr (instrs `M.union` jumps) (afterWhileCounter + 1)

            return $ [whileLabel] ++ predCode ++ [whileJump] ++ loopCode ++ [loopJump] ++ [restLabel]

-- Given an AM2 configuration, execute a single instruction
-- and transition into the next configuration.
--
-- Requires 
stepAM2 :: AM2Config -> AM2AnnotatedProgram -> AM2Config
stepAM2 conf@(_, [], stack, mem) _ = conf
stepAM2 (pc, c : cs, stack, mem) ann ={-}
    trace (
        "code: " ++ show (c : cs) ++ "\n" ++
        "stack: " ++ show stack
    ) $ -}case c of
    PUSH n -> (pc', cs, Left n : stack, mem)
    ADD -> case stack of
        Left z1 : Left z2 : stack' ->
            (pc', cs, Left (z1 + z2) : stack, mem)
        _ -> error "ADD: invalid stack for operation!"
    MULT -> case stack of
        Left z1 : Left z2 : stack' ->
            (pc', cs, Left (z1 * z2) : stack, mem)
        _ -> error "MULT: invalid stack for operation!"
    SUB -> case stack of
        Left z1 : Left z2 : stack' ->
            (pc', cs, Left (z1 - z2) : stack, mem)
        _ -> error "SUB: invalid stack for operation!"
    TRUE -> (pc', cs, Right True : stack, mem)
    FALSE -> (pc', cs, Right False : stack, mem)
    EQUAL -> case stack of
        Left z1 : Left z2 : stack' ->
            (pc', cs, Right (z1 == z2) : stack, mem)
        _ -> error "EQUAL: invalid stack for operation!"
    LE -> case stack of
        Left z1 : Left z2 : stack' ->
            (pc', cs, Right (z1 <= z2) : stack, mem)
        _ -> error "LE: invalid stack for operation!"
    GE -> case stack of
        Left z1 : Left z2 : stack' ->
            (pc', cs, Right (z1 >= z2) : stack, mem)
        _ -> error "GE: invalid stack for operation!"
    LTHAN -> case stack of
        Left z1 : Left z2 : stack' ->
            (pc', cs, Right (z1 < z2) : stack, mem)
        _ -> error "LTHAN: invalid stack for operation!"
    AND -> case stack of
        Right b1 : Right b2 : stack' ->
            (pc', cs, Right (b1 && b2) : stack, mem)
        _ -> error "AND: invalid stack for operation!"
    OR -> case stack of
        Right b1 : Right b2 : stack' ->
            (pc', cs, Right (b1 || b2) : stack, mem)
        _ -> error "OR: invalid stack for operation!"
    NEG -> case stack of
        Right b1 : stack' ->
            (pc', cs, Right (not b1) : stack, mem)
        _ -> error "NEG: invalid stack for operation!"
    PUT n -> case stack of
        Left z : stack' -> (pc', cs, stack', M.insert n z mem)
        _ -> error "PUT: invalid stack for operation"
    GET n -> (pc', cs, Left (Maybe.fromJust $ M.lookup n mem): stack, mem)
    NOOP -> (pc', cs, stack, mem)
    LABEL lab -> (pc', cs, stack, mem)
    JUMP lab -> case M.lookup lab ann of
        Nothing    -> error "JUMP: invalid label!"
        Just instr ->
            let instrs = M.elems $ M.dropWhileAntitone (<= lab) ann
            in {-trace ("instrs: " ++ show (instr : instrs) ++ "\nmem: " ++ show mem)-} (lab, instr : instrs, stack, mem)
    JUMPFALSE lab -> case stack of
        Right b : stack' -> if b
                then (pc', cs, stack', mem)
                else case M.lookup lab ann of
                    Nothing    -> error "JUMPFALSE: invalid label!"
                    Just instr ->
                        let instrs = M.elems $ M.dropWhileAntitone (<= lab) ann
                        in (lab, instr : instrs, stack', mem)
        _            -> error "JUMPFALSE: invalid stack for operation"

    where
        pc' = pc + 1

-- A configuração inicial de um programa para AM2 precisa vir acompanhada de
-- um Map com a associação entre cada instrução e o seu program counter,
-- porque no caso das instruções de salto em que é possível "regredir" no
-- programa, usar só uma lista para instruções não o permitirá.
initConfigAM2 :: State -> Stm -> (AM2Config, Env, AM2AnnotatedProgram)
initConfigAM2 initSt stm =
    let code :: AM2Code
        envSt :: EnvStateAM2
        (code, envSt) = whileToAM2 stm

        environ = getEnvSt envSt
        annotatedByteCode = getInstrs envSt--M.fromList $ zip (M.keys . getInstrs $ envSt) code

        memory :: Memory
        memory = M.fromList [(getEnv environ variable, getSt initSt variable) | variable <- M.keys environ]
    in ((1, code, [], memory), environ, annotatedByteCode)

-- Dado um estado inicial e um comando da linguagem while, simula a sua execução
-- na máquina abstrata AM2.
-- Devolve as variáveis usadas no programa, e os valores que estavam nas respetivas
-- posições de memória aquando da terminação da execução.
-- Pode não terminar! (Halting problem).
runStmInAM2 :: State -> Stm -> M.Map Var Z
runStmInAM2 initSt stm =
    let (init@(initPC, initCode, initStack, initMemory), environ, annotated) = initConfigAM2 initSt stm
        program_length = M.size annotated
        run :: AM2Config -> AM2Config
        run !cfg =
            let cfg'@(pc, code, stack, memory) = stepAM2 cfg annotated
            in if fromInteger pc == (program_length + 1) then cfg else run cfg'
        (finalPC, finalCode, finalStack, finalMemory) = run init

        varsToValues = M.fromList [(var, finalMemory M.! (environ M.! var)) | var <- M.keys environ]

    in varsToValues