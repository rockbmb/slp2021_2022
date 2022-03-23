module AbstractMachine2 (
    AM2Instr (..),
    EnvStateAM2 (..),

    aexpToAM2Code,
    bexpToAM2Code,

    whileToAM2
) where

import qualified Control.Monad.State.Strict as St
import qualified Data.Map                   as M

import           Core                       (Aexp (..), Bexp (..), Var, Z, Stm (..))

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
    getInstrs :: M.Map ProgramCounter AM2Instr,
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
    code <- aexpToAM2Code ae
    code' <- aexpToAM2Code ae'
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
            code <- bexpToAM2Code be
            code' <- bexpToAM2Code be'
            St.modify' (\(EnvSt2 environ nxtAdr instrs nxtPC) -> EnvSt2 environ nxtAdr (M.insert nxtPC instr instrs) (nxtPC + 1))
            return $ concat [code', code, [instr]]

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
            -- Incrementa-se o contador de código devido ao LABEL final.
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