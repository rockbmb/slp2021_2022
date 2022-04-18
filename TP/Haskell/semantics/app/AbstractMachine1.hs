{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE BangPatterns #-}
module AbstractMachine1 (
    EnvStateAM1 (..),
    AM1Instr (..),
    AM1Code,

    aexpToAM1Code,
    bexpToAM1Code,

    whileToAM1,

    initConfigAM1,
    stepAM1,
    runStmInAM1
) where

import Debug.Trace

import qualified Control.Monad.State.Strict as St
import qualified Data.Map                   as M

import           Core                       (Aexp (..), Bexp (..), Var, Z, Stm (..),
                                             State, getSt)
import qualified Data.Maybe                 as Maybe

-- Mapping from variable names to positions in memory.
-- Used during "compilation" of While code to AM1 bytecode.
type Env = M.Map Var Z

type NextAddr = Z

data EnvStateAM1 = EnvSt {
    getEnvSt :: !Env,
    getNxtAdr :: !NextAddr
} deriving (Eq, Show)

getEnv :: Env -> Var -> Z
getEnv e var = e M.! var

data AM1Instr
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
    | BRANCH AM1Code AM1Code
    | LOOP AM1Code AM1Code
    deriving (Eq, Show)

type AM1Code = [AM1Instr]

aexpToAM1Code :: EnvStateAM1 -> Aexp -> (AM1Code, EnvStateAM1)
aexpToAM1Code m@(EnvSt e nxtAdr) a = case a of
    Num n -> ([PUSH n], m)
    Var var -> case M.lookup var e of
        Nothing  -> ([GET nxtAdr], EnvSt (M.insert var nxtAdr e) (nxtAdr + 1))
        Just adr -> ([GET adr], m)
    ae `Plus` ae' ->
        let (code, m') = aexpToAM1Code m ae
            (code', m'') = aexpToAM1Code m' ae'
        in (concat [code', code, [ADD]], m'')
    ae `Mul` ae' ->
        let (code, m') = aexpToAM1Code m ae
            
            (code', m'') = aexpToAM1Code m' ae'
        in (concat [code', code, [MULT]], m'')
    ae `Minus` ae' ->
        let (code, m') = aexpToAM1Code m ae
            (code', m'') = aexpToAM1Code m' ae'
        in (concat [code', code, [SUB]], m'')

bexpToAM1Code :: EnvStateAM1 -> Bexp -> (AM1Code, EnvStateAM1)
bexpToAM1Code m@(EnvSt e nxtAdr) b = case b of
    T -> ([TRUE], m)
    F -> ([FALSE], m)
    ae `Eq` ae' ->
        let (code, m') = aexpToAM1Code m ae
            (code', m'') = aexpToAM1Code m' ae'
        in (concat [code', code, [EQUAL]], m'')
    ae `Le` ae' ->
        let (code, m') = aexpToAM1Code m ae
            (code', m'') = aexpToAM1Code m' ae'
        in (concat [code', code, [LE]], m'')
    ae `Lt` ae' ->
        let (code, m') = aexpToAM1Code m ae
            (code', m'') = aexpToAM1Code m' ae'
        in (concat [code', code, [LTHAN]], m'')
    ae `Ge` ae' ->
        let (code, m') = aexpToAM1Code m ae
            (code', m'') = aexpToAM1Code m' ae'
        in (concat [code', code, [GE]], m'')
    Not be ->
        let (code, m') = bexpToAM1Code m be
        in ( NEG : code, m')
    be `And` be' ->
        let (code, m') = bexpToAM1Code m be
            (code', m'') = bexpToAM1Code m' be'
        in (concat [code', code, [AND]], m'')
    be `Or` be' ->
        let (code, m') = bexpToAM1Code m be
            (code', m'') = bexpToAM1Code m' be'
        in (concat [code', code, [OR]], m'')

whileToAM1 :: Stm -> (AM1Code, EnvStateAM1)
whileToAM1 stm = St.runState (helper stm) (EnvSt M.empty 0)
    where
        helper :: Stm -> St.State EnvStateAM1 AM1Code
        helper (var `Assign` aexp) = do
            envSt <- St.get
            let (code, EnvSt e nxtAdr) = aexpToAM1Code envSt aexp
            case M.lookup var e of
                Nothing -> do
                    let newEnv = EnvSt (M.insert var nxtAdr e) (nxtAdr + 1)
                    St.put newEnv
                    return $ code ++ [PUT nxtAdr]
                Just n  -> do
                    St.put $ EnvSt e nxtAdr
                    return $ code ++ [PUT n]
        helper Skip = return [NOOP]
        helper (c1 `Comp` c2) = do
            code1 <- helper c1
            code2 <- helper c2
            return $ code1 ++ code2
        helper (IfThenElse b c1 c2) = do
            memSt <- St.get
            let (predCode, memSt') = bexpToAM1Code memSt b
            St.put memSt'
            thenCode <- helper c1
            elseCode <- helper c2
            return $ predCode ++ [BRANCH thenCode elseCode]
        helper (WhileDo b c) = do
            memSt <- St.get
            let (predCode, memSt') = bexpToAM1Code memSt b
            St.put memSt'
            loopCode <- helper c
            return [LOOP predCode loopCode]

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

type AM1Config = (AM1Code, Stack, Memory)

stepAM1 :: AM1Config -> AM1Config
stepAM1 conf@([], stack, mem) = conf
stepAM1 (c : cs, stack, mem) = case c of
    PUSH n -> (cs, Left n : stack, mem)
    ADD -> case stack of
        Left z1 : Left z2 : stack' ->
            (cs, Left (z1 + z2) : stack', mem)
        _ -> error "ADD: invalid stack for operation!"
    MULT -> case stack of
        Left z1 : Left z2 : stack' ->
            (cs, Left (z1 * z2) : stack', mem)
        _ -> error "MULT: invalid stack for operation!"
    SUB -> case stack of
        Left z1 : Left z2 : stack' ->
            (cs, Left (z1 - z2) : stack', mem)
        _ -> error "SUB: invalid stack for operation!"
    TRUE -> (cs, Right True : stack, mem)
    FALSE -> (cs, Right False : stack, mem)
    EQUAL -> case stack of
        Left z1 : Left z2 : stack' ->
            (cs, Right (z1 == z2) : stack', mem)
        _ -> error "EQUAL: invalid stack for operation!"
    LE -> case stack of
        Left z1 : Left z2 : stack' ->
            (cs, Right (z1 <= z2) : stack', mem)
        _ -> error "LE: invalid stack for operation!"
    GE -> case stack of
        Left z1 : Left z2 : stack' ->
            (cs, Right (z1 >= z2) : stack', mem)
        _ -> error "GE: invalid stack for operation!"
    LTHAN -> case stack of
        Left z1 : Left z2 : stack' ->
            (cs, Right (z1 < z2) : stack', mem)
        _ -> error "LTHAN: invalid stack for operation!"
    AND -> case stack of
        Right b1 : Right b2 : stack' ->
            (cs, Right (b1 && b2) : stack', mem)
        _ -> error "AND: invalid stack for operation!"
    OR -> case stack of
        Right b1 : Right b2 : stack' ->
            (cs, Right (b1 || b2) : stack', mem)
        _ -> error "OR: invalid stack for operation!"
    NEG -> case stack of
        Right b1 : stack' ->
            (cs, Right (not b1) : stack', mem)
        _ -> error "NEG: invalid stack for operation!"
    PUT n -> case stack of
        Left z : stack' -> (cs, stack', M.insert n z mem)
        _ -> error "PUT: invalid stack for operation"
    GET n -> (cs, Left (Maybe.fromJust $ M.lookup n mem): stack, mem)
    NOOP -> (cs, stack, mem)
    BRANCH ins ins' -> case stack of
      Right b : stack' ->
          let instr = if b then ins else ins'
          in (instr, stack', mem)
      _   -> error "BRANCH: invalid stack for operator!"

    LOOP ins ins' -> (ins ++ [BRANCH (ins' ++ [LOOP ins ins']) [NOOP]] ++ cs, stack, mem)

initConfigAM1 :: State -> Stm -> (AM1Config, Env)
initConfigAM1 initSt stm =
    let code :: AM1Code
        envSt :: EnvStateAM1
        (code, envSt) = whileToAM1 stm

        environ = getEnvSt envSt

        memory :: Memory
        memory = M.fromList [(getEnv environ variable, getSt initSt variable) | variable <- M.keys environ]
    in ((code, [], memory), environ)

-- Dado um estado inicial e um comando da linguagem while, simula a sua execução
-- na máquina abstrata AM1.
-- Devolve as variáveis usadas no programa, e os valores que estavam nas respetivas
-- posições de memória aquando da terminação da execução.
-- Pode não terminar! (Halting problem).
runStmInAM1 :: State -> Stm -> M.Map Var Z
runStmInAM1 initSt stm =
    let (init@(initCode, initStack, initMemory), environ) = initConfigAM1 initSt stm
        run :: AM1Config -> AM1Config
        run !cfg =
            let cfg' = stepAM1 cfg
            in if cfg' == cfg then cfg else run cfg'
        (finalCode, finalStack, finalMemory) = run init

        varsToValues = M.fromList [(var, finalMemory M.! (environ M.! var)) | var <- M.keys environ]

    in varsToValues
