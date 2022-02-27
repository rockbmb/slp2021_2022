import Control.Monad.Trans.State ( execState, State, get, modify )

f :: State Int ()
f = do
    r <- g
    modify (+ r)

g :: State Int Int
g = do
    modify (+ 1)
    get

main :: IO ()
main = print (execState f 4)