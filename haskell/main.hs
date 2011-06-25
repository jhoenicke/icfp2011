import Engine
import Strategy (strategy, getStrategy)
import Control.Monad (forM_, when)
import Data.IORef
import System (getArgs)
import Debug.Trace
import System.IO (hFlush, stdout)

type PlayerCode = Slots -> Slots -> IO Move

readMove :: PlayerCode
readMove my his = do
  dir <- readLn
  case dir of 
    1 -> do
      card <- readLn
      slot <- card `seq` readLn
      return $ MoveCS card slot
    2 -> do
      slot <- readLn
      card <- readLn
      card `seq` (return $ MoveSC slot card)

printMove (MoveCS card slot) =
  do print 1; print card; print slot; hFlush(stdout)
printMove (MoveSC slot card) = 
  do print 2; print slot; print card; hFlush(stdout)
     
mainloop :: Int -> PlayerCode -> PlayerCode -> IOSlots -> IOSlots -> IO ()
mainloop turn me him my his = do  
  -- forM_ [0..255] (traceSlot my)
  forM_ [0..255] (processZombie my his)
  freezeMy <- freezeSlots my
  freezeHis <- freezeSlots his
  move <- me freezeMy freezeHis
  -- trace ("turn: " ++ show (1 + (turn `div` 2))) $ return ()
  -- trace ("move: " ++ show move) $ return ()
  processMove my his move
  mainloop (turn + 1) him me his my

kiplayer :: IO PlayerCode
kiplayer = do
  strategyRef <- newIORef getStrategy 
  writeIORef strategyRef getStrategy
  let run my his = do
        strat <- readIORef strategyRef
        let (move, newstrat) = strategy strat my his
        writeIORef strategyRef newstrat
        printMove move
        return move
  return run

rungame startGame = do
  my <- createSlotsM
  his <- createSlotsM
  me <- kiplayer
  let him = readMove
  if startGame
    then mainloop 0 me him my his
    else mainloop 0 him me his my

main = do
  args <- getArgs
  rungame (head args == "0")
  return ()