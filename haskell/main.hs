import Engine
import Strategy (strategy, getStrategy)
import Control.Exception (catch)
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
     
traceSlot :: IOSlots -> Int -> IO ()
traceSlot my slot = do
  vit <- lookupVitalityM my slot
  card <- lookupCardM my slot
  when (card /= I || vit /= 10000) $
    trace (shows slot $ "={" ++ (shows vit $ "," ++ shows card "}")) $
    return ()

mainloop :: Int -> PlayerCode -> PlayerCode -> IOSlots -> IOSlots -> IO ()
mainloop turn me him my his = do
  let processMove isZombie slot func arg =
        Control.Exception.catch (applyCard isZombie func arg my his)
              ((\e -> {-trace (show e) $-} return I) :: ApplyException -> IO Card)
  let processNormal slot func arg = do
        vit <- lookupVitalityM my slot
        result <- if vit <= 0 then return I
                  else processMove False slot func arg
        writeCardM my slot result
  
  let processZombie slot = do
        vitality <- lookupVitalityM my slot
        when (vitality < 0) $ do
          card <- lookupCardM my slot
          processMove True slot card I
          writeCardM my slot I
          writeVitalityM my slot 0
  
  -- forM_ [0..255] (traceSlot my)
  forM_ [0..255] processZombie
  freezeMy <- freezeSlots my
  freezeHis <- freezeSlots his
  move <- me freezeMy freezeHis
  -- trace ("turn: " ++ show (1 + (turn `div` 2))) $ return ()
  -- trace ("move: " ++ show move) $ return ()
  result <- case move of
    MoveCS card slot -> do
      card2 <- lookupCardM my slot
      processNormal slot card card2
    MoveSC slot card -> do
      card1 <- lookupCardM my slot
      processNormal slot card1 card
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