module Strategy where
import Engine
import Control.Monad
import Debug.Trace

data Player = Me | Him
data Action = MoveAction Move 
            | StartThread Int (Strategy ())
            | KillThread Int
            | Yield
data StrategyCont a = StratRet a | StratCont Action (Strategy a)
newtype Strategy a = Strategy { runStrategy :: Slots -> Slots -> StrategyCont a}

instance Monad (Strategy) where
  return a = Strategy $ \my his -> StratRet a
  (>>=) strat1 fstrat2 = Strategy $ \my his -> 
    case runStrategy strat1 my his of
        StratRet a -> runStrategy (fstrat2 a) my his
        StratCont act cstrat -> StratCont act (cstrat >>= fstrat2)
  
action :: Action -> Strategy ()
action act = Strategy $ \my his -> StratCont act $ return ()

playMove move        = action $ MoveAction move
yield                = action Yield
startThread i thread = action $ StartThread i thread
killThread i         = action $ KillThread i

firstAction :: Strategy () -> Strategy ()
firstAction strat =  
  trace "firstAction" $
  Strategy $ \my his -> case runStrategy strat my his of
    StratCont act _ -> StratCont act   $ return ()
    StratRet _      -> StratCont Yield $ return ()

getCard :: Player -> Int -> Strategy (Card)
getCard Me i = Strategy $ \my his -> StratRet (lookupCardI my i)
getCard Him i = Strategy $ \my his -> StratRet (lookupCardI his i)

getVitality :: Player -> Int -> Strategy (Int)
getVitality Me i = Strategy $ \my his -> StratRet (lookupVitalityI my i)
getVitality Him i = Strategy $ \my his -> StratRet (lookupVitalityI his i)

---------
-- Useful card constructions
---------

s x y = S :$ x :$ y
k x   = K :$ x
zero  = Val 0
val n = Val n
get n = Get :$ Val n
buildrec card 1 = card
buildrec card n = s (buildrec card (n-1)) card

---------
-- Strategy set_number: set register r to number n.
---------

isSimpleCard (Val 0) = True
isSimpleCard (Val _) = False
isSimpleCard (_ :$ _) = False
isSimpleCard _ = True

setNumber :: Int -> Int -> Strategy ()
setNumber slot num = do
  let numSteps 0 = 2
      numSteps n = numSteps (n `div` 2) + 1 + (n `mod` 2)
  card <- getCard Me slot
  case card of
    Val i -> if i == num then return () else do
      case () of 
        _ | i < num `div` 2                   -> setNumber slot (num `div` 2)
          | i > 0 && i == num `div` 2         -> applyCS Dbl slot
          | i < num && num - i < numSteps num -> applyCS Succ slot
          | otherwise                         -> applyCS Put slot
      setNumber slot num
    I -> do { applySC slot zero ; setNumber slot num }
    _ -> do { applyCS Put slot  ; setNumber slot num }

costSetNumber I num = 1 + (costSetNumber zero num)
costSetNumber c@(Val i) num 
  | i < num `div` 2 = (costSetNumber c (num `div` 2)) + 1 + (num `mod` 2)
  | num < i         = 2 + (costSetNumber zero num)
  | num - i < 6     = num - i
  | otherwise       = min (2 + (costSetNumber zero num)) (num - i)
costSetNumber _ num = 2 + (costSetNumber zero num)

valToApp num 
  | num == 0         = Val 0
  | num `mod` 2 == 1 = Succ :$ valToApp (num - 1)
  | otherwise        = Dbl :$ valToApp (num `div` 2)

applyCS :: Card -> Int -> Strategy()
applyCS card slot 
  | isSimpleCard card = playMove $ MoveCS card slot
  | otherwise         = error (shows "applyCS on " $ show card)

applySC :: Int -> Card -> Strategy()
applySC slot (Val n) | n > 0 = applySC slot $ valToApp n
applySC slot (c1 :$ c2) =
  do applyCS K slot
     applyCS S slot
     applySC slot c1
     applySC slot c2
applySC slot card = playMove $ MoveSC slot card

setCard :: Int -> Card -> Strategy()
setCard slot (Val n) = setNumber slot n
setCard slot (c1 :$ c2)
  | isSimpleCard c1 =
    do setCard slot c2
       applyCS c1 slot
  | otherwise = 
    do setCard slot c1
       applySC slot c2
setCard slot c = do
   card <- getCard Me slot
   when (card /= c) $ case card of
     I -> applySC slot c
     _ -> do { applyCS Put slot ; setCard slot c }

reviveRegister reg = do
  let isfree x = return $ x > 5
      computeCost x = do
        card <- getCard Me x
        return $ costSetNumber card reg
      chooseBest (x,freex,costx) y = do
        vity <- getVitality Me y
        if (vity <= 0) 
          then return (x,freex,costx)
          else do
            freey <- isfree y
            costy <- computeCost y
            return $ case () of
              _ | freex && not freey -> (x, freex, costx)
                | freey && not freex -> (y, freey, costy)
                | costx < costy      -> (x, freex, costx)
                | costx > costy      -> (y, freey, costy)
                | x `mod` 8 == 7     -> (x, freex, costx)
                | otherwise          -> (y, freey, costy)
              
  vit  <- getVitality Me reg
  trace ("Check Reg " ++ show reg ++ ": " ++ show vit) $ return ()
  when (vit <= 0) $ do
    trace ("Revive Reg " ++ (show reg)) $ return ()
    (usereg,_,_) <- foldM chooseBest (0,False,100) [0..255]
    setNumber usereg reg
    applyCS Revive usereg

reviver = do 
  trace "Reviver" $ firstAction (forM_ [0..5] reviveRegister)
  trace "Recurse" $ reviver

mainStrategy :: Strategy ()
mainStrategy = do
  let c = 3
      d = 0
      e = 1
  startThread 1 $ reviver
  setCard 1 $ Attack :$ zero :$ zero
  setCard 2 $ Attack :$ (Succ :$ zero) :$ zero
  setCard 0 $ Val (6*1024)
  applySC 1 $ get 0
  applySC 2 $ get 0
  applyCS K 0
  setCard c $ S :$ s (s Help I) (get 0) 
  setCard 0 $ s (s (k Copy) (k (val c))) Succ
  applySC c $ get 0
  setCard 0 $ k (s (s (k Copy) (k (val e))) I)
  -- setCard 2 $ S :$ (s (s (buildrec Dec 10) Zombie) (get 0))
  setCard 2 $ S :$ (s Zombie (get 0))
  setCard 0 $ s (k Get) (k (Val 2))
  applySC 2 $ get 0
  setCard 0 $ k (Val c)
  setCard e $ S :$ (s (k Copy) (get 0)) 
  setCard 0 $ (s (k Copy) (k (Val d)))
  applySC e $ get 0
  let loop = 
        do setCard d (Val 0)
           applySC 2 zero
           setCard d (Val 70)
           applySC 2 zero
           setCard d (Val 140)
           applySC 2 zero
           setCard d (Val 210)
           applySC 2 zero
           loop
  loop

getStrategy = [ mainStrategy ]

strategy :: [ Strategy () ] -> Slots -> Slots -> (Move, [ Strategy () ])
strategy strat my his =
  let doAction (StartThread 1 thread) list = execute (thread:list)
      doAction (StartThread n thread) list = (StartThread (n-1) thread, list)
      doAction (KillThread 0) (_:tail)     = execute tail
      doAction (KillThread n) list         = (KillThread (n-1), list)
      doAction (MoveAction move) list      = (MoveAction move, list)
      doAction Yield (head:tail) =
        let (action, newtail) = execute tail
        in doAction action (head : newtail)
           
      execute :: [ Strategy () ] -> (Action, [ Strategy () ])
      execute (head : tail) =
        case runStrategy head my his of
          StratRet _ -> execute tail
          StratCont action newhead -> doAction action (newhead : tail)

  in case execute strat of
    (MoveAction move, newstrat) -> (move, newstrat)
