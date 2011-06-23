module Strategy where
import Engine
import Control.Monad
import Debug.Trace

data Player = Me | Him
data StrategyCont a = StratRet a | StratCont (Maybe Move) (Strategy a)
newtype Strategy a = Strategy { runStrategy :: Slots -> Slots -> StrategyCont a}

instance Monad (Strategy) where
  return a = Strategy $ \me him -> StratRet a
  (>>=) (Strategy strat1) fstrat2 = Strategy $ \me him -> 
    case strat1 me him of
        StratRet a -> runStrategy (fstrat2 a) me him
        StratCont move cstrat -> StratCont move (cstrat >>= fstrat2)
  
playMove :: Move -> Strategy ()
playMove move = Strategy $ \my his -> StratCont (Just move) (return ())

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

valToApp num 
  | num == 0         = Val 0
  | num `mod` 2 == 1 = Succ :$ valToApp (num - 1)
  | otherwise        = Dbl :$ valToApp (num `div` 2)

applyCS card slot 
  | isSimpleCard card = playMove $ MoveCS card slot
  | otherwise         = error (shows "applyCS on " $ show card)

applySC :: Int -> Card -> Strategy()
applySC slot (Val n) | n > 0 = applySC slot $ valToApp n
applySC slot (c1 :$ c2) | slot /= 0 && False =
  do setCard 0 c1
     setCard 0 c2
     applySC slot $ get 0
applySC slot (c1 :$ c2) =
  do applyCS K slot
     applyCS S slot
     applySC slot c1
     applySC slot c2
applySC slot card = playMove $ MoveSC slot card

setCard :: Int -> Card -> Strategy()
setCard slot (Val n) = setNumber slot n
setCard slot (c1 :$ c2)
   | isSimpleCard c1 = do
       setCard slot c2
       applyCS c1 slot
   | False = do
       setCard slot c2
       setCard 0 $ get slot
       setCard slot c1
       applySC slot $ get 0
   | otherwise = do
       setCard slot c1
       applySC slot c2
setCard slot c = do
   card <- getCard Me slot
   when (card /= c) $ case card of
     I -> applySC slot c
     _ -> do { applyCS Put slot ; setCard slot c }


mainStrategy :: Strategy ()
mainStrategy = do
  let c = 3
      d = 4
      e = 5
  setCard 1 $ Attack :$ zero :$ zero
  setCard 2 $ Attack :$ (Succ :$ zero) :$ zero
  setCard 0 $ Val (6*1024)
  applySC 1 $ get 0
  applySC 2 $ get 0
  setCard c $ s (s (s Help I) (k (get 0))) (s (s (k Copy) (k (val c))) Succ)
  setCard d $ k (s (s (k Copy) (k (val e))) I)
  setCard 2 $ s (s (s (buildrec Dec 10) Zombie) 
                   (get d))
                (s (k Get) (k (Val 2)))
  setCard e $ s (s (k Copy) (k (Val c))) (s (k Copy) (k (Val d)))
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

strategy :: [Strategy ()] -> Slots -> Slots -> (Move, [Strategy ()])
strategy ((Strategy strat) : fallback) my his =
  case strat my his of
    StratCont Nothing newstrat -> 
      let (move, newfallback) = strategy fallback my his 
      in (move, newstrat : newfallback)
    StratCont (Just move) newstrat -> (move, newstrat : fallback)
    StratRet _ -> strategy fallback my his
  
  