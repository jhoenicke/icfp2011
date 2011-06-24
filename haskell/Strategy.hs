module Strategy where
import Engine
import Control.Monad
import Debug.Trace
import Lambda (lambdaCard)

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

-- compute for card and given free list, the costs for
--   a : applying card to a slot, allowing use of slot 0 and free list
--   a0: applying card to a slot, not allowing use of slot 0
--   s : setting card to a slot, allowing use of slot 0 and free list
--   s0: setting card to slot 0, not allowing use of slot 0
-- and return the tuple (a,a0,s,s0)
costsSetApply :: Int -> [Int] -> Card -> (Int, Int, Int, Int)
costsSetApply slot free (c1 :$ c2) = (a, a0, s, s0)
  where (a1,a01,s1,s01) = costsSetApply slot free c1
        (a2,a02,s2,s02) = costsSetApply slot free c2
        s  = if isSimpleCard c1 then s2  + 1 else s1  + a2
        s0 = if isSimpleCard c1 then s02 + 1 else s01 + a02
        a  = minimum [a1 + a2 + 2, s + num + 7, s0 + 4]
        a0 = a01 + a02 + 2
        num = 3
costsSetApply slot free (Val n) = 
  (min (3*steps + 1) (steps+6), 3*steps + 1, steps + 2, steps + 2)
  where steps = costSetNumber zero n
costsSetApply slot free _ = (1,1,2,2)

applySCR :: [Int] -> Int -> Card -> Strategy()
applySCR freeRegs slot (Val n) | n > 0 = applySCR freeRegs slot $ valToApp n
applySCR freeRegs slot c@(c1 :$ c2)
  | freeRegs /= []
    && s + num + 7 < a1 + a2 + 2
    && s + num + 7 < s0 + 4 =
      do trace ("applySC "++show slot++" "++show c++" costs "
                ++show(a1+a2+2)++","++show(s0+4)++",!"++show(s+num+7))$
           setCardR (tail freeRegs) (head freeRegs) c
         setCard 0 $ get (head freeRegs)
         applySC slot $ get 0
  | s0 + 4 < a1 + a2 + 2 =
      do trace ("applySC "++show slot++" "++show c++" costs "
                ++show(a1+a2+2)++",!"++show(s0+4)++","++show(s+num+7))$
           setCard 0 c
         applySC slot $ get 0
  | otherwise =
      do trace ("applySC "++show slot++" "++show c++" costs !"
                ++show(a1+a2+2)++","++show(s0+4)++","++show(s+num+7))$
           applyCS K slot
         applyCS S slot
         applySCR freeRegs slot c1
         applySCR freeRegs slot c2
  where (a1,a01,s1,s01) = costsSetApply slot freeRegs c1
        (a2,a02,s2,s02) = costsSetApply slot freeRegs c2
        s  = if isSimpleCard c1 then s2  + 1 else s1  + a2
        s0 = if isSimpleCard c1 then s02 + 1 else s01 + a02
        num = 3
applySCR _ slot card = applySC slot card

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
     
setCardR :: [Int] -> Int -> Card -> Strategy()
setCardR _ slot (Val n) = setNumber slot n
setCardR freeRegs slot (c1 :$ c2)
  | isSimpleCard c1 =
    do setCardR freeRegs slot c2
       applyCS c1 slot
  | otherwise = 
    do setCardR freeRegs slot c1
       applySCR freeRegs slot c2
setCardR _ slot c = do
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
  -- trace ("Check Reg " ++ show reg ++ ": " ++ show vit) $ return ()
  when (vit <= 0) $ do
    trace ("Revive Reg " ++ (show reg)) $ return ()
    (usereg,_,_) <- foldM chooseBest (0,False,100) [0..255]
    setNumber usereg reg
    applyCS Revive usereg

reviver = do 
  firstAction (forM_ [0..5] reviveRegister)
  reviver

mainStrategy :: Strategy ()
mainStrategy = do
  startThread 1 $ reviver
  setCardR [] 2 $ lambdaCard "attack 0 0 6144"
  setCardR [] 2 $ lambdaCard "attack 1 0 (get 0)"
  setCardR [1,2] 3 $ lambdaCard "%x help x x 6144 ((?x copy 3) (succ x))"
  setCardR [1,4] 2 $ lambdaCard "%x (zombie x %y (?y copy 1) y) (?x get 2)"
  setCardR [4]   1 $ lambdaCard "%y (get 3) (?y copy 0)"
  let loop = 
        do setCard 0 (Val 0)
           applySC 2 zero
           setCard 0 (Val 70)
           applySC 2 zero
           setCard 0 (Val 140)
           applySC 2 zero
           setCard 0 (Val 210)
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

test strat = 
  do
    my <- createSlotsM 
    his <- createSlotsM 
    loop my his strat
  where 
    loop my his strat = 
      do fmy  <- freezeSlots my
         fhis <- freezeSlots his
         let (move, newstrat) = strategy strat fmy fhis
         print move
         case move of
           MoveCS card slot -> do
             card2 <- lookupCardM my slot
             result <- applyCard False card card2 my his
             print $ shows slot $ "={" ++ (shows result "}")
             writeCardM my slot result
           MoveSC slot card -> do
             card1 <- lookupCardM my slot
             result <- applyCard False card1 card my his
             print $ shows slot $ "={" ++ (shows result "}")
             writeCardM my slot result
         loop my his newstrat

