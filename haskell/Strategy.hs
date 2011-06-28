module Strategy where
import Engine
import Control.Monad
import Debug.Trace
import Lambda (lambda, lambdaCard)
import System.IO (hFlush, stdout)

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

costsNumber 0 = 1
costsNumber 1 = 2
costsNumber n = costsNumber (n `div` 2) + 1 + (n `mod` 2)

setNumber :: Int -> Int -> Strategy ()
setNumber slot num = do
  card <- getCard Me slot
  case card of
    Val i -> if i == num then return () else do
      case () of 
        _ | i < num `div` 2                  -> setNumber slot (num `div` 2)
          | i > 0 && i == num `div` 2        -> applyCS Dbl slot
          | i < num 
            && num - i < costsNumber num + 1 -> applyCS Succ slot
          | otherwise                        -> applyCS Put slot
      setNumber slot num
    I -> do { applySC slot zero ; setNumber slot num }
    _ -> do { applyCS Put slot  ; setNumber slot num }

costsSetNumber I num = (costsNumber num)
costsSetNumber c@(Val i) num 
  | i < num `div` 2  = (costsSetNumber c (num `div` 2)) + 1 + (num `mod` 2)
  | num < i          = 1 + (costsNumber num)
  | num - i < 6      = num - i
  | otherwise        = min (1 + (costsNumber num)) (num - i)
costsSetNumber _ num = 1 + (costsNumber num)

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


-----------
-- compute difference between apply cost and set cost and the
-- difference between these apply or set for different register usage.
-- returns (applyMinusSet, diff) where
--    applyMinusSet is diff between apply and set for 0 registers,
--    diff !! i tells how much apply resp. set gets cheaper if using 
--                    register i is allowed.
-- Note the following invariants:
--  the list is decreasing, i.e. the more register the smaller the gain
--  apply diff is at least as big as set diff

costsDiffCost usecost (Val n)  = 
  (2*steps - 3, if appDiff > 0 then [ (appDiff,0) ] else [])
    where steps = costsNumber n
          appDiff = 2 * steps - 3 - head usecost
costsDiffCost usecost (c1 :$ c2) = 
  (applyMinusSet, zipCostDiff applyMinusSet 0 usecost diff1 diff2)
    where 
      (applyMinusSet1, diff1) = costsDiffCost usecost c1
      (applyMinusSet2, diff2) = costsDiffCost usecost c2
      applyMinusSet = 2 + (if isSimpleCard c1 then applyMinusSet2
                           else applyMinusSet1)
      zipCostDiff _ _ [] _ _ = []
      zipCostDiff a over (use:useTail) [] [] =
        if ad > 0 then [ (ad, 0) ] else []
          where ad = (a - use)
      zipCostDiff a over (use:useTail) d1 [] =      
        zipCostDiff a over (use:useTail) d1 [(0,0)]
      zipCostDiff a over (use:useTail) [] d2 =
        zipCostDiff a over (use:useTail) [(0,0)] d2
      zipCostDiff a over (use:useTail) ((ad1,sd1):d1Tail) ((ad2,sd2):d2Tail) =
        if ad == 0 && tail == [] then []
        else (ad, sd) : tail
          where adsum = ad1 + ad2 - over
                ad = maximum[adsum, (a - use), 0]
                sd = if isSimpleCard c1 then sd2 else sd1 + ad2
                tail = zipCostDiff (a - ad + sd) (ad - adsum) useTail d1Tail d2Tail
costsDiffCost usecost _ = (-1, [])

computeRegister :: [Int] -> Card -> Int
computeRegister usecost c = 
  findbest (-1) 0 applyMinusSet usecost diff
    where
      (applyMinusSet, diff) = costsDiffCost usecost c
      findbest best index a (use:useTail) ((ad,sd):dTail) =
        findbest newbest (index+1) (a - ad + sd) useTail dTail
          where newbest = (if a - ad < use then best else index)
      findbest best index a (use:useTail) [] = (if a < use then best else index)
      findbest best _ _ [] [] = best

-- compute costs for applying a card.
--  it takes a list of additional costs for using no, one, etc extra registers
--  returns a list of costs, n-th entry is when using n free regs
costsApply :: [Int] -> Card -> Int
costsApply usecost (Val n) | n > 0 = costsApply usecost (valToApp n)
costsApply usecost (c1 :$ c2) =
  minimum $ apply1 + apply2 + 2 : map setCost [0 .. (length usecost - 1)]
  where apply1   = (costsApply usecost c1)
        apply2   = (costsApply usecost c2)
        setCost reg  = costsSet (take reg usecost) (c1 :$ c2) 
                        + (usecost !! reg)
costsApply usecost _ = 1

-- compute costs for setting a card, where
--   takes a list of additional costs for 1st,2nd,3rs,etc register
costsSet :: [Int] -> Card -> Int
costsSet usecost (Val n)    = 1 + costsNumber n
costsSet usecost (c1 :$ c2) 
  | isSimpleCard c1 = 1 + (costsSet usecost c2)
  | otherwise       = (costsSet usecost c1) + (costsApply usecost c2)
costsSet usecost _  = 2

useCosts free = map costs free
  where headcost = costsNumber (head free) * 3 + 1
        costs n = min (3*step+1) (step + 2 + headcost)
          where step = costsNumber n
        
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
  where steps = costsSetNumber zero n
costsSetApply slot free _ = (1,1,2,2)

applySCR :: [Int] -> Int -> Card -> Strategy()
applySCR freeRegs slot (Val n) | n > 0 = applySCR freeRegs slot $ valToApp n
applySCR freeRegs slot c@(c1 :$ c2)
  | num >= 0  =
      do setCardR newfree tmpreg c
         applySCR newfree slot $ get tmpreg
  | otherwise =
      do applyCS K slot
         applyCS S slot
         applySCR freeRegs slot c1
         applySCR freeRegs slot c2
  where numt    = computeRegister (useCosts freeRegs) c
        num     = 
          trace ("applySCR "++show freeRegs++" on "++show c1++" $$ "++ show c2++": "++show numt) numt
        tmpreg  = freeRegs !! num
        newfree = take num freeRegs
applySCR _ slot card = applySC slot card

{-
secureApply regs slot c1 (Val n) = secureApply regs slot c1 (valToApp n)
secureApply regs slot c1 (c2 :$ c3)
  | num >= 0  = secureCard regs   slot (S :$ (K :$ c1) :$ get)
                secureCard tmpreg slot (c2 :$ c3)
                secureCard regs   slot (c1 :$ (get :$ (Val tmpreg)))
      do setCardR newfree tmpreg c
         applySCR newfree slot $ get tmpreg
  | isSimpleCard c2 && isSimpleCard c3 =
  | otherwise = secureCard regs slot (S :$ (K :$ c1) :$ c2 :$ c3) 
  where numt    = computeRegister (useCosts regs) (c2 :$ c3)
        num     = 
          trace ("apply "++show regs++" on "++show c1++" $$ "++ show c2++": "++show numt) numt
        tmpreg  = regs !! num
        newfree = take num regs

secureCard :: [Int] -> Int -> Card -> Strategy()
secureCard regs slot (Val n) = setNumber slot n
secureCard regs slot c = do
  vit <- getVitality Me slot
  if (vit <= 0) 
    then do reviveSlot slot
            secureCard slot c
    else do current <- getCard Me slot
            when (current /= c) $ do
              case c of
                c1 :$ c2 | isSimpleCard c2 
                           && (c1 == current 
                               || !isSimpleCard c1) -> applySC slot c2
                         | isSimpleCard c1 -> do secureCard regs slot c2 
                                                 applyCS c1 slot
                         | otherwise -> secureApply regs slot c1 c2
                _ | current == I -> applySC slot c
                  | otherwise -> secureCard slot I; applySC slot c
-}

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
setCardR freeRegs slot card = do
   c <- getCard Me slot
   when (card /= c) $ case card of
     (c1 :$ c2) | isSimpleCard c1 ->
       do setCardR freeRegs slot c2
          applyCS c1 slot
                | otherwise ->
         do setCardR freeRegs slot c1
            applySCR freeRegs slot c2
     _ -> if (c == I) then applySC slot card
          else do applyCS Put slot
                  setCardR freeRegs slot card


reviveRegister reg = do
  let isfree x = return $ x > 5
      computeCost x = do
        card <- getCard Me x
        return $ costsSetNumber card reg
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

--------------
-- global slot usage
--------------
trStrategy = 
  do
    setCardR [0,1,2,3] tr transformer
    setNumber 6 9999
    setCardR [0,1,2,3] 7  $ lambda subst "(get tr) (%x I) 10"
    applySC 7 I
    applySC 7 I
    applySC 7 I
    applySC 7 I
    applySC 7 Put
    applySC 10 zero
    applySC 14 zero
  where
    tr    = 4
    subst "tr"     = Val tr
    subst "value"  = Val 6
    subst "doit"   = lambda subst "%x %y help x x y"
    transformer =
      lambda subst $"%oc %reg %x x (K get x tr) "++
                    "(%z (K doit z reg) (K get oc value) (oc z)) (succ reg)"
    
maximize reg = 
  do
    setCardR [0,1,2,3] 10 transformer
    setNumber 1 reg
    setCardR []      0  $ lambda subst "get tr zero"
    applySC   0 zero
    applySC reg zero
  where
    tr    = 10
    subst "tr"     = Val tr
    transformer =
      lambda subst $"%x %y K (help (get (succ x)) (get (succ x))) y 4096 (get y y)"
    

{-
S K x y = y
I K x y = x
K K x y = K y
S I x y = y (x y)
I I x y = x y
K I x y = y

S x S y = x y (S y)
I x I y = x I y
K x K y = x y

S K x y = y
S I x y = y (x y)
S S x y = S y (x y)

-}

mainStrategy :: Strategy ()
mainStrategy = do
  startThread 1 $ reviver
  setCardR [0]     2 $ lambdaCard "attack 0 0 6144"
  setCardR [0]     2 $ lambdaCard "attack 1 0 (get 0)"
  setCardR [0,1,2] 3 $ lambdaCard "%x help x x 6144 ((K copy x 3) (succ x))"
  setCardR [0,1,4] 2 $ lambdaCard "%x (zombie x %y (K copy y 1) y) (K get x 2)"
  setCardR [0,4]   1 $ lambdaCard "%y (get 3) (K copy y 0)"
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

getStrategy = mainStrategy

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

megarec reg =
  do setCardR []      0 $ lambdaCard "%z %f %x f (z f x)"
     setCardR []    reg $ lambdaCard "get 0"
     applySCR []      0 $ lambdaCard "I"
     applySCR []    reg $ lambdaCard "get 0"
     applySCR []    reg $ lambdaCard "get 0" 
     applySCR []    reg $ lambdaCard "get 0" 
     applySCR []    reg $ lambdaCard "S inc" 
     setCardR []      0 $ Get :$ (Val reg)
     applySCR []      0 $ lambdaCard "inc" 
     applySCR []    reg $ lambdaCard "get 0" 
     setCardR []      0 $ Get :$ (Val reg)
     applySCR []    reg $ lambdaCard "zero"
     setCardR []    reg $ lambdaCard "get 0" 
     applySCR []    reg $ lambdaCard "zero"
     setCardR []    reg $ lambdaCard "get 0" 
     applySCR []    reg $ lambdaCard "zero"
     setCardR []    reg $ lambdaCard "get 0" 
     applySCR []    reg $ lambdaCard "zero"
     applySCR []      0 $ lambdaCard "I"

{-
Y(f,c) = f(f(f c))
Y'(fxs,c) = fxs (fxs (c))
Y'(Y',fxs,c) = Y' (Y' (fxs)) c 
             = Y' (fxs)( Y' (fxs) ( c))
             = fxs(fxs(fxs(fxs(c))))
               

fxs(c, x) = (%z z x c1, c2 (c2 x))
w
Y h f = f (h h f)
Y Y 1 2  = (Y 1 1) (Y 1 1) 2 = 

%f %h f (h f h) = %h S I (S h (K h)) = K(SI) (S S K)
-}

t = test [ recurse ]
recurse =
  do setCardR [1,2,3] 0 $ lambdaCard "(%h %x inc x (h h (succ x)))"
     setCardR [0,1,2,3] 10 $ lambdaCard "(get 0) (get 0) 0"

megarevive reg =
  do setCardR []      0 $ lambdaCard "%z %f %x f (z f x)"
     setCardR []    reg $ lambdaCard "get 0"
     applySCR []      0 $ lambdaCard "I"
     applySCR []    reg $ lambdaCard "get 0"
     applySCR []    reg $ lambdaCard "get 0" 
     applySCR []    reg $ lambdaCard "get 0" 
     
     {-setCardR []      1 $ lambdaCard "get 0"
     applySCR []      1 $ lambdaCard "get 0"
     applySCR []      0 $ lambdaCard "I"
     applySCR []      1 $ lambdaCard "get 0"
     applySCR []      1 $ lambdaCard "get 0"-}
--fxs(c, x) = (%z z x c1, succ (c2 x))
     applySCR [0,2] reg $ lambdaCard "%c (S revive inc) c (succ c)"
     applySCR [0,2] reg $ lambdaCard "zero"
     {-
     setCardR []      0 $ Get :$ (Val reg)
     applySCR []      0 $ lambdaCard "%x I" 
     applySCR []      0 $ lambdaCard "64" 
     applySCR []    reg $ lambdaCard "%x (get 0)" 
     applySCR [0,2] reg $ lambdaCard "zero"
     setCardR []      0 $ Get :$ (Val reg)
     applySCR []      0 $ lambdaCard "inc" 
     applySCR []    reg $ lambdaCard "get 0" 
     setCardR []      0 $ Get :$ (Val reg)
     applySCR []    reg $ lambdaCard "zero"
     setCardR []    reg $ lambdaCard "get 0" 
     applySCR []    reg $ lambdaCard "zero"
     setCardR []    reg $ lambdaCard "get 0" 
     applySCR []    reg $ lambdaCard "zero"
     setCardR []    reg $ lambdaCard "get 0" 
     applySCR []    reg $ lambdaCard "zero"
     applySCR []      0 $ lambdaCard "I"-}

--          (%f %x (get0 f) (get0 f) x)
--  %f f (f x)          
--   (S inc) ((S inc) inc)
--          get0 get0 f x = get0 (get0 (get0 f)) x 
--            =  (get0 (get0 f)) ((get0 (get0 f)) (get0 (get0 f) x))
--           =  
--  get2 get2 f = get2 (get2 f) = (get2 f) ((get2 fi %f %x (i f x) f x)"
          


test strat = 
  do
    my <- createSlotsM 
    his <- createSlotsM 
    loop my his strat 1
  where 
    loop my his strat turn = 
      do fmy  <- freezeSlots my
         fhis <- freezeSlots his
         let (move, newstrat) = strategy strat fmy fhis
         putStrLn $ "Turn " ++ show turn ++ ": " ++ show move
         processMove my his move
         printSlot my $ case move of
           MoveCS card slot -> slot
           MoveSC slot card -> slot
         loop my his newstrat (turn + 1)

---------
-- Main engine
----------

readMove = do
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

opponentMove my his = do
  forM_ [0..255] (processZombie his my)
  move <- readMove
  processMove his my move

gameloop :: [Strategy()] -> IOSlots -> IOSlots -> IO ()
gameloop strat my his = do  
  -- my move
  forM_ [0..255] (processZombie my his)
  freezeMy <- freezeSlots my
  freezeHis <- freezeSlots his
  let (move, newstrat) = strategy strat freezeMy freezeHis
  -- trace ("turn: " ++ show (1 + (turn `div` 2))) $ return ()
  -- trace ("move: " ++ show move) $ return ()
  printMove move
  processMove my his move
  opponentMove my his
  gameloop newstrat my his

rungame :: Bool -> Strategy() -> IO ()
rungame isFirst strat = do
  my <- createSlotsM
  his <- createSlotsM
  when (not isFirst) $ opponentMove my his
  gameloop [strat] my his
