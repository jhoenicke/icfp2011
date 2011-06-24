module Lambda where
import Engine
import Data.Char (isDigit,isLower)

data LambdaTerm = X String | C Card | App LambdaTerm LambdaTerm
                deriving (Eq,Show)

infixl 1 $=
($=) (C func) (C arg) = C (func :$ arg)
($=) func arg         = App func arg

containsVar :: String -> LambdaTerm -> Bool
containsVar x (X y)          = x == y
containsVar x (C _)          = False
containsVar x (App func arg) = (containsVar x func) || (containsVar x arg)

lambda :: String -> LambdaTerm -> LambdaTerm
lambda x term 
  | not (containsVar x term) = (C K) $= term
lambda x (X y) | x == y      = C I
lambda x (App func (X y)) 
  | not (containsVar x func) 
    && x == y                = func
lambda x (App func arg)      = (C S) $= (lambda x func) $= (lambda x arg)

cardOf (C card) = card

instance Read LambdaTerm where
  readsPrec d = if d < 10 then readsTerm else read1
    where read1 s = 
            [ (card, x) | (tok, s') <- lex s,
              (card, x) <- case tok of
                 "("      -> [ (card,x) | (card,s'') <- readsTerm s', 
                               (")",x) <- lex s'']
                 "%"      -> readsLambda s'
                 "?"      -> readsLazyExpand s'
                 "zero"   -> [ (C (Val 0), s') ]
                 "I"      -> [ (C I, s') ]
                 "succ"   -> [ (C Succ, s') ]
                 "dbl"    -> [ (C Dbl, s') ]
                 "get"    -> [ (C Get, s') ]
                 "put"    -> [ (C Put, s') ]
                 "S"      -> [ (C S, s') ]
                 "K"      -> [ (C K, s') ]
                 "inc"    -> [ (C Inc, s') ]
                 "dec"    -> [ (C Dec, s') ]
                 "attack" -> [ (C Attack, s') ]
                 "help"   -> [ (C Help, s') ]
                 "copy"   -> [ (C Copy, s') ]
                 "revive" -> [ (C Revive, s') ]
                 "zombie" -> [ (C Zombie, s') ]
                 (c:_) | isDigit c -> [ (C $ Val $ read tok, s') ]
                 (c:_) | isLower c -> [ (X tok, s') ]
                 _        -> []]
          readsTerm s = [ (card, x) | 
                          (card1, s') <- read1 s,
                          (card,x)    <- readsArgs card1 s' ]
          readsArgs card s
            | args /= []= [ (result,x) | 
                            (arg, s') <- args,
                            (result,x) <- readsArgs (card $= arg) s']
            | otherwise = [ (card,s) ]
            where args = read1 s
          readsLambda s = [ (lambda var term, x) | 
                            (var, s2) <- lex s,
                            (term, x) <- readsTerm s2]
          readsLazyExpand s = [ (lazyExpand var term, x) | 
                                (var, s2) <- lex s,
                                (term, x) <- readsTerm s2]
            where lazyExpand x (App f a) = 
                    (C  K $= f  $= (X x)) $= (C  K $= a  $= (X x))
                  lazyExpand x (C (f :$ a)) = 
                    (C (K :$ f) $= (X x)) $= (C (K :$ a) $= (X x))
   
lambdaCard = cardOf . read
