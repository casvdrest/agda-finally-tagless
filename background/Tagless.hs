{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TemplateHaskell #-}

module Tagless where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax           as THS
import qualified Language.Haskell.TH.PprLib as THPP

import qualified Text.PrettyPrint as PP

class Lambda rep where
  lam      :: (rep a -> rep b)     -> rep (a -> b)
  app      :: rep (a -> b)         -> rep a                -> rep b

class Boolean rep where
  bool     :: Bool                 -> rep Bool
  not_     :: rep Bool             -> rep Bool
  and_     :: rep Bool             -> rep Bool             -> rep Bool
  or_      :: rep Bool             -> rep Bool             -> rep Bool

class Ints rep where
  int      :: Int                  -> rep Int
  neg      :: rep Int              -> rep Int
  add      :: rep Int              -> rep Int              -> rep Int
  mult_    :: rep Int              -> rep Int              -> rep Int

class IntOrder rep where
  leq      :: rep Int              -> rep Int              -> rep Bool

class Conditional rep where
  if_      :: rep Bool             -> rep a                -> rep a        -> rep a

class Pairs rep where
  pair     :: rep a                -> rep b                 -> rep (a, b)
  fst_     :: rep (a, b)           -> rep a
  snd_     :: rep (a, b)           -> rep b

class Equality rep where
  eq_      :: Eq a => rep a        -> rep a                 -> rep Bool

class Plus rep where
  left_    :: rep a                -> rep (Either a b)
  right_   :: rep b                -> rep (Either a b)
  either_  :: rep (a -> c)         -> rep (b -> c)          -> rep (Either a b)   -> rep c

class Fix rep where
  fix      :: (rep (a -> b) -> rep (a -> b))     -> rep (a -> b)

-- Useful helper classes
class Liftable rep where
  lift :: a -> rep a

class Apply f where
  lift0 :: a                  -> f a
  lift1 :: (a -> b)           -> f a -> f b
  lift2 :: (a -> b -> c)      -> f a -> f b  -> f c
  lift3 :: (a -> b -> c -> d) -> f a -> f b  -> f c  -> f d

if__ :: Bool -> a -> a -> a
if__ c t e = if c then t else e

{- ---------------------------------------------------------------
 - Interpreter
 - ---------------------------------------------------------------
 -}
newtype R a = R a
unR :: R a -> a
unR (R x) = x

instance Apply R where
  lift0 a           = R a
  lift1 o e         = R $ o (unR e)
  lift2 o e1 e2     = R $ o (unR e1) (unR e2)
  lift3 o e1 e2 e3  = R $ o (unR e1) (unR e2) (unR e3)

instance Boolean R where
  bool    = lift0
  not_    = lift1 (not)
  and_    = lift2 (&&)
  or_     = lift2 (||)

instance Ints R where
  int     = lift0
  neg     = lift1 (negate)
  add     = lift2 (+)
  mult_   = lift2 (*)

instance IntOrder R where
  leq     = lift2 (<=)

instance Conditional R where
  if_  = lift3 (if__)

instance Pairs R where
  pair    = lift2 (,)
  fst_    = lift1 (fst)
  snd_    = lift1 (snd)

instance Lambda R where
  lam     = \f -> R (unR . f . R)
  app     = lift2 ($)

instance Plus R where
  left_   = lift1 Left
  right_  = lift1 Right
  either_ = lift3 either

instance Fix R where
  fix f   = R (fx (unR . f . R)) where fx g = g (fx g)

{- ---------------------------------------------------------------
 - Pretty Printer - String version
 - ---------------------------------------------------------------
 -}
data S a = S {unS :: Int -> String}

pp :: S a -> String
pp x = unS x 0

liftS0 :: Show a => a -> S a
liftS0 = S . const . show

liftS1 :: (String -> String) -> S a -> S b
liftS1 f a = S $ \n -> f (unS a n)

liftS2 :: (String -> String -> String) -> S a -> S b -> S c
liftS2 f a b = S $ \x -> f (unS a x) (unS b x)

liftS3 :: (String -> String -> String -> String) -> S a -> S b -> S c -> S d
liftS3 f a b c = S $ \x -> f (unS a x) (unS b x) (unS c x)

string0 :: Show a => a -> S a
string0 = liftS0

string1 :: String -> S a -> S b
string1 o = liftS1 (o ++)

string2 :: String -> S a -> S b -> S c
string2 o = let f = \a b -> "(" ++ a ++ o ++ b  ++ ")" in liftS2 f

instance Boolean S where
  bool      = string0
  not_      = string1 "!"
  and_      = string2 "&&"
  or_       = string2 "||"

instance Ints S where
  int       = string0
  neg       = string1 "-"
  add       = string2 "+"
  mult_     = string2 "*"

instance IntOrder S where
  leq       = string2 "<="

instance Conditional S where
  if_ = liftS3 (\a b c -> "(if " ++ a ++ " then " ++ b ++ " else " ++ c ++ ")")

instance Pairs S where
  pair      = string2 ","
  fst_      = string1 "[0]"
  snd_      = string1 "[1]"

instance Lambda S where
  lam f     = S $ \h -> let x = ("x" ++ (show h)) in 
    "(\\" ++ x ++ " -> " ++ unS (f (S $ const x)) (succ h) ++ ")"
  app       = liftS2 (\a b -> a ++ (' ' : b))

instance Plus S where
  left_   = string1 "Left"
  right_  = string1 "Right"
  either_ = liftS3 (\a b c -> "(either " ++ a ++ " " ++ b ++ " " ++ c ++ ")")

instance Fix S where
  fix f   = S $ \h -> let x = ("x" ++ (show h)) in
    "fix" ++ (unS (f (S $ const x)) (succ h))

{- ---------------------------------------------------------------
 - Length interpreter
 - ---------------------------------------------------------------
 -}
data Length = Int
data L a = L {unL :: Int}

instance Apply L where
  lift0 _           = L 1
  lift1 _ e         = L $ (unL e)                        + 1
  lift2 _ e1 e2     = L $ (unL e1) + (unL e2)            + 1
  lift3 _ e1 e2 e3  = L $ (unL e1) + (unL e2) + (unL e3) + 1

instance Boolean L where
  bool    = lift0
  not_    = lift1 (not)
  and_    = lift2 (&&)
  or_     = lift2 (||)

instance Ints L where
  int     = lift0
  neg     = lift1 (negate)
  add     = lift2 (+)
  mult_   = lift2 (*)

instance IntOrder L where
  leq     = lift2 (<=)

instance Conditional L where
  if_  = lift3 (if__)

instance Pairs L where
  pair    = lift2 (,)
  fst_    = lift1 (fst)
  snd_    = lift1 (snd)

instance Lambda L where
  lam f   = lift1 (const) (f (L 0)) -- first argument does not matter
  app     = lift2 ($)

instance Plus L where
  left_   = lift1 Left
  right_  = lift1 Right
  either_ = lift3 either

instance Fix L where
  fix f   = lift1 id (f (L 0))

{- ---------------------------------------------------------------
 - Pretty Printer - Doc version
 - ---------------------------------------------------------------
 -}
data D a = D {unD :: Int -> PP.Doc}

liftD0 :: Show a => a -> D a
liftD0 = D . const . PP.text . show

liftD1 :: (PP.Doc -> PP.Doc) -> D a -> D b
liftD1 f a = D $ \n -> f (unD a n)

liftD2 :: (PP.Doc -> PP.Doc -> PP.Doc) -> D a -> D b -> D c
liftD2 f a b = D $ \x -> f (unD a x) (unD b x)

liftD3 :: (PP.Doc -> PP.Doc -> PP.Doc -> PP.Doc) -> D a -> D b -> D c -> D d
liftD3 f a b c = D $ \x -> f (unD a x) (unD b x) (unD c x)

doc0 :: Show a => a -> D a
doc0 = liftD0

doc1 :: String -> D a -> D b
doc1 o = liftD1 ((PP.text o) PP.<+>)

doc2 :: String -> D a -> D b -> D c
doc2 o = let f = \a b -> PP.parens $ PP.hsep [a, PP.text o, b] in liftD2 f

instance Boolean D where
  bool    = doc0
  not_    = doc1 "!"
  and_    = doc2 "&&"
  or_     = doc2 "||"

instance Ints D where
  int     = doc0
  neg     = doc1 "-"
  add     = doc2 "+"
  mult_   = doc2 "*"

instance IntOrder D where
  leq     = doc2 "<="

instance Conditional D where
  if_  = liftD3 (\a b c -> PP.hsep [PP.text "if", a, PP.text "then", b, PP.text "else", c])

instance Pairs D where
  pair    = liftD2 (\x y -> PP.parens $ x PP.<> PP.comma PP.<> y)
  fst_    = doc1 "[0]" -- to make things look nice
  snd_    = doc1 "[1]" -- to make things look nice

instance Lambda D where
  lam f   = D $ \x -> let x_n = PP.text "\\x" PP.<> PP.int x in PP.parens $ PP.hsep [x_n, PP.text "->", unD (f (D $ const x_n)) (succ x)]
  app     = liftD2 (PP.<+>)

instance Plus D where
  left_   = doc1 "Left"
  right_  = doc1 "Right"
  either_ = liftD3 (\a b c -> PP.hsep [PP.text "either", a, b, c])

instance Fix D where
  fix f   = D $ \h -> let x = PP.text "x" PP.<> PP.int h in
    PP.hsep [PP.text "fix", unD (f (D $ const x)) (succ h)]

{- ---------------------------------------------------------------
 - Compiler
 - ---------------------------------------------------------------
 -}

newtype C a = C (TExpQ a)
unC :: C a -> TExpQ a
unC (C x) = x

clift1 :: TExpQ (a -> b) -> C a -> C b
clift1 g (C x) = C $ [|| $$g $$x ||]

clift2 :: TExpQ (a -> b -> c) -> C a -> C b -> C c
clift2 g (C x) (C y) = C $ [|| $$g $$x $$y ||]

clift3 :: TExpQ (a -> b -> c -> d) -> C a -> C b -> C c -> C d
clift3 g (C x) (C y) (C z) = C $ [|| $$g $$x $$y $$z ||]

instance Ints C where
  int a   = C [|| a ||]
  neg     = clift1 [|| negate ||]
  add     = clift2 [|| (+) ||]
  mult_   = clift2 [|| (*) ||]

instance Boolean C where
  bool a  = C [|| a ||]
  not_    = clift1 [|| (not) ||]
  and_    = clift2 [|| (&&) ||]
  or_     = clift2 [|| (||) ||]

instance Equality C where
  eq_     = clift2 [|| (==) ||]

instance IntOrder C where
  leq     = clift2 [|| (<=) ||]

instance Conditional C where
  if_     = clift3 [|| if__ ||]

instance Pairs C where
  pair    = clift2 [|| (,) ||]
  fst_    = clift1 [|| (fst) ||]
  snd_    = clift1 [|| (snd) ||]

instance Plus C where
  left_   = clift1 [|| Left ||]
  right_  = clift1 [|| Right ||]
  either_ = clift3 [|| either ||]

instance Lambda C where
  app = clift2 [|| ($) ||]
  lam f = C $ [|| \x -> $$((unC . f . C) [|| x ||]) ||]

instance Fix C where
  fix f = C $ [|| let self n = $$((unC . f . C) [|| self ||]) n in self ||]

{- ---------------------------------------------------------------
 - Tracing Interpreter
 - ---------------------------------------------------------------
 -}
type Level = Int
type VarCounter = Int
newtype T a = T { unT :: Level -> VarCounter -> String }

indent :: Int -> String -> String
indent k s = let n = k * 2 in (replicate n ' ') ++ "->" ++ s ++ "\n"

trace0 :: Show a => String -> a -> T a
trace0 n a = T $ \l _ -> indent l (n ++ " " ++ (show a))

trace1 :: String -> T a1 -> T a
trace1 n a = T $ \l v -> (indent l n) ++ (unT a (succ l) v)

tracel :: String -> String -> (T a1 -> T a2) -> T a
tracel n x f = T $ \l v -> 
  let x' = x ++ (show v) in 
  (indent l (n ++ " " ++ x')) ++ 
  (unT (f (T (\l' _ -> (indent l' x')))) (succ l) (succ v))

trace2 :: String -> T a1 -> T a2 -> T a
trace2 n a1 a2 = T $ \l v -> 
  let l' = (succ l) in 
  (indent l n) ++ (unT a1 l' v) ++ (unT a2 l' v)

trace3 :: String -> T a1 -> T a2 -> T a3 -> T a
trace3 n a1 a2 a3 = T $ \l v -> 
  let l' = (succ l) in 
  (indent l n) ++ (unT a1 l' v) ++ (unT a2 l' v) ++ (unT a3 l' v)

instance Boolean T where
    bool                = trace0 "bool"
    not_                = trace1 "not_"
    and_                = trace2 "and_"
    or_                 = trace2 "or_"

instance Ints T where
    int                 = trace0 "int"
    neg                 = trace1 "neg"
    add                 = trace2 "add"
    mult_               = trace2 "mult_"

instance Pairs T where
    fst_                = trace1 "fst"
    snd_                = trace1 "snd"
    pair                = trace2 "pair"

instance IntOrder T where
    leq                 = trace2 "leq"

instance Plus T where
    left_               = trace1 "left_"
    right_              = trace1 "left_"
    either_             = trace3 "either_"

instance Conditional T where
    if_                 = trace3 "if_"

instance Lambda T where
    lam                 = tracel "lam" "x"
    app                 = trace2 "app"

-- instance Fix skipped - it's like tracel above

--------------------------------------------------------------------------------------
prog_1 :: (Lambda rep, Boolean rep) => rep Bool
prog_1 = app (lam (\x -> x)) (bool True)

prog_2 :: (Lambda rep, Boolean rep) => rep Bool
prog_2 = app (lam (\x -> x)) (app (lam (\y -> y)) (bool True))

prog_3 :: (Lambda rep, Boolean rep) => rep Bool
prog_3 = app (lam (\x -> (and_ x x))) (bool True)

prog_4 :: (Lambda rep, Boolean rep) => rep Bool
prog_4 = app (lam (\x -> (and_ x x))) (bool False)

prog_5 :: (Boolean rep) => rep Bool
prog_5 = and_ (bool True) (bool False)

prog_6 :: (Boolean rep) => rep Bool
prog_6 = or_ (bool True) (bool False)

prog_7 :: (Boolean rep) => rep Bool
prog_7 = not_ (bool True)

prog_8 :: (Ints rep) => rep Int
prog_8 = (int 1)

prog_9 :: (Ints rep) => rep Int
prog_9 = mult_ (int 1) (int 200)

prog_10 :: (Ints rep, Lambda rep) => rep Int
prog_10 = app (lam (\x -> (mult_ x x))) (int 2)

prog_11 :: (IntOrder rep, Ints rep, Lambda rep) => rep Int
prog_11 = neg $ app (lam (\x -> (mult_ x x))) (int 2)

prog_12 :: (IntOrder rep, Ints rep, Lambda rep) => rep Bool
prog_12 = leq (int 10) (neg $ app (lam (\x -> (mult_ x x))) (int 2))

prog_13 :: (IntOrder rep, Ints rep, Lambda rep) => rep Bool
prog_13 = leq (neg $ app (lam (\x -> (mult_ x x))) (int 2)) (int 10)

prog_14 :: (Boolean rep, IntOrder rep, Ints rep, Lambda rep) => rep Bool
prog_14 = not_ $ leq (int 10) (neg $ app (lam (\x -> (mult_ x x))) (int 2))

prog_15 :: (Equality rep, Ints rep) => rep Bool
prog_15 = eq_ (int 1) (int 2)

prog_16 :: (Equality rep, Ints rep) => rep Bool
prog_16 = eq_ (int 1) (int 1)

prog_17 :: (Equality rep, Boolean rep) => rep Bool
prog_17 = eq_ (bool True) (bool True)

prog_18 :: (Equality rep, Boolean rep) => rep Bool
prog_18 = eq_ (bool True) (bool False)

prog_19 :: (Lambda rep, Ints rep) => rep Int
prog_19 = app (lam (\x -> (mult_ x (add x x)))) (int 2)

prog_20 :: (Conditional rep, Ints rep, Boolean rep) => rep Int
prog_20 = if_ (bool False) (int 20) (int 0)

prog_21 :: (Conditional rep, Ints rep, Equality rep) => rep Int
prog_21 = if_ (eq_ (add (int 12) (int 1)) (int 13)) (int 20) (int 0)

prog_22 :: (Pairs rep, Boolean rep, Ints rep) => rep (Bool, Int)
prog_22 = pair (bool True) (int 1)

prog_23 :: (Pairs rep, Boolean rep, Ints rep) => rep Bool
prog_23 = fst_ $ pair (bool True) (int 1)

prog_24 :: (Pairs rep, Boolean rep, Ints rep) => rep Int
prog_24 = snd_ $ pair (bool True) (int 1)

prog_25 :: (Lambda rep, Ints rep) => rep Int
prog_25 = app (lam (\x -> mult_ x x)) (app (lam (\x -> mult_ x x)) (int 2))

prog_26 :: (Lambda rep, Conditional rep, Equality rep, Ints rep) => rep Int
prog_26 = if_ (eq_ (add (int 1) (int 2)) (int 3)) (app (lam (\x -> (mult_ x x))) (int 3)) (int 0)

prog_27 :: (Conditional rep, Lambda rep, Equality rep, Ints rep) => rep Int
prog_27 = if_ prog_16 prog_25 prog_26

prog_28 :: (Ints rep, Lambda rep) => rep Int
prog_28 = app (lam (\x -> mult_ x (app (lam (\y -> y)) (int 1)))) (int 2)

prog_29 :: (Lambda rep, Ints rep) => rep (Int -> Int)
prog_29 = lam (\x -> mult_ x (app (lam (\y -> y)) (int 1)))

prog_30 :: (Boolean rep, Ints rep, Pairs rep) => rep Int
prog_30 = mult_ (int 3) (fst_ (pair (int 1) (bool False)))

prog_31 :: (Lambda rep) => rep (rep a -> rep a)
prog_31 = lam (\x -> x)

prog_32 :: (Lambda rep, Pairs rep) => rep ((a , b) -> (b, a))
prog_32 = lam (\x -> pair (snd_ x) (fst_ x))

prog_33 :: (Pairs rep) => rep (a, b) -> rep (b, a)
prog_33 = \x -> pair (snd_ x) (fst_ x)

testgib :: (Lambda rep, Fix rep, Conditional rep, IntOrder rep, Ints rep) =>
  () -> rep (Int -> Int -> Int -> Int)
testgib () = lam (\x -> lam (\y ->
                  fix (\self -> lam (\n ->
                      if_ (leq n (int 0)) x
                        (if_ (leq n (int 1)) y
                         (add (app self (add n (int (-1))))
                              (app self (add n (int (-2))))))))))

testgib1 :: (Lambda rep, Fix rep, Conditional rep, IntOrder rep, Ints rep) =>
  () -> rep Int
testgib1 () = app (app (app (testgib ()) (int 1)) (int 1)) (int 5)

testgib2 :: (Lambda rep, Fix rep, Conditional rep, IntOrder rep, Ints rep) =>
  () -> rep (Int -> Int -> Int)
testgib2 () = lam (\x -> (lam (\y ->app (app (app (testgib ()) x) y) (int 5))))

testpowfix :: (Lambda rep, Fix rep, Conditional rep, IntOrder rep, Ints rep) =>
  () -> rep (Int -> Int -> Int)
testpowfix () = lam (\x ->
                      fix (\self -> lam (\n ->
                        if_ (leq n (int 0)) (int 1)
                            (mult_ x (app self (add n (int (-1))))))))

testpowfix7 :: (Lambda rep, Fix rep, Conditional rep, IntOrder rep, Ints rep) =>
                     () -> rep (Int -> Int)
testpowfix7 () = lam (\x -> app (app (testpowfix ()) x) (int 7))

itest :: (() -> R a) -> a
itest f = unR (f ())

--------------------------------------------------------------------------------

---------------------------------------------------------------------
-- The classes that make a partial evaluator 'work better'

class Lambda2 rep where
  lam'     :: (rep sa da -> rep sb db)  -> rep (rep sa da -> rep sb db) (da -> db)
  app'     :: rep (rep sa da -> rep sb db) (da -> db) -> rep sa da -> rep sb db

class Boolean2 rep where
  bool'    :: Bool                 -> rep Bool Bool
  not'     :: rep Bool Bool        -> rep Bool Bool
  and'     :: rep Bool Bool        -> rep Bool Bool        -> rep Bool Bool
  or'      :: rep Bool Bool        -> rep Bool Bool        -> rep Bool Bool

class Ints2 rep where
  int'     :: Int                  -> rep Int Int
  neg'     :: rep Int Int          -> rep Int Int
  add'     :: rep Int Int          -> rep Int Int          -> rep Int Int
  mult'    :: rep Int Int          -> rep Int Int          -> rep Int Int

class IntOrder2 rep where
  leq'     :: rep Int Int          -> rep Int Int          -> rep Bool Bool

class Conditional2 rep where
  if'      :: rep Bool Bool        -> rep s d              -> rep s d      -> rep s d

class Pairs2 rep where
  pair'    :: rep sa da             -> rep sb db               -> rep (sa, sb) (da, db)
  fst'     :: Lift a => rep (a, b) (a, b) -> rep a a
  snd'     :: Lift b => rep (a, b) (a, b) -> rep b b

class Equality2 rep where
  eq'      :: Eq a => rep a a      -> rep a a               -> rep Bool Bool

class Plus2 rep where
  left'    :: rep sa da               -> rep (Either sa sb) (Either da db)
  right'   :: rep sb db               -> rep (Either sa sb) (Either da db)
  either'  :: (Lift a, Lift b) => 
              rep (rep a a -> rep c c) (a -> c) -> rep (rep b b -> rep c c) (b -> c) -> rep (Either a b) (Either a b)  -> rep c c

class Fix2 rep where
  fix'     :: (rep (sa -> sb) (da -> db) -> rep (sa -> sb) (da -> db))     -> rep (sa -> sb) (da -> db)

-- a simplification here: since R is the identity wrapper, omit it
data P static dynamic = 
    P { dynamic :: C dynamic, static :: Maybe static }

stat :: (static -> C dynamic) -> static -> P static dynamic
stat f b = P (f b) (Just b)

dyna :: C dynamic -> P static dynamic
dyna d = P d Nothing

liftP1 :: (b -> C b) -> (a -> b) -> (C a -> C b) -> P a a -> P b b
liftP1 l f _ (P _ (Just x)) = stat l (f x)
liftP1 _ _ g (P y _       ) = dyna $ g y

liftP2 :: (c -> C c) -> (a -> b -> c) -> (C a -> C b -> C c) -> P a a -> P b b -> P c c
liftP2 l f _ (P _ (Just x)) (P _ (Just y)) = P (l $ f x y) (Just $ f x y)
liftP2 _ _ g (P x _       ) (P y _       ) = dyna $ g x y

-- inspired from the last paper we did
unital :: Eq static => (static -> C dynamic) -> 
  (static -> static -> static) -> 
  (C dynamic -> C dynamic -> C dynamic) -> 
  static -> 
  (P static dynamic -> P static dynamic -> P static dynamic)
unital l f _ _ (P _ (Just a)) (P _ (Just b))          = stat l (f a b)
unital _ _ _ u (P _ (Just a))  b             | a == u = b
unital _ _ _ u  a             (P _ (Just b)) | b == u = a
unital _ _ g _ (P a _)        (P b _)                 = dyna (g a b)

instance Lambda2 P where
  lam' f = P (lam (dynamic . f . dyna)) (Just f)
  app' (P _ (Just f)) = f
  app' (P f _       ) = dyna . app f . dynamic

instance Boolean2 P where
  bool' = stat bool
  not'  = liftP1 bool not not_
  and'  = unital bool (&&) and_ True
  or'   = unital bool (||) or_  False

instance Ints2 P where
  int' = stat int
  neg' = liftP1 int negate neg 
  add' = unital int (+) add 0
  mult' = unital int (*) mult_ 1

instance IntOrder2 P where
  leq' = liftP2 bool (<=) leq

instance Equality2 P where
  eq'  = liftP2 bool (==) eq_

instance Conditional2 P where
  if' (P _ (Just a)) et ee = if a then et else ee
  if' (P a _)        et ee = dyna (if_ a (dynamic et) (dynamic ee))

-- we can't use liftP2 here, but a direct implementation works
-- the point is that a and b will be as simplified as possible already
instance Pairs2 P where
  pair' (P a (Just x)) (P b (Just y)) = P (pair a b) (Just (x , y))
  pair' (P a _       ) (P b _       ) = dyna (pair a b)
  fst'  (P _ (Just x))                = P (C $ THS.liftTyped $ fst x) (Just (fst x))
  fst'  (P a _       )                = dyna (fst_ a)
  snd'  (P _ (Just x))                = P (C $ THS.liftTyped $ snd x) (Just (snd x))
  snd'  (P a _       )                = dyna (snd_ a)

instance Plus2 P where
  left' (P a (Just x))                 = P (left_ a) (Just (Left x))
  left' (P a _       )                 = dyna (left_ a)
  right' (P a (Just x))                = P (right_ a) (Just (Right x))
  right' (P a _       )                = dyna (right_ a)
  either' (P _ (Just f)) _ (P _ (Just (Left x))) = f (P (C $ THS.liftTyped x) (Just x))
  either' _ (P _ (Just f)) (P _ (Just (Right x))) = f (P (C $ THS.liftTyped x) (Just x))
  either' (P f _) (P g _) (P x _)                 = dyna $ either_ f g x

instance Fix2 P where
  fix' f = case (f (fix' f)) of
         (P _ (Just s)) -> P dfix (Just s)
         _              -> dyna dfix
       where dfix = fix (dynamic . f . dyna)
-------------------------------------------------------------------------------------------

prog_1' :: (Lambda2 rep, Boolean2 rep) => () -> rep Bool Bool
prog_1' () = app' (lam' (\x -> x)) (bool' True)
-- GHC.Types.True
prog_2' :: (Lambda2 rep, Boolean2 rep) => () -> rep Bool Bool
prog_2' () = app' (lam' (\x -> x)) (app' (lam' (\y -> y)) (bool' True))
-- GHC.Types.True
prog_3' :: (Lambda2 rep, Boolean2 rep) => () -> rep Bool Bool
prog_3' () = app' (lam' (\x -> (and' x x))) (bool' True)
-- GHC.Types.True
prog_4' :: (Lambda2 rep, Boolean2 rep) => () -> rep Bool Bool
prog_4' () = app' (lam' (\x -> (and' x x))) (bool' False)
-- GHC.Types.False
prog_5' :: (Boolean2 rep) => () -> rep Bool Bool
prog_5' () = and' (bool' True) (bool' False)
-- GHC.Types.False
prog_6' :: (Boolean2 rep) => () -> rep Bool Bool
prog_6' () = or' (bool' True) (bool' False)
-- GHC.Types.True
prog_7' :: (Boolean2 rep) => () -> rep Bool Bool
prog_7' () = not' (bool' True)
-- GHC.Types.False
prog_8' :: (Ints2 rep) => () -> rep Int Int
prog_8' () = (int' 1)
-- 1
prog_9' :: (Ints2 rep) => () -> rep Int Int
prog_9' () = mult' (int' 2) (int' 100)
-- 200
prog_10' :: (Ints2 rep, Lambda2 rep) => () -> rep Int Int
prog_10' () = app' (lam' (\x -> (mult' x x))) (int' 2)
-- 4
prog_11' :: (Ints2 rep, Lambda2 rep) => () -> rep Int Int
prog_11' () = neg' $ app' (lam' (\x -> (mult' x x))) (int' 2)
-- -4
prog_12' :: (IntOrder2 rep, Ints2 rep, Lambda2 rep) => () -> rep Bool Bool
prog_12' () = leq' (int' 10) (neg' $ app' (lam' (\x -> (mult' x x))) (int' 2))
-- GHC.Types.False
prog_13' :: (IntOrder2 rep, Ints2 rep, Lambda2 rep) => () -> rep Bool Bool
prog_13' () = leq' (neg' $ app' (lam' (\x -> (mult' x x))) (int' 2)) (int' 10)
-- GHC.Types.True
prog_14' :: (Boolean2 rep, IntOrder2 rep, Ints2 rep, Lambda2 rep) => () -> rep Bool Bool
prog_14' () = not' $ leq' (int' 10) (neg' $ app' (lam' (\x -> (mult' x x))) (int' 2))
-- GHC.Types.True
prog_15' :: (Equality2 rep, Ints2 rep) => () -> rep Bool Bool
prog_15' () = eq' (int' 1) (int' 2)
-- GHC.Types.False
prog_16' :: (Equality2 rep, Ints2 rep) => () -> rep Bool Bool
prog_16' () = eq' (int' 1) (int' 1)
-- GHC.Types.True
prog_17' :: (Equality2 rep, Boolean2 rep) => () -> rep Bool Bool
prog_17' () = eq' (bool' True) (bool' True)
-- GHC.Types.True
prog_18' :: (Equality2 rep, Boolean2 rep) => () -> rep Bool Bool
prog_18' () = eq' (bool' True) (bool' False)
-- GHC.Types.False
prog_19' :: (Lambda2 rep, Ints2 rep) => () -> rep Int Int
prog_19' () = app' (lam' (\x -> (mult' x (add' x x)))) (int' 2)
-- 8
prog_20' :: (Conditional2 rep, Ints2 rep, Boolean2 rep) => () -> rep Int Int
prog_20' () = if' (bool' False) (int' 20) (int' 0)
-- 0
prog_21' :: (Conditional2 rep, Ints2 rep, Equality2 rep) => () -> rep Int Int
prog_21' () = if' (eq' (add' (int' 12) (int' 1)) (int' 13)) (int' 20) (int' 0)
-- 20
prog_22' :: (Pairs2 rep, Boolean2 rep, Ints2 rep) => () -> rep (Bool, Int) (Bool, Int)
prog_22' () = pair' (bool' True) (int' 1)
-- GHC.Tuple.(,) GHC.Types.True 1
prog_23' :: (Pairs2 rep, Boolean2 rep, Ints2 rep) => () -> rep Bool Bool
prog_23' () = fst' $ pair' (bool' True) (int' 1)
-- GHC.Types.True
prog_24' :: (Pairs2 rep, Boolean2 rep, Ints2 rep) => () -> rep Int Int
prog_24' () = snd' $ pair' (bool' True) (int' 1)
-- 1
prog_25' :: (Lambda2 rep, Ints2 rep) => () -> rep Int Int
prog_25' () = app' (lam' (\x -> mult' x x)) (app' (lam' (\x -> mult' x x)) (int' 2))
-- 16
prog_26' :: (Lambda2 rep, Conditional2 rep, Equality2 rep, Ints2 rep) => () -> rep Int Int
prog_26' () = if' (eq' (add' (int' 1) (int' 2)) (int' 3)) (app' (lam' (\x -> (mult' x x))) (int' 3)) (int' 0)
-- 9
prog_27' :: (Conditional2 rep, Lambda2 rep, Equality2 rep, Ints2 rep) => () -> rep Int Int
prog_27' () = if' (prog_16' ()) (prog_25' ()) (prog_26' ())
-- 16
prog_28' :: (Ints2 rep, Lambda2 rep) => () -> rep Int Int
prog_28' () = app' (lam' (\x -> mult' x (app' (lam' (\y -> y)) (int' 1)))) (int' 2)
-- 2
prog_29' :: (Lambda2 rep, Ints2 rep) => () -> rep (rep Int Int -> rep Int Int) (Int -> Int) --(Lambda2 rep, Ints2 rep) => () -> rep (Int -> Int) (Int -> Int)
prog_29' () = lam' (\x -> mult' x (app' (lam' (\y -> y)) (int' 1)))
-- \x_0 -> x_0
prog_30' :: (Boolean2 rep, Ints2 rep, Pairs2 rep) => () -> rep Int Int
prog_30' () = mult' (int' 3) (fst' (pair' (int' 1) (bool' False)))
-- 3
prog_31' :: Lambda2 rep => () -> rep (rep sb db -> rep sb db) (db -> db)
prog_31' () = lam' (\x -> x)
-- \x_0 -> x_0
prog_32' :: (Lambda2 rep, Pairs2 rep, Lift sb1, Lift sb2) => () -> rep (rep (sb1, sb2) (sb1, sb2) -> rep (sb2, sb1) (sb2, sb1)) ((sb1, sb2) -> (sb2, sb1))
prog_32' () = lam' (\x -> pair' (snd' x) (fst' x))
-- doesn't print?
prog_33' :: (Lift a, Lift b, Pairs2 rep) => () -> rep (a, b) (a, b) -> rep (b, a) (b, a)
prog_33' () = \x -> pair' (snd' x) (fst' x)
-- test with 
-- ptest (\() -> prog_33' () (pair' (int' 5) (bool' True)))
-- GHC.Tuple.(,) GHC.Types.True 5
prog_34' :: (Plus2 rep, Ints2 rep) => () -> rep (Either Int (rep sb db)) (Either Int db)
prog_34' () = left' (int' 10)
-- Data.Either.Left 10
prog_35' :: (Plus2 rep, Ints2 rep, Lambda2 rep) => () -> rep Int Int
prog_35' () = either' (lam' (\x -> neg' x)) (lam' (\x -> mult' (int' 10) x)) (left' (int' 10))
-- -10
prog_36' :: (Plus2 rep, Ints2 rep, Lambda2 rep) => () -> rep Int Int
prog_36' () = either' (lam' (\x -> neg' x)) (lam' (\x -> mult' (int' 10) x)) (right' (int' 365))
-- 3650
prog_37' :: (Lambda2 rep, Ints2 rep) => () -> rep (rep Int Int -> rep Int Int) (Int -> Int)
prog_37' () = lam' (\x -> add' x (mult' (int' 2) (int' 100)))
-- \x_0 -> (GHC.Num.+) x_0 200
prog_38' :: (Lambda2 rep, Ints2 rep) => () -> rep (rep Int Int -> rep Int Int) (Int -> Int)
prog_38' () = lam' (\x -> add' (add' (int' 1) (int' 3)) (add' x (mult' (int' 2) (int' 100))))
-- \x_0 -> (GHC.Num.+) 4 ((GHC.Num.+) x_0 200)

-- itest testpowfix 2 3 -- should be 8

-- use
printcode :: Quasi f => (() -> C a) -> f THPP.Doc
printcode f = fmap (ppr . unType) $ runQ (unC $ f ())
-- to see one of the tests above as Haskell. Not necessarily nice!

-- we have to rewrite our tests (boo) in the new mode

-- get the code part
ptest :: Quasi f => (() -> P static dynamic) -> f THPP.Doc
ptest f = printcode (\() -> dynamic (f ()))

testgib' :: (Lambda2 rep, Fix2 rep, Conditional2 rep, IntOrder2 rep, Ints2 rep) =>
 () -> rep (rep Int Int -> rep (rep Int Int -> rep (rep Int Int -> rep Int Int)
           (Int -> Int))
           (Int -> Int -> Int)) (Int -> Int -> Int -> Int)   
testgib' () = lam' (\x -> lam' (\y ->
                  fix' (\self -> lam' (\n ->
                      if' (leq' n (int' 0)) x
                        (if' (leq' n (int' 1)) y
                         (add' (app' self (add' n (int' (-1))))
                              (app' self (add' n (int' (-2))))))))))

testgib1' :: (Lambda2 rep, Fix2 rep, Conditional2 rep, IntOrder2 rep, Ints2 rep) =>
  () -> rep Int Int
testgib1' () = app' (app' (app' (testgib' ()) (int' 1)) (int' 1)) (int' 5)
-- 8

testgib2' :: (Lambda2 rep, Fix2 rep, Conditional2 rep, IntOrder2 rep, Ints2 rep) =>
  () -> rep (rep Int Int -> rep (rep Int Int -> rep Int Int) (Int -> Int)) (Int -> Int -> Int)
testgib2' () = lam' (\x -> (lam' (\y -> app' (app' (app' (testgib' ()) x) y) (int' 5))))
-- \x_0 -> \x_1 -> (GHC.Num.+) ((GHC.Num.+) ((GHC.Num.+) ((GHC.Num.+) x_1 x_0) 
-- x_1) ((GHC.Num.+) x_1 x_0)) ((GHC.Num.+) ((GHC.Num.+) x_1 x_0) x_1)

testpowfix' :: (Lambda2 rep, Fix2 rep, Conditional2 rep, IntOrder2 rep, Ints2 rep) =>
  () -> rep (rep Int Int -> rep (rep Int Int -> rep Int Int) (Int -> Int)) (Int -> Int -> Int)
testpowfix' () = lam' (\x ->
                      fix' (\self -> lam' (\n ->
                        if' (leq' n (int' 0)) (int' 1)
                            (mult' x (app' self (add' n (int' (-1))))))))
-- \x_0 -> let self_1 n_2 = (\x_3 -> Tagless.if__ ((GHC.Classes.<=) x_3 0) 1 
-- ((GHC.Num.*) x_0 ((GHC.Base.$) self_1 ((GHC.Num.+) x_3 (-1))))) n_2
--         in self_1

testpowfix7' :: (Lambda2 rep, Fix2 rep, Conditional2 rep, IntOrder2 rep, Ints2 rep) =>
                     () -> rep (rep Int Int -> rep Int Int) (Int -> Int)
testpowfix7' () = lam' (\x -> app' (app' (testpowfix' ()) x) (int' 7))
-- \x_0 -> (GHC.Num.*) x_0 
-- ((GHC.Num.*) x_0 ((GHC.Num.*) x_0 ((GHC.Num.*) x_0 
-- ((GHC.Num.*) x_0 ((GHC.Num.*) x_0 x_0)))))
-- 



















-- SPOILERS !!!
{-
instance Lambda2 P where
  lam' f = P (lam (dynamic . f . dyna)) (Just f)
  app' (P _ (Just f)) = f
  app' (P f _       ) = dyna . app f . dynamic

instance Fix2 P where
  fix' f = case f (fix' f) of
             (P _ (Just s)) -> P dynfix (Just s)
             _              -> dyna dynfix
           where dynfix = fix (dynamic . f . dyna)
-}
