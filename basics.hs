data Nat = Zero | Succ Nat 

len :: Nat -> Int
len Zero = 0
len (Succ a) = 1 + len a

instance Show Nat where
    show a = show $ len a

zero = \s -> \z -> z
succ' = \n -> \s -> \z -> s (n s z)

plus = \n -> \m -> \s -> \z -> n s (m s z)
mult = \n -> \m -> \s -> n (m s)
power = \n -> \m -> m n

true = \a -> \b -> a
false = \a -> \b -> b

if' = \p -> \f -> \g -> p f g

isZero = \n -> n (\c -> false) true

pair = \a -> \b -> \t -> t a b
fst' = \p -> p true
snd' = \p -> p false

pred' = \n -> (snd' (n (\p -> (pair (succ' (fst' p)) (fst' p))) (pair zero zero))) 

minus = \n -> \m -> m pred' n

one = succ' zero
two = succ' one
three = succ' two
four = succ' three

seven = plus three four
twentyeight = mult seven four
fiftysix = mult twentyeight two
fiftyfive = pred' fiftysix
six = pred' seven
--ololo = pred' (pred' six) --minus seven three
ololo2 = (\s -> \z -> (s (s z))) pred' six

main = do print $ ololo2 Succ Zero
