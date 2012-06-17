-- Date: April 2012
-- Author: Jan Malakhovski
-- For TTFV: http://oxij.org/activity/ttfv/

-- Everything here is in Public Domain.

module PrimitiveAgda where

-- ≡ is \==
-- Martin-Lof equivalence on values.
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Properties.
≡-refl : {A : Set}{a b : A}
       → a ≡ b → b ≡ a
≡-refl refl = refl

≡-trans : {A : Set}{a b c : A}
        → a ≡ b → b ≡ c → a ≡ c
≡-trans refl refl = refl

_~_ : {A : Set}{a b c : A}
    → a ≡ b → b ≡ c → a ≡ c
_~_ = ≡-trans

cong : {A B : Set}{a b : A}
     → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

-- ⊥ is \bot
-- Empty type.
data ⊥ : Set where

-- Absurd implies anything.
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- ⊤ is \top
-- One element type.
record ⊤ : Set where
  constructor tt

-- Every type could be squashed into the one element type.
⊤-intro : {A : Set} → A → ⊤
⊤-intro _ = tt
  
-- Booleans.
data Bool : Set where
  true false : Bool

-- Magic!
isTrue : Bool -> Set
isTrue false = ⊥
isTrue true = ⊤

-- ℕ is \bn
-- Naturals.
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- ≠ is \ne
-- Not zero
≠zero : ℕ → Bool
≠zero zero = false
≠zero (succ n) = true

---------------------------------------------------------
-- Example usage of the magic.

constifsnd≠zero : (a : ℕ) → (b : ℕ) → { x : isTrue (≠zero b) } → ℕ
constifsnd≠zero a zero {()}
constifsnd≠zero a (succ b) = a 

--------------------------------------------------------

-- ∘ is \o
-- λ is \lambda
-- Most abstract (and scary) way to type a function composition.
_∘_ : {A : Set}{B : A → Set}{C : {x : A} → B x → Set}
    → (f : {x : A} → (y : B x) → C y) → (g : (x : A) → B x) → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

-- ∘ could be viewed as a proof of transitivity of the implication.
impl-trans : {A B C : Set}
           → (A → B) → (B → C) → (A → C)
impl-trans f g = g ∘ f

-- ¬ is \lnot
-- Logical negation.
¬ : Set → Set
¬ a = a → ⊥

-- If A implies B then not B implies not A.
¬impl : {A B : Set} → (A → B) → (¬ B → ¬ A)
¬impl {A} {B} AB ¬B AA = ¬B (AB AA)

-- Contradiction implies anything.
contradiction : {A B : Set} → A → ¬ A → B
contradiction {A} {B} a ¬a = ⊥-elim {B} (¬a a)

-------------------------------------------

-- Sum of two naturals.
_+_ : ℕ → ℕ → ℕ
_+_ zero a = a
_+_ (succ a) b = succ (a + b)

-- Operations' associativity and priorities to make Agda's parser happy.
infixl 10 _~_
infix 10 _≡_
infixl 20 _+_

-- Properties.
lemma-succ : {x y : ℕ} → x ≡ y → succ x ≡ succ y
lemma-succ refl = refl

lemma-unsucc : {x y : ℕ} → succ x ≡ succ y → x ≡ y
lemma-unsucc refl = refl

assoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
assoc zero y z = refl
assoc (succ x) y z = lemma-succ (assoc x y z)

y=y+0 : (y : ℕ) → y ≡ y + zero
y=y+0 zero = refl
y=y+0 (succ y) = cong succ (y=y+0 y)

sy=y+1 : (y : ℕ) → succ y ≡ y + succ zero
sy=y+1 zero = refl
sy=y+1 (succ y) = cong succ (sy=y+1 y)

sx+y=x+sy : (x y : ℕ) → succ x + y ≡ x + succ y
sx+y=x+sy zero y = refl
sx+y=x+sy (succ x) y = cong succ (sx+y=x+sy x y)

-- (*) Commutativity.
comm : (x y : ℕ) → x + y ≡ y + x
comm zero y = y=y+0 y
comm x zero = ≡-refl (y=y+0 x)
comm x (succ y) = ≡-refl (sx+y=x+sy x y) ~ cong succ (comm x y)

-- Define multiplication:
infixl 30 _*_
_*_ : ℕ → ℕ → ℕ
zero * y = zero
succ x * y = y + x * y

-- (**) Prove its properties:
lemma-plus : (x y z : ℕ) → x ≡ y → x + z ≡ y + z
lemma-plus x y zero x≡y = ≡-refl (y=y+0 x) ~ x≡y ~ y=y+0 y
lemma-plus x y (succ z) x≡y = 
           ≡-refl (sx+y=x+sy x z) ~ 
           ≡-refl (≡-refl (sx+y=x+sy y z) ~ 
           cong succ (≡-refl (lemma-plus x y z x≡y)))

lemma-unplus : (x y z : ℕ) → x + z ≡ y + z → x ≡ y
lemma-unplus x y zero x+z≡y+z = y=y+0 x ~ ≡-refl (y=y+0 y ~ ≡-refl x+z≡y+z)
lemma-unplus x y (succ z) x+sz≡y+sz = 
             lemma-unplus x y z
             (lemma-unsucc (sx+y=x+sy x z ~ 
                           x+sz≡y+sz ~ 
                           ≡-refl (sx+y=x+sy y z)))

lemma-plus2 : (x y z : ℕ) → y ≡ z → x + y ≡ x + z
lemma-plus2 zero y z y≡z = y≡z
lemma-plus2 (succ x) y z y≡z = cong succ (lemma-plus2 x y z y≡z)

lemma-plus3 : (a b c d : ℕ) → a ≡ b → c ≡ d → a + c ≡ b + d
lemma-plus3 a b c d a≡b c≡d = 
            lemma-plus2 a c d c≡d ~ 
            lemma-plus a b d a≡b

distrib : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
distrib zero y z = refl
distrib (succ x) y z = cong (λ a → z + a) (distrib x y z) ~ assoc z (x * z) (y * z)

0=y*0 : (y : ℕ) → zero ≡ y * zero
0=y*0 zero = refl
0=y*0 (succ y) = 0=y*0 y

lemma-mul : (x y z : ℕ) → y ≡ z → x * y ≡ x * z
lemma-mul zero y z y≡z = refl
lemma-mul (succ x) y z y≡z = 
          lemma-plus3 y z (x * y) (x * z) y≡z 
            (lemma-mul x y z y≡z)

distrib2 : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
distrib2 zero y z = refl
distrib2 (succ x) y z = 
         ≡-refl (assoc y z (x * (y + z))) ~ 
         ≡-refl (≡-refl (assoc y (x * y) (z + x * z)) ~ 
           lemma-plus2 y (x * y + (z + x * z)) (z + x * (y + z)) 
           (comm (x * y) (z + x * z) ~ 
             (≡-refl (assoc z (x * z) (x * y)) ~ 
             lemma-plus2 z (x * z + x * y) (x * (y + z)) 
               (comm (x * z) (x * y) ~ 
                 ≡-refl (distrib2 x y z)))))

assoc* : (x y z : ℕ) → x * (y * z) ≡ (x * y) * z
assoc* zero y z = refl
assoc* (succ x) y z = ≡-refl (distrib y (x * y) z ~ cong (λ a → y * z + a) (≡-refl (assoc* x y z)))

y=y*1 : (y : ℕ) → y ≡ y * (succ zero)
y=y*1 zero = refl
y=y*1 (succ y) = cong succ (y=y*1 y)

comm* : (x y : ℕ) → x * y ≡ y * x
comm* zero zero = refl
comm* zero (succ y) = comm* zero y
comm* (succ x) y = impl-trans (_~_ (≡-refl (comm* y (succ x)))) (λ z → z) refl
{-comm* zero y = 0=y*0 y
comm* (succ x) y = 
      ≡-refl (cong (λ a → y * a) (sy=y+1 x) ~
      ≡-refl (cong (λ a → y + a) (comm* x y) ~
      (lemma-plus y (y * succ zero) (y * x) (y=y*1 y)) ~ 
        (comm (y * succ zero) (y * x) ~ 
        ≡-refl (distrib2 y x (succ zero)))))
-}
data ℤ : Set where
  zero : ℤ
  pos : ℕ → ℤ
  neg : ℕ → ℤ

_+ℤ_ : ℤ → ℤ → ℤ
_+ℤ_ a b = {!!}

-------------------------------------------
-- Emulating type classes.

-- Interface. Almost Haskell's "class" keyword
record Summable (A : Set) : Set where
  field
    _+'_ : A → A → A

-- Haskell: (Summable A) => A -> A -> A
abstractSum : ∀ {A} → (Summable A) → A → A → A
abstractSum s = _+'_ where
  open Summable s
-- But! In Haskell Summable is not just an argument, it is inferenced.

-- Taking Summable A from a context of a call with "instance arguments"
-- available in the recent versions of Agda:
abstractSum' : ∀ {A} → {{s : Summable A}} → A → A → A
abstractSum' {{s}} = _+'_ where
  open Summable s

-- Inferencing with bare hands:

-- Hidden details (not visible in Haskell).
data What : Set where
  bool nat : What

-- Reversable total function.
W : What -> Set
W bool = Bool
W nat = ℕ

-- If you give me a name of a type I'll give you an implementation of the interface.
-- Almost like Haskell's "instance" declaration.
getSummable : (x : What) → Summable (W x)
getSummable bool = record { _+'_ = (λ x y -> x) }
getSummable nat = record { _+'_ = (λ x y -> y) }

-- Magic!
abstractSum'' : {x : What} → W x → W x → W x
abstractSum'' {x} = abstractSum {A = W x} (getSummable x)

-------------------------------------------

-- Maybes (optional values).
data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

-- Categorical sum.
data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B
  
-- ∷ is \::
-- Lists.
infix 9 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

length : ∀ {A} → List A → ℕ
length [] = zero
length (a ∷ as) = succ (length as)
  
-- Lists of known length (vectors).
data Vec (A : Set) : ℕ → Set where
  [0] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

head : ∀ {A n} → Vec A (succ n) → A
head (a :: as) = a

tail : ∀ {A n} → Vec A (succ n) → Vec A n
tail (a :: as) = as

-- Finite type. Each Fin n has exactly n elements.
data Fin : ℕ → Set where
  fzero : Fin (succ zero)
  fsucc : ∀ {n} → Fin n → Fin (succ n)

-- Get an element from a Vec by its number.
lookup : ∀ {A n} → Fin n → Vec A n → A
lookup fzero V = head V
lookup (fsucc n) V = lookup n (tail V)

-- try this:
-- test1 = head [0]

list2vec : ∀ {A} → (l : List A) → Vec A (length l)
list2vec [] = [0]
list2vec (a ∷ as) = a :: (list2vec as)

vec2list : ∀ {A} {n : ℕ} → Vec A n → List A
vec2list [0] = []
vec2list (x :: xs) = x ∷ vec2list xs 

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst : ∀ {A B} → A × B → A
fst (a , b) = a

snd : ∀ {A B} → A × B → B
snd (a , b) = b

infix 2 _,_
infixl 15 _×_
  
data _<_ : ℕ → ℕ → Set where
  z<s : {n : ℕ} → zero < succ n
  s<s  : {n m : ℕ} → n < m → succ n < succ m

-- ≤ is \le
_≤_ : ℕ → ℕ → Set
a ≤ b = Either (a ≡ b) (a < b)

-- (**) if you give me a list and a proof that its length is less than n
-- i'll give you a tuple (prefix of length n, suffix)
cuthead : ∀ {a} {n : ℕ} → (l : List a) → n ≤ length l → Vec a n × List a
cuthead {a} {zero} l n≤lenl = [0] , l
cuthead {a} {succ n} l n≤lenl = {!!} :: fst {!!} , snd {!!}

-- (***) previous definition is not total (e.g. you can make up any suffix).
-- define a better one.
-- you may need to define the subtraction with the following property:
--   ∀ a b → a ≤ b → a - b ≡ 0
-- splitn : ∀ {a} {n : ℕ} → ? → vec a n × ?

--infix 7 _⊂_
--data _⊂_ {A : Set} : List A → List A → Set where
--  stop : [] ⊂ [] 
--  drop : ∀ {xs : List A}{y : A}{ys : List A} ⇢ xs ⊂ ys → xs ⊂ (y ∷ ys)
--  keep : ∀ {x xs ys} ⇢ xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
