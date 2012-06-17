module Tutorial where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

infixl 40 _+_
_+_ : ℕ → ℕ → ℕ 
zero + m = m
succ n + m = succ (n + m)

infixl 60 _*_
_*_ : ℕ → ℕ → ℕ
zero * m = zero 
succ n * m = m + n * m

infixl 20 _∨_
_∨_ : Bool → Bool → Bool
true ∨ _ = true
false ∨ x = x

infix 5 if_then_else_
if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

infixr 40 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

id : {A : Set} → A → A
id x = x

-- f : B → C
-- g : A → B
-- f ∘ g : A → C
infixr 100 _∘_
_∘_ : {A : Set}{A→B : A → Set}{A→B→C : (x : A) → A→B x → Set}
  (f : {x : A}(y : A→B x) → A→B→C x y) → 
  (g : (x : A) → A→B x) → 
  (x : A) →
  A→B→C x (g x)
(f ∘ g) x = f (g x)

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

head : {A : Set}{n : ℕ} → Vec A (succ n) → A
head (x ∷ xs) = x

data Image_∋_ {A B : Set}(f : A → B) : B → Set where
  im : (x : A) → Image f ∋ f x

inv : {A B : Set}(f : A → B)(y : B) → Image f ∋ y → A
inv f .(f x) (im x) = x

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (succ zero)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)

magic : {A : Set} → Fin zero → A
magic ()

data Empty : Set where
  empty : Fin zero → Empty

magic' : {A : Set} → Empty → A
magic' (empty ())

_!_ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
[] ! ()
(x ∷ xs) ! fzero = x
(x ∷ xs) ! (fsucc i) = xs ! i

data False : Set where
record True : Set where

isTrue : Bool → Set
isTrue true = True
isTrue false = False

_<_ : ℕ → ℕ → Bool
_ < zero = false
zero < (succ n) = true
succ n < succ m = n < m

length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = succ (length xs)

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

data _≤_ : ℕ → ℕ → Set where
  ≤-zero : {n : ℕ} → zero ≤ n
  ≤-succ : {n m : ℕ} → n ≤ m → succ n ≤ succ m

≤-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans ≤-zero _ = ≤-zero
≤-trans (≤-succ a-1≤b-1) (≤-succ b-1≤c-1) = ≤-succ (≤-trans a-1≤b-1 b-1≤c-1)

min : ℕ → ℕ → ℕ 
min x y with x < y
... | true = x
... | false = y

filter : {A : Set} → (A → Bool) → List A → List A
filter _ [] = []
filter p (x ∷ xs) with p x
... | true = x ∷ filter p xs
... | false = filter p xs

data _≠_ : ℕ → ℕ → Set where
  z≠s : {n : ℕ} → zero ≠ n
  s≠z : {n : ℕ} → n ≠ zero
  s≠s : {n m : ℕ} → n ≠ m → succ n ≠ succ m

data Equal? (n m : ℕ) : Set where
  eq : n ≡ m → Equal? n m
  neq : n ≠ m → Equal? n m

equal? : (n m : ℕ) → Equal? n m 
equal? zero zero = eq refl
equal? zero (succ m) = neq z≠s
equal? (succ n) zero = neq s≠z
equal? (succ n) (succ m) with equal? n m
equal? (succ n) (succ .n) | eq refl = eq refl
... | neq n≠m = neq (s≠s n≠m)

infix 20 _⊆_ 
data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  drop : ∀ {xs y ys} → xs ⊆ ys → xs ⊆ y ∷ ys
  keep : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys

lemma-filter : {A : Set}(p : A → Bool) → (xs : List A) → filter p xs ⊆ xs
lemma-filter p [] = stop
lemma-filter p (x ∷ xs) with p x
... | true = keep (lemma-filter p xs)
... | false = drop (lemma-filter p xs)

open import Maybe public

mapMaybe : {A B : Set} → (A → B) → Maybe A → Maybe B
mapMaybe f nothing = nothing
mapMaybe f (just a) = just (f a)

module Sort (A : Set)(_<_ : A → A → Bool) where
  insert : A → List A → List A
  insert a [] = a ∷ []
  insert a (x ∷ xs) with x < a
  ... | true = x ∷ insert a xs
  ... | false = a ∷ x ∷ xs

  sort : List A → List A
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs)

module Sortℕ = Sort ℕ _<_

sortℕ : List ℕ → List ℕ
sortℕ = Sortℕ.sort

Matrix : Set → ℕ → ℕ → Set 
Matrix A n m = Vec (Vec A n) m

vec : {n : ℕ}{A : Set} → A → Vec A n
vec {zero} a = []
vec {succ n} a = a ∷ vec {n} a

infixl 90 _$_
_$_ : {n : ℕ}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
_$_ {zero} fs xs = []
_$_ {succ y} (f ∷ fs) (x ∷ xs) = f x ∷ fs $ xs

cutLast : {n : ℕ}{A : Set} → Vec A (succ n) → Vec A n
cutLast {zero} xs = []
cutLast {succ n} (x ∷ xs) = x ∷ cutLast xs

getLast : {n : ℕ}{A : Set} → Vec A (succ n) → A
getLast {zero} (x ∷ xs) = x
getLast {succ n} (x ∷ xs) = getLast xs


pushBack : {n : ℕ}{A : Set} → Vec A n → A → Vec A (succ n)
pushBack [] a = a ∷ []
pushBack (x ∷ xs) a = a ∷ pushBack xs a

transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
transpose {A} {zero} {m} xss = []
transpose {A} {succ n} {m} xss =
  pushBack (transpose (vec cutLast $ xss)) (vec getLast $ xss)

⊆-refl : {A : Set}{xs : List A} → xs ⊆ xs
⊆-refl {A} {[]} = stop
⊆-refl {A} {x ∷ xs} = keep ⊆-refl

[]⊆xs : {A : Set} {xs : List A} → [] ⊆ xs
[]⊆xs {A} {[]} = stop
[]⊆xs {A} {_ ∷ _}= drop []⊆xs

x∷xs⊆ys→xs⊆ys : {a : Set}{x : a}{xs ys : List a} → x ∷ xs ⊆ ys → xs ⊆ ys
x∷xs⊆ys→xs⊆ys (drop xs) = drop (x∷xs⊆ys→xs⊆ys xs)
x∷xs⊆ys→xs⊆ys (keep xs) = drop xs

⊆-trans : {A : Set}{xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans {A} {[]} _ _ = []⊆xs
⊆-trans {A} {x ∷ xs} xs⊆ys ys⊆zs = {!!}

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity ((succ (succ zero)) * k)
  odd : (k : ℕ) → Parity (succ (succ (succ zero) * k))

open import Data.Nat

{-parity : (n : ℕ) → Parity n
parity zero = even zero
parity (succ n) with parity n
parity (suc .((succ (succ zero) * k))) | even k = ?
parity (suc .(succ (succ (succ zero)) * k)) | odd k = ? -}