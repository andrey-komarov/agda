{-# OPTIONS --universe-polymorphism #-}

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_)

module Lib.BST 
  {k ℓ : Level}
  {A : Set k}
  {_<_ : Rel A ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) 
where

open import Data.Empty
open import Data.Bool
open import Data.Sum

open IsStrictTotalOrder isStrictTotalOrder

data Tree : Set k where
  Leaf : Tree
  Node : (v : A) → (left : Tree) → (right : Tree) → Tree

data _∈_ : A → Tree → Set k where
  Here : {a : A} {left right : Tree} → a ∈ (Node a left right)
  Lower : {a v : A} {left right : Tree}
    → (a ∈ left) ⊎ (a ∈ right) → a ∈ (Node v left right)

data IsNonEmpty : Tree → Set (k ⊔ ℓ) where
  HasRoot : {v : A} {left right : Tree} → IsNonEmpty (Node v left right)

insert : (a : A) → (t : Tree) → Tree
insert a Leaf = Node a Leaf Leaf
insert a (Node v left right) with compare a v 
... | tri< _ _ _ = Node v (insert a left) right 
... | tri≈ _ _ _ = Node v left right
... | tri> _ _ _ = Node v left (insert a right)

max : (t : Tree) → (p : IsNonEmpty t) → A
max .(Node v left Leaf) (HasRoot {v} {left} {Leaf}) = v
max .(Node v left (Node v' left' right)) 
  (HasRoot {v} {left} {Node v' left' right}) 
  = max (Node v' left' right) HasRoot

deleteMax : (t : Tree) → (p : IsNonEmpty t) → Tree
deleteMax .(Node v left Leaf) (HasRoot {v}{left}{Leaf}) = left
deleteMax .(Node v left (Node v→ left→ right→)) 
  (HasRoot {v}{left}{Node v→ left→ right→}) 
  = Node v left (deleteMax (Node v→ left→ right→) HasRoot)
deleteRoot : (t : Tree) → (p : IsNonEmpty t) → Tree
deleteRoot .(Node v Leaf Leaf) (HasRoot {v}{Leaf}{Leaf}) = Leaf
deleteRoot .(Node v Leaf (Node v→ left→ right→)) 
  (HasRoot {v}{Leaf}{Node v→ left→ right→}) 
  = Node v→ left→ right→
deleteRoot .(Node v' (Node v← left← right←) Leaf) 
  (HasRoot {v'} {Node v← left← right←} {Leaf}) 
  = Node v← left← right←
deleteRoot .(Node v (Node v← left← right←) (Node v→ left→ right→)) 
  (HasRoot {v}{Node v← left← right←}{Node v→ left→ right→}) 
  with max (Node v← left← right←) HasRoot
... | m = Node m 
               (deleteMax (Node v← left← right←) HasRoot) 
               (Node v→ left→ right→)

delete : (a : A) → (t : Tree) → Tree
delete a Leaf = Leaf
delete a (Node v left right) with compare a v
... | tri< _ _ _ = Node v (delete a left) right
... | tri≈ _ _ _ = deleteRoot (Node v left right) HasRoot
... | tri> _ _ _ = Node v left (delete a right)

data Valid : Tree → Set (k ⊔ ℓ) where
  Empty : Valid Leaf
  Invariant : {a : A} {left right : Tree} 
    → (←valid : Valid left)
    → (→valid : Valid right)
    → (∀∈l<b : {it : A} → it ∈ left → it < a) 
    → (b<∀∈r : {it : A} → it ∈ right → a < it) 
    → Valid (Node a left right)

expand→ : {t : Tree} {a b : A} 
  → {val : Valid t}
  → (a<b : a < b)
  → ({c : A} → c ∈ t → a < c) 
  → ({d : A} → d ∈ (insert b t) → a < d)
expand→ {Leaf} a<b _ Here = a<b
expand→ {Leaf} _ a<∀t (Lower (inj₁ x)) = a<∀t x
expand→ {Leaf} _ a<∀t (Lower (inj₂ y)) = a<∀t y
expand→ {Node v _ _} {_} {b} _ _ _ with compare b v
expand→ {Node _ _ _} {_} {_} _ a<∀t Here | tri< _ _ _
  = a<∀t Here
expand→ {Node _ left _} {a} {b} 
  {Invariant ←valid _ _ _} a<b a<∀t (Lower (inj₁ x)) | tri< _ _ _
  = expand→ {left}{a}{b}{←valid} a<b (λ {c} z → a<∀t (Lower (inj₁ z))) x
expand→ {Node _ _ _} _ a<∀t (Lower (inj₂ y)) | tri< _ _ _
  = a<∀t (Lower (inj₂ y))
expand→ {Node _ _ _} _ a<∀t d∈t | tri≈ _ _ _ 
  = a<∀t d∈t
expand→ {Node _ _ _} _ a<∀t Here | tri> _ _ _
  = a<∀t Here
expand→ {Node _ _ _} _ a<∀t (Lower (inj₁ x)) | tri> _ _ _
  = a<∀t (Lower (inj₁ x))
expand→ {Node _ _ right} {a} {b} 
  {Invariant _ →valid _ _} a<b a<∀t (Lower (inj₂ y)) | tri> _ _ _
  = expand→ {right}{a}{b}{→valid} a<b (λ {c} z → a<∀t (Lower (inj₂ z))) y

expand← : {t : Tree} {a b : A}
  → {val : Valid t}
  → (b<a : b < a)
  → ({c : A} → c ∈ t → c < a)
  → ({d : A} → d ∈ (insert b t) → d < a)
expand← {Leaf} b<a _ Here = b<a
expand← {Leaf} _ ∀t<a (Lower (inj₁ x)) = ∀t<a x
expand← {Leaf} _ ∀t<a (Lower (inj₂ y)) = ∀t<a y
expand← {Node v _ _} {_}{b} _ _ _ with compare b v
expand← {Node _ _ _} _ ∀t<a Here | tri< _ _ _ = ∀t<a Here
expand← {Node _ left _}{a}{b} 
  {Invariant ←valid _ _ _} b<a ∀t<a (Lower (inj₁ x)) | tri< _ _ _
  = expand← {left}{a}{b}{←valid} b<a (λ {c} z → ∀t<a (Lower (inj₁ z))) x
expand← {Node _ _ _} _ ∀t<a (Lower (inj₂ y)) | tri< _ _ _ 
  = ∀t<a (Lower (inj₂ y))
expand← {Node _ _ _} _ ∀t<a d∈bt | tri≈ _ _ _ 
  = ∀t<a d∈bt
expand← {Node _ _ _} _ ∀t<a Here | tri> _ _ _ 
  = ∀t<a Here
expand← {Node _ _ _} _ ∀t<a (Lower (inj₁ x)) | tri> _ _ _ 
  = ∀t<a (Lower (inj₁ x))
expand← {Node _ _ right} {a}{b} 
  {Invariant _ →valid _ _} b<a ∀t<a (Lower (inj₂ y)) | tri> _ _ _
  = expand← {right} {a} {b} {→valid} b<a (λ {c} z → ∀t<a (Lower (inj₂ z))) y

add : {a : A} {t : Tree} → Valid t → Valid (insert a t)
add {a} Empty = Invariant {a}{Leaf}{Leaf} Empty Empty (λ ()) (λ ())
add {new}{Node .a .left .right} 
  (Invariant {a}{left}{right} ←valid →valid ∀∈l ∀∈r) with compare new a
... | tri< new<a _ _ = Invariant {a}{insert new left}{right} 
      (add ←valid) →valid (expand← {left} {a} {new} {←valid} new<a ∀∈l) ∀∈r
... | tri≈ _ _ _ = Invariant ←valid →valid ∀∈l ∀∈r
... | tri> _ _ b<new = Invariant {a}{left}{insert new right} ←valid 
      (add →valid) ∀∈l (expand→ {right} {a} {new} {→valid} b<new ∀∈r)

lem-max : {t : Tree} 
      → {p : IsNonEmpty t}
      → max t p ∈ t
lem-max {Leaf} {()}
lem-max {Node v left Leaf} {HasRoot} = Here
lem-max {Node v left (Node v→ left→ right→)} {HasRoot} 
  = Lower (inj₂ (lem-max {Node v→ left→ right→}{HasRoot}))

lem-max₂ : {a : A} → {t : Tree} 
         → {p : IsNonEmpty t}
         → (a∈dmt : a ∈ deleteMax t p)
         → a ∈ t
lem-max₂ {a} {Leaf} {()} a∈dmt
lem-max₂ {a} {Node v Leaf Leaf} {HasRoot} ()
lem-max₂ {a} {Node v (Node v← left← right←) Leaf} {HasRoot} a∈dmt 
  = Lower (inj₁ a∈dmt)
lem-max₂ {.v} {Node v left (Node v→ left→ right→)} {HasRoot} Here 
  = Here
lem-max₂ {a} {Node v left (Node v→ left→ right→)} {HasRoot} 
  (Lower (inj₁ x)) = Lower (inj₁ x)
lem-max₂ {a} {Node v left (Node v→ left→ right→)} {HasRoot} 
  (Lower (inj₂ y)) = Lower (inj₂ 
    (lem-max₂ {a}{Node v→ left→ right→}{HasRoot} y))

lem-max₃ : {t : Tree} → (ne : IsNonEmpty t) → (p : Valid t)
         → {it : A} → it ∈ (deleteMax t ne) → it < max t ne
lem-max₃ {Leaf} () p it∈dmt
lem-max₃ {Node v left Leaf} HasRoot (Invariant ←valid →valid ∀∈l<b b<∀∈r) it∈dmt = ∀∈l<b it∈dmt
lem-max₃ {Node v left (Node v→ left→ right→)} HasRoot (Invariant ←valid →valid ∀∈l<b b<∀∈r) Here 
  = b<∀∈r {max (Node v→ left→ right→) HasRoot} 
    (lem-max {Node v→ left→ right→}{HasRoot})
lem-max₃ {Node v left (Node v→ left→ right→)} HasRoot (Invariant ←valid →valid ∀∈l<b b<∀∈r) {it} (Lower (inj₁ x)) 
  = trans (∀∈l<b x) 
          (b<∀∈r 
            {max (Node v→ left→ right→) HasRoot} 
            (lem-max {Node v→ left→ right→}{HasRoot})
          )
lem-max₃ {Node v left (Node v→ left→ right→)} HasRoot (Invariant ←valid →valid ∀∈l<b b<∀∈r) {it} (Lower (inj₂ y)) = lem-max₃ HasRoot →valid y

lem-root₁ : {a : A} → {t : Tree} 
      → (p : IsNonEmpty t)
      → (a∈drt : a ∈ deleteRoot t p)
      → a ∈ t
lem-root₁ {a} {Leaf} () a∈drt
lem-root₁ {a} {Node v Leaf Leaf} HasRoot a∈drt 
  = Lower (inj₁ a∈drt)
lem-root₁ {a} {Node v Leaf (Node v→ _ _)} HasRoot a∈drt 
  = Lower (inj₂ a∈drt)
lem-root₁ {a} {Node v (Node v← _ _) Leaf} HasRoot a∈drt 
  = Lower (inj₁ a∈drt)
lem-root₁ {.(max (Node v← left← right←) HasRoot)} {Node v (Node v← left← right←) (Node v→ left→ right→)} HasRoot Here 
  = Lower {max (Node v← left← right←) HasRoot} 
          (inj₁ (lem-max {Node v← left← right←}{HasRoot}))
lem-root₁ {a} {Node v (Node v← left← right←) (Node v→ left→ right→)} 
  HasRoot (Lower (inj₁ x)) 
  = Lower (inj₁ (lem-max₂ {a}{Node v← left← right←}{HasRoot} x))
lem-root₁ {a} {Node v (Node v← left← right←) (Node v→ left→ right→)} 
  HasRoot (Lower (inj₂ y)) 
  = Lower (inj₂ y)

lem-delete₁ : {v a : A} → {t : Tree} 
     → (v ∈ (delete a t)) 
     → (v ∈ t)
lem-delete₁ {v} {a} {Leaf} a∈dat = a∈dat
lem-delete₁ {v} {a} {Node v' left right} a∈dat with compare a v'
lem-delete₁ {.v'} {a} {Node v' left right} Here | tri< a' ¬b ¬c = Here
lem-delete₁ {v} {a} {Node v' left right} (Lower (inj₁ x)) 
  | tri< a' ¬b ¬c = Lower (inj₁ (lem-delete₁ x))
lem-delete₁ {v} {a} {Node v' left right} (Lower (inj₂ y)) 
  | tri< a' ¬b ¬c = Lower (inj₂ y)
... | tri≈ _ _ _ = lem-root₁ HasRoot a∈dat
lem-delete₁ {.v'} {a} {Node v' left right} Here | tri> ¬a ¬b c = Here
lem-delete₁ {v} {a} {Node v' left right} (Lower (inj₁ x)) 
  | tri> ¬a ¬b c = Lower (inj₁ x)
lem-delete₁ {v} {a} {Node v' left right} (Lower (inj₂ y)) 
  | tri> ¬a ¬b c = Lower (inj₂ (lem-delete₁ y))

lem₁ : {a v : A} → {t : Tree} → (p : Valid t) 
     → ({it : A} → it ∈ t → it < v)
     → ({it : A} → it ∈ (delete a t) → it < v)
lem₁ Empty ∀∈t<v it∈dat = ∀∈t<v it∈dat
lem₁ {a}{v}{Node val left right} 
  (Invariant ←valid →valid ∀∈l<b b<∀∈r) ∀∈t<v it∈dat with compare a val

lem₁ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) ∀∈t<v Here | tri< a<val ¬b ¬c = ∀∈t<v Here
lem₁ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) ∀∈t<v {it} (Lower (inj₁ x)) | tri< a<val ¬b ¬c = ∀∈t<v (Lower (inj₁ (lem-delete₁ x)))
lem₁ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) ∀∈t<v (Lower (inj₂ y)) | tri< a<val ¬b ¬c = ∀∈t<v (Lower (inj₂ y))

lem₁ {a} {v} {Node val left right} 
  (Invariant ←valid →valid ∀∈l<b b<∀∈r) ∀∈t<v {it} it∈dat | tri≈ ¬a<val a≈val ¬a>val = ∀∈t<v (lem-root₁ HasRoot it∈dat)

lem₁ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) ∀∈t<v Here | tri> ¬a ¬b a>val = ∀∈t<v Here
lem₁ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) ∀∈t<v (Lower (inj₁ x)) | tri> ¬a ¬b a>val = ∀∈t<v (Lower (inj₁ x))
lem₁ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) ∀∈t<v (Lower (inj₂ y)) | tri> ¬a ¬b a>val = ∀∈t<v (Lower (inj₂ (lem-delete₁ y)))

lem₂ : {a v : A} → {t : Tree} → (p : Valid t)
  → ({it : A} → it ∈ t → v < it)
  → ({it : A} → it ∈ (delete a t) → v < it)
lem₂ {a} {v} {Leaf} p v<∀∈t it∈dat = v<∀∈t it∈dat
lem₂ {a} {v} {Node val left right} 
  (Invariant ←valid →valid ∀∈l<b b<∀∈r) v<∀∈t {it} it∈dat with compare a val
lem₂ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) v<∀∈t Here | tri< a' ¬b ¬c = v<∀∈t Here
lem₂ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) v<∀∈t {it} (Lower (inj₁ x)) | tri< a' ¬b ¬c = v<∀∈t (Lower (inj₁ (lem-delete₁ x)))
lem₂ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) v<∀∈t (Lower (inj₂ y)) | tri< a' ¬b ¬c = v<∀∈t (Lower (inj₂ y))
... | tri≈ _ _ _ = v<∀∈t (lem-root₁ HasRoot it∈dat)
lem₂ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) v<∀∈t Here | tri> ¬a ¬b c = v<∀∈t Here
lem₂ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) v<∀∈t (Lower (inj₁ x)) | tri> ¬a ¬b c = v<∀∈t (Lower (inj₁ x))
lem₂ {a} {v} {Node val left right} (Invariant ←valid →valid ∀∈l<b b<∀∈r) v<∀∈t {it} (Lower (inj₂ y)) | tri> ¬a ¬b c = v<∀∈t (Lower (inj₂ (lem-delete₁ y)))

removeMax : {t : Tree} → (ne : IsNonEmpty t) → (p : Valid t) 
  → Valid (deleteMax t ne)
removeMax {Leaf} () p
removeMax {Node v left Leaf} HasRoot (Invariant ←valid →valid ∀∈l<b b<∀∈r) = ←valid
removeMax {Node v left (Node v→ left→ right→)} HasRoot 
  (Invariant ←valid →valid ∀∈l<b b<∀∈r) 
  = Invariant ←valid (removeMax HasRoot →valid) ∀∈l<b 
              (λ {it} z → 
                b<∀∈r (lem-max₂ {it}{Node v→ left→ right→}{HasRoot} z))

removeRoot : {t : Tree} → {ne : IsNonEmpty t} → (p : Valid t) 
  → Valid (deleteRoot t ne)
removeRoot {Leaf} {()} p
removeRoot {Node v Leaf Leaf} {HasRoot} p = Empty
removeRoot {Node v Leaf (Node v' left right)} {HasRoot} (Invariant ←valid →valid ∀∈l<b b<∀∈r) = →valid
removeRoot {Node v (Node v← left← right←) Leaf} {HasRoot} (Invariant ←valid →valid ∀∈l<b b<∀∈r) = ←valid
removeRoot {Node v (Node v← left← right←) (Node v→ left→ right→)} 
  {HasRoot} (Invariant ←valid →valid ∀∈l<b b<∀∈r) 
  = Invariant 
      (removeMax HasRoot ←valid) 
      →valid 
      (lem-max₃ {Node v← left← right←} HasRoot ←valid)
      (λ {it} z → trans (∀∈l<b {max (Node v← left← right←) HasRoot} (lem-max {Node v← left← right←}{HasRoot})) (b<∀∈r z))

remove : {t : Tree} → (a : A)  → (p : Valid t) → Valid (delete a t)
remove a Empty = Empty
remove {Node v left right} a 
  (Invariant ←valid →valid ∀∈l<b b<∀∈r) with compare a v
... | tri< a<v ¬a=v ¬a>v 
    = Invariant (remove a ←valid) →valid (lem₁ ←valid ∀∈l<b) b<∀∈r
... | tri≈ ¬a<v a=v ¬a>v 
    = removeRoot {Node v left right}{HasRoot}
                 (Invariant ←valid →valid ∀∈l<b b<∀∈r)
... | tri> ¬a<v ¬a=v a>v 
    = Invariant ←valid (remove a →valid) ∀∈l<b (lem₂ →valid b<∀∈r)