module Lecture10 where

open import Lecture9

-- Booleans
data Bool : Set where
  false true : Bool

_and_ : Bool → Bool → Bool
false and y = false
true  and y = y

not : Bool → Bool
not false = true
not true = false

_le_ : ℕ → ℕ → Bool
zero  le m     = true
suc n le zero  = false
suc n le suc m = n le m

if_then_else : {A : Set} (b : Bool) (x y : A) → A
if true  then x else y = x
if false then x else y = y

----

-- Lists

data List (A : Set) : Set where
  [] : List A               -- empty
  _∷_ : A → List A → List A -- cons

-- Checking the type of a term "t":
-- -- Outside of a hold: C-c C-d then type "t"
-- -- Inside a hole: type "t" and then C-c C-.

-- Pattern-matching: C-c C-c in the hole and then type the term
-- or, type the term and then C-c C-c

length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

suc-+ : (n m : ℕ) → suc n + m ≡ suc (n + m)
suc-+ n m = {!!}

trans : {A : Set} {x y z : A}
  → x ≡ y → y ≡ z → x ≡ z
trans eq eq' = {!!}

length++ : {A : Set} (xs ys : List A)
  → length xs + length ys ≡ length (xs ++ ys)
length++ [] ys = zero-+ (length ys)
length++ (x ∷ xs) ys =
  trans (suc-+ (length xs) (length ys))
        (cong suc (length++ xs ys))

recList : {A B : Set}
  → B
  → (A → B → B)
  → List A → B
recList e c [] = e
recList e c (x ∷ xs) = c x (recList e c xs)

indList : {A : Set} (P : List A → Set)
  → P []
  → ((x : A) → (ys : List A) → P ys → P (x ∷ ys)) 
  → (xs : List A) → P xs
indList P pe pc [] = pe
indList P pe pc (x ∷ xs) = pc x xs (indList P pe pc xs)

----

-- Maybe

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

head : {A : Set} → List A → Maybe A
head []       = nothing
head (x ∷ xs) = just x

---

-- Vectors

data Vec (A : Set) : ℕ → Set where 
  [] : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

headVec : {A : Set} {n : ℕ} → Vec A (suc n) → A
headVec (x ∷ xs) = x

toList : {A : Set} {n : ℕ} → Vec A n → List A
toList [] = []
toList (x ∷ xs) = x ∷ toList xs

fromList : {A : Set} (xs : List A) → Vec A (length xs)
fromList [] = []
fromList (x ∷ xs) = x ∷ fromList xs

_+'_ : ℕ → ℕ → ℕ
zero  +' n  = n
suc m +' n = suc (m +' n)

_++Vec_ : {A : Set} {n m : ℕ}
  → Vec A n → Vec A m
  → Vec A (n +' m)
[] ++Vec ys = ys
(x ∷ xs) ++Vec ys = x ∷ (xs ++Vec ys)

---

-- Finite prefixes of ℕ
-- {0,1,..,n}

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

-- Fin n = {0,1,...,n-1}

a : Fin (suc (suc (suc (suc zero))))
a = suc (suc (suc zero))

-- Vec A n ≅ (Fin n → A)

lookup : {A : Set} {n : ℕ}
  → Vec A n
  → Fin n → A
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc i) = lookup xs i

lookupList : {A : Set} → List A → ℕ → Maybe A
lookupList [] i = nothing
lookupList (x ∷ xs) zero = just x
lookupList (x ∷ xs) (suc i) = lookupList xs i

lookupList' : {A : Set}
  → (xs : List A) (i : ℕ)
  → (suc i le length xs) ≡ true
  → A
lookupList' (x ∷ xs) zero p = x
lookupList' (x ∷ xs) (suc i) p = lookupList' xs i p
