module Lecture9 where

-- the identity function
id : {A : Set} → A → A
id x = x

-- importing the product type
open import Data.Product

-- commutativity of products
×-comm : (A B : Set) → A × B → B × A
×-comm A B (a , b) = (b , a)

-- Here is how the proof is constructed in steps in Emacs:
-- type-checking: C-c C-l
-- looking at the context: C-c C-, (in a hole)
-- pattern mathcing on x: C-c C-c and then type "x"
-- refine the goal: C-c C-r
-- returning an element b: type "b" and then C-c C-spc

-- The return type of ×-comm is a dependent type, depending on the types A, B
P : (A B : Set) → Set
P A B = A × B → B × A

-- Another proof of commutativity of products, now with A and B implicit
×-comm-impl : {A B : Set} → A × B → B × A
×-comm-impl (a , b) = (b , a)

---
---

-- The inductive type of natural numbers
data ℕ : Set where
  zero : ℕ 
  suc : ℕ → ℕ

-- The natural numbers 3 and 4
t : ℕ
t = suc (suc (suc (zero)))

s : ℕ
s = suc t

-- The predecessor function
-- Defined by pattern matching on the (only) argument of type ℕ
pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

-- Addition, by pattern matching on the 2nd argument
_+_ : ℕ → ℕ → ℕ
n + zero = n
n + suc m = suc (n + m)

-- Declaring fixity of +
infix 21 _+_

-- How to normalize terms:
-- C-c C-n and then type the term you want to normalize
-- E.g. C-c C-n and then type "t + s", you will get back 7

-- The recursion principle of natural numbers
recℕ : {A : Set}
  → A
  → (A → A)
  → ℕ → A
recℕ z s zero = z
recℕ z s (suc n) = s (recℕ z s n)

-- Addition defined using the recusion principle recℕ
_+'_ : ℕ → ℕ → ℕ
n +' m = recℕ n suc m

---
---

-- Equality type
data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x   

-- Equality type again, but without infix notation
data Eq {A : Set} : A → A → Set where
  refl : (x : A) → Eq x x

-- Congruence for the equality type.
-- Proved by pattern matching on the term of type x ≡ y
cong : {A B : Set} → (f : A → B)
  → {x y : A} → x ≡ y
  → f x ≡ f y
cong f (refl x) = refl (f x)

-- Automation in Agda:
-- C-c C-a for trying to find a term that matches the goal

-- Proof that n + 0 ≡ n
-- Notice that this is just reflexivity, since n + zero computes to n.
-- I.e. if you normalize n + zero you get n.
+-zero : (n : ℕ) → n + zero ≡ n
+-zero n = refl n

-- Proof that 0 + n ≡ n
-- By pattern matching on n.
zero-+ : (n : ℕ) → zero + n ≡ n
zero-+ zero = refl _
zero-+ (suc n) = cong suc (zero-+ n)

-- C-c C-. for checking the type of the term you wrote in the hole

-- The induction principle for natural numbers.
-- Defining a (dependent) function out of ℕ by pattern matching "is" the indiction principle for ℕ
indℕ : (P : ℕ → Set)
  → P zero
  → ((m : ℕ) → P m → P (suc m))
  → (n : ℕ) → P n
indℕ P p0 ps zero = p0
indℕ P p0 ps (suc n) = ps n (indℕ P p0 ps n)

