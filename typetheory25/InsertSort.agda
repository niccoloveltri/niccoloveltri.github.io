module InsertSort where

open import Data.Nat
open import Data.Nat.Properties
open import Data.List 
open import Relation.Nullary
open import Data.Product

-- INSERTION SORT

-- The predicate `isSorted xs` states that the list xs is sorted
data _≤*_ (x : ℕ) : List ℕ → Set where
  ≤*[] : x ≤* []
  ≤*∷ : {y : ℕ} {xs : List ℕ}
    → x ≤ y → x ≤* xs
    → x ≤* (y ∷ xs)

data isSorted : List ℕ → Set where
  []sorted : isSorted []
  ∷sorted : {x : ℕ} {xs : List ℕ}
    → x ≤* xs → isSorted xs
    → isSorted (x ∷ xs)

-- The insertion sort algorithm
insert : (x : ℕ) → (xs : List ℕ) → List ℕ
insert x [] = x ∷ []
insert x (y ∷ xs) with x ≤? y
... | yes x≤y = x ∷ y ∷ xs
... | no  x≰y = y ∷ insert x xs

sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ xs) = insert x (sort xs)

-- Correctness of sorting

-- A couple of lemmata
≤*-trans : {x y : ℕ} {xs : List ℕ}
  → x ≤ y → y ≤* xs → x ≤* xs
≤*-trans x≤y ≤*[] = ≤*[]
≤*-trans x≤y (≤*∷ y≤z y≤*xs) = ≤*∷ (≤-trans x≤y y≤z) (≤*-trans x≤y y≤*xs)

≤*-insert : {x y : ℕ} {xs : List ℕ}
  → x ≤ y → x ≤* xs → x ≤* insert y xs
≤*-insert x≤y ≤*[] = ≤*∷ x≤y ≤*[]
≤*-insert {x} {y} x≤y (≤*∷ {z} x≤z x≤*xs) with y ≤? z
... | yes y≤z = ≤*∷ x≤y (≤*∷ x≤z x≤*xs)
... | no y≰z = ≤*∷ x≤z (≤*-insert x≤y x≤*xs)

-- If `xs` is sorted then `insert x xs` is sorted
insertIsSorted : (x : ℕ) {xs : List ℕ}
  → isSorted xs
  → isSorted (insert x xs)
insertIsSorted x []sorted = ∷sorted ≤*[] []sorted
insertIsSorted x (∷sorted {y} y≤*xs s) with x ≤? y
... | yes x≤y = ∷sorted (≤*∷ x≤y (≤*-trans x≤y y≤*xs)) (∷sorted y≤*xs s)
... | no  x≰y = ∷sorted (≤*-insert (≮⇒≥ (≰⇒≮ x≰y)) y≤*xs) (insertIsSorted x s)

-- `sort xs` is sorted
sortIsSorted : (xs : List ℕ) → isSorted (sort xs)
sortIsSorted [] = []sorted
sortIsSorted (x ∷ xs) = insertIsSorted x (sortIsSorted xs)


-- Bundling the sorted list and the correctness proof together using a Σ-type.
SortedList : Set
SortedList = Σ (List ℕ) (λ xs → isSorted xs)

sorted : List ℕ → SortedList
sorted xs = sort xs , sortIsSorted xs
