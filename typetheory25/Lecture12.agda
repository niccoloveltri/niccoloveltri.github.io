module Lecture12 where

open import Data.Nat
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary


-- Natural deduction system NJ

-- Formulae
data Fma : Set where
  X : ℕ → Fma
  _⇒_ : Fma → Fma → Fma

-- Contexts
Cxt : Set
Cxt = List Fma

-- Sequents are types Γ ⊢ A, whose terms are sequent derivations
infix 2 _⊢'_

data _⊢'_ : Cxt → Fma → Set where
  ax : {Γ Γ' : Cxt} {A : Fma}
    → Γ ++ A ∷ Γ' ⊢' A

  ⇒E : {Γ : Cxt} {A B : Fma}
    →   Γ ⊢' A ⇒ B   →   Γ ⊢' A
     --------------------------
    →         Γ ⊢' B

  ⇒I : {Γ : Cxt} {A B : Fma}
    →         A ∷ Γ ⊢' B 
     --------------------------
    →         Γ ⊢' A ⇒ B

-- The admissible rule of weakening
-- Requires some additional care in the case of `ax`

wk' : {Γ Γ' Δ : Cxt} {A B : Fma}
  → Δ ⊢' A
  → Δ ≡ Γ ++ Γ'
  → Γ ++ B ∷ Γ' ⊢' A
wk' ax eq = {!!}
wk' (⇒E p p') eq = {!!}
wk' (⇒I p) eq = {!!}


-- A different (but equivalent) presentation of the rules of NJ,
-- with weakening (in the leftmost position) as a primitive rule
infix 2 _⊢_

data _⊢_ : Cxt → Fma → Set where
  ax : {Γ : Cxt} {A : Fma}
    → A ∷ Γ ⊢ A

  wk : {Γ : Cxt} {A B : Fma}
    →         Γ ⊢ A
     -------------------------
    →     B ∷ Γ ⊢ A

  ⇒E : {Γ : Cxt} {A B : Fma}
    →   Γ ⊢ A ⇒ B   →   Γ ⊢ A
     --------------------------
    →         Γ ⊢ B

  ⇒I : {Γ : Cxt} {A B : Fma}
    →         A ∷ Γ ⊢ B 
     --------------------------
    →         Γ ⊢ A ⇒ B

-- The general form of weakening is admissible
wk-gen : (Γ : Cxt) {Γ' : Cxt} {A B : Fma}
  → Γ ++ Γ' ⊢ A
  → Γ ++ B ∷ Γ' ⊢ A
wk-gen [] p = wk p
wk-gen (A' ∷ Γ) ax = ax
wk-gen (A' ∷ Γ) (wk p) = wk (wk-gen Γ p)
wk-gen (A' ∷ Γ) (⇒E p p') = ⇒E (wk-gen (A' ∷ Γ) p) (wk-gen (A' ∷ Γ) p')
wk-gen (A' ∷ Γ) (⇒I {A = A} p) = ⇒I (wk-gen (A ∷ A' ∷ Γ) p)

-- The admissible rule of contraction
contr : (Γ : Cxt) {Γ' : Cxt} {A C : Fma}
  → Γ ++ A ∷ A ∷ Γ' ⊢ C
  → Γ ++ A ∷ Γ' ⊢ C
contr [] ax = ax
contr [] (wk p) = p
contr [] (⇒E p p') = ⇒E (contr [] p) (contr [] p')
contr [] (⇒I {A = A'} p) = ⇒I (contr (A' ∷ []) p)
contr (B ∷ Γ) ax = ax
contr (B ∷ Γ) (wk p) = wk (contr Γ p)
contr (B ∷ Γ) (⇒E p p') = ⇒E (contr (B ∷ Γ) p) (contr (B ∷ Γ) p')
contr (B ∷ Γ) (⇒I {A = A'} p) = ⇒I (contr (A' ∷ B ∷ Γ) p)

-- The admissible rule of exchange (finish the proof!)
exch : (Γ : Cxt) {Γ' : Cxt} {A B C : Fma}
  → Γ ++ A ∷ B ∷ Γ' ⊢ C
  → Γ ++ B ∷ A ∷ Γ' ⊢ C
exch [] ax = wk ax
exch [] (wk p) = {!!}
exch [] (⇒E p p') = {!!}
exch [] (⇒I p) = {!!}
exch (A' ∷ Γ) p = {!!}

-- The rule ⇒I is invertible (finish the proof!)
⇒I-inv : {Γ : Cxt} {A B : Fma}
    →         Γ ⊢ A ⇒ B
     --------------------------
    →         A ∷ Γ ⊢ B 
⇒I-inv ax = ⇒E (wk ax) ax
⇒I-inv (wk p) = {!⇒I-inv p!}
⇒I-inv (⇒E p p') = {!!}
⇒I-inv (⇒I p) = {!!}



----------------------------------
----------------------------------


-- Lambda calculus

-- Lambda terms, with variables as De Brujin indices
data Tm : Set where
  var : ℕ → Tm
  app : Tm → Tm → Tm
  lam : Tm → Tm

-- Some functions necessary to properly define substitution
-- (Complete the definition yourself!)
-- You can find the definitions at page 155 of the book
-- Notice that the function called `weak` below is also called `↑` in the book)

↓ : (n i : ℕ) → ¬ n ≡ i → ℕ
↓ n i ¬eq = {!!}

↑ : ℕ → ℕ → ℕ
↑ n i = {!!}

weak : ℕ → Tm → Tm
weak n t = {!!}

-- Substitution
_[_/_] : Tm → Tm → ℕ → Tm
var i [ u / n ] with n ≟ i
... | yes eq = u 
... | no ¬eq = var (↓ n i ¬eq)
app t t' [ u / n ] = app (t [ u / n ]) (t' [ u / n ])
lam t [ u / n ] = lam (t [ weak 0 u / suc n ])
