module Safety where

open import Data.Bool hiding (_<?_; _<_; if_then_else_)
open import Data.Nat hiding (_<?_) renaming (_+_ to _+ℕ_; _<_ to _<ℕ_; _≥_ to _≥ℕ_)
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- SAFETY OF A SIMPLE PROGRAMMING LANGUAGE

-- Values
data Value : Set where
  nat : ℕ → Value
  bool : Bool → Value

-- Programs
data Prog : Set where
  val : Value → Prog
  _+_ : Prog → Prog → Prog
  _<_ : Prog → Prog → Prog
  if_then_else_ : Prog → Prog → Prog → Prog

infix 50 _+_
infix 40 _<_
infix 30 if_then_else_


-- Reduction
data _⇒_ : Prog → Prog → Set where
  Add : (n₁ n₂ : ℕ) → val (nat n₁) + val (nat n₂) ⇒ val (nat (n₁ +ℕ n₂))
  AddL : {p₁ p₁' : Prog} → p₁ ⇒ p₁' → (p₂ : Prog) → p₁ + p₂ ⇒ p₁' + p₂
  AddR : (p₁ : Prog) {p₂ p₂' : Prog} → p₂ ⇒ p₂' → p₁ + p₂ ⇒ p₁ + p₂'
  Lt : (n₁ n₂ : ℕ)
    → n₁ <ℕ n₂
    → val (nat n₁) < val (nat n₂) ⇒ val (bool true)
  Ge : (n₁ n₂ : ℕ)
    → n₁ ≥ℕ n₂
    → val (nat n₁) < val (nat n₂) ⇒ val (bool false)
  IfTrue : {p₁ p₂ : Prog}
    → if val (bool true) then p₁ else p₂ ⇒ p₁

-- Finish writing the missing constructor (page 32 of the book)


-- Types
data Type : Set where
  TNat TBool : Type

-- Typing rules
data ⊢_∷_ : Prog → Type → Set where
  ⊢bool : {b : Bool} → ⊢ val (bool b) ∷ TBool
  ⊢nat : {n : ℕ} → ⊢ val (nat n) ∷ TNat
  ⊢+ : {p₁ p₂ : Prog} → ⊢ p₁ ∷ TNat → ⊢ p₂ ∷ TNat → ⊢ p₁ + p₂ ∷ TNat
  ⊢< : {p₁ p₂ : Prog} → ⊢ p₁ ∷ TNat → ⊢ p₂ ∷ TNat → ⊢ p₁ < p₂ ∷ TBool
  ⊢if : {A : Type} {p p₁ p₂ : Prog}
    → ⊢ p ∷ TBool → ⊢ p₁ ∷ A → ⊢ p₂ ∷ A
    → ⊢ if p then p₁ else p₂ ∷ A

-- Uniqueness of types
uniqType : {p : Prog} {A B : Type}
  → ⊢ p ∷ A → ⊢ p ∷ B
  → A ≡ B
uniqType ⊢bool ⊢bool = refl
uniqType ⊢nat ⊢nat = refl
uniqType (⊢+ ⊢p₁∷TNat ⊢p₂∷TNat) (⊢+ _ _) = refl
uniqType (⊢< ⊢p₁∷A ⊢p₂∷A) (⊢< ⊢p∷B ⊢p∷B₁) = refl
uniqType (⊢if ⊢p∷TBool ⊢p₁∷A ⊢p₂∷A) (⊢if ⊢p∷TBool' ⊢p₁∷B ⊢p₂∷B) = uniqType ⊢p₁∷A ⊢p₁∷B

-- Subject reduction (Finish the proof!)
subred : {p p' : Prog} {A : Type}
  → p ⇒ p'
  → ⊢ p ∷ A
  → ⊢ p' ∷ A
subred (Add n₁ n₂) (⊢+ Tn₁ Tn₂) = ⊢nat
subred (AddL p⇒p' p₂) (⊢+ Tp₁ Tp₂) = ⊢+ (subred p⇒p' Tp₁) Tp₂
subred (AddR p₁ p⇒p') pA = {!!}
subred (Lt n₁ n₂ x) (⊢< pA pA₁) = ⊢bool
subred (Ge n₁ n₂ x) pA = {!!}
subred IfTrue (⊢if Ttrue Tp₁ Tp₂) = Tp₁

-- Progress (Finish the proof!)
progress : {p : Prog} {A : Type}
  → ⊢ p ∷ A
  → Σ Value (λ v → p ≡ val v)
    ⊎
    Σ Prog (λ p' → p ⇒ p')
progress (⊢bool {b}) = inj₁ (bool b , refl)
progress (⊢nat {n}) = inj₁ (nat n , refl)
progress (⊢+ {p₂ = p₂} Tp₁ Tp₂) with progress Tp₁
... | inj₂ (p₁' , p₁⇒p₁') = inj₂ (p₁' + p₂ , AddL p₁⇒p₁' p₂)
... | inj₁ (nat n , refl) with progress Tp₂
... | inj₁ (nat m , refl) = inj₂ (val (nat (n +ℕ m)) , Add n m)
... | inj₂ (p₂' , p₂⇒p₂') = inj₂ (val (nat n) + p₂' , AddR (val (nat n)) p₂⇒p₂')
progress (⊢< Tp Tp₁) = {!!}
progress (⊢if Tp Tp₁ Tp₂) = {!!}









