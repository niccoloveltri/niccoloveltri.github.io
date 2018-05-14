{-# OPTIONS --rewriting #-}

-- Skew monoidal categories in sequent calculus form

-- ongoing development, May 2017

module MulticatLaws where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Utilities
open import SeqCalc
open import FreeSkewMonCat

-- the cut rules satisfy the laws of a (slightly generalized) multicategory

-- unit laws

ccut-unit : {T : Stp}{Γ Δ : Cxt}(Δ₀ : Cxt){A C : Tm}
  → (g : T ∣ Δ ⊢ C)(r : Δ ≡ Δ₀ ++ A ∷ Γ)
  → ccut Δ₀ (uf ax) g r ≡ subeq r g 
ccut-unit Δ₀ ax r = ⊥-elim ([]disj∷ Δ₀ r)
ccut-unit Δ₀ (uf g) r with cases∷ Δ₀ r
ccut-unit .[] (uf g) refl | inj₁ (refl , refl , refl) = refl
ccut-unit .(_ ∷ Γ) (uf g) refl | inj₂ (Γ , refl , refl) = cong uf (ccut-unit Γ g refl)
ccut-unit Δ₀ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
ccut-unit {_}{Γ} Δ₀ (⊗r {Γ = Γ'}{Δ} g g') r with cases++ Δ₀ Γ' Γ Δ r
ccut-unit Δ₀ (⊗r g g') refl | inj₁ (Γ₀ , refl , refl) = cong₂ ⊗r (ccut-unit Δ₀ g refl) refl
ccut-unit ._ (⊗r g g') refl | inj₂ (Δ₀ , refl , refl) = cong₂ ⊗r refl (ccut-unit Δ₀ g' refl)
ccut-unit Δ₀ (Il g) refl = cong Il (ccut-unit Δ₀ g refl)
ccut-unit Δ₀ (⊗l g) refl = cong ⊗l (ccut-unit (_ ∷ Δ₀) g refl)

scut-unit : {S : Stp}{Γ : Cxt}{A : Tm}(f : S ∣ Γ ⊢ A) → scut f ax ≡ f
scut-unit ax = refl
scut-unit (uf f) = cong uf (scut-unit f)
scut-unit Ir = refl
scut-unit (⊗r f f') = refl
scut-unit (Il f) = cong Il (scut-unit f)
scut-unit (⊗l f) = cong ⊗l (scut-unit f)

-- an alternative representation of ⊗l-1

⊗l-1-alt : {Γ : Cxt}{A B C : Tm}(f : just (A ⊗ B) ∣ Γ ⊢ C)
  → ⊗l-1 f ≡ scut (⊗r ax (uf ax)) f
⊗l-1-alt ax = refl
⊗l-1-alt (⊗r f f') = cong₂ ⊗r (⊗l-1-alt f) refl
⊗l-1-alt (⊗l f) = sym (ccut-unit [] f refl)

-- the cut rules commute with Il-1 and ⊗-1

ccutIl-1 : ∀{Γ}{Δ}{A}{C} Δ₀ {Δ'}
  → (f : nothing ∣ Γ ⊢ A)(g : just I ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → Il-1 (ccut Δ₀ f g r) ≡ ccut Δ₀ f (Il-1 g) r
ccutIl-1 Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
ccutIl-1 {Γ} Δ₀ {Δ'} f (⊗r {Γ = Γ'}{Δ} g g') r with cases++ Δ₀ Γ' Δ' Δ r
ccutIl-1 Δ₀ f (⊗r g g') r | inj₁ (Γ₀ , refl , refl) = cong₂ ⊗r (ccutIl-1 Δ₀ f g refl) refl
ccutIl-1 ._ f (⊗r g g') r | inj₂ (Γ₀ , refl , refl) = refl
ccutIl-1 Δ₀ f (Il g) r = refl

scutIl-1 : {Γ Δ : Cxt} → {A C : Tm}
  → (f : just I ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ C)
  → Il-1 (scut f g) ≡ scut (Il-1 f) g
scutIl-1 ax g = refl
scutIl-1 (⊗r f f') ax = refl
scutIl-1 (⊗r f f') (⊗r g g') = cong₂ ⊗r (scutIl-1 (⊗r f f') g) refl
scutIl-1 (⊗r {Γ = Γ} f f') (⊗l g) =
  begin
  Il-1 (ccut Γ f' (scut f g) refl)
  ≡⟨ ccutIl-1 Γ f' (scut f g) refl ⟩
  ccut Γ f' (Il-1 (scut f g)) refl
  ≡⟨ cong (λ a → ccut Γ f' a refl) (scutIl-1 f g) ⟩
  ccut Γ f' (scut (Il-1 f) g) refl
  ∎
scutIl-1 (Il f) g = refl

ccut⊗l-1 : ∀{Γ Δ}{A B C D} Δ₀ {Δ'}
  → (f : nothing ∣ Γ ⊢ C)(g : just (A ⊗ B) ∣ Δ ⊢ D)
  → (r : Δ ≡ Δ₀ ++ C ∷ Δ')
  → ⊗l-1 (ccut Δ₀ f g r) ≡ ccut (B ∷ Δ₀) f (⊗l-1 g) (cong (_∷_ B) r)
ccut⊗l-1 Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
ccut⊗l-1 Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') r with cases++ Δ₀ Γ Δ' Δ r
ccut⊗l-1 {C = C} Δ₀ f (⊗r {Δ = Δ} g g') refl | inj₁ (Γ₀ , refl , refl) with cases++ Δ₀ (Δ₀ ++ C ∷ Γ₀) (Γ₀ ++ Δ) Δ refl
ccut⊗l-1 Δ₀ f (⊗r {Δ = Δ} g g') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {Δ} q
ccut⊗l-1 Δ₀ f (⊗r g g') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (.Γ₀ , refl , refl) | refl = cong₂ ⊗r (ccut⊗l-1 Δ₀ f g refl) refl
ccut⊗l-1 Δ₀ f (⊗r {Δ = Δ} g g') refl | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) = ⊥-elim (canc⊥3 Γ₀ Δ Γ₀' p)
ccut⊗l-1 {C = C} ._ {Δ'} f (⊗r {Γ = Γ} g g') refl | inj₂ (Γ₀ , refl , refl) with cases++ (Γ ++ Γ₀) Γ Δ' (Γ₀ ++ C ∷ Δ') refl
ccut⊗l-1 ._ {Δ'} f (⊗r g g') refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) = ⊥-elim (canc⊥3 [] Δ' (Γ₀' ++ Γ₀) q)
ccut⊗l-1 {C = C} ._ {Δ'} f (⊗r g g') refl | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {C ∷ Δ'} p
ccut⊗l-1 ._ f (⊗r g g') refl | inj₂ (Γ₀ , refl , refl) | inj₂ (.Γ₀ , refl , refl) | refl = refl
ccut⊗l-1 Δ₀ f (⊗l g) r = refl

scut⊗l-1 : {Γ Δ : Cxt} → {A B C D : Tm}
  → (f : just (A ⊗ B) ∣ Γ ⊢ C)(g : just C ∣ Δ ⊢ D)
  → ⊗l-1 (scut f g) ≡ scut (⊗l-1 f) g
scut⊗l-1 ax g = ⊗l-1-alt g
scut⊗l-1 (⊗r f f') ax = refl
scut⊗l-1 (⊗r f f') (⊗r g g') = cong₂ ⊗r (scut⊗l-1 (⊗r f f') g) refl
scut⊗l-1 {B = B} (⊗r {Γ = Γ} f f') (⊗l g) =
  begin
  ⊗l-1 (ccut Γ f' (scut f g) refl)
  ≡⟨ ccut⊗l-1 Γ f' (scut f g) refl ⟩
  ccut (B ∷ Γ) f' (⊗l-1 (scut f g)) (cong (_∷_ B) refl)
  ≡⟨ cong₂ (ccut (B ∷ Γ) f') (scut⊗l-1 f g) refl ⟩
  ccut (B ∷ Γ) f' (scut (⊗l-1 f) g) refl
  ∎
scut⊗l-1 (⊗l f) g = refl

-- "horizontal" associativity

mutual
  scut-hass : {T : Stp}{Γ₁ Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₁ A₂ C : Tm}
    → (f₁ : T ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : just A₁ ∣ Δ ⊢ C)
    → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
    → scut f₁ (ccut Δ₀ f₂ g r) ≡ ccut (Γ₁ ++ Δ₀) f₂ (scut f₁ g) (cong (_++_ Γ₁) r)
  scut-hass Δ₀ ax f₂ g refl = refl
  scut-hass Δ₀ (uf f₁) f₂ g refl = cong uf (scut-hass Δ₀ f₁ f₂ g refl)
  scut-hass Δ₀ Ir f₂ g refl = ccutIl-1 Δ₀ f₂ g refl
  scut-hass Δ₀ (⊗r f₁ f₃) f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
  scut-hass Δ₀ {Δ'} (⊗r {Γ = Γ''}{Δ''} f₁ f₁') f₂ (⊗r {Γ = Γ}{Δ} g g') r 
    with cases++ (Γ'' ++ Δ'' ++ Δ₀) (Γ'' ++ Δ'' ++ Γ) Δ' Δ (cong (_++_ (Γ'' ++ Δ'')) r) | cases++ Δ₀ Γ Δ' Δ r
  scut-hass Δ₀ (⊗r f₁ f₁') f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , p , refl) | inj₁ (Γ₀' , refl , q') with canc++ Γ₀ Γ₀' {Δ} q'
  scut-hass Δ₀ (⊗r f₁ f₁') f₂ (⊗r g g') r | inj₁ (._ , refl , refl) | inj₁ (Γ₀ , refl , refl) | refl = cong₂ ⊗r (scut-hass Δ₀ (⊗r f₁ f₁') f₂ g refl ) refl
  scut-hass Δ₀ {Δ'} (⊗r f₁ f₁') f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , q) | inj₁ (Γ₀' , refl , q') = ⊥-elim (canc⊥3 [] Δ' (Γ₀' ++ Γ₀) q')
  scut-hass Δ₀ (⊗r f₁ f₁') f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , p , refl) | inj₂ (Γ₀' , p' , q') = ⊥-elim (canc⊥3 Γ₀ Δ Γ₀' p')
  scut-hass _ {Δ'}{_}{A₂} (⊗r f₁ f₁') f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , q) | inj₂ (Γ₀' , p' , refl) with canc++ Γ₀ Γ₀' {A₂ ∷ Δ'} p'
  scut-hass _ (⊗r f₁ f₁') f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl = refl
  scut-hass Δ₀ (⊗r {Γ = Γ}{Δ} f₁ f₁') f₂ (⊗l {B = B} g) refl =
    begin
    ccut Γ f₁' (scut f₁ (ccut (B ∷ Δ₀) f₂ g refl)) refl
    ≡⟨ cong₂ (ccut Γ f₁') (scut-hass (B ∷ Δ₀) f₁ f₂ g refl) refl ⟩
    ccut Γ f₁' (ccut (Γ ++ B ∷ Δ₀) f₂ (scut f₁ g) refl) refl
    ≡⟨ ccut-hass Γ f₁' f₂ (scut f₁ g) refl ⟩
    ccut (Γ ++ Δ ++ Δ₀) f₂ (ccut Γ f₁' (scut f₁ g) refl) refl
    ∎
  scut-hass Δ₀ (Il f₁) f₂ g refl = cong Il (scut-hass Δ₀ f₁ f₂ g refl)
  scut-hass Δ₀ (⊗l f₁) f₂ g refl = cong ⊗l (scut-hass Δ₀ f₁ f₂ g refl)

  ccut-hass : {T : Stp} → {Γ₁ Γ₂ : Cxt} → (Δ₀ : Cxt) → {Δ Δ₁ Δ₂ : Cxt} → {A₁ A₂ C : Tm}
    → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
    → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
    → ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) refl ≡ ccut (Δ₀ ++ Γ₁ ++ Δ₁) f₂ (ccut Δ₀ f₁ g r) refl
  ccut-hass Δ₀ f₁ f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-hass Δ₀ {_}{Δ₁}{_}{A₁} f₁ f₂ (uf g) r with cases∷ (Δ₀ ++ A₁ ∷ Δ₁) r
  ccut-hass Δ₀ f₁ f₂ (uf g) r | inj₁ (p , q , s) = ⊥-elim ([]disj∷ Δ₀ (sym q))
  ccut-hass Δ₀ f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , s) with cases∷ Δ₀ r
  ccut-hass .[] f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = scut-hass Γ₀ f₁ f₂ g refl
  ccut-hass .(_ ∷ Δ₀) f₁ f₂ (uf g) r | inj₂ (._ , refl , refl) | inj₂ (Δ₀ , refl , refl) = cong uf (ccut-hass Δ₀ f₁ f₂ g refl)
  ccut-hass Δ₀ f₁ f₂ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccut-hass Δ₀ {_}{Δ₁}{Δ₂}{A₁}{A₂} f₁ f₂ (⊗r {Γ = Γ}{Δ} g g') r with cases++ (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ Δ r | cases++ Δ₀ Γ (Δ₁ ++ A₂ ∷ Δ₂) Δ r
  ccut-hass Δ₀ {Δ₁ = Δ₁} {A₂ = A₂} f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p' , q') with canc++ (Δ₁ ++ A₂ ∷ Γ₀) Γ₀' {Δ} q'
  ccut-hass {_}{Γ₁}{Γ₂} Δ₀ {_}{Δ₁}{_}{A₁}{A₂} f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl
    with cases++ Δ₀ (Δ₀ ++ A₁ ∷ Δ₁ ++ Γ₂ ++ Γ₀) _ Δ refl | cases++ (Δ₀ ++ Γ₁ ++ Δ₁) (Δ₀ ++ Γ₁ ++ Δ₁ ++ A₂ ∷ Γ₀) _ Δ refl
  ccut-hass Δ₀ f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | inj₁ (Λ₀ , p , q) | inj₁ (Λ₀' , p' , q') with canc++ Γ₀ Λ₀' {Δ} q'
  ccut-hass {_}{_}{Γ₂} Δ₀ {_}{Δ₁} f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | inj₁ (Λ₀ , p , q) | inj₁ (.Γ₀ , refl , refl) | refl with canc++ (Δ₁ ++ Γ₂ ++ Γ₀) Λ₀ {Δ} q
  ccut-hass Δ₀ f₁ f₂ (⊗r g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | inj₁ (._ , refl , refl) | inj₁ (.Γ₀ , refl , refl) | refl | refl = cong₂ ⊗r (ccut-hass Δ₀ f₁ f₂ g refl) refl
  ccut-hass Δ₀ f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | inj₁ (Λ₀ , p , q) | inj₂ (Λ₀' , p' , q') = ⊥-elim (canc⊥3 Γ₀ Δ Λ₀' p')
  ccut-hass {_}{_}{Γ₂} Δ₀ {_}{Δ₁} f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | inj₂ (Λ₀ , p , q) | _ = ⊥-elim (canc⊥3 (Δ₁ ++ Γ₂ ++ Γ₀) Δ Λ₀ p)
  ccut-hass Δ₀ {_}{Δ₁}{Δ₂}{_}{A₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , q) | inj₁ (Γ₀' , refl , q') with canc++ Δ₁ (Γ₀' ++ Γ₀) {A₂ ∷ Δ₂} q'
  ccut-hass {_}{_}{Γ₂} Δ₀ {_}{_}{Δ₂}{A₁} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl with cases++ Δ₀ (Δ₀ ++ A₁ ∷ Γ₀') _ (Γ₀ ++ Γ₂ ++ Δ₂) refl
  ccut-hass {_}{_}{Γ₂} Δ₀ {_}{_}{Δ₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₁ (Λ₀ , p , q) with canc++ Γ₀' Λ₀ {Γ₀ ++ Γ₂ ++ Δ₂} q
  ccut-hass {_}{Γ₁} Δ₀ {_}{_}{Δ₂}{_}{A₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₁ (.Γ₀' , refl , refl) | refl
    with cases++ (Δ₀ ++ Γ₁ ++ Γ₀' ++ Γ₀) (Δ₀ ++ Γ₁ ++ Γ₀') Δ₂ (Γ₀ ++ A₂ ∷ Δ₂) refl
  ccut-hass Δ₀ {_}{_}{Δ₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₁ (.Γ₀' , refl , refl) | refl | inj₁ (Λ , p , q) = ⊥-elim (canc⊥3 [] Δ₂ (Λ ++ Γ₀) q)
  ccut-hass Δ₀ {_}{_}{Δ₂}{_}{A₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₁ (.Γ₀' , refl , refl) | refl | inj₂ (Λ , p , q) with canc++ Γ₀ Λ {A₂ ∷ Δ₂} p
  ccut-hass Δ₀ f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₁ (.Γ₀' , refl , refl) | refl | inj₂ (.Γ₀ , refl , refl) | refl = refl
  ccut-hass Δ₀ f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl) | refl | inj₂ (Λ₀ , p , q) = ⊥-elim (canc⊥2 Δ₀ {Γ₀' ++ Λ₀} q)
  ccut-hass Δ₀ {_}{Δ₁}{_}{A₁} f₁ f₂ (⊗r {Δ = Δ} g g') r | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p' , q') = ⊥-elim (canc⊥3 Γ₀ Δ (Γ₀' ++ A₁ ∷ Δ₁) p')
  ccut-hass ._ {_}{Δ₁}{Δ₂}{A₁}{A₂} f₁ f₂ (⊗r g g') r | inj₂ (Γ₀ , refl , q) | inj₂ (Γ₀' , p' , refl) with canc++ Γ₀ (Γ₀' ++ A₁ ∷ Δ₁) {A₂ ∷ Δ₂} p'
  ccut-hass {_}{_}{Γ₂} ._ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ} g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀' , refl , refl) | refl with cases++ (Γ ++ Γ₀') Γ (Δ₁ ++ Γ₂ ++ Δ₂) (Γ₀' ++ A₁ ∷ Δ₁ ++ Γ₂ ++ Δ₂) refl
  ccut-hass _ f₁ f₂ (⊗r {Γ = Γ} g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₁ (Γ₀' , p' , q') = ⊥-elim (canc⊥4 Γ {Γ₀'} {Γ₀} p')
  ccut-hass _ f₁ f₂ (⊗r {Γ = Γ} g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₂ (Γ₀' , p' , q') with ++canc {xs = Γ₀}{Γ₀'} Γ q'
  ccut-hass {_}{Γ₁} _ {_}{Δ₁}{Δ₂}{_}{A₂} f₁ f₂ (⊗r {Γ = Γ} g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₂ (.Γ₀ , refl , refl) | refl
    with cases++ (Γ ++ Γ₀ ++ Γ₁ ++ Δ₁) Γ Δ₂ (Γ₀ ++ Γ₁ ++ Δ₁ ++ A₂ ∷ Δ₂) refl
  ccut-hass {_}{Γ₁} _ {_}{Δ₁}{Δ₂} f₁ f₂ (⊗r g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₂ (.Γ₀ , refl , refl) | refl | inj₁ (Γ₀' , p' , q') = ⊥-elim (canc⊥3 [] Δ₂ (Γ₀' ++ Γ₀ ++ Γ₁ ++ Δ₁) q')
  ccut-hass {_}{Γ₁} ._ {_}{Δ₁}{Δ₂}{_}{A₂} f₁ f₂ (⊗r g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₂ (.Γ₀ , refl , refl) | refl | inj₂ (Γ₀' , p' , q') with canc++ (Γ₀ ++ Γ₁ ++ Δ₁) Γ₀' {A₂ ∷ Δ₂} p'
  ccut-hass _ f₁ f₂ (⊗r g g') r | inj₂ (._ , refl , refl) | inj₂ (Γ₀ , refl , refl) | refl | inj₂ (.Γ₀ , refl , refl) | refl | inj₂ (._ , refl , refl) | refl = cong (⊗r g) (ccut-hass Γ₀ f₁ f₂ g' refl)
  ccut-hass Δ₀ f₁ f₂ (Il g) refl = cong Il (ccut-hass Δ₀ f₁ f₂ g refl)
  ccut-hass Δ₀ f₁ f₂ (⊗l {B = B} g) refl = cong ⊗l (ccut-hass (B ∷ Δ₀) f₁ f₂ g refl)

-- "vertical" associativity

mutual
  scutscut-vass : {S : Stp} → {Γ Δ Δ' : Cxt} → {A B C : Tm}
    → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
    → scut f (scut g h) ≡ scut (scut f g) h
  scutscut-vass ax g h = refl
  scutscut-vass (uf f) g h = cong uf (scutscut-vass f g h)
  scutscut-vass Ir g h = scutIl-1 g h
  scutscut-vass (⊗r f f') ax h = refl
  scutscut-vass (⊗r f f') (⊗r g g') ax = refl
  scutscut-vass (⊗r f f') (⊗r g g') (⊗r h h') = cong₂ ⊗r (scutscut-vass (⊗r f f') (⊗r g g') h) refl
  scutscut-vass (⊗r {Γ = Γ'}{Δ'} f f') (⊗r {Γ = Γ} g g') (⊗l h) =
    begin
    scut (⊗r f f') (ccut Γ g' (scut g h) refl)
    ≡⟨ scut-hass Γ (⊗r f f') g' (scut g h) refl ⟩
    ccut (Γ' ++ Δ' ++ Γ) g' (scut (⊗r f f') (scut g h)) refl
    ≡⟨ cong₂ (ccut (Γ' ++ Δ' ++ Γ) g') (scutscut-vass (⊗r f f') g h) refl ⟩
    ccut (Γ' ++ Δ' ++ Γ) g' (scut (scut (⊗r f f') g) h) refl
    ∎
  scutscut-vass (⊗r {Γ = Γ} f f') (⊗l g) h =
    begin
    ccut Γ f' (scut f (scut g h)) refl
    ≡⟨ cong₂ (ccut Γ f') (scutscut-vass f g h) refl ⟩
    ccut Γ f' (scut (scut f g) h) refl
    ≡⟨ ccutscut-vass Γ f' (scut f g) h refl ⟩
    scut (ccut Γ f' (scut f g) refl) h
    ∎
  scutscut-vass (Il f) g h = cong Il (scutscut-vass f g h)
  scutscut-vass (⊗l f) g h = cong ⊗l (scutscut-vass f g h)
  
  ccutscut-vass : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' Δ'' : Cxt} → {A B C : Tm}
    → (f : nothing ∣ Γ ⊢ A)(g : T ∣ Δ ⊢ B)(h : just B ∣ Δ'' ⊢ C)
    → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
    → ccut Δ₀ f (scut g h) (cong (λ a → a ++ Δ'') r) ≡ scut (ccut Δ₀ f g r) h
  ccutscut-vass Δ₀ f ax h r = ⊥-elim ([]disj∷ Δ₀ r)
  ccutscut-vass Δ₀ {_}{Δ''} f (uf g) h r with cases∷ Δ₀ r | cases∷ Δ₀ (cong (λ a → a ++ Δ'') r)
  ccutscut-vass .[] f (uf g) h r | inj₁ (refl , refl , refl) | inj₁ (refl , refl , refl) = scutscut-vass f g h
  ccutscut-vass .[] f (uf g) h r | inj₁ (p , refl , s) | inj₂ (Γ₀' , q' , ())
  ccutscut-vass .(_ ∷ Γ₀) f (uf g) h r | inj₂ (Γ₀ , q , refl) | inj₁ (p' , () , s')
  ccutscut-vass .(_ ∷ Γ₀) f (uf g) h r | inj₂ (Γ₀ , refl , refl) | inj₂ (.Γ₀ , refl , refl) = cong uf (ccutscut-vass Γ₀ f g h refl)
  ccutscut-vass Δ₀ f Ir h r = ⊥-elim ([]disj∷ Δ₀ r)
  ccutscut-vass Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') h r with cases++ Δ₀ Γ Δ' Δ r
  ccutscut-vass Δ₀ {_}{_}{A} f (⊗r {Δ = Δ} g g') ax refl | inj₁ (Γ₀ , refl , refl) with cases++ Δ₀ (Δ₀ ++ A ∷ Γ₀) (Γ₀ ++ Δ) Δ refl
  ccutscut-vass Δ₀ f (⊗r {Δ = Δ} g g') ax refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {Δ} q
  ccutscut-vass Δ₀ f (⊗r g g') ax refl | inj₁ (Γ₀ , refl , refl) | inj₁ (.Γ₀ , refl , refl) | refl = refl
  ccutscut-vass Δ₀ f (⊗r {Δ = Δ} g g') ax refl | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) = ⊥-elim (canc⊥3 Γ₀ Δ Γ₀' p)
  ccutscut-vass Δ₀ {_}{_}{A} f (⊗r {Δ = Δ} g g') (⊗r {Γ = Γ'}{Δ'} h h') refl | inj₁ (Γ₀ , refl , refl) with cases++ Δ₀ (Δ₀ ++ A ∷ Γ₀ ++ Δ ++ Γ') (Γ₀ ++ Δ ++ Γ' ++ Δ') Δ' refl
  ccutscut-vass Δ₀ {A = A} f (⊗r {Δ = Δ} g g') (⊗r {Γ = Γ'} {Δ'} h h') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) with canc++ (Γ₀ ++ Δ ++ Γ') Γ₀' {Δ'} q
  ccutscut-vass Δ₀ f (⊗r g g') (⊗r h h') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl with ccutscut-vass Δ₀ f (⊗r g g') h refl
  ccutscut-vass Δ₀ {A = A} f (⊗r {Δ = Δ} g g') (⊗r h h') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | ih with cases++ Δ₀ (Δ₀ ++ A ∷ Γ₀) (Γ₀ ++ Δ) Δ refl
  ccutscut-vass Δ₀ f (⊗r {Δ = Δ} g g') (⊗r h h') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | ih | inj₁ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {Δ} q
  ccutscut-vass Δ₀ f (⊗r g g') (⊗r h h') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | ih | inj₁ (._ , refl , refl) | refl = cong₂ ⊗r ih refl
  ccutscut-vass Δ₀ f (⊗r {Δ = Δ} g g') (⊗r h h') refl | inj₁ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | ih | inj₂ (Γ₀' , p , q) = ⊥-elim (canc⊥3 Γ₀ Δ Γ₀' p)
  ccutscut-vass Δ₀ f (⊗r {Δ = Δ} g g') (⊗r {Γ = Γ'} {Δ'} h h') refl | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) = ⊥-elim (canc⊥3 (Γ₀ ++ Δ ++ Γ') Δ' Γ₀' p)
  ccutscut-vass {_}{Γ} Δ₀ {_}{_}{A} f (⊗r {Δ = Δ} g g') (⊗l h) refl | inj₁ (Γ₀ , refl , refl) =
    begin
    ccut Δ₀ f (ccut (Δ₀ ++ A ∷ Γ₀) g' (scut g h) refl) refl
    ≡⟨ ccut-hass Δ₀ f g' (scut g h) refl ⟩
    ccut (Δ₀ ++ Γ ++ Γ₀) g' (ccut Δ₀ f (scut g h) refl) refl
    ≡⟨ cong₂ (ccut (Δ₀ ++ Γ ++ Γ₀) g') (ccutscut-vass Δ₀ f g h refl) refl ⟩
    ccut (Δ₀ ++ Γ ++ Γ₀) g' (scut (ccut Δ₀ f g refl) h) refl
    ∎
  ccutscut-vass ._ {Δ'}{_}{A} f (⊗r {Γ = Γ} g g') ax refl | inj₂ (Γ₀ , refl , refl) with cases++ (Γ ++ Γ₀) Γ Δ' (Γ₀ ++ A ∷ Δ') refl
  ccutscut-vass ._ {Δ'} f (⊗r {Γ = Γ} g g') ax refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) = ⊥-elim (canc⊥3 [] Δ' (Γ₀' ++ Γ₀) q)
  ccutscut-vass ._ {Δ'}{_}{A} f (⊗r {Γ = Γ} g g') ax refl | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {A ∷ Δ'} p
  ccutscut-vass ._ {Δ'} f (⊗r {Γ = Γ} g g') ax refl | inj₂ (Γ₀ , refl , refl) | inj₂ (.Γ₀ , refl , refl) | refl = refl
  ccutscut-vass ._ {Δ'}{_}{A} f (⊗r {Γ = Γ} g g') (⊗r {Γ = Γ''}{Δ''} h h') refl | inj₂ (Γ₀ , refl , refl) with cases++ (Γ ++ Γ₀) (Γ ++ Γ₀ ++ A ∷ Δ' ++ Γ'') (Δ' ++ Γ'' ++ Δ'') Δ'' refl
  ccutscut-vass ._ {Δ'}{_}{A} f (⊗r {Γ = Γ} g g') (⊗r {Γ = Γ''}{Δ''} h h') refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) with canc++ (Δ' ++ Γ'') Γ₀' {Δ''} q
  ccutscut-vass ._ {Δ'}{_}{A} f (⊗r {Γ = Γ} g g') (⊗r {Γ = Γ''}{Δ''} h h') refl | inj₂ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl with ccutscut-vass (Γ ++ Γ₀) f (⊗r g g') h refl
  ccutscut-vass ._ {Δ'}{_}{A} f (⊗r {Γ = Γ} g g') (⊗r {Γ = Γ''}{Δ''} h h') refl | inj₂ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | ih with cases++ (Γ ++ Γ₀) Γ Δ' (Γ₀ ++ A ∷ Δ') refl
  ccutscut-vass ._ {Δ'}{_}{A} f (⊗r {Γ = Γ} g g') (⊗r {Γ = Γ''}{Δ''} h h') refl | inj₂ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | ih | inj₁ (Γ₀' , p , q) = ⊥-elim (canc⊥3 [] Δ' (Γ₀' ++ Γ₀) q)
  ccutscut-vass ._ {Δ'}{_}{A} f (⊗r {Γ = Γ} g g') (⊗r {Γ = Γ''}{Δ''} h h') refl | inj₂ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | ih | inj₂ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {A ∷ Δ'} p
  ccutscut-vass ._ {Δ'}{_}{A} f (⊗r {Γ = Γ} g g') (⊗r {Γ = Γ''}{Δ''} h h') refl | inj₂ (Γ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl | ih | inj₂ (._ , refl , refl) | refl = cong₂ ⊗r ih refl 
  ccutscut-vass ._ {Δ'}{_}{A} f (⊗r {Γ = Γ} g g') (⊗r {Γ = Γ''}{Δ''} h h') refl | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) = ⊥-elim (canc⊥3 (Δ' ++ Γ'') Δ'' Γ₀' p)
  ccutscut-vass ._ {Δ'} f (⊗r {Γ = Γ} g g') (⊗l h) refl | inj₂ (Γ₀ , refl , refl) = ccutccut-vass Γ₀ Γ f g' (scut g h) refl
  ccutscut-vass Δ₀ f (Il g) h refl = cong Il (ccutscut-vass Δ₀ f g h refl)
  ccutscut-vass Δ₀ f (⊗l {B = B} g) h refl = cong ⊗l (ccutscut-vass (B ∷ Δ₀) f g h refl)

  ccutccut-vass : {T : Stp} → {Γ Δ : Cxt} → (Γ₀ Δ₀ : Cxt) → {Δ' Γ' : Cxt} → {A B C : Tm}
    → (f : nothing ∣ Γ ⊢ A)(g : nothing ∣ Γ₀ ++ A ∷ Γ' ⊢ B)(h : T ∣ Δ ⊢ C)
    → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
    → ccut (Δ₀ ++ Γ₀) f (ccut Δ₀ g h r) refl ≡ ccut Δ₀ (ccut Γ₀ f g refl) h r
  ccutccut-vass Γ₀ Δ₀ f g ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccutccut-vass Γ₀ Δ₀ f g (uf h) r with cases∷ Δ₀ r
  ccutccut-vass Γ₀ .[] f g (uf h) r | inj₁ (refl , refl , refl) = ccutscut-vass Γ₀ f g h refl
  ccutccut-vass Γ₀ .(_ ∷ Δ₀) f g (uf h) r | inj₂ (Δ₀ , refl , refl) = cong uf (ccutccut-vass Γ₀ Δ₀ f g h refl)
  ccutccut-vass Γ₀ Δ₀ f g Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccutccut-vass Γ₀ Δ₀ {Δ'} f g (⊗r {Γ = Γ}{Δ} h h') r with cases++ Δ₀ Γ Δ' Δ r
  ccutccut-vass Γ₀ Δ₀ {_}{Γ'}{A} f g (⊗r {Δ = Δ} h h') r | inj₁ (Λ₀ , refl , refl) with cases++ (Δ₀ ++ Γ₀) (Δ₀ ++ Γ₀ ++ A ∷ Γ' ++ Λ₀) (Γ' ++ Λ₀ ++ Δ) Δ refl
  ccutccut-vass Γ₀ Δ₀ {_}{Γ'} f g (⊗r {Δ = Δ} h h') r | inj₁ (Λ₀ , refl , refl) | inj₁ (Λ₀' , p , q) with canc++ (Γ' ++ Λ₀) Λ₀' {Δ} q
  ccutccut-vass Γ₀ Δ₀ f g (⊗r h h') r | inj₁ (Λ₀ , refl , refl) | inj₁ (._ , refl , refl) | refl = cong₂ ⊗r (ccutccut-vass Γ₀ Δ₀ f g h refl) refl
  ccutccut-vass Γ₀ Δ₀ {_}{Γ'} f g (⊗r {Δ = Δ} h h') r | inj₁ (Λ₀ , refl , refl) | inj₂ (Λ₀' , p , q) = ⊥-elim (canc⊥3 (Γ' ++ Λ₀) Δ Λ₀' p)
  ccutccut-vass Γ₀ _ {Δ'}{Γ'}{A} f g (⊗r {Γ = Γ} h h') r | inj₂ (Λ₀ , refl , refl) with cases++ (Γ ++ Λ₀ ++ Γ₀) Γ (Γ' ++ Δ') (Λ₀ ++ Γ₀ ++ A ∷ Γ' ++ Δ') refl
  ccutccut-vass Γ₀ .(Γ ++ Λ₀) {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Λ₀ ++ _ ∷ Δ')} h h') r | inj₂ (Λ₀ , refl , refl) | inj₁ (Λ₀' , p , q) = ⊥-elim (canc⊥4 Γ {Λ₀'}{Λ₀ ++ Γ₀} p)
  ccutccut-vass Γ₀ .(Γ ++ Λ₀) {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Λ₀ ++ _ ∷ Δ')} h h') r | inj₂ (Λ₀ , refl , refl) | inj₂ (Λ₀' , p , q) with ++canc {xs = Λ₀ ++ Γ₀}{Λ₀'} Γ q
  ccutccut-vass Γ₀ .(Γ ++ Λ₀) {Δ'} {Γ'} {A} f g (⊗r {Γ = Γ} {.(Λ₀ ++ _ ∷ Δ')} h h') r | inj₂ (Λ₀ , refl , refl) | inj₂ (.(Λ₀ ++ Γ₀) , refl , refl) | refl = cong (⊗r h) (ccutccut-vass Γ₀ Λ₀ f g h' refl)
  ccutccut-vass Γ₀ Δ₀ f g (Il h) refl = cong Il (ccutccut-vass Γ₀ Δ₀ f g h refl)
  ccutccut-vass Γ₀ Δ₀ f g (⊗l {B = B} h) refl = cong ⊗l (ccutccut-vass Γ₀ (B ∷ Δ₀) f g h refl)






