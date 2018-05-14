module Focusing where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Utilities

open import FreeSkewMonCat
open import SeqCalc


-- =======================================================================

-- focused sequent calculus

StpR : Set
StpR = Maybe Var

infix 15 _∣_⊢L_
infix 15 _∣_⊢R_

mutual 
  data _∣_⊢L_ : Stp → Cxt → Tm → Set where
    uf : {Γ : Cxt} → {A C : Tm} → 
              just A ∣ Γ ⊢L C → nothing ∣ A ∷ Γ ⊢L C
    Il : {Γ : Cxt} → {C : Tm} → 
              nothing ∣ Γ ⊢L C → just I ∣ Γ ⊢L C 
    ⊗l : {Γ : Cxt} → {A B C : Tm} → 
              just A ∣ B ∷ Γ ⊢L C → just (A ⊗ B) ∣ Γ ⊢L C
    msw :  {S : StpR} → {T : Stp} → mmap ` S ≡ T → 
              {Γ : Cxt} → {C : Tm} → 
              S ∣ Γ ⊢R C → T ∣ Γ ⊢L C

  data _∣_⊢R_ : StpR → Cxt → Tm → Set where
    ax : {X : Var} → just X ∣ [] ⊢R ` X
    Ir : nothing ∣ [] ⊢R I
    ⊗r : {S : StpR} → {Γ Δ : Cxt} → {A B : Tm} → 
              S ∣ Γ ⊢R A → nothing ∣ Δ ⊢L B → S ∣ Γ ++ Δ ⊢R A ⊗ B 


-- ====================================================================

-- the embedding of focused derivations into general derivations

mutual 
  embL : {S : Stp} → {Γ : Cxt} → {C : Tm} →
              S ∣ Γ ⊢L C → S ∣ Γ ⊢ C
  embL (uf f) = uf (embL f)
  embL (Il f) = Il (embL f)
  embL (⊗l f) = ⊗l (embL f)
  embL (msw refl f) = embR f
  
  embR : {S : StpR} → {Γ : Cxt} → {C : Tm} →
              S ∣ Γ ⊢R C → mmap ` S ∣ Γ ⊢ C
  embR ax = ax
  embR Ir = Ir
  embR (⊗r f₁ f₂) = ⊗r (embR f₁) (embL f₂)


-- ====================================================================

-- the focusing function 

-- admissibility of unerestricted ⊗r (called ⊗rL)

⊗rL : {S : Stp} → {Γ Δ : Cxt} → {A B : Tm} → 
              S ∣ Γ ⊢L A → nothing ∣ Δ ⊢L B → S ∣ Γ ++ Δ ⊢L A ⊗ B
⊗rL (uf f₁) f₂ = uf (⊗rL f₁ f₂)
⊗rL (Il f₁) f₂ = Il (⊗rL f₁ f₂) 
⊗rL (⊗l f₁) f₂ = ⊗l (⊗rL f₁ f₂)
⊗rL (msw refl f₁) f₂ = msw refl (⊗r f₁ f₂)

-- admissibility of unrestricted ax (called axL)

axL :  {A : Tm} → just A ∣ [] ⊢L  A
axL {` X} = msw refl ax
axL {I} =  Il (msw refl Ir) 
axL {A₁ ⊗ A₂} = ⊗l (⊗rL (axL {A₁}) (uf (axL {A₂})) )

-- the focusing function itself

focus : {S : Stp} → {Γ : Cxt} → {C : Tm} →
              S ∣ Γ ⊢ C → S ∣ Γ ⊢L C
focus ax = axL
focus (uf f) = uf (focus f)
focus Ir = msw refl Ir
focus (⊗r f₁ f₂) = ⊗rL (focus f₁) (focus f₂)
focus (Il f) = Il (focus f)
focus (⊗l f) = ⊗l (focus f)


-- ====================================================================

-- focus-emb
-- = Thm 5.2 in the paper

mutual 
  focus-embL : {S : Stp} → {Γ : Cxt} → {C : Tm} →
              (f : S ∣ Γ ⊢L C) → focus (embL f) ≡ f
  focus-embL (uf f) = cong uf (focus-embL f)
  focus-embL (Il f) = cong Il (focus-embL f)
  focus-embL (⊗l f) = cong ⊗l (focus-embL f)
  focus-embL (msw refl f) = focus-embR f              

  focus-embR : {S : StpR} → {Γ : Cxt} → {C : Tm} →
              (f : S ∣ Γ ⊢R C) → focus (embR f) ≡ msw refl f
  focus-embR ax = refl
  focus-embR Ir = refl
  focus-embR (⊗r f₁ f₂) = cong₂ ⊗rL (focus-embR f₁) (focus-embL f₂)  


-- ====================================================================

-- focus is compatible
-- = Thm 5.3 in the paper

focus-compat : {S : Stp} → {Γ : Cxt} → {C : Tm} →
              {f g : S ∣ Γ ⊢ C} → f ≈ g → focus f ≡ focus g
focus-compat refl≈ = refl
focus-compat (sym≈ p) = sym (focus-compat p)
focus-compat (trans≈ p q) = trans (focus-compat p) (focus-compat q)
focus-compat (conguf p) = cong uf (focus-compat p)
focus-compat (cong⊗l p) = cong ⊗l (focus-compat p)
focus-compat (congIl p) = cong Il (focus-compat p)
focus-compat (cong⊗r p₁ p₂) =
                   cong₂ ⊗rL (focus-compat p₁) (focus-compat p₂)
focus-compat axI = refl
focus-compat ax⊗ = refl
focus-compat ⊗ruf = refl
focus-compat ⊗rIl = refl
focus-compat ⊗r⊗l = refl     


-- ====================================================================

-- emb-focus
-- = Thm 5.4 in the paper


embL-⊗rL : {S : Stp} → {Γ Δ : Cxt} → {A B : Tm} → 
              (f₁ : S ∣ Γ ⊢L A)  → (f₂ : nothing ∣ Δ ⊢L B) → 
              embL (⊗rL f₁ f₂) ≈ ⊗r (embL f₁) (embL f₂)
embL-⊗rL (uf f₁) f₂ = 
     trans≈ (conguf (embL-⊗rL f₁ f₂))
            (sym≈ (⊗ruf {f = embL f₁} {g = embL f₂ })) 
embL-⊗rL (Il f₁) f₂ =
     trans≈ (congIl (embL-⊗rL f₁ f₂))
            (sym≈ (⊗rIl {f = embL f₁} {g = embL f₂}))
embL-⊗rL (⊗l f₁) f₂ =
     trans≈ (cong⊗l (embL-⊗rL f₁ f₂))
            (sym≈ (⊗r⊗l {f = embL f₁} {g = embL f₂}))
embL-⊗rL (msw refl f₁) f₂ = refl≈

embL-axL : {A : Tm} → embL (axL {A}) ≈ ax
embL-axL {` X} = refl≈
embL-axL {I} = sym≈ axI
embL-axL {A₁ ⊗ A₂} =
      trans≈ (cong⊗l (trans≈ (embL-⊗rL axL (uf axL))
                             (cong⊗r embL-axL (conguf embL-axL))))
             (sym≈ ax⊗)

embL-focus : {S : Stp} → {Γ : Cxt} → {C : Tm} →
             (f : S ∣ Γ ⊢ C)  → embL (focus f) ≈ f
embL-focus ax = embL-axL
embL-focus (uf f) = conguf (embL-focus f)
embL-focus Ir = refl≈
embL-focus (⊗r f₁ f₂)
      = trans≈ (embL-⊗rL (focus f₁) (focus f₂))
               (cong⊗r (embL-focus f₁) (embL-focus f₂)) 
embL-focus (Il f) = congIl (embL-focus f)
embL-focus (⊗l f) = cong⊗l (embL-focus f)             

