{-# OPTIONS --rewriting #-}

-- Skew monoidal categories in sequent calculus form

-- ongoing development, May 2017

module SeqCalc where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Utilities
open import FreeSkewMonCat

-- =======================================================================

-- Sequent calculus

-- -- (In addition to the conclusion, sequents have a stoup and a context.)

Stp : Set
Stp = Maybe Tm

Cxt : Set
Cxt = List Tm


infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Tm → Set where
  ax : {A : Tm} → just A ∣ [] ⊢ A
  uf : {Γ : Cxt} → {A C : Tm} → 
              just A ∣ Γ ⊢ C → nothing ∣ A ∷ Γ ⊢ C 
  Ir : nothing ∣ [] ⊢ I
  ⊗r : {S : Stp} → {Γ Δ : Cxt} → {A B : Tm} → 
              S ∣ Γ ⊢ A → nothing ∣ Δ ⊢ B → S ∣ Γ ++ Δ ⊢ A ⊗ B 
  Il : {Γ : Cxt} → {C : Tm} → 
              nothing ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊗l : {Γ : Cxt} → {A B C : Tm} → 
              just A ∣ B ∷ Γ ⊢ C → just (A ⊗ B) ∣ Γ ⊢ C
              
data _≈_ : {S  : Stp}{Γ : Cxt}{A : Tm} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl≈ : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢ A} → f ≈ f
  sym≈ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢ A} → f ≈ g → g ≈ f
  trans≈ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢ A} → f ≈ g → g ≈ h → f ≈ h
  conguf : ∀{Γ}{A}{C}{f g : just A ∣ Γ ⊢ C} → f ≈ g → uf f ≈ uf g
  cong⊗l : ∀{Γ}{A}{B}{C}{f g : just A ∣ B ∷ Γ ⊢ C} → f ≈ g → ⊗l f ≈ ⊗l g
  congIl : ∀{Γ}{C}{f g : nothing ∣ Γ ⊢ C} → f ≈ g → Il f ≈ Il g
  cong⊗r : ∀{S}{Γ}{Δ}{A}{B}{f g : S ∣ Γ ⊢ A}{f' g' : nothing ∣ Δ ⊢ B}
    → f ≈ g → f' ≈ g' → ⊗r f f' ≈ ⊗r g g'
  axI : ax ≈ Il Ir
  ax⊗ : {A B : Tm} → ax {A ⊗ B} ≈ ⊗l (⊗r ax (uf ax))
  ⊗ruf : {Γ Δ : Cxt}{A A' B : Tm}
    → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (uf f) g ≈ uf (⊗r f g)
  ⊗rIl : {Γ Δ : Cxt}{A B : Tm}
    → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (Il f) g ≈ Il (⊗r f g)
  ⊗r⊗l : {Γ Δ : Cxt}{A A' B B' : Tm}
    → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (⊗l f) g ≈ ⊗l (⊗r f g)

≡-to-≈ : ∀{S}{Γ}{A}{f f' : S ∣ Γ ⊢ A} → f ≡ f' → f ≈ f'
≡-to-≈ refl = refl≈

-- equational reasoning sugar for ≈

infix 4 _≈'_
infix 1 proof≈_
infixr 2 _≈〈_〉_
infix 3 _qed≈

data _≈'_ {S  : Stp}{Γ : Cxt}{A : Tm} (f g : S ∣ Γ ⊢ A) : Set where
  relto :  f ≈ g → f ≈' g

proof≈_ : {S  : Stp}{Γ : Cxt}{A : Tm} {f g : S ∣ Γ ⊢ A} → f ≈' g → f ≈ g
proof≈ relto p = p

_≈〈_〉_ :  {S  : Stp}{Γ : Cxt}{A : Tm} (f : S ∣ Γ ⊢ A) {g h : S ∣ Γ ⊢ A} → f ≈ g → g ≈' h → f ≈' h 

_ ≈〈 p 〉 relto q = relto (trans≈ p q)

_qed≈  :  {S  : Stp}{Γ : Cxt}{A : Tm} (f : S ∣ Γ ⊢ A) → f ≈' f
_qed≈ _ = relto refl≈

-- inverted left rules

Il-1 : {Γ : Cxt} → {C : Tm} → 
              just I ∣ Γ ⊢ C → nothing ∣ Γ ⊢ C
Il-1 ax = Ir
Il-1 (⊗r p p₁) = ⊗r (Il-1 p) p₁
Il-1 (Il p) = p

Il-iso : {Γ : Cxt} → {C : Tm} → 
              (f : just I ∣ Γ ⊢ C) → Il (Il-1 f) ≈ f
Il-iso ax = sym≈ axI
Il-iso (⊗r f f₁) = trans≈ (sym≈ ⊗rIl) (cong⊗r (Il-iso f) refl≈)
Il-iso (Il f) = refl≈            

congIl-1 : {Γ : Cxt} → {C : Tm} → 
              {f g : just I ∣ Γ ⊢ C} →
              f ≈ g → Il-1 f ≈ Il-1 g
congIl-1 refl≈ = refl≈
congIl-1 (sym≈ p) = sym≈ (congIl-1 p)
congIl-1 (trans≈ p p₁) = trans≈ (congIl-1 p) (congIl-1 p₁)
congIl-1 (congIl p) = p
congIl-1 (cong⊗r p p₁) = cong⊗r (congIl-1 p) p₁
congIl-1 axI = refl≈
congIl-1 ⊗rIl = refl≈              

⊗l-1 : {Γ : Cxt} → {A B C : Tm} → 
            just (A ⊗ B) ∣ Γ ⊢ C → just A ∣ B ∷ Γ ⊢ C
⊗l-1 ax = ⊗r ax (uf ax)
⊗l-1 (⊗r f f₁) = ⊗r (⊗l-1 f) f₁
⊗l-1 (⊗l f) = f

⊗l-iso : {Γ : Cxt} → {A B C : Tm} → 
            (f : just (A ⊗ B) ∣ Γ ⊢ C) → ⊗l (⊗l-1 f) ≈ f
⊗l-iso ax = sym≈ ax⊗
⊗l-iso (⊗r f f₁) = trans≈ (sym≈ ⊗r⊗l) (cong⊗r (⊗l-iso f) refl≈)
⊗l-iso (⊗l f) = refl≈            

cong⊗l-1 : {Γ : Cxt} → {A B C : Tm} → 
            {f g : just (A ⊗ B) ∣ Γ ⊢ C} →
            f ≈ g → ⊗l-1 f ≈ ⊗l-1 g
cong⊗l-1 refl≈ = refl≈
cong⊗l-1 (sym≈ p) = sym≈ (cong⊗l-1 p)
cong⊗l-1 (trans≈ p p₁) = trans≈ (cong⊗l-1 p) (cong⊗l-1 p₁)
cong⊗l-1 (cong⊗l p) = p
cong⊗l-1 (cong⊗r p p₁) = cong⊗r (cong⊗l-1 p) p₁
cong⊗l-1 ax⊗ = refl≈
cong⊗l-1 ⊗r⊗l = refl≈            
            


-- admissibility of cut

-- -- (There are two kinds of cut: stoup ccut and context cut.)

mutual 
  scut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Tm} → 
              S ∣ Γ ⊢ A  →  just A ∣ Δ' ⊢ C  →  S ∣ Γ ++ Δ' ⊢ C

  scut ax g = g
  scut (uf f) g = uf (scut f g)
  scut Ir g = Il-1 g
  scut (⊗r f f') ax = ⊗r f f'
  scut (⊗r f f') (⊗r g g') = ⊗r (scut (⊗r f f') g) g'
  scut (⊗r {Γ = Γ} f f') (⊗l g) = ccut Γ f' (scut f g) refl
  scut (Il f) g = Il (scut f g)
  scut (⊗l f) g = ⊗l (scut f g)


  ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Tm} → 
             nothing ∣ Γ ⊢ A  →  T ∣ Δ ⊢ C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        T ∣ (Δ₀ ++ Γ) ++ Δ' ⊢ C
  
  ccut Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
  ccut Δ₀ f (uf g) p with cases∷ Δ₀ p 
  ccut .[] f (uf g) p | inj₁ (refl , refl , refl) = scut f g
  ccut .(_ ∷ Δ₀) f (uf g) p | inj₂ (Δ₀ , r , refl) =  uf (ccut Δ₀ f g r)
  ccut Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
  ccut Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
  ccut Δ₀ f (⊗r g g') p | inj₁ (Γ₀ , refl , refl) = ⊗r (ccut Δ₀ f g refl) g'
  ccut ._ f (⊗r g g') p | inj₂ (Γ₀ , refl , refl) = ⊗r g (ccut Γ₀  f g' refl)
  ccut Δ₀ f (Il g) r = Il (ccut Δ₀ f g r) 
  ccut Δ₀ f (⊗l {B = B} g) r = ⊗l (ccut (B ∷ Δ₀) f g (cong (_∷_ B) r))

subeq : {S : Stp} → {Γ Γ' : Cxt} → {A : Tm} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subeq refl f = f





{-




--  scut (⊗r {S} {Γ} {Δ} f f') ax =  
--          subeq (++ru (Γ ++ Δ)) (⊗r f f')
--  scut (⊗r {S} {Γ} {Δ} f f') (⊗r g g') = 
--          subeq (++ass (Γ ++ Δ)) (⊗r (scut (⊗r f f') g) g')
--  scut (⊗r {S} {Γ} {Δ} f f') (⊗l g) = 
--          ccut Γ f' (scut f g) refl


-- derivations with propositionally equal contexts

subeq : {S : Stp} → {Γ Γ' : Cxt} → {A : Tm} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subeq refl f = f

subeq' : {S S' : Stp} → {Γ : Cxt} → {A : Tm} → 
      S ≡ S' → S ∣ Γ ⊢ A → S' ∣ Γ ⊢ A 
subeq' refl f = f

subeqtrans : ∀{S}{Γ}{Γ'}{Γ''}{A} → {f : S ∣ Γ ⊢ A}
  → (p : Γ ≡ Γ')(q : Γ' ≡ Γ'')
  → subeq (trans p q) f ≡ subeq q (subeq p f)
subeqtrans refl refl = refl

subeqIl : ∀{Γ}{Γ'}{C} → {f : nothing ∣ Γ ⊢ C} → (p : Γ ≡ Γ')
  → subeq p (Il f) ≡ Il (subeq p f)
subeqIl refl = refl

subeqIl-1 : ∀{Γ}{Γ'}{C} → {f : just I ∣ Γ ⊢ C} → (p : Γ ≡ Γ')
  → subeq p (Il-1 f) ≡ Il-1 (subeq p f)
subeqIl-1 refl = refl  

subeq⊗l : ∀{Γ}{Γ'}{A}{B}{C} → {f : just A ∣ B ∷ Γ ⊢ C} → (p : Γ ≡ Γ')
  → subeq p (⊗l f) ≡ ⊗l (subeq (cong (_∷_ B) p) f)
subeq⊗l refl = refl

subeq⊗l-1 : ∀{Γ}{Γ'}{A}{B}{C} → {f : just (A ⊗ B) ∣ Γ ⊢ C} → (p : Γ ≡ Γ')
  → subeq (cong (_∷_ B) p) (⊗l-1 f) ≡ ⊗l-1 (subeq p f)
subeq⊗l-1 refl = refl

subeq⊗r : ∀{S}{Γ}{Γ'}{Δ}{Λ}{A}{B} → {f : S ∣ Γ ⊢ A} {g : nothing ∣ Δ ⊢ B}
  → (r : Γ' ++ Δ ≡ Λ)(p : Γ ≡ Γ') → ⊗r (subeq p f) g r ≡ ⊗r f g (trans (cong (λ a → a ++ Δ) p) r)
subeq⊗r r refl = refl

subeq⊗r₂ : ∀{S}{Γ}{Δ}{Δ'}{Λ}{A}{B} → {f : S ∣ Γ ⊢ A} {g : nothing ∣ Δ ⊢ B}
  → (r : Γ ++ Δ' ≡ Λ)(p : Δ ≡ Δ') → ⊗r f (subeq p g) r ≡ ⊗r f g (trans (cong (_++_ Γ) p) r)
subeq⊗r₂ r refl = refl

subeq⊗r' : ∀{S}{Γ}{Δ}{Λ}{Λ'}{A}{B} → {f : S ∣ Γ ⊢ A} {g : nothing ∣ Δ ⊢ B}
  → (r : Γ ++ Δ ≡ Λ)(p : Λ ≡ Λ') → subeq p (⊗r f g r) ≡ ⊗r f g (trans r p)
subeq⊗r' refl refl = refl

subequf : ∀{Γ}{Γ'}{Λ}{A}{C} → {f : just A ∣ Γ ⊢ C}
  → (r : A ∷ Γ' ≡ Λ)(p : Γ ≡ Γ') → uf (subeq p f) r ≡ uf f (trans (cong (_∷_ A) p) r)
subequf r refl = refl

subequf' : ∀{Γ}{Λ}{Λ'}{A}{C} → {f : just A ∣ Γ ⊢ C}
  → (r : A ∷ Γ ≡ Λ)(p : Λ ≡ Λ') → subeq p (uf f r) ≡ uf f (trans r p)
subequf' refl refl = refl

scutsubeq : {S : Stp} → {Γ Δ Δ' : Cxt} → {A B : Tm} → 
            (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(p : Δ ≡ Δ') → 
        scut f (subeq p g) ≡ subeq (cong (_++_ Γ) p) (scut f g)
scutsubeq f g refl = refl

scutsubeq2 : {S : Stp} → {Γ Δ Γ' : Cxt} → {A B : Tm} → 
            (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(p : Γ ≡ Γ') → 
        scut (subeq p f) g ≡ subeq (cong (λ a → a ++ Δ) p) (scut f g)
scutsubeq2 f g refl = refl

ccutsubeq : {T : Stp} → {Γ Δ Δ₁ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Tm} → 
             (f : nothing ∣ Γ ⊢ A){g :  T ∣ Δ ⊢ C}(r : Δ₁ ≡ Δ₀ ++ A ∷ Δ')(p : Δ ≡ Δ₁) →
             ccut Δ₀ f (subeq p g) r ≡ ccut Δ₀ f g (trans p r)
ccutsubeq Δ₀ f r refl = refl             

ccutsubeq2 : {T : Stp} → {Γ Δ Δ₁ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Tm} → 
             (f : nothing ∣ Γ ⊢ A){g :  T ∣ Δ₁ ⊢ C}(r : Δ₁ ≡ Δ₀ ++ A ∷ Δ')(p : Δ₁ ≡ Δ) →
             ccut Δ₀ f g r ≡ ccut Δ₀ f (subeq p g) (trans (sym p) r)
ccutsubeq2 Δ₀ f r refl = refl             
-}

