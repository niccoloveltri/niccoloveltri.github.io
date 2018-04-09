{-# OPTIONS --rewriting #-}

module FocusingComplete where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Utilities

open import FreeSkewMonCat
open import Focusing 

open import SeqCalc
open import Complete


-- ====================================================================

-- focusing completeness

-- admissibility of scut, ccut in the focused calculus
-- (called scutL, ccutL)

mutual 
  scutL : {S : Stp} → {Γ Δ' : Cxt} → {A C : Tm} → 
              S ∣ Γ ⊢L A  →  just A ∣ Δ' ⊢L C  →  S ∣ Γ ++ Δ' ⊢L C

  scutL (uf f) g = uf (scutL f g)
  scutL (Il f) g = Il (scutL f g)
  scutL (⊗l f) g = ⊗l (scutL f g)
  scutL (msw refl f) g = scutR f g

  scutR : {S : StpR} →
              {Γ Δ' : Cxt} → {A C : Tm} → 
              S ∣ Γ ⊢R A  →  just A ∣ Δ' ⊢L C  →  mmap ` S ∣ Γ ++ Δ' ⊢L C
  scutR ax g = g
  scutR Ir (Il g) = g
  scutR Ir (msw {just X} () g)
  scutR Ir (msw {nothing} () g) 
  scutR (⊗r {Γ = Γ} f₁ f₂) (⊗l g) = ccutL Γ f₂ (scutR f₁ g) refl
  scutR (⊗r f₁ f₂) (msw {just x} () g)
  scutR (⊗r f₁ f₂) (msw {nothing} () g)
 

  ccutL : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Tm} → 
             nothing ∣ Γ ⊢L A  →  T ∣ Δ ⊢L C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        T ∣ (Δ₀ ++ Γ) ++ Δ' ⊢L C
  
  ccutL Δ₀ f (uf g) p with cases∷ Δ₀ p 
  ccutL .[] f (uf g) p | inj₁ (refl , refl , refl) = scutL f g
  ccutL .(_ ∷ Δ₀) f (uf g) p | inj₂ (Δ₀ , r , refl) =  uf (ccutL Δ₀ f g r)
  ccutL Δ₀ f (Il g) r = Il (ccutL Δ₀ f g r) 
  ccutL Δ₀ f (⊗l {B = B} g) r = ⊗l (ccutL (B ∷ Δ₀) f g (cong (_∷_ B) r))
  ccutL Δ₀ f (msw refl g) r = msw refl (ccutR Δ₀ f g r)

  ccutR : {T : StpR} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Tm} → 
             nothing ∣ Γ ⊢L A  →  T ∣ Δ ⊢R C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                       T  ∣ (Δ₀ ++ Γ) ++ Δ' ⊢R C
  ccutR Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
  ccutR Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
  ccutR Δ₀ {Δ'} f (⊗r {T} {Γ} {Δ} g₁ g₂) p with cases++ Δ₀ Γ Δ' Δ p
  ccutR Δ₀ f (⊗r g₁ g₂) p | inj₁ (Γ₀ , refl , refl) = 
     ⊗r (ccutR Δ₀ f g₁ refl) g₂
  ccutR ._ {Δ'} f (⊗r g₁ g₂) p | inj₂ (Γ₀ , refl , refl) =
     ⊗r g₁ (ccutL Γ₀ f g₂ refl)                                         

-- focusing completeness

focus-cmplt : {A B : Tm} → A ⇒ B → just A ∣ [] ⊢L B
focus-cmplt id = axL
focus-cmplt (f ∘ g) = scutL (focus-cmplt g) (focus-cmplt f)
focus-cmplt (f ⊗ g) = ⊗l (⊗rL (focus-cmplt f) (uf (focus-cmplt g)))
focus-cmplt l = ⊗l (Il (uf axL))
focus-cmplt ρ = ⊗rL axL (msw refl Ir)
focus-cmplt α = ⊗l (⊗l (⊗rL axL (uf (⊗rL axL (uf axL)))))



-- =====================================================================

-- correctness of focusing completeness in the sense
-- that it is the same as completeness followed by focusing


scutR-Ir-⊗rL : {Γ Δ : Cxt} → {A B : Tm}
     (f : just I ∣ Γ ⊢L A)(g : nothing ∣ Δ ⊢L B) → 
     ⊗rL (scutR Ir f) g ≡ scutR Ir (⊗rL f g)
scutR-Ir-⊗rL (Il f) g = refl
scutR-Ir-⊗rL (msw {just X} () f) g
scutR-Ir-⊗rL (msw {nothing} () f) g


scutL-⊗rL-⊗l : {S : Stp} → {Γ₁ Γ₂ Δ : Cxt} → {A B C : Tm} →
  (f₁ : S ∣ Γ₁ ⊢L A)(f₂ : nothing ∣ Γ₂ ⊢L B)(g : just A ∣ B ∷ Δ ⊢L C) → 
  scutL (⊗rL f₁ f₂) (⊗l g) ≡ ccutL Γ₁ f₂ (scutL f₁ g) refl
scutL-⊗rL-⊗l (uf f₁) f₂ g = cong uf (scutL-⊗rL-⊗l f₁ f₂ g)
scutL-⊗rL-⊗l (Il f₁) f₂ g = cong Il (scutL-⊗rL-⊗l f₁ f₂ g)
scutL-⊗rL-⊗l (⊗l f₁) f₂ g = cong ⊗l (scutL-⊗rL-⊗l f₁ f₂ g)
scutL-⊗rL-⊗l (msw refl f₁) f₂ g = refl

subeqL : {S : Stp} → {Γ Γ' : Cxt} → {A : Tm} → 
      Γ ≡ Γ' → S ∣ Γ ⊢L A → S ∣ Γ' ⊢L A 
subeqL refl f = f

subeqR : {S : StpR} → {Γ Γ' : Cxt} → {A : Tm} → 
      Γ ≡ Γ' → S ∣ Γ ⊢R A → S ∣ Γ' ⊢R A 
subeqR refl f = f

focus-Il-1 : {Δ : Cxt} → {C : Tm} →(g : just I ∣ Δ ⊢ C) →
              focus (Il-1 g) ≡ scutR Ir (focus g)
focus-Il-1 ax = refl
focus-Il-1 (⊗r f f') =
  trans (cong (λ a → ⊗rL a (focus f')) (focus-Il-1 f))
        (scutR-Ir-⊗rL (focus f) (focus f'))
focus-Il-1 (Il f) = refl

mutual
  scutL-unit : {Δ : Cxt} → {A C : Tm} →(g : just A ∣ Δ ⊢L C) →
               scutL axL g ≡ g
  scutL-unit (Il g) = refl
  scutL-unit (⊗l g) =
    cong ⊗l (trans (scutL-⊗rL-⊗l axL (uf axL) g)
                   (trans (ccutL-unit [] (scutL axL g) refl)
                          (scutL-unit g)))
  scutL-unit (msw {just A} refl f) = refl
  scutL-unit (msw {nothing} () f)

  ccutL-unit : {T : Stp}{Γ Δ : Cxt}(Δ₀ : Cxt){A C : Tm}
    → (g : T ∣ Δ ⊢L C)(r : Δ ≡ Δ₀ ++ A ∷ Γ)
    → ccutL Δ₀ (uf axL) g r ≡ subeqL r g
  ccutL-unit Δ₀ (uf g) r with cases∷ Δ₀ r
  ccutL-unit .[] (uf g) refl | inj₁ (refl , refl , refl) =
    cong uf (scutL-unit g)
  ccutL-unit ._ (uf g) refl | inj₂ (Γ₀ , refl , refl) =
    cong uf (ccutL-unit Γ₀ g refl)
  ccutL-unit Δ₀ (Il g) refl = cong Il (ccutL-unit Δ₀ g refl)
  ccutL-unit Δ₀ (⊗l g) refl = cong ⊗l (ccutL-unit (_ ∷ Δ₀) g refl)
  ccutL-unit Δ₀ (msw refl g) refl = cong (msw refl) (ccutR-unit Δ₀ g refl)

  ccutR-unit : {T : StpR}{Γ Δ : Cxt}(Δ₀ : Cxt){A C : Tm}
    → (g : T ∣ Δ ⊢R C)(r : Δ ≡ Δ₀ ++ A ∷ Γ)
    → ccutR Δ₀ (uf axL) g r ≡ subeqR r g
  ccutR-unit Δ₀ ax r = ⊥-elim ([]disj∷ Δ₀ r)
  ccutR-unit Δ₀ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  ccutR-unit {Γ = Γ} Δ₀ (⊗r {Γ = Γ₁}{Γ₂} g g') r with cases++ Δ₀ Γ₁ Γ Γ₂ r
  ccutR-unit Δ₀ (⊗r g g') refl | inj₁ (Γ₀ , refl , refl) =
    cong (λ a → ⊗r a g') (ccutR-unit Δ₀ g refl)
  ccutR-unit ._ (⊗r g g') refl | inj₂ (Γ₀ , refl , refl) = 
    cong (⊗r g) (ccutL-unit Γ₀ g' refl)

mutual
  scutL-⊗rL : {S : Stp} → {Γ Δ Δ' : Cxt} → {A B C : Tm} → 
    (f : S ∣ Γ ⊢L A)(g : just A ∣ Δ ⊢L B)(g' : nothing ∣ Δ' ⊢L C) → 
    scutL f (⊗rL g g') ≡ ⊗rL (scutL f g) g'
  scutL-⊗rL (uf f) g g' = cong uf (scutL-⊗rL f g g')
  scutL-⊗rL (Il f) g g' = cong Il (scutL-⊗rL f g g')
  scutL-⊗rL (⊗l f) g g' = cong ⊗l (scutL-⊗rL f g g')
  scutL-⊗rL (msw refl f) g g' = scutR-⊗rL f g g'

  scutR-⊗rL : {S : StpR} → {Γ Δ Δ' : Cxt} → {A B C : Tm} → 
    (f : S ∣ Γ ⊢R A)(g : just A ∣ Δ ⊢L B)(g' : nothing ∣ Δ' ⊢L C) → 
    scutR f (⊗rL g g') ≡ ⊗rL (scutR f g) g'
  scutR-⊗rL ax g g' = refl
  scutR-⊗rL Ir g g' = sym (scutR-Ir-⊗rL g g')
  scutR-⊗rL (⊗r f f') g g' = scutR-⊗r-⊗rL f f' g g' 

  scutR-⊗r-⊗rL : {S : StpR} → {Γ Γ' Δ Δ' : Cxt} → {A B C D : Tm} →
    (f : S ∣ Γ ⊢R A)(f' : nothing ∣ Γ' ⊢L B) →
    (g : just (A ⊗ B) ∣ Δ ⊢L C)(g' : nothing ∣ Δ' ⊢L D) →
    scutR (⊗r f f') (⊗rL g g') ≡ ⊗rL (scutR (⊗r f f') g) g'
  scutR-⊗r-⊗rL {Γ = Γ} f f' (⊗l g) g' =
    trans (cong₂ (ccutL Γ f') (scutR-⊗rL f g g') refl)
          (ccutL-⊗rL Γ f' (scutR f g) g' refl)
  scutR-⊗r-⊗rL f f' (msw {just X} () g) g'
  scutR-⊗r-⊗rL f f' (msw {nothing} () g) g'

  ccutL-⊗rL : {S : Stp} → (Γ : Cxt) → {Γ' Δ Δ' Λ : Cxt} → {B C D : Tm} →
    (f : nothing ∣ Γ' ⊢L B) →
    (g : S ∣ Λ ⊢L C)(g' : nothing ∣ Δ' ⊢L D) →
    (r : Λ ≡ Γ ++ B ∷ Δ) →
    ccutL Γ f (⊗rL g g') (cong (λ a → a ++ Δ') r) ≡ ⊗rL (ccutL Γ f g r) g'
  ccutL-⊗rL Γ {Δ' = Δ'} f (uf g) g' r with cases∷ Γ r
  ccutL-⊗rL .[] f (uf g) g' refl | inj₁ (refl , refl , refl) = scutL-⊗rL f g g'
  ccutL-⊗rL ._ f (uf g) g' refl | inj₂ (Γ₀ , refl , refl) =
    cong uf (ccutL-⊗rL Γ₀ f g g' refl)
  ccutL-⊗rL Γ f (Il g) g' refl = cong Il (ccutL-⊗rL Γ f g g' refl)
  ccutL-⊗rL Γ f (⊗l g) g' refl = cong ⊗l (ccutL-⊗rL (_ ∷ Γ) f g g' refl)
  ccutL-⊗rL Γ {Δ = Δ}{Δ'} {B = B} f (msw refl g) g' refl
    with cases++ Γ (Γ ++ B ∷ Δ) (Δ ++ Δ') Δ' refl
  ccutL-⊗rL Γ {Δ = Δ}{Δ'} f (msw refl g) g' refl | inj₁ (Γ₀ , p , q)
    with canc++ Δ Γ₀ {Δ'} q
  ccutL-⊗rL Γ f (msw refl g) g' refl | inj₁ (Δ , refl , refl) | refl = refl
  ccutL-⊗rL Γ {Δ = Δ}{Δ'} f (msw refl g) g' refl | inj₂ (Γ₀ , p , q) =
    ⊥-elim (canc⊥3 Δ Δ' Γ₀ p)

ccutL-⊗rL2 : {S : Stp} → (Γ : Cxt) → {Γ' Δ Δ' Λ : Cxt} → {B C D : Tm} →
  (f : nothing ∣ Γ' ⊢L B) →
  (g : S ∣ Δ' ⊢L C)(g' : nothing ∣ Λ ⊢L D) →
  (r : Λ ≡ Γ ++ B ∷ Δ) →
  ccutL (Δ' ++ Γ) f (⊗rL g g') (cong (_++_ Δ') r) ≡ ⊗rL g (ccutL Γ f g' r)
ccutL-⊗rL2 Γ f (uf g) g' refl = cong uf (ccutL-⊗rL2 Γ f g g' refl)
ccutL-⊗rL2 Γ f (Il g) g' refl = cong Il (ccutL-⊗rL2 Γ f g g' refl)
ccutL-⊗rL2 Γ f (⊗l g) g' refl = cong ⊗l (ccutL-⊗rL2 Γ f g g' refl)
ccutL-⊗rL2 Γ {Δ = Δ}{Δ'}{B = B} f (msw refl g) g' refl
  with cases++ (Δ' ++ Γ) Δ' Δ (Γ ++ B ∷ Δ) refl
ccutL-⊗rL2 Γ {Δ = Δ} f (msw refl g) g' refl | inj₁ (Γ₀ , p , q) =
  ⊥-elim (canc⊥3 [] Δ (Γ₀ ++ Γ) q)
ccutL-⊗rL2 Γ {Δ' = Δ'} f (msw refl g) g' refl | inj₂ (Γ₀ , p , q)
  with ++canc {xs = Γ}{Γ₀} Δ' q
ccutL-⊗rL2 Γ f (msw refl g) g' refl | inj₂ (.Γ , refl , refl) | refl = refl

mutual
  scutL-unit2 : {S : Stp} → {Δ : Cxt} → {C : Tm} →(g : S ∣ Δ ⊢L C) →
               scutL g axL ≡ g
  scutL-unit2 (uf g) = cong uf (scutL-unit2 g)
  scutL-unit2 (Il g) = cong Il (scutL-unit2 g)
  scutL-unit2 (⊗l g) = cong ⊗l (scutL-unit2 g)
  scutL-unit2 (msw refl g) = scutR-unit2 g

  scutR-unit2 : {S : StpR} → {Δ : Cxt} → {C : Tm} →(g : S ∣ Δ ⊢R C) →
               scutR g axL ≡ msw refl g
  scutR-unit2 ax = refl
  scutR-unit2 Ir = refl
  scutR-unit2 (⊗r {Γ = Γ} g g') =
    trans (cong₂ (ccutL Γ g') (scutR-⊗rL g axL (uf axL)) refl)
          (trans (ccutL-⊗rL2 [] g' (scutR g axL) (uf axL) refl)
                 (cong₂ ⊗rL (scutR-unit2 g) (scutL-unit2 g')))

mutual
  focus-scut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Tm} → 
               (f : S ∣ Γ ⊢ A)  →  (g : just A ∣ Δ' ⊢ C) →
               focus (scut f g) ≡ scutL (focus f) (focus g)
  focus-scut ax g = sym (scutL-unit (focus g))
  focus-scut (uf f) g = cong uf (focus-scut f g)
  focus-scut Ir g = focus-Il-1 g
  focus-scut (⊗r {Γ = Γ} f f') ax =
    sym (trans (scutL-⊗rL-⊗l (focus f) (focus f') (⊗rL axL (uf axL)))
               (trans (cong₂ (ccutL Γ (focus f')) (scutL-⊗rL (focus f) axL (uf axL)) refl)
                      (trans (ccutL-⊗rL2 [] (focus f') (scutL (focus f) axL) (uf axL) refl)
                             (cong₂ ⊗rL (scutL-unit2 (focus f)) (scutL-unit2 (focus f'))))))
  focus-scut (⊗r f f') (⊗r g g') =
    trans (cong₂ ⊗rL (focus-scut (⊗r f f') g) refl)
          (sym (scutL-⊗rL (⊗rL (focus f) (focus f')) (focus g) (focus g')))
  focus-scut (⊗r {Γ = Γ} f f') (⊗l g) =
    trans (focus-ccut Γ f' (scut f g) refl)
          (trans (cong₂ (ccutL Γ (focus f')) (focus-scut f g) refl)
                 (sym (scutL-⊗rL-⊗l (focus f) (focus f') (focus g))))
  focus-scut (Il f) g = cong Il (focus-scut f g)
  focus-scut (⊗l f) g = cong ⊗l (focus-scut f g) 

  focus-ccut : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Tm} → 
             (f : nothing ∣ Γ ⊢ A)  →  (g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
             focus (ccut Δ₀ f g r) ≡ ccutL Δ₀ (focus f) (focus g) r
  focus-ccut Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
  focus-ccut Δ₀ f (uf g) r with cases∷ Δ₀ r
  focus-ccut .[] f (uf g) refl | inj₁ (refl , refl , refl) = focus-scut f g
  focus-ccut ._ f (uf g) r | inj₂ (Γ₀ , refl , refl) = cong uf (focus-ccut Γ₀ f g refl)
  focus-ccut Δ₀ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
  focus-ccut Δ₀ {Δ' = Δ'} f (⊗r {Γ = Γ}{Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
  focus-ccut Δ₀ f (⊗r g g') refl | inj₁ (Γ₀ , refl , refl) =
    trans (cong₂ ⊗rL (focus-ccut Δ₀ f g refl) refl)
          (sym (ccutL-⊗rL Δ₀ (focus f) (focus g) (focus g') refl))
  focus-ccut ._ f (⊗r g g') refl | inj₂ (Γ₀ , refl , refl) = 
    trans (cong (⊗rL (focus g)) (focus-ccut Γ₀ f g' refl))
          (sym (ccutL-⊗rL2 Γ₀ (focus f) (focus g) (focus g') refl))
  focus-ccut Δ₀ f (Il g) refl = cong Il (focus-ccut Δ₀ f g refl)
  focus-ccut Δ₀ f (⊗l g) refl = cong ⊗l (focus-ccut (_ ∷ Δ₀) f g refl)
  

focus-cmplt-correct : {A B : Tm} → (f : A ⇒ B) →
           focus (cmplt f) ≡ focus-cmplt f
focus-cmplt-correct id = refl
focus-cmplt-correct (f ∘ g) =
   trans (focus-scut (cmplt g) (cmplt f))
         (cong₂ scutL (focus-cmplt-correct g) (focus-cmplt-correct f))
focus-cmplt-correct (f ⊗ g) = 
   cong ⊗l (cong₂ ⊗rL (focus-cmplt-correct f)
                       (cong uf (focus-cmplt-correct g)))
focus-cmplt-correct l = refl
focus-cmplt-correct ρ = refl
focus-cmplt-correct α = refl            
