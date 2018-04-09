{-# OPTIONS --rewriting #-}

module StrongComplete where

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
open import MulticatLaws
open import Complete
open import Sound

strcmplt : {S : Stp}{Γ : Cxt}{C : Tm} → 〈 S ∣ Γ 〉 ⇒ C → S ∣ Γ ⊢ C
strcmplt {S}{Γ} f = ⊗l-1⋆ S Γ (cmplt f)

strcmpltsound : {S : Stp} → {Γ : Cxt} → {C : Tm} → (f : S ∣ Γ ⊢ C) →
                 strcmplt (sound f) ≈ f
strcmpltsound {S}{Γ} f =
  proof≈
  strcmplt (sound f)
  ≈〈 cong⊗l-1⋆ {S}{Γ} (cmpltsound' f) 〉
  ⊗l-1⋆ S Γ (⊗l⋆ S Γ f)
  ≈〈 ≡-to-≈ ⊗l⋆-iso 〉
  f
  qed≈

≐strcmplt≈ : {S : Stp}{Γ : Cxt}{C : Tm}{f g : 〈 S ∣ Γ 〉 ⇒ C} → f ≐ g →
                strcmplt {S}{Γ} f ≈ strcmplt g
≐strcmplt≈ {S}{Γ} p = cong⊗l-1⋆ {S} {Γ} (≐cmplt≈ p)

soundIl-1 : {Γ : Cxt}{C : Tm}{f : just I ∣ Γ ⊢ C}
  → sound (Il-1 f) ≐ sound f
soundIl-1 {f = ax} = refl≐
soundIl-1 {f = ⊗r f g} = soundIl-1 {f = f} ⊗≐ refl≐ ∘≐ refl≐
soundIl-1 {f = Il f} = refl≐

sound⊗l-1 : {Γ : Cxt}{A B C : Tm}{f : just (A ⊗ B) ∣ Γ ⊢ C}
  → sound (⊗l-1 f) ≐ sound f
sound⊗l-1 {f = ax} =
  proof
  id ⊗ (id ∘ l) ∘ ((id ∘ α) ∘ (ρ ⊗ id))
  ≐〈 refl≐ ⊗≐ lid ∘≐ (lid ∘≐ refl≐) 〉
  id ⊗ l ∘ (α ∘ ρ ⊗ id)
  ≐〈 sym≐ ass 〉
  id ⊗ l ∘ α ∘ ρ ⊗ id
  ≐〈 sym≐ lαρ 〉
  id
  qed
sound⊗l-1 {f = ⊗r f g} = sound⊗l-1 {f = f} ⊗≐ refl≐ ∘≐ refl≐
sound⊗l-1 {f = ⊗l f} = refl≐

sound⊗l-1⋆ : {S : Stp}{Γ : Cxt}{C : Tm}{f : just 〈 S ∣ Γ 〉 ∣ [] ⊢ C}
  → sound (⊗l-1⋆ S Γ f) ≐ sound f
sound⊗l-1⋆ {just A} {[]} = refl≐
sound⊗l-1⋆ {just A} {B ∷ Γ} {f = f} =
  proof
  sound (⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f))
  ≐〈 sound⊗l-1 {f = ⊗l-1⋆ (just (A ⊗ B)) Γ f} 〉
  sound (⊗l-1⋆ (just (A ⊗ B)) Γ f)
  ≐〈 sound⊗l-1⋆ {S = just (A ⊗ B)}{Γ} 〉
  sound f
  qed
sound⊗l-1⋆ {nothing} {[]}{f = f} = soundIl-1 {f = f}
sound⊗l-1⋆ {nothing} {B ∷ Γ}{f = f} =
  proof
  sound (Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)))
  ≐〈 soundIl-1 {f = ⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)} 〉
  sound (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f))
  ≐〈 sound⊗l-1 {f = ⊗l-1⋆ (just (I ⊗ B)) Γ f} 〉
  sound (⊗l-1⋆ (just (I ⊗ B)) Γ f)
  ≐〈 sound⊗l-1⋆ {just (I ⊗ B)}{Γ} 〉
  sound f
  qed

soundstrcmplt : {S : Stp}{Γ : Cxt}{C : Tm}(f : 〈 S ∣ Γ 〉 ⇒ C) →
           sound (strcmplt {S}{Γ} f) ≐ f 
soundstrcmplt {S}{Γ} f =
  proof
  sound (strcmplt {S}{Γ} f)
  ≐〈 sound⊗l-1⋆ {S}{Γ} 〉
  sound (cmplt f)
  ≐〈 soundcmplt f 〉
  f
  qed
