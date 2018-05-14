{-# OPTIONS --rewriting #-}

module Complete where

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

scut⊗ruf : {Γ Δ Δ' : Cxt}{A A' B C : Tm}
  → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (f' : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (uf f) g) f' ≈ uf (scut (⊗r f g) f')
scut⊗ruf ax = ⊗ruf
scut⊗ruf {f = f}{g} (⊗r h h') =
  proof≈
  ⊗r (scut (⊗r (uf f) g) h) h'
  ≈〈 cong⊗r (scut⊗ruf h) refl≈ 〉
  ⊗r (uf (scut (⊗r f g) h)) h'
  ≈〈 ⊗ruf 〉
  uf (⊗r (scut (⊗r f g) h) h')
  qed≈
scut⊗ruf (⊗l h) = refl≈

scut⊗rIl : {Γ Δ Δ' : Cxt}{A B C : Tm}
  → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (Il f) g) h ≈ Il (scut (⊗r f g) h)
scut⊗rIl ax = ⊗rIl
scut⊗rIl {f = f}{g}(⊗r h h') =
  proof≈
  ⊗r (scut (⊗r (Il f) g) h) h'
  ≈〈 cong⊗r (scut⊗rIl h) refl≈ 〉
  ⊗r (Il (scut (⊗r f g) h)) h'
  ≈〈 ⊗rIl 〉
  Il (⊗r (scut (⊗r f g) h) h')
  qed≈
scut⊗rIl (⊗l h) = refl≈

scut⊗r⊗l : {Γ Δ Δ' : Cxt}{A A' B B' C : Tm}
  → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (⊗l f) g) h ≈ ⊗l (scut (⊗r f g) h)
scut⊗r⊗l ax = ⊗r⊗l
scut⊗r⊗l {f = f}{g} (⊗r h h') =
  proof≈
  ⊗r (scut (⊗r (⊗l f) g) h) h'
  ≈〈 cong⊗r (scut⊗r⊗l h) refl≈ 〉
  ⊗r (⊗l (scut (⊗r f g) h)) h'
  ≈〈 ⊗r⊗l 〉
  ⊗l (⊗r (scut (⊗r f g) h) h')
  qed≈
scut⊗r⊗l (⊗l h) = refl≈

scut⊗r : ∀{S}{Γ}{Δ}{Δ'}{A}{B}{C}
  → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(g' : nothing ∣ Δ' ⊢ C)
  → scut f (⊗r g g') ≈ ⊗r (scut f g) g'
scut⊗r ax g g' = refl≈
scut⊗r (uf f) g g' =
  proof≈
  uf (scut f (⊗r g g'))
  ≈〈 conguf (scut⊗r f g g') 〉 
  uf (⊗r (scut f g) g')
  ≈〈 sym≈ ⊗ruf 〉 
  ⊗r (uf (scut f g)) g'
  qed≈
scut⊗r Ir g g' = refl≈
scut⊗r (⊗r f f') g g' = refl≈
scut⊗r (Il f) g g' =
  proof≈
  Il (scut f (⊗r g g'))
  ≈〈 congIl (scut⊗r f g g') 〉 
  Il (⊗r (scut f g) g')
  ≈〈 sym≈ ⊗rIl 〉 
  ⊗r (Il (scut f g)) g'
  qed≈
scut⊗r (⊗l f) g g' =
  proof≈
  ⊗l (scut f (⊗r g g'))
  ≈〈 cong⊗l (scut⊗r f g g') 〉 
  ⊗l (⊗r (scut f g) g')
  ≈〈 sym≈ ⊗r⊗l 〉 
  ⊗r (⊗l (scut f g)) g'
  qed≈

Il-1≈ : ∀{Γ}{A}{f g : just I ∣ Γ ⊢ A}
  → f ≈ g → Il-1 f ≈ Il-1 g
Il-1≈ refl≈ = refl≈
Il-1≈ (sym≈ p) = sym≈ (Il-1≈ p)
Il-1≈ (trans≈ p p') = trans≈ (Il-1≈ p) (Il-1≈ p')
Il-1≈ (congIl p) = p
Il-1≈ (cong⊗r p p') = cong⊗r (Il-1≈ p) p'
Il-1≈ axI = refl≈
Il-1≈ ⊗rIl = refl≈

mutual
  scut≈⊗r : ∀{S}{Γ}{Δ}{Δ'}{A}{B}{C}
    → {f g : S ∣ Γ ⊢ A}{f' g' : nothing ∣ Δ ⊢ B}
    → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
    → (p : f ≈ g)(q : f' ≈ g')
    → scut (⊗r f f') h ≈ scut (⊗r g g') h
  scut≈⊗r ax p q = cong⊗r p q
  scut≈⊗r (⊗r h h') p q = cong⊗r (scut≈⊗r h p q) refl≈
  scut≈⊗r {Γ = Γ}{f = f}{g}{f'}{g'} (⊗l h) p q =
    proof≈
    ccut Γ f' (scut f h) refl
    ≈〈 ccut≈2 Γ refl (scut≈ p) 〉
    ccut Γ f' (scut g h) refl
    ≈〈 ccut≈ Γ (scut g h) refl q 〉
    ccut Γ g' (scut g h) refl
    qed≈

  scut≈ : {S : Stp} → {Γ Δ' : Cxt} → {A C : Tm} → 
             {f g : S ∣ Γ ⊢ A}  → {h : just A ∣ Δ' ⊢ C} →
             f ≈ g → scut f h ≈ scut g h
  scut≈ refl≈ = refl≈
  scut≈ (sym≈ p) = sym≈ (scut≈ p)
  scut≈ (trans≈ p p₁) = trans≈ (scut≈ p) (scut≈ p₁)
  scut≈ (conguf p) = conguf (scut≈ p)
  scut≈ (cong⊗l p) = cong⊗l (scut≈ p)
  scut≈ (congIl p) = congIl (scut≈ p)
  scut≈ {h = h} (cong⊗r p p') = scut≈⊗r h p p'
  scut≈ axI = sym≈ (Il-iso _)
  scut≈ {h = h} ax⊗ =
    proof≈
    h
    ≈〈 sym≈ (⊗l-iso h) 〉
    ⊗l (⊗l-1 h)
    ≈〈 ≡-to-≈ (cong ⊗l (⊗l-1-alt h)) 〉
    ⊗l (scut (⊗r ax (uf ax)) h)
    qed≈
  scut≈ {h = h} ⊗ruf = scut⊗ruf h
  scut≈ {h = h} ⊗rIl = scut⊗rIl h
  scut≈ {h = h} ⊗r⊗l = scut⊗r⊗l h
  
  scut≈2 : {S : Stp} → {Γ Δ' : Cxt} → {A C : Tm} → 
             (h : S ∣ Γ ⊢ A)  → {f g : just A ∣ Δ' ⊢ C} →
             f ≈ g → scut h f ≈ scut h g
  scut≈2 ax p = p
  scut≈2 (uf h) p = conguf (scut≈2 h p)
  scut≈2 Ir p = Il-1≈ p
  scut≈2 (⊗r h h') refl≈ = refl≈
  scut≈2 (⊗r h h') (sym≈ p) = sym≈ (scut≈2 (⊗r h h') p)
  scut≈2 (⊗r h h') (trans≈ p p') = trans≈ (scut≈2 (⊗r h h') p) (scut≈2 (⊗r h h') p')
  scut≈2 (⊗r {Γ = Γ} h h') (cong⊗l p) = ccut≈2 Γ refl (scut≈2 h p)
  scut≈2 (⊗r h h') (cong⊗r p p') = cong⊗r (scut≈2 (⊗r h h') p) p'
  scut≈2 (⊗r {Γ = Γ} h h') ax⊗ with ccut≈2 Γ {f = h'} refl (sym≈ (scut⊗r h ax (uf ax)))
  scut≈2 (⊗r {Γ = Γ}{B = B} h h') ax⊗ | ih with cases++ Γ Γ [] (B ∷ []) refl
  scut≈2 (⊗r h h') ax⊗ | ih | inj₁ (Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ q)
  scut≈2 (⊗r {Γ = Γ} h h') ax⊗ | ih | inj₂ ([] , refl , refl) =
    proof≈
    ⊗r h h'
    ≈〈 sym≈ (cong⊗r (≡-to-≈ (scut-unit h)) (≡-to-≈ (scut-unit h'))) 〉
    ⊗r (scut h ax) (scut h' ax)
    ≈〈 ih 〉
    ccut Γ h' (scut h (⊗r ax (uf ax))) refl
    qed≈
  scut≈2 (⊗r h h') ax⊗ | ih | inj₂ (_ ∷ Γ₀ , p , q) = ⊥-elim ([]disj∷ Γ₀ (proj₂ (inj∷ p)))
  scut≈2 (⊗r {Γ = Γ} h h') (⊗r⊗l {f = f}{g}) with ccut≈2 Γ {f = h'} refl (sym≈ (scut⊗r h f g))
  scut≈2 (⊗r {Γ = Γ}{B = B} h h') (⊗r⊗l {Γ'}{Δ'}{f = f}{g}) | ih with cases++ Γ (Γ ++ B ∷ Γ') (Γ' ++ Δ') Δ' refl
  scut≈2 (⊗r {Γ = Γ} {B = B} h h') (⊗r⊗l {Γ'} {Δ'} {f = f} {g}) | ih | inj₁ (Γ₀ , p , q) with canc++ Γ' Γ₀ {Δ'}q
  scut≈2 (⊗r {Γ = Γ} {B = B} h h') (⊗r⊗l {Γ'} {Δ'} {f = f} {g}) | ih | inj₁ (.Γ' , refl , refl) | refl = ih
  scut≈2 (⊗r {Γ = Γ} {B = B} h h') (⊗r⊗l {Γ'} {Δ'} {f = f} {g}) | ih | inj₂ (Γ₀ , p , q) = ⊥-elim (canc⊥3 Γ' Δ' Γ₀ p)
  scut≈2 (Il h) p = congIl (scut≈2 h p)
  scut≈2 (⊗l h) p = cong⊗l (scut≈2 h p)

  ccut≈ : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Tm} → 
             {f f' : nothing ∣ Γ ⊢ A}(g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
             f ≈ f' → ccut Δ₀ f g r ≈ ccut Δ₀ f' g r
  ccut≈ Δ₀ ax r p = ⊥-elim ([]disj∷ Δ₀ r)
  ccut≈ Δ₀ (uf g) r p with cases∷ Δ₀ r
  ccut≈ .[] (uf g) r p | inj₁ (refl , refl , refl) = scut≈ p
  ccut≈ .(_ ∷ Δ₀) (uf g) r p | inj₂ (Δ₀ , refl , refl) = conguf (ccut≈ Δ₀ g refl p)
  ccut≈ Δ₀ Ir r p = ⊥-elim ([]disj∷ Δ₀ r)
  ccut≈ Δ₀ {Δ'} (⊗r {Γ = Γ}{Δ} g g') r p with cases++ Δ₀ Γ Δ' Δ r
  ccut≈ Δ₀ (⊗r g g') r p | inj₁ (Γ₀ , refl , refl) = cong⊗r (ccut≈ Δ₀ g refl p) refl≈
  ccut≈ ._ (⊗r g g') r p | inj₂ (Γ₀ , refl , refl) = cong⊗r refl≈ (ccut≈ Γ₀ g' refl p)
  ccut≈ Δ₀ (Il g) refl p = congIl (ccut≈ Δ₀ g refl p)
  ccut≈ Δ₀ (⊗l {B = B} g) refl p = cong⊗l (ccut≈ (B ∷ Δ₀) g refl p)
  
  ccut≈2 : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} →  {A C : Tm} → 
             {f : nothing ∣ Γ ⊢ A}{g g' : T ∣ Δ ⊢ C}  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
             g ≈ g' → ccut Δ₀ f g r ≈ ccut Δ₀ f g' r
  ccut≈2 Δ₀ r refl≈ = refl≈
  ccut≈2 Δ₀ r (sym≈ p) = sym≈ (ccut≈2 Δ₀ r p)
  ccut≈2 Δ₀ r (trans≈ p p₁) = trans≈ (ccut≈2 Δ₀ r p) (ccut≈2 Δ₀ r p₁)
  ccut≈2 Δ₀ r (conguf p) with cases∷ Δ₀ r
  ccut≈2 .[] {f = f} r (conguf p) | inj₁ (refl , refl , refl) = scut≈2 f p
  ccut≈2 .(_ ∷ Γ₀) r (conguf p) | inj₂ (Γ₀ , refl , refl) = conguf (ccut≈2 Γ₀ refl p)
  ccut≈2 Δ₀ refl (cong⊗l {B = B} p) = cong⊗l (ccut≈2 (B ∷ Δ₀) refl p)
  ccut≈2 Δ₀ refl (congIl p) = congIl (ccut≈2 Δ₀ refl p)
  ccut≈2 Δ₀ {Δ'} r (cong⊗r {Γ = Γ}{Δ} p p') with cases++ Δ₀ Γ Δ' Δ r
  ccut≈2 Δ₀ r (cong⊗r p p') | inj₁ (Γ₀ , refl , refl) = cong⊗r (ccut≈2 Δ₀ refl p) p'
  ccut≈2 ._ r (cong⊗r p p') | inj₂ (Γ₀ , refl , refl) = cong⊗r p (ccut≈2 Γ₀ refl p')
  ccut≈2 Δ₀ r axI = ⊥-elim ([]disj∷ Δ₀ r)
  ccut≈2 Δ₀ r ax⊗ = ⊥-elim ([]disj∷ Δ₀ r)
  ccut≈2 Δ₀ {Δ'} r (⊗ruf {Γ}{Δ}{A' = A'}) with cases++ Δ₀ (A' ∷ Γ) Δ' Δ r | cases∷ Δ₀ r
  ccut≈2 .[] {f = f} r (⊗ruf {f = g} {g'}) | inj₁ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = sym≈ (scut⊗r f g g')
  ccut≈2 ._ r ⊗ruf | inj₁ (Γ₀ , p , refl) | inj₂ (Γ₀' , t , refl) with inj∷ p
  ccut≈2 ._ {_}{A} r (⊗ruf {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) | refl , refl with cases++ Γ₀' (Γ₀' ++ A ∷ Γ₀) (Γ₀ ++ Δ) Δ refl
  ccut≈2 ._ r (⊗ruf {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) | refl , refl | inj₁ (Γ₀'' , p , q) with canc++ Γ₀ Γ₀'' {Δ} q
  ccut≈2 ._ r ⊗ruf | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) | refl , refl | inj₁ (.Γ₀ , refl , refl) | refl = ⊗ruf
  ccut≈2 ._ r (⊗ruf {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , refl , refl) | refl , refl | inj₂ (Γ₀'' , p , q) = ⊥-elim (canc⊥3 Γ₀ Δ Γ₀'' p)
  ccut≈2 ._ r ⊗ruf | inj₂ (Γ₀ , refl , refl) | inj₁ (s , () , u)
  ccut≈2 ._ r ⊗ruf | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , t , u) with inj∷ u
  ccut≈2 ._ {Δ'}{A} r (⊗ruf {Γ}) | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl , refl with cases++ (Γ ++ Γ₀) Γ Δ' (Γ₀ ++ A ∷ Δ') refl
  ccut≈2 ._ {Δ'} r ⊗ruf | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl , refl | inj₁ (Γ₀' , t , u) = ⊥-elim (canc⊥3 [] Δ' (Γ₀' ++ Γ₀) u)
  ccut≈2 ._ {Δ'}{A} r ⊗ruf | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl , refl | inj₂ (Γ₀' , t , u) with canc++ Γ₀ Γ₀' {A ∷ Δ'} t
  ccut≈2 ._ r ⊗ruf | inj₂ (Γ₀ , refl , refl) | inj₂ (._ , refl , refl) | refl , refl | inj₂ (.Γ₀ , refl , refl) | refl = ⊗ruf
  ccut≈2 Δ₀ {Δ'} r (⊗rIl {Γ}{Δ}) with cases++ Δ₀ Γ Δ' Δ r
  ccut≈2 Δ₀ r ⊗rIl | inj₁ (Γ₀ , refl , refl) = ⊗rIl
  ccut≈2 ._ r ⊗rIl | inj₂ (Γ₀ , refl , refl) = ⊗rIl
  ccut≈2 Δ₀ {Δ'} r (⊗r⊗l {Γ}{Δ}) with cases++ Δ₀ Γ Δ' Δ r
  ccut≈2 Δ₀ {_}{A} refl (⊗r⊗l {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) with cases++ Δ₀ (Δ₀ ++ A ∷ Γ₀) (Γ₀ ++ Δ) Δ refl
  ccut≈2 Δ₀ refl (⊗r⊗l {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {Δ} q
  ccut≈2 Δ₀ refl ⊗r⊗l | inj₁ (Γ₀ , refl , refl) | inj₁ (.Γ₀ , refl , refl) | refl = ⊗r⊗l
  ccut≈2 Δ₀ refl (⊗r⊗l {Δ = Δ}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) = ⊥-elim (canc⊥3 Γ₀ Δ Γ₀' p)
  ccut≈2 ._ {Δ'}{A} refl (⊗r⊗l {Γ}) | inj₂ (Γ₀ , refl , refl) with cases++ (Γ ++ Γ₀) Γ Δ' (Γ₀ ++ A ∷ Δ') refl
  ccut≈2 ._ {Δ'} refl ⊗r⊗l | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , p , q) = ⊥-elim (canc⊥3 [] Δ' (Γ₀' ++ Γ₀) q)
  ccut≈2 ._ {Δ'}{A} refl ⊗r⊗l | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , p , q) with canc++ Γ₀ Γ₀' {A ∷ Δ'} p
  ccut≈2 ._ refl ⊗r⊗l | inj₂ (Γ₀ , refl , refl) | inj₂ (.Γ₀ , refl , refl) | refl = ⊗r⊗l


-- completeness

cmplt : {A B : Tm} → A ⇒ B → just A ∣ [] ⊢ B
cmplt id = ax
cmplt (f ∘ g) = scut (cmplt g) (cmplt f)
cmplt (f ⊗ g) = ⊗l (⊗r (cmplt f) (uf (cmplt g)))
cmplt l = ⊗l (Il (uf ax))
cmplt ρ = ⊗r ax Ir
cmplt α = ⊗l (⊗l (⊗r ax (uf (⊗r ax (uf ax)))))

≐cmplt≈ : {A B : Tm}{f g : A ⇒ B} → f ≐ g → cmplt f ≈ cmplt g
≐cmplt≈ refl≐ = refl≈
≐cmplt≈ (sym≐ p) = sym≈ (≐cmplt≈ p)
≐cmplt≈ (trans≐ p p₁) = trans≈ (≐cmplt≈ p) (≐cmplt≈ p₁)
≐cmplt≈ (_∘≐_ {f = f}{g}{h}{k} p p') =
  proof≈
  scut (cmplt h) (cmplt f)
  ≈〈 scut≈2 (cmplt h) (≐cmplt≈ p) 〉 
  scut (cmplt h) (cmplt g)
  ≈〈 scut≈ (≐cmplt≈ p') 〉 
  scut (cmplt k) (cmplt g)
  qed≈
≐cmplt≈ (p ⊗≐ p₁) = cong⊗l (cong⊗r (≐cmplt≈ p) (conguf (≐cmplt≈ p₁)))
≐cmplt≈ {g = g} lid = ≡-to-≈ (scut-unit (cmplt g))
≐cmplt≈ rid = refl≈
≐cmplt≈ (ass {f = f}{g}{h}) = ≡-to-≈ (scutscut-vass (cmplt h) (cmplt g) (cmplt f))
≐cmplt≈ f⊗id = sym≈ ax⊗
≐cmplt≈ (f⊗∘ {f = f}{g}{h}{k}) = cong⊗l (ccut≈2 [] refl (sym≈ (scut⊗r (cmplt f) (cmplt h) (uf (cmplt k)))))
≐cmplt≈ (nl {f = f}) = cong⊗l (congIl (conguf (≡-to-≈ (scut-unit (cmplt f)))))
≐cmplt≈ (nρ {f = f}) =
  proof≈
  scut (cmplt f) (⊗r ax Ir)
  ≈〈 scut⊗r (cmplt f) ax Ir 〉 
  ⊗r (scut (cmplt f) ax) Ir
  ≈〈 cong⊗r (≡-to-≈ (scut-unit (cmplt f))) refl≈ 〉 
  ⊗r (cmplt f) Ir
  qed≈
≐cmplt≈ (nα {B = B}{f = f}{g}{h}) = cong⊗l (cong⊗l
  (proof≈
   ccut (B ∷ []) (uf (cmplt h)) (ccut [] (uf (cmplt g)) (scut (cmplt f) (⊗r ax (uf (⊗r ax (uf ax))))) refl) refl
   ≈〈 ccut≈2 (B ∷ []) refl (ccut≈2 [] refl (scut⊗r (cmplt f) ax (uf (⊗r ax (uf ax))))) 〉
   ⊗r (scut (cmplt f) ax) (uf (ccut [] (uf (cmplt h)) (scut (cmplt g) (⊗r ax (uf ax))) refl))
   ≈〈 cong⊗r refl≈ (conguf (ccut≈2 [] refl (scut⊗r (cmplt g) ax (uf ax)))) 〉
   ⊗r (scut (cmplt f) ax) (uf (⊗r (scut (cmplt g) ax) (uf (scut (cmplt h) ax))))
   ≈〈 cong⊗r (≡-to-≈ (scut-unit (cmplt f))) (conguf (cong⊗r (≡-to-≈ (scut-unit (cmplt g))) (conguf (≡-to-≈ (scut-unit (cmplt h)))))) 〉
   ⊗r (cmplt f) (uf (⊗r (cmplt g) (uf (cmplt h))))
   qed≈))
≐cmplt≈ lρ = sym≈ axI
≐cmplt≈ lαρ = ax⊗
≐cmplt≈ lα = cong⊗l
  (proof≈
   ⊗l (Il (uf (⊗r ax (uf ax))))
   ≈〈 cong⊗l (congIl (sym≈ ⊗ruf)) 〉
   ⊗l (Il (⊗r (uf ax) (uf ax)))
   ≈〈 cong⊗l (sym≈ ⊗rIl) 〉
   ⊗l (⊗r (Il (uf ax)) (uf ax))
   ≈〈 sym≈ ⊗r⊗l 〉
   ⊗r (⊗l (Il (uf ax))) (uf ax)
   qed≈)
≐cmplt≈ αρ = refl≈
≐cmplt≈ ααα = refl≈
