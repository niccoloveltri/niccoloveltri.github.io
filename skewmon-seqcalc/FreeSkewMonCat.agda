-- Skew monoidal categories in sequent calculus form

-- ongoing development, May 2017

module FreeSkewMonCat where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning
--open import Utilities

-- generating objects Var

postulate Var : Set

-- =======================================================================

-- skew-monoidal category Tm (the free skew-monoidal category)

-- -- objects Tm ("terms", "object expressions")

infixl 25 _⊗_

data Tm : Set where
  ` : Var → Tm
  I : Tm
  _⊗_ : Tm → Tm → Tm

-- -- maps (A ⇒ B) ("rewrites", "map expressions") 
-- --         quotiented by ≐ ("provable equality")

-- -- NB! "Skew" means that l, ρ, α are not asked to have inverses!

infix 15 _⇒_
infixl 20 _∘_

data _⇒_ : Tm → Tm → Set where
  id : {A : Tm} → A ⇒ A
  _∘_ : {A B C : Tm} → B ⇒ C → A ⇒ B → A ⇒ C
  _⊗_ : {A B C D : Tm} → A ⇒ B → C ⇒ D → A ⊗ C ⇒ B ⊗ D 
  l : {A : Tm} → I ⊗ A ⇒ A
  ρ : {A : Tm} → A ⇒ A ⊗ I
  α : {A B C : Tm} → (A ⊗ B) ⊗ C ⇒ A ⊗ (B ⊗ C)

-- -- equality of maps (equivalence of rewrites)

infix 15 _≐_
infixl 20 _∘≐_
infixl 25 _⊗≐_

data _≐_ : {A B : Tm} → A ⇒ B → A ⇒ B → Set where
  -- ≐ equivalence and congruence
  refl≐ : {A B : Tm} {f : A ⇒ B} → f ≐ f
  sym≐ : {A B : Tm} {f g : A ⇒ B} → f ≐ g → g ≐ f
  trans≐ : {A B : Tm} {f g h : A ⇒ B} → f ≐ g → g ≐ h → f ≐ h
  _∘≐_ : {A B C : Tm} {f g : B ⇒ C} {h k : A ⇒ B} →
                         f ≐ g → h ≐ k → f ∘ h ≐ g ∘ k
  _⊗≐_ : {A B C D : Tm} {f g : A ⇒ C} {h k : B ⇒ D} →
                         f ≐ g → h ≐ k → f ⊗ h ≐ g ⊗ k
  -- id, ∘ category
  lid : {A B : Tm} {f : A ⇒ B} → id ∘ f ≐ f
  rid : {A B : Tm} {f : A ⇒ B} → f ≐ f ∘ id
  ass : {A B C D : Tm} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
       → f ∘ g ∘ h ≐ f ∘ (g ∘ h)
  -- ⊗ functorial
  f⊗id : {A B : Tm} → id {A} ⊗ id {B} ≐ id
  f⊗∘ : {A B C D E F : Tm} {f : A ⇒ C} {g : B ⇒ D} {h : C ⇒ E} {k : D ⇒ F} →  
                    (h ∘ f) ⊗ (k ∘ g) ≐ h ⊗ k ∘ f ⊗ g
  -- l, ρ, α natural
  nl : {A B : Tm} {f : A ⇒ B} → l ∘ id ⊗ f ≐ f ∘ l
  nρ : {A B : Tm} {f : A ⇒ B} → ρ ∘ f ≐ f ⊗ id ∘ ρ 
  nα : {A B C D E F : Tm} {f : A ⇒ D} {g : B ⇒ E} {h : C ⇒ F} → 
                       α ∘ f ⊗ g ⊗ h ≐ f ⊗ (g ⊗ h) ∘ α 
  -- skew monoidality
  lρ : l ∘ ρ ≐ id 
  lαρ : {A B : Tm} → id ≐ id {A} ⊗ l ∘ α ∘ ρ ⊗ id {B}
  lα :  {A B : Tm} → l ∘ α ≐ l {A} ⊗ id {B}
  αρ : {A B : Tm} → α ∘ ρ ≐ id {A} ⊗ ρ {B}
  ααα : {A B C D : Tm} → 
         α ∘ α ≐ id {A} ⊗ α {B}{C}{D} ∘ (α ∘ α ⊗ id)

refl≐' : {A B : Tm}{f g : A ⇒ B} → f ≡ g → f ≐ g
refl≐' refl = refl≐

-- equational reasoning sugar for ≐

infix 4 _≐'_
infix 1 proof_
infixr 2 _≐〈_〉_
infix 3 _qed

data _≐'_ {A B : Tm} (f g : A ⇒ B) : Set where
  relto :  f ≐ g → f ≐' g

proof_ : {A B : Tm} {f g : A ⇒ B} → f ≐' g → f ≐ g
proof relto p = p

_≐〈_〉_ :  {A B : Tm} (f : A ⇒ B) {g h : A ⇒ B} → f ≐ g → g ≐' h → f ≐' h 
_ ≐〈 p 〉 relto q = relto (trans≐ p q)

_qed  :  {A B : Tm} (f : A ⇒ B) → f ≐' f
_qed _ = relto refl≐

{-
-- =======================================================================

-- Sequent calculus

-- Some lemmata about lists for reasoning about contexts

++ru : {X : Set} → (xs : List X) → xs ≡ xs ++ [] 
++ru [] = refl
++ru (x ∷ xs) = cong (_∷_ x) (++ru xs) 

++ass : {X : Set} → (xs : List X) → {ys zs : List X} → 
           (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++ass [] = refl
++ass (x ∷ xs) = cong (_∷_ x) (++ass xs)

inj∷ : {X : Set} → {x y : X} → {xs ys : List X} → 
           x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
inj∷ refl = refl , refl

lemma[] : {X : Set} → (xs : List X) → {ys : List X} → {x : X} →  
             [] ≡ xs ++ x ∷ ys → ⊥
lemma[] [] ()
lemma[] (x ∷ xs) ()

{-
lemma∷ : {X : Set} → (xs : List X) → {ys ys' : List X} → {x x' : X} → 
   x' ∷ ys' ≡ xs ++ x ∷ ys → 
        (x ≡ x' × xs ≡ [] × ys ≡ ys')  
        ⊎ Σ (List X) 
               (λ xs₀  → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ x' ∷ xs₀) 
lemma∷ [] refl = inj₁ (refl , refl , refl)
lemma∷ (x₀ ∷ xs) {ys} {ys'} {x} {x'} p with inj∷ p 
lemma∷ (x₀ ∷ xs) {ys} {[]} {x} {x'} p | _ , r = ⊥-elim (lemma[] xs r) 
lemma∷ (.x' ∷ xs) {ys} {y₀ ∷ ys'} {x} {x'} p | refl , r = inj₂ (xs , r , refl)
-}

lemma∷ : {X : Set} → (xs : List X) → {ys ys' : List X} → {x x' : X} → 
   x' ∷ ys' ≡ xs ++ x ∷ ys → 
        (x ≡ x' × xs ≡ [] × ys ≡ ys')  
        ⊎ Σ (List X) 
               (λ xs₀  → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ x' ∷ xs₀) 
lemma∷ [] refl = inj₁ (refl , refl , refl)
lemma∷ (x₀ ∷ xs) {ys} {.(xs ++ x ∷ ys)} {x} {.x₀} refl = inj₂ (xs , refl , refl)

lemma++ : {X : Set} → (xs xs' : List X) → {ys ys' : List X} → {x : X} → 
   xs' ++ ys' ≡ xs ++ x ∷ ys → 
       Σ (List X) (λ xs₀ → xs' ≡ xs ++ x ∷ xs₀ × ys ≡ xs₀ ++ ys')  
     ⊎ Σ (List X) (λ xs₀ → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ xs' ++ xs₀) 
lemma++ xs [] refl = inj₂ (xs , refl , refl)
lemma++ [] (x' ∷ xs') refl = inj₁ (xs' , refl , refl)
lemma++ (x₀ ∷ xs) (x' ∷ xs') {ys} {ys'} {x} p with inj∷ p
lemma++ (.x' ∷ xs) (x' ∷ xs') {ys} {ys'} {x} p | refl , q with lemma++ xs xs' {ys} {ys'} {x} q 
lemma++ (.x' ∷ xs) (x' ∷ xs') p | refl , q | inj₁ (xs₀ , r , r') = inj₁ (xs₀ , cong₂ _∷_ refl r , r')
lemma++ (.x' ∷ xs) (x' ∷ xs') p | refl , q | inj₂ (xs₀ , r , r') = inj₂ (xs₀ , r , cong₂ _∷_ refl r')

{-
-- -- (In addition to the conclusion, sequents have a stoup and a context.)

infix 15 _∣_⊢_

data _∣_⊢_ : Maybe Tm → List Tm → Tm → Set where
  ax : {X : Var} → just (` X) ∣ [] ⊢ ` X
  uf : {Γ : List Tm} → {A C : Tm} → 
              just A ∣ Γ ⊢ C → nothing ∣ A ∷ Γ ⊢ C 
  Ir : nothing ∣ [] ⊢ I
  ⊗r : {S : Maybe Tm} → {Γ Δ : List Tm} → {A B : Tm} → 
              S ∣ Γ ⊢ A → nothing ∣ Δ ⊢ B → S ∣ Γ ++ Δ ⊢ A ⊗ B 
  Il : {Γ : List Tm} → {C : Tm} → 
              nothing ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊗l : {Γ : List Tm} → {A B C : Tm} → 
              just A ∣ B ∷ Γ ⊢ C → just (A ⊗ B) ∣ Γ ⊢ C

subeq : {S : Maybe Tm} → {Γ Γ' : List Tm} → {A : Tm} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subeq refl f = f

subeq' : {S S' : Maybe Tm} → {Γ : List Tm} → {A : Tm} → 
      S ≡ S' → S ∣ Γ ⊢ A → S' ∣ Γ ⊢ A 
subeq' refl f = f


-- admissibility of identity

deduct : (A : Tm){C : Tm}{Δ : List Tm}
  → ((S : Maybe Tm)(Γ : List Tm) → S ∣ Γ  ⊢ A → S ∣ Γ ++ Δ ⊢ C)
  → just A ∣ Δ ⊢ C
deduct (` X) p = p (just (` X)) [] ax
deduct I p = Il (p nothing [] Ir)
deduct (A₁ ⊗ A₂) p =
  ⊗l (deduct A₁ (λ S Γ d → subeq (++ass Γ) (p S (Γ ++ A₂ ∷ []) (⊗r d (uf (deduct A₂ (λ _ Γ' → subeq (++ru Γ'))))))))

axf : {A : Tm} → just A ∣ [] ⊢ A 
axf {A} = deduct A (λ _ Γ → subeq (++ru Γ))

-- admissibility of cut

-- -- (There are two kinds of cut: stoup ccut and context cut.)

mutual 
  scut : {S : Maybe Tm} → {Γ Δ' : List Tm} → {A C : Tm} → 
              S ∣ Γ ⊢ A  →  just A ∣ Δ' ⊢ C  →  S ∣ Γ ++ Δ' ⊢ C

  scut ax g = g
  scut (uf f) g = uf (scut f g)
  scut Ir (⊗r g g') = ⊗r (scut Ir g) g'
  scut Ir (Il g) = g
  scut (⊗r {S} {Γ} {Δ} f f') (⊗r g g') = 
          subeq (++ass (Γ ++ Δ)) (⊗r (scut (⊗r f f') g) g')
  scut (⊗r {S} {Γ} {Δ} f f') (⊗l g) = 
          ccut Γ f' (scut f g) refl 
  scut (Il f) g = Il (scut f g)
  scut (⊗l f) g = ⊗l (scut f g)


  ccut : {T : Maybe Tm} → {Γ Δ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} → {A C : Tm} → 
             nothing ∣ Γ ⊢ A  →  T ∣ Δ ⊢ C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        T ∣ (Δ₀ ++ Γ) ++ Δ' ⊢ C
  
  ccut Δ₀ f ax p = ⊥-elim (lemma[] Δ₀ p)
  ccut Δ₀ f (uf g) p with lemma∷ Δ₀ p 
  ccut .[] f (uf g) p 
     | inj₁ (refl , refl , refl) = scut f g
  ccut .(_ ∷ Δ₀) f (uf g) p 
     | inj₂ (Δ₀ , refl , refl) =  uf (ccut Δ₀ f g refl)
  ccut Δ₀ f Ir p = ⊥-elim (lemma[] Δ₀ p)
  ccut Δ₀ f (⊗r {T} {Γ} {Γ'} g g') p with lemma++ Δ₀ Γ p 
  ccut Δ₀ f (⊗r {T} {.(Δ₀ ++ _)} {Γ'} g g') p 
     | inj₁ (Γ₀  , refl , refl) =  
                subeq (++ass (Δ₀ ++ _)) 
                      (⊗r (ccut Δ₀ f g refl) g')
  ccut .(Γ ++ Γ₀) f (⊗r {T} {Γ} g g') p 
     | inj₂ (Γ₀ , refl , refl) =  
                subeq (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))
                      (⊗r g (ccut Γ₀ f g' refl))
  ccut Δ₀ f (Il g) refl = Il (ccut Δ₀ f g refl) 
  ccut Δ₀ f (⊗l {B = B} g) refl = ⊗l (ccut (B ∷ Δ₀) f g refl) 

-- =======================================================================

-- soundness

-- interpretation of antecedents

-- -- (Note that an empty stoup contributes an I to the meaning 
-- -- of an antecedent.)

t : Maybe Tm → Tm
t nothing = I
t (just A) = A

[_∣_] : Tm → List Tm → Tm
[ A ∣ [] ] = A
[ A ∣ C ∷ Γ ] = [ A ⊗ C ∣ Γ ]

〈_∣_〉 : Maybe Tm → List Tm → Tm 
〈 S ∣ Γ 〉 = [ t S ∣ Γ ] 

[_∣_]f : {A B : Tm} → A ⇒ B → (Γ : List Tm) → [ A ∣ Γ ] ⇒ [ B ∣ Γ ]
[ f ∣ [] ]f = f
[ f ∣ C ∷ Γ ]f = [ f ⊗ id ∣ Γ ]f

lemma'' : (A B : Tm) → (Δ : List Tm) → 
                   [ A ⊗ B ∣  Δ ] ⇒ A ⊗ [ B ∣ Δ ] 
lemma'' A B [] = id
lemma'' A B (C ∷ Δ) = lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f 

lemma' : (A : Tm) → (Γ Δ : List Tm) →
                   [ A ∣ Γ ++ Δ ] ⇒ [ A ∣ Γ ] ⊗ 〈 nothing ∣ Δ 〉
lemma' A [] Δ = lemma'' A I Δ ∘ [ ρ ∣ Δ ]f 
lemma' A (C ∷ Γ) Δ  = lemma' (A ⊗ C) Γ Δ 

lemma : (S : Maybe Tm) → (Γ Δ : List Tm) →  
                   〈 S ∣ Γ ++ Δ 〉 ⇒ 〈 S ∣ Γ 〉 ⊗ 〈 nothing ∣ Δ 〉
lemma S Γ Δ = lemma' (t S) Γ Δ 


sound : {S : Maybe Tm} → {Γ : List Tm} → {A : Tm} → S ∣ Γ ⊢ A → 〈 S ∣ Γ 〉 ⇒ A 
sound ax = id
sound (uf {Γ} f) = sound f ∘ [ l ∣ Γ ]f 
sound Ir = id
sound (⊗r {S} {Γ} {Δ} f g) = sound f ⊗ sound g ∘ lemma S Γ Δ
sound (Il f) = sound f
sound (⊗l f) = sound f 

-- =======================================================================

-- completeness

cmplt : {A B : Tm} → A ⇒ B → just A ∣ [] ⊢ B
cmplt id = axf
cmplt (f ∘ g) = scut (cmplt g) (cmplt f)
cmplt (f ⊗ g) = ⊗l {!!} --⊗l (⊗r (cmplt f) (uf (cmplt g)))
cmplt l = ⊗l (Il (uf axf))
cmplt ρ = ⊗r axf Ir
cmplt α = ⊗l (⊗l (⊗r axf (uf (⊗r axf (uf axf)))))

cmplt≐ : {A B : Tm}{f g : A ⇒ B} → f ≐ g → cmplt f ≡ cmplt g
cmplt≐ refl≐ = refl
cmplt≐ (sym≐ p) = sym (cmplt≐ p)
cmplt≐ (trans≐ p p₁) = trans (cmplt≐ p) (cmplt≐ p₁)
cmplt≐ (p ∘≐ p₁) = cong₂ scut (cmplt≐ p₁) (cmplt≐ p)
cmplt≐ (p ⊗≐ p₁) = cong₂ (λ a b → ⊗l (⊗r a (uf b))) (cmplt≐ p) (cmplt≐ p₁)
cmplt≐ lid = {!!}
cmplt≐ rid = {!!}
cmplt≐ ass = {!!}
cmplt≐ f⊗id = {!!}
cmplt≐ f⊗∘ = {!!}
cmplt≐ nl = {!!}
cmplt≐ nρ = {!!}
cmplt≐ nα = {!!}
cmplt≐ lρ = refl
cmplt≐ lαρ = {!!}
cmplt≐ lα = {!lα!}
cmplt≐ αρ = {!!}
cmplt≐ ααα = {!!}

-- dammit...

cmplt≐⊥ : ({A B : Tm}{f g : A ⇒ B} → f ≐ g → cmplt f ≡ cmplt g) → ⊥
cmplt≐⊥ p with p (lα {I}{I})
cmplt≐⊥ p | ()
-}


-- -- (In addition to the conclusion, sequents have a stoup and a context.)

infix 15 _∣_⊢_

data _∣_⊢_ : Maybe Tm → List Tm → Tm → Set where
  ax : {Λ : List Tm}{A : Tm} → (p : [] ≡ Λ) → just A ∣ Λ ⊢ A
  uf : {Γ Λ : List Tm} → {A C : Tm} → 
              just A ∣ Γ ⊢ C → (p : A ∷ Γ ≡ Λ) → nothing ∣ Λ ⊢ C 
  Ir : {Λ : List Tm} → (p : [] ≡ Λ) → nothing ∣ Λ ⊢ I
  ⊗r : {S : Maybe Tm} → {Γ Δ Λ : List Tm} → {A B : Tm} → 
              S ∣ Γ ⊢ A → nothing ∣ Δ ⊢ B → (p : Γ ++ Δ ≡ Λ) → S ∣ Λ ⊢ A ⊗ B 
  Il : {Γ : List Tm} → {C : Tm} → 
              nothing ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊗l : {Γ : List Tm} → {A B C : Tm} → 
              just A ∣ B ∷ Γ ⊢ C → just (A ⊗ B) ∣ Γ ⊢ C

{-
-- equality for derivations

data _≈_ : {S  : Maybe Tm}{Γ : List Tm}{A : Tm} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl≈ : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢ A} → f ≈ f
  sym≈ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢ A} → f ≈ g → g ≈ f
  trans≈ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢ A} → f ≈ g → g ≈ h → f ≈ h
  conguf : ∀{Γ}{A}{C}{f g : just A ∣ Γ ⊢ C} → f ≈ g → uf f ≈ uf g
  cong⊗l : ∀{Γ}{A}{B}{C}{f g : just A ∣ B ∷ Γ ⊢ C} → f ≈ g → ⊗l f ≈ ⊗l g
  congIl : ∀{Γ}{C}{f g : nothing ∣ Γ ⊢ C} → f ≈ g → Il f ≈ Il g
  cong⊗r : ∀{S}{Γ}{Δ}{A}{B}{f g : S ∣ Γ ⊢ A}{f' g' : nothing ∣ Δ ⊢ B}
    → f ≈ g → f' ≈ g' → ⊗r f f' ≈ ⊗r g g'  
  axI : ax {I} ≈ Il Ir
  ax⊗ : {A B : Tm} → ax {A ⊗ B} ≈ ⊗l (⊗r ax (uf ax))
  ⊗ruf : {Γ Δ : List Tm}{A A' B : Tm}
    → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (uf f) g ≈ uf (⊗r f g)
  ⊗rIl : {Γ Δ : List Tm}{A B : Tm}
    → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (Il f) g ≈ Il (⊗r f g)
  ⊗r⊗l : {Γ Δ : List Tm}{A A' B B' : Tm}
    → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (⊗l f) g ≈ ⊗l (⊗r f g)

refl≈' : ∀{S}{Γ}{A}{f f' : S ∣ Γ ⊢ A} → f ≡ f' → f ≈ f'
refl≈' refl = refl≈
-}

-- inverted rules

Il-1 : {Γ : List Tm} → {C : Tm} → 
              just I ∣ Γ ⊢ C → nothing ∣ Γ ⊢ C
Il-1 (ax r) = Ir r
Il-1 (⊗r p p₁ r) = ⊗r (Il-1 p) p₁ r
Il-1 (Il p) = p

{-
Il-iso : {Γ : List Tm} → {C : Tm} → 
              (f : just I ∣ Γ ⊢ C) → Il (Il-1 f) ≈ f
Il-iso ax = sym≈ axI
Il-iso (⊗r f f₁) = trans≈ (sym≈ ⊗rIl) (cong⊗r (Il-iso f) refl≈)
Il-iso (Il f) = refl≈              
-}

⊗l-1 : {Γ : List Tm} → {A B C : Tm} → 
            just (A ⊗ B) ∣ Γ ⊢ C → just A ∣ B ∷ Γ ⊢ C
⊗l-1 (ax refl) = ⊗r (ax refl) (uf (ax refl) refl) refl
⊗l-1 (⊗r f f₁ r) = ⊗r (⊗l-1 f) f₁ (cong (_∷_ _) r)
⊗l-1 (⊗l f) = f

{-
⊗l-iso : {Γ : List Tm} → {A B C : Tm} → 
            (f : just (A ⊗ B) ∣ Γ ⊢ C) → ⊗l (⊗l-1 f) ≈ f
⊗l-iso ax = sym≈ ax⊗
⊗l-iso (⊗r f f₁) = trans≈ (sym≈ ⊗r⊗l) (cong⊗r (⊗l-iso f) refl≈)
⊗l-iso (⊗l f) = refl≈            
-}


{-
-- focused ax and ⊗r

mutual 
  axf : {A : Tm} → just A ∣ [] ⊢ A
  axf {` X} = ax
  axf {I} = Il Ir
  axf {A ⊗ B} = ⊗l (⊗rf axf (uf axf))

  ⊗rf : {S : Maybe Tm} → {Γ Δ : List Tm} → {A B : Tm} → 
                   S ∣ Γ ⊢ A → nothing ∣ Δ ⊢ B → S ∣ Γ ++ Δ ⊢ A ⊗ B
  ⊗rf ax g = ⊗r axf g
  ⊗rf (uf f) g = uf (⊗rf f g)
  ⊗rf Ir g = ⊗r Ir g
  ⊗rf (⊗r f f₁) g = ⊗r (⊗rf f f₁) g
  ⊗rf (Il f) g = Il (⊗rf f g)
  ⊗rf (⊗l f) g = ⊗l (⊗rf f g)            
-}

-- admissibility of cut

subeq : {S : Maybe Tm} → {Γ Γ' : List Tm} → {A : Tm} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subeq refl f = f

{-
assoc[_] : (Δ₀ : List Tm){S : Maybe Tm}{Δ₁ Δ₂ : List Tm} → {A : Tm}
  → S ∣ (Δ₀ ++ Δ₁) ++ Δ₂ ⊢ A → S ∣ Δ₀ ++ (Δ₁ ++ Δ₂) ⊢ A
assoc[ Δ₀ ] = subeq (++ass Δ₀)

assoc-1[_] : (Δ₀ : List Tm){S : Maybe Tm}{Δ₁ Δ₂ : List Tm} → {A : Tm}
  → S ∣ Δ₀ ++ (Δ₁ ++ Δ₂) ⊢ A → S ∣ (Δ₀ ++ Δ₁) ++ Δ₂ ⊢ A
assoc-1[ Δ₀ ] = subeq (sym (++ass Δ₀))

assoc[_]++_ : (Δ₀ : List Tm){S : Maybe Tm}(Γ : List Tm){Δ₁ Δ₂ : List Tm} → {A : Tm}
  → S ∣ ((Δ₀ ++ Δ₁) ++ Δ₂) ++ Γ ⊢ A → S ∣ (Δ₀ ++ (Δ₁ ++ Δ₂)) ++ Γ ⊢ A
assoc[ Δ₀ ]++ Γ = subeq (cong (λ a → a ++ Γ) (++ass Δ₀))

assoc-1[_]++_ : (Δ₀ : List Tm){S : Maybe Tm}(Γ : List Tm){Δ₁ Δ₂ : List Tm} → {A : Tm}
  → S ∣ (Δ₀ ++ Δ₁ ++ Δ₂) ++ Γ ⊢ A → S ∣ ((Δ₀ ++ Δ₁) ++ Δ₂) ++ Γ ⊢ A
assoc-1[ Δ₀ ]++ Γ = subeq (cong (λ a → a ++ Γ) (sym (++ass Δ₀)))

_++assoc[_] : (Γ : List Tm){S : Maybe Tm}(Δ₀ : List Tm){Δ₁ Δ₂ : List Tm} → {A : Tm}
  → S ∣ Γ ++ (Δ₀ ++ Δ₁) ++ Δ₂ ⊢ A → S ∣ Γ ++ Δ₀ ++ Δ₁ ++ Δ₂ ⊢ A
Γ ++assoc[ Δ₀ ] = subeq (cong (_++_ Γ) (++ass Δ₀))

_++assoc-1[_] : (Γ : List Tm){S : Maybe Tm}(Δ₀ : List Tm){Δ₁ Δ₂ : List Tm} → {A : Tm}
  → S ∣ Γ ++ Δ₀ ++ Δ₁ ++ Δ₂ ⊢ A → S ∣ Γ ++ (Δ₀ ++ Δ₁) ++ Δ₂ ⊢ A
Γ ++assoc-1[ Δ₀ ] = subeq (cong (_++_ Γ) (sym (++ass Δ₀)))
-}

subeq' : {S S' : Maybe Tm} → {Γ : List Tm} → {A : Tm} → 
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

{-
subeq⊗r : ∀{S}{Γ}{Γ'}{Δ}{A}{B} → {f : S ∣ Γ ⊢ A} {g : nothing ∣ Δ ⊢ B}
  → (p : Γ ≡ Γ') → subeq (cong (λ a → a ++ Δ) p) (⊗r f g) ≡ ⊗r (subeq p f) g
subeq⊗r refl = refl

subeq⊗r2 : ∀{S}{Γ}{Δ}{Δ'}{A}{B} → {f : S ∣ Γ ⊢ A} {g : nothing ∣ Δ ⊢ B}
  → (p : Δ ≡ Δ') → subeq (cong (_++_ Γ) p) (⊗r f g) ≡ ⊗r f (subeq p g)
subeq⊗r2 refl = refl
-}
-- -- (There are two kinds of cut: stoup ccut and context cut.)


lemma++'' : {A : Set}{x : A}(xs ys : List A)
  → ys ≡ x ∷ xs ++ ys → ⊥
lemma++'' _ [] ()
lemma++'' [] (y ∷ ys) ()
lemma++'' (x ∷ xs) (y ∷ ys) p with inj∷ p
... | (refl , q) = lemma++'' (xs ++ y ∷ []) ys (trans q (sym (++ass (x ∷ xs))))

lemma++''₂ : {A : Set}{x : A}(xs : List A){ys : List A}
  → xs ≡ xs ++ x ∷ ys → ⊥
lemma++''₂ [] ()
lemma++''₂ (x ∷ xs) p = lemma++''₂ xs (proj₂ (inj∷ p))

lemma++' : {A : Set}(xs xs' : List A){ys : List A} → xs ++ ys ≡ xs' ++ ys → xs ≡ xs'
lemma++' [] [] p = refl
lemma++' [] (x ∷ xs') {ys} p = ⊥-elim (lemma++'' xs' ys p)
lemma++' (x ∷ xs) [] {ys} p = ⊥-elim (lemma++'' xs ys (sym p))
lemma++' (x ∷ xs) (x₁ ∷ xs') p with inj∷ p
lemma++' (x ∷ xs) (.x ∷ xs') p | refl , q = cong (_∷_ x) (lemma++' xs xs' q)

lemma++'₂ : {A : Set}{xs xs' : List A}(ys : List A) → ys ++ xs ≡ ys ++ xs' → xs ≡ xs'
lemma++'₂ [] p = p
lemma++'₂ (x ∷ ys) p = lemma++'₂ ys (proj₂ (inj∷ p))

lemma++''' : {A : Set}{x : A}(xs ys zs : List A)
  → ys ≡ zs ++ x ∷ xs ++ ys → ⊥
lemma++''' xs ys [] p = lemma++'' xs ys p
lemma++''' {_} {x} xs ys (z ∷ zs) p = lemma++'' (zs ++ x ∷ xs) ys (trans p (cong (_∷_ z) (sym (++ass zs))))

lemma++'''₂ : {A : Set}{x : A}(xs : List A){ys zs : List A}
  → xs ≡ (xs ++ zs) ++ x ∷ ys → ⊥
lemma++'''₂ [] {_}{zs} p = lemma[] zs p
lemma++'''₂ (x ∷ xs) p = lemma++'''₂ xs (proj₂ (inj∷ p))

mutual 
  scut : {S : Maybe Tm} → {Γ Δ' : List Tm} → {A C : Tm} → 
              S ∣ Γ ⊢ A  →  just A ∣ Δ' ⊢ C  →  S ∣ Γ ++ Δ' ⊢ C

  scut (ax refl) g = g
  scut (uf f refl) g = uf (scut f g) refl
  scut (Ir refl) g = Il-1 g
  scut (⊗r {Γ = Γ} f f' refl) g = ccut Γ f' (scut f (⊗l-1 g)) refl
  scut (Il f) g = Il (scut f g)
  scut (⊗l f) g = ⊗l (scut f g)


  ccut : {T : Maybe Tm} → {Γ Δ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} → {A C : Tm} → 
             nothing ∣ Γ ⊢ A  →  T ∣ Δ ⊢ C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        T ∣ (Δ₀ ++ Γ) ++ Δ' ⊢ C
  
  ccut Δ₀ f (ax refl) p = ⊥-elim (lemma[] Δ₀ p)
  ccut Δ₀ f (uf g refl) p with lemma∷ Δ₀ p 
  ccut .[] f (uf g refl) p 
     | inj₁ (refl , refl , refl) = scut f g
  ccut .(_ ∷ Δ₀) f (uf g refl) p 
     | inj₂ (Δ₀ , r , refl) =  uf (ccut Δ₀ f g r) refl
  ccut Δ₀ f (Ir refl) p = ⊥-elim (lemma[] Δ₀ p)
  ccut Δ₀ f (⊗r {S} {Γ} {Δ} g g' q) p with lemma++ Δ₀ Γ (trans q p)
  ccut {_}{Γ}Δ₀ {Δ'} f (⊗r {T} {_} {Γ'} g g' q) p 
     | inj₁ (Γ₀  , r , s) = ⊗r (ccut Δ₀ f g r) g' (trans (++ass (Δ₀ ++ _)) (cong (_++_ (Δ₀ ++ _)) (sym s)))
--     where
--       e : ((Δ₀ ++ Γ) ++ Γ₀) ++ Γ' ≡ (Δ₀ ++ Γ) ++ Δ'
--       e = trans (++ass (Δ₀ ++ _)) (cong (_++_ (Δ₀ ++ _)) (sym s))
  ccut {_}{Γ'} Δ₀ {Δ'} f (⊗r {T} {Γ} g g' q) p 
     | inj₂ (Γ₀ , r , s) = ⊗r g (ccut Γ₀ f g' r) (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong (λ a → (a ++ Γ') ++ Δ') (sym s)))
--     where
--       e : Γ ++ (Γ₀ ++ Γ') ++ Δ' ≡ (Δ₀ ++ Γ') ++ Δ'
--       e = trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong (λ a → (a ++ Γ') ++ Δ') (sym s))
  ccut Δ₀ f (Il g) r = Il (ccut Δ₀ f g r) 
  ccut Δ₀ f (⊗l {B = B} g) r = ⊗l (ccut (B ∷ Δ₀) f g (cong (_∷_ B) r)) 

scutsubeq : {S : Maybe Tm} → {Γ Δ Δ' : List Tm} → {A B : Tm} → 
            (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(p : Δ ≡ Δ') → 
        scut f (subeq p g) ≡ subeq (cong (_++_ Γ) p) (scut f g)
scutsubeq f g refl = refl

scutsubeq2 : {S : Maybe Tm} → {Γ Δ Γ' : List Tm} → {A B : Tm} → 
            (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(p : Γ ≡ Γ') → 
        scut (subeq p f) g ≡ subeq (cong (λ a → a ++ Δ) p) (scut f g)
scutsubeq2 f g refl = refl

ccutsubeq : {T : Maybe Tm} → {Γ Δ Δ₁ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} →  {A C : Tm} → 
             (f : nothing ∣ Γ ⊢ A){g :  T ∣ Δ ⊢ C}(r : Δ₁ ≡ Δ₀ ++ A ∷ Δ')(p : Δ ≡ Δ₁) →
             ccut Δ₀ f (subeq p g) r ≡ ccut Δ₀ f g (trans p r)
ccutsubeq Δ₀ f r refl = refl             

ccutsubeq2 : {T : Maybe Tm} → {Γ Δ Δ₁ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} →  {A C : Tm} → 
             (f : nothing ∣ Γ ⊢ A){g :  T ∣ Δ₁ ⊢ C}(r : Δ₁ ≡ Δ₀ ++ A ∷ Δ')(p : Δ₁ ≡ Δ) →
             ccut Δ₀ f g r ≡ ccut Δ₀ f (subeq p g) (trans (sym p) r)
ccutsubeq2 Δ₀ f r refl = refl             

{-
mutual
  ccutccut : {T : Maybe Tm} → {Γ₁ Γ₂ : List Tm} → (Δ₀ : List Tm) → {Δ Δ₁ Δ₂ : List Tm} → {A₁ A₂ C : Tm}
    → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
    → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
    → (r' : Δ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Δ₂)
    → (a : ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Δ₂ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ Γ₂ ++ Δ₂)
    → (a' : (Δ₀ ++ Γ₁) ++ Δ₁ ++ A₂ ∷ Δ₂ ≡ ((Δ₀ ++ Γ₁) ++ Δ₁) ++ A₂ ∷ Δ₂)
    → (s : (((Δ₀ ++ Γ₁) ++ Δ₁) ++ Γ₂) ++ Δ₂ ≡ (Δ₀ ++ Γ₁) ++ Δ₁ ++ Γ₂ ++ Δ₂)
    → ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) a ≡
      subeq s (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g r') a')
  ccutccut Δ₀ f₁ f₂ (ax p) q q' a a' t = {!!}
  ccutccut Δ₀ f₁ f₂ (uf g p) q q' a a' t = {!!}
  ccutccut Δ₀ f₁ f₂ (Ir p) q q' a a' t = {!!}
  ccutccut Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ'} g g₁ p) q q' a a' t with lemma++ (Δ₀ ++ A₁ ∷ Δ₁) Γ' (trans p q) | lemma++ Δ₀ Γ' (trans p q')
  ccutccut {_}{Γ₁}{Γ₂} Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ'} g g₁ p) q q' a a' t | inj₁ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s')
    with lemma++ Δ₀ (((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Γ₀) (trans (trans (++ass ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂)) (cong (_++_ ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂)) (sym s))) a)
       | lemma++ ((Δ₀ ++ Γ₁) ++ Δ₁) ((Δ₀ ++ Γ₁) ++ Γ₀') (trans (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s'))) a')
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁ p) q q' a a' t | inj₁ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s') | inj₁ (Γ₀'' , r'' , s'') | inj₁ (Γ₀''' , r''' , s''') =
    begin
    ⊗r (ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) r'') g₁ (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s'')))
    ≡⟨ cong (λ z → ⊗r z g₁ (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s'')))) {!r''!} ⟩
    ⊗r (subeq {!!} (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g r') r''')) g₁ (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s'')))
    ≡⟨ {!!} ⟩
    subeq t (⊗r (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g r') r''') g₁ (trans (++ass (((Δ₀ ++ Γ₁) ++ Δ₁) ++ Γ₂)) (cong (_++_ (((Δ₀ ++ Γ₁) ++ Δ₁) ++ Γ₂)) (sym s'''))))
    ∎
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁ p) q q' a a' t | inj₁ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s') | inj₁ (Γ₀'' , r'' , s'') | inj₂ (Γ₀''' , r''' , s''') = {!!}
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁ p) q q' a a' t | inj₁ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s') | inj₂ (Γ₀'' , r'' , s'') | inj₁ (Γ₀''' , r''' , s''') = {!!}
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁ p) q q' a a' t | inj₁ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s') | inj₂ (Γ₀'' , r'' , s'') | inj₂ (Γ₀''' , r''' , s''') = {!!}
  ccutccut Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ'} g g₁ p) q q' a a' t | inj₁ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') = {!!}
  ccutccut Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ'} g g₁ p) q q' a a' t | inj₂ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s') = {!!}
  ccutccut Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ'} g g₁ p) q q' a a' t | inj₂ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') = {!!}
  ccutccut Δ₀ f₁ f₂ (Il g) q q' a a' t = {!!}
  ccutccut Δ₀ f₁ f₂ (⊗l g) q q' a a' t = {!!}
-}

--ccut⊗r : {T : Maybe Tm}{Γ' Γ Δ : List Tm}(Δ₀ : List Tm){Δ' : List Tm}{A B C : Tm}
--  → (f : nothing ∣ Γ' ⊢ A)(g : T ∣ Γ ⊢ B)(g' : nothing ∣ Δ ⊢ C)
--  → (r : Γ ++ Δ ≡ Δ₀ ++ A ∷ Δ')
--  → Σ (List Tm) (λ Γ₀ → Σ (Γ ≡ Δ₀ ++ A ∷ Γ₀) (λ p → Σ (Δ' ≡ Γ₀ ++ Δ) (λ q → ccut Δ₀ f (⊗r g g') r ≡ subeq (trans (++ass (Δ₀ ++ Γ')) (cong (_++_ (Δ₀ ++ Γ')) (sym q))) (⊗r (ccut Δ₀ f g p) g')))) ⊎
--    {!Σ (List Tm) (λ Γ₀ → Σ (Γ ≡ Δ₀ ++ A ∷ Γ₀) !}
--ccut⊗r = {!!}

ccutufax : {T : Maybe Tm}{Γ Δ : List Tm}(Δ₀ : List Tm){A C : Tm}
  → (g : T ∣ Δ ⊢ C)(r : Δ ≡ Δ₀ ++ A ∷ Γ)
  → ccut Δ₀ (uf (ax refl) refl) g r ≡ subeq (trans r (sym (++ass Δ₀))) g 
ccutufax Δ₀ (ax refl) r = ⊥-elim (lemma[] Δ₀ r)
ccutufax Δ₀ (uf g refl) r with lemma∷ Δ₀ r
ccutufax .[] (uf g refl) refl | inj₁ (refl , refl , refl) = refl
ccutufax .(_ ∷ Δ₀) (uf {A = A} g refl) refl | inj₂ (Δ₀ , refl , refl) =
  begin
  uf (ccut Δ₀ (uf (ax refl) refl) g refl) refl
  ≡⟨ cong₂ uf (ccutufax Δ₀ g refl) refl ⟩
  uf (subeq (sym (++ass Δ₀)) g) refl
  ≡⟨ subequf refl (sym (++ass Δ₀)) ⟩
  uf g (trans (cong (_∷_ A) (sym (++ass Δ₀))) refl)
  ≡⟨ cong (uf g) uip ⟩
  uf g (sym (cong (_∷_ A) (++ass Δ₀)))
  ≡⟨ sym (subequf' refl (sym (cong (_∷_ A) (++ass Δ₀)))) ⟩
  subeq (sym (cong (_∷_ A) (++ass Δ₀))) (uf g refl)
  ∎
ccutufax Δ₀ (Ir refl) r = ⊥-elim (lemma[] Δ₀ r)
ccutufax Δ₀ (⊗r {Γ = Γ'} g g₁ refl) r with lemma++ Δ₀ Γ' r
ccutufax Δ₀ {A} (⊗r {Γ = Γ} g g₁ refl) r | inj₁ (Γ₀ , refl , refl) =
  begin
  ⊗r (ccut Δ₀ (uf (ax refl) refl) g refl) g₁ (trans (++ass (Δ₀ ++ A ∷ [])) refl)
  ≡⟨ cong (λ a → ⊗r a g₁ (trans (++ass (Δ₀ ++ A ∷ [])) refl)) (ccutufax Δ₀ g refl) ⟩
  ⊗r (subeq (sym (++ass Δ₀)) g) g₁ (trans (++ass (Δ₀ ++ A ∷ [])) refl)
  ≡⟨ subeq⊗r (trans (++ass (Δ₀ ++ A ∷ [])) refl) (sym (++ass Δ₀)) ⟩
  ⊗r g g₁ _
  ≡⟨ cong (⊗r g g₁) uip ⟩
  ⊗r g g₁ (trans r (sym (++ass Δ₀)))
  ≡⟨ sym (subeq⊗r' refl (trans r (sym (++ass Δ₀)))) ⟩
  subeq (trans r (sym (++ass Δ₀))) (⊗r g g₁ refl)
  ∎
ccutufax .(Γ ++ Γ₀) (⊗r {Γ = Γ} g g₁ refl) r | inj₂ (Γ₀ , refl , refl) =
  begin
  ⊗r g (ccut Γ₀ (uf (ax refl) refl) g₁ refl) (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) refl)
  ≡⟨ cong (λ a → ⊗r g a (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) refl)) (ccutufax Γ₀ g₁ refl)  ⟩
  ⊗r g (subeq (sym (++ass Γ₀)) g₁) (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) refl)
  ≡⟨ subeq⊗r₂ (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) refl) (sym (++ass Γ₀)) ⟩
  ⊗r g g₁ _
  ≡⟨ cong (⊗r g g₁) uip ⟩
  ⊗r g g₁ _
  ≡⟨ sym (subeq⊗r' refl (trans r (sym (++ass (Γ ++ Γ₀))))) ⟩
  subeq (trans r (sym (++ass (Γ ++ Γ₀)))) (⊗r g g₁ refl)
  ∎     
ccutufax Δ₀ (Il g) refl =
  begin
  Il (ccut Δ₀ (uf (ax refl) refl) g refl)
  ≡⟨ cong Il (ccutufax Δ₀ g refl) ⟩
  Il (subeq (sym (++ass Δ₀)) g)
  ≡⟨ sym (subeqIl (sym (++ass Δ₀))) ⟩
  subeq (sym (++ass Δ₀)) (Il g)
  ∎
ccutufax Δ₀ (⊗l {B = B} g) refl =
  begin
  ⊗l (ccut (B ∷ Δ₀) (uf (ax refl) refl) g refl)
  ≡⟨ cong ⊗l (ccutufax (B ∷ Δ₀) g refl) ⟩
  ⊗l (subeq (sym (++ass (B ∷ Δ₀))) g)
  ≡⟨ cong ⊗l (cong₂ subeq (uip {p = sym (++ass (B ∷ Δ₀))}{cong (_∷_ B) (sym (++ass Δ₀))}) refl) ⟩
  ⊗l (subeq (cong (_∷_ B) (sym (++ass Δ₀))) g)
  ≡⟨ sym (subeq⊗l (sym (++ass Δ₀))) ⟩
  subeq (sym (++ass Δ₀)) (⊗l g)
  ∎

ccutIl-1 : ∀{Γ}{Δ}{A}{C} Δ₀ {Δ'}
  → (f : nothing ∣ Γ ⊢ A)(g : just I ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → Il-1 (ccut Δ₀ f g r) ≡ ccut Δ₀ f (Il-1 g) r
ccutIl-1 Δ₀ f (ax refl) r = ⊥-elim (lemma[] Δ₀ r)
ccutIl-1 Δ₀ f (⊗r {Γ = Γ}{Δ} g g₁ refl) r with lemma++ Δ₀ Γ r
ccutIl-1 {Γ} Δ₀ f (⊗r g g₁ refl) r | inj₁ (Γ₀ , p , q) = cong (λ a → ⊗r a g₁ _) (ccutIl-1 Δ₀ f g p)
ccutIl-1 Δ₀ f (⊗r g g₁ refl) r | inj₂ (Γ₀ , p , q) = refl
ccutIl-1 Δ₀ f (Il g) r = refl

scutIl-1 : {Γ Δ : List Tm} → {A C : Tm}
  → (f : just I ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ C)
  → Il-1 (scut f g) ≡ scut (Il-1 f) g
scutIl-1 (ax refl) g = refl
scutIl-1 (⊗r {Γ = Γ} f f' refl) g =
  begin
  Il-1 (ccut Γ f' (scut f (⊗l-1 g)) refl)
  ≡⟨ ccutIl-1 Γ f' (scut f (⊗l-1 g)) refl ⟩
  ccut Γ f' (Il-1 (scut f (⊗l-1 g))) refl
  ≡⟨ cong (λ a → ccut Γ f' a refl) (scutIl-1 f (⊗l-1 g)) ⟩
  ccut Γ f' (scut (Il-1 f) (⊗l-1 g)) refl
  ∎
scutIl-1 (Il f) g = refl

ccut⊗l-1 : ∀{Γ Δ}{A B C D} Δ₀ {Δ'}
  → (f : nothing ∣ Γ ⊢ C)(g : just (A ⊗ B) ∣ Δ ⊢ D)
  → (r : Δ ≡ Δ₀ ++ C ∷ Δ')
  → ⊗l-1 (ccut Δ₀ f g r) ≡ ccut (B ∷ Δ₀) f (⊗l-1 g) (cong (_∷_ B) r)
ccut⊗l-1 Δ₀ f (ax refl) r = ⊥-elim (lemma[] Δ₀ r)
ccut⊗l-1 {B = B} Δ₀ f (⊗r {Γ = Γ} g g₁ refl) r with inj∷ (cong (_∷_ B) r)
ccut⊗l-1 {B = B} Δ₀ f (⊗r {Γ = Γ} g g₁ refl) r | refl , r' with uip {p = r}{r'}
ccut⊗l-1 {B = B} Δ₀ f (⊗r {Γ = Γ} g g₁ refl) r | refl , .r | refl with lemma++ Δ₀ Γ r
ccut⊗l-1 {Γ} {B = B} Δ₀ f (⊗r {Γ = Γ'} g g₁ refl) r | refl , .r | refl | inj₁ (Γ₀ , refl , q) =
  begin
  ⊗r (⊗l-1 (ccut Δ₀ f g refl)) g₁ (cong (_∷_ B) (trans (++ass (Δ₀ ++ Γ)) (cong (_++_ (Δ₀ ++ Γ)) (sym q))))
  ≡⟨ cong (λ a → ⊗r a g₁ _) (ccut⊗l-1 Δ₀ f g refl) ⟩
  ⊗r (ccut (B ∷ Δ₀) f (⊗l-1 g) refl) g₁ (cong (_∷_ B) (trans (++ass (Δ₀ ++ Γ)) (cong (_++_ (Δ₀ ++ Γ)) (sym q))))
  ≡⟨ cong (⊗r (ccut (B ∷ Δ₀) f (⊗l-1 g) refl) g₁) uip ⟩
  ⊗r (ccut (B ∷ Δ₀) f (⊗l-1 g) refl) g₁ (trans (cong (_∷_ B) (++ass (Δ₀ ++ Γ))) (cong (λ ys → B ∷ (Δ₀ ++ Γ) ++ ys) (sym q)))
  ∎
ccut⊗l-1 {B = B} Δ₀ f (⊗r {Γ = Γ} g g₁ refl) r | refl , .r | refl | inj₂ (Γ₀ , p , q) = cong (⊗r (⊗l-1 g) (ccut Γ₀ f g₁ p)) uip
ccut⊗l-1 Δ₀ f (⊗l g) r = refl

scut⊗l-1 : {Γ Δ : List Tm} → {A B C D : Tm}
  → (f : just (A ⊗ B) ∣ Γ ⊢ C)(g : just C ∣ Δ ⊢ D)
  → ⊗l-1 (scut f g) ≡ scut (⊗l-1 f) g
scut⊗l-1 (ax refl) g = sym (ccutufax [] (⊗l-1 g) refl)
scut⊗l-1 {B = B} (⊗r {Γ = Γ} f f₁ refl) g =
  begin
  ⊗l-1 (ccut Γ f₁ (scut f (⊗l-1 g)) refl)
  ≡⟨ ccut⊗l-1 Γ f₁ (scut f (⊗l-1 g)) refl ⟩
  ccut (B ∷ Γ) f₁ (⊗l-1 (scut f (⊗l-1 g))) refl
  ≡⟨ cong (λ a → ccut (B ∷ Γ) f₁ a refl) (scut⊗l-1 f (⊗l-1 g)) ⟩
  ccut (B ∷ Γ) f₁ (scut (⊗l-1 f) (⊗l-1 g)) refl
  ∎
scut⊗l-1 (⊗l f) g = refl

mutual
  scutccut : {T : Maybe Tm}{Γ₁ Γ₂ Δ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} → {A₁ A₂ C : Tm}
    → (f₁ : T ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : just A₁ ∣ Δ ⊢ C)
    → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
    → let t = trans (cong (_++_ Γ₁) r) (sym (++ass Γ₁))
          e = trans (cong (λ a → a ++ Δ') (++ass Γ₁)) (++ass Γ₁)
       in scut f₁ (ccut Δ₀ f₂ g r) ≡
          subeq e (ccut (Γ₁ ++ Δ₀) f₂ (scut f₁ g) t)
  scutccut Δ₀ (ax refl) f₂ g refl = refl
  scutccut Δ₀ (uf {Γ}{A = A} f₁ refl) f₂ g r
    with lemma∷ (A ∷ Γ ++ Δ₀) (trans (cong (λ ys → A ∷ Γ ++ ys) r) (sym (cong (_∷_ A) (++ass Γ))))
  scutccut Δ₀ (uf {Γ} {A = A} f₁ refl) f₂ g r | inj₁ (refl , () , s)
  scutccut Δ₀ {Δ'} (uf {Γ} {A = A} f₁ refl) f₂ g r | inj₂ (.(Γ ++ Δ₀) , q , refl) =
    begin
    uf (scut f₁ (ccut Δ₀ f₂ g r)) refl
    ≡⟨ cong₂ uf (scutccut Δ₀ f₁ f₂ g r) refl ⟩
    uf (subeq (trans (cong (λ a → a ++ Δ') (++ass Γ)) (++ass Γ)) (ccut (Γ ++ Δ₀) f₂ (scut f₁ g) (trans (cong (_++_ Γ) r) (sym (++ass Γ))))) refl
    ≡⟨ subequf refl (trans (cong (λ a → a ++ Δ') (++ass Γ)) (++ass Γ)) ⟩
    uf (ccut (Γ ++ Δ₀) f₂ (scut f₁ g) (trans (cong (_++_ Γ) r) (sym (++ass Γ)))) (trans (cong (_∷_ A) (trans (cong (λ a → a ++ Δ') (++ass Γ)) (++ass Γ))) refl)
    ≡⟨ cong₂ uf (cong (ccut (Γ ++ Δ₀) f₂ (scut f₁ g)) uip) refl ⟩
    uf (ccut (Γ ++ Δ₀) f₂ (scut f₁ g) q) (trans (cong (_∷_ A) (trans (cong (λ a → a ++ Δ') (++ass Γ)) (++ass Γ))) refl)
    ≡⟨ cong (uf (ccut (Γ ++ Δ₀) f₂ (scut f₁ g) q)) uip ⟩
    uf (ccut (Γ ++ Δ₀) f₂ (scut f₁ g) q) (trans (cong (λ a → a ++ Δ') (cong (_∷_ A) (++ass Γ))) (cong (_∷_ A) (++ass Γ)))
    ≡⟨ sym (subequf' refl (trans (cong (λ a → a ++ Δ') (cong (_∷_ A) (++ass Γ))) (cong (_∷_ A) (++ass Γ)))) ⟩
    subeq (trans (cong (λ a → a ++ Δ') (cong (_∷_ A) (++ass Γ))) (cong (_∷_ A) (++ass Γ))) (uf (ccut (Γ ++ Δ₀) f₂ (scut f₁ g) q) refl)
    ∎
  scutccut Δ₀ (Ir refl) f₂ g r =
    begin
    Il-1 (ccut Δ₀ f₂ g r)
    ≡⟨ ccutIl-1 Δ₀ f₂ g r ⟩
    ccut Δ₀ f₂ (Il-1 g) r
    ≡⟨ cong (ccut Δ₀ f₂ (Il-1 g)) uip ⟩
    ccut Δ₀ f₂ (Il-1 g) (trans (cong (λ ys → ys) r) refl)
    ∎
  scutccut Δ₀ {Δ'} (⊗r {Γ = Γ}{Δ}{B = B} f₁ f₁' refl) f₂ g refl =
    begin
    ccut Γ f₁' (scut f₁ (⊗l-1 (ccut Δ₀ f₂ g refl))) refl
    ≡⟨ cong (λ a → ccut Γ f₁' (scut f₁ a) refl) (ccut⊗l-1 Δ₀ f₂ g refl) ⟩
    ccut Γ f₁' (scut f₁ (ccut (B ∷ Δ₀) f₂ (⊗l-1 g) refl)) refl
    ≡⟨ cong (λ a → ccut Γ f₁' a refl) (scutccut (B ∷ Δ₀) f₁ f₂ (⊗l-1 g) refl) ⟩
    ccut Γ f₁' (subeq (trans (cong (λ a → a ++ Δ') (++ass Γ)) (++ass Γ)) (ccut (Γ ++ B ∷ Δ₀) f₂ (scut f₁ (⊗l-1 g)) (sym (++ass Γ)))) refl
    ≡⟨ ccutsubeq Γ f₁' {ccut (Γ ++ B ∷ Δ₀) f₂ (scut f₁ (⊗l-1 g)) (sym (++ass Γ))} refl (trans (cong (λ a → a ++ Δ') (++ass Γ)) (++ass Γ)) ⟩
    ccut Γ f₁' (ccut (Γ ++ B ∷ Δ₀) f₂ (scut f₁ (⊗l-1 g)) (sym (++ass Γ))) (trans (trans (cong (λ a → a ++ Δ') (++ass Γ)) (++ass Γ)) refl)
    ≡⟨ cong (ccut Γ f₁' (ccut (Γ ++ B ∷ Δ₀) f₂ (scut f₁ (⊗l-1 g)) (sym (++ass Γ)))) uip ⟩
    ccut Γ f₁' (ccut (Γ ++ B ∷ Δ₀) f₂ (scut f₁ (⊗l-1 g)) (sym (++ass Γ))) (trans (cong (λ a → a ++ Δ') (++ass Γ)) (++ass Γ))
    ≡⟨ ccutccut Γ f₁' f₂ (scut f₁ (⊗l-1 g)) (sym (++ass Γ))  ⟩
    subeq (trans (cong (λ a → a ++ Δ') (++ass (Γ ++ Δ))) (++ass (Γ ++ Δ))) (ccut ((Γ ++ Δ) ++ Δ₀) f₂ (ccut Γ f₁' (scut f₁ (⊗l-1 g)) _) (sym (++ass (Γ ++ Δ))))
    ≡⟨ cong (λ a → subeq (trans (cong (λ a → a ++ Δ') (++ass (Γ ++ Δ))) (++ass (Γ ++ Δ))) (ccut ((Γ ++ Δ) ++ Δ₀) f₂ (ccut Γ f₁' (scut f₁ (⊗l-1 g)) a) (sym (++ass (Γ ++ Δ))))) (uip {p = trans (sym (++ass Γ)) (++ass Γ)}{refl})  ⟩
    subeq (trans (cong (λ a → a ++ Δ') (++ass (Γ ++ Δ))) (++ass (Γ ++ Δ))) (ccut ((Γ ++ Δ) ++ Δ₀) f₂ (ccut Γ f₁' (scut f₁ (⊗l-1 g)) refl) (sym (++ass (Γ ++ Δ))))
    ∎
  scutccut {_}{Γ₁} Δ₀ {Δ'} (Il f₁) f₂ g refl =
    begin
    Il (scut f₁ (ccut Δ₀ f₂ g refl))
    ≡⟨ cong Il (scutccut Δ₀ f₁ f₂ g refl) ⟩
    Il (subeq (trans (cong (λ a → a ++ Δ') (++ass Γ₁)) (++ass Γ₁))  (ccut (Γ₁ ++ Δ₀) f₂ (scut f₁ g) (sym (++ass Γ₁))))
    ≡⟨ sym (subeqIl (trans (cong (λ a → a ++ Δ') (++ass Γ₁)) (++ass Γ₁))) ⟩
    subeq (trans (cong (λ a → a ++ Δ') (++ass Γ₁)) (++ass Γ₁)) (Il (ccut (Γ₁ ++ Δ₀) f₂ (scut f₁ g) (sym (++ass Γ₁))))
    ∎
  scutccut {Γ₁ = Γ₁} Δ₀ {Δ'} (⊗l {B = B} f₁) f₂ g refl =
    begin
    ⊗l (scut f₁ (ccut Δ₀ f₂ g refl))
    ≡⟨ cong ⊗l (scutccut Δ₀ f₁ f₂ g refl) ⟩
    ⊗l (subeq (trans (cong (λ a → a ++ Δ') (++ass (B ∷ Γ₁))) (++ass (B ∷ Γ₁))) (ccut ((B ∷ Γ₁) ++ Δ₀) f₂ (scut f₁ g) (sym (++ass (B ∷ Γ₁)))))
    ≡⟨ cong₂ (λ a b → ⊗l (subeq a (ccut ((B ∷ Γ₁) ++ Δ₀) f₂ (scut f₁ g) b)))
             (uip {p = trans (cong (λ a → a ++ Δ') (++ass (B ∷ Γ₁))) (++ass (B ∷ Γ₁))}{cong (_∷_ B) (trans (cong (λ a → a ++ Δ') (++ass Γ₁)) (++ass Γ₁))})
             (uip {p = (sym (++ass (B ∷ Γ₁)))}{cong (_∷_ B) (sym (++ass Γ₁))}) ⟩
    ⊗l (subeq (cong (_∷_ B) (trans (cong (λ a → a ++ Δ') (++ass Γ₁)) (++ass Γ₁))) (ccut (B ∷ Γ₁ ++ Δ₀) f₂ (scut f₁ g) (cong (_∷_ B) (sym (++ass Γ₁)))))
    ≡⟨ sym (subeq⊗l (trans (cong (λ a → a ++ Δ') (++ass Γ₁)) (++ass Γ₁))) ⟩
    subeq (trans (cong (λ a → a ++ Δ') (++ass Γ₁)) (++ass Γ₁)) (⊗l (ccut (B ∷ Γ₁ ++ Δ₀) f₂ (scut f₁ g) (cong (_∷_ B) (sym (++ass Γ₁)))))
    ∎

  ccutccut : {T : Maybe Tm} → {Γ₁ Γ₂ : List Tm} → (Δ₀ : List Tm) → {Δ Δ₁ Δ₂ : List Tm} → {A₁ A₂ C : Tm}
    → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
    → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
    → let t = trans (cong (λ a → a ++ Δ₂) (++ass Δ₀)) (++ass Δ₀)
          r' = trans r (++ass Δ₀)
          t' = sym (++ass (Δ₀ ++ Γ₁))
          e' = trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))
       in ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) t ≡
          subeq e' (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g r') t')
  ccutccut Δ₀ {_}{Δ₁}{_}{A₁} f₁ f₂ (ax refl) r = ⊥-elim (lemma[] (Δ₀ ++ A₁ ∷ Δ₁) r)
  ccutccut Δ₀ {_}{Δ₁}{_}{A₁} f₁ f₂ (uf g refl) r with lemma∷ (Δ₀ ++ A₁ ∷ Δ₁) r
  ccutccut Δ₀ {Δ₁ = Δ₁} {A₁ = A₁} f₁ f₂ (uf g refl) r | inj₁ (refl , q , s) = ⊥-elim (lemma[] Δ₀ (sym q))
  ccutccut Δ₀ {Δ₁ = Δ₁} {A₁ = A₁} f₁ f₂ (uf g refl) r | inj₂ (Γ₀ , refl , q) with lemma∷ Δ₀ (trans r (++ass Δ₀))
  ccutccut .[] {Δ₁ = .Γ₀} {A₁ = _} f₁ f₂ (uf g refl) r | inj₂ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = scutccut Γ₀ f₁ f₂ g refl
  ccutccut {_}{Γ₁}{Γ₂} .(_ ∷ Γ₀') {Δ₁ = Δ₁}{Δ₂} {A₁}{A₂} f₁ f₂ (uf {A = A} g refl) r | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , q' , refl)
    with lemma∷ (A ∷ Γ₀') {(Δ₁ ++ Γ₂) ++ Δ₂}{((Γ₀' ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Δ₂} (trans (cong (λ a → a ++ Δ₂) (cong (_∷_ A) (++ass Γ₀'))) (cong (_∷_ A) (++ass Γ₀'))) 
  ccutccut {Γ₁ = Γ₁} {Γ₂} .(A₁ ∷ Γ₀') {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (uf {A = .A₁} g refl) r | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , q' , refl) | inj₁ (refl , () , s)
  ccutccut {Γ₁ = Γ₁} {Γ₂} .(A ∷ Γ₀') {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (uf {A = A} g refl) r | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , q , refl) | inj₂ (.Γ₀' , q' , refl)
    with lemma∷ (A ∷ (Γ₀' ++ Γ₁) ++ Δ₁) {Δ₂}{(Γ₀' ++ Γ₁) ++ Δ₁ ++ A₂ ∷ Δ₂} (sym (cong (_∷_ A) (++ass (Γ₀' ++ Γ₁))))
  ccutccut {Γ₁ = Γ₁} {Γ₂} .(A ∷ Γ₀') {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (uf {A = A} g refl) r | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , q , refl) | inj₂ (.Γ₀' , q' , refl) | inj₁ (p , () , s)
  ccutccut {Γ₁ = Γ₁} {Γ₂} .(A ∷ Γ₀') {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (uf {A = A} g refl) r | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , q , refl) | inj₂ (.Γ₀' , q' , refl) | inj₂ (.((Γ₀' ++ Γ₁) ++ Δ₁) , q'' , refl) =
    begin
    uf (ccut Γ₀' f₁ (ccut (Γ₀' ++ A₁ ∷ Δ₁) f₂ g refl) q') refl
    ≡⟨ cong₂ uf (cong (ccut Γ₀' f₁ (ccut (Γ₀' ++ A₁ ∷ Δ₁) f₂ g refl)) uip) refl ⟩
    uf (ccut Γ₀' f₁ (ccut (Γ₀' ++ A₁ ∷ Δ₁) f₂ g refl) (trans (cong (λ a → a ++ Δ₂) (++ass Γ₀')) (++ass Γ₀'))) refl
    ≡⟨ cong₂ uf (ccutccut Γ₀' f₁ f₂ g refl) refl ⟩
    uf (subeq (trans (cong (λ a → a ++ Δ₂) (++ass (Γ₀' ++ Γ₁))) (++ass (Γ₀' ++ Γ₁))) (ccut ((Γ₀' ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀' f₁ g (trans refl (++ass Γ₀'))) (sym (++ass (Γ₀' ++ Γ₁))))) refl
    ≡⟨ subequf refl (trans (cong (λ a → a ++ Δ₂) (++ass (Γ₀' ++ Γ₁))) (++ass (Γ₀' ++ Γ₁))) ⟩
    uf (ccut ((Γ₀' ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀' f₁ g (trans refl (++ass Γ₀'))) (sym (++ass (Γ₀' ++ Γ₁)))) (trans (cong (_∷_ A) (trans (cong (λ a → a ++ Δ₂) (++ass (Γ₀' ++ Γ₁))) (++ass (Γ₀' ++ Γ₁)))) refl)
    ≡⟨ cong₂ uf (cong₂ (λ a b → ccut ((Γ₀' ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀' f₁ g a) b) (uip {p = trans refl (++ass Γ₀')}{q}) (uip {p = sym (++ass (Γ₀' ++ Γ₁))}{q''})) refl ⟩
    uf (ccut ((Γ₀' ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀' f₁ g q) q'') (trans (cong (_∷_ A) (trans (cong (λ a → a ++ Δ₂) (++ass (Γ₀' ++ Γ₁))) (++ass (Γ₀' ++ Γ₁)))) refl)
    ≡⟨ cong (uf (ccut ((Γ₀' ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀' f₁ g q) q'')) uip ⟩
    uf (ccut ((Γ₀' ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀' f₁ g q) q'') (trans refl (trans (cong (λ a → a ++ Δ₂) (cong (_∷_ A) (++ass (Γ₀' ++ Γ₁)))) (cong (_∷_ A) (++ass (Γ₀' ++ Γ₁)))))
    ≡⟨ sym (subequf' refl (trans (cong (λ a → a ++ Δ₂) (cong (_∷_ A) (++ass (Γ₀' ++ Γ₁)))) (cong (_∷_ A) (++ass (Γ₀' ++ Γ₁))))) ⟩
    subeq (trans (cong (λ a → a ++ Δ₂) (cong (_∷_ A) (++ass (Γ₀' ++ Γ₁)))) (cong (_∷_ A) (++ass (Γ₀' ++ Γ₁)))) (uf (ccut ((Γ₀' ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀' f₁ g q) q'') refl)
    ∎
  ccutccut Δ₀ {_}{Δ₁}{_}{A₁} f₁ f₂ (Ir refl) r = ⊥-elim (lemma[] (Δ₀ ++ A₁ ∷ Δ₁) r)
  ccutccut Δ₀ f₁ f₂ (⊗r {Γ = Γ'} g g₁ refl) q with lemma++ Δ₀ Γ' (trans q (++ass Δ₀))
  ccutccut {_}{Γ₁}{Γ₂} Δ₀ {_}{Δ₁}{Δ₂} f₁ f₂ (⊗r {Γ = Γ'} g g₁ refl) q | inj₁ (Γ₀ , r , s) with lemma++ ((Δ₀ ++ Γ₁) ++ Δ₁) ((Δ₀ ++ Γ₁) ++ Γ₀) (trans (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s))) (sym (++ass (Δ₀ ++ Γ₁))))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₁ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s') with lemma++ (Δ₀ ++ A₁ ∷ Δ₁) Γ q
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₁ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s') | inj₁ (Γ₀'' , r'' , s'')
    with lemma++ Δ₀ (((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Γ₀'') (trans (trans (++ass ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂)) (cong (_++_ ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂)) (sym s''))) (trans (cong (λ a → a ++ Δ₂) (++ass Δ₀)) (++ass Δ₀)))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀' ++ _)} {A₁} {A₂} f₁ f₂ (⊗r {Γ = .(Δ₀ ++ A₁ ∷ Γ₀)} g g₁ refl) q | inj₁ (Γ₀ , refl , s) | inj₁ (Γ₀' , r' , refl) | inj₁ (Γ₀'' , r'' , s'') | inj₁ (Γ₀''' , r''' , s''')
    with lemma++' (Δ₁ ++ A₂ ∷ Γ₀') Γ₀ (trans (++ass Δ₁) s)
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀' ++ _)} {A₁} {A₂} f₁ f₂ (⊗r {_} {.(Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀')} g g₁ refl) q | inj₁ (.(Δ₁ ++ A₂ ∷ Γ₀') , refl , s) | inj₁ (Γ₀' , r' , refl) | inj₁ (Γ₀'' , r'' , s'') | inj₁ (Γ₀''' , r''' , s''') | refl
    with lemma++' Γ₀' Γ₀'' s''
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀' ++ _)} {A₁} {A₂} f₁ f₂ (⊗r {_} {.(Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀')}{Δ} g g₁ refl) q | inj₁ (.(Δ₁ ++ A₂ ∷ Γ₀') , refl , s) | inj₁ (Γ₀' , r' , refl) | inj₁ (.Γ₀' , r'' , refl) | inj₁ (Γ₀''' , r''' , s''') | refl | refl
    with lemma++' ((Δ₁ ++ Γ₂) ++ Γ₀') Γ₀''' (trans (++ass (Δ₁ ++ Γ₂)) s''')
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {._} {A₁} {A₂} f₁ f₂ (⊗r {_} {._} {Δ} g g₁ refl) q | inj₁ (._ , refl , s) | inj₁ (Γ₀ , r' , refl) | inj₁ (._ , r'' , refl) | inj₁ (._ , r''' , s''') | refl | refl | refl = 
    begin
    ⊗r (ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r'') r''') g₁ (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s''')))
    ≡⟨ cong (λ a → ⊗r (ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r'') a) g₁ (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s''')))) (uip {p = r'''}{trans (cong (λ a → a ++ Γ₀) (++ass Δ₀)) (++ass Δ₀)} ) ⟩
    ⊗r (ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r'') _) g₁ (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s''')))
    ≡⟨ cong (λ a → ⊗r a g₁ (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s''')))) (ccutccut Δ₀ f₁ f₂ g r'') ⟩
    ⊗r (subeq (trans (cong (λ a → a ++ Γ₀) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))) (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g (trans r'' (++ass Δ₀))) (sym (++ass (Δ₀ ++ Γ₁))))) g₁ (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s''')))
    ≡⟨ subeq⊗r (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s'''))) (trans (cong (λ a → a ++ Γ₀) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))) ⟩
    ⊗r (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g (trans r'' (++ass Δ₀))) (sym (++ass (Δ₀ ++ Γ₁)))) g₁ _
    ≡⟨ cong (λ a → ⊗r (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g a) (sym (++ass (Δ₀ ++ Γ₁)))) g₁ _) (uip {p = trans r'' (++ass Δ₀)}{refl}) ⟩
    ⊗r (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g refl) (sym (++ass (Δ₀ ++ Γ₁)))) g₁ (trans (cong (λ a → a ++ Δ) (trans (cong (λ a → a ++ Γ₀) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁)))) (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s'''))))
    ≡⟨ cong (λ a → ⊗r (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g refl) a) g₁ _) (uip {p = sym (++ass (Δ₀ ++ Γ₁))}{r'}) ⟩
    ⊗r (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g refl) r') g₁ (trans (cong (λ a → a ++ Δ) (trans (cong (λ a → a ++ Γ₀) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁)))) (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s'''))))
    ≡⟨ cong (⊗r (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g refl) r') g₁) uip ⟩
    ⊗r (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g refl) r') g₁ (trans (trans (++ass (((Δ₀ ++ Γ₁) ++ Δ₁) ++ Γ₂)) refl) (trans (cong (λ a → a ++ Γ₀ ++ Δ) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))))
    ≡⟨ sym (subeq⊗r' (trans (++ass (((Δ₀ ++ Γ₁) ++ Δ₁) ++ Γ₂)) refl) (trans (cong (λ a → a ++ Γ₀ ++ Δ) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁)))) ⟩
    subeq (trans (cong (λ a → a ++ Γ₀ ++ Δ) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))) (⊗r (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g refl) r') g₁ (trans (++ass (((Δ₀ ++ Γ₁) ++ Δ₁) ++ Γ₂)) refl))
    ∎
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀' ++ _)} {A₁} f₁ f₂ (⊗r {Γ = .(Δ₀ ++ A₁ ∷ Γ₀)}{Δ'} g g₁ refl) q | inj₁ (Γ₀ , refl , s) | inj₁ (Γ₀' , r' , refl) | inj₁ (Γ₀'' , r'' , s'') | inj₂ (Γ₀''' , r''' , s''')
    = ⊥-elim (lemma++''' ((Δ₁ ++ Γ₂) ++ Γ₀') Δ' Γ₀''' (trans r''' (cong (_++_ Γ₀''') (cong (_∷_ A₁) (sym (++ass (Δ₁ ++ Γ₂)))))))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = .(Δ₀ ++ A₁ ∷ Γ₀)} g g₁ refl) q | inj₁ (Γ₀ , refl , s) | inj₁ (Γ₀' , r' , s') | inj₂ (Γ₀'' , refl , s'')
    = ⊥-elim (lemma++''' [] Δ₂ (Γ₀' ++ Γ₀'') (trans s' (sym (++ass Γ₀')))) 
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₁ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') with lemma++ (Δ₀ ++ A₁ ∷ Δ₁) Γ q
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = .((Δ₀ ++ A₁ ∷ Δ₁) ++ _ ∷ Γ₀'')} g g₁ refl) q | inj₁ (Γ₀ , r , s) | inj₂ (Γ₀' , refl , s') | inj₁ (Γ₀'' , refl , s'')
    = ⊥-elim (lemma++''' [] Δ₂ (Γ₀'' ++ Γ₀') (trans s'' (sym (++ass Γ₀''))))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₁ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') | inj₂ (Γ₀'' , r'' , s'')
    with lemma++ Δ₀ Γ (trans (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong (λ a → (a ++ Γ₂) ++ Δ₂) (sym s''))) (trans (cong (λ a → a ++ Δ₂) (++ass Δ₀)) (++ass Δ₀)))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = .(Δ₀ ++ A₁ ∷ Γ₀''')} g g₁ refl) q | inj₁ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') | inj₂ (Γ₀'' , refl , s'') | inj₁ (Γ₀''' , refl , s''') with lemma++' Δ₁ (Γ₀ ++ Γ₀'') (trans s (sym (++ass Γ₀)))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = .(Γ₀ ++ Γ₀'')} {Δ₂} {A₁} f₁ f₂ (⊗r {_} {.(Δ₀ ++ A₁ ∷ Γ₀''')} g g₁ refl) q | inj₁ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') | inj₂ (Γ₀'' , refl , s'') | inj₁ (Γ₀''' , refl , s''') | refl with proj₂ (inj∷ (lemma++'₂ Δ₀ r))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {_} {.(Γ₀ ++ Γ₀'')} {Δ₂} {A₁} f₁ f₂ (⊗r {_} {.(Δ₀ ++ A₁ ∷ Γ₀)} g g₁ refl) q | inj₁ (Γ₀ , refl , s) | inj₂ (Γ₀' , r' , s') | inj₂ (Γ₀'' , refl , s'') | inj₁ (.Γ₀ , refl , s''') | refl | refl with lemma++' Γ₀'' Γ₀' r'
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {_} {.(Γ₀ ++ Γ₀'')} {Δ₂} {A₁} f₁ f₂ (⊗r {_} {.(Δ₀ ++ A₁ ∷ Γ₀)} g g₁ refl) q | inj₁ (Γ₀ , refl , s) | inj₂ (.Γ₀'' , refl , s') | inj₂ (Γ₀'' , refl , s'') | inj₁ (.Γ₀ , refl , s''') | refl | refl | refl =
    begin
    ⊗r (ccut Δ₀ f₁ g refl) (ccut Γ₀'' f₂ g₁ refl) (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym s''')))
    ≡⟨ cong (⊗r (ccut Δ₀ f₁ g refl) (ccut Γ₀'' f₂ g₁ refl)) uip ⟩
    ⊗r (ccut Δ₀ f₁ g refl) (ccut Γ₀'' f₂ g₁ refl) _
    ≡⟨ sym (subeq⊗r' (trans (trans (sym (++ass ((Δ₀ ++ Γ₁) ++ Γ₀))) (cong₂ _++_ (sym (++ass ((Δ₀ ++ Γ₁) ++ Γ₀))) refl)) (cong (λ a → (a ++ Γ₂) ++ Δ₂) (sym s'))) (trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁)))) ⟩
    subeq (trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))) (⊗r (ccut Δ₀ f₁ g refl) (ccut Γ₀'' f₂ g₁ refl) _)
    ∎
  ccutccut {Γ₁ = Γ₁} {Γ₂} .(Γ ++ Γ₀''') {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₁ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') | inj₂ (Γ₀'' , refl , s'') | inj₂ (Γ₀''' , r''' , refl)
    = ⊥-elim (lemma++'''₂ Γ r)
  ccutccut {_}{Γ₁}{Γ₂} Δ₀ {_}{Δ₁}{Δ₂}{A₁}{A₂} f₁ f₂ (⊗r {Γ = Γ'} g g₁ refl) q | inj₂ (Γ₀ , r , s)
    with lemma++ ((Δ₀ ++ Γ₁) ++ Δ₁) Γ' (trans (trans (trans (sym (++ass Γ')) (cong₂ _++_ (sym (++ass Γ')) refl)) (cong (λ a → (a ++ Γ₁) ++ Δ₁ ++ A₂ ∷ Δ₂) (sym s))) (sym (++ass (Δ₀ ++ Γ₁))))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₂ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s')
    = ⊥-elim (lemma++''' [] Δ₂ ((Γ₀' ++ (Γ₀ ++ Γ₁)) ++ Δ₁) (trans s' (trans (sym (++ass Γ₀')) (sym (++ass (Γ₀' ++ (Γ₀ ++ Γ₁)))))))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₂ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') with lemma++ (Δ₀ ++ A₁ ∷ Δ₁) Γ q
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {.(Γ₀'' ++ _)} {A₁} {A₂} f₁ f₂ (⊗r {Γ = .((Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Γ₀'')}{Δ'} g g₁ refl) q | inj₂ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') | inj₁ (Γ₀'' , refl , refl)
    = ⊥-elim (lemma++''' Γ₀'' Δ' (Γ₀ ++ A₁ ∷ Δ₁) (trans r (sym (++ass Γ₀)) ))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₂ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') | inj₂ (Γ₀'' , r'' , s'')
    with lemma++ Δ₀ Γ (trans (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong (λ a → (a ++ Γ₂) ++ Δ₂) (sym s''))) (trans (cong (λ a → a ++ Δ₂) (++ass Δ₀)) (++ass Δ₀)))
  ccutccut {Γ₁ = Γ₁} {Γ₂} .(Γ ++ Γ₀) {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , r' , s') | inj₂ (Γ₀'' , r'' , s'') | inj₁ (Γ₀''' , r''' , s''')
    = ⊥-elim (lemma++'''₂ Γ r''')
  ccutccut {Γ₁ = Γ₁} {Γ₂} .(Γ ++ Γ₀) {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , r' , s') | inj₂ (Γ₀'' , r'' , s'') | inj₂ (Γ₀''' , r''' , s''') with lemma++'₂ Γ s'''
  ccutccut {Γ₁ = Γ₁} {Γ₂} .(Γ ++ Γ₀) {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , r' , s') | inj₂ (Γ₀'' , r'' , s'') | inj₂ (.Γ₀ , r''' , refl) | refl with lemma++' (Γ₀ ++ A₁ ∷ Δ₁) Γ₀'' (trans (++ass Γ₀) r'')
  ccutccut {Γ₁ = Γ₁} {Γ₂} .(Γ ++ Γ₀) {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₂ (Γ₀ , refl , refl) | inj₂ (Γ₀' , r' , s') | inj₂ (.(Γ₀ ++ A₁ ∷ Δ₁) , r'' , s'') | inj₂ (.Γ₀ , r''' , refl) | refl | refl
    with lemma++' ((Γ₀ ++ Γ₁) ++ Δ₁) Γ₀' (trans (++ass (Γ₀ ++ Γ₁)) r')
  ccutccut {Γ₁ = Γ₁} {Γ₂} .(Γ ++ Γ₀) {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁ refl) q | inj₂ (Γ₀ , refl , refl) | inj₂ (.((Γ₀ ++ Γ₁) ++ Δ₁) , r' , s') | inj₂ (.(Γ₀ ++ A₁ ∷ Δ₁) , r'' , s'') | inj₂ (.Γ₀ , r''' , refl) | refl | refl | refl =
    begin
    ⊗r g (ccut Γ₀ f₁ (ccut (Γ₀ ++ A₁ ∷ Δ₁) f₂ g₁ r'') r''') (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) refl)
    ≡⟨ cong (λ a → ⊗r g (ccut Γ₀ f₁ (ccut (Γ₀ ++ A₁ ∷ Δ₁) f₂ g₁ r'') a) (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) refl)) (uip {p = r'''}{trans (cong (λ a → a ++ Δ₂) (++ass Γ₀)) (++ass Γ₀)}) ⟩
    ⊗r g (ccut Γ₀ f₁ (ccut (Γ₀ ++ A₁ ∷ Δ₁) f₂ g₁ r'') (trans (cong (λ a → a ++ Δ₂) (++ass Γ₀)) (++ass Γ₀))) (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) refl)
    ≡⟨ cong (λ a → ⊗r g a (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) refl)) (ccutccut Γ₀ f₁ f₂ g₁ r'') ⟩
    ⊗r g (subeq (trans (cong (λ a → a ++ Δ₂) (++ass (Γ₀ ++ Γ₁))) (++ass (Γ₀ ++ Γ₁))) (ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀ f₁ g₁ (trans r'' (++ass Γ₀))) (sym (++ass (Γ₀ ++ Γ₁))))) (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) refl)
    ≡⟨ subeq⊗r₂ (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) refl) (trans (cong (λ a → a ++ Δ₂) (++ass (Γ₀ ++ Γ₁))) (++ass (Γ₀ ++ Γ₁))) ⟩
    ⊗r g (ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀ f₁ g₁ (trans r'' (++ass Γ₀))) (sym (++ass (Γ₀ ++ Γ₁)))) _
    ≡⟨ cong₂ (λ a b → ⊗r g (ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀ f₁ g₁ a) b) _) (uip {p = trans r'' (++ass Γ₀)}{refl}) (uip {p = sym (++ass (Γ₀ ++ Γ₁))}{r'}) ⟩
    ⊗r g (ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀ f₁ g₁ refl) r') _
    ≡⟨ cong (⊗r g (ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀ f₁ g₁ refl) r')) uip ⟩
    ⊗r g (ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀ f₁ g₁ refl) r') (trans (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong (λ a → (a ++ Γ₂) ++ Δ₂) (sym s'))) (trans (cong (λ a → a ++ Δ₂) (++ass ((Γ ++ Γ₀) ++ Γ₁))) (++ass ((Γ ++ Γ₀) ++ Γ₁))))
    ≡⟨ sym (subeq⊗r' (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong (λ a → (a ++ Γ₂) ++ Δ₂) (sym s'))) (trans (cong (λ a → a ++ Δ₂) (++ass ((Γ ++ Γ₀) ++ Γ₁))) (++ass ((Γ ++ Γ₀) ++ Γ₁)))) ⟩
    subeq (trans (cong (λ a → a ++ Δ₂) (++ass ((Γ ++ Γ₀) ++ Γ₁))) (++ass ((Γ ++ Γ₀) ++ Γ₁))) (⊗r g (ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀ f₁ g₁ refl) r') (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong (λ a → (a ++ Γ₂) ++ Δ₂) (sym s'))))
    ∎
  ccutccut {_}{Γ₁} Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (Il g) r =
    begin
    Il (ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) (trans (cong (λ a → a ++ Δ₂) (++ass Δ₀)) (++ass Δ₀)))
    ≡⟨ cong Il (ccutccut Δ₀ f₁ f₂ g r) ⟩
    Il (subeq (trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))) (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g (trans r (++ass Δ₀))) (sym (++ass (Δ₀ ++ Γ₁)))))
    ≡⟨ sym (subeqIl (trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁)))) ⟩
    subeq (trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))) (Il (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g (trans r (++ass Δ₀))) (sym (++ass (Δ₀ ++ Γ₁)))))
    ∎
  ccutccut {_}{Γ₁} Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗l {B = B} g) r = 
    begin
    ⊗l (ccut (B ∷ Δ₀) f₁ (ccut (B ∷ Δ₀ ++ A₁ ∷ Δ₁) f₂ g (cong (_∷_ B) r)) (cong (_∷_ B) (trans (cong (λ a → a ++ Δ₂) (++ass Δ₀)) (++ass Δ₀))))
    ≡⟨ cong ⊗l (cong (ccut (B ∷ Δ₀) f₁ (ccut (B ∷ Δ₀ ++ A₁ ∷ Δ₁) f₂ g (cong (_∷_ B) r))) uip) ⟩
    ⊗l (ccut (B ∷ Δ₀) f₁ (ccut (B ∷ Δ₀ ++ A₁ ∷ Δ₁) f₂ g (cong (_∷_ B) r)) (trans (cong (λ a → a ++ Δ₂) (cong (_∷_ B) (++ass Δ₀))) (cong (_∷_ B) (++ass Δ₀))))
    ≡⟨ cong ⊗l (ccutccut (B ∷ Δ₀) f₁ f₂ g (cong (_∷_ B) r)) ⟩
    ⊗l (subeq (trans (cong (λ a → a ++ Δ₂) (++ass ((B ∷ Δ₀) ++ Γ₁))) (++ass ((B ∷ Δ₀) ++ Γ₁))) (ccut (((B ∷ Δ₀) ++ Γ₁) ++ Δ₁) f₂ (ccut (B ∷ Δ₀) f₁ g (trans (cong (_∷_ B) r) (++ass (B ∷ Δ₀)))) (sym (++ass ((B ∷ Δ₀) ++ Γ₁)))))
    ≡⟨ cong ⊗l (cong (subeq (trans (cong (λ a → a ++ Δ₂) (++ass ((B ∷ Δ₀) ++ Γ₁))) (++ass ((B ∷ Δ₀) ++ Γ₁)))) (cong (ccut (((B ∷ Δ₀) ++ Γ₁) ++ Δ₁) f₂ (ccut (B ∷ Δ₀) f₁ g (trans (cong (_∷_ B) r) (++ass (B ∷ Δ₀))))) uip)) ⟩
    ⊗l (subeq (trans (cong (λ a → a ++ Δ₂) (++ass ((B ∷ Δ₀) ++ Γ₁))) (++ass ((B ∷ Δ₀) ++ Γ₁))) (ccut (((B ∷ Δ₀) ++ Γ₁) ++ Δ₁) f₂ (ccut (B ∷ Δ₀) f₁ g (trans (cong (_∷_ B) r) (++ass (B ∷ Δ₀)))) (cong (_∷_ B) (sym (++ass (Δ₀ ++ Γ₁))))))
    ≡⟨ cong₂ (λ a b → ⊗l (subeq a (ccut (((B ∷ Δ₀) ++ Γ₁) ++ Δ₁) f₂ (ccut (B ∷ Δ₀) f₁ g b) (cong (_∷_ B) (sym (++ass (Δ₀ ++ Γ₁)))))))
         (uip {p = trans (cong (λ a → a ++ Δ₂) (++ass ((B ∷ Δ₀) ++ Γ₁))) (++ass ((B ∷ Δ₀) ++ Γ₁))}{(cong (_∷_ B) (trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))))})
         (uip {p = trans (cong (_∷_ B) r) (++ass (B ∷ Δ₀))}{cong (_∷_ B) (trans r (++ass Δ₀))}) ⟩
    ⊗l (subeq (cong (_∷_ B) (trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁)))) (ccut (B ∷ (Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut (B ∷ Δ₀) f₁ g (cong (_∷_ B) (trans r (++ass Δ₀)))) (cong (_∷_ B) (sym (++ass (Δ₀ ++ Γ₁))))))
    ≡⟨ sym (subeq⊗l (trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁)))) ⟩
    subeq (trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))) (⊗l (ccut (B ∷ (Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut (B ∷ Δ₀) f₁ g (cong (_∷_ B) (trans r (++ass Δ₀)))) (cong (_∷_ B) (sym (++ass (Δ₀ ++ Γ₁))))))
    ∎



{-
ccutccut Δ₀ f₁ f₂ ax r = {!!}
  ccutccut Δ₀ f₁ f₂ (uf g) r = {!!}
  ccutccut Δ₀ f₁ f₂ Ir r = {!!}
  ccutccut {_}{Γ₁}{Γ₂} Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ'}{Δ'} g g') p with lemma++ (Δ₀ ++ A₁ ∷ Δ₁) Γ' p | lemma++ Δ₀ Γ' (trans p (++ass Δ₀))
  ccutccut {_}{Γ₁}{Γ₂} Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ'}{Δ'} g g') p | inj₁ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s')
    with lemma++ Δ₀ (((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Γ₀) (trans (trans (++ass ((Δ₀ ++ A₁ ∷ Δ₁) ++ _)) (cong (_++_ ((Δ₀ ++ A₁ ∷ Δ₁) ++ _)) (sym s))) (trans (cong (λ a → a ++ Δ₂) (++ass Δ₀)) (++ass Δ₀)))
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ'} {Δ'} g g') p | inj₁ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s') | inj₁ (Γ₀'' , r'' , s'') = 
    begin
    ccut Δ₀ f₁ (subeq e (⊗r (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) g')) t
    ≡⟨ {!!} ⟩
    ccut Δ₀ f₁ (⊗r (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) g') (trans e t)
    ≡⟨ refl ⟩
    {!ccut Δ₀ f₁ (⊗r (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) g') (trans e t)!}
    ≡⟨ {!!} ⟩
    {!!}
    ∎
{-subeq
      (trans (cong (λ a → a ++ .Δ₂) (++ass (Δ₀ ++ .Γ₁)))
       (++ass (Δ₀ ++ .Γ₁)))
      (ccut ((Δ₀ ++ .Γ₁) ++ Δ₁) f₂
       (subeq
        (.SkewMonCatSeqCalc2002.e Δ₀ (trans r (++ass Δ₀)) Γ₀' p' q' f₁ g
         g₁)
        (⊗r (ccut Δ₀ f₁ g p') g₁))
       (sym (++ass (Δ₀ ++ .Γ₁))))
-}
   where
      e : (((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Γ₀) ++ Δ' ≡ ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Δ₂
      e = trans (++ass ((Δ₀ ++ A₁ ∷ Δ₁) ++ _)) (cong (_++_ ((Δ₀ ++ A₁ ∷ Δ₁) ++ _)) (sym s))

      t : ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Δ₂ ≡ Δ₀ ++ A₁ ∷ (Δ₁ ++ Γ₂) ++ Δ₂
      t = trans (cong (λ a → a ++ Δ₂) (++ass Δ₀)) (++ass Δ₀)
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊗r {Γ = Γ} {Δ} g g') p | inj₁ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s') | inj₂ (Γ₀'' , r'' , s'') = {!!} 
  ccutccut {_}{Γ₁}{Γ₂} Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ'}{Δ'} g g') p | inj₁ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') = {!!}
  ccutccut {_}{Γ₁}{Γ₂} Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ'}{Δ'} g g') p | inj₂ (Γ₀ , r , s) | inj₁ (Γ₀' , r' , s') = {!!}
  ccutccut {_}{Γ₁}{Γ₂} Δ₀ {_}{Δ₁}{Δ₂}{A₁} f₁ f₂ (⊗r {Γ = Γ'}{Δ'} g g') p | inj₂ (Γ₀ , r , s) | inj₂ (Γ₀' , r' , s') = {!!}
  ccutccut Δ₀ f₁ f₂ (Il g) r = {!!}
  ccutccut Δ₀ f₁ f₂ (⊗l g) r = {!!}
-}

{-
{-
ccutufax : {T : Maybe Tm} → {Γ Δ : List Tm} → (Δ₀ : List Tm) → {B C : Tm} → 
           (g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ B ∷ Γ) →  
           subeq (trans r (sym (++ass Δ₀))) g ≡ ccut Δ₀ (uf ax) g r
ccutufax Δ₀ ax r = ⊥-elim (lemma[] Δ₀ r)
ccutufax Δ₀ (uf f) r with lemma∷ Δ₀ r
ccutufax .[] (uf f) refl | inj₁ (refl , refl , refl) = refl
ccutufax .(_ ∷ Δ₀) (uf {A = A} f) refl | inj₂ (Δ₀ , refl , refl) =
  trans (trans (cong (λ a → subeq a (uf f)) (uip {p = sym (cong (_∷_ A) (++ass Δ₀))}{cong (_∷_ A) (sym (++ass Δ₀))})) (subequf (sym (++ass Δ₀))))
        (cong uf (ccutufax Δ₀ f refl))
ccutufax Δ₀ Ir r  = ⊥-elim (lemma[] Δ₀ r)
ccutufax Δ₀ (⊗r {Γ = Γ} f f') r with lemma++ Δ₀ Γ r
ccutufax Δ₀ {B} (⊗r {Γ = .(Δ₀ ++ _)}{Δ} f f') r | inj₁ (Γ₀ , refl , refl) =
  trans (trans (trans (cong (λ a → subeq a (⊗r f f')) (uip {p = trans r (sym (++ass Δ₀))}{trans (cong (λ a → a ++ Δ) (sym (++ass Δ₀))) (++ass (Δ₀ ++ B ∷ []))}))
                                (subeqtrans (cong (λ a → a ++ Δ) (sym (++ass Δ₀))) (++ass (Δ₀ ++ B ∷ []))))
               (cong (subeq (++ass (Δ₀ ++ B ∷ []))) (subeq⊗r (sym (++ass Δ₀)))))
         (cong (subeq (++ass (Δ₀ ++ B ∷ []))) (cong₂ ⊗r (ccutufax Δ₀ f refl) refl))
ccutufax .(Γ ++ Γ₀) (⊗r {Γ = Γ} f f') r | inj₂ (Γ₀ , refl , refl) = 
  trans (trans (trans (cong (λ a → subeq a (⊗r f f')) (uip {p = trans r (sym (++ass (Γ ++ Γ₀)))}
                                                            {trans (cong (_++_ Γ) (sym (++ass Γ₀))) (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))}))
                      (subeqtrans (cong (_++_ Γ) (sym (++ass Γ₀))) (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))))
               (cong (subeq (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))) (subeq⊗r2 (sym (++ass Γ₀)))))
        (cong (subeq (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))) (cong₂ ⊗r refl (ccutufax Γ₀ f' refl)))
ccutufax Δ₀ (Il f) refl =
  trans (subeqIl (sym (++ass Δ₀))) (cong Il (ccutufax Δ₀ f refl))
ccutufax Δ₀ (⊗l {B = B} f) refl =
  trans (trans (subeq⊗l (sym (++ass Δ₀))) (cong (λ a → ⊗l (subeq a f)) (uip {p = cong (_∷_ B) (sym (++ass Δ₀))}{sym (cong (_∷_ B) (++ass Δ₀))})))
        (cong ⊗l (ccutufax (B ∷ Δ₀) f refl))
-}

ccutIl-1 : ∀{Γ}{Δ}{A}{C} Δ₀ {Δ'}
  → (f : nothing ∣ Γ ⊢ A)(g : just I ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → Il-1 (ccut Δ₀ f g r) ≡ ccut Δ₀ f (Il-1 g) r
ccutIl-1 Δ₀ f ax r = ⊥-elim (lemma[] Δ₀ r)
ccutIl-1 Δ₀ f (⊗r {Γ = Γ}{Δ}  g g₁) r with lemma++ Δ₀ Γ r
ccutIl-1 {Γ} Δ₀ f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) r | inj₁ (Γ₀ , refl , refl) =
  trans (sym (subeqIl-1 (++ass (Δ₀ ++ Γ)) ))
        (cong (λ a → subeq (++ass (Δ₀ ++ Γ)) (⊗r a g₁)) (ccutIl-1 Δ₀ f g refl))
ccutIl-1 .(Γ ++ Γ₀) f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ _)} g g₁) r | inj₂ (Γ₀ , refl , refl) =
  sym (subeqIl-1 (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)))
ccutIl-1 Δ₀ f (Il g) r = refl

scutIl-1 : {Γ Δ : List Tm} → {A C : Tm}
  → (f : just I ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ C)
  → Il-1 (scut f g) ≡ scut (Il-1 f) g
scutIl-1 ax g = refl
scutIl-1 (⊗r {Γ = Γ} f f') g =
  begin
  Il-1 (ccut Γ f' (scut f (⊗l-1 g)) refl)
  ≡⟨ ccutIl-1 Γ f' (scut f (⊗l-1 g)) refl ⟩
  ccut Γ f' (Il-1 (scut f (⊗l-1 g))) refl
  ≡⟨ cong (λ a → ccut Γ f' a refl) (scutIl-1 f (⊗l-1 g)) ⟩
  ccut Γ f' (scut (Il-1 f) (⊗l-1 g)) refl
  ∎
scutIl-1 (Il f) g = refl

ccut⊗l-1 : ∀{Γ Δ}{A B C D} Δ₀ {Δ'}
  → (f : nothing ∣ Γ ⊢ C)(g : just (A ⊗ B) ∣ Δ ⊢ D)
  → (r : Δ ≡ Δ₀ ++ C ∷ Δ')
  → ⊗l-1 (ccut Δ₀ f g r) ≡ ccut (B ∷ Δ₀) f (⊗l-1 g) (cong (_∷_ B) r)
ccut⊗l-1 Δ₀ f ax r = ⊥-elim (lemma[] Δ₀ r)
ccut⊗l-1 {B = B} Δ₀ f (⊗r {Γ = Γ} g g₁) r with lemma++ Δ₀ Γ r | inj∷ (cong (_∷_ B) r)
ccut⊗l-1 {B = B} Δ₀ f (⊗r {Γ = Γ} g g₁) r | a | refl , r' with lemma++ Δ₀ Γ r'
ccut⊗l-1 {B = B} Δ₀ f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} g g₁) r | inj₁ (Γ₀ , refl , refl) | refl , r' | inj₁ (Γ₀' , a , b) with lemma++' Γ₀ Γ₀' b
ccut⊗l-1 {Γ = Γ}{B = B} Δ₀ f (⊗r {_} {.(Δ₀ ++ _ ∷ Γ₀)} g g₁) r | inj₁ (Γ₀ , refl , refl) | refl , r' | inj₁ (.Γ₀ , refl , refl) | refl =
  begin
  ⊗l-1 (subeq (++ass (Δ₀ ++ Γ)) (⊗r (ccut Δ₀ f g refl) g₁))
  ≡⟨ sym (subeq⊗l-1 (++ass (Δ₀ ++ Γ))) ⟩
  subeq (cong (_∷_ B) (++ass (Δ₀ ++ Γ))) (⊗r (⊗l-1 (ccut Δ₀ f g refl)) g₁)
  ≡⟨ cong (subeq (cong (_∷_ B) (++ass (Δ₀ ++ Γ)))) (cong (λ a → ⊗r a g₁) (ccut⊗l-1 Δ₀ f g refl)) ⟩
  subeq (cong (_∷_ B) (++ass (Δ₀ ++ Γ))) (⊗r (ccut (B ∷ Δ₀) f (⊗l-1 g) refl) g₁)
  ∎
ccut⊗l-1 {B = B}{C} Δ₀ f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) r | inj₁ (Γ₀ , refl , refl) | refl , r' | inj₂ ([] , a , b) =
  ⊥-elim (lemma++'' Γ₀ Δ a)
ccut⊗l-1 {B = B}{C} Δ₀ f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) r | inj₁ (Γ₀ , refl , refl) | refl , r' | inj₂ (X ∷ Γ₀' , a , b) =
  ⊥-elim (lemma++'' (Γ₀' ++ C ∷ Γ₀) Δ (trans a (cong (_∷_ X) (sym (++ass Γ₀')))))
ccut⊗l-1 {B = B} .(Γ ++ []) f (⊗r {Γ = Γ} g g₁) r | inj₂ ([] , refl , refl) | refl , r' | inj₁ ([] , x , ())
ccut⊗l-1 {B = B}{C} .(Γ ++ X ∷ Γ₀) {Δ'} f (⊗r {Γ = Γ} g g₁) r | inj₂ (X ∷ Γ₀ , refl , refl) | refl , r' | inj₁ ([] , x , y) =
  ⊥-elim (lemma++'' (Γ₀ ++ C ∷ []) Δ' (trans y (cong (_∷_ X) (sym (++ass Γ₀)))))
ccut⊗l-1 {B = B}{C} .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} g g₁) r | inj₂ (Γ₀ , refl , refl) | refl , r' | inj₁ (X ∷ Γ₀' , x , y) =
  ⊥-elim (lemma++'' (Γ₀' ++ Γ₀ ++ C ∷ []) Δ' (trans y (cong (_∷_ X) (trans (cong (_++_ Γ₀') (sym (++ass Γ₀))) (sym (++ass Γ₀'))))))
ccut⊗l-1 {B = B} .(Γ ++ Γ₀) f (⊗r {Γ = Γ} g g₁) r | inj₂ (Γ₀ , refl , refl) | refl , r' | inj₂ (Γ₀' , x , y) with lemma++' Γ₀ Γ₀' x
ccut⊗l-1 {B = B} .(Γ ++ Γ₀) f (⊗r {Γ = Γ} g g₁) r | inj₂ (Γ₀ , refl , refl) | refl , r' | inj₂ (.Γ₀ , refl , refl) | refl =
  begin
  ⊗l-1 (subeq (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (⊗r g (ccut Γ₀ f g₁ refl)))
  ≡⟨ sym (subeq⊗l-1 (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))) ⟩
  subeq (cong (_∷_ B) (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))) (⊗r (⊗l-1 g) (ccut Γ₀ f g₁ refl))
  ≡⟨ cong (λ a → subeq a (⊗r (⊗l-1 g) (ccut Γ₀ f g₁ refl)))
          (uip {p = cong (_∷_ B) (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))}
               {trans (sym (cong (_∷_ B) (++ass Γ))) (cong₂ _++_ (sym (cong (_∷_ B) (++ass Γ))) refl)}) ⟩
  subeq (trans (sym (cong (_∷_ B) (++ass Γ))) (cong₂ _++_ (sym (cong (_∷_ B) (++ass Γ))) refl)) (⊗r (⊗l-1 g) (ccut Γ₀ f g₁ refl))
  ∎
ccut⊗l-1 Δ₀ f (⊗l g) r = refl

{-
scut⊗l-1 : {Γ Δ : List Tm} → {A B C D : Tm}
  → (f : just (A ⊗ B) ∣ Γ ⊢ C)(g : just C ∣ Δ ⊢ D)
  → ⊗l-1 (scut f g) ≡ scut (⊗l-1 f) g
scut⊗l-1 ax g = ccutufax [] (⊗l-1 g) refl
scut⊗l-1 {B = B} (⊗r {Γ = Γ} f f₁) g =
  begin
  ⊗l-1 (ccut Γ f₁ (scut f (⊗l-1 g)) refl)
  ≡⟨ ccut⊗l-1 Γ f₁ (scut f (⊗l-1 g)) refl ⟩
  ccut (B ∷ Γ) f₁ (⊗l-1 (scut f (⊗l-1 g))) refl
  ≡⟨ cong (λ a → ccut (B ∷ Γ) f₁ a refl) (scut⊗l-1 f (⊗l-1 g)) ⟩
  ccut (B ∷ Γ) f₁ (scut (⊗l-1 f) (⊗l-1 g)) refl
  ∎
scut⊗l-1 (⊗l f) g = refl
-}
{-
ccutccut : {T : Maybe Tm} → {Γ₁ Γ₂ Δ : List Tm} → (Δ₀ : List Tm) → {Δ₁ Δ₂ : List Tm} → {A₁ A₂ C : Tm}
  → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
  → (p : (Δ₀ ++ Γ₁) ++ Δ₁ ++ A₂ ∷ Δ₂ ≡ ((Δ₀ ++ Γ₁) ++ Δ₁) ++ A₂ ∷ Δ₂)
  → (r : Δ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Δ₂)(t : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
  → (q : ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Δ₂ ≡ Δ₀ ++ A₁ ∷ (Δ₁ ++ Γ₂) ++ Δ₂)
  → (s : (((Δ₀ ++ Γ₁) ++ Δ₁) ++ Γ₂) ++ Δ₂ ≡ (Δ₀ ++ Γ₁) ++ (Δ₁ ++ Γ₂) ++ Δ₂)
  → ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g t) q ≡
    subeq s (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g r) p)
ccutccut Δ₀ f₁ f₂ ax p r t q s = ⊥-elim (lemma[] Δ₀ r)
ccutccut Δ₀ {Δ₁}{_}{A₁} f₁ f₂ (uf g) p r t q s with lemma∷ Δ₀ r | lemma∷ (Δ₀ ++ A₁ ∷ Δ₁) t
ccutccut .[] {Δ₁} {A₁ = A₁} f₁ f₂ (uf g) p r t q s | inj₁ (a , refl , c) | inj₁ (x , () , z)
ccutccut .[] {.Γ₀} {A₁ = _} f₁ f₂ (uf g) p r t refl s | inj₁ (refl , refl , refl) | inj₂ (Γ₀ , refl , refl) = {!!}
ccutccut .(_ ∷ a) {Δ₁} {A₁ = A₁} f₁ f₂ (uf g) p r t q s | inj₂ (a , refl , refl) | inj₁ (refl , () , z)
ccutccut {Γ₁ = Γ₁} .(_ ∷ Γ₀) {Δ₁} {A₁ = A₁} f₁ f₂ (uf {A = A} g) p r t q s | inj₂ (Γ₀ , refl , refl) | inj₂ (.(Γ₀ ++ A₁ ∷ Δ₁) , y , refl) with lemma∷ (A ∷ Γ₀) q | lemma∷ (A ∷ (Γ₀ ++ Γ₁) ++ Δ₁) p
ccutccut {Γ₁ = Γ₁} .(A₁ ∷ Γ₀) {Δ₁} {A₁ = A₁} f₁ f₂ (uf {A = .A₁} g) p r t q s | inj₂ (Γ₀ , refl , refl) | inj₂ (.(Γ₀ ++ A₁ ∷ Δ₁) , y , refl) | inj₁ (refl , () , _) | b
ccutccut {Γ₁ = Γ₁} .(A ∷ Γ₀) {Δ₁} {A₁ = A₁} f₁ f₂ (uf {A = A} g) p r t q s | inj₂ (Γ₀ , refl , refl) | inj₂ (.(Γ₀ ++ A₁ ∷ Δ₁) , y , refl) | inj₂ (.Γ₀ , a , refl) | inj₁ (_ , () , _)
ccutccut {Γ₁ = Γ₁} .(A ∷ Γ₀) {Δ₁} {A₁ = A₁} f₁ f₂ (uf {A = A} g) p r t q s | inj₂ (Γ₀ , refl , refl) | inj₂ (.(Γ₀ ++ A₁ ∷ Δ₁) , y , refl) | inj₂ (.Γ₀ , a , refl) | inj₂ (.((Γ₀ ++ Γ₁) ++ Δ₁) , b , refl) =
  begin
  uf (ccut Γ₀ f₁ (ccut (Γ₀ ++ A₁ ∷ Δ₁) f₂ g y) a)
  ≡⟨ cong uf (ccutccut Γ₀ f₁ f₂ g b (proj₂ (inj∷ r)) y a (proj₂ (inj∷ s))) ⟩
  uf (subeq (proj₂ (inj∷ s)) (ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀ f₁ g (proj₂ (inj∷ r))) b))
  ≡⟨ sym (subequf (proj₂ (inj∷ s))) ⟩
  subeq (cong (_∷_ A) (proj₂ (inj∷ s))) (uf (ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀ f₁ g (proj₂ (inj∷ r))) b))
  ≡⟨ cong₂ subeq (uip {p = cong (_∷_ A) (proj₂ (inj∷ s))}{s}) (cong uf (cong (λ x → ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ x b) (cong (ccut Γ₀ f₁ g) uip))) ⟩
  subeq s (uf (ccut ((Γ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀ f₁ g refl) b))
  ∎
ccutccut Δ₀ f₁ f₂ Ir p r t q s = ⊥-elim (lemma[] Δ₀ r)
ccutccut Δ₀ {Δ₁}{A₁ = A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁) p r t q s with lemma++ Δ₀ Γ r | lemma++ (Δ₀ ++ A₁ ∷ Δ₁) Γ t
ccutccut Δ₀ {Δ₁} {A₁ = A₁} f₁ f₂ (⊗r {Γ = .(Δ₀ ++ A₁ ∷ Γ₀)} g g₁) p r t q s | inj₁ (Γ₀ , refl , b) | inj₁ (Γ₀' , x , refl) = {!!}
... | inj₁ (Γ₀ , a , b) | inj₂ (Γ₀' , x , y) = {!!}
... | inj₂ (Γ₀ , a , b) | inj₁ (Γ₀' , x , y) = {!!}
... | inj₂ (Γ₀ , a , b) | inj₂ (Γ₀' , x , y) = {!!}
ccutccut Δ₀ f₁ f₂ (Il g) p r t q s = {!!}
ccutccut Δ₀ f₁ f₂ (⊗l g) p r t q s = {!!}
-}

{-
 ccut Δ₀ f (ccut (Δ₀ ++ A ∷ Γ₀) g' (scut g (⊗l-1 h)) refl)
      (trans (cong (λ a → a ++ Δ'') r) (++ass Δ₀))
      ≡
      subeq (++ass (Δ₀ ++ Γ))
      (subeq (cong (λ a → a ++ Δ'') (++ass (Δ₀ ++ Γ)))
       (ccut ((Δ₀ ++ Γ) ++ Γ₀) g' (ccut Δ₀ f (scut g (⊗l-1 h)) (++ass Δ₀))
        (trans (sym (++ass (Δ₀ ++ Γ))) refl)))
-}

ccutuf : {Γ Δ Δ' : List Tm}{A C : Tm}
  → (f : nothing ∣ Γ ⊢ A)(g :  just A ∣ Δ ⊢ C)
  → (r : A ∷ Δ ≡ A ∷ Δ')
  → (s : Γ ++ Δ ≡ Γ ++ Δ')
  → ccut [] f (uf g) r ≡ subeq s (scut f g)
ccutuf f g refl refl = refl

ccutuf2 : {Γ Δ Δ' : List Tm}(Δ₀ : List Tm){A B C : Tm}
  → (f : nothing ∣ Γ ⊢ A)(g :  just B ∣ Δ ⊢ C)
  → (r : B ∷ Δ ≡ B ∷ Δ₀ ++ A ∷ Δ')
  → (r' : Δ ≡ Δ₀ ++ A ∷ Δ')
  → ccut (B ∷ Δ₀) f (uf g) r ≡ uf (ccut Δ₀ f g r')
ccutuf2 Δ₀ f g refl refl = refl

ccut⊗r : {T : Maybe Tm}{Γ' Γ Δ : List Tm}(Δ₀ : List Tm){Δ' : List Tm}{A B C : Tm}
  → (f : nothing ∣ Γ' ⊢ A)(g : T ∣ Γ ⊢ B)(g' : nothing ∣ Δ ⊢ C)
  → (r : Γ ++ Δ ≡ Δ₀ ++ A ∷ Δ')
  → Σ (List Tm) (λ Γ₀ → Σ (Γ ≡ Δ₀ ++ A ∷ Γ₀) (λ p → Σ (Δ' ≡ Γ₀ ++ Δ) (λ q → ccut Δ₀ f (⊗r g g') r ≡ subeq (trans (++ass (Δ₀ ++ Γ')) (cong (_++_ (Δ₀ ++ Γ')) (sym q))) (⊗r (ccut Δ₀ f g p) g')))) ⊎
    {!!}
ccut⊗r = {!!}
{-
ccut⊗r : {T : Maybe Tm} → {Γ Γ' Δ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} →  {A A' B : Tm} → 
             {h : nothing ∣ Γ' ⊢ A'}{f : T ∣ Γ ⊢ A}{g :  nothing ∣ Δ ⊢ B} →
             (r : Γ ≡ Δ₀ ++ A' ∷ Δ') (s : Γ ++ Δ ≡ Δ₀ ++ A' ∷ Δ' ++ Δ) →
             subeq (++ass (Δ₀ ++ Γ')) (⊗r (ccut Δ₀ h f r) g) ≡ ccut Δ₀ h (⊗r f g) s
ccut⊗r {Γ = Γ}{_}{Δ} Δ₀ r s with lemma++ Δ₀ Γ s
ccut⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ = Δ} Δ₀ {Δ'} r s | inj₁ (Γ₀ , refl , y) with lemma++' Δ' Γ₀ y
ccut⊗r {_} {.(Δ₀ ++ _ ∷ Γ₀)} {Δ = Δ} Δ₀ {.Γ₀} refl s | inj₁ (Γ₀ , refl , refl) | refl = refl
ccut⊗r {Γ = Γ} {Δ = Δ} Δ₀ {Δ'} r s | inj₂ ([] , x , y) = ⊥-elim (lemma++'' Δ' Δ x)
ccut⊗r {Γ = Γ} {Δ = Δ} Δ₀ {Δ'} {A' = A'} r s | inj₂ (x₁ ∷ Γ₀ , x , y) = ⊥-elim (lemma++'' (Γ₀ ++ A' ∷ Δ') Δ (trans x (sym (++ass (x₁ ∷ Γ₀)))))

ccut⊗r' : {T : Maybe Tm} → {Γ Γ₀ Γ₁ Δ : List Tm} → (Δ₀ : List Tm) → {Δ₁ Δ₂ : List Tm} →  {A A₁ A₂ B : Tm} → 
             {f₁ : nothing ∣ Γ₁ ⊢ A₁}{g : T ∣ Γ ⊢ A}{g₁ : nothing ∣ Δ ⊢ B} →
             (r : Γ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀) (r' : Γ ++ Δ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀ ++ Δ) →
             subeq (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (++ass Δ₁))) (⊗r (ccut Δ₀ f₁ g r) g₁) ≡ ccut Δ₀ f₁ (⊗r g g₁) r' --subeq (++ass (Δ₀ ++ Γ')) (⊗r (ccut Δ₀ h f r) g)
ccut⊗r' = {!!}
-}

mutual
{-
  ccutccut : {T : Maybe Tm} → {Γ₁ Γ₂ : List Tm} → (Δ₀ : List Tm) → {Δ Δ' Δ₁ Δ₂ : List Tm} → {A₁ A₂ C : Tm}
    → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)
    → (g : T ∣ Δ ⊢ C)(g' : T ∣ Δ' ⊢ C)
    → (r : Δ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Δ₂)
    → (r' : Δ' ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
    → {!ccut ccut Δ₀ f₁ g r!} ≡ {!!}
  ccutccut = {!!}
-}

  ccutccut : {T : Maybe Tm} → {Γ₁ Γ₂ : List Tm} → (Δ₀ : List Tm) → {Δ Δ₁ Δ₂ : List Tm} → {A₁ A₂ C : Tm}
    → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
    → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
    → (r' : Δ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Δ₂)
    → (a : ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Δ₂ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ Γ₂ ++ Δ₂)
    → (a' : (Δ₀ ++ Γ₁) ++ Δ₁ ++ A₂ ∷ Δ₂ ≡ ((Δ₀ ++ Γ₁) ++ Δ₁) ++ A₂ ∷ Δ₂)
    → (s : (((Δ₀ ++ Γ₁) ++ Δ₁) ++ Γ₂) ++ Δ₂ ≡ (Δ₀ ++ Γ₁) ++ Δ₁ ++ Γ₂ ++ Δ₂)
    → ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) a ≡
      subeq s (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g r') a')
  ccutccut Δ₀ f₁ f₂ ax r r' a a' s = {!!}  --imp
  ccutccut Δ₀ {_}{Δ₁}{_}{A₁} f₁ f₂ (uf g) r r' a a' s with lemma∷ (Δ₀ ++ A₁ ∷ Δ₁) r | lemma∷ Δ₀ r'
  ... | inj₁ (x , y , z) | inj₁ (x' , y' , z') = {!!} --imp
  ... | inj₁ (x , y , z) | inj₂ (x' , y' , z') = {!!} --imp
  ccutccut {_}{Γ₁} .[] {Δ₁ = .Δ₁}{Δ₂} {A₁ = _} f₁ f₂ (uf g) r r' a a' s | inj₂ (Δ₁ , refl , refl) | inj₁ (refl , refl , refl) =
    begin
    ccut [] f₁ (uf (ccut Δ₁ f₂ g refl)) a
    ≡⟨ ccutuf f₁ (ccut Δ₁ f₂ g refl) a (cong (_++_ Γ₁) (++ass Δ₁)) ⟩ 
    subeq (cong (_++_ Γ₁) (++ass Δ₁)) (scut f₁ (ccut Δ₁ f₂ g refl))
    ≡⟨ {!!} ⟩ 
    subeq s (ccut (Γ₁ ++ Δ₁) f₂ (scut f₁ g) a')
    ∎
  ccutccut {_}{Γ₁} .(_ ∷ Δ₀) {Δ₁ = Δ₁} {A₁ = A₁} f₁ f₂ (uf {A = A} g) r r' a a' s | inj₂ (.(Δ₀ ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Δ₀ , y , refl) =
    begin
    ccut (A ∷ Δ₀) f₁ (uf (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g refl)) a
    ≡⟨ ccutuf2 Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g refl) a (proj₂ (inj∷ a)) ⟩
    uf (ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g refl) (proj₂ (inj∷ a)))
    ≡⟨ cong uf (ccutccut Δ₀ f₁ f₂ g refl y (proj₂ (inj∷ a)) (proj₂ (inj∷ a')) (proj₂ (inj∷ s))) ⟩
    uf (subeq (proj₂ (inj∷ s)) (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g y) (proj₂ (inj∷ a'))))
    ≡⟨ sym (subequf (proj₂ (inj∷ s))) ⟩
    subeq (cong (_∷_ A) (proj₂ (inj∷ s))) (uf (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g y) (proj₂ (inj∷ a'))))
    ≡⟨ cong (λ a → subeq a (uf (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g y) (proj₂ (inj∷ a'))))) (uip {p = cong (_∷_ A) (proj₂ (inj∷ s))}{s}) ⟩
    subeq s (uf (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g y) (proj₂ (inj∷ a'))))
    ≡⟨ cong (subeq s) (sym (ccutuf2 ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g y) a' (proj₂ (inj∷ a')))) ⟩
    subeq s (ccut (A ∷ (Δ₀ ++ Γ₁) ++ Δ₁) f₂ (uf (ccut Δ₀ f₁ g y)) a')
    ∎
  ccutccut Δ₀ f₁ f₂ Ir r r' a a' s = {!!} --imp
  ccutccut Δ₀ {Δ₁ = Δ₁}{A₁ = A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁) r r' a a' s with lemma++ (Δ₀ ++ A₁ ∷ Δ₁) Γ r | lemma++ Δ₀ Γ r'
  ccutccut {Γ₁ = Γ₁}{Γ₂} Δ₀ {Δ₁ = Δ₁} {A₁ = A₁}{A₂} f₁ f₂ (⊗r {Γ = .((Δ₀ ++ A₁ ∷ Δ₁) ++ _ ∷ Γ₀)}{Δ} g g₁) r r' a a' s | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , x , y) with lemma++' (Δ₁ ++ A₂ ∷ Γ₀) Γ₀' (trans (++ass Δ₁) y)
  ccutccut {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₁ = Δ₁} {A₁ = A₁} {A₂} f₁ f₂ (⊗r {_} {.((Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Γ₀)} {Δ} g g₁) r r' a a' s | inj₁ (Γ₀ , refl , refl) | inj₁ (.(Δ₁ ++ A₂ ∷ Γ₀) , x , y) | refl = {!!}
--    begin
--    ccut Δ₀ f₁ (subeq (++ass ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂)) (⊗r (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g refl) g₁)) a
--    ≡⟨ {!ccut⊗r!} ⟩
--    subeq s (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ {!!} a')
--    ≡⟨ cong (subeq s) (cong (λ q → ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ q a') (ccut⊗r' Δ₀ {f₁ = f₁}{g}{g₁} x r')) ⟩ --(ccut⊗r Δ₀ {{!!}} {h = f₁}{g}{g₁} (trans x {!!}) r')) ⟩
--    subeq s (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ _ r') a')
--    ∎
--    where
--      test : subeq (++ass (Δ₀ ++ Γ₁)) (⊗r (ccut Δ₀ f₁ g x) g₁) ≡ ccut Δ₀ f₁ (⊗r g g₁) (trans r' (cong (_++_ Δ₀) (cong (_∷_ A₁) (sym (++ass Δ₁)))))
--      test = ccut⊗r Δ₀ {Δ₁ ++ A₂ ∷ Γ₀}{h = f₁}{g}{g₁} x (trans r' (cong (_++_ Δ₀) (cong (_∷_ A₁) (sym (++ass Δ₁)))))
  ccutccut Δ₀ {Δ₁ = Δ₁} {A₁ = A₁} f₁ f₂ (⊗r {Γ = .((Δ₀ ++ A₁ ∷ Δ₁) ++ _ ∷ Γ₀)} g g₁) r r' a a' s | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , x , y) = {!!}
  ccutccut Δ₀ {Δ₁ = Δ₁} {A₁ = A₁} f₁ f₂ (⊗r {Γ = Γ} g g₁) r r' a a' s | inj₂ (Γ₀ , x , x') | y = {!!}
  ccutccut Δ₀ f₁ f₂ (Il g) r r' a a' s = {!!}
  ccutccut Δ₀ f₁ f₂ (⊗l g) r r' a a' s = {!!}

-- ((Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Γ₀) ++ Δ ≡ Δ₀ ++ A₁ ∷ (Δ₁ ++ A₂ ∷ Γ₀) ++ Δ
-- ((Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Γ₀) ++ Δ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Γ₀ ++ Δ
{-
  ccutccut : {T : Maybe Tm} → {Γ₁ Γ₂ : List Tm} → (Δ₀ : List Tm) → {Δ Δ₁ Δ₂ : List Tm} → {A₁ A₂ C : Tm}
    → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
    → (r : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
    → ccut Δ₀ f₁ (subeq (cong (λ a → a ++ Δ₂) (++ass Δ₀)) (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r)) (++ass Δ₀) ≡
      subeq (trans (cong (λ a → a ++ Δ₂) (++ass (Δ₀ ++ Γ₁))) (++ass (Δ₀ ++ Γ₁))) (ccut ((Δ₀ ++ Γ₁) ++ Δ₁) f₂ (ccut Δ₀ f₁ g (trans r (++ass Δ₀))) (sym (++ass (Δ₀ ++ Γ₁))))
  ccutccut Δ₀ f₁ f₂ ax r = {!!} --imp
  ccutccut Δ₀ {Δ₁ = Δ₁}{A₁ = A₁} f₁ f₂ (uf g) r with lemma∷ (Δ₀ ++ A₁ ∷ Δ₁) r | lemma∷ Δ₀ (trans r (++ass Δ₀))
  ... | inj₁ (Γ₀ , a , b) | inj₁ (Γ₀' , x , y) = {!!}  --imp
  ... | inj₁ (Γ₀ , a , b) | inj₂ (Γ₀' , x , y) = {!!}  --imp
  ccutccut {Γ₁ = Γ₁} .[] {Δ₁ = .Γ₀}{Δ₂} {A₁ = _} f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) =
    begin
    scut f₁ (ccut Γ₀ f₂ g refl)
    ≡⟨ {!ccutscut!} ⟩
    subeq (trans (cong (λ a → a ++ Δ₂) (++ass Γ₁)) (++ass Γ₁)) (ccut (Γ₁ ++ Γ₀) f₂ (scut f₁ g) (sym (++ass Γ₁)))
    ∎
  ccutccut .(_ ∷ Γ₀') {Δ₁ = Δ₁} {A₁ = A₁} f₁ f₂ (uf g) r | inj₂ (Γ₀ , refl , b) | inj₂ (Γ₀' , x , refl) with inj∷ b
  ccutccut {Γ₁ = Γ₁} .(_ ∷ Γ₀') {Δ₁ = Δ₁}{Δ₂} {A₁ = A₁}{A₂} f₁ f₂ (uf {A = A} g) r | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , x , refl) | refl , refl
    with lemma∷ (A ∷ (Γ₀' ++ Γ₁) ++ Δ₁) {Δ₂}{(Γ₀' ++ Γ₁) ++ Δ₁ ++ A₂ ∷ Δ₂}  (sym (cong (_∷_ A) (++ass (Γ₀' ++ Γ₁))))
  ccutccut {Γ₁ = Γ₁} .(A ∷ Γ₀') {Δ₁ = Δ₁} {Δ₂} {A₁} {.A} f₁ f₂ (uf {A = A} g) r | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , x , refl) | refl , refl | inj₁ (refl , () , _)
  ccutccut {Γ₁ = Γ₁} .(A ∷ Γ₀') {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (uf {A = A} g) r | inj₂ (.(Γ₀' ++ A₁ ∷ Δ₁) , refl , refl) | inj₂ (Γ₀' , x , refl) | refl , refl | inj₂ (.((Γ₀' ++ Γ₁) ++ Δ₁) , y , refl) =
    begin
    ccut (A ∷ Γ₀') f₁ (subeq (cong (λ a → a ++ Δ₂) (cong (_∷_ A) (++ass Γ₀'))) (uf (ccut (Γ₀' ++ A₁ ∷ Δ₁) f₂ g refl))) (cong (_∷_ A) (++ass Γ₀'))
    ≡⟨ {!x!} ⟩
    subeq (trans (cong (λ a → a ++ Δ₂) (cong (_∷_ A) (++ass (Γ₀' ++ Γ₁)))) (cong (_∷_ A) (++ass (Γ₀' ++ Γ₁)))) (uf (ccut ((Γ₀' ++ Γ₁) ++ Δ₁) f₂ (ccut Γ₀' f₁ g x) y))
    ∎
  ccutccut Δ₀ f₁ f₂ Ir r = {!!}  --imp
  ccutccut Δ₀ f₁ f₂ (⊗r g g₁) r = {!!}
  ccutccut Δ₀ f₁ f₂ (Il g) r = {!!}
  ccutccut Δ₀ f₁ f₂ (⊗l g) r = {!!}
-}

{-
  ccutccut : {T : Maybe Tm} → {Γ₁ Γ₂ Δ : List Tm} → (Δ₀ : List Tm) → {Λ Λ' Δ' Δ₁ Δ₂ : List Tm} → {A₁ A₂ C : Tm}
    → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
    → (p : Δ ≡ Δ' ++ A₂ ∷ Δ₂)
    → (p' : Δ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Δ₂)
    → (q : Λ ≡ (Δ₀ ++ Γ₁) ++ Δ₁ ++ A₂ ∷ Δ₂)
    → (q' : Λ' ≡ (Δ' ++ Γ₂) ++ Δ₂)
    → (r : Λ ≡ Δ' ++ A₂ ∷ Δ₂)
    → (r' : Λ' ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ Γ₂ ++ Δ₂)
    → (s : (Δ' ++ Γ₂) ++ Δ₂ ≡ (Δ₀ ++ Γ₁) ++ Δ₁ ++ Γ₂ ++ Δ₂)
    → (h₁ : T ∣ Λ ⊢ C)(h₂ : T ∣ Λ' ⊢ C)
    → subeq q h₁ ≡ ccut Δ₀ f₁ g p'
    → subeq q' h₂ ≡ ccut Δ' f₂ g p
    → ccut Δ₀ f₁ h₂ r' ≡ subeq s (ccut Δ' f₂ h₁ r)
{-    
    → (p : (Δ₀ ++ Γ₁) ++ Δ₁ ++ A₂ ∷ Δ₂ ≡ ((Δ₀ ++ Γ₁) ++ Δ₁) ++ A₂ ∷ Δ₂)
    → (r : Δ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Δ₂)(t : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
    → (q : ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Δ₂ ≡ Δ₀ ++ A₁ ∷ (Δ₁ ++ Γ₂) ++ Δ₂)
    → (s : (((Δ₀ ++ Γ₁) ++ Δ₁) ++ Γ₂) ++ Δ₂ ≡ (Δ₀ ++ Γ₁) ++ (Δ₁ ++ Γ₂) ++ Δ₂)
    → ccut Δ₀ {Δ' = (Δ₁ ++ Γ₂) ++ Δ₂} f₁ (ccut Δ' f₂ g p) (trans (++ass Δ') (trans (cong (λ a → a ++ Γ₂ ++ Δ₂) q) (trans (++ass Δ₀) (cong (_++_ Δ₀) (sym (++ass (A₁ ∷ Δ₁))))))) ≡
      subeq (trans (++ass Δ'') (trans (cong (λ a → a ++ Γ₂ ++ Δ₂) r) (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym (++ass Δ₁))))))
        (ccut Δ'' {Δ' = Δ₂} f₂ (ccut Δ₀ f₁ g (trans p (trans (cong (λ a → a ++ A₂ ∷ Δ₂) q) (++ass Δ₀)))) (trans (sym (++ass (Δ₀ ++ Γ₁))) (cong (λ a → a ++ A₂ ∷ Δ₂) (sym r))))
-}
  ccutccut Δ₀ f₁ f₂ g p p' q q' r r' s h₁ h₂ t t' = {!h₂!}
-}
{-
  ccutccut : {T : Maybe Tm} → {Γ₁ Γ₂ Δ : List Tm} → (Δ₀ : List Tm) → {Δ' Δ'' Δ₁ Δ₂ : List Tm} → {A₁ A₂ C : Tm}
    → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
{-    
    → (p : (Δ₀ ++ Γ₁) ++ Δ₁ ++ A₂ ∷ Δ₂ ≡ ((Δ₀ ++ Γ₁) ++ Δ₁) ++ A₂ ∷ Δ₂)
    → (r : Δ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Δ₂)(t : Δ ≡ (Δ₀ ++ A₁ ∷ Δ₁) ++ A₂ ∷ Δ₂)
    → (q : ((Δ₀ ++ A₁ ∷ Δ₁) ++ Γ₂) ++ Δ₂ ≡ Δ₀ ++ A₁ ∷ (Δ₁ ++ Γ₂) ++ Δ₂)
    → (s : (((Δ₀ ++ Γ₁) ++ Δ₁) ++ Γ₂) ++ Δ₂ ≡ (Δ₀ ++ Γ₁) ++ (Δ₁ ++ Γ₂) ++ Δ₂)
-}
    → (p : Δ ≡ Δ' ++ A₂ ∷ Δ₂)
    → (q : Δ' ≡ Δ₀ ++ A₁ ∷ Δ₁)
    → (r : Δ'' ≡ (Δ₀ ++ Γ₁) ++ Δ₁)
    → ccut Δ₀ {Δ' = (Δ₁ ++ Γ₂) ++ Δ₂} f₁ (ccut Δ' f₂ g p) (trans (++ass Δ') (trans (cong (λ a → a ++ Γ₂ ++ Δ₂) q) (trans (++ass Δ₀) (cong (_++_ Δ₀) (sym (++ass (A₁ ∷ Δ₁))))))) ≡
      subeq (trans (++ass Δ'') (trans (cong (λ a → a ++ Γ₂ ++ Δ₂) r) (trans (++ass (Δ₀ ++ Γ₁)) (cong (_++_ (Δ₀ ++ Γ₁)) (sym (++ass Δ₁))))))
        (ccut Δ'' {Δ' = Δ₂} f₂ (ccut Δ₀ f₁ g (trans p (trans (cong (λ a → a ++ A₂ ∷ Δ₂) q) (++ass Δ₀)))) (trans (sym (++ass (Δ₀ ++ Γ₁))) (cong (λ a → a ++ A₂ ∷ Δ₂) (sym r))))
  ccutccut Δ₀ f₁ f₂ ax p q r = {!!} --imp
  ccutccut Δ₀ f₁ f₂ (uf g) p q r = {!!}
  ccutccut Δ₀ f₁ f₂ Ir p q r = {!!} --imp
  ccutccut Δ₀ {Δ'}{Δ₂ = Δ₂}{A₂ = A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁) p q r
    with lemma++ Δ' Γ p | lemma++ Δ₀ Γ (trans p (trans (cong (λ a → a ++ A₂ ∷ Δ₂) q) (++ass Δ₀)))
  ccutccut Δ₀ {Δ'} {Δ₂ = .(Γ₀ ++ _)} {A₂ = A₂} f₁ f₂ (⊗r {Γ = .(Δ' ++ A₂ ∷ Γ₀)} g g₁) p q r | inj₁ (Γ₀ , refl , refl) | inj₁ (Γ₀' , x , y) = {!!}
  ccutccut Δ₀ {Δ'} {Δ₂ = Δ₂} {A₂ = A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁) p q r | inj₁ (Γ₀ , x , y) | inj₂ y₁ = {!!}
  ccutccut Δ₀ {Δ'} {Δ₂ = Δ₂} {A₂ = A₂} f₁ f₂ (⊗r {Γ = Γ} g g₁) p q r
    | inj₂ (Γ₀ , x , y) | b = {!!}
  ccutccut Δ₀ f₁ f₂ (Il g) p q r = {!!}
  ccutccut Δ₀ f₁ f₂ (⊗l g) p q r = {!!}
-}

{-
  ccutscut : {T : Maybe Tm} → {Γ Δ : List Tm} → (Δ₀ : List Tm) → {Δ' Δ'' : List Tm} → {A B C : Tm}
    → (f : nothing ∣ Γ ⊢ A)(g : T ∣ Δ ⊢ B)(h : just B ∣ Δ'' ⊢ C)
    → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
    → ccut Δ₀ f (scut g h) (trans (cong (λ a → a ++ Δ'') r) (++ass Δ₀)) ≡
      subeq (++ass (Δ₀ ++ Γ)) (scut (ccut Δ₀ f g r) h)
  ccutscut Δ₀ f ax h r = ⊥-elim (lemma[] Δ₀ r)
  ccutscut Δ₀ {Δ'' = Δ''} f (uf g) h r with lemma∷ Δ₀ r | lemma∷ Δ₀ (trans (cong (λ a₁ → a₁ ++ Δ'') r) (++ass Δ₀))
  ccutscut .[] {Δ'' = Δ''} f (uf g) h r | inj₁ (refl , refl , refl) | inj₁ (refl , refl , refl) = scutscut f g h
  ccutscut .[] {Δ'' = Δ''} f (uf g) h r | inj₁ (a , refl , c) | inj₂ (x , y , ())
  ccutscut .[] {Δ'' = Δ''} f (uf g) h r | inj₂ (a , b , ()) | inj₁ (x , refl , z)
  ccutscut {Γ = Γ} .(_ ∷ Γ₀) {Δ'' = Δ''} f (uf {A = A} g) h r | inj₂ (Γ₀ , refl , refl) | inj₂ (.Γ₀ , p , refl) = 
    begin
    uf (ccut Γ₀ f (scut g h) p)
    ≡⟨ cong uf (cong (ccut Γ₀ f (scut g h)) uip) ⟩
    uf (ccut Γ₀ f (scut g h) (++ass Γ₀))
    ≡⟨ cong uf (ccutscut Γ₀ f g h refl) ⟩
    uf (subeq (++ass (Γ₀ ++ Γ)) (scut (ccut Γ₀ f g refl) h))
    ≡⟨ sym (subequf (++ass (Γ₀ ++ Γ))) ⟩
    subeq (cong (_∷_ A) (++ass (Γ₀ ++ Γ))) (uf (scut (ccut Γ₀ f g refl) h))
    ∎
  ccutscut Δ₀ f Ir h r = ⊥-elim (lemma[] Δ₀ r)
  ccutscut {Γ = Γ} Δ₀ f (⊗r {Γ = Γ'} g g') h r with lemma++ Δ₀ Γ' r 
  ccutscut {Γ = Γ} Δ₀ {Δ'' = Δ''}{A} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} g g') h r | inj₁ (Γ₀ , refl , refl) = 
    begin
    ccut Δ₀ f (ccut (Δ₀ ++ A ∷ Γ₀) g' (scut g (⊗l-1 h)) refl) (trans (cong (λ a → a ++ Δ'') r) (++ass Δ₀))
    ≡⟨ {!!} ⟩
    subeq (++ass (Δ₀ ++ Γ)) (subeq (cong (λ a → a ++ Δ'') (++ass (Δ₀ ++ Γ))) (ccut ((Δ₀ ++ Γ) ++ Γ₀) g' (ccut Δ₀ f (scut g (⊗l-1 h)) (++ass Δ₀)) (trans (sym (++ass (Δ₀ ++ Γ))) refl)))
    ≡⟨ cong (subeq (++ass (Δ₀ ++ Γ))) (cong (subeq (cong (λ a → a ++ Δ'') (++ass (Δ₀ ++ Γ)))) (cong (λ a → ccut ((Δ₀ ++ Γ) ++ Γ₀) g' a (trans (sym (++ass (Δ₀ ++ Γ))) refl)) (ccutscut Δ₀ f g (⊗l-1 h) refl))) ⟩
    subeq (++ass (Δ₀ ++ Γ)) (subeq (cong (λ a → a ++ Δ'') (++ass (Δ₀ ++ Γ))) (ccut ((Δ₀ ++ Γ) ++ Γ₀) g' (subeq (++ass (Δ₀ ++ Γ)) (scut (ccut Δ₀ f g refl) (⊗l-1 h))) (trans (sym (++ass (Δ₀ ++ Γ))) refl)))
    ≡⟨ cong (subeq (++ass (Δ₀ ++ Γ))) (cong (subeq (cong (λ a → a ++ Δ'') (++ass (Δ₀ ++ Γ)))) (sym (ccutsubeq2 ((Δ₀ ++ Γ) ++ Γ₀) g' {scut (ccut Δ₀ f g refl) (⊗l-1 h)} refl (++ass (Δ₀ ++ Γ))))) ⟩
    subeq (++ass (Δ₀ ++ Γ)) (subeq (cong (λ a → a ++ Δ'') (++ass (Δ₀ ++ Γ))) (ccut ((Δ₀ ++ Γ) ++ Γ₀) g' (scut (ccut Δ₀ f g refl) (⊗l-1 h)) refl))
    ≡⟨ sym (cong (subeq (++ass (Δ₀ ++ Γ))) (scutsubeq2 (⊗r (ccut Δ₀ f g refl) g') h (++ass (Δ₀ ++ Γ)))) ⟩
    subeq (++ass (Δ₀ ++ Γ)) (scut (subeq (++ass (Δ₀ ++ Γ)) (⊗r (ccut Δ₀ f g refl) g')) h)
    ∎
  ccutscut {Γ = Γ} .(Γ' ++ Γ₀) f (⊗r {Γ = Γ'} g g') h r | inj₂ (Γ₀ , refl , refl) = {!!}
  ccutscut {Γ = Γ} Δ₀ {Δ'' = Δ''} f (Il g) h r =
    begin
    Il (ccut Δ₀ f (scut g h) (trans (cong (λ a → a ++ Δ'') r) (++ass Δ₀)))
    ≡⟨ cong Il (ccutscut Δ₀ f g h r) ⟩
    Il (subeq (++ass (Δ₀ ++ Γ)) (scut (ccut Δ₀ f g r) h))
    ≡⟨ sym (subeqIl (++ass (Δ₀ ++ Γ))) ⟩
    subeq (++ass (Δ₀ ++ Γ)) (Il (scut (ccut Δ₀ f g r) h))
    ∎
  ccutscut {Γ = Γ} Δ₀ {Δ'' = Δ''} f (⊗l {B = B} g) h r =
    begin
    ⊗l (ccut (B ∷ Δ₀) f (scut g h) (cong (_∷_ B) (trans (cong (λ a → a ++ Δ'') r) (++ass Δ₀))))
    ≡⟨ cong ⊗l (cong (ccut (B ∷ Δ₀) f (scut g h)) uip ) ⟩
    ⊗l (ccut (B ∷ Δ₀) f (scut g h) (trans (cong (λ a → a ++ Δ'') (cong (_∷_ B) r)) (++ass (B ∷ Δ₀))))
    ≡⟨ cong ⊗l (ccutscut (B ∷ Δ₀) f g h (cong (_∷_ B) r)) ⟩
    ⊗l (subeq (++ass ((B ∷ Δ₀) ++ Γ)) (scut (ccut (B ∷ Δ₀) f g (cong (_∷_ B) r)) h))
    ≡⟨ sym (subeq⊗l (++ass (Δ₀ ++ Γ))) ⟩
    subeq (++ass (Δ₀ ++ Γ)) (⊗l (scut (ccut (B ∷ Δ₀) f g (cong (_∷_ B) r)) h))
    ∎

  scutscut : {S : Maybe Tm} → {Γ Δ Δ' : List Tm} → {A B C : Tm}
    → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
    → scut f (scut g h) ≡ subeq (++ass Γ) (scut (scut f g) h)
  scutscut ax g h = refl
  scutscut (uf {Γ}{A} f) g h =
    begin
    uf (scut f (scut g h))
    ≡⟨ cong uf (scutscut f g h) ⟩
    uf (subeq (++ass Γ) (scut (scut f g) h))
    ≡⟨ sym (subequf (++ass Γ)) ⟩
    subeq (cong (_∷_ A) (++ass Γ)) (uf (scut (scut f g) h))
    ∎
  scutscut Ir g h = scutIl-1 g h
  scutscut (⊗r {Γ = Γ}{Δ} f f') g h =
    begin
    ccut Γ f' (scut f (⊗l-1 (scut g h))) refl
    ≡⟨ cong (λ a → ccut Γ f' (scut f a) refl) (scut⊗l-1 g h) ⟩
    ccut Γ f' (scut f (scut (⊗l-1 g) h)) refl
    ≡⟨ cong (λ a → ccut Γ f' a refl) (scutscut f (⊗l-1 g) h) ⟩
    ccut Γ f' (subeq (++ass Γ) (scut (scut f (⊗l-1 g)) h)) refl
    ≡⟨ ccutsubeq Γ f' {scut (scut f (⊗l-1 g)) h} refl (++ass Γ) ⟩
    ccut Γ f' (scut (scut f (⊗l-1 g)) h) (trans (++ass Γ) refl)
    ≡⟨ cong (ccut Γ f' (scut (scut f (⊗l-1 g)) h)) uip ⟩
    ccut Γ f' (scut (scut f (⊗l-1 g)) h) (++ass Γ)
    ≡⟨ ccutscut Γ f' (scut f (⊗l-1 g)) h refl  ⟩
    subeq (++ass (Γ ++ Δ)) (scut (ccut Γ f' (scut f (⊗l-1 g)) refl) h)
    ∎
  scutscut {Γ = Γ} (Il f) g h =
    begin
    Il (scut f (scut g h))
    ≡⟨ cong Il (scutscut f g h) ⟩
    Il (subeq (++ass Γ) (scut (scut f g) h))
    ≡⟨ sym (subeqIl (++ass Γ)) ⟩
    subeq (++ass Γ) (Il (scut (scut f g) h))
    ∎
  scutscut {Γ = Γ} (⊗l {B = B} f) g h =
    begin
    ⊗l (scut f (scut g h))
    ≡⟨ cong ⊗l (scutscut f g h) ⟩
    ⊗l (subeq (++ass (B ∷ Γ)) (scut (scut f g) h))
    ≡⟨ sym (subeq⊗l (++ass Γ)) ⟩
    subeq (++ass Γ) (⊗l (scut (scut f g) h))
    ∎
-}







{-
mutual 
  scut : {S : Maybe Tm} → {Γ Δ' : List Tm} → {A C : Tm} → 
              S ∣ Γ ⊢ A  →  just A ∣ Δ' ⊢ C  →  S ∣ Γ ++ Δ' ⊢ C

  scut ax g = g
  scut (uf f) g = uf (scut f g)
  scut Ir g = Il-1 g
  scut (⊗r {S} {Γ} {Δ} f f') ax =  
          subeq (++ru (Γ ++ Δ)) (⊗r f f')
  scut (⊗r {S} {Γ} {Δ} f f') (⊗r g g') = 
          subeq (++ass (Γ ++ Δ)) (⊗r (scut (⊗r f f') g) g')
  scut (⊗r {S} {Γ} {Δ} f f') (⊗l g) = 
          ccut Γ f' (scut f g) refl
--ccut Γ f' (scut f (⊗l-1 g)) refl
  scut (Il f) g = Il (scut f g)
  scut (⊗l f) g = ⊗l (scut f g)


  ccut : {T : Maybe Tm} → {Γ Δ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} → {A C : Tm} → 
             nothing ∣ Γ ⊢ A  →  T ∣ Δ ⊢ C  → Δ ≡ Δ₀ ++ A ∷ Δ' →  
                                        T ∣ (Δ₀ ++ Γ) ++ Δ' ⊢ C
  
  ccut Δ₀ f ax p = ⊥-elim (lemma[] Δ₀ p)
  ccut Δ₀ f (uf g) p with lemma∷ Δ₀ p 
  ccut .[] f (uf g) p 
     | inj₁ (refl , refl , refl) = scut f g
  ccut .(_ ∷ Δ₀) f (uf g) p 
     | inj₂ (Δ₀ , r , refl) =  uf (ccut Δ₀ f g r)
  ccut Δ₀ f Ir p = ⊥-elim (lemma[] Δ₀ p)
  ccut Δ₀ f (⊗r {T} {Γ} {Γ'} g g') p with lemma++ Δ₀ Γ p 
  ccut Δ₀ f (⊗r {T} {.(Δ₀ ++ _)} {Γ'} g g') p 
     | inj₁ (Γ₀  , refl , refl) =  
                subeq (++ass (Δ₀ ++ _)) 
                      (⊗r (ccut Δ₀ f g refl) g')
  ccut .(Γ ++ Γ₀) f (⊗r {T} {Γ} g g') p 
     | inj₂ (Γ₀ , refl , refl) =  
                subeq (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))
                      (⊗r g (ccut Γ₀ f g' refl))
  ccut Δ₀ f (Il g) r = Il (ccut Δ₀ f g r) 
  ccut Δ₀ f (⊗l {B = B} g) r = ⊗l (ccut (B ∷ Δ₀) f g (cong (_∷_ B) r)) 

lemma++'' : {A : Set}{x : A}(xs ys : List A)
  → ys ≡ x ∷ xs ++ ys → ⊥
lemma++'' _ [] ()
lemma++'' [] (y ∷ ys) ()
lemma++'' (x ∷ xs) (y ∷ ys) p with inj∷ p
... | (refl , q) = lemma++'' (xs ++ y ∷ []) ys (trans q (sym (++ass (x ∷ xs))))

lemma++' : {A : Set}(xs xs' : List A){ys : List A} → xs ++ ys ≡ xs' ++ ys → xs ≡ xs'
lemma++' [] [] p = refl
lemma++' [] (x ∷ xs') {ys} p = ⊥-elim (lemma++'' xs' ys p)
lemma++' (x ∷ xs) [] {ys} p = ⊥-elim (lemma++'' xs ys (sym p))
lemma++' (x ∷ xs) (x₁ ∷ xs') p with inj∷ p
lemma++' (x ∷ xs) (.x ∷ xs') p | refl , q = cong (_∷_ x) (lemma++' xs xs' q)

lemma++'2 : {A : Set}{xs xs' : List A}(ys : List A) → ys ++ xs ≡ ys ++ xs' → xs ≡ xs'
lemma++'2 [] p = p
lemma++'2 (x ∷ ys) p with inj∷ p
... | (refl , q) = lemma++'2 ys q

{-
scutIr : {Γ : List Tm}{C : Tm} (f : just I ∣ Γ ⊢ C) → f ≈ Il (scut Ir f)
scutIr ax = axI
scutIr (⊗r f f₁) = trans≈ (cong⊗r (scutIr f) refl≈) ⊗rIl
scutIr (Il f) = refl≈
-}

subeq≈ : ∀{S}{Γ}{Γ'}{A}{f g : S ∣ Γ ⊢ A}
  → (p : Γ ≡ Γ') → f ≈ g
  → subeq p f ≈ subeq p g
subeq≈ refl r = r

ccutufax : {T : Maybe Tm} → {Γ Δ : List Tm} → (Δ₀ : List Tm) → {B C : Tm} → 
           (g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ B ∷ Γ) →  
           subeq (trans r (sym (++ass Δ₀))) g ≡ ccut Δ₀ (uf ax) g r
ccutufax Δ₀ ax r = ⊥-elim (lemma[] Δ₀ r)
ccutufax Δ₀ (uf f) r with lemma∷ Δ₀ r
ccutufax .[] (uf f) refl | inj₁ (refl , refl , refl) = refl
ccutufax .(_ ∷ Δ₀) (uf {A = A} f) refl | inj₂ (Δ₀ , refl , refl) =
  trans (trans (cong (λ a → subeq a (uf f)) (uip {p = sym (cong (_∷_ A) (++ass Δ₀))}{cong (_∷_ A) (sym (++ass Δ₀))})) (subequf (sym (++ass Δ₀))))
        (cong uf (ccutufax Δ₀ f refl))
ccutufax Δ₀ Ir r  = ⊥-elim (lemma[] Δ₀ r)
ccutufax Δ₀ (⊗r {Γ = Γ} f f') r with lemma++ Δ₀ Γ r
ccutufax Δ₀ {B} (⊗r {Γ = .(Δ₀ ++ _)}{Δ} f f') r | inj₁ (Γ₀ , refl , refl) =
  trans (trans (trans (cong (λ a → subeq a (⊗r f f')) (uip {p = trans r (sym (++ass Δ₀))}{trans (cong (λ a → a ++ Δ) (sym (++ass Δ₀))) (++ass (Δ₀ ++ B ∷ []))}))
                                (subeqtrans (cong (λ a → a ++ Δ) (sym (++ass Δ₀))) (++ass (Δ₀ ++ B ∷ []))))
               (cong (subeq (++ass (Δ₀ ++ B ∷ []))) (subeq⊗r (sym (++ass Δ₀)))))
         (cong (subeq (++ass (Δ₀ ++ B ∷ []))) (cong₂ ⊗r (ccutufax Δ₀ f refl) refl))
ccutufax .(Γ ++ Γ₀) (⊗r {Γ = Γ} f f') r | inj₂ (Γ₀ , refl , refl) = 
  trans (trans (trans (cong (λ a → subeq a (⊗r f f')) (uip {p = trans r (sym (++ass (Γ ++ Γ₀)))}
                                                            {trans (cong (_++_ Γ) (sym (++ass Γ₀))) (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))}))
                      (subeqtrans (cong (_++_ Γ) (sym (++ass Γ₀))) (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))))
               (cong (subeq (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))) (subeq⊗r2 (sym (++ass Γ₀)))))
        (cong (subeq (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))) (cong₂ ⊗r refl (ccutufax Γ₀ f' refl)))
ccutufax Δ₀ (Il f) refl =
  trans (subeqIl (sym (++ass Δ₀))) (cong Il (ccutufax Δ₀ f refl))
ccutufax Δ₀ (⊗l {B = B} f) refl =
  trans (trans (subeq⊗l (sym (++ass Δ₀))) (cong (λ a → ⊗l (subeq a f)) (uip {p = cong (_∷_ B) (sym (++ass Δ₀))}{sym (cong (_∷_ B) (++ass Δ₀))})))
        (cong ⊗l (ccutufax (B ∷ Δ₀) f refl))

{-
scutax : ∀{S}{Γ}{A}(f : S ∣ Γ ⊢ A) → scut f ax ≡ subeq (++ru Γ) f
scutax ax = refl
scutax (uf {Γ = Γ} f) = trans (cong uf (scutax f)) (sym (subequf (++ru Γ)))
scutax Ir = refl
scutax (⊗r f f₁) = refl
scutax {Γ = Γ} (Il f) = trans (cong Il (scutax f)) (sym (subeqIl (++ru Γ)))
scutax {Γ = Γ} (⊗l f) = trans (cong ⊗l (scutax f)) (sym (subeq⊗l (++ru Γ)))
-}

scutsubeq : {S : Maybe Tm} → {Γ Δ Δ' : List Tm} → {A B : Tm} → 
            (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(p : Δ ≡ Δ') → 
        scut f (subeq p g) ≡ subeq (cong (_++_ Γ) p) (scut f g)
scutsubeq f g refl = refl

scutsubeq2 : {S : Maybe Tm} → {Γ Δ Γ' : List Tm} → {A B : Tm} → 
            (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(p : Γ ≡ Γ') → 
        scut (subeq p f) g ≡ subeq (cong (λ a → a ++ Δ) p) (scut f g)
scutsubeq2 f g refl = refl

{-
scutass : {S : Maybe Tm} → {Γ Δ Δ' : List Tm} → {A B C : Tm}
  → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
  → scut f (scut g h) ≡ subeq (++ass Γ) (scut (scut f g) h)
scutass ax g h = refl
scutass (uf f) g h = {!!}
scutass Ir ax h = refl
scutass Ir (⊗r g g₁) ax = {!!}
scutass Ir (⊗r g g₁) (⊗r h h₁) = {!!}
scutass Ir (⊗r g g₁) (⊗l h) = {!!}
scutass Ir (Il g) h = refl
scutass (⊗r f f₁) g h = {!g!}
scutass (Il f) g h = {!!}
scutass (⊗l f) g h = {!!}
-}

{-
mutual
  scutassIr : ∀{Γ}{Δ}{Δ'}{A}{B}{C} → 
    (f : just I ∣ Γ ⊢ A)(g : nothing ∣ Δ ⊢ B)(h : just (A ⊗ B) ∣ Δ' ⊢ C) → 
    scut Ir (scut (⊗r f g) h) ≡ scut (⊗r (scut Ir f) g) h
  scutassIr {Γ}{Δ} f g ax =
    trans (scutsubeq Ir (⊗r f g) (++ru (Γ ++ Δ)))
          (cong (λ a → subeq a (⊗r (scut Ir f) g))
                (uip {p = cong (λ ys → ys) (++ru (Γ ++ Δ))}{++ru (Γ ++ Δ)}))
  scutassIr {Γ}{Δ} f g (⊗r h h₁) =
    trans (trans (scutsubeq Ir (⊗r (scut (⊗r f g) h) h₁) (++ass (Γ ++ Δ)))
                 (cong (λ a → subeq a (⊗r (scut Ir (scut (⊗r f g) h)) h₁)) (uip {p = cong (λ ys → ys) (++ass (Γ ++ Δ))}{++ass (Γ ++ Δ)})))
          (cong (subeq (++ass (Γ ++ Δ))) (cong₂ ⊗r (scutassIr f g h) refl))
  scutassIr f g (⊗l h) = scutccutass g f h refl
-}


ccutIl-1 : ∀{Γ}{Δ}{A}{C} Δ₀ {Δ'}
  → (f : nothing ∣ Γ ⊢ A)(g : just I ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → Il-1 (ccut Δ₀ f g r) ≡ ccut Δ₀ f (Il-1 g) r
ccutIl-1 Δ₀ f ax r = ⊥-elim (lemma[] Δ₀ r)
ccutIl-1 Δ₀ f (⊗r {Γ = Γ}{Δ}  g g₁) r with lemma++ Δ₀ Γ r
ccutIl-1 {Γ} Δ₀ f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) r | inj₁ (Γ₀ , refl , refl) =
  trans (sym (subeqIl-1 (++ass (Δ₀ ++ Γ)) ))
        (cong (λ a → subeq (++ass (Δ₀ ++ Γ)) (⊗r a g₁)) (ccutIl-1 Δ₀ f g refl))
ccutIl-1 .(Γ ++ Γ₀) f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ _)} g g₁) r | inj₂ (Γ₀ , refl , refl) =
  sym (subeqIl-1 (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)))
ccutIl-1 Δ₀ f (Il g) r = refl

scutIl-1 : {Γ Δ : List Tm} → {A C : Tm}
  → (f : just I ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ C)
  → Il-1 (scut f g) ≡ scut (Il-1 f) g
scutIl-1 ax g = refl
scutIl-1 (⊗r {Γ = Γ}{Δ} f f₁) ax = sym (subeqIl-1 (++ru (Γ ++ Δ)))
scutIl-1 (⊗r {Γ = Γ}{Δ} f f₁) (⊗r g g₁) =
  begin
  Il-1 (subeq (++ass (Γ ++ Δ)) (⊗r (scut (⊗r f f₁) g) g₁))
  ≡⟨ sym (subeqIl-1 (++ass (Γ ++ Δ))) ⟩
  subeq (++ass (Γ ++ Δ)) (⊗r (Il-1 (scut (⊗r f f₁) g)) g₁)
  ≡⟨ cong (subeq (++ass (Γ ++ Δ))) (cong (λ a → ⊗r a g₁) (scutIl-1 (⊗r f f₁) g)) ⟩
  subeq (++ass (Γ ++ Δ)) (⊗r (scut (⊗r (Il-1 f) f₁) g) g₁)
  ∎
scutIl-1 (⊗r {Γ = Γ}{Δ} f f₁) (⊗l g) =
  begin
  Il-1 (ccut Γ f₁ (scut f g) refl)
  ≡⟨ ccutIl-1 Γ f₁ (scut f g) refl ⟩
  ccut Γ f₁ (Il-1 (scut f g)) refl
  ≡⟨ cong (λ a → ccut Γ f₁ a refl) (scutIl-1 f g) ⟩
  ccut Γ f₁ (scut (Il-1 f) g) refl
  ∎
scutIl-1 (Il f) g = refl

scutccutass : ∀{Γ}{Δ}{Δ'}{Δ''}{A}{B}{C}
  (g : nothing ∣ Δ ⊢ B)(f : just I ∣ Γ ⊢ A)(h : just A ∣ Δ' ⊢ C)(r : Γ ++ Δ' ≡ Γ ++ B ∷ Δ'') → 
  scut Ir (ccut Γ g (scut f h) r) ≡ ccut Γ g (scut (scut Ir f) h) r
scutccutass g ax ax ()
scutccutass g ax (⊗r {Γ = Γ} h h₁) r with lemma++ [] Γ r
scutccutass {Δ = Δ} g ax (⊗r {Γ = .(_ ∷ Γ₀)} h h₁) r | inj₁ (Γ₀ , refl , refl) =
  trans (scutsubeq Ir (⊗r (ccut [] g h refl) h₁) (++ass Δ))
        (cong₂ subeq (uip {p = cong (λ ys → ys) (++ass Δ)} {++ass Δ}) (cong₂ ⊗r (ccutIl-1 [] g h refl) refl))
scutccutass g ax (⊗r {Γ = []} h h₁) r | inj₂ (.[] , refl , refl) = refl
scutccutass g ax (⊗r {Γ = x ∷ Γ} h h₁) r | inj₂ (Γ₀ , refl , ())
scutccutass g ax (Il h) r = refl
scutccutass {Δ'' = Δ''} g (⊗r {Γ = Γ}{Δ} f f₁) ax r = ⊥-elim (lemma[] [] (lemma++'2 (Γ ++ Δ) r))
scutccutass g (⊗r {Γ = Γ}{Δ} f f₁) (⊗r h h₁) r =
  begin
  Il-1 (ccut (Γ ++ Δ) g (subeq (++ass (Γ ++ Δ)) (⊗r (scut (⊗r f f₁) h) h₁)) r)
  ≡⟨ ccutIl-1 (Γ ++ Δ) g (subeq (++ass (Γ ++ Δ)) (⊗r (scut (⊗r f f₁) h) h₁)) r ⟩
  ccut (Γ ++ Δ) g (Il-1 (subeq (++ass (Γ ++ Δ)) (⊗r (scut (⊗r f f₁) h) h₁))) r
  ≡⟨ cong (λ a → ccut (Γ ++ Δ) g a r) (sym (subeqIl-1 (++ass (Γ ++ Δ)))) ⟩
  ccut (Γ ++ Δ) g (subeq (++ass (Γ ++ Δ)) (Il-1 (⊗r (scut (⊗r f f₁) h) h₁))) r
  ≡⟨ cong (λ a → ccut (Γ ++ Δ) g (subeq (++ass (Γ ++ Δ)) a) r) (cong (λ a → ⊗r a h₁) (scutIl-1 (⊗r f f₁) h)) ⟩
  ccut (Γ ++ Δ) g (subeq (++ass (Γ ++ Δ)) (⊗r (scut (⊗r (Il-1 f) f₁) h) h₁)) r
  ∎
scutccutass g (⊗r {Γ = Γ}{Δ} f f₁) (⊗l h) r =
  begin
  Il-1 (ccut (Γ ++ Δ) g (ccut Γ f₁ (scut f h) refl) r)
  ≡⟨ ccutIl-1 (Γ ++ Δ) g (ccut Γ f₁ (scut f h) refl) r ⟩
  ccut (Γ ++ Δ) g (Il-1 (ccut Γ f₁ (scut f h) refl)) r
  ≡⟨ cong (λ a → ccut (Γ ++ Δ) g a r) (scutccutass f₁ f h refl) ⟩
  ccut (Γ ++ Δ) g (ccut Γ f₁ (scut (scut Ir f) h) refl) r
  ∎
scutccutass g (Il f) h r = refl


scut⊗rax : {Γ : List Tm}{A B C : Tm}(f : just (A ⊗ B) ∣ Γ ⊢ C) → f ≈ ⊗l (scut (⊗r ax (uf ax)) f)
scut⊗rax ax = ax⊗
scut⊗rax (⊗r f f₁) = trans≈ (cong⊗r (scut⊗rax f) refl≈) ⊗r⊗l
scut⊗rax (⊗l f) = cong⊗l (refl≈' (ccutufax [] f refl))

scut⊗ruf : {Γ Δ Δ' : List Tm}{A A' B C : Tm}
  → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (f' : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (uf f) g) f' ≈ uf (scut (⊗r f g) f')
scut⊗ruf {Γ}{Δ}{A' = A'} ax =
  trans≈ (subeq≈ (cong (_∷_ A') (++ru (Γ ++ Δ))) ⊗ruf)
         (refl≈' (subequf (++ru (Γ ++ Δ))))
scut⊗ruf {Γ}{Δ}{A' = A'} (⊗r f' f'') =
  trans≈ (subeq≈ (cong (_∷_ A') (++ass (Γ ++ Δ))) (cong⊗r (scut⊗ruf f') refl≈))
         (trans≈ (subeq≈ (cong (_∷_ A') (++ass (Γ ++ Δ))) ⊗ruf)
                 (refl≈' (subequf (++ass (Γ ++ Δ)))))
scut⊗ruf {Γ}{Δ}{Δ'}{A' = A'}{B} (⊗l f') with lemma∷ (A' ∷ Γ){Δ'}{_}{B} refl
scut⊗ruf {Γ} {Δ} {Δ'} {A' = A'} {B} (⊗l f') | inj₁ (_ , () , _)
scut⊗ruf {._} {Δ} {Δ'} {A' = A'} {B} (⊗l f') | inj₂ (_ , refl , refl) = refl≈

scut⊗rIl : {Γ Δ Δ' : List Tm}{A B C : Tm}
  → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (Il f) g) h ≈ Il (scut (⊗r f g) h)
scut⊗rIl {Γ}{Δ} ax =
  trans≈ (subeq≈ (++ru (Γ ++ Δ)) ⊗rIl)
         (refl≈' (subeqIl (++ru (Γ ++ Δ))))
scut⊗rIl {Γ}{Δ} (⊗r h h₁) =
  trans≈ (subeq≈ (++ass (Γ ++ Δ)) (trans≈ (cong⊗r (scut⊗rIl h) refl≈) ⊗rIl))
         (refl≈' (subeqIl (++ass (Γ ++ Δ))))
scut⊗rIl (⊗l h) = refl≈  

scut⊗r⊗l : {Γ Δ Δ' : List Tm}{A A' B B' C : Tm}
  → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (⊗l f) g) h ≈ ⊗l (scut (⊗r f g) h)
scut⊗r⊗l {Γ}{Δ} ax =
  trans≈ (subeq≈ (++ru (Γ ++ Δ)) ⊗r⊗l)
         (refl≈' (subeq⊗l (++ru (Γ ++ Δ))))
scut⊗r⊗l {Γ}{Δ} (⊗r h h₁) = 
  trans≈ (subeq≈ (++ass (Γ ++ Δ)) (trans≈ (cong⊗r (scut⊗r⊗l h) refl≈) ⊗r⊗l))
         (refl≈' (subeq⊗l (++ass (Γ ++ Δ))))
scut⊗r⊗l (⊗l h) = refl≈

scutass : {S : Maybe Tm} → {Γ Δ Δ' : List Tm} → {A B C : Tm} → 
            (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C) →
 scut f (scut g h) ≡ subeq (++ass Γ) (scut (scut f g) h)
scutass ax g h = refl
scutass (uf {Γ} f) g h = trans (cong uf (scutass f g h)) (sym (subequf (++ass Γ)))
scutass Ir ax h = refl
scutass Ir (⊗r {Γ = Γ}{Δ} f g) ax =
  trans (scutsubeq Ir (⊗r f g) (++ru (Γ ++ Δ)))
        (cong (λ a → subeq a (⊗r (scut Ir f) g)) (uip {p = cong (λ ys → ys) (++ru (Γ ++ Δ))}{++ru (Γ ++ Δ)}))
scutass Ir (⊗r {Γ = Γ}{Δ} f g) (⊗r h h₁) =
  trans (trans (scutsubeq Ir (⊗r (scut (⊗r f g) h) h₁) (++ass (Γ ++ Δ)))
               (cong (λ a → subeq a (⊗r (scut Ir (scut (⊗r f g) h)) h₁)) (uip {p = cong (λ ys → ys) (++ass (Γ ++ Δ))}{++ass (Γ ++ Δ)})))
        (cong (subeq (++ass (Γ ++ Δ))) (cong₂ ⊗r (scutass Ir (⊗r f g) h) refl))
scutass Ir (⊗r {Γ = Γ} g g₁) (⊗l h) =
  begin
  Il-1 (ccut Γ g₁ (scut g h) refl)
  ≡⟨ ccutIl-1 Γ g₁ (scut g h) refl ⟩
  ccut Γ g₁ (Il-1 (scut g h)) refl
  ≡⟨ cong (λ a → ccut Γ g₁ a refl) (scutIl-1 g h) ⟩
  ccut Γ g₁ (scut (Il-1 g) h) refl
  ∎
scutass Ir (Il g) h = refl
scutass {Δ' = Δ'} (⊗r {Γ = Γ}{Δ} f f₁) ax h =
  trans (trans (cong (λ a → subeq a (scut (⊗r f f₁) h)) (uip {p = refl}{trans (cong (λ a → a ++ Δ') (++ru (Γ ++ Δ))) (++ass (Γ ++ Δ))}))
               (subeqtrans (cong (λ a → a ++ Δ') (++ru (Γ ++ Δ))) (++ass (Γ ++ Δ))))
        (cong (subeq (++ass (Γ ++ Δ))) (sym (scutsubeq2 (⊗r f f₁) h (++ru (Γ ++ Δ)))))
scutass (⊗r {Γ = Γ} {Δ} f f₁) (⊗r {Γ = Γ'}{Δ'} g g₁) ax =
  trans (trans (scutsubeq (⊗r f f₁) (⊗r g g₁) (++ru (Γ' ++ Δ')))
               (trans (sym (subeqtrans (++ass (Γ ++ Δ)) (cong (_++_ (Γ ++ Δ)) (++ru (Γ' ++ Δ')))))
                      (cong (λ a → subeq a (⊗r (scut (⊗r f f₁) g) g₁)) (uip {p = trans (++ass (Γ ++ Δ)) (cong (_++_ (Γ ++ Δ)) (++ru (Γ' ++ Δ')))}
                                                                             {trans (trans (++ru (((Γ ++ Δ) ++ Γ') ++ Δ')) (cong (λ a → a ++ []) (++ass (Γ ++ Δ)))) (++ass (Γ ++ Δ))}))))
        (trans (trans (subeqtrans (trans (++ru (((Γ ++ Δ) ++ Γ') ++ Δ')) (cong (λ a → a ++ []) (++ass (Γ ++ Δ)))) (++ass (Γ ++ Δ)))
                      (cong (subeq (++ass (Γ ++ Δ))) (subeqtrans (++ru (((Γ ++ Δ) ++ Γ') ++ Δ')) (cong (λ a → a ++ []) (++ass (Γ ++ Δ))))))
               (cong (subeq (++ass (Γ ++ Δ))) (sym (scutsubeq2 (⊗r (scut (⊗r f f₁) g) g₁) ax (++ass (Γ ++ Δ))))))
scutass (⊗r {Γ = Γ} {Δ} f f₁) (⊗r {Γ = Γ'}{Δ'} g g₁) (⊗r {Γ = Γ''}{Δ''} h h₁) =
  trans (scutsubeq (⊗r f f₁) (⊗r (scut (⊗r g g₁) h) h₁) (++ass (Γ' ++ Δ')))
        (trans (trans (sym (subeqtrans {f = ⊗r (scut (⊗r f f₁) (scut (⊗r g g₁) h)) h₁} (++ass (Γ ++ Δ)) (cong (_++_ (Γ ++ Δ)) (++ass (Γ' ++ Δ')))))
                      (trans (cong (subeq (trans (++ass (Γ ++ Δ)) (cong (_++_ (Γ ++ Δ)) (++ass (Γ' ++ Δ'))))) (trans (cong₂ ⊗r (scutass (⊗r f f₁) (⊗r g g₁) h) refl)
                                                                                                                     (trans (sym (subeq⊗r (++ass (Γ ++ Δ))))
                                                                                                                            (cong (subeq (cong (λ a → a ++ Δ'') (++ass (Γ ++ Δ))))
                                                                                                                              (cong₂ ⊗r (scutsubeq2 (⊗r (scut (⊗r f f₁) g) g₁) h (++ass (Γ ++ Δ))) refl)))))
                                   (trans (trans (sym (subeqtrans {f = ⊗r (subeq (cong (λ a → a ++ Γ'') (++ass (Γ ++ Δ))) (scut (⊗r (scut (⊗r f f₁) g) g₁) h)) h₁}
                                                        (cong (λ a → a ++ Δ'') (++ass (Γ ++ Δ))) (trans (++ass (Γ ++ Δ)) (cong (_++_ (Γ ++ Δ)) (++ass (Γ' ++ Δ'))))))
                                           (trans (cong (subeq (trans (cong (λ a → a ++ Δ'') (++ass (Γ ++ Δ))) (trans (++ass (Γ ++ Δ)) (cong (_++_ (Γ ++ Δ)) (++ass (Γ' ++ Δ')))))) (sym (subeq⊗r (cong (λ a → a ++ Γ'') (++ass (Γ ++ Δ))))))
                                                  (trans (sym (subeqtrans {f = ⊗r (scut (⊗r (scut (⊗r f f₁) g) g₁) h) h₁}
                                                                (cong (λ a → a ++ Δ'') (cong (λ a → a ++ Γ'') (++ass (Γ ++ Δ)))) (trans (cong (λ a → a ++ Δ'') (++ass (Γ ++ Δ))) (trans (++ass (Γ ++ Δ)) (cong (_++_ (Γ ++ Δ)) (++ass (Γ' ++ Δ')))))))
                                                         (cong (λ a → subeq a (⊗r (scut (⊗r (scut (⊗r f f₁) g) g₁) h) h₁))
                                                               (uip {p = trans
                                                                          (cong (λ a → a ++ Δ'') (cong (λ a → a ++ Γ'') (++ass (Γ ++ Δ))))
                                                                          (trans (cong (λ a → a ++ Δ'') (++ass (Γ ++ Δ)))
                                                                            (trans (++ass (Γ ++ Δ))
                                                                              (cong (_++_ (Γ ++ Δ)) (++ass (Γ' ++ Δ')))))}
                                                                    {trans (++ass (((Γ ++ Δ) ++ Γ') ++ Δ'))
                                                                      (trans (cong (λ a → a ++ Γ'' ++ Δ'') (++ass (Γ ++ Δ)))
                                                                        (++ass (Γ ++ Δ)))})))))
                                    (trans (subeqtrans {f = ⊗r (scut (⊗r (scut (⊗r f f₁) g) g₁) h) h₁} (++ass (((Γ ++ Δ) ++ Γ') ++ Δ')) (trans (cong (λ a → a ++ Γ'' ++ Δ'') (++ass (Γ ++ Δ))) (++ass (Γ ++ Δ))))
                                           (subeqtrans (cong (λ a → a ++ Γ'' ++ Δ'') (++ass (Γ ++ Δ))) (++ass (Γ ++ Δ)))))))
               (cong (subeq (++ass (Γ ++ Δ))) (sym (scutsubeq2 (⊗r (scut (⊗r f f₁) g) g₁) (⊗r h h₁) (++ass (Γ ++ Δ))))))
scutass {Δ' = Δ'} (⊗r {Γ = Γ} {Δ} f f₁) (⊗r g g₁) (⊗l h) =
  trans (trans {!!}
               (subeqtrans (cong (λ a → a ++ Δ') (++ass (Γ ++ Δ))) (++ass (Γ ++ Δ))))
        (cong (subeq (++ass (Γ ++ Δ))) (sym (scutsubeq2 (⊗r (scut (⊗r f f₁) g) g₁) (⊗l h) (++ass (Γ ++ Δ)))))
scutass (⊗r f f₁) (⊗l g) h = {!!}
scutass {Γ = Γ} (Il f) g h = trans (cong Il (scutass f g h)) (sym (subeqIl (++ass Γ)))
scutass {Γ = Γ} (⊗l f) g h = trans (cong ⊗l (scutass f g h)) (sym (subeq⊗l (++ass Γ)))


-}

{-
--scutccutass : ∀{S}{Γ}{Γ'}{Δ}{Δ'}{Δ''}{A}{A'}{B}{C}(f : S ∣ Γ' ⊢ A')
--  (g : nothing ∣ Δ ⊢ B)(h : just A' ∣ Γ ⊢ A)(k : just A ∣ Δ' ⊢ C) → 
--  scut f (ccut Γ g (scut h k) {!!}) ≡ ccut {!Γ!} g (scut (scut f h) k) {!!} --ccut Γ g (scut (scut Ir f) h) r
--scutccutass = {!!}


{-
{-
mutual
  scut≈ : {S : Maybe Tm} → {Γ Δ' : List Tm} → {A C : Tm} → 
             {f g : S ∣ Γ ⊢ A}  →  {f' g' : just A ∣ Δ' ⊢ C} →
              f ≈ g → f' ≈ g' → scut f f' ≈ scut g g'
  scut≈ refl≈ q = {!!}
  scut≈ (sym≈ p) q = sym≈ (scut≈ p (sym≈ q))
  scut≈ (trans≈ p p₁) q = trans≈ (scut≈ p q) (scut≈ p₁ refl≈)
  scut≈ (conguf p) q = conguf (scut≈ p q)
  scut≈ (cong⊗l p) q = cong⊗l (scut≈ p q)
  scut≈ (congIl p) q = congIl (scut≈ p q)
  scut≈ (cong⊗r p p₁) q = trans≈ {!!} {!!}
  scut≈ axI q = trans≈ q (scutIr _)
  scut≈ ax⊗ q = trans≈ q (scut⊗rax _)
  scut≈ {g' = g'} (⊗ruf {f = f}{g}) q = trans≈ {!!} (scut⊗ruf {f = f}{g} g') 
  scut≈ ⊗rIl q = {!!}
  scut≈ ⊗r⊗l q = {!!}        
-}



scut⊗r2 : ∀{S}{Γ}{Δ}{Δ'}{A}{B}{C}
    → (h : S ∣ Γ ⊢ A){f : just A ∣ Δ ⊢ B}{g : nothing ∣ Δ' ⊢ C}
    → scut h (⊗r f g) ≈ subeq (++ass Γ) (⊗r (scut h f) g)
scut⊗r2 ax = refl≈
scut⊗r2 (uf {Γ}{A = A} h) =
  trans≈ (trans≈ (conguf (scut⊗r2 h))
                 (refl≈' (sym (subequf (++ass Γ)))))
         (subeq≈ (cong (_∷_ A) (++ass Γ)) (sym≈ ⊗ruf))
scut⊗r2 Ir = refl≈
scut⊗r2 (⊗r h h₁) = refl≈
scut⊗r2 {Γ = Γ} (Il h) =
  trans≈ (trans≈ (congIl (scut⊗r2 h))
                 (refl≈' (sym (subeqIl (++ass Γ)))))
         (subeq≈ (++ass Γ) (sym≈ ⊗rIl))
scut⊗r2 (⊗l {Γ} h) =
  trans≈ (trans≈ (cong⊗l (scut⊗r2 h))
                 (refl≈' (sym (subeq⊗l (++ass Γ)))))
         (subeq≈ (++ass Γ) (sym≈ ⊗r⊗l))



ccut⊗r : {T : Maybe Tm} → {Γ Γ' Δ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} →  {A A' B : Tm} → 
             {h : nothing ∣ Γ' ⊢ A'}{f : T ∣ Γ ⊢ A}{g :  nothing ∣ Δ ⊢ B} →
             (r : Γ ≡ Δ₀ ++ A' ∷ Δ') (s : Γ ++ Δ ≡ Δ₀ ++ A' ∷ Δ' ++ Δ) →
             subeq (++ass (Δ₀ ++ Γ')) (⊗r (ccut Δ₀ h f r) g) ≡ ccut Δ₀ h (⊗r f g) s
ccut⊗r {Γ = Γ}{_}{Δ} Δ₀ r s with lemma++ Δ₀ Γ s
ccut⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ = Δ} Δ₀ {Δ'} r s | inj₁ (Γ₀ , refl , y) with lemma++' Δ' Γ₀ y
ccut⊗r {_} {.(Δ₀ ++ _ ∷ Γ₀)} {Δ = Δ} Δ₀ {.Γ₀} refl s | inj₁ (Γ₀ , refl , refl) | refl = refl
ccut⊗r {Γ = Γ} {Δ = Δ} Δ₀ {Δ'} r s | inj₂ ([] , x , y) = ⊥-elim (lemma++'' Δ' Δ x)
ccut⊗r {Γ = Γ} {Δ = Δ} Δ₀ {Δ'} {A' = A'} r s | inj₂ (x₁ ∷ Γ₀ , x , y) = ⊥-elim (lemma++'' (Γ₀ ++ A' ∷ Δ') Δ (trans x (sym (++ass (x₁ ∷ Γ₀)))))

ccut⊗r2 : {T : Maybe Tm} → {Γ Γ' Δ : List Tm} → (Γ₀ : List Tm) → {Δ' : List Tm} →  {A A' B : Tm} → 
             {h : nothing ∣ Γ' ⊢ A'}{f : T ∣ Γ ⊢ A}{g :  nothing ∣ Δ ⊢ B} →
             (r : Δ ≡ Γ₀ ++ A' ∷ Δ')
             (s : Γ ++ Δ ≡ (Γ ++ Γ₀) ++ A' ∷ Δ') → 
             subeq (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (⊗r f (ccut Γ₀ h g r)) ≡ ccut (Γ ++ Γ₀) h (⊗r f g) s
ccut⊗r2 {Γ = Γ} Γ₀ r s with lemma++ (Γ ++ Γ₀) Γ s
ccut⊗r2 {Γ = Γ}{Δ = Δ} [] r s | inj₁ (N , a , refl) = ⊥-elim (lemma++'' N Δ r )
ccut⊗r2 {Γ = Γ} {Δ = Δ} (x ∷ Γ₀) {A' = A'} r s | inj₁ (N , a , refl) = ⊥-elim (lemma++'' (Γ₀ ++ A' ∷ N) Δ (trans r (sym (++ass (x ∷ Γ₀)))))
ccut⊗r2 {Γ = Γ} Γ₀ r s | inj₂ (N , refl , b) with lemma++'2 Γ b
ccut⊗r2 {Γ = Γ} .N refl s | inj₂ (N , refl , refl) | refl = refl

ccutsubeq : {T : Maybe Tm} → {Γ Δ Δ₁ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} →  {A C : Tm} → 
             (f : nothing ∣ Γ ⊢ A){g :  T ∣ Δ ⊢ C}(r : Δ₁ ≡ Δ₀ ++ A ∷ Δ')(p : Δ ≡ Δ₁) →
             ccut Δ₀ f (subeq p g) r ≡ ccut Δ₀ f g (trans p r)
ccutsubeq Δ₀ f r refl = refl             

ccutsubeq2 : {T : Maybe Tm} → {Γ Δ Δ₁ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} →  {A C : Tm} → 
             (f : nothing ∣ Γ ⊢ A){g :  T ∣ Δ ⊢ C}(r : Δ ≡ Δ₀ ++ A ∷ Δ')(p : Δ₁ ≡ Δ₀) →
             ccut Δ₀ f g r ≡ subeq (cong (λ a → (a ++ Γ) ++ Δ') p) (ccut Δ₁ f g (trans r (cong (λ a → a ++ A ∷ Δ') (sym p))))
ccutsubeq2 Δ₀ f refl refl = refl

mutual 
  scut⊗r : ∀{S}{Γ}{Δ}{Δ'}{A}{B}{C}
    → {f g : S ∣ Γ ⊢ A}{f' g' : nothing ∣ Δ ⊢ B}
    → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
    → (p : f ≈ g)(q : f' ≈ g')
    → scut (⊗r f f') h ≈ scut (⊗r g g') h
  scut⊗r {Γ = Γ}{Δ} ax p q = subeq≈ (++ru (Γ ++ Δ)) (cong⊗r p q)
  scut⊗r {Γ = Γ}{Δ} (⊗r h h') p q = subeq≈ (++ass (Γ ++ Δ)) (cong⊗r (scut⊗r h p q) refl≈)
  scut⊗r {Γ = Γ}{Δ} {g = g}(⊗l h) p q = trans≈ (ccut≈2 Γ refl (scut≈ p)) (ccut≈ Γ (scut g h) refl q)

  scut≈ : {S : Maybe Tm} → {Γ Δ' : List Tm} → {A C : Tm} → 
             {f g : S ∣ Γ ⊢ A}  → {h : just A ∣ Δ' ⊢ C} →
             f ≈ g → scut f h ≈ scut g h
  scut≈ refl≈ = refl≈
  scut≈ (sym≈ p) = sym≈ (scut≈ p)
  scut≈ (trans≈ p q) = trans≈ (scut≈ p) (scut≈ q)
  scut≈ (conguf p) = conguf (scut≈ p)
  scut≈ (cong⊗l p) = cong⊗l (scut≈ p)
  scut≈ (congIl p) = congIl (scut≈ p)
  scut≈ {h = h} (cong⊗r p q) = scut⊗r h p q  
  scut≈ axI = scutIr _
  scut≈ ax⊗ = scut⊗rax _
  scut≈ {h = h} ⊗ruf = scut⊗ruf h
  scut≈ {h = h} ⊗rIl = scut⊗rIl h
  scut≈ {h = h} ⊗r⊗l = scut⊗r⊗l h        

  scut≈2 : {S : Maybe Tm} → {Γ Δ' : List Tm} → {A C : Tm} → 
             (h : S ∣ Γ ⊢ A)  → {f g : just A ∣ Δ' ⊢ C} →
             f ≈ g → scut h f ≈ scut h g
  scut≈2 ax p = p
  scut≈2 (uf h) p = conguf (scut≈2 h p)
  scut≈2 Ir refl≈ = refl≈
  scut≈2 Ir (sym≈ p) = sym≈ (scut≈2 Ir p)
  scut≈2 Ir (trans≈ p p₁) = trans≈ (scut≈2 Ir p) (scut≈2 Ir p₁)
  scut≈2 Ir (congIl p) = p
  scut≈2 Ir (cong⊗r p p₁) = cong⊗r (scut≈2 Ir p) p₁
  scut≈2 Ir axI = refl≈
  scut≈2 Ir ⊗rIl = refl≈
  scut≈2 (⊗r h h₁) refl≈ = refl≈
  scut≈2 (⊗r h h₁) (sym≈ p) = sym≈ (scut≈2 (⊗r h h₁) p)
  scut≈2 (⊗r h h₁) (trans≈ p p₁) = trans≈ (scut≈2 (⊗r h h₁) p) (scut≈2 (⊗r h h₁) p₁)
  scut≈2 (⊗r {Γ = Γ} h h₁) (cong⊗l p) = ccut≈2 Γ refl (scut≈2 h p)
  scut≈2 (⊗r {Γ = Γ}{Δ} h h₁) (cong⊗r p p₁) = subeq≈ (++ass (Γ ++ Δ)) (cong⊗r (scut≈2 (⊗r h h₁) p) p₁)
  scut≈2 (⊗r {Γ = Γ}{Δ} h h₁) (ax⊗ {B = B}) =
    trans≈ (trans≈ (trans≈ (trans≈ (trans≈ (refl≈' (trans (trans (cong (λ a → subeq a (⊗r h h₁)) (uip {p = ++ru (Γ ++ Δ)}
                                                                                                      {trans (cong (_++_ Γ) (++ru Δ)) (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong (λ a → (a ++ Δ) ++ []) (sym (++ru Γ))))}))
                                                                 (subeqtrans (cong (_++_ Γ) (++ru Δ)) (trans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong (λ a → (a ++ Δ) ++ []) (sym (++ru Γ))))))
                                                          (subeqtrans (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong (λ a → (a ++ Δ) ++ []) (sym (++ru Γ))))))
                                           (trans≈ (subeq≈ (cong (λ a → (a ++ Δ) ++ []) (sym (++ru Γ))) (subeq≈ (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (refl≈' (subeq⊗r2 (++ru Δ)))))
                                                   (subeq≈ (cong (λ a → (a ++ Δ) ++ []) (sym (++ru Γ))) (subeq≈ (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong⊗r refl≈ (sym≈ (refl≈' (scutax h₁))))))))
                                   (trans≈ (subeq≈ (cong (λ a → (a ++ Δ) ++ []) (sym (++ru Γ))) (refl≈' (trans (ccut⊗r2 [] {h = h₁}{h}{uf ax} refl (cong (λ a → a ++ B ∷ []) (++ru Γ)))
                                                         (cong (ccut (Γ ++ []) h₁ (⊗r h (uf ax))) (uip {p = cong (λ a → a ++ B ∷ []) (++ru Γ)}
                                                                                                        {trans (trans (cong (λ a → a ++ B ∷ []) (++ru Γ)) (trans (++ass Γ) refl)) (cong (λ a → a ++ B ∷ []) (sym (sym (++ru Γ))))})))))
                                           (sym≈ (refl≈' (ccutsubeq2 Γ h₁ {⊗r h (uf ax)} (trans (cong (λ a → a ++ B ∷ []) (++ru Γ)) (trans (++ass Γ) refl)) (sym (++ru Γ)))))))
                           (sym≈ (refl≈' (trans (ccutsubeq Γ h₁ {subeq (cong (λ a → a ++ B ∷ []) (++ru Γ)) (⊗r h (uf ax))} refl (++ass Γ))
                                                (ccutsubeq Γ h₁ {⊗r h (uf ax)} (trans (++ass Γ) refl) (cong (λ a → a ++ B ∷ []) (++ru Γ))))))) 
                   (sym≈ (ccut≈2 Γ refl (subeq≈ (++ass Γ) (trans≈ (cong⊗r (refl≈' (scutax h)) refl≈) (sym≈ (refl≈' (subeq⊗r (++ru Γ)))))))))
           (sym≈ (ccut≈2 Γ refl (scut⊗r2 h)))
  scut≈2 (⊗r {Γ = Γ} h h₁) (⊗r⊗l {f = f}) =
    trans≈ (trans≈ (refl≈' (ccut⊗r Γ {h = h₁}{scut h f} refl (++ass Γ)))
                   (refl≈' (trans (cong (ccut Γ h₁ (⊗r (scut h f) _)) (uip {p = ++ass Γ}{trans (++ass Γ) refl}))
                                  (sym (ccutsubeq Γ h₁ {⊗r (scut h f) _} refl (++ass Γ)))))) 
           (sym≈ (ccut≈2 Γ refl (scut⊗r2 h)))
  scut≈2 (Il h) p = congIl (scut≈2 h p)
  scut≈2 (⊗l h) p = cong⊗l (scut≈2 h p)

  ccut≈ : {T : Maybe Tm} → {Γ Δ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} →  {A C : Tm} → 
             {f f' : nothing ∣ Γ ⊢ A}(g : T ∣ Δ ⊢ C)  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
             f ≈ f' → ccut Δ₀ f g r ≈ ccut Δ₀ f' g r
  ccut≈ Δ₀ ax r p = refl≈
  ccut≈ Δ₀ (uf g) r p with lemma∷ Δ₀ r
  ccut≈ .[] (uf g) r p | inj₁ (refl , refl , refl) = scut≈ p
  ccut≈ .(_ ∷ Γ₀) (uf g) r p | inj₂ (Γ₀ , b , refl) = conguf (ccut≈ Γ₀ g b p)
  ccut≈ Δ₀ Ir r p = refl≈
  ccut≈ Δ₀ (⊗r {Γ = Γ} g g₁) r p with lemma++ Δ₀ Γ r
  ccut≈ {Γ = Γ} Δ₀ (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} g g₁) r p | inj₁ (Γ₀ , refl , refl) =
    subeq≈ (++ass (Δ₀ ++ Γ)) (cong⊗r (ccut≈ Δ₀ g refl p) refl≈)
  ccut≈ .(Γ ++ Γ₀) (⊗r {Γ = Γ} g g₁) r p | inj₂ (Γ₀ , refl , refl) =
    subeq≈ (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong⊗r refl≈ (ccut≈ Γ₀ g₁ refl p))
  ccut≈ Δ₀ (Il g) r p = congIl (ccut≈ Δ₀ g r p)
  ccut≈ Δ₀ (⊗l {B = B} g) r p = cong⊗l (ccut≈ (B ∷ Δ₀) g (cong (_∷_ B) r) p)

  ccut≈2 : {T : Maybe Tm} → {Γ Δ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} →  {A C : Tm} → 
             {f : nothing ∣ Γ ⊢ A}{g g' : T ∣ Δ ⊢ C}  → (r : Δ ≡ Δ₀ ++ A ∷ Δ') →  
             g ≈ g' → ccut Δ₀ f g r ≈ ccut Δ₀ f g' r
  ccut≈2 Δ₀ r refl≈ = refl≈
  ccut≈2 Δ₀ r (sym≈ p) = sym≈ (ccut≈2 Δ₀ r p)
  ccut≈2 Δ₀ r (trans≈ p p₁) = trans≈ (ccut≈2 Δ₀ r p) (ccut≈2 Δ₀ r p₁)
  ccut≈2 Δ₀ r (conguf p) with lemma∷ Δ₀ r
  ccut≈2 .[] {f = f} r (conguf p) | inj₁ (refl , refl , refl) = scut≈2 f p
  ccut≈2 .(_ ∷ Γ₀) r (conguf p) | inj₂ (Γ₀ , refl , refl) = conguf (ccut≈2 Γ₀ refl p)
  ccut≈2 Δ₀ refl (cong⊗l {B = B} p) = cong⊗l (ccut≈2 (B ∷ Δ₀) refl p)
  ccut≈2 Δ₀ refl (congIl p) = congIl (ccut≈2 Δ₀ refl p)
  ccut≈2 Δ₀ r (cong⊗r {Γ = Γ} p p₁) with lemma++ Δ₀ Γ r
  ccut≈2 {Γ = Γ} Δ₀ r (cong⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} p p₁) | inj₁ (Γ₀ , refl , refl) =
    subeq≈ (++ass (Δ₀ ++ Γ)) (cong⊗r (ccut≈2 Δ₀ refl p) p₁)
  ccut≈2 .(Γ ++ Γ₀) r (cong⊗r {Γ = Γ} p p₁) | inj₂ (Γ₀ , refl , refl) =
    subeq≈ (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) (cong⊗r p (ccut≈2 Γ₀ refl p₁))
  ccut≈2 Δ₀ r axI = ⊥-elim (lemma[] Δ₀ r)
  ccut≈2 Δ₀ r ax⊗ = ⊥-elim (lemma[] Δ₀ r)
  ccut≈2 Δ₀ r (⊗ruf {Γ = Γ}{A' = A'}) with lemma++ Δ₀ (A' ∷ Γ) r | lemma∷ Δ₀ r
  ccut≈2 .[] {f = f} r (⊗ruf {.Γ₀} {A' = A'}) | inj₁ (Γ₀ , refl , refl) | inj₁ (refl , refl , refl) = sym≈ (scut⊗r2 f)
  ccut≈2 .(A' ∷ Γ₀') {A = A} r (⊗ruf {.(Γ₀' ++ _ ∷ Γ₀)} {A' = A'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , b , refl) with lemma∷ (A' ∷ Γ₀'){Γ₀}{_}{A} refl
  ccut≈2 .(A' ∷ Γ₀') {A = A} r (⊗ruf {.(Γ₀' ++ A ∷ Γ₀)} {A' = A'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , b , refl) | inj₁ (x , () , z)
  ccut≈2 {Γ = Γ} .(A' ∷ Γ₀') {A = A} r (⊗ruf {.(Γ₀' ++ A ∷ Γ₀)} {A' = A'}) | inj₁ (Γ₀ , refl , refl) | inj₂ (Γ₀' , b , refl) | inj₂ (_ , x , refl) =
    trans≈ (subeq≈ (cong (_∷_ A') (++ass (Γ₀' ++ Γ))) ⊗ruf)
           (trans≈ (refl≈' (subequf (++ass (Γ₀' ++ Γ))))
                   (conguf (refl≈' (ccut⊗r Γ₀' refl b))))
  ccut≈2 .[] r (⊗ruf {Γ} {A' = A'}) | inj₂ (Γ₀ , s , ()) | inj₁ (a , refl , c)
  ccut≈2 .(A' ∷ Γ ++ Γ₀) {f = h} r (⊗ruf {Γ} {A' = A'} {f = f}{g}) | inj₂ (Γ₀ , refl , refl) | inj₂ (.(Γ ++ Γ₀) , b , refl) = 
    trans≈ (subeq≈ (trans (sym (cong (_∷_ A') (++ass Γ))) (cong₂ _++_ (sym (cong (_∷_ A') (++ass Γ))) refl)) ⊗ruf)
           (trans≈ (trans≈ (refl≈' (cong (λ a → subeq a (uf (⊗r f (ccut Γ₀ h g refl))))
                                   (uip {p = (trans (sym (cong (_∷_ A') (++ass Γ))) (cong₂ _++_ (sym (cong (_∷_ A') (++ass Γ))) refl))}
                                        {(cong (_∷_ A') (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)))})))
                           (refl≈' (subequf (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)))))
                   (conguf (refl≈' (ccut⊗r2 Γ₀ {h = h}{f}{g} refl b))))
  ccut≈2 Δ₀ r (⊗rIl {Γ = Γ}) with lemma++ Δ₀ Γ r
  ccut≈2 {Γ = Γ} Δ₀ r (⊗rIl {.(Δ₀ ++ _ ∷ Γ₀)}) | inj₁ (Γ₀ , refl , refl) =
    trans≈ (subeq≈ (++ass (Δ₀ ++ Γ)) ⊗rIl) (refl≈' (subeqIl (++ass (Δ₀ ++ Γ))))
  ccut≈2 .(Γ ++ Γ₀) r (⊗rIl {Γ}) | inj₂ (Γ₀ , refl , refl) =
    trans≈ (subeq≈ (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) ⊗rIl)
           (refl≈' (subeqIl (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))))
  ccut≈2 Δ₀ r (⊗r⊗l {Γ = Γ}) with lemma++ Δ₀ Γ r
  ccut≈2 {Γ = Γ} Δ₀ r (⊗r⊗l {.(Δ₀ ++ _ ∷ Γ₀)}{B' = B'}) | inj₁ (Γ₀ , refl , refl) =
    trans≈ (subeq≈ (++ass (Δ₀ ++ Γ)) ⊗r⊗l)
           (trans≈ (refl≈' (subeq⊗l (++ass (Δ₀ ++ Γ))))
                   (cong⊗l (refl≈' (ccut⊗r (B' ∷ Δ₀) refl (cong (_∷_ B') r) ))))
  ccut≈2 .(Γ ++ Γ₀) {f = h} r (⊗r⊗l {Γ}{B' = B'} {f = f}{g}) | inj₂ (Γ₀ , refl , refl) =
    trans≈ (subeq≈ (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl)) ⊗r⊗l)
           (trans≈ (refl≈' (subeq⊗l (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))))
                   (cong⊗l (refl≈' (trans (cong (λ a → subeq a (⊗r f (ccut Γ₀ h g refl)))
                                          (uip {p = cong (_∷_ B') (trans (sym (++ass Γ)) (cong₂ _++_ (sym (++ass Γ)) refl))}
                                               {trans (sym (cong (_∷_ B') (++ass Γ))) (cong₂ _++_ (sym (cong (_∷_ B') (++ass Γ))) refl)}))
                                          (ccut⊗r2 Γ₀ {h = h}{f}{g} refl (cong (_∷_ B') r))))))
                                          
-- =======================================================================

-- soundness

-- interpretation of antecedents

-- -- (Note that an empty stoup contributes an I to the meaning 
-- -- of an antecedent.)

t : Maybe Tm → Tm
t nothing = I
t (just A) = A

[_∣_] : Tm → List Tm → Tm
[ A ∣ [] ] = A
[ A ∣ C ∷ Γ ] = [ A ⊗ C ∣ Γ ]

〈_∣_〉 : Maybe Tm → List Tm → Tm 
〈 S ∣ Γ 〉 = [ t S ∣ Γ ] 

[_∣_]f : {A B : Tm} → A ⇒ B → (Γ : List Tm) → [ A ∣ Γ ] ⇒ [ B ∣ Γ ]
[ f ∣ [] ]f = f
[ f ∣ C ∷ Γ ]f = [ f ⊗ id ∣ Γ ]f

lemma'' : (A B : Tm) → (Δ : List Tm) → 
                   [ A ⊗ B ∣  Δ ] ⇒ A ⊗ [ B ∣ Δ ] 
lemma'' A B [] = id
lemma'' A B (C ∷ Δ) = lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f 

lemma' : (A : Tm) → (Γ Δ : List Tm) →
                   [ A ∣ Γ ++ Δ ] ⇒ [ A ∣ Γ ] ⊗ 〈 nothing ∣ Δ 〉
lemma' A [] Δ = lemma'' A I Δ ∘ [ ρ ∣ Δ ]f 
lemma' A (C ∷ Γ) Δ  = lemma' (A ⊗ C) Γ Δ 

lemma : (S : Maybe Tm) → (Γ Δ : List Tm) →  
                   〈 S ∣ Γ ++ Δ 〉 ⇒ 〈 S ∣ Γ 〉 ⊗ 〈 nothing ∣ Δ 〉
lemma S Γ Δ = lemma' (t S) Γ Δ 


sound : {S : Maybe Tm} → {Γ : List Tm} → {A : Tm} → S ∣ Γ ⊢ A → 〈 S ∣ Γ 〉 ⇒ A 
sound ax = id
sound (uf {Γ} f) = sound f ∘ [ l ∣ Γ ]f 
sound Ir = id
sound (⊗r {S} {Γ} {Δ} f g) = sound f ⊗ sound g ∘ lemma S Γ Δ
sound (Il f) = sound f
sound (⊗l f) = sound f 

-- =======================================================================

-- completeness

cmplt : {A B : Tm} → A ⇒ B → just A ∣ [] ⊢ B
cmplt id = ax
cmplt (f ∘ g) = scut (cmplt g) (cmplt f)
cmplt (f ⊗ g) = ⊗l (⊗r (cmplt f) (uf (cmplt g)))
cmplt l = ⊗l (Il (uf ax))
cmplt ρ = ⊗r ax Ir 
cmplt α = ⊗l (⊗l (⊗r ax (uf (⊗r ax (uf ax))))) 

cmplt≐ : {A B : Tm}{f g : A ⇒ B} → f ≐ g → cmplt f ≈ cmplt g
cmplt≐ refl≐ = refl≈
cmplt≐ (sym≐ p) = sym≈ (cmplt≐ p)
cmplt≐ (trans≐ p p₁) = trans≈ (cmplt≐ p) (cmplt≐ p₁)
cmplt≐ (_∘≐_ {f = f}{k = k} p p₁) =
  trans≈ (scut≈  {h = cmplt f} (cmplt≐ p₁)) (scut≈2 (cmplt k) (cmplt≐ p)) 
cmplt≐ (p ⊗≐ p₁) = cong⊗l (cong⊗r (cmplt≐ p) (conguf (cmplt≐ p₁)))
cmplt≐ {g = g} lid = refl≈' (scutax (cmplt g))
cmplt≐ rid = refl≈
cmplt≐ (ass {f = f}{g}{h})  = refl≈' (scutass (cmplt h) (cmplt g) {cmplt f})
cmplt≐ f⊗id = sym≈ ax⊗
cmplt≐ (f⊗∘ {f = f}) = cong⊗l (sym≈ (ccut≈2 [] refl (scut⊗r2 (cmplt f))))
cmplt≐ (nl {f = f}) = cong⊗l (congIl (conguf (refl≈' (scutax (cmplt f)))))
cmplt≐ (nρ {f = f}) = trans≈ (scut⊗r2 (cmplt f)) (cong⊗r (refl≈' (scutax (cmplt f))) refl≈)
cmplt≐ (nα {B = B}{f = f}{g}{h}) =
  cong⊗l (cong⊗l (trans≈ (ccut≈2 (B ∷ []) refl (ccut≈2 [] refl (scut⊗r2 (cmplt f))))
                         (cong⊗r (refl≈' (scutax (cmplt f)))
                                 (conguf (trans≈ (ccut≈2 [] refl (scut⊗r2 (cmplt g)))
                                                 (cong⊗r (refl≈' (scutax (cmplt g))) (conguf (refl≈' (scutax (cmplt h))))))))))
cmplt≐ lρ = sym≈ axI
cmplt≐ lαρ = ax⊗
cmplt≐ lα = cong⊗l (trans≈ (cong⊗l (trans≈ (congIl (trans≈ refl≈ (sym≈ ⊗ruf))) (sym≈ ⊗rIl))) (sym≈ ⊗r⊗l))
cmplt≐ αρ = refl≈
cmplt≐ ααα = refl≈

-- ==================================================

{-

-- =======================================================================

-- soundness after completeness is identity


[≐∣_]f : (Γ : List Tm) → {A B : Tm} → {f g : A ⇒ B} → 
                                     f ≐ g → [ f ∣ Γ ]f ≐ [ g ∣ Γ ]f
[≐∣ [] ]f p = p
[≐∣ C ∷ Γ ]f p = [≐∣ Γ ]f (p ⊗≐ refl≐)

[id∣_]f : (Γ : List Tm) → {A : Tm} → [ id {A} ∣ Γ ]f ≐ id {[ A ∣ Γ ]}
[id∣ [] ]f = refl≐ 
[id∣ C ∷ Γ ]f = trans≐ ([≐∣ Γ ]f f⊗id) [id∣ Γ ]f 

[∘∣_]f : (Γ : List Tm) → {A B C : Tm} → (f : B ⇒ C) → (g : A ⇒ B) → 
            [ f ∘ g ∣ Γ ]f ≐ [ f ∣ Γ ]f ∘ [ g ∣ Γ ]f
[∘∣ [] ]f f g = refl≐
[∘∣ C ∷ Γ ]f f g = 
   trans≐ ([≐∣ Γ ]f (trans≐ (refl≐ ⊗≐ rid) f⊗∘)) ([∘∣ Γ ]f (f ⊗ id) (g ⊗ id))  

{-
eqid : {A B : Tm} → (p : A ≡ B) → A ⇒ B
eqid refl = id
 
ueqid : {A B : Tm} → (p q : A ≡ B) → eqid p ≐ eqid q
ueqid refl refl = refl≐
-}

[]≡ : {A : Tm} → {Γ Γ' : List Tm} → (p : Γ ≡ Γ') → 
                                             [ A ∣ Γ' ] ⇒ [ A ∣ Γ ]
[]≡ refl = id

〈〉≡ : {S : Maybe Tm} → {Γ Γ' : List Tm} → (p : Γ ≡ Γ') → 
                                             〈 S ∣ Γ' 〉 ⇒ 〈 S ∣ Γ 〉
〈〉≡ {S} p = []≡ {t S} p



[]≡id : {A : Tm} → {Γ : List Tm} → (p : Γ ≡ Γ) → []≡ {A} p ≐ id
[]≡id refl = refl≐ 

[]≡eq : {A : Tm} → {Γ Γ' : List Tm} → (p q : Γ ≡ Γ') 
                                        → []≡ {A} p ≐ []≡ {A} q
[]≡eq refl refl = refl≐

〈〉≡eq : {S : Maybe Tm} → {Γ Γ' : List Tm} → (p q : Γ ≡ Γ') 
                                        → 〈〉≡ {S} p ≐ 〈〉≡ {S} q
〈〉≡eq p q = []≡eq p q

[]≡∷ : {A C : Tm} → {Γ Γ' : List Tm} → (p : Γ ≡ Γ') → 
                     []≡ {A} (cong (_∷_ C) p) ≐ []≡ {A ⊗ C} p
[]≡∷ refl = refl≐ 

{-
[]++ : (A : Tm) → (Γ Δ : List Tm) → [ A ∣ Γ ++ Δ ] ≡ [ [ A ∣ Γ ] ∣ Δ ]
[]++ A [] Δ = refl
[]++ A (B ∷ Γ) Δ = []++ (A ⊗ B) Γ Δ

〈〉++ : (S : Maybe Tm) → (Γ Δ : List Tm) → 〈 S ∣ Γ ++ Δ 〉 ≡ [ 〈 S ∣ Γ 〉 ∣ Δ ]
〈〉++ S Γ Δ = []++ (t S) Γ Δ
-}


[]++ : (A : Tm) → (Γ Δ : List Tm) → [ A ∣ Γ ++ Δ ] ⇒ [ [ A ∣ Γ ] ∣ Δ ]
[]++ A [] Δ = id
[]++ A (C ∷ Γ) Δ = []++ (A ⊗ C) Γ Δ 

〈〉++ : (S : Maybe Tm) → (Γ Δ : List Tm) → 〈 S ∣ Γ ++ Δ 〉 ⇒ [ 〈 S ∣ Γ 〉 ∣ Δ ]
--〈〉++ S Γ Δ = eqid (〈++〉 S Γ Δ)
〈〉++ S Γ Δ = []++ (t S) Γ Δ

[]++n : {A B : Tm} → (f : A ⇒ B) → (Γ Δ : List Tm) →         
       []++ B Γ Δ ∘ [ f ∣ Γ ++ Δ ]f ≐  [ [ f ∣ Γ ]f ∣ Δ ]f ∘ []++ A Γ Δ 
[]++n f [] Δ = trans≐ lid rid
[]++n f (C ∷ Γ) Δ = []++n (f ⊗ id {C}) Γ Δ 


++[] : (A : Tm) → (Γ Δ : List Tm) → [ [ A ∣ Γ ] ∣ Δ ] ⇒ [ A ∣ Γ ++ Δ ]
++[] A [] Δ = id
++[] A (C ∷ Γ) Δ = ++[] (A ⊗ C) Γ Δ 

++〈〉 : (S : Maybe Tm) → (Γ Δ : List Tm) → [ 〈 S ∣ Γ 〉 ∣ Δ ] ⇒ 〈 S ∣ Γ ++ Δ 〉
--〈〉++ S Γ Δ = eqid (〈++〉 S Γ Δ)
++〈〉 S Γ Δ = ++[] (t S) Γ Δ


lemma10' : (A : Tm) → (Γ Δ Δ' : List Tm) → 
        ++[] A Γ Δ ⊗ id ∘ lemma' [ A ∣ Γ ] Δ Δ' 
            ≐ lemma' A (Γ ++ Δ) Δ' ∘ []≡ {A} (++ass Γ) ∘ ++[] A Γ (Δ ++ Δ') 
lemma10' A [] Δ Δ' = 
  proof 
    id ⊗ id ∘ lemma' A Δ Δ' 
  ≐〈 f⊗id ∘≐ refl≐ 〉
    id ∘ lemma' A Δ Δ' 
  ≐〈 lid 〉
    lemma' A Δ Δ' 
  ≐〈 rid 〉
    lemma' A Δ Δ' ∘ id
  ≐〈 rid 〉
    lemma' A Δ Δ' ∘ id ∘ id 
  qed
lemma10' A (C ∷ Γ) Δ Δ' = 
  trans≐ (lemma10' (A ⊗ C) Γ Δ Δ') (refl≐ ∘≐ sym≐ ([]≡∷ (++ass Γ)) ∘≐ refl≐)  

lemma10 : (S : Maybe Tm) → (Γ Δ Δ' : List Tm) → 
        ++〈〉 S Γ Δ ⊗ id ∘ lemma' 〈 S ∣ Γ 〉 Δ Δ' 
            ≐ lemma S (Γ ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass Γ) ∘ ++〈〉 S Γ (Δ ++ Δ') 
lemma10 S Γ Δ Δ' = lemma10' (t S) Γ Δ Δ'


++[]n : {A B : Tm} → (f : A ⇒ B) → (Γ Δ : List Tm) →         
        ++[] B Γ Δ  ∘ [ [ f ∣ Γ ]f ∣ Δ ]f ≐ [ f ∣ Γ ++ Δ ]f ∘ ++[] A Γ Δ  
++[]n f [] Δ = trans≐ lid rid
++[]n f (C ∷ Γ) Δ = ++[]n (f ⊗ id {C}) Γ Δ 





[]++iso : (A : Tm) → (Γ Δ : List Tm) → []++ A Γ Δ ∘ ++[] A Γ Δ ≐ id
[]++iso A [] Δ = lid
[]++iso A (C ∷ Γ) Δ = []++iso (A ⊗ C) Γ Δ

〈〉++iso : (S : Maybe Tm) → (Γ Δ : List Tm) → 〈〉++ S Γ Δ ∘ ++〈〉 S Γ Δ ≐ id
〈〉++iso S Γ Δ = []++iso (t S) Γ Δ


soundsubeq : {S : Maybe Tm} → {Γ Γ' : List Tm} → {A : Tm} → 
      (p : Γ ≡ Γ') → (f : S ∣ Γ ⊢ A) → 
                      sound (subeq p f) ≐ sound f ∘ 〈〉≡ {S} {Γ} {Γ'} p
soundsubeq {S} refl f = rid



rulemma' : (A : Tm) → (Γ : List Tm) → []≡ {A} (++ru Γ) ≐ []++ A Γ [] 
rulemma' A [] = refl≐
rulemma' A (C ∷ Γ) = trans≐ ([]≡∷ {A} (++ru Γ)) (rulemma' (A ⊗ C) Γ) 

rulemma : (S : Maybe Tm) → (Γ : List Tm) → 〈〉≡ {S} (++ru Γ) ≐ 〈〉++ S Γ [] 
rulemma S Γ = rulemma' (t S) Γ


asslemma' : (A : Tm) → (Γ Δ Δ' : List Tm) → 
       []++ A Γ Δ ⊗ id ∘ lemma' A (Γ ++ Δ) Δ' ∘ []≡ {A} (++ass Γ {Δ} {Δ'})
                         ≐ lemma' [ A ∣ Γ ] Δ Δ' ∘ []++ A Γ (Δ ++ Δ') 
asslemma' A [] Δ Δ' = 
   proof 
     id ⊗ id ∘ lemma' A Δ Δ' ∘ id 
   ≐〈  f⊗id ∘≐ refl≐ ∘≐ refl≐ 〉 
     id ∘ lemma' A Δ Δ' ∘ id 
   ≐〈  lid ∘≐ refl≐ 〉
     lemma' A Δ Δ' ∘ id 
   qed 
asslemma' A (C ∷ Γ) Δ Δ' = 
   proof 
     []++ (A ⊗ C) Γ Δ ⊗ id ∘ lemma' (A ⊗ C) (Γ ++ Δ) Δ' ∘ []≡ {A} (cong (_∷_ C) (++ass Γ))
    ≐〈 refl≐ ∘≐ []≡∷ (++ass Γ {Δ} {Δ'}) 〉 
     []++ (A ⊗ C) Γ Δ ⊗ id ∘ lemma' (A ⊗ C) (Γ ++ Δ) Δ' ∘ []≡ {A ⊗ C} (++ass Γ {Δ} {Δ'})
    ≐〈 asslemma' (A ⊗ C) Γ Δ Δ' 〉 
     lemma' [ A ⊗ C ∣ Γ ] Δ Δ' ∘ []++ (A ⊗ C) Γ (Δ ++ Δ') 
   qed


asslemma : (S : Maybe Tm) → (Γ Δ Δ' : List Tm) → 
       〈〉++ S Γ Δ ⊗ id ∘ lemma S (Γ ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass Γ {Δ} {Δ'})
                         ≐ lemma' 〈 S ∣ Γ 〉 Δ Δ' ∘ 〈〉++ S Γ (Δ ++ Δ') 
asslemma S Γ Δ Δ' = asslemma' (t S) Γ Δ Δ'


{-
asslemma2 : (S : Maybe Tm) → (Γ₀ Γ' Γ Δ' : List Tm) → 
 let 
   q = trans (sym (++ass Γ₀)) (cong₂ _++_ (sym (++ass Γ₀)) refl)
 in --id ⊗ 〈〉++ nothing Γ Δ' 
          {!!} ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ') ∘ 〈〉≡ {S} q
                         ≐ ++〈〉 S (Γ₀ ++ Γ') (Γ ++ Δ') ∘ [ lemma S (Γ₀ ++ Γ') Γ ∣ Δ' ]f
                                      ∘ 〈〉++ S ((Γ₀ ++ Γ') ++ Γ) Δ' 
asslemma2 S Γ Δ Δ' = {!!} 
-}


lemma5' : (C D : Tm) → (Δ : List Tm) → {A : Tm} → (f : C ⇒ A) → 
            f ⊗ id ∘ lemma'' C D Δ ≐ lemma'' A D Δ ∘ [ f ⊗ id ∣ Δ ]f 
lemma5' C D [] f = 
   proof 
     f ⊗ id ∘ id
   ≐〈 sym≐ rid 〉 
     f ⊗ id
   ≐〈 sym≐ lid 〉    
     id ∘ f ⊗ id 
   qed 
lemma5' C D (B ∷ Δ) {A} f =
   proof 
     f ⊗ id ∘ (lemma'' C (D ⊗ B) Δ ∘ [ α ∣ Δ ]f) 
   ≐〈 sym≐ ass 〉
     f ⊗ id ∘ lemma'' C (D ⊗ B) Δ ∘ [ α ∣ Δ ]f
   ≐〈 lemma5' C (D ⊗ B) Δ f ∘≐ refl≐ 〉 
     lemma'' A (D ⊗ B) Δ ∘ [ f ⊗ id ∣ Δ ]f ∘ [ α ∣ Δ ]f
   ≐〈 ass 〉 
     lemma'' A (D ⊗ B) Δ ∘ ([ f ⊗ id ∣ Δ ]f ∘ [ α ∣ Δ ]f)
   ≐〈 refl≐ ∘≐ sym≐ ([∘∣ Δ ]f (f ⊗ id) α) 〉 
     lemma'' A (D ⊗ B) Δ ∘ [ f ⊗ id ∘ α ∣ Δ ]f
   ≐〈 refl≐ ∘≐ sym≐ ([≐∣ Δ ]f (trans≐ nα (refl≐ ⊗≐ f⊗id ∘≐ refl≐))) 〉 
     lemma'' A (D ⊗ B) Δ ∘ [ α ∘ f ⊗ id ⊗ id ∣ Δ ]f 
   ≐〈 refl≐ ∘≐ [∘∣ Δ ]f α (f ⊗ id ⊗ id) 〉 
     lemma'' A (D ⊗ B) Δ ∘ ([ α ∣ Δ ]f ∘ [ f ⊗ id ⊗ id ∣ Δ ]f) 
   ≐〈 sym≐ ass 〉 
     lemma'' A (D ⊗ B) Δ ∘ [ α ∣ Δ ]f ∘ [ f ⊗ id ⊗ id ∣ Δ ]f 
   qed 



lemma5 : (Γ Δ : List Tm) → {A B : Tm} → (f : A ⇒ B) → 
           [ f ∣ Γ ]f ⊗ id ∘ lemma' A Γ Δ ≐ lemma' B Γ Δ ∘ [ f ∣ Γ ++ Δ ]f  
lemma5 [] Δ {A} {B} f = 
  proof 
    f ⊗ id ∘ (lemma'' A I Δ ∘ [ ρ ∣ Δ ]f) 
  ≐〈 sym≐ ass 〉
    f ⊗ id ∘ lemma'' A I Δ ∘ [ ρ ∣ Δ ]f 
  ≐〈 lemma5' A I Δ f ∘≐ refl≐ 〉
    lemma'' B I Δ ∘ [ f ⊗ id ∣ Δ ]f ∘ [ ρ ∣ Δ ]f 
  ≐〈 ass 〉
    lemma'' B I Δ ∘ ([ f ⊗ id ∣ Δ ]f ∘ [ ρ ∣ Δ ]f) 
  ≐〈 refl≐ ∘≐ sym≐ ([∘∣ Δ ]f _ _) 〉
    lemma'' B I Δ ∘ [ f ⊗ id ∘ ρ ∣ Δ ]f 
  ≐〈 refl≐ ∘≐ [≐∣ Δ ]f (sym≐ nρ) 〉
    lemma'' B I Δ ∘ [ ρ ∘ f ∣ Δ ]f 
  ≐〈 refl≐ ∘≐ ([∘∣ Δ ]f _ _) 〉
    lemma'' B I Δ ∘ ([ ρ ∣ Δ ]f ∘ [ f ∣ Δ ]f)
  ≐〈 sym≐ ass 〉
    lemma'' B I Δ ∘ [ ρ ∣ Δ ]f ∘ [ f ∣ Δ ]f 
  qed
lemma5 (C ∷ Γ) Δ {A} {B} f = lemma5 Γ Δ {A ⊗ C} {B ⊗ C} (f ⊗ id)



lemma8 : (A : Tm) → (Δ : List Tm) → l ∘ lemma'' I A Δ ≐ [ l ∣ Δ ]f
lemma8 A [] = sym≐ rid
lemma8 A (C ∷ Δ) = 
  proof 
    l ∘ (lemma'' I (A ⊗ C) Δ ∘ [ α ∣ Δ ]f) 
  ≐〈 sym≐ ass 〉
    l ∘ lemma'' I (A ⊗ C) Δ ∘ [ α ∣ Δ ]f 
  ≐〈 lemma8 (A ⊗ C) Δ ∘≐ refl≐ 〉 
    [ l ∣ Δ ]f ∘ [ α ∣ Δ ]f 
  ≐〈 sym≐ ([∘∣ Δ ]f _ _) 〉 
    [ l ∘ α ∣ Δ ]f 
  ≐〈 [≐∣ Δ ]f lα 〉
    [ l ⊗ id ∣ Δ ]f 
  qed



scomp : {S : Maybe Tm} → {Γ Δ' : List Tm} → {A C : Tm} → 
           [ A ∣ Δ' ] ⇒ C → 〈 S ∣ Γ 〉 ⇒ A  → 〈 S ∣ Γ ++ Δ' 〉 ⇒ C
scomp {S} {Γ} {Δ'} g f = g ∘ [ f ∣ Δ' ]f ∘ 〈〉++ S Γ Δ' 


ccomp : {T : Maybe Tm} → {Γ Δ : List Tm} → (Δ₀ : List Tm) → {Δ' : List Tm} → {A C : Tm} → 
         〈  T ∣ Δ 〉  ⇒ C  → [ I ∣ Γ ] ⇒ A →  Δ ≡ Δ₀ ++ A ∷ Δ' →
                                         〈 T ∣ (Δ₀ ++ Γ) ++ Δ' 〉 ⇒ C
ccomp {T} {Γ} {Δ} Δ₀ {Δ'} {A} {C} g f p =  
     g ∘ 〈〉≡ {T} p ∘ ++〈〉 T  Δ₀ (A ∷ Δ') ∘ [ id ⊗ f ∘ lemma T Δ₀ Γ ∣ Δ' ]f 
                                             ∘ 〈〉++ T (Δ₀ ++ Γ) Δ'
{-
      
〈 T ∣ (Δ₀ ++ Γ) ++ Δ' 〉 ⇒
[ 〈 T ∣ Δ₀ ++ Γ 〉 ∣ Δ' ] ⇒
[ [ 〈 T ∣ Δ₀ 〉 ∣ Γ ] ∣ Δ' ] ⇒
     [ 〈 T ∣ Δ₀ 〉 ⊗ [ I ∣ Γ ] | Δ' ] ⇒ [ 〈 T ∣ Δ₀ 〉 ⊗ A | Δ' ]         
                                   = [ [ 〈 T ∣ Δ₀ 〉 ∣ A ∷ [] ] ∣ Δ' ]
                                    ⇒ [ 〈 T ∣ Δ₀ 〉 ∣ A ∷ Δ' ]
                                    ⇒ [ T ∣ Δ₀ ++ A ∷ Δ' ] ⇒ C
-}


lemma12' : {A Z : Tm}(X Y : Tm)(Γ : List Tm)
  → Y ⇒ X ⊗ Z
  → [ Z ∣ Γ ] ⇒ A
  → [ Y ∣ Γ ] ⇒ X ⊗ A
lemma12' X Y Γ g f = id ⊗ f ∘ (lemma'' X _ Γ ∘ [ g ∣ Γ ]f)

lemma12 : {A : Tm}(X : Tm)(Γ : List Tm)
  → nothing ∣ Γ  ⊢ A
  → [ X ∣ Γ ] ⇒ X ⊗ A
lemma12 X Γ f = lemma12' X X Γ ρ (sound (Il f))

lemma13' : {A X X' Y Z : Tm}(Γ : List Tm)
  → (h : Y ⇒ X ⊗ Z)
  → (f : [ Z ∣ Γ ] ⇒ A)
  → (g : X ⇒ X')
  → g ⊗ id ∘ lemma12' X Y Γ h f ≐ lemma12' X' Y Γ (g ⊗ id ∘ h) f 
lemma13' {A}{X}{X'}{Y}{Z} [] h f g =
  proof
  g ⊗ id ∘ (id ⊗ f ∘ (id ∘ h))
  ≐〈 sym≐ ass 〉
  g ⊗ id ∘ id ⊗ f ∘ (id ∘ h)
  ≐〈 sym≐ f⊗∘ ∘≐ lid 〉
  ((g ∘ id) ⊗ (id ∘ f)) ∘ h
  ≐〈 (sym≐ rid) ⊗≐ lid ∘≐ refl≐ 〉
  (g ⊗ f) ∘ h
  ≐〈 (sym≐ lid) ⊗≐ rid ∘≐ refl≐ 〉
  ((id ∘ g) ⊗ (f ∘ id)) ∘ h
  ≐〈 f⊗∘ ∘≐ refl≐ 〉
  id ⊗ f ∘ g ⊗ id ∘ h
  ≐〈 ass 〉
  id ⊗ f ∘ (g ⊗ id ∘ h)
  ≐〈 refl≐ ∘≐ sym≐ lid 〉
  id ⊗ f ∘ (id ∘ (g ⊗ id ∘ h))
  qed
lemma13' {A}{X}{X'}{Y}{Z} (B ∷ Γ) h f g =
  proof
  g ⊗ id ∘ (id ⊗ f ∘ (lemma'' X (Z ⊗ B) Γ ∘ [ α ∣ Γ ]f ∘ [ h ∣ B ∷ Γ ]f))
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ ass) 〉
  g ⊗ id ∘ (id ⊗ f ∘ (lemma'' X (Z ⊗ B) Γ ∘ ([ α ∣ Γ ]f ∘ [ h ⊗ id ∣ Γ ]f)))
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ (refl≐ ∘≐ sym≐ ([∘∣ Γ ]f _ _))) 〉
  g ⊗ id ∘ (id ⊗ f ∘ (lemma'' X (Z ⊗ B) Γ ∘ [ α ∘ h ⊗ id ∣ Γ ]f))
  ≐〈 lemma13' Γ (α ∘ h ⊗ id) f g 〉
  id ⊗ f ∘ (lemma'' X' (Z ⊗ B) Γ ∘ [ g ⊗ id ∘ (α ∘ (h ⊗ id)) ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ [≐∣ Γ ]f
      (proof
       g ⊗ id ∘ (α ∘ h ⊗ id)
       ≐〈 refl≐ ⊗≐ sym≐ f⊗id ∘≐ refl≐ 〉
       g ⊗ (id ⊗ id) ∘ (α ∘ h ⊗ id)
       ≐〈 sym≐ ass 〉
       g ⊗ (id ⊗ id) ∘ α ∘ h ⊗ id
       ≐〈 sym≐ nα ∘≐ refl≐ 〉
       α ∘ ((g ⊗ id) ⊗ id) ∘ h ⊗ id
       ≐〈 ass 〉
       α ∘ (((g ⊗ id) ⊗ id) ∘ h ⊗ id)
       ≐〈 refl≐ ∘≐ sym≐ f⊗∘ 〉
       α ∘ (g ⊗ id ∘ h) ⊗ (id ∘ id)
       ≐〈 refl≐ ∘≐ refl≐ ⊗≐ lid 〉
       α ∘ (g ⊗ id ∘ h) ⊗ id
       qed) ) 〉
  id ⊗ f ∘ (lemma'' X' (Z ⊗ B) Γ ∘ ([ α ∘ (((g ⊗ id) ∘ h) ⊗ id) ∣ Γ ]f))
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ [∘∣ Γ ]f _ _) 〉
  id ⊗ f ∘ (lemma'' X' (Z ⊗ B) Γ ∘ ([ α ∣ Γ ]f ∘ [ (g ⊗ id ∘ h) ⊗ id ∣ Γ ]f))
  ≐〈 refl≐ ∘≐ sym≐ ass 〉
  id ⊗ f ∘ (lemma'' X' (Z ⊗ B) Γ ∘ [ α ∣ Γ ]f ∘ [ g ⊗ id ∘ h ∣ B ∷ Γ ]f)
  qed

lemma13 : {A X X' : Tm}(Γ : List Tm)
  → (f : nothing ∣ Γ  ⊢ A)
  → (g : X ⇒ X')
  → g ⊗ id ∘ lemma12 X Γ f ≐ lemma12 X' Γ f ∘ [ g ∣ Γ ]f
lemma13 {A}{X}{X'} Γ f g =
  proof
  g ⊗ id ∘ (id ⊗ sound f ∘ (lemma'' X I Γ ∘ [ ρ ∣ Γ ]f))
  ≐〈 lemma13' Γ ρ (sound (Il f)) g 〉
  id ⊗ sound f ∘ (lemma'' X' I Γ ∘ [ g ⊗ id ∘ ρ ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ [≐∣ Γ ]f (sym≐ nρ)) 〉
  id ⊗ sound f ∘ (lemma'' X' I Γ ∘ ([ ρ ∘ g ∣ Γ ]f))
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ [∘∣ Γ ]f _ _) 〉
  id ⊗ sound f ∘ (lemma'' X' I Γ ∘ ([ ρ ∣ Γ ]f ∘ [ g ∣ Γ ]f))
  ≐〈 refl≐ ∘≐ sym≐ ass 〉
  id ⊗ sound f ∘ (lemma'' X' I Γ ∘ [ ρ ∣ Γ ]f ∘ [ g ∣ Γ ]f)
  ≐〈 sym≐ ass 〉
  id ⊗ sound f ∘ (lemma'' X' I Γ ∘ [ ρ ∣ Γ ]f) ∘ [ g ∣ Γ ]f
  qed

lemma6 : (Γ : List Tm) → {A B C : Tm} → (f : B ⇒ C) → 
  lemma'' A C Γ ∘ [ id ⊗ f ∣ Γ ]f ≐ id ⊗ [ f ∣ Γ ]f ∘ lemma'' A B Γ
lemma6 [] f =
  proof
  id ∘ id ⊗ f
  ≐〈 lid 〉
  id ⊗ f
  ≐〈 rid 〉
  id ⊗ f ∘ id
  qed
lemma6 (D ∷ Γ) {A}{B}{C} f =
  proof
  lemma'' A (C ⊗ D) Γ ∘ [ α ∣ Γ ]f ∘ [ id ⊗ f ⊗ id ∣ Γ ]f
  ≐〈 ass  〉
  lemma'' A (C ⊗ D) Γ ∘ ([ α ∣ Γ ]f ∘ [ id ⊗ f ⊗ id ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ sym≐ ([∘∣ Γ ]f _ _) 〉
  lemma'' A (C ⊗ D) Γ ∘ ([ α ∘ id ⊗ f ⊗ id ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ [≐∣ Γ ]f (nα {f = id}{f}{id}) 〉
  lemma'' A (C ⊗ D) Γ ∘ ([ id ⊗ (f ⊗ id) ∘ α ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ [∘∣ Γ ]f _ _ 〉
  lemma'' A (C ⊗ D) Γ ∘ ([ id ⊗ (f ⊗ id) ∣ Γ ]f ∘ [ α ∣ Γ ]f)
  ≐〈 sym≐ ass 〉
  lemma'' A (C ⊗ D) Γ ∘ [ id ⊗ (f ⊗ id) ∣ Γ ]f ∘ [ α ∣ Γ ]f
  ≐〈 lemma6 Γ {A}{B ⊗ D}{C ⊗ D} (f ⊗ id) ∘≐ refl≐ 〉
  id ⊗ [ f ⊗ id ∣ Γ ]f ∘ lemma'' A (B ⊗ D) Γ ∘ [ α ∣ Γ ]f
  ≐〈 ass  〉
  id ⊗ [ f ⊗ id ∣ Γ ]f ∘ (lemma'' A (B ⊗ D) Γ ∘ [ α ∣ Γ ]f)
  qed

lemma16 : {A B C : Tm}(Γ : List Tm)
  → α ∘ lemma'' (A ⊗ B) C Γ ≐ id ⊗ lemma'' B C Γ ∘ lemma'' A (B ⊗ C) Γ ∘ [ α ∣ Γ ]f
lemma16 [] =
  proof
  α ∘ id
  ≐〈 sym≐ rid 〉
  α
  ≐〈 sym≐ lid 〉
  id ∘ α
  ≐〈 rid ∘≐ refl≐ 〉
  id ∘ id ∘ α
  ≐〈 sym≐ f⊗id  ∘≐ refl≐ ∘≐ refl≐  〉
  id ⊗ id ∘ id ∘ α
  qed
lemma16 {A}{B}{C}(D ∷ Γ) =
  proof
  α ∘ (lemma'' (A ⊗ B) (C ⊗ D) Γ ∘ [ α ∣ Γ ]f)
  ≐〈 sym≐ ass 〉
  α ∘ lemma'' (A ⊗ B) (C ⊗ D) Γ ∘ [ α ∣ Γ ]f
  ≐〈 lemma16 Γ ∘≐ refl≐ 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ lemma'' A (B ⊗ (C ⊗ D)) Γ ∘ [ α ∣ Γ ]f ∘ [ α ∣ Γ ]f
  ≐〈 ass 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ lemma'' A (B ⊗ (C ⊗ D)) Γ ∘ ([ α ∣ Γ ]f ∘ [ α ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ sym≐ ([∘∣ Γ ]f _ _) 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ lemma'' A (B ⊗ (C ⊗ D)) Γ ∘ ([ α ∘ α ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ [≐∣ Γ ]f ααα 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ lemma'' A (B ⊗ (C ⊗ D)) Γ ∘ ([ id ⊗ α ∘ (α ∘ α ⊗ id) ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ [∘∣ Γ ]f _ _ 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ lemma'' A (B ⊗ (C ⊗ D)) Γ ∘ ([ id ⊗ α ∣ Γ ]f ∘ [ α ∘ α ⊗ id  ∣ Γ ]f)
  ≐〈 ass 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ (lemma'' A (B ⊗ (C ⊗ D)) Γ ∘ ([ id ⊗ α ∣ Γ ]f ∘ [ α ∘ α ⊗ id  ∣ Γ ]f))
  ≐〈 refl≐ ∘≐ sym≐ ass 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ (lemma'' A (B ⊗ (C ⊗ D)) Γ ∘ [ id ⊗ α ∣ Γ ]f ∘ [ α ∘ α ⊗ id  ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ (lemma6 Γ α ∘≐ refl≐) 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ (id ⊗ [ α ∣ Γ ]f ∘ lemma'' A (B ⊗ C ⊗ D) Γ ∘ [ α ∘ α ⊗ id  ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ [∘∣ Γ ]f _ _) 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ (id ⊗ [ α ∣ Γ ]f ∘ lemma'' A (B ⊗ C ⊗ D) Γ ∘ ([ α ∣ Γ ]f ∘ [ α ⊗ id  ∣ Γ ]f))
  ≐〈 refl≐ ∘≐ sym≐ ass 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ (id ⊗ [ α ∣ Γ ]f ∘ lemma'' A (B ⊗ C ⊗ D) Γ ∘ [ α ∣ Γ ]f ∘ [ α ⊗ id  ∣ Γ ]f)
  ≐〈 sym≐ ass 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ (id ⊗ [ α ∣ Γ ]f ∘ lemma'' A (B ⊗ C ⊗ D) Γ ∘ [ α ∣ Γ ]f) ∘ [ α ⊗ id  ∣ Γ ]f
  ≐〈 refl≐ ∘≐ ass ∘≐ refl≐ 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ (id ⊗ [ α ∣ Γ ]f ∘ (lemma'' A (B ⊗ C ⊗ D) Γ ∘ [ α ∣ Γ ]f)) ∘ [ α ⊗ id  ∣ Γ ]f
  ≐〈 sym≐ ass ∘≐ refl≐ 〉
  id ⊗ lemma'' B (C ⊗ D) Γ ∘ id ⊗ [ α ∣ Γ ]f ∘ (lemma'' A (B ⊗ C ⊗ D) Γ ∘ [ α ∣ Γ ]f) ∘ [ α ⊗ id ∣ Γ ]f
  ≐〈 sym≐ f⊗∘ ∘≐ refl≐ ∘≐ refl≐ 〉
  (id ∘ id) ⊗ (lemma'' B (C ⊗ D) Γ ∘ [ α ∣ Γ ]f) ∘ (lemma'' A (B ⊗ C ⊗ D) Γ ∘ [ α ∣ Γ ]f) ∘ [ α ⊗ id ∣ Γ ]f
  ≐〈 lid ⊗≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
  id ⊗ (lemma'' B (C ⊗ D) Γ ∘ [ α ∣ Γ ]f) ∘ (lemma'' A (B ⊗ C ⊗ D) Γ ∘ [ α ∣ Γ ]f) ∘ [ α ⊗ id ∣ Γ ]f
  qed




lemma15 : {A B C : Tm}(Γ : List Tm)
  → (f : nothing ∣ Γ  ⊢ C)
  → α ∘ lemma12 (A ⊗ B) Γ f ≐ id ⊗ lemma12 B Γ f ∘ lemma'' A B Γ
lemma15 {A}{B}{C} Γ f =
  proof
  α ∘ (id ⊗ sound f ∘ (lemma'' (A ⊗ B) I Γ ∘ [ ρ ∣ Γ ]f))
  ≐〈 sym≐ ass 〉
  α ∘ id ⊗ sound f ∘ (lemma'' (A ⊗ B) I Γ ∘ [ ρ ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ sym≐ f⊗id ⊗≐ refl≐ ∘≐ refl≐ 〉
  α ∘ id ⊗ id ⊗ sound f ∘ (lemma'' (A ⊗ B) I Γ ∘ [ ρ ∣ Γ ]f)
  ≐〈 nα ∘≐ refl≐ 〉
  id ⊗ (id ⊗ sound f) ∘ α ∘ (lemma'' (A ⊗ B) I Γ ∘ [ ρ ∣ Γ ]f)
  ≐〈 ass 〉
  id ⊗ (id ⊗ sound f) ∘ (α ∘ (lemma'' (A ⊗ B) I Γ ∘ [ ρ ∣ Γ ]f))
  ≐〈 refl≐ ∘≐ sym≐ ass 〉
  id ⊗ (id ⊗ sound f) ∘ (α ∘ lemma'' (A ⊗ B) I Γ ∘ [ ρ ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ (lemma16 Γ ∘≐ refl≐) 〉
  id ⊗ (id ⊗ sound f) ∘ (id ⊗ lemma'' B I Γ ∘ lemma'' A (B ⊗ I) Γ ∘ [ α ∣ Γ ]f ∘ [ ρ ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ ass 〉
  id ⊗ (id ⊗ sound f) ∘ (id ⊗ lemma'' B I Γ ∘ lemma'' A (B ⊗ I) Γ ∘ ([ α ∣ Γ ]f ∘ [ ρ ∣ Γ ]f))
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ sym≐ ([∘∣ Γ ]f _ _)) 〉
  id ⊗ (id ⊗ sound f) ∘ (id ⊗ lemma'' B I Γ ∘ lemma'' A (B ⊗ I) Γ ∘ ([ α ∘ ρ ∣ Γ ]f))
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ [≐∣ Γ ]f αρ) 〉
  id ⊗ (id ⊗ sound f) ∘ (id ⊗ lemma'' B I Γ ∘ lemma'' A (B ⊗ I) Γ ∘ [ id ⊗ ρ ∣ Γ ]f)
  ≐〈 refl≐ ∘≐ ass 〉
  id ⊗ (id ⊗ sound f) ∘ (id ⊗ lemma'' B I Γ ∘ (lemma'' A (B ⊗ I) Γ ∘ [ id ⊗ ρ ∣ Γ ]f))
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ lemma6 Γ ρ) 〉
  id ⊗ (id ⊗ sound f) ∘ (id ⊗ lemma'' B I Γ ∘ (id ⊗ [ ρ ∣ Γ ]f ∘ lemma'' A B Γ))
  ≐〈 refl≐ ∘≐ sym≐ ass 〉
  id ⊗ (id ⊗ sound f) ∘ (id ⊗ lemma'' B I Γ ∘ id ⊗ [ ρ ∣ Γ ]f ∘ lemma'' A B Γ)
  ≐〈 refl≐ ∘≐ (sym≐ f⊗∘ ∘≐ refl≐) 〉
  id ⊗ (id ⊗ sound f) ∘ ((id ∘ id) ⊗ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∘ lemma'' A B Γ)
  ≐〈 refl≐ ∘≐ (lid ⊗≐ refl≐ ∘≐ refl≐) 〉
  id ⊗ (id ⊗ sound f) ∘ (id ⊗ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∘ lemma'' A B Γ)
  ≐〈 sym≐ ass 〉
  id ⊗ (id ⊗ sound f) ∘ id ⊗ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∘ lemma'' A B Γ
  ≐〈 sym≐ f⊗∘ ∘≐ refl≐ 〉
  (id ∘ id) ⊗ (id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f)) ∘ lemma'' A B Γ
  ≐〈 lid ⊗≐ refl≐ ∘≐ refl≐ 〉
  id ⊗ (id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f)) ∘ lemma'' A B Γ
  qed

lemma14 : (A B : Tm)(Γ Δ : List Tm)
  → id ⊗ []++ B Γ Δ ∘ lemma'' A B (Γ ++ Δ) ≐
      lemma'' A [ B ∣ Γ ] Δ ∘ [ lemma'' A B Γ ∣ Δ ]f ∘ []++ (A ⊗ B) Γ Δ
lemma14 A B [] Δ =
  proof
  id ⊗ id ∘ lemma'' A B Δ
  ≐〈 f⊗id ∘≐ refl≐ 〉
  id ∘ lemma'' A B Δ
  ≐〈 lid 〉
  lemma'' A B Δ
  ≐〈 rid 〉
  lemma'' A B Δ ∘ id
  ≐〈 refl≐ ∘≐ sym≐ ([id∣ Δ ]f) 〉
  lemma'' A B Δ ∘ [ id ∣ Δ ]f
  ≐〈 rid 〉
  lemma'' A B Δ ∘ [ id ∣ Δ ]f ∘ id
  qed
lemma14 A B (C ∷ Γ) Δ =
  proof
  id ⊗ []++ (B ⊗ C) Γ Δ ∘ (lemma'' A (B ⊗ C) (Γ ++ Δ) ∘ [ α ∣ Γ ++ Δ ]f)
  ≐〈 sym≐ ass 〉
  id ⊗ []++ (B ⊗ C) Γ Δ ∘ lemma'' A (B ⊗ C) (Γ ++ Δ) ∘ [ α ∣ Γ ++ Δ ]f
  ≐〈 lemma14 A (B ⊗ C) Γ Δ ∘≐ refl≐ 〉
  lemma'' A [ B ⊗ C ∣ Γ ] Δ ∘ [ lemma'' A (B ⊗ C) Γ ∣ Δ ]f ∘ []++ (A ⊗ (B ⊗ C)) Γ Δ ∘ [ α ∣ Γ ++ Δ ]f
  ≐〈 ass 〉
  lemma'' A [ B ⊗ C ∣ Γ ] Δ ∘ [ lemma'' A (B ⊗ C) Γ ∣ Δ ]f ∘ ([]++ (A ⊗ (B ⊗ C)) Γ Δ ∘ [ α ∣ Γ ++ Δ ]f)
  ≐〈 refl≐ ∘≐ []++n  α Γ Δ 〉
  lemma'' A [ B ⊗ C ∣ Γ ] Δ ∘ [ lemma'' A (B ⊗ C) Γ ∣ Δ ]f ∘ ([ [ α ∣ Γ ]f ∣ Δ ]f ∘ []++ (A ⊗ B ⊗ C) Γ Δ)
  ≐〈 sym≐ ass 〉
  lemma'' A [ B ⊗ C ∣ Γ ] Δ ∘ [ lemma'' A (B ⊗ C) Γ ∣ Δ ]f ∘ [ [ α ∣ Γ ]f ∣ Δ ]f ∘ []++ (A ⊗ B ⊗ C) Γ Δ
  ≐〈 ass ∘≐ refl≐ 〉
  lemma'' A [ B ⊗ C ∣ Γ ] Δ ∘ ([ lemma'' A (B ⊗ C) Γ ∣ Δ ]f ∘ [ [ α ∣ Γ ]f ∣ Δ ]f) ∘ []++ (A ⊗ B ⊗ C) Γ Δ
  ≐〈 refl≐ ∘≐ sym≐ ([∘∣ Δ ]f _ _) ∘≐ refl≐ 〉
  lemma'' A [ B ⊗ C ∣ Γ ] Δ ∘ [ lemma'' A (B ⊗ C) Γ ∘ [ α ∣ Γ ]f ∣ Δ ]f ∘ []++ (A ⊗ B ⊗ C) Γ Δ
  qed

lemma11'' : (A B X : Tm)(Γ' Γ Δ : List Tm){C : Tm}
  → (g : X ⇒ A ⊗ B)
  → (f : nothing ∣ Γ  ⊢ C)
  → id ⊗ ++[] B Γ' (C ∷ Δ) ∘
      (id ⊗ [ id ⊗ sound f ∘ lemma' B Γ' Γ ∣ Δ ]f ∘
        (id ⊗ []++ B (Γ' ++ Γ) Δ ∘
          (lemma'' A B ((Γ' ++ Γ) ++ Δ) ∘
            [ g ∣ (Γ' ++ Γ) ++ Δ ]f ∘ id)))
    ≐
    lemma'' A B (Γ' ++ C ∷ Δ) ∘ [ g ∣ Γ' ++ C ∷ Δ ]f ∘
      (id ∘
        (++[] X Γ' (C ∷ Δ) ∘
          ([ id ⊗ sound f ∘ lemma' X Γ' Γ ∣ Δ ]f ∘
            []++ X (Γ' ++ Γ) Δ)))
lemma11'' A B X [] Γ Δ {C} g f =
  proof
  id ⊗ id ∘
      (id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
       (id ⊗ []++ B Γ Δ ∘ (lemma'' A B (Γ ++ Δ) ∘ [ g ∣ Γ ++ Δ ]f ∘ id)))
  ≐〈 f⊗id ∘≐ (refl≐ ∘≐ (refl≐ ∘≐ sym≐ rid)) 〉
  id ∘
      (id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
       (id ⊗ []++ B Γ Δ ∘ (lemma'' A B (Γ ++ Δ) ∘ [ g ∣ Γ ++ Δ ]f)))
  ≐〈 lid 〉
  id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
       (id ⊗ []++ B Γ Δ ∘ (lemma'' A B (Γ ++ Δ) ∘ [ g ∣ Γ ++ Δ ]f))
  ≐〈 sym≐ ass 〉
  id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
    id ⊗ []++ B Γ Δ ∘
     (lemma'' A B (Γ ++ Δ) ∘ [ g ∣ Γ ++ Δ ]f)
  ≐〈 ass 〉
  id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
    (id ⊗ []++ B Γ Δ ∘ (lemma'' A B (Γ ++ Δ) ∘ [ g ∣ Γ ++ Δ ]f))
  ≐〈 refl≐ ∘≐ sym≐ ass 〉
  id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
    (id ⊗ []++ B Γ Δ ∘ lemma'' A B (Γ ++ Δ) ∘ [ g ∣ Γ ++ Δ ]f)
  ≐〈 refl≐ ∘≐ (lemma14 A B Γ Δ ∘≐ refl≐) 〉
  id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
    (lemma'' A ([ B ∣ Γ ]) Δ ∘ [ lemma'' A B Γ ∣ Δ ]f ∘ []++ (A ⊗ B) Γ Δ ∘ [ g ∣ Γ ++ Δ ]f)
  ≐〈 refl≐ ∘≐ ass 〉
  id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
    (lemma'' A ([ B ∣ Γ ]) Δ ∘ [ lemma'' A B Γ ∣ Δ ]f ∘ ([]++ (A ⊗ B) Γ Δ ∘ [ g ∣ Γ ++ Δ ]f))
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ []++n g Γ Δ) 〉
  id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
    (lemma'' A ([ B ∣ Γ ]) Δ ∘ [ lemma'' A B Γ ∣ Δ ]f ∘ ([ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ))
  ≐〈 sym≐ ass 〉
  id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
    (lemma'' A ([ B ∣ Γ ]) Δ ∘ [ lemma'' A B Γ ∣ Δ ]f) ∘ ([ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 sym≐ ass ∘≐ refl≐ 〉
  id ⊗ [ id ⊗ sound f ∘ (lemma'' B I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
    lemma'' A ([ B ∣ Γ ]) Δ ∘ [ lemma'' A B Γ ∣ Δ ]f ∘ ([ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 sym≐ ass 〉
  id ⊗ [ lemma12 B Γ f ∣ Δ ]f ∘ lemma'' A [ B ∣ Γ ] Δ ∘ [ lemma'' A B Γ ∣ Δ ]f ∘ [ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ
  ≐〈 sym≐ (lemma6 Δ (lemma12 B Γ f)) ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
  lemma'' A (B ⊗ C) Δ ∘ [ id ⊗ lemma12 B Γ f ∣ Δ ]f ∘ [ lemma'' A B Γ ∣ Δ ]f ∘ [ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ
  ≐〈 ass ∘≐ refl≐ ∘≐ refl≐ 〉
  lemma'' A (B ⊗ C) Δ ∘ ([ id ⊗ lemma12 B Γ f ∣ Δ ]f ∘ [ lemma'' A B Γ ∣ Δ ]f) ∘ [ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ
  ≐〈 ass ∘≐ refl≐ 〉
  lemma'' A (B ⊗ C) Δ ∘ ([ id ⊗ lemma12 B Γ f ∣ Δ ]f ∘ [ lemma'' A B Γ ∣ Δ ]f ∘ [ [ g ∣ Γ ]f ∣ Δ ]f) ∘ []++ X Γ Δ
  ≐〈 ass 〉
  lemma'' A (B ⊗ C) Δ ∘ ([ id ⊗ lemma12 B Γ f ∣ Δ ]f ∘ [ lemma'' A B Γ ∣ Δ ]f ∘ [ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 refl≐ ∘≐ (sym≐ ([∘∣ Δ ]f _ _) ∘≐ refl≐ ∘≐ refl≐) 〉
  lemma'' A (B ⊗ C) Δ ∘ ([ id ⊗ lemma12 B Γ f ∘ lemma'' A B Γ ∣ Δ ]f ∘ [ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 refl≐ ∘≐ ([≐∣ Δ ]f (sym≐ (lemma15 Γ f))  ∘≐ refl≐ ∘≐ refl≐) 〉
  lemma'' A (B ⊗ C) Δ ∘ ([ α ∘ lemma12 (A ⊗ B) Γ f ∣ Δ ]f ∘ [ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 refl≐ ∘≐ ([∘∣ Δ ]f _ _  ∘≐ refl≐ ∘≐ refl≐) 〉
  lemma'' A (B ⊗ C) Δ ∘ ([ α ∣ Δ ]f ∘ [ lemma12 (A ⊗ B) Γ f ∣ Δ ]f ∘ [ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 refl≐ ∘≐ (ass ∘≐ refl≐) 〉
  lemma'' A (B ⊗ C) Δ ∘ ([ α ∣ Δ ]f ∘ ([ lemma12 (A ⊗ B) Γ f ∣ Δ ]f ∘ [ [ g ∣ Γ ]f ∣ Δ ]f) ∘ []++ X Γ Δ)
  ≐〈 refl≐ ∘≐ ass 〉
  lemma'' A (B ⊗ C) Δ ∘ ([ α ∣ Δ ]f ∘ ([ lemma12 (A ⊗ B) Γ f ∣ Δ ]f ∘ [ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ))
  ≐〈 sym≐ ass 〉
  lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f ∘ ([ lemma12 (A ⊗ B) Γ f ∣ Δ ]f ∘ [ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 refl≐ ∘≐ (sym≐ ([∘∣ Δ ]f _ _)  ∘≐ refl≐) 〉
  lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f ∘ ([ lemma12 (A ⊗ B) Γ f ∘ [ g ∣ Γ ]f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 refl≐ ∘≐ ([≐∣ Δ ]f (sym≐ (lemma13 Γ f g)) ∘≐ refl≐) 〉
  lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f ∘ ([ g ⊗ id ∘ lemma12 X Γ f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 refl≐ ∘≐ ([∘∣ Δ ]f _ _ ∘≐ refl≐) 〉
  lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f ∘ ([ g ⊗ id ∣ Δ ]f ∘ [ lemma12 X Γ f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 refl≐ ∘≐ ass 〉
  lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f ∘ ([ g ⊗ id ∣ Δ ]f ∘ ([ lemma12 X Γ f ∣ Δ ]f ∘ []++ X Γ Δ))
  ≐〈 sym≐ ass 〉
  lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f ∘ [ g ⊗ id ∣ Δ ]f ∘ ([ lemma12 X Γ f ∣ Δ ]f ∘ []++ X Γ Δ)
  ≐〈 refl≐ ∘≐ sym≐ lid 〉
  lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f ∘ [ g ⊗ id ∣ Δ ]f ∘
  (id ∘
    ([ id ⊗ sound f ∘ (lemma'' X I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
     []++ X Γ Δ))
  ≐〈 refl≐ ∘≐ (refl≐ ∘≐ sym≐ lid) 〉
  lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f ∘ [ g ⊗ id ∣ Δ ]f ∘
  (id ∘
   (id ∘
    ([ id ⊗ sound f ∘ (lemma'' X I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘
     []++ X Γ Δ)))
  qed
lemma11'' A B X (D ∷ Γ') Γ Δ g f =
  trans≐ (refl≐ ∘≐ (refl≐ ∘≐ (refl≐ ∘≐ (trans≐ ass (refl≐ ∘≐ sym≐ ([∘∣ (Γ' ++ Γ) ++ Δ ]f α (g ⊗ id))) ∘≐ refl≐))))
         (trans≐ (lemma11'' A (B ⊗ D) (X ⊗ D) Γ' Γ Δ (α ∘ g ⊗ id) f)
                 (trans≐ (refl≐ ∘≐ [∘∣ Γ' ++ _ ∷ Δ ]f α (g ⊗ id)) (sym≐ ass) ∘≐ refl≐))

lemma11' : (A : Tm)(Γ₀ Γ' Γ Δ : List Tm){C : Tm}
  → (f : nothing ∣ Γ  ⊢ C)
  → id ⊗ ++[] I Γ' (C ∷ Δ) ∘
      (id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ ]f ∘
        (id ⊗ []++ I (Γ' ++ Γ) Δ ∘
          (lemma' A Γ₀ ((Γ' ++ Γ) ++ Δ) ∘
            []≡ {A} (trans (sym (++ass Γ₀)) (cong₂ _++_ (sym (++ass Γ₀ {Γ'} {Γ})) refl)))))
    ≐
    lemma' A Γ₀ (Γ' ++ C ∷ Δ) ∘
      ([]≡ {A} (sym (++ass Γ₀)) ∘
        (++[] A (Γ₀ ++ Γ') (C ∷ Δ) ∘
          ([ id ⊗ sound f ∘ lemma' A (Γ₀ ++ Γ') Γ ∣ Δ ]f ∘
            []++ A ((Γ₀ ++ Γ') ++ Γ) Δ)))
lemma11' A [] Γ' Γ Δ f = lemma11'' A I A Γ' Γ Δ ρ f
lemma11' A (B ∷ Γ₀) Γ' Γ Δ f =
    trans≐ (refl≐ ∘≐ (refl≐ ∘≐ (refl≐ ∘≐ (refl≐ ∘≐ trans≐ ([]≡eq _ _) ([]≡∷ _)))))
           (trans≐ (lemma11' (A ⊗ B) Γ₀ Γ' Γ Δ f)
                   (refl≐ ∘≐ (sym≐ (trans≐ ([]≡eq _ _) ([]≡∷ _)) ∘≐ (refl≐ ∘≐ (refl≐ ∘≐ refl≐)))))

lemma11 : (S : Maybe Tm)(Γ₀ Γ' Γ Δ : List Tm){A : Tm}
  → (f : nothing ∣ Γ  ⊢ A)
  → _≐_ {〈 S ∣ ((Γ₀ ++ Γ') ++ Γ) ++ Δ 〉}{〈 S ∣ Γ₀ 〉 ⊗ 〈 nothing ∣ Γ' ++ A ∷ Δ 〉}
    (id ⊗ ++[] I Γ' (A ∷ Δ) ∘
      (id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ ]f ∘
        (id ⊗ []++ I (Γ' ++ Γ) Δ ∘
          (lemma S Γ₀ ((Γ' ++ Γ) ++ Δ) ∘
            〈〉≡ {S} (trans (sym (++ass Γ₀)) (cong₂ _++_ (sym (++ass Γ₀ {Γ'} {Γ})) refl))))))
    (lemma S Γ₀ (Γ' ++ A ∷ Δ) ∘
      (〈〉≡ {S} (sym (++ass Γ₀)) ∘
        (++〈〉 S (Γ₀ ++ Γ') (A ∷ Δ) ∘
          ([ id ⊗ sound f ∘ lemma S (Γ₀ ++ Γ') Γ ∣ Δ ]f ∘
            〈〉++ S ((Γ₀ ++ Γ') ++ Γ) Δ))))
lemma11 S Γ₀ Γ' Γ Δ f = lemma11' (t S) Γ₀ Γ' Γ Δ f

mutual
  soundscut : {S : Maybe Tm} → {Γ Δ' : List Tm} → {A C : Tm} → 
       (f : S ∣ Γ ⊢ A) → (g : just A ∣ Δ' ⊢ C) → 
                 sound (scut f g) ≐ scomp {S} {Γ} {Δ'} (sound g) (sound f)
  soundscut {.(just _)} {.[]} {Δ'} ax g = 
    proof 
      sound g 
    ≐〈 rid 〉 
      sound g ∘ id 
    ≐〈 refl≐ ∘≐ sym≐ [id∣ Δ' ]f 〉 
      sound g ∘ [ id ∣ Δ' ]f  
    ≐〈 rid 〉 
      sound g ∘ [ id ∣ Δ' ]f ∘ id 
    qed
  soundscut {.nothing} {.(B ∷ Γ)} {Δ'} (uf {Γ} {B} f) g = 
    proof 
      sound (scut f g) ∘ [ l ∣ Γ ++ Δ' ]f 
    ≐〈 soundscut f g ∘≐ refl≐ 〉
      sound g ∘ [ sound f ∣ Δ' ]f ∘ []++ B Γ Δ' ∘ [ l ∣ Γ ++ Δ' ]f 
    ≐〈 ass 〉
      sound g ∘ [ sound f ∣ Δ' ]f ∘ ([]++ B Γ Δ' ∘ [ l ∣ Γ ++ Δ' ]f) 
    ≐〈 refl≐ ∘≐ []++n l Γ Δ' 〉
      sound g ∘ [ sound f ∣ Δ' ]f ∘ ([ [ l ∣ Γ ]f ∣ Δ' ]f ∘ []++ (I ⊗ B) Γ Δ') 
    ≐〈 sym≐ ass 〉
      sound g ∘ [ sound f ∣ Δ' ]f ∘ [ [ l ∣ Γ ]f ∣ Δ' ]f ∘ []++ (I ⊗ B) Γ Δ' 
    ≐〈 ass ∘≐ refl≐ 〉
      sound g ∘ ([ sound f ∣ Δ' ]f ∘ [ [ l ∣ Γ ]f ∣ Δ' ]f) ∘ []++ (I ⊗ B) Γ Δ' 
    ≐〈 refl≐ ∘≐ sym≐ ([∘∣ Δ' ]f (sound f) ([ l ∣ Γ ]f)) ∘≐ refl≐ 〉
      sound g ∘ [ sound f ∘ [ l ∣ Γ ]f ∣ Δ' ]f ∘ []++ (I ⊗ B) Γ Δ' 
    qed
  soundscut {.nothing} {.[]} {.[]} Ir ax = trans≐ rid rid
  soundscut {.nothing} {.[]} {.(Γ ++ Γ')} Ir (⊗r {.(just _)} {Γ} {Γ'} g g') =
    proof 
      sound (scut Ir g) ⊗ sound g' ∘ lemma' I Γ Γ' 
    ≐〈 soundscut Ir g ⊗≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ [ id ∣ Γ ]f ∘ id) ⊗ sound g' ∘ lemma' I Γ Γ' 
    ≐〈 sym≐ rid ⊗≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ [ id ∣ Γ ]f) ⊗ sound g' ∘ lemma' I Γ Γ' 
    ≐〈 (refl≐ ∘≐ [id∣ Γ ]f) ⊗≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ id) ⊗ sound g' ∘ lemma' I Γ Γ' 
    ≐〈 sym≐ rid ⊗≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ lemma' I Γ Γ' 
    ≐〈 rid 〉
      sound g ⊗ sound g' ∘ lemma' I Γ Γ' ∘ id
    ≐〈 refl≐ ∘≐ sym≐ [id∣ Γ ++ Γ' ]f 〉
      sound g ⊗ sound g' ∘ lemma' I Γ Γ' ∘ [ id ∣ Γ ++ Γ' ]f
    ≐〈 rid 〉
      sound g ⊗ sound g' ∘ lemma' I Γ Γ' ∘ [ id ∣ Γ ++ Γ' ]f ∘ id 
    qed
  soundscut {.nothing} {.[]} {Δ'} Ir (Il g) = 
    proof 
      sound g 
    ≐〈 rid 〉 
      sound g ∘ id 
    ≐〈 refl≐ ∘≐ sym≐ [id∣ Δ' ]f 〉 
      sound g ∘ [ id ∣ Δ' ]f  
    ≐〈 rid 〉 
      sound g ∘ [ id ∣ Δ' ]f ∘ id 
    qed
  soundscut {.S} {.(Γ ++ Γ')} {.[]} (⊗r {S} {Γ} {Γ'} f f') ax =
    let
      h = sound (⊗r {S} {Γ} {Γ'} f f')     
    in proof 
      sound (subeq (++ru (Γ ++ Γ')) (⊗r f f')) 
    ≐〈 soundsubeq (++ru (Γ ++ Γ')) (⊗r f f') 〉
      h ∘ 〈〉≡ {S} (++ru (Γ ++ Γ'))
    ≐〈 refl≐ ∘≐ rulemma S (Γ ++ Γ') 〉
      h ∘ 〈〉++ S (Γ ++ Γ') [] 
    ≐〈 sym≐ lid ∘≐ refl≐ 〉
      id ∘ h ∘ 〈〉++ S (Γ ++ Γ') [] 
    qed
  soundscut (⊗r {S} {Γ} {Γ'} {A} {B} f f') (⊗r {.(just (A ⊗ B))} {Δ} {Δ'} g g') = 
    let
      h = sound (⊗r {S} {Γ} {Γ'} f f')     
    in proof 
      sound (subeq (++ass (Γ ++ Γ')) (⊗r (scut (⊗r f f') g) g')) 
    ≐〈 soundsubeq  (++ass (Γ ++ Γ')) (⊗r (scut (⊗r f f') g) g') 〉
      sound (scut (⊗r f f') g) ⊗ sound g' ∘ 
            lemma S ((Γ ++ Γ') ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass (Γ ++ Γ'))
    ≐〈 soundscut (⊗r f f') g ⊗≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ [ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ) ⊗ sound g' ∘ 
            lemma S ((Γ ++ Γ') ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass (Γ ++ Γ'))
    ≐〈 ass ⊗≐ rid ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ ([ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ)) ⊗ (sound g' ∘ id) ∘ 
            lemma S ((Γ ++ Γ') ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass (Γ ++ Γ'))
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ) ⊗ id ∘ 
            lemma S ((Γ ++ Γ') ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass (Γ ++ Γ'))
    ≐〈 ass ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ (([ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ) ⊗ id ∘ 
            lemma S ((Γ ++ Γ') ++ Δ) Δ') ∘ 〈〉≡ {S} (++ass (Γ ++ Γ'))
    ≐〈 ass 〉
      sound g ⊗ sound g' ∘ (([ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ) ⊗ id ∘ 
            lemma S ((Γ ++ Γ') ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass (Γ ++ Γ')))
    ≐〈 refl≐ ∘≐ (refl≐ ⊗≐ rid ∘≐ refl≐ ∘≐ refl≐) 〉 
      sound g ⊗ sound g' ∘ (([ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ) ⊗ (id ∘ id) ∘ 
            lemma S ((Γ ++ Γ') ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass (Γ ++ Γ')))
    ≐〈 refl≐ ∘≐ (f⊗∘ ∘≐ refl≐ ∘≐ refl≐) 〉 
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ⊗ id ∘ 〈〉++ S (Γ ++ Γ') Δ ⊗ id ∘ 
            lemma S ((Γ ++ Γ') ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass (Γ ++ Γ')))
    ≐〈 refl≐ ∘≐ ass 〉 
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ⊗ id ∘ 〈〉++ S (Γ ++ Γ') Δ ⊗ id ∘ 
            (lemma S ((Γ ++ Γ') ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass (Γ ++ Γ'))))
    ≐〈 refl≐ ∘≐ ass 〉 
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ⊗ id ∘ (〈〉++ S (Γ ++ Γ') Δ ⊗ id 
            ∘ (lemma S ((Γ ++ Γ') ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass (Γ ++ Γ')))))
    ≐〈 refl≐ ∘≐ (refl≐ ∘≐ sym≐ ass) 〉 
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ⊗ id ∘ (〈〉++ S (Γ ++ Γ') Δ ⊗ id 
            ∘ lemma S ((Γ ++ Γ') ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass (Γ ++ Γ'))))
    ≐〈 refl≐ ∘≐ (refl≐ ∘≐ asslemma S (Γ ++ Γ') Δ Δ') 〉 
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ⊗ id ∘ (lemma' 〈 S ∣ Γ ++ Γ' 〉 Δ Δ'
            ∘ 〈〉++ S (Γ ++ Γ') (Δ ++ Δ')))
    ≐〈 refl≐ ∘≐ sym≐ ass 〉 
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ⊗ id ∘ lemma' 〈 S ∣ Γ ++ Γ' 〉 Δ Δ'
            ∘ 〈〉++ S (Γ ++ Γ') (Δ ++ Δ'))
    ≐〈 refl≐ ∘≐ (lemma5 Δ Δ' h ∘≐ refl≐) 〉 
      sound g ⊗ sound g' ∘ (lemma' (A ⊗ B) Δ Δ' ∘
            [ h ∣ Δ ++ Δ' ]f ∘ 〈〉++ S (Γ ++ Γ') (Δ ++ Δ'))
    ≐〈 sym≐ ass 〉 
      sound g ⊗ sound g' ∘ (lemma' (_ ⊗ _) Δ Δ' ∘
            [ h ∣ Δ ++ Δ' ]f) ∘ 〈〉++ S (Γ ++ Γ') (Δ ++ Δ')
    ≐〈 sym≐ ass ∘≐ refl≐ 〉 
      sound g ⊗ sound g' ∘ lemma' (_ ⊗ _) Δ Δ' ∘
            [ h ∣ Δ ++ Δ' ]f ∘ 〈〉++ S (Γ ++ Γ') (Δ ++ Δ') 
      qed
  soundscut {.S} {.(Γ ++ Γ')} (⊗r {S} {Γ} {Γ'} f f') (⊗l {Δ} {A} {B} {C} g) = 
    proof 
      sound (ccut Γ f' (scut f g) refl) 
    ≐〈 soundccut Γ f' (scut f g) refl 〉
      sound (scut f g) ∘ id 
          ∘ ++〈〉 S Γ (B ∷ Δ) ∘ [ id ⊗ sound f' ∘ lemma S Γ Γ' ∣ Δ ]f
                                       ∘ 〈〉++ S (Γ ++ Γ') Δ
    ≐〈 sym≐ rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉   
      sound (scut f g)
           ∘ ++〈〉 S Γ (B ∷ Δ) ∘ [ id ⊗ sound f' ∘ lemma S Γ Γ' ∣ Δ ]f
                                       ∘ 〈〉++ S (Γ ++ Γ') Δ
    ≐〈 soundscut f g ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉 
      sound g ∘ [ sound f ⊗ id ∣ Δ ]f ∘ 〈〉++ S Γ (B ∷ Δ)
          ∘ ++〈〉 S Γ (B ∷ Δ) ∘ [ id ⊗ sound f' ∘ lemma S Γ Γ' ∣ Δ ]f
                                       ∘ 〈〉++ S (Γ ++ Γ') Δ
    ≐〈 ass ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ∘ [ sound f ⊗ id ∣ Δ ]f ∘ (〈〉++ S Γ (B ∷ Δ)
          ∘ ++〈〉 S Γ (B ∷ Δ)) ∘ [ id ⊗ sound f' ∘ lemma S Γ Γ' ∣ Δ ]f
                                       ∘ 〈〉++ S (Γ ++ Γ') Δ
    ≐〈 refl≐ ∘≐  〈〉++iso S Γ (B ∷ Δ) ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ∘ [ sound f ⊗ id ∣ Δ ]f ∘ id 
          ∘ [ id ⊗ sound f' ∘ lemma S Γ Γ' ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ
    ≐〈 sym≐ rid ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ∘ [ sound f ⊗ id ∣ Δ ]f 
          ∘ [ id ⊗ sound f' ∘ lemma S Γ Γ' ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ
    ≐〈 ass ∘≐ refl≐ 〉
      sound g ∘ ([ sound f ⊗ id ∣ Δ ]f 
          ∘ [ id ⊗ sound f' ∘ lemma S Γ Γ' ∣ Δ ]f) ∘ 〈〉++ S (Γ ++ Γ') Δ
    ≐〈 refl≐ ∘≐ sym≐ ([∘∣ Δ ]f _ _) ∘≐ refl≐ 〉
      sound g ∘ ([ sound f ⊗ id ∘ (id ⊗ sound f' ∘ lemma S Γ Γ') ∣ Δ ]f) 
                                                  ∘ 〈〉++ S (Γ ++ Γ') Δ
    ≐〈 refl≐ ∘≐ sym≐ ([≐∣ Δ ]f ass) ∘≐ refl≐ 〉
      sound g ∘ ([ sound f ⊗ id ∘ id ⊗ sound f' ∘ lemma S Γ Γ' ∣ Δ ]f) 
                                                  ∘ 〈〉++ S (Γ ++ Γ') Δ
    ≐〈 refl≐ ∘≐ sym≐ ([≐∣ Δ ]f (f⊗∘ ∘≐ refl≐)) ∘≐ refl≐ 〉
      sound g ∘ ([ (sound f ∘ id) ⊗ (id ∘ sound f') ∘ lemma S Γ Γ' ∣ Δ ]f) 
                                                  ∘ 〈〉++ S (Γ ++ Γ') Δ
    ≐〈 refl≐ ∘≐ [≐∣ Δ ]f (sym≐ rid ⊗≐ lid ∘≐ refl≐) ∘≐ refl≐ 〉
      sound g ∘ [ sound (⊗r {S} {Γ} {Γ'} f f') ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ
    qed
  soundscut (Il f) g = soundscut f g
  soundscut (⊗l f) g = soundscut f g

  soundccut : {T : Maybe Tm} → {Γ Δ : List Tm} →  (Δ₀ : List Tm) → {Δ' : List Tm} → {A C : Tm}  → 
       (f : nothing ∣ Γ ⊢ A) → (g : T ∣ Δ ⊢ C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
                 sound (ccut Δ₀ f g p) 
                  ≐ ccomp {T} {Γ} {Δ} Δ₀ {Δ'} {A} {C} (sound g) (sound f) p
  soundccut Δ₀ f ax p = ⊥-elim (lemma[] Δ₀ p)
  soundccut Δ₀ f (uf {Δ} {B} g) p with lemma∷ Δ₀ p 
  soundccut {.nothing} {Γ} {._} .[] {.Δ} {.B} f (uf {Δ} {B} g) p 
     | inj₁ (refl , refl , refl) = 
        proof 
          sound (scut f g) 
        ≐〈 soundscut f g 〉
          sound g ∘ [ sound f ∣ Δ ]f ∘ []++ I Γ Δ
        ≐〈 refl≐ ∘≐ [≐∣ Δ ]f rid ∘≐ refl≐ 〉
          sound g ∘ [ sound f ∘ id ∣ Δ ]f ∘ []++ I Γ Δ
        ≐〈 refl≐ ∘≐ [≐∣ Δ ]f (refl≐ ∘≐ sym≐ [id∣ Γ ]f) ∘≐ refl≐ 〉
          sound g ∘ [ sound f ∘ [ id ∣ Γ ]f ∣ Δ ]f ∘ []++ I Γ Δ
        ≐〈 refl≐ ∘≐ [≐∣ Δ ]f (refl≐ ∘≐ [≐∣ Γ ]f (sym≐ lρ)) ∘≐ refl≐ 〉
          sound g ∘ [ sound f ∘ [ l ∘ ρ ∣ Γ ]f ∣ Δ ]f ∘ []++ I Γ Δ
        ≐〈 refl≐ ∘≐ [≐∣ Δ ]f (refl≐ ∘≐ [∘∣ Γ ]f _ _ ) ∘≐ refl≐ 〉
          sound g ∘ [ sound f ∘ ([ l ∣ Γ ]f ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f ∘ []++ I Γ Δ
        ≐〈 refl≐ ∘≐ [≐∣ Δ ]f (refl≐ ∘≐ (sym≐ (lemma8 I Γ) ∘≐ refl≐)) ∘≐ refl≐ 〉
          sound g  
                ∘ [ sound f ∘ (l ∘ lemma'' I I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f
                ∘ []++ I Γ Δ 
        ≐〈 refl≐ ∘≐ [≐∣ Δ ]f (refl≐ ∘≐ ass) ∘≐ refl≐ 〉
          sound g  
                ∘ [ sound f ∘ (l ∘ (lemma'' I I Γ ∘ [ ρ ∣ Γ ]f)) ∣ Δ ]f
                ∘ []++ I Γ Δ 
        ≐〈 refl≐ ∘≐ [≐∣ Δ ]f (sym≐ ass) ∘≐ refl≐ 〉
          sound g  
                ∘ [ sound f ∘ l ∘ (lemma'' I I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f
                ∘ []++ I Γ Δ 
        ≐〈 refl≐ ∘≐ [≐∣ Δ ]f (sym≐ nl ∘≐ refl≐) ∘≐ refl≐ 〉 
          sound g  
                ∘ [ l ∘ id ⊗ sound f ∘ (lemma'' I I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f
                ∘ []++ I Γ Δ 
        ≐〈 refl≐ ∘≐ [≐∣ Δ ]f ass ∘≐ refl≐ 〉 
          sound g 
                ∘ [ l ∘ (id ⊗ sound f ∘ (lemma'' I I Γ ∘ [ ρ ∣ Γ ]f)) ∣ Δ ]f
                ∘ []++ I Γ Δ 
        ≐〈 refl≐ ∘≐ ([∘∣ Δ ]f _ _) ∘≐ refl≐ 〉
          sound g ∘ ([ l ∣ Δ ]f 
                ∘ [ id ⊗ sound f ∘ (lemma'' I I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f)
                ∘ []++ I Γ Δ 
        ≐〈 sym≐ ass ∘≐ refl≐ 〉 
          sound g ∘ [ l ∣ Δ ]f 
                ∘ [ id ⊗ sound f ∘ (lemma'' I I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f
                ∘ []++ I Γ Δ 
        ≐〈 rid ∘≐ refl≐ ∘≐ refl≐ 〉
          sound g ∘ [ l ∣ Δ ]f ∘ id 
                ∘ [ id ⊗ sound f ∘ (lemma'' I I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f
                ∘ []++ I Γ Δ 
        ≐〈 refl≐ ∘≐ sym≐ ([]≡id p) ∘≐ refl≐ ∘≐ refl≐ 〉
          sound g ∘ [ l ∣ Δ ]f ∘ []≡ p 
                ∘ [ id ⊗ sound f ∘ (lemma'' I I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f
                ∘ []++ I Γ Δ 
        ≐〈 rid ∘≐ refl≐ ∘≐ refl≐ 〉
          sound g ∘ [ l ∣ Δ ]f ∘ []≡ p ∘ id 
                ∘ [ id ⊗ sound f ∘ (lemma'' I I Γ ∘ [ ρ ∣ Γ ]f) ∣ Δ ]f
                ∘ []++ I Γ Δ 
        qed
  soundccut {.nothing} {Γ} {._} .(B ∷ Δ₀) {Δ'} {A} f (uf {.(Δ₀ ++ A ∷ Δ')} {B} g) p 
     | inj₂ (Δ₀ , refl , refl) =  
        proof 
          sound (ccut Δ₀ f g refl) ∘ [ l ∣ (Δ₀ ++ Γ) ++ Δ' ]f 
        ≐〈 soundccut Δ₀ f g refl ∘≐ refl≐  〉
          sound g ∘ id ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ [ id ⊗ sound f ∘ lemma' B Δ₀ Γ ∣ Δ' ]f
            ∘ []++ B (Δ₀ ++ Γ) Δ' ∘ [ l ∣ (Δ₀ ++ Γ) ++ Δ' ]f
        ≐〈  sym≐ rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉    
          sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ [ id ⊗ sound f ∘ lemma' B Δ₀ Γ ∣ Δ' ]f
            ∘ []++ B (Δ₀ ++ Γ) Δ' ∘ [ l ∣ (Δ₀ ++ Γ) ++ Δ' ]f
        ≐〈 ass 〉    
          sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ [ id ⊗ sound f ∘ lemma' B Δ₀ Γ ∣ Δ' ]f
            ∘ ([]++ B (Δ₀ ++ Γ) Δ' ∘ [ l ∣ (Δ₀ ++ Γ) ++ Δ' ]f)
        ≐〈 refl≐ ∘≐ []++n l (Δ₀ ++ Γ) Δ' 〉    
          sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ [ id ⊗ sound f ∘ lemma' B Δ₀ Γ ∣ Δ' ]f
            ∘ ([ [ l ∣ Δ₀ ++ Γ ]f ∣ Δ' ]f ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ') 
        ≐〈 sym≐ ass 〉 
           sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ [ id ⊗ sound f ∘ lemma' B Δ₀ Γ ∣ Δ' ]f
            ∘ [ [ l ∣ Δ₀ ++ Γ ]f ∣ Δ' ]f ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 ass ∘≐ refl≐ 〉 
           sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ ([ id ⊗ sound f ∘ lemma' B Δ₀ Γ ∣ Δ' ]f
            ∘ [ [ l ∣ Δ₀ ++ Γ ]f ∣ Δ' ]f) ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 refl≐ ∘≐ sym≐ ([∘∣ Δ' ]f _ _) ∘≐ refl≐ 〉 
           sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ ([ id ⊗ sound f ∘ lemma' B Δ₀ Γ ∘ [ l ∣ Δ₀ ++ Γ ]f ∣ Δ' ]f) 
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ'
        ≐〈 refl≐ ∘≐ [≐∣ Δ' ]f ass ∘≐ refl≐ 〉 
           sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ ([ id ⊗ sound f ∘ (lemma' B Δ₀ Γ ∘ [ l ∣ Δ₀ ++ Γ ]f) ∣ Δ' ]f) 
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ'
        ≐〈 refl≐ ∘≐ [≐∣ Δ' ]f (refl≐ ∘≐ sym≐ (lemma5 Δ₀ Γ l)) ∘≐ refl≐  〉   
          sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ ([ id ⊗ sound f ∘ ([ l ∣ Δ₀ ]f ⊗ id ∘ lemma' (I ⊗ B) Δ₀ Γ) ∣ Δ' ]f)
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 refl≐ ∘≐ [≐∣ Δ' ]f (sym≐ ass) ∘≐ refl≐ 〉  
          sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ ([ id ⊗ sound f ∘ [ l ∣ Δ₀ ]f ⊗ id ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f)
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 refl≐ ∘≐ [≐∣ Δ' ]f (sym≐ f⊗∘ ∘≐ refl≐) ∘≐ refl≐ 〉  
          sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ ([ (id ∘ [ l ∣ Δ₀ ]f) ⊗ (sound f ∘ id) ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f)
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 refl≐ ∘≐ [≐∣ Δ' ]f (trans≐ lid rid ⊗≐ trans≐ (sym≐ rid) (sym≐ lid) ∘≐ refl≐) ∘≐ refl≐ 〉
           sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ ([ ([ l ∣ Δ₀ ]f ∘ id) ⊗ (id ∘ sound f) ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f)
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 refl≐ ∘≐ [≐∣ Δ' ]f (f⊗∘ ∘≐ refl≐) ∘≐ refl≐ 〉  
          sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ ([ [ l ∣ Δ₀ ]f ⊗ id ∘ id ⊗ sound f ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f)
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 refl≐ ∘≐ [≐∣ Δ' ]f ass ∘≐ refl≐ 〉  
          sound g ∘ ++[] B Δ₀ (A ∷ Δ') 
            ∘ ([ [ l ∣ Δ₀ ]f ⊗ id ∘ (id ⊗ sound f ∘ lemma' (I ⊗ B) Δ₀ Γ) ∣ Δ' ]f)
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 refl≐ ∘≐ ([∘∣ Δ' ]f _ _) ∘≐ refl≐ 〉  
          sound g ∘ ++[] B Δ₀ (A ∷ Δ') ∘ ([ [ l ∣ Δ₀ ]f ⊗ id ∣ Δ' ]f
            ∘ [ id ⊗ sound f ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f)
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ'  
        ≐〈 sym≐ ass ∘≐ refl≐ 〉  
          sound g ∘ ++[] B Δ₀ (A ∷ Δ') ∘ [ [ l ∣ Δ₀ ]f ⊗ id ∣ Δ' ]f
            ∘ [ id ⊗ sound f ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 ass ∘≐ refl≐ ∘≐ refl≐ 〉  
          sound g ∘ (++[] B Δ₀ (A ∷ Δ') ∘ [ [ l ∣ Δ₀ ]f ⊗ id ∣ Δ' ]f)
            ∘ [ id ⊗ sound f ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 refl≐ ∘≐ ++[]n l Δ₀ (A ∷ Δ') ∘≐ refl≐ ∘≐ refl≐ 〉  
          sound g ∘ ([ l ∣ Δ₀ ++ A ∷ Δ' ]f ∘ ++[] (I ⊗ B) Δ₀ (A ∷ Δ'))
            ∘ [ id ⊗ sound f ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 sym≐ ass ∘≐ refl≐ ∘≐ refl≐  〉  
          sound g ∘ [ l ∣ Δ₀ ++ A ∷ Δ' ]f ∘ ++[] (I ⊗ B) Δ₀ (A ∷ Δ')
            ∘ [ id ⊗ sound f ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉  
          sound g ∘ [ l ∣ Δ₀ ++ A ∷ Δ' ]f ∘ id ∘ ++[] (I ⊗ B) Δ₀ (A ∷ Δ')
            ∘ [ id ⊗ sound f ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        ≐〈 refl≐ ∘≐ sym≐ ([]≡id p) ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉  
          sound g ∘ [ l ∣ Δ₀ ++ A ∷ Δ' ]f ∘ []≡ p ∘ ++[] (I ⊗ B) Δ₀ (A ∷ Δ')
            ∘ [ id ⊗ sound f ∘ lemma' (I ⊗ B) Δ₀ Γ ∣ Δ' ]f
            ∘ []++ (I ⊗ B) (Δ₀ ++ Γ) Δ' 
        qed 
  soundccut Δ₀ f Ir p = ⊥-elim (lemma[] Δ₀ p)
  soundccut Δ₀ f (⊗r {S} {Δ*} g g') p with lemma++ Δ₀ Δ* p 
  soundccut {.S} {Γ} Δ₀ {.(Γ₀ ++ Γ')} {A} f (⊗r {S} {.(Δ₀ ++ A ∷ Γ₀)} {Γ'} g g') p 
     | inj₁ (Γ₀ , refl , refl) = 
    let 
      h = id ⊗ sound f ∘ lemma S Δ₀ Γ
    in proof 
      sound (subeq (++ass (Δ₀ ++ Γ)) (⊗r (ccut Δ₀ f g refl) g')) 
    ≐〈 soundsubeq (++ass (Δ₀ ++ Γ)) (⊗r (ccut Δ₀ f g refl) g')  〉
      sound (ccut Δ₀ f g refl) ⊗ sound g' ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ'
      ∘ 〈〉≡ {S} (++ass (Δ₀ ++ Γ))
    ≐〈 soundccut Δ₀ f g refl ⊗≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ id ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) 
      ∘ [ h ∣ Γ₀ ]f ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀) ⊗ sound g'  
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass (Δ₀ ++ Γ))    
    ≐〈 (sym≐ rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐) ⊗≐ rid ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) 
      ∘ [ h ∣ Γ₀ ]f ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀) ⊗ (sound g' ∘ id)
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass (Δ₀ ++ Γ))  
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ∘ [ h ∣ Γ₀ ]f) ⊗ sound g' 
      ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass (Δ₀ ++ Γ))  
    ≐〈 refl≐ ⊗≐ rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ∘ [ h ∣ Γ₀ ]f) ⊗ (sound g' ∘ id)
      ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass (Δ₀ ++ Γ)) 
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ ++〈〉 S Δ₀ (A ∷ Γ₀)) ⊗ sound g' 
      ∘ [ h ∣ Γ₀ ]f ⊗ id ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass (Δ₀ ++ Γ)) 
    ≐〈 refl≐ ⊗≐ rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ ++〈〉 S Δ₀ (A ∷ Γ₀)) ⊗ (sound g' ∘ id) 
      ∘ [ h ∣ Γ₀ ]f ⊗ id ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass (Δ₀ ++ Γ)) 
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ [ h ∣ Γ₀ ]f ⊗ id ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass (Δ₀ ++ Γ)) 
    ≐〈 ass ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ [ h ∣ Γ₀ ]f ⊗ id ∘ (〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ') ∘ 〈〉≡ {S} (++ass (Δ₀ ++ Γ)) 
    ≐〈 ass 〉
      sound g ⊗ sound g' ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ [ h ∣ Γ₀ ]f ⊗ id ∘ (〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass (Δ₀ ++ Γ)))
    ≐〈 refl≐ ∘≐ asslemma S (Δ₀ ++ Γ) Γ₀ Γ' 〉
      sound g ⊗ sound g' ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ [ h ∣ Γ₀ ]f ⊗ id  
      ∘ (lemma' 〈 S ∣ Δ₀ ++ Γ 〉 Γ₀ Γ' ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ'))
    ≐〈 sym≐ ass 〉
      sound g ⊗ sound g' ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ [ h ∣ Γ₀ ]f ⊗ id  
      ∘ lemma' 〈 S ∣ Δ₀ ++ Γ 〉 Γ₀ Γ' ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ')
    ≐〈 ass ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ ([ h ∣ Γ₀ ]f ⊗ id ∘ lemma' 〈 S ∣ Δ₀ ++ Γ 〉 Γ₀ Γ') 
      ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ')
    ≐〈 refl≐ ∘≐ lemma5 Γ₀ Γ' h ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ (lemma' (〈 S ∣ Δ₀ 〉 ⊗ A) Γ₀ Γ' ∘ [ h ∣ Γ₀ ++ Γ' ]f) 
      ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ')
    ≐〈 sym≐ ass ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ lemma' 〈 S ∣ Δ₀ 〉 (A ∷ Γ₀) Γ' ∘ [ h ∣ Γ₀ ++ Γ' ]f 
      ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ')
    ≐〈 ass ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ (++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ lemma' 〈 S ∣ Δ₀ 〉 (A ∷ Γ₀) Γ') ∘ [ h ∣ Γ₀ ++ Γ' ]f 
      ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ')
    ≐〈 refl≐ ∘≐ lemma10 S Δ₀ (A ∷ Γ₀) Γ' ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ (lemma S (Δ₀ ++ A ∷ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass Δ₀)
      ∘ ++〈〉 S Δ₀ (A ∷ Γ₀ ++ Γ')) 
      ∘ [ h ∣ Γ₀ ++ Γ' ]f ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ')
    ≐〈 sym≐ ass ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ (lemma S (Δ₀ ++ A ∷ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass Δ₀))
      ∘ ++〈〉 S Δ₀ (A ∷ Γ₀ ++ Γ')
      ∘ [ h ∣ Γ₀ ++ Γ' ]f ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ')
    ≐〈 sym≐ ass ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ lemma S (Δ₀ ++ A ∷ Γ₀) Γ' ∘ 〈〉≡ {S} (++ass Δ₀)
      ∘ ++〈〉 S Δ₀ (A ∷ Γ₀ ++ Γ')
      ∘ [ h ∣ Γ₀ ++ Γ' ]f ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ')
    ≐〈 refl≐ ∘≐ 〈〉≡eq {S} (++ass Δ₀) p ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ lemma S (Δ₀ ++ A ∷ Γ₀) Γ' ∘ 〈〉≡ {S} p 
      ∘ ++〈〉 S Δ₀ (A ∷ Γ₀ ++ Γ') 
      ∘ [ h ∣ Γ₀ ++ Γ' ]f ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ') 
    qed
  soundccut {.S} {Γ} {._} .(Γ₀ ++ Γ') {Δ'} {A} f (⊗r {S} {Γ₀} {.(Γ' ++ A ∷ Δ')} g g') p 
     | inj₂ (Γ' , refl , refl) = 
    let 
      q = trans (sym (++ass Γ₀)) (cong₂ _++_ (sym (++ass Γ₀ {Γ'} {Γ})) refl)
    in proof 
      sound (subeq q (⊗r g (ccut Γ' f g' refl)))
    ≐〈 soundsubeq q (⊗r g (ccut Γ' f g' refl)) 〉
      sound g ⊗ sound (ccut Γ' f g' refl) ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
      ∘ 〈〉≡ {S} q 
    ≐〈 refl≐ ⊗≐ soundccut Γ' f g' refl ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ (sound g' ∘ id ∘ ++[] I Γ' (A ∷ Δ') 
      ∘ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ∘ []++ I (Γ' ++ Γ) Δ') 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
      ∘ 〈〉≡ {S} q
    ≐〈 rid ⊗≐ (sym≐ rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐) ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ id) ⊗ (sound g' ∘ ++[] I Γ' (A ∷ Δ') 
      ∘ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ∘ []++ I (Γ' ++ Γ) Δ') 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
      ∘ 〈〉≡ {S} q
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ (sound g' ∘ ++[] I Γ' (A ∷ Δ') 
      ∘ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ) ∘ id ⊗ []++ I (Γ' ++ Γ) Δ' 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
      ∘ 〈〉≡ {S} q
    ≐〈 rid ⊗≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ id) ⊗ (sound g' ∘ ++[] I Γ' (A ∷ Δ') 
      ∘ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ) ∘ id ⊗ []++ I (Γ' ++ Γ) Δ' 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
      ∘ 〈〉≡ {S} q
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ (sound g' ∘ ++[] I Γ' (A ∷ Δ')) 
      ∘ id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ∘ id ⊗ []++ I (Γ' ++ Γ) Δ' 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
      ∘ 〈〉≡ {S} q
    ≐〈 rid ⊗≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ id) ⊗ (sound g' ∘ ++[] I Γ' (A ∷ Δ')) 
      ∘ id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ∘ id ⊗ []++ I (Γ' ++ Γ) Δ' 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
      ∘ 〈〉≡ {S} q
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ id ⊗ ++[] I Γ' (A ∷ Δ') 
      ∘ id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ∘ id ⊗ []++ I (Γ' ++ Γ) Δ' 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
      ∘ 〈〉≡ {S} q
    ≐〈 trans≐ ass (trans≐ ass (trans≐ ass ass)) 〉
      sound g ⊗ sound g'
      ∘ (id ⊗ ++[] I Γ' (A ∷ Δ') 
         ∘ (id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f
            ∘ (id ⊗ []++ I (Γ' ++ Γ) Δ' 
               ∘ (lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
                  ∘ 〈〉≡ {S} q))))
    ≐〈 refl≐ ∘≐ lemma11 S Γ₀ Γ' Γ Δ' f 〉
      sound g ⊗ sound g'
      ∘ (lemma S Γ₀ (Γ' ++ A ∷ Δ')
         ∘ (〈〉≡ {S} (sym (++ass Γ₀ {Γ'} {A ∷ Δ'}) )
            ∘ (++〈〉 S (Γ₀ ++ Γ') (A ∷ Δ')
               ∘ ([ id ⊗ sound f ∘ lemma S (Γ₀ ++ Γ') Γ ∣ Δ' ]f
                  ∘ 〈〉++ S ((Γ₀ ++ Γ') ++ Γ) Δ'))))
    ≐〈 sym≐ (trans≐ ass (trans≐ ass (trans≐ ass ass))) 〉
      sound g ⊗ sound g' ∘ lemma S Γ₀ (Γ' ++ A ∷ Δ') ∘ 〈〉≡ {S} (sym (++ass Γ₀ {Γ'} {A ∷ Δ'}) )
      ∘ ++〈〉 S (Γ₀ ++ Γ') (A ∷ Δ')
      ∘ [ id ⊗ sound f ∘ lemma S (Γ₀ ++ Γ') Γ ∣ Δ' ]f
      ∘ 〈〉++ S ((Γ₀ ++ Γ') ++ Γ) Δ' 
    ≐〈 refl≐ ∘≐ 〈〉≡eq {S} _ p ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ lemma S Γ₀ (Γ' ++ A ∷ Δ') ∘ 〈〉≡ {S} p 
      ∘ ++〈〉 S (Γ₀ ++ Γ') (A ∷ Δ')
      ∘ [ id ⊗ sound f ∘ lemma S (Γ₀ ++ Γ') Γ ∣ Δ' ]f
      ∘ 〈〉++ S ((Γ₀ ++ Γ') ++ Γ) Δ' 
    qed
  soundccut Δ₀ f (Il g) refl = soundccut Δ₀ f g refl
  soundccut Δ₀ f (⊗l {B = B} g) refl = soundccut (B ∷ Δ₀) f g refl



soundcmplt : {A B : Tm} → (f : A ⇒ B) → sound (cmplt f) ≐ f 
soundcmplt id = refl≐
soundcmplt (_∘_ {A} {B} {C} f g) = 
      proof 
        sound (scut (cmplt g) (cmplt f)) 
      ≐〈 soundscut {just A} {[]} {[]} (cmplt g) (cmplt f) 〉 
        sound (cmplt f) ∘ sound (cmplt g) ∘ id
      ≐〈 sym≐ rid 〉
        sound (cmplt f) ∘ sound (cmplt g)
      ≐〈 soundcmplt f ∘≐ soundcmplt g 〉 
        f ∘ g 
      qed
soundcmplt (f ⊗ g) =
      proof 
        sound (cmplt f) ⊗ (sound (cmplt g) ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id) 
      ≐〈 soundcmplt f ⊗≐ (soundcmplt g ∘≐ refl≐) ∘≐ (lid ∘≐ refl≐) 〉
        f ⊗ (g ∘ l) ∘ (α ∘ ρ ⊗ id)
      ≐〈 rid ⊗≐ refl≐ ∘≐ refl≐ 〉
        (f ∘ id) ⊗ (g ∘ l) ∘ (α ∘ ρ ⊗ id)
      ≐〈 f⊗∘ ∘≐ refl≐ 〉
        f ⊗ g ∘ id ⊗ l ∘ (α ∘ ρ ⊗ id)
      ≐〈 ass 〉
        f ⊗ g ∘ (id ⊗ l ∘ (α ∘ ρ ⊗ id))
      ≐〈 refl≐ ∘≐ sym≐ ass 〉
        f ⊗ g ∘ (id ⊗ l ∘ α ∘ ρ ⊗ id)
      ≐〈 refl≐ ∘≐ sym≐ lαρ 〉
        f ⊗ g ∘ id
      ≐〈 sym≐ rid 〉
        f ⊗ g 
      qed 
soundcmplt l = 
      proof 
         id ∘ l 
      ≐〈 lid 〉 
         l 
      qed
soundcmplt ρ =
      proof 
        id ⊗ id ∘ (id ∘ ρ) 
      ≐〈 f⊗id ∘≐ lid 〉 
        id ∘ ρ  
      ≐〈 lid 〉 
        ρ 
      qed 
soundcmplt α = 
      proof 
        id ⊗ (id ⊗ (id ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id) ∘ l ⊗ id) ∘
           (id ∘ α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
      ≐〈 refl≐ ⊗≐ (refl≐ ⊗≐ lid ∘≐ (lid ∘≐ refl≐) ∘≐ refl≐) ∘≐
           (lid ∘≐ refl≐ ∘≐ refl≐) 〉 
        id ⊗ (id ⊗ l ∘ (α ∘ ρ ⊗ id) ∘ l ⊗ id) ∘ (α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
      ≐〈 refl≐ ⊗≐ (sym≐ ass ∘≐ refl≐) ∘≐ refl≐ 〉 
        id ⊗ (id ⊗ l ∘ α ∘ ρ ⊗ id ∘ l ⊗ id) ∘ (α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
      ≐〈 refl≐ ⊗≐ (sym≐ lαρ ∘≐ refl≐) ∘≐ refl≐ 〉 
        id ⊗ (id ∘ l ⊗ id) ∘ (α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
      ≐〈 refl≐ ⊗≐ (refl≐ ∘≐ sym≐ lα) ∘≐ refl≐ 〉 
        id ⊗ (id ∘ (l ∘ α)) ∘ (α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
      ≐〈 rid ⊗≐ lid ∘≐ refl≐ 〉 
        (id ∘ id) ⊗ (l ∘ α) ∘ (α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
      ≐〈 f⊗∘ ∘≐ refl≐ 〉 
        id ⊗ l ∘ id ⊗ α ∘ (α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id)
      ≐〈 ass 〉 
        id ⊗ l ∘ (id ⊗ α ∘ (α ∘ α ⊗ id ∘ ρ ⊗ id ⊗ id))
      ≐〈 refl≐ ∘≐ sym≐ ass 〉 
        id ⊗ l ∘ (id ⊗ α ∘ (α ∘ α ⊗ id) ∘ ρ ⊗ id ⊗ id)
      ≐〈 refl≐ ∘≐ (sym≐ ααα ∘≐ refl≐) 〉 
        id ⊗ l ∘ (α ∘ α ∘ ρ ⊗ id ⊗ id)
      ≐〈 refl≐ ∘≐ ass 〉 
        id ⊗ l ∘ (α ∘ (α ∘ ρ ⊗ id ⊗ id))
      ≐〈 refl≐ ∘≐ (refl≐ ∘≐ nα) 〉 
        id ⊗ l ∘ (α ∘ (ρ ⊗ (id ⊗ id) ∘ α))
      ≐〈 refl≐ ∘≐ (refl≐ ∘≐ (refl≐ ⊗≐ f⊗id ∘≐ refl≐ )) 〉    
        id ⊗ l ∘ (α ∘ (ρ ⊗ id ∘ α))
      ≐〈 refl≐ ∘≐ sym≐ ass 〉 
        id ⊗ l ∘ (α ∘ ρ ⊗ id ∘ α)
      ≐〈 sym≐ ass 〉 
        id ⊗ l ∘ (α ∘ ρ ⊗ id) ∘ α
      ≐〈 sym≐ ass ∘≐ refl≐ 〉 
        id ⊗ l ∘ α ∘ ρ ⊗ id ∘ α
      ≐〈 sym≐ lαρ ∘≐ refl≐ 〉 
        id ∘ α
      ≐〈 lid  〉 
        α 
      qed 

--cmpltsound⊥ : ({A B : Tm} → (f : just A ∣ [] ⊢ B) → cmplt (sound f) ≡ f) → ⊥
--cmpltsound⊥ cs with cs (Il Ir)
--cmpltsound⊥ cs | ()


{-

Why is the stoup needed? (at least for the semantics; for syntax only
one can state the basic system ignoring it, i.e. conflating
the stoup and the context together into a flat antecedent)


|- I     C |- A
-----------------
  C |- I ⊗ A

This is a bad rule instance, if sglt context C is interpreted as C, 
since A -> I ⊗ A is not valid



A, B |- C
--------------
A ⊗ B |- C

This is a bad rule, if contexts A, B and  A ⊗ B are interpreted as 
(I ⊗ A) ⊗ B and I ⊗ (A ⊗ B), since I ⊗ (A ⊗ B) -> (I ⊗ A) ⊗ B 
is not valid 


Depending on whether a sequent has an empty or nonempty stoup, the
antecedent will have to be interpreted with an I as the leftmost
factor in the big tensor product or not.

-}







-}

-}
-}
-}
-}
