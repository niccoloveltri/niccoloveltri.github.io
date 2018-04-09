{-# OPTIONS --rewriting #-}

module Sound where

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

-- soundness

-- interpretation of antecedents

-- -- (Note that an empty stoup contributes an I to the meaning 
-- -- of an antecedent.)

t : Stp → Tm
t nothing = I
t (just A) = A

[_∣_] : Tm → Cxt → Tm
[ A ∣ [] ] = A
[ A ∣ C ∷ Γ ] = [ A ⊗ C ∣ Γ ]

〈_∣_〉 : Stp → Cxt → Tm 
〈 S ∣ Γ 〉 = [ t S ∣ Γ ] 

[_∣_]f : {A B : Tm} → A ⇒ B → (Γ : Cxt) → [ A ∣ Γ ] ⇒ [ B ∣ Γ ]
[ f ∣ [] ]f = f
[ f ∣ C ∷ Γ ]f = [ f ⊗ id ∣ Γ ]f

lemma'' : (A B : Tm) → (Δ : Cxt) → 
                   [ A ⊗ B ∣  Δ ] ⇒ A ⊗ [ B ∣ Δ ] 
lemma'' A B [] = id
lemma'' A B (C ∷ Δ) = lemma'' A (B ⊗ C) Δ ∘ [ α ∣ Δ ]f 

lemma' : (A : Tm) → (Γ Δ : Cxt) →
                   [ A ∣ Γ ++ Δ ] ⇒ [ A ∣ Γ ] ⊗ 〈 nothing ∣ Δ 〉
lemma' A [] Δ = lemma'' A I Δ ∘ [ ρ ∣ Δ ]f 
lemma' A (C ∷ Γ) Δ  = lemma' (A ⊗ C) Γ Δ 

lemma : (S : Stp) → (Γ Δ : Cxt) →  
                   〈 S ∣ Γ ++ Δ 〉 ⇒ 〈 S ∣ Γ 〉 ⊗ 〈 nothing ∣ Δ 〉
lemma S Γ Δ = lemma' (t S) Γ Δ 


sound : {S : Stp} → {Γ : Cxt} → {A : Tm} → S ∣ Γ ⊢ A → 〈 S ∣ Γ 〉 ⇒ A 
sound ax = id
sound (uf {Γ} f) = sound f ∘ [ l ∣ Γ ]f 
sound Ir = id
sound (⊗r {S} {Γ} {Δ} f g) = sound f ⊗ sound g ∘ lemma S Γ Δ
sound (Il f) = sound f
sound (⊗l f) = sound f 


[≐∣_]f : (Γ : Cxt) → {A B : Tm} → {f g : A ⇒ B} → 
                                     f ≐ g → [ f ∣ Γ ]f ≐ [ g ∣ Γ ]f
[≐∣ [] ]f p = p
[≐∣ C ∷ Γ ]f p = [≐∣ Γ ]f (p ⊗≐ refl≐)

[id∣_]f : (Γ : Cxt) → {A : Tm} → [ id {A} ∣ Γ ]f ≐ id {[ A ∣ Γ ]}
[id∣ [] ]f = refl≐ 
[id∣ C ∷ Γ ]f = trans≐ ([≐∣ Γ ]f f⊗id) [id∣ Γ ]f 

[∘∣_]f : (Γ : Cxt) → {A B C : Tm} → (f : B ⇒ C) → (g : A ⇒ B) → 
            [ f ∘ g ∣ Γ ]f ≐ [ f ∣ Γ ]f ∘ [ g ∣ Γ ]f
[∘∣ [] ]f f g = refl≐
[∘∣ C ∷ Γ ]f f g = 
   trans≐ ([≐∣ Γ ]f (trans≐ (refl≐ ⊗≐ rid) f⊗∘)) ([∘∣ Γ ]f (f ⊗ id) (g ⊗ id))  

[]≡ : {A : Tm} → {Γ Γ' : Cxt} → (p : Γ ≡ Γ') → 
                                             [ A ∣ Γ' ] ⇒ [ A ∣ Γ ]
[]≡ refl = id

〈〉≡ : {S : Stp} → {Γ Γ' : Cxt} → (p : Γ ≡ Γ') → 
                                             〈 S ∣ Γ' 〉 ⇒ 〈 S ∣ Γ 〉
〈〉≡ {S} p = []≡ {t S} p



[]≡id : {A : Tm} → {Γ : Cxt} → (p : Γ ≡ Γ) → []≡ {A} p ≐ id
[]≡id refl = refl≐ 

[]≡eq : {A : Tm} → {Γ Γ' : Cxt} → (p q : Γ ≡ Γ') 
                                        → []≡ {A} p ≐ []≡ {A} q
[]≡eq refl refl = refl≐

〈〉≡eq : {S : Stp} → {Γ Γ' : Cxt} → (p q : Γ ≡ Γ') 
                                        → 〈〉≡ {S} p ≐ 〈〉≡ {S} q
〈〉≡eq p q = []≡eq p q

[]≡∷ : {A C : Tm} → {Γ Γ' : Cxt} → (p : Γ ≡ Γ') → 
                     []≡ {A} (cong (_∷_ C) p) ≐ []≡ {A ⊗ C} p
[]≡∷ refl = refl≐ 

{-
[]++ : (A : Tm) → (Γ Δ : Cxt) → [ A ∣ Γ ++ Δ ] ≡ [ [ A ∣ Γ ] ∣ Δ ]
[]++ A [] Δ = refl
[]++ A (B ∷ Γ) Δ = []++ (A ⊗ B) Γ Δ

〈〉++ : (S : Stp) → (Γ Δ : Cxt) → 〈 S ∣ Γ ++ Δ 〉 ≡ [ 〈 S ∣ Γ 〉 ∣ Δ ]
〈〉++ S Γ Δ = []++ (t S) Γ Δ
-}


[]++ : (A : Tm) → (Γ Δ : Cxt) → [ A ∣ Γ ++ Δ ] ⇒ [ [ A ∣ Γ ] ∣ Δ ]
[]++ A [] Δ = id
[]++ A (C ∷ Γ) Δ = []++ (A ⊗ C) Γ Δ 

〈〉++ : (S : Stp) → (Γ Δ : Cxt) → 〈 S ∣ Γ ++ Δ 〉 ⇒ [ 〈 S ∣ Γ 〉 ∣ Δ ]
--〈〉++ S Γ Δ = eqid (〈++〉 S Γ Δ)
〈〉++ S Γ Δ = []++ (t S) Γ Δ

[]++n : {A B : Tm} → (f : A ⇒ B) → (Γ Δ : Cxt) →         
       []++ B Γ Δ ∘ [ f ∣ Γ ++ Δ ]f ≐  [ [ f ∣ Γ ]f ∣ Δ ]f ∘ []++ A Γ Δ 
[]++n f [] Δ = trans≐ lid rid
[]++n f (C ∷ Γ) Δ = []++n (f ⊗ id {C}) Γ Δ 



++[] : (A : Tm) → (Γ Δ : Cxt) → [ [ A ∣ Γ ] ∣ Δ ] ⇒ [ A ∣ Γ ++ Δ ]
++[] A [] Δ = id
++[] A (C ∷ Γ) Δ = ++[] (A ⊗ C) Γ Δ 

++〈〉 : (S : Stp) → (Γ Δ : Cxt) → [ 〈 S ∣ Γ 〉 ∣ Δ ] ⇒ 〈 S ∣ Γ ++ Δ 〉
--〈〉++ S Γ Δ = eqid (〈++〉 S Γ Δ)
++〈〉 S Γ Δ = ++[] (t S) Γ Δ

lemma10' : (A : Tm) → (Γ Δ Δ' : Cxt) → 
        ++[] A Γ Δ ⊗ id ∘ lemma' [ A ∣ Γ ] Δ Δ' 
            ≐ lemma' A (Γ ++ Δ) Δ' ∘ ++[] A Γ (Δ ++ Δ')
lemma10' A [] Δ Δ' =
  proof 
    id ⊗ id ∘ lemma' A Δ Δ' 
  ≐〈 f⊗id ∘≐ refl≐ 〉
    id ∘ lemma' A Δ Δ' 
  ≐〈 lid 〉
    lemma' A Δ Δ' 
  ≐〈 rid 〉
    lemma' A Δ Δ' ∘ id
  qed
lemma10' A (C ∷ Γ) Δ Δ' = lemma10' (A ⊗ C) Γ Δ Δ'

lemma10 : (S : Stp) → (Γ Δ Δ' : Cxt) → 
        ++〈〉 S Γ Δ ⊗ id ∘ lemma' 〈 S ∣ Γ 〉 Δ Δ' 
            ≐ lemma S (Γ ++ Δ) Δ' ∘ ++〈〉 S Γ (Δ ++ Δ') 
lemma10 S Γ Δ Δ' = lemma10' (t S) Γ Δ Δ'

++[]n : {A B : Tm} → (f : A ⇒ B) → (Γ Δ : Cxt) →         
        ++[] B Γ Δ  ∘ [ [ f ∣ Γ ]f ∣ Δ ]f ≐ [ f ∣ Γ ++ Δ ]f ∘ ++[] A Γ Δ  
++[]n f [] Δ = trans≐ lid rid
++[]n f (C ∷ Γ) Δ = ++[]n (f ⊗ id {C}) Γ Δ 

[]++iso : (A : Tm) → (Γ Δ : Cxt) → []++ A Γ Δ ∘ ++[] A Γ Δ ≐ id
[]++iso A [] Δ = lid
[]++iso A (C ∷ Γ) Δ = []++iso (A ⊗ C) Γ Δ

〈〉++iso : (S : Stp) → (Γ Δ : Cxt) → 〈〉++ S Γ Δ ∘ ++〈〉 S Γ Δ ≐ id
〈〉++iso S Γ Δ = []++iso (t S) Γ Δ


soundsubeq : {S : Stp} → {Γ Γ' : Cxt} → {A : Tm} → 
      (p : Γ ≡ Γ') → (f : S ∣ Γ ⊢ A) → 
                      sound (subeq p f) ≐ sound f ∘ 〈〉≡ {S} {Γ} {Γ'} p
soundsubeq {S} refl f = rid



rulemma' : (A : Tm) → (Γ : Cxt) → id ≐ []++ A Γ [] 
rulemma' A [] = refl≐
rulemma' A (C ∷ Γ) = rulemma' (A ⊗ C) Γ

rulemma : (S : Stp) → (Γ : Cxt) → id ≐ 〈〉++ S Γ [] 
rulemma S Γ = rulemma' (t S) Γ

asslemma' : (A : Tm) → (Γ Δ Δ' : Cxt) → 
       []++ A Γ Δ ⊗ id ∘ lemma' A (Γ ++ Δ) Δ' ≐ lemma' [ A ∣ Γ ] Δ Δ' ∘ []++ A Γ (Δ ++ Δ') 
asslemma' A [] Δ Δ' = 
   proof 
     id ⊗ id ∘ lemma' A Δ Δ' 
   ≐〈 rid 〉 
     id ⊗ id ∘ lemma' A Δ Δ' ∘ id
   ≐〈  f⊗id ∘≐ refl≐ ∘≐ refl≐ 〉 
     id ∘ lemma' A Δ Δ' ∘ id
   ≐〈  lid ∘≐ refl≐ 〉
     lemma' A Δ Δ' ∘ id
   qed 
asslemma' A (C ∷ Γ) Δ Δ' = asslemma' (A ⊗ C) Γ Δ Δ'

asslemma : (S : Stp) → (Γ Δ Δ' : Cxt) → 
       〈〉++ S Γ Δ ⊗ id ∘ lemma S (Γ ++ Δ) Δ' ≐ lemma' 〈 S ∣ Γ 〉 Δ Δ' ∘ 〈〉++ S Γ (Δ ++ Δ') 
asslemma S Γ Δ Δ' = asslemma' (t S) Γ Δ Δ'


{-
asslemma' : (A : Tm) → (Γ Δ Δ' : Cxt) → 
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


asslemma : (S : Stp) → (Γ Δ Δ' : Cxt) → 
       〈〉++ S Γ Δ ⊗ id ∘ lemma S (Γ ++ Δ) Δ' ∘ 〈〉≡ {S} (++ass Γ {Δ} {Δ'})
                         ≐ lemma' 〈 S ∣ Γ 〉 Δ Δ' ∘ 〈〉++ S Γ (Δ ++ Δ') 
asslemma S Γ Δ Δ' = asslemma' (t S) Γ Δ Δ'
-}

{-
asslemma2 : (S : Stp) → (Γ₀ Γ' Γ Δ' : Cxt) → 
 let 
   q = trans (sym (++ass Γ₀)) (cong₂ _++_ (sym (++ass Γ₀)) refl)
 in --id ⊗ 〈〉++ nothing Γ Δ' 
          {!!} ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ') ∘ 〈〉≡ {S} q
                         ≐ ++〈〉 S (Γ₀ ++ Γ') (Γ ++ Δ') ∘ [ lemma S (Γ₀ ++ Γ') Γ ∣ Δ' ]f
                                      ∘ 〈〉++ S ((Γ₀ ++ Γ') ++ Γ) Δ' 
asslemma2 S Γ Δ Δ' = {!!} 
-}


lemma5' : (C D : Tm) → (Δ : Cxt) → {A : Tm} → (f : C ⇒ A) → 
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



lemma5 : (Γ Δ : Cxt) → {A B : Tm} → (f : A ⇒ B) → 
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



lemma8 : (A : Tm) → (Δ : Cxt) → l ∘ lemma'' I A Δ ≐ [ l ∣ Δ ]f
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



scomp : {S : Stp} → {Γ Δ' : Cxt} → {A C : Tm} → 
           [ A ∣ Δ' ] ⇒ C → 〈 S ∣ Γ 〉 ⇒ A  → 〈 S ∣ Γ ++ Δ' 〉 ⇒ C
scomp {S} {Γ} {Δ'} g f = g ∘ [ f ∣ Δ' ]f ∘ 〈〉++ S Γ Δ' 


ccomp : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Tm} → 
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


lemma12' : {A Z : Tm}(X Y : Tm)(Γ : Cxt)
  → Y ⇒ X ⊗ Z
  → [ Z ∣ Γ ] ⇒ A
  → [ Y ∣ Γ ] ⇒ X ⊗ A
lemma12' X Y Γ g f = id ⊗ f ∘ (lemma'' X _ Γ ∘ [ g ∣ Γ ]f)

lemma12 : {A : Tm}(X : Tm)(Γ : Cxt)
  → nothing ∣ Γ  ⊢ A
  → [ X ∣ Γ ] ⇒ X ⊗ A
lemma12 X Γ f = lemma12' X X Γ ρ (sound (Il f))

lemma13' : {A X X' Y Z : Tm}(Γ : Cxt)
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

lemma13 : {A X X' : Tm}(Γ : Cxt)
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

lemma6 : (Γ : Cxt) → {A B C : Tm} → (f : B ⇒ C) → 
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

lemma16 : {A B C : Tm}(Γ : Cxt)
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




lemma15 : {A B C : Tm}(Γ : Cxt)
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

lemma14 : (A B : Tm)(Γ Δ : Cxt)
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

lemma11'' : (A B X : Tm)(Γ' Γ Δ : Cxt){C : Tm}
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

lemma11' : (A : Tm)(Γ₀ Γ' Γ Δ : Cxt){C : Tm}
  → (f : nothing ∣ Γ  ⊢ C)
  → id ⊗ ++[] I Γ' (C ∷ Δ) ∘
      (id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ ]f ∘
        (id ⊗ []++ I (Γ' ++ Γ) Δ ∘
          (lemma' A Γ₀ ((Γ' ++ Γ) ++ Δ) ∘ id)))
    ≐
    lemma' A Γ₀ (Γ' ++ C ∷ Δ) ∘
      (id ∘
        (++[] A (Γ₀ ++ Γ') (C ∷ Δ) ∘
          ([ id ⊗ sound f ∘ lemma' A (Γ₀ ++ Γ') Γ ∣ Δ ]f ∘
            []++ A ((Γ₀ ++ Γ') ++ Γ) Δ)))
lemma11' A [] Γ' Γ Δ f = lemma11'' A I A Γ' Γ Δ ρ f
lemma11' A (B ∷ Γ₀) Γ' Γ Δ {C} f = lemma11' (A ⊗ B) Γ₀ Γ' Γ Δ f


lemma11 : (S : Stp)(Γ₀ Γ' Γ Δ : Cxt){A : Tm}
  → (f : nothing ∣ Γ  ⊢ A)
  → _≐_ {〈 S ∣ ((Γ₀ ++ Γ') ++ Γ) ++ Δ 〉}{〈 S ∣ Γ₀ 〉 ⊗ 〈 nothing ∣ Γ' ++ A ∷ Δ 〉}
    (id ⊗ ++[] I Γ' (A ∷ Δ) ∘
      (id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ ]f ∘
        (id ⊗ []++ I (Γ' ++ Γ) Δ ∘
          (lemma S Γ₀ ((Γ' ++ Γ) ++ Δ) ∘ id))))
    (lemma S Γ₀ (Γ' ++ A ∷ Δ) ∘
      (id ∘
        (++〈〉 S (Γ₀ ++ Γ') (A ∷ Δ) ∘
          ([ id ⊗ sound f ∘ lemma S (Γ₀ ++ Γ') Γ ∣ Δ ]f ∘
            〈〉++ S ((Γ₀ ++ Γ') ++ Γ) Δ))))
lemma11 S Γ₀ Γ' Γ Δ f = lemma11' (t S) Γ₀ Γ' Γ Δ f


mutual
  soundscut : {S : Stp} → {Γ Δ' : Cxt} → {A C : Tm} → 
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
    proof 
      sound f ⊗ sound f' ∘ lemma S Γ Γ'
    ≐〈 rid 〉
      (sound f ⊗ sound f' ∘ lemma S Γ Γ') ∘ id
    ≐〈 refl≐ ∘≐ rulemma S (Γ ++ Γ') 〉
      sound f ⊗ sound f' ∘ lemma S Γ Γ' ∘ 〈〉++ S (Γ ++ Γ') []
    ≐〈 sym≐ lid ∘≐ refl≐ 〉
      id ∘ (sound f ⊗ sound f' ∘ lemma S Γ Γ') ∘ 〈〉++ S (Γ ++ Γ') []
    qed
  soundscut (⊗r {S} {Γ} {Γ'} {A} {B} f f') (⊗r {.(just (A ⊗ B))} {Δ} {Δ'} g g') = 
    let
      h = sound (⊗r {S} {Γ} {Γ'} f f')     
    in
    proof
      sound (scut (⊗r f f') g) ⊗ sound g' ∘ lemma S (Γ ++ Γ' ++ Δ) Δ'
    ≐〈 soundscut (⊗r f f') g ⊗≐ refl≐ ∘≐ refl≐  〉
      (sound g ∘ [ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ) ⊗ sound g' ∘ lemma S ((Γ ++ Γ') ++ Δ) Δ'
    ≐〈 ass ⊗≐ rid ∘≐ refl≐ 〉
      (sound g ∘ ([ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ)) ⊗ (sound g' ∘ id) ∘ lemma S ((Γ ++ Γ') ++ Δ) Δ'
    ≐〈 f⊗∘ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ) ⊗ id ∘ lemma S ((Γ ++ Γ') ++ Δ) Δ'
    ≐〈 ass 〉
      sound g ⊗ sound g' ∘ (([ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ) ⊗ id ∘ lemma S ((Γ ++ Γ') ++ Δ) Δ')
    ≐〈 refl≐ ∘≐ (refl≐ ⊗≐ rid ∘≐ refl≐) 〉 
      sound g ⊗ sound g' ∘ (([ h ∣ Δ ]f ∘ 〈〉++ S (Γ ++ Γ') Δ) ⊗ (id ∘ id) ∘ lemma S ((Γ ++ Γ') ++ Δ) Δ')
    ≐〈 refl≐ ∘≐ (f⊗∘ ∘≐ refl≐) 〉 
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ⊗ id ∘ 〈〉++ S (Γ ++ Γ') Δ ⊗ id ∘ lemma S ((Γ ++ Γ') ++ Δ) Δ')
    ≐〈 refl≐ ∘≐ ass 〉 
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ⊗ id ∘ (〈〉++ S (Γ ++ Γ') Δ ⊗ id ∘ lemma S ((Γ ++ Γ') ++ Δ) Δ'))
    ≐〈 refl≐ ∘≐ (refl≐ ∘≐ asslemma S (Γ ++ Γ') Δ Δ') 〉 
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ⊗ id ∘ (lemma' 〈 S ∣ Γ ++ Γ' 〉 Δ Δ' ∘ 〈〉++ S (Γ ++ Γ') (Δ ++ Δ')))
    ≐〈 refl≐ ∘≐ sym≐ ass 〉 
      sound g ⊗ sound g' ∘ ([ h ∣ Δ ]f ⊗ id ∘ lemma' 〈 S ∣ Γ ++ Γ' 〉 Δ Δ' ∘ 〈〉++ S (Γ ++ Γ') (Δ ++ Δ'))
    ≐〈 refl≐ ∘≐ (lemma5 Δ Δ' h ∘≐ refl≐) 〉
      sound g ⊗ sound g' ∘ (lemma' (A ⊗ B) Δ Δ' ∘ [ h ∣ Δ ++ Δ' ]f ∘ 〈〉++ S (Γ ++ Γ') (Δ ++ Δ'))
    ≐〈 sym≐ ass 〉 
      sound g ⊗ sound g' ∘ (lemma' (_ ⊗ _) Δ Δ' ∘ [ h ∣ Δ ++ Δ' ]f) ∘ 〈〉++ S (Γ ++ Γ') (Δ ++ Δ')
    ≐〈 sym≐ ass ∘≐ refl≐ 〉 
      sound g ⊗ sound g' ∘ lemma' (_ ⊗ _) Δ Δ' ∘ [ h ∣ Δ ++ Δ' ]f ∘ 〈〉++ S (Γ ++ Γ') (Δ ++ Δ') 
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

  soundccut : {T : Stp} → {Γ Δ : Cxt} →  (Δ₀ : Cxt) → {Δ' : Cxt} → {A C : Tm}  → 
       (f : nothing ∣ Γ ⊢ A) → (g : T ∣ Δ ⊢ C) → (p : Δ ≡ Δ₀ ++ A ∷ Δ') →
                 sound (ccut Δ₀ f g p) 
                  ≐ ccomp {T} {Γ} {Δ} Δ₀ {Δ'} {A} {C} (sound g) (sound f) p
  soundccut Δ₀ f ax p = ⊥-elim ([]disj∷ Δ₀ p)
  soundccut Δ₀ f (uf {Δ} {B} g) p with cases∷ Δ₀ p 
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
  soundccut Δ₀ f Ir p = ⊥-elim ([]disj∷ Δ₀ p)
  soundccut Δ₀ {Δ'} f (⊗r {S} {Δ*}{Γ'} g g') p with cases++ Δ₀ Δ* Δ' Γ' p
  soundccut {Γ = Γ} Δ₀ {.(Γ₀ ++ Γ')} {A} f (⊗r {S} {.(Δ₀ ++ A ∷ Γ₀)} {Γ'} g g') refl | inj₁ (Γ₀ , refl , refl) =
    let 
      h = id ⊗ sound f ∘ lemma S Δ₀ Γ
    in
      proof
        sound (ccut Δ₀ f g refl) ⊗ sound g' ∘ lemma S (Δ₀ ++ Γ ++ Γ₀) Γ'
    ≐〈 soundccut Δ₀ f g refl ⊗≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ id ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ∘ [ h ∣ Γ₀ ]f ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀) ⊗ sound g' ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ'    
    ≐〈 (sym≐ rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐) ⊗≐ rid ∘≐ refl≐  〉
      (sound g ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ∘ [ h ∣ Γ₀ ]f ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀) ⊗ (sound g' ∘ id) ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ'
    ≐〈 f⊗∘ ∘≐ refl≐ 〉
      (sound g ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ∘ [ h ∣ Γ₀ ]f) ⊗ sound g' ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ'
    ≐〈 refl≐ ⊗≐ rid ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ∘ [ h ∣ Γ₀ ]f) ⊗ (sound g' ∘ id) ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' 
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐  〉
      (sound g ∘ ++〈〉 S Δ₀ (A ∷ Γ₀)) ⊗ sound g' 
      ∘ [ h ∣ Γ₀ ]f ⊗ id ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' 
    ≐〈 refl≐ ⊗≐ rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐  〉
      (sound g ∘ ++〈〉 S Δ₀ (A ∷ Γ₀)) ⊗ (sound g' ∘ id) 
      ∘ [ h ∣ Γ₀ ]f ⊗ id ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ' 
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ [ h ∣ Γ₀ ]f ⊗ id ∘ 〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ'  
    ≐〈 ass 〉
      sound g ⊗ sound g' ∘ ++〈〉 S Δ₀ (A ∷ Γ₀) ⊗ id 
      ∘ [ h ∣ Γ₀ ]f ⊗ id ∘ (〈〉++ S (Δ₀ ++ Γ) Γ₀ ⊗ id 
      ∘ lemma S ((Δ₀ ++ Γ) ++ Γ₀) Γ')
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
      sound g ⊗ sound g' ∘ (lemma S (Δ₀ ++ A ∷ Γ₀) Γ' 
      ∘ ++〈〉 S Δ₀ (A ∷ Γ₀ ++ Γ')) 
      ∘ [ h ∣ Γ₀ ++ Γ' ]f ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ')
    ≐〈 sym≐ ass ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ lemma S (Δ₀ ++ A ∷ Γ₀) Γ'
      ∘ ++〈〉 S Δ₀ (A ∷ Γ₀ ++ Γ')
      ∘ [ h ∣ Γ₀ ++ Γ' ]f ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ')
    ≐〈 rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ lemma S (Δ₀ ++ A ∷ Γ₀) Γ' ∘ id
      ∘ ++〈〉 S Δ₀ (A ∷ Γ₀ ++ Γ') 
      ∘ [ h ∣ Γ₀ ++ Γ' ]f ∘ 〈〉++ S (Δ₀ ++ Γ) (Γ₀ ++ Γ') 
    qed
  soundccut {.S} {Γ} {._} .(Γ₀ ++ Γ') {Δ'} {A} f (⊗r {S} {Γ₀} {.(Γ' ++ A ∷ Δ')} g g') refl
     | inj₂ (Γ' , refl , refl) = 
--    let 
--      q = trans (sym (++ass Γ₀)) (cong₂ _++_ (sym (++ass Γ₀ {Γ'} {Γ})) refl)
    proof 
      sound g ⊗ sound (ccut Γ' f g' refl) ∘ lemma S Γ₀ (Γ' ++ Γ ++ Δ')
    ≐〈 refl≐ ⊗≐ soundccut Γ' f g' refl ∘≐ refl≐ 〉
      sound g ⊗ (sound g' ∘ id ∘ ++[] I Γ' (A ∷ Δ') 
      ∘ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ∘ []++ I (Γ' ++ Γ) Δ') 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
    ≐〈 rid ⊗≐ (sym≐ rid ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐) ∘≐ refl≐ 〉
      (sound g ∘ id) ⊗ (sound g' ∘ ++[] I Γ' (A ∷ Δ') 
      ∘ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ∘ []++ I (Γ' ++ Γ) Δ') 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
    ≐〈 f⊗∘ ∘≐ refl≐ 〉
      sound g ⊗ (sound g' ∘ ++[] I Γ' (A ∷ Δ') 
      ∘ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ) ∘ id ⊗ []++ I (Γ' ++ Γ) Δ' 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
    ≐〈 rid ⊗≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ id) ⊗ (sound g' ∘ ++[] I Γ' (A ∷ Δ') 
      ∘ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ) ∘ id ⊗ []++ I (Γ' ++ Γ) Δ' 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ (sound g' ∘ ++[] I Γ' (A ∷ Δ')) 
      ∘ id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ∘ id ⊗ []++ I (Γ' ++ Γ) Δ' 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
    ≐〈 rid ⊗≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      (sound g ∘ id) ⊗ (sound g' ∘ ++[] I Γ' (A ∷ Δ')) 
      ∘ id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ∘ id ⊗ []++ I (Γ' ++ Γ) Δ' 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
    ≐〈 f⊗∘ ∘≐ refl≐ ∘≐ refl≐ ∘≐ refl≐ 〉
      sound g ⊗ sound g' ∘ id ⊗ ++[] I Γ' (A ∷ Δ') 
      ∘ id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f ∘ id ⊗ []++ I (Γ' ++ Γ) Δ' 
      ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ')
    ≐〈 trans≐ ass (trans≐ ass ass) 〉
      sound g ⊗ sound g'
      ∘ (id ⊗ ++[] I Γ' (A ∷ Δ') 
         ∘ (id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f
            ∘ (id ⊗ []++ I (Γ' ++ Γ) Δ' 
               ∘ lemma S Γ₀ ((Γ' ++ Γ) ++ Δ'))))
    ≐〈 refl≐ ∘≐ (refl≐ ∘≐ (refl≐ ∘≐ (refl≐ ∘≐ rid)))  〉
      sound g ⊗ sound g'
      ∘ (id ⊗ ++[] I Γ' (A ∷ Δ') 
         ∘ (id ⊗ [ id ⊗ sound f ∘ lemma' I Γ' Γ ∣ Δ' ]f
            ∘ (id ⊗ []++ I (Γ' ++ Γ) Δ' 
               ∘ (lemma S Γ₀ ((Γ' ++ Γ) ++ Δ') ∘ id))))
    ≐〈 refl≐ ∘≐ lemma11 S Γ₀ Γ' Γ Δ' f 〉
      sound g ⊗ sound g'
      ∘ (lemma S Γ₀ (Γ' ++ A ∷ Δ')
         ∘ (id
            ∘ (++〈〉 S (Γ₀ ++ Γ') (A ∷ Δ')
               ∘ ([ id ⊗ sound f ∘ lemma S (Γ₀ ++ Γ') Γ ∣ Δ' ]f
                  ∘ 〈〉++ S ((Γ₀ ++ Γ') ++ Γ) Δ'))))
    ≐〈 sym≐ (trans≐ ass (trans≐ ass (trans≐ ass ass))) 〉
      sound g ⊗ sound g' ∘ lemma S Γ₀ (Γ' ++ A ∷ Δ') ∘ id 
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


≈sound≐ : {S : Stp}{Γ : Cxt}{A : Tm}
  → {f g : S ∣ Γ ⊢ A} → f ≈ g → sound f ≐ sound g
≈sound≐ refl≈ = refl≐
≈sound≐ (sym≈ p) = sym≐ (≈sound≐ p)
≈sound≐ (trans≈ p p') = trans≐ (≈sound≐ p) (≈sound≐ p')
≈sound≐ (conguf p) = ≈sound≐ p ∘≐ refl≐
≈sound≐ (cong⊗l p) = ≈sound≐ p
≈sound≐ (congIl p) = ≈sound≐ p
≈sound≐ (cong⊗r p p') = (≈sound≐ p) ⊗≐ (≈sound≐ p') ∘≐ refl≐
≈sound≐ axI = refl≐
≈sound≐ ax⊗ =
  proof
  id
  ≐〈 lαρ 〉
  id ⊗ l ∘ α ∘ ρ ⊗ id
  ≐〈 ass 〉
  id ⊗ l ∘ (α ∘ ρ ⊗ id)
  ≐〈 refl≐ ⊗≐ sym≐ lid ∘≐ sym≐ lid 〉
  id ⊗ (id ∘ l) ∘ (id ∘ (α ∘ ρ ⊗ id))
  ≐〈 refl≐ ∘≐ sym≐ ass 〉
  id ⊗ (id ∘ l) ∘ (id ∘ α ∘ ρ ⊗ id)
  qed
≈sound≐ (⊗ruf {Γ}{Δ}{A}{A'}{B}{f}{g}) =
  proof
  ((sound f ∘ [ l ∣ Γ ]f) ⊗ sound g) ∘ lemma' (I ⊗ A') Γ Δ
  ≐〈 refl≐ ⊗≐ rid ∘≐ refl≐ 〉
  ((sound f ∘ [ l ∣ Γ ]f) ⊗ (sound g ∘ id)) ∘ lemma' (I ⊗ A') Γ Δ
  ≐〈 f⊗∘ ∘≐ refl≐ 〉
  (sound f ⊗ sound g) ∘ ([ l ∣ Γ ]f ⊗ id) ∘ lemma' (I ⊗ A') Γ Δ
  ≐〈 ass 〉
  (sound f ⊗ sound g) ∘ (([ l ∣ Γ ]f ⊗ id) ∘ lemma' (I ⊗ A') Γ Δ)
  ≐〈 refl≐ ∘≐ lemma5 Γ Δ l 〉 
  (sound f ⊗ sound g) ∘ (lemma' A' Γ Δ ∘ [ l ∣ Γ ++ Δ ]f)
  ≐〈 sym≐ ass 〉
  (sound f ⊗ sound g) ∘ lemma' A' Γ Δ ∘ [ l ∣ Γ ++ Δ ]f
  qed
≈sound≐ ⊗rIl = refl≐
≈sound≐ ⊗r⊗l = refl≐

⊗l⋆ : (S : Stp) → (Γ : Cxt) → {Δ : Cxt}{C : Tm} → S ∣ Γ ++ Δ ⊢ C → just 〈 S ∣ Γ 〉 ∣ Δ ⊢ C
⊗l⋆ (just A) [] f = f
⊗l⋆ (just A) (B ∷ Γ) f = ⊗l⋆ (just (A ⊗ B)) Γ (⊗l f)
⊗l⋆ nothing [] f = Il f
⊗l⋆ nothing (B ∷ Γ) f = ⊗l⋆ (just (I ⊗ B)) Γ (⊗l (Il f))

⊗l-1⋆ : (S : Stp) → (Γ : Cxt) → {Δ : Cxt} {C : Tm} → just 〈 S ∣ Γ 〉 ∣ Δ ⊢ C → S ∣ Γ ++ Δ ⊢ C
⊗l-1⋆ (just A) [] f = f
⊗l-1⋆ (just A) (B ∷ Γ) f = ⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f)
⊗l-1⋆ nothing [] f = Il-1 f
⊗l-1⋆ nothing (B ∷ Γ) f = Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f))

cong⊗l⋆ : {S : Stp}{Γ Δ : Cxt}{C : Tm}{f g : S ∣ Γ ++ Δ ⊢ C} → f ≈ g → ⊗l⋆ S Γ {Δ} f ≈ ⊗l⋆ S Γ g
cong⊗l⋆ {just A} {[]} p = p
cong⊗l⋆ {just A} {B ∷ Γ} p = cong⊗l⋆ {just (A ⊗ B)} {Γ} (cong⊗l p)
cong⊗l⋆ {nothing} {[]} p = congIl p
cong⊗l⋆ {nothing} {B ∷ Γ} p = cong⊗l⋆ {just (I ⊗ B)} {Γ} (cong⊗l (congIl p))

cong⊗l-1⋆ : {S : Stp}{Γ Δ : Cxt}{C : Tm}{f g : just 〈 S ∣ Γ 〉 ∣ Δ ⊢ C} → f ≈ g → ⊗l-1⋆ S Γ {Δ} f ≈ ⊗l-1⋆ S Γ g
cong⊗l-1⋆ {just A} {[]} p = p
cong⊗l-1⋆ {just A} {B ∷ Γ} p = cong⊗l-1 (cong⊗l-1⋆ {just (A ⊗ B)} {Γ} p)
cong⊗l-1⋆ {nothing} {[]} p = congIl-1 p
cong⊗l-1⋆ {nothing} {B ∷ Γ} p = congIl-1 (cong⊗l-1 (cong⊗l-1⋆ {just (I ⊗ B)} {Γ} p))

cmplt-uf-lemma : {A B : Tm}(Γ : Cxt)(f : A ⇒ B) → cmplt [ f ∣ Γ ]f ≈ ⊗l⋆ (just A) Γ (scut (cmplt f) (⊗l-1⋆ (just B) Γ ax))
cmplt-uf-lemma [] f = sym≈ (≡-to-≈ (scut-unit (cmplt f)))
cmplt-uf-lemma {A}{B} (C ∷ Γ) f =
  proof≈
  cmplt [ f ⊗ id ∣ Γ ]f
  ≈〈 cmplt-uf-lemma Γ (f ⊗ id) 〉
  ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (scut (⊗r (cmplt f) (uf ax)) (⊗l-1⋆ (just (B ⊗ C)) Γ ax)))
  ≈〈 cong⊗l⋆ (cong⊗l (scut≈2 (⊗r (cmplt f) (uf ax)) (sym≈ (⊗l-iso (⊗l-1⋆ (just (B ⊗ C)) Γ ax))))) 〉
  ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (scut (⊗r (cmplt f) (uf ax)) (⊗l (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ ax)))))
  ≈〈 refl≈ 〉
  ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (ccut [] (uf ax) (scut (cmplt f) (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ ax))) refl))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just (A ⊗ C)) Γ) (cong ⊗l (ccut-unit [] (scut (cmplt f) (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ ax))) refl))) 〉
  ⊗l⋆ (just (A ⊗ C)) Γ (⊗l (scut (cmplt f) (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Γ ax))))
  qed≈

scut⊗l⋆ : {S : Stp}{Γ : Cxt}{A C : Tm}{f : S ∣ Γ ⊢ A}{g : just A ∣ [] ⊢ C}
  → scut (⊗l⋆ S Γ {[]} f) g ≡ ⊗l⋆ S Γ (scut f g)
scut⊗l⋆ {just A} {[]} = refl
scut⊗l⋆ {just A} {B ∷ Γ} = scut⊗l⋆ {just (A ⊗ B)} {Γ}
scut⊗l⋆ {nothing} {[]} = refl
scut⊗l⋆ {nothing} {B ∷ Γ} = scut⊗l⋆ {just (I ⊗ B)} {Γ}

scut⊗l-1⋆ : {S : Stp}{Γ Δ : Cxt}{A C : Tm}{f : just 〈 S ∣ Γ 〉 ∣ [] ⊢ A}{g : just A ∣ Δ ⊢ C}
  → scut (⊗l-1⋆ S Γ f) g ≡ ⊗l-1⋆ S Γ (scut f g)
scut⊗l-1⋆ {just A} {[]} = refl
scut⊗l-1⋆ {just A} {B ∷ Γ}{f = f}{g} =
  begin
  scut (⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f)) g
  ≡⟨ sym (scut⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ f) g) ⟩
  ⊗l-1 (scut (⊗l-1⋆ (just (A ⊗ B)) Γ f) g)
  ≡⟨ cong ⊗l-1 (scut⊗l-1⋆ {just (A ⊗ B)} {Γ}) ⟩
  ⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ (scut f g))
  ∎
scut⊗l-1⋆ {nothing} {[]} {f = f}{g} = sym (scutIl-1 f g)
scut⊗l-1⋆ {nothing} {B ∷ Γ} {f = f}{g} =
  begin
  scut (Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f))) g
  ≡⟨ sym (scutIl-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)) g) ⟩
  Il-1 (scut (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f)) g)
  ≡⟨ cong Il-1 (sym (scut⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ f) g)) ⟩
  Il-1 (⊗l-1 (scut (⊗l-1⋆ (just (I ⊗ B)) Γ f) g))
  ≡⟨ cong Il-1 (cong ⊗l-1 (scut⊗l-1⋆ {just (I ⊗ B)} {Γ})) ⟩
  Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ (scut f g)))
  ∎

⊗l⋆-iso : {S : Stp}{Γ Δ : Cxt}{C : Tm}{f : S ∣ Γ ++ Δ ⊢ C} → ⊗l-1⋆ S Γ (⊗l⋆ S Γ {Δ} f) ≡ f
⊗l⋆-iso {just A} {[]} = refl
⊗l⋆-iso {just A} {B ∷ Γ} = cong ⊗l-1 (⊗l⋆-iso {just (A ⊗ B)} {Γ})
⊗l⋆-iso {nothing} {[]} = refl
⊗l⋆-iso {nothing} {B ∷ Γ} = cong Il-1 (cong ⊗l-1 (⊗l⋆-iso {just (I ⊗ B)} {Γ}))

⊗r⊗l⋆ : {S : Stp}{Γ Δ : Cxt}{A B : Tm}
    → {f : S ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (⊗l⋆ S Γ {[]} f) g ≈ ⊗l⋆ S Γ {Δ} (⊗r f g)
⊗r⊗l⋆ {just A} {[]} = refl≈
⊗r⊗l⋆ {just A} {B ∷ Γ}{Δ}{C}{D}{f}{g} =
  proof≈
  ⊗r (⊗l⋆ (just (A ⊗ B)) Γ (⊗l f)) g
  ≈〈 ⊗r⊗l⋆ {just (A ⊗ B)}{Γ} 〉 
  ⊗l⋆ (just (A ⊗ B)) Γ (⊗r (⊗l f) g)
  ≈〈 cong⊗l⋆ {just (A ⊗ B)} {Γ} ⊗r⊗l 〉 
  ⊗l⋆ (just (A ⊗ B)) Γ (⊗l (⊗r f g))
  qed≈
⊗r⊗l⋆ {nothing} {[]} = ⊗rIl
⊗r⊗l⋆ {nothing} {B ∷ Γ}{Δ}{C}{D}{f}{g} =
  proof≈
  ⊗r (⊗l⋆ (just (I ⊗ B)) Γ (⊗l (Il f))) g
  ≈〈 ⊗r⊗l⋆ {just (I ⊗ B)}{Γ} 〉 
  ⊗l⋆ (just (I ⊗ B)) Γ (⊗r (⊗l (Il f)) g)
  ≈〈 cong⊗l⋆ {just (I ⊗ B)} {Γ} ⊗r⊗l 〉 
  ⊗l⋆ (just (I ⊗ B)) Γ (⊗l (⊗r (Il f) g))
  ≈〈 cong⊗l⋆ {just (I ⊗ B)} {Γ} (cong⊗l ⊗rIl) 〉 
  ⊗l⋆ (just (I ⊗ B)) Γ (⊗l (Il (⊗r f g)))
  qed≈

cmplt-⊗r-lemma'' : {A B : Tm}{Δ : Cxt}
  → cmplt (lemma'' A B Δ) ≈ ⊗l⋆ (just (A ⊗ B)) Δ (⊗l (⊗r ax (uf (⊗l-1⋆ (just B) Δ ax))))
cmplt-⊗r-lemma'' {Δ = []} = ax⊗
cmplt-⊗r-lemma'' {A}{B}{C ∷ Δ}  =
  proof≈
  scut (cmplt [ α ∣ Δ ]f) (cmplt (lemma'' A (B ⊗ C) Δ))
  ≈〈 scut≈2 (cmplt [ α ∣ Δ ]f) (cmplt-⊗r-lemma'' {Δ = Δ}) 〉 
  scut (cmplt [ α ∣ Δ ]f) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ ax)))))
  ≈〈 scut≈ (cmplt-uf-lemma Δ α) 〉 
  scut (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ ax))) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ ax)))))
  ≈〈 ≡-to-≈ (scut⊗l⋆ {just (A ⊗ B ⊗ C)} {Δ}) 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} ax)) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} ax))))))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (sym (scutscut-vass (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} ax) _))) 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (scut (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} ax) (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} ax)))))))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong (scut (cmplt α)) (scut⊗l-1⋆ {just (A ⊗ (B ⊗ C))}{Δ}))) 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ (scut ax (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} ax))))))))
  ≈〈 refl≈ 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l-1⋆ (just (A ⊗ (B ⊗ C))) Δ (⊗l⋆ (just (A ⊗ (B ⊗ C))) Δ {[]} (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} ax)))))))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong (scut (cmplt α)) (⊗l⋆-iso {just (A ⊗ (B ⊗ C))}{Δ}))) 〉
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (scut (cmplt α) (⊗l (⊗r ax (uf (⊗l-1⋆ (just (B ⊗ C)) Δ {[]} ax)))))
  ≈〈 refl≈ 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (⊗l (⊗l (⊗r ax (uf (scut (⊗r ax (uf ax)) (⊗l-1⋆ (just (B ⊗ C)) Δ ax))))))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just (A ⊗ B ⊗ C)) Δ) (cong ⊗l (cong ⊗l (cong (⊗r ax) (cong uf (sym (⊗l-1-alt (⊗l-1⋆ (just (B ⊗ C)) Δ ax)))))))) 〉 
  ⊗l⋆ (just (A ⊗ B ⊗ C)) Δ (⊗l (⊗l (⊗r ax (uf (⊗l-1 (⊗l-1⋆ (just (B ⊗ C)) Δ ax))))))
  qed≈

⊗l-1⋆-lem : {Γ : Cxt}{C : Tm}{f : just [ I ∣ Γ ] ∣ [] ⊢ C}
  → Il-1 (⊗l-1⋆ (just I) Γ f) ≡ ⊗l-1⋆ nothing Γ f
⊗l-1⋆-lem {[]} = refl
⊗l-1⋆-lem {B ∷ Γ} = refl

⊗l⋆-lem : {Γ : Cxt}{C : Tm}{f : nothing ∣ Γ ⊢ C}
  → ⊗l⋆ (just I) Γ {[]} (⊗r ax f) ≈ ⊗l⋆ nothing Γ (⊗r Ir f)
⊗l⋆-lem {[]} = trans≈ (cong⊗r axI refl≈) ⊗rIl
⊗l⋆-lem {B ∷ Γ} = cong⊗l⋆ {just (I ⊗ B)} {Γ} (cong⊗l (trans≈ (cong⊗r axI refl≈) ⊗rIl))

cmplt-⊗r-lemma : {S : Stp}{Γ Δ : Cxt}
  → cmplt (lemma S Γ Δ) ≈ ⊗l⋆ S (Γ ++ Δ) (⊗r (⊗l-1⋆ S Γ ax) (⊗l-1⋆ nothing Δ ax))
cmplt-⊗r-lemma {just A} {[]} {Δ}  =
  proof≈
  scut (cmplt [ ρ ∣ Δ ]f) (cmplt (lemma'' A I Δ))
  ≈〈 scut≈ (cmplt-uf-lemma Δ ρ) 〉
  scut (⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ ax))) (cmplt (lemma'' A I Δ))
  ≈〈 ≡-to-≈ (scut⊗l⋆ {just A}{Δ}) 〉
  ⊗l⋆ (just A) Δ (scut (scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ ax)) (cmplt (lemma'' A I Δ)))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just A) Δ) (sym (scutscut-vass (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ ax) _))) 〉
  ⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (scut (⊗l-1⋆ (just (A ⊗ I)) Δ ax) (cmplt (lemma'' A I Δ))))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just A) Δ) (cong (scut (⊗r ax Ir)) (scut⊗l-1⋆ {just (A ⊗ I)}{Δ}))) 〉
  ⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ (scut ax (cmplt (lemma'' A I Δ)))))
  ≈〈 refl≈ 〉
  ⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ (cmplt (lemma'' A I Δ))))
  ≈〈 cong⊗l⋆ {just A} {Δ} (scut≈2 (⊗r ax Ir) (cong⊗l-1⋆ {just (A ⊗ I)} {Δ} (cmplt-⊗r-lemma'' {A}{I}{Δ}))) 〉
  ⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (A ⊗ I)) Δ {[]} (⊗l⋆ (just (A ⊗ I)) Δ (⊗l (⊗r ax (uf (⊗l-1⋆ (just I) Δ ax)))))))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just A) Δ) (cong (scut (⊗r ax Ir)) (⊗l⋆-iso {just (A ⊗ I)}{Δ}))) 〉
  ⊗l⋆ (just A) Δ (scut (⊗r ax Ir) (⊗l (⊗r ax (uf (⊗l-1⋆ (just I) Δ ax)))))
  ≈〈 refl≈ 〉
  ⊗l⋆ (just A) Δ (⊗r ax (Il-1 (⊗l-1⋆ (just I) Δ ax)))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just A) Δ) (cong (⊗r ax) (⊗l-1⋆-lem {Δ}))) 〉
  ⊗l⋆ (just A) Δ (⊗r ax (⊗l-1⋆ nothing Δ ax))
  qed≈
cmplt-⊗r-lemma {just A} {B ∷ Γ} {Δ} =
  proof≈
  cmplt (lemma (just A) (B ∷ Γ) Δ)
  ≈〈 cmplt-⊗r-lemma {just (A ⊗ B)} {Γ} 〉
  ⊗l⋆ (just (A ⊗ B)) (Γ ++ Δ) (⊗r (⊗l-1⋆ (just (A ⊗ B)) Γ ax) (⊗l-1⋆ nothing Δ ax))
  ≈〈 cong⊗l⋆ {just (A ⊗ B)} {Γ ++ Δ} (cong⊗r (sym≈ (⊗l-iso (⊗l-1⋆ (just (A ⊗ B)) Γ ax) )) refl≈) 〉
  ⊗l⋆ (just (A ⊗ B)) (Γ ++ Δ) (⊗r (⊗l (⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ ax))) (⊗l-1⋆ nothing Δ ax))
  ≈〈 cong⊗l⋆ {just (A ⊗ B)} {Γ ++ Δ} ⊗r⊗l 〉
  ⊗l⋆ (just (A ⊗ B)) (Γ ++ Δ) (⊗l (⊗r (⊗l-1 (⊗l-1⋆ (just (A ⊗ B)) Γ ax)) (⊗l-1⋆ nothing Δ ax)))
  qed≈
cmplt-⊗r-lemma {nothing} {[]} {Δ} =
  proof≈
  scut (cmplt [ ρ ∣ Δ ]f) (cmplt (lemma'' I I Δ))
  ≈〈 scut≈ (cmplt-uf-lemma Δ ρ) 〉
  scut (⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ ax))) (cmplt (lemma'' I I Δ))
  ≈〈 ≡-to-≈ (scut⊗l⋆ {just I}{Δ}) 〉
  ⊗l⋆ (just I) Δ (scut (scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ ax)) (cmplt (lemma'' I I Δ)))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just I) Δ) (sym (scutscut-vass (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ ax) _))) 〉
  ⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (scut (⊗l-1⋆ (just (I ⊗ I)) Δ ax) (cmplt (lemma'' I I Δ))))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just I) Δ) (cong (scut (⊗r ax Ir)) (scut⊗l-1⋆ {just (I ⊗ I)}{Δ}))) 〉
  ⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ (scut ax (cmplt (lemma'' I I Δ)))))
  ≈〈 refl≈ 〉
  ⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ (cmplt (lemma'' I I Δ))))
  ≈〈 cong⊗l⋆ {just I} {Δ} (scut≈2 (⊗r ax Ir) (cong⊗l-1⋆ {just (I ⊗ I)} {Δ} (cmplt-⊗r-lemma'' {I}{I}{Δ}))) 〉
  ⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (⊗l-1⋆ (just (I ⊗ I)) Δ {[]} (⊗l⋆ (just (I ⊗ I)) Δ (⊗l (⊗r ax (uf (⊗l-1⋆ (just I) Δ ax)))))))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just I) Δ) (cong (scut (⊗r ax Ir)) (⊗l⋆-iso {just (I ⊗ I)}{Δ}))) 〉
  ⊗l⋆ (just I) Δ (scut (⊗r ax Ir) (⊗l (⊗r ax (uf (⊗l-1⋆ (just I) Δ ax)))))
  ≈〈 refl≈ 〉
  ⊗l⋆ (just I) Δ (⊗r ax (Il-1 (⊗l-1⋆ (just I) Δ ax)))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just I) Δ) (cong (⊗r ax) (⊗l-1⋆-lem {Δ}))) 〉
  ⊗l⋆ (just I) Δ {[]} (⊗r ax (⊗l-1⋆ nothing Δ ax))
  ≈〈 ⊗l⋆-lem {Δ} 〉
  ⊗l⋆ nothing Δ {[]} (⊗r Ir (⊗l-1⋆ nothing Δ ax))
  qed≈
cmplt-⊗r-lemma {nothing} {B ∷ Γ} {Δ} = 
  proof≈
  cmplt (lemma nothing (B ∷ Γ) Δ)
  ≈〈 cmplt-⊗r-lemma {just (I ⊗ B)} {Γ} 〉
  ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗r (⊗l-1⋆ (just (I ⊗ B)) Γ ax) (⊗l-1⋆ nothing Δ ax))
  ≈〈 cong⊗l⋆ {just (I ⊗ B)} {Γ ++ Δ} (cong⊗r (sym≈ (⊗l-iso (⊗l-1⋆ (just (I ⊗ B)) Γ ax) )) refl≈) 〉
  ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗r (⊗l (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax))) (⊗l-1⋆ nothing Δ ax))
  ≈〈 cong⊗l⋆ {just (I ⊗ B)} {Γ ++ Δ} ⊗r⊗l 〉
  ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗l (⊗r (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax)) (⊗l-1⋆ nothing Δ ax)))
  ≈〈 cong⊗l⋆ {just (I ⊗ B)} {Γ ++ Δ} (cong⊗l (cong⊗r (sym≈ (Il-iso (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax)))) refl≈)) 〉
  ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗l (⊗r (Il (Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax)))) (⊗l-1⋆ nothing Δ ax)))
  ≈〈 cong⊗l⋆ {just (I ⊗ B)} {Γ ++ Δ} (cong⊗l ⊗rIl) 〉
  ⊗l⋆ (just (I ⊗ B)) (Γ ++ Δ) (⊗l (Il (⊗r (Il-1 (⊗l-1 (⊗l-1⋆ (just (I ⊗ B)) Γ ax))) (⊗l-1⋆ nothing Δ ax))))
  qed≈
  
ccut-lem : {S : Stp}{Γ Δ : Cxt}{A B C : Tm}
  → {f : nothing ∣ Γ ⊢ A}{g : S ∣ Δ ⊢ B}{h : nothing ∣ A ∷ [] ⊢ C}
  → ccut Δ f (⊗r g h) refl ≡ ⊗r g (ccut [] f h refl)
ccut-lem {Δ = Δ}{A = A} with cases++ Δ Δ [] (A ∷ []) refl
ccut-lem {Δ = Δ} {A} | inj₁ (Δ₀ , p , q) = ⊥-elim ([]disj∷ Δ₀ q)
ccut-lem {Δ = Δ} {A} | inj₂ (Δ₀ , p , q) with canc++ [] Δ₀ {A ∷ []} p
ccut-lem {Δ = Δ} {A} | inj₂ (.[] , refl , refl) | refl = refl

cmpltsound' : {S : Stp} → {Γ : Cxt} → {C : Tm} → (f : S ∣ Γ ⊢ C) → cmplt (sound f) ≈ ⊗l⋆ S Γ f
cmpltsound' ax = refl≈
cmpltsound' (uf {Γ}{A} f) =
  proof≈
  scut (cmplt [ l ∣ Γ ]f) (cmplt (sound f))
  ≈〈 scut≈2 (cmplt [ l ∣ Γ ]f) (cmpltsound' f) 〉
  scut (cmplt [ l ∣ Γ ]f) (⊗l⋆ (just A) Γ f)
  ≈〈 scut≈ (cmplt-uf-lemma Γ l) 〉
  scut (⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ ax))))) (⊗l⋆ (just A) Γ f)
  ≈〈 ≡-to-≈ (scut⊗l⋆ {just (I ⊗ A)}{Γ})  〉
  ⊗l⋆ (just (I ⊗ A)) Γ (scut (⊗l (Il (uf (⊗l-1⋆ (just A) Γ ax)))) (⊗l⋆ (just A) Γ {[]} f))
  ≈〈 refl≈ 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (scut (⊗l-1⋆ (just A) Γ ax) (⊗l⋆ (just A) Γ {[]} f)))))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just (I ⊗ A)) Γ) (cong ⊗l (cong Il (cong uf (scut⊗l-1⋆ {just A}{Γ}))))) 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ (scut ax (⊗l⋆ (just A) Γ {[]} f))))))
  ≈〈 refl≈ 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf (⊗l-1⋆ (just A) Γ (⊗l⋆ (just A) Γ {[]} f)))))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ (just (I ⊗ A)) Γ) (cong ⊗l (cong Il (cong uf (⊗l⋆-iso {just A}{Γ}))))) 〉
  ⊗l⋆ (just (I ⊗ A)) Γ (⊗l (Il (uf f)))
  qed≈
cmpltsound' Ir = axI
cmpltsound' (⊗r {S}{Γ}{Δ} f f') = 
  proof≈
  scut (cmplt (lemma S Γ Δ)) (⊗l (⊗r (cmplt (sound f)) (uf (cmplt (sound f')))))
  ≈〈 scut≈2 (cmplt (lemma S Γ Δ)) (cong⊗l (cong⊗r (cmpltsound' f) (conguf (cmpltsound' f')))) 〉
  scut (cmplt (lemma S Γ Δ)) (⊗l (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f'))))
  ≈〈 scut≈ (cmplt-⊗r-lemma {S}{Γ}{Δ}) 〉
  scut (⊗l⋆ S (Γ ++ Δ) (⊗r (⊗l-1⋆ S Γ ax) (⊗l-1⋆ nothing Δ ax))) (⊗l (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f'))))
  ≈〈 ≡-to-≈ (scut⊗l⋆ {S}{Γ ++ Δ}) 〉
  ⊗l⋆ S (Γ ++ Δ) (scut (⊗r (⊗l-1⋆ S Γ ax) (⊗l-1⋆ nothing Δ ax)) (⊗l (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f')))))
  ≈〈 refl≈ 〉
  ⊗l⋆ S (Γ ++ Δ) (ccut Γ (⊗l-1⋆ nothing Δ ax) (scut (⊗l-1⋆ S Γ ax) (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f')))) refl)
  ≈〈 ≡-to-≈ (cong (⊗l⋆ S (Γ ++ Δ)) (cong₂ (ccut Γ (⊗l-1⋆ nothing Δ {[]} ax)) (scut⊗l-1⋆ {S}{Γ}) refl)) 〉
  ⊗l⋆ S (Γ ++ Δ) (ccut Γ (⊗l-1⋆ nothing Δ {[]} ax) (⊗l-1⋆ S Γ {〈 nothing ∣ Δ 〉 ∷ []} (scut ax (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f'))))) refl)
  ≈〈 refl≈ 〉
  ⊗l⋆ S (Γ ++ Δ) (ccut Γ (⊗l-1⋆ nothing Δ {[]} ax) (⊗l-1⋆ S Γ {〈 nothing ∣ Δ 〉 ∷ []} (⊗r (⊗l⋆ S Γ {[]} f) (uf (⊗l⋆ nothing Δ {[]} f')))) refl)
  ≈〈 cong⊗l⋆ {S} {Γ ++ Δ} (ccut≈2 Γ refl (cong⊗l-1⋆ {S} {Γ} (⊗r⊗l⋆ {S}{Γ}))) 〉
  ⊗l⋆ S (Γ ++ Δ) (ccut Γ (⊗l-1⋆ nothing Δ {[]} ax) (⊗l-1⋆ S Γ {〈 nothing ∣ Δ 〉 ∷ []} (⊗l⋆ S Γ {〈 nothing ∣ Δ 〉 ∷ []} (⊗r f (uf (⊗l⋆ nothing Δ {[]} f'))))) refl)
  ≈〈 ≡-to-≈ (cong (⊗l⋆ S (Γ ++ Δ)) (cong₂ (ccut Γ (⊗l-1⋆ nothing Δ {[]} ax)) (⊗l⋆-iso {S} {Γ}) refl)) 〉
  ⊗l⋆ S (Γ ++ Δ) (ccut Γ (⊗l-1⋆ nothing Δ {[]} ax) (⊗r f (uf (⊗l⋆ nothing Δ {[]} f'))) refl)
  ≈〈 ≡-to-≈ (cong (⊗l⋆ S (Γ ++ Δ)) ccut-lem) 〉
  ⊗l⋆ S (Γ ++ Δ) (⊗r f (ccut [] (⊗l-1⋆ nothing Δ {[]} ax) (uf (⊗l⋆ nothing Δ {[]} f')) refl))
  ≈〈 refl≈ 〉
  ⊗l⋆ S (Γ ++ Δ) (⊗r f (scut (⊗l-1⋆ nothing Δ {[]} ax) (⊗l⋆ nothing Δ {[]} f')))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ S (Γ ++ Δ)) (cong (⊗r f) (scut⊗l-1⋆ {nothing} {Δ}))) 〉
  ⊗l⋆ S (Γ ++ Δ) (⊗r f (⊗l-1⋆ nothing Δ {[]} (scut ax (⊗l⋆ nothing Δ {[]} f'))))
  ≈〈 refl≈ 〉
  ⊗l⋆ S (Γ ++ Δ) (⊗r f (⊗l-1⋆ nothing Δ {[]} (⊗l⋆ nothing Δ {[]} f')))
  ≈〈 ≡-to-≈ (cong (⊗l⋆ S (Γ ++ Δ)) (cong (⊗r f) (⊗l⋆-iso {nothing} {Δ}))) 〉
  ⊗l⋆ S (Γ ++ Δ) (⊗r f f')
  qed≈
cmpltsound' (Il {Γ = []} f) = cmpltsound' f
cmpltsound' (Il {Γ = _ ∷ _} f) = cmpltsound' f
cmpltsound' (⊗l f) = cmpltsound' f

cmpltsound : {A B : Tm} → (f : just A ∣ [] ⊢ B) → cmplt (sound f) ≈ f
cmpltsound = cmpltsound'


