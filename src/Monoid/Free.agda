{-# OPTIONS --cubical #-}

module Monoid.Free where

open import Level renaming (suc to sucℓ)
open import Cubical.Foundations.Prelude hiding (_∙_)
import Monoid.Core as M

private
  variable 
    ℓ : Level

data Free (I : Type ℓ) : Type ℓ where
  gen : (i : I) → Free I
  e   : Free I
  _∙_ : Free I → Free I → Free I


  idₗ : (f : Free I) → e ∙ f ≡ f
  idᵣ : (f : Free I) → f ∙ e ≡ f
  assoc : (f₁ f₂ f₃ : Free I) → f₁ ∙ (f₂ ∙ f₃) ≡ (f₁ ∙ f₂) ∙ f₃
  hSet  : isSet (Free I)

freeMonoid : {I : Set ℓ} → M.MonoidLaws (Free I) _∙_ e
freeMonoid = 
  record { idₗ = idₗ ; idᵣ = idᵣ ; assoc = assoc ; hSet = hSet }

module RecFreeTy {ℓ'} (I : Type ℓ) where
  record Motives : Set (ℓ-suc ℓ') where
    field
      Freeᴹ : Set ℓ'
  record Methods (M : Motives) : Set (ℓ ⊔ ℓ') where
    open Motives M
    field
      genᴹ : (i : I) → Freeᴹ
      eᴹ   : Freeᴹ
      _∙ᴹ_ : Freeᴹ → Freeᴹ → Freeᴹ


      idₗᴹ : (fᴹ : Freeᴹ) → (eᴹ ∙ᴹ fᴹ) ≡ fᴹ
      idᵣᴹ : {f : Free I} →  (fᴹ : Freeᴹ) → (fᴹ ∙ᴹ eᴹ) ≡ fᴹ
      assocᴹ : (fᴹ gᴹ hᴹ : Freeᴹ) →
        (fᴹ ∙ᴹ (gᴹ ∙ᴹ hᴹ)) ≡ ((fᴹ ∙ᴹ gᴹ) ∙ᴹ hᴹ)

      hSetᴹ  : isSet Freeᴹ

module Init {ℓ'} (I : Type ℓ) where
  open RecFreeTy {ℓ' = ℓ'} I

  initial : (M : M.MonoidObj {ℓ'}) → Free I → fst M
  initial = {!!}

    


module ElimFreeTy {ℓ'} (I : Type ℓ) where
  record Motives : Set (ℓ ⊔ (ℓ-suc ℓ')) where
    field
      Freeᴹ : Free I → Set ℓ'
  record Methods (M : Motives) : Set (ℓ ⊔ (ℓ-suc ℓ')) where
    open Motives M
    field
      genᴹ : (i : I) → Freeᴹ (gen i)
      eᴹ   : Freeᴹ e
      _∙ᴹ_ : ∀ {g h : Free I} → Freeᴹ g → Freeᴹ h → Freeᴹ (g ∙ h)


      idₗᴹ : {f : Free I} → (fᴹ : Freeᴹ f) → PathP (λ i → Freeᴹ (idₗ f i)) (eᴹ ∙ᴹ fᴹ) fᴹ
      idᵣᴹ : {f : Free I} →  (fᴹ : Freeᴹ f) → PathP (λ i → Freeᴹ (idᵣ f i)) (fᴹ ∙ᴹ eᴹ) fᴹ
      assocᴹ : {f g h : Free I} →   (fᴹ : Freeᴹ f)(gᴹ : Freeᴹ g)(hᴹ : Freeᴹ h) →
        PathP (λ i → Freeᴹ (assoc f g h i)) (fᴹ ∙ᴹ (gᴹ ∙ᴹ hᴹ)) ((fᴹ ∙ᴹ gᴹ) ∙ᴹ hᴹ)

      hSetᴹ  : {f : Free I} → isSet (Freeᴹ f)
      
  
