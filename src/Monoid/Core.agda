{-# OPTIONS --cubical #-}

module Monoid.Core where

open import Cubical.Foundations.Prelude hiding (_∙_)
-- open import Cubical.Foundations.Primitive
open import Cubical.Core.Everything

private
  variable 
    ℓ : Level

record MonoidLaws (M : Type ℓ) (_∙_ : M → M → M) (e : M) : Type ℓ where
  field
    idₗ : (m : M) → e ∙ m ≡ m
    idᵣ : (m : M) → m ∙ e ≡ m
    assoc : (m₁ m₂ m₃ : M) → m₁ ∙ (m₂ ∙ m₃) ≡ (m₁ ∙ m₂) ∙ m₃

  field
    hSet : isSet M

record Monoid (M : Type ℓ) : Set (ℓ-suc ℓ) where
  field
    _∙_ : M → M → M
    e : M
    isMonoid : MonoidLaws M _∙_ e
  

MonoidObj : Type (ℓ-suc ℓ)
MonoidObj = Σ[ M ∈ Type _ ] (Monoid M)


