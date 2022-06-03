{-# OPTIONS --cubical #-}

module Ring.Core where

open import Level renaming (suc to sucℓ)
open import Cubical.Foundations.Prelude


private
  variable
    ℓ : Level

record Ring (A : Type ℓ) : Type (sucℓ ℓ) where
  field
    1R : A
    0R : A
    _+_ : A → A → A
    _*_ : A → A → A

  field
    id+l
