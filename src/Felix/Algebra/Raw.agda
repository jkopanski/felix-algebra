{-# OPTIONS --safe --without-K #-}

module Felix.Algebra.Raw where

-- standard-library
open import Level
  using (_⊔_; Level)

-- felix
open import Felix.Homomorphism
  using (Equivalent; Homomorphismₒ; Fₒ)
open import Felix.Raw
  using (Products; _×_; ⊤)

private
  variable
    o i ℓ : Level

record Operand (O : Set o) : Set o where
  field
    𝕆 : O

open Operand ⦃ … ⦄ public

record Magma
  {O : Set o} ⦃ _ : Products O ⦄ ⦃ _ : Operand O ⦄
  (_⇨′_ : O → O → Set ℓ)
    : Set (o ⊔ ℓ) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_

  field
    ⟨∙⟩ : 𝕆 × 𝕆 ⇨ 𝕆

open Magma ⦃ … ⦄ public

record Semigroup
  {O : Set o} ⦃ _ : Products O ⦄ ⦃ _ : Operand O ⦄
  (_⇨′_ : O → O → Set ℓ)
    : Set (o  ⊔ ℓ) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ magma ⦄ : Magma _⇨_

open Semigroup ⦃ … ⦄ public
