{-# OPTIONS --safe --without-K #-}

module Felix.Algebra.Laws where

-- standard-library
open import Level
  using (_⊔_; Level)

-- felix
open import Felix.Equiv
  using (Equivalent; refl; _≈_)
open import Felix.Raw
  as Raw
open import Felix.Laws
  as Laws

-- felix-algebra
open import Felix.Algebra.Raw
  as Raw
  hiding (Magma; Semigroup)

private
  variable
    o i ℓ : Level

record Semigroup
  {O : Set o} ⦃ _ : Products O ⦄ ⦃ _ : Operand O ⦄
  (_⇨′_ : O → O → Set ℓ) {q} ⦃ _ : Equivalent q _⇨′_ ⦄
  ⦃ _ : Raw.Category _⇨′_ ⦄ ⦃ _ : Laws.Category _⇨′_ ⦄
  ⦃ _ : Raw.Cartesian _⇨′_ ⦄ ⦃ _ : Laws.Cartesian _⇨′_ ⦄
    : Set (o ⊔ ℓ ⊔ q) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ raw-magma ⦄ : Raw.Magma _⇨_
    ⟨∙⟩-assoc : ⟨∙⟩ ∘ first ⟨∙⟩ ≈ ⟨∙⟩ ∘ second ⟨∙⟩ ∘ assocʳ

open Semigroup ⦃ … ⦄ public
