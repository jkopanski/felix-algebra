{-# OPTIONS --safe --without-K #-}

module Felix.Algebra.Raw where

open import Level
  using (_⊔_; Level)

open import Algebra
  using (Op₁; Op₂)
open import Felix.Homomorphism
  using (Equivalent; Homomorphismₒ; Fₒ)
open import Felix.Raw
  using (Products; _×_; ⊤)

private
  variable
    o i ℓ : Level

record Magma
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_∙_ : Op₂ I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ)
    : Set (o ⊔ i ⊔ ℓ) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_

  field
    ⟨∙⟩ : ∀ {p q : I} → M p × M q ⇨ M (p ∙ q)

open Magma ⦃ … ⦄ public

record Unary
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (f : Op₁ I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ)
    : Set (o ⊔ i ⊔ ℓ) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_

  field
    ⟨f⟩ : ∀ {p : I} → M p ⇨ M (f p)

open Unary ⦃ … ⦄ public

record Element
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (ι : I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ)
    : Set (o ⊔ i ⊔ ℓ) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_

  field
    ⟨ι⟩ : ⊤ ⇨ M ι

open Element ⦃ … ⦄ public

record Semigroup
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_∙_ : Op₂ I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ)
    : Set (o ⊔ i ⊔ ℓ) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ magma ⦄ : Magma _∙_ M _⇨′_

open Semigroup ⦃ … ⦄ public

record Monoid
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_∙_ : Op₂ I) (ι : I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ)
    : Set (o ⊔ i ⊔ ℓ) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ semigroup ⦄ : Semigroup _∙_ M _⇨_
    ⦃ unit      ⦄ : Element ι M _⇨_

open Monoid ⦃ … ⦄ public

record Group
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_∙_ : Op₂ I) (ι : I) (_⁻¹ : Op₁ I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ)
    : Set (o ⊔ i ⊔ ℓ) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ monoid  ⦄ : Monoid _∙_ ι M _⇨_
    ⦃ inverse ⦄ : Unary _⁻¹ M _⇨_

  ⟨⁻¹⟩ = ⟨f⟩

open Group ⦃ … ⦄ public

record Ring
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_+_ _*_ : Op₂ I) (-_ : Op₁ I) (0# 1# : I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ)
    : Set (o ⊔ i ⊔ ℓ) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⦃ +-group ⦄ : Group _+_ 0# -_ M _⇨_
    ⦃ *-monoid ⦄ : Monoid _*_ 1# M _⇨_

  ⟨*⟩ : ∀ {p q : I} → M p × M q ⇨ M (p * q)
  ⟨*⟩ = ⟨∙⟩
  ⟨+⟩ : ∀ {p q : I} → M p × M q ⇨ M (p + q)
  ⟨+⟩ = ⟨∙⟩
  ⟨-⟩ : ∀ {p : I} → M p ⇨ M (- p)
  ⟨-⟩ = ⟨⁻¹⟩
  ⟨0⟩ : ⊤ ⇨ M 0#
  ⟨0⟩ = ⟨ι⟩
  ⟨1⟩ : ⊤ ⇨ M 1#
  ⟨1⟩ = ⟨ι⟩

open Ring ⦃ … ⦄ public
