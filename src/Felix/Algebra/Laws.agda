{-# OPTIONS --safe --without-K #-}

module Felix.Algebra.Laws where

open import Algebra
  using (Op₁; Op₂)
open import Level
  using (_⊔_; Level)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Felix.Equiv
  using (Equivalent; refl; _≈_)
open import Felix.Raw
  as Raw
open import Felix.Laws
  as Laws
  hiding (assoc)

open import Felix.Algebra.Raw
  as Raw
  hiding (Magma; Semigroup; Monoid; Group; Ring)

private
  variable
    o i ℓ : Level

import Algebra.Structures
open module Structures {a} {A : Set a}
  = Algebra.Structures {A = A} _≡_

record Magma
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_∙_ : Op₂ I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ) {q} ⦃ _ : Equivalent q _⇨′_ ⦄
  ⦃ _ : Raw.Category _⇨′_ ⦄ ⦃ _ : Raw.Cartesian _⇨′_ ⦄
  ⦃ _ : Raw.Magma _∙_ M _⇨′_ ⦄ ⦃ _ : IsMagma _∙_ ⦄
    : Set (o ⊔ i ⊔ ℓ ⊔ q) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
  field
   ⟨∙⟩-cong :
      -- {p q r s : I} → (p≡q : p ≡ q) → (r≡s : r ≡ s) →
      -- Raw.sub M (∙-cong p≡q r≡s) ∘ ⟨∙⟩ ≈ ⟨∙⟩ ∘ (Raw.sub M p≡q ⊗ Raw.sub M r≡s)

      {p q r s : I} → {f f′ : M p ⇨ M q} → {g g′ : M r ⇨ M s} →
      f ≈ f′ → g ≈ g′ →
      ⟨∙⟩ ∘ (f ⊗ g) ≈ ⟨∙⟩ ∘ (f′ ⊗ g′)

open Magma ⦃ … ⦄ public

record Semigroup
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_∙_ : Op₂ I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ) {q} ⦃ _ : Equivalent q _⇨′_ ⦄
  ⦃ _ : Raw.Category _⇨′_ ⦄ ⦃ _ : Raw.Cartesian _⇨′_ ⦄
  ⦃ _ : Raw.Semigroup _∙_ M _⇨′_ ⦄ ⦃ _ : IsSemigroup _∙_ ⦄
    : Set (o ⊔ i ⊔ ℓ ⊔ q) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
    open IsSemigroup ⦃ … ⦄
    instance
      is-magma : IsMagma _∙_
      is-magma = isMagma
  field
    ⦃ magma ⦄ : Magma _∙_ M _⇨_
    ⟨∙⟩-assoc :
      ∀ {p q r : I} →
      sub M (assoc p q r) ∘ ⟨∙⟩ ∘ first ⟨∙⟩ ≈ ⟨∙⟩ ∘ second ⟨∙⟩ ∘ assocʳ
      -- ⟨∙⟩ ∘ ((⟨∙⟩ ∘ (f ⊗ g)) ⊗ h) ∘ Raw.assocˡ ≈  {!!} ∘ (⟨∙⟩ ∘ (f ⊗ (⟨∙⟩ ∘ (g ⊗ h))))

open Semigroup ⦃ … ⦄ public

record Monoid
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_∙_ : Op₂ I) (ι : I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ) {q} ⦃ _ : Equivalent q _⇨′_ ⦄
  ⦃ _ : Raw.Category _⇨′_ ⦄ ⦃ _ : Raw.Cartesian _⇨′_ ⦄
  ⦃ _ : Raw.Monoid _∙_ ι M _⇨′_ ⦄ ⦃ _ : IsMonoid _∙_ ι ⦄
    : Set (o ⊔ i ⊔ ℓ ⊔ q) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
    open IsMonoid ⦃ … ⦄
      renaming (identityˡ to idˡ; identityʳ to idʳ)
    -- needed this to bring it into scope, didn't work when passed
    -- directly as Semigroup argument.  Solution: instance argements
    -- go *after* ordinary arguments but I kind of like instance
    -- fields more, plus it won't complain when opening a record after
    -- fields declarations.
    instance
      is-semigroup : IsSemigroup _∙_
      is-semigroup = isSemigroup
  field
    ⦃ semigroup ⦄ : Semigroup _∙_ M _⇨′_
    ⟨∙⟩-identityˡ : ∀ {q : I} →
      sub M (idˡ q) ∘ ⟨∙⟩ ∘ first  ⟨ι⟩ ≈ unitorᵉˡ
    ⟨∙⟩-identityʳ : ∀ {q : I} →
      sub M (idʳ q) ∘ ⟨∙⟩ ∘ second ⟨ι⟩ ≈ unitorᵉʳ

open Monoid ⦃ … ⦄ public

record Group
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_∙_ : Op₂ I) (-_ : Op₁ I) (ι : I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ) {q} ⦃ _ : Equivalent q _⇨′_ ⦄
  ⦃ _ : Raw.Category _⇨′_ ⦄ ⦃ _ : Raw.Cartesian _⇨′_ ⦄
  ⦃ _ : Raw.Group _∙_ ι -_ M _⇨′_ ⦄ ⦃ _ : IsGroup _∙_ ι -_ ⦄
    : Set (o ⊔ i ⊔ ℓ ⊔ q) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
    open IsGroup ⦃ … ⦄
      renaming (inverseˡ to invˡ; inverseʳ to invʳ)
    instance
      is-monoid : IsMonoid _∙_ ι
      is-monoid = isMonoid
  field
    ⦃ monoid ⦄ : Monoid _∙_ ι M _⇨_
    inverseˡ : ∀ {p : I} →
      sub M (invˡ p) ∘ ⟨∙⟩ ∘ first  ⟨f⟩ ∘ dup ≈ ⟨ι⟩ ∘ !
    inverseʳ : ∀ {p : I} →
      sub M (invʳ p) ∘ ⟨∙⟩ ∘ second ⟨f⟩ ∘ dup ≈ ⟨ι⟩ ∘ !

open Group ⦃ … ⦄ public

record AbelianGroup
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_∙_ : Op₂ I) (-_ : Op₁ I) (ι : I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ) {q} ⦃ _ : Equivalent q _⇨′_ ⦄
  ⦃ _ : Raw.Category _⇨′_ ⦄ ⦃ _ : Raw.Cartesian _⇨′_ ⦄
  ⦃ _ : Raw.Group _∙_ ι (-_) M _⇨′_ ⦄ ⦃ _ : IsAbelianGroup _∙_ ι -_ ⦄
    : Set (o ⊔ i ⊔ ℓ ⊔ q) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
    open IsAbelianGroup ⦃ … ⦄
    instance
      is-group : IsGroup _∙_ ι (-_)
      is-group = isGroup
  field
    ⦃ group ⦄ : Group _∙_ -_ ι M _⇨_
    ⟨∙⟩-comm : ∀ {p q : I} →
      sub M (comm p q) ∘ ⟨∙⟩ ≈ ⟨∙⟩ ∘ swap

open AbelianGroup ⦃ … ⦄ public

module _
  {O : Set o} ⦃ _ : Products O ⦄
  {_⇨′_ : O → O → Set ℓ}
  ⦃ _ : Raw.Category _⇨′_ ⦄ ⦃ _ : Raw.Cartesian _⇨′_ ⦄
  (let infix 0 _⇨_; _⇨_ = _⇨′_) where

  ×-distribˡ :
    ∀ {p q r : O} → p × (q × r) ⇨ (p × q) × (p × r)
  ×-distribˡ = transpose ∘ first dup

  ×-distribʳ :
    ∀ {p q r : O} → (p × q) × r ⇨ (p × r) × (q × r)
  ×-distribʳ = transpose ∘ second dup

record Ring
  {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} (_+_ _*_ : Op₂ I) (-_ : Op₁ I) (0# 1# : I) (M : I → O)
  (_⇨′_ : O → O → Set ℓ) {q} ⦃ _ : Equivalent q _⇨′_ ⦄
  ⦃ _ : Raw.Category _⇨′_ ⦄ ⦃ _ : Raw.Cartesian _⇨′_ ⦄
  ⦃ _ : Raw.Ring _+_ _*_ -_ 0# 1# M _⇨′_ ⦄
  ⦃ _ : IsRing _+_ _*_ -_ 0# 1# ⦄
    : Set (o ⊔ i ⊔ ℓ ⊔ q) where
  private
    infix 0 _⇨_; _⇨_ = _⇨′_
    open IsRing ⦃ … ⦄
    instance
      *-is-monoid : IsMonoid _*_ 1#
      *-is-monoid = *-isMonoid
      +-is-group : IsAbelianGroup _+_ 0# (-_)
      +-is-group = +-isAbelianGroup
  field
    ⦃ *-monoid ⦄ : Monoid _*_ 1# M _⇨_
    ⦃ +-group  ⦄ : AbelianGroup _+_ -_ 0# M _⇨_
    ⟨*⟩-distribʳ-⟨+⟩ : ∀ {p q r : I} →
      sub M (distribʳ p q r) ∘ ⟨*⟩ ∘ first  ⟨+⟩ ≈ ⟨+⟩ ∘ (⟨*⟩ ⊗ ⟨*⟩) ∘ ×-distribʳ
    ⟨*⟩-distribˡ-⟨+⟩ : ∀ {p q r : I} →
      sub M (distribˡ p q r) ∘ ⟨*⟩ ∘ second ⟨+⟩ ≈ ⟨+⟩ ∘ (⟨*⟩ ⊗ ⟨*⟩) ∘ ×-distribˡ

open Ring ⦃ … ⦄ public

LawfulMagmaᶠ :
  ∀ {O : Set o} ⦃ _ : Products O ⦄
  {I : Set i} {_∙_ : Op₂ I} (M : I → O)
  {_⇨_ : O → O → Set ℓ} {q} ⦃ _ : Equivalent q _⇨_ ⦄
  ⦃ _ : Raw.Category _⇨_ ⦄ ⦃ _ : Raw.Cartesian _⇨_ ⦄ ⦃ _ : Raw.Magma _∙_ M _⇨_ ⦄
  ⦃ _ : Laws.Category _⇨_ ⦄ ⦃ _ : Laws.Cartesian _⇨_ ⦄ ⦃ _ : IsMagma _∙_ ⦄ →
  Magma _∙_ M _⇨_
LawfulMagmaᶠ M = record
  { ⟨∙⟩-cong = λ f≈f′ g≈g′ → ∘≈ refl (⊗≈ f≈f′ g≈g′) }
