{-# OPTIONS --safe --without-K #-}

module Felix.Algebra.Homomorphism where

-- standard-library
open import Level
  using (_⊔_; Level)

-- felix
open import Felix.Homomorphism
  using ( Equivalent
        ; _;_ ; sym
        ; Homomorphismₒ; Homomorphism
        ; ProductsH; StrongProductsH
        ; Fₒ; Fₘ; _≈_; μ; μ⁻¹; μ∘μ⁻¹
        ; id-Hₒ; id-H; id-ProductsH
        )
open import Felix.Raw
  using ( Category; Cartesian; Products
        ; id; _∘_; _⊗_
        )
open import Felix.Reasoning
open import Felix.Laws
  as Laws
  hiding (Category; Cartesian)

-- felix-algebra
open import Felix.Algebra.Raw
  as Raw
  using (Operand; 𝕆; ⟨∙⟩; Magma)

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ j : Level

record OperandH
  (O₁ : Set o₁) ⦃ _ : Operand O₁ ⦄
  {O₂ : Set o₂} ⦃ _ : Operand O₂ ⦄
  (_⇨₂′_ : O₂ → O₂ → Set ℓ₂)
  ⦃ Hₒ : Homomorphismₒ O₁ O₂ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private
    infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β   : 𝕆 ⇨₂ Fₒ 𝕆
    β⁻¹ : Fₒ 𝕆 ⇨₂ 𝕆

open OperandH ⦃ … ⦄ public

id-OperandH :
  ∀ {O : Set o} ⦃ _ : Operand O ⦄
  {_⇨_ : O → O → Set ℓ} ⦃ _ : Category _⇨_ ⦄ →
  OperandH O _⇨_ ⦃ Hₒ = id-Hₒ ⦄
id-OperandH = record { β = id; β⁻¹ = id}

record StrongOperandH
  (O₁ : Set o₁) ⦃ _ : Operand O₁ ⦄
  {O₂ : Set o₂} ⦃ _ : Operand O₂ ⦄
  (_⇨₂′_ : O₂ → O₂ → Set ℓ₂) ⦃ _ : Category _⇨₂′_ ⦄
  {q} ⦃ _ : Equivalent q _⇨₂′_ ⦄
  ⦃ Hₒ : Homomorphismₒ O₁ O₂ ⦄
  ⦃ opH : OperandH O₁ _⇨₂′_ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private
    infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β⁻¹∘β : β⁻¹ ∘ β ≈ id
    β∘β⁻¹ : β ∘ β⁻¹ ≈ id

open StrongOperandH ⦃ … ⦄ public

record MagmaH
  {O₁ : Set o₁} (_⇨₁_ : O₁ → O₁ → Set ℓ₁)
  {O₂ : Set o₂} (_⇨₂_ : O₂ → O₂ → Set ℓ₂)
  ⦃ _ : Operand O₁ ⦄ ⦃ _ : Products O₁ ⦄
  ⦃ _ : Operand O₂ ⦄ ⦃ _ : Products O₂ ⦄
  {q} ⦃ _ : Equivalent q _⇨₂_ ⦄
  ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ magma₁ : Magma _⇨₁_ ⦄
  ⦃ _ : Category _⇨₂_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄ ⦃ magma₂ : Magma _⇨₂_ ⦄
  ⦃ Hₒ : Homomorphismₒ O₁ O₂ ⦄
  ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
  ⦃ pH : ProductsH O₁ _⇨₂_ ⦄
  ⦃ opH : OperandH O₁ _⇨₂_ ⦄
    : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  field
    F-⟨∙⟩ : Fₘ ⟨∙⟩ ∘ μ ∘ (β ⊗ β) ≈ β ∘ ⟨∙⟩

  module _
    ⦃ _ : Laws.Category _⇨₂_ ⦄
    ⦃ _ : Laws.Cartesian _⇨₂_ ⦄
    ⦃ spH : StrongProductsH O₁ _⇨₂_ ⦄
    ⦃ _ : StrongOperandH O₁ _⇨₂_ ⦄ where

    F-⟨∙⟩′ : Fₘ ⟨∙⟩ ≈ β ∘ ⟨∙⟩ ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    F-⟨∙⟩′ = sym (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ β∘β⁻¹)))
            ; ∘≈ˡ F-⟨∙⟩ ; ∘-assocʳ

open MagmaH ⦃ … ⦄ public

id-MagmaH :
  {O : Set o} {_⇨_ : O → O → Set ℓ}
  ⦃ _ : Operand O ⦄ ⦃ _ : Products O ⦄
  {q : Level} ⦃ _ : Equivalent q _⇨_ ⦄
  ⦃ _ : Category _⇨_ ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Magma _⇨_ ⦄
  ⦃ _ : Laws.Category _⇨_ ⦄ ⦃ _ : Laws.Cartesian _⇨_ ⦄ →
  MagmaH _⇨_ _⇨_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ H = id-H ⦄ ⦃ pH = id-ProductsH ⦄ ⦃ opH = id-OperandH ⦄
id-MagmaH = record
  { F-⟨∙⟩ = elimʳ (identityˡ ; id⊗id) ; sym identityˡ }
