{-# OPTIONS --safe --without-K #-}

open import Felix.Equiv
  using (Equivalent)
open import Felix.Homomorphism
  using ( Homomorphismₒ; Homomorphism
        ; CategoryH; CartesianH; ProductsH; StrongProductsH
        ; _;_; sym
        )
open import Felix.Laws
  as Laws
  hiding (Category; Cartesian)
open import Felix.Raw
  using (Category; Cartesian; Products; _∘_; _×_)
open import Felix.Reasoning

-- per wiki I use names source and target (subscript ₛ and ₜ) for functors
-- (homomorphisms here) instead of ₁ and ₂ respectively.
-- I wonder if it would make sense to use those for categories?
module Felix.Algebra.Comma
   {o₀} {O₀ : Set o₀} {ℓ₀} (_⇨₀_ : O₀ → O₀ → Set ℓ₀) ⦃ _ : Category _⇨₀_ ⦄
   {o₁} {O₁ : Set o₁} {ℓ₁} (_⇨₁_ : O₁ → O₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄
   {o₂} {O₂ : Set o₂} {ℓ₂} (_⇨₂_ : O₂ → O₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄
   {q₀} ⦃ _ : Equivalent q₀ _⇨₀_ ⦄ ⦃ _ : Laws.Category _⇨₀_ ⦄
   {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ -- ⦃ _ : Laws.Category _⇨₁_ ⦄
   {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄ -- ⦃ _ : Laws.Category _⇨₂_ ⦄
   ⦃ Hₒₛ : Homomorphismₒ O₁ O₀ ⦄ ⦃ Hₛ : Homomorphism _⇨₁_ _⇨₀_ ⦄
     ⦃ categoryHₛ : CategoryH _⇨₁_ _⇨₀_ ⦄
   ⦃ Hₒₜ : Homomorphismₒ O₂ O₀ ⦄ ⦃ Hₜ : Homomorphism _⇨₂_ _⇨₀_ ⦄
     ⦃ categoryHₜ : CategoryH _⇨₂_ _⇨₀_ ⦄
     where

-- felix
open import Felix.Construct.Comma.Raw _⇨₀_ _⇨₁_ _⇨₂_

-- felix-algebra
open import Felix.Algebra.Raw
  using (Operand; 𝕆; Magma; ⟨∙⟩)
open import Felix.Algebra.Homomorphism
  using ( OperandH; StrongOperandH; MagmaH
        ; β; β⁻¹; F-⟨∙⟩; F-⟨∙⟩′
        ; β⁻¹∘β
        )

module operands
  ⦃ productsₛ : Products O₁ ⦄ ⦃ productsₜ : Products O₂ ⦄ ⦃ products₀ : Products O₀ ⦄
  ⦃ pHₛ : ProductsH O₁ _⇨₀_ ⦄ ⦃ pHₜ : ProductsH O₂ _⇨₀_ ⦄
  ⦃ spHₛ : StrongProductsH O₁ _⇨₀_ ⦄ ⦃ spHₜ : StrongProductsH O₂ _⇨₀_ ⦄
  ⦃ opₛ : Operand O₁ ⦄ ⦃ opₜ : Operand O₂ ⦄ ⦃ op : Operand O₀ ⦄
  ⦃ opHₛ : OperandH O₁ _⇨₀_ ⦄ ⦃ opHₜ : OperandH O₂ _⇨₀_ ⦄
  where instance

    operand : Operand Obj
    -- β   : 𝕆₀ ⇨₀ Fₒ Hₒ₂ 𝕆₂
    -- β⁻¹ : Fₒ Hₒ₁ 𝕆₁ ⇨₀ 𝕆₀
    operand = record { 𝕆 = mkᵒ (β ∘ β⁻¹) }

    open Obj

    module magma
      ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄ ⦃ _ : Cartesian _⇨₀_ ⦄
      ⦃ _ : StrongOperandH O₁ _⇨₀_ ⦄ -- ⦃ _ : OperandH O₂ _⇨₀_ ⦄
      ⦃ _ : Laws.Cartesian _⇨₀_ ⦄
      ⦃ cartesianHₛ : CartesianH _⇨₁_ _⇨₀_ ⦄ ⦃ cartesianHₜ : CartesianH _⇨₂_ _⇨₀_ ⦄
      ⦃ magmaₛ : Magma _⇨₁_ ⦄ ⦃ magmaₜ : Magma _⇨₂_ ⦄ ⦃ magma₀ : Magma _⇨₀_ ⦄
      ⦃ magmaHₛ : MagmaH _⇨₁_ _⇨₀_ ⦄ ⦃ magmaHₜ : MagmaH _⇨₂_ _⇨₀_ ⦄
      where
        ⟨∙⟩′ : 𝕆 × 𝕆 ↬ 𝕆
        ⟨∙⟩′ = mkᵐ ⟨∙⟩ ⟨∙⟩
          ( ∘≈ʳ F-⟨∙⟩′
          ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
          ; ∘-assocˡ′ (sym F-⟨∙⟩)
          ; ∘-assocʳ′ ∘-assocʳ
          ; ∘≈ʳ² (∘-assocˡ′ ⊗∘⊗)
          )

        instance
          magma : Magma _↬_
          magma = record { ⟨∙⟩ = ⟨∙⟩′ }
