{-# OPTIONS --safe --without-K #-}

open import Level
  using (0ℓ)

module Felix.Algebra.Instances.Function.Raw where

-- standard-library
open import Data.Integer
  as ℤ using ()
open import Data.Nat
  as ℕ using ()
open import Data.Rational
  as ℚ using ()
open import Data.Product
  using (uncurry′)

-- felix
open import Felix.Instances.Function 0ℓ
  as Fun
  using (_⇾_)

-- felix-algebra
open import Felix.Algebra.Raw
  using (Operand; 𝕆; Magma; ⟨∙⟩)

module natural-instances where instance
  open ℕ using (ℕ; _+_; _*_)

  operand : Operand Set
  operand = record { 𝕆 = ℕ }

  +-magma : Magma _⇾_
  +-magma = record { ⟨∙⟩ = uncurry′ _+_ }

  *-magma : Magma _⇾_
  *-magma = record { ⟨∙⟩ = uncurry′ _*_ }

module integer-instances where instance
  open ℤ using (ℤ; _+_; _*_)

  operand : Operand Set
  operand = record { 𝕆 = ℤ }

  +-magma : Magma _⇾_
  +-magma = record { ⟨∙⟩ = uncurry′ _+_ }

  *-magma : Magma _⇾_
  *-magma = record { ⟨∙⟩ = uncurry′ _*_ }

module rational-instances where instance
  open ℚ using (ℚ; _+_; _*_)

  operand : Operand Set
  operand = record { 𝕆 = ℚ }

  +-magma : Magma _⇾_
  +-magma = record { ⟨∙⟩ = uncurry′ _+_ }

  *-magma : Magma _⇾_
  *-magma = record { ⟨∙⟩ = uncurry′ _*_ }
