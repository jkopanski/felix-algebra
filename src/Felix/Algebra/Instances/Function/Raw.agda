{-# OPTIONS --safe --without-K #-}

open import Level
  using (_⊔_; Level; Lift; lift)

module Felix.Algebra.Instances.Function.Raw (ℓ : Level) where

-- standard-library
open import Data.Integer
  as ℤ using ()
open import Data.Nat
  as ℕ using ()
open import Data.Rational
  as ℚ using ()
open import Data.Product
  using (_,_)
open import Function
  using (const)

-- felix
open import Felix.Instances.Function ℓ
  as Fun
open import Felix.Raw
  using (_∘_; _×_; ⊤; uncurry)

-- felix-algebra
open import Felix.Algebra.Raw
  as Raw
  hiding (*-monoid)

private
  variable
    A : Set

-- until it is available from felix, see
-- https://github.com/conal/felix/pull/5
lift₀ : A → (⊤ ⇾ Lift ℓ A)
lift₀ n tt = lift n

lift₁ : (A → A) → (Lift ℓ A ⇾ Lift ℓ A)
lift₁ f (lift a) = lift (f a)

lift₂′ : (A → A → A) → (Lift ℓ A ⇾ Lift ℓ A ⇾ Lift ℓ A)
lift₂′ f (lift a) (lift b) = lift (f a b)

lift₂ : (A → A → A) → (Lift ℓ A × Lift ℓ A ⇾ Lift ℓ A)
lift₂ = uncurry Function.∘ lift₂′

ℕ : Set ℓ
ℕ = Lift ℓ ℕ.ℕ

ℤ : Set ℓ
ℤ = Lift ℓ ℤ.ℤ

ℚ : Set ℓ
ℚ = Lift ℓ ℚ.ℚ

module natural-raw-instances where instance
  open ℕ using (_+_; _*_)

  +-magma : Magma _+_ (const ℕ) _⇾_
  +-magma = record { ⟨∙⟩ = lift₂ _+_ }

  *-magma : Magma _*_ (const ℕ) _⇾_
  *-magma = record { ⟨∙⟩ = lift₂ _*_ }

  +-semigroup : Semigroup _+_ (const ℕ) _⇾_
  +-semigroup = record { }

  *-semigroup : Semigroup _*_ (const ℕ) _⇾_
  *-semigroup = record { }

  +-unit : Element 0 (const ℕ) _⇾_
  +-unit = record { ⟨ι⟩ = lift₀ 0 }

  *-unit : Element 1 (const ℕ) _⇾_
  *-unit = record { ⟨ι⟩ = lift₀ 1 }

  +-0-monoid : Monoid _+_ 0 (const ℕ) _⇾_
  +-0-monoid = record { }

  *-1-monoid : Monoid _*_ 1 (const ℕ) _⇾_
  *-1-monoid = record { }

module integer-raw-instances where instance
  open ℤ using (0ℤ; 1ℤ; _+_; _*_; -_)

  +-magma : Magma _+_ (const ℤ) _⇾_
  +-magma = record { ⟨∙⟩ = lift₂ _+_ }

  *-magma : Magma _*_ (const ℤ) _⇾_
  *-magma = record { ⟨∙⟩ = lift₂ _*_ }

  +-semigroup : Semigroup _+_ (const ℤ) _⇾_
  +-semigroup = record { }

  *-semigroup : Semigroup _*_ (const ℤ) _⇾_
  *-semigroup = record { }

  +-unit : Element 0ℤ (const ℤ) _⇾_
  +-unit = record { ⟨ι⟩ = lift₀ 0ℤ }

  *-unit : Element 1ℤ (const ℤ) _⇾_
  *-unit = record { ⟨ι⟩ = lift₀ 1ℤ }

  +-0-monoid : Monoid _+_ 0ℤ (const ℤ) _⇾_
  +-0-monoid = record { }

  *-1-monoid : Monoid _*_ 1ℤ (const ℤ) _⇾_
  *-1-monoid = record { }

  +-inverse : Unary (-_) (const ℤ) _⇾_
  +-inverse = record { ⟨f⟩ = lift₁ (-_) }

  +-0-group : Group _+_ 0ℤ (-_) (const ℤ) _⇾_
  +-0-group = record { }

  +-*-ring : Ring _+_ _*_ (-_) 0ℤ 1ℤ (const ℤ) _⇾_
  +-*-ring = record { }

module rational-raw-instances where instance
  open ℚ using (0ℚ; 1ℚ; _+_; _*_; -_)

  +-magma : Magma _+_ (const ℚ) _⇾_
  +-magma = record { ⟨∙⟩ = lift₂ _+_ }

  *-magma : Magma _*_ (const ℚ) _⇾_
  *-magma = record { ⟨∙⟩ = lift₂ _*_ }

  +-semigroup : Semigroup _+_ (const ℚ) _⇾_
  +-semigroup = record { }

  *-semigroup : Semigroup _*_ (const ℚ) _⇾_
  *-semigroup = record { }

  +-unit : Element 0ℚ (const ℚ) _⇾_
  +-unit = record { ⟨ι⟩ = lift₀ 0ℚ }

  *-unit : Element 1ℚ (const ℚ) _⇾_
  *-unit = record { ⟨ι⟩ = lift₀ 1ℚ }

  +-0-monoid : Monoid _+_ 0ℚ (const ℚ) _⇾_
  +-0-monoid = record { }

  *-1-monoid : Monoid _*_ 1ℚ (const ℚ) _⇾_
  *-1-monoid = record { }

  +-inverse : Unary (-_) (const ℚ) _⇾_
  +-inverse = record { ⟨f⟩ = lift₁ (-_) }

  +-0-group : Group _+_ 0ℚ (-_) (const ℚ) _⇾_
  +-0-group = record { }

  +-*-ring : Ring _+_ _*_ (-_) 0ℚ 1ℚ (const ℚ) _⇾_
  +-*-ring = record { }
