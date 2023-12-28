{-# OPTIONS --safe --without-K #-}

open import Level
  using (_⊔_; 0ℓ; Level)

module Felix.Algebra.Instances.Function.Laws where

-- standard-library
open import Algebra.Structures
  as Structures using ()
open import Data.Integer
  as ℤ using ()
open import Data.Integer.Properties
  as ℤₚ using ()
open import Data.Nat
  as ℕ using ()
open import Data.Nat.Properties
  as ℕₚ using ()
open import Data.Rational
  as ℚ using ()
open import Data.Rational.Properties
  as ℚₚ using ()
open import Data.Product
  using (_,_)

-- felix
open import Felix.Instances.Function 0ℓ
  as Fun
  using (_⇾_)
open import Felix.Raw
  using (_∘_; ⊤; assocʳ; first; id; second; sub)

-- felix-algebra
open import Felix.Algebra.Laws
  as Laws
open import Felix.Algebra.Instances.Function.Raw
  as Raw using ()

module natural-instances where
  module raw-instances = Raw.natural-instances

  instance
    +-semigroup : Semigroup _⇾_
    +-semigroup = record
      { raw-magma = raw-instances.+-magma
      ; ⟨∙⟩-assoc = λ ((a , b) , c) → ℕassoc a b c
      } where ℕassoc = Structures.IsSemigroup.assoc ℕₚ.+-isSemigroup

    *-semigroup : Semigroup _⇾_
    *-semigroup = record
      { raw-magma = raw-instances.*-magma
      ; ⟨∙⟩-assoc = λ ((a , b) , c) → ℕassoc a b c
      } where ℕassoc = Structures.IsSemigroup.assoc ℕₚ.*-isSemigroup

module integer-instances where
  module raw-instances = Raw.integer-instances

  instance
    +-semigroup : Semigroup _⇾_
    +-semigroup = record
      { raw-magma = raw-instances.+-magma
      ; ⟨∙⟩-assoc = λ ((a , b) , c) → ℕassoc a b c
      } where ℕassoc = Structures.IsSemigroup.assoc ℤₚ.+-isSemigroup

    *-semigroup : Semigroup _⇾_
    *-semigroup = record
      { raw-magma = raw-instances.*-magma
      ; ⟨∙⟩-assoc = λ ((a , b) , c) → ℕassoc a b c
      } where ℕassoc = Structures.IsSemigroup.assoc ℤₚ.*-isSemigroup

module rational-instances where
  module raw-instances = Raw.rational-instances

  instance
    +-semigroup : Semigroup _⇾_
    +-semigroup = record
      { raw-magma = raw-instances.+-magma
      ; ⟨∙⟩-assoc = λ ((a , b) , c) → ℕassoc a b c
      } where ℕassoc = Structures.IsSemigroup.assoc ℚₚ.+-isSemigroup

    *-semigroup : Semigroup _⇾_
    *-semigroup = record
      { raw-magma = raw-instances.*-magma
      ; ⟨∙⟩-assoc = λ ((a , b) , c) → ℕassoc a b c
      } where ℕassoc = Structures.IsSemigroup.assoc ℚₚ.*-isSemigroup
