{-# OPTIONS --safe --without-K #-}

open import Level
  using (_⊔_; 0ℓ; Level; Lift; lift)

module Felix.Algebra.Instances.Function.Laws (ℓ : Level) where

-- standard-library
open import Data.Integer
  as ℤ using ()
open import Data.Integer.Properties
  as ℤₚ using ()
open import Data.Nat
  as ℕ using ()
open import Data.Nat.Properties
  as ℕₚ using ()
open import Data.Product
  using (_,_)
open import Function
  using (_∘′_; const)
open import Relation.Binary.PropositionalEquality
  using (module ≡-Reasoning; _≗_; cong₂; isEquivalence; refl)

-- felix
open import Felix.Raw
  using (_∘_; _×_; ⊤; assocʳ; first; id; second; sub)
open import Felix.Equiv
  using (_≈_; module ≈-Reasoning)

-- felix-algebra
open import Felix.Algebra.Laws
  as Laws
-- open import Felix.Algebra.Instances.Function.Raw ℓ public

private
  variable
    A : Set

module natural-laws-instances-0ℓ where
  open ℕ using (_+_; _*_)

  open import Felix.Instances.Function 0ℓ
    as F0ℓ
    renaming (_⇾_ to _0ℓ⇾_)
  open import Felix.Instances.Function 0ℓ
    as Fun
  open import Felix.Algebra.Instances.Function.Raw 0ℓ
    as R0ℓ

  private
    instance
      +-isMagma′ = ℕₚ.+-isMagma
      *-isMagma′ = ℕₚ.*-isMagma
      +-isSemigroup′ = ℕₚ.+-isSemigroup
      *-isSemigroup′ = ℕₚ.*-isSemigroup

  instance
    +-magma : Magma _+_ (const ℕ) _0ℓ⇾_
    +-magma = LawfulMagmaᶠ (const ℕ)

    *-magma : Magma _*_ (const ℕ) _⇾_
    *-magma = LawfulMagmaᶠ (const ℕ)

    +-semigroup : Semigroup _+_ (const ℕ) _⇾_
    +-semigroup = record
      { ⟨∙⟩-assoc = λ { ((lift p′ , lift q′) , lift r′) → {!assoc p′ q′ r′!} }
      -- λ { {p} {q} {r} →
      --     begin
      --       sub (const ℕ) (assoc p q r) ∘′
      --       lift₂ _+_ ∘′
      --       first (lift₂ _+_)
      --     ≡⟨⟩
      --       id ∘′ lift₂ _+_ ∘′ first (lift₂ _+_)
      --     ≡⟨ {!assoc p q r !} ⟩
      --       lift₂ _+_ ∘′ second (lift₂ _+_) ∘′ assocʳ
      --     ∎
      --     }
      }
      where
        open Structures.IsSemigroup +-isSemigroup′
      --   open ≈-Reasoning
      --   assoc′ : {p q r : ℕ.ℕ} →
      --     sub (const ℕ) (assoc p q r) ∘ lift₂ _+_ ∘ first (lift₂ _+_) ≈
      --     lift₂ _+_ ∘ second (lift₂ _+_) ∘ assocʳ
      --   assoc′ {p} {q} {r} a = assoc (lift p) (lift q) (lift r)

    -- *-semigroup : Semigroup _*_ (const ℕ) _⇾_
    -- *-semigroup = record
    --   { ⟨∙⟩-assoc = {!!} }
