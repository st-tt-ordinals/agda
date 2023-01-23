----------------------------------------------------------------------------------------------------
-- The "if-and-only-if" relation
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Iff where

open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

_↔_ : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) → Type _
A ↔ B = (A → B) × (B → A)

infix   2 _↔_

_↔⟨_⟩_ : ∀ {ℓ₁ ℓ₂ ℓ₃} (A : Type ℓ₁) {B : Type ℓ₂} {C : Type ℓ₃}
         → (A ↔ B) → (B ↔ C) → (A ↔ C)
A ↔⟨ A↔B ⟩ B↔C = (fst B↔C ∘ fst A↔B) , (snd A↔B ∘ snd B↔C)

_↔∎ : ∀ {ℓ} (A : Type ℓ) → A ↔ A
_ ↔∎ = (λ a → a) , (λ a → a)

infixr  0 _↔⟨_⟩_
infix   1 _↔∎


