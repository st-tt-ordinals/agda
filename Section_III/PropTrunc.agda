{-
We define our own version of the propositional truncation so that we
can use --erased-cubical with it for our benchmarks. In a
non-`erased-cubical` setting, it is exactly like the library
definition.
-}


{-# OPTIONS --erased-cubical --safe #-}
module PropTrunc where

open import Cubical.Core.Primitives

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

data ∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥
  squash : ∀ (x y : ∥ A ∥) → x ≡ y

∥-∥rec : {P : Type ℓ} → ((x y : P) → (x ≡ y)) → (A → P) → ∥ A ∥ → P
∥-∥rec Pprop f ∣ x ∣ = f x
∥-∥rec Pprop f (squash x y i) = Pprop (∥-∥rec Pprop f x) (∥-∥rec Pprop f y) i

isPropPropTrunc : (x y : ∥ A ∥) → x ≡ y
isPropPropTrunc x y = squash x y

∥-∥map : {A : Type ℓ}{B : Type ℓ'} → (A → B) → ∥ A ∥ → ∥ B ∥
∥-∥map f = ∥-∥rec isPropPropTrunc (λ a → ∣ f a ∣)


import Cubical.HITs.PropositionalTruncation.Base as Lib

fromLib∥-∥ : Lib.∥ A ∥₁ → ∥ A ∥
fromLib∥-∥ Lib.∣ x ∣₁ = ∣ x ∣
fromLib∥-∥ (Lib.squash₁ x y i) = squash (fromLib∥-∥ x) (fromLib∥-∥ y) i
