----------------------------------------------------------------------------------------------------
-- The "if-and-only-if" relation
----------------------------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module RelationIff where

open import MLTT.Universes
open import MLTT.Sigma using (_×_)

_↔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A ↔ B = (A → B) × (B → A)

infix   2 _↔_

