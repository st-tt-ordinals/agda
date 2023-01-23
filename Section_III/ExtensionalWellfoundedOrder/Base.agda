----------------------------------------------------------------------------------------------------
-- Definition of Extensional Wellfounded orders and their basic properties
----------------------------------------------------------------------------------------------------

-- See Martin Escardo's https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.html
-- for a much more extensive formalisation

{-# OPTIONS --cubical --safe #-}

module ExtensionalWellfoundedOrder.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open BinaryRelation renaming (isTrans to isTransitive)
open import Cubical.Induction.WellFounded
  renaming (WellFounded to isWellFounded)

open import General-Properties

record Ord : Type₁ where
  constructor  _,,_,,_,,_,,_,,_
  field
    Carrier : Type
    _≺_ : Carrier -> Carrier -> Type
    truncated   : isPropValued _≺_
    wellfounded : isWellFounded _≺_
    extensional : isExtensional _≺_
    transitive  : isTransitive _≺_

isSetCarrier : (A : Ord) → isSet (Ord.Carrier A)
isSetCarrier A = Collapsible≡→isSet λ x y → (f , f-wconst) where
  open Ord A
  f : ∀ {x y} → x ≡ y → x ≡ y
  f {x} {y} p = extensional x y λ c → subst (c ≺_) p , subst (c ≺_) (sym p)

  f-wconst : ∀ {x y} → (p q : x ≡ y) → f p ≡ f q
  f-wconst {x} {y} p q = cong (extensional x y)
                              (funExt (λ c → ΣPathP ((funExt λ r → truncated _ _ _ _) ,
                                                     (funExt λ r → truncated _ _ _ _))))

{- Order between ordinals -}

record isSimulation {A B : Ord} (f : Ord.Carrier A → Ord.Carrier B) : Type where
  module A = Ord A
  module B = Ord B
  field
    monotone : ∀ {a a'} → a A.≺ a' → f a B.≺ f a'
    simulation : ∀ {b a} → b B.≺ f a → Σ[ a' ∈ A.Carrier ] (a' A.≺ a × (f a' ≡ b))

record _≤_ (A B : Ord) : Type where
  field
    f : Ord.Carrier A → Ord.Carrier B
    f-simulation : isSimulation {A} {B} f

  open isSimulation f-simulation public

module _ (A : Ord) where

  open Ord A

  initial-segment : Carrier → Ord
  Carrier (initial-segment a) = Σ[ y ∈ Carrier ] (y ≺ a)
  _≺_ (initial-segment a) (y , y<a) (y' , y'<a) = y ≺ y'
  truncated (initial-segment a) x y = truncated _ _
  wellfounded (initial-segment a) (y , y<a) = helper y y<a (wellfounded y ) where
    helper : ∀ y y<a → Acc _≺_ y → Acc (Ord._≺_ (initial-segment a) ) (y , y<a)
    helper y y<a (acc p) = acc λ { (z , z<a) z<y → helper z z<a (p z z<y) }
  extensional (initial-segment a) (x , x<a) (y , y<a) ext =
    Σ≡Prop {B = λ y → y ≺ a} (λ x → truncated x a)
           (extensional x y λ c → (λ c<x → fst (ext (c , transitive c x a c<x x<a)) c<x) ,
                                  (λ c<y → snd (ext (c , transitive c y a c<y y<a)) c<y))
  transitive (initial-segment a) (x , _) (y , _) (z , _) x<y y<z = transitive x y z x<y y<z

record _<_ (A B : Ord) : Type where
  module A = Ord A
  module B = Ord B
  field
    sim : A ≤ B
    bound : B.Carrier
    bounded : (a : A.Carrier) → _≤_.f sim a B.≺ bound

  f' : A.Carrier → Ord.Carrier (initial-segment B bound)
  f' a = _≤_.f sim a , bounded a

  field
    equiv : isEquiv f'
