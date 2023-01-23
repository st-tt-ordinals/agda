----------------------------------------------------------------------------------------------------
-- Index of the Agda Development of the paper
--
--     Set-Theoretic and Type-Theoretic Ordinals Coincide
--
----------------------------------------------------------------------------------------------------

{- §II ORDINALS IN TYPE THEORY AND SET THEORY -}

-- These files are tested with
--
--  ● Agda version 2.6.2.2 and
--
--  ● TypeTopology (commit: 318d913c878c1f3cbcfd03c911ed6c1461bf1d9f)

{-# OPTIONS --safe #-}

open import MLTT.Spartan

open import UF.PropTrunc
open import UF.Univalence
open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient hiding (is-prop-valued)
open import UF.UA-FunExt

open import RelationIff

module _ (pt : propositional-truncations-exist)
         (ua : Univalence)
         (𝓤 : Universe)
         (sq : set-quotients-exist)
 where

open import UF.ImageAndSurjection pt

open PropositionalTruncation pt

private
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' _ _ = fe

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open import CumulativeHierarchy pt fe pe
open import CumulativeHierarchy-LocallySmall pt fe pe
open import OrdinalCumulativeHierarchy pt ua 𝓤
open import OrdinalCumulativeHierarchy-Addendum pt ua 𝓤

open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.WellOrderTransport fe'
open import Ordinals.Underlying
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Arithmetic fe'
open import Ordinals.Arithmetic-Properties ua

module _ (ch : cumulative-hierarchy-exists 𝓤)
 where

 open cumulative-hierarchy-exists ch
 open 𝕍-is-locally-small ch
 open ordinal-of-set-theoretic-ordinals ch
 open total-space-of-an-element-of-𝕍
 open Ψ-construction sq
 open 𝕍-set-carrier-quotient ch sq
 open small-quotient-as-ordinal
 open quotient-as-ordinal
 open suprema pt (set-replacement-from-set-quotients sq pt)


 {- A. Ordinals in homotopy type theory -}

 -- Accessibility
 Definition-1 : {X : 𝓤 ̇} (_<_ : X → X → 𝓥 ̇) → X → 𝓤 ⊔ 𝓥 ̇
 Definition-1 = is-accessible

 Lemma-2-→ : {X : 𝓤 ̇} (_<_ : X → X → 𝓥 ̇)
           → (∀ x → is-accessible _<_ x)
           → ∀ {𝓦} (P : X → 𝓦 ̇) → (∀ x → (∀ y → y < x → P y) → P x) → ∀ x → P x
 Lemma-2-→ = transfinite-induction
 --
 Lemma-2-← : {X : 𝓤 ̇} (_<_ : X → X → 𝓥 ̇)
           → (∀ {𝓦} (P : X → 𝓦 ̇) → (∀ x → (∀ y → y < x → P y) → P x) → ∀ x → P x)
           → ∀ x → is-accessible _<_ x
 Lemma-2-← _<_ ti = ti (is-accessible _<_) (λ _ → step)

 -- Type-theoretic ordinal
 Definition-3 : ({X : 𝓤 ̇} (_<_ : X → X → 𝓥 ̇) → (𝓤 ⊔ 𝓥 ̇))
              × ({X : 𝓤 ̇} (_<_ : X → X → 𝓥 ̇) → (𝓤 ⊔ 𝓥 ̇))
              × ({X : 𝓤 ̇} (_<_ : X → X → 𝓥 ̇) → (𝓤 ⊔ 𝓥 ̇))
              × ({X : 𝓤 ̇} (_<_ : X → X → 𝓥 ̇) → (𝓤 ⊔ 𝓥 ̇))
              × (𝓤 ⁺ ̇)
 Definition-3 = is-prop-valued
              , is-well-founded
              , is-extensional
              , is-transitive
              , Ordinal _

 Remark-4 : (α : Ordinal 𝓤) → is-set ⟨ α ⟩
 Remark-4 = underlying-type-is-set fe'

 -- Initial segment and bounded simulation
 -- The bounded simulation relation ⊲ is named < in the paper.
 Definition-5 : ((α : Ordinal 𝓤) → ⟨ α ⟩ → Ordinal 𝓤)
              × (Ordinal 𝓤 → Ordinal 𝓤 → 𝓤 ⁺ ̇)
 Definition-5 = _↓_
              , _⊲_

 -- ⊲⁻ is the small version of ⊲
 Remark-6 : (α β : Ordinal 𝓤) → (α ⊲ β) ≃ (α ⊲⁻ β)
 Remark-6 = ⊲-is-equivalent-to-⊲⁻

 -- The ordinal OO of ordinals is named Ord in the paper.
 Theorem-7 : is-well-order (_⊲_ {𝓤}) × (Ordinal (𝓤 ⁺))
 Theorem-7 = ⊲-is-well-order , OO _

 -- Simulation
 -- The simulation relation ⊴ is named ≤ in the paper.
 Definition-8 : ((α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇)
              × (Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇)
 Definition-8 = is-simulation
              , _⊴_

 Proposition-9 : ((α : Ordinal 𝓤) → α ⊴ α)
               × ((α β : Ordinal 𝓤) → α ⊴ β → β ⊴ α → α ＝ β)
               × ((α : Ordinal 𝓤) (β : Ordinal 𝓥) (γ : Ordinal 𝓦) → α ⊴ β → β ⊴ γ → α ⊴ γ)
               × ((α β : Ordinal 𝓤) → α ⊴ β
                                    → ∀ γ → γ ⊲ α → γ ⊲ β)
               × ({α β : Ordinal 𝓤} → (∀ γ → γ ⊲ α → γ ⊲ β)
                                    → (a : ⟨ α ⟩) → Σ b ꞉ ⟨ β ⟩ , (α ↓ a) ＝ (β ↓ b))
               × ({α β : Ordinal 𝓤} → ((a : ⟨ α ⟩) → Σ b ꞉ ⟨ β ⟩ , (α ↓ a) ＝ (β ↓ b))
                                    → α ⊴ β)
 Proposition-9 = ⊴-refl
               , ⊴-antisym
               , ⊴-trans
               , ⊴-gives-≼
               , from-≼
               , to-⊴ _ _

 Lemma-10 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
          → (is-order-equiv α β f) ↔
            (is-equiv f × is-order-preserving α β f × is-order-reflecting α β f)
 Lemma-10 α β f = (λ p → order-equivs-are-equivs α β p
                       , order-equivs-are-order-preserving α β p
                       , order-equivs-are-order-reflecting α β f p)
                , (λ (x , y , z) → order-preserving-reflecting-equivs-are-order-equivs α β f x y z)

 Lemma-11 : (α : Ordinal 𝓤) (a b : ⟨ α ⟩) (p : b ≺⟨ α ⟩ a)
          → ((α ↓ a ) ↓ (b , p)) ＝ (α ↓ b)
 Lemma-11 = iterated-↓

 -- Sum of type-theoretic ordinals
 Definition-12 : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
 Definition-12 = _+ₒ_

 Lemma-13-i : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
            → (α ↓ a) ＝ ((α +ₒ β) ↓ inl a)
 Lemma-13-i = +ₒ-↓-left
 --
 Lemma-13-ii : (α : Ordinal 𝓤) → (α +ₒ 𝟙ₒ) ↓ inr ⋆ ＝ α
 Lemma-13-ii = +ₒ-𝟙ₒ-↓-right

 -- Supremum of type-theoretic ordinals
 Definition-14 : {I : 𝓤 ̇} (α : I → Ordinal 𝓤) → Ordinal 𝓤
 Definition-14 = sup

 Lemma-15-i : {I : 𝓤 ̇} (α : I → Ordinal 𝓤)
            → (i : I) (x : ⟨ α i ⟩) → sup α ↓ pr₁ (sup-is-upper-bound α i) x ＝ α i ↓ x
 Lemma-15-i = initial-segment-of-sup-at-component
 --
 Lemma-15-ii : {I : 𝓤 ̇} (α : I → Ordinal 𝓤)
             → (y : ⟨ sup α ⟩) → ∥ Σ i ꞉ I , Σ x ꞉ ⟨ α i ⟩ , sup α ↓ y ＝ α i ↓ x ∥
 Lemma-15-ii = initial-segment-of-sup-is-initial-segment-of-some-component

 {- B. Ordinals in set theory -}

 -- (Here, we phrase the definitions and lemmas from set theory in terms of 𝕍 introduced below.)

 -- Transitive set
 Definition-16 : 𝕍 → 𝓤 ⁺ ̇
 Definition-16 = is-transitive-set

 -- Example 17:

 ∅ ⟨∅⟩ ⟨∅,⟨∅⟩⟩ ⟨⟨∅⟩⟩ ⟨∅,⟨∅⟩,⟨⟨∅⟩⟩⟩ : 𝕍
 ∅ = 𝕍-set {𝟘} 𝟘-elim
 ⟨∅⟩ = 𝕍-set {𝟙} (λ _ → ∅)
 ⟨∅,⟨∅⟩⟩ = 𝕍-set {𝟙 {𝓤} + 𝟙 {𝓤}} (cases (λ _ → ∅) (λ _ → ⟨∅⟩))
 ⟨⟨∅⟩⟩ = 𝕍-set {𝟙} λ _ → ⟨∅⟩
 ⟨∅,⟨∅⟩,⟨⟨∅⟩⟩⟩ = 𝕍-set {𝟙 {𝓤} + 𝟙 {𝓤} + 𝟙 {𝓤}} (cases (λ _ → ∅) (cases (λ _ → ⟨∅⟩) λ _ → ⟨⟨∅⟩⟩))

 ¬x∈∅ : {x : 𝕍} → x ∈ ∅ → 𝟘
 ¬x∈∅ x∈∅ = ∥∥-rec 𝟘-is-prop pr₁ (from-∈-of-𝕍-set x∈∅)

 Example-17-i : is-transitive-set ∅
 Example-17-i u v u∈∅ v∈u = 𝟘-elim (¬x∈∅ u∈∅)

 Example-17-ii : is-transitive-set ⟨∅⟩
 Example-17-ii u v u∈⟨∅⟩ v∈u =
   ∥∥-rec ∈-is-prop-valued
         (λ (_ , ∅＝u) → 𝟘-elim (¬x∈∅ (transport (v ∈_) (∅＝u ⁻¹) v∈u)))
         (from-∈-of-𝕍-set u∈⟨∅⟩)

 Example-17-iii : is-transitive-set ⟨∅,⟨∅⟩⟩
 Example-17-iii u v u∈⟨∅,⟨∅⟩⟩ v∈u =
   ∥∥-rec ∈-is-prop-valued
         (λ { (inl _ , ∅＝u) → 𝟘-elim (¬x∈∅ (transport (v ∈_) (∅＝u ⁻¹) v∈u))
            ; (inr _ , ⟨∅⟩＝u) → ∥∥-rec ∈-is-prop-valued
                                       (λ (_ , ∅＝v) → to-∈-of-𝕍-set ∣ inl _ , ∅＝v ∣)
                                       (from-∈-of-𝕍-set (transport (v ∈_) (⟨∅⟩＝u ⁻¹) v∈u))
            })
         (from-∈-of-𝕍-set u∈⟨∅,⟨∅⟩⟩)

 Example-17-iv : is-transitive-set ⟨∅,⟨∅⟩,⟨⟨∅⟩⟩⟩
 Example-17-iv u v u∈⟨∅,⟨⟨∅⟩⟩⟩ v∈u =
   ∥∥-rec ∈-is-prop-valued
         (λ { (inl _ , ∅＝u) → 𝟘-elim (¬x∈∅ (transport (v ∈_) (∅＝u ⁻¹) v∈u))
            ; (inr (inl _) , ⟨∅⟩＝u) → ∥∥-rec ∈-is-prop-valued
                                             (λ (_ , ∅＝v) → to-∈-of-𝕍-set ∣ inl _ , ∅＝v ∣)
                                             (from-∈-of-𝕍-set (transport (v ∈_) (⟨∅⟩＝u ⁻¹) v∈u))
            ; (inr (inr _) , ⟨⟨∅⟩⟩＝u) → ∥∥-rec ∈-is-prop-valued
                                               (λ (_ , ⟨∅⟩＝v) → to-∈-of-𝕍-set ∣ inr (inl _) , ⟨∅⟩＝v ∣)
                                               (from-∈-of-𝕍-set (transport (v ∈_) (⟨⟨∅⟩⟩＝u ⁻¹) v∈u))
            })
         (from-∈-of-𝕍-set u∈⟨∅,⟨⟨∅⟩⟩⟩)

 Example-17-v : is-transitive-set ⟨⟨∅⟩⟩ → 𝟘 {𝓤}
 Example-17-v transitive-⟨⟨∅⟩⟩ =
   ∥∥-rec 𝟘-is-prop (λ (_ , ⟨∅⟩＝∅) → ¬∅＝⟨∅⟩ ⟨∅⟩＝∅) (from-∈-of-𝕍-set ∅∈⟨⟨∅⟩⟩)
   where
     ∅∈⟨⟨∅⟩⟩ : ∅ ∈ ⟨⟨∅⟩⟩
     ∅∈⟨⟨∅⟩⟩ = transitive-⟨⟨∅⟩⟩ ⟨∅⟩ ∅ (to-∈-of-𝕍-set ∣ _ , refl ∣) (to-∈-of-𝕍-set ∣ _ , refl ∣)
     ¬∅＝⟨∅⟩ : ⟨∅⟩ ＝ ∅ → 𝟘 {𝓤}
     ¬∅＝⟨∅⟩ ⟨∅⟩＝∅ = ¬x∈∅ {∅} (transport (∅ ∈_) ⟨∅⟩＝∅ (to-∈-of-𝕍-set ∣ _ , refl ∣))

 -- Set-theoretic ordinal
 Definition-18 : 𝕍 → 𝓤 ⁺ ̇
 Definition-18 = is-set-theoretic-ordinal

 Lemma-19 : {x : 𝕍} → is-set-theoretic-ordinal x
          → {y : 𝕍}
          → y ∈ x → is-set-theoretic-ordinal y
 Lemma-19 = being-set-theoretic-ordinal-is-hereditary

 {- C. Set theory in homotopy type theory -}

 -- Equal images
 -- f ≈ g denotes that f and g have equal images.
 Definition-20 : {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓣 ̇} → (A → X) → (B → X) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 Definition-20 = _≈_

 -- Cumulative hierarchy
 Definition-21 : 𝓤 ⁺ ̇
 Definition-21 = 𝕍

 -- Set membership
 Definition-22 : 𝕍 → 𝕍 → 𝓤 ⁺ ̇
 Definition-22 = _∈_

 -- Subset relation
 Definition-23 : 𝕍 → 𝕍 → 𝓤 ⁺ ̇
 Definition-23 = _⊆_

 Lemma-24-i : (x y : 𝕍) → (x ＝ y) ↔ (x ⊆ y × y ⊆ x)
 Lemma-24-i x y = (λ x=y → ＝-to-⊆ x=y , ＝-to-⊆ (x=y ⁻¹))
                , (λ (p , q) → ∈-extensionality x y p q)
 --
 Lemma-24-ii : {𝓣 : Universe} (P : 𝕍 → 𝓣 ̇ )
             → ((x : 𝕍) → is-prop (P x))
             → ((x : 𝕍) → ((y : 𝕍) → y ∈ x → P y) → P x)
             → (x : 𝕍) → P x
 Lemma-24-ii = ∈-induction

 -- Type of set-theoretic ordinals
 Definition-25 : 𝓤 ⁺ ̇
 Definition-25 = 𝕍ᵒʳᵈ

 Theorem-26 : OrdinalStructure 𝕍ᵒʳᵈ
 Theorem-26 = _∈ᵒʳᵈ_
            , (λ x y → ∈-is-prop-valued)
            , ∈ᵒʳᵈ-is-well-founded
            , ∈ᵒʳᵈ-is-extensional
            , ∈ᵒʳᵈ-is-transitive

 {- D. Set-theoretic and type-theoretic ordinals coincide -}

 -- Map Φ
 Definition-27 : Ordinal 𝓤 → 𝕍
 Definition-27 = Φ

 Lemma-28-i : (α β : Ordinal 𝓤)
            → (α ＝ β) ↔ (Φ α ＝ Φ β)
 Lemma-28-i α β = ap Φ , Φ-is-left-cancellable α β
 --
 Lemma-28-ii : (α β : Ordinal 𝓤)
             → (α ⊲ β) ↔ (Φ α ∈ Φ β)
 Lemma-28-ii α β = Φ-preserves-strict-order α β , Φ-reflects-strict-order α β
 --
 Lemma-28-iii : (α β : Ordinal 𝓤)
              → (α ⊴ β) ↔ (Φ α ⊆ Φ β)
 Lemma-28-iii α β = Φ-preserves-weak-order α β , Φ-reflects-weak-order α β

 -- The map Φ : Ord → V factors through the inclusion 𝕍ᵒʳᵈ → 𝕍.
 Lemma-29 : Ordinal 𝓤 → 𝕍ᵒʳᵈ
 Lemma-29 = Φᵒʳᵈ

 -- Map Ψ
 Definition-30 : 𝕍 → Ordinal 𝓤
 Definition-30 = Ψ

 -- Remark-31 : No formalizable content

 Proposition-32 : Φᵒʳᵈ ∘ Ψᵒʳᵈ ∼ id
 Proposition-32 = Ψᵒʳᵈ-is-section-of-Φᵒʳᵈ

 Theorem-33 : (OO 𝓤 ≃ₒ 𝕍ᴼᴿᴰ)
            × (OO 𝓤 ＝ 𝕍ᴼᴿᴰ)
 Theorem-33 = 𝕍ᵒʳᵈ-isomorphic-to-Ord
            , eqtoidₒ (OO 𝓤)  𝕍ᴼᴿᴰ 𝕍ᵒʳᵈ-isomorphic-to-Ord

 {- E. Revisiting the rank of a set -}

 -- Type of elements
 Definition-34 : (x : 𝕍) (σ : is-set-theoretic-ordinal x)
               → (𝓤 ⁺ ̇)
 Definition-34 = 𝕋x ch

 -- The type of elements with ∈ is a type-theroetic ordinal.
 Proposition-35 : (x : 𝕍) (σ : is-set-theoretic-ordinal x)
                → Ordinal (𝓤 ⁺)
 Proposition-35 = 𝕋xᵒʳᵈ ch

 -- Bisimulation
 -- The 𝓤-valued bisimulation relation ＝⁻ is named ≈ in the paper.
 Definition-36 : 𝕍 → 𝕍 → 𝓤 ̇
 Definition-36 = _＝⁻_

 Lemma-37 : {x y : 𝕍} → (x ＝⁻ y) ≃ (x ＝ y)
 Lemma-37 = ＝⁻-≃-＝

 -- Membership
 -- The 𝓤-valued membership relation ∈⁻ is named ∈ᵤ in the paper.
 Definition-38 : 𝕍 → 𝕍 → 𝓤 ̇
 Definition-38 = _∈⁻_

 Lemma-39 : {x y : 𝕍} → x ∈⁻ y ≃ x ∈ y
 Lemma-39 = ∈⁻-≃-∈

 -- Set quotients
 -- The 𝓤-valued equivalence relation ~⁻ is named ~ᵤ in the paper.
 Definition-40 : {A : 𝓤 ̇} (f : A → 𝕍)
               → (A → A → 𝓤 ⁺ ̇) × (𝓤 ⁺ ̇)
               × (A → A → 𝓤 ̇) × (𝓤 ̇)
 Definition-40 f = _~_ f , A/~ f
                 , _~⁻_ f , A/~⁻ f

 Lemma-41 : {A : 𝓤 ̇} (f : A → 𝕍)
          → (A/~ f ≃ A/~⁻ f)
          × (image f ≃ A/~ f)
 Lemma-41 f = A/~-≃-A/~⁻ f
            , UF.Quotient.set-replacement-construction.image-≃-quotient
                 sq pt f 𝕍-is-locally-small 𝕍-is-large-set

 -- Order relation
 -- The 𝓤-valued order relation ≺⁻ is named ≺ᵤ in the paper.
 Definition-42 : {A : 𝓤 ̇} (f : A → 𝕍) (σ : is-set-theoretic-ordinal (𝕍-set f))
               → (A/~ f → A/~ f → 𝓤 ⁺ ̇)
               × (A/~⁻ f → A/~⁻ f → 𝓤 ̇)
 Definition-42 f σ = _≺_ f
                   , _≺⁻_ f σ

 Proposition-43 : {A : 𝓤 ̇} (f : A → 𝕍) (σ : is-set-theoretic-ordinal (𝕍-set f))
                → Ordinal (𝓤 ⁺)
                × Ordinal 𝓤
 Proposition-43 f σ = A/~ᵒʳᵈ f σ
                    , A/~⁻ᵒʳᵈ f σ

 Lemma-44 : {A : 𝓤 ̇} (f : A → 𝕍) (σ : is-set-theoretic-ordinal (𝕍-set f))
          → total-spaceᵒʳᵈ ch (𝕍-set f) σ ＝ A/~ᵒʳᵈ f σ
 Lemma-44 = total-space-is-quotientᵒʳᵈ

 Theorem-45 : {A : 𝓤 ̇} (f : A → 𝕍) (σ : is-set-theoretic-ordinal (𝕍-set f))
            → Ψᵒʳᵈ (𝕍-set f , σ) ＝ A/~⁻ᵒʳᵈ f σ
 Theorem-45 = Ψᵒʳᵈ-is-quotient-of-carrier

 Corollary-46 : (x : 𝕍) (σ : is-set-theoretic-ordinal x)
              → Ψᵒʳᵈ (x , σ) ≃ₒ total-spaceᵒʳᵈ ch x σ
 Corollary-46 = Ψᵒʳᵈ-is-isomorphic-to-total-space ch sq
