----------------------------------------------------------------------------------------------------
-- Index of the Agda Development of the paper
--
--     Set-Theoretic and Type-Theoretic Ordinals Coincide
--
----------------------------------------------------------------------------------------------------

{- ยงII ORDINALS IN TYPE THEORY AND SET THEORY -}

-- These files are tested with
--
--  โ Agda version 2.6.2.2 and
--
--  โ TypeTopology (commit: 318d913c878c1f3cbcfd03c911ed6c1461bf1d9f)

{-# OPTIONS --safe #-}

open import MLTT.Spartan

open import UF.PropTrunc
open import UF.Univalence
open import UF.Base hiding (_โ_)
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
         (๐ค : Universe)
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
open import OrdinalCumulativeHierarchy pt ua ๐ค
open import OrdinalCumulativeHierarchy-Addendum pt ua ๐ค

open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.WellOrderTransport fe'
open import Ordinals.Underlying
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Arithmetic fe'
open import Ordinals.Arithmetic-Properties ua

module _ (ch : cumulative-hierarchy-exists ๐ค)
 where

 open cumulative-hierarchy-exists ch
 open ๐-is-locally-small ch
 open ordinal-of-set-theoretic-ordinals ch
 open total-space-of-an-element-of-๐
 open ฮจ-construction sq
 open ๐-set-carrier-quotient ch sq
 open small-quotient-as-ordinal
 open quotient-as-ordinal
 open suprema pt (set-replacement-from-set-quotients sq pt)


 {- A. Ordinals in homotopy type theory -}

 -- Accessibility
 Definition-1 : {X : ๐ค ฬ} (_<_ : X โ X โ ๐ฅ ฬ) โ X โ ๐ค โ ๐ฅ ฬ
 Definition-1 = is-accessible

 Lemma-2-โ : {X : ๐ค ฬ} (_<_ : X โ X โ ๐ฅ ฬ)
           โ (โ x โ is-accessible _<_ x)
           โ โ {๐ฆ} (P : X โ ๐ฆ ฬ) โ (โ x โ (โ y โ y < x โ P y) โ P x) โ โ x โ P x
 Lemma-2-โ = transfinite-induction
 --
 Lemma-2-โ : {X : ๐ค ฬ} (_<_ : X โ X โ ๐ฅ ฬ)
           โ (โ {๐ฆ} (P : X โ ๐ฆ ฬ) โ (โ x โ (โ y โ y < x โ P y) โ P x) โ โ x โ P x)
           โ โ x โ is-accessible _<_ x
 Lemma-2-โ _<_ ti = ti (is-accessible _<_) (ฮป _ โ step)

 -- Type-theoretic ordinal
 Definition-3 : ({X : ๐ค ฬ} (_<_ : X โ X โ ๐ฅ ฬ) โ (๐ค โ ๐ฅ ฬ))
              ร ({X : ๐ค ฬ} (_<_ : X โ X โ ๐ฅ ฬ) โ (๐ค โ ๐ฅ ฬ))
              ร ({X : ๐ค ฬ} (_<_ : X โ X โ ๐ฅ ฬ) โ (๐ค โ ๐ฅ ฬ))
              ร ({X : ๐ค ฬ} (_<_ : X โ X โ ๐ฅ ฬ) โ (๐ค โ ๐ฅ ฬ))
              ร (๐ค โบ ฬ)
 Definition-3 = is-prop-valued
              , is-well-founded
              , is-extensional
              , is-transitive
              , Ordinal _

 Remark-4 : (ฮฑ : Ordinal ๐ค) โ is-set โจ ฮฑ โฉ
 Remark-4 = underlying-type-is-set fe'

 -- Initial segment and bounded simulation
 -- The bounded simulation relation โฒ is named < in the paper.
 Definition-5 : ((ฮฑ : Ordinal ๐ค) โ โจ ฮฑ โฉ โ Ordinal ๐ค)
              ร (Ordinal ๐ค โ Ordinal ๐ค โ ๐ค โบ ฬ)
 Definition-5 = _โ_
              , _โฒ_

 -- โฒโป is the small version of โฒ
 Remark-6 : (ฮฑ ฮฒ : Ordinal ๐ค) โ (ฮฑ โฒ ฮฒ) โ (ฮฑ โฒโป ฮฒ)
 Remark-6 = โฒ-is-equivalent-to-โฒโป

 -- The ordinal OO of ordinals is named Ord in the paper.
 Theorem-7 : is-well-order (_โฒ_ {๐ค}) ร (Ordinal (๐ค โบ))
 Theorem-7 = โฒ-is-well-order , OO _

 -- Simulation
 -- The simulation relation โด is named โค in the paper.
 Definition-8 : ((ฮฑ : Ordinal ๐ค) (ฮฒ : Ordinal ๐ฅ) โ (โจ ฮฑ โฉ โ โจ ฮฒ โฉ) โ ๐ค โ ๐ฅ ฬ)
              ร (Ordinal ๐ค โ Ordinal ๐ฅ โ ๐ค โ ๐ฅ ฬ)
 Definition-8 = is-simulation
              , _โด_

 Proposition-9 : ((ฮฑ : Ordinal ๐ค) โ ฮฑ โด ฮฑ)
               ร ((ฮฑ ฮฒ : Ordinal ๐ค) โ ฮฑ โด ฮฒ โ ฮฒ โด ฮฑ โ ฮฑ ๏ผ ฮฒ)
               ร ((ฮฑ : Ordinal ๐ค) (ฮฒ : Ordinal ๐ฅ) (ฮณ : Ordinal ๐ฆ) โ ฮฑ โด ฮฒ โ ฮฒ โด ฮณ โ ฮฑ โด ฮณ)
               ร ((ฮฑ ฮฒ : Ordinal ๐ค) โ ฮฑ โด ฮฒ
                                    โ โ ฮณ โ ฮณ โฒ ฮฑ โ ฮณ โฒ ฮฒ)
               ร ({ฮฑ ฮฒ : Ordinal ๐ค} โ (โ ฮณ โ ฮณ โฒ ฮฑ โ ฮณ โฒ ฮฒ)
                                    โ (a : โจ ฮฑ โฉ) โ ฮฃ b ๊ โจ ฮฒ โฉ , (ฮฑ โ a) ๏ผ (ฮฒ โ b))
               ร ({ฮฑ ฮฒ : Ordinal ๐ค} โ ((a : โจ ฮฑ โฉ) โ ฮฃ b ๊ โจ ฮฒ โฉ , (ฮฑ โ a) ๏ผ (ฮฒ โ b))
                                    โ ฮฑ โด ฮฒ)
 Proposition-9 = โด-refl
               , โด-antisym
               , โด-trans
               , โด-gives-โผ
               , from-โผ
               , to-โด _ _

 Lemma-10 : (ฮฑ : Ordinal ๐ค) (ฮฒ : Ordinal ๐ฅ) (f : โจ ฮฑ โฉ โ โจ ฮฒ โฉ)
          โ (is-order-equiv ฮฑ ฮฒ f) โ
            (is-equiv f ร is-order-preserving ฮฑ ฮฒ f ร is-order-reflecting ฮฑ ฮฒ f)
 Lemma-10 ฮฑ ฮฒ f = (ฮป p โ order-equivs-are-equivs ฮฑ ฮฒ p
                       , order-equivs-are-order-preserving ฮฑ ฮฒ p
                       , order-equivs-are-order-reflecting ฮฑ ฮฒ f p)
                , (ฮป (x , y , z) โ order-preserving-reflecting-equivs-are-order-equivs ฮฑ ฮฒ f x y z)

 Lemma-11 : (ฮฑ : Ordinal ๐ค) (a b : โจ ฮฑ โฉ) (p : b โบโจ ฮฑ โฉ a)
          โ ((ฮฑ โ a ) โ (b , p)) ๏ผ (ฮฑ โ b)
 Lemma-11 = iterated-โ

 -- Sum of type-theoretic ordinals
 Definition-12 : Ordinal ๐ค โ Ordinal ๐ค โ Ordinal ๐ค
 Definition-12 = _+โ_

 Lemma-13-i : {ฮฑ ฮฒ : Ordinal ๐ค} (a : โจ ฮฑ โฉ)
            โ (ฮฑ โ a) ๏ผ ((ฮฑ +โ ฮฒ) โ inl a)
 Lemma-13-i = +โ-โ-left
 --
 Lemma-13-ii : (ฮฑ : Ordinal ๐ค) โ (ฮฑ +โ ๐โ) โ inr โ ๏ผ ฮฑ
 Lemma-13-ii = +โ-๐โ-โ-right

 -- Supremum of type-theoretic ordinals
 Definition-14 : {I : ๐ค ฬ} (ฮฑ : I โ Ordinal ๐ค) โ Ordinal ๐ค
 Definition-14 = sup

 Lemma-15-i : {I : ๐ค ฬ} (ฮฑ : I โ Ordinal ๐ค)
            โ (i : I) (x : โจ ฮฑ i โฉ) โ sup ฮฑ โ prโ (sup-is-upper-bound ฮฑ i) x ๏ผ ฮฑ i โ x
 Lemma-15-i = initial-segment-of-sup-at-component
 --
 Lemma-15-ii : {I : ๐ค ฬ} (ฮฑ : I โ Ordinal ๐ค)
             โ (y : โจ sup ฮฑ โฉ) โ โฅ ฮฃ i ๊ I , ฮฃ x ๊ โจ ฮฑ i โฉ , sup ฮฑ โ y ๏ผ ฮฑ i โ x โฅ
 Lemma-15-ii = initial-segment-of-sup-is-initial-segment-of-some-component

 {- B. Ordinals in set theory -}

 -- (Here, we phrase the definitions and lemmas from set theory in terms of ๐ introduced below.)

 -- Transitive set
 Definition-16 : ๐ โ ๐ค โบ ฬ
 Definition-16 = is-transitive-set

 -- Example 17:

 โ โจโโฉ โจโ,โจโโฉโฉ โจโจโโฉโฉ โจโ,โจโโฉ,โจโจโโฉโฉโฉ : ๐
 โ = ๐-set {๐} ๐-elim
 โจโโฉ = ๐-set {๐} (ฮป _ โ โ)
 โจโ,โจโโฉโฉ = ๐-set {๐ {๐ค} + ๐ {๐ค}} (cases (ฮป _ โ โ) (ฮป _ โ โจโโฉ))
 โจโจโโฉโฉ = ๐-set {๐} ฮป _ โ โจโโฉ
 โจโ,โจโโฉ,โจโจโโฉโฉโฉ = ๐-set {๐ {๐ค} + ๐ {๐ค} + ๐ {๐ค}} (cases (ฮป _ โ โ) (cases (ฮป _ โ โจโโฉ) ฮป _ โ โจโจโโฉโฉ))

 ยฌxโโ : {x : ๐} โ x โ โ โ ๐
 ยฌxโโ xโโ = โฅโฅ-rec ๐-is-prop prโ (from-โ-of-๐-set xโโ)

 Example-17-i : is-transitive-set โ
 Example-17-i u v uโโ vโu = ๐-elim (ยฌxโโ uโโ)

 Example-17-ii : is-transitive-set โจโโฉ
 Example-17-ii u v uโโจโโฉ vโu =
   โฅโฅ-rec โ-is-prop-valued
         (ฮป (_ , โ๏ผu) โ ๐-elim (ยฌxโโ (transport (v โ_) (โ๏ผu โปยน) vโu)))
         (from-โ-of-๐-set uโโจโโฉ)

 Example-17-iii : is-transitive-set โจโ,โจโโฉโฉ
 Example-17-iii u v uโโจโ,โจโโฉโฉ vโu =
   โฅโฅ-rec โ-is-prop-valued
         (ฮป { (inl _ , โ๏ผu) โ ๐-elim (ยฌxโโ (transport (v โ_) (โ๏ผu โปยน) vโu))
            ; (inr _ , โจโโฉ๏ผu) โ โฅโฅ-rec โ-is-prop-valued
                                       (ฮป (_ , โ๏ผv) โ to-โ-of-๐-set โฃ inl _ , โ๏ผv โฃ)
                                       (from-โ-of-๐-set (transport (v โ_) (โจโโฉ๏ผu โปยน) vโu))
            })
         (from-โ-of-๐-set uโโจโ,โจโโฉโฉ)

 Example-17-iv : is-transitive-set โจโ,โจโโฉ,โจโจโโฉโฉโฉ
 Example-17-iv u v uโโจโ,โจโจโโฉโฉโฉ vโu =
   โฅโฅ-rec โ-is-prop-valued
         (ฮป { (inl _ , โ๏ผu) โ ๐-elim (ยฌxโโ (transport (v โ_) (โ๏ผu โปยน) vโu))
            ; (inr (inl _) , โจโโฉ๏ผu) โ โฅโฅ-rec โ-is-prop-valued
                                             (ฮป (_ , โ๏ผv) โ to-โ-of-๐-set โฃ inl _ , โ๏ผv โฃ)
                                             (from-โ-of-๐-set (transport (v โ_) (โจโโฉ๏ผu โปยน) vโu))
            ; (inr (inr _) , โจโจโโฉโฉ๏ผu) โ โฅโฅ-rec โ-is-prop-valued
                                               (ฮป (_ , โจโโฉ๏ผv) โ to-โ-of-๐-set โฃ inr (inl _) , โจโโฉ๏ผv โฃ)
                                               (from-โ-of-๐-set (transport (v โ_) (โจโจโโฉโฉ๏ผu โปยน) vโu))
            })
         (from-โ-of-๐-set uโโจโ,โจโจโโฉโฉโฉ)

 Example-17-v : is-transitive-set โจโจโโฉโฉ โ ๐ {๐ค}
 Example-17-v transitive-โจโจโโฉโฉ =
   โฅโฅ-rec ๐-is-prop (ฮป (_ , โจโโฉ๏ผโ) โ ยฌโ๏ผโจโโฉ โจโโฉ๏ผโ) (from-โ-of-๐-set โโโจโจโโฉโฉ)
   where
     โโโจโจโโฉโฉ : โ โ โจโจโโฉโฉ
     โโโจโจโโฉโฉ = transitive-โจโจโโฉโฉ โจโโฉ โ (to-โ-of-๐-set โฃ _ , refl โฃ) (to-โ-of-๐-set โฃ _ , refl โฃ)
     ยฌโ๏ผโจโโฉ : โจโโฉ ๏ผ โ โ ๐ {๐ค}
     ยฌโ๏ผโจโโฉ โจโโฉ๏ผโ = ยฌxโโ {โ} (transport (โ โ_) โจโโฉ๏ผโ (to-โ-of-๐-set โฃ _ , refl โฃ))

 -- Set-theoretic ordinal
 Definition-18 : ๐ โ ๐ค โบ ฬ
 Definition-18 = is-set-theoretic-ordinal

 Lemma-19 : {x : ๐} โ is-set-theoretic-ordinal x
          โ {y : ๐}
          โ y โ x โ is-set-theoretic-ordinal y
 Lemma-19 = being-set-theoretic-ordinal-is-hereditary

 {- C. Set theory in homotopy type theory -}

 -- Equal images
 -- f โ g denotes that f and g have equal images.
 Definition-20 : {A : ๐ค ฬ} {B : ๐ฅ ฬ} {X : ๐ฃ ฬ} โ (A โ X) โ (B โ X) โ ๐ค โ ๐ฅ โ ๐ฃ ฬ
 Definition-20 = _โ_

 -- Cumulative hierarchy
 Definition-21 : ๐ค โบ ฬ
 Definition-21 = ๐

 -- Set membership
 Definition-22 : ๐ โ ๐ โ ๐ค โบ ฬ
 Definition-22 = _โ_

 -- Subset relation
 Definition-23 : ๐ โ ๐ โ ๐ค โบ ฬ
 Definition-23 = _โ_

 Lemma-24-i : (x y : ๐) โ (x ๏ผ y) โ (x โ y ร y โ x)
 Lemma-24-i x y = (ฮป x=y โ ๏ผ-to-โ x=y , ๏ผ-to-โ (x=y โปยน))
                , (ฮป (p , q) โ โ-extensionality x y p q)
 --
 Lemma-24-ii : {๐ฃ : Universe} (P : ๐ โ ๐ฃ ฬ )
             โ ((x : ๐) โ is-prop (P x))
             โ ((x : ๐) โ ((y : ๐) โ y โ x โ P y) โ P x)
             โ (x : ๐) โ P x
 Lemma-24-ii = โ-induction

 -- Type of set-theoretic ordinals
 Definition-25 : ๐ค โบ ฬ
 Definition-25 = ๐แตสณแต

 Theorem-26 : OrdinalStructure ๐แตสณแต
 Theorem-26 = _โแตสณแต_
            , (ฮป x y โ โ-is-prop-valued)
            , โแตสณแต-is-well-founded
            , โแตสณแต-is-extensional
            , โแตสณแต-is-transitive

 {- D. Set-theoretic and type-theoretic ordinals coincide -}

 -- Map ฮฆ
 Definition-27 : Ordinal ๐ค โ ๐
 Definition-27 = ฮฆ

 Lemma-28-i : (ฮฑ ฮฒ : Ordinal ๐ค)
            โ (ฮฑ ๏ผ ฮฒ) โ (ฮฆ ฮฑ ๏ผ ฮฆ ฮฒ)
 Lemma-28-i ฮฑ ฮฒ = ap ฮฆ , ฮฆ-is-left-cancellable ฮฑ ฮฒ
 --
 Lemma-28-ii : (ฮฑ ฮฒ : Ordinal ๐ค)
             โ (ฮฑ โฒ ฮฒ) โ (ฮฆ ฮฑ โ ฮฆ ฮฒ)
 Lemma-28-ii ฮฑ ฮฒ = ฮฆ-preserves-strict-order ฮฑ ฮฒ , ฮฆ-reflects-strict-order ฮฑ ฮฒ
 --
 Lemma-28-iii : (ฮฑ ฮฒ : Ordinal ๐ค)
              โ (ฮฑ โด ฮฒ) โ (ฮฆ ฮฑ โ ฮฆ ฮฒ)
 Lemma-28-iii ฮฑ ฮฒ = ฮฆ-preserves-weak-order ฮฑ ฮฒ , ฮฆ-reflects-weak-order ฮฑ ฮฒ

 -- The map ฮฆ : Ord โ V factors through the inclusion ๐แตสณแต โ ๐.
 Lemma-29 : Ordinal ๐ค โ ๐แตสณแต
 Lemma-29 = ฮฆแตสณแต

 -- Map ฮจ
 Definition-30 : ๐ โ Ordinal ๐ค
 Definition-30 = ฮจ

 -- Remark-31 : No formalizable content

 Proposition-32 : ฮฆแตสณแต โ ฮจแตสณแต โผ id
 Proposition-32 = ฮจแตสณแต-is-section-of-ฮฆแตสณแต

 Theorem-33 : (OO ๐ค โโ ๐แดผแดฟแดฐ)
            ร (OO ๐ค ๏ผ ๐แดผแดฟแดฐ)
 Theorem-33 = ๐แตสณแต-isomorphic-to-Ord
            , eqtoidโ (OO ๐ค)  ๐แดผแดฟแดฐ ๐แตสณแต-isomorphic-to-Ord

 {- E. Revisiting the rank of a set -}

 -- Type of elements
 Definition-34 : (x : ๐) (ฯ : is-set-theoretic-ordinal x)
               โ (๐ค โบ ฬ)
 Definition-34 = ๐x ch

 -- The type of elements with โ is a type-theroetic ordinal.
 Proposition-35 : (x : ๐) (ฯ : is-set-theoretic-ordinal x)
                โ Ordinal (๐ค โบ)
 Proposition-35 = ๐xแตสณแต ch

 -- Bisimulation
 -- The ๐ค-valued bisimulation relation ๏ผโป is named โ in the paper.
 Definition-36 : ๐ โ ๐ โ ๐ค ฬ
 Definition-36 = _๏ผโป_

 Lemma-37 : {x y : ๐} โ (x ๏ผโป y) โ (x ๏ผ y)
 Lemma-37 = ๏ผโป-โ-๏ผ

 -- Membership
 -- The ๐ค-valued membership relation โโป is named โแตค in the paper.
 Definition-38 : ๐ โ ๐ โ ๐ค ฬ
 Definition-38 = _โโป_

 Lemma-39 : {x y : ๐} โ x โโป y โ x โ y
 Lemma-39 = โโป-โ-โ

 -- Set quotients
 -- The ๐ค-valued equivalence relation ~โป is named ~แตค in the paper.
 Definition-40 : {A : ๐ค ฬ} (f : A โ ๐)
               โ (A โ A โ ๐ค โบ ฬ) ร (๐ค โบ ฬ)
               ร (A โ A โ ๐ค ฬ) ร (๐ค ฬ)
 Definition-40 f = _~_ f , A/~ f
                 , _~โป_ f , A/~โป f

 Lemma-41 : {A : ๐ค ฬ} (f : A โ ๐)
          โ (A/~ f โ A/~โป f)
          ร (image f โ A/~ f)
 Lemma-41 f = A/~-โ-A/~โป f
            , UF.Quotient.set-replacement-construction.image-โ-quotient
                 sq pt f ๐-is-locally-small ๐-is-large-set

 -- Order relation
 -- The ๐ค-valued order relation โบโป is named โบแตค in the paper.
 Definition-42 : {A : ๐ค ฬ} (f : A โ ๐) (ฯ : is-set-theoretic-ordinal (๐-set f))
               โ (A/~ f โ A/~ f โ ๐ค โบ ฬ)
               ร (A/~โป f โ A/~โป f โ ๐ค ฬ)
 Definition-42 f ฯ = _โบ_ f
                   , _โบโป_ f ฯ

 Proposition-43 : {A : ๐ค ฬ} (f : A โ ๐) (ฯ : is-set-theoretic-ordinal (๐-set f))
                โ Ordinal (๐ค โบ)
                ร Ordinal ๐ค
 Proposition-43 f ฯ = A/~แตสณแต f ฯ
                    , A/~โปแตสณแต f ฯ

 Lemma-44 : {A : ๐ค ฬ} (f : A โ ๐) (ฯ : is-set-theoretic-ordinal (๐-set f))
          โ total-spaceแตสณแต ch (๐-set f) ฯ ๏ผ A/~แตสณแต f ฯ
 Lemma-44 = total-space-is-quotientแตสณแต

 Theorem-45 : {A : ๐ค ฬ} (f : A โ ๐) (ฯ : is-set-theoretic-ordinal (๐-set f))
            โ ฮจแตสณแต (๐-set f , ฯ) ๏ผ A/~โปแตสณแต f ฯ
 Theorem-45 = ฮจแตสณแต-is-quotient-of-carrier

 Corollary-46 : (x : ๐) (ฯ : is-set-theoretic-ordinal x)
              โ ฮจแตสณแต (x , ฯ) โโ total-spaceแตสณแต ch x ฯ
 Corollary-46 = ฮจแตสณแต-is-isomorphic-to-total-space ch sq
