----------------------------------------------------------------------------------------------------
-- Index of the Agda Development of the paper
--
--     Set-Theoretic and Type-Theoretic Ordinals Coincide
--
----------------------------------------------------------------------------------------------------

{- §III GENERALIZING FROM ORDINALS TO SETS -}

-- These files are tested with
--
--  ● Agda version 2.6.2.2 and
--
--  ● Cubical Agda library (version 0.4).

{-# OPTIONS --safe --cubical #-}

module index where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Induction.WellFounded

open import PropTrunc

open import Iff
open import ExtensionalWellfoundedOrder.Base hiding (isSetCarrier; isSimulation; _≤_; _<_)
open import Cubical.HITs.CumulativeHierarchy.Base

open import Relation.Closure
open import MEWO.Base hiding (ℓ ; ℓ')
open import MEWO.Covered
open import MEWO.Constructions
open import MEWO.TranslationV

variable ℓ ℓ' : Level


{- A. Mewos: marked extensional wellfounded orders -}

-- mewos and covered mewos
Definition-47 : (Type ℓ → Type (ℓ-suc ℓ))
              × ((A : MEWO ℓ) → ⟨ A ⟩ → Type ℓ)
              × (MEWO ℓ → Type ℓ)
              × Type (ℓ-suc ℓ)
Definition-47 {ℓ = ℓ} = MEWO-structure
                     , marked
                     , isCovered
                     , MEWOcov ℓ

Remark-48 : ((A : MEWO ℓ) → isSet (⟨ A ⟩))
          × ((A B : MEWO ℓ) → (A ≡ B) ≃ (A ≃ₒ B))
Remark-48 = isSetCarrier
          , λ A B → (idtoeqₒ A B , UAₒ A B)

-- Ordinals as covered mewos
Example-49 : Ord → MEWOcov _
Example-49 (X ,, _≺_ ,, trunc ,, wf ,, ext ,, trans) =
           (X , (_≺_ , λ _ → Unit , isPropUnit) , trunc , ext , wf) ,
           (λ x → ∣ x , tt , ReflTransCl.done ∣)

{- B. Order relations between mewos -}

-- Simulation
Definition-50 : ((A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → Type _)
              × (MEWO ℓ → MEWO ℓ' → Type _)
              × (MEWOcov ℓ → MEWOcov ℓ → Type ℓ)
Definition-50 = isSimulation
              , _≤_
              , _≤c_

Lemma-51-i : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩)
           → isSimulation A B f → {x y : ⟨ A ⟩} → f x ≡ f y → x ≡ y
Lemma-51-i = simulationsInjective
--
Lemma-51-ii : ((A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → isProp (isSimulation A B f))
            × ((A : MEWO ℓ)(B : MEWO ℓ') → isProp (A ≤ B))
Lemma-51-ii = isPropSimulation
            , isProp⟨≤⟩
--
Lemma-51-iii : (A B : MEWO ℓ) → A ≤ B → B ≤ A → A ≡ B
Lemma-51-iii = ≤Antisymmetry
--
Lemma-51-iv  : (A : MEWO ℓ)(B : MEWO ℓ')(C : MEWO ℓ'') → A ≤ B → B ≤ C → A ≤ C
Lemma-51-iv = ≤Trans
--
Lemma-51-v : isSet (MEWO ℓ)
Lemma-51-v = isSetMEWO
--
Lemma-51-vi : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩)
            → isSimulationWithExists A B f → isSimulation A B f
Lemma-51-vi = existsSimulationsAreSimulations

-- Initial segment
Definition-52 : (A : MEWO ℓ) → ⟨ A ⟩ → MEWO ℓ
Definition-52 = _↓+_

Lemma-53 : (A : MEWO ℓ) → (a : ⟨ A ⟩) → isCovered (A ↓+ a)
Lemma-53 = initialSegmentsCovered

-- Bounded simulation
Definition-54 : (MEWO ℓ → MEWO ℓ' → Type (ℓ-max ℓ ℓ'))
              × (MEWOcov ℓ → MEWOcov ℓ → Type ℓ)
Definition-54 = _<⁻_
              , _≤c_

Lemma-55 : WellFounded (_<_ {ℓ = ℓ})
         × WellFounded (_<c_ {ℓ = ℓ})
Lemma-55 = <Wellfounded
         , coveredWellfounded

{- C. Subtleties caused by markings -}

-- Trivializing the marking: every element of a mewo is marked
Definition-56 : MEWO ℓ → MEWO ℓ
Definition-56 = markAll

Lemma-57-i : (X : MEWO ℓ) → (x : ⟨ X ⟩) → isSimulation (X ↓+ x) (markAll X) fst
Lemma-57-i = segment-inclusion-markAll
--
Lemma-57-ii : (X Y : MEWO ℓ) → X < Y → X ≤ markAll Y
Lemma-57-ii = <-to-<-withoutMarking
--
Lemma-57-iii : (X Y Z : MEWO ℓ) → X < Y → Y < Z → X < markAll Z
Lemma-57-iii = <-transWithoutMarking

Lemma-58 : (A : MEWO ℓ) (x y : ⟨ A ⟩) → (A ↓+ x) ≡ (A ↓+ y) → x ≡ y
Lemma-58 = ↓+Injective

Corollary-59 : (A B : MEWO ℓ) → isProp (A < B)
Corollary-59 = isProp⟨<⟩

{- D. Simulations and coverings -}

Lemma-60 : (A B : MEWO ℓ) (f : ⟨ A ⟩ → ⟨ B ⟩) → isMarkingPreserving A B f
         → isSimulation A B f ↔ ((a : ⟨ A ⟩) → A ↓+ a ≡ B ↓+ f a)
Lemma-60 A B f mpf = simulationsPreserve↓ A B f , λ q → preserve↓→Simulation A B f q mpf

Corollary-61 : (X Y Z : MEWO ℓ) → X < Y → Y ≤ Z → X < Z
Corollary-61 = <∘≤-in-<

-- Partial simulation
Definition-62 : ((A B : MEWO ℓ) → (f : (x : ⟨ A ⟩) → marked A x → ⟨ B ⟩) → Type _)
              × (MEWO ℓ → MEWO ℓ → Type _)
Definition-62 = IsPartialSimulation
              , _≤ₚ_

Lemma-63 : ((A B : MEWO ℓ) →
            A ≤ₚ B ≡
            ((x : ⟨ A ⟩) → (marked A x) → ∥ Σ[ y ∈ ⟨ B ⟩ ] (A ↓+ x ≡ B ↓+ y) × marked B y ∥))
         × ((A B : MEWO ℓ) → isProp (A ≤ₚ B))
Lemma-63 = ≤ₚCharacterisation
         , isProp⟨≤ₚ⟩

-- Principality
Definition-64 : MEWO ℓ → Type (ℓ-suc ℓ)
Definition-64 = isPrincipal

Lemma-65 : (A : MEWO ℓ)
         → isCovered A ↔ isPrincipal A
Lemma-65 A = covered→principal A , principal→covered A

Theorem-66 : isEWO (_<c_ {ℓ = ℓ})
Theorem-66 = isEWO⟨MEWOcov⟩

{- E. Constructions on mewos -}

-- Singleton
Definition-67 : ((A : MEWO ℓ) → ⟨ A ⟩ ⊎ Unit → ⟨ A ⟩ ⊎ Unit → Type ℓ)
              × ((A : MEWO ℓ) → ⟨ A ⟩ ⊎ Unit → hProp ℓ)
              × ((A : MEWO ℓ) → isCovered A → MEWO ℓ)
Definition-67 = succ-<
              , succ-marking
              , succ

Lemma-68 : ((A : MEWO ℓ) → (cov : isCovered A) → isCovered (succ A cov))
         × (MEWOcov ℓ → MEWOcov ℓ)
Lemma-68 = succCovered
         , csucc

-- Union of mewos
Definition-69 : (A : Type ℓ) → (A → MEWO ℓ) → MEWO ℓ
Definition-69 = ⋃

-- Remark-70 : No formalizable content

Lemma-71 : (A : Type ℓ) (F : A → MEWO ℓ)
         → ((a : A) → F a ≤ ⋃ A F)
         × ((X : MEWO ℓ) → ((a : A) → F a ≤ X) → ⋃ A F ≤ X)
Lemma-71 A F = ⋃-isUpperBound A F
             , ⋃-isLeastUpperBound A F

Lemma-72 : (A : Type ℓ) (F : A → MEWO ℓ)
         → ((a : A) → isCovered (F a)) → isCovered (⋃ A F)
Lemma-72 = ⋃-covered

-- Remark-73 : No formalizable content

{- F. V-sets and covered mewos coincide -}

Lemma-74 : V-as-MEWO ℓ ≤ MEWOcov-as-MEWO ℓ
Lemma-74 = ψ , ψ-simulation

Lemma-75 : MEWOcov-as-MEWO ℓ ≤ V-as-MEWO ℓ
Lemma-75 = φ , φ-simulation

Theorem-76 : V-as-MEWO ℓ ≡ MEWOcov-as-MEWO ℓ
Theorem-76 = V≡MEWOcov
