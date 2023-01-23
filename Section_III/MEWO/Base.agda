
----------------------------------------------------------------------------------------------------
-- Definition and Basic Properties of of Marked Extensional Wellfounded orders
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module MEWO.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure using (typ; str)

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open BinaryRelation
open import Cubical.Induction.WellFounded
  renaming (WellFounded to isWellFounded)

open import PropTrunc

open import General-Properties
open import Relation.Closure

variable
  ℓ ℓ' ℓ'' : Level

isEWO : {A : Type ℓ}(_≺_ : A -> A -> Type ℓ) → Type ℓ
isEWO _≺_ = isPropValued _≺_ × isExtensional _≺_ × isWellFounded _≺_

MEWO-structure : Type ℓ → Type (ℓ-suc ℓ)
MEWO-structure {ℓ = ℓ} A = Σ[ x ∈ ((A -> A -> Type ℓ) × (A → hProp ℓ)) ] (isEWO (fst x))

MEWO : (ℓ : Level) → Type (ℓ-suc ℓ)
MEWO ℓ = Σ[ A ∈ (Type ℓ) ] (MEWO-structure A)

-- Carrier
⟨_⟩  : MEWO ℓ → Type ℓ
⟨_⟩ = fst

underlyingOrder : (A : MEWO ℓ) → ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ
underlyingOrder (A , (_<_ , M) , ax) = _<_

transitiveClosureUnderlyingOrder : (A : MEWO ℓ) → ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ
transitiveClosureUnderlyingOrder A = TransCl (underlyingOrder A)

reflexiveTransitiveClosureUnderlyingOrder : (A : MEWO ℓ) → ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ
reflexiveTransitiveClosureUnderlyingOrder A = ReflTransCl (underlyingOrder A)

syntax underlyingOrder A x y = x ≺⟨ A ⟩ y
syntax transitiveClosureUnderlyingOrder A x y = x ≺⁺⟨ A ⟩ y
syntax reflexiveTransitiveClosureUnderlyingOrder A x y = x ≺̂*⟨ A ⟩ y

marked : (A : MEWO ℓ) → ⟨ A ⟩ → Type ℓ
marked (A , (_<_ , M) , ax) a = typ (M a)

isPropMarked : (A : MEWO ℓ) → (x : ⟨ A ⟩) → isProp (marked A x)
isPropMarked (A , (_<_ , M) , ax) a = str (M a)

truncated : (A : MEWO ℓ) → isPropValued (underlyingOrder A)
truncated (A , (_<_ , M) , ax) = fst ax

extensional : (A : MEWO ℓ) → isExtensional (underlyingOrder A)
extensional (A , (_<_ , M) , ax) = fst (snd ax)

wellfounded : (A : MEWO ℓ) → isWellFounded (underlyingOrder A)
wellfounded (A , (_<_ , M) , ax) = snd (snd ax)

{- The carrier of a MEWO is a set -}

propValued-and-extensional→isSetCarrier : (A : Type ℓ) → (_<_ : A → A → Type ℓ) →
                                          isPropValued _<_ → isExtensional _<_ →
                                          isSet A
propValued-and-extensional→isSetCarrier A _<_ truncated extensional
  = Collapsible≡→isSet λ x y → (f , f-wconst)
     where
       f : ∀ {x y} → x ≡ y → x ≡ y
       f {x} {y} p = extensional x y (λ c → subst (c <_) p , subst (c <_) (sym p))

       f-wconst : ∀ {x y} → (p q : x ≡ y) → f p ≡ f q
       f-wconst {x} {y} p q = cong (extensional x y)
                                   (funExt (λ c → ΣPathP ((funExt λ r → truncated _ _ _ _) ,
                                                          (funExt λ r → truncated _ _ _ _))))

isSetCarrier : (A : MEWO ℓ) → isSet (⟨ A ⟩)
isSetCarrier A
  = propValued-and-extensional→isSetCarrier ⟨ A ⟩ (underlyingOrder A) (truncated A) (extensional A)


isPropIsEWO : {A : Type ℓ}(_≺_ : A -> A -> Type ℓ) → isProp (isEWO _≺_)
isPropIsEWO _≺_ p@(t , e , w) =
  isProp×2 (isPropΠ2 (λ x y → isPropIsProp))
           (isPropΠ2 (λ a b → isProp→ (propValued-and-extensional→isSetCarrier _ _≺_ t e a b)))
           (isPropΠ isPropAcc)  p

{- Notions of structure preservation for MEWOS -}

isMonotone : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isMonotone A B f = ∀ {a a'} → a ≺⟨ A ⟩ a' → f a ≺⟨ B ⟩ f a'

isMarkingPreserving : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isMarkingPreserving A B f = ∀ {a} → marked A a → marked B (f a)

isStructurePreserving : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isStructurePreserving A B f = isMonotone A B f × isMarkingPreserving A B f

isReflecting : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isReflecting A B f = ∀ {a a'} → f a ≺⟨ B ⟩ f a' → a ≺⟨ A ⟩ a'

isOrderEquiv : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isOrderEquiv A B f
  = (isStructurePreserving A B f) × (Σ[ e ∈ isEquiv f ] (isStructurePreserving B A (invIsEq e)))

isPropMonotone : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) → isProp (isMonotone A B f)
isPropMonotone A B f = isPropImplicitΠ2 (λ x x' → isProp→ (truncated B (f x) (f x')))

isPropMarkingPreserving : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) →
                          isProp (isMarkingPreserving A B f)
isPropMarkingPreserving A B f = isPropImplicitΠ (λ a → isProp→ (isPropMarked B (f a)))

isPropStructurePreserving : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) →
                            isProp (isStructurePreserving A B f)
isPropStructurePreserving A B f = isProp× (isPropMonotone A B f) (isPropMarkingPreserving A B f)

isPropOrderEquiv : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) → isProp (isOrderEquiv A B f)
isPropOrderEquiv A B f
  = isProp× (isPropStructurePreserving A B f)
            (isPropΣ (isPropIsEquiv f) λ e → isPropStructurePreserving B A (invIsEq e))

{- Order between MEWOs -}

isSimulation : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isSimulation A B f
  = isStructurePreserving A B f × ∀ {b a} → b ≺⟨ B ⟩ f a → Σ[ a' ∈ ⟨ A ⟩ ] (a' ≺⟨ A ⟩ a × (f a' ≡ b))

isSimulationExceptMarking : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isSimulationExceptMarking A B f
  = isMonotone A B f × ∀ {b a} → b ≺⟨ B ⟩ f a → Σ[ a' ∈ ⟨ A ⟩ ] (a' ≺⟨ A ⟩ a × (f a' ≡ b))

-- Another characterisation of non-marking preserving simulations

markAll : MEWO ℓ → MEWO ℓ
markAll (A , (_≺_ , _) , p) = (A , (_≺_ , λ _ → Unit* , isPropUnit*) , p)

isSimulationExceptMarking→isSimulationMarkAll : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) →
                                                isSimulationExceptMarking A B f →
                                                isSimulation A (markAll B) f
isSimulationExceptMarking→isSimulationMarkAll A B f (mon , sim) = (mon , (λ _ → tt*)) , sim

isSimulationMarkAll→isSimulationExceptMarking : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) →
                                                isSimulation A (markAll B) f →
                                                isSimulationExceptMarking A B f
isSimulationMarkAll→isSimulationExceptMarking A B f ((mon , _) , sim) = (mon , sim)

forgetMarkingPreservation : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) →
                            isSimulation A B f → isSimulationExceptMarking A B f
forgetMarkingPreservation A B f ((mon , mark) , sim) = (mon , sim)

simulationsInjective : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) →
                       isSimulation A B f → {x y : ⟨ A ⟩} → f x ≡ f y → x ≡ y
simulationsInjective A B f ((mon , mark) , sim) {x} {y}
  = wf-step x y (wellfounded A x) (wellfounded A y)
    where
    wf-step : ∀ x y → Acc (underlyingOrder A) x → Acc (underlyingOrder A) y → f x ≡ f y → x ≡ y
    wf-step x y (acc wf-x) (acc wf-y) fx≡fy =
      extensional A x y λ c →
         (λ c<x → let (u , u<y , fu≡fc) = sim (subst (λ z → f c ≺⟨ B ⟩ z) fx≡fy (mon c<x))
                   in subst (λ z → z ≺⟨ A ⟩ y) (wf-step u c (wf-y u u<y) (wf-x c c<x) fu≡fc ) u<y) ,
         (λ c<y → let (u , u<x , fu≡fc) = sim (subst (λ z → f c ≺⟨ B ⟩ z) (sym fx≡fy) (mon c<y))
                   in subst (λ z → z ≺⟨ A ⟩ x) (wf-step u c (wf-x u u<x) (wf-y c c<y) fu≡fc) u<x)


injective→simulationConclusionIsProp : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) →
                                       (∀ {x y} → f x ≡ f y → x ≡ y) → {a : ⟨ A ⟩}{b : ⟨ B ⟩} →
                                       isProp (Σ[ a' ∈ ⟨ A ⟩ ] ((a' ≺⟨ A ⟩ a) × (f a' ≡ b)))
injective→simulationConclusionIsProp A B f f-inj {a} {b} (x , x<a , fx≡b) (y , y<a , fy≡b)
  = Σ≡Prop (λ a' → isProp× (truncated A a' a) (isSetCarrier B (f a') b)) (f-inj (fx≡b ∙ sym fy≡b))

simulationConclusionIsProp : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → isSimulation A B f →
                                {a : ⟨ A ⟩}{b : ⟨ B ⟩} →
                                isProp (Σ[ a' ∈ ⟨ A ⟩ ] ((a' ≺⟨ A ⟩ a) × (f a' ≡ b)))
simulationConclusionIsProp A B f f-sim
  = injective→simulationConclusionIsProp A B f (simulationsInjective A B f f-sim)

isPropSimulation : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → isProp (isSimulation A B f)
isPropSimulation A B f f-sim
  = isProp× (isPropStructurePreserving A B f)
            (isPropImplicitΠ2 (λ b a → isProp→ (simulationConclusionIsProp A B f f-sim))) f-sim

simulationsExceptMarkingUnique : (A : MEWO ℓ)(B : MEWO ℓ') (f g : ⟨ A ⟩ → ⟨ B ⟩) →
                                 isSimulationExceptMarking A B f →
                                 isSimulationExceptMarking A B g →
                                 f ≡ g
simulationsExceptMarkingUnique A B f g (str-f , sim-f) (str-g , sim-g)
  = funExt λ x → wf-step x (wellfounded A x)
    where
    wf-step : (x : ⟨ A ⟩) → Acc (underlyingOrder A) x → f x ≡ g x
    wf-step x (acc wf-x)
      = extensional B (f x) (g x) λ c →
         (λ c<fx → let (y , y<x , fy≡c) = sim-f c<fx
                    in subst (λ z → z ≺⟨ B ⟩ _) (sym (wf-step y (wf-x y y<x)) ∙ fy≡c) (str-g y<x)) ,
         (λ c<gx → let (y , y<x , gy≡c) = sim-g c<gx
                    in subst (λ z → z ≺⟨ B ⟩ _) (wf-step y (wf-x y y<x) ∙ gy≡c) (str-f y<x))

simulationsUnique : (A : MEWO ℓ)(B : MEWO ℓ') (f g : ⟨ A ⟩ → ⟨ B ⟩) →
                    isSimulation A B f → isSimulation A B g → f ≡ g
simulationsUnique A B f g sim-f sim-g
  = simulationsExceptMarkingUnique A B f g (forgetMarkingPreservation A B f sim-f)
                                           (forgetMarkingPreservation A B g sim-g)


simulationsReflect : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) →
                      isSimulation A B f → isReflecting A B f
simulationsReflect A B f (p , q) {x} {y} fx<fy
  = let (x' , x'<y , fx'≡fx) = q fx<fy
     in subst (λ z → z ≺⟨ A ⟩ y) (simulationsInjective A B f (p , q) fx'≡fx) x'<y

simulationsExceptMarking-comp : (A : MEWO ℓ)(B : MEWO ℓ')(C : MEWO ℓ') →
                                (f : ⟨ A ⟩ → ⟨ B ⟩)(g : ⟨ B ⟩ → ⟨ C ⟩) →
                                isSimulationExceptMarking A B f →
                                isSimulationExceptMarking B C g →
                                isSimulationExceptMarking A C (g ∘ f)
simulationsExceptMarking-comp  A B C f g (m-f , s-f) (m-g , s-g)
  =  ((m-g ∘ m-f) , λ {b} {a} b<gfa → let (y , y<fa , gy≡b) = s-g b<gfa in
                                      let (z , z<a , fz≡y) = s-f y<fa in
                                      z , z<a , cong g (fz≡y) ∙ gy≡b)

{- Two alternative characterisations of simulations -}

-- Simulations where the conclusion is ∃ rather than Σ
isSimulationWithExists : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isSimulationWithExists A B f
  = isStructurePreserving A B f
  × ∀ {b a} → b ≺⟨ B ⟩ f a → ∥ Σ[ a' ∈ ⟨ A ⟩ ] (a' ≺⟨ A ⟩ a × (f a' ≡ b)) ∥

-- Functions which preserve and reflect <, preserve markings, and whose image is downwards closed
isSimulation' : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
isSimulation' A B f
  = isStructurePreserving A B f
  × isReflecting A B f × ∀ {b a} → b ≺⟨ B ⟩ f a → ∥ Σ[ a' ∈ ⟨ A ⟩ ] (f a' ≡ b) ∥


simulationsWithExistsInjective : (A : MEWO ℓ)(B : MEWO ℓ') → (f : ⟨ A ⟩ → ⟨ B ⟩) →
                               isSimulationWithExists A B f → {x y : ⟨ A ⟩} → f x ≡ f y → x ≡ y
simulationsWithExistsInjective A B f ((mon , mark) , sim) {x} {y}
  = wf-step x y (wellfounded A x) (wellfounded A y)
    where
    wf-step : ∀ x y →
              Acc (underlyingOrder A) x →
              Acc (underlyingOrder A) y →
              f x ≡ f y → x ≡ y
    wf-step x y (acc wf-x) (acc wf-y) fx≡fy =
      extensional A x y λ c →
         (λ c<x → ∥-∥rec (truncated A c y)
                        (λ (u , u<y , fu≡fc) → subst (λ z → z ≺⟨ A ⟩ y)
                                                     (wf-step u c (wf-y u u<y) (wf-x c c<x) fu≡fc )
                                                     u<y)
                        (sim (subst (λ z → f c ≺⟨ B ⟩ z) fx≡fy (mon c<x)))) ,
         (λ c<y → ∥-∥rec (truncated A c x)
                        (λ (u , u<x , fu≡fc) → subst (λ z → z ≺⟨ A ⟩ x)
                                                     (wf-step u c (wf-x u u<x) (wf-y c c<y) fu≡fc)
                                                     u<x)
                        (sim (subst (λ z → f c ≺⟨ B ⟩ z) (sym fx≡fy) (mon c<y))))

simulationsArePrimedSimulations : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) →
                                  isSimulation A B f → isSimulation' A B f
simulationsArePrimedSimulations A B f (p , q)
  = p , simulationsReflect A B f (p , q) , λ b<fa → let (a' , _ , fa'≡b) = q b<fa in ∣ a' , fa'≡b ∣

primedSimulationsAreExistsSimulations : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) →
                                        isSimulation' A B f → isSimulationWithExists A B f
primedSimulationsAreExistsSimulations A B f (p , r , q)
  = p , λ {b} {a} b<fa → ∥-∥map (λ (a' , fa'≡b) → (a' ,
                                                  r (subst (λ z → z ≺⟨ B ⟩ f a) (sym fa'≡b) b<fa) ,
                                                  fa'≡b))
                                (q b<fa)

existsSimulationsAreSimulations : (A : MEWO ℓ)(B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) →
                                  isSimulationWithExists A B f → isSimulation A B f
existsSimulationsAreSimulations A B f sim@(p , q)
  = p , λ b<fa → ∥-∥rec (injective→simulationConclusionIsProp A B f
                          (simulationsWithExistsInjective A B f sim))
                        (idfun _)
                        (q b<fa)

{- end of alternative characterisations -}

_≤_ : (A : MEWO ℓ)(B : MEWO ℓ') → Type _
A ≤ B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩) ] (isSimulation A B f)

isProp⟨≤⟩ : (A : MEWO ℓ)(B : MEWO ℓ') → isProp (A ≤ B)
isProp⟨≤⟩ A B (f , p) (g , q) = Σ≡Prop (isPropSimulation A B) (simulationsUnique A B f g p q)

≤Refl : (A : MEWO ℓ) → A ≤ A
≤Refl A = idfun ⟨ A ⟩ , ((λ p → p) , (λ p → p)) , (λ b<a → _ , b<a , refl)

≤Refl≡ : {A B : MEWO ℓ} → A ≡ B → A ≤ B
≤Refl≡ {A = A} = J (λ B A≡B → A ≤ B) (≤Refl A)

≤Trans : (A : MEWO ℓ)(B : MEWO ℓ')(C : MEWO ℓ'') → A ≤ B → B ≤ C → A ≤ C
≤Trans A B C (f , ((m-f , M-f) , s-f)) (g , ((m-g , M-g) , s-g))
  = (g ∘ f , (((m-g ∘ m-f) , M-g ∘ M-f) , λ {b} {a} b<gfa → let (y , y<fa , gy≡b) = s-g b<gfa in
                                                            let (z , z<a , fz≡y) = s-f y<fa in
                                                            z , z<a , cong g (fz≡y) ∙ gy≡b))



equivToSimulation : (A : MEWO ℓ) (B : MEWO ℓ') (f : ⟨ A ⟩ → ⟨ B ⟩) →
                    isOrderEquiv A B f → isSimulation A B f
fst (equivToSimulation A B f p) = fst p
snd (equivToSimulation A B f (f-mono , (f-eq , (inv-mono , inv-marking)))) {b} {a} b<fa
  = invIsEq f-eq b , subst (λ z → _ ≺⟨ A ⟩ z) (retIsEq f-eq a) (inv-mono b<fa) , secIsEq f-eq b


-- The type of order equivalences
_≃ₒ_ : MEWO ℓ → MEWO ℓ' → Type (ℓ-max ℓ ℓ')
A ≃ₒ B = Σ[ f ∈ (⟨ A ⟩ → ⟨ B ⟩) ] (isOrderEquiv A B f)

≃ₒRefl : {A : MEWO ℓ} → A ≃ₒ A
≃ₒRefl = idfun _ , (((λ p → p) , (λ p → p)) , idIsEquiv _ , ((λ p → p) , (λ p → p)))

isProp⟨≃ₒ⟩ : (A : MEWO ℓ) → (B : MEWO ℓ') → isProp (A ≃ₒ B)
isProp⟨≃ₒ⟩ A B (f , f-eq) (g , g-eq)
  = Σ≡Prop (isPropOrderEquiv A B) (simulationsUnique A B f g (equivToSimulation A B f f-eq)
                                                             (equivToSimulation A B g g-eq))

idtoeqₒ : (A B : MEWO ℓ) → A ≡ B → A ≃ₒ B
idtoeqₒ A B = J (λ B p → A ≃ₒ B) (≃ₒRefl {A = A})

idtoeqₒRefl : (A : MEWO ℓ) → idtoeqₒ A A refl ≡ (≃ₒRefl {A = A})
idtoeqₒRefl A = JRefl {x = A} (λ B p → A ≃ₒ B) (≃ₒRefl {A = A})

eqtoidₒ : (A B : MEWO ℓ) → A ≃ₒ B → A ≡ B
eqtoidₒ {ℓ = ℓ} (A , (<A , MA) , axA) Y@(B , (<B , MB) , axB) (f , (f-mono , (f-eq , invf-mono)))
  = EquivJ P d (f , f-eq) ((<A , MA) , axA) f-mono invf-mono
    where
      P : (C : Type ℓ) → C ≃ ⟨ Y ⟩ → Type (ℓ-suc ℓ)
      P C e = (strC : MEWO-structure C) →
              isStructurePreserving (C , strC) Y (equivFun e) →
              isStructurePreserving Y (C , strC) (invIsEq (snd e)) →
              (C , strC) ≡ Y
      d : P B (idEquiv B)
      d ((<B' , M') , axB') m m-inv
        = cong (B ,_)
               (Σ≡Prop (λ x → isPropIsEWO (fst x))
                       (≡-× (funExt (λ x → funExt (λ y → hPropExt (fst axB' x y)
                                                                  (fst axB x y)
                                                                  (fst m {x} {y})
                                                                  (fst m-inv {x} {y}))))
                            (funExt (λ b → Σ≡Prop (λ x → isPropIsProp) (hPropExt (str (M' b))
                                                                                 (str (MB b))
                                                                                 (snd m)
                                                                                 (snd m-inv))))))

-- We adapt the proof in TypeTopology that idtoeqₒ is an equivalence from ordinals to MEWOs
-- see https://www.cs.bham.ac.uk/~mhe/TypeTopology/Published.Ordinals.OrdinalOfOrdinals.html
UAₒ : (A B : MEWO ℓ) → isEquiv (idtoeqₒ A B)
UAₒ A = nats-with-sections-are-equivs A (idtoeqₒ A) λ B → eqtoidₒ A B , λ e → isProp⟨≃ₒ⟩ A B _ e
  where
    idemp-is-id : {X : Type ℓ} {x : X} (e : (y : X) → x ≡ y → x ≡ y) (y : X) (p : x ≡ y)
                → e y (e y p) ≡ e y p
                → e y p ≡ p
    idemp-is-id {X = X} {x} e y p idemp
      = cancel-left (e x refl) (Hedberg-lemma x e y (e y p) ∙ idemp ∙ sym (Hedberg-lemma x e y p))
        where
        Hedberg-lemma : {X : Type ℓ } (x : X) (η : (y : X) → x ≡ y → x ≡ y) (y : X) (p : x ≡ y)
                      → η x refl ∙ p ≡ η y p
        Hedberg-lemma x η y = J (λ y p → η x refl ∙ p ≡ η y p) (sym (rUnit (η x refl)))
        cancel-left : {X : Type ℓ} → {x y z : X} → (p : x ≡ y){q q' : y ≡ z} →
                      p ∙ q ≡ p ∙ q' → q ≡ q'
        cancel-left p {q} {q'}
          = J (λ x p → ∀ q q' → p ∙ q ≡ p ∙ q' → q ≡ q')
              (λ q q' → subst2 _≡_ (sym (lUnit q)) (sym (lUnit q'))) p q q'

    nat-retraction-is-section : {X : Type ℓ } {A : X → Type ℓ' } (x : X) (η : ∀ y → x ≡ y → A y)
                              → ((y : X) → Σ[ s ∈ (A y → x ≡ y) ] (∀ x → η y (s x) ≡ x))
                              → ((y : X) → Σ[ s ∈ (A y → x ≡ y) ] (∀ x → s (η y x) ≡ x))
    nat-retraction-is-section {X = X} {A} x η hs y = s y , i y
      where
        s : (y : X) → A y → x ≡ y
        s y = fst (hs y)
        ηs : {y : X} (a : A y) → η y (s y a) ≡ a
        ηs {y} = snd (hs y)
        e : (y : X) → x ≡ y → x ≡ y
        e y p = s y (η y p)
        idemp : (y : X) (p : x ≡ y) → e y (e y p) ≡ e y p
        idemp y p = cong (s y) (ηs (η y p))
        i : (y : X) (p : x ≡ y) → e y p ≡ p
        i y p = idemp-is-id e y p (idemp y p)

    nats-with-sections-are-equivs : {X : Type ℓ} {A : X → Type ℓ' } (x : X) (η : ∀ y → x ≡ y → A y)
                                  → ((y : X) → Σ[ s ∈ (A y → x ≡ y) ] (∀ x → η y (s x) ≡ x))
                                  → ∀ y → isEquiv (η y)
    nats-with-sections-are-equivs {A = A} x η hs y
      = isoToIsEquiv (iso (fun e) (invr e) (invr-rightInv e) (invr-leftInv e))
        where
          open BiInvEquiv
          e : BiInvEquiv (x ≡ y) (A y)
          e = biInvEquiv (η y) (fst (hs y)) (snd (hs y))
                               (fst (nat-retraction-is-section x η hs y))
                               (snd (nat-retraction-is-section x η hs y))


isSetMEWO : isSet (MEWO ℓ)
isSetMEWO A B = isPropRetract (idtoeqₒ A B) (eqtoidₒ A B) (retIsEq (UAₒ A B)) (isProp⟨≃ₒ⟩ A B)

≤Antisymmetry : (A B : MEWO ℓ) → A ≤ B → B ≤ A → A ≡ B
≤Antisymmetry A B (f , sim-f) (g , sim-g) = eqtoidₒ A B e where
  f-iso : Iso ⟨ A ⟩ ⟨ B ⟩
  f-iso = iso f g (λ b → cong (λ z → z b)
                              (simulationsUnique B B (f ∘ g) (idfun _)
                                                     (snd (≤Trans B A B (g , sim-g) (f , sim-f)))
                                                     (snd (≤Refl B))))
                  (λ a → cong (λ z → z a)
                              (simulationsUnique A A (g ∘ f) (idfun _)
                                                     (snd (≤Trans A B A (f , sim-f) (g , sim-g)))
                                                     (snd (≤Refl A))))
  e : A ≃ₒ B
  e = f , fst sim-f , isoToIsEquiv f-iso , fst sim-g

{- Strict order -}

_↓+_ : (A : MEWO ℓ) → ⟨ A ⟩ → MEWO ℓ
A ↓+ a
  = (Σ[ y ∈ ⟨ A ⟩ ] (∥ y ≺⁺⟨ A ⟩ a ∥))
  , ((λ (y , _) (y' , _) → y ≺⟨ A ⟩ y') , (λ (x , _) → (x ≺⟨ A ⟩ a) , truncated A x a))
  , (λ x y → truncated A _ _)
  , (λ (x , ∥x<a∥) (y , ∥y<a∥) ext → Σ≡Prop (λ x → isPropPropTrunc)
      (extensional A x y (λ c → (λ c<x → fst (ext (c , ∥-∥map (λ x<a → step c<x x<a) ∥x<a∥)) c<x) ,
                                (λ c<y → snd (ext (c , ∥-∥map (λ y<a → step c<y y<a) ∥y<a∥)) c<y))))
  , (λ (y , y<a) → acc-helper y y<a (wellfounded A y))
  where
   acc-helper : ∀ y y<a → Acc (underlyingOrder A) y → Acc (λ (y , _) (y' , _) → y ≺⟨ A ⟩ y') (y , y<a)
   acc-helper y y<a (acc p) = acc λ { (z , z<a) z<y → acc-helper z z<a (p z z<y) }

↓+Eq : (A B : MEWO ℓ) → (a : ⟨ A ⟩) → (p : A ≡ B) →
        (b : ⟨ B ⟩) → fst (idtoeqₒ A B p) a ≡ b → A ↓+ a ≡ B ↓+ b
↓+Eq A B a = J (λ B p → (b : ⟨ B ⟩) → fst (idtoeqₒ A B p) a ≡ b → A ↓+ a ≡ B ↓+ b)
               (λ b q → cong (A ↓+_) (sym (cong (λ z → fst z a) (idtoeqₒRefl A)) ∙ q))

_<_ : (A B : MEWO ℓ) → Type (ℓ-suc ℓ)
A < B = Σ[ b ∈ ⟨ B ⟩ ] marked B b × (A ≡ B ↓+ b)

-- A small version of _<_
_<⁻_ : (A : MEWO ℓ)(B : MEWO ℓ') → Type (ℓ-max ℓ ℓ')
A <⁻ B = Σ[ b ∈ ⟨ B ⟩ ] marked B b × (A ≃ₒ (B ↓+ b))

<⁻To< : (A B : MEWO ℓ) → A <⁻ B → A < B
<⁻To< A B (b , mb , p) = b , mb , eqtoidₒ _ _ p

<To<⁻ : (A B : MEWO ℓ) → A < B → A <⁻ B
<To<⁻ A B (b , mb , p) = b , mb , idtoeqₒ _ _ p

segment-inclusion : (A : MEWO ℓ) → (a : ⟨ A ⟩) → isSimulationExceptMarking (A ↓+ a) A fst
segment-inclusion A a
  = (λ p → p) , (λ {b} {(a , p)} b<a → (b , ∥-∥map (TransCl-trans _ (emb b<a)) p) , b<a , refl)

segment-inclusion-markAll : (A : MEWO ℓ) → (a : ⟨ A ⟩) → isSimulation (A ↓+ a) (markAll A) fst
segment-inclusion-markAll A a
  = isSimulationExceptMarking→isSimulationMarkAll (A ↓+ a) A fst (segment-inclusion A a)

↓+Monotone≤ : (A : MEWO ℓ) (x y : ⟨ A ⟩) → (A ↓+ x) ≤ (A ↓+ y) → (∀ c → c ≺⟨ A ⟩ x → c ≺⟨ A ⟩ y)
↓+Monotone≤ A@(⟨A⟩ , (_<A_ , M) , axA) x y (f , s@((mon , mark) , sim)) c c<x = subst (_<A y) q u<y
  where
    u : ⟨ A ⟩
    u = fst (f (c , ∣ emb c<x ∣))

    u<y : u <A y
    u<y = mark {c , ∣ emb c<x ∣} c<x

    q : u ≡ c
    q = cong (λ z → z (c , ∣ emb c<x ∣))
             (simulationsExceptMarkingUnique (A ↓+ x) A (fst ∘ f) fst
                 (simulationsExceptMarking-comp (A ↓+ x) (A ↓+ y) A f fst
                                                (forgetMarkingPreservation (A ↓+ x) (A ↓+ y) f s)
                                                (segment-inclusion A y))
                 (segment-inclusion A x))

↓+Injective : (A : MEWO ℓ) (x y : ⟨ A ⟩) → (A ↓+ x) ≡ (A ↓+ y) → x ≡ y
↓+Injective A x y A↓x≡A↓y = extensional A x y λ c → (↓+Monotone≤ A x y (≤Refl≡ A↓x≡A↓y) c) ,
                                                    (↓+Monotone≤ A y x (≤Refl≡ (sym A↓x≡A↓y)) c)

isProp⟨<⟩ : (A B : MEWO ℓ) → isProp (A < B)
isProp⟨<⟩ A B (b , p) (b' , p')
  = Σ≡Prop (λ x → isProp× (isPropMarked B x) (isSetMEWO A (B ↓+ x))) b≡b'
    where
      b≡b' : b ≡ b'
      b≡b' = ↓+Injective B b b' (sym (snd p) ∙ snd p')

isProp⟨<⁻⟩ : (A B : MEWO ℓ) → isProp (A <⁻ B)
isProp⟨<⁻⟩ A B (b , p) (b' , p')
  = Σ≡Prop (λ x → isProp× (isPropMarked B x) (isProp⟨≃ₒ⟩ A (B ↓+ x))) b≡b'
    where
      b≡b' : b ≡ b'
      b≡b' = ↓+Injective B b b' (sym (eqtoidₒ A _ (snd p)) ∙ eqtoidₒ _ _ (snd p'))

iterated↓+ : (A : MEWO ℓ) → (x y : ⟨ A ⟩) → (p : ∥ y ≺⁺⟨ A ⟩ x ∥) →
             (A ↓+ x) ↓+ (y , p) ≡ A ↓+ y
iterated↓+ A x y p = ≤Antisymmetry _ _ f g
  where
    cast : ∀ {b y p q} → b ≺⁺⟨ A ⟩ y → (b , p) ≺⁺⟨ A ↓+ x ⟩ (y , q)
    cast (emb x) = emb x
    cast {q = q} (step {y = y} x ps) = step {y = y , ∥-∥map (TransCl-trans _ ps) q} x (cast ps)

    f : ((A ↓+ x) ↓+ (y , p)) ≤ (A ↓+ y)
    f = (λ ((a , r) , q) → a , ∥-∥map (TransCl-map fst (idfun _)) q) ,
        ((idfun _) , idfun _) ,
        (λ {(b , r)} {a} b<fa →
          ((b ,
            ∥-∥rec isPropPropTrunc (λ p → ∥-∥map (λ r → TransCl-trans _ r p) r) p) ,
           ∥-∥map cast r) , b<fa , Σ≡Prop (λ x → isPropPropTrunc) refl)
    g : (A ↓+ y) ≤ ((A ↓+ x) ↓+ (y , p))
    g = (λ (a , r)  →  (a , ∥-∥rec isPropPropTrunc
                      (λ p → ∥-∥map (λ r → TransCl-trans _ r p) r) p) , ∥-∥map cast r) ,
        (idfun _ , idfun _) ,
        (λ {((b , q) , r)} {a} b<fa →
          (b ,
           ∥-∥map (TransCl-map fst (idfun _)) r) ,
          b<fa , Σ≡Prop (λ x → isPropPropTrunc) (Σ≡Prop (λ x → isPropPropTrunc) refl))

↓+Monotone< : (A : MEWO ℓ) (x y : ⟨ A ⟩) → x ≺⟨ A ⟩ y → (A ↓+ x) < (A ↓+ y)
↓+Monotone< A x y p = ((x , ∣ emb p ∣)) , p , sym (iterated↓+ A y x ∣ emb p ∣)

↓+Reflects< : (A : MEWO ℓ) (x y : ⟨ A ⟩) → (A ↓+ x) < (A ↓+ y) → x ≺⟨ A ⟩ y
↓+Reflects< A x y ((b , l) , (p , r)) = subst (λ z → z ≺⟨ A ⟩ y) (sym x≡b) p
  where
    q : (A ↓+ x) ≡ (A ↓+ b)
    q = r ∙ iterated↓+ A y b l

    x≡b : x ≡ b
    x≡b = ↓+Injective A x b q

↓Accessible : (A : MEWO ℓ) (a : ⟨ A ⟩) → Acc _<_ (A ↓+ a)
↓Accessible {ℓ = ℓ} A a = acc-helper a (wellfounded A a)
  where
    acc-helper : (a : ⟨ A ⟩) → Acc (underlyingOrder A) a → Acc _<_ (A ↓+ a)
    acc-helper a (acc ih) = acc g
      where
        g : (B : MEWO ℓ) → B < (A ↓+ a) → Acc _<_ B
        g B ((b , l) , (m , p)) = subst (Acc _<_) (sym (p ∙ iterated↓+ A a b l))
                                        (acc-helper b (ih b m))

<Wellfounded : isWellFounded (_<_ {ℓ = ℓ})
<Wellfounded A = acc (λ B (a , (p , q)) → subst (Acc _<_) (sym q) (↓Accessible A a))


simulationsTransCl : (A B : MEWO ℓ) (f : ⟨ A ⟩ → ⟨ B ⟩) → isSimulation A B f →
                     {a : ⟨ A ⟩}{b : ⟨ B ⟩} → b ≺⁺⟨ B ⟩ (f a) →
                     Σ[ a' ∈ ⟨ A ⟩ ] (a' ≺⁺⟨ A ⟩ a × (f a' ≡ b))
simulationsTransCl A B f f-sim {a} {b} (emb b<fa)
  = let (a' , a'<a , fa'≡b) = snd f-sim b<fa in a' , emb a'<a , fa'≡b
simulationsTransCl A B f f-sim {a} {b} (step p ps)
  = let (a' , a'<+a , fa'≡y) = simulationsTransCl A B f f-sim ps in
    let (a'' , a''<a , fa''≡b) = snd f-sim (subst (λ z → b ≺⟨ B ⟩ z) (sym fa'≡y) p) in
    a'' , step a''<a a'<+a , fa''≡b

simulations∥TransCl∥ : (A B : MEWO ℓ) (f : ⟨ A ⟩ → ⟨ B ⟩) → isSimulation A B f →
                       {a : ⟨ A ⟩}{b : ⟨ B ⟩} → ∥ b ≺⁺⟨ B ⟩ (f a) ∥ →
                       Σ[ a' ∈ ⟨ A ⟩ ] (∥ a' ≺⁺⟨ A ⟩ a ∥ × (f a' ≡ b))
simulations∥TransCl∥ A B f f-sim {a} {b} b<+fa =
  ∥-∥rec (λ (x , _ , p) (x' , _ , p') → Σ≡Prop (λ a' → isProp× isPropPropTrunc
                                                               (isSetCarrier B (f a') b))
                                               (simulationsInjective A B f f-sim (p ∙ sym p')))
         (λ b<+fa → let (a , p , q) = simulationsTransCl A B f f-sim {a} {b} b<+fa in
                    a , ∣ p ∣ , q) b<+fa


surjectiveSimulation→Equality : (A B : MEWO ℓ) (f : ⟨ A ⟩ → ⟨ B ⟩) → isSimulation A B f →
                                ((a : ⟨ A ⟩) → marked B (f a) → marked A a) →
                                ((b : ⟨ B ⟩) → ∥ Σ[ a ∈ ⟨ A ⟩ ] (f a ≡ b) ∥) → A ≡ B
surjectiveSimulation→Equality A B f sim reflect-mark surj =
 ≤Antisymmetry _ _ (f , sim) (fst ∘ h , sim-h) where
  h : (b : ⟨ B ⟩) → Σ[ a ∈ ⟨ A ⟩ ] (f a ≡ b)
  h b = ∥-∥rec (λ { (a , p) (a' , p') → Σ≡Prop (λ x → isSetCarrier B (f x) b)
                                               (simulationsInjective A B f sim (p ∙ sym p'))})
               (idfun _) (surj b)

  hf≡id : (b : ⟨ B ⟩) → f (fst (h b)) ≡ b
  hf≡id b with h b
  ... | (a , fa≡b) = fa≡b

  sim-h : isSimulation B A (fst ∘ h)
  sim-h = (monotone , preservesMarking) , simulation where
    monotone : {x y : ⟨ B ⟩} → x ≺⟨ B ⟩ y → (fst ∘ h) x ≺⟨ A ⟩ (fst ∘ h) y
    monotone {x} {y} x<y with h x | h y
    ... | (a , fa≡x) | (a' , fa'≡y)
      = simulationsReflect A B f sim (subst2 (underlyingOrder B) (sym fa≡x) (sym fa'≡y) x<y)

    preservesMarking : ∀ {x} → marked B x → marked A (fst (h x))
    preservesMarking {x} mx with h x
    ... | (a , fa≡x) = reflect-mark a (subst (marked B) (sym fa≡x) mx)

    simulation : ∀ {b} {a} → a ≺⟨ A ⟩ fst (h b) → Σ[ b' ∈ ⟨ B ⟩ ] b' ≺⟨ B ⟩ b × (fst (h b') ≡ a)
    simulation {b} {a} a<hb with h b
    ... | (a' , fa'≡b) = f a , subst (λ z → f a ≺⟨ B ⟩ z) fa'≡b (fst (fst sim) a<hb)
                             , simulationsInjective A B f sim (hf≡id (f a))


simulationsPreserve↓ : (A B : MEWO ℓ) (f : ⟨ A ⟩ → ⟨ B ⟩) → isSimulation A B f →
                       (a : ⟨ A ⟩) → A ↓+ a ≡ B ↓+ f a
simulationsPreserve↓ A@(⟨A⟩ , (_<A_ , MA) , axA) B@(⟨B⟩ , (_<B_ , MB) , axB)
                     f f-sim@((mon , mark) , sim) a
  = surjectiveSimulation→Equality (A ↓+ a) (B ↓+ f a) g g-sim
                                  (λ x mx → simulationsReflect A B f f-sim mx) surj
    where
      g : ⟨ A ↓+ a ⟩ → ⟨ B ↓+ f a ⟩
      g (x , p) = f x , ∥-∥map (TransCl-map f mon) p

      g-sim : isSimulation (A ↓+ a) (B ↓+ f a) g
      g-sim = (mon , mon)
            , (λ {(x , x<fa)} {(b , b<a)} b<fx → let (a' , a'<a , fa'≡b) = sim b<fx in
                                                 (a' , ∥-∥map (λ b<a → step a'<a b<a) b<a) , a'<a
                                                     , Σ≡Prop (λ x → isPropPropTrunc) fa'≡b)

      surj : (b : ⟨ B ↓+ f a ⟩ ) → ∥ Σ[ x ∈ ⟨ A ↓+ a ⟩ ] (g x ≡ b) ∥
      surj (y , p) = let (x , q , r) = simulations∥TransCl∥ A B f f-sim p in
                     ∣ (x , q) , Σ≡Prop (λ x → isPropPropTrunc) r ∣


preserve↓Equiv→Simulation : (A B : MEWO ℓ) (f : ⟨ A ⟩ → ⟨ B ⟩) →
                            ((a : ⟨ A ⟩) → (A ↓+ a) ≃ₒ (B ↓+ f a)) →
                            isMarkingPreserving A B f → isSimulation A B f
preserve↓Equiv→Simulation {ℓ = ℓ} A B f e f-pres-mark
  = ((λ {x} {y} x<y → monUpTo y (∥TransCl∥-wellfounded (wellfounded A) y) x x<y) , f-pres-mark)
  , λ {b} {a} b<fa → simulUpTo a ((∥TransCl∥-wellfounded (wellfounded A) a)) b b<fa
   where
    ∥≺⁺⟨A⟩∥ = λ x y → ∥ x ≺⁺⟨ A ⟩ y ∥

    isSimulationUpTo : (x : ⟨ A ⟩) → (f : ⟨ A ⟩ → ⟨ B ⟩) → Type ℓ
    isSimulationUpTo x f = isSimulationExceptMarking (A ↓+ x) B (f ∘ fst)

    mutual
      simUpTo : (x : ⟨ A ⟩) → Acc ∥≺⁺⟨A⟩∥ x → isSimulationUpTo x f
      simUpTo x (acc s)
        = ((λ { {(a , p)} {(b , q)} a<b → monUpTo b (s b q) a a<b }) ,
           (λ {b} {(a , a<x)} b<fa → let (a' , a'<a , fa'≡b) = simulUpTo a (s a a<x) b b<fa in
                                     (a' , ∥-∥map (λ a<x → step a'<a a<x) a<x) ,  a'<a , fa'≡b))

      monUpTo : (x : ⟨ A ⟩) → Acc ∥≺⁺⟨A⟩∥ x → (y : ⟨ A ⟩) → y ≺⟨ A ⟩ x → f y ≺⟨ B ⟩ f x
      monUpTo x s y y<x = subst (λ z → z ≺⟨ B ⟩ f x)
                                (cong (λ z → z (y , ∣ emb y<x ∣)) e'≡f)
                                (mark y<x)
        where
          e' = fst (e x)

          mark : isMarkingPreserving (A ↓+ x) (B ↓+ f x) e'
          mark = snd (fst (snd (e x)))

          e'≡f : fst ∘ e' ≡ f ∘ fst
          e'≡f = simulationsExceptMarkingUnique (A ↓+ x) B (fst ∘ e') (f ∘ fst)
                  (simulationsExceptMarking-comp (A ↓+ x) (B ↓+ f x) B e' fst
                  (forgetMarkingPreservation (A ↓+ x) (B ↓+ f x) e'
                                             (equivToSimulation (A ↓+ x) (B ↓+ f x) e' (snd (e x))))
                  (segment-inclusion B (f x)))
                  (simUpTo x s)

      simulUpTo : (x : ⟨ A ⟩) → Acc ∥≺⁺⟨A⟩∥ x → (y : ⟨ B ⟩) → y ≺⟨ B ⟩ f x →
                  Σ[ x' ∈ ⟨ A ⟩ ] (x' ≺⟨ A ⟩ x × (f x' ≡ y))
      simulUpTo x s y y<fx = fst (e⁻¹ (y , ∣ emb y<fx ∣)) ,
                             mark y<fx ,
                             (sym (cong (λ z → z (e⁻¹ (y , ∣ emb y<fx ∣))) e'≡f)
                               ∙ cong fst (secIsEq (fst (snd (snd (e x)))) (y , ∣ emb y<fx ∣)))
        where
          e' = fst (e x)
          e⁻¹ = invIsEq (fst (snd (snd (e x))))

          mark : isMarkingPreserving (B ↓+ f x) (A ↓+ x) e⁻¹
          mark = snd (snd (snd (snd (e x))))

          e'≡f : fst ∘ e' ≡ f ∘ fst
          e'≡f = simulationsExceptMarkingUnique (A ↓+ x) B (fst ∘ e') (f ∘ fst)
                  (simulationsExceptMarking-comp (A ↓+ x) (B ↓+ f x) B e' fst
                  (forgetMarkingPreservation (A ↓+ x) (B ↓+ f x) e'
                                             (equivToSimulation (A ↓+ x) (B ↓+ f x) e' (snd (e x))))
                  (segment-inclusion B (f x)))
                  (simUpTo x s)


preserve↓→Simulation : (A B : MEWO ℓ) (f : ⟨ A ⟩ → ⟨ B ⟩) → ((a : ⟨ A ⟩) → A ↓+ a ≡ B ↓+ f a) →
                       isMarkingPreserving A B f → isSimulation A B f
preserve↓→Simulation A B f e = preserve↓Equiv→Simulation A B f (λ a → idtoeqₒ _ _ (e a))

<∘≤-in-< : (X Y Z : MEWO ℓ) → X < Y → Y ≤ Z → X < Z
<∘≤-in-< X Y Z (y , my , X≡Y↓+y) (f , sim-f) = f y , snd (fst (sim-f)) my ,
                                               X≡Y↓+y ∙ simulationsPreserve↓ Y Z f sim-f y

markAllInitialSegmentsTheSame : (X : MEWO ℓ) → (x : ⟨ X ⟩) → X ↓+ x ≡ markAll X ↓+ x
markAllInitialSegmentsTheSame X x = ≤Antisymmetry _ _ X↓+x≤markAllX↓+x markAllX↓+x≤X↓+x
  where
    X↓+x≤markAllX↓+x : (X ↓+ x) ≤ (markAll X ↓+ x)
    X↓+x≤markAllX↓+x = (idfun _) , ((λ p → p) , λ p → p) , (λ {b} b<a → b , b<a , refl)

    markAllX↓+x≤X↓+x : (markAll X ↓+ x) ≤ (X ↓+ x)
    markAllX↓+x≤X↓+x = (idfun _) , ((λ p → p) , λ p → p) , (λ {b} b<a → b , b<a , refl)


<-to-<-withoutMarking : (X Y : MEWO ℓ) → X < Y → X ≤ markAll Y
<-to-<-withoutMarking X Y (y , (_ , X≡Y↓+y)) = subst (_≤ markAll Y) (sym X≡Y↓+y) Y↓+y≤markAllY
  where
    Y↓+y≤markAllY : (Y ↓+ y) ≤ markAll Y
    Y↓+y≤markAllY = fst , isSimulationExceptMarking→isSimulationMarkAll (Y ↓+ y) Y fst
                                                                        (segment-inclusion Y y)
<-transWithoutMarking : (X Y Z : MEWO ℓ) → X < Y → Y < Z → X < markAll Z
<-transWithoutMarking X Y Z (y , (_ , X≡Y↓+y)) (z , (_ , Y≡Z↓+z)) = z' , tt* , X≡markAllZ↓+z'
  where
    z' : ⟨ Z ⟩
    z' = fst (subst ⟨_⟩ Y≡Z↓+z y)
    z'<+z : ∥ z' ≺⁺⟨ Z ⟩ z ∥
    z'<+z = snd (subst ⟨_⟩ Y≡Z↓+z y)

    X≡markAllZ↓+z' : X ≡ (markAll Z ↓+ z')
    X≡markAllZ↓+z' = X≡Y↓+y ∙ t Y≡Z↓+z ∙ iterated↓+ Z z z' z'<+z ∙ markAllInitialSegmentsTheSame Z z'
      where
        t : (q : Y ≡ (Z ↓+ z)) → (Y ↓+ y) ≡ ((Z ↓+ z) ↓+ subst ⟨_⟩ q y)
        t = J (λ Z' q → (Y ↓+ y) ≡ (Z' ↓+ subst ⟨_⟩ q y))
              (subst (λ r → (Y ↓+ y) ≡ (Y ↓+ r)) (sym (substRefl {B = ⟨_⟩} {x = Y} y)) refl)
