
----------------------------------------------------------------------------------------------------
-- Covered Marked Extensional and Wellfounded Orders
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module MEWO.Covered where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Induction.WellFounded
  renaming (WellFounded to isWellFounded)

open import PropTrunc

open import General-Properties
open import Relation.Closure

open import MEWO.Base

{- Covered MEWOs -}

isCovered : MEWO ℓ → Type ℓ
isCovered A = (x : ⟨ A ⟩) → ∥ (Σ[ y ∈ ⟨ A ⟩ ] marked A y × x ≺̂*⟨ A ⟩ y) ∥

isProp⟨isCovered⟩ : (A : MEWO ℓ) → isProp (isCovered A)
isProp⟨isCovered⟩ A = isPropΠ (λ x → isPropPropTrunc)

initialSegmentsCovered : (A : MEWO ℓ) → (a : ⟨ A ⟩) → isCovered (A ↓+ a)
initialSegmentsCovered A a (x , p) = ∥-∥map f p where
  f : {x : ⟨ A ⟩}{p : ∥ x ≺⁺⟨ A ⟩ a ∥} → x ≺⁺⟨ A ⟩ a →
      Σ[ y ∈ ⟨ A ↓+ a ⟩ ] (fst y ≺⟨ A ⟩ a × ((x , p) ≺̂*⟨ A ↓+ a ⟩ y) )
  f {x} {p} (emb x<a) = (x , p) , x<a , done
  f {x} {p} (step x<y y<*a) = let (y₀ , y₀<a , y<*y₀) = f {p = ∣ y<*a ∣} y<*a in
                              y₀ , y₀<a , step x<y y<*y₀

{- Principality -}

IsPartialSimulation : (A B : MEWO ℓ) → (f : (x : ⟨ A ⟩) → marked A x → ⟨ B ⟩) → Type (ℓ-suc ℓ)
IsPartialSimulation A B f = (x : ⟨ A ⟩) → (mx : marked A x) →
                            (A ↓+ x ≡ B ↓+ (f x mx)) × marked B (f x mx)

IsPartialSimulation⁻ : (A : MEWO ℓ)(B : MEWO ℓ') → (f : (x : ⟨ A ⟩) → marked A x → ⟨ B ⟩) → Type (ℓ-max ℓ ℓ')
IsPartialSimulation⁻ A B f = (x : ⟨ A ⟩) → (mx : marked A x) →
                             ((A ↓+ x) ≃ₒ (B ↓+ (f x mx))) × marked B (f x mx)

_≤ₚ_ : (A B : MEWO ℓ) → Type (ℓ-suc ℓ)
A ≤ₚ B = Σ[ f ∈ ((x : ⟨ A ⟩) → marked A x → ⟨ B ⟩) ] (IsPartialSimulation A B f)

isPropIsPartialSimulation : (A B : MEWO ℓ) → (f : (x : ⟨ A ⟩) → marked A x → ⟨ B ⟩) →
                            isProp (IsPartialSimulation A B f)
isPropIsPartialSimulation A B f = isPropΠ2 (λ x mx → isProp× (isSetMEWO _ _)
                                                             (isPropMarked B (f x mx)))

≤ₚCharacterisationTo : (A B : MEWO ℓ) → A ≤ₚ B → (x : ⟨ A ⟩) → (marked A x) →
                       ∥ Σ[ y ∈ ⟨ B ⟩ ] (A ↓+ x ≡ B ↓+ y) × marked B y ∥
≤ₚCharacterisationTo A B (f , p) x mx = ∣ (f x mx , p x mx) ∣

abstract
 ≤ₚCharacterisationFrom : (A B : MEWO ℓ) → ((x : ⟨ A ⟩) → (marked A x) →
                          ∥ Σ[ y ∈ ⟨ B ⟩ ] (A ↓+ x ≡ B ↓+ y) × marked B y ∥) → A ≤ₚ B
 ≤ₚCharacterisationFrom A B g = (λ x mx → fst (g' x mx)) , λ x mx → snd (g' x mx) where
  g' : (x : ⟨ A ⟩) → (marked A x) → Σ[ y ∈ ⟨ B ⟩ ] (A ↓+ x ≡ B ↓+ y) × (marked B y)
  g' x mx = ∥-∥rec (λ (y , (p , _)) (y' , (p' , _)) → Σ≡Prop (λ b → isProp× (isSetMEWO _ _)
                                                                            (isPropMarked B b))
                                                             (↓+Injective B y y' (sym p ∙ p')))
                   (idfun _) (g x mx)


 isProp⟨≤ₚ⟩ : (A B : MEWO ℓ) → isProp (A ≤ₚ B)
 isProp⟨≤ₚ⟩ A B = isPropRetract (≤ₚCharacterisationTo A B)
                               (≤ₚCharacterisationFrom A B)
                               (λ { (f , p) → Σ≡Prop (isPropIsPartialSimulation A B)
                                                     (funExt (λ x → funExt (λ mx → refl))) })
                               (isPropΠ2 (λ x mx → isPropPropTrunc))

≤ₚCharacterisation : (A B : MEWO ℓ) →
                     A ≤ₚ B ≡
                     ((x : ⟨ A ⟩) → (marked A x) → ∥ Σ[ y ∈ ⟨ B ⟩ ] (A ↓+ x ≡ B ↓+ y) × marked B y ∥)
≤ₚCharacterisation A B = hPropExt (isProp⟨≤ₚ⟩ A B) (isPropΠ2 (λ x mx → isPropPropTrunc))
                                  (≤ₚCharacterisationTo A B) (≤ₚCharacterisationFrom A B)


restrictPartial : (A B : MEWO ℓ) → A ≤ B → A ≤ₚ B
restrictPartial A B (f , p) = (λ x _ → f x) ,
                              λ x mx → (simulationsPreserve↓ A B f p x , snd (fst p) mx)

isPrincipal : MEWO ℓ → Type (ℓ-suc ℓ)
isPrincipal {ℓ = ℓ} A = (Y : MEWO ℓ) → A ≤ₚ Y → A ≤ Y

isPrincipal→restrictPartialEquiv : (A : MEWO ℓ) → isPrincipal A → (Y : MEWO ℓ) →
                                   isEquiv (restrictPartial A Y)
isPrincipal→restrictPartialEquiv A principal Y = isoToIsEquiv (iso (restrictPartial A Y)
                                                                   (principal Y)
                                                                   (λ x → isProp⟨≤ₚ⟩ A Y _ _)
                                                                   (λ y → isProp⟨≤⟩ A Y _ _))

restrictPartialEquiv→isPrincipal : (A : MEWO ℓ) → ((Y : MEWO ℓ) →
                                   isEquiv (restrictPartial A Y)) → isPrincipal A
restrictPartialEquiv→isPrincipal A equiv Y = invIsEq (equiv Y)

covered : MEWO ℓ → MEWO ℓ
covered A = (Σ[ x ∈ ⟨ A ⟩ ] ∥ Σ[ y ∈ ⟨ A ⟩ ] (marked A y × x ≺̂*⟨ A ⟩ y) ∥) ,
              ((λ (x , _) (y , _) → x ≺⟨ A ⟩ y) , (λ (x , _) → marked A x , isPropMarked A x)) ,
              (λ a b → truncated A _ _) ,
              ext ,
              (λ x → acc-lemma x (wellfounded A (fst x)))
    where
      acc-lemma : ∀ x → Acc (underlyingOrder A) (fst x) → Acc (λ (x , _) (y , _) → x ≺⟨ A ⟩ y) x
      acc-lemma x (acc s) = acc (λ y y<x → acc-lemma y (s (fst y) y<x))
      ext : isExtensional (λ (x , _) (y , _) → x ≺⟨ A ⟩ y)
      ext x y ext
        = Σ≡Prop (λ _ → isPropPropTrunc)
                 (extensional A _ _
                              (λ c → (λ c<x → fst (ext (c , ∥-∥map (λ (p , mp , x<p) → p , mp ,
                                                                                        step c<x x<p)
                                                                   (snd x)))
                                              c<x) ,
                                     (λ c<y → snd (ext (c , ∥-∥map (λ (p , mp , y<p) → p , mp ,
                                                                                        step c<y y<p)
                                                               (snd y)))
                                              c<y)))

coveredA≤A : (A : MEWO ℓ) → covered A ≤ A
coveredA≤A A = fst , (idfun _ , idfun _) ,
               (λ {b} {a} b<fa → (b , ∥-∥map (λ (p , mp , a<p) → (p , mp , step b<fa a<p)) (snd a)) ,
                                  b<fa , refl)


principal→covered : (A : MEWO ℓ) → isPrincipal A → isCovered A
principal→covered {ℓ = ℓ} A principal x = subst (λ z → ∥ Σ[ y ∈ ⟨ A ⟩ ]
                                                (marked A y × z ≺̂*⟨ A ⟩ y) ∥)
                                                (sym (tr⁻¹≡fst (tr x)) ∙ tr⁻¹tr x)
                                                (snd (tr x))
 where
  coveredA : MEWO ℓ
  coveredA = covered A

  A≤ₚcoveredA : A ≤ₚ coveredA
  A≤ₚcoveredA = (λ x mx → x , ∣ x , (mx , done) ∣) ,
                (λ x mx → (≤Antisymmetry _ _ (f x mx) (g x mx) , mx))
    where
      cast : ∀ {b y p q} → b ≺⁺⟨ A ⟩ y → (b , p) ≺⁺⟨ coveredA ⟩ (y , q)
      cast (emb x) = emb x
      cast {p = p} {q = q} (step {y = y} b<y ps)
        = step {y = y ,
                    ∥-∥map (λ (z , mz , b<*z) → z , mz ,
                                                ReflTransCl-trans _ (Trans→ReflTrans _ ps) b<*z) q}
               b<y (cast ps)

      f : ∀ x mx → (A ↓+ x) ≤ (coveredA ↓+ (x , ∣ x , mx , done ∣))
      f x mx = (λ (y , y<+x) → (y , ∥-∥map (λ y<+x → x , mx , Trans→ReflTrans _ y<+x) y<+x) ,
                               ∥-∥map (λ y<+x → cast y<+x) y<+x) ,
                               (idfun _ , idfun _) ,
                               (λ {(b , p)} {a} b<fa → (fst b ,
                                                        ∥-∥map (TransCl-map fst (idfun _)) p ) ,
                                                        b<fa ,
                                                        Σ≡Prop (λ x → isPropPropTrunc)
                                                               (Σ≡Prop (λ x → isPropPropTrunc) refl))

      g : ∀ x mx → (coveredA ↓+ (x , ∣ x , mx , done ∣)) ≤ (A ↓+ x)
      g x mx = (λ (y , p) → fst y , ∥-∥map (TransCl-map fst (idfun _)) p) ,
               (idfun _ , idfun _) ,
               (λ {(b , b<+x)} {(a , a<+x)} b<fa → ((b , ∥-∥map (λ (z , mz , a<*z) → z , mz ,
                                                                                     step b<fa a<*z)
                                                         (snd a)) ,
                                                    ∥-∥map cast b<+x) ,
                                                    b<fa ,
                                                    Σ≡Prop (λ x → isPropPropTrunc) refl)

  allCovered : A ≡ coveredA
  allCovered = ≤Antisymmetry A coveredA (principal coveredA A≤ₚcoveredA) (coveredA≤A A)

  tr : ⟨ A ⟩ → ⟨ coveredA ⟩
  tr = fst (idtoeqₒ _ _ allCovered)

  tr⁻¹ : ⟨ coveredA ⟩ → ⟨ A ⟩
  tr⁻¹ = invIsEq (fst (snd (snd (idtoeqₒ _ _ allCovered))))

  tr⁻¹≡fst : (x : ⟨ coveredA ⟩) → tr⁻¹ x ≡ fst x
  tr⁻¹≡fst x = transportRefl _ ∙ transportRefl _ ∙ transportRefl _ ∙
               transportRefl _ ∙ transportRefl _ ∙ transportRefl _

  tr⁻¹tr : (x : ⟨ A ⟩) → tr⁻¹ (tr x) ≡ x
  tr⁻¹tr x = retIsEq (fst (snd (snd (idtoeqₒ _ _ allCovered)))) x

abstract
  ≤CharacterisationFrom : (A B : MEWO ℓ) → ((x : ⟨ A ⟩) →
                            ∥ Σ[ y ∈ ⟨ B ⟩ ] (A ↓+ x ≡ B ↓+ y) × (marked A x → marked B y) ∥) →
                            A ≤ B
  ≤CharacterisationFrom A B g = (fst ∘ g') ,
                                preserve↓→Simulation A B (fst ∘ g')
                                                     (λ x → fst (snd (g' x)))
                                                     (λ {x} mx → snd (snd (g' x)) mx)
   where
     g' : (x : ⟨ A ⟩) → Σ[ y ∈ ⟨ B ⟩ ] (A ↓+ x ≡ B ↓+ y) × (marked A x → marked B y)
     g' x =
       ∥-∥rec (λ (y , (p , _)) (y' , (p' , _)) → Σ≡Prop (λ x → isProp× (isSetMEWO _ _)
                                                                       (isProp→ (isPropMarked B x)))
                                                        (↓+Injective B y y' (sym p ∙ p')))
              (idfun _) (g x)


covered→principal : (A : MEWO ℓ) → isCovered A → isPrincipal A
covered→principal A cover Y (f , psim) =
 ≤CharacterisationFrom A Y
                       (λ x → ∥-∥rec isPropPropTrunc (λ (p , mp , x<p) → ∣ h x p mp x<p ∣) (cover x))
  where
    h : (x : ⟨ A ⟩) → (p : ⟨ A ⟩) → marked A p → x ≺̂*⟨ A ⟩ p →
        Σ[ y ∈ ⟨ Y ⟩ ] ((A ↓+ x) ≡ (Y ↓+ y)) × (marked A x → marked Y y)
    h x .x mx done = (f x mx) , fst (psim x mx) , λ _ → snd (psim x mx)
    h x p mp (step {y = x'} x<x' x'<*p) = (y , A↓x≡Y↓y , M)
      where
        tr : ⟨ A ↓+ p ⟩ → ⟨ Y ↓+ f p mp ⟩
        tr = fst (idtoeqₒ _ _ (fst (psim p mp)))

        y : ⟨ Y ⟩
        y = fst (tr (x , ∣ stepT _ x<x' x'<*p ∣))

        y<*p : ∥ y ≺⁺⟨ Y ⟩ f p mp ∥
        y<*p = snd (tr (x , ∣ stepT _ x<x' x'<*p ∣))

        A↓x≡Y↓y : A ↓+ x ≡ Y ↓+ y
        A↓x≡Y↓y = sym (iterated↓+ A p x ∣ stepT _ x<x' x'<*p ∣) ∙
                  A↓p↓x≡Y↓fp↓y ∙
                  iterated↓+ Y (f p mp) y y<*p
          where
            A↓p↓x≡Y↓fp↓y : ((A ↓+ p) ↓+ (x , _)) ≡ ((Y ↓+ f p mp) ↓+ (y , _))
            A↓p↓x≡Y↓fp↓y = ↓+Eq (A ↓+ p) (Y ↓+ f p mp) (x , _) (fst (psim p mp)) (y , _) refl

        y≡fx : (mx : marked A x) → y ≡ f x mx
        y≡fx mx = ↓+Injective Y y (f x mx) (sym A↓x≡Y↓y ∙ fst (psim x mx))

        M : marked A x → marked Y y
        M mx = subst (marked Y) (sym (y≡fx mx)) (snd (psim x mx))


MEWOcov : (ℓ : Level) → Type (ℓ-suc ℓ)
MEWOcov ℓ = Σ[ A ∈ (MEWO ℓ) ] isCovered A

_<c_ : MEWOcov ℓ → MEWOcov ℓ → Type (ℓ-suc ℓ)
(A , _) <c (B , _) = A < B

_≤c_ : MEWOcov ℓ → MEWOcov ℓ → Type ℓ
(A , _) ≤c (B , _) = A ≤ B

coveredWellfounded : isWellFounded (_<c_ {ℓ = ℓ})
coveredWellfounded {ℓ = ℓ} X = lemma X (<Wellfounded (fst X))
  where
    lemma : (X : MEWOcov ℓ) → Acc _<_ (fst X) → Acc _<c_ X
    lemma X (acc s) = acc (λ Y Y<X → lemma Y (s (fst Y) Y<X))

coveredExtensional : isExtensional (_<c_ {ℓ = ℓ})
coveredExtensional {ℓ = ℓ} (A , cA) (B , cB) exteq =
  Σ≡Prop isProp⟨isCovered⟩ (≤Antisymmetry A B (oneway A B cA cB (fst ∘ exteq))
                                             (oneway B A cB cA (snd ∘ exteq)))
  where
    oneway : (A B : MEWO ℓ) → (cA : isCovered A) → (cB : isCovered B) →
             ((Z : MEWOcov ℓ) → Σ[ a ∈ ⟨ A ⟩ ] (marked A a × (fst Z ≡ (A ↓+ a))) →
             Σ[ b ∈ ⟨ B ⟩ ] (marked B b × (fst Z ≡ (B ↓+ b)))) → A ≤ B
    oneway A B cA cB hyp = covered→principal A cA B A≤ₚB
      where
        singletonContractHyp : ((a : ⟨ A ⟩) →  marked A a →
                               Σ[ b ∈ ⟨ B ⟩ ] (marked B b × ((A ↓+ a) ≡ (B ↓+ b))))
        singletonContractHyp a ma  = hyp ((A ↓+ a) , initialSegmentsCovered A a) (a , ma , refl)

        A≤ₚB : A ≤ₚ B
        A≤ₚB = (λ a ma → fst (singletonContractHyp a ma)) ,
               (λ a ma → snd (snd (singletonContractHyp a ma)) ,
               fst (snd (singletonContractHyp a ma)))


isEWO⟨MEWOcov⟩ : isEWO (_<c_ {ℓ = ℓ})
isEWO⟨MEWOcov⟩ = (λ A B → isProp⟨<⟩ (fst A) (fst B)) , coveredExtensional , coveredWellfounded

MEWOcov-as-MEWO : (ℓ : Level) → MEWO (ℓ-suc ℓ)
MEWOcov-as-MEWO ℓ = MEWOcov ℓ , (_<c_ , λ _ → Unit* , isPropUnit*) , isEWO⟨MEWOcov⟩

isSet⟨MEWOcov⟩ : isSet (MEWOcov ℓ)
isSet⟨MEWOcov⟩ = isSetΣSndProp isSetMEWO isProp⟨isCovered⟩

↓+-simulation : (X : MEWO ℓ) → isSimulation X (MEWOcov-as-MEWO ℓ)
                                            (λ x → X ↓+ x , initialSegmentsCovered X x)
↓+-simulation X = ((↓+Monotone< X _ _ , λ p → lift tt) ,
                  (λ {b} {a} ((a' , a'<+a) , ma' , b=X↓a↓a') → a' , ma' ,
                                                               Σ≡Prop isProp⟨isCovered⟩
                                                                      (sym (b=X↓a↓a' ∙
                                                                            iterated↓+ X a a'
                                                                                       a'<+a))))
