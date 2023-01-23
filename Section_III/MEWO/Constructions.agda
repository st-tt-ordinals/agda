
----------------------------------------------------------------------------------------------------
-- Constructions on (Covered) Marked Extensional and Wellfounded Orders
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module MEWO.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (typ; str)

open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Induction.WellFounded
  renaming (WellFounded to isWellFounded)
open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.HITs.SetQuotients as Q

open import PropTrunc

open import Iff
open import General-Properties
open import Relation.Closure

open import MEWO.Base
open import MEWO.Covered

open import Abstract.ZerSucLim

{- Successor -}

succ-< : (A : MEWO ℓ) → ⟨ A ⟩ ⊎ Unit → ⟨ A ⟩ ⊎ Unit → Type ℓ
succ-< A (inl x) (inl y) = x ≺⟨ A ⟩ y
succ-< A (inl x) (inr _) = marked A x
succ-< A (inr _) y = ⊥*

isProp⟨succ-<⟩ : (A : MEWO ℓ) → isPropValued (succ-< A)
isProp⟨succ-<⟩ A (inl x) (inl y) = truncated A x y
isProp⟨succ-<⟩ A (inl x) (inr _) = isPropMarked A x
isProp⟨succ-<⟩ A (inr x) y = isProp⊥*

isExtensional⟨succ-<⟩ : (A : MEWO ℓ) → isCovered A → isExtensional (succ-< A)
isExtensional⟨succ-<⟩ A cov (inl x) (inl y) ext
  = cong inl (extensional A x y λ c → ext (inl c))
isExtensional⟨succ-<⟩ A cov (inl x) (inr tt) ext
  = ∥-∥rec (isSet⊎ (isSetCarrier A) isSetUnit _ _)
          (λ (p , mp , x<*p) → ⊥.rec (wellfounded→irreflexive (TransClWellfounded _ (wellfounded A)) _
                                                              (stepT _ (snd (ext (inl p)) mp) x<*p)))
          (cov x)
isExtensional⟨succ-<⟩ A cov (inr tt) (inl y) ext
  = ∥-∥rec (isSet⊎ (isSetCarrier A) isSetUnit _ _)
          (λ (p , mp , y<*p) → ⊥.rec (wellfounded→irreflexive (TransClWellfounded _ (wellfounded A)) _
                                                              (stepT _ (fst (ext (inl p)) mp) y<*p)))
          (cov y)
isExtensional⟨succ-<⟩ A cov (inr tt) (inr tt) ext = refl

isWellFounded⟨succ-<⟩ : (A : MEWO ℓ) → isWellFounded (succ-< A)
isWellFounded⟨succ-<⟩ A (inl y) = acc-lemma y (wellfounded A y)
  where
    acc-lemma : ∀ y → Acc (underlyingOrder A) y → Acc (succ-< A) (inl y)
    acc-lemma y (acc s) = acc λ { (inl z) z<y → acc-lemma z (s z z<y) }
isWellFounded⟨succ-<⟩ A (inr x) = acc λ { (inl y) my → acc-lemma y (wellfounded A y) }
  where
    acc-lemma : ∀ y → Acc (underlyingOrder A) y → Acc (succ-< A) (inl y)
    acc-lemma y (acc s) = acc λ { (inl z) z<y → acc-lemma z (s z z<y) }

succ-marking : (A : MEWO ℓ) → ⟨ A ⟩ ⊎ Unit → hProp ℓ
succ-marking A (inl x) = ⊥* , isProp⊥*
succ-marking A (inr _) = Unit* , isPropUnit*

succ : (A : MEWO ℓ) → isCovered A → MEWO ℓ
succ A cov = (⟨ A ⟩ ⊎ Unit) ,
             (succ-< A , succ-marking A) ,
             isProp⟨succ-<⟩ A , isExtensional⟨succ-<⟩ A cov , isWellFounded⟨succ-<⟩ A

inl<inr-lemma : (A : MEWO ℓ) → (cov : isCovered A) → (a : ⟨ A ⟩) → ∥ inl a ≺⁺⟨ succ A cov ⟩ inr tt ∥
inl<inr-lemma A cov a
  = ∥-∥map (λ (p , mp , a<*p) → ReflTransTransCl-trans _
                                                      (ReflTransCl-map inl (idfun _) a<*p) (emb mp))
          (cov a)

succCovered : (A : MEWO ℓ) → (cov : isCovered A) → isCovered (succ A cov)
succCovered A cov (inr tt) = ∣ inr tt , tt* , done ∣
succCovered A cov (inl x)
  = ∥-∥map (λ inlx<+inrtt → inr tt , tt* , Trans→ReflTrans _ inlx<+inrtt) (inl<inr-lemma A cov x)


csucc : MEWOcov ℓ → MEWOcov ℓ
csucc (A , cov) = (succ A cov , succCovered A cov)

↓+inr : (A : MEWO ℓ) → (cov : isCovered A) → succ A cov ↓+ inr tt ≡ A
↓+inr A cov = ≤Antisymmetry _ _ sA↓inr≤A A≤sA↓inr
  where
   A≤sA↓inr : A ≤ (succ A cov ↓+ inr tt)
   A≤sA↓inr = (λ a → inl a ,
              inl<inr-lemma A cov a) ,
              ((λ p → p) , λ p → p) ,
              (λ { {inl a , p} {b} a<b → a , a<b , Σ≡Prop (λ x → isPropPropTrunc) refl })

   sA↓inr≤A : (succ A cov ↓+ inr tt) ≤ A
   sA↓inr≤A = f , ((λ {x} {y} → mono {x} {y}) , λ {x} → mark {x}) , sim
    where
     f : ⟨ succ A cov ↓+ inr tt ⟩ → ⟨ A ⟩
     f (inl a , p) = a
     f (inr x , p) =
       ⊥.rec (wellfounded→irreflexive (∥TransCl∥-wellfounded (isWellFounded⟨succ-<⟩ A)) _ p)

     mono : isMonotone (succ A cov ↓+ inr tt) A f
     mono {inl x , p} {inl y , q} x<y = x<y
     mono {inl x , p} {inr tt , q} x<y =
       ⊥.rec (wellfounded→irreflexive (∥TransCl∥-wellfounded (isWellFounded⟨succ-<⟩ A)) _ q)

     mark : isMarkingPreserving (succ A cov ↓+ inr tt) A f
     mark {inl x , p} mx = mx

     sim : {b : ⟨ A ⟩} {a : ⟨ succ A cov ↓+ inr tt ⟩} → b ≺⟨ A ⟩ (f a) →
           Σ ⟨ succ A cov ↓+ inr tt ⟩ (λ a' → a' ≺⟨ succ A cov ↓+ inr tt ⟩ a × (f a' ≡ b))
     sim {b} {inl a , p} b<a = (inl b , ∥-∥map (λ p → TransCl-trans _ (emb b<a) p) p) , b<a , refl
     sim {b} {inr tt , p} =
       ⊥.rec (wellfounded→irreflexive (∥TransCl∥-wellfounded (isWellFounded⟨succ-<⟩ A)) _ p)

¬inr<+inl : (A : MEWO ℓ) → (a : ⟨ A ⟩) → TransCl (succ-< A) (inr tt) (inl a) → ⊥
¬inr<+inl A a (emb ())
¬inr<+inl A a (step () ps)


↓+inl : (A : MEWO ℓ) → (cov : isCovered A) → (a : ⟨ A ⟩) → succ A cov ↓+ inl a ≡ A ↓+ a
↓+inl A cov a = ≤Antisymmetry _ _ sA↓inla≤A↓a A↓a≤sA↓inla
  where
    cast : ∀ {x y} → (inl x) ≺⁺⟨ succ A cov ⟩ (inl y) → x ≺⁺⟨ A ⟩ y
    cast (emb p) = emb p
    cast (step {y = inl y} p ps) = step p (cast ps)
    cast (step {y = inr tt} p ps) = ⊥.rec (¬inr<+inl A _ ps)

    sA↓inla≤A↓a : (succ A cov ↓+ inl a) ≤ (A ↓+ a)
    sA↓inla≤A↓a = f , ((λ {x} {y} → mono {x} {y}) , λ {x} → mark {x}) , sim
      where
        f : ⟨ succ A cov ↓+ inl a ⟩ → ⟨ A ↓+ a ⟩
        f (inl x , p) = x , ∥-∥map cast p
        f (inr tt , p) = ⊥.rec (∥-∥rec isProp⊥ (¬inr<+inl A a) p)

        mono : isMonotone (succ A cov ↓+ inl a) (A ↓+ a) f
        mono {inl x , p} {inl y , q} x<y = x<y
        mono {inl x , p} {inr tt , q} x<y = ⊥.rec (∥-∥rec isProp⊥ (¬inr<+inl A a) q)

        mark : isMarkingPreserving (succ A cov ↓+ inl a) (A ↓+ a) f
        mark {inl x , p} mx = mx

        sim : {b : ⟨ A ↓+ a ⟩} {x : ⟨ succ A cov ↓+ inl a ⟩} → b ≺⟨ A ↓+ a ⟩ (f x) →
              Σ ⟨ succ A cov ↓+ inl a ⟩ (λ x' → x' ≺⟨ succ A cov ↓+ inl a ⟩ x × (f x' ≡ b))
        sim {b , p} {inl x , q} b<x =
          (inl b , ∥-∥map (λ q → step b<x q) q) , b<x , Σ≡Prop (λ x → isPropPropTrunc) refl
        sim {b , p} {inr tt , q} b<x = ⊥.rec (∥-∥rec isProp⊥ (¬inr<+inl A a) q)

    A↓a≤sA↓inla : (A ↓+ a) ≤ (succ A cov ↓+ inl a)
    A↓a≤sA↓inla = (λ (x , p) → inl x ,
                  ∥-∥map (TransCl-map inl (idfun _)) p) ,
                  ((λ p → p) , (λ p → p)) ,
                  (λ { {inl b , p} b<a → (b , ∥-∥map cast p) , b<a , Σ≡Prop (λ x → isPropPropTrunc)
                                                                           refl })

A<succA : (X : MEWOcov ℓ) → X <c csucc X
A<succA (A , cov) = (inr tt) , tt* , sym (↓+inr A cov)

X<Y→sX≤Y : (X Y : MEWOcov ℓ) → X <c Y → csucc X ≤c Y
X<Y→sX≤Y (A , covA) (B , covB) (b , mb , A≡B↓b)
 = f , ((λ {x} {y} → mono-f {x} {y}) , λ {x} → mark-f {x}) , sim-f
   where
    tr : ⟨ A ⟩ → ⟨ B ↓+ b ⟩
    tr = fst (idtoeqₒ A (B ↓+ b) A≡B↓b)

    tr⁻¹ : ⟨ B ↓+ b ⟩ → ⟨ A ⟩
    tr⁻¹ = invIsEq (fst (snd (snd (idtoeqₒ A (B ↓+ b) A≡B↓b))))

    tr⁻¹tr≡id : ∀ y → tr⁻¹ (tr y) ≡ y
    tr⁻¹tr≡id = retIsEq (fst (snd (snd (idtoeqₒ A (B ↓+ b) A≡B↓b))))

    trtr⁻¹≡id : ∀ y → tr (tr⁻¹ y) ≡ y
    trtr⁻¹≡id = secIsEq (fst (snd (snd (idtoeqₒ A (B ↓+ b) A≡B↓b))))

    f : ⟨ succ A covA ⟩ → ⟨ B ⟩
    f (inl x) = fst (tr x)
    f (inr x) = b

    mono-f : isMonotone (succ A covA) B f
    mono-f {inl x} {inl y} x<y = fst (fst (snd (idtoeqₒ A (B ↓+ b) A≡B↓b))) x<y
    mono-f {inl x} {inr tt} mx = snd (fst (snd (idtoeqₒ A (B ↓+ b) A≡B↓b))) mx

    mark-f : isMarkingPreserving (succ A covA) B f
    mark-f {inr x} tt* = mb

    sim-f : {y : ⟨ B ⟩}{a : ⟨ succ A covA ⟩} → y ≺⟨ B ⟩ f a →
            Σ ⟨ succ A covA ⟩ (λ a' → a' ≺⟨ succ A covA ⟩ a × (f a' ≡ y))
    sim-f {y} {inl a} b<fa = inl (tr⁻¹ (y , ∥-∥map (λ q → step b<fa q) (snd (tr a)))) ,
                             subst (λ z → tr⁻¹ (y , ∥-∥map (λ q → step b<fa q) (snd (tr a))) ≺⟨ A ⟩ z)
                                   (tr⁻¹tr≡id a)
                                   (fst (snd (snd (snd (idtoeqₒ A (B ↓+ b) A≡B↓b)))) b<fa) ,
                             cong fst (trtr⁻¹≡id (y , _))
    sim-f {y} {inr tt} b<fa = inl (tr⁻¹ (y , ∣ emb b<fa ∣)) ,
                              snd (snd (snd (snd (idtoeqₒ A (B ↓+ b) A≡B↓b)))) b<fa ,
                              cong fst (trtr⁻¹≡id (y , ∣ emb b<fa ∣))

X<sY→X≤Y : (X Y : MEWOcov ℓ) → X <c csucc Y → X ≤c Y
X<sY→X≤Y (A , cA) (B , cB) (inr tt , mb , A≡sB↓b) = subst (A ≤_) (A≡sB↓b ∙ ↓+inr B cB) (≤Refl A)

MEWOcov-has-succ : calc-strong-suc (_<c_ {ℓ = ℓ}) _≤c_ csucc
MEWOcov-has-succ b = ((A<succA b) , X<Y→sX≤Y b) , λ Y → X<sY→X≤Y Y b

{- Union -}

module _ (A : Type ℓ)(F : A → MEWO ℓ) where

  private
    ΣAF = Σ[ a ∈ A ] ⟨ F a ⟩

  -- In order to stay in the same universe with the union, we use the
  -- small characterisations of ≡ and < here
  ~∪ : ΣAF → ΣAF → Type ℓ
  ~∪ (a , x) (b , y) = (F a ↓+ x) ≃ₒ (F b ↓+ y)

  <∪ : ΣAF → ΣAF → Type ℓ
  <∪ (a , x) (b , y) = (F a ↓+ x) <⁻ (F b ↓+ y)

  isWellFounded⟨<∪⟩ : isWellFounded <∪
  isWellFounded⟨<∪⟩ (a , x) = acc-lemma a x  (<Wellfounded (F a ↓+ x))
    where
      acc-lemma : ∀ b y → Acc _<_ (F b ↓+ y) → Acc <∪ (b , y)
      acc-lemma b y (acc s) = acc (λ (c , z) p → acc-lemma c z (s (F c ↓+ z) (<⁻To< _ _ p)))

  <∪-extensionalUpto-~ : (p q : ΣAF) →
                          ((r : ΣAF) → <∪ r p ↔ <∪ r q) →
                          ~∪ p q
  <∪-extensionalUpto-~ (a , x) (b , y) ext = idtoeqₒ _ _ Fa↓+x≡Fb↓+y
    where
      ext' : (C : MEWO ℓ) → C < (F a ↓+ x) ↔ C < (F b ↓+ y)
      ext' C =
        (λ ((z , q) , mz , p) → subst (_< (F b ↓+ y))
                                      (sym (p ∙ iterated↓+ (F a) x z q))
                                      (<⁻To< _ _ (fst (ext (a , z))
                                                      (<To<⁻ _ _ (↓+Monotone< (F a) z x mz))))) ,
        (λ ((z , q) , mz , p) → subst (_< (F a ↓+ x))
                                      (sym (p ∙ iterated↓+ (F b) y z q))
                                      (<⁻To< _ _ (snd (ext (b , z))
                                                      (<To<⁻ _ _ (↓+Monotone< (F b) z y mz)))))

      Fa↓+x≡Fb↓+y : F a ↓+ x ≡ F b ↓+ y
      Fa↓+x≡Fb↓+y = cong fst (coveredExtensional (F a ↓+ x , initialSegmentsCovered (F a) x)
                                                 (F b ↓+ y , initialSegmentsCovered (F b) y)
                                                 (λ (C , covC) → ext' C))

  <∪/~P : ΣAF / ~∪ → ΣAF / ~∪ → hProp ℓ
  <∪/~P = rec2 isSetHProp
            (λ (a , x) (b , y) → <∪ _ _ , isProp⟨<⁻⟩ (F a ↓+ x) (F b ↓+ y))
            (λ (a , x) (b , y) (c , z) p → Σ≡Prop (λ x → isPropIsProp)
                                                  (hPropExt
                                                    (isProp⟨<⁻⟩ (F a ↓+ x) (F c ↓+ z))
                                                    (isProp⟨<⁻⟩ (F b ↓+ y) (F c ↓+ z))
                                                    (subst (_<⁻ (F c ↓+ z))
                                                           (eqtoidₒ (F a ↓+ x) (F b ↓+ y) p))
                                                    (subst (_<⁻ (F c ↓+ z))
                                                           (sym (eqtoidₒ (F a ↓+ x) (F b ↓+ y) p)))))
            (λ (a , x) (b , y) (c , z) p → Σ≡Prop (λ x → isPropIsProp)
                                                  (hPropExt
                                                    (isProp⟨<⁻⟩ (F a ↓+ x) (F b ↓+ y))
                                                    (isProp⟨<⁻⟩ (F a ↓+ x) (F c ↓+ z))
                                                    (subst ((F a ↓+ x) <⁻_)
                                                           (eqtoidₒ (F b ↓+ y) (F c ↓+ z) p))
                                                    (subst ((F a ↓+ x) <⁻_)
                                                           (sym (eqtoidₒ (F b ↓+ y) (F c ↓+ z) p)))))

  <∪/~ : ΣAF / ~∪ → ΣAF / ~∪ → Type ℓ
  <∪/~ x y = typ (<∪/~P x y)

  isProp⟨<∪/~⟩ : isPropValued <∪/~
  isProp⟨<∪/~⟩ x y = str (<∪/~P x y)

  ⋃-marking : ΣAF / ~∪ → hProp ℓ
  ⋃-marking s = ∥ (Σ[ a ∈ A ] (Σ[ x ∈ ⟨ F a ⟩ ] (s ≡ [ a , x ]) × marked (F a) x)) ∥ , isPropPropTrunc

  Acc-<∪/~-lemma : (x : ΣAF) → Acc <∪ x → Acc <∪/~ [ x ]
  Acc-<∪/~-lemma x (acc s) = acc (elimProp (λ y → isProp→ (isPropAcc _))
                                           (λ y y<x → Acc-<∪/~-lemma y (s y y<x)))

  ⋃ : MEWO ℓ
  ⋃ = ((ΣAF / ~∪) ,
      (<∪/~ , ⋃-marking) ,
      (λ x y → str (<∪/~P x y)) ,
      elimProp2
        (λ x y → isProp→ (squash/ x y))
        (λ p q ext → eq/ p q (<∪-extensionalUpto-~ p q
                                (λ r → elimProp {P = λ c → <∪/~ c [ p ] ↔ <∪/~ c [ q ]}
                                                (λ c → isProp× (isProp→ (isProp⟨<∪/~⟩ c [ q ]))
                                                               (isProp→ (isProp⟨<∪/~⟩ c [ p ])))
                                                (λ c → ext [ c ]) [ r ]))) ,
      elimProp (λ x → isPropAcc _) λ { x → Acc-<∪/~-lemma x (isWellFounded⟨<∪⟩ x) })

  ~-equivRel : isEquivRel ~∪
  isEquivRel.reflexive ~-equivRel (a , x) = idtoeqₒ (F a ↓+ x) _ refl
  isEquivRel.symmetric ~-equivRel (a , x) (b , y) p
    = idtoeqₒ _ _ (sym (eqtoidₒ (F a ↓+ x) (F b ↓+ y) p))
  isEquivRel.transitive ~-equivRel (a , x) (b , y) (c , z) p q
    = idtoeqₒ _ _ (eqtoidₒ (F a ↓+ x) (F b ↓+ y) p ∙ eqtoidₒ (F b ↓+ y) (F c ↓+ z) q)

  ~-effective : (a b : A) → (x : ⟨ F a ⟩)(y : ⟨ F b ⟩) → [ a , x ] ≡ [ b , y ] → F a ↓+ x ≡ F b ↓+ y
  ~-effective a b x y eq
    = eqtoidₒ _ _ (effective (λ (a , x) (b , y) → isProp⟨≃ₒ⟩ (F a ↓+ x) (F b ↓+ y))
                             ~-equivRel
                             (a , x) (b , y) eq)

  ⋃-isUpperBound : (a : A) → F a ≤ ⋃
  ⋃-isUpperBound a = (λ x → [ a , x ]) ,
                     ((λ {x} {y} x<y → <To<⁻ _ (F a ↓+ y)
                                               (↓+Monotone< _ _ _ x<y)) ,
                      (λ {x} mx → ∣ a , x , refl , mx ∣)) ,
                     (λ {b} {x} → elimProp {P = P x} (isPropP x) (d x) b)
    where
      P : (x : ⟨ F a ⟩) → ΣAF / ~∪ → Type ℓ
      P x = λ b → b ≺⟨ ⋃ ⟩ [ a , x ] → Σ[ x' ∈ ⟨ F a ⟩ ] (x' ≺⟨ F a ⟩ x × ([ a , x' ] ≡ b))

      isPropP : (x : ⟨ F a ⟩) → (y : ΣAF / ~∪) → isProp (P x y)
      isPropP x y = isProp→ (injective→simulationConclusionIsProp (F a) ⋃ (λ x → [ a , x ])
                              (λ {x} {y} eq → ↓+Injective (F a) x y (~-effective a a x y eq)))

      d : (x : ⟨ F a ⟩) → (y : ΣAF) → P x [ y ]
      d x (b , y) ((b' , b'<+x) , mb' , eq)
        = (b' ,
           mb' ,
           eq/ _ _ (idtoeqₒ _ _ (sym (eqtoidₒ (F b ↓+ y) _ eq ∙ iterated↓+ (F a) x b' b'<+x))))

  ⋃-covered : ((a : A) → isCovered (F a)) → isCovered ⋃
  ⋃-covered covF = elimProp (λ x → isPropPropTrunc)
                            (λ (a , x) → ∥-∥map (cov a x) (covF a x))
    where
      cov : (a : A) → (x : ⟨ F a ⟩) →
            Σ[ y ∈ ⟨ F a ⟩ ] marked (F a) y × x ≺̂*⟨ F a ⟩ y →
            Σ[ y ∈ ⟨ ⋃ ⟩ ] marked ⋃ y × [ a , x ] ≺̂*⟨ ⋃ ⟩ y
      cov a x (p , mp , x<*p) = [ a , p ] ,
                                ∣ a , p , refl , mp ∣ ,
                                ReflTransCl-map (λ x → [ a , x ])
                                                (λ x<y → <To<⁻ _ _ (↓+Monotone< (F a) _ _ x<y)) x<*p

  ⋃↓[] : (a : A) → (x : ⟨ F a ⟩) → ⋃ ↓+ [ a , x ] ≡ F a ↓+ x
  ⋃↓[] a x = acc-helper a x (wellfounded ⋃ [ a , x ])
    where
      acc-helper : (a : A) → (x : ⟨ F a ⟩) → Acc <∪/~ [ a , x ] → ⋃ ↓+ [ a , x ] ≡ F a ↓+ x
      acc-helper a x (acc s) = ≤Antisymmetry _ _ f g
       where
        f : (⋃ ↓+ [ a , x ]) ≤ (F a ↓+ x)
        f = covered→principal (⋃ ↓+ [ a , x ])
                              (initialSegmentsCovered (⋃) [ a , x ])
                              (F a ↓+ x)
                              (≤ₚCharacterisationFrom (⋃ ↓+ [ a , x ])
                                                      (F a ↓+ x)
                                                      (λ (y , p) → lem y p))
          where
            lem : (y : ⟨ ⋃ ⟩) → (p : ∥ y ≺⁺⟨ ⋃ ⟩ [ a , x ] ∥) → marked (⋃ ↓+ [ a , x ]) (y , p) →
                  ∥ Σ[ z ∈ ⟨ F a ↓+ x ⟩ ] ((⋃ ↓+ [ a , x ]) ↓+ (y , p) ≡ (F a ↓+ x) ↓+ z) ×
                                           marked (F a ↓+ x) z ∥
            lem = elimProp (λ y → isPropΠ2 (λ p _ → isPropPropTrunc))
                           (λ (b , y) p my@(b' , mb' , q) → ∣ b' ,
                                                              iterated↓+ ⋃ [ a , x ] [ b , y ] p ∙
                                                              acc-helper b y (s [ b , y ] my) ∙
                                                              eqtoidₒ (F b ↓+ y) _ q , mb' ∣)

        g : (F a ↓+ x) ≤ (⋃ ↓+ [ a , x ])
        g = covered→principal
              (F a ↓+ x)
              (initialSegmentsCovered (F a) x)
              (⋃ ↓+ [ a , x ])
              (≤ₚCharacterisationFrom
                (F a ↓+ x)
                (⋃ ↓+ [ a , x ])
                (λ (y , p) my → ∣ ([ a , y ] ,
                                   ∥-∥map (TransCl-map (λ x → [ a , x ])
                                         (λ {x} {y} x<y → <To<⁻ _ _
                                                                (↓+Monotone< (F a) x y x<y))) p) ,
                                  iterated↓+ (F a) x y p ∙
                                  sym
                                    (iterated↓+ ⋃
                                                [ a , x ]
                                                [ a , y ]
                                                (∥-∥map
                                                  (TransCl-map
                                                    (λ x → [ a , x ])
                                                    (λ {x} {y} x<y →
                                                       <To<⁻ _ _ (↓+Monotone< (F a) x y x<y))) p) ∙
                                    (acc-helper a y (s [ a , y ]
                                                       (<To<⁻ (F a ↓+ y) (F a ↓+ x)
                                                              (↓+Monotone< (F a) y x my)))))                                                           ,
                                  <To<⁻ (F a ↓+ y) (F a ↓+ x) (↓+Monotone< (F a) y x my) ∣))

  ⋃-isLeastUpperBound : (X : MEWO ℓ) → ((a : A) → F a ≤ X) → ⋃ ≤ X
  ⋃-isLeastUpperBound X ub =
    ≤CharacterisationFrom ⋃ X
      (elimProp (λ x → isPropPropTrunc)
                (λ (a , x) → ∣ f a x ,
                               ⋃↓[] a x ∙ f-preserves-↓ a x ,
                               ∥-∥rec (isPropMarked X (f a x))
                                     (λ (a' , x' , ax=a'x' , mx') →
                                         subst (marked X)
                                               (↓+Injective X (f a' x')
                                                              (f a x)
                                                              (sym (f-preserves-↓ a' x') ∙
                                                               ~-effective a' a x' x (sym ax=a'x') ∙
                                                               f-preserves-↓ a x))
                                               (f-preserves-marking a' x' mx')) ∣))
    where
      f : (a : A) → ⟨ F a ⟩ → ⟨ X ⟩
      f a x = fst (ub a) x

      f-preserves-↓ : (a : A) → (x : ⟨ F a ⟩) → F a ↓+ x ≡ X ↓+ (f a x)
      f-preserves-↓ a x = simulationsPreserve↓ (F a) X (f a) (snd (ub a)) x

      f-preserves-marking : (a : A) → (x : ⟨ F a ⟩) → marked (F a) x → marked X (f a x)
      f-preserves-marking a x = snd (fst (snd (ub a)))
