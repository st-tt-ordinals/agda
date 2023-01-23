
----------------------------------------------------------------------------------------------------
-- Translation between covered marked EWOs and Aczel's V
----------------------------------------------------------------------------------------------------

{-# OPTIONS --cubical --safe --experimental-lossy-unification #-}

module MEWO.TranslationV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
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
open import Cubical.HITs.CumulativeHierarchy.Base as V

open import PropTrunc
open import Cubical.HITs.PropositionalTruncation.Base

open import Iff
open import General-Properties

open import MEWO.Base
open import MEWO.Covered
open import MEWO.Constructions


{- V as an extensional, wellfounded order -}

_∈₀_ : V ℓ → V ℓ → Type (ℓ-suc ℓ)
A ∈₀ B = typ (A ∈ B)

isEWO⟨∈₀⟩ : isEWO (_∈₀_ {ℓ = ℓ})
isEWO⟨∈₀⟩ {ℓ = ℓ} = (λ A B → str (A ∈ B)) , e , w
  where
    e : isExtensional _∈₀_
    e = V.elimProp
          {Z = λ a → (b : V ℓ) → ((c : V ℓ) → (c ∈₀ a ↔ c ∈₀ b)) → a ≡ b}
          (λ a → isPropΠ2 (λ b _ → setIsSet a b))
          (λ A f ihAf → V.elimProp {Z = λ b → ((c : V ℓ) → (c ∈₀ sett A f ↔ c ∈₀ b)) → sett A f ≡ b}
                                   (λ b → isProp→ (setIsSet (sett A f) b))
                                   (λ B g ihBg ext → seteq A B f g
                                       ((λ a → fst (ext (f a)) ∣ a , refl ∣₁) ,
                                        (λ b → snd (ext (g b)) ∣ b , refl ∣₁))))
    w : isWellFounded _∈₀_
    w = V.elimProp isPropAcc
                   (λ A f ih → acc (λ b b<a → ∥-∥rec (isPropAcc b)
                                                    (λ (a , fa≡b) → subst (Acc _∈₀_)
                                                                          fa≡b
                                                                          (ih a))
                                                    (fromLib∥-∥ b<a)))

V-as-MEWO : (ℓ : Level) → MEWO (ℓ-suc ℓ)
V-as-MEWO ℓ = (V ℓ , (_∈₀_ , λ _ → Unit* , isPropUnit*) , isEWO⟨∈₀⟩)

{- V to MEWOcov -}

ψ : V ℓ → MEWOcov ℓ
ψ {ℓ = ℓ} = V.elim {isSetZ = λ _ → isSet⟨MEWOcov⟩} (record { ElimSett = pt ; ElimEq = eq })
  where
   pt : ∀ {ℓ} (A : Type ℓ) (f : A → V ℓ) → (ih : (a : A) → MEWOcov ℓ) → MEWOcov ℓ
   pt A f ih = ⋃ A (λ a → fst (csucc (ih a))) , ⋃-covered A _ (λ a → snd (csucc (ih a)))
   eq : ∀ {ℓ} (A B : Type ℓ) (f : A → V ℓ) (g : B → V ℓ) →
        eqImage f g → (ihf : (a : A) → MEWOcov ℓ) → (ihg : (b : B) → MEWOcov ℓ) →
        ((a : A) → ∥ Σ (fiber g (f a)) (λ y → ihg (fst y) ≡ ihf a) ∥₁) →
        ((b : B) → ∥ Σ (fiber f (g b)) (λ y → ihf (fst y) ≡ ihg b) ∥₁) →
        pt A f ihf ≡ pt B g ihg
   eq A B f g f~g ihf ihg p q =
     Σ≡Prop isProp⟨isCovered⟩
            (≤Antisymmetry (fst (pt A f ihf))
                           (fst (pt B g ihg))
                           (lemma A B f g ihf ihg p)
                           (lemma B A g f ihg ihf q))
     where
       lemma : ∀ A B f g ihf ihg → ((a : A) → ∥ Σ (fiber g (f a)) (λ y → ihg (fst y) ≡ ihf a) ∥₁) →
               fst (pt A f ihf) ≤ fst (pt B g ihg)
       lemma A B f g ihf ihg p =
         ⋃-isLeastUpperBound A _ (fst (pt B g ihg))
                             (λ a → ∥-∥rec (isProp⟨≤⟩ (fst (csucc (ihf a))) (fst (pt B g ihg)))
                                          (λ ((b , gb=fa) , ihgb=ihfa) →
                                            subst (λ z → fst (csucc z) ≤ fst (pt B g ihg))
                                                  ihgb=ihfa
                                                  (⋃-isUpperBound B (λ b → fst (csucc (ihg b))) b))
                                          (fromLib∥-∥ (p a)))

{-
-- With `--experimental-lossy-unification`, the following typechecks
-- quickly. Without it, it takes seemingly forever.
ψ-comp : (A : Type ℓ) → (f : A → V ℓ) →
         ψ (sett A f) ≡ (⋃ A (λ a → fst (csucc (ψ (f a)))) ,
                         ⋃-covered A (λ a → fst (csucc (ψ (f a)))) λ a → snd (csucc (ψ (f a))))
ψ-comp A f = refl
-}

ψ-simulation : isSimulation (V-as-MEWO ℓ) (MEWOcov-as-MEWO ℓ) ψ
ψ-simulation {ℓ = ℓ} = existsSimulationsAreSimulations (V-as-MEWO ℓ) (MEWOcov-as-MEWO ℓ) ψ
                         (((λ {x} {y} → monotone x y) , (λ p → p)) ,
                          (λ {B} {A} → simul (fst B) (snd B) A))
  where
    ψgb<ψsBg-lemma : ∀ B g b → fst (ψ (g b)) < fst (ψ (sett B g))
    ψgb<ψsBg-lemma B g b = [ b , inr tt ] ,
                           ∣ b , inr tt , refl , tt* ∣ ,
                           sym (⋃↓[] B (λ b → fst (csucc (ψ (g b)))) b (inr tt) ∙
                                ↓+inr (fst (ψ (g b))) (snd (ψ (g b))))

    monotone : (x y : V ℓ) → x ∈₀ y → ψ x <c ψ y
    monotone =
      V.elimProp
        (λ x → isPropΠ2 (λ y _ → isProp⟨<⟩ (fst (ψ x)) (fst (ψ y))))
        (λ A f ihf → V.elimProp
                       (λ y → isProp→ (isProp⟨<⟩ (fst (ψ _)) (fst (ψ y))))
                       (λ B g ihg x<y → ∥-∥rec (isProp⟨<⟩ _ _)
                                              (λ (b , gb≡x) →
                                                   subst (λ z → fst (ψ z) < fst (ψ (sett B g)))
                                                         gb≡x
                                                         (ψgb<ψsBg-lemma B g b))
                                              (fromLib∥-∥ x<y)))

    simul : (B : MEWO ℓ) → (covB : isCovered B) → (A : V ℓ) → B < fst (ψ A) →
            ∥ Σ[ A' ∈ V ℓ ] (A' ∈₀ A × (ψ A' ≡ (B , covB))) ∥
    simul B covB =
      V.elimProp
        (λ A → isProp→ isPropPropTrunc)
        (λ { A f ih (b , mb , eq) →
               Q.elimProp
                  {P = λ b → marked (fst (ψ (sett A f))) b →
                             B ≡ (fst (ψ (sett A f)) ↓+ b) →
                             ∥ Σ (V ℓ) (λ A' → (A' ∈₀ sett A f) × (ψ A' ≡ (B , covB))) ∥}
                  (λ b → isPropΠ2 (λ _ _ → isPropPropTrunc))
                  (λ { (a , p) mb eq →
                    ∥-∥map (λ { (a' , inr tt , qq , tt*) →
                                 f a' ,
                                 ∣ a' , refl ∣₁ ,
                                 Σ≡Prop isProp⟨isCovered⟩
                                        (sym (eq ∙
                                              ⋃↓[] A (λ a → fst (csucc (ψ (f a)))) a p ∙
                                              ~-effective A (λ a → fst (csucc (ψ (f a))))
                                                          a a' p (inr tt) qq ∙
                                              ↓+inr (fst (ψ (f a')))
                                                    (snd (ψ (f a'))))) }) mb }) b mb eq })

{- MEWOcov to V -}

φ-wf : (A : MEWO ℓ) → (covA : isCovered A) → Acc _<c_ (A , covA) → V ℓ
φ-wf A covA (acc s) =
  sett (Σ[ a ∈ ⟨ A ⟩ ] marked A a)
       (λ (a , ma) → φ-wf (A ↓+ a) (initialSegmentsCovered A a) (s _ (a , ma , refl)))

φ : MEWOcov ℓ → V ℓ
φ {ℓ = ℓ} (A , covA) = φ-wf A covA (wellfounded (MEWOcov-as-MEWO ℓ) (A , covA))

φ-wf-comp : (A : MEWO ℓ) → (covA : isCovered A) → (a : Acc _<c_ (A , covA)) →
            φ-wf A covA a ≡ φ (A , covA)
φ-wf-comp A covA (acc s) =
  cong (sett (Σ[ a ∈ ⟨ A ⟩ ] marked A a))
       (funExt λ { (a , ma) → cong (φ-wf (A ↓+ a) (initialSegmentsCovered A a))
                                   (isPropAcc ((A ↓+ a) , initialSegmentsCovered A a) _ _) })

φ-comp : (A : MEWO ℓ) → (covA : isCovered A) →
         φ (A , covA) ≡ sett (Σ[ a ∈ ⟨ A ⟩ ] marked A a)
                             (λ (a , ma) → φ ((A ↓+ a) , initialSegmentsCovered A a))
φ-comp A covA = cong (sett (Σ[ a ∈ ⟨ A ⟩ ] marked A a))
                     (funExt (λ (a , ma) → φ-wf-comp (A ↓+ a) (initialSegmentsCovered A a) _))

φ-simulation : isSimulation (MEWOcov-as-MEWO ℓ) (V-as-MEWO ℓ) φ
φ-simulation {ℓ = ℓ} =
  existsSimulationsAreSimulations (MEWOcov-as-MEWO ℓ)
                                  (V-as-MEWO ℓ)
                                  φ
                                  (((λ {(A , cA)} {(B , cB)} → monotone A cA B cB) , (λ p → p)) ,
                                   (λ {B} {A} → simul B (fst A) (snd A)))
  where
    monotone : (A : MEWO ℓ) → (covA : isCovered A) → (B : MEWO ℓ) → (covB : isCovered B) →
               A < B → φ (A , covA) ∈₀ φ (B , covB)
    monotone A covA B covB (b , mb , A≡B↓b) =
      subst (λ z → φ (A , covA) ∈₀ z)
            (sym (φ-comp B covB))
            ∣ (b , mb) , cong φ (Σ≡Prop isProp⟨isCovered⟩ (sym A≡B↓b)) ∣₁

    simul : (B : V ℓ) → (A : MEWO ℓ) → (covA : isCovered A) → B ∈₀ φ (A , covA) →
            ∥ Σ[ A' ∈ MEWOcov ℓ ] (A' <c (A , covA) × (φ A' ≡ B)) ∥
    simul B A covA B∈φA =
      ∥-∥map (λ ((a , ma) , φA↓a≡B) → (A ↓+ a ,
                                      initialSegmentsCovered A a) ,
                                      (a , ma , refl) ,
                                      sym (φ-wf-comp (A ↓+ a) (initialSegmentsCovered A a) _) ∙
                                      φA↓a≡B)
            (fromLib∥-∥ B∈φA)

{- MEWOcov equals V -}

MEWOcov≡V : MEWOcov-as-MEWO ℓ ≡ V-as-MEWO ℓ
MEWOcov≡V {ℓ = ℓ} = ≤Antisymmetry (MEWOcov-as-MEWO ℓ)
                                 (V-as-MEWO ℓ)
                                 (φ , φ-simulation)
                                 (ψ , ψ-simulation)

V≡MEWOcov : V-as-MEWO ℓ ≡ MEWOcov-as-MEWO ℓ
V≡MEWOcov = sym MEWOcov≡V
