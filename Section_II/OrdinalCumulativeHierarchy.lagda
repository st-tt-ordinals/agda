\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan

open import UF.PropTrunc
open import UF.Univalence

module OrdinalCumulativeHierarchy
        (pt : propositional-truncations-exist)
        (ua : Univalence)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' _ _ = fe

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type hiding (Ord)
open import Ordinals.Underlying

open import CumulativeHierarchy pt fe pe

module ordinal-of-set-theoretic-ordinals
        (ch : cumulative-hierarchy-exists 𝓤)
       where

 open cumulative-hierarchy-exists ch

\end{code}

We start by defining a set theoretic ordinal to be a transitive set whose
elements are again transitive sets.

\begin{code}

 is-transitive-set : 𝕍 → 𝓤 ⁺ ̇
 is-transitive-set x = (u : 𝕍) (v : 𝕍) → u ∈ x → v ∈ u → v ∈ x

 being-transitive-set-is-prop : {x : 𝕍} → is-prop (is-transitive-set x)
 being-transitive-set-is-prop = Π₄-is-prop fe (λ _ _ _ _ → ∈-is-prop-valued)

 is-set-theoretic-ordinal : 𝕍 → 𝓤 ⁺ ̇
 is-set-theoretic-ordinal x = is-transitive-set x
                            × ((y : 𝕍) → y ∈ x → is-transitive-set y)

 being-set-theoretic-ordinal-is-prop : {x : 𝕍} → is-prop (is-set-theoretic-ordinal x)
 being-set-theoretic-ordinal-is-prop =
  ×-is-prop being-transitive-set-is-prop
            (Π₂-is-prop fe (λ _ _ → being-transitive-set-is-prop))

 transitive-set-if-set-theoretic-ordinal : {x : 𝕍}
                                         → is-set-theoretic-ordinal x
                                         → is-transitive-set x
 transitive-set-if-set-theoretic-ordinal = pr₁

 transitive-set-if-element-of-set-theoretic-ordinal : {x : 𝕍}
                                                    → is-set-theoretic-ordinal x
                                                    → {y : 𝕍} → y ∈ x
                                                    → is-transitive-set y
 transitive-set-if-element-of-set-theoretic-ordinal σ {y} m = pr₂ σ y m

 being-set-theoretic-ordinal-is-hereditary : {x : 𝕍} → is-set-theoretic-ordinal x
                                           → {y : 𝕍}
                                           → y ∈ x → is-set-theoretic-ordinal y
 being-set-theoretic-ordinal-is-hereditary {x} (t , τ) {y} m =
  τ y m , (λ z n → τ z (t y z m n))

\end{code}

Restricting our attention to those elements of 𝕍 that are set theoretic
ordinals, we show that the membership relation ∈ makes this subtype into a type
theoretic ordinal.

\begin{code}

 𝕍ᵒʳᵈ : 𝓤 ⁺ ̇
 𝕍ᵒʳᵈ = Σ x ꞉ 𝕍 , is-set-theoretic-ordinal x

 𝕍ᵒʳᵈ-is-subtype : {x y : 𝕍ᵒʳᵈ} → pr₁ x ＝ pr₁ y → x ＝ y
 𝕍ᵒʳᵈ-is-subtype = to-subtype-＝ (λ _ → being-set-theoretic-ordinal-is-prop)

 _∈ᵒʳᵈ_ : 𝕍ᵒʳᵈ → 𝕍ᵒʳᵈ → 𝓤 ⁺  ̇
 _∈ᵒʳᵈ_ (x , _) (y , _) = x ∈ y

 ∈ᵒʳᵈ-is-extensional : is-extensional _∈ᵒʳᵈ_
 ∈ᵒʳᵈ-is-extensional (x , u) (y , v) s t =
  𝕍ᵒʳᵈ-is-subtype
   (∈-extensionality
     x y
     (λ z m → s (z , being-set-theoretic-ordinal-is-hereditary u m) m)
     (λ z m → t (z , being-set-theoretic-ordinal-is-hereditary v m) m))

 ∈ᵒʳᵈ-is-transitive : is-transitive _∈ᵒʳᵈ_
 ∈ᵒʳᵈ-is-transitive (x , _) (y , _) (z , τ) x-in-y y-in-z =
  transitive-set-if-set-theoretic-ordinal τ y x y-in-z x-in-y

 ∈-is-well-founded : is-well-founded _∈_
 ∈-is-well-founded = ∈-induction (is-accessible _∈_)
                                 (λ x → accessibility-is-prop _∈_ fe' x)
                                 (λ x IH → step IH)

 ∈ᵒʳᵈ-is-well-founded : is-well-founded _∈ᵒʳᵈ_
 ∈ᵒʳᵈ-is-well-founded = transfinite-induction-converse _∈ᵒʳᵈ_ W
  where
   W : Well-founded _∈ᵒʳᵈ_
   W P IH = (λ (x , σ) → Q-holds-everywhere x σ)
    where
     Q : 𝕍 → 𝓤 ⁺ ̇
     Q x = (σ : is-set-theoretic-ordinal x) → P (x , σ)
     Q-holds-everywhere : (x : 𝕍) → Q x
     Q-holds-everywhere = transfinite-induction _∈_ ∈-is-well-founded Q f
      where
       f : (x : 𝕍) → ((y : 𝕍) → y ∈ x → Q y) → Q x
       f x IH' σ = IH (x , σ) g
        where
         g : (y : 𝕍ᵒʳᵈ) → y ∈ᵒʳᵈ (x , σ) → P y
         g (y , τ) y-in-x = IH' y y-in-x τ

 𝕍ᴼᴿᴰ : Ordinal (𝓤 ⁺)
 𝕍ᴼᴿᴰ = 𝕍ᵒʳᵈ , _∈ᵒʳᵈ_
             , (λ x y → ∈-is-prop-valued)
             , ∈ᵒʳᵈ-is-well-founded
             , ∈ᵒʳᵈ-is-extensional
             , ∈ᵒʳᵈ-is-transitive

\end{code}

We now work towards proving that 𝕍ᴼᴿᴰ and Ord, the ordinal of type theoretic
ordinals, are isomorphic (as type theoretic ordinals).

We start by defining a map Ord → 𝕍 by transfinite recursion on Ord.

\begin{code}

 private
  Ord : 𝓤 ⁺ ̇
  Ord = Ordinal 𝓤

 Φ : Ord → 𝕍
 Φ = transfinite-recursion-on-OO 𝕍 (λ α f → 𝕍-set f)

 Φ-behaviour : (α : Ord) → Φ α ＝ 𝕍-set (λ a → Φ (α ↓ a))
 Φ-behaviour = transfinite-recursion-on-OO-behaviour 𝕍 (λ a f → 𝕍-set f)

 ∈-of-Φ : (α : Ord) (x : 𝕍)
        → x ∈ Φ α ＝ (∃ a ꞉ ⟨ α ⟩ , Φ (α ↓ a) ＝ x)
 ∈-of-Φ α x =
  x ∈ Φ α                        ＝⟨ ap (x ∈_) (Φ-behaviour α) ⟩
  x ∈ 𝕍-set (λ a → Φ (α ↓ a))    ＝⟨ ∈-for-𝕍-sets x _ ⟩
  (∃ a ꞉ ⟨ α ⟩ , Φ (α ↓ a) ＝ x) ∎

 to-∈-of-Φ : (α : Ord) {x : 𝕍}
           → (∃ a ꞉ ⟨ α ⟩ , Φ (α ↓ a) ＝ x) → x ∈ Φ α
 to-∈-of-Φ α {x} = back-Idtofun (∈-of-Φ α x)

 from-∈-of-Φ : (α : Ord) {x : 𝕍}
             → x ∈ Φ α → (∃ a ꞉ ⟨ α ⟩ , Φ (α ↓ a) ＝ x)
 from-∈-of-Φ α {x} = Idtofun (∈-of-Φ α x)

\end{code}

The map Ord → 𝕍 preserves the strict and weak order.

\begin{code}

 Φ-preserves-strict-order : (α β : Ord) → α ⊲ β → Φ α ∈ Φ β
 Φ-preserves-strict-order α β (b , refl) = to-∈-of-Φ β ∣ b , refl ∣

 Φ-preserves-weak-order : (α β : Ord) → α ⊴ β → Φ α ⊆ Φ β
 Φ-preserves-weak-order α β l x m = to-∈-of-Φ β m'
  where
   l' : (a : ⟨ α ⟩) → Σ b ꞉ ⟨ β ⟩ , α ↓ a ＝ β ↓ b
   l' = from-≼ (⊴-gives-≼ α β l)
   m' : ∃ b ꞉ ⟨ β ⟩ , Φ (β ↓ b) ＝ x
   m' = ∥∥-functor h (from-∈-of-Φ α m)
    where
     h : (Σ a ꞉ ⟨ α ⟩ , Φ (α ↓ a) ＝ x)
       → (Σ b ꞉ ⟨ β ⟩ , Φ (β ↓ b) ＝ x)
     h (a , refl) = (b , ap Φ (e ⁻¹))
      where
       b : ⟨ β ⟩
       b = pr₁ (l' a)
       e : α ↓ a ＝ β ↓ b
       e = pr₂ (l' a)

\end{code}

An argument by transfinite induction shows that the map Φ is left
cancellable, which yields a quick proof that Φ not only preserves the
strict order, but also reflects it. It follows that Φ also reflects the
weak order.

\begin{code}

 Φ-is-left-cancellable : (α β : Ord) → Φ α ＝ Φ β → α ＝ β
 Φ-is-left-cancellable = transfinite-induction-on-OO _ f
  where
   f : (α : Ord)
     → ((a : ⟨ α ⟩) (β : Ord) → Φ (α ↓ a) ＝ Φ β → (α ↓ a) ＝ β)
     → (β : Ord) → Φ α ＝ Φ β → α ＝ β
   f α IH β e = ⊴-antisym α β (to-⊴ α β g₁) (to-⊴ β α g₂)
    where
     g₁ : (a : ⟨ α ⟩) → (α ↓ a) ⊲ β
     g₁ a = ∥∥-rec (⊲-is-prop-valued (α ↓ a) β) h (from-∈-of-Φ β m)
      where
       h : (Σ b ꞉ ⟨ β ⟩ , Φ (β ↓ b) ＝ Φ (α ↓ a)) → (α ↓ a) ⊲ β
       h (b , e) = (b , (IH a (β ↓ b) (e ⁻¹)))
       m : Φ (α ↓ a) ∈ Φ β
       m = transport (Φ (α ↓ a) ∈_) e
                     (to-∈-of-Φ α ∣ a , refl ∣)
     g₂ : (b : ⟨ β ⟩) → (β ↓ b) ⊲ α
     g₂ b = ∥∥-rec (⊲-is-prop-valued (β ↓ b) α) h (from-∈-of-Φ α m)
      where
       h : (Σ a ꞉ ⟨ α ⟩ , Φ (α ↓ a) ＝ Φ (β ↓ b)) → (β ↓ b) ⊲ α
       h (a , e) = (a , ((IH a (β ↓ b) e) ⁻¹))
       m : Φ (β ↓ b) ∈ Φ α
       m = transport (Φ (β ↓ b) ∈_) (e ⁻¹)
                     (to-∈-of-Φ β ∣ b , refl ∣)

 Φ-reflects-strict-order : (α β : Ord) → Φ α ∈ Φ β → α ⊲ β
 Φ-reflects-strict-order α β m = ∥∥-rec (⊲-is-prop-valued α β) h m'
  where
   h : (Σ b ꞉ ⟨ β ⟩ , Φ (β ↓ b) ＝ Φ α) → α ⊲ β
   h (b , e) = (b , ((Φ-is-left-cancellable (β ↓ b) α e) ⁻¹))
   m' : ∃ b ꞉ ⟨ β ⟩ , Φ (β ↓ b) ＝ Φ α
   m' = from-∈-of-Φ β m

 Φ-reflects-weak-order : (α β : Ord) → Φ α ⊆ Φ β → α ⊴ β
 Φ-reflects-weak-order α β s = to-⊴ α β h
  where
   h : (a : ⟨ α ⟩) → (α ↓ a) ⊲ β
   h a = Φ-reflects-strict-order (α ↓ a) β m
    where
     m : Φ (α ↓ a) ∈ Φ β
     m = s (Φ (α ↓ a)) (to-∈-of-Φ α ∣ a , refl ∣)

\end{code}

The map Ord → 𝕍 constructed above actually factors through the subtype 𝕍ᵒʳᵈ.

(The proof is quite straightforward, but the formal proof is slightly long,
because we need to use from-∈-of-Φ and to-∈-of-Φ as we don't have
judgemental computation rules for 𝕍.)

\begin{code}

 Φᵒʳᵈ : Ord → 𝕍ᵒʳᵈ
 Φᵒʳᵈ α = (Φ α , ρ α)
  where
   τ : (β : Ord) → is-transitive-set (Φ β)
   τ β x y x-in-β y-in-x = to-∈-of-Φ β (∥∥-rec ∃-is-prop lemma x-in-β')
    where
     x-in-β' : ∃ b ꞉ ⟨ β ⟩ , Φ (β ↓ b) ＝ x
     x-in-β' = from-∈-of-Φ β x-in-β
     lemma : (Σ b ꞉ ⟨ β ⟩ , Φ (β ↓ b) ＝ x)
           → ∃ c ꞉ ⟨ β ⟩ , Φ (β ↓ c) ＝ y
     lemma (b , refl) = ∥∥-functor h y-in-β↓b
      where
       h : (Σ c ꞉ ⟨ β ↓ b ⟩ , Φ ((β ↓ b) ↓ c) ＝ y)
         → Σ d ꞉ ⟨ β ⟩ , Φ (β ↓ d) ＝ y
       h ((c , l) , refl) = (c , ap Φ ((iterated-↓ β b c l) ⁻¹))
       y-in-β↓b : ∃ c ꞉ ⟨ β ↓ b ⟩ , Φ ((β ↓ b) ↓ c) ＝ y
       y-in-β↓b = from-∈-of-Φ (β ↓ b) y-in-x

   ρ : (β : Ord) → is-set-theoretic-ordinal (Φ β)
   ρ = transfinite-induction-on-OO
        (λ - → is-set-theoretic-ordinal (Φ -))
        ρ'
    where
     ρ' : (β : Ord)
        → ((b : ⟨ β ⟩) → is-set-theoretic-ordinal (Φ (β ↓ b)))
        → is-set-theoretic-ordinal (Φ β)
     ρ' β IH = (τ β , τ')
      where
       τ' : (y : 𝕍) → y ∈ Φ β → is-transitive-set y
       τ' y m = ∥∥-rec being-transitive-set-is-prop h (from-∈-of-Φ β m)
        where
         h : (Σ b ꞉ ⟨ β ⟩ , Φ (β ↓ b) ＝ y) → is-transitive-set y
         h (b , refl) = τ (β ↓ b)

 Φᵒʳᵈ-is-left-cancellable : {α β : Ord} → Φᵒʳᵈ α ＝ Φᵒʳᵈ β → α ＝ β
 Φᵒʳᵈ-is-left-cancellable {α} {β} e =
  Φ-is-left-cancellable α β (ap pr₁ e)

\end{code}

To show that Φᵒʳᵈ is an isomorphism of ordinals it now suffices to prove
that it is split surjective.

We construct a map 𝕍 → Ord by recursion on 𝕍 by sending 𝕍-set {A} f to the
supremum of ordinals ⋁ (ψ (f a) + 𝟙) indexed by a : A.

\begin{code}

 open import Ordinals.Arithmetic fe'
 open import Ordinals.Arithmetic-Properties ua hiding (lemma₁ ; lemma₂)
 open import Ordinals.OrdinalOfOrdinalsSuprema ua

 open import UF.Quotient hiding (is-prop-valued)

 module Ψ-construction
         (sq : set-quotients-exist)
        where

  open suprema pt (set-replacement-from-set-quotients sq pt)

  private
   Ψ-aux : {A : 𝓤 ̇ } → (A → 𝕍) → (A → Ord) → Ord
   Ψ-aux _ r = sup (λ a → r a +ₒ 𝟙ₒ)

   Ψ-packaged : Σ ϕ ꞉ (𝕍 → Ord) , ({A : 𝓤 ̇} (f : A → 𝕍)
                                  (r : A → Ordinal 𝓤) → ϕ (𝕍-set f) ＝ Ψ-aux f r)
   Ψ-packaged = 𝕍-recursion-with-computation the-type-of-ordinals-is-a-set ρ τ
    where
     ρ = Ψ-aux
     monotone-lemma : {A B : 𝓤 ̇} (f : A → 𝕍) (g : B → 𝕍)
                    → (r₁ : A → Ord) (r₂ : B → Ord)
                    → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , r₁ a ＝ r₂ b ∥)
                    → ρ f r₁ ⊴ ρ g r₂
     monotone-lemma {A} {B} f g r₁ r₂ e =
      sup-is-lower-bound-of-upper-bounds (λ a → r₁ a +ₒ 𝟙ₒ) (ρ g r₂) ϕ
       where
        ϕ : (a : A) → (r₁ a +ₒ 𝟙ₒ) ⊴ ρ g r₂
        ϕ a = ∥∥-rec (⊴-is-prop-valued _ _) ψ (e a)
         where
          ψ : (Σ b ꞉ B , Σ p ꞉ f a ＝ g b , r₁ a ＝ r₂ b)
            → (r₁ a +ₒ 𝟙ₒ) ⊴ ρ g r₂
          ψ (b , _ , q) = ⊴-trans _ (r₂ b +ₒ 𝟙ₒ) _ k l
           where
            k : (r₁ a +ₒ 𝟙ₒ) ⊴ (r₂ b +ₒ 𝟙ₒ)
            k = ≃ₒ-to-⊴ _ _ (idtoeqₒ _ _ (ap (_+ₒ 𝟙ₒ) q))
            l : (r₂ b +ₒ 𝟙ₒ) ⊴ ρ g r₂
            l = sup-is-upper-bound _ b
     τ : {A B : 𝓤 ̇} (f : A → 𝕍) (g : B → 𝕍)
       → (r₁ : A → Ord) (r₂ : B → Ord)
       → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , r₁ a ＝ r₂ b ∥)
       → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , r₂ b ＝ r₁ a ∥)
       → f ≈ g
       → ρ f r₁ ＝ ρ g r₂
     τ {A} {B} f g r₁ r₂ e₁ e₂ _ =
      ⊴-antisym (ρ f r₁) (ρ g r₂)
                (monotone-lemma f g r₁ r₂ e₁)
                (monotone-lemma g f r₂ r₁ e₂)

  Ψ : 𝕍 → Ord
  Ψ = pr₁ (Ψ-packaged)

\end{code}

The below records the behaviour on 𝕍-sets that we announced above.

\begin{code}

  Ψ-behaviour-on-𝕍-sets :
     {A : 𝓤 ̇ } (f : A → 𝕍)
   → Ψ (𝕍-set f) ＝ sup (λ a → Ψ (f a) +ₒ 𝟙ₒ)
  Ψ-behaviour-on-𝕍-sets f = pr₂ Ψ-packaged f (λ a → Ψ (f a))

  Ψᵒʳᵈ : 𝕍ᵒʳᵈ → Ord
  Ψᵒʳᵈ = Ψ ∘ pr₁

\end{code}

We show that Φ is a split surjection by showing that Ψᵒʳᵈ is a
section of it. The fact that we are restricting the inputs to set theoretic
ordinals is crucial in proving one of the inequalities.

\begin{code}

  Ψ-is-section-of-Φ : (x : 𝕍)
                    → is-set-theoretic-ordinal x
                    → Φ (Ψ x) ＝ x
  Ψ-is-section-of-Φ =
   𝕍-prop-induction _ (λ x → Π-is-prop fe (λ _ → 𝕍-is-large-set)) ρ
    where
     ρ : {A : 𝓤 ̇} (f : A → 𝕍)
       → ((a : A) → is-set-theoretic-ordinal (f a)
                  → Φ (Ψ (f a)) ＝ f a)
       → is-set-theoretic-ordinal (𝕍-set f)
       → Φ (Ψ (𝕍-set f)) ＝ 𝕍-set f
     ρ {A} f IH σ =
      Φ (Ψ (𝕍-set f))         ＝⟨ ⦅1⦆ ⟩
      Φ s                     ＝⟨ ⦅2⦆ ⟩
      𝕍-set (λ y → Φ (s ↓ y)) ＝⟨ ⦅3⦆ ⟩
      𝕍-set f                 ∎
       where
        s : Ord
        s = sup (λ a → Ψ (f a) +ₒ 𝟙ₒ)
        ⦅1⦆ = ap Φ (Ψ-behaviour-on-𝕍-sets f)
        ⦅2⦆ = Φ-behaviour s
        ⦅3⦆ = 𝕍-set-ext _ _ (e₁ , e₂)
          {- The proof of e₂ and especially e₁ are the only hard parts. We set
             up two lemmas and some abbreviations to get e₁ and e₂. -}
         where
          c : (a : A) → Ord
          c a = Ψ (f a) +ₒ 𝟙ₒ
          abstract -- For performance
           u : (a : A) → ⟨ c a ⟩  → ⟨ s ⟩
           u a = pr₁ (sup-is-upper-bound _ a)

           IH' : (a : A) → Φ (Ψ (f a)) ＝ f a
           IH' a = IH a (being-set-theoretic-ordinal-is-hereditary σ
                          (to-∈-of-𝕍-set ∣ a , refl ∣))

           lemma₁ : (a : A) → Φ (c a ↓ inr ⋆) ＝ f a
           lemma₁ a = Φ (c a ↓ inr ⋆) ＝⟨ ap Φ ⦅e⦆ ⟩
                      Φ (Ψ (f a))     ＝⟨ IH' a            ⟩
                      f a             ∎
            where
             ⦅e⦆ : c a ↓ inr ⋆ ＝ Ψ (f a)
             ⦅e⦆ = +ₒ-𝟙ₒ-↓-right (Ψ (f a))

           lemma₂ : (a : A) → Φ (s ↓ u a (inr ⋆)) ＝ f a
           lemma₂ a = Φ (s ↓ u a (inr ⋆)) ＝⟨ ap Φ ⦅e⦆ ⟩
                      Φ (c a ↓ inr ⋆)     ＝⟨ lemma₁ a ⟩
                      f a                 ∎
            where
             ⦅e⦆ : s ↓ u a (inr ⋆) ＝ c a ↓ inr ⋆
             ⦅e⦆ = initial-segment-of-sup-at-component _ a (inr ⋆)

          e₂ : f ≲ (λ y → Φ (s ↓ y))
          e₂ a = ∣ u a (inr ⋆) , lemma₂ a ∣

          e₁ : (λ y → Φ (s ↓ y)) ≲ f
          e₁ y =
           ∥∥-rec ∃-is-prop h
            (initial-segment-of-sup-is-initial-segment-of-some-component _ y)
            where
             h : (Σ a ꞉ A , Σ x ꞉ ⟨ c a ⟩ , s ↓ y ＝ c a ↓ x)
               → ∃ a ꞉ A , f a ＝ Φ (s ↓ y)
             h (a , inr ⋆ , e) = ∣ a , (e' ⁻¹) ∣
              where
               e' = Φ (s ↓ y)       ＝⟨ ap Φ e ⟩
                    Φ (c a ↓ inr ⋆) ＝⟨ lemma₁ a ⟩
                    f a             ∎
             h (a , inl x , e) = goal
              where
               ∈-claim₁ : Φ (Ψ (f a) ↓ x) ∈ f a
               ∈-claim₁ = transport (Φ (Ψ (f a) ↓ x) ∈_)
                                    (IH' a)
                                    (Φ-preserves-strict-order
                                      (Ψ (f a) ↓ x)
                                      (Ψ (f a))
                                      (x , refl))
               ∈-claim₂ : Φ (Ψ (f a) ↓ x) ∈ 𝕍-set f
               ∈-claim₂ = transitive-set-if-set-theoretic-ordinal σ
                            (f a)
                            (Φ (Ψ (f a) ↓ x))
                            (to-∈-of-𝕍-set ∣ a , refl ∣)
                            ∈-claim₁

               goal : ∃ a' ꞉ A , f a' ＝ Φ (s ↓ y)
               goal = ∥∥-functor g (from-∈-of-𝕍-set ∈-claim₂)
                where
                 g : (Σ a' ꞉ A , f a' ＝ Φ (Ψ (f a) ↓ x))
                   → Σ a' ꞉ A , f a' ＝ Φ (s ↓ y)
                 g (a' , p) = (a' , q)
                  where
                   q = f a'            ＝⟨ p  ⟩
                       Φ (Ψ (f a) ↓ x) ＝⟨ e' ⟩
                       Φ (s ↓ y)       ∎
                    where
                     ↓-fact : c a ↓ inl x ＝ Ψ (f a) ↓ x
                     ↓-fact = +ₒ-↓-left x ⁻¹
                     e' = ap Φ (↓-fact ⁻¹ ∙ e ⁻¹)


  Ψᵒʳᵈ-is-section-of-Φᵒʳᵈ : Φᵒʳᵈ ∘ Ψᵒʳᵈ ∼ id
  Ψᵒʳᵈ-is-section-of-Φᵒʳᵈ (x , σ) =
   𝕍ᵒʳᵈ-is-subtype (Ψ-is-section-of-Φ x σ)

\end{code}

Finally we obtain the result that ordinal of type theoretic ordinals is
isomorphic to the (type theoretic) ordinal 𝕍ᴼᴿᴰ of set theoretic ordinals.

\begin{code}

  𝕍ᵒʳᵈ-isomorphic-to-Ord : OO 𝓤 ≃ₒ 𝕍ᴼᴿᴰ
  𝕍ᵒʳᵈ-isomorphic-to-Ord =
   Φᵒʳᵈ , order-preserving-reflecting-equivs-are-order-equivs
          (OO 𝓤) 𝕍ᴼᴿᴰ Φᵒʳᵈ
          Φᵒʳᵈ-is-equiv
          Φ-preserves-strict-order
          Φ-reflects-strict-order
    where
     Φᵒʳᵈ-is-split-surjective : (x : 𝕍ᵒʳᵈ) → Σ α ꞉ Ord , Φᵒʳᵈ α ＝ x
     Φᵒʳᵈ-is-split-surjective x = Ψᵒʳᵈ x , Ψᵒʳᵈ-is-section-of-Φᵒʳᵈ x
     Φᵒʳᵈ-is-equiv : is-equiv (Φᵒʳᵈ)
     Φᵒʳᵈ-is-equiv = lc-split-surjections-are-equivs
                     Φᵒʳᵈ
                     Φᵒʳᵈ-is-left-cancellable
                     Φᵒʳᵈ-is-split-surjective


\end{code}
