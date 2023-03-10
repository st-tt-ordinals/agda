We define the induction principle (with a non-judgemental computation principle)
of the cumulative hierarchy ð (with respect to a type universe ð¤) as introduced
in Section 10.5 of the HoTT Book. Using the induction principle we formulate
what it means for the cumulative hierarchy to exist, so that can use it as an
(module) assumption in further developments.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc

module CumulativeHierarchy
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.Base hiding (_â_)
open import UF.Subsingletons-FunExt

_â²_ : {A : ð¤ Ì } {B : ð¥ Ì } {X : ð£ Ì } â (A â X) â (B â X) â ð¤ â ð¥ â ð£ Ì
_â²_ {ð¤} {ð¥} {ð£} {A} {B} f g = (a : A) â â b ê B , g b ï¼ f a

-- Note that _â_ says that f and g have equal images
_â_ : {A : ð¤ Ì } {B : ð¥ Ì } {X : ð£ Ì } â (A â X) â (B â X) â ð¤ â ð¥ â ð£ Ì
f â g = f â² g Ã g â² f

â-sym : {A : ð¤ Ì } {B : ð¥ Ì } {X : ð£ Ì } {f : A â X} {g : B â X}
      â f â g â g â f
â-sym (u , v) = (v , u)

module _ (ð¤ : Universe) where

 is-large-set : ð¤ âº Ì â ð¤ âº Ì
 is-large-set = is-set

 record cumulative-hierarchy-exists : ð¤Ï where
  field
   ð : ð¤ âº Ì
   ð-is-large-set : is-large-set ð
   ð-set : {A : ð¤ Ì } â (A â ð) â ð
   ð-set-ext : {A B : ð¤ Ì } (f : A â ð) (g : B â ð) â f â g â ð-set f ï¼ ð-set g
   ð-induction : {ð£ : Universe} (P : ð â ð£ Ì )
               â ((x : ð) â is-set (P x))
               â (Ï : {A : ð¤ Ì } (f : A â ð ) â ((a : A) â P (f a)) â P (ð-set f))
               â ({A B : ð¤ Ì } (f : A â ð) (g : B â ð) (e : f â g)
                   â (IHâ : (a : A) â P (f a))
                   â (IHâ : (b : B) â P (g b))
                   â ((a : A) â â¥ Î£ b ê B , Î£ p ê f a ï¼ g b ,
                                    transport P p (IHâ a) ï¼ IHâ b â¥)
                   â ((b : B) â â¥ Î£ a ê A , Î£ p ê g b ï¼ f a ,
                                    transport P p (IHâ b) ï¼ IHâ a â¥)
                   â transport P (ð-set-ext f g e) (Ï f IHâ) ï¼ Ï g IHâ)
               â (x : ð) â P x
   ð-induction-computes : {ð£ : Universe} (P : ð â ð£ Ì )
                        â (Ï : (x : ð) â is-set (P x))
                        â (Ï : {A : ð¤ Ì } (f : A â ð ) â ((a : A) â P (f a))
                                                        â P (ð-set f))
                        â (Ï : {A B : ð¤ Ì } (f : A â ð) (g : B â ð) (e : f â g)
                             â (IHâ : (a : A) â P (f a))
                             â (IHâ : (b : B) â P (g b))
                             â ((a : A) â â¥ Î£ b ê B , Î£ p ê f a ï¼ g b ,
                                              transport P p (IHâ a) ï¼ IHâ b â¥)
                             â ((b : B) â â¥ Î£ a ê A , Î£ p ê g b ï¼ f a ,
                                              transport P p (IHâ b) ï¼ IHâ a â¥)
                             â transport P (ð-set-ext f g e) (Ï f IHâ) ï¼ Ï g IHâ)
                        â {A : ð¤ Ì } (f : A â ð) (IH : (a : A) â P (f a))
                           â ð-induction P Ï Ï Ï (ð-set f) ï¼ Ï f IH

\end{code}

Statements and proofs of some simpler, more specialised, induction and recursion
principles for ð.

We start with deriving the recursion principle for ð, i.e. its nondependent
induction principle. It should be noted that this is completely routine.

\begin{code}

  ð-recursion-with-computation :
     {ð£ : Universe} {X : ð£ Ì }
   â (Ï : is-set X)
   â (Ï : {A : ð¤ Ì } (f : A â ð) â (A â X) â X)
   â (Ï : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
        â (IHâ : A â X)
        â (IHâ : B â X)
        â ((a : A) â â¥ Î£ b ê B , Î£ p ê f a ï¼ g b , IHâ a ï¼ IHâ b â¥)
        â ((b : B) â â¥ Î£ a ê A , Î£ p ê g b ï¼ f a , IHâ b ï¼ IHâ a â¥)
        â f â g â Ï f IHâ ï¼ Ï g IHâ)
   â Î£ Ï ê (ð â X) , ({A : ð¤ Ì } (f : A â ð)
                      (IH : A â X) â Ï (ð-set f) ï¼ Ï f IH)
  ð-recursion-with-computation {ð£} {X} Ï Ï Ï =
   ( ð-induction (Î» _ â X) (Î» _ â Ï) Ï Ï'
   , ð-induction-computes (Î» _ â X) (Î» _ â Ï) Ï Ï')
      where
       Ï' : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
          â (e : f â g) (IHâ : A â X) (IHâ : B â X)
          â ((a : A) â â¥ Î£ b ê B , Î£ p ê f a ï¼ g b ,
                           transport (Î» _ â X) p (IHâ a) ï¼ IHâ b â¥)
          â ((b : B) â â¥ Î£ a ê A , Î£ p ê g b ï¼ f a ,
                           transport (Î» _ â X) p (IHâ b) ï¼ IHâ a â¥)
          â transport (Î» _ â X) (ð-set-ext f g e) (Ï f IHâ) ï¼ Ï g IHâ
       Ï' {A} {B} f g e IHâ IHâ hIHâ hIHâ =
        transport (Î» _ â X) e' (Ï f IHâ) ï¼â¨ transport-const e'          â©
        Ï f IHâ                          ï¼â¨ Ï f g IHâ IHâ hIHâ' hIHâ' e â©
        Ï g IHâ                          â
         where
          e' = ð-set-ext f g e
          hIHâ' : (a : A) â â¥ Î£ b ê B , Î£ p ê f a ï¼ g b , IHâ a ï¼ IHâ b â¥
          hIHâ' a = â¥â¥-functor
                     (Î» (b , p , q) â (b , p , ((transport-const p) â»Â¹ â q)))
                     (hIHâ a)
          hIHâ' : (b : B) â â¥ Î£ a ê A , Î£ p ê g b ï¼ f a , IHâ b ï¼ IHâ a â¥
          hIHâ' b = â¥â¥-functor
                     (Î» (a , p , q) â (a , p , ((transport-const p) â»Â¹ â q)))
                     (hIHâ b)

  ð-recursion : {ð£ : Universe} {X : ð£ Ì }
              â is-set X
              â (Ï : ({A : ð¤ Ì } (f : A â ð) â (A â X) â X))
              â ({A B : ð¤ Ì } (f : A â ð) (g : B â ð)
                  â (IHâ : A â X) (IHâ : B â X)
                  â ((a : A) â â¥ Î£ b ê B , Î£ p ê f a ï¼ g b , IHâ a ï¼ IHâ b â¥)
                  â ((b : B) â â¥ Î£ a ê A , Î£ p ê g b ï¼ f a , IHâ b ï¼ IHâ a â¥)
                  â f â g â Ï f IHâ ï¼ Ï g IHâ)
              â ð â X
  ð-recursion Ï Ï Ï = prâ (ð-recursion-with-computation Ï Ï Ï)

  ð-recursion-computes :
      {ð£ : Universe} {X : ð£ Ì }
    â (Ï : is-set X)
    â (Ï : {A : ð¤ Ì } (f : A â ð) â (A â X) â X)
    â (Ï : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
         â (IHâ : A â X) (IHâ : B â X)
         â ((a : A) â â¥ Î£ b ê B , Î£ p ê f a ï¼ g b , IHâ a ï¼ IHâ b â¥)
         â ((b : B) â â¥ Î£ a ê A , Î£ p ê g b ï¼ f a , IHâ b ï¼ IHâ a â¥)
         â f â g â Ï f IHâ ï¼ Ï g IHâ)
    â ({A : ð¤ Ì } (f : A â ð) (IH : A â X)
        â ð-recursion Ï Ï Ï (ð-set f) ï¼ Ï f IH)
  ð-recursion-computes Ï Ï Ï f = prâ (ð-recursion-with-computation Ï Ï Ï) f

\end{code}

Next, we observe that when P is a family of propositions, then the induction
principle simplifies significantly.

\begin{code}

  ð-prop-induction : {ð£ : Universe} (P : ð â ð£ Ì )
                   â ((x : ð) â is-prop (P x))
                   â ({A : ð¤ Ì } (f : A â ð) â ((a : A) â P (f a)) â P (ð-set f))
                   â (x : ð) â P x
  ð-prop-induction {ð£} P P-is-prop-valued Ï =
   ð-induction P (Î» x â props-are-sets (P-is-prop-valued x)) Ï
                 (Î» f g e IHâ IHâ _ _ â P-is-prop-valued _ _ _)


  ð-prop-simple-induction : {ð£ : Universe} (P : ð â ð£ Ì )
                          â ((x : ð) â is-prop (P x))
                          â ({A : ð¤ Ì } (f : A â ð) â P (ð-set f))
                          â (x : ð) â P x
  ð-prop-simple-induction P Ï Ï = ð-prop-induction P Ï (Î» f _ â Ï f)

\end{code}

Because implication makes the set Î© into a poset, we can give specialised
recursion principles for ð â Î© by (roughly) asking that â² is mapped to
implication.

\begin{code}

  private
   ð-prop-recursion-with-computation :
      {ð£ : Universe}
    â (Ï : ({A : ð¤ Ì } (f : A â ð) â (A â Î© ð£) â Î© ð£))
    â (Ï : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
         â (IHâ : A â Î© ð£) (IHâ : B â Î© ð£)
         â ((a : A) â â¥ Î£ b ê B , Î£ p ê f a ï¼ g b , IHâ a ï¼ IHâ b â¥)
         â f â² g â Ï f IHâ holds â Ï g IHâ holds)
    â Î£ Ï ê (ð â Î© ð£) , ({A : ð¤ Ì } (f : A â ð) (IH : A â Î© ð£)
                      â Ï (ð-set f) ï¼ Ï f IH)
   ð-prop-recursion-with-computation {ð£} Ï Ï =
    ( ð-recursion (Î©-is-set fe pe) Ï Ï'
    , ð-recursion-computes (Î©-is-set fe pe) Ï Ï')
     where
      Ï' : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
         â (IHâ : A â Î© ð£) (IHâ : B â Î© ð£)
         â ((a : A) â â¥ Î£ b ê B , Î£ p ê f a ï¼ g b , IHâ a ï¼ IHâ b â¥)
         â ((b : B) â â¥ Î£ a ê A , Î£ p ê g b ï¼ f a , IHâ b ï¼ IHâ a â¥)
         â f â g â Ï f IHâ ï¼ Ï g IHâ
      Ï' f g IHâ IHâ hIHâ hIHâ (mâ , mâ) =
       Î©-extensionality fe pe (Ï f g IHâ IHâ hIHâ mâ)
                              (Ï g f IHâ IHâ hIHâ mâ)

  ð-prop-recursion : {ð£ : Universe}
                   â (Ï : ({A : ð¤ Ì } (f : A â ð) â (A â Î© ð£) â Î© ð£))
                   â ({A B : ð¤ Ì } (f : A â ð) (g : B â ð)
                       â (IHâ : A â Î© ð£) (IHâ : B â Î© ð£)
                       â ((a : A) â â¥ Î£ b ê B ,
                                      Î£ p ê f a ï¼ g b , IHâ a ï¼ IHâ b â¥)
                     â f â² g â Ï f IHâ holds â Ï g IHâ holds)
                   â ð â Î© ð£
  ð-prop-recursion {ð£} Ï Ï =
   prâ (ð-prop-recursion-with-computation Ï Ï)

  ð-prop-recursion-computes : {ð£ : Universe}
                            â (Ï : ({A : ð¤ Ì } (f : A â ð) â (A â Î© ð£) â Î© ð£))
                            â (Ï : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
                                 â (IHâ : A â Î© ð£) (IHâ : B â Î© ð£)
                                 â ((a : A) â â¥ Î£ b ê B , Î£ p ê f a ï¼ g b ,
                                                  IHâ a ï¼ IHâ b â¥)
                                 â f â² g â Ï f IHâ holds â Ï g IHâ holds)
                            â ({A : ð¤ Ì } (f : A â ð) (IH : A â Î© ð£)
                              â ð-prop-recursion Ï Ï (ð-set f) ï¼ Ï f IH)
  ð-prop-recursion-computes Ï Ï f =
   prâ (ð-prop-recursion-with-computation Ï Ï) f

\end{code}

We also have a simpler version of the above in the case that we don't need to
make recursive calls.

\begin{code}

  ð-prop-simple-recursion : {ð£ : Universe}
                          â (Ï : ({A : ð¤ Ì } â (A â ð) â Î© ð£))
                          â ({A B : ð¤ Ì } (f : A â ð) (g : B â ð)
                            â f â² g â Ï f holds â Ï g holds)
                          â ð â Î© ð£
  ð-prop-simple-recursion {ð£} Ï Ï =
   ð-prop-recursion (Î» f _ â Ï f) (Î» f g _ _ _ â Ï f g)

  ð-prop-simple-recursion-computes :
      {ð£ : Universe}
    â (Ï : ({A : ð¤ Ì } â (A â ð) â Î© ð£))
    â (Ï : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
         â f â² g â Ï f holds â Ï g holds)
    â ({A : ð¤ Ì } (f : A â ð) â ð-prop-simple-recursion Ï Ï (ð-set f) ï¼ Ï f)
  ð-prop-simple-recursion-computes Ï Ï f =
   ð-prop-recursion-computes (Î» f _ â Ï f) (Î» f g _ _ _ â Ï f g)
                             f (Î» _ â ð , ð-is-prop)

\end{code}

Basic constructions and proofs for ð, i.e. the definition of set membership (â),
subset relation (â) and proofs of â-extensionality and â-induction.

\begin{code}

  _â[Î©]_ : ð â ð â Î© (ð¤ âº)
  _â[Î©]_ x = ð-prop-simple-recursion
              (Î» {A} f â (â a ê A , f a ï¼ x) , â-is-prop) e
   where
    e : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
      â f â² g â (â a ê A , f a ï¼ x) â (â b ê B , g b ï¼ x)
    e {A} {B} f g s = â¥â¥-rec â-is-prop
                             (Î» (a , p)
                                â â¥â¥-functor (Î» (b , q)
                                                â b , (q â p)) (s a))

  _â_ : ð â ð â ð¤ âº Ì
  x â y = (x â[Î©] y) holds

  â-is-prop-valued : {x y : ð} â is-prop (x â y)
  â-is-prop-valued {x} {y} = holds-is-prop (x â[Î©] y)

  â-for-ð-sets : (x : ð) {A : ð¤ Ì } (f : A â ð)
               â (x â ð-set f) ï¼ (â a ê A , f a ï¼ x)
  â-for-ð-sets x f = ap prâ (ð-prop-simple-recursion-computes _ _ f)

  from-â-of-ð-set : {x : ð} {A : ð¤ Ì } {f : A â ð}
                    â (x â ð-set f) â (â a ê A , f a ï¼ x)
  from-â-of-ð-set {x} {A} {f} = Idtofun (â-for-ð-sets x f)

  to-â-of-ð-set : {x : ð} {A : ð¤ Ì } {f : A â ð}
                  â (â a ê A , f a ï¼ x) â (x â ð-set f)
  to-â-of-ð-set {x} {A} {f} = back-Idtofun (â-for-ð-sets x f)

  _â_ : ð â ð â ð¤ âº Ì
  x â y = (v : ð) â v â x â v â y

  â-to-â² : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
         â ð-set f â ð-set g â f â² g
  â-to-â² {A} {B} f g s a = from-â-of-ð-set m
   where
    m : f a â ð-set g
    m = s (f a) (to-â-of-ð-set â£ a , refl â£)

  â²-to-â : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
         â f â² g â ð-set f â ð-set g
  â²-to-â {A} {B} f g s x m = to-â-of-ð-set n
   where
    m' : â a ê A , f a ï¼ x
    m' = from-â-of-ð-set m
    n : â b ê B , g b ï¼ x
    n = â¥â¥-rec â-is-prop
               (Î» (a , p) â â¥â¥-functor (Î» (b , q) â b , (q â p)) (s a)) m'

  â-is-prop-valued : {x y : ð} â is-prop (x â y)
  â-is-prop-valued = Î â-is-prop fe (Î» _ _ â â-is-prop-valued)

  â-is-reflexive : {x : ð} â x â x
  â-is-reflexive _ = id

  ï¼-to-â : {x y : ð} â x ï¼ y â x â y
  ï¼-to-â refl = â-is-reflexive

\end{code}

We now prove, using the induction principles of ð above, two simple
set-theoretic axioms: â-extensionality and â-induction.

\begin{code}

  pre-extensionality : {A : ð¤ Ì } (f : A â ð) (x : ð)
                     â x â ð-set f â ð-set f â x â x ï¼ ð-set f
  pre-extensionality f =
   ð-prop-simple-induction (Î» x â x â ð-set f â ð-set f â x â x ï¼ ð-set f)
                           (Î» _ â Î â-is-prop fe (Î» _ _ â ð-is-large-set))
                           Î³
    where
     Î³ : {B : ð¤ Ì  } (g : B â ð)
       â ð-set g â ð-set f â ð-set f â ð-set g â ð-set g ï¼ ð-set f
     Î³ g s t = ð-set-ext g f (â-to-â² g f s , â-to-â² f g t)

  â-extensionality : (x y : ð) â x â y â y â x â x ï¼ y
  â-extensionality x y =
   ð-prop-simple-induction (Î» v â x â v â v â x â x ï¼ v)
                           (Î» _ â Î â-is-prop fe (Î» _ _ â ð-is-large-set))
                           (Î» f â pre-extensionality f x)
                           y

  â-induction : {ð£ : Universe} (P : ð â ð£ Ì )
              â ((x : ð) â is-prop (P x))
              â ((x : ð) â ((y : ð) â y â x â P y) â P x)
              â (x : ð) â P x
  â-induction P P-is-prop-valued h = ð-prop-induction P P-is-prop-valued Î³
   where
    Î³ : {A : ð¤ Ì } (f : A â ð) â ((a : A) â P (f a)) â P (ð-set f)
    Î³ {A} f IH = h (ð-set f) c
     where
      c : (y : ð) â y â ð-set f â P y
      c y m = â¥â¥-rec (P-is-prop-valued y) (Î» (a , p) â transport P p (IH a)) m'
       where
        m' : â a ê A , f a ï¼ y
        m' = from-â-of-ð-set m

\end{code}
