We show that ð is locally small, following Section 10.5 of the HoTT Book.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc

module CumulativeHierarchy-LocallySmall
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import MLTT.Spartan
open import UF.Base hiding (_â_)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Equiv-FunExt
open import UF.Logic
open import UF.Size
open import UF.Subsingletons-FunExt

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

The idea is to have a ð¤-valued equality relation on ð by defining:
  ð-set {A} f ï¼â» ð-set {B} g
inductively as
    (Î  a : A , â b : B , f a ï¼â» g b)
  Ã (Î  b : B , â a : A , g b ï¼â» f a).

Of course, we need to formally check that this definition respects the ð-set-ext
constructor of ð in both arguments, which is provided by the setup below.

\begin{code}

open import CumulativeHierarchy pt fe pe

module ð-is-locally-small
        {ð¤ : Universe}
        (ch : cumulative-hierarchy-exists ð¤)
       where

 open cumulative-hierarchy-exists ch

 private
  module _
          {A : ð¤ Ì }
          (f : A â ð)
          (r : A â ð â Î© ð¤)
         where

   ï¼â»-auxâ : {B : ð¤ Ì } â (B â ð) â Î© ð¤
   ï¼â»-auxâ {B} g = (â±¯ a â¶ A , Æ b â¶ B , r a (g b) holds)
                  â§ (â±¯ b â¶ B , Æ a â¶ A , r a (g b) holds)

   ï¼â»-auxâ-respects-â : {B' B : ð¤ Ì} (g' : B' â ð) (g : B â ð)
                       â g' â g
                       â ï¼â»-auxâ g' holds
                       â ï¼â»-auxâ g  holds
   ï¼â»-auxâ-respects-â {B'} {B} g' g (s , t) (u , v) = â¦1â¦ , â¦2â¦
    where
     â¦1â¦ : (a : A) â â b ê B , r a (g b) holds
     â¦1â¦ a = â¥â¥-rec â-is-prop hâ (u a)
      where
       hâ : (Î£ b' ê B' , r a (g' b') holds) â â b ê B , r a (g b) holds
       hâ (b' , p) = â¥â¥-functor hâ (s b')
        where
         hâ : (Î£ b ê B , g b ï¼ g' b') â Î£ b ê B , r a (g b) holds
         hâ (b , e) = b , transport (Î» - â (r a -) holds) (e â»Â¹) p
     â¦2â¦ : (b : B) â â a ê A , r a (g b) holds
     â¦2â¦ b = â¥â¥-rec â-is-prop hâ (t b)
      where
       hâ : (Î£ b' ê B' , g' b' ï¼ g b) â â a ê A , r a (g b) holds
       hâ (b' , e) = â¥â¥-functor hâ (v b')
        where
         hâ : (Î£ a ê A , r a (g' b') holds) â Î£ a ê A , r a (g b) holds
         hâ (a , p) = a , transport (Î» - â (r a -) holds) e p

   ï¼â»-auxâ-respects-â' : {B' B : ð¤ Ì} (g' : B' â ð) (g : B â ð)
                        â g' â g
                        â ï¼â»-auxâ g' ï¼ ï¼â»-auxâ g
   ï¼â»-auxâ-respects-â' {B'} {B} g' g e =
    Î©-extensionality fe pe
     (ï¼â»-auxâ-respects-â g' g e)
     (ï¼â»-auxâ-respects-â g g' (â-sym e))

   ï¼â»-auxâ : ð â Î© ð¤
   ï¼â»-auxâ = ð-recursion (Î©-is-set fe pe) (Î» g _ â ï¼â»-auxâ g)
                          (Î» g' g _ _ _ _ e â ï¼â»-auxâ-respects-â' g' g e)

   ï¼â»-auxâ-behaviour : {B : ð¤ Ì } (g : B â ð) â ï¼â»-auxâ (ð-set g) ï¼ ï¼â»-auxâ g
   ï¼â»-auxâ-behaviour g =
    ð-recursion-computes (Î©-is-set fe pe) (Î» gâ _ â ï¼â»-auxâ gâ)
                         (Î» g' g _ _ _ _ e â ï¼â»-auxâ-respects-â' g' g e)
                         g (Î» _ â ð , ð-is-prop)

  ï¼â»-auxâ-respects-â : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
                      â (râ : A â ð â Î© ð¤) (râ : B â ð â Î© ð¤)
                      â ((a : A) â â b ê B , (f a ï¼ g b) Ã (râ a ï¼ râ b))
                      â ((b : B) â â a ê A , (g b ï¼ f a) Ã (râ b ï¼ râ a))
                      â {C : ð¤ Ì } (h : C â ð)
                      â ï¼â»-auxâ f râ h holds
                      â ï¼â»-auxâ g râ h holds
  ï¼â»-auxâ-respects-â {A} {B} f g râ râ s t {C} h (u , v) = â¦1â¦ , â¦2â¦
   where
    â¦1â¦ : (b : B) â â c ê C , râ b (h c) holds
    â¦1â¦ b = â¥â¥-rec â-is-prop m (t b)
     where
      m : (Î£ a ê A , (g b ï¼ f a) Ã (râ b ï¼ râ a))
        â â c ê C , râ b (h c) holds
      m (a , _ , q) = â¥â¥-functor n (u a)
       where
        n : (Î£ c ê C , râ a (h c) holds)
          â Î£ c ê C , râ b (h c) holds
        n (c , w) = c , Idtofun (ap _holds (happly (q â»Â¹) (h c))) w
    â¦2â¦ : (c : C) â â b ê B , râ b (h c) holds
    â¦2â¦ c = â¥â¥-rec â-is-prop n (v c)
     where
      n : (Î£ a ê A , râ a (h c) holds)
        â â b ê B , râ b (h c) holds
      n (a , w) = â¥â¥-functor m (s a)
       where
        m : (Î£ b ê B , (f a ï¼ g b) Ã (râ a ï¼ râ b))
          â Î£ b ê B , râ b (h c) holds
        m (b , _ , q) = b , Idtofun (ap _holds (happly q (h c))) w

  ï¼â»-auxâ-respects-â' : {A B : ð¤ Ì} (f : A â ð) (g : B â ð)
                         (râ : A â ð â Î© ð¤) (râ : B â ð â Î© ð¤)
                       â ((a : A) â â b ê B , (f a ï¼ g b) Ã (râ a ï¼ râ b))
                       â ((b : B) â â a ê A , (g b ï¼ f a) Ã (râ b ï¼ râ a))
                       â f â g
                       â ï¼â»-auxâ f râ ï¼ ï¼â»-auxâ g râ
  ï¼â»-auxâ-respects-â' {A} {B} f g râ râ IHâ IHâ _ =
   dfunext fe (ð-prop-simple-induction (Î» x â ï¼â»-auxâ f râ x ï¼ ï¼â»-auxâ g râ x)
                                       (Î» _ â Î©-is-set fe pe)
                                       Ï)
    where
     Ï : {C : ð¤ Ì } (h : C â ð)
       â ï¼â»-auxâ f râ (ð-set h) ï¼ ï¼â»-auxâ g râ (ð-set h)
     Ï h = ï¼â»-auxâ f râ (ð-set h) ï¼â¨ ï¼â»-auxâ-behaviour f râ h      â©
           ï¼â»-auxâ f râ h         ï¼â¨ e                              â©
           ï¼â»-auxâ g râ h         ï¼â¨ (ï¼â»-auxâ-behaviour g râ h) â»Â¹ â©
           ï¼â»-auxâ g râ (ð-set h) â
      where
       e = Î©-extensionality fe pe
            (ï¼â»-auxâ-respects-â f g râ râ IHâ IHâ h)
            (ï¼â»-auxâ-respects-â g f râ râ IHâ IHâ h)

\end{code}

We package up the above in the following definition which records the behaviour
of the relation on the ð-set constructor.

\begin{code}

  ï¼â»[Î©]-packaged : Î£ Ï ê (ð â ð â Î© ð¤) , ({A : ð¤ Ì} (f : A â ð)
                                           (r : A â ð â Î© ð¤)
                                        â Ï (ð-set f) ï¼ ï¼â»-auxâ f r)
  ï¼â»[Î©]-packaged = ð-recursion-with-computation
                     (Î -is-set fe (Î» _ â Î©-is-set fe pe))
                     ï¼â»-auxâ
                     ï¼â»-auxâ-respects-â'

 _ï¼â»[Î©]_ : ð â ð â Î© ð¤
 _ï¼â»[Î©]_ = prâ ï¼â»[Î©]-packaged

 _ï¼â»_ : ð â ð â ð¤ Ì
 x ï¼â» y = (x ï¼â»[Î©] y) holds

 ï¼â»-is-prop-valued : {x y : ð} â is-prop (x ï¼â» y)
 ï¼â»-is-prop-valued {x} {y} = holds-is-prop (x ï¼â»[Î©] y)

\end{code}

The following lemma shows that the relation ï¼â» indeed implements the idea
announced in the comment above.

\begin{code}

 private
  ï¼â»-behaviour : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
               â (ð-set f ï¼â» ð-set g)
               ï¼ ( ((a : A) â â b ê B , f a ï¼â» g b)
                  Ã ((b : B) â â a ê A , f a ï¼â» g b))
  ï¼â»-behaviour {A} {B} f g =
   (ð-set f ï¼â» ð-set g)          ï¼â¨ â¦1â¦ â©
   (ï¼â»-auxâ f r (ð-set g) holds) ï¼â¨ â¦2â¦ â©
   T                              â
    where
     T : ð¤ Ì
     T = ((a : A) â â b ê B , f a ï¼â» g b)
       Ã ((b : B) â â a ê A , f a ï¼â» g b)
     r : A â ð â Î© ð¤
     r a y = f a ï¼â»[Î©] y
     â¦1â¦ = ap _holds (happly (prâ ï¼â»[Î©]-packaged f r) (ð-set g))
     â¦2â¦ = ap _holds (ï¼â»-auxâ-behaviour f r g)

\end{code}

Finally, we show that ï¼â» and ï¼ are equivalent, making ð a locally small type.

\begin{code}

 ï¼â»-to-ï¼ : {x y : ð} â x ï¼â» y â x ï¼ y
 ï¼â»-to-ï¼ {x} {y} =
  ð-prop-induction (Î» u â ((v : ð) â u ï¼â» v â u ï¼ v))
                   (Î» _ â Î â-is-prop fe (Î» _ _ â ð-is-large-set))
                   (Î» {A} f r â ð-prop-simple-induction _
                                 (Î» _ â Î -is-prop fe (Î» _ â ð-is-large-set))
                                 (Î» {B} g â h f g r))
                   x y
   where
    h : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
      â ((a : A) (v : ð) â f a ï¼â» v â f a ï¼ v)
      â ð-set f ï¼â» ð-set g â ð-set f ï¼ ð-set g
    h {A} {B} f g r e = ð-set-ext f g (â¦1â¦ , â¦2â¦)
     where
      u : (a : A) â â b ê B , f a ï¼â» g b
      u = prâ (Idtofun (ï¼â»-behaviour f g) e)
      v : (b : B)Â â â a ê A , f a ï¼â» g b
      v = prâ (Idtofun (ï¼â»-behaviour f g) e)
      â¦1â¦ : (a : A) â â b ê B , g b ï¼ f a
      â¦1â¦ a = â¥â¥-functor (Î» (b , p) â b , ((r a (g b) p) â»Â¹)) (u a)
      â¦2â¦ : (b : B) â â a ê A , f a ï¼ g b
      â¦2â¦ b = â¥â¥-functor (Î» (a , p) â a , r a (g b) p) (v b)

 ï¼â»-is-reflexive : {x : ð} â x ï¼â» x
 ï¼â»-is-reflexive {x} = ð-prop-induction (Î» - â - ï¼â» -)
                                         (Î» _ â ï¼â»-is-prop-valued)
                                         h x
  where
   h : {A : ð¤ Ì } (f : A â ð)
     â ((a : A) â f a ï¼â» f a)
     â ð-set f ï¼â» ð-set f
   h {A} f r = back-Idtofun (ï¼â»-behaviour f f)
                            ((Î» a â â£ a , r a â£) , (Î» a â â£ a , r a â£))

 ï¼-to-ï¼â» : {x y : ð} â x ï¼ y â x ï¼â» y
 ï¼-to-ï¼â» refl = ï¼â»-is-reflexive

 ï¼â»-â-ï¼ : {x y : ð} â (x ï¼â» y) â (x ï¼ y)
 ï¼â»-â-ï¼ = logically-equivalent-props-are-equivalent
             ï¼â»-is-prop-valued
             ð-is-large-set
             ï¼â»-to-ï¼
             ï¼-to-ï¼â»

 ð-is-locally-small : is-locally-small ð
 ð-is-locally-small x y = (x ï¼â» y) , ï¼â»-â-ï¼

 ï¼â»-is-transitive : {x y z : ð} â x ï¼â» y â y ï¼â» z â x ï¼â» z
 ï¼â»-is-transitive {x} {y} {z} u v = ï¼-to-ï¼â» (ï¼â»-to-ï¼ u â ï¼â»-to-ï¼ v)

 ï¼â»-is-symmetric : {x y : ð} â x ï¼â» y â y ï¼â» x
 ï¼â»-is-symmetric {x} {y} e = ï¼-to-ï¼â» ((ï¼â»-to-ï¼ e)â»Â¹)

\end{code}

We now make use of the fact that ð is locally small by introducing a
small-valued membership relation on ð.

\begin{code}

 _ââ»[Î©]_ : ð â ð â Î© ð¤
 _ââ»[Î©]_ x = ð-prop-simple-recursion
              (Î» {A} f â (â a ê A , f a ï¼â» x) , â-is-prop) e
  where
   e : {A B : ð¤ Ì } (f : A â ð) (g : B â ð)
     â f â² g â (â a ê A , f a ï¼â» x) â (â b ê B , g b ï¼â» x)
   e {A} {B} f g s =
    â¥â¥-rec â-is-prop
           (Î» (a , p) â â¥â¥-functor (Î» (b , q)
                                      â b , ï¼-to-ï¼â» (q â ï¼â»-to-ï¼ p))
                                   (s a))

 _ââ»_ : ð â ð â ð¤  Ì
 x ââ» y = (x ââ»[Î©] y) holds

 ââ»-for-ð-sets : (x : ð) {A : ð¤ Ì } (f : A â ð)
               â (x ââ» ð-set f) ï¼ (â a ê A , f a ï¼â» x)
 ââ»-for-ð-sets x f = ap prâ (ð-prop-simple-recursion-computes _ _ f)

 ââ»-is-prop-valued : {x y : ð} â is-prop (x ââ» y)
 ââ»-is-prop-valued {x} {y} = holds-is-prop (x ââ»[Î©] y)

 ââ»-â-â : {x y : ð} â x ââ» y â x â y
 ââ»-â-â {x} {y} =
  ð-prop-simple-induction _ (Î» _ â â-is-prop (Î» _ _ â fe) â-is-prop-valued) h y
   where
    h : {A : ð¤ Ì } (f : A â ð) â (x ââ» ð-set f) â (x â ð-set f)
    h {A} f = x ââ» ð-set f          ââ¨ â¦1â¦ â©
              (â a ê A , f a ï¼â» x) ââ¨ â¦2â¦ â©
              (â a ê A , f a ï¼ x)  ââ¨ â¦3â¦ â©
              x â ð-set f           â 
     where
      â¦1â¦ = idtoeq _ _ (ââ»-for-ð-sets x f)
      â¦2â¦ = â-cong pt (Î» a â ï¼â»-â-ï¼)
      â¦3â¦ = idtoeq _ _ ((â-for-ð-sets x f) â»Â¹)

 ââ»-to-â : {x y : ð} â x ââ» y â x â y
 ââ»-to-â {x} {y} = â ââ»-â-â â

 â-to-ââ» : {x y : ð} â x â y â x ââ» y
 â-to-ââ» {x} {y} = â ââ»-â-â ââ»Â¹

\end{code}
