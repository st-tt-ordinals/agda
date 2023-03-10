\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan

open import UF.PropTrunc
open import UF.Univalence

module OrdinalCumulativeHierarchy-Addendum
        (pt : propositional-truncations-exist)
        (ua : Univalence)
        (ð¤ : Universe)
       where

open import UF.Base hiding (_â_)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.ImageAndSurjection pt
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient hiding (is-prop-valued)
open import UF.UA-FunExt

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
open import OrdinalCumulativeHierarchy pt ua ð¤

open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.WellOrderTransport fe'
open import Ordinals.Underlying

module _
        (ch : cumulative-hierarchy-exists ð¤)
       where

 open cumulative-hierarchy-exists ch

 open ð-is-locally-small ch
 open ordinal-of-set-theoretic-ordinals ch

\end{code}

We start by showing that the total space (Î£ y ê ð , y â x) of a set theoretic
ordinal x is a (large) type theoretic ordinal when ordered by membership.

\begin{code}

 module total-space-of-an-element-of-ð
         (x : ð)
         (Ï : is-set-theoretic-ordinal x)
        where

  ðx : ð¤ âº Ì
  ðx = Î£ y ê ð , y â x

  _ââ_ : ðx â ðx â ð¤ âº Ì
  u ââ v = prâ u â prâ v

  ââ-is-prop-valued : is-prop-valued _ââ_
  ââ-is-prop-valued u v = â-is-prop-valued

  ââ-is-transitive : is-transitive _ââ_
  ââ-is-transitive u v w m n =
   transitive-set-if-set-theoretic-ordinal
    (being-set-theoretic-ordinal-is-hereditary Ï (prâ w)) (prâ v) (prâ u) n m

  ââ-is-extensional : is-extensional _ââ_
  ââ-is-extensional u v s t =
   to-subtype-ï¼ (Î» _ â â-is-prop-valued)
                (â-extensionality (prâ u) (prâ v) s' t')
    where
     s' : prâ u â prâ v
     s' y y-in-u = s (y , Ï) y-in-u
      where
       Ï : y â x
       Ï = transitive-set-if-set-theoretic-ordinal Ï (prâ u) y (prâ u) y-in-u
     t' : prâ v â prâ u
     t' y y-in-v = t (y , Ï) y-in-v
      where
       Ï : y â x
       Ï = transitive-set-if-set-theoretic-ordinal Ï (prâ v) y (prâ v) y-in-v

  ââ-is-well-founded : is-well-founded _ââ_
  ââ-is-well-founded = Î» (y , m) â Ï y m
   where
    Ï : (y : ð) (m : y â x) â is-accessible _ââ_ (y , m)
    Ï = transfinite-induction _â_ â-is-well-founded _ h
     where
      h : (y : ð)
        â ((u : ð) â u â y â (m : u â x) â is-accessible _ââ_ (u , m))
        â (m : y â x) â is-accessible _ââ_ (y , m)
      h y IH m = step (Î» (u , u-in-x) u-in-y â IH u u-in-y u-in-x)

  ðxáµÊ³áµ : Ordinal (ð¤ âº)
  ðxáµÊ³áµ = ðx , _ââ_ , ââ-is-prop-valued , ââ-is-well-founded
                    , ââ-is-extensional , ââ-is-transitive

  total-spaceáµÊ³áµ : Ordinal (ð¤ âº)
  total-spaceáµÊ³áµ = ðxáµÊ³áµ

\end{code}

Because being an set theoretic ordinal is hereditary the total spaces
  (Î£ y ê ð , y â x) and (Î£ y ê ðáµÊ³áµ , y âáµÊ³áµ (x , Ï))
are equivalent, as we record below.

\begin{code}

  ðx-restricted-to-ðáµÊ³áµ : ð¤ âº Ì
  ðx-restricted-to-ðáµÊ³áµ = Î£ y ê ðáµÊ³áµ , y âáµÊ³áµ (x , Ï)

  ðx-restricted-to-ðáµÊ³áµ-â-ðx : ðx-restricted-to-ðáµÊ³áµ â ðx
  ðx-restricted-to-ðáµÊ³áµ-â-ðx = qinveq f (g , Î· , Îµ)
   where
    f : ðx-restricted-to-ðáµÊ³áµ â ðx
    f ((y , _) , m) = y , m
    g : ðx â ðx-restricted-to-ðáµÊ³áµ
    g (y , m) = (y , (being-set-theoretic-ordinal-is-hereditary Ï m)) , m
    Îµ : f â g â¼ id
    Îµ (y , m) = to-subtype-ï¼ (Î» _ â â-is-prop-valued) refl
    Î· : g â f â¼ id
    Î· ((y , Ï) , m) =
     to-subtype-ï¼ (Î» _ â â-is-prop-valued)
                   (to-subtype-ï¼ (Î» _ â being-set-theoretic-ordinal-is-prop)
                                  refl)

\end{code}

When x = ð-set f, then the total space of x is equivalent to the image f,
because y â ð-set f if and only if y is in the image of f.

\begin{code}

 module total-space-of-ð-set
         (sq : set-quotients-exist)
         {A : ð¤ Ì }
         (f : A â ð)
         (Ï : is-set-theoretic-ordinal (ð-set f))
        where

  private
   x = ð-set f

  open total-space-of-an-element-of-ð x Ï
  open set-quotients-exist sq

  ðx-â-image-f : ðx â image f
  ðx-â-image-f = Î£-cong h
   where
    h : (y : ð) â (y â x) â y âimage f
    h y = logically-equivalent-props-are-equivalent
           â-is-prop-valued
           (being-in-the-image-is-prop y f)
           from-â-of-ð-set
           to-â-of-ð-set

\end{code}

The well order on the total space induces a well order on the image of f.

\begin{code}

  private
   transfer : Î£ s ê OrdinalStructure (image f) , (image f , s) ââ ðxáµÊ³áµ
   transfer = transfer-structure (image f) ðxáµÊ³áµ
               (â-sym ðx-â-image-f)
               (_ââ_ , (Î» u v â â-refl (u ââ v)))

  image-fáµÊ³áµ : Ordinal (ð¤ âº)
  image-fáµÊ³áµ = image f , prâ transfer

  ðxáµÊ³áµ-â-image-fáµÊ³áµ : ðxáµÊ³áµ ââ image-fáµÊ³áµ
  ðxáµÊ³áµ-â-image-fáµÊ³áµ = ââ-sym _ _ (prâ transfer)

\end{code}

We show that the relation âº on A/~ defined by [ a ] âº [ a' ] := f a â f a' makes
this quotient into a type theoretic ordinal that moreover is isomorphic to the
ordinal image-fáµÊ³áµ.

Note that because equality on ð and â take values in ð¤ âº, this quotient
construction yields an ordinal in ð¤ âº. We present a resized small-valued
variation of this construction below to get a quotient that lives in ð¤, rather
than ð¤ âº.

NB: We use the word "resized" here to indicate that we have a small type/ordinal
equivalent to a large one. We do *not* use resizing axioms.

\begin{code}

 module ð-set-carrier-quotient
         (sq : set-quotients-exist)
         {A : ð¤ Ì }
         (f : A â ð)
        where

  open set-quotients-exist sq
  open extending-relations-to-quotient fe pe

  _~_ : A â A â ð¤ âº Ì
  a ~ b = f a ï¼ f b

  ~EqRel : EqRel A
  ~EqRel = _~_ , (Î» a b â ð-is-large-set)
               , (Î» a â refl)
               , (Î» a b e â e â»Â¹)
               , (Î» a b c eâ eâ â eâ â eâ)

  A/~ : ð¤ âº Ì
  A/~ = A / ~EqRel

  [_] : A â A/~
  [_] = Î·/ ~EqRel

  _âº[Î©]_ : A/~ â A/~ â Î© (ð¤ âº)
  _âº[Î©]_ = extension-relâ ~EqRel (Î» a b â f a â[Î©] f b) Ï
   where
    Ï : {a b a' b' : A}
      â a ~ a' â b ~ b' â f a â[Î©] f b ï¼ f a' â[Î©] f b'
    Ï {a} {b} {a'} {b'} e e' =
     Î©-extensionality fe pe (transportâ _â_ e e')
                            (transportâ _â_ (e â»Â¹) (e' â»Â¹))

  _âº_ : A/~ â A/~ â ð¤ âº Ì
  a âº b = (a âº[Î©] b) holds

  âº-is-prop-valued : is-prop-valued _âº_
  âº-is-prop-valued a b = holds-is-prop (a âº[Î©] b)

  âº-ï¼-â : {a b : A} â [ a ] âº [ b ] ï¼ f a â f b
  âº-ï¼-â {a} {b} = ap (_holds) (extension-rel-triangleâ ~EqRel _ _ a b)

  â-to-âº : {a b : A} â f a â f b â [ a ] âº [ b ]
  â-to-âº = back-Idtofun âº-ï¼-â

  âº-to-â : {a b : A} â [ a ] âº [ b ] â f a â f b
  âº-to-â = Idtofun âº-ï¼-â

  âº-is-transitive : is-set-theoretic-ordinal (ð-set f)
                  â is-transitive _âº_
  âº-is-transitive Ï = /-inductionâ fe ~EqRel prop-valued trans
    where
     prop-valued : (x y z : A / ~EqRel) â is-prop (x âº y â y âº z â x âº z)
     prop-valued x y z = Î â-is-prop fe (Î» _ _ â âº-is-prop-valued x z)
     trans : (a b c : A) â [ a ] âº [ b ] â [ b ] âº [ c ] â [ a ] âº [ c ]
     trans a b c m n = â-to-âº (Ï (f a) (âº-to-â n) (âº-to-â m))
      where
       Ï : (v : ð) â f b â f c â v â f b â v â f c
       Ï = transitive-set-if-element-of-set-theoretic-ordinal Ï
            (to-â-of-ð-set â£ c , refl â£) (f b)

  âº-is-extensional : is-transitive-set (ð-set f)
                   â is-extensional _âº_
  âº-is-extensional Ï =
   /-inductionâ fe ~EqRel (Î» x y â Î â-is-prop fe (Î» _ _ â /-is-set ~EqRel))
                ext
    where
     ext : (a b : A)
         â ((x : A/~) â x âº [ a ] â x âº [ b ])
         â ((x : A/~) â x âº [ b ] â x âº [ a ])
         â [ a ] ï¼ [ b ]
     ext a b s t = Î·/-identifies-related-points ~EqRel e'
      where
       e' : a ~ b
       e' = â-extensionality (f a) (f b) s' t'
        where
         lem : (x : ð) (c : A) â x â f c â â d ê A , f d ï¼ x
         lem x c m = from-â-of-ð-set (Ï (f c) x (to-â-of-ð-set â£ c , refl â£) m)
         s' : f a â f b
         s' x m = â¥â¥-rec â-is-prop-valued h (lem x a m)
          where
           h : (Î£ c ê A , f c ï¼ x) â x â f b
           h (c , refl) = âº-to-â (s [ c ] (â-to-âº m))
         t' : f b â f a
         t' x m = â¥â¥-rec â-is-prop-valued h (lem x b m)
          where
           h : (Î£ c ê A , f c ï¼ x) â x â f a
           h (c , refl) = âº-to-â (t [ c ] (â-to-âº m))

  âº-is-well-founded : is-well-founded _âº_
  âº-is-well-founded = /-induction ~EqRel acc-is-prop acc
   where
    acc-is-prop : (x : A/~) â is-prop (is-accessible _âº_ x)
    acc-is-prop = accessibility-is-prop _âº_ fe'
    acc' : (x : ð) â ((a : A) â f a ï¼ x â is-accessible _âº_ [ a ])
    acc' = transfinite-induction _â_ â-is-well-founded _ h
     where
      h : (x : ð)
        â ((y : ð) â y â x â (a : A) â f a ï¼ y â is-accessible _âº_ [ a ])
        â (a : A) â f a ï¼ x â is-accessible _âº_ [ a ]
      h x IH a refl =
       step (/-induction ~EqRel (Î» _ â Î -is-prop fe (Î» _ â acc-is-prop _)) Î±)
        where
         Î± : (b : A) â [ b ] âº [ a ] â is-accessible _âº_ [ b ]
         Î± b m = IH (f b) (âº-to-â m) b refl
    acc : (a : A) â is-accessible _âº_ [ a ]
    acc a = acc' (f a) a refl

  module quotient-as-ordinal
          (Ï : is-set-theoretic-ordinal (ð-set f))
         where

   A/~áµÊ³áµ : Ordinal (ð¤ âº)
   A/~áµÊ³áµ = A/~ , _âº_
                , âº-is-prop-valued
                , âº-is-well-founded
                , âº-is-extensional (transitive-set-if-set-theoretic-ordinal Ï)
                , âº-is-transitive Ï

\end{code}

We now show that for x = ð-set {A} f, the total space ðxáµÊ³áµ and the above set
quotient A/~áµÊ³áµ are equal as (large) ordinals. The equivalence of types is
proved generally in the module set-replacement-construction in the file
UF/Quotient.lagda. We only need to check that the equivalence is order
preserving and reflecting.

\begin{code}

   private
    x = ð-set f

   open total-space-of-an-element-of-ð x Ï
   open total-space-of-ð-set sq f Ï

   open set-replacement-construction sq pt f
                                     ð-is-locally-small
                                     ð-is-large-set
        hiding ([_])

   private
    Ï : A/~ â image f
    Ï = quotient-to-image

    Ï-behaviour : (a : A) â Ï [ a ] ï¼ corestriction f a
    Ï-behaviour = universality-triangle/ ~EqRel
                   (image-is-set f ð-is-large-set) (corestriction f) _

    Ï-is-order-preserving : is-order-preserving A/~áµÊ³áµ image-fáµÊ³áµ Ï
    Ï-is-order-preserving = /-inductionâ fe ~EqRel prop-valued preserve
     where
      prop-valued : (a' b' : A / ~EqRel)
                  â is-prop (a' âº b' â underlying-order image-fáµÊ³áµ (Ï a') (Ï b'))
      prop-valued a' b' = Î -is-prop fe (Î» _ â prop-valuedness _
                                               (is-well-ordered image-fáµÊ³áµ)
                                               (Ï a') (Ï b'))
      preserve : (a b : A)
               â [ a ] âº [ b ]
               â underlying-order image-fáµÊ³áµ (Ï [ a ]) (Ï [ b ])
      preserve a b l = transportâ (underlying-order image-fáµÊ³áµ) p q mon
       where
        mem : f a â f b
        mem = âº-to-â l
        mon : underlying-order image-fáµÊ³áµ (corestriction f a) (corestriction f b)
        mon = mem
        p : corestriction f a ï¼ Ï [ a ]
        p = (Ï-behaviour a) â»Â¹
        q : corestriction f b ï¼ Ï [ b ]
        q = (Ï-behaviour b) â»Â¹

    Ï-is-order-reflecting : is-order-reflecting A/~áµÊ³áµ image-fáµÊ³áµ Ï
    Ï-is-order-reflecting = /-inductionâ fe ~EqRel prop-valued reflect
     where
      prop-valued : (a' b' : A/~)
                  â is-prop (underlying-order image-fáµÊ³áµ (Ï a') (Ï b') â a' âº b')
      prop-valued a' b' = Î -is-prop fe (Î» _ â prop-valuedness _âº_
                                               (is-well-ordered A/~áµÊ³áµ) a' b')
      reflect : (a b : A)
              â underlying-order image-fáµÊ³áµ (Ï [ a ]) (Ï [ b ])
              â [ a ] âº [ b ]
      reflect a b l = â-to-âº mem
       where
        p : Ï [ a ] ï¼ corestriction f a
        p = Ï-behaviour a
        q : Ï [ b ] ï¼ corestriction f b
        q = Ï-behaviour b
        mem : f a â f b
        mem = transportâ (underlying-order image-fáµÊ³áµ) p q l

   total-space-is-quotientáµÊ³áµ : ðxáµÊ³áµ ï¼ A/~áµÊ³áµ
   total-space-is-quotientáµÊ³áµ = ðxáµÊ³áµ      ï¼â¨ â¦1â¦ â©
                                image-fáµÊ³áµ ï¼â¨ â¦2â¦ â©
                                A/~áµÊ³áµ     â
    where
     â¦1â¦ = eqtoidâ ðxáµÊ³áµ image-fáµÊ³áµ ðxáµÊ³áµ-â-image-fáµÊ³áµ
     â¦2â¦ = eqtoidâ image-fáµÊ³áµ A/~áµÊ³áµ (ââ-sym A/~áµÊ³áµ image-fáµÊ³áµ (Ï , Ï-is-order-equiv))
      where
       Ï-is-order-equiv : is-order-equiv A/~áµÊ³áµ image-fáµÊ³áµ Ï
       Ï-is-order-equiv =
        order-preserving-reflecting-equivs-are-order-equivs _ _
         Ï (âââ»Â¹-is-equiv image-â-quotient)
         Ï-is-order-preserving
         Ï-is-order-reflecting

\end{code}

Next, we make use of the fact that the cumulative hierarchy ð is locally small,
as shown in UF/CumulativeHierarchy-LocallySmall.lagda, to construct a small quotient
A/~â» equivalent to A/~.

In general, we use the symbol â» to indicate a resized small-valued analogue.

\begin{code}

  _~â»_ : A â A â ð¤ Ì
  a ~â» b = f a ï¼â» f b

  ~â»EqRel : EqRel A
  ~â»EqRel = _~â»_ , (Î» a b â ï¼â»-is-prop-valued)
                 , (Î» a â ï¼â»-is-reflexive)
                 , (Î» a b â ï¼â»-is-symmetric)
                 , (Î» a b c â ï¼â»-is-transitive)

  A/~â» : ð¤ Ì
  A/~â» = A / ~â»EqRel

  A/~-â-A/~â» : A/~ â A/~â»
  A/~-â-A/~â» = quotients-equivalent A ~EqRel ~â»EqRel (ï¼-to-ï¼â» , ï¼â»-to-ï¼)

\end{code}

The small-valued membership relation ââ» developed in the aforementioned file now
allows us to define a small-valued relation âº' on A/~ and transfer the well
order on A/~ to A/~â», for which we use the machinery developed by MartÃ­n EscardÃ³
in Ordinals/WellOrderTransport.lagda.

\begin{code}

  private
   âº-has-small-values : (x y : A/~) â is-small (x âº y)
   âº-has-small-values =
    /-inductionâ fe ~EqRel
                 (Î» x y â being-small-is-prop ua (x âº y) ð¤)
                 (Î» a b â (f a ââ» f b)
                        , ((f a ââ» f b)    ââ¨ ââ»-â-â â©
                           (f a â f b)     ââ¨ idtoeq _ _ (âº-ï¼-â â»Â¹) â©
                           ([ a ] âº [ b ]) â ))

   _âº'_ : A/~ â A/~ â ð¤ Ì
   x âº' y = prâ (âº-has-small-values x y)

   âº-â-âº' : {x y : A/~} â x âº y â x âº' y
   âº-â-âº' {x} {y} = â-sym (prâ (âº-has-small-values x y))

  module small-quotient-as-ordinal
          (Ï : is-set-theoretic-ordinal (ð-set f))
         where

   open quotient-as-ordinal Ï

   private
    resize-ordinal : Î£ s ê OrdinalStructure A/~â» , (A/~â» , s) ââ A/~áµÊ³áµ
    resize-ordinal = transfer-structure A/~â» A/~áµÊ³áµ (â-sym A/~-â-A/~â»)
                      (_âº'_ , (Î» x y â âº-â-âº'))

   A/~â»áµÊ³áµ : Ordinal ð¤
   A/~â»áµÊ³áµ = A/~â» , prâ resize-ordinal

   A/~â»áµÊ³áµ-ââ-A/~áµÊ³áµ : A/~â»áµÊ³áµ ââ A/~áµÊ³áµ
   A/~â»áµÊ³áµ-ââ-A/~áµÊ³áµ = prâ resize-ordinal

   A/~áµÊ³áµ--ââ-A/~â»áµÊ³áµ : A/~áµÊ³áµ ââ A/~â»áµÊ³áµ
   A/~áµÊ³áµ--ââ-A/~â»áµÊ³áµ = ââ-sym A/~â»áµÊ³áµ A/~áµÊ³áµ A/~â»áµÊ³áµ-ââ-A/~áµÊ³áµ

   [_]â» : A â A/~â»
   [_]â» = â A/~-â-A/~â» â â [_]

   []â»-is-surjection : is-surjection [_]â»
   []â»-is-surjection =
    â-is-surjection
     (surjection-induction-converse [_] (Î» P â /-induction ~EqRel))
     (equivs-are-surjections (ââ-is-equiv A/~-â-A/~â»))

   _âºâ»_ : A/~â» â A/~â» â ð¤ Ì
   _âºâ»_ = underlying-order A/~â»áµÊ³áµ

\end{code}

We relate the order âºâ» on the small quotient A/~â» to the order âº on the large
quotient A/~ and the set membership relation â on ð.

\begin{code}

   âºâ»-â-âº : {a b : A} â [ a ]â» âºâ» [ b ]â» â [ a ] âº [ b ]
   âºâ»-â-âº {a} {b} = logically-equivalent-props-are-equivalent
                      (prop-valuedness _âºâ»_ (is-well-ordered A/~â»áµÊ³áµ)
                        [ a ]â» [ b ]â»)
                      (âº-is-prop-valued [ a ] [ b ])
                      (â¦2â¦ [ a ] [ b ])
                      (â¦1â¦ [ a ] [ b ])
    where
     Ïâº : A/~â»áµÊ³áµ ââ A/~áµÊ³áµ
     Ïâº = A/~â»áµÊ³áµ-ââ-A/~áµÊ³áµ
     Ïâ»Â¹ : A/~ â A/~â»
     Ïâ»Â¹ = ââ-to-funâ»Â¹ _ _ Ïâº
     Ï-is-order-equiv : is-order-equiv A/~â»áµÊ³áµ A/~áµÊ³áµ (ââ-to-fun _ _ Ïâº)
     Ï-is-order-equiv = ââ-to-fun-is-order-equiv _ _ Ïâº
     â¦1â¦ : (x y : A/~) â x âº y â Ïâ»Â¹ x âºâ» Ïâ»Â¹ y
     â¦1â¦ = inverses-of-order-equivs-are-order-preserving A/~â»áµÊ³áµ A/~áµÊ³áµ
                                                         Ï-is-order-equiv
     â¦2â¦ : (x y : A/~) â Ïâ»Â¹ x âºâ» Ïâ»Â¹ y â x âº y
     â¦2â¦ = inverses-of-order-equivs-are-order-reflecting A/~â»áµÊ³áµ A/~áµÊ³áµ
                                                          Ï-is-order-equiv

   âºâ»-â-â : {a b : A} â [ a ]â» âºâ» [ b ]â» â f a â f b
   âºâ»-â-â {a} {b} = [ a ]â» âºâ» [ b ]â» ââ¨ âºâ»-â-âº â©
                    ([ a ] âº [ b ])  ââ¨ idtoeq _ _ âº-ï¼-â â©
                    f a â f b        â 

   âºâ»-to-â : {a b : A} â [ a ]â» âºâ» [ b ]â» â f a â f b
   âºâ»-to-â = â âºâ»-â-â â

   â-to-âºâ» : {a b : A} â f a â f b â [ a ]â» âºâ» [ b ]â»
   â-to-âºâ» = â âºâ»-â-â ââ»Â¹

\end{code}

Because A/~â»áµÊ³áµ is a small ordinal in ð¤, it now typechecks to ask whether it
equals the recursive supremum given by Î¨áµÊ³áµ (ð-set f).

This is indeed the case and because Î¦áµÊ³áµ is left-cancellable, it suffices
to show that
  Î¦ (A/~áµÊ³áµ) ï¼ ð-set f.
This boils down to proving the equality
  f a ï¼ Î¦ (A/~â»áµÊ³áµ â [ a ]â»)
for every a : A, where â denotes taking the initial segment.

We slightly generalise this statement so that we can prove it by transfinite
induction on A/~â»áµÊ³áµ.

\begin{code}

   initial-segments-of-A/~â»áµÊ³áµ-are-given-by-f :
      (a' : A/~â») (a : A)
    â a' ï¼ [ a ]â»
    â Î¦ (A/~â»áµÊ³áµ â [ a ]â») ï¼ f a
   initial-segments-of-A/~â»áµÊ³áµ-are-given-by-f =
    transfinite-induction _âºâ»_ (Well-foundedness A/~â»áµÊ³áµ) _ ind-proof
     where
      ind-proof : (a' : A/~â»)
                â ((b' : A/~â») â b' âºâ» a'
                               â (b : A) â b' ï¼ [ b ]â»
                               â Î¦ (A/~â»áµÊ³áµ â [ b ]â») ï¼ f b)
                â (a : A) â a' ï¼ [ a ]â» â Î¦ (A/~â»áµÊ³áµ â [ a ]â») ï¼ f a
      ind-proof a' IH a refl = â-extensionality _ _ â¦1â¦ â¦2â¦
       where
        âa : Ordinal ð¤
        âa = A/~â»áµÊ³áµ â [ a ]â»

        â¦1â¦ : Î¦ âa â f a
        â¦1â¦ x m = â¥â¥-rec â-is-prop-valued â¦1â¦' fact
         where
          lemma : (b : A)
                â f b â f a
                â x ï¼ Î¦ (A/~â»áµÊ³áµ â [ b ]â»)
                â x â f a
          lemma b n e = transport (_â f a) (e' â»Â¹) n
           where
            e' = x                   ï¼â¨ e                            â©
                 Î¦ (A/~â»áµÊ³áµ â [ b ]â») ï¼â¨ IH [ b ]â» (â-to-âºâ» n) b refl â©
                 f b                â

          fact : â b' ê â¨ âa â© , Î¦ (âa â b') ï¼ x
          fact = from-â-of-ð-set (transport (x â_) (Î¦-behaviour âa) m)

          â¦1â¦' : (Î£ b' ê â¨ A/~â»áµÊ³áµ â [ a ]â» â© , Î¦ (âa â b') ï¼ x)
              â x â f a
          â¦1â¦' ((b' , l) , e) = â¥â¥-rec â-is-prop-valued h ([]â»-is-surjection b')
           where
            h : (Î£ b ê A , [ b ]â» ï¼ b') â x â f a
            h (b , refl) = lemma b (âºâ»-to-â l) e'
             where
              e' = x                     ï¼â¨ e â»Â¹ â©
                   Î¦ (âa â ([ b ]â» , l)) ï¼â¨ e''  â©
                   Î¦ (A/~â»áµÊ³áµ â [ b ]â»)  â
               where
                e'' = ap Î¦ (iterated-â A/~â»áµÊ³áµ [ a ]â» [ b ]â» l)

        â¦2â¦ : f a â Î¦ âa
        â¦2â¦ x m = â¥â¥-rec â-is-prop-valued (Î» (b , n , e) â â¦2â¦' b n e) fact
         where
          fact : â b ê A , (f b â f a) Ã (f b ï¼ x)
          fact = â¥â¥-functor h fact'
           where
            fact' : â b ê A , f b ï¼ x
            fact' = from-â-of-ð-set (transitive-set-if-set-theoretic-ordinal Ï
                                      (f a) x (to-â-of-ð-set â£ a , refl â£) m)
            abstract
             h : (Î£ b ê A , f b ï¼ x)
               â Î£ b ê A , (f b â f a) Ã (f b ï¼ x)
             h (b , e) = b , transportâ»Â¹ (_â f a) e m , e

          lemma : (b : A)
                â f b â f a
                â f b ï¼ x
                â Î¦ (A/~â»áµÊ³áµ â [ b ]â») ï¼ x
          lemma b n e = IH [ b ]â» (â-to-âºâ» n) b refl â e

          â¦2â¦' : (b : A)
               â f b â f a
               â f b ï¼ x
               â x â Î¦ âa
          â¦2â¦' b n e = transport (_â Î¦ âa) (lemma b n e) mem
           where
            mem' : Î¦ (A/~â»áµÊ³áµ â [ b ]â») â ð-set (Î» b' â Î¦ (âa â b'))
            mem' = to-â-of-ð-set â£ ([ b ]â» , â-to-âºâ» n) , e' â£
             where
              e' : Î¦ (âa â ([ b ]â» , â-to-âºâ» n))
                 ï¼ Î¦ (A/~â»áµÊ³áµ â [ b ]â»)
              e' = ap Î¦ (iterated-â A/~â»áµÊ³áµ [ a ]â» [ b ]â» (â-to-âºâ» n))
            mem : Î¦ (A/~â»áµÊ³áµ â [ b ]â») â Î¦ âa
            mem = transportâ»Â¹ (Î¦ (A/~â»áµÊ³áµ â [ b ]â») â_)
                              (Î¦-behaviour âa)
                              mem'

\end{code}

Using that Î¦áµÊ³áµ is left-cancellable and a retraction of Î¨áµÊ³áµ, we
now prove that the recursive supremum given by Î¨áµÊ³áµ (ð-set f) is equal to
the nonrecursive set quotient A/~â»áµÊ³áµ.

\begin{code}

   open Î¨-construction sq

   Î¨áµÊ³áµ-is-quotient-of-carrier : Î¨áµÊ³áµ (ð-set f , Ï) ï¼ A/~â»áµÊ³áµ
   Î¨áµÊ³áµ-is-quotient-of-carrier =
    Î¦-is-left-cancellable (Î¨áµÊ³áµ (ð-set f , Ï)) A/~â»áµÊ³áµ e
     where
      e = Î¦ (Î¨áµÊ³áµ (ð-set f , Ï))          ï¼â¨ ap prâ â¦1â¦        â©
          ð-set f                         ï¼â¨ ð-set-ext _ _ â¦2â¦ â©
          ð-set (Î» a' â Î¦ (A/~â»áµÊ³áµ â a')) ï¼â¨ â¦3â¦               â©
          Î¦ A/~â»áµÊ³áµ                       â
       where
        â¦1â¦ : Î¦áµÊ³áµ (Î¨áµÊ³áµ (ð-set f , Ï)) ï¼ ð-set f , Ï
        â¦1â¦ = Î¨áµÊ³áµ-is-section-of-Î¦áµÊ³áµ (ð-set f , Ï)
        â¦2â¦ : f â (Î» a' â Î¦ (A/~â»áµÊ³áµ â a'))
        â¦2â¦ = â¦2â¦Ë¡ , â¦2â¦Ê³
         where
          â¦2â¦Ë¡ : f â² (Î» a' â Î¦ (A/~â»áµÊ³áµ â a'))
          â¦2â¦Ë¡ a =
           â£ [ a ]â» , initial-segments-of-A/~â»áµÊ³áµ-are-given-by-f [ a ]â» a refl â£
          â¦2â¦Ê³ : (Î» a' â Î¦ (A/~â»áµÊ³áµ â a')) â² f
          â¦2â¦Ê³ a' = â¥â¥-functor h ([]â»-is-surjection a')
           where
            h : (Î£ a ê A , [ a ]â» ï¼ a')
              â (Î£ a ê A , f a ï¼ Î¦ (A/~â»áµÊ³áµ â a'))
            h (a , refl) =
             a , ((initial-segments-of-A/~â»áµÊ³áµ-are-given-by-f a' a refl) â»Â¹)
        â¦3â¦ = (Î¦-behaviour A/~â»áµÊ³áµ) â»Â¹

\end{code}

Finally, using that the total space of (ð-set {A} f) and A/~ are equal as
(large) ordinals we distill a proof that Î¨áµÊ³áµ x is isomorphic as an
ordinal to the total space ðxáµÊ³áµ of x.

\begin{code}

 module _
         (sq : set-quotients-exist)
        where

  open total-space-of-an-element-of-ð
  open Î¨-construction sq

  Î¨áµÊ³áµ-is-isomorphic-to-total-space :
     (x : ð) (Ï : is-set-theoretic-ordinal x)
   â Î¨áµÊ³áµ (x , Ï) ââ total-spaceáµÊ³áµ x Ï
  Î¨áµÊ³áµ-is-isomorphic-to-total-space = ð-prop-simple-induction _ prop-valued Î³
   where
    prop-valued : (x : ð)
                â is-prop ((Ï : is-set-theoretic-ordinal x) â Î¨áµÊ³áµ (x , Ï)
                                                            ââ total-spaceáµÊ³áµ x Ï)
    prop-valued x = Î -is-prop fe (Î» Ï â ââ-is-prop-valued _ _)
    Î³ : {A : ð¤ Ì } (f : A â ð) (Ï : is-set-theoretic-ordinal (ð-set f))
      â Î¨áµÊ³áµ (ð-set f , Ï) ââ total-spaceáµÊ³áµ (ð-set f) Ï
    Î³ {A} f Ï = ââ-trans (Î¨áµÊ³áµ (ð-set f , Ï))
                         A/~â»áµÊ³áµ
                         (total-spaceáµÊ³áµ (ð-set f) Ï)
                         â¦1â¦ â¦2â¦
     where
      open ð-set-carrier-quotient sq f
      open small-quotient-as-ordinal Ï
      open quotient-as-ordinal Ï
      â¦1â¦ : Î¨áµÊ³áµ (ð-set f , Ï) ââ A/~â»áµÊ³áµ
      â¦1â¦ = idtoeqâ _ _ Î¨áµÊ³áµ-is-quotient-of-carrier
      â¦2â¦ : A/~â»áµÊ³áµ ââ total-spaceáµÊ³áµ (ð-set f) Ï
      â¦2â¦ = ââ-sym _ _ (ââ-trans (total-spaceáµÊ³áµ (ð-set f) Ï)
                                 A/~áµÊ³áµ
                                 A/~â»áµÊ³áµ
                                 â¦3â¦ â¦4â¦)
       where
        â¦3â¦ : total-spaceáµÊ³áµ (ð-set f) Ï ââ A/~áµÊ³áµ
        â¦3â¦ = idtoeqâ _ _ total-space-is-quotientáµÊ³áµ
        â¦4â¦ : A/~áµÊ³áµ ââ A/~â»áµÊ³áµ
        â¦4â¦ = A/~áµÊ³áµ--ââ-A/~â»áµÊ³áµ

\end{code}
