-- TODO: remove this after filling the holes below
{-# OPTIONS --allow-unsolved-metas #-}

-- Here we transform the syntactic term constructs given by the rules
-- into more usable basic terms.

open import Rules

module RulesToTerms
  (rules : IdPiSigmaRules)
  where

private module R = IdPiSigmaRules rules

open import ConvenienceNotation rules


-- We will need a `subst` operation,
-- even though we do not consider it a basic term.

module subst-construct
  (A : Ty)
  (B : Tm A → Ty)
  where

  private
    P : (a : Tm A) → (a' : Tm A) → Tm (a ＝ a') → Ty
    P a a' _ = Π _ ∈ B a , B a'

    d : (a : Tm A) → Tm (P a a (R.refl A a))
    d a = b ↦ b

  subst :
    (a : Tm A) →
    (a' : Tm A) →
    (p : Tm (a ＝ a')) →
    Tm (
      Π _ ∈ B a ,
      B a'
    )
  subst a a' p =
    R.idrec A P a a' p d

  module properties where
    subst-refl :
      (a : Tm A) →
      Tm (
        subst a a (R.refl A a) ＝ (b ↦ b)
      )
    subst-refl a = R.idconv A P a d


-- Basic terms for identity types

module refl
  (A : Ty)
  where

  -- The final `refl` term.
  refl :
    Tm (
      Π a ∈ A ,
      (a ＝ a)
    )
  refl =
    a ↦ R.refl A a

  module properties where
    refl<> :
      (a : Tm A) →
      Tm ((refl < a >) ＝ R.refl A a)
    refl<> a = R.betaconv A (λ a → a ＝ a) a (R.refl A)

module with-refl where
  idrec :
    (A : Ty) →
    (P : (x : Tm A) → (y : Tm A) → Tm (x ＝ y) → Ty) →
    (a : Tm A) →
    (b : Tm A) →
    (p : Tm (a ＝ b)) →
    (d : (x : Tm A) → Tm (P x x (refl.refl A < x >))) →
    Tm (P a b p)
  idrec A P a b p d =
    let
    open refl A
    in
    R.idrec A P a b p
      (λ x →
        subst-construct.subst (x ＝ x) (P x x) (refl < x >) (R.refl A x)
          (properties.refl<> x)
          < d x >)

module idrec
  (A : Ty)
  (P : (x : Tm A) → (y : Tm A) → Tm (x ＝ y) → Ty)
  where

  transform-d :
    Tm (Π x ∈ A , P x x (refl.refl A < x >)) →
    (x : Tm A) → Tm (P x x (refl.refl A < x >))
  transform-d d x = d < x >

  -- The final `idrec` term.
  idrec :
    Tm (
      Π d ∈ (Π x ∈ A , P x x (refl.refl A < x >)) ,
      Π a ∈ A ,
      Π b ∈ A ,
      Π p ∈ a ＝ b ,
      P a b p
    )
  idrec =
    d ↦
    a ↦
    b ↦
    p ↦
    with-refl.idrec A P a b p (transform-d d)

idconv :
  (A : Ty) →
  (P : (x : Tm A) → (y : Tm A) → Tm (x ＝ y) → Ty) →
  Tm (
    Π d ∈ (Π x ∈ A , P x x (refl.refl A < x >)) ,
    Π a ∈ A ,
    ((idrec.idrec A P < d > < a > < a > < refl.refl A < a > >) ＝ (d < a >))
  )
idconv = {!!}

open refl public using (refl)
open idrec public using (idrec)
