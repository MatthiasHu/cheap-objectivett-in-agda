
-- Here we transform the syntactic term constructs given by the rules
-- into more usable basic terms.

open import Rules

module RulesToTerms
  (rules : IdPiSigmaRules)
  where

private module R = IdPiSigmaRules rules

open import ConvenienceNotation rules


-- Basic terms for identity types

refl :
  (A : Ty) →
  Tm (
    Π a ∈ A ,
    (a ＝ a)
  )
refl A =
  a ↦ R.refl A a

idrec :
  (A : Ty) →
  (P : (x : Tm A) → (y : Tm A) → Tm (x ＝ y) → Ty) →
  Tm (
    Π d ∈ (Π x ∈ A , P x x (refl A < x >)) ,
    Π a ∈ A ,
    Π b ∈ A ,
    Π p ∈ a ＝ b ,
    P a b p
  )
idrec = {!!}

idconv :
  (A : Ty) →
  (P : (x : Tm A) → (y : Tm A) → Tm (x ＝ y) → Ty) →
  Tm (
    Π d ∈ (Π x ∈ A , P x x (refl A < x >)) ,
    Π a ∈ A ,
    ((idrec A P < d > < a > < a > < refl A < a > >) ＝ (d < a >))
  )
idconv = {!!}
