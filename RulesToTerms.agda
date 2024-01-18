
-- Here we transform the syntactic term constructs given by the rules
-- into more usable basic terms.

open import Rules

module RulesToTerms
  (rules : IdPiSigmaRules)
  where

private module R = IdPiSigmaRules rules

open import ConvenienceNotation rules


refl :
  (A : Ty) →
  Tm (
    Π a ∈ A ,
    (a ＝ a)
  )
refl A =
  a ↦ R.refl A a
