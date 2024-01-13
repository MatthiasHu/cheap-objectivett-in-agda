
open import Rules

module Sigma
  (rules : IdPiSigmaRules)
  where

open IdPiSigmaRules rules

open import ConvenienceNotation rules hiding (Ty; Tm)


-- Ad hoc stuff about Sigma.

module _
  (A : Ty)
  (B : Tm A → Ty)
  where


  fst :
    Tm (
      Π ab ∈ Sigma A B ,
      A
    )
  fst =
    ab ↦
    sigmarec A B (λ ab → A) (λ a b → a) ab

  -- We should transform `sigmarec`, ... to terms of Pi type before we use them a lot...

  fst-pair :
    Tm (
      Π a ∈ A ,
      Π b ∈ B a ,
      ((fst < pair A B a b >) ＝ a)
    )
  fst-pair =
    a ↦
    b ↦
    -- Here we are cheating a bit: ...
    {!sigmaconv A B (λ ab → A) (λ a b → a) a b!}

  snd :
    Tm (
      Π ab ∈ Sigma A B ,
      B (fst < ab >)
    )
  snd =
    ab ↦
    sigmarec A B (λ ab → B (fst < ab >)) (λ a b → {!subst ... fst-pair ... b!}) ab
