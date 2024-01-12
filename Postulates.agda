-- Trying to formalize some stuff in typal (= objective) type theory,
-- taking a "two-level type theory" or "logical framework" approach.

-- We postulate a meta type of types and a meta type family of terms.
-- Then we postulate functions corresponding to the rules in appendix A of:
-- https://arxiv.org/abs/2102.00905

-- We can imagine that our meta language (Agda) is the internal language
-- of the presheaf topos over the category of contexts and substitutions
-- of some model of typal type theory.


module Postulates where

record MetaUniverse : Set₁ where
  field
    Ty : Set
    Tm : Ty → Set

module _
  (meta-universe : MetaUniverse)
  where

  open MetaUniverse meta-universe

  -- We stay as close as possible to the roles in the paper here.

  -- In particular, we translate syntactic term constructs that take term arguments
  -- to Agda functions, not to terms of Pi type.
  -- Note: This leaves open the possibility for "exotic syntax" (proper meta level functions
  -- embedded in supposedly object language expressions) perhaps more than necessary.

  -- Rules for identity types
  record IdRules : Set where
    field
      Id :
        (A : Ty) →
        (a : Tm A) →
        (b : Tm A) →
        Ty

      refl :
        (A : Ty) →
        (a : Tm A) →
        Tm (Id A a a)

      idrec :
        (A : Ty) →
        (P : (x : Tm A) → (y : Tm A) → Tm (Id A x y) → Ty) →
        (a : Tm A) →
        (b : Tm A) →
        (p : Tm (Id A a b)) →
        (d : (x : Tm A) → Tm (P x x (refl A x))) →
        Tm (P a b p)

      idconv :
        (A : Ty) →
        (P : (x : Tm A) → (y : Tm A) → Tm (Id A x y) → Ty) →
        (a : Tm A) →
        (d : (x : Tm A) → Tm (P x x (refl A x))) →
        Tm (Id (P a a (refl A a)) (idrec A P a a (refl A a) d) (d a))

  -- Rules for Π-types
  record PiRules (id-rules : IdRules) : Set where
    open IdRules id-rules

    field
      Pi :
        (A : Ty) →
        (B : Tm A → Ty) →
        Ty

      lam :
        (A : Ty) →
        (B : Tm A → Ty) →
        (t : (x : Tm A) → Tm (B x)) →
        Tm (Pi A B)

      app :
        (A : Ty) →
        (B : Tm A → Ty) →
        (f : Tm (Pi A B)) →
        (a : Tm A) →
        Tm (B a)

      betaconv :
        (A : Ty) →
        (B : Tm A → Ty) →
        (a : Tm A) →
        (t : (x : Tm A) → Tm (B x)) →
        Tm (Id (B a) (app A B (lam A B t) a) (t a))

  -- Additional types that are not in the paper.

  -- Σ-types
  record SigmaRules (id-rules : IdRules) : Set where
    open IdRules id-rules

    field
      Sigma :
        (A : Ty) →
        (B : Tm A → Ty) →
        Ty

      pair :
        (A : Ty) →
        (B : Tm A → Ty) →
        (a : Tm A) →
        (b : Tm (B a)) →
        Tm (Sigma A B)

      sigmarec :
        (A : Ty) →
        (B : Tm A → Ty) →
        (P : Tm (Sigma A B) → Ty) →
        (d : (a : Tm A) → (b : Tm (B a)) → Tm (P (pair A B a b))) →
        (ab : Tm (Sigma A B)) →
        Tm (P ab)

      sigmaconv :
        (A : Ty) →
        (B : Tm A → Ty) →
        (P : Tm (Sigma A B) → Ty) →
        (d : (a : Tm A) → (b : Tm (B a)) → Tm (P (pair A B a b))) →
        (a : Tm A) →
        (b : Tm (B a)) →
        Tm (Id (P (pair A B a b)) (sigmarec A B P d (pair A B a b)) (d a b))

-- Bundle up all rules into one assumption.
record IdPiSigmaRules : Set₁ where
  field
    meta-universe : MetaUniverse
    Id-rules : IdRules meta-universe
    Pi-rules : PiRules meta-universe Id-rules
    Sigma-rules : SigmaRules meta-universe Id-rules
