-- Trying to formalize some stuff in typal (= objective) type theory,
-- taking a "two-level type theory" or "logical framework" approach.

-- We postulate a meta type of types and a meta type family of terms.
-- Then we postulate functions corresponding to the rules in appendix A of:
-- https://arxiv.org/abs/2102.00905

-- We can imagine that our meta language (Agda) is the internal language
-- of the presheaf topos over the category of contexts and substitutions
-- of some model of typal type theory.


postulate
  Ty : Set
  Tm : Ty → Set

-- Rules for identity types
postulate
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

  idconf :
    (A : Ty) →
    (P : (x : Tm A) → (y : Tm A) → Tm (Id A x y) → Ty) →
    (a : Tm A) →
    (d : (x : Tm A) → Tm (P x x (refl A x))) →
    Tm (Id (P a a (refl A a)) (idrec A P a a (refl A a) d) (d a))

-- Rules for Π-types
postulate
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
