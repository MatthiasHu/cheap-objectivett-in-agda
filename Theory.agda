
open import Rules

module Theory
  (rules : IdPiSigmaRules)
  where

private module R = IdPiSigmaRules rules

open import ConvenienceNotation rules


-- As long as we have no universe in the object language (typal tt),
-- polymorphism can only be expressed in the meta language (Agda).

id :
  (A : Ty) →
  Tm (
    Π _ ∈ A ,
    A
  )
id A =
  a ↦ a

module _ where private
  -- This version of subst uses the function types of the meta language
  -- instead of the function types of the object language.
  -- It behaves more like a syntactic construct than a term of function type.
  subst' :
    (A : Ty) →
    (B : Tm A → Ty) →
    (a : Tm A) →
    (b : Tm A) →
    (p : Tm (a ＝ b)) →
    Tm (B a) → Tm (B b)
  subst' A B a b p =
    R.app (B a) (λ _ → B b)
      (R.idrec A (λ x y _ → Π _ ∈ B x , B y)
        a
        b
        p
        (λ a' → id (B a')))

subst :
  (A : Ty) →
  (B : Tm A → Ty) →
  Tm (
    Π a ∈ A ,
    Π b ∈ A ,
    Π _ ∈ (a ＝ b) ,
    Π _ ∈ (B a) ,
    B b
  )
subst A B =
  a ↦
  b ↦
  p ↦
  R.idrec A (λ x y _ → (Π _ ∈ B x , B y))
    a
    b
    p
    (λ a' → id (B a'))

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
    Π _ ∈ (Π x ∈ A , P x x (refl A < x >)) ,
    Π a ∈ A ,
    Π b ∈ A ,
    Π p ∈ a ＝ b ,
    P a b p
  )
idrec A P =
  d ↦
  a ↦
  b ↦
  p ↦
  let
  d' : (x : Tm A) → Tm (P x x (R.refl A x))
  d' = λ x →
    subst
      (x ＝ x)
      (P x x)
      < refl A < x > >
      < R.refl A x >
      < R.betaconv A (λ x → x ＝ x) x (λ a → R.refl A a) >
      < d < x > >
  in
  R.idrec A P a b p d'

-- TODO: Do we want a version of idrec with the first endpoint fixed and only the second free?

idconv :
  (A : Ty) →
  (P : (x : Tm A) → (y : Tm A) → Tm (x ＝ y) → Ty) →
  Tm (
    Π d ∈ (Π x ∈ A , P x x (refl A < x >)) ,
    Π a ∈ A ,
    ((idrec A P < d > < a > < a > < refl A < a > >) ＝ (d < a >))
  )
idconv A P =
  d ↦
  let
  d' : (x : Tm A) → Tm (P x x (R.refl A x))
  d' = λ x →
    subst
      (x ＝ x)
      (P x x)
      < refl A < x > >
      < R.refl A x >
      < R.betaconv A (λ x → x ＝ x) x (λ a → R.refl A a) >
      < d < x > >
  in
  a ↦
  let
  eq' : Tm (R.idrec A P a a (R.refl A a) d' ＝ d' a)
  eq' = R.idconv A P a d'
  in
  {!eq'!}


-- Example of a statement that can not be expressed as concisely
-- without judgemental beta reduction:
-- "ap(const x)(p) = refl x"


is-prop :
  (A : Ty) →
  Ty
is-prop A =
  Π a ∈ A ,
  Π b ∈ A ,
  (a ＝ b)

-- This seems half cheating.
Contraction :
  (A : Ty) →
  (a : Tm A) →
  Ty
Contraction A a =
  Π b ∈ A ,
  (a ＝ b)

is-contr :
  (A : Ty) →
  Ty
is-contr A =
  -- Needs sigma types...
  {!Sigma A λ a →
  Contraction A a!}

compose-paths :
  (A : Ty) →
  Tm (
    -- This order of argument makes the definition easy.
    -- (Not the function convenient to use.)
    Π a ∈ A ,
    Π b ∈ A ,
    Π _ ∈ (a ＝ b) ,
    Π c ∈ A ,
    Π _ ∈ (b ＝ c) ,
    (a ＝ c)
  )
compose-paths A =
  a ↦
  b ↦
  p ↦
  R.idrec A
    (λ a b p → Π c ∈ A , Π _ ∈ (b ＝ c) , (a ＝ c))
    a b p
    λ a → c ↦ id (a ＝ c)

invert-path :
  (A : Ty) →
  Tm (
    Π a ∈ A ,
    Π b ∈ A ,
    Π _ ∈ (a ＝ b) ,
    (b ＝ a)
  )
invert-path A =
  idrec A (λ x y p → y ＝ x) < refl A >

compose-invert-path :
  (A : Ty) →
  Tm (
    Π a ∈ A ,
    Π b ∈ A ,
    Π p ∈ (a ＝ b) ,
    ((compose-paths A < a > < b > < p > < a > < invert-path A < a > < b > < p > >) ＝ (refl A < a >))
  )
compose-invert-path A =
  a ↦
  b ↦
  p ↦
  R.idrec A
    (λ a b p → (compose-paths A < a > < b > < p > < a > < invert-path A < a > < b > < p > >) ＝ (refl A < a >))
    a b p
    λ x → {!!}
    -- We will need idconv here.

Contraction-→-is-prop :
  (A : Ty) →
  Tm (
    Π a ∈ A ,
    Π _ ∈ Contraction A a ,
    is-prop A
  )
Contraction-→-is-prop A =
  a ↦
  contraction ↦
  x ↦
  y ↦
  (compose-paths A
    < x >
    < a >
    < invert-path A < a > < x > < contraction < x > > >
    < y >
    < contraction < y > >)

Constraction-→-Id-type-Contraction :
  (A : Ty) →
  Tm (
    Π a ∈ A ,
    Π contraction ∈ (Contraction A a) ,
    Π b ∈ A ,
    Π b' ∈ A ,
    Contraction (b ＝ b')
      (Contraction-→-is-prop A < a > < contraction > < b > < b' >)
  )
Constraction-→-Id-type-Contraction =
  {!!}

is-prop-→-has-contr-Id-types-1 :
  (A : Ty) →
  Tm (
    Π _ ∈ (is-prop A) ,
    Π a ∈ A ,
    Π b ∈ A ,
    (a ＝ b)
  )
is-prop-→-has-contr-Id-types-1 A =
  id (is-prop A)
  -- Yes, `is-prop` does unfold automatically.

is-prop-→-has-contr-Id-types-2 :
  (A : Ty) →
  Tm (
    Π is-prop-A ∈ (is-prop A) ,
    Π a ∈ A ,
    Π b ∈ A ,
    Π p ∈ (a ＝ b) ,
    (p ＝ (is-prop-→-has-contr-Id-types-1 A < is-prop-A > < a > < b >))
  )
is-prop-→-has-contr-Id-types-2 =
  {!!}

-- (Cheating about is-contr.)
-- is-contr-→-is-prop :
--   (A : Ty) →
--   {!!}
-- is-contr-→-is-prop =
--   {!!}
