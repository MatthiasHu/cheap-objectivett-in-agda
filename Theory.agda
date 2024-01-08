
module Theory where

open import Convenience
open import Postulates


-- As long as we have no universe in the object language (typal tt),
-- polymorphism can only be expressed in the meta language (Agda).

Fun : Ty → Ty → Ty
Fun A B =
  Π _ ∈ A ,
  B

id :
  (A : Ty) →
  Tm (Fun A A)
id A =
  a ↦ a

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
  app (B a) (λ _ → B b)
    (idrec A (λ x y _ → (Fun (B x) (B y)))
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
  idrec A (λ x y _ → (Fun (B x) (B y)))
    a
    b
    p
    (λ a' → id (B a'))


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

trivial-path :
  (A : Ty) →
  Tm (
    Π a ∈ A ,
    (a ＝ a)
  )
trivial-path A =
  a ↦
  refl A a

compose-paths :
  (A : Ty) →
  Tm (
    -- This order of argument makes the definition easy.
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
  idrec A
    (λ a b p → Π c ∈ A , Π _ ∈ (b ＝ c) , (a ＝ c))
    a b p
    λ a → c ↦ id (a ＝ c)

Contraction-→-is-prop :
  (A : Ty) →
  Tm (
    Π a ∈ A ,
    Fun (Contraction A a) (is-prop A)
  )
Contraction-→-is-prop =
  {!!}

Constraction-→-Id-type-Contraction :
  (A : Ty) →
  Tm (
    Π a ∈ A ,
    Π contraction ∈ (Contraction A a) ,
    Π b ∈ A ,
    Π b' ∈ A ,
    Contraction (b ＝ b')
      (app _ _ (app _ _ (app _ _ (app _ _ (Contraction-→-is-prop A) {!!}) {!!}) {!!}) {!!})
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
    Id (a ＝ b)
      p
      (app _ _ (app _ _ (app _ _ (is-prop-→-has-contr-Id-types-1 A) (is-prop-A)) a) b)
  )
is-prop-→-has-contr-Id-types-2 =
  {!!}

-- (Cheating about is-contr.)
is-contr-→-is-prop :
  (A : Ty) →
  {!!}
is-contr-→-is-prop =
  {!!}
