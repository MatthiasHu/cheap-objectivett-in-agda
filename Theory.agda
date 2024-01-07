
module Theory where

open import Postulates


-- As long as we have no universe in the object language (typal tt),
-- polymorphism can only be expressed in the meta language (Agda).

Fun : Ty → Ty → Ty
Fun A B = Pi A (λ _ → B)

id :
  (A : Ty) →
  Tm (Fun A A)
id A =
  lam
    A
    (λ _ → A)
    (λ a → a)

-- This version of subst uses the function types of the meta language
-- instead of the function types of the object language.
-- It behaves more like a syntactic construct than a term of function type.
subst' :
  (A : Ty) →
  (B : Tm A → Ty) →
  (a : Tm A) →
  (b : Tm A) →
  (p : Tm (Id A a b)) →
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
    Pi A λ a →
    Pi A λ b →
    Pi (Id A a b) λ p →
    Pi (B a) λ _ →
    B b
  )
subst A B =
  lam A _ λ a →
  lam A _ λ b →
  lam (Id A a b) _ λ p →
  idrec A (λ x y _ → (Fun (B x) (B y)))
    a
    b
    p
    (λ a' → id (B a'))


-- Example of a statement that can not be expressed as concisely
-- without judgemental equality:
-- "ap(const x)(p) = refl x"
