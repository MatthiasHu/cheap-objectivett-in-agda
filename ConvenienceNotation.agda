
open import Rules

module ConvenienceNotation
  (rules : IdPiSigmaRules)
  where

private module R = IdPiSigmaRules rules


open R public using (Ty; Tm)


-- Shorthands for some of the syntactic constructions,
-- with some type arguments made implicit.

_＝_ : {A : Ty} → Tm A → Tm A → Ty
_＝_ = R.Id _

Pi' = R.Pi

syntax Pi' A (λ a → B) = Π a ∈ A , B

lam' : {A : Ty} → {B : Tm A → Ty} → (t : (x : Tm A) → Tm (B x)) → Tm (R.Pi A B)
lam' t = R.lam _ _ t

syntax lam' (λ a → b) = a ↦ b

_<_> : {A : Ty} → {B : Tm A → Ty} → Tm (R.Pi A B) → (a : Tm A) → Tm (B a)
f < x > = R.app _ _ f x

module _ where private
  -- Idea for hidden argument notation.
  _<> : {A : Ty} → {B : Tm A → Ty} → Tm (R.Pi A B) → {a : Tm A} → Tm (B a)
  (f <>) {a = a} = f < a >
