
module Convenience where

import Postulates as P


open P public using (Ty; Tm)


-- Shorthands for the syntactic constructions,
-- with many type arguments left implicit.

_＝_ : {A : Ty} → Tm A → Tm A → Ty
_＝_ = P.Id _

Pi' = P.Pi

syntax Pi' A (λ a → B) = Π a ∈ A , B

lam' : {A : Ty} → {B : Tm A → Ty} → (t : (x : Tm A) → Tm (B x)) → Tm (P.Pi A B)
lam' t = P.lam _ _ t

syntax lam' (λ a → b) = a ↦ b

_<_> : {A : Ty} → {B : Tm A → Ty} → Tm (P.Pi A B) → (a : Tm A) → Tm (B a)
f < x > = P.app _ _ f x


-- To bring other syntactic constructs into a more convenient form
-- we already need subst...
