
module Convenience where

open import Postulates


open Postulates public using (Ty; Tm)


-- Shorthands for the syntactic constructions,
-- with many type arguments left implicit.

_＝_ : {A : Ty} → Tm A → Tm A → Ty
_＝_ = Id _

Pi' = Pi

syntax Pi' A (λ a → B) = Π a ∈ A , B

Pi'' : {A : Ty} → (Tm A → Ty) → Ty
Pi'' B = Pi _ B

syntax Pi'' (λ a → B) = Π a , B

lam' : {A : Ty} → {B : Tm A → Ty} → (t : (x : Tm A) → Tm (B x)) → Tm (Pi A B)
lam' t = lam _ _ t

syntax lam' (λ a → b) = a ↦ b

_<_> : {A : Ty} → {B : Tm A → Ty} → Tm (Pi A B) → (a : Tm A) → Tm (B a)
f < x > = app _ _ f x


-- TODO: Bring other syntactic constructs into a more convenient form.
