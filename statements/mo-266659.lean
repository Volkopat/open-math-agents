import Mathlib

/-!
# An inequality between idempotents

Source: https://mathoverflow.net/questions/266659
Credit: @koolkao

Question (ABB, MathOverflow 266659, 2017; CC BY-SA 3.0). Let `R` be a unital ring. Let us denote
`I_R` by the set of all idempotent (`p^2 = p`) in `R`. For given `p, q` in `I_R`, we write
`p ≤ q` if `pq = qp = p`. Assume that both `p ∨ q` (the supremum of `p` and `q`) and `p ∧ q`
(the infimum of `p` and `q`) exist in `R` for every `p, q` in `I_R`. We also assume that
`pq = 0` if and only if `qp = 0`. Let `p, q, e` and `f` be in `I_R` with
`pe = pf = qe = qf = 0`. Can we conclude the following inequality?
`(p + e) ∧ (q + f) ≤ p ∧ q + e ∧ f`.

`main` states that the answer is yes, for every ring `R` (in `Type`) satisfying the two
assumptions. A disproof is a ring satisfying them together with `p, q, e, f` for which the
inequality fails.

Translation choices:
* `R` is a `Ring` (associative, with `1`); `I_R` is the set of `p` with `IsIdempotentElem p`;
* `p ≤ q` is `IdemLE p q`, that is `p * q = p ∧ q * p = p`; it is applied to the two sides of
  the inequality exactly as written;
* "`p ∨ q` and `p ∧ q` exist for every `p, q ∈ I_R`" is read as: `(I_R, ≤)` has binary suprema
  and infima. They are given as functions `sup inf : R → R → R` such that, for idempotent
  `p, q`, `inf p q` is an idempotent which is a lower bound of `p` and `q` and lies above every
  idempotent lower bound, and dually for `sup p q`. Their values at non-idempotent arguments are
  not constrained (they are never used there: `p + e` and `q + f` are idempotents under the
  hypotheses);
* the assumption "`pq = 0` iff `qp = 0`" is read for idempotents `p, q`, the objects it is
  stated about.
-/

namespace OMA.S_mo_266659

/-- The order on idempotents from the source: `p ≤ q` iff `pq = qp = p`. -/
def IdemLE {R : Type} [Ring R] (p q : R) : Prop :=
  p * q = p ∧ q * p = p

/-- Under the source's assumptions, `(p + e) ∧ (q + f) ≤ p ∧ q + e ∧ f`. -/
theorem main :
    ∀ (R : Type) [Ring R] (inf sup : R → R → R),
      (∀ p q : R, IsIdempotentElem p → IsIdempotentElem q →
        IsIdempotentElem (inf p q) ∧ IdemLE (inf p q) p ∧ IdemLE (inf p q) q ∧
          ∀ r : R, IsIdempotentElem r → IdemLE r p → IdemLE r q → IdemLE r (inf p q)) →
      (∀ p q : R, IsIdempotentElem p → IsIdempotentElem q →
        IsIdempotentElem (sup p q) ∧ IdemLE p (sup p q) ∧ IdemLE q (sup p q) ∧
          ∀ r : R, IsIdempotentElem r → IdemLE p r → IdemLE q r → IdemLE (sup p q) r) →
      (∀ p q : R, IsIdempotentElem p → IsIdempotentElem q → (p * q = 0 ↔ q * p = 0)) →
      ∀ p q e f : R, IsIdempotentElem p → IsIdempotentElem q → IsIdempotentElem e →
        IsIdempotentElem f → p * e = 0 → p * f = 0 → q * e = 0 → q * f = 0 →
        IdemLE (inf (p + e) (q + f)) (inf p q + inf e f) := by
  sorry

end OMA.S_mo_266659
