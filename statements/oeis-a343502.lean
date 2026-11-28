import Mathlib

/-!
# A343502: Numbers k such that tau(tau(k)) and tau(k+1) are both prime

Source: https://oeis.org/A343502
Credit: @xor2k

Formalizes the OEIS A343502 conjecture (offset 1): all members except 2 and 3 are composite.

Conventions: `tau n` is the number of divisors, rendered as `(Nat.divisors n).card` (so
`tau 0 = 0`, which plays no role since `0` is not a member: `tau (tau 0) = 0` is not prime).
A member is any natural number `k` with `tau (tau k)` and `tau (k + 1)` both prime; the
statement quantifies over all `k : ℕ`, including `k = 0`, which is harmless because `0` and
`1` are not members (their exclusion is part of what must be proved). Composite means
`1 < k` and `k` not prime. The entry also poses an open question (whether there are finitely
many odd terms); it is phrased as a question, not a conjecture, and is not formalized.
-/

namespace OMA.S_oeis_a343502

/-- The number of divisors of `n`. -/
def tau (n : ℕ) : ℕ :=
  (Nat.divisors n).card

/-- Every `k` with `tau (tau k)` and `tau (k + 1)` both prime, other than `2` and `3`, is
composite. -/
theorem main :
    ∀ k : ℕ, (tau (tau k)).Prime → (tau (k + 1)).Prime → k ≠ 2 → k ≠ 3 →
      1 < k ∧ ¬ k.Prime := by
  sorry

end OMA.S_oeis_a343502
