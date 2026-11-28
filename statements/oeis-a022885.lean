import Mathlib

/-!
# A022885: Primes with equal subsequent alternate prime gaps

Source: https://oeis.org/A022885
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Let `p(k)` be the `k`-th prime and consider the alternate prime gap ratio
`r(k) = (p(k + 3) - p(k + 2)) / (p(k + 1) - p(k))`.
It is conjectured that the most frequent value of `r(k)` is `1`; that is, for every
rational number `q ≠ 1`, the count of `k < N` with `r(k) = q` is eventually strictly
less than the count of `k < N` with `r(k) = 1`.

Conventions:
- `p k = Nat.nth Nat.Prime k` (0-indexed primes).
- `gapRatio k` is computed in `ℚ`.
-/

namespace OMA.S_oeis_a022885

noncomputable def gapRatio (k : ℕ) : ℚ :=
  ((Nat.nth Nat.Prime (k + 3) - Nat.nth Nat.Prime (k + 2) : ℕ) : ℚ) /
    ((Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k : ℕ) : ℚ)

noncomputable def countRatio (N : ℕ) (q : ℚ) : ℕ :=
  ((Finset.range N).filter fun k => gapRatio k = q).card

theorem main :
    ∀ q : ℚ, q ≠ 1 →
      Filter.Eventually (fun N : ℕ => countRatio N q < countRatio N 1) Filter.atTop := by
  sorry

end OMA.S_oeis_a022885
