import Mathlib

/-!
# A180476: Smallest k>0 such that q=p+6k, 6kp+q, 6kp-q, 6kq+p and 6kq-p are simultaneously prime

Source: https://oeis.org/A180476
Credit: @warshanks

For the `n`-th prime `p`, `a(n)` is the smallest `k > 0` such that, with `q = p + 6k`, the five
numbers `q`, `6kp + q`, `6kp - q`, `6kq + p` and `6kq - p` are all prime (or `0` if there is no
such `k`). The entry records one conjecture:

  such a `k > 0` exists for every prime `p > 3`.

`main` states it for every prime `p > 3`. The subtractions are in `ℕ`, and they are exact here: for
`p ≥ 5` and `k ≥ 1`, `6kp - q = p(6k - 1) - 6k ≥ 24k - 5 > 0`, and `6kq - p > 0` since `q > p`.
-/

namespace OMA.S_oeis_a180476

/-- The five primality conditions of A180476 for the prime `p` and the multiplier `k`,
with `q = p + 6k`. -/
def Good (p k : ℕ) : Prop :=
  (p + 6 * k).Prime ∧ (6 * k * p + (p + 6 * k)).Prime ∧ (6 * k * p - (p + 6 * k)).Prime ∧
    (6 * k * (p + 6 * k) + p).Prime ∧ (6 * k * (p + 6 * k) - p).Prime

/-- The conjecture of OEIS A180476: for every prime `p > 3` there is some `k > 0` such that
`q = p + 6k`, `6kp + q`, `6kp - q`, `6kq + p` and `6kq - p` are all prime. -/
theorem main : ∀ p : ℕ, p.Prime → 3 < p → ∃ k : ℕ, 0 < k ∧ Good p k := by
  sorry

end OMA.S_oeis_a180476
