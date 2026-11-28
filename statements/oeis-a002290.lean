import Mathlib

/-!
# Sum of squares of Glaisher's `α(n)` grows like `c n⁶` (A002290)

Source: https://oeis.org/A002290
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = |α(n)|`, Glaisher's `α(n)`, equal to `|A225543(n)|` where A225543 has generating function
`∏_{k>0} (1 - x^k)^4 (1 - (-x)^k)^8`. Conjecture (Kotesovec, 2026):
`Σ_{k=1..n} a(k)² ~ c n⁶` with `c = 2.19…`.

Conventions:
* The `n`-th coefficient of the infinite product only involves the factors with `k ≤ n`, so it is
  computed from the finite product in `ℤ[X]`.
* The partial sum is taken over the coefficients of index `0..n`; shifting the index or adding
  one term does not change the asymptotics.
* `c = 2.19…` is read as `2.19 ≤ c < 2.20`.
-/

namespace OMA.S_oeis_a002290

open Polynomial Filter

/-- `|A225543(n)|`. -/
noncomputable def a (n : ℕ) : ℕ :=
  (((Finset.Icc 1 n).prod fun k => (1 - X ^ k) ^ 4 * (1 - (-X) ^ k) ^ 8 : ℤ[X]).coeff n).natAbs

theorem main :
    ∃ c : ℝ, 2.19 ≤ c ∧ c < 2.20 ∧
      Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), (a k : ℝ) ^ 2) / (n : ℝ) ^ 6) atTop
        (nhds c) := by
  sorry

end OMA.S_oeis_a002290
