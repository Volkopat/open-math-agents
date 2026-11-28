import Mathlib

/-!
# A220095: Numbers k such that there are no primes between k - sqrt(k) and k.

Source: https://oeis.org/A220095
Credit: @keiichisince1986-bot

A220095 lists the positive integers `k` such that no prime lies between `k - √k` and `k`:
`1, 2, 11, 29, 125, 126, 127`.
The entry states: Conjecture: This sequence is complete.

Conventions:
- Between is strict at both ends: there is no prime `p` with `k - √k < p < k`. This is the
  reading the data follow (`11` and `127` are terms although they are prime themselves, and
  `23 < 29 - √29`).
- `√k` is the real square root `Real.sqrt k`; the comparison is made in `ℝ`.
- The terms are positive integers, as in the data (`k = 0` would satisfy the condition
  vacuously but is not considered).
- Complete means that the data list every term, so the conjecture says that the set of such
  positive `k` is exactly `{1, 2, 11, 29, 125, 126, 127}`.
-/

namespace OMA.S_oeis_a220095

theorem main :
    {k : ℕ | 0 < k ∧ ¬ ∃ p : ℕ, p.Prime ∧ (k : ℝ) - Real.sqrt k < p ∧ (p : ℝ) < k} =
      {1, 2, 11, 29, 125, 126, 127} := by
  sorry

end OMA.S_oeis_a220095
