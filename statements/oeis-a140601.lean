import Mathlib

/-!
# A140601: Values of m such that binomial(m, a) + binomial(m, b) divides binomial(m, a + b) for some distinct nonnegative integers a and b with a + b <= m.

Source: https://oeis.org/A140601
Credit: @gblacher2

Conjecture (Stefan Steinerberger, comment in A140601): "there are infinitely many terms", that
is, there are infinitely many `m` for which some distinct nonnegative integers `a`, `b` with
`a + b ≤ m` satisfy `C(m, a) + C(m, b) ∣ C(m, a + b)`.

Conventions: `C(m, k)` is Mathlib's `Nat.choose m k`. The terms are natural numbers `m`; the
conditions `a ≠ b` and `a + b ≤ m` are exactly those of the OEIS name.

With this definition the terms below 1900 are 19, 34, 41, 89, 104, 359, 398, 495, 527, 1845, as
in the OEIS data (for example `C(19, 3) + C(19, 5) ∣ C(19, 8)`).
-/

namespace OMA.S_oeis_a140601

/-- `m` is a term of A140601: there are distinct nonnegative integers `a`, `b` with `a + b ≤ m`
such that `C(m, a) + C(m, b)` divides `C(m, a + b)`. -/
def IsTerm (m : ℕ) : Prop :=
  ∃ a b : ℕ, a ≠ b ∧ a + b ≤ m ∧ (m.choose a + m.choose b) ∣ m.choose (a + b)

/-- Steinerberger's conjecture: A140601 has infinitely many terms. -/
theorem main : {m : ℕ | IsTerm m}.Infinite := by
  sorry

end OMA.S_oeis_a140601
