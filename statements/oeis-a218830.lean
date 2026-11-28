import Mathlib

/-!
# A218830: Largest odd integer not of the form p+2q with p, q, p^2+4(2^n-1)q^2 all prime, or 0 if there would be no such upper bound.

Source: https://oeis.org/A218830
Credit: @eltociear

For `n ≥ 1`, call a positive odd integer `m` *representable* if `m = p + 2q` with `p`, `q` and
`p^2 + 4(2^n - 1) q^2` all prime. `a(n)` (offset 1) is the largest positive odd integer that is
not representable (`a(3) = 73`, `a(4) = 15`), or `0` if there is no such upper bound. The entry
records the conjecture of Zhi-Wei Sun (Nov 07 2012, arXiv:1211.1588):

  for any n > 0, there is only a finite number of positive odd integers not of the given form.

`main` states that for every `n ≥ 1` the set of positive odd integers that are not representable
is finite. Since `n ≥ 1`, `2 ^ n - 1` is an exact natural-number subtraction.
-/

namespace OMA.S_oeis_a218830

/-- `m = p + 2q` with `p`, `q` and `p^2 + 4(2^n - 1) q^2` all prime. -/
def Representable (n m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p + 2 * q ∧ (p ^ 2 + 4 * (2 ^ n - 1) * q ^ 2).Prime

/-- Sun's conjecture recorded in OEIS A218830: for every `n ≥ 1`, only finitely many positive odd
integers are not representable. -/
theorem main : ∀ n : ℕ, 1 ≤ n → {m : ℕ | 0 < m ∧ Odd m ∧ ¬ Representable n m}.Finite := by
  sorry

end OMA.S_oeis_a218830
