import Mathlib

/-!
# OEIS A218459: least `d` with `prime(n) = x² + d y²`

Source: https://oeis.org/A218459
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest positive integer `d` such that `prime(n) = x² + d y²` has a solution in
integers. Conjecture (OEIS entry): the odd composite values of `a` belong to A176255, the numbers
of the form `4k - 1` whose least prime divisor is of the form `4m + 1`.

Conventions:
* `prime(n)` is `Nat.nth Nat.Prime n` (any indexing gives the same set of values). `a(n)` exists
  since `p = 1 + (p - 1)·1²`; it is `sInf` of the admissible `d ≥ 1`.
* 'Odd composite' means odd and `> 1` and not prime.
-/

namespace OMA.S_oeis_a218459

/-- Least `d ≥ 1` with `p = x² + d y²` solvable in integers. -/
noncomputable def a (p : ℕ) : ℕ := sInf {d : ℕ | 1 ≤ d ∧ ∃ x y : ℤ, (p : ℤ) = x ^ 2 + d * y ^ 2}

/-- Odd composite values of `a` are `≡ 3 (mod 4)` with least prime factor `≡ 1 (mod 4)`. -/
theorem main : ∀ n : ℕ, let d := a (Nat.nth Nat.Prime n);
    Odd d → 1 < d → ¬ d.Prime → d % 4 = 3 ∧ d.minFac % 4 = 1 := by
  sorry

end OMA.S_oeis_a218459
