import Mathlib

/-!
# A323206: A(n, k) = hypergeometric([-k, k+1], [-k-1], n)

Source: https://oeis.org/A323206
Credit: @ehsanmok (agent: Claude Code, model claude-opus-5-5)

Square array for `n, k ≥ 0`: `1, 1, 1, 1, 2, 1, 1, 3, 5, 1, …` (row `n = 1` is the Catalan numbers).
Conjecture (OEIS A323206): `A(n, k)` is odd if and only if `n` is even or (`n` is odd and
`k + 2 = 2^j` for some `j > 0`).

## Encoding

* `A(n, k) = ∑_{j=0}^{k} (-k)_j (k+1)_j / ((-k-1)_j j!) n^j`, with the rising factorial
  `(x)_j = x (x+1) ⋯ (x+j-1)` (`ascPochhammer`). The series terminates: `(-k)_j = 0` for `j > k`,
  and the lower parameter `(-k-1)_j` is nonzero for `j ≤ k`. This is the terminating
  hypergeometric sum the entry uses (it equals the entry formula
  `∑_{j=0}^{k} binomial(k+j, k) (1 - j/(k+1)) n^j`). It is computed in `ℚ`.
* `A(n, k)` is odd means it is an odd integer: `∃ m : ℤ, A n k = m ∧ Odd m`.
-/

namespace OMA.S_oeis_a323206

open Polynomial

/-- The `j`-th term `(-k)_j (k+1)_j / ((-k-1)_j j!) n^j` of the hypergeometric series. -/
noncomputable def term (n k j : ℕ) : ℚ :=
  (ascPochhammer ℚ j).eval (-(k : ℚ)) * (ascPochhammer ℚ j).eval ((k : ℚ) + 1) /
    ((ascPochhammer ℚ j).eval (-(k : ℚ) - 1) * (j.factorial : ℚ)) * (n : ℚ) ^ j

/-- `A(n, k) = hypergeometric([-k, k+1], [-k-1], n)`. -/
noncomputable def A (n k : ℕ) : ℚ := ∑ j ∈ Finset.range (k + 1), term n k j

theorem main : ∀ n k : ℕ, (∃ m : ℤ, A n k = m ∧ Odd m) ↔
    (Even n ∨ (Odd n ∧ ∃ j : ℕ, 0 < j ∧ k + 2 = 2 ^ j)) := by
  sorry

end OMA.S_oeis_a323206
