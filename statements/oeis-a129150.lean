import Mathlib

/-!
# A129150: The n-th arithmetic derivative of 2^3

Source: https://oeis.org/A129150

Conjecture (OEIS A129150):
The sequence `a(n)` obtained by iterating the arithmetic derivative (OEIS A003415)
starting from `a(0) = 2^3 = 8` is strictly increasing.

Conventions:
- Offset: `0`; first terms: `8, 12, 16, 32, 80, 176, 368, 752, 1520, ...`.
- The arithmetic derivative of `n : ℕ` is `n' = ∑_{p ∣ n} (n / p) * v_p(n)` (with
  `0' = 1' = 0`), implemented directly via `n.primeFactors` and `n.factorization`.
-/

namespace OMA.S_oeis_a129150

/-- The arithmetic derivative of `n : ℕ` (OEIS A003415). -/
def arithDeriv (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, (n / p) * n.factorization p

/-- The `n`-th arithmetic derivative of `8 = 2^3` (OEIS A129150). -/
def a : ℕ → ℕ
  | 0 => 8
  | n + 1 => arithDeriv (a n)

/-- Conjecture: the sequence A129150 is strictly increasing. -/
theorem main : ∀ n : ℕ, a n < a (n + 1) := by
  sorry

end OMA.S_oeis_a129150
