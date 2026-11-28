import Mathlib

/-!
# A253233: Smallest even pseudoprime (> 2n+1) in base 2n+1

Source: https://oeis.org/A253233

Conjecture (OEIS A253233):
In every odd base `b = 2 * n + 1` (`n ≥ 1`), there are infinitely many even
Fermat pseudoprimes `m` (composite even integers `m > b` with `b ^ (m - 1) ≡ 1 [MOD m]`).

Conventions:
- Offset: `1`; first terms: `a(1) = 286` (base `3`), `a(2) = 124` (base `5`),
  `a(3) = 16806` (base `7`), ...
- Note that any even integer `m > 2 * n + 1` with `n ≥ 1` satisfies `m ≥ 4`,
  hence is automatically composite.
-/

namespace OMA.S_oeis_a253233

/-- The set of even Fermat pseudoprimes strictly greater than `b` in base `b`. -/
def EvenPseudoprimes (b : ℕ) : Set ℕ :=
  {m : ℕ | Even m ∧ b < m ∧ ¬ Nat.Prime m ∧ b ^ (m - 1) % m = 1}

/-- Conjecture: for every odd base `2 * n + 1` (`n ≥ 1`), there are infinitely many
even Fermat pseudoprimes. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Set.Infinite (EvenPseudoprimes (2 * n + 1)) := by
  sorry

end OMA.S_oeis_a253233
