import Mathlib

/-!
# Identity relating floor function and hexagonal numbers

Source: https://mathoverflow.net/questions/450392
Credit: @ivillar

The question considers the sum of the square roots of all natural numbers between two
consecutive perfect squares $n^2$ and $(n+1)^2$ (both inclusive) and observes that the floor of
this sum is a hexagonal number:
$$\left\lfloor \sum_{h=0}^{2n+1} \sqrt{n^2+h} \right\rfloor = H(n+1),$$
where $H(n+1) = 2n^2+3n+1 = (n+1)(2(n+1)-1)$. The values quoted in the question are
$6, 15, 28, \ldots$ for $n = 1, 2, 3, \ldots$.

Formalization notes:
* `hexagonal m = m * (2 * m - 1)` is the `m`-th hexagonal number (1, 6, 15, 28, ...).
* The sum runs over `h = 0, ..., 2n+1`, that is over `Finset.range (2 * n + 2)`; the square roots
  are real square roots and the floor is the natural-number floor of a nonnegative real.
* `n` ranges over the positive integers, as in the values listed in the question.
-/

namespace OMA.S_mo_450392

/-- The `m`-th hexagonal number `m (2m - 1)`. -/
def hexagonal (m : ℕ) : ℕ := m * (2 * m - 1)

/-- The floor of `√(n²) + √(n² + 1) + ... + √((n+1)²)` is the hexagonal number `H(n+1)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ⌊∑ h ∈ Finset.range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ))⌋₊ = hexagonal (n + 1) := by
  sorry

end OMA.S_mo_450392
