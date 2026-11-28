import Mathlib

/-!
# OEIS A047211: irreducible characteristic polynomials of skew band matrices

Source: https://oeis.org/A047211
`A047211` lists the numbers congruent to `2` or `4` mod `5`. Conjecture (tested up to
`n = 177`): these are exactly the `n` such that the characteristic polynomial of `M(n)` is
irreducible over `ℚ`, where `M(n)` is the `n × n` matrix with ones on the skew diagonal and
below it and on the skew line two positions above it, and zeros elsewhere.

Conventions. Indices `i, j : Fin n` from `0`; the skew diagonal is `i + j = n - 1`, "below it"
is `i + j ≥ n - 1`, the skew line two positions above is `i + j = n - 3`. `n ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a047211

/-- The matrix `M(n)`. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if n - 1 ≤ i.val + j.val ∨ i.val + j.val + 3 = n then 1 else 0

theorem main :
    ∀ n : ℕ, 1 ≤ n → (Irreducible (M n).charpoly ↔ n % 5 = 2 ∨ n % 5 = 4) := by
  sorry

end OMA.S_oeis_a047211
