import Mathlib

/-!
# OEIS A339210: Prime-index pentagonal sum equals 2

Source: https://oeis.org/A339210 (OEIS Foundation, CC BY-SA 4.0).
Definition: `a(n) = ∑_{k=0}^{⌊(n+1)/2⌋} A010815(n * k)`, where `A010815(m)` is the coefficient
of `q^m` in Euler's pentagonal product `∏_{j≥1} (1 - q^j)`, equal to `(-1)^j` if
`m = j * (3 * j - 1) / 2` for some integer `j`, and `0` otherwise.

Conjecture (OEIS A339210): `a(p) = 2` for every prime `p > 5`.
-/

namespace OMA.S_oeis_a339210

/-- The Euler pentagonal coefficient `A010815(m)`: `(-1)^|j|` if `2 * m = j * (3 * j - 1)` for
some integer `j`, and `0` otherwise. Since `j ↦ j * (3 * j - 1)` is injective on `ℤ` and
`2 * m = j * (3 * j - 1)` implies `|j| ≤ m`, summing over `[-m, m]` gives the exact value. -/
noncomputable def pentCoeff (m : ℕ) : ℤ :=
  ∑ j ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
    if j * (3 * j - 1) = 2 * (m : ℤ) then (-1 : ℤ) ^ j.natAbs else 0

/-- OEIS A339210: `a(n) = ∑_{k=0}^{⌊(n+1)/2⌋} A010815(n * k)`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range ((n + 1) / 2 + 1), pentCoeff (n * k)

/-- Conjecture on OEIS A339210: `a(p) = 2` for every prime `p > 5`. -/
theorem main : ∀ p : ℕ, p.Prime → 5 < p → a p = 2 := by
  sorry

end OMA.S_oeis_a339210
