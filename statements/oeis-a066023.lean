import Mathlib

/-!
# A066023: (a(n)^7+1)/(n^7+1) is the smallest integer > 1.

Source: https://oeis.org/A066023
Credit: @gblacher2

-/

namespace OMA.S_oeis_a066023

/-- `a n` is the least `m` such that `(m^7 + 1) / (n^7 + 1)` is an integer greater than `1`,
i.e. `m^7 + 1 = k * (n^7 + 1)` for some integer `k > 1` (OEIS A066023, offset 1).
For fixed `n`, the quotient increases with `m`, so the least such `m` gives the least quotient. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ k : ℕ, 1 < k ∧ m ^ 7 + 1 = k * (n ^ 7 + 1)}

/-- Conjecture (R. J. Mathar, 2014): `a(n) = A000578(n) = n^3` for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → a n = n ^ 3 := by
  sorry

end OMA.S_oeis_a066023
