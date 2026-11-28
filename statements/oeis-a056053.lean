import Mathlib

/-!
# A056053: a(n) = smallest odd number 2m+1 such that the partial sum of the odd harmonic series Sum_{j=0..m} 1/(2j+1) is > n.

Source: https://oeis.org/A056053
Credit: @eltociear

`a(n)` (offset 0) is the least odd number `2m + 1` such that `∑_{j=0}^m 1/(2j+1) > n`
(`1, 3, 15, 113, 837, ...`). The entry's formula section records (M. F. Hasler, Jan 24 2017):

  a(n) = A092315(n)*2 + 1 = floor(exp(n*2-Euler)/4+1/8)*2+1 for all n (conjectured).

`main` states the closed form `a(n) = 2 ⌊exp(2n - γ)/4 + 1/8⌋ + 1` for every `n`, where `γ` is the
Euler–Mascheroni constant (`Real.eulerMascheroniConstant`). The middle expression `A092315(n)*2 + 1`
is a restatement and is not formalized separately. `a n` is written with the least admissible `m`
(`sInf`; the odd harmonic series diverges, so such `m` exists). A direct comparison with the
entry's eleven listed terms agrees.
-/

namespace OMA.S_oeis_a056053

/-- `∑_{j=0}^m 1/(2j+1)`. -/
noncomputable def oddHarmonic (m : ℕ) : ℝ := ∑ j ∈ Finset.range (m + 1), 1 / (2 * (j : ℝ) + 1)

/-- OEIS A056053: `2m + 1` for the least `m` with `oddHarmonic m > n`. -/
noncomputable def a (n : ℕ) : ℕ := 2 * sInf {m : ℕ | (n : ℝ) < oddHarmonic m} + 1

/-- Hasler's conjectured closed form in OEIS A056053. -/
theorem main : ∀ n : ℕ, a n = 2 * ⌊Real.exp (2 * n - Real.eulerMascheroniConstant) / 4 + 1 / 8⌋₊ + 1 := by
  sorry

end OMA.S_oeis_a056053
