import Mathlib

/-!
# A275235: Number of primes between n and n+log(n)^2.

Source: https://oeis.org/A275235
Credit: @eltociear

`a(n)` (offset 1) counts the primes `p` with `n < p < n + (log n)^2` (natural logarithm); the data
fixes the strict lower end (`a(7) = 0`, since `7` itself is not counted and `11 > 7 + (log 7)^2`).
The entry comments:

  According to Schinzel's formulation of Cramer's conjecture, a(n) > 0 for n > 7; see Guy.

`main` states that for every `n > 7` there is a prime `p` with `n < p < n + (log n)^2`. For
`n ≥ 2`, `n + (log n)^2` is irrational, so the choice of `<` or `≤` at the upper end does not
matter.
-/

namespace OMA.S_oeis_a275235


/-- Schinzel's form of Cramér's conjecture, as recorded in OEIS A275235: for every `n > 7` there
is a prime strictly between `n` and `n + (log n)^2`. -/
theorem main : ∀ n : ℕ, 7 < n → ∃ p : ℕ, p.Prime ∧ n < p ∧ (p : ℝ) < n + Real.log n ^ 2 := by
  sorry

end OMA.S_oeis_a275235
