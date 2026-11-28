import Mathlib

/-!
# A281229: Smallest number k of the form x^2 + y^2 with 0 <= x <= y such that gcd(x, y) = 1, x + y = n, and k has no other decompositions into a sum of two squares.

Source: https://oeis.org/A281229
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A281229 (Thomas Ordowski, Jan 18 2017): for each n
there exists such a number k.

Conventions:
* The sequence has offset 1 (data 1, 2, 5, 10, 13, 26, 29, 34, 41, 58, 61, 74, ...).
* A number k as in the name exists for n exactly when there are natural numbers x <= y with gcd(x,
  y) = 1 and x + y = n such that x^2 + y^2 has no other decomposition into a sum of two squares:
  every pair u <= v of natural numbers with u^2 + v^2 = x^2 + y^2 is the pair (x, y). The
  statement is for n >= 1 (the offset of the sequence; a(1) = 1 = 0^2 + 1^2).
-/

namespace OMA.S_oeis_a281229

/-- The conjecture recorded in A281229. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ x y : ℕ, x ≤ y ∧ Nat.gcd x y = 1 ∧ x + y = n ∧
    ∀ u v : ℕ, u ≤ v → u ^ 2 + v ^ 2 = x ^ 2 + y ^ 2 → u = x ∧ v = y := by
  sorry

end OMA.S_oeis_a281229
