import Mathlib

/-!
# A093387: a(n) = 2^(n-1) - binomial(n, floor(n/2)).

Source: https://oeis.org/A093387 (OEIS Foundation, CC BY-SA 4.0)
Credit: @OrangeHeadz

The OEIS entry has offset 1 and begins 0, 0, 1, 2, 6, 12, 29, 58, 130, 260, 562, ... Its formula
section contains the recurrence of R. J. Mathar (Nov 30 2012), which a later formula there calls
Mathar's conjecture:

  (n+1)*a(n) + 2*(-n-1)*a(n-1) + 4*(-n+2)*a(n-2) + 8*(n-2)*a(n-3) = 0.

Conventions.
* The sequence starts at `n = 1`, so the recurrence is stated for every `n ≥ 4`, the indices for
  which `a(n-1)`, `a(n-2)` and `a(n-3)` are terms of the sequence.
* It is stated as an equation in the integers; `n / 2` is the floor of `n/2`.
-/

namespace OMA.S_oeis_a093387

/-- A093387 (offset 1): `a n = 2^(n-1) - binomial(n, floor(n/2))`. -/
def a (n : ℕ) : ℤ := (2 : ℤ) ^ (n - 1) - (Nat.choose n (n / 2) : ℤ)

/-- Mathar's four-term recurrence for A093387. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n + 2 * (-(n : ℤ) - 1) * a (n - 1) + 4 * (-(n : ℤ) + 2) * a (n - 2) +
      8 * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a093387
