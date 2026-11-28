import Mathlib

/-!
# A177265: Mathar's recurrence

Source: https://oeis.org/A177265
Credit: @ivillar

Status: known result. The entry records: The above conjecture is correct. See Ray, 2026. - Deepnil Ray,
Aug 10 2026.

A177265 (offset 1): number of permutations of {1,2,...,n} having exactly one string of consecutive
fixed points (including singletons);
data 1, 1, 4, 12, 57, 321, 2176, 17008, 150505, 1485465, 16170036, 192384876, ...

Conjecture (R. J. Mathar, Jul 01 2022): D-finite with recurrence
a(n) - (n-1)*a(n-1) - (n-1)*a(n-2) +(n-1)*a(n-3) + (n-2)*a(n-4) = 0.

Formalization: the entry records a(1) = 1, a(2) = 1, a(n) = a(n-1) + n*A000166(n-1) (Daniel Suteu,
Jan 25 2018), where A000166 are the derangement numbers (`numDerangements` in Mathlib). Since
A000166(1) = 0, the recurrence also gives a(2) = a(1) + 2*0 = 1, so a(n) is defined here by a(1) = 1
and a(n) = a(n-1) + n*A000166(n-1) for n ≥ 2 (with values in ℤ; the value a(0) = 0 is a placeholder
and is not used). The sequence has offset 1 and the recurrence involves a(n-4), so it is stated for
n ≥ 5; it is checked by the data, for example at n = 5:
(1)*(57) + (-4)*(12) + (-4)*(4) + (4)*(1) + (3)*(1) = 0.
-/

namespace OMA.S_oeis_a177265

/-- a(1) = 1, a(n) = a(n-1) + n*d(n-1) for n ≥ 2, with d the derangement numbers (a(0) = 0 is a
placeholder). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => a (n + 1) + ((n : ℤ) + 2) * (numDerangements (n + 1) : ℤ)

/-- Mathar's conjectured recurrence for A177265, for n ≥ 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n - ((n : ℤ) - 1) * a (n - 1) - ((n : ℤ) - 1) * a (n - 2) + ((n : ℤ) - 1) * a (n - 3) +
      ((n : ℤ) - 2) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a177265
