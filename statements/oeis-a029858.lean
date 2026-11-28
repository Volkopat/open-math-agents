import Mathlib

/-!
# A029858: a(n) = (3^n - 3)/2.

Source: https://oeis.org/A029858
Credit: @ShoQo

Conjectured to be the number of integers from 0 to 10^(n-1) - 1 that lack 0, 1, 2, 3, 4, 5 and
6 as a digit. - Alexandre Wajnberg, Apr 25 2005. (Renzo Benedetti, Sep 25 2008: "This is easily
verified to be true.")

Formalization notes:
* Offset 1: the claim is stated for `n ≥ 1` (a(1) = 0, a(2) = 3, a(3) = 12, ...).
* Digits are decimal digits. The integer 0 is written "0", so it contains the digit 0 and is
  excluded explicitly (`Nat.digits 10 0` is the empty list, which would otherwise make 0
  vacuously qualify). With 0 excluded the counts match the data: 0, 3, 12, 39, ...
* `(3^n - 3)/2` is exact natural-number division (3^n - 3 is even).
-/

namespace OMA.S_oeis_a029858

/-- a(n) = (3^n - 3)/2. -/
def a (n : ℕ) : ℕ := (3 ^ n - 3) / 2

theorem main : ∀ n : ℕ, 1 ≤ n →
    ((Finset.range (10 ^ (n - 1))).filter
      (fun m => m ≠ 0 ∧ ∀ d ∈ Nat.digits 10 m, d ∉ Finset.range 7)).card = a n := by
  sorry

end OMA.S_oeis_a029858
