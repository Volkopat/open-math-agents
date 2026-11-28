import Mathlib

/-!
# A090079: In binary expansion of n: reduce contiguous blocks of 0's to 0 and contiguous blocks of 1's to 1.

Source: https://oeis.org/A090079
Credit: @jagong-cmu

The entry gives (Velin Yanev, Dec 12 2016):
Conjecture: a(n) = (2^(A005811(n)+1) + (1-(-1)^n)/2 - 2)/3.

Here A005811(n) is the number of runs in the binary expansion of n (n > 0), with
A005811(0) = 0.

Conventions:
* Offset 0, as in the entry (data: 0, 1, 2, 1, 2, 5, 2, 1, 2, 5, 10, ...).
* `Nat.digits 2 n` is the list of binary digits of `n`, least significant digit first
  (`Nat.digits 2 0 = []`). `List.destutter (· ≠ ·)` replaces each maximal block of equal
  adjacent entries by one entry, so it reduces each contiguous block of 0's to 0 and each
  contiguous block of 1's to 1. The order of the digits does not change this reduction.
  `Nat.ofDigits 2` reads the reduced list back as a number.
* The number of runs, A005811(n), is the length of the reduced list (it is 0 for n = 0).
* The formula is computed in `ℤ`. The divisions `/ 2` and `/ 3` are exact, and the claim is
  stated for every `n ≥ 0`.
-/

namespace OMA.S_oeis_a090079

/-- The binary digits of `n` (least significant first), with each block of equal adjacent
digits reduced to one digit. -/
def reduced (n : ℕ) : List ℕ := (Nat.digits 2 n).destutter (· ≠ ·)

/-- A090079: the number whose binary expansion is the reduced expansion of `n`. -/
def a (n : ℕ) : ℕ := Nat.ofDigits 2 (reduced n)

/-- A005811: the number of runs in the binary expansion of `n`. -/
def runs (n : ℕ) : ℕ := (reduced n).length

/-- `a(n) = (2^(A005811(n)+1) + (1-(-1)^n)/2 - 2)/3` for every `n ≥ 0`. -/
theorem main :
    ∀ n : ℕ, (a n : ℤ) = (2 ^ (runs n + 1) + (1 - (-1) ^ n) / 2 - 2) / 3 := by
  sorry

end OMA.S_oeis_a090079
