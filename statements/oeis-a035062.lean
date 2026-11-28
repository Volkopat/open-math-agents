import Mathlib

/-!
# A035062: Numbers n such that 2^n does not contain the digit 7.

Source: https://oeis.org/A035062
Credit: @darealpandaboi

Conjecture: 71 is the last term.

Translation notes.
* Contains the digit 7 means 7 occurs among the decimal digits of 2^n.
* 71 is the last term is stated as: for every n > 71, 2^n contains the digit 7.
* The terms below 5000 are exactly the listed data 0, 1, ..., 14, 16, 18, 19, 22, 23, 25, 28,
  33, 41, 42, 49, 50, 54, 61, 71 (checked by computer).
-/

namespace OMA.S_oeis_a035062

theorem main : ∀ n : ℕ, 71 < n → 7 ∈ Nat.digits 10 (2 ^ n) := by
  sorry

end OMA.S_oeis_a035062
