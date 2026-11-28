import Mathlib

/-!
# A380070: Square pyramidal numbers sp(n) with a zeroless decimal representation such that (product of decimal digits of sp(n)) / n is an integer.

Source: https://oeis.org/A380070
Credit: @darealpandaboi

Conjecture: the sequence has only finitely many members, i.e., for all n, sp(n) < 10^r for a
large enough r.

Translation notes.
* sp(n) = n(n+1)(2n+1)/6 is the n-th square pyramidal number; n >= 1 (offset 1).
* Zeroless: 0 is not a decimal digit of sp(n). The quotient is an integer: n divides the
  product of the decimal digits of sp(n).
* The members are the values sp(n); the statement says this set of values is finite.
* This reading reproduces the listed data: 1, 55, 385, 5525, 7714, 9455, 31395, 116795,
  3382596, 6597495, 14352975, 38381931, ... (checked by computer).
-/

namespace OMA.S_oeis_a380070

/-- The n-th square pyramidal number n(n+1)(2n+1)/6. -/
def sp (n : ℕ) : ℕ := n * (n + 1) * (2 * n + 1) / 6

theorem main :
    {m : ℕ | ∃ n : ℕ, 0 < n ∧ m = sp n ∧ 0 ∉ Nat.digits 10 (sp n) ∧
      n ∣ (Nat.digits 10 (sp n)).prod}.Finite := by
  sorry

end OMA.S_oeis_a380070
