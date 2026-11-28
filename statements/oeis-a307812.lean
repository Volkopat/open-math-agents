import Mathlib

/-!
# A307812: Triangular numbers t(n) with a zeroless decimal representation such that (product of decimal digits of t(n)) / n is an integer.

Source: https://oeis.org/A307812
Credit: @darealpandaboi

Conjecture: 1 and 15 are the only terms for which (product of decimal digits of t(n)) = n.

Translation notes.
* t(n) = n(n+1)/2, n >= 1. A term t(n) is zeroless with n dividing the product of its decimal
  digits; when the product equals n, divisibility is automatic, so the conjecture says: the
  zeroless triangular numbers t(n) whose digit product equals n are exactly 1 = t(1) and 15 = t(5).
* The question whether all terms > 1 are divisible by 3 is not a conjecture and is not stated.
  A computer check for n < 3*10^6 finds only n = 1 and n = 5.
-/

namespace OMA.S_oeis_a307812

theorem main :
    {t : ℕ | ∃ n : ℕ, 0 < n ∧ t = n * (n + 1) / 2 ∧ 0 ∉ Nat.digits 10 t ∧
      (Nat.digits 10 t).prod = n} = {1, 15} := by
  sorry

end OMA.S_oeis_a307812
