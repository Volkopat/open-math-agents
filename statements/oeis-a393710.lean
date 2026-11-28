import Mathlib

/-!
# A393710: a(n) = number of triples (x, y, z) such that x^2 + y*z = n, where x, y, z are positive integers satisfying x < y < z.

Source: https://oeis.org/A393710
Credit: @darealpandaboi

Conjectures: each nonnegative integer occurs only finitely many times in the sequence; and
a(1722) = 0 and a(n) > 0 for n > 1722; a(1482) = 1 and a(n) != 1 for n > 1482.

Translation notes.
* a(n) counts triples of positive integers x < y < z with x^2 + y*z = n (offset 0). This
  reproduces the listed data a(0..105) (checked by computer).
* The source says each nonnegative positive integer; the values are natural numbers and the
  second conjecture makes 0 occur finitely often too, so the first conjecture is stated for
  every t >= 0.
* A computer check up to n = 12000 confirms a(1722) = 0, a(1482) = 1, and that 1722 and 1482
  are the last n <= 12000 with a(n) = 0 and a(n) = 1 respectively.
-/

namespace OMA.S_oeis_a393710

/-- The number of triples 0 < x < y < z with x^2 + y*z = n. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 ^ 2 + t.2.1 * t.2.2 = n)).card

theorem main :
    (∀ t : ℕ, {n : ℕ | a n = t}.Finite) ∧
    (a 1722 = 0 ∧ ∀ n : ℕ, 1722 < n → 0 < a n) ∧
    (a 1482 = 1 ∧ ∀ n : ℕ, 1482 < n → a n ≠ 1) := by
  sorry

end OMA.S_oeis_a393710
