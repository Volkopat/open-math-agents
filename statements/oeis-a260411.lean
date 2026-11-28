import Mathlib

/-!
# A260411: Number of ways n can be represented as a sum of a positive cube, a positive square, and a positive triangular number.

Source: https://oeis.org/A260411
Credit: @darealpandaboi

Conjecture: every integer appears in the sequence finitely many times.

Translation notes.
* a(n) counts triples (x, y, z) of positive integers with x^3 + y^2 + z(z+1)/2 = n. This
  reproduces all 91 listed terms a(0..90) (checked by computer).
* The values of a are natural numbers, so every integer means every t >= 0: for each t the set
  of n with a(n) = t is finite. The remark that there appear to be 14 zeros and 33 ones is an
  observation, not part of the conjecture.
-/

namespace OMA.S_oeis_a260411

/-- The number of (x, y, z), all positive, with x^3 + y^2 + z(z+1)/2 = n. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun t => t.1 ^ 3 + t.2.1 ^ 2 + t.2.2 * (t.2.2 + 1) / 2 = n)).card

theorem main : ∀ t : ℕ, {n : ℕ | a n = t}.Finite := by
  sorry

end OMA.S_oeis_a260411
