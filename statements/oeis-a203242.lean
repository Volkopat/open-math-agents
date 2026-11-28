import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A203242: second elementary symmetric sums of the Mersenne numbers

The OEIS entry A203242 records a recurrence of R. J. Mathar and a generating
function of Colin Barker. Robert Israel verified both in 2019.
The indexed sequence starts at two. At zero and one the sum of pairs is empty.
Source: https://oeis.org/A203242
-/

namespace OMA.S_oeis_a203242

open PowerSeries

/-- The sum of the first n entries and the sum of all products of two distinct entries. -/
def sums : ℕ → ℚ × ℚ
  | 0 => (0, 0)
  | n + 1 =>
    let (s, a) := sums n
    let t : ℚ := 2 ^ (n + 1) - 1
    (s + t, a + s * t)

def a (n : ℕ) : ℚ := (sums n).2

theorem main :
    (∀ n : ℕ, 5 < n →
      (-103 * (n : ℚ) + 258) * a n + (881 * (n : ℚ) - 2116) * a (n - 1) +
      6 * (-427 * (n : ℚ) + 960) * a (n - 2) +
      4 * (766 * (n : ℚ) - 1545) * a (n - 3) +
      16 * (-80 * (n : ℚ) + 121) * a (n - 4) = 0) ∧
    ((1 - X : ℚ⟦X⟧) ^ 3 * (1 - C 2 * X) ^ 2 * (1 - C 4 * X) * mk a =
      C 3 * X ^ 2 - C 2 * X ^ 3 - C 4 * X ^ 4) := by
  sorry

end OMA.S_oeis_a203242
