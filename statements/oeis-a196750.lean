import Mathlib

/-!
# A196750: Numbers k such that 3, 5, 7 and 11 do not divide swing(k) = A056040(k).

Source: https://oeis.org/A196750
Credit: @darealpandaboi

Conjecture: there are no other terms than 0, 1, 2, 6320.

Translation notes.
* The swinging factorial is swing(k) = k! / (floor(k/2)!)^2 (A056040); the division is exact.
* The statement says the set of k with none of 3, 5, 7, 11 dividing swing(k) is exactly
  {0, 1, 2, 6320}. A computer check of all k < 2*10^6 (via p-adic valuations of factorials)
  finds exactly these.
-/

namespace OMA.S_oeis_a196750

/-- The swinging factorial k! / (floor(k/2)!)^2. -/
def swing (k : ℕ) : ℕ := k.factorial / (k / 2).factorial ^ 2

theorem main :
    {k : ℕ | ¬ 3 ∣ swing k ∧ ¬ 5 ∣ swing k ∧ ¬ 7 ∣ swing k ∧ ¬ 11 ∣ swing k} =
      {0, 1, 2, 6320} := by
  sorry

end OMA.S_oeis_a196750
