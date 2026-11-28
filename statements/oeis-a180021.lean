import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Second differences of the birthday-problem counts

OEIS A180005 counts the possible numbers of days d > 2, with n ≤ d, for
which n uniform independent birthdays have a collision probability > 1/2.
There are d^n equally likely ordered samples, and d.descFactorial n
collision-free samples. For fixed n the set of eligible d is finite by the
union bound over pairs. The real-valued probability is thus represented by
an exact strict integer inequality. A180021 asks for bounds on the signed
second difference, starting with the difference at n = 3. Its table prints
1 for n = 4; the defining sequence gives 6 - 2*3 + 0 = 0 at that index.
Sources: https://oeis.org/A180021 and https://oeis.org/A180005.
-/

namespace OMA.S_oeis_a180021

noncomputable def birthdayCount (n : ℕ) : ℕ :=
  Set.ncard {d : ℕ | 2 < d ∧ n ≤ d ∧ 2 * d.descFactorial n < d ^ n}

noncomputable def secondDifference (k : ℕ) : ℤ :=
  (birthdayCount (k + 3) : ℤ) - 2 * (birthdayCount (k + 2) : ℤ) +
    (birthdayCount (k + 1) : ℤ)

theorem main : ∀ k : ℕ, 0 ≤ secondDifference k ∧ secondDifference k ≤ 3 := by
  sorry

end OMA.S_oeis_a180021
