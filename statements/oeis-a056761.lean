import Mathlib

/-!
# A056761: Odd numbers less than the cube of their number of divisors.

Source: https://oeis.org/A056761
Credit: @Rob1Ham

OEIS A056761 (offset 1, keywords fini,full,nonn) lists the odd natural numbers strictly less than
the cube of their number of positive divisors. The entry records that the last term is
a(267) = 883575, confirming the conjecture of Labos Elemer. Accordingly, main states that 883575
belongs to A056761, no larger natural number belongs to A056761, and the set of terms has
cardinality 267.
-/

namespace OMA.S_oeis_a056761

/-- Membership in OEIS A056761: odd natural numbers strictly less than the cube of their
number of positive divisors. -/
def IsA056761 (n : ℕ) : Prop :=
  Odd n ∧ n < n.divisors.card ^ 3

theorem main :
    IsA056761 883575 ∧
    (∀ n : ℕ, IsA056761 n → n ≤ 883575) ∧
    {n : ℕ | IsA056761 n}.ncard = 267 := by
  sorry

end OMA.S_oeis_a056761
