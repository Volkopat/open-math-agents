import Mathlib

/-!
# A026923: Number of partitions of n into an odd number of parts, the greatest being 3; also, a(n+5) = number of partitions of n+2 into an even number of parts, each <= 3.

Source: https://oeis.org/A026923
Credit: @rtflynn

Colin Barker (Sep 01 2019), in the formula section of A026923:
  Conjectures: G.f.: x^3*(1 - x + x^2 + x^4) / ((1 - x)^3*(1 + x)^2*(1 - x + x^2)*(1 + x^2)*(1 + x + x^2)).
  a(n) = a(n-1) + a(n-4) - a(n-5) + a(n-6) - a(n-7) - a(n-10) + a(n-11) for n>11.

Conventions:
* The first description of the NAME is the definition: partitions of n (`Nat.Partition n`) with an
  odd number of parts whose greatest part is 3 (3 is a part and every part is ≤ 3). The second
  description (*also, ...*) is not used.
* Offset 1. The definition also gives a(0) = 0 (the empty partition has no part 3), so the power
  series ∑ a(n) X^n over all n ≥ 0 is the g.f. of the entry; the g.f. is stated as an identity of
  formal power series over ℚ, (∑ a(n) X^n) * denominator = numerator.
* The recurrence is stated in ℤ for every n ≥ 12 (n > 11).

Numerical check: a Python copy of the definition gives the DATA of the entry for n = 1..28.
-/

namespace OMA.S_oeis_a026923

/-- A026923: the number of partitions of n into an odd number of parts, the greatest being 3. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {p : n.Partition // Odd p.parts.card ∧ 3 ∈ p.parts ∧ ∀ i ∈ p.parts, i ≤ 3}

/-- Barker's conjectures: the rational g.f. and the recurrence for n > 11. -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2 *
        (1 - PowerSeries.X + PowerSeries.X ^ 2) * (1 + PowerSeries.X ^ 2) *
        (1 + PowerSeries.X + PowerSeries.X ^ 2)) =
      PowerSeries.X ^ 3 * (1 - PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 4) ∧
    ∀ n : ℕ, 12 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) + a (n - 6) - a (n - 7) -
      a (n - 10) + a (n - 11) := by
  sorry

end OMA.S_oeis_a026923
