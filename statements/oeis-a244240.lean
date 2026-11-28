import Mathlib

/-!
# A244240: Number of partitions of n into 4 parts such that every i-th smallest part (counted with multiplicity) is different from i.

Source: https://oeis.org/A244240
Credit: @rtflynn

Chai Wah Wu (Apr 18 2024), in the formula section of A244240:
  Conjectures: a(n) = a(n-1) + a(n-2) - 2*a(n-5) + a(n-8) + a(n-9) - a(n-10) for n > 26.
  G.f.: x^14*(-x^4 + x + 1)*(x^8 - x^5 - 2*x^4 + 2*x + 1)/((x - 1)^4*(x + 1)^2*(x^2 + 1)*(x^2 + x + 1)).

Conventions:
* A partition of n into 4 parts is a `Nat.Partition n` with 4 parts. Its parts in increasing
  order, counted with multiplicity, are `p.parts.sort (· ≤ ·)`; the i-th smallest part is the entry
  at index i - 1 of that list, and the condition is that it is different from i, for i = 1..4.
* Offset 14. The definition gives a(n) = 0 for n < 14, so the power series ∑ a(n) X^n over all
  n ≥ 0 is the g.f. of the entry; the g.f. is stated as an identity of formal power series over ℚ,
  (∑ a(n) X^n) * denominator = numerator, with the factors written exactly as in the source.
* The recurrence is stated in ℤ for every n ≥ 27 (n > 26).

Numerical check: a Python copy of the definition gives 0 for n = 10..13 and then 1, 4, 7, 11, 15,
19, 25, 30, 37, 44, 53, 61, 72, 82, 95, 107, 122, 136, 154, 170, 190, 209 for n = 14..35, the DATA
of the entry.
-/

namespace OMA.S_oeis_a244240

/-- A244240: the number of partitions of n into 4 parts whose i-th smallest part is not i. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {p : n.Partition // p.parts.card = 4 ∧
    ∀ (i : ℕ) (h : i < (p.parts.sort (· ≤ ·)).length), (p.parts.sort (· ≤ ·))[i] ≠ i + 1}

/-- Wu's conjectures: the recurrence for n > 26 and the rational g.f. -/
theorem main : (∀ n : ℕ, 27 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 2) - 2 * a (n - 5) +
      a (n - 8) + a (n - 9) - a (n - 10)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((PowerSeries.X - 1) ^ 4 * (PowerSeries.X + 1) ^ 2 * (PowerSeries.X ^ 2 + 1) *
        (PowerSeries.X ^ 2 + PowerSeries.X + 1)) =
      PowerSeries.X ^ 14 * (-PowerSeries.X ^ 4 + PowerSeries.X + 1) *
        (PowerSeries.X ^ 8 - PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 4 +
          2 * PowerSeries.X + 1) := by
  sorry

end OMA.S_oeis_a244240
