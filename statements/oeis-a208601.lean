import Mathlib

/-!
# A208601: Number of 7-bead necklaces labeled with numbers -n..n not allowing reversal, with sum zero.

Source: https://oeis.org/A208601
Credit: @rtflynn

Colin Barker (Mar 07 2018), in the formula section of A208601:
  Conjectures: G.f.: x*(57 + 764*x + 1727*x^2 + 750*x^3 + 71*x^4 - 6*x^5 + x^6) / (1 - x)^7.
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Conventions:
* A labeling of the 7 beads is a function f : Fin 7 → ℤ with every value in -n..n and sum zero.
* Necklaces not allowing reversal: two labelings f, g give the same necklace when one is a rotation
  of the other: g(i) = f(i + r) for all i, for some r (indices mod 7). This relation is an
  equivalence, and `a n` is the number of its classes, `Nat.card` of the quotient.
* Offset 1. The definition also gives a value at n = 0 (one necklace, all labels 0), which is not a
  term: the g.f. is stated for the series with constant term 0 and coefficient a(n) at X^n for
  n ≥ 1, as an identity of formal power series over ℚ, (∑ a(n) X^n) * (1 - X)^7 = numerator.
* The recurrence is stated in ℤ for every n ≥ 8 (n > 7).

Numerical check: a Python copy of the definition (orbits counted by brute force) gives
57, 1163, 8671 for n = 1..3, the DATA of the entry.
-/

namespace OMA.S_oeis_a208601

/-- Labelings of 7 beads by numbers -n..n with sum zero. -/
def L (n : ℕ) : Type :=
  {f : Fin 7 → ℤ // (∀ i, -(n : ℤ) ≤ f i ∧ f i ≤ n) ∧ ∑ i, f i = 0}

/-- Two labelings give the same necklace (reversal not allowed). -/
def SameNecklace (n : ℕ) (f g : L n) : Prop :=
  ∃ r : Fin 7, ∀ i, g.1 i = f.1 (i + r)

/-- A208601: the number of 7-bead necklaces labeled with numbers -n..n not allowing reversal,
with sum zero. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Quot (SameNecklace n))

/-- Barker's conjectures: the rational g.f. and the recurrence for n > 7. -/
theorem main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - PowerSeries.X) ^ 7 =
      PowerSeries.X * (57 + 764 * PowerSeries.X + 1727 * PowerSeries.X ^ 2 +
        750 * PowerSeries.X ^ 3 + 71 * PowerSeries.X ^ 4 -
        6 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6) ∧
    ∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
      35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a208601
