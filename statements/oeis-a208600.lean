import Mathlib

/-!
# A208600: Number of 6-bead necklaces labeled with numbers -n..n not allowing reversal, with sum zero.

Source: https://oeis.org/A208600
Credit: @rtflynn

Colin Barker (Mar 07 2018), in the formula section of A208600:
  Conjectures: G.f.: x*(26 + 141*x + 172*x^2 + 8*x^3 + 6*x^4 - x^5) / (1 - x)^6.
  a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.

Conventions:
* A labeling of the 6 beads is a function f : Fin 6 → ℤ with every value in -n..n and sum zero.
* Necklaces not allowing reversal: two labelings f, g give the same necklace when one is a rotation
  of the other: g(i) = f(i + r) for all i, for some r (indices mod 6). This relation is an
  equivalence, and `a n` is the number of its classes, `Nat.card` of the quotient.
* Offset 1. The definition also gives a value at n = 0 (one necklace, all labels 0), which is not a
  term: the g.f. is stated for the series with constant term 0 and coefficient a(n) at X^n for
  n ≥ 1, as an identity of formal power series over ℚ, (∑ a(n) X^n) * (1 - X)^6 = numerator.
* The recurrence is stated in ℤ for every n ≥ 7 (n > 6).

Numerical check: a Python copy of the definition (orbits counted by brute force) gives
26, 297, 1564, 5457 for n = 1..4, the DATA of the entry.
-/

namespace OMA.S_oeis_a208600

/-- Labelings of 6 beads by numbers -n..n with sum zero. -/
def L (n : ℕ) : Type :=
  {f : Fin 6 → ℤ // (∀ i, -(n : ℤ) ≤ f i ∧ f i ≤ n) ∧ ∑ i, f i = 0}

/-- Two labelings give the same necklace (reversal not allowed). -/
def SameNecklace (n : ℕ) (f g : L n) : Prop :=
  ∃ r : Fin 6, ∀ i, g.1 i = f.1 (i + r)

/-- A208600: the number of 6-bead necklaces labeled with numbers -n..n not allowing reversal,
with sum zero. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Quot (SameNecklace n))

/-- Barker's conjectures: the rational g.f. and the recurrence for n > 6. -/
theorem main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - PowerSeries.X) ^ 6 =
      PowerSeries.X * (26 + 141 * PowerSeries.X + 172 * PowerSeries.X ^ 2 +
        8 * PowerSeries.X ^ 3 + 6 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5) ∧
    ∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a208600
