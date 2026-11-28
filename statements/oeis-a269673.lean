import Mathlib

/-!
# A269673: Number of length-n 0..3 arrays with no repeated value differing from the previous repeated value by other than plus or minus one modulo 3+1.

Source: https://oeis.org/A269673
Credit: @agchua

Colin Barker (Jan 26 2019), in the formula section of A269673:
  Conjectures from Colin Barker, Jan 26 2019: (Start)
  G.f.: 4*x*(1 - x - 4*x^2) / ((1 - 3*x)*(1 - 2*x - 5*x^2)).
  a(n) = (-20*3^n + (18-7*sqrt(6))*(1-sqrt(6))^n + (1+sqrt(6))^n*(18+7*sqrt(6))) / 15.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for all n ≥ 1 in ℝ.
Definition (R. H. Hardin's convention for these arrays, as in A269680): an array is
x(0), ..., x(n-1) with entries in 0..3 (a function Fin n → Fin 4, read as the list of its
values). A repeated value is an entry x(i) with x(i) = x(i+1), taken in the order of i; the
previous repeated value of the one at i is the one at the largest j < i with x(j) = x(j+1). The
condition is that no repeated value differs from its previous repeated value by anything other
than plus or minus one modulo 4, that is, each repeated value after the first one differs from
its previous repeated value by plus or minus one modulo 4 (pm below).
The function ok reads the array from the left and carries the latest repeated value p (none
before the first repetition): at each repetition x = y it checks the new repeated value x against
p (compat) and then carries x. The definition gives the listed terms
4, 16, 60, 224, 820, 2976, 10700, 38224, 135780, 480176 for n = 1..10 (checked by direct enumeration for the first terms and through
the resulting linear recurrence for all of them).
-/

namespace OMA.S_oeis_a269673

/-- u and v differ by plus or minus one modulo 4. -/
def pm (u v : ℕ) : Prop := v % 4 = (u + 1) % 4 ∨ u % 4 = (v + 1) % 4
instance (u v : ℕ) : Decidable (pm u v) := by
  unfold pm
  exact instDecidableOr

/-- The new repeated value x is admissible after the previous repeated value p (if any): it
differs from p by plus or minus one modulo 4. -/
def compat : Option ℕ → ℕ → Bool
  | none, _ => true
  | some r, x => decide (pm r x)

/-- ok p l: the list l satisfies the condition, p being the latest repeated value before it. -/
def ok : Option ℕ → List ℕ → Bool
  | p, x :: y :: t => if x = y then compat p x && ok (some x) (y :: t) else ok p (y :: t)
  | _, _ => true

/-- A269673: the number of arrays of length n with entries in 0..3 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 4)).filter
    (fun x => ok none (List.ofFn (fun i => ((x i : Fin 4) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f. 4x(1 - x - 4x^2)/((1 - 3x)(1 - 2x - 5x^2)), and
a(n) = (-20*3^n + (18 - 7 sqrt 6)(1 - sqrt 6)^n + (1 + sqrt 6)^n(18 + 7 sqrt 6))/15 for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - 3 * PowerSeries.X) * (1 - 2 * PowerSeries.X - 5 * PowerSeries.X ^ 2)) =
      4 * PowerSeries.X * (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = (-20 * 3 ^ n + (18 - 7 * Real.sqrt 6) * (1 - Real.sqrt 6) ^ n +
        (1 + Real.sqrt 6) ^ n * (18 + 7 * Real.sqrt 6)) / 15 := by
  sorry

end OMA.S_oeis_a269673
