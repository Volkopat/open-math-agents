import Mathlib

/-!
# A269687: Number of length-n 0..5 arrays with no repeated value differing from the previous repeated value by plus or minus one modulo 5+1.

Source: https://oeis.org/A269687
Credit: @agchua

Colin Barker (Jan 27 2019), in the formula section of A269687:
  Conjectures from Colin Barker, Jan 27 2019: (Start)
  G.f.: 6*x*(1 - 4*x - 3*x^2) / ((1 - 5*x)*(1 - 5*x - 4*x^2)).
  a(n) = (3/205)*2^(-2-n)*(-41*2^(2+n)*5^n-5*(5-sqrt(41))^n*(-41+7*sqrt(41)) + 5*(5+sqrt(41))^n*(41+7*sqrt(41))).
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for all n ≥ 1 in ℝ.
Definition (R. H. Hardin's convention for these arrays, as in A269680): an array is
x(0), ..., x(n-1) with entries in 0..5 (a function Fin n → Fin 6, read as the list of its
values). A repeated value is an entry x(i) with x(i) = x(i+1), taken in the order of i; the
previous repeated value of the one at i is the one at the largest j < i with x(j) = x(j+1). The
condition is that no repeated value differs from its previous repeated value by plus or minus one
modulo 6 (pm below).
The function ok reads the array from the left and carries the latest repeated value p (none
before the first repetition): at each repetition x = y it checks the new repeated value x against
p (compat) and then carries x. The definition gives the listed terms
6, 36, 216, 1284, 7584, 44556, 260616, 1518804, 8823984, 51132636 for n = 1..10 (checked by direct enumeration for the first terms and through
the resulting linear recurrence for all of them).
-/

namespace OMA.S_oeis_a269687

/-- u and v differ by plus or minus one modulo 6. -/
def pm (u v : ℕ) : Prop := v % 6 = (u + 1) % 6 ∨ u % 6 = (v + 1) % 6
instance (u v : ℕ) : Decidable (pm u v) := by
  unfold pm
  exact instDecidableOr

/-- The new repeated value x is admissible after the previous repeated value p (if any): it does
not differ from p by plus or minus one modulo 6. -/
def compat : Option ℕ → ℕ → Bool
  | none, _ => true
  | some r, x => !decide (pm r x)

/-- ok p l: the list l satisfies the condition, p being the latest repeated value before it. -/
def ok : Option ℕ → List ℕ → Bool
  | p, x :: y :: t => if x = y then compat p x && ok (some x) (y :: t) else ok p (y :: t)
  | _, _ => true

/-- A269687: the number of arrays of length n with entries in 0..5 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 6)).filter
    (fun x => ok none (List.ofFn (fun i => ((x i : Fin 6) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f. 6x(1 - 4x - 3x^2)/((1 - 5x)(1 - 5x - 4x^2)), and
a(n) = (3/205)2^(-2-n)(-41*2^(2+n)*5^n - 5(5 - sqrt 41)^n(-41 + 7 sqrt 41) + 5(5 + sqrt 41)^n(41 + 7 sqrt 41)) (the power 2^(-2-n) taken in ℝ as an integer power) for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - 5 * PowerSeries.X) * (1 - 5 * PowerSeries.X - 4 * PowerSeries.X ^ 2)) =
      6 * PowerSeries.X * (1 - 4 * PowerSeries.X - 3 * PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = (3 / 205) * (2 : ℝ) ^ (-2 - (n : ℤ)) * (-41 * 2 ^ (2 + n) * 5 ^ n -
        5 * (5 - Real.sqrt 41) ^ n * (-41 + 7 * Real.sqrt 41) + 5 * (5 + Real.sqrt 41) ^ n * (41 + 7 * Real.sqrt 41)) := by
  sorry

end OMA.S_oeis_a269687
