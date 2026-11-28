import Mathlib

/-!
# A269688: Number of length-n 0..6 arrays with no repeated value differing from the previous repeated value by plus or minus one modulo 6+1.

Source: https://oeis.org/A269688
Credit: @agchua

Colin Barker (Jan 27 2019), in the formula section of A269688:
  Conjectures from Colin Barker, Jan 27 2019: (Start)
  G.f.: 7*x*(1 - 5*x - 4*x^2) / ((1 - 6*x)*(1 - 6*x - 5*x^2)).
  a(n) = (-7*2^(1+n)*3^n + (21-6*sqrt(14))*(3-sqrt(14))^n + 3*(3+sqrt(14))^n*(7+2*sqrt(14))) / 30.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for all n ≥ 1 in ℝ.
Definition (R. H. Hardin's convention for these arrays, as in A269680): an array is
x(0), ..., x(n-1) with entries in 0..6 (a function Fin n → Fin 7, read as the list of its
values). A repeated value is an entry x(i) with x(i) = x(i+1), taken in the order of i; the
previous repeated value of the one at i is the one at the largest j < i with x(j) = x(j+1). The
condition is that no repeated value differs from its previous repeated value by plus or minus one
modulo 7 (pm below).
The function ok reads the array from the left and carries the latest repeated value p (none
before the first repetition): at each repetition x = y it checks the new repeated value x against
p (compat) and then carries x. The definition gives the listed terms
7, 49, 343, 2387, 16541, 114205, 786079, 5396363, 36961757, 252671461 for n = 1..10 (checked by direct enumeration for the first terms and through
the resulting linear recurrence for all of them).
-/

namespace OMA.S_oeis_a269688

/-- u and v differ by plus or minus one modulo 7. -/
def pm (u v : ℕ) : Prop := v % 7 = (u + 1) % 7 ∨ u % 7 = (v + 1) % 7
instance (u v : ℕ) : Decidable (pm u v) := by
  unfold pm
  exact instDecidableOr

/-- The new repeated value x is admissible after the previous repeated value p (if any): it does
not differ from p by plus or minus one modulo 7. -/
def compat : Option ℕ → ℕ → Bool
  | none, _ => true
  | some r, x => !decide (pm r x)

/-- ok p l: the list l satisfies the condition, p being the latest repeated value before it. -/
def ok : Option ℕ → List ℕ → Bool
  | p, x :: y :: t => if x = y then compat p x && ok (some x) (y :: t) else ok p (y :: t)
  | _, _ => true

/-- A269688: the number of arrays of length n with entries in 0..6 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 7)).filter
    (fun x => ok none (List.ofFn (fun i => ((x i : Fin 7) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f. 7x(1 - 5x - 4x^2)/((1 - 6x)(1 - 6x - 5x^2)), and
a(n) = (-7*2^(1+n)*3^n + (21 - 6 sqrt 14)(3 - sqrt 14)^n + 3(3 + sqrt 14)^n(7 + 2 sqrt 14))/30 for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - 6 * PowerSeries.X) * (1 - 6 * PowerSeries.X - 5 * PowerSeries.X ^ 2)) =
      7 * PowerSeries.X * (1 - 5 * PowerSeries.X - 4 * PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = (-7 * 2 ^ (1 + n) * 3 ^ n + (21 - 6 * Real.sqrt 14) * (3 - Real.sqrt 14) ^ n +
        3 * (3 + Real.sqrt 14) ^ n * (7 + 2 * Real.sqrt 14)) / 30 := by
  sorry

end OMA.S_oeis_a269688
