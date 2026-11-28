import Mathlib

/-!
# A269685: Number of length-n 0..3 arrays with no repeated value differing from the previous repeated value by plus or minus one modulo 3+1.

Source: https://oeis.org/A269685
Credit: @agchua

Colin Barker (Jan 27 2019), in the formula section of A269685:
  Conjectures from Colin Barker, Jan 27 2019: (Start)
  G.f.: 4*x*(1 - 2*x - x^2) / ((1 - 3*x)*(1 - 3*x - 2*x^2)).
  a(n) = 2^(-n)*(-17*2^(2+n)*3^n + (51-15*sqrt(17))*(3-sqrt(17))^n + 3*(3+sqrt(17))^n*(17+5*sqrt(17))) / 51.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for all n ≥ 1 in ℝ.
Definition (R. H. Hardin's convention for these arrays, as in A269680): an array is
x(0), ..., x(n-1) with entries in 0..3 (a function Fin n → Fin 4, read as the list of its
values). A repeated value is an entry x(i) with x(i) = x(i+1), taken in the order of i; the
previous repeated value of the one at i is the one at the largest j < i with x(j) = x(j+1). The
condition is that no repeated value differs from its previous repeated value by plus or minus one
modulo 4 (pm below).
The function ok reads the array from the left and carries the latest repeated value p (none
before the first repetition): at each repetition x = y it checks the new repeated value x against
p (compat) and then carries x. The definition gives the listed terms
4, 16, 64, 248, 944, 3544, 13168, 48536, 177776, 647896 for n = 1..10 (checked by direct enumeration for the first terms and through
the resulting linear recurrence for all of them).
-/

namespace OMA.S_oeis_a269685

/-- u and v differ by plus or minus one modulo 4. -/
def pm (u v : ℕ) : Prop := v % 4 = (u + 1) % 4 ∨ u % 4 = (v + 1) % 4
instance (u v : ℕ) : Decidable (pm u v) := by
  unfold pm
  exact instDecidableOr

/-- The new repeated value x is admissible after the previous repeated value p (if any): it does
not differ from p by plus or minus one modulo 4. -/
def compat : Option ℕ → ℕ → Bool
  | none, _ => true
  | some r, x => !decide (pm r x)

/-- ok p l: the list l satisfies the condition, p being the latest repeated value before it. -/
def ok : Option ℕ → List ℕ → Bool
  | p, x :: y :: t => if x = y then compat p x && ok (some x) (y :: t) else ok p (y :: t)
  | _, _ => true

/-- A269685: the number of arrays of length n with entries in 0..3 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 4)).filter
    (fun x => ok none (List.ofFn (fun i => ((x i : Fin 4) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f. 4x(1 - 2x - x^2)/((1 - 3x)(1 - 3x - 2x^2)), and
a(n) = 2^(-n)(-17*2^(2+n)*3^n + (51 - 15 sqrt 17)(3 - sqrt 17)^n + 3(3 + sqrt 17)^n(17 + 5 sqrt 17))/51 (the power 2^(-n) taken in ℝ as an integer power) for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - 3 * PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2)) =
      4 * PowerSeries.X * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = (2 : ℝ) ^ (-(n : ℤ)) * (-17 * 2 ^ (2 + n) * 3 ^ n +
        (51 - 15 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ n + 3 * (3 + Real.sqrt 17) ^ n * (17 + 5 * Real.sqrt 17)) / 51 := by
  sorry

end OMA.S_oeis_a269685
