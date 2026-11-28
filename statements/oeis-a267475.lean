import Mathlib

/-!
# OEIS A267475: Barker's conjectures for length-7 0..n arrays with no following element larger than the first repeated value

Source: https://oeis.org/A267475 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267475 (R. H. Hardin, Jan 15 2016), offset 1: Number of length-7 0..n arrays with no following elements larger than the first repeated value.
Formula section:
Empirical: a(n) = n^7 + (69/20)*n^6 + (17/2)*n^5 + (97/6)*n^4 + 20*n^3 + (893/60)*n^2 + 6*n + 1.
Conjectures from Colin Barker, Feb 05 2018: (Start)
G.f.: x*(71 + 544*x + 1862*x^2 + 1901*x^3 + 651*x^4 + 4*x^5 + 8*x^6 - x^7) / (1 - x)^8.
a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.
(End)

Formalization notes:
* An array of length 7 with entries in 0..n is a map x : Fin 7 -> Fin (n + 1).
* The repeated values are read as the values of adjacent equal pairs x(i) = x(i+1), and the first
  repeated value is that of the first such pair; the condition is that no entry after that pair
  is larger than it. This reading reproduces the table A267471 (of which the entry is row 7) for
  every length up to 6 and every n up to 4, checked by direct enumeration; arrays without an
  adjacent equal pair are counted.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n (a(0) = 1, the zero array, is left out).
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^8 = x N(x) with N the numerator in the entry, in the formal power
  series ring over the rationals; and the recurrence, for every n > 8, as an identity of integers.
* The definition reproduces the entry's data (71, 1112, 8770, 44901, 171601, 532840, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a267475

open PowerSeries Finset

/-- After the first adjacent equal pair x(i) = x(i+1), no later entry x(j), j > i + 1, is larger than the repeated value x(i). -/
def good {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i i' j : Fin L, i'.val = i.val + 1 → x i = x i' →
    (∀ k k' : Fin L, k'.val = k.val + 1 → k.val < i.val → x k ≠ x k') →
    i'.val < j.val → x j ≤ x i

instance {L N : ℕ} : DecidablePred (@good L N) := fun x => by unfold good; infer_instance

/-- A267475: the number of length-7 0..n arrays with no following elements larger than the first
repeated value. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 7 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (71 + 544 * X + 1862 * X ^ 2 + 1901 * X ^ 3 + 651 * X ^ 4 + 4 * X ^ 5 + 8 * X ^ 6 - X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a267475
