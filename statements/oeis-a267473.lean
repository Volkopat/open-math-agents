import Mathlib

/-!
# OEIS A267473: Barker's conjectures for length-5 0..n arrays with no following element larger than the first repeated value

Source: https://oeis.org/A267473 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267473 (R. H. Hardin, Jan 15 2016), offset 1: Number of length-5 0..n arrays with no following elements larger than the first repeated value.
Formula section:
Empirical: a(n) = n^5 + (37/12)*n^4 + (11/2)*n^3 + (77/12)*n^2 + 4*n + 1.
Conjectures from Colin Barker, Feb 05 2018: (Start)
G.f.: x*(21 + 34*x + 67*x^2 - 7*x^3 + 6*x^4 - x^5) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.
(End)

Formalization notes:
* An array of length 5 with entries in 0..n is a map x : Fin 5 -> Fin (n + 1).
* The repeated values are read as the values of adjacent equal pairs x(i) = x(i+1), and the first
  repeated value is that of the first such pair; the condition is that no entry after that pair
  is larger than it. This reading reproduces the table A267471 (of which the entry is row 5) for
  every length up to 6 and every n up to 4, checked by direct enumeration; arrays without an
  adjacent equal pair are counted.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n (a(0) = 1, the zero array, is left out).
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^6 = x N(x) with N the numerator in the entry, in the formal power
  series ring over the rationals; and the recurrence, for every n > 6, as an identity of integers.
* The definition reproduces the entry's data (21, 160, 712, 2285, 5921, 13216, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a267473

open PowerSeries Finset

/-- After the first adjacent equal pair x(i) = x(i+1), no later entry x(j), j > i + 1, is larger than the repeated value x(i). -/
def good {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i i' j : Fin L, i'.val = i.val + 1 → x i = x i' →
    (∀ k k' : Fin L, k'.val = k.val + 1 → k.val < i.val → x k ≠ x k') →
    i'.val < j.val → x j ≤ x i

instance {L N : ℕ} : DecidablePred (@good L N) := fun x => by unfold good; infer_instance

/-- A267473: the number of length-5 0..n arrays with no following elements larger than the first
repeated value. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 5 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (21 + 34 * X + 67 * X ^ 2 - 7 * X ^ 3 + 6 * X ^ 4 - X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a267473
