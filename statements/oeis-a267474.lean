import Mathlib

/-!
# OEIS A267474: Barker's conjectures for length-6 0..n arrays with no following element larger than the first repeated value

Source: https://oeis.org/A267474 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267474 (R. H. Hardin, Jan 15 2016), offset 1: Number of length-6 0..n arrays with no following elements larger than the first repeated value.
Formula section:
Empirical: a(n) = n^6 + (197/60)*n^5 + 7*n^4 + (43/4)*n^3 + 10*n^2 + (149/30)*n + 1.
Conjectures from Colin Barker, Feb 05 2018: (Start)
G.f.: x*(38 + 152*x + 362*x^2 + 137*x^3 + 37*x^4 - 7*x^5 + x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* An array of length 6 with entries in 0..n is a map x : Fin 6 -> Fin (n + 1).
* The repeated values are read as the values of adjacent equal pairs x(i) = x(i+1), and the first
  repeated value is that of the first such pair; the condition is that no entry after that pair
  is larger than it. This reading reproduces the table A267471 (of which the entry is row 6) for
  every length up to 6 and every n up to 4, checked by direct enumeration; arrays without an
  adjacent equal pair are counted.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n (a(0) = 1, the zero array, is left out).
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^7 = x N(x) with N the numerator in the entry, in the formal power
  series ring over the rationals; and the recurrence, for every n > 7, as an identity of integers.
* The definition reproduces the entry's data (38, 418, 2490, 10119, 31880, 83972, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a267474

open PowerSeries Finset

/-- After the first adjacent equal pair x(i) = x(i+1), no later entry x(j), j > i + 1, is larger than the repeated value x(i). -/
def good {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i i' j : Fin L, i'.val = i.val + 1 → x i = x i' →
    (∀ k k' : Fin L, k'.val = k.val + 1 → k.val < i.val → x k ≠ x k') →
    i'.val < j.val → x j ≤ x i

instance {L N : ℕ} : DecidablePred (@good L N) := fun x => by unfold good; infer_instance

/-- A267474: the number of length-6 0..n arrays with no following elements larger than the first
repeated value. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (38 + 152 * X + 362 * X ^ 2 + 137 * X ^ 3 + 37 * X ^ 4 - 7 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a267474
