import Mathlib

/-!
# OEIS A269681: Barker's conjectures for length-6 0..n arrays with no repeated value differing from the previous repeated value by other than plus or minus one modulo n+1

Source: https://oeis.org/A269681 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A269681 (R. H. Hardin, Mar 03 2016), offset 1: Number of length-6 0..n arrays with no repeated value differing from the previous repeated value by other than plus or minus one modulo n+1.
Formula section:
Empirical: a(n) = n^6 + 6*n^5 + 5*n^4 + 12*n^3 + 6*n^2 + 6 for n>1.
Conjectures from Colin Barker, Jan 26 2019: (Start)
G.f.: 2*x*(11 + 154*x + 102*x^2 + 245*x^3 - 239*x^4 + 126*x^5 - 46*x^6 + 7*x^7) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>8.
(End)

Formalization notes:
* An array of length 6 with entries in 0..n is a map x : Fin 6 -> Fin (n + 1), and arithmetic
  modulo n + 1 is the arithmetic of Fin (n + 1).
* The repeated values are the values x(i) of the adjacent equal pairs x(i) = x(i+1), listed in
  order (`reps`), and the condition relates each repeated value to the previous one in that list.
  This reading reproduces the table A269678 (of which the entry is row 6) for every length up to
  6 and every n up to 4, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^7 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 8, as an identity of integers.
* The definition reproduces the entry's data (22, 462, 2976, 12390, 39156, 102606, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a269681

open PowerSeries Finset

/-- The repeated values of x: x(i) for every adjacent equal pair x(i) = x(i+1), in order. -/
def reps {m N : ℕ} (x : Fin (m + 1) → Fin N) : List (Fin N) :=
  (List.finRange m).filterMap (fun i => if x i.castSucc = x i.succ then some (x i.castSucc) else none)

/-- No repeated value differs from the previous repeated value by other than plus or minus one modulo n + 1: each repeated value c after the first, with p the previous one, has c = p + 1 or p = c + 1 in Fin (n + 1). -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Prop :=
  (reps x).IsChain (fun p c => c = p + 1 ∨ p = c + 1)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A269681: number of length-6 0..n arrays with no repeated value differing from the previous repeated value by other than plus or minus one modulo n+1. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X * (11 + 154 * X + 102 * X ^ 2 + 245 * X ^ 3 - 239 * X ^ 4 + 126 * X ^ 5 - 46 * X ^ 6 + 7 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a269681
