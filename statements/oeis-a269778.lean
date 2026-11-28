import Mathlib

/-!
# OEIS A269778: Barker's conjectures for length-6 0..n arrays with every repeated value unequal to the previous repeated value plus one mod n+1

Source: https://oeis.org/A269778 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A269778 (R. H. Hardin, Mar 04 2016), offset 1: Number of length-6 0..n arrays with every repeated value unequal to the previous repeated value plus one mod n+1.
Formula section:
Empirical: a(n) = n^6 + 6*n^5 + 15*n^4 + 14*n^3 + 4*n^2.
Conjectures from Colin Barker, Jan 29 2019: (Start)
G.f.: 8*x*(5 + 43*x + 36*x^2 + 4*x^3 + 2*x^4) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* An array of length 6 with entries in 0..n is a map x : Fin 6 -> Fin (n + 1), and arithmetic
  modulo n + 1 is the arithmetic of Fin (n + 1).
* The repeated values are the values x(i) of the adjacent equal pairs x(i) = x(i+1), listed in
  order (`reps`), and the condition relates each repeated value to the previous one in that list.
  This reading reproduces the table A269776 (of which the entry is row 6) for every length up to
  6 and every n up to 4, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^7 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 7, as an identity of integers.
* The definition reproduces the entry's data (40, 624, 3816, 15040, 45600, 115920, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a269778

open PowerSeries Finset

/-- The repeated values of x: x(i) for every adjacent equal pair x(i) = x(i+1), in order. -/
def reps {m N : ℕ} (x : Fin (m + 1) → Fin N) : List (Fin N) :=
  (List.finRange m).filterMap (fun i => if x i.castSucc = x i.succ then some (x i.castSucc) else none)

/-- Every repeated value is unequal to the previous repeated value plus one modulo n + 1: each repeated value c after the first, with p the previous one, has c != p + 1 in Fin (n + 1). -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Prop :=
  (reps x).IsChain (fun p c => c ≠ p + 1)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A269778: number of length-6 0..n arrays with every repeated value unequal to the previous repeated value plus one mod n+1. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      8 * X * (5 + 43 * X + 36 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a269778
