import Mathlib

/-!
# OEIS A268947: Barker's conjectures for length-6 0..n arrays with no repeated value unequal to the previous repeated value plus one mod n+1

Source: https://oeis.org/A268947 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A268947 (R. H. Hardin, Feb 16 2016), offset 1: Number of length-6 0..n arrays with no repeated value unequal to the previous repeated value plus one mod n+1.
Formula section:
Empirical: a(n) = n^6 + 6*n^5 + 5*n^4 + 6*n^3 + 3*n^2 - n + 2.
Conjectures from Colin Barker, Jan 17 2019: (Start)
G.f.: 2*x*(11 + 121*x + 235*x^2 + 18*x^3 - 19*x^4 - 7*x^5 + x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* An array of length 6 with entries in 0..n is a map x : Fin 6 -> Fin (n + 1), and arithmetic
  modulo n + 1 is the arithmetic of Fin (n + 1).
* The repeated values are the values x(i) of the adjacent equal pairs x(i) = x(i+1), listed in
  order (`reps`), and the condition relates each repeated value to the previous one in that list.
  This reading reproduces the table A268944 (of which the entry is row 6) for every length up to
  6 and every n up to 4, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^7 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 7, as an identity of integers.
* The definition reproduces the entry's data (22, 396, 2780, 11950, 38322, 101192, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a268947

open PowerSeries Finset

/-- The repeated values of x: x(i) for every adjacent equal pair x(i) = x(i+1), in order. -/
def reps {m N : ℕ} (x : Fin (m + 1) → Fin N) : List (Fin N) :=
  (List.finRange m).filterMap (fun i => if x i.castSucc = x i.succ then some (x i.castSucc) else none)

/-- No repeated value is unequal to the previous repeated value plus one modulo n + 1: each repeated value c after the first, with p the previous one, has c = p + 1 in Fin (n + 1). -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Prop :=
  (reps x).IsChain (fun p c => c = p + 1)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A268947: number of length-6 0..n arrays with no repeated value unequal to the previous repeated value plus one mod n+1. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X * (11 + 121 * X + 235 * X ^ 2 + 18 * X ^ 3 - 19 * X ^ 4 - 7 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a268947
