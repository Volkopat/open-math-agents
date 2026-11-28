import Mathlib

/-!
# OEIS A269693: Barker's conjectures for length-7 0..n arrays with no repeated value differing from the previous repeated value by plus or minus one modulo n+1

Source: https://oeis.org/A269693 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A269693 (R. H. Hardin, Mar 03 2016), offset 1: Number of length-7 0..n arrays with no repeated value differing from the previous repeated value by plus or minus one modulo n+1.
Formula section:
Empirical: a(n) = n^7 + 7*n^6 + 21*n^5 + 15*n^4 - 13*n^3 - 11*n^2 + 3*n + 1 for n>1.
Conjectures from Colin Barker, Jan 28 2019: (Start)
G.f.: x*(66 + 819*x + 4240*x^2 - 1919*x^3 + 3268*x^4 - 2323*x^5 + 1184*x^6 - 337*x^7 + 42*x^8) / (1 - x)^8.
a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>9.
(End)

Formalization notes:
* An array of length 7 with entries in 0..n is a map x : Fin 7 -> Fin (n + 1), and arithmetic
  modulo n + 1 is the arithmetic of Fin (n + 1).
* The repeated values are the values x(i) of the adjacent equal pairs x(i) = x(i+1), listed in
  order (`reps`), and the condition relates each repeated value to the previous one in that list.
  This reading reproduces the table A269690 (of which the entry is row 7) for every length up to
  6 and every n up to 4, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^8 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 9, as an identity of integers.
* The definition reproduces the entry's data (66, 1347, 13168, 69405, 260616, 786079, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a269693

open PowerSeries Finset

/-- The repeated values of x: x(i) for every adjacent equal pair x(i) = x(i+1), in order. -/
def reps {m N : ℕ} (x : Fin (m + 1) → Fin N) : List (Fin N) :=
  (List.finRange m).filterMap (fun i => if x i.castSucc = x i.succ then some (x i.castSucc) else none)

/-- No repeated value differs from the previous repeated value by plus or minus one modulo n + 1: for each repeated value c after the first, with p the previous one, neither c = p + 1 nor p = c + 1 holds in Fin (n + 1). -/
def good {n : ℕ} (x : Fin 7 → Fin (n + 1)) : Prop :=
  (reps x).IsChain (fun p c => ¬ (c = p + 1 ∨ p = c + 1))

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A269693: number of length-7 0..n arrays with no repeated value differing from the previous repeated value by plus or minus one modulo n+1. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 7 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (66 + 819 * X + 4240 * X ^ 2 - 1919 * X ^ 3 + 3268 * X ^ 4 - 2323 * X ^ 5 + 1184 * X ^ 6 - 337 * X ^ 7 + 42 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a269693
