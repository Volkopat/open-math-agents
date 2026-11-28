import Mathlib

/-!
# OEIS A269538: Barker's conjectures for length-4 0..n arrays with no repeated value differing from the previous repeated value by other than one

Source: https://oeis.org/A269538 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A269538 (R. H. Hardin, Feb 29 2016), offset 1: Number of length-4 0..n arrays with no repeated value differing from the previous repeated value by other than one.
Formula section:
Empirical: a(n) = n^4 + 4*n^3 + 3*n^2 + 2*n.
Conjectures from Colin Barker, Jan 24 2019: (Start)
G.f.: 2*x*(1 + x)*(5 + 2*x - x^2) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
(End)

Formalization notes:
* An array of length 4 with entries in 0..n is a map x : Fin 4 -> Fin (n + 1). Two values are
  compared through their values as natural numbers, with no wraparound modulo n + 1.
* The repeated values are the values x(i) of the adjacent equal pairs x(i) = x(i+1), listed in
  order (`reps`), and the condition relates each repeated value c to the previous one p in that
  list, as c - p = 1 or -1; an array with at most one adjacent equal pair always counts. Reversing
  the orientation (p - c in place of c - p) gives the same counts, by the symmetry x -> n - x.
  This reading reproduces every listed term of the table A269537 (of which the entry is row 4)
  with length at most 7 and n at most 4, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^5 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 5, as an identity of integers.
* The definition reproduces the entry's data (10, 64, 222, 568, 1210, 2280, ... from n = 1,
  checked by direct enumeration for small n and against every listed term through the formula of
  the proof).
-/

namespace OMA.S_oeis_a269538

open PowerSeries Finset

/-- The repeated values of x: x(i) for every adjacent equal pair x(i) = x(i+1), in order. -/
def reps {m N : ℕ} (x : Fin (m + 1) → Fin N) : List (Fin N) :=
  (List.finRange m).filterMap (fun i => if x i.castSucc = x i.succ then some (x i.castSucc) else none)

/-- No repeated value differs from the previous repeated value by other than one: each repeated value c after the first, with p the previous one, has c = p + 1 or p = c + 1. -/
def good {n : ℕ} (x : Fin 4 → Fin (n + 1)) : Prop :=
  (reps x).IsChain (fun (p c : Fin (n + 1)) => (c : ℕ) = (p : ℕ) + 1 ∨ (p : ℕ) = (c : ℕ) + 1)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A269538: number of length-4 0..n arrays with no repeated value differing from the previous repeated value by other than one. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 4 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      2 * X * (1 + X) * (5 + 2 * X - X ^ 2) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a269538
