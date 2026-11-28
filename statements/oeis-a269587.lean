import Mathlib

/-!
# OEIS A269587: Barker's conjectures for length-7 0..n arrays with no repeated value differing from the previous repeated value by more than one

Source: https://oeis.org/A269587 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A269587 (R. H. Hardin, Mar 01 2016), offset 1: Number of length-7 0..n arrays with no repeated value differing from the previous repeated value by more than one.
Formula section:
Empirical: a(n) = n^7 + 7*n^6 + 11*n^5 + 35*n^4 + 28*n^3 + 42*n^2 + 5*n - 1.
Conjectures from Colin Barker, Jan 24 2019: (Start)
G.f.: x*(128 + 865*x + 2418*x^2 + 1919*x^3 - 116*x^4 - 129*x^5 - 46*x^6 + x^7) / (1 - x)^8.
a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.
(End)

Formalization notes:
* An array of length 7 with entries in 0..n is a map x : Fin 7 -> Fin (n + 1). Two values are
  compared through their values as natural numbers, with no wraparound modulo n + 1.
* The repeated values are the values x(i) of the adjacent equal pairs x(i) = x(i+1), listed in
  order (`reps`), and the condition relates each repeated value c to the previous one p in that
  list, as |c - p| <= 1; an array with at most one adjacent equal pair always counts. Reversing
  the orientation (p - c in place of c - p) gives the same counts, by the symmetry x -> n - x.
  This reading reproduces every listed term of the table A269583 (of which the entry is row 7)
  with length at most 7 and n at most 4, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^8 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 8, as an identity of integers.
* The definition reproduces the entry's data (128, 1889, 13946, 67763, 248324, 745013, ... from
  n = 1, checked by direct enumeration for small n and against every listed term through the
  formula of the proof).
-/

namespace OMA.S_oeis_a269587

open PowerSeries Finset

/-- The repeated values of x: x(i) for every adjacent equal pair x(i) = x(i+1), in order. -/
def reps {m N : ℕ} (x : Fin (m + 1) → Fin N) : List (Fin N) :=
  (List.finRange m).filterMap (fun i => if x i.castSucc = x i.succ then some (x i.castSucc) else none)

/-- No repeated value differs from the previous repeated value by more than one: each repeated value c after the first, with p the previous one, has c <= p + 1 and p <= c + 1. -/
def good {n : ℕ} (x : Fin 7 → Fin (n + 1)) : Prop :=
  (reps x).IsChain (fun (p c : Fin (n + 1)) => (c : ℕ) ≤ (p : ℕ) + 1 ∧ (p : ℕ) ≤ (c : ℕ) + 1)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A269587: number of length-7 0..n arrays with no repeated value differing from the previous repeated value by more than one. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 7 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (128 + 865 * X + 2418 * X ^ 2 + 1919 * X ^ 3 - 116 * X ^ 4 - 129 * X ^ 5 - 46 * X ^ 6 + X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a269587
