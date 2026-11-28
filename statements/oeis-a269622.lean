import Mathlib

/-!
# OEIS A269622: Barker's conjectures for length-6 0..n arrays with no repeated value differing from the previous repeated value by other than plus two, zero or minus 1

Source: https://oeis.org/A269622 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A269622 (R. H. Hardin, Mar 01 2016), offset 1: Number of length-6 0..n arrays with no repeated value differing from the previous repeated value by other than plus two, zero or minus 1.
Formula section:
Empirical: a(n) = n^6 + 6*n^5 + 9*n^4 + 22*n^3 + 9*n^2 + 9*n - 7 for n>2.
Conjectures from Colin Barker, Jan 25 2019: (Start)
G.f.: x*(51 + 267*x + 314*x^2 + 167*x^3 - 86*x^4 + 17*x^5 - 14*x^6 + 5*x^7 - x^8) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>9.
(End)

Formalization notes:
* An array of length 6 with entries in 0..n is a map x : Fin 6 -> Fin (n + 1). Two values are
  compared through their values as natural numbers, with no wraparound modulo n + 1.
* The repeated values are the values x(i) of the adjacent equal pairs x(i) = x(i+1), listed in
  order (`reps`), and the condition relates each repeated value c to the previous one p in that
  list, as c - p = 2, 0 or -1; an array with at most one adjacent equal pair always counts.
  Reversing the orientation (p - c in place of c - p) gives the same counts, by the symmetry
  x -> n - x. This reading reproduces every listed term of the table A269619 (of which the entry
  is row 6) with length at most 7 and n at most 4, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^7 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 9, as an identity of integers.
* The definition reproduces the entry's data (51, 624, 3611, 14125, 43013, 110099, ... from n = 1,
  checked by direct enumeration for small n and against every listed term through the formula of
  the proof).
-/

namespace OMA.S_oeis_a269622

open PowerSeries Finset

/-- The repeated values of x: x(i) for every adjacent equal pair x(i) = x(i+1), in order. -/
def reps {m N : ℕ} (x : Fin (m + 1) → Fin N) : List (Fin N) :=
  (List.finRange m).filterMap (fun i => if x i.castSucc = x i.succ then some (x i.castSucc) else none)

/-- No repeated value differs from the previous repeated value by other than plus two, zero or minus one: each repeated value c after the first, with p the previous one, has c = p + 2, c = p or p = c + 1. -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Prop :=
  (reps x).IsChain (fun (p c : Fin (n + 1)) => (c : ℕ) = (p : ℕ) + 2 ∨ c = p ∨ (p : ℕ) = (c : ℕ) + 1)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A269622: number of length-6 0..n arrays with no repeated value differing from the previous repeated value by other than plus two, zero or minus 1. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (51 + 267 * X + 314 * X ^ 2 + 167 * X ^ 3 - 86 * X ^ 4 + 17 * X ^ 5 - 14 * X ^ 6 + 5 * X ^ 7 - X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a269622
