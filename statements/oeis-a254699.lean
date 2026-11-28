import Mathlib

/-!
# OEIS A254699: Barker's recurrence and generating function

Source: https://oeis.org/A254699 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Feb 05 2015), offset 1: Number of length 1+4 0..n arrays with every five
consecutive terms having the maximum of some two terms equal to the minimum of the remaining three
terms. Data: 22, 133, 464, 1205, 2606, 4977, 8688, 14169, 21910, 32461, ... The formula section
states: Empirical: a(n) = (5/2)*n^4 + (20/3)*n^3 + (15/2)*n^2 + (13/3)*n + 1. Conjectures from Colin
Barker, Dec 17 2018: (Start) G.f.: x*(22 + 23*x + 19*x^2 - 5*x^3 + x^4) / (1 - x)^5. a(n) =
5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5. (End)

Formalization notes:
* An array is a function x : Fin 5 → Fin (n + 1), the array x(0..4) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `splitAt w i j` says that i and j are two different positions of the window w and that max(w i, w
  j) is the minimum of the other terms of w (at most each of them and equal to one of them);
  `someSplit w` says that some such pair exists. The array x(0..4) is the only window of 5
  consecutive terms.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^5 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..32), all the entry's listed terms.
-/

namespace OMA.S_oeis_a254699

open PowerSeries

/-- In the window w, the maximum of the two terms w i and w j (i ≠ j) equals the minimum of
the remaining terms: it is at most each of them and equal to one of them. -/
def splitAt {L : ℕ} (w : Fin L → ℕ) (i j : Fin L) : Prop :=
  i ≠ j ∧ (∀ t, t ≠ i → t ≠ j → max (w i) (w j) ≤ w t) ∧
    ∃ t, t ≠ i ∧ t ≠ j ∧ w t = max (w i) (w j)

/-- Some two terms of the window w have maximum equal to the minimum of the remaining terms. -/
def someSplit {L : ℕ} (w : Fin L → ℕ) : Prop := ∃ i j, splitAt w i j

/-- Some two terms of x(0..4) have maximum equal to the minimum of the remaining three. -/
def good (x : Fin 5 → ℕ) : Prop :=
  someSplit x

instance : DecidablePred good := fun x => by unfold good someSplit splitAt; infer_instance

/-- A254699(n): the number of 0..n arrays x(0..4) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 5 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      X * (22 + 23 * X + 19 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  sorry

end OMA.S_oeis_a254699
