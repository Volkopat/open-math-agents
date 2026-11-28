import Mathlib

/-!
# OEIS A249845: Barker's recurrence and generating function

Source: https://oeis.org/A249845 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 07 2014), offset 1: Number of length 1+4 0..n arrays with no five
consecutive terms having the maximum of any two terms equal to the minimum of the remaining three
terms. Data: 10, 110, 560, 1920, 5170, 11830, 24080, 44880, 78090, 128590, ... The formula section
states: Empirical: a(n) = n^5 + (5/2)*n^4 + (10/3)*n^3 + (5/2)*n^2 + (2/3)*n. Conjectures from Colin
Barker, Aug 18 2017: (Start) G.f.: 10*x*(1 + x)*(1 + 4*x + x^2) / (1 - x)^6. a(n) = 6*a(n-1) -
15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* An array is a function x : Fin 5 → Fin (n + 1), the array x(0..4) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `splitAt w i j` says that i and j are two different positions of the window w and that max(w i, w
  j) is the minimum of the other terms of w (at most each of them and equal to one of them);
  `someSplit w` says that some such pair exists. The array x(0..4) is the only window of 5
  consecutive terms.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^6 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..29), all the entry's listed terms.
-/

namespace OMA.S_oeis_a249845

open PowerSeries

/-- In the window w, the maximum of the two terms w i and w j (i ≠ j) equals the minimum of
the remaining terms: it is at most each of them and equal to one of them. -/
def splitAt {L : ℕ} (w : Fin L → ℕ) (i j : Fin L) : Prop :=
  i ≠ j ∧ (∀ t, t ≠ i → t ≠ j → max (w i) (w j) ≤ w t) ∧
    ∃ t, t ≠ i ∧ t ≠ j ∧ w t = max (w i) (w j)

/-- Some two terms of the window w have maximum equal to the minimum of the remaining terms. -/
def someSplit {L : ℕ} (w : Fin L → ℕ) : Prop := ∃ i j, splitAt w i j

/-- No two terms of x(0..4) have maximum equal to the minimum of the remaining three. -/
def good (x : Fin 5 → ℕ) : Prop :=
  ¬ someSplit x

instance : DecidablePred good := fun x => by unfold good someSplit splitAt; infer_instance

/-- A249845(n): the number of 0..n arrays x(0..4) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 5 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      10 * X * (1 + X) * (1 + 4 * X + X ^ 2) := by
  sorry

end OMA.S_oeis_a249845
