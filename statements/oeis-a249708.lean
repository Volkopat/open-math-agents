import Mathlib

/-!
# OEIS A249708: Barker's recurrence and generating function

Source: https://oeis.org/A249708 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 04 2014), offset 1: Number of length 2+3 0..n arrays with every four
consecutive terms having the maximum of some two terms equal to the minimum of the remaining two
terms. Data: 14, 69, 208, 485, 966, 1729, 2864, 4473, 6670, 9581, ... The formula section states:
Empirical: a(n) = (1/2)*n^4 + 4*n^3 + (11/2)*n^2 + 3*n + 1. Conjectures from Colin Barker, Nov 09
2018: (Start) G.f.: x*(2 - x)*(7 + 3*x + 3*x^2 - x^3) / (1 - x)^5. a(n) = 5*a(n-1) - 10*a(n-2) +
10*a(n-3) - 5*a(n-4) + a(n-5) for n>5. (End)

Formalization notes:
* An array is a function x : Fin 5 → Fin (n + 1), the array x(0..4) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `splitAt w i j` says that i and j are two different positions of the window w and that max(w i, w
  j) is the minimum of the other terms of w (at most each of them and equal to one of them);
  `someSplit w` says that some such pair exists. The windows of 4 consecutive terms of x(0..4) are
  `fun t : Fin 4 => x t.castSucc`, which is x(0..3), and `fun t : Fin 4 => x t.succ`, which is
  x(1..4).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^5 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..35), all the entry's listed terms.
-/

namespace OMA.S_oeis_a249708

open PowerSeries

/-- In the window w, the maximum of the two terms w i and w j (i ≠ j) equals the minimum of
the remaining terms: it is at most each of them and equal to one of them. -/
def splitAt {L : ℕ} (w : Fin L → ℕ) (i j : Fin L) : Prop :=
  i ≠ j ∧ (∀ t, t ≠ i → t ≠ j → max (w i) (w j) ≤ w t) ∧
    ∃ t, t ≠ i ∧ t ≠ j ∧ w t = max (w i) (w j)

/-- Some two terms of the window w have maximum equal to the minimum of the remaining terms. -/
def someSplit {L : ℕ} (w : Fin L → ℕ) : Prop := ∃ i j, splitAt w i j

/-- Each of the windows x(0..3) and x(1..4) has two terms whose maximum equals the minimum of the
remaining two. -/
def good (x : Fin 5 → ℕ) : Prop :=
  someSplit (fun t : Fin 4 => x t.castSucc) ∧ someSplit (fun t : Fin 4 => x t.succ)

instance : DecidablePred good := fun x => by unfold good someSplit splitAt; infer_instance

/-- A249708(n): the number of 0..n arrays x(0..4) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 5 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      X * (2 - X) * (7 + 3 * X + 3 * X ^ 2 - X ^ 3) := by
  sorry

end OMA.S_oeis_a249708
