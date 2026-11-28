import Mathlib

/-!
# OEIS A229775: Barker's recurrence and generating function

Source: https://oeis.org/A229775 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Sep 29 2013), offset 1: Number of 3 X 3 0..n arrays with rows in
lexicographically nondecreasing order and columns in nonincreasing order. Data: 20, 322, 3232,
21331, 103222, 397460, 1287672, 3647349, 9281272, 21642038, ... The formula section states:
Empirical: a(n) = (1/120)*n^9 + (1/12)*n^8 + (133/360)*n^7 + (371/360)*n^6 + (19/9)*n^5 +
(247/72)*n^4 + (403/90)*n^3 + (401/90)*n^2 + (91/30)*n + 1. Conjectures from Colin Barker, Sep 21
2018: (Start) G.f.: x*(20 + 122*x + 912*x^2 + 1101*x^3 + 912*x^4 - 125*x^5 + 118*x^6 - 45*x^7 +
10*x^8 - x^9) / (1 - x)^10. a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) -
210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>10. (End)

Formalization notes:
* An array is a function x : Fin 9 → Fin (n + 1), the array x(0..8) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* The 3 X 3 array is x(0..8) read row by row: rows (x 0, x 1, x 2), (x 3, x 4, x 5), (x 6, x 7, x 8)
  and columns (x 0, x 3, x 6), (x 1, x 4, x 7), (x 2, x 5, x 8). `lexLE a0 a1 a2 b0 b1 b2` is (a0,
  a1, a2) ≤ (b0, b1, b2) in lexicographic order. `good x` requires the rows in lexicographically
  nondecreasing order from top to bottom and the columns in lexicographically nonincreasing order
  from left to right; this reading reproduces the entry's data by brute force.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^10 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..23), all the entry's listed terms.
-/

namespace OMA.S_oeis_a229775

open PowerSeries

/-- (a0, a1, a2) ≤ (b0, b1, b2) in lexicographic order. -/
def lexLE (a0 a1 a2 b0 b1 b2 : ℕ) : Prop :=
  a0 < b0 ∨ (a0 = b0 ∧ (a1 < b1 ∨ (a1 = b1 ∧ a2 ≤ b2)))

/-- The 3 X 3 array is x(0..8) read row by row: rows (x 0, x 1, x 2), (x 3, x 4, x 5),
(x 6, x 7, x 8), columns (x 0, x 3, x 6), (x 1, x 4, x 7), (x 2, x 5, x 8). Its rows are in
lexicographically nondecreasing order and its columns in lexicographically nonincreasing order
(top to bottom, left to right). -/
def good (x : Fin 9 → ℕ) : Prop :=
  lexLE (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) ∧ lexLE (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) ∧
    lexLE (x 1) (x 4) (x 7) (x 0) (x 3) (x 6) ∧ lexLE (x 2) (x 5) (x 8) (x 1) (x 4) (x 7)

instance : DecidablePred good := fun x => by unfold good lexLE; infer_instance

/-- A229775(n): the number of 0..n arrays x(0..8) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 9 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 10 < n →
      (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
      X * (20 + 122 * X + 912 * X ^ 2 + 1101 * X ^ 3 + 912 * X ^ 4 - 125 * X ^ 5 + 118 * X ^ 6 - 45 * X ^ 7 + 10 * X ^ 8 - X ^ 9) := by
  sorry

end OMA.S_oeis_a229775
