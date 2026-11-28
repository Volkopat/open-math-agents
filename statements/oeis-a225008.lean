import Mathlib

/-!
# OEIS A225008: Barker's conjectures for n X 6 0..1 arrays with rows unimodal and columns nondecreasing

Source: https://oeis.org/A225008 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A225008 (R. H. Hardin, Apr 23 2013), offset 1: Number of n X 6 0..1 arrays with rows unimodal
and columns nondecreasing.
Formula section:
Empirical: a(n) = (2/45)*n^6 + (8/15)*n^5 + (91/36)*n^4 + 6*n^3 + (1337/180)*n^2 + (67/15)*n + 1.
Conjectures from Colin Barker, Sep 05 2018: (Start)
G.f.: x*(22 - 6*x + 36*x^2 - 35*x^3 + 21*x^4 - 7*x^5 + x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* A n X 6 array with entries in 0..1 is a map x : Fin n -> Fin 6 -> Fin 2, x i j the entry in row i
  and column j; entries are compared as natural numbers.
* Columns nondecreasing: x i j <= x (i + 1) j.
* A line of the array (a row, read from left to right) is unimodal when it weakly increases and then
  weakly decreases. Equivalently it has no valley: no three positions p, q, r on it, in this order,
  with the value at q smaller than both the value at p and the value at r. The statement uses the
  valley form. Reversing the order of a line does not change unimodality.
* This reading reproduces the entry's data (22, 148, 610, 1897, 4900, 11088, 22716, ... from n = 1),
  checked by direct enumeration for n <= 3 and through a transfer matrix for every listed term.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the identity
  A(x) (1 - x)^7 = x (22 - 6*x + 36*x^2 - 35*x^3 + 21*x^4 - 7*x^5 + x^6) in the formal power series
  ring over the rationals with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0); and
  the recurrence, for every n > 7, as an identity of integers.
-/

namespace OMA.S_oeis_a225008

open PowerSeries Finset

/-- Every row is unimodal: it has no valley, that is no three of its positions, from left to
right, whose middle value is smaller than both outer values. -/
def RowsUnimodal {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i : Fin R) (j₁ j₂ j₃ : Fin C), j₁ < j₂ → j₂ < j₃ → ¬ (x i j₂ < x i j₁ ∧ x i j₂ < x i j₃)

instance {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every column is nondecreasing from top to bottom. -/
def ColsNondecreasing {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i i' : Fin R) (j : Fin C), i'.val = i.val + 1 → x i j ≤ x i' j

instance {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Decidable (ColsNondecreasing x) := by
  unfold ColsNondecreasing; infer_instance

/-- The condition of the entry. -/
def good {n : ℕ} (x : Fin n → Fin 6 → Fin 2) : Prop :=
  RowsUnimodal x ∧ ColsNondecreasing x

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good; infer_instance

/-- A225008: Number of n X 6 0..1 arrays with rows unimodal and columns nondecreasing. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 6 → Fin 2)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (22 - 6 * X + 36 * X ^ 2 - 35 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a225008
