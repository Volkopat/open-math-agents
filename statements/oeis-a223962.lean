import Mathlib

/-!
# OEIS A223962: Barker's conjectures for 2 X n 0..3 arrays with antidiagonals unimodal and rows and diagonals nondecreasing

Source: https://oeis.org/A223962 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A223962 (R. H. Hardin, Mar 29 2013), offset 1: Number of 2 X n 0..3 arrays with antidiagonals
unimodal and rows and diagonals nondecreasing.
Formula section:
Empirical: a(n) = (1/144)*n^6 + (7/48)*n^5 + (157/144)*n^4 + (59/16)*n^3 + (425/72)*n^2 + (25/6)*n + 1.
Conjectures from Colin Barker, Aug 24 2018: (Start)
G.f.: x*(16 - 27*x + 36*x^2 - 35*x^3 + 21*x^4 - 7*x^5 + x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* A 2 X n array with entries in 0..3 is a map x : Fin 2 -> Fin n -> Fin 4, x i j the entry in row i
  and column j; entries are compared as natural numbers.
* Rows nondecreasing: x i j <= x i (j + 1). Diagonals nondecreasing: x i j <= x (i + 1) (j + 1).
* A line of the array (an antidiagonal, the positions with i + j constant, read in order of the row
  index) is unimodal when it weakly increases and then weakly decreases. Equivalently it has no
  valley: no three positions p, q, r on it, in this order, with the value at q smaller than both the
  value at p and the value at r. The statement uses the valley form. Reversing the order of a line
  does not change unimodality. The antidiagonals of a 2 X n array have at most two entries, so this
  condition always holds; it is stated anyway, as in the entry.
* This reading reproduces the entry's data (16, 85, 295, 805, 1876, 3906, 7470, ... from n = 1),
  checked by direct enumeration for n <= 5 and through a transfer matrix for every listed term.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the identity
  A(x) (1 - x)^7 = x (16 - 27*x + 36*x^2 - 35*x^3 + 21*x^4 - 7*x^5 + x^6) in the formal power series
  ring over the rationals with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0); and
  the recurrence, for every n > 7, as an identity of integers.
-/

namespace OMA.S_oeis_a223962

open PowerSeries Finset

/-- Every antidiagonal (i + j constant) is unimodal: it has no valley, that is no three of its
positions, in order of the row index, whose middle value is smaller than both outer values. -/
def AntidiagsUnimodal {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i₁ i₂ i₃ : Fin R) (j₁ j₂ j₃ : Fin C), i₁ < i₂ → i₂ < i₃ →
    i₁.val + j₁.val = i₂.val + j₂.val → i₂.val + j₂.val = i₃.val + j₃.val →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

instance {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Decidable (AntidiagsUnimodal x) := by
  unfold AntidiagsUnimodal; infer_instance

/-- Every row is nondecreasing from left to right. -/
def RowsNondecreasing {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i : Fin R) (j j' : Fin C), j'.val = j.val + 1 → x i j ≤ x i j'

instance {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Decidable (RowsNondecreasing x) := by
  unfold RowsNondecreasing; infer_instance

/-- Every diagonal (i - j constant) is nondecreasing from top left to bottom right. -/
def DiagsNondecreasing {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i i' : Fin R) (j j' : Fin C), i'.val = i.val + 1 → j'.val = j.val + 1 → x i j ≤ x i' j'

instance {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Decidable (DiagsNondecreasing x) := by
  unfold DiagsNondecreasing; infer_instance

/-- The condition of the entry. -/
def good {n : ℕ} (x : Fin 2 → Fin n → Fin 4) : Prop :=
  AntidiagsUnimodal x ∧ RowsNondecreasing x ∧ DiagsNondecreasing x

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good; infer_instance

/-- A223962: Number of 2 X n 0..3 arrays with antidiagonals unimodal and rows and diagonals nondecreasing. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 2 → Fin n → Fin 4)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (16 - 27 * X + 36 * X ^ 2 - 35 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a223962
