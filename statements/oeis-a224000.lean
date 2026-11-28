import Mathlib

/-!
# OEIS A224000: Barker's conjectures for 2 X n 0..2 arrays with antidiagonals unimodal and rows and diagonals nondecreasing

Source: https://oeis.org/A224000 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224000 (R. H. Hardin, Mar 30 2013), offset 1: Number of 2 X n 0..2 arrays with antidiagonals
unimodal and rows and diagonals nondecreasing.
Formula section:
Empirical: a(n) = (1/12)*n^4 + 1*n^3 + (41/12)*n^2 + (7/2)*n + 1.
Conjectures from Colin Barker, Aug 25 2018: (Start)
G.f.: x*(9 - 14*x + 11*x^2 - 5*x^3 + x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
(End)

Formalization notes:
* A 2 X n array with entries in 0..2 is a map x : Fin 2 -> Fin n -> Fin 3, x i j the entry in row i
  and column j; entries are compared as natural numbers.
* Rows nondecreasing: x i j <= x i (j + 1). Diagonals nondecreasing: x i j <= x (i + 1) (j + 1).
* A line of the array (here an antidiagonal, the positions with i + j constant, read in order of
  the row index) is unimodal when it weakly increases and then weakly decreases. Equivalently it
  has no valley: no three positions p, q, r on it, in this order, with the value at q smaller than
  both the value at p and the value at r. The statement uses the valley form. Reversing the order
  of a line does not change unimodality. The antidiagonals of a 2 X n array have at most two
  entries, so this condition always holds; it is stated anyway, as in the entry.
* This reading reproduces the entry's data (9, 31, 76, 155, 281, 469, 736, ... from n = 1), checked
  by direct enumeration for n <= 6 and through a transfer matrix for every listed term.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^5 = x (9 - 14x + 11x^2 - 5x^3 + x^4) in the formal power series ring over
  the rationals with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0); and the
  recurrence, for every n > 5, as an identity of integers.
-/

namespace OMA.S_oeis_a224000

open PowerSeries Finset

/-- Every row is nondecreasing from left to right. -/
def RowsNondecreasing {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i : Fin R) (j j' : Fin C), j'.val = j.val + 1 → x i j ≤ x i j'

/-- Every diagonal (i - j constant) is nondecreasing from top left to bottom right. -/
def DiagsNondecreasing {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i i' : Fin R) (j j' : Fin C), i'.val = i.val + 1 → j'.val = j.val + 1 → x i j ≤ x i' j'

/-- Every antidiagonal (i + j constant) is unimodal: it has no valley, that is no three of its
positions, in order of the row index, whose middle value is smaller than both outer values. -/
def AntidiagsUnimodal {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i₁ i₂ i₃ : Fin R) (j₁ j₂ j₃ : Fin C), i₁ < i₂ → i₂ < i₃ →
    i₁.val + j₁.val = i₂.val + j₂.val → i₂.val + j₂.val = i₃.val + j₃.val →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- The condition of the entry. -/
def good {n : ℕ} (x : Fin 2 → Fin n → Fin 3) : Prop :=
  AntidiagsUnimodal x ∧ RowsNondecreasing x ∧ DiagsNondecreasing x

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good AntidiagsUnimodal RowsNondecreasing DiagsNondecreasing; infer_instance

/-- A224000: the number of 2 X n 0..2 arrays with antidiagonals unimodal and rows and diagonals
nondecreasing. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 2 → Fin n → Fin 3)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (9 - 14 * X + 11 * X ^ 2 - 5 * X ^ 3 + X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a224000
