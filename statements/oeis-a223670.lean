import Mathlib

/-!
# OEIS A223670: Barker's conjectures for 3 X n 0..1 arrays with rows, diagonals and antidiagonals unimodal

Source: https://oeis.org/A223670 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A223670 (R. H. Hardin, Mar 25 2013), offset 1: Number of 3 X n 0..1 arrays with rows,
diagonals and antidiagonals unimodal.
Formula section:
Empirical: a(n) = (23/360)*n^6 - (3/40)*n^5 + (37/18)*n^4 + (119/24)*n^3 - (3103/360)*n^2 + (997/60)*n - 9 for n>1.
Conjectures from Colin Barker, Mar 16 2018: (Start)
G.f.: x*(8 + 8*x + 12*x^2 - 32*x^3 + 63*x^4 - 16*x^5 + 5*x^6 - 2*x^7) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>8.
(End)

Formalization notes:
* A 3 X n array with entries in 0..1 is a map x : Fin 3 -> Fin n -> Fin 2, x i j the entry in row i
  and column j; entries are compared as natural numbers.
* A line of the array (a row, read from left to right or a diagonal, the positions with i - j
  constant, read in order of the row index or an antidiagonal, the positions with i + j constant, read
  in order of the row index) is unimodal when it weakly increases and then weakly decreases.
  Equivalently it has no valley: no three positions p, q, r on it, in this order, with the value at q
  smaller than both the value at p and the value at r. The statement uses the valley form. Reversing
  the order of a line does not change unimodality.
* This reading reproduces the entry's data (8, 64, 292, 948, 2527, 5913, 12577, ... from n = 1),
  checked by direct enumeration for n <= 7 and through a transfer matrix for every listed term.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the identity
  A(x) (1 - x)^7 = x (8 + 8*x + 12*x^2 - 32*x^3 + 63*x^4 - 16*x^5 + 5*x^6 - 2*x^7) in the formal power
  series ring over the rationals with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is
  0); and the recurrence, for every n > 8, as an identity of integers.
-/

namespace OMA.S_oeis_a223670

open PowerSeries Finset

/-- Every row is unimodal: it has no valley, that is no three of its positions, from left to
right, whose middle value is smaller than both outer values. -/
def RowsUnimodal {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i : Fin R) (j₁ j₂ j₃ : Fin C), j₁ < j₂ → j₂ < j₃ → ¬ (x i j₂ < x i j₁ ∧ x i j₂ < x i j₃)

instance {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every diagonal (i - j constant) is unimodal: it has no valley, that is no three of its
positions, in order of the row index, whose middle value is smaller than both outer values. -/
def DiagsUnimodal {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i₁ i₂ i₃ : Fin R) (j₁ j₂ j₃ : Fin C), i₁ < i₂ → i₂ < i₃ →
    i₁.val + j₂.val = i₂.val + j₁.val → i₂.val + j₃.val = i₃.val + j₂.val →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

instance {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Decidable (DiagsUnimodal x) := by
  unfold DiagsUnimodal; infer_instance

/-- Every antidiagonal (i + j constant) is unimodal: it has no valley, that is no three of its
positions, in order of the row index, whose middle value is smaller than both outer values. -/
def AntidiagsUnimodal {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i₁ i₂ i₃ : Fin R) (j₁ j₂ j₃ : Fin C), i₁ < i₂ → i₂ < i₃ →
    i₁.val + j₁.val = i₂.val + j₂.val → i₂.val + j₂.val = i₃.val + j₃.val →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

instance {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Decidable (AntidiagsUnimodal x) := by
  unfold AntidiagsUnimodal; infer_instance

/-- The condition of the entry. -/
def good {n : ℕ} (x : Fin 3 → Fin n → Fin 2) : Prop :=
  RowsUnimodal x ∧ DiagsUnimodal x ∧ AntidiagsUnimodal x

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good; infer_instance

/-- A223670: Number of 3 X n 0..1 arrays with rows, diagonals and antidiagonals unimodal. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 3 → Fin n → Fin 2)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (8 + 8 * X + 12 * X ^ 2 - 32 * X ^ 3 + 63 * X ^ 4 - 16 * X ^ 5 + 5 * X ^ 6 - 2 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a223670
