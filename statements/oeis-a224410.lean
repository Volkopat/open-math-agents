import Mathlib

/-!
# OEIS A224410: Barker's conjectures for 3 X n 0..1 arrays with rows unimodal and antidiagonals nondecreasing

Source: https://oeis.org/A224410 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224410 (R. H. Hardin, Apr 05 2013), offset 1: Number of 3 X n 0..1 arrays with rows unimodal
and antidiagonals nondecreasing.
Formula section:
Empirical: a(n) = (1/720)*n^6 + (1/48)*n^5 + (29/144)*n^4 + (13/16)*n^3 + (2087/360)*n^2 + (7/6)*n.
Conjectures from Colin Barker, Aug 30 2018: (Start)
G.f.: x*(8 - 20*x + 16*x^2 + 4*x^3 - 11*x^4 + 4*x^5) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* A 3 X n array with entries in 0..1 is a map x : Fin 3 -> Fin n -> Fin 2, x i j the entry in row i
  and column j; entries are compared as natural numbers.
* Antidiagonals nondecreasing: x i (j + 1) <= x (i + 1) j, that is read in order of the row index;
  the opposite reading gives the same counts, by the half-turn rotation of the array, which preserves
  the other conditions of the entry.
* A line of the array (a row, read from left to right) is unimodal when it weakly increases and then
  weakly decreases. Equivalently it has no valley: no three positions p, q, r on it, in this order,
  with the value at q smaller than both the value at p and the value at r. The statement uses the
  valley form. Reversing the order of a line does not change unimodality.
* This reading reproduces the entry's data (8, 36, 100, 228, 465, 879, 1568, ... from n = 1),
  checked by direct enumeration for n <= 7 and through a transfer matrix for every listed term.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the identity
  A(x) (1 - x)^7 = x (8 - 20*x + 16*x^2 + 4*x^3 - 11*x^4 + 4*x^5) in the formal power series ring over
  the rationals with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0); and the
  recurrence, for every n > 7, as an identity of integers.
-/

namespace OMA.S_oeis_a224410

open PowerSeries Finset

/-- Every row is unimodal: it has no valley, that is no three of its positions, from left to
right, whose middle value is smaller than both outer values. -/
def RowsUnimodal {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i : Fin R) (j₁ j₂ j₃ : Fin C), j₁ < j₂ → j₂ < j₃ → ¬ (x i j₂ < x i j₁ ∧ x i j₂ < x i j₃)

instance {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every antidiagonal (i + j constant) is nondecreasing in order of the row index (from top right
to bottom left). -/
def AntidiagsNondecreasing {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Prop :=
  ∀ (i i' : Fin R) (j j' : Fin C), i'.val = i.val + 1 → j.val = j'.val + 1 → x i j ≤ x i' j'

instance {R C m : ℕ} (x : Fin R → Fin C → Fin m) : Decidable (AntidiagsNondecreasing x) := by
  unfold AntidiagsNondecreasing; infer_instance

/-- The condition of the entry. -/
def good {n : ℕ} (x : Fin 3 → Fin n → Fin 2) : Prop :=
  RowsUnimodal x ∧ AntidiagsNondecreasing x

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good; infer_instance

/-- A224410: Number of 3 X n 0..1 arrays with rows unimodal and antidiagonals nondecreasing. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 3 → Fin n → Fin 2)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (8 - 20 * X + 16 * X ^ 2 + 4 * X ^ 3 - 11 * X ^ 4 + 4 * X ^ 5) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a224410
