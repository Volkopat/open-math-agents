import Mathlib

/-!
# OEIS A224014: Barker's conjectures for 4 X n 0..2 arrays with rows nondecreasing and antidiagonals unimodal

Source: https://oeis.org/A224014 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224014 (R. H. Hardin), offset 1: Number of 4 X n 0..2 arrays with rows nondecreasing and antidiagonals unimodal.
Formula section:
Empirical: a(n) = (41/4032)*n^8 + (55/336)*n^7 + (733/480)*n^6 + (1037/120)*n^5 + (4789/192)*n^4 + (2125/48)*n^3 + (216821/5040)*n^2 + (9329/210)*n + 4 for n>2.
Conjectures from _Colin Barker_, Aug 26 2018: (Start)
G.f.: x*(81 + 567*x - 1370*x^2 + 1991*x^3 + 132*x^4 - 4590*x^5 + 7855*x^6 - 6900*x^7 + 3514*x^8 - 990*x^9 + 120*x^10) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>11.
(End)

Formalization notes:
* A 4 X n array with entries in 0..2 is a map x : Fin 4 -> Fin n -> Fin 3, x i j being
  the entry in row i (of 4) and column j (of n).
* A finite sequence is unimodal when it weakly increases up to some point and weakly decreases
  afterwards (plateaus allowed); equivalently, as stated here, no entry is strictly smaller than
  both an earlier and a later entry.
* Antidiagonals are the cells with i + j constant, read by increasing column (the direction does not
  matter for unimodality).
* Rows nondecreasing: x i j <= x i j′ whenever j <= j′. Reading them as nonincreasing gives the
  same counts (the half turn of the array preserves diagonals and antidiagonals).
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the entry's three conjectures: the empirical polynomial
  (for n > 2), Barker's g.f. as the identity A(x) (1 - x)^9 = (the entry's numerator)
  in the formal power series ring over the rationals, and Barker's recurrence for n > 11 as an
  identity of integers.
* The definition reproduces every listed term of the entry (81, 1296, 7378, ... from n = 1;
  checked by direct enumeration for small n and by a transfer-matrix count for all listed n).
-/

namespace OMA.S_oeis_a224014

open PowerSeries

/-- Every antidiagonal of x (the cells (i, j) with i + j constant), read by increasing column, is
unimodal. -/
def AntidiagUnimodal {r c : ℕ} (x : Fin r → Fin c → Fin 3) : Prop :=
  ∀ i₁ i₂ i₃ : Fin r, ∀ j₁ j₂ j₃ : Fin c, j₁ < j₂ → j₂ < j₃ →
    (i₁ : ℕ) + j₁ = i₂ + j₂ → (i₂ : ℕ) + j₂ = i₃ + j₃ →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- The 4 X n arrays with entries in 0..2 whose rows are nondecreasing and whose antidiagonals are unimodal. -/
def Good {n : ℕ} (x : Fin 4 → Fin n → Fin 3) : Prop :=
  (∀ i, Monotone (x i)) ∧ AntidiagUnimodal x

instance {r c : ℕ} (x : Fin r → Fin c → Fin 3) : Decidable (AntidiagUnimodal x) := by
  unfold AntidiagUnimodal; infer_instance

instance {n : ℕ} : DecidablePred (@Good n) := fun x => by
  unfold Good Monotone; infer_instance

/-- A224014(n): the number of such 4 X n arrays. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 4 → Fin n → Fin 3)).filter Good).card

/-- The empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (41/4032) * (n : ℚ) ^ 8 + (55/336) * (n : ℚ) ^ 7 + (733/480) * (n : ℚ) ^ 6 + (1037/120) * (n : ℚ) ^ 5 + (4789/192) * (n : ℚ) ^ 4 + (2125/48) * (n : ℚ) ^ 3 + (216821/5040) * (n : ℚ) ^ 2 + (9329/210) * (n : ℚ) + 4) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (81 + 567 * X - 1370 * X ^ 2 + 1991 * X ^ 3 + 132 * X ^ 4 - 4590 * X ^ 5 + 7855 * X ^ 6 - 6900 * X ^ 7 + 3514 * X ^ 8 - 990 * X ^ 9 + 120 * X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a224014
