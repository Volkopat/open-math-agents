import Mathlib

/-!
# OEIS A224135: Barker's conjectures for 4 X n 0..1 arrays with rows nondecreasing and antidiagonals unimodal

Source: https://oeis.org/A224135 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224135 (R. H. Hardin), offset 1: Number of 4 X n 0..1 arrays with rows nondecreasing and antidiagonals unimodal.
Formula section:
Empirical: a(n) = (1/3)*n^4 + 2*n^3 + (26/3)*n^2 + 18*n - 5 for n>2.
Conjectures from _Colin Barker_, Aug 27 2018: (Start)
G.f.: x*(16 + x - 37*x^2 + 29*x^3 + 15*x^4 - 22*x^5 + 6*x^6) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>7.
(End)

Formalization notes:
* A 4 X n array with entries in 0..1 is a map x : Fin 4 -> Fin n -> Fin 2, x i j being
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
  (for n > 2), Barker's g.f. as the identity A(x) (1 - x)^5 = (the entry's numerator)
  in the formal power series ring over the rationals, and Barker's recurrence for n > 7 as an
  identity of integers.
* The definition reproduces every listed term of the entry (16, 81, 208, ... from n = 1;
  checked by direct enumeration for small n and by a transfer-matrix count for all listed n).
-/

namespace OMA.S_oeis_a224135

open PowerSeries

/-- Every antidiagonal of x (the cells (i, j) with i + j constant), read by increasing column, is
unimodal. -/
def AntidiagUnimodal {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Prop :=
  ∀ i₁ i₂ i₃ : Fin r, ∀ j₁ j₂ j₃ : Fin c, j₁ < j₂ → j₂ < j₃ →
    (i₁ : ℕ) + j₁ = i₂ + j₂ → (i₂ : ℕ) + j₂ = i₃ + j₃ →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- The 4 X n arrays with entries in 0..1 whose rows are nondecreasing and whose antidiagonals are unimodal. -/
def Good {n : ℕ} (x : Fin 4 → Fin n → Fin 2) : Prop :=
  (∀ i, Monotone (x i)) ∧ AntidiagUnimodal x

instance {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Decidable (AntidiagUnimodal x) := by
  unfold AntidiagUnimodal; infer_instance

instance {n : ℕ} : DecidablePred (@Good n) := fun x => by
  unfold Good Monotone; infer_instance

/-- A224135(n): the number of such 4 X n arrays. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 4 → Fin n → Fin 2)).filter Good).card

/-- The empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (1/3) * (n : ℚ) ^ 4 + 2 * (n : ℚ) ^ 3 + (26/3) * (n : ℚ) ^ 2 + 18 * (n : ℚ) - 5) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (16 + X - 37 * X ^ 2 + 29 * X ^ 3 + 15 * X ^ 4 - 22 * X ^ 5 + 6 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a224135
