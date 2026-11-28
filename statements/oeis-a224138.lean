import Mathlib

/-!
# OEIS A224138: Barker's conjectures for 7 X n 0..1 arrays with rows nondecreasing and antidiagonals unimodal

Source: https://oeis.org/A224138 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224138 (R. H. Hardin), offset 1: Number of 7 X n 0..1 arrays with rows nondecreasing and antidiagonals unimodal.
Formula section:
Empirical: a(n) = (4/315)*n^7 + (1/5)*n^6 + (112/45)*n^5 + (461/24)*n^4 + (19267/180)*n^3 + (50171/120)*n^2 + (463243/420)*n - 511 for n>5.
Conjectures from _Colin Barker_, Aug 27 2018: (Start)
G.f.: x*(128 + 1163*x - 4224*x^2 + 1611*x^3 + 9957*x^4 - 14526*x^5 + 3960*x^6 + 4357*x^7 - 1401*x^8 - 1818*x^9 + 659*x^10 + 353*x^11 - 155*x^12) / (1 - x)^8.
a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>13.
(End)

Formalization notes:
* A 7 X n array with entries in 0..1 is a map x : Fin 7 -> Fin n -> Fin 2, x i j being
  the entry in row i (of 7) and column j (of n).
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
  (for n > 5), Barker's g.f. as the identity A(x) (1 - x)^8 = (the entry's numerator)
  in the formal power series ring over the rationals, and Barker's recurrence for n > 13 as an
  identity of integers.
* The definition reproduces every listed term of the entry (128, 2187, 9688, ... from n = 1;
  checked by direct enumeration for small n and by a transfer-matrix count for all listed n).
-/

namespace OMA.S_oeis_a224138

open PowerSeries

/-- Every antidiagonal of x (the cells (i, j) with i + j constant), read by increasing column, is
unimodal. -/
def AntidiagUnimodal {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Prop :=
  ∀ i₁ i₂ i₃ : Fin r, ∀ j₁ j₂ j₃ : Fin c, j₁ < j₂ → j₂ < j₃ →
    (i₁ : ℕ) + j₁ = i₂ + j₂ → (i₂ : ℕ) + j₂ = i₃ + j₃ →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- The 7 X n arrays with entries in 0..1 whose rows are nondecreasing and whose antidiagonals are unimodal. -/
def Good {n : ℕ} (x : Fin 7 → Fin n → Fin 2) : Prop :=
  (∀ i, Monotone (x i)) ∧ AntidiagUnimodal x

instance {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Decidable (AntidiagUnimodal x) := by
  unfold AntidiagUnimodal; infer_instance

instance {n : ℕ} : DecidablePred (@Good n) := fun x => by
  unfold Good Monotone; infer_instance

/-- A224138(n): the number of such 7 X n arrays. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 7 → Fin n → Fin 2)).filter Good).card

/-- The empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℚ) = (4/315) * (n : ℚ) ^ 7 + (1/5) * (n : ℚ) ^ 6 + (112/45) * (n : ℚ) ^ 5 + (461/24) * (n : ℚ) ^ 4 + (19267/180) * (n : ℚ) ^ 3 + (50171/120) * (n : ℚ) ^ 2 + (463243/420) * (n : ℚ) - 511) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (128 + 1163 * X - 4224 * X ^ 2 + 1611 * X ^ 3 + 9957 * X ^ 4 - 14526 * X ^ 5 + 3960 * X ^ 6 + 4357 * X ^ 7 - 1401 * X ^ 8 - 1818 * X ^ 9 + 659 * X ^ 10 + 353 * X ^ 11 - 155 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a224138
