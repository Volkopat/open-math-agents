import Mathlib

/-!
# OEIS A224136: Barker's conjectures for 5 X n 0..1 arrays with rows nondecreasing and antidiagonals unimodal

Source: https://oeis.org/A224136 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224136 (R. H. Hardin), offset 1: Number of 5 X n 0..1 arrays with rows nondecreasing and antidiagonals unimodal.
Formula section:
Empirical: a(n) = (2/15)*n^5 + (7/6)*n^4 + (47/6)*n^3 + (173/6)*n^2 + (1981/30)*n - 27 for n>3.
Conjectures from _Colin Barker_, Aug 27 2018: (Start)
G.f.: x*(32 + 51*x - 230*x^2 + 152*x^3 + 179*x^4 - 228*x^5 + 18*x^6 + 63*x^7 - 21*x^8) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>9.
(End)

Formalization notes:
* A 5 X n array with entries in 0..1 is a map x : Fin 5 -> Fin n -> Fin 2, x i j being
  the entry in row i (of 5) and column j (of n).
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
  (for n > 3), Barker's g.f. as the identity A(x) (1 - x)^6 = (the entry's numerator)
  in the formal power series ring over the rationals, and Barker's recurrence for n > 9 as an
  identity of integers.
* The definition reproduces every listed term of the entry (32, 243, 748, ... from n = 1;
  checked by direct enumeration for small n and by a transfer-matrix count for all listed n).
-/

namespace OMA.S_oeis_a224136

open PowerSeries

/-- Every antidiagonal of x (the cells (i, j) with i + j constant), read by increasing column, is
unimodal. -/
def AntidiagUnimodal {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Prop :=
  ∀ i₁ i₂ i₃ : Fin r, ∀ j₁ j₂ j₃ : Fin c, j₁ < j₂ → j₂ < j₃ →
    (i₁ : ℕ) + j₁ = i₂ + j₂ → (i₂ : ℕ) + j₂ = i₃ + j₃ →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- The 5 X n arrays with entries in 0..1 whose rows are nondecreasing and whose antidiagonals are unimodal. -/
def Good {n : ℕ} (x : Fin 5 → Fin n → Fin 2) : Prop :=
  (∀ i, Monotone (x i)) ∧ AntidiagUnimodal x

instance {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Decidable (AntidiagUnimodal x) := by
  unfold AntidiagUnimodal; infer_instance

instance {n : ℕ} : DecidablePred (@Good n) := fun x => by
  unfold Good Monotone; infer_instance

/-- A224136(n): the number of such 5 X n arrays. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 5 → Fin n → Fin 2)).filter Good).card

/-- The empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℚ) = (2/15) * (n : ℚ) ^ 5 + (7/6) * (n : ℚ) ^ 4 + (47/6) * (n : ℚ) ^ 3 + (173/6) * (n : ℚ) ^ 2 + (1981/30) * (n : ℚ) - 27) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (32 + 51 * X - 230 * X ^ 2 + 152 * X ^ 3 + 179 * X ^ 4 - 228 * X ^ 5 + 18 * X ^ 6 + 63 * X ^ 7 - 21 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a224136
