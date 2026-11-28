import Mathlib

/-!
# OEIS A223919: Barker's conjectures for 2 X n 0..2 arrays with rows and antidiagonals unimodal and columns nondecreasing

Source: https://oeis.org/A223919 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A223919 (R. H. Hardin), offset 1: Number of 2 X n 0..2 arrays with rows and antidiagonals unimodal and columns nondecreasing.
Formula section:
Empirical: a(n) = (1/10080)*n^8 + (1/504)*n^7 + (1/40)*n^6 + (109/720)*n^5 + (259/480)*n^4 + (173/144)*n^3 + (4877/2520)*n^2 + (481/420)*n + 1.
Conjectures from _Colin Barker_, Feb 23 2018: (Start)
G.f.: x*(6 - 18*x + 50*x^2 - 82*x^3 + 88*x^4 - 62*x^5 + 29*x^6 - 8*x^7 + x^8) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.
(End)

Formalization notes:
* A 2 X n array with entries in 0..2 is a map x : Fin 2 -> Fin n -> Fin 3, x i j being
  the entry in row i (of 2) and column j (of n).
* A finite sequence is unimodal when it weakly increases up to some point and weakly decreases
  afterwards (plateaus allowed); equivalently, as stated here, no entry is strictly smaller than
  both an earlier and a later entry.
* Antidiagonals are the cells with i + j constant, read by increasing column (the direction does not
  matter for unimodality).
* Columns nondecreasing from top to bottom: x i j <= x i′ j whenever i <= i′. Reading them as
  nonincreasing gives the same counts (the half turn preserves rows and antidiagonals).
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the entry's three conjectures: the empirical polynomial
  (for n > 0, i.e. for every n >= 1), Barker's g.f. as the identity A(x) (1 - x)^9 = (the entry's numerator)
  in the formal power series ring over the rationals, and Barker's recurrence for n > 9 as an
  identity of integers.
* The definition reproduces every listed term of the entry (6, 36, 158, ... from n = 1;
  checked by direct enumeration for small n and by a transfer-matrix count for all listed n).
-/

namespace OMA.S_oeis_a223919

open PowerSeries

/-- A finite sequence is unimodal (weakly increasing, then weakly decreasing): no entry is
strictly smaller than both an earlier entry and a later entry. -/
def Unimodal {L : ℕ} (f : Fin L → Fin 3) : Prop :=
  ∀ a b c : Fin L, a < b → b < c → ¬ (f b < f a ∧ f b < f c)

/-- Every antidiagonal of x (the cells (i, j) with i + j constant), read by increasing column, is
unimodal. -/
def AntidiagUnimodal {r c : ℕ} (x : Fin r → Fin c → Fin 3) : Prop :=
  ∀ i₁ i₂ i₃ : Fin r, ∀ j₁ j₂ j₃ : Fin c, j₁ < j₂ → j₂ < j₃ →
    (i₁ : ℕ) + j₁ = i₂ + j₂ → (i₂ : ℕ) + j₂ = i₃ + j₃ →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- The 2 X n arrays with entries in 0..2 whose rows and antidiagonals are unimodal and whose columns are nondecreasing. -/
def Good {n : ℕ} (x : Fin 2 → Fin n → Fin 3) : Prop :=
  (∀ i, Unimodal (x i)) ∧ AntidiagUnimodal x ∧ ∀ j, Monotone (fun i => x i j)

instance {L : ℕ} (f : Fin L → Fin 3) : Decidable (Unimodal f) := by
  unfold Unimodal; infer_instance

instance {r c : ℕ} (x : Fin r → Fin c → Fin 3) : Decidable (AntidiagUnimodal x) := by
  unfold AntidiagUnimodal; infer_instance

instance {n : ℕ} : DecidablePred (@Good n) := fun x => by
  unfold Good Monotone; infer_instance

/-- A223919(n): the number of such 2 X n arrays. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 2 → Fin n → Fin 3)).filter Good).card

/-- The empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = (1/10080) * (n : ℚ) ^ 8 + (1/504) * (n : ℚ) ^ 7 + (1/40) * (n : ℚ) ^ 6 + (109/720) * (n : ℚ) ^ 5 + (259/480) * (n : ℚ) ^ 4 + (173/144) * (n : ℚ) ^ 3 + (4877/2520) * (n : ℚ) ^ 2 + (481/420) * (n : ℚ) + 1) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (6 - 18 * X + 50 * X ^ 2 - 82 * X ^ 3 + 88 * X ^ 4 - 62 * X ^ 5 + 29 * X ^ 6 - 8 * X ^ 7 + X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a223919
