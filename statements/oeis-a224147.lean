import Mathlib

/-!
# OEIS A224147: Barker's conjectures for 3 X n 0..1 arrays with rows and antidiagonals unimodal and columns nondecreasing

Source: https://oeis.org/A224147 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224147 (R. H. Hardin), offset 1: Number of 3 X n 0..1 arrays with rows and antidiagonals unimodal and columns nondecreasing.
Formula section:
Empirical: a(n) = (1/720)*n^6 + (1/80)*n^5 + (23/144)*n^4 + (29/48)*n^3 + (241/180)*n^2 + (53/60)*n + 1.
Conjectures from _Colin Barker_, Aug 28 2018: (Start)
G.f.: x*(4 - 12*x + 21*x^2 - 23*x^3 + 16*x^4 - 6*x^5 + x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* A 3 X n array with entries in 0..1 is a map x : Fin 3 -> Fin n -> Fin 2, x i j being
  the entry in row i (of 3) and column j (of n).
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
  (for n > 0, i.e. for every n >= 1), Barker's g.f. as the identity A(x) (1 - x)^7 = (the entry's numerator)
  in the formal power series ring over the rationals, and Barker's recurrence for n > 7 as an
  identity of integers.
* The definition reproduces every listed term of the entry (4, 16, 49, ... from n = 1;
  checked by direct enumeration for small n and by a transfer-matrix count for all listed n).
-/

namespace OMA.S_oeis_a224147

open PowerSeries

/-- A finite sequence is unimodal (weakly increasing, then weakly decreasing): no entry is
strictly smaller than both an earlier entry and a later entry. -/
def Unimodal {L : ℕ} (f : Fin L → Fin 2) : Prop :=
  ∀ a b c : Fin L, a < b → b < c → ¬ (f b < f a ∧ f b < f c)

/-- Every antidiagonal of x (the cells (i, j) with i + j constant), read by increasing column, is
unimodal. -/
def AntidiagUnimodal {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Prop :=
  ∀ i₁ i₂ i₃ : Fin r, ∀ j₁ j₂ j₃ : Fin c, j₁ < j₂ → j₂ < j₃ →
    (i₁ : ℕ) + j₁ = i₂ + j₂ → (i₂ : ℕ) + j₂ = i₃ + j₃ →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- The 3 X n arrays with entries in 0..1 whose rows and antidiagonals are unimodal and whose columns are nondecreasing. -/
def Good {n : ℕ} (x : Fin 3 → Fin n → Fin 2) : Prop :=
  (∀ i, Unimodal (x i)) ∧ AntidiagUnimodal x ∧ ∀ j, Monotone (fun i => x i j)

instance {L : ℕ} (f : Fin L → Fin 2) : Decidable (Unimodal f) := by
  unfold Unimodal; infer_instance

instance {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Decidable (AntidiagUnimodal x) := by
  unfold AntidiagUnimodal; infer_instance

instance {n : ℕ} : DecidablePred (@Good n) := fun x => by
  unfold Good Monotone; infer_instance

/-- A224147(n): the number of such 3 X n arrays. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 3 → Fin n → Fin 2)).filter Good).card

/-- The empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = (1/720) * (n : ℚ) ^ 6 + (1/80) * (n : ℚ) ^ 5 + (23/144) * (n : ℚ) ^ 4 + (29/48) * (n : ℚ) ^ 3 + (241/180) * (n : ℚ) ^ 2 + (53/60) * (n : ℚ) + 1) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (4 - 12 * X + 21 * X ^ 2 - 23 * X ^ 3 + 16 * X ^ 4 - 6 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a224147
