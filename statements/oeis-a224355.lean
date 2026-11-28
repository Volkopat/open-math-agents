import Mathlib

/-!
# OEIS A224355: Barker's conjectures for 4 X n 0..2 arrays with diagonals and antidiagonals unimodal and rows nondecreasing

Source: https://oeis.org/A224355 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224355 (R. H. Hardin), offset 1: Number of 4 X n 0..2 arrays with diagonals and antidiagonals unimodal and rows nondecreasing.
Formula section:
Empirical: a(n) = (41/4032)*n^8 + (9/112)*n^7 + (239/288)*n^6 + (109/24)*n^5 + (12079/576)*n^4 + (39/16)*n^3 + (310151/1008)*n^2 - (21299/84)*n + 142 for n>3.
Conjectures from _Colin Barker_, Aug 29 2018: (Start)
G.f.: x*(81 + 567*x - 2868*x^2 + 6540*x^3 - 6063*x^4 - 415*x^5 + 7550*x^6 - 8564*x^7 + 4918*x^8 - 1584*x^9 + 262*x^10 - 14*x^11) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>12.
(End)

Formalization notes:
* A 4 X n array with entries in 0..2 is a map x : Fin 4 -> Fin n -> Fin 3, x i j being
  the entry in row i (of 4) and column j (of n).
* A finite sequence is unimodal when it weakly increases up to some point and weakly decreases
  afterwards (plateaus allowed); equivalently, as stated here, no entry is strictly smaller than
  both an earlier and a later entry.
* Diagonals are the cells with i - j constant and antidiagonals the cells with i + j constant;
  each is read by increasing column (the direction does not matter for unimodality).
* Rows nondecreasing: x i j <= x i j′ whenever j <= j′. Reading them as nonincreasing gives the
  same counts (the half turn of the array preserves diagonals and antidiagonals).
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the entry's three conjectures: the empirical polynomial
  (for n > 3), Barker's g.f. as the identity A(x) (1 - x)^9 = (the entry's numerator)
  in the formal power series ring over the rationals, and Barker's recurrence for n > 12 as an
  identity of integers.
* The definition reproduces every listed term of the entry (81, 1296, 5880, ... from n = 1;
  checked by direct enumeration for small n and by a transfer-matrix count for all listed n).
-/

namespace OMA.S_oeis_a224355

open PowerSeries

/-- Every diagonal of x (the cells (i, j) with i - j constant), read by increasing column, is
unimodal. -/
def DiagUnimodal {r c : ℕ} (x : Fin r → Fin c → Fin 3) : Prop :=
  ∀ i₁ i₂ i₃ : Fin r, ∀ j₁ j₂ j₃ : Fin c, j₁ < j₂ → j₂ < j₃ →
    (i₁ : ℤ) - j₁ = (i₂ : ℤ) - j₂ → (i₂ : ℤ) - j₂ = (i₃ : ℤ) - j₃ →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- Every antidiagonal of x (the cells (i, j) with i + j constant), read by increasing column, is
unimodal. -/
def AntidiagUnimodal {r c : ℕ} (x : Fin r → Fin c → Fin 3) : Prop :=
  ∀ i₁ i₂ i₃ : Fin r, ∀ j₁ j₂ j₃ : Fin c, j₁ < j₂ → j₂ < j₃ →
    (i₁ : ℕ) + j₁ = i₂ + j₂ → (i₂ : ℕ) + j₂ = i₃ + j₃ →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- The 4 X n arrays with entries in 0..2 whose diagonals and antidiagonals are unimodal and whose rows are nondecreasing. -/
def Good {n : ℕ} (x : Fin 4 → Fin n → Fin 3) : Prop :=
  DiagUnimodal x ∧ AntidiagUnimodal x ∧ ∀ i, Monotone (x i)

instance {r c : ℕ} (x : Fin r → Fin c → Fin 3) : Decidable (DiagUnimodal x) := by
  unfold DiagUnimodal; infer_instance

instance {r c : ℕ} (x : Fin r → Fin c → Fin 3) : Decidable (AntidiagUnimodal x) := by
  unfold AntidiagUnimodal; infer_instance

instance {n : ℕ} : DecidablePred (@Good n) := fun x => by
  unfold Good Monotone; infer_instance

/-- A224355(n): the number of such 4 X n arrays. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 4 → Fin n → Fin 3)).filter Good).card

/-- The empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℚ) = (41/4032) * (n : ℚ) ^ 8 + (9/112) * (n : ℚ) ^ 7 + (239/288) * (n : ℚ) ^ 6 + (109/24) * (n : ℚ) ^ 5 + (12079/576) * (n : ℚ) ^ 4 + (39/16) * (n : ℚ) ^ 3 + (310151/1008) * (n : ℚ) ^ 2 - (21299/84) * (n : ℚ) + 142) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (81 + 567 * X - 2868 * X ^ 2 + 6540 * X ^ 3 - 6063 * X ^ 4 - 415 * X ^ 5 + 7550 * X ^ 6 - 8564 * X ^ 7 + 4918 * X ^ 8 - 1584 * X ^ 9 + 262 * X ^ 10 - 14 * X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a224355
