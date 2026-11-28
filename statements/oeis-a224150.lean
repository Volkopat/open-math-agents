import Mathlib

/-!
# OEIS A224150: Barker's conjectures for 6 X n 0..1 arrays with rows and antidiagonals unimodal and columns nondecreasing

Source: https://oeis.org/A224150 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224150 (R. H. Hardin), offset 1: Number of 6 X n 0..1 arrays with rows and antidiagonals unimodal and columns nondecreasing.
Formula section:
Empirical: a(n) = (1/479001600)*n^12 + (1/26611200)*n^11 + (43/43545600)*n^10 + (29/1451520)*n^9 + (5671/14515200)*n^8 + (2219/345600)*n^7 + (2174569/43545600)*n^6 + (116341/483840)*n^5 + (8531549/10886400)*n^4 + (2862857/1814400)*n^3 + (3602461/1663200)*n^2 + (2327/1980)*n + 1.
Conjectures from _Colin Barker_, Aug 28 2018: (Start)
G.f.: x*(7 - 42*x + 151*x^2 - 396*x^3 + 762*x^4 - 1076*x^5 + 1137*x^6 - 906*x^7 + 538*x^8 - 230*x^9 + 67*x^10 - 12*x^11 + x^12) / (1 - x)^13.
a(n) = 13*a(n-1) - 78*a(n-2) + 286*a(n-3) - 715*a(n-4) + 1287*a(n-5) - 1716*a(n-6) + 1716*a(n-7) - 1287*a(n-8) + 715*a(n-9) - 286*a(n-10) + 78*a(n-11) - 13*a(n-12) + a(n-13) for n>13.
(End)

Formalization notes:
* A 6 X n array with entries in 0..1 is a map x : Fin 6 -> Fin n -> Fin 2, x i j being
  the entry in row i (of 6) and column j (of n).
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
  (for n > 0, i.e. for every n >= 1), Barker's g.f. as the identity A(x) (1 - x)^13 = (the entry's numerator)
  in the formal power series ring over the rationals, and Barker's recurrence for n > 13 as an
  identity of integers.
* The definition reproduces every listed term of the entry (7, 49, 242, ... from n = 1;
  checked by direct enumeration for small n and by a transfer-matrix count for all listed n).
-/

namespace OMA.S_oeis_a224150

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

/-- The 6 X n arrays with entries in 0..1 whose rows and antidiagonals are unimodal and whose columns are nondecreasing. -/
def Good {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : Prop :=
  (∀ i, Unimodal (x i)) ∧ AntidiagUnimodal x ∧ ∀ j, Monotone (fun i => x i j)

instance {L : ℕ} (f : Fin L → Fin 2) : Decidable (Unimodal f) := by
  unfold Unimodal; infer_instance

instance {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Decidable (AntidiagUnimodal x) := by
  unfold AntidiagUnimodal; infer_instance

instance {n : ℕ} : DecidablePred (@Good n) := fun x => by
  unfold Good Monotone; infer_instance

/-- A224150(n): the number of such 6 X n arrays. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 6 → Fin n → Fin 2)).filter Good).card

/-- The empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = (1/479001600) * (n : ℚ) ^ 12 + (1/26611200) * (n : ℚ) ^ 11 + (43/43545600) * (n : ℚ) ^ 10 + (29/1451520) * (n : ℚ) ^ 9 + (5671/14515200) * (n : ℚ) ^ 8 + (2219/345600) * (n : ℚ) ^ 7 + (2174569/43545600) * (n : ℚ) ^ 6 + (116341/483840) * (n : ℚ) ^ 5 + (8531549/10886400) * (n : ℚ) ^ 4 + (2862857/1814400) * (n : ℚ) ^ 3 + (3602461/1663200) * (n : ℚ) ^ 2 + (2327/1980) * (n : ℚ) + 1) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 13 =
      X * (7 - 42 * X + 151 * X ^ 2 - 396 * X ^ 3 + 762 * X ^ 4 - 1076 * X ^ 5 + 1137 * X ^ 6 - 906 * X ^ 7 + 538 * X ^ 8 - 230 * X ^ 9 + 67 * X ^ 10 - 12 * X ^ 11 + X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 13 * a (n - 1) - 78 * a (n - 2) + 286 * a (n - 3) - 715 * a (n - 4) + 1287 * a (n - 5) - 1716 * a (n - 6) + 1716 * a (n - 7) - 1287 * a (n - 8) + 715 * a (n - 9) - 286 * a (n - 10) + 78 * a (n - 11) - 13 * a (n - 12) + a (n - 13) := by
  sorry

end OMA.S_oeis_a224150
