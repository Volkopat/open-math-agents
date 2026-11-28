import Mathlib

/-!
# OEIS A224025: Barker's conjectures for 3 X n 0..3 arrays with rows nondecreasing and antidiagonals unimodal

Source: https://oeis.org/A224025 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224025 (R. H. Hardin), offset 1: Number of 3 X n 0..3 arrays with rows nondecreasing and antidiagonals unimodal.
Formula section:
Empirical: a(n) = (353/181440)*n^9 + (5/126)*n^8 + (12287/30240)*n^7 + (131/60)*n^6 + (64877/8640)*n^5 + (135/8)*n^4 + (998257/45360)*n^3 + (53933/2520)*n^2 + (3421/252)*n - 2 for n>1.
Conjectures from _Colin Barker_, Aug 26 2018: (Start)
G.f.: x*(64 + 360*x - 324*x^2 + 1883*x^3 - 3447*x^4 + 4386*x^5 - 3748*x^6 + 2193*x^7 - 825*x^8 + 182*x^9 - 18*x^10) / (1 - x)^10.
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>11.
(End)

Formalization notes:
* A 3 X n array with entries in 0..3 is a map x : Fin 3 -> Fin n -> Fin 4, x i j being
  the entry in row i (of 3) and column j (of n).
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
  (for n > 1), Barker's g.f. as the identity A(x) (1 - x)^10 = (the entry's numerator)
  in the formal power series ring over the rationals, and Barker's recurrence for n > 11 as an
  identity of integers.
* The definition reproduces every listed term of the entry (64, 1000, 6796, ... from n = 1;
  checked by direct enumeration for small n and by a transfer-matrix count for all listed n).
-/

namespace OMA.S_oeis_a224025

open PowerSeries

/-- Every antidiagonal of x (the cells (i, j) with i + j constant), read by increasing column, is
unimodal. -/
def AntidiagUnimodal {r c : ℕ} (x : Fin r → Fin c → Fin 4) : Prop :=
  ∀ i₁ i₂ i₃ : Fin r, ∀ j₁ j₂ j₃ : Fin c, j₁ < j₂ → j₂ < j₃ →
    (i₁ : ℕ) + j₁ = i₂ + j₂ → (i₂ : ℕ) + j₂ = i₃ + j₃ →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- The 3 X n arrays with entries in 0..3 whose rows are nondecreasing and whose antidiagonals are unimodal. -/
def Good {n : ℕ} (x : Fin 3 → Fin n → Fin 4) : Prop :=
  (∀ i, Monotone (x i)) ∧ AntidiagUnimodal x

instance {r c : ℕ} (x : Fin r → Fin c → Fin 4) : Decidable (AntidiagUnimodal x) := by
  unfold AntidiagUnimodal; infer_instance

instance {n : ℕ} : DecidablePred (@Good n) := fun x => by
  unfold Good Monotone; infer_instance

/-- A224025(n): the number of such 3 X n arrays. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 3 → Fin n → Fin 4)).filter Good).card

/-- The empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℚ) = (353/181440) * (n : ℚ) ^ 9 + (5/126) * (n : ℚ) ^ 8 + (12287/30240) * (n : ℚ) ^ 7 + (131/60) * (n : ℚ) ^ 6 + (64877/8640) * (n : ℚ) ^ 5 + (135/8) * (n : ℚ) ^ 4 + (998257/45360) * (n : ℚ) ^ 3 + (53933/2520) * (n : ℚ) ^ 2 + (3421/252) * (n : ℚ) - 2) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (64 + 360 * X - 324 * X ^ 2 + 1883 * X ^ 3 - 3447 * X ^ 4 + 4386 * X ^ 5 - 3748 * X ^ 6 + 2193 * X ^ 7 - 825 * X ^ 8 + 182 * X ^ 9 - 18 * X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a224025
