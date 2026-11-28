import Mathlib

/-!
# OEIS A224137: Barker's conjectures for 6 X n 0..1 arrays with rows nondecreasing and antidiagonals unimodal

Source: https://oeis.org/A224137 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A224137 (R. H. Hardin), offset 1: Number of 6 X n 0..1 arrays with rows nondecreasing and antidiagonals unimodal.
Formula section:
Empirical: a(n) = (2/45)*n^6 + (8/15)*n^5 + (181/36)*n^4 + 28*n^3 + (19247/180)*n^2 + (3952/15)*n - 120 for n>4.
Conjectures from _Colin Barker_, Aug 27 2018: (Start)
G.f.: x*(64 + 281*x - 1067*x^2 + 617*x^3 + 1387*x^4 - 1840*x^5 + 160*x^6 + 696*x^7 - 172*x^8 - 154*x^9 + 60*x^10) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>11.
(End)

Formalization notes:
* A 6 X n array with entries in 0..1 is a map x : Fin 6 -> Fin n -> Fin 2, x i j being
  the entry in row i (of 6) and column j (of n).
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
  (for n > 4), Barker's g.f. as the identity A(x) (1 - x)^7 = (the entry's numerator)
  in the formal power series ring over the rationals, and Barker's recurrence for n > 11 as an
  identity of integers.
* The definition reproduces every listed term of the entry (64, 729, 2692, ... from n = 1;
  checked by direct enumeration for small n and by a transfer-matrix count for all listed n).
-/

namespace OMA.S_oeis_a224137

open PowerSeries

/-- Every antidiagonal of x (the cells (i, j) with i + j constant), read by increasing column, is
unimodal. -/
def AntidiagUnimodal {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Prop :=
  ∀ i₁ i₂ i₃ : Fin r, ∀ j₁ j₂ j₃ : Fin c, j₁ < j₂ → j₂ < j₃ →
    (i₁ : ℕ) + j₁ = i₂ + j₂ → (i₂ : ℕ) + j₂ = i₃ + j₃ →
    ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃)

/-- The 6 X n arrays with entries in 0..1 whose rows are nondecreasing and whose antidiagonals are unimodal. -/
def Good {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : Prop :=
  (∀ i, Monotone (x i)) ∧ AntidiagUnimodal x

instance {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Decidable (AntidiagUnimodal x) := by
  unfold AntidiagUnimodal; infer_instance

instance {n : ℕ} : DecidablePred (@Good n) := fun x => by
  unfold Good Monotone; infer_instance

/-- A224137(n): the number of such 6 X n arrays. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 6 → Fin n → Fin 2)).filter Good).card

/-- The empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℚ) = (2/45) * (n : ℚ) ^ 6 + (8/15) * (n : ℚ) ^ 5 + (181/36) * (n : ℚ) ^ 4 + 28 * (n : ℚ) ^ 3 + (19247/180) * (n : ℚ) ^ 2 + (3952/15) * (n : ℚ) - 120) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (64 + 281 * X - 1067 * X ^ 2 + 617 * X ^ 3 + 1387 * X ^ 4 - 1840 * X ^ 5 + 160 * X ^ 6 + 696 * X ^ 7 - 172 * X ^ 8 - 154 * X ^ 9 + 60 * X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a224137
