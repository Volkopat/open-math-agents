import Mathlib

/-!
# OEIS A250882: Barker's conjectures for (5+1) X (n+1) 0..3 arrays with nondecreasing horizontal differences and vertical sums

Source: https://oeis.org/A250882 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A250882 (R. H. Hardin, Nov 28 2014), offset 1: Number of (5+1) X (n+1) 0..3 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing x(i,j)+x(i-1,j) in the j direction.
Formula section:
Empirical: a(n) = 5328*n^3 + 14468*n^2 + 13238*n + 4096.
Conjectures from _Colin Barker_, Nov 22 2018: (Start)
G.f.: 2*x*(18565 - 8726*x + 8193*x^2 - 2048*x^3) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.
(End)

Formalization notes:
* An array is x : Fin 6 → Fin (n + 1) → Fin 4, with row i and column j (so 5+1 rows and n+1
  columns); entries are compared as natural numbers or integers, never modulo 4.
* Nondecreasing x(i,j)-x(i,j-1) in the i direction: for each column j ≥ 1 the differences
  x(i,j) - x(i,j-1) do not decrease as i increases; nondecreasing x(i,j)+x(i-1,j) in the j direction: for each row i ≥ 1 the values
  named do not decrease as j increases. Both conditions compare consecutive indices only, so `good`
  asks, for the 2 X 2 block of every two consecutive rows i-1, i and columns j-1, j,
  x(i-1,j) - x(i-1,j-1) ≤ x(i,j) - x(i,j-1) and x(i,j-1) + x(i-1,j-1) ≤ x(i,j) + x(i-1,j) (`blk`, with p, q the upper row and r, s the lower row of the block).
* This reading reproduces all 25 listed terms of the entry (37130, 131068, 317878, ...), checked by a
  transfer-matrix computation over the 4^6 columns, and the same reading reproduces the data of the
  sibling entries A250878 - A250881 (fewer rows).
* a(n) is defined for every n (a(0) counts the single-column arrays); the entry starts at n = 1, so the
  g.f. is stated for A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) (1 - x)^4 = (the entry's
  numerator) in the formal power series ring over the rationals, and the recurrence as an identity of
  integers for every n > 4.
* `main` is the conjunction of Barker's two conjectures, the problem as posed by the site. Hardin's
  empirical polynomial is not part of it.
-/

namespace OMA.S_oeis_a250882

open PowerSeries

/-- The 2 X 2 block condition: p = x(i-1,j-1), q = x(i-1,j) (upper row), r = x(i,j-1), s = x(i,j). -/
def blk (p q r s : Fin 4) : Prop :=
  ((q : ℕ) : ℤ) - (p : ℕ) ≤ ((s : ℕ) : ℤ) - (r : ℕ) ∧ (r : ℕ) + (p : ℕ) ≤ (s : ℕ) + (q : ℕ)

instance : ∀ p q r s, Decidable (blk p q r s) := fun p q r s => by unfold blk; infer_instance

/-- Every 2 X 2 block of consecutive rows and columns satisfies `blk`. -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1) → Fin 4) : Prop :=
  ∀ i : Fin 5, ∀ j : Fin n,
    blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A250882: the number of good (5+1) X (n+1) arrays over 0..3. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 6 → Fin (n + 1) → Fin 4)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      2 * X * (18565 - 8726 * X + 8193 * X ^ 2 - 2048 * X ^ 3) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a250882
