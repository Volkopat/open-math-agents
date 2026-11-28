import Mathlib

/-!
# OEIS A250819: Barker's conjectures for (7+1) X (n+1) 0..2 arrays with nondecreasing horizontal differences and vertical minima

Source: https://oeis.org/A250819 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A250819 (R. H. Hardin, Nov 27 2014), offset 1: Number of (7+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction.
Formula section:
Empirical: a(n) = (1695/4)*n^4 + 3786*n^3 + (54287/4)*n^2 + (33539/2)*n + 6561.
Conjectures from _Colin Barker_, Nov 21 2018: (Start)
G.f.: x*(41112 - 74105*x + 69406*x^2 - 32804*x^3 + 6561*x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
(End)

Formalization notes:
* An array is x : Fin 8 → Fin (n + 1) → Fin 3, with row i and column j (so 7+1 rows and n+1
  columns); entries are compared as natural numbers or integers, never modulo 3.
* Nondecreasing x(i,j)-x(i,j-1) in the i direction: for each column j ≥ 1 the differences
  x(i,j) - x(i,j-1) do not decrease as i increases; nondecreasing min(x(i,j),x(i-1,j)) in the j direction: for each row i ≥ 1 the values
  named do not decrease as j increases. Both conditions compare consecutive indices only, so `good`
  asks, for the 2 X 2 block of every two consecutive rows i-1, i and columns j-1, j,
  x(i-1,j) - x(i-1,j-1) ≤ x(i,j) - x(i,j-1) and min(x(i,j-1), x(i-1,j-1)) ≤ min(x(i,j), x(i-1,j)) (`blk`, with p, q the upper row and r, s the lower row of the block).
* This reading reproduces all 24 listed terms of the entry (41112, 131455, 315561, ...), checked by a
  transfer-matrix computation over the 3^8 columns, and the same reading reproduces the data of the
  sibling entries A250813 - A250818 (fewer rows).
* a(n) is defined for every n (a(0) counts the single-column arrays); the entry starts at n = 1, so the
  g.f. is stated for A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) (1 - x)^5 = (the entry's
  numerator) in the formal power series ring over the rationals, and the recurrence as an identity of
  integers for every n > 5.
* `main` is the conjunction of Barker's two conjectures, the problem as posed by the site. Hardin's
  empirical polynomial is not part of it.
-/

namespace OMA.S_oeis_a250819

open PowerSeries

/-- The 2 X 2 block condition: p = x(i-1,j-1), q = x(i-1,j) (upper row), r = x(i,j-1), s = x(i,j). -/
def blk (p q r s : Fin 3) : Prop :=
  ((q : ℕ) : ℤ) - (p : ℕ) ≤ ((s : ℕ) : ℤ) - (r : ℕ) ∧ min (r : ℕ) (p : ℕ) ≤ min (s : ℕ) (q : ℕ)

instance : ∀ p q r s, Decidable (blk p q r s) := fun p q r s => by unfold blk; infer_instance

/-- Every 2 X 2 block of consecutive rows and columns satisfies `blk`. -/
def good {n : ℕ} (x : Fin 8 → Fin (n + 1) → Fin 3) : Prop :=
  ∀ i : Fin 7, ∀ j : Fin n,
    blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A250819: the number of good (7+1) X (n+1) arrays over 0..2. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 8 → Fin (n + 1) → Fin 3)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (41112 - 74105 * X + 69406 * X ^ 2 - 32804 * X ^ 3 + 6561 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a250819
