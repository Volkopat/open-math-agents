import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Lemmas

/-!
# Column one of the Geode Bi-Tri array

The Geode factorization `S - 1 = (x + y) G` defines the columns through
the hyper-Catalan coefficients of `S`. Column and row indices both start
at zero. Rubine gives this recurrence in Section 5 and proves the
general Bi-Tri closed form in Theorem 9, arXiv:2507.04552.

Sources: https://oeis.org/A383456, https://oeis.org/A383453 and
https://arxiv.org/abs/2507.04552. OEIS entries: CC BY-SA 4.0.
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a383456

/-- Hyper-Catalan coefficient for i triangular and j quadrilateral faces. -/
def hyperCoeff (i j : ℕ) : ℚ :=
  ((2 * i + 3 * j).factorial : ℚ) /
    (((1 + i + 2 * j).factorial : ℚ) * i.factorial * j.factorial)

/-- Column j, row i of G, by coefficient comparison in (x+y)G = S-1. -/
def geodeColumn : ℕ → ℕ → ℚ
  | 0, i => hyperCoeff (i + 1) 0
  | j + 1, i => hyperCoeff (i + 1) (j + 1) - geodeColumn j (i + 1)

theorem main :
    ∀ n : ℕ, geodeColumn 1 n =
      2 * ((2 * n + 4).choose n : ℚ) * ((n : ℚ) + 3) / ((n : ℚ) + 2) := by
  sorry

end OMA.S_oeis_a383456
