import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Nonzero successive principal minors need not have positive products

Source: https://mathoverflow.net/questions/292809
Credit: @etaubman.

Abdelmalek Abdesselam suggested a diagonal counterexample in comment 726481. We use
`diag(1, -1)` over the rationals. Its rank is two and every leading principal minor
is nonzero, but its successive minor product and ratio at index two are negative.

The title asks about nonsingular symmetric matrices; the body quotes a statement for
rank r with nonzero leading minors through r. The statement below follows the title.
Since positivity needs an ordering, the universal statement uses ordered number fields.
The rational counterexample also answers the source's real-matrix interpretation.
The empty leading minor has determinant one, giving the usual convention D_0 = 1.
-/

namespace OMA.S_mo_292809

noncomputable def leadingMinor {K : Type*} [CommRing K] {n : ℕ}
    (S : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : k ≤ n) : K :=
  Matrix.det (S.submatrix (Fin.castLE hk) (Fin.castLE hk))

theorem main :
    ∀ (K : Type) [Field K] [LinearOrder K] [IsOrderedRing K] [NumberField K]
      (n : ℕ) (S : Matrix (Fin n) (Fin n) K),
      S.IsSymm → S.det ≠ 0 →
      (∀ k (hk : k ≤ n), 0 < k → leadingMinor S k hk ≠ 0) →
      ∀ k (hk : k ≤ n), 0 < k →
        0 < leadingMinor S k hk /
          leadingMinor S (k - 1) ((Nat.sub_le k 1).trans hk) := by
  sorry

end OMA.S_mo_292809
