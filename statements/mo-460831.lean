import Mathlib

/-!
# $\mathscr{H}^{n-2}(\Sigma)< \infty$ implies $\mathscr{H}^{n-1}(\pi(\Sigma))=0$

Source: https://mathoverflow.net/questions/460831
Credit: @artnoage

The source: let `Σ ⊆ ℝ^(n+1)` have finite `(n-2)`-dimensional Hausdorff measure, and let
`π : ℝ^(n+1) → ℝ^n` be the projection on the first `n` coordinates. Claim (quoted from a paper,
proof asked for): `H^(n-1)(π(Σ)) = 0`.

Choices made here:

* `ℝ^k` is `EuclideanSpace ℝ (Fin k)`, with its Euclidean distance; the Hausdorff measures are
  Mathlib's `μH[d]` for that distance.
* The source does not restrict `n`. The dimension `n - 2` of a Hausdorff measure has to be
  nonnegative, so the statement is for `n ≥ 2`. The dimensions are the real numbers `n - 2` and
  `n - 1`.
* `Σ` is an arbitrary set, as in the source (no measurability assumption).
-/

namespace OMA.S_mo_460831

open MeasureTheory

/-- The projection of `ℝ^(n+1)` on its first `n` coordinates. -/
def proj (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i : Fin n => x (Fin.castSucc i))

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∀ S : Set (EuclideanSpace ℝ (Fin (n + 1))),
      μH[(n : ℝ) - 2] S < ⊤ → μH[(n : ℝ) - 1] (proj n '' S) = 0 := by
  sorry

end OMA.S_mo_460831
