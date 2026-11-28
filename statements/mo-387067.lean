import Mathlib

/-!
# On the real and finite field rank of a $0/1$ matrix - I

Source: https://mathoverflow.net/questions/387067
Credit: @zarnab222-dev

Let `M` be an `n × n` matrix with entries in `{-1, 0, +1}` and real rank `r`. The matrix `f(M)` of
size `mn × mn` replaces each `0` of `M` by the `m × m` zero block, each `+1` by the `m × m` identity
and each `-1` by the `m × m` anti-identity (ones on the anti-diagonal). First question of the post:
"Is the real rank of the new matrix `O(r)`?" The affirmative claim is stated.

Translation choices:
* `M` is a real matrix with every entry equal to `-1`, `0` or `1`; ranks are `Matrix.rank` over `ℝ`.
* `f(M)` is `blowUp m n M`, indexed by `Fin n × Fin m` (block index, position inside the block)
  instead of `Fin (m * n)`; the rank does not depend on this relabelling. Positions inside a block
  are 0-indexed, so the anti-identity has a one at `(a, b)` exactly when `a + b + 1 = m`.
* `O(r)` is the usual big-O in `r`: there are a constant `C` and a threshold `r₀` such that
  `rank f(M) ≤ C * r` whenever `r ≥ r₀`. The block size `m` is a parameter of the construction,
  so `C` and `r₀` may depend on `m` (a constant uniform in `m` is impossible for the trivial
  reason that `rank f(M) ≥ m` when `M ≠ 0`); they do not depend on `n` or on `M`.
* `m = 0` (empty blocks) is allowed and harmless: there the claim holds with `C = 0`.
* Not stated here: the same question over `𝔽₂` and the request for a precise bound.
-/

namespace OMA.S_mo_387067

/-- The block matrix `f(M)`: the block at `(i, j)` is the `m × m` identity if `M i j = 1`, the
`m × m` anti-identity if `M i j = -1`, and the zero block otherwise. -/
noncomputable def blowUp (m n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ :=
  fun p q =>
    if M p.1 q.1 = 1 then (if p.2 = q.2 then 1 else 0)
    else if M p.1 q.1 = -1 then (if (p.2 : ℕ) + (q.2 : ℕ) + 1 = m then 1 else 0)
    else 0

theorem main :
    ∀ m : ℕ, ∃ C r₀ : ℕ, ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, M i j = -1 ∨ M i j = 0 ∨ M i j = 1) →
      r₀ ≤ M.rank →
      (blowUp m n M).rank ≤ C * M.rank := by
  sorry

end OMA.S_mo_387067
