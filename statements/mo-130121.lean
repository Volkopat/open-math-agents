import Mathlib

/-!
# Maximum number of vertices of a hypercube covered by a ball of radius R

Source: https://mathoverflow.net/questions/130121
Asked by MathOverflow user user21277.

Given `R > 0`, the question asks for the maximum number of vertices of the unit hypercube
`H^n ⊂ ℝ^n` that a closed ball of radius `R` can cover. The asker states the conjecture that
for any `R` an optimal ball is the one centred at `(1/2, ..., 1/2, 0, ..., 0)` whose number of
nonzero coordinates is `⌊4R^2⌋ = ⌊D^2⌋`, where `D = 2R` is the diameter (for `D^2 ≤ n`).

Translation choices.
* The vertices of `H^n` are the points of `{0,1}^n`, encoded as `v : Fin n → Bool` with the
  point `i ↦ if v i then 1 else 0`.
* A vertex lies in the closed ball of radius `R` about `c : Fin n → ℝ` when its squared
  Euclidean distance to `c` is at most `R^2`.
* `halfCenter n k` is the point whose first `k` coordinates are `1/2` and whose other
  coordinates are `0`.
* The proviso `D ≤ n` of the post is read as `D^2 = 4R^2 ≤ n`, which is exactly what is needed
  for the centre `halfCenter n ⌊4R^2⌋` to make sense; reading it as `2R ≤ n` instead would only
  enlarge the set of radii covered.
* `main` is the asker's conjecture: no closed ball of radius `R` covers more vertices than the
  ball of radius `R` about `halfCenter n ⌊4R^2⌋`.
-/

namespace OMA.S_mo_130121

/-- Squared Euclidean distance from the cube vertex `v` to the point `c`. -/
noncomputable def sqDist {n : ℕ} (v : Fin n → Bool) (c : Fin n → ℝ) : ℝ :=
  ∑ i, ((if v i then (1 : ℝ) else 0) - c i) ^ 2

/-- Number of vertices of the unit `n`-cube in the closed ball of radius `R` about `c`. -/
noncomputable def covered (n : ℕ) (c : Fin n → ℝ) (R : ℝ) : ℕ :=
  (Finset.univ.filter (fun v : Fin n → Bool => sqDist v c ≤ R ^ 2)).card

/-- The point `(1/2, ..., 1/2, 0, ..., 0)` with `k` coordinates equal to `1/2`. -/
noncomputable def halfCenter (n k : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < k then 1 / 2 else 0

theorem main :
    ∀ (n : ℕ) (R : ℝ), 0 < R → 4 * R ^ 2 ≤ n → ∀ c : Fin n → ℝ,
      covered n c R ≤ covered n (halfCenter n ⌊4 * R ^ 2⌋₊) R := by
  sorry

end OMA.S_mo_130121
