import Mathlib

/-!
# Erdős Problem 612 (odd clique case)

Source: https://www.erdosproblems.com/612
Credit: @shc261392

Erdős, Pach, Pollack and Tuza asked: let `G` be a connected graph with `n` vertices, minimum
degree `d` and diameter `D`. If `G` contains no `K_{2r}` and `(r-1)(3r+2) ∣ d` then
`D ≤ 2(r-1)(3r+2)/(2r^2-1) · n/d + O(1)`, and if `G` contains no `K_{2r+1}` and `3r-1 ∣ d`
then `D ≤ (3r-1)/r · n/d + O(1)`.

The first (even) part was disproved by Czabarka, Singgih and Székely for every `r ≥ 2`. The
second (odd) part agrees with their amended conjecture `D ≤ (3 - 2/k) n/d + O(1)` for
`K_{k+1}`-free graphs at `k = 2r`, and is the part stated here. The case `r = 1` is proved in
the original paper.

Reading used here: for fixed `r ≥ 1` and fixed `d` with `3r - 1 ∣ d`, there is a constant `C`
(depending on `r` and `d`, not on `n`) such that every connected `K_{2r+1}`-free graph on `n`
vertices with minimum degree `d` has diameter at most `(3r-1)/r · n/d + C`.
-/

namespace OMA.S_erdos_612

theorem main :
    ∀ r : ℕ, 1 ≤ r → ∀ d : ℕ, (3 * r - 1) ∣ d → ∃ C : ℝ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → G.CliqueFree (2 * r + 1) → G.minDegree = d →
          (G.diam : ℝ) ≤ ((3 * r - 1 : ℝ) / r) * ((n : ℝ) / d) + C := by
  sorry

end OMA.S_erdos_612
