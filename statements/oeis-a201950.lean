import Mathlib

namespace OMA.S_oeis_a201950

open Polynomial BigOperators

/-- OEIS A201950: central coefficient `[X^n]` of `∏_{k=0}^{n-1} (1 + k * X + X^2)`. -/
noncomputable def a201950 (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.range n, (1 + Polynomial.C k * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ)).coeff n

/-- Number of left-to-right maxima of a permutation `σ` of `Fin m`:
positions `i : Fin m` such that `σ j < σ i` for all `j < i`. -/
def lrMaxCount {m : ℕ} (σ : Equiv.Perm (Fin m)) : ℕ :=
  (Finset.univ.filter fun i : Fin m => ∀ j : Fin m, j < i → σ j < σ i).card

/-- Number of right-to-left maxima of a permutation `σ` of `Fin m`:
positions `i : Fin m` such that `σ j < σ i` for all `j > i`. -/
def rlMaxCount {m : ℕ} (σ : Equiv.Perm (Fin m)) : ℕ :=
  (Finset.univ.filter fun i : Fin m => ∀ j : Fin m, i < j → σ j < σ i).card

/-- Conjecture on OEIS A201950:
for every `n : ℕ`, `a201950 n` equals the number of permutations of `Fin (n + 1)`
in which the number of left-to-right maxima equals the number of right-to-left maxima. -/
theorem main :
    ∀ n : ℕ,
      a201950 n =
        (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) =>
          lrMaxCount σ = rlMaxCount σ).card := by
  sorry

end OMA.S_oeis_a201950
