import Mathlib

/-!
# A Gamma ratio, a weighted geometric mean, and their proposed asymptotic relation

Barackouda asks both for an upper bound and whether the additive difference
between its right and left sides tends to zero for each fixed integer n ≥ 3.
The exponent of each factor x+j is its own value.
Source: https://math.stackexchange.com/questions/3709724
Credit: @connoranderson
-/

namespace OMA.S_mse_3709724

noncomputable def weightSum (n : ℕ) (x : ℝ) : ℝ :=
  n*x + (n:ℝ)*(n-1)/2

noncomputable def upper (n : ℕ) (x : ℝ) : ℝ :=
  (weightSum n x / (n/2 : ℝ) -
    (∏ j ∈ Finset.range n, (x+j) ^ (x+j : ℝ)) ^ (1 / weightSum n x)) ^ n

theorem main :
    (∀ n : ℕ, 3 ≤ n → ∀ x : ℝ, 1 ≤ x → Real.Gamma (x+n) / Real.Gamma x ≤ upper n x) ∧
    (∀ n : ℕ, 3 ≤ n → Filter.Tendsto
      (fun x : ℝ => upper n x - Real.Gamma (x+n) / Real.Gamma x)
      Filter.atTop (nhds 0)) := by
  sorry

end OMA.S_mse_3709724
