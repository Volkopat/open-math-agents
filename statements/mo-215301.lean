import Mathlib

/-!
# Integer sum of distinct reciprocals with no integer subset sum

Source: https://mathoverflow.net/questions/215301 (CC BY-SA 3.0).

Question: for any `n ∈ ℕ⁺`, is there a finite set `S ⊂ ℕ⁺` such that `∑_{k ∈ S} 1/k = n` but
`∑_{k ∈ T} 1/k ∉ ℕ⁺` for every proper subset `T ⊊ S`? The poser believes the answer is yes;
`main` states it. Sums are taken in `ℚ`.
-/

namespace OMA.S_mo_215301

theorem main : ∀ n : ℕ, 0 < n → ∃ S : Finset ℕ, (∀ k ∈ S, 0 < k) ∧
    ∑ k ∈ S, (1 / (k : ℚ)) = n ∧
    ∀ T ⊂ S, ∀ m : ℕ, 0 < m → ∑ k ∈ T, (1 / (k : ℚ)) ≠ m := by
  sorry

end OMA.S_mo_215301
