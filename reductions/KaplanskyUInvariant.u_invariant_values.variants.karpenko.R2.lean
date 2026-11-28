import FormalConjectures.Paper.KaplanskyUInvariant

namespace OMA.R_KaplanskyUInvariant_u_invariant_values_variants_karpenko_R2

open KaplanskyUInvariant

/-- Passing from a witness field to its Laurent series field doubles the invariant.
    See `ku_step` in the external formal proof linked from the upstream powers-of-two theorem. -/
def H1 : Prop := ∀ m : ℕ, IsUInvariant m → IsUInvariant (2 * m)

/-- Even seeds whose halves are excluded from Karpenko's theorem. All other even
    dimensions can be obtained by doubling an admissible smaller dimension. -/
def H2 : Prop := ∀ m : ℕ, 0 < m →
    ((∃ r : ℕ, 2 ^ r = m + 1) ∨ (∃ r : ℕ, 2 ^ r = m + 3)) → IsUInvariant (2 * m)

/-- The odd dimensions allowed by Karpenko's two exclusions. -/
def H3 : Prop := ∀ n : ℕ, Odd n →
    (∀ r : ℕ, 2 ^ r ≠ n + 1) → (∀ r : ℕ, 2 ^ r ≠ n + 3) → IsUInvariant n

theorem main : H1 → H2 → H3 → type_of% @KaplanskyUInvariant.u_invariant_values.variants.karpenko := by
  intro double seeds odd_case n
  refine Nat.strongRecOn (motive := fun n =>
    (∀ r : ℕ, 2 ^ r ≠ n + 1) → (∀ r : ℕ, 2 ^ r ≠ n + 3) → IsUInvariant n) n ?_
  intro n ih hn1 hn3
  by_cases heven : n % 2 = 0
  · let m := n / 2
    have he : n = 2 * m := by dsimp [m]; omega
    have hn : n ≠ 0 := fun h => hn1 0 (by simp [h])
    have hm : 0 < m := by omega
    rw [he]
    by_cases h1 : ∃ r : ℕ, 2 ^ r = m + 1
    · exact seeds m hm (Or.inl h1)
    by_cases h3 : ∃ r : ℕ, 2 ^ r = m + 3
    · exact seeds m hm (Or.inr h3)
    exact double m (ih m (by omega) (fun r hr => h1 ⟨r, hr⟩) (fun r hr => h3 ⟨r, hr⟩))
  · exact odd_case n ⟨n / 2, by omega⟩ hn1 hn3

end OMA.R_KaplanskyUInvariant_u_invariant_values_variants_karpenko_R2
