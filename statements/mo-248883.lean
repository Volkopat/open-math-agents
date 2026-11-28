import Mathlib

/-!
# Commutativity in permutation group

Source: https://mathoverflow.net/questions/248883
Credit: @zarnab222-dev

The question: let `G = S_n` with `7 ≤ n ≤ 10`, and let `H₁, H₂` be subgroups of `G` with `H₁` isomorphic to
`S_k`, `H₂` isomorphic to `S_{n-k}`, and every element of `H₁` commuting with every element of `H₂`. Is it true
that `H₁, H₂` are the stabilizers of `n - k` and `k` letters respectively? We state the affirmative claim.

Translation choices. `S_m` is `Equiv.Perm (Fin m)`, so `G = Equiv.Perm (Fin n)`. The source does not give a
range for `k`; we quantify over all `k ≤ n`, the range in which `S_k` and `S_{n-k}` both make sense (so the
truncated subtraction `n - k` is the true difference). Isomorphic means there is a group isomorphism (`≃*`).
The stabilizer of `m` letters is read as the pointwise stabilizer of a set of `m` letters: the subgroup of all
permutations fixing each letter of some `S` with `S.card = m` (this is the only reading under which the
stabilizer is isomorphic to a symmetric group on the remaining letters). The two sets of letters are not
required to be complementary, since the source does not say so; this only weakens the claim.
-/

namespace OMA.S_mo_248883

theorem main : ∀ n : ℕ, 7 ≤ n → n ≤ 10 → ∀ k : ℕ, k ≤ n →
    ∀ H₁ H₂ : Subgroup (Equiv.Perm (Fin n)),
      Nonempty (H₁ ≃* Equiv.Perm (Fin k)) →
      Nonempty (H₂ ≃* Equiv.Perm (Fin (n - k))) →
      (∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) →
      (∃ S : Finset (Fin n), S.card = n - k ∧
        ∀ g : Equiv.Perm (Fin n), g ∈ H₁ ↔ ∀ x ∈ S, g x = x) ∧
      (∃ T : Finset (Fin n), T.card = k ∧
        ∀ g : Equiv.Perm (Fin n), g ∈ H₂ ↔ ∀ x ∈ T, g x = x) := by
  sorry

end OMA.S_mo_248883
