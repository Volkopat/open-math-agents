import FormalConjectures.ErdosProblems.«647»

namespace OMA.R_Erdos647_erdos_647_R2

open ArithmeticFunction.sigma

def H1 : Prop := ∀ m : ℕ, (σ 0 m) ^ 8 ≤ 45197 ^ 8 * m

def H2 : Prop :=
  ∀ t k : ℕ, 0 < t →
    k ∈ ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24} : Finset ℕ) →
    Nat.Prime ((720720 / k) * t - 1) →
    σ 0 (720720 * t - k) ≤ k + 2

def H3 : Prop :=
  ∃ t : ℕ, 0 < t ∧
    (∀ k ∈ ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24} : Finset ℕ),
      Nat.Prime ((720720 / k) * t - 1)) ∧
    (∀ k : ℕ, 0 < k → k ≤ 720720 * t →
      k ∉ ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24} : Finset ℕ) →
      (k + 3) ^ 8 ≤ 45197 ^ 8 * (720720 * t - k) →
      σ 0 (720720 * t - k) ≤ k + 2)

theorem main : H1 → H2 → H3 → type_of% @Erdos647.erdos_647 := by
  intro hbound hforced hwindow
  obtain ⟨t, ht, hprimes, hrest⟩ := hwindow
  have hn : 24 < 720720 * t := by omega
  letI : Nonempty (Fin (720720 * t)) := ⟨⟨0, by omega⟩⟩
  refine ⟨720720 * t, hn, ciSup_le ?_⟩
  intro m
  change (m : ℕ) + σ 0 (m : ℕ) ≤ 720720 * t + 2
  have hm := m.isLt
  let k := 720720 * t - (m : ℕ)
  have hk : 0 < k := Nat.sub_pos_of_lt hm
  have hkn : k ≤ 720720 * t := Nat.sub_le _ _
  have hback : 720720 * t - k = (m : ℕ) := by dsimp [k]; omega
  by_cases hkS : k ∈ ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24} : Finset ℕ)
  · have hsmall := hforced t k ht hkS (hprimes k hkS)
    rw [hback] at hsmall
    dsimp [k] at hsmall
    omega
  · by_contra! hfail
    have hlarge : k + 3 ≤ σ 0 (m : ℕ) := by dsimp [k]; omega
    have hcut : (k + 3) ^ 8 ≤ 45197 ^ 8 * (m : ℕ) :=
      (Nat.pow_le_pow_left hlarge 8).trans (hbound (m : ℕ))
    have hsmall := hrest k hk hkn hkS (by simpa only [hback] using hcut)
    rw [hback] at hsmall
    omega

end OMA.R_Erdos647_erdos_647_R2
