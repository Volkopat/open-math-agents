import OMAReductions.R_Erdos647_erdos_647_R2

open ArithmeticFunction.sigma

namespace OMA.Erdos647R2H2

lemma card_mul_prime (k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hpk : k < p) :
    ArithmeticFunction.sigma 0 (k * p) = 2 * ArithmeticFunction.sigma 0 k := by
  have hcop : Nat.Coprime k p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    exact absurd (Nat.le_of_dvd hk h) (by omega)
  have h2 : ArithmeticFunction.sigma 0 p = 2 := by
    simpa using ArithmeticFunction.sigma_zero_apply_prime_pow hp (i := 1)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, h2, mul_comm]

end OMA.Erdos647R2H2

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R2.H2 := by
  intro t k ht hk hp
  have hk' : (∃ c, 720720 = k * c ∧ 30030 ≤ c) ∧ 0 < k ∧ k ≤ 24 ∧
      2 * ArithmeticFunction.sigma 0 k ≤ k + 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    refine ⟨⟨720720 / k, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  obtain ⟨⟨c, hc, hc30⟩, hkpos, hk24, hsig⟩ := hk'
  have hc' : 720720 / k = c := by rw [hc, Nat.mul_div_cancel_left _ hkpos]
  rw [hc'] at hp
  have hct : 30030 ≤ c * t := le_trans hc30 (Nat.le_mul_of_pos_right _ ht)
  have hpk : k < c * t - 1 := by omega
  have heq : 720720 * t - k = k * (c * t - 1) := by
    rw [Nat.mul_sub, mul_one, hc, mul_assoc]
  rw [heq, OMA.Erdos647R2H2.card_mul_prime k _ hkpos hp hpk]
  exact hsig
