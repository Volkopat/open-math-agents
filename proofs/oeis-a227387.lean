import OMAStatements.S_oeis_a227387

open scoped ArithmeticFunction.sigma
open ArithmeticFunction Finset

namespace NeighborDivisors

private def powers : Finset (ℕ × ℕ) :=
  {(2,6), (3,4), (5,3), (7,3), (11,2), (13,2), (17,2), (19,2),
   (23,1), (29,1), (31,1), (37,1), (41,1), (43,1), (47,1)}

private def M : ℕ := ∏ pe ∈ powers, pe.1 ^ pe.2

private theorem abundant : 7 * M < σ 1 M := by
  have hprime : ∀ pe ∈ powers, Nat.Prime pe.1 := by decide +kernel
  have hcop : ∀ pe ∈ powers, ∀ qe ∈ powers, pe ≠ qe →
      Nat.Coprime (pe.1 ^ pe.2) (qe.1 ^ qe.2) := by decide +kernel
  unfold M
  rw [isMultiplicative_sigma.map_prod (fun pe : ℕ × ℕ => pe.1 ^ pe.2) powers
    (fun pe hp qe hq hne => hcop pe hp qe hq hne)]
  have heq : (∏ pe ∈ powers, σ 1 (pe.1 ^ pe.2)) =
      ∏ pe ∈ powers, ∑ j ∈ range (pe.2 + 1), pe.1 ^ j :=
    prod_congr rfl fun pe hp => sigma_one_apply_prime_pow (hprime pe hp)
  rw [heq]
  decide +kernel

private theorem sigma_multiple {m t : ℕ} (hmt : m*t ≠ 0) :
    t * σ 1 m ≤ σ 1 (m*t) := by
  rw [sigma_eq_sum_div, sigma_eq_sum_div]
  simp only [pow_one]
  calc
    _ = ∑ d ∈ m.divisors, (m*t)/d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [mul_comm m t, Nat.mul_div_assoc _ (Nat.dvd_of_mem_divisors hd)]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset
      intro d hd
      exact Nat.mem_divisors.2 ⟨(Nat.dvd_of_mem_divisors hd).trans (dvd_mul_right m t), hmt⟩

theorem result : type_of% @OMA.S_oeis_a227387.main := by
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  have hm : M ≠ 0 := by decide +kernel
  have hcop : (M-1).Coprime M := by decide +kernel
  obtain ⟨p, hgt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq N hm hcop
  have hadd : M-1+1 = M := Nat.sub_add_cancel (by omega)
  have hcong : p+1 ≡ M [MOD M] := hadd ▸ hmod.add (Nat.ModEq.refl 1)
  have hdvd : M ∣ p+1 := Nat.modEq_zero_iff_dvd.mp
    (hcong.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
  obtain ⟨t, ht⟩ := hdvd
  have htp : 0 < t := by
    by_contra! h
    rw [show t = 0 by omega, mul_zero] at ht
    omega
  have hmt : M*t ≠ 0 := mul_ne_zero hm htp.ne'
  have hlt : 7*(p+1) < σ 1 (p+1) := calc
    _ = t * (7*M) := by rw [ht]; ring
    _ < t * σ 1 M := Nat.mul_lt_mul_of_pos_left abundant htp
    _ ≤ _ := by rw [ht]; exact sigma_multiple hmt
  have hsig : σ 1 p = p+1 := by
    rw [sigma_one_apply, hp.divisors, sum_pair hp.ne_one.symm]
    exact Nat.add_comm _ _
  refine ⟨p, ?_, hgt⟩
  change 2 ≤ p ∧ σ 1 p * 7 < σ 1 (p-1) + σ 1 (p+1)
  rw [hsig]
  exact ⟨hp.two_le, by omega⟩

end NeighborDivisors

theorem OMA.solution : type_of% @OMA.S_oeis_a227387.main := NeighborDivisors.result