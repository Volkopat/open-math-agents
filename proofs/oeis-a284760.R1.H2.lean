import OMAReductions.R_oeis_a284760_R1

open Finset

namespace OMA.A284760H2

lemma sum_pairs_mod_two (e : ℕ) (he : 0 < e) (m : ℕ) :
    (∑ i ∈ range (2 * m), i ^ e) ≡ m [MOD 2] := by
  induction m with
  | zero => simp [Nat.ModEq]
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, sum_range_succ, sum_range_succ]
      have h₀ : 2 * m ≡ 0 [MOD 2] := by unfold Nat.ModEq; omega
      have h₁ : 2 * m + 1 ≡ 1 [MOD 2] := by unfold Nat.ModEq; omega
      simpa [zero_pow (Nat.ne_of_gt he)] using (ih.add (h₀.pow e)).add (h₁.pow e)

lemma shifted_even_power (i t k : ℕ) :
    (2 * t + i) ^ (2 * k) ≡ i ^ (2 * k) [MOD 2 * (2 * t)] := by
  have h : (2 * (2 * t)) * (i + t) ≡ 0 [MOD 2 * (2 * t)] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
  have hsq : (2 * t + i) ^ 2 ≡ i ^ 2 [MOD 2 * (2 * t)] := by
    calc
      (2 * t + i) ^ 2 = i ^ 2 + (2 * (2 * t)) * (i + t) := by ring
      _ ≡ i ^ 2 [MOD 2 * (2 * t)] := by
        simpa only [add_zero] using (Nat.ModEq.refl (i ^ 2)).add h
  rw [pow_mul, pow_mul]
  exact hsq.pow k

lemma even_power_sum_not_dvd (k : ℕ) (hk : 0 < k) (n : ℕ)
    (hn : 0 < n) (he : 2 ∣ n) :
    ¬ n ∣ ∑ i ∈ range n, i ^ (2 * k) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨m, rfl⟩ := he
      intro hdiv
      by_cases hm : 2 ∣ m
      · obtain ⟨t, rfl⟩ := hm
        have hsum : (∑ i ∈ range (2 * (2 * t)), i ^ (2 * k)) ≡
            2 * (∑ i ∈ range (2 * t), i ^ (2 * k)) [MOD 2 * (2 * t)] := by
          conv_lhs => rw [two_mul (2 * t), sum_range_add]
          conv_rhs => rw [two_mul]
          exact (Nat.ModEq.refl (∑ i ∈ range (2 * t), i ^ (2 * k))).add (Nat.ModEq.sum (s := range (2 * t)) fun i _ => shifted_even_power i t k)
        have hsmall : (2 * t) ∣ ∑ i ∈ range (2 * t), i ^ (2 * k) :=
          (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp
            (Nat.modEq_zero_iff_dvd.mp (hsum.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdiv)))
        exact ih (2 * t) (by omega) (by omega) (dvd_mul_right _ _) hsmall
      · have htwo : 2 ∣ ∑ i ∈ range (2 * m), i ^ (2 * k) :=
          (dvd_mul_right 2 m).trans hdiv
        exact hm (Nat.modEq_zero_iff_dvd.mp
          ((sum_pairs_mod_two (2 * k) (by omega) m).symm.trans
            (Nat.modEq_zero_iff_dvd.mpr htwo)))

end OMA.A284760H2

theorem OMA.solution : OMA.R_oeis_a284760_R1.H2 := by
  intro n hn hfour hz
  have he : 2 ∣ n := (by decide : 2 ∣ 4).trans hfour
  let k := (n - 2) / 2
  have hk : 0 < k := by
    dsimp [k]
    omega
  have hexp : n - 2 = 2 * k := by
    dsimp [k]
    omega
  have hdiv : n ∣ ∑ i ∈ Ico 1 n, i ^ (n - 2) :=
    (dvd_pow_self n (by decide : 4 ≠ 0)).trans (Nat.dvd_of_mod_eq_zero hz)
  apply OMA.A284760H2.even_power_sum_not_dvd k hk n hn he
  rw [← hexp]
  rwa [sum_range_eq_add_Ico _ (by omega : 1 ≤ n),
    zero_pow (by omega : n - 2 ≠ 0), zero_add]
