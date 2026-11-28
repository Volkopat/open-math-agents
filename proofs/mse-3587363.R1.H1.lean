import OMAReductions.R_mse_3587363_R1

/-!
# Proof of `mse-3587363.R1.H1`

If `p` is prime with `2 * p ≤ n`, then both `2 * p` and `p` divide `n!`, so `p ^ 2 ∣ n!`.
Combined with `p ∣ k` and `n! + k = a ^ b` (`b ≥ 2`), we get `p ∣ a ^ b`, hence `p ∣ a` and
`p ^ 2 ∣ a ^ b = n! + k`, forcing `p ^ 2 ∣ k`, contradicting `¬ p ^ 2 ∣ k`.
-/

theorem OMA.solution : OMA.R_mse_3587363_R1.H1 := by
  intro n k a b p hb heq hp hpk hnp2 h2p
  have hp2_ge : 2 ≤ p := hp.two_le
  have h2p_pos : 0 < 2 * p := by omega
  have hp_dvd_pred : p ∣ (2 * p - 1).factorial :=
    Nat.dvd_factorial hp.pos (by omega)
  have hp2_dvd_2pfac : p ^ 2 ∣ (2 * p).factorial := by
    have hmul : (2 * p).factorial = (2 * p) * (2 * p - 1).factorial := by
      have := Nat.mul_factorial_pred h2p_pos.ne'
      exact this.symm
    rw [hmul, sq]
    exact mul_dvd_mul (dvd_mul_left p 2) hp_dvd_pred
  have hp2_dvd_nfac : p ^ 2 ∣ n.factorial :=
    hp2_dvd_2pfac.trans (Nat.factorial_dvd_factorial h2p)
  have hp_dvd_nfac : p ∣ n.factorial :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hp2_dvd_nfac
  have hp_dvd_ab : p ∣ a ^ b := by
    rw [← heq]
    exact dvd_add hp_dvd_nfac hpk
  have hp_dvd_a : p ∣ a := hp.dvd_of_dvd_pow hp_dvd_ab
  have hp2_dvd_ab : p ^ 2 ∣ a ^ b :=
    (Nat.pow_dvd_pow p hb).trans (pow_dvd_pow_of_dvd hp_dvd_a b)
  rw [← heq] at hp2_dvd_ab
  have hp2_dvd_k : p ^ 2 ∣ k := (Nat.dvd_add_right hp2_dvd_nfac).mp hp2_dvd_ab
  exact hnp2 hp2_dvd_k
