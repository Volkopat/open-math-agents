import OMAReductions.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H2_R1

/-! An admissible path length and a uniform lower bound on the number of disjoint
blocks obtainable from the original paths. Credit: @VestigeClub. -/

private theorem admissible_length (B : ℕ) (hB : 3475 ≤ B) :
    ∃ k, k ≤ B ∧ B < k + 8340 ∧ k % 12 = 7 ∧ 695 ∣ k :=
  ⟨3475 + 8340 * ((B - 3475) / 8340), by omega, by omega, by omega,
    ⟨5 + 12 * ((B - 3475) / 8340), by ring⟩⟩

private theorem capacity {n L k : ℕ} (hL : 0 < L) (hk : 0 < k)
    (hsize : 800*L ≤ n) (hfit : k ≤ L) :
    n/(6400*k) ≤ (n/(800*L))*((L+1)/(k+1)) := by
  let m := n/(800*L)
  let q := (L+1)/(k+1)
  have hm : 1 ≤ m := Nat.div_pos hsize (by positivity)
  have hq : 1 ≤ q := Nat.div_pos (by omega) (by omega)
  have hm' : n < 800*L*(m+1) := Nat.lt_mul_div_succ _ (by positivity)
  have hq' : L+1 < (k+1)*(q+1) := Nat.lt_mul_div_succ _ (by omega)
  have hm2 : n ≤ 1600*L*m := calc
    n ≤ 800*L*(m+1) := hm'.le
    _ ≤ 800*L*(2*m) := Nat.mul_le_mul_left _ (by omega)
    _ = 1600*L*m := by ring
  have hl4 : L ≤ 4*k*q := calc
    L ≤ (k+1)*(q+1) := by omega
    _ ≤ (2*k)*(2*q) := Nat.mul_le_mul (by omega) (by omega)
    _ = 4*k*q := by ring
  apply Nat.div_le_of_le_mul
  calc
    n ≤ 1600*L*m := hm2
    _ ≤ 1600*(4*k*q)*m := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hl4)
    _ = 6400*k*(m*q) := by ring

theorem OMA.solution : OMA.R_Arxiv_2001_02665_kotzig_conjecture_large_R1_H2_R1.H1 := by
  filter_upwards [Filter.eventually_ge_atTop (2^625)] with n hn
  dsimp only
  let e := Nat.sqrt (Nat.log 2 n)
  let L := 2^e
  have ht : 625 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) hn
  have he : 25 ≤ e := Nat.le_sqrt.mpr (by omega)
  have hh : e*e ≤ Nat.log 2 n := Nat.sqrt_le _
  have he10 : e+10 ≤ Nat.log 2 n := by nlinarith
  have hnpos : n ≠ 0 := (lt_of_lt_of_le (pow_pos (by decide : (0:ℕ)<2) 625) hn).ne'
  have hsize : 800*L ≤ n := calc
    800*L ≤ 2^10*L := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(e+10) := by simp [L,pow_add,mul_comm]
    _ ≤ 2^Nat.log 2 n := Nat.pow_le_pow_right (by decide) he10
    _ ≤ n := Nat.pow_log_le_self _ hnpos
  have hL : 2^25 ≤ L := Nat.pow_le_pow_right (by decide) he
  have enough : 3475 ≤ Nat.sqrt L := Nat.le_sqrt.mpr (by omega)
  obtain ⟨k,hk,close,res,dvd⟩ := admissible_length _ enough
  have pos : 0 < k := by omega
  have fit : k ≤ L := hk.trans (Nat.sqrt_le_self _)
  exact ⟨k,pos,hk,close,res,dvd,capacity (by positivity) pos hsize fit⟩
