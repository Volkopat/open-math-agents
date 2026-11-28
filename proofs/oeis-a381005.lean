import OMAStatements.S_oeis_a381005

-- Credit: @oh-meh
open OMA.S_oeis_a381005

theorem OMA.solution : type_of% @OMA.S_oeis_a381005.main := by
  intro n hn
  let k := 2^(4*n-2)
  let t := 2^(2*n)
  have hk : t ≤ k := Nat.pow_le_pow_right (by decide) (by omega)
  have ht : 0 < t := by dsimp [t]; positivity
  have he : 2^(4*n) = 4*k := by
    change 2^(4*n) = 4*2^(4*n-2)
    conv_lhs => rw [show 4*n = 2+(4*n-2) by omega, pow_add]
    norm_num
  have hsum : B n + C n = 2^(4*n+1) := by
    unfold B C
    rw [pow_succ,he]
    change 4*k-k-t-1+(4*k+k+t+1) = 4*k*2
    omega
  have hodd : ¬ 2 ∣ C n := by
    have h₁ : 2 ∣ k := dvd_pow_self 2 (by omega : 4*n-2 ≠ 0)
    have h₂ : 2 ∣ t := dvd_pow_self 2 (by omega : 2*n ≠ 0)
    unfold C
    rw [he]
    change ¬ 2 ∣ 4*k+k+t+1
    omega
  by_contra h
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd h
  have hc := hd.trans (Nat.gcd_dvd_right _ (C n))
  have hb := (hd.trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_right _ (B n))
  have hd₂ := dvd_add hb hc
  rw [hsum] at hd₂
  have h₂ : p=2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd₂)
  exact hodd (h₂ ▸ hc)
