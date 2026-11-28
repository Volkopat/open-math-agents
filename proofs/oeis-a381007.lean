import OMAStatements.S_oeis_a381007

-- The sum and parity calculations are adapted from the sibling A381005 proof in PR #20766.
open OMA.S_oeis_a381007

theorem OMA.solution : type_of% @OMA.S_oeis_a381007.main := by
  intro n hn
  let k := 2^(4*n-2)
  let t := 2^(2*n)
  have hk : t ≤ k := Nat.pow_le_pow_right (by decide) (by omega)
  have ht : 0 < t := by dsimp [t]; positivity
  have he : 2^(4*n) = 4*k := by
    change 2^(4*n) = 4*2^(4*n-2)
    conv_lhs => rw [show 4*n = 2+(4*n-2) by omega, pow_add]
    norm_num
  have hsum : legB n + hyp n = 2^(4*n+1) := by
    unfold legB hyp
    rw [pow_succ,he]
    change 4*k-k-t-1+(4*k+k+t+1) = 4*k*2
    omega
  have hodd : ¬ 2 ∣ hyp n := by
    have h₁ : 2 ∣ k := dvd_pow_self 2 (by omega : 4*n-2 ≠ 0)
    have h₂ : 2 ∣ t := dvd_pow_self 2 (by omega : 2*n ≠ 0)
    unfold hyp
    rw [he]
    change ¬ 2 ∣ 4*k+k+t+1
    omega
  apply Nat.Coprime.of_dvd_left (Nat.gcd_dvd_right _ _)
  apply Nat.coprime_add_self_left.mp
  rw [hsum]
  exact Nat.Coprime.pow_left _ (Nat.prime_two.coprime_iff_not_dvd.mpr hodd)
