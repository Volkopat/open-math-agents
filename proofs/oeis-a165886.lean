import OMAStatements.S_oeis_a165886

/-!
Paul Curtz's conjectured ratio of consecutive normalized Hirzebruch numbers.
On incrementing the index, a prime p enters the ratio precisely when p-1
divides the new index. Legendre's formula for the binary digit sum accounts
for the valuation factor in the normalization.
-/

namespace HirzebruchRatios

open Finset OMA.S_oeis_a165886

private theorem factor_step (n p : ℕ) :
    (if p.Prime then p ^ ((n+1)/(p-1)) else 1) =
      (if p.Prime then p ^ (n/(p-1)) else 1) *
      (if p = 2 then 2 else 1) *
      (if p.Prime ∧ p ≠ 2 ∧ (p-1) ∣ n+1 then p else 1) := by
  by_cases he : p = 2
  · subst p
    simp [Nat.prime_two, pow_succ]
  by_cases hp : p.Prime
  · by_cases hd : (p-1) ∣ n+1 <;> simp [hp, he, hd, Nat.succ_div, pow_succ]
  · simp [he, hp]

private theorem hirzebruch_step (n : ℕ) :
    A091137 (n+1) = A091137 n * 2 * A141459 (n+1) := by
  have hold : (∏ p ∈ range (n+3), if p.Prime then p^(n/(p-1)) else 1) = A091137 n := by
    rw [show n+3 = (n+2)+1 by omega, prod_range_succ]
    have he : n / (n+1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [A091137, prod_filter, he]
  have htwo : (∏ p ∈ range (n+3), if p = 2 then 2 else 1) = 2 := by
    simp [show 2 < n+3 by omega]
  unfold A091137 A141459
  simp only [prod_filter]
  simp_rw [factor_step n]
  rw [prod_mul_distrib, prod_mul_distrib, htwo, hold]
  simp only [A091137, prod_filter]

private theorem binary_step (n : ℕ) :
    A001316 (n+1) * A006519 (n+1) = 2 * A001316 n := by
  have hv (m : ℕ) : padicValNat 2 m.factorial + ((2 : ℕ).digits m).sum = m := by
    have hl := sub_one_mul_padicValNat_factorial (p := 2) m
    have hd := Nat.digit_sum_le 2 m
    norm_num at hl
    omega
  have h := hv (n+1)
  rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)] at h
  have hn := hv n
  unfold A001316 A006519
  rw [← pow_add, show ((2 : ℕ).digits (n+1)).sum + padicValNat 2 (n+1) =
    ((2 : ℕ).digits n).sum + 1 by omega, pow_succ]
  omega

theorem result : type_of% @OMA.S_oeis_a165886.main := by
  intro n
  have hA : 0 < A091137 n := Finset.prod_pos fun p hp =>
    pow_pos ((mem_filter.mp hp).2.pos) _
  have hB : 0 < A141459 (n+1) := Finset.prod_pos fun p hp => (mem_filter.mp hp).2.1.pos
  have hC : 0 < A001316 n := by unfold A001316; positivity
  have hD : 0 < A006519 (n+1) := by unfold A006519; positivity
  have ha : (A091137 n : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  have hb : (A141459 (n+1) : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have hc : (A001316 n : ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  have hd : (A006519 (n+1) : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hq : (A001316 (n+1) : ℚ) = 2 * A001316 n / A006519 (n+1) := by
    apply (eq_div_iff hd).2
    exact_mod_cast binary_step n
  rw [a, A165641, A165641, hirzebruch_step, hq]
  push_cast
  field_simp

end HirzebruchRatios

theorem OMA.solution : type_of% @OMA.S_oeis_a165886.main := HirzebruchRatios.result
