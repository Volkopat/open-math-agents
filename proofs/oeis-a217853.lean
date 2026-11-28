import OMAStatements.S_oeis_a217853

/-!
# Proof of the A217853 conjecture (Cipolla 1904)

For every prime p >= 5, (3^(2p) - 1)/8 = ((3^p - 1)/2) * ((3^p + 1)/4) is a Fermat pseudoprime to
base 3; with p = 2k + 1 this is (3^(4k+2) - 1)/8. The Cipolla lemma is a copy of the non-exported
Mathlib lemma Nat.psp_from_prime_psp (Mathlib/NumberTheory/FermatPsp.lean, by Niels Voss).
-/

namespace OMA.P_oeis_a217853

theorem a_id_helper' {a b : ℕ} (ha : 2 ≤ a) (hb : 2 < b) : b < (a ^ b - 1) / (a - 1) := by
  rw [← Nat.geomSum_eq ha]
  calc
    b = ∑ _ ∈ Finset.range b, (1 : ℕ) := by simp
    _ < _ := by
      refine Finset.sum_lt_sum (fun i hi => Nat.one_le_pow _ _ (by lia)) ?_
      exact ⟨1, Finset.mem_range.mpr (by lia), by simpa using! ha⟩

theorem b_id_helper' {a b : ℕ} (ha : 2 ≤ a) (hb : 2 < b) : 2 ≤ (a ^ b + 1) / (a + 1) := by
  rw [Nat.le_div_iff_mul_le (Nat.zero_lt_succ _)]
  apply Nat.succ_le_succ
  calc
    2 * a + 1 ≤ a ^ 2 * a := by nlinarith
    _ = a ^ 3 := by rw [Nat.pow_succ a 2]
    _ ≤ a ^ b := pow_right_mono₀ (Nat.le_of_succ_le ha) hb

theorem AB_id_helper' (b p : ℕ) (_ : 2 ≤ b) (hp : Odd p) :
    (b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1)) = (b ^ (2 * p) - 1) / (b ^ 2 - 1) := by
  have q₁ : b - 1 ∣ b ^ p - 1 := by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow b 1 p
  have q₂ : b + 1 ∣ b ^ p + 1 := by simpa only [one_pow] using hp.nat_add_dvd_pow_add_pow b 1
  convert! Nat.div_mul_div_comm q₁ q₂ using 2 <;> rw [mul_comm (_ - 1), ← Nat.sq_sub_sq]
  ring_nf

theorem bp_helper' {b p : ℕ} (hb : 0 < b) (hp : 1 ≤ p) :
    b ^ (2 * p) - 1 - (b ^ 2 - 1) = b * (b ^ (p - 1) - 1) * (b ^ p + b) :=
  have hi_bsquared : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  calc
    b ^ (2 * p) - 1 - (b ^ 2 - 1) = b ^ (2 * p) - (1 + (b ^ 2 - 1)) := by rw [Nat.sub_sub]
    _ = b ^ (2 * p) - (1 + b ^ 2 - 1) := by rw [Nat.add_sub_assoc hi_bsquared]
    _ = b ^ (2 * p) - b ^ 2 := by rw [Nat.add_sub_cancel_left]
    _ = b ^ (p * 2) - b ^ 2 := by rw [mul_comm]
    _ = (b ^ p) ^ 2 - b ^ 2 := by rw [pow_mul]
    _ = (b ^ p + b) * (b ^ p - b) := by rw [Nat.sq_sub_sq]
    _ = (b ^ p - b) * (b ^ p + b) := by rw [mul_comm]
    _ = (b ^ (p - 1 + 1) - b) * (b ^ p + b) := by rw [Nat.sub_add_cancel hp]
    _ = (b * b ^ (p - 1) - b) * (b ^ p + b) := by rw [pow_succ']
    _ = (b * b ^ (p - 1) - b * 1) * (b ^ p + b) := by rw [mul_one]
    _ = b * (b ^ (p - 1) - 1) * (b ^ p + b) := by rw [Nat.mul_sub_left_distrib]

/-- Cipolla's construction (copied from the Mathlib lemma `Nat.psp_from_prime_psp`). -/
theorem cipolla {b : ℕ} (b_ge_two : 2 ≤ b) {p : ℕ} (p_prime : p.Prime)
    (p_gt_two : 2 < p) (not_dvd : ¬p ∣ b * (b ^ 2 - 1)) :
    Nat.FermatPsp ((b ^ p - 1) / (b - 1) * ((b ^ p + 1) / (b + 1))) b := by
  set A := (b ^ p - 1) / (b - 1)
  set B := (b ^ p + 1) / (b + 1)
  have hA : p < A := a_id_helper' b_ge_two p_gt_two
  have hi_A : 1 < A := by lia
  have hi_B : 1 < B := b_id_helper' b_ge_two p_gt_two
  have hi_b : 0 < b := by lia
  have hi_bsquared : 0 < b ^ 2 - 1 := by
    have := Nat.pow_le_pow_left b_ge_two 2
    lia
  have hi_bpowtwop : 1 ≤ b ^ (2 * p) := Nat.one_le_pow (2 * p) b hi_b
  have p_odd : Odd p := p_prime.odd_of_ne_two p_gt_two.ne.symm
  have AB_not_prime : ¬Nat.Prime (A * B) := Nat.not_prime_mul hi_A.ne' hi_B.ne'
  have AB_id : A * B = (b ^ (2 * p) - 1) / (b ^ 2 - 1) := AB_id_helper' _ _ b_ge_two p_odd
  have hd : b ^ 2 - 1 ∣ b ^ (2 * p) - 1 := by
    simpa only [one_pow, pow_mul] using Nat.sub_dvd_pow_sub_pow _ 1 p
  refine ⟨?_, AB_not_prime, one_lt_mul'' hi_A hi_B⟩
  have ha₁ : (b ^ 2 - 1) * (A * B - 1) = b * (b ^ (p - 1) - 1) * (b ^ p + b) := by
    apply_fun fun x => x * (b ^ 2 - 1) at AB_id
    rw [Nat.div_mul_cancel hd] at AB_id
    apply_fun fun x => x - (b ^ 2 - 1) at AB_id
    nth_rw 2 [← one_mul (b ^ 2 - 1)] at AB_id
    rw [← Nat.mul_sub_right_distrib, mul_comm] at AB_id
    rw [AB_id]
    exact bp_helper' hi_b (by grind)
  have ha₂ : 2 ∣ b ^ p + b := by
    rw [← even_iff_two_dvd, Nat.even_add, Nat.even_pow' p_prime.ne_zero]
  have ha₃ : p ∣ b ^ (p - 1) - 1 := by
    have : ¬p ∣ b := mt (fun h : p ∣ b => dvd_mul_of_dvd_left h _) not_dvd
    have : p.Coprime b := Or.resolve_right (Nat.coprime_or_dvd_of_prime p_prime b) this
    have : IsCoprime (b : ℤ) ↑p := this.symm.isCoprime
    have : ↑b ^ (p - 1) ≡ 1 [ZMOD ↑p] := Int.ModEq.pow_card_sub_one_eq_one p_prime this
    have h2 : (p : ℤ) ∣ (b : ℤ) ^ (p - 1) - 1 := Int.ModEq.dvd (Int.ModEq.symm this)
    have h1 : 1 ≤ b ^ (p - 1) := Nat.one_le_pow _ _ hi_b
    have h3 : (p : ℤ) ∣ ((b ^ (p - 1) - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h1]
      push_cast
      exact h2
    exact Int.natCast_dvd_natCast.mp h3
  have ha₄ : b ^ 2 - 1 ∣ b ^ (p - 1) - 1 := by
    obtain ⟨k, hk⟩ := p_odd
    have : 2 ∣ p - 1 := ⟨k, by simp [hk]⟩
    obtain ⟨c, hc⟩ := this
    have : b ^ 2 - 1 ∣ (b ^ 2) ^ c - 1 := by
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow _ 1 c
    have : b ^ 2 - 1 ∣ b ^ (2 * c) - 1 := by rwa [← pow_mul] at this
    rwa [← hc] at this
  have ha₅ : 2 * p * (b ^ 2 - 1) ∣ (b ^ 2 - 1) * (A * B - 1) := by
    suffices q : 2 * p * (b ^ 2 - 1) ∣ b * (b ^ (p - 1) - 1) * (b ^ p + b) by rwa [ha₁]
    have q₁ : Nat.Coprime p (b ^ 2 - 1) :=
      haveI q₂ : ¬p ∣ b ^ 2 - 1 := by
        rw [mul_comm] at not_dvd
        exact mt (fun h : p ∣ b ^ 2 - 1 => dvd_mul_of_dvd_left h _) not_dvd
      (Nat.Prime.coprime_iff_not_dvd p_prime).mpr q₂
    have q₂ : p * (b ^ 2 - 1) ∣ b ^ (p - 1) - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd q₁ ha₃ ha₄
    have q₃ : p * (b ^ 2 - 1) * 2 ∣ (b ^ (p - 1) - 1) * (b ^ p + b) := mul_dvd_mul q₂ ha₂
    have q₄ : p * (b ^ 2 - 1) * 2 ∣ b * ((b ^ (p - 1) - 1) * (b ^ p + b)) :=
      dvd_mul_of_dvd_right q₃ _
    rwa [mul_assoc, mul_comm, mul_assoc b]
  have ha₆ : 2 * p ∣ A * B - 1 := by
    rw [mul_comm] at ha₅
    exact Nat.dvd_of_mul_dvd_mul_left hi_bsquared ha₅
  have ha₇ : A * B ∣ b ^ (2 * p) - 1 := by
    use b ^ 2 - 1
    have : A * B * (b ^ 2 - 1) = (b ^ (2 * p) - 1) / (b ^ 2 - 1) * (b ^ 2 - 1) :=
      congr_arg (fun x : ℕ => x * (b ^ 2 - 1)) AB_id
    simpa only [add_comm, Nat.div_mul_cancel hd, Nat.sub_add_cancel hi_bpowtwop] using this.symm
  obtain ⟨q, hq⟩ := ha₆
  have ha₈ : b ^ (2 * p) - 1 ∣ b ^ (A * B - 1) - 1 := by
    simpa only [one_pow, pow_mul, hq] using Nat.sub_dvd_pow_sub_pow _ 1 q
  exact dvd_trans ha₇ ha₈

theorem psp3 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : Nat.FermatPsp ((3 ^ (2 * p) - 1) / 8) 3 := by
  have hnd : ¬p ∣ 3 * (3 ^ 2 - 1) := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases p <;> (revert hp h; norm_num)
  have h := cipolla (b := 3) (by norm_num) hp (by lia) hnd
  rwa [AB_id_helper' 3 p (by norm_num) (hp.odd_of_ne_two (by lia))] at h

theorem infinite_k : {k : ℕ | Nat.FermatPsp ((3 ^ (4 * k + 2) - 1) / 8) 3}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (2 * B + 5)
  have hodd : Odd p := hp.odd_of_ne_two (by lia)
  obtain ⟨k, hk⟩ := hodd
  have hmem : k ∈ {k : ℕ | Nat.FermatPsp ((3 ^ (4 * k + 2) - 1) / 8) 3} := by
    have h := psp3 hp (by lia)
    have e : 2 * p = 4 * k + 2 := by lia
    rw [e] at h
    exact h
  have := hB hmem
  lia

end OMA.P_oeis_a217853

theorem OMA.solution : type_of% @OMA.S_oeis_a217853.main := OMA.P_oeis_a217853.infinite_k
