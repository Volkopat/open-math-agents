import OMAStatements.S_oeis_a369378

-- Problem: A369378, 2^(2^n+1)-1+2^k is composite for 0 < n, k < 2^n: writing k = 2^j * odd with j < n,
-- the Fermat number 2^(2^j)+1 divides it (2^k = -1 and 2^(2^n+1) = 2 modulo it); k = 0 gives a power of 2.
-- Credit: @bnb9001

namespace OMA_A369378_Proof

theorem two_pow_mod (j : ℕ) :
    (2 : ZMod (2 ^ (2 ^ j) + 1)) ^ (2 ^ j) = -1 := by
  have h : ((2 ^ (2 ^ j) + 1 : ℕ) : ZMod (2 ^ (2 ^ j) + 1)) = 0 := ZMod.natCast_self _
  push_cast at h
  linear_combination h

end OMA_A369378_Proof

open OMA_A369378_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a369378.main := by
  intro n hn k hk hp
  have hbig : 8 ≤ 2 ^ (2 ^ n + 1) := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 ^ n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- the number is a power of two at least 8
    rw [pow_zero, Nat.sub_add_cancel (by omega)] at hp
    have h2 : 2 ∣ 2 ^ (2 ^ n + 1) := dvd_pow_self 2 (by omega)
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega
  · obtain ⟨j, t, ht, hkt⟩ := Nat.exists_eq_two_pow_mul_odd (n := k) (by omega)
    have hjn : j < n := by
      have : 2 ^ j ≤ k := by rw [hkt]; exact Nat.le_mul_of_pos_right _ ht.pos
      have : 2 ^ j < 2 ^ n := lt_of_le_of_lt this hk
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    set F := 2 ^ (2 ^ j) + 1 with hF
    have hF3 : 3 ≤ F := by
      have : 2 ≤ 2 ^ (2 ^ j) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 ^ j) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)
      omega
    -- F divides the number
    have hdvd : F ∣ 2 ^ (2 ^ n + 1) - 1 + 2 ^ k := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_sub (by omega)]
      push_cast
      have hm := two_pow_mod j
      rw [← hF] at hm
      obtain ⟨s, rfl⟩ := ht
      have h1 : (2 : ZMod F) ^ k = -1 := by
        rw [hkt, pow_mul, hm, pow_succ, pow_mul]; simp
      have h2 : (2 : ZMod F) ^ (2 ^ n + 1) = 2 := by
        have : 2 ^ n = 2 ^ j * (2 * 2 ^ (n - j - 1)) := by
          rw [← pow_succ', ← pow_add]; congr 1; omega
        rw [pow_succ, this, pow_mul, hm, pow_mul]; simp
      rw [h1, h2]; ring
    -- F is a proper divisor
    have hlt : F < 2 ^ (2 ^ n + 1) - 1 + 2 ^ k := by
      have : 2 ^ (2 ^ j) ≤ 2 ^ (2 ^ n) :=
        Nat.pow_le_pow_right (by norm_num) (by
          have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mpr hjn; omega)
      have e : 2 ^ (2 ^ n + 1) = 2 * 2 ^ (2 ^ n) := by rw [pow_succ]; ring
      have : 4 ≤ 2 ^ (2 ^ n) := by omega
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    rcases hp.eq_one_or_self_of_dvd F hdvd with h | h <;> omega
