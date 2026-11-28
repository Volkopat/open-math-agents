import OMAStatements.S_oeis_a400454

-- Problem: A400454: Numbers k such that (2^k-1)*2^(k+3)+1 is a prime.
-- Credit: original proof by @agchua (#23604).
-- Finite multiplicative order supplies the required unit and nonzero element directly.
-- Proof idea (Pocklington): write 2^k = m + 1, so N = 8m(m+1) + 1 and (N-1)/4 = m * 2^(k+1).
-- If N is not prime, let p be its least prime factor, so p^2 <= N and p is odd. In ZMod p the
-- element c = 2^m satisfies c^(2^(k+1)) = -1, which is not 1, and c^(2^(k+2)) = 1, so the order
-- of c is 2^(k+2) = 4(m+1). The order divides p - 1, so p >= 4m + 5 and p^2 > N, a contradiction.

open OMA.S_oeis_a400454 in
theorem OMA.solution : type_of% @OMA.S_oeis_a400454.main := by
  intro k hk h
  have ht : 2 ≤ 2 ^ k := le_self_pow₀ (by decide) (by omega)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 ^ k = m + 1 := ⟨2 ^ k - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have h1 : 2 ^ k - 1 = m := by omega
  have h2 : 2 ^ (k + 1) = 2 * (m + 1) := by
    rw [pow_succ, hm]
    ring
  have h4 : 2 ^ (k + 1 + 1) = 4 * (m + 1) := by
    rw [pow_succ, h2]
    ring
  have hN : N k = 8 * (m * (m + 1)) + 1 := by
    show (2 ^ k - 1) * 2 ^ (k + 3) + 1 = 8 * (m * (m + 1)) + 1
    rw [h1, pow_add, hm]
    ring
  have hmm : 0 < m * (m + 1) := Nat.mul_pos (by omega) (by omega)
  have he : (N k - 1) / 4 = m * 2 ^ (k + 1) := by
    rw [hN, h2, show m * (2 * (m + 1)) = 2 * (m * (m + 1)) by ring]
    omega
  rw [he] at h
  by_contra hnp
  have hN1 : N k ≠ 1 := by omega
  have hNpos : 0 < N k := by omega
  obtain ⟨p, hp, hsq, hdvd⟩ : ∃ p : ℕ, p.Prime ∧ p ^ 2 ≤ N k ∧ p ∣ N k :=
    ⟨(N k).minFac, Nat.minFac_prime hN1, Nat.minFac_sq_le_self hNpos hnp, Nat.minFac_dvd (N k)⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hpne : p ≠ 2 := by
    rintro rfl
    rw [hN] at hdvd
    omega
  have : Fact (2 < p) := ⟨by omega⟩
  have h' : (2 : ℤ) ^ (m * 2 ^ (k + 1)) ≡ -1 [ZMOD (p : ℤ)] :=
    Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hdvd) h
  have hz : (((2 : ℤ) ^ (m * 2 ^ (k + 1)) : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) :=
    (ZMod.intCast_eq_intCast_iff _ _ p).mpr h'
  push_cast at hz
  have hc1 : ((2 : ZMod p) ^ m) ^ 2 ^ (k + 1) = -1 := by
    rw [← pow_mul]
    exact hz
  have hnot : ¬ ((2 : ZMod p) ^ m) ^ 2 ^ (k + 1) = 1 := by
    rw [hc1]
    exact ZMod.neg_one_ne_one
  have hfin : ((2 : ZMod p) ^ m) ^ 2 ^ (k + 1 + 1) = 1 := by
    rw [pow_succ (2 : ℕ) (k + 1), pow_mul, hc1, neg_one_sq]
  have hord : orderOf ((2 : ZMod p) ^ m) = 2 ^ (k + 1 + 1) := orderOf_eq_prime_pow hnot hfin
  have hdiv := ZMod.orderOf_dvd_card_sub_one
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, by positivity, hfin⟩).isUnit.ne_zero
  rw [hord, h4] at hdiv
  have hle : 4 * (m + 1) ≤ p - 1 := Nat.le_of_dvd (by omega) hdiv
  have hp5 : 4 * m + 5 ≤ p := by omega
  rw [hN] at hsq
  nlinarith [Nat.mul_le_mul hp5 hp5, Nat.zero_le (m * m), hm1]
