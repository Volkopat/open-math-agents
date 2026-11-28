import OMAStatements.S_oeis_a099237
import Mathlib

/-!
# Proof of the three conjectures of OEIS A099237 (Peter Bala, Jan 19 2023)

`a(n) = Sum_{k=0..n} C(n(n-k), k)`. Claims: `a(2^k) == 1 (mod 2^k)`, `a(3^k) == 1 (mod 3^(k+1))`,
`a(p^k) == 1 (mod p^(k+1))` for primes `p >= 5`.

Write `n = p^m` with `m >= 1` (for `m = 0`, `a(1) = 1`). The terms `k = 0` and `k = n` of the sum are
`1` and `0`, so `a(n) - 1 = Sum_{0<k<n} C(n(n-k), k)`.

1. If `p^m` divides `N` and `0 < i < p^m` then `p` divides `C(N, i)`: `i C(N,i) = N C(N-1,i-1)`, and
   `p^m` does not divide `i`.
2. If `p^m` divides `N` and `i < p^m` then `C(N-1, i) == (-1)^i (mod p)`: induction on `i` with
   Pascal's rule and step 1.
3. For `0 < k < n`, `N = n(n-k)`: `k (C(N,k) + n C(N-1,k-1)) = n^2 C(N-1,k-1)`, and `p^m` does not
   divide `k`, hence `p^(m+1)` divides `C(N,k) + n C(N-1,k-1)`.
4. Steps 2 and 3 give the key congruence `C(n(n-k), k) == (-1)^k p^m (mod p^(m+1))` for `0 < k < p^m`,
   valid for every prime `p`.
5. For odd `p`, `Sum_{0<k<n} (-1)^k = 0` since `n` is odd, so `a(n) - 1 == 0 (mod p^(m+1))`.
   For `p = 2` every term is a multiple of `2^m`.
-/

/-- Integer-valued copy of the sequence. -/
private def a099237_aZ (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((n * (n - k)).choose k : ℤ)

private theorem a099237_bridge (n : ℕ) : ((OMA.S_oeis_a099237.a n : ℕ) : ℤ) = a099237_aZ n := by
  unfold OMA.S_oeis_a099237.a a099237_aZ
  push_cast
  rfl

private theorem a099237_modeq (n N : ℕ) (h : (N : ℤ) ∣ a099237_aZ n - 1) :
    OMA.S_oeis_a099237.a n ≡ 1 [MOD N] := by
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd]
  rw [a099237_bridge]
  push_cast
  exact h

/-- L1: a prime `p` divides `C(N, i)` when `p^m ∣ N` and `0 < i < p^m`. -/
private theorem a099237_dvd_choose (p m N i : ℕ) (hp : p.Prime) (hN : p ^ m ∣ N)
    (hi0 : 0 < i) (hi : i < p ^ m) : p ∣ N.choose i := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have h := Nat.add_one_mul_choose_eq N' i'
  have hd : p ^ m ∣ (N' + 1).choose (i' + 1) * (i' + 1) := by
    rw [← h]
    exact Dvd.dvd.mul_right hN _
  by_contra hnd
  have hcop : Nat.Coprime (p ^ m) ((N' + 1).choose (i' + 1)) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
  have h2 : p ^ m ∣ i' + 1 := hcop.dvd_of_dvd_mul_left hd
  exact absurd (Nat.le_of_dvd (Nat.succ_pos _) h2) (by omega)

/-- L2: `C(N, i) == (-1)^i (mod p)` when `p^m ∣ N + 1` and `i < p^m`. -/
private theorem a099237_choose_pred (p m N : ℕ) (hp : p.Prime) (hN : p ^ m ∣ N + 1) :
    ∀ i : ℕ, i < p ^ m → (p : ℤ) ∣ (N.choose i : ℤ) - (-1) ^ i := by
  intro i
  induction i with
  | zero =>
    intro _
    simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 : (p : ℤ) ∣ ((N + 1).choose (i + 1) : ℤ) :=
      Int.natCast_dvd_natCast.2 (a099237_dvd_choose p m (N + 1) (i + 1) hp hN (Nat.succ_pos _) hi)
    have h3 : ((N + 1).choose (i + 1) : ℤ) = (N.choose i : ℤ) + (N.choose (i + 1) : ℤ) := by
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    have h4 : ((N.choose (i + 1) : ℤ) - (-1) ^ (i + 1))
        = ((N + 1).choose (i + 1) : ℤ) - ((N.choose i : ℤ) - (-1) ^ i) := by
      rw [h3]
      ring
    rw [h4]
    exact dvd_sub h2 h1

/-- L3a: the absorption identity, arranged without subtraction. -/
private theorem a099237_ident (n k' : ℕ) (hk : k' + 1 < n) :
    (k' + 1) * ((n * (n - (k' + 1))).choose (k' + 1) + n * (n * (n - (k' + 1)) - 1).choose k')
      = n * n * (n * (n - (k' + 1)) - 1).choose k' := by
  obtain ⟨N', hN'⟩ : ∃ N', n * (n - (k' + 1)) = N' + 1 :=
    ⟨n * (n - (k' + 1)) - 1, by
      have := Nat.mul_pos (show 0 < n by omega) (show 0 < n - (k' + 1) by omega)
      omega⟩
  rw [hN', Nat.add_sub_cancel]
  have h := Nat.add_one_mul_choose_eq N' k'
  have hnk : n - (k' + 1) + (k' + 1) = n := Nat.sub_add_cancel hk.le
  calc (k' + 1) * ((N' + 1).choose (k' + 1) + n * N'.choose k')
      = (N' + 1).choose (k' + 1) * (k' + 1) + (k' + 1) * n * N'.choose k' := by ring
    _ = (N' + 1) * N'.choose k' + (k' + 1) * n * N'.choose k' := by rw [← h]
    _ = n * (n - (k' + 1)) * N'.choose k' + (k' + 1) * n * N'.choose k' := by rw [hN']
    _ = n * (n - (k' + 1) + (k' + 1)) * N'.choose k' := by ring
    _ = n * n * N'.choose k' := by rw [hnk]

/-- L3b: if `p^(2m) ∣ k * x` with `0 < k < p^m` then `p^(m+1) ∣ x`. -/
private theorem a099237_val (p m k x : ℕ) (hp : p.Prime) (hk0 : 0 < k) (hk : k < p ^ m)
    (h : p ^ m * p ^ m ∣ k * x) : p ^ (m + 1) ∣ x := by
  obtain ⟨e, t, ht, hkt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0.ne' p hp.ne_one
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exact absurd (h0 ▸ dvd_zero p) ht
    · exact h0
  have hem : e < m := by
    have h1 : p ^ e ≤ k := by
      rw [hkt]
      exact Nat.le_mul_of_pos_right _ htpos
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 (lt_of_le_of_lt h1 hk)
  have h2 : p ^ e * p ^ (2 * m - e) ∣ p ^ e * (t * x) := by
    have h5 : p ^ e * p ^ (2 * m - e) = p ^ m * p ^ m := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [h5, ← mul_assoc, ← hkt]
    exact h
  have h3 : p ^ (2 * m - e) ∣ t * x := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos e) h2
  have hcop : Nat.Coprime (p ^ (2 * m - e)) t :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 ht)
  have h4 : p ^ (2 * m - e) ∣ x := hcop.dvd_of_dvd_mul_left h3
  exact dvd_trans (pow_dvd_pow p (by omega)) h4

/-- From the natural-number divisibility and L2 to the signed congruence. -/
private theorem a099237_combine (p m k' c d : ℕ) (h1 : p ^ (m + 1) ∣ c + p ^ m * d)
    (h2 : (p : ℤ) ∣ (d : ℤ) - (-1) ^ k') :
    (p : ℤ) ^ (m + 1) ∣ (c : ℤ) - (-1) ^ (k' + 1) * (p : ℤ) ^ m := by
  have hint : (p : ℤ) ^ (m + 1) ∣ (c : ℤ) + (p : ℤ) ^ m * (d : ℤ) := by
    exact_mod_cast h1
  have hmul : (p : ℤ) ^ (m + 1) ∣ (p : ℤ) ^ m * ((d : ℤ) - (-1) ^ k') := by
    rw [pow_succ]
    exact mul_dvd_mul_left _ h2
  have h3 := dvd_sub hint hmul
  have e : (c : ℤ) - (-1) ^ (k' + 1) * (p : ℤ) ^ m
      = (c : ℤ) + (p : ℤ) ^ m * (d : ℤ) - (p : ℤ) ^ m * ((d : ℤ) - (-1) ^ k') := by
    ring
  rw [e]
  exact h3

/-- L4: `C(p^m (p^m - k), k) == (-1)^k p^m (mod p^(m+1))` for `0 < k < p^m`. -/
private theorem a099237_key (p m k : ℕ) (hp : p.Prime) (hk0 : 0 < k) (hk : k < p ^ m) :
    (p : ℤ) ^ (m + 1) ∣ ((p ^ m * (p ^ m - k)).choose k : ℤ) - (-1) ^ k * (p : ℤ) ^ m := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hid := a099237_ident (p ^ m) k' hk
  have hnat : p ^ (m + 1) ∣ (p ^ m * (p ^ m - (k' + 1))).choose (k' + 1)
      + p ^ m * (p ^ m * (p ^ m - (k' + 1)) - 1).choose k' :=
    a099237_val p m (k' + 1) _ hp hk0 hk (by rw [hid]; exact dvd_mul_right _ _)
  have hpos : 0 < p ^ m * (p ^ m - (k' + 1)) := Nat.mul_pos (pow_pos hp.pos m) (by omega)
  have hN : p ^ m ∣ (p ^ m * (p ^ m - (k' + 1)) - 1) + 1 := by
    rw [Nat.sub_add_cancel hpos]
    exact dvd_mul_right _ _
  have hd := a099237_choose_pred p m _ hp hN k' (by omega)
  exact a099237_combine p m k' _ _ hnat hd

/-- L5: the alternating sum over `1 ≤ k < 2r+1` vanishes. -/
private theorem a099237_alt (r : ℕ) : ∑ k ∈ Finset.Ico 1 (2 * r + 1), (-1 : ℤ) ^ k = 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : 2 * (r + 1) + 1 = (2 * r + 1) + 1 + 1 := by ring
    have h2 : (-1 : ℤ) ^ (2 * r + 1) = -1 := Odd.neg_one_pow ⟨r, rfl⟩
    have h3 : (-1 : ℤ) ^ (2 * r + 1 + 1) = 1 := Even.neg_one_pow ⟨r + 1, by ring⟩
    rw [h1, Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega), ih, h2, h3]
    norm_num

private theorem a099237_a_one : a099237_aZ 1 = 1 := by
  simp [a099237_aZ, Finset.sum_range_succ]

/-- For `n ≥ 1` the terms `k = 0` and `k = n` of the sum are `1` and `0`. -/
private theorem a099237_a_eq (n : ℕ) (hn : 0 < n) :
    a099237_aZ n = 1 + ∑ k ∈ Finset.Ico 1 n, ((n * (n - k)).choose k : ℤ) := by
  unfold a099237_aZ
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
  rw [Nat.sub_self, Nat.mul_zero, Nat.choose_eq_zero_of_lt hn, Nat.choose_zero_right]
  simp

private theorem a099237_odd (p m : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (p : ℤ) ^ (m + 1) ∣ a099237_aZ (p ^ m) - 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [pow_zero, a099237_a_one]
    simp
  have hnpos : 0 < p ^ m := pow_pos hp.pos m
  obtain ⟨r, hr⟩ : Odd (p ^ m) := (hp.odd_of_ne_two hodd).pow
  rw [a099237_a_eq (p ^ m) hnpos, add_sub_cancel_left]
  have hsplit : (∑ k ∈ Finset.Ico 1 (p ^ m), ((p ^ m * (p ^ m - k)).choose k : ℤ))
      = ∑ k ∈ Finset.Ico 1 (p ^ m),
          (((p ^ m * (p ^ m - k)).choose k : ℤ) - (-1) ^ k * (p : ℤ) ^ m) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    have h0 : ∑ k ∈ Finset.Ico 1 (p ^ m), (-1 : ℤ) ^ k = 0 := by
      rw [hr]
      exact a099237_alt r
    rw [h0]
    ring
  rw [hsplit]
  refine Finset.dvd_sum fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  exact a099237_key p m k hp (by omega) hk.2

private theorem a099237_two (m : ℕ) : (2 : ℤ) ^ m ∣ a099237_aZ (2 ^ m) - 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [a099237_a_eq (2 ^ m) (pow_pos (by norm_num) m), add_sub_cancel_left]
  refine Finset.dvd_sum fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  have hkey := a099237_key 2 m k Nat.prime_two (by omega) hk.2
  have h1 : (2 : ℤ) ^ m ∣ ((2 ^ m * (2 ^ m - k)).choose k : ℤ) - (-1) ^ k * (2 : ℤ) ^ m := by
    refine dvd_trans (pow_dvd_pow _ (Nat.le_succ m)) ?_
    exact_mod_cast hkey
  have h2 : (2 : ℤ) ^ m ∣ (-1) ^ k * (2 : ℤ) ^ m := Dvd.intro_left _ rfl
  have h3 := dvd_add h1 h2
  rwa [sub_add_cancel] at h3

theorem OMA.solution : type_of% @OMA.S_oeis_a099237.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro k _
    apply a099237_modeq
    push_cast
    exact a099237_two k
  · intro k _
    apply a099237_modeq
    have h := a099237_odd 3 k Nat.prime_three (by norm_num)
    push_cast
    exact_mod_cast h
  · intro p k hp h5 _
    apply a099237_modeq
    push_cast
    exact a099237_odd p k hp (by omega)
