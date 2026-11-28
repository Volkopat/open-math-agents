import OMAStatements.S_oeis_a363739
import Mathlib

-- Problem: OEIS A363739, conjectures of Spezia on the run lengths a(n) of A349509 (the
-- denominator b(k) of binomial(k^3 + 6 k^2 - 6 k + 2, k^3 - 1) / k^3): a(2n) = 1 and
-- a(2n-1) = A349929(n) - A349929(n-1) - 1 for n >= 1, where A349929 lists the k with b(k) = 3.
-- Statement: statements/oeis-a363739.lean (declaration OMA.S_oeis_a363739.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let N = k^3 + 6 k^2 - 6 k + 3. The absorption identity gives
-- binomial(N - 1, k^3 - 1) / k^3 = binomial(N, k^3) / N, so b(k) divides k^3 and N, thus also
-- N - k^3 = 6 k (k - 1) + 3. A common divisor d of k^3 and 6 k j + 3 divides 27 and is not a
-- multiple of 9, so d divides 3. Thus b(k) is 1 or 3, and b(k) = 3 only if 3 divides k.
-- For k = 3^j with j >= 2, M = 6 k (k - 1) + 3 < k^3, and the Vandermonde identity gives
-- binomial(k^3 + M, k^3) = 1 (mod 3), while 3 divides N. So b(3^j) = 3: the set of the k with
-- b(k) = 3 is infinite. No two adjacent indices have b = 3, and b(1) = 1. By induction, the
-- runs with even number are the single terms 3 at the positions A349929(j), and the runs with
-- odd number are the blocks of terms 1 between them. The two formulas follow.

namespace OMA.A363739

open OMA.S_oeis_a363739

/-- If d divides k^3 and 6 k j + 3, then d divides 3. -/
lemma dvd_three (d k j : ℕ) (h1 : d ∣ k ^ 3) (h2 : d ∣ 6 * k * j + 3) : d ∣ 3 := by
  have h27 : d ∣ 27 := by
    have h1' : (d : ℤ) ∣ (k : ℤ) ^ 3 := by exact_mod_cast h1
    have h2' : (d : ℤ) ∣ 6 * (k : ℤ) * j + 3 := by exact_mod_cast h2
    have : (d : ℤ) ∣ 27 := by
      have h := dvd_sub (Dvd.dvd.mul_right h2' ((6 * (k : ℤ) * j + 3) ^ 2
        - 3 * (6 * (k : ℤ) * j + 3) * (6 * k * j) + 3 * (6 * (k : ℤ) * j) ^ 2))
        (Dvd.dvd.mul_left h1' (216 * (j : ℤ) ^ 3))
      have e : (6 * (k : ℤ) * j + 3) * ((6 * (k : ℤ) * j + 3) ^ 2
        - 3 * (6 * (k : ℤ) * j + 3) * (6 * k * j) + 3 * (6 * (k : ℤ) * j) ^ 2)
        - 216 * (j : ℤ) ^ 3 * (k : ℤ) ^ 3 = 27 := by ring
      rwa [e] at h
    exact_mod_cast this
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show d ∣ 3 ^ 3 from by simpa using h27)
  interval_cases i
  · simp
  · simp
  all_goals
    exfalso
    have h9 : 9 ∣ k ^ 3 := Dvd.dvd.trans (by norm_num) h1
    have h9' : 9 ∣ 6 * k * j + 3 := Dvd.dvd.trans (by norm_num) h2
    have h3 : 3 ∣ k := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Dvd.dvd.trans (by norm_num) h9)
    obtain ⟨t, rfl⟩ := h3
    have e : 6 * (3 * t) * j + 3 = 9 * (2 * (t * j)) + 3 := by ring
    rw [e] at h9'
    omega

/-- The top index of the binomial, for k = m + 1. -/
lemma top_eq (m : ℕ) : (m + 1) ^ 3 + 6 * (m + 1) ^ 2 - 6 * (m + 1) + 2
    = (m + 1) ^ 3 + (6 * (m + 1) * m + 2) := by
  have : 6 * (m + 1) ^ 2 = 6 * (m + 1) * m + 6 * (m + 1) := by ring
  omega

/-- Two forms of the rational number: c / k^3 = c' / (k^3 + 6 k m + 3). -/
lemma two_forms (m : ℕ) :
    ((Nat.choose ((m + 1) ^ 3 + (6 * (m + 1) * m + 2)) ((m + 1) ^ 3 - 1) : ℚ) / ((m + 1 : ℕ) : ℚ) ^ 3)
    = (Nat.choose ((m + 1) ^ 3 + (6 * (m + 1) * m + 3)) ((m + 1) ^ 3) : ℚ)
      / (((m + 1) ^ 3 + (6 * (m + 1) * m + 3) : ℕ) : ℚ) := by
  have hpos : 0 < (m + 1) ^ 3 := by positivity
  have h := Nat.add_one_mul_choose_eq ((m + 1) ^ 3 + (6 * (m + 1) * m + 2)) ((m + 1) ^ 3 - 1)
  rw [show (m + 1) ^ 3 - 1 + 1 = (m + 1) ^ 3 by omega,
    show (m + 1) ^ 3 + (6 * (m + 1) * m + 2) + 1 = (m + 1) ^ 3 + (6 * (m + 1) * m + 3) by omega] at h
  have h' : ((((m + 1) ^ 3 + (6 * (m + 1) * m + 3) : ℕ) : ℚ)) *
      (Nat.choose ((m + 1) ^ 3 + (6 * (m + 1) * m + 2)) ((m + 1) ^ 3 - 1) : ℚ)
      = (Nat.choose ((m + 1) ^ 3 + (6 * (m + 1) * m + 3)) ((m + 1) ^ 3) : ℚ) * (((m + 1) ^ 3 : ℕ) : ℚ) := by
    exact_mod_cast h
  have h1 : (((m + 1 : ℕ) : ℚ)) ^ 3 ≠ 0 := by positivity
  have h2 : ((((m + 1) ^ 3 + (6 * (m + 1) * m + 3) : ℕ) : ℚ)) ≠ 0 := by positivity
  rw [div_eq_div_iff h1 h2]
  push_cast at h' ⊢
  linarith

lemma den_dvd_nat (c n : ℕ) : ((c : ℚ) / (n : ℚ)).den ∣ n := by
  have := Rat.den_dvd (c : ℤ) (n : ℤ)
  rw [Rat.divInt_eq_div] at this
  simp only [Int.cast_natCast] at this
  exact Int.natCast_dvd_natCast.mp this

/-- b(k) divides 3 for k >= 1. -/
lemma b_dvd_three (k : ℕ) (hk : 1 ≤ k) : b k ∣ 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : b (m + 1) ∣ (m + 1) ^ 3 := by
    unfold b
    have := den_dvd_nat (Nat.choose ((m + 1) ^ 3 + 6 * (m + 1) ^ 2 - 6 * (m + 1) + 2) ((m + 1) ^ 3 - 1))
      ((m + 1) ^ 3)
    simpa using this
  have e2 : b (m + 1) ∣ (m + 1) ^ 3 + (6 * (m + 1) * m + 3) := by
    unfold b
    rw [top_eq, two_forms]
    exact den_dvd_nat _ _
  exact dvd_three _ (m + 1) m e1 ((Nat.dvd_add_right e1).mp e2)

lemma b_cases (k : ℕ) (hk : 1 ≤ k) : b k = 1 ∨ b k = 3 :=
  (Nat.dvd_prime Nat.prime_three).mp (b_dvd_three k hk)

lemma b_zero : b 0 = 1 := by simp [b]

lemma three_dvd_of_b (k : ℕ) (h : b k = 3) : 3 ∣ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have e1 : b (m + 1) ∣ (m + 1) ^ 3 := by
      unfold b
      have := den_dvd_nat (Nat.choose ((m + 1) ^ 3 + 6 * (m + 1) ^ 2 - 6 * (m + 1) + 2) ((m + 1) ^ 3 - 1))
        ((m + 1) ^ 3)
      simpa using this
    rw [h] at e1
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three e1

/-- binomial(3^e + M, 3^e) is 1 modulo 3 for M < 3^e. -/
lemma choose_mod (e M : ℕ) (hM : M < 3 ^ e) : (3 ^ e + M).choose (3 ^ e) % 3 = 1 := by
  have hs : (3 ^ e + M).choose (3 ^ e) = (3 ^ e + M).choose M := by
    rw [Nat.add_comm, Nat.choose_symm_add]
  rw [hs, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ']
  have hd : 3 ∣ ∑ i ∈ Finset.range M, (3 ^ e).choose (i + 1) * M.choose (M - (i + 1)) := by
    apply Finset.dvd_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Dvd.dvd.mul_right
      (Nat.Prime.dvd_choose_pow Nat.prime_three (by omega) (by omega)) _
  obtain ⟨q, hq⟩ := hd
  rw [hq]
  simp

/-- b(3^j) = 3 for j >= 2. -/
lemma b_pow (j : ℕ) (hj : 2 ≤ j) : b (3 ^ j) = 3 := by
  obtain ⟨m, hm⟩ : ∃ m, 3 ^ j = m + 1 := ⟨3 ^ j - 1, by have : 0 < 3 ^ j := by positivity
                                                        omega⟩
  have h9 : 9 ≤ m + 1 := by
    rw [← hm]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hmod : ((m + 1) ^ 3 + (6 * (m + 1) * m + 3)).choose ((m + 1) ^ 3) % 3 = 1 := by
    have e : (m + 1) ^ 3 = 3 ^ (j * 3) := by rw [← hm, ← pow_mul]
    rw [e]
    apply choose_mod
    rw [← e]
    have : 6 * (m + 1) * m + 3 < 9 * (m + 1) * (m + 1) := by nlinarith
    calc 6 * (m + 1) * m + 3 < 9 * (m + 1) * (m + 1) := this
      _ ≤ (m + 1) * (m + 1) * (m + 1) := by nlinarith
      _ = (m + 1) ^ 3 := by ring
  rcases b_cases (3 ^ j) (Nat.one_le_pow _ _ (by norm_num)) with h1 | h3
  · exfalso
    rw [hm] at h1
    unfold b at h1
    rw [top_eq, two_forms] at h1
    set c := Nat.choose ((m + 1) ^ 3 + (6 * (m + 1) * m + 3)) ((m + 1) ^ 3) with hc
    set N := (m + 1) ^ 3 + (6 * (m + 1) * m + 3) with hN
    have hNpos : (0 : ℚ) < (N : ℚ) := by rw [hN]; positivity
    have hint : ((c : ℚ) / (N : ℚ)) = (((c : ℚ) / (N : ℚ)).num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den ((c : ℚ) / (N : ℚ)), h1]
      simp
    have hcz : (c : ℤ) = ((c : ℚ) / (N : ℚ)).num * (N : ℤ) := by
      have : (c : ℚ) = (((c : ℚ) / (N : ℚ)).num : ℚ) * (N : ℚ) := by
        rw [← hint]; field_simp
      exact_mod_cast this
    have h3N : (3 : ℤ) ∣ (N : ℤ) := by
      have : 3 ∣ N := by
        rw [hN, ← hm]
        have h3j : 3 ∣ 3 ^ j := dvd_pow_self 3 (by omega)
        exact (Nat.dvd_add_right (Dvd.dvd.trans h3j (dvd_pow_self _ (by norm_num)))).mpr
          ((Nat.dvd_add_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h3j 6) m)).mpr (dvd_refl 3))
      exact_mod_cast this
    have h3c : (3 : ℤ) ∣ (c : ℤ) := by rw [hcz]; exact Dvd.dvd.mul_left h3N _
    have h3c' : 3 ∣ c := by exact_mod_cast h3c
    omega
  · exact h3

lemma inf3 : {k | b k = 3}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  exact ⟨3 ^ (n + 2), b_pow (n + 2) (by omega), lt_of_lt_of_le (Nat.lt_pow_self (by norm_num : 1 < 3))
    (Nat.pow_le_pow_right (by norm_num) (by omega))⟩

/-- The positions of the terms 3, counted from 0. -/
noncomputable def T' (j : ℕ) : ℕ := Nat.nth (fun k => b k = 3) j

lemma bT' (j : ℕ) : b (T' j) = 3 := Nat.nth_mem_of_infinite inf3 j

lemma T'_mono : StrictMono T' := Nat.nth_strictMono inf3

lemma T'_pos (j : ℕ) : 1 ≤ T' j := by
  rcases Nat.eq_zero_or_pos (T' j) with h | h
  · have := bT' j
    rw [h, b_zero] at this
    omega
  · exact h

lemma b_succ_T' (j : ℕ) : b (T' j + 1) = 1 := by
  rcases b_cases (T' j + 1) (by omega) with h | h
  · exact h
  · have h1 := three_dvd_of_b _ h
    have h2 := three_dvd_of_b _ (bT' j)
    omega

lemma start_all : ∀ j : ℕ, start (2 * j + 1) = T' j ∧ start (2 * j + 2) = T' j + 1 := by
  have even_step : ∀ j, start (2 * j + 1) = T' j → start (2 * j + 2) = T' j + 1 := by
    intro j h
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, start, h, bT']
    apply le_antisymm
    · apply Nat.sInf_le
      exact ⟨by omega, by rw [b_succ_T']; norm_num⟩
    · apply le_csInf
      · exact ⟨T' j + 1, by omega, by rw [b_succ_T']; norm_num⟩
      · intro x hx
        have := hx.1
        omega
  intro j
  induction j with
  | zero =>
    have h1 : start 1 = T' 0 := by
      rw [start, T', Nat.nth_zero]
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq, start]
      have hb1 : b 1 = 1 := by
        rcases b_cases 1 le_rfl with h | h
        · exact h
        · have := three_dvd_of_b _ h; omega
      rw [hb1]
      constructor
      · rintro ⟨hx1, hx2⟩
        rcases b_cases x (by omega) with h | h
        · exact absurd h hx2
        · exact h
      · intro hx
        have h3 := three_dvd_of_b _ hx
        refine ⟨?_, by rw [hx]; norm_num⟩
        rcases Nat.lt_or_ge 1 x with h | h
        · exact h
        · interval_cases x
          · rw [b_zero] at hx; omega
          · omega
    exact ⟨h1, even_step 0 h1⟩
  | succ j ih =>
    have h1 : start (2 * (j + 1) + 1) = T' (j + 1) := by
      rw [show 2 * (j + 1) + 1 = (2 * j + 2) + 1 by ring, start, ih.2, b_succ_T',
        show T' (j + 1) = sInf {x | b x = 3 ∧ ∀ k < j + 1, Nat.nth (fun k => b k = 3) k < x}
          from Nat.nth_eq_sInf _ _]
      refine congrArg (sInf : Set ℕ → ℕ) (Set.ext fun x => ?_)
      show (T' j + 1 < x ∧ b x ≠ 1) ↔ (b x = 3 ∧ ∀ k < j + 1, Nat.nth (fun k => b k = 3) k < x)
      constructor
      · rintro ⟨hx1, hx2⟩
        refine ⟨?_, ?_⟩
        · rcases b_cases x (by omega) with h | h
          · exact absurd h hx2
          · exact h
        · intro k hk
          have : T' k ≤ T' j := T'_mono.monotone (by omega)
          show T' k < x
          omega
      · rintro ⟨hx1, hx2⟩
        have hlt : T' j < x := hx2 j (by omega)
        refine ⟨?_, by rw [hx1]; norm_num⟩
        rcases Nat.lt_or_ge (T' j + 1) x with h | h
        · exact h
        · have : x = T' j + 1 := by omega
          rw [this, b_succ_T'] at hx1
          omega
    exact ⟨h1, even_step (j + 1) h1⟩

theorem main' : ∀ n : ℕ, 1 ≤ n → a (2 * n) = 1 ∧ a (2 * n - 1) = T n - T (n - 1) - 1 := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  obtain ⟨s1, s2⟩ := start_all j
  constructor
  · unfold a
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 - 1 = 2 * j + 1 by omega, s1, s2]
    omega
  · unfold a T
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * j + 1 - 1 = 2 * j by omega, s1,
      if_neg (by omega), show j + 1 - 1 = j by omega]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [start]; rfl
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, (start_all i).2, if_neg (by omega),
        show i + 1 - 1 = i by omega]
      show T' (i + 1) - (T' i + 1) = T' (i + 1) - T' i - 1
      omega

end OMA.A363739

theorem OMA.solution : type_of% @OMA.S_oeis_a363739.main :=
  OMA.A363739.main'
