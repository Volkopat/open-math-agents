import OMAStatements.S_oeis_a221130

-- Problem: A221130, least start of n consecutive numbers h*2^m+m (1<=h<2^m) is 2^(2n-1)+n.
-- Consecutive members have consecutive parameters m, so 2^(m0+n-1) divides w - m0, forcing m0 >= n.
-- Credit: @bnb9001

namespace OMA_A221130_Proof

open OMA.S_oeis_a221130

theorem lt_two_pow' (m : ℕ) : m < 2 ^ m := Nat.lt_two_pow_self

/-- consecutive members have consecutive parameters -/
theorem consec {N m h m' h' : ℕ} (hm : 0 < m) (hh1 : 1 ≤ h) (hh2 : h < 2 ^ m) (hN : N = h * 2 ^ m + m)
    (hm' : 0 < m') (hh1' : 1 ≤ h') (hh2' : h' < 2 ^ m') (hN' : N + 1 = h' * 2 ^ m' + m') :
    m' = m + 1 := by
  have hm2 := lt_two_pow' m
  have hm2' := lt_two_pow' m'
  -- upper bounds: N < 4^m, N + 1 < 4^m'
  have hNup : N < 2 ^ (2 * m) := by
    have : h * 2 ^ m ≤ (2 ^ m - 1) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
    have e : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
    have : (2 ^ m - 1) * 2 ^ m + 2 ^ m = 2 ^ m * 2 ^ m := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by positivity))]
    omega
  have hNup' : N + 1 < 2 ^ (2 * m') := by
    have : h' * 2 ^ m' ≤ (2 ^ m' - 1) * 2 ^ m' := Nat.mul_le_mul_right _ (by omega)
    have : (2 ^ m' - 1) * 2 ^ m' + 2 ^ m' = 2 ^ m' * 2 ^ m' := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by positivity))]
    have e : 2 ^ (2 * m') = 2 ^ m' * 2 ^ m' := by rw [two_mul, pow_add]
    omega
  have hlow : 2 ^ m ≤ N := by have : 2 ^ m ≤ h * 2 ^ m := Nat.le_mul_of_pos_left _ (by omega); omega
  have hlow' : 2 ^ m' ≤ N + 1 := by
    have : 2 ^ m' ≤ h' * 2 ^ m' := Nat.le_mul_of_pos_left _ (by omega); omega
  rcases Nat.lt_or_ge m' (m + 1) with hlt | hge
  · -- m' ≤ m: 2^m' divides m - m' + 1, which is positive and small
    exfalso
    have hdm : 2 ^ m' ∣ 2 ^ m := pow_dvd_pow 2 (by omega)
    have h1 : 2 ^ m' ∣ N - m := by rw [hN, Nat.add_sub_cancel]; exact dvd_mul_of_dvd_right hdm _
    have h2 : 2 ^ m' ∣ N + 1 - m' := by rw [hN', Nat.add_sub_cancel]; exact dvd_mul_left _ _
    have h3 : 2 ^ m' ∣ (N + 1 - m') - (N - m) := Nat.dvd_sub h2 h1
    have hm2m : m < 2 * m' := by
      have : 2 ^ m < 2 ^ (2 * m') := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    rw [show (N + 1 - m') - (N - m) = m - m' + 1 by omega] at h3
    have := Nat.le_of_dvd (by omega) h3
    omega
  · -- m' ≥ m + 1: 2^m divides m' - m - 1, which is small
    have h1 : 2 ^ m ∣ N - m := by rw [hN, Nat.add_sub_cancel]; exact dvd_mul_left _ _
    have hdm : 2 ^ m ∣ 2 ^ m' := pow_dvd_pow 2 (by omega)
    have h2 : 2 ^ m ∣ N + 1 - m' := by
      rw [hN', Nat.add_sub_cancel]; exact dvd_mul_of_dvd_right hdm _
    have h3 : 2 ^ m ∣ (N - m) - (N + 1 - m') := Nat.dvd_sub h1 h2
    have hm2m : m' ≤ 2 * m := by
      have : 2 ^ m' ≤ 2 ^ (2 * m) := by omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    rw [show (N - m) - (N + 1 - m') = m' - m - 1 by omega] at h3
    by_contra hne
    have := Nat.le_of_dvd (by omega) h3
    omega

end OMA_A221130_Proof

open OMA.S_oeis_a221130 OMA_A221130_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a221130.main := by
  intro n hn
  refine ⟨?_, ?_⟩
  · -- membership: a n + i = 2^(n-1-i) * 2^(n+i) + (n+i)
    show ∀ i < n, IsForm (a n + i)
    intro i hi
    refine ⟨n + i, 2 ^ (n - 1 - i), by omega, Nat.one_le_two_pow,
      Nat.pow_lt_pow_right (by norm_num) (by omega), ?_⟩
    unfold a
    rw [← pow_add, show n - 1 - i + (n + i) = 2 * n - 1 by omega]
    ring
  · -- minimality
    intro w hw
    choose m hrest using hw
    choose h hspec using hrest
    -- parameters increase by one along the run
    have hstep : ∀ i (hi : i + 1 < n), m (i + 1) hi = m i (by omega) + 1 := by
      intro i hi
      obtain ⟨a1, a2, a3, a4⟩ := hspec i (by omega)
      obtain ⟨b1, b2, b3, b4⟩ := hspec (i + 1) hi
      exact consec a1 a2 a3 a4 b1 b2 b3 (by rw [← add_assoc] at b4; exact b4)
    have hpar : ∀ i (hi : i < n), m i hi = m 0 hn + i := by
      intro i
      induction i with
      | zero => intro hi; rfl
      | succ i ih => intro hi; rw [hstep i hi, ih (by omega)]; ring
    -- 2^(m0 + n - 1) divides w - m0
    obtain ⟨c1, c2, c3, c4⟩ := hspec 0 hn
    obtain ⟨d1, d2, d3, d4⟩ := hspec (n - 1) (by omega)
    rw [hpar (n - 1) (by omega)] at d1 d3 d4
    set m0 := m 0 hn
    set h0 := h 0 hn
    set hl := h (n - 1) (by omega)
    -- w - m0 = h0 * 2^m0 = hl * 2^(m0 + n - 1)
    have e0 : w - m0 = h0 * 2 ^ m0 := by rw [show w = w + 0 from rfl, c4]; omega
    have el : w - m0 = hl * 2 ^ (m0 + (n - 1)) := by
      have : w + (n - 1) = hl * 2 ^ (m0 + (n - 1)) + (m0 + (n - 1)) := d4
      omega
    -- so h0 = hl * 2^(n-1) ≥ 2^(n-1), and h0 < 2^m0 forces m0 ≥ n
    have hh0 : h0 = hl * 2 ^ (n - 1) := by
      have : h0 * 2 ^ m0 = (hl * 2 ^ (n - 1)) * 2 ^ m0 := by rw [← e0, el, pow_add]; ring
      exact Nat.eq_of_mul_eq_mul_right (by positivity) this
    have hge : 2 ^ (n - 1) ≤ h0 := by rw [hh0]; exact Nat.le_mul_of_pos_left _ (by omega)
    have hm0 : n ≤ m0 := by
      have : 2 ^ (n - 1) < 2 ^ m0 := lt_of_le_of_lt hge c3
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
      omega
    -- conclude
    unfold a
    have hw : w = h0 * 2 ^ m0 + m0 := by simpa using c4
    have : 2 ^ (2 * n - 1) ≤ h0 * 2 ^ m0 := by
      calc 2 ^ (2 * n - 1) = 2 ^ (n - 1) * 2 ^ n := by rw [← pow_add]; congr 1; omega
        _ ≤ h0 * 2 ^ m0 := Nat.mul_le_mul hge (Nat.pow_le_pow_right (by norm_num) hm0)
    omega
