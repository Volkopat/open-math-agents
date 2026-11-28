import OMAStatements.S_mo_346091

-- Problem: Sum of two n-th powers, of two m-th powers, but not of two mn-th powers
-- Upstream: formal-conjectures statements/mo-346091.lean:0 (declaration OMA.S_mo_346091.main)
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof idea. Take v with v = 0 (mod n) and v = 1 (mod m). Then
--   2^v = (2^(v/n))^n + 0^n = (2^((v-1)/m))^m + (2^((v-1)/m))^m
-- lies in S_n and in S_m. On the other hand, if a^N + b^N = 2^v with N >= 2, then v = 0 or 1
-- (mod N): divide out common factors 2; if exactly one of a, b is odd the sum is odd; if both are
-- odd and N is even the sum is 2 (mod 4); if both are odd and N is odd, then
-- (a^N + b^N)/(a + b) is odd, so 2^v divides a + b, and comparing sizes forces a = b = 1.
-- With N = m n this excludes 2^v from S_{mn}. The exponents v form an arithmetic progression.

namespace OMAmo346091

lemma odd_sum_range (f : ℕ → ℤ) (hf : ∀ i, Odd (f i)) :
    ∀ n : ℕ, (Odd (∑ i ∈ Finset.range n, f i) ↔ Odd n)
  | 0 => by simp
  | n + 1 => by
    have h1 : ¬ Even (f n) := Int.not_even_iff_odd.2 (hf n)
    rw [Finset.sum_range_succ, Int.odd_add, odd_sum_range f hf n, Nat.odd_add_one]
    simp [h1]

/-- Size step: `a > 0 > b`, `N` odd, cannot have `0 < a^N + b^N ≤ |a + b|`. -/
lemma size_mixed (N : ℕ) (hN3 : 3 ≤ N) (hNo : Odd N) (a b : ℤ) (ha : 0 < a) (hb : b < 0)
    (hpos : 0 < a ^ N + b ^ N) (hle : a ^ N + b ^ N ≤ |a + b|) : False := by
  obtain ⟨g, rfl⟩ : ∃ g : ℤ, b = -g := ⟨-b, by ring⟩
  have hg : 0 < g := by linarith
  rw [hNo.neg_pow] at hpos hle
  have hlt : g < a := by
    have h1 : g ^ N < a ^ N := by linarith
    exact lt_of_pow_lt_pow_left₀ N ha.le h1
  have habs : |a + -g| = a - g := by
    rw [abs_of_pos (by linarith)]; ring
  rw [habs] at hle
  have hN1 : N - 1 ≠ 0 := by omega
  have h1 : g ^ (N - 1) ≤ a ^ (N - 1) := pow_le_pow_left₀ hg.le hlt.le _
  have h2 : a ^ N = a * a ^ (N - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have h3 : g ^ N = g * g ^ (N - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have ha2 : (2 : ℤ) ≤ a := by linarith
  have h4 : (2 : ℤ) ≤ a ^ (N - 1) := le_trans ha2 (le_self_pow₀ (by linarith) hN1)
  have h5 : g * g ^ (N - 1) ≤ g * a ^ (N - 1) := mul_le_mul_of_nonneg_left h1 hg.le
  have h6 : 0 ≤ (a - g) * (a ^ (N - 1) - 2) := mul_nonneg (by linarith) (by linarith)
  nlinarith [h5, h6]

/-- Both odd, `N` odd: `a^N + b^N = 2^v` forces `v = 1`. -/
lemma odd_case (N : ℕ) (hN3 : 3 ≤ N) (hNo : Odd N) (a b : ℤ) (ha : Odd a) (hb : Odd b)
    (v : ℕ) (h : a ^ N + b ^ N = 2 ^ v) : v = 1 := by
  have hterm : ∀ i : ℕ, Odd (a ^ i * (-b) ^ (N - 1 - i)) := fun i => ha.pow.mul hb.neg.pow
  have hQodd : Odd (∑ i ∈ Finset.range N, a ^ i * (-b) ^ (N - 1 - i)) :=
    (odd_sum_range _ hterm N).2 hNo
  have hQ : (∑ i ∈ Finset.range N, a ^ i * (-b) ^ (N - 1 - i)) * (a + b) = 2 ^ v := by
    have h1 := geom_sum₂_mul a (-b) N
    rw [hNo.neg_pow] at h1
    rw [← h, show a + b = a - -b by ring, h1]
    ring
  obtain ⟨k, hk⟩ := hQodd
  have hcop : IsCoprime ((2 : ℤ) ^ v) (∑ i ∈ Finset.range N, a ^ i * (-b) ^ (N - 1 - i)) := by
    apply IsCoprime.pow_left
    exact ⟨-k, 1, by rw [hk]; ring⟩
  have hdvd : (2 : ℤ) ^ v ∣ a + b := by
    apply hcop.dvd_of_dvd_mul_right
    exact ⟨1, by rw [mul_one, mul_comm, hQ]⟩
  have hpos : (0 : ℤ) < 2 ^ v := by positivity
  have hne : a + b ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hQ
    linarith
  have hle : (2 : ℤ) ^ v ≤ |a + b| := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hdvd)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact (Int.not_even_iff_odd.2 ha) ⟨0, (add_zero 0).symm⟩
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact (Int.not_even_iff_odd.2 hb) ⟨0, (add_zero 0).symm⟩
  have hN0 : N ≠ 0 := by omega
  rcases lt_or_gt_of_ne ha0 with ha' | ha'
  · rcases lt_or_gt_of_ne hb0 with hb' | hb'
    · exfalso
      have h1 : a ^ N < 0 := hNo.pow_neg ha'
      have h2 : b ^ N < 0 := hNo.pow_neg hb'
      linarith
    · exfalso
      apply size_mixed N hN3 hNo b a hb' ha'
      · rw [add_comm, h]; exact hpos
      · rw [add_comm, h, add_comm b a]; exact hle
  · rcases lt_or_gt_of_ne hb0 with hb' | hb'
    · exfalso
      apply size_mixed N hN3 hNo a b ha' hb'
      · rw [h]; exact hpos
      · rw [h]; exact hle
    · have h1 : a ≤ a ^ N := le_self_pow₀ (by linarith) hN0
      have h2 : b ≤ b ^ N := le_self_pow₀ (by linarith) hN0
      have habs : |a + b| = a + b := abs_of_pos (by linarith)
      rw [habs, ← h] at hle
      have hone : ∀ c : ℤ, 0 < c → c ^ N ≤ c → c = 1 := by
        intro c hc hcN
        by_contra hc1
        have hc2 : (2 : ℤ) ≤ c := by omega
        have h3 : c ^ 2 ≤ c ^ N := pow_le_pow_right₀ (by linarith) (by omega)
        nlinarith
      have ha1 : a = 1 := hone a ha' (by linarith)
      have hb1 : b = 1 := hone b hb' (by linarith)
      rw [ha1, hb1, one_pow] at h
      rcases v with _ | _ | w
      · norm_num at h
      · rfl
      · exfalso
        have h4 : (2 : ℤ) ^ (w + 1 + 1) = 4 * 2 ^ w := by ring
        have h5 : (0 : ℤ) < 2 ^ w := by positivity
        rw [h4] at h
        linarith

/-- If `a^N + b^N = 2^v` with `N ≥ 2`, then `v ≡ 0` or `1 (mod N)`. -/
lemma key (N : ℕ) (hN : 2 ≤ N) :
    ∀ v : ℕ, ∀ a b : ℤ, a ^ N + b ^ N = 2 ^ v → v % N = 0 ∨ v % N = 1 := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro a b h
    have hN0 : N ≠ 0 := by omega
    have hmixed : ∀ c d : ℤ, Even c → Odd d → c ^ N + d ^ N = 2 ^ v → v % N = 0 := by
      intro c d hc hd hcd
      have hodd : Odd (c ^ N + d ^ N) := (hc.pow_of_ne_zero hN0).add_odd hd.pow
      rw [hcd] at hodd
      rcases Nat.eq_zero_or_pos v with rfl | hv
      · simp
      · exfalso
        have hev : Even ((2 : ℤ) ^ v) := even_two.pow_of_ne_zero (by omega)
        exact (Int.not_even_iff_odd.2 hodd) hev
    rcases Int.even_or_odd a with ha | ha
    · rcases Int.even_or_odd b with hb | hb
      · obtain ⟨c, rfl⟩ := ha
        obtain ⟨d, rfl⟩ := hb
        have h2 : (2 : ℤ) ^ N * (c ^ N + d ^ N) = 2 ^ v := by
          rw [← h]; ring
        have hvN : N ≤ v := by
          by_contra hlt
          push Not at hlt
          have h3 : (2 : ℤ) ^ v * (2 ^ (N - v) * (c ^ N + d ^ N)) = 2 ^ v * 1 := by
            rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le, h2, mul_one]
          have h4 := mul_left_cancel₀ (pow_ne_zero v (two_ne_zero)) h3
          have h5 : (2 : ℤ) ∣ 1 := by
            rw [← h4]
            exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
          omega
        have h5 : c ^ N + d ^ N = 2 ^ (v - N) := by
          have h6 : (2 : ℤ) ^ N * (c ^ N + d ^ N) = 2 ^ N * 2 ^ (v - N) := by
            rw [h2, ← pow_add, Nat.add_sub_cancel' hvN]
          exact mul_left_cancel₀ (pow_ne_zero N two_ne_zero) h6
        have h7 := ih (v - N) (by omega) c d h5
        have hmod : (v - N) % N = v % N := by
          conv_rhs => rw [← Nat.sub_add_cancel hvN]
          rw [Nat.add_mod_right]
        rw [hmod] at h7
        exact h7
      · left
        exact hmixed a b ha hb h
    · rcases Int.even_or_odd b with hb | hb
      · left
        exact hmixed b a hb ha (by rw [add_comm]; exact h)
      · right
        rcases Nat.even_or_odd N with hNe | hNo
        · obtain ⟨k, hk⟩ := hNe
          have ha2 : a ^ N % 4 = 1 := by
            have h1 := Int.sq_mod_four_eq_one_of_odd (ha.pow (n := k))
            rwa [← pow_mul, show k * 2 = N by omega] at h1
          have hb2 : b ^ N % 4 = 1 := by
            have h1 := Int.sq_mod_four_eq_one_of_odd (hb.pow (n := k))
            rwa [← pow_mul, show k * 2 = N by omega] at h1
          have h3 : (2 : ℤ) ^ v % 4 = 2 := by
            rw [← h]; omega
          rcases v with _ | _ | w
          · norm_num at h3
          · exact Nat.mod_eq_of_lt (by omega)
          · exfalso
            have h4 : (2 : ℤ) ^ (w + 1 + 1) = 4 * 2 ^ w := by ring
            rw [h4] at h3
            omega
        · have hv1 := odd_case N (by obtain ⟨k, hk⟩ := hNo; omega) hNo a b ha hb v h
          rw [hv1]
          exact Nat.mod_eq_of_lt (by omega)

end OMAmo346091

theorem OMA.solution : type_of% @OMA.S_mo_346091.main := by
  intro m n hm hn hco
  obtain ⟨v0, h0, h1⟩ := Nat.chineseRemainder hco.symm 0 1
  have hn0 : n ∣ v0 := (Nat.modEq_zero_iff_dvd).1 h0
  have hm1 : v0 % m = 1 := by
    have h2 : v0 % m = 1 % m := h1
    rw [h2]
    exact Nat.mod_eq_of_lt (by omega)
  have hmn : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℕ => (2 : ℤ) ^ (v0 + m * n * t)) ?_ ?_
  · intro s t hst
    have h2 := pow_right_injective₀ (by norm_num : (0 : ℤ) < 2) (by norm_num : (2 : ℤ) ≠ 1) hst
    have h3 : m * n * s = m * n * t := by omega
    exact Nat.eq_of_mul_eq_mul_left hmn h3
  · intro t
    have hvn : (v0 + m * n * t) % n = 0 := by
      have h2 : n ∣ v0 + m * n * t :=
        Dvd.dvd.add hn0 (Dvd.dvd.mul_right (Dvd.intro_left m rfl) t)
      exact Nat.mod_eq_zero_of_dvd h2
    have hvm : (v0 + m * n * t) % m = 1 := by
      rw [mul_assoc, Nat.add_mul_mod_self_left]
      exact hm1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero hvn
      refine ⟨2 ^ j, 0, ?_⟩
      show ((2 : ℤ) ^ j) ^ n + 0 ^ n = 2 ^ (v0 + m * n * t)
      rw [hj, zero_pow (by omega), add_zero, ← pow_mul, mul_comm]
    · have h2 := Nat.div_add_mod (v0 + m * n * t) m
      rw [hvm] at h2
      refine ⟨2 ^ ((v0 + m * n * t) / m), 2 ^ ((v0 + m * n * t) / m), ?_⟩
      show ((2 : ℤ) ^ ((v0 + m * n * t) / m)) ^ m + (2 ^ ((v0 + m * n * t) / m)) ^ m
        = 2 ^ (v0 + m * n * t)
      conv_rhs => rw [← h2]
      rw [pow_succ, pow_mul']
      ring
    · rintro ⟨a, b, hab⟩
      have h2 := OMAmo346091.key (m * n) (by nlinarith) (v0 + m * n * t) a b hab
      rcases h2 with h3 | h3
      · have h4 := Nat.mod_mod_of_dvd (v0 + m * n * t) (Dvd.intro n rfl : m ∣ m * n)
        rw [h3, hvm] at h4
        simp at h4
      · have h4 := Nat.mod_mod_of_dvd (v0 + m * n * t) (Dvd.intro_left m rfl : n ∣ m * n)
        rw [h3, hvn, Nat.mod_eq_of_lt (by omega : 1 < n)] at h4
        omega
