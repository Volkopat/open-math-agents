import OMAStatements.S_oeis_a378258
import Mathlib

namespace OMA.S_oeis_a378258

private lemma coeff_pow_zero_of_lt (C : PowerSeries ℤ) (hC0 : PowerSeries.constantCoeff C = 0) :
    ∀ k n, n < k → PowerSeries.coeff n (C ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    have hsum : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    by_cases h2 : ab.2 = 0
    · rw [h2, PowerSeries.coeff_zero_eq_constantCoeff, hC0, mul_zero]
    · rw [ih ab.1 (by omega), zero_mul]

private lemma coeff_pow_self (C : PowerSeries ℤ) (hC0 : PowerSeries.constantCoeff C = 0) :
    ∀ k, PowerSeries.coeff k (C ^ k) = (PowerSeries.coeff 1 C) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul]
    rw [Finset.sum_eq_single (k, 1)]
    · rw [ih]
    · intro ab hab hne
      have hsum : ab.1 + ab.2 = k + 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      by_cases h2 : ab.2 = 0
      · rw [h2, PowerSeries.coeff_zero_eq_constantCoeff, hC0, mul_zero]
      · have hlt : ab.1 < k := by
          rcases ab with ⟨a, b⟩
          by_contra hge
          apply hne
          ext <;> dsimp <;> omega
        rw [coeff_pow_zero_of_lt C hC0 k ab.1 hlt, zero_mul]
    · intro hnot
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)) hnot

private lemma coeff_pow_even_of_mod2_X (C : PowerSeries ℤ)
    (hC0 : PowerSeries.constantCoeff C = 0)
    (n : ℕ) (hC_even : ∀ m, 2 ≤ m → m < n → 2 ∣ PowerSeries.coeff m C) :
    ∀ k, 2 ≤ k → k < n → 2 ∣ PowerSeries.coeff n (C ^ k) := by
  suffices h : ∀ k, 2 ≤ k → ∀ m, k < m → m ≤ n → 2 ∣ PowerSeries.coeff m (C ^ k) by
    intro k hk hkn; exact h k hk n hkn le_rfl
  intro k
  induction k with
  | zero => intro h0; omega
  | succ k ih =>
    intro hk m hkm hmn
    cases k with
    | zero => omega
    | succ k' =>
      rw [pow_succ, PowerSeries.coeff_mul]
      refine Finset.dvd_sum fun ab hab => ?_
      have hsum : ab.1 + ab.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      by_cases hb0 : ab.2 = 0
      · rw [hb0, PowerSeries.coeff_zero_eq_constantCoeff, hC0, mul_zero]; exact dvd_zero 2
      · by_cases ha_lt : ab.1 < k' + 1
        · rw [coeff_pow_zero_of_lt C hC0 (k' + 1) ab.1 ha_lt, zero_mul]; exact dvd_zero 2
        · by_cases ha_eq : ab.1 = k' + 1
          · have hb2 : 2 ≤ ab.2 := by omega
            have hbn : ab.2 < n := by omega
            exact dvd_mul_of_dvd_right (hC_even ab.2 hb2 hbn) _
          · have h1 : 2 ∣ PowerSeries.coeff ab.1 (C ^ (k' + 1)) := by
              cases k' with
              | zero =>
                rw [pow_one]
                exact hC_even ab.1 (by omega) (by omega)
              | succ k'' =>
                exact ih (by omega) ab.1 (by omega) (by omega)
            exact dvd_mul_of_dvd_left h1 _

private lemma coeff_sq_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 2) =
      if Even n then PowerSeries.coeff (n / 2) f else 0 := by
  have hz2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hsq : ∀ x : ZMod 2, x ^ 2 = x := by decide
  have htrunc : PowerSeries.coeff n (f ^ 2) =
      PowerSeries.coeff n ((∑ k ∈ Finset.range (n + 1),
        PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k) ^ 2) := by
    set P : PowerSeries (ZMod 2) :=
      ∑ k ∈ Finset.range (n + 1), PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k
    have hdiff : ∀ k ≤ n, PowerSeries.coeff k (f - P) = 0 := by
      intro k hk
      rw [map_sub, sub_eq_zero]
      simp only [P, map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; rw [if_neg (Ne.symm hjk), mul_zero]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    have hmul0 : PowerSeries.coeff n ((f - P) * (f + P)) = 0 := by
      rw [PowerSeries.coeff_mul]
      refine Finset.sum_eq_zero fun ab hab => ?_
      have hsum : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      rw [hdiff ab.1 (by omega), zero_mul]
    have hsub : f ^ 2 - P ^ 2 = (f - P) * (f + P) := by ring
    rw [← hsub, map_sub, sub_eq_zero] at hmul0
    exact hmul0
  rw [htrunc]
  have hadd2 : ∀ a b : PowerSeries (ZMod 2), (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
    intro a b
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
      have : (2 : ZMod 2) = 0 := by decide
      rw [← map_ofNat PowerSeries.C 2, this, map_zero]
    calc (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [h2, zero_mul, add_zero]
  have hfrob : ∀ (s : Finset ℕ) (g : ℕ → PowerSeries (ZMod 2)),
      (∑ k ∈ s, g k) ^ 2 = ∑ k ∈ s, (g k) ^ 2 := by
    intro s g
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, hadd2, ih]
  rw [hfrob]
  simp only [mul_pow, ← map_pow PowerSeries.C, ← pow_mul, map_sum, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow]
  rcases Nat.even_or_odd n with ⟨q, hq⟩ | ⟨q, hq⟩
  · rw [if_pos ⟨q, hq⟩, show n / 2 = q by omega]
    rw [Finset.sum_eq_single q]
    · simp [hsq, show q * 2 = n by omega]
    · intro k _ hkq; rw [if_neg (by omega), mul_zero]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · have hne : ¬ Even n := by rw [Nat.not_even_iff_odd]; exact ⟨q, hq⟩
    rw [if_neg hne]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (by omega), mul_zero]

private theorem main_proved :
    ∀ (A B : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.coeff 1 A = 1 →
      A = B + PowerSeries.C (5 : ℤ) * A ^ 2 →
      PowerSeries.subst (A - A ^ 2) B = PowerSeries.X →
      ∀ n : ℕ, 1 ≤ n → (Odd (PowerSeries.coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  intro A B hA0 hA1 hAB hsubst
  set C : PowerSeries ℤ := A - A ^ 2
  have hBC : B = C - PowerSeries.C (4 : ℤ) * A ^ 2 := by
    have h5 : PowerSeries.C (5 : ℤ) = 1 + PowerSeries.C (4 : ℤ) := by
      rw [← map_one PowerSeries.C, ← map_add]; norm_num
    simp only [C]
    rw [h5] at hAB
    linear_combination -hAB
  have hC0 : PowerSeries.constantCoeff C = 0 := by
    simp [C, hA0]
  have hB0 : PowerSeries.constantCoeff B = 0 := by
    simp [hBC, hC0, hA0]
  have hA2_1 : PowerSeries.coeff 1 (A ^ 2) = 0 := by
    rw [pow_two, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    have hsum : ab.1 + ab.2 = 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    rcases ab with ⟨a, b⟩
    have : a = 0 ∨ b = 0 := by omega
    rcases this with rfl | rfl
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, hA0, zero_mul]
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, hA0, mul_zero]
  have hC1 : PowerSeries.coeff 1 C = 1 := by
    simp [C, hA1, hA2_1]
  have hB1 : PowerSeries.coeff 1 B = 1 := by
    rw [hBC, map_sub, PowerSeries.coeff_C_mul, hC1, hA2_1]; ring
  have hC_hs : PowerSeries.HasSubst C := PowerSeries.HasSubst.of_constantCoeff_zero hC0
  -- Prove by strong induction: ∀ n ≥ 2, 2 ∣ coeff n C
  have hC_even : ∀ n, 2 ≤ n → 2 ∣ PowerSeries.coeff n C := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have hsub_n := congr_arg (PowerSeries.coeff n) hsubst
      rw [PowerSeries.coeff_subst' hC_hs, PowerSeries.coeff_X, if_neg (by omega)] at hsub_n
      rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))] at hsub_n
      · have hmod4 : (∑ k ∈ Finset.range (n + 1),
            PowerSeries.coeff k B * PowerSeries.coeff n (C ^ k)) % 4 = 0 := by
          have : ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k B * PowerSeries.coeff n (C ^ k) = 0 := by
            simpa [smul_eq_mul] using hsub_n
          rw [this]; rfl
        have hsplit : ∑ k ∈ Finset.range (n + 1),
            PowerSeries.coeff k B * PowerSeries.coeff n (C ^ k) =
            PowerSeries.coeff n C + PowerSeries.coeff n B +
            ∑ k ∈ (Finset.range n).filter (fun k => 2 ≤ k),
              PowerSeries.coeff k B * PowerSeries.coeff n (C ^ k) := by
          rw [Finset.sum_range_succ, coeff_pow_self C hC0 n, hC1, one_pow, mul_one]
          have hfilt : ∑ k ∈ Finset.range (n - 2),
              PowerSeries.coeff (k + 2) B * PowerSeries.coeff n (C ^ (k + 2)) =
              ∑ k ∈ (Finset.range n).filter (fun k => 2 ≤ k),
                PowerSeries.coeff k B * PowerSeries.coeff n (C ^ k) := by
            refine Finset.sum_bij (fun k _ => k + 2) ?_ ?_ ?_ ?_
            · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega
            · intro k1 _ k2 _ h; omega
            · intro k hk
              simp only [Finset.mem_filter, Finset.mem_range] at hk
              exact ⟨k - 2, Finset.mem_range.mpr (by omega), by omega⟩
            · intro k _; rfl
          have hhead : ∑ k ∈ Finset.range n,
              PowerSeries.coeff k B * PowerSeries.coeff n (C ^ k) =
              PowerSeries.coeff n C +
              ∑ k ∈ Finset.range (n - 2),
                PowerSeries.coeff (k + 2) B * PowerSeries.coeff n (C ^ (k + 2)) := by
            have hrange : Finset.range n = Finset.range ((n - 2) + 1 + 1) := by congr 1; omega
            rw [hrange, Finset.sum_range_succ', Finset.sum_range_succ']
            simp only [PowerSeries.coeff_zero_eq_constantCoeff, hB0, zero_mul, add_zero,
              hB1, one_mul, pow_one]
            ring
          rw [hhead, hfilt]
          ring
        -- Simpler split without sum_range_succ' index mismatch:
        have h4mid : 4 ∣ ∑ k ∈ (Finset.range n).filter (fun k => 2 ≤ k),
            PowerSeries.coeff k B * PowerSeries.coeff n (C ^ k) := by
          refine Finset.dvd_sum fun k hk => ?_
          simp only [Finset.mem_filter, Finset.mem_range] at hk
          have h2Ck : 2 ∣ PowerSeries.coeff k C := ih k hk.1 hk.2
          have h2Bk : 2 ∣ PowerSeries.coeff k B := by
            rw [hBC, map_sub, PowerSeries.coeff_C_mul]
            exact dvd_sub h2Ck ⟨2 * PowerSeries.coeff k (A ^ 2), by ring⟩
          have h2pow : 2 ∣ PowerSeries.coeff n (C ^ k) :=
            coeff_pow_even_of_mod2_X C hC0 n (fun m hm1 hm2 => ih m hm2 hm1) k hk.2 hk.1
          obtain ⟨u, hu⟩ := h2Bk
          obtain ⟨v, hv⟩ := h2pow
          exact ⟨u * v, by rw [hu, hv]; ring⟩
        have hBn : PowerSeries.coeff n B =
            PowerSeries.coeff n C - 4 * PowerSeries.coeff n (A ^ 2) := by
          rw [hBC, map_sub, PowerSeries.coeff_C_mul]
        obtain ⟨q, hq⟩ := h4mid
        rw [hsplit, hBn, hq] at hmod4
        have : 2 ∣ PowerSeries.coeff n C := by omega
        exact this
      · intro k hk
        simp only [Function.mem_support, ne_eq] at hk
        by_contra hnot
        simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hnot
        exact hk (by rw [coeff_pow_zero_of_lt C hC0 k n (by omega), smul_zero])
  -- Now reduce C = A - A^2 mod 2: Φ2 C = X, so Φ2 A = X + (Φ2 A)^2!
  set φ2 : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  set Φ2 : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map φ2
  have hC_mod2 : Φ2 C = PowerSeries.X := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_X]
    match m with
    | 0 => rw [PowerSeries.coeff_zero_eq_constantCoeff, hC0]; simp [φ2]
    | 1 => rw [hC1]; simp [φ2]
    | k + 2 =>
      rw [if_neg (by omega)]
      obtain ⟨q, hq⟩ := hC_even (k + 2) (by omega)
      rw [hq]; simp only [φ2, map_mul, map_ofNat]
      have : (2 : ZMod 2) = 0 := by decide
      rw [this, zero_mul]
  have hA_eq_mod2 : Φ2 A = PowerSeries.X + (Φ2 A) ^ 2 := by
    have h1 : Φ2 C = Φ2 A - (Φ2 A) ^ 2 := by
      simp only [C, map_sub, map_pow]
    rw [hC_mod2] at h1
    have hadd : ∀ x y : PowerSeries (ZMod 2), x - y = x + y := by
      intro x y; ext k
      have hneg : ∀ z : ZMod 2, -z = z := by decide
      simp [sub_eq_add_neg, hneg]
    have h2 : Φ2 A = (Φ2 A - (Φ2 A) ^ 2) + (Φ2 A) ^ 2 := by ring
    rw [← h1] at h2
    exact h2
  -- Strong induction on n ≥ 1: coeff n (Φ2 A) = 1 ↔ ∃ k, n = 2^k
  have hmod2 : ∀ n, 1 ≤ n → (PowerSeries.coeff n (Φ2 A) = 1 ↔ ∃ k : ℕ, n = 2 ^ k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have hc := congr_arg (PowerSeries.coeff n) hA_eq_mod2
      rw [map_add, PowerSeries.coeff_X, coeff_sq_zmod2] at hc
      rcases Nat.even_or_odd n with ⟨q, hq⟩ | ⟨q, hq⟩
      · have hn1 : n ≠ 1 := by omega
        have hq1 : 1 ≤ q := by omega
        have hdiv : n / 2 = q := by omega
        rw [if_neg hn1, zero_add, if_pos ⟨q, hq⟩, hdiv] at hc
        rw [hc]
        have ihq : PowerSeries.coeff q (Φ2 A) = 1 ↔ ∃ k : ℕ, q = 2 ^ k := ih q (by omega) hq1
        refine ihq.trans ?_
        constructor
        · rintro ⟨k, rfl⟩; exact ⟨k + 1, by rw [pow_succ]; omega⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => omega
          | succ k' => exact ⟨k', by rw [pow_succ] at hk; omega⟩
      · cases q with
        | zero =>
          have hn1 : n = 1 := by omega
          subst hn1
          have hne : ¬ Even 1 := by decide
          rw [if_pos rfl, if_neg hne, add_zero] at hc
          rw [hc]
          exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
        | succ r =>
          have hn1 : n ≠ 1 := by omega
          have hne : ¬ Even n := by rw [Nat.not_even_iff_odd]; exact ⟨r + 1, hq⟩
          rw [if_neg hn1, if_neg hne, add_zero] at hc
          rw [hc]
          constructor
          · intro h01; exact absurd h01 (by decide)
          · rintro ⟨k, hk⟩
            cases k with
            | zero => omega
            | succ k' =>
              have h2 : 2 ∣ n := ⟨2 ^ k', by rw [hk, pow_succ]; ring⟩
              omega
  intro n hn
  have h1 := hmod2 n hn
  rw [PowerSeries.coeff_map] at h1
  have hodd : Odd (PowerSeries.coeff n A) ↔ φ2 (PowerSeries.coeff n A) = 1 := by
    rw [Int.odd_iff]
    constructor
    · intro h
      have hdiv := Int.emod_add_mul_ediv (PowerSeries.coeff n A) 2
      have : PowerSeries.coeff n A = 1 + 2 * (PowerSeries.coeff n A / 2) := by
        rw [← h]; exact hdiv.symm
      rw [this]; simp only [φ2, map_add, map_one, map_mul, map_ofNat]
      have : (2 : ZMod 2) = 0 := by decide
      rw [this, zero_mul, add_zero]
    · intro h
      have hmod := (ZMod.intCast_eq_intCast_iff (PowerSeries.coeff n A) 1 2).mp (by simpa [φ2] using h)
      rw [Int.ModEq] at hmod; norm_num at hmod; exact hmod
  exact hodd.trans h1

end OMA.S_oeis_a378258

theorem OMA.solution : type_of% @OMA.S_oeis_a378258.main :=
  OMA.S_oeis_a378258.main_proved
