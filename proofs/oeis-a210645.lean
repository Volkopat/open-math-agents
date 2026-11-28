import OMAStatements.S_oeis_a210645

-- Problem: A210645: Area A of the triangles such that A, the sides and one of the altitudes are four consecutive integers of an arithmetic progression d.
-- Upstream: formal-conjectures statements/oeis-a210645.lean:0 (declaration OMA.S_oeis_a210645.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: Heron gives 16 A^2 = 3q^2 (q-2d)(q+2d). With 2A = (q-2d) s this becomes
-- (q-2d) F(q,d) = 0, where F = q^2 (q - 14d) for s = q, F = q^3 - 6q^2 d - 12q d^2 - 8d^3 for
-- s = q+d and F = q^3 - 22q^2 d + 20q d^2 - 8d^3 for s = q-d. The two cubics have no roots with
-- q, d > 0: divide by gcd(q,d), then d | q^3 with gcd 1 forces d = 1, and then q | 8 leaves eight
-- cases. So q = 14d and A = 84 d^2, and every 84 m^2 (m >= 1) occurs (sides 15m, 14m, 13m,
-- altitude 12m). Hence the n-th area is 84 n^2 (Nat.nth_comp_of_strictMono), and the recurrence
-- and the g.f. follow by ring and by comparing coefficients.

open OMA.S_oeis_a210645 in
theorem OMA.solution : type_of% @OMA.S_oeis_a210645.main := by
  have desc : ∀ b c e : ℤ, (∀ x : ℤ, 0 < x → x ^ 3 + b * x ^ 2 + c * x + e ≠ 0) →
      ∀ q d : ℤ, 0 < q → 0 < d → q ^ 3 + b * q ^ 2 * d + c * q * d ^ 2 + e * d ^ 3 ≠ 0 := by
    intro b c e h1 q d hq hd hF
    obtain ⟨g, q', d', hg, hcop, rfl, rfl⟩ :=
      Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left d hq.ne')
    have hg' : (0 : ℤ) < g := by exact_mod_cast hg
    have hq' : 0 < q' := by nlinarith
    have hd' : 0 < d' := by nlinarith
    have h3 : (g : ℤ) ^ 3 * (q' ^ 3 + b * q' ^ 2 * d' + c * q' * d' ^ 2 + e * d' ^ 3) = 0 := by
      linear_combination hF
    have hF' : q' ^ 3 + b * q' ^ 2 * d' + c * q' * d' ^ 2 + e * d' ^ 3 = 0 :=
      (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 3 hg'.ne')
    have hdvd : d' ∣ q' ^ 3 :=
      ⟨-(b * q' ^ 2 + c * q' * d' + e * d' ^ 2), by linear_combination hF'⟩
    have hco : IsCoprime d' (q' ^ 3) := (Int.isCoprime_iff_gcd_eq_one.mpr hcop).symm.pow_right
    have hu : IsUnit d' := hco.isUnit_of_dvd' (dvd_refl d') hdvd
    rcases Int.isUnit_iff.mp hu with h | h
    · subst h
      exact h1 q' hq' (by linear_combination hF')
    · omega
  have r2 : ∀ x : ℤ, 0 < x → x ^ 3 + (-6) * x ^ 2 + (-12) * x + (-8) ≠ 0 := by
    intro x hx h
    have h8 : x ∣ 8 := ⟨x ^ 2 - 6 * x - 12, by linear_combination (-1 : ℤ) * h⟩
    have hx8 : x ≤ 8 := Int.le_of_dvd (by norm_num) h8
    interval_cases x <;> norm_num at h
  have r3 : ∀ x : ℤ, 0 < x → x ^ 3 + (-22) * x ^ 2 + 20 * x + (-8) ≠ 0 := by
    intro x hx h
    have h8 : x ∣ 8 := ⟨x ^ 2 - 22 * x + 20, by linear_combination (-1 : ℤ) * h⟩
    have hx8 : x ≤ 8 := Int.le_of_dvd (by norm_num) h8
    interval_cases x <;> norm_num at h
  have char : ∀ A : ℕ, IsArea A ↔ ∃ m : ℕ, 0 < m ∧ A = 84 * m ^ 2 := by
    intro A
    unfold IsArea
    constructor
    · rintro ⟨q, d, hd, hq, hH, hs⟩
      simp only [heron] at hH
      have hh : 0 < q - 2 * d := by linarith
      have hq0 : 0 < q := by linarith
      rcases hs with hs | hs | hs
      · exfalso
        have h1 : (q - 2 * d) *
            (q ^ 3 + (-6) * q ^ 2 * d + (-12) * q * d ^ 2 + (-8) * d ^ 3) = 0 := by
          linear_combination hH + (-4 * (2 * (A : ℤ) + (q - 2 * d) * (q + d))) * hs
        exact desc (-6) (-12) (-8) r2 q d hq0 hd ((mul_eq_zero.mp h1).resolve_left hh.ne')
      · have h1 : q ^ 2 * (q - 2 * d) * (q - 14 * d) = 0 := by
          linear_combination hH + (-4 * (2 * (A : ℤ) + (q - 2 * d) * q)) * hs
        have h14 : q - 14 * d = 0 :=
          (mul_eq_zero.mp h1).resolve_left (mul_ne_zero (pow_ne_zero 2 hq0.ne') hh.ne')
        refine ⟨d.toNat, by omega, ?_⟩
        have hdn : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd.le
        have h2A : 2 * (A : ℤ) = 2 * (84 * d ^ 2) := by
          linear_combination hs + (q + 12 * d) * h14
        have hA : (A : ℤ) = 84 * ((d.toNat : ℕ) : ℤ) ^ 2 := by
          rw [hdn]
          linarith
        exact_mod_cast hA
      · exfalso
        have h1 : (q - 2 * d) *
            (q ^ 3 + (-22) * q ^ 2 * d + 20 * q * d ^ 2 + (-8) * d ^ 3) = 0 := by
          linear_combination hH + (-4 * (2 * (A : ℤ) + (q - 2 * d) * (q - d))) * hs
        exact desc (-22) 20 (-8) r3 q d hq0 hd ((mul_eq_zero.mp h1).resolve_left hh.ne')
    · rintro ⟨m, hm, rfl⟩
      have hm' : (0 : ℤ) < m := by exact_mod_cast hm
      refine ⟨14 * (m : ℤ), (m : ℤ), hm', by linarith, ?_, Or.inr (Or.inl ?_)⟩
      · simp only [heron]
        push_cast
        ring
      · push_cast
        ring
  have hf : StrictMono (fun i : ℕ => 84 * (i + 1) ^ 2) := by
    intro i j hij
    have h1 : (i + 1) ^ 2 < (j + 1) ^ 2 :=
      pow_lt_pow_left₀ (by omega) (Nat.zero_le _) (by norm_num)
    show 84 * (i + 1) ^ 2 < 84 * (j + 1) ^ 2
    linarith
  have hall : ∀ i : ℕ, IsArea (84 * (i + 1) ^ 2) := fun i => (char _).2 ⟨i + 1, by omega, rfl⟩
  have h0 : ∀ k, IsArea k → k ∈ Set.range (fun i : ℕ => 84 * (i + 1) ^ 2) := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := (char k).1 hk
    refine Set.mem_range.mpr ⟨m - 1, ?_⟩
    show 84 * (m - 1 + 1) ^ 2 = 84 * m ^ 2
    rw [show m - 1 + 1 = m by omega]
  have hinf : (Set.ofPred IsArea).Infinite := by
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hf.injective)
    rintro _ ⟨i, rfl⟩
    exact hall i
  have hnth : ∀ n : ℕ, Nat.nth IsArea n = 84 * (n + 1) ^ 2 := by
    intro n
    have h : 84 * (Nat.nth (fun i => IsArea (84 * (i + 1) ^ 2)) n + 1) ^ 2 = Nat.nth IsArea n :=
      Nat.nth_comp_of_strictMono (p := IsArea) (n := n) hf h0 (fun hfi => absurd hfi hinf)
    rw [Nat.nth_of_forall (fun k _ => hall k)] at h
    exact h.symm
  have ha : ∀ n : ℕ, 1 ≤ n → a n = 84 * n ^ 2 := by
    intro n hn
    show Nat.nth IsArea (n - 1) = 84 * n ^ 2
    rw [hnth, Nat.sub_add_cancel hn]
  have hb : ∀ m : ℕ, (if m = 0 then (0 : ℚ) else (a m : ℚ)) = 84 * (m : ℚ) ^ 2 := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp
    · rw [if_neg (show ¬(m = 0) by omega), ha m (by omega)]
      push_cast
      ring
  refine ⟨ha, fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, ha (m + 4) (by omega), ha (m + 3) (by omega),
      ha (m + 2) (by omega), ha (m + 1) (by omega)]
    push_cast
    ring
  · have hmk : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
        PowerSeries.mk (fun n => 84 * (n : ℚ) ^ 2) := congrArg PowerSeries.mk (funext hb)
    rw [hmk]
    have e1 : PowerSeries.mk (fun n => 84 * (n : ℚ) ^ 2) * (1 - PowerSeries.X) ^ 3 =
        PowerSeries.mk (fun n => 84 * (n : ℚ) ^ 2)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
            (PowerSeries.mk (fun n => 84 * (n : ℚ) ^ 2) * PowerSeries.X ^ 2)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
            (PowerSeries.mk (fun n => 84 * (n : ℚ) ^ 2) * PowerSeries.X ^ 1)
          - PowerSeries.mk (fun n => 84 * (n : ℚ) ^ 2) * PowerSeries.X ^ 3 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3]
      ring
    have e2 : (84 * PowerSeries.X * (1 + PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84
          + PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84]
      ring
    rw [e1, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [if_pos (show 2 ≤ k + 3 by omega), if_pos (show 1 ≤ k + 3 by omega),
        if_pos (show 3 ≤ k + 3 by omega), if_neg (show ¬(k + 3 = 1) by omega),
        if_neg (show ¬(k + 3 = 2) by omega), show k + 3 - 2 = k + 1 by omega,
        show k + 3 - 1 = k + 2 by omega, show k + 3 - 3 = k by omega]
      push_cast
      ring
