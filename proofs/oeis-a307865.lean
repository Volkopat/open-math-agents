import OMAStatements.S_oeis_a307865

-- Problem: A307865: a(n) is the number of natural bases b < 2n+1 such that b^n == -1 (mod 2n+1).
-- Upstream: formal-conjectures statements/oeis-a307865.lean:0 (declaration OMA.S_oeis_a307865.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (the argument recorded in the entry): let N = 2n+1 and suppose b^n = -1 mod N.
-- Then b is a unit. Write N = p^e * m with p prime and p not dividing m. If m > 1, the CRT
-- number c with c = b mod p^e and c = 1 mod m is coprime to N, and c^n = -1 mod p^e but
-- c^n = 1 mod m, so c^n is neither 1 nor -1 mod N (both moduli are odd and > 1). If m = 1, then
-- e >= 2, y = p^(e-1) has y^2 = 0 mod N, and (1+y)^n = 1 + n*y, which is 1 only if p divides n
-- and -1 only if p divides 2; both contradict p | 2n+1.

open OMA.S_oeis_a307865 in
theorem OMA.solution : type_of% @OMA.S_oeis_a307865.main := by
  intro n hN
  obtain ⟨_, h1, hnp, hE⟩ := hN
  rw [show (2 * n + 1 - 1) / 2 = n by omega] at hE
  have hn0 : n ≠ 0 := by omega
  have key : ∀ d : ℕ, 1 < d → d ∣ 2 * n + 1 → (1 : ZMod d) ≠ -1 := by
    intro d hd hdN heq
    have h2 : ((2 : ℕ) : ZMod d) = 0 := by
      push_cast
      linear_combination heq
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hle : d ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have hd2 : d = 2 := by omega
    rw [hd2] at hdN
    obtain ⟨t, ht⟩ := hdN
    omega
  have down1 : ∀ d : ℕ, d ∣ 2 * n + 1 → ∀ x : ℕ,
      (x : ZMod (2 * n + 1)) ^ n = 1 → (x : ZMod d) ^ n = 1 := by
    intro d hd x hx
    have h := congrArg (ZMod.castHom hd (ZMod d)) hx
    rw [map_pow, map_natCast, map_one] at h
    exact h
  have downm : ∀ d : ℕ, d ∣ 2 * n + 1 → ∀ x : ℕ,
      (x : ZMod (2 * n + 1)) ^ n = -1 → (x : ZMod d) ^ n = -1 := by
    intro d hd x hx
    have h := congrArg (ZMod.castHom hd (ZMod d)) hx
    rw [map_pow, map_natCast, map_neg, map_one] at h
    exact h
  unfold a
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _ hbn
  have hbunit : IsUnit (b : ZMod (2 * n + 1)) := by
    have hu : IsUnit ((b : ZMod (2 * n + 1)) ^ n) := by
      rw [hbn]
      exact isUnit_one.neg
    exact (isUnit_pow_iff hn0).mp hu
  have hbcop : Nat.Coprime b (2 * n + 1) := (ZMod.isUnit_iff_coprime b (2 * n + 1)).mp hbunit
  obtain ⟨p, hp, hpN⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ 2 * n + 1 :=
    ⟨(2 * n + 1).minFac, Nat.minFac_prime (show 2 * n + 1 ≠ 1 by omega), Nat.minFac_dvd _⟩
  obtain ⟨e, m, hpm, hNem⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show 2 * n + 1 ≠ 0 by omega) p hp.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hNem
    rw [hNem] at hpN
    exact hpm hpN
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hNem
    omega
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  · have hA1 : 1 < p ^ e := one_lt_pow₀ hp.one_lt he
    have hcop : Nat.Coprime (p ^ e) m :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
    have hAdvd : p ^ e ∣ 2 * n + 1 := ⟨m, hNem⟩
    have hBdvd : m ∣ 2 * n + 1 := ⟨p ^ e, by rw [hNem, mul_comm]⟩
    obtain ⟨c, hcA, hcB⟩ := Nat.chineseRemainder hcop b 1
    have hc1 : Nat.Coprime c (p ^ e) := by
      have hg := Nat.ModEq.gcd_eq hcA
      have hb1 : Nat.Coprime b (p ^ e) := Nat.Coprime.coprime_dvd_right hAdvd hbcop
      show Nat.gcd c (p ^ e) = 1
      rw [hg]
      exact hb1
    have hc2 : Nat.Coprime c m := by
      have hg := Nat.ModEq.gcd_eq hcB
      show Nat.gcd c m = 1
      rw [hg, Nat.gcd_one_left]
    have hcN : Nat.Coprime c (2 * n + 1) := by
      rw [hNem]
      exact Nat.Coprime.mul_right hc1 hc2
    have hcA' : (c : ZMod (p ^ e)) = (b : ZMod (p ^ e)) :=
      (ZMod.natCast_eq_natCast_iff c b (p ^ e)).mpr hcA
    have hcB' : (c : ZMod m) = ((1 : ℕ) : ZMod m) :=
      (ZMod.natCast_eq_natCast_iff c 1 m).mpr hcB
    have hbA : (b : ZMod (p ^ e)) ^ n = -1 := downm (p ^ e) hAdvd b hbn
    rcases hE c hcN with hc | hc
    · have h1A := down1 (p ^ e) hAdvd c hc
      rw [hcA', hbA] at h1A
      exact key (p ^ e) hA1 hAdvd h1A.symm
    · have hmB := downm m hBdvd c hc
      rw [hcB', Nat.cast_one, one_pow] at hmB
      exact key m hm1 hBdvd hmB
  · have hm : m = 1 := by omega
    rw [hm, mul_one] at hNem
    have he2 : 2 ≤ e := by
      rcases Nat.lt_or_ge e 2 with h | h
      · have he1 : e = 1 := by omega
        rw [he1, pow_one] at hNem
        rw [hNem] at hnp
        exact absurd hp hnp
      · exact h
    have hcop : Nat.Coprime (1 + p ^ (e - 1)) (2 * n + 1) := by
      rw [hNem]
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      have hpy : p ∣ p ^ (e - 1) := dvd_pow_self p (by omega)
      rw [add_comm] at hdvd
      have hp1 : p ∣ 1 := (Nat.dvd_add_right hpy).mp hdvd
      have := Nat.le_of_dvd one_pos hp1
      have := hp.two_le
      omega
    have hy2 : ((p ^ (e - 1) : ℕ) : ZMod (2 * n + 1)) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ← pow_mul, ZMod.natCast_eq_zero_iff, hNem]
      exact pow_dvd_pow p (by omega)
    have hbin : ∀ t : ℕ, ((1 + p ^ (e - 1) : ℕ) : ZMod (2 * n + 1)) ^ t =
        1 + (t : ZMod (2 * n + 1)) * ((p ^ (e - 1) : ℕ) : ZMod (2 * n + 1)) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        rw [pow_succ, ih]
        push_cast at hy2 ⊢
        linear_combination (t : ZMod (2 * n + 1)) * hy2
    have hval := hbin n
    rcases hE (1 + p ^ (e - 1)) hcop with hc | hc
    · rw [hval] at hc
      have h0 : ((n * p ^ (e - 1) : ℕ) : ZMod (2 * n + 1)) = 0 := by
        push_cast at hc ⊢
        linear_combination hc
      rw [ZMod.natCast_eq_zero_iff, hNem] at h0
      have hpe : p ^ e = p ^ (e - 1) * p := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ e)]
      rw [hpe, mul_comm n] at h0
      have hpn : p ∣ n := (mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)).mp h0
      have hp1 : p ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_left hpn 2)).mp hpN
      have := Nat.le_of_dvd one_pos hp1
      have := hp.two_le
      omega
    · rw [hval] at hc
      have h0 : ((2 + n * p ^ (e - 1) : ℕ) : ZMod (2 * n + 1)) = 0 := by
        push_cast at hc ⊢
        linear_combination hc
      rw [ZMod.natCast_eq_zero_iff, hNem] at h0
      have hp1 : p ∣ p ^ e := dvd_pow_self p he
      have hp2 : p ∣ n * p ^ (e - 1) := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) n
      have hp3 : p ∣ 2 := (Nat.dvd_add_left hp2).mp (dvd_trans hp1 h0)
      have hp4 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp3
      have hp5 : p = 2 := by
        have := hp.two_le
        omega
      rw [hp5] at hpN
      obtain ⟨t, ht⟩ := hpN
      omega
