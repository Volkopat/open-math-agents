import OMAStatements.S_mo_46445

/-!
Two consecutive unit intervals cannot both contain zeros when the finite cotangent sum has no
pole at their shared endpoint and its summation range is constant across both intervals.
The prime configurations in `H1` supply such endpoints. Once those configurations stop
occurring, both endpoints of each sufficiently large unit interval are poles and there is
a zero in between.
-/

namespace OMA.R_mo_46445_R1

open Real Set Filter
open scoped Topology

/-- Arbitrarily large primes followed two steps later by a prime or a prime square. -/
def H1 : Prop :=
  ∀ B : ℕ, ∃ k ≥ B, k.Prime ∧ ((k + 2).Prime ∨ ∃ p : ℕ, p.Prime ∧ k + 2 = p ^ 2)

/-- Strict decrease of a shifted cotangent on an interval with no poles. -/
def H2 : Prop :=
  ∀ a b c t : ℝ, 0 < t → (∀ x ∈ Ioo a b, sin ((x + c) * t) ≠ 0) →
    StrictAntiOn (fun x => cot ((x + c) * t)) (Ioo a b)

lemma floor_sqrt_center {k : ℕ} (hk : k.sqrt ^ 2 < k) {x : ℝ}
    (hx : x ∈ Ioo ((k : ℝ) - 1) ((k : ℝ) + 1)) : ⌊sqrt x⌋₊ = k.sqrt := by
  have hlo : ((k.sqrt : ℝ) ^ 2) + 1 ≤ (k : ℝ) := by
    exact_mod_cast (show k.sqrt ^ 2 + 1 ≤ k by omega)
  have hhi : (k : ℝ) + 1 ≤ ((k.sqrt : ℝ) + 1) ^ 2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' k)
  refine (Nat.floor_eq_iff (sqrt_nonneg x)).mpr ⟨?_, ?_⟩
  · rw [← sqrt_sq (Nat.cast_nonneg k.sqrt)]
    exact sqrt_le_sqrt (by linarith only [hx.1, hlo])
  · exact (sqrt_lt' (by positivity)).mpr (hx.2.trans_le hhi)

private lemma integer_of_sine_zero {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hs : sin (u * (π / n)) = 0) :
    ∃ z : ℤ, u = (z : ℝ) * (n : ℝ) := by
  obtain ⟨z, hz⟩ := sin_eq_zero_iff.mp hs
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_div_assoc] at hz
  have hmul := (eq_div_iff hnR).mp hz
  refine ⟨z, mul_right_cancel₀ pi_ne_zero ?_⟩
  linear_combination -hmul

private lemma sine_ne_center {k n c : ℕ} (hn : 0 < n) (hnd : ¬ n ∣ k + c)
    {x : ℝ} (hx : x ∈ Ioo ((k : ℝ) - 1) ((k : ℝ) + 1)) :
    sin ((x + (c : ℝ)) * (π / n)) ≠ 0 := by
  intro h
  obtain ⟨z, hz⟩ := integer_of_sine_zero hn h
  have hlo : (k : ℤ) + (c : ℤ) - 1 < z * (n : ℤ) := by
    exact_mod_cast (show (k : ℝ) + (c : ℝ) - 1 < (z : ℝ) * (n : ℝ) from
      by linarith only [hx.1, hz])
  have hhi : z * (n : ℤ) < (k : ℤ) + (c : ℤ) + 1 := by
    exact_mod_cast (show (z : ℝ) * (n : ℝ) < (k : ℝ) + (c : ℝ) + 1 from
      by linarith only [hx.2, hz])
  have hint : z * (n : ℤ) = (k : ℤ) + (c : ℤ) := by omega
  apply hnd
  exact Int.natCast_dvd_natCast.mp ⟨z, by simpa [mul_comm] using hint.symm⟩

private lemma no_small_divisor {k : ℕ} (hk : k.Prime)
    (hk2 : (k + 2).Prime ∨ ∃ p : ℕ, p.Prime ∧ k + 2 = p ^ 2) {n : ℕ}
    (hn : n ∈ Finset.Icc 2 k.sqrt) : (¬ n ∣ k) ∧ (¬ n ∣ k + 2) := by
  rcases Finset.mem_Icc.mp hn with ⟨hn2, hnle⟩
  have hnk : n < k := hnle.trans_lt (Nat.sqrt_lt_self hk.one_lt)
  refine ⟨fun hd => hnk.ne ((Nat.dvd_prime_two_le hk hn2).mp hd), ?_⟩
  intro hd
  rcases hk2 with hprime | ⟨p, hp, hsq⟩
  · exact (show n < k + 2 by omega).ne ((Nat.dvd_prime_two_le hprime hn2).mp hd)
  · have hnp : n < p := hnle.trans_lt (Nat.sqrt_lt'.mpr (by omega : k < p ^ 2))
    rw [hsq] at hd
    obtain ⟨e, he, heq⟩ := (Nat.dvd_prime_pow hp).mp hd
    have hpos : 1 ≤ e := by
      by_contra! h
      have he0 : e = 0 := by omega
      simp [he0] at heq
      omega
    have hle : p ≤ n := by
      rw [heq]
      simpa only [pow_one] using (pow_le_pow_right₀ hp.one_lt.le hpos)
    exact hnp.not_ge hle

private lemma sum_strictAnti (hcot : H2) {k : ℕ} (hk4 : 4 ≤ k) (hsq : k.sqrt ^ 2 < k)
    (hnp : ∀ n ∈ Finset.Icc 2 k.sqrt, (¬ n ∣ k) ∧ (¬ n ∣ k + 2)) :
    StrictAntiOn OMA.S_mo_46445.h (Ioo ((k : ℝ) - 1) ((k : ℝ) + 1)) := by
  intro x hx y hy hxy
  unfold OMA.S_mo_46445.h
  rw [floor_sqrt_center hsq hx, floor_sqrt_center hsq hy]
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_sqrt'.mpr (by simpa using hk4)⟩⟩
  · intro n hn
    have hn0 : 0 < n := lt_of_lt_of_le (by decide) (Finset.mem_Icc.mp hn).1
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
    have ht : 0 < π / (n : ℝ) := div_pos pi_pos hnR
    have h0 := hcot ((k : ℝ) - 1) ((k : ℝ) + 1) 0 (π / n) ht
      (fun z hz => by simpa using sine_ne_center (c := 0) hn0 (by simpa using (hnp n hn).1) hz)
      hx hy hxy
    have h2 := hcot ((k : ℝ) - 1) ((k : ℝ) + 1) 2 (π / n) ht
      (fun z hz => by simpa using sine_ne_center (c := 2) hn0 (hnp n hn).2 hz)
      hx hy hxy
    simpa only [add_zero, mul_div_assoc] using div_lt_div_of_pos_right (add_lt_add h0 h2) hnR

theorem main : H1 → H2 → type_of% @OMA.S_mo_46445.main := by
  intro centers cotAnti
  rintro ⟨N, hN⟩
  obtain ⟨k, hk, hp, hp2⟩ := centers (max 4 (N + 1))
  have hk4 : 4 ≤ k := (le_max_left _ _).trans hk
  have hkN : N + 1 ≤ k := (le_max_right _ _).trans hk
  have hsq : k.sqrt ^ 2 < k := by
    refine lt_of_le_of_ne (Nat.sqrt_le' k) ?_
    intro he
    exact (Nat.prime_iff.mp hp).not_isSquare ⟨k.sqrt, by simpa [pow_two] using he.symm⟩
  have anti := sum_strictAnti cotAnti hk4 hsq (fun _ hn => no_small_divisor hp hp2 hn)
  obtain ⟨x, hxl, hxu, hx0⟩ := hN (k - 1) (by omega)
  obtain ⟨y, hyl, hyu, hy0⟩ := hN k (by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at hxl hxu
  have hx : x ∈ Ioo ((k : ℝ) - 1) ((k : ℝ) + 1) := ⟨hxl, by linarith only [hxu]⟩
  have hy : y ∈ Ioo ((k : ℝ) - 1) ((k : ℝ) + 1) := ⟨by linarith only [hyl], hyu⟩
  have hxy : x < y := by linarith only [hxu, hyl]
  have hlt := anti hx hy hxy
  rw [hx0, hy0] at hlt
  exact (lt_irrefl (0 : ℝ)) hlt

/-- Within two of the next square, a composite with no small factor must be a prime square. -/
private lemma prime_or_square_of_no_small_factor {m n : ℕ} (hm : 2 ≤ m) (hn : 1 < n)
    (hbound : n ≤ (m + 1) ^ 2 + 2) (hfree : ∀ d ∈ Finset.Icc 2 m, ¬ d ∣ n) :
    n.Prime ∨ ∃ p : ℕ, p.Prime ∧ n = p ^ 2 ∧ m < p := by
  by_cases hprime : n.Prime
  · exact Or.inl hprime
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ n := Nat.minFac_dvd n
  have hm_lt : m < p := by
    by_contra! h
    exact hfree p (Finset.mem_Icc.mpr ⟨hp.two_le, h⟩) hpd
  have hsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hprime
  obtain ⟨q, heq⟩ := hpd
  have hpq : p ≤ q := by
    by_contra! h
    have hlt := Nat.mul_lt_mul_of_pos_left h hp.pos
    rw [← heq, ← pow_two] at hlt
    exact hlt.not_ge hsq
  have hqp : q = p := by
    by_contra h
    have hab := Nat.pow_le_pow_left (show m + 1 ≤ p by omega) 2
    have hbig : p ^ 2 + p ≤ n := by
      calc
        _ = p * (p + 1) := by ring
        _ ≤ p * q := Nat.mul_le_mul_left _ (by omega)
        _ = n := heq.symm
    omega
  exact Or.inr ⟨p, hp, by simpa [hqp, pow_two] using heq, hm_lt⟩

/-- If the unshifted argument is a prime square, the shifted argument supplies a pole at 3. -/
private lemma endpoint_divisor {m k : ℕ} (hm : 3 ≤ m) (hk : 1 < k)
    (hbound : k ≤ (m + 1) ^ 2)
    (hpair : ¬ (k.Prime ∧ ((k + 2).Prime ∨ ∃ p : ℕ, p.Prime ∧ k + 2 = p ^ 2))) :
    ∃ d ∈ Finset.Icc 2 m, d ∣ k ∨ d ∣ k + 2 := by
  by_contra h
  have h₁ (d : ℕ) (hd : d ∈ Finset.Icc 2 m) : ¬ d ∣ k :=
    fun hdiv => h ⟨d, hd, Or.inl hdiv⟩
  have h₂ (d : ℕ) (hd : d ∈ Finset.Icc 2 m) : ¬ d ∣ k + 2 :=
    fun hdiv => h ⟨d, hd, Or.inr hdiv⟩
  rcases prime_or_square_of_no_small_factor (by omega) hk (by omega) h₁ with hp | ⟨p, hp, hsq, hmp⟩
  · refine hpair ⟨hp, ?_⟩
    rcases prime_or_square_of_no_small_factor (by omega) (by omega : 1 < k + 2)
        (by omega : k + 2 ≤ (m + 1) ^ 2 + 2) h₂ with hq | ⟨q, hq, he, _⟩
    · exact Or.inl hq
    · exact Or.inr ⟨q,hq,he⟩
  · have hp3 : ¬ 3 ∣ p := by
      intro hd
      have he := (Nat.dvd_prime_two_le hp (by decide : 2 ≤ 3)).mp hd
      omega
    have hp0 : p % 3 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hp3
    have hp12 : p % 3 = 1 ∨ p % 3 = 2 := by omega
    have hd : 3 ∣ p ^ 2 + 2 := by
      rw [Nat.dvd_iff_mod_eq_zero, pow_two, Nat.add_mod, Nat.mul_mod]
      rcases hp12 with h1 | h2
      · norm_num [h1]
      · norm_num [h2]
    exact h₂ 3 (Finset.mem_Icc.mpr ⟨by decide, hm⟩) (by simpa [hsq] using hd)

private lemma sine_ne_unit {k n c : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Ioo (k : ℝ) ((k : ℝ) + 1)) :
    sin ((x + (c : ℝ)) * (π / n)) ≠ 0 := by
  intro hs
  obtain ⟨z, hz⟩ := integer_of_sine_zero hn hs
  have hlo : (k : ℤ) + (c : ℤ) < z * (n : ℤ) := by
    exact_mod_cast (show (k : ℝ) + (c : ℝ) < (z : ℝ) * (n : ℝ) from
      by linarith only [hx.1, hz])
  have hhi : z * (n : ℤ) < (k : ℤ) + (c : ℤ) + 1 := by
    exact_mod_cast (show (z : ℝ) * (n : ℝ) < (k : ℝ) + (c : ℝ) + 1 from
      by linarith only [hx.2, hz])
  omega

private lemma cot_add_nat_mul_pi (x : ℝ) (j : ℕ) :
    cot (x + (j : ℝ) * π) = cot x := by
  have hcot (y : ℝ) : cot y = (tan y)⁻¹ := by rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos, inv_div]
  simp only [hcot, tan_add_nat_mul_pi]

private lemma scaled_cot_limit {d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun t : ℝ => t * cot (t * d)) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / d)) := by
  have hsin : HasDerivAt (fun t : ℝ => sin (t * d)) d 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const d).sin)
  have hslope : Tendsto (fun t : ℝ => sin (t * d) / t) (𝓝[≠] (0 : ℝ)) (𝓝 d) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hsin.tendsto_slope_zero
  have hcos : ContinuousAt (fun t : ℝ => cos (t * d)) 0 := by fun_prop
  have hc : Tendsto (fun t : ℝ => cos (t * d)) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa using hcos.tendsto.mono_left nhdsWithin_le_nhds
  convert hc.div hslope hd using 1
  ext t
  change t * cot (t * d) = cos (t * d) / (sin (t * d) / t)
  rw [cot_eq_cos_div_sin, div_div_eq_mul_div, mul_comm (cos (t * d)) t, mul_div_assoc]

/-- A summand contributes residue `1 / π` at its poles, and zero at other integers. -/
private lemma offset_residue (K c : ℕ) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun t : ℝ => t * (cot (((K : ℝ) + t + (c : ℝ)) * (π / n)) / n))
      (𝓝[≠] (0 : ℝ)) (𝓝 (if n ∣ K + c then 1 / π else 0)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  by_cases hdiv : n ∣ K + c
  · obtain ⟨j, hj⟩ := hdiv
    have hjR : (K : ℝ) + (c : ℝ) = (n : ℝ) * (j : ℝ) := by exact_mod_cast hj
    have he (t : ℝ) :
        ((K : ℝ) + t + (c : ℝ)) * (π / n) = t * (π / n) + (j : ℝ) * π := by
      rw [show (K : ℝ) + t + (c : ℝ) = ((K : ℝ) + (c : ℝ)) + t by ring, hjR]
      field_simp [hnR]
      ring
    have hr : (1 / (π / (n : ℝ))) / (n : ℝ) = 1 / π := by
      field_simp [pi_ne_zero]
    simpa only [if_pos (show n ∣ K + c from ⟨j, hj⟩), he, cot_add_nat_mul_pi, mul_div_assoc, hr]
      using (scaled_cot_limit (div_ne_zero pi_ne_zero hnR)).div_const (n : ℝ)
  · have hsin : sin (((K : ℝ) + 0 + (c : ℝ)) * (π / n)) ≠ 0 := by
      intro hs
      obtain ⟨z, hz⟩ := integer_of_sine_zero hn hs
      have hzI : (K : ℤ) + (c : ℤ) = z * (n : ℤ) := by
        exact_mod_cast (show (K : ℝ) + (c : ℝ) = (z : ℝ) * (n : ℝ) by simpa using hz)
      apply hdiv
      exact Int.natCast_dvd_natCast.mp ⟨z, by simpa [mul_comm] using hzI⟩
    have hcos : ContinuousAt (fun t : ℝ => cos (((K : ℝ) + t + (c : ℝ)) * (π / n))) 0 :=
      by fun_prop
    have hsinCont : ContinuousAt (fun t : ℝ => sin (((K : ℝ) + t + (c : ℝ)) * (π / n))) 0 :=
      by fun_prop
    have hcont : ContinuousAt
        (fun t : ℝ => cot (((K : ℝ) + t + (c : ℝ)) * (π / n)) / n) 0 := by
      simp only [cot_eq_cos_div_sin]
      exact (hcos.div hsinCont hsin).div_const (n : ℝ)
    have hmul : ContinuousAt
        (fun t : ℝ => t * (cot (((K : ℝ) + t + (c : ℝ)) * (π / n)) / n)) 0 :=
      continuousAt_id.mul hcont
    simpa only [if_neg hdiv, zero_mul] using
      hmul.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)


private lemma scaled_sum_eventually_pos {m K : ℕ}
    (hPole : ∃ n ∈ Finset.Icc 2 m, n ∣ K ∨ n ∣ K + 2) :
    let f (x : ℝ) := ∑ n ∈ Finset.Icc 2 m, (cot (x * (π / n)) + cot ((x + 2) * (π / n))) / n
    ∀ᶠ t : ℝ in 𝓝[≠] 0, 0 < t * f ((K : ℝ) + t) := by
  intro f
  let residue (n : ℕ) : ℝ :=
    (if n ∣ K then 1 / π else 0) + (if n ∣ K + 2 then 1 / π else 0)
  have hlim : Tendsto (fun t : ℝ => t * f ((K : ℝ) + t)) (𝓝[≠] (0 : ℝ))
      (𝓝 (∑ n ∈ Finset.Icc 2 m, residue n)) := by
    simp only [f, Finset.mul_sum, add_div, mul_add]
    apply tendsto_finsetSum
    intro n hn
    have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    simpa only [residue, add_zero, Nat.cast_zero, Nat.cast_ofNat] using
      (offset_residue K 0 hn0).add (offset_residue K 2 hn0)
  have hpos : 0 < ∑ n ∈ Finset.Icc 2 m, residue n := by
    apply Finset.sum_pos'
    · intro n _
      dsimp [residue]
      split_ifs <;> positivity
    · obtain ⟨n, hn, hdiv⟩ := hPole
      refine ⟨n, hn, ?_⟩
      dsimp [residue]
      rcases hdiv with h | h
      · rw [if_pos h]
        split_ifs <;> positivity
      · rw [if_pos h]
        split_ifs <;> positivity
  exact hlim.eventually (Ioi_mem_nhds hpos)

private lemma floor_sqrt_unit {k : ℕ} {x : ℝ} (hx : x ∈ Ioo (k : ℝ) ((k : ℝ) + 1)) :
    ⌊sqrt x⌋₊ = k.sqrt := by
  have hlo : ((k.sqrt : ℝ) ^ 2) ≤ (k : ℝ) := by exact_mod_cast Nat.sqrt_le' k
  have hhi : (k : ℝ) + 1 ≤ ((k.sqrt : ℝ) + 1) ^ 2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' k)
  refine (Nat.floor_eq_iff (sqrt_nonneg x)).mpr ⟨?_, ?_⟩
  · rw [← sqrt_sq (Nat.cast_nonneg k.sqrt)]
    exact sqrt_le_sqrt (hlo.trans hx.1.le)
  · exact (sqrt_lt' (by positivity)).mpr (hx.2.trans_le hhi)

private lemma fixedSum_continuousOn (m k : ℕ) :
    ContinuousOn
      (fun x : ℝ => ∑ n ∈ Finset.Icc 2 m, (cot (x * (π / n)) + cot ((x + 2) * (π / n))) / n)
      (Ioo (k : ℝ) ((k : ℝ) + 1)) := by
  apply continuousOn_finsetSum
  intro n hn
  have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  have hcot (c : ℕ) :
      ContinuousOn (fun x : ℝ => cot ((x + (c : ℝ)) * (π / n))) (Ioo (k : ℝ) ((k : ℝ) + 1)) := by
    simp only [cot_eq_cos_div_sin]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    exact fun x hx => sine_ne_unit hn0 hx
  simpa only [Nat.cast_zero, add_zero, Nat.cast_ofNat, Pi.add_apply] using
    ((hcot 0).add (hcot 2)).div_const (n : ℝ)

/-- Endpoint poles give positive values near the left and negative values near the right. -/
private lemma zero_of_endpoint_divisors (k : ℕ)
    (hLeft : ∃ n ∈ Finset.Icc 2 k.sqrt, n ∣ k ∨ n ∣ k + 2)
    (hRight : ∃ n ∈ Finset.Icc 2 k.sqrt, n ∣ k + 1 ∨ n ∣ k + 1 + 2) :
    ∃ x : ℝ, (k : ℝ) < x ∧ x < (k : ℝ) + 1 ∧ OMA.S_mo_46445.h x = 0 := by
  let f (x : ℝ) := ∑ n ∈ Finset.Icc 2 k.sqrt, (cot (x * (π / n)) + cot ((x + 2) * (π / n))) / n
  have hpos : ∃ t : ℝ, 0 < t ∧ t < 1 / 3 ∧ 0 < f ((k : ℝ) + t) := by
    have hnear : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 / 3 :=
      mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))) (fun _ ht => ht)
    have hsign := (scaled_sum_eventually_pos hLeft).filter_mono (nhdsGT_le_nhdsNE (0 : ℝ))
    have hmem : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have he : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 / 3 ∧ 0 < f ((k : ℝ) + t) := by
      filter_upwards [hmem, hnear, hsign] with t ht ht' hs
      exact ⟨ht, ht', pos_of_mul_pos_right hs ht.le⟩
    exact he.exists
  have hneg : ∃ t : ℝ, -(1 / 3) < t ∧ t < 0 ∧ f ((k : ℝ) + 1 + t) < 0 := by
    have hnear : ∀ᶠ t : ℝ in 𝓝[<] (0 : ℝ), -(1 / 3) < t :=
      mem_of_superset (nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : -(1 / 3) < (0 : ℝ)))) (fun _ ht => ht)
    have hsign := (scaled_sum_eventually_pos hRight).filter_mono (nhdsLT_le_nhdsNE (0 : ℝ))
    have hmem : ∀ᶠ t : ℝ in 𝓝[<] (0 : ℝ), t < 0 := self_mem_nhdsWithin
    have he : ∀ᶠ t : ℝ in 𝓝[<] (0 : ℝ), -(1 / 3) < t ∧ t < 0 ∧ f ((k : ℝ) + 1 + t) < 0 := by
      filter_upwards [hnear, hmem, hsign] with t ht ht' hs
      refine ⟨ht, ht', ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one] using neg_of_mul_pos_right hs ht'.le
    exact he.exists
  obtain ⟨t, ht, ht', htpos⟩ := hpos
  obtain ⟨u, hu, hu', huneg⟩ := hneg
  let a : ℝ := (k : ℝ) + t
  let b : ℝ := (k : ℝ) + 1 + u
  have ha : (k : ℝ) < a := by dsimp [a]; linarith
  have hb : b < (k : ℝ) + 1 := by dsimp [b]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hsub : Icc a b ⊆ Ioo (k : ℝ) ((k : ℝ) + 1) := fun _ hx =>
    ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  obtain ⟨x, hx, hzero⟩ := intermediate_value_Icc' hab ((fixedSum_continuousOn k.sqrt k).mono hsub)
    (show (0 : ℝ) ∈ Icc (f b) (f a) from ⟨huneg.le, htpos.le⟩)
  refine ⟨x, (hsub hx).1, (hsub hx).2, ?_⟩
  simpa only [OMA.S_mo_46445.h, floor_sqrt_unit (hsub hx), mul_div_assoc] using hzero

private lemma affine_cot_deriv (c t x : ℝ) (h : sin ((x + c) * t) ≠ 0) :
    HasDerivAt (fun y => cot ((y + c) * t)) (-(t / sin ((x + c) * t) ^ 2)) x := by
  let z := (x + c) * t
  have hz : sin z ≠ 0 := h
  have hd := (hasDerivAt_cos z).div (hasDerivAt_sin z) hz
  have ha : HasDerivAt (fun y : ℝ => (y + c) * t) t x := by
    simpa using (((hasDerivAt_id x).add_const c).mul_const t)
  have hc := hd.comp x ha
  have hn : -sin z * sin z - cos z * cos z = -1 := by
    nlinarith only [sin_sq_add_cos_sq z]
  have he : (-sin z * sin z - cos z * cos z) / sin z ^ 2 * t = -(t / sin z ^ 2) := by
    rw [hn]
    ring
  rw [he] at hc
  simpa [Function.comp_def, cot_eq_cos_div_sin, z] using hc

private lemma strictAntiOn_affine_cot : H2 := by
  intro a b c t ht h
  apply strictAntiOn_of_deriv_neg (convex_Ioo a b)
  · intro x hx
    exact (affine_cot_deriv c t x (h x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(affine_cot_deriv c t x (h x hx)).deriv]
    exact neg_lt_zero.mpr (div_pos ht (sq_pos_of_ne_zero (h x hx)))


/-- Arbitrarily large unit intervals without a zero exist exactly when the prime
configurations in `H1` are unbounded. -/
theorem equivalent_to_prime_condition : (type_of% @OMA.S_mo_46445.main) ↔ H1 := by
  classical
  constructor
  · intro h
    by_contra hbounded
    obtain ⟨B, hB⟩ := not_forall.mp hbounded
    apply h
    refine ⟨max 9 B, ?_⟩
    intro k hk
    have hk9 : 9 ≤ k := (le_max_left _ _).trans hk
    have hkB : B ≤ k := (le_max_right _ _).trans hk
    have hm : 3 ≤ k.sqrt := Nat.le_sqrt'.mpr (by simpa using hk9)
    have hbound : k + 1 ≤ (k.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' k
    have hleft := endpoint_divisor hm (by omega : 1 < k) ((Nat.le_succ k).trans hbound)
      (fun hp => hB ⟨k, hkB, hp⟩)
    have hright := endpoint_divisor hm (by omega : 1 < k + 1) hbound
      (fun hp => hB ⟨k + 1, by omega, hp⟩)
    exact zero_of_endpoint_divisors k hleft hright
  · intro hprime
    exact main hprime strictAntiOn_affine_cot

end OMA.R_mo_46445_R1
