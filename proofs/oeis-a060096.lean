import OMAStatements.S_oeis_a060096

-- Problem: A060096: Numerator of coefficients of Euler polynomials (rising powers).
-- Upstream: formal-conjectures statements/oeis-a060096.lean:0 (declaration OMA.S_oeis_a060096.main)
-- Credit: @thtsben2 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a060096

private lemma eulerConst_zero : eulerConst 0 = 1 := by
  rw [eulerConst, WellFounded.fix_eq]
  simp

private lemma eulerConst_succ (n : ℕ) :
    eulerConst (n + 1) = -(1 / 2 : ℚ) * ∑ k : Fin (n + 1), ((n + 1).choose k : ℚ) * eulerConst k := by
  rw [eulerConst, WellFounded.fix_eq]
  simp only [Nat.succ_ne_zero, ↓reduceIte]

private lemma r_zero : r 0 = 1 := by
  rw [r, WellFounded.fix_eq]
  simp

private lemma r_succ (n : ℕ) :
    r (n + 1) = -(1 / 2 : ℚ) * ∑ k : Fin (n + 1), ((n + 1).choose k : ℚ) * (-1 : ℚ) ^ (n + 1 - (k : ℕ)) * r k := by
  rw [r, WellFounded.fix_eq]
  simp only [Nat.succ_ne_zero, ↓reduceIte]

private lemma r_eq_neg_one_pow_mul_eulerConst (n : ℕ) :
    r n = (-1 : ℚ) ^ n * eulerConst n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [r_zero, eulerConst_zero]
    | succ n =>
      rw [r_succ, eulerConst_succ]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ih k k.2]
      have hk : (k : ℕ) ≤ n + 1 := k.2.le
      have hpow : (-1 : ℚ) ^ (n + 1 - (k : ℕ)) * (-1 : ℚ) ^ (k : ℕ) = (-1 : ℚ) ^ (n + 1) := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      calc -(1 / 2 : ℚ) * (((n + 1).choose k : ℚ) * (-1) ^ (n + 1 - (k : ℕ)) *
              ((-1 : ℚ) ^ (k : ℕ) * eulerConst k))
          = -(1 / 2 : ℚ) * (((n + 1).choose k : ℚ) *
              ((-1 : ℚ) ^ (n + 1 - (k : ℕ)) * (-1 : ℚ) ^ (k : ℕ)) * eulerConst k) := by ring
        _ = (-1 : ℚ) ^ (n + 1) * (-(1 / 2 : ℚ) * (((n + 1).choose k : ℚ) * eulerConst k)) := by
            rw [hpow]; ring

private lemma two_pow_mul_eulerConst_int (n : ℕ) :
    ∃ m : ℤ, (2 : ℚ) ^ n * eulerConst n = m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => exact ⟨1, by simp [eulerConst_zero]⟩
    | succ n =>
      choose m hm using fun k : Fin (n + 1) => ih k k.2
      rw [eulerConst_succ]
      refine ⟨- ∑ k : Fin (n + 1), ((n + 1).choose k : ℤ) * 2 ^ (n - (k : ℕ)) * m k, ?_⟩
      push_cast
      have hhalf : (2 : ℚ) ^ (n + 1) * -(1 / 2 : ℚ) = -(2 : ℚ) ^ n := by
        rw [pow_succ]; ring
      rw [← mul_assoc, hhalf, neg_mul, neg_inj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
      have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - (k : ℕ)) * (2 : ℚ) ^ (k : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      calc (2 : ℚ) ^ n * (((n + 1).choose k : ℚ) * eulerConst k)
          = ((n + 1).choose k : ℚ) * (2 : ℚ) ^ (n - (k : ℕ)) * ((2 : ℚ) ^ (k : ℕ) * eulerConst k) := by
            rw [hpow]; ring
        _ = ((n + 1).choose k : ℚ) * (2 : ℚ) ^ (n - (k : ℕ)) * (m k : ℚ) := by rw [hm k]

private lemma eulerConst_den_dvd_two_pow (n : ℕ) : (eulerConst n).den ∣ 2 ^ n := by
  obtain ⟨m, hm⟩ := two_pow_mul_eulerConst_int n
  have h1 : (2 : ℚ) ^ n * ((eulerConst n).num / (eulerConst n).den) = m := by
    rwa [Rat.num_div_den]
  have hden : ((eulerConst n).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (eulerConst n).den_nz
  have h2 : (2 : ℤ) ^ n * (eulerConst n).num = m * (eulerConst n).den := by
    field_simp [hden] at h1
    exact_mod_cast h1.trans (mul_comm _ _)
  have hdvd : ((eulerConst n).den : ℤ) ∣ (2 : ℤ) ^ n * (eulerConst n).num := ⟨m, by linarith⟩
  have hcop : Nat.Coprime (eulerConst n).den (eulerConst n).num.natAbs := (eulerConst n).reduced.symm
  have hdvd_nat : (eulerConst n).den ∣ 2 ^ n * (eulerConst n).num.natAbs := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr hdvd
  exact hcop.dvd_of_dvd_mul_right hdvd_nat

section PowerSeriesRel

open PowerSeries

private noncomputable def eulerPS : PowerSeries ℚ :=
  mk fun n => eulerConst n / (n.factorial : ℚ)

private noncomputable def bernoulli2PS : PowerSeries ℚ :=
  mk fun n => (2 : ℚ) ^ n * bernoulli n / (n.factorial : ℚ)

private lemma eulerPS_mul_exp_add_one : eulerPS * (exp ℚ + 1) = 2 := by
  ext n
  cases n with
  | zero =>
    simp only [coeff_zero_eq_constantCoeff, map_mul, map_add, map_one, eulerPS,
      constantCoeff_mk, eulerConst_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      constantCoeff_exp]
    change (1 : ℚ) * (1 + 1) = (2 : ℚ)
    norm_num
  | succ n =>
    rw [mul_add, mul_one, map_add, coeff_mul]
    have h2 : coeff (n + 1) (2 : PowerSeries ℚ) = 0 := by
      rw [show (2 : PowerSeries ℚ) = 1 + 1 by norm_num, map_add]
      simp
    rw [h2]
    have hsum_anti : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
        coeff p.1 eulerPS * coeff p.2 (exp ℚ)) =
        (((n + 1).factorial : ℚ))⁻¹ *
          ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℚ) * eulerConst k := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i eulerPS * coeff j (exp ℚ))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [eulerPS, coeff_mk, coeff_exp, Algebra.algebraMap_self, RingHom.id_apply]
      have hfac := Nat.add_choose_mul_factorial_mul_factorial (n + 1 - k) k
      rw [Nat.sub_add_cancel hk_le] at hfac
      have hfac_q : ((n + 1).choose k : ℚ) * ((n + 1 - k).factorial : ℚ) * (k.factorial : ℚ) =
          ((n + 1).factorial : ℚ) := by exact_mod_cast hfac
      have hk_ne : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have hnk_ne : ((n + 1 - k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hn_ne : ((n + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp [hk_ne, hnk_ne, hn_ne]
      rw [← hfac_q]; ring
    rw [hsum_anti, Finset.sum_range_succ]
    have hrec : ∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℚ) * eulerConst k =
        -2 * eulerConst (n + 1) := by
      have h := eulerConst_succ n
      rw [← Fin.sum_univ_eq_sum_range (fun k => ((n + 1).choose k : ℚ) * eulerConst k)]
      linarith
    rw [hrec]
    simp only [eulerPS, coeff_mk, Nat.choose_self, Nat.cast_one]
    ring

private lemma exp_mul_exp_eq :
    exp ℚ * exp ℚ = mk fun n => (2 : ℚ) ^ n / (n.factorial : ℚ) := by
  ext n
  rw [coeff_mul, coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (exp ℚ) * coeff j (exp ℚ))]
  have hsum : (∑ k ∈ Finset.range (n + 1),
      coeff k (exp ℚ) * coeff (n - k) (exp ℚ)) =
      ((n.factorial : ℚ))⁻¹ * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp only [coeff_exp, Algebra.algebraMap_self, RingHom.id_apply]
    have hfac := Nat.add_choose_mul_factorial_mul_factorial (n - k) k
    rw [Nat.sub_add_cancel hk_le] at hfac
    have hfac_q : (n.choose k : ℚ) * ((n - k).factorial : ℚ) * (k.factorial : ℚ) =
        (n.factorial : ℚ) := by exact_mod_cast hfac
    have hk_ne : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hnk_ne : ((n - k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hn_ne : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hk_ne, hnk_ne, hn_ne]
    linarith
  rw [hsum]
  have hchoose : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ)) = (2 : ℚ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [hchoose]
  ring

private lemma bernoulli2PS_mul_exp_sq_sub_one :
    bernoulli2PS * (exp ℚ * exp ℚ - 1) = 2 * X := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul, exp_mul_exp_eq]
  have hsum_anti : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      coeff p.1 bernoulli2PS * coeff p.2 (mk fun m => (2 : ℚ) ^ m / (m.factorial : ℚ))) =
      (2 : ℚ) ^ n / (n.factorial : ℚ) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * bernoulli k := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i bernoulli2PS * coeff j (mk fun m => (2 : ℚ) ^ m / (m.factorial : ℚ)))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp only [bernoulli2PS, coeff_mk]
    have hfac := Nat.add_choose_mul_factorial_mul_factorial (n - k) k
    rw [Nat.sub_add_cancel hk_le] at hfac
    have hfac_q : (n.choose k : ℚ) * ((n - k).factorial : ℚ) * (k.factorial : ℚ) =
        (n.factorial : ℚ) := by exact_mod_cast hfac
    have hpow : (2 : ℚ) ^ k * (2 : ℚ) ^ (n - k) = (2 : ℚ) ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hk_le]
    have hk_ne : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hnk_ne : ((n - k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hn_ne : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hk_ne, hnk_ne, hn_ne]
    calc (2 : ℚ) ^ k * bernoulli k * (2 : ℚ) ^ (n - k) * (n.factorial : ℚ)
        = ((2 : ℚ) ^ k * (2 : ℚ) ^ (n - k)) * bernoulli k * (n.factorial : ℚ) := by ring
      _ = (2 : ℚ) ^ n * bernoulli k * ((n.choose k : ℚ) * ((n - k).factorial : ℚ) * (k.factorial : ℚ)) := by
          rw [hpow, hfac_q]
      _ = bernoulli k * (k.factorial : ℚ) * ((n - k).factorial : ℚ) * (2 : ℚ) ^ n * (n.choose k : ℚ) := by ring
  rw [hsum_anti, Finset.sum_range_succ]
  have hsb := sum_bernoulli n
  rw [hsb]
  rcases n with _ | _ | n
  · simp [bernoulli2PS]
  · simp [bernoulli2PS]
    change 2 * (1 + -1 / 2) - 2 * (-1 / 2) = (2 : ℚ)
    norm_num
  · simp [bernoulli2PS]
    have h2 : coeff (n + 1) (2 : PowerSeries ℚ) = 0 := by
      rw [show (2 : PowerSeries ℚ) = 1 + 1 by norm_num, map_add]
      simp
    rw [h2]
    ring

private lemma mul_eulerConst_eq_bernoulli (n : ℕ) :
    (n + 1 : ℚ) * eulerConst n = 2 * (1 - (2 : ℚ) ^ (n + 1)) * bernoulli (n + 1) := by
  have hB : bernoulliPowerSeries ℚ * (exp ℚ - 1) = X :=
    bernoulliPowerSeries_mul_exp_sub_one ℚ
  have hB2 : bernoulli2PS * (exp ℚ * exp ℚ - 1) = 2 * X :=
    bernoulli2PS_mul_exp_sq_sub_one
  have hE : eulerPS * (exp ℚ + 1) = 2 := eulerPS_mul_exp_add_one
  have hexp_sq : exp ℚ * exp ℚ - 1 = (exp ℚ - 1) * (exp ℚ + 1) := by ring
  have hmul : ((2 * bernoulliPowerSeries ℚ - 2 * bernoulli2PS) * (exp ℚ + 1)) * (exp ℚ - 1) =
      (2 * X) * (exp ℚ - 1) := by
    calc ((2 * bernoulliPowerSeries ℚ - 2 * bernoulli2PS) * (exp ℚ + 1)) * (exp ℚ - 1)
        = 2 * (bernoulliPowerSeries ℚ * (exp ℚ - 1)) * (exp ℚ + 1) -
            2 * (bernoulli2PS * ((exp ℚ - 1) * (exp ℚ + 1))) := by ring
      _ = 2 * X * (exp ℚ + 1) - 2 * (2 * X) := by rw [hB, ← hexp_sq, hB2]
      _ = (2 * X) * (exp ℚ - 1) := by ring
  have hexp_sub_ne : exp ℚ - 1 ≠ 0 := by
    intro h
    have h1 := congr_arg (coeff 1) h
    simp at h1
  have h1 : (2 * bernoulliPowerSeries ℚ - 2 * bernoulli2PS) * (exp ℚ + 1) = 2 * X :=
    mul_right_cancel₀ hexp_sub_ne hmul
  have h2 : (2 * bernoulliPowerSeries ℚ - 2 * bernoulli2PS) * (exp ℚ + 1) =
      (X * eulerPS) * (exp ℚ + 1) := by
    rw [h1, mul_assoc, hE, mul_comm X 2]
  have hexp_add_ne : exp ℚ + 1 ≠ 0 := by
    intro h
    have h0 := congr_arg (coeff 0) h
    simp at h0
  have h3 : 2 * bernoulliPowerSeries ℚ - 2 * bernoulli2PS = X * eulerPS :=
    mul_right_cancel₀ hexp_add_ne h2
  have hcoeff := congr_arg (coeff (n + 1)) h3
  have h2mul (f : PowerSeries ℚ) : coeff (n + 1) (2 * f) = 2 * coeff (n + 1) f := by
    rw [two_mul, map_add, two_mul]
  have hXmul : coeff (n + 1) (X * eulerPS) = coeff n eulerPS := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i X * coeff j eulerPS)]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b _ hb
      simp [coeff_X, hb]
    · simp
  rw [map_sub, h2mul, h2mul, hXmul] at hcoeff
  simp only [bernoulliPowerSeries, bernoulli2PS, eulerPS, coeff_mk,
    Algebra.algebraMap_self, RingHom.id_apply] at hcoeff
  have hfac_ne : ((n.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1_ne : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [Nat.factorial_succ] at hcoeff
  push_cast at hcoeff
  field_simp [hfac_ne, hn1_ne] at hcoeff ⊢
  linarith

end PowerSeriesRel

private lemma two_mul_one_sub_pow_bernoulli_odd_int {k : ℕ} (hk : 0 < k) :
    ∃ g : ℤ, Odd g ∧ 2 * (1 - (2 : ℚ) ^ (2 * k)) * bernoulli (2 * k) = g := by
  obtain ⟨m, hm⟩ := Bernoulli.vonStaudt_clausen k
  set S := (Finset.range (2 * k + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * k)
  have hB : bernoulli (2 * k) = (m : ℚ) - ∑ p ∈ S, (1 : ℚ) / p := by
    have : bernoulli (2 * k) + ∑ p ∈ S, (1 : ℚ) / p = m := hm.symm
    linarith
  have h2_mem : 2 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two, one_dvd _⟩
  have hterm : ∀ p : ℕ, ∃ t : ℤ, p ∈ S →
      2 * (1 - (2 : ℚ) ^ (2 * k)) * ((1 : ℚ) / p) = t ∧ (p ≠ 2 → Even t) ∧ (p = 2 → Odd t) := by
    intro p
    by_cases hp : p ∈ S
    · have hp' := hp
      simp only [S, Finset.mem_filter, Finset.mem_range] at hp'
      rcases hp' with ⟨_, hp_prime, hp_dvd⟩
      by_cases hp2 : p = 2
      · subst hp2
        refine ⟨1 - (2 : ℤ) ^ (2 * k), fun _ => ⟨?_, fun h => (h rfl).elim, fun _ => ?_⟩⟩
        · push_cast; ring
        · have h2k_ne : 2 * k ≠ 0 := by omega
          have heven : Even ((2 : ℤ) ^ (2 * k)) := even_two.pow_of_ne_zero h2k_ne
          simpa using odd_one.sub_even heven
      · have : Fact p.Prime := ⟨hp_prime⟩
        have h2_ne_zero : (2 : ZMod p) ≠ 0 := by
          intro h
          have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
          have : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left hp_prime.ne_one
          exact hp2 this
        have hflt : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2_ne_zero
        obtain ⟨c, hc⟩ := hp_dvd
        have hpow_zmod : (2 : ZMod p) ^ (2 * k) = 1 := by
          rw [hc, pow_mul, hflt, one_pow]
        have hdvd_z : (p : ℤ) ∣ 1 - (2 : ℤ) ^ (2 * k) := by
          have : ((1 - (2 : ℤ) ^ (2 * k) : ℤ) : ZMod p) = 0 := by
            push_cast
            rw [hpow_zmod, sub_self]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
        obtain ⟨q, hq⟩ := hdvd_z
        refine ⟨2 * q, fun _ => ⟨?_, fun _ => even_two_mul q, fun h => (hp2 h).elim⟩⟩
        have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp_prime.ne_zero
        have hq_q : (1 - (2 : ℚ) ^ (2 * k)) = (p : ℚ) * (q : ℚ) := by exact_mod_cast hq
        rw [hq_q]
        field_simp [hp_ne]
        push_cast; ring
    · exact ⟨0, fun h => (hp h).elim⟩
  choose t ht using hterm
  have hsum_q : (∑ p ∈ S, 2 * (1 - (2 : ℚ) ^ (2 * k)) * ((1 : ℚ) / p)) =
      ((∑ p ∈ S, t p : ℤ) : ℚ) := by
    push_cast
    exact Finset.sum_congr rfl fun p hp => (ht p hp).1
  refine ⟨2 * (1 - (2 : ℤ) ^ (2 * k)) * m - ∑ p ∈ S, t p, ?_, ?_⟩
  · have h_even_first : Even (2 * (1 - (2 : ℤ) ^ (2 * k)) * m) := by
      rw [mul_assoc]; exact even_two_mul _
    have hsum_split : (∑ p ∈ S, t p) = t 2 + ∑ p ∈ S.erase 2, t p :=
      (Finset.add_sum_erase S t h2_mem).symm
    have h_odd_2 : Odd (t 2) := (ht 2 h2_mem).2.2 rfl
    have h_even_rest : Even (∑ p ∈ S.erase 2, t p) := by
      apply Finset.even_sum
      intro p hp
      exact (ht p (Finset.mem_of_mem_erase hp)).2.1 (Finset.ne_of_mem_erase hp)
    rw [hsum_split]
    exact h_even_first.sub_odd (h_odd_2.add_even h_even_rest)
  · rw [hB, mul_sub, Finset.mul_sum, hsum_q]
    push_cast
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a060096.main := by
  intro n
  rw [OMA.S_oeis_a060096.eulerCoeff, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
  rw [OMA.S_oeis_a060096.A198631, OMA.S_oeis_a060096.A006519]
  rw [r_eq_neg_one_pow_mul_eulerConst]
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simp [eulerConst_zero]
  rcases n.even_or_odd with heven | hodd
  · have hodd_succ : Odd (n + 1) := heven.add_one
    have hgt : 1 < n + 1 := by omega
    have hbern : bernoulli (n + 1) = 0 := bernoulli_eq_zero_of_odd hodd_succ hgt
    have hmul := mul_eulerConst_eq_bernoulli n
    rw [hbern, mul_zero] at hmul
    have hn1_ne : (n + 1 : ℚ) ≠ 0 := by positivity
    have heul : eulerConst n = 0 := (mul_eq_zero.mp hmul).resolve_left hn1_ne
    simp [heul]
  · obtain ⟨k, hk_eq⟩ := hodd
    have hk_pos : 0 < k + 1 := Nat.succ_pos k
    have hn1_eq : n + 1 = 2 * (k + 1) := by omega
    obtain ⟨g, hg_odd, hg_eq⟩ := two_mul_one_sub_pow_bernoulli_odd_int hk_pos
    have hmul := mul_eulerConst_eq_bernoulli n
    rw [← hn1_eq] at hg_eq
    have hmul_g : ((n + 1 : ℕ) : ℚ) * eulerConst n = (g : ℚ) := by
      push_cast; rw [hmul, ← hg_eq]
    have hdvd_pow : (eulerConst n).den ∣ 2 ^ n := eulerConst_den_dvd_two_pow n
    obtain ⟨j, hj_le, hj_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_pow
    have heul_num_den : (eulerConst n) = (eulerConst n).num / (eulerConst n).den :=
      (Rat.num_div_den _).symm
    have hden_ne : ((eulerConst n).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (eulerConst n).den_nz
    have hmul_z : ((n + 1 : ℕ) : ℤ) * (eulerConst n).num = g * ((eulerConst n).den : ℤ) := by
      have hq : ((n + 1 : ℕ) : ℚ) * ((eulerConst n).num / (eulerConst n).den) = g := by
        rwa [← heul_num_den]
      field_simp [hden_ne] at hq
      push_cast at hq
      exact_mod_cast hq.trans (mul_comm _ _)
    rw [hj_eq] at hmul_z
    have hj_pos : 0 < j := by
      by_contra hj0
      have hjz : j = 0 := by omega
      rw [hjz, pow_zero] at hmul_z
      simp only [Nat.cast_one, mul_one] at hmul_z
      have heven_lhs : Even (((n + 1 : ℕ) : ℤ) * (eulerConst n).num) := by
        rw [hn1_eq]; push_cast; rw [mul_assoc]; exact even_two_mul _
      rw [hmul_z] at heven_lhs
      exact (Int.not_even_iff_odd.mpr hg_odd) heven_lhs
    have hnum_odd : Odd (eulerConst n).num := by
      have hcop := (eulerConst n).reduced
      rw [hj_eq] at hcop
      have hnot_dvd : ¬ 2 ∣ (eulerConst n).num.natAbs := by
        intro h
        have h2dvd : 2 ∣ 2 ^ j := dvd_pow_self 2 hj_pos.ne'
        have := Nat.dvd_gcd h h2dvd
        rw [hcop] at this
        omega
      exact Int.odd_iff.mpr (by
        have hmod := Nat.mod_two_of_bodd (eulerConst n).num.natAbs
        omega)
    set v := (n + 1).factorization 2
    set m := (n + 1) / 2 ^ v
    have hm_decomp : 2 ^ v * m = n + 1 := Nat.ordProj_mul_ordCompl_eq_self (n + 1) 2
    have hm_odd : Odd m := by
      have hn1_ne0 : n + 1 ≠ 0 := by omega
      have hnot_dvd : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two hn1_ne0
      exact Nat.odd_iff.mpr (by omega)
    have hn1_z : ((n + 1 : ℕ) : ℤ) = (2 : ℤ) ^ v * (m : ℤ) := by
      exact_mod_cast hm_decomp.symm
    rw [hn1_z, mul_assoc] at hmul_z
    have h_vj : v = j := by
      have hnat : 2 ^ v * (m * (eulerConst n).num.natAbs) = 2 ^ j * g.natAbs := by
        have h := congr_arg Int.natAbs hmul_z
        simpa [Int.natAbs_mul, Int.natAbs_pow, mul_comm (g.natAbs) (2 ^ j)] using h
      have hm_num_odd : Odd (m * (eulerConst n).num.natAbs) :=
        hm_odd.mul (Int.natAbs_odd.mpr hnum_odd)
      have hg_nat_odd : Odd g.natAbs := Int.natAbs_odd.mpr hg_odd
      have hnot2_g : ¬ 2 ∣ g.natAbs := by
        intro hd; exact Nat.not_even_iff_odd.mpr hg_nat_odd (even_iff_two_dvd.mpr hd)
      have hnot2_mn : ¬ 2 ∣ m * (eulerConst n).num.natAbs := by
        intro hd; exact Nat.not_even_iff_odd.mpr hm_num_odd (even_iff_two_dvd.mpr hd)
      have hv_le : v ≤ j := by
        have hd : 2 ^ v ∣ 2 ^ j * g.natAbs := ⟨m * (eulerConst n).num.natAbs, hnat.symm⟩
        have hcop : Nat.Coprime (2 ^ v) g.natAbs :=
          Nat.Coprime.pow_left v (Nat.prime_two.coprime_iff_not_dvd.mpr hnot2_g)
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hd)
      have hj_le' : j ≤ v := by
        have hd : 2 ^ j ∣ 2 ^ v * (m * (eulerConst n).num.natAbs) := ⟨g.natAbs, hnat⟩
        have hcop : Nat.Coprime (2 ^ j) (m * (eulerConst n).num.natAbs) :=
          Nat.Coprime.pow_left j (Nat.prime_two.coprime_iff_not_dvd.mpr hnot2_mn)
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hd)
      omega
    have hv_padic : padicValNat 2 (n + 1) = v := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hn1_ne0 : n + 1 ≠ 0 := by omega
      have hv_le : v ≤ padicValNat 2 (n + 1) :=
        (padicValNat_dvd_iff_le hn1_ne0).mp ⟨m, hm_decomp.symm⟩
      have hnot_le : ¬ (v + 1 ≤ padicValNat 2 (n + 1)) := by
        intro h
        have hd : 2 ^ (v + 1) ∣ n + 1 := (padicValNat_dvd_iff_le hn1_ne0).mpr h
        rw [← hm_decomp, pow_succ] at hd
        have h2m : 2 ∣ m := (mul_dvd_mul_iff_left (pow_ne_zero v (by norm_num))).mp hd
        exact Nat.not_even_iff_odd.mpr hm_odd (even_iff_two_dvd.mpr h2m)
      omega
    have hden_eq : (eulerConst n).den = 2 ^ padicValNat 2 (n + 1) := by
      rw [hj_eq, ← h_vj, hv_padic]
    have hn_odd : Odd n := ⟨k, hk_eq⟩
    have hneg1 : (-1 : ℚ) ^ n = (-1 : ℚ) := hn_odd.neg_one_pow
    have hneg1_z : (-1 : ℤ) ^ n = (-1 : ℤ) := hn_odd.neg_one_pow
    have hrat_r : ((-1 : ℚ) ^ n * eulerConst n).num = (-1 : ℤ) ^ n * (eulerConst n).num := by
      rw [hneg1, hneg1_z, neg_one_mul, neg_one_mul]
      simp
    have hpow_sq : (-1 : ℚ) ^ n * (-1 : ℚ) ^ n = 1 := by
      rw [hneg1]; norm_num
    rw [hrat_r]
    calc eulerConst n
        = ((eulerConst n).num : ℚ) / ((eulerConst n).den : ℚ) := (Rat.num_div_den _).symm
      _ = ((eulerConst n).num : ℚ) / ((2 ^ padicValNat 2 (n + 1) : ℕ) : ℚ) := by rw [hden_eq]
      _ = ((-1 : ℚ) ^ n * (-1 : ℚ) ^ n) * ((eulerConst n).num : ℚ) /
            ((2 ^ padicValNat 2 (n + 1) : ℕ) : ℚ) := by rw [hpow_sq, one_mul]
      _ = (-1 : ℚ) ^ n * (((-1 : ℤ) ^ n * (eulerConst n).num : ℤ) : ℚ) /
            ((2 ^ padicValNat 2 (n + 1) : ℕ) : ℚ) := by push_cast; ring
