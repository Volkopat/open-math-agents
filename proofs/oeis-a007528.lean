import OMAStatements.S_oeis_a007528

/-! Proof of Dimitris Valianatos's product identity in OEIS A007528.
Credit: @cjchaffin with Codex.

The character modulo six has harmonic sum π/(2√3). Chebyshev's bound and
the divisor sum for log give bounded partial sums of the twisted
von Mangoldt function divided by n. Dirichlet summation and an Abel
limit then identify the natural logarithmic Euler product at the endpoint.
The square correction is the Euler product for ζ(2) with 2 and 3 removed.
Finally, ordinary prime density zero justifies pairing the two prime
classes by index as prescribed in the question. -/

section
namespace Mo7528Character
open Filter Finset
open scoped Topology

def chi (n : ℕ) : ℝ := if n % 6 = 1 then 1 else if n % 6 = 5 then -1 else 0

private noncomputable def ps (N : ℕ) : ℝ := ∑ i ∈ Icc 1 N, chi i / i
private noncomputable def v (k d : ℕ) : ℝ := 1 / (6 * (k:ℝ) + d)
private noncomputable def low (k : ℕ) := ps (6*k)
private noncomputable def high (k : ℕ) := low k + v k 1

private theorem offsets (k r : ℕ) (hr : r ≤ 6) :
    ps (6*k+r) = low k + (if 1 ≤ r then v k 1 else 0) - (if 5 ≤ r then v k 5 else 0) := by
  induction r with
  | zero => simp [low]
  | succ r ih =>
    have ih' := ih (by omega)
    have hstep (m : ℕ) : ps (m+1) = ps m + chi (m+1) / (m+1 : ℕ) :=
      sum_Icc_succ_top (by omega) _
    rw [← Nat.add_assoc, hstep, ih']
    have hr5 : r ≤ 5 := by omega
    interval_cases r <;> norm_num [chi, Nat.add_assoc, v, Nat.cast_add, Nat.cast_mul]; ring

private theorem low_step (k : ℕ) : low (k+1) = low k + v k 1 - v k 5 := by
  change ps (6*(k+1)) = _
  rw [Nat.mul_add, Nat.mul_one]
  simpa using offsets k 6 (by decide)

private theorem high_step (k : ℕ) : high (k+1) = high k + (v k 7 - v k 5) := by
  simp only [high, low_step, v, Nat.cast_succ]
  ring_nf

private theorem high_eq (k : ℕ) :
    high k = 1 + ∑ i ∈ range k, (v i 7 - v i 5) := by
  induction k with
  | zero => norm_num [high, low, ps, v]
  | succ k ih => rw [high_step, ih, sum_range_succ]; ring

private theorem high_limit : Tendsto high atTop (𝓝 (Real.pi / (2 * Real.sqrt 3))) := by
  have hx : (1 / 6 : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨z, hz⟩
    have he : (z:ℂ)*6 = 1 := (eq_div_iff (by norm_num)).mp hz
    have hi : z * 6 = 1 := by exact_mod_cast he
    omega
  have hcot := tendsto_logDeriv_euler_cot_sub hx
  have hv (n : ℕ) : cotTerm (1/6 : ℂ) n = ((6 * (v n 7 - v n 5) : ℝ) : ℂ) := by
    unfold cotTerm v
    push_cast
    ring_nf
    field_simp
    rw [show (-5 - 6 * (n:ℂ)) = -(5 + 6 * (n:ℂ)) by ring, div_neg]
    ring
  have hval : Complex.cot ((Real.pi : ℂ) * (1/6)) = ((Real.sqrt 3 : ℝ) : ℂ) := by
    rw [mul_one_div, Complex.cot, ← Complex.ofReal_ofNat (n := 6), ← Complex.ofReal_div,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_six, Real.sin_pi_div_six]
    push_cast
    ring
  have hh := Complex.continuous_re.continuousAt.tendsto.comp hcot
  simp only [Function.comp_def, hv, ← Complex.ofReal_sum, Complex.ofReal_re, ← mul_sum,
    hval, ← Complex.ofReal_mul, Complex.sub_re] at hh
  norm_num at hh
  have hlim := (tendsto_const_nhds (x := (1:ℝ))).add (hh.div_const 6)
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  convert hlim using 1
  · ext k
    rw [high_eq, sum_sub_distrib]
    ring
  · congr 1
    field_simp
    linear_combination -2 * Real.pi * hs

private theorem inv_order (k : ℕ) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : v k b ≤ v k a := by
  unfold v
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_left hab (6*k)

private theorem low_mono : Monotone low := monotone_nat_of_le_succ fun k => by
  rw [low_step]
  linarith [inv_order k (by decide : 0 < 1) (by decide : 1 ≤ 5)]

private theorem high_anti : Antitone high := antitone_nat_of_succ_le fun k => by
  rw [high_step]
  linarith [inv_order k (by decide : 0 < 5) (by decide : 5 ≤ 7)]

private theorem block_bounds (k : ℕ) :
    low k ≤ Real.pi / (2 * Real.sqrt 3) ∧ Real.pi / (2 * Real.sqrt 3) ≤ high k := by
  constructor
  · refine ge_of_tendsto high_limit ((eventually_ge_atTop k).mono fun j hj => ?_)
    exact (low_mono hj).trans (le_add_of_nonneg_right (by dsimp [v]; positivity))
  · exact le_of_tendsto high_limit ((eventually_ge_atTop k).mono fun j hj => high_anti hj)

theorem partial_error (N : ℕ) (hN : 1 ≤ N) :
    |(∑ i ∈ Icc 1 N, chi i / i) - Real.pi / (2 * Real.sqrt 3)| ≤ 6 / N := by
  let k := N / 6
  let r := N % 6
  have hr : r < 6 := Nat.mod_lt N (by decide)
  have hNr : 6*k+r=N := Nat.div_add_mod N 6
  have hn : N ≤ 6*(6*k+1) := by omega
  have hc := block_bounds k
  have hv₁ : 0 ≤ v k 1 := by dsimp [v]; positivity
  have hv₅ : 0 ≤ v k 5 := by dsimp [v]; positivity
  have h₅ := inv_order k (by decide : 0 < 1) (by decide : 1 ≤ 5)
  have hp := offsets k r (by omega)
  rw [hNr] at hp
  change |ps N - _| ≤ _
  refine le_trans (b := v k 1) ?_ ?_
  · apply abs_le.mpr
    unfold high at hc
    split_ifs at hp <;> obtain ⟨hlo,hhi⟩ := hc <;> constructor <;> linarith
  · unfold v
    apply (div_le_div_iff₀ (by positivity) (by exact_mod_cast (show 0 < N by omega))).mpr
    push_cast
    exact_mod_cast (by omega : 1*N ≤ 6*(6*k+1))

theorem partial_limit :
    Tendsto (fun N : ℕ => ∑ i ∈ Icc 1 N, chi i / i) atTop (𝓝 (Real.pi / (2 * Real.sqrt 3))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (g := fun N : ℕ => (6:ℝ) / N) (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact partial_error N hN
  · simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 6

end Mo7528Character
end

section
namespace Mo7528Character
open ArithmeticFunction

private def residueValue (a : ZMod 6) : ℤ :=
  if a.val = 1 then 1 else if a.val = 5 then -1 else 0

/-- The real nonprincipal character modulo six, with values in the complex numbers. -/
noncomputable def character6 : DirichletCharacter ℂ 6 where
  toFun a := (residueValue a : ℂ)
  map_one' := by change ((1 : ℤ) : ℂ) = 1; norm_num
  map_mul' a b := by
    have h : ∀ u v : ZMod 6, residueValue (u*v) = residueValue u * residueValue v := by decide
    exact_mod_cast h a b
  map_nonunit' a ha := by
    have h : ∀ x : ZMod 6, residueValue x = 0 ∨ x = 1 ∨ x = 5 := by decide
    obtain hz | rfl | rfl := h a
    · simp [hz]
    · exact (ha isUnit_one).elim
    · exact (ha ⟨⟨5, 5, by decide, by decide⟩, rfl⟩).elim

theorem character6_nat (n : ℕ) : character6 n = (chi n : ℂ) := by
  change ((residueValue (n : ZMod 6) : ℤ) : ℂ) = _
  unfold residueValue chi
  rw [ZMod.val_natCast]
  by_cases h : n % 6 = 1 <;> by_cases k : n % 6 = 5 <;> simp [h, k]

theorem chi_mul (n m : ℕ) : chi (n*m) = chi n * chi m := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, ← character6_nat, Nat.cast_mul, map_mul]

private theorem abs_chi_le_one (n : ℕ) : |chi n| ≤ 1 := by
  unfold chi
  by_cases h : n % 6 = 1 <;> by_cases k : n % 6 = 5 <;> simp [h, k]

private theorem summable_weight {s : ℝ} (hs : 1 < s) (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) : Summable (fun n : ℕ => f n / (n : ℝ)^s) := by
  apply (Real.summable_one_div_nat_rpow.mpr hs).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
  exact div_le_div_of_nonneg_right (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

theorem summable_chi {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => chi n / (n : ℝ)^s) :=
  summable_weight hs _ abs_chi_le_one

theorem summable_chi_mangoldt {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (chi n * vonMangoldt n / Real.log n) / (n : ℝ)^s) := by
  apply summable_weight hs
  intro n
  have hn : 0 ≤ Real.log (n : ℝ) := vonMangoldt_nonneg.trans vonMangoldt_le_log
  rw [abs_div, abs_mul, abs_of_nonneg vonMangoldt_nonneg, abs_of_nonneg hn]
  by_cases hz : Real.log (n : ℝ) = 0
  · simp [hz]
  · rw [div_le_iff₀ (lt_of_le_of_ne hn (Ne.symm hz)), one_mul]
    exact (mul_le_of_le_one_left vonMangoldt_nonneg (abs_chi_le_one n)).trans vonMangoldt_le_log

/-- Euler's exponential identity for the two real Dirichlet series at real s > 1. -/
theorem exp_twisted_eq {s : ℝ} (hs : 1 < s) :
    Real.exp (∑' n : ℕ, (chi n * vonMangoldt n / Real.log n) / (n : ℝ)^s) =
      ∑' n : ℕ, chi n / (n : ℝ)^s := by
  have h := character6.LSeries_eq_exp_LSeries (s := (s : ℂ)) (by simpa using hs)
  rw [LSeries_def₀ (by simp), LSeries_def₀ (by simpa only [character6_nat] using (show (chi 0 : ℂ) = 0 by norm_num [chi]))] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_exp, Complex.ofReal_tsum, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast,
    character6_nat] using h

end Mo7528Character
end

section
namespace Mo7528Twist
open Finset ArithmeticFunction Filter
open scoped Topology

private noncomputable def wt (χ : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => χ n * Λ n / n, by simp⟩

private noncomputable def harmonicWt (χ : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => χ n / n, by simp⟩

private theorem conv_apply (χ : ℕ → ℝ) (hm : ∀ d m, χ (d*m) = χ d * χ m) (n : ℕ) :
    (wt χ * harmonicWt χ) n = χ n * Real.log n / n := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun d m => wt χ d * harmonicWt χ m), ← vonMangoldt_sum, mul_sum, sum_div]
  apply sum_congr rfl
  intro d hd
  have hdm : d*(n/d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  have hh := hm d (n/d)
  rw [hdm] at hh
  change (χ d * Λ d / d) * (χ (n/d) / (n/d : ℕ)) = _
  rw [hh]
  calc
    _ = (χ d * χ (n/d) * Λ d) / ((d : ℝ)*(n/d : ℕ)) := by ring
    _ = _ := by rw [← Nat.cast_mul, hdm]

theorem convolution (χ : ℕ → ℝ) (hm : ∀ d m, χ (d*m) = χ d * χ m) (N : ℕ) :
    (∑ n ∈ Icc 1 N, χ n * Real.log n / n) =
      ∑ d ∈ Icc 1 N, (χ d * Λ d / d) * (∑ m ∈ Icc 1 (N/d), χ m / m) := by
  have hi (x : ℕ) : Icc 1 x = Ioc 0 x := by ext; simp; omega
  simp_rw [hi]
  have h := sum_Ioc_mul_eq_sum_sum (wt χ) (harmonicWt χ) N
  simp only [conv_apply χ hm] at h
  exact h

private theorem half_floor {d N : ℕ} (hd : 0 < d) (hN : d ≤ N) :
    (N : ℝ) ≤ 2 * (d : ℝ) * (N/d : ℕ) := by
  have hr := Nat.mod_lt N hd
  have hq := Nat.div_pos hN hd
  have hm := Nat.div_add_mod N d
  have hprod : d ≤ d*(N/d) := by simpa using Nat.mul_le_mul_left d hq
  exact_mod_cast (show N ≤ 2*d*(N/d) by nlinarith)

theorem bound (χ : ℕ → ℝ) (hm : ∀ d m, χ (d*m) = χ d * χ m)
    (hχ : ∀ n, |χ n| ≤ 1) {L C D : ℝ} (hL : 0 < L) (hC : 0 ≤ C)
    (hh : ∀ N : ℕ, 1 ≤ N → |(∑ m ∈ Icc 1 N, χ m / m) - L| ≤ C / N)
    (hlog : ∀ N : ℕ, |∑ n ∈ Icc 1 N, χ n * Real.log n / n| ≤ D) :
    ∃ K : ℝ, ∀ N : ℕ, |∑ n ∈ Icc 1 N, χ n * Λ n / n| ≤ K := by
  let K := D + 2*C*(Real.log 4 + 4)
  refine ⟨max 0 (K/L), fun N => ?_⟩
  by_cases hN0 : N=0
  · subst N; simp
  have hN : 0 < (N : ℝ) := by positivity
  have hv (d) (hd : d ∈ Icc 1 N) :
      |(χ d * Λ d / d) * ((∑ m ∈ Icc 1 (N/d), χ m / m) - L)| ≤ (2*C/N) * Λ d := by
    obtain ⟨hd1,hdN⟩ := mem_Icc.mp hd
    have hd' : 0 < (d:ℝ) := by exact_mod_cast hd1
    have hq := Nat.div_pos hdN hd1
    have hq' : 0 < ((N/d:ℕ):ℝ) := by exact_mod_cast hq
    have hfactor : (1:ℝ)/d*(C/(N/d:ℕ)) ≤ 2*C/N := by
      apply (le_div_iff₀ hN).mpr
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right (half_floor hd1 hdN) hC]
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg vonMangoldt_nonneg, abs_of_pos hd']
    calc
      _ ≤ (1 * Λ d / d) * (C/(N/d:ℕ)) := by gcongr; exacts [hχ _, hh _ hq]
      _ = (1/d*(C/(N/d:ℕ))) * Λ d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor vonMangoldt_nonneg
  have hpsi : (∑ d ∈ Icc 1 N, Λ d) ≤ (Real.log 4 + 4)*N := by
    have hi : Icc 1 N = Ioc 0 N := by ext; simp; omega
    simpa only [hi, Chebyshev.psi, Nat.floor_natCast] using Chebyshev.psi_le_const_mul_self hN.le
  have he : |∑ d ∈ Icc 1 N, (χ d * Λ d / d) * ((∑ m ∈ Icc 1 (N/d), χ m / m) - L)| ≤
      2*C*(Real.log 4+4) := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hv).trans ?_)
    rw [← mul_sum]
    calc
      _ ≤ (2*C/N)*((Real.log 4+4)*N) := mul_le_mul_of_nonneg_left hpsi (by positivity)
      _ = _ := by field_simp
  simp_rw [mul_sub, sum_sub_distrib] at he
  rw [← convolution χ hm N, ← sum_mul] at he
  apply le_trans _ (le_max_right _ _)
  apply (le_div_iff₀ hL).mpr
  rw [← abs_of_pos hL, ← abs_mul]

  dsimp [K]
  have htri (a b : ℝ) : |b| ≤ |a|+|a-b| := by
    calc
      _ = |a-(a-b)| := by ring_nf
      _ ≤ _ := abs_sub _ _
  exact (htri _ _).trans (add_le_add (hlog N) he)

end Mo7528Twist
end

section
namespace Mo7528Twist
open Finset Filter ArithmeticFunction Mo7528Character
open scoped Topology

private theorem start_iff (f : ℕ → ℝ) (k : ℕ) :
    CauchySeq (fun N => ∑ i ∈ range N, f i) ↔
      CauchySeq (fun N => ∑ i ∈ range N, f (i+k)) := by
  rw [← cauchySeq_shift k]
  have h (N : ℕ) : (∑ i ∈ range (N+k), f i) =
      (∑ i ∈ range k, f i) + ∑ i ∈ range N, f (i+k) := by
    rw [add_comm N k, sum_range_add]
    simp [add_comm]
  simp_rw [h]
  constructor
  · intro hc
    obtain ⟨L,hL⟩ := cauchySeq_tendsto_of_complete hc
    simpa using (hL.sub_const (∑ i ∈ range k, f i)).cauchySeq
  · intro hc
    obtain ⟨L,hL⟩ := cauchySeq_tendsto_of_complete hc
    exact (hL.const_add _).cauchySeq

private theorem pref (N : ℕ) : (∑ i ∈ range N, chi i) =
    if 2 ≤ N%6 then (1:ℝ) else 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    have h := Nat.mod_lt n (by decide : 0 < 6)
    rw [Nat.add_mod]
    unfold chi
    generalize n%6 = m at h ⊢
    interval_cases m <;> norm_num

private theorem chi_mul_local (n m : ℕ) : chi (n*m) = chi n*chi m := by
  unfold chi
  rw [Nat.mul_mod]
  have hn := Nat.mod_lt n (by decide : 0 < 6)
  have hm := Nat.mod_lt m (by decide : 0 < 6)
  generalize n%6 = a at hn ⊢
  generalize m%6 = b at hm ⊢
  interval_cases a <;> interval_cases b <;> norm_num

private theorem range_succ_Icc (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N+1), f i) = f 0 + ∑ i ∈ Icc 1 N, f i := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ n+1)]
    abel

private theorem log_weight_bound : ∃ D : ℝ, ∀ N : ℕ,
    |∑ n ∈ Icc 1 N, chi n * Real.log n / n| ≤ D := by
  let g (i : ℕ) := Real.log (i+3 : ℕ) / (i+3 : ℕ)
  have h3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hg : Antitone g := by
    intro a b hab
    apply Real.log_div_self_antitoneOn
    · exact h3.trans (by exact_mod_cast (show 3≤a+3 by omega))
    · exact h3.trans (by exact_mod_cast (show 3≤b+3 by omega))
    · exact_mod_cast Nat.add_le_add_right hab 3
  have hnat : Tendsto (fun i : ℕ => ((i+3 : ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hzero : Tendsto g atTop (𝓝 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hbound (N : ℕ) : ‖∑ i ∈ range N, chi (i+3)‖ ≤ 1 := by
    have h := sum_range_add chi 3 N
    simp_rw [Nat.add_comm 3] at h
    rw [pref, pref] at h
    simp only [Nat.reduceMod, Nat.reduceLeDiff, ↓reduceIte] at h
    rw [Real.norm_eq_abs]
    split_ifs at h <;> exact abs_le.mpr (by constructor <;> linarith)
  have hc := hg.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero hbound
  have hfull : CauchySeq (fun N => ∑ i ∈ range N, chi i * Real.log i / i) := by
    apply (start_iff _ 3).mpr
    simpa only [g, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hc
  obtain ⟨D,hD⟩ := hfull.isBounded_range.exists_norm_le
  refine ⟨D, fun N => ?_⟩
  have hx := hD _ ⟨N+1,rfl⟩
  simpa only [range_succ_Icc, Nat.cast_zero, Real.log_zero, mul_zero, div_zero, zero_add,
    Real.norm_eq_abs] using hx

theorem weighted_bound : ∃ K : ℝ, ∀ N : ℕ, |∑ n ∈ Icc 1 N, chi n * Λ n / n| ≤ K := by
  obtain ⟨D,hD⟩ := log_weight_bound
  exact bound chi chi_mul_local (fun _ => by unfold chi; split_ifs <;> norm_num)
    (by positivity : 0 < Real.pi/(2*Real.sqrt 3)) (by norm_num : 0 ≤ (6:ℝ))
    partial_error hD

theorem weighted_log_limit : ∃ L : ℝ, Tendsto
    (fun N : ℕ => ∑ n ∈ Icc 1 N, (chi n * Λ n / Real.log n) / n) atTop (𝓝 L) := by
  obtain ⟨K,hK⟩ := weighted_bound
  let z (n : ℕ) := chi n * Λ n / n
  let g (i : ℕ) := (Real.log (i+2 : ℕ))⁻¹
  have hg : Antitone g := by
    intro a b hab
    apply inv_anti₀ (Real.log_pos (by exact_mod_cast (show 1<a+2 by omega)))
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 2)
  have hnat : Tendsto (fun i : ℕ => ((i+2 : ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hzero : Tendsto g atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hnat)
  have hp (N : ℕ) : (∑ i ∈ range N, z (i+2)) = ∑ n ∈ Icc 1 (N+1), z n := by
    have h := sum_range_add z 2 N
    rw [Nat.add_comm 2 N, range_succ_Icc z (N+1)] at h
    simp only [Nat.add_comm 2, Finset.sum_range_succ, Finset.sum_range_zero,
      z, Nat.cast_zero, div_zero, zero_add, vonMangoldt_apply_one, mul_zero, zero_div] at h
    simpa only [z] using h.symm
  have hbound (N) : ‖∑ i ∈ range N, z (i+2)‖ ≤ K := by rw [hp, Real.norm_eq_abs]; exact hK _
  have hc := hg.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero hbound
  have hfull : CauchySeq (fun N => ∑ i ∈ range N, (chi i * Λ i / Real.log i) / i) := by
    apply (start_iff _ 2).mpr
    simpa only [g, z, smul_eq_mul, div_eq_mul_inv, mul_left_comm, mul_assoc, mul_comm] using hc
  obtain ⟨L,hL⟩ := cauchySeq_tendsto_of_complete hfull
  refine ⟨L, ?_⟩
  simpa only [Function.comp_def, range_succ_Icc, Nat.cast_zero, div_zero, zero_add] using
    hL.comp (tendsto_add_atTop_nat 1)

end Mo7528Twist
end

section
namespace OeisA007528Abel
open Filter Finset
open scoped Topology

private theorem abel_bound (c w : ℕ → ℝ) (δ : ℝ) (hc : ∀ n, |∑ i ∈ range n, c i| ≤ δ)
    (hw : Antitone w) (hpos : ∀ n, 0 ≤ w n) (n : ℕ) :
    |∑ i ∈ range n, w i * c i| ≤ w 0 * δ := by
  let S (n : ℕ) := ∑ i ∈ range n, c i
  cases n with
  | zero =>
    have hd : 0 ≤ δ := by simpa using hc 0
    simpa using mul_nonneg (hpos 0) hd
  | succ n =>
    have he := Finset.sum_range_by_parts w c (n+1)
    simp only [smul_eq_mul, Nat.add_one_sub_one] at he
    rw [he]
    calc
      |w n * S (n+1) - ∑ i ∈ range n, (w (i+1)-w i) * S (i+1)| ≤
          |w n * S (n+1)| + |∑ i ∈ range n, (w (i+1)-w i) * S (i+1)| := abs_sub _ _
      _ ≤ w n * δ + ∑ i ∈ range n, (w i - w (i+1)) * δ := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg (hpos n)]
          exact mul_le_mul_of_nonneg_left (hc _) (hpos _)
        · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
          rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hw (Nat.le_succ i))), neg_sub]
          exact mul_le_mul_of_nonneg_left (hc _) (sub_nonneg.mpr (hw (Nat.le_succ i)))
      _ = _ := by rw [← sum_mul, sum_range_sub']; ring

noncomputable def weight (u : ℝ) (n : ℕ) : ℝ := ((n:ℝ)+1)^(-u)

theorem dirichlet_endpoint (c : ℕ → ℝ) (D : ℝ → ℝ) (L : ℝ)
    (hc : Tendsto (fun N => ∑ i ∈ range N, c i) atTop (𝓝 L))
    (hD : ∀ u > 0, Tendsto (fun N => ∑ i ∈ range N, c i * weight u i) atTop (𝓝 (D u))) :
    Tendsto D (𝓝[>] 0) (𝓝 L) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hc (ε/5) (by positivity))
  let P (u : ℝ) := ∑ i ∈ range N, c i * weight u i
  let S := ∑ i ∈ range N, c i
  have h0 : Tendsto P (𝓝[>] 0) (𝓝 S) := by
    have he (i : ℕ) : Tendsto (fun u : ℝ => weight u i) (𝓝[>] 0) (𝓝 1) := by
      have ha : Continuous (fun u : ℝ => weight u i) :=
        (Real.continuous_const_rpow (by positivity : (i:ℝ)+1 ≠ 0)).comp continuous_neg
      simpa [weight] using ((ha.continuousAt (x := 0)).continuousWithinAt (s := Set.Ioi 0)).tendsto
    apply tendsto_finsetSum _ fun i _ => ?_
    simpa only [mul_one] using (he i).const_mul (c i)
  filter_upwards [Metric.tendsto_nhds.mp h0 (ε/5) (by positivity), self_mem_nhdsWithin] with u hup hu
  have hu' : 0 < u := hu
  have htail (m : ℕ) : |∑ i ∈ range m, c (N+i)| ≤ 2*(ε/5) := by
    have he := sum_range_add c N m
    have h1 := hN (N+m) (Nat.le_add_right _ _)
    have h2 := hN N le_rfl
    rw [Real.dist_eq] at h1 h2
    have he' : (∑ i ∈ range m, c (N+i)) =
        ((∑ i ∈ range (N+m), c i)-L) - ((∑ i ∈ range N, c i)-L) := by linarith
    rw [he']
    exact (abs_sub _ _).trans (by linarith)
  have hw : Antitone (fun i : ℕ => weight u (N+i)) := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    exact_mod_cast (show N+i+1 ≤ N+j+1 by omega)
  have hp (i : ℕ) : 0 ≤ weight u (N+i) := Real.rpow_nonneg (by positivity) _
  have hone : weight u (N+0) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)
  have hlim : Tendsto (fun m : ℕ => |(∑ i ∈ range (N+m), c i * weight u i) - P u|)
       atTop (𝓝 |D u - P u|) := by
    have hshift : Tendsto (fun m : ℕ => N+m) atTop atTop := by
      simpa only [Nat.add_comm N] using tendsto_add_atTop_nat N
    exact (((hD u hu').comp hshift).sub_const (P u)).abs
  have hdu : |D u - P u| ≤ 2*(ε/5) := by
    apply le_of_tendsto hlim
    apply Eventually.of_forall
    intro m
    rw [sum_range_add]
    simp only [P, add_sub_cancel_left]
    have h := abel_bound (fun i => c (N+i)) (fun i => weight u (N+i)) (2*(ε/5)) htail hw hp m
    simpa only [mul_comm (c _)] using h.trans
      (show weight u (N+0)*(2*(ε/5)) ≤ 2*(ε/5) by nlinarith)
  have hSL := hN N le_rfl
  have hdist := dist_triangle (D u) (P u) L
  have hdist' := dist_triangle (P u) S L
  change dist S L < ε/5 at hSL
  rw [← Real.dist_eq] at hdu
  linarith

private theorem sum_Icc_eq (c : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, c n) = ∑ i ∈ range N, c (i+1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

theorem dirichlet_endpoint_Icc (c : ℕ → ℝ) (D : ℝ → ℝ) (L : ℝ)
    (hc : Tendsto (fun N => ∑ n ∈ Icc 1 N, c n) atTop (𝓝 L))
    (hD : ∀ u > 0, Tendsto (fun N => ∑ n ∈ Icc 1 N, c n * (n:ℝ)^(-u)) atTop (𝓝 (D u))) :
    Tendsto D (𝓝[>] 0) (𝓝 L) := by
  apply dirichlet_endpoint (fun i => c (i+1)) D L
  · simpa only [sum_Icc_eq] using hc
  · intro u hu
    simpa only [sum_Icc_eq, Nat.cast_add, Nat.cast_one, weight] using hD u hu

end OeisA007528Abel
end

section
namespace Mo7528Endpoint
open Filter Finset ArithmeticFunction Mo7528Character
open scoped Topology

private theorem weighted_partial (g : ℕ → ℝ) (h0 : g 0=0) {u : ℝ}
    (hs : Summable (fun n : ℕ => g n/(n:ℝ)^(1+u))) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, g n / n * (n:ℝ)^(-u)) atTop
      (𝓝 (∑' n : ℕ, g n/(n:ℝ)^(1+u))) := by
  have hr (f : ℕ → ℝ) (N : ℕ) : (∑ i ∈ range (N+1), f i) = f 0 + ∑ i ∈ Icc 1 N, f i := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ N+1)]
      abel
  have he := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine he.congr fun N => ?_
  dsimp only [Function.comp_apply]
  rw [hr, h0, zero_div, zero_add]
  apply sum_congr rfl
  intro n hn
  have hp : 0 < (n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
  rw [Real.rpow_add hp, Real.rpow_one, Real.rpow_neg hp.le]
  ring

theorem identified : ∃ L : ℝ, Real.exp L = Real.pi/(2*Real.sqrt 3) ∧
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, (chi n * vonMangoldt n / Real.log n) / n) atTop (𝓝 L) := by
  obtain ⟨L,hL⟩ := Mo7528Twist.weighted_log_limit
  let g (n : ℕ) := chi n * vonMangoldt n / Real.log n
  let G (u : ℝ) := ∑' n : ℕ, g n / (n : ℝ)^(1+u)
  let F (u : ℝ) := ∑' n : ℕ, chi n / (n : ℝ)^(1+u)
  have hg : Tendsto G (𝓝[>] 0) (𝓝 L) := by
    apply OeisA007528Abel.dirichlet_endpoint_Icc _ _ _ hL
    intro u hu
    exact weighted_partial g (by simp [g]) (summable_chi_mangoldt (by linarith))
  have hf : Tendsto F (𝓝[>] 0) (𝓝 (Real.pi/(2*Real.sqrt 3))) := by
    apply OeisA007528Abel.dirichlet_endpoint_Icc _ _ _ partial_limit
    intro u hu
    exact weighted_partial chi (by norm_num [chi]) (summable_chi (by linarith))
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u := self_mem_nhdsWithin
  have hv : (fun u => Real.exp (G u)) =ᶠ[𝓝[>] 0] F :=
    hpos.mono fun u hu => exp_twisted_eq (by linarith : 1 < 1 + u)
  exact ⟨L, tendsto_nhds_unique ((Real.continuous_exp.tendsto L).comp hg |>.congr' hv) hf, hL⟩

end Mo7528Endpoint
end

section
namespace Mo7528Pair
open Filter Topology Finset Real OMA.S_oeis_a007528

noncomputable def w (p : ℕ) : ℝ := Real.log (((p : ℝ) + 1) / ((p : ℝ) - 1))
abbrev cls (r p : ℕ) := p.Prime ∧ p % 6 = r
noncomputable def cut (r X : ℕ) : ℝ := ∑ p ∈ (range X).filter (cls r), w p
noncomputable def idx (r N : ℕ) : ℝ := ∑ i ∈ range N, w (Nat.nth (cls r) i)

private theorem inf_cls (r : ℕ) (hr : r=1 ∨ r=5) : (Set.ofPred (cls r)).Infinite := by
  have hm : r % 6 = r := by rcases hr with rfl | rfl <;> decide
  have hc : r.Coprime 6 := by rcases hr with rfl | rfl <;> decide
  simpa only [cls, Set.ofPred, Nat.ModEq, hm] using
    Nat.infinite_setOfPred_prime_and_modEq (by decide : 6 ≠ 0) hc

private theorem idx_eq_cut (r N : ℕ) (hr : (Set.ofPred (cls r)).Infinite) :
    idx r N = cut r (Nat.nth (cls r) N) := by
  have hc (n : ℕ) := Nat.count_nth_of_infinite hr n
  induction N with
  | zero =>
    have he : ((range (Nat.nth (cls r) 0)).filter (cls r)).card = 0 := by
      simpa only [Nat.count_eq_card_filter_range] using hc 0
    simp [idx, cut, card_eq_zero.mp he]
  | succ n ih =>
    have hn : Nat.nth (cls r) n ∉ (range (Nat.nth (cls r) n)).filter (cls r) := by simp
    simpa only [idx, cut, sum_range_succ, Nat.filter_range_nth_eq_insert_of_infinite hr,
      sum_insert hn, add_comm] using congrArg (· + w (Nat.nth (cls r) n)) ih

private theorem w_bounds {p X : ℕ} (hX : 2 ≤ X) (hp : X ≤ p) :
    0 ≤ w p ∧ w p ≤ 4 / (X : ℝ) := by
  have h : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hh : (X : ℝ) ≤ p := by exact_mod_cast hp
  have hp' : 0 < (p : ℝ)-1 := by linarith
  have hr : 1 ≤ ((p : ℝ)+1)/(p-1) := (le_div_iff₀ hp').mpr (by linarith)
  refine ⟨Real.log_nonneg hr, (Real.log_le_sub_one_of_pos (by positivity : 0 < ((p:ℝ)+1)/(p-1))).trans ?_⟩
  rw [div_sub_one hp'.ne', div_le_div_iff₀ hp' (by linarith : 0 < (X : ℝ))]
  nlinarith

private theorem tail_bounds (r N X : ℕ) (hr : (Set.ofPred (cls r)).Infinite)
    (hX : 2 ≤ X) (hXN : X ≤ Nat.nth (cls r) N) :
    0 ≤ idx r N - cut r X ∧ idx r N - cut r X ≤ (N : ℝ) * (4 / X) := by
  let S := (range (Nat.nth (cls r) N)).filter (cls r)
  let T := (range X).filter (cls r)
  have hTS : T ⊆ S := filter_subset_filter _ (range_mono hXN)
  have he : idx r N - cut r X = ∑ p ∈ S \ T, w p := by
    rw [idx_eq_cut r N hr, sub_eq_iff_eq_add]
    exact (sum_sdiff hTS).symm
  have hl (p : ℕ) (hp : p ∈ S \ T) : X ≤ p := by
    have h₁ := mem_sdiff.mp hp
    have h₂ := (mem_filter.mp h₁.1).2
    by_contra! h
    exact h₁.2 (mem_filter.mpr ⟨mem_range.mpr h,h₂⟩)
  have hc : S.card = N := by
    simpa only [S, Nat.count_eq_card_filter_range] using Nat.count_nth_of_infinite hr N
  rw [he]
  refine ⟨sum_nonneg fun p hp => (w_bounds hX (hl p hp)).1, ?_⟩
  calc
    _ ≤ ∑ _p ∈ S \ T, (4 / X : ℝ) := sum_le_sum fun p hp => (w_bounds hX (hl p hp)).2
    _ = ((S \ T).card : ℝ) * (4 / X) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (card_le_card sdiff_subset).trans_eq hc) (by positivity)

private noncomputable def X (N : ℕ) := min (a N) (b N)

private theorem X_tendsto : Tendsto X atTop atTop := by
  apply tendsto_atTop_mono (f := id) _ tendsto_id
  intro N
  exact le_min ((Nat.nth_strictMono (inf_cls 5 (Or.inr rfl))).id_le N)
    ((Nat.nth_strictMono (inf_cls 1 (Or.inl rfl))).id_le N)

private theorem le_pi (N : ℕ) : N ≤ (X N).primeCounting := by
  have aux (r : ℕ) (hr : r=1 ∨ r=5) : N ≤ (Nat.nth (cls r) N).primeCounting := by
    let Y := Nat.nth (cls r) N
    have h : Nat.count (cls r) Y ≤ Nat.count Nat.Prime Y :=
      Nat.count_mono_left fun _ _ h => h.1
    rw [Nat.count_nth_of_infinite (inf_cls r hr)] at h
    exact h.trans (Nat.monotone_primeCounting' (Nat.le_succ Y))
  unfold X
  rcases le_total (a N) (b N) with h | h
  · rw [min_eq_left h]; exact aux 5 (Or.inr rfl)
  · rw [min_eq_right h]; exact aux 1 (Or.inl rfl)

private theorem ratio_zero : Tendsto (fun N : ℕ => (N : ℝ)/(X N : ℝ)) atTop (𝓝 0) := by
  have hx : Tendsto (fun N => (X N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp X_tendsto
  have lim : Tendsto (fun N => (Real.log 4 + 1)/Real.log (X N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hx)
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ lim
  filter_upwards [hx.eventually_ge_atTop 2,
    hx.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))] with N hn hh
  have hh' : ((X N).primeCounting : ℝ) ≤ (Real.log 4 + 1) * (X N : ℝ) / Real.log (X N : ℝ) := by simpa using hh
  rw [div_le_iff₀ (by linarith : 0 < (X N : ℝ))]
  calc
    _ ≤ ((X N).primeCounting : ℝ) := by exact_mod_cast le_pi N
    _ ≤ _ := hh'.trans_eq (by ring)

private theorem discrepancy_zero (r : ℕ) (hr : r=1 ∨ r=5) :
    Tendsto (fun N => idx r N - cut r (X N)) atTop (𝓝 0) := by
  have ht : ∀ᶠ N in atTop, 0 ≤ idx r N - cut r (X N) ∧
      idx r N - cut r (X N) ≤ 4 * ((N : ℝ)/(X N : ℝ)) := by
    filter_upwards [X_tendsto.eventually_ge_atTop 2] with N hN
    have hmin : X N ≤ Nat.nth (cls r) N := by
      rcases hr with rfl | rfl
      · exact min_le_right _ _
      · exact min_le_left _ _
    have h := tail_bounds r N (X N) (inf_cls r hr) hN hmin
    exact ⟨h.1, h.2.trans_eq (by ring)⟩
  apply squeeze_zero' (ht.mono fun _ h => h.1) (ht.mono fun _ h => h.2)
  simpa using (tendsto_const_nhds (x := (4 : ℝ))).mul ratio_zero

theorem paired_of_cutoff {L : ℝ}
    (h : Tendsto (fun X : ℕ => cut 1 X - cut 5 X) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => ∏ n ∈ range N,
      (((a n : ℝ)-1)/((a n : ℝ)+1)) * (((b n : ℝ)+1)/((b n : ℝ)-1)))
      atTop (𝓝 (Real.exp L)) := by
  have hsum : Tendsto (fun N => idx 1 N - idx 5 N) atTop (𝓝 L) := by
    have H := ((h.comp X_tendsto).add (discrepancy_zero 1 (Or.inl rfl))).sub
      (discrepancy_zero 5 (Or.inr rfl))
    simp only [add_zero, sub_zero] at H
    apply H.congr fun N => ?_
    dsimp only [Function.comp_apply]
    ring
  have hp (r : ℕ) (hr : r=1 ∨ r=5) (i : ℕ) : (1 : ℝ) < Nat.nth (cls r) i := by
    exact_mod_cast (Nat.nth_mem_of_infinite (inf_cls r hr) i).1.one_lt
  apply (Real.continuous_exp.continuousAt.tendsto.comp hsum).congr
  intro N
  change Real.exp (idx 1 N - idx 5 N) = _
  unfold idx
  rw [← sum_sub_distrib, Real.exp_sum]
  apply prod_congr rfl
  intro n hn
  have ha : (1 : ℝ) < a n := hp 5 (Or.inr rfl) n
  have hb : (1 : ℝ) < b n := hp 1 (Or.inl rfl) n
  change Real.exp (Real.log (((b n : ℝ)+1)/((b n : ℝ)-1)) -
    Real.log (((a n : ℝ)+1)/((a n : ℝ)-1))) = _
  rw [Real.exp_sub, Real.exp_log (by positivity), Real.exp_log (by positivity)]
  field_simp

end Mo7528Pair
end

section
open Filter Topology Finset

namespace A007528Zeta

/-- The Euler product for ζ(2), with the factors at 2 and 3 removed. -/
theorem prime_square_factors :
    Tendsto (fun n : ℕ => ∏ p ∈ (Nat.primesBelow n).filter (5 ≤ ·),
      (1 - ((p : ℝ) ^ 2)⁻¹)) atTop (𝓝 (9 / Real.pi ^ 2)) := by
  have hz := riemannZeta_eulerProduct (s := (2 : ℂ)) (by norm_num)
  have hc : Tendsto (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, (1 - ((p : ℂ) ^ 2)⁻¹))
      atTop (𝓝 (((Real.pi : ℂ) ^ 2 / 6)⁻¹)) := by
    rw [riemannZeta_two] at hz
    have hne : (Real.pi : ℂ) ^ 2 / 6 ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by norm_num)
    have hi := hz.inv₀ hne
    convert hi using 1
    funext n
    simp [Complex.cpow_neg, Complex.cpow_ofNat, Finset.prod_inv_distrib]
  have hr : Tendsto (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, (1 - ((p : ℝ) ^ 2)⁻¹))
      atTop (𝓝 ((Real.pi ^ 2 / 6)⁻¹)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hc
    convert h using 1
    · funext n
      have he : ((∏ p ∈ Nat.primesBelow n, (1 - ((p : ℝ) ^ 2)⁻¹) : ℝ) : ℂ) =
          ∏ p ∈ Nat.primesBelow n, (1 - ((p : ℂ) ^ 2)⁻¹) := by simp
      rw [Function.comp_apply, ← he, Complex.ofReal_re]
    · congr 1
      have he : ((((Real.pi ^ 2 / 6)⁻¹ : ℝ)) : ℂ) =
          ((Real.pi : ℂ) ^ 2 / 6)⁻¹ := by simp
      rw [← he, Complex.ofReal_re]
  have hfactor : ∀ᶠ n : ℕ in atTop,
      (∏ p ∈ Nat.primesBelow n, (1 - ((p : ℝ) ^ 2)⁻¹)) =
      (2 / 3 : ℝ) * ∏ p ∈ (Nat.primesBelow n).filter (5 ≤ ·),
        (1 - ((p : ℝ) ^ 2)⁻¹) := by
    filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
    have hsmall : (Nat.primesBelow n).filter (fun p => ¬ 5 ≤ p) = {2, 3} := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hp, _⟩, hp'⟩
        interval_cases p <;> norm_num at *
      · rintro (rfl | rfl) <;> norm_num <;> omega
    rw [← Finset.prod_filter_mul_prod_filter_not (Nat.primesBelow n) (5 ≤ ·),
      hsmall, mul_comm]
    norm_num [Finset.prod_insert]
  have hv : Tendsto (fun n : ℕ => (∏ p ∈ Nat.primesBelow n, (1 - ((p : ℝ) ^ 2)⁻¹)) /
      (2 / 3 : ℝ)) atTop (𝓝 ((Real.pi ^ 2 / 6)⁻¹ / (2 / 3 : ℝ))) :=
    hr.div_const _
  convert hv.congr' ?_ using 1
  · congr 1
    field_simp
    norm_num
  · filter_upwards [hfactor] with n hn
    rw [hn]
    ring


/-- The signed local ratio is the square of an L-factor times the inverse ζ-factor. -/
theorem prime_factor_identity {p sign : ℝ} (hp : 1 < p) (hs : sign ^ 2 = 1) :
    (p + sign) / (p - sign) = ((1 - sign / p)⁻¹) ^ 2 * (1 - (p ^ 2)⁻¹) := by
  have hp0 : p ≠ 0 := by linarith
  have hps : p - sign ≠ 0 := by
    intro h
    have : p = sign := sub_eq_zero.mp h
    nlinarith
  have hden : 1 - sign / p ≠ 0 := by
    rw [← div_self hp0, ← sub_div]
    exact div_ne_zero hps hp0
  field_simp
  nlinarith

theorem limit_value : (Real.pi / (2 * Real.sqrt 3)) ^ 2 * (9 / Real.pi ^ 2) = (3 : ℝ) / 4 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

theorem prime_square_logs :
    Tendsto (fun n : ℕ => ∑ p ∈ (Nat.primesBelow n).filter (5 ≤ ·),
      Real.log (1 - ((p : ℝ) ^ 2)⁻¹)) atTop (𝓝 (Real.log (9 / Real.pi ^ 2))) := by
  have h := prime_square_factors.log (by positivity : (9 : ℝ) / Real.pi ^ 2 ≠ 0)
  refine h.congr' (Eventually.of_forall fun n => ?_)
  apply Real.log_prod
  intro p hp
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2
  have hp2 : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
  have hpinv : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp2
  linarith

theorem exp_limit_value {L : ℝ} (hL : Real.exp L = Real.pi / (2 * Real.sqrt 3)) :
    Real.exp (2 * L + Real.log (9 / Real.pi ^ 2)) = (3 : ℝ) / 4 := by
  rw [Real.exp_add, show 2 * L = L + L by ring, Real.exp_add, hL, Real.exp_log (by positivity)]
  simpa [pow_two] using limit_value

end A007528Zeta
end

section
namespace Mo7528LogLocal

open ArithmeticFunction

lemma prime_power_term {χ : ℕ → ℝ} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hχ : χ (p ^ k) = χ p ^ k) :
    χ (p ^ k) * vonMangoldt (p ^ k) / ((p ^ k : ℕ) * Real.log (p ^ k : ℕ)) =
      (χ p / p) ^ k / k := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [hχ, vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp, Nat.cast_pow,
    Real.log_pow, div_pow]
  field_simp [ne_of_gt (zero_lt_one.trans hp'), (Real.log_pos hp').ne', hk']

theorem prime_power_tail {χ : ℕ → ℝ} {p : ℕ} (hp : p.Prime)
    (hpow : ∀ k, χ (p ^ k) = χ p ^ k) (hχ : |χ p| ≤ 1) :
    HasSum (fun k : ℕ => χ (p ^ (k + 2)) * vonMangoldt (p ^ (k + 2)) /
      ((p ^ (k + 2) : ℕ) * Real.log (p ^ (k + 2) : ℕ)))
      (-Real.log (1 - χ p / p) - χ p / p) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hs : |χ p / (p : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos (zero_lt_one.trans hp'), div_lt_one (zero_lt_one.trans hp')]
    exact hχ.trans_lt hp'
  have h := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_pow_div_log_of_abs_lt_one hs)
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one] at h
  have he : (fun k : ℕ => χ (p ^ (k + 2)) * vonMangoldt (p ^ (k + 2)) /
      ((p ^ (k + 2) : ℕ) * Real.log (p ^ (k + 2) : ℕ))) =
      (fun k : ℕ => (χ p / (p : ℝ)) ^ (k + 1 + 1) / ((↑(k + 1) : ℝ) + 1)) := by
    funext k
    simpa [Nat.cast_add, add_assoc, one_add_one_eq_two] using
      prime_power_term (χ := χ) hp (k := k + 2) (by omega) (hpow _)
  rw [he]
  exact h

end Mo7528LogLocal
end

section
namespace Mo7528Reindex
open Filter Finset Real ArithmeticFunction Mo7528Character Mo7528Pair
open scoped Topology

private noncomputable def g (n : ℕ) := chi n * Λ n / ((n:ℝ)*Real.log n)
private noncomputable def u (n : ℕ) := if n.Prime then 0 else g n
private noncomputable def tail (p : ℕ) := ∑' k : ℕ, g (p^(k+2))

private theorem summable_u : Summable u := by
  have hd := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  have hd' : Summable (fun n : ℕ => (if n.Prime then 0 else Λ n)/(n:ℝ)) := by
    convert hd using 1
    funext n
    have hz : (n : ZMod 1) = 0 := Subsingleton.elim _ _
    simp [vonMangoldt.residueClass,Set.indicator,hz]
  apply (hd'.mul_right ((Real.log 2)⁻¹)).of_norm_bounded
  intro n
  dsimp only [u,g]
  by_cases hn : n.Prime
  · simp [hn]
  simp only [if_neg hn]
  rcases le_or_gt 2 n with h | h
  · have hreal : (2:ℝ) ≤ n := by exact_mod_cast h
    have hlog := Real.log_le_log (by norm_num : 0 < (2:ℝ)) hreal
    have hl : 0 < Real.log (2:ℝ) := by positivity
    have hln : 0 < Real.log n := hl.trans_le hlog
    have hn' : 0 < (n:ℝ) := by linarith
    have hc : |chi n| ≤ 1 := by unfold chi; split_ifs <;> norm_num
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (mul_pos hn' hln),abs_of_nonneg vonMangoldt_nonneg]
    calc
      _ ≤ (Λ n)/((n:ℝ)*Real.log n) := by gcongr; simpa using mul_le_mul_of_nonneg_right hc (vonMangoldt_nonneg (n:=n))
      _ ≤ (Λ n)/((n:ℝ)*Real.log 2) := by gcongr
      _ = _ := by ring
  · interval_cases n <;> simp

private theorem reindex :
    Tendsto (fun X : ℕ => (∑ p ∈ (range X).filter Nat.Prime, tail p) - ∑ n ∈ range X, u n)
      atTop (𝓝 0) := by
  let F : Nat.Primes × ℕ → ℝ := fun v => u (v.1.val^(v.2+1))
  have hF : Summable F := (summable_u.comp_injective (i := fun v : Nat.Primes × ℕ => (Nat.Primes.prodNatEquiv v).val)
    (Subtype.val_injective.comp Nat.Primes.prodNatEquiv.injective))
  have hf (p : Nat.Primes) : ∑' k, F (p,k) = tail p := by
    rw [(hF.prod_factor p).tsum_eq_zero_add]
    simp only [F,u,pow_one,zero_add,p.prop,if_true,zero_add,tail]
    apply tsum_congr
    intro k
    rw [if_neg (Nat.Prime.not_prime_pow (by omega : 2 ≤ k+1+1))]
  have hsupp : Function.support u ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra h
    apply hn
    simp [u,g,vonMangoldt_eq_zero_iff.mpr h]
  have htot : ∑' v, F v = ∑' n, u n := by
    exact ((Nat.Primes.prodNatEquiv.tsum_eq (fun x => u x.val))).trans
      (tsum_subtype_eq_of_support_subset hsupp)
  let T := {p : ℕ | p.Prime}.indicator tail
  have hT : Summable T := summable_subtype_iff_indicator.mp (hF.prod.congr hf)
  have he : ∑' p, T p = ∑' n, u n := by
    rw [show (∑' p,T p) = ∑' p : Nat.Primes, tail p from (_root_.tsum_subtype _ _).symm, ← htot, hF.tsum_prod]
    exact tsum_congr (fun p => (hf p).symm)
  have hlimits := hT.hasSum.tendsto_sum_nat.sub summable_u.hasSum.tendsto_sum_nat
  rw [he,sub_self] at hlimits
  apply hlimits.congr
  intro X
  rw [sum_filter]
  congr 1
  exact sum_congr rfl fun n _ => by by_cases hn : n.Prime <;> simp [T,hn]





private theorem power_chi (p k : ℕ) : chi (p^k) = chi p ^ k := by
  induction k with
  | zero => norm_num [chi]
  | succ k ih => rw [pow_succ,pow_succ,chi_mul,ih]

private theorem prime_means (p : ℕ) (hp : p.Prime) :
    tail p + g p = -Real.log (1-chi p/p) := by
  have h := (Mo7528LogLocal.prime_power_tail hp (power_chi p) (show |chi p| ≤ 1 by unfold chi; split_ifs <;> norm_num)).tsum_eq
  change tail p = _ at h
  rw [h,g,vonMangoldt_apply_prime hp]
  have hlog : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  field_simp [hlog.ne', Nat.cast_ne_zero.mpr hp.ne_zero]
  ring

private theorem local_log {a t : ℝ} (ha : 1<a) (ht : t=1 ∨ t = -1) :
    t*Real.log ((a+1)/(a-1)) = 2*(-Real.log (1-t/a)) + Real.log (1-(a^2)⁻¹) := by
  have hsg : t^2=1 := by rcases ht with rfl|rfl <;> norm_num
  have h1 : 0 < 1-t/a := by
    rcases ht with rfl|rfl <;> apply sub_pos.mpr <;> rw [div_lt_one (by linarith)] <;> linarith
  have h2 : 0 < 1-(a^2)⁻¹ := sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr (by nlinarith))
  have e := congrArg Real.log (A007528Zeta.prime_factor_identity ha hsg)
  rw [Real.log_mul (by positivity) h2.ne',Real.log_pow,Real.log_inv] at e
  calc
    _ = Real.log ((a+t)/(a-t)) := by
      rcases ht with rfl|rfl
      · simp
      · rw [neg_one_mul,← Real.log_inv,inv_div]; congr 1; ring
    _ = _ := by simpa using e

private theorem local_wp (p : ℕ) (hp : p.Prime) :
    (if p%6 = 1 then w p else 0) - (if p%6 = 5 then w p else 0) =
      2*(tail p + g p) + (if 5 ≤ p then Real.log (1-((p:ℝ)^2)⁻¹) else 0) := by
  rw [prime_means _ hp]
  by_cases h5 : 5 ≤ p
  · have h2 : ¬2 ∣ p := fun h => by have := hp.eq_one_or_self_of_dvd 2 h; omega
    have h3 : ¬3 ∣ p := fun h => by have := hp.eq_one_or_self_of_dvd 3 h; omega
    have H : p%6=1 ∨ p%6=5 := by omega
    have sign : chi p=1 ∨ chi p= -1 := by rcases H with H|H <;> simp [chi,H]
    have he := local_log (a := (p:ℝ)) (by exact_mod_cast hp.one_lt) sign
    rcases H with H|H <;> simpa [chi,H,w,h5] using he
  · have hh := hp.two_le
    interval_cases p <;> norm_num [chi] at *

theorem cutoff_reindex : Tendsto (fun X : ℕ => (cut 1 X - cut 5 X) -
    (2 * (∑ n ∈ range X, chi n * Λ n / ((n:ℝ)*Real.log n)) +
      ∑ p ∈ (Nat.primesBelow X).filter (5 ≤ ·), Real.log (1-((p:ℝ)^2)⁻¹))) atTop (𝓝 0) := by
  have h := reindex.const_mul (2:ℝ)
  rw [mul_zero] at h
  apply h.congr
  intro X
  simp only [cut,cls,Nat.primesBelow,sum_filter]
  simp only [mul_sub, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  by_cases hpp : p.Prime
  · have he := local_wp p hpp
    simp only [hpp,true_and,if_true,u,g] at *
    linear_combination -he
  · simp [hpp,u,g]

end Mo7528Reindex
end

section
namespace Mo7528Endpoint
open Filter Finset ArithmeticFunction Mo7528Character Mo7528Pair
open scoped Topology

theorem result_of_reindex (h : Tendsto (fun X : ℕ => (cut 1 X - cut 5 X) -
    (2*(∑ n ∈ range X, chi n * Λ n / ((n:ℝ)*Real.log n)) +
      ∑ p ∈ (Nat.primesBelow X).filter (5 ≤ ·), Real.log (1-((p:ℝ)^2)⁻¹))) atTop (𝓝 0)) :
    type_of% @OMA.S_oeis_a007528.main := by
  obtain ⟨L,hL,ht⟩ := identified
  have hg : Tendsto (fun X : ℕ => ∑ n ∈ range X, chi n * Λ n / ((n:ℝ)*Real.log n)) atTop (𝓝 L) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    apply ht.congr
    intro N
    have hr (f : ℕ → ℝ) (K : ℕ) : (∑ i ∈ range (K+1), f i) = f 0 + ∑ i ∈ Icc 1 K, f i := by
      induction K with
      | zero => simp
      | succ K ih =>
        rw [sum_range_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ K+1)]
        abel
    rw [hr]
    simp only [Nat.cast_zero, zero_mul, div_zero, zero_add]
    apply sum_congr rfl
    intro n _
    ring
  have hs := ((hg.const_mul 2).add A007528Zeta.prime_square_logs).add h
  have hh : Tendsto (fun X : ℕ => cut 1 X - cut 5 X) atTop (𝓝 (2*L+Real.log (9/Real.pi^2))) := by
    rw [add_zero] at hs
    refine hs.congr fun X => ?_
    ring
  have final := paired_of_cutoff hh
  rw [A007528Zeta.exp_limit_value hL] at final
  exact final

end Mo7528Endpoint
end

theorem OMA.solution : type_of% @OMA.S_oeis_a007528.main :=
  Mo7528Endpoint.result_of_reindex Mo7528Reindex.cutoff_reindex
