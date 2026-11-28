import OMAStatements.S_oeis_a346695
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- Exact density-zero proof for OEIS A346695.
-- Statement: @Alienchisel, PR22455. Mertens component: own PR25517.
-- Complete source and earlier-note credits accompany the pull request.


namespace D7Mertens
open Finset Real Filter
open scoped Topology BigOperators

lemma weighted_prefix_bound (c : ℕ → ℝ) (C : ℝ)
    (hC : ∀ n, (∑ k ∈ range n, c (k+1)) ≤ C*n) (n : ℕ) :
    (∑ k ∈ range n, c (k+1)/(k+1)) ≤ C*(harmonic n : ℝ) := by
  have strong : ∀ n : ℕ, (∑ k ∈ range n, c (k+1)/(k+1)) ≤
      C*(harmonic n : ℝ) + ((∑ k ∈ range n, c (k+1))-C*n)/n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      by_cases hn : n=0
      · subst n
        simp
      have hnR : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hneg : (∑ k ∈ range n, c (k+1))-C*n ≤ 0 := sub_nonpos.mpr (hC n)
      have hdiv : ((∑ k ∈ range n, c (k+1))-C*n)/n ≤
          ((∑ k ∈ range n, c (k+1))-C*n)/(n+1) := by
        apply (div_le_div_iff₀ hnR (by linarith)).2
        nlinarith
      rw [sum_range_succ]
      calc
        _ ≤ C*(harmonic n : ℝ) + ((∑ k ∈ range n,c (k+1))-C*n)/n +
            c (n+1)/(n+1) := by linarith
        _ ≤ C*(harmonic n : ℝ) + ((∑ k ∈ range n,c (k+1))-C*n)/(n+1) +
            c (n+1)/(n+1) := by linarith
        _ = _ := by
          rw [sum_range_succ, harmonic_succ]
          push_cast
          field_simp
          <;> ring
  have hd := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hC n)) (Nat.cast_nonneg n)
  linarith [strong n]

lemma log_weight (n : ℕ) :
    (∑ p ∈ n.primesLE, Real.log p / p) ≤ Real.log 4 * (harmonic n : ℝ) := by
  let c : ℕ → ℝ := fun k => if k.Prime then Real.log k else 0
  have hsum (n : ℕ) : (∑ k ∈ range n,c (k+1)) = Chebyshev.theta n := by
    rw [← Nat.Ico_zero_eq_range,sum_Ico_add' (fun k : ℕ => c k) 0 n 1]
    simp only [zero_add,Ico_add_one_right_eq_Icc]
    rw [Chebyshev.theta_eq_sum_primesLE_log,Nat.primesLE_eq_filter_Icc_one,sum_filter]
  have h := weighted_prefix_bound c (Real.log 4)
    (fun n => by rw [hsum]; exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) n
  have hsum' : (∑ k ∈ range n,c (k+1)/(k+1)) = ∑ p ∈ n.primesLE,Real.log p/p := by
    simp_rw [← Nat.cast_add_one]
    rw [← Nat.Ico_zero_eq_range,sum_Ico_add' (fun k : ℕ => c k/k) 0 n 1]
    simp only [zero_add, Ico_add_one_right_eq_Icc]
    rw [Nat.primesLE_eq_filter_Icc_one,sum_filter]
    simp only [c,ite_div,zero_div]
  rwa [hsum'] at h

noncomputable def rpowHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n:ℝ)^(-s)
  map_one' := by simp
  map_mul' n m := by
    push_cast
    exact mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg m)

lemma prime_rpow_small {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : p.Prime) :
    ‖rpowHom s p‖ < 1 := by
  change ‖(p:ℝ)^(-s)‖ < 1
  rw [norm_of_nonneg (rpow_nonneg (Nat.cast_nonneg p) _)]
  exact rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

noncomputable def geom (s : ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ n.primesLE, (1-(p:ℝ)^(-s))⁻¹

lemma geom_hasSum {s : ℝ} (hs : 0 < s) (n : ℕ) :
    HasSum (fun k : Nat.factoredNumbers n.primesLE => (k.val:ℝ)^(-s)) (geom s n) := by
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f:=rpowHom s) (fun {_} hp => prime_rpow_small hs hp) n.primesLE).2
  have hf : n.primesLE.filter Nat.Prime=n.primesLE :=
    filter_eq_self.mpr (fun p hp => (Nat.mem_primesLE.mp hp).2)
  rw [hf] at h
  exact h

lemma rpow_lt_one {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : p.Prime) :
    (p:ℝ)^(-s) < 1 := by
  exact (le_abs_self _).trans_lt (prime_rpow_small hs hp)

lemma geom_pos {s : ℝ} (hs : 0 < s) (n : ℕ) : 0 < geom s n := by
  apply prod_pos
  intro p hp
  exact inv_pos.mpr (sub_pos.mpr (rpow_lt_one hs (Nat.mem_primesLE.mp hp).2))

lemma log_geom {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Real.log (geom s n) = ∑ p ∈ n.primesLE,Real.log (1-(p:ℝ)^(-s))⁻¹ := by
  exact log_prod (fun p hp => inv_ne_zero (ne_of_gt
    (sub_pos.mpr (rpow_lt_one hs (Nat.mem_primesLE.mp hp).2))))

lemma sum_rpow_le_log_geom {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (∑ p ∈ n.primesLE,(p:ℝ)^(-s)) ≤ Real.log (geom s n) := by
  rw [log_geom hs]
  apply sum_le_sum
  intro p hp
  have h := one_sub_inv_le_log_of_pos (inv_pos.mpr
    (sub_pos.mpr (rpow_lt_one hs (Nat.mem_primesLE.mp hp).2)))
  simpa only [inv_inv,sub_sub_cancel] using h

lemma geom_le_zeta {s : ℝ} (hs : 1 < s) (n : ℕ) :
    geom s n ≤ ∑' k : ℕ, 1/(k:ℝ)^s := by
  have hsum : Summable (fun k : ℕ => (k:ℝ)^(-s)) := summable_nat_rpow.mpr (by linarith)
  rw [← (geom_hasSum (by linarith : 0 < s) n).tsum_eq]
  simpa only [rpow_neg (Nat.cast_nonneg _),one_div] using
    Summable.tsum_subtype_le (fun k : ℕ => (k:ℝ)^(-s))
      (Nat.factoredNumbers n.primesLE) (fun k => rpow_nonneg (Nat.cast_nonneg k) _) hsum

lemma harmonic_le_geom (n : ℕ) : (harmonic n : ℝ) ≤ geom 1 n := by
  have h := geom_hasSum (by norm_num : (0:ℝ)<1) n
  simp only [rpow_neg_one] at h
  have h' := (hasSum_subtype_iff_indicator (f:=fun k : ℕ => (k:ℝ)⁻¹)
    (s:=Nat.factoredNumbers n.primesLE)).mp h
  have hm {k : ℕ} (hk : k ∈ Icc 1 n) : k ∈ Nat.factoredNumbers n.primesLE := by
    refine Nat.mem_factoredNumbers_iff_forall_le.mpr ⟨by have := (mem_Icc.mp hk).1; omega,?_⟩
    intro p hpk hp _
    exact Nat.mem_primesLE.mpr ⟨hpk.trans (mem_Icc.mp hk).2,hp⟩
  calc
    _ = ∑ k ∈ Icc 1 n,(k:ℝ)⁻¹ := by simp [harmonic_eq_sum_Icc]
    _ = ∑ k ∈ Icc 1 n,(Nat.factoredNumbers n.primesLE).indicator
        (fun k : ℕ => (k:ℝ)⁻¹) k := by
      apply sum_congr rfl
      intro k hk
      rw [Set.indicator_of_mem (hm hk)]
    _ ≤ geom 1 n := by
      exact sum_le_hasSum _ (fun k _ => Set.indicator_nonneg (fun _ _ => by positivity) _) h'

lemma prime_error_le_one (n : ℕ) :
    (∑ p ∈ n.primesLE, (((p:ℝ)-1)⁻¹ - (p:ℝ)⁻¹)) ≤ 1 := by
  by_cases hn : n=0
  · simp [hn]
  have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hsub : n.primesLE ⊆ Icc 2 n := by
    intro p hp
    exact mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.two_le,(Nat.mem_primesLE.mp hp).1⟩
  calc
    _ ≤ ∑ p ∈ Icc 2 n, (((p:ℝ)-1)⁻¹ - (p:ℝ)⁻¹) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hp' : (2:ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp hp).1
      apply sub_nonneg.mpr
      have ha : (0:ℝ) < (p:ℝ)-1 := by linarith
      have hb : (p:ℝ)-1 ≤ p := by linarith
      simpa only [one_div] using one_div_le_one_div_of_le ha hb
    _ = 1-(n:ℝ)⁻¹ := by
      rw [← Ico_add_one_right_eq_Icc,
        ← sum_Ico_add' (fun p : ℕ => ((p:ℝ)-1)⁻¹-(p:ℝ)⁻¹) 1 n 1]
      simpa [Nat.cast_add,sub_eq_add_neg,add_comm]
        using (sum_Ico_sub (f:=fun p : ℕ => -(p:ℝ)⁻¹) hn')
    _ ≤ 1 := by linarith [inv_nonneg.mpr (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

lemma log_geom_one_le (n : ℕ) :
    Real.log (geom 1 n) ≤ (∑ p ∈ n.primesLE, (p:ℝ)⁻¹)+1 := by
  rw [log_geom (by norm_num : (0:ℝ)<1)]
  have h : (∑ p ∈ n.primesLE,Real.log (1-(p:ℝ)^(-(1:ℝ)))⁻¹) ≤
      ∑ p ∈ n.primesLE,((p:ℝ)-1)⁻¹ := by
    apply sum_le_sum
    intro p hp
    have hp' : (1:ℝ)<p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    have h := log_le_sub_one_of_pos (inv_pos.mpr (sub_pos.mpr
      (rpow_lt_one (by norm_num : (0:ℝ)<1) (Nat.mem_primesLE.mp hp).2)))
    simp only [rpow_neg_one] at h ⊢
    have he : (1-(p:ℝ)⁻¹)⁻¹-1=((p:ℝ)-1)⁻¹ := by
      field_simp [ne_of_gt (by linarith : (0:ℝ)<p-1)]
      <;> ring
    exact he ▸ h
  have he := prime_error_le_one n
  rw [sum_sub_distrib] at he
  linarith

lemma lower_bound (n : ℕ) (hn : 2 ≤ n) :
    Real.log (Real.log n)-1 ≤ ∑ p ∈ n.primesLE,(p:ℝ)⁻¹ := by
  have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hlo : Real.log (n:ℝ) ≤ (harmonic n : ℝ) :=
    (log_le_log (by positivity) (by exact_mod_cast Nat.le_succ n)).trans (log_add_one_le_harmonic n)
  have hH : (0:ℝ)<harmonic n := (log_pos hn').trans_le hlo
  have hlog := (log_le_log (log_pos hn') hlo).trans
    (log_le_log hH (harmonic_le_geom n))
  linarith [log_geom_one_le n]

lemma reciprocal_gap {s p : ℝ} (hp : 0 < p) :
    p⁻¹-p^(-s) ≤ (s-1)*Real.log p/p := by
  have he : p^(-s)=p⁻¹*exp (-(s-1)*Real.log p) := by
    rw [rpow_def_of_pos hp,show Real.log p * -s = -Real.log p + (-(s-1)*Real.log p) by ring,
      exp_add,exp_neg,exp_log hp]
  have h := mul_le_mul_of_nonneg_left (add_one_le_exp (-(s-1)*Real.log p)) (inv_nonneg.mpr hp.le)
  rw [he]
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

lemma upper_bound_eventually : ∀ᶠ n : ℕ in atTop,
    (∑ p ∈ n.primesLE,(p:ℝ)⁻¹) ≤ Real.log (Real.log n)+Real.log 2+2*Real.log 4 := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => 1+(Real.log (n:ℝ))⁻¹) atTop (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add hlog.inv_tendsto_atTop,?_⟩
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    simp only [Set.mem_Ioi]
    linarith [inv_pos.mpr hn]
  have hb := (tendsto_order.mp (tendsto_sub_mul_tsum_nat_rpow.comp hs)).2 2 (by norm_num)
  filter_upwards [hb,hlog.eventually_ge_atTop 1,eventually_ge_atTop 2] with n hb hn hn2
  let s : ℝ := 1+(Real.log (n:ℝ))⁻¹
  have hln : 0 < Real.log (n:ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hs1 : 1 < s := by dsimp [s]; linarith [inv_pos.mpr hln]
  have hz : (∑' k : ℕ,1/(k:ℝ)^s) ≤ 2*Real.log n := by
    change (s-1)*(∑' k : ℕ,1/(k:ℝ)^s) < 2 at hb
    dsimp [s] at hb
    rw [add_sub_cancel_left,inv_mul_eq_div] at hb
    exact ((div_lt_iff₀ hln).mp hb).le
  have hsum : (∑ p ∈ n.primesLE,(p:ℝ)⁻¹) - (∑ p ∈ n.primesLE,(p:ℝ)^(-s)) ≤
      (s-1)*(∑ p ∈ n.primesLE,Real.log p/p) := by
    rw [← sum_sub_distrib,mul_sum]
    exact sum_le_sum (fun p hp => by simpa [mul_div_assoc] using
      (reciprocal_gap (s:=s) (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos)))
  have hweight := log_weight n
  have hH := harmonic_le_one_add_log n
  have hC : 0 ≤ Real.log (4:ℝ) := log_nonneg (by norm_num)
  have hgap : (s-1)*(∑ p ∈ n.primesLE,Real.log p/p) ≤ 2*Real.log 4 := by
    calc
      _ ≤ (s-1)*(Real.log 4*(harmonic n : ℝ)) := mul_le_mul_of_nonneg_left hweight (le_of_lt (sub_pos.mpr hs1))
      _ ≤ (s-1)*(Real.log 4*(1+Real.log n)) := by gcongr
      _ ≤ 2*Real.log 4 := by
        dsimp [s]
        rw [add_sub_cancel_left]
        apply (inv_mul_le_iff₀ hln).2
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hn)]
  have hsr := sum_rpow_le_log_geom (by linarith : 0<s) n
  have hgeom := (geom_le_zeta hs1 n).trans hz
  have hl := log_le_log (geom_pos (by linarith : 0<s) n) hgeom
  rw [log_mul (by norm_num : (2:ℝ)≠0) hln.ne'] at hl
  linarith

theorem mertens_bounded : ∃ C : ℝ, ∀ n : ℕ,
    |(∑ p ∈ n.primesLE,(p:ℝ)⁻¹)-Real.log (Real.log n)| ≤ C := by
  let B : ℝ := 1+Real.log 2+2*Real.log 4
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hev : ∀ᶠ n : ℕ in atTop,
      |(∑ p ∈ n.primesLE,(p:ℝ)⁻¹)-Real.log (Real.log n)| ≤ B := by
    filter_upwards [upper_bound_eventually,eventually_ge_atTop 2] with n hu hn
    have hl := lower_bound n hn
    apply abs_le.mpr
    dsimp [B]
    constructor <;> linarith [log_nonneg (show (1:ℝ)≤2 by norm_num),log_nonneg (show (1:ℝ)≤4 by norm_num)]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨B+∑ k ∈ range N, |(∑ p ∈ k.primesLE,(p:ℝ)⁻¹)-Real.log (Real.log k)|,?_⟩
  intro n
  by_cases hn : N ≤ n
  · have h := hN n hn
    have hp := sum_nonneg (s:=range N)
      (fun k _ => abs_nonneg ((∑ p ∈ k.primesLE,(p:ℝ)⁻¹)-Real.log (Real.log k)))
    linarith
  · have h := single_le_sum (f:=fun k : ℕ => |(∑ p ∈ k.primesLE,(p:ℝ)⁻¹)-Real.log (Real.log k)|)
      (fun _ _ => abs_nonneg _) (mem_range.mpr (Nat.lt_of_not_ge hn))
    linarith

end D7Mertens


namespace D7Density
open Finset Real Filter ArithmeticFunction
open scoped Topology BigOperators ArithmeticFunction.zeta

noncomputable def weight : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else (10/7 : ℝ) ^ cardFactors n
  map_zero' := by simp

lemma weight_apply {n : ℕ} (hn : n ≠ 0) :
    weight n = (10/7 : ℝ) ^ cardFactors n := by simp [weight, hn]

lemma weight_mult : weight.IsMultiplicative := by
  apply IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [weight], ?_⟩
  intro m n hm hn _
  simp [weight_apply, hm, hn, mul_ne_zero hm hn, cardFactors_mul hm hn, pow_add]

lemma weight_nonneg (n : ℕ) : 0 ≤ weight n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [weight_apply hn]
    positivity

lemma weight_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    weight (p ^ k) = (10/7 : ℝ) ^ k := by
  rw [weight_apply (pow_ne_zero k hp.ne_zero), cardFactors_apply_prime_pow hp]

noncomputable def coeff : ArithmeticFunction ℝ :=
  (prodPrimeFactors (fun _ => (3/10 : ℝ))).pmul weight

lemma coeff_mult : coeff.IsMultiplicative :=
  (IsMultiplicative.prodPrimeFactors _).pmul weight_mult

lemma coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [coeff, pmul_apply, prodPrimeFactors_apply hn]
    exact mul_nonneg (prod_nonneg fun _ _ => by norm_num) (weight_nonneg n)

lemma coeff_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    coeff (p ^ (k + 1)) = (3/7 : ℝ) * (10/7 : ℝ) ^ k := by
  rw [coeff, pmul_apply, prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow (Nat.succ_ne_zero k) hp, prod_singleton,
    weight_prime_pow hp, pow_succ]
  ring

lemma coeff_divisor_sum (n : ℕ) : (∑ d ∈ n.divisors, coeff d) = weight n := by
  have heq : (ζ : ArithmeticFunction ℝ) * coeff = weight := by
    apply (IsMultiplicative.eq_iff_eq_on_prime_powers
      ((ζ : ArithmeticFunction ℝ) * coeff)
      (isMultiplicative_zeta.natCast.mul coeff_mult) weight weight_mult).mpr
    intro p k hp
    rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp, weight_prime_pow hp]
    induction k with
    | zero => simp [coeff_mult.map_one]
    | succ k ih =>
      rw [sum_range_succ, coeff_prime_pow hp, ih, pow_succ]
      ring
  simpa only [coe_zeta_mul_apply] using congrArg (fun f : ArithmeticFunction ℝ => f n) heq

lemma divisor_card_le_weight_sq (n : ℕ) : (n.divisors.card : ℝ) ≤ weight n ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [weight_mult.map_one]
  | prime_pow p k hp hk =>
    rw [← sigma_zero_apply, sigma_zero_apply_prime_pow hp, weight_prime_pow hp]
    have he : ∀ k : ℕ, (k + 1 : ℝ) ≤ ((10/7 : ℝ) ^ k) ^ 2 := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        rw [pow_succ (10/7 : ℝ) k, mul_pow]
        push_cast
        nlinarith
    exact_mod_cast he k
  | coprime m n hm hn hmn ih ih' =>
    rw [hmn.card_divisors_mul, Nat.cast_mul, weight_mult.map_mul_of_coprime hmn, mul_pow]
    exact mul_le_mul ih ih' (Nat.cast_nonneg _) (sq_nonneg _)

lemma sqrt_divisor_card_le_weight (n : ℕ) : Real.sqrt (n.divisors.card : ℝ) ≤ weight n := by
  exact (Real.sqrt_le_left (weight_nonneg n)).mpr (divisor_card_le_weight_sq n)

end D7Density

namespace D7Density
open Finset
open scoped BigOperators

lemma divisor_mean_bound (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, f d) ≤
      (N : ℝ) * ∑ d ∈ Icc 1 N, f d / d := by
  let I := Icc 1 N
  have hdiv {n : ℕ} (hn : n ∈ I) : n.divisors = I.filter (fun d => d ∣ n) := by
    ext d
    constructor
    · intro hd
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        (Nat.divisor_le hd).trans (mem_Icc.mp hn).2⟩, Nat.dvd_of_mem_divisors hd⟩
    · intro hd
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, by
        have := (mem_Icc.mp hn).1
        omega⟩
  have hcount {d : ℕ} (hd : d ∈ I) : (I.filter (fun n => d ∣ n)).card * d ≤ N := by
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hc : (I.filter (fun n => d ∣ n)).card ≤ N / d := by
      have hm : Set.MapsTo (fun n : ℕ => n / d) (I.filter (fun n => d ∣ n) : Set ℕ)
          (Icc 1 (N/d) : Set ℕ) := by
        intro n hn
        obtain ⟨hnI, hdn⟩ := mem_filter.mp hn
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnI
        have he : n / d * d = n := Nat.div_mul_cancel hdn
        exact mem_Icc.mpr ⟨by nlinarith, Nat.div_le_div_right hnN⟩
      have hi : Set.InjOn (fun n : ℕ => n / d) (I.filter (fun n => d ∣ n) : Set ℕ) := by
        intro n hn m hm hnm
        have hn' := Nat.div_mul_cancel (mem_filter.mp hn).2
        have hm' := Nat.div_mul_cancel (mem_filter.mp hm).2
        nlinarith
      simpa using Finset.card_le_card_of_injOn (fun n : ℕ => n/d) hm hi
    exact (Nat.mul_le_mul_right d hc).trans (Nat.div_mul_le_self N d)
  calc
    _ = ∑ n ∈ I, ∑ d ∈ I, if d ∣ n then f d else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [hdiv hn, sum_filter]
    _ = ∑ d ∈ I, ∑ n ∈ I, if d ∣ n then f d else 0 := sum_comm
    _ = ∑ d ∈ I, f d * ((I.filter (fun n => d ∣ n)).card : ℝ) := by
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter]
      simp [mul_comm]
    _ ≤ ∑ d ∈ I, (N : ℝ) * (f d / d) := by
      apply sum_le_sum
      intro d hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      have hcR : ((I.filter (fun n => d ∣ n)).card : ℝ) ≤ (N : ℝ)/d := by
        apply (le_div_iff₀ hdR).mpr
        exact_mod_cast hcount hd
      calc
        _ ≤ f d * ((N : ℝ)/d) := mul_le_mul_of_nonneg_left hcR (hf d)
        _ = _ := by ring
    _ = _ := by rw [mul_sum]

end D7Density
namespace D7Density
open Finset Real Filter ArithmeticFunction
open scoped Topology BigOperators ArithmeticFunction.zeta

noncomputable def localFactor (p : ℕ) : ℝ := 1 + (3/7 : ℝ) / ((p : ℝ) - 10/7)

lemma coeff_over_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    coeff (p ^ (k+1)) / ((p ^ (k+1) : ℕ) : ℝ) =
      (3 / (7 * (p : ℝ))) * ((10/7 : ℝ) / p) ^ k := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [coeff_prime_pow hp, Nat.cast_pow,
    div_pow (10/7 : ℝ) (p : ℝ) k, pow_succ (p : ℝ) k]
  field_simp [hp0, pow_ne_zero k hp0]
  <;> ring

lemma local_series {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => coeff (p ^ k) / ((p ^ k : ℕ) : ℝ)) (localFactor p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : 0 ≤ (10/7 : ℝ) / p := by positivity
  have hr1 : (10/7 : ℝ) / p < 1 := (div_lt_one hp0).mpr (by linarith)
  have hg : HasSum (fun k : ℕ => ((10/7 : ℝ)/p)^k) (1-(10/7 : ℝ)/p)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (ξ := (10/7 : ℝ) / p)
      (by simpa only [Real.norm_of_nonneg hr0] using hr1)
  have ht : HasSum (fun k : ℕ => coeff (p ^ (k+1)) / ((p ^ (k+1) : ℕ) : ℝ))
      ((3 / (7 * (p : ℝ))) * (1 - (10/7 : ℝ)/p)⁻¹) := by
    simp_rw [coeff_over_prime_pow hp]
    exact hg.mul_left (3 / (7 * (p : ℝ)))
  have hs := HasSum.zero_add (f := fun k : ℕ => coeff (p ^ k) / ((p ^ k : ℕ) : ℝ)) ht
  convert hs using 1
  simp only [pow_zero, Nat.cast_one, coeff_mult.map_one, div_one]
  dsimp [localFactor]
  have hpa : (p : ℝ) - 10/7 ≠ 0 := by linarith
  field_simp
  <;> ring

lemma smooth_coeff_series (N : ℕ) :
    HasSum (fun d : Nat.factoredNumbers N.primesLE => coeff d / (d : ℝ))
      (∏ p ∈ N.primesLE, localFactor p) := by
  have h1 : coeff 1 / ((1 : ℕ) : ℝ) = 1 := by simp [coeff_mult.map_one]
  have hm : ∀ {m n : ℕ}, m.Coprime n →
      coeff (m*n) / ((m*n : ℕ) : ℝ) = (coeff m / m) * (coeff n / n) := by
    intro m n hmn
    rw [coeff_mult.map_mul_of_coprime hmn, Nat.cast_mul, div_mul_div_comm]
  have hsum : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖coeff (p^k) / ((p^k : ℕ) : ℝ)‖) := by
    intro p hp
    simpa only [Real.norm_of_nonneg (div_nonneg (coeff_nonneg _) (Nat.cast_nonneg _))]
      using (local_series hp).summable
  have hs := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun d : ℕ => coeff d / (d : ℝ)) h1 hm hsum N.primesLE).2
  have hf : N.primesLE.filter Nat.Prime = N.primesLE :=
    filter_eq_self.mpr (fun p hp => (Nat.mem_primesLE.mp hp).2)
  rw [hf] at hs
  have he : (∏ p ∈ N.primesLE, ∑' k : ℕ, coeff (p^k) / ((p^k : ℕ) : ℝ)) =
      ∏ p ∈ N.primesLE, localFactor p := by
    apply prod_congr rfl
    intro p hp
    exact (local_series (Nat.mem_primesLE.mp hp).2).tsum_eq
  rwa [he] at hs

lemma coeff_prefix_le_product (N : ℕ) :
    (∑ d ∈ Icc 1 N, coeff d / d) ≤ ∏ p ∈ N.primesLE, localFactor p := by
  have hs := (hasSum_subtype_iff_indicator
    (f := fun d : ℕ => coeff d / d) (s := Nat.factoredNumbers N.primesLE)).mp
      (smooth_coeff_series N)
  have hm {d : ℕ} (hd : d ∈ Icc 1 N) : d ∈ Nat.factoredNumbers N.primesLE := by
    refine Nat.mem_factoredNumbers_iff_forall_le.mpr ⟨by have := (mem_Icc.mp hd).1; omega, ?_⟩
    intro p hpd hp _
    exact Nat.mem_primesLE.mpr ⟨hpd.trans (mem_Icc.mp hd).2, hp⟩
  calc
    _ = ∑ d ∈ Icc 1 N, (Nat.factoredNumbers N.primesLE).indicator
        (fun d : ℕ => coeff d / d) d := by
      apply sum_congr rfl
      intro d hd
      rw [Set.indicator_of_mem (hm hd)]
    _ ≤ _ := sum_le_hasSum _ (fun d _ =>
      Set.indicator_nonneg (fun _ _ => div_nonneg (coeff_nonneg _) (Nat.cast_nonneg _)) _) hs

lemma localFactor_pos {p : ℕ} (hp : p.Prime) : 0 < localFactor p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  dsimp [localFactor]
  have : (0 : ℝ) < (p : ℝ)-10/7 := by linarith
  positivity

lemma local_log_bound {p : ℕ} (hp : p.Prime) :
    Real.log (localFactor p) ≤ (3/7 : ℝ) / p + 2 * (((p : ℝ)-1)⁻¹ - (p : ℝ)⁻¹) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ)-1 := by linarith
  have hpa : (0 : ℝ) < (p : ℝ)-10/7 := by linarith
  have hlog := log_le_sub_one_of_pos (localFactor_pos hp)
  have he : (3/7 : ℝ)/p + 2*(((p : ℝ)-1)⁻¹-(p : ℝ)⁻¹) -
      (3/7 : ℝ)/((p : ℝ)-10/7) =
      ((68*(p : ℝ)-110)/49) / ((p : ℝ)*((p : ℝ)-1)*((p : ℝ)-10/7)) := by
    have hden : -10 + (p : ℝ)*7 ≠ 0 := by linarith
    field_simp [hp0.ne', hp1.ne', hpa.ne', hden]
    <;> ring_nf
    <;> field_simp [hden]
    <;> ring
  have hb : 0 ≤ (3/7 : ℝ)/p + 2*(((p : ℝ)-1)⁻¹-(p : ℝ)⁻¹) -
      (3/7 : ℝ)/((p : ℝ)-10/7) := by
    rw [he]
    apply div_nonneg _ (by positivity)
    linarith
  dsimp [localFactor] at hlog ⊢
  linarith

lemma product_log_bound (herr : ∀ N : ℕ,
    (∑ p ∈ N.primesLE, (((p : ℝ)-1)⁻¹-(p : ℝ)⁻¹)) ≤ 1) (N : ℕ) :
    Real.log (∏ p ∈ N.primesLE, localFactor p) ≤
      (3/7 : ℝ) * (∑ p ∈ N.primesLE, (p : ℝ)⁻¹) + 2 := by
  rw [log_prod (fun p hp => (localFactor_pos (Nat.mem_primesLE.mp hp).2).ne')]
  have h := sum_le_sum (s := N.primesLE) (fun p hp => local_log_bound (Nat.mem_primesLE.mp hp).2)
  simp only [sum_add_distrib, div_eq_mul_inv, ← mul_sum] at h
  linarith [herr N]

lemma product_power_bound (M : ℝ)
    (hM : ∀ N : ℕ, (∑ p ∈ N.primesLE, (p : ℝ)⁻¹) ≤ Real.log (Real.log N) + M)
    (herr : ∀ N : ℕ, (∑ p ∈ N.primesLE, (((p : ℝ)-1)⁻¹-(p : ℝ)⁻¹)) ≤ 1)
    {N : ℕ} (hN : 2 ≤ N) :
    (∏ p ∈ N.primesLE, localFactor p) ≤
      exp ((3/7 : ℝ)*M+2) * (Real.log (N : ℝ)) ^ (3/7 : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := log_pos hN1
  have hP : 0 < ∏ p ∈ N.primesLE, localFactor p :=
    prod_pos fun p hp => localFactor_pos (Nat.mem_primesLE.mp hp).2
  have hlog := product_log_bound herr N
  have hb : Real.log (∏ p ∈ N.primesLE, localFactor p) ≤
      ((3/7 : ℝ)*M+2) + Real.log (Real.log (N : ℝ)) * (3/7 : ℝ) := by
    linarith [hM N]
  have he := exp_le_exp.mpr hb
  rw [exp_log hP, exp_add, ← rpow_def_of_pos hl] at he
  exact he

lemma weight_mean_bound (M : ℝ)
    (hM : ∀ N : ℕ, (∑ p ∈ N.primesLE, (p : ℝ)⁻¹) ≤ Real.log (Real.log N) + M)
    (herr : ∀ N : ℕ, (∑ p ∈ N.primesLE, (((p : ℝ)-1)⁻¹-(p : ℝ)⁻¹)) ≤ 1)
    {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Icc 1 N, weight n) ≤
      exp ((3/7 : ℝ)*M+2) * (N : ℝ) * (Real.log (N : ℝ)) ^ (3/7 : ℝ) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, coeff d := by
      simp_rw [coeff_divisor_sum]
    _ ≤ (N : ℝ) * ∑ d ∈ Icc 1 N, coeff d / d :=
      divisor_mean_bound coeff coeff_nonneg N
    _ ≤ (N : ℝ) * ∏ p ∈ N.primesLE, localFactor p :=
      mul_le_mul_of_nonneg_left (coeff_prefix_le_product N) (Nat.cast_nonneg N)
    _ ≤ (N : ℝ) * (exp ((3/7 : ℝ)*M+2) * (Real.log (N : ℝ)) ^ (3/7 : ℝ)) :=
      mul_le_mul_of_nonneg_left (product_power_bound M hM herr hN) (Nat.cast_nonneg N)
    _ = _ := by ring

end D7Density


namespace D7Density
open Finset Real Filter ArithmeticFunction
open scoped Topology BigOperators ArithmeticFunction.zeta

def goodUpTo (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => (Nat.digits 2 n).length < n.divisors.card)

lemma log_le_binary_length (n : ℕ) (hn : 0 < n) :
    Real.log (n : ℝ) ≤ ((Nat.digits 2 n).length : ℝ) * Real.log 2 := by
  have hpow : (n : ℝ) < (2 : ℝ) ^ (Nat.digits 2 n).length := by
    exact_mod_cast (Nat.lt_base_pow_length_digits (b := 2) (m := n) (by decide))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := log_le_log hnR hpow.le
  rwa [Real.log_pow] at hl

lemma log_le_card_of_good {N n : ℕ} (hn : n ∈ goodUpTo N) :
    Real.log (n : ℝ) ≤ (n.divisors.card : ℝ) := by
  obtain ⟨hnI, hg⟩ := mem_filter.mp hn
  have hlen := log_le_binary_length n (mem_Icc.mp hnI).1
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have hlen0 : (0 : ℝ) ≤ (Nat.digits 2 n).length := Nat.cast_nonneg _
  have hcard : ((Nat.digits 2 n).length : ℝ) ≤ n.divisors.card := by
    exact_mod_cast hg.le
  nlinarith

lemma density_bound (C : ℝ)
    (hmean : ∀ N : ℕ, 2 ≤ N → (∑ n ∈ Icc 1 N, weight n) ≤
      C * (N : ℝ) * (Real.log (N : ℝ)) ^ (3/7 : ℝ))
    {N : ℕ} (hN : 2 ≤ N) :
    ((goodUpTo N).card : ℝ) / N ≤ (N : ℝ) ^ (-(1/2 : ℝ)) +
      2*C*(Real.log (N : ℝ)) ^ (-(1/14 : ℝ)) := by
  let M := ⌊sqrt (N : ℝ)⌋₊
  let T := (goodUpTo N).filter (fun n => M < n)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := log_pos hN1
  have hs : 0 < sqrt (Real.log (N : ℝ)) := sqrt_pos.mpr hl
  have hterm {n : ℕ} (hn : n ∈ T) : sqrt (Real.log (N : ℝ)) ≤ 2 * weight n := by
    obtain ⟨hnG, hnM⟩ := mem_filter.mp hn
    have hnroot : sqrt (N : ℝ) < (n : ℝ) :=
      (Nat.floor_lt (sqrt_nonneg (N : ℝ))).mp hnM
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hroot0 : 0 ≤ sqrt (N : ℝ) := sqrt_nonneg _
    have hsq : (N : ℝ) ≤ (n : ℝ)^2 := by
      nlinarith [sq_sqrt (Nat.cast_nonneg N)]
    have hln := log_le_log hN0 hsq
    rw [Real.log_pow] at hln
    norm_num only [Nat.cast_ofNat] at hln
    have hcard := log_le_card_of_good hnG
    have hw := divisor_card_le_weight_sq n
    have hw0 := weight_nonneg n
    apply (sqrt_le_left (by positivity : (0 : ℝ) ≤ 2*weight n)).mpr
    nlinarith [sq_nonneg (weight n)]
  have hTsub : T ⊆ Icc 1 N := by
    intro n hn
    exact (mem_filter.mp (mem_filter.mp hn).1).1
  have hsum : (T.card : ℝ) * sqrt (Real.log (N : ℝ)) ≤
      2 * C * (N : ℝ) * (Real.log (N : ℝ)) ^ (3/7 : ℝ) := by
    calc
      _ = ∑ n ∈ T, sqrt (Real.log (N : ℝ)) := by simp
      _ ≤ ∑ n ∈ T, 2 * weight n := sum_le_sum fun n hn => hterm hn
      _ = 2 * ∑ n ∈ T, weight n := (mul_sum _ _ _).symm
      _ ≤ 2 * ∑ n ∈ Icc 1 N, weight n :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hTsub (fun n _ _ => weight_nonneg n)) (by norm_num)
      _ ≤ _ := by linarith [hmean N hN]
  have hT : (T.card : ℝ) ≤
      (2 * C * (N : ℝ) * (Real.log (N : ℝ)) ^ (3/7 : ℝ)) / sqrt (Real.log (N : ℝ)) :=
    (le_div_iff₀ hs).mpr hsum
  have hsub : goodUpTo N ⊆ Icc 1 M ∪ T := by
    intro n hn
    by_cases hnM : n ≤ M
    · exact mem_union_left _ (mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hn).1).1, hnM⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn, by omega⟩)
  have hc : (goodUpTo N).card ≤ M + T.card := by
    have h := (card_le_card hsub).trans (card_union_le _ _)
    simpa using h
  have hcR : ((goodUpTo N).card : ℝ) ≤ sqrt (N : ℝ) + T.card := by
    have hcast : ((goodUpTo N).card : ℝ) ≤ (M : ℝ) + T.card := by exact_mod_cast hc
    have hf : (M : ℝ) ≤ sqrt (N : ℝ) := Nat.floor_le (sqrt_nonneg _)
    linarith
  have hratio : sqrt (N : ℝ) / N = (N : ℝ) ^ (-(1/2 : ℝ)) := by
    rw [sqrt_eq_rpow]
    convert (rpow_sub hN0 (1/2 : ℝ) 1).symm using 1 <;> norm_num
  have hlogratio : (Real.log (N : ℝ)) ^ (3/7 : ℝ) / sqrt (Real.log (N : ℝ)) =
      (Real.log (N : ℝ)) ^ (-(1/14 : ℝ)) := by
    rw [sqrt_eq_rpow]
    convert (rpow_sub hl (3/7 : ℝ) (1/2 : ℝ)).symm using 1 <;> norm_num
  calc
    _ ≤ (sqrt (N : ℝ) + T.card) / N := (div_le_div_iff_of_pos_right hN0).mpr hcR
    _ = sqrt (N : ℝ)/N + (T.card : ℝ)/N := add_div _ _ _
    _ ≤ sqrt (N : ℝ)/N +
        ((2*C*(N : ℝ)*(Real.log (N : ℝ))^(3/7 : ℝ))/sqrt (Real.log (N : ℝ)))/N := by
      gcongr
    _ = sqrt (N : ℝ)/N + 2*C*((Real.log (N : ℝ))^(3/7 : ℝ)/sqrt (Real.log (N : ℝ))) := by
      field_simp
      <;> ring
    _ = _ := by rw [hratio, hlogratio]

lemma density_tendsto (C : ℝ)
    (hmean : ∀ N : ℕ, 2 ≤ N → (∑ n ∈ Icc 1 N, weight n) ≤
      C * (N : ℝ) * (Real.log (N : ℝ)) ^ (3/7 : ℝ)) :
    Tendsto (fun N : ℕ => ((goodUpTo N).card : ℝ) / N) atTop (𝓝 (0 : ℝ)) := by
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop := tendsto_log_atTop.comp hNat
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)).comp hNat
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/14)).comp hlog
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N))
    ((eventually_ge_atTop 2).mono fun N hN => density_bound C hmean hN)
  simpa only [Function.comp_def, mul_zero, add_zero] using
    h1.add ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 2*C) atTop (𝓝 (2*C))).mul h2)

end D7Density


namespace D7Density
open Finset Real Filter
open scoped Topology BigOperators

theorem complete_density :
    Tendsto (fun N : ℕ => ((goodUpTo N).card : ℝ) / N) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨M, hM⟩ := D7Mertens.mertens_bounded
  have hupper : ∀ N : ℕ, (∑ p ∈ N.primesLE, (p : ℝ)⁻¹) ≤ Real.log (Real.log N) + M := by
    intro N
    have h := (abs_le.mp (hM N)).2
    linarith
  exact density_tendsto (exp ((3/7 : ℝ)*M+2))
    (fun N hN => weight_mean_bound M hupper D7Mertens.prime_error_le_one hN)

end D7Density

theorem OMA.solution : type_of% @OMA.S_oeis_a346695.main := by
  simpa only [OMA.S_oeis_a346695.qualifyingUpTo, D7Density.goodUpTo] using
    D7Density.complete_density
