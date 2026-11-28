import OMAReductions.R_Erdos377_erdos_377_variants_ub_R1
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
    (∑ p ∈ n.primesLE, log p / p) ≤ log 4 * (harmonic n : ℝ) := by
  let c : ℕ → ℝ := fun k => if k.Prime then log k else 0
  have hsum (n : ℕ) : (∑ k ∈ range n,c (k+1)) = Chebyshev.theta n := by
    rw [← Nat.Ico_zero_eq_range,sum_Ico_add' (fun k : ℕ => c k) 0 n 1]
    simp only [zero_add,Ico_add_one_right_eq_Icc]
    rw [Chebyshev.theta_eq_sum_primesLE_log,Nat.primesLE_eq_filter_Icc_one,sum_filter]
  have h := weighted_prefix_bound c (log 4)
    (fun n => by rw [hsum]; exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) n
  have hsum' : (∑ k ∈ range n,c (k+1)/(k+1)) = ∑ p ∈ n.primesLE,log p/p := by
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
    log (geom s n) = ∑ p ∈ n.primesLE,log (1-(p:ℝ)^(-s))⁻¹ := by
  exact log_prod (fun p hp => inv_ne_zero (ne_of_gt
    (sub_pos.mpr (rpow_lt_one hs (Nat.mem_primesLE.mp hp).2))))

lemma sum_rpow_le_log_geom {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (∑ p ∈ n.primesLE,(p:ℝ)^(-s)) ≤ log (geom s n) := by
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
    log (geom 1 n) ≤ (∑ p ∈ n.primesLE, (p:ℝ)⁻¹)+1 := by
  rw [log_geom (by norm_num : (0:ℝ)<1)]
  have h : (∑ p ∈ n.primesLE,log (1-(p:ℝ)^(-(1:ℝ)))⁻¹) ≤
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
    log (log n)-1 ≤ ∑ p ∈ n.primesLE,(p:ℝ)⁻¹ := by
  have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hlo : log (n:ℝ) ≤ (harmonic n : ℝ) :=
    (log_le_log (by positivity) (by exact_mod_cast Nat.le_succ n)).trans (log_add_one_le_harmonic n)
  have hH : (0:ℝ)<harmonic n := (log_pos hn').trans_le hlo
  have hlog := (log_le_log (log_pos hn') hlo).trans
    (log_le_log hH (harmonic_le_geom n))
  linarith [log_geom_one_le n]

lemma reciprocal_gap {s p : ℝ} (hp : 0 < p) :
    p⁻¹-p^(-s) ≤ (s-1)*log p/p := by
  have he : p^(-s)=p⁻¹*exp (-(s-1)*log p) := by
    rw [rpow_def_of_pos hp,show log p * -s = -log p + (-(s-1)*log p) by ring,
      exp_add,exp_neg,exp_log hp]
  have h := mul_le_mul_of_nonneg_left (add_one_le_exp (-(s-1)*log p)) (inv_nonneg.mpr hp.le)
  rw [he]
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

lemma upper_bound_eventually : ∀ᶠ n : ℕ in atTop,
    (∑ p ∈ n.primesLE,(p:ℝ)⁻¹) ≤ log (log n)+log 2+2*log 4 := by
  have hlog : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => 1+(log (n:ℝ))⁻¹) atTop (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add hlog.inv_tendsto_atTop,?_⟩
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    simp only [Set.mem_Ioi]
    linarith [inv_pos.mpr hn]
  have hb := (tendsto_order.mp (tendsto_sub_mul_tsum_nat_rpow.comp hs)).2 2 (by norm_num)
  filter_upwards [hb,hlog.eventually_ge_atTop 1,eventually_ge_atTop 2] with n hb hn hn2
  let s : ℝ := 1+(log (n:ℝ))⁻¹
  have hln : 0 < log (n:ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hs1 : 1 < s := by dsimp [s]; linarith [inv_pos.mpr hln]
  have hz : (∑' k : ℕ,1/(k:ℝ)^s) ≤ 2*log n := by
    change (s-1)*(∑' k : ℕ,1/(k:ℝ)^s) < 2 at hb
    dsimp [s] at hb
    rw [add_sub_cancel_left,inv_mul_eq_div] at hb
    exact ((div_lt_iff₀ hln).mp hb).le
  have hsum : (∑ p ∈ n.primesLE,(p:ℝ)⁻¹) - (∑ p ∈ n.primesLE,(p:ℝ)^(-s)) ≤
      (s-1)*(∑ p ∈ n.primesLE,log p/p) := by
    rw [← sum_sub_distrib,mul_sum]
    exact sum_le_sum (fun p hp => by simpa [mul_div_assoc] using
      (reciprocal_gap (s:=s) (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos)))
  have hweight := log_weight n
  have hH := harmonic_le_one_add_log n
  have hC : 0 ≤ log (4:ℝ) := log_nonneg (by norm_num)
  have hgap : (s-1)*(∑ p ∈ n.primesLE,log p/p) ≤ 2*log 4 := by
    calc
      _ ≤ (s-1)*(log 4*(harmonic n : ℝ)) := mul_le_mul_of_nonneg_left hweight (le_of_lt (sub_pos.mpr hs1))
      _ ≤ (s-1)*(log 4*(1+log n)) := by gcongr
      _ ≤ 2*log 4 := by
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
    |(∑ p ∈ n.primesLE,(p:ℝ)⁻¹)-log (log n)| ≤ C := by
  let B : ℝ := 1+log 2+2*log 4
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hev : ∀ᶠ n : ℕ in atTop,
      |(∑ p ∈ n.primesLE,(p:ℝ)⁻¹)-log (log n)| ≤ B := by
    filter_upwards [upper_bound_eventually,eventually_ge_atTop 2] with n hu hn
    have hl := lower_bound n hn
    apply abs_le.mpr
    dsimp [B]
    constructor <;> linarith [log_nonneg (show (1:ℝ)≤2 by norm_num),log_nonneg (show (1:ℝ)≤4 by norm_num)]
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨B+∑ k ∈ range N, |(∑ p ∈ k.primesLE,(p:ℝ)⁻¹)-log (log k)|,?_⟩
  intro n
  by_cases hn : N ≤ n
  · have h := hN n hn
    have hp := sum_nonneg (s:=range N)
      (fun k _ => abs_nonneg ((∑ p ∈ k.primesLE,(p:ℝ)⁻¹)-log (log k)))
    linarith
  · have h := single_le_sum (f:=fun k : ℕ => |(∑ p ∈ k.primesLE,(p:ℝ)⁻¹)-log (log k)|)
      (fun _ _ => abs_nonneg _) (mem_range.mpr (Nat.lt_of_not_ge hn))
    linarith

end D7Mertens

theorem OMA.solution : OMA.R_Erdos377_erdos_377_variants_ub_R1.H1 := by
  simpa only [OMA.R_Erdos377_erdos_377_variants_ub_R1.H1,one_div] using D7Mertens.mertens_bounded
