import OMAStatements.S_oeis_a401897
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries

open OMA.S_oeis_a401897
open ArithmeticFunction Finset Filter MeasureTheory Bornology WithLp
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Pointwise Topology

namespace OMA.S_oeis_a401897.Proof

private noncomputable def disk (z : ℕ × ℕ) : Finset (ℤ × ℤ) :=
  let r : ℤ := normSq z
  (Finset.Icc (-r) r ×ˢ Finset.Icc (-r) r).filter (fun w => w.1 ^ 2 + w.2 ^ 2 < r)

private def displacementGcd (z : ℕ × ℕ) (w : ℤ × ℤ) : ℕ :=
  Nat.gcd (w.1 - (z.1 : ℤ)).natAbs (w.2 - (z.2 : ℤ)).natAbs

private theorem indicator (g : ℕ) :
    (∑ d ∈ g.divisors, μ d) = if g = 1 then 1 else (0 : ℤ) := by
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

private theorem visible_moebius (z : ℕ × ℕ) :
    (visible z : ℤ) = ∑ w ∈ disk z, ∑ d ∈ (displacementGcd z w).divisors, μ d := by
  simp_rw [indicator]
  rw [Finset.sum_boole]
  have h : visible z = ((disk z).filter (fun w => displacementGcd z w = 1)).card := by
    unfold visible disk displacementGcd Nat.Coprime
    apply congrArg Finset.card
    ext w
    simp only [Finset.mem_filter]
    tauto
  exact_mod_cast h

private theorem gcd_bound (z : ℕ × ℕ) (w : ℤ × ℤ) (hw : w ∈ disk z) :
    displacementGcd z w ≤ 2 * normSq z := by
  have bounds := Finset.mem_product.mp (Finset.mem_filter.mp hw).1
  obtain ⟨h1, h2⟩ := bounds
  have hX := Finset.mem_Icc.mp h1
  have hY := Finset.mem_Icc.mp h2
  have hz1 : z.1 ≤ normSq z := by
    unfold normSq
    have := Nat.le_self_pow (by decide : 2 ≠ 0) z.1
    omega
  have hz2 : z.2 ≤ normSq z := by
    unfold normSq
    have := Nat.le_self_pow (by decide : 2 ≠ 0) z.2
    omega
  have hx : (w.1 - (z.1 : ℤ)).natAbs ≤ 2 * normSq z := by omega
  have hy : (w.2 - (z.2 : ℤ)).natAbs ≤ 2 * normSq z := by omega
  unfold displacementGcd
  by_cases h0 : (w.1 - (z.1 : ℤ)).natAbs = 0
  · simpa [h0] using hy
  · exact (Nat.gcd_le_left _ (Nat.pos_of_ne_zero h0)).trans hx

private noncomputable def multiples (z : ℕ × ℕ) (d : ℕ) : ℕ :=
  ((disk z).filter (fun w => d ∈ (displacementGcd z w).divisors)).card

private theorem visible_divisor_sum (z : ℕ × ℕ) :
    (visible z : ℤ) = ∑ d ∈ range (2 * normSq z + 1), μ d * (multiples z d : ℤ) := by
  rw [visible_moebius]
  have step (w : ℤ × ℤ) (hw : w ∈ disk z) :
      (∑ d ∈ (displacementGcd z w).divisors, μ d) =
        ∑ d ∈ range (2 * normSq z + 1), if d ∈ (displacementGcd z w).divisors then μ d else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨by
      have hd := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp h).2) (Nat.mem_divisors.mp h).1
      have hb := gcd_bound z w hw
      omega, h⟩, And.right⟩
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [multiples, Finset.natCast_card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split <;> simp_all

private noncomputable def densityTerm (d : ℕ) : ℝ := (μ d : ℝ) / (d : ℝ) ^ 2

private theorem density_hasSum : HasSum densityTerm (6 / Real.pi ^ 2) := by
  have hre : 1 < (2 : ℂ).re := by norm_num
  have conj := LSeries_zeta_mul_Lseries_moebius hre
  rw [LSeries_zeta_eq_riemannZeta hre, riemannZeta_two] at conj
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hValue : LSeries (fun n => (μ n : ℂ)) 2 = 6 / (Real.pi : ℂ) ^ 2 := by
    apply mul_left_cancel₀ (a := (Real.pi : ℂ) ^ 2 / 6) (div_ne_zero (pow_ne_zero _ hpi) (by norm_num))
    rw [conj]
    field_simp
  have hS : HasSum (LSeries.term (fun n => (μ n : ℂ)) 2) (6 / (Real.pi : ℂ) ^ 2) := by
    rw [← hValue]
    exact (LSeriesSummable_moebius_iff.mpr hre).hasSum
  have hTerm (d : ℕ) : LSeries.term (fun n => (μ n : ℂ)) 2 d = (densityTerm d : ℂ) := by
    rw [LSeries.term_of_ne_zero' (by norm_num : (2 : ℂ) ≠ 0)]
    simp [densityTerm]
  rw [funext hTerm] at hS
  apply Complex.hasSum_ofReal.mp
  push_cast
  exact hS

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def point (w : ℤ × ℤ) : Plane := toLp 2 ![(w.1 : ℝ), (w.2 : ℝ)]

private theorem point_normSq (w : ℤ × ℤ) :
    ‖point w‖ ^ 2 = (w.1 : ℝ)^2 + (w.2 : ℝ)^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [point, sq_abs]

private def unitRegion : Set (Fin 2 → ℝ) :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm ⁻¹' Metric.ball (0 : Plane) 1

private theorem unitRegion_bdd : IsBounded unitRegion := by
  have h := (isCompact_closedBall (0 : Plane) 1).image (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))
  apply h.isBounded.subset
  intro x hx
  exact ⟨toLp 2 x, Metric.ball_subset_closedBall hx, rfl⟩

private theorem unitRegion_measurable : MeasurableSet unitRegion :=
  (Metric.isOpen_ball.preimage (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm.continuous).measurableSet

private theorem unitRegion_frontier : volume (frontier unitRegion) = 0 := by
  unfold unitRegion
  rw [← Homeomorph.preimage_frontier]
  change volume ((toLp 2 : (Fin 2 → ℝ) → Plane) ⁻¹' frontier (Metric.ball 0 1)) = 0
  rw [(PiLp.volume_preserving_toLp (Fin 2)).measure_preimage measurableSet_frontier.nullMeasurableSet]
  exact measure_mono_null Metric.frontier_ball_subset_sphere (Measure.addHaar_sphere volume _ _)

private theorem unitRegion_volume : volume.real unitRegion = Real.pi := by
  unfold unitRegion
  change (volume ((toLp 2 : (Fin 2 → ℝ) → Plane) ⁻¹' Metric.ball 0 1)).toReal = Real.pi
  rw [(PiLp.volume_preserving_toLp (Fin 2)).measure_preimage Metric.isOpen_ball.measurableSet.nullMeasurableSet,
    EuclideanSpace.volume_ball_fin_two]
  simp [Real.pi_nonneg]

private theorem scale_region (r : ℝ) (hr : 0 < r) :
    r • unitRegion = (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm ⁻¹' Metric.ball (0 : Plane) r := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    change dist (toLp 2 x) 0 < 1 at hx
    have hx' : ‖toLp 2 x‖ < 1 := by rwa [dist_zero_right] at hx
    change dist (toLp 2 (r • x)) 0 < r
    rw [dist_zero_right]
    change ‖r • toLp 2 x‖ < r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simpa using mul_lt_mul_of_pos_left hx' hr
  · intro hv
    change dist (toLp 2 v) 0 < r at hv
    rw [dist_zero_right] at hv
    refine ⟨r⁻¹ • v, ?_, smul_inv_smul₀ hr.ne' v⟩
    change dist (toLp 2 (r⁻¹ • v)) 0 < 1
    rw [dist_zero_right]
    change ‖r⁻¹ • toLp 2 v‖ < 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    simpa [inv_mul_cancel₀ hr.ne'] using mul_lt_mul_of_pos_left hv (inv_pos.mpr hr)

private theorem scale_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : x • unitRegion ⊆ y • unitRegion := by
  rw [scale_region x hx, scale_region y (hx.trans_le hxy)]
  exact Set.preimage_mono (Metric.ball_subset_ball hxy)

private noncomputable def ballCount (r : ℝ) : ℕ := Nat.card {w : ℤ × ℤ // ‖point w‖ < r}

private theorem span_iff (v : Fin 2 → ℝ) :
    v ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2))) ↔
      ∀ i : Fin 2, ∃ t : ℤ, (t : ℝ) = v i := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  simp [Pi.basisFun_repr, Set.mem_range, Int.castRingHom]

private theorem coord_injective : Function.Injective (fun w : ℤ × ℤ => ofLp (point w)) := by
  intro w v hv
  apply Prod.ext
  · have h := congrFun hv 0
    change (w.1 : ℝ) = v.1 at h
    exact_mod_cast h
  · have h := congrFun hv 1
    change (w.2 : ℝ) = v.2 at h
    exact_mod_cast h

private theorem ball_equiv_scaled (r : ℝ) (hr : 0 < r) :
    ballCount r = Nat.card ↑(unitRegion ∩ r⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) := by
  let f : {w : ℤ × ℤ // ‖point w‖ < r} →
      ↑(unitRegion ∩ r⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))) :=
    fun w => ⟨r⁻¹ • ofLp (point w.val), ⟨by
      change dist (r⁻¹ • point w.val) 0 < 1
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      simpa [inv_mul_cancel₀ hr.ne'] using mul_lt_mul_of_pos_left w.prop (inv_pos.mpr hr),
    ⟨ofLp (point w.val), (span_iff _).mpr (fun i => by
      fin_cases i
      · exact ⟨w.val.1, rfl⟩
      · exact ⟨w.val.2, rfl⟩), rfl⟩⟩⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro w v h
    apply Subtype.ext
    apply coord_injective
    have hh := congrArg Subtype.val h
    change r⁻¹ • ofLp (point w.val) = r⁻¹ • ofLp (point v.val) at hh
    simpa only [smul_inv_smul₀ hr.ne'] using congrArg (r • ·) hh
  · rintro ⟨y, hyR, x, hxL, rfl⟩
    obtain ⟨a, ha⟩ := (span_iff x).mp hxL 0
    obtain ⟨b, hb⟩ := (span_iff x).mp hxL 1
    have hx : ofLp (point (a, b)) = x := by
      funext i
      fin_cases i
      · exact ha
      · exact hb
    have hR : x ∈ r • unitRegion := ⟨r⁻¹ • x, hyR, smul_inv_smul₀ hr.ne' x⟩
    rw [scale_region r hr, ← hx] at hR
    have hNorm : ‖point (a, b)‖ < r := by
      change dist (point (a, b)) 0 < r at hR
      simpa only [dist_zero_right] using hR
    exact ⟨⟨(a, b), hNorm⟩, Subtype.ext (by simpa [f] using congrArg (r⁻¹ • ·) hx)⟩

private theorem ball_limit : Tendsto (fun r : ℝ => (ballCount r : ℝ) / r ^ 2)
    atTop (𝓝 Real.pi) := by
  have h := tendsto_card_div_pow_atTop_volume' unitRegion unitRegion_bdd unitRegion_measurable
    unitRegion_frontier (fun ⦃x y⦄ hx hxy => @scale_mono x y hx hxy)
  rw [unitRegion_volume] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp [ball_equiv_scaled r hr]

private theorem finite_ball (r : ℝ) : Set.Finite {w : ℤ × ℤ | ‖point w‖ < r} := by
  let N : ℤ := ⌈r⌉
  apply ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset
  intro w hw
  have hn : ‖point w‖ < r := hw
  have hc : r ≤ (N : ℝ) := Int.le_ceil r
  have habs (i : Fin 2) : ‖point w i‖ < N := (PiLp.norm_apply_le (point w) i).trans_lt (hn.trans_le hc)
  have h0 := habs 0
  have h1 := habs 1
  change ‖(w.1 : ℝ)‖ < (N : ℝ) at h0
  change ‖(w.2 : ℝ)‖ < (N : ℝ) at h1
  rw [Real.norm_eq_abs, abs_lt] at h0 h1
  exact ⟨⟨by exact_mod_cast h0.1.le, by exact_mod_cast h0.2.le⟩,
    ⟨by exact_mod_cast h1.1.le, by exact_mod_cast h1.2.le⟩⟩

private noncomputable def radius (z : ℕ × ℕ) : ℝ := Real.sqrt (normSq z)

private theorem radius_sq (z : ℕ × ℕ) : (radius z) ^ 2 = normSq z :=
  Real.sq_sqrt (by positivity)

private theorem radius_nonneg (z : ℕ × ℕ) : 0 ≤ radius z := Real.sqrt_nonneg _

private theorem norm_observer (z : ℕ × ℕ) :
    ‖point ((z.1 : ℤ), (z.2 : ℤ))‖ = radius z := by
  have h := point_normSq ((z.1 : ℤ), (z.2 : ℤ))
  simp only [Int.cast_natCast] at h
  have hr := radius_sq z
  push_cast [normSq] at hr
  nlinarith [norm_nonneg (point ((z.1 : ℤ), (z.2 : ℤ))), radius_nonneg z]

private theorem disk_iff (z : ℕ × ℕ) (w : ℤ × ℤ) : w ∈ disk z ↔ ‖point w‖ < radius z := by
  have hsq := point_normSq w
  have hr := radius_sq z
  have hn := norm_nonneg (point w)
  have hR := radius_nonneg z
  constructor
  · intro hw
    have hb : (w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2 < (normSq z : ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hw).2
    nlinarith
  · intro hw
    have hsq' : (w.1 : ℝ) ^ 2 + (w.2 : ℝ) ^ 2 < (normSq z : ℝ) := by
      nlinarith
    have hsz : (0 : ℝ) < normSq z := (by positivity : 0 ≤ (w.1 : ℝ)^2 + (w.2 : ℝ)^2).trans_lt hsq'
    have hN : (1 : ℝ) ≤ normSq z := by
      exact_mod_cast (Nat.succ_le_of_lt (by exact_mod_cast hsz : 0 < normSq z))
    have hRadius : radius z ≤ (normSq z : ℝ) := by
      by_contra! hbad
      nlinarith
    have hcoord (i : Fin 2) : ‖point w i‖ < (normSq z : ℝ) :=
      (PiLp.norm_apply_le (point w) i).trans_lt (hw.trans_le hRadius)
    have h0 := hcoord 0
    have h1 := hcoord 1
    change ‖(w.1 : ℝ)‖ < _ at h0
    change ‖(w.2 : ℝ)‖ < _ at h1
    rw [Real.norm_eq_abs, abs_lt] at h0 h1
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_,
      Finset.mem_Icc.mpr ?_⟩, by exact_mod_cast hsq'⟩
    · exact ⟨by exact_mod_cast h0.1.le, by exact_mod_cast h0.2.le⟩
    · exact ⟨by exact_mod_cast h1.1.le, by exact_mod_cast h1.2.le⟩

private theorem displacement_pos (z : ℕ × ℕ) (w : ℤ × ℤ) (hw : w ∈ disk z) :
    displacementGcd z w ≠ 0 := by
  intro h
  have h0 : w.1 = (z.1 : ℤ) ∧ w.2 = (z.2 : ℤ) := by
    simpa [displacementGcd, Nat.gcd_eq_zero_iff, Int.natAbs_eq_zero, sub_eq_zero] using h
  have he : w = ((z.1 : ℤ), (z.2 : ℤ)) := Prod.ext h0.1 h0.2
  have hd := (disk_iff z w).mp hw
  rw [he, norm_observer] at hd
  exact (lt_irrefl _) hd

private theorem displacement_le (z : ℕ × ℕ) (w : ℤ × ℤ) (hw : w ∈ disk z) :
    (displacementGcd z w : ℝ) ≤ 2 * radius z := by
  have hn := (disk_iff z w).mp hw
  have habs (i : Fin 2) :
      ‖point w i - point ((z.1 : ℤ), (z.2 : ℤ)) i‖ ≤ 2 * radius z := by
    calc
      _ ≤ ‖point w i‖ + ‖point ((z.1 : ℤ), (z.2 : ℤ)) i‖ := norm_sub_le _ _
      _ ≤ ‖point w‖ + ‖point ((z.1 : ℤ), (z.2 : ℤ))‖ :=
        add_le_add (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)
      _ ≤ _ := by rw [norm_observer]; linarith
  have h0 := habs 0
  have h1 := habs 1
  change ‖(w.1 : ℝ) - ((z.1 : ℤ) : ℝ)‖ ≤ _ at h0
  change ‖(w.2 : ℝ) - ((z.2 : ℤ) : ℝ)‖ ≤ _ at h1
  rw [Real.norm_eq_abs, ← Int.cast_sub, ← Int.cast_abs, ← Int.natCast_natAbs] at h0 h1
  simp only [Int.cast_natCast] at h0 h1
  unfold displacementGcd
  by_cases ha : (w.1 - (z.1 : ℤ)).natAbs = 0
  · simpa [ha] using h1
  · exact (by exact_mod_cast Nat.gcd_le_left _ (Nat.pos_of_ne_zero ha) : _ ≤ ((w.1 - (z.1 : ℤ)).natAbs : ℝ)).trans h0

private theorem large_multiples_zero (z : ℕ × ℕ) (d : ℕ) (hd : 2 * radius z < d) :
    multiples z d = 0 := by
  unfold multiples
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hw, hm⟩ := Finset.mem_filter.mp hw
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (displacement_pos z w hw)) (Nat.mem_divisors.mp hm).1
  exact (not_le_of_gt hd) ((by exact_mod_cast hle : (d : ℝ) ≤ (displacementGcd z w : ℝ)).trans
    (displacement_le z w hw))

private theorem zero_multiples (z : ℕ × ℕ) : multiples z 0 = 0 := by
  unfold multiples
  simp

private def residue (z : ℕ × ℕ) (d : ℕ) : ℤ × ℤ :=
  (((z.1 : ℤ) % d), ((z.2 : ℤ) % d))

private noncomputable def shift (z : ℕ × ℕ) (d : ℕ) : Plane :=
  (d : ℝ)⁻¹ • point (residue z d)

private theorem shift_bound (z : ℕ × ℕ) (d : ℕ) (hd : 0 < d) :
    ‖shift z d‖ ≤ 2 := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hb (w : ℤ) : 0 ≤ w % (d : ℤ) ∧ w % (d : ℤ) < d :=
    ⟨Int.emod_nonneg _ hd'.ne', Int.emod_lt_of_pos _ hd'⟩
  have ha := hb z.1
  have hB := hb z.2
  have hrN := point_normSq (residue z d)
  have hcastA : (0 : ℝ) ≤ ((residue z d).1 : ℝ) ∧ ((residue z d).1 : ℝ) ≤ d :=
    ⟨by simpa only [Int.cast_zero] using (Int.cast_le.mpr ha.1 : ((0 : ℤ) : ℝ) ≤ ((residue z d).1 : ℝ)), Int.cast_le.mpr ha.2.le⟩
  have hcastB : (0 : ℝ) ≤ ((residue z d).2 : ℝ) ∧ ((residue z d).2 : ℝ) ≤ d :=
    ⟨by simpa only [Int.cast_zero] using (Int.cast_le.mpr hB.1 : ((0 : ℤ) : ℝ) ≤ ((residue z d).2 : ℝ)), Int.cast_le.mpr hB.2.le⟩
  have hN : ‖point (residue z d)‖ ≤ 2 * (d : ℝ) := by
    nlinarith [sq_nonneg (‖point (residue z d)‖ - 2 * (d : ℝ)),
      mul_nonneg (sub_nonneg.mpr hcastA.2) hcastA.1,
      mul_nonneg (sub_nonneg.mpr hcastB.2) hcastB.1,
      mul_nonneg (sub_nonneg.mpr hcastA.2) (show 0 ≤ (d : ℝ) by positivity),
      mul_nonneg (sub_nonneg.mpr hcastB.2) (show 0 ≤ (d : ℝ) by positivity)]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  unfold shift
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdR), inv_mul_eq_div]
  exact (div_le_iff₀ hdR).mpr hN

private theorem coset (a b d : ℤ) :
    d ∣ a - b ↔ ∃ j : ℤ, a = d * j + b % d := by
  have hmod := Int.emod_add_mul_ediv b d
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q + b / d, ?_⟩
    linarith [mul_add d q (b / d)]
  · rintro ⟨q, hq⟩
    refine ⟨q - b / d, ?_⟩
    linarith [mul_sub d q (b / d)]

private def fromCoset (z : ℕ × ℕ) (d : ℕ) (v : ℤ × ℤ) : ℤ × ℤ :=
  ((d : ℤ) * v.1 + (residue z d).1, (d : ℤ) * v.2 + (residue z d).2)

private theorem scaled_point (z : ℕ × ℕ) (d : ℕ) (hd : 0 < d) (v : ℤ × ℤ) :
    point (fromCoset z d v) = (d : ℝ) • (point v + shift z d) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  ext i
  fin_cases i <;> simp [fromCoset, point, shift, hdR]

private theorem member_multiples (z : ℕ × ℕ) (d : ℕ) (w : ℤ × ℤ) (hw : w ∈ disk z) :
    d ∈ (displacementGcd z w).divisors ↔
      (d : ℤ) ∣ w.1 - (z.1 : ℤ) ∧ (d : ℤ) ∣ w.2 - (z.2 : ℤ) := by
  rw [Nat.mem_divisors, and_iff_left (displacement_pos z w hw), displacementGcd, Nat.dvd_gcd_iff]
  rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]

private noncomputable def shiftedSet (z : ℕ × ℕ) (d : ℕ) : Set (ℤ × ℤ) :=
  {v | ‖point v + shift z d‖ < radius z / d}

private theorem coset_disk (z : ℕ × ℕ) (d : ℕ) (hd : 0 < d) (v : ℤ × ℤ) :
    fromCoset z d v ∈ disk z ↔ v ∈ shiftedSet z d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [disk_iff, scaled_point z d hd]
  change ‖(d : ℝ) • (point v + shift z d)‖ < radius z ↔ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hdR]
  change _ ↔ ‖point v + shift z d‖ < radius z / d
  rw [lt_div_iff₀ hdR, mul_comm (d : ℝ)]

private theorem fromCoset_injective (z : ℕ × ℕ) (d : ℕ) (hd : 0 < d) :
    Function.Injective (fromCoset z d) := by
  have hn : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  intro v w h
  apply Prod.ext
  · have h' := congrArg Prod.fst h
    change (d : ℤ) * v.1 + (residue z d).1 = (d : ℤ) * w.1 + (residue z d).1 at h'
    exact mul_left_cancel₀ hn (add_right_cancel h')
  · have h' := congrArg Prod.snd h
    change (d : ℤ) * v.2 + (residue z d).2 = (d : ℤ) * w.2 + (residue z d).2 at h'
    exact mul_left_cancel₀ hn (add_right_cancel h')

private theorem multiples_eq (z : ℕ × ℕ) (d : ℕ) (hd : 0 < d) :
    multiples z d = Nat.card ↑(shiftedSet z d) := by
  let s := (disk z).filter (fun w => d ∈ (displacementGcd z w).divisors)
  have hf (v : ↑(shiftedSet z d)) : fromCoset z d v.val ∈ s := by
    have hw := (coset_disk z d hd _).mpr v.prop
    refine Finset.mem_filter.mpr ⟨hw, (member_multiples _ _ _ hw).mpr ⟨?_, ?_⟩⟩
    · exact (coset _ _ _).mpr ⟨v.val.1, rfl⟩
    · exact (coset _ _ _).mpr ⟨v.val.2, rfl⟩
  let f : ↑(shiftedSet z d) → ↑s := fun v => ⟨fromCoset z d v.val, hf v⟩
  change s.card = _
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro a b h
    apply Subtype.ext
    exact fromCoset_injective z d hd (congrArg Subtype.val h)
  · intro w
    have hw := Finset.mem_filter.mp w.prop
    have hdiv := (member_multiples z d w.val hw.1).mp hw.2
    obtain ⟨a, ha⟩ := (coset _ _ _).mp hdiv.1
    obtain ⟨b, hb⟩ := (coset _ _ _).mp hdiv.2
    have he : fromCoset z d (a,b) = w.val := Prod.ext ha.symm hb.symm
    refine ⟨⟨(a,b), (coset_disk z d hd _).mp (he ▸ hw.1)⟩, Subtype.ext he⟩

private theorem multiples_sandwich (z : ℕ × ℕ) (d : ℕ) (hd : 0 < d) :
    ballCount (radius z / d - 2) ≤ multiples z d ∧
      multiples z d ≤ ballCount (radius z / d + 2) := by
  have hshift := shift_bound z d hd
  have hupper : shiftedSet z d ⊆ {v | ‖point v‖ < radius z / d + 2} := by
    intro w hw
    have h : ‖point w + shift z d‖ < radius z / d := hw
    change ‖point w‖ < _
    calc
      ‖point w‖ = ‖(point w + shift z d) - shift z d‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖point w + shift z d‖ + ‖shift z d‖ := norm_sub_le _ _
      _ < _ := add_lt_add_of_lt_of_le h hshift
  have hLower : {v | ‖point v‖ < radius z / d - 2} ⊆ shiftedSet z d := by
    intro w hw
    have hw' : ‖point w‖ < radius z / d - 2 := hw
    change ‖point w + shift z d‖ < _
    exact (norm_add_le _ _).trans_lt (by linarith)
  rw [multiples_eq z d hd, ballCount, ballCount]
  exact ⟨Nat.card_mono ((finite_ball _).subset hupper) hLower, Nat.card_mono (finite_ball _) hupper⟩

private theorem ball_box_bound (r : ℝ) (hr : 0 ≤ r) :
    (ballCount r : ℝ) ≤ (2 * r + 3)^2 := by
  let N : ℤ := ⌈r⌉
  let box := Finset.Icc (-N) N ×ˢ Finset.Icc (-N) N
  have hMem (w : ℤ × ℤ) (hw : ‖point w‖ < r) : w ∈ box := by
    have hc : r ≤ (N : ℝ) := Int.le_ceil r
    have habs (i : Fin 2) : ‖point w i‖ < N := (PiLp.norm_apply_le (point w) i).trans_lt (hw.trans_le hc)
    have h0 := habs 0
    have h1 := habs 1
    change ‖(w.1 : ℝ)‖ < (N : ℝ) at h0
    change ‖(w.2 : ℝ)‖ < (N : ℝ) at h1
    rw [Real.norm_eq_abs, abs_lt] at h0 h1
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by exact_mod_cast h0.1.le, by exact_mod_cast h0.2.le⟩,
      Finset.mem_Icc.mpr ⟨by exact_mod_cast h1.1.le, by exact_mod_cast h1.2.le⟩⟩
  have hb : ballCount r ≤ box.card := by
    rw [ballCount, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective (fun w => ⟨w.val, hMem _ w.prop⟩) ?_
    intro w v h
    exact Subtype.ext (congrArg (fun q : ↑box => q.val) h)
  have hN0 : 0 ≤ (N : ℝ) := hr.trans (Int.le_ceil r)
  have hN' : (N : ℝ) ≤ r + 1 := (Int.ceil_lt_add_one r).le
  have hInt : (Finset.Icc (-N) N).card = (2 * N + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  have hcast : (((2 * N + 1).toNat : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    have hn : 0 ≤ 2 * N + 1 := by exact_mod_cast (by linarith : 0 ≤ 2 * (N : ℝ) + 1)
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
    push_cast
    ring
  have hbR : (ballCount r : ℝ) ≤ ((box.card : ℕ) : ℝ) := by exact_mod_cast hb
  dsimp only [box] at hbR
  rw [Finset.card_product, hInt] at hbR
  push_cast at hbR
  rw [hcast] at hbR
  nlinarith [mul_nonneg (show 0 ≤ 2 * (N : ℝ) + 2 * r + 4 by linarith)
    (show 0 ≤ 2 * (r + 1) - 2 * (N : ℝ) by linarith)]

private theorem scaled_ball_limit (d c : ℝ) (hd : 0 < d) :
    Tendsto (fun r : ℝ => (ballCount (r / d + c) : ℝ) / r ^ 2)
      atTop (𝓝 (Real.pi / d ^ 2)) := by
  have hs : Tendsto (fun r : ℝ => r / d + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c (tendsto_id.atTop_div_const hd)
  have hr : Tendsto (fun r : ℝ => (r / d + c) / r) atTop (𝓝 d⁻¹) := by
    have h : Tendsto (fun r : ℝ => d⁻¹ + c * r⁻¹) atTop (𝓝 (d⁻¹ + c * 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul c)
    simp only [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    field_simp [hr.ne', hd.ne']
  have h := (ball_limit.comp hs).mul (hr.pow 2)
  rw [inv_pow, ← div_eq_mul_inv] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), hs.eventually (eventually_gt_atTop (0 : ℝ))] with r hr hrc
  change (ballCount (r / d + c) : ℝ) / (r / d + c)^2 * (((r / d + c) / r)^2) =
    (ballCount (r / d + c) : ℝ) / r^2
  rw [div_pow, ← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hrc.ne')]

private noncomputable def radii : Filter (ℕ × ℕ) := Filter.comap radius atTop

private theorem radius_tends : Tendsto radius radii atTop := tendsto_comap

private theorem multiples_limit (d : ℕ) (hd : 0 < d) :
    Tendsto (fun z : ℕ × ℕ => (multiples z d : ℝ) / (radius z)^2)
      radii (𝓝 (Real.pi / (d : ℝ)^2)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hL : Tendsto (fun z => (ballCount (radius z / (d : ℝ) - 2) : ℝ) / (radius z)^2)
      radii (𝓝 (Real.pi / (d : ℝ)^2)) := by
    simpa [Function.comp_def, sub_eq_add_neg] using ((scaled_ball_limit (d : ℝ) (-2) hdR).comp radius_tends)
  have hU := (scaled_ball_limit (d : ℝ) 2 hdR).comp radius_tends
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
    (Eventually.of_forall (fun z => ?_)) (Eventually.of_forall (fun z => ?_))
  · exact div_le_div_of_nonneg_right (by exact_mod_cast (multiples_sandwich z d hd).1) (sq_nonneg _)
  · exact div_le_div_of_nonneg_right (by exact_mod_cast (multiples_sandwich z d hd).2) (sq_nonneg _)

private noncomputable def contribution (z : ℕ × ℕ) (d : ℕ) : ℝ :=
  (μ d : ℝ) * (multiples z d : ℝ) / (radius z)^2

private theorem contribution_bound (z : ℕ × ℕ) (d : ℕ) :
    ‖contribution z d‖ ≤ 256 / (d : ℝ)^2 := by
  by_cases hzero : d = 0
  · subst d
    simp [contribution, zero_multiples]
  have hd : 0 < d := Nat.pos_of_ne_zero hzero
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hlarge : 2 * radius z < d
  · rw [contribution, large_multiples_zero z d hlarge]
    simp
    positivity
  have hR : 0 < radius z := by linarith
  have hrd : 1 / 2 ≤ radius z / (d : ℝ) := by
    rw [le_div_iff₀ hdR]
    linarith
  have hb : (multiples z d : ℝ) ≤ 256 * (radius z / (d : ℝ)) ^ 2 := by
    have hs : (multiples z d : ℝ) ≤ ballCount (radius z / d + 2) := by
      exact_mod_cast (multiples_sandwich z d hd).2
    have hu := ball_box_bound (radius z / d + 2) (by positivity)
    have hle : 2 * (radius z / (d : ℝ) + 2) + 3 ≤ 16 * (radius z / (d : ℝ)) := by linarith
    calc
      _ ≤ _ := hs.trans hu
      _ ≤ (16 * (radius z / (d : ℝ)))^2 := by gcongr
      _ = _ := by ring
  have hA : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
  rw [contribution, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (multiples z d : ℝ)),
    abs_of_nonneg (show 0 ≤ (radius z)^2 from sq_nonneg _)]
  apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
  have hB : |(μ d : ℝ)| * (multiples z d : ℝ) ≤ (multiples z d : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hA (show 0 ≤ (multiples z d : ℝ) by positivity)
  exact hB.trans (hb.trans_eq (by rw [div_pow]; ring))

private theorem contribution_sum (z : ℕ × ℕ) :
    ∑' d, contribution z d = (visible z : ℝ) / (radius z)^2 := by
  rw [tsum_eq_sum (s := range (2 * normSq z + 1))]
  · simp only [contribution, ← Finset.sum_div]
    congr 1
    exact_mod_cast (visible_divisor_sum z).symm
  · intro d hd
    have hzero : multiples z d = 0 := by
      unfold multiples
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hw, hm⟩ := Finset.mem_filter.mp hw
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero ((Nat.mem_divisors.mp hm).2)) (Nat.mem_divisors.mp hm).1
      have hb := gcd_bound z w hw
      simp only [Finset.mem_range, not_lt] at hd
      omega
    simp [contribution, hzero]

private theorem visible_limit :
    Tendsto (fun z : ℕ × ℕ => (visible z : ℝ) / (radius z)^2) radii (𝓝 (6 / Real.pi)) := by
  have hbound : Summable (fun d : ℕ => 256 / (d : ℝ)^2) := by
    simpa only [mul_div, mul_one] using ((Real.summable_one_div_nat_pow).mpr (by decide : 1 < 2)).mul_left 256
  have hterm (d : ℕ) :
      Tendsto (contribution · d) radii (𝓝 ((μ d : ℝ) * (Real.pi / (d : ℝ)^2))) := by
    by_cases hzero : d = 0
    · subst d
      simpa [contribution, zero_multiples] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ × ℕ => (0 : ℝ)) radii (𝓝 0))
    · simpa only [contribution, mul_div_assoc] using (multiples_limit d (Nat.pos_of_ne_zero hzero)).const_mul (μ d : ℝ)
  have hSum : HasSum (fun d : ℕ => (μ d : ℝ) * (Real.pi / (d : ℝ)^2)) (6 / Real.pi) := by
    have hs := density_hasSum.mul_left Real.pi
    have he : Real.pi * (6 / Real.pi^2) = 6 / Real.pi := by
      field_simp [Real.pi_ne_zero]
    rw [he] at hs
    exact hs.congr (fun d => by simp [densityTerm, div_eq_mul_inv, mul_left_comm])
  have h := tendsto_tsum_of_dominated_convergence hbound hterm
    (Eventually.of_forall (fun z d => contribution_bound z d))
  rw [hSum.tsum_eq] at h
  exact h.congr (fun z => contribution_sum z)

private def rankSet (z : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (normSq z + 1) ×ˢ Finset.range (normSq z + 1)).filter
    (fun w => 0 < w.1 ∧ w.2 ≤ w.1 ∧
      (normSq w < normSq z ∨ normSq w = normSq z ∧ w.2 ≤ z.2))

private theorem rank_coord (w : ℕ × ℕ) : w.1 ≤ normSq w ∧ w.2 ≤ normSq w := by
  have h1 := Nat.le_self_pow (by decide : 2 ≠ 0) w.1
  have h2 := Nat.le_self_pow (by decide : 2 ≠ 0) w.2
  unfold normSq
  omega

private theorem mem_rank (z w : ℕ × ℕ) :
    w ∈ rankSet z ↔ sector w ∧ (normSq w < normSq z ∨ normSq w = normSq z ∧ w.2 ≤ z.2) := by
  unfold rankSet sector
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, ha, hb, hc⟩
    exact ⟨⟨ha, hb⟩, hc⟩
  · rintro ⟨⟨ha, hb⟩, hc⟩
    have hs : normSq w ≤ normSq z := by rcases hc with h | ⟨h, _⟩ <;> omega
    have h := rank_coord w
    exact ⟨⟨by omega, by omega⟩, ha, hb, hc⟩

private def strictSet (z : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (rankSet z).filter (fun w => 0 < w.2 ∧ w.2 < w.1 ∧ normSq w < normSq z)

private theorem mem_strict (z w : ℕ × ℕ) :
    w ∈ strictSet z ↔ 0 < w.2 ∧ w.2 < w.1 ∧ normSq w < normSq z := by
  rw [strictSet, Finset.mem_filter, mem_rank]
  constructor
  · exact And.right
  · intro h
    exact ⟨⟨⟨by omega, by omega⟩, Or.inl h.2.2⟩, h⟩

private noncomputable def genericSet (z : ℕ × ℕ) : Finset (ℤ × ℤ) :=
  (disk z).filter (fun w => 0 < w.1.natAbs ∧ 0 < w.2.natAbs ∧ w.1.natAbs ≠ w.2.natAbs)

private abbrev Orientation := Bool × Bool × Bool

private def signed (positive : Bool) (u : ℕ) : ℤ :=
  if positive then u else -(u : ℤ)

private theorem abs_signed (positive : Bool) (u : ℕ) : (signed positive u).natAbs = u := by
  cases positive <;> simp [signed]

private theorem sign_signed (positive : Bool) (u : ℕ) (hu : 0 < u) :
    decide (0 < signed positive u) = positive := by
  cases positive <;> simp [signed, hu]

private theorem signed_restore (a : ℤ) (ha : a ≠ 0) :
    signed (decide (0 < a)) a.natAbs = a := by
  unfold signed
  by_cases h : 0 < a
  · simp [h, abs_of_pos]
  · have h' : a < 0 := lt_of_le_of_ne (le_of_not_gt h) ha
    simp [h, abs_of_neg h']

private def arrange (u : ℕ × ℕ) (flags : Orientation) : ℤ × ℤ :=
  if flags.1 then
    (signed flags.2.1 u.2, signed flags.2.2 u.1)
  else
    (signed flags.2.1 u.1, signed flags.2.2 u.2)

private def sortedAbs (w : ℤ × ℤ) : ℕ × ℕ :=
  (max w.1.natAbs w.2.natAbs, min w.1.natAbs w.2.natAbs)

private def orientations (w : ℤ × ℤ) : Orientation :=
  (decide (w.1.natAbs < w.2.natAbs), decide (0 < w.1), decide (0 < w.2))

private theorem sort_arrange (u : ℕ × ℕ) (flags : Orientation) (hu : u.2 < u.1) :
    sortedAbs (arrange u flags) = u := by
  rcases flags with ⟨s, a, b⟩
  cases s <;> simp [arrange, sortedAbs, abs_signed, min_eq_left hu.le, min_eq_right hu.le,
    max_eq_left hu.le, max_eq_right hu.le]

private theorem orientations_arrange (u : ℕ × ℕ) (flags : Orientation)
    (hu : u.2 < u.1) (hp : 0 < u.2) : orientations (arrange u flags) = flags := by
  have hp' : 0 < u.1 := by omega
  rcases flags with ⟨s, a, b⟩
  cases s <;> simp [arrange, orientations, abs_signed, sign_signed, hu, not_lt_of_ge hu.le, hp, hp']

private theorem arrange_restore (w : ℤ × ℤ)
    (h : 0 < w.1.natAbs ∧ 0 < w.2.natAbs ∧ w.1.natAbs ≠ w.2.natAbs) :
    arrange (sortedAbs w) (orientations w) = w := by
  have h1 : w.1 ≠ 0 := Int.natAbs_ne_zero.mp h.1.ne'
  have h2 : w.2 ≠ 0 := Int.natAbs_ne_zero.mp h.2.1.ne'
  by_cases hw : w.1.natAbs < w.2.natAbs
  · simp [arrange, sortedAbs, orientations, hw, min_eq_left hw.le, max_eq_right hw.le,
      signed_restore, h1, h2]
  · have hb : w.2.natAbs ≤ w.1.natAbs := by omega
    simp [arrange, sortedAbs, orientations, hw, min_eq_right hb, max_eq_left hb,
      signed_restore, h1, h2]

private theorem sorted_norm (w : ℤ × ℤ) : (normSq (sortedAbs w) : ℝ) = ‖point w‖^2 := by
  rw [point_normSq]
  by_cases h : w.1.natAbs ≤ w.2.natAbs
  · simp [normSq, sortedAbs, min_eq_left h, max_eq_right h, add_comm]
  · have hh : w.2.natAbs ≤ w.1.natAbs := by omega
    simp [normSq, sortedAbs, min_eq_right hh, max_eq_left hh]

private theorem arrange_generic (z : ℕ × ℕ) (u : ↑(strictSet z)) (flags : Orientation) :
    arrange u.val flags ∈ genericSet z := by
  obtain ⟨hP, hlt, hNorm⟩ := (mem_strict z u.val).mp u.prop
  apply Finset.mem_filter.mpr
  refine ⟨(disk_iff _ _).mpr ?_, ?_⟩
  · have hS := sorted_norm (arrange u.val flags)
    rw [sort_arrange _ _ hlt] at hS
    have hN : (normSq u.val : ℝ) < normSq z := by exact_mod_cast hNorm
    nlinarith [radius_sq z, radius_nonneg z, norm_nonneg (point (arrange u.val flags))]
  · rcases flags with ⟨s,a,b⟩
    cases s <;> simp [arrange, abs_signed] <;> omega

private theorem sort_strict (z : ℕ × ℕ) (w : ↑(genericSet z)) :
    sortedAbs w.val ∈ strictSet z := by
  obtain ⟨hw, h⟩ := Finset.mem_filter.mp w.prop
  have hD := (disk_iff _ _).mp hw
  have hNorm : normSq (sortedAbs w.val) < normSq z := by
    have hh : (normSq (sortedAbs w.val) : ℝ) < normSq z := by
      nlinarith [sorted_norm w.val, radius_sq z, radius_nonneg z, norm_nonneg (point w.val)]
    exact_mod_cast hh
  apply (mem_strict _ _).mpr
  refine ⟨?_, ?_, hNorm⟩
  · exact lt_min h.1 h.2.1
  · unfold sortedAbs
    rcases lt_or_gt_of_ne h.2.2 with ha | ha
    · rw [min_eq_left ha.le, max_eq_right ha.le]; exact ha
    · rw [min_eq_right ha.le, max_eq_left ha.le]; exact ha

private theorem generic_card (z : ℕ × ℕ) : (genericSet z).card = 8 * (strictSet z).card := by
  classical
  let e : ↑(strictSet z) × Orientation ≃ ↑(genericSet z) :=
    { toFun := fun t => ⟨arrange t.1.val t.2, arrange_generic z t.1 t.2⟩
      invFun := fun w => (⟨sortedAbs w.val, sort_strict z w⟩, orientations w.val)
      left_inv := fun ⟨a, f⟩ => by
        have ha := (mem_strict _ _).mp a.prop
        exact Prod.ext (Subtype.ext (sort_arrange _ _ ha.2.1)) (orientations_arrange _ _ ha.2.1 ha.1)
      right_inv := fun w => Subtype.ext (arrange_restore _ (Finset.mem_filter.mp w.prop).2) }
  have h := Fintype.card_congr e
  simpa [Orientation, Fintype.card_prod, Nat.mul_comm] using h.symm

private noncomputable def width (z : ℕ × ℕ) : ℕ := ⌈radius z⌉₊

private def selectCoord {α : Type*} (first : Bool) (w : α × α) : α :=
  if first then w.1 else w.2

private theorem disk_coord (z : ℕ × ℕ) (w : ℤ × ℤ) (hw : w ∈ disk z) (first : Bool) :
    selectCoord first w ∈ Finset.Icc (-(width z : ℤ)) (width z : ℤ) := by
  have hc : radius z ≤ (width z : ℝ) := Nat.le_ceil _
  have hn := (disk_iff z w).mp hw
  have habs (i : Fin 2) : ‖point w i‖ < (width z : ℝ) :=
    (PiLp.norm_apply_le _ _).trans_lt (hn.trans_le hc)
  have h0 := habs 0
  have h1 := habs 1
  change ‖(w.1 : ℝ)‖ < _ at h0
  change ‖(w.2 : ℝ)‖ < _ at h1
  rw [Real.norm_eq_abs, abs_lt] at h0 h1
  apply Finset.mem_Icc.mpr
  cases first
  · change -((width z : ℕ) : ℤ) ≤ w.2 ∧ w.2 ≤ (width z : ℤ)
    exact ⟨by exact_mod_cast h1.1.le, by exact_mod_cast h1.2.le⟩
  · change -((width z : ℕ) : ℤ) ≤ w.1 ∧ w.1 ≤ (width z : ℤ)
    exact ⟨by exact_mod_cast h0.1.le, by exact_mod_cast h0.2.le⟩

private theorem disk_line (z : ℕ × ℕ) (s : Finset (ℤ × ℤ)) (hs : s ⊆ disk z) (first : Bool)
    (hi : Set.InjOn (selectCoord first) (↑s : Set (ℤ × ℤ))) : s.card ≤ 2 * width z + 1 := by
  have hcard : (Finset.Icc (-(width z : ℤ)) (width z : ℤ)).card = 2 * width z + 1 := by
    rw [Int.card_Icc]
    omega
  rw [← hcard]
  exact Finset.card_le_card_of_injOn (selectCoord first) (fun w hw => disk_coord z w (hs hw) first) hi

private theorem disk_boundary (z : ℕ × ℕ) :
    ((disk z) \ genericSet z).card ≤ 4 * (2 * width z + 1) := by
  let s1 := (disk z).filter (fun w => w.2 = 0)
  let s2 := (disk z).filter (fun w => w.1 = 0)
  let s3 := (disk z).filter (fun w => w.1 = w.2)
  let s4 := (disk z).filter (fun w => w.1 = -w.2)
  have h1 : s1.card ≤ 2 * width z + 1 := by
    apply disk_line z s1 (Finset.filter_subset _ _) true
    intro a ha b hb h
    exact Prod.ext h ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have h2 : s2.card ≤ 2 * width z + 1 := by
    apply disk_line z s2 (Finset.filter_subset _ _) false
    intro a ha b hb h
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) h
  have h3 : s3.card ≤ 2 * width z + 1 := by
    apply disk_line z s3 (Finset.filter_subset _ _) true
    intro a ha b hb h
    exact Prod.ext h ((Finset.mem_filter.mp ha).2.symm.trans (h.trans (Finset.mem_filter.mp hb).2))
  have h4 : s4.card ≤ 2 * width z + 1 := by
    apply disk_line z s4 (Finset.filter_subset _ _) false
    intro a ha b hb h
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans ((congrArg Neg.neg h).trans (Finset.mem_filter.mp hb).2.symm)) h
  have hs : (disk z) \ genericSet z ⊆ ((s1 ∪ s2) ∪ s3) ∪ s4 := by
    intro w hw
    obtain ⟨hd, hg⟩ := Finset.mem_sdiff.mp hw
    simp only [s1, s2, s3, s4, Finset.mem_union, Finset.mem_filter, hd, true_and]
    by_cases a : w.1 = 0
    · exact Or.inl (Or.inl (Or.inr a))
    by_cases b : w.2 = 0
    · exact Or.inl (Or.inl (Or.inl b))
    have hEq : w.1.natAbs = w.2.natAbs := by
      by_contra hNe
      exact hg (Finset.mem_filter.mpr ⟨hd, Int.natAbs_pos.mpr a, Int.natAbs_pos.mpr b, hNe⟩)
    rcases Int.natAbs_eq_natAbs_iff.mp hEq with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hsub := Finset.card_le_card hs
  have h12 := Finset.card_union_le s1 s2
  have h123 := Finset.card_union_le (s1 ∪ s2) s3
  have h1234 := Finset.card_union_le ((s1 ∪ s2) ∪ s3) s4
  omega

private theorem rank_coord_width (z w : ℕ × ℕ) (hw : w ∈ rankSet z) (first : Bool) :
    selectCoord first w ∈ Finset.range (width z + 1) := by
  have h := (mem_rank z w).mp hw
  have hNs : normSq w ≤ normSq z := by rcases h.2 with hs | ⟨hs, _⟩ <;> omega
  have hRs : radius w ≤ radius z := Real.sqrt_le_sqrt (by exact_mod_cast hNs)
  have hc (i : Fin 2) : ‖point ((w.1 : ℤ), (w.2 : ℤ)) i‖ ≤ (width z : ℝ) := by
    refine (PiLp.norm_apply_le _ _).trans ?_
    rw [norm_observer]
    exact hRs.trans (Nat.le_ceil _)
  have h0 := hc 0
  have h1 := hc 1
  change ‖((w.1 : ℤ) : ℝ)‖ ≤ _ at h0
  change ‖((w.2 : ℤ) : ℝ)‖ ≤ _ at h1
  simp only [Int.cast_natCast, Real.norm_eq_abs] at h0 h1
  rw [abs_of_nonneg (Nat.cast_nonneg w.1)] at h0
  rw [abs_of_nonneg (Nat.cast_nonneg w.2)] at h1
  cases first
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by exact_mod_cast h1))
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by exact_mod_cast h0))

private theorem rank_line (z : ℕ × ℕ) (s : Finset (ℕ × ℕ)) (hs : s ⊆ rankSet z) (first : Bool)
    (hi : Set.InjOn (selectCoord first) (↑s : Set (ℕ × ℕ))) : s.card ≤ width z + 1 := by
  rw [← Finset.card_range (width z + 1)]
  exact Finset.card_le_card_of_injOn (selectCoord first) (fun w hw => rank_coord_width z w (hs hw) first) hi

private theorem rank_boundary (z : ℕ × ℕ) :
    ((rankSet z) \ strictSet z).card ≤ 3 * (width z + 1) := by
  let s1 := (rankSet z).filter (fun w => w.2 = 0)
  let s2 := (rankSet z).filter (fun w => w.2 = w.1)
  let s3 := (rankSet z).filter (fun w => normSq w = normSq z)
  have h1 : s1.card ≤ width z + 1 := by
    apply rank_line z s1 (Finset.filter_subset _ _) true
    intro a ha b hb h
    exact Prod.ext h ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have h2 : s2.card ≤ width z + 1 := by
    apply rank_line z s2 (Finset.filter_subset _ _) true
    intro a ha b hb h
    exact Prod.ext h ((Finset.mem_filter.mp ha).2.trans (h.trans (Finset.mem_filter.mp hb).2.symm))
  have h3 : s3.card ≤ width z + 1 := by
    apply rank_line z s3 (Finset.filter_subset _ _) false
    intro a ha b hb h
    change a.2 = b.2 at h
    have he := (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    unfold normSq at he
    rw [h] at he
    exact Prod.ext (Nat.pow_left_injective (by decide : 2 ≠ 0) (Nat.add_right_cancel he)) h
  have hs : (rankSet z) \ strictSet z ⊆ (s1 ∪ s2) ∪ s3 := by
    intro w hw
    obtain ⟨hr, hp⟩ := Finset.mem_sdiff.mp hw
    have h := (mem_rank z w).mp hr
    have hn := h.2
    have hs := h.1.2
    simp only [s1, s2, s3, Finset.mem_union, Finset.mem_filter, hr, true_and]
    by_contra hneg
    apply hp
    apply (mem_strict z w).mpr
    rcases hn with hn | ⟨hn, _⟩ <;> grind
  have hsub := Finset.card_le_card hs
  have h12 := Finset.card_union_le s1 s2
  have h123 := Finset.card_union_le (s1 ∪ s2) s3
  omega

private theorem ball_count_disk (z : ℕ × ℕ) : ballCount (radius z) = (disk z).card := by
  unfold ballCount
  let e : {w : ℤ × ℤ // ‖point w‖ < radius z} ≃ ↑(disk z) :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun w => (disk_iff z w).symm)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

private theorem rank_error (z : ℕ × ℕ) :
    |8 * (rank z : ℝ) - (ballCount (radius z) : ℝ)| ≤ 24 * (radius z + 2) := by
  have hR := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _ : strictSet z ⊆ rankSet z)
  have hD := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _ : genericSet z ⊆ disk z)
  have hbR := rank_boundary z
  have hbD := disk_boundary z
  change ((disk z) \ genericSet z).card + (genericSet z).card = (disk z).card at hD
  rw [generic_card, ← ball_count_disk] at hD
  change ((rankSet z) \ strictSet z).card + (strictSet z).card = rank z at hR
  have h1 : 8 * rank z ≤ ballCount (radius z) + 24 * (width z + 1) := by omega
  have h2 : ballCount (radius z) ≤ 8 * rank z + 24 * (width z + 1) := by omega
  have he : (width z : ℝ) ≤ radius z + 1 := (Nat.ceil_lt_add_one (radius_nonneg z)).le
  apply abs_le.mpr
  constructor <;> first
    | have hn : (ballCount (radius z) : ℝ) ≤ 8 * (rank z : ℝ) + 24 * ((width z : ℝ) + 1) := by exact_mod_cast h2
      linarith
    | have hn : 8 * (rank z : ℝ) ≤ (ballCount (radius z) : ℝ) + 24 * ((width z : ℝ) + 1) := by exact_mod_cast h1
      linarith

private theorem error_bound_limit :
    Tendsto (fun z : ℕ × ℕ => (24 * (radius z + 2)) / (radius z)^2) radii (𝓝 0) := by
  have hI := tendsto_inv_atTop_zero.comp radius_tends
  have h := (hI.add ((hI.pow 2).const_mul (2 : ℝ))).const_mul (24 : ℝ)
  norm_num at h
  refine h.congr' ?_
  filter_upwards [radius_tends.eventually (eventually_gt_atTop (0 : ℝ))] with z hz
  change 24 * ((radius z)⁻¹ + 2 * ((radius z)^2)⁻¹) = _
  field_simp [hz.ne']

private theorem rank_limit :
    Tendsto (fun z : ℕ × ℕ => (rank z : ℝ) / (radius z)^2) radii (𝓝 (Real.pi / 8)) := by
  have hNeg := error_bound_limit.neg
  simp only [neg_zero] at hNeg
  have hE : Tendsto (fun z : ℕ × ℕ => (8 * (rank z : ℝ) - ballCount (radius z)) / (radius z)^2)
      radii (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hNeg error_bound_limit
      (Eventually.of_forall (fun z => ?_)) (Eventually.of_forall (fun z => ?_))
    · rw [← neg_div]
      exact div_le_div_of_nonneg_right (abs_le.mp (rank_error z)).1 (sq_nonneg _)
    · exact div_le_div_of_nonneg_right (abs_le.mp (rank_error z)).2 (sq_nonneg _)
  have h := ((ball_limit.comp radius_tends).add hE).div_const (8 : ℝ)
  rw [add_zero] at h
  refine h.congr (fun z => ?_)
  change ((ballCount (radius z) : ℝ) / (radius z)^2 +
    (8 * (rank z : ℝ) - ballCount (radius z)) / (radius z)^2) / 8 = _
  ring

private theorem ratio_limit :
    Tendsto (fun z : ℕ × ℕ => (visible z : ℝ) / (48 * (rank z : ℝ) / Real.pi^2)) radii (𝓝 1) := by
  have hh := (rank_limit.const_mul (48 : ℝ)).div_const (Real.pi^2)
  have he : 48 * (Real.pi / 8) / Real.pi^2 = 6 / Real.pi := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [he] at hh
  have hne : ((6 : ℝ) / Real.pi) ≠ 0 := div_ne_zero (by norm_num) Real.pi_ne_zero
  have h := visible_limit.div hh hne
  rw [div_self hne] at h
  refine h.congr' ?_
  filter_upwards [radius_tends.eventually (eventually_gt_atTop (0 : ℝ))] with z hz
  change ((visible z : ℝ) / (radius z)^2) / (48 * ((rank z : ℝ) / (radius z)^2) / Real.pi^2) = _
  rw [show 48 * ((rank z : ℝ) / (radius z)^2) / Real.pi^2 =
      (48 * (rank z : ℝ) / Real.pi^2) / (radius z)^2 by ring]
  exact div_div_div_cancel_right₀ (pow_ne_zero _ hz.ne') _ _

private theorem rank_box (z : ℕ × ℕ) : rank z ≤ (normSq z + 1)^2 := by
  have h := Finset.card_filter_le (Finset.range (normSq z + 1) ×ˢ Finset.range (normSq z + 1))
    (fun w : ℕ × ℕ => 0 < w.1 ∧ w.2 ≤ w.1 ∧
      (normSq w < normSq z ∨ normSq w = normSq z ∧ w.2 ≤ z.2))
  simpa [rank, pow_two] using h

end OMA.S_oeis_a401897.Proof

open OMA.S_oeis_a401897.Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a401897.main := by
  intro ε hε
  have h := Metric.tendsto_nhds.mp ratio_limit ε hε
  change (∀ᶠ z in Filter.comap radius atTop,
    dist ((visible z : ℝ) / (48 * (rank z : ℝ) / Real.pi^2)) 1 < ε) at h
  rw [Filter.eventually_comap] at h
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp h
  let N : ℕ := (⌈R⌉₊ ^ 2 + 1)^2 + 1
  refine ⟨N, ?_⟩
  intro z _ hz
  have hRad : R ≤ radius z := by
    by_contra! hLt
    have hh : radius z ≤ (⌈R⌉₊ : ℝ) := hLt.le.trans (Nat.le_ceil _)
    have hqR : (normSq z : ℝ) ≤ (⌈R⌉₊ : ℝ)^2 := by
      rw [← radius_sq]
      gcongr
      exact radius_nonneg z
    have hq : normSq z ≤ ⌈R⌉₊ ^ 2 := by exact_mod_cast hqR
    have hB : rank z ≤ (⌈R⌉₊ ^ 2 + 1)^2 := (rank_box z).trans (Nat.pow_le_pow_left (Nat.succ_le_succ hq) 2)
    exact (Nat.not_succ_le_self _) (hz.trans hB)
  simpa [Real.dist_eq] using hR (radius z) hRad z rfl
