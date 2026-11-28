import OMAReductions.R_Green85_green_85_R1
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.Thickening

/-!
Shortening of @amp2600's merged proof #28269, head
61bd5c7cfc44bf33b6e19dafd6f5b4b070106573. The compact-grid construction
is retained; interval-distance and reciprocal-order APIs replace manual bounds.

A compact subset of an open set lies there with a uniform neighborhood.
Cover the compact subset by the grid cells meeting it, then use finite
subadditivity and the area of an individual grid cell.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

private def gridCell (N : ℕ) (p : ℕ × ℕ) : Set (ℝ × ℝ) :=
  Icc ((p.1 : ℝ) / N) (((p.1 : ℝ) + 1) / N) ×ˢ
    Icc ((p.2 : ℝ) / N) (((p.2 : ℝ) + 1) / N)

private theorem grid_coordinate {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ i ∈ Finset.range N, t ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      norm_num
    refine ⟨N - 1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [heq]
    exact ⟨(div_le_iff₀ hNr).mpr (by rw [hcast]; linarith),
      (le_div_iff₀ hNr).mpr (by rw [hcast]; linarith)⟩
  · let i := ⌊t * (N : ℝ)⌋₊
    have hlo : (i : ℝ) ≤ t * N := Nat.floor_le (mul_nonneg ht.1 hNr.le)
    have hhi : t * N < (i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hiReal : (i : ℝ) < (N : ℝ) :=
      hlo.trans_lt (by simpa only [one_mul] using mul_lt_mul_of_pos_right hlt hNr)
    have hi : i < N := Nat.cast_lt.mp hiReal
    exact ⟨i, Finset.mem_range.mpr hi, (div_le_iff₀ hNr).mpr hlo,
      (le_div_iff₀ hNr).mpr hhi.le⟩

private theorem grid_coordinate_dist (N i : ℕ) {x y : ℝ}
    (hx : x ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N))
    (hy : y ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) :
    dist x y ≤ 1 / (N : ℝ) := by
  simpa [add_div] using Real.dist_le_of_mem_Icc hx hy

private theorem gridCell_volume {N : ℕ} (hN : 0 < N) (p : ℕ × ℕ) :
    volume (gridCell N p) = ENNReal.ofReal (1 / (N : ℝ) ^ 2) := by
  simp only [gridCell, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod,
    Real.volume_Icc, add_div, add_sub_cancel_left]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / N)]
  congr 1
  rw [← pow_two, div_pow, one_pow]

theorem OMA.solution : OMA.R_Green85_green_85_R1.H2 := by
  classical
  intro A hA hsub r hr hrt
  have compactBox : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have finiteA : volume A ≠ ∞ :=
    ne_top_of_le_ne_top compactBox.measure_ne_top (measure_mono hsub)
  have hrA : ENNReal.ofReal r < volume A :=
    (ENNReal.ofReal_lt_iff_lt_toReal hr finiteA).mpr hrt
  obtain ⟨K, hKA, hK, hrK⟩ :=
    hA.measurableSet.exists_lt_isCompact_of_ne_top finiteA hrA
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_cthickening_subset_open hA hKA
  obtain ⟨N, hδN⟩ := exists_nat_gt (1 / δ)
  have hNr : (0 : ℝ) < N := (one_div_pos.mpr hδ).trans hδN
  have hN : 0 < N := Nat.cast_pos.mp hNr
  have hside : 1 / (N : ℝ) ≤ δ := ((one_div_lt hNr hδ).2 hδN).le
  let S := (Finset.range N ×ˢ Finset.range N).filter (fun p => gridCell N p ⊆ A)
  have covered : K ⊆ ⋃ p ∈ S, gridCell N p := by
    intro x hx
    have hbox := hsub (hKA hx)
    obtain ⟨i, hi, hxi⟩ := grid_coordinate hN hbox.1
    obtain ⟨j, hj, hxj⟩ := grid_coordinate hN hbox.2
    have good : gridCell N (i,j) ⊆ A := by
      intro y hy
      have hydist : dist y x ≤ 1 / (N : ℝ) := by
        rw [Prod.dist_eq]
        exact max_le (grid_coordinate_dist N i hy.1 hxi)
          (grid_coordinate_dist N j hy.2 hxj)
      exact hthick (Metric.mem_cthickening_of_dist_le y x δ K hx (hydist.trans hside))
    have hp : (i,j) ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, good⟩
    exact mem_iUnion.mpr ⟨(i,j), mem_iUnion.mpr ⟨hp, hxi, hxj⟩⟩
  have volumeBound : volume K ≤ ENNReal.ofReal ((S.card : ℝ) / (N : ℝ) ^ 2) := by
    calc
      volume K ≤ volume (⋃ p ∈ S, gridCell N p) := measure_mono covered
      _ ≤ ∑ p ∈ S, volume (gridCell N p) := measure_biUnion_finset_le _ _
      _ = ∑ _p ∈ S, ENNReal.ofReal (1 / (N : ℝ) ^ 2) := by
        exact Finset.sum_congr rfl (fun p _ => gridCell_volume hN p)
      _ = ENNReal.ofReal ((S.card : ℝ) / (N : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        congr 1
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  refine ⟨N, hN, S, Finset.filter_subset _ _, ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      (hrK.le.trans volumeBound)
