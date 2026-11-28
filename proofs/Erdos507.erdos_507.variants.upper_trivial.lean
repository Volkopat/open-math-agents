import FormalConjectures.ErdosProblems.«507»

/-! The strip pigeonhole argument uses the three horizontal differences in
 the area determinant. Each multiplies an original vertical coordinate. -/

open Asymptotics Filter
open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos507.erdos_507.variants.upper_trivial := by
  classical
  apply IsBigO.of_bound 12
  filter_upwards [eventually_ge_atTop (7 : ℕ)] with n hn
  have hnonneg : 0 ≤ Erdos507.α n :=
    Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ Real.sInf_nonneg fun _ ⟨_, _, _, h'⟩ => h' ▸ abs_nonneg _
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (by positivity)]
  refine Real.sSup_le ?_ (by positivity)
  rintro _ ⟨S, ⟨hS, hball, _⟩, rfl⟩
  have hcoord (p) (hp : p ∈ S) (i : Fin 2) : |p i| ≤ 1 :=
    (Real.norm_eq_abs (p i) ▸ PiLp.norm_apply_le p i).trans
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hball hp)
  let k := (n - 3) / 2
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let sc (p : ℝ²) : ℝ := (p 0 + 1) * k / 2
  have hsc {p} (hp : p ∈ S) : 0 ≤ sc p ∧ sc p ≤ k := by
    have := abs_le.mp (hcoord p hp 0)
    dsimp [sc]; constructor <;> nlinarith
  obtain ⟨j, _, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (n := 2)
    (t := Finset.range (k + 1)) (fun p hp => Finset.mem_range.mpr
      ((Nat.floor_lt (hsc hp).1).mpr (by push_cast; linarith [(hsc hp).2])))
    (by rw [Finset.card_range, hS]; omega)
  obtain ⟨p, hp⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (s := S.filter (⌊sc ·⌋₊ = j)) (by simpa using Nat.succ_le_of_lt hj)
  have hpF (i : Fin 3) := Finset.mem_filter.mp (hp (Set.mem_range_self i))
  have hst (i : Fin 3) := (Nat.floor_eq_iff (hsc (hpF i).1).1).mp (hpF i).2
  have hx (i j : Fin 3) : |p i 0 - p j 0| ≤ 2 / k := by
    have a := hst i; have b := hst j
    rw [abs_le, ← neg_div, div_le_iff₀ hk, le_div_iff₀ hk]
    dsimp [sc] at a b
    constructor <;> linarith
  have hmin : Erdos507.minTriangleArea S ≤ |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| :=
    csInf_le ⟨0, by rintro _ ⟨_, _, _, rfl⟩; exact abs_nonneg _⟩ ⟨p, p.injective, fun i => (hpF i).1, rfl⟩
  refine hmin.trans ?_
  rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
  have h (i j l : Fin 3) : |(p i 0 - p j 0) * p l 1| ≤ 2 / k := by
    simpa [abs_mul] using mul_le_mul (hx i j) (hcoord _ (hpF l).1 1) (abs_nonneg _) (by positivity)
  calc
    _ = |(p 0 0 - p 2 0) * p 1 1 + (p 1 0 - p 0 0) * p 2 1 +
        (p 2 0 - p 1 0) * p 0 1| / 2 := by rw [abs_div, abs_two]; congr 2; simp; ring
    _ ≤ (2 / k + 2 / k + 2 / k) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (h 0 2 1) (h 1 0 2))) (h 2 1 0))
    _ = 3 / k := by ring
    _ ≤ _ := by
      rw [mul_one_div, div_le_div_iff₀ hk (by exact_mod_cast (show 0 < n by omega))]
      exact_mod_cast (show 3 * n ≤ 12 * k by omega)
