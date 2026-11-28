import OMAStatements.S_mo_104224
import Mathlib

open Set Topology

namespace OMA.CircleSquare

open OMA.S_mo_104224

private theorem neg_square (u : Circle) : (-u) ^ 2 = u ^ 2 := by
  apply Circle.ext
  simp only [Circle.coe_pow, neg_sq]

private theorem root_exists (x : Circle) : ∃ u : Circle, u ^ 2 = x := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective x
  refine ⟨Circle.exp (t / 2), ?_⟩
  rw [pow_two, ← Circle.exp_add, show t / 2 + t / 2 = t by ring]

private theorem sq_eq_pair (u v : Circle) : v ^ 2 = u ^ 2 ↔ v = u ∨ v = -u := by
  constructor
  · intro h
    have hc : (v : ℂ) ^ 2 = (u : ℂ) ^ 2 := by
      simpa only [Circle.coe_pow] using congrArg (fun z : Circle => (z : ℂ)) h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with hv | hv
    · exact Or.inl (Circle.ext hv)
    · exact Or.inr (Circle.ext (by simpa only [Circle.coe_neg] using hv))
  · rintro (rfl | rfl)
    · rfl
    · exact neg_square u

private theorem fiber_pair (x : Circle) :
    ∃ u : Circle, roots x = {u, -u} ∧ u ≠ -u := by
  obtain ⟨u, hu⟩ := root_exists x
  refine ⟨u, ?_, (Circle.neg_ne_self u).symm⟩
  ext v
  simpa only [roots, Set.mem_ofPred_eq, ← hu, Set.mem_insert_iff, Set.mem_singleton_iff] using
    sq_eq_pair u v

private theorem chord_bound (u v : Circle) :
    dist u v ≤ dist (u ^ 2) (v ^ 2) / Real.sqrt 2 ∨
      dist u (-v) ≤ dist (u ^ 2) (v ^ 2) / Real.sqrt 2 := by
  let a := ‖(u : ℂ) - (v : ℂ)‖
  let b := ‖(u : ℂ) + (v : ℂ)‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hab : b ^ 2 + a ^ 2 = 4 := by
    have h := parallelogram_law_with_norm ℂ (u : ℂ) (v : ℂ)
    rw [Circle.norm_coe, Circle.norm_coe] at h
    convert h using 1 <;> norm_num
  have hd (p q : Circle) : dist p q = ‖(p : ℂ) - (q : ℂ)‖ := by
    change dist (p : ℂ) (q : ℂ) = _
    exact dist_eq_norm _ _
  have hprod : dist (u ^ 2) (v ^ 2) = a * b := by
    rw [hd, Circle.coe_pow, Circle.coe_pow,
      show (u : ℂ)^2 - (v : ℂ)^2 = ((u : ℂ) - v) * ((u : ℂ) + v) by ring, norm_mul]
  rw [hprod, hd u v, hd u (-v), Circle.coe_neg, sub_neg_eq_add]
  change a ≤ a * b / Real.sqrt 2 ∨ b ≤ a * b / Real.sqrt 2
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rcases le_total a b with h | h
  · left
    have hb' : Real.sqrt 2 ≤ b := (Real.sqrt_le_left hb).2 (by
      have := (sq_le_sq₀ ha hb).2 h
      linarith)
    exact (le_div_iff₀ hs).2 (mul_le_mul_of_nonneg_left hb' ha)
  · right
    have ha' : Real.sqrt 2 ≤ a := (Real.sqrt_le_left ha).2 (by
      have := (sq_le_sq₀ hb ha).2 h
      linarith)
    apply (le_div_iff₀ hs).2
    calc
      b * Real.sqrt 2 ≤ b * a := mul_le_mul_of_nonneg_left ha' hb
      _ = a * b := mul_comm b a

private theorem directed (x y : Circle) (u : Circle) (hu : u ∈ roots x) :
    ∃ v ∈ roots y, dist u v ≤ dist x y / Real.sqrt 2 := by
  obtain ⟨v, hv⟩ := root_exists y
  change u ^ 2 = x at hu
  have h := chord_bound u v
  rw [hu, hv] at h
  rcases h with h | h
  · exact ⟨v, hv, h⟩
  · exact ⟨-v, (neg_square v).trans hv, h⟩

private theorem upper : UpperHemicontinuous roots := by
  have hs : Continuous (fun u : Circle => u ^ 2) := continuous_id.pow 2
  exact isClosedMap_iff_upperHemicontinuous.mp hs.isClosedMap

private theorem lower : LowerHemicontinuous roots := by
  rw [lowerHemicontinuous_iff_isOpen_inter_nonempty]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨u, hux, huU⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds huU)
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε, hε, ?_⟩
  intro y hy
  obtain ⟨v, hv, hd⟩ := directed x y u hux
  have hxy : dist x y < ε := by simpa only [Metric.mem_ball, dist_comm y x] using hy
  have hweak : dist x y / Real.sqrt 2 ≤ dist x y :=
    div_le_self dist_nonneg Real.one_lt_sqrt_two.le
  refine ⟨v, hv, hball ?_⟩
  rw [Metric.mem_ball, dist_comm v u]
  exact (hd.trans hweak).trans_lt hxy

private theorem hausdorff (x y : Circle) :
    Metric.hausdorffDist (roots x) (roots y) ≤ dist x y / Real.sqrt 2 := by
  refine Metric.hausdorffDist_le_of_mem_dist (by positivity) (directed x y) ?_
  simpa only [dist_comm y x] using directed y x

private theorem no_section :
    ¬ ∃ g : Circle → Circle, Continuous g ∧ ∀ x, g x ∈ roots x := by
  rintro ⟨g, hg, hselect⟩
  let f : Circle → Circle := fun u => g (u ^ 2) / u
  have hf : Continuous f := (hg.comp (continuous_id.pow 2)).div' continuous_id
  have hsign (u : Circle) : f u ∈ ({1, -1} : Set Circle) := by
    have hs : (g (u ^ 2)) ^ 2 = u ^ 2 := hselect (u ^ 2)
    have hf2 : (f u) ^ 2 = 1 := by
      dsimp only [f]
      rw [div_pow, hs, div_self']
    have hz : (f u : ℂ) ^ 2 = 1 := by
      simpa only [Circle.coe_pow, Circle.coe_one] using
        congrArg (fun z : Circle => (z : ℂ)) hf2
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases sq_eq_one_iff.mp hz with h | h
    · exact Or.inl (Circle.ext h)
    · exact Or.inr (Circle.ext (by simpa only [Circle.coe_one, Circle.coe_neg] using h))
  have hfinite : (Set.range f).Finite := ((Set.finite_singleton (-(1 : Circle))).insert 1).subset (by
    rintro _ ⟨u, rfl⟩
    exact hsign u)
  have heq : f (-(1 : Circle)) = f 1 := by
    by_contra hne
    exact (isPreconnected_range hf).infinite_of_nontrivial
      ⟨_, ⟨-(1 : Circle), rfl⟩, _, ⟨1, rfl⟩, hne⟩ hfinite
  have hopp (u : Circle) : f (-u) = -f u := by
    apply Circle.ext
    simp only [f, neg_square, Circle.coe_div, Circle.coe_neg, div_neg]
  exact Circle.neg_ne_self (f 1) ((hopp 1).symm.trans heq)

end OMA.CircleSquare

theorem OMA.solution : type_of% @OMA.S_mo_104224.main :=
  ⟨OMA.CircleSquare.fiber_pair, OMA.CircleSquare.upper, OMA.CircleSquare.lower,
    OMA.CircleSquare.hausdorff, OMA.CircleSquare.no_section⟩