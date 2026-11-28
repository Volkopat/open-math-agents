import OMAStatements.S_mo_165168

/-!
Disproof of the 3-dimensional Japanese theorem question (MO 165168)
using the 5-vertex integer triangular bipyramid on the sphere of radius 5:
  A = (5, 0, 0), B = (-3, 4, 0), C = (-3, -4, 0), N = (0, 0, 5), S = (0, 0, -5).
Splitting across the equator gives 2 tetrahedra (inradius sum < 28 / 9), while
splitting around the polar axis gives 3 tetrahedra (inradius sum > 158 / 49 > 28 / 9).
-/

open scoped BigOperators RealInnerProductSpace Classical
open Affine EuclideanGeometry OMA.S_mo_165168

namespace Mo165168Disproof

noncomputable def mkPt (x y z : ℝ) : Point := WithLp.toLp 2 ![x, y, z]

@[simp] lemma mkPt_0 (x y z : ℝ) : mkPt x y z 0 = x := rfl
@[simp] lemma mkPt_1 (x y z : ℝ) : mkPt x y z 1 = y := rfl
@[simp] lemma mkPt_2 (x y z : ℝ) : mkPt x y z 2 = z := rfl
@[simp] lemma pt_add (u v : Point) (i : Fin 3) : (u + v) i = u i + v i := rfl
@[simp] lemma pt_smul (c : ℝ) (u : Point) (i : Fin 3) : (c • u) i = c * u i := rfl
@[simp] lemma pt_sub (u v : Point) (i : Fin 3) : (u - v) i = u i - v i := rfl

lemma inner_eq (u v : Point) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma norm_sq_eq (u : Point) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq]
  ring

lemma dist_sq_eq (u v : Point) :
    dist u v ^ 2 = (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 + (u 2 - v 2) ^ 2 := by
  simp [dist_eq_norm, norm_sq_eq]

noncomputable def pA : Point := mkPt 5 0 0
noncomputable def pB : Point := mkPt (-3) 4 0
noncomputable def pC : Point := mkPt (-3) (-4) 0
noncomputable def pN : Point := mkPt 0 0 5
noncomputable def pS : Point := mkPt 0 0 (-5)

noncomputable def verts : Finset Point := {pA, pB, pC, pN, pS}

lemma coords_ne {u v : Point} (h : u 0 ≠ v 0 ∨ u 1 ≠ v 1 ∨ u 2 ≠ v 2) : u ≠ v := by
  rintro rfl; rcases h with h | h | h <;> exact h rfl

lemma p_ne_AB : pA ≠ pB := coords_ne (by norm_num [pA, pB])
lemma p_ne_AC : pA ≠ pC := coords_ne (by norm_num [pA, pC])
lemma p_ne_AN : pA ≠ pN := coords_ne (by norm_num [pA, pN])
lemma p_ne_AS : pA ≠ pS := coords_ne (by norm_num [pA, pS])
lemma p_ne_BC : pB ≠ pC := coords_ne (by norm_num [pB, pC])
lemma p_ne_BN : pB ≠ pN := coords_ne (by norm_num [pB, pN])
lemma p_ne_BS : pB ≠ pS := coords_ne (by norm_num [pB, pS])
lemma p_ne_CN : pC ≠ pN := coords_ne (by norm_num [pC, pN])
lemma p_ne_CS : pC ≠ pS := coords_ne (by norm_num [pC, pS])
lemma p_ne_NS : pN ≠ pS := coords_ne (by norm_num [pN, pS])

lemma sphere_cond :
    ∃ (center : Point) (radius : ℝ), (verts : Set Point) ⊆ Metric.sphere center radius := by
  refine ⟨0, 5, fun x hx => ?_⟩
  rw [Metric.mem_sphere, dist_zero_right]
  have hsq : ‖x‖ ^ 2 = 5 ^ 2 := by
    simp only [verts, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      · rw [norm_sq_eq]; simp [pA, pB, pC, pN, pS]; try norm_num
  nlinarith [norm_nonneg x]

lemma mem_convexHull_range_iff {k : ℕ} (f : Fin k → Point) {x : Point} :
    x ∈ convexHull ℝ (Set.range f) ↔
      ∃ w : Fin k → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x := by
  constructor
  · intro hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    rcases hx with ⟨s, w, hw0, hw1, hfx⟩
    let w' : Fin k → ℝ := fun i => if i ∈ s then w i else 0
    refine ⟨w', fun i => by by_cases hi : i ∈ s <;> simp [w', hi]; exact hw0 i hi, ?_, ?_⟩
    · have hs : ∑ i : Fin k, w' i = ∑ i ∈ s, w i := by
        simp [w', Finset.sum_ite_mem, Finset.univ_inter]
      rw [hs, hw1]
    · have hs : ∑ i : Fin k, w' i • f i = ∑ i ∈ s, w i • f i := by
        simp [w', Finset.sum_ite_mem, Finset.univ_inter]
      rw [hs, ← Finset.affineCombination_eq_linear_combination s f w hw1, hfx]
  · rintro ⟨w, hw0, hw1, hx⟩
    exact mem_convexHull_of_exists_fintype w f hw0 hw1 (fun i => ⟨i, rfl⟩) hx

lemma interior_nonempty : (interior (convexHull ℝ (verts : Set Point))).Nonempty := by
  refine ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨1 / 2, by norm_num, fun x hx => ?_⟩)⟩
  rw [Metric.mem_ball, dist_zero_right] at hx
  have h0 : |x 0| < 1 / 2 := (PiLp.norm_apply_le x 0).trans_lt hx
  have h1 : |x 1| < 1 / 2 := (PiLp.norm_apply_le x 1).trans_lt hx
  have h2 : |x 2| < 1 / 2 := (PiLp.norm_apply_le x 2).trans_lt hx
  rcases abs_lt.mp h0 with ⟨_, _⟩
  rcases abs_lt.mp h1 with ⟨_, _⟩
  rcases abs_lt.mp h2 with ⟨_, _⟩
  let pts : Fin 5 → Point := ![pA, pB, pC, pN, pS]
  let w : Fin 5 → ℝ := ![3 / 10 + x 0 / 8, 1 / 4 - x 0 / 16 + x 1 / 8,
    1 / 4 - x 0 / 16 - x 1 / 8, 1 / 10 + x 2 / 10, 1 / 10 - x 2 / 10]
  refine convexHull_mono (s := Set.range pts) ?_ ?_
  · rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [pts, verts]
  · rw [mem_convexHull_range_iff]
    refine ⟨w, fun i => ?_, ?_, ?_⟩
    · fin_cases i <;> simp [w] <;> linarith
    · rw [Fin.sum_univ_five]; simp [w]; ring
    · rw [Fin.sum_univ_five]
      ext i
      fin_cases i <;> simp [w, pts, pA, pB, pC, pN, pS] <;> ring

lemma aff_indep_of_coord_eq (pts : Fin 4 → Point)
    (hsolve : ∀ w0 w1 w2 w3 : ℝ, w0 + w1 + w2 + w3 = 0 →
      (w0 * pts 0 0 + w1 * pts 1 0 + w2 * pts 2 0 + w3 * pts 3 0 = 0) →
      (w0 * pts 0 1 + w1 * pts 1 1 + w2 * pts 2 1 + w3 * pts 3 1 = 0) →
      (w0 * pts 0 2 + w1 * pts 1 2 + w2 * pts 2 2 + w3 * pts 3 2 = 0) →
      w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0) :
    AffineIndependent ℝ pts := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw0 hwx i
  rw [Finset.univ.weightedVSub_eq_linear_combination hw0, Fin.sum_univ_four] at hwx
  rw [Fin.sum_univ_four] at hw0
  have h0 := congr_arg (fun p : Point => p 0) hwx
  have h1 := congr_arg (fun p : Point => p 1) hwx
  have h2 := congr_arg (fun p : Point => p 2) hwx
  simp only [pt_add, pt_smul, PiLp.zero_apply] at h0 h1 h2
  have hs := hsolve (w 0) (w 1) (w 2) (w 3) hw0 h0 h1 h2
  fin_cases i
  · exact hs.1
  · exact hs.2.1
  · exact hs.2.2.1
  · exact hs.2.2.2

noncomputable def T1 : Tetrahedron :=
  ⟨![pA, pB, pC, pN], aff_indep_of_coord_eq ![pA, pB, pC, pN] fun w0 w1 w2 w3 hs hx hy hz => by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, pA, pB, pC, pN,
      mkPt_0, mkPt_1, mkPt_2] at hx hy hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

noncomputable def T2 : Tetrahedron :=
  ⟨![pA, pB, pC, pS], aff_indep_of_coord_eq ![pA, pB, pC, pS] fun w0 w1 w2 w3 hs hx hy hz => by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, pA, pB, pC, pS,
      mkPt_0, mkPt_1, mkPt_2] at hx hy hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

noncomputable def U1 : Tetrahedron :=
  ⟨![pN, pS, pA, pB], aff_indep_of_coord_eq ![pN, pS, pA, pB] fun w0 w1 w2 w3 hs hx hy hz => by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, pN, pS, pA, pB,
      mkPt_0, mkPt_1, mkPt_2] at hx hy hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

noncomputable def U2 : Tetrahedron :=
  ⟨![pN, pS, pB, pC], aff_indep_of_coord_eq ![pN, pS, pB, pC] fun w0 w1 w2 w3 hs hx hy hz => by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, pN, pS, pB, pC,
      mkPt_0, mkPt_1, mkPt_2] at hx hy hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

noncomputable def U3 : Tetrahedron :=
  ⟨![pN, pS, pC, pA], aff_indep_of_coord_eq ![pN, pS, pC, pA] fun w0 w1 w2 w3 hs hx hy hz => by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, pN, pS, pC, pA,
      mkPt_0, mkPt_1, mkPt_2] at hx hy hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

noncomputable def famT : Finset Tetrahedron := {T1, T2}
noncomputable def famU : Finset Tetrahedron := {U1, U2, U3}

lemma T1_ne_T2 : T1 ≠ T2 := fun h => by
  have := congr_arg (fun t : Tetrahedron => t.points 3) h
  exact p_ne_NS this

lemma U1_ne_U2 : U1 ≠ U2 := fun h => by
  have := congr_arg (fun t : Tetrahedron => t.points 2) h
  exact p_ne_AB this

lemma U1_ne_U3 : U1 ≠ U3 := fun h => by
  have := congr_arg (fun t : Tetrahedron => t.points 2) h
  exact p_ne_AC this

lemma U2_ne_U3 : U2 ≠ U3 := fun h => by
  have := congr_arg (fun t : Tetrahedron => t.points 2) h
  exact p_ne_BC this

lemma range_T1_ne_T2 : Set.range T1.points ≠ Set.range T2.points := fun h => by
  have hmem : pN ∈ Set.range T1.points := ⟨3, rfl⟩
  rw [h] at hmem
  rcases hmem with ⟨i, hi⟩
  fin_cases i
  · exact p_ne_AN hi
  · exact p_ne_BN hi
  · exact p_ne_CN hi
  · exact p_ne_NS hi.symm

lemma range_U1_ne_U2 : Set.range U1.points ≠ Set.range U2.points := fun h => by
  have hmem : pA ∈ Set.range U1.points := ⟨2, rfl⟩
  rw [h] at hmem
  rcases hmem with ⟨i, hi⟩
  fin_cases i
  · exact p_ne_AN hi.symm
  · exact p_ne_AS hi.symm
  · exact p_ne_AB hi.symm
  · exact p_ne_AC hi.symm

lemma range_U1_ne_U3 : Set.range U1.points ≠ Set.range U3.points := fun h => by
  have hmem : pB ∈ Set.range U1.points := ⟨3, rfl⟩
  rw [h] at hmem
  rcases hmem with ⟨i, hi⟩
  fin_cases i
  · exact p_ne_BN hi.symm
  · exact p_ne_BS hi.symm
  · exact p_ne_BC hi.symm
  · exact p_ne_AB hi

lemma range_U2_ne_U3 : Set.range U2.points ≠ Set.range U3.points := fun h => by
  have hmem : pB ∈ Set.range U2.points := ⟨2, rfl⟩
  rw [h] at hmem
  rcases hmem with ⟨i, hi⟩
  fin_cases i
  · exact p_ne_BN hi.symm
  · exact p_ne_BS hi.symm
  · exact p_ne_BC hi.symm
  · exact p_ne_AB hi

lemma verts_range : (verts : Set Point) = Set.range ![pA, pB, pC, pN, pS] := by
  ext x
  simp only [verts, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

lemma mem_verts_convexHull_iff {x : Point} :
    x ∈ convexHull ℝ (verts : Set Point) ↔
      ∃ wA wB wC wN wS : ℝ, 0 ≤ wA ∧ 0 ≤ wB ∧ 0 ≤ wC ∧ 0 ≤ wN ∧ 0 ≤ wS ∧
        wA + wB + wC + wN + wS = 1 ∧
        wA • pA + wB • pB + wC • pC + wN • pN + wS • pS = x := by
  rw [verts_range, mem_convexHull_range_iff]
  constructor
  · rintro ⟨w, hw0, hw1, hx⟩
    refine ⟨w 0, w 1, w 2, w 3, w 4, hw0 0, hw0 1, hw0 2, hw0 3, hw0 4, ?_, ?_⟩
    · rw [Fin.sum_univ_five] at hw1; linarith
    · rw [Fin.sum_univ_five] at hx; simpa [add_assoc] using hx
  · rintro ⟨wA, wB, wC, wN, wS, hA, hB, hC, hN, hS, hs, hx⟩
    refine ⟨![wA, wB, wC, wN, wS], fun i => by fin_cases i <;> assumption, ?_, ?_⟩
    · rw [Fin.sum_univ_five]; simpa [add_assoc] using hs
    · rw [Fin.sum_univ_five]; simpa [add_assoc] using hx

lemma mem_region_iff (t : Tetrahedron) {x : Point} :
    x ∈ region t ↔
      ∃ w0 w1 w2 w3 : ℝ, 0 ≤ w0 ∧ 0 ≤ w1 ∧ 0 ≤ w2 ∧ 0 ≤ w3 ∧
        w0 + w1 + w2 + w3 = 1 ∧
        w0 • t.points 0 + w1 • t.points 1 + w2 • t.points 2 + w3 • t.points 3 = x := by
  rw [region, mem_convexHull_range_iff]
  constructor
  · rintro ⟨w, hw0, hw1, hx⟩
    refine ⟨w 0, w 1, w 2, w 3, hw0 0, hw0 1, hw0 2, hw0 3, ?_, ?_⟩
    · rw [Fin.sum_univ_four] at hw1; linarith
    · rw [Fin.sum_univ_four] at hx; simpa [add_assoc] using hx
  · rintro ⟨w0, w1, w2, w3, h0, h1, h2, h3, hs, hx⟩
    refine ⟨![w0, w1, w2, w3], fun i => by fin_cases i <;> assumption, ?_, ?_⟩
    · rw [Fin.sum_univ_four]; simpa [add_assoc] using hs
    · rw [Fin.sum_univ_four]; simpa [add_assoc] using hx

lemma isTet_T : IsTetrahedralization verts famT := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t ht _ ⟨i, rfl⟩
    simp only [famT, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> fin_cases i <;> simp [T1, T2, verts]
  · refine Set.Subset.antisymm ?_ ?_
    · refine Set.iUnion₂_subset fun t ht => convexHull_mono ?_
      rintro _ ⟨i, rfl⟩
      simp only [famT, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> fin_cases i <;> simp [T1, T2, verts]
    · intro x hx
      rw [mem_verts_convexHull_iff] at hx
      rcases hx with ⟨wA, wB, wC, wN, wS, hA, hB, hC, hN, hS, hs, hx⟩
      rcases le_total wS wN with hSN | hNS
      · refine Set.mem_iUnion₂.mpr ⟨T1, by simp [famT], (mem_region_iff T1).mpr ?_⟩
        refine ⟨wA + 3 / 4 * wS, wB + 5 / 8 * wS, wC + 5 / 8 * wS, wN - wS,
          by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
        ext i; fin_cases i <;> simp [T1, ← hx, pA, pB, pC, pN, pS] <;> ring
      · refine Set.mem_iUnion₂.mpr ⟨T2, by simp [famT], (mem_region_iff T2).mpr ?_⟩
        refine ⟨wA + 3 / 4 * wN, wB + 5 / 8 * wN, wC + 5 / 8 * wN, wS - wN,
          by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
        ext i; fin_cases i <;> simp [T2, ← hx, pA, pB, pC, pN, pS] <;> ring
  · intro t ht u hu htu
    have sub_inter : ∀ {x : Point}, x ∈ region T1 → x ∈ region T2 →
        x ∈ convexHull ℝ (Set.range T1.points ∩ Set.range T2.points) := by
      intro x hx1 hx2
      rw [mem_region_iff] at hx1 hx2
      rcases hx1 with ⟨w0, w1, w2, w3, h0, h1, h2, h3, hs, hx⟩
      rcases hx2 with ⟨u0, u1, u2, u3, hu0, hu1, hu2, hu3, hus, hux⟩
      have hz1 : x 2 = 5 * w3 := by rw [← hx]; simp [T1, pA, pB, pC, pN]; ring
      have hz2 : x 2 = -5 * u3 := by rw [← hux]; simp [T2, pA, pB, pC, pS]; ring
      have hw3 : w3 = 0 := by linarith
      refine convexHull_mono (s := Set.range ![pA, pB, pC]) ?_ ?_
      · rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
        · exact ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩
        · exact ⟨⟨2, rfl⟩, ⟨2, rfl⟩⟩
      · rw [mem_convexHull_range_iff]
        refine ⟨![w0, w1, w2], fun i => by fin_cases i <;> assumption, ?_, ?_⟩
        · rw [Fin.sum_univ_three]; simp; linarith
        · rw [Fin.sum_univ_three, ← hx, hw3]; simp [T1, zero_smul, add_zero, add_assoc]
    simp only [famT, Finset.mem_insert, Finset.mem_singleton] at ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
    · exact absurd rfl htu
    · exact ⟨range_T1_ne_T2, Set.Subset.antisymm (fun x ⟨hx1, hx2⟩ => sub_inter hx1 hx2)
        (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))⟩
    · refine ⟨range_T1_ne_T2.symm, Set.Subset.antisymm (fun x ⟨hx2, hx1⟩ => ?_)
        (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))⟩
      rw [Set.inter_comm]; exact sub_inter hx1 hx2
    · exact absurd rfl htu

lemma isTet_U : IsTetrahedralization verts famU := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t ht _ ⟨i, rfl⟩
    simp only [famU, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> fin_cases i <;> simp [U1, U2, U3, verts]
  · refine Set.Subset.antisymm ?_ ?_
    · refine Set.iUnion₂_subset fun t ht => convexHull_mono ?_
      rintro _ ⟨i, rfl⟩
      simp only [famU, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> fin_cases i <;> simp [U1, U2, U3, verts]
    · intro x hx
      rw [mem_verts_convexHull_iff] at hx
      rcases hx with ⟨wA, wB, wC, wN, wS, hA, hB, hC, hN, hS, hs, hx⟩
      set m := min (4 / 3 * wA) (min (8 / 5 * wB) (8 / 5 * wC))
      have hmA : 3 / 4 * m ≤ wA := by
        have := min_le_left (4 / 3 * wA) (min (8 / 5 * wB) (8 / 5 * wC)); linarith
      have hmB : 5 / 8 * m ≤ wB := by
        have := (min_le_right (4 / 3 * wA) (min (8 / 5 * wB) (8 / 5 * wC))).trans
          (min_le_left (8 / 5 * wB) (8 / 5 * wC)); linarith
      have hmC : 5 / 8 * m ≤ wC := by
        have := (min_le_right (4 / 3 * wA) (min (8 / 5 * wB) (8 / 5 * wC))).trans
          (min_le_right (8 / 5 * wB) (8 / 5 * wC)); linarith
      have hm0 : 0 ≤ m := le_min (by linarith) (le_min (by linarith) (by linarith))
      rcases min_cases (4 / 3 * wA) (min (8 / 5 * wB) (8 / 5 * wC)) with ⟨hm_eq, _⟩ | ⟨hm_eq, _⟩
      · refine Set.mem_iUnion₂.mpr ⟨U2, by simp [famU], (mem_region_iff U2).mpr ?_⟩
        have hwA : wA = 3 / 4 * m := by linarith
        refine ⟨wN + m, wS + m, wB - 5 / 8 * m, wC - 5 / 8 * m,
          by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
        ext i; fin_cases i <;> simp [U2, ← hx, hwA, pA, pB, pC, pN, pS] <;> ring
      · rcases min_cases (8 / 5 * wB) (8 / 5 * wC) with ⟨hmB_eq, _⟩ | ⟨hmC_eq, _⟩
        · refine Set.mem_iUnion₂.mpr ⟨U3, by simp [famU], (mem_region_iff U3).mpr ?_⟩
          have hwB : wB = 5 / 8 * m := by linarith
          refine ⟨wN + m, wS + m, wC - 5 / 8 * m, wA - 3 / 4 * m,
            by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
          ext i; fin_cases i <;> simp [U3, ← hx, hwB, pA, pB, pC, pN, pS] <;> ring
        · refine Set.mem_iUnion₂.mpr ⟨U1, by simp [famU], (mem_region_iff U1).mpr ?_⟩
          have hwC : wC = 5 / 8 * m := by linarith
          refine ⟨wN + m, wS + m, wA - 3 / 4 * m, wB - 5 / 8 * m,
            by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
          ext i; fin_cases i <;> simp [U1, ← hx, hwC, pA, pB, pC, pN, pS] <;> ring
  · have sub_12 : ∀ {x : Point}, x ∈ region U1 → x ∈ region U2 →
        x ∈ convexHull ℝ (Set.range U1.points ∩ Set.range U2.points) := by
      intro x hx1 hx2
      rw [mem_region_iff] at hx1 hx2
      rcases hx1 with ⟨w0, w1, w2, w3, h0, h1, h2, h3, hs, hx⟩
      rcases hx2 with ⟨u0, u1, u2, u3, hu0, hu1, hu2, hu3, hus, hux⟩
      have hl1 : 4 * x 0 + 3 * x 1 = 20 * w2 := by
        rw [← hx]; simp [U1, pN, pS, pA, pB]; ring
      have hl2 : 4 * x 0 + 3 * x 1 = -24 * u3 := by
        rw [← hux]; simp [U2, pN, pS, pB, pC]; ring
      have hw2 : w2 = 0 := by linarith
      refine convexHull_mono (s := Set.range ![pN, pS, pB]) ?_ ?_
      · rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
        · exact ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩
        · exact ⟨⟨3, rfl⟩, ⟨2, rfl⟩⟩
      · rw [mem_convexHull_range_iff]
        refine ⟨![w0, w1, w3], fun i => by fin_cases i <;> assumption, ?_, ?_⟩
        · rw [Fin.sum_univ_three]; simp; linarith
        · rw [Fin.sum_univ_three, ← hx, hw2]; simp [U1, zero_smul, add_zero, add_assoc]
    have sub_23 : ∀ {x : Point}, x ∈ region U2 → x ∈ region U3 →
        x ∈ convexHull ℝ (Set.range U2.points ∩ Set.range U3.points) := by
      intro x hx2 hx3
      rw [mem_region_iff] at hx2 hx3
      rcases hx2 with ⟨w0, w1, w2, w3, h0, h1, h2, h3, hs, hx⟩
      rcases hx3 with ⟨u0, u1, u2, u3, hu0, hu1, hu2, hu3, hus, hux⟩
      have hl2 : 4 * x 0 - 3 * x 1 = -24 * w2 := by
        rw [← hx]; simp [U2, pN, pS, pB, pC]; ring
      have hl3 : 4 * x 0 - 3 * x 1 = 20 * u3 := by
        rw [← hux]; simp [U3, pN, pS, pC, pA]; ring
      have hw2 : w2 = 0 := by linarith
      refine convexHull_mono (s := Set.range ![pN, pS, pC]) ?_ ?_
      · rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
        · exact ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩
        · exact ⟨⟨3, rfl⟩, ⟨2, rfl⟩⟩
      · rw [mem_convexHull_range_iff]
        refine ⟨![w0, w1, w3], fun i => by fin_cases i <;> assumption, ?_, ?_⟩
        · rw [Fin.sum_univ_three]; simp; linarith
        · rw [Fin.sum_univ_three, ← hx, hw2]; simp [U2, zero_smul, add_zero, add_assoc]
    have sub_13 : ∀ {x : Point}, x ∈ region U1 → x ∈ region U3 →
        x ∈ convexHull ℝ (Set.range U1.points ∩ Set.range U3.points) := by
      intro x hx1 hx3
      rw [mem_region_iff] at hx1 hx3
      rcases hx1 with ⟨w0, w1, w2, w3, h0, h1, h2, h3, hs, hx⟩
      rcases hx3 with ⟨u0, u1, u2, u3, hu0, hu1, hu2, hu3, hus, hux⟩
      have hl1 : x 1 = 4 * w3 := by rw [← hx]; simp [U1, pN, pS, pA, pB]; ring
      have hl3 : x 1 = -4 * u2 := by rw [← hux]; simp [U3, pN, pS, pC, pA]; ring
      have hw3 : w3 = 0 := by linarith
      refine convexHull_mono (s := Set.range ![pN, pS, pA]) ?_ ?_
      · rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
        · exact ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩
        · exact ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩
      · rw [mem_convexHull_range_iff]
        refine ⟨![w0, w1, w2], fun i => by fin_cases i <;> assumption, ?_, ?_⟩
        · rw [Fin.sum_univ_three]; simp; linarith
        · rw [Fin.sum_univ_three, ← hx, hw3]; simp [U1, zero_smul, add_zero, add_assoc]
    intro t ht u hu htu
    simp only [famU, Finset.mem_insert, Finset.mem_singleton] at ht hu
    rcases ht with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl
    · exact absurd rfl htu
    · exact ⟨range_U1_ne_U2, Set.Subset.antisymm (fun x ⟨hx1, hx2⟩ => sub_12 hx1 hx2)
        (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))⟩
    · exact ⟨range_U1_ne_U3, Set.Subset.antisymm (fun x ⟨hx1, hx3⟩ => sub_13 hx1 hx3)
        (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))⟩
    · refine ⟨range_U1_ne_U2.symm, Set.Subset.antisymm (fun x ⟨hx2, hx1⟩ => ?_)
        (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))⟩
      rw [Set.inter_comm]; exact sub_12 hx1 hx2
    · exact absurd rfl htu
    · exact ⟨range_U2_ne_U3, Set.Subset.antisymm (fun x ⟨hx2, hx3⟩ => sub_23 hx2 hx3)
        (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))⟩
    · refine ⟨range_U1_ne_U3.symm, Set.Subset.antisymm (fun x ⟨hx3, hx1⟩ => ?_)
        (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))⟩
      rw [Set.inter_comm]; exact sub_13 hx1 hx3
    · refine ⟨range_U2_ne_U3.symm, Set.Subset.antisymm (fun x ⟨hx3, hx2⟩ => ?_)
        (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))⟩
      rw [Set.inter_comm]; exact sub_23 hx2 hx3
    · exact absurd rfl htu

lemma inradius_eq (s : Tetrahedron) : s.inradius = (∑ i : Fin 4, (s.height i)⁻¹)⁻¹ := by
  rw [Simplex.inradius_eq_abs_inv_sum]
  simp_rw [Simplex.excenterWeightsUnnorm_empty_apply]
  exact abs_of_pos (inv_pos.mpr (Finset.sum_pos (fun i _ => inv_pos.mpr (s.height_pos i)) Finset.univ_nonempty))

lemma height_le_dist_bary (s : Tetrahedron) (i j0 j1 j2 : Fin 4)
    (hj0 : j0 ≠ i) (hj1 : j1 ≠ i) (hj2 : j2 ≠ i) (w0 w1 w2 : ℝ) (hw : w0 + w1 + w2 = 1) :
    s.height i ≤ dist (s.points i) (w0 • s.points j0 + w1 • s.points j1 + w2 • s.points j2) := by
  let f : Fin 3 → Point := ![s.points j0, s.points j1, s.points j2]
  let w : Fin 3 → ℝ := ![w0, w1, w2]
  have hw1 : ∑ k : Fin 3, w k = 1 := by rw [Fin.sum_univ_three]; simpa [w] using hw
  have hq_aff : Finset.univ.affineCombination ℝ f w =
      w0 • s.points j0 + w1 • s.points j1 + w2 • s.points j2 := by
    rw [Finset.univ.affineCombination_eq_linear_combination f w hw1, Fin.sum_univ_three]
    simp [f, w, add_assoc]
  have hq_mem : w0 • s.points j0 + w1 • s.points j1 + w2 • s.points j2 ∈
      affineSpan ℝ (Set.range (s.faceOpposite i).points) := by
    rw [← hq_aff]
    refine affineSpan_mono ℝ ?_ (affineCombination_mem_affineSpan hw1 f)
    rintro _ ⟨k, rfl⟩
    rw [Simplex.range_faceOpposite_points]
    fin_cases k
    · exact ⟨j0, hj0, rfl⟩
    · exact ⟨j1, hj1, rfl⟩
    · exact ⟨j2, hj2, rfl⟩
  haveI : Nonempty (affineSpan ℝ (Set.range (s.faceOpposite i).points)) :=
    ⟨⟨(s.faceOpposite i).points 0, subset_affineSpan ℝ _ ⟨0, rfl⟩⟩⟩
  rw [Simplex.height, Simplex.altitudeFoot, Simplex.orthogonalProjectionSpan,
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist]
  exact Metric.infDist_le_dist_of_mem hq_mem

lemma inv_height_gt_bary (s : Tetrahedron) (i j0 j1 j2 : Fin 4)
    (hj0 : j0 ≠ i) (hj1 : j1 ≠ i) (hj2 : j2 ≠ i) (w0 w1 w2 r : ℝ) (hw : w0 + w1 + w2 = 1)
    (hr : 0 < r)
    (hdist : dist (s.points i) (w0 • s.points j0 + w1 • s.points j1 + w2 • s.points j2) ^ 2 < r ^ 2) :
    r⁻¹ < (s.height i)⁻¹ := by
  have hlt : s.height i < r := by
    have hle := height_le_dist_bary s i j0 j1 j2 hj0 hj1 hj2 w0 w1 w2 hw
    have hdlt : dist (s.points i) (w0 • s.points j0 + w1 • s.points j1 + w2 • s.points j2) < r := by
      nlinarith [dist_nonneg (x := s.points i) (y := w0 • s.points j0 + w1 • s.points j1 + w2 • s.points j2)]
    exact hle.trans_lt hdlt
  exact (inv_lt_inv₀ hr (s.height_pos i)).mpr hlt

lemma inv_height_ge_bary (s : Tetrahedron) (i j0 j1 j2 : Fin 4)
    (hj0 : j0 ≠ i) (hj1 : j1 ≠ i) (hj2 : j2 ≠ i) (w0 w1 w2 r : ℝ) (hw : w0 + w1 + w2 = 1)
    (hr : 0 < r)
    (hdist : dist (s.points i) (w0 • s.points j0 + w1 • s.points j1 + w2 • s.points j2) ^ 2 ≤ r ^ 2) :
    r⁻¹ ≤ (s.height i)⁻¹ := by
  have hle_r : s.height i ≤ r := by
    have hle := height_le_dist_bary s i j0 j1 j2 hj0 hj1 hj2 w0 w1 w2 hw
    have hdle : dist (s.points i) (w0 • s.points j0 + w1 • s.points j1 + w2 • s.points j2) ≤ r := by
      nlinarith [dist_nonneg (x := s.points i) (y := w0 • s.points j0 + w1 • s.points j1 + w2 • s.points j2)]
    exact hle.trans hdle
  exact (inv_le_inv₀ hr (s.height_pos i)).mpr hle_r

lemma height_ge_of_normal (s : Tetrahedron) (i : Fin 4) (n : Point) (hn : 0 < ‖n‖)
    (d : ℝ) (hface : ∀ j : Fin 4, j ≠ i → ⟪s.points j, n⟫ = d) :
    |⟪s.points i, n⟫ - d| / ‖n‖ ≤ s.height i := by
  have hfoot_mem := s.altitudeFoot_mem_affineSpan_faceOpposite i
  rw [mem_affineSpan_iff_eq_affineCombination] at hfoot_mem
  obtain ⟨fs, w, hw1, hfq⟩ := hfoot_mem
  have hpt : ∀ k, ⟪(s.faceOpposite i).points k, n⟫ = d := fun k => by
    have hk : (s.faceOpposite i).points k ∈ Set.range (s.faceOpposite i).points := ⟨k, rfl⟩
    rw [Simplex.range_faceOpposite_points] at hk
    obtain ⟨j, hj, hjk⟩ := hk
    rw [← hjk]; exact hface j hj
  have hfoot_dot : ⟪s.altitudeFoot i, n⟫ = d := by
    rw [hfq, Finset.affineCombination_eq_linear_combination fs _ w hw1, sum_inner]
    simp_rw [real_inner_smul_left, hpt, ← Finset.sum_mul, hw1, one_mul]
  have hineq : |⟪s.points i, n⟫ - d| ≤ s.height i * ‖n‖ := by
    rw [← hfoot_dot, ← inner_sub_left, Simplex.height, dist_eq_norm]
    exact abs_real_inner_le_norm (s.points i - s.altitudeFoot i) n
  exact (div_le_iff₀ hn).mpr hineq

lemma inv_height_lt_of_normal (s : Tetrahedron) (i : Fin 4) (n : Point) (d r c : ℝ)
    (hr : 0 < r) (hc : 0 < c) (hface : ∀ j : Fin 4, j ≠ i → ⟪s.points j, n⟫ = d)
    (hdot : |⟪s.points i, n⟫ - d| = c) (hn_sq : r ^ 2 * ‖n‖ ^ 2 < c ^ 2) :
    (s.height i)⁻¹ < r⁻¹ := by
  have hn_pos : 0 < ‖n‖ := by
    by_contra h
    have hn0 : n = 0 := norm_eq_zero.mp (le_antisymm (not_lt.mp h) (norm_nonneg n))
    have hd0 : d = 0 := by
      obtain ⟨j, hj⟩ : ∃ j : Fin 4, j ≠ i := by
        fin_cases i
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
      have := hface j hj
      simp [hn0] at this
      exact this.symm
    simp [hn0, hd0] at hdot
    linarith
  have h1 : r * ‖n‖ < c := by
    have hsq : (r * ‖n‖) ^ 2 < c ^ 2 := by nlinarith
    nlinarith [mul_pos hr hn_pos]
  have h2 : r < s.height i := by
    have hge := height_ge_of_normal s i n hn_pos d hface
    rw [hdot] at hge
    exact ((lt_div_iff₀ hn_pos).mpr h1).trans_le hge
  exact (inv_lt_inv₀ (s.height_pos i) hr).mpr h2

lemma inv_height_le_of_normal (s : Tetrahedron) (i : Fin 4) (n : Point) (d r c : ℝ)
    (hr : 0 < r) (hc : 0 < c) (hface : ∀ j : Fin 4, j ≠ i → ⟪s.points j, n⟫ = d)
    (hdot : |⟪s.points i, n⟫ - d| = c) (hn_sq : r ^ 2 * ‖n‖ ^ 2 ≤ c ^ 2) :
    (s.height i)⁻¹ ≤ r⁻¹ := by
  have hn_pos : 0 < ‖n‖ := by
    by_contra h
    have hn0 : n = 0 := norm_eq_zero.mp (le_antisymm (not_lt.mp h) (norm_nonneg n))
    have hd0 : d = 0 := by
      obtain ⟨j, hj⟩ : ∃ j : Fin 4, j ≠ i := by
        fin_cases i
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
      have := hface j hj
      simp [hn0] at this
      exact this.symm
    simp [hn0, hd0] at hdot
    linarith
  have h1 : r * ‖n‖ ≤ c := by
    have hsq : (r * ‖n‖) ^ 2 ≤ c ^ 2 := by nlinarith
    nlinarith [mul_pos hr hn_pos]
  have h2 : r ≤ s.height i := by
    have hge := height_ge_of_normal s i n hn_pos d hface
    rw [hdot] at hge
    exact ((le_div_iff₀ hn_pos).mpr h1).trans hge
  exact (inv_le_inv₀ (s.height_pos i) hr).mpr h2

lemma T1_inradius_lt : T1.inradius < 14 / 9 := by
  have h0 : (7 : ℝ)⁻¹ < (T1.height 0)⁻¹ := by
    refine inv_height_gt_bary T1 0 1 2 3 (by decide) (by decide) (by decide)
      (5 / 34) (5 / 34) (12 / 17) 7 (by norm_num) (by norm_num) ?_
    rw [dist_sq_eq]; simp [T1, pA, pB, pC, pN]; norm_num
  have h1 : (20 / 3 : ℝ)⁻¹ < (T1.height 1)⁻¹ := by
    refine inv_height_gt_bary T1 1 0 2 3 (by decide) (by decide) (by decide)
      (2 / 15) (1 / 3) (8 / 15) (20 / 3) (by norm_num) (by norm_num) ?_
    rw [dist_sq_eq]; simp [T1, pA, pB, pC, pN]; norm_num
  have h2 : (20 / 3 : ℝ)⁻¹ < (T1.height 2)⁻¹ := by
    refine inv_height_gt_bary T1 2 0 1 3 (by decide) (by decide) (by decide)
      (2 / 15) (1 / 3) (8 / 15) (20 / 3) (by norm_num) (by norm_num) ?_
    rw [dist_sq_eq]; simp [T1, pA, pB, pC, pN]; norm_num
  have h3 : (5 : ℝ)⁻¹ ≤ (T1.height 3)⁻¹ := by
    refine inv_height_ge_bary T1 3 0 1 2 (by decide) (by decide) (by decide)
      (3 / 8) (5 / 16) (5 / 16) 5 (by norm_num) (by norm_num) ?_
    rw [dist_sq_eq]; simp [T1, pA, pB, pC, pN]; norm_num
  have hsum : (9 / 14 : ℝ) < ∑ i : Fin 4, (T1.height i)⁻¹ := by
    rw [Fin.sum_univ_four]
    linarith
  have hpos : 0 < ∑ i : Fin 4, (T1.height i)⁻¹ := by linarith
  rw [inradius_eq]
  simpa using (inv_lt_inv₀ hpos (by norm_num : (0 : ℝ) < 9 / 14)).mpr hsum

lemma T2_inradius_lt : T2.inradius < 14 / 9 := by
  have h0 : (7 : ℝ)⁻¹ < (T2.height 0)⁻¹ := by
    refine inv_height_gt_bary T2 0 1 2 3 (by decide) (by decide) (by decide)
      (5 / 34) (5 / 34) (12 / 17) 7 (by norm_num) (by norm_num) ?_
    rw [dist_sq_eq]; simp [T2, pA, pB, pC, pS]; norm_num
  have h1 : (20 / 3 : ℝ)⁻¹ < (T2.height 1)⁻¹ := by
    refine inv_height_gt_bary T2 1 0 2 3 (by decide) (by decide) (by decide)
      (2 / 15) (1 / 3) (8 / 15) (20 / 3) (by norm_num) (by norm_num) ?_
    rw [dist_sq_eq]; simp [T2, pA, pB, pC, pS]; norm_num
  have h2 : (20 / 3 : ℝ)⁻¹ < (T2.height 2)⁻¹ := by
    refine inv_height_gt_bary T2 2 0 1 3 (by decide) (by decide) (by decide)
      (2 / 15) (1 / 3) (8 / 15) (20 / 3) (by norm_num) (by norm_num) ?_
    rw [dist_sq_eq]; simp [T2, pA, pB, pC, pS]; norm_num
  have h3 : (5 : ℝ)⁻¹ ≤ (T2.height 3)⁻¹ := by
    refine inv_height_ge_bary T2 3 0 1 2 (by decide) (by decide) (by decide)
      (3 / 8) (5 / 16) (5 / 16) 5 (by norm_num) (by norm_num) ?_
    rw [dist_sq_eq]; simp [T2, pA, pB, pC, pS]; norm_num
  have hsum : (9 / 14 : ℝ) < ∑ i : Fin 4, (T2.height i)⁻¹ := by
    rw [Fin.sum_univ_four]
    linarith
  have hpos : 0 < ∑ i : Fin 4, (T2.height i)⁻¹ := by linarith
  rw [inradius_eq]
  simpa using (inv_lt_inv₀ hpos (by norm_num : (0 : ℝ) < 9 / 14)).mpr hsum

lemma U1_inradius_gt : (1 : ℝ) < U1.inradius := by
  have h0 : (U1.height 0)⁻¹ < (4 : ℝ)⁻¹ := by
    refine inv_height_lt_of_normal U1 0 (mkPt (-1) (-2) 1) (-5) 4 10
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U1, pN, pS, pA, pB, pC]
    · norm_num [inner_eq, U1, pN]
    · norm_num [norm_sq_eq]
  have h1 : (U1.height 1)⁻¹ < (4 : ℝ)⁻¹ := by
    refine inv_height_lt_of_normal U1 1 (mkPt 1 2 1) 5 4 10
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U1, pN, pS, pA, pB, pC]
    · norm_num [inner_eq, U1, pS]
    · norm_num [norm_sq_eq]
  have h2 : (U1.height 2)⁻¹ ≤ (4 : ℝ)⁻¹ := by
    refine inv_height_le_of_normal U1 2 (mkPt 4 3 0) 0 4 20
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U1, pN, pS, pA, pB, pC]
    · simp [inner_eq, U1, pA]; try norm_num
    · norm_num [norm_sq_eq]
  have h3 : (U1.height 3)⁻¹ ≤ (4 : ℝ)⁻¹ := by
    refine inv_height_le_of_normal U1 3 (mkPt 0 (-1) 0) 0 4 4
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U1, pN, pS, pA, pB, pC]
    · simp [inner_eq, U1, pB]; try norm_num
    · norm_num [norm_sq_eq]
  have hpos : 0 < ∑ i : Fin 4, (U1.height i)⁻¹ :=
    Finset.sum_pos (fun i _ => inv_pos.mpr (U1.height_pos i)) Finset.univ_nonempty
  have hsum : ∑ i : Fin 4, (U1.height i)⁻¹ < 1 := by
    rw [Fin.sum_univ_four]; linarith
  rw [inradius_eq]
  simpa using (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 1) hpos).mpr hsum

lemma U2_inradius_gt : (60 / 49 : ℝ) < U2.inradius := by
  have h0 : (U2.height 0)⁻¹ < (5 : ℝ)⁻¹ := by
    refine inv_height_lt_of_normal U2 0 (mkPt 5 0 3) (-15) 5 30
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U2, pN, pS, pA, pB, pC]
    · norm_num [inner_eq, U2, pN]
    · norm_num [norm_sq_eq]
  have h1 : (U2.height 1)⁻¹ < (5 : ℝ)⁻¹ := by
    refine inv_height_lt_of_normal U2 1 (mkPt (-5) 0 3) 15 5 30
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U2, pN, pS, pA, pB, pC]
    · norm_num [inner_eq, U2, pS]
    · norm_num [norm_sq_eq]
  have h2 : (U2.height 2)⁻¹ ≤ (24 / 5 : ℝ)⁻¹ := by
    refine inv_height_le_of_normal U2 2 (mkPt (-4) 3 0) 0 (24 / 5) 24
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U2, pN, pS, pA, pB, pC]
    · simp [inner_eq, U2, pB]; try norm_num
    · norm_num [norm_sq_eq]
  have h3 : (U2.height 3)⁻¹ ≤ (24 / 5 : ℝ)⁻¹ := by
    refine inv_height_le_of_normal U2 3 (mkPt 4 3 0) 0 (24 / 5) 24
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U2, pN, pS, pA, pB, pC]
    · simp [inner_eq, U2, pC]; try norm_num
    · norm_num [norm_sq_eq]
  have hpos : 0 < ∑ i : Fin 4, (U2.height i)⁻¹ :=
    Finset.sum_pos (fun i _ => inv_pos.mpr (U2.height_pos i)) Finset.univ_nonempty
  have hsum : ∑ i : Fin 4, (U2.height i)⁻¹ < 49 / 60 := by
    rw [Fin.sum_univ_four]; linarith
  rw [inradius_eq]
  simpa using (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 49 / 60) hpos).mpr hsum

lemma U3_inradius_gt : (1 : ℝ) < U3.inradius := by
  have h0 : (U3.height 0)⁻¹ < (4 : ℝ)⁻¹ := by
    refine inv_height_lt_of_normal U3 0 (mkPt (-1) 2 1) (-5) 4 10
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U3, pN, pS, pA, pB, pC]
    · norm_num [inner_eq, U3, pN]
    · norm_num [norm_sq_eq]
  have h1 : (U3.height 1)⁻¹ < (4 : ℝ)⁻¹ := by
    refine inv_height_lt_of_normal U3 1 (mkPt 1 (-2) 1) 5 4 10
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U3, pN, pS, pA, pB, pC]
    · norm_num [inner_eq, U3, pS]
    · norm_num [norm_sq_eq]
  have h2 : (U3.height 2)⁻¹ ≤ (4 : ℝ)⁻¹ := by
    refine inv_height_le_of_normal U3 2 (mkPt 0 (-1) 0) 0 4 4
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U3, pN, pS, pA, pB, pC]
    · simp [inner_eq, U3, pC]; try norm_num
    · norm_num [norm_sq_eq]
  have h3 : (U3.height 3)⁻¹ ≤ (4 : ℝ)⁻¹ := by
    refine inv_height_le_of_normal U3 3 (mkPt (-4) 3 0) 0 4 20
      (by norm_num) (by norm_num) (fun j hj => ?_) ?_ ?_
    · fin_cases j <;> first | exact absurd rfl hj | norm_num [inner_eq, U3, pN, pS, pA, pB, pC]
    · simp [inner_eq, U3, pA]; try norm_num
    · norm_num [norm_sq_eq]
  have hpos : 0 < ∑ i : Fin 4, (U3.height i)⁻¹ :=
    Finset.sum_pos (fun i _ => inv_pos.mpr (U3.height_pos i)) Finset.univ_nonempty
  have hsum : ∑ i : Fin 4, (U3.height i)⁻¹ < 1 := by
    rw [Fin.sum_univ_four]; linarith
  rw [inradius_eq]
  simpa using (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 1) hpos).mpr hsum

end Mo165168Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_165168.main) := by
  intro hmain
  have heq := hmain Mo165168Disproof.verts Mo165168Disproof.sphere_cond
    Mo165168Disproof.interior_nonempty Mo165168Disproof.famT Mo165168Disproof.famU
    Mo165168Disproof.isTet_T Mo165168Disproof.isTet_U
  have hsumT : (∑ t ∈ Mo165168Disproof.famT, t.inradius) =
      Mo165168Disproof.T1.inradius + Mo165168Disproof.T2.inradius := by
    rw [Mo165168Disproof.famT, Finset.sum_pair Mo165168Disproof.T1_ne_T2]
  have hsumU : (∑ u ∈ Mo165168Disproof.famU, u.inradius) =
      Mo165168Disproof.U1.inradius + (Mo165168Disproof.U2.inradius + Mo165168Disproof.U3.inradius) := by
    rw [Mo165168Disproof.famU,
      Finset.sum_insert (by rw [Finset.mem_insert, Finset.mem_singleton]; push Not; exact ⟨Mo165168Disproof.U1_ne_U2, Mo165168Disproof.U1_ne_U3⟩),
      Finset.sum_pair Mo165168Disproof.U2_ne_U3]
  have hlt := Mo165168Disproof.T1_inradius_lt
  have hlt2 := Mo165168Disproof.T2_inradius_lt
  have hgt1 := Mo165168Disproof.U1_inradius_gt
  have hgt2 := Mo165168Disproof.U2_inradius_gt
  have hgt3 := Mo165168Disproof.U3_inradius_gt
  linarith
