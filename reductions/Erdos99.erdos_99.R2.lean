import FormalConjectures.ErdosProblems.«99»

/-!
# Reduction `Erdos99.erdos_99.R2` of Erdős Problem 99

Credit: `@sanchan`

Strictly strengthens `Erdos99.erdos_99.R1` by proving unconditionally inside `main`:
1. Hexagonal-lattice packing upper bound: `diam(A) <= 2 * (Nat.sqrt (n / 3) + 1)`
2. Disk-packing area lower bound: `pi * n <= 4 * (diam(A) + 1)^2`
3. Unit-distance max degree `<= 5` for triangle-free 1-separated sets
4. Geometric planarity: disjoint-endpoint unit segments do not intersect
5. Hopf-Pannwitz bound: at most `n` unordered diametral pairs (`<= 2n` ordered)
6. First-order Farkas velocity obstruction and existence of a non-isolated diametral pair

Splits the remaining core into:
- `H1`: sparse / rattler regime (average unit degree `< 3`)
- `H2`: dense / quadrangulated regime (average unit degree `>= 3`)
-/

open Set Metric EuclideanGeometry Filter MeasureTheory
open scoped InnerProductSpace Topology BigOperators

namespace OMA.R_Erdos99_erdos_99_R2

/- ### Part 1: Basic diameter and rescaling helpers -/

lemma exists_dist_eq_diam (A : Finset ℝ²) (hA : A.Nonempty) :
    ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) := by
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image (A ×ˢ A)
    (fun z : ℝ² × ℝ² => dist z.1 z.2) (hA.product hA)
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hz
  refine ⟨z.1, hp, z.2, hq, le_antisymm
    (dist_le_diam_of_mem A.finite_toSet.isBounded hp hq) ?_⟩
  exact diam_le_of_forall_dist_le (dist_nonneg (x := z.1) (y := z.2))
    (fun p hp q hq => hmax (p, q) (Finset.mem_product.mpr ⟨hp, hq⟩))

lemma no_separated_improvement {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    (f : ℝ² → ℝ²)
    (hsep : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist (f p) (f q)) :
    ¬ (∀ p ∈ A, ∀ q ∈ A, dist (f p) (f q) < diam (A : Set ℝ²)) := by
  classical
  intro hsmall
  let pairs := (A ×ˢ A).filter (fun z => z.1 ≠ z.2)
  obtain ⟨p0, hp0, q0, hq0, hpq0⟩ := hA.2
  have hpq0_ne : p0 ≠ q0 := by
    intro h; subst h; simp at hpq0
  have hpair : pairs.Nonempty :=
    ⟨(p0, q0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp0, hq0⟩, hpq0_ne⟩⟩
  obtain ⟨z, hz, hzmin⟩ :=
    Finset.exists_min_image pairs (fun w => dist (f w.1) (f w.2)) hpair
  have hz_mem := Finset.mem_filter.mp hz
  have hz1 : z.1 ∈ A := (Finset.mem_product.mp hz_mem.1).1
  have hz2 : z.2 ∈ A := (Finset.mem_product.mp hz_mem.1).2
  have hzne : z.1 ≠ z.2 := hz_mem.2
  let m : ℝ := dist (f z.1) (f z.2)
  have hm1 : 1 ≤ m := hsep z.1 hz1 z.2 hz2 hzne
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  let g : ℝ² → ℝ² := fun x => m⁻¹ • f x
  have hdist_g : ∀ x y, dist (g x) (g y) = m⁻¹ * dist (f x) (f y) := by
    intro x y
    change ‖m⁻¹ • f x - m⁻¹ • f y‖ = m⁻¹ * ‖f x - f y‖
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hm0.le)]
  have hg_inj : Set.InjOn g A := by
    intro x hx y hy hxy
    by_contra hne
    have h1 : 1 ≤ dist (f x) (f y) := hsep x hx y hy hne
    have h0 : dist (g x) (g y) = 0 := by rw [hxy, dist_self]
    rw [hdist_g] at h0
    have hpos : 0 < m⁻¹ * dist (f x) (f y) := mul_pos (inv_pos.mpr hm0) (lt_of_lt_of_le zero_lt_one h1)
    linarith
  let B : Finset ℝ² := A.image g
  have hBcard : B.card = A.card := Finset.card_image_of_injOn hg_inj
  have hBsep : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → dist u v ≥ 1 := by
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    have hxy : x ≠ y := fun h => huv (congrArg g h)
    rw [hdist_g]
    have hle : m ≤ dist (f x) (f y) :=
      hzmin (x, y) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩)
    have : m⁻¹ * m ≤ m⁻¹ * dist (f x) (f y) :=
      mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hm0.le)
    rwa [inv_mul_cancel₀ hm0.ne'] at this
  have hBmin : ∃ u ∈ B, ∃ v ∈ B, dist u v = 1 := by
    refine ⟨g z.1, Finset.mem_image_of_mem g hz1, g z.2, Finset.mem_image_of_mem g hz2, ?_⟩
    rw [hdist_g]
    exact inv_mul_cancel₀ hm0.ne'
  have hBmem : B ∈ {C : Finset ℝ² | C.card = A.card ∧ Erdos99.HasMinDist1 C} :=
    ⟨hBcard, hBsep, hBmin⟩
  have hdiam_le : diam (A : Set ℝ²) ≤ diam (B : Set ℝ²) := hmin hBmem
  have hBne : B.Nonempty := ⟨g z.1, Finset.mem_image_of_mem g hz1⟩
  obtain ⟨u, hu, v, hv, huv⟩ := exists_dist_eq_diam B hBne
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  have hlt : dist (g x) (g y) < diam (A : Set ℝ²) := by
    rw [hdist_g]
    have hinv : m⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm1
    have hle : m⁻¹ * dist (f x) (f y) ≤ 1 * dist (f x) (f y) :=
      mul_le_mul_of_nonneg_right hinv dist_nonneg
    linarith [hsmall x hx y hy]
  linarith

/- ### Part 2: Hexagonal-lattice packing upper bound -/

lemma hex_norm_sq (u v : ℝ) :
    ‖(WithLp.toLp 2 ![u + v / 2, Real.sqrt 3 / 2 * v] : ℝ²)‖ ^ 2 = u ^ 2 + u * v + v ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith only [h3]

lemma hex_int_quad_pos {u v : ℤ} (h : u ≠ 0 ∨ v ≠ 0) :
    (1 : ℝ) ≤ (u : ℝ) ^ 2 + (u : ℝ) * (v : ℝ) + (v : ℝ) ^ 2 := by
  have hint : (2 : ℤ) ≤ 2 * (u ^ 2 + u * v + v ^ 2) := by
    have hsq : 2 * (u ^ 2 + u * v + v ^ 2) = u ^ 2 + v ^ 2 + (u + v) ^ 2 := by ring
    rw [hsq]
    have hsq1 : ∀ x : ℤ, x ≠ 0 → (1 : ℤ) ≤ x ^ 2 := fun x hx => by
      rcases lt_or_gt_of_ne hx with hlt | hgt <;> nlinarith
    rcases h with hu | hv
    · have hu1 := hsq1 u hu
      by_cases hv0 : v = 0
      · subst hv0; nlinarith
      · have hv1 := hsq1 v hv0
        nlinarith [sq_nonneg (u + v)]
    · have hv1 := hsq1 v hv
      by_cases hu0 : u = 0
      · subst hu0; nlinarith
      · have hu1 := hsq1 u hu0
        nlinarith [sq_nonneg (u + v)]
  have h1 : (1 : ℤ) ≤ u ^ 2 + u * v + v ^ 2 := by omega
  exact_mod_cast h1

lemma hex_packing_exists (n : ℕ) (hn : 2 ≤ n) :
    ∃ B : Finset ℝ², B.card = n ∧ Erdos99.HasMinDist1 B ∧
      diam (B : Set ℝ²) ≤ 2 * ((Nat.sqrt (n / 3) : ℝ) + 1) := by
  classical
  let k : ℕ := Nat.sqrt (n / 3) + 1
  have hk1 : 1 ≤ k := Nat.succ_le_succ (Nat.zero_le _)
  have hk_sq : n ≤ 3 * k ^ 2 := by
    have hlt : n / 3 < k ^ 2 := by
      dsimp only [k]
      have := Nat.lt_succ_sqrt (n / 3)
      nlinarith
    omega
  let φ : ℤ × ℤ → ℝ² := fun z =>
    WithLp.toLp 2 ![(z.1 : ℝ) + (z.2 : ℝ) / 2, Real.sqrt 3 / 2 * (z.2 : ℝ)]
  have hdist_φ : ∀ z w : ℤ × ℤ,
      dist (φ z) (φ w) ^ 2 = ((z.1 - w.1 : ℤ) : ℝ) ^ 2 +
        ((z.1 - w.1 : ℤ) : ℝ) * ((z.2 - w.2 : ℤ) : ℝ) + ((z.2 - w.2 : ℤ) : ℝ) ^ 2 := by
    intro z w
    have hsub : φ z - φ w =
        WithLp.toLp 2 ![((z.1 - w.1 : ℤ) : ℝ) + ((z.2 - w.2 : ℤ) : ℝ) / 2,
          Real.sqrt 3 / 2 * ((z.2 - w.2 : ℤ) : ℝ)] := by
      ext i
      fin_cases i <;> simp [φ] <;> ring
    rw [dist_eq_norm, hsub, hex_norm_sq]
  have hφ_sep : ∀ z w : ℤ × ℤ, z ≠ w → 1 ≤ dist (φ z) (φ w) := by
    intro z w hne
    have hneq : z.1 - w.1 ≠ 0 ∨ z.2 - w.2 ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hne
      ext <;> omega
    have hsq : 1 ≤ dist (φ z) (φ w) ^ 2 := by
      rw [hdist_φ]
      exact hex_int_quad_pos hneq
    nlinarith [dist_nonneg (x := φ z) (y := φ w)]
  have hφ_inj : Function.Injective φ := by
    intro z w hzw
    by_contra hne
    have h1 := hφ_sep z w hne
    rw [hzw, dist_self] at h1
    linarith
  have hφ_norm : ∀ a b : ℕ, a ≤ k → b ≤ k →
      (a : ℝ) ^ 2 - (a : ℝ) * (b : ℝ) + (b : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
    intro a b ha hb
    have ha' : (a : ℝ) ≤ k := by exact_mod_cast ha
    have hb' : (b : ℝ) ≤ k := by exact_mod_cast hb
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    rcases le_total (a : ℝ) (b : ℝ) with hab | hba
    · nlinarith only [ha0, hb0, ha', hb', hab]
    · nlinarith only [ha0, hb0, ha', hb', hba]
  let idx : Finset (ℕ × ℕ) := (Finset.Icc 1 k) ×ˢ (Finset.range k)
  have hidx_card : idx.card = k ^ 2 := by
    simp [idx, sq]
  let S1 : Finset (ℤ × ℤ) := idx.image (fun p => ((p.1 : ℤ) - (p.2 : ℤ), (p.2 : ℤ)))
  let S2 : Finset (ℤ × ℤ) := idx.image (fun p => (-(p.1 : ℤ), (p.1 : ℤ) - (p.2 : ℤ)))
  let S3 : Finset (ℤ × ℤ) := idx.image (fun p => ((p.2 : ℤ), -(p.1 : ℤ)))
  have hS1_card : S1.card = k ^ 2 := by
    rw [← hidx_card]
    apply Finset.card_image_of_injective
    intro p q h
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  have hS2_card : S2.card = k ^ 2 := by
    rw [← hidx_card]
    apply Finset.card_image_of_injective
    intro p q h
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  have hS3_card : S3.card = k ^ 2 := by
    rw [← hidx_card]
    apply Finset.card_image_of_injective
    intro p q h
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  have hS12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp hz2
    have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
    have hq2 : q.2 < k := Finset.mem_range.mp (Finset.mem_product.mp hq).2
    simp only [Prod.mk.injEq] at hEq
    omega
  have hS13 : Disjoint S1 S3 := by
    rw [Finset.disjoint_left]
    intro z hz1 hz3
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp hz3
    have hq1 : 1 ≤ q.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hq).1).1
    simp only [Prod.mk.injEq] at hEq
    omega
  have hS23 : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]
    intro z hz2 hz3
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz2
    obtain ⟨q, _, hEq⟩ := Finset.mem_image.mp hz3
    have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
    simp only [Prod.mk.injEq] at hEq
    omega
  let H : Finset (ℤ × ℤ) := insert (0, 0) ((S1 ∪ S2) ∪ S3)
  have h0_not_mem : (0, 0) ∉ (S1 ∪ S2) ∪ S3 := by
    simp only [Finset.mem_union, not_or]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro h
      obtain ⟨p, hp, hEq⟩ := Finset.mem_image.mp h
      have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
      simp only [Prod.mk.injEq] at hEq; omega
    · intro h
      obtain ⟨p, hp, hEq⟩ := Finset.mem_image.mp h
      have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
      simp only [Prod.mk.injEq] at hEq; omega
    · intro h
      obtain ⟨p, hp, hEq⟩ := Finset.mem_image.mp h
      have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
      simp only [Prod.mk.injEq] at hEq; omega
  have hH_card : H.card = 3 * k ^ 2 + 1 := by
    rw [Finset.card_insert_of_notMem h0_not_mem,
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hS13, hS23⟩),
      Finset.card_union_of_disjoint hS12, hS1_card, hS2_card, hS3_card]
    ring
  have h0_mem : (0, 0) ∈ H := Finset.mem_insert_self _ _
  have h1_mem : (1, 0) ∈ H := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(1, 0),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hk1⟩, Finset.mem_range.mpr hk1⟩,
      by simp⟩
  have hH_norm : ∀ z ∈ H, ‖φ z‖ ≤ (k : ℝ) := by
    intro z hz
    have hsq : ‖φ z‖ ^ 2 ≤ (k : ℝ) ^ 2 := by
      have h0eq : ‖φ z‖ ^ 2 = (z.1 : ℝ) ^ 2 + (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2 := by
        simpa [φ] using hex_norm_sq (z.1 : ℝ) (z.2 : ℝ)
      rw [h0eq]
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · simp
      · rcases Finset.mem_union.mp hz' with hz12 | hz3
        · rcases Finset.mem_union.mp hz12 with hz1 | hz2
          · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz1
            have hp1 : p.1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).2
            have hp2 : p.2 ≤ k := (Finset.mem_range.mp (Finset.mem_product.mp hp).2).le
            have hring : (((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) ^ 2 +
                (((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * ((p.2 : ℤ) : ℝ) + ((p.2 : ℤ) : ℝ) ^ 2 =
                (p.1 : ℝ) ^ 2 - (p.1 : ℝ) * (p.2 : ℝ) + (p.2 : ℝ) ^ 2 := by push_cast; ring
            rw [hring]
            exact hφ_norm p.1 p.2 hp1 hp2
          · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz2
            have hp1 : p.1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).2
            have hp2 : p.2 ≤ k := (Finset.mem_range.mp (Finset.mem_product.mp hp).2).le
            have hring : ((-(p.1 : ℤ) : ℤ) : ℝ) ^ 2 +
                ((-(p.1 : ℤ) : ℤ) : ℝ) * (((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) +
                (((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) ^ 2 =
                (p.1 : ℝ) ^ 2 - (p.1 : ℝ) * (p.2 : ℝ) + (p.2 : ℝ) ^ 2 := by push_cast; ring
            rw [hring]
            exact hφ_norm p.1 p.2 hp1 hp2
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz3
          have hp1 : p.1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).2
          have hp2 : p.2 ≤ k := (Finset.mem_range.mp (Finset.mem_product.mp hp).2).le
          have hring : ((p.2 : ℤ) : ℝ) ^ 2 + ((p.2 : ℤ) : ℝ) * ((-(p.1 : ℤ) : ℤ) : ℝ) +
              ((-(p.1 : ℤ) : ℤ) : ℝ) ^ 2 =
              (p.1 : ℝ) ^ 2 - (p.1 : ℝ) * (p.2 : ℝ) + (p.2 : ℝ) ^ 2 := by push_cast; ring
          rw [hring]
          exact hφ_norm p.1 p.2 hp1 hp2
    nlinarith [norm_nonneg (φ z), Nat.cast_nonneg (α := ℝ) k]
  let rem : Finset (ℤ × ℤ) := (H.erase (0, 0)).erase (1, 0)
  have h1_in_erase : (1, 0) ∈ H.erase (0, 0) :=
    Finset.mem_erase.mpr ⟨by simp, h1_mem⟩
  have hrem_card : n - 2 ≤ rem.card := by
    have h1c : (H.erase (0, 0)).card = H.card - 1 := Finset.card_erase_of_mem h0_mem
    have h2c : rem.card = (H.erase (0, 0)).card - 1 := Finset.card_erase_of_mem h1_in_erase
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hrem_card
  have h0_not_T : (0, 0) ∉ T := fun h => by
    have := hTsub h
    simp [rem] at this
  have h1_not_T : (1, 0) ∉ T := fun h => by
    have := hTsub h
    simp [rem] at this
  let Z : Finset (ℤ × ℤ) := insert (0, 0) (insert (1, 0) T)
  have hZcard : Z.card = n := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem h1_not_T, hTcard]
    · omega
    · simp [h0_not_T]
  have hZsub : Z ⊆ H := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact h0_mem
    · rcases Finset.mem_insert.mp hz' with rfl | hz''
      · exact h1_mem
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hTsub hz''))
  let B : Finset ℝ² := Z.image φ
  refine ⟨B, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injective _ hφ_inj, hZcard]
  · intro p hp q hq hpq
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
    exact hφ_sep z w (fun h => hpq (congrArg φ h))
  · refine ⟨φ (0, 0), Finset.mem_image_of_mem φ (Finset.mem_insert_self _ _),
      φ (1, 0), Finset.mem_image_of_mem φ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩
    have hsq : dist (φ (0, 0)) (φ (1, 0)) ^ 2 = 1 := by
      rw [hdist_φ]; norm_num
    nlinarith [dist_nonneg (x := φ (0, 0)) (y := φ (1, 0))]
  · have hcast : 2 * ((Nat.sqrt (n / 3) : ℝ) + 1) = 2 * (k : ℝ) := by
      dsimp only [k]; push_cast; ring
    rw [hcast]
    apply diam_le_of_forall_dist_le (by positivity)
    intro p hp q hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    calc dist (φ z) (φ w)
        ≤ dist (φ z) 0 + dist 0 (φ w) := dist_triangle _ _ _
      _ = ‖φ z‖ + ‖φ w‖ := by simp [dist_zero_right, dist_zero_left]
      _ ≤ (k : ℝ) + (k : ℝ) := add_le_add (hH_norm z (hZsub hz)) (hH_norm w (hZsub hw))
      _ = 2 * (k : ℝ) := by ring

/- ### Part 3: Disk-packing area lower bound -/

lemma disk_packing_lower_bound (A : Finset ℝ²) (hAne : A.Nonempty)
    (hsep : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) :
    Real.pi * (A.card : ℝ) ≤ 4 * (diam (A : Set ℝ²) + 1) ^ 2 := by
  classical
  let D : ℝ := diam (A : Set ℝ²)
  have hD0 : 0 ≤ D := diam_nonneg
  obtain ⟨px, hpx, hxmin⟩ := Finset.exists_min_image A (fun p : ℝ² => p 0) hAne
  obtain ⟨py, hpy, hymin⟩ := Finset.exists_min_image A (fun p : ℝ² => p 1) hAne
  let a : Fin 2 → ℝ := ![px 0 - 1 / 2, py 1 - 1 / 2]
  let b : Fin 2 → ℝ := ![px 0 + D + 1 / 2, py 1 + D + 1 / 2]
  let box : Set ℝ² := WithLp.ofLp ⁻¹' (Set.univ.pi fun i => Set.Icc (a i) (b i))
  have hsub : (⋃ p ∈ A, Metric.ball p (1 / 2)) ⊆ box := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    have hzd : dist z p < 1 / 2 := Metric.mem_ball.mp hzp
    have hcoord : ∀ i : Fin 2, |z i - p i| ≤ dist z p := fun i => by
      simpa [dist_eq_norm] using PiLp.norm_apply_le (z - p) i
    simp only [box, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Icc]
    intro i
    fin_cases i
    · have h0l : px 0 ≤ p 0 := hxmin p hp
      have h0u : p 0 - px 0 ≤ D := by
        have h1 : |p 0 - px 0| ≤ dist p px := by
          simpa [dist_eq_norm] using PiLp.norm_apply_le (p - px) 0
        have h2 : dist p px ≤ D := dist_le_diam_of_mem A.finite_toSet.isBounded hp hpx
        linarith [(le_abs_self (p 0 - px 0)).trans (h1.trans h2)]
      have hc0 := abs_le.mp ((hcoord 0).trans hzd.le)
      change px 0 - 1 / 2 ≤ z 0 ∧ z 0 ≤ px 0 + D + 1 / 2
      constructor <;> linarith
    · have h1l : py 1 ≤ p 1 := hymin p hp
      have h1u : p 1 - py 1 ≤ D := by
        have h1 : |p 1 - py 1| ≤ dist p py := by
          simpa [dist_eq_norm] using PiLp.norm_apply_le (p - py) 1
        have h2 : dist p py ≤ D := dist_le_diam_of_mem A.finite_toSet.isBounded hp hpy
        linarith [(le_abs_self (p 1 - py 1)).trans (h1.trans h2)]
      have hc1 := abs_le.mp ((hcoord 1).trans hzd.le)
      change py 1 - 1 / 2 ≤ z 1 ∧ z 1 ≤ py 1 + D + 1 / 2
      constructor <;> linarith
  have hdisj : (A : Set ℝ²).PairwiseDisjoint (fun p => Metric.ball p (1 / 2)) := by
    intro p hp q hq hpq
    apply Metric.ball_disjoint_ball
    have h1 : 1 ≤ dist p q := hsep p hp q hq hpq
    linarith
  have hvol_union : volume (⋃ p ∈ A, Metric.ball p (1 / 2)) =
      ENNReal.ofReal (Real.pi * (A.card : ℝ) / 4) := by
    rw [MeasureTheory.measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
    have hball : ∀ p : ℝ², volume (Metric.ball p (1 / 2)) = ENNReal.ofReal (Real.pi / 4) := by
      intro p
      rw [EuclideanSpace.volume_ball]
      simp only [Fintype.card_fin, Nat.cast_ofNat]
      have hsqpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
      have hgam : Real.Gamma ((2 : ℝ) / 2 + 1) = 1 := by
        have : (2 : ℝ) / 2 + 1 = 2 := by norm_num
        rw [this, Real.Gamma_two]
      rw [hsqpi, hgam, div_one, ← ENNReal.ofReal_pow (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    simp only [hball, Finset.sum_const, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1; ring
  have hvol_box : volume box = ENNReal.ofReal ((D + 1) ^ 2) := by
    have hmeas : MeasurableSet (Set.univ.pi fun i => Set.Icc (a i) (b i)) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Icc
    dsimp only [box]
    rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage hmeas.nullMeasurableSet]
    rw [show (volume : Measure (Fin 2 → ℝ)) = Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ)) from rfl,
      Measure.pi_pi]
    simp only [Real.volume_Icc, Fin.prod_univ_two, a, b, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 : px 0 + D + 1 / 2 - (px 0 - 1 / 2) = D + 1 := by ring
    have h1 : py 1 + D + 1 / 2 - (py 1 - 1 / 2) = D + 1 := by ring
    rw [h0, h1, ← ENNReal.ofReal_mul (by linarith)]
    congr 1; ring
  have hle : ENNReal.ofReal (Real.pi * (A.card : ℝ) / 4) ≤ ENNReal.ofReal ((D + 1) ^ 2) := by
    rw [← hvol_union, ← hvol_box]
    exact measure_mono hsub
  have hreal := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg (D + 1))).mp hle
  linarith

/- ### Part 4: Unit-distance degree at most 5 (triangle-free) -/

lemma unit_inner_of_arg_diff {u v : ℝ²} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {zu zv : ℂ} (hzu : zu = ⟨u 0, u 1⟩) (hzv : zv = ⟨v 0, v 1⟩) :
    ⟪u, v⟫_ℝ = Real.cos (zu.arg - zv.arg) := by
  have hzun : ‖zu‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, hzu]
    have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
      have := congrArg (· ^ 2) hu
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
      simpa [Real.norm_eq_abs, sq_abs] using this
    rw [hu2, Real.sqrt_one]
  have hzvn : ‖zv‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, hzv]
    have hv2 : v 0 ^ 2 + v 1 ^ 2 = 1 := by
      have := congrArg (· ^ 2) hv
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
      simpa [Real.norm_eq_abs, sq_abs] using this
    rw [hv2, Real.sqrt_one]
  have hzu0 : zu ≠ 0 := by intro h; rw [h, norm_zero] at hzun; norm_num at hzun
  have hzv0 : zv ≠ 0 := by intro h; rw [h, norm_zero] at hzvn; norm_num at hzvn
  have hc1 : Real.cos zu.arg = u 0 := by
    rw [Complex.cos_arg hzu0, hzun, div_one, hzu]
  have hs1 : Real.sin zu.arg = u 1 := by
    rw [Complex.sin_arg, hzun, div_one, hzu]
  have hc2 : Real.cos zv.arg = v 0 := by
    rw [Complex.cos_arg hzv0, hzvn, div_one, hzv]
  have hs2 : Real.sin zv.arg = v 1 := by
    rw [Complex.sin_arg, hzvn, div_one, hzv]
  rw [Real.cos_sub, hc1, hc2, hs1, hs2, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two, mul_comm]

lemma unit_degree_le_five (A : Finset ℝ²)
    (hsep : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q)
    (htri : ¬ ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, Erdos99.FormsEquilateralTriangle p q r)
    (p : ℝ²) (hp : p ∈ A) :
    (A.filter (fun q => dist p q = 1)).card ≤ 5 := by
  classical
  let N : Finset ℝ² := A.filter (fun q => dist p q = 1)
  by_contra hgt
  have h6 : 6 ≤ N.card := by dsimp only [N] at hgt ⊢; omega
  let ang : ℝ² → ℝ := fun q => (⟨(q - p) 0, (q - p) 1⟩ : ℂ).arg
  have hclose : ∀ q ∈ N, ∀ r ∈ N, q ≠ r →
      ¬ (|ang q - ang r| ≤ Real.pi / 3 ∨ |ang q - ang r - 2 * Real.pi| ≤ Real.pi / 3 ∨
        |ang r - ang q - 2 * Real.pi| ≤ Real.pi / 3) := by
    intro q hq r hr hqr hgap
    have hqA : q ∈ A := (Finset.mem_filter.mp hq).1
    have hrA : r ∈ A := (Finset.mem_filter.mp hr).1
    have hqd : dist p q = 1 := (Finset.mem_filter.mp hq).2
    have hrd : dist p r = 1 := (Finset.mem_filter.mp hr).2
    have hqn : ‖q - p‖ = 1 := by rw [← dist_eq_norm, dist_comm, hqd]
    have hrn : ‖r - p‖ = 1 := by rw [← dist_eq_norm, dist_comm, hrd]
    have hinner : ⟪q - p, r - p⟫_ℝ = Real.cos (ang q - ang r) :=
      unit_inner_of_arg_diff hqn hrn rfl rfl
    have hcos_ge : (1 : ℝ) / 2 ≤ Real.cos (ang q - ang r) := by
      have hpi3 : Real.pi / 3 ≤ Real.pi := by linarith [Real.pi_pos]
      rcases hgap with h1 | h2 | h3
      · rw [← Real.cos_abs (ang q - ang r), ← Real.cos_pi_div_three]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi3 h1
      · have heq : Real.cos (ang q - ang r) = Real.cos (ang q - ang r - 2 * Real.pi) := by
          rw [Real.cos_sub_two_pi]
        rw [heq, ← Real.cos_abs, ← Real.cos_pi_div_three]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi3 h2
      · have heq : Real.cos (ang q - ang r) = Real.cos (ang r - ang q - 2 * Real.pi) := by
          rw [Real.cos_sub_two_pi, ← Real.cos_neg]; congr 1; ring
        rw [heq, ← Real.cos_abs, ← Real.cos_pi_div_three]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi3 h3
    have hdle : dist q r ≤ 1 := by
      have hsq : dist q r ^ 2 ≤ 1 := by
        have hsub : q - r = (q - p) - (r - p) := by abel
        rw [dist_eq_norm, hsub, norm_sub_sq_real, hqn, hrn, hinner]
        linarith
      nlinarith [dist_nonneg (x := q) (y := r)]
    have hdge : 1 ≤ dist q r := hsep q hqA r hrA hqr
    have hdeq : dist q r = 1 := le_antisymm hdle hdge
    exact htri ⟨p, hp, q, hqA, r, hrA, hqd, hdeq, hrd⟩
  have hang_inj : Set.InjOn ang N := by
    intro q hq r hr heq
    by_contra hne
    exact hclose q hq r hr hne (Or.inl (by rw [heq, sub_self, abs_zero]; positivity))
  let θs : Finset ℝ := N.image ang
  have hθcard : 6 ≤ θs.card := by
    rwa [Finset.card_image_of_injOn hang_inj]
  let L : List ℝ := θs.sort (· ≤ ·)
  have hLlen : 6 ≤ L.length := by
    simpa [L, Finset.length_sort] using hθcard
  have hLle : L.Pairwise (· ≤ ·) := θs.pairwise_sort (· ≤ ·)
  have hLnodup : L.Nodup := θs.sort_nodup (· ≤ ·)
  have hLmem : ∀ i : Fin 6, L[i.val]'(lt_of_lt_of_le i.isLt hLlen) ∈ θs := fun i =>
    (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem _)
  have hLlt : ∀ (i j : Fin 6), i < j →
      L[i.val]'(lt_of_lt_of_le i.isLt hLlen) < L[j.val]'(lt_of_lt_of_le j.isLt hLlen) := by
    intro i j hij
    have hi : i.val < L.length := lt_of_lt_of_le i.isLt hLlen
    have hj : j.val < L.length := lt_of_lt_of_le j.isLt hLlen
    have hle' : L[i.val]'hi ≤ L[j.val]'hj := List.pairwise_iff_getElem.mp hLle i.val j.val hi hj hij
    have hne' : L[i.val]'hi ≠ L[j.val]'hj := fun heq => by
      have hinj := List.nodup_iff_injective_getElem.mp hLnodup
      have := hinj (a₁ := ⟨i.val, hi⟩) (a₂ := ⟨j.val, hj⟩) heq
      have hval : i.val = j.val := congrArg (fun t : Fin L.length => t.val) this
      omega
    exact lt_of_le_of_ne hle' hne'
  let x : Fin 6 → ℝ := fun i => L[i.val]'(lt_of_lt_of_le i.isLt hLlen)
  have hx_gap : ∀ (i j : Fin 6), i < j → Real.pi / 3 < x j - x i := by
    intro i j hij
    obtain ⟨q, hq, hxq⟩ := Finset.mem_image.mp (hLmem i)
    obtain ⟨r, hr, hxr⟩ := Finset.mem_image.mp (hLmem j)
    have hxi : ang q = x i := hxq
    have hxj : ang r = x j := hxr
    have hne : q ≠ r := fun h => by
      have hlt : x i < x j := hLlt i j hij
      rw [← hxi, ← hxj, h] at hlt
      exact lt_irrefl _ hlt
    have hnot := hclose r hr q hq hne.symm
    push Not at hnot
    have hpos : 0 < x j - x i := sub_pos.mpr (hLlt i j hij)
    have h1 := hnot.1
    rw [hxj, hxi, abs_of_pos hpos] at h1
    exact h1
  have hwrap : Real.pi / 3 < (x 0 + 2 * Real.pi) - x 5 := by
    obtain ⟨q, hq, hxq⟩ := Finset.mem_image.mp (hLmem 0)
    obtain ⟨r, hr, hxr⟩ := Finset.mem_image.mp (hLmem 5)
    have hx0 : ang q = x 0 := hxq
    have hx5 : ang r = x 5 := hxr
    have hne : q ≠ r := fun h => by
      have hlt : x 0 < x 5 := hLlt 0 5 (by decide)
      rw [← hx0, ← hx5, h] at hlt
      exact lt_irrefl _ hlt
    have hnot := hclose r hr q hq hne.symm
    push Not at hnot
    have hbd0 : -Real.pi < x 0 ∧ x 0 ≤ Real.pi := by
      rw [← hx0]; exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
    have hbd5 : -Real.pi < x 5 ∧ x 5 ≤ Real.pi := by
      rw [← hx5]; exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
    have hneg : x 5 - x 0 - 2 * Real.pi < 0 := by linarith
    have h2 := hnot.2.1
    rw [hx5, hx0, abs_of_neg hneg] at h2
    linarith
  have g0 := hx_gap 0 1 (by decide)
  have g1 := hx_gap 1 2 (by decide)
  have g2 := hx_gap 2 3 (by decide)
  have g3 := hx_gap 3 4 (by decide)
  have g4 := hx_gap 4 5 (by decide)
  linarith

/- ### Part 5: Geometric planarity (non-crossing unit segments) -/

lemma dist_add_dist_of_mem_segment {p q x : ℝ²} (hx : x ∈ segment ℝ p q) :
    dist p x + dist x q = dist p q := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  have h1 : p - (a • p + b • q) = b • (p - q) := by
    calc p - (a • p + b • q) = (a + b) • p - (a • p + b • q) := by rw [hab, one_smul]
      _ = b • (p - q) := by rw [add_smul, smul_sub]; abel
  have h2 : (a • p + b • q) - q = a • (p - q) := by
    calc (a • p + b • q) - q = (a • p + b • q) - (a + b) • q := by rw [hab, one_smul]
      _ = a • (p - q) := by rw [add_smul, smul_sub]; abel
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, h1, h2,
    norm_smul, norm_smul, Real.norm_of_nonneg hb, Real.norm_of_nonneg ha]
  calc b * ‖p - q‖ + a * ‖p - q‖ = (a + b) * ‖p - q‖ := by ring
    _ = ‖p - q‖ := by rw [hab, one_mul]

lemma unit_segments_disjoint (A : Finset ℝ²)
    (hsep : ∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q)
    (htri : ¬ ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, Erdos99.FormsEquilateralTriangle p q r)
    {p q r s : ℝ²} (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A) (hs : s ∈ A)
    (hpq : dist p q = 1) (hrs : dist r s = 1)
    (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) :
    Disjoint (segment ℝ p q) (segment ℝ r s) := by
  rw [Set.disjoint_left]
  intro x hxpq hxrs
  have h1 : dist p x + dist x q = 1 := by rw [dist_add_dist_of_mem_segment hxpq, hpq]
  have h2 : dist r x + dist x s = 1 := by rw [dist_add_dist_of_mem_segment hxrs, hrs]
  have dpr_ge : 1 ≤ dist p r := hsep p hp r hr hpr
  have dps_ge : 1 ≤ dist p s := hsep p hp s hs hps
  have dqr_ge : 1 ≤ dist q r := hsep q hq r hr hqr
  have dqs_ge : 1 ≤ dist q s := hsep q hq s hs hqs
  have dpr_le : dist p r ≤ dist p x + dist x r := dist_triangle p x r
  have dps_le : dist p s ≤ dist p x + dist x s := dist_triangle p x s
  have dqr_le : dist q r ≤ dist q x + dist x r := dist_triangle q x r
  have dqs_le : dist q s ≤ dist q x + dist x s := dist_triangle q x s
  have hpr_eq : dist p r = 1 := by
    rw [dist_comm x r] at dpr_le
    rw [dist_comm q x] at dqs_le
    linarith
  have hps_eq : dist p s = 1 := by
    rw [dist_comm x r, dist_comm q x] at dqr_le
    linarith
  exact htri ⟨p, hp, r, hr, s, hs, hpr_eq, hrs, hps_eq⟩

/- ### Part 6: Hopf-Pannwitz diametral pair bound (at most n unordered pairs) -/

lemma hopf_middle_unique_neighbor {D : ℝ} (hD : 0 < D) {p y x z w : ℝ²}
    (hyp : dist y p = D) (hxp : dist x p = D) (hzp : dist z p = D) (hwy : dist w y = D)
    (hwx : dist w x ≤ D) (hwz : dist w z ≤ D)
    (hxy : x ≠ y) (hzy : z ≠ y)
    (hs1 : 0 < (y - p) 0 * (x - p) 1 - (y - p) 1 * (x - p) 0)
    (hs2 : 0 < (z - p) 0 * (y - p) 1 - (z - p) 1 * (y - p) 0) :
    w = p := by
  let a : ℝ := (y - p) 0
  let b : ℝ := (y - p) 1
  have hab : a ^ 2 + b ^ 2 = D ^ 2 := by
    have := congrArg (· ^ 2) hyp
    rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
    simpa [a, b, Real.norm_eq_abs, sq_abs] using this
  let x0 : ℝ := (x - p) 0
  let x1 : ℝ := (x - p) 1
  have hxab : x0 ^ 2 + x1 ^ 2 = D ^ 2 := by
    have := congrArg (· ^ 2) hxp
    rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
    simpa [x0, x1, Real.norm_eq_abs, sq_abs] using this
  let z0 : ℝ := (z - p) 0
  let z1 : ℝ := (z - p) 1
  have hzab : z0 ^ 2 + z1 ^ 2 = D ^ 2 := by
    have := congrArg (· ^ 2) hzp
    rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
    simpa [z0, z1, Real.norm_eq_abs, sq_abs] using this
  let w0 : ℝ := (w - p) 0
  let w1 : ℝ := (w - p) 1
  have hwy2 : (w0 - a) ^ 2 + (w1 - b) ^ 2 = D ^ 2 := by
    have hsub : w - y = (w - p) - (y - p) := by abel
    have := congrArg (· ^ 2) hwy
    rw [dist_eq_norm, hsub, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
    simpa [w0, w1, a, b, Real.norm_eq_abs, sq_abs] using this
  have hwx2 : (w0 - x0) ^ 2 + (w1 - x1) ^ 2 ≤ D ^ 2 := by
    have hsub : w - x = (w - p) - (x - p) := by abel
    have hsq : dist w x ^ 2 ≤ D ^ 2 := sq_le_sq' (by linarith [dist_nonneg (x := w) (y := x)]) hwx
    rw [dist_eq_norm, hsub, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at hsq
    simpa [w0, w1, x0, x1, Real.norm_eq_abs, sq_abs] using hsq
  have hwz2 : (w0 - z0) ^ 2 + (w1 - z1) ^ 2 ≤ D ^ 2 := by
    have hsub : w - z = (w - p) - (z - p) := by abel
    have hsq : dist w z ^ 2 ≤ D ^ 2 := sq_le_sq' (by linarith [dist_nonneg (x := w) (y := z)]) hwz
    rw [dist_eq_norm, hsub, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at hsq
    simpa [w0, w1, z0, z1, Real.norm_eq_abs, sq_abs] using hsq
  let u : ℝ := a * w0 + b * w1
  let v : ℝ := a * w1 - b * w0
  let c1 : ℝ := a * x0 + b * x1
  let s1 : ℝ := a * x1 - b * x0
  let c2 : ℝ := a * z0 + b * z1
  let s2 : ℝ := b * z0 - a * z1
  have hs1' : 0 < s1 := hs1
  have hs2' : 0 < s2 := by
    change 0 < (z - p) 0 * (y - p) 1 - (z - p) 1 * (y - p) 0 at hs2
    dsimp only [s2, a, b, z0, z1]; linarith
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
  have hxy_pos : 0 < D ^ 2 - c1 := by
    have hne : (x0 - a) ^ 2 + (x1 - b) ^ 2 > 0 := by
      by_contra hle
      have h0 : x0 = a ∧ x1 = b := by nlinarith [sq_nonneg (x0 - a), sq_nonneg (x1 - b)]
      apply hxy
      ext i; fin_cases i
      · change x 0 = y 0; dsimp only [x0, a] at h0; simp at h0; linarith
      · change x 1 = y 1; dsimp only [x1, b] at h0; simp at h0; linarith
    nlinarith only [hab, hxab, hne, show c1 = a * x0 + b * x1 from rfl]
  have hzy_pos : 0 < D ^ 2 - c2 := by
    have hne : (z0 - a) ^ 2 + (z1 - b) ^ 2 > 0 := by
      by_contra hle
      have h0 : z0 = a ∧ z1 = b := by nlinarith [sq_nonneg (z0 - a), sq_nonneg (z1 - b)]
      apply hzy
      ext i; fin_cases i
      · change z 0 = y 0; dsimp only [z0, a] at h0; simp at h0; linarith
      · change z 1 = y 1; dsimp only [z1, b] at h0; simp at h0; linarith
    nlinarith only [hab, hzab, hne, show c2 = a * z0 + b * z1 from rfl]
  have h_wsq : w0 ^ 2 + w1 ^ 2 = 2 * u := by
    have : (w0 - a) ^ 2 + (w1 - b) ^ 2 = w0 ^ 2 + w1 ^ 2 - 2 * u + (a ^ 2 + b ^ 2) := by
      dsimp only [u]; ring
    linarith
  have h_dot1 : D ^ 2 * (x0 * w0 + x1 * w1) = c1 * u + s1 * v := by
    dsimp only [c1, s1, u, v]
    linear_combination -(x0 * w0 + x1 * w1) * hab
  have h_dot2 : D ^ 2 * (z0 * w0 + z1 * w1) = c2 * u - s2 * v := by
    dsimp only [c2, s2, u, v]
    linear_combination -(z0 * w0 + z1 * w1) * hab
  have hineq1 : u * (D ^ 2 - c1) ≤ v * s1 := by
    have h1 : w0 ^ 2 + w1 ^ 2 ≤ 2 * (x0 * w0 + x1 * w1) := by
      nlinarith only [hwx2, hxab]
    have h2 : 2 * u * D ^ 2 ≤ 2 * (D ^ 2 * (x0 * w0 + x1 * w1)) := by
      rw [← h_wsq]; nlinarith only [h1, hD2]
    nlinarith only [h2, h_dot1]
  have hineq2 : u * (D ^ 2 - c2) ≤ -(v * s2) := by
    have h1 : w0 ^ 2 + w1 ^ 2 ≤ 2 * (z0 * w0 + z1 * w1) := by
      nlinarith only [hwz2, hzab]
    have h2 : 2 * u * D ^ 2 ≤ 2 * (D ^ 2 * (z0 * w0 + z1 * w1)) := by
      rw [← h_wsq]; nlinarith only [h1, hD2]
    nlinarith only [h2, h_dot2]
  have hcomb : u * ((D ^ 2 - c1) * s2 + (D ^ 2 - c2) * s1) ≤ 0 := by
    have h1 := mul_le_mul_of_nonneg_right hineq1 hs2'.le
    have h2 := mul_le_mul_of_nonneg_right hineq2 hs1'.le
    linarith
  have hcoef : 0 < (D ^ 2 - c1) * s2 + (D ^ 2 - c2) * s1 := by positivity
  have hu0 : u ≤ 0 := by nlinarith only [hcomb, hcoef]
  have hw0 : w0 = 0 := by nlinarith only [h_wsq, hu0, sq_nonneg w0, sq_nonneg w1]
  have hw1 : w1 = 0 := by nlinarith only [h_wsq, hu0, sq_nonneg w0, sq_nonneg w1]
  ext i; fin_cases i
  · have h0 : w 0 - p 0 = 0 := by simpa [w0, PiLp.sub_apply] using hw0
    change w 0 = p 0; linarith
  · have h1 : w 1 - p 1 = 0 := by simpa [w1, PiLp.sub_apply] using hw1
    change w 1 = p 1; linarith

lemma exists_middle_of_three_on_circle {D : ℝ} (hD : 0 < D) {p a b c : ℝ²}
    (ha : dist a p = D) (hb : dist b p = D) (hc : dist c p = D)
    (hab : dist a b ≤ D) (hbc : dist b c ≤ D) (hac : dist a c ≤ D)
    (h1 : a ≠ b) (h2 : b ≠ c) (h3 : a ≠ c) :
    ∃ x y z : ℝ²,
      (x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c) ∧ (z = a ∨ z = b ∨ z = c) ∧
      x ≠ y ∧ z ≠ y ∧
      0 < (y - p) 0 * (x - p) 1 - (y - p) 1 * (x - p) 0 ∧
      0 < (z - p) 0 * (y - p) 1 - (z - p) 1 * (y - p) 0 := by
  have hdet_ne : ∀ u v : ℝ², dist u p = D → dist v p = D → dist u v ≤ D → u ≠ v →
      (u - p) 0 * (v - p) 1 - (u - p) 1 * (v - p) 0 ≠ 0 := by
    intro u v hu hv huv hne hdet
    have hu2 : (u - p) 0 ^ 2 + (u - p) 1 ^ 2 = D ^ 2 := by
      have := congrArg (· ^ 2) hu
      rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
      simpa [Real.norm_eq_abs, sq_abs] using this
    have hv2 : (v - p) 0 ^ 2 + (v - p) 1 ^ 2 = D ^ 2 := by
      have := congrArg (· ^ 2) hv
      rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
      simpa [Real.norm_eq_abs, sq_abs] using this
    have huv2 : ((u - p) 0 - (v - p) 0) ^ 2 + ((u - p) 1 - (v - p) 1) ^ 2 ≤ D ^ 2 := by
      have hsub : u - v = (u - p) - (v - p) := by abel
      have hsq : dist u v ^ 2 ≤ D ^ 2 := sq_le_sq' (by linarith [dist_nonneg (x := u) (y := v)]) huv
      rw [dist_eq_norm, hsub, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at hsq
      simpa [Real.norm_eq_abs, sq_abs] using hsq
    have hdot_sq : ((u - p) 0 * (v - p) 0 + (u - p) 1 * (v - p) 1) ^ 2 = D ^ 4 := by
      nlinarith only [hu2, hv2, hdet]
    have hdot_ge : D ^ 2 ≤ 2 * ((u - p) 0 * (v - p) 0 + (u - p) 1 * (v - p) 1) := by
      nlinarith only [hu2, hv2, huv2]
    have hdot_eq : (u - p) 0 * (v - p) 0 + (u - p) 1 * (v - p) 1 = D ^ 2 := by
      nlinarith only [hdot_sq, hdot_ge, hD]
    have hzero : ((u - p) 0 - (v - p) 0) ^ 2 + ((u - p) 1 - (v - p) 1) ^ 2 = 0 := by
      nlinarith only [hu2, hv2, hdot_eq]
    apply hne
    ext i; fin_cases i
    · have h0 : (u - p) 0 = (v - p) 0 := by nlinarith [sq_nonneg ((u - p) 1 - (v - p) 1)]
      have h0' : u 0 - p 0 = v 0 - p 0 := by simpa [PiLp.sub_apply] using h0
      change u 0 = v 0; linarith
    · have h1 : (u - p) 1 = (v - p) 1 := by nlinarith [sq_nonneg ((u - p) 0 - (v - p) 0)]
      have h1' : u 1 - p 1 = v 1 - p 1 := by simpa [PiLp.sub_apply] using h1
      change u 1 = v 1; linarith
  have hcyc : ∀ u v w : ℝ², dist u p = D → dist v p = D → dist w p = D →
      dist u v ≤ D → dist v w ≤ D → dist u w ≤ D →
      0 < (u - p) 0 * (v - p) 1 - (u - p) 1 * (v - p) 0 →
      0 < (v - p) 0 * (w - p) 1 - (v - p) 1 * (w - p) 0 →
      0 < (w - p) 0 * (u - p) 1 - (w - p) 1 * (u - p) 0 → False := by
    intro u v w hu hv hw huv hvw huw d1 d2 d3
    have hsum : ∀ x y : ℝ², dist x p = D → dist y p = D → dist x y ≤ D →
        D ^ 2 ≤ 2 * ((x - p) 0 * (y - p) 0 + (x - p) 1 * (y - p) 1) := by
      intro x y hx hy hxy
      have hx2 : (x - p) 0 ^ 2 + (x - p) 1 ^ 2 = D ^ 2 := by
        have := congrArg (· ^ 2) hx
        rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
        simpa [Real.norm_eq_abs, sq_abs] using this
      have hy2 : (y - p) 0 ^ 2 + (y - p) 1 ^ 2 = D ^ 2 := by
        have := congrArg (· ^ 2) hy
        rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
        simpa [Real.norm_eq_abs, sq_abs] using this
      have hxy2 : ((x - p) 0 - (y - p) 0) ^ 2 + ((x - p) 1 - (y - p) 1) ^ 2 ≤ D ^ 2 := by
        have hsub : x - y = (x - p) - (y - p) := by abel
        have hsq : dist x y ^ 2 ≤ D ^ 2 := sq_le_sq' (by linarith [dist_nonneg (x := x) (y := y)]) hxy
        rw [dist_eq_norm, hsub, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at hsq
        simpa [Real.norm_eq_abs, sq_abs] using hsq
      nlinarith only [hx2, hy2, hxy2]
    have hduv := hsum u v hu hv huv
    have hdvw := hsum v w hv hw hvw
    have hdwu := hsum w u hw hu (by rwa [dist_comm])
    let s1 : ℝ := (u - p) 0 * (v - p) 1 - (u - p) 1 * (v - p) 0
    let s2 : ℝ := (v - p) 0 * (w - p) 1 - (v - p) 1 * (w - p) 0
    let s3 : ℝ := (w - p) 0 * (u - p) 1 - (w - p) 1 * (u - p) 0
    have h0 : s2 * (u - p) 0 + s3 * (v - p) 0 + s1 * (w - p) 0 = 0 := by
      dsimp only [s1, s2, s3]; ring
    have h1' : s2 * (u - p) 1 + s3 * (v - p) 1 + s1 * (w - p) 1 = 0 := by
      dsimp only [s1, s2, s3]; ring
    have hnorm0 : (s2 * (u - p) 0 + s3 * (v - p) 0 + s1 * (w - p) 0) ^ 2 +
        (s2 * (u - p) 1 + s3 * (v - p) 1 + s1 * (w - p) 1) ^ 2 = 0 := by
      rw [h0, h1']; norm_num
    have hu2 : (u - p) 0 ^ 2 + (u - p) 1 ^ 2 = D ^ 2 := by
      have := congrArg (· ^ 2) hu
      rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
      simpa [Real.norm_eq_abs, sq_abs] using this
    have hv2 : (v - p) 0 ^ 2 + (v - p) 1 ^ 2 = D ^ 2 := by
      have := congrArg (· ^ 2) hv
      rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
      simpa [Real.norm_eq_abs, sq_abs] using this
    have hw2 : (w - p) 0 ^ 2 + (w - p) 1 ^ 2 = D ^ 2 := by
      have := congrArg (· ^ 2) hw
      rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two] at this
      simpa [Real.norm_eq_abs, sq_abs] using this
    have hexp : (s2 * (u - p) 0 + s3 * (v - p) 0 + s1 * (w - p) 0) ^ 2 +
        (s2 * (u - p) 1 + s3 * (v - p) 1 + s1 * (w - p) 1) ^ 2 =
        s2 ^ 2 * ((u - p) 0 ^ 2 + (u - p) 1 ^ 2) +
        s3 ^ 2 * ((v - p) 0 ^ 2 + (v - p) 1 ^ 2) +
        s1 ^ 2 * ((w - p) 0 ^ 2 + (w - p) 1 ^ 2) +
        s2 * s3 * (2 * ((u - p) 0 * (v - p) 0 + (u - p) 1 * (v - p) 1)) +
        s3 * s1 * (2 * ((v - p) 0 * (w - p) 0 + (v - p) 1 * (w - p) 1)) +
        s1 * s2 * (2 * ((w - p) 0 * (u - p) 0 + (w - p) 1 * (u - p) 1)) := by ring
    rw [hnorm0, hu2, hv2, hw2] at hexp
    have hpos_rhs : 0 < s2 ^ 2 * D ^ 2 + s3 ^ 2 * D ^ 2 + s1 ^ 2 * D ^ 2 +
        s2 * s3 * D ^ 2 + s3 * s1 * D ^ 2 + s1 * s2 * D ^ 2 := by positivity
    have hle_rhs : s2 ^ 2 * D ^ 2 + s3 ^ 2 * D ^ 2 + s1 ^ 2 * D ^ 2 +
        s2 * s3 * D ^ 2 + s3 * s1 * D ^ 2 + s1 * s2 * D ^ 2 ≤ 0 := by
      have h1m : s2 * s3 * D ^ 2 ≤ s2 * s3 * (2 * ((u - p) 0 * (v - p) 0 + (u - p) 1 * (v - p) 1)) :=
        mul_le_mul_of_nonneg_left hduv (by positivity)
      have h2m : s3 * s1 * D ^ 2 ≤ s3 * s1 * (2 * ((v - p) 0 * (w - p) 0 + (v - p) 1 * (w - p) 1)) :=
        mul_le_mul_of_nonneg_left hdvw (by positivity)
      have h3m : s1 * s2 * D ^ 2 ≤ s1 * s2 * (2 * ((w - p) 0 * (u - p) 0 + (w - p) 1 * (u - p) 1)) :=
        mul_le_mul_of_nonneg_left hdwu (by positivity)
      linarith
    linarith
  have dab := lt_or_gt_of_ne (hdet_ne a b ha hb hab h1)
  have dbc := lt_or_gt_of_ne (hdet_ne b c hb hc hbc h2)
  have dca := lt_or_gt_of_ne (hdet_ne c a hc ha (by rwa [dist_comm]) h3.symm)
  rcases dab with dab | dab <;> rcases dbc with dbc | dbc <;> rcases dca with dca | dca
  · exfalso
    exact hcyc a c b ha hc hb hac (by rwa [dist_comm]) hab
      (by linarith only [dca]) (by linarith only [dbc]) (by linarith only [dab])
  · exact ⟨a, b, c, Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), h1, h2.symm, by linarith only [dab], by linarith only [dbc]⟩
  · exact ⟨c, a, b, Or.inr (Or.inr rfl), Or.inl rfl, Or.inr (Or.inl rfl), h3.symm, h1.symm, by linarith only [dca], by linarith only [dab]⟩
  · exact ⟨a, c, b, Or.inl rfl, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), h3, h2, dca, dbc⟩
  · exact ⟨b, c, a, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), Or.inl rfl, h2, h3, by linarith only [dbc], by linarith only [dca]⟩
  · exact ⟨b, a, c, Or.inr (Or.inl rfl), Or.inl rfl, Or.inr (Or.inr rfl), h1.symm, h3.symm, dab, dca⟩
  · exact ⟨c, b, a, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), Or.inl rfl, h2.symm, h1, dbc, dab⟩
  · exfalso
    exact hcyc a b c ha hb hc hab hbc hac dab dbc dca

lemma hopf_pannwitz_aux (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, ∀ A : Finset ℝ², A.card = k →
      (∀ p ∈ A, ∀ q ∈ A, dist p q ≤ D) →
      ((A ×ˢ A).filter (fun z => dist z.1 z.2 = D)).card ≤ 2 * A.card := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A hcard hle
    classical
    by_cases hall : ∀ p ∈ A, (A.filter (fun q => dist p q = D)).card ≤ 2
    · have hsum : ((A ×ˢ A).filter (fun z => dist z.1 z.2 = D)).card =
          ∑ p ∈ A, (A.filter (fun q => dist p q = D)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        congr 1; ext p; rw [Finset.card_filter]
      rw [hsum]
      calc ∑ p ∈ A, (A.filter (fun q => dist p q = D)).card
          ≤ ∑ _p ∈ A, 2 := Finset.sum_le_sum hall
        _ = 2 * A.card := by simp [mul_comm]
    · push Not at hall
      obtain ⟨p, hp, hdeg⟩ := hall
      have h3 : 3 ≤ (A.filter (fun q => dist p q = D)).card := by omega
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq h3
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hTcard
      have haM := Finset.mem_filter.mp (hTsub (show a ∈ ({a, b, c} : Finset ℝ²) by simp))
      have hbM := Finset.mem_filter.mp (hTsub (show b ∈ ({a, b, c} : Finset ℝ²) by simp))
      have hcM := Finset.mem_filter.mp (hTsub (show c ∈ ({a, b, c} : Finset ℝ²) by simp))
      obtain ⟨x, y, z, hx3, hy3, hz3, hxy, hzy, hs1, hs2⟩ :=
        exists_middle_of_three_on_circle hD
          (by rw [dist_comm]; exact haM.2) (by rw [dist_comm]; exact hbM.2)
          (by rw [dist_comm]; exact hcM.2)
          (hle a haM.1 b hbM.1) (hle b hbM.1 c hcM.1) (hle a haM.1 c hcM.1) hab hbc hac
      have hmem_T : ∀ u, (u = a ∨ u = b ∨ u = c) → u ∈ A ∧ dist u p = D := by
        intro u hu
        rcases hu with rfl | rfl | rfl
        · exact ⟨haM.1, by rw [dist_comm]; exact haM.2⟩
        · exact ⟨hbM.1, by rw [dist_comm]; exact hbM.2⟩
        · exact ⟨hcM.1, by rw [dist_comm]; exact hcM.2⟩
      obtain ⟨hxA, hxp⟩ := hmem_T x hx3
      obtain ⟨hyA, hyp⟩ := hmem_T y hy3
      obtain ⟨hzA, hzp⟩ := hmem_T z hz3
      have hy_uniq : ∀ w ∈ A, dist w y = D → w = p := fun w hw hwy =>
        hopf_middle_unique_neighbor hD hyp hxp hzp hwy (hle w hw x hxA) (hle w hw z hzA)
          hxy hzy hs1 hs2
      let A' : Finset ℝ² := A.erase y
      have hA'card : A'.card = k - 1 := by rw [Finset.card_erase_of_mem hyA, hcard]
      have hkpos : 0 < k := by
        rw [← hcard]; exact Finset.card_pos.mpr ⟨y, hyA⟩
      have hsub_ih := ih (k - 1) (by omega) A' hA'card
        (fun u hu v hv => hle u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv))
      have hsplit : ((A ×ˢ A).filter (fun z => dist z.1 z.2 = D)) ⊆
          ((A' ×ˢ A').filter (fun z => dist z.1 z.2 = D)) ∪ {(p, y), (y, p)} := by
        intro u hu
        have hM := Finset.mem_filter.mp hu
        have hu1 : u.1 ∈ A := (Finset.mem_product.mp hM.1).1
        have hu2 : u.2 ∈ A := (Finset.mem_product.mp hM.1).2
        by_cases h1 : u.1 = y
        · have h2 : u.2 = p := hy_uniq u.2 hu2 (by rw [dist_comm, ← h1]; exact hM.2)
          have : u = (y, p) := Prod.ext h1 h2
          simp [this]
        · by_cases h2 : u.2 = y
          · have h1' : u.1 = p := hy_uniq u.1 hu1 (by rw [← h2]; exact hM.2)
            have : u = (p, y) := Prod.ext h1' h2
            simp [this]
          · apply Finset.mem_union_left
            exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_erase.mpr ⟨h1, hu1⟩, Finset.mem_erase.mpr ⟨h2, hu2⟩⟩, hM.2⟩
      have hcard_le : ((A ×ˢ A).filter (fun z => dist z.1 z.2 = D)).card ≤
          ((A' ×ˢ A').filter (fun z => dist z.1 z.2 = D)).card + 2 := by
        calc ((A ×ˢ A).filter (fun z => dist z.1 z.2 = D)).card
            ≤ (((A' ×ˢ A').filter (fun z => dist z.1 z.2 = D)) ∪ {(p, y), (y, p)}).card :=
              Finset.card_le_card hsplit
          _ ≤ ((A' ×ˢ A').filter (fun z => dist z.1 z.2 = D)).card + ({(p, y), (y, p)} : Finset _).card :=
              Finset.card_union_le _ _
          _ ≤ ((A' ×ˢ A').filter (fun z => dist z.1 z.2 = D)).card + 2 := by
              have : ({(p, y), (y, p)} : Finset _).card ≤ 2 := Finset.card_le_two
              omega
      omega

lemma hopf_pannwitz_diam_pairs (A : Finset ℝ²) (hA : Erdos99.HasMinDist1 A) :
    ((A ×ˢ A).filter (fun z => dist z.1 z.2 = diam (A : Set ℝ²))).card ≤ 2 * A.card := by
  obtain ⟨p0, hp0, q0, hq0, hpq0⟩ := hA.2
  have hDpos : 0 < diam (A : Set ℝ²) := by
    have h1 : dist p0 q0 ≤ diam (A : Set ℝ²) :=
      dist_le_diam_of_mem A.finite_toSet.isBounded hp0 hq0
    linarith
  exact hopf_pannwitz_aux (diam (A : Set ℝ²)) hDpos A.card A rfl
    (fun p hp q hq => dist_le_diam_of_mem A.finite_toSet.isBounded hp hq)

/- ### Part 7: First-order Farkas rigidity and non-isolated diametral pair -/

lemma no_contracting_velocity {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A)
    (v : ℝ² → ℝ²)
    (hv : ∀ p ∈ A, ∀ q ∈ A, dist p q = 1 → 0 ≤ ⟪p - q, v p - v q⟫_ℝ) :
    ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧ 0 ≤ ⟪p - q, v p - v q⟫_ℝ := by
  classical
  by_contra hneg
  push Not at hneg
  let move : ℝ → ℝ² → ℝ² := fun t p => p + t • v p
  have hdist_sq : ∀ (t : ℝ) (p q : ℝ²),
      dist (move t p) (move t q) ^ 2 =
        dist p q ^ 2 + 2 * t * ⟪p - q, v p - v q⟫_ℝ + t ^ 2 * ‖v p - v q‖ ^ 2 := by
    intro t p q
    have hsub : move t p - move t q = (p - q) + t • (v p - v q) := by
      dsimp only [move]; rw [smul_sub]; abel
    rw [dist_eq_norm, dist_eq_norm, hsub, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      inner_smul_right, mul_pow, sq_abs]
    ring
  have hpairs : ∀ p ∈ A, ∀ q ∈ A,
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (p ≠ q → 1 ≤ dist (move t p) (move t q)) ∧
        dist (move t p) (move t q) < diam (A : Set ℝ²) := by
    intro p hp q hq
    have hDpos : 0 < diam (A : Set ℝ²) := by
      obtain ⟨p0, hp0, q0, hq0, hpq0⟩ := hA.2
      have := dist_le_diam_of_mem A.finite_toSet.isBounded hp0 hq0
      linarith
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), p ≠ q → 1 ≤ dist (move t p) (move t q) := by
      by_cases hpq : p = q
      · exact Eventually.of_forall fun _ h => (h hpq).elim
      · have hge : 1 ≤ dist p q := hA.1 p hp q hq hpq
        rcases eq_or_lt_of_le hge with h1eq | h1lt
        · filter_upwards [self_mem_nhdsWithin] with t ht _
          have hsq : 1 ≤ dist (move t p) (move t q) ^ 2 := by
            rw [hdist_sq, ← h1eq]
            have h0 : 0 ≤ ⟪p - q, v p - v q⟫_ℝ := hv p hp q hq h1eq.symm
            have ht0 : 0 < t := ht
            nlinarith [sq_nonneg t, sq_nonneg ‖v p - v q‖]
          nlinarith [dist_nonneg (x := move t p) (y := move t q)]
        · have hcont : Continuous (fun t : ℝ => dist (move t p) (move t q)) := by
            fun_prop
          have hlim : Tendsto (fun t : ℝ => dist (move t p) (move t q)) (𝓝[>] 0) (𝓝 (dist p q)) := by
            have := (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
            simpa [move] using this
          filter_upwards [hlim.eventually (Ioi_mem_nhds h1lt)] with t ht _
          exact ht.le
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), dist (move t p) (move t q) < diam (A : Set ℝ²) := by
      have hle : dist p q ≤ diam (A : Set ℝ²) :=
        dist_le_diam_of_mem A.finite_toSet.isBounded hp hq
      rcases eq_or_lt_of_le hle with hdeq | hdlt
      · have hneg' : ⟪p - q, v p - v q⟫_ℝ < 0 := hneg p hp q hq hdeq
        let M : ℝ := ‖v p - v q‖ ^ 2 + 1
        have hM : 0 < M := by positivity
        let δ : ℝ := -(2 * ⟪p - q, v p - v q⟫_ℝ) / M
        have hδ : 0 < δ := div_pos (by linarith) hM
        filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
        have hsq : dist (move t p) (move t q) ^ 2 < diam (A : Set ℝ²) ^ 2 := by
          rw [hdist_sq, hdeq]
          have htm : t * M < -(2 * ⟪p - q, v p - v q⟫_ℝ) := by
            have := (lt_div_iff₀ hM).mp ht.2
            linarith
          have ht0 : 0 < t := ht.1
          have hsqM : t ^ 2 * ‖v p - v q‖ ^ 2 ≤ t * (t * M) := by
            dsimp only [M]; nlinarith [sq_nonneg t]
          nlinarith [ht0, htm, hsqM]
        nlinarith [dist_nonneg (x := move t p) (y := move t q), hDpos]
      · have hcont : Continuous (fun t : ℝ => dist (move t p) (move t q)) := by
          fun_prop
        have hlim : Tendsto (fun t : ℝ => dist (move t p) (move t q)) (𝓝[>] 0) (𝓝 (dist p q)) := by
          have := (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
          simpa [move] using this
        exact hlim.eventually (Iio_mem_nhds hdlt)
    filter_upwards [h1, h2] with t ht1 ht2
    exact ⟨ht1, ht2⟩
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ p ∈ A, ∀ q ∈ A,
        (p ≠ q → 1 ≤ dist (move t p) (move t q)) ∧
        dist (move t p) (move t q) < diam (A : Set ℝ²) :=
    (Finset.eventually_all A).mpr fun p hp =>
      (Finset.eventually_all A).mpr fun q hq => hpairs p hp q hq
  obtain ⟨t, ht⟩ := hall.exists
  exact no_separated_improvement hA hmin (move t)
    (fun p hp q hq => (ht p hp q hq).1) (fun p hp q hq => (ht p hp q hq).2)

lemma exists_nonisolated_diam_pair {A : Finset ℝ²}
    (hA : Erdos99.HasMinDist1 A)
    (hmin : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A) :
    ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧
      (∃ u ∈ A, dist p u = 1) ∧ (∃ w ∈ A, dist q w = 1) := by
  classical
  obtain ⟨p0, hp0, q0, hq0, hpq0⟩ := hA.2
  have hAne : A.Nonempty := ⟨p0, hp0⟩
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hAne
  have hDpos : 0 < diam (A : Set ℝ²) := by
    have := dist_le_diam_of_mem A.finite_toSet.isBounded hp0 hq0
    linarith
  let c : ℝ² := ((A.card : ℝ)⁻¹) • ∑ x ∈ A, x
  let isIso : ℝ² → Prop := fun p => ∀ u ∈ A, dist p u ≠ 1
  let v : ℝ² → ℝ² := fun p => if isIso p then c - p else 0
  have hv_unit : ∀ p ∈ A, ∀ q ∈ A, dist p q = 1 → 0 ≤ ⟪p - q, v p - v q⟫_ℝ := by
    intro p hp q hq hpq
    have hp_ni : ¬ isIso p := fun h => h q hq hpq
    have hq_ni : ¬ isIso q := fun h => h p hp (by rw [dist_comm]; exact hpq)
    simp [v, hp_ni, hq_ni]
  obtain ⟨p, hp, q, hq, hd, hge⟩ := no_contracting_velocity hA hmin v hv_unit
  have hneg_cent : ∀ a ∈ A, ∀ b ∈ A, dist a b = diam (A : Set ℝ²) →
      ⟪a - b, c - a⟫_ℝ < 0 := by
    intro a ha b hb hab
    have hterm : ∀ x ∈ A, 2 * ⟪a - b, x - a⟫_ℝ ≤ -(dist x a ^ 2) := by
      intro x hx
      have hxb : dist x b ≤ dist a b := by
        rw [hab]; exact dist_le_diam_of_mem A.finite_toSet.isBounded hx hb
      have hsq : dist x b ^ 2 ≤ dist a b ^ 2 :=
        sq_le_sq' (by linarith [dist_nonneg (x := x) (y := b), dist_nonneg (x := a) (y := b)]) hxb
      have hident : x - b = (x - a) + (a - b) := by abel
      rw [dist_eq_norm, dist_eq_norm, hident, norm_add_sq_real] at hsq
      rw [dist_eq_norm, real_inner_comm]
      linarith
    have hsum_le : ∑ x ∈ A, 2 * ⟪a - b, x - a⟫_ℝ ≤ ∑ x ∈ A, -(dist x a ^ 2) :=
      Finset.sum_le_sum hterm
    have hsum_neg : ∑ x ∈ A, -(dist x a ^ 2) < 0 := by
      have hb_lt : -(dist b a ^ 2) < 0 := by
        rw [dist_comm, hab]; nlinarith
      have hnonpos : ∀ x ∈ A, -(dist x a ^ 2) ≤ 0 := fun x _ => by nlinarith
      have hsplit := Finset.add_sum_erase A (fun x => -(dist x a ^ 2)) hb
      have hrest : ∑ x ∈ A.erase b, -(dist x a ^ 2) ≤ 0 :=
        Finset.sum_nonpos fun x hx => hnonpos x (Finset.mem_of_mem_erase hx)
      linarith
    have hca : c - a = ((A.card : ℝ)⁻¹) • ∑ x ∈ A, (x - a) := by
      dsimp only [c]
      rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub,
        smul_smul, inv_mul_cancel₀ hApos.ne', one_smul]
    rw [hca, inner_smul_right, inner_sum]
    have h2sum : 2 * ∑ x ∈ A, ⟪a - b, x - a⟫_ℝ < 0 := by
      rw [Finset.mul_sum]; linarith
    have : (A.card : ℝ)⁻¹ * ∑ x ∈ A, ⟪a - b, x - a⟫_ℝ < 0 :=
      mul_neg_of_pos_of_neg (inv_pos.mpr hApos) (by linarith)
    exact this
  have hp_not_iso : ¬ isIso p := by
    intro hpI
    by_cases hqI : isIso q
    · have hvpq : v p - v q = -(p - q) := by
        simp only [v, hpI, hqI, ↓reduceIte]; abel
      rw [hvpq, inner_neg_right, real_inner_self_eq_norm_sq, ← dist_eq_norm, hd] at hge
      nlinarith
    · have hvpq : v p - v q = c - p := by simp [v, hpI, hqI]
      rw [hvpq] at hge
      linarith [hneg_cent p hp q hq hd]
  have hq_not_iso : ¬ isIso q := by
    intro hqI
    have hvpq : v p - v q = -(c - q) := by simp [v, hp_not_iso, hqI]
    rw [hvpq, inner_neg_right] at hge
    have hcomm : ⟪p - q, c - q⟫_ℝ = -⟪q - p, c - q⟫_ℝ := by
      rw [← inner_neg_left]; congr 1; abel
    rw [hcomm, neg_neg] at hge
    linarith [hneg_cent q hq p hp (by rw [dist_comm]; exact hd)]
  dsimp only [isIso] at hp_not_iso hq_not_iso
  push Not at hp_not_iso hq_not_iso
  exact ⟨p, hp, q, hq, hd, hp_not_iso, hq_not_iso⟩

/- ### Reduction hypotheses H1 and H2 -/

/-- Sparse / rattler regime: no triangle-free 1-separated n-point set satisfying all six
proved geometric invariants (hexagonal diameter upper bound, disk-packing area lower bound,
max unit degree <= 5, non-crossing unit segments, Hopf-Pannwitz diametral pair bound, and
Farkas rigidity with a non-isolated diametral pair) and having average unit degree < 3
can minimize diameter for large n. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℝ², A.card = n →
    (∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) → (∃ p ∈ A, ∃ q ∈ A, dist p q = 1) →
    diam (A : Set ℝ²) ≤ 2 * ((Nat.sqrt (n / 3) : ℝ) + 1) →
    Real.pi * (n : ℝ) ≤ 4 * (diam (A : Set ℝ²) + 1) ^ 2 →
    (∀ p ∈ A, (A.filter (fun q => dist p q = 1)).card ≤ 5) →
    (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, ∀ s ∈ A, dist p q = 1 → dist r s = 1 →
      p ≠ r → p ≠ s → q ≠ r → q ≠ s → Disjoint (segment ℝ p q) (segment ℝ r s)) →
    ((A ×ˢ A).filter (fun z => dist z.1 z.2 = diam (A : Set ℝ²))).card ≤ 2 * n →
    (∀ v : ℝ² → ℝ²,
      (∀ p ∈ A, ∀ q ∈ A, dist p q = 1 → 0 ≤ ⟪p - q, v p - v q⟫_ℝ) →
      ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧ 0 ≤ ⟪p - q, v p - v q⟫_ℝ) →
    (∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧
      (∃ u ∈ A, dist p u = 1) ∧ (∃ w ∈ A, dist q w = 1)) →
    (¬ ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1) →
    ((A ×ˢ A).filter (fun z => dist z.1 z.2 = 1)).card < 3 * n →
    ∃ B : Finset ℝ², B.card = n ∧
      (∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) ∧
      diam (B : Set ℝ²) < diam (A : Set ℝ²)

/-- Dense / quadrangulated regime: the same conclusion when the triangle-free planar
unit-distance graph has average unit degree >= 3 (ordered unit pairs >= 3n). -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℝ², A.card = n →
    (∀ p ∈ A, ∀ q ∈ A, p ≠ q → 1 ≤ dist p q) → (∃ p ∈ A, ∃ q ∈ A, dist p q = 1) →
    diam (A : Set ℝ²) ≤ 2 * ((Nat.sqrt (n / 3) : ℝ) + 1) →
    Real.pi * (n : ℝ) ≤ 4 * (diam (A : Set ℝ²) + 1) ^ 2 →
    (∀ p ∈ A, (A.filter (fun q => dist p q = 1)).card ≤ 5) →
    (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, ∀ s ∈ A, dist p q = 1 → dist r s = 1 →
      p ≠ r → p ≠ s → q ≠ r → q ≠ s → Disjoint (segment ℝ p q) (segment ℝ r s)) →
    ((A ×ˢ A).filter (fun z => dist z.1 z.2 = diam (A : Set ℝ²))).card ≤ 2 * n →
    (∀ v : ℝ² → ℝ²,
      (∀ p ∈ A, ∀ q ∈ A, dist p q = 1 → 0 ≤ ⟪p - q, v p - v q⟫_ℝ) →
      ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧ 0 ≤ ⟪p - q, v p - v q⟫_ℝ) →
    (∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧
      (∃ u ∈ A, dist p u = 1) ∧ (∃ w ∈ A, dist q w = 1)) →
    (¬ ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A, dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1) →
    3 * n ≤ ((A ×ˢ A).filter (fun z => dist z.1 z.2 = 1)).card →
    ∃ B : Finset ℝ², B.card = n ∧
      (∀ p ∈ B, ∀ q ∈ B, p ≠ q → 1 ≤ dist p q) ∧
      diam (B : Set ℝ²) < diam (A : Set ℝ²)

theorem main : H1 → H2 → type_of% @Erdos99.erdos_99 := by
  intro h1 h2
  filter_upwards [(eventually_ge_atTop 2).and (h1.and h2)] with n ⟨hn2, hn1, hn2'⟩
  intro A hcard hA hmin
  by_contra htri
  have hmin' : IsMinOn (fun B : Finset ℝ² => diam (B : Set ℝ²))
      {B : Finset ℝ² | B.card = A.card ∧ Erdos99.HasMinDist1 B} A := by
    simpa only [hcard] using hmin
  obtain ⟨B0, hB0c, hB0min1, hB0d⟩ := hex_packing_exists n hn2
  have hd_ub : diam (A : Set ℝ²) ≤ 2 * ((Nat.sqrt (n / 3) : ℝ) + 1) :=
    (hmin ⟨hB0c, hB0min1⟩).trans hB0d
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hd_lb : Real.pi * (n : ℝ) ≤ 4 * (diam (A : Set ℝ²) + 1) ^ 2 := by
    simpa only [hcard] using disk_packing_lower_bound A hAne (fun p hp q hq hpq => hA.1 p hp q hq hpq)
  have hdeg5 : ∀ p ∈ A, (A.filter (fun q => dist p q = 1)).card ≤ 5 :=
    unit_degree_le_five A (fun p hp q hq hpq => hA.1 p hp q hq hpq) htri
  have hplanar : ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, ∀ s ∈ A, dist p q = 1 → dist r s = 1 →
      p ≠ r → p ≠ s → q ≠ r → q ≠ s → Disjoint (segment ℝ p q) (segment ℝ r s) :=
    fun _ hp _ hq _ hr _ hs => unit_segments_disjoint A
      (fun a ha b hb hab => hA.1 a ha b hb hab) htri hp hq hr hs
  have hhp : ((A ×ˢ A).filter (fun z => dist z.1 z.2 = diam (A : Set ℝ²))).card ≤ 2 * n := by
    simpa only [hcard] using hopf_pannwitz_diam_pairs A hA
  have hfarkas : ∀ v : ℝ² → ℝ²,
      (∀ p ∈ A, ∀ q ∈ A, dist p q = 1 → 0 ≤ ⟪p - q, v p - v q⟫_ℝ) →
      ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧ 0 ≤ ⟪p - q, v p - v q⟫_ℝ :=
    fun v hv => no_contracting_velocity hA hmin' v hv
  have hnoniso : ∃ p ∈ A, ∃ q ∈ A, dist p q = diam (A : Set ℝ²) ∧
      (∃ u ∈ A, dist p u = 1) ∧ (∃ w ∈ A, dist q w = 1) :=
    exists_nonisolated_diam_pair hA hmin'
  have htri' : ¬ ∃ p ∈ A, ∃ q ∈ A, ∃ r ∈ A,
      dist p q = 1 ∧ dist q r = 1 ∧ dist p r = 1 := by
    rintro ⟨p, hp, q, hq, r, hr, h⟩
    exact htri ⟨p, hp, q, hq, r, hr, h⟩
  obtain ⟨C, hCc, hCsep, hCd⟩ : ∃ C : Finset ℝ², C.card = n ∧
      (∀ p ∈ C, ∀ q ∈ C, p ≠ q → 1 ≤ dist p q) ∧ diam (C : Set ℝ²) < diam (A : Set ℝ²) := by
    by_cases hsparse : ((A ×ˢ A).filter (fun z => dist z.1 z.2 = 1)).card < 3 * n
    · exact hn1 A hcard (fun p hp q hq hpq => hA.1 p hp q hq hpq) hA.2
        hd_ub hd_lb hdeg5 hplanar hhp hfarkas hnoniso htri' hsparse
    · exact hn2' A hcard (fun p hp q hq hpq => hA.1 p hp q hq hpq) hA.2
        hd_ub hd_lb hdeg5 hplanar hhp hfarkas hnoniso htri' (Nat.le_of_not_lt hsparse)
  classical
  let e : A ≃ C := Finset.equivOfCardEq (hcard.trans hCc.symm)
  let f : ℝ² → ℝ² := fun p => if hp : p ∈ A then (e ⟨p, hp⟩ : ℝ²) else p
  have hf (p : ℝ²) (hp : p ∈ A) : f p = (e ⟨p, hp⟩ : ℝ²) := by simp [f, hp]
  have hmem (p : ℝ²) (hp : p ∈ A) : f p ∈ C := by
    rw [hf p hp]
    exact (e ⟨p, hp⟩).property
  refine no_separated_improvement hA hmin' f ?_ (fun p hp q hq =>
    (dist_le_diam_of_mem C.finite_toSet.isBounded (hmem p hp) (hmem q hq)).trans_lt hCd)
  intro p hp q hq hpq
  apply hCsep _ (hmem p hp) _ (hmem q hq)
  rw [hf p hp, hf q hq]
  intro heq
  exact hpq (congrArg Subtype.val (e.injective (Subtype.ext heq)))

end OMA.R_Erdos99_erdos_99_R2
