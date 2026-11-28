import OMAStatements.S_mo_29000

/-!
Arman, Bondarenko, Nazarov, Prymak, and Radchenko construct the width-two body
in *Small volume bodies of constant width* (https://arxiv.org/abs/2405.18501v2).
The proof below formalizes their body and width argument. For volume, it uses
coordinate-wise ellipsoids on each sign orthant, together with a strict
mixed-sign gap in every dimension greater than one.
-/


/-!
The constant-width body follows Claims 2 and 3 of Arman, Bondarenko, Nazarov,
Prymak, and Radchenko, *Small volume bodies of constant width*,
https://arxiv.org/abs/2405.18501v2, DOI 10.1093/imrn/rnaf020.
-/

namespace OMA.MO29000

open Metric

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def posPart {n : ℕ} (x : Space n) : Space n :=
  WithLp.toLp 2 (fun i => max (x i) 0)

noncomputable def negPart {n : ℕ} (x : Space n) : Space n := posPart (-x)

@[simp] theorem posPart_apply {n : ℕ} (x : Space n) (i : Fin n) :
    posPart x i = max (x i) 0 := rfl

@[simp] theorem negPart_apply {n : ℕ} (x : Space n) (i : Fin n) :
    negPart x i = max (-x i) 0 := rfl

noncomputable def body (n : ℕ) : Set (Space n) :=
  {x | ‖posPart x‖ ^ 2 + (‖negPart x‖ + Real.sqrt 2) ^ 2 ≤ 4}

noncomputable def halfBody (n : ℕ) : Set (Space n) :=
  (fun x : Space n => (1 / 2 : ℝ) • x) '' body n

theorem mem_body_iff {n : ℕ} (x : Space n) :
    x ∈ body n ↔ ‖posPart x‖ ^ 2 + (‖negPart x‖ + Real.sqrt 2) ^ 2 ≤ 4 := Iff.rfl

theorem norm_sq_posPart {n : ℕ} (x : Space n) :
    ‖posPart x‖ ^ 2 = ∑ i, (max (x i) 0) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, posPart_apply]

theorem norm_sq_negPart {n : ℕ} (x : Space n) :
    ‖negPart x‖ ^ 2 = ∑ i, (max (-x i) 0) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, negPart_apply]

private theorem root_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)

private theorem root_pos : 0 < Real.sqrt 2 := by positivity

theorem eq_pos_sub_neg {n : ℕ} (x : Space n) : x = posPart x - negPart x := by
  ext i
  simp only [PiLp.sub_apply, posPart_apply, negPart_apply]
  rcases le_total 0 (x i) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -x i ≤ 0), sub_zero]
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -x i)]
    ring

theorem norm_sq_parts {n : ℕ} (x : Space n) :
    ‖x‖ ^ 2 = ‖posPart x‖ ^ 2 + ‖negPart x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [posPart_apply, negPart_apply]
  rcases le_total 0 (x i) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -x i ≤ 0)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -x i)]
    ring

private theorem norm_le_of_nonneg_le {n : ℕ} {x y : Space n}
    (hn : ∀ i, 0 ≤ x i) (hle : ∀ i, x i ≤ y i) : ‖x‖ ≤ ‖y‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_le_sum fun i _ => (sq_le_sq₀ (hn i) ((hn i).trans (hle i))).2 (hle i)

private theorem mem_body_of_parts {n : ℕ} {x y : Space n}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (h : ‖x‖ ^ 2 + (‖y‖ + Real.sqrt 2) ^ 2 ≤ 4) : x - y ∈ body n := by
  have h1 : ‖posPart (x - y)‖ ≤ ‖x‖ :=
    norm_le_of_nonneg_le (fun i => le_max_right _ _) (fun i => by
      simp only [posPart_apply, PiLp.sub_apply, max_le_iff]
      exact ⟨sub_le_self _ (hy i), hx i⟩)
  have h2 : ‖negPart (x - y)‖ ≤ ‖y‖ :=
    norm_le_of_nonneg_le (fun i => le_max_right _ _) (fun i => by
      simp only [negPart_apply, PiLp.sub_apply, max_le_iff]
      exact ⟨by linarith [hx i], hy i⟩)
  have hs := (sq_le_sq₀ (norm_nonneg (posPart (x - y))) (norm_nonneg x)).2 h1
  have ht := (sq_le_sq₀ (by positivity : 0 ≤ ‖negPart (x - y)‖ + Real.sqrt 2)
    (by positivity : 0 ≤ ‖y‖ + Real.sqrt 2)).2 (by linarith : ‖negPart (x - y)‖ + Real.sqrt 2 ≤ ‖y‖ + Real.sqrt 2)
  exact (add_le_add hs ht).trans h

private theorem norm_sub_sq_le {n : ℕ} (x y : Space n)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    ‖x - y‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [PiLp.sub_apply]
  nlinarith only [mul_nonneg (hx i) (hy i)]

private theorem sub_rearrange {n : ℕ} (x y : Space n) :
    x - y = (posPart x + negPart y) - (posPart y + negPart x) := by
  calc
    x - y = (posPart x - negPart x) - (posPart y - negPart y) :=
      congrArg₂ (· - ·) (eq_pos_sub_neg x) (eq_pos_sub_neg y)
    _ = _ := by abel

private theorem norm_pos_le {n : ℕ} {x : Space n} (hx : x ∈ body n) : ‖posPart x‖ ≤ Real.sqrt 2 := by
  change ‖posPart x‖ ^ 2 + (‖negPart x‖ + Real.sqrt 2) ^ 2 ≤ 4 at hx
  apply (sq_le_sq₀ (norm_nonneg _) root_pos.le).1
  nlinarith only [hx, root_sq, sq_nonneg ‖negPart x‖, mul_nonneg (norm_nonneg (negPart x)) root_pos.le]

/-- The profile body has diameter at most two. -/
theorem dist_le_two {n : ℕ} {x y : Space n} (hx : x ∈ body n) (hy : y ∈ body n) :
    dist x y ≤ 2 := by
  rw [dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2), sub_rearrange]
  have hn1 i : 0 ≤ (posPart x + negPart y) i := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hn2 i : 0 ≤ (posPart y + negPart x) i := add_nonneg (le_max_right _ _) (le_max_right _ _)
  apply (norm_sub_sq_le _ _ hn1 hn2).trans
  have h1 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖posPart x‖ + ‖negPart y‖)).2
    (norm_add_le (posPart x) (negPart y))
  have h2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖posPart y‖ + ‖negPart x‖)).2
    (norm_add_le (posPart y) (negPart x))
  change ‖posPart x‖ ^ 2 + (‖negPart x‖ + Real.sqrt 2) ^ 2 ≤ 4 at hx
  change ‖posPart y‖ ^ 2 + (‖negPart y‖ + Real.sqrt 2) ^ 2 ≤ 4 at hy
  have hx' := mul_nonneg (sub_nonneg.mpr (norm_pos_le hx)) (norm_nonneg (negPart y))
  have hy' := mul_nonneg (sub_nonneg.mpr (norm_pos_le hy)) (norm_nonneg (negPart x))
  nlinarith only [h1, h2, hx, hy, hx', hy', root_sq]

private theorem posPart_combo_le {n : ℕ} (x y : Space n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖posPart (a • x + b • y)‖ ≤ a * ‖posPart x‖ + b * ‖posPart y‖ := by
  have h1 : ‖posPart (a • x + b • y)‖ ≤ ‖a • posPart x + b • posPart y‖ := by
    apply norm_le_of_nonneg_le (fun i => le_max_right _ _)
    intro i
    simp only [posPart_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, max_le_iff]
    exact ⟨add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb),
      add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))⟩
  refine h1.trans ?_
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] using
    norm_add_le (a • posPart x) (b • posPart y)

private theorem negPart_combo_le {n : ℕ} (x y : Space n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖negPart (a • x + b • y)‖ ≤ a * ‖negPart x‖ + b * ‖negPart y‖ := by
  unfold negPart
  rw [neg_add, ← smul_neg, ← smul_neg]
  exact posPart_combo_le (-x) (-y) ha hb

private theorem sq_combo {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (u v : ℝ) :
    (a*u+b*v)^2 ≤ a*u^2 + b*v^2 := by
  have hs : 0 ≤ a*b*(u-v)^2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  calc
    (a*u+b*v)^2 = (a+b)*(a*u^2+b*v^2) - a*b*(u-v)^2 := by ring
    _ ≤ _ := by rw [hab, one_mul]; linarith

/-- Convexity follows from the coordinatewise convexity of the two parts. -/
theorem body_convex (n : ℕ) : Convex ℝ (body n) := by
  intro x hx y hy a b ha hb hab
  have h1 := posPart_combo_le x y ha hb
  have h2 := negPart_combo_le x y ha hb
  have e : a*(‖negPart x‖ + Real.sqrt 2) + b*(‖negPart y‖ + Real.sqrt 2) =
      a*‖negPart x‖ + b*‖negPart y‖ + Real.sqrt 2 := by
    linear_combination Real.sqrt 2 * hab
  have hpos := (sq_le_sq₀ (norm_nonneg _) (le_trans (norm_nonneg _) h1)).2 h1
  have hneg := (sq_le_sq₀ (by positivity : 0 ≤ ‖negPart (a • x + b • y)‖ + Real.sqrt 2)
      (by positivity : 0 ≤ a*(‖negPart x‖ + Real.sqrt 2) + b*(‖negPart y‖ + Real.sqrt 2))).2
      (by rw [e]; exact add_le_add_left h2 _)
  have w1 := sq_combo ha hb hab ‖posPart x‖ ‖posPart y‖
  have w2 := sq_combo ha hb hab (‖negPart x‖ + Real.sqrt 2) (‖negPart y‖ + Real.sqrt 2)
  change ‖posPart x‖ ^ 2 + (‖negPart x‖ + Real.sqrt 2) ^ 2 ≤ 4 at hx
  change ‖posPart y‖ ^ 2 + (‖negPart y‖ + Real.sqrt 2) ^ 2 ≤ 4 at hy
  change ‖posPart (a • x + b • y)‖ ^ 2 + (‖negPart (a • x + b • y)‖ + Real.sqrt 2) ^ 2 ≤ 4
  nlinarith only [hpos, hneg, w1, w2, mul_le_mul_of_nonneg_left hx ha,
    mul_le_mul_of_nonneg_left hy hb, hab]

theorem continuous_posPart (n : ℕ) : Continuous (@posPart n) :=
  PiLp.continuous_toLp 2 _ |>.comp (continuous_pi fun i => (PiLp.continuous_apply 2 _ i).max continuous_const)

theorem continuous_negPart (n : ℕ) : Continuous (@negPart n) :=
  (continuous_posPart n).comp continuous_neg

@[simp] theorem zero_mem_body (n : ℕ) : (0 : Space n) ∈ body n := by
  have hp : posPart (0 : Space n) = 0 := by ext i; simp
  have hn : negPart (0 : Space n) = 0 := by ext i; simp
  change ‖posPart (0 : Space n)‖ ^ 2 + (‖negPart (0 : Space n)‖ + Real.sqrt 2) ^ 2 ≤ 4
  rw [hp, hn]
  norm_num

theorem body_isClosed (n : ℕ) : IsClosed (body n) := by
  exact isClosed_le (((continuous_posPart n).norm.pow 2).add
    (((continuous_negPart n).norm.add continuous_const).pow 2)) continuous_const

/-- The profile body is compact. -/
theorem body_compact (n : ℕ) : IsCompact (body n) := by
  apply Metric.isCompact_of_isClosed_isBounded (body_isClosed n)
  exact Metric.isBounded_closedBall.subset (fun x hx =>
    Metric.mem_closedBall.mpr (dist_le_two hx (zero_mem_body n)))

private theorem unit_chord_oriented {n : ℕ} (u : Space n) (hu : ‖u‖ = 1)
    (hparts : ‖posPart u‖ ≤ ‖negPart u‖) :
    ∃ x ∈ body n, ∃ y ∈ body n, x - y = (2 : ℝ) • u := by
  let p := posPart u
  let q := negPart u
  have hp i : 0 ≤ p i := le_max_right _ _
  have hq i : 0 ≤ q i := le_max_right _ _
  have heq : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1 := by
    have h := norm_sq_parts u
    rw [hu] at h
    simpa [p, q] using h.symm
  have hpp : ‖p‖ ^ 2 ≤ ‖q‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hparts
  have hqpos : 0 < ‖q‖ := by
    by_contra! h
    have hz : ‖q‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [hz] at hpp heq
    nlinarith only [hpp, heq]
  let r := Real.sqrt 2 / ‖q‖
  have hr : 0 ≤ r := div_nonneg root_pos.le hqpos.le
  have hscale : r * ‖q‖ = Real.sqrt 2 := div_mul_cancel₀ _ hqpos.ne'
  have hr2 : r ≤ 2 := by
    apply (div_le_iff₀ hqpos).2
    apply (sq_le_sq₀ root_pos.le (by positivity)).1
    nlinarith only [heq, hpp, root_sq]
  let x := (2 : ℝ) • p - (2 - r) • q
  let y := r • q
  have hx : x ∈ body n := by
    apply mem_body_of_parts
    · intro i
      rw [PiLp.smul_apply, smul_eq_mul]
      exact mul_nonneg (by norm_num) (hp i)
    · intro i
      rw [PiLp.smul_apply, smul_eq_mul]
      exact mul_nonneg (sub_nonneg.mpr hr2) (hq i)
    · have he : (2 - r) * ‖q‖ + Real.sqrt 2 = 2 * ‖q‖ := by
        rw [sub_mul, hscale]; ring
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sub_nonneg.mpr hr2), he]
      nlinarith only [heq]
  have hy : y ∈ body n := by
    change r • q ∈ body n
    rw [← sub_zero (r • q)]
    apply mem_body_of_parts
    · intro i
      rw [PiLp.smul_apply, smul_eq_mul]
      exact mul_nonneg hr (hq i)
    · intro i
      simp
    · simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hscale, norm_zero,
        zero_add, root_sq]
      norm_num
  refine ⟨x, hx, y, hy, ?_⟩
  have hh : u = p - q := eq_pos_sub_neg u
  rw [hh]
  dsimp only [x, y]
  module

/-- Every unit direction is the orientation of a length-two chord. -/
theorem unit_chord {n : ℕ} (u : Space n) (hu : ‖u‖ = 1) :
    ∃ x ∈ body n, ∃ y ∈ body n, x - y = (2 : ℝ) • u := by
  by_cases h : ‖posPart u‖ ≤ ‖negPart u‖
  · exact unit_chord_oriented u hu h
  have hp : posPart (-u) = negPart u := rfl
  have hq : negPart (-u) = posPart u := by simp only [negPart, neg_neg]
  have hs : ‖posPart (-u)‖ ≤ ‖negPart (-u)‖ := by rw [hp, hq]; exact (le_of_not_ge h)
  obtain ⟨x, hx, y, hy, he⟩ := unit_chord_oriented (-u) (by simpa only [norm_neg] using hu) hs
  refine ⟨y, hy, x, hx, ?_⟩
  rw [← neg_sub x y, he, smul_neg, neg_neg]

private theorem half_dist_le_one {n : ℕ} {x y : Space n} (hx : x ∈ halfBody n) (hy : y ∈ halfBody n) :
    ‖x-y‖ ≤ 1 := by
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  have h := dist_le_two hx hy
  rw [dist_eq_norm] at h
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  linarith

private theorem half_unit_chord {n : ℕ} (u : Space n) (hu : ‖u‖ = 1) :
    ∃ x ∈ halfBody n, ∃ y ∈ halfBody n, x - y = u := by
  obtain ⟨x, hx, y, hy, he⟩ := unit_chord u hu
  refine ⟨(1/2:ℝ) • x, ⟨x, hx, rfl⟩, (1/2:ℝ) • y, ⟨y, hy, rfl⟩, ?_⟩
  rw [← smul_sub, he, smul_smul]
  norm_num

private theorem width_support {n : ℕ} (u : Space n) (hu : ‖u‖ = 1) :
    (⨆ x : halfBody n, inner ℝ (x : Space n) u) -
      (⨅ x : halfBody n, inner ℝ (x : Space n) u) = 1 := by
  obtain ⟨x, hx, y, hy, he⟩ := half_unit_chord u hu
  have hw : inner ℝ x u - inner ℝ y u = 1 := by
    rw [← inner_sub_left, he, real_inner_self_eq_norm_sq, hu]
    norm_num
  have hd (a b : Space n) (ha : a ∈ halfBody n) (hb : b ∈ halfBody n) :
      inner ℝ a u - inner ℝ b u ≤ 1 := by
    rw [← inner_sub_left]
    exact (real_inner_le_norm _ _).trans (by rw [hu, mul_one]; exact half_dist_le_one ha hb)
  have hi (z : halfBody n) : inner ℝ (z : Space n) u ≤ inner ℝ x u := by
    linarith only [hd z y z.property hy, hw]
  have lo (z : halfBody n) : inner ℝ y u ≤ inner ℝ (z : Space n) u := by
    linarith only [hd x z hx z.property, hw]
  have : Nonempty (halfBody n) := ⟨⟨x, hx⟩⟩
  have hb : BddAbove (Set.range (fun z : halfBody n => inner ℝ (z : Space n) u)) :=
    ⟨inner ℝ x u, Set.forall_mem_range.mpr hi⟩
  have hc : BddBelow (Set.range (fun z : halfBody n => inner ℝ (z : Space n) u)) :=
    ⟨inner ℝ y u, Set.forall_mem_range.mpr lo⟩
  have sup_eq : (⨆ z : halfBody n, inner ℝ (z : Space n) u) = inner ℝ x u :=
    le_antisymm (ciSup_le hi) (le_ciSup hb ⟨x, hx⟩)
  have inf_eq : (⨅ z : halfBody n, inner ℝ (z : Space n) u) = inner ℝ y u :=
    le_antisymm (ciInf_le hc ⟨y, hy⟩) (le_ciInf lo)
  rw [sup_eq, inf_eq, hw]

theorem halfBody_compact (n : ℕ) : IsCompact (halfBody n) :=
  (body_compact n).image (continuous_id.const_smul (1 / 2 : ℝ))

theorem halfBody_convex (n : ℕ) : Convex ℝ (halfBody n) := by
  exact (body_convex n).linear_image ((1/2:ℝ) • (LinearMap.id : Space n →ₗ[ℝ] Space n))

theorem halfBody_nonempty (n : ℕ) : (halfBody n).Nonempty :=
  ⟨_, ⟨0, zero_mem_body n, rfl⟩⟩

theorem halfBody_width (n : ℕ) (u : Space n) (hu : ‖u‖ = 1) :
    (⨆ x : halfBody n, inner ℝ (x : Space n) u) -
      (⨅ x : halfBody n, inner ℝ (x : Space n) u) = 1 := width_support u hu

end OMA.MO29000

namespace OMA.MO29000

theorem halfBody_constant_width (n : ℕ) : OMA.S_mo_29000.ConstantWidthOne (halfBody n) :=
  ⟨halfBody_compact n, halfBody_convex n, halfBody_nonempty n, halfBody_width n⟩

open Metric MeasureTheory
open scoped Pointwise ENNReal

/-- The same volume ratio applies after scaling from width two to width one. -/
theorem halfBody_volume_transfer (n : ℕ) (q : ℝ≥0∞)
    (h : volume (body n) ≤ q * volume (closedBall (0 : Space n) 1)) :
    volume (halfBody n) ≤ q * volume (closedBall (0 : Space n) (1/2)) := by
  have hr : 0 < (1/2 : ℝ) := by norm_num
  change volume ((1/2 : ℝ) • body n) ≤ _
  have hb := Measure.addHaar_closedBall_mul_of_pos (volume : Measure (Space n)) 0 hr 1
  simp only [mul_one] at hb
  rw [Measure.addHaar_smul_of_nonneg volume hr.le, hb, mul_left_comm q]
  gcongr

end OMA.MO29000

namespace OMA.MO29000Profile

noncomputable def big : ℝ := Real.sqrt 2
noncomputable def small : ℝ := 2 - big

def profile (a b : ℝ) : Prop := a ^ 2 + (b + big) ^ 2 ≤ 4

noncomputable def ellipse (r s a b : ℝ) : ℝ := a ^ 2 / r ^ 2 + b ^ 2 / s ^ 2

theorem big_sq : big ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem big_lower : (7 / 5 : ℝ) ≤ big := by
  unfold big
  exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)

theorem big_upper : big ≤ (10 / 7 : ℝ) := by
  unfold big
  exact (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)

theorem big_pos : 0 < big := by linarith [big_lower]

theorem small_lower : (4 / 7 : ℝ) ≤ small := by unfold small; linarith [big_upper]

theorem small_upper : small ≤ (3 / 5 : ℝ) := by unfold small; linarith [big_lower]

theorem small_pos : 0 < small := by linarith [small_lower]

private theorem ellipse_le_one_iff {r s a b : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ellipse r s a b ≤ 1 ↔ a ^ 2 * s ^ 2 + b ^ 2 * r ^ 2 ≤ r ^ 2 * s ^ 2 := by
  have he : ellipse r s a b = (a ^ 2 * s ^ 2 + b ^ 2 * r ^ 2) / (r ^ 2 * s ^ 2) := by
    unfold ellipse
    field_simp
  rw [he, div_le_iff₀ (by positivity), one_mul]

private theorem profile_y {a b : ℝ} (hp : profile a b) : b ≤ small := by
  unfold profile at hp
  have hba : b + big ≤ 2 := by
    by_contra! hlt
    have hs := pow_lt_pow_left₀ hlt (by norm_num : 0 ≤ (2 : ℝ)) (by norm_num : 2 ≠ 0)
    nlinarith only [hs, hp, sq_nonneg a]
  unfold small
  linarith

private theorem compact_profile {a b : ℝ} (hp : profile a b) :
    a ^ 2 ≤ (small - b) * (small + b + 2 * big) := by
  unfold profile at hp
  have he : (small - b) * (small + b + 2 * big) = 4 - (b + big) ^ 2 := by
    unfold small
    ring
  linarith only [hp, he]

theorem in_original_ellipse {a b : ℝ} (hb : 0 ≤ b) (hp : profile a b) :
    ellipse big small a b ≤ 1 := by
  have hbmax := profile_y hp
  have hh : big ^ 2 = small ^ 2 + 2 * big * small := by
    unfold small
    nlinarith only [big_sq]
  apply (ellipse_le_one_iff big_pos small_pos).mpr
  unfold profile at hp
  have hcore : a ^ 2 + b ^ 2 + 2 * big * b ≤ big ^ 2 := by
    nlinarith only [hp, big_sq]
  calc
    a ^ 2 * small ^ 2 + b ^ 2 * big ^ 2 =
        (a ^ 2 + b ^ 2) * small ^ 2 + (2 * big * small) * (b ^ 2) := by
      conv_lhs => rw [hh]
      ring
    _ ≤ (a ^ 2 + b ^ 2) * small ^ 2 + (2 * big * small) * (b * small) := by
      have hbsq : b ^ 2 ≤ b * small := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_left hbmax hb
      have hc : 0 ≤ 2 * big * small :=
        mul_nonneg (mul_nonneg (by norm_num) big_pos.le) small_pos.le
      exact add_le_add_right (mul_le_mul_of_nonneg_left hbsq hc) _
    _ = (a ^ 2 + b ^ 2 + 2 * big * b) * small ^ 2 := by ring
    _ ≤ big ^ 2 * small ^ 2 := mul_le_mul_of_nonneg_right hcore (sq_nonneg _)

theorem in_smaller_ellipses {a b : ℝ} (hb : 0 ≤ b) (hp : profile a b) :
    ellipse big (1 / 2) a b ≤ 1 ∨ ellipse (5 / 4) small a b ≤ 1 := by
  by_cases hsmall : b ≤ 1 / 3
  · left
    apply (ellipse_le_one_iff big_pos (by norm_num)).mpr
    unfold profile at hp
    have hlin : 0 ≤ 2 * big - 7 * b := by linarith [big_lower]
    rw [big_sq]
    nlinarith only [hp, big_sq, mul_nonneg hb hlin]
  · right
    push Not at hsmall
    apply (ellipse_le_one_iff (by norm_num) small_pos).mpr
    have hbmax := profile_y hp
    have hprod := compact_profile hp
    have hcoef : (small + b + 2 * big) * small ^ 2 ≤ (5 / 4 : ℝ) ^ 2 * (small + b) := by
      have harg : small + b + 2 * big ≤ 13 / 3 * (small + b) := by
        linarith [small_lower, big_upper]
      have hs2 : small ^ 2 ≤ (3 / 5 : ℝ) ^ 2 :=
        pow_le_pow_left₀ small_pos.le small_upper _
      calc
        (small + b + 2 * big) * small ^ 2 ≤ (13 / 3 * (small + b)) * (3 / 5) ^ 2 :=
          mul_le_mul harg hs2 (sq_nonneg _) (by linarith [small_pos])
        _ ≤ (5 / 4 : ℝ) ^ 2 * (small + b) := by linarith [small_pos]
    calc
      a ^ 2 * small ^ 2 + b ^ 2 * (5 / 4) ^ 2 ≤
          ((small - b) * (small + b + 2 * big)) * small ^ 2 + b ^ 2 * (5 / 4) ^ 2 :=
        add_le_add_left (mul_le_mul_of_nonneg_right hprod (sq_nonneg _)) _
      _ = (small - b) * ((small + b + 2 * big) * small ^ 2) + b ^ 2 * (5 / 4) ^ 2 := by ring
      _ ≤ (small - b) * ((5 / 4) ^ 2 * (small + b)) + b ^ 2 * (5 / 4) ^ 2 :=
        add_le_add_left (mul_le_mul_of_nonneg_left hcoef (sub_nonneg.mpr hbmax)) _
      _ = (5 / 4) ^ 2 * small ^ 2 := by ring

theorem interior_gap :
    ellipse big small (7 / 10 * big) (7 / 10 * small) < 1 ∧
      ¬ profile (7 / 10 * big) (7 / 10 * small) := by
  constructor
  · have he : ellipse big small (7 / 10 * big) (7 / 10 * small) = 49 / 50 := by
      unfold ellipse
      rw [mul_pow, mul_div_assoc, div_self (pow_ne_zero 2 (ne_of_gt big_pos)), mul_one,
        mul_pow, mul_div_assoc, div_self (pow_ne_zero 2 (ne_of_gt small_pos)), mul_one]
      norm_num
    rw [he]
    norm_num
  · unfold profile small
    have hh : (91 / 50 : ℝ) ≤ 7 / 10 * (2 - big) + big := by linarith [big_lower]
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 91 / 50) hh 2
    nlinarith only [hsq, big_sq]

end OMA.MO29000Profile

namespace OMA.MO29000Uniform

open scoped ENNReal

/-- Two exponential estimates with bases at most 97/100 fit under one with
base 99/100 at all dimensions from 100 onward. -/
theorem absorb_two {n : ℕ} (hn : 100 ≤ n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ 97 / 100) (hb' : b ≤ 97 / 100) :
    a ^ n + b ^ n ≤ (99 / 100 : ℝ) ^ n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h100 : 2 * (97 / 100 : ℝ) ^ 100 ≤ (99 / 100 : ℝ) ^ 100 := by norm_num
  calc
    a ^ (100 + j) + b ^ (100 + j) ≤ 2 * (97 / 100 : ℝ) ^ (100 + j) := by
      rw [two_mul]
      exact add_le_add (pow_le_pow_left₀ ha ha' _) (pow_le_pow_left₀ hb hb' _)
    _ = (2 * (97 / 100 : ℝ) ^ 100) * (97 / 100) ^ j := by
      rw [pow_add, mul_assoc]
    _ ≤ (99 / 100 : ℝ) ^ 100 * (99 / 100) ^ j :=
      mul_le_mul h100 (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
        (by positivity) (by positivity)
    _ = (99 / 100 : ℝ) ^ (100 + j) := by rw [pow_add]

/-- Strict bounds in the initial dimensions and a uniform exponential estimate
thereafter give a single exponential bound for all dimensions greater than one. -/
theorem uniform {v b : ℕ → ℝ≥0∞}
    (hbfinite : ∀ n, b n ≠ ∞) (hbpos : ∀ n, b n ≠ 0)
    (hstrict : ∀ n, 1 < n → v n < b n)
    (hlarge : ∀ n, 100 ≤ n → v n ≤ ENNReal.ofReal ((99 / 100 : ℝ) ^ n) * b n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n, 1 < n →
      v n ≤ ENNReal.ofReal ((1 - ε) ^ n) * b n := by
  let ratio (n : ℕ) := (v n).toReal / (b n).toReal
  have table : (Finset.Ico 2 100).Nonempty := ⟨2, by simp⟩
  let R := (Finset.Ico 2 100).sup' table ratio
  have hR : R < 1 := by
    apply (Finset.sup'_lt_iff table).mpr
    intro n hn
    have h : 1 < n := by have := (Finset.mem_Ico.mp hn).1; omega
    have hvfinite := ne_top_of_le_ne_top (hbfinite n) (hstrict n h).le
    have hdel := (ENNReal.toReal_lt_toReal hvfinite (hbfinite n)).mpr (hstrict n h)
    exact (div_lt_iff₀ (ENNReal.toReal_pos (hbpos n) (hbfinite n))).mpr (by simpa using hdel)
  let ε : ℝ := min (1 / 100) ((1 - R) / 100)
  have hε : 0 < ε := lt_min (by norm_num) (div_pos (sub_pos.mpr hR) (by norm_num))
  have hε' : ε ≤ (1 / 100 : ℝ) := min_le_left _ _
  have h99 : (99 / 100 : ℝ) ≤ 1 - ε := by linarith
  have hbase : 0 ≤ 1 - ε := by linarith
  refine ⟨ε, hε, fun n hn => ?_⟩
  by_cases h100 : 100 ≤ n
  · exact (hlarge n h100).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (by norm_num) h99 n)) le_rfl)
  · have hn100 : n < 100 := by omega
    have hRbound : ratio n ≤ R :=
      Finset.le_sup' ratio (Finset.mem_Ico.mpr ⟨by omega, hn100⟩)
    have hN : (n : ℝ) ≤ 100 := by exact_mod_cast hn100.le
    have he' : ε ≤ (1 - R) / 100 := min_le_right _ _
    have he100 : 100 * ε ≤ 1 - R := by
      simpa only [mul_comm (100 : ℝ) ε] using
        (le_div_iff₀ (by norm_num : 0 < (100 : ℝ))).mp he'
    have hεn : (n : ℝ) * ε ≤ 1 - R :=
      (mul_le_mul_of_nonneg_right hN hε.le).trans he100
    have hbern := one_add_mul_le_pow (a := -ε) (by linarith : -2 ≤ -ε) n
    have hp : R ≤ (1 - ε) ^ n := by
      rw [← sub_eq_add_neg] at hbern
      linarith only [hεn, hbern]
    have hden : 0 < (b n).toReal := ENNReal.toReal_pos (hbpos n) (hbfinite n)
    have hreal := (div_le_iff₀ hden).mp (hRbound.trans hp)
    have hvfinite : v n ≠ ∞ := ne_top_of_le_ne_top (hbfinite n) (hstrict n hn).le
    have hlo := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul (pow_nonneg hbase _), ENNReal.ofReal_toReal hvfinite,
      ENNReal.ofReal_toReal (hbfinite n)] at hlo
    exact hlo

end OMA.MO29000Uniform

namespace OMA.MO29000Volume

open MeasureTheory Set Finset Matrix Metric
open scoped ENNReal

abbrev Point (n : ℕ) := Fin n → ℝ

def posPart {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => max (x i) 0

def negPart {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => max (-(x i)) 0

noncomputable def weightedSquare {n : ℕ} (r s : ℝ) (x : Point n) : ℝ :=
  ∑ i, ((max (x i) 0)^2 / r^2 + (max (-(x i)) 0)^2 / s^2)

def orthant {n : ℕ} (b : Fin n → Bool) : Set (Point n) :=
  {x | ∀ i, if b i then 0 ≤ x i else x i ≤ 0}

def base {n : ℕ} : Set (Point n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, (x i)^2 ≤ 1}

def scale {n : ℕ} (r s : ℝ) (b : Fin n → Bool) (i : Fin n) : ℝ :=
  if b i then r else -s

def diag {n : ℕ} (d : Point n) (x : Point n) : Point n :=
  fun i => d i * x i

private theorem base_measurable {n : ℕ} : MeasurableSet (base (n := n)) := by
  have h : base = (⋂ i : Fin n, {x : Point n | 0 ≤ x i}) ∩
      {x : Point n | ∑ i, (x i)^2 ≤ 1} := by
    ext x
    simp [base]
  rw [h]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    apply measurableSet_le <;> fun_prop
  · apply measurableSet_le <;> fun_prop

private theorem diag_measurable {n : ℕ} (d : Point n) : Measurable (diag d) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_const.mul (measurable_pi_apply i)

private theorem volume_diag_preimage {n : ℕ} (d : Point n) (hd : ∀ i, d i ≠ 0)
    (T : Set (Point n)) (hT : MeasurableSet T) :
    volume (diag (fun i => (d i)⁻¹) ⁻¹' T) =
      ENNReal.ofReal (∏ i, |d i|) * volume T := by
  have hdet : det (diagonal (fun i => (d i)⁻¹)) ≠ 0 := by
    rw [det_diagonal]
    exact prod_ne_zero_iff.mpr (fun i _ => inv_ne_zero (hd i))
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  have hlin : (toLin' (diagonal (fun i => (d i)⁻¹)) : Point n → Point n) =
      diag (fun i => (d i)⁻¹) := by
    ext x i; simp [diag, Matrix.mulVec_diagonal]
  rw [hlin] at hmap
  rw [← Measure.map_apply (diag_measurable _) hT, hmap, Measure.smul_apply, smul_eq_mul]
  congr 2
  rw [det_diagonal, ← Finset.prod_inv_distrib]
  simp [Finset.abs_prod]

private theorem hyperplane_null {n : ℕ} (i : Fin n) :
    (volume : Measure (Point n)) {x | x i = 0} = 0 := by
  classical
  let t (j : Fin n) : Set ℝ := if j = i then {0} else univ
  have ht : {x : Point n | x i = 0} = univ.pi t := by
    ext x
    constructor
    · intro hx
      change x i = 0 at hx
      intro j _
      by_cases hj : j = i
      · simp [t, hj, hx]
      · simp [t, hj]
    · intro hx
      have hi := hx i trivial
      simpa [t] using hi
  rw [ht, volume_pi_pi]
  apply Finset.prod_eq_zero (mem_univ i)
  simp [t]

private theorem pieces {n : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (b : Fin n → Bool) :
    diag (fun i => (scale r s b i)⁻¹) ⁻¹' (base (n := n)) =
      {x | weightedSquare r s x ≤ 1} ∩ orthant b := by
  ext x
  have hsign : ∀ i, 0 ≤ (scale r s b i)⁻¹ * x i ↔
      if b i then 0 ≤ x i else x i ≤ 0 := by
    intro i
    cases hb : b i
    · have hn := not_congr (mul_pos_iff_of_pos_left (a := s⁻¹) (b := x i) (inv_pos.mpr hs))
      simpa [scale, hb, neg_mul, not_lt] using hn
    · simp [scale, hb, mul_nonneg_iff_of_pos_left, inv_pos.mpr hr]
  have hsum (h : x ∈ orthant b) :
      (∑ i, ((scale r s b i)⁻¹ * x i)^2) = weightedSquare r s x := by
    apply Finset.sum_congr rfl
    intro i _
    have hi := h i
    cases hb : b i
    · simp only [hb, Bool.false_eq_true, if_false] at hi
      simp [scale, hb, max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), div_eq_mul_inv,
        mul_pow, mul_comm]
    · simp only [hb, if_true] at hi
      simp [scale, hb, max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), div_eq_mul_inv,
        mul_pow, mul_comm]
  change ((∀ i, 0 ≤ (scale r s b i)⁻¹ * x i) ∧
    (∑ i, ((scale r s b i)⁻¹ * x i)^2) ≤ 1) ↔
    weightedSquare r s x ≤ 1 ∧ x ∈ orthant b
  constructor
  · rintro ⟨h, hl⟩
    have ho : x ∈ orthant b := fun i => (hsign i).mp (h i)
    exact ⟨hsum ho ▸ hl, ho⟩
  · rintro ⟨hl, ho⟩
    exact ⟨fun i => (hsign i).mpr (ho i), (hsum ho).symm ▸ hl⟩

private theorem all_pieces {n : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (volume : Measure (Point n)) {x | weightedSquare r s x ≤ 1} =
      ENNReal.ofReal ((r + s)^n) * volume (base (n := n)) := by
  classical
  let A (b : Fin n → Bool) := {x : Point n | weightedSquare r s x ≤ 1} ∩ orthant b
  have hcover : (⋃ b, A b) = {x | weightedSquare r s x ≤ 1} := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨b, hx⟩
      exact hx.1
    · intro hx
      refine ⟨fun i => decide (0 ≤ x i), hx, ?_⟩
      intro i
      by_cases hi : 0 ≤ x i
      · simp [hi]
      · simp [hi, le_of_lt (lt_of_not_ge hi)]
  have hdisj : Pairwise (Function.onFun (AEDisjoint (volume : Measure (Point n))) A) := by
    intro b c hbc
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := not_forall.mp (fun H => hbc (funext H))
    apply measure_mono_null _ (hyperplane_null i)
    rintro x ⟨hb, hc⟩
    have hb' := hb.2 i
    have hc' := hc.2 i
    change (if b i then 0 ≤ x i else x i ≤ 0) at hb'
    change (if c i then 0 ≤ x i else x i ≤ 0) at hc'
    change x i = 0
    cases hbi : b i <;> cases hci : c i
    · exact (hi (hbi.trans hci.symm)).elim
    · exact le_antisymm (by simpa [hbi] using hb') (by simpa [hci] using hc')
    · exact le_antisymm (by simpa [hci] using hc') (by simpa [hbi] using hb')
    · exact (hi (hbi.trans hci.symm)).elim
  have hmeas b : MeasurableSet (A b) := by
    rw [show A b = _ from (pieces hr hs b).symm]
    exact base_measurable.preimage (diag_measurable _)
  have hvolume b : volume (A b) =
      ENNReal.ofReal (∏ i : Fin n, |scale r s b i|) * volume (base (n := n)) := by
    rw [show A b = _ from (pieces hr hs b).symm]
    apply volume_diag_preimage _ _ _ base_measurable
    intro i
    cases hi : b i <;> simp [scale, hi, hr.ne', hs.ne']
  rw [← hcover, measure_iUnion₀ hdisj (fun b => (hmeas b).nullMeasurableSet), tsum_fintype]
  simp_rw [hvolume]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
    (fun b _ => Finset.prod_nonneg fun i _ => abs_nonneg _)]
  congr 2
  let f : Bool → ℝ := fun b => if b then r else s
  have hscale (b : Fin n → Bool) (i : Fin n) : |scale r s b i| = f (b i) := by
    cases hi : b i <;> simp [scale, f, hi, abs_of_pos hr, abs_of_pos hs]
  simp_rw [hscale]
  rw [← Fintype.sum_pow]
  simp [f]

private theorem euclidean_preimage {n : ℕ} {r s : ℝ} :
    WithLp.ofLp ⁻¹' {x : Point n | weightedSquare r s x ≤ 1} =
    {x : EuclideanSpace ℝ (Fin n) | ‖posPart x‖^2 / r^2 + ‖negPart x‖^2 / s^2 ≤ 1} := by
  ext x
  change (weightedSquare r s (WithLp.ofLp x) ≤ 1) ↔ _
  simp only [Set.mem_ofPred_eq, EuclideanSpace.real_norm_sq_eq, posPart, negPart]
  unfold weightedSquare
  rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]

private theorem one_preimage {n : ℕ} :
    WithLp.ofLp ⁻¹' {x : Point n | weightedSquare 1 1 x ≤ 1} =
    closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  ext x
  have hsum : weightedSquare 1 1 (WithLp.ofLp x) = ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, weightedSquare]
    apply Finset.sum_congr rfl
    intro i _
    change (max (x i) 0)^2 / (1:ℝ)^2 +
      (max (-(x i)) 0)^2 / (1:ℝ)^2 = (x i)^2
    by_cases hi : 0 ≤ x i
    · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
    · have hh := le_of_lt (lt_of_not_ge hi)
      simp [max_eq_right hh, max_eq_left (neg_nonneg.mpr hh)]
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hsum, Metric.mem_closedBall, dist_zero_right]
  exact (sq_le_one_iff₀ (norm_nonneg x))

theorem weightedVolume {n : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    volume {x : EuclideanSpace ℝ (Fin n) |
      ‖posPart x‖^2 / r^2 + ‖negPart x‖^2 / s^2 ≤ 1} =
    ENNReal.ofReal (((r + s) / 2)^n) *
      volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  classical
  have M := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  have hv (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      volume (WithLp.ofLp (p := 2) ⁻¹' {x : Point n | weightedSquare a b x ≤ 1}) =
        ENNReal.ofReal ((a+b)^n) * volume (base (n := n)) := by
    have hmeas : MeasurableSet {x : Point n | weightedSquare a b x ≤ 1} := by
      unfold weightedSquare
      apply measurableSet_le <;> fun_prop
    change volume ((MeasurableEquiv.toLp 2 (Point n)).symm ⁻¹' _) = _
    rw [← Measure.map_apply M.measurable hmeas, M.map_eq]
    exact all_pieces ha hb
  rw [← euclidean_preimage, ← one_preimage, hv r s hr hs,
    hv 1 1 zero_lt_one zero_lt_one, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ ((r + s) / 2)^n)]
  congr 2
  rw [← mul_pow]
  ring

end OMA.MO29000Volume

namespace OMA.MO29000Volume

theorem explicit_gap_norms {n : ℕ} (hn : 1 < n) :
    ∃ x : MO29000.Space n,
      ‖MO29000.posPart x‖ = 1 ∧ ‖MO29000.negPart x‖ = (3 / 8 : ℝ) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, hn⟩
  have hij : i ≠ j := by
    intro h
    have h' := congrArg Fin.val h
    exact Nat.zero_ne_one h'
  let x : MO29000.Space n := WithLp.toLp 2
    (fun k => if k = i then (1 : ℝ) else if k = j then -(3 / 8 : ℝ) else 0)
  have hx (k : Fin n) :
      x k = if k = i then (1 : ℝ) else if k = j then -(3 / 8 : ℝ) else 0 := rfl
  have hp : ‖MO29000.posPart x‖ ^ 2 = 1 := by
    rw [MO29000.norm_sq_posPart, Finset.sum_eq_single i]
    · norm_num [hx]
    · intro k _ hki
      by_cases hkj : k = j <;> norm_num [hx, hki, hkj, hij.symm, max_def]
    · simp
  have hq : ‖MO29000.negPart x‖ ^ 2 = (3 / 8 : ℝ) ^ 2 := by
    rw [MO29000.norm_sq_negPart, Finset.sum_eq_single j]
    · norm_num [hx, hij.symm, max_def]
    · intro k _ hkj
      by_cases hki : k = i <;> norm_num [hx, hki, hkj, hij, max_def]
    · simp
  refine ⟨x, ?_, ?_⟩
  · exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) (by decide : 2 ≠ 0)).mp (by simpa using hp)
  · exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) (by decide : 2 ≠ 0)).mp hq

end OMA.MO29000Volume

namespace OMA.MO29000Bounds

open OMA.MO29000 OMA.MO29000Profile OMA.MO29000Uniform
open Metric MeasureTheory Set
open scoped ENNReal Pointwise

private noncomputable def region (n : ℕ) (r s : ℝ) : Set (Space n) :=
  {x | ellipse r s ‖posPart x‖ ‖negPart x‖ ≤ 1}

private noncomputable def ballVolume (n : ℕ) : ℝ≥0∞ :=
  volume (closedBall (0 : Space n) 1)

private theorem ballVolume_finite (n : ℕ) : ballVolume n ≠ ∞ :=
  measure_closedBall_lt_top.ne

private theorem ballVolume_pos (n : ℕ) : ballVolume n ≠ 0 :=
  (measure_closedBall_pos volume (0 : Space n) (by norm_num : (0 : ℝ) < 1)).ne'

private theorem volume_region {n : ℕ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    volume (region n r s) = ENNReal.ofReal (((r + s) / 2) ^ n) * ballVolume n :=
  OMA.MO29000Volume.weightedVolume hr hs

private theorem gap_pair : ellipse big small 1 (3 / 8) < 1 ∧ ¬ profile 1 (3 / 8) := by
  have hdiv : (3 / 8 : ℝ) / small ≤ 21 / 32 := by
    apply (div_le_iff₀ small_pos).mpr
    linarith [small_lower]
  have hs := pow_le_pow_left₀ (a := (3 / 8 : ℝ) / small)
    (div_nonneg (by norm_num) small_pos.le) hdiv 2
  rw [div_pow] at hs
  constructor
  · unfold ellipse
    rw [big_sq]
    norm_num at hs ⊢
    linarith
  · unfold profile
    have ht : (71 / 40 : ℝ) ≤ 3 / 8 + big := by linarith [big_lower]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 71 / 40) ht 2
    nlinarith

private theorem strict_volume {n : ℕ}
    (hex : ∃ x : Space n, ‖posPart x‖ = 1 ∧ ‖negPart x‖ = 3 / 8) :
    volume (body n) < ballVolume n := by
  let P (x : Space n) : ℝ := ‖posPart x‖ ^ 2 + (‖negPart x‖ + big) ^ 2
  let E (x : Space n) : ℝ := ellipse big small ‖posPart x‖ ‖negPart x‖
  let U : Set (Space n) := {x | E x < 1} ∩ {x | 4 < P x}
  have hP : Continuous P :=
    ((continuous_posPart n).norm.pow 2).add (((continuous_negPart n).norm.add continuous_const).pow 2)
  have hE : Continuous E :=
    (((continuous_posPart n).norm.pow 2).div_const _).add (((continuous_negPart n).norm.pow 2).div_const _)
  have hU : IsOpen U := (isOpen_lt hE continuous_const).inter (isOpen_lt continuous_const hP)
  obtain ⟨x, hx, hy⟩ := hex
  have hxU : x ∈ U := by
    change E x < 1 ∧ 4 < P x
    dsimp [E, P]
    rw [hx, hy]
    exact ⟨gap_pair.1, lt_of_not_ge gap_pair.2⟩
  have hd : Disjoint (body n) U := Set.disjoint_left.mpr fun y hy hyU =>
    not_lt_of_ge ((mem_body_iff y).mp hy) hyU.2
  have hsub : body n ∪ U ⊆ region n big small := by
    rintro y (hy | hy)
    · exact in_original_ellipse (norm_nonneg _) ((mem_body_iff y).mp hy)
    · exact (show E y < 1 from hy.1).le
  have hvol : volume (region n big small) = ballVolume n := by
    rw [volume_region big_pos small_pos]
    simp [small]
  have hbfin : volume (body n) ≠ ∞ :=
    ne_top_of_le_ne_top (ballVolume_finite n) (hvol ▸ measure_mono (fun y hy => hsub (Or.inl hy)))
  calc
    volume (body n) < volume (body n) + volume U :=
      ENNReal.lt_add_right hbfin (hU.measure_pos volume ⟨x, hxU⟩).ne'
    _ = volume (body n ∪ U) := (measure_union hd hU.measurableSet).symm
    _ ≤ volume (region n big small) := measure_mono hsub
    _ = ballVolume n := hvol

private theorem large_volume (n : ℕ) (hn : 100 ≤ n) :
    volume (body n) ≤ ENNReal.ofReal ((99 / 100 : ℝ) ^ n) * ballVolume n := by
  let a : ℝ := (big + 1 / 2) / 2
  let b : ℝ := (5 / 4 + small) / 2
  have ha : 0 ≤ a := by change 0 ≤ (big + 1 / 2) / 2; linarith [big_pos]
  have hb : 0 ≤ b := by change 0 ≤ (5 / 4 + small) / 2; linarith [small_pos]
  have hab : a ^ n + b ^ n ≤ (99 / 100 : ℝ) ^ n :=
    absorb_two hn ha hb (by dsimp [a]; linarith [big_upper])
      (by dsimp [b]; linarith [small_upper])
  have hsub : body n ⊆ region n big (1 / 2) ∪ region n (5 / 4) small := by
    intro x hx
    exact in_smaller_ellipses (norm_nonneg _) ((mem_body_iff x).mp hx)
  calc
    volume (body n) ≤ volume (region n big (1 / 2) ∪ region n (5 / 4) small) := measure_mono hsub
    _ ≤ volume (region n big (1 / 2)) + volume (region n (5 / 4) small) := measure_union_le _ _
    _ = ENNReal.ofReal (a ^ n + b ^ n) * ballVolume n := by
      rw [volume_region big_pos (by norm_num), volume_region (by norm_num) small_pos]
      change ENNReal.ofReal (a ^ n) * ballVolume n +
        ENNReal.ofReal (b ^ n) * ballVolume n = _
      rw [← add_mul, ENNReal.ofReal_add (pow_nonneg ha _) (pow_nonneg hb _)]
    _ ≤ ENNReal.ofReal ((99 / 100 : ℝ) ^ n) * ballVolume n :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hab) le_rfl

theorem half_body_volume :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 < n →
      volume (halfBody n) ≤ ENNReal.ofReal ((1 - ε) ^ n) * volume (closedBall (0 : Space n) (1 / 2)) := by
  obtain ⟨ε, he, h⟩ := uniform (v := fun n => volume (body n)) (b := ballVolume)
    ballVolume_finite ballVolume_pos
      (fun _ hn => strict_volume (OMA.MO29000Volume.explicit_gap_norms hn)) large_volume
  refine ⟨ε, he, fun n hn => ?_⟩
  exact halfBody_volume_transfer n _ (h n hn)

end OMA.MO29000Bounds

open OMA.MO29000 OMA.MO29000Bounds in
theorem OMA.solution : type_of% @OMA.S_mo_29000.main := by
  obtain ⟨ε, he, hv⟩ := half_body_volume
  exact ⟨ε, he, fun n hn => ⟨halfBody n, halfBody_constant_width n, hv n hn⟩⟩
