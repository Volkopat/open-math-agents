import OMAStatements.S_mo_201359
import Mathlib

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace MO201359Proof

abbrev Plane := OMA.S_mo_201359.Plane

noncomputable def mkP (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

def px (p : Plane) : ℝ := p.ofLp 0
def py (p : Plane) : ℝ := p.ofLp 1

@[simp] lemma px_mkP (x y : ℝ) : px (mkP x y) = x := rfl
@[simp] lemma py_mkP (x y : ℝ) : py (mkP x y) = y := rfl

lemma mkP_px_py (p : Plane) : mkP (px p) (py p) = p := by
  ext i
  fin_cases i <;> rfl

lemma plane_ext {p q : Plane} (hx : px p = px q) (hy : py p = py q) : p = q := by
  rw [← mkP_px_py p, ← mkP_px_py q, hx, hy]

@[simp] lemma px_add (p q : Plane) : px (p + q) = px p + px q := rfl
@[simp] lemma py_add (p q : Plane) : py (p + q) = py p + py q := rfl
@[simp] lemma px_sub (p q : Plane) : px (p - q) = px p - px q := rfl
@[simp] lemma py_sub (p q : Plane) : py (p - q) = py p - py q := rfl
@[simp] lemma px_neg (p : Plane) : px (-p) = -px p := rfl
@[simp] lemma py_neg (p : Plane) : py (-p) = -py p := rfl
@[simp] lemma px_smul (c : ℝ) (p : Plane) : px (c • p) = c * px p := rfl
@[simp] lemma py_smul (c : ℝ) (p : Plane) : py (c • p) = c * py p := rfl
@[simp] lemma px_zero : px (0 : Plane) = 0 := rfl
@[simp] lemma py_zero : py (0 : Plane) = 0 := rfl

lemma inner_plane (u v : Plane) : inner ℝ u v = px u * px v + py u * py v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two, px, py, mul_comm]

lemma norm_sq_plane (u : Plane) : ‖u‖ ^ 2 = px u ^ 2 + py u ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity)]
  simp [px, py]

lemma dist_sq_plane (u v : Plane) : dist u v ^ 2 = (px u - px v) ^ 2 + (py u - py v) ^ 2 := by
  rw [dist_eq_norm, norm_sq_plane]
  rfl

lemma dist_le_of_sq_le {u v : Plane} {r : ℝ} (hr : 0 ≤ r)
    (h : (px u - px v) ^ 2 + (py u - py v) ^ 2 ≤ r ^ 2) : dist u v ≤ r := by
  have h1 : dist u v ^ 2 ≤ r ^ 2 := by rwa [dist_sq_plane]
  nlinarith [dist_nonneg (x := u) (y := v)]

lemma abs_px_le_norm (u : Plane) : |px u| ≤ ‖u‖ := by
  have h := norm_sq_plane u
  have h2 : px u ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith [sq_nonneg (py u)]
  nlinarith [abs_nonneg (px u), norm_nonneg u, sq_abs (px u)]

lemma abs_py_le_norm (u : Plane) : |py u| ≤ ‖u‖ := by
  have h := norm_sq_plane u
  have h2 : py u ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith [sq_nonneg (px u)]
  nlinarith [abs_nonneg (py u), norm_nonneg u, sq_abs (py u)]

lemma continuous_px : Continuous px := by
  have h : px = fun p : Plane => (WithLp.equiv 2 (Fin 2 → ℝ) p) 0 := rfl
  rw [h]
  exact (continuous_apply 0).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))

lemma continuous_py : Continuous py := by
  have h : py = fun p : Plane => (WithLp.equiv 2 (Fin 2 → ℝ) p) 1 := rfl
  rw [h]
  exact (continuous_apply 1).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))

lemma continuous_inner_left (u : Plane) : Continuous (fun x : Plane => inner ℝ u x) := by
  have h : (fun x : Plane => inner ℝ u x) = fun x => px u * px x + py u * py x := by
    ext x; exact inner_plane u x
  rw [h]
  exact (continuous_const.mul continuous_px).add (continuous_const.mul continuous_py)

lemma finrank_plane : Module.finrank ℝ Plane = 2 := by
  simp [Plane]

lemma measurableSet_side {C : Set Plane} (hC : MeasurableSet C) (u : Plane) (t : ℝ) :
    MeasurableSet (OMA.S_mo_201359.side C u t) :=
  hC.inter (isClosed_le (continuous_inner_left u) continuous_const).measurableSet

lemma measurableSet_opposite {C : Set Plane} (hC : MeasurableSet C) (u : Plane) (t : ℝ) :
    MeasurableSet (OMA.S_mo_201359.opposite C u t) :=
  hC.inter (isClosed_le continuous_const (continuous_inner_left u)).measurableSet

/-! ### Measure-preserving equivalence `Plane ≃ᵐ ℝ × ℝ` and Tonelli region formulas -/

noncomputable def planeToProd : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

@[simp] lemma planeToProd_apply (p : Plane) : planeToProd p = (px p, py p) := rfl

lemma measurePreserving_planeToProd :
    MeasurePreserving planeToProd (volume : Measure Plane) (volume : Measure (ℝ × ℝ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm volume volume :=
    PiLp.volume_preserving_ofLp (Fin 2)
  have h2 : MeasurePreserving (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) volume volume :=
    MeasureTheory.volume_preserving_finTwoArrow ℝ
  exact h2.comp h1

lemma volume_preimage_planeToProd (S : Set (ℝ × ℝ)) :
    (volume : Measure Plane) (planeToProd ⁻¹' S) = volume S :=
  measurePreserving_planeToProd.measure_preimage_equiv S

lemma volume_region_x (a b : ℝ) (hab : a ≤ b) (lo hi : ℝ → ℝ)
    (hlo : Continuous lo) (hhi : Continuous hi) (hle : ∀ x ∈ Icc a b, lo x ≤ hi x) :
    (volume : Measure Plane)
      {p : Plane | a ≤ px p ∧ px p ≤ b ∧ lo (px p) ≤ py p ∧ py p ≤ hi (px p)} =
    ENNReal.ofReal (∫ x in a..b, (hi x - lo x)) := by
  let S : Set (ℝ × ℝ) := {z | a ≤ z.1 ∧ z.1 ≤ b ∧ lo z.1 ≤ z.2 ∧ z.2 ≤ hi z.1}
  have hpre : {p : Plane | a ≤ px p ∧ px p ≤ b ∧ lo (px p) ≤ py p ∧ py p ≤ hi (px p)} =
      planeToProd ⁻¹' S := rfl
  rw [hpre, volume_preimage_planeToProd]
  have hS_meas : MeasurableSet S := by
    have h1 : MeasurableSet {z : ℝ × ℝ | a ≤ z.1} := (isClosed_le continuous_const continuous_fst).measurableSet
    have h2 : MeasurableSet {z : ℝ × ℝ | z.1 ≤ b} := (isClosed_le continuous_fst continuous_const).measurableSet
    have h3 : MeasurableSet {z : ℝ × ℝ | lo z.1 ≤ z.2} :=
      (isClosed_le (hlo.comp continuous_fst) continuous_snd).measurableSet
    have h4 : MeasurableSet {z : ℝ × ℝ | z.2 ≤ hi z.1} :=
      (isClosed_le continuous_snd (hhi.comp continuous_fst)).measurableSet
    exact h1.inter (h2.inter (h3.inter h4))
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl]
  rw [Measure.prod_apply hS_meas]
  have hsec : ∀ x : ℝ, (volume : Measure ℝ) (Prod.mk x ⁻¹' S) =
      if x ∈ Icc a b then ENNReal.ofReal (hi x - lo x) else 0 := by
    intro x
    by_cases hx : x ∈ Icc a b
    · rw [if_pos hx]
      have hset : Prod.mk x ⁻¹' S = Icc (lo x) (hi x) := by
        ext y; simp [S, hx.1, hx.2]
      rw [hset, Real.volume_Icc]
    · rw [if_neg hx]
      have hset : Prod.mk x ⁻¹' S = ∅ := by
        ext y; simp only [mem_preimage, mem_empty_iff_false, iff_false]
        intro h; exact hx ⟨h.1, h.2.1⟩
      rw [hset, measure_empty]
  simp_rw [hsec]
  have h1 : ∫⁻ x, (if x ∈ Icc a b then ENNReal.ofReal (hi x - lo x) else 0) ∂volume =
      ∫⁻ x in Icc a b, ENNReal.ofReal (hi x - lo x) ∂volume := by
    rw [← lintegral_indicator measurableSet_Icc]
    congr 1; ext x; by_cases hx : x ∈ Icc a b <;> simp [hx]
  rw [h1]
  have hint : IntegrableOn (fun x => hi x - lo x) (Icc a b) volume :=
    (hhi.sub hlo).continuousOn.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Icc fun x hx => sub_nonneg.mpr (hle x hx))]
  congr 1
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

lemma volume_region_y (a b : ℝ) (hab : a ≤ b) (lo hi : ℝ → ℝ)
    (hlo : Continuous lo) (hhi : Continuous hi) (hle : ∀ y ∈ Icc a b, lo y ≤ hi y) :
    (volume : Measure Plane)
      {p : Plane | a ≤ py p ∧ py p ≤ b ∧ lo (py p) ≤ px p ∧ px p ≤ hi (py p)} =
    ENNReal.ofReal (∫ y in a..b, (hi y - lo y)) := by
  let S : Set (ℝ × ℝ) := {z | a ≤ z.2 ∧ z.2 ≤ b ∧ lo z.2 ≤ z.1 ∧ z.1 ≤ hi z.2}
  have hpre : {p : Plane | a ≤ py p ∧ py p ≤ b ∧ lo (py p) ≤ px p ∧ px p ≤ hi (py p)} =
      planeToProd ⁻¹' S := rfl
  rw [hpre, volume_preimage_planeToProd]
  have hS_meas : MeasurableSet S := by
    have h1 : MeasurableSet {z : ℝ × ℝ | a ≤ z.2} := (isClosed_le continuous_const continuous_snd).measurableSet
    have h2 : MeasurableSet {z : ℝ × ℝ | z.2 ≤ b} := (isClosed_le continuous_snd continuous_const).measurableSet
    have h3 : MeasurableSet {z : ℝ × ℝ | lo z.2 ≤ z.1} :=
      (isClosed_le (hlo.comp continuous_snd) continuous_fst).measurableSet
    have h4 : MeasurableSet {z : ℝ × ℝ | z.1 ≤ hi z.2} :=
      (isClosed_le continuous_fst (hhi.comp continuous_snd)).measurableSet
    exact h1.inter (h2.inter (h3.inter h4))
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl]
  rw [Measure.prod_apply_symm hS_meas]
  have hsec : ∀ y : ℝ, (volume : Measure ℝ) ((fun x => (x, y)) ⁻¹' S) =
      if y ∈ Icc a b then ENNReal.ofReal (hi y - lo y) else 0 := by
    intro y
    by_cases hy : y ∈ Icc a b
    · rw [if_pos hy]
      have hset : (fun x => (x, y)) ⁻¹' S = Icc (lo y) (hi y) := by
        ext x; simp [S, hy.1, hy.2]
      rw [hset, Real.volume_Icc]
    · rw [if_neg hy]
      have hset : (fun x => (x, y)) ⁻¹' S = ∅ := by
        ext x; simp only [mem_preimage, mem_empty_iff_false, iff_false]
        intro h; exact hy ⟨h.1, h.2.1⟩
      rw [hset, measure_empty]
  simp_rw [hsec]
  have h1 : ∫⁻ y, (if y ∈ Icc a b then ENNReal.ofReal (hi y - lo y) else 0) ∂volume =
      ∫⁻ y in Icc a b, ENNReal.ofReal (hi y - lo y) ∂volume := by
    rw [← lintegral_indicator measurableSet_Icc]
    congr 1; ext y; by_cases hy : y ∈ Icc a b <;> simp [hy]
  rw [h1]
  have hint : IntegrableOn (fun y => hi y - lo y) (Icc a b) volume :=
    (hhi.sub hlo).continuousOn.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Icc fun y hy => sub_nonneg.mpr (hle y hy))]
  congr 1
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

lemma volume_rect (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    (volume : Measure Plane)
      {p : Plane | a ≤ px p ∧ px p ≤ b ∧ c ≤ py p ∧ py p ≤ d} =
    ENNReal.ofReal ((b - a) * (d - c)) := by
  rw [volume_region_x a b hab (fun _ => c) (fun _ => d) continuous_const continuous_const
    (fun _ _ => hcd)]
  simp only [intervalIntegral.integral_const, smul_eq_mul]

lemma integral_linear (a b c d : ℝ) :
    ∫ x in a..b, (c * x + d) = c * ((b ^ 2 - a ^ 2) / 2) + d * (b - a) := by
  have hint1 : IntervalIntegrable (fun x : ℝ => c * x) volume a b :=
    (by fun_prop : Continuous fun x : ℝ => c * x).intervalIntegrable a b
  rw [intervalIntegral.integral_add hint1 intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-! ### Measure zero of lines, bisection equivalence, and IVT existence -/

lemma volume_line_zero (v : Plane) (hv : v ≠ 0) (s : ℝ) :
    (volume : Measure Plane) {x : Plane | inner ℝ v x = s} = 0 := by
  by_cases hne : ({x : Plane | inner ℝ v x = s}).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    have hx₀' : inner ℝ v x₀ = s := hx₀
    let A : AffineSubspace ℝ Plane := AffineSubspace.mk' x₀ (Submodule.span ℝ {v})ᗮ
    have hA_coe : (A : Set Plane) = {x : Plane | inner ℝ v x = s} := by
      ext x
      show x ∈ A ↔ inner ℝ v x = s
      rw [AffineSubspace.mem_mk', vsub_eq_sub, Submodule.mem_orthogonal_singleton_iff_inner_right,
        inner_sub_right, hx₀']
      constructor <;> intro h <;> linarith
    have hne_top : A ≠ ⊤ := by
      intro htop
      have hv_mem : x₀ + v ∈ (A : Set Plane) := by rw [htop]; trivial
      rw [hA_coe] at hv_mem
      have h1 : inner ℝ v (x₀ + v) = s := hv_mem
      rw [inner_add_right, hx₀'] at h1
      have h2 : inner ℝ v v = 0 := by linarith
      exact hv (inner_self_eq_zero.mp h2)
    rw [← hA_coe]
    exact Measure.addHaar_affineSubspace volume A hne_top
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]

lemma volume_side_add_opposite (C : Set Plane) (hC : MeasurableSet C) (u : Plane) (hu : u ≠ 0) (t : ℝ) :
    volume (OMA.S_mo_201359.side C u t) + volume (OMA.S_mo_201359.opposite C u t) = volume C := by
  have h2 : MeasurableSet (OMA.S_mo_201359.opposite C u t) := measurableSet_opposite hC u t
  have hunion : OMA.S_mo_201359.side C u t ∪ OMA.S_mo_201359.opposite C u t = C := by
    ext x
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases le_total (inner ℝ u x) t with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hinter : volume (OMA.S_mo_201359.side C u t ∩ OMA.S_mo_201359.opposite C u t) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (volume_line_zero u hu t)
    exact le_antisymm hx.1.2 hx.2.2
  have h := measure_union_add_inter (μ := volume) (OMA.S_mo_201359.side C u t) h2
  rw [hunion, hinter, add_zero] at h
  exact h.symm

lemma bisects_iff_toReal (C : Set Plane) (hC : IsCompact C) (u : Plane) (hu : u ≠ 0) (t : ℝ) :
    OMA.S_mo_201359.bisects C u t ↔
      (volume (OMA.S_mo_201359.side C u t)).toReal = (volume C).toReal / 2 := by
  have hfin : volume C ≠ ⊤ := hC.measure_lt_top.ne
  have hsum := volume_side_add_opposite C hC.measurableSet u hu t
  have hfin1 : volume (OMA.S_mo_201359.side C u t) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono fun x hx => hx.1)
  have hfin2 : volume (OMA.S_mo_201359.opposite C u t) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono fun x hx => hx.1)
  have hsumR : (volume (OMA.S_mo_201359.side C u t)).toReal +
      (volume (OMA.S_mo_201359.opposite C u t)).toReal = (volume C).toReal := by
    rw [← ENNReal.toReal_add hfin1 hfin2, hsum]
  constructor
  · rintro ⟨_, heq⟩
    have heqR : (volume (OMA.S_mo_201359.side C u t)).toReal =
        (volume (OMA.S_mo_201359.opposite C u t)).toReal := congrArg ENNReal.toReal heq
    linarith
  · intro hhalf
    refine ⟨hu, ?_⟩
    have h2 : (volume (OMA.S_mo_201359.side C u t)).toReal =
        (volume (OMA.S_mo_201359.opposite C u t)).toReal := by linarith
    exact (ENNReal.toReal_eq_toReal_iff' hfin1 hfin2).mp h2

/-- Linear isometry mapping unit vector `u / ‖u‖` to `e₁ = (1, 0)`. -/
noncomputable def rotEquiv (u : Plane) (hu : u ≠ 0) : Plane ≃ₗᵢ[ℝ] Plane := by
  let n := ‖u‖
  have hn : 0 < n := norm_pos_iff.mpr hu
  let a := px u / n
  let b := py u / n
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have hns := norm_sq_plane u
    have hn2 : n ^ 2 ≠ 0 := by positivity
    dsimp [a, b]
    field_simp
    linarith
  let f : Plane →ₗ[ℝ] Plane :=
    { toFun := fun p => mkP (a * px p + b * py p) (-b * px p + a * py p)
      map_add' := fun p q => by apply plane_ext <;> simp <;> ring
      map_smul' := fun c p => by apply plane_ext <;> simp <;> ring }
  let g : Plane →ₗ[ℝ] Plane :=
    { toFun := fun p => mkP (a * px p - b * py p) (b * px p + a * py p)
      map_add' := fun p q => by apply plane_ext <;> simp <;> ring
      map_smul' := fun c p => by apply plane_ext <;> simp <;> ring }
  refine
    { toLinearEquiv :=
        { toLinearMap := f
          invFun := g
          left_inv := fun p => by
            apply plane_ext
            · show a * (a * px p + b * py p) - b * (-b * px p + a * py p) = px p
              calc a * (a * px p + b * py p) - b * (-b * px p + a * py p)
                  = (a ^ 2 + b ^ 2) * px p := by ring
                _ = px p := by rw [hab, one_mul]
            · show b * (a * px p + b * py p) + a * (-b * px p + a * py p) = py p
              calc b * (a * px p + b * py p) + a * (-b * px p + a * py p)
                  = (a ^ 2 + b ^ 2) * py p := by ring
                _ = py p := by rw [hab, one_mul]
          right_inv := fun p => by
            apply plane_ext
            · show a * (a * px p - b * py p) + b * (b * px p + a * py p) = px p
              calc a * (a * px p - b * py p) + b * (b * px p + a * py p)
                  = (a ^ 2 + b ^ 2) * px p := by ring
                _ = px p := by rw [hab, one_mul]
            · show -b * (a * px p - b * py p) + a * (b * px p + a * py p) = py p
              calc -b * (a * px p - b * py p) + a * (b * px p + a * py p)
                  = (a ^ 2 + b ^ 2) * py p := by ring
                _ = py p := by rw [hab, one_mul] }
      norm_map' := fun p => by
        change ‖f p‖ = ‖p‖
        have hsq : ‖f p‖ ^ 2 = ‖p‖ ^ 2 := by
          rw [norm_sq_plane, norm_sq_plane]
          show (a * px p + b * py p) ^ 2 + (-b * px p + a * py p) ^ 2 = px p ^ 2 + py p ^ 2
          calc (a * px p + b * py p) ^ 2 + (-b * px p + a * py p) ^ 2
              = (a ^ 2 + b ^ 2) * (px p ^ 2 + py p ^ 2) := by ring
            _ = px p ^ 2 + py p ^ 2 := by rw [hab, one_mul]
        nlinarith [norm_nonneg (f p), norm_nonneg p] }

lemma rotEquiv_px (u : Plane) (hu : u ≠ 0) (p : Plane) :
    px (rotEquiv u hu p) = inner ℝ u p / ‖u‖ := by
  change px u / ‖u‖ * px p + py u / ‖u‖ * py p = inner ℝ u p / ‖u‖
  rw [inner_plane]
  ring

lemma continuous_side_vol (C : Set Plane) (hC : IsCompact C) (v : Plane) (hv : v ≠ 0) :
    Continuous (fun s : ℝ => (volume (OMA.S_mo_201359.side C v s)).toReal) := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Plane)
  let R' := max R 1
  have hR'_pos : 0 < R' := by positivity
  have hCR : ∀ p ∈ C, ‖p‖ ≤ R' := fun p hp => by
    have := hR hp
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    exact le_trans this (le_max_left R 1)
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let K : NNReal := ⟨2 * R' / ‖v‖, by positivity⟩
  have hKval : (K : ℝ) = 2 * R' / ‖v‖ := rfl
  refine (LipschitzWith.of_dist_le_mul (K := K) fun s₁ s₂ => ?_).continuous
  have hstep : ∀ a b : ℝ, a ≤ b →
      (volume (OMA.S_mo_201359.side C v b)).toReal -
      (volume (OMA.S_mo_201359.side C v a)).toReal ≤ (2 * R' / ‖v‖) * (b - a) := by
    intro a b hab
    have hsub : OMA.S_mo_201359.side C v a ⊆ OMA.S_mo_201359.side C v b :=
      fun p hp => ⟨hp.1, le_trans hp.2 hab⟩
    have hfin_b : volume (OMA.S_mo_201359.side C v b) ≠ ⊤ :=
      ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono fun p hp => hp.1)
    have hfin_a : volume (OMA.S_mo_201359.side C v a) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin_b (measure_mono hsub)
    have hdiff : volume (OMA.S_mo_201359.side C v b) =
        volume (OMA.S_mo_201359.side C v a) +
        volume (OMA.S_mo_201359.side C v b \ OMA.S_mo_201359.side C v a) := by
      have hma := measurableSet_side hC.measurableSet v a
      have hmb := measurableSet_side hC.measurableSet v b
      rw [← measure_union disjoint_sdiff_self_right (hmb.diff hma), union_sdiff_cancel hsub]
    have hfin_d : volume (OMA.S_mo_201359.side C v b \ OMA.S_mo_201359.side C v a) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin_b (measure_mono sdiff_subset)
    have hd_eq : (volume (OMA.S_mo_201359.side C v b)).toReal -
        (volume (OMA.S_mo_201359.side C v a)).toReal =
        (volume (OMA.S_mo_201359.side C v b \ OMA.S_mo_201359.side C v a)).toReal := by
      have := congrArg ENNReal.toReal hdiff
      rw [ENNReal.toReal_add hfin_a hfin_d] at this
      linarith
    rw [hd_eq]
    let Φ := rotEquiv v hv
    let Rect : Set Plane := {q | a / ‖v‖ ≤ px q ∧ px q ≤ b / ‖v‖ ∧ -R' ≤ py q ∧ py q ≤ R'}
    have hRect_meas : MeasurableSet Rect :=
      (isClosed_le continuous_const continuous_px).measurableSet.inter
        ((isClosed_le continuous_px continuous_const).measurableSet.inter
        ((isClosed_le continuous_const continuous_py).measurableSet.inter
        (isClosed_le continuous_py continuous_const).measurableSet))
    have hinc : OMA.S_mo_201359.side C v b \ OMA.S_mo_201359.side C v a ⊆ Φ ⁻¹' Rect := by
      intro p hp
      have hpC : p ∈ C := hp.1.1
      have hpb : inner ℝ v p ≤ b := hp.1.2
      have hpa : a < inner ℝ v p := by
        by_contra h
        push Not at h
        exact hp.2 ⟨hpC, h⟩
      have hnorm : ‖Φ p‖ ≤ R' := by rw [Φ.norm_map]; exact hCR p hpC
      have hpy := abs_le.mp (le_trans (abs_py_le_norm (Φ p)) hnorm)
      refine ⟨?_, ?_, hpy.1, hpy.2⟩
      · rw [rotEquiv_px]; exact div_le_div_of_nonneg_right hpa.le hvn.le
      · rw [rotEquiv_px]; exact div_le_div_of_nonneg_right hpb hvn.le
    have hvol_rect : volume (Φ ⁻¹' Rect) = ENNReal.ofReal ((b / ‖v‖ - a / ‖v‖) * (R' - (-R'))) := by
      rw [Φ.measurePreserving.measure_preimage hRect_meas.nullMeasurableSet]
      exact volume_rect (a / ‖v‖) (b / ‖v‖) (-R') R'
        (div_le_div_of_nonneg_right hab hvn.le) (by linarith)
    have hle_m : volume (OMA.S_mo_201359.side C v b \ OMA.S_mo_201359.side C v a) ≤
        ENNReal.ofReal ((2 * R' / ‖v‖) * (b - a)) := by
      calc volume (OMA.S_mo_201359.side C v b \ OMA.S_mo_201359.side C v a)
          ≤ volume (Φ ⁻¹' Rect) := measure_mono hinc
        _ = ENNReal.ofReal ((b / ‖v‖ - a / ‖v‖) * (R' - (-R'))) := hvol_rect
        _ = ENNReal.ofReal ((2 * R' / ‖v‖) * (b - a)) := by congr 1; ring
    have hnn : 0 ≤ (2 * R' / ‖v‖) * (b - a) := mul_nonneg (by positivity) (sub_nonneg.mpr hab)
    calc (volume (OMA.S_mo_201359.side C v b \ OMA.S_mo_201359.side C v a)).toReal
        ≤ (ENNReal.ofReal ((2 * R' / ‖v‖) * (b - a))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle_m
      _ = (2 * R' / ‖v‖) * (b - a) := ENNReal.toReal_ofReal hnn
  rw [Real.dist_eq, Real.dist_eq, hKval]
  rcases le_total s₁ s₂ with h | h
  · have hmono : (volume (OMA.S_mo_201359.side C v s₁)).toReal ≤
        (volume (OMA.S_mo_201359.side C v s₂)).toReal :=
      ENNReal.toReal_mono (ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono fun p hp => hp.1))
        (measure_mono fun p hp => ⟨hp.1, le_trans hp.2 h⟩)
    rw [abs_of_nonpos (sub_nonpos.mpr hmono), abs_of_nonpos (sub_nonpos.mpr h)]
    have := hstep s₁ s₂ h
    linarith
  · have hmono : (volume (OMA.S_mo_201359.side C v s₂)).toReal ≤
        (volume (OMA.S_mo_201359.side C v s₁)).toReal :=
      ENNReal.toReal_mono (ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono fun p hp => hp.1))
        (measure_mono fun p hp => ⟨hp.1, le_trans hp.2 h⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr h)]
    exact hstep s₂ s₁ h

lemma exists_bisects (C : Set Plane) (hC : IsCompact C) (v : Plane) (hv : v ≠ 0) :
    ∃ s : ℝ, OMA.S_mo_201359.bisects C v s := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Plane)
  let M := ‖v‖ * max R 0 + 1
  have hM : 0 < M := by positivity
  let F : ℝ → ℝ := fun s => (volume (OMA.S_mo_201359.side C v s)).toReal
  have hcont : Continuous F := continuous_side_vol C hC v hv
  have hF_lo : F (-M) = 0 := by
    have hempty : OMA.S_mo_201359.side C v (-M) = ∅ := by
      ext p
      simp only [OMA.S_mo_201359.side, mem_empty_iff_false, iff_false]
      rintro ⟨hp, hle⟩
      have hnp : ‖p‖ ≤ max R 0 := by
        have := hR hp; simp only [Metric.mem_closedBall, dist_zero_right] at this
        exact le_trans this (le_max_left R 0)
      have hcs : |inner ℝ v p| ≤ ‖v‖ * ‖p‖ := abs_real_inner_le_norm v p
      have hge : -(‖v‖ * max R 0) ≤ inner ℝ v p := by
        have := (abs_le.mp hcs).1
        nlinarith [norm_nonneg v]
      dsimp [M] at hle; linarith
    simp [F, hempty]
  have hF_hi : F M = (volume C).toReal := by
    have hall : OMA.S_mo_201359.side C v M = C := by
      ext p
      simp only [OMA.S_mo_201359.side]
      refine ⟨fun h => h.1, fun hp => ⟨hp, ?_⟩⟩
      have hnp : ‖p‖ ≤ max R 0 := by
        have := hR hp; simp only [Metric.mem_closedBall, dist_zero_right] at this
        exact le_trans this (le_max_left R 0)
      have hcs : |inner ℝ v p| ≤ ‖v‖ * ‖p‖ := abs_real_inner_le_norm v p
      have hle : inner ℝ v p ≤ ‖v‖ * max R 0 := by
        have := (abs_le.mp hcs).2
        nlinarith [norm_nonneg v]
      dsimp [M]; linarith
    simp [F, hall]
  have hmid : (volume C).toReal / 2 ∈ Icc (F (-M)) (F M) := by
    rw [hF_lo, hF_hi]
    constructor <;> linarith [ENNReal.toReal_nonneg (a := volume C)]
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc (by linarith : -M ≤ M) hcont.continuousOn hmid
  exact ⟨s, (bisects_iff_toReal C hC v hv s).mpr hs⟩

/-! ### Normalized configuration -/

structure Normalized (C : Set Plane) : Prop where
  compact : IsCompact C
  convex : Convex ℝ C
  int_ne : (interior C).Nonempty
  bisect_zero : OMA.S_mo_201359.bisects C (mkP 1 0) 0
  chord_eq : {p ∈ C | px p = 0} = {p : Plane | px p = 0 ∧ 0 ≤ py p ∧ py p ≤ 1}
  minimal : ∀ (v : Plane) (s : ℝ), OMA.S_mo_201359.bisects C v s →
    1 ≤ OMA.S_mo_201359.chordLength C v s

lemma normalized_mem_S {C : Set Plane} (hN : Normalized C) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    mkP 0 y ∈ C := by
  have h : mkP 0 y ∈ {p : Plane | px p = 0 ∧ 0 ≤ py p ∧ py p ≤ 1} := ⟨rfl, hy0, hy1⟩
  rw [← hN.chord_eq] at h
  exact h.1

lemma normalized_S_bounds {C : Set Plane} (hN : Normalized C) {y : ℝ} (hy : mkP 0 y ∈ C) :
    0 ≤ y ∧ y ≤ 1 := by
  have h : mkP 0 y ∈ {p ∈ C | px p = 0} := ⟨hy, rfl⟩
  rw [hN.chord_eq] at h
  exact ⟨h.2.1, h.2.2⟩

lemma normalized_side_eq {C : Set Plane} :
    OMA.S_mo_201359.side C (mkP 1 0) 0 = {p ∈ C | px p ≤ 0} := by
  ext p; simp [OMA.S_mo_201359.side, inner_plane]

lemma normalized_opposite_eq {C : Set Plane} :
    OMA.S_mo_201359.opposite C (mkP 1 0) 0 = {p ∈ C | 0 ≤ px p} := by
  ext p; simp [OMA.S_mo_201359.opposite, inner_plane]

lemma normalized_vol_pos {C : Set Plane} (hN : Normalized C) : 0 < (volume C).toReal := by
  have hpos : 0 < volume C :=
    lt_of_lt_of_le (isOpen_interior.measure_pos volume hN.int_ne) (measure_mono interior_subset)
  exact ENNReal.toReal_pos hpos.ne' hN.compact.measure_lt_top.ne

lemma normalized_vol_side_eq {C : Set Plane} (hN : Normalized C) :
    (volume {p ∈ C | px p ≤ 0}).toReal = (volume C).toReal / 2 ∧
    (volume {p ∈ C | 0 ≤ px p}).toReal = (volume C).toReal / 2 := by
  have h10 : mkP 1 0 ≠ 0 := by intro h; have := congrArg px h; simp at this
  have hb := (bisects_iff_toReal C hN.compact (mkP 1 0) h10 0).mp hN.bisect_zero
  rw [normalized_side_eq] at hb
  have heq := hN.bisect_zero.2
  rw [normalized_side_eq, normalized_opposite_eq] at heq
  exact ⟨hb, by rw [← heq]; exact hb⟩

/-! ### Step 2: Vertical-base triangles and area lower bound `volume C ≥ 1/2` -/

lemma triangle_subset_convex {C : Set Plane} (hC : Convex ℝ C)
    (hA : mkP 0 0 ∈ C) (hB : mkP 0 1 ∈ C) {x₀ y₀ : ℝ} (hQ : mkP x₀ y₀ ∈ C) :
    ∀ p : Plane,
      (x₀ > 0 → 0 ≤ px p ∧ px p ≤ x₀ ∧ (px p / x₀) * y₀ ≤ py p ∧ py p ≤ 1 + (px p / x₀) * (y₀ - 1) → p ∈ C) ∧
      (x₀ < 0 → x₀ ≤ px p ∧ px p ≤ 0 ∧ (px p / x₀) * y₀ ≤ py p ∧ py p ≤ 1 + (px p / x₀) * (y₀ - 1) → p ∈ C) := by
  intro p
  have hmain : ∀ (ht0 : 0 ≤ px p / x₀) (ht1 : px p / x₀ ≤ 1)
      (hlo : (px p / x₀) * y₀ ≤ py p) (hhi : py p ≤ 1 + (px p / x₀) * (y₀ - 1)) (hx0 : x₀ ≠ 0), p ∈ C := by
    intro ht0 ht1 hlo hhi hx0
    set t := px p / x₀
    set u := py p - t * y₀
    set w := 1 - t - u
    have hu0 : 0 ≤ u := by linarith
    have hw0 : 0 ≤ w := by linarith
    have hp_eq : p = w • mkP 0 0 + u • mkP 0 1 + t • mkP x₀ y₀ := by
      apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
      · dsimp [t]; rw [mul_zero, mul_zero, zero_add, zero_add, div_mul_cancel₀ _ hx0]
      · dsimp [u]; ring
    rw [hp_eq]
    by_cases ht_eq : t = 1
    · have hu_eq : u = 0 := by linarith
      have hw_eq : w = 0 := by linarith
      simp [ht_eq, hu_eq, hw_eq, hQ]
    · have h1_pos : 0 < 1 - t := lt_of_le_of_ne (by linarith) (fun h => ht_eq (by linarith))
      let m := (w / (1 - t)) • mkP 0 0 + (u / (1 - t)) • mkP 0 1
      have hsum_wu : w / (1 - t) + u / (1 - t) = 1 := by
        rw [← add_div, show w + u = 1 - t by dsimp [w]; ring, div_self h1_pos.ne']
      have hm : m ∈ C := hC hA hB (div_nonneg hw0 h1_pos.le) (div_nonneg hu0 h1_pos.le) hsum_wu
      have hcomb : w • mkP 0 0 + u • mkP 0 1 + t • mkP x₀ y₀ = (1 - t) • m + t • mkP x₀ y₀ := by
        apply plane_ext <;> simp only [m, px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
        · ring
        · simp only [mul_zero, zero_add, mul_one]; rw [mul_div_cancel₀ _ h1_pos.ne']
      rw [hcomb]
      exact hC hm hQ h1_pos.le ht0 (by ring)
  constructor
  · intro hx0 ⟨h1, h2, h3, h4⟩
    exact hmain (div_nonneg h1 hx0.le) ((div_le_one hx0).mpr h2) h3 h4 hx0.ne'
  · intro hx0 ⟨h1, h2, h3, h4⟩
    have ht0 : 0 ≤ px p / x₀ := div_nonneg_of_nonpos h2 hx0.le
    have ht1 : px p / x₀ ≤ 1 := by rw [div_le_iff_of_neg hx0]; linarith
    exact hmain ht0 ht1 h3 h4 hx0.ne

lemma volume_triangle_pos {x₀ y₀ : ℝ} (hx₀ : 0 < x₀) :
    (volume : Measure Plane)
      {p : Plane | 0 ≤ px p ∧ px p ≤ x₀ ∧ (px p / x₀) * y₀ ≤ py p ∧ py p ≤ 1 + (px p / x₀) * (y₀ - 1)} =
    ENNReal.ofReal (x₀ / 2) := by
  rw [volume_region_x 0 x₀ hx₀.le (fun x => (x / x₀) * y₀) (fun x => 1 + (x / x₀) * (y₀ - 1))
    (by fun_prop) (by fun_prop) (fun x hx => by
      have : x / x₀ ≤ 1 := (div_le_one hx₀).mpr hx.2
      linarith)]
  congr 1
  have hfun : (fun x => 1 + x / x₀ * (y₀ - 1) - x / x₀ * y₀) = fun x => -(1 / x₀) * x + 1 := by
    ext x; ring
  rw [hfun, integral_linear]
  field_simp
  ring

lemma volume_triangle_neg {x₀ y₀ : ℝ} (hx₀ : x₀ < 0) :
    (volume : Measure Plane)
      {p : Plane | x₀ ≤ px p ∧ px p ≤ 0 ∧ (px p / x₀) * y₀ ≤ py p ∧ py p ≤ 1 + (px p / x₀) * (y₀ - 1)} =
    ENNReal.ofReal (-x₀ / 2) := by
  rw [volume_region_x x₀ 0 hx₀.le (fun x => (x / x₀) * y₀) (fun x => 1 + (x / x₀) * (y₀ - 1))
    (by fun_prop) (by fun_prop) (fun x hx => by
      have : x / x₀ ≤ 1 := by rw [div_le_iff_of_neg hx₀]; linarith [hx.1]
      linarith)]
  congr 1
  have hfun : (fun x => 1 + x / x₀ * (y₀ - 1) - x / x₀ * y₀) = fun x => -(1 / x₀) * x + 1 := by
    ext x; ring
  rw [hfun, integral_linear]
  have hxne : x₀ ≠ 0 := hx₀.ne
  field_simp
  ring

lemma normalized_area_ge_half {C : Set Plane} (hN : Normalized C) :
    (1 / 2 : ℝ) ≤ (volume C).toReal := by
  have h01 : mkP 0 1 ≠ 0 := by intro h; have := congrArg py h; simp at this
  obtain ⟨tH, hbis⟩ := exists_bisects C hN.compact (mkP 0 1) h01
  have hlen : 1 ≤ OMA.S_mo_201359.chordLength C (mkP 0 1) tH := hN.minimal (mkP 0 1) tH hbis
  let H : Set Plane := {p ∈ C | py p = tH}
  have hH_eq : {p ∈ C | inner ℝ (mkP 0 1) p = tH} = H := by
    ext p; simp [H, inner_plane]
  have hdiam : 1 ≤ Metric.diam H := by rwa [OMA.S_mo_201359.chordLength, hH_eq] at hlen
  have hH_compact : IsCompact H :=
    hN.compact.inter_right (isClosed_eq continuous_py continuous_const)
  have hH_ne : H.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, Metric.diam_empty] at hdiam
    linarith
  obtain ⟨pL, hpL, hmin⟩ := hH_compact.exists_isMinOn hH_ne continuous_px.continuousOn
  obtain ⟨pR, hpR, hmax⟩ := hH_compact.exists_isMaxOn hH_ne continuous_px.continuousOn
  have hspan : 1 ≤ px pR - px pL := by
    have hle : Metric.diam H ≤ px pR - px pL := by
      refine Metric.diam_le_of_forall_dist_le (sub_nonneg.mpr (hmin hpR)) fun a ha b hb => ?_
      have hay : py a = tH := ha.2
      have hby : py b = tH := hb.2
      refine dist_le_of_sq_le (sub_nonneg.mpr (hmin hpR)) ?_
      rw [hay, hby, sub_self, zero_pow two_ne_zero, add_zero]
      have h1 : px pL ≤ px a := hmin ha
      have h2 : px a ≤ px pR := hmax ha
      have h3 : px pL ≤ px b := hmin hb
      have h4 : px b ≤ px pR := hmax hb
      nlinarith
    linarith
  have hA : mkP 0 0 ∈ C := normalized_mem_S hN le_rfl (by norm_num)
  have hB : mkP 0 1 ∈ C := normalized_mem_S hN (by norm_num) le_rfl
  have hpL_eq : mkP (px pL) tH ∈ C := by
    have : mkP (px pL) tH = pL := by apply plane_ext <;> simp [hpL.2]
    rw [this]; exact hpL.1
  have hpR_eq : mkP (px pR) tH ∈ C := by
    have : mkP (px pR) tH = pR := by apply plane_ext <;> simp [hpR.2]
    rw [this]; exact hpR.1
  have hfin : volume C ≠ ⊤ := hN.compact.measure_lt_top.ne
  by_cases hL : px pL < 0
  · by_cases hR : 0 < px pR
    · let TL := {p : Plane | px pL ≤ px p ∧ px p ≤ 0 ∧
        (px p / px pL) * tH ≤ py p ∧ py p ≤ 1 + (px p / px pL) * (tH - 1)}
      let TR := {p : Plane | 0 ≤ px p ∧ px p ≤ px pR ∧
        (px p / px pR) * tH ≤ py p ∧ py p ≤ 1 + (px p / px pR) * (tH - 1)}
      have hTL_sub : TL ⊆ {p ∈ C | px p ≤ 0} := fun p hp =>
        ⟨(triangle_subset_convex hN.convex hA hB hpL_eq p).2 hL hp, hp.2.1⟩
      have hTR_sub : TR ⊆ {p ∈ C | 0 ≤ px p} := fun p hp =>
        ⟨(triangle_subset_convex hN.convex hA hB hpR_eq p).1 hR hp, hp.1⟩
      have hvolL : ENNReal.ofReal (-px pL / 2) ≤ volume {p ∈ C | px p ≤ 0} := by
        rw [← volume_triangle_neg hL]; exact measure_mono hTL_sub
      have hvolR : ENNReal.ofReal (px pR / 2) ≤ volume {p ∈ C | 0 ≤ px p} := by
        rw [← volume_triangle_pos hR]; exact measure_mono hTR_sub
      have h10 : mkP 1 0 ≠ 0 := by intro h; have := congrArg px h; simp at this
      have hsum := volume_side_add_opposite C hN.compact.measurableSet (mkP 1 0) h10 0
      rw [normalized_side_eq, normalized_opposite_eq] at hsum
      have hle : ENNReal.ofReal (-px pL / 2 + px pR / 2) ≤ volume C := by
        rw [ENNReal.ofReal_add (by linarith) (by linarith), ← hsum]
        exact add_le_add hvolL hvolR
      have htoR := ENNReal.toReal_mono hfin hle
      rw [ENNReal.toReal_ofReal (by linarith)] at htoR
      linarith
    · let TL := {p : Plane | px pL ≤ px p ∧ px p ≤ 0 ∧
        (px p / px pL) * tH ≤ py p ∧ py p ≤ 1 + (px p / px pL) * (tH - 1)}
      have hTL_sub : TL ⊆ C := fun p hp =>
        (triangle_subset_convex hN.convex hA hB hpL_eq p).2 hL hp
      have hle : ENNReal.ofReal (-px pL / 2) ≤ volume C := by
        rw [← volume_triangle_neg hL]; exact measure_mono hTL_sub
      have htoR := ENNReal.toReal_mono hfin hle
      rw [ENNReal.toReal_ofReal (by linarith)] at htoR
      linarith
  · have hR : 0 < px pR := by linarith
    let TR := {p : Plane | 0 ≤ px p ∧ px p ≤ px pR ∧
      (px p / px pR) * tH ≤ py p ∧ py p ≤ 1 + (px p / px pR) * (tH - 1)}
    have hTR_sub : TR ⊆ C := fun p hp =>
      (triangle_subset_convex hN.convex hA hB hpR_eq p).1 hR hp
    have hle : ENNReal.ofReal (px pR / 2) ≤ volume C := by
      rw [← volume_triangle_pos hR]; exact measure_mono hTR_sub
    have htoR := ENNReal.toReal_mono hfin hle
    rw [ENNReal.toReal_ofReal (by linarith)] at htoR
    linarith

/-! ### Step 3: Canonical one-sided slopes, tilt inequality, and symmetric supporting wedge -/

lemma exists_pos_and_neg_x {C : Set Plane} (hN : Normalized C) :
    (∃ p ∈ C, px p < 0) ∧ (∃ p ∈ C, 0 < px p) := by
  have h10 : mkP 1 0 ≠ 0 := by intro h; have := congrArg px h; simp at this
  have hhalf := normalized_vol_side_eq hN
  have hvol_pos := normalized_vol_pos hN
  have hline0 : volume {p : Plane | px p = 0} = 0 := by
    convert volume_line_zero (mkP 1 0) h10 0 using 2; ext p; simp [inner_plane]
  constructor
  · by_contra h
    push Not at h
    have hsub : {p ∈ C | px p ≤ 0} ⊆ {p : Plane | px p = 0} :=
      fun p hp => le_antisymm hp.2 (h p hp.1)
    have h0 : volume {p ∈ C | px p ≤ 0} = 0 := measure_mono_null hsub hline0
    rw [h0] at hhalf
    simp at hhalf; linarith
  · by_contra h
    push Not at h
    have hsub : {p ∈ C | 0 ≤ px p} ⊆ {p : Plane | px p = 0} :=
      fun p hp => le_antisymm (h p hp.1) hp.2
    have h0 : volume {p ∈ C | 0 ≤ px p} = 0 := measure_mono_null hsub hline0
    rw [h0] at hhalf
    simp at hhalf; linarith

noncomputable def fBot (C : Set Plane) (x : ℝ) : ℝ := sInf {y : ℝ | mkP x y ∈ C}
noncomputable def gTop (C : Set Plane) (x : ℝ) : ℝ := sSup {y : ℝ | mkP x y ∈ C}

noncomputable def aMinus (C : Set Plane) : ℝ := sSup {q | ∃ x < 0, (∃ y, mkP x y ∈ C) ∧ q = fBot C x / x}
noncomputable def aPlus  (C : Set Plane) : ℝ := sInf {q | ∃ x > 0, (∃ y, mkP x y ∈ C) ∧ q = fBot C x / x}
noncomputable def bMinus (C : Set Plane) : ℝ := sInf {q | ∃ x < 0, (∃ y, mkP x y ∈ C) ∧ q = (gTop C x - 1) / x}
noncomputable def bPlus  (C : Set Plane) : ℝ := sSup {q | ∃ x > 0, (∃ y, mkP x y ∈ C) ∧ q = (gTop C x - 1) / x}

lemma fBot_gTop_mem {C : Set Plane} (hC : IsCompact C) {x : ℝ} (hx : ∃ y, mkP x y ∈ C) :
    mkP x (fBot C x) ∈ C ∧ mkP x (gTop C x) ∈ C ∧
    (∀ y, mkP x y ∈ C → fBot C x ≤ y ∧ y ≤ gTop C x) := by
  let Sx : Set Plane := {p ∈ C | px p = x}
  have hSx_compact : IsCompact Sx := hC.inter_right (isClosed_eq continuous_px continuous_const)
  have hSx_ne : Sx.Nonempty := by obtain ⟨y, hy⟩ := hx; exact ⟨mkP x y, hy, rfl⟩
  obtain ⟨pmin, hpmin, hmin⟩ := hSx_compact.exists_isMinOn hSx_ne continuous_py.continuousOn
  obtain ⟨pmax, hpmax, hmax⟩ := hSx_compact.exists_isMaxOn hSx_ne continuous_py.continuousOn
  have hpmin_mem : mkP x (py pmin) ∈ C := by rw [← hpmin.2, mkP_px_py]; exact hpmin.1
  have hpmax_mem : mkP x (py pmax) ∈ C := by rw [← hpmax.2, mkP_px_py]; exact hpmax.1
  have hf : fBot C x = py pmin := by
    apply le_antisymm
    · exact csInf_le ⟨py pmin, fun y hy => hmin ⟨hy, rfl⟩⟩ hpmin_mem
    · exact le_csInf hx fun y hy => hmin ⟨hy, rfl⟩
  have hg : gTop C x = py pmax := by
    apply le_antisymm
    · exact csSup_le hx fun y hy => hmax ⟨hy, rfl⟩
    · exact le_csSup ⟨py pmax, fun y hy => hmax ⟨hy, rfl⟩⟩ hpmax_mem
  refine ⟨by rwa [hf], by rwa [hg], fun y hy => ?_⟩
  rw [hf, hg]
  exact ⟨hmin ⟨hy, rfl⟩, hmax ⟨hy, rfl⟩⟩

lemma mem_of_between_fBot_gTop {C : Set Plane} (hC : IsCompact C) (hconv : Convex ℝ C)
    {x y : ℝ} (hx : ∃ y', mkP x y' ∈ C) (hlo : fBot C x ≤ y) (hhi : y ≤ gTop C x) :
    mkP x y ∈ C := by
  obtain ⟨hf, hg, _⟩ := fBot_gTop_mem hC hx
  by_cases heq : fBot C x = gTop C x
  · have : y = fBot C x := by linarith
    rwa [this]
  · have hlt : fBot C x < gTop C x := lt_of_le_of_ne (le_trans hlo hhi) heq
    have hpos : gTop C x - fBot C x ≠ 0 := by linarith
    let t := (y - fBot C x) / (gTop C x - fBot C x)
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have ht1 : t ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hcomb : mkP x y = (1 - t) • mkP x (fBot C x) + t • mkP x (gTop C x) := by
      apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
      · ring
      · dsimp [t]; field_simp; ring
    rw [hcomb]
    exact hconv hf hg (by linarith) ht0 (by ring)

lemma secant_f_le {C : Set Plane} (hN : Normalized C) {x₁ x₂ : ℝ}
    (hx₁ : x₁ < 0) (hx₂ : 0 < x₂) (hex₁ : ∃ y, mkP x₁ y ∈ C) (hex₂ : ∃ y, mkP x₂ y ∈ C) :
    fBot C x₁ / x₁ ≤ fBot C x₂ / x₂ := by
  have hf₁ := (fBot_gTop_mem hN.compact hex₁).1
  have hf₂ := (fBot_gTop_mem hN.compact hex₂).1
  have hd : 0 < x₂ - x₁ := by linarith
  have hdne : x₂ - x₁ ≠ 0 := hd.ne'
  let lam := x₂ / (x₂ - x₁)
  have h1lam : 1 - lam = -x₁ / (x₂ - x₁) := by dsimp [lam]; field_simp; ring
  have hlam0 : 0 ≤ lam := div_nonneg hx₂.le hd.le
  have hlam1 : 0 ≤ 1 - lam := by rw [h1lam]; exact div_nonneg (by linarith) hd.le
  have h0mem : lam • mkP x₁ (fBot C x₁) + (1 - lam) • mkP x₂ (fBot C x₂) ∈ C :=
    hN.convex hf₁ hf₂ hlam0 hlam1 (by ring)
  have h0eq : lam • mkP x₁ (fBot C x₁) + (1 - lam) • mkP x₂ (fBot C x₂) =
      mkP 0 ((x₂ * fBot C x₁ - x₁ * fBot C x₂) / (x₂ - x₁)) := by
    apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
    · rw [h1lam]; dsimp [lam]; field_simp; ring
    · rw [h1lam]; dsimp [lam]; field_simp; ring
  rw [h0eq] at h0mem
  have hy0 := (normalized_S_bounds hN h0mem).1
  have hnum : 0 ≤ x₂ * fBot C x₁ - x₁ * fBot C x₂ := by
    have := mul_nonneg hy0 hd.le
    rwa [div_mul_cancel₀ _ hdne] at this
  have hprod : x₁ * x₂ < 0 := mul_neg_of_neg_of_pos hx₁ hx₂
  have hx₁ne : x₁ ≠ 0 := hx₁.ne
  have hx₂ne : x₂ ≠ 0 := hx₂.ne'
  have hmul : (fBot C x₂ / x₂ - fBot C x₁ / x₁) * (x₁ * x₂) = x₁ * fBot C x₂ - x₂ * fBot C x₁ := by
    field_simp
  nlinarith

lemma secant_g_le {C : Set Plane} (hN : Normalized C) {x₁ x₂ : ℝ}
    (hx₁ : x₁ < 0) (hx₂ : 0 < x₂) (hex₁ : ∃ y, mkP x₁ y ∈ C) (hex₂ : ∃ y, mkP x₂ y ∈ C) :
    (gTop C x₂ - 1) / x₂ ≤ (gTop C x₁ - 1) / x₁ := by
  have hg₁ := (fBot_gTop_mem hN.compact hex₁).2.1
  have hg₂ := (fBot_gTop_mem hN.compact hex₂).2.1
  have hd : 0 < x₂ - x₁ := by linarith
  have hdne : x₂ - x₁ ≠ 0 := hd.ne'
  let lam := x₂ / (x₂ - x₁)
  have h1lam : 1 - lam = -x₁ / (x₂ - x₁) := by dsimp [lam]; field_simp; ring
  have hlam0 : 0 ≤ lam := div_nonneg hx₂.le hd.le
  have hlam1 : 0 ≤ 1 - lam := by rw [h1lam]; exact div_nonneg (by linarith) hd.le
  have h0mem : lam • mkP x₁ (gTop C x₁) + (1 - lam) • mkP x₂ (gTop C x₂) ∈ C :=
    hN.convex hg₁ hg₂ hlam0 hlam1 (by ring)
  have h0eq : lam • mkP x₁ (gTop C x₁) + (1 - lam) • mkP x₂ (gTop C x₂) =
      mkP 0 (1 + (x₂ * (gTop C x₁ - 1) - x₁ * (gTop C x₂ - 1)) / (x₂ - x₁)) := by
    apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
    · rw [h1lam]; dsimp [lam]; field_simp; ring
    · rw [h1lam]; dsimp [lam]; field_simp; ring
  rw [h0eq] at h0mem
  have hy1 := (normalized_S_bounds hN h0mem).2
  have hdiv : (x₂ * (gTop C x₁ - 1) - x₁ * (gTop C x₂ - 1)) / (x₂ - x₁) ≤ 0 := by linarith
  have hnum : x₂ * (gTop C x₁ - 1) - x₁ * (gTop C x₂ - 1) ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg hdiv hd.le
    rwa [div_mul_cancel₀ _ hdne] at this
  have hprod : x₁ * x₂ < 0 := mul_neg_of_neg_of_pos hx₁ hx₂
  have hx₁ne : x₁ ≠ 0 := hx₁.ne
  have hx₂ne : x₂ ≠ 0 := hx₂.ne'
  have hmul : ((gTop C x₁ - 1) / x₁ - (gTop C x₂ - 1) / x₂) * (x₁ * x₂) =
      x₂ * (gTop C x₁ - 1) - x₁ * (gTop C x₂ - 1) := by field_simp
  nlinarith

lemma slopes_basic {C : Set Plane} (hN : Normalized C) :
    aMinus C ≤ aPlus C ∧ bPlus C ≤ bMinus C ∧
    (∀ p ∈ C, px p ≤ 0 → aMinus C * px p ≤ py p ∧ py p ≤ 1 + bMinus C * px p) ∧
    (∀ p ∈ C, 0 ≤ px p → aPlus C * px p ≤ py p ∧ py p ≤ 1 + bPlus C * px p) := by
  obtain ⟨⟨pneg, hpneg, hxneg⟩, ⟨ppos, hppos, hxpos⟩⟩ := exists_pos_and_neg_x hN
  have hex_neg : ∃ y, mkP (px pneg) y ∈ C := ⟨py pneg, by rwa [mkP_px_py]⟩
  have hex_pos : ∃ y, mkP (px ppos) y ∈ C := ⟨py ppos, by rwa [mkP_px_py]⟩
  have hne_fM : ({q | ∃ x < 0, (∃ y, mkP x y ∈ C) ∧ q = fBot C x / x}).Nonempty :=
    ⟨_, px pneg, hxneg, hex_neg, rfl⟩
  have hne_fP : ({q | ∃ x > 0, (∃ y, mkP x y ∈ C) ∧ q = fBot C x / x}).Nonempty :=
    ⟨_, px ppos, hxpos, hex_pos, rfl⟩
  have hne_gM : ({q | ∃ x < 0, (∃ y, mkP x y ∈ C) ∧ q = (gTop C x - 1) / x}).Nonempty :=
    ⟨_, px pneg, hxneg, hex_neg, rfl⟩
  have hne_gP : ({q | ∃ x > 0, (∃ y, mkP x y ∈ C) ∧ q = (gTop C x - 1) / x}).Nonempty :=
    ⟨_, px ppos, hxpos, hex_pos, rfl⟩
  have hbdd_fM : BddAbove {q | ∃ x < 0, (∃ y, mkP x y ∈ C) ∧ q = fBot C x / x} :=
    ⟨fBot C (px ppos) / px ppos, by rintro q ⟨x, hx, hex, rfl⟩; exact secant_f_le hN hx hxpos hex hex_pos⟩
  have hbdd_fP : BddBelow {q | ∃ x > 0, (∃ y, mkP x y ∈ C) ∧ q = fBot C x / x} :=
    ⟨fBot C (px pneg) / px pneg, by rintro q ⟨x, hx, hex, rfl⟩; exact secant_f_le hN hxneg hx hex_neg hex⟩
  have hbdd_gM : BddBelow {q | ∃ x < 0, (∃ y, mkP x y ∈ C) ∧ q = (gTop C x - 1) / x} :=
    ⟨(gTop C (px ppos) - 1) / px ppos, by rintro q ⟨x, hx, hex, rfl⟩; exact secant_g_le hN hx hxpos hex hex_pos⟩
  have hbdd_gP : BddAbove {q | ∃ x > 0, (∃ y, mkP x y ∈ C) ∧ q = (gTop C x - 1) / x} :=
    ⟨(gTop C (px pneg) - 1) / px pneg, by rintro q ⟨x, hx, hex, rfl⟩; exact secant_g_le hN hxneg hx hex_neg hex⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact csSup_le hne_fM fun q ⟨x₁, hx₁, hex₁, hq⟩ =>
      le_csInf hne_fP fun r ⟨x₂, hx₂, hex₂, hr⟩ => by rw [hq, hr]; exact secant_f_le hN hx₁ hx₂ hex₁ hex₂
  · exact csSup_le hne_gP fun q ⟨x₂, hx₂, hex₂, hq⟩ =>
      le_csInf hne_gM fun r ⟨x₁, hx₁, hex₁, hr⟩ => by rw [hq, hr]; exact secant_g_le hN hx₁ hx₂ hex₁ hex₂
  · intro p hp hx
    rcases eq_or_lt_of_le hx with h0 | hlt
    · have hpS : mkP 0 (py p) ∈ C := by rwa [← h0, mkP_px_py]
      obtain ⟨h0y, hy1⟩ := normalized_S_bounds hN hpS
      rw [h0]; simp [h0y, hy1]
    · have hex : ∃ y, mkP (px p) y ∈ C := ⟨py p, by rwa [mkP_px_py]⟩
      have hpy := (fBot_gTop_mem hN.compact hex).2.2 (py p) (by rwa [mkP_px_py])
      have hf_le : fBot C (px p) / px p ≤ aMinus C := le_csSup hbdd_fM ⟨px p, hlt, hex, rfl⟩
      have hg_ge : bMinus C ≤ (gTop C (px p) - 1) / px p := csInf_le hbdd_gM ⟨px p, hlt, hex, rfl⟩
      have h1 : aMinus C * px p ≤ fBot C (px p) := by
        have := mul_le_mul_of_nonpos_right hf_le hlt.le
        rwa [div_mul_cancel₀ _ hlt.ne] at this
      have h2 : gTop C (px p) - 1 ≤ bMinus C * px p := by
        have := mul_le_mul_of_nonpos_right hg_ge hlt.le
        rwa [div_mul_cancel₀ _ hlt.ne] at this
      exact ⟨le_trans h1 hpy.1, by linarith [hpy.2]⟩
  · intro p hp hx
    rcases eq_or_lt_of_le hx with h0 | hlt
    · have hpS : mkP 0 (py p) ∈ C := by rwa [h0, mkP_px_py]
      obtain ⟨h0y, hy1⟩ := normalized_S_bounds hN hpS
      rw [← h0]; simp [h0y, hy1]
    · have hex : ∃ y, mkP (px p) y ∈ C := ⟨py p, by rwa [mkP_px_py]⟩
      have hpy := (fBot_gTop_mem hN.compact hex).2.2 (py p) (by rwa [mkP_px_py])
      have hf_ge : aPlus C ≤ fBot C (px p) / px p := csInf_le hbdd_fP ⟨px p, hlt, hex, rfl⟩
      have hg_le : (gTop C (px p) - 1) / px p ≤ bPlus C := le_csSup hbdd_gP ⟨px p, hlt, hex, rfl⟩
      have h1 : aPlus C * px p ≤ fBot C (px p) := by
        have := mul_le_mul_of_nonneg_right hf_ge hlt.le
        rwa [div_mul_cancel₀ _ hlt.ne'] at this
      have h2 : gTop C (px p) - 1 ≤ bPlus C * px p := by
        have := mul_le_mul_of_nonneg_right hg_le hlt.le
        rwa [div_mul_cancel₀ _ hlt.ne'] at this
      exact ⟨le_trans h1 hpy.1, by linarith [hpy.2]⟩

lemma exists_local_sandwich {C : Set Plane} (hN : Normalized C) :
    ∃ δ₁ K : ℝ, 0 < δ₁ ∧ 1 ≤ K ∧
      |aMinus C| ≤ K ∧ |aPlus C| ≤ K ∧ |bMinus C| ≤ K ∧ |bPlus C| ≤ K ∧
      (∀ x ∈ Icc (-δ₁) δ₁, ∃ y, mkP x y ∈ C) ∧
      (∀ p ∈ C, -K * |px p| ≤ py p ∧ py p ≤ 1 + K * |px p|) ∧
      (∀ x ∈ Icc (-δ₁) δ₁, fBot C x ≤ K * |x| ∧ 1 - K * |x| ≤ gTop C x) := by
  obtain ⟨⟨pneg, hpneg, hxneg⟩, ⟨ppos, hppos, hxpos⟩⟩ := exists_pos_and_neg_x hN
  obtain ⟨_, _, hbound_neg, hbound_pos⟩ := slopes_basic hN
  set δ₁ := min (-px pneg) (px ppos)
  have hδ₁ : 0 < δ₁ := lt_min (by linarith) hxpos
  have hI_mem : ∀ x ∈ Icc (-δ₁) δ₁, ∃ y, mkP x y ∈ C := by
    intro x hx
    have hA : mkP 0 0 ∈ C := normalized_mem_S hN le_rfl (by norm_num)
    by_cases hx0 : x ≤ 0
    · let t := x / px pneg
      have ht0 : 0 ≤ t := div_nonneg_of_nonpos hx0 hxneg.le
      have ht1 : t ≤ 1 := by
        rw [div_le_iff_of_neg hxneg]
        have : -δ₁ ≥ px pneg := by dsimp [δ₁]; linarith [min_le_left (-px pneg) (px ppos)]
        linarith [hx.1]
      have hm := hN.convex hA hpneg (show 0 ≤ 1 - t by linarith) ht0 (by ring)
      refine ⟨t * py pneg, ?_⟩
      convert hm using 1
      apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
      · dsimp [t]; rw [mul_zero, zero_add, div_mul_cancel₀ _ hxneg.ne]
      · ring
    · push Not at hx0
      let t := x / px ppos
      have ht0 : 0 ≤ t := div_nonneg hx0.le hxpos.le
      have ht1 : t ≤ 1 := (div_le_one hxpos).mpr (le_trans hx.2 (min_le_right _ _))
      have hm := hN.convex hA hppos (show 0 ≤ 1 - t by linarith) ht0 (by ring)
      refine ⟨t * py ppos, ?_⟩
      convert hm using 1
      apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
      · dsimp [t]; rw [mul_zero, zero_add, div_mul_cancel₀ _ hxpos.ne']
      · ring
  set K1 := max 1 (max |aMinus C| (max |aPlus C| (max |bMinus C| |bPlus C|)))
  set K2 := max (|fBot C (-δ₁)| / δ₁) (max (|fBot C δ₁| / δ₁)
    (max (|gTop C (-δ₁) - 1| / δ₁) (|gTop C δ₁ - 1| / δ₁)))
  set K := max K1 K2
  have hK1 : 1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKaM : |aMinus C| ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hKaP : |aPlus C| ≤ K :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_left _ _)
  have hKbM : |bMinus C| ≤ K :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_left _ _)
  have hKbP : |bPlus C| ≤ K :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_left _ _)
  have hKfM : |fBot C (-δ₁)| / δ₁ ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKfP : |fBot C δ₁| / δ₁ ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hKgM : |gTop C (-δ₁) - 1| / δ₁ ≤ K :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hKgP : |gTop C δ₁ - 1| / δ₁ ≤ K :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨δ₁, K, hδ₁, hK1, hKaM, hKaP, hKbM, hKbP, hI_mem, ?_, ?_⟩
  · intro p hp
    rcases le_total (px p) 0 with hx | hx
    · obtain ⟨h1, h2⟩ := hbound_neg p hp hx
      have hax : |px p| = -px p := abs_of_nonpos hx
      have ha1 : -K * |px p| ≤ aMinus C * px p := by rw [hax]; nlinarith [abs_le.mp hKaM]
      have hb1 : bMinus C * px p ≤ K * |px p| := by rw [hax]; nlinarith [abs_le.mp hKbM]
      exact ⟨le_trans ha1 h1, by linarith⟩
    · obtain ⟨h1, h2⟩ := hbound_pos p hp hx
      have hax : |px p| = px p := abs_of_nonneg hx
      have ha1 : -K * |px p| ≤ aPlus C * px p := by rw [hax]; nlinarith [abs_le.mp hKaP]
      have hb1 : bPlus C * px p ≤ K * |px p| := by rw [hax]; nlinarith [abs_le.mp hKbP]
      exact ⟨le_trans ha1 h1, by linarith⟩
  · intro x hx
    have hA : mkP 0 0 ∈ C := normalized_mem_S hN le_rfl (by norm_num)
    have hB : mkP 0 1 ∈ C := normalized_mem_S hN (by norm_num) le_rfl
    rcases le_total x 0 with hx0 | hx0
    · let t := -x / δ₁
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hδ₁.le
      have ht1 : t ≤ 1 := (div_le_one hδ₁).mpr (by linarith [hx.1])
      have hfm := (fBot_gTop_mem hN.compact (hI_mem (-δ₁) ⟨le_rfl, by linarith⟩)).1
      have hgm := (fBot_gTop_mem hN.compact (hI_mem (-δ₁) ⟨le_rfl, by linarith⟩)).2.1
      have h1 : mkP x (t * fBot C (-δ₁)) ∈ C := by
        convert hN.convex hA hfm (show 0 ≤ 1 - t by linarith) ht0 (by ring) using 1
        apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
        · dsimp [t]; rw [mul_zero, zero_add, mul_neg, div_mul_cancel₀ _ hδ₁.ne', neg_neg]
        · ring
      have h2 : mkP x (1 - t + t * gTop C (-δ₁)) ∈ C := by
        convert hN.convex hB hgm (show 0 ≤ 1 - t by linarith) ht0 (by ring) using 1
        apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
        · dsimp [t]; rw [mul_zero, zero_add, mul_neg, div_mul_cancel₀ _ hδ₁.ne', neg_neg]
        · ring
      have hfg := (fBot_gTop_mem hN.compact (hI_mem x hx)).2.2
      have hax : |x| = -x := abs_of_nonpos hx0
      have hfK : t * fBot C (-δ₁) ≤ K * |x| := by
        rw [hax]; dsimp [t]
        have h3 : fBot C (-δ₁) ≤ K * δ₁ := (abs_le.mp ((div_le_iff₀ hδ₁).mp hKfM)).2
        have h4 := mul_le_mul_of_nonneg_left h3 (div_nonneg (show 0 ≤ -x by linarith) hδ₁.le)
        have h5 : -x / δ₁ * (K * δ₁) = K * (-x) := by
          rw [mul_comm K δ₁, ← mul_assoc, div_mul_cancel₀ _ hδ₁.ne']; ring
        linarith
      have hgK : 1 - K * |x| ≤ 1 - t + t * gTop C (-δ₁) := by
        rw [hax]; dsimp [t]
        have h3 : -(K * δ₁) ≤ gTop C (-δ₁) - 1 := (abs_le.mp ((div_le_iff₀ hδ₁).mp hKgM)).1
        have h4 := mul_le_mul_of_nonneg_left h3 (div_nonneg (show 0 ≤ -x by linarith) hδ₁.le)
        have h5 : -x / δ₁ * -(K * δ₁) = -(K * (-x)) := by
          rw [mul_neg, mul_comm K δ₁, ← mul_assoc, div_mul_cancel₀ _ hδ₁.ne']; ring
        linarith
      exact ⟨le_trans (hfg _ h1).1 hfK, le_trans hgK (hfg _ h2).2⟩
    · let t := x / δ₁
      have ht0 : 0 ≤ t := div_nonneg hx0 hδ₁.le
      have ht1 : t ≤ 1 := (div_le_one hδ₁).mpr hx.2
      have hfp := (fBot_gTop_mem hN.compact (hI_mem δ₁ ⟨by linarith, le_rfl⟩)).1
      have hgp := (fBot_gTop_mem hN.compact (hI_mem δ₁ ⟨by linarith, le_rfl⟩)).2.1
      have h1 : mkP x (t * fBot C δ₁) ∈ C := by
        convert hN.convex hA hfp (show 0 ≤ 1 - t by linarith) ht0 (by ring) using 1
        apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
        · dsimp [t]; rw [mul_zero, zero_add, div_mul_cancel₀ _ hδ₁.ne']
        · ring
      have h2 : mkP x (1 - t + t * gTop C δ₁) ∈ C := by
        convert hN.convex hB hgp (show 0 ≤ 1 - t by linarith) ht0 (by ring) using 1
        apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
        · dsimp [t]; rw [mul_zero, zero_add, div_mul_cancel₀ _ hδ₁.ne']
        · ring
      have hfg := (fBot_gTop_mem hN.compact (hI_mem x hx)).2.2
      have hax : |x| = x := abs_of_nonneg hx0
      have hfK : t * fBot C δ₁ ≤ K * |x| := by
        rw [hax]; dsimp [t]
        have h3 : fBot C δ₁ ≤ K * δ₁ := (abs_le.mp ((div_le_iff₀ hδ₁).mp hKfP)).2
        have h4 := mul_le_mul_of_nonneg_left h3 (div_nonneg hx0 hδ₁.le)
        have h5 : x / δ₁ * (K * δ₁) = K * x := by
          rw [mul_comm K δ₁, ← mul_assoc, div_mul_cancel₀ _ hδ₁.ne']; ring
        linarith
      have hgK : 1 - K * |x| ≤ 1 - t + t * gTop C δ₁ := by
        rw [hax]; dsimp [t]
        have h3 : -(K * δ₁) ≤ gTop C δ₁ - 1 := (abs_le.mp ((div_le_iff₀ hδ₁).mp hKgP)).1
        have h4 := mul_le_mul_of_nonneg_left h3 (div_nonneg hx0 hδ₁.le)
        have h5 : x / δ₁ * -(K * δ₁) = -(K * x) := by
          rw [mul_neg, mul_comm K δ₁, ← mul_assoc, div_mul_cancel₀ _ hδ₁.ne']; ring
        linarith
      exact ⟨le_trans (hfg _ h1).1 hfK, le_trans hgK (hfg _ h2).2⟩

/-- Helper for Lemma 3.3: for small `ε > 0`, there is a bisecting chord with normal `(1, -ε)`
    at offset `tε - ε/2` where `|tε| ≤ 3 K ε^2`. -/
lemma exists_tilt_bisector {C : Set Plane} (hN : Normalized C) {δ₁ K ε : ℝ}
    (hδ₁ : 0 < δ₁) (hK1 : 1 ≤ K)
    (hI_mem : ∀ x ∈ Icc (-δ₁) δ₁, ∃ y, mkP x y ∈ C)
    (hglob : ∀ p ∈ C, -K * |px p| ≤ py p ∧ py p ≤ 1 + K * |px p|)
    (hloc : ∀ x ∈ Icc (-δ₁) δ₁, fBot C x ≤ K * |x| ∧ 1 - K * |x| ≤ gTop C x)
    (hε : 0 < ε) (hε_δ₂ : ε ≤ min δ₁ (1 / (4 * K))) (hKε : K * ε ≤ 1 / 100) :
    ∃ tε : ℝ, |tε| ≤ 3 * K * ε ^ 2 ∧ OMA.S_mo_201359.bisects C (mkP 1 (-ε)) (tε - ε / 2) := by
  have hKpos : 0 < K := by linarith
  set δ₂ := min δ₁ (1 / (4 * K))
  have hδ₂ : 0 < δ₂ := lt_min hδ₁ (by positivity)
  have hε_δ₁ : ε ≤ δ₁ := le_trans hε_δ₂ (min_le_left _ _)
  have hcore : ∀ p : Plane, -δ₂ ≤ px p → px p ≤ δ₂ → (1 / 4 : ℝ) ≤ py p → py p ≤ 3 / 4 → p ∈ C := by
    intro p hx1 hx2 hy1 hy2
    have hxI : px p ∈ Icc (-δ₁) δ₁ := ⟨by linarith [min_le_left δ₁ (1 / (4 * K))],
      le_trans hx2 (min_le_left _ _)⟩
    obtain ⟨hfl, hgl⟩ := hloc (px p) hxI
    have hKabs : K * |px p| ≤ 1 / 4 := by
      have h1 : |px p| ≤ δ₂ := abs_le.mpr ⟨hx1, hx2⟩
      have h2 : δ₂ ≤ 1 / (4 * K) := min_le_right _ _
      have h3 := mul_le_mul_of_nonneg_left (le_trans h1 h2) hKpos.le
      have h4 : K * (1 / (4 * K)) = 1 / 4 := by field_simp
      linarith
    rw [← mkP_px_py p]
    exact mem_of_between_fBot_gTop hN.compact hN.convex (hI_mem (px p) hxI)
      (by linarith) (by linarith)
  let vε : Plane := mkP 1 (-ε)
  have hvε : vε ≠ 0 := by intro h; have := congrArg px h; simp [vε] at this
  have hvε_inner : ∀ p : Plane, inner ℝ vε p = px p - ε * py p := fun p => by
    simp [vε, inner_plane]; ring
  let H0 : Set Plane := {p ∈ C | px p ≤ 0}
  let Hε : Set Plane := OMA.S_mo_201359.side C vε (-ε / 2)
  have hHε_eq : Hε = {p ∈ C | px p ≤ ε * (py p - 1 / 2)} := by
    ext p; simp only [Hε, OMA.S_mo_201359.side, hvε_inner]
    constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  let Gε : Set Plane := Hε \ H0
  let Lε : Set Plane := H0 \ Hε
  have hG_hi : Gε ⊆ {p : Plane | 1 / 2 ≤ py p ∧ py p ≤ 1 + K * ε ∧ 0 ≤ px p ∧ px p ≤ ε * (py p - 1 / 2)} := by
    intro p ⟨hpH, hp0⟩
    rw [hHε_eq] at hpH
    have hpC : p ∈ C := hpH.1
    have hpx_pos : 0 < px p := by by_contra h; push Not at h; exact hp0 ⟨hpC, h⟩
    have hpy_gt : 1 / 2 < py p := by nlinarith [hpH.2]
    have hpy_ub : py p ≤ 1 + K * px p := by
      have := (hglob p hpC).2; rwa [abs_of_pos hpx_pos] at this
    have hpy_ub2 : py p ≤ 1 + K * ε := by
      have hKpx : K * px p ≤ K * ε * (py p - 1 / 2) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpH.2 hKpos.le
      have h1 : (1 - K * ε) * (py p - 1 / 2) ≤ 1 / 2 := by
        have h1id : (1 - K * ε) * (py p - 1 / 2) = py p - 1 / 2 - K * ε * (py p - 1 / 2) := by ring
        linarith only [hpy_ub, hKpx, h1id]
      have hid : (1 - K * ε) * (1 / 2 + K * ε) = 1 / 2 + (K * ε) * (1 / 2 - K * ε) := by ring
      have hprod_nn : 0 ≤ (K * ε) * (1 / 2 - K * ε) :=
        mul_nonneg (by positivity) (by linarith only [hKε])
      have h2 : (1 - K * ε) * (py p - 1 / 2) ≤ (1 - K * ε) * (1 / 2 + K * ε) := by
        linarith only [h1, hid, hprod_nn]
      have h3 := le_of_mul_le_mul_left h2 (by linarith only [hKε])
      linarith only [h3]
    exact ⟨hpy_gt.le, hpy_ub2, hpx_pos.le, hpH.2⟩
  have hG_lo : {p : Plane | 1 / 2 ≤ py p ∧ py p ≤ 1 - K * ε ∧ 0 ≤ px p ∧ px p ≤ ε * (py p - 1 / 2)} \
      {p : Plane | px p = 0} ⊆ Gε := by
    intro p ⟨⟨hy1, hy2, hx1, hx2⟩, hxne⟩
    have hxpos' : 0 < px p := lt_of_le_of_ne hx1 (Ne.symm hxne)
    have hKε0 : 0 ≤ K * ε := by positivity
    have hx_le : px p ≤ ε / 2 := by
      calc px p ≤ ε * (py p - 1 / 2) := hx2
        _ ≤ ε * (1 / 2) := mul_le_mul_of_nonneg_left (by linarith only [hy2, hKε0]) hε.le
        _ = ε / 2 := by ring
    have hxI : px p ∈ Icc (-δ₁) δ₁ := ⟨by linarith only [hx1, hδ₁], by linarith only [hx_le, hε_δ₁, hε]⟩
    obtain ⟨hfl, hgl⟩ := hloc (px p) hxI
    have hax : |px p| = px p := abs_of_pos hxpos'
    have hKpx_le : K * px p ≤ (K * ε) / 2 := by
      have := mul_le_mul_of_nonneg_left hx_le hKpos.le
      linarith only [this]
    have hpC : p ∈ C := by
      rw [← mkP_px_py p]
      exact mem_of_between_fBot_gTop hN.compact hN.convex (hI_mem (px p) hxI)
        (by rw [hax] at hfl; linarith only [hfl, hKpx_le, hKε, hy1])
        (by rw [hax] at hgl; linarith only [hgl, hKpx_le, hKε0, hy2])
    show p ∈ Hε ∧ p ∉ H0
    rw [hHε_eq]
    exact ⟨⟨hpC, hx2⟩, fun h => by linarith only [hxpos', h.2]⟩
  have hL_hi : Lε ⊆ {p : Plane | -(K * ε) ≤ py p ∧ py p ≤ 1 / 2 ∧ ε * (py p - 1 / 2) ≤ px p ∧ px p ≤ 0} := by
    intro p ⟨hp0, hpH⟩
    rw [hHε_eq] at hpH
    have hpC : p ∈ C := hp0.1
    have hpx_gt : ε * (py p - 1 / 2) < px p := by by_contra h; push Not at h; exact hpH ⟨hpC, h⟩
    have hpy_lt : py p < 1 / 2 := by nlinarith only [hε, hpx_gt, hp0.2]
    have hpy_lb : -(K * (-px p)) ≤ py p := by
      have := (hglob p hpC).1; rw [abs_of_nonpos hp0.2] at this; linarith only [this]
    have hpy_lb2 : -(K * ε) ≤ py p := by
      have hKpx : K * ε * (py p - 1 / 2) ≤ K * px p := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpx_gt.le hKpos.le
      have h1 : (1 - K * ε) * (1 / 2 - py p) ≤ 1 / 2 := by
        have h1id : (1 - K * ε) * (1 / 2 - py p) = 1 / 2 - py p + K * ε * (py p - 1 / 2) := by ring
        linarith only [hpy_lb, hKpx, h1id]
      have hid : (1 - K * ε) * (1 / 2 + K * ε) = 1 / 2 + (K * ε) * (1 / 2 - K * ε) := by ring
      have hprod_nn : 0 ≤ (K * ε) * (1 / 2 - K * ε) :=
        mul_nonneg (by positivity) (by linarith only [hKε])
      have h2 : (1 - K * ε) * (1 / 2 - py p) ≤ (1 - K * ε) * (1 / 2 + K * ε) := by
        linarith only [h1, hid, hprod_nn]
      have h3 := le_of_mul_le_mul_left h2 (by linarith only [hKε])
      linarith only [h3]
    exact ⟨hpy_lb2, hpy_lt.le, hpx_gt.le, hp0.2⟩
  have hL_lo : {p : Plane | K * ε ≤ py p ∧ py p ≤ 1 / 2 ∧ ε * (py p - 1 / 2) ≤ px p ∧ px p ≤ 0} \
      {p : Plane | px p = ε * (py p - 1 / 2)} ⊆ Lε := by
    intro p ⟨⟨hy1, hy2, hx1, hx2⟩, hxne⟩
    have hstrict : ε * (py p - 1 / 2) < px p := lt_of_le_of_ne hx1 (Ne.symm hxne)
    have hKε0 : 0 ≤ K * ε := by positivity
    have hx_ge : -(ε / 2) ≤ px p := by
      calc -(ε / 2) = ε * (-(1 / 2)) := by ring
        _ ≤ ε * (py p - 1 / 2) := mul_le_mul_of_nonneg_left (by linarith only [hy1, hKε0]) hε.le
        _ ≤ px p := hx1
    have hxI : px p ∈ Icc (-δ₁) δ₁ := ⟨by linarith only [hx_ge, hε_δ₁, hε], by linarith only [hx2, hδ₁]⟩
    obtain ⟨hfl, hgl⟩ := hloc (px p) hxI
    have hax : |px p| = -px p := abs_of_nonpos hx2
    have hKpx_le : K * (-px p) ≤ (K * ε) / 2 := by
      have := mul_le_mul_of_nonneg_left (show -px p ≤ ε / 2 by linarith only [hx_ge]) hKpos.le
      linarith only [this]
    have hpC : p ∈ C := by
      rw [← mkP_px_py p]
      exact mem_of_between_fBot_gTop hN.compact hN.convex (hI_mem (px p) hxI)
        (by rw [hax] at hfl; linarith only [hfl, hKpx_le, hKε0, hy1])
        (by rw [hax] at hgl; linarith only [hgl, hKpx_le, hKε, hy2])
    show p ∈ H0 ∧ p ∉ Hε
    rw [hHε_eq]
    exact ⟨⟨hpC, hx2⟩, fun h => by linarith only [hstrict, h.2]⟩
  have hvol_G_hi : volume {p : Plane | 1 / 2 ≤ py p ∧ py p ≤ 1 + K * ε ∧ 0 ≤ px p ∧ px p ≤ ε * (py p - 1 / 2)} =
      ENNReal.ofReal (ε / 2 * (1 / 2 + K * ε) ^ 2) := by
    rw [volume_region_y (1 / 2) (1 + K * ε) (by nlinarith) (fun _ => 0) (fun y => ε * (y - 1 / 2))
      continuous_const (by fun_prop) (fun y hy => mul_nonneg hε.le (by linarith [hy.1]))]
    congr 1
    have hf : (fun y : ℝ => ε * (y - 1 / 2) - 0) = fun y => ε * y + (-(ε / 2)) := by ext y; ring
    rw [hf, integral_linear]; ring
  have hvol_G_lo : volume {p : Plane | 1 / 2 ≤ py p ∧ py p ≤ 1 - K * ε ∧ 0 ≤ px p ∧ px p ≤ ε * (py p - 1 / 2)} =
      ENNReal.ofReal (ε / 2 * (1 / 2 - K * ε) ^ 2) := by
    rw [volume_region_y (1 / 2) (1 - K * ε) (by linarith) (fun _ => 0) (fun y => ε * (y - 1 / 2))
      continuous_const (by fun_prop) (fun y hy => mul_nonneg hε.le (by linarith [hy.1]))]
    congr 1
    have hf : (fun y : ℝ => ε * (y - 1 / 2) - 0) = fun y => ε * y + (-(ε / 2)) := by ext y; ring
    rw [hf, integral_linear]; ring
  have hvol_L_hi : volume {p : Plane | -(K * ε) ≤ py p ∧ py p ≤ 1 / 2 ∧ ε * (py p - 1 / 2) ≤ px p ∧ px p ≤ 0} =
      ENNReal.ofReal (ε / 2 * (1 / 2 + K * ε) ^ 2) := by
    rw [volume_region_y (-(K * ε)) (1 / 2) (by nlinarith) (fun y => ε * (y - 1 / 2)) (fun _ => 0)
      (by fun_prop) continuous_const (fun y hy => mul_nonpos_of_nonneg_of_nonpos hε.le (by linarith [hy.2]))]
    congr 1
    have hf : (fun y : ℝ => 0 - ε * (y - 1 / 2)) = fun y => (-ε) * y + (ε / 2) := by ext y; ring
    rw [hf, integral_linear]; ring
  have hvol_L_lo : volume {p : Plane | K * ε ≤ py p ∧ py p ≤ 1 / 2 ∧ ε * (py p - 1 / 2) ≤ px p ∧ px p ≤ 0} =
      ENNReal.ofReal (ε / 2 * (1 / 2 - K * ε) ^ 2) := by
    rw [volume_region_y (K * ε) (1 / 2) (by linarith) (fun y => ε * (y - 1 / 2)) (fun _ => 0)
      (by fun_prop) continuous_const (fun y hy => mul_nonpos_of_nonneg_of_nonpos hε.le (by linarith [hy.2]))]
    congr 1
    have hf : (fun y : ℝ => 0 - ε * (y - 1 / 2)) = fun y => (-ε) * y + (ε / 2) := by ext y; ring
    rw [hf, integral_linear]; ring
  have hline_x0 : volume {p : Plane | px p = 0} = 0 := by
    have h10 : mkP 1 0 ≠ 0 := by intro h; have := congrArg px h; simp at this
    convert volume_line_zero (mkP 1 0) h10 0 using 2; ext p; simp [inner_plane]
  have hline_vε : volume {p : Plane | px p = ε * (py p - 1 / 2)} = 0 := by
    convert volume_line_zero vε hvε (-ε / 2) using 2
    ext p; simp only [mem_ofPred_eq, hvε_inner]; constructor <;> intro h <;> linarith
  have hG_fin : volume Gε ≠ ⊤ := ne_top_of_le_ne_top hN.compact.measure_lt_top.ne (measure_mono fun p hp => hp.1.1)
  have hL_fin : volume Lε ≠ ⊤ := ne_top_of_le_ne_top hN.compact.measure_lt_top.ne (measure_mono fun p hp => hp.1.1)
  have hG_ub : (volume Gε).toReal ≤ ε / 2 * (1 / 2 + K * ε) ^ 2 := by
    have hm : volume Gε ≤ ENNReal.ofReal (ε / 2 * (1 / 2 + K * ε) ^ 2) := by
      rw [← hvol_G_hi]; exact measure_mono hG_hi
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hG_lb : ε / 2 * (1 / 2 - K * ε) ^ 2 ≤ (volume Gε).toReal := by
    have hm : ENNReal.ofReal (ε / 2 * (1 / 2 - K * ε) ^ 2) ≤ volume Gε := by
      rw [← hvol_G_lo, ← measure_sdiff_null hline_x0]
      exact measure_mono hG_lo
    have h1 := ENNReal.toReal_mono hG_fin hm
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hL_ub : (volume Lε).toReal ≤ ε / 2 * (1 / 2 + K * ε) ^ 2 := by
    have hm : volume Lε ≤ ENNReal.ofReal (ε / 2 * (1 / 2 + K * ε) ^ 2) := by
      rw [← hvol_L_hi]; exact measure_mono hL_hi
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hL_lb : ε / 2 * (1 / 2 - K * ε) ^ 2 ≤ (volume Lε).toReal := by
    have hm : ENNReal.ofReal (ε / 2 * (1 / 2 - K * ε) ^ 2) ≤ volume Lε := by
      rw [← hvol_L_lo, ← measure_sdiff_null hline_vε]
      exact measure_mono hL_lo
    have h1 := ENNReal.toReal_mono hL_fin hm
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hH0_meas : MeasurableSet H0 :=
    hN.compact.measurableSet.inter (isClosed_le continuous_px continuous_const).measurableSet
  have hHε_meas : MeasurableSet Hε := measurableSet_side hN.compact.measurableSet vε (-ε / 2)
  have hH0_fin : volume H0 ≠ ⊤ := ne_top_of_le_ne_top hN.compact.measure_lt_top.ne (measure_mono fun p hp => hp.1)
  have hHε_fin : volume Hε ≠ ⊤ := ne_top_of_le_ne_top hN.compact.measure_lt_top.ne (measure_mono fun p hp => hp.1)
  have hI_fin : volume (Hε ∩ H0) ≠ ⊤ := ne_top_of_le_ne_top hH0_fin (measure_mono inter_subset_right)
  have hHε_split : volume Hε = volume (Hε ∩ H0) + volume Gε := by
    change volume Hε = volume (Hε ∩ H0) + volume (Hε \ H0)
    rw [← measure_union (disjoint_sdiff_self_right.mono_left inter_subset_right) (hHε_meas.diff hH0_meas),
      inter_union_sdiff]
  have hH0_split : volume H0 = volume (Hε ∩ H0) + volume Lε := by
    change volume H0 = volume (Hε ∩ H0) + volume (H0 \ Hε)
    rw [inter_comm, ← measure_union (disjoint_sdiff_self_right.mono_left inter_subset_right)
      (hH0_meas.diff hHε_meas), inter_union_sdiff]
  have hdiff_H : (volume Hε).toReal - (volume H0).toReal = (volume Gε).toReal - (volume Lε).toReal := by
    have e1 := congrArg ENNReal.toReal hHε_split
    have e2 := congrArg ENNReal.toReal hH0_split
    rw [ENNReal.toReal_add hI_fin hG_fin] at e1
    rw [ENNReal.toReal_add hI_fin hL_fin] at e2
    linarith only [e1, e2]
  have hH0_half : (volume H0).toReal = (volume C).toReal / 2 := (normalized_vol_side_eq hN).1
  have hbal : |(volume Hε).toReal - (volume C).toReal / 2| ≤ K * ε ^ 2 := by
    rw [← hH0_half, hdiff_H, abs_le]
    have hgap : ε / 2 * (1 / 2 + K * ε) ^ 2 - ε / 2 * (1 / 2 - K * ε) ^ 2 = K * ε ^ 2 := by ring
    constructor <;> linarith only [hG_ub, hG_lb, hL_ub, hL_lb, hgap]
  -- Locate bisecting offset tε ∈ [-3Kε², 3Kε²]
  let Fv : ℝ → ℝ := fun t => (volume (OMA.S_mo_201359.side C vε (t - ε / 2))).toReal
  have hFv_cont : Continuous Fv := (continuous_side_vol C hN.compact vε hvε).comp (continuous_id.sub continuous_const)
  let t0 := 3 * K * ε ^ 2
  have ht0_pos : 0 < t0 := by positivity
  have hFv_hi : (volume C).toReal / 2 < Fv t0 := by
    let Ppos : Set Plane := {p : Plane | 1 / 4 ≤ py p ∧ py p ≤ 3 / 4 ∧
      ε * (py p - 1 / 2) ≤ px p ∧ px p ≤ ε * (py p - 1 / 2) + t0}
    have hP_vol : volume Ppos = ENNReal.ofReal (t0 / 2) := by
      rw [volume_region_y (1 / 4) (3 / 4) (by norm_num) (fun y => ε * (y - 1 / 2))
        (fun y => ε * (y - 1 / 2) + t0) (by fun_prop) (by fun_prop) (fun _ _ => by linarith only [ht0_pos])]
      congr 1
      have hf : (fun y : ℝ => ε * (y - 1 / 2) + t0 - ε * (y - 1 / 2)) = fun _ => t0 := by ext y; ring
      rw [hf, intervalIntegral.integral_const, smul_eq_mul]; ring
    have hP_sub : Ppos \ {p : Plane | px p = ε * (py p - 1 / 2)} ⊆
        OMA.S_mo_201359.side C vε (t0 - ε / 2) \ Hε := by
      intro p ⟨⟨hy1, hy2, hx1, hx2⟩, hxne⟩
      have hstrict : ε * (py p - 1 / 2) < px p := lt_of_le_of_ne hx1 (Ne.symm hxne)
      have hpx_bd : -δ₂ ≤ px p ∧ px p ≤ δ₂ := by
        have ht0_bd : t0 ≤ 3 / 100 * δ₂ := by
          calc t0 = 3 * (K * ε) * ε := by dsimp [t0]; ring
            _ ≤ 3 * (1 / 100) * δ₂ := mul_le_mul (by linarith only [hKε]) hε_δ₂ hε.le (by norm_num)
            _ = 3 / 100 * δ₂ := by ring
        have h1 : -(ε / 4) ≤ ε * (py p - 1 / 2) := by nlinarith only [hε, hy1]
        have h2 : ε * (py p - 1 / 2) ≤ ε / 4 := by nlinarith only [hε, hy2]
        constructor <;> linarith only [hx1, hx2, h1, h2, ht0_bd, hε_δ₂, hδ₂]
      have hpC : p ∈ C := hcore p hpx_bd.1 hpx_bd.2 hy1 hy2
      rw [hHε_eq]
      refine ⟨⟨hpC, ?_⟩, fun h => by linarith only [hstrict, h.2]⟩
      rw [hvε_inner]; linarith only [hx2]
    have hsub_H : Hε ⊆ OMA.S_mo_201359.side C vε (t0 - ε / 2) :=
      fun p hp => ⟨hp.1, by linarith only [hp.2, ht0_pos]⟩
    have hfin_t0 : volume (OMA.S_mo_201359.side C vε (t0 - ε / 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top hN.compact.measure_lt_top.ne (measure_mono fun p hp => hp.1)
    have hsplit : volume (OMA.S_mo_201359.side C vε (t0 - ε / 2)) =
        volume Hε + volume (OMA.S_mo_201359.side C vε (t0 - ε / 2) \ Hε) := by
      have hm := (measurableSet_side hN.compact.measurableSet vε (t0 - ε / 2)).diff hHε_meas
      rw [← measure_union disjoint_sdiff_self_right hm, union_sdiff_cancel hsub_H]
    have hfin_d : volume (OMA.S_mo_201359.side C vε (t0 - ε / 2) \ Hε) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin_t0 (measure_mono sdiff_subset)
    have hge_d : t0 / 2 ≤ (volume (OMA.S_mo_201359.side C vε (t0 - ε / 2) \ Hε)).toReal := by
      have hm : ENNReal.ofReal (t0 / 2) ≤ volume (OMA.S_mo_201359.side C vε (t0 - ε / 2) \ Hε) := by
        rw [← hP_vol, ← measure_sdiff_null hline_vε]
        exact measure_mono hP_sub
      have := ENNReal.toReal_mono hfin_d hm
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have heq := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add hHε_fin hfin_d] at heq
    have hbal1 := (abs_le.mp hbal).1
    have hKε2 : 0 < K * ε ^ 2 := by positivity
    have ht0_eq : t0 = 3 * K * ε ^ 2 := rfl
    dsimp [Fv]
    linarith only [heq, hge_d, hbal1, hKε2, ht0_eq]
  have hFv_lo : Fv (-t0) < (volume C).toReal / 2 := by
    let Pneg : Set Plane := {p : Plane | 1 / 4 ≤ py p ∧ py p ≤ 3 / 4 ∧
      ε * (py p - 1 / 2) - t0 ≤ px p ∧ px p ≤ ε * (py p - 1 / 2)}
    have hP_vol : volume Pneg = ENNReal.ofReal (t0 / 2) := by
      rw [volume_region_y (1 / 4) (3 / 4) (by norm_num) (fun y => ε * (y - 1 / 2) - t0)
        (fun y => ε * (y - 1 / 2)) (by fun_prop) (by fun_prop) (fun _ _ => by linarith only [ht0_pos])]
      congr 1
      have hf : (fun y : ℝ => ε * (y - 1 / 2) - (ε * (y - 1 / 2) - t0)) = fun _ => t0 := by ext y; ring
      rw [hf, intervalIntegral.integral_const, smul_eq_mul]; ring
    have hline_neg : volume {p : Plane | px p = ε * (py p - 1 / 2) - t0} = 0 := by
      convert volume_line_zero vε hvε (-t0 - ε / 2) using 2
      ext p; simp only [mem_ofPred_eq, hvε_inner]; constructor <;> intro h <;> linarith
    have hP_sub : Pneg \ {p : Plane | px p = ε * (py p - 1 / 2) - t0} ⊆
        Hε \ OMA.S_mo_201359.side C vε (-t0 - ε / 2) := by
      intro p ⟨⟨hy1, hy2, hx1, hx2⟩, hxne⟩
      have hstrict : ε * (py p - 1 / 2) - t0 < px p := lt_of_le_of_ne hx1 (Ne.symm hxne)
      have hpx_bd : -δ₂ ≤ px p ∧ px p ≤ δ₂ := by
        have ht0_bd : t0 ≤ 3 / 100 * δ₂ := by
          calc t0 = 3 * (K * ε) * ε := by dsimp [t0]; ring
            _ ≤ 3 * (1 / 100) * δ₂ := mul_le_mul (by linarith only [hKε]) hε_δ₂ hε.le (by norm_num)
            _ = 3 / 100 * δ₂ := by ring
        have h1 : -(ε / 4) ≤ ε * (py p - 1 / 2) := by nlinarith only [hε, hy1]
        have h2 : ε * (py p - 1 / 2) ≤ ε / 4 := by nlinarith only [hε, hy2]
        constructor <;> linarith only [hx1, hx2, h1, h2, ht0_bd, hε_δ₂, hδ₂]
      have hpC : p ∈ C := hcore p hpx_bd.1 hpx_bd.2 hy1 hy2
      rw [hHε_eq]
      refine ⟨⟨hpC, hx2⟩, fun h => ?_⟩
      have h2 := h.2; rw [hvε_inner] at h2; linarith only [hstrict, h2]
    have hsub_H : OMA.S_mo_201359.side C vε (-t0 - ε / 2) ⊆ Hε :=
      fun p hp => ⟨hp.1, by linarith only [hp.2, ht0_pos]⟩
    have hfin_mt0 : volume (OMA.S_mo_201359.side C vε (-t0 - ε / 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top hHε_fin (measure_mono hsub_H)
    have hsplit : volume Hε = volume (OMA.S_mo_201359.side C vε (-t0 - ε / 2)) +
        volume (Hε \ OMA.S_mo_201359.side C vε (-t0 - ε / 2)) := by
      have hm := hHε_meas.diff (measurableSet_side hN.compact.measurableSet vε (-t0 - ε / 2))
      rw [← measure_union disjoint_sdiff_self_right hm, union_sdiff_cancel hsub_H]
    have hfin_d : volume (Hε \ OMA.S_mo_201359.side C vε (-t0 - ε / 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top hHε_fin (measure_mono sdiff_subset)
    have hge_d : t0 / 2 ≤ (volume (Hε \ OMA.S_mo_201359.side C vε (-t0 - ε / 2))).toReal := by
      have hm : ENNReal.ofReal (t0 / 2) ≤ volume (Hε \ OMA.S_mo_201359.side C vε (-t0 - ε / 2)) := by
        rw [← hP_vol, ← measure_sdiff_null hline_neg]
        exact measure_mono hP_sub
      have := ENNReal.toReal_mono hfin_d hm
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have heq := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add hfin_mt0 hfin_d] at heq
    have hbal2 := (abs_le.mp hbal).2
    have hKε2 : 0 < K * ε ^ 2 := by positivity
    have ht0_eq : t0 = 3 * K * ε ^ 2 := rfl
    dsimp [Fv]
    linarith only [heq, hge_d, hbal2, hKε2, ht0_eq]
  have hmid : (volume C).toReal / 2 ∈ Icc (Fv (-t0)) (Fv t0) := ⟨hFv_lo.le, hFv_hi.le⟩
  obtain ⟨tε, htε_mem, htε_eq⟩ := intermediate_value_Icc (by linarith only [ht0_pos] : -t0 ≤ t0) hFv_cont.continuousOn hmid
  exact ⟨tε, abs_le.mpr ⟨htε_mem.1, htε_mem.2⟩,
    (bisects_iff_toReal C hN.compact vε hvε (tε - ε / 2)).mpr htε_eq⟩

/-- Lemma 3.3: `0 ≤ aMinus C + bPlus C`. -/
lemma tilt_nonneg {C : Set Plane} (hN : Normalized C) : 0 ≤ aMinus C + bPlus C := by
  by_contra hneg
  push Not at hneg
  set η := -(aMinus C + bPlus C)
  have hη : 0 < η := by linarith
  obtain ⟨_, _, hbound_neg, hbound_pos⟩ := slopes_basic hN
  obtain ⟨δ₁, K, hδ₁, hK1, hKaM, _, _, hKbP, hI_mem, hglob, hloc⟩ := exists_local_sandwich hN
  have hKpos : 0 < K := by linarith
  set δ₂ := min δ₁ (1 / (4 * K))
  have hδ₂ : 0 < δ₂ := lt_min hδ₁ (by positivity)
  set ε := min δ₂ (min (1 / (100 * K)) (η / (40 * K ^ 2 + 4)))
  have hε : 0 < ε := lt_min hδ₂ (lt_min (by positivity) (by positivity))
  have hε_δ₂ : ε ≤ δ₂ := min_le_left _ _
  have hKε : K * ε ≤ 1 / 100 := by
    have h1 : ε ≤ 1 / (100 * K) := le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 := mul_le_mul_of_nonneg_left h1 hKpos.le
    have h3 : K * (1 / (100 * K)) = 1 / 100 := by field_simp
    linarith
  have hε_η : ε ≤ η / (40 * K ^ 2 + 4) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hε_le1 : ε ≤ 1 / 100 := by nlinarith only [hK1, hKε, hε]
  let vε : Plane := mkP 1 (-ε)
  have hvε_inner : ∀ p : Plane, inner ℝ vε p = px p - ε * py p := fun p => by
    simp [vε, inner_plane]; ring
  obtain ⟨tε, htε_abs, hbis_ε⟩ :=
    exists_tilt_bisector hN hδ₁ hK1 hI_mem hglob hloc hε hε_δ₂ hKε
  have hchord_ge : 1 ≤ OMA.S_mo_201359.chordLength C vε (tε - ε / 2) :=
    hN.minimal vε (tε - ε / 2) hbis_ε
  -- Strict chord contraction
  let c_bd := max (3 / 4 : ℝ) (1 - (10 / 44) * η * ε)
  have hc_lt1 : c_bd < 1 := by
    have hpos_term : 0 < (10 / 44 : ℝ) * η * ε := by positivity
    exact max_lt (by norm_num) (by linarith only [hpos_term])
  have hc_pos : 0 ≤ c_bd := le_trans (by norm_num) (le_max_left _ _)
  have hdist_le : ∀ q₁ ∈ {p ∈ C | inner ℝ vε p = tε - ε / 2},
      ∀ q₂ ∈ {p ∈ C | inner ℝ vε p = tε - ε / 2}, dist q₁ q₂ ≤ √c_bd := by
    have hord : ∀ q₁ ∈ {p ∈ C | inner ℝ vε p = tε - ε / 2},
        ∀ q₂ ∈ {p ∈ C | inner ℝ vε p = tε - ε / 2}, py q₁ ≤ py q₂ → dist q₁ q₂ ≤ √c_bd := by
      intro q₁ hq₁ q₂ hq₂ hy12
      have hx₁_eq : px q₁ = ε * (py q₁ - 1 / 2) + tε := by
        have := hq₁.2; rw [hvε_inner] at this; linarith only [this]
      have hx₂_eq : px q₂ = ε * (py q₂ - 1 / 2) + tε := by
        have := hq₂.2; rw [hvε_inner] at this; linarith only [this]
      have hsq_eq : (px q₁ - px q₂) ^ 2 + (py q₁ - py q₂) ^ 2 = (1 + ε ^ 2) * (py q₂ - py q₁) ^ 2 := by
        rw [hx₁_eq, hx₂_eq]; ring
      refine dist_le_of_sq_le (Real.sqrt_nonneg _) ?_
      rw [Real.sq_sqrt hc_pos, hsq_eq]
      have hKε0 : 0 ≤ K * ε := by positivity
      have hKεsq : 3 * K ^ 2 * ε ^ 2 ≤ 3 / 10000 := by
        have : (K * ε) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith only [hKε, hKε0]
        nlinarith only [this]
      have hy₂_rough : py q₂ ≤ 11 / 10 := by
        by_cases hyh : py q₂ ≤ 1 / 2
        · linarith only [hyh]
        · push Not at hyh
          have h1 := (hglob q₂ hq₂.1).2
          have habx : |px q₂| ≤ ε * (py q₂ - 1 / 2) + |tε| := by
            rw [hx₂_eq]
            calc |ε * (py q₂ - 1 / 2) + tε| ≤ |ε * (py q₂ - 1 / 2)| + |tε| := abs_add_le _ _
              _ = ε * (py q₂ - 1 / 2) + |tε| := by rw [abs_of_pos (mul_pos hε (by linarith only [hyh]))]
          have hKabs : K * |px q₂| ≤ K * ε * (py q₂ - 1 / 2) + 3 * K ^ 2 * ε ^ 2 := by
            calc K * |px q₂| ≤ K * (ε * (py q₂ - 1 / 2) + |tε|) := mul_le_mul_of_nonneg_left habx hKpos.le
              _ ≤ K * (ε * (py q₂ - 1 / 2) + 3 * K * ε ^ 2) :=
                mul_le_mul_of_nonneg_left (by linarith only [htε_abs]) hKpos.le
              _ = K * ε * (py q₂ - 1 / 2) + 3 * K ^ 2 * ε ^ 2 := by ring
          have h2id : (1 - K * ε) * (py q₂ - 1 / 2) = py q₂ - 1 / 2 - K * ε * (py q₂ - 1 / 2) := by ring
          have h2 : (1 - K * ε) * (py q₂ - 1 / 2) ≤ 1 / 2 + 3 * K ^ 2 * ε ^ 2 := by
            linarith only [h1, hKabs, h2id]
          have h99 : (99 / 100 : ℝ) * (py q₂ - 1 / 2) ≤ (1 - K * ε) * (py q₂ - 1 / 2) :=
            mul_le_mul_of_nonneg_right (by linarith only [hKε]) (by linarith only [hyh])
          linarith only [h2, hKεsq, h99]
      have hy₁_rough : -(1 / 10 : ℝ) ≤ py q₁ := by
        by_cases hyh : 1 / 2 ≤ py q₁
        · linarith only [hyh]
        · push Not at hyh
          have h1 := (hglob q₁ hq₁.1).1
          have habx : |px q₁| ≤ ε * (1 / 2 - py q₁) + |tε| := by
            rw [hx₁_eq]
            calc |ε * (py q₁ - 1 / 2) + tε| ≤ |ε * (py q₁ - 1 / 2)| + |tε| := abs_add_le _ _
              _ = ε * (1 / 2 - py q₁) + |tε| := by
                rw [abs_of_neg (mul_neg_of_pos_of_neg hε (by linarith only [hyh]))]; ring
          have hKabs : K * |px q₁| ≤ K * ε * (1 / 2 - py q₁) + 3 * K ^ 2 * ε ^ 2 := by
            calc K * |px q₁| ≤ K * (ε * (1 / 2 - py q₁) + |tε|) := mul_le_mul_of_nonneg_left habx hKpos.le
              _ ≤ K * (ε * (1 / 2 - py q₁) + 3 * K * ε ^ 2) :=
                mul_le_mul_of_nonneg_left (by linarith only [htε_abs]) hKpos.le
              _ = K * ε * (1 / 2 - py q₁) + 3 * K ^ 2 * ε ^ 2 := by ring
          have h2id : (1 - K * ε) * (1 / 2 - py q₁) = 1 / 2 - py q₁ - K * ε * (1 / 2 - py q₁) := by ring
          have h2 : (1 - K * ε) * (1 / 2 - py q₁) ≤ 1 / 2 + 3 * K ^ 2 * ε ^ 2 := by
            linarith only [h1, hKabs, h2id]
          have h99 : (99 / 100 : ℝ) * (1 / 2 - py q₁) ≤ (1 - K * ε) * (1 / 2 - py q₁) :=
            mul_le_mul_of_nonneg_right (by linarith only [hKε]) (by linarith only [hyh])
          linarith only [h2, hKεsq, h99]
      by_cases hcase1 : py q₂ ≤ 3 / 4 ∨ 1 / 4 ≤ py q₁
      · have hdiff : py q₂ - py q₁ ≤ 17 / 20 := by rcases hcase1 with h | h <;> linarith only [h, hy₁_rough, hy₂_rough]
        have h1 : (1 + ε ^ 2) * (py q₂ - py q₁) ^ 2 ≤ 3 / 4 := by
          have hnn : 0 ≤ py q₂ - py q₁ := by linarith only [hy12]
          have hεsq : ε ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith only [hε, hε_le1]
          have hd2 : (py q₂ - py q₁) ^ 2 ≤ (17 / 20 : ℝ) ^ 2 := by nlinarith only [hdiff, hnn]
          nlinarith only [hεsq, hd2, sq_nonneg ε, sq_nonneg (py q₂ - py q₁)]
        exact le_trans h1 (le_max_left _ _)
      · push Not at hcase1
        obtain ⟨hy₂_gt, hy₁_lt⟩ := hcase1
        have h3K : 3 * K * ε ^ 2 ≤ (3 / 100) * ε := by nlinarith only [hKε, hε]
        have hx₂_pos : 0 < px q₂ := by
          nlinarith only [hx₂_eq, hy₂_gt, (abs_le.mp htε_abs).1, h3K, hε]
        have hx₁_neg : px q₁ < 0 := by
          nlinarith only [hx₁_eq, hy₁_lt, (abs_le.mp htε_abs).2, h3K, hε]
        have hq₂_bd : py q₂ ≤ 1 + bPlus C * px q₂ := (hbound_pos q₂ hq₂.1 hx₂_pos.le).2
        have hq₁_bd : aMinus C * px q₁ ≤ py q₁ := (hbound_neg q₁ hq₁.1 hx₁_neg.le).1
        have h1bP_lo : 99 / 100 ≤ 1 - bPlus C * ε := by nlinarith only [(abs_le.mp hKbP).2, hKε, hε]
        have h1aM_lo : 99 / 100 ≤ 1 - aMinus C * ε := by nlinarith only [(abs_le.mp hKaM).2, hKε, hε]
        have hq₂_lin : (1 - bPlus C * ε) * (py q₂ - 1) ≤ bPlus C / 2 * ε + bPlus C * tε := by
          rw [hx₂_eq] at hq₂_bd; linarith only [hq₂_bd]
        have hq₁_lin : -(aMinus C / 2) * ε + aMinus C * tε ≤ (1 - aMinus C * ε) * py q₁ := by
          rw [hx₁_eq] at hq₁_bd; linarith only [hq₁_bd]
        have hE_nn : 0 ≤ K ^ 2 * ε ^ 2 := by positivity
        have hy₂_ub : py q₂ - 1 ≤ bPlus C / 2 * ε + 5 * K ^ 2 * ε ^ 2 := by
          have hbt : bPlus C * tε ≤ 3 * K ^ 2 * ε ^ 2 := by
            calc bPlus C * tε ≤ |bPlus C * tε| := le_abs_self _
              _ = |bPlus C| * |tε| := abs_mul _ _
              _ ≤ K * (3 * K * ε ^ 2) := mul_le_mul hKbP htε_abs (abs_nonneg _) hKpos.le
              _ = 3 * K ^ 2 * ε ^ 2 := by ring
          have hB2 : (bPlus C * ε) ^ 2 ≤ K ^ 2 * ε ^ 2 := by
            have hab : |bPlus C * ε| ≤ K * ε := by
              rw [abs_mul, abs_of_pos hε]; exact mul_le_mul_of_nonneg_right hKbP hε.le
            nlinarith only [abs_le.mp hab]
          have h5E : (99 / 100 : ℝ) * (5 * K ^ 2 * ε ^ 2) ≤ (1 - bPlus C * ε) * (5 * K ^ 2 * ε ^ 2) :=
            mul_le_mul_of_nonneg_right h1bP_lo (by positivity)
          have hkey_id : (1 - bPlus C * ε) * (bPlus C / 2 * ε + 5 * K ^ 2 * ε ^ 2) -
              (bPlus C / 2 * ε + bPlus C * tε) =
              -(bPlus C * ε) ^ 2 / 2 + (1 - bPlus C * ε) * (5 * K ^ 2 * ε ^ 2) - bPlus C * tε := by ring
          have hkey : (1 - bPlus C * ε) * (py q₂ - 1) ≤
              (1 - bPlus C * ε) * (bPlus C / 2 * ε + 5 * K ^ 2 * ε ^ 2) := by
            linarith only [hq₂_lin, hbt, hB2, h5E, hkey_id, hE_nn]
          exact le_of_mul_le_mul_left hkey (by linarith only [h1bP_lo])
        have hy₁_lb : -(aMinus C / 2) * ε - 5 * K ^ 2 * ε ^ 2 ≤ py q₁ := by
          have hat : -(3 * K ^ 2 * ε ^ 2) ≤ aMinus C * tε := by
            have : |aMinus C * tε| ≤ K * (3 * K * ε ^ 2) := by
              rw [abs_mul]; exact mul_le_mul hKaM htε_abs (abs_nonneg _) hKpos.le
            have h1 := (abs_le.mp this).1
            linarith only [h1]
          have hA2 : (aMinus C * ε) ^ 2 ≤ K ^ 2 * ε ^ 2 := by
            have hab : |aMinus C * ε| ≤ K * ε := by
              rw [abs_mul, abs_of_pos hε]; exact mul_le_mul_of_nonneg_right hKaM hε.le
            nlinarith only [abs_le.mp hab]
          have h5E : (99 / 100 : ℝ) * (5 * K ^ 2 * ε ^ 2) ≤ (1 - aMinus C * ε) * (5 * K ^ 2 * ε ^ 2) :=
            mul_le_mul_of_nonneg_right h1aM_lo (by positivity)
          have hkey_id : -(aMinus C / 2) * ε + aMinus C * tε -
              (1 - aMinus C * ε) * (-(aMinus C / 2) * ε - 5 * K ^ 2 * ε ^ 2) =
              -(aMinus C * ε) ^ 2 / 2 + (1 - aMinus C * ε) * (5 * K ^ 2 * ε ^ 2) + aMinus C * tε := by ring
          have hkey : (1 - aMinus C * ε) * (-(aMinus C / 2) * ε - 5 * K ^ 2 * ε ^ 2) ≤
              (1 - aMinus C * ε) * py q₁ := by
            linarith only [hq₁_lin, hat, hA2, h5E, hkey_id, hE_nn]
          exact le_of_mul_le_mul_left hkey (by linarith only [h1aM_lo])
        have hdiff : py q₂ - py q₁ ≤ 1 - (η / 4) * ε := by
          have h10 : 10 * K ^ 2 * ε ≤ η / 4 := by
            have := mul_le_mul_of_nonneg_left hε_η (show (0 : ℝ) ≤ 40 * K ^ 2 + 4 by positivity)
            rw [mul_div_cancel₀ _ (by positivity)] at this
            linarith only [this, hε]
          have h10ε : 10 * K ^ 2 * ε ^ 2 ≤ (η / 4) * ε := by nlinarith only [h10, hε]
          have hη_def : aMinus C + bPlus C = -η := by dsimp [η]; ring
          have hlin_comb : bPlus C / 2 * ε + aMinus C / 2 * ε = -(η / 2) * ε := by
            nlinarith only [hη_def, hε]
          linarith only [hy₂_ub, hy₁_lb, h10ε, hlin_comb]
        have h44 : (44 : ℝ) ≤ 40 * K ^ 2 + 4 := by nlinarith only [hK1]
        have hε_le_η : ε ≤ η / 44 :=
          le_trans hε_η (div_le_div_of_nonneg_left hη.le (by norm_num) h44)
        have hfinal : (1 + ε ^ 2) * (py q₂ - py q₁) ^ 2 ≤ 1 - (10 / 44) * η * ε := by
          have hnn : 0 ≤ py q₂ - py q₁ := by linarith only [hy12]
          have hsq : (py q₂ - py q₁) ^ 2 ≤ (1 - (η / 4) * ε) ^ 2 := by nlinarith only [hnn, hdiff]
          have hη_le : η ≤ 2 * K := by dsimp [η]; linarith only [(abs_le.mp hKaM).1, (abs_le.mp hKbP).1]
          have hηε_le : (η / 4) * ε ≤ 1 := by nlinarith only [hη_le, hKε, hε]
          have hηε_nn : 0 ≤ (η / 4) * ε := by positivity
          have hsub1 : (1 - (η / 4) * ε) ^ 2 ≤ 1 - (η / 4) * ε := by nlinarith only [hηε_le, hηε_nn]
          have h1 : (1 + ε ^ 2) * (py q₂ - py q₁) ^ 2 ≤ (1 + ε ^ 2) * (1 - (η / 4) * ε) :=
            mul_le_mul_of_nonneg_left (le_trans hsq hsub1) (by positivity)
          have hε2_le : ε ^ 2 ≤ (η / 44) * ε := by nlinarith only [hε_le_η, hε]
          have hterm_nn : 0 ≤ (η / 4) * ε * ε ^ 2 := by positivity
          have h1_exp : (1 + ε ^ 2) * (1 - (η / 4) * ε) =
              1 - (η / 4) * ε + ε ^ 2 - (η / 4) * ε * ε ^ 2 := by ring
          linarith only [h1, h1_exp, hε2_le, hterm_nn]
        exact le_trans hfinal (le_max_right _ _)
    intro q₁ hq₁ q₂ hq₂
    rcases le_total (py q₁) (py q₂) with h | h
    · exact hord q₁ hq₁ q₂ hq₂ h
    · rw [dist_comm]; exact hord q₂ hq₂ q₁ hq₁ h
  have hdiam_le : OMA.S_mo_201359.chordLength C vε (tε - ε / 2) ≤ √c_bd :=
    Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg _) hdist_le
  have hsqrt_lt : √c_bd < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
  linarith

/-- Horizontal reflection `(-x, y)` preserves `Normalized`. -/
noncomputable def reflectX : Plane ≃ₗᵢ[ℝ] Plane :=
  { toLinearEquiv :=
      { toFun := fun p => mkP (-px p) (py p)
        map_add' := fun p q => by
          apply plane_ext
          · simp; ring
          · simp
        map_smul' := fun c p => by apply plane_ext <;> simp
        invFun := fun p => mkP (-px p) (py p)
        left_inv := fun p => by apply plane_ext <;> simp
        right_inv := fun p => by apply plane_ext <;> simp }
    norm_map' := fun p => by
      change ‖mkP (-px p) (py p)‖ = ‖p‖
      have hsq : ‖mkP (-px p) (py p)‖ ^ 2 = ‖p‖ ^ 2 := by
        rw [norm_sq_plane, norm_sq_plane]; simp
      nlinarith [norm_nonneg (mkP (-px p) (py p)), norm_nonneg p] }

@[simp] lemma reflectX_apply (p : Plane) : reflectX p = mkP (-px p) (py p) := rfl

lemma reflectX_invol (p : Plane) : reflectX (reflectX p) = p := by
  apply plane_ext <;> simp

lemma normalized_reflect {C : Set Plane} (hN : Normalized C) :
    Normalized (reflectX '' C) := by
  have hmp := reflectX.measurePreserving
  have himg_eq : ∀ S : Set Plane, reflectX '' S = reflectX ⁻¹' S := by
    intro S; ext x; constructor
    · rintro ⟨y, hy, rfl⟩; show reflectX (reflectX y) ∈ S; rwa [reflectX_invol]
    · intro hx; exact ⟨reflectX x, hx, reflectX_invol x⟩
  have hvol_img : ∀ S : Set Plane, MeasurableSet S → volume (reflectX '' S) = volume S := by
    intro S hS; rw [himg_eq]; exact hmp.measure_preimage hS.nullMeasurableSet
  have hinner_ref : ∀ u x : Plane, inner ℝ u (reflectX x) = inner ℝ (reflectX u) x := fun u x => by
    simp [inner_plane]
  have hbis_iff : ∀ u s, OMA.S_mo_201359.bisects (reflectX '' C) u s ↔
      OMA.S_mo_201359.bisects C (reflectX u) s := by
    intro u s
    have hside : OMA.S_mo_201359.side (reflectX '' C) u s =
        reflectX '' OMA.S_mo_201359.side C (reflectX u) s := by
      ext x; constructor
      · rintro ⟨⟨y, hy, rfl⟩, hle⟩; exact ⟨y, ⟨hy, by rwa [← hinner_ref]⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hle⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, by rwa [hinner_ref]⟩
    have hopp : OMA.S_mo_201359.opposite (reflectX '' C) u s =
        reflectX '' OMA.S_mo_201359.opposite C (reflectX u) s := by
      ext x; constructor
      · rintro ⟨⟨y, hy, rfl⟩, hle⟩; exact ⟨y, ⟨hy, by rwa [← hinner_ref]⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hle⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, by rwa [hinner_ref]⟩
    have hm1 := measurableSet_side hN.compact.measurableSet (reflectX u) s
    have hm2 := measurableSet_opposite hN.compact.measurableSet (reflectX u) s
    simp only [OMA.S_mo_201359.bisects, hside, hopp, hvol_img _ hm1, hvol_img _ hm2]
    constructor <;> rintro ⟨hu, heq⟩
    · exact ⟨fun h => hu (reflectX.map_eq_zero_iff.mp h), heq⟩
    · exact ⟨fun h => hu (by rw [h, map_zero]), heq⟩
  refine
    { compact := hN.compact.image reflectX.continuous
      convex := hN.convex.linear_image reflectX.toLinearMap
      int_ne := by
        obtain ⟨x, hx⟩ := hN.int_ne
        have hopen : IsOpen (reflectX '' interior C) :=
          reflectX.toHomeomorph.isOpenMap _ isOpen_interior
        have hsub : reflectX '' interior C ⊆ reflectX '' C := image_mono interior_subset
        exact ⟨reflectX x, interior_maximal hsub hopen ⟨x, hx, rfl⟩⟩
      bisect_zero := by
        rw [hbis_iff]
        have hneg : reflectX (mkP 1 0) = -(mkP 1 0) := by apply plane_ext <;> simp
        rw [hneg]
        obtain ⟨h10, heq⟩ := hN.bisect_zero
        refine ⟨neg_ne_zero.mpr h10, ?_⟩
        have hs1 : OMA.S_mo_201359.side C (-(mkP 1 0)) 0 = OMA.S_mo_201359.opposite C (mkP 1 0) 0 := by
          ext p; simp [OMA.S_mo_201359.side, OMA.S_mo_201359.opposite, inner_neg_left]
        have hs2 : OMA.S_mo_201359.opposite C (-(mkP 1 0)) 0 = OMA.S_mo_201359.side C (mkP 1 0) 0 := by
          ext p; simp [OMA.S_mo_201359.side, OMA.S_mo_201359.opposite, inner_neg_left]
        rw [hs1, hs2, heq]
      chord_eq := by
        ext p
        constructor
        · rintro ⟨⟨q, hq, rfl⟩, hpx⟩
          have hqx : px q = 0 := by simp at hpx; linarith
          have hqS : q ∈ {p ∈ C | px p = 0} := ⟨hq, hqx⟩
          rw [hN.chord_eq] at hqS
          exact ⟨hpx, hqS.2.1, hqS.2.2⟩
        · rintro ⟨hpx, hy0, hy1⟩
          have hpS : p ∈ {p ∈ C | px p = 0} := by rw [hN.chord_eq]; exact ⟨hpx, hy0, hy1⟩
          refine ⟨⟨p, hpS.1, ?_⟩, hpx⟩
          apply plane_ext <;> simp [hpx]
      minimal := fun v s hbis => by
        rw [hbis_iff] at hbis
        have hch : {p ∈ reflectX '' C | inner ℝ v p = s} =
            reflectX '' {p ∈ C | inner ℝ (reflectX v) p = s} := by
          ext p; constructor
          · rintro ⟨⟨q, hq, rfl⟩, heq⟩; exact ⟨q, ⟨hq, by rwa [← hinner_ref]⟩, rfl⟩
          · rintro ⟨q, ⟨hq, heq⟩, rfl⟩; exact ⟨⟨q, hq, rfl⟩, by rwa [hinner_ref]⟩
        rw [OMA.S_mo_201359.chordLength, hch, reflectX.isometry.diam_image]
        exact hN.minimal (reflectX v) s hbis }

lemma fBot_reflect (C : Set Plane) (x : ℝ) : fBot (reflectX '' C) x = fBot C (-x) := by
  unfold fBot
  congr 1; ext y; constructor
  · rintro ⟨q, hq, heq⟩
    have : q = mkP (-x) y := by
      have h1 := congrArg px heq; have h2 := congrArg py heq
      simp at h1 h2; apply plane_ext <;> simp <;> linarith
    show mkP (-x) y ∈ C
    rwa [← this]
  · intro h; exact ⟨mkP (-x) y, h, by apply plane_ext <;> simp⟩

lemma gTop_reflect (C : Set Plane) (x : ℝ) : gTop (reflectX '' C) x = gTop C (-x) := by
  unfold gTop
  congr 1; ext y; constructor
  · rintro ⟨q, hq, heq⟩
    have : q = mkP (-x) y := by
      have h1 := congrArg px heq; have h2 := congrArg py heq
      simp at h1 h2; apply plane_ext <;> simp <;> linarith
    show mkP (-x) y ∈ C
    rwa [← this]
  · intro h; exact ⟨mkP (-x) y, h, by apply plane_ext <;> simp⟩

lemma aMinus_reflect (C : Set Plane) : aMinus (reflectX '' C) = -aPlus C := by
  unfold aMinus aPlus
  rw [← Real.sSup_neg]
  congr 1; ext q
  simp only [Set.mem_neg, mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, ⟨y, hy⟩, rfl⟩
    refine ⟨-x, by linarith, ?_, ?_⟩
    · rcases hy with ⟨p, hp, heq⟩
      refine ⟨y, ?_⟩
      have h1 := congrArg px heq; have h2 := congrArg py heq
      simp at h1 h2
      have : mkP (-x) y = p := by apply plane_ext <;> simp <;> linarith
      rwa [this]
    · rw [fBot_reflect]; ring
  · rintro ⟨x, hx, ⟨y, hy⟩, hq⟩
    refine ⟨-x, by linarith, ⟨y, mkP x y, hy, by apply plane_ext <;> simp⟩, ?_⟩
    rw [fBot_reflect, neg_neg]
    have hq' : q = -(fBot C x / x) := by linarith
    rw [hq']; ring

lemma bPlus_reflect (C : Set Plane) : bPlus (reflectX '' C) = -bMinus C := by
  unfold bPlus bMinus
  rw [← Real.sSup_neg]
  congr 1; ext q
  simp only [Set.mem_neg, mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, ⟨y, hy⟩, rfl⟩
    refine ⟨-x, by linarith, ?_, ?_⟩
    · rcases hy with ⟨p, hp, heq⟩
      refine ⟨y, ?_⟩
      have h1 := congrArg px heq; have h2 := congrArg py heq
      simp at h1 h2
      have : mkP (-x) y = p := by apply plane_ext <;> simp <;> linarith
      rwa [this]
    · rw [gTop_reflect]; ring
  · rintro ⟨x, hx, ⟨y, hy⟩, hq⟩
    refine ⟨-x, by linarith, ⟨y, mkP x y, hy, by apply plane_ext <;> simp⟩, ?_⟩
    rw [gTop_reflect, neg_neg]
    have hq' : q = -((gTop C x - 1) / x) := by linarith
    rw [hq']; ring

/-- Theorem 3.4: Symmetric supporting wedge `s * x ≤ y ≤ 1 - s * x` with `|s| ≤ 1`. -/
lemma exists_supporting_wedge {C : Set Plane} (hN : Normalized C) :
    ∃ s : ℝ, |s| ≤ 1 ∧ ∀ p ∈ C, s * px p ≤ py p ∧ py p ≤ 1 - s * px p := by
  obtain ⟨ha_le, hb_le, hneg, hpos⟩ := slopes_basic hN
  have ht1 : 0 ≤ aMinus C + bPlus C := tilt_nonneg hN
  have ht2 : 0 ≤ aMinus (reflectX '' C) + bPlus (reflectX '' C) := tilt_nonneg (normalized_reflect hN)
  rw [aMinus_reflect, bPlus_reflect] at ht2
  -- Chain: 0 ≤ aMinus + bPlus ≤ aPlus + bMinus ≤ 0
  set s := aMinus C
  have ha_eq : aPlus C = s := by linarith
  have hb_eq1 : bPlus C = -s := by linarith
  have hb_eq2 : bMinus C = -s := by linarith
  have hwedge : ∀ p ∈ C, s * px p ≤ py p ∧ py p ≤ 1 - s * px p := by
    intro p hp
    rcases le_total (px p) 0 with hx | hx
    · obtain ⟨h1, h2⟩ := hneg p hp hx
      rw [hb_eq2] at h2; exact ⟨h1, by linarith⟩
    · obtain ⟨h1, h2⟩ := hpos p hp hx
      rw [ha_eq] at h1; rw [hb_eq1] at h2; exact ⟨h1, by linarith⟩
  have hvol_half : (1 / 4 : ℝ) ≤ (volume {p ∈ C | px p ≤ 0}).toReal ∧
      (1 / 4 : ℝ) ≤ (volume {p ∈ C | 0 ≤ px p}).toReal := by
    have harea := normalized_area_ge_half hN
    obtain ⟨h1, h2⟩ := normalized_vol_side_eq hN
    exact ⟨by linarith, by linarith⟩
  have hs_abs : |s| ≤ 1 := by
    rw [abs_le]
    constructor
    · by_contra hlt
      push Not at hlt
      have hs_neg : s < 0 := by linarith
      let Tri : Set Plane := {p : Plane | 1 / (2 * s) ≤ px p ∧ px p ≤ 0 ∧
        s * px p ≤ py p ∧ py p ≤ 1 - s * px p}
      have hsub : {p ∈ C | px p ≤ 0} ⊆ Tri := by
        intro p ⟨hpC, hpx⟩
        obtain ⟨h1, h2⟩ := hwedge p hpC
        have h3 : 2 * s * px p ≤ 1 := by linarith
        have h4 : 1 / (2 * s) ≤ px p := by
          rw [div_le_iff_of_neg (by linarith)]; linarith
        exact ⟨h4, hpx, h1, h2⟩
      have hTri_vol : volume Tri = ENNReal.ofReal (-1 / (4 * s)) := by
        rw [volume_region_x (1 / (2 * s)) 0 (div_nonpos_of_nonneg_of_nonpos zero_le_one (by linarith))
          (fun x => s * x) (fun x => 1 - s * x) (by fun_prop) (by fun_prop) (fun x hx => by
            have := (div_le_iff_of_neg (by linarith : 2 * s < 0)).mp hx.1; linarith)]
        congr 1
        have hf : (fun x : ℝ => 1 - s * x - s * x) = fun x => (-2 * s) * x + 1 := by ext x; ring
        rw [hf, integral_linear]
        have hsne : s ≠ 0 := hs_neg.ne
        field_simp; ring
      have hle_m : volume {p ∈ C | px p ≤ 0} ≤ ENNReal.ofReal (-1 / (4 * s)) := by
        rw [← hTri_vol]; exact measure_mono hsub
      have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle_m
      rw [ENNReal.toReal_ofReal (div_nonneg_of_nonpos (by norm_num) (by linarith))] at hle
      have h14 : 1 / 4 ≤ -1 / (4 * s) := le_trans hvol_half.1 hle
      have := mul_le_mul_of_nonpos_right h14 (show 4 * s ≤ 0 by linarith)
      rw [div_mul_cancel₀ _ (by linarith : 4 * s ≠ 0)] at this
      linarith
    · by_contra hgt
      push Not at hgt
      have hs_pos : 0 < s := by linarith
      let Tri : Set Plane := {p : Plane | 0 ≤ px p ∧ px p ≤ 1 / (2 * s) ∧
        s * px p ≤ py p ∧ py p ≤ 1 - s * px p}
      have hsub : {p ∈ C | 0 ≤ px p} ⊆ Tri := by
        intro p ⟨hpC, hpx⟩
        obtain ⟨h1, h2⟩ := hwedge p hpC
        have h3 : 2 * s * px p ≤ 1 := by linarith
        have h4 : px p ≤ 1 / (2 * s) := (le_div_iff₀ (by linarith)).mpr (by linarith)
        exact ⟨hpx, h4, h1, h2⟩
      have hTri_vol : volume Tri = ENNReal.ofReal (1 / (4 * s)) := by
        rw [volume_region_x 0 (1 / (2 * s)) (by positivity)
          (fun x => s * x) (fun x => 1 - s * x) (by fun_prop) (by fun_prop) (fun x hx => by
            have := (le_div_iff₀ (by linarith : 0 < 2 * s)).mp hx.2; linarith)]
        congr 1
        have hf : (fun x : ℝ => 1 - s * x - s * x) = fun x => (-2 * s) * x + 1 := by ext x; ring
        rw [hf, integral_linear]
        have hsne : s ≠ 0 := hs_pos.ne'
        field_simp; ring
      have hle_m : volume {p ∈ C | 0 ≤ px p} ≤ ENNReal.ofReal (1 / (4 * s)) := by
        rw [← hTri_vol]; exact measure_mono hsub
      have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle_m
      rw [ENNReal.toReal_ofReal (by positivity)] at hle
      have h14 : 1 / 4 ≤ 1 / (4 * s) := le_trans hvol_half.2 hle
      have := mul_le_mul_of_nonneg_right h14 (show 0 ≤ 4 * s by linarith)
      rw [div_mul_cancel₀ _ (by linarith : 4 * s ≠ 0)] at this
      linarith
  exact ⟨s, hs_abs, hwedge⟩

/-! ### Step 4 & 5: Left-width, explicit interior disk, and all ball-area cases -/

lemma volume_closedBall_scale (p c : Plane) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    ENNReal.ofReal ((r₁ / r₂) ^ 2) * volume (Metric.closedBall p r₂) =
      volume (Metric.closedBall c r₁) := by
  rw [Measure.addHaar_closedBall volume p hr₂.le, Measure.addHaar_closedBall volume c hr₁.le,
    finrank_plane, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

/-- Helper for Step 5: `volume (Cplus ∩ B) ≤ K * volume (Cminus ∩ B)` with `K ≤ 102399` implies the main bound. -/
lemma ratio_of_mul_bound {C : Set Plane} (hN : Normalized C) (p : Plane) (r : ℝ)
    {K : ℝ} (hK0 : 0 ≤ K) (hKbd : K ≤ 102399)
    (hle : volume ({q ∈ C | 0 ≤ px q} ∩ Metric.closedBall p r) ≤
      ENNReal.ofReal K * volume ({q ∈ C | px q ≤ 0} ∩ Metric.closedBall p r)) :
    ENNReal.ofReal (1 / 102400 : ℝ) * volume (C ∩ Metric.closedBall p r) ≤
      volume ({q ∈ C | px q ≤ 0} ∩ Metric.closedBall p r) := by
  let Cminus : Set Plane := {q ∈ C | px q ≤ 0}
  let Cplus  : Set Plane := {q ∈ C | 0 ≤ px q}
  have hsplit_B : volume (C ∩ Metric.closedBall p r) =
      volume (Cminus ∩ Metric.closedBall p r) + volume (Cplus ∩ Metric.closedBall p r) := by
    have h10 : mkP 1 0 ≠ 0 := by intro h; have := congrArg px h; simp at this
    have h := volume_side_add_opposite (C ∩ Metric.closedBall p r)
      (hN.compact.measurableSet.inter Metric.isClosed_closedBall.measurableSet) (mkP 1 0) h10 0
    have e1 : OMA.S_mo_201359.side (C ∩ Metric.closedBall p r) (mkP 1 0) 0 =
        Cminus ∩ Metric.closedBall p r := by
      ext q; simp [OMA.S_mo_201359.side, Cminus, inner_plane]; tauto
    have e2 : OMA.S_mo_201359.opposite (C ∩ Metric.closedBall p r) (mkP 1 0) 0 =
        Cplus ∩ Metric.closedBall p r := by
      ext q; simp [OMA.S_mo_201359.opposite, Cplus, inner_plane]; tauto
    rw [e1, e2] at h; exact h.symm
  rw [hsplit_B]
  have hsum : volume (Cminus ∩ Metric.closedBall p r) + volume (Cplus ∩ Metric.closedBall p r) ≤
      ENNReal.ofReal (1 + K) * volume (Cminus ∩ Metric.closedBall p r) := by
    calc volume (Cminus ∩ Metric.closedBall p r) + volume (Cplus ∩ Metric.closedBall p r)
        ≤ 1 * volume (Cminus ∩ Metric.closedBall p r) +
            ENNReal.ofReal K * volume (Cminus ∩ Metric.closedBall p r) := by
          rw [one_mul]; gcongr
      _ = (ENNReal.ofReal 1 + ENNReal.ofReal K) * volume (Cminus ∩ Metric.closedBall p r) := by
          rw [ENNReal.ofReal_one, add_mul]
      _ = ENNReal.ofReal (1 + K) * volume (Cminus ∩ Metric.closedBall p r) := by
          rw [← ENNReal.ofReal_add zero_le_one hK0]
  have hle1 : ENNReal.ofReal ((1 / 102400 : ℝ) * (1 + K)) ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal (1 / 102400 : ℝ) *
        (volume (Cminus ∩ Metric.closedBall p r) + volume (Cplus ∩ Metric.closedBall p r))
      ≤ ENNReal.ofReal (1 / 102400 : ℝ) *
        (ENNReal.ofReal (1 + K) * volume (Cminus ∩ Metric.closedBall p r)) := by gcongr
    _ = ENNReal.ofReal ((1 / 102400 : ℝ) * (1 + K)) * volume (Cminus ∩ Metric.closedBall p r) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ 1 * volume (Cminus ∩ Metric.closedBall p r) := by gcongr
    _ = volume (Cminus ∩ Metric.closedBall p r) := one_mul _

/-- Case 5.1: `0 < r ≤ 4` via explicit interior disk `D₀ = closedBall c₀ (1/40)` and homothety `r/8`. -/
lemma normalized_case_small_r {C : Set Plane} (hN : Normalized C)
    {p Q : Plane} {r s w : ℝ} (hr : 0 < r) (hr4 : r ≤ 4)
    (hp : p ∈ {q ∈ C | px q ≤ 0}) (hp_x_lb : -r ≤ px p)
    (hs_abs : |s| ≤ 1) (hwedge : ∀ q ∈ C, s * px q ≤ py q ∧ py q ≤ 1 - s * px q)
    (hQ_mem : Q ∈ {q ∈ C | px q ≤ 0}) (hw_def : w = -px Q) (hw_gt : (1 / 5 : ℝ) < w) :
    ENNReal.ofReal (1 / 102400 : ℝ) * volume (C ∩ Metric.closedBall p r) ≤
      volume ({q ∈ C | px q ≤ 0} ∩ Metric.closedBall p r) := by
  let Cminus : Set Plane := {q ∈ C | px q ≤ 0}
  have hCminus_conv : Convex ℝ Cminus := by
    intro x hx y hy a b ha hb hab
    refine ⟨hN.convex hx.1 hy.1 ha hb hab, ?_⟩
    simp only [px_add, px_smul]
    nlinarith [hx.2, hy.2]
  have hA : mkP 0 0 ∈ Cminus := ⟨normalized_mem_S hN le_rfl (by norm_num), le_rfl⟩
  have hB : mkP 0 1 ∈ Cminus := ⟨normalized_mem_S hN (by norm_num) le_rfl, le_rfl⟩
  have hM : mkP 0 (1 / 2) ∈ Cminus := ⟨normalized_mem_S hN (by norm_num) (by norm_num), le_rfl⟩
  have hs_lo : -1 ≤ s := (abs_le.mp hs_abs).1
  have hs_hi : s ≤ 1 := (abs_le.mp hs_abs).2
  have hw_pos : 0 < w := by linarith
  have hQ_y : -w ≤ py Q ∧ py Q ≤ 1 + w := by
    obtain ⟨h1, h2⟩ := hwedge Q hQ_mem.1
    have hQx : px Q = -w := by linarith
    rw [hQx] at h1 h2
    exact ⟨by nlinarith, by nlinarith⟩
  let lam0 := (1 / 5 : ℝ) / w
  have hlam0_pos : 0 ≤ lam0 := by positivity
  have hlam0_le1 : lam0 ≤ 1 := (div_le_one hw_pos).mpr hw_gt.le
  let Q0 : Plane := (1 - lam0) • mkP 0 (1 / 2) + lam0 • Q
  have hQ0_mem : Q0 ∈ Cminus := hCminus_conv hM hQ_mem (by linarith) hlam0_pos (by ring)
  have hQ0_x : px Q0 = -(1 / 5 : ℝ) := by
    simp only [Q0, px_add, px_smul, px_mkP, lam0]
    have hQx : px Q = -w := by linarith
    rw [hQx, mul_zero, zero_add, mul_neg, div_mul_cancel₀ _ hw_pos.ne']
  set y0s := py Q0
  have hy0s_bd : -(1 / 5 : ℝ) ≤ y0s ∧ y0s ≤ 6 / 5 := by
    have hy0s_eq : y0s = (1 - lam0) * (1 / 2) + lam0 * py Q := by simp [y0s, Q0]
    have hlw : lam0 * w = 1 / 5 := div_mul_cancel₀ _ hw_pos.ne'
    rw [hy0s_eq]
    constructor
    · have h1 := mul_le_mul_of_nonneg_left hQ_y.1 hlam0_pos; linarith
    · have h1 := mul_le_mul_of_nonneg_left hQ_y.2 hlam0_pos; linarith
  let c0 : Plane := mkP (-(1 / 10 : ℝ)) (1 / 4 + y0s / 2)
  have hD0_sub : Metric.closedBall c0 (1 / 40 : ℝ) ⊆ Cminus := by
    intro z hz
    have hdz : dist z c0 ≤ 1 / 40 := Metric.mem_closedBall.mp hz
    have hu : |px z - (-(1 / 10 : ℝ))| ≤ 1 / 40 := by
      have := abs_px_le_norm (z - c0)
      rw [← dist_eq_norm, px_sub] at this
      simpa [c0] using le_trans this hdz
    have hv : |py z - (1 / 4 + y0s / 2)| ≤ 1 / 40 := by
      have := abs_py_le_norm (z - c0)
      rw [← dist_eq_norm, py_sub] at this
      simpa [c0] using le_trans this hdz
    set u := px z + 1 / 10
    set v := py z - (1 / 4 + y0s / 2)
    have hu_bd : -(1 / 40 : ℝ) ≤ u ∧ u ≤ 1 / 40 := by
      have := abs_le.mp hu; dsimp [u]; constructor <;> linarith
    have hv_bd : -(1 / 40 : ℝ) ≤ v ∧ v ≤ 1 / 40 := abs_le.mp hv
    set lQ := -5 * px z
    set lB := py z + 5 * y0s * px z
    set lA := 1 - lB - lQ
    have hlQ_eq : lQ = 1 / 2 - 5 * u := by dsimp [lQ, u]; ring
    have hlB_eq : lB = 1 / 4 + v + 5 * y0s * u := by dsimp [lB, u, v]; ring
    have hlA_eq : lA = 1 / 4 - v + 5 * (1 - y0s) * u := by dsimp [lA, lB, lQ, u, v]; ring
    have hlQ_pos : 3 / 8 ≤ lQ := by linarith
    have hlB_pos : 3 / 40 ≤ lB := by nlinarith only [hlB_eq, hy0s_bd.1, hy0s_bd.2, hu_bd.1, hu_bd.2, hv_bd.1]
    have hlA_pos : 3 / 40 ≤ lA := by nlinarith only [hlA_eq, hy0s_bd.1, hy0s_bd.2, hu_bd.1, hu_bd.2, hv_bd.2]
    have hz_eq : z = lA • mkP 0 0 + lB • mkP 0 1 + lQ • Q0 := by
      apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP, hQ0_x]
      · dsimp [lQ]; ring
      · change py z = lA * 0 + lB * 1 + lQ * y0s
        dsimp [lB, lQ]; ring
    rw [hz_eq]
    have h1lQ : 0 < 1 - lQ := by linarith
    let m := (lA / (1 - lQ)) • mkP 0 0 + (lB / (1 - lQ)) • mkP 0 1
    have hm : m ∈ Cminus := hCminus_conv hA hB (div_nonneg (by linarith) h1lQ.le)
      (div_nonneg (by linarith) h1lQ.le) (by
        rw [← add_div, show lA + lB = 1 - lQ by dsimp [lA]; ring, div_self h1lQ.ne'])
    have hcomb : lA • mkP 0 0 + lB • mkP 0 1 + lQ • Q0 = (1 - lQ) • m + lQ • Q0 := by
      apply plane_ext <;> simp only [m, px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
      · ring
      · simp only [mul_zero, zero_add, mul_one]; rw [mul_div_cancel₀ _ h1lQ.ne']
    rw [hcomb]
    exact hCminus_conv hm hQ0_mem h1lQ.le (by linarith) (by ring)
  have hp_y_bd : -4 ≤ py p ∧ py p ≤ 5 := by
    obtain ⟨h1, h2⟩ := hwedge p hp.1
    have hpx4 : -4 ≤ px p := by linarith
    exact ⟨by nlinarith only [h1, hs_lo, hs_hi, hp.2, hpx4],
      by nlinarith only [h2, hs_lo, hs_hi, hp.2, hpx4]⟩
  have hpc0 : dist p c0 < 7 := by
    have hsq : dist p c0 ^ 2 < 7 ^ 2 := by
      rw [dist_sq_plane]
      simp only [c0, px_mkP, py_mkP]
      have hpx4 : -4 ≤ px p := by linarith
      nlinarith only [hp.2, hpx4, hp_y_bd.1, hp_y_bd.2, hy0s_bd.1, hy0s_bd.2]
    nlinarith only [hsq, dist_nonneg (x := p) (y := c0)]
  set lam := r / 8
  have hlam_pos : 0 < lam := by positivity
  have hlam_le1 : lam ≤ 1 := by dsimp [lam]; linarith
  let c_lam : Plane := (1 - lam) • p + lam • c0
  have hDlam_sub : Metric.closedBall c_lam (r / 320) ⊆ Cminus ∩ Metric.closedBall p r := by
    intro z hz
    have hdz : dist z c_lam ≤ r / 320 := Metric.mem_closedBall.mp hz
    let wpt : Plane := c0 + lam⁻¹ • (z - c_lam)
    have hwpt_D0 : wpt ∈ Metric.closedBall c0 (1 / 40 : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsub : wpt - c0 = lam⁻¹ • (z - c_lam) := by simp [wpt]
      rw [hsub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlam_pos.le), ← dist_eq_norm]
      have h1 : lam⁻¹ * dist z c_lam ≤ lam⁻¹ * (r / 320) :=
        mul_le_mul_of_nonneg_left hdz (inv_nonneg.mpr hlam_pos.le)
      have h2 : lam⁻¹ * (r / 320) = 1 / 40 := by dsimp [lam]; field_simp; ring
      linarith
    have hz_comb : z = (1 - lam) • p + lam • wpt := by
      simp only [wpt, smul_add, smul_inv_smul₀ hlam_pos.ne', c_lam]
      abel
    refine ⟨?_, ?_⟩
    · rw [hz_comb]
      exact hCminus_conv hp (hD0_sub hwpt_D0) (by linarith) hlam_pos.le (by ring)
    · rw [Metric.mem_closedBall, hz_comb, dist_eq_norm]
      have hsub : (1 - lam) • p + lam • wpt - p = lam • (wpt - p) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      rw [hsub, norm_smul, Real.norm_of_nonneg hlam_pos.le, ← dist_eq_norm]
      have htri : dist wpt p ≤ dist wpt c0 + dist c0 p := dist_triangle wpt c0 p
      have hdw : dist wpt c0 ≤ 1 / 40 := Metric.mem_closedBall.mp hwpt_D0
      rw [dist_comm c0 p] at htri
      have : dist wpt p < 8 := by linarith
      dsimp [lam]; nlinarith only [this, hr]
  have hvol_eq := volume_closedBall_scale p c_lam (show 0 < r / 320 by positivity) hr
  have hscale_num : (r / 320 / r) ^ 2 = (1 / 102400 : ℝ) := by field_simp; norm_num
  rw [hscale_num] at hvol_eq
  calc ENNReal.ofReal (1 / 102400 : ℝ) * volume (C ∩ Metric.closedBall p r)
      ≤ ENNReal.ofReal (1 / 102400 : ℝ) * volume (Metric.closedBall p r) := by
        have := measure_mono (μ := volume) (inter_subset_right (s := C) (t := Metric.closedBall p r))
        gcongr
    _ = volume (Metric.closedBall c_lam (r / 320)) := hvol_eq
    _ ≤ volume (Cminus ∩ Metric.closedBall p r) := measure_mono hDlam_sub

/-- Case 5.2: `r > 4` and `s ≤ 0`. -/
lemma normalized_case_large_r_nonpos {C : Set Plane} (hN : Normalized C)
    {p Q : Plane} {r s w : ℝ} (hr : 0 < r) (hr4 : 4 < r)
    (hp : p ∈ {q ∈ C | px q ≤ 0}) (hp_x_lb : -r ≤ px p)
    (hs0 : s ≤ 0) (hwedge : ∀ q ∈ C, s * px q ≤ py q ∧ py q ≤ 1 - s * px q)
    (hQ_mem : Q ∈ {q ∈ C | px q ≤ 0}) (hw_def : w = -px Q)
    (hw_ge : ∀ q ∈ {q ∈ C | px q ≤ 0}, -w ≤ px q) (hw_pos : 0 < w) :
    ENNReal.ofReal (1 / 102400 : ℝ) * volume (C ∩ Metric.closedBall p r) ≤
      volume ({q ∈ C | px q ≤ 0} ∩ Metric.closedBall p r) := by
  let Cminus : Set Plane := {q ∈ C | px q ≤ 0}
  let Cplus  : Set Plane := {q ∈ C | 0 ≤ px q}
  have hCminus_conv : Convex ℝ Cminus := by
    intro x hx y hy a b ha hb hab
    refine ⟨hN.convex hx.1 hy.1 ha hb hab, ?_⟩
    simp only [px_add, px_smul]
    nlinarith [hx.2, hy.2]
  have hA : mkP 0 0 ∈ Cminus := ⟨normalized_mem_S hN le_rfl (by norm_num), le_rfl⟩
  have hB : mkP 0 1 ∈ Cminus := ⟨normalized_mem_S hN (by norm_num) le_rfl, le_rfl⟩
  have hCminus_y : ∀ q ∈ Cminus, 0 ≤ py q ∧ py q ≤ 1 := by
    intro q hq
    obtain ⟨h1, h2⟩ := hwedge q hq.1
    have hsq : 0 ≤ s * px q := mul_nonneg_of_nonpos_of_nonpos hs0 hq.2
    exact ⟨by linarith, by linarith⟩
  have hsw_le : (-s) * w ≤ 1 / 2 := by
    obtain ⟨h1, h2⟩ := hwedge Q hQ_mem.1
    have hQx : px Q = -w := by linarith
    rw [hQx] at h1 h2; linarith
  by_cases hw_half : w ≤ r / 2
  · have hsub : Cminus ⊆ Metric.closedBall p r := by
      intro q hq
      refine Metric.mem_closedBall.mpr (dist_le_of_sq_le hr.le ?_)
      have hqx : -w ≤ px q ∧ px q ≤ 0 := ⟨hw_ge q hq, hq.2⟩
      have hpx : -w ≤ px p ∧ px p ≤ 0 := ⟨hw_ge p hp, hp.2⟩
      have hqy := hCminus_y q hq
      have hpy := hCminus_y p hp
      nlinarith only [hqx.1, hqx.2, hpx.1, hpx.2, hqy.1, hqy.2, hpy.1, hpy.2, hw_half, hr4]
    have heq_m : Cminus ∩ Metric.closedBall p r = Cminus := inter_eq_left.mpr hsub
    have hle_p : volume (Cplus ∩ Metric.closedBall p r) ≤ volume Cminus := by
      have heq := hN.bisect_zero.2
      rw [normalized_side_eq, normalized_opposite_eq] at heq
      calc volume (Cplus ∩ Metric.closedBall p r) ≤ volume Cplus := measure_mono inter_subset_left
        _ = volume Cminus := heq.symm
    apply ratio_of_mul_bound hN p r zero_le_one (by norm_num)
    show volume (Cplus ∩ Metric.closedBall p r) ≤ ENNReal.ofReal 1 * volume (Cminus ∩ Metric.closedBall p r)
    rw [heq_m, ENNReal.ofReal_one, one_mul]
    exact hle_p
  · push Not at hw_half
    have hsr : (-s) * r < 1 := by
      rcases eq_or_lt_of_le hs0 with rfl | hs_neg
      · norm_num
      · nlinarith only [hsw_le, hw_half, hs_neg]
    have hCp_sub : Cplus ∩ Metric.closedBall p r ⊆
        {q : Plane | 0 ≤ px q ∧ px q ≤ r ∧ -1 ≤ py q ∧ py q ≤ 2} := by
      intro q ⟨⟨hqC, hqx⟩, hqB⟩
      have hqx_ub : px q ≤ r := by
        have h1 : px q - px p ≤ dist q p := by
          have h := abs_px_le_norm (q - p)
          rw [← dist_eq_norm, px_sub] at h
          exact le_trans (le_abs_self _) h
        have h2 : dist q p ≤ r := Metric.mem_closedBall.mp hqB
        linarith [hp.2]
      obtain ⟨h1, h2⟩ := hwedge q hqC
      exact ⟨hqx, hqx_ub, by nlinarith only [h1, hsr, hs0, hqx, hqx_ub],
        by nlinarith only [h2, hsr, hs0, hqx, hqx_ub]⟩
    have hCp_vol : volume (Cplus ∩ Metric.closedBall p r) ≤ ENNReal.ofReal (3 * r) := by
      calc volume (Cplus ∩ Metric.closedBall p r)
          ≤ volume {q : Plane | 0 ≤ px q ∧ px q ≤ r ∧ -1 ≤ py q ∧ py q ≤ 2} := measure_mono hCp_sub
        _ = ENNReal.ofReal ((r - 0) * (2 - (-1))) := volume_rect 0 r (-1) 2 hr.le (by norm_num)
        _ = ENNReal.ofReal (3 * r) := by congr 1; ring
    set L := min w r
    have hL_gt : r / 2 < L := lt_min hw_half (by linarith)
    have hL_le_w : L ≤ w := min_le_left _ _
    have hL_le_r : L ≤ r := min_le_right _ _
    have hL_pos : 0 < L := by linarith
    let U : Set Plane := {q : Plane | -(L / 2) ≤ px q ∧ px q ≤ -(L / 4) ∧
      (px q / (-w)) * py Q ≤ py q ∧ py q ≤ 1 + (px q / (-w)) * (py Q - 1)}
    have hQ_eq : mkP (-w) (py Q) ∈ Cminus := by
      have : mkP (-w) (py Q) = Q := by apply plane_ext <;> simp; linarith
      rwa [this]
    have hU_sub : U ⊆ Cminus ∩ Metric.closedBall p r := by
      intro q hq
      have hq_tri : q ∈ Cminus := by
        refine (triangle_subset_convex hCminus_conv hA hB hQ_eq q).2 (by linarith) ?_
        exact ⟨by linarith [hq.1], by linarith [hq.2.1], hq.2.2.1, hq.2.2.2⟩
      refine ⟨hq_tri, Metric.mem_closedBall.mpr (dist_le_of_sq_le hr.le ?_)⟩
      have hpx_L : -L ≤ px p ∧ px p ≤ 0 := ⟨by
        have h1 := hw_ge p hp
        exact neg_le.mp (le_trans (le_min (neg_le.mp h1) (neg_le.mp hp_x_lb)) le_rfl), hp.2⟩
      have hqy := hCminus_y q hq_tri
      have hpy := hCminus_y p hp
      have hdx : (px q - px p) ^ 2 ≤ (3 / 4 * r) ^ 2 := by
        have h1 : -(3 / 4 * L) ≤ px q - px p := by linarith only [hq.1, hpx_L.2, hL_pos]
        have h2 : px q - px p ≤ 3 / 4 * L := by linarith only [hq.2.1, hpx_L.1, hL_pos]
        nlinarith only [h1, h2, hL_le_r, hL_pos, hr]
      have hdy : (py q - py p) ^ 2 ≤ (r / 4) ^ 2 := by
        nlinarith only [hqy.1, hqy.2, hpy.1, hpy.2, hr4]
      nlinarith only [hdx, hdy, hr]
    have hU_vol : volume U = ENNReal.ofReal (∫ x in (-(L / 2))..(-(L / 4)), (1 + x / w)) := by
      rw [volume_region_x (-(L / 2)) (-(L / 4)) (by linarith)
        (fun x => (x / (-w)) * py Q) (fun x => 1 + (x / (-w)) * (py Q - 1))
        (by fun_prop) (by fun_prop) (fun x hx => by
          have h1 : x / (-w) ≤ 1 := by rw [div_le_iff_of_neg (by linarith)]; linarith [hx.1]
          linarith)]
      congr 1
      apply intervalIntegral.integral_congr
      intro x _; ring
    have hU_ge : ENNReal.ofReal (r / 16) ≤ volume (Cminus ∩ Metric.closedBall p r) := by
      have hint_eq : ∫ x in (-(L / 2))..(-(L / 4)), (1 + x / w) =
          L / 4 - (3 * L ^ 2) / (32 * w) := by
        have hf : (fun x : ℝ => 1 + x / w) = fun x => (1 / w) * x + 1 := by ext x; ring
        rw [hf, integral_linear]
        have hwne : w ≠ 0 := hw_pos.ne'
        field_simp; ring
      have hint_lb : r / 16 ≤ L / 4 - (3 * L ^ 2) / (32 * w) := by
        have h1 : 3 * L ^ 2 / (32 * w) ≤ 3 * L / 32 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith only [hL_le_w, hL_pos]
        linarith
      calc ENNReal.ofReal (r / 16)
          ≤ ENNReal.ofReal (L / 4 - (3 * L ^ 2) / (32 * w)) := ENNReal.ofReal_le_ofReal hint_lb
        _ = volume U := by rw [hU_vol, hint_eq]
        _ ≤ volume (Cminus ∩ Metric.closedBall p r) := measure_mono hU_sub
    apply ratio_of_mul_bound hN p r (K := 48) (by norm_num) (by norm_num)
    show volume (Cplus ∩ Metric.closedBall p r) ≤ ENNReal.ofReal 48 * volume (Cminus ∩ Metric.closedBall p r)
    calc volume (Cplus ∩ Metric.closedBall p r)
        ≤ ENNReal.ofReal (3 * r) := hCp_vol
      _ = ENNReal.ofReal (48 * (r / 16)) := by congr 1; ring
      _ = ENNReal.ofReal 48 * ENNReal.ofReal (r / 16) := ENNReal.ofReal_mul (by norm_num)
      _ ≤ ENNReal.ofReal 48 * volume (Cminus ∩ Metric.closedBall p r) := by gcongr

/-- Case 5.3: `r > 4` and `0 < s`. -/
lemma normalized_case_large_r_pos {C : Set Plane} (hN : Normalized C)
    {p qPlus Q : Plane} {r s w : ℝ} (hr : 0 < r) (hr4 : 4 < r)
    (hp : p ∈ {q ∈ C | px q ≤ 0})
    (hqPlusC : qPlus ∈ C) (hqPlus_x : 0 ≤ px qPlus) (hqPlusB : qPlus ∈ Metric.closedBall p r)
    (hs_pos : 0 < s) (hs_hi : s ≤ 1) (hwedge : ∀ q ∈ C, s * px q ≤ py q ∧ py q ≤ 1 - s * px q)
    (hQ_mem : Q ∈ {q ∈ C | px q ≤ 0}) (hw_def : w = -px Q)
    (hw_ge : ∀ q ∈ {q ∈ C | px q ≤ 0}, -w ≤ px q) (hw_pos : 0 < w)
    (hQ_y : -w ≤ py Q ∧ py Q ≤ 1 + w) :
    ENNReal.ofReal (1 / 102400 : ℝ) * volume (C ∩ Metric.closedBall p r) ≤
      volume ({q ∈ C | px q ≤ 0} ∩ Metric.closedBall p r) := by
  let Cminus : Set Plane := {q ∈ C | px q ≤ 0}
  let Cplus  : Set Plane := {q ∈ C | 0 ≤ px q}
  have hCminus_conv : Convex ℝ Cminus := by
    intro x hx y hy a b ha hb hab
    refine ⟨hN.convex hx.1 hy.1 ha hb hab, ?_⟩
    simp only [px_add, px_smul]
    nlinarith [hx.2, hy.2]
  have hA : mkP 0 0 ∈ Cminus := ⟨normalized_mem_S hN le_rfl (by norm_num), le_rfl⟩
  have hB : mkP 0 1 ∈ Cminus := ⟨normalized_mem_S hN (by norm_num) le_rfl, le_rfl⟩
  have hM : mkP 0 (1 / 2) ∈ Cminus := ⟨normalized_mem_S hN (by norm_num) (by norm_num), le_rfl⟩
  have hCp_y : ∀ q ∈ Cplus, 0 ≤ py q ∧ py q ≤ 1 := by
    intro q hq
    obtain ⟨h1, h2⟩ := hwedge q hq.1
    have hsq : 0 ≤ s * px q := mul_nonneg hs_pos.le hq.2
    exact ⟨by linarith, by linarith⟩
  have hCp_sub : Cplus ∩ Metric.closedBall p r ⊆
      {q : Plane | 0 ≤ px q ∧ px q ≤ r ∧ 0 ≤ py q ∧ py q ≤ 1} := by
    intro q ⟨hqP, hqB⟩
    have hqx_ub : px q ≤ r := by
      have h1 : px q - px p ≤ dist q p := by
        have h := abs_px_le_norm (q - p)
        rw [← dist_eq_norm, px_sub] at h
        exact le_trans (le_abs_self _) h
      have h2 : dist q p ≤ r := Metric.mem_closedBall.mp hqB
      linarith [hp.2]
    have hqy := hCp_y q hqP
    exact ⟨hqP.2, hqx_ub, hqy.1, hqy.2⟩
  have hCp_vol : volume (Cplus ∩ Metric.closedBall p r) ≤ ENNReal.ofReal r := by
    calc volume (Cplus ∩ Metric.closedBall p r)
        ≤ volume {q : Plane | 0 ≤ px q ∧ px q ≤ r ∧ 0 ≤ py q ∧ py q ≤ 1} := measure_mono hCp_sub
      _ = ENNReal.ofReal ((r - 0) * (1 - 0)) := volume_rect 0 r 0 1 hr.le (by norm_num)
      _ = ENNReal.ofReal r := by congr 1; ring
  have hqPlus_y := hCp_y qPlus ⟨hqPlusC, hqPlus_x⟩
  let qS : Plane := mkP 0 (py qPlus)
  have hqS_dist : dist qS p ≤ r := by
    refine dist_le_of_sq_le hr.le ?_
    have h1 : dist qPlus p ^ 2 ≤ r ^ 2 := by
      have := Metric.mem_closedBall.mp hqPlusB
      nlinarith only [this, dist_nonneg (x := qPlus) (y := p)]
    rw [dist_sq_plane] at h1
    simp only [qS, px_mkP, py_mkP]
    nlinarith only [h1, hqPlus_x, hp.2]
  have hAp_le : dist (mkP 0 0) p ≤ 5 / 4 * r := by
    have h1 : dist (mkP 0 0) qS ≤ 1 := by
      refine dist_le_of_sq_le zero_le_one ?_; simp only [qS, px_mkP, py_mkP]
      nlinarith only [hqPlus_y.1, hqPlus_y.2]
    linarith [dist_triangle (mkP 0 0) qS p]
  have hBp_le : dist (mkP 0 1) p ≤ 5 / 4 * r := by
    have h1 : dist (mkP 0 1) qS ≤ 1 := by
      refine dist_le_of_sq_le zero_le_one ?_; simp only [qS, px_mkP, py_mkP]
      nlinarith only [hqPlus_y.1, hqPlus_y.2]
    linarith [dist_triangle (mkP 0 1) qS p]
  by_cases hx_big : r / 4 ≤ -px p
  · have hpx_neg : px p < 0 := by linarith
    let Tp : Set Plane := {q : Plane | px p ≤ px q ∧ px q ≤ 0 ∧
      (px q / px p) * py p ≤ py q ∧ py q ≤ 1 + (px q / px p) * (py p - 1)}
    have hTp_sub : Tp ⊆ Cminus := fun q hq => by
      have hp_eq : mkP (px p) (py p) ∈ Cminus := by rwa [mkP_px_py]
      exact (triangle_subset_convex hCminus_conv hA hB hp_eq q).2 hpx_neg hq
    have hTp_vol : volume Tp = ENNReal.ofReal (-px p / 2) := volume_triangle_neg hpx_neg
    let Tscaled : Set Plane := (fun q => p + (4 / 5 : ℝ) • (q - p)) '' Tp
    have hTs_sub : Tscaled ⊆ Cminus ∩ Metric.closedBall p r := by
      rintro z ⟨q, hq, rfl⟩
      have hz_comb : p + (4 / 5 : ℝ) • (q - p) = (1 / 5 : ℝ) • p + (4 / 5 : ℝ) • q := by
        rw [smul_sub]; module
      refine ⟨?_, ?_⟩
      · dsimp only
        rw [hz_comb]
        exact hCminus_conv hp (hTp_sub hq) (by norm_num) (by norm_num) (by norm_num)
      · rw [Metric.mem_closedBall, dist_eq_norm]
        have hsub : p + (4 / 5 : ℝ) • (q - p) - p = (4 / 5 : ℝ) • (q - p) := by abel
        rw [hsub, norm_smul, Real.norm_of_nonneg (by norm_num), ← dist_eq_norm]
        have hq_dist : dist q p ≤ 5 / 4 * r := by
          set t := px q / px p
          have ht0 : 0 ≤ t := div_nonneg_of_nonpos hq.2.1 hpx_neg.le
          have ht1 : t ≤ 1 := by rw [div_le_iff_of_neg hpx_neg]; linarith [hq.1]
          set u := py q - t * py p
          set ww := 1 - t - u
          have hu0 : 0 ≤ u := by linarith [hq.2.2.1]
          have hw0 : 0 ≤ ww := by linarith [hq.2.2.2]
          have hq_eq : q = ww • mkP 0 0 + u • mkP 0 1 + t • p := by
            apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul, px_mkP, py_mkP]
            · dsimp [t]; rw [mul_zero, mul_zero, zero_add, zero_add, div_mul_cancel₀ _ hpx_neg.ne]
            · dsimp [u]; ring
          have hdiff : q - p = ww • (mkP 0 0 - p) + u • (mkP 0 1 - p) := by
            rw [hq_eq, smul_sub, smul_sub]
            have h1 : ww + u + t = 1 := by dsimp [ww]; ring
            apply plane_ext <;> simp only [px_add, py_add, px_sub, py_sub, px_smul, py_smul, px_mkP, py_mkP]
            · nlinarith only [h1]
            · nlinarith only [h1]
          rw [dist_eq_norm, hdiff]
          calc ‖ww • (mkP 0 0 - p) + u • (mkP 0 1 - p)‖
              ≤ ‖ww • (mkP 0 0 - p)‖ + ‖u • (mkP 0 1 - p)‖ := norm_add_le _ _
            _ = ww * dist (mkP 0 0) p + u * dist (mkP 0 1) p := by
                rw [norm_smul, norm_smul, Real.norm_of_nonneg hw0, Real.norm_of_nonneg hu0,
                  ← dist_eq_norm, ← dist_eq_norm]
            _ ≤ ww * (5 / 4 * r) + u * (5 / 4 * r) := by nlinarith only [hw0, hu0, hAp_le, hBp_le]
            _ ≤ (ww + u + t) * (5 / 4 * r) := by nlinarith only [ht0, hr]
            _ = 5 / 4 * r := by rw [show ww + u + t = 1 by dsimp [ww]; ring, one_mul]
        linarith
    have hTs_vol : volume Tscaled = ENNReal.ofReal ((4 / 5 : ℝ) ^ 2) * volume Tp := by
      have hrew : Tscaled = (fun x => p + x) '' ((4 / 5 : ℝ) • ((fun x => -p + x) '' Tp)) := by
        ext z; constructor
        · rintro ⟨q, hq, rfl⟩
          exact ⟨(4 / 5 : ℝ) • (-p + q), ⟨-p + q, ⟨q, hq, rfl⟩, rfl⟩, by simp [sub_eq_neg_add]⟩
        · rintro ⟨y, ⟨x, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
          exact ⟨q, hq, by simp [sub_eq_neg_add]⟩
      rw [hrew]
      have hadd1 : ∀ S : Set Plane, volume ((fun x => p + x) '' S) = volume S := fun S => by
        have : (fun x => p + x) '' S = (fun x => -p + x) ⁻¹' S := by
          ext x; simp only [mem_image, mem_preimage]
          constructor
          · rintro ⟨y, hy, rfl⟩; simpa using hy
          · intro hx; exact ⟨-p + x, hx, by simp⟩
        rw [this, measure_preimage_add]
      have hadd2 : ∀ S : Set Plane, volume ((fun x => -p + x) '' S) = volume S := fun S => by
        have : (fun x => -p + x) '' S = (fun x => p + x) ⁻¹' S := by
          ext x; simp
        rw [this, measure_preimage_add]
      rw [hadd1, Measure.addHaar_smul, finrank_plane, abs_of_pos (by norm_num), hadd2]
    have hCm_ge : ENNReal.ofReal (2 / 25 * r) ≤ volume (Cminus ∩ Metric.closedBall p r) := by
      calc ENNReal.ofReal (2 / 25 * r)
          ≤ ENNReal.ofReal ((4 / 5 : ℝ) ^ 2 * (-px p / 2)) := ENNReal.ofReal_le_ofReal (by linarith)
        _ = ENNReal.ofReal ((4 / 5 : ℝ) ^ 2) * ENNReal.ofReal (-px p / 2) :=
            ENNReal.ofReal_mul (by positivity)
        _ = volume Tscaled := by rw [hTs_vol, hTp_vol]
        _ ≤ volume (Cminus ∩ Metric.closedBall p r) := measure_mono hTs_sub
    apply ratio_of_mul_bound hN p r (K := 25 / 2) (by norm_num) (by norm_num)
    show volume (Cplus ∩ Metric.closedBall p r) ≤ ENNReal.ofReal (25 / 2) * volume (Cminus ∩ Metric.closedBall p r)
    calc volume (Cplus ∩ Metric.closedBall p r)
        ≤ ENNReal.ofReal r := hCp_vol
      _ = ENNReal.ofReal (25 / 2 * (2 / 25 * r)) := by congr 1; ring
      _ = ENNReal.ofReal (25 / 2) * ENNReal.ofReal (2 / 25 * r) := ENNReal.ofReal_mul (by norm_num)
      _ ≤ ENNReal.ofReal (25 / 2) * volume (Cminus ∩ Metric.closedBall p r) := by gcongr
  · push Not at hx_big
    have hp_box : -(r / 4) ≤ px p ∧ px p ≤ 0 ∧ -(r / 4) ≤ py p ∧ py p ≤ 1 + r / 4 := by
      obtain ⟨h1, h2⟩ := hwedge p hp.1
      exact ⟨by linarith, hp.2, by nlinarith only [h1, hs_pos, hs_hi, hx_big, hp.2],
        by nlinarith only [h2, hs_pos, hs_hi, hx_big, hp.2]⟩
    have hbox_ball : ∀ q : Plane, -(r / 4) ≤ px q → px q ≤ 0 →
        -(r / 4) ≤ py q → py q ≤ 1 + r / 4 → q ∈ Metric.closedBall p r := by
      intro q hqx1 hqx2 hqy1 hqy2
      refine Metric.mem_closedBall.mpr (dist_le_of_sq_le hr.le ?_)
      have hdx : (px q - px p) ^ 2 ≤ (r / 4) ^ 2 := by
        nlinarith only [hqx1, hqx2, hp_box.1, hp_box.2.1]
      have hdy : (py q - py p) ^ 2 ≤ (3 / 4 * r) ^ 2 := by
        nlinarith only [hqy1, hqy2, hp_box.2.2.1, hp_box.2.2.2, hr4]
      nlinarith only [hdx, hdy, hr]
    by_cases hw_q : w ≤ r / 4
    · have hsub : Cminus ⊆ Metric.closedBall p r := by
        intro q hq
        obtain ⟨h1, h2⟩ := hwedge q hq.1
        have hqx1 : -(r / 4) ≤ px q := by linarith [hw_ge q hq]
        exact hbox_ball q hqx1 hq.2 (by nlinarith only [h1, hs_pos, hs_hi, hqx1, hq.2])
          (by nlinarith only [h2, hs_pos, hs_hi, hqx1, hq.2])
      have heq_m : Cminus ∩ Metric.closedBall p r = Cminus := inter_eq_left.mpr hsub
      have hle_p : volume (Cplus ∩ Metric.closedBall p r) ≤ volume Cminus := by
        have heq := hN.bisect_zero.2
        rw [normalized_side_eq, normalized_opposite_eq] at heq
        calc volume (Cplus ∩ Metric.closedBall p r) ≤ volume Cplus := measure_mono inter_subset_left
          _ = volume Cminus := heq.symm
      apply ratio_of_mul_bound hN p r zero_le_one (by norm_num)
      show volume (Cplus ∩ Metric.closedBall p r) ≤ ENNReal.ofReal 1 * volume (Cminus ∩ Metric.closedBall p r)
      rw [heq_m, ENNReal.ofReal_one, one_mul]
      exact hle_p
    · push Not at hw_q
      let lamr := (r / 4) / w
      have hlamr0 : 0 ≤ lamr := by positivity
      have hlamr1 : lamr ≤ 1 := (div_le_one hw_pos).mpr hw_q.le
      let Qr : Plane := (1 - lamr) • mkP 0 (1 / 2) + lamr • Q
      have hQr_mem : Qr ∈ Cminus := hCminus_conv hM hQ_mem (by linarith) hlamr0 (by ring)
      have hQr_x : px Qr = -(r / 4) := by
        simp only [Qr, px_add, px_smul, px_mkP, lamr]
        have hQx : px Q = -w := by linarith
        rw [hQx, mul_zero, zero_add, mul_neg, div_mul_cancel₀ _ hw_pos.ne']
      have hQr_y : -(r / 4) ≤ py Qr ∧ py Qr ≤ 1 + r / 4 := by
        have hy_eq : py Qr = (1 - lamr) * (1 / 2) + lamr * py Q := by simp [Qr]
        have hlw : lamr * w = r / 4 := div_mul_cancel₀ _ hw_pos.ne'
        rw [hy_eq]
        constructor
        · have := mul_le_mul_of_nonneg_left hQ_y.1 hlamr0; linarith
        · have := mul_le_mul_of_nonneg_left hQ_y.2 hlamr0; linarith
      let Tr : Set Plane := {q : Plane | -(r / 4) ≤ px q ∧ px q ≤ 0 ∧
        (px q / (-(r / 4))) * py Qr ≤ py q ∧ py q ≤ 1 + (px q / (-(r / 4))) * (py Qr - 1)}
      have hQr_eq : mkP (-(r / 4)) (py Qr) ∈ Cminus := by
        have : mkP (-(r / 4)) (py Qr) = Qr := by apply plane_ext <;> simp [hQr_x]
        rwa [this]
      have hTr_sub : Tr ⊆ Cminus ∩ Metric.closedBall p r := by
        intro q hq
        have hqm := (triangle_subset_convex hCminus_conv hA hB hQr_eq q).2 (by linarith) hq
        refine ⟨hqm, hbox_ball q hq.1 hq.2.1 ?_ ?_⟩
        · have hlo : (px q / (-(r / 4))) * py Qr ≤ py q := hq.2.2.1
          set t := px q / (-(r / 4))
          have ht0 : 0 ≤ t := div_nonneg_of_nonpos hq.2.1 (by linarith)
          have ht1 : t ≤ 1 := by rw [div_le_iff_of_neg (by linarith)]; linarith [hq.1]
          nlinarith only [hlo, ht0, ht1, hQr_y.1, hr]
        · have hhi : py q ≤ 1 + (px q / (-(r / 4))) * (py Qr - 1) := hq.2.2.2
          set t := px q / (-(r / 4))
          have ht0 : 0 ≤ t := div_nonneg_of_nonpos hq.2.1 (by linarith)
          have ht1 : t ≤ 1 := by rw [div_le_iff_of_neg (by linarith)]; linarith [hq.1]
          nlinarith only [hhi, ht0, ht1, hQr_y.2, hr]
      have hTr_vol : volume Tr = ENNReal.ofReal (r / 8) := by
        have := volume_triangle_neg (y₀ := py Qr) (show -(r / 4) < 0 by linarith)
        convert this using 2; ring
      have hCm_ge : ENNReal.ofReal (r / 8) ≤ volume (Cminus ∩ Metric.closedBall p r) := by
        rw [← hTr_vol]; exact measure_mono hTr_sub
      apply ratio_of_mul_bound hN p r (K := 8) (by norm_num) (by norm_num)
      show volume (Cplus ∩ Metric.closedBall p r) ≤ ENNReal.ofReal 8 * volume (Cminus ∩ Metric.closedBall p r)
      calc volume (Cplus ∩ Metric.closedBall p r)
          ≤ ENNReal.ofReal r := hCp_vol
        _ = ENNReal.ofReal (8 * (r / 8)) := by congr 1; ring
        _ = ENNReal.ofReal 8 * ENNReal.ofReal (r / 8) := ENNReal.ofReal_mul (by norm_num)
        _ ≤ ENNReal.ofReal 8 * volume (Cminus ∩ Metric.closedBall p r) := by gcongr

lemma normalized_main {C : Set Plane} (hN : Normalized C)
    (p : Plane) (hp : p ∈ OMA.S_mo_201359.side C (mkP 1 0) 0) (r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (1 / 102400 : ℝ) * volume (C ∩ Metric.closedBall p r) ≤
      volume (OMA.S_mo_201359.side C (mkP 1 0) 0 ∩ Metric.closedBall p r) := by
  rw [normalized_side_eq] at hp ⊢
  let Cminus : Set Plane := {q ∈ C | px q ≤ 0}
  let Cplus  : Set Plane := {q ∈ C | 0 ≤ px q}
  have hCminus_compact : IsCompact Cminus :=
    hN.compact.inter_right (isClosed_le continuous_px continuous_const)
  have hA : mkP 0 0 ∈ Cminus := ⟨normalized_mem_S hN le_rfl (by norm_num), le_rfl⟩
  by_cases hhit : (Cplus ∩ Metric.closedBall p r).Nonempty
  swap
  · have heq : C ∩ Metric.closedBall p r = Cminus ∩ Metric.closedBall p r := by
      ext q; constructor
      · rintro ⟨hqC, hqB⟩
        refine ⟨⟨hqC, ?_⟩, hqB⟩
        by_contra h
        push Not at h
        exact hhit ⟨q, ⟨hqC, h.le⟩, hqB⟩
      · rintro ⟨hqm, hqB⟩; exact ⟨hqm.1, hqB⟩
    rw [heq]
    have hle1 : ENNReal.ofReal (1 / 102400 : ℝ) ≤ 1 := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
    calc ENNReal.ofReal (1 / 102400 : ℝ) * volume (Cminus ∩ Metric.closedBall p r)
        ≤ 1 * volume (Cminus ∩ Metric.closedBall p r) := by gcongr
      _ = volume (Cminus ∩ Metric.closedBall p r) := one_mul _
  obtain ⟨qPlus, ⟨hqPlusC, hqPlus_x⟩, hqPlusB⟩ := hhit
  have hp_x_lb : -r ≤ px p := by
    have h1 : px qPlus - px p ≤ dist qPlus p := by
      have h := abs_px_le_norm (qPlus - p)
      rw [← dist_eq_norm, px_sub] at h
      exact le_trans (le_abs_self _) h
    have h2 : dist qPlus p ≤ r := Metric.mem_closedBall.mp hqPlusB
    linarith
  obtain ⟨s, hs_abs, hwedge⟩ := exists_supporting_wedge hN
  have hs_lo : -1 ≤ s := (abs_le.mp hs_abs).1
  have hs_hi : s ≤ 1 := (abs_le.mp hs_abs).2
  obtain ⟨Q, hQ_mem, hQ_min⟩ := hCminus_compact.exists_isMinOn ⟨mkP 0 0, hA⟩ continuous_px.continuousOn
  set w := -px Q with hw_def
  have hw_ge : ∀ q ∈ Cminus, -w ≤ px q := fun q hq => by
    have h1 : px Q ≤ px q := hQ_min hq; dsimp [w]; linarith
  have hw_nn : 0 ≤ w := by linarith [hQ_mem.2]
  have hw_gt : (1 / 5 : ℝ) < w := by
    let Wset : Set Plane := {q : Plane | -w ≤ px q ∧ px q ≤ 0 ∧ px q ≤ py q ∧ py q ≤ 1 - px q}
    have hsub : Cminus ⊆ Wset := by
      intro q hq
      obtain ⟨h1, h2⟩ := hwedge q hq.1
      exact ⟨hw_ge q hq, hq.2, by nlinarith only [h1, hs_lo, hs_hi, hq.2],
        by nlinarith only [h2, hs_lo, hs_hi, hq.2]⟩
    have hW_vol : volume Wset = ENNReal.ofReal (w + w ^ 2) := by
      rw [volume_region_x (-w) 0 (by linarith) (fun x => x) (fun x => 1 - x)
        continuous_id (by fun_prop) (fun x hx => by linarith [hx.2])]
      congr 1
      have hf : (fun x : ℝ => 1 - x - x) = fun x => (-2) * x + 1 := by ext x; ring
      rw [hf, integral_linear]; ring
    have hle_m : volume Cminus ≤ ENNReal.ofReal (w + w ^ 2) := by
      rw [← hW_vol]; exact measure_mono hsub
    have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle_m
    rw [ENNReal.toReal_ofReal (by positivity)] at hle
    have h14 : (1 / 4 : ℝ) ≤ (volume Cminus).toReal := by
      have := normalized_area_ge_half hN
      have := (normalized_vol_side_eq hN).1
      linarith
    nlinarith only [hle, h14, hw_nn]
  have hw_pos : 0 < w := by linarith
  have hQ_y : -w ≤ py Q ∧ py Q ≤ 1 + w := by
    obtain ⟨h1, h2⟩ := hwedge Q hQ_mem.1
    have hQx : px Q = -w := by linarith
    rw [hQx] at h1 h2
    exact ⟨by nlinarith only [h1, hs_lo, hs_hi, hw_pos],
      by nlinarith only [h2, hs_lo, hs_hi, hw_pos]⟩
  by_cases hr4 : r ≤ 4
  · exact normalized_case_small_r hN hr hr4 hp hp_x_lb hs_abs hwedge hQ_mem hw_def hw_gt
  · push Not at hr4
    by_cases hs0 : s ≤ 0
    · exact normalized_case_large_r_nonpos hN hr hr4 hp hp_x_lb hs0 hwedge hQ_mem hw_def hw_ge hw_pos
    · push Not at hs0
      exact normalized_case_large_r_pos hN hr hr4 hp hqPlusC hqPlus_x hqPlusB hs0 hs_hi
        hwedge hQ_mem hw_def hw_ge hw_pos hQ_y

/-! ### Step 1: Reduction from arbitrary `(C, u, t)` to `Normalized` -/

lemma chord_pos_of_bisects_e1 {C : Set Plane} (hC : IsCompact C) (hconv : Convex ℝ C)
    (hint : (interior C).Nonempty) {t₀ : ℝ}
    (hbis : OMA.S_mo_201359.bisects C (mkP 1 0) t₀) :
    ∃ y₁ y₂ : ℝ, y₁ < y₂ ∧
      {p ∈ C | px p = t₀} = {p : Plane | px p = t₀ ∧ y₁ ≤ py p ∧ py p ≤ y₂} ∧
      OMA.S_mo_201359.chordLength C (mkP 1 0) t₀ = y₂ - y₁ := by
  have h10 : mkP 1 0 ≠ 0 := by intro h; have := congrArg px h; simp at this
  have hvol_pos : 0 < (volume C).toReal := by
    have hpos : 0 < volume C :=
      lt_of_lt_of_le (isOpen_interior.measure_pos volume hint) (measure_mono interior_subset)
    exact ENNReal.toReal_pos hpos.ne' hC.measure_lt_top.ne
  have hline0 : volume {p : Plane | px p = t₀} = 0 := by
    convert volume_line_zero (mkP 1 0) h10 t₀ using 2; ext p; simp [inner_plane]
  have hhalf := (bisects_iff_toReal C hC (mkP 1 0) h10 t₀).mp hbis
  have heq_so := hbis.2
  have hside_eq : OMA.S_mo_201359.side C (mkP 1 0) t₀ = {p ∈ C | px p ≤ t₀} := by
    ext p; simp [OMA.S_mo_201359.side, inner_plane]
  have hopp_eq : OMA.S_mo_201359.opposite C (mkP 1 0) t₀ = {p ∈ C | t₀ ≤ px p} := by
    ext p; simp [OMA.S_mo_201359.opposite, inner_plane]
  rw [hside_eq] at hhalf heq_so
  rw [hopp_eq] at heq_so
  have hneg : ∃ q ∈ C, px q < t₀ := by
    by_contra h; push Not at h
    have h0 : volume {p ∈ C | px p ≤ t₀} = 0 :=
      measure_mono_null (fun p hp => le_antisymm hp.2 (h p hp.1)) hline0
    rw [h0] at hhalf; simp at hhalf; linarith
  have hpos : ∃ q ∈ C, t₀ < px q := by
    by_contra h; push Not at h
    have h0 : volume {p ∈ C | t₀ ≤ px p} = 0 :=
      measure_mono_null (fun p hp => le_antisymm (h p hp.1) hp.2) hline0
    rw [← heq_so] at h0; rw [h0] at hhalf; simp at hhalf; linarith
  obtain ⟨qM, hqMC, hqMx⟩ := hneg
  obtain ⟨qP, hqPC, hqPx⟩ := hpos
  obtain ⟨z, hz⟩ := hint
  obtain ⟨ρ, hρ, hball_int⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  have hball : Metric.ball z ρ ⊆ C := hball_int.trans interior_subset
  -- Exhibit two points in S = {p ∈ C | px p = t₀} with distinct y-coordinates
  have htwo : ∃ a b : Plane, a ∈ {p ∈ C | px p = t₀} ∧ b ∈ {p ∈ C | px p = t₀} ∧ py a < py b := by
    have hz1 : z + mkP 0 (ρ / 2) ∈ C := hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      have : ‖mkP 0 (ρ / 2)‖ = ρ / 2 := by
        have hsq : ‖mkP 0 (ρ / 2)‖ ^ 2 = (ρ / 2) ^ 2 := by rw [norm_sq_plane]; simp
        nlinarith [norm_nonneg (mkP 0 (ρ / 2))]
      linarith)
    have hz2 : z - mkP 0 (ρ / 2) ∈ C := hball (by
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      have : ‖mkP 0 (ρ / 2)‖ = ρ / 2 := by
        have hsq : ‖mkP 0 (ρ / 2)‖ ^ 2 = (ρ / 2) ^ 2 := by rw [norm_sq_plane]; simp
        nlinarith [norm_nonneg (mkP 0 (ρ / 2))]
      linarith)
    rcases lt_trichotomy (px z) t₀ with hlt | heq | hgt
    · let lam := (t₀ - px z) / (px qP - px z)
      have hd : 0 < px qP - px z := by linarith
      have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hd.le
      have hlam1 : lam < 1 := (div_lt_one hd).mpr (by linarith)
      let a := (1 - lam) • (z - mkP 0 (ρ / 2)) + lam • qP
      let b := (1 - lam) • (z + mkP 0 (ρ / 2)) + lam • qP
      refine ⟨a, b, ⟨hconv hz2 hqPC (by linarith) hlam0 (by ring), ?_⟩,
        ⟨hconv hz1 hqPC (by linarith) hlam0 (by ring), ?_⟩, ?_⟩
      · simp only [a, px_add, px_smul, px_sub, px_mkP, sub_zero, lam]
        field_simp [hd.ne']; ring
      · simp only [b, px_add, px_smul, px_mkP, add_zero, lam]
        field_simp [hd.ne']; ring
      · simp only [a, b, py_add, py_smul, py_sub, py_mkP]
        nlinarith
    · refine ⟨z - mkP 0 (ρ / 2), z + mkP 0 (ρ / 2), ⟨hz2, by simp [heq]⟩, ⟨hz1, by simp [heq]⟩, ?_⟩
      simp; linarith
    · let lam := (px z - t₀) / (px z - px qM)
      have hd : 0 < px z - px qM := by linarith
      have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hd.le
      have hlam1 : lam < 1 := (div_lt_one hd).mpr (by linarith)
      let a := (1 - lam) • (z - mkP 0 (ρ / 2)) + lam • qM
      let b := (1 - lam) • (z + mkP 0 (ρ / 2)) + lam • qM
      refine ⟨a, b, ⟨hconv hz2 hqMC (by linarith) hlam0 (by ring), ?_⟩,
        ⟨hconv hz1 hqMC (by linarith) hlam0 (by ring), ?_⟩, ?_⟩
      · simp only [a, px_add, px_smul, px_sub, px_mkP, sub_zero, lam]
        field_simp [hd.ne']; ring
      · simp only [b, px_add, px_smul, px_mkP, add_zero, lam]
        field_simp [hd.ne']; ring
      · simp only [a, b, py_add, py_smul, py_sub, py_mkP]
        nlinarith
  obtain ⟨a, b, ha, hb, hab⟩ := htwo
  let S : Set Plane := {p ∈ C | px p = t₀}
  have hS_comp : IsCompact S := hC.inter_right (isClosed_eq continuous_px continuous_const)
  obtain ⟨pmin, hpmin, hmin⟩ := hS_comp.exists_isMinOn ⟨a, ha⟩ continuous_py.continuousOn
  obtain ⟨pmax, hpmax, hmax⟩ := hS_comp.exists_isMaxOn ⟨a, ha⟩ continuous_py.continuousOn
  have hlt : py pmin < py pmax := lt_of_le_of_lt (hmin ha) (lt_of_lt_of_le hab (hmax hb))
  refine ⟨py pmin, py pmax, hlt, ?_, ?_⟩
  · ext p; constructor
    · intro hp; exact ⟨hp.2, hmin hp, hmax hp⟩
    · rintro ⟨hpx, hy1, hy2⟩
      have hd : 0 < py pmax - py pmin := by linarith
      let t := (py p - py pmin) / (py pmax - py pmin)
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
      have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
      have hp_eq : p = (1 - t) • pmin + t • pmax := by
        apply plane_ext <;> simp only [px_add, py_add, px_smul, py_smul]
        · rw [hpmin.2, hpmax.2, hpx]; ring
        · dsimp [t]; field_simp [hd.ne']; ring
      exact ⟨by rw [hp_eq]; exact hconv hpmin.1 hpmax.1 (by linarith) ht0 (by ring), hpx⟩
  · have hch_eq : {p ∈ C | inner ℝ (mkP 1 0) p = t₀} = S := by
      ext p; simp [S, inner_plane]
    rw [OMA.S_mo_201359.chordLength, hch_eq]
    apply le_antisymm
    · refine Metric.diam_le_of_forall_dist_le (by linarith) fun x hx y hy => ?_
      refine dist_le_of_sq_le (by linarith) ?_
      rw [hx.2, hy.2, sub_self, zero_pow two_ne_zero, zero_add]
      have h1 : py pmin ≤ py x := hmin hx
      have h2 : py x ≤ py pmax := hmax hx
      have h3 : py pmin ≤ py y := hmin hy
      have h4 : py y ≤ py pmax := hmax hy
      nlinarith only [h1, h2, h3, h4]
    · have hdist : dist pmin pmax = py pmax - py pmin := by
        have hsq : dist pmin pmax ^ 2 = (py pmax - py pmin) ^ 2 := by
          rw [dist_sq_plane, hpmin.2, hpmax.2]; ring
        nlinarith [dist_nonneg (x := pmin) (y := pmax)]
      rw [← hdist]
      exact Metric.dist_le_diam_of_mem hS_comp.isBounded hpmin hpmax

lemma main_proof :
    ∃ α : ℝ, 0 < α ∧
      ∀ (C : Set Plane), IsCompact C → Convex ℝ C → (interior C).Nonempty →
      ∀ (u : Plane) (t : ℝ), OMA.S_mo_201359.bisects C u t →
      (∀ (v : Plane) (s : ℝ), OMA.S_mo_201359.bisects C v s →
        OMA.S_mo_201359.chordLength C u t ≤ OMA.S_mo_201359.chordLength C v s) →
      ∀ (p : Plane), p ∈ OMA.S_mo_201359.side C u t → ∀ (r : ℝ), 0 < r →
        ENNReal.ofReal α * volume (C ∩ Metric.closedBall p r) ≤
          volume (OMA.S_mo_201359.side C u t ∩ Metric.closedBall p r) := by
  refine ⟨1 / 102400, by norm_num, ?_⟩
  intro C hC hconv hint u t hbis hmin p hp r hr
  -- Step A: Rotate by Φ = rotEquiv u hbis.1
  let Φ := rotEquiv u hbis.1
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hbis.1
  have hΦ_vol : ∀ S : Set Plane, MeasurableSet S → volume (Φ '' S) = volume S := fun S hS => by
    have hpre : Φ '' S = Φ.symm ⁻¹' S := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; simpa using hy
      · intro hx; exact ⟨Φ.symm x, hx, by simp⟩
    rw [hpre]
    exact Φ.symm.measurePreserving.measure_preimage hS.nullMeasurableSet
  have hΦ_inner : ∀ v x : Plane, inner ℝ v (Φ x) = inner ℝ (Φ.symm v) x := fun v x => by
    rw [← Φ.inner_map_map (Φ.symm v) x, Φ.apply_symm_apply]
  let C₁ : Set Plane := Φ '' C
  have hC₁_comp : IsCompact C₁ := hC.image Φ.continuous
  have hC₁_conv : Convex ℝ C₁ := hconv.linear_image Φ.toLinearMap
  have hC₁_int : (interior C₁).Nonempty := by
    obtain ⟨z, hz⟩ := hint
    exact ⟨Φ z, interior_maximal (image_mono interior_subset)
      (Φ.toHomeomorph.isOpenMap _ isOpen_interior) ⟨z, hz, rfl⟩⟩
  have hbis_Φ : ∀ v s, OMA.S_mo_201359.bisects C₁ v s ↔ OMA.S_mo_201359.bisects C (Φ.symm v) s := by
    intro v s
    have hs : OMA.S_mo_201359.side C₁ v s = Φ '' OMA.S_mo_201359.side C (Φ.symm v) s := by
      ext x; constructor
      · rintro ⟨⟨y, hy, rfl⟩, hle⟩; exact ⟨y, ⟨hy, by rwa [← hΦ_inner]⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hle⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, by rwa [hΦ_inner]⟩
    have ho : OMA.S_mo_201359.opposite C₁ v s = Φ '' OMA.S_mo_201359.opposite C (Φ.symm v) s := by
      ext x; constructor
      · rintro ⟨⟨y, hy, rfl⟩, hle⟩; exact ⟨y, ⟨hy, by rwa [← hΦ_inner]⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hle⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, by rwa [hΦ_inner]⟩
    simp only [OMA.S_mo_201359.bisects, hs, ho,
      hΦ_vol _ (measurableSet_side hC.measurableSet _ _),
      hΦ_vol _ (measurableSet_opposite hC.measurableSet _ _)]
    constructor <;> rintro ⟨hv, heq⟩
    · exact ⟨fun h => hv (Φ.symm.injective (by simpa using h)), heq⟩
    · exact ⟨fun h => hv (by simp [h]), heq⟩
  have hch_Φ : ∀ v s, OMA.S_mo_201359.chordLength C₁ v s =
      OMA.S_mo_201359.chordLength C (Φ.symm v) s := by
    intro v s
    have heq : {q ∈ C₁ | inner ℝ v q = s} = Φ '' {q ∈ C | inner ℝ (Φ.symm v) q = s} := by
      ext x; constructor
      · rintro ⟨⟨y, hy, rfl⟩, h⟩; exact ⟨y, ⟨hy, by rwa [← hΦ_inner]⟩, rfl⟩
      · rintro ⟨y, ⟨hy, h⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, by rwa [hΦ_inner]⟩
    rw [OMA.S_mo_201359.chordLength, heq, Φ.isometry.diam_image, OMA.S_mo_201359.chordLength]
  have hΦ_symm_e1 : Φ.symm (mkP 1 0) = ‖u‖⁻¹ • u := by
    apply Φ.injective
    rw [Φ.apply_symm_apply, map_smul]
    apply plane_ext
    · rw [px_mkP, px_smul, rotEquiv_px, real_inner_self_eq_norm_sq]
      field_simp [hu_pos.ne']
    · rw [py_mkP, py_smul]
      change 0 = ‖u‖⁻¹ * (-(py u / ‖u‖) * px u + px u / ‖u‖ * py u)
      ring
  set t₀ := t / ‖u‖
  have hside_e1 : ∀ q : Plane, inner ℝ (mkP 1 0) (Φ q) ≤ t₀ ↔ inner ℝ u q ≤ t := fun q => by
    rw [hΦ_inner, hΦ_symm_e1, real_inner_smul_left]
    constructor <;> intro h
    · have := mul_le_mul_of_nonneg_left h hu_pos.le
      rw [← mul_assoc, mul_inv_cancel₀ hu_pos.ne', one_mul] at this
      have h2 : ‖u‖ * t₀ = t := mul_div_cancel₀ _ hu_pos.ne'
      linarith
    · have := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hu_pos.le)
      have h2 : ‖u‖⁻¹ * t = t₀ := by dsimp [t₀]; ring
      linarith
  have hopp_e1 : ∀ q : Plane, t₀ ≤ inner ℝ (mkP 1 0) (Φ q) ↔ t ≤ inner ℝ u q := fun q => by
    rw [hΦ_inner, hΦ_symm_e1, real_inner_smul_left]
    constructor <;> intro h
    · have := mul_le_mul_of_nonneg_left h hu_pos.le
      rw [← mul_assoc, mul_inv_cancel₀ hu_pos.ne', one_mul] at this
      have h2 : ‖u‖ * t₀ = t := mul_div_cancel₀ _ hu_pos.ne'
      linarith
    · have := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hu_pos.le)
      have h2 : ‖u‖⁻¹ * t = t₀ := by dsimp [t₀]; ring
      linarith
  have hbis₁ : OMA.S_mo_201359.bisects C₁ (mkP 1 0) t₀ := by
    have h10 : mkP 1 0 ≠ 0 := by intro h; have := congrArg px h; simp at this
    refine ⟨h10, ?_⟩
    have hs : OMA.S_mo_201359.side C₁ (mkP 1 0) t₀ = Φ '' OMA.S_mo_201359.side C u t := by
      ext x; constructor
      · rintro ⟨⟨y, hy, rfl⟩, hle⟩; exact ⟨y, ⟨hy, (hside_e1 y).mp hle⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hle⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, (hside_e1 y).mpr hle⟩
    have ho : OMA.S_mo_201359.opposite C₁ (mkP 1 0) t₀ = Φ '' OMA.S_mo_201359.opposite C u t := by
      ext x; constructor
      · rintro ⟨⟨y, hy, rfl⟩, hle⟩; exact ⟨y, ⟨hy, (hopp_e1 y).mp hle⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hle⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, (hopp_e1 y).mpr hle⟩
    rw [hs, ho, hΦ_vol _ (measurableSet_side hC.measurableSet u t),
      hΦ_vol _ (measurableSet_opposite hC.measurableSet u t), hbis.2]
  have hch_e1 : OMA.S_mo_201359.chordLength C₁ (mkP 1 0) t₀ = OMA.S_mo_201359.chordLength C u t := by
    have heq : {q ∈ C₁ | inner ℝ (mkP 1 0) q = t₀} = Φ '' {q ∈ C | inner ℝ u q = t} := by
      ext x; constructor
      · rintro ⟨⟨y, hy, rfl⟩, h⟩
        exact ⟨y, ⟨hy, le_antisymm ((hside_e1 y).mp h.le) ((hopp_e1 y).mp h.ge)⟩, rfl⟩
      · rintro ⟨y, ⟨hy, h⟩, rfl⟩
        exact ⟨⟨y, hy, rfl⟩, le_antisymm ((hside_e1 y).mpr h.le) ((hopp_e1 y).mpr h.ge)⟩
    rw [OMA.S_mo_201359.chordLength, heq, Φ.isometry.diam_image, OMA.S_mo_201359.chordLength]
  have hmin₁ : ∀ v s, OMA.S_mo_201359.bisects C₁ v s →
      OMA.S_mo_201359.chordLength C₁ (mkP 1 0) t₀ ≤ OMA.S_mo_201359.chordLength C₁ v s := by
    intro v s hbv
    rw [hch_e1, hch_Φ]
    exact hmin (Φ.symm v) s ((hbis_Φ v s).mp hbv)
  -- Step B: Translate by (-t₀, -y₁) and scale by ℓ⁻¹ where ℓ = y₂ - y₁ > 0
  obtain ⟨y₁, y₂, hy₁₂, hS₁_eq, hch₁_eq⟩ := chord_pos_of_bisects_e1 hC₁_comp hC₁_conv hC₁_int hbis₁
  set ℓ := y₂ - y₁
  have hℓ : 0 < ℓ := by linarith
  let v₀ : Plane := mkP t₀ y₁
  let T : Plane → Plane := fun q => ℓ⁻¹ • (q - v₀)
  let Tinv : Plane → Plane := fun w => ℓ • w + v₀
  have hT_left : ∀ q, Tinv (T q) = q := fun q => by
    simp [T, Tinv, smul_inv_smul₀ hℓ.ne']
  have hT_right : ∀ w, T (Tinv w) = w := fun w => by
    simp [T, Tinv, inv_smul_smul₀ hℓ.ne']
  have hT_vol : ∀ S : Set Plane, volume (T '' S) = ENNReal.ofReal (ℓ⁻¹ ^ 2) * volume S := fun S => by
    have hrew : T '' S = (ℓ⁻¹ : ℝ) • ((fun x => -v₀ + x) '' S) := by
      ext z; constructor
      · rintro ⟨q, hq, rfl⟩; exact ⟨-v₀ + q, ⟨q, hq, rfl⟩, by simp [T, sub_eq_neg_add]⟩
      · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩; exact ⟨q, hq, by simp [T, sub_eq_neg_add]⟩
    rw [hrew, Measure.addHaar_smul, finrank_plane, abs_of_pos (by positivity)]
    have hadd : volume ((fun x => -v₀ + x) '' S) = volume S := by
      have : (fun x => -v₀ + x) '' S = (fun x => v₀ + x) ⁻¹' S := by
        ext x; simp
      rw [this, measure_preimage_add]
    rw [hadd]
  have hT_dist : ∀ x y : Plane, dist (T x) (T y) = ℓ⁻¹ * dist x y := fun x y => by
    rw [dist_eq_norm, dist_eq_norm]
    have : T x - T y = ℓ⁻¹ • (x - y) := by simp [T, smul_sub]
    rw [this, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
  have hT_diam : ∀ S : Set Plane, Metric.diam (T '' S) = ℓ⁻¹ * Metric.diam S := fun S => by
    by_cases hS : S.Nonempty
    · by_cases hb : Bornology.IsBounded S
      · apply le_antisymm
        · refine Metric.diam_le_of_forall_dist_le (mul_nonneg (inv_nonneg.mpr hℓ.le) Metric.diam_nonneg) ?_
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          rw [hT_dist]
          exact mul_le_mul_of_nonneg_left (Metric.dist_le_diam_of_mem hb hx hy) (inv_nonneg.mpr hℓ.le)
        · have hbT : Bornology.IsBounded (T '' S) := by
            obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : Plane)
            refine Metric.isBounded_iff_subset_closedBall (T 0) |>.mpr ⟨ℓ⁻¹ * max R 0, ?_⟩
            rintro _ ⟨x, hx, rfl⟩
            rw [Metric.mem_closedBall, hT_dist]
            have := Metric.mem_closedBall.mp (hR hx)
            exact mul_le_mul_of_nonneg_left (le_trans this (le_max_left R 0)) (inv_nonneg.mpr hℓ.le)
          rw [← le_div_iff₀' (inv_pos.mpr hℓ), div_inv_eq_mul]
          refine Metric.diam_le_of_forall_dist_le (mul_nonneg Metric.diam_nonneg hℓ.le) fun x hx y hy => ?_
          have h1 : dist (T x) (T y) ≤ Metric.diam (T '' S) :=
            Metric.dist_le_diam_of_mem hbT ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
          rw [hT_dist] at h1
          have := mul_le_mul_of_nonneg_right h1 hℓ.le
          rw [mul_comm (ℓ⁻¹), mul_assoc, inv_mul_cancel₀ hℓ.ne', mul_one] at this
          exact this
      · -- only used on bounded C₁ slices; handle cleanly anyway via diam = 0 if unbounded
        have hbu : ¬ Bornology.IsBounded (T '' S) := by
          intro hbt
          apply hb
          obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (T 0) |>.mp hbt
          refine Metric.isBounded_iff_subset_closedBall 0 |>.mpr ⟨ℓ * max R 0, fun x hx => ?_⟩
          have h1 := Metric.mem_closedBall.mp (hR ⟨x, hx, rfl⟩)
          rw [hT_dist] at h1
          rw [Metric.mem_closedBall]
          have := mul_le_mul_of_nonneg_left h1 hℓ.le
          rw [← mul_assoc, mul_inv_cancel₀ hℓ.ne', one_mul] at this
          exact le_trans this (mul_le_mul_of_nonneg_left (le_max_left R 0) hℓ.le)
        rw [Metric.diam_eq_zero_of_unbounded hb, Metric.diam_eq_zero_of_unbounded hbu, mul_zero]
    · rw [Set.not_nonempty_iff_eq_empty.mp hS]; simp
  let C₂ : Set Plane := T '' C₁
  have hT_cont : Continuous T := by dsimp only [T]; fun_prop
  have hTinv_cont : Continuous Tinv := by dsimp only [Tinv]; fun_prop
  let hT_homeo : Plane ≃ₜ Plane := ⟨⟨T, Tinv, hT_left, hT_right⟩, hT_cont, hTinv_cont⟩
  have hbis_T : ∀ v s, OMA.S_mo_201359.bisects C₂ v s ↔
      OMA.S_mo_201359.bisects C₁ v (ℓ * s + inner ℝ v v₀) := by
    intro v s
    have hcond : ∀ q : Plane, inner ℝ v (T q) ≤ s ↔ inner ℝ v q ≤ ℓ * s + inner ℝ v v₀ := fun q => by
      simp only [T, inner_smul_right, inner_sub_right]
      constructor <;> intro h
      · have := mul_le_mul_of_nonneg_left h hℓ.le
        rw [← mul_assoc, mul_inv_cancel₀ hℓ.ne', one_mul] at this; linarith
      · have := mul_le_mul_of_nonneg_left (show inner ℝ v q - inner ℝ v v₀ ≤ ℓ * s by linarith)
          (inv_nonneg.mpr hℓ.le)
        rwa [← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul] at this
    have hcond2 : ∀ q : Plane, s ≤ inner ℝ v (T q) ↔ ℓ * s + inner ℝ v v₀ ≤ inner ℝ v q := fun q => by
      simp only [T, inner_smul_right, inner_sub_right]
      constructor <;> intro h
      · have := mul_le_mul_of_nonneg_left h hℓ.le
        rw [← mul_assoc, mul_inv_cancel₀ hℓ.ne', one_mul] at this; linarith
      · have := mul_le_mul_of_nonneg_left (show ℓ * s ≤ inner ℝ v q - inner ℝ v v₀ by linarith)
          (inv_nonneg.mpr hℓ.le)
        rwa [← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul] at this
    have hs : OMA.S_mo_201359.side C₂ v s = T '' OMA.S_mo_201359.side C₁ v (ℓ * s + inner ℝ v v₀) := by
      ext z; constructor
      · rintro ⟨⟨q, hq, rfl⟩, hle⟩; exact ⟨q, ⟨hq, (hcond q).mp hle⟩, rfl⟩
      · rintro ⟨q, ⟨hq, hle⟩, rfl⟩; exact ⟨⟨q, hq, rfl⟩, (hcond q).mpr hle⟩
    have ho : OMA.S_mo_201359.opposite C₂ v s =
        T '' OMA.S_mo_201359.opposite C₁ v (ℓ * s + inner ℝ v v₀) := by
      ext z; constructor
      · rintro ⟨⟨q, hq, rfl⟩, hle⟩; exact ⟨q, ⟨hq, (hcond2 q).mp hle⟩, rfl⟩
      · rintro ⟨q, ⟨hq, hle⟩, rfl⟩; exact ⟨⟨q, hq, rfl⟩, (hcond2 q).mpr hle⟩
    simp only [OMA.S_mo_201359.bisects, hs, ho, hT_vol]
    have hc_ne0 : ENNReal.ofReal (ℓ⁻¹ ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero]; push Not; positivity
    have hc_top : ENNReal.ofReal (ℓ⁻¹ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    constructor <;> rintro ⟨hv, heq⟩
    · exact ⟨hv, (ENNReal.mul_right_inj hc_ne0 hc_top).mp heq⟩
    · exact ⟨hv, by rw [heq]⟩
  have hN₂ : Normalized C₂ :=
    { compact := hC₁_comp.image hT_cont
      convex := by
        intro x hx y hy a b ha hb hab
        rcases hx with ⟨x', hx', rfl⟩
        rcases hy with ⟨y', hy', rfl⟩
        refine ⟨a • x' + b • y', hC₁_conv hx' hy' ha hb hab, ?_⟩
        simp only [T]
        apply plane_ext <;> simp only [px_add, py_add, px_sub, py_sub, px_smul, py_smul]
        · have h1 : a * px x' + b * px y' - px v₀ = a * (px x' - px v₀) + b * (px y' - px v₀) := by
            have := congrArg (· * px v₀) hab; linarith
          rw [h1]; ring
        · have h1 : a * py x' + b * py y' - py v₀ = a * (py x' - py v₀) + b * (py y' - py v₀) := by
            have := congrArg (· * py v₀) hab; linarith
          rw [h1]; ring
      int_ne := by
        obtain ⟨z, hz⟩ := hC₁_int
        have hopen : IsOpen (T '' interior C₁) := by
          change IsOpen (hT_homeo '' interior C₁)
          exact hT_homeo.isOpenMap (interior C₁) isOpen_interior
        exact ⟨T z, interior_maximal (image_mono interior_subset) hopen ⟨z, hz, rfl⟩⟩
      bisect_zero := by
        rw [hbis_T]
        have : ℓ * 0 + inner ℝ (mkP 1 0) v₀ = t₀ := by simp [v₀, inner_plane]
        rwa [this]
      chord_eq := by
        ext z; constructor
        · rintro ⟨⟨q, hq, rfl⟩, hpx⟩
          have hqx : px q = t₀ := by
            simp only [T, px_smul, px_sub, v₀, px_mkP] at hpx
            have := (mul_eq_zero.mp hpx).resolve_left (inv_ne_zero hℓ.ne')
            linarith
          have hqS : q ∈ {q ∈ C₁ | px q = t₀} := ⟨hq, hqx⟩
          rw [hS₁_eq] at hqS
          refine ⟨hpx, ?_, ?_⟩
          · simp only [T, py_smul, py_sub, v₀, py_mkP]
            exact mul_nonneg (inv_nonneg.mpr hℓ.le) (by linarith [hqS.2.1])
          · simp only [T, py_smul, py_sub, v₀, py_mkP]
            rw [inv_mul_le_iff₀ hℓ, mul_one]; dsimp [ℓ]; linarith [hqS.2.2]
        · rintro ⟨hpx, hy0, hy1⟩
          refine ⟨⟨Tinv z, ?_, hT_right z⟩, hpx⟩
          have hqS : Tinv z ∈ {q : Plane | px q = t₀ ∧ y₁ ≤ py q ∧ py q ≤ y₂} := by
            refine ⟨by simp [Tinv, v₀, hpx], ?_, ?_⟩
            · simp only [Tinv, v₀, py_add, py_smul, py_mkP]; nlinarith
            · simp only [Tinv, v₀, py_add, py_smul, py_mkP]; dsimp [ℓ]; nlinarith
          rw [← hS₁_eq] at hqS
          exact hqS.1
      minimal := fun v s hbv => by
        rw [hbis_T] at hbv
        have hch : {z ∈ C₂ | inner ℝ v z = s} =
            T '' {q ∈ C₁ | inner ℝ v q = ℓ * s + inner ℝ v v₀} := by
          ext z; constructor
          · rintro ⟨⟨q, hq, rfl⟩, h⟩
            refine ⟨q, ⟨hq, ?_⟩, rfl⟩
            simp only [T, inner_smul_right, inner_sub_right] at h
            have := congrArg (ℓ * ·) h
            rw [← mul_assoc, mul_inv_cancel₀ hℓ.ne', one_mul] at this
            linarith
          · rintro ⟨q, ⟨hq, h⟩, rfl⟩
            refine ⟨⟨q, hq, rfl⟩, ?_⟩
            simp only [T, inner_smul_right, inner_sub_right]
            rw [show inner ℝ v q - inner ℝ v v₀ = ℓ * s by linarith,
              ← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul]
        rw [OMA.S_mo_201359.chordLength, hch, hT_diam]
        have hm := hmin₁ v (ℓ * s + inner ℝ v v₀) hbv
        rw [hch₁_eq] at hm
        have := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hℓ.le)
        rwa [inv_mul_cancel₀ hℓ.ne'] at this }
  -- Apply normalized_main to C₂, p₂ = T (Φ p), r₂ = ℓ⁻¹ * r
  let p₂ := T (Φ p)
  have hp₂ : p₂ ∈ OMA.S_mo_201359.side C₂ (mkP 1 0) 0 := by
    refine ⟨⟨Φ p, ⟨p, hp.1, rfl⟩, rfl⟩, ?_⟩
    simp only [p₂, T, inner_smul_right, inner_sub_right]
    have h1 : inner ℝ (mkP 1 0) (Φ p) ≤ t₀ := (hside_e1 p).mpr hp.2
    have h2 : inner ℝ (mkP 1 0) v₀ = t₀ := by simp [v₀, inner_plane]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hℓ.le) (by linarith)
  have hres := normalized_main hN₂ p₂ hp₂ (ℓ⁻¹ * r) (by positivity)
  -- Pull back both sets from C₂ to C
  have hball_T : ∀ S : Set Plane,
      T '' (S ∩ Metric.closedBall (Φ p) r) = (T '' S) ∩ Metric.closedBall p₂ (ℓ⁻¹ * r) := by
    intro S; ext z; constructor
    · rintro ⟨q, ⟨hqS, hqB⟩, rfl⟩
      refine ⟨⟨q, hqS, rfl⟩, ?_⟩
      rw [Metric.mem_closedBall, hT_dist]
      exact mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hqB) (inv_nonneg.mpr hℓ.le)
    · rintro ⟨⟨q, hqS, rfl⟩, hqB⟩
      refine ⟨q, ⟨hqS, ?_⟩, rfl⟩
      rw [Metric.mem_closedBall] at hqB ⊢
      rw [hT_dist] at hqB
      exact le_of_mul_le_mul_left hqB (inv_pos.mpr hℓ)
  have hball_Φ : ∀ S : Set Plane,
      Φ '' (S ∩ Metric.closedBall p r) = (Φ '' S) ∩ Metric.closedBall (Φ p) r := by
    intro S; ext z; constructor
    · rintro ⟨q, ⟨hqS, hqB⟩, rfl⟩
      exact ⟨⟨q, hqS, rfl⟩, by simpa [Metric.mem_closedBall, Φ.isometry.dist_eq] using hqB⟩
    · rintro ⟨⟨q, hqS, rfl⟩, hqB⟩
      exact ⟨q, ⟨hqS, by simpa [Metric.mem_closedBall, Φ.isometry.dist_eq] using hqB⟩, rfl⟩
  have hside_pull : OMA.S_mo_201359.side C₂ (mkP 1 0) 0 =
      T '' (Φ '' OMA.S_mo_201359.side C u t) := by
    ext z; constructor
    · rintro ⟨⟨_, ⟨q, hqC, rfl⟩, rfl⟩, hle⟩
      refine ⟨Φ q, ⟨q, ⟨hqC, ?_⟩, rfl⟩, rfl⟩
      simp only [T, inner_smul_right, inner_sub_right] at hle
      have hv0 : inner ℝ (mkP 1 0) v₀ = t₀ := by simp [v₀, inner_plane]
      have h1 : inner ℝ (mkP 1 0) (Φ q) ≤ t₀ := by
        have := mul_nonpos_iff.mp hle
        rcases this with ⟨_, h2⟩ | ⟨h2, _⟩
        · linarith
        · linarith [inv_pos.mpr hℓ]
      exact (hside_e1 q).mp h1
    · rintro ⟨_, ⟨q, ⟨hqC, hqle⟩, rfl⟩, rfl⟩
      refine ⟨⟨Φ q, ⟨q, hqC, rfl⟩, rfl⟩, ?_⟩
      simp only [T, inner_smul_right, inner_sub_right]
      have hv0 : inner ℝ (mkP 1 0) v₀ = t₀ := by simp [v₀, inner_plane]
      have h1 : inner ℝ (mkP 1 0) (Φ q) ≤ t₀ := (hside_e1 q).mpr hqle
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hℓ.le) (by linarith)
  have hvol1 : volume (C₂ ∩ Metric.closedBall p₂ (ℓ⁻¹ * r)) =
      ENNReal.ofReal (ℓ⁻¹ ^ 2) * volume (C ∩ Metric.closedBall p r) := by
    dsimp [C₂, C₁]
    rw [← hball_T, hT_vol, ← hball_Φ,
      hΦ_vol _ (hC.measurableSet.inter Metric.isClosed_closedBall.measurableSet)]
  have hvol2 : volume (OMA.S_mo_201359.side C₂ (mkP 1 0) 0 ∩ Metric.closedBall p₂ (ℓ⁻¹ * r)) =
      ENNReal.ofReal (ℓ⁻¹ ^ 2) * volume (OMA.S_mo_201359.side C u t ∩ Metric.closedBall p r) := by
    rw [hside_pull, ← hball_T, hT_vol, ← hball_Φ,
      hΦ_vol _ ((measurableSet_side hC.measurableSet u t).inter Metric.isClosed_closedBall.measurableSet)]
  rw [hvol1, hvol2] at hres
  have hres' : ENNReal.ofReal (ℓ⁻¹ ^ 2) *
      (ENNReal.ofReal (1 / 102400 : ℝ) * volume (C ∩ Metric.closedBall p r)) ≤
      ENNReal.ofReal (ℓ⁻¹ ^ 2) * volume (OMA.S_mo_201359.side C u t ∩ Metric.closedBall p r) := by
    calc ENNReal.ofReal (ℓ⁻¹ ^ 2) *
          (ENNReal.ofReal (1 / 102400 : ℝ) * volume (C ∩ Metric.closedBall p r))
        = ENNReal.ofReal (1 / 102400 : ℝ) *
          (ENNReal.ofReal (ℓ⁻¹ ^ 2) * volume (C ∩ Metric.closedBall p r)) := by ring
      _ ≤ _ := hres
  have hc_ne0 : ENNReal.ofReal (ℓ⁻¹ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]; push Not; positivity
  have hinv : (ENNReal.ofReal (ℓ⁻¹ ^ 2))⁻¹ *
      (ENNReal.ofReal (ℓ⁻¹ ^ 2) * (ENNReal.ofReal (1 / 102400 : ℝ) * volume (C ∩ Metric.closedBall p r))) ≤
      (ENNReal.ofReal (ℓ⁻¹ ^ 2))⁻¹ *
      (ENNReal.ofReal (ℓ⁻¹ ^ 2) * volume (OMA.S_mo_201359.side C u t ∩ Metric.closedBall p r)) := by
    gcongr
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc_ne0 ENNReal.ofReal_ne_top, one_mul] at hinv
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc_ne0 ENNReal.ofReal_ne_top, one_mul] at hinv
  exact hinv

end MO201359Proof

theorem OMA.solution : type_of% @OMA.S_mo_201359.main := MO201359Proof.main_proof
