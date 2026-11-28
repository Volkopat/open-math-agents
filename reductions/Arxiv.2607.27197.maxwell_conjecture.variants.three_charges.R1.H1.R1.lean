import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_charges_R1

/-!
# Barycentric polynomial equations for three-charge equilibria

In barycentric coordinates the squared distances to the three vertices are translates of one
positive-definite quadratic form. Squaring the equilibrium identities keeps the equations
polynomial. The common sign condition retains the signed charge information.
-/

namespace OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_charges_R1_H1_R1

open Arxiv.«2607.27197» InnerProductSpace Filter Topology
open scoped BigOperators Gradient RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_sq_gram (b c : E) (s t : ℝ) :
    ‖s • b + t • c‖ ^ 2 =
      ‖b‖ ^ 2 * s ^ 2 + 2 * ⟪b, c⟫_ℝ * s * t + ‖c‖ ^ 2 * t ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq, real_inner_comm c b]
  ring

private theorem coefficients_eq_zero (a : Fin 3 → E) (ha : AffineIndependent ℝ a)
    {s t : ℝ} (h : s • (a 1 - a 0) + t • (a 2 - a 0) = 0) : s = 0 ∧ t = 0 := by
  let index : Fin 2 → {i : Fin 3 // i ≠ 0} := fun i => ⟨i.succ, Fin.succ_ne_zero i⟩
  have hi : Function.Injective index := by
    intro i j hij
    exact Fin.succ_injective _ (congrArg Subtype.val hij)
  have hlin := ((affineIndependent_iff_linearIndependent_vsub ℝ a 0).mp ha).comp index hi
  have hz := (Fintype.linearIndependent_iff.mp hlin) ![s, t]
    (by simpa [Fin.sum_univ_two, index, Function.comp_def, vsub_eq_sub] using h)
  exact ⟨hz 0, hz 1⟩

private theorem barycentric_force (q : Fin 3 → ℝ) (a : Fin 3 → E)
    (ha : AffineIndependent ℝ a) (hq : ∀ i, q i ≠ 0) {x : E}
    (hx : x ∉ Set.range a) (hf : ∑ i, (-q i / ‖x - a i‖ ^ 3) • (x - a i) = 0) :
    let w := fun i => -q i / ‖x - a i‖ ^ 3
    let T := ∑ i, w i
    let u := w 1 / T
    let v := w 2 / T
    let b : Fin 3 → ℝ := ![1 - u - v, u, v]
    x = a 0 + (u • (a 1 - a 0) + v • (a 2 - a 0)) ∧ T ≠ 0 ∧
      (∀ i, b i * ‖x - a i‖ ^ 3 = -q i / T) ∧
      ∃ s : ℝ, ∀ i, 0 < s * b i * q i := by
  let w := fun i => -q i / ‖x - a i‖ ^ 3
  let T := ∑ i, w i
  let u := w 1 / T
  let v := w 2 / T
  let b : Fin 3 → ℝ := ![1 - u - v, u, v]
  have hn (i : Fin 3) : 0 < ‖x - a i‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hx ⟨i, h.symm⟩))
  have hT : T ≠ 0 := by
    intro hz
    have he := Finset.sum_smul_const_vsub_eq_neg_weightedVSub Finset.univ w a x hz
    rw [show (∑ i, w i • (x -ᵥ a i)) = 0 from hf, eq_comm, neg_eq_zero] at he
    exact (div_ne_zero (neg_ne_zero.mpr (hq 0)) (pow_ne_zero 3 (hn 0).ne'))
      ((affineIndependent_iff_of_fintype ℝ a).mp ha w hz he 0)
  have hweighted : T • x = ∑ i, w i • a i := by
    simpa only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_eq_zero] using hf
  have hshift : T • (x - a 0) = w 1 • (a 1 - a 0) + w 2 • (a 2 - a 0) := by
    calc
      T • (x - a 0) = ∑ i, w i • (a i - a 0) := by
        rw [smul_sub, hweighted]
        simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, T]
      _ = _ := by simp [Fin.sum_univ_three]
  have hpos : x = a 0 + (u • (a 1 - a 0) + v • (a 2 - a 0)) := by
    have hh := congrArg (fun y : E => T⁻¹ • y) hshift
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hT, one_smul] at hh
    rw [sub_eq_iff_eq_add] at hh
    simpa only [u, v, div_eq_mul_inv, mul_comm T⁻¹, add_comm] using hh
  have hb (i : Fin 3) : b i = w i / T := by
    fin_cases i
    · change 1 - w 1 / T - w 2 / T = w 0 / T
      field_simp [hT]
      simp only [T, Fin.sum_univ_three]
      ring
    · rfl
    · rfl
  refine ⟨hpos, hT, ?_, -T, ?_⟩
  · intro i
    change b i * ‖x - a i‖ ^ 3 = -q i / T
    rw [hb]
    change (-q i / ‖x - a i‖ ^ 3) / T * ‖x - a i‖ ^ 3 = -q i / T
    field_simp [(hn i).ne', hT]
  · intro i
    have he : -T * b i * q i = q i ^ 2 / ‖x - a i‖ ^ 3 := by
      rw [hb]
      change -T * ((-q i / ‖x - a i‖ ^ 3) / T) * q i = _
      field_simp [(hn i).ne', hT]
    rw [he]
    exact div_pos (sq_pos_of_ne_zero (hq i)) (pow_pos (hn i) _)

/-- Differentiate a single Coulomb term away from its source.
The gradient calculation is from the parent reduction (Open Math Agents PR #4126). -/
private theorem coulomb_hasGradient (q : ℝ) {a x : (EuclideanSpace ℝ (Fin 3))} (hne : x ≠ a) :
    HasGradientAt (fun y : (EuclideanSpace ℝ (Fin 3)) => q / dist y a)
      ((-q / ‖x - a‖ ^ 3) • (x - a)) x := by
  have hn : ‖x - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hs : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y - a‖ ^ 2)
      (2 • innerSL ℝ (x - a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  have hd : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y - a‖)
      (‖x - a‖⁻¹ • innerSL ℝ (x - a)) x := by
    convert! hs.sqrt (pow_ne_zero 2 hn) using 1
    · funext y
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      field_simp [hn]
      norm_num
  have hderiv := ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul q
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hderiv using 1
  ext v
  simp [toDual_apply_apply, div_eq_mul_inv, smul_smul]
  field_simp [hn]
  simp

private theorem potential_gradient (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3)))
    (hx : x ∉ Set.range a) :
    HasGradientAt (potential q a) (∑ i, (-q i / ‖x - a i‖ ^ 3) • (x - a i)) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  unfold potential
  rw [map_sum]
  exact HasFDerivAt.fun_sum fun i _ =>
    (coulomb_hasGradient (q i) (fun h => hx ⟨i, h.symm⟩)).hasFDerivAt

set_option maxHeartbeats 1000000 in
/-- A nondegenerate Hessian at an off-site equilibrium gives an injective Jacobian
for the two-variable polynomial equations. The square differences factor through
the ratios of barycentric coordinates to Coulomb weights. -/
private theorem jacobian_at_equilibrium :
  ∀ (q : Fin 3 → ℝ) (a : Fin 3 → EuclideanSpace ℝ (Fin 3)),
    AffineIndependent ℝ a → (∀ i, q i ≠ 0) →
    let x := fun t : ℝ × ℝ => a 0 + (t.1 • (a 1 - a 0) + t.2 • (a 2 - a 0))
    let D := fun (t : ℝ × ℝ) i => ‖x t - a i‖ ^ 2
    let P := fun t : ℝ × ℝ =>
      ((q 0 * t.1) ^ 2 * (D t 1) ^ 3 - (q 1 * (1 - t.1 - t.2)) ^ 2 * (D t 0) ^ 3,
       (q 0 * t.2) ^ 2 * (D t 2) ^ 3 - (q 2 * (1 - t.1 - t.2)) ^ 2 * (D t 0) ^ 3)
    ∀ t, x t ∈ equilibria q a → HasNondegenerateHessianAt (potential q a) (x t) →
      Function.Injective (fderiv ℝ P t) := by
  intro q a ha hq X D P t ht hnd
  let r (i : Fin 3) (s : ℝ × ℝ) := ‖X s - a i‖
  let w (i : Fin 3) (s : ℝ × ℝ) := -q i / r i s ^ 3
  let B (i : Fin 3) (s : ℝ × ℝ) := (![1 - s.1 - s.2, s.1, s.2] : Fin 3 → ℝ) i
  let L (i : Fin 3) (s : ℝ × ℝ) := B i s * r i s ^ 3 / (-q i)
  let F (y : EuclideanSpace ℝ (Fin 3)) :=
    ∑ i, (-q i / ‖y - a i‖ ^ 3) • (y - a i)
  change X t ∉ Set.range a ∧ ∇ (potential q a) (X t) = 0 at ht
  change Function.Injective (fderiv ℝ P t)
  have hfar (i : Fin 3) : X t - a i ≠ 0 :=
    sub_ne_zero.mpr (fun h => ht.1 ⟨i, h.symm⟩)
  have hF : F (X t) = 0 := (potential_gradient q a (X t) ht.1).gradient.symm.trans ht.2
  let T := ∑ i, w i t
  obtain ⟨hx, hT, hb, _⟩ := barycentric_force q a ha hq ht.1 hF
  let u := w 1 t / T
  let v := w 2 t / T
  change X t = X (u, v) at hx
  have hc : t.1 = u ∧ t.2 = v := by
    have he : (t.1 - u) • (a 1 - a 0) + (t.2 - v) • (a 2 - a 0) = 0 := by
      simp only [X, add_right_inj] at hx
      simp only [sub_smul]
      rw [sub_add_sub_comm, hx, sub_self]
    obtain ⟨h₁, h₂⟩ := coefficients_eq_zero a ha he
    exact ⟨sub_eq_zero.mp h₁, sub_eq_zero.mp h₂⟩
  have hL (i : Fin 3) : L i t = T⁻¹ := by
    change B i t * r i t ^ 3 / (-q i) = _
    have he : B i t * r i t ^ 3 = -q i / T := by
      dsimp only [B, r]
      rw [hc.1, hc.2]
      exact hb i
    rw [he]
    field_simp [hq i, hT]
  have hL0 : L 0 t ≠ 0 := by rw [hL]; exact inv_ne_zero hT
  have hX : DifferentiableAt ℝ X t := by fun_prop
  have hD (i : Fin 3) : DifferentiableAt ℝ (r i) t := by
    exact (hX.sub_const (a i)).norm ℝ (hfar i)
  have hB (i : Fin 3) : DifferentiableAt ℝ (B i) t := by
    fin_cases i
    · change DifferentiableAt ℝ (fun s : ℝ × ℝ => 1 - s.1 - s.2) t
      fun_prop
    · change DifferentiableAt ℝ Prod.fst t
      fun_prop
    · change DifferentiableAt ℝ Prod.snd t
      fun_prop
  have hLd (i : Fin 3) : DifferentiableAt ℝ (L i) t := by
    unfold L
    fun_prop
  have hwd (i : Fin 3) : DifferentiableAt ℝ (w i) t := by
    change DifferentiableAt ℝ (fun s => -q i / r i s ^ 3) t
    have hc : DifferentiableAt ℝ (fun _ : ℝ × ℝ => -q i) t := differentiableAt_const _
    have hd : DifferentiableAt ℝ (fun s => r i s ^ 3) t := by fun_prop
    have hn : r i t ^ 3 ≠ 0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr (hfar i))
    fun_prop (disch := exact hn)
  have hP : DifferentiableAt ℝ P t := by
    have hD' (i : Fin 3) : DifferentiableAt ℝ (fun s => D s i) t := (hD i).pow 2
    dsimp only [P]
    fun_prop
  apply (LinearMap.ker_eq_bot.mp ?_ : Function.Injective (fderiv ℝ P t))
  rw [LinearMap.ker_eq_bot']
  intro z hz'
  change fderiv ℝ P t z = 0 at hz'
  -- A direction in the polynomial kernel differentiates all three ratios equally.
  have hsq (i : Fin 3) : (fun s => (q 0 * B i s) ^ 2 * (D s i) ^ 3 -
      (q i * B 0 s) ^ 2 * (D s 0) ^ 3) =
      fun s => (q 0 * q i) ^ 2 * ((L i s) ^ 2 - (L 0 s) ^ 2) := by
    funext s
    dsimp only [D, L, r]
    field_simp [hq i, hq 0]
  have hLi (i : Fin 3)
      (hi : fderiv ℝ (fun s => (q 0 * B i s) ^ 2 * (D s i) ^ 3 -
          (q i * B 0 s) ^ 2 * (D s 0) ^ 3) t z = 0) :
        fderiv ℝ (L i) t z = fderiv ℝ (L 0) t z := by
    have he : fderiv ℝ (fun s => (q 0 * q i) ^ 2 * ((L i s) ^ 2 - (L 0 s) ^ 2)) t = _ :=
      ((((hLd i).hasFDerivAt.pow 2).sub ((hLd 0).hasFDerivAt.pow 2))
        |>.const_mul ((q 0 * q i) ^ 2)).fderiv
    rw [hsq, he] at hi
    simp only [smul_apply, sub_apply, smul_eq_mul, hL] at hi
    have hc : (q 0 * q i) ^ 2 * (2 * T⁻¹) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 (mul_ne_zero (hq 0) (hq i)))
        (mul_ne_zero (by norm_num) (inv_ne_zero hT))
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (_ : ((q 0 * q i) ^ 2 * (2 * T⁻¹)) *
      (fderiv ℝ (L i) t z - fderiv ℝ (L 0) t z) = 0)).resolve_left hc
    linear_combination hi
  have hdiff (i : Fin 3) : fderiv ℝ (L i) t z = fderiv ℝ (L 0) t z := by
    fin_cases i
    · rfl
    · apply hLi 1
      change fderiv ℝ (fun s => (P s).1) t z = 0
      rw [hP.hasFDerivAt.fst.fderiv]
      exact congrArg Prod.fst hz'
    · apply hLi 2
      change fderiv ℝ (fun s => (P s).2) t z = 0
      rw [hP.hasFDerivAt.snd.fderiv]
      exact congrArg Prod.snd hz'
  have hZd (i : Fin 3) :
      DifferentiableAt ℝ (fun s => w i s • (X s - a i)) t :=
    (hwd i).smul (hX.sub_const _)
  have hFd : DifferentiableAt ℝ F (X t) := by
    have hterm (i : Fin 3) : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
        (-q i / ‖y - a i‖ ^ 3) • (y - a i)) (X t) := by
      have hl : DifferentiableAt ℝ
          (fun y : EuclideanSpace ℝ (Fin 3) => y - a i) (X t) :=
        differentiableAt_id.sub_const (a i)
      have hr : DifferentiableAt ℝ (fun y => ‖y - a i‖ ^ 3) (X t) := by
        have hd := hl.norm ℝ (hfar i)
        fun_prop
      have hn : ‖X t - a i‖ ^ 3 ≠ 0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr (hfar i))
      fun_prop (disch := exact hn)
    simp only [F, Fin.sum_univ_three]
    fun_prop
  have hoff : ∀ᶠ s in 𝓝 t, ∀ i, X s - a i ≠ 0 := by
    rw [Filter.eventually_all]
    exact fun i => (hX.sub_const (a i)).continuousAt.eventually_ne (hfar i)
  -- The barycentric force is identically zero. Subtract it from the Coulomb force.
  have halg : (fun s => L 0 s • F (X s)) =ᶠ[𝓝 t] fun s =>
      ∑ i, (L 0 s - L i s) • (w i s • (X s - a i)) := by
    filter_upwards [hoff] with s hs
    have hweighted : ∑ i, B i s • (X s - a i) = 0 := by
      have hb0 : B 0 s = 1 - s.1 - s.2 := rfl
      have hb1 : B 1 s = s.1 := rfl
      have hb2 : B 2 s = s.2 := rfl
      simp only [Fin.sum_univ_three, hb0, hb1, hb2, X, smul_sub, sub_smul, one_smul]
      module
    have hcancel (i : Fin 3) : L i s • (w i s • (X s - a i)) = B i s • (X s - a i) := by
      rw [smul_smul]
      congr 1
      have hr : r i s ≠ 0 := norm_ne_zero_iff.mpr (hs i)
      dsimp only [L, w]
      field_simp [hr, hq i]
    change L 0 s • (∑ i, w i s • (X s - a i)) =
      ∑ i, (L 0 s - L i s) • (w i s • (X s - a i))
    simp only [Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, hcancel, hweighted, sub_zero]
  have hdcomp := hFd.comp t hX
  have hcorrect (i : Fin 3) :
      fderiv ℝ (fun s => (L 0 s - L i s) • (w i s • (X s - a i))) t z = 0 := by
    have he : fderiv ℝ (fun s => (L 0 s - L i s) • (w i s • (X s - a i))) t = _ :=
      (((hLd 0).hasFDerivAt.sub (hLd i).hasFDerivAt).smul (hZd i).hasFDerivAt).fderiv
    rw [he]
    simp [hL, hdiff i]
  have hcompzero : fderiv ℝ (F ∘ X) t z = 0 := by
    have heq := congrArg (fun f : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) => f z)
      (halg.fderiv_eq)
    have hl : fderiv ℝ (fun s => L 0 s • F (X s)) t = _ :=
      ((hLd 0).hasFDerivAt.smul hdcomp.hasFDerivAt).fderiv
    have hterm (i : Fin 3) : DifferentiableAt ℝ
        (fun s => (L 0 s - L i s) • (w i s • (X s - a i))) t := by
      fun_prop
    have hr := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (hterm i).hasFDerivAt
    rw [hl, hr.fderiv] at heq
    simp [hF, hcorrect, Function.comp_def] at heq
    exact heq.resolve_left hL0
  have hchain := (hFd.hasFDerivAt.comp t hX.hasFDerivAt).fderiv
  rw [hchain, ContinuousLinearMap.comp_apply] at hcompzero
  have hfdd : fderiv ℝ (fderiv ℝ (potential q a)) (X t) (fderiv ℝ X t z) = 0 := by
    have hoff' : ∀ᶠ y in 𝓝 (X t), ∀ i, y - a i ≠ 0 := by
      rw [Filter.eventually_all]
      intro i
      have hc : ContinuousAt (fun y : EuclideanSpace ℝ (Fin 3) => y - a i) (X t) := by
        fun_prop
      exact hc.eventually_ne (hfar i)
    have hevent : fderiv ℝ (potential q a) =ᶠ[𝓝 (X t)] fun y => innerSL ℝ (F y) := by
      filter_upwards [hoff'] with y hy
      have hya : y ∉ Set.range a := by
        rintro ⟨i, hi⟩
        exact (hy i) (sub_eq_zero.mpr hi.symm)
      exact (potential_gradient q a y hya).hasFDerivAt.fderiv
    have hdg : fderiv ℝ (fun y => innerSL ℝ (F y)) (X t) = _ :=
      ((innerSL ℝ : _ →L[ℝ] _).hasFDerivAt.comp (X t) hFd.hasFDerivAt).fderiv
    rw [hevent.fderiv_eq, hdg, ContinuousLinearMap.comp_apply, hcompzero, map_zero]
  have hxzero : fderiv ℝ X t z = 0 := by
    by_contra hn
    obtain ⟨y, hy⟩ := hnd _ hn
    apply hy
    rw [iteratedFDeriv_two_apply]
    change fderiv ℝ (fderiv ℝ (potential q a)) (X t) (fderiv ℝ X t z) y = 0
    rw [hfdd, zero_apply]
  have hXexplicit := (((hasFDerivAt_fst (𝕜 := ℝ) (p := t)).smul_const (a 1 - a 0)).add
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := t)).smul_const (a 2 - a 0))).const_add (a 0)
  rw [show fderiv ℝ X t = _ from hXexplicit.fderiv] at hxzero
  have final : z.1 • (a 1 - a 0) + z.2 • (a 2 - a 0) = 0 := hxzero
  obtain ⟨hz₁, hz₂⟩ := coefficients_eq_zero a ha final
  exact Prod.ext hz₁ hz₂

/-- Four-root bound for the same-sign charge chamber. -/
def H1 : Prop :=
  ∀ (A B C : ℝ) (q : Fin 3 → ℝ),
    (∀ s t : ℝ, (s, t) ≠ (0, 0) → 0 < A * s ^ 2 + 2 * B * s * t + C * t ^ 2) →
    (∀ i, q i ≠ 0) → (∀ i, 0 < q 0 * q i) →
    let G := fun s t : ℝ => A * s ^ 2 + 2 * B * s * t + C * t ^ 2
    let D := fun t : ℝ × ℝ =>
      ![G t.1 t.2, G (t.1 - 1) t.2, G t.1 (t.2 - 1)]
    let P := fun t : ℝ × ℝ =>
      ((q 0 * t.1) ^ 2 * (D t 1) ^ 3 - (q 1 * (1 - t.1 - t.2)) ^ 2 * (D t 0) ^ 3,
       (q 0 * t.2) ^ 2 * (D t 2) ^ 3 - (q 2 * (1 - t.1 - t.2)) ^ 2 * (D t 0) ^ 3)
    {t : ℝ × ℝ | P t = 0 ∧ Function.Injective (fderiv ℝ P t) ∧
      ∃ s : ℝ, ∀ i, 0 < s * (![1 - t.1 - t.2, t.1, t.2] : Fin 3 → ℝ) i * q i}.encard ≤ 4

/-- Four-root bound for mixed signs. -/
def H2 : Prop :=
  ∀ (A B C : ℝ) (q : Fin 3 → ℝ),
    (∀ s t : ℝ, (s, t) ≠ (0, 0) → 0 < A * s ^ 2 + 2 * B * s * t + C * t ^ 2) →
    (∀ i, q i ≠ 0) → (∃ i, q 0 * q i < 0) →
    let G := fun s t : ℝ => A * s ^ 2 + 2 * B * s * t + C * t ^ 2
    let D := fun t : ℝ × ℝ =>
      ![G t.1 t.2, G (t.1 - 1) t.2, G t.1 (t.2 - 1)]
    let P := fun t : ℝ × ℝ =>
      ((q 0 * t.1) ^ 2 * (D t 1) ^ 3 - (q 1 * (1 - t.1 - t.2)) ^ 2 * (D t 0) ^ 3,
       (q 0 * t.2) ^ 2 * (D t 2) ^ 3 - (q 2 * (1 - t.1 - t.2)) ^ 2 * (D t 0) ^ 3)
    {t : ℝ × ℝ | P t = 0 ∧ Function.Injective (fderiv ℝ P t) ∧
      ∃ s : ℝ, ∀ i, 0 < s * (![1 - t.1 - t.2, t.1, t.2] : Fin 3 → ℝ) i * q i}.encard ≤ 4

theorem main : H1 → H2 → OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_charges_R1.H1 := by
  intro hSame hMixed q a ha hq hnd
  let A := ‖a 1 - a 0‖ ^ 2
  let B := ⟪a 1 - a 0, a 2 - a 0⟫_ℝ
  let C := ‖a 2 - a 0‖ ^ 2
  let G := fun s t : ℝ => A * s ^ 2 + 2 * B * s * t + C * t ^ 2
  let X := fun t : ℝ × ℝ => a 0 + (t.1 • (a 1 - a 0) + t.2 • (a 2 - a 0))
  let D := fun t : ℝ × ℝ =>
    ![G t.1 t.2, G (t.1 - 1) t.2, G t.1 (t.2 - 1)]
  let P := fun t : ℝ × ℝ =>
    ((q 0 * t.1) ^ 2 * (D t 1) ^ 3 - (q 1 * (1 - t.1 - t.2)) ^ 2 * (D t 0) ^ 3,
     (q 0 * t.2) ^ 2 * (D t 2) ^ 3 - (q 2 * (1 - t.1 - t.2)) ^ 2 * (D t 0) ^ 3)
  let Roots := {t : ℝ × ℝ | P t = 0 ∧ Function.Injective (fderiv ℝ P t) ∧
    ∃ s : ℝ, ∀ i, 0 < s * (![1 - t.1 - t.2, t.1, t.2] : Fin 3 → ℝ) i * q i}
  have hpos (s t : ℝ) (hst : (s, t) ≠ (0, 0)) : 0 < G s t := by
    change 0 < ‖a 1 - a 0‖ ^ 2 * s ^ 2 + 2 * ⟪a 1 - a 0, a 2 - a 0⟫_ℝ * s * t +
      ‖a 2 - a 0‖ ^ 2 * t ^ 2
    rw [← norm_sq_gram]
    refine pow_pos (norm_pos_iff.mpr ?_) _
    intro hz
    obtain ⟨rfl, rfl⟩ := coefficients_eq_zero a ha hz
    exact hst rfl
  have hdist : D = fun (t : ℝ × ℝ) i => ‖X t - a i‖ ^ 2 := by
    funext t i
    fin_cases i
    · change G t.1 t.2 = ‖X t - a 0‖ ^ 2
      simpa only [X, add_sub_cancel_left] using
        (norm_sq_gram (a 1 - a 0) (a 2 - a 0) t.1 t.2).symm
    · change G (t.1 - 1) t.2 = ‖X t - a 1‖ ^ 2
      have hv : X t - a 1 =
          (t.1 - 1) • (a 1 - a 0) + t.2 • (a 2 - a 0) := by
        simp only [X, sub_smul, one_smul]
        abel
      rw [hv]
      exact (norm_sq_gram (a 1 - a 0) (a 2 - a 0) (t.1 - 1) t.2).symm
    · change G t.1 (t.2 - 1) = ‖X t - a 2‖ ^ 2
      have hv : X t - a 2 =
          t.1 • (a 1 - a 0) + (t.2 - 1) • (a 2 - a 0) := by
        simp only [X, sub_smul, one_smul]
        abel
      rw [hv]
      exact (norm_sq_gram (a 1 - a 0) (a 2 - a 0) t.1 (t.2 - 1)).symm
  let coord (x : EuclideanSpace ℝ (Fin 3)) : ℝ × ℝ :=
    let w := fun i => -q i / ‖x - a i‖ ^ 3
    let T := ∑ i, w i
    (w 1 / T, w 2 / T)
  let Z := {x : EuclideanSpace ℝ (Fin 3) | x ∈ affineSpan ℝ (Set.range a) ∧
    x ∉ Set.range a ∧ (∑ i, (-q i / ‖x - a i‖ ^ 3) • (x - a i)) = 0}
  have hrec (x) (hx : x ∈ Z) : x = X (coord x) :=
    (barycentric_force q a ha hq hx.2.1 hx.2.2).1
  have hmaps : Set.MapsTo coord Z Roots := by
    intro x hx
    let t := coord x
    let T := ∑ i, -q i / ‖x - a i‖ ^ 3
    let b : Fin 3 → ℝ := ![1 - t.1 - t.2, t.1, t.2]
    obtain ⟨hX, _, hb, hsign⟩ := barycentric_force q a ha hq hx.2.1 hx.2.2
    change x = X t at hX
    change (∀ i, b i * ‖x - a i‖ ^ 3 = -q i / T) at hb
    have heq : x ∈ equilibria q a :=
      ⟨hx.2.1, (potential_gradient q a x hx.2.1).gradient.trans hx.2.2⟩
    have hreg : Function.Injective (fderiv ℝ P t) := by
      have heq' : X t ∈ equilibria q a := hX ▸ heq
      have hj := jacobian_at_equilibrium q a ha hq t heq' (hnd _ heq')
      have hP : P = fun t : ℝ × ℝ =>
          ((q 0 * t.1) ^ 2 * (D t 1) ^ 3 - (q 1 * (1 - t.1 - t.2)) ^ 2 * (D t 0) ^ 3,
           (q 0 * t.2) ^ 2 * (D t 2) ^ 3 - (q 2 * (1 - t.1 - t.2)) ^ 2 * (D t 0) ^ 3) := rfl
      rw [hP, hdist]
      exact hj
    have hpoly (i : Fin 3) :
        (q 0 * b i) ^ 2 * (D t i) ^ 3 = (q i * b 0) ^ 2 * (D t 0) ^ 3 := by
      have hmul : q 0 * b i * ‖x - a i‖ ^ 3 = q i * b 0 * ‖x - a 0‖ ^ 3 := by
        rw [mul_assoc, hb i, mul_assoc, hb 0]
        ring
      simp only [hdist, ← hX]
      linear_combination congrArg (fun z : ℝ => z ^ 2) hmul
    refine ⟨?_, hreg, hsign⟩
    change P t = 0
    exact Prod.ext (sub_eq_zero.mpr (hpoly 1)) (sub_eq_zero.mpr (hpoly 2))
  have hinj : Set.InjOn coord Z := by
    intro x hx y hy hxy
    rw [hrec x hx, hrec y hy, hxy]
  refine (Set.encard_le_encard_of_injOn hmaps hinj).trans ?_
  change Roots.encard ≤ 4
  by_cases hs : ∀ i, 0 < q 0 * q i
  · exact hSame A B C q hpos hq hs
  · push Not at hs
    obtain ⟨i, hi⟩ := hs
    exact hMixed A B C q hpos hq ⟨i, lt_of_le_of_ne hi (mul_ne_zero (hq 0) (hq i))⟩

end OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_charges_R1_H1_R1
