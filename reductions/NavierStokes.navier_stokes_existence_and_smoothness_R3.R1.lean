import FormalConjectures.Millennium.NavierStokes
import Mathlib.Tactic

/-!
# Navier–Stokes on ℝ³, Clay alternative (A): classical local theory + an a priori bound

This file splits the registry statement the way the problem is usually described in the
literature (Fefferman's Clay statement; Robinson–Rodrigo–Sadowski, *The Three-Dimensional
Navier–Stokes Equations: Classical Theory*, CUP 2016).

* `H1` is classical, published mathematics: local well-posedness of strong solutions for smooth
  divergence-free Schwartz data together with Leray's blow-up alternative (J. Leray, Acta Math. 63
  (1934) 193–248; T. Kato, Math. Z. 187 (1984) 471–480). At viscosity `1`, either the maximal
  strong solution is global (and then it is a solution in the sense of the registry, with energy
  at most `‖u₀‖²`), or the maximal time `T` is finite, the solution is smooth on `ℝ³ × [0,T)`
  with every spatial `Hᵐ` norm bounded on each `[0,T']`, `T' < T`, and its sup norm is unbounded.
* `H2` is the open core: an a priori sup-norm bound for such strong solutions on a finite time
  interval, at viscosity `1`. Given `H1` and the classical uniqueness of strong solutions, `H2` is
  equivalent to the registry statement, so it carries exactly the difficulty of the Millennium
  problem; nothing here claims progress on it. Known reformulations that would also suffice
  through classical criteria: a bound on `‖v(t)‖_{L³}` (Escauriaza–Seregin–Šverák 2003) or on
  `∫ ‖curl v‖_∞` (Beale–Kato–Majda 1984).

What `main` proves (no extra assumptions): the viscosity normalisation. If `(w, q)` solves the
problem with viscosity `1` and data `ν⁻¹ • u₀`, then `v x t = ν • w x (ν t)`,
`p x t = ν² q x (ν t)` solves it with viscosity `ν` and data `u₀` (equation, incompressibility,
initial condition, smoothness on `ℝ³ × [0,∞)`, square integrability and the energy bound are all
transported), and the data `ν⁻¹ • u₀` again satisfies the decay condition. The blow-up branch of
`H1` is excluded by `H2`.
-/

namespace OMA.R_NavierStokes_navier_stokes_existence_and_smoothness_R3_R1

open NavierStokes Set MeasureTheory InnerProductSpace ContDiff EuclideanGeometry
open scoped Laplacian

/-- Classical local theory at viscosity 1 (Leray 1934, Kato 1984): the maximal strong solution
is either global, or blows up in sup norm at a finite time `T`, being smooth on `ℝ³ × [0,T)` with
every spatial `Hᵐ` norm bounded on each `[0,T']`, `T' < T`. -/
def H1 : Prop :=
  ∀ u₀ : ℝ³ → ℝ³, InitialVelocityConditionDecay u₀ →
    (∃ v p, NavierStokesExistenceAndSmoothnessRn 1 u₀ 0 v p) ∨
    ∃ T > (0 : ℝ), ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      ((∀ x, ∀ t ∈ Ico 0 T, derivWithin (v x ·) (Ici 0) t + fderiv ℝ (v · t) x (v x t) =
          Δ (v · t) x - gradient (p · t) x) ∧
        (∀ x, ∀ t ∈ Ico 0 T, ∇⬝ (v · t) x = 0) ∧ (∀ x, v x 0 = u₀ x) ∧
        ContDiffOn ℝ ∞ (↿v) (univ ×ˢ Ico 0 T) ∧ ContDiffOn ℝ ∞ (↿p) (univ ×ˢ Ico 0 T) ∧
        ∀ m : ℕ, ∀ T' < T, ∃ C : ℝ, ∀ t ∈ Icc 0 T',
          eLpNorm (iteratedFDeriv ℝ m (v · t)) 2 volume ≤ ENNReal.ofReal C) ∧
      ∀ M : ℝ, ∃ x, ∃ t ∈ Ico 0 T, M < ‖v x t‖

/-- The open core at viscosity 1: strong solutions on a finite interval `[0,T)`, in the same
class, have bounded velocity. Equivalent to the target given the first hypothesis and the
classical uniqueness of strong solutions. -/
def H2 : Prop :=
  ∀ u₀ : ℝ³ → ℝ³, InitialVelocityConditionDecay u₀ →
    ∀ T > (0 : ℝ), ∀ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      ((∀ x, ∀ t ∈ Ico 0 T, derivWithin (v x ·) (Ici 0) t + fderiv ℝ (v · t) x (v x t) =
          Δ (v · t) x - gradient (p · t) x) ∧
        (∀ x, ∀ t ∈ Ico 0 T, ∇⬝ (v · t) x = 0) ∧ (∀ x, v x 0 = u₀ x) ∧
        ContDiffOn ℝ ∞ (↿v) (univ ×ˢ Ico 0 T) ∧ ContDiffOn ℝ ∞ (↿p) (univ ×ˢ Ico 0 T) ∧
        ∀ m : ℕ, ∀ T' < T, ∃ C : ℝ, ∀ t ∈ Icc 0 T',
          eLpNorm (iteratedFDeriv ℝ m (v · t)) 2 volume ≤ ENNReal.ofReal C) →
      ∃ M : ℝ, ∀ x, ∀ t ∈ Ico 0 T, ‖v x t‖ ≤ M

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function smooth on `ℝ³ × [0,∞)` is smooth in space at every time `s ≥ 0`. -/
lemma slice_x {w : ℝ³ → ℝ → F} (hw : ContDiffOn ℝ ∞ (↿w) (univ ×ˢ Ici 0)) {s : ℝ}
    (hs : 0 ≤ s) : ContDiff ℝ ∞ (fun x => w x s) := by
  have : ContDiffOn ℝ ∞ (fun x : ℝ³ => (↿w) (x, s)) univ :=
    hw.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun x _ => ⟨mem_univ _, hs⟩)
  exact contDiffOn_univ.mp this

/-- A function smooth on `ℝ³ × [0,∞)` is smooth in time on `[0,∞)` at every point. -/
lemma slice_t {w : ℝ³ → ℝ → F} (hw : ContDiffOn ℝ ∞ (↿w) (univ ×ˢ Ici 0)) (x : ℝ³) :
    ContDiffOn ℝ ∞ (fun t => w x t) (Ici 0) :=
  hw.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ ht => ⟨mem_univ _, ht⟩)

lemma decay_smul {u₀ : ℝ³ → ℝ³} (hu : InitialVelocityConditionDecay u₀) (c : ℝ) :
    InitialVelocityConditionDecay (c • u₀) where
  div_free x := by
    have hd : DifferentiableAt ℝ u₀ x := (hu.smooth.differentiable (by simp)).differentiableAt
    have := divergence_smul c hd
    simp only [hu.div_free x, mul_zero] at this
    exact this
  smooth := hu.smooth.const_smul c
  decay m K := by
    obtain ⟨C, hC⟩ := hu.decay m K
    refine ⟨|c| * C, fun x => ?_⟩
    rw [iteratedFDeriv_const_smul_apply (contDiff_infty.1 hu.smooth m).contDiffAt, norm_smul,
      Real.norm_eq_abs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)

theorem rescale {nu : ℝ} (hnu : 0 < nu) {u₀ : ℝ³ → ℝ³} {w : ℝ³ → ℝ → ℝ³} {q : ℝ³ → ℝ → ℝ}
    (h : NavierStokesExistenceAndSmoothnessRn 1 (nu⁻¹ • u₀) 0 w q) :
    NavierStokesExistenceAndSmoothnessRn nu u₀ 0 (fun x t => nu • w x (nu * t))
      (fun x t => nu ^ 2 * q x (nu * t)) := by
  have hv := h.velocity_smooth
  have hp := h.pressure_smooth
  have hφ : MapsTo (fun z : ℝ³ × ℝ => (z.1, nu * z.2)) (univ ×ˢ Ici 0) (univ ×ˢ Ici 0) :=
    fun z hz => ⟨mem_univ _, mul_nonneg hnu.le hz.2⟩
  have hφc : ContDiff ℝ ∞ (fun z : ℝ³ × ℝ => (z.1, nu * z.2)) :=
    contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)
  refine
    { navier_stokes := ?_
      div_free := ?_
      initial_condition := ?_
      velocity_smooth := ?_
      pressure_smooth := ?_
      integrable := ?_
      globally_bounded_energy := ?_ }
  · intro x t ht
    have ht' : 0 ≤ nu * t := mul_nonneg hnu.le ht
    have hns := h.navier_stokes x (nu * t) ht'
    have hdt : HasDerivWithinAt (fun s => w x s)
        (derivWithin (fun s => w x s) (Ici 0) (nu * t)) (Ici 0) (nu * t) :=
      ((slice_t hv x).differentiableOn (by simp) _ ht').hasDerivWithinAt
    have hcomp : HasDerivWithinAt (fun s => nu • w x (nu * s))
        (nu • (nu • derivWithin (fun s => w x s) (Ici 0) (nu * t))) (Ici 0) t := by
      have h1 : HasDerivWithinAt (fun s : ℝ => nu * s) nu (Ici 0) t := by
        simpa using (hasDerivWithinAt_id t (Ici 0)).const_mul nu
      have h2 := hdt.scomp t h1 (fun s hs => mul_nonneg hnu.le hs)
      exact h2.const_smul nu
    have hxs := slice_x hv ht'
    have hdiff : DifferentiableAt ℝ (fun y => w y (nu * t)) x :=
      (hxs.differentiable (by simp)).differentiableAt
    have hqs := slice_x hp ht'
    have hqdiff : DifferentiableAt ℝ (fun y => q y (nu * t)) x :=
      (hqs.differentiable (by simp)).differentiableAt
    have hfd : fderiv ℝ (fun y => nu • w y (nu * t)) x = nu • fderiv ℝ (fun y => w y (nu * t)) x :=
      fderiv_const_smul hdiff nu
    have hlap : Δ (fun y => nu • w y (nu * t)) x = nu • Δ (fun y => w y (nu * t)) x :=
      laplacian_smul nu (contDiff_infty.1 hxs 2).contDiffAt
    have hgrad : gradient (fun y => nu ^ 2 * q y (nu * t)) x =
        nu ^ 2 • gradient (fun y => q y (nu * t)) x := by
      simp only [gradient]
      rw [fderiv_const_mul hqdiff]
      simp
    show derivWithin (fun s => nu • w x (nu * s)) (Ici 0) t +
        fderiv ℝ (fun y => nu • w y (nu * t)) x (nu • w x (nu * t)) =
      nu • Δ (fun y => nu • w y (nu * t)) x - gradient (fun y => nu ^ 2 * q y (nu * t)) x +
        (0 : ℝ³ → ℝ → ℝ³) x t
    rw [hcomp.derivWithin (uniqueDiffOn_Ici 0 t ht), hfd, hlap, hgrad]
    simp only [Pi.zero_apply, add_zero, one_smul] at hns ⊢
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    linear_combination (norm := module) (nu ^ 2) • hns
  · intro x t ht
    have ht' : 0 ≤ nu * t := mul_nonneg hnu.le ht
    have hdiff : DifferentiableAt ℝ (fun y => w y (nu * t)) x :=
      ((slice_x hv ht').differentiable (by simp)).differentiableAt
    show ∇⬝ (fun y => nu • w y (nu * t)) x = 0
    rw [divergence_smul nu hdiff, h.div_free x (nu * t) ht', mul_zero]
  · intro x
    show nu • w x (nu * 0) = u₀ x
    rw [mul_zero, h.initial_condition x, Pi.smul_apply, smul_smul, mul_inv_cancel₀ hnu.ne',
      one_smul]
  · exact (hv.comp hφc.contDiffOn hφ).const_smul nu
  · exact (contDiffOn_const (c := nu ^ 2)).mul (hp.comp hφc.contDiffOn hφ)
  · intro t ht
    have := (h.integrable (nu * t) (mul_nonneg hnu.le ht)).const_mul nu
    simpa [norm_smul, abs_of_pos hnu] using this
  · obtain ⟨E, hE⟩ := h.globally_bounded_energy
    refine ⟨nu ^ 2 * E, fun t ht => ?_⟩
    have := hE (nu * t) (mul_nonneg hnu.le ht)
    simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [integral_const_mul]
    exact mul_lt_mul_of_pos_left this (by positivity)

theorem main : H1 → H2 → type_of% @NavierStokes.navier_stokes_existence_and_smoothness_R3 := by
  intro h1 h2 nu hnu u₀ hu₀
  have hu₁ := decay_smul hu₀ nu⁻¹
  rcases h1 _ hu₁ with ⟨w, q, hw⟩ | ⟨T, hT, w, q, hloc, hunb⟩
  · exact ⟨_, _, rescale hnu hw⟩
  · obtain ⟨M, hM⟩ := h2 _ hu₁ T hT w q hloc
    obtain ⟨x, t, ht, hlt⟩ := hunb M
    exact absurd (hM x t ht) (not_le.mpr hlt)

end OMA.R_NavierStokes_navier_stokes_existence_and_smoothness_R3_R1
