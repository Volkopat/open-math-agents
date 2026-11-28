import OMAReductions.R_Hilbert5_hilbert_fifth_problem_R1
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Reduction of `Hilbert5.hilbert_fifth_problem.R1.H2` (NSS ⇒ Real-Analytic Lie Group)

Following Gleason (1952), Montgomery–Zippin (1952), Yamabe (1953), and Lie's globalization of
local analytic group laws, we reduce `OMA.R_Hilbert5_hilbert_fifth_problem_R1.H2` (every connected
Hausdorff locally Euclidean topological group `H : Type` with no small subgroups admits an
`n`-dimensional real-analytic `LieGroupPresentation`) to three canonical theorems:

1. (`H1`) **Gleason's Canonical Coordinates of the First Kind**: every connected Hausdorff
   locally Euclidean topological group `H` with no small subgroups admits a local homeomorphism
   `φ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin d))` at `1` (`φ 1 = 0`, `B(0, r) ⊆ φ.target`)
   whose inverse maps radial lines `t ↦ t • v` locally to one-parameter subgroups (in particular
   `φ.symm (-u) = (φ.symm u)⁻¹` on `B(0, r)`).
2. (`H2`) **Baker–Campbell–Hausdorff Real Analyticity**: for any connected Hausdorff topological
   group `H` equipped with canonical coordinates of the first kind `φ` on `B(0, r)`, there exists
   `r₀ ∈ (0, r]` such that the local multiplication `F(u, v) = φ (φ.symm u * φ.symm v)` maps
   `B(0, r₀) × B(0, r₀)` into `B(0, r)` and is real-analytic (`ContDiffOn ℝ ω`) on
   `B(0, r₀) × B(0, r₀)`.
3. (`H3`) **Brouwer's Invariance of Dimension**: if a nonempty Hausdorff space `H : Type` has
   `ChartedSpace (EuclideanSpace ℝ (Fin n)) H` and admits a `OpenPartialHomeomorph` to
   `EuclideanSpace ℝ (Fin d)` with nonempty source, then `d = n`.

Inside `main`, we prove **Lie's globalization theorem** completely from scratch:
- Transport `d = n` from `H3`, shrink `r₁ ∈ (0, r₀]` so `F(B(0, r₁) × B(0, r₁)) ⊆ B(0, r₀)`,
  and build the global left-translated atlas `chart_g(x) = φ(g⁻¹ * x)` on `H`.
- Prove every chart transition `(chart_h ∘ chart_g.symm)(u) = F(v₀, F(-u₀, u))` near every
  overlap point `u₀` is real-analytic (`ContDiffAt ℝ ω`), establishing `IsManifold (𝓡 n) ω H`.
- Prove that the set of `w : H` whose conjugation `u ↦ φ(w⁻¹ * φ.symm u * w)` is real-analytic
  at `0` is an open (hence, by connectedness, full) subgroup of `H`.
- Prove `LieGroup (𝓡 n) ω H` (`contMDiff_mul` via `F(conj_h(u), v)` and `contMDiff_inv` via
  `conj_{g⁻¹}(-u)`) and construct `LieGroupPresentation H n`.
-/

-- Reduction Hilbert5.hilbert_fifth_problem.R1.H2.R1 of Hilbert5.hilbert_fifth_problem.R1.H2
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

open Set Topology Filter TopologicalSpace
open scoped Manifold ContDiff Pointwise Classical

noncomputable section

namespace OMA.R_Hilbert5_hilbert_fifth_problem_R1_H2_R1

/- ### Helper 1: Left-translated chart atlas from a local homeomorphism at `1` -/

private def restrictBall {H : Type*} [TopologicalSpace H] {n : ℕ}
    (φ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin n))) (r : ℝ) :
    OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin n)) :=
  φ.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) Metric.isOpen_ball)

private def leftChart {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ}
    (e₀ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin n))) (g : H) :
    OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin n)) :=
  (Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph.trans e₀

private lemma leftChart_source {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ}
    (e₀ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin n))) (g : H) :
    (leftChart e₀ g).source = (fun x : H => g⁻¹ * x) ⁻¹' e₀.source := by
  ext x; simp [leftChart]

private lemma leftChart_target {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ}
    (e₀ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin n))) (g : H) :
    (leftChart e₀ g).target = e₀.target := by
  ext y; simp [leftChart]

private lemma leftChart_apply {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ}
    (e₀ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin n))) (g x : H) :
    leftChart e₀ g x = e₀ (g⁻¹ * x) := rfl

private lemma leftChart_symm_apply {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ}
    (e₀ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin n))) (g : H) (u : EuclideanSpace ℝ (Fin n)) :
    (leftChart e₀ g).symm u = g * e₀.symm u := by
  change (g⁻¹)⁻¹ * e₀.symm u = g * e₀.symm u
  rw [inv_inv]

private abbrev leftChartedSpace {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ}
    (e₀ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin n))) (h1 : (1 : H) ∈ e₀.source) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) H where
  atlas := Set.range (leftChart e₀)
  chartAt := leftChart e₀
  mem_chart_source g := by
    rw [leftChart_source]; simpa [inv_mul_cancel] using h1
  chart_mem_atlas g := ⟨g, rfl⟩

/- ### Hypotheses -/

/-- **Hypothesis 1 (Gleason's Canonical Coordinates of the First Kind)**:
every connected Hausdorff locally Euclidean topological group `H : Type` with no small subgroups
admits a local homeomorphism `φ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin d))` around `1`
(`1 ∈ φ.source`, `φ 1 = 0`, `Metric.ball 0 r ⊆ φ.target`) whose inverse turns radial lines into
local one-parameter subgroups (`φ.symm ((s + t) • v) = φ.symm (s • v) * φ.symm (t • v)` whenever
`s • v, t • v, (s + t) • v ∈ Metric.ball 0 r`). -/
def H1 : Prop :=
  ∀ (n : ℕ) (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [ConnectedSpace H] [ChartedSpace (EuclideanSpace ℝ (Fin n)) H],
    (∃ U : Set H, U ∈ 𝓝 (1 : H) ∧ ∀ K : Subgroup H, (K : Set H) ⊆ U → K = ⊥) →
    ∃ (d : ℕ) (φ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin d))) (r : ℝ),
      0 < r ∧ (1 : H) ∈ φ.source ∧ φ 1 = 0 ∧ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r ⊆ φ.target ∧
      ∀ (v : EuclideanSpace ℝ (Fin d)) (s t : ℝ),
        s • v ∈ Metric.ball 0 r → t • v ∈ Metric.ball 0 r → (s + t) • v ∈ Metric.ball 0 r →
        φ.symm ((s + t) • v) = φ.symm (s • v) * φ.symm (t • v)

/-- **Hypothesis 2 (Baker–Campbell–Hausdorff Real Analyticity of Canonical Coordinates)**:
whenever a connected Hausdorff topological group `H : Type` admits canonical coordinates of the
first kind `φ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin d))` on `Metric.ball 0 r`, there exists
`r₀ ∈ (0, r]` such that for all `u, v ∈ Metric.ball 0 r₀`, `φ.symm u * φ.symm v ∈ φ.source` and
`φ (φ.symm u * φ.symm v) ∈ Metric.ball 0 r`, and the local group law
`(u, v) ↦ φ (φ.symm u * φ.symm v)` is real-analytic (`ContDiffOn ℝ ω`) on
`Metric.ball 0 r₀ ×ˢ Metric.ball 0 r₀`. -/
def H2 : Prop :=
  ∀ (d : ℕ) (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [ConnectedSpace H] (φ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin d))) (r : ℝ),
    0 < r → (1 : H) ∈ φ.source → φ 1 = 0 → Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r ⊆ φ.target →
    (∀ (v : EuclideanSpace ℝ (Fin d)) (s t : ℝ),
      s • v ∈ Metric.ball 0 r → t • v ∈ Metric.ball 0 r → (s + t) • v ∈ Metric.ball 0 r →
      φ.symm ((s + t) • v) = φ.symm (s • v) * φ.symm (t • v)) →
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ r ∧
      (∀ u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r₀,
        ∀ v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r₀,
          φ.symm u * φ.symm v ∈ φ.source ∧ φ (φ.symm u * φ.symm v) ∈ Metric.ball 0 r) ∧
      ContDiffOn ℝ ω
        (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => φ (φ.symm p.1 * φ.symm p.2))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r₀ ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r₀)

/-- **Hypothesis 3 (Brouwer's Invariance of Dimension)**:
if a nonempty Hausdorff topological space `H : Type` has `ChartedSpace (EuclideanSpace ℝ (Fin n)) H`
and admits a `OpenPartialHomeomorph` to `EuclideanSpace ℝ (Fin d)` with nonempty source, then `d = n`. -/
def H3 : Prop :=
  ∀ (n d : ℕ) (H : Type) [TopologicalSpace H] [T2Space H] [Nonempty H]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) H]
    (φ : OpenPartialHomeomorph H (EuclideanSpace ℝ (Fin d))),
    φ.source.Nonempty → d = n

/- ### Main Reduction Theorem (Lie's Globalization Theorem) -/

theorem main : H1 → H2 → H3 → OMA.R_Hilbert5_hilbert_fifth_problem_R1.H2 := by
  intro hGleason hBCH hBrouwer
  dsimp only [OMA.R_Hilbert5_hilbert_fifth_problem_R1.H2]
  intro n H _ _ _ _ _ instCS₀ hNSS
  -- Step 1: Obtain canonical coordinates `φ` of dimension `d`, then identify `d = n` by Brouwer
  obtain ⟨d, φ, r, hr_pos, h1_src, hφ1, hball_sub, h1param⟩ := @hGleason n H _ _ _ _ _ instCS₀ hNSS
  have hd_eq_n : d = n := @hBrouwer n d H _ _ _ instCS₀ φ ⟨1, h1_src⟩
  subst d
  clear instCS₀
  -- Step 2: Obtain real-analyticity radius `r₀ ∈ (0, r]` from `H2`
  obtain ⟨r₀, hr₀_pos, hr₀_le, hmul_in, hF_anal⟩ := hBCH n H φ r hr_pos h1_src hφ1 hball_sub h1param
  set E := EuclideanSpace ℝ (Fin n)
  let F : E × E → E := fun p => φ (φ.symm p.1 * φ.symm p.2)
  have hsymm0 : φ.symm 0 = 1 := by rw [← hφ1, φ.left_inv h1_src]
  have hsymm_neg : ∀ u ∈ Metric.ball (0 : E) r, φ.symm (-u) = (φ.symm u)⁻¹ := by
    intro u hu
    have hneg_mem : (-1 : ℝ) • u ∈ Metric.ball (0 : E) r := by simpa using hu
    have hpos_mem : (1 : ℝ) • u ∈ Metric.ball (0 : E) r := by simpa using hu
    have h0_mem : ((-1 : ℝ) + 1) • u ∈ Metric.ball (0 : E) r := by
      simp [Metric.mem_ball_self hr_pos]
    have hmul := h1param u (-1) 1 hneg_mem hpos_mem h0_mem
    have h1 : φ.symm (-u) * φ.symm u = 1 := by
      simpa [hsymm0] using hmul.symm
    exact eq_inv_of_mul_eq_one_left h1
  have hF_00 : F (0, 0) = 0 := by
    dsimp [F]; rw [hsymm0, mul_one, hφ1]
  have hF_0_right : ∀ u ∈ Metric.ball (0 : E) r, F (u, 0) = u := fun u hu => by
    dsimp [F]; rw [hsymm0, mul_one, φ.right_inv (hball_sub hu)]
  have hF_0_left : ∀ u ∈ Metric.ball (0 : E) r, F (0, u) = u := fun u hu => by
    dsimp [F]; rw [hsymm0, one_mul, φ.right_inv (hball_sub hu)]
  have hF_neg_self : ∀ u ∈ Metric.ball (0 : E) r, F (-u, u) = 0 := fun u hu => by
    dsimp [F]; rw [hsymm_neg u hu, inv_mul_cancel, hφ1]
  have hF_contAt_00 : ContinuousAt F (0, 0) :=
    (hF_anal.continuousOn).continuousAt
      ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds ⟨Metric.mem_ball_self hr₀_pos, Metric.mem_ball_self hr₀_pos⟩)
  -- Step 3: Shrink `r₁ ∈ (0, r₀]` so `F (B(0, r₁) × B(0, r₁)) ⊆ B(0, r₀)`
  have hmem_pre : F ⁻¹' Metric.ball (0 : E) r₀ ∈ 𝓝 ((0 : E), (0 : E)) :=
    hF_contAt_00.preimage_mem_nhds (by rw [hF_00]; exact Metric.ball_mem_nhds 0 hr₀_pos)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hmem_pre
  obtain ⟨s₁, hs₁, s₂, hs₂, hs_sub⟩ := hmem_pre
  obtain ⟨δ₁, hδ₁, hB₁⟩ := Metric.mem_nhds_iff.mp hs₁
  obtain ⟨δ₂, hδ₂, hB₂⟩ := Metric.mem_nhds_iff.mp hs₂
  set r₁ : ℝ := min r₀ (min δ₁ δ₂)
  have hr₁_pos : 0 < r₁ := lt_min hr₀_pos (lt_min hδ₁ hδ₂)
  have hr₁_le_r₀ : r₁ ≤ r₀ := min_le_left _ _
  have hr₁_le_r : r₁ ≤ r := hr₁_le_r₀.trans hr₀_le
  have hF_r₁_in_r₀ : ∀ u ∈ Metric.ball (0 : E) r₁, ∀ v ∈ Metric.ball (0 : E) r₁,
      F (u, v) ∈ Metric.ball (0 : E) r₀ := by
    intro u hu v hv
    have hu1 : u ∈ s₁ := hB₁ (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hu)
    have hv2 : v ∈ s₂ := hB₂ (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _)) hv)
    exact hs_sub ⟨hu1, hv2⟩
  have hF_analAt : ∀ u ∈ Metric.ball (0 : E) r₀, ∀ v ∈ Metric.ball (0 : E) r₀,
      ContDiffAt ℝ ω F (u, v) := fun u hu v hv =>
    hF_anal.contDiffAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds ⟨hu, hv⟩)
  -- Step 4: Build the restricted base chart `e₀` on `B(0, r₁)` and global left-translated `ChartedSpace`
  let e₀ : OpenPartialHomeomorph H E := restrictBall φ r₁
  have he₀_target : e₀.target = Metric.ball (0 : E) r₁ := by
    ext y
    simp only [e₀, restrictBall, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.ofSet_target,
      mem_inter_iff, mem_preimage]
    change (y ∈ Metric.ball (0 : E) r₁ ∧ y ∈ φ.target) ↔ y ∈ Metric.ball (0 : E) r₁
    exact ⟨fun h => h.1, fun hy => ⟨hy, hball_sub (Metric.ball_subset_ball hr₁_le_r hy)⟩⟩
  have h1_e₀ : (1 : H) ∈ e₀.source := by
    simp only [e₀, restrictBall, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.ofSet_source,
      mem_inter_iff, mem_preimage, hφ1]
    exact ⟨h1_src, Metric.mem_ball_self hr₁_pos⟩
  have he₀_apply : ∀ x, e₀ x = φ x := fun _ => rfl
  have he₀_symm : ∀ u, e₀.symm u = φ.symm u := fun _ => rfl
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) H := leftChartedSpace e₀ h1_e₀
  -- Step 5: Prove `IsManifold (𝓡 n) ω H` via local chart transition `F(v₀, F(-u₀, u))`
  have hManH : IsManifold (𝓡 n) ω H := by
    refine isManifold_of_contDiffOn (𝓡 n) ω H fun e₁ e₂ he₁ he₂ => ?_
    obtain ⟨g, rfl⟩ := he₁
    obtain ⟨h, rfl⟩ := he₂
    simp only [modelWithCornersSelf_coe, Function.comp_id, Function.id_comp,
      modelWithCornersSelf_coe_symm, Set.preimage_id, Set.range_id, Set.inter_univ]
    intro u₀ hu₀
    have hu₀_t1 : u₀ ∈ (leftChart e₀ g).target := hu₀.1
    rw [leftChart_target, he₀_target] at hu₀_t1
    have hx₀_s2 : (leftChart e₀ g).symm u₀ ∈ (leftChart e₀ h).source := hu₀.2
    have hv₀_mem : leftChart e₀ h ((leftChart e₀ g).symm u₀) ∈ Metric.ball (0 : E) r₁ := by
      have := (leftChart e₀ h).map_source hx₀_s2
      rwa [leftChart_target, he₀_target] at this
    set v₀ : E := leftChart e₀ h ((leftChart e₀ g).symm u₀)
    have hgh_eq : h⁻¹ * (g * φ.symm u₀) = φ.symm v₀ := by
      have hleft := (leftChart e₀ h).left_inv hx₀_s2
      have h1 : h * φ.symm v₀ = g * φ.symm u₀ := by
        simpa [v₀, leftChart_symm_apply, he₀_symm] using hleft
      calc h⁻¹ * (g * φ.symm u₀) = h⁻¹ * (h * φ.symm v₀) := by rw [h1]
        _ = φ.symm v₀ := by group
    -- Define the real-analytic local transition `T(u) = F(v₀, F(-u₀, u))` near `u₀`
    let T : E → E := fun u => F (v₀, F (-u₀, u))
    have hnu₀_r₀ : -u₀ ∈ Metric.ball (0 : E) r₀ := by
      simpa using Metric.ball_subset_ball hr₁_le_r₀ hu₀_t1
    have hu₀_r₀ : u₀ ∈ Metric.ball (0 : E) r₀ := Metric.ball_subset_ball hr₁_le_r₀ hu₀_t1
    have hv₀_r₀ : v₀ ∈ Metric.ball (0 : E) r₀ := Metric.ball_subset_ball hr₁_le_r₀ hv₀_mem
    have hδ_anal : ContDiffAt ℝ ω (fun u : E => F (-u₀, u)) u₀ :=
      ContDiffAt.comp (g := F) (f := fun u : E => (-u₀, u)) u₀
        (hF_analAt (-u₀) hnu₀_r₀ u₀ hu₀_r₀) (contDiffAt_const.prodMk contDiffAt_id)
    have hδ_val : F (-u₀, u₀) = 0 := hF_neg_self u₀ (Metric.ball_subset_ball hr₁_le_r hu₀_t1)
    have hT_anal : ContDiffAt ℝ ω T u₀ := by
      have h0_r₀ : F (-u₀, u₀) ∈ Metric.ball (0 : E) r₀ := by
        rw [hδ_val]; exact Metric.mem_ball_self hr₀_pos
      exact ContDiffAt.comp (g := F) (f := fun u : E => (v₀, F (-u₀, u))) u₀
        (hF_analAt v₀ hv₀_r₀ (F (-u₀, u₀)) h0_r₀) (contDiffAt_const.prodMk hδ_anal)
    -- Show `T u = (leftChart e₀ h ∘ (leftChart e₀ g).symm) u` on a neighborhood of `u₀`
    have hδ_near : ∀ᶠ u in 𝓝 u₀, F (-u₀, u) ∈ Metric.ball (0 : E) r₁ :=
      hδ_anal.continuousAt.preimage_mem_nhds (by rw [hδ_val]; exact Metric.ball_mem_nhds 0 hr₁_pos)
    have hu_near : ∀ᶠ u in 𝓝 u₀, u ∈ Metric.ball (0 : E) r₁ :=
      Metric.isOpen_ball.mem_nhds hu₀_t1
    have heq_ev : (fun u => leftChart e₀ h ((leftChart e₀ g).symm u)) =ᶠ[𝓝 u₀] T := by
      filter_upwards [hδ_near, hu_near] with u hδu hu1
      have hu_r₀ : u ∈ Metric.ball (0 : E) r₀ := Metric.ball_subset_ball hr₁_le_r₀ hu1
      have hmul1 := hmul_in (-u₀) hnu₀_r₀ u hu_r₀
      have hφ_inv1 : φ.symm (F (-u₀, u)) = (φ.symm u₀)⁻¹ * φ.symm u := by
        dsimp [F]
        rw [φ.left_inv hmul1.1, hsymm_neg u₀ (Metric.ball_subset_ball hr₁_le_r hu₀_t1)]
      have hprod_eq : h⁻¹ * (g * φ.symm u) = φ.symm v₀ * φ.symm (F (-u₀, u)) := by
        rw [hφ_inv1]
        calc h⁻¹ * (g * φ.symm u) = (h⁻¹ * (g * φ.symm u₀)) * ((φ.symm u₀)⁻¹ * φ.symm u) := by group
          _ = φ.symm v₀ * ((φ.symm u₀)⁻¹ * φ.symm u) := by rw [hgh_eq]
      dsimp only [T, F]
      rw [leftChart_apply, leftChart_symm_apply, he₀_apply, he₀_symm, hprod_eq]
    exact (hT_anal.congr_of_eventuallyEq heq_ev).contDiffWithinAt
  -- Step 6: Prove conjugation `u ↦ φ (w⁻¹ * φ.symm u * w)` is real-analytic at `0` for all `w : H`
  let conjFn : H → E → E := fun w u => φ (w⁻¹ * φ.symm u * w)
  have hconj_zero : ∀ w : H, conjFn w 0 = 0 := fun w => by
    dsimp [conjFn]; rw [hsymm0, mul_one, inv_mul_cancel, hφ1]
  have hconj_ball : ∀ z ∈ Metric.ball (0 : E) r₁,
      ContDiffAt ℝ ω (conjFn (φ.symm z)) 0 := by
    intro z hz
    have hz_r₀ : z ∈ Metric.ball (0 : E) r₀ := Metric.ball_subset_ball hr₁_le_r₀ hz
    have hnz_r₀ : -z ∈ Metric.ball (0 : E) r₀ := by simpa using hz_r₀
    have h0_r₀ : (0 : E) ∈ Metric.ball (0 : E) r₀ := Metric.mem_ball_self hr₀_pos
    have hFuz_anal : ContDiffAt ℝ ω (fun u : E => F (u, z)) 0 :=
      ContDiffAt.comp (g := F) (f := fun u : E => (u, z)) 0
        (hF_analAt 0 h0_r₀ z hz_r₀) (contDiffAt_id.prodMk contDiffAt_const)
    have hFuz_val : F (0, z) = z := hF_0_left z (Metric.ball_subset_ball hr₁_le_r hz)
    have hcomp_anal : ContDiffAt ℝ ω (fun u : E => F (-z, F (u, z))) 0 :=
      ContDiffAt.comp (g := F) (f := fun u : E => (-z, F (u, z))) 0
        (hF_analAt (-z) hnz_r₀ (F (0, z)) (by rwa [hFuz_val])) (contDiffAt_const.prodMk hFuz_anal)
    have hu_ev : ∀ᶠ u in 𝓝 (0 : E), u ∈ Metric.ball (0 : E) r₀ :=
      Metric.ball_mem_nhds 0 hr₀_pos
    have hFuz_ev : ∀ᶠ u in 𝓝 (0 : E), F (u, z) ∈ Metric.ball (0 : E) r₀ :=
      hFuz_anal.continuousAt.preimage_mem_nhds (by rw [hFuz_val]; exact Metric.isOpen_ball.mem_nhds hz_r₀)
    have heq_ev : conjFn (φ.symm z) =ᶠ[𝓝 (0 : E)] fun u => F (-z, F (u, z)) := by
      filter_upwards [hu_ev, hFuz_ev] with u hu _
      have hmul1 := hmul_in u hu z hz_r₀
      dsimp [conjFn, F]
      rw [φ.left_inv hmul1.1, hsymm_neg z (Metric.ball_subset_ball hr₁_le_r hz), mul_assoc]
    exact hcomp_anal.congr_of_eventuallyEq heq_ev
  have hconj_comp : ∀ w₁ w₂ : H, ContDiffAt ℝ ω (conjFn w₁) 0 → ContDiffAt ℝ ω (conjFn w₂) 0 →
      ContDiffAt ℝ ω (conjFn (w₁ * w₂)) 0 := by
    intro w₁ w₂ h1 h2
    have hcomp : ContDiffAt ℝ ω (conjFn w₂ ∘ conjFn w₁) 0 := by
      refine ContDiffAt.comp 0 ?_ h1
      rw [hconj_zero w₁]; exact h2
    have hev1 : ∀ᶠ u in 𝓝 (0 : E), w₁⁻¹ * φ.symm u * w₁ ∈ φ.source := by
      have hcont : ContinuousAt (fun u : E => w₁⁻¹ * φ.symm u * w₁) 0 :=
        ((continuousAt_const.mul (φ.continuousOn_invFun.continuousAt
          (Filter.mem_of_superset (Metric.ball_mem_nhds 0 hr_pos) hball_sub))).mul continuousAt_const)
      refine hcont.preimage_mem_nhds ?_
      rw [hsymm0, mul_one, inv_mul_cancel]
      exact φ.open_source.mem_nhds h1_src
    have heq : conjFn (w₁ * w₂) =ᶠ[𝓝 (0 : E)] (conjFn w₂ ∘ conjFn w₁) := by
      filter_upwards [hev1] with u hu
      dsimp [conjFn, Function.comp]
      rw [φ.left_inv hu]
      congr 1; group
    exact hcomp.congr_of_eventuallyEq heq
  let S_conj : Subgroup H :=
    { carrier := {w : H | ContDiffAt ℝ ω (conjFn w) 0 ∧ ContDiffAt ℝ ω (conjFn w⁻¹) 0}
      mul_mem' := fun {a b} ha hb =>
        ⟨hconj_comp a b ha.1 hb.1, by rw [mul_inv_rev]; exact hconj_comp b⁻¹ a⁻¹ hb.2 ha.2⟩
      one_mem' := by
        have hid : conjFn 1 =ᶠ[𝓝 (0 : E)] id := by
          filter_upwards [Metric.ball_mem_nhds 0 hr_pos] with u hu
          dsimp [conjFn]; rw [inv_one, one_mul, mul_one, φ.right_inv (hball_sub hu)]
        have hcd : ContDiffAt ℝ ω (conjFn 1) 0 := contDiffAt_id.congr_of_eventuallyEq hid
        exact ⟨hcd, by simpa using hcd⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by simpa using ha.1⟩ }
  have hS_sub : e₀.source ⊆ (S_conj : Set H) := by
    intro w hw
    have hw_t : e₀ w ∈ Metric.ball (0 : E) r₁ := by
      have := e₀.map_source hw; rwa [he₀_target] at this
    have hw_eq : φ.symm (e₀ w) = w := e₀.left_inv hw
    have hnw_t : -e₀ w ∈ Metric.ball (0 : E) r₁ := by simpa using hw_t
    have hwinv_eq : φ.symm (-e₀ w) = w⁻¹ := by
      rw [hsymm_neg (e₀ w) (Metric.ball_subset_ball hr₁_le_r hw_t), hw_eq]
    exact ⟨hw_eq ▸ hconj_ball (e₀ w) hw_t, hwinv_eq ▸ hconj_ball (-e₀ w) hnw_t⟩
  have hS_open : IsOpen (S_conj : Set H) :=
    Subgroup.isOpen_of_mem_nhds S_conj (Filter.mem_of_superset (e₀.open_source.mem_nhds h1_e₀) hS_sub)
  have hS_top : S_conj = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hclopen : IsClopen (S_conj : Set H) := ⟨S_conj.isClosed_of_isOpen hS_open, hS_open⟩
    have huniv : (S_conj : Set H) = Set.univ := hclopen.eq_univ ⟨1, S_conj.one_mem⟩
    rw [← SetLike.mem_coe, huniv]; trivial
  have hconj_anal : ∀ w : H, ContDiffAt ℝ ω (conjFn w) 0 := fun w =>
    (show w ∈ S_conj by rw [hS_top]; trivial).1
  -- Step 7: Prove `LieGroup (𝓡 n) ω H` (`contMDiff_mul` and `contMDiff_inv`)
  have hLieH : LieGroup (𝓡 n) ω H := by
    refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
    · intro ⟨g, h⟩
      rw [contMDiffAt_iff]
      refine ⟨continuous_mul.continuousAt, ?_⟩
      have hrange : Set.range ((𝓡 n).prod (𝓡 n)) = Set.univ :=
        Set.range_eq_univ.mpr fun p => ⟨p, rfl⟩
      rw [hrange, contDiffWithinAt_univ]
      have h0_g : leftChart e₀ g g = 0 := by
        rw [leftChart_apply, inv_mul_cancel]; exact hφ1
      have h0_h : leftChart e₀ h h = 0 := by
        rw [leftChart_apply, inv_mul_cancel]; exact hφ1
      have hpt : extChartAt ((𝓡 n).prod (𝓡 n)) (g, h) (g, h) = ((0 : E), (0 : E)) := by
        change (leftChart e₀ g g, leftChart e₀ h h) = (0, 0)
        rw [h0_g, h0_h]
      rw [hpt]
      let G : E × E → E := fun p => F (conjFn h p.1, p.2)
      have hG_anal : ContDiffAt ℝ ω G (0, 0) := by
        have h0_r₀ : (0 : E) ∈ Metric.ball (0 : E) r₀ := Metric.mem_ball_self hr₀_pos
        have hch : ContDiffAt ℝ ω (fun p : E × E => conjFn h p.1) (0, 0) :=
          ContDiffAt.comp (g := conjFn h) (f := Prod.fst) (0, 0) (hconj_anal h) contDiffAt_fst
        have hp_at : ContDiffAt ℝ ω (fun p : E × E => (conjFn h p.1, p.2)) (0, 0) :=
          hch.prodMk contDiffAt_snd
        have hF00 : ContDiffAt ℝ ω F (conjFn h 0, (0 : E)) := by
          rw [hconj_zero h]; exact hF_analAt 0 h0_r₀ 0 h0_r₀
        exact ContDiffAt.comp (g := F) (f := fun p : E × E => (conjFn h p.1, p.2)) (0, 0) hF00 hp_at
      have hev : (extChartAt (𝓡 n) (g * h) ∘ (fun p : H × H => p.1 * p.2) ∘
          (extChartAt ((𝓡 n).prod (𝓡 n)) (g, h)).symm) =ᶠ[𝓝 ((0 : E), (0 : E))] G := by
        have hev1 : ∀ᶠ p : E × E in 𝓝 ((0 : E), (0 : E)), h⁻¹ * φ.symm p.1 * h ∈ φ.source := by
          have hinv0 : ContinuousAt (fun u : E => φ.symm u) (0 : E) :=
            φ.continuousOn_invFun.continuousAt
              (Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) hr_pos) hball_sub)
          have hcomp0 : ContinuousAt (fun p : E × E => φ.symm p.1) (0, 0) :=
            ContinuousAt.comp (g := fun u : E => φ.symm u) (f := Prod.fst) hinv0 continuousAt_fst
          have hcont : ContinuousAt (fun p : E × E => h⁻¹ * φ.symm p.1 * h) (0, 0) :=
            (continuousAt_const.mul hcomp0).mul continuousAt_const
          refine hcont.preimage_mem_nhds ?_
          rw [hsymm0, mul_one, inv_mul_cancel]
          exact φ.open_source.mem_nhds h1_src
        filter_upwards [hev1] with p hp
        change leftChart e₀ (g * h) ((leftChart e₀ g).symm p.1 * (leftChart e₀ h).symm p.2) = G p
        dsimp [G, F, conjFn]
        rw [leftChart_apply, leftChart_symm_apply, leftChart_symm_apply, he₀_apply, he₀_symm,
          he₀_symm, φ.left_inv hp]
        congr 1; group
      exact hG_anal.congr_of_eventuallyEq hev
    · intro g
      rw [contMDiffAt_iff]
      refine ⟨continuous_inv.continuousAt, ?_⟩
      have hrange : Set.range (𝓡 n) = Set.univ := Set.range_eq_univ.mpr fun u => ⟨u, rfl⟩
      rw [hrange, contDiffWithinAt_univ]
      have h0_g : leftChart e₀ g g = 0 := by
        rw [leftChart_apply, inv_mul_cancel]; exact hφ1
      have hpt : extChartAt (𝓡 n) g g = (0 : E) := by
        change leftChart e₀ g g = 0; exact h0_g
      rw [hpt]
      have hI_anal : ContDiffAt ℝ ω (fun u : E => conjFn g⁻¹ (-u)) 0 := by
        have hcg : ContDiffAt ℝ ω (conjFn g⁻¹) (-(0 : E)) := by
          rw [neg_zero]; exact hconj_anal g⁻¹
        exact hcg.comp 0 contDiffAt_id.neg
      have hev : (extChartAt (𝓡 n) g⁻¹ ∘ (fun x : H => x⁻¹) ∘ (extChartAt (𝓡 n) g).symm) =ᶠ[𝓝 (0 : E)]
          fun u => conjFn g⁻¹ (-u) := by
        filter_upwards [Metric.ball_mem_nhds 0 hr_pos] with u hu
        change leftChart e₀ g⁻¹ ((leftChart e₀ g).symm u)⁻¹ = conjFn g⁻¹ (-u)
        dsimp [conjFn]
        rw [leftChart_apply, leftChart_symm_apply, he₀_apply, he₀_symm, hsymm_neg u hu, inv_inv]
        congr 1; group
      exact hI_anal.congr_of_eventuallyEq hev
  -- Step 8: Package the `LieGroupPresentation H n`
  exact ⟨{ carrier := H, equiv := ContinuousMulEquiv.refl H }⟩

end OMA.R_Hilbert5_hilbert_fifth_problem_R1_H2_R1
