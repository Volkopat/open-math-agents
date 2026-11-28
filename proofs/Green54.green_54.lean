import FormalConjectures.GreensOpenProblems.«54»

/-!
# Ben Green's Open Problem 54 (Talagrand's convexity conjecture)

Let `K ⊆ ℝ^ℕ` be a balanced compact set with `γ_∞(K) ≥ 0.99`.  Problem 54 of Ben Green's list
(M. Talagrand's convexity problem) asks whether the ten-fold sumset `10 K` contains a compact convex
set of Gaussian measure at least `0.01`.  This was answered affirmatively by

* D. Hua, A. Song, S. Tudose, *On Talagrand's convexity conjecture*, arXiv:2605.10908 (2026),

who prove that every random vector dominated in the convex order by a standard Gaussian vector is a
sum of three standard Gaussian vectors (the *Three Gaussians theorem*), and deduce (by an argument
of M. Talagrand based on the Hahn–Banach theorem) that `3 (A + A + A)` contains a convex set of
large Gaussian measure whenever `γₙ(A)` is large, uniformly in the dimension.

## Proof

The theorem `OMA.solution` uses a discrete Gaussian bridge to prove `G54.TwoGaussians`.
For a convex Lipschitz potential, Prékopa–Leindler gives log-concavity of its Gaussian convolution.
The conditional endpoint mean is nonexpansive. Along a finite time grid its increments telescope
to the centered endpoint. Split each increment equally between two sums, adding an independent
Gaussian correction with opposite signs. Each sum has the prescribed conditional covariance.
A third-moment estimate controls the characteristic functions, and a weak limit gives a coupling
of two standard Gaussian vectors with the exact required sum law.

The proof then applies the following finite-dimensional reductions and compactness arguments.

1. **Entropic martingale coupling** (Hua–Song–Tudose, Proposition 3.2, direct part;
   `G54.softmax_max`, `G54.softmax_stationary`, `G54.gauss_slack`, `G54.gauss_R_pos`,
   `G54.exists_softmax_gauss`).  For a finitely supported law `∑ pᵢ δ_{xᵢ}` dominated by `γₙ` in
   the convex order and `ε ∈ (0, 1]`, the concave functional
   `g(θ) = ∑ᵢ pᵢ ⟨θᵢ, (1, (1-ε) xᵢ)⟩ - ∫ log ∑ⱼ pⱼ exp ⟨θⱼ, (1, y)⟩ dγₙ(y)`
   is coercive modulo its gauge symmetry (this uses the slack `ε` and the full support of `γₙ`),
   hence has a maximiser; its first-order conditions say that the softmax weights
   `wᵢ = pᵢ e^{⟨θᵢ,(1,y)⟩} / ∑ⱼ pⱼ e^{⟨θⱼ,(1,y)⟩}` define a martingale coupling of the contracted
   atoms with `γₙ` whose conditional laws `e^{-ψᵢ} γₙ` have convex smooth potentials `ψᵢ`.
2. **Discretisation** (Lemma 3.1 there; `G54.exists_discretization`) of compactly supported laws
   by barycentres of the cells of a cubical partition (Jensen's inequality).
3. **Three Gaussians, in the form of a landing property** (`G54.atoms_landing`,
   `G54.landing_of_twoGaussians`): a compactly supported law dominated by `γₙ` in the convex order
   gives mass `≥ 0.97` to `A + A + A` for every balanced compact `A` with `γₙ(A) ≥ 0.99` (union
   bound for `X = G - G₁ - G₂`).
4. **Talagrand's Hahn–Banach argument** (Section 5 there, due to M. Talagrand;
   `G54.exists_measure_of_separation`, `G54.scaled_dom`, `G54.convex_dom_of_nonneg`,
   `G54.half_le_cylinder`), run directly in `ℝ^ℕ` on
   the compact box spanned by `K`, with the geometric Hahn–Banach theorem and the
   Riesz–Markov–Kakutani theorem from Mathlib.
5. **Passage to the compact set `3 (K + K + K) ⊆ 10 K`** by a Blaschke-type selection principle for
   convex sets (`G54.exists_convex_limit`, Kuratowski limits along an ultrafilter), and the transfer
   between `ℝ^ℕ` and its finite-dimensional marginals (`G54.half_le_T`, `G54.green54_of_landing`).

The file also provides the conditional reductions `G54.green54_of_threeGaussians` (from the
Three Gaussians theorem `G54.ThreeGaussians`, Theorem 1.1 of Hua–Song–Tudose) and
`G54.green54_of_twoGaussians` (from `G54.TwoGaussians`, their Corollary 2.6).

## References

* M. Talagrand, *Are all sets of positive measure essentially convex?*, Operator Theory: Advances
  and Applications 77 (1995), 295–310.
* M. Talagrand, *My favorite problems* (2026), https://michel.talagrand.net/Korea15.pdf
* B. Green, *100 open problems*, Problem 54.
* D. Hua, A. Song, S. Tudose, *On Talagrand's convexity conjecture*, arXiv:2605.10908 (2026).
* A. Song, *Sum of Gaussian vectors and large sets*, arXiv:2602.22342 (2026).
* L. A. Caffarelli, Comm. Math. Phys. 214 (2000), 547–563.
-/


section ModLim

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- **A Blaschke-type selection principle.**  Let `T` be a compact subset of a Hausdorff
topological vector space, `B` a compact set and `γ` an outer regular measure.  If every open
neighbourhood `U` of `T` contains a convex subset of `B` of measure at least `c`, then `T` itself
contains a compact convex set of measure at least `c`.

The limit set is the Kuratowski limit of the approximating convex sets along an ultrafilter on the
neighbourhoods of `T`. -/
theorem G54.exists_convex_limit {X : Type*} [TopologicalSpace X] [T2Space X] [AddCommGroup X]
    [Module ℝ X] [ContinuousAdd X] [ContinuousSMul ℝ X] [MeasurableSpace X]
    (γ : Measure X) [γ.OuterRegular] {B T : Set X} (hB : IsCompact B) (hT : IsCompact T)
    (c : ℝ≥0∞)
    (h : ∀ U : Set X, IsOpen U → T ⊆ U →
      ∃ C : Set X, C ⊆ U ∧ C ⊆ B ∧ Convex ℝ C ∧ c ≤ γ C) :
    ∃ C : Set X, IsCompact C ∧ Convex ℝ C ∧ C ⊆ T ∧ c ≤ γ C := by
  classical
  have h' : ∀ U : Set X, U ∈ 𝓝ˢ T → ∃ C : Set X, C ⊆ U ∧ C ⊆ B ∧ Convex ℝ C ∧ c ≤ γ C := by
    intro U hU
    obtain ⟨V, hVo, hTV, hVU⟩ := mem_nhdsSet_iff_exists.mp hU
    obtain ⟨C, hCV, hCB, hCc, hCm⟩ := h V hVo hTV
    exact ⟨C, hCV.trans hVU, hCB, hCc, hCm⟩
  choose! C hCU hCB hCc hCm using h'
  -- the index filter: small neighbourhoods of `T`
  set S : Set (Set X) := {U | U ∈ 𝓝ˢ T} with hSdef
  set F : Filter (Set X) := (𝓝ˢ T).smallSets ⊓ 𝓟 S with hFdef
  have : F.NeBot := by
    rw [hFdef, ← frequently_mem_iff_neBot, frequently_smallSets]
    intro t ht
    exact ⟨t, Subset.rfl, ht⟩
  set 𝒰 : Ultrafilter (Set X) := Ultrafilter.of F with h𝒰def
  have h𝒰F : (𝒰 : Filter (Set X)) ≤ F := Ultrafilter.of_le F
  have hS : S ∈ (𝒰 : Filter (Set X)) := h𝒰F (mem_inf_of_right (mem_principal_self S))
  have hsmall : ∀ t ∈ 𝓝ˢ T, {U : Set X | U ⊆ t} ∈ (𝒰 : Filter (Set X)) := by
    intro t ht
    exact h𝒰F (mem_inf_of_left (eventually_smallSets_subset.2 ht))
  set L : Set X := {x | ∀ W ∈ 𝓝 x, {U : Set X | (C U ∩ W).Nonempty} ∈ (𝒰 : Filter (Set X))}
    with hLdef
  have hBcl : IsClosed B := hB.isClosed
  have hTcl : IsClosed T := hT.isClosed
  -- `L ⊆ B`
  have hLB : L ⊆ B := by
    intro x hx
    by_contra hxB
    have h1 := hx Bᶜ (hBcl.isOpen_compl.mem_nhds hxB)
    obtain ⟨U, hU1, hU2⟩ := (𝒰 : Filter (Set X)).nonempty_of_mem (inter_mem h1 hS)
    obtain ⟨y, hyC, hyB⟩ := hU1
    exact hyB (hCB U hU2 hyC)
  -- `L` is closed
  have hLcl : IsClosed L := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hx' : ∃ W ∈ 𝓝 x, {U : Set X | (C U ∩ W).Nonempty} ∉ (𝒰 : Filter (Set X)) := by
      by_contra hcon
      apply hx
      intro W hW
      by_contra hW2
      exact hcon ⟨W, hW, hW2⟩
    obtain ⟨W, hW, hWU⟩ := hx'
    obtain ⟨W', hW'W, hW'o, hxW'⟩ := mem_nhds_iff.mp hW
    refine mem_of_superset (hW'o.mem_nhds hxW') ?_
    intro y hy hyL
    apply hWU
    refine mem_of_superset (hyL W' (hW'o.mem_nhds hy)) ?_
    rintro U ⟨z, hzC, hzW⟩
    exact ⟨z, hzC, hW'W hzW⟩
  -- `L ⊆ T`
  have hLT : L ⊆ T := by
    intro x hx
    by_contra hxT
    have hdisj : Disjoint T {x} := by
      rw [disjoint_singleton_right]; exact hxT
    obtain ⟨U₀, W, hU₀o, hWo, hTU₀, hxW, hUW⟩ :=
      SeparatedNhds.of_isCompact_isCompact hT isCompact_singleton hdisj
    have hxW' : x ∈ W := hxW (mem_singleton x)
    have h1 := hx W (hWo.mem_nhds hxW')
    have h2 := hsmall U₀ (hU₀o.mem_nhdsSet.mpr hTU₀)
    obtain ⟨U, ⟨hU1, hU2⟩, hU3⟩ :=
      (𝒰 : Filter (Set X)).nonempty_of_mem (inter_mem (inter_mem h1 h2) hS)
    obtain ⟨y, hyC, hyW⟩ := hU1
    have hyU₀ : y ∈ U₀ := hU2 (hCU U hU3 hyC)
    exact (disjoint_left.mp hUW) hyU₀ hyW
  -- `L` is convex
  have hLconv : Convex ℝ L := by
    intro x hx y hy a b ha hb hab W hW
    have hcont : Continuous (fun p : X × X => a • p.1 + b • p.2) := by fun_prop
    have hW' : (fun p : X × X => a • p.1 + b • p.2) ⁻¹' W ∈ 𝓝 (x, y) :=
      hcont.continuousAt.preimage_mem_nhds hW
    rw [nhds_prod_eq] at hW'
    obtain ⟨Wx, hWx, Wy, hWy, hsub⟩ := Filter.mem_prod_iff.mp hW'
    refine mem_of_superset (inter_mem (inter_mem (hx Wx hWx) (hy Wy hWy)) hS) ?_
    rintro U ⟨⟨⟨u, huC, huW⟩, ⟨v, hvC, hvW⟩⟩, hU⟩
    refine ⟨a • u + b • v, hCc U hU huC hvC ha hb hab, ?_⟩
    exact hsub (mk_mem_prod huW hvW)
  -- measure of `L`
  have hLmeas : c ≤ γ L := by
    rw [Set.measure_eq_iInf_isOpen L γ]
    refine le_iInf fun W => le_iInf fun hLW => le_iInf fun hWo => ?_
    have hkey : {U : Set X | C U ⊆ W} ∈ (𝒰 : Filter (Set X)) := by
      by_contra hcon
      have hcon' : {U : Set X | C U ⊆ W}ᶜ ∈ (𝒰 : Filter (Set X)) :=
        Ultrafilter.compl_mem_iff_notMem.mpr hcon
      have hbad := inter_mem hcon' hS
      obtain ⟨U₁, hU₁a, hU₁b⟩ := (𝒰 : Filter (Set X)).nonempty_of_mem hbad
      have hex₁ : ∃ y, y ∈ C U₁ ∧ y ∉ W := by
        have : ¬ C U₁ ⊆ W := hU₁a
        rw [not_subset] at this
        obtain ⟨y, hy1, hy2⟩ := this
        exact ⟨y, hy1, hy2⟩
      obtain ⟨x₀, hx₀C, hx₀W⟩ := hex₁
      set xf : Set X → X := fun U => if hU : ∃ y, y ∈ C U ∧ y ∉ W then hU.choose else x₀ with hxf
      have hxf_spec : ∀ U, U ∈ {U : Set X | C U ⊆ W}ᶜ ∩ S → xf U ∈ C U ∧ xf U ∉ W := by
        intro U hU
        have hex : ∃ y, y ∈ C U ∧ y ∉ W := by
          have : ¬ C U ⊆ W := hU.1
          rw [not_subset] at this
          obtain ⟨y, hy1, hy2⟩ := this
          exact ⟨y, hy1, hy2⟩
        simp only [hxf, dif_pos hex]
        exact hex.choose_spec
      have hcomp : IsCompact (B ∩ Wᶜ) := hB.inter_right hWo.isClosed_compl
      have hmap : ((𝒰.map xf : Ultrafilter X) : Filter X) ≤ 𝓟 (B ∩ Wᶜ) := by
        rw [le_principal_iff]
        change xf ⁻¹' (B ∩ Wᶜ) ∈ (𝒰 : Filter (Set X))
        refine mem_of_superset hbad ?_
        intro U hU
        obtain ⟨h1, h2⟩ := hxf_spec U hU
        exact ⟨hCB U hU.2 h1, h2⟩
      obtain ⟨x, hxBW, hxlim⟩ := hcomp.ultrafilter_le_nhds (𝒰.map xf) hmap
      have hxL : x ∈ L := by
        intro W' hW'
        have h1 : xf ⁻¹' W' ∈ (𝒰 : Filter (Set X)) := hxlim hW'
        refine mem_of_superset (inter_mem h1 hbad) ?_
        intro U hU
        obtain ⟨h2, h3⟩ := hxf_spec U hU.2
        exact ⟨xf U, h2, hU.1⟩
      exact hxBW.2 (hLW hxL)
    obtain ⟨U, hU1, hU2⟩ := (𝒰 : Filter (Set X)).nonempty_of_mem (inter_mem hkey hS)
    exact (hCm U hU2).trans (measure_mono hU1)
  exact ⟨L, hB.of_isClosed_subset hLcl hLB, hLconv, hLT, hLmeas⟩

end ModLim

section ModSep

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- **Hahn–Banach separation + Riesz–Markov–Kakutani.**  Let `Q` be a compact Hausdorff space and
`𝒞` a convex set of continuous functions containing `0` such that every `f ∈ 𝒞` takes a value
`≤ 3` somewhere.  Then there is a Borel probability measure `μ` on `Q` with `∫ f dμ ≤ 3` for all
`f ∈ 𝒞`.  (This is the functional-analytic heart of Talagrand's argument.) -/
theorem G54.exists_measure_of_separation {Q : Type*} [TopologicalSpace Q] [CompactSpace Q]
    [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    (𝒞 : Set C(Q, ℝ)) (h𝒞conv : Convex ℝ 𝒞) (h0 : (0 : C(Q, ℝ)) ∈ 𝒞)
    (h : ∀ f ∈ 𝒞, ∃ x, f x ≤ 3) :
    ∃ μ : Measure Q, IsProbabilityMeasure μ ∧ ∀ f ∈ 𝒞, ∫ x, f x ∂μ ≤ 3 := by
  classical
  obtain ⟨x₀, -⟩ := h 0 h0
  have : Nonempty Q := ⟨x₀⟩
  set s : Set C(Q, ℝ) := {g | ∀ x, 3 < g x} with hs
  have hs_conv : Convex ℝ s := by
    intro g₁ hg₁ g₂ hg₂ a b ha hb hab x
    have h1 := hg₁ x
    have h2 := hg₂ x
    have hval : (a • g₁ + b • g₂) x = a * g₁ x + b * g₂ x := by simp
    rw [hval]
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      subst hb1
      rw [← ha0]
      linarith
    · have : a * 3 < a * g₁ x := by nlinarith
      have : b * 3 ≤ b * g₂ x := by nlinarith
      nlinarith
  have hs_open : IsOpen s := by
    rw [Metric.isOpen_iff]
    intro g hg
    obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMinOn univ_nonempty g.continuous.continuousOn
    refine ⟨g x₁ - 3, sub_pos.mpr (hg x₁), ?_⟩
    intro g' hg' x
    have h1 : dist (g' x) (g x) < g x₁ - 3 :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) hg'
    have h2 : g x₁ ≤ g x := hx₁ (mem_univ x)
    rw [Real.dist_eq] at h1
    have h3 := abs_lt.mp h1
    linarith [h3.1]
  have hdisj : Disjoint s 𝒞 := by
    rw [Set.disjoint_left]
    intro g hgs hg𝒞
    obtain ⟨x, hx⟩ := h g hg𝒞
    exact absurd (hgs x) (not_lt.mpr hx)
  obtain ⟨φ, u, hφs, hφ𝒞⟩ := geometric_hahn_banach_open hs_conv hs_open h𝒞conv hdisj
  have hu : u ≤ 0 := by simpa using hφ𝒞 0 h0
  have hconst : ∀ c : ℝ, 3 < c → c * φ 1 < u := by
    intro c hc
    have hmem : (c • (1 : C(Q, ℝ))) ∈ s := by
      intro x
      simpa using hc
    have := hφs _ hmem
    simpa using this
  have hone : φ 1 < 0 := by
    have := hconst 4 (by norm_num)
    linarith
  have hpos : ∀ g : C(Q, ℝ), 0 ≤ g → φ g ≤ 0 := by
    intro g hg
    by_contra hcon
    have hcon' : 0 < φ g := not_le.mp hcon
    set t : ℝ := (-(4 * φ 1)) / φ g with ht
    have ht0 : 0 ≤ t := by
      apply div_nonneg _ hcon'.le
      linarith
    have hmem : ((4 : ℝ) • (1 : C(Q, ℝ)) + t • g) ∈ s := by
      intro x
      have hgx : 0 ≤ g x := hg x
      have hval : ((4 : ℝ) • (1 : C(Q, ℝ)) + t • g) x = 4 + t * g x := by simp
      rw [hval]
      nlinarith
    have h1 := hφs _ hmem
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    have h2 : t * φ g = -(4 * φ 1) := by
      rw [ht]; field_simp
    linarith
  -- the normalised positive functional
  set a : ℝ := (-(φ 1))⁻¹ with ha
  have ha0 : 0 < a := by rw [ha]; apply inv_pos.mpr; linarith
  let Λ : CompactlySupportedContinuousMap Q ℝ →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀
      { toFun := fun g => a * (-(φ (g : C(Q, ℝ))))
        map_add' := by
          intro g g'
          have : ((g + g' : CompactlySupportedContinuousMap Q ℝ) : C(Q, ℝ))
              = (g : C(Q, ℝ)) + (g' : C(Q, ℝ)) := by ext x; simp
          rw [this, map_add]; ring
        map_smul' := by
          intro c g
          have : ((c • g : CompactlySupportedContinuousMap Q ℝ) : C(Q, ℝ))
              = c • (g : C(Q, ℝ)) := by ext x; simp
          rw [this, map_smul]; simp only [smul_eq_mul, RingHom.id_apply]; ring }
      (by
        intro g hg
        have hg' : (0 : C(Q, ℝ)) ≤ (g : C(Q, ℝ)) := fun x => hg x
        have := hpos _ hg'
        change 0 ≤ a * (-(φ (g : C(Q, ℝ))))
        apply mul_nonneg ha0.le
        linarith)
  have hΛ : ∀ g : CompactlySupportedContinuousMap Q ℝ, Λ g = a * (-(φ (g : C(Q, ℝ)))) :=
    fun g => rfl
  set μ : Measure Q := RealRMK.rieszMeasure Λ with hμ
  have hint : ∀ f : C(Q, ℝ), ∫ x, f x ∂μ = a * (-(φ f)) := by
    intro f
    have h1 := RealRMK.integral_rieszMeasure Λ
      (CompactlySupportedContinuousMap.continuousMapEquiv f)
    rw [hΛ] at h1
    exact h1
  have hμuniv : μ univ = 1 := by
    have h1 := hint 1
    have h2 : ∫ x, (1 : C(Q, ℝ)) x ∂μ = μ.real univ := by simp
    rw [h2] at h1
    have h3 : a * (-(φ 1)) = 1 := by
      rw [ha]; exact inv_mul_cancel₀ (by linarith)
    rw [h3, measureReal_def] at h1
    exact (ENNReal.toReal_eq_one_iff _).mp h1
  refine ⟨μ, ⟨hμuniv⟩, ?_⟩
  intro f hf
  rw [hint f]
  have h1 : u ≤ φ f := hφ𝒞 f hf
  apply le_of_forall_pos_lt_add
  intro ε hε
  have h2 := hconst (3 + ε) (by linarith)
  have h3 : a * (-(φ 1)) = 1 := by
    rw [ha]; exact inv_mul_cancel₀ (by linarith)
  have h4 : a * (-(φ f)) ≤ a * (-u) := by
    apply mul_le_mul_of_nonneg_left _ ha0.le
    linarith
  have h5 : a * (-u) < a * ((3 + ε) * (-(φ 1))) := by
    apply mul_lt_mul_of_pos_left _ ha0
    linarith
  have h6 : a * ((3 + ε) * (-(φ 1))) = 3 + ε := by
    calc a * ((3 + ε) * (-(φ 1))) = (3 + ε) * (a * (-(φ 1))) := by ring
      _ = 3 + ε := by rw [h3, mul_one]
  linarith

end ModSep

section ModGauss

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/- ### Decimal literals in `ℝ≥0∞` -/

theorem G54.ennreal_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℝ≥0∞)
      = ENNReal.ofReal (OfScientific.ofScientific m s e) := by
  have h1 : (OfScientific.ofScientific m s e : ℝ≥0∞)
      = ((OfScientific.ofScientific m s e : NNReal) : ℝ≥0∞) := rfl
  rw [h1, ENNReal.ofReal, ← NNReal.coe_ofScientific, Real.toNNReal_coe]

theorem G54.le_real_of_ofScientific_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (s : Set α) (m : ℕ) (b : Bool) (e : ℕ)
    (h : (OfScientific.ofScientific m b e : ℝ≥0∞) ≤ μ s) :
    (OfScientific.ofScientific m b e : ℝ) ≤ μ.real s := by
  rw [G54.ennreal_ofScientific] at h
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ s)).mp h

theorem G54.ofScientific_le_of_le_real {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (s : Set α) (m : ℕ) (b : Bool) (e : ℕ)
    (h : (OfScientific.ofScientific m b e : ℝ) ≤ μ.real s) :
    (OfScientific.ofScientific m b e : ℝ≥0∞) ≤ μ s := by
  rw [G54.ennreal_ofScientific]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ s)).mpr h

/- ### Symmetry and finite-dimensional marginals of the Gaussian measures -/

theorem G54.gInf_map_neg :
    (Green54.gaussianMeasureInf).map (fun x : ℕ → ℝ => -x) = Green54.gaussianMeasureInf := by
  unfold Green54.gaussianMeasureInf
  have h := Measure.infinitePi_map_pi (μ := fun _ : ℕ => gaussianReal 0 1)
    (f := fun _ x => -x) (fun _ => measurable_neg)
  simp only [gaussianReal_map_neg, neg_zero] at h
  exact h

theorem G54.gInf_map_proj (n : ℕ) :
    (Green54.gaussianMeasureInf).map (fun (x : ℕ → ℝ) (i : Fin n) => x i)
      = Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  classical
  unfold Green54.gaussianMeasureInf
  symm
  apply Measure.pi_eq
  intro s hs
  have hmeas : Measurable (fun (x : ℕ → ℝ) (i : Fin n) => x i) := by fun_prop
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  set t : ℕ → Set ℝ := fun k => if h : k < n then s ⟨k, h⟩ else univ with ht
  have hpre : (fun (x : ℕ → ℝ) (i : Fin n) => x i) ⁻¹' (univ.pi s)
      = Set.pi (Finset.range n : Set ℕ) t := by
    ext x
    simp only [mem_preimage, Set.mem_pi, Finset.coe_range, mem_Iio]
    constructor
    · intro h k hk
      have h1 : t k = s ⟨k, hk⟩ := by simp only [ht, dif_pos hk]
      rw [h1]
      exact h ⟨k, hk⟩ (mem_univ _)
    · intro h i _
      have h1 : t i = s i := by simp only [ht, dif_pos i.2]
      have h2 := h i i.2
      rw [h1] at h2
      exact h2
  rw [hpre, Measure.infinitePi_pi]
  · rw [← Fin.prod_univ_eq_prod_range (fun k => (gaussianReal 0 1) (t k)) n]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [ht, dif_pos i.2]
  · intro k hk
    simp only [ht]
    split_ifs with h
    · exact hs _
    · exact MeasurableSet.univ

theorem G54.pi_gauss_map_neg (n : ℕ) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (fun x : Fin n → ℝ => -x)
      = Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  have hsf : ∀ _ : Fin n, SigmaFinite (Measure.map (fun x : ℝ => -x) (gaussianReal 0 1)) := by
    intro _
    rw [gaussianReal_map_neg]
    infer_instance
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (f := fun _ x => -x) (hμ := hsf) (fun _ => measurable_neg.aemeasurable)
  simp only [gaussianReal_map_neg, neg_zero] at h
  exact h

theorem G54.integrable_clm_pi_gauss (n : ℕ) (l : (Fin n → ℝ) →L[ℝ] ℝ) :
    Integrable (fun x => l x) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  classical
  have hrep : (fun x : Fin n → ℝ => l x)
      = fun x => ∑ i, x i * l (fun j => if i = j then 1 else 0) := by
    funext x
    have := LinearMap.pi_apply_eq_sum_univ (l : (Fin n → ℝ) →ₗ[ℝ] ℝ) x
    simpa [smul_eq_mul] using this
  rw [hrep]
  refine integrable_finsetSum _ fun i _ => ?_
  refine Integrable.mul_const ?_ _
  exact MeasureTheory.integrable_eval (μ := fun _ : Fin n => gaussianReal 0 1)
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))

/-- A closed subset of `ℕ → ℝ` is the intersection of its finite-dimensional cylinders. -/
theorem G54.iInter_cylinder_eq {T : Set (ℕ → ℝ)} (hT : IsClosed T) :
    ⋂ n : ℕ, {x : ℕ → ℝ | ∃ y ∈ T, ∀ i : Fin n, y i = x i} = T := by
  apply Subset.antisymm
  · intro x hx
    rw [mem_iInter] at hx
    choose y hyT hy using hx
    have hlim : Tendsto y atTop (𝓝 x) := by
      rw [tendsto_pi_nhds]
      intro k
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop k] with n hn
      exact (hy n ⟨k, hn⟩).symm
    exact hT.mem_of_tendsto hlim (Eventually.of_forall hyT)
  · intro x hx
    rw [mem_iInter]
    intro n
    exact ⟨x, hx, fun _ => rfl⟩

end ModGauss

section ModDom

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/-- Continuous functions are integrable against a finite measure carried by a compact set. -/
theorem G54.integrable_of_compact_support {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {S : Set X} (hS : IsCompact S) (hμS : μ Sᶜ = 0) {g : X → ℝ} (hg : ContinuousOn g S) :
    Integrable g μ := by
  have h1 : IntegrableOn g S μ := hg.integrableOn_compact hS
  have h2 : μ.restrict S = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]
    exact hμS)
  rw [IntegrableOn, h2] at h1
  exact h1

/-- For symmetric measures, convex domination can be tested on nonnegative convex functions
vanishing at the origin (the affine part is killed by symmetry). -/
theorem G54.convex_dom_of_nonneg {n : ℕ} (μ γ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure γ]
    (hμsymm : μ.map (fun x => -x) = μ) (hγsymm : γ.map (fun x => -x) = γ)
    (hμcpt : ∃ S : Set (Fin n → ℝ), IsCompact S ∧ μ Sᶜ = 0)
    (hγlin : ∀ l : (Fin n → ℝ) →L[ℝ] ℝ, Integrable (fun x => l x) γ)
    (hdom : ∀ g : (Fin n → ℝ) → ℝ, Continuous g → ConvexOn ℝ univ g → (∀ x, 0 ≤ g x) →
        g 0 = 0 → Integrable g γ → ∫ x, g x ∂μ ≤ ∫ x, g x ∂γ)
    (h : (Fin n → ℝ) → ℝ) (hconv : ConvexOn ℝ univ h) (hint : Integrable h γ) :
    ∫ x, h x ∂μ ≤ ∫ x, h x ∂γ := by
  have hcont : Continuous h := hconv.locallyLipschitz.continuous
  obtain ⟨S, hS, hμS⟩ := hμcpt
  have hμint : ∀ g : (Fin n → ℝ) → ℝ, Continuous g → Integrable g μ := fun g hg =>
    G54.integrable_of_compact_support μ hS hμS hg.continuousOn
  have hodd : ∀ (ν : Measure (Fin n → ℝ)) (l : (Fin n → ℝ) →L[ℝ] ℝ),
      ν.map (fun x => -x) = ν → ∫ x, l x ∂ν = 0 := by
    intro ν l hν
    have h1 : ∫ x, l x ∂(ν.map (fun x => -x)) = ∫ x, l (-x) ∂ν :=
      integral_map measurable_neg.aemeasurable l.continuous.aestronglyMeasurable
    rw [hν] at h1
    simp only [map_neg, integral_neg] at h1
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨l, c, hle, hlc⟩ := ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ)
    (x := (0 : Fin n → ℝ)) (a := h 0 - ε) (mem_univ _) (by linarith) isClosed_univ
    (hcont.lowerSemicontinuous.lowerSemicontinuousOn univ) hconv
  have hle' : ∀ z, l z + c ≤ h z := fun z => by simpa using hle ⟨z, mem_univ z⟩
  have hc : c = h 0 - ε := by simpa using hlc
  set h₁ : (Fin n → ℝ) → ℝ := fun z => h z - l z - h 0 with hh₁
  have h₁lb : ∀ z, -ε ≤ h₁ z := fun z => by
    simp only [hh₁]
    linarith [hle' z]
  set h₂ : (Fin n → ℝ) → ℝ := fun z => max (h₁ z) 0 with hh₂
  have h₁cont : Continuous h₁ := (hcont.sub l.continuous).sub continuous_const
  have h₂cont : Continuous h₂ := h₁cont.max continuous_const
  have h₁conv : ConvexOn ℝ univ h₁ :=
    (hconv.sub (l.toLinearMap.concaveOn convex_univ)).sub (concaveOn_const _ convex_univ)
  have h₂conv : ConvexOn ℝ univ h₂ := h₁conv.sup (convexOn_const 0 convex_univ)
  have h₁int : Integrable h₁ γ := (hint.sub (hγlin l)).sub (integrable_const _)
  have h₂int : Integrable h₂ γ := h₁int.sup (integrable_const 0)
  have key := hdom h₂ h₂cont h₂conv (fun x => le_max_right _ _) (by simp [hh₂, hh₁]) h₂int
  have e1 : ∫ x, h₁ x ∂μ ≤ ∫ x, h₂ x ∂μ :=
    integral_mono (hμint _ h₁cont) (hμint _ h₂cont) (fun x => le_max_left _ _)
  have e2 : ∫ x, h₂ x ∂γ ≤ ∫ x, h₁ x ∂γ + ε := by
    have h3 : ∫ x, h₂ x ∂γ ≤ ∫ x, (h₁ x + ε) ∂γ := by
      refine integral_mono h₂int (h₁int.add (integrable_const _)) (fun x => ?_)
      simp only [hh₂]
      exact max_le (by linarith) (by linarith [h₁lb x])
    rw [integral_add h₁int (integrable_const _)] at h3
    simpa using h3
  have e3 : ∀ (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν], ν.map (fun x => -x) = ν →
      Integrable h ν → Integrable (fun x => l x) ν →
      ∫ x, h x ∂ν = ∫ x, h₁ x ∂ν + h 0 := by
    intro ν _ hν hhν hlν
    have h4 : ∫ x, h₁ x ∂ν = ∫ x, h x ∂ν - ∫ x, l x ∂ν - h 0 := by
      have h5 : ∫ x, h₁ x ∂ν = ∫ x, ((h x - l x) - h 0) ∂ν := rfl
      have h6 : ∫ x, ((h x - l x) - h 0) ∂ν = ∫ x, (h x - l x) ∂ν - ∫ _, h 0 ∂ν :=
        integral_sub (hhν.sub hlν) (integrable_const _)
      have h7 : ∫ x, (h x - l x) ∂ν = ∫ x, h x ∂ν - ∫ x, l x ∂ν := integral_sub hhν hlν
      rw [h5, h6, h7]
      simp
    rw [h4, hodd ν l hν]
    ring
  rw [e3 μ hμsymm (hμint _ hcont) (hμint _ l.continuous),
    e3 γ hγsymm hint (hγlin l)]
  linarith

end ModDom

section ModScale

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/-- From the normalised family of test functions to arbitrary ones: if `∫ f dν ≤ 3` for every
admissible `f` with `∫ f dγ ≤ 1`, then `∫ f(x/3) dν ≤ ∫ f dγ` and `∫ f(-x/3) dν ≤ ∫ f dγ` for
every admissible `f` (nonnegative, convex, continuous, vanishing at `0`, `γ`-integrable). -/
theorem G54.scaled_dom (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] {Q : Set (ℕ → ℝ)}
    (hQ : IsCompact Q) (hνQ : ν Qᶜ = 0)
    (hν : ∀ f : (ℕ → ℝ) → ℝ, Continuous f → ConvexOn ℝ univ f → (∀ x, 0 ≤ f x) → f 0 = 0 →
      Integrable f Green54.gaussianMeasureInf → ∫ x, f x ∂Green54.gaussianMeasureInf ≤ 1 →
      ∫ x, f x ∂ν ≤ 3)
    (f : (ℕ → ℝ) → ℝ) (hfc : Continuous f) (hfconv : ConvexOn ℝ univ f) (hf0 : ∀ x, 0 ≤ f x)
    (hfz : f 0 = 0) (hfi : Integrable f Green54.gaussianMeasureInf) :
    ∫ x, f ((3 : ℝ)⁻¹ • x) ∂ν ≤ ∫ x, f x ∂Green54.gaussianMeasureInf ∧
    ∫ x, f (-((3 : ℝ)⁻¹ • x)) ∂ν ≤ ∫ x, f x ∂Green54.gaussianMeasureInf := by
  have hνint : ∀ g : (ℕ → ℝ) → ℝ, Continuous g → Integrable g ν := fun g hg =>
    G54.integrable_of_compact_support ν hQ hνQ hg.continuousOn
  -- Step 1: `∫ g dν ≤ 3 ∫ g dγ` for admissible `g`.
  have step1 : ∀ g : (ℕ → ℝ) → ℝ, Continuous g → ConvexOn ℝ univ g → (∀ x, 0 ≤ g x) → g 0 = 0 →
      Integrable g Green54.gaussianMeasureInf →
      ∫ x, g x ∂ν ≤ 3 * ∫ x, g x ∂Green54.gaussianMeasureInf := by
    intro g hgc hgconv hg0 hgz hgi
    set m : ℝ := ∫ x, g x ∂Green54.gaussianMeasureInf with hm
    have hm0 : 0 ≤ m := integral_nonneg hg0
    apply le_of_forall_pos_le_add
    intro δ hδ
    set ε : ℝ := δ / 3 with hε
    have hε0 : 0 < ε := by positivity
    have hme : 0 < m + ε := by linarith
    set c : ℝ := (m + ε)⁻¹ with hc
    have hc0 : 0 < c := inv_pos.mpr hme
    have h1 := hν (fun x => c * g x) (continuous_const.mul hgc)
      (by
        have := hgconv.smul hc0.le
        simpa [smul_eq_mul] using this)
      (fun x => mul_nonneg hc0.le (hg0 x)) (by simp [hgz]) (hgi.const_mul c)
      (by
        rw [integral_const_mul, ← hm, hc, inv_mul_le_iff₀ hme]
        linarith)
    rw [integral_const_mul, hc, inv_mul_le_iff₀ hme] at h1
    have : (m + ε) * 3 = 3 * m + δ := by rw [hε]; ring
    linarith
  -- Step 2: `∫ g(x/3) dν ≤ ∫ g dγ`.
  have step2 : ∀ g : (ℕ → ℝ) → ℝ, Continuous g → ConvexOn ℝ univ g → (∀ x, 0 ≤ g x) → g 0 = 0 →
      Integrable g Green54.gaussianMeasureInf →
      ∫ x, g ((3 : ℝ)⁻¹ • x) ∂ν ≤ ∫ x, g x ∂Green54.gaussianMeasureInf := by
    intro g hgc hgconv hg0 hgz hgi
    have hpt : ∀ x, g ((3 : ℝ)⁻¹ • x) ≤ (3 : ℝ)⁻¹ * g x := by
      intro x
      have h1 := hgconv.2 (mem_univ x) (mem_univ (0 : ℕ → ℝ))
        (show (0 : ℝ) ≤ 3⁻¹ by norm_num) (show (0 : ℝ) ≤ 2 / 3 by norm_num) (by norm_num)
      simpa [hgz, smul_eq_mul] using h1
    have h2 : ∫ x, g ((3 : ℝ)⁻¹ • x) ∂ν ≤ ∫ x, (3 : ℝ)⁻¹ * g x ∂ν :=
      integral_mono (hνint _ (hgc.comp (continuous_const_smul _)))
        ((hνint _ hgc).const_mul _) hpt
    rw [integral_const_mul] at h2
    have h3 := step1 g hgc hgconv hg0 hgz hgi
    linarith
  refine ⟨step2 f hfc hfconv hf0 hfz hfi, ?_⟩
  -- the reflected function
  have hneg_meas : Measurable (fun x : ℕ → ℝ => -x) := measurable_neg
  have hfi' : Integrable (fun x => f (-x)) Green54.gaussianMeasureInf := by
    have h1 : Integrable f (Green54.gaussianMeasureInf.map (fun x : ℕ → ℝ => -x)) := by
      rw [G54.gInf_map_neg]; exact hfi
    exact (integrable_map_measure hfc.aestronglyMeasurable hneg_meas.aemeasurable).mp h1
  have hfint' : ∫ x, f (-x) ∂Green54.gaussianMeasureInf = ∫ x, f x ∂Green54.gaussianMeasureInf := by
    have h1 := integral_map (μ := Green54.gaussianMeasureInf) hneg_meas.aemeasurable
      (f := f) hfc.aestronglyMeasurable
    rw [G54.gInf_map_neg] at h1
    exact h1.symm
  have hconv' : ConvexOn ℝ univ (fun x : ℕ → ℝ => f (-x)) := by
    have := hfconv.comp_linearMap (-LinearMap.id : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ))
    simpa [Function.comp_def] using this
  have h4 := step2 (fun x => f (-x)) (hfc.comp continuous_neg) hconv' (fun x => hf0 _)
    (by simp [hfz]) hfi'
  rw [hfint'] at h4
  exact h4

end ModScale

section ModCyl

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/-- **Finite-dimensional step.**  Let `ν` be a probability measure on `ℕ → ℝ`, carried by a compact
set, satisfying Talagrand's dual condition `∫ f dν ≤ 3` for all admissible `f`.  Projecting the
symmetrisation of `x ↦ x/3` to the first `n` coordinates gives a compactly supported measure which
is dominated in the convex order by the standard Gaussian of `ℝⁿ`.  The landing property `hL`
(a consequence of the Three Gaussians theorem) then shows that `ν` gives mass at least `1/2` to the
`n`-th cylinder over `3 • (K + K + K)`. -/
theorem G54.half_le_cylinder
    (hL : ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), IsProbabilityMeasure μ →
      (∃ S : Set (Fin n → ℝ), IsCompact S ∧ μ Sᶜ = 0) →
      (∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
        Integrable f (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
        ∫ x, f x ∂μ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) →
      ∀ A : Set (Fin n → ℝ), IsCompact A → Balanced ℝ A →
        (0.99 : ℝ≥0∞) ≤ (Measure.pi fun _ : Fin n => gaussianReal 0 1) A →
        (1 / 2 : ℝ≥0∞) ≤ μ (A + A + A))
    {K : Set (ℕ → ℝ)} (hK : IsCompact K) (hKb : Balanced ℝ K)
    (hKm : (0.99 : ℝ≥0∞) ≤ Green54.gaussianMeasureInf K)
    (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] {Q : Set (ℕ → ℝ)} (hQ : IsCompact Q)
    (hνQ : ν Qᶜ = 0)
    (hν : ∀ f : (ℕ → ℝ) → ℝ, Continuous f → ConvexOn ℝ univ f → (∀ x, 0 ≤ f x) → f 0 = 0 →
      Integrable f Green54.gaussianMeasureInf → ∫ x, f x ∂Green54.gaussianMeasureInf ≤ 1 →
      ∫ x, f x ∂ν ≤ 3) (n : ℕ) :
    (1 / 2 : ℝ≥0∞) ≤ ν {x : ℕ → ℝ | ∃ y ∈ (3 : ℝ) • (K + K + K), ∀ i : Fin n, y i = x i} := by
  classical
  have hνint : ∀ g : (ℕ → ℝ) → ℝ, Continuous g → Integrable g ν := fun g hg =>
    G54.integrable_of_compact_support ν hQ hνQ hg.continuousOn
  set γn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1) with hγn
  set P : (ℕ → ℝ) → (Fin n → ℝ) := fun x i => x i with hP
  have hPc : Continuous P := continuous_pi fun i => continuous_apply _
  have hPm : Measurable P := hPc.measurable
  set pp : (ℕ → ℝ) → (Fin n → ℝ) := fun x => P ((3 : ℝ)⁻¹ • x) with hpp
  set pm : (ℕ → ℝ) → (Fin n → ℝ) := fun x => P (-((3 : ℝ)⁻¹ • x)) with hpm
  have hppc : Continuous pp := hPc.comp (continuous_const_smul _)
  have hpmc : Continuous pm := hPc.comp (continuous_const_smul _).neg
  set μ : Measure (Fin n → ℝ) := (2⁻¹ : ℝ≥0∞) • (ν.map pp + ν.map pm) with hμ
  have hpp1 : IsProbabilityMeasure (ν.map pp) := Measure.isProbabilityMeasure_map hppc.aemeasurable
  have hpm1 : IsProbabilityMeasure (ν.map pm) := Measure.isProbabilityMeasure_map hpmc.aemeasurable
  have hμ1 : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
      one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  -- symmetry
  have hμsymm : μ.map (fun x => -x) = μ := by
    have h1 : (fun x : Fin n → ℝ => -x) ∘ pp = pm := by
      funext x
      rfl
    have h2 : (fun x : Fin n → ℝ => -x) ∘ pm = pp := by
      funext x
      funext i
      simp [hpm, hpp, hP]
    rw [hμ, Measure.map_smul, Measure.map_add _ _ measurable_neg,
      Measure.map_map measurable_neg hppc.measurable,
      Measure.map_map measurable_neg hpmc.measurable, h1, h2, add_comm]
  -- compact support
  have hμcpt : ∃ S : Set (Fin n → ℝ), IsCompact S ∧ μ Sᶜ = 0 := by
    have hSc : IsCompact (pp '' Q ∪ pm '' Q) := (hQ.image hppc).union (hQ.image hpmc)
    refine ⟨pp '' Q ∪ pm '' Q, hSc, ?_⟩
    have hSm : MeasurableSet (pp '' Q ∪ pm '' Q)ᶜ := hSc.measurableSet.compl
    have h1 : ν (pp ⁻¹' (pp '' Q ∪ pm '' Q)ᶜ) = 0 :=
      measure_mono_null (fun x hx hxQ => hx (Or.inl ⟨x, hxQ, rfl⟩)) hνQ
    have h2 : ν (pm ⁻¹' (pp '' Q ∪ pm '' Q)ᶜ) = 0 :=
      measure_mono_null (fun x hx hxQ => hx (Or.inr ⟨x, hxQ, rfl⟩)) hνQ
    rw [hμ, Measure.smul_apply, Measure.add_apply, Measure.map_apply hppc.measurable hSm,
      Measure.map_apply hpmc.measurable hSm, h1, h2]
    simp
  -- domination on admissible test functions
  have hdom0 : ∀ g : (Fin n → ℝ) → ℝ, Continuous g → ConvexOn ℝ univ g → (∀ x, 0 ≤ g x) →
      g 0 = 0 → Integrable g γn → ∫ x, g x ∂μ ≤ ∫ x, g x ∂γn := by
    intro g hgc hgconv hg0 hgz hgi
    set f : (ℕ → ℝ) → ℝ := fun x => g (P x) with hf
    have hfc : Continuous f := hgc.comp hPc
    have hfconv : ConvexOn ℝ univ f := by
      have h1 := hgconv.comp_linearMap
        (LinearMap.pi (fun i : Fin n => (LinearMap.proj (i : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ)))
      rw [preimage_univ] at h1
      exact h1
    have hfi : Integrable f Green54.gaussianMeasureInf := by
      have h1 : Integrable g (Green54.gaussianMeasureInf.map P) := by
        rw [G54.gInf_map_proj]; exact hgi
      exact (integrable_map_measure hgc.aestronglyMeasurable hPm.aemeasurable).mp h1
    have hfint : ∫ x, f x ∂Green54.gaussianMeasureInf = ∫ x, g x ∂γn := by
      have h1 := integral_map (μ := Green54.gaussianMeasureInf) hPm.aemeasurable
        (f := g) hgc.aestronglyMeasurable
      rw [G54.gInf_map_proj] at h1
      exact h1.symm
    have hfz : f 0 = 0 := by
      have : P 0 = 0 := rfl
      simp only [hf, this, hgz]
    obtain ⟨h1, h2⟩ := G54.scaled_dom ν hQ hνQ hν f hfc hfconv (fun x => hg0 _) hfz hfi
    rw [hfint] at h1 h2
    have hgi1 : Integrable g (ν.map pp) :=
      (integrable_map_measure hgc.aestronglyMeasurable hppc.aemeasurable).mpr
        (hνint _ (hgc.comp hppc))
    have hgi2 : Integrable g (ν.map pm) :=
      (integrable_map_measure hgc.aestronglyMeasurable hpmc.aemeasurable).mpr
        (hνint _ (hgc.comp hpmc))
    rw [hμ, integral_smul_measure, integral_add_measure hgi1 hgi2,
      integral_map hppc.aemeasurable hgc.aestronglyMeasurable,
      integral_map hpmc.aemeasurable hgc.aestronglyMeasurable]
    have h3 : ((2⁻¹ : ℝ≥0∞)).toReal = 2⁻¹ := by simp
    rw [h3, smul_eq_mul]
    have h4 : ∫ x, g (pp x) ∂ν ≤ ∫ x, g x ∂γn := h1
    have h5 : ∫ x, g (pm x) ∂ν ≤ ∫ x, g x ∂γn := h2
    linarith
  have hγn1 : IsProbabilityMeasure γn := by rw [hγn]; infer_instance
  have hdom := G54.convex_dom_of_nonneg μ γn hμsymm (G54.pi_gauss_map_neg n) hμcpt
    (G54.integrable_clm_pi_gauss n) hdom0
  -- the projected set
  set A : Set (Fin n → ℝ) := P '' K with hA
  have hAc : IsCompact A := hK.image hPc
  have hAb : Balanced ℝ A := by
    rw [balanced_iff_smul_mem]
    rintro a ha _ ⟨x, hxK, rfl⟩
    exact ⟨a • x, balanced_iff_smul_mem.mp hKb ha hxK, rfl⟩
  have hAm : (0.99 : ℝ≥0∞) ≤ γn A := by
    rw [hγn, ← G54.gInf_map_proj n, Measure.map_apply hPm hAc.measurableSet]
    exact hKm.trans (measure_mono (subset_preimage_image P K))
  have hland := hL n μ hμ1 hμcpt (fun f hf hfi => hdom f hf hfi) A hAc hAb hAm
  have hAAA : IsCompact (A + A + A) := (hAc.add hAc).add hAc
  rw [hμ, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply hppc.measurable hAAA.measurableSet,
    Measure.map_apply hpmc.measurable hAAA.measurableSet] at hland
  set An : Set (ℕ → ℝ) := {x : ℕ → ℝ | ∃ y ∈ (3 : ℝ) • (K + K + K), ∀ i : Fin n, y i = x i}
    with hAn
  have hsub1 : pp ⁻¹' (A + A + A) ⊆ An := by
    rintro x ⟨_, ⟨_, ⟨a, haK, rfl⟩, _, ⟨b, hbK, rfl⟩, rfl⟩, _, ⟨c, hcK, rfl⟩, hsum⟩
    refine ⟨(3 : ℝ) • (a + b + c), smul_mem_smul_set (add_mem_add (add_mem_add haK hbK) hcK), ?_⟩
    intro i
    have h1 := congrFun hsum i
    simp only [hpp, hP, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    linarith
  have hsub2 : pm ⁻¹' (A + A + A) ⊆ An := by
    rintro x ⟨_, ⟨_, ⟨a, haK, rfl⟩, _, ⟨b, hbK, rfl⟩, rfl⟩, _, ⟨c, hcK, rfl⟩, hsum⟩
    refine ⟨(3 : ℝ) • (-a + -b + -c), smul_mem_smul_set (add_mem_add (add_mem_add
      (hKb.neg_mem_iff.mpr haK) (hKb.neg_mem_iff.mpr hbK)) (hKb.neg_mem_iff.mpr hcK)), ?_⟩
    intro i
    have h1 := congrFun hsum i
    simp only [hpm, hP, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at h1 ⊢
    linarith
  calc (1 / 2 : ℝ≥0∞) ≤ (2⁻¹ : ℝ≥0∞) • (ν (pp ⁻¹' (A + A + A)) + ν (pm ⁻¹' (A + A + A))) := hland
    _ ≤ (2⁻¹ : ℝ≥0∞) • (ν An + ν An) := by
        rw [smul_eq_mul, smul_eq_mul]
        gcongr
    _ = ν An := by
        rw [smul_eq_mul, ← two_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

end ModCyl

section ModMain

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/-- For a balanced set containing `0`, `3 (K + K + K) ⊆ 10 K` (ten-fold sumset). -/
theorem G54.T_subset {K : Set (ℕ → ℝ)} (h0 : (0 : ℕ → ℝ) ∈ K) :
    (3 : ℝ) • (K + K + K) ⊆ (10 : ℕ) • K := by
  have h10 : (10 : ℕ) • K = K + K + K + K + K + K + K + K + K + K := by
    simp only [succ_nsmul, zero_nsmul, zero_add]
  rw [h10]
  rintro _ ⟨_, ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩, rfl⟩
  have heq : (3 : ℝ) • (a + b + c) = a + a + a + b + b + b + c + c + c + 0 := by
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply]
    ring
  change (3 : ℝ) • (a + b + c) ∈ _
  rw [heq]
  exact add_mem_add (add_mem_add (add_mem_add (add_mem_add (add_mem_add (add_mem_add
    (add_mem_add (add_mem_add (add_mem_add ha ha) ha) hb) hb) hb) hc) hc) hc) h0

/-- The convex sets `B ∩ {f ≤ 3} ∩ {f ∘ neg ≤ 3}` have Gaussian measure at least `0.01`. -/
theorem G54.measure_D (B : Set (ℕ → ℝ)) (hBm : MeasurableSet B)
    (hB : (0.99 : ℝ≥0∞) ≤ Green54.gaussianMeasureInf B)
    (f : (ℕ → ℝ) → ℝ) (hfc : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f Green54.gaussianMeasureInf)
    (hf1 : ∫ x, f x ∂Green54.gaussianMeasureInf ≤ 1) :
    (0.01 : ℝ≥0∞) ≤ Green54.gaussianMeasureInf (B ∩ {x | f x ≤ 3} ∩ {x | f (-x) ≤ 3}) := by
  have hprob : IsProbabilityMeasure Green54.gaussianMeasureInf := by
    unfold Green54.gaussianMeasureInf; infer_instance
  apply G54.ofScientific_le_of_le_real
  have hBr : (0.99 : ℝ) ≤ Green54.gaussianMeasureInf.real B :=
    G54.le_real_of_ofScientific_le _ B _ _ _ hB
  set D : Set (ℕ → ℝ) := B ∩ {x | f x ≤ 3} ∩ {x | f (-x) ≤ 3} with hD
  have hDm : MeasurableSet D :=
    (hBm.inter (isClosed_le hfc continuous_const).measurableSet).inter
      (isClosed_le (hfc.comp continuous_neg) continuous_const).measurableSet
  have hsub : Dᶜ ⊆ Bᶜ ∪ {x | 3 ≤ f x} ∪ {x | 3 ≤ f (-x)} := by
    intro x hx
    by_contra hcon
    have h1 : x ∈ B := by
      by_contra hxB
      exact hcon (Or.inl (Or.inl hxB))
    have h2 : f x ≤ 3 := by
      by_contra hfx
      exact hcon (Or.inl (Or.inr (not_le.mp hfx).le))
    have h3 : f (-x) ≤ 3 := by
      by_contra hfx
      exact hcon (Or.inr (not_le.mp hfx).le)
    exact hx ⟨⟨h1, h2⟩, h3⟩
  have h1 : Green54.gaussianMeasureInf.real {x | 3 ≤ f x} ≤ 1 / 3 := by
    have := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hf0) hfi 3
    linarith
  have h2 : Green54.gaussianMeasureInf.real {x | 3 ≤ f (-x)} ≤ 1 / 3 := by
    have hS : MeasurableSet {x : ℕ → ℝ | 3 ≤ f x} :=
      (isClosed_le continuous_const hfc).measurableSet
    have h := Measure.map_apply (μ := Green54.gaussianMeasureInf)
      (f := fun x : ℕ → ℝ => -x) measurable_neg hS
    rw [G54.gInf_map_neg] at h
    have h' : Green54.gaussianMeasureInf {x | 3 ≤ f (-x)}
        = Green54.gaussianMeasureInf {x | 3 ≤ f x} := h.symm
    rw [measureReal_def, h', ← measureReal_def]
    exact h1
  have h3 : Green54.gaussianMeasureInf.real Dᶜ ≤ Green54.gaussianMeasureInf.real Bᶜ
      + Green54.gaussianMeasureInf.real {x | 3 ≤ f x}
      + Green54.gaussianMeasureInf.real {x | 3 ≤ f (-x)} :=
    (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
      (add_le_add_left (measureReal_union_le _ _) _))
  have h4 : Green54.gaussianMeasureInf.real Dᶜ = 1 - Green54.gaussianMeasureInf.real D :=
    probReal_compl_eq_one_sub hDm
  have h5 : Green54.gaussianMeasureInf.real Bᶜ = 1 - Green54.gaussianMeasureInf.real B :=
    probReal_compl_eq_one_sub hBm
  have h6 : (0.01 : ℝ) ≤ Green54.gaussianMeasureInf.real D := by linarith
  exact h6

/-- Passing to the limit along the cylinders: `ν` gives mass at least `1/2` to `3 (K + K + K)`. -/
theorem G54.half_le_T
    (hL : ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), IsProbabilityMeasure μ →
      (∃ S : Set (Fin n → ℝ), IsCompact S ∧ μ Sᶜ = 0) →
      (∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
        Integrable f (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
        ∫ x, f x ∂μ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) →
      ∀ A : Set (Fin n → ℝ), IsCompact A → Balanced ℝ A →
        (0.99 : ℝ≥0∞) ≤ (Measure.pi fun _ : Fin n => gaussianReal 0 1) A →
        (1 / 2 : ℝ≥0∞) ≤ μ (A + A + A))
    {K : Set (ℕ → ℝ)} (hK : IsCompact K) (hKb : Balanced ℝ K)
    (hKm : (0.99 : ℝ≥0∞) ≤ Green54.gaussianMeasureInf K)
    (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] {Q : Set (ℕ → ℝ)} (hQ : IsCompact Q)
    (hνQ : ν Qᶜ = 0)
    (hν : ∀ f : (ℕ → ℝ) → ℝ, Continuous f → ConvexOn ℝ univ f → (∀ x, 0 ≤ f x) → f 0 = 0 →
      Integrable f Green54.gaussianMeasureInf → ∫ x, f x ∂Green54.gaussianMeasureInf ≤ 1 →
      ∫ x, f x ∂ν ≤ 3) :
    (1 / 2 : ℝ≥0∞) ≤ ν ((3 : ℝ) • (K + K + K)) := by
  set T : Set (ℕ → ℝ) := (3 : ℝ) • (K + K + K) with hT
  have hTc : IsCompact T := ((hK.add hK).add hK).smul 3
  set An : ℕ → Set (ℕ → ℝ) := fun n => {x : ℕ → ℝ | ∃ y ∈ T, ∀ i : Fin n, y i = x i} with hAn
  have hAn_meas : ∀ n, MeasurableSet (An n) := by
    intro n
    have hPc : Continuous (fun (x : ℕ → ℝ) (i : Fin n) => x i) :=
      continuous_pi fun i => continuous_apply _
    have heq : An n = (fun (x : ℕ → ℝ) (i : Fin n) => x i) ⁻¹'
        ((fun (x : ℕ → ℝ) (i : Fin n) => x i) '' T) := by
      ext x
      constructor
      · rintro ⟨y, hyT, hy⟩
        exact ⟨y, hyT, funext hy⟩
      · rintro ⟨y, hyT, hy⟩
        exact ⟨y, hyT, fun i => congrFun hy i⟩
    rw [heq]
    exact ((hTc.image hPc).isClosed.preimage hPc).measurableSet
  have hAn_anti : Antitone An := by
    intro n m hnm x hx
    obtain ⟨y, hyT, hy⟩ := hx
    exact ⟨y, hyT, fun i => hy ⟨i, lt_of_lt_of_le i.2 hnm⟩⟩
  have hlim := tendsto_measure_iInter_atTop (μ := ν) (fun n => (hAn_meas n).nullMeasurableSet)
    hAn_anti ⟨0, measure_ne_top ν _⟩
  have hinter : ⋂ n, An n = T := G54.iInter_cylinder_eq hTc.isClosed
  rw [hinter] at hlim
  exact ge_of_tendsto' hlim (fun n => G54.half_le_cylinder hL hK hKb hKm ν hQ hνQ hν n)

/-- **Talagrand's convexity conjecture in the form of Green's Problem 54**, conditional on the
landing property `hL` of measures dominated by the Gaussian in the convex order. -/
theorem G54.green54_of_landing
    (hL : ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), IsProbabilityMeasure μ →
      (∃ S : Set (Fin n → ℝ), IsCompact S ∧ μ Sᶜ = 0) →
      (∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
        Integrable f (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
        ∫ x, f x ∂μ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) →
      ∀ A : Set (Fin n → ℝ), IsCompact A → Balanced ℝ A →
        (0.99 : ℝ≥0∞) ≤ (Measure.pi fun _ : Fin n => gaussianReal 0 1) A →
        (1 / 2 : ℝ≥0∞) ≤ μ (A + A + A)) :
    ∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K →
      (0.99 : ℝ≥0∞) ≤ Green54.gaussianMeasureInf K →
      ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℕ) • K ∧
        (0.01 : ℝ≥0∞) ≤ Green54.gaussianMeasureInf C := by
  intro K hK hKb hKm
  classical
  have hprob : IsProbabilityMeasure Green54.gaussianMeasureInf := by
    unfold Green54.gaussianMeasureInf; infer_instance
  have hreg : (Green54.gaussianMeasureInf).OuterRegular := by
    unfold Green54.gaussianMeasureInf; infer_instance
  have hKne : K.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have h1 := G54.le_real_of_ofScientific_le _ K _ _ _ hKm
    rw [h, measureReal_empty] at h1
    norm_num at h1
  have h0K : (0 : ℕ → ℝ) ∈ K := hKb.zero_mem hKne
  set T : Set (ℕ → ℝ) := (3 : ℝ) • (K + K + K) with hT
  have hTc : IsCompact T := ((hK.add hK).add hK).smul 3
  have hTsub : T ⊆ (10 : ℕ) • K := G54.T_subset h0K
  -- the box
  have hbd : ∀ k : ℕ, ∃ M : ℝ, ∀ x ∈ K, |x k| ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := (hK.image (continuous_abs.comp (continuous_apply k))).bddAbove
    exact ⟨M, fun x hx => hM ⟨x, hx, rfl⟩⟩
  choose M hM using hbd
  set B : Set (ℕ → ℝ) := {x | ∀ k, |x k| ≤ M k} with hB
  have hBeq : B = Set.pi univ (fun k => Icc (-(M k)) (M k)) := by
    ext x
    constructor
    · intro hx k _
      exact abs_le.mp (hx k)
    · intro hx k
      exact abs_le.mpr (hx k (mem_univ k))
  have hBc : IsCompact B := by
    rw [hBeq]
    exact isCompact_univ_pi (fun k => isCompact_Icc)
  have hBconv : Convex ℝ B := by
    rw [hBeq]
    exact convex_pi (fun k _ => convex_Icc _ _)
  have hKB : K ⊆ B := fun x hx k => hM k x hx
  have hBm : (0.99 : ℝ≥0∞) ≤ Green54.gaussianMeasureInf B := hKm.trans (measure_mono hKB)
  by_cases hcase : ∀ U : Set (ℕ → ℝ), IsOpen U → T ⊆ U →
      ∃ C : Set (ℕ → ℝ), C ⊆ U ∧ C ⊆ B ∧ Convex ℝ C ∧
        (0.01 : ℝ≥0∞) ≤ Green54.gaussianMeasureInf C
  · obtain ⟨C, hCc, hCconv, hCT, hCm⟩ :=
      G54.exists_convex_limit Green54.gaussianMeasureInf hBc hTc 0.01 hcase
    exact ⟨C, hCc, hCconv, hCT.trans hTsub, hCm⟩
  · exfalso
    have hcase' : ∃ U : Set (ℕ → ℝ), IsOpen U ∧ T ⊆ U ∧ ∀ C : Set (ℕ → ℝ), C ⊆ U → C ⊆ B →
        Convex ℝ C → ¬ (0.01 : ℝ≥0∞) ≤ Green54.gaussianMeasureInf C := by
      by_contra hcon
      apply hcase
      intro U hUo hTU
      by_contra hcon2
      exact hcon ⟨U, hUo, hTU, fun C h1 h2 h3 h4 => hcon2 ⟨C, h1, h2, h3, h4⟩⟩
    obtain ⟨U, hUo, hTU, hU⟩ := hcase'
    set Q : Set (ℕ → ℝ) := B ∩ Uᶜ with hQ
    have hQc : IsCompact Q := hBc.inter_right hUo.isClosed_compl
    -- every admissible `f` takes a value `≤ 3` on `Q`
    have hpt : ∀ f : (ℕ → ℝ) → ℝ, Continuous f → ConvexOn ℝ univ f → (∀ x, 0 ≤ f x) →
        f 0 = 0 → Integrable f Green54.gaussianMeasureInf →
        ∫ x, f x ∂Green54.gaussianMeasureInf ≤ 1 → ∃ x ∈ Q, f x ≤ 3 := by
      intro f hfc hfconv hf0 hfz hfi hf1
      by_contra hcon
      have hcon' : ∀ x ∈ Q, 3 < f x := by
        intro x hx
        by_contra hx3
        exact hcon ⟨x, hx, not_lt.mp hx3⟩
      have hDU : B ∩ {x | f x ≤ 3} ∩ {x | f (-x) ≤ 3} ⊆ U := by
        intro x hx
        by_contra hxU
        exact absurd (hcon' x ⟨hx.1.1, hxU⟩) (not_lt.mpr hx.1.2)
      have hDB : B ∩ {x | f x ≤ 3} ∩ {x | f (-x) ≤ 3} ⊆ B := fun x hx => hx.1.1
      have hconv' : ConvexOn ℝ univ (fun x : ℕ → ℝ => f (-x)) := by
        have := hfconv.comp_linearMap (-LinearMap.id : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ))
        simpa [Function.comp_def] using this
      have hDconv : Convex ℝ (B ∩ {x | f x ≤ 3} ∩ {x | f (-x) ≤ 3}) := by
        have h1 : Convex ℝ {x : ℕ → ℝ | f x ≤ 3} := by
          have := hfconv.convex_le 3
          simpa using this
        have h2 : Convex ℝ {x : ℕ → ℝ | f (-x) ≤ 3} := by
          have := hconv'.convex_le 3
          simpa using this
        exact (hBconv.inter h1).inter h2
      exact hU _ hDU hDB hDconv
        (G54.measure_D B hBc.measurableSet hBm f hfc hf0 hfi hf1)
    -- separation on the compact space `Q`
    have hQcs : CompactSpace Q := isCompact_iff_compactSpace.mp hQc
    set 𝒞 : Set C(Q, ℝ) := {g | ∃ f : (ℕ → ℝ) → ℝ, Continuous f ∧ ConvexOn ℝ univ f ∧
      (∀ x, 0 ≤ f x) ∧ f 0 = 0 ∧ Integrable f Green54.gaussianMeasureInf ∧
      ∫ x, f x ∂Green54.gaussianMeasureInf ≤ 1 ∧ ∀ x : Q, g x = f x} with h𝒞
    have h𝒞conv : Convex ℝ 𝒞 := by
      rintro g₁ ⟨f₁, hc₁, hv₁, hn₁, hz₁, hi₁, hl₁, he₁⟩ g₂ ⟨f₂, hc₂, hv₂, hn₂, hz₂, hi₂, hl₂, he₂⟩
        a b ha hb hab
      refine ⟨fun x => a * f₁ x + b * f₂ x,
        (continuous_const.mul hc₁).add (continuous_const.mul hc₂), ?_,
        fun x => add_nonneg (mul_nonneg ha (hn₁ x)) (mul_nonneg hb (hn₂ x)), by simp [hz₁, hz₂],
        (hi₁.const_mul a).add (hi₂.const_mul b), ?_, ?_⟩
      · have h1 := (hv₁.smul ha).add (hv₂.smul hb)
        exact h1
      · rw [integral_add (hi₁.const_mul a) (hi₂.const_mul b), integral_const_mul,
          integral_const_mul]
        nlinarith
      · intro x
        simp [he₁ x, he₂ x]
    have h𝒞0 : (0 : C(Q, ℝ)) ∈ 𝒞 :=
      ⟨fun _ => 0, continuous_const, convexOn_const 0 convex_univ, fun _ => le_rfl, rfl,
        integrable_zero _ _ _, by simp, fun _ => rfl⟩
    have h𝒞pt : ∀ g ∈ 𝒞, ∃ x, g x ≤ 3 := by
      rintro g ⟨f, hfc, hfconv, hf0, hfz, hfi, hf1, hgf⟩
      obtain ⟨x, hxQ, hx⟩ := hpt f hfc hfconv hf0 hfz hfi hf1
      exact ⟨⟨x, hxQ⟩, by rw [hgf]; exact hx⟩
    obtain ⟨μQ, hμQ1, hμQ⟩ := G54.exists_measure_of_separation 𝒞 h𝒞conv h𝒞0 h𝒞pt
    set ν : Measure (ℕ → ℝ) := μQ.map Subtype.val with hνdef
    have hν1 : IsProbabilityMeasure ν :=
      Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
    have hνQ : ν Qᶜ = 0 := by
      rw [hνdef, Measure.map_apply measurable_subtype_coe hQc.measurableSet.compl]
      have : (Subtype.val : Q → (ℕ → ℝ)) ⁻¹' Qᶜ = ∅ := by
        ext x
        simp
      rw [this, measure_empty]
    have hν : ∀ f : (ℕ → ℝ) → ℝ, Continuous f → ConvexOn ℝ univ f → (∀ x, 0 ≤ f x) → f 0 = 0 →
        Integrable f Green54.gaussianMeasureInf → ∫ x, f x ∂Green54.gaussianMeasureInf ≤ 1 →
        ∫ x, f x ∂ν ≤ 3 := by
      intro f hfc hfconv hf0 hfz hfi hf1
      rw [hνdef, integral_map measurable_subtype_coe.aemeasurable hfc.aestronglyMeasurable]
      exact hμQ ⟨fun x => f x, hfc.comp continuous_subtype_val⟩
        ⟨f, hfc, hfconv, hf0, hfz, hfi, hf1, fun _ => rfl⟩
    have hhalf := G54.half_le_T hL hK hKb hKm ν hQc hνQ hν
    have hTQ : T ⊆ Qᶜ := fun x hx hxQ => hxQ.2 (hTU hx)
    have hT0 : ν T = 0 := measure_mono_null hTQ hνQ
    rw [hT0] at hhalf
    simp at hhalf

end ModMain

section ModThree

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/-- **The Three Gaussians theorem** (Hua–Song–Tudose, arXiv:2605.10908, Theorem 1.1), stated for
compactly supported laws: a probability measure `μ` on `ℝⁿ` which is dominated in the convex order
by the standard Gaussian measure `γₙ` is the law of a sum `G₁ + G₂ + G₃` of three (coupled) standard
Gaussian vectors.  The coupling is encoded by a measure `π` on `ℝⁿ × ℝⁿ × ℝⁿ` whose three marginals
are `γₙ` and whose image under `(x, y, z) ↦ x + y + z` is `μ`. -/
def G54.ThreeGaussians : Prop :=
  ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), IsProbabilityMeasure μ →
    (∃ S : Set (Fin n → ℝ), IsCompact S ∧ μ Sᶜ = 0) →
    (∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
      Integrable f (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) →
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)),
      π.map (fun p => p.1) = Measure.pi (fun _ : Fin n => gaussianReal 0 1) ∧
      π.map (fun p => p.2.1) = Measure.pi (fun _ : Fin n => gaussianReal 0 1) ∧
      π.map (fun p => p.2.2) = Measure.pi (fun _ : Fin n => gaussianReal 0 1) ∧
      π.map (fun p => p.1 + p.2.1 + p.2.2) = μ

/-- The union bound: a sum of three standard Gaussian vectors lands in `A + A + A` with
probability at least `1 - 3 (1 - γₙ(A))`. -/
theorem G54.landing_of_threeGaussians (h3 : G54.ThreeGaussians) :
    ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), IsProbabilityMeasure μ →
      (∃ S : Set (Fin n → ℝ), IsCompact S ∧ μ Sᶜ = 0) →
      (∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
        Integrable f (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
        ∫ x, f x ∂μ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) →
      ∀ A : Set (Fin n → ℝ), IsCompact A → Balanced ℝ A →
        (0.99 : ℝ≥0∞) ≤ (Measure.pi fun _ : Fin n => gaussianReal 0 1) A →
        (1 / 2 : ℝ≥0∞) ≤ μ (A + A + A) := by
  intro n μ hμ hcpt hdom A hAc _ hAm
  obtain ⟨π, h1, h2, h3', h4⟩ := h3 n μ hμ hcpt hdom
  set γn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1) with hγn
  have hγn1 : IsProbabilityMeasure γn := by rw [hγn]; infer_instance
  have hf1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.1) := measurable_fst
  have hf2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hf3 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.2.2) :=
    measurable_snd.comp measurable_snd
  have hsum : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.1 + p.2.1 + p.2.2) :=
    (hf1.add hf2).add hf3
  have hπ1 : IsProbabilityMeasure π := by
    constructor
    have := Measure.map_apply (μ := π) hf1 MeasurableSet.univ
    rw [h1, measure_univ] at this
    simpa using this.symm
  have hAmeas : MeasurableSet A := hAc.measurableSet
  have hAr : (0.99 : ℝ) ≤ γn.real A := G54.le_real_of_ofScientific_le γn A _ _ _ hAm
  have hAcr : γn.real Aᶜ ≤ 0.01 := by
    rw [probReal_compl_eq_one_sub hAmeas]
    linarith
  -- the three bad events
  have hb1 : π.real ((fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.1) ⁻¹' Aᶜ)
      = γn.real Aᶜ := by
    rw [measureReal_def, ← Measure.map_apply hf1 hAmeas.compl, h1, measureReal_def]
  have hb2 : π.real ((fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.2.1) ⁻¹' Aᶜ)
      = γn.real Aᶜ := by
    rw [measureReal_def, ← Measure.map_apply hf2 hAmeas.compl, h2, measureReal_def]
  have hb3 : π.real ((fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.2.2) ⁻¹' Aᶜ)
      = γn.real Aᶜ := by
    rw [measureReal_def, ← Measure.map_apply hf3 hAmeas.compl, h3', measureReal_def]
  set S : Set ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) :=
    (fun p => p.1 + p.2.1 + p.2.2) ⁻¹' (A + A + A) with hS
  have hAAA : IsCompact (A + A + A) := (hAc.add hAc).add hAc
  have hSm : MeasurableSet S := hsum hAAA.measurableSet
  have hsub : Sᶜ ⊆ ((fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.1) ⁻¹' Aᶜ)
      ∪ ((fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.2.1) ⁻¹' Aᶜ)
      ∪ ((fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.2.2) ⁻¹' Aᶜ) := by
    intro p hp
    by_contra hcon
    have ha : p.1 ∈ A := by
      by_contra h
      exact hcon (Or.inl (Or.inl h))
    have hb : p.2.1 ∈ A := by
      by_contra h
      exact hcon (Or.inl (Or.inr h))
    have hc : p.2.2 ∈ A := by
      by_contra h
      exact hcon (Or.inr h)
    exact hp (add_mem_add (add_mem_add ha hb) hc)
  have hSc : π.real Sᶜ ≤ 0.03 := by
    have := (measureReal_mono (μ := π) hsub).trans ((measureReal_union_le _ _).trans
      (add_le_add_left (measureReal_union_le _ _) _))
    rw [hb1, hb2, hb3] at this
    linarith
  have hSr : (0.97 : ℝ) ≤ π.real S := by
    have := probReal_compl_eq_one_sub (μ := π) hSm
    linarith
  have hμS : μ.real (A + A + A) = π.real S := by
    rw [measureReal_def, ← h4, Measure.map_apply hsum hAAA.measurableSet, measureReal_def]
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos]
    simp
  rw [hhalf, ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _), ← measureReal_def, hμS]
  linarith

/-- **Green's Problem 54 (Talagrand's convexity conjecture), conditional on the Three Gaussians
theorem.** -/
theorem G54.green54_of_threeGaussians (h3 : G54.ThreeGaussians) :
    type_of% @Green54.green_54 :=
  G54.green54_of_landing (G54.landing_of_threeGaussians h3)

end ModThree

section ModLse

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/- ### The log-sum-exp function `a ↦ log (∑ i, p i * exp (a i))` -/

theorem G54.lse_sum_pos {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (a : ι → ℝ) : 0 < ∑ i, p i * Real.exp (a i) :=
  Finset.sum_pos (fun i _ => mul_pos (hp i) (Real.exp_pos _)) Finset.univ_nonempty

theorem G54.lse_ge {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (a : ι → ℝ) (j : ι) :
    a j + Real.log (p j) ≤ Real.log (∑ i, p i * Real.exp (a i)) := by
  have h1 : a j + Real.log (p j) = Real.log (p j * Real.exp (a j)) := by
    rw [Real.log_mul (hp j).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [h1]
  apply Real.log_le_log (mul_pos (hp j) (Real.exp_pos _))
  exact Finset.single_le_sum (f := fun i => p i * Real.exp (a i))
    (fun i _ => (mul_pos (hp i) (Real.exp_pos _)).le) (Finset.mem_univ j)

theorem G54.lse_le_add {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (a b : ι → ℝ) (s : ℝ) (h : ∀ i, a i ≤ b i + s) :
    Real.log (∑ i, p i * Real.exp (a i)) ≤ Real.log (∑ i, p i * Real.exp (b i)) + s := by
  have h1 : Real.log (∑ i, p i * Real.exp (b i)) + s
      = Real.log ((∑ i, p i * Real.exp (b i)) * Real.exp s) := by
    rw [Real.log_mul (G54.lse_sum_pos p hp b).ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [h1]
  apply Real.log_le_log (G54.lse_sum_pos p hp a)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h i)) (hp i).le

theorem G54.lse_le_of_le {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1) (a : ι → ℝ) (c : ℝ) (h : ∀ i, a i ≤ c) :
    Real.log (∑ i, p i * Real.exp (a i)) ≤ c := by
  have h1 := G54.lse_le_add p hp a (fun _ => 0) c (fun i => by simpa using h i)
  simpa [hp1] using h1

/-- Hölder's inequality in logarithmic form: log-sum-exp is convex. -/
theorem G54.lse_convex {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    ConvexOn ℝ univ (fun a : ι → ℝ => Real.log (∑ i, p i * Real.exp (a i))) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ lam mu hlam hmu hlm
  set X : ℝ := ∑ i, p i * Real.exp (a i) with hX
  set Y : ℝ := ∑ i, p i * Real.exp (b i) with hY
  have hXpos : 0 < X := G54.lse_sum_pos p hp a
  have hYpos : 0 < Y := G54.lse_sum_pos p hp b
  have hterm : ∀ i, p i * Real.exp ((lam • a + mu • b) i)
      ≤ Real.exp (lam * Real.log X + mu * Real.log Y)
        * (lam * (p i * Real.exp (a i) / X) + mu * (p i * Real.exp (b i) / Y)) := by
    intro i
    have hconv := convexOn_exp.2 (mem_univ (a i - Real.log X)) (mem_univ (b i - Real.log Y))
      hlam hmu hlm
    simp only [smul_eq_mul] at hconv
    have h1 : (lam • a + mu • b) i
        = (lam * (a i - Real.log X) + mu * (b i - Real.log Y))
          + (lam * Real.log X + mu * Real.log Y) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1, Real.exp_add]
    have h2 : Real.exp (a i - Real.log X) = Real.exp (a i) / X := by
      rw [Real.exp_sub, Real.exp_log hXpos]
    have h3 : Real.exp (b i - Real.log Y) = Real.exp (b i) / Y := by
      rw [Real.exp_sub, Real.exp_log hYpos]
    rw [h2, h3] at hconv
    have h4 : p i * (Real.exp (lam * (a i - Real.log X) + mu * (b i - Real.log Y))
        * Real.exp (lam * Real.log X + mu * Real.log Y))
        ≤ p i * ((lam * (Real.exp (a i) / X) + mu * (Real.exp (b i) / Y))
          * Real.exp (lam * Real.log X + mu * Real.log Y)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hconv (Real.exp_pos _).le) (hp i).le
    refine h4.trans (le_of_eq ?_)
    ring
  have hsum : ∑ i, p i * Real.exp ((lam • a + mu • b) i)
      ≤ Real.exp (lam * Real.log X + mu * Real.log Y) := by
    calc ∑ i, p i * Real.exp ((lam • a + mu • b) i)
        ≤ ∑ i, Real.exp (lam * Real.log X + mu * Real.log Y)
          * (lam * (p i * Real.exp (a i) / X) + mu * (p i * Real.exp (b i) / Y)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = Real.exp (lam * Real.log X + mu * Real.log Y)
          * (lam * (X / X) + mu * (Y / Y)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.sum_div, ← Finset.sum_div]
      _ = Real.exp (lam * Real.log X + mu * Real.log Y) := by
          rw [div_self hXpos.ne', div_self hYpos.ne', mul_one, mul_one, hlm, mul_one]
  have hfin := Real.log_le_log (G54.lse_sum_pos p hp (lam • a + mu • b)) hsum
  rw [Real.log_exp] at hfin
  simpa [smul_eq_mul] using hfin

/-- Derivative of log-sum-exp along a line. -/
theorem G54.lse_hasDerivAt {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (a b : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (∑ i, p i * Real.exp (a i + t * b i)))
      ((∑ i, b i * (p i * Real.exp (a i + t * b i))) / (∑ i, p i * Real.exp (a i + t * b i)))
      t := by
  have hpos : 0 < ∑ i, p i * Real.exp (a i + t * b i) :=
    G54.lse_sum_pos p hp (fun i => a i + t * b i)
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), HasDerivAt
      (fun t : ℝ => p i * Real.exp (a i + t * b i))
      (b i * (p i * Real.exp (a i + t * b i))) t := by
    intro i _
    have h1 : HasDerivAt (fun t : ℝ => a i + t * b i) (b i) t := by
      simpa using ((hasDerivAt_id t).mul_const (b i)).const_add (a i)
    have h2 := (h1.exp).const_mul (p i)
    have h3 : b i * (p i * Real.exp (a i + t * b i))
        = p i * (Real.exp (a i + t * b i) * b i) := by ring
    rw [h3]
    exact h2
  have hsum := HasDerivAt.fun_sum hterm
  exact hsum.log hpos.ne'

end ModLse

section ModSoft1

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

theorem G54.abs_dot_le {ι : Type*} [Fintype ι] {d : ℕ} (θ : ι → Fin d → ℝ) (i : ι)
    (v : Fin d → ℝ) : |∑ k, θ i k * v k| ≤ ‖θ‖ * ∑ k, |v k| := by
  calc |∑ k, θ i k * v k| ≤ ∑ k, |θ i k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ‖θ‖ * |v k| := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        calc |θ i k| = ‖θ i k‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖θ i‖ := norm_le_pi_norm (θ i) k
          _ ≤ ‖θ‖ := norm_le_pi_norm θ i
    _ = ‖θ‖ * ∑ k, |v k| := by rw [Finset.mul_sum]

theorem G54.measurable_sup' {Y : Type*} [MeasurableSpace Y] {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : Y → ι → ℝ) (hf : ∀ i, Measurable (fun y => f y i)) :
    Measurable (fun y => Finset.univ.sup' Finset.univ_nonempty (f y)) := by
  have h := Finset.measurable_sup' (s := (Finset.univ : Finset ι)) Finset.univ_nonempty
    (f := fun i y => f y i) (fun i _ => hf i)
  have heq : (fun y => Finset.univ.sup' Finset.univ_nonempty (f y))
      = Finset.univ.sup' Finset.univ_nonempty (fun i y => f y i) := by
    funext y
    rw [Finset.sup'_apply]
  rw [heq]
  exact h

/-- **Existence of the entropy maximiser.**  The concave dual functional
`g(θ) = ∑ᵢ pᵢ ⟨θᵢ, tᵢ⟩ - ∫ log ∑ⱼ pⱼ exp ⟨θⱼ, T y⟩ dγ(y)` attains its maximum, provided it is
coercive on the gauge-fixed subspace `∑ᵢ pᵢ θᵢ = 0` (hypothesis `hc`) and the first moments match
(hypothesis `hm`, which makes `g` invariant under the gauge `θᵢ ↦ θᵢ + c`). -/
theorem G54.softmax_max {Y : Type*} [MeasurableSpace Y] (γ : Measure Y) [IsProbabilityMeasure γ]
    {d : ℕ} (T : Y → Fin d → ℝ) (hTm : Measurable T) (hTi : ∀ k, Integrable (fun y => T y k) γ)
    {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (t : ι → Fin d → ℝ)
    (hm : ∀ k, ∫ y, T y k ∂γ = ∑ i, p i * t i k)
    (hc : ∃ c : ℝ, 0 < c ∧ ∀ θ : ι → Fin d → ℝ, (∀ k, ∑ i, p i * θ i k = 0) →
      c * ‖θ‖ ≤ ∫ y, (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k) ∂γ
        - ∑ i, p i * ∑ k, θ i k * t i k) :
    ∃ θs : ι → Fin d → ℝ, ∀ θ : ι → Fin d → ℝ,
      (∑ i, p i * ∑ k, θ i k * t i k)
          - ∫ y, Real.log (∑ j, p j * Real.exp (∑ k, θ j k * T y k)) ∂γ
        ≤ (∑ i, p i * ∑ k, θs i k * t i k)
          - ∫ y, Real.log (∑ j, p j * Real.exp (∑ k, θs j k * T y k)) ∂γ := by
  classical
  obtain ⟨c, hc0, hcS⟩ := hc
  set N : Y → ℝ := fun y => ∑ k, |T y k| with hN
  have hNi : Integrable N γ := integrable_finsetSum _ (fun k _ => (hTi k).abs)
  have hN0 : ∀ y, 0 ≤ N y := fun y => Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hTkm : ∀ k, Measurable (fun y => T y k) := fun k => (measurable_pi_apply k).comp hTm
  set A : (ι → Fin d → ℝ) → Y → ι → ℝ := fun θ y i => ∑ k, θ i k * T y k with hA
  have hAm : ∀ θ i, Measurable (fun y => A θ y i) := fun θ i =>
    Finset.measurable_sum _ (fun k _ => (hTkm k).const_mul _)
  have hAbd : ∀ θ y i, |A θ y i| ≤ ‖θ‖ * N y := fun θ y i => G54.abs_dot_le θ i (T y)
  have hAsub : ∀ θ θ' y i, A θ y i - A θ' y i = A (θ - θ') y i := by
    intro θ θ' y i
    simp only [hA, Pi.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  set Ψ : (ι → Fin d → ℝ) → Y → ℝ := fun θ y => Real.log (∑ j, p j * Real.exp (A θ y j))
    with hΨ
  have hΨm : ∀ θ, Measurable (Ψ θ) := fun θ =>
    Real.measurable_log.comp (Finset.measurable_sum _ fun j _ =>
      (Real.measurable_exp.comp (hAm θ j)).const_mul _)
  have hΨlip : ∀ θ θ' y, |Ψ θ y - Ψ θ' y| ≤ ‖θ - θ'‖ * N y := by
    intro θ θ' y
    have hdiff : ∀ i, |A θ y i - A θ' y i| ≤ ‖θ - θ'‖ * N y := by
      intro i
      rw [hAsub]
      exact hAbd _ _ _
    rw [abs_le]
    constructor
    · have h1 := G54.lse_le_add p hp (A θ' y) (A θ y) (‖θ - θ'‖ * N y) (fun i => by
        linarith [(abs_le.mp (hdiff i)).1])
      simp only [hΨ]
      linarith
    · have h1 := G54.lse_le_add p hp (A θ y) (A θ' y) (‖θ - θ'‖ * N y) (fun i => by
        linarith [(abs_le.mp (hdiff i)).2])
      simp only [hΨ]
      linarith
  have hΨ0 : ∀ y, Ψ 0 y = 0 := by
    intro y
    simp [hΨ, hA, hp1]
  have hΨbd : ∀ θ y, |Ψ θ y| ≤ ‖θ‖ * N y := by
    intro θ y
    have h1 := hΨlip θ 0 y
    rw [hΨ0, sub_zero, sub_zero] at h1
    exact h1
  have hΨi : ∀ θ, Integrable (Ψ θ) γ := fun θ =>
    (hNi.const_mul ‖θ‖).mono' (hΨm θ).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        exact hΨbd θ y)
  set lin : (ι → Fin d → ℝ) → ℝ := fun θ => ∑ i, p i * ∑ k, θ i k * t i k with hlin
  set g : (ι → Fin d → ℝ) → ℝ := fun θ => lin θ - ∫ y, Ψ θ y ∂γ with hg
  -- continuity of `g`
  have hlinc : Continuous lin := by
    simp only [hlin]
    fun_prop
  have hintc : Continuous (fun θ : ι → Fin d → ℝ => ∫ y, Ψ θ y ∂γ) := by
    have hK : (0 : ℝ) ≤ ∫ y, N y ∂γ := integral_nonneg hN0
    have hlip : LipschitzWith ⟨∫ y, N y ∂γ, hK⟩ (fun θ : ι → Fin d → ℝ => ∫ y, Ψ θ y ∂γ) := by
      apply LipschitzWith.of_dist_le_mul
      intro θ θ'
      rw [Real.dist_eq, dist_eq_norm, ← integral_sub (hΨi θ) (hΨi θ')]
      calc |∫ y, (Ψ θ y - Ψ θ' y) ∂γ| ≤ ∫ y, |Ψ θ y - Ψ θ' y| ∂γ := abs_integral_le_integral_abs
        _ ≤ ∫ y, ‖θ - θ'‖ * N y ∂γ :=
            integral_mono ((hΨi θ).sub (hΨi θ')).abs (hNi.const_mul _) (fun y => hΨlip θ θ' y)
        _ = (∫ y, N y ∂γ) * ‖θ - θ'‖ := by rw [integral_const_mul, mul_comm]
    exact hlip.continuous
  have hgc : Continuous g := hlinc.sub hintc
  -- the value at `0`
  have hg0 : g 0 = 0 := by
    simp [hg, hlin, hΨ0]
  -- gauge invariance
  have hgauge : ∀ (θ : ι → Fin d → ℝ) (v : Fin d → ℝ), g (fun i k => θ i k - v k) = g θ := by
    intro θ v
    set s : Y → ℝ := fun y => ∑ k, v k * T y k with hs
    have hsi : Integrable s γ := integrable_finsetSum _ (fun k _ => (hTi k).const_mul _)
    have hAshift : ∀ y i, A (fun i k => θ i k - v k) y i = A θ y i - s y := by
      intro y i
      simp only [hA, hs, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hΨshift : ∀ y, Ψ (fun i k => θ i k - v k) y = Ψ θ y - s y := by
      intro y
      simp only [hΨ]
      have h1 : ∑ j, p j * Real.exp (A (fun i k => θ i k - v k) y j)
          = (∑ j, p j * Real.exp (A θ y j)) * Real.exp (-(s y)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hAshift, sub_eq_add_neg, Real.exp_add]
        ring
      rw [h1, Real.log_mul (G54.lse_sum_pos p hp _).ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    have hint : ∫ y, Ψ (fun i k => θ i k - v k) y ∂γ = ∫ y, Ψ θ y ∂γ - ∫ y, s y ∂γ := by
      rw [← integral_sub (hΨi θ) hsi]
      exact integral_congr_ae (Eventually.of_forall hΨshift)
    have hsint : ∫ y, s y ∂γ = ∑ k, v k * ∑ i, p i * t i k := by
      simp only [hs]
      rw [integral_finsetSum _ (fun k _ => (hTi k).const_mul _)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, hm k]
    have hlinshift : lin (fun i k => θ i k - v k) = lin θ - ∑ k, v k * ∑ i, p i * t i k := by
      simp only [hlin]
      have h1 : ∑ k, v k * ∑ i, p i * t i k = ∑ i, p i * ∑ k, v k * t i k := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [h1, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    simp only [hg]
    rw [hint, hsint, hlinshift]
    ring
  -- the upper bound on the gauge-fixed subspace
  set pmin : ℝ := Finset.univ.inf' Finset.univ_nonempty p with hpmin
  have hpmin0 : 0 < pmin := by
    rw [hpmin, Finset.lt_inf'_iff]
    exact fun i _ => hp i
  have hsupm : ∀ θ, Measurable (fun y => Finset.univ.sup' Finset.univ_nonempty (A θ y)) :=
    fun θ => G54.measurable_sup' (fun y => A θ y) (hAm θ)
  have hsupbd : ∀ θ y, |Finset.univ.sup' Finset.univ_nonempty (A θ y)| ≤ ‖θ‖ * N y := by
    intro θ y
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (A θ y)
    rw [hi₀]
    exact hAbd θ y i₀
  have hsupi : ∀ θ, Integrable (fun y => Finset.univ.sup' Finset.univ_nonempty (A θ y)) γ :=
    fun θ => (hNi.const_mul ‖θ‖).mono' (hsupm θ).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        exact hsupbd θ y)
  have hΨlow : ∀ θ y, Finset.univ.sup' Finset.univ_nonempty (A θ y) + Real.log pmin ≤ Ψ θ y := by
    intro θ y
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (A θ y)
    rw [hi₀]
    have h1 := G54.lse_ge p hp (A θ y) i₀
    have h2 : Real.log pmin ≤ Real.log (p i₀) :=
      Real.log_le_log hpmin0 (Finset.inf'_le _ (Finset.mem_univ i₀))
    simp only [hΨ]
    linarith
  have hupper : ∀ θ : ι → Fin d → ℝ, (∀ k, ∑ i, p i * θ i k = 0) →
      g θ ≤ -(c * ‖θ‖) - Real.log pmin := by
    intro θ hθ
    have h1 := hcS θ hθ
    have h2 : ∫ y, (Finset.univ.sup' Finset.univ_nonempty (A θ y) + Real.log pmin) ∂γ
        ≤ ∫ y, Ψ θ y ∂γ :=
      integral_mono ((hsupi θ).add (integrable_const _)) (hΨi θ) (fun y => hΨlow θ y)
    rw [integral_add (hsupi θ) (integrable_const _)] at h2
    simp only [integral_const, probReal_univ, one_smul] at h2
    simp only [hg, hlin]
    linarith
  -- maximise over a compact piece of the gauge-fixed subspace
  set S : Set (ι → Fin d → ℝ) := {θ | ∀ k, ∑ i, p i * θ i k = 0} with hS
  have hSclosed : IsClosed S := by
    have : S = ⋂ k : Fin d, {θ : ι → Fin d → ℝ | ∑ i, p i * θ i k = 0} := by
      ext θ
      simp [hS]
    rw [this]
    refine isClosed_iInter fun k => isClosed_eq ?_ continuous_const
    fun_prop
  set r : ℝ := (-Real.log pmin) / c with hr
  have hcomp : IsCompact (S ∩ Metric.closedBall (0 : ι → Fin d → ℝ) r) :=
    (isCompact_closedBall _ _).inter_left hSclosed
  have h0S : (0 : ι → Fin d → ℝ) ∈ S := by
    intro k
    simp
  have hupper0 := hupper 0 h0S
  rw [hg0, norm_zero, mul_zero, neg_zero, zero_sub] at hupper0
  have hr0 : 0 ≤ r := div_nonneg hupper0 hc0.le
  have hne : (S ∩ Metric.closedBall (0 : ι → Fin d → ℝ) r).Nonempty :=
    ⟨0, h0S, Metric.mem_closedBall_self hr0⟩
  obtain ⟨θs, hθs, hmax⟩ := hcomp.exists_isMaxOn hne hgc.continuousOn
  have hmaxS : ∀ θ ∈ S, g θ ≤ g θs := by
    intro θ hθ
    by_cases hball : θ ∈ Metric.closedBall (0 : ι → Fin d → ℝ) r
    · exact hmax ⟨hθ, hball⟩
    · have h1 : r < ‖θ‖ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hball
        exact not_le.mp hball
      have h2 := hupper θ hθ
      have h3 : -Real.log pmin < c * ‖θ‖ := by
        rw [hr, div_lt_iff₀ hc0] at h1
        linarith
      have h4 : g 0 ≤ g θs := hmax ⟨h0S, Metric.mem_closedBall_self hr0⟩
      rw [hg0] at h4
      linarith
  refine ⟨θs, fun θ => ?_⟩
  -- reduce an arbitrary `θ` to the gauge-fixed subspace
  set v : Fin d → ℝ := fun k => ∑ i, p i * θ i k with hv
  have hmem : (fun i k => θ i k - v k) ∈ S := by
    intro k
    have h1 : ∑ i, p i * (θ i k - v k) = ∑ i, p i * θ i k - (∑ i, p i) * v k := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h1, hp1, one_mul]
    simp [hv]
  have h1 := hmaxS _ hmem
  rw [hgauge θ v] at h1
  exact h1

end ModSoft1

section ModSoft2

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

theorem G54.abs_lse_dot_le {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1) {d : ℕ} (θ : ι → Fin d → ℝ) (v : Fin d → ℝ) :
    |Real.log (∑ j, p j * Real.exp (∑ k, θ j k * v k))| ≤ ‖θ‖ * ∑ k, |v k| := by
  have hb : ∀ j, |∑ k, θ j k * v k| ≤ ‖θ‖ * ∑ k, |v k| := fun j => G54.abs_dot_le θ j v
  rw [abs_le]
  constructor
  · have h1 := G54.lse_le_add p hp (fun _ => -(‖θ‖ * ∑ k, |v k|)) (fun j => ∑ k, θ j k * v k) 0
      (fun j => by
        have := (abs_le.mp (hb j)).1
        linarith)
    have h2 : Real.log (∑ i, p i * Real.exp (-(‖θ‖ * ∑ k, |v k|))) = -(‖θ‖ * ∑ k, |v k|) := by
      rw [← Finset.sum_mul, hp1, one_mul, Real.log_exp]
    rw [h2] at h1
    linarith
  · exact G54.lse_le_of_le p hp hp1 _ _ (fun j => (abs_le.mp (hb j)).2)

/-- **First-order conditions at the entropy maximiser**: the softmax weights reproduce the
prescribed moments. -/
theorem G54.softmax_stationary {Y : Type*} [MeasurableSpace Y] (γ : Measure Y)
    [IsProbabilityMeasure γ] {d : ℕ} (T : Y → Fin d → ℝ) (hTm : Measurable T)
    (hTi : ∀ k, Integrable (fun y => T y k) γ)
    {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (t : ι → Fin d → ℝ) (θs : ι → Fin d → ℝ)
    (hmax : ∀ θ : ι → Fin d → ℝ,
      (∑ i, p i * ∑ k, θ i k * t i k)
          - ∫ y, Real.log (∑ j, p j * Real.exp (∑ k, θ j k * T y k)) ∂γ
        ≤ (∑ i, p i * ∑ k, θs i k * t i k)
          - ∫ y, Real.log (∑ j, p j * Real.exp (∑ k, θs j k * T y k)) ∂γ)
    (i₀ : ι) (k₀ : Fin d) :
    ∫ y, T y k₀ * (p i₀ * Real.exp (∑ k, θs i₀ k * T y k)
      / ∑ j, p j * Real.exp (∑ k, θs j k * T y k)) ∂γ = p i₀ * t i₀ k₀ := by
  classical
  have hTkm : ∀ k, Measurable (fun y => T y k) := fun k => (measurable_pi_apply k).comp hTm
  set a : Y → ι → ℝ := fun y j => ∑ k, θs j k * T y k with ha
  set b : Y → ι → ℝ := fun y j => if j = i₀ then T y k₀ else 0 with hb
  have ham : ∀ j, Measurable (fun y => a y j) := fun j =>
    Finset.measurable_sum _ (fun k _ => (hTkm k).const_mul _)
  have hbm : ∀ j, Measurable (fun y => b y j) := by
    intro j
    simp only [hb]
    split_ifs
    · exact hTkm k₀
    · exact measurable_const
  set F : ℝ → Y → ℝ := fun s y => Real.log (∑ j, p j * Real.exp (a y j + s * b y j)) with hF
  set F' : ℝ → Y → ℝ := fun s y => (∑ j, b y j * (p j * Real.exp (a y j + s * b y j)))
    / (∑ j, p j * Real.exp (a y j + s * b y j)) with hF'
  have hFm : ∀ s, Measurable (F s) := fun s =>
    Real.measurable_log.comp (Finset.measurable_sum _ fun j _ =>
      (Real.measurable_exp.comp ((ham j).add ((hbm j).const_mul s))).const_mul _)
  have hF'm : ∀ s, Measurable (F' s) := fun s =>
    (Finset.measurable_sum _ fun j _ => (hbm j).mul
      ((Real.measurable_exp.comp ((ham j).add ((hbm j).const_mul s))).const_mul _)).div
    (Finset.measurable_sum _ fun j _ =>
      (Real.measurable_exp.comp ((ham j).add ((hbm j).const_mul s))).const_mul _)
  -- the numerator of `F'`
  have hnum : ∀ s y, (∑ j, b y j * (p j * Real.exp (a y j + s * b y j)))
      = T y k₀ * (p i₀ * Real.exp (a y i₀ + s * b y i₀)) := by
    intro s y
    have h1 : ∀ j ∈ (Finset.univ : Finset ι), j ≠ i₀ →
        b y j * (p j * Real.exp (a y j + s * b y j)) = 0 := by
      intro j _ hj
      simp only [hb, if_neg hj, zero_mul]
    rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀) h1]
    simp only [hb, if_true]
  have hF'bd : ∀ s y, ‖F' s y‖ ≤ |T y k₀| := by
    intro s y
    have hpos : 0 < ∑ j, p j * Real.exp (a y j + s * b y j) :=
      G54.lse_sum_pos p hp (fun j => a y j + s * b y j)
    have hterm : p i₀ * Real.exp (a y i₀ + s * b y i₀)
        ≤ ∑ j, p j * Real.exp (a y j + s * b y j) :=
      Finset.single_le_sum (f := fun j => p j * Real.exp (a y j + s * b y j))
        (fun j _ => (mul_pos (hp j) (Real.exp_pos _)).le) (Finset.mem_univ i₀)
    have hterm0 : 0 ≤ p i₀ * Real.exp (a y i₀ + s * b y i₀) :=
      (mul_pos (hp i₀) (Real.exp_pos _)).le
    simp only [hF']
    rw [hnum, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hpos, abs_of_nonneg hterm0,
      div_le_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left hterm (abs_nonneg _)
  -- integrability of `F 0`
  have hF0 : ∀ y, F 0 y = Real.log (∑ j, p j * Real.exp (∑ k, θs j k * T y k)) := by
    intro y
    simp only [hF, ha, zero_mul, add_zero]
  have hF0i : Integrable (F 0) γ := by
    have hNi : Integrable (fun y => ‖θs‖ * ∑ k, |T y k|) γ :=
      (integrable_finsetSum _ (fun k _ => (hTi k).abs)).const_mul _
    refine hNi.mono' (hFm 0).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, hF0]
    exact G54.abs_lse_dot_le p hp hp1 θs (T y)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ) (F := F) (F' := F')
    (x₀ := (0 : ℝ)) (s := univ) (bound := fun y => |T y k₀|) univ_mem
    (Eventually.of_forall fun s => (hFm s).aestronglyMeasurable) hF0i
    (hF'm 0).aestronglyMeasurable
    (Eventually.of_forall fun y s _ => hF'bd s y) (hTi k₀).abs
    (Eventually.of_forall fun y s _ => G54.lse_hasDerivAt p hp (a y) (b y) s)
  obtain ⟨-, hder⟩ := hderiv
  -- the one-parameter family through `θs`
  set φ : ℝ → ℝ := fun s => (∑ i, p i * ∑ k, θs i k * t i k) + s * (p i₀ * t i₀ k₀)
    - ∫ y, F s y ∂γ with hφ
  have hφder : HasDerivAt φ (p i₀ * t i₀ k₀ - ∫ y, F' 0 y ∂γ) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (∑ i, p i * ∑ k, θs i k * t i k) + s * (p i₀ * t i₀ k₀))
        (p i₀ * t i₀ k₀) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (p i₀ * t i₀ k₀)).const_add
        (∑ i, p i * ∑ k, θs i k * t i k)
    exact h1.sub hder
  have hφmax : ∀ s, φ s ≤ φ 0 := by
    intro s
    set θ : ι → Fin d → ℝ := fun i k => θs i k + s * (if i = i₀ ∧ k = k₀ then 1 else 0) with hθ
    have hAθ : ∀ y j, ∑ k, θ j k * T y k = a y j + s * b y j := by
      intro y j
      simp only [hθ, ha, hb, add_mul, Finset.sum_add_distrib]
      congr 1
      by_cases hj : j = i₀
      · subst hj
        simp only [true_and, if_true]
        rw [Finset.sum_eq_single_of_mem k₀ (Finset.mem_univ k₀)]
        · simp
        · intro k _ hk
          simp [hk]
      · simp [hj]
    have hlinθ : ∑ i, p i * ∑ k, θ i k * t i k
        = (∑ i, p i * ∑ k, θs i k * t i k) + s * (p i₀ * t i₀ k₀) := by
      simp only [hθ, add_mul, Finset.sum_add_distrib, mul_add]
      congr 1
      rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)]
      · rw [Finset.sum_eq_single_of_mem k₀ (Finset.mem_univ k₀)]
        · simp
          ring
        · intro k _ hk
          simp [hk]
      · intro i _ hi
        simp [hi]
    have h1 := hmax θ
    rw [hlinθ] at h1
    have h2 : ∫ y, Real.log (∑ j, p j * Real.exp (∑ k, θ j k * T y k)) ∂γ = ∫ y, F s y ∂γ := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hF]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hAθ]
    have h3 : ∫ y, Real.log (∑ j, p j * Real.exp (∑ k, θs j k * T y k)) ∂γ = ∫ y, F 0 y ∂γ :=
      integral_congr_ae (Eventually.of_forall fun y => (hF0 y).symm)
    rw [h2, h3] at h1
    simp only [hφ, zero_mul, add_zero]
    exact h1
  have hloc : IsLocalMax φ 0 := Eventually.of_forall hφmax
  have hzero := hloc.hasDerivAt_eq_zero hφder
  have hF'0 : ∀ y, F' 0 y = T y k₀ * (p i₀ * Real.exp (∑ k, θs i₀ k * T y k)
      / ∑ j, p j * Real.exp (∑ k, θs j k * T y k)) := by
    intro y
    simp only [hF']
    rw [hnum]
    simp only [ha, zero_mul, add_zero]
    rw [mul_div_assoc]
  rw [← integral_congr_ae (Eventually.of_forall hF'0)]
  linarith

end ModSoft2

section ModCoer1

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/- ### Homogeneous coordinates `y ↦ (1, y)` under the standard Gaussian -/

theorem G54.cons_dot {n : ℕ} (θ : Fin (n + 1) → ℝ) (y : Fin n → ℝ) :
    ∑ k, θ k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k = θ 0 + ∑ k : Fin n, θ k.succ * y k := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_one]

theorem G54.measurable_cons (n : ℕ) :
    Measurable (fun y : Fin n → ℝ => (Fin.cons 1 y : Fin (n + 1) → ℝ)) := by
  refine measurable_pi_lambda _ (fun k => ?_)
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Fin.cons_zero]
    exact measurable_const
  · simp only [Fin.cons_succ]
    exact measurable_pi_apply j

theorem G54.continuous_cons (n : ℕ) :
    Continuous (fun y : Fin n → ℝ => (Fin.cons 1 y : Fin (n + 1) → ℝ)) := by
  refine continuous_pi (fun k => ?_)
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Fin.cons_zero]
    exact continuous_const
  · simp only [Fin.cons_succ]
    exact continuous_apply j

theorem G54.integrable_coord_pi_gauss (n : ℕ) (j : Fin n) :
    Integrable (fun y : Fin n → ℝ => y j) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
  MeasureTheory.integrable_eval (μ := fun _ : Fin n => gaussianReal 0 1)
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))

theorem G54.integral_coord_pi_gauss (n : ℕ) (j : Fin n) :
    ∫ y : Fin n → ℝ, y j ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1)) = 0 := by
  have h1 : ∫ x, (fun y : Fin n → ℝ => y j) x
      ∂((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (fun x : Fin n → ℝ => -x))
      = ∫ x : Fin n → ℝ, (-x) j ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    integral_map measurable_neg.aemeasurable (measurable_pi_apply j).aestronglyMeasurable
  rw [G54.pi_gauss_map_neg] at h1
  simp only [Pi.neg_apply, integral_neg] at h1
  linarith

theorem G54.integrable_cons_pi_gauss (n : ℕ) (k : Fin (n + 1)) :
    Integrable (fun y : Fin n → ℝ => (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Fin.cons_zero]
    exact integrable_const _
  · simp only [Fin.cons_succ]
    exact G54.integrable_coord_pi_gauss n j

theorem G54.pi_gauss_isOpenPos (n : ℕ) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).IsOpenPosMeasure := by
  have h1 : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  infer_instance

/- ### The support functional `θ ↦ ∫ maxᵢ ⟨θᵢ, T y⟩ dγ` -/

theorem G54.sup_dot_lip {Y : Type*} {d : ℕ} (T : Y → Fin d → ℝ) {ι : Type*} [Fintype ι]
    [Nonempty ι] (θ θ' : ι → Fin d → ℝ) (y : Y) :
    |(Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k)
      - (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ' i k * T y k)|
      ≤ ‖θ - θ'‖ * ∑ k, |T y k| := by
  have hdiff : ∀ i, |(∑ k, θ i k * T y k) - ∑ k, θ' i k * T y k| ≤ ‖θ - θ'‖ * ∑ k, |T y k| := by
    intro i
    have h1 : (∑ k, θ i k * T y k) - ∑ k, θ' i k * T y k = ∑ k, (θ - θ') i k * T y k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.sub_apply]
      ring
    rw [h1]
    exact G54.abs_dot_le (θ - θ') i (T y)
  rw [abs_le]
  constructor
  · have h1 : (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ' i k * T y k)
        ≤ (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k)
          + ‖θ - θ'‖ * ∑ k, |T y k| := by
      apply Finset.sup'_le
      intro i _
      have h2 := (abs_le.mp (hdiff i)).1
      have h3 : (∑ k, θ i k * T y k)
          ≤ Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k :=
        Finset.le_sup' (fun i => ∑ k, θ i k * T y k) (Finset.mem_univ i)
      linarith
    linarith
  · have h1 : (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k)
        ≤ (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ' i k * T y k)
          + ‖θ - θ'‖ * ∑ k, |T y k| := by
      apply Finset.sup'_le
      intro i _
      have h2 := (abs_le.mp (hdiff i)).2
      have h3 : (∑ k, θ' i k * T y k)
          ≤ Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ' i k * T y k :=
        Finset.le_sup' (fun i => ∑ k, θ' i k * T y k) (Finset.mem_univ i)
      linarith
    linarith

theorem G54.sup_dot_integrable {Y : Type*} [MeasurableSpace Y] (γ : Measure Y)
    {d : ℕ} (T : Y → Fin d → ℝ) (hTm : Measurable T) (hTi : ∀ k, Integrable (fun y => T y k) γ)
    {ι : Type*} [Fintype ι] [Nonempty ι] (θ : ι → Fin d → ℝ) :
    Integrable (fun y => Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k) γ := by
  have hTkm : ∀ k, Measurable (fun y => T y k) := fun k => (measurable_pi_apply k).comp hTm
  have hm : Measurable (fun y => Finset.univ.sup' Finset.univ_nonempty
      fun i => ∑ k, θ i k * T y k) :=
    G54.measurable_sup' (fun y i => ∑ k, θ i k * T y k)
      (fun i => Finset.measurable_sum _ (fun k _ => (hTkm k).const_mul _))
  have hNi : Integrable (fun y => ‖θ‖ * ∑ k, |T y k|) γ :=
    (integrable_finsetSum _ (fun k _ => (hTi k).abs)).const_mul _
  refine hNi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => ∑ k, θ i k * T y k)
  rw [hi₀]
  exact G54.abs_dot_le θ i₀ (T y)

theorem G54.sup_dot_continuous {Y : Type*} [MeasurableSpace Y] (γ : Measure Y)
    {d : ℕ} (T : Y → Fin d → ℝ) (hTm : Measurable T) (hTi : ∀ k, Integrable (fun y => T y k) γ)
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (fun θ : ι → Fin d → ℝ =>
      ∫ y, (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k) ∂γ) := by
  have hNi : Integrable (fun y => ∑ k, |T y k|) γ :=
    integrable_finsetSum _ (fun k _ => (hTi k).abs)
  have hK : (0 : ℝ) ≤ ∫ y, ∑ k, |T y k| ∂γ :=
    integral_nonneg (fun y => Finset.sum_nonneg (fun k _ => abs_nonneg _))
  have hlip : LipschitzWith ⟨∫ y, ∑ k, |T y k| ∂γ, hK⟩ (fun θ : ι → Fin d → ℝ =>
      ∫ y, (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k) ∂γ) := by
    apply LipschitzWith.of_dist_le_mul
    intro θ θ'
    rw [Real.dist_eq, dist_eq_norm, ← integral_sub (G54.sup_dot_integrable γ T hTm hTi θ)
      (G54.sup_dot_integrable γ T hTm hTi θ')]
    calc |∫ y, ((Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k)
          - (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ' i k * T y k)) ∂γ|
        ≤ ∫ y, |(Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k)
          - (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ' i k * T y k)| ∂γ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, ‖θ - θ'‖ * ∑ k, |T y k| ∂γ :=
          integral_mono ((G54.sup_dot_integrable γ T hTm hTi θ).sub
            (G54.sup_dot_integrable γ T hTm hTi θ')).abs (hNi.const_mul _)
            (fun y => G54.sup_dot_lip T θ θ' y)
      _ = (∫ y, ∑ k, |T y k| ∂γ) * ‖θ - θ'‖ := by rw [integral_const_mul, mul_comm]
  exact hlip.continuous

theorem G54.sup_dot_smul {Y : Type*} {d : ℕ} (T : Y → Fin d → ℝ) {ι : Type*} [Fintype ι]
    [Nonempty ι] (θ : ι → Fin d → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (y : Y) :
    (Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, (lam • θ) i k * T y k)
      = lam * Finset.univ.sup' Finset.univ_nonempty fun i => ∑ k, θ i k * T y k := by
  have hterm : ∀ i, ∑ k, (lam • θ) i k * T y k = lam * ∑ k, θ i k * T y k := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rw [hterm]
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun i => ∑ k, θ i k * T y k) (Finset.mem_univ i)) hlam
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => ∑ k, θ i k * T y k)
    rw [hi₀, ← hterm]
    exact Finset.le_sup' (fun i => ∑ k, (lam • θ) i k * T y k) (Finset.mem_univ i₀)

/-- A continuous positively homogeneous function which is positive away from the origin on a closed
cone dominates a multiple of the norm there. -/
theorem G54.exists_coercive_const {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    [ProperSpace Θ] (R : Θ → ℝ) (hRc : Continuous R)
    (hRh : ∀ (lam : ℝ) (θ : Θ), 0 ≤ lam → R (lam • θ) = lam * R θ)
    (S : Set Θ) (hSc : IsClosed S) (hSs : ∀ (lam : ℝ) (θ : Θ), θ ∈ S → lam • θ ∈ S)
    (hpos : ∀ θ ∈ S, R θ ≤ 0 → θ = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ S, c * ‖θ‖ ≤ R θ := by
  have hR0 : R 0 = 0 := by
    have := hRh 0 0 le_rfl
    simpa using this
  have hcomp : IsCompact (S ∩ Metric.sphere (0 : Θ) 1) := (isCompact_sphere _ _).inter_left hSc
  have hnormalize : ∀ θ ∈ S, θ ≠ 0 → (‖θ‖⁻¹ • θ) ∈ S ∩ Metric.sphere (0 : Θ) 1 := by
    intro θ hθ hne
    refine ⟨hSs _ _ hθ, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
  rcases (S ∩ Metric.sphere (0 : Θ) 1).eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun θ hθ => ?_⟩
    by_cases h0 : θ = 0
    · rw [h0, hR0, norm_zero, mul_zero]
    · have := hnormalize θ hθ h0
      rw [hempty] at this
      exact absurd this (notMem_empty _)
  · obtain ⟨θ₀, hθ₀, hmin⟩ := hcomp.exists_isMinOn hne hRc.continuousOn
    have hθ₀ne : θ₀ ≠ 0 := by
      intro h
      have := hθ₀.2
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
      exact zero_ne_one this
    have hc : 0 < R θ₀ := by
      by_contra hcon
      exact hθ₀ne (hpos θ₀ hθ₀.1 (not_lt.mp hcon))
    refine ⟨R θ₀, hc, fun θ hθ => ?_⟩
    by_cases h0 : θ = 0
    · rw [h0, hR0, norm_zero, mul_zero]
    · have h1 : R θ₀ ≤ R (‖θ‖⁻¹ • θ) := hmin (hnormalize θ hθ h0)
      rw [hRh _ _ (inv_nonneg.mpr (norm_nonneg _))] at h1
      have hn : 0 < ‖θ‖ := norm_pos_iff.mpr h0
      rw [inv_mul_eq_div, le_div_iff₀ hn] at h1
      exact h1

end ModCoer1

section ModCoer2

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/-- The slack inequality: if the atoms `xᵢ` (with weights `pᵢ`) are dominated by the Gaussian in
the convex order, then the contracted atoms `(1 - ε) xᵢ` satisfy a strict form of the dual
inequality against max-affine test functions. -/
theorem G54.gauss_slack {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (x : ι → Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hD : ∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
      Integrable f (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) →
      ∑ i, p i * f (x i) ≤ ∫ y, f y ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
    (θ : ι → Fin (n + 1) → ℝ) :
    ∑ i, p i * ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k
      ≤ (1 - ε) * ∫ y, (Finset.univ.sup' Finset.univ_nonempty
          fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
          ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        + ε * Finset.univ.sup' Finset.univ_nonempty (fun i => θ i 0) := by
  set γn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1) with hγn
  have hγn1 : IsProbabilityMeasure γn := by rw [hγn]; infer_instance
  set M : (Fin n → ℝ) → ℝ := fun y => Finset.univ.sup' Finset.univ_nonempty
    fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k with hM
  have hMi : Integrable M γn :=
    G54.sup_dot_integrable γn _ (G54.measurable_cons n) (G54.integrable_cons_pi_gauss n) θ
  set f : (Fin n → ℝ) → ℝ := fun y => Finset.univ.sup' Finset.univ_nonempty
    fun i => ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • y) : Fin (n + 1) → ℝ) k with hf
  -- the scaled row
  have hrow : ∀ i y, ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • y) : Fin (n + 1) → ℝ) k
      = (1 - ε) * (∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) + ε * θ i 0 := by
    intro i y
    rw [G54.cons_dot, G54.cons_dot, mul_add, Finset.mul_sum]
    have h1 : ∑ k : Fin n, θ i k.succ * ((1 - ε) • y) k
        = ∑ k : Fin n, (1 - ε) * (θ i k.succ * y k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1]
    ring
  have hfconv : ConvexOn ℝ univ f := by
    refine ⟨convex_univ, fun y _ y' _ a b ha hb hab => ?_⟩
    simp only [hf]
    apply Finset.sup'_le
    intro i _
    have h1 : ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • (a • y + b • y')) : Fin (n + 1) → ℝ) k
        = a * (∑ k, θ i k * (Fin.cons 1 ((1 - ε) • y) : Fin (n + 1) → ℝ) k)
          + b * (∑ k, θ i k * (Fin.cons 1 ((1 - ε) • y') : Fin (n + 1) → ℝ) k) := by
      rw [G54.cons_dot, G54.cons_dot, G54.cons_dot]
      have h2 : ∑ k : Fin n, θ i k.succ * ((1 - ε) • (a • y + b • y')) k
          = a * (∑ k : Fin n, θ i k.succ * ((1 - ε) • y) k)
            + b * (∑ k : Fin n, θ i k.succ * ((1 - ε) • y') k) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        ring
      rw [h2]
      have h3 : θ i 0 = a * θ i 0 + b * θ i 0 := by rw [← add_mul, hab, one_mul]
      nlinarith [h3]
    rw [h1, smul_eq_mul, smul_eq_mul]
    have h4 := Finset.le_sup' (fun i => ∑ k, θ i k
      * (Fin.cons 1 ((1 - ε) • y) : Fin (n + 1) → ℝ) k) (Finset.mem_univ i)
    have h5 := Finset.le_sup' (fun i => ∑ k, θ i k
      * (Fin.cons 1 ((1 - ε) • y') : Fin (n + 1) → ℝ) k) (Finset.mem_univ i)
    exact add_le_add (mul_le_mul_of_nonneg_left h4 ha) (mul_le_mul_of_nonneg_left h5 hb)
  have hfupper : ∀ y, f y ≤ (1 - ε) * M y
      + ε * Finset.univ.sup' Finset.univ_nonempty (fun i => θ i 0) := by
    intro y
    simp only [hf]
    apply Finset.sup'_le
    intro i _
    rw [hrow]
    have h4 := Finset.le_sup' (fun i => ∑ k, θ i k
      * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) (Finset.mem_univ i)
    have h5 := Finset.le_sup' (fun i => θ i 0) (Finset.mem_univ i)
    exact add_le_add (mul_le_mul_of_nonneg_left h4 (by linarith))
      (mul_le_mul_of_nonneg_left h5 hε)
  have hfm : Measurable f := by
    have hmeas : Measurable (fun y : Fin n → ℝ => (Fin.cons 1 ((1 - ε) • y) : Fin (n + 1) → ℝ)) :=
      (G54.measurable_cons n).comp (measurable_const_smul _)
    exact G54.measurable_sup' (fun y i => ∑ k, θ i k
      * (Fin.cons 1 ((1 - ε) • y) : Fin (n + 1) → ℝ) k)
      (fun i => Finset.measurable_sum _ (fun k _ =>
        ((measurable_pi_apply k).comp hmeas).const_mul _))
  have hflower : ∀ y, (1 - ε) * M y + ε * Finset.univ.inf' Finset.univ_nonempty (fun i => θ i 0)
      ≤ f y := by
    intro y
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
    have h1 := Finset.le_sup' (fun i => ∑ k, θ i k
      * (Fin.cons 1 ((1 - ε) • y) : Fin (n + 1) → ℝ) k) (Finset.mem_univ i₀)
    simp only [hf, hM]
    rw [hi₀]
    refine le_trans ?_ h1
    rw [hrow]
    have h2 := Finset.inf'_le (fun i => θ i 0) (Finset.mem_univ i₀)
    have := mul_le_mul_of_nonneg_left h2 hε
    linarith
  have hfint : Integrable f γn := by
    have hbd : Integrable (fun y => |(1 - ε) * M y|
        + (|ε * Finset.univ.sup' Finset.univ_nonempty (fun i => θ i 0)|
          + |ε * Finset.univ.inf' Finset.univ_nonempty (fun i => θ i 0)|)) γn :=
      ((hMi.const_mul _).abs).add (integrable_const _)
    refine hbd.mono' hfm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hfupper y
    have h2 := hflower y
    have h3 := neg_abs_le ((1 - ε) * M y)
    have h4 := le_abs_self ((1 - ε) * M y)
    have h5 := le_abs_self (ε * Finset.univ.sup' Finset.univ_nonempty (fun i => θ i 0))
    have h6 := neg_abs_le (ε * Finset.univ.inf' Finset.univ_nonempty (fun i => θ i 0))
    have h7 := abs_nonneg (ε * Finset.univ.sup' Finset.univ_nonempty (fun i => θ i 0))
    have h8 := abs_nonneg (ε * Finset.univ.inf' Finset.univ_nonempty (fun i => θ i 0))
    constructor <;> linarith
  have hdom := hD f hfconv hfint
  have hleft : ∑ i, p i * ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k
      ≤ ∑ i, p i * f (x i) := by
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hp i).le
    exact Finset.le_sup' (fun j => ∑ k, θ j k
      * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k) (Finset.mem_univ i)
  have hright : ∫ y, f y ∂γn ≤ (1 - ε) * ∫ y, M y ∂γn
      + ε * Finset.univ.sup' Finset.univ_nonempty (fun i => θ i 0) := by
    have h1 : ∫ y, f y ∂γn ≤ ∫ y, ((1 - ε) * M y
        + ε * Finset.univ.sup' Finset.univ_nonempty (fun i => θ i 0)) ∂γn :=
      integral_mono hfint ((hMi.const_mul _).add (integrable_const _)) hfupper
    rw [integral_add (hMi.const_mul _) (integrable_const _), integral_const_mul] at h1
    simpa using h1
  linarith

/-- First moments match: the contracted atoms are centred. -/
theorem G54.gauss_moment {n : ℕ} {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp1 : ∑ i, p i = 1) (x : ι → Fin n → ℝ) (ε : ℝ)
    (hD : ∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
      Integrable f (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) →
      ∑ i, p i * f (x i) ≤ ∫ y, f y ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
    (k : Fin (n + 1)) :
    ∫ y, (Fin.cons 1 y : Fin (n + 1) → ℝ) k ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      = ∑ i, p i * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k := by
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [hp1]
  · simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
    rw [G54.integral_coord_pi_gauss]
    have h1 := hD (fun y => y j)
      ((LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ).convexOn convex_univ)
      (G54.integrable_coord_pi_gauss n j)
    have h2 := hD (fun y => -(y j))
      ((LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ).concaveOn convex_univ).neg
      (G54.integrable_coord_pi_gauss n j).neg
    rw [G54.integral_coord_pi_gauss] at h1
    rw [integral_neg, G54.integral_coord_pi_gauss] at h2
    have h3 : ∑ i, p i * -(x i j) = -∑ i, p i * x i j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h3] at h2
    have h4 : ∑ i, p i * x i j = 0 := by linarith
    have h5 : ∑ i, p i * ((1 - ε) * x i j) = (1 - ε) * ∑ i, p i * x i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h5, h4, mul_zero]

end ModCoer2

section ModCoer3

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/-- Rigidity: on the gauge-fixed subspace the dual gap vanishes only at the origin.  This uses the
slack `ε > 0` and the full support of the Gaussian measure. -/
theorem G54.gauss_R_pos {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (x : ι → Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hD : ∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
      Integrable f (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) →
      ∑ i, p i * f (x i) ≤ ∫ y, f y ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
    (θ : ι → Fin (n + 1) → ℝ) (hθS : ∀ k, ∑ i, p i * θ i k = 0)
    (hR : ∫ y, (Finset.univ.sup' Finset.univ_nonempty
          fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
          ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        - ∑ i, p i * ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k ≤ 0) :
    θ = 0 := by
  set γn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1) with hγn
  have hγn1 : IsProbabilityMeasure γn := by rw [hγn]; infer_instance
  have hγnpos : γn.IsOpenPosMeasure := G54.pi_gauss_isOpenPos n
  set M : (Fin n → ℝ) → ℝ := fun y => Finset.univ.sup' Finset.univ_nonempty
    fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k with hM
  have hMi : Integrable M γn :=
    G54.sup_dot_integrable γn _ (G54.measurable_cons n) (G54.integrable_cons_pi_gauss n) θ
  obtain ⟨is, -, his⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => θ i 0)
  have hslack := G54.gauss_slack p hp x ε hε.le hε1 hD θ
  rw [his] at hslack
  -- `∫ M ≤ θ is 0`
  have hMle : ∫ y, M y ∂γn ≤ θ is 0 := by
    have h1 : ε * ∫ y, M y ∂γn ≤ ε * θ is 0 := by linarith
    exact le_of_mul_le_mul_left h1 hε
  -- the affine function attached to `is`
  have hrowc : ∀ i, Continuous (fun y : Fin n → ℝ =>
      ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) := fun i =>
    continuous_finsetSum _ (fun k _ =>
      continuous_const.mul ((continuous_apply k).comp (G54.continuous_cons n)))
  have hrowi : ∀ i, Integrable (fun y : Fin n → ℝ =>
      ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) γn := fun i =>
    integrable_finsetSum _ (fun k _ => (G54.integrable_cons_pi_gauss n k).const_mul _)
  have hrowint : ∫ y, ∑ k, θ is k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k ∂γn = θ is 0 := by
    have h0 : ∀ y : Fin n → ℝ, ∑ k, θ is k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k
        = θ is 0 + ∑ k : Fin n, θ is k.succ * y k := fun y => G54.cons_dot (θ is) y
    have h1 : ∀ k : Fin n, ∫ y : Fin n → ℝ, θ is k.succ * y k ∂γn = 0 := by
      intro k
      rw [integral_const_mul, hγn, G54.integral_coord_pi_gauss, mul_zero]
    have h2 : Integrable (fun y : Fin n → ℝ => ∑ k : Fin n, θ is k.succ * y k) γn :=
      integrable_finsetSum _ (fun k _ => (G54.integrable_coord_pi_gauss n k).const_mul _)
    have h3 : ∫ y : Fin n → ℝ, ∑ k : Fin n, θ is k.succ * y k ∂γn = 0 := by
      rw [integral_finsetSum _ (fun k _ => (G54.integrable_coord_pi_gauss n k).const_mul _)]
      exact Finset.sum_eq_zero (fun k _ => h1 k)
    rw [integral_congr_ae (Eventually.of_forall h0), integral_add (integrable_const _) h2, h3]
    simp
  have hMc : Continuous M := by
    simp only [hM]
    exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => hrowc i)
  set h : (Fin n → ℝ) → ℝ := fun y => M y
    - ∑ k, θ is k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k with hh
  have hh0 : ∀ y, 0 ≤ h y := by
    intro y
    simp only [hh, hM, sub_nonneg]
    exact Finset.le_sup' (fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
      (Finset.mem_univ is)
  have hhi : Integrable h γn := hMi.sub (hrowi is)
  have hhint : ∫ y, h y ∂γn = 0 := by
    have h1 : ∫ y, h y ∂γn = ∫ y, M y ∂γn - θ is 0 := by
      simp only [hh]
      rw [integral_sub hMi (hrowi is), hrowint]
    have h2 : 0 ≤ ∫ y, h y ∂γn := integral_nonneg hh0
    linarith
  have hhae : h =ᵐ[γn] 0 := (integral_eq_zero_iff_of_nonneg hh0 hhi).mp hhint
  have hhzero : h = 0 := Measure.eq_of_ae_eq hhae (hMc.sub (hrowc is)) continuous_const
  have hdom : ∀ y i, ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k
      ≤ ∑ k, θ is k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k := by
    intro y i
    have h1 : h y = 0 := congrFun hhzero y
    simp only [hh, hM] at h1
    have h2 := Finset.le_sup' (fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
      (Finset.mem_univ i)
    linarith
  -- all linear parts coincide
  have hV : ∀ j (k : Fin n), θ j k.succ = θ is k.succ := by
    intro j
    set D : Fin n → ℝ := fun k => θ j k.succ - θ is k.succ with hD'
    have hineq : ∀ y : Fin n → ℝ, (θ j 0 - θ is 0) + ∑ k, D k * y k ≤ 0 := by
      intro y
      have h1 := hdom y j
      rw [G54.cons_dot, G54.cons_dot] at h1
      have h2 : ∑ k, D k * y k = ∑ k, θ j k.succ * y k - ∑ k, θ is k.succ * y k := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hD']
        ring
      rw [h2]
      linarith
    have hsq : ∑ k, D k * D k = 0 := by
      by_contra hne
      have hpos : 0 < ∑ k, D k * D k :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun k _ => mul_self_nonneg _)) (Ne.symm hne)
      set s : ℝ := (θ is 0 - θ j 0 + 1) / ∑ k, D k * D k with hs
      have h1 := hineq (fun k => s * D k)
      have h2 : ∑ k, D k * (s * D k) = s * ∑ k, D k * D k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [h2, hs, div_mul_cancel₀ _ hpos.ne'] at h1
      linarith
    intro k
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg (D k))).mp hsq k
      (Finset.mem_univ k)
    have h2 : D k = 0 := mul_self_eq_zero.mp h1
    simp only [hD'] at h2
    linarith
  have hV0 : ∀ j (k : Fin n), θ j k.succ = 0 := by
    intro j k
    have h1 := hθS k.succ
    have h2 : ∑ i, p i * θ i k.succ = θ is k.succ := by
      have h3 : ∑ i, p i * θ i k.succ = ∑ i, p i * θ is k.succ :=
        Finset.sum_congr rfl fun i _ => by rw [hV i k]
      rw [h3, ← Finset.sum_mul, hp1, one_mul]
    rw [h2] at h1
    rw [hV j k, h1]
  have hrow0 : ∀ i (y : Fin n → ℝ), ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k = θ i 0 := by
    intro i y
    rw [G54.cons_dot]
    simp only [hV0, zero_mul, Finset.sum_const_zero, add_zero]
  have hMconst : ∀ y, M y = θ is 0 := by
    intro y
    simp only [hM]
    simp only [hrow0]
    exact his
  have hMint : ∫ y, M y ∂γn = θ is 0 := by
    simp only [hMconst, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hlin0 : ∑ i, p i * ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k = 0 := by
    simp only [hrow0]
    exact hθS 0
  have hθis : θ is 0 ≤ 0 := by
    have h1 : ∫ y, M y ∂γn
        - ∑ i, p i * ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k ≤ 0 := hR
    rw [hMint, hlin0] at h1
    linarith
  have hU0 : ∀ i, θ i 0 = 0 := by
    have hnonpos : ∀ i ∈ (Finset.univ : Finset ι), p i * θ i 0 ≤ 0 := by
      intro i _
      have h1 : θ i 0 ≤ θ is 0 := by
        rw [← his]
        exact Finset.le_sup' (fun i => θ i 0) (Finset.mem_univ i)
      exact mul_nonpos_of_nonneg_of_nonpos (hp i).le (h1.trans hθis)
    intro i
    have h1 := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp (hθS 0) i (Finset.mem_univ i)
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (hp i).ne'
    · exact h2
  funext i k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact hU0 i
  · exact hV0 i j

/-- **Existence of the entropic martingale coupling** (Hua–Song–Tudose, Proposition 3.2, direct
part), for finitely supported laws: if the atoms `xᵢ` with weights `pᵢ` are dominated by the
standard Gaussian in the convex order, then for every `ε ∈ (0, 1]` there are softmax weights
`wᵢ(y) = pᵢ exp ⟨θᵢ, (1, y)⟩ / ∑ⱼ pⱼ exp ⟨θⱼ, (1, y)⟩` with `∫ wᵢ dγ = pᵢ` and
`∫ y wᵢ(y) dγ(y) = pᵢ (1 - ε) xᵢ`. -/
theorem G54.exists_softmax_gauss {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (x : ι → Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hD : ∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
      Integrable f (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) →
      ∑ i, p i * f (x i) ≤ ∫ y, f y ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :
    ∃ θ : ι → Fin (n + 1) → ℝ, ∀ i k,
      ∫ y, (Fin.cons 1 y : Fin (n + 1) → ℝ) k
        * (p i * Real.exp (∑ k', θ i k' * (Fin.cons 1 y : Fin (n + 1) → ℝ) k')
          / ∑ j, p j * Real.exp (∑ k', θ j k' * (Fin.cons 1 y : Fin (n + 1) → ℝ) k'))
        ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      = p i * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k := by
  set γn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1) with hγn
  have hγn1 : IsProbabilityMeasure γn := by rw [hγn]; infer_instance
  have hTm := G54.measurable_cons n
  have hTi := G54.integrable_cons_pi_gauss n
  -- coercivity
  have hcoer : ∃ c : ℝ, 0 < c ∧ ∀ θ : ι → Fin (n + 1) → ℝ, (∀ k, ∑ i, p i * θ i k = 0) →
      c * ‖θ‖ ≤ ∫ y, (Finset.univ.sup' Finset.univ_nonempty
          fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) ∂γn
        - ∑ i, p i * ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k := by
    have hRc : Continuous (fun θ : ι → Fin (n + 1) → ℝ =>
        ∫ y, (Finset.univ.sup' Finset.univ_nonempty
          fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) ∂γn
        - ∑ i, p i * ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k) := by
      refine (G54.sup_dot_continuous γn _ hTm hTi).sub ?_
      fun_prop
    have hRh : ∀ (lam : ℝ) (θ : ι → Fin (n + 1) → ℝ), 0 ≤ lam →
        (∫ y, (Finset.univ.sup' Finset.univ_nonempty
          fun i => ∑ k, (lam • θ) i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) ∂γn
        - ∑ i, p i * ∑ k, (lam • θ) i k * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k)
        = lam * (∫ y, (Finset.univ.sup' Finset.univ_nonempty
          fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) ∂γn
        - ∑ i, p i * ∑ k, θ i k * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k) := by
      intro lam θ hlam
      have h1 : ∫ y, (Finset.univ.sup' Finset.univ_nonempty
          fun i => ∑ k, (lam • θ) i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) ∂γn
          = lam * ∫ y, (Finset.univ.sup' Finset.univ_nonempty
          fun i => ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) ∂γn := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        exact G54.sup_dot_smul _ θ lam hlam y
      have h2 : ∑ i, p i * ∑ k, (lam • θ) i k
            * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k
          = lam * ∑ i, p i * ∑ k, θ i k
            * (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ) k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [h1, h2, mul_sub]
    have hSc : IsClosed {θ : ι → Fin (n + 1) → ℝ | ∀ k, ∑ i, p i * θ i k = 0} := by
      have : {θ : ι → Fin (n + 1) → ℝ | ∀ k, ∑ i, p i * θ i k = 0}
          = ⋂ k : Fin (n + 1), {θ : ι → Fin (n + 1) → ℝ | ∑ i, p i * θ i k = 0} := by
        ext θ
        simp
      rw [this]
      refine isClosed_iInter fun k => isClosed_eq ?_ continuous_const
      fun_prop
    have hSs : ∀ (lam : ℝ) (θ : ι → Fin (n + 1) → ℝ),
        θ ∈ {θ : ι → Fin (n + 1) → ℝ | ∀ k, ∑ i, p i * θ i k = 0} →
        lam • θ ∈ {θ : ι → Fin (n + 1) → ℝ | ∀ k, ∑ i, p i * θ i k = 0} := by
      intro lam θ hθ k
      have h1 : ∑ i, p i * (lam • θ) i k = lam * ∑ i, p i * θ i k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [h1, hθ k, mul_zero]
    obtain ⟨c, hc0, hc⟩ := G54.exists_coercive_const _ hRc hRh _ hSc hSs
      (fun θ hθ hR => G54.gauss_R_pos p hp hp1 x ε hε hε1 hD θ hθ hR)
    exact ⟨c, hc0, fun θ hθ => hc θ hθ⟩
  obtain ⟨θs, hmax⟩ := G54.softmax_max γn _ hTm hTi p hp hp1
    (fun i => (Fin.cons 1 ((1 - ε) • x i) : Fin (n + 1) → ℝ))
    (fun k => G54.gauss_moment p hp1 x ε hD k) hcoer
  exact ⟨θs, fun i k => G54.softmax_stationary γn _ hTm hTi p hp hp1 _ θs hmax i k⟩

end ModCoer3

section ModPot

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal ContDiff

theorem G54.cons_affine {n : ℕ} (θ : Fin (n + 1) → ℝ) (y y' : Fin n → ℝ) (a b : ℝ)
    (hab : a + b = 1) :
    ∑ k, θ k * (Fin.cons 1 (a • y + b • y') : Fin (n + 1) → ℝ) k
      = a * (∑ k, θ k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
        + b * (∑ k, θ k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k) := by
  rw [G54.cons_dot, G54.cons_dot, G54.cons_dot]
  have h2 : ∑ k : Fin n, θ k.succ * (a • y + b • y') k
      = a * (∑ k : Fin n, θ k.succ * y k) + b * (∑ k : Fin n, θ k.succ * y' k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [h2]
  have h3 : θ 0 = a * θ 0 + b * θ 0 := by rw [← add_mul, hab, one_mul]
  nlinarith [h3]

theorem G54.contDiff_cons_apply {n : ℕ} (m : WithTop ℕ∞) (k : Fin (n + 1)) :
    ContDiff ℝ m (fun y : Fin n → ℝ => (Fin.cons 1 y : Fin (n + 1) → ℝ) k) := by
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Fin.cons_zero]
    exact contDiff_const
  · simp only [Fin.cons_succ]
    exact contDiff_apply ℝ ℝ j

/-- The potentials `ψᵢ = log ∑ⱼ pⱼ exp ⟨θⱼ, (1, y)⟩ - ⟨θᵢ, (1, y)⟩` of the softmax conditional
laws are convex, smooth and Lipschitz. -/
theorem G54.softmax_potential {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (θ : ι → Fin (n + 1) → ℝ) (i : ι) :
    ConvexOn ℝ univ (fun y : Fin n → ℝ =>
        Real.log (∑ j, p j * Real.exp (∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k))
          - ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) ∧
    ContDiff ℝ ∞ (fun y : Fin n → ℝ =>
        Real.log (∑ j, p j * Real.exp (∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k))
          - ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) ∧
    ∃ L : ℝ, ∀ y y' : Fin n → ℝ,
      |(Real.log (∑ j, p j * Real.exp (∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k))
          - ∑ k, θ i k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
        - (Real.log (∑ j, p j * Real.exp (∑ k, θ j k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k))
          - ∑ k, θ i k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k)| ≤ L * ‖y - y'‖ := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨convex_univ, fun y _ y' _ a b ha hb hab => ?_⟩
    have hlse := (G54.lse_convex p hp).2
      (mem_univ (fun j => ∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k))
      (mem_univ (fun j => ∑ k, θ j k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k)) ha hb hab
    have hvec : (fun j => ∑ k, θ j k * (Fin.cons 1 (a • y + b • y') : Fin (n + 1) → ℝ) k)
        = a • (fun j => ∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
          + b • (fun j => ∑ k, θ j k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k) := by
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact G54.cons_affine (θ j) y y' a b hab
    have hrow := G54.cons_affine (θ i) y y' a b hab
    simp only [smul_eq_mul] at hlse ⊢
    have hlse' : Real.log (∑ j, p j * Real.exp
        (∑ k, θ j k * (Fin.cons 1 (a • y + b • y') : Fin (n + 1) → ℝ) k))
        ≤ a * Real.log (∑ j, p j * Real.exp (∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k))
          + b * Real.log (∑ j, p j * Real.exp
            (∑ k, θ j k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k)) := by
      have h1 : (fun j => ∑ k, θ j k * (Fin.cons 1 (a • y + b • y') : Fin (n + 1) → ℝ) k)
          = fun j => (a • (fun j => ∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
          + b • (fun j => ∑ k, θ j k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k)) j := hvec
      rw [show (∑ j, p j * Real.exp
          (∑ k, θ j k * (Fin.cons 1 (a • y + b • y') : Fin (n + 1) → ℝ) k))
          = ∑ j, p j * Real.exp ((a • (fun j => ∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
          + b • (fun j => ∑ k, θ j k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k)) j) from
        Finset.sum_congr rfl fun j _ => by rw [congrFun h1 j]]
      exact hlse
    rw [hrow]
    linarith
  · have hrow : ∀ j, ContDiff ℝ ∞ (fun y : Fin n → ℝ =>
        ∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) := fun j =>
      ContDiff.sum fun k _ => contDiff_const.mul (G54.contDiff_cons_apply ∞ k)
    refine ContDiff.sub (ContDiff.log ?_ ?_) (hrow i)
    · exact ContDiff.sum fun j _ => contDiff_const.mul (Real.contDiff_exp.comp (hrow j))
    · intro y
      exact (G54.lse_sum_pos p hp _).ne'
  · refine ⟨2 * (‖θ‖ * n), fun y y' => ?_⟩
    have hT : ∑ k, |(Fin.cons 1 y : Fin (n + 1) → ℝ) k - (Fin.cons 1 y' : Fin (n + 1) → ℝ) k|
        ≤ n * ‖y - y'‖ := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, sub_self, abs_zero, zero_add]
      calc ∑ k : Fin n, |y k - y' k| ≤ ∑ _k : Fin n, ‖y - y'‖ := by
            refine Finset.sum_le_sum fun k _ => ?_
            have := norm_le_pi_norm (y - y') k
            rw [Real.norm_eq_abs] at this
            exact this
        _ = n * ‖y - y'‖ := by simp
    have hrow : ∀ j, |(∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
        - ∑ k, θ j k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k| ≤ ‖θ‖ * (n * ‖y - y'‖) := by
      intro j
      have h1 : (∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
          - ∑ k, θ j k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k
          = ∑ k, θ j k * ((Fin.cons 1 y : Fin (n + 1) → ℝ) k
            - (Fin.cons 1 y' : Fin (n + 1) → ℝ) k) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [h1]
      exact (G54.abs_dot_le θ j _).trans (mul_le_mul_of_nonneg_left hT (norm_nonneg _))
    have h1 := G54.lse_le_add p hp
      (fun j => ∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k)
      (fun j => ∑ k, θ j k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k) (‖θ‖ * (n * ‖y - y'‖))
      (fun j => by linarith [(abs_le.mp (hrow j)).2])
    have h2 := G54.lse_le_add p hp
      (fun j => ∑ k, θ j k * (Fin.cons 1 y' : Fin (n + 1) → ℝ) k)
      (fun j => ∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k) (‖θ‖ * (n * ‖y - y'‖))
      (fun j => by linarith [(abs_le.mp (hrow j)).1])
    have h3 := abs_le.mp (hrow i)
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2]

end ModPot

section ModDisc

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal

/-- **Discretisation** (Hua–Song–Tudose, Lemma 3.1).  A compactly supported probability measure
`μ` on `ℝⁿ` dominated by `γ` in the convex order can be replaced by a finitely supported one: the
barycentres `xᵢ` of the cells `Cᵢ` of a fine cubical partition, with weights `pᵢ = μ(Cᵢ)`.  The
atomic measure is still dominated by `γ` (Jensen), and each atom is `δ`-close to its cell. -/
theorem G54.exists_discretization {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hμS : μ Sᶜ = 0) {R : ℝ} (hR : ∀ y ∈ S, ‖y‖ ≤ R)
    (γ : Measure (Fin n → ℝ))
    (hdom : ∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f → Integrable f γ →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂γ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (p : ι → ℝ) (x : ι → Fin n → ℝ)
      (C : ι → Set (Fin n → ℝ)),
      (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧ (∀ i, MeasurableSet (C i)) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧ (∀ i, μ.real (C i) = p i) ∧
      (∀ i, ∀ y ∈ C i, dist y (x i) ≤ δ) ∧ (∀ i, ‖x i‖ ≤ R + δ) ∧
      (∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f → Integrable f γ →
        ∑ i, p i * f (x i) ≤ ∫ y, f y ∂γ) := by
  classical
  have hae : ∀ᵐ y ∂μ, y ∈ S := by
    rw [ae_iff]
    exact hμS
  have hidint : Integrable (fun y : Fin n → ℝ => y) μ := by
    have h1 : IntegrableOn (fun y : Fin n → ℝ => y) S μ :=
      continuous_id.continuousOn.integrableOn_compact hS
    rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h1
    exact h1
  set c : (Fin n → ℝ) → (Fin n → ℤ) := fun y j => ⌊y j / δ⌋ with hc
  have hdivm : ∀ j : Fin n, Measurable (fun y : Fin n → ℝ => y j / δ) := by
    intro j
    have h1 : Measurable (fun y : Fin n → ℝ => y j) := measurable_pi_apply j
    exact h1.div_const δ
  have hcm : Measurable c :=
    measurable_pi_lambda _ (fun j => Int.measurable_floor.comp (hdivm j))
  set cell : (Fin n → ℤ) → Set (Fin n → ℝ) := fun k => c ⁻¹' {k} with hcell
  have hcellm : ∀ k, MeasurableSet (cell k) := fun k => hcm (measurableSet_singleton k)
  have hdiam : ∀ k, ∀ y ∈ cell k, ∀ y' ∈ cell k, dist y y' ≤ δ := by
    intro k y hy y' hy'
    rw [dist_pi_le_iff hδ.le]
    intro j
    have hy1 : c y = k := hy
    have hy2 : c y' = k := hy'
    have h1 : ⌊y j / δ⌋ = ⌊y' j / δ⌋ := by
      have e1 := congrFun hy1 j
      have e2 := congrFun hy2 j
      simp only [hc] at e1 e2
      rw [e1, e2]
    have h2 := Int.abs_sub_lt_one_of_floor_eq_floor h1
    rw [Real.dist_eq]
    have h3 : |y j - y' j| = |y j / δ - y' j / δ| * δ := by
      rw [← sub_div, abs_div, abs_of_pos hδ, div_mul_cancel₀ _ hδ.ne']
    rw [h3]
    nlinarith [abs_nonneg (y j / δ - y' j / δ)]
  -- the finite set of relevant cells
  set J : Finset (Fin n → ℤ) :=
    Fintype.piFinset (fun _ : Fin n => Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋) with hJ
  have hcS : ∀ y ∈ S, c y ∈ J := by
    intro y hy
    rw [hJ, Fintype.mem_piFinset]
    intro j
    have h1 : |y j| ≤ R := by
      have := norm_le_pi_norm y j
      rw [Real.norm_eq_abs] at this
      exact this.trans (hR y hy)
    have h2 := abs_le.mp h1
    rw [Finset.mem_Icc]
    simp only [hc]
    constructor
    · apply Int.floor_le_floor
      rw [div_le_div_iff_of_pos_right hδ]
      exact h2.1
    · apply Int.floor_le_floor
      rw [div_le_div_iff_of_pos_right hδ]
      exact h2.2
  set I : Finset (Fin n → ℤ) := J.filter (fun k => μ (cell k) ≠ 0) with hI
  have hnull : ∀ k, k ∉ I → μ (cell k) = 0 := by
    intro k hk
    by_cases hkJ : k ∈ J
    · by_contra hne
      exact hk (Finset.mem_filter.mpr ⟨hkJ, hne⟩)
    · apply measure_mono_null _ hμS
      intro y hy hyS
      have hy1 : c y = k := hy
      exact hkJ (hy1 ▸ hcS y hyS)
  have hpos : ∀ i : I, 0 < μ.real (cell i.1) := by
    intro i
    have h1 := (Finset.mem_filter.mp i.2).2
    exact ENNReal.toReal_pos h1 (measure_ne_top μ _)
  have hdisj : Pairwise (Function.onFun Disjoint (fun i : I => cell i.1)) := by
    intro i j hij
    change Disjoint (cell i.1) (cell j.1)
    rw [Set.disjoint_left]
    intro y hy1 hy2
    have e1 : c y = i.1 := hy1
    have e2 : c y = j.1 := hy2
    exact hij (Subtype.ext (e1.symm.trans e2))
  have hcover : ∀ᵐ y ∂μ, y ∈ ⋃ i : I, cell i.1 := by
    rw [ae_iff]
    have hsub : {y | y ∉ ⋃ i : I, cell i.1} ⊆ ⋃ k ∈ {k : Fin n → ℤ | k ∉ I}, cell k := by
      intro y hy
      simp only [mem_iUnion, not_exists] at hy
      have hk : c y ∉ I := fun hmem => hy ⟨c y, hmem⟩ rfl
      exact mem_biUnion (show c y ∈ {k : Fin n → ℤ | k ∉ I} from hk) rfl
    refine measure_mono_null hsub ?_
    rw [measure_biUnion_null_iff (Set.to_countable _)]
    intro k hk
    exact hnull k hk
  have hrestr : μ.restrict (⋃ i : I, cell i.1) = μ := Measure.restrict_eq_self_of_ae_mem hcover
  -- integrals split along the cells
  have hsplit : ∀ f : (Fin n → ℝ) → ℝ, Integrable f μ →
      ∫ y, f y ∂μ = ∑ i : I, ∫ y in cell i.1, f y ∂μ := by
    intro f hf
    have h1 := integral_iUnion_fintype (μ := μ) (f := f) (s := fun i : I => cell i.1)
      (fun i => hcellm i.1) hdisj (fun i => hf.integrableOn)
    rw [hrestr] at h1
    exact h1
  have hsum1 : ∑ i : I, μ.real (cell i.1) = 1 := by
    have h1 := hsplit (fun _ => (1 : ℝ)) (integrable_const _)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, measureReal_restrict_apply,
      MeasurableSet.univ, univ_inter] at h1
    exact h1.symm
  have hne : Nonempty I := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    rw [Finset.sum_of_isEmpty] at hsum1
    exact zero_ne_one hsum1
  -- barycentres
  set x : I → Fin n → ℝ := fun i => ⨍ y in cell i.1, y ∂μ with hx
  have hcellne : ∀ i : I, μ (cell i.1) ≠ 0 := fun i => (Finset.mem_filter.mp i.2).2
  have hclose : ∀ i : I, ∀ y ∈ cell i.1, dist y (x i) ≤ δ := by
    intro i y hy
    have hmem : x i ∈ Metric.closedBall y δ := by
      apply Convex.set_average_mem (convex_closedBall y δ) Metric.isClosed_closedBall
        (hcellne i) (measure_ne_top μ _) _ hidint.integrableOn
      rw [ae_restrict_iff' (hcellm i.1)]
      exact Eventually.of_forall fun y' hy' => by
        rw [Metric.mem_closedBall, dist_comm]
        exact hdiam i.1 y hy y' hy'
    rw [Metric.mem_closedBall] at hmem
    rw [dist_comm]
    exact hmem
  have hnorm : ∀ i : I, ‖x i‖ ≤ R + δ := by
    intro i
    -- the cell meets `S`
    have hmeet : ∃ y, y ∈ cell i.1 ∧ y ∈ S := by
      by_contra hcon
      apply hcellne i
      apply measure_mono_null _ hμS
      intro y hy hyS
      exact hcon ⟨y, hy, hyS⟩
    obtain ⟨y, hy, hyS⟩ := hmeet
    have h1 := hclose i y hy
    have h2 : ‖x i‖ ≤ ‖y‖ + dist y (x i) := by
      rw [dist_eq_norm]
      have : x i = y - (y - x i) := by abel
      calc ‖x i‖ = ‖y - (y - x i)‖ := by rw [← this]
        _ ≤ ‖y‖ + ‖y - x i‖ := norm_sub_le _ _
    linarith [hR y hyS]
  refine ⟨I, inferInstance, hne, fun i => μ.real (cell i.1), x, fun i => cell i.1, hpos, hsum1,
    fun i => hcellm i.1, fun i j hij => hdisj hij, fun _ => rfl, hclose, hnorm, ?_⟩
  intro f hfconv hfint
  have hfc : Continuous f := hfconv.locallyLipschitz.continuous
  have hfμ : Integrable f μ := G54.integrable_of_compact_support μ hS hμS hfc.continuousOn
  have hjensen : ∀ i : I, μ.real (cell i.1) * f (x i) ≤ ∫ y in cell i.1, f y ∂μ := by
    intro i
    have h1 := hfconv.map_set_average_le (μ := μ) (t := cell i.1) (f := fun y => y)
      hfc.continuousOn isClosed_univ (hcellne i) (measure_ne_top μ _)
      (Eventually.of_forall fun _ => mem_univ _) hidint.integrableOn hfμ.integrableOn
    rw [setAverage_eq μ (fun y => f y) (cell i.1), smul_eq_mul] at h1
    have h2 := hpos i
    rw [inv_mul_eq_div, le_div_iff₀ h2] at h1
    rw [mul_comm]
    exact h1
  calc ∑ i : I, μ.real (cell i.1) * f (x i) ≤ ∑ i : I, ∫ y in cell i.1, f y ∂μ :=
        Finset.sum_le_sum fun i _ => hjensen i
    _ = ∫ y, f y ∂μ := (hsplit f hfμ).symm
    _ ≤ ∫ y, f y ∂γ := hdom f hfconv hfint

end ModDisc

section ModTwo

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal ContDiff

/-- **Two Gaussians for log-concave perturbations** (Hua–Song–Tudose, Corollary 2.6): if `ψ` is a
smooth, Lipschitz, convex function on `ℝⁿ` and `ν = e^{-ψ} γₙ` is a probability measure with mean
`m` (so that `ν` is `1`-uniformly log-concave), then `ν` is the law of `m + X + Y` for two (coupled)
standard Gaussian vectors `X, Y`. -/
def G54.TwoGaussians : Prop :=
  ∀ (n : ℕ) (ψ : (Fin n → ℝ) → ℝ), ConvexOn ℝ univ ψ → ContDiff ℝ ∞ ψ →
    (∃ L : ℝ, ∀ y y' : Fin n → ℝ, |ψ y - ψ y'| ≤ L * ‖y - y'‖) →
    IsProbabilityMeasure ((Measure.pi fun _ : Fin n => gaussianReal 0 1).withDensity
      (fun y => ENNReal.ofReal (Real.exp (-ψ y)))) →
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)),
      π.map Prod.fst = Measure.pi (fun _ : Fin n => gaussianReal 0 1) ∧
      π.map Prod.snd = Measure.pi (fun _ : Fin n => gaussianReal 0 1) ∧
      π.map (fun q => (fun k => ∫ y, y k
          ∂((Measure.pi fun _ : Fin n => gaussianReal 0 1).withDensity
            (fun y => ENNReal.ofReal (Real.exp (-ψ y))))) + (q.1 + q.2))
        = (Measure.pi fun _ : Fin n => gaussianReal 0 1).withDensity
          (fun y => ENNReal.ofReal (Real.exp (-ψ y)))

/-- **Atoms land in `A + A + A`.**  For a finitely supported law dominated by the Gaussian in the
convex order, the contracted atoms `(1 - ε) xᵢ` outside `A + A + A` carry total weight at most
`3 γₙ(Aᶜ)`.  (Proof of the Three Gaussians theorem via the entropic martingale coupling, combined
with the union bound for `X = G - G₁ - G₂`.) -/
theorem G54.atoms_landing (h2 : G54.TwoGaussians) {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (x : ι → Fin n → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD : ∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
      Integrable f (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) →
      ∑ i, p i * f (x i) ≤ ∫ y, f y ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
    (A : Set (Fin n → ℝ)) (hAm : MeasurableSet A) (hAb : Balanced ℝ A) :
    ∑ i, Set.indicator {i | (1 - ε) • x i ∉ A + A + A} p i
      ≤ 3 * (Measure.pi fun _ : Fin n => gaussianReal 0 1).real Aᶜ := by
  classical
  set γn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1) with hγn
  have hγn1 : IsProbabilityMeasure γn := by rw [hγn]; infer_instance
  obtain ⟨θ, hθ⟩ := G54.exists_softmax_gauss p hp hp1 x ε hε hε1 hD
  set a : ι → (Fin n → ℝ) → ℝ := fun j y => ∑ k, θ j k * (Fin.cons 1 y : Fin (n + 1) → ℝ) k
    with ha
  set Zs : (Fin n → ℝ) → ℝ := fun y => ∑ j, p j * Real.exp (a j y) with hZs
  have hZpos : ∀ y, 0 < Zs y := fun y => G54.lse_sum_pos p hp _
  set w : ι → (Fin n → ℝ) → ℝ := fun i y => p i * Real.exp (a i y) / Zs y with hw
  set ψ : ι → (Fin n → ℝ) → ℝ := fun i y => Real.log (Zs y) - a i y with hψ
  have hexp : ∀ i y, Real.exp (-(ψ i y)) = Real.exp (a i y) / Zs y := by
    intro i y
    simp only [hψ]
    rw [neg_sub, Real.exp_sub, Real.exp_log (hZpos y)]
  have hwexp : ∀ i y, w i y = p i * Real.exp (-(ψ i y)) := by
    intro i y
    rw [hexp]
    simp only [hw]
    ring
  have hexpw : ∀ i y, Real.exp (-(ψ i y)) = (p i)⁻¹ * w i y := by
    intro i y
    rw [hwexp, ← mul_assoc, inv_mul_cancel₀ (hp i).ne', one_mul]
  have hac : ∀ j, Continuous (a j) := fun j =>
    continuous_finsetSum _ (fun k _ =>
      continuous_const.mul ((continuous_apply k).comp (G54.continuous_cons n)))
  have hZc : Continuous Zs :=
    continuous_finsetSum _ (fun j _ => continuous_const.mul (Real.continuous_exp.comp (hac j)))
  have hwc : ∀ i, Continuous (w i) := fun i =>
    (continuous_const.mul (Real.continuous_exp.comp (hac i))).div hZc (fun y => (hZpos y).ne')
  have hψc : ∀ i, Continuous (ψ i) := fun i =>
    (hZc.log (fun y => (hZpos y).ne')).sub (hac i)
  have hw0 : ∀ i y, 0 ≤ w i y := fun i y =>
    div_nonneg (mul_nonneg (hp i).le (Real.exp_pos _).le) (hZpos y).le
  have hw1 : ∀ i y, w i y ≤ 1 := by
    intro i y
    simp only [hw]
    rw [div_le_one (hZpos y)]
    exact Finset.single_le_sum (f := fun j => p j * Real.exp (a j y))
      (fun j _ => (mul_pos (hp j) (Real.exp_pos _)).le) (Finset.mem_univ i)
  have hwsum : ∀ y, ∑ i, w i y = 1 := by
    intro y
    simp only [hw]
    rw [← Finset.sum_div, div_self (hZpos y).ne']
  have hwi : ∀ i, Integrable (w i) γn := fun i =>
    (integrable_const (1 : ℝ)).mono' (hwc i).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw0 i y)]
        exact hw1 i y)
  -- stationarity
  have hstat0 : ∀ i, ∫ y, w i y ∂γn = p i := by
    intro i
    have h1 := hθ i 0
    simp only [Fin.cons_zero, one_mul, mul_one] at h1
    exact h1
  have hstatk : ∀ i (k : Fin n), ∫ y, y k * w i y ∂γn = p i * ((1 - ε) * x i k) := by
    intro i k
    have h1 := hθ i k.succ
    simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul] at h1
    exact h1
  -- the conditional laws
  set ν : ι → Measure (Fin n → ℝ) := fun i =>
    γn.withDensity (fun y => ENNReal.ofReal (Real.exp (-(ψ i y)))) with hν
  have hdm : ∀ i, Measurable (fun y => ENNReal.ofReal (Real.exp (-(ψ i y)))) := fun i =>
    (Real.continuous_exp.comp (hψc i).neg).measurable.ennreal_ofReal
  have hexpi : ∀ i, Integrable (fun y => Real.exp (-(ψ i y))) γn := by
    intro i
    have h1 : (fun y => Real.exp (-(ψ i y))) = fun y => (p i)⁻¹ * w i y := funext (hexpw i)
    rw [h1]
    exact (hwi i).const_mul _
  have hexpint : ∀ i, ∫ y, Real.exp (-(ψ i y)) ∂γn = 1 := by
    intro i
    have h1 : (fun y => Real.exp (-(ψ i y))) = fun y => (p i)⁻¹ * w i y := funext (hexpw i)
    rw [h1, integral_const_mul, hstat0, inv_mul_cancel₀ (hp i).ne']
  have hν1 : ∀ i, IsProbabilityMeasure (ν i) := by
    intro i
    constructor
    simp only [hν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hexpi i)
        (Eventually.of_forall fun y => (Real.exp_pos _).le), hexpint, ENNReal.ofReal_one]
  have hmean : ∀ i (k : Fin n), ∫ y, y k ∂(ν i) = (1 - ε) * x i k := by
    intro i k
    simp only [hν]
    rw [integral_withDensity_eq_integral_toReal_smul (hdm i)
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
    have h1 : ∀ y : Fin n → ℝ, (ENNReal.ofReal (Real.exp (-(ψ i y)))).toReal • y k
        = (p i)⁻¹ * (y k * w i y) := by
      intro y
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, hexpw]
      ring
    rw [integral_congr_ae (Eventually.of_forall h1), integral_const_mul, hstatk,
      ← mul_assoc, inv_mul_cancel₀ (hp i).ne', one_mul]
  have hνA : ∀ i, (ν i).real Aᶜ = (p i)⁻¹ * ∫ y in Aᶜ, w i y ∂γn := by
    intro i
    simp only [hν]
    rw [measureReal_def, withDensity_apply _ hAm.compl,
      ← ofReal_integral_eq_lintegral_ofReal (hexpi i).integrableOn
        (Eventually.of_forall fun y => (Real.exp_pos _).le),
      ENNReal.toReal_ofReal (integral_nonneg fun y => (Real.exp_pos _).le),
      ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => hexpw i y)
  -- the key bound for a bad index
  have hkey : ∀ i, (1 - ε) • x i ∉ A + A + A → 1 ≤ 2 * γn.real Aᶜ + (ν i).real Aᶜ := by
    intro i hbad
    obtain ⟨hconv, hsmooth, hlip⟩ := G54.softmax_potential p hp θ i
    obtain ⟨π, hπ1, hπ2, hπ3⟩ := h2 n (ψ i) hconv hsmooth hlip (hν1 i)
    have hm : (fun k => ∫ y, y k ∂(ν i)) = (1 - ε) • x i := by
      funext k
      rw [hmean]
      simp
    have hπ3' : π.map (fun q => (1 - ε) • x i + (q.1 + q.2)) = ν i := by
      rw [← hm]
      exact hπ3
    have hπprob : IsProbabilityMeasure π := by
      constructor
      have h1 := Measure.map_apply (μ := π) (measurable_fst (α := Fin n → ℝ) (β := Fin n → ℝ))
        MeasurableSet.univ
      rw [hπ1, measure_univ] at h1
      simpa using h1.symm
    set G : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) :=
      fun q => (1 - ε) • x i + (q.1 + q.2) with hG
    have hGm : Measurable G := by
      have h0 : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 + q.2) :=
        measurable_fst.add measurable_snd
      exact measurable_const.add h0
    have hcover : (univ : Set ((Fin n → ℝ) × (Fin n → ℝ)))
        ⊆ (Prod.fst ⁻¹' Aᶜ) ∪ (Prod.snd ⁻¹' Aᶜ) ∪ (G ⁻¹' Aᶜ) := by
      intro q _
      by_contra hcon
      have h1 : q.1 ∈ A := by
        by_contra h
        exact hcon (Or.inl (Or.inl h))
      have h2' : q.2 ∈ A := by
        by_contra h
        exact hcon (Or.inl (Or.inr h))
      have h3 : G q ∈ A := by
        by_contra h
        exact hcon (Or.inr h)
      apply hbad
      have e : (1 - ε) • x i = G q + (-1 : ℝ) • q.1 + (-1 : ℝ) • q.2 := by
        simp only [hG]
        module
      rw [e]
      exact add_mem_add (add_mem_add h3 (balanced_iff_smul_mem.mp hAb (by simp) h1))
        (balanced_iff_smul_mem.mp hAb (by simp) h2')
    have h1 : π.real univ ≤ π.real (Prod.fst ⁻¹' Aᶜ) + π.real (Prod.snd ⁻¹' Aᶜ)
        + π.real (G ⁻¹' Aᶜ) :=
      (measureReal_mono hcover).trans ((measureReal_union_le _ _).trans
        (add_le_add_left (measureReal_union_le _ _) _))
    have e1 : π.real (Prod.fst ⁻¹' Aᶜ) = γn.real Aᶜ := by
      rw [measureReal_def, ← Measure.map_apply measurable_fst hAm.compl, hπ1, measureReal_def]
    have e2 : π.real (Prod.snd ⁻¹' Aᶜ) = γn.real Aᶜ := by
      rw [measureReal_def, ← Measure.map_apply measurable_snd hAm.compl, hπ2, measureReal_def]
    have e3 : π.real (G ⁻¹' Aᶜ) = (ν i).real Aᶜ := by
      rw [measureReal_def, ← Measure.map_apply hGm hAm.compl, hπ3', measureReal_def]
    rw [probReal_univ, e1, e2, e3] at h1
    linarith
  have hterm : ∀ i, Set.indicator {i | (1 - ε) • x i ∉ A + A + A} p i
      ≤ p i * (2 * γn.real Aᶜ + (ν i).real Aᶜ) := by
    intro i
    have h1 : 0 ≤ γn.real Aᶜ := measureReal_nonneg
    have h2' : 0 ≤ (ν i).real Aᶜ := measureReal_nonneg
    by_cases hbad : (1 - ε) • x i ∉ A + A + A
    · rw [Set.indicator_of_mem (show i ∈ {i | (1 - ε) • x i ∉ A + A + A} from hbad)]
      have h3 := hkey i hbad
      nlinarith [hp i]
    · rw [Set.indicator_of_notMem (show i ∉ {i | (1 - ε) • x i ∉ A + A + A} from hbad)]
      exact mul_nonneg (hp i).le (by linarith)
  calc ∑ i, Set.indicator {i | (1 - ε) • x i ∉ A + A + A} p i
      ≤ ∑ i, p i * (2 * γn.real Aᶜ + (ν i).real Aᶜ) := Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * γn.real Aᶜ + ∑ i, ∫ y in Aᶜ, w i y ∂γn := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hp1, one_mul]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hνA, ← mul_assoc, mul_inv_cancel₀ (hp i).ne', one_mul]
    _ = 2 * γn.real Aᶜ + γn.real Aᶜ := by
        rw [← integral_finsetSum _ (fun i _ => (hwi i).integrableOn)]
        simp only [hwsum]
        simp
    _ = 3 * γn.real Aᶜ := by ring

end ModTwo

section ModLand

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Pointwise ENNReal ContDiff

/-- **Landing property from the two-Gaussian decomposition.**  A compactly supported probability
measure on `ℝⁿ` dominated by the Gaussian in the convex order gives mass at least `1/2` to
`A + A + A` whenever `A` is a balanced compact set with `γₙ(A) ≥ 0.99`.  (Discretise, contract by
`1 - ε`, apply the entropic coupling and the union bound, then let the mesh go to zero.) -/
theorem G54.landing_of_twoGaussians (h2 : G54.TwoGaussians) :
    ∀ (n : ℕ) (μ : Measure (Fin n → ℝ)), IsProbabilityMeasure μ →
      (∃ S : Set (Fin n → ℝ), IsCompact S ∧ μ Sᶜ = 0) →
      (∀ f : (Fin n → ℝ) → ℝ, ConvexOn ℝ univ f →
        Integrable f (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
        ∫ x, f x ∂μ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) →
      ∀ A : Set (Fin n → ℝ), IsCompact A → Balanced ℝ A →
        (0.99 : ℝ≥0∞) ≤ (Measure.pi fun _ : Fin n => gaussianReal 0 1) A →
        (1 / 2 : ℝ≥0∞) ≤ μ (A + A + A) := by
  intro n μ hμ hcpt hdom A hAc hAb hAm
  classical
  obtain ⟨S, hS, hμS⟩ := hcpt
  set γn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1) with hγn
  have hγn1 : IsProbabilityMeasure γn := by rw [hγn]; infer_instance
  have hAmeas : MeasurableSet A := hAc.measurableSet
  have hAr : (0.99 : ℝ) ≤ γn.real A := G54.le_real_of_ofScientific_le γn A _ _ _ hAm
  have hAcr : γn.real Aᶜ ≤ 0.01 := by
    rw [probReal_compl_eq_one_sub hAmeas]
    linarith
  have hFc : IsCompact (A + A + A) := (hAc.add hAc).add hAc
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  -- the main claim: every closed thickening of `A + A + A` has measure `≥ 0.97`
  have hclaim : ∀ r : ℝ, 0 < r → (0.97 : ℝ) ≤ μ.real (Metric.cthickening r (A + A + A)) := by
    intro r hr
    set δ : ℝ := r / 2 with hδdef
    have hδ : 0 < δ := by positivity
    set R' : ℝ := max R 0 with hR'
    have hR'0 : 0 ≤ R' := le_max_right _ _
    set ε : ℝ := min 1 (δ / (R' + δ + 1)) with hεdef
    have hden : 0 < R' + δ + 1 := by linarith
    have hε : 0 < ε := lt_min one_pos (div_pos hδ hden)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεR : ε * (R' + δ) ≤ δ := by
      have h1 : ε ≤ δ / (R' + δ + 1) := min_le_right _ _
      have h2 : ε * (R' + δ + 1) ≤ δ := by
        rw [le_div_iff₀ hden] at h1
        exact h1
      nlinarith
    obtain ⟨ι, hfin, hne, p, x, C, hp, hp1, hCm, hCd, hCp, hCx, hxn, hD⟩ :=
      G54.exists_discretization μ hS hμS (R := R')
        (fun y hy => (hR y hy).trans (le_max_left _ _)) γn hdom δ hδ
    have hbad := G54.atoms_landing h2 p hp hp1 x ε hε hε1 hD A hAmeas hAb
    have hgood : ∀ i, (1 - ε) • x i ∈ A + A + A → C i ⊆ Metric.cthickening r (A + A + A) := by
      intro i hi y hy
      apply Metric.mem_cthickening_of_dist_le y ((1 - ε) • x i) r (A + A + A) hi
      have h1 : dist (x i) ((1 - ε) • x i) = ε * ‖x i‖ := by
        rw [dist_eq_norm]
        have h2 : x i - (1 - ε) • x i = ε • x i := by module
        rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      have h3 : ε * ‖x i‖ ≤ δ :=
        (mul_le_mul_of_nonneg_left (hxn i) hε.le).trans hεR
      calc dist y ((1 - ε) • x i) ≤ dist y (x i) + dist (x i) ((1 - ε) • x i) :=
            dist_triangle _ _ _
        _ ≤ δ + δ := by
            rw [h1]
            exact add_le_add (hCx i y hy) h3
        _ = r := by
            rw [hδdef]
            ring
    set Th : Set (Fin n → ℝ) := Metric.cthickening r (A + A + A) with hTh
    have hThm : MeasurableSet Th := Metric.isClosed_cthickening.measurableSet
    have hsumle : ∑ i, Set.indicator {i | (1 - ε) • x i ∈ A + A + A} p i ≤ μ.real Th := by
      have h1 : ∀ i, Set.indicator {i | (1 - ε) • x i ∈ A + A + A} p i ≤ μ.real (C i ∩ Th) := by
        intro i
        by_cases hi : (1 - ε) • x i ∈ A + A + A
        · rw [Set.indicator_of_mem (show i ∈ {i | (1 - ε) • x i ∈ A + A + A} from hi),
            inter_eq_self_of_subset_left (hgood i hi), hCp]
        · rw [Set.indicator_of_notMem (show i ∉ {i | (1 - ε) • x i ∈ A + A + A} from hi)]
          exact measureReal_nonneg
      have h2 : μ.real (⋃ i ∈ (Finset.univ : Finset ι), C i ∩ Th)
          = ∑ i, μ.real (C i ∩ Th) := by
        refine measureReal_biUnion_finset ?_ ?_ ?_
        · intro i _ j _ hij
          exact (hCd i j hij).mono inter_subset_left inter_subset_left
        · intro i _
          exact (hCm i).inter hThm
        · intro i _
          exact measure_ne_top μ _
      calc ∑ i, Set.indicator {i | (1 - ε) • x i ∈ A + A + A} p i
          ≤ ∑ i, μ.real (C i ∩ Th) := Finset.sum_le_sum fun i _ => h1 i
        _ = μ.real (⋃ i ∈ (Finset.univ : Finset ι), C i ∩ Th) := h2.symm
        _ ≤ μ.real Th := by
            refine measureReal_mono ?_ (measure_ne_top μ _)
            intro y hy
            simp only [mem_iUnion] at hy
            obtain ⟨i, -, hyi⟩ := hy
            exact hyi.2
    have hsplit : ∑ i, Set.indicator {i | (1 - ε) • x i ∈ A + A + A} p i
        + ∑ i, Set.indicator {i | (1 - ε) • x i ∉ A + A + A} p i = 1 := by
      rw [← Finset.sum_add_distrib]
      refine Eq.trans ?_ hp1
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : (1 - ε) • x i ∈ A + A + A
      · rw [Set.indicator_of_mem (show i ∈ {i | (1 - ε) • x i ∈ A + A + A} from hi),
          Set.indicator_of_notMem (show i ∉ {i | (1 - ε) • x i ∉ A + A + A} from
            fun h => h hi), add_zero]
      · rw [Set.indicator_of_notMem (show i ∉ {i | (1 - ε) • x i ∈ A + A + A} from hi),
          Set.indicator_of_mem (show i ∈ {i | (1 - ε) • x i ∉ A + A + A} from hi), zero_add]
    linarith
  -- pass to the limit `r → 0`
  have hlim := tendsto_measure_cthickening_of_isClosed (μ := μ) (s := A + A + A)
    ⟨1, one_pos, measure_ne_top μ _⟩ hFc.isClosed
  have hlim' : Tendsto (fun r => μ (Metric.cthickening r (A + A + A))) (𝓝[>] (0 : ℝ))
      (𝓝 (μ (A + A + A))) := hlim.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal 0.97 ≤ μ (Metric.cthickening r (A + A + A)) := by
    refine eventually_nhdsWithin_of_forall fun r hr => ?_
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)]
    exact hclaim r hr
  have hfinal : ENNReal.ofReal 0.97 ≤ μ (A + A + A) := ge_of_tendsto hlim' hev
  refine le_trans ?_ hfinal
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos]
    simp
  rw [hhalf]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **Green's Problem 54, conditional on the two-Gaussian decomposition of log-concave
perturbations of the Gaussian.** -/
theorem G54.green54_of_twoGaussians (h2 : G54.TwoGaussians) : type_of% @Green54.green_54 :=
  G54.green54_of_landing (G54.landing_of_twoGaussians h2)

/-- **Lipschitz Gaussian transport** (a weak form of Caffarelli's contraction theorem:
L. A. Caffarelli, Comm. Math. Phys. 214 (2000), Theorem 11): if `ψ` is a smooth, Lipschitz, convex
function on `ℝⁿ` and `e^{-ψ} γₙ` is a probability measure, then it is the image of the standard
Gaussian measure `γₙ` under a map `F` which is `2`-Lipschitz for the Euclidean distance.
Caffarelli's theorem gives a `1`-Lipschitz map (the Brenier map); only the constant `2` is needed
here. -/
def G54.CaffarelliContraction : Prop :=
  ∀ (n : ℕ) (ψ : (Fin n → ℝ) → ℝ), ConvexOn ℝ univ ψ → ContDiff ℝ ∞ ψ →
    (∃ L : ℝ, ∀ y y' : Fin n → ℝ, |ψ y - ψ y'| ≤ L * ‖y - y'‖) →
    IsProbabilityMeasure ((Measure.pi fun _ : Fin n => gaussianReal 0 1).withDensity
      (fun y => ENNReal.ofReal (Real.exp (-ψ y)))) →
    ∃ F : (Fin n → ℝ) → (Fin n → ℝ),
      (∀ y y' : Fin n → ℝ, ∑ k, (F y k - F y' k) ^ 2 ≤ 4 * ∑ k, (y k - y' k) ^ 2) ∧
      (Measure.pi fun _ : Fin n => gaussianReal 0 1).map F
        = (Measure.pi fun _ : Fin n => gaussianReal 0 1).withDensity
          (fun y => ENNReal.ofReal (Real.exp (-ψ y)))

/-- **The Lipschitz image lemma** (A. Song, *Sum of Gaussian vectors and large sets*,
arXiv:2602.22342, Lemma 2.4; Hua–Song–Tudose, Lemma 2.3): if `F : ℝⁿ → ℝⁿ` is `1`-Lipschitz for the
Euclidean distance and `G` is a standard Gaussian vector, then `F(G) - 𝔼 F(G)` has the law of
`(X + Y)/2` for two (coupled) standard Gaussian vectors `X, Y`. -/
def G54.GaussianLipschitzImage : Prop :=
  ∀ (n : ℕ) (F : (Fin n → ℝ) → (Fin n → ℝ)),
    (∀ y y' : Fin n → ℝ, ∑ k, (F y k - F y' k) ^ 2 ≤ ∑ k, (y k - y' k) ^ 2) →
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)),
      π.map Prod.fst = Measure.pi (fun _ : Fin n => gaussianReal 0 1) ∧
      π.map Prod.snd = Measure.pi (fun _ : Fin n => gaussianReal 0 1) ∧
      π.map (fun q => (2⁻¹ : ℝ) • (q.1 + q.2))
        = (Measure.pi fun _ : Fin n => gaussianReal 0 1).map
          (fun y => F y - fun k => ∫ y', F y' k ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))

theorem G54.continuous_of_euclid_lip {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ∀ y y' : Fin n → ℝ, ∑ k, (F y k - F y' k) ^ 2 ≤ ∑ k, (y k - y' k) ^ 2) :
    Continuous F := by
  refine continuous_pi (fun k => ?_)
  have hlip : LipschitzWith ⟨Real.sqrt n, Real.sqrt_nonneg _⟩ (fun y => F y k) := by
    apply LipschitzWith.of_dist_le_mul
    intro y y'
    rw [Real.dist_eq, dist_eq_norm]
    have h1 : (F y k - F y' k) ^ 2 ≤ ∑ k, (y k - y' k) ^ 2 :=
      (Finset.single_le_sum (f := fun j => (F y j - F y' j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ k)).trans (hF y y')
    have h2 : ∑ k, (y k - y' k) ^ 2 ≤ n * ‖y - y'‖ ^ 2 := by
      calc ∑ k : Fin n, (y k - y' k) ^ 2 ≤ ∑ _k : Fin n, ‖y - y'‖ ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h3 := norm_le_pi_norm (y - y') j
            rw [Real.norm_eq_abs] at h3
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = n * ‖y - y'‖ ^ 2 := by simp
    have h3 : |F y k - F y' k| ≤ Real.sqrt (n * ‖y - y'‖ ^ 2) := Real.abs_le_sqrt (h1.trans h2)
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg _)] at h3
    exact h3
  exact hlip.continuous

/-- A `2`-Lipschitz Gaussian transport map and the Lipschitz image lemma (applied to `F / 2`) give
the two-Gaussian decomposition `W - 𝔼 W = X + Y`. -/
theorem G54.twoGaussians_of_caffarelli_lipschitzImage (hC : G54.CaffarelliContraction)
    (hL : G54.GaussianLipschitzImage) : G54.TwoGaussians := by
  intro n ψ hconv hsmooth hlip hprob
  obtain ⟨F, hF, hFmap⟩ := hC n ψ hconv hsmooth hlip hprob
  set F' : (Fin n → ℝ) → (Fin n → ℝ) := fun y => (2⁻¹ : ℝ) • F y with hF'
  have hF'lip : ∀ y y' : Fin n → ℝ, ∑ k, (F' y k - F' y' k) ^ 2 ≤ ∑ k, (y k - y' k) ^ 2 := by
    intro y y'
    have h1 : ∑ k, (F' y k - F' y' k) ^ 2 = 4⁻¹ * ∑ k, (F y k - F y' k) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hF', Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1]
    have h2 := hF y y'
    linarith
  obtain ⟨π, h1, h2, h3⟩ := hL n F' hF'lip
  refine ⟨π, h1, h2, ?_⟩
  have hF'm : Measurable F' := (G54.continuous_of_euclid_lip F' hF'lip).measurable
  have hFeq : F = fun y => (2 : ℝ) • F' y := by
    funext y
    simp only [hF', smul_smul]
    norm_num
  have hFm : Measurable F := by
    rw [hFeq]
    exact hF'm.const_smul (2 : ℝ)
  set γn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1) with hγn
  have hmean : (fun k => ∫ y, y k ∂(γn.withDensity (fun y => ENNReal.ofReal (Real.exp (-ψ y)))))
      = fun k => ∫ y', F y' k ∂γn := by
    funext k
    rw [← hFmap, integral_map hFm.aemeasurable (measurable_pi_apply k).aestronglyMeasurable]
  rw [hmean]
  set m : Fin n → ℝ := fun k => ∫ y', F y' k ∂γn with hm
  set m' : Fin n → ℝ := fun k => ∫ y', F' y' k ∂γn with hm'
  have hmm' : m = (2 : ℝ) • m' := by
    funext k
    simp only [hm, hm', hF', Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul]
    ring
  have hsm : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (2⁻¹ : ℝ) • (q.1 + q.2)) := by
    have h0 : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 + q.2) :=
      measurable_fst.add measurable_snd
    exact h0.const_smul (2⁻¹ : ℝ)
  have hadd : Measurable (fun z : Fin n → ℝ => m + (2 : ℝ) • z) :=
    measurable_const.add (measurable_id.const_smul (2 : ℝ))
  have e1 : π.map (fun q => m + (q.1 + q.2))
      = (π.map (fun q => (2⁻¹ : ℝ) • (q.1 + q.2))).map (fun z => m + (2 : ℝ) • z) := by
    rw [Measure.map_map hadd hsm]
    congr 1
    funext q
    simp only [Function.comp_apply, smul_smul]
    norm_num
  have hsub : Measurable (fun y => F' y - m') := hF'm.sub measurable_const
  rw [e1, h3, Measure.map_map hadd hsub]
  have e2 : (fun z : Fin n → ℝ => m + (2 : ℝ) • z) ∘ (fun y => F' y - m') = F := by
    funext y
    simp only [Function.comp_apply, hmm', smul_sub]
    rw [hFeq]
    abel
  rw [e2, hFmap]

/-- **Green's Problem 54 (Talagrand's convexity conjecture), conditional on (a weak form of)
Caffarelli's contraction theorem and the Lipschitz image lemma.** -/
theorem G54.green54_of_caffarelli_lipschitzImage (hC : G54.CaffarelliContraction)
    (hL : G54.GaussianLipschitzImage) : type_of% @Green54.green_54 :=
  G54.green54_of_twoGaussians (G54.twoGaussians_of_caffarelli_lipschitzImage hC hL)

end ModLand

section ModPrekopa

/- # Prékopa–Leindler for continuous positive densities -/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace G54

/-- The quantile of a continuous, strictly positive integrable density has derivative
equal to the total mass divided by the density at the quantile. -/
theorem exists_quantile_hasDerivAt {f : ℝ → ℝ} (hc : Continuous f)
    (hi : Integrable f) (hp : ∀ x, 0 < f x) :
    ∃ Q : ℝ → ℝ, StrictMonoOn Q (Ioo 0 1) ∧
      ∀ t ∈ Ioo 0 1, HasDerivAt Q ((∫ x, f x) / f (Q t)) t := by
  classical
  let Z := ∫ x, f x
  have hZ : 0 < Z := integral_pos_of_integrable_nonneg_nonzero hc hi
    (fun x => (hp x).le) (hp 0).ne'
  let F := fun z : ℝ => ∫ x in Iic z, f x
  have hF (x : ℝ) : HasDerivAt F (f x) x := by
    have eqn : F = fun y => (∫ z in (0 : ℝ)..y, f z) + F 0 := by
      funext y
      rw [← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
      simp [F]
    rw [eqn]
    exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const _
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hFmono : StrictMono F := strictMono_of_deriv_pos fun x => (hF x).deriv ▸ hp x
  have hFembed := hFmono.isEmbedding_of_ordConnected (isPreconnected_range hFc).ordConnected
  have hbot : Tendsto F atBot (𝓝 0) := tendsto_integral_Iic_zero tendsto_id
  have htop : Tendsto F atTop (𝓝 Z) := by
    have ht : Tendsto (fun x : ℝ => ∫ z in Ioi x, f z) atTop (𝓝 0) :=
      tendsto_integral_Ioi_zero tendsto_id
    have eqn (x : ℝ) : F x = Z - ∫ z in Ioi x, f z := by
      exact eq_sub_of_add_eq (intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn)
    change Tendsto (fun x => F x) atTop (𝓝 Z)
    simpa only [eqn, sub_zero] using (tendsto_const_nhds (x := Z)).sub ht
  let Q := fun t : ℝ => Function.invFun F (Z * t)
  have hQ {t : ℝ} (ht : t ∈ Ioo 0 1) : F (Q t) = Z * t := by
    apply Function.invFun_eq
    apply mem_range_of_exists_le_of_exists_ge hFc
    · exact (hbot.eventually_le_const (mul_pos hZ ht.1)).exists
    · exact (htop.eventually_const_le (by nlinarith [ht.2, mul_pos hZ (sub_pos.mpr ht.2)])).exists
  refine ⟨Q, fun x hx y hy hxy => hFmono.lt_iff_lt.mp (by rw [hQ hx, hQ hy]; gcongr), ?_⟩
  intro t ht
  have he : F ∘ Q =ᶠ[𝓝 t] fun u => Z * u := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu using hQ hu
  have hd : HasDerivAt (fun u : ℝ => Z * u) Z t := by
    simpa using (hasDerivAt_id t).const_mul Z
  have hqc : ContinuousAt Q t :=
    hFembed.isInducing.continuousAt_iff.mpr (hd.continuousAt.congr he.symm)
  exact HasDerivAt.of_comp_left hqc (hF _) hd (hp _).ne' he

/-- One-dimensional Prékopa–Leindler, for strictly positive continuous integrable
input densities. The majorant need only be nonnegative and integrable. -/
theorem prekopaLeindler_real {f g h : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hfc : Continuous f) (hfi : Integrable f) (hfp : ∀ x, 0 < f x)
    (hgc : Continuous g) (hgi : Integrable g) (hgp : ∀ x, 0 < g x)
    (hhi : Integrable h) (hhp : ∀ x, 0 ≤ h x)
    (hdom : ∀ x y, f x ^ a * g y ^ b ≤ h (a * x + b * y)) :
    (∫ x, f x) ^ a * (∫ x, g x) ^ b ≤ ∫ x, h x := by
  obtain ⟨P, hPm, hPd⟩ := exists_quantile_hasDerivAt hfc hfi hfp
  obtain ⟨Q, hQm, hQd⟩ := exists_quantile_hasDerivAt hgc hgi hgp
  let Z := ∫ x, f x
  let W := ∫ x, g x
  have hZ : 0 < Z := integral_pos_of_integrable_nonneg_nonzero hfc hfi
    (fun x => (hfp x).le) (hfp 0).ne'
  have hW : 0 < W := integral_pos_of_integrable_nonneg_nonzero hgc hgi
    (fun x => (hgp x).le) (hgp 0).ne'
  let T := fun t => a * P t + b * Q t
  let D := fun t => a * (Z / f (P t)) + b * (W / g (Q t))
  let I : Set ℝ := Ioo 0 1
  have hD (t : ℝ) (ht : t ∈ I) : HasDerivWithinAt T (D t) I t :=
    (((hPd t ht).const_mul a).add ((hQd t ht).const_mul b)).hasDerivWithinAt
  have hT : MonotoneOn T I := by
    intro x hx y hy hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (hPm.monotoneOn hx hy hxy) ha)
      (mul_le_mul_of_nonneg_left (hQm.monotoneOn hx hy hxy) hb)
  have hI : MeasurableSet I := measurableSet_Ioo
  have hi : IntegrableOn (fun t => D t • h (T t)) I :=
    (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hI hD hT h).mp hhi.integrableOn
  have hpt (t : ℝ) : Z ^ a * W ^ b ≤ D t • h (T t) := by
    have hf := hfp (P t)
    have hg := hgp (Q t)
    have hj := Real.geom_mean_le_arith_mean2_weighted ha hb
      (div_nonneg hZ.le hf.le) (div_nonneg hW.le hg.le) hab
    calc
      Z ^ a * W ^ b =
          ((Z / f (P t)) ^ a * (W / g (Q t)) ^ b) * (f (P t) ^ a * g (Q t) ^ b) := by
            rw [Real.div_rpow hZ.le hf.le, Real.div_rpow hW.le hg.le]
            field_simp [(Real.rpow_pos_of_pos hf a).ne', (Real.rpow_pos_of_pos hg b).ne']
      _ ≤ D t * h (T t) := mul_le_mul hj (hdom _ _)
            (mul_nonneg (Real.rpow_nonneg hf.le _) (Real.rpow_nonneg hg.le _))
            (add_nonneg (mul_nonneg ha (div_nonneg hZ.le hf.le))
              (mul_nonneg hb (div_nonneg hW.le hg.le)))
      _ = _ := rfl
  change Z ^ a * W ^ b ≤ _
  calc
    Z ^ a * W ^ b = ∫ _ in I, Z ^ a * W ^ b := by
      simp [I]
    _ ≤ ∫ t in I, D t • h (T t) :=
      setIntegral_mono_on (integrableOn_const (by simp [I])) hi hI (fun t _ => hpt t)
    _ = ∫ x in T '' I, h x :=
      (integral_image_eq_integral_deriv_smul_of_monotoneOn hI hD hT h).symm
    _ ≤ ∫ x, h x := setIntegral_le_integral hhi (ae_of_all _ hhp)

private theorem gaussianPDF_weighted_mean {a b : ℝ}
    (hab : a + b = 1) (x y : ℝ) :
    (gaussianPDFReal 0 1 x ^ a * gaussianPDFReal 0 1 y ^ b) *
      Real.exp (a*b/2*(x-y)^2) =
      gaussianPDFReal 0 1 (a * x + b * y) := by
  let c := (Real.sqrt (2 * Real.pi))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have den (t : ℝ) : gaussianPDFReal 0 1 t = c * Real.exp (-(t ^ 2) / 2) := by
    simp [gaussianPDFReal, c]
  rw [den, den, den, Real.mul_rpow hc.le (Real.exp_pos _).le,
    Real.mul_rpow hc.le (Real.exp_pos _).le]
  rw [← Real.exp_mul, ← Real.exp_mul]
  calc
    _ = (c ^ a * c ^ b) * Real.exp ((-(x ^ 2) / 2) * a + (-(y ^ 2) / 2) * b + a*b/2*(x-y)^2) := by
      rw [Real.exp_add, Real.exp_add]; ring
    _ = _ := by
      rw [← Real.rpow_add hc, hab, Real.rpow_one]
      congr 2
      linear_combination (a*x^2+b*y^2) / 2 * hab

private theorem gaussianPL_one {f g h : ℝ → ℝ} {B a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    (hfb : ∀ x, f x ∈ Ioc 0 B) (hgb : ∀ x, g x ∈ Ioc 0 B)
    (hhb : ∀ x, h x ∈ Ioc 0 B)
    (hdom : ∀ x y, f x ^ a * g y ^ b ≤ h (a * x + b * y) * Real.exp (a*b/2*(x-y)^2)) :
    (∫ x, f x ∂gaussianReal 0 1) ^ a * (∫ x, g x ∂gaussianReal 0 1) ^ b
      ≤ ∫ x, h x ∂gaussianReal 0 1 := by
  let p := gaussianPDFReal 0 1
  have hp (x : ℝ) : 0 < p x := gaussianPDFReal_pos _ _ _ one_ne_zero
  have hpc : Continuous p := by unfold p; rw [gaussianPDFReal_def]; fun_prop
  have hpi (F : ℝ → ℝ) (hc : Continuous F) (hbnd : ∀ x, F x ∈ Ioc 0 B) :
      Integrable (fun x => p x * F x) := by
    apply ((integrable_gaussianPDFReal 0 1).mul_const B).mono' (hpc.mul hc).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change ‖p x * F x‖ ≤ p x * B
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hp x) (hbnd x).1)]
      exact mul_le_mul_of_nonneg_left (hbnd x).2 (hp x).le
  simp only [integral_gaussianReal_eq_integral_smul (v := 1) one_ne_zero, smul_eq_mul]
  apply prekopaLeindler_real ha hb hab (hpc.mul hfc) (hpi _ hfc hfb)
    (fun x => mul_pos (hp x) (hfb x).1) (hpc.mul hgc) (hpi _ hgc hgb)
    (fun x => mul_pos (hp x) (hgb x).1) (hpi _ hhc hhb)
    (fun x => mul_nonneg (hp x).le (hhb x).1.le)
  intro x y
  change (p x * f x) ^ a * (p y * g y) ^ b ≤ _
  rw [Real.mul_rpow (hp x).le (hfb x).1.le, Real.mul_rpow (hp y).le (hgb y).1.le]
  calc
    _ = (p x ^ a * p y ^ b) * (f x ^ a * g y ^ b) := by ring
    _ ≤ (p x ^ a * p y ^ b) * (h (a*x+b*y) * Real.exp (a*b/2*(x-y)^2)) :=
      mul_le_mul_of_nonneg_left (hdom _ _) <|
        mul_nonneg (Real.rpow_nonneg (hp x).le _) (Real.rpow_nonneg (hp y).le _)
    _ = p (a*x+b*y) * h (a*x+b*y) := by
      dsimp only [p]
      rw [← gaussianPDF_weighted_mean hab x y]
      ring

private theorem pl_cons_cont (n : ℕ) :
    Continuous (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n+1) → ℝ)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (continuous_fst : Continuous fun p : ℝ × (Fin n → ℝ) => p.1)
  · simp only [Fin.cons_succ]
    fun_prop

private theorem gaussianPL_section {n : ℕ} {B : ℝ}
    (f : (Fin (n+1) → ℝ) → ℝ) (hc : Continuous f) (hb : ∀ x, f x ∈ Ioc 0 B) :
    let S := fun t : ℝ => ∫ z, f (Fin.cons t z) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
    Continuous S ∧ (∀ t, S t ∈ Ioc 0 B) ∧
      (∫ x, f x ∂(Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1)) =
      ∫ t, S t ∂gaussianReal 0 1 := by
  let γ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let F := fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2)
  have hFc : Continuous F := hc.comp (pl_cons_cont n)
  have hF (p : ℝ × (Fin n → ℝ)) : ‖F p‖ ≤ B := by
    rw [Real.norm_eq_abs, abs_of_pos (hb _).1]
    exact (hb _).2
  have hfci (t : ℝ) : Continuous (fun z : Fin n → ℝ => F (t,z)) :=
    hFc.comp (continuous_const.prodMk continuous_id)
  have hfi (t : ℝ) : Integrable (fun z => F (t,z)) γ :=
    (integrable_const B).mono' (hfci t).aestronglyMeasurable (ae_of_all _ fun z => hF (t,z))
  refine ⟨continuous_of_dominated (fun t => (hfci t).aestronglyMeasurable)
    (fun t => ae_of_all _ fun z => hF (t,z)) (integrable_const B)
    (ae_of_all _ fun z => hFc.comp (continuous_id.prodMk continuous_const)), ?_, ?_⟩
  · intro t
    constructor
    · apply (integral_pos_iff_support_of_nonneg (fun z => (hb (Fin.cons t z)).1.le) (hfi t)).mpr
      have h : Function.support (fun z : Fin n → ℝ => F (t, z)) = univ :=
        Set.eq_univ_of_forall fun z => (hb _).1.ne'
      change 0 < γ (Function.support (fun z => F (t,z)))
      rw [h, measure_univ]
      exact zero_lt_one
    · exact (integral_mono (hfi t) (integrable_const B) (fun z => (hb _).2)).trans_eq (by simp)
  · have hi : Integrable F ((gaussianReal 0 1).prod γ) :=
      (integrable_const B).mono' hFc.aestronglyMeasurable (ae_of_all _ hF)
    rw [← integral_prod F hi]
    rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0).symm).integral_comp' f]
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, γ, F]

/-- Prékopa–Leindler for bounded positive continuous functions under a product
of standard Gaussian measures, obtained by iterating its one-dimensional form. -/
theorem prekopaLeindler_gaussian_sharp_bounded {n : ℕ} {f g h : (Fin n → ℝ) → ℝ}
    {B a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    (hfb : ∀ x, f x ∈ Ioc 0 B) (hgb : ∀ x, g x ∈ Ioc 0 B) (hhb : ∀ x, h x ∈ Ioc 0 B)
    (hdom : ∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y) *
      Real.exp (a*b/2 * ∑ i, (x i-y i)^2)) :
    let γ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
    (∫ x, f x ∂γ) ^ a * (∫ x, g x ∂γ) ^ b ≤ ∫ x, h x ∂γ := by
  induction n generalizing B with
  | zero =>
    have eqn (F : (Fin 0 → ℝ) → ℝ) :
        (∫ x, F x ∂(Measure.pi fun _ : Fin 0 => gaussianReal 0 1)) = F 0 := by
      have he : F = fun _ => F 0 := funext fun x => congrArg F (Subsingleton.elim x 0)
      conv_lhs => rw [he]
      simp
    dsimp only
    rw [eqn f, eqn g, eqn h]
    simpa using hdom 0 0
  | succ n ih =>
    obtain ⟨hF, hFb, eF⟩ := gaussianPL_section f hfc hfb
    obtain ⟨hG, hGb, eG⟩ := gaussianPL_section g hgc hgb
    obtain ⟨hH, hHb, eH⟩ := gaussianPL_section h hhc hhb
    dsimp only
    rw [eF, eG, eH]
    apply gaussianPL_one ha hb hab hF hG hH hFb hGb hHb
    intro x y
    have hcons (s : ℝ) : Continuous (fun z : Fin n → ℝ => (Fin.cons s z : Fin (n+1) → ℝ)) :=
      (pl_cons_cont n).comp (continuous_const.prodMk continuous_id)
    let c := Real.exp (a*b/2*(x-y)^2)
    have hc : 1 ≤ c := Real.one_le_exp (by positivity)
    have hc0 : 0 < c := Real.exp_pos _
    have hBC : B ≤ B * c := le_mul_of_one_le_right ((hfb 0).1.le.trans (hfb 0).2) hc
    have hres := ih (B := B*c) (hfc.comp (hcons x)) (hgc.comp (hcons y))
      ((hhc.comp (hcons (a*x+b*y))).mul (continuous_const (y := c)))
      (fun z => ⟨(hfb _).1, (hfb _).2.trans hBC⟩)
      (fun z => ⟨(hgb _).1, (hgb _).2.trans hBC⟩)
      (fun z => ⟨mul_pos (hhb _).1 hc0, mul_le_mul_of_nonneg_right (hhb _).2 hc0.le⟩)
    apply (by simpa [Function.comp_def, Pi.mul_apply, integral_mul_const, c] using hres)
    intro z w
    have eqn : a • Fin.cons x z + b • Fin.cons y w =
        (Fin.cons (a*x+b*y) (a • z + b • w) : Fin (n+1) → ℝ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    simpa only [eqn, Function.comp_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      mul_add, Real.exp_add, c, Pi.mul_apply, mul_assoc] using hdom (Fin.cons x z) (Fin.cons y w)

/-- Sharp Gaussian Prékopa–Leindler retains the quadratic gain from the
Gaussian density at a convex combination. -/
theorem prekopaLeindler_gaussian_sharp {n : ℕ} {f g h : (Fin n → ℝ) → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (hhp : ∀ x, 0 < h x)
    (hfi : Integrable f (Measure.pi fun _ : Fin n => gaussianReal 0 1))
    (hgi : Integrable g (Measure.pi fun _ : Fin n => gaussianReal 0 1))
    (hhi : Integrable h (Measure.pi fun _ : Fin n => gaussianReal 0 1))
    (hdom : ∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y) *
      Real.exp (a*b/2 * ∑ i, (x i-y i)^2)) :
    let γ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
    (∫ x, f x ∂γ) ^ a * (∫ x, g x ∂γ) ^ b ≤ ∫ x, h x ∂γ := by
  let γ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let B := fun k : ℕ => (k : ℝ) + 1
  have hB (k : ℕ) : 0 < B k := by dsimp [B]; positivity
  let truncate := fun k (F : (Fin n → ℝ) → ℝ) x => min (F x) (B k)
  have htc (k : ℕ) {F : (Fin n → ℝ) → ℝ} (hc : Continuous F) : Continuous (truncate k F) :=
    hc.min continuous_const
  have htb (k : ℕ) {F : (Fin n → ℝ) → ℝ} (hp : ∀ x, 0 < F x) (x) :
      truncate k F x ∈ Ioc 0 (B k) := ⟨lt_min (hp x) (hB k), min_le_right _ _⟩
  have htlim {F : (Fin n → ℝ) → ℝ} (hc : Continuous F) (hp : ∀ x, 0 < F x) (hi : Integrable F γ) :
      Tendsto (fun k => ∫ x, truncate k F x ∂γ) atTop (𝓝 (∫ x, F x ∂γ)) := by
    apply tendsto_integral_of_dominated_convergence F (fun k => (htc k hc).aestronglyMeasurable) hi
    · exact fun k => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (htb k hp x).1]
        exact min_le_left _ _
    · apply ae_of_all
      intro x
      apply tendsto_const_nhds.congr'
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (F x))]
        with k hk
      exact (min_eq_left (by dsimp [B]; linarith : F x ≤ B k)).symm
  apply le_of_tendsto_of_tendsto'
    (((htlim hfc hfp hfi).rpow_const (.inr ha)).mul ((htlim hgc hgp hgi).rpow_const (.inr hb)))
    (htlim hhc hhp hhi)
  intro k
  apply prekopaLeindler_gaussian_sharp_bounded ha hb hab (htc k hfc) (htc k hgc) (htc k hhc)
    (htb k hfp) (htb k hgp) (htb k hhp)
  intro x y
  have h1 (A A' B' B'' : ℝ) (hA : 0 < A) (hA' : A ≤ A') (hB' : 0 < B') (hB'' : B' ≤ B'') :
      A^a * B'^b ≤ A'^a * B''^b := by
    exact mul_le_mul (Real.rpow_le_rpow hA.le hA' ha) (Real.rpow_le_rpow hB'.le hB'' hb)
      (Real.rpow_nonneg hB'.le _) (Real.rpow_nonneg (hA.le.trans hA') _)
  by_cases hsmall : h (a • x + b • y) ≤ B k
  · rw [show truncate k h (a • x + b • y) = h (a • x + b • y) from min_eq_left hsmall]
    exact (h1 _ _ _ _ (htb k hfp x).1 (min_le_left _ _) (htb k hgp y).1
      (min_le_left _ _)).trans (hdom x y)
  · rw [show truncate k h (a • x + b • y) = B k from min_eq_right (le_of_not_ge hsmall)]
    calc
      _ ≤ (B k) ^ a * (B k) ^ b := h1 _ _ _ _ (htb k hfp x).1 (htb k hfp x).2
        (htb k hgp y).1 (htb k hgp y).2
      _ = B k := by rw [← Real.rpow_add (hB k), hab, Real.rpow_one]
      _ ≤ _ := le_mul_of_one_le_right (hB k).le (Real.one_le_exp (by positivity))

/-- The ordinary Gaussian Prékopa–Leindler inequality. -/
theorem prekopaLeindler_gaussian {n : ℕ} {f g h : (Fin n → ℝ) → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hfc : Continuous f) (hgc : Continuous g) (hhc : Continuous h)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (hhp : ∀ x, 0 < h x)
    (hfi : Integrable f (Measure.pi fun _ : Fin n => gaussianReal 0 1))
    (hgi : Integrable g (Measure.pi fun _ : Fin n => gaussianReal 0 1))
    (hhi : Integrable h (Measure.pi fun _ : Fin n => gaussianReal 0 1))
    (hdom : ∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y)) :
    let γ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
    (∫ x, f x ∂γ) ^ a * (∫ x, g x ∂γ) ^ b ≤ ∫ x, h x ∂γ := by
  apply prekopaLeindler_gaussian_sharp ha hb hab hfc hgc hhc hfp hgp hhp hfi hgi hhi
  intro x y
  exact (hdom x y).trans (le_mul_of_one_le_right (hhp _).le (Real.one_le_exp (by positivity)))

/-- The exponential of a Lipschitz potential is integrable under every shifted,
scaled finite-dimensional standard Gaussian. -/
theorem integrable_exp_neg_lipschitz_gaussian {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (x : Fin n → ℝ) (r : ℝ) :
    Integrable (fun z => Real.exp (-ψ (x + r • z))) (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  let c := |L| * |r|
  have hc0 : 0 ≤ c := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hi : Integrable (fun z : ℝ => Real.exp (c * |z|)) (gaussianReal 0 1) :=
    integrable_exp_mul_abs (integrable_exp_mul_gaussianReal c) (integrable_exp_mul_gaussianReal (-c))
  have hprod : Integrable (fun z : Fin n → ℝ => ∏ i, Real.exp (c * |z i|))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := Integrable.fintype_prod fun _ => hi
  apply (hprod.const_mul (Real.exp (-ψ x))).mono' (by fun_prop)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hzn : ‖z‖ ≤ ∑ i, |z i| := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact Finset.single_le_sum (f := fun i => |z i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h := hL (x+r•z) x
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
  have h' := (neg_le_abs (ψ (x+r•z) - ψ x)).trans h
  have h'' := mul_le_mul_of_nonneg_right (le_abs_self L) (mul_nonneg (abs_nonneg r) (norm_nonneg z))
  rw [← Finset.mul_sum]
  linarith [mul_le_mul_of_nonneg_left hzn hc0, show c * ‖z‖ = |L| * (|r| *‖z‖) by dsimp [c]; ring]

/-- Convolution of a log-concave Lipschitz-potential tilt with the finite-dimensional
Gaussian heat kernel is log-concave, for every scale including zero. -/
theorem concaveOn_log_gaussianHeat {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hconv : ConvexOn ℝ univ ψ) (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖)
    (r : ℝ) :
    ConcaveOn ℝ univ (fun x : Fin n → ℝ =>
      Real.log (∫ z, Real.exp (-ψ (x + r • z)) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))) := by
  let γ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let F := fun (x z : Fin n → ℝ) => Real.exp (-ψ (x + r • z))
  have hF (x) : Continuous (F x) := by dsimp [F]; fun_prop
  have hp (x z) : 0 < F x z := Real.exp_pos _
  have hi (x) : Integrable (F x) γ := integrable_exp_neg_lipschitz_gaussian hc hL x r
  have hpos (x) : 0 < ∫ z, F x z ∂γ := by
    apply (integral_pos_iff_support_of_nonneg (fun z => (hp x z).le) (hi x)).mpr
    rw [show Function.support (F x) = univ from eq_univ_of_forall fun z => (hp x z).ne',
      measure_univ]
    exact zero_lt_one
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have e (z w : Fin n → ℝ) :
      a • (x+r•z) + b • (y+r•w) = (a•x+b•y) + r • (a•z+b•w) := by module
  have hdom (z w) : F x z ^ a * F y w ^ b ≤ F (a•x+b•y) (a•z+b•w) := by
    dsimp [F]
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := hconv.2 (mem_univ (x+r•z)) (mem_univ (y+r•w)) ha hb hab
    rw [e] at hh
    simp only [smul_eq_mul] at hh
    linarith
  have hPL := prekopaLeindler_gaussian ha hb hab (hF x) (hF y) (hF _) (hp x) (hp y)
    (hp _) (hi x) (hi y) (hi _) hdom
  have hlog := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos (hpos x) a)
    (Real.rpow_pos_of_pos (hpos y) b)) hPL
  rw [Real.log_mul (Real.rpow_pos_of_pos (hpos x) a).ne' (Real.rpow_pos_of_pos (hpos y) b).ne',
    Real.log_rpow (hpos x), Real.log_rpow (hpos y)] at hlog
  exact hlog

/-- Gaussian smoothing preserves the Lipschitz constant of a log density. -/
theorem log_gaussianHeat_lipschitz {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (r : ℝ)
    (x y : Fin n → ℝ) :
    let H := fun w => ∫ z, Real.exp (-ψ (w+r•z)) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
    |Real.log (H x) - Real.log (H y)| ≤ L * ‖x-y‖ := by
  let γ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let H := fun w => ∫ z, Real.exp (-ψ (w+r•z)) ∂γ
  have hZ (w) : 0 < H w := integral_exp_pos (integrable_exp_neg_lipschitz_gaussian hc hL w r)
  have hdir (u v : Fin n → ℝ) : Real.log (H u) - Real.log (H v) ≤ L * ‖u-v‖ := by
    let K := L * ‖u-v‖
    have hdom (z : Fin n → ℝ) : Real.exp (-ψ (u+r•z)) ≤ Real.exp K * Real.exp (-ψ (v+r•z)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := (neg_le_abs (ψ (u+r•z) - ψ (v+r•z))).trans (hL (u+r•z) (v+r•z))
      rw [add_sub_add_right_eq_sub] at hh
      dsimp only [K]
      linarith
    have hh := integral_mono (integrable_exp_neg_lipschitz_gaussian hc hL u r)
      ((integrable_exp_neg_lipschitz_gaussian hc hL v r).const_mul (Real.exp K)) hdom
    rw [integral_const_mul] at hh
    have : Real.log (H u) ≤ Real.log (Real.exp K * H v) := Real.log_le_log (hZ u) hh
    rw [Real.log_mul (Real.exp_pos K).ne' (hZ v).ne', Real.log_exp] at this
    linarith
  apply abs_le.mpr
  have hrev := hdir y x
  rw [norm_sub_rev y x] at hrev
  exact ⟨by linarith, hdir x y⟩

end G54

end ModPrekopa

section ModHeatCov

/- # Covariance bounds from Gaussian partition functions -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace G54

/-- The second derivative of a cumulant bounded in curvature by a quadratic bounds the variance. -/
theorem variance_le_of_concave_cgf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : ℝ)
    (hI : ∀ t : ℝ, Integrable (fun y => Real.exp (t * X y)) μ)
    (h : ConcaveOn ℝ univ (fun t : ℝ => cgf X μ t - c * t ^ 2 / 2)) :
    variance X μ ≤ c := by
  have hset : integrableExpSet X μ = univ := eq_univ_of_forall hI
  have hint (t : ℝ) : t ∈ interior (integrableExpSet X μ) := by simp [hset]
  have ha (t : ℝ) := analyticAt_cgf (hint t)
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => c * u ^ 2 / 2) (c * t) t := by
    have hp := ((hasDerivAt_const t c).mul ((hasDerivAt_id t).pow 2)).div_const (2 : ℝ)
    convert hp using 1 <;> first | rfl | (simp [id]; ring)
  let f (t : ℝ) := cgf X μ t - c * t ^ 2 / 2
  have hdf (t : ℝ) : HasDerivAt f (deriv (cgf X μ) t - c * t) t :=
    (ha t).differentiableAt.hasDerivAt.sub (hd t)
  have hmono : Antitone (deriv f) :=
    antitoneOn_univ.mp (h.antitoneOn_deriv (fun t _ => (hdf t).differentiableAt))
  have hdd := hmono.deriv_nonpos (x := 0)
  have hder : deriv f = fun t => deriv (cgf X μ) t - c * t := funext (fun t => (hdf t).deriv)
  rw [hder, deriv_fun_sub (ha 0).deriv.differentiableAt (by fun_prop),
      deriv_const_mul _ differentiableAt_id, deriv_id''] at hdd
  have hv := iteratedDeriv_two_cgf_eq_integral (hint 0)
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_cgf_zero (hint 0)] at hv
  simp only [probReal_univ, div_one, zero_mul, Real.exp_zero, mul_one, mgf_zero] at hv
  rw [variance_eq_integral (aemeasurable_of_mem_interior_integrableExpSet (hint 0))]
  linarith

/-- Exponent of the unnormalised Gaussian likelihood with variance parameter `s`. -/
noncomputable def heatExponent {n : ℕ} (s : ℝ) (x y : Fin n → ℝ) : ℝ :=
  -(∑ i, (y i - x i)^2) / (2 * s)

/-- Gaussian partition function of a measure at a translated centre. -/
noncomputable def heatMass {n : ℕ} (ν : Measure (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, Real.exp (heatExponent s x y) ∂ν

/-- Completing the square shifts the Gaussian centre by `s t v`. -/
theorem heatExponent_shift {n : ℕ} {s : ℝ} (hs : 0 < s) (x y v : Fin n → ℝ) (t : ℝ) :
    heatExponent s x y + t * (∑ i, v i * (y i - x i)) =
      heatExponent s (x + (s * t) • v) y + (s * ∑ i, v i ^ 2) * t ^ 2 / 2 := by
  unfold heatExponent
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hs.ne']
  simp only [Finset.mul_sum]
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The moment generating function in a direction is a ratio of translated partition functions. -/
theorem heat_mgf {n : ℕ} (ν : Measure (Fin n → ℝ)) {s : ℝ} (hs : 0 < s)
    (x v : Fin n → ℝ) (t : ℝ) :
    mgf (fun y => ∑ i, v i * (y i - x i)) (ν.tilted (heatExponent s x)) t =
      (Real.exp ((s * ∑ i, v i ^ 2) * t ^ 2 / 2) / heatMass ν s x) *
        heatMass ν s (x + (s * t) • v) := by
  unfold mgf heatMass
  rw [integral_tilted, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [smul_eq_mul]
  rw [div_mul_eq_mul_div, ← Real.exp_add, heatExponent_shift hs, Real.exp_add]
  ring

/-- Every directional variance of the posterior is bounded by `s` times the squared
Euclidean length of the direction when its Gaussian partition function is log-concave. -/
theorem heat_variance_le {n : ℕ} (ν : Measure (Fin n → ℝ)) [NeZero ν]
    {s : ℝ} (hs : 0 < s) (hpos : ∀ z, 0 < heatMass ν s z)
    (hlog : ConcaveOn ℝ univ (fun z => Real.log (heatMass ν s z))) (x v : Fin n → ℝ) :
    variance (fun y => ∑ i, v i * (y i - x i)) (ν.tilted (heatExponent s x))
      ≤ s * ∑ i, v i ^ 2 := by
  have : IsProbabilityMeasure (ν.tilted (heatExponent s x)) :=
    isProbabilityMeasure_tilted (Integrable.of_integral_ne_zero (hpos x).ne')
  apply variance_le_of_concave_cgf
  · intro t
    apply mgf_pos_iff.mp
    rw [heat_mgf ν hs]
    exact mul_pos (div_pos (Real.exp_pos _) (hpos x)) (hpos _)
  · have hid (t : ℝ) :
        cgf (fun y => ∑ i, v i * (y i - x i)) (ν.tilted (heatExponent s x)) t -
          (s * ∑ i, v i ^ 2) * t ^ 2 / 2 =
        Real.log (heatMass ν s (x + (s * t) • v)) - Real.log (heatMass ν s x) := by
      rw [cgf, heat_mgf ν hs, Real.log_mul (div_pos (Real.exp_pos _) (hpos x)).ne' (hpos _).ne',
        Real.log_div (Real.exp_pos _).ne' (hpos x).ne', Real.log_exp]
      ring
    simp_rw [hid]
    constructor
    · exact convex_univ
    · intro t₁ _ t₂ _ a b ha hb hab
      have harg : x + (s * (a • t₁ + b • t₂)) • v =
          a • (x + (s * t₁) • v) + b • (x + (s * t₂) • v) := by
        ext i
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        linear_combination (-(x i)) * hab
      have hc := hlog.2 (mem_univ (x + (s * t₁) • v)) (mem_univ (x + (s * t₂) • v)) ha hb hab
      dsimp only at hc ⊢
      rw [harg]
      simp only [smul_eq_mul] at hc ⊢
      linarith only [hc, show (a + b) * Real.log (heatMass ν s x) = Real.log (heatMass ν s x) by rw [hab, one_mul]]

private theorem secondDeriv_nonpos_at_max {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hmax : ∀ t, f t ≤ f 0) : iteratedDeriv 2 f 0 ≤ 0 := by
  by_contra! hc
  have he := (hf.continuous_iteratedDeriv 2 (by norm_num)).continuousAt.eventually
    (lt_mem_nhds hc)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  set t := r / 2 with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have h₁ : deriv f 0 = 0 := IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall hmax)
  have hd : derivWithin f (Icc 0 t) 0 = 0 :=
    ((hf.differentiable (by norm_num) 0).derivWithin
      (uniqueDiffOn_Icc htpos 0 ⟨le_rfl, htpos.le⟩)).trans h₁
  obtain ⟨u, hu, hu'⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) htpos.ne hf.contDiffOn
  rw [uIoo_of_lt htpos] at hu
  have hp : 0 < iteratedDeriv 2 f u := hball (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hu.1]
    linarith [hu.2])
  simp [uIcc_of_lt htpos, hd, Nat.factorial] at hu'
  nlinarith [hmax t, mul_pos hp (sq_pos_of_pos htpos)]

/-- The symmetric moment-generating-function bound needed for the midpoint form of
Prékopa–Leindler implies a sharp variance bound. -/
theorem variance_le_of_mgf_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : ℝ)
    (hI : ∀ t : ℝ, Integrable (fun y => Real.exp (t * X y)) μ)
    (h : ∀ t, mgf X μ t * mgf X μ (-t) ≤ Real.exp (c * t ^ 2)) :
    variance X μ ≤ c := by
  have hset : integrableExpSet X μ = univ := eq_univ_of_forall hI
  have hint (t : ℝ) : t ∈ interior (integrableExpSet X μ) := by simp [hset]
  have ha : ContDiff ℝ 2 (cgf X μ) := by
    rw [contDiff_iff_contDiffAt]
    exact fun t => (analyticAt_cgf (hint t)).contDiffAt
  have hn : ContDiff ℝ 2 (fun t : ℝ => cgf X μ (-t)) := ha.comp contDiff_neg
  have hq : ContDiff ℝ 2 (fun t : ℝ => c * t^2) := by fun_prop
  have hmax (t : ℝ) : cgf X μ t + cgf X μ (-t) - c * t ^ 2 ≤
      cgf X μ 0 + cgf X μ (-0) - c * 0 ^ 2 := by
    have hl := Real.log_le_log (mul_pos (mgf_pos (hI t)) (mgf_pos (hI (-t)))) (h t)
    rw [Real.log_mul (mgf_pos (hI t)).ne' (mgf_pos (hI (-t))).ne', Real.log_exp] at hl
    simpa [cgf] using sub_nonpos.mpr hl
  have h₂ := secondDeriv_nonpos_at_max ((ha.add hn).sub hq) hmax
  rw [iteratedDeriv_fun_sub (ha.add hn).contDiffAt hq.contDiffAt,
    iteratedDeriv_fun_add ha.contDiffAt hn.contDiffAt, iteratedDeriv_comp_neg,
    iteratedDeriv_const_mul c (by fun_prop), iteratedDeriv_pow] at h₂
  have hv := iteratedDeriv_two_cgf_eq_integral (hint 0)
  rw [deriv_cgf_zero (hint 0)] at hv
  simp only [probReal_univ, div_one, zero_mul, Real.exp_zero, mul_one, mgf_zero] at hv
  rw [variance_eq_integral (aemeasurable_of_mem_interior_integrableExpSet (hint 0))]
  norm_num [Nat.descFactorial] at h₂
  linarith

/-- The sharpened Gaussian midpoint inequality includes the quadratic Gaussian density factor. -/
def SharpGaussianMidpoint (n : ℕ) (μ : Measure (Fin n → ℝ)) : Prop :=
  ∀ (f g h : (Fin n → ℝ) → ℝ), Continuous f → Continuous g → Continuous h →
    (∀ x, 0 < f x) → (∀ x, 0 < g x) → (∀ x, 0 < h x) →
    Integrable f μ → Integrable g μ → Integrable h μ →
    (∀ x y, f x ^ (1 / 2 : ℝ) * g y ^ (1 / 2 : ℝ) ≤
      h ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) *
        Real.exp ((∑ i, (x i - y i)^2) / 8)) →
    (∫ x, f x ∂μ) ^ (1 / 2 : ℝ) * (∫ x, g x ∂μ) ^ (1 / 2 : ℝ) ≤ ∫ x, h x ∂μ

/-- The Gaussian product law satisfies the sharp midpoint inequality in every dimension. -/
theorem sharpGaussianMidpoint (n : ℕ) :
    SharpGaussianMidpoint n (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  intro f g h hfc hgc hhc hfp hgp hhp hfi hgi hhi hdom
  apply prekopaLeindler_gaussian_sharp (by norm_num) (by norm_num) (by norm_num)
    hfc hgc hhc hfp hgp hhp hfi hgi hhi
  intro x y
  convert hdom x y using 2
  ring_nf

theorem mgf_tilted_ratio {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A X : Ω → ℝ) (t : ℝ) :
    mgf X (μ.tilted A) t = (∫ y, Real.exp (A y + t * X y) ∂μ) / ∫ y, Real.exp (A y) ∂μ := by
  unfold mgf
  rw [integral_tilted, ← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by simp only [smul_eq_mul, Real.exp_add]; ring

/-- A Lipschitz observable of a log-concave tilt of the Gaussian satisfies a symmetric
MGF bound. This uses Prékopa–Leindler only at its midpoint. -/
theorem tilted_lipschitz_mgf_mul {n : ℕ} (μ : Measure (Fin n → ℝ)) [NeZero μ]
    (hPL : SharpGaussianMidpoint n μ) (A X : (Fin n → ℝ) → ℝ) (L : ℝ)
    (hA : Continuous A) (hAc : ConcaveOn ℝ univ A) (hX : Continuous X)
    (hLip : ∀ z w, |X z - X w| ≤ L * Real.sqrt (∑ i, (z i - w i)^2))
    (hI : ∀ t : ℝ, Integrable (fun z => Real.exp (A z + t * X z)) μ) (t : ℝ) :
    mgf X (μ.tilted A) t * mgf X (μ.tilted A) (-t) ≤ Real.exp (L^2 * t^2) := by
  let f (u : ℝ) (z : Fin n → ℝ) := Real.exp (A z + u * X z)
  let C := (L^2 * t^2) / 2
  have hf (u : ℝ) : Continuous (f u) := (hA.add (continuous_const.mul hX)).rexp
  have hi : Integrable (fun z => Real.exp (A z)) μ := by simpa using (hI 0)
  have hZ := integral_exp_pos hi
  let h := fun z => Real.exp C * Real.exp (A z)
  have hh : Continuous h := continuous_const.mul hA.rexp
  have hpos (z : Fin n → ℝ) : 0 < h z := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hdom (z w : Fin n → ℝ) :
      f t z ^ (1 / 2 : ℝ) * f (-t) w ^ (1 / 2 : ℝ) ≤
      h ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w) * Real.exp ((∑ i, (z i - w i)^2) / 8) := by
    have hj := hAc.2 (mem_univ z) (mem_univ w) (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hj
    let d := Real.sqrt (∑ i, (z i - w i)^2)
    have hd : d^2 = ∑ i, (z i - w i)^2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have htx : t * (X z - X w) ≤ |t| * (L * d) :=
      (le_abs_self _).trans ((abs_mul _ _).le.trans <|
        mul_le_mul_of_nonneg_left (hLip z w) (abs_nonneg _))
    have hcost : |t| * (L * d) / 2 ≤ C + (∑ i, (z i - w i)^2) / 8 := by
      dsimp only [C]
      rw [← hd, ← sq_abs t]
      nlinarith [sq_nonneg (d - 2 * |t| * L)]
    unfold f h
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      Real.exp_le_exp]
    linarith
  have hpl := hPL (f t) (f (-t)) h (hf _) (hf _) hh (fun _ => Real.exp_pos _)
    (fun _ => Real.exp_pos _) hpos (hI _) (hI _) (hi.const_mul _) hdom
  simp only [← Real.sqrt_eq_rpow, h, integral_const_mul] at hpl
  have hp : 0 ≤ Real.sqrt (∫ y, f t y ∂μ) * Real.sqrt (∫ y, f (-t) y ∂μ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs := pow_le_pow_left₀ hp hpl 2
  rw [mul_pow, Real.sq_sqrt (integral_exp_pos (hI t)).le,
    Real.sq_sqrt (integral_exp_pos (hI (-t))).le, mul_pow, sq (Real.exp C),
    ← Real.exp_add, show C + C = L ^ 2 * t ^ 2 by unfold C; ring] at hs
  rw [mgf_tilted_ratio, mgf_tilted_ratio, div_mul_div_comm, div_le_iff₀ (mul_pos hZ hZ)]
  simpa [pow_two, f] using hs

/-- The sharp directional Poincaré constant for a Lipschitz observable of a log-concave
tilt, assuming the midpoint Prékopa–Leindler inequality for the reference law. -/
theorem tilted_lipschitz_variance {n : ℕ} (μ : Measure (Fin n → ℝ)) [NeZero μ]
    (hPL : SharpGaussianMidpoint n μ) (A X : (Fin n → ℝ) → ℝ) (L : ℝ)
    (hA : Continuous A) (hAc : ConcaveOn ℝ univ A) (hX : Continuous X)
    (hLip : ∀ z w, |X z - X w| ≤ L * Real.sqrt (∑ i, (z i - w i)^2))
    (hI : ∀ t : ℝ, Integrable (fun z => Real.exp (A z + t * X z)) μ) :
    variance X (μ.tilted A) ≤ L^2 := by
  have hi : Integrable (fun z => Real.exp (A z)) μ := by simpa using (hI 0)
  have : IsProbabilityMeasure (μ.tilted A) := isProbabilityMeasure_tilted hi
  apply variance_le_of_mgf_mul
  · intro t
    apply mgf_pos_iff.mp
    rw [mgf_tilted_ratio]
    exact div_pos (integral_exp_pos (hI t)) (integral_exp_pos hi)
  · exact tilted_lipschitz_mgf_mul μ hPL A X L hA hAc hX hLip hI

/-- A symmetric MGF bound gives uniform control of the third absolute
centered moment at its natural scale. -/
theorem abs_third_central_moment_le_of_mgf_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) {L : ℝ} (hL : 0 < L)
    (hI : ∀ t : ℝ, Integrable (fun y => Real.exp (t * X y)) μ)
    (hM : ∀ t, mgf X μ t * mgf X μ (-t) ≤ Real.exp (L^2 * t^2)) :
    (∫ y, |X y - ∫ z, X z ∂μ|^3 ∂μ) ≤ 12 * Real.exp 1 * L^3 := by
  let m := ∫ z, X z ∂μ
  let Y := fun y => X y - m
  have hset : integrableExpSet X μ = univ := eq_univ_of_forall hI
  have hXi := integrable_of_mem_interior_integrableExpSet (X := X) (μ := μ)
    (by simp [hset])
  have hshift (u : ℝ) : mgf Y μ u = mgf X μ u * Real.exp (-u * m) := by
    simp only [Y, sub_eq_add_neg, mgf_add_const, mul_neg, neg_mul]
  have hYi (u : ℝ) : Integrable (fun z => Real.exp (u * Y z)) μ := by
    apply mgf_pos_iff.mp
    rw [hshift]
    exact mul_pos (mgf_pos (hI u)) (Real.exp_pos _)
  have hYset : integrableExpSet Y μ = univ := eq_univ_of_forall hYi
  have hY3 := integrable_pow_abs_of_mem_interior_integrableExpSet (X := Y) (μ := μ)
    (by simp [hYset]) 3
  have hbound (u : ℝ) : mgf Y μ u ≤ Real.exp (L^2 * u^2) := by
    have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all μ fun z => mem_univ (-u * X z)) (hXi.const_mul (-u)) (hI (-u))
    rw [integral_const_mul] at hj
    rw [hshift]
    exact (mul_le_mul_of_nonneg_left hj mgf_nonneg).trans (hM u)
  let q := L⁻¹
  have hq : 0 < q := inv_pos.mpr hL
  have hqn : L^2 * (-q)^2 = 1 := by dsimp [q]; field_simp
  have hqp : L^2 * q^2 = 1 := by simpa using hqn
  have hpt (z : Ω) : q ^ 3 * |Y z|^3 ≤
      6 * (Real.exp (q * Y z) + Real.exp (-q * Y z)) := by
    have he := Real.pow_div_factorial_le_exp |q * Y z| (abs_nonneg (q * Y z)) 3
    have hsum : Real.exp |q * Y z| ≤ Real.exp (q * Y z) + Real.exp (-q * Y z) := by
      rcases le_total 0 (q * Y z) with hp | hn
      · rw [abs_of_nonneg hp]
        linarith [Real.exp_pos (-q * Y z)]
      · rw [abs_of_nonpos hn, neg_mul]
        linarith [Real.exp_pos (q * Y z)]
    rw [abs_mul, abs_of_pos hq, mul_pow] at he
    rw [abs_mul, abs_of_pos hq] at hsum
    norm_num at he
    linarith
  have hn := integral_mono (hY3.const_mul (q^3)) (((hYi q).add (hYi (-q))).const_mul 6) hpt
  simp only [integral_const_mul, Pi.add_apply, integral_add (hYi q) (hYi (-q))] at hn
  change q ^ 3 * (∫ z, |Y z| ^ 3 ∂μ) ≤ 6 * (mgf Y μ q + mgf Y μ (-q)) at hn
  have hp := hbound q
  have hm := hbound (-q)
  rw [hqn] at hm
  rw [hqp] at hp
  have he : q^3 * (∫ z, |Y z|^3 ∂μ) ≤ 12 * Real.exp 1 := by linarith
  rw [show q ^ 3 = (L ^ 3)⁻¹ by simp [q], inv_mul_le_iff₀ (pow_pos hL 3)] at he
  exact he.trans_eq (mul_comm _ _)

theorem euclidean_lipschitz_to_sup {n : ℕ} {X : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hX : ∀ z w, |X z - X w| ≤ L * Real.sqrt (∑ i, (z i - w i)^2))
    (z w : Fin n → ℝ) : |X z - X w| ≤ L * n * ‖z - w‖ := by
    apply (hX z w).trans
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hL
    have hs : Real.sqrt (∑ i, (z i - w i)^2) ≤ ∑ i, |z i - w i| := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
      simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (f := fun i => |z i - w i|) (fun i _ => abs_nonneg _)
    apply hs.trans
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Fintype.card_fin, nsmul_eq_mul] using
      Pi.sum_norm_apply_le_norm (z - w)

theorem continuous_of_sup_lipschitz {n : ℕ} {f : (Fin n → ℝ) → ℝ} {B : ℝ}
      (hf : ∀ z w, |f z - f w| ≤ B * ‖z - w‖) : Continuous f := by
    apply (LipschitzWith.of_dist_le_mul (K := Real.toNNReal B) _).continuous
    intro z w
    simpa only [dist_eq_norm, Real.norm_eq_abs] using
      (hf z w).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))

/-- Sharp variance and third centered moment bounds for a Lipschitz observable under
a log-concave tilt of a standard Gaussian product. The potential `A` is the log density. -/
theorem gaussian_tilt_lipschitz_moments_memLp {n : ℕ} (A X : (Fin n → ℝ) → ℝ)
    {K L : ℝ} (hL : 0 ≤ L) (hAc : ConcaveOn ℝ univ A)
    (hA : ∀ z w, |A z - A w| ≤ K * ‖z - w‖)
    (hX : ∀ z w, |X z - X w| ≤ L * Real.sqrt (∑ i, (z i - w i)^2)) :
    let μ := (Measure.pi fun _ : Fin n => gaussianReal 0 1).tilted A
    (∀ p : ℝ≥0, MemLp X p μ) ∧
    variance X μ ≤ L^2 ∧ (∫ z, |X z - ∫ w, X w ∂μ|^3 ∂μ) ≤ 12 * Real.exp 1 * L^3 := by
  let γ := Measure.pi fun _ : Fin n => gaussianReal 0 1
  have hXsup := euclidean_lipschitz_to_sup hL hX
  have hI (t : ℝ) : Integrable (fun z => Real.exp (A z + t * X z)) γ := by
    let ψ := fun z => -(A z + t * X z)
    have hψ : Continuous ψ := ((continuous_of_sup_lipschitz hA).add (continuous_const.mul (continuous_of_sup_lipschitz hXsup))).neg
    have hLip (z w) : |ψ z - ψ w| ≤ (K + |t| * (L * n)) * ‖z - w‖ := by
      have he : ψ z - ψ w = -((A z - A w) + t * (X z - X w)) := by unfold ψ; ring
      rw [he, abs_neg, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hA z w) (by
        rw [abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hXsup z w) (abs_nonneg _)))
    simpa [γ, ψ] using integrable_exp_neg_lipschitz_gaussian hψ hLip 0 1
  have hi : Integrable (fun z => Real.exp (A z)) γ := by simpa using hI 0
  have : IsProbabilityMeasure (γ.tilted A) := isProbabilityMeasure_tilted hi
  have hMG := tilted_lipschitz_mgf_mul γ (sharpGaussianMidpoint n) A X L (continuous_of_sup_lipschitz hA) hAc
    (continuous_of_sup_lipschitz hXsup) hX hI
  have hIX (t : ℝ) : Integrable (fun z => Real.exp (t * X z)) (γ.tilted A) := by
    apply mgf_pos_iff.mp
    rw [mgf_tilted_ratio]
    exact div_pos (integral_exp_pos (hI t)) (integral_exp_pos hi)
  have hexps : integrableExpSet X (γ.tilted A) = univ := eq_univ_of_forall hIX
  refine ⟨memLp_of_mem_interior_integrableExpSet (X := X) (μ := γ.tilted A) (by simp [hexps]),
    variance_le_of_mgf_mul _ _ _ hIX hMG, ?_⟩
  rcases hL.eq_or_lt with h0 | hpos
  · subst L
    have he : X = fun _ => X 0 := funext fun z => sub_eq_zero.mp
      (abs_nonpos_iff.mp (by simpa using hX z 0))
    change (∫ z, |X z - ∫ w, X w ∂(γ.tilted A)|^3 ∂(γ.tilted A)) ≤ _
    rw [he]
    simp
  · exact abs_third_central_moment_le_of_mgf_mul _ _ hpos hIX hMG

theorem gaussian_tilt_lipschitz_moments {n : ℕ} (A X : (Fin n → ℝ) → ℝ)
    {K L : ℝ} (hL : 0 ≤ L) (hAc : ConcaveOn ℝ univ A)
    (hA : ∀ z w, |A z - A w| ≤ K * ‖z - w‖)
    (hX : ∀ z w, |X z - X w| ≤ L * Real.sqrt (∑ i, (z i - w i)^2)) :
    let μ := (Measure.pi fun _ : Fin n => gaussianReal 0 1).tilted A
    variance X μ ≤ L^2 ∧ (∫ z, |X z - ∫ w, X w ∂μ|^3 ∂μ) ≤ 12 * Real.exp 1 * L^3 :=
  (gaussian_tilt_lipschitz_moments_memLp A X hL hAc hA hX).2

end G54

end ModHeatCov

section ModHeatMean

/- # Lipschitz continuity of the Gaussian posterior mean -/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace G54

/-- Barycentre of the posterior with Gaussian likelihood centred at `x`. -/
noncomputable def heatMean {n : ℕ} (ν : Measure (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∫ y, y i ∂(ν.tilted (heatExponent s x))

private theorem heat_expSet {n : ℕ} (ν : Measure (Fin n → ℝ)) [NeZero ν]
    {s : ℝ} (hs : 0 < s) (hp : ∀ z, 0 < heatMass ν s z) (x v : Fin n → ℝ) :
    integrableExpSet (fun y => ∑ i, v i * (y i - x i)) (ν.tilted (heatExponent s x)) = univ := by
  let := isProbabilityMeasure_tilted (μ := ν) (f := heatExponent s x)
    (by by_contra h; exact (hp x).ne' (integral_undef h))
  apply eq_univ_of_forall
  intro t
  apply mgf_pos_iff.mp
  rw [heat_mgf ν hs]
  exact mul_pos (div_pos (Real.exp_pos _) (hp _)) (hp _)

theorem heat_integrable_coord {n : ℕ} (ν : Measure (Fin n → ℝ)) [NeZero ν] {s : ℝ}
    (hs : 0 < s) (hp : ∀ z, 0 < heatMass ν s z) (x : Fin n → ℝ) (i : Fin n) :
    Integrable (fun y => y i) (ν.tilted (heatExponent s x)) := by
  let := isProbabilityMeasure_tilted (μ := ν) (f := heatExponent s x)
    (by by_contra h; exact (hp x).ne' (integral_undef h))
  have h := heat_expSet ν hs hp x (Pi.single i 1)
  have h' : Integrable (fun y : Fin n → ℝ => y i - x i) (ν.tilted (heatExponent s x)) := by
    have hc := integrable_of_mem_interior_integrableExpSet (by rw [h]; simp :
      0 ∈ interior (integrableExpSet (fun y => ∑ j, (Pi.single i 1 : Fin n → ℝ) j * (y j - x j))
          (ν.tilted (heatExponent s x))))
    simpa [Pi.single_apply] using hc
  exact (show Integrable (fun y : Fin n → ℝ => (y i - x i) + x i) _ from h'.add (integrable_const (x i))).congr
    (ae_of_all _ fun _ => sub_add_cancel _ _)

/-- The mean is the gradient of `s * log Z + |x|²/2` in the supporting-plane sense.
The difference from that plane is bounded by the Gaussian quadratic cost. -/
theorem heatMean_support {n : ℕ} (ν : Measure (Fin n → ℝ)) [NeZero ν] {s : ℝ}
    (hs : 0 < s) (hp : ∀ z, 0 < heatMass ν s z)
    (hlog : ConcaveOn ℝ univ (fun z => Real.log (heatMass ν s z))) (x y : Fin n → ℝ) :
    let A := fun z : Fin n → ℝ => s * Real.log (heatMass ν s z) + (∑ i, z i ^ 2) / 2
    let d := A y - A x - ∑ i, heatMean ν s x i * (y i - x i)
    0 ≤ d ∧ d ≤ (∑ i, (y i - x i)^2) / 2 := by
  let P := ν.tilted (heatExponent s x)
  let : IsProbabilityMeasure P := isProbabilityMeasure_tilted
    (by by_contra h; exact (hp x).ne' (integral_undef h))
  let v := s⁻¹ • (y - x)
  let U := fun z : Fin n → ℝ => ∑ i, v i * (z i - x i)
  let Q := (s * ∑ i, v i ^ 2) / 2
  have hmem : ∀ t, t ∈ interior (integrableExpSet U P) := by
    intro t; rw [heat_expSet ν hs hp]; simp
  have hUI : Integrable U P := integrable_of_mem_interior_integrableExpSet (hmem 0)
  have hUexp : Integrable (fun z => Real.exp (U z)) P := by
    simpa using (show Integrable (fun z => Real.exp (1 * U z)) P from interior_subset (s := integrableExpSet U P) (hmem 1))
  have hlow : (∫ z, U z ∂P) ≤ cgf U P 1 := by
    have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
        (ae_of_all P (fun z => mem_univ (U z))) hUI hUexp
    apply Real.exp_le_exp.mp
    simpa [cgf, mgf, Real.exp_log (integral_exp_pos hUexp)] using h
  let line := fun t : ℝ => x + (s * t) • v
  have hid (t : ℝ) : cgf U P t - Q * t ^ 2 =
      Real.log (heatMass ν s (line t)) - Real.log (heatMass ν s x) := by
    rw [cgf, heat_mgf ν hs, Real.log_mul (div_pos (Real.exp_pos _) (hp x)).ne' (hp _).ne',
      Real.log_div (Real.exp_pos _).ne' (hp x).ne', Real.log_exp]
    dsimp [line, Q]; ring
  have hconc : ConcaveOn ℝ univ (fun t : ℝ => cgf U P t - Q * t ^ 2) := by
    simp_rw [hid]
    refine ⟨convex_univ, ?_⟩
    intro t _ u _ a b ha hb hab
    have e : line (a • t + b • u) = a • line t + b • line u := by
      ext i; simp only [line, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination -(x i) * hab
    have H := hlog.2 (mem_univ (line t)) (mem_univ (line u)) ha hb hab
    dsimp only at H ⊢; rw [e]; simp only [smul_eq_mul] at H ⊢
    linarith only [H, show (a+b)*Real.log (heatMass ν s x) = Real.log (heatMass ν s x) by rw [hab, one_mul]]
  have hd : HasDerivAt (fun t : ℝ => cgf U P t - Q * t ^ 2) (∫ z, U z ∂P) 0 := by
    convert ((analyticAt_cgf (hmem 0)).differentiableAt.hasDerivAt.sub
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul Q)) using 1
    all_goals first | rfl | simp [deriv_cgf_zero (hmem 0)]
  have hu := hconc.slope_le_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hd
  simp [slope_def_field] at hu
  have hline : line 1 = y := by simp [line, v, smul_smul, hs.ne']
  have h1 := hid 1; rw [hline] at h1; simp only [one_pow, mul_one] at h1
  have hcoord i : Integrable (fun z : Fin n → ℝ => z i) P := heat_integrable_coord ν hs hp x i
  have hm : s * (∫ z, U z ∂P) = ∑ i, (y i - x i) * (heatMean ν s x i - x i) := by
    have hi (i) : Integrable (fun z : Fin n → ℝ => v i * (z i - x i)) P := ((hcoord i).sub (integrable_const _)).const_mul _
    dsimp only [U]; rw [integral_finsetSum _ fun i _ => hi i, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [integral_const_mul, integral_sub (hcoord i) (integrable_const _), integral_const]
    simp [v, heatMean, P, ← mul_assoc, hs.ne']
  have hQ : s * Q = (∑ i, (y i - x i)^2) / 2 := by
    dsimp [Q, v]; simp only [mul_pow, ← Finset.mul_sum]
    field_simp
  have hdot : (∑ i, heatMean ν s x i * (y i - x i)) =
      (∑ i, (y i - x i) * (heatMean ν s x i - x i)) + ∑ i, x i * (y i - x i) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  have hnorm : (∑ i, y i ^ 2) - (∑ i, x i ^ 2) - (∑ i, (y i - x i)^2) =
      2 * ∑ i, x i * (y i-x i) := by
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  dsimp only
  constructor <;> nlinarith only [mul_le_mul_of_nonneg_left hlow hs.le,
    mul_le_mul_of_nonneg_left hu hs.le, congrArg (s * ·) h1, hm, hQ, hdot, hnorm]

/-- A Gaussian posterior with log-concave heat mass has a nonexpansive mean map. -/
theorem heatMean_nonexpansive {n : ℕ} (ν : Measure (Fin n → ℝ)) [NeZero ν] {s : ℝ}
    (hs : 0 < s) (hp : ∀ z, 0 < heatMass ν s z)
    (hlog : ConcaveOn ℝ univ (fun z => Real.log (heatMass ν s z))) (x y : Fin n → ℝ) :
    ∑ i, (heatMean ν s x i - heatMean ν s y i)^2 ≤ ∑ i, (x i - y i)^2 := by
  let M := heatMean ν s
  let A := fun z : Fin n → ℝ => s * Real.log (heatMass ν s z) + (∑ i, z i ^ 2)/2
  have h (x y : Fin n → ℝ) : ∑ i, (M x i - M y i)^2 ≤
      2 * (A x - A y - ∑ i, M y i * (x i - y i)) := by
    let z := x + (M y - M x)
    have h1 : 0 ≤ A z - A y - ∑ i, M y i * (z i - y i) := (heatMean_support ν hs hp hlog y z).1
    have h2 : A z - A x - ∑ i, M x i * (z i - x i) ≤ (∑ i, (z i - x i)^2)/2 :=
      (heatMean_support ν hs hp hlog x z).2
    have e : (∑ i, M y i * (z i - y i)) - (∑ i, M x i * (z i - x i))
        - (∑ i, M y i * (x i - y i)) = ∑ i, (M x i - M y i)^2 := by
      simp only [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
      dsimp [z]; ring
    have ez : (∑ i, (z i - x i)^2) = ∑ i, (M x i - M y i)^2 := by
      apply Finset.sum_congr rfl; intro i _; dsimp [z]; ring
    linarith only [h1, h2, e, ez]
  have he : (∑ i, (M y i - M x i)^2) = ∑ i, (M x i - M y i)^2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have hcross : 2 * (-(∑ i, M y i * (x i - y i)) - (∑ i, M x i * (y i - x i))) ≤
      (∑ i, (M x i - M y i)^2) + ∑ i, (x i - y i)^2 := by
    simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    nlinarith only [sq_nonneg ((M x i - M y i) - (x i - y i))]
  change (∑ i, (M x i - M y i)^2) ≤ _
  linarith only [h x y, h y x, he, hcross]

end G54

end ModHeatMean

section ModHeatKernel

/- # Finite Gaussian transitions and their Doob transforms -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace G54

/-- Product Gaussian increments in the coordinates used by Green 54. -/
noncomputable def gaussianIncrements (n : ℕ) (s : ℝ≥0) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 s

instance (n : ℕ) (s : ℝ≥0) : IsProbabilityMeasure (gaussianIncrements n s) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

theorem gaussianIncrements_add (n : ℕ) (s t : ℝ≥0) :
    ((gaussianIncrements n s).prod (gaussianIncrements n t)).map
      (fun q => q.1 + q.2) = gaussianIncrements n (s+t) := by
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => gaussianReal 0 s) (fun _ => gaussianReal 0 t)
  have h : MeasurePreserving (fun p : ℝ × ℝ => p.1 + p.2)
      ((gaussianReal 0 s).prod (gaussianReal 0 t)) (gaussianReal 0 (s+t)) := by
    refine ⟨measurable_fst.add measurable_snd, ?_⟩
    simpa only [Measure.conv, zero_add] using gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0) (v₁ := s) (v₂ := t)
  have hh := measurePreserving_pi (ι := Fin n) _ _ (fun _ => h)
  exact (hh.comp (he.symm)).map_eq

/-- Gaussian translation kernel, also defined when the variance vanishes. -/
noncomputable def heatStep (n : ℕ) (s : ℝ≥0) : Kernel (Fin n → ℝ) (Fin n → ℝ) :=
  (Kernel.id ×ₖ Kernel.const _ (gaussianIncrements n s)).map (fun q => q.1 + q.2)

theorem heatStep_apply (n : ℕ) (s : ℝ≥0) (x : Fin n → ℝ) :
    heatStep n s x = (gaussianIncrements n s).map (fun z => x + z) := by
  have ha : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 + q.2) := measurable_fst.add measurable_snd
  rw [heatStep, Kernel.map_apply _ ha, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod, Measure.map_map
      ha (measurable_prodMk_left)]
  rfl

instance (n : ℕ) (s : ℝ≥0) : IsMarkovKernel (heatStep n s) where
  isProbabilityMeasure x := by rw [heatStep_apply]; exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem heatStep_add (n : ℕ) (s t : ℝ≥0) : heatStep n t ∘ₖ heatStep n s = heatStep n (s+t) := by
  ext x B hB
  have ha : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 + q.2) := measurable_fst.add measurable_snd
  have hx : Measurable (fun z : Fin n → ℝ => x + z) := measurable_const.add measurable_id
  rw [Kernel.comp_apply' _ _ _ hB, heatStep_apply, heatStep_apply,
      ← gaussianIncrements_add n s t, Measure.map_map hx ha]
  rw [Measure.map_apply (hx.comp ha) hB,
    Measure.prod_apply ((hx.comp ha) hB)]
  rw [lintegral_map ((heatStep n t).measurable_coe hB) hx]
  apply lintegral_congr
  intro z
  rw [heatStep_apply, Measure.map_apply (show Measurable (fun u : Fin n → ℝ => x + z + u) from measurable_const.add measurable_id) hB]
  congr 1
  ext y
  simp [Function.comp_def, add_assoc]

/-- Reweight a transition by its destination and divide by its conditional mass. -/
noncomputable def doobStep {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (K : Kernel E F) [IsSFiniteKernel K] (w : F → ℝ≥0∞) : Kernel E F :=
  K.withDensity (fun x y => (∫⁻ z, w z ∂K x)⁻¹ * w y)

theorem doobStep_apply {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (K : Kernel E F) [IsSFiniteKernel K] {w : F → ℝ≥0∞} (hw : Measurable w) (x : E) :
    doobStep K w x = (∫⁻ z, w z ∂K x)⁻¹ • (K x).withDensity w := by
  rw [doobStep, Kernel.withDensity_apply _ (show Measurable
    (fun q : E × F => (∫⁻ z, w z ∂K q.1)⁻¹ * w q.2) from
    (hw.lintegral_kernel.comp measurable_fst).inv.mul (hw.comp measurable_snd))]
  ext B hB
  rw [withDensity_apply _ hB, Measure.smul_apply, withDensity_apply _ hB, smul_eq_mul, lintegral_const_mul _ hw]

theorem doobStep_markov {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (K : Kernel E F) [IsSFiniteKernel K] {w : F → ℝ≥0∞} (hw : Measurable w)
    (hz : ∀ x, (∫⁻ z, w z ∂K x) ≠ 0) (hf : ∀ x, (∫⁻ z, w z ∂K x) ≠ ∞) :
    IsMarkovKernel (doobStep K w) where
  isProbabilityMeasure x := ⟨by rw [doobStep_apply K hw, Measure.smul_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel (hz x) (hf x)]⟩

/-- Weighting the starting law by the conditional mass telescopes against the Doob
normalization, so the output is precisely the original endpoint law weighted by `w`. -/
theorem doobStep_propagate {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (K : Kernel E F) [IsSFiniteKernel K] {w : F → ℝ≥0∞} (hw : Measurable w)
    (hz : ∀ x, (∫⁻ z, w z ∂K x) ≠ 0) (hf : ∀ x, (∫⁻ z, w z ∂K x) ≠ ∞) :
    doobStep K w ∘ₘ μ.withDensity (fun x => ∫⁻ z, w z ∂K x) = (K ∘ₘ μ).withDensity w := by
  ext B hB
  rw [Measure.bind_apply hB (doobStep K w).aemeasurable, lintegral_withDensity_eq_lintegral_mul _
    hw.lintegral_kernel ((doobStep K w).measurable_coe hB), withDensity_apply _ hB,
    ← lintegral_indicator hB, Measure.lintegral_bind K.aemeasurable (hw.indicator hB).aemeasurable]
  apply lintegral_congr
  intro x
  dsimp only [Pi.mul_apply]
  rw [doobStep_apply K hw, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (hz x) (hf x), one_mul, withDensity_apply _ hB, lintegral_indicator hB]

/-- Gaussian expectation of an unnormalized terminal weight. -/
noncomputable def heatWeight {n : ℕ} (w : (Fin n → ℝ) → ℝ≥0∞) (s : ℝ≥0) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, w y ∂heatStep n s x

theorem heatWeight_add {n : ℕ} {w : (Fin n → ℝ) → ℝ≥0∞} (hw : Measurable w)
    (s t : ℝ≥0) (x : Fin n → ℝ) :
    heatWeight (heatWeight w t) s x = heatWeight w (s+t) x := by
  unfold heatWeight
  rw [← heatStep_add, Kernel.lintegral_comp _ _ _ hw]

theorem gaussianIncrements_scale (n : ℕ) (s : ℝ≥0) :
    (gaussianIncrements n 1).map (fun z => Real.sqrt (s : ℝ) • z) = gaussianIncrements n s := by
  have h : MeasurePreserving (fun a : ℝ => Real.sqrt (s : ℝ) * a)
      (gaussianReal 0 1) (gaussianReal 0 s) := by
    constructor
    · fun_prop
    · rw [gaussianReal_map_const_mul]
      simp only [mul_zero, mul_one]
      congr 1; exact Subtype.ext (Real.sq_sqrt s.2)
  exact (measurePreserving_pi (ι := Fin n) _ _ (fun _ => h)).map_eq

theorem heatStep_map_standard (n : ℕ) (s : ℝ≥0) (x : Fin n → ℝ) :
    (gaussianIncrements n 1).map (fun z => x + Real.sqrt (s : ℝ) • z) = heatStep n s x := by
  rw [heatStep_apply, ← gaussianIncrements_scale n s, Measure.map_map
      (show Measurable (fun z : Fin n → ℝ => x + z) by fun_prop)
      (show Measurable (fun z : Fin n → ℝ => Real.sqrt (s : ℝ) • z) by fun_prop)]
  rfl

theorem heatStep_zero (n : ℕ) (x : Fin n → ℝ) : heatStep n 0 x = Measure.dirac x := by
  rw [← heatStep_map_standard]
  simp

/-- Conditional law of the endpoint with a given remaining time. -/
noncomputable def bridgeEndpoint {n : ℕ} (w : (Fin n → ℝ) → ℝ≥0∞) (s : ℝ≥0) :=
  doobStep (heatStep n s) w

/-- Advance by `s` when the endpoint will be observed `t` time units later. -/
noncomputable def bridgeStep {n : ℕ} (w : (Fin n → ℝ) → ℝ≥0∞) (s t : ℝ≥0) :=
  doobStep (heatStep n s) (heatWeight w t)

theorem bridgeEndpoint_zero {n : ℕ} {w : (Fin n → ℝ) → ℝ≥0∞}
    (hw : Measurable w) (hw0 : ∀ x, w x ≠ 0) (hwf : ∀ x, w x ≠ ∞) (x : Fin n → ℝ) :
    bridgeEndpoint w 0 x = Measure.dirac x := by
  rw [bridgeEndpoint, doobStep_apply _ hw, heatStep_zero, lintegral_dirac' _ hw,
    dirac_withDensity' hw, smul_smul, ENNReal.inv_mul_cancel (hw0 _) (hwf _), one_smul]

theorem bridgeEndpoint_comp {n : ℕ} {w : (Fin n → ℝ) → ℝ≥0∞} (hw : Measurable w)
    (s t : ℝ≥0) (hz : ∀ x, heatWeight w t x ≠ 0) (hf : ∀ x, heatWeight w t x ≠ ∞) :
    bridgeEndpoint w t ∘ₖ bridgeStep w s t = bridgeEndpoint w (s+t) := by
  have hmeas : Measurable (heatWeight w t) := hw.lintegral_kernel
  have h (x : Fin n → ℝ) :
      (bridgeEndpoint w t ∘ₖ bridgeStep w s t) x = bridgeEndpoint w (s+t) x := by
    change doobStep (heatStep n t) w ∘ₘ (doobStep (heatStep n s) (heatWeight w t) x) = _
    rw [doobStep_apply _ hmeas, Measure.comp_smul]
    have hd := doobStep_propagate (heatStep n s x) (heatStep n t) hw hz hf
    change _ ∘ₘ ((heatStep n s) x).withDensity (heatWeight w t) = _ at hd
    rw [hd]
    change (heatWeight (heatWeight w t) s x)⁻¹ •
      (((heatStep n t ∘ₖ heatStep n s) x).withDensity w) = _
    rw [heatWeight_add hw, heatStep_add, bridgeEndpoint, doobStep_apply _ hw]
    rfl
  ext a B _; rw [h]

/-- The endpoint mean evaluated at the next location has current expectation equal to
the endpoint mean evaluated at the current location. -/
theorem bridge_mean_tower {n : ℕ} {w : (Fin n → ℝ) → ℝ≥0∞} (hw : Measurable w)
    (s t : ℝ≥0) (hz : ∀ x, heatWeight w t x ≠ 0) (hf : ∀ x, heatWeight w t x ≠ ∞)
    (x : Fin n → ℝ) (i : Fin n)
    (hi : Integrable (fun y => y i) (bridgeEndpoint w (s+t) x)) :
    (∫ y, (∫ z, z i ∂bridgeEndpoint w t y) ∂bridgeStep w s t x) =
      ∫ y, y i ∂bridgeEndpoint w (s+t) x := by
  rw [← bridgeEndpoint_comp hw s t hz hf] at hi ⊢
  exact (Kernel.integral_comp hi).symm

end G54

end ModHeatKernel

section ModHeatDensity

/- # The Gaussian posterior in product and density coordinates -/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace G54

/-- The possibly infinite measure with Lebesgue density `exp (-ψ)`. -/
noncomputable def potentialVolume {n : ℕ} (ψ : (Fin n → ℝ) → ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity (fun y => ENNReal.ofReal (Real.exp (-ψ y)))

/-- Normalization factor multiplying the unnormalized heat kernel. -/
noncomputable def heatNormalizer (n : ℕ) (s : ℝ) := (Real.sqrt (2 * Real.pi * s))⁻¹ ^ n

theorem heatNormalizer_pos (n : ℕ) {s : ℝ} (hs : 0 < s) : 0 < heatNormalizer n s := by
  unfold heatNormalizer
  positivity

theorem gaussianPi_density {n : ℕ} (x : Fin n → ℝ) {s : ℝ} (hs : 0 < s) :
    Measure.pi (fun i => gaussianReal (x i) (NNReal.mk s hs.le)) = volume.withDensity
      (fun y => ENNReal.ofReal (heatNormalizer n s * Real.exp (heatExponent s x y))) := by
  classical
  let v : ℝ≥0 := (NNReal.mk s hs.le)
  have hv : v ≠ 0 := by exact_mod_cast (show (v : ℝ) ≠ 0 from hs.ne')
  let p := fun i => gaussianPDFReal (x i) v
  have hprod (y : Fin n → ℝ) : (∏ i, p i (y i)) =
      heatNormalizer n s * Real.exp (heatExponent s x y) := by
    simp only [p, gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← Real.exp_sum, heatNormalizer, heatExponent, v, NNReal.coe_mk,
      ← Finset.sum_div, Finset.sum_neg_distrib]
  let (i : Fin n) : SigmaFinite (gaussianReal (x i) v) := inferInstance
  change Measure.pi (fun i => gaussianReal (x i) v) = _
  apply Measure.pi_eq
  intro u hu
  rw [withDensity_apply _ (MeasurableSet.univ_pi hu)]
  change (∫⁻ y, ENNReal.ofReal (heatNormalizer n s * Real.exp (heatExponent s x y))
    ∂((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict (univ.pi u))) = _
  rw [Measure.restrict_pi_pi]
  simp_rw [← hprod]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod fun i => (integrable_gaussianPDFReal (x i) v).restrict)
    (ae_of_all _ fun y => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg (x i) v (y i)),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
      (fun i _ => integral_nonneg fun z => gaussianPDFReal_nonneg (x i) v z)]
  exact Finset.prod_congr rfl fun i _ => (gaussianReal_apply_eq_integral (x i) hv _).symm

/-- A translated and scaled standard Gaussian has the coordinatewise Gaussian product law. -/
theorem gaussianPi_map_affine {n : ℕ} (x : Fin n → ℝ) (r : ℝ) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (fun z => x + r • z) =
      Measure.pi (fun i => gaussianReal (x i) (NNReal.mk (r^2) (sq_nonneg r))) := by
  let f := fun (i : Fin n) (t : ℝ) => x i + r * t
  have he (i : Fin n) : (gaussianReal 0 1).map (f i) =
      gaussianReal (x i) (NNReal.mk (r^2) (sq_nonneg r)) := by
    change (gaussianReal 0 1).map ((fun z : ℝ => x i + z) ∘ (fun z : ℝ => r * z)) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul, gaussianReal_map_const_add]
    simp
  have hσ (i : Fin n) : SigmaFinite ((gaussianReal 0 1).map (f i)) := by
    exact IsFiniteMeasure.toSigmaFinite ((gaussianReal 0 1).map (f i))
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1) (f := f) (hμ := hσ)
    (fun i => (show Continuous (f i) by dsimp [f]; fun_prop).aemeasurable)
  change (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (fun z i => f i (z i)) = _
  simpa only [he] using h

theorem gaussianPi_map_heat {n : ℕ} (x : Fin n → ℝ) {s : ℝ} (hs : 0 < s) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (fun z => x + Real.sqrt s • z) =
      volume.withDensity
        (fun y => ENNReal.ofReal (heatNormalizer n s * Real.exp (heatExponent s x y))) := by
  rw [gaussianPi_map_affine]
  convert gaussianPi_density x hs using 2
  simp [Real.sq_sqrt hs.le]

/-- Heat partition mass equals convolution against a translated normalized Gaussian,
up to its density normalization constant. -/
theorem heatMass_mul_normalizer {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} (hc : Continuous ψ)
    (x : Fin n → ℝ) {s : ℝ} (hs : 0 < s) :
    heatNormalizer n s * heatMass (potentialVolume ψ) s x =
      ∫ z, Real.exp (-ψ (x + Real.sqrt s • z)) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  let γ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let T := fun z : Fin n → ℝ => x + Real.sqrt s • z
  let d := fun y => Real.exp (-ψ y)
  let q := fun y => Real.exp (heatExponent s x y)
  have hd : Continuous d := hc.neg.rexp
  have hq : Continuous q := by unfold q heatExponent; fun_prop
  have hN := heatNormalizer_pos n hs
  have hm : Measurable (fun y => ENNReal.ofReal (heatNormalizer n s * q y)) :=
    (continuous_const.mul hq).measurable.ennreal_ofReal
  have hT : Continuous T := by unfold T; fun_prop
  change heatNormalizer n s * (∫ y, q y ∂potentialVolume ψ) = ∫ z, d (T z) ∂γ
  rw [← integral_map hT.aemeasurable hd.aestronglyMeasurable]
  change _ = ∫ y, d y ∂((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (fun z => x + Real.sqrt s • z))
  rw [gaussianPi_map_heat x hs, potentialVolume,
    integral_withDensity_eq_integral_toReal_smul hd.measurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal (mul_pos hN (Real.exp_pos _)).le, smul_eq_mul, q, d]
    ring

theorem heatMass_potentialVolume_pos {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) {s : ℝ} (hs : 0 < s)
    (x : Fin n → ℝ) : 0 < heatMass (potentialVolume ψ) s x := by
  have h := integral_exp_pos (integrable_exp_neg_lipschitz_gaussian hc hL x (Real.sqrt s))
  rw [← heatMass_mul_normalizer hc x hs] at h
  exact pos_of_mul_pos_right h (heatNormalizer_pos n hs).le

theorem concaveOn_log_heatMass_potentialVolume {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hconv : ConvexOn ℝ univ ψ) (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖)
    {s : ℝ} (hs : 0 < s) :
    ConcaveOn ℝ univ (fun x => Real.log (heatMass (potentialVolume ψ) s x)) := by
  have h := concaveOn_log_gaussianHeat hconv hc hL (Real.sqrt s)
  have he (x : Fin n → ℝ) : Real.log
      (∫ z, Real.exp (-ψ (x + Real.sqrt s • z)) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      = Real.log (heatNormalizer n s) + Real.log (heatMass (potentialVolume ψ) s x) := by
    rw [← heatMass_mul_normalizer hc x hs, Real.log_mul (heatNormalizer_pos n hs).ne'
      (heatMass_potentialVolume_pos hc hL hs x).ne']
  simp only [he] at h
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh := h.2 (mem_univ x) (mem_univ y) ha hb hab
  dsimp only at hh ⊢
  simp only [smul_eq_mul] at hh ⊢
  linear_combination hh - Real.log (heatNormalizer n s) * hab

/-- Finite heat mass makes the potential-weighted volume nonzero. -/
theorem potentialVolume_neZero {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) :
    NeZero (potentialVolume ψ) := by
  refine ⟨fun h => ?_⟩
  have hp := heatMass_potentialVolume_pos hc hL (s := 1) zero_lt_one 0
  simp [heatMass, h] at hp

/-- Doob reweighting of a Gaussian transition by the terminal potential is the
Gaussian-likelihood tilt of the potential-weighted Lebesgue measure. -/
theorem bridgeEndpoint_eq_heatPosterior {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) {s : ℝ≥0} (hs : 0 < s)
    (x : Fin n → ℝ) :
    bridgeEndpoint (fun y => ENNReal.ofReal (Real.exp (-ψ y))) s x =
      (potentialVolume ψ).tilted (heatExponent (s : ℝ) x) := by
  let N := heatNormalizer n s
  let d := fun y => Real.exp (-ψ y)
  let q := fun y => Real.exp (heatExponent s x y)
  let Z := heatMass (potentialVolume ψ) s x
  have hN : 0 < N := heatNormalizer_pos _ (show 0 < (s:ℝ) from hs)
  have hZ : 0 < Z := heatMass_potentialVolume_pos hc hL hs x
  have hd : Continuous d := hc.neg.rexp
  have hq : Continuous q := by unfold q heatExponent; fun_prop
  have hstep : heatStep n s x =
      volume.withDensity (fun y => ENNReal.ofReal (N * q y)) := by
    rw [← heatStep_map_standard]
    exact gaussianPi_map_heat x hs
  have hm : ∫⁻ z, ENNReal.ofReal (d z) ∂heatStep n s x = ENNReal.ofReal (N*Z) := by
    rw [← heatStep_map_standard, lintegral_map hd.measurable.ennreal_ofReal (by fun_prop)]
    unfold d gaussianIncrements
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_lipschitz_gaussian hc hL x _)
        (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    exact congrArg ENNReal.ofReal (heatMass_mul_normalizer hc x hs).symm
  change doobStep (heatStep n s) (fun z => ENNReal.ofReal (d z)) x = _
  rw [doobStep_apply _ hd.measurable.ennreal_ofReal, hm, hstep]
  change _ = (volume.withDensity (fun z => ENNReal.ofReal (d z))).withDensity
    (fun y => ENNReal.ofReal (q y / Z))
  have hqm : Measurable (fun y => ENNReal.ofReal (N * q y)) :=
    (continuous_const.mul hq).measurable.ennreal_ofReal
  have hdm : Measurable (fun y => ENNReal.ofReal (d y)) := hd.measurable.ennreal_ofReal
  have hqZ : Measurable (fun y => ENNReal.ofReal (q y / Z)) := (hq.measurable.div_const Z).ennreal_ofReal
  rw [← withDensity_mul _ hqm hdm, ← withDensity_mul _ hdm hqZ,
    ← withDensity_smul _ (hqm.mul hdm)]
  apply withDensity_congr_ae
  apply ae_of_all
  intro y
  change (ENNReal.ofReal (N*Z))⁻¹ * (ENNReal.ofReal (N*q y) * ENNReal.ofReal (d y)) =
    ENNReal.ofReal (d y) * ENNReal.ofReal (q y / Z)
  have hnq : 0 ≤ N * q y := mul_nonneg hN.le (Real.exp_pos _).le
  have hd0 : 0 ≤ d y := (Real.exp_pos _).le
  rw [← ENNReal.ofReal_inv_of_pos (mul_pos hN hZ), ← ENNReal.ofReal_mul hnq,
    ← ENNReal.ofReal_mul (inv_pos.mpr (mul_pos hN hZ)).le, ← ENNReal.ofReal_mul hd0]
  apply congrArg ENNReal.ofReal
  field_simp [hN.ne', hZ.ne']

end G54

end ModHeatDensity

section ModBridgePotential

/- # Gaussian bridge weights of convex Lipschitz potentials -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace G54

noncomputable def potentialWeight {n : ℕ} (ψ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) :=
  ENNReal.ofReal (Real.exp (-ψ y))

noncomputable def bridgeLogWeight {n : ℕ} (ψ : (Fin n → ℝ) → ℝ) (s : ℝ≥0) (x : Fin n → ℝ) :=
  Real.log (∫ z, Real.exp (-ψ (x + Real.sqrt (s : ℝ) • z)) ∂gaussianIncrements n 1)

theorem measurable_potentialWeight {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} (hc : Continuous ψ) :
    Measurable (potentialWeight ψ) :=
  (Real.continuous_exp.comp hc.neg).measurable.ennreal_ofReal

theorem heatWeight_exp_log {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ} (hc : Continuous ψ)
    (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (s : ℝ≥0) (x : Fin n → ℝ) :
    heatWeight (potentialWeight ψ) s x = ENNReal.ofReal (Real.exp (bridgeLogWeight ψ s x)) := by
  have hi := integrable_exp_neg_lipschitz_gaussian hc hL x (Real.sqrt (s : ℝ))
  unfold heatWeight bridgeLogWeight
  rw [← heatStep_map_standard, lintegral_map (measurable_potentialWeight hc) (by fun_prop),
    gaussianIncrements, Real.exp_log (integral_exp_pos hi)]
  exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun z => (Real.exp_pos _).le))).symm

theorem bridgeLogWeight_lipschitz {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ} (hc : Continuous ψ)
    (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (s : ℝ≥0) (x y : Fin n → ℝ) :
    |bridgeLogWeight ψ s x - bridgeLogWeight ψ s y| ≤ L * ‖x-y‖ :=
  log_gaussianHeat_lipschitz hc hL _ x y

theorem bridgeLogWeight_concave {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hcv : ConvexOn ℝ univ ψ) (hc : Continuous ψ)
    (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (s : ℝ≥0) :
    ConcaveOn ℝ univ (bridgeLogWeight ψ s) := concaveOn_log_gaussianHeat hcv hc hL _

theorem bridgeLogWeight_continuous {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (s : ℝ≥0) :
    Continuous (bridgeLogWeight ψ s) := by
  apply LipschitzWith.continuous (K := Real.toNNReal L)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  exact (bridgeLogWeight_lipschitz hc hL s x y).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))

theorem bridgeEndpoint_markov {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ} (hc : Continuous ψ)
    (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (s : ℝ≥0) :
    IsMarkovKernel (bridgeEndpoint (potentialWeight ψ) s) := by
  refine doobStep_markov _ (measurable_potentialWeight hc) (fun x => ?_) (fun x => ?_)
  · change heatWeight _ _ _ ≠ 0
    rw [heatWeight_exp_log hc hL]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  · change heatWeight _ _ _ ≠ ∞
    rw [heatWeight_exp_log hc hL]; exact ENNReal.ofReal_ne_top

theorem bridgeStep_markov {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ} (hc : Continuous ψ)
    (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (s t : ℝ≥0) :
    IsMarkovKernel (bridgeStep (potentialWeight ψ) s t) := by
  have hm : Measurable (heatWeight (potentialWeight ψ) t) := (measurable_potentialWeight hc).lintegral_kernel
  refine doobStep_markov _ hm (fun x => ?_) (fun x => ?_)
  · change heatWeight (heatWeight _ _) _ _ ≠ 0
    rw [heatWeight_add (measurable_potentialWeight hc), heatWeight_exp_log hc hL]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  · change heatWeight (heatWeight _ _) _ _ ≠ ∞
    rw [heatWeight_add (measurable_potentialWeight hc), heatWeight_exp_log hc hL]
    exact ENNReal.ofReal_ne_top

/-- Reweighting a pushforward is equivalent to reweighting before applying its map. -/
private theorem reweight_pushforward {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) {T : E → F} (hT : Measurable T) {w : F → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity (fun x => w (T x))).map T = (μ.map T).withDensity w := by
  ext B hB
  rw [Measure.map_apply hT hB, withDensity_apply _ (hT hB), withDensity_apply _ hB,
    ← lintegral_indicator hB, lintegral_map (hw.indicator hB) hT, ← lintegral_indicator (hT hB)]
  exact lintegral_congr (fun x => by by_cases hx : T x ∈ B <;> simp [hx])

/-- A normalized exponential Doob transform of a Gaussian transition is the affine
pushforward of an exponentially tilted standard Gaussian. -/
theorem doobStep_eq_affine_tilt {n : ℕ} {A : (Fin n → ℝ) → ℝ} (hm : Measurable A)
    (s : ℝ≥0) (x : Fin n → ℝ)
    (hi : Integrable (fun z => Real.exp (A (x + Real.sqrt (s : ℝ) • z))) (gaussianIncrements n 1)) :
    let T := fun z : Fin n → ℝ => x + Real.sqrt (s : ℝ) • z
    doobStep (heatStep n s) (fun y => ENNReal.ofReal (Real.exp (A y))) x =
      ((gaussianIncrements n 1).tilted (fun z => A (T z))).map T := by
  let T := fun z : Fin n → ℝ => x + Real.sqrt (s : ℝ) • z
  let μ := gaussianIncrements n 1
  let w := fun y => ENNReal.ofReal (Real.exp (A y))
  have hT : Measurable T := by dsimp [T]; fun_prop
  have hw : Measurable w := hm.exp.ennreal_ofReal
  let c := ∫ z, Real.exp (A (T z)) ∂μ
  have hc : 0 < c := integral_exp_pos hi
  have hN : (∫⁻ z, w z ∂heatStep n s x) = ENNReal.ofReal c := by
    rw [← heatStep_map_standard, lintegral_map hw hT]
    exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm
  have he : μ.tilted (fun z => A (T z)) = (ENNReal.ofReal c)⁻¹ • μ.withDensity (fun z => w (T z)) := by
    rw [Measure.tilted, ← withDensity_smul _ (show Measurable (fun z => w (T z)) from hw.comp hT)]
    congr 1; funext z
    change ENNReal.ofReal (Real.exp (A (T z)) / c) = (ENNReal.ofReal c)⁻¹ * w (T z)
    rw [ENNReal.ofReal_div_of_pos hc, div_eq_mul_inv, mul_comm]
  change doobStep (heatStep n s) w x = (μ.tilted (fun z => A (T z))).map T
  rw [he, Measure.map_smul, reweight_pushforward _ hT hw, doobStep_apply _ hw, hN]
  exact congrArg (fun ρ : Measure (Fin n → ℝ) => (ENNReal.ofReal c)⁻¹ • ρ.withDensity w)
    (heatStep_map_standard n s x).symm

theorem bridgeStep_eq_affine_tilt {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ} (hc : Continuous ψ)
    (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (s t : ℝ≥0) (x : Fin n → ℝ) :
    let T := fun z : Fin n → ℝ => x + Real.sqrt (s : ℝ) • z
    bridgeStep (potentialWeight ψ) s t x =
      ((gaussianIncrements n 1).tilted (fun z => bridgeLogWeight ψ t (T z))).map T := by
  have he := funext (heatWeight_exp_log hc hL t)
  unfold bridgeStep; rw [he]
  apply doobStep_eq_affine_tilt (bridgeLogWeight_continuous hc hL t).measurable
  simpa only [gaussianIncrements, Pi.neg_apply, neg_neg] using integrable_exp_neg_lipschitz_gaussian
    (bridgeLogWeight_continuous hc hL t).neg
    (fun u v => by simpa only [Pi.neg_apply, neg_sub_neg, abs_sub_comm] using bridgeLogWeight_lipschitz hc hL t u v)
    x (Real.sqrt (s : ℝ))

theorem bridgeEndpoint_normalized {n : ℕ} {w : (Fin n → ℝ) → ℝ≥0∞} (hw : Measurable w)
    (hprob : IsProbabilityMeasure ((gaussianIncrements n 1).withDensity w)) :
    bridgeEndpoint w 1 0 = (gaussianIncrements n 1).withDensity w := by
  have h0 : heatStep n 1 0 = gaussianIncrements n 1 := by rw [heatStep_apply]; simp
  have h1 := hprob.measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [bridgeEndpoint, doobStep_apply _ hw, h0, h1, inv_one, one_smul]

end G54

end ModBridgePotential

section ModBridgeMean

/- # The endpoint martingale of the discrete Gaussian bridge -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace G54

/-- Conditional endpoint barycentre at a location with remaining Gaussian variance `t`. -/
noncomputable def bridgeMean {n : ℕ} (ψ : (Fin n → ℝ) → ℝ) (t : ℝ≥0)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∫ y, y i ∂bridgeEndpoint (potentialWeight ψ) t x

theorem measurable_bridgeMean {n : ℕ} (ψ : (Fin n → ℝ) → ℝ) (t : ℝ≥0) :
    Measurable (bridgeMean ψ t) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_pi_apply (X := fun _ : Fin n => ℝ) i).stronglyMeasurable.integral_kernel
    (κ := bridgeEndpoint (potentialWeight ψ) t)).measurable

private theorem bridge_potential_zero {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} (hc : Continuous ψ)
    (x : Fin n → ℝ) : bridgeEndpoint (potentialWeight ψ) 0 x = Measure.dirac x :=
  bridgeEndpoint_zero (measurable_potentialWeight hc)
    (fun _ => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne') (fun _ => ENNReal.ofReal_ne_top) x

theorem bridgeMean_zero {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} (hc : Continuous ψ) (x : Fin n → ℝ) :
    bridgeMean ψ 0 x = x := by
  funext i
  rw [bridgeMean, bridge_potential_zero hc]
  simp

theorem bridgeMean_eq_heatMean {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ} (hc : Continuous ψ)
    (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) {t : ℝ≥0} (ht : 0 < t) (x : Fin n → ℝ) :
    bridgeMean ψ t x = heatMean (potentialVolume ψ) t x := by
  unfold bridgeMean heatMean potentialWeight
  rw [bridgeEndpoint_eq_heatPosterior hc hL ht]

theorem bridgeMean_nonexpansive {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hconv : ConvexOn ℝ univ ψ) (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖)
    (t : ℝ≥0) (x y : Fin n → ℝ) :
    ∑ i, (bridgeMean ψ t x i - bridgeMean ψ t y i)^2 ≤ ∑ i, (x i-y i)^2 := by
  rcases eq_or_lt_of_le (show 0 ≤ t from zero_le) with h | ht
  · simp [← h, bridgeMean_zero hc]
  have := potentialVolume_neZero hc hL
  rw [bridgeMean_eq_heatMean hc hL ht, bridgeMean_eq_heatMean hc hL ht]
  exact heatMean_nonexpansive (potentialVolume ψ) ht
    (heatMass_potentialVolume_pos hc hL ht) (concaveOn_log_heatMass_potentialVolume hconv hc hL ht) x y

theorem bridgeEndpoint_integrable_coord {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (t : ℝ≥0)
    (x : Fin n → ℝ) (i : Fin n) :
    Integrable (fun y => y i) (bridgeEndpoint (potentialWeight ψ) t x) := by
  rcases eq_or_lt_of_le (show 0 ≤ t from zero_le) with h | ht
  · rw [← h, bridge_potential_zero hc]
    exact integrable_dirac (by finiteness)
  have := potentialVolume_neZero hc hL
  unfold potentialWeight
  rw [bridgeEndpoint_eq_heatPosterior hc hL ht]
  exact heat_integrable_coord (potentialVolume ψ) ht (heatMass_potentialVolume_pos hc hL ht) x i

theorem bridgeMean_tower {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖) (s t : ℝ≥0)
    (x : Fin n → ℝ) (i : Fin n) :
    (∫ y, bridgeMean ψ t y i ∂bridgeStep (potentialWeight ψ) s t x) =
      bridgeMean ψ (s+t) x i := by
  apply bridge_mean_tower (measurable_potentialWeight hc)
  · intro y
    rw [heatWeight_exp_log hc hL]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  · intro y
    rw [heatWeight_exp_log hc hL]
    exact ENNReal.ofReal_ne_top
  · exact bridgeEndpoint_integrable_coord hc hL _ _ _

end G54

end ModBridgeMean

section ModBridgeGrid

/- # Endpoint distribution along a discrete Föllmer bridge -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace G54

noncomputable def gridStep (N : ℕ) : ℝ≥0 := (N : ℝ≥0)⁻¹

noncomputable def gridRemaining (N k : ℕ) : ℝ≥0 := (N-k : ℕ) * gridStep N

theorem gridRemaining_start {N : ℕ} (h : 0 < N) : gridRemaining N 0 = 1 := by
  simp [gridRemaining, gridStep, Nat.ne_zero_of_lt h]

@[simp] theorem gridRemaining_end (N : ℕ) : gridRemaining N N = 0 := by simp [gridRemaining]

theorem gridRemaining_succ {N k : ℕ} (hk : k < N) :
    gridStep N + gridRemaining N (k+1) = gridRemaining N k := by
  have h : N - k = 1 + (N - (k+1)) := by omega
  unfold gridRemaining
  conv_rhs => rw [h, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

noncomputable def gridSite {n : ℕ} (w : (Fin n → ℝ) → ℝ≥0∞) (N : ℕ) :
    ℕ → Measure (Fin n → ℝ)
  | 0 => Measure.dirac 0
  | k+1 => bridgeStep w (gridStep N) (gridRemaining N (k+1)) ∘ₘ gridSite w N k

/-- A finite row of tilted Gaussian transitions has exactly the required endpoint law. -/
theorem gridSite_end {n N : ℕ} (hN : 0 < N) {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ u v, |ψ u - ψ v| ≤ L * ‖u-v‖)
    (hprob : IsProbabilityMeasure ((gaussianIncrements n 1).withDensity (potentialWeight ψ))) :
    gridSite (potentialWeight ψ) N N = (gaussianIncrements n 1).withDensity (potentialWeight ψ) := by
  let w := potentialWeight ψ
  have hw : Measurable w := measurable_potentialWeight hc
  have h (k : ℕ) (hk : k ≤ N) :
      bridgeEndpoint w (gridRemaining N k) ∘ₘ gridSite w N k = bridgeEndpoint w 1 0 := by
    induction k with
    | zero =>
      rw [gridRemaining_start hN, gridSite, Measure.dirac_bind (bridgeEndpoint w 1).measurable]
    | succ k ih =>
      let t := gridRemaining N (k+1)
      have hze x : heatWeight w t x ≠ 0 := by
        rw [heatWeight_exp_log hc hL]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      have hfe x : heatWeight w t x ≠ ∞ := by rw [heatWeight_exp_log hc hL]; exact ENNReal.ofReal_ne_top
      change bridgeEndpoint w t ∘ₘ (bridgeStep w (gridStep N) t ∘ₘ gridSite w N k) = _
      rw [Measure.comp_assoc, bridgeEndpoint_comp hw _ _ hze hfe, gridRemaining_succ (by omega : k < N)]
      exact ih (by omega)
  have h0 : bridgeEndpoint w 0 = Kernel.id := by
    ext x B _
    rw [bridgeEndpoint_zero hw (fun _ => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
      (fun _ => ENNReal.ofReal_ne_top), Kernel.id_apply]
  have hh := h N le_rfl
  rwa [gridRemaining_end, h0, Measure.id_comp, bridgeEndpoint_normalized hw hprob] at hh

theorem tendsto_gridStep : Tendsto (fun N => (gridStep N : ℝ)) atTop (𝓝 0) := by
  simpa [gridStep, Function.comp_def] using (tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem tendsto_gridError (C : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * (C * (Real.sqrt (gridStep N : ℝ))^3)) atTop (𝓝 0) := by
  have he := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp tendsto_gridStep
  have hlim : Tendsto (fun N => C * Real.sqrt (gridStep N : ℝ)) atTop (𝓝 0) := by
    simpa using he.const_mul C
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have h : (N : ℝ) * (gridStep N : ℝ) = 1 := by
    simp [gridStep, Nat.ne_zero_of_lt hN]
  let r : ℝ := gridStep N
  let u := Real.sqrt r
  have hu : u^2 = r := Real.sq_sqrt (show 0 ≤ r from (gridStep N).2)
  change C * u = (N : ℝ) * (C * u^3)
  calc
    C * u = C * u * ((N : ℝ) * r) := by rw [show (N : ℝ) * r = 1 from h, mul_one]
    _ = (N : ℝ) * (C * u^3) := by rw [← hu]; ring


end G54

end ModBridgeGrid

section ModStepMoments

/- # Conditional projected moments for a Gaussian bridge step -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace G54

/-- Projecting a Euclidean nonexpansive map along a vector `v` gives a scalar
observable with Lipschitz constant equal to the Euclidean length of `v`. -/
theorem nonexpansive_projection_lipschitz {n : ℕ} {M : (Fin n → ℝ) → (Fin n → ℝ)}
    (hM : ∀ y z, ∑ i, (M y i - M z i)^2 ≤ ∑ i, (y i - z i)^2)
    (v x y : Fin n → ℝ) :
    |(∑ i, v i * M x i) - (∑ i, v i * M y i)| ≤
      Real.sqrt (∑ i, v i^2) * Real.sqrt (∑ i, (x i - y i)^2) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))]
  apply Real.sqrt_le_sqrt
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun i => M x i - M y i)).trans
    (mul_le_mul_of_nonneg_left (hM x y) (Finset.sum_nonneg fun i _ => sq_nonneg _))

/-- Uniform projected variance and third centered moment for a Gaussian step with time
increment `δ`, starting at `x` and reweighted by the destination log weight `A`. -/
theorem affine_step_projection_moments_memLp {n : ℕ} (A : (Fin n → ℝ) → ℝ)
    {K : ℝ} (hAc : ConcaveOn ℝ univ A) (hA : ∀ z w, |A z - A w| ≤ K * ‖z - w‖)
    (M : (Fin n → ℝ) → (Fin n → ℝ))
    (hM : ∀ z w, ∑ i, (M z i - M w i)^2 ≤ ∑ i, (z i - w i)^2)
    (δ : ℝ≥0) (x v : Fin n → ℝ) :
    let T := fun z : Fin n → ℝ => x + Real.sqrt (δ : ℝ) • z
    let μ := ((Measure.pi fun _ : Fin n => gaussianReal 0 1).tilted (fun z => A (T z))).map T
    let U := fun y => ∑ i, v i * M y i
    (∀ p : ℝ≥0, MemLp U p μ) ∧
    variance U μ ≤ (δ : ℝ) * ∑ i, v i^2 ∧
      (∫ y, |U y - ∫ z, U z ∂μ|^3 ∂μ) ≤
        12 * Real.exp 1 * (Real.sqrt (δ : ℝ) * Real.sqrt (∑ i, v i^2))^3 := by
  let r := Real.sqrt (δ : ℝ)
  let T := fun z : Fin n → ℝ => x + r • z
  let U := fun y => ∑ i, v i * M y i
  let V := Real.sqrt (∑ i, v i^2)
  let γ := Measure.pi fun _ : Fin n => gaussianReal 0 1
  let P := γ.tilted (fun z => A (T z))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hV : 0 ≤ V := Real.sqrt_nonneg _
  have hUL (z w) : |U z - U w| ≤ V * Real.sqrt (∑ i, (z i-w i)^2) :=
    nonexpansive_projection_lipschitz hM v z w
  have hUc : Continuous U := continuous_of_sup_lipschitz (euclidean_lipschitz_to_sup hV hUL)
  have hTc : Continuous T := continuous_const.add (continuous_const_smul _)
  have hconv : ConcaveOn ℝ univ (fun z => A (T z)) := by
    refine ⟨convex_univ, ?_⟩
    intro z _ w _ a b ha hb hab
    have he : T (a • z + b • w) = a • (T z) + b • (T w) := by
      ext i
      simp only [T, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      linear_combination -(x i) * hab
    dsimp only
    rw [he]
    exact hAc.2 (mem_univ (T z)) (mem_univ (T w)) ha hb hab
  have hsub (z w) : T z - T w = r • (z-w) := by dsimp only [T]; module
  have hAL (z w) : |A (T z) - A (T w)| ≤ (K * r) * ‖z-w‖ := by
    simpa only [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, mul_assoc] using hA (T z) (T w)
  have hWL (z w) : |U (T z) - U (T w)| ≤ (r * V) * Real.sqrt (∑ i, (z i - w i)^2) := by
    apply (hUL (T z) (T w)).trans_eq
    have he : (∑ i, (T z i - T w i)^2) = r^2 * ∑ i, (z i - w i)^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by dsimp [T]; ring
    rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr]
    ring
  obtain ⟨hp,h2,h3⟩ := gaussian_tilt_lipschitz_moments_memLp (fun z => A (T z)) (fun z => U (T z))
    (mul_nonneg hr hV) hconv hAL hWL
  refine ⟨fun p => (memLp_map_measure_iff hUc.aestronglyMeasurable hTc.aemeasurable).mpr (hp p), ?_⟩
  change variance U (P.map T) ≤ _ ∧ (∫ y, |U y - ∫ z, U z ∂(P.map T)|^3 ∂(P.map T)) ≤ _
  rw [variance_map hUc.aemeasurable hTc.aemeasurable, integral_map hTc.aemeasurable hUc.aestronglyMeasurable,
    integral_map hTc.aemeasurable (by fun_prop)]
  refine ⟨h2.trans_eq ?_, h3⟩
  dsimp only [r,V]
  rw [mul_pow]
  exact congrArg₂ (· * ·) (Real.sq_sqrt δ.coe_nonneg)
    (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i)))

theorem affine_step_projection_moments {n : ℕ} (A : (Fin n → ℝ) → ℝ)
    {K : ℝ} (hAc : ConcaveOn ℝ univ A) (hA : ∀ z w, |A z - A w| ≤ K * ‖z - w‖)
    (M : (Fin n → ℝ) → (Fin n → ℝ))
    (hM : ∀ z w, ∑ i, (M z i - M w i)^2 ≤ ∑ i, (z i - w i)^2)
    (δ : ℝ≥0) (x v : Fin n → ℝ) :
    let T := fun z : Fin n → ℝ => x + Real.sqrt (δ : ℝ) • z
    let μ := ((Measure.pi fun _ : Fin n => gaussianReal 0 1).tilted (fun z => A (T z))).map T
    let U := fun y => ∑ i, v i * M y i
    variance U μ ≤ (δ : ℝ) * ∑ i, v i^2 ∧
      (∫ y, |U y - ∫ z, U z ∂μ|^3 ∂μ) ≤
        12 * Real.exp 1 * (Real.sqrt (δ : ℝ) * Real.sqrt (∑ i, v i^2))^3 :=
  (affine_step_projection_moments_memLp A hAc hA M hM δ x v).2

theorem affine_step_memLp {n : ℕ} (A : (Fin n → ℝ) → ℝ)
    {K : ℝ} (hAc : ConcaveOn ℝ univ A) (hA : ∀ z w, |A z - A w| ≤ K * ‖z - w‖)
    (M : (Fin n → ℝ) → (Fin n → ℝ))
    (hM : ∀ z w, ∑ i, (M z i - M w i)^2 ≤ ∑ i, (z i - w i)^2)
    (δ : ℝ≥0) (x : Fin n → ℝ) (p : ℝ≥0) :
    let T := fun z : Fin n → ℝ => x + Real.sqrt (δ : ℝ) • z
    let μ := ((Measure.pi fun _ : Fin n => gaussianReal 0 1).tilted (fun z => A (T z))).map T
    MemLp M p μ := by
  apply memLp_pi_iff.mpr
  intro i
  have hh := (affine_step_projection_moments_memLp A hAc hA M hM δ x (Pi.single i 1)).1 p
  simpa [Pi.single_apply] using hh

end G54

end ModStepMoments

section ModCompensation

/- # Gaussian covariance compensation for vector martingale increments -/

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace G54

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

local instance : BorelSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℝ))

/-- The centered Gaussian with a measurable positive semidefinite covariance matrix
depends measurably on the parameter, including at singular covariances. -/
theorem measurable_centered_multivariateGaussian {α : Type*} [MeasurableSpace α]
    (R : α → Matrix ι ι ℝ) (hR : ∀ i j, Measurable (fun a => R a i j)) (hpos : ∀ a, (R a).PosSemidef) :
    Measurable (fun a => multivariateGaussian (0 : EuclideanSpace ℝ ι) (R a)) := by
  have hRm : Measurable R := measurable_pi_lambda _ fun i => measurable_pi_lambda _ (hR i)
  have hs : Measurable (fun a => CFC.sqrt (R a)) := by
    let p := {A : Matrix ι ι ℝ | 0 ≤ A}
    have h : Continuous (fun A : p => CFC.sqrt A.val) :=
      continuousOn_iff_continuous_domRestrict.mp CFC.continuousOn_sqrt
    exact h.measurable.comp (hRm.subtype_mk (h := fun a => (hpos a).nonneg))
  let F := fun q : α × EuclideanSpace ℝ ι => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (R q.1)) q.2
  have hF : Measurable F := by
    have hclm : Continuous (fun A : Matrix ι ι ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ) A) :=
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous
    have happ : Continuous (fun p : (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) × EuclideanSpace ℝ ι => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    exact happ.measurable.comp ((hclm.measurable.comp (hs.comp measurable_fst)).prodMk measurable_snd)
  let κ := (Kernel.id (α := α)).prod (Kernel.const α (stdGaussian (EuclideanSpace ℝ ι)))
  have hmeas := (κ.map F).measurable
  convert hmeas using 1
  funext a
  rw [Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
  simp [multivariateGaussian, Function.comp_def, F]

/-- The conditional law of the Gaussian noise filling the covariance deficit. -/
noncomputable def compensationNoiseKernel {α : Type*} [MeasurableSpace α]
    (R : α → Matrix ι ι ℝ) (hR : ∀ i j, Measurable (fun a => R a i j)) (hpos : ∀ a, (R a).PosSemidef) :
    Kernel α (EuclideanSpace ℝ ι) where
  toFun a := multivariateGaussian 0 (R a)
  measurable' := measurable_centered_multivariateGaussian R hR hpos

instance {α : Type*} [MeasurableSpace α] (R : α → Matrix ι ι ℝ)
    (hR : ∀ i j, Measurable (fun a => R a i j)) (hpos : ∀ a, (R a).PosSemidef) :
    IsMarkovKernel (compensationNoiseKernel R hR hpos) where
  isProbabilityMeasure a := by
    change IsProbabilityMeasure (multivariateGaussian _ _)
    infer_instance

/-- The two vector increments on the product space of the original increment and
the compensating Gaussian. Their sum equals the original increment pointwise. -/
noncomputable def compensatedPair (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  ((2⁻¹ : ℝ) • p.1 + p.2, (2⁻¹ : ℝ) • p.1 - p.2)

omit [DecidableEq ι] in
theorem measurable_compensatedPair : Measurable (compensatedPair (ι := ι)) := by
  unfold compensatedPair
  fun_prop

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem compensatedPair_sum (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (compensatedPair p).1 + (compensatedPair p).2 = p.1 := by
  unfold compensatedPair
  module

/-- The pair can be sampled conditionally on any measurable past state. -/
noncomputable def compensatedKernel {α : Type*} [MeasurableSpace α]
    (κ : Kernel α (EuclideanSpace ℝ ι)) (R : α → Matrix ι ι ℝ) (hR : ∀ i j, Measurable (fun a => R a i j))
    (hpos : ∀ a, (R a).PosSemidef) : Kernel α (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  (κ.prod (compensationNoiseKernel R hR hpos)).map compensatedPair

instance {α : Type*} [MeasurableSpace α]
    (κ : Kernel α (EuclideanSpace ℝ ι)) [IsMarkovKernel κ] (R : α → Matrix ι ι ℝ)
    (hR : ∀ i j, Measurable (fun a => R a i j)) (hpos : ∀ a, (R a).PosSemidef) :
    IsMarkovKernel (compensatedKernel κ R hR hpos) := Kernel.IsMarkovKernel.map _ measurable_compensatedPair

/-- Projected first and second moments after adding or subtracting the independent
Gaussian compensation. The scalar `c` is normally either `1` or `-1`. -/
theorem compensated_projection_moments (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hm : (∫ x, x ∂μ) = 0) {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    (t : EuclideanSpace ℝ ι) (c : ℝ) (hc : c ^ 2 = 1) :
    let ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) R
    let Z := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      ⟪t, (2⁻¹ : ℝ) • p.1 + c • p.2⟫
    (∫ p, Z p ∂μ.prod ν) = 0 ∧
      Var[Z; μ.prod ν] = (4⁻¹ : ℝ) * Var[fun x => ⟪t, x⟫; μ] + t ⬝ᵥ R *ᵥ t := by
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) R
  let L := fun x : EuclideanSpace ℝ ι => ⟪t, x⟫
  have hμL : MemLp L 2 μ := hμ.const_inner t
  have hν2 : MemLp id 2 ν := IsGaussian.memLp_two_id
  have hνL : MemLp L 2 ν := hν2.const_inner t
  have hμI : (∫ x, L x ∂μ) = 0 := by
    simpa [L, hm] using integral_inner (𝕜 := ℝ) (hμ.integrable (by norm_num)) t
  have hνI : (∫ x, L x ∂ν) = 0 := by
    simpa [L, ν] using integral_inner (𝕜 := ℝ) (hν2.integrable (by norm_num)) t
  have hv : Var[L; ν] = t ⬝ᵥ R *ᵥ t := by
    rw [← covarianceBilin_self hν2, covarianceBilin_multivariateGaussian hR]
  simp only [inner_add_right, real_inner_smul_right]
  change (∫ p, 2⁻¹ * L p.1 + c * L p.2 ∂μ.prod ν) = 0 ∧
    Var[fun p => 2⁻¹ * L p.1 + c * L p.2; μ.prod ν] = _
  have hf : MemLp (fun x => 2⁻¹ * L x) 2 μ := hμL.const_mul _
  have hg : MemLp (fun x => c * L x) 2 ν := hνL.const_mul _
  constructor
  · rw [integral_add ((hf.comp_fst ν).integrable (by norm_num)) ((hg.comp_snd μ).integrable (by norm_num))]
    rw [integral_fun_fst (fun x => 2⁻¹ * L x), integral_fun_snd (fun x => c * L x)]
    simp [integral_const_mul, hμI, hνI]
  · rw [variance_add_prod hf hg, variance_const_mul, variance_const_mul, hc, one_mul, hv]
    norm_num [L]

/-- Pushing the compensated increment pair forward by addition recovers
the prescribed conditional increment distribution. -/
theorem compensatedKernel_sum {α : Type*} [MeasurableSpace α]
    (κ : Kernel α (EuclideanSpace ℝ ι)) [IsMarkovKernel κ] (R : α → Matrix ι ι ℝ)
    (hR : ∀ i j, Measurable (fun a => R a i j)) (hpos : ∀ a, (R a).PosSemidef)
    (a : α) :
    ((compensatedKernel κ R hR hpos) a).map (fun p => p.1 + p.2) = κ a := by
  rw [compensatedKernel, Kernel.map_apply _ measurable_compensatedPair,
    Kernel.prod_apply, Measure.map_map (by fun_prop) measurable_compensatedPair]
  simp [Function.comp_def]

/-- Covariance deficit after splitting an increment in half. -/
noncomputable def covarianceDeficit (δ : ℝ) (μ : Measure (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  δ • 1 - (4⁻¹ : ℝ) • Matrix.of (fun i j => cov[fun x => x i, fun x => x j; μ])

theorem covarianceDeficit_quad (δ : ℝ) (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (t : EuclideanSpace ℝ ι) :
    t ⬝ᵥ covarianceDeficit δ μ *ᵥ t = δ * ‖t‖^2 - (4⁻¹ : ℝ) * Var[fun x => ⟪t, x⟫; μ] := by
  have heq := covarianceBilin_apply_pi (X := fun i (x : EuclideanSpace ℝ ι) => x i)
    (fun i => hμ.eval_piLp i) t t
  have hid : (fun ω : EuclideanSpace ℝ ι => toLp 2 (fun i => ω i)) = id := rfl
  rw [hid, Measure.map_id, covarianceBilin_self hμ] at heq
  rw [covarianceDeficit, sub_mulVec, dotProduct_sub, smul_mulVec, smul_mulVec,
    dotProduct_smul, dotProduct_smul, one_mulVec, smul_eq_mul, smul_eq_mul, heq]
  congr 2
  · rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  · simp [dotProduct, mulVec, Finset.mul_sum, mul_comm, mul_assoc]

theorem covarianceDeficit_posSemidef (δ : ℝ) (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ)
    (hvar : ∀ t : EuclideanSpace ℝ ι, Var[fun x => ⟪t, x⟫; μ] ≤ 4 * δ * ‖t‖^2) :
    (covarianceDeficit δ μ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have hcov : (Matrix.of (fun i j : ι => cov[fun x => x i, fun x => x j; μ])).IsHermitian := by
      ext i j
      simp [Matrix.conjTranspose_apply, covariance_comm]
    exact (Matrix.isHermitian_one.smul (IsSelfAdjoint.all δ)).sub (hcov.smul (IsSelfAdjoint.all _))
  · intro x
    let t : EuclideanSpace ℝ ι := toLp 2 x
    have h := covarianceDeficit_quad δ μ hμ t
    simp only [star_trivial]
    change 0 ≤ t ⬝ᵥ covarianceDeficit δ μ *ᵥ t
    rw [h]
    linarith [hvar t]

/-- The deficit entries are measurable for a kernel with finite second moments. -/
theorem measurable_covarianceDeficit_entry {α : Type*} [MeasurableSpace α]
    (κ : Kernel α (EuclideanSpace ℝ ι)) [IsMarkovKernel κ] (hκ : ∀ a, MemLp id 2 (κ a))
    (δ : ℝ) (i j : ι) : Measurable (fun a => covarianceDeficit δ (κ a) i j) := by
  have hi (k : ι) : StronglyMeasurable (fun x : EuclideanSpace ℝ ι => x k) := by fun_prop
  have hcov : Measurable (fun a => cov[fun x => x i, fun x => x j; κ a]) := by
    have e (a : α) : cov[fun x => x i, fun x => x j; κ a] =
        (∫ x, x i * x j ∂κ a) - (∫ x, x i ∂κ a) * (∫ x, x j ∂κ a) :=
      covariance_eq_sub ((hκ a).eval_piLp i) ((hκ a).eval_piLp j)
    simp_rw [e]
    exact ((hi i).mul (hi j)).integral_kernel.measurable.sub
      ((hi i).integral_kernel.measurable.mul (hi j).integral_kernel.measurable)
  exact measurable_const.sub (measurable_const.mul hcov)

/-- Exact third absolute moment of a centered one-dimensional Gaussian, including variance zero. -/
theorem centeredGaussian_third (v : ℝ≥0) :
    (∫ x : ℝ, |x|^3 ∂gaussianReal 0 v) =
      (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => (Real.sqrt v) * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    simp [Real.sq_sqrt v.coe_nonneg]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
  congr 1
  ext x
  simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]

/-- Every projection of the Gaussian compensation has its third absolute moment
controlled by the three-halves power of the allotted time step. -/
theorem compensationNoise_third (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (δ : ℝ) (hR : (covarianceDeficit δ μ).PosSemidef)
    (t : EuclideanSpace ℝ ι) :
    let ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) (covarianceDeficit δ μ)
    (∫ z, |⟪t, z⟫| ^ 3 ∂ν) ≤ (Real.sqrt (δ * ‖t‖^2))^3 *
      ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) (covarianceDeficit δ μ)
  let L := innerSL ℝ t
  have h2 : MemLp id 2 ν := IsGaussian.memLp_two_id
  have hmean : (∫ z, L z ∂ν) = 0 := by
    rw [L.integral_comp_id_comm IsGaussian.integrable_id]
    simp [ν]
  have hvar : Var[L; ν] = t ⬝ᵥ covarianceDeficit δ μ *ᵥ t := by
    change Var[fun x => ⟪t, x⟫; ν] = _
    rw [← covarianceBilin_self h2 t, covarianceBilin_multivariateGaussian hR]
  have hle : Var[L; ν] ≤ δ * ‖t‖^2 := by
    rw [hvar, covarianceDeficit_quad _ _ hμ]
    linarith [variance_nonneg (fun x => ⟪t, x⟫) μ]
  change (∫ z, |L z| ^ 3 ∂ν) ≤ _
  rw [← integral_map (f := fun x : ℝ => |x|^3) (φ := L) (by fun_prop) (by fun_prop),
    IsGaussian.map_eq_gaussianReal L, hmean, centeredGaussian_third,
    Real.coe_toNNReal _ (variance_nonneg _ _)]
  gcongr

/-- A usable bound on the third moment after Gaussian compensation, on either sign. -/
theorem compensated_projection_third (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (δ : ℝ) (hR : (covarianceDeficit δ μ).PosSemidef)
    (t : EuclideanSpace ℝ ι) (ht : Integrable (fun x => |⟪t, x⟫|^3) μ)
    (c : ℝ) (hc : |c| ≤ 1) :
    let ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) (covarianceDeficit δ μ)
    let Z := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => ⟪t, (2⁻¹ : ℝ) • p.1 + c • p.2⟫
    Integrable (fun p => |Z p|^3) (μ.prod ν) ∧
    (∫ p, |Z p|^3 ∂μ.prod ν) ≤ 4 * ((∫ x, |⟪t, x⟫|^3 ∂μ) +
      (Real.sqrt (δ * ‖t‖^2))^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1) := by
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) (covarianceDeficit δ μ)
  let F := fun x : EuclideanSpace ℝ ι => |⟪t, x⟫|^3
  have hν : Integrable F ν := by
    have h : MemLp (fun x : EuclideanSpace ℝ ι => ⟪t, x⟫) 3 ν :=
      (IsGaussian.memLp_id ν 3 (by norm_num)).const_inner t
    simpa [F, Real.norm_eq_abs] using h.integrable_norm_pow' (p := 3)
  have hdom : Integrable (fun p => 4 * (F p.1 + F p.2)) (μ.prod ν) :=
    ((ht.comp_fst ν).add (hν.comp_snd μ)).const_mul _
  have hpt (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
      |⟪t, (2⁻¹ : ℝ) • p.1 + c • p.2⟫| ^ 3 ≤ 4 * (F p.1 + F p.2) := by
    let a := |⟪t, p.1⟫|
    let b := |⟪t, p.2⟫|
    have ha : 0 ≤ a := abs_nonneg _
    have hb : 0 ≤ b := abs_nonneg _
    have hab : |⟪t, (2⁻¹ : ℝ) • p.1 + c • p.2⟫| ≤ a + b := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      apply (abs_add_le _ _).trans
      simp only [abs_mul]
      exact add_le_add (mul_le_of_le_one_left ha (by norm_num)) (mul_le_of_le_one_left hb hc)
    calc
      _ ≤ (a+b)^3 := by gcongr
      _ ≤ 4 * (a^3 + b^3) := by nlinarith [mul_nonneg (sq_nonneg (a-b)) (add_nonneg ha hb)]
  have hZi : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      |⟪t, (2⁻¹ : ℝ) • p.1 + c • p.2⟫| ^ 3) (μ.prod ν) := by
    apply hdom.mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hpt p
  refine ⟨hZi, (integral_mono hZi hdom hpt).trans ?_⟩
  rw [integral_const_mul, integral_add (ht.comp_fst ν) (hν.comp_snd μ),
    integral_fun_fst F, integral_fun_snd F]
  simp only [probReal_univ, one_smul]
  gcongr
  exact compensationNoise_third μ hμ δ hR t

end G54

end ModCompensation

section ModMartingaleCLT

/- # Characteristic functions of discrete martingales -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace G54

/-- Global Taylor remainder for a phase. The constant is uniform in the phase. -/
theorem phase_remainder_le (x : ℝ) :
    ‖Complex.exp (x * Complex.I) - (1 + x * Complex.I - (x : ℂ)^2 / 2)‖ ≤
      4 * |x| ^ 3 := by
  have hnorm : ‖(x : ℂ) * Complex.I‖ = |x| := by simp [Real.norm_eq_abs]
  by_cases hx : |x| ≤ 1
  · have h := Complex.exp_bound (x := (x : ℂ) * Complex.I) (hnorm.trans_le hx) (n := 3)
        (by decide)
    have heq : (∑ m ∈ Finset.range 3, ((x : ℂ) * Complex.I)^m / m.factorial)
        = 1 + x * Complex.I - (x : ℂ)^2 / 2 := by
      norm_num [Finset.sum_range_succ, mul_pow, Complex.I_sq]
      ring
    rw [heq, hnorm] at h
    norm_num [Nat.factorial] at h
    linarith [pow_nonneg (abs_nonneg x) 3]
  · calc
      _ ≤ ‖Complex.exp (x * Complex.I)‖ + ‖1 + x * Complex.I - (x : ℂ)^2 / 2‖ :=
        norm_sub_le _ _
      _ ≤ ‖Complex.exp (x * Complex.I)‖ +
          ((‖(1 : ℂ)‖ + ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ)^2 / 2‖) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ = 1 + ((1 + |x|) + |x|^2 / 2) := by
        simp [norm_pow, Real.norm_eq_abs]
      _ ≤ _ := by
        have hge : 1 ≤ |x| := le_of_not_ge hx
        nlinarith [mul_nonneg (sub_nonneg.mpr hge) (abs_nonneg x),
          mul_nonneg (sub_nonneg.mpr hge) (sq_nonneg |x|)]

/-- Contractive scalar recurrences accumulate at most the sum of their one-step errors. -/
theorem phase_recurrence_bound (a : ℕ → ℂ) (q : ℂ) (b : ℕ → ℝ) (N : ℕ)
    (hzero : a 0 = 1) (hq : ‖q‖ ≤ 1)
    (hstep : ∀ k < N, ‖a (k+1) - a k * q‖ ≤ b k) :
    ‖a N - q^N‖ ≤ ∑ k ∈ Finset.range N, b k := by
  induction N with
  | zero => simp [hzero]
  | succ N ih =>
    calc
      _ = ‖(a (N+1) - a N * q) + (a N - q^N) * q‖ := by
        congr 1
        rw [pow_succ]
        ring
      _ ≤ ‖a (N+1) - a N * q‖ + ‖(a N - q^N) * q‖ := norm_add_le _ _
      _ ≤ b N + ∑ k ∈ Finset.range N, b k := by
        apply add_le_add (hstep _ (Nat.lt_succ_self _))
        rw [norm_mul]
        calc
          _ ≤ ‖a N - q ^ N‖ * 1 := by gcongr
          _ ≤ _ := by simpa using ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
      _ = _ := by rw [Finset.sum_range_succ, add_comm]

/-- A past-measurable phase can be tested against either an integrable scalar random
variable or its constant conditional expectation. -/
private theorem integral_phase_conditional {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {P : Ω → ℂ} {D : Ω → ℝ} {c : ℝ}
    (hP : AEStronglyMeasurable[m] P μ) (hD : Integrable D μ)
    (hbounded : ∀ᵐ ω ∂μ, ‖P ω‖ ≤ 1) (hc : μ[D | m] =ᵐ[μ] fun _ => c) :
    ∫ ω, D ω • P ω ∂μ = c • ∫ ω, P ω ∂μ := by
  have hDP := hD.smul_bdd 1 (hP.mono hm) hbounded
  have hpull := condExp_smul_of_aestronglyMeasurable_right hD hDP hP
  rw [← integral_smul]
  calc
    _ = ∫ ω, μ[D • P | m] ω ∂μ := (integral_condExp hm).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hpull, hc] with ω hω hcω
      simpa [Pi.smul_apply, hcω] using hω

/-- A martingale increment of deterministic conditional variance has a Gaussian one-step
characteristic-function expansion. Only the unconditional third moment enters the error. -/
theorem martingale_phase_step {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {S D : Ω → ℝ} {v : ℝ}
    (hS : Measurable[m] S) (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hmean : μ[D | m] =ᵐ[μ] fun _ => 0)
    (hvariance : μ[fun ω => D ω ^ 2 | m] =ᵐ[μ] fun _ => v) :
    ‖(∫ ω, Complex.exp (((S ω + D ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ ω, Complex.exp ((S ω : ℂ) * Complex.I) ∂μ) * (1 - (v : ℂ)/2)‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂μ := by
  let P := fun ω => Complex.exp ((S ω : ℂ) * Complex.I)
  have hphase : Continuous (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) := by fun_prop
  have hP : AEStronglyMeasurable[m] P μ := (hphase.measurable.comp hS).stronglyMeasurable.aestronglyMeasurable
  have hPn (ω) : ‖P ω‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hPb : ∀ᵐ ω ∂μ, ‖P ω‖ ≤ 1 := ae_of_all _ (fun ω => (hPn ω).le)
  have hPi : Integrable P μ := (integrable_const (1 : ℝ)).mono' (hP.mono hm) hPb
  let L := fun ω => D ω • P ω
  let Q := fun ω => (D ω ^ 2) • P ω
  have hLi : Integrable L μ := hD.smul_bdd 1 (hP.mono hm) hPb
  have hQi : Integrable Q μ := hD2.smul_bdd 1 (hP.mono hm) hPb
  have hL : ∫ ω, L ω ∂μ = 0 := by
    simpa [L] using integral_phase_conditional μ hm hP hD hPb hmean
  have hQ : ∫ ω, Q ω ∂μ = (v : ℂ) * ∫ ω, P ω ∂μ :=
    integral_phase_conditional μ hm hP hD2 hPb hvariance
  let T := fun ω => P ω + L ω * Complex.I - Q ω * (2 : ℂ)⁻¹
  have hTi : Integrable T μ := (hPi.add (hLi.mul_const _)).sub (hQi.mul_const _)
  have hT : ∫ ω, T ω ∂μ = (∫ ω, P ω ∂μ) * (1 - (v : ℂ)/2) := by
    dsimp only [T]
    have hsumI : Integrable (fun ω => P ω + L ω * Complex.I) μ := hPi.add (hLi.mul_const _)
    rw [integral_sub hsumI (hQi.mul_const (2 : ℂ)⁻¹),
      integral_add hPi (hLi.mul_const _), integral_mul_const, integral_mul_const, hL, hQ]
    ring
  have hsum : AEMeasurable (fun ω => S ω + D ω) μ :=
    (hS.mono hm le_rfl).aemeasurable.add hD.aemeasurable
  have hEi : Integrable (fun ω => Complex.exp (((S ω + D ω : ℝ) : ℂ) * Complex.I)) μ := by
    exact (integrable_const (1 : ℝ)).mono'
      (hphase.comp_aestronglyMeasurable hsum.aestronglyMeasurable)
      (ae_of_all _ (fun ω => (Complex.norm_exp_ofReal_mul_I _).le))
  change ‖_ - (∫ ω, P ω ∂μ) * _‖ ≤ _
  rw [← hT, ← integral_sub hEi hTi, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hD3.const_mul 4)
  filter_upwards with ω
  have he : Complex.exp (((S ω + D ω : ℝ) : ℂ) * Complex.I) - T ω =
      P ω * (Complex.exp ((D ω : ℂ) * Complex.I) -
        (1 + (D ω : ℂ) * Complex.I - (D ω : ℂ)^2 / 2)) := by
    simp only [Complex.ofReal_add, add_mul, Complex.exp_add, T, Q, L, P,
      Complex.real_smul, Complex.ofReal_pow]
    ring
  rw [he, norm_mul, hPn, one_mul]
  exact phase_remainder_le _

/-- Finite-time characteristic-function estimate for real projections of a martingale.
The conditional variance of every projected increment is equal to the same scalar. -/
theorem martingale_phase_bound {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (m : ℕ → MeasurableSpace Ω)
    (S D : ℕ → Ω → ℝ) (v : ℝ) (hv : |1 - v / 2| ≤ 1)
    (hzero : S 0 =ᵐ[μ] fun _ => 0)
    (hadd : ∀ k < N, S (k+1) =ᵐ[μ] fun ω => S k ω + D k ω)
    (hm : ∀ k < N, m k ≤ m₀) (hS : ∀ k < N, Measurable[m k] (S k))
    (hD : ∀ k < N, Integrable (D k) μ)
    (hD2 : ∀ k < N, Integrable (fun ω => D k ω ^ 2) μ)
    (hD3 : ∀ k < N, Integrable (fun ω => |D k ω| ^ 3) μ)
    (hmean : ∀ k < N, μ[D k | m k] =ᵐ[μ] fun _ => 0)
    (hvar : ∀ k < N, μ[fun ω => D k ω ^ 2 | m k] =ᵐ[μ] fun _ => v) :
    ‖(∫ ω, Complex.exp ((S N ω : ℂ) * Complex.I) ∂μ) - (1 - (v : ℂ)/2)^N‖ ≤
      4 * ∑ k ∈ Finset.range N, ∫ ω, |D k ω| ^ 3 ∂μ := by
  rw [Finset.mul_sum]
  apply phase_recurrence_bound (fun k => ∫ ω, Complex.exp ((S k ω : ℂ) * Complex.I) ∂μ)
  · calc
      _ = ∫ _ : Ω, (1 : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hzero] with ω hω
        simp [hω]
      _ = 1 := by simp
  · exact_mod_cast (show ‖1 - v / 2‖ ≤ 1 from hv)
  · intro k hk
    have heq : (∫ ω, Complex.exp ((S (k+1) ω : ℂ) * Complex.I) ∂μ) =
        ∫ ω, Complex.exp (((S k ω + D k ω : ℝ) : ℂ) * Complex.I) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hadd k hk] with ω hω
      rw [hω]
    rw [heq]
    exact martingale_phase_step μ (hm k hk) (hS k hk) (hD k hk) (hD2 k hk) (hD3 k hk)
      (hmean k hk) (hvar k hk)

/-- Passing a triangular-array estimate to the Gaussian characteristic-function limit. -/
theorem tendsto_gaussian_phase_of_bound {a : ℕ → ℂ} {e : ℕ → ℝ} (v : ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (h : ∀ᶠ n : ℕ in atTop, ‖a n - (1 - ((v / n : ℝ) : ℂ)/2)^n‖ ≤ e n) :
    Tendsto a atTop (𝓝 (Complex.exp (-(v : ℂ)/2))) := by
  let b := fun n : ℕ => (1 - ((v / n : ℝ) : ℂ)/2)^n
  have hb : Tendsto b atTop (𝓝 (Complex.exp (-(v : ℂ)/2))) := by
    apply (Complex.tendsto_one_add_div_pow_exp (-(v : ℂ)/2)).congr
    intro n
    dsimp [b]
    push_cast
    ring
  have hdiff : Tendsto (fun n => a n - b n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
      (.of_forall fun _ => norm_nonneg _) h
  simpa using hdiff.add hb

/-- Scalar characteristic-function CLT for triangular arrays of martingale increments.
The spaces can vary by row. Apply to the projection of each vector increment onto the
chosen Fourier frequency; its total variance `v` includes the frequency factor. -/
theorem martingale_phase_clt {Ω : ℕ → Type*} [M : ∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (m : ∀ n, ℕ → MeasurableSpace (Ω n)) (S D : ∀ n, ℕ → Ω n → ℝ)
    {v : ℝ} (hv : 0 ≤ v)
    (hzero : ∀ n, S n 0 =ᵐ[μ n] fun _ => 0)
    (hadd : ∀ n k, k < n → S n (k+1) =ᵐ[μ n] fun ω => S n k ω + D n k ω)
    (hm : ∀ n k, k < n → m n k ≤ M n)
    (hS : ∀ n k, k < n → Measurable[m n k] (S n k))
    (hD : ∀ n k, k < n → Integrable (D n k) (μ n))
    (hD2 : ∀ n k, k < n → Integrable (fun ω => D n k ω ^ 2) (μ n))
    (hD3 : ∀ n k, k < n → Integrable (fun ω => |D n k ω| ^ 3) (μ n))
    (hmean : ∀ n k, k < n → (μ n)[D n k | m n k] =ᵐ[μ n] fun _ => 0)
    (hvar : ∀ n k, k < n → (μ n)[fun ω => D n k ω ^ 2 | m n k] =ᵐ[μ n] fun _ => v / n)
    (hsmall : Tendsto (fun n => ∑ k ∈ Finset.range n, ∫ ω, |D n k ω|^3 ∂μ n)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, Complex.exp ((S n n ω : ℂ) * Complex.I) ∂μ n)
      atTop (𝓝 (Complex.exp (-(v : ℂ)/2))) := by
  apply tendsto_gaussian_phase_of_bound (e := fun n =>
    4 * ∑ k ∈ Finset.range n, ∫ ω, |D n k ω|^3 ∂μ n) v
  · simpa using hsmall.const_mul 4
  · have hn : ∀ᶠ n : ℕ in atTop, v + 1 ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (v + 1)
    filter_upwards [hn] with n hn
    have hnpos : 0 < (n : ℝ) := by linarith
    have hq : |1 - v / n / 2| ≤ 1 := by
      have hle : v / n ≤ 1 := (div_le_one hnpos).mpr (by linarith)
      have hge := div_nonneg hv hnpos.le
      rw [abs_le]
      constructor <;> linarith
    exact martingale_phase_bound (μ n) n (m n) (S n) (D n) (v / n) hq
      (hzero n) (hadd n) (hm n) (hS n) (hD n) (hD2 n) (hD3 n) (hmean n) (hvar n)

end G54

end ModMartingaleCLT

section ModCouplingLimit

/- # Weak limits of couplings -/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace G54

private theorem tight_of_convergent_sequence {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {p : ℕ → ProbabilityMeasure E} {q : ProbabilityMeasure E} (hp : Tendsto p atTop (𝓝 q)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ range p} := by
  apply isTightMeasureSet_of_isCompact_closure
  exact hp.isCompact_insert_range.of_isClosed_subset isClosed_closure
    (closure_minimal (subset_insert _ _) hp.isCompact_insert_range.isClosed)

/-- If both coordinates and a continuous image of a sequence of joint laws have weak
limits, some joint law realizes all three limits simultaneously. -/
theorem exists_coupling_of_tendsto {E F T : Type*}
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
    [MetricSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (p : ℕ → ProbabilityMeasure (E × F)) (a : ProbabilityMeasure E) (b : ProbabilityMeasure F)
    (f : E × F → T) (hf : Continuous f) (c : ProbabilityMeasure T)
    (ha : Tendsto (fun k => (p k).map measurable_fst.aemeasurable) atTop (𝓝 a))
    (hb : Tendsto (fun k => (p k).map measurable_snd.aemeasurable) atTop (𝓝 b))
    (hc : Tendsto (fun k => (p k).map hf.measurable.aemeasurable) atTop (𝓝 c)) :
    ∃ π : Measure (E × F), π.map Prod.fst = a ∧ π.map Prod.snd = b ∧ π.map f = c := by
  have ht : IsCompact (closure (range p)) := by
    apply isCompact_closure_of_isTightMeasureSet
    apply IsTightMeasureSet.prodMk
    · apply (tight_of_convergent_sequence ha).subset
      rintro _ ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, rfl⟩
    · apply (tight_of_convergent_sequence hb).subset
      rintro _ ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, rfl⟩
  obtain ⟨π, _, u, hu, hπ⟩ := ht.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  refine ⟨π, ?_, ?_, ?_⟩
  · exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hπ continuous_fst)
      (ha.comp hu.tendsto_atTop))
  · exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hπ continuous_snd)
      (hb.comp hu.tendsto_atTop))
  · exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hπ hf)
      (hc.comp hu.tendsto_atTop))

/-- Lévy's criterion in the product coordinates used by the problem. -/
theorem tendsto_gaussian_of_phases {n : ℕ} (p : ℕ → ProbabilityMeasure (Fin n → ℝ))
    (hp : ∀ v : Fin n → ℝ, Tendsto
      (fun k => ∫ x : Fin n → ℝ, Complex.exp (((∑ i, v i * x i : ℝ) : ℂ) * Complex.I) ∂(p k : Measure _))
      atTop (𝓝 (Complex.exp (-((∑ i, v i ^ 2 : ℝ) : ℂ) / 2)))) :
    Tendsto p atTop (𝓝 (⟨Measure.pi fun _ : Fin n => gaussianReal 0 1, inferInstance⟩ :
      ProbabilityMeasure (Fin n → ℝ))) := by
  let toE := @WithLp.toLp 2 (Fin n → ℝ)
  let ofE := @WithLp.ofLp 2 (Fin n → ℝ)
  have ht : Continuous toE := PiLp.continuous_toLp _ _
  have ho : Continuous ofE := PiLp.continuous_ofLp _ _
  let γ : ProbabilityMeasure (Fin n → ℝ) := ⟨Measure.pi fun _ => gaussianReal 0 1, inferInstance⟩
  have h (v : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun k => charFun ((p k).map ht.measurable.aemeasurable : ProbabilityMeasure _) v)
        atTop (𝓝 (charFun (γ.map ht.measurable.aemeasurable : ProbabilityMeasure _) v)) := by
    change Tendsto (fun k => charFun ((p k : Measure _).map toE) v) atTop
      (𝓝 (charFun ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (WithLp.toLp 2)) v))
    rw [map_pi_eq_stdGaussian, charFun_stdGaussian]
    have he (x : Fin n → ℝ) : inner ℝ (toE x) v = ∑ i, v i * x i := rfl
    have hn : ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, sq]
    simp only [charFun_apply, integral_map (f := fun x : EuclideanSpace ℝ (Fin n) => Complex.exp (((inner ℝ x v : ℝ) : ℂ) * Complex.I)) ht.measurable.aemeasurable (by fun_prop), he]
    simpa [hn, ← Complex.ofReal_pow] using hp (ofE v)
  have h' := ProbabilityMeasure.tendsto_of_tendsto_charFun h
  have h'' := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h' ho
  have e (q : ProbabilityMeasure (Fin n → ℝ)) :
      (q.map ht.measurable.aemeasurable).map ho.measurable.aemeasurable = q := by
    apply Subtype.ext
    change ((q : Measure _).map toE).map ofE = q
    rw [Measure.map_map ho.measurable ht.measurable]
    exact Measure.map_id
  simpa only [e] using h''

/-- A finite-dimensional coupling can be recovered from its two limiting Gaussian
characteristic functions and the weak limit of its translated sum. -/
theorem gaussian_sum_coupling_of_phases {n : ℕ}
    (p : ℕ → ProbabilityMeasure ((Fin n → ℝ) × (Fin n → ℝ)))
    (m : Fin n → ℝ) (μ : ProbabilityMeasure (Fin n → ℝ))
    (hphase : ∀ (f : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)),
      f = Prod.fst ∨ f = Prod.snd → ∀ v : Fin n → ℝ, Tendsto
        (fun k => ∫ q, Complex.exp (((∑ i, v i * f q i : ℝ) : ℂ) * Complex.I) ∂(p k : Measure _))
        atTop (𝓝 (Complex.exp (-((∑ i, v i ^ 2 : ℝ) : ℂ) / 2))))
    (hsum : Tendsto (fun k => (p k).map (f := fun q => m + (q.1 + q.2))
      (measurable_const.add (measurable_fst.add measurable_snd)).aemeasurable) atTop (𝓝 μ)) :
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)),
      π.map Prod.fst = Measure.pi (fun _ => gaussianReal 0 1) ∧
      π.map Prod.snd = Measure.pi (fun _ => gaussianReal 0 1) ∧
      π.map (fun q => m + (q.1 + q.2)) = μ := by
  let γ : ProbabilityMeasure (Fin n → ℝ) := ⟨Measure.pi fun _ => gaussianReal 0 1, inferInstance⟩
  have hmarg (f : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)) (hf : Measurable f)
      (h : f = Prod.fst ∨ f = Prod.snd) :
      Tendsto (fun k => (p k).map hf.aemeasurable) atTop (𝓝 γ) := by
    apply tendsto_gaussian_of_phases
    intro v
    have hph : Continuous (fun x : Fin n → ℝ => Complex.exp (((∑ i, v i * x i : ℝ) : ℂ) * Complex.I)) := by fun_prop
    simpa only [ProbabilityMeasure.toMeasure_map, integral_map hf.aemeasurable hph.aestronglyMeasurable] using
      (show Tendsto _ _ _ from hphase f h v)
  exact exists_coupling_of_tendsto p γ γ _ (continuous_const.add (continuous_fst.add continuous_snd)) μ
    (hmarg Prod.fst measurable_fst (Or.inl rfl)) (hmarg Prod.snd measurable_snd (Or.inr rfl)) hsum

end G54

end ModCouplingLimit

section ModWalk

/- # Iterating compensated kernels and telescoping their vector sum -/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped RealInnerProductSpace ProbabilityTheory

namespace G54

variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]

/-- State consists of the current site and the two partial sums. -/
abbrev WalkState (α : Type*) (ι : Type*) := α × EuclideanSpace ℝ ι × EuclideanSpace ℝ ι

/-- One step draws the new site and a noise vector. It then splits the change of
the vector potential and adds opposite copies of the noise to its two halves. -/
noncomputable def walkUpdate (f g : α → EuclideanSpace ℝ ι)
    (p : WalkState α ι × (α × EuclideanSpace ℝ ι)) : WalkState α ι :=
  let q := compensatedPair (g p.2.1 - f p.1.1, p.2.2)
  (p.2.1, p.1.2.1 + q.1, p.1.2.2 + q.2)

theorem measurable_walkUpdate {f g : α → EuclideanSpace ℝ ι} (hf : Measurable f)
    (hg : Measurable g) : Measurable (walkUpdate f g) := by
  unfold walkUpdate compensatedPair
  fun_prop

/-- Push the current joint law through one fresh transition. -/
noncomputable def walkStep (ρ : Measure (WalkState α ι))
    (T : Kernel α (α × EuclideanSpace ℝ ι)) (f g : α → EuclideanSpace ℝ ι) :
    Measure (WalkState α ι) :=
  (ρ ⊗ₘ T.comap Prod.fst measurable_fst).map (walkUpdate f g)

theorem walkStep_prob {ρ : Measure (WalkState α ι)} [IsProbabilityMeasure ρ]
    (T : Kernel α (α × EuclideanSpace ℝ ι)) [IsMarkovKernel T]
    {f g : α → EuclideanSpace ℝ ι} (hf : Measurable f) (hg : Measurable g) :
    IsProbabilityMeasure (walkStep ρ T f g) :=
  Measure.isProbabilityMeasure_map (measurable_walkUpdate hf hg).aemeasurable

/-- Finite discrete walk started from a deterministic site, with zero partial sums. -/
noncomputable def walkLaw (x₀ : α) (T : ℕ → Kernel α (α × EuclideanSpace ℝ ι))
    (M : ℕ → α → EuclideanSpace ℝ ι) : ℕ → Measure (WalkState α ι)
  | 0 => Measure.dirac (x₀, 0, 0)
  | k+1 => walkStep (walkLaw x₀ T M k) (T k) (M k) (M (k+1))

theorem walkLaw_prob (x₀ : α) (T : ℕ → Kernel α (α × EuclideanSpace ℝ ι))
    [∀ k, IsMarkovKernel (T k)] (M : ℕ → α → EuclideanSpace ℝ ι)
    (hM : ∀ k, Measurable (M k)) (k : ℕ) : IsProbabilityMeasure (walkLaw x₀ T M k) := by
  induction k with
  | zero => unfold walkLaw; infer_instance
  | succ k ih => exact walkStep_prob (T k) (hM k) (hM (k+1))

/-- The site marginal evolves by the site marginal of the transition kernel. -/
theorem walkStep_fst (ρ : Measure (WalkState α ι)) [IsProbabilityMeasure ρ]
    (T : Kernel α (α × EuclideanSpace ℝ ι)) [IsMarkovKernel T]
    {f g : α → EuclideanSpace ℝ ι} (hf : Measurable f) (hg : Measurable g) :
    (walkStep ρ T f g).map Prod.fst = T.fst ∘ₘ (ρ.map Prod.fst) := by
  ext s hs
  rw [walkStep, Measure.map_map measurable_fst (measurable_walkUpdate hf hg)]
  rw [Measure.map_apply (measurable_fst.comp (measurable_walkUpdate hf hg)) hs,
    Measure.compProd_apply (measurable_fst.comp (measurable_walkUpdate hf hg) hs),
    Measure.bind_apply hs T.fst.aemeasurable, lintegral_map (T.fst.measurable_coe hs) measurable_fst]
  congr 1
  funext p
  change T p.1 (Prod.fst ⁻¹' s) = T.fst p.1 s
  rw [Kernel.fst_apply' _ _ hs]
  rfl

/-- Mass is concentrated on the telescoping identity at each time. -/
theorem walkLaw_sum (x₀ : α) (T : ℕ → Kernel α (α × EuclideanSpace ℝ ι))
    [∀ k, IsMarkovKernel (T k)] (M : ℕ → α → EuclideanSpace ℝ ι)
    (hM : ∀ k, Measurable (M k)) (k : ℕ) :
    ∀ᵐ p ∂walkLaw x₀ T M k, p.2.1 + p.2.2 = M k p.1 - M 0 x₀ := by
  induction k with
  | zero =>
    rw [walkLaw]
    apply (ae_dirac_iff (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
    simp
  | succ k ih =>
    let ρ := walkLaw x₀ T M k
    have : IsProbabilityMeasure ρ := walkLaw_prob _ _ _ hM _
    let η : Kernel (WalkState α ι) (α × EuclideanSpace ℝ ι) := (T k).comap Prod.fst measurable_fst
    change ∀ᵐ p ∂(ρ ⊗ₘ η).map (walkUpdate (M k) (M (k+1))), _
    rw [ae_map_iff (measurable_walkUpdate (hM k) (hM (k+1))).aemeasurable
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))]
    apply Measure.ae_compProd_of_ae_ae
    · have hmSet : MeasurableSet {p : WalkState α ι | p.2.1 + p.2.2 = M (k+1) p.1 - M 0 x₀} :=
        measurableSet_eq_fun (by fun_prop) (by fun_prop)
      exact measurable_walkUpdate (hM k) (hM (k+1)) hmSet
    · filter_upwards [ih] with p hp
      filter_upwards with q
      change (p.2.1 + (compensatedPair _).1) + (p.2.2 + (compensatedPair _).2) = _
      rw [add_add_add_comm, hp, compensatedPair_sum]
      change M k p.1 - M 0 x₀ + (M (k+1) q.1 - M k p.1) = M (k+1) q.1 - M 0 x₀
      abel

/-- The total-site distribution at any specified time can be supplied by an independent
induction on the site transition kernels. -/
theorem walkLaw_fst (x₀ : α) (T : ℕ → Kernel α (α × EuclideanSpace ℝ ι))
    [∀ k, IsMarkovKernel (T k)] (M : ℕ → α → EuclideanSpace ℝ ι)
    (hM : ∀ k, Measurable (M k)) (laws : ℕ → Measure α) (hz : laws 0 = Measure.dirac x₀)
    {N : ℕ} (hnext : ∀ k < N, (T k).fst ∘ₘ laws k = laws (k+1)) :
    (walkLaw x₀ T M N).map Prod.fst = laws N := by
  induction N with
  | zero => simp [walkLaw, hz, Measure.map_dirac' measurable_fst]
  | succ k ih =>
    have := walkLaw_prob x₀ T M hM k
    rw [walkLaw, walkStep_fst _ _ (hM k) (hM (k+1)), ih (fun j hj => hnext j (Nat.lt_succ_of_lt hj))]
    exact hnext _ (Nat.lt_succ_self k)

/-- A linear probe of the pair increment; a probe of the first or second coordinate
recovers the corresponding marginal characteristic function. -/
noncomputable def walkIncrement (L : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] ℝ)
    (f g : α → EuclideanSpace ℝ ι) (x : α) (q : α × EuclideanSpace ℝ ι) : ℝ :=
  L (compensatedPair (g q.1 - f x, q.2))

/-- A single transition only needs ordinary scalar moments on its conditional law.
The past phase is arbitrary and constant during that transition. -/
theorem phase_step_fixed {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : ℝ) (D : Ω → ℝ) (v : ℝ) (hD : MemLp D 2 μ)
    (h3 : Integrable (fun q => |D q|^3) μ) (hz : ∫ q, D q ∂μ = 0)
    (hv : Var[D; μ] = v) :
    ‖(∫ q, Complex.exp (((s + D q : ℝ) : ℂ) * Complex.I) ∂μ) -
      Complex.exp ((s : ℂ) * Complex.I) * (1 - (v : ℂ)/2)‖ ≤ 4 * ∫ q, |D q|^3 ∂μ := by
  have h2 : ∫ q, D q ^ 2 ∂μ = v := by simpa [variance_eq_sub hD, hz] using hv
  simpa using martingale_phase_step μ (m := ⊥) bot_le (S := fun _ => s) measurable_const
    (hD.integrable (by norm_num)) (hD.integrable_sq) h3
    (by simp [hz]) (by simp [h2])

/-- Lift a conditional Fourier estimate to the updated joint law; this avoids a
separate construction of the path-space filtration. -/
theorem walkStep_phase_bound (ρ : Measure (WalkState α ι)) [IsProbabilityMeasure ρ]
    (T : Kernel α (α × EuclideanSpace ℝ ι)) [IsMarkovKernel T]
    {f g : α → EuclideanSpace ℝ ι} (hf : Measurable f) (hg : Measurable g)
    (L : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] ℝ) (v b : ℝ)
    (hlocal : ∀ x s,
      ‖(∫ q, Complex.exp (((s + walkIncrement L f g x q : ℝ) : ℂ) * Complex.I) ∂T x) -
        Complex.exp ((s : ℂ) * Complex.I) * (1 - (v : ℂ)/2)‖ ≤ b) :
    let P := fun p : WalkState α ι => Complex.exp ((L p.2 : ℂ) * Complex.I)
    ‖(∫ p, P p ∂walkStep ρ T f g) - (∫ p, P p ∂ρ) * (1 - (v : ℂ)/2)‖ ≤ b := by
  let P := fun p : WalkState α ι => Complex.exp ((L p.2 : ℂ) * Complex.I)
  let η : Kernel (WalkState α ι) (α × EuclideanSpace ℝ ι) := T.comap Prod.fst measurable_fst
  have hP : Measurable P := by dsimp [P]; fun_prop
  have hU := measurable_walkUpdate hf hg
  have hE : Integrable (fun p => P (walkUpdate f g p)) (ρ ⊗ₘ η) :=
    (integrable_const (1 : ℝ)).mono' (hP.comp hU).aestronglyMeasurable
      (ae_of_all _ fun _ => (Complex.norm_exp_ofReal_mul_I _).le)
  have hPi : Integrable P ρ := (integrable_const (1 : ℝ)).mono' hP.aestronglyMeasurable
    (ae_of_all _ fun _ => (Complex.norm_exp_ofReal_mul_I _).le)
  have hEi : Integrable (fun p => ∫ q, P (walkUpdate f g (p, q)) ∂η p) ρ := hE.integral_compProd
  change ‖(∫ p, P p ∂(ρ ⊗ₘ η).map (walkUpdate f g)) - (∫ p, P p ∂ρ) * _‖ ≤ _
  rw [integral_map hU.aemeasurable hP.aestronglyMeasurable, Measure.integral_compProd hE,
    ← integral_mul_const, ← integral_sub hEi (hPi.mul_const (1 - (v : ℂ)/2))]
  refine (norm_integral_le_of_norm_le_const (C := b) (μ := ρ) ?_).trans_eq (by simp)
  apply ae_of_all
  intro p
  have heq (q : α × EuclideanSpace ℝ ι) : P (walkUpdate f g (p, q)) =
      Complex.exp (((L p.2 + walkIncrement L f g p.1 q : ℝ) : ℂ) * Complex.I) := by
    dsimp only [P]
    change Complex.exp ((L (p.2 + compensatedPair _) : ℂ) * Complex.I) = _
    rw [map_add]
    rfl
  simpa only [heq] using! hlocal p.1 (L p.2)

/-- Iterate uniform one-step conditional characteristic-function bounds for one linear
probe. The bound holds for the terminal law of the explicitly constructed walk. -/
theorem walkLaw_phase_bound (x₀ : α) (T : ℕ → Kernel α (α × EuclideanSpace ℝ ι))
    [∀ k, IsMarkovKernel (T k)] (M : ℕ → α → EuclideanSpace ℝ ι)
    (hM : ∀ k, Measurable (M k)) (L : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] ℝ)
    (N : ℕ) (v : ℝ) (b : ℕ → ℝ) (hv : |1 - v / 2| ≤ 1)
    (hlocal : ∀ k < N, ∀ x s,
      ‖(∫ q, Complex.exp (((s + walkIncrement L (M k) (M (k+1)) x q : ℝ) : ℂ) * Complex.I) ∂T k x) -
        Complex.exp ((s : ℂ) * Complex.I) * (1 - (v : ℂ)/2)‖ ≤ b k) :
    ‖(∫ p, Complex.exp ((L p.2 : ℂ) * Complex.I) ∂walkLaw x₀ T M N) -
      (1 - (v : ℂ)/2)^N‖ ≤ ∑ k ∈ Finset.range N, b k := by
  apply phase_recurrence_bound (fun k =>
    ∫ p, Complex.exp ((L p.2 : ℂ) * Complex.I) ∂walkLaw x₀ T M k)
  · rw [walkLaw, integral_dirac' _ _ (by fun_prop)]
    change Complex.exp ((L 0 : ℂ) * Complex.I) = 1
    simp
  · exact_mod_cast (show ‖1 - v/2‖ ≤ 1 from hv)
  · intro k hk
    have := walkLaw_prob x₀ T M hM k
    exact walkStep_phase_bound _ (T k) (hM k) (hM (k+1)) L v (b k) (hlocal k hk)

/-- A single linear probe handles either marginal. -/
noncomputable def walkProbe (first : Bool) (v : EuclideanSpace ℝ ι) :
    (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] ℝ :=
  (innerSL ℝ v).comp (if first then .fst ℝ _ _ else .snd ℝ _ _)

@[simp] theorem walkProbe_apply_true (t : EuclideanSpace ℝ ι)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : walkProbe true t p = ⟪t, p.1⟫ := rfl

@[simp] theorem walkProbe_apply_false (t : EuclideanSpace ℝ ι)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : walkProbe false t p = ⟪t, p.2⟫ := rfl

/-- A compensated site transition satisfies the local characteristic-function estimate
needed in `walkLaw_phase_bound`, in both marginal directions. -/
theorem walkProduct_phase_bound [DecidableEq ι] (P : Measure α) [IsProbabilityMeasure P]
    (f g : α → EuclideanSpace ℝ ι) (hg : Measurable g) (x : α) (δ : ℝ)
    (first : Bool) (t : EuclideanSpace ℝ ι) (s b₃ : ℝ) :
    let μ := P.map (fun y => g y - f x)
    let R := covarianceDeficit δ μ
    let ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) R
    MemLp id 2 μ → (∫ d, d ∂μ) = 0 → R.PosSemidef →
    Integrable (fun d => |⟪t, d⟫|^3) μ → (∫ d, |⟪t, d⟫|^3 ∂μ) ≤ b₃ →
    ‖(∫ q, Complex.exp (((s + walkIncrement (walkProbe first t) f g x q : ℝ) : ℂ) *
      Complex.I) ∂P.prod ν) - Complex.exp ((s : ℂ) * Complex.I) * (1 - ((δ * ‖t‖^2 : ℝ) : ℂ)/2)‖ ≤
      16 * (b₃ + (Real.sqrt (δ * ‖t‖^2))^3 * ∫ u : ℝ, |u|^3 ∂gaussianReal 0 1) := by
  intro μ R ν hμ hm hR ht hb
  let D := fun y => g y - f x
  have hD : Measurable D := hg.sub measurable_const
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hD.aemeasurable
  let c : ℝ := if first then 1 else -1
  have hc : c ^ 2 = 1 := by cases first <;> norm_num [c]
  have hac : |c| ≤ 1 := by cases first <;> norm_num [c]
  let Z := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => ⟪t, (2⁻¹ : ℝ) • p.1 + c • p.2⟫
  have hZ : Measurable Z := by dsimp only [Z]; fun_prop
  have hZ2 : MemLp Z 2 (μ.prod ν) := by
    have hν : MemLp id 2 ν := IsGaussian.memLp_two_id
    simpa only [Z, inner_add_right, real_inner_smul_right, Pi.add_def, id_eq] using
      (((hμ.const_inner t).comp_fst ν).const_mul (2⁻¹ : ℝ)).add
        (((hν.const_inner t).comp_snd μ).const_mul c)
  obtain ⟨hmean, hvar⟩ := compensated_projection_moments μ hμ hm hR t c hc
  have hv : Var[Z; μ.prod ν] = δ * ‖t‖^2 := by
    change Var[Z; μ.prod ν] = (4⁻¹ : ℝ) * Var[fun x => ⟪t, x⟫; μ] + t ⬝ᵥ R *ᵥ t at hvar
    rw [hvar, covarianceDeficit_quad δ μ hμ]
    ring
  obtain ⟨hZ3,hthird⟩ := compensated_projection_third μ hμ δ hR t ht c hac
  have hbound := phase_step_fixed (μ.prod ν) s Z (δ * ‖t‖^2) hZ2 hZ3 hmean hv
  have hmap : (P.prod ν).map (Prod.map D id) = μ.prod ν := by
    simpa [μ, D] using (Measure.map_prod_map P ν hD measurable_id).symm
  have he (q) : walkIncrement (walkProbe first t) f g x q = Z (Prod.map D id q) := by
    cases first <;> simp [walkIncrement, compensatedPair, Z, c, D, sub_eq_add_neg]
  have hfun : (fun q => Complex.exp (((s + walkIncrement (walkProbe first t) f g x q : ℝ) : ℂ) *
      Complex.I)) = (fun p => Complex.exp (((s + Z p : ℝ) : ℂ) * Complex.I)) ∘ Prod.map D id := by
    funext q
    rw [he]; rfl
  rw [hfun]
  simp only [Function.comp_def]
  rw [← integral_map (φ := Prod.map D id) (hD.prodMap measurable_id).aemeasurable
    (f := fun p => Complex.exp (((s + Z p : ℝ) : ℂ) * Complex.I)) (by fun_prop), hmap]
  apply hbound.trans
  calc
    _ ≤ 4 * (4 * ((∫ d, |⟪t, d⟫|^3 ∂μ) + _)) := mul_le_mul_of_nonneg_left hthird (by norm_num)
    _ ≤ 16 * (b₃ + _) := by linarith

end G54

end ModWalk

section ModBridgeMoments

/- # Compensated discrete Gaussian bridge transitions -/

open MeasureTheory ProbabilityTheory WithLp Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace G54

noncomputable def bridgeVector {n : ℕ} (ψ : (Fin n → ℝ) → ℝ) (t : ℝ≥0)
    (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) := toLp 2 (bridgeMean ψ t x)

theorem measurable_bridgeVector {n : ℕ} (ψ : (Fin n → ℝ) → ℝ) (t : ℝ≥0) :
    Measurable (bridgeVector ψ t) :=
  (PiLp.continuous_toLp _ _).measurable.comp (measurable_bridgeMean ψ t)

/-- Distribution of the change in posterior mean after one site transition. -/
noncomputable def bridgeDisplacement {n : ℕ} (ψ : (Fin n → ℝ) → ℝ) (δ t : ℝ≥0) :
    Kernel (Fin n → ℝ) (EuclideanSpace ℝ (Fin n)) :=
  (Kernel.id ×ₖ bridgeStep (potentialWeight ψ) δ t).map
    (fun p => bridgeVector ψ t p.2 - bridgeVector ψ (δ+t) p.1)

theorem bridgeDisplacement_apply {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ z w, |ψ z - ψ w| ≤ L * ‖z-w‖) (δ t : ℝ≥0) (x : Fin n → ℝ) :
    bridgeDisplacement ψ δ t x = (bridgeStep (potentialWeight ψ) δ t x).map
      (fun y => bridgeVector ψ t y - bridgeVector ψ (δ+t) x) := by
  have := bridgeStep_markov hc hL δ t
  have hm : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      bridgeVector ψ t p.2 - bridgeVector ψ (δ+t) p.1) := ((measurable_bridgeVector ψ t).comp measurable_snd).sub
    ((measurable_bridgeVector ψ (δ+t)).comp measurable_fst)
  rw [bridgeDisplacement, Kernel.map_apply _ hm, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hm measurable_prodMk_left]
  rfl

theorem bridgeDisplacement_markov {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
    (hc : Continuous ψ) (hL : ∀ z w, |ψ z - ψ w| ≤ L * ‖z-w‖) (δ t : ℝ≥0) :
    IsMarkovKernel (bridgeDisplacement ψ δ t) where
  isProbabilityMeasure x := by
    have := bridgeStep_markov hc hL δ t
    rw [bridgeDisplacement_apply hc hL]
    exact Measure.isProbabilityMeasure_map ((measurable_bridgeVector ψ t).sub measurable_const).aemeasurable

section
variable {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {L : ℝ}
  (hcv : ConvexOn ℝ univ ψ) (hc : Continuous ψ) (hL : ∀ z w, |ψ z - ψ w| ≤ L * ‖z-w‖)

include hcv hc hL

theorem bridgeVector_memLp (δ t : ℝ≥0) (x : Fin n → ℝ) (p : ℝ≥0) :
    MemLp (bridgeVector ψ t) p (bridgeStep (potentialWeight ψ) δ t x) := by
  apply memLp_piLp_iff.mpr
  rw [bridgeStep_eq_affine_tilt hc hL]
  exact (affine_step_memLp (bridgeLogWeight ψ t) (bridgeLogWeight_concave hcv hc hL t)
    (bridgeLogWeight_lipschitz hc hL t) (bridgeMean ψ t) (bridgeMean_nonexpansive hcv hc hL t)
    δ x p).eval

theorem bridgeDisplacement_memLp (δ t : ℝ≥0) (x : Fin n → ℝ) (p : ℝ≥0) :
    MemLp id p (bridgeDisplacement ψ δ t x) := by
  have := bridgeStep_markov hc hL δ t
  rw [bridgeDisplacement_apply hc hL]
  apply (memLp_map_measure_iff (by fun_prop)
    ((measurable_bridgeVector ψ t).sub (measurable_const (a := bridgeVector ψ (δ+t) x))).aemeasurable).mpr
  exact (bridgeVector_memLp hcv hc hL δ t x p).sub (memLp_const _)

theorem bridgeVector_integral (δ t : ℝ≥0) (x : Fin n → ℝ) :
    (∫ y, bridgeVector ψ t y ∂bridgeStep (potentialWeight ψ) δ t x) = bridgeVector ψ (δ+t) x := by
  have hi : Integrable (bridgeVector ψ t) (bridgeStep (potentialWeight ψ) δ t x) :=
    memLp_one_iff_integrable.mp (bridgeVector_memLp hcv hc hL δ t x 1)
  ext i
  rw [eval_integral_piLp hi.eval_piLp]
  exact bridgeMean_tower hc hL δ t x i

theorem bridgeDisplacement_integral (δ t : ℝ≥0) (x : Fin n → ℝ) :
    (∫ y, y ∂bridgeDisplacement ψ δ t x) = 0 := by
  have := bridgeStep_markov hc hL δ t
  have hi : Integrable (bridgeVector ψ t) (bridgeStep (potentialWeight ψ) δ t x) :=
    memLp_one_iff_integrable.mp (bridgeVector_memLp hcv hc hL δ t x 1)
  have hd : Measurable (fun y => bridgeVector ψ t y - bridgeVector ψ (δ+t) x) :=
    (measurable_bridgeVector ψ t).sub measurable_const
  rw [bridgeDisplacement_apply hc hL, integral_map hd.aemeasurable
    (show AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) => y) _ from measurable_id.aestronglyMeasurable),
    integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul, bridgeVector_integral hcv hc hL,
    sub_self]

theorem bridgeDisplacement_projected_moments (δ t : ℝ≥0) (x : Fin n → ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    Var[fun d => ⟪v,d⟫; bridgeDisplacement ψ δ t x] ≤ (δ : ℝ) * ‖v‖^2 ∧
    (∫ d, |⟪v,d⟫|^3 ∂bridgeDisplacement ψ δ t x) ≤ 12 * Real.exp 1 * (Real.sqrt (δ : ℝ) * ‖v‖)^3 := by
  let P := bridgeStep (potentialWeight ψ) δ t x
  let M := bridgeVector ψ t
  let m := bridgeVector ψ (δ+t) x
  let U := fun y => ⟪v, M y⟫
  have := bridgeStep_markov hc hL δ t
  have : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure (bridgeStep _ _ _ _))
  have hU : Measurable U := measurable_const.inner (measurable_bridgeVector ψ t)
  have hi : Integrable M P := memLp_one_iff_integrable.mp (bridgeVector_memLp hcv hc hL δ t x 1)
  have hcoord (y) : U y = ∑ i, v i * bridgeMean ψ t y i := by
    simp [U,M,bridgeVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hnorm : ∑ i, v i ^ 2 = ‖v‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq v).symm
  have hm : (∫ z, U z ∂P) = ⟪v,m⟫ := by
    change (∫ z, (innerSL ℝ v) (M z) ∂P) = _
    rw [ContinuousLinearMap.integral_comp_comm _ hi, bridgeVector_integral hcv hc hL]
    rfl
  have hs := affine_step_projection_moments (bridgeLogWeight ψ t) (bridgeLogWeight_concave hcv hc hL t)
    (bridgeLogWeight_lipschitz hc hL t) (bridgeMean ψ t) (bridgeMean_nonexpansive hcv hc hL t) δ x (ofLp v)
  dsimp only at hs
  rw [bridgeDisplacement_apply hc hL]
  have hD : Measurable (fun y => M y - m) := (measurable_bridgeVector ψ t).sub measurable_const
  rw [variance_map (by fun_prop) hD.aemeasurable, integral_map hD.aemeasurable (by fun_prop)]
  change Var[fun y => ⟪v, M y - m⟫; P] ≤ _ ∧ (∫ y, |⟪v, M y - m⟫|^3 ∂P) ≤ _
  simp_rw [inner_sub_right]
  rw [variance_sub_const hU.aestronglyMeasurable]
  change Var[U; P] ≤ _ ∧ (∫ y, |U y - ⟪v,m⟫|^3 ∂P) ≤ _
  rw [← hm, show P = _ from bridgeStep_eq_affine_tilt hc hL δ t x]
  rw [funext hcoord]
  simpa only [gaussianIncrements, hnorm, Real.sqrt_sq (norm_nonneg v)] using hs

theorem bridgeDeficit_posSemidef (δ t : ℝ≥0) (x : Fin n → ℝ) :
    (covarianceDeficit δ (bridgeDisplacement ψ δ t x)).PosSemidef := by
  have := bridgeDisplacement_markov hc hL δ t
  apply covarianceDeficit_posSemidef _ _ (bridgeDisplacement_memLp hcv hc hL δ t x 2)
  intro v
  apply (bridgeDisplacement_projected_moments hcv hc hL δ t x v).1.trans
  nlinarith only [mul_nonneg δ.coe_nonneg (sq_nonneg ‖v‖)]

/-- Sample the next bridge site and, independently conditional on the present site,
the Gaussian compensation needed by the two marginal walks. -/
noncomputable def bridgeCompensatedStep (δ t : ℝ≥0) :
    Kernel (Fin n → ℝ) ((Fin n → ℝ) × EuclideanSpace ℝ (Fin n)) := by
  have := bridgeDisplacement_markov hc hL δ t
  let D := bridgeDisplacement ψ δ t
  let R := fun x => covarianceDeficit (δ : ℝ) (D x)
  have hme (i j : Fin n) : Measurable (fun x => R x i j) :=
    measurable_covarianceDeficit_entry D (fun x => bridgeDisplacement_memLp hcv hc hL δ t x 2) δ i j
  exact (bridgeStep (potentialWeight ψ) δ t).prod
    (compensationNoiseKernel R hme (bridgeDeficit_posSemidef hcv hc hL δ t))

theorem bridgeCompensatedStep_markov (δ t : ℝ≥0) :
    IsMarkovKernel (bridgeCompensatedStep hcv hc hL δ t) := by
  have := bridgeStep_markov hc hL δ t
  unfold bridgeCompensatedStep
  infer_instance

theorem bridgeCompensatedStep_fst (δ t : ℝ≥0) :
    (bridgeCompensatedStep hcv hc hL δ t).fst = bridgeStep (potentialWeight ψ) δ t := by
  have := bridgeStep_markov hc hL δ t
  unfold bridgeCompensatedStep
  exact Kernel.fst_prod _ _

theorem bridgeCompensatedStep_apply (δ t : ℝ≥0) (x : Fin n → ℝ) :
    bridgeCompensatedStep hcv hc hL δ t x = (bridgeStep (potentialWeight ψ) δ t x).prod
      (multivariateGaussian 0 (covarianceDeficit δ (bridgeDisplacement ψ δ t x))) := by
  have := bridgeStep_markov hc hL δ t
  unfold bridgeCompensatedStep
  exact Kernel.prod_apply _ _ _

theorem bridgeCompensatedStep_phase (δ t : ℝ≥0) (first : Bool) (v : EuclideanSpace ℝ (Fin n))
    (x : Fin n → ℝ) (s : ℝ) :
    ‖(∫ q, Complex.exp (((s + walkIncrement (walkProbe first v) (bridgeVector ψ (δ+t))
      (bridgeVector ψ t) x q : ℝ) : ℂ) * Complex.I) ∂bridgeCompensatedStep hcv hc hL δ t x) -
      Complex.exp ((s : ℂ) * Complex.I) * (1 - (((δ:ℝ) * ‖v‖^2 : ℝ) : ℂ)/2)‖ ≤
      (16 * (12 * Real.exp 1 + ∫ u : ℝ, |u|^3 ∂gaussianReal 0 1) * ‖v‖^3) *
        (Real.sqrt (δ:ℝ))^3 := by
  have := bridgeStep_markov hc hL δ t
  have := bridgeDisplacement_markov hc hL δ t
  let P := bridgeStep (potentialWeight ψ) δ t x
  let μ := bridgeDisplacement ψ δ t x
  have hμ : MemLp id 2 μ := bridgeDisplacement_memLp hcv hc hL δ t x 2
  have hm : (∫ d, d ∂μ) = 0 := bridgeDisplacement_integral hcv hc hL δ t x
  have ht : Integrable (fun d => |⟪v,d⟫|^3) μ := by
    have hh : MemLp (fun d => ⟪v,d⟫) 3 μ := (bridgeDisplacement_memLp hcv hc hL δ t x 3).const_inner v
    simpa only [Real.norm_eq_abs] using hh.integrable_norm_pow' (p := 3)
  have h := walkProduct_phase_bound P (bridgeVector ψ (δ+t)) (bridgeVector ψ t)
    (measurable_bridgeVector ψ t) x δ first v s (12 * Real.exp 1 * (Real.sqrt (δ:ℝ) * ‖v‖)^3)
  dsimp only at h
  rw [← bridgeDisplacement_apply hc hL] at h
  have hh := h hμ hm (bridgeDeficit_posSemidef hcv hc hL δ t x) ht
    (bridgeDisplacement_projected_moments hcv hc hL δ t x v).2
  rw [bridgeCompensatedStep_apply]
  apply hh.trans_eq
  rw [Real.sqrt_mul δ.coe_nonneg, Real.sqrt_sq (norm_nonneg v)]
  ring

end

end G54

end ModBridgeMoments

section ModWalkLimit

/- # From a triangular array of compensated walks to a Gaussian sum coupling -/

open MeasureTheory ProbabilityTheory Filter Topology WithLp
open scoped NNReal RealInnerProductSpace

namespace G54

/-- If the two partial sums of each row have the prescribed one-step Fourier estimates
and the translated terminal sum has law `μ`, a single coupling realizes all three laws. -/
theorem gaussian_sum_of_walk_bounds {n : ℕ} (m : Fin n → ℝ) (μ : ProbabilityMeasure (Fin n → ℝ))
    (T : ℕ → ℕ → Kernel (Fin n → ℝ) ((Fin n → ℝ) × EuclideanSpace ℝ (Fin n)))
    [∀ N k, IsMarkovKernel (T N k)] (M : ℕ → ℕ → (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
    (hM : ∀ N k, Measurable (M N k))
    (hstart : ∀ N, 0 < N → M N 0 0 = toLp 2 m)
    (hend : ∀ N, 0 < N → ∀ x, M N N x = toLp 2 x)
    (hsite : ∀ N, 0 < N → (walkLaw 0 (T N) (M N) N).map Prod.fst = μ)
    (hlocal : ∀ (b : Bool) (v : EuclideanSpace ℝ (Fin n)), ∃ C : ℝ,
      ∀ N, 0 < N → ∀ k < N, ∀ x s,
        ‖(∫ q, Complex.exp (((s + walkIncrement (walkProbe b v) (M N k) (M N (k+1)) x q : ℝ) : ℂ) *
          Complex.I) ∂T N k x) - Complex.exp ((s : ℂ) * Complex.I) *
            (1 - ((((gridStep N : ℝ) * ‖v‖^2 : ℝ) : ℂ)/2))‖ ≤ C * (Real.sqrt (gridStep N : ℝ))^3) :
    ∃ π : Measure ((Fin n → ℝ) × (Fin n → ℝ)), π.map Prod.fst = gaussianIncrements n 1 ∧
      π.map Prod.snd = gaussianIncrements n 1 ∧ π.map (fun q => m + (q.1 + q.2)) = μ := by
  let ρ := fun N => walkLaw 0 (T N) (M N) N
  have hρ N : IsProbabilityMeasure (ρ N) := walkLaw_prob _ _ _ (hM N) _
  let R := fun p : WalkState (Fin n → ℝ) (Fin n) => (ofLp p.2.1, ofLp p.2.2)
  have hR : Measurable R := by
    exact ((PiLp.continuous_ofLp 2 _).measurable.comp (measurable_fst.comp measurable_snd)).prodMk
      ((PiLp.continuous_ofLp 2 _).measurable.comp (measurable_snd.comp measurable_snd))
  let p : ℕ → ProbabilityMeasure ((Fin n → ℝ) × (Fin n → ℝ)) := fun N =>
    ProbabilityMeasure.map ⟨ρ N, hρ N⟩ hR.aemeasurable
  have hproj (b : Bool) (v : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun N => ∫ z, Complex.exp (((walkProbe b v) z.2 : ℂ) * Complex.I) ∂ρ N)
        atTop (𝓝 (Complex.exp (-((‖v‖^2 : ℝ) : ℂ) / 2))) := by
    obtain ⟨C, hC⟩ := hlocal b v
    apply tendsto_gaussian_phase_of_bound _ (tendsto_gridError C)
    have ht : Tendsto (fun N => (gridStep N : ℝ) * ‖v‖^2) atTop (𝓝 0) := by
      simpa using tendsto_gridStep.mul_const (‖v‖^2)
    filter_upwards [eventually_gt_atTop 0, ht.eventually_le_const (by norm_num : (0 : ℝ) < 2)] with N hN hle
    have hv : |1 - ((gridStep N : ℝ) * ‖v‖^2)/2| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by nlinarith [mul_nonneg (gridStep N).2 (sq_nonneg ‖v‖)]⟩
    have hB := walkLaw_phase_bound 0 (T N) (M N) (hM N) (walkProbe b v) N
      ((gridStep N : ℝ) * ‖v‖^2) (fun _ => C * (Real.sqrt (gridStep N : ℝ))^3) hv (hC N hN)
    simpa [ρ, gridStep, div_eq_mul_inv, mul_comm] using hB
  apply gaussian_sum_coupling_of_phases p m μ
  · intro f hf v
    let g := fun q => Complex.exp (((∑ i, v i * f q i : ℝ) : ℂ) * Complex.I)
    have hfm : Measurable f := hf.elim (fun h => h ▸ measurable_fst) (fun h => h ▸ measurable_snd)
    have hdot : Continuous (fun x : Fin n → ℝ => Complex.exp (((∑ i, v i * x i : ℝ) : ℂ) * Complex.I)) := by fun_prop
    have hgm : Measurable g := hdot.measurable.comp hfm
    have hi (N) : (∫ q, g q ∂(p N : Measure _)) = ∫ z, g (R z) ∂ρ N :=
      integral_map hR.aemeasurable hgm.aestronglyMeasurable
    change Tendsto (fun N => ∫ q, g q ∂(p N : Measure _)) _ _
    simp_rw [hi]
    have hn : ‖(toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ∑ i, v i ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    have he (z : EuclideanSpace ℝ (Fin n)) : ⟪toLp 2 v, z⟫ = ∑ i, v i * z i := by
      rw [real_inner_comm]; rfl
    rcases hf with rfl | rfl
    · simpa only [walkProbe_apply_true, he, hn, R, g] using hproj true (toLp 2 v)
    · simpa only [walkProbe_apply_false, he, hn, R, g] using hproj false (toLp 2 v)
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    apply Subtype.ext
    have hsum := walkLaw_sum 0 (T N) (M N) (hM N) N
    have he : (fun z : WalkState (Fin n → ℝ) (Fin n) => m + ((R z).1 + (R z).2)) =ᵐ[ρ N] Prod.fst := by
      filter_upwards [hsum] with z hz
      rw [hend N hN, hstart N hN] at hz
      change m + ofLp (z.2.1 + z.2.2) = z.1
      rw [hz]
      change m + (z.1 - m) = z.1
      abel
    change (μ : Measure _) = ((ρ N).map R).map (fun q => m + (q.1 + q.2))
    rw [Measure.map_map (show Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => m + (q.1+q.2)) by fun_prop) hR]
    exact (hsite N hN).symm.trans (Measure.map_congr he).symm

end G54

end ModWalkLimit

section ModRelay

/- # Coupling a centered Gaussian tilt as the sum of two Gaussian marginals -/

open MeasureTheory ProbabilityTheory WithLp Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace G54

/-- The discrete bridge and its compensated increments give a joint law with both
Gaussian marginals and the prescribed translated sum. -/
theorem twoGaussians_unconditional : TwoGaussians := by
  intro n ψ hcv hsmooth hLip hprob
  obtain ⟨L, hL⟩ := hLip
  have hc := hsmooth.continuous
  let w := potentialWeight ψ
  let μ : ProbabilityMeasure (Fin n → ℝ) := ⟨(gaussianIncrements n 1).withDensity w, hprob⟩
  let m : Fin n → ℝ := fun i => ∫ y : Fin n → ℝ, y i ∂(μ : Measure (Fin n → ℝ))
  let T := fun N k => bridgeCompensatedStep hcv hc hL (gridStep N) (gridRemaining N (k+1))
  let M := fun N k => bridgeVector ψ (gridRemaining N k)
  have hT : ∀ N k, IsMarkovKernel (T N k) :=
    fun N k => bridgeCompensatedStep_markov hcv hc hL _ _
  have hM (N k) : Measurable (M N k) := measurable_bridgeVector _ _
  apply gaussian_sum_of_walk_bounds m μ T M hM
  · intro N hN
    simp only [M, gridRemaining_start hN, bridgeVector]
    congr 1
    unfold bridgeMean
    rw [bridgeEndpoint_normalized (measurable_potentialWeight hc) hprob]
    rfl
  · intro N _ x
    simp [M, bridgeVector, bridgeMean_zero hc x]
  · intro N hN
    calc
      _ = gridSite w N N := by
        apply walkLaw_fst 0 (T N) (M N) (hM N) (gridSite w N) rfl
        intro k _
        change (bridgeCompensatedStep hcv hc hL _ _).fst ∘ₘ gridSite w N k = _
        rw [bridgeCompensatedStep_fst hcv hc hL]
        rfl
      _ = _ := gridSite_end hN hc hL hprob
  · intro b v
    refine ⟨16 * (12 * Real.exp 1 + ∫ u : ℝ, |u|^3 ∂gaussianReal 0 1) * ‖v‖^3, ?_⟩
    intro N _ k hk x s
    have h := bridgeCompensatedStep_phase hcv hc hL (gridStep N)
      (gridRemaining N (k+1)) b v x s
    simpa only [M, T, gridRemaining_succ hk] using h

end G54

end ModRelay

/-- **Green's Problem 54 (Talagrand's convexity conjecture), conditional on a weak form of
Caffarelli's contraction theorem and on the Lipschitz image lemma.** -/
theorem OMA.solution_conditional (hC : G54.CaffarelliContraction)
    (hL : G54.GaussianLipschitzImage) : type_of% @Green54.green_54 :=
  G54.green54_of_caffarelli_lipschitzImage hC hL

/-- The ten-fold sumset contains a compact convex subset of Gaussian measure at least `0.01`. -/
theorem OMA.solution : type_of% @Green54.green_54 := by
  exact G54.green54_of_twoGaussians G54.twoGaussians_unconditional
