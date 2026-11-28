import OMAReductions.R_Hilbert5_hilbert_fifth_problem_R1
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Reduction of `Hilbert5.hilbert_fifth_problem.R1.H1` (No Small Subgroups for Locally Euclidean Groups)

Following Gleason (1952), Montgomery–Zippin (1952, 1955), and Yamabe (1953) (see also Tao,
*Hilbert's Fifth Problem and Related Topics*, Section 4.2), we reduce the No-Small-Subgroups (NSS)
theorem for connected Hausdorff locally Euclidean topological groups `H : Type` to three canonical
structural theorems of Lie theory:

1. (`H1`) **Gleason–Yamabe approximation with Brouwer dimension bound**: every connected Hausdorff
   locally Euclidean group `H` of dimension `n` admits arbitrarily small compact normal subgroups
   `K ◁ H` with Lie quotients `H ⧸ K` of dimension `d ≤ n`, and the intersection `K₁ ⊓ K₂` of
   two such compact normal subgroups also has a Lie quotient of dimension `≤ n` (via the closed
   embedding `H ⧸ (K₁ ⊓ K₂) ↪ (H ⧸ K₁) × (H ⧸ K₂)` and Cartan's closed subgroup theorem).
2. (`H2`) **Dimension monotonicity, zero-dimensional fiber finiteness, and NSS for Lie groups**:
   every finite-dimensional Lie group has no small subgroups; and whenever `K₂ ≤ K₁` are compact
   normal subgroups of `H` with Lie quotients of dimensions `d₁, d₂`, we have `d₁ ≤ d₂`, with
   `d₁ = d₂` implying finite index `Finite (K₁ ⧸ K₂.subgroupOf K₁)`.
3. (`H3`) **Montgomery–Zippin finiteness of compact totally disconnected normal subgroups**:
   if `K ◁ H` is a compact totally disconnected normal subgroup of a connected locally Euclidean
   group `H` with Lie quotient `H ⧸ K`, then `K` is finite (locally trivial principal `K`-bundle
   over the locally connected manifold `H ⧸ K` forces `K` to be discrete, hence finite).

Inside `main`, we prove completely from scratch:
- Choosing a compact normal subgroup `K ◁ H` maximizing the Lie quotient dimension `d ≤ n`.
- Every smaller Lie quotient `K' = K ⊓ K₁` has `d' = d`, hence finite index in `K`, making
  `K'.subgroupOf K` a clopen subgroup of `K` (finite union of closed cosets).
- Separating any two distinct points `x ≠ y` in `K` by a clopen coset `x · (K'.subgroupOf K)`,
  proving `TotallyDisconnectedSpace K`.
- Applying `H3` to obtain `Finite K`, separating `1` from `K \ {1}` in `T2Space H`, and
  intersecting with the preimage of an NSS neighborhood of `1` in the Lie group `H ⧸ K` to obtain
  an NSS neighborhood `U ∈ 𝓝 (1 : H)`.
-/

-- Reduction Hilbert5.hilbert_fifth_problem.R1.H1.R1 of Hilbert5.hilbert_fifth_problem.R1.H1
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

open Set Topology Filter TopologicalSpace
open scoped Manifold ContDiff Pointwise Classical

noncomputable section

namespace OMA.R_Hilbert5_hilbert_fifth_problem_R1_H1_R1

/- ### Helper lemmas: clopen finite-index compact subgroups & total disconnectedness -/

private lemma isOpen_of_isClosed_finiteIndex {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] (N : Subgroup K) [N.Normal] (hN_closed : IsClosed (N : Set K))
    [Finite (K ⧸ N)] : IsOpen (N : Set K) := by
  have hcompl_eq : (N : Set K)ᶜ = ⋃ (q : K ⧸ N) (_ : q ≠ (1 : K ⧸ N)),
      (QuotientGroup.mk ⁻¹' ({q} : Set (K ⧸ N))) := by
    ext x
    simp only [mem_compl_iff, SetLike.mem_coe, mem_iUnion, mem_preimage, mem_singleton_iff]
    constructor
    · intro hx
      refine ⟨QuotientGroup.mk x, ?_, rfl⟩
      intro h1
      exact hx (QuotientGroup.eq_one_iff x |>.mp h1)
    · rintro ⟨q, hq, rfl⟩ hx
      exact hq ((QuotientGroup.eq_one_iff x).mpr hx)
  rw [← isClosed_compl_iff, hcompl_eq]
  refine isClosed_iUnion_of_finite fun q => ?_
  refine isClosed_iUnion_of_finite fun _ => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hcoset : QuotientGroup.mk ⁻¹' ({QuotientGroup.mk g} : Set (K ⧸ N)) =
      (fun x : K => g⁻¹ * x) ⁻¹' (N : Set K) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, QuotientGroup.eq, SetLike.mem_coe]
    constructor
    · intro h; simpa using N.inv_mem h
    · intro h; simpa using N.inv_mem h
  rw [hcoset]
  exact hN_closed.preimage (continuous_const.mul continuous_id)

private lemma totallyDisconnectedSpace_of_clopen_sep {X : Type*} [TopologicalSpace X]
    (hsep : ∀ x y : X, x ≠ y → ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ y ∉ C) :
    TotallyDisconnectedSpace X := by
  refine ⟨fun s hs_sub hs_pre => ?_⟩
  intro x hx y hy
  by_contra hne
  obtain ⟨C, hC_clopen, hxC, hyC⟩ := hsep x y hne
  have hsub : s ⊆ C ∪ Cᶜ := by intro z _; exact em (z ∈ C)
  have hdisj : s ∩ (C ∩ Cᶜ) = ∅ := by simp
  have hne1 : (s ∩ C).Nonempty := ⟨x, hx, hxC⟩
  have hne2 : (s ∩ Cᶜ).Nonempty := ⟨y, hy, hyC⟩
  have hcontra := hs_pre C Cᶜ hC_clopen.isOpen hC_clopen.isClosed.isOpen_compl hsub hne1 hne2
  rcases hcontra with ⟨z, _, hzC, hzCc⟩
  exact hzCc hzC

/- ### Hypotheses -/

/-- **Hypothesis 1 (Gleason–Yamabe approximation with Brouwer dimension bound)**:
for any connected Hausdorff locally Euclidean topological group `H : Type` of dimension `n`,
(1) every neighborhood `U ∈ 𝓝 (1 : H)` contains a compact normal subgroup `K ◁ H` whose quotient
`H ⧸ K` admits a Lie group presentation of dimension `d ≤ n`, and
(2) for any two compact normal subgroups `K₁, K₂ ◁ H` with Lie quotients, `H ⧸ (K₁ ⊓ K₂)` also
admits a Lie group presentation of dimension `d ≤ n`. -/
def H1 : Prop :=
  ∀ (n : ℕ) (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [ConnectedSpace H] [ChartedSpace (EuclideanSpace ℝ (Fin n)) H],
    (∀ U : Set H, U ∈ 𝓝 (1 : H) →
      ∃ (K : Subgroup H) (_ : K.Normal), IsCompact (K : Set H) ∧ (K : Set H) ⊆ U ∧
        ∃ d : ℕ, d ≤ n ∧ Nonempty (LieGroupPresentation (H ⧸ K) d)) ∧
    (∀ (K₁ K₂ : Subgroup H) [K₁.Normal] [K₂.Normal],
      IsCompact (K₁ : Set H) → IsCompact (K₂ : Set H) →
      (∃ d₁ : ℕ, Nonempty (LieGroupPresentation (H ⧸ K₁) d₁)) →
      (∃ d₂ : ℕ, Nonempty (LieGroupPresentation (H ⧸ K₂) d₂)) →
      ∃ d : ℕ, d ≤ n ∧ Nonempty (LieGroupPresentation (H ⧸ (K₁ ⊓ K₂)) d))

/-- **Hypothesis 2 (Lie quotient dimension monotonicity, zero-dimensional fiber finiteness, and NSS for Lie groups)**:
(1) every topological group admitting a finite-dimensional real-analytic `LieGroupPresentation` has
no small subgroups; and
(2) whenever `K₂ ≤ K₁` are compact normal subgroups of a connected Hausdorff topological group `H`
whose quotients admit Lie group presentations of dimensions `d₁` and `d₂`, we have `d₁ ≤ d₂`, and
if `d₁ = d₂` then `K₂` has finite index in `K₁`. -/
def H2 : Prop :=
  (∀ (d : ℕ) (G : Type) [Group G] [TopologicalSpace G],
    Nonempty (LieGroupPresentation G d) →
    ∃ W : Set G, W ∈ 𝓝 (1 : G) ∧ ∀ M : Subgroup G, (M : Set G) ⊆ W → M = ⊥) ∧
  (∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [ConnectedSpace H] (K₁ K₂ : Subgroup H) [K₁.Normal] [K₂.Normal],
    IsCompact (K₁ : Set H) → IsCompact (K₂ : Set H) → K₂ ≤ K₁ →
    ∀ (d₁ d₂ : ℕ), Nonempty (LieGroupPresentation (H ⧸ K₁) d₁) →
      Nonempty (LieGroupPresentation (H ⧸ K₂) d₂) →
      d₁ ≤ d₂ ∧ (d₁ = d₂ → Finite (K₁ ⧸ K₂.subgroupOf K₁)))

/-- **Hypothesis 3 (Montgomery–Zippin finiteness of compact totally disconnected normal subgroups)**:
if `K ◁ H` is a compact totally disconnected normal subgroup of a connected Hausdorff locally
Euclidean topological group `H : Type` such that `H ⧸ K` admits a finite-dimensional Lie group
presentation, then `K` is finite. -/
def H3 : Prop :=
  ∀ (n d : ℕ) (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [ConnectedSpace H] [ChartedSpace (EuclideanSpace ℝ (Fin n)) H]
    (K : Subgroup H) [K.Normal],
    IsCompact (K : Set H) → TotallyDisconnectedSpace K →
    Nonempty (LieGroupPresentation (H ⧸ K) d) →
    Finite K

/- ### Main Reduction Theorem -/

theorem main : H1 → H2 → H3 → OMA.R_Hilbert5_hilbert_fifth_problem_R1.H1 := by
  intro hGY hLie hMZ
  dsimp only [OMA.R_Hilbert5_hilbert_fifth_problem_R1.H1]
  intro n H _ _ _ _ _ _
  obtain ⟨hGY_approx, hGY_inf⟩ := hGY n H
  obtain ⟨hLie_NSS, hLie_dim⟩ := hLie
  -- Step 1: Collect all Lie-quotient dimensions `d ≤ n` realized by compact normal subgroups `K ◁ H`
  let D : Finset ℕ := (Finset.range (n + 1)).filter fun d =>
    ∃ (K : Subgroup H) (_ : K.Normal), IsCompact (K : Set H) ∧
      Nonempty (LieGroupPresentation (H ⧸ K) d)
  have hD_nonempty : D.Nonempty := by
    obtain ⟨K₀, hK₀_norm, hK₀_comp, _, d₀, hd₀_le, hpres₀⟩ := hGY_approx Set.univ Filter.univ_mem
    exact ⟨d₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨K₀, hK₀_norm, hK₀_comp, hpres₀⟩⟩⟩
  -- Pick the maximal dimension `d_max ∈ D` and a witness compact normal subgroup `K ◁ H`
  let d_max : ℕ := D.max' hD_nonempty
  have hd_max_mem : d_max ∈ D := Finset.max'_mem D hD_nonempty
  obtain ⟨K, hK_norm, hK_comp, hK_pres⟩ := (Finset.mem_filter.mp hd_max_mem).2
  have : K.Normal := hK_norm
  -- Step 2: Prove `TotallyDisconnectedSpace K` by separating points via clopen finite-index subgroups
  have hK_td : TotallyDisconnectedSpace K := by
    apply totallyDisconnectedSpace_of_clopen_sep
    intro x y hxy
    have hdiff_ne1 : (x : H)⁻¹ * (y : H) ≠ 1 := by
      intro h1
      apply hxy
      apply Subtype.ext
      have : (y : H) = (x : H) * ((x : H)⁻¹ * (y : H)) := by group
      rw [h1, mul_one] at this
      exact this.symm
    let U : Set H := ({(x : H)⁻¹ * (y : H)} : Set H)ᶜ
    have hU_nhds : U ∈ 𝓝 (1 : H) :=
      isClosed_singleton.isOpen_compl.mem_nhds (by simpa [U] using hdiff_ne1.symm)
    obtain ⟨K₁, hK₁_norm, hK₁_comp, hK₁_sub, d₁, _, hK₁_pres⟩ := hGY_approx U hU_nhds
    have : K₁.Normal := hK₁_norm
    let K' : Subgroup H := K ⊓ K₁
    have hK'_norm : K'.Normal := Subgroup.normal_inf_normal K K₁
    have : K'.Normal := hK'_norm
    have hK'_comp : IsCompact (K' : Set H) := by
      change IsCompact ((K : Set H) ∩ (K₁ : Set H))
      exact hK_comp.inter_right hK₁_comp.isClosed
    have hK'_le : K' ≤ K := inf_le_left
    obtain ⟨d', hd'_le_n, hK'_pres⟩ := hGY_inf K K₁ hK_comp hK₁_comp ⟨d_max, hK_pres⟩ ⟨d₁, hK₁_pres⟩
    have hd'_mem : d' ∈ D :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨K', hK'_norm, hK'_comp, hK'_pres⟩⟩
    have hd'_le_max : d' ≤ d_max := Finset.le_max' D d' hd'_mem
    obtain ⟨hmax_le_d', hfin_of_eq⟩ := hLie_dim H K K' hK_comp hK'_comp hK'_le d_max d' hK_pres hK'_pres
    have hd'_eq : d_max = d' := le_antisymm hmax_le_d' hd'_le_max
    have : Finite (K ⧸ K'.subgroupOf K) := hfin_of_eq hd'_eq
    have : (K'.subgroupOf K).Normal := ⟨fun n hn g => hK'_norm.conj_mem (n : H) hn (g : H)⟩
    have hsub_closed : IsClosed ((K'.subgroupOf K : Subgroup K) : Set K) := by
      have heq : ((K'.subgroupOf K : Subgroup K) : Set K) = ((↑) : K → H) ⁻¹' (K' : Set H) := rfl
      rw [heq]
      exact hK'_comp.isClosed.preimage continuous_subtype_val
    have hsub_open : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) :=
      isOpen_of_isClosed_finiteIndex (K'.subgroupOf K) hsub_closed
    let C : Set K := (fun z : K => x⁻¹ * z) ⁻¹' ((K'.subgroupOf K : Subgroup K) : Set K)
    have hC_clopen : IsClopen C :=
      ⟨hsub_closed.preimage (continuous_const.mul continuous_id),
       hsub_open.preimage (continuous_const.mul continuous_id)⟩
    refine ⟨C, hC_clopen, ?_, ?_⟩
    · change x⁻¹ * x ∈ K'.subgroupOf K
      rw [inv_mul_cancel]
      exact (K'.subgroupOf K).one_mem
    · intro hyC
      have hmem_K' : (x : H)⁻¹ * (y : H) ∈ K' := by
        have h1 : x⁻¹ * y ∈ K'.subgroupOf K := hyC
        simpa [Subgroup.mem_subgroupOf] using h1
      have hmem_K₁ : (x : H)⁻¹ * (y : H) ∈ (K₁ : Set H) := hmem_K'.2
      have hmem_U : (x : H)⁻¹ * (y : H) ∈ U := hK₁_sub hmem_K₁
      exact hmem_U rfl
  -- Step 3: Apply Montgomery–Zippin (`H3`) to deduce `Finite K`
  have : Finite K := hMZ n d_max H K hK_comp hK_td hK_pres
  -- Step 4: Separate `1` from `K \ {1}` in `T2Space H` and intersect with an NSS neighborhood of `H ⧸ K`
  have hK_fin_set : (K : Set H).Finite := Set.finite_coe_iff.mp ‹Finite K›
  have hK_diff_closed : IsClosed ((K : Set H) \ {(1 : H)}) :=
    (hK_fin_set.sdiff).isClosed
  let W₁ : Set H := ((K : Set H) \ {(1 : H)})ᶜ
  have hW₁_nhds : W₁ ∈ 𝓝 (1 : H) :=
    hK_diff_closed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨W₂, hW₂_nhds, hW₂_NSS⟩ := hLie_NSS d_max (H ⧸ K) hK_pres
  let U : Set H := W₁ ∩ ((QuotientGroup.mk : H → H ⧸ K) ⁻¹' W₂)
  have hU_nhds : U ∈ 𝓝 (1 : H) := by
    refine Filter.inter_mem hW₁_nhds ?_
    have hcont : Continuous (QuotientGroup.mk : H → H ⧸ K) := continuous_quot_mk
    have h1 : (QuotientGroup.mk (1 : H) : H ⧸ K) = 1 := rfl
    exact hcont.continuousAt.preimage_mem_nhds (h1.symm ▸ hW₂_nhds)
  refine ⟨U, hU_nhds, fun L hL_sub => ?_⟩
  -- First show `L.map (QuotientGroup.mk' K) = ⊥` via NSS of `H ⧸ K`
  have hmap_sub : (L.map (QuotientGroup.mk' K) : Set (H ⧸ K)) ⊆ W₂ := by
    rintro _ ⟨g, hgL, rfl⟩
    exact (hL_sub hgL).2
  have hmap_bot : L.map (QuotientGroup.mk' K) = ⊥ := hW₂_NSS _ hmap_sub
  -- Deduce `L ≤ K`, hence `L ⊆ W₁ ∩ K = {1}`, hence `L = ⊥`
  rw [Subgroup.eq_bot_iff_forall]
  intro g hgL
  have hq1 : (QuotientGroup.mk g : H ⧸ K) = 1 := by
    have hmem : QuotientGroup.mk' K g ∈ L.map (QuotientGroup.mk' K) := ⟨g, hgL, rfl⟩
    rw [hmap_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hgK : g ∈ K := (QuotientGroup.eq_one_iff g).mp hq1
  have hgW₁ : g ∈ W₁ := (hL_sub hgL).1
  by_contra hne
  exact hgW₁ ⟨hgK, hne⟩

end OMA.R_Hilbert5_hilbert_fifth_problem_R1_H1_R1
