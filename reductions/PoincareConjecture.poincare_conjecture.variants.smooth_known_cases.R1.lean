import FormalConjectures.Millennium.Poincare

/-! # A reduction for the known smooth Poincaré cases

We extract an open neighborhood of the sphere image with finitely many charts.
The hypotheses supply compactness, topological recognition, and a smooth local
diffeomorphism. Homotopy lifting turns that local map into a diffeomorphism.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_known_cases_R1

open Metric PoincareConjecture Set TopologicalSpace
open scoped Manifold ContDiff ContinuousMap

-- A homotopy retract onto the sphere gives a nonzero top mod-two homology class.
-- Hatcher, Algebraic Topology, Proposition 3.29, rules this out for a
-- connected noncompact manifold.
def H1 : Prop :=
  ∀ (n : ℕ), n ∈ SmoothTrueValues →
    ∀ (N : Type) [TopologicalSpace N] [T2Space N]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
      [PathConnectedSpace N] [SecondCountableTopology N],
      let S := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
      (∃ (g : C(S, N)) (r : C(N, S)), (r.comp g).Homotopic (ContinuousMap.id S)) →
        CompactSpace N

-- Topological recognition with the usual compactness and countability assumptions.
-- Use the classification of compact manifolds in dimensions one and two,
-- Perelman in dimension three, and Smale in the listed dimensions at least five.
def H2 : Prop :=
  ∀ (n : ℕ), n ∈ SmoothTrueValues →
    ∀ (M : Type) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [PathConnectedSpace M] [CompactSpace M] [SecondCountableTopology M],
      let S := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
      M ≃ₕ S → Nonempty (M ≃ₜ S)

-- On a topological sphere, construct a smooth local model with a homotopy right inverse.
-- Smooth classification in dimensions one through three and Wang and Xu,
-- Corollary 1.15, for the listed dimensions at least five give such maps.
def H3 : Prop :=
  ∀ (n : ℕ), n ∈ SmoothTrueValues →
    ∀ (M : Type) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [CompactSpace M] [SecondCountableTopology M],
      let S := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
      Nonempty (M ≃ₜ S) → ∃ (p : C(S, M)) (q : C(M, S)),
        IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p ∧ (p.comp q).Homotopic (ContinuousMap.id M)

lemma positive_of_known_dimension {n : ℕ} (hn : n ∈ SmoothTrueValues) : 0 < n := by
  cases n with
  | zero => simp [SmoothTrueValues] at hn
  | succ k => exact Nat.zero_lt_succ k

-- Lift the homotopy to turn its right inverse into an actual section. Uniqueness
-- of lifts on the connected total space then gives the other inverse identity.
lemma covering_bijective_of_homotopy_right_inverse
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] [PreconnectedSpace E]
    (p : C(E, B)) (hp : IsCoveringMap p) (q : C(B, E))
    (h : (p.comp q).Homotopic (ContinuousMap.id B)) : Function.Bijective p := by
  obtain ⟨F⟩ := h
  have hzero : ∀ b, F (0, b) = p (q b) := fun b => F.apply_zero b
  let lift := hp.liftHomotopy F.toContinuousMap q hzero
  let s : B → E := fun b => lift (1, b)
  have hs_cont : Continuous s := lift.continuous.comp (continuous_const.prodMk continuous_id)
  have hs : Function.RightInverse s p := fun b =>
    (congrFun (hp.liftHomotopy_lifts F.toContinuousMap q hzero) (1, b)).trans (F.apply_one b)
  have hs_left : Function.LeftInverse s p := by
    intro x
    have hcomp : (⇑p) ∘ (s ∘ p) = (⇑p) ∘ id := funext fun z => hs (p z)
    have hagree := hp.eq_of_comp_eq (hs_cont.comp p.continuous) continuous_id hcomp
      (s (p x)) (congrArg s (hs (p x)))
    exact congrFun hagree x
  exact ⟨hs_left.injective, hs.surjective⟩

lemma sphere_path_connected {n : ℕ} (hn : 0 < n) :
    PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have hfin : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin]
    omega
  exact isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (Module.one_lt_rank_of_one_lt_finrank hfin) 0
      (zero_le_one : (0 : ℝ) ≤ 1))

lemma path_connected_of_homotopy_equiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace Y] (e : X ≃ₕ Y) : PathConnectedSpace X := by
  obtain ⟨F⟩ := e.left_inv
  refine ⟨(inferInstance : Nonempty Y).map e.symm, ?_⟩
  intro x y
  have hx : Joined (e.symm (e x)) x := ⟨F.evalAt x⟩
  have hy : Joined (e.symm (e y)) y := ⟨F.evalAt y⟩
  exact hx.symm.trans (((PathConnectedSpace.joined (e x) (e y)).map e.symm.continuous).trans hy)

-- Compactness of the source sphere turns a local diffeomorphism into a covering.
lemma sphere_diffeomorph_iff_local_section {n : ℕ} (hn : 0 < n)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    let S := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
    Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ S) ↔ ∃ (p : C(S, M)) (q : C(M, S)),
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p ∧ (p.comp q).Homotopic (ContinuousMap.id M) := by
  dsimp only
  constructor
  · rintro ⟨d⟩
    let p : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, M) := ⟨d.symm, d.symm.continuous⟩
    let q : C(M, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := ⟨d, d.continuous⟩
    refine ⟨p, q, d.symm.isLocalDiffeomorph, ?_⟩
    have hcomp : p.comp q = ContinuousMap.id M := by
      ext x
      exact d.symm_apply_apply x
    rw [hcomp]
  · rintro ⟨p, q, hp, hq⟩
    have := sphere_path_connected hn
    have hcov : IsCoveringMap p := isLocalHomeomorph_iff_isCoveringMap.mp hp.isLocalHomeomorph
    exact ⟨(hp.diffeomorphOfBijective (covering_bijective_of_homotopy_right_inverse p hcov q hq)).symm⟩

-- Cover the compact image of the inverse map by finitely many charts.
lemma finite_chart_homotopy_core (H : Type*) [TopologicalSpace H] [SecondCountableTopology H]
    {M Y : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace Y] [CompactSpace Y]
    (e : M ≃ₕ Y) :
    ∃ U : TopologicalSpace.Opens M, SecondCountableTopology U ∧
      ∃ (g : C(Y, U)) (r : C(U, Y)), (r.comp g).Homotopic (ContinuousMap.id Y) := by
  classical
  let V (x : M) := (chartAt H x).source
  have hV (x : M) : IsOpen (V x) := (chartAt H x).open_source
  have hcover : range e.symm ⊆ ⋃ x, V x := fun y _ =>
    mem_iUnion.mpr ⟨y, mem_chart_source H y⟩
  obtain ⟨t, ht⟩ := (isCompact_range e.symm.continuous).elim_finite_subcover V hV hcover
  let U : TopologicalSpace.Opens M := ⟨⋃ x ∈ t, V x, isOpen_biUnion fun x _ => hV x⟩
  let W (i : t) : Set U := (Subtype.val : U → M) ⁻¹' V i.val
  have hW (i : t) : SecondCountableTopology (W i) := by
    have : SecondCountableTopology (V i.val) := (chartAt H i.val).secondCountableTopology_source
    have he : Topology.IsEmbedding (fun z : W i => z.val.val) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact (he.codRestrict (V i.val) (fun z => z.property)).secondCountableTopology
  have hU : SecondCountableTopology U := by
    apply secondCountableTopology_of_countable_cover (U := W)
      (fun i => (hV i.val).preimage continuous_subtype_val)
    apply eq_univ_of_forall
    intro z
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.mp z.property
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hz⟩
  let g : C(Y, U) := ⟨fun y => ⟨e.symm y, ht (mem_range_self y)⟩,
    e.symm.continuous.subtype_mk _⟩
  exact ⟨U, hU, g, e.toFun.restrict U, e.right_inv⟩

lemma compact_of_compact_open_piece {M : Type*} [TopologicalSpace M] [T2Space M]
    [PreconnectedSpace M] (U : TopologicalSpace.Opens M)
    (h : ∃ K : Set U, K.Nonempty ∧ IsOpen K ∧ IsCompact K) : CompactSpace M := by
  obtain ⟨K, hne, hopen, hcompact⟩ := h
  have hc := hcompact.image (continuous_subtype_val : Continuous (Subtype.val : U → M))
  have hclopen : IsClopen ((Subtype.val : U → M) '' K) :=
    ⟨hc.isClosed, U.isOpen.isOpenMap_subtype_val _ hopen⟩
  exact ⟨hclopen.eq_univ (hne.image _) ▸ hc⟩

-- Membership in a countable basis embeds the underlying set into Set ℕ in Type.
lemma small_topological_model (X : Type*) [TopologicalSpace X] [T1Space X]
    [SecondCountableTopology X] : ∃ (N : Type) (_ : TopologicalSpace N), Nonempty (N ≃ₜ X) := by
  classical
  let B := countableBasis X
  let : Encodable B := (countable_countableBasis X).toEncodable
  let code (x : X) : Set ℕ := {k | ∃ t : B, Encodable.encode t = k ∧ x ∈ t.val}
  have hinj : Function.Injective code := by
    intro x y hxy
    by_contra hne
    obtain ⟨v, hv, hx, hsub⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open
      (show x ∈ ({y} : Set X)ᶜ from hne) isOpen_compl_singleton
    let b : B := ⟨v, hv⟩
    have hm : Encodable.encode b ∈ code x := ⟨b, rfl, hx⟩
    rw [hxy] at hm
    obtain ⟨c, hc, hy⟩ := hm
    have he : c = b := Encodable.encode_injective hc
    rw [he] at hy
    exact hsub hy rfl
  let e := Equiv.ofInjective code hinj
  let : TopologicalSpace (range code) := TopologicalSpace.induced e.symm inferInstance
  exact ⟨range code, inferInstance, ⟨e.symm.toHomeomorphOfIsInducing ⟨rfl⟩⟩⟩

-- Pull each chart back through the homeomorphism. Its coordinate changes are unchanged.
-- Pull back the atlas so a homeomorphism between universes becomes a diffeomorphism.
lemma transport_smooth_atlas {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] (h : N ≃ₜ M) :
    ∃ (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) N) (_ : IsManifold (𝓡 n) ∞ N),
      Nonempty (N ≃ₘ⟮𝓡 n, 𝓡 n⟯ M) := by
  let E := EuclideanSpace ℝ (Fin n)
  let T (a : OpenPartialHomeomorph M E) := h.transOpenPartialHomeomorph a
  have hchange (a b : OpenPartialHomeomorph M E) : (T a).symm.trans (T b) = a.symm.trans b := by
    apply OpenPartialHomeomorph.ext
    · intro z
      change b (h (h.symm (a.symm z))) = b (a.symm z)
      rw [h.apply_symm_apply]
    · intro z
      change a (h (h.symm (b.symm z))) = a (b.symm z)
      rw [h.apply_symm_apply]
    · ext z
      change (z ∈ a.target ∧ h (h.symm (a.symm z)) ∈ b.source) ↔
        (z ∈ a.target ∧ a.symm z ∈ b.source)
      rw [h.apply_symm_apply]
  let charts : ChartedSpace E N :=
    { atlas := T '' atlas E M
      chartAt := fun x => T (chartAt E (h x))
      mem_chart_source := fun x => mem_chart_source E (h x)
      chart_mem_atlas := fun x => ⟨_, chart_mem_atlas E (h x), rfl⟩ }
  have group : HasGroupoid N (contDiffGroupoid ∞ (𝓡 n)) := by
    constructor
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [hchange]
    exact (contDiffGroupoid ∞ (𝓡 n)).compatible ha hb
  have smooth : IsManifold (𝓡 n) ∞ N := IsManifold.mk' _ _ _
  refine ⟨charts, smooth, ⟨{ toEquiv := h.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }⟩⟩
  · intro x
    apply contMDiffAt_iff.mpr
    refine ⟨h.continuous.continuousAt, ?_⟩
    change ContDiffWithinAt ℝ ∞
      (fun z => (chartAt E (h x)) (h (h.symm ((chartAt E (h x)).symm z)))) _
      ((chartAt E (h x)) (h x))
    simp only [h.apply_symm_apply]
    exact (contMDiffAt_iff.mp (contMDiffAt_id (I := 𝓡 n) (n := ∞) (x := h x))).2
  · intro x
    apply contMDiffAt_iff.mpr
    refine ⟨h.symm.continuous.continuousAt, ?_⟩
    change ContDiffWithinAt ℝ ∞
      (fun z => (chartAt E (h (h.symm x))) (h (h.symm ((chartAt E x).symm z)))) _
      ((chartAt E x) x)
    simp only [h.apply_symm_apply]
    exact (contMDiffAt_iff.mp (contMDiffAt_id (I := 𝓡 n) (n := ∞) (x := x))).2

-- Apply the obstruction to the single open path component containing the sphere image.
lemma compact_open_piece_from_second_countable (hsupport : H1) {n : ℕ} (hn : n ∈ SmoothTrueValues)
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [SecondCountableTopology X]
    (g : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X))
    (r : C(X, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (hr : (r.comp g).Homotopic (ContinuousMap.id _)) :
    ∃ K : Set X, K.Nonempty ∧ IsOpen K ∧ IsCompact K := by
  let S := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
  have : PathConnectedSpace S := sphere_path_connected (positive_of_known_dimension hn)
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  have : LocallyPathConnectedSpace X :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n)) X
  let V : TopologicalSpace.Opens X := ⟨pathComponent (g s), IsOpen.pathComponent (g s)⟩
  have hg (z : S) : g z ∈ V := (PathConnectedSpace.joined s z).map g.continuous
  let gV : C(S, V) := ⟨fun z => ⟨g z, hg z⟩, g.continuous.subtype_mk _⟩
  let rV : C(V, S) := r.restrict V
  have : PathConnectedSpace V :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent
  obtain ⟨N, top, ⟨h⟩⟩ := small_topological_model V
  have : T2Space N := h.isEmbedding.t2Space
  have : SecondCountableTopology N := h.secondCountableTopology
  have : PathConnectedSpace N := path_connected_of_homotopy_equiv h.toHomotopyEquiv
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) N := h.symm.chartedSpace (H := EuclideanSpace ℝ (Fin n))
  let g' := (h.symm : C(V, N)).comp gV
  let r' := rV.comp (h : C(N, V))
  have hr' : (r'.comp g').Homotopic (ContinuousMap.id _) := by
    have heq : r'.comp g' = r.comp g := by
      apply ContinuousMap.ext
      intro z
      exact congrArg rV (h.apply_symm_apply (gV z))
    rwa [heq]
  have : CompactSpace N := hsupport n hn N ⟨g', r', hr'⟩
  have : CompactSpace V := h.compactSpace
  exact ⟨V, ⟨g s, hg s⟩, V.isOpen, isCompact_iff_compactSpace.mpr inferInstance⟩

theorem main : H1 → H2 → H3 → type_of% @PoincareConjecture.poincare_conjecture.variants.smooth_known_cases := by
  intro hsupport htop hsmooth n hn M top haus charts smooth e
  have hpos := positive_of_known_dimension hn
  have := sphere_path_connected hpos
  have := path_connected_of_homotopy_equiv e
  obtain ⟨U, hU, g, r, hr⟩ := finite_chart_homotopy_core (EuclideanSpace ℝ (Fin n)) e
  have : CompactSpace M := compact_of_compact_open_piece U
    (compact_open_piece_from_second_countable hsupport hn g r hr)
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact
    (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨N, topN, ⟨homeo⟩⟩ := small_topological_model M
  have : T2Space N := homeo.isEmbedding.t2Space
  have : CompactSpace N := homeo.symm.compactSpace
  have : SecondCountableTopology N := homeo.secondCountableTopology
  have : PathConnectedSpace N := path_connected_of_homotopy_equiv homeo.toHomotopyEquiv
  obtain ⟨chartN, smoothN, ⟨d⟩⟩ := transport_smooth_atlas (n := n) homeo
  have htopN := htop n hn N (homeo.toHomotopyEquiv.trans e)
  obtain ⟨s⟩ := (sphere_diffeomorph_iff_local_section hpos).2 (hsmooth n hn N htopN)
  exact ⟨d.symm.trans s⟩

-- The two classification statements are necessary for the original conclusion.
lemma classification_conditions_of_solution
    (h : ∀ (n : ℕ), n ∈ SmoothTrueValues → SmoothConjectureFor.{0} n) : H2 ∧ H3 := by
  constructor
  · dsimp only [H2]
    intro n hn M top haus charts smooth path compact countable e
    exact (h n hn M e).map (fun d => d.toHomeomorph)
  · dsimp only [H3]
    intro n hn M top haus charts smooth compact countable homeo
    obtain ⟨e⟩ := homeo
    exact (sphere_diffeomorph_iff_local_section (positive_of_known_dimension hn)).1
      (h n hn M e.toHomotopyEquiv)

end OMA.R_PoincareConjecture_poincare_conjecture_variants_smooth_known_cases_R1
