import OMAStatements.S_wp_fujita_conjecture

-- Reduction of Fujita's conjecture. Credit: @Pixelstorm44
namespace OMA.R_wp_fujita_conjecture_R1

open OMA.S_wp_fujita_conjecture
open scoped Manifold ContDiff

/-- At the borderline exponent only ordinary evaluation matters. -/
def H1 : Prop :=
  ∀ (n : ℕ) (_ : 0 < n) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold (𝓘(ℂ, Coordinates n)) ω M]
    (L : HolomorphicLineBundle n M), IsPositive L →
    SpannedBySections L (adjointTransition L (n + 1))

/-- A two-point functional with coefficient 1 at the second point cannot
annihilate the entire section space. No zero is prescribed for the witness. -/
def H2 : Prop :=
  ∀ (n : ℕ) (_ : 0 < n) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold (𝓘(ℂ, Coordinates n)) ω M]
    (L : HolomorphicLineBundle n M), IsPositive L → ∀ m, n + 2 ≤ m →
    ∀ x y : M, x ≠ y → ∀ c : ℂ, ∃ s : GlobalSection L (adjointTransition L m),
      s.val y (L.chart y y) ≠ c * s.val x (L.chart x x)

/-- The value and the derivative in any nonzero direction have no nonzero
linear relation on global sections. -/
def H3 : Prop :=
  ∀ (n : ℕ) (_ : 0 < n) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold (𝓘(ℂ, Coordinates n)) ω M]
    (L : HolomorphicLineBundle n M), IsPositive L → ∀ m, n + 2 ≤ m →
    ∀ (x : M) (v : Coordinates n), v ≠ 0 → ∀ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) →
      ∃ s : GlobalSection L (adjointTransition L m),
        a * s.val x (L.chart x x) + b * fderiv ℂ (s.val x) (L.chart x x) v ≠ 0

/-- Each chart in dimension zero contains just its indexing point. Thus an
indicator in the frame index is a global section for the adjoint cocycle. -/
lemma dimension_zero {M : Type*} [TopologicalSpace M] [ChartedSpace (Coordinates 0) M]
    (L : HolomorphicLineBundle 0 M) (m : ℕ) : VeryAmple L (adjointTransition L m) := by
  classical
  have only (i x : M) (hx : x ∈ (L.chart i).source) : x = i :=
    (L.chart i).injOn hx (L.mem_source i) (Subsingleton.elim _ _)
  have diag (i : M) : adjointTransition L m i i i = 1 := by
    have h := L.transition_comp i i i i (L.mem_source i) (L.mem_source i) (L.mem_source i)
    have hn := L.transition_ne i i i (L.mem_source i) (L.mem_source i)
    have ht : L.transition i i i = 1 := (mul_eq_left₀ hn).mp h
    unfold adjointTransition
    have hd : (fderiv ℂ (L.chart i ∘ (L.chart i).symm) (L.chart i i)).toLinearMap =
        LinearMap.id := by ext v k; exact Fin.elim0 k
    simp [hd, ht]
  have peak (p : M) : ∃ s : GlobalSection L (adjointTransition L m),
      ∀ i z, s.val i z = if i = p then 1 else 0 := by
    refine ⟨⟨fun i _ => if i = p then 1 else 0, ?_, ?_⟩, fun _ _ => rfl⟩
    · intro i
      exact analyticOnNhd_const
    · intro i j x hi hj
      have hxi := only i x hi
      have hxj := only j x hj
      subst i
      subst j
      simp [diag]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨s, hs⟩ := peak x
    exact ⟨s, by simp [hs]⟩
  · intro x y hxy
    obtain ⟨s, hs⟩ := peak y
    exact ⟨s, by simp [hs, hxy], by simp [hs]⟩
  · intro x v hv
    exact (hv (Subsingleton.elim _ _)).elim

/-- Linear combinations glue in every frame and commute with the local first derivative. -/
lemma subtract_multiple {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    {L : HolomorphicLineBundle n M} {g : M → M → M → ℂ}
    (s t : GlobalSection L g) (c : ℂ) :
    ∃ u : GlobalSection L g, (∀ i z, u.val i z = s.val i z - c * t.val i z) ∧
      ∀ i v, fderiv ℂ (u.val i) (L.chart i i) v =
        fderiv ℂ (s.val i) (L.chart i i) v - c * fderiv ℂ (t.val i) (L.chart i i) v := by
  refine ⟨⟨fun i z => s.val i z - c * t.val i z, ?_, ?_⟩, fun _ _ => rfl, ?_⟩
  · intro i
    exact (s.property.1 i).sub (analyticOnNhd_const.mul (t.property.1 i))
  · intro i j x hi hj
    dsimp only
    rw [s.property.2 i j x hi hj, t.property.2 i j x hi hj]
    ring
  · intro i v
    have hi := (L.chart i).map_source (L.mem_source i)
    have hs := (s.property.1 i _ hi).differentiableAt
    have ht := (t.property.1 i _ hi).differentiableAt
    change fderiv ℂ (s.val i - c • t.val i) _ v = _
    rw [fderiv_sub hs (ht.const_smul c), fderiv_const_smul ht c]
    rfl

lemma assemble : H1 → H2 → H3 → type_of% @OMA.S_wp_fujita_conjecture.main.{0} := by
  intro border pair jet n M _ _ _ _ _ L hL m
  by_cases hn : n = 0
  · subst n
    have h := dimension_zero L m
    exact ⟨fun _ => h.1, fun _ => h⟩
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  suffices large : n + 2 ≤ m → VeryAmple L (adjointTransition L m) by
    refine ⟨fun hm => ?_, large⟩
    by_cases he : m = n + 1
    · subst m
      exact border n hn' M L hL
    · exact (large (by omega)).1
  intro hm
  have J := jet n hn' M L hL m hm
  have spanAt : SpannedBySections L (adjointTransition L m) := by
    intro x
    let v : Coordinates n := fun _ => 1
    have hv : v ≠ 0 := fun h => one_ne_zero (congrFun h ⟨0, hn'⟩)
    obtain ⟨s, hs⟩ := J x v hv 1 0 (Or.inl one_ne_zero)
    exact ⟨s, by simpa using hs⟩
  refine ⟨spanAt, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨t, ht⟩ := spanAt x
    obtain ⟨s, hs⟩ := pair n hn' M L hL m hm x y hxy (t.val y (L.chart y y) / t.val x (L.chart x x))
    obtain ⟨u, hu, _⟩ := subtract_multiple s t (s.val x (L.chart x x) / t.val x (L.chart x x))
    refine ⟨u, by simp [hu, ht], ?_⟩
    rw [hu, sub_ne_zero]
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
  · intro x v hv
    obtain ⟨t, ht⟩ := spanAt x
    let d := fderiv ℂ (t.val x) (L.chart x x) v
    obtain ⟨s, hs⟩ := J x v hv (-d / t.val x (L.chart x x)) 1 (Or.inr one_ne_zero)
    obtain ⟨u, hu, du⟩ := subtract_multiple s t (s.val x (L.chart x x) / t.val x (L.chart x x))
    refine ⟨u, by simp [hu, ht], ?_⟩
    rw [du]
    convert hs using 1
    dsimp [d]
    ring

/-- A compact manifold is covered by finitely many chart sources. The inverse
chart maps therefore give a surjection from a small type onto the manifold. -/
lemma small_carrier {n : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (Coordinates n) M] (L : HolomorphicLineBundle n M) : Small.{0} M := by
  classical
  obtain ⟨t, cover⟩ := isCompact_univ.elim_finite_subcover (fun i => (L.chart i).source)
    (fun i => (L.chart i).open_source) (fun x _ => Set.mem_iUnion.mpr ⟨x, L.mem_source x⟩)
  apply small_of_surjective.{0} (f := fun p : (↑t : Type _) × Coordinates n => (L.chart p.1.val).symm p.2)
  intro x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (cover (Set.mem_univ x))
  obtain ⟨hit, hxi⟩ := Set.mem_iUnion.mp hi
  exact ⟨(⟨i, hit⟩, L.chart i x), (L.chart i).left_inv hxi⟩

/-- Reindex the bundle charts along a homeomorphism. Their changes of
coordinates agree on the entire coordinate type, including in the Jacobian. -/
lemma resize (smallCase : type_of% @OMA.S_wp_fujita_conjecture.main.{0}) :
    type_of% @OMA.S_wp_fujita_conjecture.main := by
  classical
  intro n M _ _ _ _ _ L hL m
  let : Small.{0} M := small_carrier L
  let S := Shrink.{0} M
  let e : S ≃ M := (equivShrink M).symm
  let := e.topologicalSpace
  let f : S ≃ₜ M := e.homeomorph
  let := f.symm.compactSpace
  let := f.symm.t2Space
  let C := fun i : S => f.transOpenPartialHomeomorph (L.chart (f i))
  let : ChartedSpace (Coordinates n) S :=
    ⟨Set.range C, C, fun i => L.mem_source (f i), fun i => Set.mem_range_self i⟩
  have cancel (i j : S) :
      (C i).symm.trans (C j) = (L.chart (f i)).symm.trans (L.chart (f j)) := by
    apply OpenPartialHomeomorph.ext
    · intro z
      change L.chart (f j) (f (f.symm _)) = _
      rw [f.apply_symm_apply]
      rfl
    · intro z
      change L.chart (f i) (f (f.symm _)) = _
      rw [f.apply_symm_apply]
      rfl
    · ext z
      change (z ∈ (L.chart (f i)).target ∧ f (f.symm ((L.chart (f i)).symm z)) ∈ (L.chart (f j)).source) ↔ _
      rw [f.apply_symm_apply]
      rfl
  let : IsManifold (𝓘(ℂ, Coordinates n)) ω S := by
    refine { compatible := ?_ }
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    rw [cancel]
    exact IsManifold.compatible_of_mem_maximalAtlas (L.compatible _) (L.compatible _)
  let B : HolomorphicLineBundle n S := {
    chart := C
    mem_source := fun i => L.mem_source (f i)
    compatible := fun i => IsManifold.chart_mem_maximalAtlas i
    transition := fun i j x => L.transition (f i) (f j) (f x)
    transition_ne := fun i j x => L.transition_ne (f i) (f j) (f x)
    transition_comp := fun i j k x => L.transition_comp (f i) (f j) (f k) (f x)
    transition_holomorphic := by
      intro i j
      change AnalyticOnNhd ℂ (fun z => L.transition (f i) (f j) (f (f.symm ((L.chart (f i)).symm z))))
        {z | z ∈ (L.chart (f i)).target ∧ f (f.symm ((L.chart (f i)).symm z)) ∈ (L.chart (f j)).source}
      simp only [Homeomorph.apply_symm_apply]
      exact L.transition_holomorphic (f i) (f j) }
  have hB : IsPositive B := by
    obtain ⟨h, hs, hp, hg, hc⟩ := hL
    exact ⟨fun i => h (f i), fun i => hs _, fun i => hp _, fun i j x => hg _ _ _, fun i => hc _⟩
  have adj (i j x : S) : adjointTransition B m i j x = adjointTransition L m (f i) (f j) (f x) := by
    have he : B.chart i ∘ (B.chart j).symm = L.chart (f i) ∘ (L.chart (f j)).symm := by
      funext z
      change L.chart (f i) (f (f.symm _)) = _
      rw [f.apply_symm_apply]
      rfl
    unfold adjointTransition
    rw [he]
    rfl
  have liftSection (s : GlobalSection B (adjointTransition B m)) :
      ∃ t : GlobalSection L (adjointTransition L m), ∀ i, t.val (f i) = s.val i := by
    refine ⟨⟨fun x => s.val (f.symm x), ?_, ?_⟩, fun i => by simp⟩
    · intro x
      have hs := s.property.1 (f.symm x)
      change AnalyticOnNhd ℂ _ (L.chart (f (f.symm x))).target at hs
      simpa using hs
    · intro i j x hi hj
      obtain ⟨i, rfl⟩ := f.surjective i
      obtain ⟨j, rfl⟩ := f.surjective j
      obtain ⟨x, rfl⟩ := f.surjective x
      have eq := s.property.2 i j x hi hj
      rw [adj] at eq
      simp only [Homeomorph.symm_apply_apply]
      exact eq
  have spanLift (h : SpannedBySections B (adjointTransition B m)) :
      SpannedBySections L (adjointTransition L m) := by
    rintro x
    obtain ⟨i, rfl⟩ := f.surjective x
    obtain ⟨s, hs⟩ := h i
    obtain ⟨t, ht⟩ := liftSection s
    exact ⟨t, by rw [ht]; exact hs⟩
  obtain ⟨hs, hv⟩ := smallCase n S B hB m
  refine ⟨fun hm => spanLift (hs hm), fun hm => ?_⟩
  obtain ⟨hgen, hpair, hjet⟩ := hv hm
  refine ⟨spanLift hgen, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨i, rfl⟩ := f.surjective x
    obtain ⟨j, rfl⟩ := f.surjective y
    obtain ⟨s, si, sj⟩ := hpair i j (fun h => hxy (congrArg f h))
    obtain ⟨t, ht⟩ := liftSection s
    exact ⟨t, by rw [ht]; exact si, by rw [ht]; exact sj⟩
  · intro x v hne
    obtain ⟨i, rfl⟩ := f.surjective x
    obtain ⟨s, si, sd⟩ := hjet i v hne
    obtain ⟨t, ht⟩ := liftSection s
    exact ⟨t, by rw [ht]; exact si, by rw [ht]; exact sd⟩

theorem main : H1 → H2 → H3 → type_of% @OMA.S_wp_fujita_conjecture.main :=
  fun border pair jet => resize (assemble border pair jet)

end OMA.R_wp_fujita_conjecture_R1
