import FormalConjectures.ErdosProblems.«501»

/-! Hechler's counterexample uses a well-order of the reals with countable initial segments. -/

open Set MeasureTheory
open scoped Cardinal ENNReal

theorem OMA.solution : type_of% @Erdos501.erdos_501.variants.hechler_CH := by
  classical
  intro hCH
  let α := (ℵ₁ : Cardinal).ord.ToType
  have hcard : #ℝ = #α := by
    rw [Cardinal.mk_real, Cardinal.mk_toType, Cardinal.card_ord]
    exact (Cardinal.lift_inj.mp
      (by simpa only [Cardinal.lift_aleph, Ordinal.lift_one, Cardinal.lift_continuum] using hCH)).symm
  obtain ⟨e⟩ := Cardinal.eq.mp hcard
  let lvl (x : ℝ) : ℕ := ⌈|x|⌉₊
  refine ⟨fun x => {y | e y < e x ∧ lvl y ≤ lvl x}, fun x => ?_, fun x => ?_, fun ⟨X, hX, hInd⟩ => ?_⟩
  · refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).2 ⟨(lvl x : ℝ), fun y hy => ?_⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact (Nat.le_ceil |y|).trans (by exact_mod_cast hy.2)
  · have hiio : (Iio (e x)).Countable :=
      Cardinal.le_aleph0_iff_set_countable.1 (Cardinal.lt_aleph_one_iff.1
        (by simpa [α, Cardinal.mk_toType] using Cardinal.mk_Iio_lt (e x) (by simp [α])))
    change volume _ < 1
    rw [((hiio.preimage e.injective).mono fun _ h => h.1).measure_zero volume]; norm_num
  · have hdec {x y} (hx : x ∈ X) (hy : y ∈ X) (hxy : e x < e y) : lvl y < lvl x :=
      lt_of_not_ge fun hle => hInd hx hy (fun h => hxy.ne (congrArg e h)) ⟨hxy, hle⟩
    obtain ⟨_, ⟨x₀, hx₀, rfl⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min (e '' X) (hX.nonempty.image e)
    have hmaps : MapsTo lvl X (Iic (lvl x₀)) := fun x hx => by
      by_cases h : x = x₀
      · subst x; exact Set.mem_Iic.2 le_rfl
      · exact (hdec hx₀ hx (lt_of_le_of_ne (le_of_not_gt (hmin _ (mem_image_of_mem e hx)))
          fun h' => h (e.injective h').symm)).le
    have hinj : InjOn lvl X := fun x hx y hy hxy => by_contra fun hne =>
      (lt_or_gt_of_ne fun h => hne (e.injective h)).elim
        (fun h => (hdec hx hy h).ne hxy.symm) (fun h => (hdec hy hx h).ne hxy)
    exact hX (Set.Finite.of_injOn hmaps hinj (Set.finite_Iic (lvl x₀)))
