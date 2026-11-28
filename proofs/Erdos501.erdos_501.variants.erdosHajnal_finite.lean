import FormalConjectures.ErdosProblems.«501»

/-! Finite independent sets, following @Genbox (#711) and @joshuadc11 (#14696). -/

open Set MeasureTheory
open scoped ENNReal

theorem OMA.solution : type_of% @Erdos501.erdos_501.variants.erdosHajnal_finite := by
  classical
  intro n A hBnd hMeas
  let B (t : ℝ) (m : ℕ) : Set ℝ := {x | t < x ∧ x < m ∧ ∀ z ∈ A x, z < m}
  have monoB t : Monotone (B t) := fun i j hij x hx =>
    have h : (i : ℝ) ≤ j := by exact_mod_cast hij
    ⟨hx.1, hx.2.1.trans_le h, fun z hz => (hx.2.2 z hz).trans_le h⟩
  have unionB t : (⋃ m, B t m) = Ioi t := ext fun x =>
    ⟨fun hx => (mem_iUnion.mp hx).choose_spec.1, fun hx => by
      obtain ⟨R, hR⟩ := (hBnd x).bddAbove
      obtain ⟨m, hm⟩ := exists_nat_gt (max x R)
      exact mem_iUnion.mpr ⟨m, hx, (le_max_left x R).trans_lt hm, fun z hz =>
        (hR hz).trans_lt
          ((le_max_right x R).trans_lt hm)⟩⟩
  have above (k : ℕ) (t : ℝ) : ∃ X : Finset ℝ, X.card = k ∧
      (∀ x ∈ X, t < x) ∧ (X : Set ℝ).Pairwise fun x y => x ∉ A y := by
    induction k generalizing t with
    | zero => exact ⟨∅, by simp⟩
    | succ k ih =>
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (k : ℝ≥0∞) < volume (B t m) := by
        apply lt_iSup_iff.mp
        rw [← (monoB t).measure_iUnion, unionB, Real.volume_Ioi]
        exact ENNReal.natCast_lt_top k
      obtain ⟨Y, hYc, hYa, hYi⟩ := ih m
      have hU : volume (⋃ y ∈ Y, A y) ≤ k := (measure_biUnion_finset_le Y A).trans <|
        (Finset.sum_le_sum fun y _ => (hMeas y).le).trans_eq (by simp [hYc])
      obtain ⟨x, hx, hxA⟩ := not_subset.mp fun hSub => not_le_of_gt hm ((measure_mono hSub).trans hU)
      have hxN : x ∉ Y := fun hxy => (not_lt_of_ge (hYa x hxy).le) hx.2.1
      refine ⟨insert x Y, by simp [hxN, hYc], fun z hz => ?_, ?_⟩
      · rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx.1
        · exact hx.1.trans (hx.2.1.trans (hYa z hz))
      · rw [Finset.coe_insert, pairwise_insert]
        exact ⟨hYi, fun y hy _ => ⟨fun hxy => hxA (mem_iUnion₂.mpr ⟨y, hy, hxy⟩),
          fun hyx => (not_lt_of_ge (hYa y hy).le) (hx.2.2 y hyx)⟩⟩
  obtain ⟨X, hX, -, hI⟩ := above n 0
  exact ⟨X, hX.ge, hI⟩
