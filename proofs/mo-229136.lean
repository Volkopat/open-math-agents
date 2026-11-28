import OMAStatements.S_mo_229136

/-! On a fair two-point space, use the same nontrivial event in alternating rows.
Each column has at most one nontrivial event, but the first two row tails both contain it. -/

namespace MO229136Proof

open MeasureTheory OMA.S_mo_229136
open scoped ENNReal

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSingletonClass Bool where
  measurableSet_singleton _ := trivial

private noncomputable def coin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.count

private instance : IsProbabilityMeasure coin where
  measure_univ := by
    rw [coin, Measure.smul_apply, smul_eq_mul, ← Finset.coe_univ,
      Measure.count_apply_finset, Finset.card_univ, Fintype.card_bool]
    simpa only [Nat.cast_ofNat] using ENNReal.div_mul_cancel (a := 2) (b := 1) (by norm_num) (by norm_num)

private def event : Set Bool := {true}

private lemma coin_event : coin.real event = 1 / 2 := by
  norm_num [coin, event, measureReal_def, Measure.count_singleton]

private def col (i n : ℕ) : Set Bool :=
  if i = n % 2 then event else Set.univ

private def tailEvent (i : ℕ) : Set Bool :=
  if i < 2 then event else Set.univ

private lemma col_factors (n : ℕ) (s : Finset ℕ) :
    Factors coin (fun i => col i n) s := by
  unfold Factors
  by_cases h : n % 2 ∈ s
  · have hInter : (⋂ i ∈ s, col i n) = event := by
      ext x
      simp only [Set.mem_iInter]
      refine ⟨fun hx => ?_, fun hx i hi => ?_⟩
      · simpa [col] using hx (n % 2) h
      · by_cases hi' : i = n % 2 <;> simp [col, hi', hx]
    rw [hInter, Finset.prod_eq_single (n % 2)]
    · simp [col]
    · intro i hi hne
      change coin.real (col i n) = 1
      rw [col, if_neg hne, probReal_univ]
    · exact fun hn => False.elim (hn h)
  · have hcol (i : ℕ) (hi : i ∈ s) : col i n = Set.univ := by
      have hne : i ≠ n % 2 := by
        rintro rfl
        exact h hi
      simp [col, hne]
    have hInter : (⋂ i ∈ s, col i n) = Set.univ := by
      ext x
      constructor
      · intro _
        exact Set.mem_univ x
      · intro _
        simp only [Set.mem_iInter]
        intro i hi
        rw [hcol i hi]
        exact Set.mem_univ x
    rw [hInter, probReal_univ]
    symm
    apply Finset.prod_eq_one
    intro i hi
    change coin.real (col i n) = 1
    rw [hcol i hi, probReal_univ]

private lemma tail_measurable (i N : ℕ) :
    MeasurableSet[MeasurableSpace.generateFrom (Set.range (fun k => col i (N + k)))] (tailEvent i) := by
  by_cases hi : i < 2
  · rw [tailEvent, if_pos hi]
    apply MeasurableSpace.measurableSet_generateFrom
    by_cases hp : N % 2 = i
    · exact ⟨0, by simp [col, hp]⟩
    · have hpar : (N + 1) % 2 = i := by omega
      exact ⟨1, by simp [col, hpar]⟩
  · rw [tailEvent, if_neg hi]
    exact MeasurableSet.univ

private lemma tail_not_factors : ¬ Factors coin tailEvent ({0, 1} : Finset ℕ) := by
  unfold Factors
  have hInter : (⋂ i ∈ ({0, 1} : Finset ℕ), tailEvent i) = event := by
    ext x
    simp [tailEvent]
  rw [hInter, Finset.prod_insert (by decide), Finset.prod_singleton]
  norm_num [tailEvent, coin_event]

end MO229136Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_229136.main) := by
  intro h
  open MO229136Proof in
  exact tail_not_factors (h Bool coin col tailEvent (fun _ _ => trivial)
    (fun n s _ => col_factors n s) tail_measurable {0, 1})
