import OMAStatements.S_mo_229136

/-!
Retains @romechenko's fair-coin counterexample, PR #16095, pinned at
https://github.com/lefttosolve2/open-math-agents/blob/b78c0c84e362444c8abcd2f695b9329974d73a3a/proofs/mo-229136.lean
Statement by @zarnab222-dev, PR #12535. This revision combines the bounded
intersection cases and uses Finset.prod_ite_eq' for the matching product.
Original question: BCLC, https://mathoverflow.net/questions/229136 (CC BY-SA 3.0).
-/

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
  have hInter : (⋂ i ∈ s, col i n) = if n % 2 ∈ s then event else Set.univ := by
    ext x
    simp only [col, Set.mem_iInter, Set.mem_ite_univ_right]
    constructor
    · intro h hk
      exact h (n % 2) hk rfl
    · intro h i hi he
      subst i
      exact h hi
  rw [hInter]
  simp only [col, apply_ite, probReal_univ, Finset.prod_ite_eq']
  split_ifs <;> rfl

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
