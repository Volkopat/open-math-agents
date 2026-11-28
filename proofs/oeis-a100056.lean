import OMAStatements.S_oeis_a100056

/-!
At n = 5, the fractional parts order the entries as 5,2,4,1,3, whose
adjacent jumps total 10. The permutation 2,5,1,4,3 has jump sum 11.
The finite enumeration below also certifies that 11 is the true maximum.
-/

open OMA.S_oeis_a100056 Finset

private def oma_golden_rank (j : ℕ) : ℕ := [0,3,1,4,2,0][j]!

private def oma_golden_floor (j : ℕ) : ℤ := [0,1,3,4,6,8][j]!

private lemma oma_golden_lt {i j : ℕ} (hi : i ∈ Icc 1 5) (hj : j ∈ Icc 1 5) :
    Int.fract ((i : ℝ)*τ) < Int.fract ((j : ℝ)*τ) ↔ oma_golden_rank i < oma_golden_rank j := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg 5
  have ht : 161/100 < τ ∧ τ < 162/100 := by
    unfold τ
    constructor <;> nlinarith
  have tab (h : ℕ) (hh : h ∈ Icc 1 5) : ⌊(h : ℝ) * τ⌋ = oma_golden_floor h := by
    obtain ⟨l,u⟩ := Finset.mem_Icc.mp hh
    apply Int.floor_eq_iff.mpr
    interval_cases h <;> norm_num [oma_golden_floor] <;> constructor <;> linarith
  rw [Int.fract, Int.fract, tab i hi, tab j hj]
  obtain ⟨il,iu⟩ := Finset.mem_Icc.mp hi
  obtain ⟨jl,ju⟩ := Finset.mem_Icc.mp hj
  interval_cases i <;> interval_cases j <;> norm_num [oma_golden_rank,oma_golden_floor] <;> linarith

private def oma_golden_adj (q : ℕ × ℕ) : Bool :=
  decide (oma_golden_rank q.1 < oma_golden_rank q.2 ∧
    ((Icc 1 5).filter (fun g => oma_golden_rank q.1 < oma_golden_rank g ∧
      oma_golden_rank g < oma_golden_rank q.2)).card = 0)

private lemma oma_golden_value : a 5 = 10 := by
  classical
  unfold a
  have eqf : ((Icc 1 5 ×ˢ Icc 1 5).filter fun q => Consecutive 5 q.1 q.2) =
      ((Icc 1 5 ×ˢ Icc 1 5).filter fun q => oma_golden_adj q) := by
    apply Finset.filter_congr
    rintro ⟨i,j⟩ h
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp h
    simp only [Consecutive,hi,hj,true_and,oma_golden_adj,decide_eq_true_eq,
      Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    rw [oma_golden_lt hi hj]
    refine and_congr_right fun _ => ?_
    constructor <;> intro H g hg
    · simpa only [← oma_golden_lt hi hg, ← oma_golden_lt hg hj] using @H g hg
    · simpa only [oma_golden_lt hi hg, oma_golden_lt hg hj] using @H g hg
  rw [eqf]
  decide

/-- The 120 permutations give a maximum of 11 at n=5. -/
private lemma true_maximum_five :
    IsGreatest {s : ℕ | ∃ l : List ℕ, l.Perm (List.range' 1 5) ∧ jumpSum l = s} 11 := by
  constructor
  · exact ⟨[2,5,1,4,3], by decide, by decide⟩
  · rintro s ⟨l,hl,rfl⟩
    have allsmall : ((List.range' 1 5).permutations'.all fun w => decide (jumpSum w ≤ 11)) = true := by decide
    have h := List.all_eq_true.mp allsmall l (List.mem_permutations'.mpr hl)
    exact of_decide_eq_true h

private lemma refute_maximum (hfive : a 5 = 10) : ¬ (type_of% @OMA.S_oeis_a100056.main) := by
  intro claim
  have comparison := (claim 5 (by decide)).2 true_maximum_five.1
  rw [hfive] at comparison
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a100056.main) :=
  refute_maximum oma_golden_value
