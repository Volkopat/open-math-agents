import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph Matrix Polynomial WrittenOnTheWallII.Test

set_option maxHeartbeats 1000000 in
theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.house_cvetkovic := by
  classical
  let f : ℝ[X] := X^3 - 2*X^2 - 2*X + 2
  let A := HouseGraph.adjMatrix ℝ
  have hA : A = !![0,1,0,1,0; 1,0,1,0,0; 0,1,0,1,1; 1,0,1,0,1; 0,0,1,1,0] := by
    ext i j
    change (if HouseGraph.Adj i j then (1 : ℝ) else 0) = _
    fin_cases i <;> fin_cases j <;>
      norm_num [HouseGraph, fromEdgeSet_adj, Sym2.eq_iff, Fin.ext_iff]
  have hp : A.charpoly = X * (X+2) * f := by
    rw [hA]
    simp [f, Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Matrix.charmatrix_apply, Fin.succAbove]
    ring
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Icc (by norm_num : (-3/2 : ℝ) ≤ -1)
    f.continuous.continuousOn (show 0 ∈ Set.Icc (f.eval (-3/2)) (f.eval (-1)) by norm_num [f])
  obtain ⟨b, hb, hfb⟩ := intermediate_value_Icc' (by norm_num : (1/2 : ℝ) ≤ 1)
    f.continuous.continuousOn (show 0 ∈ Set.Icc (f.eval 1) (f.eval (1/2)) by norm_num [f])
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc (by norm_num : (2 : ℝ) ≤ 3)
    f.continuous.continuousOn (show 0 ∈ Set.Icc (f.eval 2) (f.eval 3) by norm_num [f])
  have hlt : (-2 : ℝ) < a ∧ a < 0 ∧ 0 < b ∧ b < c := by
    rcases ha with ⟨ha₁,ha₂⟩
    rcases hb with ⟨hb₁,hb₂⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith [hc.1]⟩
  rcases hlt with ⟨ha₁,ha₂,hb₁,hb₂⟩
  have hp' : A.charpoly.roots = (-2) ::ₘ a ::ₘ 0 ::ₘ b ::ₘ c ::ₘ 0 := by
    refine roots_eq_of_natDegree_le_card_of_ne_zero
      (S := ⟨(-2) ::ₘ a ::ₘ 0 ::ₘ b ::ₘ c ::ₘ 0, ?_⟩) ?_ (by change A.charpoly.natDegree ≤ 5; simp) (Matrix.charpoly_monic _).ne_zero
    · simp only [Multiset.nodup_cons, Multiset.mem_cons, Multiset.notMem_zero, or_false, not_or,
        Multiset.nodup_zero, and_true]
      repeat' apply And.intro
      all_goals intro h
      all_goals first | linarith | exact h
    · intro x hx
      simp only [Finset.mem_mk, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [hp, hfa, hfb, hfc]
  change A.charpoly.roots.countP (fun x => 0 = x) +
     min (A.charpoly.roots.countP (fun x => 0 < x))
         (A.charpoly.roots.countP (fun x => 0 > x)) = 3
  rw [hp']
  have hc₀ : 0 < c := hb₁.trans hb₂
  simp only [Multiset.countP_cons, Multiset.countP_zero]
  norm_num [ha₂, ha₂.ne, ha₂.ne', ha₂.not_gt,
    hb₁, hb₁.ne, hb₁.ne', hb₁.not_gt, hc₀, hc₀.ne, hc₀.ne', hc₀.not_gt]
