import OMAReductions.R_LittlewoodConjecture_littlewood_conjecture_R1_H2_R1

-- If n * dist(n alpha, Z) takes arbitrarily small values for infinitely many n, then the Littlewood liminf
-- for (alpha, beta) is 0, for every beta.
-- Original Lean proof of the classical remark that the Littlewood conjecture is only open for badly
-- approximable pairs: the third factor dist(n beta, Z) is at most 1/2, so the product is below epsilon
-- infinitely often for every epsilon > 0, and it is nonnegative.
-- An elementary case, not progress on the Littlewood conjecture.

namespace OMA.Littlewood2

open Filter

theorem well_approximable (α β : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, n * distToNearestInt (n * α) < ε) :
    atTop.liminf (fun (n : ℕ) ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) = 0 := by
  have hd0 : ∀ x : ℝ, 0 ≤ distToNearestInt x := fun x => abs_nonneg _
  have hd1 : ∀ x : ℝ, distToNearestInt x ≤ 1 := fun x =>
    le_trans (abs_sub_round x) (by norm_num)
  have hg0 : ∀ n : ℕ, 0 ≤ (n : ℝ) * distToNearestInt (n * α) := fun n =>
    mul_nonneg (Nat.cast_nonneg n) (hd0 _)
  have hnonneg : ∀ n : ℕ,
      0 ≤ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) := fun n =>
    mul_nonneg (hg0 n) (hd0 _)
  have hle : ∀ n : ℕ, (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) ≤
      (n : ℝ) * distToNearestInt (n * α) := fun n =>
    mul_le_of_le_one_right (hg0 n) (hd1 _)
  have hfreq : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) ≤ ε := fun ε hε =>
    (h ε hε).mono fun n hn => le_trans (hle n) hn.le
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)) :=
    isBoundedUnder_of ⟨0, hnonneg⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop
      (fun (n : ℕ) ↦ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)) :=
    IsCoboundedUnder.of_frequently_le (hfreq 1 one_pos)
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    rw [zero_add]
    exact liminf_le_of_frequently_le (hfreq ε hε) hbdd
  · exact le_liminf_of_le hcobdd (Eventually.of_forall hnonneg)

end OMA.Littlewood2

theorem OMA.solution : OMA.R_LittlewoodConjecture_littlewood_conjecture_R1_H2_R1.H1 := by
  intro α β h
  exact OMA.Littlewood2.well_approximable α β h
