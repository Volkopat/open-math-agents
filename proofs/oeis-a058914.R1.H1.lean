import OMAReductions.R_oeis_a058914_R1
import Mathlib

/-!
This formalizes the classical lower bound using the rational sign change proposed
by @marcusbuffett in PR #21131. It does not assume uniqueness of the solution
of the functional equations.
-/

open Set

private lemma oma_question_mark_anchors (f : ℝ → ℝ)
    (L : ∀ x ∈ Set.Icc (0 : ℝ) 1, f (x / (x + 1)) = f x / 2)
    (S : ∀ x ∈ Set.Icc (0 : ℝ) 1, f (1 - x) = 1 - f x) :
    f 0 = 0 ∧ f (1/2) = 1/2 ∧ f 1 = 1 ∧
      f (5/12) = 13/32 ∧ f (3/7) = 7/16 := by
  have zero := L 0 (by norm_num)
  have one := S 0 (by norm_num)
  have half := S (1/2) (by norm_num)
  have third := L (1/2) (by norm_num)
  have two_thirds := S (1/3) (by norm_num)
  have two_fifths := L (2/3) (by norm_num)
  have two_sevenths := L (2/5) (by norm_num)
  have five_sevenths := S (2/7) (by norm_num)
  have five_twelfths := L (5/7) (by norm_num)
  have quarter := L (1/3) (by norm_num)
  have three_quarters := S (1/4) (by norm_num)
  have three_sevenths := L (3/4) (by norm_num)
  norm_num at zero one half third two_thirds two_fifths two_sevenths five_sevenths
  norm_num at five_twelfths quarter three_quarters three_sevenths
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

private lemma question_mark_interior (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1))
    (ha : f (5/12) = 13/32) (hb : f (3/7) = 7/16) :
    ∃ x : ℝ, 5/12 < x ∧ x < 3/7 ∧ f x = x := by
  have cont : ContinuousOn (fun x => f x - x) (Icc (5/12) (3/7)) :=
    (hf.mono (Icc_subset_Icc (by norm_num) (by norm_num))).sub continuousOn_id
  have val : (0:ℝ) ∈ Icc (f (5/12) - 5/12) (f (3/7) - 3/7) := by
    rw [ha, hb]
    constructor <;> norm_num
  obtain ⟨x, ⟨hx, hx'⟩, he⟩ := intermediate_value_Icc (by norm_num) cont val
  change f x - x = 0 at he
  have left : x ≠ 5/12 := by rintro rfl; rw [ha] at he; norm_num at he
  have right : x ≠ 3/7 := by rintro rfl; rw [hb] at he; norm_num at he
  exact ⟨x, lt_of_le_of_ne hx left.symm, lt_of_le_of_ne hx' right, by linarith⟩

private lemma five_fixed (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x) (hx' : x < 1/2)
    (h0 : f 0 = 0) (hh : f (1/2) = 1/2) (h1 : f 1 = 1)
    (hfix : f x = x) (href : f (1-x) = 1-x) :
    5 ≤ {y ∈ Set.Icc (0 : ℝ) 1 | f y = y}.encard := by
  classical
  let S : Finset ℝ := {0,x,1/2,1-x,1}
  have size : S.card = 5 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    all_goals repeat' constructor
    all_goals linarith
  have sub : (S : Set ℝ) ⊆ {y ∈ Set.Icc (0 : ℝ) 1 | f y = y} := by
    intro y hy
    simp only [S,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨⟨by linarith,by linarith⟩,by assumption⟩
  simpa [size] using Set.encard_mono sub

theorem OMA.solution : OMA.R_oeis_a058914_R1.H1 := by
  intro f hf hl hs
  obtain ⟨h0, hh, h1, ha, hb⟩ := oma_question_mark_anchors f hl hs
  obtain ⟨x, hx, hx', he⟩ := question_mark_interior f hf ha hb
  have hI : x ∈ Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  exact five_fixed f x (by linarith) (by linarith) h0 hh h1 he (by rw [hs x hI, he])
