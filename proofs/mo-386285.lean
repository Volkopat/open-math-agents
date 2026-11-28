import OMAStatements.S_mo_386285
import Mathlib

namespace Mo386285aux

/-- The lower limit topology on the real line: a set is open when with each point it
contains a half-open interval starting at that point. -/
def sorg : TopologicalSpace ℝ where
  IsOpen s := ∀ x ∈ s, ∃ ε : ℝ, 0 < ε ∧ Set.Ico x (x + ε) ⊆ s
  isOpen_univ := fun x _ => ⟨1, one_pos, Set.subset_univ _⟩
  isOpen_inter := by
    intro s t hs ht x hx
    obtain ⟨e1, he1, h1⟩ := hs x hx.1
    obtain ⟨e2, he2, h2⟩ := ht x hx.2
    refine ⟨min e1 e2, lt_min he1 he2, ?_⟩
    intro y hy
    have m1 : min e1 e2 ≤ e1 := min_le_left _ _
    have m2 : min e1 e2 ≤ e2 := min_le_right _ _
    exact ⟨h1 ⟨hy.1, by linarith [hy.2]⟩, h2 ⟨hy.1, by linarith [hy.2]⟩⟩
  isOpen_sUnion := by
    intro S hS x hx
    obtain ⟨t, htS, hxt⟩ := hx
    obtain ⟨e, he, h⟩ := hS t htS x hxt
    exact ⟨e, he, fun y hy => ⟨t, htS, h hy⟩⟩

lemma isOpen_Ico (a c : ℝ) : @IsOpen ℝ sorg (Set.Ico a c) := by
  intro z hz
  refine ⟨c - z, by linarith [hz.2], ?_⟩
  intro w hw
  exact ⟨le_trans hz.1 hw.1, by linarith [hw.2]⟩

lemma t2 : @T2Space ℝ sorg := by
  let _inst : TopologicalSpace ℝ := sorg
  refine ⟨?_⟩
  intro x y hxy
  rcases lt_or_gt_of_ne hxy with h | h
  · refine ⟨Set.Ico x y, Set.Ico y (y + 1), isOpen_Ico _ _, isOpen_Ico _ _,
      ⟨le_refl _, h⟩, ⟨le_refl _, by linarith⟩, ?_⟩
    rw [Set.disjoint_left]
    intro z hz1 hz2
    linarith [hz1.2, hz2.1]
  · refine ⟨Set.Ico x (x + 1), Set.Ico y x, isOpen_Ico _ _, isOpen_Ico _ _,
      ⟨le_refl _, by linarith⟩, ⟨le_refl _, h⟩, ?_⟩
    rw [Set.disjoint_left]
    intro z hz1 hz2
    linarith [hz1.1, hz2.2]

lemma add_cont : @Continuous (ℝ × ℝ) ℝ (@instTopologicalSpaceProd ℝ ℝ sorg sorg) sorg
    (fun xy : ℝ × ℝ => xy.1 + xy.2) := by
  let _inst : TopologicalSpace ℝ := sorg
  rw [continuous_def]
  intro s hs
  rw [isOpen_prod_iff]
  intro a c hac
  obtain ⟨ε, hε, h⟩ := hs (a + c) hac
  refine ⟨Set.Ico a (a + ε / 2), Set.Ico c (c + ε / 2), isOpen_Ico _ _, isOpen_Ico _ _,
    ⟨le_refl _, by linarith⟩, ⟨le_refl _, by linarith⟩, ?_⟩
  rintro ⟨p, q⟩ ⟨hp, hq⟩
  exact h ⟨by linarith [hp.1, hq.1], by linarith [hp.2, hq.2]⟩

lemma neg_not_cont : ¬ @Continuous ℝ ℝ sorg sorg (fun x : ℝ => -x) := by
  intro hc
  let _inst : TopologicalSpace ℝ := sorg
  have h1 := (continuous_def.mp hc) (Set.Ico 0 1) (isOpen_Ico 0 1)
  obtain ⟨ε, hε, h⟩ := h1 0 (by simp)
  have h2 : ε / 2 ∈ Set.Ico (0 : ℝ) (0 + ε) := ⟨by linarith, by linarith⟩
  have h3 := h h2
  have h4 : (0 : ℝ) ≤ -(ε / 2) := h3.1
  linarith

end Mo386285aux

theorem OMA.solution : type_of% @OMA.S_mo_386285.main := by
  refine ⟨ℝ, inferInstance, Mo386285aux.sorg, ?_, ?_, ?_⟩
  · exact Mo386285aux.t2
  · exact Mo386285aux.add_cont
  · exact Mo386285aux.neg_not_cont
