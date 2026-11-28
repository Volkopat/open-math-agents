import OMAReductions.R_ZagierMZV_zagier_upper_bound_R1

/-!
Proof of `OMA.R_ZagierMZV_zagier_upper_bound_R1.H2`.

The indices with entries in `{2, 3}` and weight `n` are the compositions of `n` into parts
`2` and `3`; they are automatically admissible. Splitting by the first part, the finite set
`comp n` of these compositions satisfies `comp (n + 3) = 2 :: comp (n + 1) ⊔ 3 :: comp n`,
which is the defining recursion of `zagierDim`.
-/

namespace OMAProof.ZagierCompositions

/-- Compositions of `n` into parts `2` and `3`. -/
def comp : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | 1 => ∅
  | 2 => {[2]}
  | (n + 3) => (comp (n + 1)).image (List.cons 2) ∪ (comp n).image (List.cons 3)

/-- Membership in `comp n`. -/
def Good (n : ℕ) (s : List ℕ) : Prop := (∀ a ∈ s, a = 2 ∨ a = 3) ∧ s.sum = n

theorem good_nil (n : ℕ) : Good n [] ↔ n = 0 := by
  simp [Good, eq_comm]

theorem good_cons (n a : ℕ) (t : List ℕ) :
    Good n (a :: t) ↔ (a = 2 ∨ a = 3) ∧ (∀ b ∈ t, b = 2 ∨ b = 3) ∧ a + t.sum = n := by
  simp only [Good, List.forall_mem_cons, List.sum_cons, and_assoc]

theorem sum_ge (t : List ℕ) (h : ∀ b ∈ t, b = 2 ∨ b = 3) (ht : t ≠ []) : 2 ≤ t.sum := by
  cases t with
  | nil => exact absurd rfl ht
  | cons b u =>
    rw [List.sum_cons]
    rcases h b (by simp) with rfl | rfl <;> omega

theorem eq_nil_of_sum_zero (t : List ℕ) (h : ∀ b ∈ t, b = 2 ∨ b = 3) (hs : t.sum = 0) :
    t = [] := by
  by_contra hne
  have := sum_ge t h hne
  omega

theorem mem_comp : ∀ (n : ℕ) (s : List ℕ), s ∈ comp n ↔ Good n s
  | 0, s => by
    cases s with
    | nil => simp [comp, good_nil]
    | cons a t =>
      simp only [comp, Finset.mem_singleton, reduceCtorEq, false_iff, good_cons]
      rintro ⟨ha, -, hs⟩
      rcases ha with rfl | rfl <;> omega
  | 1, s => by
    cases s with
    | nil => simp [comp, good_nil]
    | cons a t =>
      simp only [comp, Finset.notMem_empty, false_iff, good_cons]
      rintro ⟨ha, -, hs⟩
      rcases ha with rfl | rfl <;> omega
  | 2, s => by
    cases s with
    | nil => simp [comp, good_nil]
    | cons a t =>
      simp only [comp, Finset.mem_singleton, List.cons.injEq, good_cons]
      constructor
      · rintro ⟨rfl, rfl⟩
        simp
      · rintro ⟨ha, ht, hs⟩
        rcases ha with rfl | rfl
        · exact ⟨rfl, eq_nil_of_sum_zero t ht (by omega)⟩
        · omega
  | (n + 3), s => by
    have ih1 := mem_comp (n + 1)
    have ih0 := mem_comp n
    cases s with
    | nil =>
      simp only [comp, Finset.mem_union, Finset.mem_image, reduceCtorEq, and_false,
        exists_false, or_self, good_nil]
    | cons a t =>
      simp only [comp, Finset.mem_union, Finset.mem_image, List.cons.injEq, good_cons]
      constructor
      · rintro (⟨u, hu, rfl, rfl⟩ | ⟨u, hu, rfl, rfl⟩)
        · obtain ⟨h1, h2⟩ := (ih1 u).mp hu
          exact ⟨Or.inl rfl, h1, by omega⟩
        · obtain ⟨h1, h2⟩ := (ih0 u).mp hu
          exact ⟨Or.inr rfl, h1, by omega⟩
      · rintro ⟨ha, ht, hs⟩
        rcases ha with rfl | rfl
        · exact Or.inl ⟨t, (ih1 t).mpr ⟨ht, by omega⟩, rfl, rfl⟩
        · exact Or.inr ⟨t, (ih0 t).mpr ⟨ht, by omega⟩, rfl, rfl⟩

theorem card_comp : ∀ n : ℕ, (comp n).card = ZagierMZV.zagierDim n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (n + 3) => by
    have hdisj : Disjoint ((comp (n + 1)).image (List.cons 2)) ((comp n).image (List.cons 3)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hy
      simp at hv
    rw [comp, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (List.cons_injective),
      Finset.card_image_of_injective _ (List.cons_injective), card_comp (n + 1), card_comp n]
    rfl

theorem admissible_of (s : List ℕ) (h : ∀ a ∈ s, a = 2 ∨ a = 3) : ZagierMZV.AdmissibleIndex s := by
  cases s with
  | nil => trivial
  | cons a t =>
    refine ⟨?_, fun b hb => ?_⟩
    · rcases h a (by simp) with rfl | rfl <;> omega
    · rcases h b (by simp [hb]) with rfl | rfl <;> omega

end OMAProof.ZagierCompositions

open OMAProof.ZagierCompositions in
theorem OMA.solution : OMA.R_ZagierMZV_zagier_upper_bound_R1.H2 := by
  intro n
  refine ⟨comp n, ?_, card_comp n⟩
  ext s
  simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_comp, Good, ZagierMZV.weight]
  constructor
  · rintro ⟨-, hw, h23⟩
    exact ⟨h23, hw⟩
  · rintro ⟨h23, hw⟩
    exact ⟨admissible_of s h23, hw, h23⟩
