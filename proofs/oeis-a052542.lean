import OMAStatements.S_oeis_a052542

namespace P052542
open OMA.S_oeis_a052542

def V (m : ℕ) : Finset (List ℕ) :=
  ((Finset.univ : Finset (Composition m)).filter (fun c => ∀ p ∈ c.blocks, Odd p)).image
    Composition.blocks

lemma mem_V (m : ℕ) (l : List ℕ) : l ∈ V m ↔ (∀ x ∈ l, Odd x) ∧ l.sum = m := by
  unfold V
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨hc, c.blocks_sum⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨l, fun hx => (h1 _ hx).pos, h2⟩, h1, rfl⟩

lemma rhs_eq (m : ℕ) : ∑ c ∈ (Finset.univ : Finset (Composition m)).filter
    (fun c => ∀ p ∈ c.blocks, Odd p), 2 ^ c.length = ∑ l ∈ V m, 2 ^ l.length := by
  unfold V
  rw [Finset.sum_image]
  intro x _ y _ h
  exact Composition.ext h

def g (m : ℕ) : ℕ := ∑ l ∈ V m, 2 ^ l.length

lemma partA (m : ℕ) : ∑ l ∈ (V (m+1)).filter (fun l => l.head? = some 1), 2 ^ l.length
    = 2 * g m := by
  unfold g
  rw [Finset.mul_sum]
  apply Finset.sum_nbij' List.tail (List.cons 1)
  · intro l hl
    simp only [Finset.mem_filter, mem_V] at hl ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hl
    rcases l with _ | ⟨x, t⟩
    · simp at h3
    · simp at h3
      subst h3
      simp at h1 h2 ⊢
      exact ⟨h1, by omega⟩
  · intro l hl
    simp only [Finset.mem_filter, mem_V] at hl ⊢
    obtain ⟨h1, h2⟩ := hl
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact odd_one
      · exact h1 x hx
    · simp [h2]; omega
  · intro l hl
    simp only [Finset.mem_filter, mem_V] at hl
    obtain ⟨⟨h1, h2⟩, h3⟩ := hl
    rcases l with _ | ⟨x, t⟩
    · simp at h3
    · simp at h3
      simp [h3]
  · intro l _
    rfl
  · intro l hl
    simp only [Finset.mem_filter, mem_V] at hl
    obtain ⟨⟨h1, h2⟩, h3⟩ := hl
    rcases l with _ | ⟨x, t⟩
    · simp at h3
    · simp [pow_succ]; ring

lemma partB (m : ℕ) : ∑ l ∈ (V (m+3)).filter (fun l => ¬ l.head? = some 1), 2 ^ l.length
    = g (m+1) := by
  unfold g
  apply Finset.sum_nbij' (List.modifyHead (fun x => x - 2)) (List.modifyHead (fun x => x + 2))
  · intro l hl
    simp only [Finset.mem_filter, mem_V] at hl ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hl
    rcases l with _ | ⟨x, t⟩
    · simp at h2
    · simp only [List.head?_cons, Option.some.injEq] at h3
      simp only [List.mem_cons, forall_eq_or_imp, List.sum_cons] at h1 h2
      have hx := h1.1
      rw [Nat.odd_iff] at hx
      simp only [List.modifyHead_cons, List.mem_cons, forall_eq_or_imp, List.sum_cons]
      refine ⟨⟨?_, h1.2⟩, by omega⟩
      rw [Nat.odd_iff]; omega
  · intro l hl
    simp only [Finset.mem_filter, mem_V] at hl ⊢
    obtain ⟨h1, h2⟩ := hl
    rcases l with _ | ⟨x, t⟩
    · simp at h2
    · simp only [List.mem_cons, forall_eq_or_imp, List.sum_cons] at h1 h2
      have hx := h1.1
      rw [Nat.odd_iff] at hx
      simp only [List.modifyHead_cons, List.mem_cons, forall_eq_or_imp, List.sum_cons,
        List.head?_cons, Option.some.injEq]
      refine ⟨⟨⟨?_, h1.2⟩, by omega⟩, by omega⟩
      rw [Nat.odd_iff]; omega
  · intro l hl
    simp only [Finset.mem_filter, mem_V] at hl
    obtain ⟨⟨h1, h2⟩, h3⟩ := hl
    rcases l with _ | ⟨x, t⟩
    · rfl
    · simp only [List.head?_cons, Option.some.injEq] at h3
      simp only [List.mem_cons, forall_eq_or_imp, List.sum_cons] at h1 h2
      have hx := h1.1
      rw [Nat.odd_iff] at hx
      simp only [List.modifyHead_cons, List.cons.injEq, and_true]
      omega
  · intro l _
    rcases l with _ | ⟨x, t⟩
    · rfl
    · simp
  · intro l _
    rcases l with _ | ⟨x, t⟩
    · rfl
    · simp

lemma g_rec (m : ℕ) : g (m+3) = 2 * g (m+2) + g (m+1) := by
  rw [← partA (m+2), ← partB m]
  unfold g
  rw [Finset.sum_filter_add_sum_filter_not]

lemma V1 : V 1 = {[1]} := by
  ext l
  simp only [mem_V, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
    · simp at h2
    · simp at h2 ⊢; exact h2
    · have hx := (h1 x (by simp)).pos
      have hy := (h1 y (by simp)).pos
      simp at h2; omega
  · rintro rfl
    exact ⟨by simp, rfl⟩

lemma V2 : V 2 = {[1, 1]} := by
  ext l
  simp only [mem_V, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
    · simp at h2
    · have hx := h1 x (by simp)
      rw [Nat.odd_iff] at hx
      simp at h2; omega
    · have hx := (h1 x (by simp)).pos
      have hy := (h1 y (by simp)).pos
      simp at h2 ⊢; omega
    · have hx := (h1 x (by simp)).pos
      have hy := (h1 y (by simp)).pos
      have hz := (h1 z (by simp)).pos
      simp at h2; omega
  · rintro rfl
    exact ⟨by simp, rfl⟩

lemma key (k : ℕ) : a (k+1) = g (k+1) ∧ a (k+2) = g (k+2) := by
  induction k with
  | zero => exact ⟨by simp [g, V1]; rfl, by simp [g, V2]; rfl⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    show a (k+3) = g (k+3)
    have h : a (k+3) = 2 * a (k+2) + a (k+1) := rfl
    rw [h, g_rec, ih.1, ih.2]

end P052542

theorem OMA.solution : type_of% @OMA.S_oeis_a052542.main := by
  intro n hn
  rw [P052542.rhs_eq]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (P052542.key k).1
