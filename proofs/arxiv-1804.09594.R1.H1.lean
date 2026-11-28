import OMAReductions.R_arxiv_1804_09594_R1
import Mathlib

/-! For odd `n ≥ 5`, the terms of `V(2, n)` up to `2n - 1` are `2` and the odd numbers from `n` on:
an odd `z` in `(n, 2n)` has the single representation `2 + (z - 2)`, an even one has none, and
`2n = n + n` is the next even term. -/

open OMA.S_arxiv_1804_09594

namespace A1804

def P (n y : ℕ) : Prop := y = 2 ∨ (n ≤ y ∧ y % 2 = 1)

lemma terms_succ (a b M : ℕ) : terms a b (M + 1) = step a b (terms a b M) (M + 1) := by
  simp [terms, List.range_succ, List.foldl_append]

lemma mem_step {a b : ℕ} {L : List ℕ} {x y : ℕ} :
    y ∈ step a b L x ↔ y ∈ L ∨ (y = x ∧ (x = a ∨ x = b ∨ (b < x ∧ reps L x = 1))) := by
  unfold step
  split_ifs with h
  · simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h' | rfl)
      · exact Or.inl h'
      · exact Or.inr ⟨rfl, h⟩
    · rintro (h' | ⟨rfl, -⟩)
      · exact Or.inl h'
      · exact Or.inr rfl
  · constructor
    · exact Or.inl
    · rintro (h' | ⟨rfl, h'⟩)
      · exact h'
      · exact absurd h' h

lemma terms_zero {n : ℕ} (hn : 5 ≤ n) : terms 2 n 0 = [] := by
  unfold terms
  rw [show List.range (0 + 1) = [0] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  unfold step
  rw [if_neg (by omega)]

lemma bound (a b M : ℕ) : (terms a b M).Nodup ∧ ∀ y ∈ terms a b M, y ≤ M := by
  induction M with
  | zero =>
    unfold terms
    rw [show List.range (0 + 1) = [0] from rfl]
    simp only [List.foldl_cons, List.foldl_nil]
    unfold step
    split_ifs <;> simp
  | succ M ih =>
    rw [terms_succ]
    unfold step
    split_ifs
    · refine ⟨List.nodup_append_comm.mp (List.nodup_cons.mpr ⟨fun h => ?_, ih.1⟩), ?_⟩
      · have := ih.2 _ h; omega
      · intro y hy
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · have := ih.2 y hy; omega
        · exact le_rfl
    · exact ⟨ih.1, fun y hy => (ih.2 y hy).trans (by omega)⟩

lemma reps_eq (L : List ℕ) (hL : L.Nodup) (x : ℕ) :
    reps L x = ((L.toFinset ×ˢ L.toFinset).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = x)).card := by
  unfold reps
  rw [← List.toFinset_card_of_nodup ((hL.product hL).filter _)]
  congr 1
  ext ⟨u, v⟩
  simp [List.mem_product]

lemma reps_val {n : ℕ} (ho : n % 2 = 1) (hn : 5 ≤ n) {z : ℕ} (hz1 : n < z) (hz2 : z ≤ 2 * n)
    {L : List ℕ} (hL : L.Nodup) (hmem : ∀ y, y ∈ L ↔ y ≤ z - 1 ∧ P n y) :
    reps L z = if z % 2 = 1 ∨ z = 2 * n then 1 else 0 := by
  rw [reps_eq L hL]
  split_ifs with h
  · rw [Finset.card_eq_one]
    rcases h with h | h
    · refine ⟨(2, z - 2), ?_⟩
      ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_product, List.mem_toFinset, hmem, P,
        Finset.mem_singleton, Prod.mk.injEq]
      omega
    · refine ⟨(n, n), ?_⟩
      ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_product, List.mem_toFinset, hmem, P,
        Finset.mem_singleton, Prod.mk.injEq]
      omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨u, v⟩ huv
    simp only [Finset.mem_product, List.mem_toFinset, hmem, P] at huv
    omega

lemma mem_terms {n : ℕ} (ho : n % 2 = 1) (hn : 5 ≤ n) :
    ∀ M, M < 2 * n → ∀ y, y ∈ terms 2 n M ↔ y ≤ M ∧ P n y := by
  intro M
  induction M with
  | zero =>
    intro _ y
    rw [terms_zero hn]
    simp [P]
    omega
  | succ M ih =>
    intro hM y
    rw [terms_succ, mem_step, ih (by omega)]
    by_cases hz : n < M + 1
    · have hr := reps_val ho hn hz (by omega) (bound 2 n M).1 (fun y => by
        rw [ih (by omega)]; simp only [Nat.add_sub_cancel])
      unfold P
      by_cases hc : (M + 1) % 2 = 1 ∨ M + 1 = 2 * n
      · rw [if_pos hc] at hr; rw [hr]; omega
      · rw [if_neg hc] at hr; rw [hr]; omega
    · unfold P
      omega

end A1804

open A1804 in
theorem OMA.solution : OMA.R_arxiv_1804_09594_R1.H1 := by
  intro n ho hn x hx he
  rw [Nat.odd_iff] at ho
  rw [Nat.even_iff] at he
  unfold InV
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · rw [terms_zero hn]
    simp
    omega
  obtain ⟨M, rfl⟩ : ∃ M, x = M + 1 := ⟨x - 1, by omega⟩
  rw [terms_succ, mem_step]
  have hnot : M + 1 ∉ terms 2 n M := fun h => by have := (bound 2 n M).2 _ h; omega
  by_cases hz : n < M + 1
  · have hr := reps_val ho hn hz hx (bound 2 n M).1 (fun y => by
      rw [mem_terms ho hn M (by omega)]; simp only [Nat.add_sub_cancel])
    by_cases hc : (M + 1) % 2 = 1 ∨ M + 1 = 2 * n
    · rw [if_pos hc] at hr
      rw [hr]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact absurd h hnot
        · omega
      · intro h; right; exact ⟨rfl, by omega⟩
    · rw [if_neg hc] at hr
      rw [hr]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact absurd h hnot
        · omega
      · intro h; omega
  · constructor
    · rintro (h | ⟨-, h⟩)
      · exact absurd h hnot
      · omega
    · intro h
      right
      exact ⟨rfl, by omega⟩
