import OMAStatements.S_oeis_a293137
import Mathlib

namespace OMA.P293137

open OMA.S_oeis_a293137

lemma floor_eq (n : ℕ) : ⌊2 * Real.sqrt n⌋₊ = Nat.sqrt (4 * n) := by
  have h : (2 : ℝ) * Real.sqrt n = Real.sqrt ((4 * n : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (by norm_num)]
    congr 1
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h, Real.nat_floor_real_sqrt_eq_nat_sqrt]

lemma a_eq (n : ℕ) : a n = Nat.sqrt (4 * n) - 1 := by
  unfold a
  split_ifs with h
  · subst h
    simp
  · rw [floor_eq]

lemma inc_bound : ∀ (l : List ℕ) (c : ℕ), l.Pairwise (· < ·) → (∀ x ∈ l, c ≤ x) →
    l.length * (2 * c + l.length) ≤ 2 * l.sum + l.length
  | [], c, _, _ => by simp
  | x :: l, c, h, hc => by
    rw [List.pairwise_cons] at h
    have hx : c ≤ x := hc x (by simp)
    have hl : ∀ y ∈ l, c + 1 ≤ y := fun y hy => by
      have := h.1 y hy
      omega
    have ih := inc_bound l (c + 1) h.2 hl
    simp only [List.length_cons, List.sum_cons]
    nlinarith

lemma inc_top : ∀ (l : List ℕ) (c p : ℕ), l.Pairwise (· < ·) → (∀ x ∈ l, c ≤ x) →
    (∀ x ∈ l, x < p) → c ≤ p → c + l.length ≤ p
  | [], c, p, _, _, _, hcp => by simpa using hcp
  | x :: l, c, p, h, hc, hp, _ => by
    rw [List.pairwise_cons] at h
    have hx : c ≤ x := hc x (by simp)
    have hxp : x < p := hp x (by simp)
    have hl : ∀ y ∈ l, c + 1 ≤ y := fun y hy => by
      have := h.1 y hy
      omega
    have ih := inc_top l (c + 1) p h.2 hl (fun y hy => hp y (by simp [hy])) (by omega)
    simp only [List.length_cons]
    omega

lemma su_bound (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x) (hl : l ≠ []) (h : StronglyUnimodal l) :
    (l.length + 1) * (l.length + 1) ≤ 4 * l.sum := by
  rcases h with h | ⟨l₁, p, l₂, rfl, h1, h2⟩
  · exact absurd h hl
  · rw [List.pairwise_append] at h1
    rw [List.pairwise_cons] at h2
    have hp : 0 < p := hpos p (by simp)
    have h1pos : ∀ x ∈ l₁, 1 ≤ x := fun x hx => hpos x (by simp [hx])
    have h2pos : ∀ x ∈ l₂.reverse, 1 ≤ x := fun x hx => hpos x (by
      simp only [List.mem_reverse] at hx
      simp [hx])
    have hr : l₂.reverse.Pairwise (· < ·) := List.pairwise_reverse.mpr h2.2
    have A := inc_bound l₁ 1 h1.1 h1pos
    have B := inc_bound l₂.reverse 1 hr h2pos
    have C := inc_top l₁ 1 p h1.1 h1pos (fun x hx => h1.2.2 x hx p (by simp)) hp
    have D := inc_top l₂.reverse 1 p hr h2pos
      (fun x hx => h2.1 x (by simpa using hx)) hp
    simp only [List.length_reverse, List.sum_reverse] at B D
    simp only [List.length_append, List.length_cons, List.sum_append, List.sum_cons]
    nlinarith [two_mul_le_add_sq l₁.length l₂.length]

def up (j : ℕ) : List ℕ := (List.range j).map (· + 1)

lemma sum_up (j : ℕ) : 2 * (up j).sum = j * (j + 1) := by
  induction j with
  | zero => simp [up]
  | succ j ih =>
    unfold up at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    nlinarith [ih]

lemma mem_up {x j : ℕ} (h : x ∈ up j) : 1 ≤ x ∧ x ≤ j := by
  simp only [up, List.mem_map, List.mem_range] at h
  obtain ⟨b, hb, rfl⟩ := h
  omega

lemma pw_up (j : ℕ) : (up j).Pairwise (· < ·) := by
  unfold up
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp (fun h => by omega)

lemma length_up (j : ℕ) : (up j).length = j := by
  simp [up]

lemma exists_comp (n x y : ℕ) (hyx : y ≤ x)
    (h : x * (x + 1) + y * (y + 1) + 2 * (x + 1) ≤ 2 * n) :
    ∃ c : Composition n, c.length = x + 1 + y ∧ StronglyUnimodal c.blocks := by
  have s1 := sum_up x
  have s2 := sum_up y
  obtain ⟨p, hp, hpx⟩ : ∃ p, n = (up x).sum + p + (up y).sum ∧ x + 1 ≤ p :=
    ⟨n - (up x).sum - (up y).sum, by omega, by omega⟩
  refine ⟨⟨up x ++ p :: (up y).reverse, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_append, List.mem_cons, List.mem_reverse] at hi
    rcases hi with hi | hi | hi
    · exact (mem_up hi).1
    · omega
    · exact (mem_up hi).1
  · simp only [List.sum_append, List.sum_cons, List.sum_reverse]
    omega
  · show (up x ++ p :: (up y).reverse).length = x + 1 + y
    simp only [List.length_append, List.length_cons, List.length_reverse, length_up]
    omega
  · refine Or.inr ⟨up x, p, (up y).reverse, rfl, ?_, ?_⟩
    · refine List.pairwise_append.mpr ⟨pw_up x, List.pairwise_singleton _ _, ?_⟩
      intro u hu v hv
      simp only [List.mem_singleton] at hv
      subst hv
      have := (mem_up hu).2
      omega
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_reverse.mpr (pw_up y)⟩
      intro u hu
      simp only [List.mem_reverse] at hu
      have := (mem_up hu).2
      show u < p
      omega

theorem sol : type_of% @OMA.S_oeis_a293137.main := by
  classical
  intro n
  rw [a_eq]
  constructor
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · unfold T
      exact Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_univ (⟨[], by simp, by simp⟩ : Composition 0),
          by simp [Composition.length], Or.inl rfl⟩)
    · have hs : Nat.sqrt (4 * n) * Nat.sqrt (4 * n) ≤ 4 * n := Nat.sqrt_le (4 * n)
      have h2 : 2 ≤ Nat.sqrt (4 * n) := Nat.le_sqrt.mpr (by omega)
      obtain ⟨x, y, hyx, hk, h⟩ : ∃ x y, y ≤ x ∧ Nat.sqrt (4 * n) - 1 = x + 1 + y ∧
          x * (x + 1) + y * (y + 1) + 2 * (x + 1) ≤ 2 * n := by
        obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (Nat.sqrt (4 * n))
        · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          refine ⟨i, i, le_refl _, by omega, ?_⟩
          rw [hj] at hs
          ring_nf at hs ⊢
          omega
        · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          refine ⟨i + 1, i, by omega, by omega, ?_⟩
          rw [hj] at hs
          ring_nf at hs ⊢
          omega
      obtain ⟨c, hc1, hc2⟩ := exists_comp n x y hyx h
      unfold T
      exact Finset.card_ne_zero_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1.trans hk.symm, hc2⟩)
  · intro k hk
    unfold T
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro c - ⟨hck, hsu⟩
    have hlen : c.blocks.length = k := hck
    have hne : c.blocks ≠ [] := by
      intro h
      rw [h] at hlen
      simp at hlen
      omega
    have hb := su_bound c.blocks (fun x hx => c.blocks_pos hx) hne hsu
    rw [c.blocks_sum, hlen] at hb
    have : k + 1 ≤ Nat.sqrt (4 * n) := Nat.le_sqrt.mpr hb
    omega

end OMA.P293137

theorem OMA.solution : type_of% @OMA.S_oeis_a293137.main := OMA.P293137.sol
