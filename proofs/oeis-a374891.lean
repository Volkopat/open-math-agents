import OMAStatements.S_oeis_a374891

-- Problem: A374891: Obverse convolution (1)**A000984; see Comments.
-- Upstream: formal-conjectures statements/oeis-a374891.lean:0 (declaration OMA.S_oeis_a374891.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(n) = Product_{j=0..n} (1 + binomial(2j, j)), so a(n+1) = a(n)*(1 + binomial(2n+2, n+1)),
-- and A323230(n+2) = binomial(2n+2, n+1) + 1. For A244174(N), N >= 1: if every occurring part p has
-- multiplicity at least N then N*p <= 3N, so all parts are 1, 2 or 3, and the sum c1 + 2c2 + 3c3 = 3N
-- forces either N threes, or N ones and N twos. The lists of N ones and N twos are the set W(N,N)
-- built by the recursion W(u+1,v+1) = 1::W(u,v+1) + 2::W(u+1,v), which has binomial(2N, N) elements.

namespace K07A374891

open OMA.S_oeis_a374891

theorem a_alt (n : ℕ) : a n = ∏ j ∈ Finset.range (n + 1), (1 + Nat.choose (2 * j) j) := by
  rw [a, ← Finset.prod_range_reflect (fun j => 1 + Nat.choose (2 * j) j) (n + 1)]
  apply Finset.prod_congr rfl
  intro k _
  rw [show n + 1 - 1 - k = n - k by omega]

theorem a_succ (n : ℕ) : a (n + 1) = a n * (1 + Nat.choose (2 * (n + 1)) (n + 1)) := by
  rw [a_alt, a_alt, Finset.prod_range_succ]

theorem count_mul_le_sum (p : ℕ) (l : List ℕ) : l.count p * p ≤ l.sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.count_cons, List.sum_cons]
    by_cases h : x = p
    · rw [if_pos (show (x == p) = true by simp [h]), add_mul, one_mul, h]
      omega
    · rw [if_neg (show ¬ (x == p) = true by simpa using h), add_zero]
      omega

theorem sum_counts (l : List ℕ) (h : ∀ x ∈ l, x = 1 ∨ x = 2 ∨ x = 3) :
    l.sum = l.count 1 + 2 * l.count 2 + 3 * l.count 3 := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    rcases h x List.mem_cons_self with rfl | rfl | rfl
    · rw [List.sum_cons, List.count_cons_self, List.count_cons_of_ne (show (1 : ℕ) ≠ 2 by decide),
        List.count_cons_of_ne (show (1 : ℕ) ≠ 3 by decide)]
      omega
    · rw [List.sum_cons, List.count_cons_of_ne (show (2 : ℕ) ≠ 1 by decide), List.count_cons_self,
        List.count_cons_of_ne (show (2 : ℕ) ≠ 3 by decide)]
      omega
    · rw [List.sum_cons, List.count_cons_of_ne (show (3 : ℕ) ≠ 1 by decide),
        List.count_cons_of_ne (show (3 : ℕ) ≠ 2 by decide), List.count_cons_self]
      omega

theorem len_counts (l : List ℕ) (h : ∀ x ∈ l, x = 1 ∨ x = 2 ∨ x = 3) :
    l.length = l.count 1 + l.count 2 + l.count 3 := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    rcases h x List.mem_cons_self with rfl | rfl | rfl
    · rw [List.length_cons, List.count_cons_self, List.count_cons_of_ne (show (1 : ℕ) ≠ 2 by decide),
        List.count_cons_of_ne (show (1 : ℕ) ≠ 3 by decide)]
      omega
    · rw [List.length_cons, List.count_cons_of_ne (show (2 : ℕ) ≠ 1 by decide), List.count_cons_self,
        List.count_cons_of_ne (show (2 : ℕ) ≠ 3 by decide)]
      omega
    · rw [List.length_cons, List.count_cons_of_ne (show (3 : ℕ) ≠ 1 by decide),
        List.count_cons_of_ne (show (3 : ℕ) ≠ 2 by decide), List.count_cons_self]
      omega

theorem charac (N : ℕ) (hN : 0 < N) (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 3 * N)
    (h1 : ∀ p ∈ l, N ≤ l.count p) (h2 : ∃ p ∈ l, l.count p = N) :
    l = List.replicate N 3 ∨ ((∀ x ∈ l, x = 1 ∨ x = 2) ∧ l.count 1 = N ∧ l.count 2 = N) := by
  have hle : ∀ x ∈ l, x ≤ 3 := by
    intro x hx
    have e1 := h1 x hx
    have e2 := count_mul_le_sum x l
    have e3 : N * x ≤ l.count x * x := Nat.mul_le_mul_right x e1
    have e4 : N * x ≤ N * 3 := by omega
    exact Nat.le_of_mul_le_mul_left e4 hN
  have h123 : ∀ x ∈ l, x = 1 ∨ x = 2 ∨ x = 3 := by
    intro x hx
    have f1 := hle x hx
    have f2 := hpos x hx
    omega
  have hs := sum_counts l h123
  have hlen := len_counts l h123
  by_cases h3 : 3 ∈ l
  · left
    have e3 := h1 3 h3
    have hc1 : l.count 1 = 0 := by omega
    have hc2 : l.count 2 = 0 := by omega
    rw [List.eq_replicate_iff]
    refine ⟨by omega, ?_⟩
    intro b hb
    rcases h123 b hb with hb1 | hb2 | hb3
    · rw [hb1] at hb
      have f3 := List.count_pos_iff.mpr hb
      omega
    · rw [hb2] at hb
      have f3 := List.count_pos_iff.mpr hb
      omega
    · exact hb3
  · right
    have hc3 : l.count 3 = 0 := List.count_eq_zero.mpr h3
    have h12 : ∀ x ∈ l, x = 1 ∨ x = 2 := by
      intro x hx
      rcases h123 x hx with hx1 | hx2 | hx3
      · exact Or.inl hx1
      · exact Or.inr hx2
      · rw [hx3] at hx
        exact absurd hx h3
    refine ⟨h12, ?_⟩
    obtain ⟨p, hp, hpN⟩ := h2
    by_cases h1m : 1 ∈ l
    · by_cases h2m : 2 ∈ l
      · have f1 := h1 1 h1m
        have f2 := h1 2 h2m
        constructor
        · omega
        · omega
      · have hc2 : l.count 2 = 0 := List.count_eq_zero.mpr h2m
        rcases h12 p hp with hp1 | hp2
        · rw [hp1] at hpN
          exfalso
          omega
        · rw [hp2] at hp
          exact absurd hp h2m
    · have hc1 : l.count 1 = 0 := List.count_eq_zero.mpr h1m
      rcases h12 p hp with hp1 | hp2
      · rw [hp1] at hp
        exact absurd hp h1m
      · rw [hp2] at hpN
        exfalso
        omega

/-- The lists with u ones and v twos and no other entries. -/
def W : ℕ → ℕ → Finset (List ℕ)
  | 0, 0 => {[]}
  | u + 1, 0 => (W u 0).image (List.cons 1)
  | 0, v + 1 => (W 0 v).image (List.cons 2)
  | u + 1, v + 1 => (W u (v + 1)).image (List.cons 1) ∪ (W (u + 1) v).image (List.cons 2)

theorem W_elems : ∀ u v : ℕ, ∀ l ∈ W u v, ∀ y ∈ l, y = 1 ∨ y = 2
  | 0, 0 => by
    intro l hl y hy
    simp only [W, Finset.mem_singleton] at hl
    subst hl
    simp at hy
  | u + 1, 0 => by
    intro l hl y hy
    simp only [W, Finset.mem_image] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    rcases List.mem_cons.mp hy with h | h
    · exact Or.inl h
    · exact W_elems u 0 l' hl' y h
  | 0, v + 1 => by
    intro l hl y hy
    simp only [W, Finset.mem_image] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    rcases List.mem_cons.mp hy with h | h
    · exact Or.inr h
    · exact W_elems 0 v l' hl' y h
  | u + 1, v + 1 => by
    intro l hl y hy
    simp only [W, Finset.mem_union, Finset.mem_image] at hl
    rcases hl with ⟨l', hl', rfl⟩ | ⟨l', hl', rfl⟩
    · rcases List.mem_cons.mp hy with h | h
      · exact Or.inl h
      · exact W_elems u (v + 1) l' hl' y h
    · rcases List.mem_cons.mp hy with h | h
      · exact Or.inr h
      · exact W_elems (u + 1) v l' hl' y h

theorem mem_W (l : List ℕ) : ∀ u v : ℕ,
    l ∈ W u v ↔ (∀ x ∈ l, x = 1 ∨ x = 2) ∧ l.count 1 = u ∧ l.count 2 = v := by
  induction l with
  | nil =>
    intro u v
    cases u <;> cases v <;> simp [W]
  | cons x t ih =>
    intro u v
    by_cases hx1 : x = 1
    · subst hx1
      rw [List.count_cons_self, List.count_cons_of_ne (show (1 : ℕ) ≠ 2 by decide)]
      cases u <;> cases v <;> simp [W, ih]
    · by_cases hx2 : x = 2
      · subst hx2
        rw [List.count_cons_of_ne (show (2 : ℕ) ≠ 1 by decide), List.count_cons_self]
        cases u <;> cases v <;> simp [W, ih]
      · have hL : x :: t ∉ W u v := fun hm => by
          rcases W_elems u v (x :: t) hm x List.mem_cons_self with h' | h'
          · exact hx1 h'
          · exact hx2 h'
        have hR : ¬ ((∀ y ∈ x :: t, y = 1 ∨ y = 2) ∧ (x :: t).count 1 = u ∧
            (x :: t).count 2 = v) := by
          intro hh
          rcases hh.1 x List.mem_cons_self with h' | h'
          · exact hx1 h'
          · exact hx2 h'
        exact iff_of_false hL hR

theorem card_W : ∀ u v : ℕ, (W u v).card = Nat.choose (u + v) u
  | 0, 0 => by simp [W]
  | u + 1, 0 => by
    simp only [W]
    rw [Finset.card_image_of_injective _ List.cons_injective, card_W u 0]
    simp
  | 0, v + 1 => by
    simp only [W]
    rw [Finset.card_image_of_injective _ List.cons_injective, card_W 0 v]
    simp
  | u + 1, v + 1 => by
    have hd : Disjoint ((W u (v + 1)).image (List.cons 1)) ((W (u + 1) v).image (List.cons 2)) := by
      rw [Finset.disjoint_left]
      intro l h1 h2
      rw [Finset.mem_image] at h1 h2
      obtain ⟨l1, _, rfl⟩ := h1
      obtain ⟨l2, _, h⟩ := h2
      simp at h
    have hp := Nat.choose_succ_succ' (u + (v + 1)) u
    rw [show u + (v + 1) + 1 = u + 1 + (v + 1) by ring] at hp
    simp only [W]
    rw [Finset.card_union_eq_card_add_card.mpr hd,
      Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective, card_W u (v + 1), card_W (u + 1) v,
      show u + 1 + v = u + (v + 1) by ring]
    omega

/-- A composition is determined by its list of blocks. -/
def blocksEmb (m : ℕ) : Composition m ↪ List ℕ := ⟨Composition.blocks, fun _ _ h => Composition.ext h⟩

theorem A244174_succ (n : ℕ) : A244174 (n + 1) = 1 + Nat.choose (2 * (n + 1)) (n + 1) := by
  have hN : 0 < n + 1 := Nat.succ_pos n
  have hset : (Finset.univ.filter (fun c : Composition (3 * (n + 1)) =>
      (∀ p ∈ c.blocks, n + 1 ≤ c.blocks.count p) ∧ ∃ p ∈ c.blocks, c.blocks.count p = n + 1)).map
        (blocksEmb (3 * (n + 1))) = insert (List.replicate (n + 1) 3) (W (n + 1) (n + 1)) := by
    ext l
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, mem_W]
    constructor
    · rintro ⟨c, ⟨hc1, hc2⟩, rfl⟩
      exact charac (n + 1) hN c.blocks (fun x hx => c.blocks_pos hx) c.blocks_sum hc1 hc2
    · rintro (rfl | ⟨h12, hc1, hc2⟩)
      · refine ⟨⟨List.replicate (n + 1) 3, fun {i} hi => ?_, ?_⟩, ⟨?_, ?_⟩, rfl⟩
        · rw [List.eq_of_mem_replicate hi]
          norm_num
        · rw [List.sum_replicate_nat, Nat.mul_comm]
        · intro p hp
          rw [List.eq_of_mem_replicate hp]
          simp
        · exact ⟨3, by simp, by simp⟩
      · have h123 : ∀ x ∈ l, x = 1 ∨ x = 2 ∨ x = 3 := fun x hx =>
          (h12 x hx).elim Or.inl (fun h => Or.inr (Or.inl h))
        have hc3 : l.count 3 = 0 := List.count_eq_zero.mpr (fun h3 => by
          rcases h12 3 h3 with h | h <;> omega)
        have hs := sum_counts l h123
        refine ⟨⟨l, fun {i} hi => ?_, ?_⟩, ⟨?_, ⟨1, List.count_pos_iff.mp (show 0 < l.count 1 by omega),
          hc1⟩⟩, rfl⟩
        · rcases h12 i hi with h | h <;> omega
        · omega
        · intro p hp
          show n + 1 ≤ l.count p
          rcases h12 p hp with h | h <;> rw [h] <;> omega
  rw [A244174, if_neg (show n + 1 ≠ 0 by omega), ← Finset.card_map (blocksEmb (3 * (n + 1))), hset,
    Finset.card_insert_of_notMem, card_W, show n + 1 + (n + 1) = 2 * (n + 1) by ring]
  · omega
  · intro h
    rw [mem_W] at h
    have h3 := h.1 3 (by simp)
    omega

end K07A374891

open OMA.S_oeis_a374891 in
theorem OMA.solution : type_of% @OMA.S_oeis_a374891.main := by
  intro n
  refine ⟨?_, ?_⟩
  · rw [K07A374891.a_succ, K07A374891.A244174_succ]
  · rw [K07A374891.a_succ, A323230, if_neg (show n + 2 ≠ 0 by omega),
      show n + 2 - 1 = n + 1 by omega]
    ring
