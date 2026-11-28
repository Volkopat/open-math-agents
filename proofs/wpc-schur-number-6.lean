import OMAStatements.S_wpc_schur_number_6
import Mathlib

-- Problem wpc-schur-number-6: there is a positive integer S such that every colouring of {1, ..., S} with 6
-- colours has a monochromatic solution of x + y = z (Schur's theorem for 6 colours).
-- Upstream: statements/wpc-schur-number-6.lean (declaration OMA.S_wpc_schur_number_6.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: Schur's classical argument, by induction on the number k of colours. Claim: there is N such that for
-- every finite set A of at least N natural numbers whose differences a - b (b < a in A) only use colours from a
-- set of k colours, three such differences x, y, z of the same colour satisfy x + y = z. For k = 0 take N = 2.
-- For k + 1 colours take N = (k + 1) * N' + 2. Let a0 be the least element of A. By the pigeonhole principle
-- more than N' of the numbers a - a0 (a in A, a > a0) have one colour c0; let B be the set of these numbers.
-- Differences of elements of B are differences of elements of A. If one of them, b - b', has colour c0, then
-- b' + (b - b') = b is a monochromatic solution. Otherwise the differences of B avoid c0 and the induction
-- hypothesis applies to B. Finally apply the claim with k = 6 to A = {0, 1, ..., S}, whose differences are
-- exactly 1, ..., S.

open OMA.S_wpc_schur_number_6

private lemma schur_diff : ∀ k : ℕ, ∃ N : ℕ, ∀ (χ : ℕ → ℕ) (C A : Finset ℕ), C.card = k → N ≤ A.card →
    (∀ a ∈ A, ∀ b ∈ A, b < a → χ (a - b) ∈ C) →
    ∃ x y z : ℕ, (∃ a ∈ A, ∃ b ∈ A, b < a ∧ a - b = x) ∧ (∃ a ∈ A, ∃ b ∈ A, b < a ∧ a - b = y) ∧
      (∃ a ∈ A, ∃ b ∈ A, b < a ∧ a - b = z) ∧ χ x = χ y ∧ χ y = χ z ∧ x + y = z := by
  intro k
  induction k with
  | zero =>
    refine ⟨2, ?_⟩
    intro χ C A hC hA hχ
    exfalso
    have hC0 : C = ∅ := Finset.card_eq_zero.mp hC
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    rcases lt_or_gt_of_ne hab with h | h
    · have h1 := hχ b hb a ha h
      rw [hC0] at h1
      simp at h1
    · have h1 := hχ a ha b hb h
      rw [hC0] at h1
      simp at h1
  | succ k ih =>
    obtain ⟨N', hN'⟩ := ih
    refine ⟨(k + 1) * N' + 2, ?_⟩
    intro χ C A hC hA hχ
    have hAne : A.Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨a₀, ha₀A, hmin⟩ : ∃ a₀ ∈ A, ∀ a ∈ A, a₀ ≤ a :=
      ⟨A.min' hAne, Finset.min'_mem A hAne, fun a ha => Finset.min'_le A a ha⟩
    have hmaps : ∀ a ∈ A.erase a₀, χ (a - a₀) ∈ C := by
      intro a ha
      have haA := Finset.mem_of_mem_erase ha
      have hne := Finset.ne_of_mem_erase ha
      exact hχ a haA a₀ ha₀A (lt_of_le_of_ne (hmin a haA) (Ne.symm hne))
    have hcard : C.card * N' < (A.erase a₀).card := by
      have h1 := Finset.card_erase_of_mem ha₀A
      rw [hC, h1]
      generalize (k + 1) * N' = m at hA ⊢
      omega
    obtain ⟨c₀, hc₀C, hfib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
    obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, F = (A.erase a₀).filter (fun a => χ (a - a₀) = c₀) := ⟨_, rfl⟩
    have hFcard : N' < F.card := by
      rw [hF]
      exact hfib
    have hFA : ∀ a ∈ F, a ∈ A ∧ a₀ < a ∧ χ (a - a₀) = c₀ := by
      intro a ha
      rw [hF, Finset.mem_filter] at ha
      have haA := Finset.mem_of_mem_erase ha.1
      have hne := Finset.ne_of_mem_erase ha.1
      exact ⟨haA, lt_of_le_of_ne (hmin a haA) (Ne.symm hne), ha.2⟩
    obtain ⟨B, hB⟩ : ∃ B : Finset ℕ, B = F.image (fun a => a - a₀) := ⟨_, rfl⟩
    have hBcard : N' ≤ B.card := by
      rw [hB, Finset.card_image_of_injOn]
      · exact hFcard.le
      · intro a ha a' ha' h
        have h1 := (hFA a ha).2.1
        have h2 := (hFA a' ha').2.1
        have h3 : a - a₀ = a' - a₀ := h
        omega
    have hBmem : ∀ b ∈ B, ∃ a ∈ A, a₀ < a ∧ χ (a - a₀) = c₀ ∧ a - a₀ = b := by
      intro b hb
      rw [hB, Finset.mem_image] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      exact ⟨a, (hFA a ha).1, (hFA a ha).2.1, (hFA a ha).2.2, rfl⟩
    by_cases hcase : ∃ b ∈ B, ∃ b' ∈ B, b' < b ∧ χ (b - b') = c₀
    · obtain ⟨b, hb, b', hb', hlt, hcol⟩ := hcase
      obtain ⟨a, haA, ha0, hac, rfl⟩ := hBmem b hb
      obtain ⟨a', ha'A, ha'0, ha'c, rfl⟩ := hBmem b' hb'
      refine ⟨a' - a₀, (a - a₀) - (a' - a₀), a - a₀, ⟨a', ha'A, a₀, ha₀A, ha'0, rfl⟩,
        ⟨a, haA, a', ha'A, by omega, by omega⟩, ⟨a, haA, a₀, ha₀A, ha0, rfl⟩, ?_, ?_, by omega⟩
      · rw [ha'c, hcol]
      · rw [hcol, hac]
    · have hχ' : ∀ b ∈ B, ∀ b' ∈ B, b' < b → χ (b - b') ∈ C.erase c₀ := by
        intro b hb b' hb' hlt
        rw [Finset.mem_erase]
        refine ⟨fun h => hcase ⟨b, hb, b', hb', hlt, h⟩, ?_⟩
        obtain ⟨a, haA, ha0, hac, rfl⟩ := hBmem b hb
        obtain ⟨a', ha'A, ha'0, ha'c, rfl⟩ := hBmem b' hb'
        have h1 : (a - a₀) - (a' - a₀) = a - a' := by omega
        rw [h1]
        exact hχ a haA a' ha'A (by omega)
      have hC' : (C.erase c₀).card = k := by
        have h1 := Finset.card_erase_of_mem hc₀C
        omega
      obtain ⟨x, y, z, hx, hy, hz, h1, h2, h3⟩ := hN' χ (C.erase c₀) B hC' hBcard hχ'
      have lift : ∀ d, (∃ b ∈ B, ∃ b' ∈ B, b' < b ∧ b - b' = d) →
          (∃ a ∈ A, ∃ a' ∈ A, a' < a ∧ a - a' = d) := by
        rintro d ⟨b, hb, b', hb', hlt, rfl⟩
        obtain ⟨a, haA, ha0, hac, rfl⟩ := hBmem b hb
        obtain ⟨a', ha'A, ha'0, ha'c, rfl⟩ := hBmem b' hb'
        exact ⟨a, haA, a', ha'A, by omega, by omega⟩
      exact ⟨x, y, z, lift x hx, lift y hy, lift z hz, h1, h2, h3⟩

theorem OMA.solution : type_of% @OMA.S_wpc_schur_number_6.main := by
  obtain ⟨N, hN⟩ := schur_diff 6
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  show ∀ color : Fin (N + 1) → Fin 6, ∃ x y z : Fin (N + 1),
    color x = color y ∧ color y = color z ∧ x.val + y.val + 1 = z.val
  intro color
  obtain ⟨χ, hχ⟩ : ∃ χ : ℕ → ℕ,
      ∀ d, χ d = if h : d - 1 < N + 1 then ((color ⟨d - 1, h⟩ : Fin 6) : ℕ) else 0 :=
    ⟨fun d => if h : d - 1 < N + 1 then ((color ⟨d - 1, h⟩ : Fin 6) : ℕ) else 0, fun d => rfl⟩
  have hχ6 : ∀ d, χ d ∈ Finset.range 6 := by
    intro d
    rw [hχ, Finset.mem_range]
    split_ifs with h
    · exact (color ⟨d - 1, h⟩).isLt
    · norm_num
  obtain ⟨x, y, z, ⟨a1, ha1, b1, hb1, hlt1, hx⟩, ⟨a2, ha2, b2, hb2, hlt2, hy⟩,
      ⟨a3, ha3, b3, hb3, hlt3, hz⟩, hxy, hyz, hsum⟩ :=
    hN χ (Finset.range 6) (Finset.range (N + 2)) (Finset.card_range 6)
      (by rw [Finset.card_range]; omega) (fun a _ b _ _ => hχ6 (a - b))
  rw [Finset.mem_range] at ha1 ha2 ha3
  have hx1 : x - 1 < N + 1 := by omega
  have hy1 : y - 1 < N + 1 := by omega
  have hz1 : z - 1 < N + 1 := by omega
  refine ⟨⟨x - 1, hx1⟩, ⟨y - 1, hy1⟩, ⟨z - 1, hz1⟩, ?_, ?_, ?_⟩
  · apply Fin.ext
    have h := hxy
    rw [hχ x, hχ y, dif_pos hx1, dif_pos hy1] at h
    exact h
  · apply Fin.ext
    have h := hyz
    rw [hχ y, hχ z, dif_pos hy1, dif_pos hz1] at h
    exact h
  · show x - 1 + (y - 1) + 1 = z - 1
    omega
