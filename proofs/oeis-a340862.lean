import OMAStatements.S_oeis_a340862

-- Problem: A340862: Number of times the number n turns up in pseudo-Fibonacci sequences starting with [k, 1] (with k >= 1), excluding the starting terms.
-- Upstream: formal-conjectures statements/oeis-a340862.lean:0 (declaration OMA.S_oeis_a340862.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: S k j = B (k+1) j for j >= 1. The pair (k, 2) with S k 2 = n is k = n - 1; every
-- other pair (k, j), j >= 3, gives i = S k (j-1), and (k, j) -> i is a bijection onto the set
-- counted by A067148: injective because two consecutive terms determine a sequence B c (c >= 2)
-- and its position backwards, surjective because a sequence with c >= 2 is a [k, 1] sequence and
-- B 1 is B 2 shifted by one place (the shift fails only for the pair (1, 2), that is, n = 2).

open OMA.S_oeis_a340862 in
theorem OMA.solution : type_of% @OMA.S_oeis_a340862.main := by
  have S2 : ∀ k j, S k (j + 2) = S k j + S k (j + 1) := fun k j => by rw [S]
  have B3 : ∀ c j, B c (j + 3) = B c (j + 1) + B c (j + 2) := fun c j => by rw [B]
  have hS2 : ∀ k, S k 2 = k + 1 := fun k => rfl
  have SB : ∀ k j, S k (j + 1) = B (k + 1) (j + 1) ∧ S k (j + 2) = B (k + 1) (j + 2) := by
    intro k j
    induction j with
    | zero =>
      show S k 1 = B (k + 1) 1 ∧ S k 2 = B (k + 1) 2
      exact ⟨rfl, rfl⟩
    | succ m ih =>
      show S k (m + 2) = B (k + 1) (m + 2) ∧ S k (m + 3) = B (k + 1) (m + 3)
      refine ⟨ih.2, ?_⟩
      have e1 : S k (m + 3) = S k (m + 1) + S k (m + 2) := S2 k (m + 1)
      rw [e1, B3, ih.1, ih.2]
  have SBj : ∀ k j, 1 ≤ j → S k j = B (k + 1) j := by
    intro k j hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    exact (SB k m).1
  have Sbd : ∀ k m, 1 ≤ S k (m + 1) ∧ k + m + 1 ≤ S k (m + 2) := by
    intro k m
    induction m with
    | zero =>
      show 1 ≤ 1 ∧ k + 0 + 1 ≤ k + 1
      omega
    | succ m ih =>
      show 1 ≤ S k (m + 2) ∧ k + (m + 1) + 1 ≤ S k (m + 3)
      have e : S k (m + 3) = S k (m + 1) + S k (m + 2) := S2 k (m + 1)
      obtain ⟨h1, h2⟩ := ih
      exact ⟨by omega, by omega⟩
  have Bp : ∀ c, 1 ≤ c → ∀ m, 1 ≤ B c (m + 1) ∧ c ≤ B c (m + 2) ∧ 1 ≤ B c (m + 2) := by
    intro c hc m
    induction m with
    | zero =>
      show 1 ≤ 1 ∧ c ≤ c ∧ 1 ≤ c
      exact ⟨le_refl 1, le_refl c, hc⟩
    | succ m ih =>
      show 1 ≤ B c (m + 2) ∧ c ≤ B c (m + 3) ∧ 1 ≤ B c (m + 3)
      have e : B c (m + 3) = B c (m + 1) + B c (m + 2) := B3 c m
      obtain ⟨h1, h2, h3⟩ := ih
      exact ⟨h3, by omega, by omega⟩
  have shift : ∀ j, B 1 (j + 2) = B 2 (j + 1) ∧ B 1 (j + 3) = B 2 (j + 2) := by
    intro j
    induction j with
    | zero =>
      show B 1 2 = B 2 1 ∧ B 1 3 = B 2 2
      exact ⟨rfl, rfl⟩
    | succ m ih =>
      show B 1 (m + 3) = B 2 (m + 2) ∧ B 1 (m + 4) = B 2 (m + 3)
      refine ⟨ih.2, ?_⟩
      have e1 : B 1 (m + 4) = B 1 (m + 2) + B 1 (m + 3) := B3 1 (m + 1)
      have e2 : B 2 (m + 3) = B 2 (m + 1) + B 2 (m + 2) := B3 2 m
      rw [e1, e2, ih.1, ih.2]
  have uniq : ∀ j c c' j', 2 ≤ c → 2 ≤ c' → 1 ≤ j' → B c (j + 1) = B c' j' →
      B c (j + 2) = B c' (j' + 1) → c = c' ∧ j + 1 = j' := by
    intro j
    induction j with
    | zero =>
      intro c c' j' hc hc' hj' h1 h2
      have h1' : 1 = B c' j' := h1
      rcases Nat.lt_or_ge j' 2 with h | h
      · have hj1 : j' = 1 := by omega
        subst hj1
        have h2' : c = c' := h2
        exact ⟨h2', rfl⟩
      · exfalso
        obtain ⟨u, rfl⟩ : ∃ u, j' = u + 2 := ⟨j' - 2, by omega⟩
        have h3 := (Bp c' (by omega) u).2.1
        omega
    | succ m ih =>
      intro c c' j' hc hc' hj' h1 h2
      have h1' : B c (m + 2) = B c' j' := h1
      have h2' : B c (m + 3) = B c' (j' + 1) := h2
      rcases Nat.lt_or_ge j' 2 with h | h
      · exfalso
        have hj1 : j' = 1 := by omega
        subst hj1
        have h3 := (Bp c (by omega) m).2.1
        have h4 : B c' 1 = 1 := rfl
        omega
      · obtain ⟨v, rfl⟩ : ∃ v, j' = v + 2 := ⟨j' - 2, by omega⟩
        have e1 : B c (m + 3) = B c (m + 1) + B c (m + 2) := B3 c m
        have e2 : B c' (v + 3) = B c' (v + 1) + B c' (v + 2) := B3 c' v
        have h2'' : B c (m + 3) = B c' (v + 3) := h2'
        have h5 : B c (m + 1) = B c' (v + 1) := by omega
        obtain ⟨hcc, hmv⟩ := ih c c' (v + 1) hc hc' (by omega) h5 h1'
        exact ⟨hcc, by omega⟩
  intro n hn
  have hT : {p : ℕ × ℕ | 1 ≤ p.1 ∧ 2 ≤ p.2 ∧ S p.1 p.2 = n} =
      insert (n - 1, 2) {p : ℕ × ℕ | 1 ≤ p.1 ∧ 3 ≤ p.2 ∧ S p.1 p.2 = n} := by
    ext ⟨k, j⟩
    show (1 ≤ k ∧ 2 ≤ j ∧ S k j = n) ↔ ((k, j) = (n - 1, 2) ∨ (1 ≤ k ∧ 3 ≤ j ∧ S k j = n))
    constructor
    · rintro ⟨hk, hj, hs⟩
      rcases Nat.lt_or_ge j 3 with h | h
      · left
        have hj2 : j = 2 := by omega
        subst hj2
        rw [hS2] at hs
        rw [show k = n - 1 by omega]
      · exact Or.inr ⟨hk, h, hs⟩
    · rintro (h | ⟨hk, hj, hs⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        refine ⟨by omega, le_refl 2, ?_⟩
        rw [hS2]
        omega
      · exact ⟨hk, by omega, hs⟩
  have hnot : (n - 1, 2) ∉ {p : ℕ × ℕ | 1 ≤ p.1 ∧ 3 ≤ p.2 ∧ S p.1 p.2 = n} := by
    intro h
    have h' : 1 ≤ n - 1 ∧ 3 ≤ 2 ∧ S (n - 1) 2 = n := h
    exact absurd h'.2.1 (by norm_num)
  have hfin : {p : ℕ × ℕ | 1 ≤ p.1 ∧ 3 ≤ p.2 ∧ S p.1 p.2 = n}.Finite := by
    apply Set.Finite.subset ((Set.finite_le_nat n).prod (Set.finite_le_nat (n + 1)))
    rintro ⟨k, j⟩ h
    have h' : 1 ≤ k ∧ 3 ≤ j ∧ S k j = n := h
    obtain ⟨hk, hj, hs⟩ := h'
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
    have hb := (Sbd k m).2
    show k ≤ n ∧ m + 2 ≤ n + 1
    exact ⟨by omega, by omega⟩
  have hRI : {p : ℕ × ℕ | 1 ≤ p.1 ∧ 3 ≤ p.2 ∧ S p.1 p.2 = n}.ncard =
      {i : ℕ | 0 < i ∧ i < n ∧
        ∃ c j : ℕ, 0 < c ∧ 2 < j ∧ B c (j - 1) = i ∧ B c j = n}.ncard := by
    apply Set.ncard_congr (fun p _ => S p.1 (p.2 - 1))
    · rintro ⟨k, j⟩ hp
      have hp' : 1 ≤ k ∧ 3 ≤ j ∧ S k j = n := hp
      obtain ⟨hk, hj, hs⟩ := hp'
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 3 := ⟨j - 3, by omega⟩
      have e1 : S k (m + 2) = B (k + 1) (m + 2) := SBj k (m + 2) (by omega)
      have e2 : S k (m + 3) = B (k + 1) (m + 3) := SBj k (m + 3) (by omega)
      have e3 : S k (m + 3) = S k (m + 1) + S k (m + 2) := S2 k (m + 1)
      have b1 := (Sbd k m).1
      have b2 := (Sbd k m).2
      show 0 < S k (m + 3 - 1) ∧ S k (m + 3 - 1) < n ∧
        ∃ c j : ℕ, 0 < c ∧ 2 < j ∧ B c (j - 1) = S k (m + 3 - 1) ∧ B c j = n
      rw [show m + 3 - 1 = m + 2 by omega]
      refine ⟨by omega, by omega, k + 1, m + 3, by omega, by omega, ?_, ?_⟩
      · rw [show m + 3 - 1 = m + 2 by omega, e1]
      · rw [← e2]
        exact hs
    · rintro ⟨k, j⟩ ⟨k', j'⟩ ha hb hf
      have ha' : 1 ≤ k ∧ 3 ≤ j ∧ S k j = n := ha
      have hb' : 1 ≤ k' ∧ 3 ≤ j' ∧ S k' j' = n := hb
      have hf' : S k (j - 1) = S k' (j' - 1) := hf
      obtain ⟨hk, hj, hs⟩ := ha'
      obtain ⟨hk', hj', hs'⟩ := hb'
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 3 := ⟨j - 3, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', j' = m' + 3 := ⟨j' - 3, by omega⟩
      rw [show m + 3 - 1 = m + 2 by omega, show m' + 3 - 1 = m' + 2 by omega,
        SBj k (m + 2) (by omega), SBj k' (m' + 2) (by omega)] at hf'
      rw [SBj k (m + 3) (by omega)] at hs
      rw [SBj k' (m' + 3) (by omega)] at hs'
      obtain ⟨h1, h2⟩ := uniq (m + 1) (k + 1) (k' + 1) (m' + 2) (by omega) (by omega)
        (by omega) hf' (hs.trans hs'.symm)
      rw [show k = k' by omega, show m = m' by omega]
    · rintro i hi
      have hi' : 0 < i ∧ i < n ∧
          ∃ c j : ℕ, 0 < c ∧ 2 < j ∧ B c (j - 1) = i ∧ B c j = n := hi
      obtain ⟨hi0, hin, c, j, hc, hj, hbi, hbn⟩ := hi'
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 3 := ⟨j - 3, by omega⟩
      rw [show m + 3 - 1 = m + 2 by omega] at hbi
      rcases Nat.lt_or_ge c 2 with hc2 | hc2
      · have hc1 : c = 1 := by omega
        subst hc1
        rcases Nat.eq_zero_or_pos m with hm | hm
        · exfalso
          subst hm
          have h3 : B 1 (0 + 3) = 2 := rfl
          omega
        · obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
          have sh := shift (t + 1)
          refine ⟨(1, t + 3), ?_, ?_⟩
          · show 1 ≤ 1 ∧ 3 ≤ t + 3 ∧ S 1 (t + 3) = n
            refine ⟨le_refl 1, by omega, ?_⟩
            rw [SBj 1 (t + 3) (by omega)]
            exact sh.2.symm.trans hbn
          · show S 1 (t + 3 - 1) = i
            rw [show t + 3 - 1 = t + 2 by omega, SBj 1 (t + 2) (by omega)]
            exact sh.1.symm.trans hbi
      · obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
        refine ⟨(k, m + 3), ?_, ?_⟩
        · show 1 ≤ k ∧ 3 ≤ m + 3 ∧ S k (m + 3) = n
          refine ⟨by omega, by omega, ?_⟩
          rw [SBj k (m + 3) (by omega)]
          exact hbn
        · show S k (m + 3 - 1) = i
          rw [show m + 3 - 1 = m + 2 by omega, SBj k (m + 2) (by omega)]
          exact hbi
  unfold a A067148
  rw [hT, Set.ncard_insert_of_notMem hnot hfin, hRI]
  omega
