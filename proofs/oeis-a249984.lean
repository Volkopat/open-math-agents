import OMAStatements.S_oeis_a249984

-- Problem: A249984: Number of length 4+1 0..2*n arrays with the sum of the absolute values of adjacent differences equal to 4*n.
-- Upstream: statements/oeis-a249984.lean (declaration OMA.S_oeis_a249984.main)
-- Credit: @rgoldman73-dev

namespace OMA.Proof_oeis_a249984

open Finset PowerSeries OMA.S_oeis_a249984

private def halfSet (M m s : ℕ) : Finset (ℕ × ℕ) :=
  ((range (M + 1)) ×ˢ (range (M + 1))).filter fun p =>
    Int.natAbs ((p.1 : ℤ) - (p.2 : ℤ)) + Int.natAbs ((p.2 : ℤ) - (m : ℤ)) = s

private def halfCount (M m s : ℕ) : ℕ := (halfSet M m s).card

private def halfUp (M m s : ℕ) : Finset (ℕ × ℕ) :=
  (halfSet M m s).filter fun p => p.2 < p.1

private def halfDown (M m s : ℕ) : Finset (ℕ × ℕ) :=
  (halfSet M m s).filter fun p => p.1 < p.2

private def halfEq (M m s : ℕ) : Finset (ℕ × ℕ) :=
  (halfSet M m s).filter fun p => p.1 = p.2

private lemma halfSet_card_split (M m s : ℕ) :
    halfCount M m s = (halfUp M m s).card + (halfDown M m s).card + (halfEq M m s).card := by
  unfold halfCount halfUp halfDown halfEq
  let A := (halfSet M m s).filter fun p => p.2 < p.1
  let B := (halfSet M m s).filter fun p => p.1 < p.2
  let C := (halfSet M m s).filter fun p => p.1 = p.2
  have h1 : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro p _ hlt hgt
    omega
  have h2 : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro p hp heq
    simp only [A, B, C, mem_union, mem_filter] at hp heq
    rcases hp with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hunion : (A ∪ B) ∪ C = halfSet M m s := by
    ext p
    simp only [A, B, C, mem_union, mem_filter]
    constructor
    · rintro ((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
    · intro hp
      rcases lt_trichotomy p.2 p.1 with h | h | h
      · exact Or.inl (Or.inl ⟨hp, h⟩)
      · exact Or.inr ⟨hp, h.symm⟩
      · exact Or.inl (Or.inr ⟨hp, h⟩)
  change (halfSet M m s).card = A.card + B.card + C.card
  rw [← hunion, Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1]

private lemma halfDown_card_eq_halfUp (M m s : ℕ) (hm : m ≤ M) :
    (halfDown M m s).card = (halfUp M (M - m) s).card := by
  apply Finset.card_bij (fun p _ => (M - p.1, M - p.2))
  · intro p hp
    simp only [halfDown, halfUp, halfSet, mem_filter, mem_product, mem_range] at hp ⊢
    rcases hp with ⟨⟨⟨h1, h2⟩, hsum⟩, hlt⟩
    refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    have e1 : (((M - p.1 : ℕ) : ℤ) - ((M - p.2 : ℕ) : ℤ)) = -((p.1 : ℤ) - (p.2 : ℤ)) := by omega
    have e2 : (((M - p.2 : ℕ) : ℤ) - ((M - m : ℕ) : ℤ)) = -((p.2 : ℤ) - (m : ℤ)) := by omega
    rw [e1, e2, Int.natAbs_neg, Int.natAbs_neg]
    exact hsum
  · intro p1 hp1 p2 hp2 heq
    simp only [halfDown, halfSet, mem_filter, mem_product, mem_range] at hp1 hp2
    simp only [Prod.mk.injEq] at heq
    ext <;> omega
  · intro q hq
    simp only [halfDown, halfUp, halfSet, mem_filter, mem_product, mem_range] at hq ⊢
    rcases hq with ⟨⟨⟨h1, h2⟩, hsum⟩, hlt⟩
    refine ⟨(M - q.1, M - q.2), ⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩, ?_⟩
    · have e1 : (((M - q.1 : ℕ) : ℤ) - ((M - q.2 : ℕ) : ℤ)) = -((q.1 : ℤ) - (q.2 : ℤ)) := by omega
      have e2 : (((M - q.2 : ℕ) : ℤ) - (m : ℤ)) = -((q.2 : ℤ) - ((M - m : ℕ) : ℤ)) := by omega
      rw [e1, e2, Int.natAbs_neg, Int.natAbs_neg]
      exact hsum
    · ext <;> omega

private lemma halfCount_symm (M m s : ℕ) (hm : m ≤ M) :
    halfCount M (M - m) s = halfCount M m s := by
  unfold halfCount
  apply Finset.card_bij (fun p _ => (M - p.1, M - p.2))
  · intro p hp
    simp only [halfSet, mem_filter, mem_product, mem_range] at hp ⊢
    rcases hp with ⟨⟨h1, h2⟩, hsum⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have e1 : (((M - p.1 : ℕ) : ℤ) - ((M - p.2 : ℕ) : ℤ)) = -((p.1 : ℤ) - (p.2 : ℤ)) := by omega
    have e2 : (((M - p.2 : ℕ) : ℤ) - (m : ℤ)) = -((p.2 : ℤ) - ((M - m : ℕ) : ℤ)) := by omega
    rw [e1, e2, Int.natAbs_neg, Int.natAbs_neg]
    exact hsum
  · intro p1 hp1 p2 hp2 heq
    simp only [halfSet, mem_filter, mem_product, mem_range] at hp1 hp2
    simp only [Prod.mk.injEq] at heq
    ext <;> omega
  · intro q hq
    simp only [halfSet, mem_filter, mem_product, mem_range] at hq ⊢
    rcases hq with ⟨⟨h1, h2⟩, hsum⟩
    refine ⟨(M - q.1, M - q.2), ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
    · have e1 : (((M - q.1 : ℕ) : ℤ) - ((M - q.2 : ℕ) : ℤ)) = -((q.1 : ℤ) - (q.2 : ℤ)) := by omega
      have e2 : (((M - q.2 : ℕ) : ℤ) - ((M - m : ℕ) : ℤ)) = -((q.2 : ℤ) - (m : ℤ)) := by omega
      rw [e1, e2, Int.natAbs_neg, Int.natAbs_neg]
      exact hsum
    · ext <;> omega

private lemma halfEq_card (M m s : ℕ) (hm : m ≤ M) :
    (halfEq M m s).card =
      if s = 0 then 1 else (if m + s ≤ M then 1 else 0) + (if s ≤ m then 1 else 0) := by
  have hbij : (halfEq M m s).card =
      ((range (M + 1)).filter fun b : ℕ => Int.natAbs ((b : ℤ) - (m : ℤ)) = s).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · intro p hp
      simp only [halfEq, halfSet, mem_filter, mem_product, mem_range] at hp ⊢
      rcases hp with ⟨⟨⟨_, h2⟩, hsum⟩, heq⟩
      refine ⟨h2, ?_⟩
      rw [heq, sub_self, Int.natAbs_zero, zero_add] at hsum
      exact hsum
    · intro p1 hp1 p2 hp2 heq
      simp only [halfEq, mem_filter] at hp1 hp2
      ext <;> omega
    · intro b hb
      simp only [mem_filter, mem_range] at hb
      refine ⟨(b, b), ?_, rfl⟩
      simp only [halfEq, halfSet, mem_filter, mem_product, mem_range]
      refine ⟨⟨⟨hb.1, hb.1⟩, ?_⟩, trivial⟩
      rw [sub_self, Int.natAbs_zero, zero_add]
      exact hb.2
  rw [hbij]
  split_ifs with hs0 h1 h2
  · subst hs0
    have hset : (range (M + 1)).filter (fun b : ℕ => Int.natAbs ((b : ℤ) - (m : ℤ)) = 0) = {m} := by
      ext b; simp only [mem_filter, mem_range, mem_singleton]; omega
    rw [hset, card_singleton]
  · have hset : (range (M + 1)).filter (fun b : ℕ => Int.natAbs ((b : ℤ) - (m : ℤ)) = s) =
        {m + s, m - s} := by
      ext b; simp only [mem_filter, mem_range, mem_insert, mem_singleton]; omega
    rw [hset, card_pair (by omega)]
  · have hset : (range (M + 1)).filter (fun b : ℕ => Int.natAbs ((b : ℤ) - (m : ℤ)) = s) = {m + s} := by
      ext b; simp only [mem_filter, mem_range, mem_singleton]; omega
    rw [hset, card_singleton]
  · have hset : (range (M + 1)).filter (fun b : ℕ => Int.natAbs ((b : ℤ) - (m : ℤ)) = s) = {m - s} := by
      ext b; simp only [mem_filter, mem_range, mem_singleton]; omega
    rw [hset, card_singleton]
  · have hset : (range (M + 1)).filter (fun b : ℕ => Int.natAbs ((b : ℤ) - (m : ℤ)) = s) = ∅ := by
      ext b; simp only [mem_filter, mem_range, notMem_empty, iff_false]; omega
    rw [hset, card_empty]

private lemma halfUp_card (M m s : ℕ) (hm : m ≤ M) :
    (halfUp M m s).card =
      (if m + s ≤ M then s else 0) +
      (if s = 0 ∨ M + m < s ∨ m = 0 then 0
       else min (m - 1) ((M + m - s) / 2) + 1 - (m + 1 - s)) := by
  let S : Finset ℕ := (range (M + 1)).filter fun b : ℕ =>
    Int.natAbs ((b : ℤ) - (m : ℤ)) < s ∧ b + (s - Int.natAbs ((b : ℤ) - (m : ℤ))) ≤ M
  have hbij : (halfUp M m s).card = S.card := by
    apply Finset.card_bij (fun p _ => p.2)
    · intro p hp
      simp only [halfUp, halfSet, S, mem_filter, mem_product, mem_range] at hp ⊢
      rcases hp with ⟨⟨⟨h1, h2⟩, hsum⟩, hlt⟩
      refine ⟨h2, ?_, ?_⟩ <;> omega
    · intro p1 hp1 p2 hp2 heq
      simp only [halfUp, halfSet, mem_filter] at hp1 hp2
      ext <;> omega
    · intro b hb
      simp only [S, mem_filter, mem_range] at hb
      refine ⟨(b + (s - Int.natAbs ((b : ℤ) - (m : ℤ))), b), ?_, rfl⟩
      simp only [halfUp, halfSet, mem_filter, mem_product, mem_range]
      refine ⟨⟨⟨by omega, hb.1⟩, ?_⟩, by omega⟩
      omega
  rw [hbij]
  let Sge := S.filter fun b : ℕ => m ≤ b
  let Slt := S.filter fun b : ℕ => b < m
  have hdisj : Disjoint Sge Slt := by
    rw [Finset.disjoint_filter]; intro b _ h1 h2; omega
  have hun : Sge ∪ Slt = S := by
    ext b; simp only [Sge, Slt, mem_union, mem_filter]; constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩); exact h; exact h
    · intro h; by_cases hmb : m ≤ b; exact Or.inl ⟨h, hmb⟩; exact Or.inr ⟨h, by omega⟩
  rw [← hun, Finset.card_union_of_disjoint hdisj]
  congr 1
  · by_cases hms : m + s ≤ M
    · have hset : Sge = Finset.Ico m (m + s) := by
        ext b
        simp only [Sge, S, mem_filter, mem_range, Finset.mem_Ico]
        omega
      rw [hset, Nat.card_Ico, if_pos hms]
      omega
    · have hset : Sge = ∅ := by
        ext b
        simp only [Sge, S, mem_filter, mem_range, notMem_empty, iff_false]
        omega
      rw [hset, card_empty, if_neg hms]
  · by_cases hbad : s = 0 ∨ M + m < s ∨ m = 0
    · rw [if_pos hbad]
      have hset : Slt = ∅ := by
        ext b; simp only [Slt, S, mem_filter, mem_range, notMem_empty, iff_false]; omega
      rw [hset, card_empty]
    · rw [if_neg hbad]
      have hset : Slt = Finset.Icc (m + 1 - s) (min (m - 1) ((M + m - s) / 2)) := by
        ext b
        simp only [Slt, S, mem_filter, mem_range, Finset.mem_Icc]
        omega
      rw [hset, Nat.card_Icc]

private def halfPiece (n m s : ℕ) : ℕ :=
  if s = 0 then 1
  else if s ≤ m then 4 * s
  else if s ≤ 2 * n - m then s + m + 1 + (m + s) / 2
  else if s ≤ 2 * n + m then (2 * n + m - s) / 2 + (4 * n - m - s) / 2 + 2
  else if s ≤ 4 * n - m then (4 * n - m - s) / 2 + 1
  else 0

private lemma halfCount_eq_piece (n m s : ℕ) (hm : m ≤ n) :
    halfCount (2 * n) m s = halfPiece n m s := by
  rw [halfSet_card_split, halfDown_card_eq_halfUp (2 * n) m s (by omega),
    halfUp_card (2 * n) m s (by omega), halfUp_card (2 * n) (2 * n - m) s (by omega),
    halfEq_card (2 * n) m s (by omega)]
  unfold halfPiece
  by_cases hs0 : s = 0
  · subst hs0; simp
  · by_cases hsm : s ≤ m
    · rw [if_pos (by omega : m + s ≤ 2 * n),
        if_neg (by rintro (h | h | h) <;> omega : ¬ (s = 0 ∨ 2 * n + m < s ∨ m = 0)),
        if_pos (by omega : 2 * n - m + s ≤ 2 * n),
        if_neg (by rintro (h | h | h) <;> omega : ¬ (s = 0 ∨ 2 * n + (2 * n - m) < s ∨ 2 * n - m = 0)),
        if_neg hs0, if_pos (by omega : m + s ≤ 2 * n), if_pos hsm,
        if_neg hs0, if_pos hsm,
        min_eq_left (by omega), min_eq_left (by omega)]
      omega
    · by_cases hs1 : s ≤ 2 * n - m
      · rw [if_pos (by omega : m + s ≤ 2 * n),
          if_neg (by omega : ¬ 2 * n - m + s ≤ 2 * n),
          if_neg (by rintro (h | h | h) <;> omega : ¬ (s = 0 ∨ 2 * n + (2 * n - m) < s ∨ 2 * n - m = 0)),
          if_neg hs0, if_pos (by omega : m + s ≤ 2 * n), if_neg hsm,
          if_neg hs0, if_neg hsm, if_pos hs1,
          min_eq_right (by omega : (2 * n + (2 * n - m) - s) / 2 ≤ 2 * n - m - 1)]
        by_cases hm0 : m = 0
        · rw [if_pos (Or.inr (Or.inr hm0))]; omega
        · rw [if_neg (by rintro (h | h | h) <;> omega : ¬ (s = 0 ∨ 2 * n + m < s ∨ m = 0)),
            min_eq_left (by omega : m - 1 ≤ (2 * n + m - s) / 2)]
          omega
      · by_cases hs2 : s ≤ 2 * n + m
        · rw [if_neg (by omega : ¬ m + s ≤ 2 * n),
            if_neg (by rintro (h | h | h) <;> omega : ¬ (s = 0 ∨ 2 * n + m < s ∨ m = 0)),
            if_neg (by omega : ¬ 2 * n - m + s ≤ 2 * n),
            if_neg (by rintro (h | h | h) <;> omega : ¬ (s = 0 ∨ 2 * n + (2 * n - m) < s ∨ 2 * n - m = 0)),
            if_neg hs0, if_neg (by omega : ¬ m + s ≤ 2 * n), if_neg hsm,
            if_neg hs0, if_neg hsm, if_neg hs1, if_pos hs2,
            min_eq_right (by omega : (2 * n + m - s) / 2 ≤ m - 1),
            min_eq_right (by omega : (2 * n + (2 * n - m) - s) / 2 ≤ 2 * n - m - 1)]
          omega
        · by_cases hs3 : s ≤ 4 * n - m
          · rw [if_neg (by omega : ¬ m + s ≤ 2 * n),
              if_pos (Or.inr (Or.inl (by omega : 2 * n + m < s))),
              if_neg (by omega : ¬ 2 * n - m + s ≤ 2 * n),
              if_neg (by rintro (h | h | h) <;> omega : ¬ (s = 0 ∨ 2 * n + (2 * n - m) < s ∨ 2 * n - m = 0)),
              if_neg hs0, if_neg (by omega : ¬ m + s ≤ 2 * n), if_neg hsm,
              if_neg hs0, if_neg hsm, if_neg hs1, if_neg hs2, if_pos hs3,
              min_eq_right (by omega : (2 * n + (2 * n - m) - s) / 2 ≤ 2 * n - m - 1)]
            omega
          · rw [if_neg (by omega : ¬ m + s ≤ 2 * n),
              if_pos (Or.inr (Or.inl (by omega : 2 * n + m < s))),
              if_neg (by omega : ¬ 2 * n - m + s ≤ 2 * n),
              if_pos (Or.inr (Or.inl (by omega : 2 * n + (2 * n - m) < s))),
              if_neg hs0, if_neg (by omega : ¬ m + s ≤ 2 * n), if_neg hsm,
              if_neg hs0, if_neg hsm, if_neg hs1, if_neg hs2, if_neg hs3]

private lemma a_eq_sum_halfCount (n : ℕ) :
    a n = ∑ m ∈ range (2 * n + 1), ∑ s ∈ range (4 * n + 1),
      halfCount (2 * n) m s * halfCount (2 * n) m (4 * n - s) := by
  unfold a
  have hstep :
      (Finset.univ.filter fun x : Fin 5 → Fin (2 * n + 1) => variation x = 4 * n).card =
      ∑ m ∈ range (2 * n + 1), ∑ s ∈ range (4 * n + 1),
        (Finset.univ.filter fun x : Fin 5 → Fin (2 * n + 1) =>
          variation x = 4 * n ∧ (x 2).val = m ∧
          Int.natAbs (((x 0).val : ℤ) - ((x 1).val : ℤ)) +
            Int.natAbs (((x 1).val : ℤ) - ((x 2).val : ℤ)) = s).card := by
    rw [← Finset.sum_product']
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [mem_biUnion, mem_product, mem_range, mem_filter, mem_univ, true_and]
      constructor
      · intro hx
        refine ⟨((x 2).val, Int.natAbs (((x 0).val : ℤ) - ((x 1).val : ℤ)) +
            Int.natAbs (((x 1).val : ℤ) - ((x 2).val : ℤ))), ⟨(x 2).isLt, ?_⟩, hx, rfl, rfl⟩
        unfold variation at hx
        simp only [Fin.sum_univ_four, Int.abs_eq_natAbs] at hx
        have h0 := (x 0).isLt; have h1 := (x 1).isLt; have h2 := (x 2).isLt
        have h3 := (x 3).isLt; have h4 := (x 4).isLt
        omega
      · rintro ⟨_, _, hx, _, _⟩
        exact hx
    · intro p _ q _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro x _ hx1 hx2
      apply hne
      ext
      · exact hx1.2.1.symm.trans hx2.2.1
      · exact hx1.2.2.symm.trans hx2.2.2
  rw [hstep]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro s hs
  rw [mem_range] at hm hs
  unfold halfCount
  rw [← Finset.card_product]
  apply Finset.card_bij (fun x _ => (((x 0).val, (x 1).val), ((x 4).val, (x 3).val)))
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rcases hx with ⟨hvar, hm2, hs1⟩
    unfold variation at hvar
    simp only [Fin.sum_univ_four, Int.abs_eq_natAbs] at hvar
    change (((x 0).val : ℤ) - ((x 1).val : ℤ)).natAbs +
        (((x 1).val : ℤ) - ((x 2).val : ℤ)).natAbs +
        (((x 2).val : ℤ) - ((x 3).val : ℤ)).natAbs +
        (((x 3).val : ℤ) - ((x 4).val : ℤ)).natAbs = 4 * (n : ℤ) at hvar
    simp only [mem_product, halfSet, mem_filter, mem_range]
    refine ⟨⟨⟨(x 0).isLt, (x 1).isLt⟩, ?_⟩, ⟨⟨(x 4).isLt, (x 3).isLt⟩, ?_⟩⟩
    · rw [← hm2]; exact hs1
    · have hswap1 : Int.natAbs (((x 4).val : ℤ) - ((x 3).val : ℤ)) =
          Int.natAbs (((x 3).val : ℤ) - ((x 4).val : ℤ)) := by
        rw [← Int.natAbs_neg]; congr 1; ring
      have hswap2 : Int.natAbs (((x 3).val : ℤ) - (m : ℤ)) =
          Int.natAbs (((x 2).val : ℤ) - ((x 3).val : ℤ)) := by
        rw [← hm2, ← Int.natAbs_neg]; congr 1; ring
      rw [hswap1, hswap2]
      omega
  · intro x1 hx1 x2 hx2 heq
    simp only [mem_filter, mem_univ, true_and] at hx1 hx2
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨⟨e0, e1⟩, ⟨e4, e3⟩⟩
    have e2 : (x1 2).val = (x2 2).val := hx1.2.1.trans hx2.2.1.symm
    funext i
    fin_cases i
    · exact Fin.ext e0
    · exact Fin.ext e1
    · exact Fin.ext e2
    · exact Fin.ext e3
    · exact Fin.ext e4
  · intro y hy
    simp only [mem_product, halfSet, mem_filter, mem_range] at hy
    rcases hy with ⟨⟨⟨h0, h1⟩, hs1⟩, ⟨⟨h4, h3⟩, hs2⟩⟩
    let x : Fin 5 → Fin (2 * n + 1) := fun i =>
      match i with
      | ⟨0, _⟩ => ⟨y.1.1, h0⟩
      | ⟨1, _⟩ => ⟨y.1.2, h1⟩
      | ⟨2, _⟩ => ⟨m, hm⟩
      | ⟨3, _⟩ => ⟨y.2.2, h3⟩
      | ⟨4, _⟩ => ⟨y.2.1, h4⟩
    refine ⟨x, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and, variation, Fin.sum_univ_four, Int.abs_eq_natAbs, x]
    have hswap1 : Int.natAbs (((y.2.2 : ℕ) : ℤ) - ((y.2.1 : ℕ) : ℤ)) =
        Int.natAbs (((y.2.1 : ℕ) : ℤ) - ((y.2.2 : ℕ) : ℤ)) := by
      rw [← Int.natAbs_neg]; congr 1; ring
    have hswap2 : Int.natAbs ((m : ℤ) - ((y.2.2 : ℕ) : ℤ)) =
        Int.natAbs (((y.2.2 : ℕ) : ℤ) - (m : ℤ)) := by
      rw [← Int.natAbs_neg]; congr 1; ring
    refine ⟨?_, ?_⟩
    · simp only [Fin.isValue, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one,
        Fin.succ_one_eq_two]
      change (((y.1.1 : ℤ) - (y.1.2 : ℤ)).natAbs : ℤ) +
        (((y.1.2 : ℤ) - (m : ℤ)).natAbs : ℤ) +
        (((m : ℤ) - (y.2.2 : ℤ)).natAbs : ℤ) +
        (((y.2.2 : ℤ) - (y.2.1 : ℤ)).natAbs : ℤ) = 4 * (n : ℤ)
      rw [hswap1, hswap2]
      omega
    · exact hs1

private def g (n m : ℕ) : ℤ :=
  ∑ s ∈ range (4 * n + 1), (halfCount (2 * n) m s : ℤ) * (halfCount (2 * n) m (4 * n - s) : ℤ)

private lemma g_symm (n m : ℕ) (hm : m ≤ 2 * n) : g n (2 * n - m) = g n m := by
  unfold g
  apply Finset.sum_congr rfl
  intro s _
  rw [halfCount_symm (2 * n) m s hm, halfCount_symm (2 * n) m (4 * n - s) hm]

private lemma sum_id_int (N : ℕ) : 2 * ∑ k ∈ range N, (k : ℤ) = (N : ℤ) * ((N : ℤ) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

private lemma sum_sq_int (N : ℕ) :
    6 * ∑ k ∈ range N, (k : ℤ) ^ 2 = (N : ℤ) * ((N : ℤ) - 1) * (2 * (N : ℤ) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

private lemma sum_cube_int (N : ℕ) :
    4 * ∑ k ∈ range N, (k : ℤ) ^ 3 = (N : ℤ) ^ 2 * ((N : ℤ) - 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

private lemma sum_even_odd (N : ℕ) (f : ℕ → ℤ) :
    ∑ t ∈ range (2 * N), f t =
      (∑ k ∈ range N, f (2 * k)) + (∑ k ∈ range N, f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

private lemma sum_Ioo_reflect (n a b : ℕ) (ha : a ≤ b) (hb : b ≤ 4 * n) (f : ℕ → ℤ) :
    ∑ s ∈ Finset.Ioo (4 * n - b) (4 * n - a), f (4 * n - s) = ∑ s ∈ Finset.Ioo a b, f s := by
  apply Finset.sum_bij (fun s _ => 4 * n - s)
  · intro s hs; rw [Finset.mem_Ioo] at hs ⊢; omega
  · intro s1 hs1 s2 hs2 heq; rw [Finset.mem_Ioo] at hs1 hs2; omega
  · intro t ht; rw [Finset.mem_Ioo] at ht
    refine ⟨4 * n - t, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro s _; rfl

private lemma sum_quad_type1 (m L : ℕ) :
    6 * ((∑ k ∈ range L, (3 * (m : ℤ) + 1 + 3 * k) * (k + 1)) +
         (∑ k ∈ range L, (3 * (m : ℤ) + 2 + 3 * k) * (k + 1))) =
      12 * (L : ℤ) ^ 3 + (18 * (m : ℤ) + 9) * (L : ℤ) ^ 2 + (18 * (m : ℤ) - 3) * (L : ℤ) := by
  have h1 : (∑ k ∈ range L, (3 * (m : ℤ) + 1 + 3 * k) * (k + 1)) +
      (∑ k ∈ range L, (3 * (m : ℤ) + 2 + 3 * k) * (k + 1)) =
      6 * (∑ k ∈ range L, (k : ℤ) ^ 2) + (6 * (m : ℤ) + 9) * (∑ k ∈ range L, (k : ℤ)) +
      (6 * (m : ℤ) + 3) * (L : ℤ) := by
    rw [← Finset.sum_add_distrib]
    have hpt : ∀ k ∈ range L,
        (3 * (m : ℤ) + 1 + 3 * (k : ℤ)) * ((k : ℤ) + 1) +
        (3 * (m : ℤ) + 2 + 3 * (k : ℤ)) * ((k : ℤ) + 1) =
        6 * (k : ℤ) ^ 2 + (6 * (m : ℤ) + 9) * (k : ℤ) + (6 * (m : ℤ) + 3) := by
      intro k _; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, card_range, nsmul_eq_mul]
    ring
  have h2 := sum_sq_int L
  have h3 := sum_id_int L
  linear_combination 6 * h1 + 6 * h2 + (18 * (m : ℤ) + 27) * h3

private lemma sum_quad_type2 (n m : ℕ) :
    3 * ((∑ k ∈ range m, ((n : ℤ) + m + 2 - 2 * k) * ((n : ℤ) - m + 2 + 2 * k)) +
         (∑ k ∈ range m, ((n : ℤ) + m - 2 * k) * ((n : ℤ) - m + 2 + 2 * k))) =
      6 * (m : ℤ) * (n : ℤ) ^ 2 - 2 * (m : ℤ) ^ 3 + 18 * (m : ℤ) * (n : ℤ) +
      14 * (m : ℤ) := by
  have h1 : (∑ k ∈ range m, ((n : ℤ) + m + 2 - 2 * k) * ((n : ℤ) - m + 2 + 2 * k)) +
      (∑ k ∈ range m, ((n : ℤ) + m - 2 * k) * ((n : ℤ) - m + 2 + 2 * k)) =
      -8 * (∑ k ∈ range m, (k : ℤ) ^ 2) + (8 * (m : ℤ) - 4) * (∑ k ∈ range m, (k : ℤ)) +
      (2 * (n : ℤ) ^ 2 - 2 * (m : ℤ) ^ 2 + 6 * (n : ℤ) + 2 * (m : ℤ) + 4) * (m : ℤ) := by
    rw [← Finset.sum_add_distrib]
    have hpt : ∀ k ∈ range m,
        ((n : ℤ) + m + 2 - 2 * (k : ℤ)) * ((n : ℤ) - m + 2 + 2 * (k : ℤ)) +
        ((n : ℤ) + m - 2 * (k : ℤ)) * ((n : ℤ) - m + 2 + 2 * (k : ℤ)) =
        -8 * (k : ℤ) ^ 2 + (8 * (m : ℤ) - 4) * (k : ℤ) +
        (2 * (n : ℤ) ^ 2 - 2 * (m : ℤ) ^ 2 + 6 * (n : ℤ) + 2 * (m : ℤ) + 4) := by
      intro k _; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, card_range, nsmul_eq_mul]
    ring
  have h2 := sum_sq_int m
  have h3 := sum_id_int m
  have h6 : 6 * ((∑ k ∈ range m, ((n : ℤ) + m + 2 - 2 * k) * ((n : ℤ) - m + 2 + 2 * k)) +
      (∑ k ∈ range m, ((n : ℤ) + m - 2 * k) * ((n : ℤ) - m + 2 + 2 * k))) =
      2 * (6 * (m : ℤ) * (n : ℤ) ^ 2 - 2 * (m : ℤ) ^ 3 + 18 * (m : ℤ) * (n : ℤ) +
        14 * (m : ℤ)) := by
    linear_combination 6 * h1 - 8 * h2 + (24 * (m : ℤ) - 12) * h3
  linarith

private lemma g_zero (n : ℕ) (hn : 1 ≤ n) :
    g n 0 = 4 * (n : ℤ) ^ 3 + 12 * (n : ℤ) ^ 2 + 5 * (n : ℤ) + 1 := by
  unfold g
  have hpt : ∀ s ∈ range (4 * n + 1),
      (halfCount (2 * n) 0 s : ℤ) * (halfCount (2 * n) 0 (4 * n - s) : ℤ) =
      (halfPiece n 0 s : ℤ) * (halfPiece n 0 (4 * n - s) : ℤ) := by
    intro s _
    rw [halfCount_eq_piece n 0 s (by omega), halfCount_eq_piece n 0 (4 * n - s) (by omega)]
  rw [Finset.sum_congr rfl hpt]
  let F : ℕ → ℤ := fun s => (halfPiece n 0 s : ℤ) * (halfPiece n 0 (4 * n - s) : ℤ)
  change ∑ s ∈ range (4 * n + 1), F s = _
  have hpart : range (4 * n + 1) =
      insert 0 (insert (2 * n) (insert (4 * n)
        (Finset.Ioo 0 (2 * n) ∪ Finset.Ioo (2 * n) (4 * n)))) := by
    ext s
    simp only [mem_range, mem_insert, mem_union, Finset.mem_Ioo]
    omega
  rw [hpart,
    Finset.sum_insert (by simp only [mem_insert, mem_union, Finset.mem_Ioo]; omega),
    Finset.sum_insert (by simp only [mem_insert, mem_union, Finset.mem_Ioo]; omega),
    Finset.sum_insert (by simp only [mem_union, Finset.mem_Ioo]; omega),
    Finset.sum_union (by rw [Finset.disjoint_left]; intro s hs1 hs2; simp only [Finset.mem_Ioo] at hs1 hs2; omega)]
  have hsym : ∑ s ∈ Finset.Ioo (2 * n) (4 * n), F s = ∑ s ∈ Finset.Ioo 0 (2 * n), F s := by
    have hr := sum_Ioo_reflect n 0 (2 * n) (by omega) (by omega) F
    rw [show 4 * n - 2 * n = 2 * n by omega, Nat.sub_zero] at hr
    rw [← hr]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_Ioo] at hs
    simp only [F]
    rw [show 4 * n - (4 * n - s) = s by omega, mul_comm]
  rw [hsym]
  have hF0 : F 0 = 1 := by
    have h1 : halfPiece n 0 0 = 1 := by unfold halfPiece; simp
    have h2 : halfPiece n 0 (4 * n) = 1 := by unfold halfPiece; split_ifs <;> omega
    simp only [F, Nat.sub_zero, h1, h2]; norm_num
  have hF4 : F (4 * n) = 1 := by
    have h1 : halfPiece n 0 0 = 1 := by unfold halfPiece; simp
    have h2 : halfPiece n 0 (4 * n) = 1 := by unfold halfPiece; split_ifs <;> omega
    simp only [F, Nat.sub_self, h1, h2]; norm_num
  have hF2 : F (2 * n) = (3 * (n : ℤ) + 1) ^ 2 := by
    have hval : halfPiece n 0 (2 * n) = 3 * n + 1 := by
      unfold halfPiece; split_ifs <;> omega
    simp only [F, show 4 * n - 2 * n = 2 * n by omega, hval]
    push_cast; ring
  have hIoo : ∑ s ∈ Finset.Ioo 0 (2 * n), F s =
      (∑ k ∈ range n, (1 + 3 * (k : ℤ)) * ((k : ℤ) + 1)) +
      (∑ k ∈ range n, (2 + 3 * (k : ℤ)) * ((k : ℤ) + 1)) - 1 := by
    have hterm : ∀ t ∈ range (2 * n),
        (if t = 0 then (1 : ℤ) else F t) =
        (1 + (t : ℤ) + ((t / 2 : ℕ) : ℤ)) * (((t / 2 : ℕ) : ℤ) + 1) := by
      intro t ht
      rw [mem_range] at ht
      by_cases ht0 : t = 0
      · subst ht0; norm_num
      · rw [if_neg ht0]
        have hp1 : halfPiece n 0 t = t + 1 + t / 2 := by unfold halfPiece; split_ifs <;> omega
        have hp2 : halfPiece n 0 (4 * n - t) = t / 2 + 1 := by unfold halfPiece; split_ifs <;> omega
        simp only [F, hp1, hp2]
        push_cast; ring
    have hadd : (∑ s ∈ Finset.Ioo 0 (2 * n), F s) + 1 =
        ∑ t ∈ range (2 * n), (1 + (t : ℤ) + ((t / 2 : ℕ) : ℤ)) * (((t / 2 : ℕ) : ℤ) + 1) := by
      rw [← Finset.sum_congr rfl hterm]
      have h0mem : (0 : ℕ) ∈ range (2 * n) := by rw [mem_range]; omega
      rw [← Finset.add_sum_erase _ _ h0mem]
      simp only [if_true]
      have herase : (range (2 * n)).erase 0 = Finset.Ioo 0 (2 * n) := by
        ext s; simp only [mem_erase, mem_range, Finset.mem_Ioo]; omega
      rw [herase, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_Ioo] at hs
      rw [if_neg (by omega)]
    rw [sum_even_odd] at hadd
    have he1 : ∑ k ∈ range n, (1 + ((2 * k : ℕ) : ℤ) + (((2 * k) / 2 : ℕ) : ℤ)) *
        ((((2 * k) / 2 : ℕ) : ℤ) + 1) =
        ∑ k ∈ range n, (1 + 3 * (k : ℤ)) * ((k : ℤ) + 1) := by
      apply Finset.sum_congr rfl; intro k _
      rw [show (2 * k) / 2 = k by omega]; push_cast; ring
    have he2 : ∑ k ∈ range n, (1 + ((2 * k + 1 : ℕ) : ℤ) + (((2 * k + 1) / 2 : ℕ) : ℤ)) *
        ((((2 * k + 1) / 2 : ℕ) : ℤ) + 1) =
        ∑ k ∈ range n, (2 + 3 * (k : ℤ)) * ((k : ℤ) + 1) := by
      apply Finset.sum_congr rfl; intro k _
      rw [show (2 * k + 1) / 2 = k by omega]; push_cast; ring
    rw [he1, he2] at hadd
    linarith
  have hq := sum_quad_type1 0 n
  simp only [Nat.cast_zero, mul_zero, zero_add] at hq
  rw [hF0, hF2, hF4, hIoo]
  have h3 : 3 * (1 + ((3 * (n : ℤ) + 1) ^ 2 + (1 +
      (((∑ k ∈ range n, (1 + 3 * (k : ℤ)) * ((k : ℤ) + 1)) +
        (∑ k ∈ range n, (2 + 3 * (k : ℤ)) * ((k : ℤ) + 1)) - 1) +
       ((∑ k ∈ range n, (1 + 3 * (k : ℤ)) * ((k : ℤ) + 1)) +
        (∑ k ∈ range n, (2 + 3 * (k : ℤ)) * ((k : ℤ) + 1)) - 1))))) =
      3 * (4 * (n : ℤ) ^ 3 + 12 * (n : ℤ) ^ 2 + 5 * (n : ℤ) + 1) := by
    linear_combination hq
  linarith

private lemma g_mid (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m < n) :
    3 * g n m = 12 * (n : ℤ) ^ 3 - 12 * (n : ℤ) ^ 2 * m + 4 * (m : ℤ) ^ 3 +
      24 * (n : ℤ) ^ 2 - 6 * (m : ℤ) ^ 2 + 27 * (n : ℤ) + 17 * (m : ℤ) - 6 := by
  unfold g
  have hpt : ∀ s ∈ range (4 * n + 1),
      (halfCount (2 * n) m s : ℤ) * (halfCount (2 * n) m (4 * n - s) : ℤ) =
      (halfPiece n m s : ℤ) * (halfPiece n m (4 * n - s) : ℤ) := by
    intro s _
    rw [halfCount_eq_piece n m s (by omega), halfCount_eq_piece n m (4 * n - s) (by omega)]
  rw [Finset.sum_congr rfl hpt]
  let F : ℕ → ℤ := fun s => (halfPiece n m s : ℤ) * (halfPiece n m (4 * n - s) : ℤ)
  change 3 * ∑ s ∈ range (4 * n + 1), F s = _
  have hzero : ∀ s ∈ range (4 * n + 1), (s < m ∨ 4 * n - m < s) → F s = 0 := by
    intro s hs htail
    rw [mem_range] at hs
    simp only [F]
    rcases htail with h1 | h2
    · have hp : halfPiece n m (4 * n - s) = 0 := by unfold halfPiece; split_ifs <;> omega
      rw [hp]; simp
    · have hp : halfPiece n m s = 0 := by unfold halfPiece; split_ifs <;> omega
      rw [hp]; simp
  let core : Finset ℕ :=
    insert m (insert (4 * n - m) (insert (2 * n - m) (insert (2 * n + m)
      (Finset.Ioo m (2 * n - m) ∪ Finset.Ioo (2 * n + m) (4 * n - m) ∪
        Finset.Ioo (2 * n - m) (2 * n + m)))))
  have hsum_core : ∑ s ∈ range (4 * n + 1), F s = ∑ s ∈ core, F s := by
    symm
    apply Finset.sum_subset
    · intro s hs
      simp only [core, mem_insert, mem_union, Finset.mem_Ioo] at hs
      rw [mem_range]; omega
    · intro s hs hnot
      apply hzero s hs
      simp only [core, mem_insert, mem_union, Finset.mem_Ioo] at hnot
      rw [mem_range] at hs
      omega
  rw [hsum_core]
  simp only [core]
  rw [Finset.sum_insert (by simp only [mem_insert, mem_union, Finset.mem_Ioo]; omega),
    Finset.sum_insert (by simp only [mem_insert, mem_union, Finset.mem_Ioo]; omega),
    Finset.sum_insert (by simp only [mem_insert, mem_union, Finset.mem_Ioo]; omega),
    Finset.sum_insert (by simp only [mem_union, Finset.mem_Ioo]; omega),
    Finset.sum_union (by rw [Finset.disjoint_left]; intro s h1 h2; simp only [mem_union, Finset.mem_Ioo] at h1 h2; omega),
    Finset.sum_union (by rw [Finset.disjoint_left]; intro s h1 h2; simp only [Finset.mem_Ioo] at h1 h2; omega)]
  have hFm : F m = 4 * (m : ℤ) := by
    have h1 : halfPiece n m m = 4 * m := by unfold halfPiece; split_ifs <;> omega
    have h2 : halfPiece n m (4 * n - m) = 1 := by unfold halfPiece; split_ifs <;> omega
    simp only [F, h1, h2]; push_cast; ring
  have hF4m : F (4 * n - m) = 4 * (m : ℤ) := by
    have hsub : 4 * n - (4 * n - m) = m := by omega
    simp only [F]
    rw [hsub, mul_comm]
    exact hFm
  have hF2m : F (2 * n - m) = (3 * (n : ℤ) + 1) * ((n : ℤ) - m + 2) := by
    have h1 : halfPiece n m (2 * n - m) = 3 * n + 1 := by unfold halfPiece; split_ifs <;> omega
    have h2 : halfPiece n m (4 * n - (2 * n - m)) = n - m + 2 := by
      rw [show 4 * n - (2 * n - m) = 2 * n + m by omega]
      unfold halfPiece; split_ifs <;> omega
    simp only [F, h1, h2]
    have hmn' : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Nat.cast_sub (by omega)
    push_cast; rw [hmn']
  have hF2p : F (2 * n + m) = (3 * (n : ℤ) + 1) * ((n : ℤ) - m + 2) := by
    have hsub : 4 * n - (2 * n + m) = 2 * n - m := by omega
    have hsub2 : 4 * n - (2 * n - m) = 2 * n + m := by omega
    simp only [F]
    rw [hsub, mul_comm]
    simpa only [F, hsub2] using hF2m
  have hsym1 : ∑ s ∈ Finset.Ioo (2 * n + m) (4 * n - m), F s =
      ∑ s ∈ Finset.Ioo m (2 * n - m), F s := by
    have hr := sum_Ioo_reflect n m (2 * n - m) (by omega) (by omega) F
    rw [show 4 * n - (2 * n - m) = 2 * n + m by omega] at hr
    rw [← hr]
    apply Finset.sum_congr rfl
    intro s hs; rw [Finset.mem_Ioo] at hs
    simp only [F]
    rw [show 4 * n - (4 * n - s) = s by omega, mul_comm]
  rw [hsym1]
  have hIoo1 : 6 * ∑ s ∈ Finset.Ioo m (2 * n - m), F s =
      12 * ((n : ℤ) - m) ^ 3 + (18 * (m : ℤ) + 9) * ((n : ℤ) - m) ^ 2 +
      (18 * (m : ℤ) - 3) * ((n : ℤ) - m) - 6 * (3 * (m : ℤ) + 1) := by
    let L := n - m
    have hL : (L : ℤ) = (n : ℤ) - m := Nat.cast_sub (by omega)
    have hadd : (∑ s ∈ Finset.Ioo m (2 * n - m), F s) + (3 * (m : ℤ) + 1) =
        ∑ t ∈ range (2 * L), (3 * (m : ℤ) + 1 + (t : ℤ) + ((t / 2 : ℕ) : ℤ)) *
          (((t / 2 : ℕ) : ℤ) + 1) := by
      have h0mem : (0 : ℕ) ∈ range (2 * L) := by rw [mem_range]; omega
      rw [← Finset.add_sum_erase _ _ h0mem]
      simp only [Nat.cast_zero, Nat.zero_div, add_zero, zero_add, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_bij (fun s _ => s - m)
      · intro s hs; rw [Finset.mem_Ioo] at hs; rw [mem_erase, mem_range]; omega
      · intro s1 hs1 s2 hs2 heq; rw [Finset.mem_Ioo] at hs1 hs2; omega
      · intro t ht; rw [mem_erase, mem_range] at ht
        refine ⟨m + t, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro s hs
        rw [Finset.mem_Ioo] at hs
        have hp1 : halfPiece n m s = 3 * m + 1 + (s - m) + (s - m) / 2 := by
          unfold halfPiece; split_ifs <;> omega
        have hp2 : halfPiece n m (4 * n - s) = (s - m) / 2 + 1 := by
          unfold halfPiece; split_ifs <;> omega
        simp only [F, hp1, hp2]; push_cast; ring
    rw [sum_even_odd] at hadd
    have he1 : ∑ k ∈ range L, (3 * (m : ℤ) + 1 + ((2 * k : ℕ) : ℤ) + (((2 * k) / 2 : ℕ) : ℤ)) *
        ((((2 * k) / 2 : ℕ) : ℤ) + 1) =
        ∑ k ∈ range L, (3 * (m : ℤ) + 1 + 3 * (k : ℤ)) * ((k : ℤ) + 1) := by
      apply Finset.sum_congr rfl; intro k _
      rw [show (2 * k) / 2 = k by omega]; push_cast; ring
    have he2 : ∑ k ∈ range L, (3 * (m : ℤ) + 1 + ((2 * k + 1 : ℕ) : ℤ) + (((2 * k + 1) / 2 : ℕ) : ℤ)) *
        ((((2 * k + 1) / 2 : ℕ) : ℤ) + 1) =
        ∑ k ∈ range L, (3 * (m : ℤ) + 2 + 3 * (k : ℤ)) * ((k : ℤ) + 1) := by
      apply Finset.sum_congr rfl; intro k _
      rw [show (2 * k + 1) / 2 = k by omega]; push_cast; ring
    rw [he1, he2] at hadd
    have hq := sum_quad_type1 m L
    rw [hL] at hq
    linear_combination 6 * hadd + hq
  have hIoo2 : 3 * ∑ s ∈ Finset.Ioo (2 * n - m) (2 * n + m), F s =
      6 * (m : ℤ) * (n : ℤ) ^ 2 - 2 * (m : ℤ) ^ 3 + 18 * (m : ℤ) * (n : ℤ) +
      14 * (m : ℤ) - 3 * ((n : ℤ) + m + 2) * ((n : ℤ) - m + 2) := by
    have hadd : (∑ s ∈ Finset.Ioo (2 * n - m) (2 * n + m), F s) +
        ((n : ℤ) + m + 2) * ((n : ℤ) - m + 2) =
        ∑ t ∈ range (2 * m),
          ((((2 * m - t) / 2 : ℕ) : ℤ) + (((2 * n - t) / 2 : ℕ) : ℤ) + 2) *
          ((((t / 2 : ℕ) : ℤ) + (((2 * n - 2 * m + t) / 2 : ℕ) : ℤ) + 2)) := by
      have h0mem : (0 : ℕ) ∈ range (2 * m) := by rw [mem_range]; omega
      rw [← Finset.add_sum_erase _ _ h0mem]
      have h0val : ((((2 * m - 0) / 2 : ℕ) : ℤ) + (((2 * n - 0) / 2 : ℕ) : ℤ) + 2) *
          ((((0 / 2 : ℕ) : ℤ) + (((2 * n - 2 * m + 0) / 2 : ℕ) : ℤ) + 2)) =
          ((n : ℤ) + m + 2) * ((n : ℤ) - m + 2) := by
        rw [show (2 * m - 0) / 2 = m by omega, show (2 * n - 0) / 2 = n by omega,
          show (2 * n - 2 * m + 0) / 2 = n - m by omega]
        have hnm : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Nat.cast_sub (by omega)
        simp only [Nat.zero_div, Nat.cast_zero, zero_add, hnm]; ring
      rw [h0val, add_comm]
      congr 1
      apply Finset.sum_bij (fun s _ => s - (2 * n - m))
      · intro s hs; rw [Finset.mem_Ioo] at hs; rw [mem_erase, mem_range]; omega
      · intro s1 hs1 s2 hs2 heq; rw [Finset.mem_Ioo] at hs1 hs2; omega
      · intro t ht; rw [mem_erase, mem_range] at ht
        refine ⟨2 * n - m + t, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro s hs
        rw [Finset.mem_Ioo] at hs
        have hp1 : halfPiece n m s =
            (2 * m - (s - (2 * n - m))) / 2 + (2 * n - (s - (2 * n - m))) / 2 + 2 := by
          unfold halfPiece; split_ifs <;> omega
        have hp2 : halfPiece n m (4 * n - s) =
            (s - (2 * n - m)) / 2 + (2 * n - 2 * m + (s - (2 * n - m))) / 2 + 2 := by
          unfold halfPiece; split_ifs <;> omega
        simp only [F, hp1, hp2]; push_cast; ring
    rw [sum_even_odd] at hadd
    have he1 : ∑ k ∈ range m,
        ((((2 * m - 2 * k) / 2 : ℕ) : ℤ) + (((2 * n - 2 * k) / 2 : ℕ) : ℤ) + 2) *
        ((((2 * k) / 2 : ℕ) : ℤ) + (((2 * n - 2 * m + 2 * k) / 2 : ℕ) : ℤ) + 2) =
        ∑ k ∈ range m, ((n : ℤ) + m + 2 - 2 * k) * ((n : ℤ) - m + 2 + 2 * k) := by
      apply Finset.sum_congr rfl; intro k hk; rw [mem_range] at hk
      rw [show (2 * m - 2 * k) / 2 = m - k by omega,
        show (2 * n - 2 * k) / 2 = n - k by omega,
        show (2 * k) / 2 = k by omega,
        show (2 * n - 2 * m + 2 * k) / 2 = n - m + k by omega]
      have h1 : ((m - k : ℕ) : ℤ) = (m : ℤ) - k := Nat.cast_sub (by omega)
      have h2 : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := Nat.cast_sub (by omega)
      have h3 : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Nat.cast_sub (by omega)
      push_cast; rw [h1, h2, h3]; ring
    have he2 : ∑ k ∈ range m,
        ((((2 * m - (2 * k + 1)) / 2 : ℕ) : ℤ) + (((2 * n - (2 * k + 1)) / 2 : ℕ) : ℤ) + 2) *
        ((((2 * k + 1) / 2 : ℕ) : ℤ) + (((2 * n - 2 * m + (2 * k + 1)) / 2 : ℕ) : ℤ) + 2) =
        ∑ k ∈ range m, ((n : ℤ) + m - 2 * k) * ((n : ℤ) - m + 2 + 2 * k) := by
      apply Finset.sum_congr rfl; intro k hk; rw [mem_range] at hk
      rw [show (2 * m - (2 * k + 1)) / 2 = m - k - 1 by omega,
        show (2 * n - (2 * k + 1)) / 2 = n - k - 1 by omega,
        show (2 * k + 1) / 2 = k by omega,
        show (2 * n - 2 * m + (2 * k + 1)) / 2 = n - m + k by omega]
      have h1 : ((m - k - 1 : ℕ) : ℤ) = (m : ℤ) - k - 1 := by omega
      have h2 : ((n - k - 1 : ℕ) : ℤ) = (n : ℤ) - k - 1 := by omega
      have h3 : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Nat.cast_sub (by omega)
      push_cast; rw [h1, h2, h3]; ring
    rw [he1, he2] at hadd
    have hq := sum_quad_type2 n m
    linear_combination 3 * hadd + hq
  rw [hFm, hF4m, hF2m, hF2p]
  linear_combination hIoo1 + hIoo2

private lemma g_eq (n : ℕ) (hn : 1 ≤ n) :
    3 * g n n = 4 * (n : ℤ) ^ 3 + 18 * (n : ℤ) ^ 2 + 50 * (n : ℤ) - 12 := by
  unfold g
  have hpt : ∀ s ∈ range (4 * n + 1),
      (halfCount (2 * n) n s : ℤ) * (halfCount (2 * n) n (4 * n - s) : ℤ) =
      (halfPiece n n s : ℤ) * (halfPiece n n (4 * n - s) : ℤ) := by
    intro s _
    rw [halfCount_eq_piece n n s le_rfl, halfCount_eq_piece n n (4 * n - s) le_rfl]
  rw [Finset.sum_congr rfl hpt]
  let F : ℕ → ℤ := fun s => (halfPiece n n s : ℤ) * (halfPiece n n (4 * n - s) : ℤ)
  change 3 * ∑ s ∈ range (4 * n + 1), F s = _
  have hzero : ∀ s ∈ range (4 * n + 1), (s < n ∨ 3 * n < s) → F s = 0 := by
    intro s hs htail
    rw [mem_range] at hs
    simp only [F]
    rcases htail with h1 | h2
    · have hp : halfPiece n n (4 * n - s) = 0 := by unfold halfPiece; split_ifs <;> omega
      rw [hp]; simp
    · have hp : halfPiece n n s = 0 := by unfold halfPiece; split_ifs <;> omega
      rw [hp]; simp
  let core : Finset ℕ := insert n (insert (3 * n) (Finset.Ioo n (3 * n)))
  have hsum_core : ∑ s ∈ range (4 * n + 1), F s = ∑ s ∈ core, F s := by
    symm
    apply Finset.sum_subset
    · intro s hs
      simp only [core, mem_insert, Finset.mem_Ioo] at hs
      rw [mem_range]; omega
    · intro s hs hnot
      apply hzero s hs
      simp only [core, mem_insert, Finset.mem_Ioo] at hnot
      rw [mem_range] at hs
      omega
  rw [hsum_core]
  simp only [core]
  rw [Finset.sum_insert (by simp only [mem_insert, Finset.mem_Ioo]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Ioo]; omega)]
  have hFn : F n = 8 * (n : ℤ) := by
    have h1 : halfPiece n n n = 4 * n := by unfold halfPiece; split_ifs <;> omega
    have h2 : halfPiece n n (4 * n - n) = 2 := by unfold halfPiece; split_ifs <;> omega
    simp only [F, h1, h2]; push_cast; ring
  have hF3n : F (3 * n) = 8 * (n : ℤ) := by
    have hsub : 4 * n - 3 * n = n := by omega
    have hsub2 : 4 * n - n = 3 * n := by omega
    simp only [F]
    rw [hsub, mul_comm]
    simpa only [F, hsub2] using hFn
  have hIoo2 : 3 * ∑ s ∈ Finset.Ioo n (3 * n), F s =
      4 * (n : ℤ) ^ 3 + 18 * (n : ℤ) ^ 2 + 14 * (n : ℤ) - 3 * (2 * (n : ℤ) + 2) * 2 := by
    have hadd : (∑ s ∈ Finset.Ioo n (3 * n), F s) + (2 * (n : ℤ) + 2) * 2 =
        ∑ t ∈ range (2 * n),
          ((((2 * n - t) / 2 : ℕ) : ℤ) + (((2 * n - t) / 2 : ℕ) : ℤ) + 2) *
          ((((t / 2 : ℕ) : ℤ) + (((t / 2 : ℕ) : ℤ)) + 2)) := by
      have h0mem : (0 : ℕ) ∈ range (2 * n) := by rw [mem_range]; omega
      rw [← Finset.add_sum_erase _ _ h0mem]
      have h0val : ((((2 * n - 0) / 2 : ℕ) : ℤ) + (((2 * n - 0) / 2 : ℕ) : ℤ) + 2) *
          ((((0 / 2 : ℕ) : ℤ) + (((0 / 2 : ℕ) : ℤ)) + 2)) = (2 * (n : ℤ) + 2) * 2 := by
        rw [show (2 * n - 0) / 2 = n by omega]
        simp only [Nat.zero_div, Nat.cast_zero, zero_add]; ring
      rw [h0val, add_comm]
      congr 1
      apply Finset.sum_bij (fun s _ => s - n)
      · intro s hs; rw [Finset.mem_Ioo] at hs; rw [mem_erase, mem_range]; omega
      · intro s1 hs1 s2 hs2 heq; rw [Finset.mem_Ioo] at hs1 hs2; omega
      · intro t ht; rw [mem_erase, mem_range] at ht
        refine ⟨n + t, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro s hs
        rw [Finset.mem_Ioo] at hs
        have hp1 : halfPiece n n s = (2 * n - (s - n)) / 2 + (2 * n - (s - n)) / 2 + 2 := by
          unfold halfPiece; split_ifs <;> omega
        have hp2 : halfPiece n n (4 * n - s) = (s - n) / 2 + (s - n) / 2 + 2 := by
          unfold halfPiece; split_ifs <;> omega
        simp only [F, hp1, hp2]; push_cast; ring
    rw [sum_even_odd] at hadd
    have he1 : ∑ k ∈ range n,
        ((((2 * n - 2 * k) / 2 : ℕ) : ℤ) + (((2 * n - 2 * k) / 2 : ℕ) : ℤ) + 2) *
        ((((2 * k) / 2 : ℕ) : ℤ) + (((2 * k) / 2 : ℕ) : ℤ) + 2) =
        ∑ k ∈ range n, ((n : ℤ) + n + 2 - 2 * k) * ((n : ℤ) - n + 2 + 2 * k) := by
      apply Finset.sum_congr rfl; intro k hk; rw [mem_range] at hk
      rw [show (2 * n - 2 * k) / 2 = n - k by omega, show (2 * k) / 2 = k by omega]
      have h1 : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := Nat.cast_sub (by omega)
      rw [h1]; ring
    have he2 : ∑ k ∈ range n,
        ((((2 * n - (2 * k + 1)) / 2 : ℕ) : ℤ) + (((2 * n - (2 * k + 1)) / 2 : ℕ) : ℤ) + 2) *
        ((((2 * k + 1) / 2 : ℕ) : ℤ) + (((2 * k + 1) / 2 : ℕ) : ℤ) + 2) =
        ∑ k ∈ range n, ((n : ℤ) + n - 2 * k) * ((n : ℤ) - n + 2 + 2 * k) := by
      apply Finset.sum_congr rfl; intro k hk; rw [mem_range] at hk
      rw [show (2 * n - (2 * k + 1)) / 2 = n - k - 1 by omega, show (2 * k + 1) / 2 = k by omega]
      have h1 : ((n - k - 1 : ℕ) : ℤ) = (n : ℤ) - k - 1 := by omega
      rw [h1]; ring
    rw [he1, he2] at hadd
    have hq := sum_quad_type2 n n
    linear_combination 3 * hadd + hq
  rw [hFn, hF3n]
  linear_combination hIoo2

private lemma a_formula (n : ℕ) (hn : 1 ≤ n) :
    3 * (a n : ℤ) =
      14 * (n : ℤ) ^ 4 + 56 * (n : ℤ) ^ 3 + 121 * (n : ℤ) ^ 2 - 5 * (n : ℤ) + 6 := by
  have ha : (a n : ℤ) = ∑ m ∈ range (2 * n + 1), g n m := by
    rw [a_eq_sum_halfCount]
    unfold g
    push_cast
    rfl
  rw [ha]
  have hpart : range (2 * n + 1) =
      insert 0 (insert (2 * n) (insert n (Finset.Ioo 0 n ∪ Finset.Ioo n (2 * n)))) := by
    ext m
    simp only [mem_range, mem_insert, mem_union, Finset.mem_Ioo]
    omega
  rw [hpart,
    Finset.sum_insert (by simp only [mem_insert, mem_union, Finset.mem_Ioo]; omega),
    Finset.sum_insert (by simp only [mem_insert, mem_union, Finset.mem_Ioo]; omega),
    Finset.sum_insert (by simp only [mem_union, Finset.mem_Ioo]; omega),
    Finset.sum_union (by rw [Finset.disjoint_left]; intro m h1 h2; simp only [Finset.mem_Ioo] at h1 h2; omega)]
  have hg2n : g n (2 * n) = g n 0 := by
    have := g_symm n 0 (by omega)
    simpa only [Nat.sub_zero] using this
  have hsym : ∑ m ∈ Finset.Ioo n (2 * n), g n m = ∑ m ∈ Finset.Ioo 0 n, g n m := by
    apply Finset.sum_bij (fun m _ => 2 * n - m)
    · intro m hm; rw [Finset.mem_Ioo] at hm ⊢; omega
    · intro m1 h1 m2 h2 heq; rw [Finset.mem_Ioo] at h1 h2; omega
    · intro m hm; rw [Finset.mem_Ioo] at hm
      refine ⟨2 * n - m, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro m hm; rw [Finset.mem_Ioo] at hm; exact (g_symm n m (by omega)).symm
  rw [hg2n, hsym]
  have hmid : 3 * ∑ m ∈ Finset.Ioo 0 n, g n m =
      ∑ m ∈ Finset.Ioo 0 n, (12 * (n : ℤ) ^ 3 - 12 * (n : ℤ) ^ 2 * m + 4 * (m : ℤ) ^ 3 +
        24 * (n : ℤ) ^ 2 - 6 * (m : ℤ) ^ 2 + 27 * (n : ℤ) + 17 * (m : ℤ) - 6) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Ioo] at hm
    exact g_mid n m (by omega) hm.2
  have hmid_val : 6 * ∑ m ∈ Finset.Ioo 0 n, g n m =
      14 * (n : ℤ) ^ 4 + 28 * (n : ℤ) ^ 3 + 31 * (n : ℤ) ^ 2 - 85 * (n : ℤ) + 12 := by
    have h0mem : (0 : ℕ) ∈ range n := by rw [mem_range]; omega
    let P : ℕ → ℤ := fun m =>
      12 * (n : ℤ) ^ 3 - 12 * (n : ℤ) ^ 2 * m + 4 * (m : ℤ) ^ 3 +
      24 * (n : ℤ) ^ 2 - 6 * (m : ℤ) ^ 2 + 27 * (n : ℤ) + 17 * (m : ℤ) - 6
    have herase : (range n).erase 0 = Finset.Ioo 0 n := by
      ext m; simp only [mem_erase, mem_range, Finset.mem_Ioo]; omega
    have hsumP : P 0 + ∑ m ∈ Finset.Ioo 0 n, P m = ∑ m ∈ range n, P m := by
      rw [← herase, Finset.add_sum_erase _ _ h0mem]
    have hP0 : P 0 = 12 * (n : ℤ) ^ 3 + 24 * (n : ℤ) ^ 2 + 27 * (n : ℤ) - 6 := by
      simp only [P, Nat.cast_zero]; ring
    have hPrange : ∑ m ∈ range n, P m =
        4 * (∑ m ∈ range n, (m : ℤ) ^ 3) - 6 * (∑ m ∈ range n, (m : ℤ) ^ 2) +
        (17 - 12 * (n : ℤ) ^ 2) * (∑ m ∈ range n, (m : ℤ)) +
        (12 * (n : ℤ) ^ 3 + 24 * (n : ℤ) ^ 2 + 27 * (n : ℤ) - 6) * (n : ℤ) := by
      have hpt : ∀ m ∈ range n, P m =
          4 * (m : ℤ) ^ 3 + (-6) * (m : ℤ) ^ 2 + (17 - 12 * (n : ℤ) ^ 2) * (m : ℤ) +
          (12 * (n : ℤ) ^ 3 + 24 * (n : ℤ) ^ 2 + 27 * (n : ℤ) - 6) := by
        intro m _; simp only [P]; ring
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, card_range, nsmul_eq_mul]
      ring
    have s1 := sum_id_int n
    have s2 := sum_sq_int n
    have s3 := sum_cube_int n
    change 3 * ∑ m ∈ Finset.Ioo 0 n, g n m = ∑ m ∈ Finset.Ioo 0 n, P m at hmid
    linear_combination 2 * hmid + 2 * hsumP - 2 * hP0 + 2 * hPrange + 2 * s3 - 2 * s2 +
      (17 - 12 * (n : ℤ) ^ 2) * s1
  have h0 := g_zero n hn
  have he := g_eq n hn
  linear_combination 6 * h0 + he + hmid_val

private lemma a_recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  have h0 := a_formula n (by omega)
  have h1 := a_formula (n - 1) (by omega)
  have h2 := a_formula (n - 2) (by omega)
  have h3 := a_formula (n - 3) (by omega)
  have h4 := a_formula (n - 4) (by omega)
  have h5 := a_formula (n - 5) (by omega)
  have c1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub (by omega)
  have c2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := Nat.cast_sub (by omega)
  have c3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := Nat.cast_sub (by omega)
  have c4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := Nat.cast_sub (by omega)
  have c5 : ((n - 5 : ℕ) : ℤ) = (n : ℤ) - 5 := Nat.cast_sub (by omega)
  rw [c1] at h1; rw [c2] at h2; rw [c3] at h3; rw [c4] at h4; rw [c5] at h5
  have h3rec : 3 * (a n : ℤ) =
      3 * (5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
    linear_combination h0 - 5 * h1 + 10 * h2 - 10 * h3 + 5 * h4 - h5
  linarith

private lemma a_small_vals :
    a 1 = 64 ∧ a 2 = 384 ∧ a 3 = 1242 ∧ a 4 = 3030 ∧ a 5 = 6252 := by
  have h1 := a_formula 1 (by decide)
  have h2 := a_formula 2 (by decide)
  have h3 := a_formula 3 (by decide)
  have h4 := a_formula 4 (by decide)
  have h5 := a_formula 5 (by decide)
  omega

private lemma coeff_mul_one_sub_X_pow_five (F : PowerSeries ℚ) (k : ℕ) :
    coeff k (F * (1 - X : PowerSeries ℚ) ^ 5) =
      coeff k F
      - (if 1 ≤ k then 5 * coeff (k - 1) F else 0)
      + (if 2 ≤ k then 10 * coeff (k - 2) F else 0)
      - (if 3 ≤ k then 10 * coeff (k - 3) F else 0)
      + (if 4 ≤ k then 5 * coeff (k - 4) F else 0)
      - (if 5 ≤ k then coeff (k - 5) F else 0) := by
  have hexp : (1 - X : PowerSeries ℚ) ^ 5 =
      1 - C 5 * X + C 10 * X ^ 2 - C 10 * X ^ 3 + C 5 * X ^ 4 - X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [hexp, mul_sub, mul_add, mul_sub, mul_add, mul_sub, mul_one,
    map_sub, map_add, map_sub, map_add, map_sub]
  have hmul : ∀ (c : ℚ) (d : ℕ),
      coeff k (F * (C c * X ^ d)) = if d ≤ k then c * coeff (k - d) F else 0 := by
    intro c d
    rw [show F * (C c * X ^ d) = C c * (F * X ^ d) by ring, coeff_C_mul, coeff_mul_X_pow']
    split_ifs <;> ring
  have h1 : coeff k (F * (C 5 * X)) = if 1 ≤ k then 5 * coeff (k - 1) F else 0 := by
    simpa only [pow_one] using hmul 5 1
  have h5 : coeff k (F * X ^ 5) = if 5 ≤ k then coeff (k - 5) F else 0 := by
    rw [coeff_mul_X_pow']
  rw [h1, hmul 10 2, hmul 10 3, hmul 5 4, h5]

private lemma gf_identity :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      2 * X * (32 + 32 * X - 19 * X ^ 2 + 10 * X ^ 3 + X ^ 4) := by
  ext k
  rw [coeff_mul_one_sub_X_pow_five]
  have hrhs : (2 * X * (32 + 32 * X - 19 * X ^ 2 + 10 * X ^ 3 + X ^ 4) : PowerSeries ℚ) =
      C 64 * X + C 64 * X ^ 2 - C 38 * X ^ 3 + C 20 * X ^ 4 + C 2 * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hrhs]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X, coeff_X_pow, coeff_mk]
  obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := a_small_vals
  by_cases hk : k ≤ 5
  · interval_cases k
    · norm_num
    · norm_num [ha1]
    · norm_num [ha1, ha2]
    · norm_num [ha1, ha2, ha3]
    · norm_num [ha1, ha2, ha3, ha4]
    · norm_num [ha1, ha2, ha3, ha4, ha5]
  · have hk5 : 5 < k := by omega
    have hrec := a_recurrence k hk5
    have hrec_q : (a k : ℚ) =
        5 * (a (k - 1) : ℚ) - 10 * (a (k - 2) : ℚ) + 10 * (a (k - 3) : ℚ) -
        5 * (a (k - 4) : ℚ) + (a (k - 5) : ℚ) := by
      exact_mod_cast hrec
    rw [if_neg (by omega : ¬ k = 0),
      if_pos (by omega : 1 ≤ k), if_neg (by omega : ¬ k - 1 = 0),
      if_pos (by omega : 2 ≤ k), if_neg (by omega : ¬ k - 2 = 0),
      if_pos (by omega : 3 ≤ k), if_neg (by omega : ¬ k - 3 = 0),
      if_pos (by omega : 4 ≤ k), if_neg (by omega : ¬ k - 4 = 0),
      if_pos (by omega : 5 ≤ k), if_neg (by omega : ¬ k - 5 = 0),
      if_neg (by omega : ¬ k = 1), if_neg (by omega : ¬ k = 2),
      if_neg (by omega : ¬ k = 3), if_neg (by omega : ¬ k = 4),
      if_neg (by omega : ¬ k = 5)]
    linarith

end OMA.Proof_oeis_a249984

theorem OMA.solution : type_of% @OMA.S_oeis_a249984.main :=
  ⟨OMA.Proof_oeis_a249984.gf_identity, OMA.Proof_oeis_a249984.a_recurrence⟩
