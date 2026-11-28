import OMAStatements.S_oeis_a183409

-- Problem: A183409: Number of n x 2 binary arrays with prefix sums <= i*j/2 and rows/columns lex-nondecreasing.
-- Credit: @ceejcake
-- Proof: Bijection with tuples (s, b, c00) where s = c10 + c11 <= n/2, b = c11 <= s,
-- and c00 in [s, n-s] (if b = s) or [b, n-s-1] (if b < s), followed by exact summation by parity.

namespace ProofA183409

open OMA.S_oeis_a183409
open scoped Classical
noncomputable section

-- Row code: (0,0) -> 0, (0,1) -> 1, (1,0) -> 2, (1,1) -> 3
private def rowCode (r : Fin 2 → Fin 2) : ℕ :=
  2 * (r 0).1 + (r 1).1

private lemma rowCode_le_three (r : Fin 2 → Fin 2) : rowCode r ≤ 3 := by
  unfold rowCode; have := (r 0).2; have := (r 1).2; omega

private lemma rowLex_iff_code {r s : Fin 2 → Fin 2} :
    (r 0 < s 0 ∨ (r 0 = s 0 ∧ r 1 ≤ s 1)) ↔ rowCode r ≤ rowCode s := by
  unfold rowCode
  have h0 := (r 0).2; have h1 := (r 1).2; have h2 := (s 0).2; have h3 := (s 1).2
  constructor
  · rintro (h | ⟨heq, hle⟩)
    · change (r 0).1 < (s 0).1 at h; omega
    · rw [heq]; change (r 1).1 ≤ (s 1).1 at hle; omega
  · intro h
    by_cases hlt : (r 0).1 < (s 0).1
    · exact Or.inl hlt
    · right
      have heq : (r 0).1 = (s 0).1 := by omega
      exact ⟨Fin.ext heq, by change (r 1).1 ≤ (s 1).1; omega⟩

-- Construct array from (c00, c01, c10, c11) with c00 + c01 + c10 + c11 = n
private def mkArr (n c00 c01 c10 : ℕ) : Fin n → Fin 2 → Fin 2 :=
  fun i j =>
    if i.1 < c00 then 0
    else if i.1 < c00 + c01 then (if j = 0 then 0 else 1)
    else if i.1 < c00 + c01 + c10 then (if j = 0 then 1 else 0)
    else 1

-- Valid parameter triples (s, b, c00): s = c10 + c11, b = c11, c00 = #(0,0), c01 = n - s - c00
private def paramSet (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n / 2 + 1)).biUnion (fun s =>
    (Finset.range (s + 1)).biUnion (fun b =>
      (if b = s then Finset.Icc s (n - s) else Finset.Icc b (n - s - 1)).map
        ⟨fun c00 => (s, b, c00), fun _ _ h => by simp only [Prod.mk.injEq] at h; exact h.2.2⟩))

private lemma mem_paramSet {n s b c00 : ℕ} :
    (s, b, c00) ∈ paramSet n ↔
      s ≤ n / 2 ∧ b ≤ s ∧
      (if b = s then s ≤ c00 ∧ c00 ≤ n - s else b ≤ c00 ∧ c00 ≤ n - s - 1) := by
  simp only [paramSet, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨s', hs', b', hb', c', hc', rfl, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    split_ifs at hc' ⊢ <;> exact Finset.mem_Icc.mp hc'
  · rintro ⟨hs, hb, hc⟩
    refine ⟨s, by omega, b, by omega, c00, ?_, rfl⟩
    split_ifs at hc ⊢ <;> exact Finset.mem_Icc.mpr hc

-- Helper: monotone rowCode implies rowCode (A i) ≤ rowCode (A j) for i ≤ j
private lemma mono_rowCode {n : ℕ} {A : Fin n → Fin 2 → Fin 2}
    (hlex : ∀ (i : Fin n) (h : i.1 + 1 < n),
      A i 0 < A ⟨i.1 + 1, h⟩ 0 ∨ (A i 0 = A ⟨i.1 + 1, h⟩ 0 ∧ A i 1 ≤ A ⟨i.1 + 1, h⟩ 1)) :
    ∀ i j : Fin n, i.1 ≤ j.1 → rowCode (A i) ≤ rowCode (A j) := by
  intro i j hij
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  induction k generalizing j with
  | zero =>
    have : i = j := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    have hprev := ih ⟨i.1 + k, by omega⟩ (by dsimp only; omega) rfl
    have hstep := rowLex_iff_code.mp (hlex ⟨i.1 + k, by omega⟩ (by dsimp only; omega))
    have hjeq : (⟨(⟨i.1 + k, by omega⟩ : Fin n).1 + 1, by dsimp only; omega⟩ : Fin n) = j :=
      Fin.ext (by dsimp only; omega)
    rw [hjeq] at hstep
    exact le_trans hprev hstep

-- Bijection: valid arrays ↔ paramSet n
private lemma card_valid_eq_paramSet (n : ℕ) :
    (Finset.univ.filter (isValid n)).card = (paramSet n).card := by
  let cnt (A : Fin n → Fin 2 → Fin 2) (code : ℕ) : ℕ :=
    (Finset.univ.filter (fun i : Fin n => rowCode (A i) = code)).card
  have hsum_cnt : ∀ A : Fin n → Fin 2 → Fin 2,
      cnt A 0 + cnt A 1 + cnt A 2 + cnt A 3 = n := by
    intro A
    have hu : (Finset.univ : Finset (Fin n)) =
        Finset.univ.filter (fun i => rowCode (A i) = 0) ∪
        Finset.univ.filter (fun i => rowCode (A i) = 1) ∪
        Finset.univ.filter (fun i => rowCode (A i) = 2) ∪
        Finset.univ.filter (fun i => rowCode (A i) = 3) := by
      ext i; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
      have := rowCode_le_three (A i); omega
    have hd : ∀ a b : ℕ, a ≠ b →
        Disjoint (Finset.univ.filter (fun i : Fin n => rowCode (A i) = a))
                 (Finset.univ.filter (fun i : Fin n => rowCode (A i) = b)) := by
      intro a b hab; rw [Finset.disjoint_left]; intro i h1 h2
      simp only [Finset.mem_filter] at h1 h2; omega
    have hc : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
    rw [← hc, hu]
    rw [Finset.card_union_of_disjoint (by
          rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
          exact ⟨⟨hd 0 3 (by omega), hd 1 3 (by omega)⟩, hd 2 3 (by omega)⟩)]
    rw [Finset.card_union_of_disjoint (by
          rw [Finset.disjoint_union_left]
          exact ⟨hd 0 2 (by omega), hd 1 2 (by omega)⟩)]
    rw [Finset.card_union_of_disjoint (hd 0 1 (by omega))]
  -- For any lex-nondecreasing A, A = mkArr n (cnt A 0) (cnt A 1) (cnt A 2)
  have hA_eq_mk : ∀ A : Fin n → Fin 2 → Fin 2,
      (∀ (i : Fin n) (h : i.1 + 1 < n),
        A i 0 < A ⟨i.1 + 1, h⟩ 0 ∨ (A i 0 = A ⟨i.1 + 1, h⟩ 0 ∧ A i 1 ≤ A ⟨i.1 + 1, h⟩ 1)) →
      A = mkArr n (cnt A 0) (cnt A 1) (cnt A 2) := by
    intro A hlex
    have hmono := mono_rowCode hlex
    -- A prefix of indices has rowCode < t
    have hpref : ∀ (t : ℕ) (i : Fin n),
        rowCode (A i) < t ↔ i.1 < (Finset.univ.filter (fun r : Fin n => rowCode (A r) < t)).card := by
      intro t i
      let F := Finset.univ.filter (fun r : Fin n => rowCode (A r) < t)
      have hF_down : ∀ a b : Fin n, a.1 ≤ b.1 → b ∈ F → a ∈ F := by
        intro a b hab hb
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact lt_of_le_of_lt (hmono a b hab) hb
      constructor
      · intro hi
        have hsub : Finset.univ.filter (fun r : Fin n => r.1 ≤ i.1) ⊆ F := by
          intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          exact hF_down r i hr (by simp [F, hi])
        have hcard_le : (Finset.univ.filter (fun r : Fin n => r.1 ≤ i.1)).card = i.1 + 1 := by
          have : (Finset.univ.filter (fun r : Fin n => r.1 ≤ i.1)).card = (Finset.range (i.1 + 1)).card := by
            refine Finset.card_bij (fun r _ => r.1) ?_ ?_ ?_
            · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
              exact Finset.mem_range.mpr (by omega)
            · intro r1 _ r2 _ h; exact Fin.ext h
            · intro m hm; rw [Finset.mem_range] at hm
              exact ⟨⟨m, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩
          rw [this, Finset.card_range]
        have hle := Finset.card_le_card hsub
        change i.1 < F.card; omega
      · intro hi
        change i.1 < F.card at hi
        by_contra hnot
        have hsub : F ⊆ Finset.univ.filter (fun r : Fin n => r.1 < i.1) := by
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_contra hge
          have : i ∈ F := hF_down i r (by omega) hr
          simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact hnot this
        have hcard_lt : (Finset.univ.filter (fun r : Fin n => r.1 < i.1)).card = i.1 := by
          have : (Finset.univ.filter (fun r : Fin n => r.1 < i.1)).card = (Finset.range i.1).card := by
            refine Finset.card_bij (fun r _ => r.1) ?_ ?_ ?_
            · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
              exact Finset.mem_range.mpr hr
            · intro r1 _ r2 _ h; exact Fin.ext h
            · intro m hm; rw [Finset.mem_range] at hm
              exact ⟨⟨m, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩
          rw [this, Finset.card_range]
        have hle := Finset.card_le_card hsub
        omega
    have hc1 : (Finset.univ.filter (fun r : Fin n => rowCode (A r) < 1)).card = cnt A 0 := by
      congr 1; ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hc2 : (Finset.univ.filter (fun r : Fin n => rowCode (A r) < 2)).card = cnt A 0 + cnt A 1 := by
      have hu : Finset.univ.filter (fun r : Fin n => rowCode (A r) < 2) =
          Finset.univ.filter (fun r : Fin n => rowCode (A r) = 0) ∪
          Finset.univ.filter (fun r : Fin n => rowCode (A r) = 1) := by
        ext r; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]; omega
      rw [hu, Finset.card_union_of_disjoint]
      rw [Finset.disjoint_left]; intro r h1 h2; simp only [Finset.mem_filter] at h1 h2; omega
    have hc3 : (Finset.univ.filter (fun r : Fin n => rowCode (A r) < 3)).card = cnt A 0 + cnt A 1 + cnt A 2 := by
      have hu : Finset.univ.filter (fun r : Fin n => rowCode (A r) < 3) =
          Finset.univ.filter (fun r : Fin n => rowCode (A r) < 2) ∪
          Finset.univ.filter (fun r : Fin n => rowCode (A r) = 2) := by
        ext r; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]; omega
      rw [hu, Finset.card_union_of_disjoint, hc2]
      rw [Finset.disjoint_left]; intro r h1 h2; simp only [Finset.mem_filter] at h1 h2; omega
    funext i j
    unfold mkArr
    have hp1 := hpref 1 i; rw [hc1] at hp1
    have hp2 := hpref 2 i; rw [hc2] at hp2
    have hp3 := hpref 3 i; rw [hc3] at hp3
    have hrc := rowCode_le_three (A i)
    unfold rowCode at hp1 hp2 hp3 hrc
    have ha0 := (A i 0).2; have ha1 := (A i 1).2
    by_cases h1 : i.1 < cnt A 0
    · rw [if_pos h1]
      have h0 : 2 * (A i 0).1 + (A i 1).1 < 1 := hp1.mpr h1
      match j with | 0 => exact Fin.ext (by omega) | 1 => exact Fin.ext (by omega)
    · rw [if_neg h1]
      by_cases h2 : i.1 < cnt A 0 + cnt A 1
      · rw [if_pos h2]
        have h01 : 2 * (A i 0).1 + (A i 1).1 = 1 := by
          have := hp2.mpr h2; have : ¬ (2 * (A i 0).1 + (A i 1).1 < 1) := fun h => h1 (hp1.mp h); omega
        match j with
        | 0 => simp; exact Fin.ext (by omega)
        | 1 => simp; exact Fin.ext (by omega)
      · rw [if_neg h2]
        by_cases h3 : i.1 < cnt A 0 + cnt A 1 + cnt A 2
        · rw [if_pos h3]
          have h10 : 2 * (A i 0).1 + (A i 1).1 = 2 := by
            have := hp3.mpr h3; have : ¬ (2 * (A i 0).1 + (A i 1).1 < 2) := fun h => h2 (hp2.mp h); omega
          match j with
          | 0 => simp; exact Fin.ext (by omega)
          | 1 => simp; exact Fin.ext (by omega)
        · rw [if_neg h3]
          have h11 : 2 * (A i 0).1 + (A i 1).1 = 3 := by
            have : ¬ (2 * (A i 0).1 + (A i 1).1 < 3) := fun h => h3 (hp3.mp h); omega
          match j with | 0 => exact Fin.ext (by omega) | 1 => exact Fin.ext (by omega)
  -- Helper: sums for mkArr
  have hmk_sum0 : ∀ c00 c01 c10 : ℕ, c00 + c01 + c10 ≤ n → ∀ i : ℕ, i ≤ n →
      (∑ r ∈ Finset.univ.filter (fun r : Fin n => r.1 < i), (mkArr n c00 c01 c10 r 0).1) =
        i - (c00 + c01) := by
    intro c00 c01 c10 hle i hi
    have hval : ∀ r : Fin n, (mkArr n c00 c01 c10 r 0).1 = if r.1 < c00 + c01 then 0 else 1 := by
      intro r; unfold mkArr; split_ifs <;> simp <;> omega
    simp_rw [hval]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
    have hcard : (Finset.filter (fun r : Fin n => ¬ r.1 < c00 + c01)
        (Finset.univ.filter (fun r : Fin n => r.1 < i))).card = i - (c00 + c01) := by
      have : (Finset.filter (fun r : Fin n => ¬ r.1 < c00 + c01)
          (Finset.univ.filter (fun r : Fin n => r.1 < i))).card = (Finset.Ico (c00 + c01) i).card := by
        refine Finset.card_bij (fun r _ => r.1) ?_ ?_ ?_
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          exact Finset.mem_Ico.mpr ⟨by omega, hr.1⟩
        · intro r1 _ r2 _ h; exact Fin.ext h
        · intro m hm; rw [Finset.mem_Ico] at hm
          exact ⟨⟨m, by omega⟩, by simp; omega, rfl⟩
      rw [this, Nat.card_Ico]
    exact hcard
  have hmk_sum01 : ∀ c00 c01 c10 : ℕ, c00 + c01 + c10 ≤ n → ∀ i : ℕ, i ≤ n →
      (∑ r ∈ Finset.univ.filter (fun r : Fin n => r.1 < i),
        ((mkArr n c00 c01 c10 r 0).1 + (mkArr n c00 c01 c10 r 1).1)) =
        (i - c00) + (i - (c00 + c01 + c10)) := by
    intro c00 c01 c10 hle i hi
    have hval : ∀ r : Fin n,
        (mkArr n c00 c01 c10 r 0).1 + (mkArr n c00 c01 c10 r 1).1 =
          (if r.1 < c00 then 0 else 1) + (if r.1 < c00 + c01 + c10 then 0 else 1) := by
      intro r; unfold mkArr; split_ifs <;> simp <;> omega
    simp_rw [hval]
    rw [Finset.sum_add_distrib]
    have hcnt : ∀ t : ℕ,
        (∑ r ∈ Finset.univ.filter (fun r : Fin n => r.1 < i), if r.1 < t then 0 else 1) = i - t := by
      intro t
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
      have : (Finset.filter (fun r : Fin n => ¬ r.1 < t)
          (Finset.univ.filter (fun r : Fin n => r.1 < i))).card = (Finset.Ico t i).card := by
        refine Finset.card_bij (fun r _ => r.1) ?_ ?_ ?_
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          exact Finset.mem_Ico.mpr ⟨by omega, hr.1⟩
        · intro r1 _ r2 _ h; exact Fin.ext h
        · intro m hm; rw [Finset.mem_Ico] at hm
          exact ⟨⟨m, by omega⟩, by simp; omega, rfl⟩
      rw [this, Nat.card_Ico]
    rw [hcnt c00, hcnt (c00 + c01 + c10)]
  -- Main bijection
  refine Finset.card_bij (fun A _ => (cnt A 2 + cnt A 3, cnt A 3, cnt A 0)) ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    rcases hA with ⟨hlex, hcol, hsum1, hsum2⟩
    have htot := hsum_cnt A
    have hAeq := hA_eq_mk A hlex
    have hs1 := hsum1 n le_rfl
    rw [hAeq, hmk_sum0 _ _ _ (by omega) n le_rfl] at hs1
    have hs2 := hsum2 n le_rfl
    rw [hAeq, hmk_sum01 _ _ _ (by omega) n le_rfl] at hs2
    have hc01_or_c10 : 0 < cnt A 1 ∨ cnt A 2 = 0 := by
      by_contra hbad
      have hb1 : cnt A 1 = 0 := by omega
      have hb2 : 0 < cnt A 2 := by omega
      have hidx : cnt A 0 < n := by omega
      let i0 : Fin n := ⟨cnt A 0, hidx⟩
      have hA0 : A i0 0 = 1 := by
        rw [hAeq]; unfold mkArr; dsimp only [i0]
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; rfl
      have hA1 : A i0 1 = 0 := by
        rw [hAeq]; unfold mkArr; dsimp only [i0]
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; rfl
      rcases hcol with hall | ⟨i, hlt, hilt⟩
      · have := hall i0; rw [hA0, hA1] at this; exact absurd this (by decide)
      · by_cases hi : i.1 < cnt A 0
        · rw [hAeq] at hilt; unfold mkArr at hilt; simp [hi] at hilt
        · by_cases hieq : i.1 = cnt A 0
          · have : i = i0 := Fin.ext hieq; rw [this, hA0, hA1] at hilt; exact absurd hilt (by decide)
          · have := hlt i0 (by dsimp only [i0]; omega); rw [hA0, hA1] at this; exact absurd this (by decide)
    rw [mem_paramSet]
    refine ⟨by omega, by omega, ?_⟩
    split_ifs with h
    · omega
    · omega
  · intro A1 hA1 A2 hA2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA1 hA2
    simp only [Prod.mk.injEq] at h
    have ht1 := hsum_cnt A1; have ht2 := hsum_cnt A2
    have h1 := hA_eq_mk A1 hA1.1; have h2 := hA_eq_mk A2 hA2.1
    rw [h1, h2]
    have e0 : cnt A1 0 = cnt A2 0 := h.2.2
    have e3 : cnt A1 3 = cnt A2 3 := h.2.1
    have e2 : cnt A1 2 = cnt A2 2 := by omega
    have e1 : cnt A1 1 = cnt A2 1 := by omega
    rw [e0, e1, e2]
  · intro ⟨s, b, c00⟩ hp
    rw [mem_paramSet] at hp
    rcases hp with ⟨hs, hb, hc⟩
    have hc_le : c00 + s ≤ n := by split_ifs at hc <;> omega
    have hb_le_c00 : b ≤ c00 := by split_ifs at hc <;> omega
    have hc01_or : 0 < n - s - c00 ∨ s - b = 0 := by split_ifs at hc <;> omega
    let c01 := n - s - c00
    let c10 := s - b
    let A := mkArr n c00 c01 c10
    have hA_valid : isValid n A := by
      refine ⟨fun i hi => ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
      · rw [rowLex_iff_code]
        unfold rowCode A mkArr
        dsimp only
        split_ifs <;> simp <;> omega
      · by_cases h01 : 0 < c01
        · right
          refine ⟨⟨c00, by omega⟩, fun k hk => ?_, ?_⟩
          · unfold A mkArr; dsimp only at hk; simp [hk]
          · unfold A mkArr; dsimp only
            simp only [lt_irrefl, show c00 < c00 + c01 by omega, ↓reduceIte]; decide
        · left
          have h10 : c10 = 0 := by omega
          intro i
          unfold A mkArr
          by_cases h1 : i.1 < c00
          · simp [h1]
          · simp only [h1, show ¬ i.1 < c00 + c01 by omega, show ¬ i.1 < c00 + c01 + c10 by omega, ↓reduceIte]
      · rw [hmk_sum0 c00 c01 c10 (by omega) i hi]; omega
      · rw [hmk_sum01 c00 c01 c10 (by omega) i hi]; omega
    -- Check cnt A values
    have hcntA : ∀ code : ℕ,
        cnt A 0 = c00 ∧ cnt A 1 = c01 ∧ cnt A 2 = c10 ∧ cnt A 3 = b := by
      intro _
      have hcard_Ico : ∀ l r : ℕ, l ≤ r → r ≤ n →
          (Finset.univ.filter (fun i : Fin n => l ≤ i.1 ∧ i.1 < r)).card = r - l := by
        intro l r hlr hrn
        have : (Finset.univ.filter (fun i : Fin n => l ≤ i.1 ∧ i.1 < r)).card = (Finset.Ico l r).card := by
          refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact Finset.mem_Ico.mpr hi
          · intro i1 _ i2 _ h; exact Fin.ext h
          · intro m hm; rw [Finset.mem_Ico] at hm
            exact ⟨⟨m, by omega⟩, by simp; omega, rfl⟩
        rw [this, Nat.card_Ico]
      have hrcA : ∀ i : Fin n, rowCode (A i) =
          if i.1 < c00 then 0 else if i.1 < c00 + c01 then 1 else if i.1 < c00 + c01 + c10 then 2 else 3 := by
        intro i; unfold rowCode A mkArr
        by_cases h1 : i.1 < c00
        · simp [h1]
        · by_cases h2 : i.1 < c00 + c01
          · simp [h1, h2]
          · by_cases h3 : i.1 < c00 + c01 + c10
            · simp [h1, h2, h3]
            · simp [h1, h2, h3]
      have h0 : cnt A 0 = c00 := by
        have : Finset.univ.filter (fun i : Fin n => rowCode (A i) = 0) =
            Finset.univ.filter (fun i : Fin n => 0 ≤ i.1 ∧ i.1 < c00) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrcA]
          split_ifs <;> simp <;> omega
        unfold cnt; rw [this, hcard_Ico 0 c00 (by omega) (by omega)]; omega
      have h1 : cnt A 1 = c01 := by
        have : Finset.univ.filter (fun i : Fin n => rowCode (A i) = 1) =
            Finset.univ.filter (fun i : Fin n => c00 ≤ i.1 ∧ i.1 < c00 + c01) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrcA]
          split_ifs <;> simp <;> omega
        unfold cnt; rw [this, hcard_Ico c00 (c00 + c01) (by omega) (by omega)]; omega
      have h2 : cnt A 2 = c10 := by
        have : Finset.univ.filter (fun i : Fin n => rowCode (A i) = 2) =
            Finset.univ.filter (fun i : Fin n => c00 + c01 ≤ i.1 ∧ i.1 < c00 + c01 + c10) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrcA]
          split_ifs <;> simp <;> omega
        unfold cnt; rw [this, hcard_Ico (c00 + c01) (c00 + c01 + c10) (by omega) (by omega)]; omega
      have h3 : cnt A 3 = b := by have := hsum_cnt A; omega
      exact ⟨h0, h1, h2, h3⟩
    rcases hcntA 0 with ⟨h0, h1, h2, h3⟩
    refine ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ A, hA_valid⟩, ?_⟩
    simp only [Prod.mk.injEq]
    omega

-- Exact cardinality of paramSet n as a double sum
private def rowSum (n s : ℕ) : ℕ :=
  (n - 2 * s + 1) + ∑ b ∈ Finset.range s, (n - s - b)

private lemma card_paramSet_eq_sum (n : ℕ) :
    (paramSet n).card = ∑ s ∈ Finset.range (n / 2 + 1), rowSum n s := by
  unfold paramSet
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [Finset.mem_range] at hs
    rw [Finset.card_biUnion]
    · rw [Finset.sum_range_succ]
      have hlast : ((if s = s then Finset.Icc s (n - s) else Finset.Icc s (n - s - 1)).map
          ⟨fun c00 => (s, s, c00), fun _ _ h => by simp only [Prod.mk.injEq] at h; exact h.2.2⟩).card =
          n - 2 * s + 1 := by
        rw [if_pos rfl, Finset.card_map, Nat.card_Icc]; omega
      have hinit : ∑ b ∈ Finset.range s,
          ((if b = s then Finset.Icc s (n - s) else Finset.Icc b (n - s - 1)).map
            ⟨fun c00 => (s, b, c00), fun _ _ h => by simp only [Prod.mk.injEq] at h; exact h.2.2⟩).card =
          ∑ b ∈ Finset.range s, (n - s - b) := by
        refine Finset.sum_congr rfl (fun b hb => ?_)
        rw [Finset.mem_range] at hb
        rw [if_neg (by omega), Finset.card_map, Nat.card_Icc]; omega
      rw [hlast, hinit]; unfold rowSum; omega
    · intro b1 _ b2 _ hne
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_map] at h1 h2
      rcases h1 with ⟨_, _, rfl⟩; rcases h2 with ⟨_, _, h2⟩
      exact hne (congr_arg (fun q => q.2.1) h2).symm
  · intro s1 _ s2 _ hne
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_biUnion, Finset.mem_map] at h1 h2
    rcases h1 with ⟨_, _, _, _, rfl⟩; rcases h2 with ⟨_, _, _, _, h2⟩
    exact hne (congr_arg Prod.fst h2).symm

private lemma two_mul_rowSum (n s : ℕ) (hs : 2 * s ≤ n) :
    2 * rowSum n s + 3 * s ^ 2 + 3 * s = 2 * n * (s + 1) + 2 := by
  unfold rowSum
  have hsum : 2 * (∑ b ∈ Finset.range s, (n - s - b)) + 3 * s ^ 2 = 2 * n * s + s := by
    induction s with
    | zero => simp
    | succ s ih =>
      have hstep : (∑ b ∈ Finset.range (s + 1), (n - (s + 1) - b)) + s =
          (∑ b ∈ Finset.range s, (n - s - b)) + (n - 2 * s - 1) := by
        rw [Finset.sum_range_succ]
        have hsub : ∀ b ∈ Finset.range s, (n - s - b) = (n - (s + 1) - b) + 1 := by
          intro b hb; rw [Finset.mem_range] at hb; omega
        have hs1 := Finset.sum_congr rfl hsub
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hs1
        have hlast : n - (s + 1) - s = n - 2 * s - 1 := by omega
        rw [hs1, hlast]; omega
      have hih := ih (by omega)
      have hsub1 : (n - 2 * s - 1) + 2 * s + 1 = n := by omega
      nlinarith
  have hsub2 : (n - 2 * s) + 2 * s = n := by omega
  nlinarith

private lemma two_mul_sum_succ (m : ℕ) :
    2 * (∑ s ∈ Finset.range (m + 1), (s + 1)) = (m + 1) * (m + 2) := by
  induction m with
  | zero => simp
  | succ k ihk => rw [Finset.sum_range_succ]; nlinarith

private lemma sum_rowSum_even (m : ℕ) :
    2 * (∑ s ∈ Finset.range (m + 1), rowSum (2 * m) s) = m ^ 3 + 3 * m ^ 2 + 4 * m + 2 := by
  induction m with
  | zero => simp [rowSum]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hshift : ∀ s ∈ Finset.range (m + 1),
        rowSum (2 * (m + 1)) s = rowSum (2 * m) s + 2 * (s + 1) := by
      intro s hs; rw [Finset.mem_range] at hs
      have h1 := two_mul_rowSum (2 * (m + 1)) s (by omega)
      have h2 := two_mul_rowSum (2 * m) s (by omega)
      nlinarith
    rw [Finset.sum_congr rfl hshift, Finset.sum_add_distrib]
    have htri := two_mul_sum_succ m
    have hlast := two_mul_rowSum (2 * (m + 1)) (m + 1) (by omega)
    have hmul : ∑ s ∈ Finset.range (m + 1), 2 * (s + 1) = 2 * ∑ s ∈ Finset.range (m + 1), (s + 1) := by
      rw [Finset.mul_sum]
    rw [hmul]
    nlinarith

private lemma sum_rowSum_odd (m : ℕ) :
    2 * (∑ s ∈ Finset.range (m + 1), rowSum (2 * m + 1) s) = m ^ 3 + 4 * m ^ 2 + 7 * m + 4 := by
  induction m with
  | zero => simp [rowSum]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hshift : ∀ s ∈ Finset.range (m + 1),
        rowSum (2 * (m + 1) + 1) s = rowSum (2 * m + 1) s + 2 * (s + 1) := by
      intro s hs; rw [Finset.mem_range] at hs
      have h1 := two_mul_rowSum (2 * (m + 1) + 1) s (by omega)
      have h2 := two_mul_rowSum (2 * m + 1) s (by omega)
      nlinarith
    rw [Finset.sum_congr rfl hshift, Finset.sum_add_distrib]
    have htri := two_mul_sum_succ m
    have hlast := two_mul_rowSum (2 * (m + 1) + 1) (m + 1) (by omega)
    have hmul : ∑ s ∈ Finset.range (m + 1), 2 * (s + 1) = 2 * ∑ s ∈ Finset.range (m + 1), (s + 1) := by
      rw [Finset.mul_sum]
    rw [hmul]
    nlinarith

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      32 * (a n : ℤ) =
        2 * (n : ℤ) ^ 3 + 11 * (n : ℤ) ^ 2 + 31 * (n : ℤ) + 27 +
          ((n : ℤ) ^ 2 + (n : ℤ) + 5) * (-1 : ℤ) ^ n := by
  intro n _
  have ha : a n = (paramSet n).card := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_valid_eq_paramSet]
  rw [ha, card_paramSet_eq_sum]
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h2m : m + m = 2 * m := by omega
    rw [h2m]
    have hdiv : (2 * m) / 2 = m := by omega
    rw [hdiv]
    have hsum := sum_rowSum_even m
    have hpow : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
    rw [hpow]
    have hsumZ : (2 : ℤ) * (∑ s ∈ Finset.range (m + 1), rowSum (2 * m) s : ℕ) =
        (m : ℤ) ^ 3 + 3 * (m : ℤ) ^ 2 + 4 * (m : ℤ) + 2 := by exact_mod_cast hsum
    push_cast
    linarith
  · have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
    have hsum := sum_rowSum_odd m
    have hpow : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hpow]
    have hsumZ : (2 : ℤ) * (∑ s ∈ Finset.range (m + 1), rowSum (2 * m + 1) s : ℕ) =
        (m : ℤ) ^ 3 + 4 * (m : ℤ) ^ 2 + 7 * (m : ℤ) + 4 := by exact_mod_cast hsum
    push_cast
    linarith

end
end ProofA183409

theorem OMA.solution : type_of% @OMA.S_oeis_a183409.main :=
  ProofA183409.main
