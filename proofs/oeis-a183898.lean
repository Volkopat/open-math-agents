import OMAStatements.S_oeis_a183898

namespace OMA.S_oeis_a183898_Proof

open OMA.S_oeis_a183898 PowerSeries

private def counts {N : ℕ} (w : Fin N → Fin 4) (r : Fin 4) : ℕ :=
  (Finset.univ.filter fun i : Fin N => w i = r).card

private lemma sum_counts {N : ℕ} (w : Fin N → Fin 4) :
    ∑ r : Fin 4, counts w r = N := by
  unfold counts
  have h := Finset.card_eq_sum_card_fiberwise (f := w) (s := Finset.univ)
    (t := (Finset.univ : Finset (Fin 4))) (fun _ _ => Finset.mem_univ _)
  simpa using h.symm

private def fromCounts {N : ℕ} (c : Fin 4 → ℕ) (i : Fin N) : Fin 4 :=
  if i.1 < c 0 then 0
  else if i.1 < c 0 + c 1 then 1
  else if i.1 < c 0 + c 1 + c 2 then 2
  else 3

private lemma fromCounts_mono {N : ℕ} (c : Fin 4 → ℕ) : Monotone (@fromCounts N c) := by
  intro i j hij
  have hij' : i.1 ≤ j.1 := hij
  unfold fromCounts
  split_ifs <;> simp <;> omega

private lemma card_fin_interval (N a b : ℕ) (_hab : a ≤ b) (hb : b ≤ N) :
    (Finset.univ.filter fun i : Fin N => a ≤ i.1 ∧ i.1 < b).card = b - a := by
  have hbij :
      (Finset.univ.filter fun i : Fin N => a ≤ i.1 ∧ i.1 < b).card =
      (Finset.Ico a b).card := by
    refine Finset.card_bij (fun i _ => i.1)
      (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico] at hi ⊢
        exact hi)
      (fun i _ j _ h => Fin.ext h)
      (fun k hk => by
        simp only [Finset.mem_Ico] at hk
        exact ⟨⟨k, by omega⟩, by simp [hk], rfl⟩)
  rw [hbij, Nat.card_Ico]

private lemma counts_fromCounts {N : ℕ} (c : Fin 4 → ℕ) (hc : ∑ r : Fin 4, c r = N) :
    counts (@fromCounts N c) = c := by
  rw [Fin.sum_univ_four] at hc
  funext r
  fin_cases r
  · change (Finset.univ.filter fun i : Fin N => @fromCounts N c i = 0).card = c 0
    have hset : (Finset.univ.filter fun i : Fin N => @fromCounts N c i = 0) =
        Finset.univ.filter fun i : Fin N => 0 ≤ i.1 ∧ i.1 < c 0 := by
      ext i; unfold fromCounts; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp <;> omega
    rw [hset, card_fin_interval N 0 (c 0) (by omega) (by omega)]
    omega
  · change (Finset.univ.filter fun i : Fin N => @fromCounts N c i = 1).card = c 1
    have hset : (Finset.univ.filter fun i : Fin N => @fromCounts N c i = 1) =
        Finset.univ.filter fun i : Fin N => c 0 ≤ i.1 ∧ i.1 < c 0 + c 1 := by
      ext i; unfold fromCounts; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp <;> omega
    rw [hset, card_fin_interval N (c 0) (c 0 + c 1) (by omega) (by omega)]
    omega
  · change (Finset.univ.filter fun i : Fin N => @fromCounts N c i = 2).card = c 2
    have hset : (Finset.univ.filter fun i : Fin N => @fromCounts N c i = 2) =
        Finset.univ.filter fun i : Fin N => c 0 + c 1 ≤ i.1 ∧ i.1 < c 0 + c 1 + c 2 := by
      ext i; unfold fromCounts; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp <;> omega
    rw [hset, card_fin_interval N (c 0 + c 1) (c 0 + c 1 + c 2) (by omega) (by omega)]
    omega
  · change (Finset.univ.filter fun i : Fin N => @fromCounts N c i = 3).card = c 3
    have hset : (Finset.univ.filter fun i : Fin N => @fromCounts N c i = 3) =
        Finset.univ.filter fun i : Fin N => c 0 + c 1 + c 2 ≤ i.1 ∧ i.1 < N := by
      ext i; unfold fromCounts; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hi := i.2
      split_ifs <;> simp <;> omega
    rw [hset, card_fin_interval N (c 0 + c 1 + c 2) N (by omega) (by omega)]
    omega

private lemma mono_lt_iff_card {N : ℕ} {w : Fin N → Fin 4} (hw : Monotone w)
    (k : ℕ) (i : Fin N) :
    (w i).1 < k ↔ i.1 < (Finset.univ.filter fun j : Fin N => (w j).1 < k).card := by
  constructor
  · intro hwi
    have hsub : (Finset.univ.filter fun j : Fin N => j.1 ≤ i.1) ⊆
        Finset.univ.filter fun j : Fin N => (w j).1 < k := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have hle : w j ≤ w i := hw hj
      exact lt_of_le_of_lt hle hwi
    have hcard := Finset.card_le_card hsub
    have hle_card : (Finset.univ.filter fun j : Fin N => j.1 ≤ i.1).card = i.1 + 1 := by
      have h1 : (Finset.univ.filter fun j : Fin N => j.1 ≤ i.1) =
          Finset.univ.filter fun j : Fin N => 0 ≤ j.1 ∧ j.1 < i.1 + 1 := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [h1, card_fin_interval N 0 (i.1 + 1) (by omega) (by omega)]
      omega
    omega
  · intro hi
    by_contra hge
    have hsub : (Finset.univ.filter fun j : Fin N => (w j).1 < k) ⊆
        Finset.univ.filter fun j : Fin N => 0 ≤ j.1 ∧ j.1 < i.1 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      refine ⟨Nat.zero_le _, ?_⟩
      by_contra hji
      have hle : i ≤ j := Nat.le_of_not_lt hji
      have hwle : (w i).1 ≤ (w j).1 := hw hle
      omega
    have hcard := Finset.card_le_card hsub
    rw [card_fin_interval N 0 i.1 (by omega) (by omega)] at hcard
    omega

private lemma fromCounts_counts {N : ℕ} {w : Fin N → Fin 4} (hw : Monotone w) :
    fromCounts (counts w) = w := by
  have h1 : (Finset.univ.filter fun j : Fin N => (w j).1 < 1).card = counts w 0 := by
    unfold counts; congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := (w j).2; constructor <;> intro h
    · exact Fin.ext (by omega)
    · rw [h]; decide
  have h2 : (Finset.univ.filter fun j : Fin N => (w j).1 < 2).card = counts w 0 + counts w 1 := by
    unfold counts
    have hdisj : Disjoint (Finset.univ.filter fun j : Fin N => w j = 0)
        (Finset.univ.filter fun j : Fin N => w j = 1) := by
      rw [Finset.disjoint_filter]; intro j _ h0 h1; rw [h0] at h1; exact absurd h1 (by decide)
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    have hj := (w j).2
    constructor
    · intro hlt
      by_cases h0 : (w j).1 = 0
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext (by omega))
    · rintro (h | h) <;> rw [h] <;> decide
  have h3 : (Finset.univ.filter fun j : Fin N => (w j).1 < 3).card =
      counts w 0 + counts w 1 + counts w 2 := by
    unfold counts
    have hdisj01 : Disjoint (Finset.univ.filter fun j : Fin N => w j = 0)
        (Finset.univ.filter fun j : Fin N => w j = 1) := by
      rw [Finset.disjoint_filter]; intro j _ h0 h1; rw [h0] at h1; exact absurd h1 (by decide)
    have hdisj012 : Disjoint ((Finset.univ.filter fun j : Fin N => w j = 0) ∪
        (Finset.univ.filter fun j : Fin N => w j = 1))
        (Finset.univ.filter fun j : Fin N => w j = 2) := by
      rw [Finset.disjoint_left]; intro j hj h2
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hj h2
      rcases hj with h0 | h1
      · rw [h0] at h2; exact absurd h2 (by decide)
      · rw [h1] at h2; exact absurd h2 (by decide)
    rw [← Finset.card_union_of_disjoint hdisj01, ← Finset.card_union_of_disjoint hdisj012]
    congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    have hj := (w j).2
    constructor
    · intro hlt
      by_cases h0 : (w j).1 = 0
      · exact Or.inl (Or.inl (Fin.ext h0))
      · by_cases h1' : (w j).1 = 1
        · exact Or.inl (Or.inr (Fin.ext h1'))
        · exact Or.inr (Fin.ext (by omega))
    · rintro ((h | h) | h) <;> rw [h] <;> decide
  funext i
  unfold fromCounts
  rw [← h3, ← h2, ← h1]
  simp only [← mono_lt_iff_card hw 1 i, ← mono_lt_iff_card hw 2 i, ← mono_lt_iff_card hw 3 i]
  have hwi := (w i).2
  apply Fin.ext
  split_ifs <;> simp <;> omega

private def mult4 (r a b d x : Fin 4) : ℕ :=
  (if x = r then 1 else 0) + (if x = a then 1 else 0) +
  (if x = b then 1 else 0) + (if x = d then 1 else 0)

private def validCounts (c : Fin 4 → ℕ) : Prop :=
  ∀ r : Fin 4, 0 < c r →
    ∃ a b d : Fin 4, (a.1 + b.1 + d.1) % 4 = r.1 ∧ ∀ x : Fin 4, mult4 r a b d x ≤ c x

private lemma card_filter_insert_eq {α : Type*} [DecidableEq α] (s : Finset α) (a : α)
    (P : α → Prop) [DecidablePred P] (ha : a ∉ s) :
    ((insert a s).filter P).card = (if P a then 1 else 0) + (s.filter P).card := by
  rw [Finset.filter_insert]
  have hna : a ∉ s.filter P := fun hm => ha (Finset.mem_filter.1 hm).1
  by_cases hP : P a
  · simp [hP, Finset.card_insert_of_notMem hna, add_comm]
  · simp [hP]

private lemma card_filter_singleton_eq {α : Type*} [DecidableEq α] (a : α)
    (P : α → Prop) [DecidablePred P] :
    (({a} : Finset α).filter P).card = if P a then 1 else 0 := by
  by_cases hP : P a <;> simp [Finset.filter_singleton, hP]

private lemma valid_iff_validCounts {N : ℕ} (w : Fin N → Fin 4) :
    Valid w ↔ validCounts (counts w) := by
  constructor
  · intro hvalid r hcr
    have hne : (Finset.univ.filter fun i : Fin N => w i = r).Nonempty :=
      Finset.card_pos.1 hcr
    obtain ⟨i, hi⟩ := hne
    have hwi : w i = r := (Finset.mem_filter.1 hi).2
    obtain ⟨t, ht3, hit, hsum⟩ := hvalid i
    rw [Finset.card_eq_three] at ht3
    obtain ⟨j1, j2, j3, h12, h13, h23, rfl⟩ := ht3
    have hi1 : i ≠ j1 := fun h => hit (by simp [h])
    have hi2 : i ≠ j2 := fun h => hit (by simp [h])
    have hi3 : i ≠ j3 := fun h => hit (by simp [h])
    refine ⟨w j1, w j2, w j3, ?_, ?_⟩
    · rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
          Finset.sum_singleton] at hsum
      rw [hwi] at hsum
      simpa [add_assoc] using hsum
    · intro x
      unfold mult4 counts
      let Q : Finset (Fin N) := {i, j1, j2, j3}
      have hQsub : (Q.filter fun j => w j = x) ⊆ Finset.univ.filter fun j => w j = x :=
        Finset.filter_subset_filter _ (Finset.subset_univ _)
      have hcard := Finset.card_le_card hQsub
      have hQcard : (Q.filter fun j => w j = x).card =
          (if x = r then 1 else 0) + (if x = w j1 then 1 else 0) +
          (if x = w j2 then 1 else 0) + (if x = w j3 then 1 else 0) := by
        dsimp only [Q]
        rw [card_filter_insert_eq _ _ _ (by simp [hi1, hi2, hi3]),
            card_filter_insert_eq _ _ _ (by simp [h12, h13]),
            card_filter_insert_eq _ _ _ (by simp [h23]),
            card_filter_singleton_eq, hwi]
        by_cases h0 : x = r <;> by_cases h1 : x = w j1 <;>
          by_cases h2 : x = w j2 <;> by_cases h3 : x = w j3 <;>
          simp [h0, h1, h2, h3, eq_comm] <;> omega
      omega
  · intro hvc i
    have hpos : 0 < counts w (w i) :=
      Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
    obtain ⟨a, b, d, hmod, hmult⟩ := hvc (w i) hpos
    have hpick1 : ∃ j1 : Fin N, w j1 = a ∧ j1 ≠ i := by
      let S := (Finset.univ.filter fun j : Fin N => w j = a).erase i
      have hcard : 0 < S.card := by
        dsimp only [S]
        have hm := hmult a
        unfold mult4 counts at hm
        have h1 : (if a = a then 1 else 0) = 1 := if_pos rfl
        rw [h1] at hm
        by_cases hia : a = w i
        · have hmem : i ∈ Finset.univ.filter fun j : Fin N => w j = a :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, hia.symm⟩
          rw [Finset.card_erase_of_mem hmem, hia]
          simp [hia] at hm
          omega
        · have hnot : i ∉ Finset.univ.filter fun j : Fin N => w j = a := by
            simp [hia, eq_comm]
          rw [Finset.erase_eq_of_notMem hnot]
          simp [hia] at hm
          omega
      obtain ⟨j1, hj1⟩ := Finset.card_pos.1 hcard
      exact ⟨j1, (Finset.mem_filter.1 (Finset.mem_erase.1 hj1).2).2, (Finset.mem_erase.1 hj1).1⟩
    obtain ⟨j1, hj1w, hj1i⟩ := hpick1
    have hpick2 : ∃ j2 : Fin N, w j2 = b ∧ j2 ≠ i ∧ j2 ≠ j1 := by
      let S := (Finset.univ.filter fun j : Fin N => w j = b) \ {i, j1}
      have hcard : 0 < S.card := by
        dsimp only [S]
        have hm := hmult b
        unfold mult4 counts at hm
        have h1 : (if b = b then 1 else 0) = 1 := if_pos rfl
        rw [h1] at hm
        have hsub : ((Finset.univ.filter fun j : Fin N => w j = b) ∩ {i, j1}).card =
            (if b = w i then 1 else 0) + (if b = a then 1 else 0) := by
          have hset : ((Finset.univ.filter fun j : Fin N => w j = b) ∩ {i, j1}) =
              ({i, j1} : Finset (Fin N)).filter (fun j => w j = b) := by
            ext j; simp [and_comm]
          rw [hset, card_filter_insert_eq _ _ _ (by simp [hj1i.symm]), card_filter_singleton_eq, hj1w]
          have heq1 : (w i = b) ↔ (b = w i) := eq_comm
          have heq2 : (a = b) ↔ (b = a) := eq_comm
          simp only [heq1, heq2]
        have hle := Finset.card_sdiff_add_card_inter
          (Finset.univ.filter fun j : Fin N => w j = b) ({i, j1} : Finset (Fin N))
        omega
      obtain ⟨j2, hj2⟩ := Finset.card_pos.1 hcard
      rw [Finset.mem_sdiff] at hj2
      exact ⟨j2, (Finset.mem_filter.1 hj2.1).2, by simp_all⟩
    obtain ⟨j2, hj2w, hj2i, hj21⟩ := hpick2
    have hpick3 : ∃ j3 : Fin N, w j3 = d ∧ j3 ≠ i ∧ j3 ≠ j1 ∧ j3 ≠ j2 := by
      let S := (Finset.univ.filter fun j : Fin N => w j = d) \ {i, j1, j2}
      have hcard : 0 < S.card := by
        dsimp only [S]
        have hm := hmult d
        unfold mult4 counts at hm
        have h1 : (if d = d then 1 else 0) = 1 := if_pos rfl
        rw [h1] at hm
        have hsub : ((Finset.univ.filter fun j : Fin N => w j = d) ∩ {i, j1, j2}).card =
            (if d = w i then 1 else 0) + (if d = a then 1 else 0) + (if d = b then 1 else 0) := by
          have hset : ((Finset.univ.filter fun j : Fin N => w j = d) ∩ {i, j1, j2}) =
              ({i, j1, j2} : Finset (Fin N)).filter (fun j => w j = d) := by
            ext j; simp [and_comm]
          rw [hset, card_filter_insert_eq _ _ _ (by simp [hj1i.symm, hj2i.symm]),
              card_filter_insert_eq _ _ _ (by simp [hj21.symm]), card_filter_singleton_eq,
              hj1w, hj2w]
          have heq1 : (w i = d) ↔ (d = w i) := eq_comm
          have heq2 : (a = d) ↔ (d = a) := eq_comm
          have heq3 : (b = d) ↔ (d = b) := eq_comm
          simp only [heq1, heq2, heq3]
          ring
        have hle := Finset.card_sdiff_add_card_inter
          (Finset.univ.filter fun j : Fin N => w j = d) ({i, j1, j2} : Finset (Fin N))
        omega
      obtain ⟨j3, hj3⟩ := Finset.card_pos.1 hcard
      rw [Finset.mem_sdiff] at hj3
      exact ⟨j3, (Finset.mem_filter.1 hj3.1).2, by simp_all⟩
    obtain ⟨j3, hj3w, hj3i, hj31, hj32⟩ := hpick3
    refine ⟨{j1, j2, j3}, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [hj21.symm, hj31.symm]),
          Finset.card_insert_of_notMem (by simp [hj32.symm]), Finset.card_singleton]
    · simp [hj1i.symm, hj2i.symm, hj3i.symm]
    · rw [Finset.sum_insert (by simp [hj21.symm, hj31.symm]),
          Finset.sum_insert (by simp [hj32.symm]), Finset.sum_singleton,
          hj1w, hj2w, hj3w]
      simpa [add_assoc] using hmod

private lemma validCounts_cap4 (c : Fin 4 → ℕ) :
    validCounts c ↔ validCounts (fun x => min (c x) 4) := by
  unfold validCounts
  constructor <;> intro h r hr
  · dsimp only at hr
    obtain ⟨a, b, d, hmod, hmult⟩ := h r (by omega)
    refine ⟨a, b, d, hmod, fun x => ?_⟩
    dsimp only
    have hm := hmult x
    have hle4 : mult4 r a b d x ≤ 4 := by unfold mult4; split_ifs <;> omega
    omega
  · obtain ⟨a, b, d, hmod, hmult⟩ := h r (by dsimp only; omega)
    refine ⟨a, b, d, hmod, fun x => ?_⟩
    have hm := hmult x
    dsimp only at hm
    omega

private def validProfB (p : Fin 4 → Fin 5) : Bool :=
  (List.finRange 4).all fun r =>
    if (p r).1 == 0 then true
    else
      (List.finRange 4).any fun a =>
        (List.finRange 4).any fun b =>
          (List.finRange 4).any fun d =>
            ((a.1 + b.1 + d.1) % 4 == r.1) &&
            (List.finRange 4).all fun x =>
              Nat.ble (mult4 r a b d x) (p x).1

private lemma validProfB_iff (p : Fin 4 → Fin 5) :
    validProfB p = true ↔ validCounts (fun x => (p x).1) := by
  unfold validProfB validCounts
  rw [List.all_eq_true]
  constructor
  · intro h r hr
    dsimp only at hr
    have h' := h r (List.mem_finRange r)
    have hne : ((p r).1 == 0) = false := beq_false_of_ne (by omega)
    rw [hne] at h'
    simp only [Bool.false_eq_true, ↓reduceIte, List.any_eq_true, List.mem_finRange, true_and,
      Bool.and_eq_true, beq_iff_eq, List.all_eq_true, true_implies, Nat.ble_eq] at h'
    obtain ⟨a, b, d, hmod, hmult⟩ := h'
    exact ⟨a, b, d, hmod, hmult⟩
  · intro h r _
    by_cases h0 : (p r).1 = 0
    · simp [h0]
    · have hne : ((p r).1 == 0) = false := beq_false_of_ne h0
      rw [hne]
      simp only [Bool.false_eq_true, ↓reduceIte, List.any_eq_true, List.mem_finRange, true_and,
        Bool.and_eq_true, beq_iff_eq, List.all_eq_true, true_implies, Nat.ble_eq]
      obtain ⟨a, b, d, hmod, hmult⟩ := h r (by dsimp only; omega)
      exact ⟨a, b, d, hmod, hmult⟩

private instance : DecidablePred validCounts := fun c =>
  decidable_of_iff (validProfB (fun r => ⟨min (c r) 4, by omega⟩) = true) (by
    rw [validProfB_iff, ← validCounts_cap4])

private def profSum (p : Fin 4 → Fin 5) : ℕ :=
  (p 0).1 + (p 1).1 + (p 2).1 + (p 3).1

private def profFree (p : Fin 4 → Fin 5) : ℕ :=
  (if (p 0).1 = 4 then 1 else 0) + (if (p 1).1 = 4 then 1 else 0) +
  (if (p 2).1 = 4 then 1 else 0) + (if (p 3).1 = 4 then 1 else 0)

private def simplexCard : ℕ → ℕ → ℕ
  | 0, m => if m = 0 then 1 else 0
  | 1, _ => 1
  | 2, m => m + 1
  | 3, m => (m + 2) * (m + 1) / 2
  | 4, m => (m + 3) * (m + 2) * (m + 1) / 6
  | _ + 5, _ => 0

private def profCard (p : Fin 4 → Fin 5) (N : ℕ) : ℕ :=
  if profSum p ≤ N then simplexCard (profFree p) (N - profSum p) else 0

private lemma card_tuples_sum_eq (k m : ℕ) (hk : k ≤ 4) :
    ((Fintype.piFinset fun _ : Fin k => Finset.range (m + 1)).filter
      (fun d => ∑ i : Fin k, d i = m)).card = simplexCard k m := by
  match k with
  | 0 =>
    simp only [simplexCard]
    by_cases hm : m = 0
    · subst hm; simp
    · simp only [hm, ↓reduceIte]
      have hemp : ((Fintype.piFinset fun _ : Fin 0 => Finset.range (m + 1)).filter
          (fun d => ∑ i : Fin 0, d i = m)) = ∅ := by
        ext d; simp [hm, eq_comm]
      rw [hemp, Finset.card_empty]
  | 1 =>
    simp only [simplexCard]
    have hset : ((Fintype.piFinset fun _ : Fin 1 => Finset.range (m + 1)).filter
        (fun d => ∑ i : Fin 1, d i = m)) = {fun _ => m} := by
      ext d
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Fin.sum_univ_one,
        Finset.mem_singleton]
      constructor
      · intro ⟨_, h0⟩; funext i; fin_cases i; exact h0
      · intro hd; subst hd; exact ⟨fun _ => by dsimp only; omega, rfl⟩
    rw [hset, Finset.card_singleton]
  | 2 =>
    simp only [simplexCard]
    have hbij :
        ((Fintype.piFinset fun _ : Fin 2 => Finset.range (m + 1)).filter
          (fun d => ∑ i : Fin 2, d i = m)).card = (Finset.range (m + 1)).card := by
      refine Finset.card_bij (fun d _ => d 0)
        (fun d hd => by
          simp only [Finset.mem_filter, Fintype.mem_piFinset] at hd
          exact hd.1 0)
        (fun d1 hd1 d2 hd2 h => by
          simp only [Finset.mem_filter, Fin.sum_univ_two] at hd1 hd2
          funext i; fin_cases i
          · exact h
          · change d1 1 = d2 1; omega)
        (fun a ha => by
          simp only [Finset.mem_range] at ha
          refine ⟨![a, m - a], ?_, rfl⟩
          simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Fin.sum_univ_two,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          refine ⟨fun i => ?_, by omega⟩
          fin_cases i
          · change a < m + 1; omega
          · change m - a < m + 1; omega)
    rw [hbij, Finset.card_range]
  | 3 =>
    have hrec : ∀ n : ℕ,
        ((Fintype.piFinset fun _ : Fin 3 => Finset.range (n + 1)).filter
          (fun d => ∑ i : Fin 3, d i = n)).card = (n + 2) * (n + 1) / 2 := by
      intro n
      have hpart :
          ((Fintype.piFinset fun _ : Fin 3 => Finset.range (n + 1)).filter
            (fun d => ∑ i : Fin 3, d i = n)).card =
          ∑ a ∈ Finset.range (n + 1), (n - a + 1) := by
        rw [Finset.card_eq_sum_card_fiberwise (f := fun d : Fin 3 → ℕ => d 0)
          (t := Finset.range (n + 1)) (fun d hd => (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hd).1) 0)]
        refine Finset.sum_congr rfl fun a ha => ?_
        have hale : a ≤ n := by have := Finset.mem_range.1 ha; omega
        have hbij :
            (((Fintype.piFinset fun _ : Fin 3 => Finset.range (n + 1)).filter
              (fun d => ∑ i : Fin 3, d i = n)).filter (fun d => d 0 = a)).card =
            (Finset.range (n - a + 1)).card := by
          refine Finset.card_bij (fun d _ => d 1)
            (fun d hd => by
              simp only [Finset.mem_filter, Fin.sum_univ_three, Finset.mem_range] at hd ⊢
              omega)
            (fun d1 hd1 d2 hd2 h => by
              simp only [Finset.mem_filter, Fin.sum_univ_three] at hd1 hd2
              funext i; fin_cases i
              · change d1 0 = d2 0; omega
              · exact h
              · change d1 2 = d2 2; omega)
            (fun b hb => by
              simp only [Finset.mem_range] at hb
              refine ⟨![a, b, n - a - b], ?_, rfl⟩
              simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
                Fin.sum_univ_three]
              refine ⟨⟨fun i => ?_, ?_⟩, rfl⟩
              · fin_cases i
                · change a < n + 1; omega
                · change b < n + 1; omega
                · change n - a - b < n + 1; omega
              · change a + b + (n - a - b) = n; omega)
        rw [hbij, Finset.card_range]
      rw [hpart]
      have hsum : 2 * (∑ a ∈ Finset.range (n + 1), (n - a + 1)) = (n + 2) * (n + 1) := by
        clear hpart
        induction n with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ']
          have hshift : (∑ a ∈ Finset.range (k + 1), (k + 1 - (a + 1) + 1)) =
              ∑ a ∈ Finset.range (k + 1), (k - a + 1) := by
            refine Finset.sum_congr rfl fun a _ => by omega
          rw [hshift]
          have h0 : k + 1 - 0 + 1 = k + 2 := by omega
          rw [h0, mul_add, ih]
          ring
      omega
    exact hrec m
  | 4 =>
    have hrec : ∀ n : ℕ,
        ((Fintype.piFinset fun _ : Fin 4 => Finset.range (n + 1)).filter
          (fun d => ∑ i : Fin 4, d i = n)).card = (n + 3) * (n + 2) * (n + 1) / 6 := by
      intro n
      have hpart :
          ((Fintype.piFinset fun _ : Fin 4 => Finset.range (n + 1)).filter
            (fun d => ∑ i : Fin 4, d i = n)).card =
          ∑ a ∈ Finset.range (n + 1), ((n - a + 2) * (n - a + 1) / 2) := by
        rw [Finset.card_eq_sum_card_fiberwise (f := fun d : Fin 4 → ℕ => d 0)
          (t := Finset.range (n + 1)) (fun d hd => (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hd).1) 0)]
        refine Finset.sum_congr rfl fun a ha => ?_
        have hale : a ≤ n := by have := Finset.mem_range.1 ha; omega
        have hbij :
            (((Fintype.piFinset fun _ : Fin 4 => Finset.range (n + 1)).filter
              (fun d => ∑ i : Fin 4, d i = n)).filter (fun d => d 0 = a)).card =
            ((Fintype.piFinset fun _ : Fin 3 => Finset.range (n - a + 1)).filter
              (fun d => ∑ i : Fin 3, d i = n - a)).card := by
          refine Finset.card_bij (fun d _ => fun i : Fin 3 => d i.succ)
            (fun d hd => by
              simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
                Fin.sum_univ_four, Fin.sum_univ_three] at hd ⊢
              refine ⟨fun i => ?_, ?_⟩
              · fin_cases i
                · change d 1 < n - a + 1; omega
                · change d 2 < n - a + 1; omega
                · change d 3 < n - a + 1; omega
              · change d 1 + d 2 + d 3 = n - a; omega)
            (fun d1 hd1 d2 hd2 h => by
              simp only [Finset.mem_filter] at hd1 hd2
              funext i
              refine Fin.cases ?_ (fun k => congrFun h k) i
              omega)
            (fun d hd => by
              simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
                Fin.sum_univ_three] at hd
              refine ⟨Fin.cons a d, ?_, by funext k; rfl⟩
              simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Fin.sum_univ_four]
              refine ⟨⟨fun i => ?_, ?_⟩, rfl⟩
              · refine Fin.cases (by change a < n + 1; omega)
                  (fun k => by have := hd.1 k; change d k < n + 1; omega) i
              · change a + d 0 + d 1 + d 2 = n
                omega)
        rw [hbij]
        exact card_tuples_sum_eq 3 (n - a) (by omega)
      rw [hpart]
      have hdiv2 : ∀ t : ℕ, 2 ∣ (t + 2) * (t + 1) := fun t => by
        rcases Nat.even_or_odd t with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
        · exact ⟨(2 * k + 3) * (k + 1), by ring⟩
      have hsum : 6 * (∑ a ∈ Finset.range (n + 1), ((n - a + 2) * (n - a + 1) / 2)) =
          (n + 3) * (n + 2) * (n + 1) := by
        clear hpart
        induction n with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ']
          have hshift :
              (∑ a ∈ Finset.range (k + 1), ((k + 1 - (a + 1) + 2) * (k + 1 - (a + 1) + 1) / 2)) =
              ∑ a ∈ Finset.range (k + 1), ((k - a + 2) * (k - a + 1) / 2) := by
            refine Finset.sum_congr rfl fun a _ => by congr 1; congr 1 <;> omega
          rw [hshift]
          have h0 : k + 1 - 0 + 2 = k + 3 := by omega
          have h1 : k + 1 - 0 + 1 = k + 2 := by omega
          rw [h0, h1]
          have hd : 2 * ((k + 3) * (k + 2) / 2) = (k + 3) * (k + 2) :=
            Nat.mul_div_cancel' (hdiv2 (k + 1))
          have hmul : 6 * ((k + 3) * (k + 2) / 2) = 3 * ((k + 3) * (k + 2)) := by omega
          rw [mul_add, ih, hmul]
          ring
      omega
    exact hrec m

private lemma card_fiber_prof (p : Fin 4 → Fin 5) (N : ℕ) :
    ((Fintype.piFinset fun _ : Fin 4 => Finset.range (N + 1)).filter
      (fun c => (∑ r : Fin 4, c r = N) ∧ ∀ r : Fin 4, min (c r) 4 = (p r).1)).card =
    profCard p N := by
  unfold profCard
  by_cases hle : profSum p ≤ N
  · simp only [hle, ↓reduceIte]
    let freeSet : Finset (Fin 4) := Finset.univ.filter fun r => (p r).1 = 4
    have hfreeCard : freeSet.card = profFree p := by
      unfold freeSet profFree
      rw [Finset.card_filter, Fin.sum_univ_four]
    have hfreeLe : freeSet.card ≤ 4 := by
      have := Finset.card_le_univ freeSet
      simpa using this
    let e : Fin (profFree p) ≃ freeSet :=
      (Fintype.equivFinOfCardEq (by simp [hfreeCard])).symm
    have hbij :
        ((Fintype.piFinset fun _ : Fin 4 => Finset.range (N + 1)).filter
          (fun c => (∑ r : Fin 4, c r = N) ∧ ∀ r : Fin 4, min (c r) 4 = (p r).1)).card =
        ((Fintype.piFinset fun _ : Fin (profFree p) => Finset.range (N - profSum p + 1)).filter
          (fun d => ∑ i : Fin (profFree p), d i = N - profSum p)).card := by
      refine Finset.card_bij
        (fun c _ => fun i : Fin (profFree p) => c (e i).1 - 4)
        (fun c hc => by
          simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hc ⊢
          have hge : ∀ r : Fin 4, (p r).1 ≤ c r := fun r => by have := hc.2.2 r; omega
          have hsum_eq : ∑ r : Fin 4, (c r - (p r).1) = N - profSum p := by
            have h1 : ∑ r : Fin 4, (c r - (p r).1) + ∑ r : Fin 4, (p r).1 = ∑ r : Fin 4, c r := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun r _ => Nat.sub_add_cancel (hge r)
            have hps : ∑ r : Fin 4, (p r).1 = profSum p := by
              unfold profSum; rw [Fin.sum_univ_four]
            omega
          have hsum_free : ∑ i : Fin (profFree p), (c (e i).1 - 4) = ∑ r : Fin 4, (c r - (p r).1) := by
            rw [Fintype.sum_equiv e _ (fun x : freeSet => c x.1 - 4) (fun _ => rfl)]
            rw [Finset.univ_eq_attach]
            have hsub : (∑ x ∈ freeSet.attach, (c x.1 - 4)) = ∑ r ∈ freeSet, (c r - (p r).1) := by
              rw [← Finset.sum_attach (s := freeSet) (f := fun r => c r - (p r).1)]
              refine Finset.sum_congr rfl fun x _ => by
                have hx : (p x.1).1 = 4 := (Finset.mem_filter.1 x.2).2
                rw [hx]
            rw [hsub]
            refine Finset.sum_subset (Finset.subset_univ _) fun r _ hr => ?_
            have hne4 : (p r).1 ≠ 4 := fun h4 => hr (Finset.mem_filter.2 ⟨Finset.mem_univ _, h4⟩)
            have hpr := hc.2.2 r
            have hlt : (p r).1 < 4 := by have := (p r).2; omega
            have hceq : c r = (p r).1 := by omega
            omega
          refine ⟨fun i => ?_, hsum_free.trans hsum_eq⟩
          have hi : c (e i).1 - 4 ≤ ∑ j : Fin (profFree p), (c (e j).1 - 4) :=
            Finset.single_le_sum (f := fun j => c (e j).1 - 4) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          omega)
        (fun c1 hc1 c2 hc2 h => by
          simp only [Finset.mem_filter] at hc1 hc2
          funext r
          by_cases hr : (p r).1 = 4
          · have hmem : r ∈ freeSet := Finset.mem_filter.2 ⟨Finset.mem_univ _, hr⟩
            have hi := congrFun h (e.symm ⟨r, hmem⟩)
            simp only [Equiv.apply_symm_apply] at hi
            have h1 := hc1.2.2 r
            have h2 := hc2.2.2 r
            omega
          · have hlt : (p r).1 < 4 := by have := (p r).2; omega
            have h1 := hc1.2.2 r
            have h2 := hc2.2.2 r
            omega)
        (fun d hd => by
          simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hd
          let c : Fin 4 → ℕ := fun r =>
            if hr : r ∈ freeSet then 4 + d (e.symm ⟨r, hr⟩) else (p r).1
          refine ⟨c, ?_, ?_⟩
          · simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
            have hsum_c : ∑ r : Fin 4, c r = N := by
              have h1 : ∀ r : Fin 4,
                  c r = (p r).1 + if hr : r ∈ freeSet then d (e.symm ⟨r, hr⟩) else 0 := by
                intro r
                dsimp only [c]
                by_cases hr : r ∈ freeSet
                · have hp4 : (p r).1 = 4 := (Finset.mem_filter.1 hr).2
                  simp [hr, hp4]
                · simp [hr]
              have hsplit : ∑ r : Fin 4, c r =
                  (∑ r : Fin 4, (p r).1) +
                  ∑ r ∈ freeSet, if hr : r ∈ freeSet then d (e.symm ⟨r, hr⟩) else 0 := by
                calc ∑ r : Fin 4, c r
                    = ∑ r : Fin 4, ((p r).1 + if hr : r ∈ freeSet then d (e.symm ⟨r, hr⟩) else 0) :=
                        Finset.sum_congr rfl fun r _ => h1 r
                  _ = (∑ r : Fin 4, (p r).1) +
                      ∑ r : Fin 4, (if hr : r ∈ freeSet then d (e.symm ⟨r, hr⟩) else 0) :=
                        Finset.sum_add_distrib
                  _ = _ := by
                        congr 1
                        rw [← Finset.sum_subset (Finset.subset_univ freeSet)]
                        intro r _ hr; simp [hr]
              have hsum_d :
                  (∑ r ∈ freeSet, if hr : r ∈ freeSet then d (e.symm ⟨r, hr⟩) else 0) =
                  ∑ i : Fin (profFree p), d i := by
                rw [← Finset.sum_attach (s := freeSet)]
                rw [← Finset.univ_eq_attach]
                refine Fintype.sum_equiv e.symm _ d fun x => by simp [x.2]
              have hps : ∑ r : Fin 4, (p r).1 = profSum p := by unfold profSum; rw [Fin.sum_univ_four]
              omega
            refine ⟨fun r => ?_, hsum_c, fun r => ?_⟩
            · have hle_r : c r ≤ ∑ s : Fin 4, c s :=
                Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
              omega
            · dsimp only [c]
              by_cases hr : r ∈ freeSet
              · have hp4 : (p r).1 = 4 := (Finset.mem_filter.1 hr).2
                simp [hr, hp4]
              · have hne4 : (p r).1 ≠ 4 := fun h4 => hr (Finset.mem_filter.2 ⟨Finset.mem_univ _, h4⟩)
                have hlt : (p r).1 < 4 := by have := (p r).2; omega
                simp [hr]
                omega
          · funext i
            dsimp only [c]
            simp [(e i).2])
    rw [hbij]
    exact card_tuples_sum_eq (profFree p) (N - profSum p) (by omega)
  · simp only [hle, ↓reduceIte]
    have hemp : ((Fintype.piFinset fun _ : Fin 4 => Finset.range (N + 1)).filter
        (fun c => (∑ r : Fin 4, c r = N) ∧ ∀ r : Fin 4, min (c r) 4 = (p r).1)) = ∅ := by
      ext c
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨_, hsum, hmin⟩
      rw [Fin.sum_univ_four] at hsum
      have h0 := hmin 0; have h1 := hmin 1; have h2 := hmin 2; have h3 := hmin 3
      unfold profSum at hle
      omega
    rw [hemp, Finset.card_empty]

private lemma card_valid_eq_profSum (N : ℕ) :
    ((sortedWords N).filter Valid).card =
      ∑ p : Fin 4 → Fin 5, if validProfB p = true then profCard p N else 0 := by
  have h1 :
      ((sortedWords N).filter Valid).card =
      ((Fintype.piFinset fun _ : Fin 4 => Finset.range (N + 1)).filter
        (fun c : Fin 4 → ℕ => (∑ r : Fin 4, c r = N) ∧ validCounts c)).card := by
    refine Finset.card_bij (fun w _ => counts w)
      (fun w hw => by
        simp only [Finset.mem_filter, sortedWords, Finset.mem_univ, true_and,
          Fintype.mem_piFinset, Finset.mem_range] at hw ⊢
        refine ⟨fun r => ?_, sum_counts w, (valid_iff_validCounts w).1 hw.2⟩
        have hle : counts w r ≤ ∑ s : Fin 4, counts w s :=
          Finset.single_le_sum (f := counts w) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
        rw [sum_counts w] at hle
        omega)
      (fun w1 hw1 w2 hw2 h => by
        simp only [Finset.mem_filter, sortedWords, Finset.mem_univ, true_and] at hw1 hw2
        rw [← fromCounts_counts hw1.1, ← fromCounts_counts hw2.1, h])
      (fun c hc => by
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hc
        refine ⟨fromCounts c, ?_, counts_fromCounts c hc.2.1⟩
        simp only [Finset.mem_filter, sortedWords, Finset.mem_univ, true_and]
        exact ⟨fromCounts_mono c, (valid_iff_validCounts (fromCounts c)).2
          (by rw [counts_fromCounts c hc.2.1]; exact hc.2.2)⟩)
  rw [h1]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun c : Fin 4 → ℕ => fun r : Fin 4 => (⟨min (c r) 4, by omega⟩ : Fin 5))
    (t := (Finset.univ : Finset (Fin 4 → Fin 5)))
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : validProfB p = true
  · simp only [hp, ↓reduceIte]
    have hvp : validCounts (fun r => (p r).1) := (validProfB_iff p).1 hp
    have hset :
        (((Fintype.piFinset fun _ : Fin 4 => Finset.range (N + 1)).filter
          (fun c : Fin 4 → ℕ => (∑ r : Fin 4, c r = N) ∧ validCounts c)).filter
          (fun c => (fun r => (⟨min (c r) 4, by omega⟩ : Fin 5)) = p)) =
        ((Fintype.piFinset fun _ : Fin 4 => Finset.range (N + 1)).filter
          (fun c : Fin 4 → ℕ => (∑ r : Fin 4, c r = N) ∧ ∀ r : Fin 4, min (c r) 4 = (p r).1)) := by
      ext c
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hmem, hsum, _⟩, hpeq⟩
        exact ⟨hmem, hsum, fun r => by simpa using congrArg Fin.val (congrFun hpeq r)⟩
      · rintro ⟨hmem, hsum, hmin⟩
        refine ⟨⟨hmem, hsum, ?_⟩, funext fun r => Fin.ext (hmin r)⟩
        rw [validCounts_cap4]
        convert hvp using 1
        funext r; exact hmin r
    rw [hset]
    exact card_fiber_prof p N
  · rw [if_neg hp]
    have hemp :
        (((Fintype.piFinset fun _ : Fin 4 => Finset.range (N + 1)).filter
          (fun c : Fin 4 → ℕ => (∑ r : Fin 4, c r = N) ∧ validCounts c)).filter
          (fun c => (fun r => (⟨min (c r) 4, by omega⟩ : Fin 5)) = p)) = ∅ := by
      ext c
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨⟨_, _, hvc⟩, hpeq⟩
      apply hp
      rw [validProfB_iff]
      rw [validCounts_cap4] at hvc
      convert hvc using 1
      funext r
      exact (congrArg Fin.val (congrFun hpeq r)).symm
    rw [hemp, Finset.card_empty]

private def profPoly6 (p : Fin 4 → Fin 5) : ℤ × ℤ × ℤ × ℤ :=
  let k := profFree p
  let s : ℤ := profSum p
  match k with
  | 1 => (0, 0, 0, 6)
  | 2 => (0, 0, 6, 6 * (1 - s))
  | 3 => (0, 3, 3 * (3 - 2 * s), 3 * (s - 2) * (s - 1))
  | 4 => (1, 6 - 3 * s, 3 * s * s - 12 * s + 11, -s * s * s + 6 * s * s - 11 * s + 6)
  | _ => (0, 0, 0, 0)

private lemma six_mul_profCard_ge16 (p : Fin 4 → Fin 5) (N : ℕ) (hN : 16 ≤ N) :
    (6 : ℤ) * (profCard p N : ℤ) =
      let c := profPoly6 p
      c.1 * (N : ℤ) ^ 3 + c.2.1 * (N : ℤ) ^ 2 + c.2.2.1 * (N : ℤ) + c.2.2.2 := by
  have hsle : profSum p ≤ 16 := by
    unfold profSum
    have h0 := (p 0).2; have h1 := (p 1).2; have h2 := (p 2).2; have h3 := (p 3).2
    omega
  have hle : profSum p ≤ N := by omega
  unfold profCard profPoly6
  simp only [hle, ↓reduceIte]
  have hk : profFree p ≤ 4 := by
    unfold profFree; split_ifs <;> omega
  have h0lt : profFree p = 0 → profSum p < 16 := by
    intro h0
    unfold profFree at h0
    unfold profSum
    have hp0 := (p 0).2; have hp1 := (p 1).2; have hp2 := (p 2).2; have hp3 := (p 3).2
    split_ifs at h0 <;> omega
  have hdiv2 : ∀ m : ℕ, 2 ∣ (m + 2) * (m + 1) := fun m => by
    rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact ⟨(t + 1) * (2 * t + 1), by ring⟩
    · exact ⟨(2 * t + 3) * (t + 1), by ring⟩
  have hdiv6 : ∀ m : ℕ, 6 ∣ (m + 3) * (m + 2) * (m + 1) := fun m => by
    have hd2 : 2 ∣ (m + 3) * (m + 2) * (m + 1) := by
      rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨(2 * t + 3) * (t + 1) * (2 * t + 1), by ring⟩
      · exact ⟨(t + 2) * (2 * t + 3) * (2 * t + 2), by ring⟩
    have hd3 : 3 ∣ (m + 3) * (m + 2) * (m + 1) := by
      have hmod : ∃ q, m = 3 * q ∨ m = 3 * q + 1 ∨ m = 3 * q + 2 := ⟨m / 3, by omega⟩
      obtain ⟨q, rfl | rfl | rfl⟩ := hmod
      · exact ⟨(q + 1) * (3 * q + 2) * (3 * q + 1), by ring⟩
      · exact ⟨(3 * q + 4) * (q + 1) * (3 * q + 2), by ring⟩
      · exact ⟨(3 * q + 5) * (3 * q + 4) * (q + 1), by ring⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) hd2 hd3
  rcases hfree : profFree p with _ | _ | _ | _ | _ | k
  · have hlt := h0lt hfree
    simp only [simplexCard, show N - profSum p ≠ 0 by omega, ↓reduceIte]
    ring
  · simp only [simplexCard]
    ring
  · simp only [simplexCard]
    have hsub : ((N - profSum p : ℕ) : ℤ) = (N : ℤ) - (profSum p : ℤ) := Nat.cast_sub hle
    push_cast [hsub]
    ring
  · simp only [simplexCard]
    set m := N - profSum p
    have hm : (m : ℤ) = (N : ℤ) - (profSum p : ℤ) := Nat.cast_sub hle
    have hd : (2 : ℤ) * (((m + 2) * (m + 1) / 2 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' (hdiv2 m)
    have h6 : (6 : ℤ) * (((m + 2) * (m + 1) / 2 : ℕ) : ℤ) = 3 * (((m + 2 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ)) := by
      linarith
    rw [h6]
    push_cast [hm]
    ring
  · simp only [simplexCard]
    set m := N - profSum p
    have hm : (m : ℤ) = (N : ℤ) - (profSum p : ℤ) := Nat.cast_sub hle
    have hd : (6 : ℤ) * (((m + 3) * (m + 2) * (m + 1) / 6 : ℕ) : ℤ) =
        ((m + 3 : ℕ) : ℤ) * ((m + 2 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' (hdiv6 m)
    rw [hd]
    push_cast [hm]
    ring
  · omega

private lemma sum_univ_prof (f : (Fin 4 → Fin 5) → ℤ) :
    (∑ p : Fin 4 → Fin 5, f p) =
      ∑ p0 : Fin 5, ∑ p1 : Fin 5, ∑ p2 : Fin 5, ∑ p3 : Fin 5,
        f (fun r => match r with | ⟨0, _⟩ => p0 | ⟨1, _⟩ => p1 | ⟨2, _⟩ => p2 | ⟨3, _⟩ => p3) := by
  let e : (Fin 4 → Fin 5) ≃ Fin 5 × Fin 5 × Fin 5 × Fin 5 :=
    { toFun := fun p => (p 0, p 1, p 2, p 3)
      invFun := fun q r =>
        match r with
        | ⟨0, _⟩ => q.1
        | ⟨1, _⟩ => q.2.1
        | ⟨2, _⟩ => q.2.2.1
        | ⟨3, _⟩ => q.2.2.2
      left_inv := fun p => by funext r; fin_cases r <;> rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  rw [Fintype.sum_equiv e _ (fun q => f (e.symm q)) (fun p => by simp)]
  simp only [Fintype.sum_prod_type]
  rfl

private def sumProf5 (f : (Fin 4 → Fin 5) → ℤ) : ℤ :=
  ∑ p0 : Fin 5, ∑ p1 : Fin 5, ∑ p2 : Fin 5, ∑ p3 : Fin 5,
    f (fun r => match r with | ⟨0, _⟩ => p0 | ⟨1, _⟩ => p1 | ⟨2, _⟩ => p2 | ⟨3, _⟩ => p3)

private lemma checkCoeffs :
    sumProf5 (fun p => if validProfB p then (profPoly6 p).1 else 0) = 1 ∧
    sumProf5 (fun p => if validProfB p then (profPoly6 p).2.1 else 0) = 6 ∧
    sumProf5 (fun p => if validProfB p then (profPoly6 p).2.2.1 else 0) = -13 ∧
    sumProf5 (fun p => if validProfB p then (profPoly6 p).2.2.2 else 0) = -126 := by
  decide +kernel

private lemma checkSmall :
    sumProf5 (fun p => if validProfB p then (profCard p 4 : ℤ) else 0) = 5 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 5 : ℤ) else 0) = 14 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 6 : ℤ) else 0) = 38 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 7 : ℤ) else 0) = 70 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 8 : ℤ) else 0) = 111 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 9 : ℤ) else 0) = 162 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 10 : ℤ) else 0) = 224 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 11 : ℤ) else 0) = 298 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 12 : ℤ) else 0) = 385 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 13 : ℤ) else 0) = 486 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 14 : ℤ) else 0) = 602 ∧
    sumProf5 (fun p => if validProfB p then (profCard p 15 : ℤ) else 0) = 734 := by
  decide +kernel

private lemma a_eq_sumProf5 (n : ℕ) (hn : 1 ≤ n) :
    a n = sumProf5 (fun p => if validProfB p then (profCard p (n + 3) : ℤ) else 0) := by
  unfold a
  simp only [show n ≠ 0 by omega, ↓reduceIte]
  rw [card_valid_eq_profSum (n + 3), Nat.cast_sum]
  rw [sum_univ_prof]
  unfold sumProf5
  refine Finset.sum_congr rfl fun p0 _ => Finset.sum_congr rfl fun p1 _ =>
    Finset.sum_congr rfl fun p2 _ => Finset.sum_congr rfl fun p3 _ => ?_
  dsimp only
  split_ifs <;> simp

private lemma six_mul_a_ge2 (n : ℕ) (hn : 2 ≤ n) :
    6 * a n = (n : ℤ) ^ 3 + 15 * (n : ℤ) ^ 2 + 50 * (n : ℤ) - 84 := by
  obtain ⟨_, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := checkSmall
  by_cases h13 : 13 ≤ n
  · rw [a_eq_sumProf5 n (by omega)]
    have hN : 16 ≤ n + 3 := by omega
    have hsum :
        (6 : ℤ) * sumProf5 (fun p => if validProfB p then (profCard p (n + 3) : ℤ) else 0) =
        sumProf5 (fun p => if validProfB p then (profPoly6 p).1 else 0) * ((n + 3 : ℕ) : ℤ) ^ 3 +
        sumProf5 (fun p => if validProfB p then (profPoly6 p).2.1 else 0) * ((n + 3 : ℕ) : ℤ) ^ 2 +
        sumProf5 (fun p => if validProfB p then (profPoly6 p).2.2.1 else 0) * ((n + 3 : ℕ) : ℤ) +
        sumProf5 (fun p => if validProfB p then (profPoly6 p).2.2.2 else 0) := by
      unfold sumProf5
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p0 _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p1 _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p2 _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p3 _ => ?_
      by_cases hp : validProfB (fun r => match r with | ⟨0, _⟩ => p0 | ⟨1, _⟩ => p1 | ⟨2, _⟩ => p2 | ⟨3, _⟩ => p3) = true
      · simp only [hp, ↓reduceIte]
        exact six_mul_profCard_ge16 _ (n + 3) hN
      · simp [hp]
    rw [hsum, checkCoeffs.1, checkCoeffs.2.1, checkCoeffs.2.2.1, checkCoeffs.2.2.2]
    push_cast
    ring
  · interval_cases n <;> simp [a_eq_sumProf5, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

private lemma a_one : a 1 = 5 := by
  rw [a_eq_sumProf5 1 (by omega)]
  exact checkSmall.1

private lemma a_zero : a 0 = 0 := by simp [a]

private lemma a_rec (n : ℕ) (hn : 5 < n) :
    a n = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  have h0 := six_mul_a_ge2 n (by omega)
  have h1 := six_mul_a_ge2 (n - 1) (by omega)
  have h2 := six_mul_a_ge2 (n - 2) (by omega)
  have h3 := six_mul_a_ge2 (n - 3) (by omega)
  have h4 := six_mul_a_ge2 (n - 4) (by omega)
  have c1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have c2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have c3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  have c4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
  rw [c1] at h1; rw [c2] at h2; rw [c3] at h3; rw [c4] at h4
  linarith

private theorem main_proved :
    (∀ n : ℕ, 2 ≤ n → 6 * a n = (n : ℤ)^3 + 15*(n : ℤ)^2 + 50*(n : ℤ) - 84) ∧
    (PowerSeries.mk a * (1 - X)^4 = X*(5 - 6*X + 12*X^2 - 18*X^3 + 8*X^4)) ∧
    (∀ n : ℕ, 5 < n → a n = 4*a (n-1) - 6*a (n-2) + 4*a (n-3) - a (n-4)) := by
  refine ⟨six_mul_a_ge2, ?_, a_rec⟩
  set F : PowerSeries ℤ := PowerSeries.mk a
  have hD : (1 - X : PowerSeries ℤ) ^ 4 = 1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4 := by ring
  have hR : X * (5 - 6 * X + 12 * X ^ 2 - 18 * X ^ 3 + 8 * X ^ 4 : PowerSeries ℤ) =
      C (5 : ℤ) * X - C (6 : ℤ) * X ^ 2 + C (12 : ℤ) * X ^ 3 -
        C (18 : ℤ) * X ^ 4 + C (8 : ℤ) * X ^ 5 := by
    simp only [map_ofNat]
    ring
  ext n
  have hL : PowerSeries.coeff n (F * (1 - X) ^ 4) =
      PowerSeries.coeff n F
      - 4 * PowerSeries.coeff n (F * X ^ 1)
      + 6 * PowerSeries.coeff n (F * X ^ 2)
      - 4 * PowerSeries.coeff n (F * X ^ 3)
      + PowerSeries.coeff n (F * X ^ 4) := by
    rw [hD]
    have hring : F * (1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4) =
        F - C (4 : ℤ) * (F * X ^ 1) + C (6 : ℤ) * (F * X ^ 2) -
          C (4 : ℤ) * (F * X ^ 3) + (F * X ^ 4) := by
      simp only [map_ofNat]
      ring
    rw [hring]
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul]
  rw [hL, hR]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_X, PowerSeries.coeff_C]
  have ha0 := a_zero
  have ha1 := a_one
  have ha2 : a 2 = 14 := by have := six_mul_a_ge2 2 (by omega); omega
  have ha3 : a 3 = 38 := by have := six_mul_a_ge2 3 (by omega); omega
  have ha4 : a 4 = 70 := by have := six_mul_a_ge2 4 (by omega); omega
  have ha5 : a 5 = 111 := by have := six_mul_a_ge2 5 (by omega); omega
  match n with
  | 0 => simp [F, ha0]
  | 1 => simp [F, ha0, ha1]
  | 2 => norm_num [F, ha0, ha1, ha2]
  | 3 => norm_num [F, ha0, ha1, ha2, ha3]
  | 4 => norm_num [F, ha0, ha1, ha2, ha3, ha4]
  | 5 => norm_num [F, ha0, ha1, ha2, ha3, ha4, ha5]
  | m + 6 =>
    simp only [F, PowerSeries.coeff_mk,
      show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega,
      show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega,
      show m + 6 ≠ 1 by omega,
      show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega,
      show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega,
      show m + 1 ≠ 0 by omega,
      ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hr := a_rec (m + 6) (by omega)
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega] at hr
    linarith

end OMA.S_oeis_a183898_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a183898.main :=
  OMA.S_oeis_a183898_Proof.main_proved
