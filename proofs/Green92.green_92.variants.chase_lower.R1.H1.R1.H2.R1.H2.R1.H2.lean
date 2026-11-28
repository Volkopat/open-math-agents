import OMAReductions.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1_H2_R1

/-!
Proof of `Green92.green_92.variants.chase_lower.R1.H1.R1.H2.R1.H2.R1.H2`:
Separated-position second moment bound for Chase's lower bound on trace reconstruction
(arXiv:1905.03031v2, Section 3.4).
-/

section Green92ChaseH2

open Finset Filter Real

private lemma mL {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := mul_le_mul_of_nonneg_left h hc
private lemma mR {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := mul_le_mul_of_nonneg_right h hc
private lemma dR {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := div_le_div_of_nonneg_right h hc

-- ============================================================================
-- Section 1: Exact combinatorial identities for `cnt`, `F`, and 4-case regrouping
-- ============================================================================

private def cnt (w : List Bool) : ℕ :=
  (w.zip w.tail).count (false, true)

private def F (a : ℕ) (w : List Bool) : ℕ :=
  (a + cnt w).choose w.length

private lemma zip_tail_append_singleton (v : List Bool) (x : Bool) :
    (v ++ [x]).zip (v ++ [x]).tail =
      match v.getLast? with
      | none => []
      | some y => v.zip v.tail ++ [(y, x)] := by
  induction v with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b r =>
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons, List.getLast?_cons_cons]
      have iht : (b :: (r ++ [x])).zip (r ++ [x]) =
          match (b :: r).getLast? with
          | none => []
          | some y => (b :: r).zip r ++ [(y, x)] := by
        simpa only [List.cons_append, List.tail_cons] using ih
      cases hlast : (b :: r).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hlast) (List.cons_ne_nil b r)
      | some y =>
        rw [hlast] at iht
        simp only [iht]

private lemma cnt_append_singleton (v : List Bool) (x : Bool) :
    cnt (v ++ [x]) = cnt v + if v.getLast? = some false ∧ x = true then 1 else 0 := by
  unfold cnt
  rw [zip_tail_append_singleton]
  cases hv : v.getLast? with
  | none =>
    have hnil : v = [] := List.getLast?_eq_none_iff.mp hv
    subst hnil; simp
  | some y =>
    rw [List.count_append]
    cases y <;> cases x <;> simp

private lemma cnt_append (u v : List Bool) :
    cnt (u ++ v) = cnt u + cnt v +
      if u.getLast? = some false ∧ v.head? = some true then 1 else 0 := by
  induction v using List.reverseRecOn with
  | nil => simp [cnt]
  | append_singleton v' x ih =>
    rw [← List.append_assoc, cnt_append_singleton, cnt_append_singleton, ih]
    cases v' with
    | nil =>
      simp only [List.append_nil, List.nil_append, List.head?_nil, List.head?_cons,
        List.getLast?_nil, Option.some.injEq]
      cases x <;> simp
    | cons h t =>
      have hne : h :: t ≠ [] := List.cons_ne_nil h t
      rw [List.getLast?_append_of_ne_nil u hne]
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at ih ⊢
      split_ifs <;> omega

private lemma cnt_append_true_append (u v : List Bool) :
    cnt (u ++ [true] ++ v) = cnt u + cnt v + if u.getLast? = some false then 1 else 0 := by
  rw [cnt_append, cnt_append_singleton]
  have hlast : (u ++ [true]).getLast? = some true := by simp
  rw [hlast]
  simp
  omega

private def altWord (a : ℕ) (i : Fin (2 * a)) : Bool :=
  decide (i.val % 2 = 1)

private def altTrace (a : ℕ) (S : Finset (Fin (2 * a))) : List Bool :=
  ((List.finRange (2 * a)).filter (fun i => i ∈ S)).map (altWord a)

private lemma list_finRange_two_succ (a : ℕ) :
    List.finRange (2 * (a + 1)) =
      (List.finRange (2 * a)).map (Fin.castAdd 2) ++
        [⟨2 * a, by omega⟩, ⟨2 * a + 1, by omega⟩] := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_finRange]
    by_cases hi : i < 2 * a
    · rw [List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_finRange]
      rfl
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_map, List.length_finRange]
      have hsub : i - 2 * a = 0 ∨ i - 2 * a = 1 := by simp at h1; omega
      rcases hsub with h0 | h1'
      · apply Fin.ext; simp [h0]; omega
      · apply Fin.ext; simp [h1']; omega

private lemma altTrace_succ (a : ℕ) (S : Finset (Fin (2 * (a + 1)))) :
    let S' : Finset (Fin (2 * a)) := univ.filter (fun i => Fin.castAdd 2 i ∈ S)
    let b0 : Bool := decide (⟨2 * a, by omega⟩ ∈ S)
    let b1 : Bool := decide (⟨2 * a + 1, by omega⟩ ∈ S)
    altTrace (a + 1) S =
      altTrace a S' ++ (if b0 then [false] else []) ++ (if b1 then [true] else []) := by
  intro S' b0 b1
  unfold altTrace
  rw [list_finRange_two_succ, List.filter_append, List.map_append]
  have hleft :
      (((List.finRange (2 * a)).map (Fin.castAdd 2)).filter (fun i => i ∈ S)).map (altWord (a + 1)) =
        ((List.finRange (2 * a)).filter (fun i => i ∈ S')).map (altWord a) := by
    rw [List.filter_map, List.map_map]
    refine congrArg₂ List.map ?_ ?_
    · funext i; simp [altWord]
    · refine congrArg (fun p => List.filter p (List.finRange (2 * a))) ?_
      funext i; simp [S']
  rw [hleft, List.append_assoc]
  congr 1
  have hw0 : altWord (a + 1) ⟨2 * a, by omega⟩ = false := by simp [altWord]
  have hw1 : altWord (a + 1) ⟨2 * a + 1, by omega⟩ = true := by simp [altWord]
  dsimp only [b0, b1]
  by_cases h0 : (⟨2 * a, by omega⟩ : Fin (2 * (a + 1))) ∈ S <;>
  by_cases h1 : (⟨2 * a + 1, by omega⟩ : Fin (2 * (a + 1))) ∈ S <;>
  simp [h0, h1, hw0, hw1]

private lemma card_altTrace_eq_F (a : ℕ) :
    ∀ w : List Bool, (univ.filter (fun S : Finset (Fin (2 * a)) => altTrace a S = w)).card = F a w := by
  induction a with
  | zero =>
    intro w
    have huniv : (univ : Finset (Finset (Fin 0))) = {∅} := by
      ext s; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Finset.eq_empty_of_isEmpty s
    cases w with
    | nil => rw [huniv]; simp [altTrace, F, cnt]
    | cons x xs =>
      rw [huniv]
      have hne : altTrace 0 ∅ ≠ x :: xs := by simp [altTrace]
      have hcnt : cnt (x :: xs) < (x :: xs).length := by
        unfold cnt
        have h1 : ((x :: xs).zip (x :: xs).tail).count (false, true) ≤
            ((x :: xs).zip (x :: xs).tail).length := List.count_le_length
        simp only [List.tail_cons, List.length_zip, List.length_cons,
          min_eq_right (Nat.le_succ _)] at h1 ⊢
        omega
      rw [Finset.filter_singleton, if_neg hne, card_empty]
      simp only [F, zero_add]
      exact (Nat.choose_eq_zero_of_lt hcnt).symm
  | succ a ih =>
    intro w
    let p0 : Fin (2 * (a + 1)) := ⟨2 * a, by omega⟩
    let p1 : Fin (2 * (a + 1)) := ⟨2 * a + 1, by omega⟩
    let split : Finset (Fin (2 * (a + 1))) ≃ Finset (Fin (2 * a)) × Bool × Bool :=
      { toFun := fun S => (univ.filter (fun i => Fin.castAdd 2 i ∈ S), decide (p0 ∈ S), decide (p1 ∈ S))
        invFun := fun ⟨S', b0, b1⟩ =>
          S'.image (Fin.castAdd 2) ∪ (if b0 then {p0} else ∅) ∪ (if b1 then {p1} else ∅)
        left_inv := fun S => by
          ext i
          simp only [mem_union, mem_image, mem_filter, mem_univ, true_and]
          by_cases hlt : i.val < 2 * a
          · have hi0 : i ≠ p0 := fun h => by have := congrArg Fin.val h; dsimp [p0] at this; omega
            have hi1 : i ≠ p1 := fun h => by have := congrArg Fin.val h; dsimp [p1] at this; omega
            have h1 : (∃ x : Fin (2 * a), Fin.castAdd 2 x ∈ S ∧ Fin.castAdd 2 x = i) ↔ i ∈ S :=
              ⟨fun ⟨x, hx, hxi⟩ => hxi ▸ hx, fun hi => ⟨⟨i.val, hlt⟩, hi, Fin.ext rfl⟩⟩
            by_cases hb0 : p0 ∈ S <;> by_cases hb1 : p1 ∈ S <;> simp [hb0, hb1, hi0, hi1, h1]
          · have hcases : i = p0 ∨ i = p1 := by
              have := i.isLt
              rcases (show i.val = 2 * a ∨ i.val = 2 * a + 1 by omega) with h | h
              · exact Or.inl (Fin.ext h)
              · exact Or.inr (Fin.ext h)
            have hno : ¬ ∃ x : Fin (2 * a), Fin.castAdd 2 x ∈ S ∧ Fin.castAdd 2 x = i := by
              rintro ⟨x, _, hxi⟩; have := congrArg Fin.val hxi; simp at this; omega
            have hp01 : p0 ≠ p1 := fun h => by have := congrArg Fin.val h; dsimp [p0, p1] at this; omega
            rcases hcases with rfl | rfl <;>
            · by_cases hb0 : p0 ∈ S <;> by_cases hb1 : p1 ∈ S <;> simp [hb0, hb1, hno, hp01, hp01.symm]
        right_inv := fun ⟨S', b0, b1⟩ => by
          have h0 : ∀ i : Fin (2 * a), Fin.castAdd 2 i ≠ p0 := fun i h => by
            have := congrArg Fin.val h; dsimp [p0] at this; omega
          have h1 : ∀ i : Fin (2 * a), Fin.castAdd 2 i ≠ p1 := fun i h => by
            have := congrArg Fin.val h; dsimp [p1] at this; omega
          have hp01 : p0 ≠ p1 := fun h => by have := congrArg Fin.val h; dsimp [p0, p1] at this; omega
          ext1
          · ext i
            simp only [mem_filter, mem_univ, true_and, mem_union, mem_image]
            cases b0 <;> cases b1 <;> simp [h0 i, h1 i]
          · ext1
            · cases b0 <;> cases b1 <;> simp [h0, hp01]
            · cases b0 <;> cases b1 <;> simp [h1, hp01.symm] }
    have hcard_eq :
        (univ.filter (fun S : Finset (Fin (2 * (a + 1))) => altTrace (a + 1) S = w)).card =
        (univ.filter (fun t : Finset (Fin (2 * a)) × Bool × Bool =>
          altTrace a t.1 ++ (if t.2.1 then [false] else []) ++ (if t.2.2 then [true] else []) = w)).card := by
      refine card_bij (fun S _ => split S) ?_ ?_ ?_
      · intro S hS
        simp only [mem_filter, mem_univ, true_and] at hS ⊢
        dsimp only [split, Equiv.coe_fn_mk, p0, p1]
        rw [← altTrace_succ a S]; exact hS
      · intro S₁ _ S₂ _ h; exact split.injective h
      · intro t ht
        refine ⟨split.symm t, ?_, split.apply_symm_apply t⟩
        simp only [mem_filter, mem_univ, true_and] at ht ⊢
        rw [altTrace_succ a (split.symm t)]
        have hst := split.apply_symm_apply t
        have h1 : (split (split.symm t)).1 = t.1 := congrArg Prod.fst hst
        have h2 : (split (split.symm t)).2.1 = t.2.1 := congrArg (fun p => p.2.1) hst
        have h3 : (split (split.symm t)).2.2 = t.2.2 := congrArg (fun p => p.2.2) hst
        change altTrace a (split (split.symm t)).1 ++
            (if (split (split.symm t)).2.1 then [false] else []) ++
            (if (split (split.symm t)).2.2 then [true] else []) = w
        rw [h1, h2, h3]; exact ht
    rw [hcard_eq]
    have hsum4 :
        (univ.filter (fun t : Finset (Fin (2 * a)) × Bool × Bool =>
          altTrace a t.1 ++ (if t.2.1 then [false] else []) ++ (if t.2.2 then [true] else []) = w)).card =
        (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' = w)).card +
        (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [false] = w)).card +
        (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [true] = w)).card +
        (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [false, true] = w)).card := by
      have hprod : (univ : Finset (Finset (Fin (2 * a)) × Bool × Bool)) =
          univ ×ˢ (univ ×ˢ univ) := rfl
      rw [hprod, card_filter, sum_product, sum_comm]
      simp only [sum_product, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
        List.append_nil]
      have hft : ∀ s : List Bool, s ++ [false] ++ [true] = s ++ [false, true] := fun s => by simp
      simp only [hft, ← card_filter]
      omega
    rw [hsum4]
    induction w using List.reverseRecOn with
    | nil =>
      have h1 : (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [false] = [])).card = 0 := by
        simp
      have h2 : (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [true] = [])).card = 0 := by
        simp
      have h3 : (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [false, true] = [])).card = 0 := by
        simp
      rw [ih [], h1, h2, h3]; simp [F, cnt]
    | append_singleton v x _ =>
      cases x
      · have h0 : (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [false] = v ++ [false])).card = F a v := by
          simp only [List.append_cancel_right_eq]; exact ih v
        have h1 : (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [true] = v ++ [false])).card = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]; intro S' _ h
          have := congrArg List.getLast? h; simp at this
        have h2 : (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [false, true] = v ++ [false])).card = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]; intro S' _ h
          have h' : (altTrace a S' ++ [false]) ++ [true] = v ++ [false] := by simpa using h
          have := congrArg List.getLast? h'; simp at this
        rw [ih (v ++ [false]), h0, h1, h2]
        simp only [add_zero, F, cnt_append_singleton, Bool.false_eq_true, and_false, ↓reduceIte,
          List.length_append, List.length_singleton]
        have hch := Nat.choose_succ_succ (a + cnt v) v.length
        simp only [Nat.succ_eq_add_one] at hch
        rw [show a + 1 + cnt v = (a + cnt v) + 1 by omega]; omega
      · have h0 : ∀ v' : List Bool, (univ.filter (fun S' : Finset (Fin (2 * a)) =>
            altTrace a S' ++ [false] = v' ++ [true])).card = 0 := by
          intro v'; rw [card_eq_zero, filter_eq_empty_iff]; intro S' _ h
          have := congrArg List.getLast? h; simp at this
        have h1 : ∀ v' : List Bool, (univ.filter (fun S' : Finset (Fin (2 * a)) =>
            altTrace a S' ++ [true] = v' ++ [true])).card = F a v' := by
          intro v'; simp only [List.append_cancel_right_eq]; exact ih v'
        refine List.reverseRecOn v ?_ ?_
        · have h2 : (univ.filter (fun S' : Finset (Fin (2 * a)) =>
              altTrace a S' ++ [false, true] = [] ++ [true])).card = 0 := by
            rw [card_eq_zero, filter_eq_empty_iff]; intro S' _ h
            have := congrArg List.length h; simp at this
          rw [ih ([] ++ [true]), h0 [], h1 [], h2]; simp [F, cnt]
        · intro u y _
          cases y
          · have h2 : (univ.filter (fun S' : Finset (Fin (2 * a)) =>
                altTrace a S' ++ [false, true] = (u ++ [false]) ++ [true])).card = F a u := by
              have heq : (u ++ [false]) ++ [true] = u ++ [false, true] := by simp
              rw [heq]; simp only [List.append_cancel_right_eq]; exact ih u
            rw [ih ((u ++ [false]) ++ [true]), h0 (u ++ [false]), h1 (u ++ [false]), h2]
            have hcf : cnt (u ++ [false]) = cnt u := by simp [cnt_append_singleton]
            have hcf2 : cnt ((u ++ [false]) ++ [true]) = cnt u + 1 := by
              rw [cnt_append_singleton, hcf]; simp
            simp only [add_zero, F, hcf, hcf2, List.length_append, List.length_singleton]
            have hc1 := Nat.choose_succ_succ (a + cnt u) u.length
            have hc2 := Nat.choose_succ_succ (a + cnt u + 1) (u.length + 1)
            simp only [Nat.succ_eq_add_one] at hc1 hc2
            have ha1 : a + 1 + (cnt u + 1) = (a + cnt u + 1) + 1 := by omega
            have ha2 : a + (cnt u + 1) = a + cnt u + 1 := by omega
            rw [ha1, ha2]; omega
          · have h2 : (univ.filter (fun S' : Finset (Fin (2 * a)) =>
                altTrace a S' ++ [false, true] = (u ++ [true]) ++ [true])).card = 0 := by
              rw [card_eq_zero, filter_eq_empty_iff]; intro S' _ h
              have h' : (altTrace a S' ++ [false]) ++ [true] = (u ++ [true]) ++ [true] := by simpa using h
              have := congrArg List.getLast? (List.append_cancel_right h'); simp at this
            rw [ih ((u ++ [true]) ++ [true]), h0 (u ++ [true]), h1 (u ++ [true]), h2]
            have hct2 : cnt ((u ++ [true]) ++ [true]) = cnt (u ++ [true]) := by
              rw [cnt_append_singleton]; simp
            simp only [add_zero, F, hct2, List.length_append, List.length_singleton]
            have hch := Nat.choose_succ_succ (a + cnt (u ++ [true])) (u.length + 1)
            simp only [Nat.succ_eq_add_one] at hch
            rw [show a + 1 + cnt (u ++ [true]) = (a + cnt (u ++ [true])) + 1 by omega]; omega

private lemma sum_F_le_pow (a : ℕ) (S : Finset (List Bool)) :
    ∑ w ∈ S, F a w ≤ 2 ^ (2 * a) := by
  have h1 : ∑ w ∈ S, F a w =
      ∑ w ∈ S, (univ.filter (fun X : Finset (Fin (2 * a)) => altTrace a X = w)).card :=
    sum_congr rfl fun w _ => (card_altTrace_eq_F a w).symm
  rw [h1, ← card_biUnion]
  · calc (S.biUnion (fun w => univ.filter (fun X : Finset (Fin (2 * a)) => altTrace a X = w))).card
        ≤ (univ : Finset (Finset (Fin (2 * a)))).card := card_le_univ _
      _ = 2 ^ (2 * a) := by simp
  · intro w₁ _ w₂ _ hne
    exact disjoint_left.mpr fun X h1 h2 =>
      hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)

private def allLists (L : ℕ) : Finset (List Bool) :=
  (univ : Finset (Fin L → Bool)).image List.ofFn

private lemma mem_allLists_iff {L : ℕ} {w : List Bool} :
    w ∈ allLists L ↔ w.length = L := by
  unfold allLists
  rw [mem_image]
  constructor
  · rintro ⟨f, _, rfl⟩; simp
  · intro h
    refine ⟨fun i => w[i.val]'(by omega), mem_univ _, ?_⟩
    apply List.ext_getElem
    · simp [h]
    · intro i h1 h2; simp

private lemma card_allLists_cnt_last :
    ∀ (L : ℕ), 1 ≤ L → ∀ (c : ℕ) (b : Bool),
      ((allLists L).filter (fun w => cnt w = c ∧ w.getLast? = some b)).card =
        L.choose (2 * c + if b then 0 else 1) := by
  intro L hL
  obtain ⟨L', rfl⟩ := Nat.exists_eq_add_of_le' hL
  clear hL
  induction L' with
  | zero =>
    intro c b
    have hset : allLists 1 = {[false], [true]} := by
      ext w
      rw [mem_allLists_iff]
      simp only [mem_insert, mem_singleton]
      constructor
      · intro hw
        cases w with
        | nil => simp at hw
        | cons x xs =>
          cases xs with
          | nil => cases x <;> simp
          | cons _ _ => simp at hw
      · rintro (rfl | rfl) <;> simp
    rw [hset]
    cases b <;> cases c with
    | zero => decide
    | succ c' =>
      rw [Nat.choose_eq_zero_of_lt (by omega), card_eq_zero, filter_eq_empty_iff]
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp [cnt]
  | succ L' ih =>
    intro c b
    have hL' : L' + 1 + 1 = (L' + 1) + 1 := rfl
    let S := (allLists (L' + 1 + 1)).filter (fun w => cnt w = c ∧ w.getLast? = some b)
    let S0 := (allLists (L' + 1)).filter (fun v => cnt (v ++ [b]) = c ∧ v.getLast? = some false)
    let S1 := (allLists (L' + 1)).filter (fun v => cnt (v ++ [b]) = c ∧ v.getLast? = some true)
    have hbij : S.card = (S0 ∪ S1).card := by
      refine card_bij (fun w _ => w.dropLast) ?_ ?_ ?_
      · intro w hw
        simp only [S, mem_filter, mem_allLists_iff] at hw
        have hwne : w ≠ [] := by intro h; subst h; simp at hw
        have hwl : w.dropLast ++ [b] = w := by
          have h1 := List.dropLast_append_getLast hwne
          have h2 : w.getLast hwne = b := by
            have := List.getLast?_eq_some_getLast hwne
            rw [hw.2.2] at this
            exact Option.some.inj this.symm
          rwa [h2] at h1
        have hlen : w.dropLast.length = L' + 1 := by simp [hw.1]
        have hne' : w.dropLast ≠ [] := by intro h; rw [h] at hlen; simp at hlen
        have hlast := List.getLast?_eq_some_getLast hne'
        cases hb' : w.dropLast.getLast hne'
        · rw [hb'] at hlast
          exact mem_union_left _ (mem_filter.mpr ⟨mem_allLists_iff.mpr hlen, hwl.symm ▸ hw.2.1, hlast⟩)
        · rw [hb'] at hlast
          exact mem_union_right _ (mem_filter.mpr ⟨mem_allLists_iff.mpr hlen, hwl.symm ▸ hw.2.1, hlast⟩)
      · intro w₁ hw₁ w₂ hw₂ hEq
        simp only [S, mem_filter, mem_allLists_iff] at hw₁ hw₂
        have h1ne : w₁ ≠ [] := by intro h; subst h; simp at hw₁
        have h2ne : w₂ ≠ [] := by intro h; subst h; simp at hw₂
        have h1 := List.dropLast_append_getLast h1ne
        have h2 := List.dropLast_append_getLast h2ne
        have hl1 : w₁.getLast h1ne = b := Option.some.inj ((List.getLast?_eq_some_getLast h1ne).symm.trans hw₁.2.2)
        have hl2 : w₂.getLast h2ne = b := Option.some.inj ((List.getLast?_eq_some_getLast h2ne).symm.trans hw₂.2.2)
        rw [← h1, ← h2, hEq, hl1, hl2]
      · intro v hv
        refine ⟨v ++ [b], ?_, by simp⟩
        rcases mem_union.mp hv with hv0 | hv1
        · simp only [S0, mem_filter, mem_allLists_iff] at hv0
          exact mem_filter.mpr ⟨mem_allLists_iff.mpr (by simp [hv0.1]), hv0.2.1, by simp⟩
        · simp only [S1, mem_filter, mem_allLists_iff] at hv1
          exact mem_filter.mpr ⟨mem_allLists_iff.mpr (by simp [hv1.1]), hv1.2.1, by simp⟩
    have hdisj : Disjoint S0 S1 := by
      rw [disjoint_left]
      intro v hv0 hv1
      have h0 := (mem_filter.mp hv0).2.2
      have h1 := (mem_filter.mp hv1).2.2
      rw [h0] at h1; simp at h1
    change S.card = _
    rw [hbij, card_union_of_disjoint hdisj]
    cases b
    · -- b = false: cnt (v ++ [false]) = cnt v
      have hS0 : S0 = (allLists (L' + 1)).filter (fun v => cnt v = c ∧ v.getLast? = some false) := by
        ext v; simp [S0, cnt_append_singleton]
      have hS1 : S1 = (allLists (L' + 1)).filter (fun v => cnt v = c ∧ v.getLast? = some true) := by
        ext v; simp [S1, cnt_append_singleton]
      rw [hS0, hS1, ih c false, ih c true]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      have hch := Nat.choose_succ_succ (L' + 1) (2 * c)
      simp only [Nat.succ_eq_add_one] at hch
      omega
    · -- b = true: if v ends in false, cnt (v ++ [true]) = cnt v + 1; if true, cnt v
      have hS1 : S1 = (allLists (L' + 1)).filter (fun v => cnt v = c ∧ v.getLast? = some true) := by
        ext v
        simp only [S1, mem_filter, cnt_append_singleton]
        constructor
        · rintro ⟨hv, hcnt, hlast⟩
          refine ⟨hv, ?_, hlast⟩
          simp [hlast] at hcnt; exact hcnt
        · rintro ⟨hv, hcnt, hlast⟩
          refine ⟨hv, ?_, hlast⟩
          simp [hlast]; exact hcnt
      cases c with
      | zero =>
        have hS0 : S0 = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro v hv
          simp only [S0, mem_filter, cnt_append_singleton] at hv
          simp [hv.2.2] at hv
        rw [hS0, hS1, card_empty, zero_add, ih 0 true]
        simp
      | succ c' =>
        have hS0 : S0 = (allLists (L' + 1)).filter (fun v => cnt v = c' ∧ v.getLast? = some false) := by
          ext v
          simp only [S0, mem_filter, cnt_append_singleton]
          constructor
          · rintro ⟨hv, hcnt, hlast⟩
            refine ⟨hv, ?_, hlast⟩
            simp [hlast] at hcnt; omega
          · rintro ⟨hv, hcnt, hlast⟩
            refine ⟨hv, ?_, hlast⟩
            simp [hlast]; omega
        rw [hS0, hS1, ih c' false, ih (c' + 1) true]
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        have hch := Nat.choose_succ_succ (L' + 1) (2 * c' + 1)
        simp only [Nat.succ_eq_add_one] at hch
        rw [show 2 * (c' + 1) = 2 * c' + 1 + 1 by omega]
        omega

private lemma card_allLists_cnt (L c : ℕ) :
    ((allLists L).filter (fun w => cnt w = c)).card = (L + 1).choose (2 * c + 1) := by
  cases L with
  | zero =>
    have h0 : allLists 0 = {[]} := by
      ext w; rw [mem_allLists_iff]; simp
    rw [h0]
    cases c with
    | zero => decide
    | succ c' =>
      rw [Nat.choose_eq_zero_of_lt (by omega), card_eq_zero, filter_eq_empty_iff]
      intro w hw
      rw [mem_singleton.mp hw]
      simp [cnt]
  | succ L' =>
    let S := (allLists (L' + 1)).filter (fun w => cnt w = c)
    let S0 := (allLists (L' + 1)).filter (fun w => cnt w = c ∧ w.getLast? = some false)
    let S1 := (allLists (L' + 1)).filter (fun w => cnt w = c ∧ w.getLast? = some true)
    have hunion : S = S0 ∪ S1 := by
      ext w
      simp only [S, S0, S1, mem_union, mem_filter, mem_allLists_iff]
      constructor
      · rintro ⟨hlen, hc⟩
        have hne : w ≠ [] := by intro h; subst h; simp at hlen
        have hlast := List.getLast?_eq_some_getLast hne
        cases hb : w.getLast hne
        · rw [hb] at hlast; exact Or.inl ⟨hlen, hc, hlast⟩
        · rw [hb] at hlast; exact Or.inr ⟨hlen, hc, hlast⟩
      · rintro (⟨hlen, hc, _⟩ | ⟨hlen, hc, _⟩) <;> exact ⟨hlen, hc⟩
    have hdisj : Disjoint S0 S1 := by
      rw [disjoint_left]; intro w h0 h1
      have a := (mem_filter.mp h0).2.2; have b := (mem_filter.mp h1).2.2
      rw [a] at b; simp at b
    change S.card = _
    rw [hunion, card_union_of_disjoint hdisj,
      card_allLists_cnt_last (L' + 1) (by omega) c false,
      card_allLists_cnt_last (L' + 1) (by omega) c true]
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    have hch := Nat.choose_succ_succ (L' + 1) (2 * c)
    simp only [Nat.succ_eq_add_one] at hch
    omega

private def P_val (k b : ℕ) (w : List Bool) (j : ℕ) : ℕ :=
  if w[j]? = some true then F b (w.take j) * F (2 * k + 1 - b) (w.drop (j + 1)) else 0

private def A_val (k : ℕ) (w : List Bool) (j : ℕ) : ℝ :=
  (P_val k k w j : ℝ) - (P_val k (k + 1) w j : ℝ)

private def deltaK (k r s p q : ℕ) : ℝ :=
  (((k + r).choose p * (k + 1 + s).choose q : ℕ) : ℝ) -
    (((k + 1 + r).choose p * (k + s).choose q : ℕ) : ℝ)

private lemma A_val_eq_deltaK (k : ℕ) (w : List Bool) (j : ℕ) (hj : j < w.length)
    (ht : w[j]? = some true) :
    A_val k w j =
      deltaK k (cnt (w.take j)) (cnt (w.drop (j + 1))) j (w.length - 1 - j) := by
  unfold A_val P_val deltaK F
  rw [if_pos ht, if_pos ht]
  have h1 : 2 * k + 1 - k = k + 1 := by omega
  have h2 : 2 * k + 1 - (k + 1) = k := by omega
  have hlen1 : (w.take j).length = j := by simp; omega
  have hlen2 : (w.drop (j + 1)).length = w.length - 1 - j := by simp; omega
  rw [h1, h2, hlen1, hlen2]

private lemma cnt_drop_le (w : List Bool) (i : ℕ) : cnt (w.drop i) ≤ cnt w := by
  have hsplit : w = w.take i ++ w.drop i := (List.take_append_drop i w).symm
  conv_rhs => rw [hsplit]
  rw [cnt_append]
  omega

private lemma A_val_zero_eq_zero (k : ℕ) (w : List Bool) (h : k + 1 + cnt w < w.length - 1) :
    A_val k w 0 = 0 := by
  unfold A_val P_val
  split_ifs with ht
  · have hlen : (w.drop 1).length = w.length - 1 := by simp
    have hcnt : cnt (w.drop 1) ≤ cnt w := cnt_drop_le w 1
    have h2k1 : 2 * k + 1 - k = k + 1 := by omega
    have h2k2 : 2 * k + 1 - (k + 1) = k := by omega
    simp only [zero_add]
    rw [h2k1, h2k2]
    unfold F
    have hc1 : (k + 1 + cnt (w.drop 1)).choose (w.drop 1).length = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have hc2 : (k + cnt (w.drop 1)).choose (w.drop 1).length = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [hc1, hc2]; simp
  · simp

private lemma sum_separated_eq_two_mul_ordered (m : ℕ) (a : ℕ → ℝ) :
    (∑ p ∈ ((range m).product (range m)).filter (fun p => ¬ (p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5)),
      a p.1 * a p.2) =
    2 * ∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + 5 < t), a j * a t := by
  let S := ((range m).product (range m)).filter (fun p => ¬ (p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5))
  let S1 := ((range m).product (range m)).filter (fun p => p.1 + 5 < p.2)
  let S2 := ((range m).product (range m)).filter (fun p => p.2 + 5 < p.1)
  have hunion : S = S1 ∪ S2 := by
    ext ⟨i, j⟩
    simp only [S, S1, S2, mem_union, mem_filter]
    constructor
    · rintro ⟨hm, hnot⟩
      by_cases h1 : i + 5 < j
      · exact Or.inl ⟨hm, h1⟩
      · exact Or.inr ⟨hm, by omega⟩
    · rintro (⟨hm, h1⟩ | ⟨hm, h2⟩) <;> exact ⟨hm, by omega⟩
  have hdisj : Disjoint S1 S2 := by
    rw [disjoint_left]
    intro ⟨i, j⟩ h1 h2
    simp only [S1, S2, mem_filter] at h1 h2
    omega
  have hsym : ∑ p ∈ S2, a p.1 * a p.2 = ∑ p ∈ S1, a p.1 * a p.2 := by
    refine sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro ⟨i, j⟩ hp
      simp only [S1, S2, mem_filter, product_eq_sprod, mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro ⟨i1, j1⟩ _ ⟨i2, j2⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro ⟨i, j⟩ hp
      refine ⟨(j, i), ?_, rfl⟩
      simp only [S1, S2, mem_filter, product_eq_sprod, mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro ⟨i, j⟩ _; ring
  have hS1 : ∑ p ∈ S1, a p.1 * a p.2 =
      ∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + 5 < t), a j * a t := by
    change ∑ p ∈ ((range m) ×ˢ (range m)).filter (fun p => p.1 + 5 < p.2), a p.1 * a p.2 = _
    rw [sum_filter, sum_product]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_filter]
  change ∑ p ∈ S, a p.1 * a p.2 = _
  rw [hunion, sum_union hdisj, hsym, hS1]
  ring

private lemma list_split_two_true {w : List Bool} {m j t : ℕ}
    (hlen : w.length = m) (hjt : j + 1 < t) (htm : t < m)
    (hwj : w[j]? = some true) (hwt : w[t]? = some true) :
    w = w.take j ++ [true] ++ (w.drop (j + 1)).take (t - j - 1) ++ [true] ++ w.drop (t + 1) := by
  have hj_lt : j < w.length := by omega
  have ht_lt : t < w.length := by omega
  have hjv : w[j] = true := by
    have := List.getElem?_eq_getElem hj_lt; rw [hwj] at this; exact Option.some.inj this.symm
  have htv : w[t] = true := by
    have := List.getElem?_eq_getElem ht_lt; rw [hwt] at this; exact Option.some.inj this.symm
  have h1 : w = w.take j ++ w.drop j := (List.take_append_drop j w).symm
  have h2 : w.drop j = true :: w.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj_lt, hjv]
  have h4 : (w.drop (j + 1)).drop (t - j - 1) = w.drop t := by
    rw [List.drop_drop, show j + 1 + (t - j - 1) = t by omega]
  have h5 : w.drop t = true :: w.drop (t + 1) := by
    rw [List.drop_eq_getElem_cons ht_lt, htv]
  have h345 : w.drop (j + 1) =
      (w.drop (j + 1)).take (t - j - 1) ++ (true :: w.drop (t + 1)) := by
    rw [← h5, ← h4]
    exact (List.take_append_drop (t - j - 1) (w.drop (j + 1))).symm
  conv_lhs => rw [h1, h2, h345]
  simp [List.append_assoc]

private lemma take_drop_concat_two_true (u v z : List Bool) {j t : ℕ}
    (hu : u.length = j) (hv : v.length = t - j - 1) (hjt : j + 1 < t) :
    let w := u ++ [true] ++ v ++ [true] ++ z
    w[j]? = some true ∧
    w[t]? = some true ∧
    w.take j = u ∧
    w.drop (j + 1) = v ++ [true] ++ z ∧
    w.take t = u ++ [true] ++ v ∧
    w.drop (t + 1) = z ∧
    (w.drop (j + 1)).take (t - j - 1) = v := by
  intro w
  have hw1 : w = u ++ (true :: (v ++ [true] ++ z)) := by simp [w, List.append_assoc]
  have hw2 : w = (u ++ [true] ++ v) ++ (true :: z) := by simp [w, List.append_assoc]
  have huv_len : (u ++ [true] ++ v).length = t := by simp [hu, hv]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw1, List.getElem?_append_right (by omega)]
    simp [hu]
  · rw [hw2, List.getElem?_append_right (by omega), huv_len]
    simp
  · rw [hw1, List.take_left' hu]
  · rw [hw1]
    have : u ++ (true :: (v ++ [true] ++ z)) = (u ++ [true]) ++ (v ++ [true] ++ z) := by simp
    rw [this, List.drop_left' (by simp [hu])]
  · rw [hw2, List.take_left' huv_len]
  · rw [hw2]
    have : (u ++ [true] ++ v) ++ (true :: z) = (u ++ [true] ++ v ++ [true]) ++ z := by
      simp [List.append_assoc]
    rw [this, List.drop_left' (by simp [hu, hv]; omega)]
  · have hd : w.drop (j + 1) = v ++ ([true] ++ z) := by
      rw [hw1]
      have : u ++ (true :: (v ++ [true] ++ z)) = (u ++ [true]) ++ (v ++ ([true] ++ z)) := by
        simp [List.append_assoc]
      rw [this, List.drop_left' (by simp [hu])]
    rw [hd, List.take_left' hv]

private def dBit (u : List Bool) : ℕ :=
  if u.getLast? = some false then 1 else 0

private lemma dBit_eq_iff {u : List Bool} (hne : u ≠ []) {d : ℕ} (hd : d ∈ ({0, 1} : Finset ℕ)) :
    dBit u = d ↔ u.getLast? = some (decide (d = 0)) := by
  have hlast := List.getLast?_eq_some_getLast hne
  simp only [mem_insert, mem_singleton] at hd
  cases hb : u.getLast hne <;> rw [hb] at hlast <;> rcases hd with rfl | rfl <;>
    simp [dBit, hlast]

private lemma sum_words_pair_eq_four_cases (k m f j t : ℕ)
    (hj : 1 ≤ j) (hjt : j + 5 < t) (htm : t < m) :
    (∑ w ∈ (allLists m).filter (fun w => cnt w = f), A_val k w j * A_val k w t) =
      ∑ d1 ∈ ({0, 1} : Finset ℕ), ∑ d2 ∈ ({0, 1} : Finset ℕ),
        ∑ a ∈ range (f + 1),
          ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
            ((j.choose (2 * a + d1) * (t - j - 1).choose (2 * (b - a - d1) + d2) *
              (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) *
            deltaK k a (f - a - d1) j (m - 1 - j) *
            deltaK k b (f - b - d2) t (m - 1 - t) := by
  let W := (allLists m).filter (fun w => cnt w = f ∧ w[j]? = some true ∧ w[t]? = some true)
  have hrestrict :
      (∑ w ∈ (allLists m).filter (fun w => cnt w = f), A_val k w j * A_val k w t) =
      ∑ w ∈ W, A_val k w j * A_val k w t := by
    symm
    apply sum_subset
    · intro w hw; simp only [W, mem_filter] at hw ⊢; exact ⟨hw.1, hw.2.1⟩
    · intro w hw hnot
      simp only [W, mem_filter] at hw hnot
      have hfail : ¬ (w[j]? = some true ∧ w[t]? = some true) := fun h => hnot ⟨hw.1, hw.2, h⟩
      by_cases h1 : w[j]? = some true
      · have h2 : w[t]? ≠ some true := fun h2 => hfail ⟨h1, h2⟩
        simp [A_val, P_val, h2]
      · simp [A_val, P_val, h1]
  rw [hrestrict]
  let T := ((allLists j ×ˢ allLists (t - j - 1)) ×ˢ allLists (m - t - 1)).filter
    (fun p => cnt p.1.1 + cnt p.1.2 + cnt p.2 + dBit p.1.1 + dBit p.1.2 = f)
  have hcnt_concat : ∀ (u v z : List Bool), v.length = t - j - 1 →
      cnt (u ++ [true] ++ v ++ [true] ++ z) = cnt u + cnt v + cnt z + dBit u + dBit v := by
    intro u v z hv
    have hvne : v ≠ [] := by intro h; rw [h] at hv; simp at hv; omega
    have hlast_uv : (u ++ [true] ++ v).getLast? = v.getLast? :=
      List.getLast?_append_of_ne_nil (u ++ [true]) hvne
    rw [cnt_append_true_append (u ++ [true] ++ v) z, hlast_uv, cnt_append_true_append u v]
    unfold dBit; omega
  have hbij :
      (∑ w ∈ W, A_val k w j * A_val k w t) =
      ∑ p ∈ T,
        deltaK k (cnt p.1.1) (f - cnt p.1.1 - dBit p.1.1) j (m - 1 - j) *
        deltaK k (cnt p.1.1 + cnt p.1.2 + dBit p.1.1)
          (f - (cnt p.1.1 + cnt p.1.2 + dBit p.1.1) - dBit p.1.2) t (m - 1 - t) := by
    refine sum_bij (fun w _ => ((w.take j, (w.drop (j + 1)).take (t - j - 1)), w.drop (t + 1)))
      ?_ ?_ ?_ ?_
    · intro w hw
      simp only [W, T, mem_filter, mem_product, mem_allLists_iff] at hw ⊢
      have hu : (w.take j).length = j := by simp [hw.1]; omega
      have hv : ((w.drop (j + 1)).take (t - j - 1)).length = t - j - 1 := by simp [hw.1]; omega
      have hz : (w.drop (t + 1)).length = m - t - 1 := by simp [hw.1]; omega
      have hsp := list_split_two_true hw.1 (by omega) htm hw.2.2.1 hw.2.2.2
      have hc := hcnt_concat (w.take j) ((w.drop (j + 1)).take (t - j - 1)) (w.drop (t + 1)) hv
      rw [← hsp] at hc
      exact ⟨⟨⟨hu, hv⟩, hz⟩, by omega⟩
    · intro w1 hw1 w2 hw2 hEq
      simp only [W, mem_filter, mem_allLists_iff] at hw1 hw2
      simp only [Prod.mk.injEq] at hEq
      have hsp1 := list_split_two_true hw1.1 (by omega) htm hw1.2.2.1 hw1.2.2.2
      have hsp2 := list_split_two_true hw2.1 (by omega) htm hw2.2.2.1 hw2.2.2.2
      rw [hsp1, hsp2, hEq.1.1, hEq.1.2, hEq.2]
    · intro ⟨⟨u, v⟩, z⟩ hp
      simp only [T, mem_filter, mem_product, mem_allLists_iff] at hp
      obtain ⟨⟨⟨hu, hv⟩, hz⟩, hcf⟩ := hp
      let w := u ++ [true] ++ v ++ [true] ++ z
      have htd := take_drop_concat_two_true u v z hu hv (by omega)
      have hwlen : w.length = m := by simp [w, hu, hv, hz]; omega
      have hwcnt : cnt w = f := by rw [hcnt_concat u v z hv]; exact hcf
      refine ⟨w, ?_, ?_⟩
      · simp only [W, mem_filter, mem_allLists_iff]
        exact ⟨hwlen, hwcnt, htd.1, htd.2.1⟩
      · exact Prod.ext (Prod.ext htd.2.2.1 htd.2.2.2.2.2.2) htd.2.2.2.2.2.1
    · intro w hw
      simp only [W, mem_filter, mem_allLists_iff] at hw
      have hu : (w.take j).length = j := by simp [hw.1]; omega
      have hv : ((w.drop (j + 1)).take (t - j - 1)).length = t - j - 1 := by simp [hw.1]; omega
      have hsp := list_split_two_true hw.1 (by omega) htm hw.2.2.1 hw.2.2.2
      have htd := take_drop_concat_two_true (w.take j) ((w.drop (j + 1)).take (t - j - 1))
        (w.drop (t + 1)) hu hv (by omega)
      rw [← hsp] at htd
      have hcf := hcnt_concat (w.take j) ((w.drop (j + 1)).take (t - j - 1)) (w.drop (t + 1)) hv
      rw [← hsp, hw.2.1] at hcf
      have hcdj : cnt (w.drop (j + 1)) = f - cnt (w.take j) - dBit (w.take j) := by
        rw [htd.2.2.2.1, cnt_append_true_append]; unfold dBit at hcf ⊢; omega
      have hctt : cnt (w.take t) =
          cnt (w.take j) + cnt ((w.drop (j + 1)).take (t - j - 1)) + dBit (w.take j) := by
        rw [htd.2.2.2.2.1, cnt_append_true_append]; unfold dBit at hcf ⊢; omega
      have hcdt : cnt (w.drop (t + 1)) =
          f - (cnt (w.take j) + cnt ((w.drop (j + 1)).take (t - j - 1)) + dBit (w.take j)) -
            dBit ((w.drop (j + 1)).take (t - j - 1)) := by
        omega
      rw [A_val_eq_deltaK k w j (by omega) hw.2.2.1, A_val_eq_deltaK k w t (by omega) hw.2.2.2,
        hw.1, hcdj, hctt, hcdt]
  rw [hbij]
  let weight (d1 d2 a b : ℕ) : ℝ :=
    deltaK k a (f - a - d1) j (m - 1 - j) * deltaK k b (f - b - d2) t (m - 1 - t)
  have hexpand :
      (∑ p ∈ T, weight (dBit p.1.1) (dBit p.1.2) (cnt p.1.1) (cnt p.1.1 + cnt p.1.2 + dBit p.1.1)) =
      ∑ u ∈ allLists j, ∑ v ∈ allLists (t - j - 1), ∑ z ∈ allLists (m - t - 1),
        ∑ d1 ∈ ({0, 1} : Finset ℕ), ∑ d2 ∈ ({0, 1} : Finset ℕ),
          ∑ a ∈ range (f + 1),
            ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
              if (dBit u = d1 ∧ cnt u = a) ∧
                 (dBit v = d2 ∧ cnt v = b - a - d1) ∧
                 (cnt z = f - b - d2)
              then weight d1 d2 a b else 0 := by
    rw [sum_filter, sum_product, sum_product]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ =>
      sum_congr rfl fun z _ => ?_
    have hd1_mem : dBit u ∈ ({0, 1} : Finset ℕ) := by unfold dBit; split_ifs <;> simp
    have hd2_mem : dBit v ∈ ({0, 1} : Finset ℕ) := by unfold dBit; split_ifs <;> simp
    by_cases hsum : cnt u + cnt v + cnt z + dBit u + dBit v = f
    · rw [if_pos hsum]
      symm
      rw [sum_eq_single (dBit u)]
      · rw [sum_eq_single (dBit v)]
        · rw [sum_eq_single (cnt u)]
          · rw [sum_eq_single (cnt u + cnt v + dBit u)]
            · rw [if_pos]; refine ⟨⟨rfl, rfl⟩, ⟨rfl, by omega⟩, by omega⟩
            · intro b _ hne
              rw [if_neg]; rintro ⟨⟨_, _⟩, ⟨_, hcv⟩, _⟩; omega
            · intro hnot
              exfalso; apply hnot
              simp only [mem_filter, mem_range]; omega
          · intro a _ hne
            apply sum_eq_zero; intro b _
            rw [if_neg]; rintro ⟨⟨_, ha⟩, _, _⟩; exact hne ha.symm
          · intro hnot
            exfalso; apply hnot; simp only [mem_range]; omega
        · intro d2 _ hne
          apply sum_eq_zero; intro a _
          apply sum_eq_zero; intro b _
          rw [if_neg]; rintro ⟨_, ⟨hd2', _⟩, _⟩; exact hne hd2'.symm
        · intro hnot; exact (hnot hd2_mem).elim
      · intro d1 _ hne
        apply sum_eq_zero; intro d2 _
        apply sum_eq_zero; intro a _
        apply sum_eq_zero; intro b _
        rw [if_neg]; rintro ⟨⟨hd1', _⟩, _, _⟩; exact hne hd1'.symm
      · intro hnot; exact (hnot hd1_mem).elim
    · rw [if_neg hsum]
      symm
      apply sum_eq_zero; intro d1 _
      apply sum_eq_zero; intro d2 _
      apply sum_eq_zero; intro a _
      apply sum_eq_zero; intro b hb
      simp only [mem_filter, mem_range] at hb
      rw [if_neg]
      rintro ⟨⟨hd1, ha⟩, ⟨hd2, hcv⟩, hcz⟩
      apply hsum; omega
  change (∑ p ∈ T, weight (dBit p.1.1) (dBit p.1.2) (cnt p.1.1)
    (cnt p.1.1 + cnt p.1.2 + dBit p.1.1)) = _
  rw [hexpand]
  simp_rw [sum_comm (s := allLists (m - t - 1))]
  simp_rw [sum_comm (s := allLists (t - j - 1))]
  simp_rw [sum_comm (s := allLists j)]
  refine sum_congr rfl fun d1 hd1 => sum_congr rfl fun d2 hd2 =>
    sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  have hinner :
      (∑ z ∈ allLists (m - t - 1), ∑ v ∈ allLists (t - j - 1), ∑ u ∈ allLists j,
        if (dBit u = d1 ∧ cnt u = a) ∧ (dBit v = d2 ∧ cnt v = b - a - d1) ∧
          (cnt z = f - b - d2)
        then weight d1 d2 a b else 0) =
      (((allLists j).filter (fun u => dBit u = d1 ∧ cnt u = a)).card *
       ((allLists (t - j - 1)).filter (fun v => dBit v = d2 ∧ cnt v = b - a - d1)).card *
       ((allLists (m - t - 1)).filter (fun z => cnt z = f - b - d2)).card : ℕ) *
      weight d1 d2 a b := by
    have hstep1 : ∀ z v,
        (∑ u ∈ allLists j,
          if (dBit u = d1 ∧ cnt u = a) ∧ (dBit v = d2 ∧ cnt v = b - a - d1) ∧
            (cnt z = f - b - d2)
          then weight d1 d2 a b else 0) =
        if (dBit v = d2 ∧ cnt v = b - a - d1) ∧ (cnt z = f - b - d2) then
          (((allLists j).filter (fun u => dBit u = d1 ∧ cnt u = a)).card : ℝ) *
            weight d1 d2 a b
        else 0 := by
      intro z v
      by_cases hvz : (dBit v = d2 ∧ cnt v = b - a - d1) ∧ (cnt z = f - b - d2)
      · rw [if_pos hvz]
        simp only [hvz, and_true, ← sum_filter, sum_const, nsmul_eq_mul]
      · rw [if_neg hvz]
        apply sum_eq_zero; intro u _; rw [if_neg]; tauto
    simp_rw [hstep1]
    have hstep2 : ∀ z,
        (∑ v ∈ allLists (t - j - 1),
          if (dBit v = d2 ∧ cnt v = b - a - d1) ∧ (cnt z = f - b - d2) then
            (((allLists j).filter (fun u => dBit u = d1 ∧ cnt u = a)).card : ℝ) *
              weight d1 d2 a b
          else 0) =
        if cnt z = f - b - d2 then
          (((allLists (t - j - 1)).filter (fun v => dBit v = d2 ∧ cnt v = b - a - d1)).card : ℝ) *
          ((((allLists j).filter (fun u => dBit u = d1 ∧ cnt u = a)).card : ℝ) *
            weight d1 d2 a b)
        else 0 := by
      intro z
      by_cases hz : cnt z = f - b - d2
      · rw [if_pos hz]
        simp only [hz, and_true, ← sum_filter, sum_const, nsmul_eq_mul]
      · rw [if_neg hz]
        apply sum_eq_zero; intro v _; rw [if_neg]; tauto
    simp_rw [hstep2]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    push_cast; ring
  rw [hinner]
  have hcard1 : ((allLists j).filter (fun u => dBit u = d1 ∧ cnt u = a)).card =
      j.choose (2 * a + d1) := by
    have heq : (allLists j).filter (fun u => dBit u = d1 ∧ cnt u = a) =
        (allLists j).filter (fun u => cnt u = a ∧ u.getLast? = some (decide (d1 = 0))) := by
      ext u; simp only [mem_filter, mem_allLists_iff]
      constructor
      · rintro ⟨hlen, hdb, hc⟩
        have hne : u ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
        exact ⟨hlen, hc, (dBit_eq_iff hne hd1).mp hdb⟩
      · rintro ⟨hlen, hc, hlast⟩
        have hne : u ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
        exact ⟨hlen, (dBit_eq_iff hne hd1).mpr hlast, hc⟩
    rw [heq, card_allLists_cnt_last j hj a (decide (d1 = 0))]
    simp only [mem_insert, mem_singleton] at hd1
    rcases hd1 with rfl | rfl <;> simp
  have hcard2 : ((allLists (t - j - 1)).filter (fun v => dBit v = d2 ∧ cnt v = b - a - d1)).card =
      (t - j - 1).choose (2 * (b - a - d1) + d2) := by
    have heq : (allLists (t - j - 1)).filter (fun v => dBit v = d2 ∧ cnt v = b - a - d1) =
        (allLists (t - j - 1)).filter
          (fun v => cnt v = b - a - d1 ∧ v.getLast? = some (decide (d2 = 0))) := by
      ext v; simp only [mem_filter, mem_allLists_iff]
      constructor
      · rintro ⟨hlen, hdb, hc⟩
        have hne : v ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
        exact ⟨hlen, hc, (dBit_eq_iff hne hd2).mp hdb⟩
      · rintro ⟨hlen, hc, hlast⟩
        have hne : v ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
        exact ⟨hlen, (dBit_eq_iff hne hd2).mpr hlast, hc⟩
    rw [heq, card_allLists_cnt_last (t - j - 1) (by omega) (b - a - d1) (decide (d2 = 0))]
    simp only [mem_insert, mem_singleton] at hd2
    rcases hd2 with rfl | rfl <;> simp
  have hcard3 : ((allLists (m - t - 1)).filter (fun z => cnt z = f - b - d2)).card =
      (m - t).choose (2 * (f - b - d2) + 1) := by
    rw [card_allLists_cnt, show m - t - 1 + 1 = m - t by omega]
  rw [hcard1, hcard2, hcard3]
  unfold weight
  ring

-- ============================================================================
-- Section 2: Universal hypergeometric bounds, discrete Gaussians, and Regime 1
-- ============================================================================

private lemma choose_succ_mul_real (a r : ℕ) :
    ((a : ℝ) + 1) * (a.choose r : ℝ) = ((a : ℝ) + 1 - r) * ((a + 1).choose r : ℝ) := by
  by_cases hr : r ≤ a + 1
  · have hnat : (a + 1) * a.choose r = (a + 1 - r) * (a + 1).choose r := by
      cases r with
      | zero => simp
      | succ r' =>
        have h2 : (r' + 1) * (a + 1).choose (r' + 1) = (a + 1) * a.choose r' := by
          have := Nat.add_one_mul_choose_eq a r'; linarith
        have h3 : (a + 1).choose (r' + 1) = a.choose (r' + 1) + a.choose r' := by
          have hch := Nat.choose_succ_succ a r'; simp only [Nat.succ_eq_add_one] at hch; omega
        have h4 : (a + 1 - (r' + 1)) * (a + 1).choose (r' + 1) +
            (r' + 1) * (a + 1).choose (r' + 1) = (a + 1) * (a + 1).choose (r' + 1) := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hr]
        have h5 : (a + 1) * (a + 1).choose (r' + 1) =
            (a + 1) * a.choose (r' + 1) + (a + 1) * a.choose r' := by
          rw [h3, Nat.mul_add]
        omega
    have hR : (((a + 1) * a.choose r : ℕ) : ℝ) = (((a + 1 - r) * (a + 1).choose r : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast [Nat.cast_sub hr] at hR
    linarith
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

private lemma deltaK_exact_identity (a b m1 m2 : ℕ) :
    (((a.choose m1 * (b + 1).choose m2 : ℕ) : ℝ) - (((a + 1).choose m1 * b.choose m2 : ℕ) : ℝ)) =
      (((m2 : ℝ) * ((a : ℝ) + 1) - (m1 : ℝ) * ((b : ℝ) + 1)) /
        (((a : ℝ) + 1) * ((b : ℝ) + 1))) *
        (((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ)) := by
  have hab : (0 : ℝ) < ((a : ℝ) + 1) * ((b : ℝ) + 1) := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hab.ne']
  have hca := choose_succ_mul_real a m1
  have hcb := choose_succ_mul_real b m2
  push_cast
  calc ((a.choose m1 : ℝ) * ((b + 1).choose m2 : ℝ) -
          ((a + 1).choose m1 : ℝ) * (b.choose m2 : ℝ)) * (((a : ℝ) + 1) * ((b : ℝ) + 1))
      = (((a : ℝ) + 1) * (a.choose m1 : ℝ)) * ((b : ℝ) + 1) * ((b + 1).choose m2 : ℝ) -
        ((a : ℝ) + 1) * ((a + 1).choose m1 : ℝ) * (((b : ℝ) + 1) * (b.choose m2 : ℝ)) := by ring
    _ = (((a : ℝ) + 1 - m1) * ((a + 1).choose m1 : ℝ)) * ((b : ℝ) + 1) * ((b + 1).choose m2 : ℝ) -
        ((a : ℝ) + 1) * ((a + 1).choose m1 : ℝ) * (((b : ℝ) + 1 - m2) * ((b + 1).choose m2 : ℝ)) := by
          rw [hca, hcb]
    _ = ((m2 : ℝ) * ((a : ℝ) + 1) - (m1 : ℝ) * ((b : ℝ) + 1)) *
          (((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ)) := by ring

private lemma choose_step_real (n r : ℕ) :
    ((r : ℝ) + 1) * (n.choose (r + 1) : ℝ) = ((n : ℝ) - r) * (n.choose r : ℝ) := by
  by_cases hr : r ≤ n
  · have hnat : (r + 1) * n.choose (r + 1) = (n - r) * n.choose r := by
      have := Nat.choose_succ_right_eq n r; linarith
    have hR : (((r + 1) * n.choose (r + 1) : ℕ) : ℝ) = (((n - r) * n.choose r : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast [Nat.cast_sub hr] at hR
    linarith
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

private lemma hypergeom_step_eq (A B M r : ℕ) (hr : r < M) :
    ((A.choose (r + 1) : ℝ) * (B.choose (M - (r + 1)) : ℝ)) *
      (((r : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + (r : ℝ) + 1)) =
    ((A.choose r : ℝ) * (B.choose (M - r) : ℝ)) *
      (((A : ℝ) - (r : ℝ)) * ((M : ℝ) - (r : ℝ))) := by
  have hm : M - r = (M - (r + 1)) + 1 := by omega
  have h1 := choose_step_real A r
  have h2 := choose_step_real B (M - (r + 1))
  have hcast1 : ((M - (r + 1) : ℕ) : ℝ) + 1 = (M : ℝ) - (r : ℝ) := by
    have : (M - (r + 1) : ℕ) + 1 = M - r := by omega
    have hR : (((M - (r + 1) : ℕ) + 1 : ℕ) : ℝ) = ((M - r : ℕ) : ℝ) := by exact_mod_cast this
    push_cast [Nat.cast_sub (le_of_lt hr)] at hR
    linarith
  have hcast2 : (B : ℝ) - ((M - (r + 1) : ℕ) : ℝ) = (B : ℝ) - (M : ℝ) + (r : ℝ) + 1 := by
    linarith
  rw [hcast1, hcast2] at h2
  rw [hm]
  calc ((A.choose (r + 1) : ℝ) * (B.choose (M - (r + 1)) : ℝ)) *
        (((r : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + (r : ℝ) + 1))
      = (((r : ℝ) + 1) * (A.choose (r + 1) : ℝ)) *
        (((B : ℝ) - (M : ℝ) + (r : ℝ) + 1) * (B.choose (M - (r + 1)) : ℝ)) := by ring
    _ = (((A : ℝ) - (r : ℝ)) * (A.choose r : ℝ)) *
        (((M : ℝ) - (r : ℝ)) * (B.choose ((M - (r + 1)) + 1) : ℝ)) := by rw [h1, ← h2]
    _ = ((A.choose r : ℝ) * (B.choose ((M - (r + 1)) + 1) : ℝ)) *
        (((A : ℝ) - (r : ℝ)) * ((M : ℝ) - (r : ℝ))) := by ring

private lemma sum_hypergeom (A B M : ℕ) :
    ∑ r ∈ range (M + 1), (A.choose r : ℝ) * (B.choose (M - r) : ℝ) =
      ((A + B).choose M : ℝ) := by
  have hnat : ∑ r ∈ range (M + 1), A.choose r * B.choose (M - r) = (A + B).choose M := by
    rw [Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => A.choose i * B.choose j)]
  exact_mod_cast hnat

private lemma exp_half_lt_two : exp (1 / 2 : ℝ) < 2 := by
  have hsq : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by
    rw [sq, ← exp_add]; norm_num
  have h1 : exp 1 < 4 := lt_trans exp_one_lt_d9 (by norm_num)
  nlinarith [exp_pos (1 / 2 : ℝ)]

set_option maxHeartbeats 800000 in
private lemma hypergeom_mode_decay (A B M r0 r : ℕ) (hA : 1 ≤ A) (hr0 : r0 ≤ M) (hr : r ≤ M)
    (hmax : ∀ i ≤ M, (A.choose i : ℝ) * (B.choose (M - i) : ℝ) ≤
      (A.choose r0 : ℝ) * (B.choose (M - r0) : ℝ)) :
    (A.choose r : ℝ) * (B.choose (M - r) : ℝ) ≤
      2 * ((A.choose r0 : ℝ) * (B.choose (M - r0) : ℝ)) *
        exp (-((r : ℝ) - (A : ℝ) * (M : ℝ) / ((A : ℝ) + (B : ℝ))) ^ 2 / (8 * (A : ℝ))) := by
  let p (i : ℕ) : ℝ := (A.choose i : ℝ) * (B.choose (M - i) : ℝ)
  change p r ≤ 2 * p r0 * _
  have hp_nn : ∀ i, 0 ≤ p i := fun i => by positivity
  by_cases hp0 : p r0 = 0
  · have hpr : p r = 0 := le_antisymm ((hmax r hr).trans hp0.le) (hp_nn r)
    rw [hpr, hp0]; positivity
  have hp0_pos : 0 < p r0 := lt_of_le_of_ne (hp_nn r0) (Ne.symm hp0)
  have hr0_A : r0 ≤ A := by
    by_contra hgt; exact hp0 (by simp [p, Nat.choose_eq_zero_of_lt (by omega : A < r0)])
  have hr0_B : M - r0 ≤ B := by
    by_contra hgt; exact hp0 (by simp [p, Nat.choose_eq_zero_of_lt (by omega : B < M - r0)])
  have hA_pos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hAB_pos : (0 : ℝ) < (A : ℝ) + (B : ℝ) := by positivity
  have hr0_AR : (r0 : ℝ) ≤ A := by exact_mod_cast hr0_A
  have hr0_MR : (r0 : ℝ) ≤ M := by exact_mod_cast hr0
  have hBMr0_R : (M : ℝ) - r0 ≤ B := by
    have hR : ((M - r0 : ℕ) : ℝ) ≤ B := by exact_mod_cast hr0_B
    rwa [Nat.cast_sub hr0] at hR
  have hmode_R : ((A : ℝ) - r0) * ((M : ℝ) - r0) ≤
      ((r0 : ℝ) + 1) * ((B : ℝ) - M + r0 + 1) := by
    by_cases hlt : r0 < M
    · have hst := hypergeom_step_eq A B M r0 hlt
      have hle : p (r0 + 1) ≤ p r0 := hmax (r0 + 1) (by omega)
      have hden : 0 ≤ ((r0 : ℝ) + 1) * ((B : ℝ) - M + r0 + 1) := by nlinarith
      nlinarith
    · have heq : r0 = M := by omega
      subst heq; simp only [sub_self, mul_zero]; nlinarith
  have hmode_L : 0 < r0 → (r0 : ℝ) * ((B : ℝ) - M + r0) ≤
      ((A : ℝ) - r0 + 1) * ((M : ℝ) - r0 + 1) := by
    intro hr0_pos
    have hst := hypergeom_step_eq A B M (r0 - 1) (by omega)
    have hle : p (r0 - 1) ≤ p r0 := hmax (r0 - 1) (by omega)
    have hcast : ((r0 - 1 : ℕ) : ℝ) + 1 = r0 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r0)]; push_cast; ring
    have hidx : r0 - 1 + 1 = r0 := by omega
    rw [hidx] at hst
    have hst' : p r0 * ((r0 : ℝ) * ((B : ℝ) - M + r0)) =
        p (r0 - 1) * (((A : ℝ) - r0 + 1) * ((M : ℝ) - r0 + 1)) := by
      have h1 : (A : ℝ) - ((r0 - 1 : ℕ) : ℝ) = (A : ℝ) - r0 + 1 := by linarith
      have h2 : (M : ℝ) - ((r0 - 1 : ℕ) : ℝ) = (M : ℝ) - r0 + 1 := by linarith
      have h3 : (B : ℝ) - M + ((r0 - 1 : ℕ) : ℝ) + 1 = (B : ℝ) - M + r0 := by linarith
      rw [hcast, h1, h2, h3] at hst; exact hst
    have hnum : 0 ≤ ((A : ℝ) - r0 + 1) * ((M : ℝ) - r0 + 1) := by nlinarith
    nlinarith
  let μ : ℝ := (A : ℝ) * (M : ℝ) / ((A : ℝ) + (B : ℝ))
  have hmu_dist : |(r0 : ℝ) - μ| ≤ 1 := by
    rw [abs_le]
    have hupper : (r0 : ℝ) ≤ μ + 1 := by
      by_cases hr0_pos : 0 < r0
      · have hL := hmode_L hr0_pos
        have hr0_ge1 : (1 : ℝ) ≤ r0 := by exact_mod_cast hr0_pos
        have hlin : ((A : ℝ) + B) * r0 ≤ (A : ℝ) * M + ((A : ℝ) + B) := by nlinarith
        have hdiv : (r0 : ℝ) ≤ ((A : ℝ) * M + ((A : ℝ) + B)) / ((A : ℝ) + B) :=
          (le_div_iff₀ hAB_pos).mpr (by linarith)
        have heq : ((A : ℝ) * M + ((A : ℝ) + B)) / ((A : ℝ) + B) = μ + 1 := by
          dsimp [μ]; field_simp [hAB_pos.ne']
        linarith
      · have : r0 = 0 := by omega
        subst this; simp only [Nat.cast_zero]; positivity
    have hlower : μ - 1 ≤ (r0 : ℝ) := by
      by_cases hlt : r0 < M
      · have hltR : (r0 : ℝ) + 1 ≤ M := by exact_mod_cast hlt
        have hlin : (A : ℝ) * M - ((A : ℝ) + B) ≤ ((A : ℝ) + B) * r0 := by nlinarith [hmode_R]
        have hdiv : ((A : ℝ) * M - ((A : ℝ) + B)) / ((A : ℝ) + B) ≤ r0 :=
          (div_le_iff₀ hAB_pos).mpr (by linarith)
        have heq : ((A : ℝ) * M - ((A : ℝ) + B)) / ((A : ℝ) + B) = μ - 1 := by
          dsimp [μ]; field_simp [hAB_pos.ne']
        linarith
      · have heq : r0 = M := by omega
        have hmu_le : μ ≤ M := by
          dsimp [μ]; rw [div_le_iff₀ hAB_pos]; nlinarith
        have hr0M : (r0 : ℝ) = M := by exact_mod_cast heq
        linarith
    exact ⟨by linarith, by linarith⟩
  have hdecay_R : ∀ s : ℕ, r0 + s ≤ M →
      p (r0 + s) ≤ p r0 * exp (-(s : ℝ) * ((s : ℝ) - 1) / (2 * A)) := by
    intro s
    induction s with
    | zero => intro _; simp
    | succ s ih =>
      intro hsM
      by_cases hzero : p (r0 + (s + 1)) = 0
      · rw [hzero]; positivity
      have hleA : r0 + (s + 1) ≤ A := by
        by_contra hgt
        exact hzero (by simp [p, Nat.choose_eq_zero_of_lt (by omega : A < r0 + (s + 1))])
      have hst := hypergeom_step_eq A B M (r0 + s) (by omega)
      have hidx : r0 + (s + 1) = (r0 + s) + 1 := by omega
      rw [hidx]
      let d : ℝ := (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - M + ((r0 + s : ℕ) : ℝ) + 1)
      let num : ℝ := ((A : ℝ) - ((r0 + s : ℕ) : ℝ)) * ((M : ℝ) - ((r0 + s : ℕ) : ℝ))
      have hd_pos : 0 < d := by
        have h1 : 0 < ((r0 + s : ℕ) : ℝ) + 1 := by positivity
        have h2 : 0 < (B : ℝ) - M + ((r0 + s : ℕ) : ℝ) + 1 := by push_cast; linarith
        exact mul_pos h1 h2
      have hd_ub : d ≤ (A : ℝ) * ((A : ℝ) + B + 2) := by
        have h1 : ((r0 + s : ℕ) : ℝ) + 1 ≤ A := by exact_mod_cast hleA
        have h2 : (B : ℝ) - M + ((r0 + s : ℕ) : ℝ) + 1 ≤ B := by
          have hR : ((r0 + s : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast hsM
          linarith
        have h3 : (B : ℝ) ≤ (A : ℝ) + B + 2 := by linarith
        have h2' : (B : ℝ) - M + ((r0 + s : ℕ) : ℝ) + 1 ≤ (A : ℝ) + B + 2 := by linarith
        exact mul_le_mul h1 h2' (by push_cast; linarith) hA_pos.le
      have hdiff : (s : ℝ) * ((A : ℝ) + B + 2) ≤ d - num := by
        have halg : d - num = (((r0 : ℝ) + 1) * ((B : ℝ) - M + r0 + 1) -
            ((A : ℝ) - r0) * ((M : ℝ) - r0)) + (s : ℝ) * ((A : ℝ) + B + 2) := by
          dsimp [d, num]; push_cast; ring
        linarith [hmode_R, halg]
      have hnum_le : num ≤ exp (-(s : ℝ) / A) * d := by
        have hmul : ((s : ℝ) / A) * d ≤ (s : ℝ) * ((A : ℝ) + B + 2) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hA_pos]
          calc (s : ℝ) * d ≤ (s : ℝ) * ((A : ℝ) * ((A : ℝ) + B + 2)) :=
                mL hd_ub (Nat.cast_nonneg _)
            _ = (s : ℝ) * ((A : ℝ) + B + 2) * A := by ring
        have h1 : num ≤ (1 - (s : ℝ) / A) * d := by linarith
        have h2 : 1 - (s : ℝ) / A ≤ exp (-(s : ℝ) / A) := by
          have hexp := add_one_le_exp (-(s : ℝ) / A)
          have hneg : -(s : ℝ) / A = -((s : ℝ) / A) := neg_div _ _
          linarith [hexp, hneg]
        have h3 := mR h2 hd_pos.le
        linarith
      have hstep_le : p ((r0 + s) + 1) ≤ p (r0 + s) * exp (-(s : ℝ) / A) := by
        apply le_of_mul_le_mul_right _ hd_pos
        calc p ((r0 + s) + 1) * d = p (r0 + s) * num := hst
          _ ≤ p (r0 + s) * (exp (-(s : ℝ) / A) * d) :=
              mL hnum_le (hp_nn _)
          _ = p (r0 + s) * exp (-(s : ℝ) / A) * d := by ring
      calc p ((r0 + s) + 1) ≤ p (r0 + s) * exp (-(s : ℝ) / A) := hstep_le
        _ ≤ (p r0 * exp (-(s : ℝ) * ((s : ℝ) - 1) / (2 * A))) * exp (-(s : ℝ) / A) :=
            mR (ih (by omega)) (exp_pos _).le
        _ = p r0 * exp (-((s + 1 : ℕ) : ℝ) * (((s + 1 : ℕ) : ℝ) - 1) / (2 * A)) := by
            rw [mul_assoc, ← exp_add]
            congr 2; push_cast; field_simp [hA_pos.ne']; ring
  have hdecay_L : ∀ s : ℕ, s ≤ r0 →
      p (r0 - s) ≤ p r0 * exp (-(s : ℝ) * ((s : ℝ) - 1) / (2 * A)) := by
    intro s
    induction s with
    | zero => intro _; simp
    | succ s ih =>
      intro hs
      by_cases hzero : p (r0 - (s + 1)) = 0
      · rw [hzero]; positivity
      have hleB : M - (r0 - (s + 1)) ≤ B := by
        by_contra hgt
        exact hzero (by simp [p, Nat.choose_eq_zero_of_lt (by omega : B < M - (r0 - (s + 1)))])
      let t := r0 - (s + 1)
      have ht1 : t + 1 = r0 - s := by omega
      have hst := hypergeom_step_eq A B M t (by omega)
      rw [ht1] at hst
      let d : ℝ := ((t : ℝ) + 1) * ((B : ℝ) - M + (t : ℝ) + 1)
      let num : ℝ := ((A : ℝ) - t) * ((M : ℝ) - t)
      have hnum_pos : 0 < num := by
        have htA : (t : ℝ) + 1 ≤ A := by exact_mod_cast (show t + 1 ≤ A by omega)
        have htM : (t : ℝ) + 1 ≤ M := by exact_mod_cast (show t + 1 ≤ M by omega)
        exact mul_pos (by linarith) (by linarith)
      have hnum_ub : num ≤ (A : ℝ) * ((A : ℝ) + B + 2) := by
        have h1 : (A : ℝ) - t ≤ A := by linarith [Nat.cast_nonneg (α := ℝ) t]
        have h2 : (M : ℝ) - t ≤ B := by
          have hR : ((M - t : ℕ) : ℝ) ≤ B := by exact_mod_cast hleB
          rwa [Nat.cast_sub (by omega : t ≤ M)] at hR
        have h2' : (M : ℝ) - t ≤ (A : ℝ) + B + 2 := by linarith
        have htM : (t : ℝ) ≤ M := by exact_mod_cast (show t ≤ M by omega)
        exact mul_le_mul h1 h2' (by linarith) hA_pos.le
      have hdiff : (s : ℝ) * ((A : ℝ) + B + 2) ≤ num - d := by
        have hL := hmode_L (by omega)
        have htR : (t : ℝ) = (r0 : ℝ) - s - 1 := by
          have hnat : t + (s + 1) = r0 := by omega
          have hR : (t : ℝ) + ((s : ℝ) + 1) = r0 := by exact_mod_cast hnat
          linarith
        have halg : num - d = (((A : ℝ) - r0 + 1) * ((M : ℝ) - r0 + 1) -
            (r0 : ℝ) * ((B : ℝ) - M + r0)) + (s : ℝ) * ((A : ℝ) + B + 2) := by
          dsimp [d, num]; rw [htR]; ring
        linarith [hL, halg]
      have hd_le : d ≤ exp (-(s : ℝ) / A) * num := by
        have hmul : ((s : ℝ) / A) * num ≤ (s : ℝ) * ((A : ℝ) + B + 2) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hA_pos]
          calc (s : ℝ) * num ≤ (s : ℝ) * ((A : ℝ) * ((A : ℝ) + B + 2)) :=
                mL hnum_ub (Nat.cast_nonneg _)
            _ = (s : ℝ) * ((A : ℝ) + B + 2) * A := by ring
        have h1 : d ≤ (1 - (s : ℝ) / A) * num := by linarith
        have h2 : 1 - (s : ℝ) / A ≤ exp (-(s : ℝ) / A) := by
          have hexp := add_one_le_exp (-(s : ℝ) / A)
          have hneg : -(s : ℝ) / A = -((s : ℝ) / A) := neg_div _ _
          linarith [hexp, hneg]
        have h3 := mR h2 hnum_pos.le
        linarith
      have hstep_le : p t ≤ p (r0 - s) * exp (-(s : ℝ) / A) := by
        apply le_of_mul_le_mul_right _ hnum_pos
        calc p t * num = p (r0 - s) * d := hst.symm
          _ ≤ p (r0 - s) * (exp (-(s : ℝ) / A) * num) :=
              mL hd_le (hp_nn _)
          _ = p (r0 - s) * exp (-(s : ℝ) / A) * num := by ring
      calc p t ≤ p (r0 - s) * exp (-(s : ℝ) / A) := hstep_le
        _ ≤ (p r0 * exp (-(s : ℝ) * ((s : ℝ) - 1) / (2 * A))) * exp (-(s : ℝ) / A) :=
            mR (ih (by omega)) (exp_pos _).le
        _ = p r0 * exp (-((s + 1 : ℕ) : ℝ) * (((s + 1 : ℕ) : ℝ) - 1) / (2 * A)) := by
            rw [mul_assoc, ← exp_add]
            congr 2; push_cast; field_simp [hA_pos.ne']; ring
  have hcore : p r ≤ p r0 *
      exp (-|((r : ℝ) - r0)| * (|((r : ℝ) - r0)| - 1) / (2 * A)) := by
    by_cases hle : r0 ≤ r
    · have h1 := hdecay_R (r - r0) (by omega)
      rw [Nat.add_sub_of_le hle] at h1
      have hcast : ((r - r0 : ℕ) : ℝ) = |(r : ℝ) - r0| := by
        rw [Nat.cast_sub hle, abs_of_nonneg (by
          have : (r0 : ℝ) ≤ r := by exact_mod_cast hle
          linarith)]
      rwa [hcast] at h1
    · have hlt : r ≤ r0 := by omega
      have h1 := hdecay_L (r0 - r) (by omega)
      rw [Nat.sub_sub_self hlt] at h1
      have hcast : ((r0 - r : ℕ) : ℝ) = |(r : ℝ) - r0| := by
        rw [Nat.cast_sub hlt, abs_of_nonpos (by
          have : (r : ℝ) ≤ r0 := by exact_mod_cast hlt
          linarith)]
        ring
      rwa [hcast] at h1
  have hexp_le :
      exp (-|((r : ℝ) - r0)| * (|((r : ℝ) - r0)| - 1) / (2 * A)) ≤
      2 * exp (-((r : ℝ) - μ) ^ 2 / (8 * A)) := by
    have hsq1 : ((r : ℝ) - μ) ^ 2 ≤ 2 * ((r : ℝ) - r0) ^ 2 + 2 := by
      have h1 : ((r0 : ℝ) - μ) ^ 2 ≤ 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg ((r0 : ℝ) - μ)]
      nlinarith [sq_nonneg (((r : ℝ) - r0) - ((r0 : ℝ) - μ))]
    have hsq2 : -|((r : ℝ) - r0)| * (|((r : ℝ) - r0)| - 1) / (2 * A) ≤
        1 / (2 * A) + (-((r : ℝ) - μ) ^ 2 / (8 * A)) := by
      have habs : |((r : ℝ) - r0)| ^ 2 = ((r : ℝ) - r0) ^ 2 := sq_abs _
      have hq : 0 ≤ (|((r : ℝ) - r0)| - 1) ^ 2 := sq_nonneg _
      have hnum : -4 * |((r : ℝ) - r0)| * (|((r : ℝ) - r0)| - 1) ≤ 4 - ((r : ℝ) - μ) ^ 2 := by
        nlinarith [habs, hq, hsq1]
      have hden : (0 : ℝ) < 8 * A := by positivity
      have hstep : -|((r : ℝ) - r0)| * (|((r : ℝ) - r0)| - 1) / (2 * A) =
          (-4 * |((r : ℝ) - r0)| * (|((r : ℝ) - r0)| - 1)) / (8 * A) := by
        field_simp [hA_pos.ne']; ring
      have hstep2 : 1 / (2 * A) + (-((r : ℝ) - μ) ^ 2 / (8 * A)) =
          (4 - ((r : ℝ) - μ) ^ 2) / (8 * A) := by
        field_simp [hA_pos.ne']; ring
      rw [hstep, hstep2]
      exact dR hnum hden.le
    have h12 : exp (1 / (2 * (A : ℝ))) ≤ 2 := by
      have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
      have hle : 1 / (2 * (A : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      exact (exp_le_exp.mpr hle).trans exp_half_lt_two.le
    calc exp (-|((r : ℝ) - r0)| * (|((r : ℝ) - r0)| - 1) / (2 * A))
        ≤ exp (1 / (2 * A) + (-((r : ℝ) - μ) ^ 2 / (8 * A))) := exp_le_exp.mpr hsq2
      _ = exp (1 / (2 * A)) * exp (-((r : ℝ) - μ) ^ 2 / (8 * A)) := exp_add _ _
      _ ≤ 2 * exp (-((r : ℝ) - μ) ^ 2 / (8 * A)) :=
          mR h12 (exp_pos _).le
  calc p r ≤ p r0 * exp (-|((r : ℝ) - r0)| * (|((r : ℝ) - r0)| - 1) / (2 * A)) := hcore
    _ ≤ p r0 * (2 * exp (-((r : ℝ) - μ) ^ 2 / (8 * A))) :=
        mL hexp_le (hp_nn r0)
    _ = 2 * p r0 * exp (-((r : ℝ) - μ) ^ 2 / (8 * A)) := by ring

private lemma hypergeom_universal_tail (A B M r : ℕ) (hA : 1 ≤ A) (hr : r ≤ M) :
    (A.choose r : ℝ) * (B.choose (M - r) : ℝ) ≤
      2 * ((A + B).choose M : ℝ) *
        exp (-((r : ℝ) - (A : ℝ) * (M : ℝ) / ((A : ℝ) + (B : ℝ))) ^ 2 / (8 * (A : ℝ))) := by
  let p (i : ℕ) : ℝ := (A.choose i : ℝ) * (B.choose (M - i) : ℝ)
  have hne : (range (M + 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨r0, hr0_mem, hr0_max⟩ := exists_max_image (range (M + 1)) p hne
  have hr0_le : r0 ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hr0_mem)
  have hmax : ∀ i ≤ M, p i ≤ p r0 := fun i hi => hr0_max i (mem_range.mpr (by omega))
  have hdecay := hypergeom_mode_decay A B M r0 r hA hr0_le hr hmax
  have hpr0_le : p r0 ≤ ((A + B).choose M : ℝ) := by
    rw [← sum_hypergeom A B M]
    exact single_le_sum (fun i _ => by positivity) hr0_mem
  have hexp_nn : 0 ≤ exp (-((r : ℝ) - (A : ℝ) * (M : ℝ) / ((A : ℝ) + (B : ℝ))) ^ 2 / (8 * (A : ℝ))) :=
    (exp_pos _).le
  calc p r ≤ 2 * p r0 * _ := hdecay
    _ ≤ 2 * ((A + B).choose M : ℝ) * _ := by nlinarith

set_option maxHeartbeats 800000 in
private lemma hypergeom_peak_bound (k A B M r : ℕ)
    (hk : 1600 ≤ k) (hA1 : k ≤ A) (hA2 : A ≤ 2 * k)
    (hB1 : k ≤ B) (hB2 : B ≤ 2 * k)
    (hM1 : k ≤ M) (hM2 : M + k / 4 ≤ A + B) (hr : r ≤ M) :
    (A.choose r : ℝ) * (B.choose (M - r) : ℝ) ≤
      (80 / sqrt k) * ((A + B).choose M : ℝ) := by
  let p (i : ℕ) : ℝ := (A.choose i : ℝ) * (B.choose (M - i) : ℝ)
  have hp_nonneg : ∀ i, 0 ≤ p i := fun i => by positivity
  have hne : (range (M + 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨r0, hr0_mem, hr0_max⟩ := exists_max_image (range (M + 1)) p hne
  have hr0_le : r0 ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hr0_mem)
  suffices hmode : p r0 ≤ (80 / sqrt k) * ((A + B).choose M : ℝ) by
    exact (hr0_max r (mem_range.mpr (by omega))).trans hmode
  by_cases hp0 : p r0 = 0
  · rw [hp0]; positivity
  have hp0_pos : 0 < p r0 := lt_of_le_of_ne (hp_nonneg r0) (Ne.symm hp0)
  have hr0_A : r0 ≤ A := by
    by_contra hgt; exact hp0 (by simp [p, Nat.choose_eq_zero_of_lt (by omega : A < r0)])
  have hr0_B : M - r0 ≤ B := by
    by_contra hgt; exact hp0 (by simp [p, Nat.choose_eq_zero_of_lt (by omega : B < M - r0)])
  have hmode_upper : ((r0 : ℝ) + 1) * ((B : ℝ) - M + r0 + 1) ≥
      ((A : ℝ) - r0) * ((M : ℝ) - r0) := by
    by_cases hrm : r0 < M
    · have hstep := hypergeom_step_eq A B M r0 hrm
      have hle : p (r0 + 1) ≤ p r0 := hr0_max (r0 + 1) (mem_range.mpr (by omega))
      have hden : 0 ≤ ((r0 : ℝ) + 1) * ((B : ℝ) - M + r0 + 1) := by
        have hR : ((M - r0 : ℕ) : ℝ) ≤ B := by exact_mod_cast hr0_B
        rw [Nat.cast_sub hr0_le] at hR; nlinarith
      nlinarith
    · have hr0M : r0 = M := by omega
      subst hr0M
      rw [sub_self, mul_zero, show (B : ℝ) - r0 + r0 + 1 = (B : ℝ) + 1 by ring]; positivity
  have hmode_lower : (r0 : ℝ) * ((B : ℝ) - M + r0) ≤
      ((A : ℝ) - r0 + 1) * ((M : ℝ) - r0 + 1) := by
    by_cases hr0_pos : 0 < r0
    · have hstep := hypergeom_step_eq A B M (r0 - 1) (by omega)
      have hle : p (r0 - 1) ≤ p r0 := hr0_max (r0 - 1) (mem_range.mpr (by omega))
      have hcast : ((r0 - 1 : ℕ) : ℝ) + 1 = r0 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r0)]; push_cast; ring
      have hidx : r0 - 1 + 1 = r0 := by omega
      rw [hidx] at hstep
      have hst' : p r0 * ((r0 : ℝ) * ((B : ℝ) - M + r0)) =
          p (r0 - 1) * (((A : ℝ) - r0 + 1) * ((M : ℝ) - r0 + 1)) := by
        have h1 : (A : ℝ) - ((r0 - 1 : ℕ) : ℝ) = (A : ℝ) - r0 + 1 := by linarith
        have h2 : (M : ℝ) - ((r0 - 1 : ℕ) : ℝ) = (M : ℝ) - r0 + 1 := by linarith
        have h3 : (B : ℝ) - M + ((r0 - 1 : ℕ) : ℝ) + 1 = (B : ℝ) - M + r0 := by linarith
        rw [hcast, h1, h2, h3] at hstep; exact hstep
      have hnum : 0 ≤ ((A : ℝ) - r0 + 1) * ((M : ℝ) - r0 + 1) := by
        have h1 : (r0 : ℝ) ≤ A := by exact_mod_cast hr0_A
        have h2 : (r0 : ℝ) ≤ M := by exact_mod_cast hr0_le
        nlinarith
      nlinarith
    · have : r0 = 0 := by omega
      subst this; simp; positivity
  have hA1R : (k : ℝ) ≤ A := by exact_mod_cast hA1
  have hA2R : (A : ℝ) ≤ 2 * k := by exact_mod_cast hA2
  have hB1R : (k : ℝ) ≤ B := by exact_mod_cast hB1
  have hB2R : (B : ℝ) ≤ 2 * k := by exact_mod_cast hB2
  have hM1R : (k : ℝ) ≤ M := by exact_mod_cast hM1
  have hkR : (1600 : ℝ) ≤ k := by exact_mod_cast hk
  have hM2R : (M : ℝ) + (k : ℝ) / 5 ≤ (A : ℝ) + B := by
    have hdiv : (k : ℝ) / 5 ≤ ((k / 4 : ℕ) : ℝ) := by
      have : 4 * (k / 4) + 3 ≥ k := by omega
      have hR : (4 : ℝ) * ((k / 4 : ℕ) : ℝ) + 3 ≥ k := by exact_mod_cast this
      linarith
    have hR : (M : ℝ) + ((k / 4 : ℕ) : ℝ) ≤ (A : ℝ) + B := by exact_mod_cast hM2
    linarith
  have hr0_lb : (k : ℝ) / 5 ≤ r0 := by nlinarith
  have hMr0_lb : (k : ℝ) / 5 ≤ (M : ℝ) - r0 := by nlinarith
  have hBMr0_lb : (k : ℝ) / 25 ≤ (B : ℝ) - M + r0 := by nlinarith
  let t : ℕ := ⌊sqrt k / 40⌋₊
  have ht_le : (t : ℝ) ≤ sqrt k / 40 := Nat.floor_le (by positivity)
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr (by positivity)
  have hsq_ge : 40 ≤ sqrt k := by
    rw [le_sqrt (by norm_num) (by positivity)]; linarith
  have ht_sq : (t : ℝ) ^ 2 ≤ (k : ℝ) / 1600 := by
    calc (t : ℝ) ^ 2 ≤ (sqrt k / 40) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) ht_le 2
      _ = (k : ℝ) / 1600 := by rw [div_pow, sq_sqrt (by positivity)]; norm_num
  have ht_lin : (t : ℝ) ≤ (k : ℝ) / 1600 := by
    have : sqrt k ≤ (k : ℝ) / 40 := by
      have := mL hsq_ge hsq_pos.le
      rw [mul_self_sqrt (by positivity)] at this; linarith
    linarith
  have hstep_drop : ∀ s ≤ t, (1 - 700 * (s : ℝ) ^ 2 / (k : ℝ)) * p r0 ≤ p (r0 + s) := by
    intro s hs
    induction s with
    | zero => simp
    | succ s ih =>
      have hs_le : s ≤ t := by omega
      have ihs := ih hs_le
      have hrm : r0 + s < M := by
        have : (s : ℝ) ≤ t := by exact_mod_cast hs_le
        have : (r0 : ℝ) + s < M := by linarith
        exact_mod_cast this
      have hstep := hypergeom_step_eq A B M (r0 + s) hrm
      have hden_pos : 0 < (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - M + ((r0 + s : ℕ) : ℝ) + 1) := by
        push_cast; nlinarith
      have hs_t : ((s + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast hs
      have hden_lb : (k : ℝ) ^ 2 / 125 ≤
          (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - M + ((r0 + s : ℕ) : ℝ) + 1) := by
        push_cast; nlinarith
      have hdiff_k :
          (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - M + ((r0 + s : ℕ) : ℝ) + 1) -
          ((A : ℝ) - ((r0 + s : ℕ) : ℝ)) * ((M : ℝ) - ((r0 + s : ℕ) : ℝ)) ≤
          5 * ((s : ℝ) + 1) * k := by
        have hdiff_ub :
            (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - M + ((r0 + s : ℕ) : ℝ) + 1) -
            ((A : ℝ) - ((r0 + s : ℕ) : ℝ)) * ((M : ℝ) - ((r0 + s : ℕ) : ℝ)) ≤
            ((s : ℝ) + 1) * ((A : ℝ) + B + 2) := by
          push_cast; nlinarith [hmode_lower]
        nlinarith
      have hratio : (1 - 700 * ((s : ℝ) + 1) / k) * p (r0 + s) ≤ p (r0 + (s + 1)) := by
        rw [show r0 + (s + 1) = (r0 + s) + 1 by omega]
        apply le_of_mul_le_mul_right _ hden_pos
        rw [mul_assoc, hstep]
        have hk_pos : (0 : ℝ) < k := by positivity
        have h700 : 5 * ((s : ℝ) + 1) * k ≤
            (700 * ((s : ℝ) + 1) / k) *
              ((((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - M + ((r0 + s : ℕ) : ℝ) + 1)) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hk_pos]
          have hmul := mL hden_lb (show 0 ≤ 700 * ((s : ℝ) + 1) by positivity)
          have h56 : 5 * ((s : ℝ) + 1) * k * k ≤ 700 * ((s : ℝ) + 1) * ((k : ℝ) ^ 2 / 125) := by
            have : 0 ≤ ((s : ℝ) + 1) * (k : ℝ) ^ 2 := by positivity
            linarith
          linarith
        have hcoef : (1 - 700 * ((s : ℝ) + 1) / k) *
            ((((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - M + ((r0 + s : ℕ) : ℝ) + 1)) ≤
            ((A : ℝ) - ((r0 + s : ℕ) : ℝ)) * ((M : ℝ) - ((r0 + s : ℕ) : ℝ)) := by linarith
        have hmul2 := mL hcoef (hp_nonneg (r0 + s))
        linarith
      have hk_pos : (0 : ℝ) < k := by positivity
      have h1_nn : 0 ≤ 1 - 700 * ((s : ℝ) + 1) / k := by
        rw [sub_nonneg, div_le_iff₀ hk_pos]; push_cast at hs_t; linarith
      have hprod_le : (1 - 700 * (((s + 1 : ℕ) : ℝ)) ^ 2 / k) ≤
          (1 - 700 * ((s : ℝ) + 1) / k) * (1 - 700 * (s : ℝ) ^ 2 / k) := by
        push_cast
        have hpos_prod : 0 ≤ 700 * ((s : ℝ) + 1) / k * (700 * (s : ℝ) ^ 2 / k) := by positivity
        have hsum_sq : 700 * ((s : ℝ) + 1) / k + 700 * (s : ℝ) ^ 2 / k ≤
            700 * ((s : ℝ) + 1) ^ 2 / k := by
          rw [← add_div, div_le_div_iff_of_pos_right hk_pos]
          have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
          nlinarith [hs0]
        have hexp : (1 - 700 * ((s : ℝ) + 1) / k) * (1 - 700 * (s : ℝ) ^ 2 / k) =
            1 - (700 * ((s : ℝ) + 1) / k + 700 * (s : ℝ) ^ 2 / k) +
              700 * ((s : ℝ) + 1) / k * (700 * (s : ℝ) ^ 2 / k) := by ring
        linarith [hpos_prod, hsum_sq, hexp]
      calc (1 - 700 * (((s + 1 : ℕ) : ℝ)) ^ 2 / k) * p r0
          ≤ (1 - 700 * ((s : ℝ) + 1) / k) * ((1 - 700 * (s : ℝ) ^ 2 / k) * p r0) := by
            have := mR hprod_le (hp_nonneg r0)
            linarith
        _ ≤ (1 - 700 * ((s : ℝ) + 1) / k) * p (r0 + s) := mL ihs h1_nn
        _ ≤ p (r0 + (s + 1)) := hratio
  have hsum_lb : ((t + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * p r0) ≤ ((A + B).choose M : ℝ) := by
    have hsub : (range (t + 1)).image (fun s => r0 + s) ⊆ range (M + 1) := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hx
      have hs_le : s ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hs)
      have : (s : ℝ) ≤ t := by exact_mod_cast hs_le
      have : (r0 : ℝ) + s < (M : ℝ) + 1 := by linarith
      exact mem_range.mpr (by exact_mod_cast this)
    rw [← sum_hypergeom A B M]
    calc ((t + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * p r0)
        = ∑ _s ∈ range (t + 1), ((1 / 2 : ℝ) * p r0) := by simp
      _ ≤ ∑ s ∈ range (t + 1), p (r0 + s) := by
          apply sum_le_sum; intro s hs
          have hs_le : s ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hs)
          have hsq_s : (s : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hs_le) 2
          have hk_pos : (0 : ℝ) < k := by positivity
          have h12 : (1 / 2 : ℝ) ≤ 1 - 700 * (s : ℝ) ^ 2 / k := by
            have hfrac : 700 * (s : ℝ) ^ 2 / k ≤ 1 / 2 := by
              rw [div_le_iff₀ hk_pos]; linarith
            linarith
          exact (mR h12 (hp_nonneg r0)).trans (hstep_drop s hs_le)
      _ = ∑ x ∈ (range (t + 1)).image (fun s => r0 + s), p x := by
          rw [sum_image (fun a _ b _ h => by omega)]
      _ ≤ ∑ x ∈ range (M + 1), p x :=
          sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hp_nonneg x)
  have ht1_lb : sqrt k / 40 ≤ ((t + 1 : ℕ) : ℝ) := by
    push_cast; exact (Nat.lt_floor_add_one _).le
  have hkey : (sqrt k / 80) * p r0 ≤ ((A + B).choose M : ℝ) := by
    have h1 : (sqrt k / 40) * ((1 / 2 : ℝ) * p r0) ≤
        ((t + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * p r0) :=
      mR ht1_lb (by positivity)
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hsq_pos]
  linarith

private lemma hypergeom_peak_tail_bound (k A B M r : ℕ)
    (hk : 1600 ≤ k) (hA1 : k ≤ A) (hA2 : A ≤ 2 * k)
    (hB1 : k ≤ B) (hB2 : B ≤ 2 * k)
    (hM1 : k ≤ M) (hM2 : M + k / 4 ≤ A + B) (hr : r ≤ M) :
    (A.choose r : ℝ) * (B.choose (M - r) : ℝ) ≤
      (160 / sqrt k) * ((A + B).choose M : ℝ) *
        exp (-((r : ℝ) - (A : ℝ) * (M : ℝ) / ((A : ℝ) + (B : ℝ))) ^ 2 / (16 * (k : ℝ))) := by
  let p (i : ℕ) : ℝ := (A.choose i : ℝ) * (B.choose (M - i) : ℝ)
  have hne : (range (M + 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨r0, hr0_mem, hr0_max⟩ := exists_max_image (range (M + 1)) p hne
  have hr0_le : r0 ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hr0_mem)
  have hmax : ∀ i ≤ M, p i ≤ p r0 := fun i hi => hr0_max i (mem_range.mpr (by omega))
  have hdecay := hypergeom_mode_decay A B M r0 r (by omega) hr0_le hr hmax
  have hpeak := hypergeom_peak_bound k A B M r0 hk hA1 hA2 hB1 hB2 hM1 hM2 hr0_le
  have hexp_mono :
      exp (-((r : ℝ) - (A : ℝ) * M / ((A : ℝ) + B)) ^ 2 / (8 * A)) ≤
      exp (-((r : ℝ) - (A : ℝ) * M / ((A : ℝ) + B)) ^ 2 / (16 * k)) := by
    apply exp_le_exp.mpr
    have hA2R : (A : ℝ) ≤ 2 * k := by exact_mod_cast hA2
    have hA_pos : (0 : ℝ) < 8 * A := by
      have : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
      linarith
    have hsq : 0 ≤ ((r : ℝ) - (A : ℝ) * M / ((A : ℝ) + B)) ^ 2 := sq_nonneg _
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hsq hA_pos (by linarith)
  calc p r ≤ 2 * p r0 * exp (-((r : ℝ) - (A : ℝ) * M / ((A : ℝ) + B)) ^ 2 / (8 * A)) := hdecay
    _ ≤ 2 * ((80 / sqrt k) * ((A + B).choose M : ℝ)) *
          exp (-((r : ℝ) - (A : ℝ) * M / ((A : ℝ) + B)) ^ 2 / (8 * A)) :=
        mR
          (mL hpeak (by norm_num : (0 : ℝ) ≤ 2)) (exp_pos _).le
    _ ≤ 2 * ((80 / sqrt k) * ((A + B).choose M : ℝ)) *
          exp (-((r : ℝ) - (A : ℝ) * M / ((A : ℝ) + B)) ^ 2 / (16 * k)) :=
        mL hexp_mono (by positivity)
    _ = (160 / sqrt k) * ((A + B).choose M : ℝ) *
          exp (-((r : ℝ) - (A : ℝ) * M / ((A : ℝ) + B)) ^ 2 / (16 * k)) := by ring

private lemma sum_exp_sq_geom_bound (M : ℕ) {α : ℝ} (hα : 0 < α) :
    ∑ t ∈ range M, exp (-α * (t : ℝ) ^ 2) ≤ 3 + 2 / sqrt α := by
  let u : ℝ := 2 * sqrt α
  have hu : 0 < u := by dsimp [u]; positivity
  let q : ℝ := exp (-u)
  have hq_pos : 0 < q := exp_pos _
  have hq_lt1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hterm : ∀ t : ℕ, exp (-α * (t : ℝ) ^ 2) ≤ exp 1 * q ^ t := by
    intro t
    rw [← exp_nat_mul, ← exp_add]
    apply exp_le_exp.mpr
    have hsq : 0 ≤ (sqrt α * (t : ℝ) - 1) ^ 2 := sq_nonneg _
    have hsq_α : sqrt α ^ 2 = α := sq_sqrt hα.le
    dsimp [u]
    nlinarith [hsq, hsq_α]
  have hgeom : ∑ t ∈ range M, q ^ t ≤ 1 / (1 - q) := by
    rw [geom_sum_eq hq_lt1.ne]
    have hden : 0 < 1 - q := by linarith
    have hnum : 0 ≤ q ^ M := pow_nonneg hq_pos.le M
    have heq : (q ^ M - 1) / (q - 1) = (1 - q ^ M) / (1 - q) := by
      field_simp [show q - 1 ≠ 0 by linarith, hden.ne']; ring
    rw [heq]
    exact dR (by linarith) hden.le
  have h1mq : 1 / (1 - q) ≤ 1 + 1 / u := by
    have hexp_ge : 1 + u ≤ exp u := by linarith [add_one_le_exp u]
    have hq_le : q ≤ 1 / (1 + u) := by
      dsimp [q]
      rw [exp_neg, one_div]
      exact inv_anti₀ (by positivity) hexp_ge
    have hden1 : 0 < 1 - q := by linarith
    have hsub : u / (1 + u) ≤ 1 - q := by
      have : 1 - 1 / (1 + u) = u / (1 + u) := by field_simp [show (1 + u : ℝ) ≠ 0 by positivity]; ring
      linarith
    have hinv : 1 / (1 - q) ≤ (1 + u) / u := by
      rw [div_le_div_iff₀ hden1 hu]
      have := (div_le_iff₀ (show (0 : ℝ) < 1 + u by positivity)).mp hsub
      linarith
    have heq : (1 + u) / u = 1 + 1 / u := by field_simp [hu.ne']; ring
    linarith
  have he : exp 1 ≤ 3 := (lt_trans exp_one_lt_d9 (by norm_num)).le
  calc ∑ t ∈ range M, exp (-α * (t : ℝ) ^ 2)
      ≤ ∑ t ∈ range M, exp 1 * q ^ t := sum_le_sum fun t _ => hterm t
    _ = exp 1 * ∑ t ∈ range M, q ^ t := (mul_sum _ _ _).symm
    _ ≤ exp 1 * (1 + 1 / u) := mL (hgeom.trans h1mq) (exp_pos _).le
    _ ≤ 3 * (1 + 1 / u) := mR he (by positivity)
    _ = 3 + 3 / (2 * sqrt α) := by dsimp [u]; ring
    _ ≤ 3 + 2 / sqrt α := by
        have hsq : 0 < sqrt α := sqrt_pos.mpr hα
        have : 3 / (2 * sqrt α) ≤ 2 / sqrt α := by
          rw [div_le_div_iff₀ (by positivity) hsq]; linarith
        linarith

private lemma sum_exp_sq_of_step_ge_one (N : ℕ) (x : ℕ → ℝ) {α : ℝ} (hα : 0 < α)
    (hstep : ∀ i, x i + 1 ≤ x (i + 1)) :
    ∑ i ∈ range N, exp (-α * (x i) ^ 2) ≤ 6 + 4 / sqrt α := by
  have hshift : ∀ a d : ℕ, x a + (d : ℝ) ≤ x (a + d) := by
    intro a d
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 := hstep (a + d)
      rw [show a + (d + 1) = (a + d) + 1 by omega]
      push_cast; linarith
  let Spos := (range N).filter (fun i => 0 ≤ x i)
  let Sneg := (range N).filter (fun i => ¬ (0 ≤ x i))
  have hsplit : ∑ i ∈ range N, exp (-α * (x i) ^ 2) =
      (∑ i ∈ Spos, exp (-α * (x i) ^ 2)) + (∑ i ∈ Sneg, exp (-α * (x i) ^ 2)) :=
    (sum_filter_add_sum_filter_not (range N) (fun i => 0 ≤ x i) _).symm
  have hpos_le : ∑ i ∈ Spos, exp (-α * (x i) ^ 2) ≤ 3 + 2 / sqrt α := by
    by_cases hne : Spos.Nonempty
    · let i0 := Spos.min' hne
      have hi0_mem : i0 ∈ Spos := min'_mem Spos hne
      have hi0_nn : 0 ≤ x i0 := (mem_filter.mp hi0_mem).2
      have hsub : Spos.image (fun i => i - i0) ⊆ range N := by
        intro d hd
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hd
        have hiN : i < N := mem_range.mp (mem_filter.mp hi).1
        exact mem_range.mpr (by omega)
      calc ∑ i ∈ Spos, exp (-α * (x i) ^ 2)
          ≤ ∑ i ∈ Spos, exp (-α * ((i - i0 : ℕ) : ℝ) ^ 2) := by
            apply sum_le_sum; intro i hi
            have hle : i0 ≤ i := min'_le Spos i hi
            have hxi : ((i - i0 : ℕ) : ℝ) ≤ x i := by
              have h1 := hshift i0 (i - i0)
              rw [Nat.add_sub_of_le hle] at h1; linarith
            apply exp_le_exp.mpr
            have hsq : ((i - i0 : ℕ) : ℝ) ^ 2 ≤ (x i) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hxi 2
            nlinarith
        _ = ∑ d ∈ Spos.image (fun i => i - i0), exp (-α * (d : ℝ) ^ 2) := by
            rw [sum_image]
            intro a ha b hb hab
            have ha' : i0 ≤ a := min'_le Spos a ha
            have hb' : i0 ≤ b := min'_le Spos b hb
            dsimp only at hab; omega
        _ ≤ ∑ d ∈ range N, exp (-α * (d : ℝ) ^ 2) :=
            sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (exp_pos _).le)
        _ ≤ 3 + 2 / sqrt α := sum_exp_sq_geom_bound N hα
    · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]; positivity
  have hneg_le : ∑ i ∈ Sneg, exp (-α * (x i) ^ 2) ≤ 3 + 2 / sqrt α := by
    by_cases hne : Sneg.Nonempty
    · let i1 := Sneg.max' hne
      have hi1_mem : i1 ∈ Sneg := max'_mem Sneg hne
      have hi1_lt : x i1 < 0 := not_le.mp (mem_filter.mp hi1_mem).2
      have hsub : Sneg.image (fun i => i1 - i) ⊆ range N := by
        intro d hd
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hd
        have hi1N : i1 < N := mem_range.mp (mem_filter.mp hi1_mem).1
        exact mem_range.mpr (by omega)
      calc ∑ i ∈ Sneg, exp (-α * (x i) ^ 2)
          ≤ ∑ i ∈ Sneg, exp (-α * ((i1 - i : ℕ) : ℝ) ^ 2) := by
            apply sum_le_sum; intro i hi
            have hle : i ≤ i1 := le_max' Sneg i hi
            have hxi : ((i1 - i : ℕ) : ℝ) ≤ -(x i) := by
              have h1 := hshift i (i1 - i)
              rw [Nat.add_sub_of_le hle] at h1; linarith
            apply exp_le_exp.mpr
            have hsq : ((i1 - i : ℕ) : ℝ) ^ 2 ≤ (x i) ^ 2 := by
              have := pow_le_pow_left₀ (Nat.cast_nonneg _) hxi 2
              simpa only [neg_sq] using this
            nlinarith
        _ = ∑ d ∈ Sneg.image (fun i => i1 - i), exp (-α * (d : ℝ) ^ 2) := by
            rw [sum_image]
            intro a ha b hb hab
            have ha' : a ≤ i1 := le_max' Sneg a ha
            have hb' : b ≤ i1 := le_max' Sneg b hb
            dsimp only at hab; omega
        _ ≤ ∑ d ∈ range N, exp (-α * (d : ℝ) ^ 2) :=
            sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (exp_pos _).le)
        _ ≤ 3 + 2 / sqrt α := sum_exp_sq_geom_bound N hα
    · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]; positivity
  have htot : (3 + 2 / sqrt α) + (3 + 2 / sqrt α) = 6 + 4 / sqrt α := by ring
  linarith [hsplit, hpos_le, hneg_le, htot]

private lemma cnt_append_two_le (v : List Bool) (x y : Bool) :
    cnt (v ++ [x, y]) ≤ cnt v + 1 := by
  have h1 : v ++ [x, y] = (v ++ [x]) ++ [y] := by simp
  rw [h1, cnt_append_singleton, cnt_append_singleton]
  have hlast : (v ++ [x]).getLast? = some x := by simp
  rw [hlast]
  cases x <;> cases y <;> simp <;> split_ifs <;> omega

private lemma cnt_take_step2 (w : List Bool) (j : ℕ) :
    cnt (w.take (j + 2)) ≤ cnt (w.take j) + 1 := by
  by_cases h1 : j + 1 < w.length
  · have heq : w.take (j + 2) = w.take j ++ [w[j], w[j + 1]] := by
      have ha : w.take (j + 1) = w.take j ++ [w[j]] := List.take_succ_eq_append_getElem (by omega)
      have hb : w.take (j + 2) = w.take (j + 1) ++ [w[j + 1]] := List.take_succ_eq_append_getElem h1
      rw [hb, ha, List.append_assoc]; rfl
    rw [heq]; exact cnt_append_two_le (w.take j) w[j] w[j + 1]
  · by_cases h0 : j < w.length
    · have heq : w.take (j + 2) = w.take j ++ [w[j]] := by
        have hlen : w.length = j + 1 := by omega
        calc w.take (j + 2) = w := List.take_of_length_le (by omega)
          _ = w.take (j + 1) := by rw [← hlen, List.take_length]
          _ = w.take j ++ [w[j]] := List.take_succ_eq_append_getElem h0
      rw [heq, cnt_append_singleton]; split_ifs <;> omega
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]; omega

private lemma choose_nearby_le (N m : ℕ) (hN : m + 1 ≤ N) (hgap : 5 * (N - m) ≥ N) :
    ((N.choose (m - 1) : ℝ) ≤ 10 * (N.choose m : ℝ)) ∧
    (((N + 1).choose (m - 1) : ℝ) ≤ 60 * (N.choose m : ℝ)) := by
  have h1 : (N.choose (m - 1) : ℝ) ≤ 10 * (N.choose m : ℝ) := by
    cases m with
    | zero => simp
    | succ m' =>
      have hst := choose_step_real N m'
      have hden : (0 : ℝ) < (N : ℝ) - m' := by
        have : m' < N := by omega
        have hR : (m' : ℝ) < N := by exact_mod_cast this
        linarith
      have hratio : ((m' : ℝ) + 1) ≤ 10 * ((N : ℝ) - m') := by
        have hR : 5 * ((N - (m' + 1) : ℕ) : ℝ) ≥ N := by exact_mod_cast hgap
        rw [Nat.cast_sub (by omega : m' + 1 ≤ N)] at hR
        push_cast at hR; linarith
      have hch_nn : (0 : ℝ) ≤ N.choose (m' + 1) := Nat.cast_nonneg _
      have hch_nn2 : (0 : ℝ) ≤ N.choose m' := Nat.cast_nonneg _
      simp only [Nat.add_sub_cancel]
      nlinarith
  have h2 : ((N + 1).choose (m - 1) : ℝ) ≤ 60 * (N.choose m : ℝ) := by
    have hcm := choose_succ_mul_real N (m - 1)
    have hden : (0 : ℝ) < (N : ℝ) + 1 - (m - 1 : ℕ) := by
      have : m - 1 < N + 1 := by omega
      have hR : ((m - 1 : ℕ) : ℝ) < (N : ℝ) + 1 := by exact_mod_cast this
      linarith
    have hratio : (N : ℝ) + 1 ≤ 6 * ((N : ℝ) + 1 - (m - 1 : ℕ)) := by
      have hR : 5 * ((N - m : ℕ) : ℝ) ≥ N := by exact_mod_cast hgap
      rw [Nat.cast_sub (by omega : m ≤ N)] at hR
      have hle : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
      linarith
    have hstep : ((N + 1).choose (m - 1) : ℝ) ≤ 6 * (N.choose (m - 1) : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) ((N + 1).choose (m - 1))]
    linarith
  exact ⟨h1, h2⟩

set_option maxHeartbeats 800000 in
private lemma diag_sum_A_sq_le (k : ℕ) (w : List Bool)
    (hk : 10000 ≤ k)
    (hm : |((w.length : ℕ) : ℝ) - 2 * k| ≤ (k : ℝ) / 20)
    (hf : |((cnt w : ℕ) : ℝ) - 2 * (k : ℝ) / 3| ≤ (k : ℝ) / 20) :
    ∑ j ∈ range w.length, (A_val k w j) ^ 2 ≤
      (4e12 : ℝ) / (k : ℝ) ^ ((3 : ℝ) / 2) * ((F (2 * k + 1) w : ℕ) : ℝ) ^ 2 := by
  let m := w.length
  let f := cnt w
  let Bw : ℝ := (F (2 * k + 1) w : ℝ)
  have hBw_nn : 0 ≤ Bw := Nat.cast_nonneg _
  have hkR : (10000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hm_lo : (39 : ℝ) / 20 * k ≤ m := by linarith [(abs_le.mp hm).1]
  have hm_hi : (m : ℝ) ≤ (41 : ℝ) / 20 * k := by linarith [(abs_le.mp hm).2]
  have hf_lo : (37 : ℝ) / 60 * k ≤ f := by linarith [(abs_le.mp hf).1]
  have hf_hi : (f : ℝ) ≤ (43 : ℝ) / 60 * k := by linarith [(abs_le.mp hf).2]
  have hm_ge1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hN_gap : 5 * (2 * k + 1 + f - m) ≥ 2 * k + 1 + f := by
    have h1 : (2 * k + 1 + f : ℝ) ≤ 5 * ((2 * k + 1 + f : ℝ) - m) := by linarith
    have hle : m ≤ 2 * k + 1 + f := by
      have : (m : ℝ) ≤ (2 * k + 1 + f : ℝ) := by linarith
      exact_mod_cast this
    have hR : ((2 * k + 1 + f : ℕ) : ℝ) ≤ 5 * (((2 * k + 1 + f - m : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hle]; push_cast; linarith
    exact_mod_cast hR
  let Ntot : ℝ := (2 * k + 1 + f : ℕ)
  have hNtot_pos : 0 < Ntot := by dsimp [Ntot]; push_cast; linarith
  let hseq (j : ℕ) : ℝ :=
    (j : ℝ) - ((k + 1 + cnt (w.take j) : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ) / Ntot
  have hpt : ∀ j ∈ range m,
      (A_val k w j) ^ 2 ≤
        (16 * 38400 ^ 2 * 2 / (k : ℝ) ^ 2) * Bw ^ 2 *
          exp (-(hseq j) ^ 2 / (32 * k)) := by
    intro j hj
    have hj_lt : j < m := mem_range.mp hj
    by_cases hwt : w[j]? = some true
    · rw [A_val_eq_deltaK k w j hj_lt hwt]
      let c1 := cnt (w.take j)
      let c2 := cnt (w.drop (j + 1))
      have hsplit_w : w = w.take j ++ [true] ++ w.drop (j + 1) := by
        have h1 : w = w.take j ++ w.drop j := (List.take_append_drop j w).symm
        have hjv : w[j] = true := by
          have := List.getElem?_eq_getElem hj_lt; rw [hwt] at this; exact Option.some.inj this.symm
        have h2 : w.drop j = true :: w.drop (j + 1) := by
          rw [List.drop_eq_getElem_cons hj_lt, hjv]
        conv_lhs => rw [h1, h2]
        simp
      have hcf : f = c1 + c2 + if (w.take j).getLast? = some false then 1 else 0 := by
        change cnt w = _; conv_lhs => rw [hsplit_w]
        exact cnt_append_true_append (w.take j) (w.drop (j + 1))
      have hcf_bounds : c1 + c2 ≤ f ∧ f ≤ c1 + c2 + 1 := by
        split_ifs at hcf <;> omega
      have hc1_le : c1 ≤ f := by omega
      have hc2_le : c2 ≤ f := by omega
      let A' := k + c1 + 1
      let B' := k + c2 + 1
      let M' := m - 1
      have hdelta : deltaK k c1 c2 j (m - 1 - j) =
          (((m - 1 - j : ℕ) * (A' : ℝ) - (j : ℝ) * (B' : ℝ)) / ((A' : ℝ) * (B' : ℝ))) *
            ((A'.choose j : ℝ) * (B'.choose (M' - j) : ℝ)) := by
        unfold deltaK
        have := deltaK_exact_identity (k + c1) (k + c2) j (m - 1 - j)
        have hA' : k + 1 + c1 = A' := by omega
        have hB' : k + 1 + c2 = B' := by omega
        have hA'R : ((k + c1 : ℕ) : ℝ) + 1 = A' := by push_cast [A']; ring
        have hB'R : ((k + c2 : ℕ) : ℝ) + 1 = B' := by push_cast [B']; ring
        rw [hA', hB']
        simpa only [A', B', M', hA'R, hB'R, show k + c1 + 1 = A' by omega,
          show k + c2 + 1 = B' by omega] using this
      let μj : ℝ := (A' : ℝ) * M' / ((A' : ℝ) + B')
      have hA'B'_pos : (0 : ℝ) < (A' : ℝ) + B' := by positivity
      have hnum_eq : ((m - 1 - j : ℕ) : ℝ) * A' - (j : ℝ) * B' =
          -((A' : ℝ) + B') * ((j : ℝ) - μj) := by
        have hsub : ((m - 1 - j : ℕ) : ℝ) = (M' : ℝ) - j := by
          dsimp [M']; rw [Nat.cast_sub (by omega : j ≤ m - 1)]
        rw [hsub]
        dsimp [μj]; field_simp [hA'B'_pos.ne']; ring
      have hAB_ratio : ((A' : ℝ) + B') / ((A' : ℝ) * B') ≤ 4 / k := by
        have hA'_lo : (k : ℝ) ≤ A' := by exact_mod_cast (show k ≤ A' by omega)
        have hB'_lo : (k : ℝ) ≤ B' := by exact_mod_cast (show k ≤ B' by omega)
        have hA'_hi : (A' : ℝ) ≤ 2 * k := by
          have : (c1 : ℝ) ≤ f := by exact_mod_cast hc1_le
          dsimp [A']; push_cast; linarith
        have hB'_hi : (B' : ℝ) ≤ 2 * k := by
          have : (c2 : ℝ) ≤ f := by exact_mod_cast hc2_le
          dsimp [B']; push_cast; linarith
        rw [div_le_div_iff₀ (by positivity) hk_pos]
        nlinarith
      have hA'1 : k ≤ A' := by omega
      have hA'2 : A' ≤ 2 * k := by
        have : (A' : ℝ) ≤ 2 * k := by
          have : (c1 : ℝ) ≤ f := by exact_mod_cast hc1_le
          dsimp [A']; push_cast; linarith
        exact_mod_cast this
      have hB'1 : k ≤ B' := by omega
      have hB'2 : B' ≤ 2 * k := by
        have : (B' : ℝ) ≤ 2 * k := by
          have : (c2 : ℝ) ≤ f := by exact_mod_cast hc2_le
          dsimp [B']; push_cast; linarith
        exact_mod_cast this
      have hM'1 : k ≤ M' := by
        have : (k : ℝ) ≤ M' := by dsimp [M']; rw [Nat.cast_sub hm_ge1]; push_cast; linarith
        exact_mod_cast this
      have hM'2 : M' + k / 4 ≤ A' + B' := by
        have h1 : 2 * k + 1 + f ≤ A' + B' := by omega
        have hdiv : ((k / 4 : ℕ) : ℝ) ≤ (k : ℝ) / 4 := by
          have : 4 * (k / 4) ≤ k := Nat.mul_div_le k 4
          have hR : (4 : ℝ) * ((k / 4 : ℕ) : ℝ) ≤ k := by exact_mod_cast this
          linarith
        have hR : (M' : ℝ) + ((k / 4 : ℕ) : ℝ) ≤ (2 * k + 1 + f : ℕ) := by
          dsimp [M']; rw [Nat.cast_sub hm_ge1]; push_cast; linarith
        have hnat : M' + k / 4 ≤ 2 * k + 1 + f := by exact_mod_cast hR
        omega
      have hptail := hypergeom_peak_tail_bound k A' B' M' j (by omega) hA'1 hA'2 hB'1 hB'2 hM'1 hM'2 (by omega)
      have hchoose_le : (((A' + B').choose M' : ℕ) : ℝ) ≤ 60 * Bw := by
        have hN_le : m + 1 ≤ 2 * k + 1 + f := by
          have : (m : ℝ) + 1 ≤ (2 * k + 1 + f : ℕ) := by push_cast; linarith
          exact_mod_cast this
        have hnear := choose_nearby_le (2 * k + 1 + f) m hN_le hN_gap
        have hAB_cases : A' + B' = 2 * k + 1 + f ∨ A' + B' = (2 * k + 1 + f) + 1 := by omega
        change (((A' + B').choose (m - 1) : ℕ) : ℝ) ≤ 60 * (((2 * k + 1 + f).choose m : ℕ) : ℝ)
        rcases hAB_cases with h | h
        · rw [h]; linarith [hnear.1, Nat.cast_nonneg (α := ℝ) ((2 * k + 1 + f).choose m)]
        · rw [h]; exact hnear.2
      have habs_delta : |deltaK k c1 c2 j (m - 1 - j)| ≤
          (38400 / (k * sqrt k)) * Bw * |(j : ℝ) - μj| *
            exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) := by
        rw [hdelta, hnum_eq, abs_mul, abs_div, abs_mul, abs_neg]
        have h1 : |((A' : ℝ) + B')| = (A' : ℝ) + B' := abs_of_pos hA'B'_pos
        have h2 : |((A' : ℝ) * B')| = (A' : ℝ) * B' := abs_of_pos (by positivity)
        have h3 : |(A'.choose j : ℝ) * (B'.choose (M' - j) : ℝ)| =
            (A'.choose j : ℝ) * (B'.choose (M' - j) : ℝ) := abs_of_nonneg (by positivity)
        rw [h1, h2, h3]
        have hfac : ((A' : ℝ) + B') * |(j : ℝ) - μj| / ((A' : ℝ) * B') ≤
            (4 / k) * |(j : ℝ) - μj| := by
          rw [mul_div_right_comm]
          exact mR hAB_ratio (abs_nonneg _)
        have htail2 : (A'.choose j : ℝ) * (B'.choose (M' - j) : ℝ) ≤
            (160 / sqrt k) * (60 * Bw) * exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) := by
          have hnn : 0 ≤ (160 / sqrt k) * exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) := by positivity
          calc (A'.choose j : ℝ) * (B'.choose (M' - j) : ℝ)
              ≤ (160 / sqrt k) * (((A' + B').choose M' : ℕ) : ℝ) *
                  exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) := hptail
            _ ≤ (160 / sqrt k) * (60 * Bw) * exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) := by
                have := mL hchoose_le hnn
                linarith
        calc ((A' : ℝ) + B') * |(j : ℝ) - μj| / ((A' : ℝ) * B') *
              ((A'.choose j : ℝ) * (B'.choose (M' - j) : ℝ))
            ≤ ((4 / k) * |(j : ℝ) - μj|) *
              ((160 / sqrt k) * (60 * Bw) * exp (-((j : ℝ) - μj) ^ 2 / (16 * k))) :=
              mul_le_mul hfac htail2 (by positivity) (by positivity)
          _ = (38400 / (k * sqrt k)) * Bw * |(j : ℝ) - μj| *
              exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) := by ring
      have hsq_delta : (deltaK k c1 c2 j (m - 1 - j)) ^ 2 ≤
          (16 * 38400 ^ 2 / (k : ℝ) ^ 2) * Bw ^ 2 *
            exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) := by
        have hsq1 : (deltaK k c1 c2 j (m - 1 - j)) ^ 2 ≤
            ((38400 / (k * sqrt k)) * Bw * |(j : ℝ) - μj| *
              exp (-((j : ℝ) - μj) ^ 2 / (16 * k))) ^ 2 := by
          rw [← sq_abs (deltaK k c1 c2 j (m - 1 - j))]
          exact pow_le_pow_left₀ (abs_nonneg _) habs_delta 2
        have hu_le : ((j : ℝ) - μj) ^ 2 / (16 * k) *
            exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) ≤ 1 := by
          let u := ((j : ℝ) - μj) ^ 2 / (16 * k)
          have hu_nn : 0 ≤ u := by dsimp [u]; positivity
          have hexp : u ≤ exp u := by linarith [add_one_le_exp u]
          have hmul := mR hexp (exp_pos (-u)).le
          rw [← exp_add, add_neg_cancel, exp_zero] at hmul
          simpa [u, neg_div] using hmul
        have hexp2 : (exp (-((j : ℝ) - μj) ^ 2 / (16 * k))) ^ 2 =
            exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) *
            exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) := sq _
        have hksq : ((k : ℝ) * sqrt k) ^ 2 = (k : ℝ) ^ 3 := by
          rw [mul_pow, sq_sqrt hk_pos.le]; ring
        have hrw : ((38400 / (k * sqrt k)) * Bw * |(j : ℝ) - μj| *
              exp (-((j : ℝ) - μj) ^ 2 / (16 * k))) ^ 2 =
            (16 * 38400 ^ 2 / (k : ℝ) ^ 2) * Bw ^ 2 *
              (((j : ℝ) - μj) ^ 2 / (16 * k) * exp (-((j : ℝ) - μj) ^ 2 / (16 * k))) *
              exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) := by
          rw [mul_pow, mul_pow, mul_pow, div_pow, hksq, sq_abs, hexp2]
          field_simp [hk_pos.ne']
        rw [hrw] at hsq1
        have hnn : 0 ≤ (16 * 38400 ^ 2 / (k : ℝ) ^ 2) * Bw ^ 2 := by positivity
        have hmul1 : (16 * 38400 ^ 2 / (k : ℝ) ^ 2) * Bw ^ 2 *
            (((j : ℝ) - μj) ^ 2 / (16 * k) * exp (-((j : ℝ) - μj) ^ 2 / (16 * k))) ≤
            (16 * 38400 ^ 2 / (k : ℝ) ^ 2) * Bw ^ 2 * 1 :=
          mL hu_le hnn
        have hmul2 := mR hmul1 (exp_pos (-((j : ℝ) - μj) ^ 2 / (16 * k))).le
        linarith [hsq1, hmul2]
      have hmu_diff : |((j : ℝ) - μj) - hseq j| ≤ 1 := by
        have hdiff_eq : ((j : ℝ) - μj) - hseq j =
            (A' : ℝ) * M' * (((A' : ℝ) + B') - Ntot) / (Ntot * ((A' : ℝ) + B')) := by
          dsimp [hseq, μj]
          have hA'_eq : ((k + 1 + c1 : ℕ) : ℝ) = A' := by push_cast [A']; ring
          rw [hA'_eq]
          field_simp [hNtot_pos.ne', hA'B'_pos.ne']; ring
        rw [hdiff_eq, abs_div, abs_of_pos (mul_pos hNtot_pos hA'B'_pos), div_le_one (mul_pos hNtot_pos hA'B'_pos)]
        have hAB_N : |((A' : ℝ) + B') - Ntot| ≤ 1 := by
          have hcases : A' + B' = 2 * k + 1 + f ∨ A' + B' = 2 * k + 1 + f + 1 := by omega
          rcases hcases with h | h
          · have hR : ((A' + B' : ℕ) : ℝ) = Ntot := by dsimp [Ntot]; exact_mod_cast h
            push_cast at hR; rw [hR, sub_self, abs_zero]; norm_num
          · have hR : ((A' + B' : ℕ) : ℝ) = Ntot + 1 := by
              have h1 : ((A' + B' : ℕ) : ℝ) = ((2 * k + 1 + f + 1 : ℕ) : ℝ) := by exact_mod_cast h
              dsimp [Ntot]; push_cast at h1 ⊢; linarith
            push_cast at hR; rw [hR, add_sub_cancel_left, abs_one]
        have hA'_le : (A' : ℝ) ≤ (A' : ℝ) + B' := by linarith
        have hM'_le : (M' : ℝ) ≤ Ntot := by
          dsimp [M', Ntot]; rw [Nat.cast_sub hm_ge1]; push_cast; linarith
        calc |(A' : ℝ) * M' * (((A' : ℝ) + B') - Ntot)|
            = (A' : ℝ) * M' * |((A' : ℝ) + B') - Ntot| := by
              rw [abs_mul, abs_of_nonneg (by positivity)]
          _ ≤ (A' : ℝ) * M' * 1 := mL hAB_N (by positivity)
          _ = (M' : ℝ) * (A' : ℝ) := by ring
          _ ≤ Ntot * ((A' : ℝ) + B') := mul_le_mul hM'_le hA'_le (by positivity) hNtot_pos.le
      have hexp_shift : exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) ≤
          2 * exp (-(hseq j) ^ 2 / (32 * k)) := by
        have hsq : (hseq j) ^ 2 / 2 - 1 ≤ ((j : ℝ) - μj) ^ 2 := by
          have h1 : (((j : ℝ) - μj) - hseq j) ^ 2 ≤ 1 := by
            rw [← sq_abs]; nlinarith [abs_nonneg (((j : ℝ) - μj) - hseq j)]
          nlinarith [sq_nonneg (2 * ((j : ℝ) - μj) - hseq j), h1]
        have h1 : -((j : ℝ) - μj) ^ 2 / (16 * k) ≤ 1 / (16 * k) + (-(hseq j) ^ 2 / (32 * k)) := by
          have hstep1 : -((j : ℝ) - μj) ^ 2 / (16 * k) = (-2 * ((j : ℝ) - μj) ^ 2) / (32 * k) := by
            field_simp [hk_pos.ne']; ring
          have hstep2 : 1 / (16 * k) + (-(hseq j) ^ 2 / (32 * k)) = (2 - (hseq j) ^ 2) / (32 * k) := by
            field_simp [hk_pos.ne']; ring
          rw [hstep1, hstep2]
          exact dR (by linarith) (by positivity)
        have he : exp (1 / (16 * (k : ℝ))) ≤ 2 :=
          (exp_le_exp.mpr (by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)).trans exp_half_lt_two.le
        calc exp (-((j : ℝ) - μj) ^ 2 / (16 * k))
            ≤ exp (1 / (16 * k) + (-(hseq j) ^ 2 / (32 * k))) := exp_le_exp.mpr h1
          _ = exp (1 / (16 * k)) * exp (-(hseq j) ^ 2 / (32 * k)) := exp_add _ _
          _ ≤ 2 * exp (-(hseq j) ^ 2 / (32 * k)) :=
              mR he (exp_pos _).le
      calc (deltaK k c1 c2 j (m - 1 - j)) ^ 2
          ≤ (16 * 38400 ^ 2 / (k : ℝ) ^ 2) * Bw ^ 2 * exp (-((j : ℝ) - μj) ^ 2 / (16 * k)) := hsq_delta
        _ ≤ (16 * 38400 ^ 2 / (k : ℝ) ^ 2) * Bw ^ 2 * (2 * exp (-(hseq j) ^ 2 / (32 * k))) :=
            mL hexp_shift (by positivity)
        _ = (16 * 38400 ^ 2 * 2 / (k : ℝ) ^ 2) * Bw ^ 2 * exp (-(hseq j) ^ 2 / (32 * k)) := by ring
    · simp only [A_val, P_val, hwt, ↓reduceIte, sub_self, sq, zero_mul]
      positivity
  have hstep2 : ∀ j : ℕ, hseq j + 1 ≤ hseq (j + 2) := by
    intro j
    have hc := cnt_take_step2 w j
    have hcR : ((cnt (w.take (j + 2)) : ℕ) : ℝ) ≤ (cnt (w.take j) : ℝ) + 1 := by
      exact_mod_cast hc
    have hratio : ((m - 1 : ℕ) : ℝ) / Ntot ≤ 1 := by
      rw [div_le_one hNtot_pos]
      dsimp [Ntot]; rw [Nat.cast_sub hm_ge1]; push_cast; linarith
    have hdiff : hseq (j + 2) - hseq j =
        2 - (((cnt (w.take (j + 2)) : ℕ) : ℝ) - cnt (w.take j)) * (((m - 1 : ℕ) : ℝ) / Ntot) := by
      dsimp [hseq]; push_cast; ring
    have hsub_le : (((cnt (w.take (j + 2)) : ℕ) : ℝ) - cnt (w.take j)) * (((m - 1 : ℕ) : ℝ) / Ntot) ≤ 1 := by
      have hnn : 0 ≤ ((m - 1 : ℕ) : ℝ) / Ntot := by positivity
      nlinarith
    linarith
  let α : ℝ := 1 / (32 * k)
  have hα : 0 < α := by positivity
  have hsum_gauss : ∑ j ∈ range m, exp (-(hseq j) ^ 2 / (32 * k)) ≤
      2 * (6 + 4 / sqrt α) := by
    have hrewrite : ∀ j, exp (-(hseq j) ^ 2 / (32 * k)) = exp (-α * (hseq j) ^ 2) := by
      intro j; dsimp [α]; congr 1; ring
    simp_rw [hrewrite]
    let Seven := (range m).filter (fun j => j % 2 = 0)
    let Sodd := (range m).filter (fun j => ¬ (j % 2 = 0))
    rw [← sum_filter_add_sum_filter_not (range m) (fun j => j % 2 = 0)]
    have heven : ∑ j ∈ Seven, exp (-α * (hseq j) ^ 2) ≤ 6 + 4 / sqrt α := by
      have hsub : Seven ⊆ (range (m + 1)).image (fun r => 2 * r) := by
        intro j hj
        have hj' := mem_filter.mp hj
        have hjlt := mem_range.mp hj'.1
        exact mem_image.mpr ⟨j / 2, mem_range.mpr (by omega), by omega⟩
      calc ∑ j ∈ Seven, exp (-α * (hseq j) ^ 2)
          ≤ ∑ j ∈ (range (m + 1)).image (fun r => 2 * r), exp (-α * (hseq j) ^ 2) :=
            sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (exp_pos _).le)
        _ = ∑ r ∈ range (m + 1), exp (-α * (hseq (2 * r)) ^ 2) := by
            rw [sum_image (fun a _ b _ h => by omega)]
        _ ≤ 6 + 4 / sqrt α :=
            sum_exp_sq_of_step_ge_one (m + 1) (fun r => hseq (2 * r)) hα
              (fun r => by simpa [Nat.mul_add] using hstep2 (2 * r))
    have hodd : ∑ j ∈ Sodd, exp (-α * (hseq j) ^ 2) ≤ 6 + 4 / sqrt α := by
      have hsub : Sodd ⊆ (range (m + 1)).image (fun r => 2 * r + 1) := by
        intro j hj
        have hj' := mem_filter.mp hj
        have hjlt := mem_range.mp hj'.1
        exact mem_image.mpr ⟨j / 2, mem_range.mpr (by omega), by omega⟩
      calc ∑ j ∈ Sodd, exp (-α * (hseq j) ^ 2)
          ≤ ∑ j ∈ (range (m + 1)).image (fun r => 2 * r + 1), exp (-α * (hseq j) ^ 2) :=
            sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (exp_pos _).le)
        _ = ∑ r ∈ range (m + 1), exp (-α * (hseq (2 * r + 1)) ^ 2) := by
            rw [sum_image (fun a _ b _ h => by omega)]
        _ ≤ 6 + 4 / sqrt α :=
            sum_exp_sq_of_step_ge_one (m + 1) (fun r => hseq (2 * r + 1)) hα
              (fun r => by
                have h2 := hstep2 (2 * r + 1)
                rwa [show 2 * (r + 1) + 1 = 2 * r + 1 + 2 by omega])
    linarith
  have hgauss_k : 2 * (6 + 4 / sqrt α) ≤ 60 * sqrt k := by
    have hsqα : 1 / sqrt α = sqrt (32 * k) := by
      dsimp [α]; rw [sqrt_div (by norm_num), sqrt_one, one_div_one_div]
    have hsq32 : sqrt (32 * (k : ℝ)) ≤ 6 * sqrt k := by
      rw [sqrt_mul (by norm_num)]
      have : sqrt 32 ≤ 6 := by rw [sqrt_le_left (by norm_num)]; norm_num
      nlinarith [sqrt_nonneg (k : ℝ)]
    have hsqk : 100 ≤ sqrt k := by rw [le_sqrt (by norm_num) hk_pos.le]; linarith
    have hdiv : 4 / sqrt α = 4 * sqrt (32 * k) := by
      rw [div_eq_mul_one_div, hsqα]
    linarith
  have hk32 : (k : ℝ) ^ ((3 : ℝ) / 2) = (k : ℝ) * sqrt k := by
    have h1 : ((3 : ℝ) / 2) = 1 + (1 / 2 : ℝ) := by norm_num
    rw [h1, rpow_add hk_pos, rpow_one, sqrt_eq_rpow]
  calc ∑ j ∈ range m, (A_val k w j) ^ 2
      ≤ ∑ j ∈ range m, (16 * 38400 ^ 2 * 2 / (k : ℝ) ^ 2) * Bw ^ 2 *
          exp (-(hseq j) ^ 2 / (32 * k)) := sum_le_sum hpt
    _ = (16 * 38400 ^ 2 * 2 / (k : ℝ) ^ 2) * Bw ^ 2 *
          ∑ j ∈ range m, exp (-(hseq j) ^ 2 / (32 * k)) := (mul_sum _ _ _).symm
    _ ≤ (16 * 38400 ^ 2 * 2 / (k : ℝ) ^ 2) * Bw ^ 2 * (60 * sqrt k) :=
        mL (hsum_gauss.trans hgauss_k) (by positivity)
    _ ≤ (4e12 : ℝ) / (k : ℝ) ^ ((3 : ℝ) / 2) * Bw ^ 2 := by
        rw [hk32]
        have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
        have hcoef : 16 * 38400 ^ 2 * 2 * 60 ≤ (4e12 : ℝ) := by norm_num
        have hsimp : (16 * 38400 ^ 2 * 2 / (k : ℝ) ^ 2) * Bw ^ 2 * (60 * sqrt k) =
            (16 * 38400 ^ 2 * 2 * 60) / (k * sqrt k) * Bw ^ 2 := by
          have hsq : sqrt k * sqrt k = k := mul_self_sqrt hk_pos.le
          field_simp [hk_pos.ne', hsq_pos.ne']
          nlinarith [hsq]
        rw [hsimp]
        exact mR
          (dR hcoef (by positivity)) (sq_nonneg Bw)

private lemma regime1_sum_le (m D0 : ℕ) (a : ℕ → ℝ) :
    |∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0), a j * a t| ≤
      (D0 : ℝ) * ∑ j ∈ range m, (a j) ^ 2 := by
  let S := ((range m) ×ˢ (range m)).filter (fun p => p.1 + 5 < p.2 ∧ p.2 ≤ p.1 + D0)
  have hS : (∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0), a j * a t) =
      ∑ p ∈ S, a p.1 * a p.2 := by
    rw [sum_filter, sum_product]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_filter]
  rw [hS]
  have h1 : |∑ p ∈ S, a p.1 * a p.2| ≤ ∑ p ∈ S, ((a p.1) ^ 2 + (a p.2) ^ 2) / 2 := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
    have hsq1 : 0 ≤ (a p.1 - a p.2) ^ 2 := sq_nonneg _
    have hsq2 : 0 ≤ (a p.1 + a p.2) ^ 2 := sq_nonneg _
    rw [abs_le]; constructor <;> nlinarith
  have h2 : ∑ p ∈ S, (a p.1) ^ 2 ≤ (D0 : ℝ) * ∑ j ∈ range m, (a j) ^ 2 := by
    rw [sum_filter, sum_product, mul_sum]
    apply sum_le_sum; intro j _
    dsimp only
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hcard : ((range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0)).card ≤ D0 := by
      have hsub : (range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0) ⊆
          (range D0).image (fun d => j + 1 + d) := by
        intro t ht
        have h' := (mem_filter.mp ht).2
        exact mem_image.mpr ⟨t - j - 1, mem_range.mpr (by omega), by omega⟩
      exact (card_le_card hsub).trans (card_image_le.trans (by simp))
    have hcardR : (((range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0)).card : ℝ) ≤ D0 := by
      exact_mod_cast hcard
    exact mR hcardR (sq_nonneg _)
  have h3 : ∑ p ∈ S, (a p.2) ^ 2 ≤ (D0 : ℝ) * ∑ t ∈ range m, (a t) ^ 2 := by
    rw [sum_filter, sum_product, sum_comm, mul_sum]
    apply sum_le_sum; intro t _
    dsimp only
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hcard : ((range m).filter (fun j => j + 5 < t ∧ t ≤ j + D0)).card ≤ D0 := by
      have hsub : (range m).filter (fun j => j + 5 < t ∧ t ≤ j + D0) ⊆
          (range D0).image (fun d => t - 1 - d) := by
        intro j hj
        have h' := (mem_filter.mp hj).2
        exact mem_image.mpr ⟨t - 1 - j, mem_range.mpr (by omega), by omega⟩
      exact (card_le_card hsub).trans (card_image_le.trans (by simp))
    have hcardR : (((range m).filter (fun j => j + 5 < t ∧ t ≤ j + D0)).card : ℝ) ≤ D0 := by
      exact_mod_cast hcard
    exact mR hcardR (sq_nonneg _)
  have h4 : ∑ p ∈ S, ((a p.1) ^ 2 + (a p.2) ^ 2) / 2 =
      (∑ p ∈ S, (a p.1) ^ 2) / 2 + (∑ p ∈ S, (a p.2) ^ 2) / 2 := by
    rw [← sum_div, sum_add_distrib, add_div]
  linarith

-- ============================================================================
-- Section 3: Two-sided Robbins Stirling and One-Binomial Master Formula
-- ============================================================================

private lemma stirling_log_factorial_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ log (Nat.factorial n : ℝ) - ((n : ℝ) * log n - n + (1 / 2) * log (2 * Real.pi * n)) ∧
    log (Nat.factorial n : ℝ) - ((n : ℝ) * log n - n + (1 / 2) * log (2 * Real.pi * n)) ≤
      1 / (12 * (n : ℝ)) := by
  have hn_ne : n ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpi_pos : (0 : ℝ) < Real.pi := pi_pos
  have hlog2pin : log (2 * Real.pi * n) = log (2 * Real.pi) + log n :=
    log_mul (by positivity) hn_pos.ne'
  have hlo : (n : ℝ) * log n - n + (1 / 2) * log (2 * Real.pi * n) ≤ log (Nat.factorial n : ℝ) := by
    have h := Stirling.le_log_factorial_stirling hn_ne
    rw [hlog2pin]; linarith
  have hhi : log (Nat.factorial n : ℝ) - ((n : ℝ) * log n - n + (1 / 2) * log (2 * Real.pi * n)) ≤
      1 / (12 * (n : ℝ)) := by
    let g (k : ℕ) : ℝ := log (Stirling.stirlingSeq (n + k))
    let h (k : ℕ) : ℝ := 1 / (12 * ((n + k : ℕ) : ℝ))
    have hstep : ∀ k : ℕ, g k - g (k + 1) ≤ h k - h (k + 1) := by
      intro k
      have hs := Stirling.log_stirlingSeq_sdiff_le (n + k)
      have hpos1 : (0 : ℝ) < ((n + k : ℕ) : ℝ) := by positivity
      have hpos2 : (0 : ℝ) < ((n + k : ℕ) : ℝ) + 1 := by positivity
      have halg : 1 / (12 * ((n + k : ℕ) : ℝ) * (((n + k : ℕ) : ℝ) + 1)) =
          1 / (12 * ((n + k : ℕ) : ℝ)) - 1 / (12 * (((n + k : ℕ) : ℝ) + 1)) := by
        field_simp [hpos1.ne', hpos2.ne']; ring
      have hcast : ((n + k + 1 : ℕ) : ℝ) = ((n + k : ℕ) : ℝ) + 1 := by push_cast; ring
      dsimp [g, h]
      rw [show n + (k + 1) = n + k + 1 by omega, hcast]
      linarith [hs, halg]
    have htele : ∀ m : ℕ, g 0 - 1 / (12 * (n : ℝ)) ≤ g m := by
      intro m
      have hsum : ∑ k ∈ range m, (g k - g (k + 1)) ≤ ∑ k ∈ range m, (h k - h (k + 1)) :=
        sum_le_sum fun k _ => hstep k
      rw [Finset.sum_range_sub' g m, Finset.sum_range_sub' h m] at hsum
      have hh0 : h 0 = 1 / (12 * (n : ℝ)) := by simp [h]
      have hhm : 0 ≤ h m := by dsimp [h]; positivity
      linarith
    have htend : Filter.Tendsto g atTop (nhds (log (sqrt Real.pi))) := by
      have h1 : Filter.Tendsto (fun m => Stirling.stirlingSeq (m + n)) atTop (nhds (sqrt Real.pi)) :=
        Stirling.tendsto_stirlingSeq_sqrt_pi.comp (Filter.tendsto_add_atTop_nat n)
      have h2 : Filter.Tendsto (fun m => Stirling.stirlingSeq (n + m)) atTop (nhds (sqrt Real.pi)) := by
        simpa [Nat.add_comm] using h1
      exact ((Real.continuousAt_log (by positivity : sqrt Real.pi ≠ 0)).tendsto).comp h2
    have hlim : g 0 - 1 / (12 * (n : ℝ)) ≤ log (sqrt Real.pi) :=
      ge_of_tendsto' htend htele
    have hform : g 0 = log (Nat.factorial n : ℝ) - (1 / 2) * log (2 * n) - n * (log n - 1) := by
      dsimp [g]; rw [Stirling.log_stirlingSeq_formula n]
      rw [log_div hn_pos.ne' (exp_pos 1).ne', log_exp]
    have hlogpi : log (sqrt Real.pi) = (1 / 2) * log Real.pi := by
      rw [Real.log_sqrt hpi_pos.le]; ring
    have hlog2n : log (2 * Real.pi * n) = log (2 * n) + log Real.pi := by
      rw [show (2 : ℝ) * Real.pi * n = (2 * n) * Real.pi by ring,
        log_mul (by positivity) hpi_pos.ne']
    rw [hform, hlogpi] at hlim
    rw [hlog2n]; linarith
  exact ⟨by linarith, hhi⟩

private lemma abs_log_one_add_sub_quad_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 * |x| ^ 3 := by
  have hneg : |-x| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hneg 2
  simp only [sum_range_succ, Finset.sum_range_zero, zero_add, pow_one, Nat.cast_zero,
    Nat.cast_one, zero_add, div_one, sub_neg_eq_add, abs_neg] at h
  have halg : (-x + (-x) ^ 2 / (1 + 1)) + log (1 + x) =
      log (1 + x) - (x - x ^ 2 / 2) := by ring
  rw [halg] at h
  have hden : 1 / 2 ≤ 1 - |x| := by linarith
  have hdiv : |x| ^ 3 / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - |x|)]
    nlinarith [pow_nonneg (abs_nonneg x) 3]
  exact h.trans hdiv

private lemma abs_log_one_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |log (1 + x)| ≤ 2 * |x| := by
  have hneg : |-x| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hneg 0
  simp only [Finset.range_zero, sum_empty, zero_add, sub_neg_eq_add, abs_neg, pow_one] at h
  have hdiv : |x| / (1 - |x|) ≤ 2 * |x| := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - |x|)]
    nlinarith [abs_nonneg x]
  exact h.trans hdiv

private lemma abs_exp_sub_one_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |exp x - 1| ≤ 2 * |x| := by
  have hx_lo : -(1 / 2 : ℝ) ≤ x := (abs_le.mp hx).1
  have hx_hi : x ≤ 1 / 2 := (abs_le.mp hx).2
  have hlo : -2 * |x| ≤ exp x - 1 := by
    have h1 := add_one_le_exp x
    have h2 : -|x| ≤ x := neg_abs_le x
    linarith [abs_nonneg x]
  have hhi : exp x - 1 ≤ 2 * |x| := by
    have h1 : 1 - x ≤ exp (-x) := by linarith [add_one_le_exp (-x)]
    have hpos : 0 < 1 - x := by linarith
    have hexp_le : exp x ≤ 1 / (1 - x) := by
      have hmul : (1 - x) * exp x ≤ 1 := by
        calc (1 - x) * exp x ≤ exp (-x) * exp x :=
              mR h1 (exp_pos x).le
          _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
      rwa [le_div_iff₀ hpos, mul_comm]
    have hfrac : 1 / (1 - x) - 1 ≤ 2 * |x| := by
      have heq : 1 / (1 - x) - 1 = x / (1 - x) := by field_simp [hpos.ne']; ring
      rw [heq, div_le_iff₀ hpos]
      have hx_le : x ≤ |x| := le_abs_self x
      nlinarith [abs_nonneg x]
    linarith
  exact abs_le.mpr ⟨by linarith, hhi⟩

private lemma abs_exp_sub_one_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |exp x - 1 - x| ≤ 2 * x ^ 2 := by
  by_cases hx0 : x = 0
  · subst hx0; simp
  let f (t : ℝ) : ℝ := exp t - 1 - t
  have hderiv : ∀ t : ℝ, HasDerivAt f (exp t - 1) t := fun t => by
    exact (((Real.hasDerivAt_exp t).sub_const (1 : ℝ)).sub (hasDerivAt_id t)).congr_deriv (by ring)
  have hcont : Continuous f := by fun_prop
  have hbound : ∀ c : ℝ, |c| ≤ |x| → |exp c - 1| ≤ 2 * |x| := fun c hc =>
    (abs_exp_sub_one_le (hc.trans hx)).trans (by linarith)
  rcases lt_or_gt_of_ne hx0 with hlt | hgt
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f (fun t => exp t - 1) hlt
      hcont.continuousOn (fun t _ => hderiv t)
    have hf0 : f 0 = 0 := by simp [f]
    have hfeq : f x = x * (exp c - 1) := by
      rw [hf0, zero_sub, eq_div_iff (by linarith : (0 : ℝ) - x ≠ 0)] at hslope
      linarith
    have hc_abs : |c| ≤ |x| := by
      rw [abs_of_neg hlt, abs_le]; constructor <;> linarith [hc.1, hc.2]
    rw [show exp x - 1 - x = f x from rfl, hfeq, abs_mul]
    calc |x| * |exp c - 1| ≤ |x| * (2 * |x|) :=
          mL (hbound c hc_abs) (abs_nonneg x)
      _ = 2 * x ^ 2 := by rw [← sq_abs x]; ring
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f (fun t => exp t - 1) hgt
      hcont.continuousOn (fun t _ => hderiv t)
    have hf0 : f 0 = 0 := by simp [f]
    have hfeq : f x = x * (exp c - 1) := by
      rw [hf0, sub_zero, sub_zero, eq_div_iff hgt.ne'] at hslope
      linarith
    have hc_abs : |c| ≤ |x| := by
      rw [abs_of_pos hgt, abs_le]; constructor <;> linarith [hc.1, hc.2]
    rw [show exp x - 1 - x = f x from rfl, hfeq, abs_mul]
    calc |x| * |exp c - 1| ≤ |x| * (2 * |x|) :=
          mL (hbound c hc_abs) (abs_nonneg x)
      _ = 2 * x ^ 2 := by rw [← sq_abs x]; ring

private lemma abs_add_mul_log_one_add_div_le {X0 x : ℝ} (hX : 0 < X0) (hx : |x| ≤ X0 / 2) :
    |(X0 + x) * log (1 + x / X0) - (x + x ^ 2 / (2 * X0))| ≤ 4 * |x| ^ 3 / X0 ^ 2 := by
  have ht : |x / X0| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hX, div_le_iff₀ hX]; linarith
  have hlog := abs_log_one_add_sub_quad_le ht
  have halg : (X0 + x) * log (1 + x / X0) - (x + x ^ 2 / (2 * X0)) =
      (X0 + x) * (log (1 + x / X0) - (x / X0 - (x / X0) ^ 2 / 2)) - x ^ 3 / (2 * X0 ^ 2) := by
    field_simp [hX.ne']; ring
  rw [halg]
  have h1 : |(X0 + x) * (log (1 + x / X0) - (x / X0 - (x / X0) ^ 2 / 2))| ≤
      3 * |x| ^ 3 / X0 ^ 2 := by
    rw [abs_mul]
    have hX_ub : |X0 + x| ≤ (3 / 2 : ℝ) * X0 := by
      rw [abs_le]; constructor <;> linarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
    have hcub : 2 * |x / X0| ^ 3 = 2 * |x| ^ 3 / X0 ^ 3 := by
      rw [abs_div, abs_of_pos hX, div_pow]; ring
    calc |X0 + x| * |log (1 + x / X0) - (x / X0 - (x / X0) ^ 2 / 2)|
        ≤ ((3 / 2 : ℝ) * X0) * (2 * |x / X0| ^ 3) :=
          mul_le_mul hX_ub hlog (abs_nonneg _) (by positivity)
      _ = ((3 / 2 : ℝ) * X0) * (2 * |x| ^ 3 / X0 ^ 3) := by rw [hcub]
      _ = 3 * |x| ^ 3 / X0 ^ 2 := by field_simp [hX.ne']
  have h2 : |x ^ 3 / (2 * X0 ^ 2)| ≤ |x| ^ 3 / X0 ^ 2 := by
    rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < 2 * X0 ^ 2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg (abs_nonneg x) 3, sq_nonneg X0]
  have htri := abs_sub ((X0 + x) * (log (1 + x / X0) - (x / X0 - (x / X0) ^ 2 / 2)))
    (x ^ 3 / (2 * X0 ^ 2))
  have hsum : 3 * |x| ^ 3 / X0 ^ 2 + |x| ^ 3 / X0 ^ 2 = 4 * |x| ^ 3 / X0 ^ 2 := by ring
  linarith [htri, h1, h2, hsum]

private noncomputable def logG (N0 R0 : ℝ) : ℝ :=
  N0 * log N0 - R0 * log R0 - (N0 - R0) * log (N0 - R0) -
    (1 / 2) * log (2 * Real.pi * R0 * (N0 - R0) / N0)

private lemma logG_double {N0 R0 : ℝ} (hR : 0 < R0) (hRN : R0 < N0) :
    logG (2 * N0) (2 * R0) =
      2 * logG N0 R0 + (1 / 2) * log (Real.pi * R0 * (N0 - R0) / N0) := by
  have hN : 0 < N0 := lt_trans hR hRN
  have hS : 0 < N0 - R0 := sub_pos.mpr hRN
  have hpi : 0 < Real.pi := pi_pos
  unfold logG
  have h1 : 2 * N0 - 2 * R0 = 2 * (N0 - R0) := by ring
  rw [h1]
  have hlN : log (2 * N0) = log 2 + log N0 := log_mul (by norm_num) hN.ne'
  have hlR : log (2 * R0) = log 2 + log R0 := log_mul (by norm_num) hR.ne'
  have hlS : log (2 * (N0 - R0)) = log 2 + log (N0 - R0) :=
    log_mul (by norm_num) hS.ne'
  have harg1 : 2 * Real.pi * (2 * R0) * (2 * (N0 - R0)) / (2 * N0) =
      2 * (2 * Real.pi * R0 * (N0 - R0) / N0) := by field_simp [hN.ne']
  have harg2 : 2 * Real.pi * R0 * (N0 - R0) / N0 =
      2 * (Real.pi * R0 * (N0 - R0) / N0) := by ring
  rw [hlN, hlR, hlS, harg1, log_mul (by norm_num) (by positivity),
    harg2, log_mul (by norm_num) (by positivity)]
  ring

set_option maxHeartbeats 800000 in
private lemma log_choose_master (N R : ℕ) {N0 R0 : ℝ}
    (hN0 : 20 ≤ N0) (hR_lo : (1 / 10 : ℝ) * N0 ≤ R0) (hR_hi : R0 ≤ (9 / 10 : ℝ) * N0)
    (hu : |(N : ℝ) - N0| ≤ N0 / 40) (hv : |(R : ℝ) - R0| ≤ N0 / 40) :
    let u : ℝ := (N : ℝ) - N0
    let v : ℝ := (R : ℝ) - R0
    let η : ℝ := R0 / N0
    |log (N.choose R : ℝ) -
      (logG N0 R0 + u * log (1 / (1 - η)) + v * log ((1 - η) / η) -
        (v - η * u) ^ 2 / (2 * η * (1 - η) * N0))| ≤
      4000 * ((|u| ^ 3 + |v| ^ 3) / N0 ^ 2 + (|u| + |v| + 1) / N0) := by
  intro u v η
  have hN0_pos : 0 < N0 := by linarith
  have hR0_pos : 0 < R0 := by linarith
  let S0 : ℝ := N0 - R0
  have hS0_lo : (1 / 10 : ℝ) * N0 ≤ S0 := by dsimp [S0]; linarith
  have hS0_pos : 0 < S0 := by linarith
  let w : ℝ := u - v
  have hNR_pos : 0 < (N : ℝ) ∧ 0 < (R : ℝ) ∧ 0 < (N : ℝ) - R := by
    have hu1 := (abs_le.mp hu).1; have hu2 := (abs_le.mp hu).2
    have hv1 := (abs_le.mp hv).1; have hv2 := (abs_le.mp hv).2
    exact ⟨by linarith, by linarith, by linarith⟩
  have hN_ge1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith [(abs_le.mp hu).1]
    exact_mod_cast this
  have hR_ge1 : 1 ≤ R := by
    have : (1 : ℝ) ≤ R := by linarith [(abs_le.mp hv).1]
    exact_mod_cast this
  have hRN_le : R ≤ N := by
    have : (R : ℝ) ≤ N := by linarith [hNR_pos.2.2]
    exact_mod_cast this
  have hNR_ge1 : 1 ≤ N - R := by
    have : (1 : ℝ) ≤ (N : ℝ) - R := by
      have hu1 := (abs_le.mp hu).1; have hv2 := (abs_le.mp hv).2; linarith
    rw [← Nat.cast_sub hRN_le] at this
    exact_mod_cast this
  have hNR_cast : ((N - R : ℕ) : ℝ) = S0 + w := by
    rw [Nat.cast_sub hRN_le]; dsimp [S0, w, u, v]; ring
  have hN_eq : (N : ℝ) = N0 + u := by dsimp [u]; ring
  have hR_eq : (R : ℝ) = R0 + v := by dsimp [v]; ring
  have hlog_ch : log (N.choose R : ℝ) =
      log (Nat.factorial N : ℝ) - log (Nat.factorial R : ℝ) -
        log (Nat.factorial (N - R) : ℝ) := by
    have hfac : (N.choose R : ℝ) =
        (Nat.factorial N : ℝ) / ((Nat.factorial R : ℝ) * (Nat.factorial (N - R) : ℝ)) := by
      have hnat := Nat.choose_mul_factorial_mul_factorial hRN_le
      have hR' : ((N.choose R : ℕ) : ℝ) * ((Nat.factorial R : ℕ) : ℝ) *
          ((Nat.factorial (N - R) : ℕ) : ℝ) = (Nat.factorial N : ℝ) := by
        exact_mod_cast hnat
      rw [eq_div_iff (by positivity)]
      linarith
    rw [hfac, log_div (by positivity) (by positivity),
      log_mul (by positivity) (by positivity)]
    ring
  have hstN := stirling_log_factorial_bounds N hN_ge1
  have hstR := stirling_log_factorial_bounds R hR_ge1
  have hstS := stirling_log_factorial_bounds (N - R) hNR_ge1
  let eN := log (Nat.factorial N : ℝ) -
    ((N : ℝ) * log N - N + (1 / 2) * log (2 * Real.pi * N))
  let eR := log (Nat.factorial R : ℝ) -
    ((R : ℝ) * log R - R + (1 / 2) * log (2 * Real.pi * R))
  let eS := log (Nat.factorial (N - R) : ℝ) -
    (((N - R : ℕ) : ℝ) * log ((N - R : ℕ) : ℝ) - (N - R : ℕ) +
      (1 / 2) * log (2 * Real.pi * ((N - R : ℕ) : ℝ)))
  have he_stirl : |eN - eR - eS| ≤ 10 / N0 := by
    have hN_lb : N0 / 20 ≤ (N : ℝ) := by linarith [(abs_le.mp hu).1]
    have hR_lb : N0 / 20 ≤ (R : ℝ) := by linarith [(abs_le.mp hv).1]
    have hS_lb : N0 / 20 ≤ ((N - R : ℕ) : ℝ) := by
      rw [hNR_cast]; dsimp [w]; linarith [(abs_le.mp hu).1, (abs_le.mp hv).2]
    have h1 : 1 / (12 * (N : ℝ)) ≤ 2 / N0 := by
      rw [div_le_div_iff₀ (by positivity) hN0_pos]; linarith
    have h2 : 1 / (12 * (R : ℝ)) ≤ 2 / N0 := by
      rw [div_le_div_iff₀ (by positivity) hN0_pos]; linarith
    have h3 : 1 / (12 * ((N - R : ℕ) : ℝ)) ≤ 2 / N0 := by
      rw [div_le_div_iff₀ (by positivity) hN0_pos]; linarith
    have h4 : 2 / N0 + 2 / N0 ≤ 10 / N0 := by
      rw [← add_div, div_le_div_iff₀ hN0_pos hN0_pos]; linarith
    have h210 : 2 / N0 ≤ 10 / N0 := by
      rw [div_le_div_iff₀ hN0_pos hN0_pos]; linarith
    change 0 ≤ eN ∧ eN ≤ 1 / (12 * (N : ℝ)) at hstN
    change 0 ≤ eR ∧ eR ≤ 1 / (12 * (R : ℝ)) at hstR
    change 0 ≤ eS ∧ eS ≤ 1 / (12 * ((N - R : ℕ) : ℝ)) at hstS
    rw [abs_le]; constructor <;> linarith only [hstN.1, hstN.2, hstR.1, hstR.2, hstS.1, hstS.2, h1, h2, h3, h4, h210]
  have hu_half : |u| ≤ N0 / 2 := le_trans hu (by linarith)
  have hv_half : |v| ≤ R0 / 2 := le_trans hv (by linarith)
  have hw_half : |w| ≤ S0 / 2 := by
    have h1 : |w| ≤ |u| + |v| := abs_sub u v
    linarith
  have h1u_pos : 0 < 1 + u / N0 := by
    have : -1 / 2 ≤ u / N0 := by rw [le_div_iff₀ hN0_pos]; linarith [(abs_le.mp hu_half).1]
    linarith
  have h1v_pos : 0 < 1 + v / R0 := by
    have : -1 / 2 ≤ v / R0 := by rw [le_div_iff₀ hR0_pos]; linarith [(abs_le.mp hv_half).1]
    linarith
  have h1w_pos : 0 < 1 + w / S0 := by
    have : -1 / 2 ≤ w / S0 := by rw [le_div_iff₀ hS0_pos]; linarith [(abs_le.mp hw_half).1]
    linarith
  have hlogN : log (N : ℝ) = log N0 + log (1 + u / N0) := by
    rw [← log_mul hN0_pos.ne' h1u_pos.ne']
    congr 1; rw [hN_eq]; field_simp [hN0_pos.ne']
  have hlogR : log (R : ℝ) = log R0 + log (1 + v / R0) := by
    rw [← log_mul hR0_pos.ne' h1v_pos.ne']
    congr 1; rw [hR_eq]; field_simp [hR0_pos.ne']
  have hlogS : log ((N - R : ℕ) : ℝ) = log S0 + log (1 + w / S0) := by
    rw [← log_mul hS0_pos.ne' h1w_pos.ne']
    congr 1; rw [hNR_cast]; field_simp [hS0_pos.ne']
  let T_main := (N0 + u) * log (1 + u / N0) - (u + u ^ 2 / (2 * N0))
      - ((R0 + v) * log (1 + v / R0) - (v + v ^ 2 / (2 * R0)))
      - ((S0 + w) * log (1 + w / S0) - (w + w ^ 2 / (2 * S0)))
  let T_half := (1 / 2 : ℝ) * (log (1 + u / N0) - log (1 + v / R0) - log (1 + w / S0))
  have hη_pos : 0 < η := div_pos hR0_pos hN0_pos
  have h1mη_eq : 1 - η = S0 / N0 := by dsimp [η, S0]; field_simp [hN0_pos.ne']
  have h1mη_pos : 0 < 1 - η := by rw [h1mη_eq]; positivity
  have hquad_eq : u ^ 2 / (2 * N0) - v ^ 2 / (2 * R0) - w ^ 2 / (2 * S0) =
      -(v - η * u) ^ 2 / (2 * η * (1 - η) * N0) := by
    rw [h1mη_eq]; dsimp [η, S0, w]
    have hNR_ne : N0 - R0 ≠ 0 := by linarith
    field_simp [hN0_pos.ne', hR0_pos.ne', hNR_ne]; ring
  have hlin1 : log (1 / (1 - η)) = log N0 - log S0 := by
    rw [h1mη_eq, one_div_div, log_div hN0_pos.ne' hS0_pos.ne']
  have hlin2 : log ((1 - η) / η) = log S0 - log R0 := by
    rw [h1mη_eq]; dsimp [η]
    rw [div_div_div_cancel_right₀ hN0_pos.ne', log_div hS0_pos.ne' hR0_pos.ne']
  have hlog2pi_eq :
      (1 / 2 : ℝ) * log (2 * Real.pi * N) - (1 / 2) * log (2 * Real.pi * R) -
      (1 / 2) * log (2 * Real.pi * ((N - R : ℕ) : ℝ)) +
      (1 / 2) * log (2 * Real.pi * R0 * S0 / N0) = T_half := by
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [log_mul h2pi.ne' hNR_pos.1.ne', log_mul h2pi.ne' hNR_pos.2.1.ne',
      log_mul h2pi.ne' (by rw [Nat.cast_sub hRN_le]; exact hNR_pos.2.2.ne'),
      log_div (by positivity) hN0_pos.ne', log_mul (by positivity) hS0_pos.ne',
      log_mul h2pi.ne' hR0_pos.ne', hlogN, hlogR, hlogS]
    dsimp [T_half]; ring
  have hdecomp :
      log (N.choose R : ℝ) -
        (logG N0 R0 + u * log (1 / (1 - η)) + v * log ((1 - η) / η) -
          (v - η * u) ^ 2 / (2 * η * (1 - η) * N0)) =
      (eN - eR - eS) + T_main + T_half := by
    have h1 : log (N.choose R : ℝ) = (eN - eR - eS) +
        ((N : ℝ) * log N - (R : ℝ) * log R - ((N - R : ℕ) : ℝ) * log ((N - R : ℕ) : ℝ)) +
        ((1 / 2) * log (2 * Real.pi * N) - (1 / 2) * log (2 * Real.pi * R) -
          (1 / 2) * log (2 * Real.pi * ((N - R : ℕ) : ℝ))) := by
      rw [hlog_ch]; dsimp [eN, eR, eS]; rw [Nat.cast_sub hRN_le]; ring
    have h2pi_sub :
        (1 / 2) * log (2 * Real.pi * N) - (1 / 2) * log (2 * Real.pi * R) -
          (1 / 2) * log (2 * Real.pi * ((N - R : ℕ) : ℝ)) =
        T_half - (1 / 2) * log (2 * Real.pi * R0 * S0 / N0) := by
      linarith [hlog2pi_eq]
    rw [h1, h2pi_sub, hlogN, hlogR, hlogS, hN_eq, hR_eq, hNR_cast]
    unfold logG
    rw [hlin1, hlin2]
    have h2 : (N0 + u) * (log N0 + log (1 + u / N0)) -
        (R0 + v) * (log R0 + log (1 + v / R0)) -
        (S0 + w) * (log S0 + log (1 + w / S0)) -
        (N0 * log N0 - R0 * log R0 - S0 * log S0 +
          u * (log N0 - log S0) + v * (log S0 - log R0)) =
        T_main + (u ^ 2 / (2 * N0) - v ^ 2 / (2 * R0) - w ^ 2 / (2 * S0)) := by
      dsimp [T_main, w]; ring
    have hS0_def : N0 - R0 = S0 := rfl
    rw [hS0_def]
    rw [neg_div] at hquad_eq
    linarith only [h2, hquad_eq]
  have hT_main : |T_main| ≤ 2500 * ((|u| ^ 3 + |v| ^ 3) / N0 ^ 2) := by
    have b1 := abs_add_mul_log_one_add_div_le hN0_pos hu_half
    have b2 := abs_add_mul_log_one_add_div_le hR0_pos hv_half
    have b3 := abs_add_mul_log_one_add_div_le hS0_pos hw_half
    have hR0_sq : (1 / 100 : ℝ) * N0 ^ 2 ≤ R0 ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hR_lo 2
      rw [mul_pow] at h; linarith
    have hS0_sq : (1 / 100 : ℝ) * N0 ^ 2 ≤ S0 ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hS0_lo 2
      rw [mul_pow] at h; linarith
    have hc2 : 4 * |v| ^ 3 / R0 ^ 2 ≤ 400 * |v| ^ 3 / N0 ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hmul := mL hR0_sq (show 0 ≤ 400 * |v| ^ 3 by positivity)
      linarith
    have hw_cub : |w| ^ 3 ≤ 4 * (|u| ^ 3 + |v| ^ 3) := by
      have hw1 : |w| ≤ |u| + |v| := abs_sub u v
      have hcu : (|u| + |v|) ^ 3 ≤ 4 * (|u| ^ 3 + |v| ^ 3) := by
        have hpos : 0 ≤ (|u| - |v|) ^ 2 * (|u| + |v|) := by positivity
        have hid : 4 * (|u| ^ 3 + |v| ^ 3) - (|u| + |v|) ^ 3 = 3 * ((|u| - |v|) ^ 2 * (|u| + |v|)) := by ring
        linarith
      exact (pow_le_pow_left₀ (abs_nonneg w) hw1 3).trans hcu
    have hc3 : 4 * |w| ^ 3 / S0 ^ 2 ≤ 1600 * (|u| ^ 3 + |v| ^ 3) / N0 ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 4 * |w| ^ 3 * N0 ^ 2 ≤ 16 * (|u| ^ 3 + |v| ^ 3) * N0 ^ 2 := by
        have := mR hw_cub (sq_nonneg N0); linarith
      have h2 := mL hS0_sq (show 0 ≤ 1600 * (|u| ^ 3 + |v| ^ 3) by positivity)
      linarith
    have htri : |T_main| ≤
        |(N0 + u) * log (1 + u / N0) - (u + u ^ 2 / (2 * N0))| +
        |(R0 + v) * log (1 + v / R0) - (v + v ^ 2 / (2 * R0))| +
        |(S0 + w) * log (1 + w / S0) - (w + w ^ 2 / (2 * S0))| := by
      dsimp [T_main]
      have h1 := abs_sub ((N0 + u) * log (1 + u / N0) - (u + u ^ 2 / (2 * N0)) -
        ((R0 + v) * log (1 + v / R0) - (v + v ^ 2 / (2 * R0))))
        ((S0 + w) * log (1 + w / S0) - (w + w ^ 2 / (2 * S0)))
      have h2 := abs_sub ((N0 + u) * log (1 + u / N0) - (u + u ^ 2 / (2 * N0)))
        ((R0 + v) * log (1 + v / R0) - (v + v ^ 2 / (2 * R0)))
      linarith
    have hsum : 4 * |u| ^ 3 / N0 ^ 2 + 400 * |v| ^ 3 / N0 ^ 2 +
        1600 * (|u| ^ 3 + |v| ^ 3) / N0 ^ 2 ≤ 2500 * ((|u| ^ 3 + |v| ^ 3) / N0 ^ 2) := by
      have : 0 ≤ (|u| ^ 3 + |v| ^ 3) / N0 ^ 2 := by positivity
      have hu3 : 0 ≤ |u| ^ 3 / N0 ^ 2 := by positivity
      have hv3 : 0 ≤ |v| ^ 3 / N0 ^ 2 := by positivity
      have halg : 4 * |u| ^ 3 / N0 ^ 2 + 400 * |v| ^ 3 / N0 ^ 2 +
          1600 * (|u| ^ 3 + |v| ^ 3) / N0 ^ 2 =
          1604 * (|u| ^ 3 / N0 ^ 2) + 2000 * (|v| ^ 3 / N0 ^ 2) := by ring
      have halg2 : 2500 * ((|u| ^ 3 + |v| ^ 3) / N0 ^ 2) =
          2500 * (|u| ^ 3 / N0 ^ 2) + 2500 * (|v| ^ 3 / N0 ^ 2) := by ring
      linarith
    linarith
  have hT_half : |T_half| ≤ 25 * ((|u| + |v|) / N0) := by
    have l1 := abs_log_one_add_le (show |u / N0| ≤ 1 / 2 by
      rw [abs_div, abs_of_pos hN0_pos, div_le_iff₀ hN0_pos]; linarith)
    have l2 := abs_log_one_add_le (show |v / R0| ≤ 1 / 2 by
      rw [abs_div, abs_of_pos hR0_pos, div_le_iff₀ hR0_pos]; linarith)
    have l3 := abs_log_one_add_le (show |w / S0| ≤ 1 / 2 by
      rw [abs_div, abs_of_pos hS0_pos, div_le_iff₀ hS0_pos]; linarith)
    have h2 : |v / R0| ≤ 10 * |v| / N0 := by
      rw [abs_div, abs_of_pos hR0_pos, div_le_div_iff₀ hR0_pos hN0_pos]
      have hmul := mL hR_lo (abs_nonneg v)
      linarith only [hmul]
    have h3 : |w / S0| ≤ 10 * (|u| + |v|) / N0 := by
      rw [abs_div, abs_of_pos hS0_pos, div_le_div_iff₀ hS0_pos hN0_pos]
      have hw1 : |w| ≤ |u| + |v| := abs_sub u v
      have hmul1 := mR hw1 hN0_pos.le
      have hmul2 := mL hS0_lo (show 0 ≤ |u| + |v| by positivity)
      linarith only [hmul1, hmul2]
    have h1 : |u / N0| = |u| / N0 := by rw [abs_div, abs_of_pos hN0_pos]
    have htri : |T_half| ≤ (1 / 2 : ℝ) * (|log (1 + u / N0)| +
        |log (1 + v / R0)| + |log (1 + w / S0)|) := by
      dsimp [T_half]; rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have ha := abs_sub (log (1 + u / N0) - log (1 + v / R0)) (log (1 + w / S0))
      have hb := abs_sub (log (1 + u / N0)) (log (1 + v / R0))
      linarith
    have hsum : (1 / 2 : ℝ) * (2 * (|u| / N0) + 2 * (10 * |v| / N0) + 2 * (10 * (|u| + |v|) / N0)) ≤
        25 * ((|u| + |v|) / N0) := by
      have hu_nn : 0 ≤ |u| / N0 := by positivity
      have hv_nn : 0 ≤ |v| / N0 := by positivity
      have heq1 : (1 / 2 : ℝ) * (2 * (|u| / N0) + 2 * (10 * |v| / N0) + 2 * (10 * (|u| + |v|) / N0)) =
          11 * (|u| / N0) + 20 * (|v| / N0) := by ring
      have heq2 : 25 * ((|u| + |v|) / N0) = 25 * (|u| / N0) + 25 * (|v| / N0) := by ring
      linarith
    linarith
  rw [hdecomp]
  have htri_tot : |(eN - eR - eS) + T_main + T_half| ≤ |eN - eR - eS| + |T_main| + |T_half| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hfinal : 10 / N0 + 2500 * ((|u| ^ 3 + |v| ^ 3) / N0 ^ 2) + 25 * ((|u| + |v|) / N0) ≤
      4000 * ((|u| ^ 3 + |v| ^ 3) / N0 ^ 2 + (|u| + |v| + 1) / N0) := by
    have h1 : 0 ≤ (|u| ^ 3 + |v| ^ 3) / N0 ^ 2 := by positivity
    have h2 : 0 ≤ (|u| + |v|) / N0 := by positivity
    have h3 : 0 ≤ 1 / N0 := by positivity
    have heq : (|u| + |v| + 1) / N0 = (|u| + |v|) / N0 + 1 / N0 := by ring
    have h10 : 10 / N0 = 10 * (1 / N0) := by ring
    rw [heq, h10]; linarith only [h1, h2, h3]
  linarith

-- ============================================================================
-- Section 4: Lemma 5 (Exact second-difference identity and parity sum bound)
-- ============================================================================

private lemma alt_sum_eq_second_diff (D : ℕ) (T : ℕ → ℝ) :
    let U (j : ℕ) : ℝ := if 2 ≤ j ∧ j ≤ D + 2 then T (j - 2) else 0
    ∑ j ∈ range (D + 3), (-1 : ℝ) ^ j * (2 * U (j + 1) - U j - U (j + 2)) =
      -4 * ∑ r ∈ range (D + 1), (-1 : ℝ) ^ r * T r := by
  intro U
  have hsplit :
      (∑ j ∈ range (D + 3), (-1 : ℝ) ^ j * (2 * U (j + 1) - U j - U (j + 2))) =
      2 * (∑ j ∈ range (D + 3), (-1 : ℝ) ^ j * U (j + 1)) -
      (∑ j ∈ range (D + 3), (-1 : ℝ) ^ j * U j) -
      (∑ j ∈ range (D + 3), (-1 : ℝ) ^ j * U (j + 2)) := by
    have h1 : ∀ j : ℕ, (-1 : ℝ) ^ j * (2 * U (j + 1) - U j - U (j + 2)) =
        2 * ((-1 : ℝ) ^ j * U (j + 1)) - (-1 : ℝ) ^ j * U j - (-1 : ℝ) ^ j * U (j + 2) := by
      intro j; ring
    simp_rw [h1, sum_sub_distrib, ← mul_sum]
  have hA : ∑ j ∈ range (D + 3), (-1 : ℝ) ^ j * U (j + 1) =
      -∑ r ∈ range (D + 1), (-1 : ℝ) ^ r * T r := by
    rw [Finset.sum_range_succ', sum_range_succ]
    have hU1 : U 1 = 0 := by simp [U]
    have hUD : U (D + 3) = 0 := by simp [U]
    simp only [hU1, hUD, mul_zero, add_zero, zero_add]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun r hr => ?_
    have hrD : r ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hr)
    have hUr : U (r + 1 + 1) = T r := by dsimp [U]; rw [if_pos (by omega)]; rfl
    rw [hUr, pow_succ]; ring
  have hB : ∑ j ∈ range (D + 3), (-1 : ℝ) ^ j * U j =
      ∑ r ∈ range (D + 1), (-1 : ℝ) ^ r * T r := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hU0 : U 0 = 0 := by simp [U]
    have hU1 : U 1 = 0 := by simp [U]
    simp only [hU0, hU1, mul_zero, add_zero]
    refine sum_congr rfl fun r hr => ?_
    have hrD : r ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hr)
    have hUr : U (r + 1 + 1) = T r := by dsimp [U]; rw [if_pos (by omega)]; rfl
    rw [hUr, pow_succ, pow_succ]; ring
  have hC : ∑ j ∈ range (D + 3), (-1 : ℝ) ^ j * U (j + 2) =
      ∑ r ∈ range (D + 1), (-1 : ℝ) ^ r * T r := by
    rw [sum_range_succ, sum_range_succ]
    have hUD1 : U (D + 3) = 0 := by simp [U]
    have hUD2 : U (D + 4) = 0 := by simp [U]
    have hidx1 : D + 1 + 2 = D + 3 := by omega
    have hidx2 : D + 2 + 2 = D + 4 := by omega
    rw [hidx1, hidx2, hUD1, hUD2]
    simp only [mul_zero, add_zero]
    refine sum_congr rfl fun r hr => ?_
    have hrD : r ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hr)
    have hUr : U (r + 2) = T r := by dsimp [U]; rw [if_pos (by omega)]; rfl
    rw [hUr]
  linarith

private lemma abs_add3_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le (a + b) c).trans (add_le_add (abs_add_le a b) le_rfl)

private lemma abs_add_sub_le (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| :=
  (abs_sub (a + b) c).trans (add_le_add (abs_add_le a b) le_rfl)

private lemma abs_sub_add_le (a b c : ℝ) : |a - b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le (a - b) c).trans (add_le_add (abs_sub a b) le_rfl)

set_option maxHeartbeats 800000 in
private lemma lemma5_parity_sum (D M2 S2 d2 : ℕ) {L : ℝ}
    (hD : 100 ≤ D) (hDM : D ≤ M2) (_hS2 : S2 ≤ D + M2)
    (hd2 : d2 ∈ ({0, 1} : Finset ℕ))
    (hL : 2 ≤ L)
    (hW : 10 * sqrt D * L ≤ (D : ℝ) / 10)
    (hη_lo : (1 / 2 : ℝ) * ((D : ℝ) + M2) ≤ S2)
    (hη_hi : (S2 : ℝ) ≤ (4 / 5 : ℝ) * ((D : ℝ) + M2))
    (htail : ((D + 3 : ℕ) : ℝ) * exp (-9 * L ^ 2) ≤ 1 / (D : ℝ)) :
    let T (r : ℕ) : ℝ := (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ)
    |∑ r ∈ (range (D + 1)).filter (fun r => r % 2 = d2), T r -
      (1 / 2) * (((D + M2).choose S2 : ℕ) : ℝ)| ≤
      (1000000 * L ^ 2 / (D : ℝ)) * (((D + M2).choose S2 : ℕ) : ℝ) := by
  intro T
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hM2_pos : (0 : ℝ) < M2 := by exact_mod_cast (show 0 < M2 by omega)
  have hDM_pos : (0 : ℝ) < (D : ℝ) + M2 := by positivity
  have hD_le_M2 : (D : ℝ) ≤ M2 := by exact_mod_cast hDM
  let tot : ℝ := (((D + M2).choose S2 : ℕ) : ℝ)
  have htot_nn : 0 ≤ tot := Nat.cast_nonneg _
  have hsum_tot : ∑ r ∈ range (D + 1), T r = tot := by
    have h1 := sum_hypergeom D M2 S2
    have hsplit : ∑ r ∈ range (S2 + 1), T r = ∑ r ∈ range (D + 1), T r := by
      have hsub1 : ∀ r, D < r → T r = 0 := fun r hr => by
        simp [T, Nat.choose_eq_zero_of_lt hr]
      have hsub2 : ∀ r, S2 < r → T r = 0 := fun r hr => by
        by_cases hDlt : D < r
        · exact hsub1 r hDlt
        · have : S2 - r = 0 := by omega
          exfalso
          have hS2_ge : D ≤ S2 := by
            have : (D : ℝ) ≤ S2 := by linarith
            exact_mod_cast this
          omega
      have hD_le_S2 : D ≤ S2 := by
        have : (D : ℝ) ≤ S2 := by linarith
        exact_mod_cast this
      symm
      apply sum_subset (range_mono (by omega : D + 1 ≤ S2 + 1))
      intro r _ hr
      exact hsub1 r (by simp only [mem_range] at hr; omega)
    rw [← hsplit]; exact h1
  let alt : ℝ := ∑ r ∈ range (D + 1), (-1 : ℝ) ^ r * T r
  have hparity : |∑ r ∈ (range (D + 1)).filter (fun r => r % 2 = d2), T r - (1 / 2) * tot| =
      |alt| / 2 := by
    let Seven := (range (D + 1)).filter (fun r => r % 2 = 0)
    let Sodd := (range (D + 1)).filter (fun r => r % 2 = 1)
    have hdisj : Disjoint Seven Sodd := by
      rw [disjoint_left]; intro r h0 h1
      have a := (mem_filter.mp h0).2; have b := (mem_filter.mp h1).2; omega
    have hunion : Seven ∪ Sodd = range (D + 1) := by
      ext r; simp only [Seven, Sodd, mem_union, mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases h0 : r % 2 = 0
        · exact Or.inl ⟨h, h0⟩
        · exact Or.inr ⟨h, by omega⟩
    have hsum_add : (∑ r ∈ Seven, T r) + (∑ r ∈ Sodd, T r) = tot := by
      rw [← sum_union hdisj, hunion, hsum_tot]
    have hsum_sub : (∑ r ∈ Seven, T r) - (∑ r ∈ Sodd, T r) = alt := by
      dsimp [alt]
      rw [← hunion, sum_union hdisj]
      have he : ∑ r ∈ Seven, (-1 : ℝ) ^ r * T r = ∑ r ∈ Seven, T r := by
        refine sum_congr rfl fun r hr => ?_
        have h0 : r % 2 = 0 := (mem_filter.mp hr).2
        have hpow : (-1 : ℝ) ^ r = 1 := by
          obtain ⟨q, rfl⟩ : ∃ q, r = 2 * q := ⟨r / 2, by omega⟩
          rw [pow_mul]; norm_num
        rw [hpow, one_mul]
      have ho : ∑ r ∈ Sodd, (-1 : ℝ) ^ r * T r = -∑ r ∈ Sodd, T r := by
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun r hr => ?_
        have h1 : r % 2 = 1 := (mem_filter.mp hr).2
        have hpow : (-1 : ℝ) ^ r = -1 := by
          obtain ⟨q, rfl⟩ : ∃ q, r = 2 * q + 1 := ⟨r / 2, by omega⟩
          rw [pow_add, pow_mul]; norm_num
        rw [hpow]; ring
      linarith
    simp only [mem_insert, mem_singleton] at hd2
    rcases hd2 with rfl | rfl
    · have : ∑ r ∈ Seven, T r - (1 / 2) * tot = alt / 2 := by linarith
      change |∑ r ∈ Seven, T r - (1 / 2) * tot| = |alt| / 2
      rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    · have : ∑ r ∈ Sodd, T r - (1 / 2) * tot = -(alt / 2) := by linarith
      change |∑ r ∈ Sodd, T r - (1 / 2) * tot| = |alt| / 2
      rw [this, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hparity]
  let U (j : ℕ) : ℝ := if 2 ≤ j ∧ j ≤ D + 2 then T (j - 2) else 0
  have hU_nn : ∀ j, 0 ≤ U j := fun j => by dsimp [U]; split_ifs <;> positivity
  have hid := alt_sum_eq_second_diff D T
  have halt_le : |alt| ≤ (1 / 4 : ℝ) * ∑ j ∈ range (D + 3), |2 * U (j + 1) - U j - U (j + 2)| := by
    have heq : alt = -(1 / 4 : ℝ) * ∑ j ∈ range (D + 3), (-1 : ℝ) ^ j * (2 * U (j + 1) - U j - U (j + 2)) := by
      dsimp [alt]; linarith [hid]
    rw [heq, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    apply mL _ (by norm_num)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  let μ : ℝ := (D : ℝ) * S2 / ((D : ℝ) + M2)
  let W : ℝ := 10 * sqrt D * L
  have hW_pos : 0 < W := by dsimp [W]; positivity
  let Jcent := (range (D + 3)).filter (fun j => 2 ≤ j ∧ j ≤ D ∧ |((j - 1 : ℕ) : ℝ) - μ| ≤ W)
  let Jtail := (range (D + 3)).filter (fun j => ¬ (2 ≤ j ∧ j ≤ D ∧ |((j - 1 : ℕ) : ℝ) - μ| ≤ W))
  have hsplit_J :
      (∑ j ∈ range (D + 3), |2 * U (j + 1) - U j - U (j + 2)|) =
      (∑ j ∈ Jcent, |2 * U (j + 1) - U j - U (j + 2)|) +
      (∑ j ∈ Jtail, |2 * U (j + 1) - U j - U (j + 2)|) :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hcent_bound : ∑ j ∈ Jcent, |2 * U (j + 1) - U j - U (j + 2)| ≤
      (5500000 * L ^ 2 / (D : ℝ)) * tot := by
    have hpt : ∀ j ∈ Jcent, |2 * U (j + 1) - U j - U (j + 2)| ≤
        (5500000 * L ^ 2 / (D : ℝ)) * U (j + 1) := by
      intro j hj
      obtain ⟨_, hj_lo, hj_hi, hdist⟩ := mem_filter.mp hj
      let r := j - 1
      have hr1 : 1 ≤ r := by omega
      have hrD : r + 1 ≤ D := by omega
      have hU0 : U j = T (r - 1) := by dsimp [U]; rw [if_pos (by omega)]; rfl
      have hU1 : U (j + 1) = T r := by dsimp [U]; rw [if_pos (by omega)]; rfl
      have hU2 : U (j + 2) = T (r + 1) := by dsimp [U]; rw [if_pos (by omega)]; congr 1; omega
      rw [hU0, hU1, hU2]
      have hμ_lo : (1 / 2 : ℝ) * D ≤ μ := by dsimp [μ]; rw [le_div_iff₀ hDM_pos]; nlinarith
      have hμ_hi : μ ≤ (4 / 5 : ℝ) * D := by dsimp [μ]; rw [div_le_iff₀ hDM_pos]; nlinarith
      have hr_lo : (2 / 5 : ℝ) * D ≤ r := by linarith [(abs_le.mp hdist).1]
      have hr_hi : (r : ℝ) ≤ (9 / 10 : ℝ) * D := by linarith [(abs_le.mp hdist).2]
      have hS2_gt : r < S2 := by
        have : (r : ℝ) < S2 := by linarith
        exact_mod_cast this
      have hS2_r_lo : (2 / 5 : ℝ) * M2 ≤ (S2 : ℝ) - r := by
        have h1 : (S2 : ℝ) - μ = (M2 : ℝ) * S2 / ((D : ℝ) + M2) := by
          dsimp [μ]; field_simp [hDM_pos.ne']; ring
        have h2 : (1 / 2 : ℝ) * M2 ≤ (M2 : ℝ) * S2 / ((D : ℝ) + M2) := by
          rw [le_div_iff₀ hDM_pos]; nlinarith
        linarith [(abs_le.mp hdist).2]
      have hS2_r_hi : (S2 : ℝ) - r ≤ (9 / 10 : ℝ) * M2 := by
        have h1 : (S2 : ℝ) - μ = (M2 : ℝ) * S2 / ((D : ℝ) + M2) := by
          dsimp [μ]; field_simp [hDM_pos.ne']; ring
        have h2 : (M2 : ℝ) * S2 / ((D : ℝ) + M2) ≤ (4 / 5 : ℝ) * M2 := by
          rw [div_le_iff₀ hDM_pos]; nlinarith
        linarith [(abs_le.mp hdist).1]
      by_cases hTr : T r = 0
      · exfalso
        have hS2_r : S2 - r ≤ M2 := by
          have hR : ((S2 - r : ℕ) : ℝ) ≤ M2 := by
            rw [Nat.cast_sub (le_of_lt hS2_gt)]; linarith
          exact_mod_cast hR
        have hc1 : 0 < D.choose r := Nat.choose_pos (by omega)
        have hc2 : 0 < M2.choose (S2 - r) := Nat.choose_pos hS2_r
        have hpos : 0 < T r := by dsimp [T]; positivity
        linarith
      let a : ℝ := r
      let b : ℝ := (D : ℝ) - r
      let c : ℝ := (S2 : ℝ) - r
      let d : ℝ := (M2 : ℝ) - S2 + r
      have ha_lo : (1 / 10 : ℝ) * D ≤ a := by dsimp [a]; linarith
      have hb_lo : (1 / 10 : ℝ) * D ≤ b := by dsimp [b]; linarith
      have hc_lo : (1 / 10 : ℝ) * M2 ≤ c := by dsimp [c]; linarith
      have hd_lo : (1 / 10 : ℝ) * M2 ≤ d := by dsimp [d]; linarith
      have had_pos : 0 < (a + 1) * (d + 1) := by nlinarith
      have hbc_pos : 0 < (b + 1) * (c + 1) := by nlinarith
      have hst_R : T (r + 1) * ((a + 1) * (d + 1)) = T r * (b * c) := by
        dsimp [T, a, b, c, d]; exact hypergeom_step_eq D M2 S2 r hS2_gt
      have hst_L : T (r - 1) * ((b + 1) * (c + 1)) = T r * (a * d) := by
        have h := hypergeom_step_eq D M2 S2 (r - 1) (by omega)
        have hidx : r - 1 + 1 = r := by omega
        have hcast : ((r - 1 : ℕ) : ℝ) + 1 = r := by rw [Nat.cast_sub hr1]; push_cast; ring
        rw [hidx] at h
        have h1 : (D : ℝ) - ((r - 1 : ℕ) : ℝ) = b + 1 := by dsimp [b]; linarith
        have h2 : (S2 : ℝ) - ((r - 1 : ℕ) : ℝ) = c + 1 := by dsimp [c]; linarith
        have h3 : (M2 : ℝ) - S2 + ((r - 1 : ℕ) : ℝ) + 1 = d := by dsimp [d]; linarith
        rw [hcast, h1, h2, h3] at h
        dsimp [T, a]; exact h.symm
      have hTR_eq : T (r + 1) = T r * (b * c / ((a + 1) * (d + 1))) := by
        rw [mul_div_assoc', eq_div_iff had_pos.ne']; exact hst_R
      have hTL_eq : T (r - 1) = T r * (a * d / ((b + 1) * (c + 1))) := by
        rw [mul_div_assoc', eq_div_iff hbc_pos.ne']; exact hst_L
      let u : ℝ := (r : ℝ) - μ
      have had_bc : a * d - b * c = ((D : ℝ) + M2) * u := by
        dsimp [a, b, c, d, u, μ]; field_simp [hDM_pos.ne']; ring
      have h2diff : 2 * T r - T (r - 1) - T (r + 1) =
          T r * (((D : ℝ) + M2) * u * (-(D + M2) * u + (b + c - a - d)) /
            (((a + 1) * (d + 1)) * ((b + 1) * (c + 1))) +
            (a + d + 1) / ((a + 1) * (d + 1)) +
            (b + c + 1) / ((b + 1) * (c + 1))) := by
        rw [hTR_eq, hTL_eq]
        have hcomb : 2 - a * d / ((b + 1) * (c + 1)) - b * c / ((a + 1) * (d + 1)) =
            (a * d - b * c) * ((b + 1) * (c + 1) - (a + 1) * (d + 1)) /
              (((a + 1) * (d + 1)) * ((b + 1) * (c + 1))) +
            (a + d + 1) / ((a + 1) * (d + 1)) +
            (b + c + 1) / ((b + 1) * (c + 1)) := by
          have ha1 : a + 1 ≠ 0 := by linarith
          have hd1 : d + 1 ≠ 0 := by linarith
          have hb1 : b + 1 ≠ 0 := by linarith
          have hc1 : c + 1 ≠ 0 := by linarith
          field_simp [ha1, hd1, hb1, hc1]; ring
        have hbc_ad : (b + 1) * (c + 1) - (a + 1) * (d + 1) =
            -(a * d - b * c) + (b + c - a - d) := by ring
        rw [hbc_ad, had_bc] at hcomb
        have hstep : 2 * T r - T r * (a * d / ((b + 1) * (c + 1))) -
            T r * (b * c / ((a + 1) * (d + 1))) =
            T r * (2 - a * d / ((b + 1) * (c + 1)) - b * c / ((a + 1) * (d + 1))) := by ring
        rw [hstep, hcomb]
        congr 2; congr 1; ring
      have hden_lb1 : (1 / 100 : ℝ) * (D * M2) ≤ (a + 1) * (d + 1) := by
        have h1 : (1 / 10 : ℝ) * D ≤ a + 1 := by linarith
        have h2 : (1 / 10 : ℝ) * M2 ≤ d + 1 := by linarith
        have hmul := mul_le_mul h1 h2 (by positivity) (by linarith)
        linarith
      have hden_lb2 : (1 / 100 : ℝ) * (D * M2) ≤ (b + 1) * (c + 1) := by
        have h1 : (1 / 10 : ℝ) * D ≤ b + 1 := by linarith
        have h2 : (1 / 10 : ℝ) * M2 ≤ c + 1 := by linarith
        have hmul := mul_le_mul h1 h2 (by positivity) (by linarith)
        linarith
      have hden_prod : (1 / 10000 : ℝ) * ((D : ℝ) ^ 2 * M2 ^ 2) ≤
          ((a + 1) * (d + 1)) * ((b + 1) * (c + 1)) := by
        have hmul := mul_le_mul hden_lb1 hden_lb2 (by positivity) (by positivity)
        linarith
      have hu_le_W : |u| ≤ W := hdist
      have hu_sq : u ^ 2 ≤ 100 * (D : ℝ) * L ^ 2 := by
        have h1 : u ^ 2 ≤ W ^ 2 := by
          rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg u) hu_le_W 2
        have hW2 : W ^ 2 = 100 * (D : ℝ) * L ^ 2 := by
          dsimp [W]; rw [mul_pow, mul_pow, sq_sqrt hD_pos.le]; ring
        linarith
      have hbcad_le : |b + c - a - d| ≤ (D : ℝ) + M2 := by
        dsimp [a, b, c, d]; rw [abs_le]; constructor <;> linarith
      have hterm1 : |((D : ℝ) + M2) * u * (-(D + M2) * u + (b + c - a - d)) /
          (((a + 1) * (d + 1)) * ((b + 1) * (c + 1)))| ≤ 5000000 * L ^ 2 / D := by
        rw [abs_div, abs_of_pos (mul_pos had_pos hbc_pos)]
        have hnum_le : |((D : ℝ) + M2) * u * (-(D + M2) * u + (b + c - a - d))| ≤
            ((D : ℝ) + M2) ^ 2 * (u ^ 2 + |u|) := by
          rw [abs_mul, abs_mul, abs_of_pos hDM_pos]
          have hinner : |-(D + M2) * u + (b + c - a - d)| ≤ ((D : ℝ) + M2) * (|u| + 1) := by
            have h1 := abs_add_le (-(D + M2) * u) (b + c - a - d)
            rw [abs_mul, abs_neg, abs_of_pos hDM_pos] at h1
            linarith [hbcad_le]
          have hmul := mL hinner (show 0 ≤ ((D : ℝ) + M2) * |u| by positivity)
          have heq : ((D : ℝ) + M2) * |u| * (((D : ℝ) + M2) * (|u| + 1)) =
              ((D : ℝ) + M2) ^ 2 * (u ^ 2 + |u|) := by rw [← sq_abs u]; ring
          linarith
        have hDM_sq : ((D : ℝ) + M2) ^ 2 ≤ 4 * (M2 : ℝ) ^ 2 := by
          have h := pow_le_pow_left₀ hDM_pos.le (show (D : ℝ) + M2 ≤ 2 * M2 by linarith) 2
          rw [mul_pow] at h; linarith
        have hu_u : u ^ 2 + |u| ≤ 110 * (D : ℝ) * L ^ 2 := by
          have h1 : |u| ≤ 10 * (D : ℝ) * L ^ 2 := by
            have hsq : sqrt D ≤ D := by
              rw [sqrt_le_left hD_pos.le]
              have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
              have := mR hD1 hD_pos.le
              linarith
            have hL2 : L ≤ L ^ 2 := by
              have := mR (show (1 : ℝ) ≤ L by linarith) (by linarith : (0 : ℝ) ≤ L)
              linarith
            have hmul1 : 10 * sqrt D * L ≤ 10 * (D : ℝ) * L :=
              mR (mL hsq (by norm_num)) (by linarith)
            have hmul2 : 10 * (D : ℝ) * L ≤ 10 * (D : ℝ) * L ^ 2 :=
              mL hL2 (by positivity)
            dsimp [W] at hu_le_W
            linarith
          linarith
        have hnum2 : ((D : ℝ) + M2) ^ 2 * (u ^ 2 + |u|) ≤ 440 * (D : ℝ) * M2 ^ 2 * L ^ 2 := by
          have := mul_le_mul hDM_sq hu_u (by positivity) (by positivity)
          linarith
        rw [div_le_div_iff₀ (mul_pos had_pos hbc_pos) hD_pos]
        calc |((D : ℝ) + M2) * u * (-(D + M2) * u + (b + c - a - d))| * D
            ≤ (440 * (D : ℝ) * M2 ^ 2 * L ^ 2) * D :=
              mR (hnum_le.trans hnum2) hD_pos.le
          _ ≤ 5000000 * L ^ 2 * (((1 / 10000 : ℝ) * ((D : ℝ) ^ 2 * M2 ^ 2))) := by
              have hnn : 0 ≤ (D : ℝ) ^ 2 * M2 ^ 2 * L ^ 2 := by positivity
              have hid1 : (440 * (D : ℝ) * M2 ^ 2 * L ^ 2) * D = 440 * ((D : ℝ) ^ 2 * M2 ^ 2 * L ^ 2) := by ring
              have hid2 : 5000000 * L ^ 2 * (((1 / 10000 : ℝ) * ((D : ℝ) ^ 2 * M2 ^ 2))) =
                  500 * ((D : ℝ) ^ 2 * M2 ^ 2 * L ^ 2) := by ring
              rw [hid1, hid2]; linarith only [hnn]
          _ ≤ 5000000 * L ^ 2 * (((a + 1) * (d + 1)) * ((b + 1) * (c + 1))) :=
              mL hden_prod (by positivity)
      have hterm2 : |(a + d + 1) / ((a + 1) * (d + 1))| ≤ 20 / D := by
        have ha_pos : 0 < a := by linarith only [ha_lo, hD_pos]
        have hd_pos : 0 < d := by linarith only [hd_lo, hM2_pos]
        rw [abs_of_pos (div_pos (by linarith only [ha_pos, hd_pos]) had_pos), div_le_div_iff₀ had_pos hD_pos]
        have h1 : (a + 1) * D ≤ 10 * ((a + 1) * (d + 1)) := by
          have hdm : (D : ℝ) ≤ 10 * (d + 1) := by linarith only [hd_lo, hD_le_M2]
          have hmul := mL hdm (by linarith only [ha_pos] : 0 ≤ a + 1)
          linarith only [hmul]
        have h2 : d * D ≤ 10 * ((a + 1) * (d + 1)) := by
          have ham : (D : ℝ) ≤ 10 * (a + 1) := by linarith only [ha_lo]
          have hmul := mL ham hd_pos.le
          have h3 : 0 ≤ 10 * (a + 1) := by linarith only [ha_pos]
          have hid : 10 * ((a + 1) * (d + 1)) = d * (10 * (a + 1)) + 10 * (a + 1) := by ring
          linarith only [hmul, h3, hid]
        have hadd : (a + d + 1) * (D : ℝ) = (a + 1) * D + d * D := by ring
        linarith only [h1, h2, hadd]
      have hterm3 : |(b + c + 1) / ((b + 1) * (c + 1))| ≤ 20 / D := by
        have hb_pos : 0 < b := by linarith only [hb_lo, hD_pos]
        have hc_pos : 0 < c := by linarith only [hc_lo, hM2_pos]
        rw [abs_of_pos (div_pos (by linarith only [hb_pos, hc_pos]) hbc_pos), div_le_div_iff₀ hbc_pos hD_pos]
        have h1 : (b + 1) * D ≤ 10 * ((b + 1) * (c + 1)) := by
          have hcm : (D : ℝ) ≤ 10 * (c + 1) := by linarith only [hc_lo, hD_le_M2]
          have hmul := mL hcm (by linarith only [hb_pos] : 0 ≤ b + 1)
          linarith only [hmul]
        have h2 : c * D ≤ 10 * ((b + 1) * (c + 1)) := by
          have hbm : (D : ℝ) ≤ 10 * (b + 1) := by linarith only [hb_lo]
          have hmul := mL hbm hc_pos.le
          have h3 : 0 ≤ 10 * (b + 1) := by linarith only [hb_pos]
          have hid : 10 * ((b + 1) * (c + 1)) = c * (10 * (b + 1)) + 10 * (b + 1) := by ring
          linarith only [hmul, h3, hid]
        have hadd : (b + c + 1) * (D : ℝ) = (b + 1) * D + c * D := by ring
        linarith only [h1, h2, hadd]
      rw [h2diff, abs_mul, abs_of_nonneg (show 0 ≤ T r by dsimp [T]; positivity)]
      have hbrack : |((D : ℝ) + M2) * u * (-(D + M2) * u + (b + c - a - d)) /
            (((a + 1) * (d + 1)) * ((b + 1) * (c + 1))) +
            (a + d + 1) / ((a + 1) * (d + 1)) +
            (b + c + 1) / ((b + 1) * (c + 1))| ≤ 5500000 * L ^ 2 / D := by
        have htri := abs_add3_le (((D : ℝ) + M2) * u * (-(D + M2) * u + (b + c - a - d)) /
            (((a + 1) * (d + 1)) * ((b + 1) * (c + 1))))
          ((a + d + 1) / ((a + 1) * (d + 1))) ((b + c + 1) / ((b + 1) * (c + 1)))
        have h40 : 40 / (D : ℝ) ≤ 500000 * L ^ 2 / D := by
          rw [div_le_div_iff₀ hD_pos hD_pos]
          have hL2 : (4 : ℝ) ≤ L ^ 2 := by
            have := mul_le_mul hL hL (by norm_num) (by linarith only [hL])
            linarith only [this]
          have hmul := mR hL2 hD_pos.le
          linarith only [hmul]
        have hadd : 5000000 * L ^ 2 / (D : ℝ) + 500000 * L ^ 2 / (D : ℝ) = 5500000 * L ^ 2 / (D : ℝ) := by ring
        have h20 : (20 : ℝ) / D + 20 / D = 40 / D := by ring
        linarith only [htri, hterm1, hterm2, hterm3, h40, hadd, h20]
      rw [mul_comm]
      exact mR hbrack (by dsimp [T]; positivity)
    calc ∑ j ∈ Jcent, |2 * U (j + 1) - U j - U (j + 2)|
        ≤ ∑ j ∈ Jcent, (5500000 * L ^ 2 / D) * U (j + 1) := sum_le_sum hpt
      _ = (5500000 * L ^ 2 / D) * ∑ j ∈ Jcent, U (j + 1) := (mul_sum _ _ _).symm
      _ ≤ (5500000 * L ^ 2 / D) * tot := by
          apply mL _ (by positivity)
          have hsub : Jcent.image (fun j => j - 1) ⊆ range (D + 1) := by
            intro r hr; obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
            obtain ⟨_, hj_lo, hj_hi, _⟩ := mem_filter.mp hj
            exact mem_range.mpr (by omega)
          have heq : ∑ j ∈ Jcent, U (j + 1) = ∑ r ∈ Jcent.image (fun j => j - 1), T r := by
            rw [sum_image]
            · refine sum_congr rfl fun j hj => ?_
              obtain ⟨_, hj_lo, hj_hi, _⟩ := mem_filter.mp hj
              dsimp [U]; rw [if_pos (by omega)]; rfl
            · intro a ha b hb hab
              have ha' := (mem_filter.mp ha).2.1
              have hb' := (mem_filter.mp hb).2.1
              dsimp only at hab; omega
          rw [heq, ← hsum_tot]
          exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by dsimp [T]; positivity)
  have htail_bound : ∑ j ∈ Jtail, |2 * U (j + 1) - U j - U (j + 2)| ≤
      (8 / (D : ℝ)) * tot := by
    have hU_tail : ∀ i : ℕ, 9 * sqrt D * L ≤ |((i - 2 : ℕ) : ℝ) - μ| →
        U i ≤ 2 * tot * exp (-9 * L ^ 2) := by
      intro i hdist
      dsimp [U]
      split_ifs with hi
      · have hle_S2 : i - 2 ≤ S2 := by
          have : D ≤ S2 := by
            have : (D : ℝ) ≤ S2 := by linarith
            exact_mod_cast this
          omega
        have hut := hypergeom_universal_tail D M2 S2 (i - 2) (by omega) hle_S2
        have hexp : exp (-(((i - 2 : ℕ) : ℝ) - μ) ^ 2 / (8 * D)) ≤ exp (-9 * L ^ 2) := by
          apply exp_le_exp.mpr
          have hsq : (9 * sqrt D * L) ^ 2 ≤ (((i - 2 : ℕ) : ℝ) - μ) ^ 2 := by
            rw [← sq_abs (((i - 2 : ℕ) : ℝ) - μ)]
            exact pow_le_pow_left₀ (by positivity) hdist 2
          have h81 : (9 * sqrt D * L) ^ 2 = 81 * (D : ℝ) * L ^ 2 := by
            rw [mul_pow, mul_pow, sq_sqrt hD_pos.le]; ring
          rw [show (-9 : ℝ) * L ^ 2 = -(9 * L ^ 2) by ring, neg_div, neg_le_neg_iff,
            le_div_iff₀ (by positivity : (0 : ℝ) < 8 * D)]
          have hnn : 0 ≤ (D : ℝ) * L ^ 2 := by positivity
          linarith only [hsq, h81, hnn]
        exact hut.trans (mL hexp (by positivity))
      · positivity
    have hpt : ∀ j ∈ Jtail, |2 * U (j + 1) - U j - U (j + 2)| ≤
        8 * tot * exp (-9 * L ^ 2) := by
      intro j hj
      obtain ⟨hj_rng, hnot⟩ := mem_filter.mp hj
      have hj_le : j < D + 3 := mem_range.mp hj_rng
      have hDR : (100 : ℝ) ≤ D := by exact_mod_cast hD
      have hdist_all : ∀ i : ℕ, (i = j ∨ i = j + 1 ∨ i = j + 2) →
          2 ≤ i ∧ i ≤ D + 2 → 9 * sqrt D * L ≤ |((i - 2 : ℕ) : ℝ) - μ| := by
        intro i hi hrange
        have hμ_lo : (1 / 2 : ℝ) * D ≤ μ := by
          dsimp [μ]; rw [le_div_iff₀ hDM_pos]
          have := mL hη_lo hD_pos.le; linarith only [this]
        have hμ_hi : μ ≤ (4 / 5 : ℝ) * D := by
          dsimp [μ]; rw [div_le_iff₀ hDM_pos]
          have := mL hη_hi hD_pos.le; linarith only [this]
        have hsq_ge : 10 ≤ sqrt D := by
          rw [le_sqrt (by norm_num) hD_pos.le]; exact_mod_cast hD
        by_cases hj_lo : j < 2
        · -- i - 2 ≤ 1 while μ ≥ D/2 ≥ 50, W ≤ D/10
          have hi2 : ((i - 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show i - 2 ≤ 1 by omega)
          have h1 : 9 * sqrt D * L ≤ μ - ((i - 2 : ℕ) : ℝ) := by
            have hnn : 0 ≤ sqrt D * L := by positivity
            linarith only [hμ_lo, hW, hi2, hDR, hnn]
          exact h1.trans (by rw [abs_sub_comm]; exact le_abs_self _)
        · by_cases hj_hi : D < j
          · -- i - 2 ≥ D - 1 while μ ≤ 4D/5, W ≤ D/10
            have hi2 : (D : ℝ) - 1 ≤ ((i - 2 : ℕ) : ℝ) := by
              have hnat : D - 1 ≤ i - 2 := by omega
              have hR : ((D - 1 : ℕ) : ℝ) ≤ ((i - 2 : ℕ) : ℝ) := by exact_mod_cast hnat
              rw [Nat.cast_sub (by omega : 1 ≤ D)] at hR; push_cast at hR; linarith
            have h1 : 9 * sqrt D * L ≤ ((i - 2 : ℕ) : ℝ) - μ := by
              have hnn : 0 ≤ sqrt D * L := by positivity
              linarith only [hμ_hi, hW, hi2, hDR, hnn]
            exact h1.trans (le_abs_self _)
          · -- 2 ≤ j ≤ D, so |((j - 1) : ℝ) - μ| > W = 10 * √D * L
            have hgt : W < |((j - 1 : ℕ) : ℝ) - μ| := by
              by_contra hle; exact hnot ⟨by omega, by omega, not_lt.mp hle⟩
            have hdiff : |((i - 2 : ℕ) : ℝ) - ((j - 1 : ℕ) : ℝ)| ≤ 1 := by
              rcases hi with hi0 | hi1 | hi2
              · have : i - 2 + 1 = j - 1 := by omega
                have hR : ((i - 2 : ℕ) : ℝ) + 1 = ((j - 1 : ℕ) : ℝ) := by exact_mod_cast this
                rw [abs_le]; constructor <;> linarith only [hR]
              · have : i - 2 = j - 1 := by omega
                rw [this, sub_self, abs_zero]; norm_num
              · have : i - 2 = (j - 1) + 1 := by omega
                have hR : ((i - 2 : ℕ) : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast this
                rw [abs_le]; constructor <;> linarith only [hR]
            have htri : |((j - 1 : ℕ) : ℝ) - μ| ≤
                |((i - 2 : ℕ) : ℝ) - ((j - 1 : ℕ) : ℝ)| + |((i - 2 : ℕ) : ℝ) - μ| := by
              have := abs_sub_le ((j - 1 : ℕ) : ℝ) ((i - 2 : ℕ) : ℝ) μ
              rw [abs_sub_comm ((j - 1 : ℕ) : ℝ) ((i - 2 : ℕ) : ℝ)] at this
              exact this
            have h1 : 1 ≤ sqrt D * L := by
              have := mul_le_mul hsq_ge hL (by norm_num) (by positivity)
              linarith only [this]
            dsimp [W] at hgt; linarith only [hgt, hdiff, htri, h1]
      have hU_le : ∀ i : ℕ, (i = j ∨ i = j + 1 ∨ i = j + 2) →
          U i ≤ 2 * tot * exp (-9 * L ^ 2) := by
        intro i hi
        by_cases hr : 2 ≤ i ∧ i ≤ D + 2
        · exact hU_tail i (hdist_all i hi hr)
        · dsimp [U]; rw [if_neg hr]; positivity
      have hb0 := hU_le j (Or.inl rfl)
      have hb1 := hU_le (j + 1) (Or.inr (Or.inl rfl))
      have hb2 := hU_le (j + 2) (Or.inr (Or.inr rfl))
      have htri : |2 * U (j + 1) - U j - U (j + 2)| ≤ 2 * U (j + 1) + U j + U (j + 2) := by
        rw [abs_le]; constructor <;> linarith only [hU_nn j, hU_nn (j + 1), hU_nn (j + 2)]
      linarith only [htri, hb0, hb1, hb2]
    calc ∑ j ∈ Jtail, |2 * U (j + 1) - U j - U (j + 2)|
        ≤ ∑ _j ∈ Jtail, (8 * tot * exp (-9 * L ^ 2)) := sum_le_sum hpt
      _ = (Jtail.card : ℝ) * (8 * tot * exp (-9 * L ^ 2)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ((D + 3 : ℕ) : ℝ) * (8 * tot * exp (-9 * L ^ 2)) := by
          have hc : Jtail.card ≤ D + 3 := (card_filter_le _ _).trans (by simp)
          have hcR : (Jtail.card : ℝ) ≤ (D + 3 : ℕ) := by exact_mod_cast hc
          exact mR hcR (by positivity)
      _ = 8 * (((D + 3 : ℕ) : ℝ) * exp (-9 * L ^ 2)) * tot := by ring
      _ ≤ 8 * (1 / (D : ℝ)) * tot :=
          mR (mL htail (by norm_num)) htot_nn
      _ = (8 / (D : ℝ)) * tot := by ring
  have hL2 : (4 : ℝ) ≤ L ^ 2 := by nlinarith
  have hcomb : (5500000 * L ^ 2 / (D : ℝ)) + 8 / (D : ℝ) ≤ 8000000 * L ^ 2 / D := by
    rw [← add_div, div_le_div_iff₀ hD_pos hD_pos]
    have hmul := mR hL2 hD_pos.le
    linarith only [hmul]
  have htot_bound : |alt| / 2 ≤ ((5500000 * L ^ 2 / D + 8 / D) / 8) * tot := by
    linarith only [halt_le, hsplit_J, hcent_bound, htail_bound]
  have hfinal : (5500000 * L ^ 2 / D + 8 / D) / 8 ≤ 1000000 * L ^ 2 / D := by
    have hdiv8 : (8000000 * L ^ 2 / (D : ℝ)) / 8 = 1000000 * L ^ 2 / D := by ring
    linarith only [hcomb, hdiv8]
  exact htot_bound.trans (mR hfinal htot_nn)

-- ============================================================================
-- Section 5: MVT Odd-Gaussian Cancellation Lemma (for b, t, and j sums)
-- ============================================================================

private noncomputable def phiG (α x : ℝ) : ℝ := x * exp (-α * x ^ 2)

private lemma hasDerivAt_neg_exp_sq (α x : ℝ) (hα : 0 < α) :
    HasDerivAt (fun t : ℝ => -exp (-α * t ^ 2) / (2 * α)) (phiG α x) x := by
  have h1 : HasDerivAt (fun t : ℝ => -α * t ^ 2) (-2 * α * x) x :=
    ((hasDerivAt_pow 2 x).const_mul (-α)).congr_deriv (by norm_num; ring)
  have h2 : HasDerivAt (fun t : ℝ => exp (-α * t ^ 2))
      (exp (-α * x ^ 2) * (-2 * α * x)) x :=
    (Real.hasDerivAt_exp _).comp x h1
  exact ((h2.neg).div_const (2 * α)).congr_deriv (by unfold phiG; field_simp [hα.ne'])

private lemma hasDerivAt_phiG (α x : ℝ) :
    HasDerivAt (phiG α) ((1 - 2 * α * x ^ 2) * exp (-α * x ^ 2)) x := by
  have h1 : HasDerivAt (fun t : ℝ => -α * t ^ 2) (-2 * α * x) x :=
    ((hasDerivAt_pow 2 x).const_mul (-α)).congr_deriv (by norm_num; ring)
  have h2 : HasDerivAt (fun t : ℝ => exp (-α * t ^ 2))
      (exp (-α * x ^ 2) * (-2 * α * x)) x :=
    (Real.hasDerivAt_exp _).comp x h1
  exact ((hasDerivAt_id x).mul h2).congr_deriv (by simp only [id_eq]; ring)

private lemma abs_deriv_phiG_le (α x : ℝ) (hα : 0 < α) :
    |(1 - 2 * α * x ^ 2) * exp (-α * x ^ 2)| ≤ 5 * exp (-α * x ^ 2 / 2) := by
  let u : ℝ := α * x ^ 2 / 2
  have hu_nn : 0 ≤ u := by dsimp [u]; positivity
  have hu_exp : u * exp (-u) ≤ 1 := by
    have h1 : u ≤ exp u := by linarith [add_one_le_exp u]
    have h2 := mR h1 (exp_pos (-u)).le
    rwa [← exp_add, add_neg_cancel, exp_zero] at h2
  have hexp_split : exp (-α * x ^ 2) = exp (-u) * exp (-u) := by
    rw [← exp_add]; congr 1; dsimp [u]; ring
  have h12 : |1 - 2 * α * x ^ 2| ≤ 1 + 4 * u := by
    rw [abs_le]; dsimp [u]; constructor <;> nlinarith [sq_nonneg x]
  rw [abs_mul, abs_of_pos (exp_pos _), hexp_split]
  have hle : (1 + 4 * u) * exp (-u) ≤ 5 := by
    have h0 : exp (-u) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    linarith
  have hneg : -α * x ^ 2 / 2 = -u := by dsimp [u]; ring
  rw [hneg]
  calc |1 - 2 * α * x ^ 2| * (exp (-u) * exp (-u))
      ≤ (1 + 4 * u) * (exp (-u) * exp (-u)) :=
        mR h12 (by positivity)
    _ = ((1 + 4 * u) * exp (-u)) * exp (-u) := by ring
    _ ≤ 5 * exp (-u) := mR hle (exp_pos _).le

private lemma odd_gaussian_step_mvt {α s : ℝ} (hα : 0 < α) (hs : 0 < s) (hαs : α * s ^ 2 ≤ 1)
    (x : ℝ) :
    |s * phiG α x - ((-exp (-α * (x + s) ^ 2) / (2 * α)) -
      (-exp (-α * x ^ 2) / (2 * α)))| ≤
      10 * s ^ 2 * exp (-α * x ^ 2 / 4) := by
  let F (t : ℝ) : ℝ := -exp (-α * t ^ 2) / (2 * α)
  have hF_cont : Continuous F := by fun_prop
  have hphi_cont : Continuous (phiG α) := by unfold phiG; fun_prop
  obtain ⟨ξ, hξ, hslope1⟩ := exists_hasDerivAt_eq_slope F (phiG α) (by linarith : x < x + s)
    hF_cont.continuousOn (fun t _ => hasDerivAt_neg_exp_sq α t hα)
  have hFdiff : F (x + s) - F x = s * phiG α ξ := by
    have hden : x + s - x = s := by ring
    rw [hden, eq_div_iff hs.ne'] at hslope1
    linarith
  obtain ⟨η, hη, hslope2⟩ := exists_hasDerivAt_eq_slope (phiG α)
    (fun t => (1 - 2 * α * t ^ 2) * exp (-α * t ^ 2)) hξ.1
    hphi_cont.continuousOn (fun t _ => hasDerivAt_phiG α t)
  have hphidiff : phiG α ξ - phiG α x = (ξ - x) * ((1 - 2 * α * η ^ 2) * exp (-α * η ^ 2)) := by
    have hpos : 0 < ξ - x := sub_pos.mpr hξ.1
    rw [eq_div_iff hpos.ne'] at hslope2
    linarith
  have hη_sq : -α * η ^ 2 / 2 ≤ 1 / 2 + (-α * x ^ 2 / 4) := by
    have hdiff : |η - x| ≤ s := by
      rw [abs_le]; constructor <;> linarith [hη.1, hη.2, hξ.2]
    have hsq1 : (η - x) ^ 2 ≤ s ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
    have hsq2 : x ^ 2 / 2 - s ^ 2 ≤ η ^ 2 := by
      nlinarith [sq_nonneg (2 * η - x), hsq1]
    nlinarith
  have hexp_η : exp (-α * η ^ 2 / 2) ≤ 2 * exp (-α * x ^ 2 / 4) := by
    calc exp (-α * η ^ 2 / 2)
        ≤ exp (1 / 2 + (-α * x ^ 2 / 4)) := exp_le_exp.mpr hη_sq
      _ = exp (1 / 2) * exp (-α * x ^ 2 / 4) := exp_add _ _
      _ ≤ 2 * exp (-α * x ^ 2 / 4) :=
          mR exp_half_lt_two.le (exp_pos _).le
  change |s * phiG α x - (F (x + s) - F x)| ≤ _
  rw [hFdiff, show s * phiG α x - s * phiG α ξ = -(s * (phiG α ξ - phiG α x)) by ring,
    abs_neg, abs_mul, abs_of_pos hs, hphidiff, abs_mul, abs_of_pos (sub_pos.mpr hξ.1)]
  have hξ_le : ξ - x ≤ s := by linarith [hξ.2]
  have hderiv_le := abs_deriv_phiG_le α η hα
  calc s * ((ξ - x) * |(1 - 2 * α * η ^ 2) * exp (-α * η ^ 2)|)
      ≤ s * (s * (5 * exp (-α * η ^ 2 / 2))) :=
        mL
          (mul_le_mul hξ_le hderiv_le (abs_nonneg _) hs.le) hs.le
    _ ≤ s * (s * (5 * (2 * exp (-α * x ^ 2 / 4)))) :=
        mL
          (mL
            (mL hexp_η (by norm_num)) hs.le) hs.le
    _ = 10 * s ^ 2 * exp (-α * x ^ 2 / 4) := by ring

private lemma odd_gaussian_sum_mvt {α s : ℝ} (hα : 0 < α) (hs : 0 < s) (hαs : α * s ^ 2 ≤ 1)
    (a0 : ℝ) (N : ℕ) :
    |∑ r ∈ range N, phiG α (a0 + s * (r : ℝ)) -
      (exp (-α * a0 ^ 2) - exp (-α * (a0 + s * (N : ℝ)) ^ 2)) / (2 * α * s)| ≤
      60 * s + 80 / sqrt α := by
  let F (t : ℝ) : ℝ := -exp (-α * t ^ 2) / (2 * α)
  have htele : F (a0 + s * (N : ℝ)) - F a0 =
      ∑ r ∈ range N, (F (a0 + s * ((r + 1 : ℕ) : ℝ)) - F (a0 + s * (r : ℝ))) := by
    have h := sum_range_sub (fun r : ℕ => F (a0 + s * (r : ℝ))) N
    simp only [Nat.cast_zero, mul_zero, add_zero] at h
    exact h.symm
  have hmul :
      |s * ∑ r ∈ range N, phiG α (a0 + s * (r : ℝ)) - (F (a0 + s * (N : ℝ)) - F a0)| ≤
      10 * s ^ 2 * (6 + 8 / (s * sqrt α)) := by
    rw [mul_sum, htele, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ range N, |s * phiG α (a0 + s * (r : ℝ)) -
            (F (a0 + s * ((r + 1 : ℕ) : ℝ)) - F (a0 + s * (r : ℝ)))|
        ≤ ∑ r ∈ range N, 10 * s ^ 2 * exp (-α * (a0 + s * (r : ℝ)) ^ 2 / 4) := by
          apply sum_le_sum; intro r _
          have hstep : a0 + s * ((r + 1 : ℕ) : ℝ) = (a0 + s * (r : ℝ)) + s := by
            push_cast; ring
          rw [hstep]
          exact odd_gaussian_step_mvt hα hs hαs (a0 + s * (r : ℝ))
      _ = 10 * s ^ 2 * ∑ r ∈ range N, exp (-(α * s ^ 2 / 4) * (a0 / s + (r : ℝ)) ^ 2) := by
          rw [← mul_sum]; congr 1
          refine sum_congr rfl fun r _ => ?_
          congr 1; field_simp [hs.ne']
      _ ≤ 10 * s ^ 2 * (6 + 4 / sqrt (α * s ^ 2 / 4)) := by
          apply mL _ (by positivity)
          exact sum_exp_sq_of_step_ge_one N (fun r => a0 / s + (r : ℝ)) (by positivity)
            (fun r => by push_cast; linarith)
      _ = 10 * s ^ 2 * (6 + 8 / (s * sqrt α)) := by
          have hsq : sqrt (α * s ^ 2 / 4) = s * sqrt α / 2 := by
            rw [sqrt_div (by positivity), sqrt_mul hα.le, sqrt_sq hs.le,
              show sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
            ring
          rw [hsq]; field_simp [hs.ne', (sqrt_pos.mpr hα).ne']; ring
  have hdiv :
      (F (a0 + s * (N : ℝ)) - F a0) / s =
      (exp (-α * a0 ^ 2) - exp (-α * (a0 + s * (N : ℝ)) ^ 2)) / (2 * α * s) := by
    dsimp [F]; field_simp [hα.ne', hs.ne']; ring
  have h1 : |∑ r ∈ range N, phiG α (a0 + s * (r : ℝ)) - (F (a0 + s * (N : ℝ)) - F a0) / s| =
      |s * ∑ r ∈ range N, phiG α (a0 + s * (r : ℝ)) - (F (a0 + s * (N : ℝ)) - F a0)| / s := by
    calc |∑ r ∈ range N, phiG α (a0 + s * (r : ℝ)) - (F (a0 + s * (N : ℝ)) - F a0) / s|
        = |(s * ∑ r ∈ range N, phiG α (a0 + s * (r : ℝ)) - (F (a0 + s * (N : ℝ)) - F a0)) / s| := by
          congr 1; field_simp [hs.ne']
      _ = |s * ∑ r ∈ range N, phiG α (a0 + s * (r : ℝ)) - (F (a0 + s * (N : ℝ)) - F a0)| / s := by
          rw [abs_div, abs_of_pos hs]
  rw [← hdiv, h1, div_le_iff₀ hs]
  have hrhs : (60 * s + 80 / sqrt α) * s = 10 * s ^ 2 * (6 + 8 / (s * sqrt α)) := by
    field_simp [hs.ne', (sqrt_pos.mpr hα).ne']; ring
  linarith

private lemma exp_sq_lipschitz {α : ℝ} (hα : 0 < α) (x y : ℝ) :
    |exp (-α * y ^ 2) - exp (-α * x ^ 2)| ≤ 2 * sqrt α * |y - x| := by
  by_cases hxy : x = y
  · subst hxy; simp
  let g (t : ℝ) : ℝ := exp (-α * t ^ 2)
  have hderiv : ∀ t : ℝ, HasDerivAt g (-2 * α * t * exp (-α * t ^ 2)) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => -α * s ^ 2) (-2 * α * t) t :=
      ((hasDerivAt_pow 2 t).const_mul (-α)).congr_deriv (by norm_num; ring)
    exact ((Real.hasDerivAt_exp _).comp t h1).congr_deriv (by ring)
  have hcont : Continuous g := by fun_prop
  have hg'_le : ∀ c : ℝ, |-2 * α * c * exp (-α * c ^ 2)| ≤ 2 * sqrt α := fun c => by
    let u : ℝ := sqrt α * |c|
    have hu_nn : 0 ≤ u := by dsimp [u]; positivity
    have hu_sq : u ^ 2 = α * c ^ 2 := by
      dsimp [u]; rw [mul_pow, sq_sqrt hα.le, sq_abs]
    have h1 : u * exp (-u ^ 2) ≤ 1 := by
      have hle : u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
      have hexp : 1 + u ^ 2 ≤ exp (u ^ 2) := by linarith [add_one_le_exp (u ^ 2)]
      have h2 := mR (hle.trans hexp) (exp_pos (-u ^ 2)).le
      rwa [← exp_add, add_neg_cancel, exp_zero] at h2
    have hrew : |-2 * α * c * exp (-α * c ^ 2)| =
        2 * sqrt α * (u * exp (-u ^ 2)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos hα, abs_of_pos (exp_pos _), hu_sq, show -(α * c ^ 2) = -α * c ^ 2 by ring]
      dsimp [u]
      calc 2 * α * |c| * exp (-α * c ^ 2)
          = 2 * (sqrt α * sqrt α) * |c| * exp (-α * c ^ 2) := by rw [mul_self_sqrt hα.le]
        _ = 2 * sqrt α * (sqrt α * |c| * exp (-α * c ^ 2)) := by ring
    rw [hrew]
    nlinarith [sqrt_nonneg α]
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope g _ hlt
      hcont.continuousOn (fun t _ => hderiv t)
    have heq : g y - g x = (y - x) * (-2 * α * c * exp (-α * c ^ 2)) := by
      rw [eq_div_iff (sub_pos.mpr hlt).ne'] at hslope; linarith
    change |g y - g x| ≤ _
    rw [heq, abs_mul, mul_comm]
    exact mR (hg'_le c) (abs_nonneg _)
  · obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope g _ hgt
      hcont.continuousOn (fun t _ => hderiv t)
    have heq : g y - g x = (y - x) * (-2 * α * c * exp (-α * c ^ 2)) := by
      rw [eq_div_iff (sub_pos.mpr hgt).ne'] at hslope; linarith
    change |g y - g x| ≤ _
    rw [heq, abs_mul, mul_comm]
    exact mR (hg'_le c) (abs_nonneg _)

set_option maxHeartbeats 800000 in
private lemma double_odd_gaussian_sum_bound {α : ℝ} (hα : 0 < α) (hα18 : 18 * α ≤ 1)
    (c : ℝ) (D0 r0 q0 Q T2 : ℕ)
    (hT2 : ∀ q < Q, r0 + 3 * (q0 + q) + D0 + 1 ≤ T2) :
    let x_lo : ℝ := ((r0 + 3 * q0 : ℕ) : ℝ) - c
    let x_hi : ℝ := ((r0 + 3 * (q0 + Q) : ℕ) : ℝ) - c
    let y_hi : ℝ := (T2 : ℝ) - c
    |∑ q ∈ range Q,
      phiG α (((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c) *
        ∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)| ≤
      3000 * ((D0 : ℝ) + 1) / (α * sqrt α) +
        (100 / α ^ 2) * (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2) +
          exp (-α * y_hi ^ 2)) := by
  intro x_lo x_hi y_hi
  have hsqα : 0 < sqrt α := sqrt_pos.mpr hα
  have hsqα_le : sqrt α ≤ 1 := by
    rw [sqrt_le_one]; linarith
  have hsum_abs_phi : ∑ q ∈ range Q, |phiG α (((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c)| ≤ 20 / α := by
    have hpt : ∀ q : ℕ, |phiG α (((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c)| ≤
        (2 / sqrt α) * exp (-(α / 2) * (((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c) ^ 2) := by
      intro q
      let x := ((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c
      let u := sqrt (α / 2) * |x|
      have hu_nn : 0 ≤ u := by dsimp [u]; positivity
      have hu_sq : u ^ 2 = (α / 2) * x ^ 2 := by
        dsimp [u]; rw [mul_pow, sq_sqrt (by positivity), sq_abs]
      have hu_le : u * exp (-u ^ 2) ≤ 1 := by
        have h1 : u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
        have h2 : 1 + u ^ 2 ≤ exp (u ^ 2) := by linarith [add_one_le_exp (u ^ 2)]
        have h3 := mR (h1.trans h2) (exp_pos (-u ^ 2)).le
        rwa [← exp_add, add_neg_cancel, exp_zero] at h3
      have hsq2 : 1 / sqrt (α / 2) ≤ 2 / sqrt α := by
        rw [sqrt_div hα.le, one_div_div, div_le_div_iff₀ hsqα hsqα]
        have : sqrt 2 ≤ 2 := by rw [sqrt_le_left (by norm_num)]; norm_num
        nlinarith
      change |x * exp (-α * x ^ 2)| ≤ (2 / sqrt α) * exp (-(α / 2) * x ^ 2)
      rw [abs_mul, abs_of_pos (exp_pos _)]
      have hsplit : exp (-α * x ^ 2) = exp (-u ^ 2) * exp (-(α / 2) * x ^ 2) := by
        rw [← exp_add]; congr 1; rw [hu_sq]; ring
      rw [hsplit]
      have hxu : |x| = (1 / sqrt (α / 2)) * u := by
        dsimp [u]; field_simp [(sqrt_pos.mpr (by positivity : 0 < α / 2)).ne']
      calc |x| * (exp (-u ^ 2) * exp (-(α / 2) * x ^ 2))
          = (1 / sqrt (α / 2)) * (u * exp (-u ^ 2)) * exp (-(α / 2) * x ^ 2) := by
            rw [hxu]; ring
        _ ≤ (1 / sqrt (α / 2)) * 1 * exp (-(α / 2) * x ^ 2) :=
            mR
              (mL hu_le (by positivity)) (exp_pos _).le
        _ ≤ (2 / sqrt α) * exp (-(α / 2) * x ^ 2) := by
            rw [mul_one]; exact mR hsq2 (exp_pos _).le
    calc ∑ q ∈ range Q, |phiG α (((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c)|
        ≤ ∑ q ∈ range Q, (2 / sqrt α) *
            exp (-(α / 2) * (((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c) ^ 2) :=
          sum_le_sum fun q _ => hpt q
      _ = (2 / sqrt α) * ∑ q ∈ range Q,
            exp (-(α / 2) * (((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c) ^ 2) :=
          (mul_sum _ _ _).symm
      _ ≤ (2 / sqrt α) * (6 + 4 / sqrt (α / 2)) := by
          apply mL _ (by positivity)
          exact sum_exp_sq_of_step_ge_one Q (fun q => ((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c)
            (by positivity) (fun q => by push_cast; linarith)
      _ ≤ 20 / α := by
          have hsq2 : 4 / sqrt (α / 2) ≤ 6 / sqrt α := by
            rw [sqrt_div hα.le, div_div_eq_mul_div, div_le_div_iff₀ hsqα hsqα]
            have : sqrt 2 ≤ 3 / 2 := by rw [sqrt_le_left (by norm_num)]; norm_num
            nlinarith
          have h6 : (6 : ℝ) ≤ 4 / sqrt α := by
            rw [le_div_iff₀ hsqα]
            have : sqrt α ≤ 1 / 4 := by
              rw [sqrt_le_left (by norm_num)]; linarith
            linarith
          have h46 : 4 / sqrt α + 6 / sqrt α = 10 / sqrt α := by ring
          have hmul : (2 / sqrt α) * (6 + 4 / sqrt (α / 2)) ≤
              (2 / sqrt α) * (10 / sqrt α) :=
            mL (by linarith [h6, hsq2, h46]) (by positivity)
          have hsq : (2 / sqrt α) * (10 / sqrt α) = 20 / α := by
            rw [div_mul_div_comm, mul_self_sqrt hα.le]; ring
          linarith
  let x (q : ℕ) : ℝ := ((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c
  have hinner_approx : ∀ q ∈ range Q,
      |(∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
        exp (-α * (x q) ^ 2) / (2 * α)| ≤
      (100 + ((D0 : ℝ) + 1)) / sqrt α + exp (-α * y_hi ^ 2) / (2 * α) := by
    intro q hq
    have hqQ : q < Q := mem_range.mp hq
    have hle : r0 + 3 * (q0 + q) + D0 + 1 ≤ T2 := hT2 q hqQ
    let a0 : ℝ := ((r0 + 3 * (q0 + q) + D0 + 1 : ℕ) : ℝ) - c
    let N : ℕ := T2 - (r0 + 3 * (q0 + q) + D0 + 1)
    have hIco : ∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c) =
        ∑ r ∈ range N, phiG α (a0 + 1 * (r : ℝ)) := by
      have hbij : Ico (r0 + 3 * (q0 + q) + D0 + 1) T2 =
          (range N).image (fun r => r0 + 3 * (q0 + q) + D0 + 1 + r) := by
        ext t; simp only [mem_Ico, mem_image, mem_range]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨t - (r0 + 3 * (q0 + q) + D0 + 1), by omega, by omega⟩
        · rintro ⟨r, hr, rfl⟩; omega
      rw [hbij, sum_image (fun a _ b _ h => by omega)]
      refine sum_congr rfl fun r _ => ?_
      congr 1; dsimp [a0]; push_cast; ring
    have hmvt := odd_gaussian_sum_mvt hα (by norm_num : (0 : ℝ) < 1) (by linarith) a0 N
    have ha0N : a0 + 1 * (N : ℝ) = y_hi := by
      dsimp [a0, N, y_hi]; rw [Nat.cast_sub hle]; push_cast; ring
    rw [← hIco, ha0N, mul_one] at hmvt
    have hshift : |exp (-α * a0 ^ 2) / (2 * α) - exp (-α * (x q) ^ 2) / (2 * α)| ≤
        ((D0 : ℝ) + 1) / sqrt α := by
      rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * α)]
      have hlip := exp_sq_lipschitz hα (x q) a0
      have hdiff : |a0 - x q| = (D0 : ℝ) + 1 := by
        have : a0 - x q = (D0 : ℝ) + 1 := by dsimp [a0, x]; push_cast; ring
        rw [this, abs_of_pos (by positivity)]
      rw [hdiff] at hlip
      have hdiv : 2 * sqrt α * ((D0 : ℝ) + 1) / (2 * α) = ((D0 : ℝ) + 1) / sqrt α := by
        have hsq : sqrt α * sqrt α = α := mul_self_sqrt hα.le
        field_simp [hα.ne', hsqα.ne']; nlinarith [hsq]
      calc |exp (-α * a0 ^ 2) - exp (-α * (x q) ^ 2)| / (2 * α)
          ≤ (2 * sqrt α * ((D0 : ℝ) + 1)) / (2 * α) :=
            dR hlip (by positivity)
        _ = ((D0 : ℝ) + 1) / sqrt α := hdiv
    have h60 : (60 : ℝ) * 1 + 80 / sqrt α ≤ 100 / sqrt α := by
      have : 60 * sqrt α ≤ 20 := by
        have : sqrt α ≤ 1 / 4 := by rw [sqrt_le_left (by norm_num)]; linarith
        linarith
      have h20 : (60 : ℝ) ≤ 20 / sqrt α := by rw [le_div_iff₀ hsqα]; linarith
      have hadd : 20 / sqrt α + 80 / sqrt α = 100 / sqrt α := by ring
      linarith
    have htri : |(∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
        exp (-α * (x q) ^ 2) / (2 * α)| ≤
        |(∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
          (exp (-α * a0 ^ 2) - exp (-α * y_hi ^ 2)) / (2 * α)| +
        |exp (-α * a0 ^ 2) / (2 * α) - exp (-α * (x q) ^ 2) / (2 * α)| +
        exp (-α * y_hi ^ 2) / (2 * α) := by
      have heq : (∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
          exp (-α * (x q) ^ 2) / (2 * α) =
          ((∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
            (exp (-α * a0 ^ 2) - exp (-α * y_hi ^ 2)) / (2 * α)) +
          (exp (-α * a0 ^ 2) / (2 * α) - exp (-α * (x q) ^ 2) / (2 * α)) -
          exp (-α * y_hi ^ 2) / (2 * α) := by ring
      rw [heq]
      have h1 := abs_sub ((∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
            (exp (-α * a0 ^ 2) - exp (-α * y_hi ^ 2)) / (2 * α) +
          (exp (-α * a0 ^ 2) / (2 * α) - exp (-α * (x q) ^ 2) / (2 * α)))
          (exp (-α * y_hi ^ 2) / (2 * α))
      have h2 := abs_add_le
          ((∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
            (exp (-α * a0 ^ 2) - exp (-α * y_hi ^ 2)) / (2 * α))
          (exp (-α * a0 ^ 2) / (2 * α) - exp (-α * (x q) ^ 2) / (2 * α))
      rw [abs_of_pos (by positivity : 0 < exp (-α * y_hi ^ 2) / (2 * α))] at h1
      linarith
    have hadd : 100 / sqrt α + ((D0 : ℝ) + 1) / sqrt α =
        (100 + ((D0 : ℝ) + 1)) / sqrt α := by ring
    linarith
  have hmain_eq : ∑ q ∈ range Q, phiG α (x q) * (exp (-α * (x q) ^ 2) / (2 * α)) =
      (1 / (2 * α)) * ∑ q ∈ range Q, phiG (2 * α) (x_lo + 3 * (q : ℝ)) := by
    rw [mul_sum]
    refine sum_congr rfl fun q _ => ?_
    have hxq : x q = x_lo + 3 * (q : ℝ) := by dsimp [x, x_lo]; push_cast; ring
    rw [hxq]; dsimp [phiG]
    have hexp : exp (-α * (x_lo + 3 * (q : ℝ)) ^ 2) * exp (-α * (x_lo + 3 * (q : ℝ)) ^ 2) =
        exp (-(2 * α) * (x_lo + 3 * (q : ℝ)) ^ 2) := by
      rw [← exp_add]; congr 1; ring
    have : (x_lo + 3 * (q : ℝ)) * exp (-α * (x_lo + 3 * (q : ℝ)) ^ 2) *
        (exp (-α * (x_lo + 3 * (q : ℝ)) ^ 2) / (2 * α)) =
        (1 / (2 * α)) * ((x_lo + 3 * (q : ℝ)) *
          (exp (-α * (x_lo + 3 * (q : ℝ)) ^ 2) * exp (-α * (x_lo + 3 * (q : ℝ)) ^ 2))) := by
      ring
    rw [this, hexp]
  have hmain_bound : |∑ q ∈ range Q, phiG α (x q) * (exp (-α * (x q) ^ 2) / (2 * α))| ≤
      200 / (α * sqrt α) +
        (1 / α ^ 2) * (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2)) := by
    rw [hmain_eq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * α))]
    have hmvt := odd_gaussian_sum_mvt (by positivity : 0 < 2 * α) (by norm_num : (0 : ℝ) < 3)
      (by linarith : (2 * α) * 3 ^ 2 ≤ 1) x_lo Q
    have hxhi : x_lo + 3 * (Q : ℝ) = x_hi := by dsimp [x_lo, x_hi]; push_cast; ring
    rw [hxhi] at hmvt
    have hsum_le : |∑ q ∈ range Q, phiG (2 * α) (x_lo + 3 * (q : ℝ))| ≤
        (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2)) / (12 * α) +
          (60 * 3 + 80 / sqrt (2 * α)) := by
      have htri : |∑ q ∈ range Q, phiG (2 * α) (x_lo + 3 * (q : ℝ))| ≤
          |∑ q ∈ range Q, phiG (2 * α) (x_lo + 3 * (q : ℝ)) -
            (exp (-(2 * α) * x_lo ^ 2) - exp (-(2 * α) * x_hi ^ 2)) / (2 * (2 * α) * 3)| +
          |(exp (-(2 * α) * x_lo ^ 2) - exp (-(2 * α) * x_hi ^ 2)) / (2 * (2 * α) * 3)| := by
        have := abs_add_le
          (∑ q ∈ range Q, phiG (2 * α) (x_lo + 3 * (q : ℝ)) -
            (exp (-(2 * α) * x_lo ^ 2) - exp (-(2 * α) * x_hi ^ 2)) / (2 * (2 * α) * 3))
          ((exp (-(2 * α) * x_lo ^ 2) - exp (-(2 * α) * x_hi ^ 2)) / (2 * (2 * α) * 3))
        simpa using this
      have hbnd : |(exp (-(2 * α) * x_lo ^ 2) - exp (-(2 * α) * x_hi ^ 2)) /
          (2 * (2 * α) * 3)| ≤ (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2)) / (12 * α) := by
        rw [abs_div, abs_of_pos (by positivity : 0 < 2 * (2 * α) * 3)]
        have h1 : |exp (-(2 * α) * x_lo ^ 2) - exp (-(2 * α) * x_hi ^ 2)| ≤
            exp (-(2 * α) * x_lo ^ 2) + exp (-(2 * α) * x_hi ^ 2) := by
          rw [abs_le]; constructor <;> linarith [exp_pos (-(2 * α) * x_lo ^ 2),
            exp_pos (-(2 * α) * x_hi ^ 2)]
        have h2 : exp (-(2 * α) * x_lo ^ 2) ≤ exp (-α * x_lo ^ 2) :=
          exp_le_exp.mpr (by nlinarith [sq_nonneg x_lo])
        have h3 : exp (-(2 * α) * x_hi ^ 2) ≤ exp (-α * x_hi ^ 2) :=
          exp_le_exp.mpr (by nlinarith [sq_nonneg x_hi])
        rw [show 2 * (2 * α) * 3 = 12 * α by ring]
        exact dR (by linarith) (by positivity)
      linarith
    have h180 : 60 * 3 + 80 / sqrt (2 * α) ≤ 400 / sqrt α := by
      have hsq2 : 80 / sqrt (2 * α) ≤ 80 / sqrt α := by
        apply div_le_div_of_nonneg_left (by norm_num) hsqα
        exact sqrt_le_sqrt (by linarith)
      have h180' : (180 : ℝ) ≤ 320 / sqrt α := by
        rw [le_div_iff₀ hsqα]
        have : sqrt α ≤ 1 / 4 := by rw [sqrt_le_left (by norm_num)]; linarith
        linarith
      have hadd : 320 / sqrt α + 80 / sqrt α = 400 / sqrt α := by ring
      linarith
    calc (1 / (2 * α)) * |∑ q ∈ range Q, phiG (2 * α) (x_lo + 3 * (q : ℝ))|
        ≤ (1 / (2 * α)) * ((exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2)) / (12 * α) +
            400 / sqrt α) :=
          mL (by linarith) (by positivity)
      _ = 200 / (α * sqrt α) +
          (1 / (24 * α ^ 2)) * (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2)) := by
          field_simp [hα.ne', hsqα.ne']; ring
      _ ≤ 200 / (α * sqrt α) +
          (1 / α ^ 2) * (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2)) := by
          have hnn : 0 ≤ exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2) := by positivity
          have h124 : 1 / (24 * α ^ 2) ≤ 1 / α ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
          nlinarith
  have herr_bound :
      |∑ q ∈ range Q, phiG α (x q) *
          ((∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
            exp (-α * (x q) ^ 2) / (2 * α))| ≤
      (20 / α) * ((100 + ((D0 : ℝ) + 1)) / sqrt α + exp (-α * y_hi ^ 2) / (2 * α)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ q ∈ range Q, |phiG α (x q) *
            ((∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
              exp (-α * (x q) ^ 2) / (2 * α))|
        ≤ ∑ q ∈ range Q, |phiG α (x q)| *
            ((100 + ((D0 : ℝ) + 1)) / sqrt α + exp (-α * y_hi ^ 2) / (2 * α)) := by
          apply sum_le_sum; intro q hq
          rw [abs_mul]
          exact mL (hinner_approx q hq) (abs_nonneg _)
      _ = (∑ q ∈ range Q, |phiG α (x q)|) *
            ((100 + ((D0 : ℝ) + 1)) / sqrt α + exp (-α * y_hi ^ 2) / (2 * α)) :=
          (sum_mul _ _ _).symm
      _ ≤ (20 / α) * ((100 + ((D0 : ℝ) + 1)) / sqrt α + exp (-α * y_hi ^ 2) / (2 * α)) :=
          mR hsum_abs_phi (by positivity)
  have hsplit_tot :
      (∑ q ∈ range Q, phiG α (x q) *
        ∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) =
      (∑ q ∈ range Q, phiG α (x q) *
        ((∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
          exp (-α * (x q) ^ 2) / (2 * α))) +
      (∑ q ∈ range Q, phiG α (x q) * (exp (-α * (x q) ^ 2) / (2 * α))) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun q _ => ?_; ring
  change |∑ q ∈ range Q, phiG α (x q) *
    ∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)| ≤ _
  rw [hsplit_tot]
  have htri := abs_add_le
    (∑ q ∈ range Q, phiG α (x q) *
      ((∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) T2, phiG α ((t : ℝ) - c)) -
        exp (-α * (x q) ^ 2) / (2 * α)))
    (∑ q ∈ range Q, phiG α (x q) * (exp (-α * (x q) ^ 2) / (2 * α)))
  have hcomb :
      (20 / α) * ((100 + ((D0 : ℝ) + 1)) / sqrt α + exp (-α * y_hi ^ 2) / (2 * α)) +
      (200 / (α * sqrt α) +
        (1 / α ^ 2) * (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2))) ≤
      3000 * ((D0 : ℝ) + 1) / (α * sqrt α) +
        (100 / α ^ 2) * (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2) +
          exp (-α * y_hi ^ 2)) := by
    have heq1 : (20 / α) * ((100 + ((D0 : ℝ) + 1)) / sqrt α +
        exp (-α * y_hi ^ 2) / (2 * α)) =
        (2000 + 20 * ((D0 : ℝ) + 1)) / (α * sqrt α) +
        (10 / α ^ 2) * exp (-α * y_hi ^ 2) := by
      field_simp [hα.ne', hsqα.ne']; ring
    have hD0_ge : (1 : ℝ) ≤ (D0 : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) D0]
    have hpart1 : (2000 + 20 * ((D0 : ℝ) + 1)) / (α * sqrt α) + 200 / (α * sqrt α) ≤
        3000 * ((D0 : ℝ) + 1) / (α * sqrt α) := by
      rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hD0_ge, mul_pos hα hsqα]
    have hpart2 : (10 / α ^ 2) * exp (-α * y_hi ^ 2) +
        (1 / α ^ 2) * (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2)) ≤
        (100 / α ^ 2) * (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2) +
          exp (-α * y_hi ^ 2)) := by
      have h1 : 0 ≤ exp (-α * x_lo ^ 2) / α ^ 2 := by positivity
      have h2 : 0 ≤ exp (-α * x_hi ^ 2) / α ^ 2 := by positivity
      have h3 : 0 ≤ exp (-α * y_hi ^ 2) / α ^ 2 := by positivity
      have he1 : (10 / α ^ 2) * exp (-α * y_hi ^ 2) +
          (1 / α ^ 2) * (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2)) =
          1 * (exp (-α * x_lo ^ 2) / α ^ 2) + 1 * (exp (-α * x_hi ^ 2) / α ^ 2) +
          10 * (exp (-α * y_hi ^ 2) / α ^ 2) := by ring
      have he2 : (100 / α ^ 2) * (exp (-α * x_lo ^ 2) + exp (-α * x_hi ^ 2) +
          exp (-α * y_hi ^ 2)) =
          100 * (exp (-α * x_lo ^ 2) / α ^ 2) + 100 * (exp (-α * x_hi ^ 2) / α ^ 2) +
          100 * (exp (-α * y_hi ^ 2) / α ^ 2) := by ring
      linarith
    linarith
  linarith

-- ============================================================================
-- Section 6: Regime 2 (t - j > D0) Gaussian approximations and cancellation
-- ============================================================================

private lemma abs_sub_exp_of_log_approx {X Y ε : ℝ} (hX : 0 < X)
    (hlog : |log X - Y| ≤ ε) (hε : ε ≤ 1 / 2) :
    |X - exp Y| ≤ 2 * ε * exp Y := by
  have heq : X - exp Y = exp Y * (exp (log X - Y) - 1) := by
    rw [mul_sub, mul_one, ← exp_add, add_sub_cancel, exp_log hX]
  rw [heq, abs_mul, abs_of_pos (exp_pos Y)]
  have h1 := abs_exp_sub_one_le (hlog.trans hε)
  calc exp Y * |exp (log X - Y) - 1|
      ≤ exp Y * (2 * |log X - Y|) := mL h1 (exp_pos Y).le
    _ ≤ exp Y * (2 * ε) := mL (by linarith) (exp_pos Y).le
    _ = 2 * ε * exp Y := by ring

private def ValidMF (k m f : ℕ) : Prop :=
  10 ^ 6 ≤ k ∧
  10 ^ 20 ≤ log k ∧
  log k ^ 15 / sqrt k ≤ 1 / 10 ^ 6 ∧
  (k : ℝ) ^ 10 * exp (-log k ^ 2) ≤ 1 ∧
  |(m : ℝ) - 2 * k| ≤ sqrt k * log k ∧
  |(f : ℝ) - 2 * (k : ℝ) / 3| ≤ sqrt k * log k

private noncomputable def cK_val (k m f d : ℕ) : ℝ :=
  let Nk : ℝ := (k : ℝ) + (f : ℝ) / 2
  let Rk : ℝ := (m : ℝ) / 2
  let ηk : ℝ := Rk / Nk
  (if d = 0 then ηk / (1 - ηk) else ηk) * exp (2 * logG Nk Rk)

private noncomputable def cM_val (m f d1 : ℕ) : ℝ :=
  let Nm : ℝ := (m : ℝ) / 2
  let Rm : ℝ := (f : ℝ)
  let ηm : ℝ := Rm / Nm
  (if d1 = 0 then (1 - ηm) / ηm else 1) * exp (2 * logG Nm Rm)

private noncomputable def cC_val (m f d2 : ℕ) : ℝ :=
  let ηm : ℝ := (f : ℝ) / ((m : ℝ) / 2)
  if d2 = 0 then 1 - ηm else ηm

private noncomputable def δ_coord (m j : ℕ) : ℝ :=
  (j : ℝ) - (m : ℝ) / 2

private noncomputable def ε_coord (m f j a : ℕ) : ℝ :=
  (a : ℝ) - ((j : ℝ) / 3 + (f : ℝ) / 2 - (m : ℝ) / 6)

private noncomputable def αk_val (k : ℕ) : ℝ :=
  9 / (4 * (k : ℝ))

private lemma validMF_pow_le {k m f : ℕ} (hV : ValidMF k m f) (p : ℕ) (hp : p ≤ 15) :
    log k ^ p / sqrt k ≤ 1 / 10 ^ 6 := by
  obtain ⟨hk, hL, hL15, _, _, _⟩ := hV
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsq : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hpow : log k ^ p ≤ log k ^ 15 :=
    pow_le_pow_right₀ (by linarith) hp
  exact (dR hpow hsq.le).trans hL15

private lemma validMF_sqL_le {k m f : ℕ} (hV : ValidMF k m f) :
    sqrt k * log k ≤ (k : ℝ) / 10 ^ 6 := by
  have h1 := validMF_pow_le hV 1 (by omega)
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := hV.1; omega)
  have hsq : 0 < sqrt k := sqrt_pos.mpr hk_pos
  rw [pow_one, div_le_div_iff₀ hsq (by norm_num)] at h1
  have hmul := mL h1 hsq.le
  rw [show sqrt k * (log k * 10 ^ 6) =
      (sqrt k * log k) * 10 ^ 6 by ring,
    show sqrt k * (1 * sqrt k) = (k : ℝ) by
      rw [one_mul, mul_self_sqrt hk_pos.le]] at hmul
  linarith

private lemma validMF_eta_bounds {k m f : ℕ} (hV : ValidMF k m f) :
    (199 / 100 : ℝ) * k ≤ m ∧ (m : ℝ) ≤ (201 / 100 : ℝ) * k ∧
    (66 / 100 : ℝ) * k ≤ f ∧ (f : ℝ) ≤ (67 / 100 : ℝ) * k ∧
    |((m : ℝ) / 2) / ((k : ℝ) + (f : ℝ) / 2) - 3 / 4| ≤ 2 * log k / sqrt k ∧
    |(f : ℝ) / ((m : ℝ) / 2) - 2 / 3| ≤ 2 * log k / sqrt k := by
  let L := log k
  let Nk : ℝ := (k : ℝ) + (f : ℝ) / 2
  let Rk : ℝ := (m : ℝ) / 2
  let Nm : ℝ := (m : ℝ) / 2
  let Rm : ℝ := (f : ℝ)
  have hsqL := validMF_sqL_le hV
  have ⟨hk, hL, _, _, hm, hf⟩ := hV
  change |(m : ℝ) - 2 * k| ≤ sqrt k * L at hm
  change |(f : ℝ) - 2 * (k : ℝ) / 3| ≤ sqrt k * L at hf
  change 10 ^ 20 ≤ L at hL
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hm1 : (199 / 100 : ℝ) * k ≤ m := by linarith [(abs_le.mp hm).1]
  have hm2 : (m : ℝ) ≤ (201 / 100 : ℝ) * k := by linarith [(abs_le.mp hm).2]
  have hf1 : (66 / 100 : ℝ) * k ≤ f := by linarith [(abs_le.mp hf).1]
  have hf2 : (f : ℝ) ≤ (67 / 100 : ℝ) * k := by linarith [(abs_le.mp hf).2]
  have hNk_lo : (13 / 10 : ℝ) * k ≤ Nk := by dsimp [Nk]; linarith
  have hNk_pos : 0 < Nk := by linarith
  have hNm_lo : (9 / 10 : ℝ) * k ≤ Nm := by dsimp [Nm]; linarith
  have hNm_pos : 0 < Nm := by linarith
  have hm_ne : (m : ℝ) ≠ 0 := by linarith
  have hηk : |Rk / Nk - 3 / 4| ≤ 2 * L / sqrt k := by
    have heq : Rk / Nk - 3 / 4 = ((m : ℝ) - 2 * k - (3 / 4) * ((f : ℝ) - 2 * k / 3)) / (2 * Nk) := by
      dsimp [Rk, Nk]; field_simp [hNk_pos.ne']; ring
    rw [heq, abs_div, abs_of_pos (by positivity : 0 < 2 * Nk)]
    have hnum : |(m : ℝ) - 2 * k - (3 / 4) * ((f : ℝ) - 2 * k / 3)| ≤ 2 * sqrt k * L := by
      have htri := abs_sub ((m : ℝ) - 2 * k) ((3 / 4) * ((f : ℝ) - 2 * k / 3))
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)] at htri
      have hpos : 0 ≤ sqrt k * L := by positivity
      have hass : 2 * sqrt k * L = 2 * (sqrt k * L) := by ring
      linarith only [htri, hm, hf, hpos, hass]
    rw [div_le_div_iff₀ (by positivity) hsq_pos]
    have hmul : 2 * sqrt k * L * sqrt k = 2 * k * L := by
      calc 2 * sqrt k * L * sqrt k
          = 2 * (sqrt k * sqrt k) * L := by ring
        _ = 2 * k * L := by rw [mul_self_sqrt hk_pos.le]
    calc |(m : ℝ) - 2 * k - (3 / 4) * ((f : ℝ) - 2 * k / 3)| * sqrt k
        ≤ (2 * sqrt k * L) * sqrt k :=
          mR hnum hsq_pos.le
      _ = 2 * k * L := hmul
      _ ≤ 2 * L * (2 * Nk) := by
          have := mL (show (k : ℝ) ≤ 2 * Nk by linarith) (by linarith : 0 ≤ 2 * L)
          linarith
  have hηm : |Rm / Nm - 2 / 3| ≤ 2 * L / sqrt k := by
    have heq : Rm / Nm - 2 / 3 = ((f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k)) / Nm := by
      dsimp [Rm, Nm]; field_simp [hm_ne]; ring
    rw [heq, abs_div, abs_of_pos hNm_pos]
    have hnum : |(f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k)| ≤ (3 / 2) * sqrt k * L := by
      have htri := abs_sub ((f : ℝ) - 2 * k / 3) ((1 / 3) * ((m : ℝ) - 2 * k))
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] at htri
      have hpos : 0 ≤ sqrt k * L := by positivity
      have hass : (3 / 2) * sqrt k * L = (3 / 2) * (sqrt k * L) := by ring
      linarith only [htri, hm, hf, hpos, hass]
    rw [div_le_div_iff₀ hNm_pos hsq_pos]
    have hmul : (3 / 2) * sqrt k * L * sqrt k = (3 / 2) * k * L := by
      calc (3 / 2) * sqrt k * L * sqrt k
          = (3 / 2) * (sqrt k * sqrt k) * L := by ring
        _ = (3 / 2) * k * L := by rw [mul_self_sqrt hk_pos.le]
    calc |(f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k)| * sqrt k
        ≤ ((3 / 2) * sqrt k * L) * sqrt k :=
          mR hnum hsq_pos.le
      _ = (3 / 2) * k * L := hmul
      _ ≤ 2 * L * Nm := by
          have := mL (show (3 / 4 : ℝ) * k ≤ Nm by linarith) (by linarith : 0 ≤ 2 * L)
          linarith
  exact ⟨hm1, hm2, hf1, hf2, hηk, hηm⟩

set_option maxHeartbeats 800000 in
private lemma cK_cM_bounds {k m f : ℕ} (hV : ValidMF k m f) {d : ℕ} (hd : d ∈ ({0, 1} : Finset ℕ)) :
    0 < cK_val k m f d ∧ cK_val k m f d ≤ 10 * (((2 * k + 1 + f).choose m : ℕ) : ℝ) / sqrt k ∧
    0 < cM_val m f d ∧ cM_val m f d ≤ 10 * (((m + 1).choose (2 * f + 1) : ℕ) : ℝ) / sqrt k ∧
    0 < cC_val m f d ∧ cC_val m f d ≤ 1 := by
  have hb := validMF_eta_bounds hV
  have hL1 := validMF_pow_le hV 1 (by omega)
  rw [pow_one] at hL1
  have h2L1 : 2 * log k / sqrt k ≤ 2 / 10 ^ 6 := by
    rw [mul_div_assoc]; linarith only [hL1]
  have ⟨hk, hL, _, _, _, _⟩ := hV
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  let Nk : ℝ := (k : ℝ) + (f : ℝ) / 2
  let Rk : ℝ := (m : ℝ) / 2
  let ηk : ℝ := Rk / Nk
  let Nm : ℝ := (m : ℝ) / 2
  let Rm : ℝ := (f : ℝ)
  let ηm : ℝ := Rm / Nm
  have hNk_lo : (13 / 10 : ℝ) * k ≤ Nk := by dsimp [Nk]; linarith only [hb.2.2.1, hk_pos]
  have hNk_hi : Nk ≤ (14 / 10 : ℝ) * k := by dsimp [Nk]; linarith only [hb.2.2.2.1, hk_pos]
  have hNm_lo : (9 / 10 : ℝ) * k ≤ Nm := by dsimp [Nm]; linarith only [hb.1, hk_pos]
  have hNm_hi : Nm ≤ (11 / 10 : ℝ) * k := by dsimp [Nm]; linarith only [hb.2.1, hk_pos]
  have hηk_lo : (7 / 10 : ℝ) ≤ ηk := by dsimp [ηk, Rk, Nk]; linarith only [(abs_le.mp hb.2.2.2.2.1).1, h2L1]
  have hηk_hi : ηk ≤ (8 / 10 : ℝ) := by dsimp [ηk, Rk, Nk]; linarith only [(abs_le.mp hb.2.2.2.2.1).2, h2L1]
  have hηm_lo : (6 / 10 : ℝ) ≤ ηm := by dsimp [ηm, Rm, Nm]; linarith only [(abs_le.mp hb.2.2.2.2.2).1, h2L1]
  have hηm_hi : ηm ≤ (7 / 10 : ℝ) := by dsimp [ηm, Rm, Nm]; linarith only [(abs_le.mp hb.2.2.2.2.2).2, h2L1]
  have hRk_eq : Rk = ηk * Nk := by dsimp [ηk]; field_simp [show Nk ≠ 0 by linarith]
  have hRm_eq : Rm = ηm * Nm := by dsimp [ηm]; field_simp [show Nm ≠ 0 by linarith]
  have hB0_rel : exp (2 * logG Nk Rk) ≤
      2 * (((2 * k + 1 + f).choose m : ℕ) : ℝ) / sqrt k := by
    have hm_B0 := log_choose_master (2 * k + 1 + f) m (N0 := 2 * Nk) (R0 := 2 * Rk)
      (by linarith) (by nlinarith [hRk_eq]) (by nlinarith [hRk_eq])
      (by
        have heq : ((2 * k + 1 + f : ℕ) : ℝ) - 2 * Nk = 1 := by dsimp [Nk]; push_cast; ring
        rw [heq, abs_one]; linarith)
      (by
        have heq : (m : ℝ) - 2 * Rk = 0 := by dsimp [Rk]; ring
        rw [heq, abs_zero]; linarith)
    have hu_eq : ((2 * k + 1 + f : ℕ) : ℝ) - 2 * Nk = 1 := by dsimp [Nk]; push_cast; ring
    have hv_eq : (m : ℝ) - 2 * Rk = 0 := by dsimp [Rk]; ring
    have hη_eq : 2 * Rk / (2 * Nk) = ηk := by dsimp [ηk]; field_simp [show Nk ≠ 0 by linarith]
    dsimp only at hm_B0
    rw [hu_eq, hv_eq, hη_eq] at hm_B0
    have hlogG2 := logG_double (N0 := Nk) (R0 := Rk) (by nlinarith [hRk_eq]) (by nlinarith [hRk_eq])
    have herr_le : 4000 * ((|(1 : ℝ)| ^ 3 + |(0 : ℝ)| ^ 3) / (2 * Nk) ^ 2 +
        (|(1 : ℝ)| + |(0 : ℝ)| + 1) / (2 * Nk)) ≤ 1 / 10 := by
      simp only [abs_one, abs_zero, one_pow, zero_pow (by norm_num : 3 ≠ 0), add_zero]
      have h1 : 1 / (2 * Nk) ^ 2 ≤ 1 / (2 * Nk) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hNk1 : (1 : ℝ) ≤ 2 * Nk := by linarith
        have := mR hNk1 (show 0 ≤ 2 * Nk by linarith)
        linarith
      have h2 : 3 / (2 * Nk) ≤ 1 / 100000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have hadd : 1 / (2 * Nk) + (1 + 1) / (2 * Nk) = 3 / (2 * Nk) := by ring
      linarith only [h1, h2, hadd]
    have hquad_le : (0 - ηk * 1) ^ 2 / (2 * ηk * (1 - ηk) * (2 * Nk)) ≤ 1 / 10 := by
      have hden_lb : (100 : ℝ) ≤ 2 * ηk * (1 - ηk) * (2 * Nk) := by
        have h1 : (1 / 10 : ℝ) ≤ ηk * (1 - ηk) := by nlinarith only [hηk_lo, hηk_hi]
        have h2 : (1000 : ℝ) ≤ 2 * Nk := by linarith only [hNk_lo, hkR]
        have hmul := mul_le_mul h1 h2 (by norm_num) (by linarith only [h1])
        linarith only [hmul]
      rw [div_le_iff₀ (by linarith only [hden_lb])]
      have hnum : (0 - ηk * 1) ^ 2 ≤ 1 := by nlinarith only [hηk_lo, hηk_hi]
      linarith only [hnum, hden_lb]
    have hlog_lo : 2 * logG Nk Rk + (1 / 2) * log (Real.pi * Rk * (Nk - Rk) / Nk) +
        log (1 / (1 - ηk)) - 1 / 5 ≤ log (((2 * k + 1 + f).choose m : ℕ) : ℝ) := by
      have hlo := (abs_le.mp hm_B0).1
      rw [hlogG2] at hlo
      linarith only [hlo, herr_le, hquad_le]
    have hB0_pos : 0 < (((2 * k + 1 + f).choose m : ℕ) : ℝ) := by
      have hle : m ≤ 2 * k + 1 + f := by
        have : (m : ℝ) ≤ (2 * k + 1 + f : ℕ) := by push_cast; linarith only [hb.2.1, hb.2.2.1, hk_pos]
        exact_mod_cast this
      exact_mod_cast Nat.choose_pos hle
    have hNk_pos : 0 < Nk := by linarith only [hNk_lo, hk_pos]
    have h1m_k : 0 < 1 - ηk := by linarith only [hηk_hi]
    have hRk_pos : 0 < Rk := by rw [hRk_eq]; exact mul_pos (by linarith only [hηk_lo]) hNk_pos
    have hNk_sub : 0 < Nk - Rk := by
      rw [hRk_eq, show Nk - ηk * Nk = (1 - ηk) * Nk by ring]; exact mul_pos h1m_k hNk_pos
    have hpi_rk : 0 < Real.pi * Rk * (Nk - Rk) / Nk :=
      div_pos (mul_pos (mul_pos pi_pos hRk_pos) hNk_sub) hNk_pos
    have hexp_le : exp (2 * logG Nk Rk) *
        sqrt (Real.pi * Rk * (Nk - Rk) / Nk) * (1 / (1 - ηk)) * exp (-(1 / 5)) ≤
        (((2 * k + 1 + f).choose m : ℕ) : ℝ) := by
      have h1 := exp_le_exp.mpr hlog_lo
      rw [exp_log hB0_pos, exp_sub, exp_add, exp_add,
        exp_log (div_pos one_pos h1m_k),
        show exp ((1 / 2) * log (Real.pi * Rk * (Nk - Rk) / Nk)) =
          sqrt (Real.pi * Rk * (Nk - Rk) / Nk) by
            rw [sqrt_eq_rpow, rpow_def_of_pos hpi_rk]; ring_nf] at h1
      rw [div_eq_mul_inv, ← exp_neg] at h1
      exact h1
    have hfac_lb : (1 / 2 : ℝ) * sqrt k ≤
        sqrt (Real.pi * Rk * (Nk - Rk) / Nk) * (1 / (1 - ηk)) * exp (-(1 / 5)) := by
      have hpi : (3 : ℝ) ≤ Real.pi := le_trans (by norm_num) pi_gt_three.le
      have hinner : (1 / 2 : ℝ) * k ≤ Real.pi * Rk * (Nk - Rk) / Nk := by
        rw [le_div_iff₀ hNk_pos]
        have h1 : Rk * (Nk - Rk) = ηk * (1 - ηk) * Nk ^ 2 := by rw [hRk_eq]; ring
        rw [show Real.pi * Rk * (Nk - Rk) = Real.pi * (Rk * (Nk - Rk)) by ring, h1]
        have h2 : (16 / 100 : ℝ) ≤ ηk * (1 - ηk) := by nlinarith only [hηk_lo, hηk_hi]
        have h3 : (48 / 100 : ℝ) ≤ Real.pi * (ηk * (1 - ηk)) := by
          have := mul_le_mul hpi h2 (by norm_num) (by linarith only [hpi]); linarith only [this]
        have h4 : (13 / 10 : ℝ) * (k : ℝ) * Nk ≤ Nk ^ 2 := by
          rw [sq]; exact mR hNk_lo hNk_pos.le
        have h5 := mul_le_mul h3 h4 (by positivity) (by linarith only [h3])
        have hnn : 0 ≤ (k : ℝ) * Nk := by positivity
        linarith only [h5, hnn]
      have hsq_lb : sqrt (1 / 2 : ℝ) * sqrt k ≤
          sqrt (Real.pi * Rk * (Nk - Rk) / Nk) := by
        rw [← sqrt_mul (by norm_num)]
        exact sqrt_le_sqrt hinner
      have hsq12 : (7 / 10 : ℝ) ≤ sqrt (1 / 2 : ℝ) := by
        rw [le_sqrt (by norm_num) (by norm_num)]; norm_num
      have hinv : (3 : ℝ) ≤ 1 / (1 - ηk) := by
        rw [le_div_iff₀ h1m_k]; linarith only [hηk_lo]
      have hexp15 : (1 / 2 : ℝ) ≤ exp (-(1 / 5)) := by
        have h1 := add_one_le_exp (-(1 / 5 : ℝ)); linarith only [h1]
      have hmul1 : (7 / 10 : ℝ) * sqrt k ≤ sqrt (Real.pi * Rk * (Nk - Rk) / Nk) :=
        (mR hsq12 hsq_pos.le).trans hsq_lb
      have hmul2 := mul_le_mul hmul1 hinv (by norm_num) (sqrt_nonneg _)
      have hmul3 := mul_le_mul hmul2 hexp15 (by norm_num) (mul_nonneg (sqrt_nonneg _) (div_nonneg zero_le_one h1m_k.le))
      linarith only [hmul3, hsq_pos]
    rw [le_div_iff₀ hsq_pos]
    have hmul := mL hfac_lb (exp_pos (2 * logG Nk Rk)).le
    linarith only [hmul, hexp_le]
  have hN0_rel : exp (2 * logG Nm Rm) ≤
      4 * (((m + 1).choose (2 * f + 1) : ℕ) : ℝ) / sqrt k := by
    have hNm_pos : 0 < Nm := by linarith only [hNm_lo, hk_pos]
    have h1m_m : 0 < 1 - ηm := by linarith only [hηm_hi]
    have hηm_pos : 0 < ηm := by linarith only [hηm_lo]
    have hm_N0 := log_choose_master (m + 1) (2 * f + 1) (N0 := 2 * Nm) (R0 := 2 * Rm)
      (by linarith only [hNm_lo, hkR]) (by nlinarith only [hRm_eq, hηm_lo, hNm_pos]) (by nlinarith only [hRm_eq, hηm_hi, hNm_pos])
      (by
        have heq : ((m + 1 : ℕ) : ℝ) - 2 * Nm = 1 := by dsimp [Nm]; push_cast; ring
        rw [heq, abs_one]; linarith only [hNm_lo, hkR])
      (by
        have heq : ((2 * f + 1 : ℕ) : ℝ) - 2 * Rm = 1 := by dsimp [Rm]; push_cast; ring
        rw [heq, abs_one]; linarith only [hNm_lo, hkR])
    have hu_eq : ((m + 1 : ℕ) : ℝ) - 2 * Nm = 1 := by dsimp [Nm]; push_cast; ring
    have hv_eq : ((2 * f + 1 : ℕ) : ℝ) - 2 * Rm = 1 := by dsimp [Rm]; push_cast; ring
    have hη_eq : 2 * Rm / (2 * Nm) = ηm := by dsimp [ηm]; field_simp [hNm_pos.ne']
    dsimp only at hm_N0
    rw [hu_eq, hv_eq, hη_eq] at hm_N0
    have hlogG2 := logG_double (N0 := Nm) (R0 := Rm) (by nlinarith only [hRm_eq, hηm_lo, hNm_pos]) (by nlinarith only [hRm_eq, hηm_hi, hNm_pos])
    have herr_le : 4000 * ((|(1 : ℝ)| ^ 3 + |(1 : ℝ)| ^ 3) / (2 * Nm) ^ 2 +
        (|(1 : ℝ)| + |(1 : ℝ)| + 1) / (2 * Nm)) ≤ 1 / 10 := by
      simp only [abs_one, one_pow]
      have h1 : (1 + 1) / (2 * Nm) ^ 2 ≤ 2 / (2 * Nm) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hNm1 : (1 : ℝ) ≤ 2 * Nm := by linarith only [hNm_lo, hkR]
        have := mR hNm1 (by linarith only [hNm_pos] : 0 ≤ 2 * Nm)
        linarith only [this]
      have h2 : 5 / (2 * Nm) ≤ 1 / 100000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hNm_lo, hkR]
      have hadd : 2 / (2 * Nm) + (1 + 1 + 1) / (2 * Nm) = 5 / (2 * Nm) := by ring
      linarith only [h1, h2, hadd]
    have hquad_le : (1 - ηm * 1) ^ 2 / (2 * ηm * (1 - ηm) * (2 * Nm)) ≤ 1 / 10 := by
      have hden_lb : (100 : ℝ) ≤ 2 * ηm * (1 - ηm) * (2 * Nm) := by
        have h1 : (1 / 10 : ℝ) ≤ ηm * (1 - ηm) := by nlinarith only [hηm_lo, hηm_hi]
        have h2 : (1000 : ℝ) ≤ 2 * Nm := by linarith only [hNm_lo, hkR]
        have hmul := mul_le_mul h1 h2 (by norm_num) (by linarith only [h1])
        linarith only [hmul]
      rw [div_le_iff₀ (by linarith only [hden_lb])]
      have hnum : (1 - ηm * 1) ^ 2 ≤ 1 := by nlinarith only [hηm_lo, hηm_hi]
      linarith only [hnum, hden_lb]
    have hlin_sum : 1 * log (1 / (1 - ηm)) + 1 * log ((1 - ηm) / ηm) = log (1 / ηm) := by
      rw [one_mul, one_mul, ← log_mul (div_pos one_pos h1m_m).ne' (div_pos h1m_m hηm_pos).ne']
      congr 1; field_simp [h1m_m.ne', hηm_pos.ne']
    have hlog_lo : 2 * logG Nm Rm + (1 / 2) * log (Real.pi * Rm * (Nm - Rm) / Nm) +
        log (1 / ηm) - 1 / 5 ≤ log (((m + 1).choose (2 * f + 1) : ℕ) : ℝ) := by
      have hlo := (abs_le.mp hm_N0).1
      rw [hlogG2] at hlo
      linarith only [hlo, herr_le, hquad_le, hlin_sum]
    have hN0_pos : 0 < (((m + 1).choose (2 * f + 1) : ℕ) : ℝ) := by
      have hle : 2 * f + 1 ≤ m + 1 := by
        have : (2 * f + 1 : ℝ) ≤ (m + 1 : ℝ) := by linarith only [hb.1, hb.2.2.2.1, hk_pos]
        exact_mod_cast this
      exact_mod_cast Nat.choose_pos hle
    have hRm_pos : 0 < Rm := by rw [hRm_eq]; exact mul_pos hηm_pos hNm_pos
    have hNm_sub : 0 < Nm - Rm := by
      rw [hRm_eq, show Nm - ηm * Nm = (1 - ηm) * Nm by ring]; exact mul_pos h1m_m hNm_pos
    have hpi_rm : 0 < Real.pi * Rm * (Nm - Rm) / Nm :=
      div_pos (mul_pos (mul_pos pi_pos hRm_pos) hNm_sub) hNm_pos
    have hexp_le : exp (2 * logG Nm Rm) *
        sqrt (Real.pi * Rm * (Nm - Rm) / Nm) * (1 / ηm) * exp (-(1 / 5)) ≤
        (((m + 1).choose (2 * f + 1) : ℕ) : ℝ) := by
      have h1 := exp_le_exp.mpr hlog_lo
      rw [exp_log hN0_pos, exp_sub, exp_add, exp_add,
        exp_log (div_pos one_pos hηm_pos),
        show exp ((1 / 2) * log (Real.pi * Rm * (Nm - Rm) / Nm)) =
          sqrt (Real.pi * Rm * (Nm - Rm) / Nm) by
            rw [sqrt_eq_rpow, rpow_def_of_pos hpi_rm]; ring_nf] at h1
      rw [div_eq_mul_inv, ← exp_neg] at h1
      exact h1
    have hfac_lb : (1 / 4 : ℝ) * sqrt k ≤
        sqrt (Real.pi * Rm * (Nm - Rm) / Nm) * (1 / ηm) * exp (-(1 / 5)) := by
      have hpi : (3 : ℝ) ≤ Real.pi := le_trans (by norm_num) pi_gt_three.le
      have hinner : (1 / 2 : ℝ) * k ≤ Real.pi * Rm * (Nm - Rm) / Nm := by
        rw [le_div_iff₀ hNm_pos]
        have h1 : Rm * (Nm - Rm) = ηm * (1 - ηm) * Nm ^ 2 := by rw [hRm_eq]; ring
        rw [show Real.pi * Rm * (Nm - Rm) = Real.pi * (Rm * (Nm - Rm)) by ring, h1]
        have h2 : (2 / 10 : ℝ) ≤ ηm * (1 - ηm) := by nlinarith only [hηm_lo, hηm_hi]
        have h3 : (6 / 10 : ℝ) ≤ Real.pi * (ηm * (1 - ηm)) := by
          have := mul_le_mul hpi h2 (by norm_num) (by linarith only [hpi]); linarith only [this]
        have h4 : (9 / 10 : ℝ) * (k : ℝ) * Nm ≤ Nm ^ 2 := by
          rw [sq]; exact mR hNm_lo hNm_pos.le
        have h5 := mul_le_mul h3 h4 (by positivity) (by linarith only [h3])
        have hnn : 0 ≤ (k : ℝ) * Nm := by positivity
        linarith only [h5, hnn]
      have hsq_lb : sqrt (1 / 2 : ℝ) * sqrt k ≤
          sqrt (Real.pi * Rm * (Nm - Rm) / Nm) := by
        rw [← sqrt_mul (by norm_num)]
        exact sqrt_le_sqrt hinner
      have hsq12 : (7 / 10 : ℝ) ≤ sqrt (1 / 2 : ℝ) := by
        rw [le_sqrt (by norm_num) (by norm_num)]; norm_num
      have hinv : (1 : ℝ) ≤ 1 / ηm := by rw [le_div_iff₀ hηm_pos]; linarith only [hηm_hi]
      have hexp15 : (1 / 2 : ℝ) ≤ exp (-(1 / 5)) := by
        have h1 := add_one_le_exp (-(1 / 5 : ℝ)); linarith only [h1]
      have hmul1 : (7 / 10 : ℝ) * sqrt k ≤ sqrt (Real.pi * Rm * (Nm - Rm) / Nm) :=
        (mR hsq12 hsq_pos.le).trans hsq_lb
      have hmul2 := mul_le_mul hmul1 hinv (by norm_num) (sqrt_nonneg _)
      have hmul3 := mul_le_mul hmul2 hexp15 (by norm_num) (mul_nonneg (sqrt_nonneg _) (div_nonneg zero_le_one hηm_pos.le))
      linarith only [hmul3, hsq_pos]
    rw [le_div_iff₀ hsq_pos]
    have hmul := mL hfac_lb (exp_pos (2 * logG Nm Rm)).le
    linarith only [hmul, hexp_le]
  have hB0_scale : 5 * (2 * (((2 * k + 1 + f).choose m : ℕ) : ℝ) / sqrt k) =
      10 * (((2 * k + 1 + f).choose m : ℕ) : ℝ) / sqrt k := by ring
  have hN0_scale : 4 * (((m + 1).choose (2 * f + 1) : ℕ) : ℝ) / sqrt k ≤
      10 * (((m + 1).choose (2 * f + 1) : ℕ) : ℝ) / sqrt k := by
    apply dR _ hsq_pos.le
    have hnn : (0 : ℝ) ≤ ((m + 1).choose (2 * f + 1) : ℕ) := Nat.cast_nonneg _
    linarith only [hnn]
  simp only [mem_insert, mem_singleton] at hd
  rcases hd with rfl | rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · change 0 < (ηk / (1 - ηk)) * exp (2 * logG Nk Rk)
      exact mul_pos (div_pos (by linarith only [hηk_lo]) (by linarith only [hηk_hi])) (exp_pos _)
    · change (ηk / (1 - ηk)) * exp (2 * logG Nk Rk) ≤ _
      have hfac : ηk / (1 - ηk) ≤ 5 := by rw [div_le_iff₀ (by linarith only [hηk_hi])]; linarith only [hηk_hi]
      have hmul := mul_le_mul hfac hB0_rel (exp_pos _).le (by norm_num)
      linarith only [hmul, hB0_scale]
    · change 0 < ((1 - ηm) / ηm) * exp (2 * logG Nm Rm)
      exact mul_pos (div_pos (by linarith only [hηm_hi]) (by linarith only [hηm_lo])) (exp_pos _)
    · change ((1 - ηm) / ηm) * exp (2 * logG Nm Rm) ≤ _
      have hfac : (1 - ηm) / ηm ≤ 1 := by rw [div_le_iff₀ (by linarith only [hηm_lo])]; linarith only [hηm_lo]
      have hmul := mul_le_mul hfac hN0_rel (exp_pos _).le (by norm_num)
      linarith only [hmul, hN0_scale]
    · change 0 < 1 - ηm; linarith only [hηm_hi]
    · change 1 - ηm ≤ 1; linarith only [hηm_lo]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · change 0 < ηk * exp (2 * logG Nk Rk)
      exact mul_pos (by linarith only [hηk_lo]) (exp_pos _)
    · change ηk * exp (2 * logG Nk Rk) ≤ _
      have hmul := mul_le_mul (show ηk ≤ 5 by linarith only [hηk_hi]) hB0_rel (exp_pos _).le (by norm_num)
      linarith only [hmul, hB0_scale]
    · change 0 < 1 * exp (2 * logG Nm Rm); rw [one_mul]; exact exp_pos _
    · change 1 * exp (2 * logG Nm Rm) ≤ _; rw [one_mul]
      linarith only [hN0_rel, hN0_scale]
    · change 0 < ηm; linarith only [hηm_lo]
    · change ηm ≤ 1; linarith only [hηm_hi]

set_option maxHeartbeats 1600000 in
private lemma deltaK_gaussian_approx {k m f d j a : ℕ} (hV : ValidMF k m f)
    (hd : d ∈ ({0, 1} : Finset ℕ))
    (hj_box : |δ_coord m j| ≤ 40 * sqrt k * log k)
    (ha_box : |ε_coord m f j a| ≤ 20 * sqrt k * log k) :
    let L := log k
    let x : ℝ := δ_coord m j - ε_coord m f j a
    let G : ℝ := cK_val k m f d * exp (-αk_val k * x ^ 2)
    |((k + a).choose j : ℝ) * ((k + f - a - d).choose (m - 1 - j) : ℝ) - G| ≤
      (1e10 : ℝ) * (L ^ 3 / sqrt k) * G ∧
    |deltaK k a (f - a - d) j (m - 1 - j) - (-18 / (k : ℝ)) * cK_val k m f d * phiG (αk_val k) x| ≤
      (2e13 : ℝ) * (L ^ 4 / (k : ℝ)) * G := by
  intro L x G
  have hb := validMF_eta_bounds hV
  have hsqL := validMF_sqL_le hV
  have hL1 := validMF_pow_le hV 1 (by omega)
  have hL3 := validMF_pow_le hV 3 (by omega)
  rw [pow_one] at hL1
  have h2L1 : 2 * log k / sqrt k ≤ 2 / 10 ^ 6 := by
    rw [mul_div_assoc]; linarith only [hL1]
  have ⟨hk, hL, _, _, hm_box, hf_box⟩ := hV
  change 10 ^ 20 ≤ L at hL
  have hL10 : (10 : ℝ) ≤ L := by linarith only [hL]
  change |(m : ℝ) - 2 * k| ≤ sqrt k * L at hm_box
  change |(f : ℝ) - 2 * (k : ℝ) / 3| ≤ sqrt k * L at hf_box
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hsq_ge1 : (1 : ℝ) ≤ sqrt k := by
    rw [le_sqrt (by norm_num) hk_pos.le]; linarith only [hkR]
  have h1sq : (1 : ℝ) ≤ sqrt k * L := by
    have := mul_le_mul hsq_ge1 (by linarith only [hL10] : (1 : ℝ) ≤ L) (by norm_num) hsq_pos.le
    linarith only [this]
  have hd_le1 : (d : ℝ) ≤ 1 := by
    simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl | rfl <;> norm_num
  have hd_nn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  let Nk : ℝ := (k : ℝ) + (f : ℝ) / 2
  let Rk : ℝ := (m : ℝ) / 2
  let ηk : ℝ := Rk / Nk
  let δj : ℝ := δ_coord m j
  let εj : ℝ := ε_coord m f j a
  change |δj| ≤ 40 * sqrt k * L at hj_box
  change |εj| ≤ 20 * sqrt k * L at ha_box
  change sqrt k * L ≤ (k : ℝ) / 10 ^ 6 at hsqL
  have hNk_lo : (13 / 10 : ℝ) * k ≤ Nk := by dsimp [Nk]; linarith only [hb.2.2.1, hk_pos]
  have hNk_hi : Nk ≤ (14 / 10 : ℝ) * k := by dsimp [Nk]; linarith only [hb.2.2.2.1, hk_pos]
  have hNk_pos : 0 < Nk := by linarith only [hNk_lo, hk_pos]
  have hηk_lo : (7 / 10 : ℝ) ≤ ηk := by dsimp [ηk, Rk, Nk]; linarith only [(abs_le.mp hb.2.2.2.2.1).1, h2L1]
  have hηk_hi : ηk ≤ (8 / 10 : ℝ) := by dsimp [ηk, Rk, Nk]; linarith only [(abs_le.mp hb.2.2.2.2.1).2, h2L1]
  have hRk_eq : Rk = ηk * Nk := by dsimp [ηk]; field_simp [hNk_pos.ne']
  have hj_eq : (j : ℝ) = Rk + δj := by dsimp [Rk, δj, δ_coord]; ring
  have ha_eq : (a : ℝ) = (f : ℝ) / 2 + δj / 3 + εj := by
    dsimp [δj, εj, δ_coord, ε_coord]; ring
  have hj_lt_m : j + 1 ≤ m := by
    have : (j : ℝ) + 1 ≤ m := by
      have hj_le : (j : ℝ) = (m : ℝ) / 2 + δj := hj_eq
      linarith [(abs_le.mp hj_box).2, hb.1, hsqL, hkR]
    exact_mod_cast this
  have ha_le_f : a + d ≤ f := by
    have : (a : ℝ) + d ≤ f := by
      linarith [(abs_le.mp hj_box).2, (abs_le.mp ha_box).2, hb.2.2.1, hsqL, hkR, hd_le1, ha_eq]
    exact_mod_cast this
  let u1 : ℝ := δj / 3 + εj
  let v1 : ℝ := δj
  let u2 : ℝ := -(δj / 3 + εj) - (d : ℝ)
  let v2 : ℝ := -δj - 1
  have hu1_eq : ((k + a : ℕ) : ℝ) - Nk = u1 := by dsimp [Nk, u1]; push_cast; linarith [ha_eq]
  have hv1_eq : (j : ℝ) - Rk = v1 := by dsimp [v1]; linarith [hj_eq]
  have hu2_eq : ((k + f - a - d : ℕ) : ℝ) - Nk = u2 := by
    have hsub : k + f - a - d = k + (f - (a + d)) := by omega
    rw [hsub, Nat.cast_add, Nat.cast_sub ha_le_f, Nat.cast_add]
    dsimp [Nk, u2]; linarith [ha_eq]
  have hv2_eq : ((m - 1 - j : ℕ) : ℝ) - Rk = v2 := by
    have hsub : m - 1 - j = m - (j + 1) := by omega
    rw [hsub, Nat.cast_sub hj_lt_m, Nat.cast_add, Nat.cast_one]
    dsimp [Rk, v2] at hj_eq ⊢; linarith only [hj_eq]
  have hW_u1 : |u1| ≤ 40 * sqrt k * L := by
    dsimp [u1]; have h := abs_add_le (δj / 3) εj
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h
    have hnn : 0 ≤ sqrt k * L := by positivity
    linarith only [h, hj_box, ha_box, hnn]
  have hW_v1 : |v1| ≤ 40 * sqrt k * L := hj_box
  have hW_u2 : |u2| ≤ 41 * sqrt k * L := by
    dsimp [u2]; have h := abs_sub (-(δj / 3 + εj)) (d : ℝ)
    rw [abs_neg, abs_of_nonneg hd_nn] at h
    linarith only [h, hW_u1, hd_le1, h1sq]
  have hW_v2 : |v2| ≤ 41 * sqrt k * L := by
    dsimp [v2]; have h := abs_sub (-δj) (1 : ℝ)
    rw [abs_neg, abs_one] at h
    linarith only [h, hj_box, h1sq]
  have hNk20 : 20 ≤ Nk := by linarith only [hNk_lo, hkR]
  have hRk_lo : (1 / 10 : ℝ) * Nk ≤ Rk := by nlinarith only [hRk_eq, hηk_lo, hNk_pos]
  have hRk_hi : Rk ≤ (9 / 10 : ℝ) * Nk := by nlinarith only [hRk_eq, hηk_hi, hNk_pos]
  have hW41_Nk : 41 * sqrt k * L ≤ Nk / 40 := by linarith only [hsqL, hNk_lo, hk_pos]
  have hW40_Nk : 40 * sqrt k * L ≤ Nk / 40 := by linarith only [hsqL, hNk_lo, hk_pos]
  have hm1 := log_choose_master (k + a) j (N0 := Nk) (R0 := Rk)
    hNk20 hRk_lo hRk_hi
    (by rw [hu1_eq]; exact hW_u1.trans hW40_Nk) (by rw [hv1_eq]; exact hW_v1.trans hW40_Nk)
  have hm2 := log_choose_master (k + f - a - d) (m - 1 - j) (N0 := Nk) (R0 := Rk)
    hNk20 hRk_lo hRk_hi
    (by rw [hu2_eq]; exact hW_u2.trans hW41_Nk) (by rw [hv2_eq]; exact hW_v2.trans hW41_Nk)
  dsimp only at hm1 hm2
  rw [hu1_eq, hv1_eq] at hm1
  rw [hu2_eq, hv2_eq] at hm2
  have herr_single : ∀ (u v : ℝ), |u| ≤ 41 * sqrt k * L →
      |v| ≤ 41 * sqrt k * L →
      4000 * ((|u| ^ 3 + |v| ^ 3) / Nk ^ 2 + (|u| + |v| + 1) / Nk) ≤
        1e9 * (L ^ 3 / sqrt k) := by
    intro u v hu hv
    have hu3 : |u| ^ 3 ≤ 41 ^ 3 * ((k : ℝ) * sqrt k) * L ^ 3 := by
      have h1 := pow_le_pow_left₀ (abs_nonneg u) hu 3
      have h2 : (41 * sqrt k * L) ^ 3 =
          41 ^ 3 * (sqrt k ^ 2 * sqrt k) * L ^ 3 := by ring
      rw [h2, sq_sqrt hk_pos.le] at h1; exact h1
    have hv3 : |v| ^ 3 ≤ 41 ^ 3 * ((k : ℝ) * sqrt k) * L ^ 3 := by
      have h1 := pow_le_pow_left₀ (abs_nonneg v) hv 3
      have h2 : (41 * sqrt k * L) ^ 3 =
          41 ^ 3 * (sqrt k ^ 2 * sqrt k) * L ^ 3 := by ring
      rw [h2, sq_sqrt hk_pos.le] at h1; exact h1
    have hNk_sq : (k : ℝ) ^ 2 ≤ Nk ^ 2 := pow_le_pow_left₀ hk_pos.le (by linarith) 2
    have hcub : (|u| ^ 3 + |v| ^ 3) / Nk ^ 2 ≤ 2 * 41 ^ 3 * (L ^ 3 / sqrt k) := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : |u| ^ 3 + |v| ^ 3 ≤ 2 * 41 ^ 3 * ((k : ℝ) * sqrt k) * L ^ 3 := by linarith only [hu3, hv3]
      have h2 : 2 * 41 ^ 3 * (L ^ 3 / sqrt k) * (k : ℝ) ^ 2 =
          2 * 41 ^ 3 * ((k : ℝ) * sqrt k) * L ^ 3 := by
        rw [show (k : ℝ) ^ 2 = (k : ℝ) * (sqrt k * sqrt k) by
          rw [mul_self_sqrt hk_pos.le]; ring]
        field_simp [hsq_pos.ne']
      have h3 := mL hNk_sq
        (show 0 ≤ 2 * 41 ^ 3 * (L ^ 3 / sqrt k) by positivity)
      linarith only [h1, h2, h3]
    have hlin : (|u| + |v| + 1) / Nk ≤ 100 * (L ^ 3 / sqrt k) := by
      have h1 : |u| + |v| + 1 ≤ 100 * sqrt k * L ^ 3 := by
        have hL13 : L ≤ L ^ 3 := by
          have : L ^ 1 ≤ L ^ 3 := pow_le_pow_right₀ (by linarith only [hL10]) (by omega)
          simpa using this
        have hmul := mL hL13 hsq_pos.le
        linarith only [hu, hv, h1sq, hmul]
      rw [div_le_iff₀ hNk_pos]
      have h2 : 100 * (L ^ 3 / sqrt k) * (k : ℝ) = 100 * sqrt k * L ^ 3 := by
        calc 100 * (L ^ 3 / sqrt k) * (k : ℝ)
            = 100 * L ^ 3 * ((sqrt k * sqrt k) / sqrt k) := by
              rw [mul_self_sqrt hk_pos.le]; ring
          _ = 100 * sqrt k * L ^ 3 := by field_simp [hsq_pos.ne']
      have h3 := mL (show (k : ℝ) ≤ Nk by linarith only [hNk_lo, hk_pos])
        (show 0 ≤ 100 * (L ^ 3 / sqrt k) by positivity)
      linarith only [h1, h2, h3]
    have hnn3 : 0 ≤ L ^ 3 / sqrt k := by positivity
    linarith only [hcub, hlin, hnn3]
  have h40_41 : 40 * sqrt k * L ≤ 41 * sqrt k * L := by
    have hnn : 0 ≤ sqrt k * L := by positivity
    have h1 : 40 * sqrt k * L = 40 * (sqrt k * L) := by ring
    have h2 : 41 * sqrt k * L = 41 * (sqrt k * L) := by ring
    linarith only [hnn, h1, h2]
  have hW_u1' : |u1| ≤ 41 * sqrt k * L := hW_u1.trans h40_41
  have hW_v1' : |v1| ≤ 41 * sqrt k * L := hW_v1.trans h40_41
  have he1 := hm1.trans (herr_single u1 v1 hW_u1' hW_v1')
  have he2 := hm2.trans (herr_single u2 v2 hW_u2 hW_v2)
  have hlin_sum : (u1 + u2) * log (1 / (1 - ηk)) + (v1 + v2) * log ((1 - ηk) / ηk) =
      log (if d = 0 then ηk / (1 - ηk) else ηk) := by
    have hu12 : u1 + u2 = -(d : ℝ) := by dsimp [u1, u2]; ring
    have hv12 : v1 + v2 = -1 := by dsimp [v1, v2]; ring
    have h1m_pos : 0 < 1 - ηk := by linarith only [hηk_hi]
    have hηk_pos : 0 < ηk := by linarith only [hηk_lo]
    rw [hu12, hv12]
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl
    · simp only [Nat.cast_zero, neg_zero, zero_mul, zero_add, neg_mul, one_mul, ↓reduceIte]
      rw [← log_inv, inv_div]
    · simp only [Nat.cast_one, neg_mul, one_mul, one_ne_zero, ↓reduceIte]
      rw [← log_inv, ← log_inv,
        ← log_mul (inv_pos.mpr (div_pos one_pos h1m_pos)).ne'
          (inv_pos.mpr (div_pos h1m_pos hηk_pos)).ne']
      congr 1; field_simp [h1m_pos.ne', hηk_pos.ne']
  have hquad_diff :
      |(v1 - ηk * u1) ^ 2 / (2 * ηk * (1 - ηk) * Nk) +
       (v2 - ηk * u2) ^ 2 / (2 * ηk * (1 - ηk) * Nk) - αk_val k * x ^ 2| ≤
      1e8 * (L ^ 3 / sqrt k) := by
    have hηk_err : |ηk - 3 / 4| ≤ 2 * L / sqrt k := hb.2.2.2.2.1
    have hx_le : |x| ≤ 60 * sqrt k * L := by
      dsimp [x]; exact (abs_sub δj εj).trans (by linarith only [hj_box, ha_box])
    have hq1 : |(v1 - ηk * u1) - (3 / 4) * x| ≤ 100 * L ^ 2 := by
      have heq : (v1 - ηk * u1) - (3 / 4) * x = -(ηk - 3 / 4) * u1 := by
        dsimp [v1, u1, x]; ring
      rw [heq, abs_mul, abs_neg]
      have hmul := mul_le_mul hηk_err hW_u1 (abs_nonneg _) (by positivity)
      have hsimp : (2 * L / sqrt k) * (40 * sqrt k * L) = 80 * L ^ 2 := by
        field_simp [hsq_pos.ne']; ring
      have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
      linarith only [hmul, hsimp, hL2nn]
    have hq2 : |(v2 - ηk * u2) - (-(3 / 4) * x)| ≤ 101 * L ^ 2 := by
      have heq : (v2 - ηk * u2) - (-(3 / 4) * x) =
          -((v1 - ηk * u1) - (3 / 4) * x) + (ηk * d - 1) := by
        dsimp [v1, u1, v2, u2, x]; ring
      rw [heq]
      have h1 : |ηk * d - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> nlinarith only [hηk_lo, hηk_hi, hd_nn, hd_le1]
      have h2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
      exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith only [hq1, h1, h2])
    have hsq_diff : ∀ (z t : ℝ), |z - t| ≤ 101 * L ^ 2 → |t| ≤ 50 * sqrt k * L →
        |z ^ 2 - t ^ 2| ≤ 12000 * sqrt k * L ^ 3 := by
      intro z t hzt ht
      have hz : |z + t| ≤ 110 * sqrt k * L := by
        have h1 : z + t = (z - t) + 2 * t := by ring
        rw [h1]
        have h2 : 101 * L ^ 2 ≤ 10 * sqrt k * L := by
          have hL1' := validMF_pow_le hV 1 (by omega)
          rw [pow_one, div_le_div_iff₀ hsq_pos (by norm_num)] at hL1'
          have hmul := mR hL1' (by linarith only [hL10] : 0 ≤ L)
          change L * 10 ^ 6 * L ≤ 1 * sqrt k * L at hmul
          have hnn : 0 ≤ sqrt k * L := by positivity
          linarith only [hmul, hnn]
        have htri := abs_add_le (z - t) (2 * t)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
        linarith only [htri, hzt, ht, h2]
      rw [show z ^ 2 - t ^ 2 = (z - t) * (z + t) by ring, abs_mul]
      have hmul := mul_le_mul hzt hz (abs_nonneg _) (by positivity)
      have hnn : 0 ≤ sqrt k * L ^ 3 := by positivity
      linarith only [hmul, hnn]
    have h34x : |(3 / 4 : ℝ) * x| ≤ 50 * sqrt k * L := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
      have hnn : 0 ≤ sqrt k * L := by positivity
      linarith only [hx_le, hnn]
    have hs1 := hsq_diff (v1 - ηk * u1) ((3 / 4) * x)
      (hq1.trans (by have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L; linarith only [hL2nn])) h34x
    have hs2 := hsq_diff (v2 - ηk * u2) (-(3 / 4) * x) hq2
      (by rw [show -(3 / 4 : ℝ) * x = -((3 / 4) * x) by ring, abs_neg]; exact h34x)
    let Dq : ℝ := 2 * ηk * (1 - ηk) * Nk
    have hDq_lo : (4 / 10 : ℝ) * k ≤ Dq := by
      dsimp [Dq]
      have h1 : (16 / 100 : ℝ) ≤ ηk * (1 - ηk) := by nlinarith only [hηk_lo, hηk_hi]
      have hmul := mul_le_mul h1 hNk_lo (by positivity) (by linarith only [h1])
      have hnn : 0 ≤ (k : ℝ) := hk_pos.le
      linarith only [hmul, hnn]
    have hDq_diff : |Dq - (k : ℝ) / 2| ≤ 10 * sqrt k * L := by
      have h1 : Dq - (k : ℝ) / 2 =
          2 * (ηk * (1 - ηk) - 3 / 16) * Nk + (3 / 8) * (Nk - (4 / 3) * k) := by
        dsimp [Dq]; ring
      have hη_quad : |ηk * (1 - ηk) - 3 / 16| ≤ 2 * L / sqrt k := by
        have heq : ηk * (1 - ηk) - 3 / 16 = (ηk - 3 / 4) * (1 / 4 - ηk) := by ring
        rw [heq, abs_mul]
        have h2 : |1 / 4 - ηk| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        exact (mul_le_mul hb.2.2.2.2.1 h2 (abs_nonneg _) (by positivity)).trans (by linarith)
      have hNk_diff : |Nk - (4 / 3 : ℝ) * k| ≤ sqrt k * L := by
        have heq : Nk - (4 / 3 : ℝ) * k = (1 / 2) * ((f : ℝ) - 2 * k / 3) := by dsimp [Nk]; ring
        rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith
      rw [h1]
      have htri := abs_add_le (2 * (ηk * (1 - ηk) - 3 / 16) * Nk) ((3 / 8) * (Nk - (4 / 3) * k))
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hNk_pos,
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 8)] at htri
      have hmul : 2 * (2 * L / sqrt k) * Nk ≤ 6 * sqrt k * L := by
        have h2 : (2 * L / sqrt k) * (14 / 10 * k) = (28 / 10) * sqrt k * L := by
          calc (2 * L / sqrt k) * (14 / 10 * k)
              = (28 / 10) * L * ((sqrt k * sqrt k) / sqrt k) := by
                rw [mul_self_sqrt hk_pos.le]; ring
            _ = (28 / 10) * sqrt k * L := by field_simp [hsq_pos.ne']
        have h3 := mL hNk_hi (show 0 ≤ 2 * L / sqrt k by positivity)
        have hnn : 0 ≤ sqrt k * L := by positivity
        linarith only [h2, h3, hnn]
      have hterm1 : 2 * |ηk * (1 - ηk) - 3 / 16| * Nk ≤ 2 * (2 * L / sqrt k) * Nk :=
        mR (mL hη_quad (by norm_num)) hNk_pos.le
      have hnn : 0 ≤ sqrt k * L := by positivity
      linarith only [htri, hterm1, hmul, hNk_diff, hnn]
    have hDq_pos : 0 < Dq := by linarith only [hDq_lo, hk_pos]
    have hrew : (v1 - ηk * u1) ^ 2 / Dq + (v2 - ηk * u2) ^ 2 / Dq - αk_val k * x ^ 2 =
        ((v1 - ηk * u1) ^ 2 - ((3 / 4) * x) ^ 2) / Dq +
        ((v2 - ηk * u2) ^ 2 - (-(3 / 4) * x) ^ 2) / Dq +
        (9 / 8) * x ^ 2 * ((k : ℝ) / 2 - Dq) / (Dq * ((k : ℝ) / 2)) := by
      dsimp [αk_val]; field_simp [hDq_pos.ne', hk_pos.ne']; ring
    change |(v1 - ηk * u1) ^ 2 / Dq + (v2 - ηk * u2) ^ 2 / Dq - αk_val k * x ^ 2| ≤ _
    rw [hrew]
    have htri := abs_add3_le (((v1 - ηk * u1) ^ 2 - ((3 / 4) * x) ^ 2) / Dq)
      (((v2 - ηk * u2) ^ 2 - (-(3 / 4) * x) ^ 2) / Dq)
      ((9 / 8) * x ^ 2 * ((k : ℝ) / 2 - Dq) / (Dq * ((k : ℝ) / 2)))
    have hp1 : |((v1 - ηk * u1) ^ 2 - ((3 / 4) * x) ^ 2) / Dq| ≤ 30000 * (L ^ 3 / sqrt k) := by
      rw [abs_div, abs_of_pos hDq_pos, div_le_iff₀ hDq_pos]
      have h2 : 30000 * (L ^ 3 / sqrt k) * ((4 / 10) * k) =
          12000 * sqrt k * L ^ 3 := by
        calc 30000 * (L ^ 3 / sqrt k) * ((4 / 10) * k)
            = 12000 * L ^ 3 * ((sqrt k * sqrt k) / sqrt k) := by
              rw [mul_self_sqrt hk_pos.le]; ring
          _ = 12000 * sqrt k * L ^ 3 := by field_simp [hsq_pos.ne']
      have h3 := mL hDq_lo
        (show 0 ≤ 30000 * (L ^ 3 / sqrt k) by positivity)
      linarith only [hs1, h2, h3]
    have hp2 : |((v2 - ηk * u2) ^ 2 - (-(3 / 4) * x) ^ 2) / Dq| ≤ 30000 * (L ^ 3 / sqrt k) := by
      rw [abs_div, abs_of_pos hDq_pos, div_le_iff₀ hDq_pos]
      have h2 : 30000 * (L ^ 3 / sqrt k) * ((4 / 10) * k) =
          12000 * sqrt k * L ^ 3 := by
        calc 30000 * (L ^ 3 / sqrt k) * ((4 / 10) * k)
            = 12000 * L ^ 3 * ((sqrt k * sqrt k) / sqrt k) := by
              rw [mul_self_sqrt hk_pos.le]; ring
          _ = 12000 * sqrt k * L ^ 3 := by field_simp [hsq_pos.ne']
      have h3 := mL hDq_lo
        (show 0 ≤ 30000 * (L ^ 3 / sqrt k) by positivity)
      linarith only [hs2, h2, h3]
    have hp3 : |(9 / 8) * x ^ 2 * ((k : ℝ) / 2 - Dq) / (Dq * ((k : ℝ) / 2))| ≤
        300000 * (L ^ 3 / sqrt k) := by
      have hDq_k_pos : 0 < Dq * ((k : ℝ) / 2) := mul_pos hDq_pos (by positivity)
      rw [abs_div, abs_of_pos hDq_k_pos,
        abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 8), abs_of_nonneg (sq_nonneg x),
        abs_sub_comm]
      have hx2 : x ^ 2 ≤ 3600 * (k : ℝ) * L ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg x) hx_le 2
        rw [sq_abs, mul_pow, mul_pow, sq_sqrt hk_pos.le] at h; linarith only [h]
      have hnum : (9 / 8 : ℝ) * x ^ 2 * |Dq - (k : ℝ) / 2| ≤
          45000 * ((k : ℝ) * sqrt k) * L ^ 3 := by
        have hmul := mul_le_mul hx2 hDq_diff (abs_nonneg _) (by positivity)
        have hnn : 0 ≤ ((k : ℝ) * sqrt k) * L ^ 3 := by positivity
        linarith only [hmul, hnn]
      have hden : (1 / 5 : ℝ) * (k : ℝ) ^ 2 ≤ Dq * ((k : ℝ) / 2) := by
        have := mR hDq_lo (show 0 ≤ (k : ℝ) / 2 by positivity)
        linarith only [this]
      rw [div_le_iff₀ hDq_k_pos]
      have h2 : 300000 * (L ^ 3 / sqrt k) * ((1 / 5 : ℝ) * (k : ℝ) ^ 2) =
          60000 * ((k : ℝ) * sqrt k) * L ^ 3 := by
        rw [show (k : ℝ) ^ 2 = (k : ℝ) * (sqrt k * sqrt k) by
          rw [mul_self_sqrt hk_pos.le]; ring]
        field_simp [hsq_pos.ne']; ring
      have h3 := mL hden
        (show 0 ≤ 300000 * (L ^ 3 / sqrt k) by positivity)
      have hnn : 0 ≤ ((k : ℝ) * sqrt k) * L ^ 3 := by positivity
      linarith only [hnum, h2, h3, hnn]
    have hnn3 : 0 ≤ L ^ 3 / sqrt k := by positivity
    linarith only [htri, hp1, hp2, hp3, hnn3]
  have hKj_pos : 0 < ((k + a).choose j : ℝ) * ((k + f - a - d).choose (m - 1 - j) : ℝ) := by
    have h1 : j ≤ k + a := by
      have : (j : ℝ) ≤ (k + a : ℕ) := by
        have hj' : (j : ℝ) = (m : ℝ) / 2 + δj := hj_eq
        push_cast; linarith only [(abs_le.mp hj_box).2, (abs_le.mp ha_box).1, hb.2.1, hb.2.2.1, ha_eq, hj', hsqL, hk_pos]
      exact_mod_cast this
    have h2 : m - 1 - j ≤ k + f - a - d := by
      have : ((m - 1 - j : ℕ) : ℝ) ≤ ((k + f - a - d : ℕ) : ℝ) := by
        have hv2' : ((m - 1 - j : ℕ) : ℝ) = Rk + v2 := by linarith only [hv2_eq]
        have hu2' : ((k + f - a - d : ℕ) : ℝ) = Nk + u2 := by linarith only [hu2_eq]
        rw [hv2', hu2']
        dsimp [Rk]
        linarith only [(abs_le.mp hW_v2).2, (abs_le.mp hW_u2).1, hNk_lo, hb.2.1, hsqL, hk_pos]
      exact_mod_cast this
    have hc1 : 0 < (k + a).choose j := Nat.choose_pos h1
    have hc2 : 0 < (k + f - a - d).choose (m - 1 - j) := Nat.choose_pos h2
    positivity
  have hG_eq : G = exp (2 * logG Nk Rk + log (if d = 0 then ηk / (1 - ηk) else ηk) -
      αk_val k * x ^ 2) := by
    have hif_pos : 0 < (if d = 0 then ηk / (1 - ηk) else ηk) := by
      split_ifs <;> [exact div_pos (by linarith only [hηk_lo]) (by linarith only [hηk_hi]); linarith only [hηk_lo]]
    rw [sub_eq_add_neg, exp_add, exp_add, exp_log hif_pos,
      show -(αk_val k * x ^ 2) = -αk_val k * x ^ 2 by ring]
    change (if d = 0 then ηk / (1 - ηk) else ηk) * exp (2 * logG Nk Rk) * exp (-αk_val k * x ^ 2) = _
    ring
  have hlog_Kj : |log (((k + a).choose j : ℝ) * ((k + f - a - d).choose (m - 1 - j) : ℝ)) -
      (2 * logG Nk Rk + log (if d = 0 then ηk / (1 - ηk) else ηk) - αk_val k * x ^ 2)| ≤
      3e9 * (L ^ 3 / sqrt k) := by
    have hc1_pos : (0 : ℝ) < ((k + a).choose j : ℝ) := by
      by_contra h; push Not at h
      have h0 : ((k + a).choose j : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
      rw [h0, zero_mul] at hKj_pos; exact lt_irrefl 0 hKj_pos
    have hc2_pos : (0 : ℝ) < ((k + f - a - d).choose (m - 1 - j) : ℝ) := by
      by_contra h; push Not at h
      have h0 : ((k + f - a - d).choose (m - 1 - j) : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
      rw [h0, mul_zero] at hKj_pos; exact lt_irrefl 0 hKj_pos
    rw [log_mul hc1_pos.ne' hc2_pos.ne']
    have hsplit : log ((k + a).choose j : ℝ) + log ((k + f - a - d).choose (m - 1 - j) : ℝ) -
        (2 * logG Nk Rk + log (if d = 0 then ηk / (1 - ηk) else ηk) - αk_val k * x ^ 2) =
        (log ((k + a).choose j : ℝ) - (logG Nk Rk + u1 * log (1 / (1 - ηk)) +
          v1 * log ((1 - ηk) / ηk) - (v1 - ηk * u1) ^ 2 / (2 * ηk * (1 - ηk) * Nk))) +
        (log ((k + f - a - d).choose (m - 1 - j) : ℝ) - (logG Nk Rk + u2 * log (1 / (1 - ηk)) +
          v2 * log ((1 - ηk) / ηk) - (v2 - ηk * u2) ^ 2 / (2 * ηk * (1 - ηk) * Nk))) -
        ((v1 - ηk * u1) ^ 2 / (2 * ηk * (1 - ηk) * Nk) +
          (v2 - ηk * u2) ^ 2 / (2 * ηk * (1 - ηk) * Nk) - αk_val k * x ^ 2) := by
      rw [← hlin_sum]; ring
    rw [hsplit]
    have htri := abs_add_sub_le
      (log ((k + a).choose j : ℝ) - (logG Nk Rk + u1 * log (1 / (1 - ηk)) +
        v1 * log ((1 - ηk) / ηk) - (v1 - ηk * u1) ^ 2 / (2 * ηk * (1 - ηk) * Nk)))
      (log ((k + f - a - d).choose (m - 1 - j) : ℝ) - (logG Nk Rk + u2 * log (1 / (1 - ηk)) +
        v2 * log ((1 - ηk) / ηk) - (v2 - ηk * u2) ^ 2 / (2 * ηk * (1 - ηk) * Nk)))
      ((v1 - ηk * u1) ^ 2 / (2 * ηk * (1 - ηk) * Nk) +
        (v2 - ηk * u2) ^ 2 / (2 * ηk * (1 - ηk) * Nk) - αk_val k * x ^ 2)
    have he1' : |log ((k + a).choose j : ℝ) - (logG Nk Rk + u1 * log (1 / (1 - ηk)) +
        v1 * log ((1 - ηk) / ηk) - (v1 - ηk * u1) ^ 2 / (2 * ηk * (1 - ηk) * Nk))| ≤
        1e9 * (L ^ 3 / sqrt k) := he1
    have he2' : |log ((k + f - a - d).choose (m - 1 - j) : ℝ) - (logG Nk Rk + u2 * log (1 / (1 - ηk)) +
        v2 * log ((1 - ηk) / ηk) - (v2 - ηk * u2) ^ 2 / (2 * ηk * (1 - ηk) * Nk))| ≤
        1e9 * (L ^ 3 / sqrt k) := he2
    have hnn3 : 0 ≤ L ^ 3 / sqrt k := by positivity
    linarith only [htri, he1', he2', hquad_diff, hnn3]
  have hL3_tiny : 3e9 * (L ^ 3 / sqrt k) ≤ 1 / 2 := by
    have hL12 : (10 ^ 12 : ℝ) * L ^ 3 ≤ L ^ 15 := by
      have h1 : (10 : ℝ) ^ 12 ≤ L ^ 12 := pow_le_pow_left₀ (by norm_num) hL10 12
      have h2 := mR h1 (pow_nonneg (by linarith only [hL10]) 3)
      rwa [← pow_add] at h2
    have hdiv : (10 ^ 12 : ℝ) * (L ^ 3 / sqrt k) ≤ L ^ 15 / sqrt k := by
      rw [mul_div_assoc']; exact dR hL12 hsq_pos.le
    have hL15 : L ^ 15 / sqrt k ≤ 1 / 10 ^ 6 := hV.2.2.1
    linarith only [hdiv, hL15]
  have hPart1 : |((k + a).choose j : ℝ) * ((k + f - a - d).choose (m - 1 - j) : ℝ) - G| ≤
      (1e10 : ℝ) * (L ^ 3 / sqrt k) * G := by
    have h := abs_sub_exp_of_log_approx hKj_pos hlog_Kj hL3_tiny
    rw [← hG_eq] at h
    have hG_nn : 0 ≤ G := by
      dsimp [G]; exact mul_nonneg (cK_cM_bounds hV hd).1.le (exp_pos _).le
    have hle : 2 * (3e9 * (L ^ 3 / sqrt k)) ≤ (1e10 : ℝ) * (L ^ 3 / sqrt k) := by
      have : 0 ≤ L ^ 3 / sqrt k := by positivity
      linarith
    exact h.trans (mR hle hG_nn)
  have hPart2 : |deltaK k a (f - a - d) j (m - 1 - j) -
      (-18 / (k : ℝ)) * cK_val k m f d * phiG (αk_val k) x| ≤
      (2e13 : ℝ) * (L ^ 4 / (k : ℝ)) * G := by
    let Kj : ℝ := ((k + a).choose j : ℝ) * ((k + f - a - d).choose (m - 1 - j) : ℝ)
    let D1 : ℝ := ((k + a : ℕ) : ℝ) + 1 - j
    let D2 : ℝ := ((k + f - a - d : ℕ) : ℝ) + 1 - ((m - 1 - j : ℕ) : ℝ)
    have hD1_eq : D1 = Nk - Rk + (u1 - v1) + 1 := by dsimp [D1]; linarith [hu1_eq, hv1_eq]
    have hD2_eq : D2 = Nk - Rk + (u2 - v2) + 1 := by dsimp [D2]; linarith [hu2_eq, hv2_eq]
    have hD1_diff : |D1 - (k : ℝ) / 3| ≤ 90 * sqrt k * L := by
      have heq : D1 - (k : ℝ) / 3 = (1 / 2) * ((f : ℝ) - 2 * k / 3) -
          (1 / 2) * ((m : ℝ) - 2 * k) + (u1 - v1) + 1 := by
        rw [hD1_eq]; dsimp [Nk, Rk]; ring
      rw [heq]
      have h1 : |u1 - v1| ≤ 80 * sqrt k * L := (abs_sub u1 v1).trans (by linarith only [hW_u1, hW_v1])
      have htri : |(1 / 2 : ℝ) * ((f : ℝ) - 2 * k / 3) - (1 / 2) * ((m : ℝ) - 2 * k) + (u1 - v1) + 1| ≤
          |(1 / 2 : ℝ) * ((f : ℝ) - 2 * k / 3)| + |(1 / 2 : ℝ) * ((m : ℝ) - 2 * k)| + |u1 - v1| + |1| := by
        have t1 := abs_add_le ((1 / 2 : ℝ) * ((f : ℝ) - 2 * k / 3) - (1 / 2) * ((m : ℝ) - 2 * k) + (u1 - v1)) 1
        have t2 := abs_add_le ((1 / 2 : ℝ) * ((f : ℝ) - 2 * k / 3) - (1 / 2) * ((m : ℝ) - 2 * k)) (u1 - v1)
        have t3 := abs_sub ((1 / 2 : ℝ) * ((f : ℝ) - 2 * k / 3)) ((1 / 2 : ℝ) * ((m : ℝ) - 2 * k))
        linarith only [t1, t2, t3]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_one] at htri
      have hnn : 0 ≤ sqrt k * L := by positivity
      linarith only [htri, h1, h1sq, hm_box, hf_box, hnn]
    have hD2_diff : |D2 - (k : ℝ) / 3| ≤ 90 * sqrt k * L := by
      have heq : D2 - (k : ℝ) / 3 = (1 / 2) * ((f : ℝ) - 2 * k / 3) -
          (1 / 2) * ((m : ℝ) - 2 * k) + (u2 - v2) + 1 := by
        rw [hD2_eq]; dsimp [Nk, Rk]; ring
      rw [heq]
      have h1 : |u2 - v2| ≤ 82 * sqrt k * L := (abs_sub u2 v2).trans (by linarith only [hW_u2, hW_v2])
      have htri : |(1 / 2 : ℝ) * ((f : ℝ) - 2 * k / 3) - (1 / 2) * ((m : ℝ) - 2 * k) + (u2 - v2) + 1| ≤
          |(1 / 2 : ℝ) * ((f : ℝ) - 2 * k / 3)| + |(1 / 2 : ℝ) * ((m : ℝ) - 2 * k)| + |u2 - v2| + |1| := by
        have t1 := abs_add_le ((1 / 2 : ℝ) * ((f : ℝ) - 2 * k / 3) - (1 / 2) * ((m : ℝ) - 2 * k) + (u2 - v2)) 1
        have t2 := abs_add_le ((1 / 2 : ℝ) * ((f : ℝ) - 2 * k / 3) - (1 / 2) * ((m : ℝ) - 2 * k)) (u2 - v2)
        have t3 := abs_sub ((1 / 2 : ℝ) * ((f : ℝ) - 2 * k / 3)) ((1 / 2 : ℝ) * ((m : ℝ) - 2 * k))
        linarith only [t1, t2, t3]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_one] at htri
      have hnn : 0 ≤ sqrt k * L := by positivity
      linarith only [htri, h1, h1sq, hm_box, hf_box, hnn]
    have hD1_lo : (3 / 10 : ℝ) * k ≤ D1 := by linarith only [(abs_le.mp hD1_diff).1, hsqL, hk_pos]
    have hD2_lo : (3 / 10 : ℝ) * k ≤ D2 := by linarith only [(abs_le.mp hD2_diff).1, hsqL, hk_pos]
    have hD1_pos : 0 < D1 := by linarith only [hD1_lo, hk_pos]
    have hD2_pos : 0 < D2 := by linarith only [hD2_lo, hk_pos]
    have hdelta_eq : deltaK k a (f - a - d) j (m - 1 - j) =
        Kj * (((m - 1 - j : ℕ) : ℝ) / D2 - (j : ℝ) / D1) := by
      unfold deltaK
      have hca := choose_succ_mul_real (k + a) j
      have hcb := choose_succ_mul_real (k + (f - a - d)) (m - 1 - j)
      have hs_eq : k + (f - a - d) = k + f - a - d := by omega
      have h1a : k + 1 + a = (k + a) + 1 := by omega
      have h1b : k + 1 + (f - a - d) = (k + f - a - d) + 1 := by omega
      rw [hs_eq] at hcb
      rw [h1a, h1b, hs_eq]
      have hca' : (((k + a) + 1).choose j : ℝ) = (((k + a : ℕ) : ℝ) + 1) / D1 * ((k + a).choose j : ℝ) := by
        rw [div_mul_eq_mul_div, eq_div_iff hD1_pos.ne']; linarith only [hca]
      have hcb' : (((k + f - a - d) + 1).choose (m - 1 - j) : ℝ) =
          (((k + f - a - d : ℕ) : ℝ) + 1) / D2 * ((k + f - a - d).choose (m - 1 - j) : ℝ) := by
        rw [div_mul_eq_mul_div, eq_div_iff hD2_pos.ne']; linarith only [hcb]
      push_cast
      rw [hca', hcb']
      dsimp [Kj, D1, D2] at hD1_pos hD2_pos ⊢
      field_simp [hD1_pos.ne', hD2_pos.ne']; ring
    have hrat_diff : |(((m - 1 - j : ℕ) : ℝ) / D2 - (j : ℝ) / D1) - (-18 / (k : ℝ)) * x| ≤
        2e6 * (L ^ 2 / (k : ℝ)) := by
      let num : ℝ := ((m - 1 - j : ℕ) : ℝ) * D1 - (j : ℝ) * D2
      have hnum_eq : num = ((m - 1 - j : ℕ) : ℝ) * (((k + a : ℕ) : ℝ) + 1) -
          (j : ℝ) * (((k + f - a - d : ℕ) : ℝ) + 1) := by
        dsimp [num, D1, D2]; ring
      have hnum_lin : |num - (-2 * (k : ℝ) * x)| ≤ 500 * (k : ℝ) * L ^ 2 := by
        have halg2 : num - (-2 * (k : ℝ) * x) =
            ((m : ℝ) - 2 * k) * u1 - δj * ((f : ℝ) - 2 * k / 3) -
            (Nk + u1 + 1) + (Rk + δj) * d - 2 * δj := by
          rw [hnum_eq]
          have h1 : ((m - 1 - j : ℕ) : ℝ) = Rk + v2 := by linarith only [hv2_eq]
          have h2 : ((k + a : ℕ) : ℝ) = Nk + u1 := by linarith only [hu1_eq]
          have h3 : (j : ℝ) = Rk + v1 := by linarith only [hv1_eq]
          have h4 : ((k + f - a - d : ℕ) : ℝ) = Nk + u2 := by linarith only [hu2_eq]
          rw [h1, h2, h3, h4]
          dsimp [Nk, Rk, u1, v1, u2, v2, x]; ring
        rw [halg2]
        have ht1 : |((m : ℝ) - 2 * k) * u1| ≤ 40 * (k : ℝ) * L ^ 2 := by
          rw [abs_mul]
          have hmul := mul_le_mul hm_box hW_u1 (abs_nonneg _) (by positivity)
          have hsq : (sqrt k * L) * (40 * sqrt k * L) = 40 * (k : ℝ) * L ^ 2 := by
            calc (sqrt k * L) * (40 * sqrt k * L)
                = 40 * (sqrt k * sqrt k) * L ^ 2 := by ring
              _ = 40 * (k : ℝ) * L ^ 2 := by rw [mul_self_sqrt hk_pos.le]
          linarith only [hmul, hsq]
        have ht2 : |δj * ((f : ℝ) - 2 * k / 3)| ≤ 40 * (k : ℝ) * L ^ 2 := by
          rw [abs_mul]
          have hmul := mul_le_mul hj_box hf_box (abs_nonneg _) (by positivity)
          have hsq : (40 * sqrt k * L) * (sqrt k * L) = 40 * (k : ℝ) * L ^ 2 := by
            calc (40 * sqrt k * L) * (sqrt k * L)
                = 40 * (sqrt k * sqrt k) * L ^ 2 := by ring
              _ = 40 * (k : ℝ) * L ^ 2 := by rw [mul_self_sqrt hk_pos.le]
          linarith only [hmul, hsq]
        have ht3 : |Nk + u1 + 1| ≤ 2 * (k : ℝ) * L ^ 2 := by
          have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
          have h1 : |Nk + u1 + 1| ≤ 2 * k := by
            rw [abs_le]; constructor <;> linarith only [(abs_le.mp hW_u1).1, (abs_le.mp hW_u1).2, hNk_lo, hNk_hi, hsqL, hkR]
          have h2 := mL hL2 (show 0 ≤ 2 * (k : ℝ) by positivity)
          linarith only [h1, h2]
        have ht4 : |(Rk + δj) * d| ≤ 2 * (k : ℝ) * L ^ 2 := by
          have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
          have hRk_d : |Rk + δj| ≤ 2 * k := by
            rw [abs_le]; dsimp [Rk]; constructor <;>
              linarith only [(abs_le.mp hj_box).1, (abs_le.mp hj_box).2, hb.1, hb.2.1, hsqL, hkR]
          rw [abs_mul, abs_of_nonneg hd_nn]
          have h1 := mul_le_mul hRk_d hd_le1 hd_nn (by positivity)
          have h2 := mL hL2 (show 0 ≤ 2 * (k : ℝ) by positivity)
          linarith only [h1, h2]
        have ht5 : |2 * δj| ≤ 2 * (k : ℝ) * L ^ 2 := by
          have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          have h1 : 2 * |δj| ≤ 2 * k := by linarith only [hj_box, hsqL, hk_pos]
          have h2 := mL hL2 (show 0 ≤ 2 * (k : ℝ) by positivity)
          linarith only [h1, h2]
        have htri : |((m : ℝ) - 2 * k) * u1 - δj * ((f : ℝ) - 2 * k / 3) -
            (Nk + u1 + 1) + (Rk + δj) * d - 2 * δj| ≤
            |((m : ℝ) - 2 * k) * u1| + |δj * ((f : ℝ) - 2 * k / 3)| +
            |Nk + u1 + 1| + |(Rk + δj) * d| + |2 * δj| := by
          have t1 := abs_sub (((m : ℝ) - 2 * k) * u1 - δj * ((f : ℝ) - 2 * k / 3) -
            (Nk + u1 + 1) + (Rk + δj) * d) (2 * δj)
          have t2 := abs_add_le (((m : ℝ) - 2 * k) * u1 - δj * ((f : ℝ) - 2 * k / 3) -
            (Nk + u1 + 1)) ((Rk + δj) * d)
          have t3 := abs_sub (((m : ℝ) - 2 * k) * u1 - δj * ((f : ℝ) - 2 * k / 3)) (Nk + u1 + 1)
          have t4 := abs_sub (((m : ℝ) - 2 * k) * u1) (δj * ((f : ℝ) - 2 * k / 3))
          linarith only [t1, t2, t3, t4]
        have hnn : 0 ≤ (k : ℝ) * L ^ 2 := by positivity
        linarith only [htri, ht1, ht2, ht3, ht4, ht5, hnn]
      have hD12_diff : |D1 * D2 - (k : ℝ) ^ 2 / 9| ≤ 100 * (k : ℝ) * sqrt k * L := by
        have heq : D1 * D2 - (k : ℝ) ^ 2 / 9 =
            (D1 - (k : ℝ) / 3) * D2 + ((k : ℝ) / 3) * (D2 - (k : ℝ) / 3) := by ring
        rw [heq]
        have hD2_hi : |D2| ≤ (4 / 10 : ℝ) * k := by
          rw [abs_of_pos hD2_pos]; linarith only [(abs_le.mp hD2_diff).2, hsqL, hk_pos]
        have htri := abs_add_le ((D1 - (k : ℝ) / 3) * D2) (((k : ℝ) / 3) * (D2 - (k : ℝ) / 3))
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < (k : ℝ) / 3)] at htri
        have hm1' := mul_le_mul hD1_diff hD2_hi (abs_nonneg D2) (by positivity)
        have hm2' := mL hD2_diff (by positivity : 0 ≤ (k : ℝ) / 3)
        have hnn : 0 ≤ (k : ℝ) * sqrt k * L := by positivity
        linarith only [htri, hm1', hm2', hnn]
      have hfrac_eq : (((m - 1 - j : ℕ) : ℝ) / D2 - (j : ℝ) / D1) - (-18 / (k : ℝ)) * x =
          (num - (-2 * (k : ℝ) * x)) / (D1 * D2) +
          (-2 * (k : ℝ) * x) * ((k : ℝ) ^ 2 / 9 - D1 * D2) / (D1 * D2 * ((k : ℝ) ^ 2 / 9)) := by
        dsimp [num]; field_simp [hD1_pos.ne', hD2_pos.ne', hk_pos.ne']; ring
      rw [hfrac_eq]
      have hD12_lo : (9 / 100 : ℝ) * (k : ℝ) ^ 2 ≤ D1 * D2 := by
        have hmul := mul_le_mul hD1_lo hD2_lo (by positivity) (by positivity)
        linarith only [hmul]
      have hx_le : |x| ≤ 60 * sqrt k * L := by
        have hnn : 0 ≤ sqrt k * L := by positivity
        exact (abs_sub δj εj).trans (by linarith only [hj_box, ha_box, hnn])
      have hp1 : |(num - (-2 * (k : ℝ) * x)) / (D1 * D2)| ≤ 6000 * (L ^ 2 / (k : ℝ)) := by
        rw [abs_div, abs_of_pos (mul_pos hD1_pos hD2_pos), div_le_iff₀ (mul_pos hD1_pos hD2_pos)]
        have h1 : 6000 * (L ^ 2 / (k : ℝ)) * ((9 / 100 : ℝ) * (k : ℝ) ^ 2) = 540 * (k : ℝ) * L ^ 2 := by
          field_simp [hk_pos.ne']; ring
        have h2 := mL hD12_lo (show 0 ≤ 6000 * (L ^ 2 / (k : ℝ)) by positivity)
        have hnn : 0 ≤ (k : ℝ) * L ^ 2 := by positivity
        linarith only [hnum_lin, h1, h2, hnn]
      have hp2 : |(-2 * (k : ℝ) * x) * ((k : ℝ) ^ 2 / 9 - D1 * D2) / (D1 * D2 * ((k : ℝ) ^ 2 / 9))| ≤
          1500000 * (L ^ 2 / (k : ℝ)) := by
        have hden_pos : 0 < D1 * D2 * ((k : ℝ) ^ 2 / 9) := mul_pos (mul_pos hD1_pos hD2_pos) (by positivity)
        rw [abs_div, abs_of_pos hden_pos,
          abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos hk_pos, abs_sub_comm ((k : ℝ) ^ 2 / 9) (D1 * D2)]
        have hnum : 2 * (k : ℝ) * |x| * |D1 * D2 - (k : ℝ) ^ 2 / 9| ≤
            12000 * (k : ℝ) ^ 3 * L ^ 2 := by
          have h1 := mul_le_mul hx_le hD12_diff (abs_nonneg _) (by positivity)
          have h2 : (60 * sqrt k * L) * (100 * (k : ℝ) * sqrt k * L) =
              6000 * (k : ℝ) ^ 2 * L ^ 2 := by
            calc (60 * sqrt k * L) * (100 * (k : ℝ) * sqrt k * L)
                = 6000 * (k : ℝ) * (sqrt k * sqrt k) * L ^ 2 := by ring
              _ = 6000 * (k : ℝ) ^ 2 * L ^ 2 := by rw [mul_self_sqrt hk_pos.le]; ring
          have h3 := mL (h1.trans h2.le) (show 0 ≤ 2 * (k : ℝ) by positivity)
          have h4 : 2 * (k : ℝ) * (6000 * (k : ℝ) ^ 2 * L ^ 2) = 12000 * (k : ℝ) ^ 3 * L ^ 2 := by ring
          have h5 : 2 * (k : ℝ) * (|x| * |D1 * D2 - (k : ℝ) ^ 2 / 9|) =
              2 * (k : ℝ) * |x| * |D1 * D2 - (k : ℝ) ^ 2 / 9| := by ring
          linarith only [h3, h4, h5]
        have hden : (1 / 100 : ℝ) * (k : ℝ) ^ 4 ≤ D1 * D2 * ((k : ℝ) ^ 2 / 9) := by
          have h1 := mR hD12_lo (show 0 ≤ (k : ℝ) ^ 2 / 9 by positivity)
          have h2 : (9 / 100 : ℝ) * (k : ℝ) ^ 2 * ((k : ℝ) ^ 2 / 9) = (1 / 100 : ℝ) * (k : ℝ) ^ 4 := by ring
          linarith only [h1, h2]
        rw [div_le_iff₀ hden_pos]
        have h2 : 1500000 * (L ^ 2 / (k : ℝ)) * ((1 / 100 : ℝ) * (k : ℝ) ^ 4) =
            15000 * (k : ℝ) ^ 3 * L ^ 2 := by field_simp [hk_pos.ne']; ring
        have h3 := mL hden (show 0 ≤ 1500000 * (L ^ 2 / (k : ℝ)) by positivity)
        have hnn : 0 ≤ (k : ℝ) ^ 3 * L ^ 2 := by positivity
        nlinarith only [hnum, h2, h3, hnn]
      have hnn : 0 ≤ L ^ 2 / (k : ℝ) := by positivity
      exact (abs_add_le _ _).trans (by linarith only [hp1, hp2, hnn])
    have hG_pos : 0 < G := mul_pos (cK_cM_bounds hV hd).1 (exp_pos _)
    have hKj_le : Kj ≤ 2 * G := by
      have h1 : (1e10 : ℝ) * (L ^ 3 / sqrt k) ≤ 1 := by
        have hL12 : (10 ^ 12 : ℝ) * L ^ 3 ≤ L ^ 15 := by
          have h1 := pow_le_pow_left₀ (by norm_num) hL10 12
          have h2 := mR h1 (pow_nonneg (by linarith only [hL10]) 3)
          rwa [← pow_add] at h2
        have hdiv : (10 ^ 12 : ℝ) * (L ^ 3 / sqrt k) ≤ L ^ 15 / sqrt k := by
          rw [mul_div_assoc']; exact dR hL12 hsq_pos.le
        have hL15 : L ^ 15 / sqrt k ≤ 1 / 10 ^ 6 := hV.2.2.1
        linarith only [hdiv, hL15]
      have h2 := (abs_le.mp hPart1).2
      have h3 := mR h1 hG_pos.le
      linarith only [h2, h3]
    have hphi_eq : (-18 / (k : ℝ)) * cK_val k m f d * phiG (αk_val k) x =
        G * ((-18 / (k : ℝ)) * x) := by dsimp [G, phiG]; ring
    rw [hdelta_eq, hphi_eq]
    have hsplit : Kj * (((m - 1 - j : ℕ) : ℝ) / D2 - (j : ℝ) / D1) - G * ((-18 / (k : ℝ)) * x) =
        Kj * ((((m - 1 - j : ℕ) : ℝ) / D2 - (j : ℝ) / D1) - (-18 / (k : ℝ)) * x) +
        (Kj - G) * ((-18 / (k : ℝ)) * x) := by ring
    rw [hsplit]
    have htri := abs_add_le
      (Kj * ((((m - 1 - j : ℕ) : ℝ) / D2 - (j : ℝ) / D1) - (-18 / (k : ℝ)) * x))
      ((Kj - G) * ((-18 / (k : ℝ)) * x))
    have h1 : |Kj * ((((m - 1 - j : ℕ) : ℝ) / D2 - (j : ℝ) / D1) - (-18 / (k : ℝ)) * x)| ≤
        4e6 * (L ^ 4 / (k : ℝ)) * G := by
      rw [abs_mul, abs_of_pos hKj_pos]
      have hL24 : L ^ 2 ≤ L ^ 4 := by
        have h1 : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
        have h2 := mL h1 (sq_nonneg L)
        linarith only [h2]
      have hdiv : L ^ 2 / (k : ℝ) ≤ L ^ 4 / (k : ℝ) := dR hL24 hk_pos.le
      calc Kj * |(((m - 1 - j : ℕ) : ℝ) / D2 - (j : ℝ) / D1) - (-18 / (k : ℝ)) * x|
          ≤ (2 * G) * (2e6 * (L ^ 2 / (k : ℝ))) :=
            mul_le_mul hKj_le hrat_diff (abs_nonneg _) (by positivity)
        _ ≤ (2 * G) * (2e6 * (L ^ 4 / (k : ℝ))) :=
            mL (mL hdiv (by norm_num)) (by positivity)
        _ = 4e6 * (L ^ 4 / (k : ℝ)) * G := by ring
    have h2 : |(Kj - G) * ((-18 / (k : ℝ)) * x)| ≤ 1.2e13 * (L ^ 4 / (k : ℝ)) * G := by
      rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 18),
        abs_of_pos hk_pos]
      have hx_le : |x| ≤ 60 * sqrt k * L := by
        have hnn : 0 ≤ sqrt k * L := by positivity
        exact (abs_sub δj εj).trans (by linarith only [hj_box, ha_box, hnn])
      have hmul := mul_le_mul hPart1
        (mL hx_le (by positivity : (0 : ℝ) ≤ 18 / k))
        (by positivity) (by positivity)
      have hsimp : (1e10 : ℝ) * (L ^ 3 / sqrt k) * G *
          ((18 / (k : ℝ)) * (60 * sqrt k * L)) =
          1.08e13 * (L ^ 4 / (k : ℝ)) * G := by
        field_simp [hsq_pos.ne', hk_pos.ne']; ring
      have hnn : 0 ≤ (L ^ 4 / (k : ℝ)) * G := by positivity
      linarith only [hmul, hsimp, hnn]
    have hnn : 0 ≤ (L ^ 4 / (k : ℝ)) * G := by positivity
    linarith only [htri, h1, h2, hnn]
  exact ⟨hPart1, hPart2⟩

set_option maxHeartbeats 1600000 in
private lemma M_pair_gaussian_approx {k m f d1 d2 j a : ℕ} (hV : ValidMF k m f)
    (hd1 : d1 ∈ ({0, 1} : Finset ℕ)) (hd2 : d2 ∈ ({0, 1} : Finset ℕ))
    (hj_box : |δ_coord m j| ≤ 40 * sqrt k * log k)
    (ha_box : |ε_coord m f j a| ≤ 10 * sqrt k * log k) :
    let L := log k
    let εj : ℝ := ε_coord m f j a
    let GM : ℝ := cM_val m f d1 * cC_val m f d2 * exp (-18 * εj ^ 2 / (k : ℝ))
    |(j.choose (2 * a + d1) : ℝ) * ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) - GM| ≤
      (2e10 : ℝ) * (L ^ 3 / sqrt k) * GM := by
  intro L εj GM
  have hb := validMF_eta_bounds hV
  have hsqL := validMF_sqL_le hV
  have hL1 := validMF_pow_le hV 1 (by omega)
  rw [pow_one] at hL1
  have h2L1 : 2 * log k / sqrt k ≤ 2 / 10 ^ 6 := by
    rw [mul_div_assoc]; linarith only [hL1]
  have ⟨hk, hL, _, _, hm_box, hf_box⟩ := hV
  change 10 ^ 20 ≤ L at hL
  have hL10 : (10 : ℝ) ≤ L := by linarith only [hL]
  change |(m : ℝ) - 2 * k| ≤ sqrt k * L at hm_box
  change |(f : ℝ) - 2 * (k : ℝ) / 3| ≤ sqrt k * L at hf_box
  change sqrt k * L ≤ (k : ℝ) / 10 ^ 6 at hsqL
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hsq_ge1 : (1 : ℝ) ≤ sqrt k := by
    rw [le_sqrt (by norm_num) hk_pos.le]; linarith only [hkR]
  have hd1_le1 : (d1 : ℝ) ≤ 1 := by
    simp only [mem_insert, mem_singleton] at hd1; rcases hd1 with rfl | rfl <;> norm_num
  have hd2_le1 : (d2 : ℝ) ≤ 1 := by
    simp only [mem_insert, mem_singleton] at hd2; rcases hd2 with rfl | rfl <;> norm_num
  let Nm : ℝ := (m : ℝ) / 2
  let Rm : ℝ := (f : ℝ)
  let ηm : ℝ := Rm / Nm
  let δj : ℝ := δ_coord m j
  change |δj| ≤ 40 * sqrt k * L at hj_box
  change |εj| ≤ 10 * sqrt k * L at ha_box
  have hNm_lo : (9 / 10 : ℝ) * k ≤ Nm := by dsimp [Nm]; linarith only [hb.1, hk_pos]
  have hNm_hi : Nm ≤ (11 / 10 : ℝ) * k := by dsimp [Nm]; linarith only [hb.2.1, hk_pos]
  have hNm_pos : 0 < Nm := by linarith only [hNm_lo, hk_pos]
  have hηm_lo : (6 / 10 : ℝ) ≤ ηm := by dsimp [ηm, Rm, Nm]; linarith only [(abs_le.mp hb.2.2.2.2.2).1, h2L1]
  have hηm_hi : ηm ≤ (7 / 10 : ℝ) := by dsimp [ηm, Rm, Nm]; linarith only [(abs_le.mp hb.2.2.2.2.2).2, h2L1]
  have hRm_eq : Rm = ηm * Nm := by dsimp [ηm]; field_simp [hNm_pos.ne']
  have hj_eq : (j : ℝ) = Nm + δj := by dsimp [Nm, δj, δ_coord]; ring
  have ha_eq : (a : ℝ) = (f : ℝ) / 2 + δj / 3 + εj := by
    dsimp [δj, εj, δ_coord, ε_coord]; ring
  have hj_lt_m : j + 1 ≤ m := by
    have : (j : ℝ) + 1 ≤ m := by
      have hj_le : (j : ℝ) = (m : ℝ) / 2 + δj := hj_eq
      linarith [(abs_le.mp hj_box).2, hb.1, hsqL, hkR]
    exact_mod_cast this
  have ha_le_f : a + d1 ≤ f := by
    have : (a : ℝ) + d1 ≤ f := by
      linarith [(abs_le.mp hj_box).2, (abs_le.mp ha_box).2, hb.2.2.1, hsqL, hkR, hd1_le1, ha_eq]
    exact_mod_cast this
  have hd2_le_s : d2 ≤ 2 * (f - a - d1) + 1 := by
    simp only [mem_insert, mem_singleton] at hd2; rcases hd2 with rfl | rfl <;> omega
  let u1 : ℝ := δj
  let v1 : ℝ := (2 / 3) * δj + 2 * εj + d1
  let u2 : ℝ := -δj - 1
  let v2 : ℝ := -(2 / 3) * δj - 2 * εj - 2 * d1 + 1 - d2
  have hu1_eq : (j : ℝ) - Nm = u1 := by dsimp [u1]; linarith [hj_eq]
  have hv1_eq : ((2 * a + d1 : ℕ) : ℝ) - Rm = v1 := by
    dsimp [Rm, v1]; push_cast; linarith [ha_eq]
  have hu2_eq : ((m - j - 1 : ℕ) : ℝ) - Nm = u2 := by
    have hsub : m - j - 1 = m - (j + 1) := by omega
    rw [hsub, Nat.cast_sub hj_lt_m, Nat.cast_add, Nat.cast_one]
    dsimp [Nm, u2] at hj_eq ⊢; linarith only [hj_eq]
  have hv2_eq : ((2 * (f - a - d1) + 1 - d2 : ℕ) : ℝ) - Rm = v2 := by
    have hsub : f - a - d1 = f - (a + d1) := by omega
    rw [Nat.cast_sub hd2_le_s, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_two,
      hsub, Nat.cast_sub ha_le_f, Nat.cast_add]
    dsimp [Rm, v2]; linarith [ha_eq]
  have h1sq : (1 : ℝ) ≤ sqrt k * L := by
    have := mul_le_mul hsq_ge1 (by linarith only [hL10] : (1 : ℝ) ≤ L) (by norm_num) hsq_pos.le
    linarith only [this]
  have hW_u1 : |u1| ≤ 50 * sqrt k * L := by
    have hnn : 0 ≤ sqrt k * L := by positivity
    have h1 : 40 * sqrt k * L = 40 * (sqrt k * L) := by ring
    have h2 : 50 * sqrt k * L = 50 * (sqrt k * L) := by ring
    exact hj_box.trans (by linarith only [hnn, h1, h2])
  have hW_v1 : |v1| ≤ 50 * sqrt k * L := by
    dsimp [v1]; have h := abs_add3_le ((2 / 3 : ℝ) * δj) (2 * εj) (d1 : ℝ)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3),
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (show (0 : ℝ) ≤ d1 from Nat.cast_nonneg d1)] at h
    linarith only [h, hj_box, ha_box, hd1_le1, h1sq]
  have hW_u2 : |u2| ≤ 50 * sqrt k * L := by
    dsimp [u2]; have h := abs_sub (-δj) (1 : ℝ); rw [abs_neg, abs_one] at h; linarith only [h, hj_box, h1sq]
  have hW_v2 : |v2| ≤ 55 * sqrt k * L := by
    have hv2_rew : v2 = -(2 / 3) * δj - 2 * εj + (1 - 2 * (d1 : ℝ) - d2) := by dsimp [v2]; ring
    rw [hv2_rew]
    have htri := abs_sub_add_le (-(2 / 3 : ℝ) * δj) (2 * εj) (1 - 2 * (d1 : ℝ) - d2)
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3),
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
    have hc : |1 - 2 * (d1 : ℝ) - d2| ≤ 3 := by
      rw [abs_le]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) d1, Nat.cast_nonneg (α := ℝ) d2]
    linarith only [htri, hj_box, ha_box, hc, h1sq]
  have hm1 := log_choose_master j (2 * a + d1) (N0 := Nm) (R0 := Rm)
    (by linarith) (by nlinarith [hRm_eq]) (by nlinarith [hRm_eq])
    (by rw [hu1_eq]; linarith) (by rw [hv1_eq]; linarith)
  have hm2 := log_choose_master (m - j - 1) (2 * (f - a - d1) + 1 - d2) (N0 := Nm) (R0 := Rm)
    (by linarith) (by nlinarith [hRm_eq]) (by nlinarith [hRm_eq])
    (by rw [hu2_eq]; linarith) (by rw [hv2_eq]; linarith)
  dsimp only at hm1 hm2
  rw [hu1_eq, hv1_eq] at hm1
  rw [hu2_eq, hv2_eq] at hm2
  have herr_single : ∀ (u v : ℝ), |u| ≤ 55 * sqrt k * L →
      |v| ≤ 55 * sqrt k * L →
      4000 * ((|u| ^ 3 + |v| ^ 3) / Nm ^ 2 + (|u| + |v| + 1) / Nm) ≤
        4e9 * (L ^ 3 / sqrt k) := by
    intro u v hu hv
    have hu3 : |u| ^ 3 ≤ 55 ^ 3 * ((k : ℝ) * sqrt k) * L ^ 3 := by
      have h1 := pow_le_pow_left₀ (abs_nonneg u) hu 3
      have h2 : (55 * sqrt k * L) ^ 3 =
          55 ^ 3 * (sqrt k ^ 2 * sqrt k) * L ^ 3 := by ring
      rw [h2, sq_sqrt hk_pos.le] at h1; exact h1
    have hv3 : |v| ^ 3 ≤ 55 ^ 3 * ((k : ℝ) * sqrt k) * L ^ 3 := by
      have h1 := pow_le_pow_left₀ (abs_nonneg v) hv 3
      have h2 : (55 * sqrt k * L) ^ 3 =
          55 ^ 3 * (sqrt k ^ 2 * sqrt k) * L ^ 3 := by ring
      rw [h2, sq_sqrt hk_pos.le] at h1; exact h1
    have hNm_sq : (8 / 10 : ℝ) * (k : ℝ) ^ 2 ≤ Nm ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hNm_lo 2
      rw [mul_pow, show (9 / 10 : ℝ) ^ 2 = 81 / 100 by norm_num] at h
      have hk2 : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
      linarith only [h, hk2]
    have hcub : (|u| ^ 3 + |v| ^ 3) / Nm ^ 2 ≤ 500000 * (L ^ 3 / sqrt k) := by
      rw [div_le_iff₀ (by positivity)]
      have h2 : 500000 * (L ^ 3 / sqrt k) * ((8 / 10 : ℝ) * (k : ℝ) ^ 2) =
          400000 * ((k : ℝ) * sqrt k) * L ^ 3 := by
        rw [show (k : ℝ) ^ 2 = (k : ℝ) * (sqrt k * sqrt k) by
          rw [mul_self_sqrt hk_pos.le]; ring]
        field_simp [hsq_pos.ne']; ring
      have h3 := mL hNm_sq
        (show 0 ≤ 500000 * (L ^ 3 / sqrt k) by positivity)
      have hnn : 0 ≤ ((k : ℝ) * sqrt k) * L ^ 3 := by positivity
      linarith only [hu3, hv3, h2, h3, hnn]
    have hlin : (|u| + |v| + 1) / Nm ≤ 200 * (L ^ 3 / sqrt k) := by
      have hL13 : L ≤ L ^ 3 := by
        have : L ^ 1 ≤ L ^ 3 := pow_le_pow_right₀ (by linarith only [hL10]) (by omega); simpa using this
      have h1 : |u| + |v| + 1 ≤ 150 * sqrt k * L ^ 3 := by
        have hmul := mL hL13 hsq_pos.le
        linarith only [hu, hv, h1sq, hmul]
      rw [div_le_iff₀ hNm_pos]
      have h2 : 200 * (L ^ 3 / sqrt k) * ((9 / 10 : ℝ) * k) =
          180 * sqrt k * L ^ 3 := by
        calc 200 * (L ^ 3 / sqrt k) * ((9 / 10 : ℝ) * k)
            = 180 * L ^ 3 * ((sqrt k * sqrt k) / sqrt k) := by
              rw [mul_self_sqrt hk_pos.le]; ring
          _ = 180 * sqrt k * L ^ 3 := by field_simp [hsq_pos.ne']
      have h3 := mL hNm_lo
        (show 0 ≤ 200 * (L ^ 3 / sqrt k) by positivity)
      have hnn : 0 ≤ sqrt k * L ^ 3 := by positivity
      linarith only [h1, h2, h3, hnn]
    have hnn3 : 0 ≤ L ^ 3 / sqrt k := by positivity
    linarith only [hcub, hlin, hnn3]
  have hnn_sqL : 0 ≤ sqrt k * L := by positivity
  have he1 := hm1.trans (herr_single u1 v1 (hW_u1.trans (by linarith only [hnn_sqL])) (hW_v1.trans (by linarith only [hnn_sqL])))
  have he2 := hm2.trans (herr_single u2 v2 (hW_u2.trans (by linarith only [hnn_sqL])) hW_v2)
  have hlin_sum : (u1 + u2) * log (1 / (1 - ηm)) + (v1 + v2) * log ((1 - ηm) / ηm) =
      log ((if d1 = 0 then (1 - ηm) / ηm else 1) * (if d2 = 0 then 1 - ηm else ηm)) := by
    have hu12 : u1 + u2 = -1 := by dsimp [u1, u2]; ring
    have hv12 : v1 + v2 = 1 - (d1 : ℝ) - (d2 : ℝ) := by dsimp [v1, v2]; ring
    rw [hu12, hv12]
    have h1m_pos : 0 < 1 - ηm := by linarith only [hηm_hi]
    have hη_pos : 0 < ηm := by linarith only [hηm_lo]
    simp only [mem_insert, mem_singleton] at hd1 hd2
    rcases hd1 with rfl | rfl <;> rcases hd2 with rfl | rfl <;>
      simp only [Nat.cast_zero, Nat.cast_one, ↓reduceIte, one_ne_zero]
    · -- d1 = 0, d2 = 0
      rw [show (1 : ℝ) - 0 - 0 = 1 by norm_num, neg_mul, one_mul, one_mul,
        ← log_inv, inv_div, div_one, ← log_mul h1m_pos.ne' (div_pos h1m_pos hη_pos).ne']
      congr 1; ring
    · -- d1 = 0, d2 = 1
      rw [show (1 : ℝ) - 0 - 1 = 0 by norm_num, neg_mul, one_mul, zero_mul, add_zero,
        ← log_inv, inv_div, div_one]
      congr 1; field_simp [hη_pos.ne']
    · -- d1 = 1, d2 = 0
      rw [show (1 : ℝ) - 1 - 0 = 0 by norm_num, neg_mul, one_mul, zero_mul, add_zero,
        ← log_inv, inv_div, div_one, one_mul]
    · -- d1 = 1, d2 = 1
      rw [show (1 : ℝ) - 1 - 1 = -1 by norm_num, neg_mul, one_mul, neg_mul, one_mul, one_mul,
        ← log_inv, ← log_inv, inv_div, div_one, inv_div,
        ← log_mul h1m_pos.ne' (div_pos hη_pos h1m_pos).ne']
      congr 1; field_simp [h1m_pos.ne']
  have hquad_diff :
      |(v1 - ηm * u1) ^ 2 / (2 * ηm * (1 - ηm) * Nm) +
       (v2 - ηm * u2) ^ 2 / (2 * ηm * (1 - ηm) * Nm) - 18 * εj ^ 2 / (k : ℝ)| ≤
      1e8 * (L ^ 3 / sqrt k) := by
    have hηm_err : |ηm - 2 / 3| ≤ 2 * L / sqrt k := hb.2.2.2.2.2
    have h1L2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
    have hq1 : |(v1 - ηm * u1) - 2 * εj| ≤ 100 * L ^ 2 := by
      have heq : (v1 - ηm * u1) - 2 * εj = -(ηm - 2 / 3) * δj + d1 := by dsimp [v1, u1]; ring
      rw [heq]
      have hmul := mul_le_mul hηm_err hj_box (abs_nonneg _) (by positivity)
      have hsimp : (2 * L / sqrt k) * (40 * sqrt k * L) = 80 * L ^ 2 := by
        field_simp [hsq_pos.ne']; ring
      exact (abs_add_le _ _).trans (by
        rw [abs_mul, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ d1 from Nat.cast_nonneg d1)]
        linarith only [hmul, hsimp, hd1_le1, h1L2])
    have hq2 : |(v2 - ηm * u2) - (-2 * εj)| ≤ 100 * L ^ 2 := by
      have heq : (v2 - ηm * u2) - (-2 * εj) = (ηm - 2 / 3) * δj + (ηm - 2 * d1 + 1 - d2) := by
        dsimp [v2, u2]; ring
      rw [heq]
      have hmul := mul_le_mul hηm_err hj_box (abs_nonneg _) (by positivity)
      have hsimp : (2 * L / sqrt k) * (40 * sqrt k * L) = 80 * L ^ 2 := by
        field_simp [hsq_pos.ne']; ring
      have hc : |ηm - 2 * (d1 : ℝ) + 1 - d2| ≤ 4 := by
        rw [abs_le]; constructor <;>
          linarith only [hηm_lo, hηm_hi, hd1_le1, hd2_le1,
            Nat.cast_nonneg (α := ℝ) d1, Nat.cast_nonneg (α := ℝ) d2]
      exact (abs_add_le _ _).trans (by rw [abs_mul]; linarith only [hmul, hsimp, hc, h1L2])
    have hsq_diff : ∀ (z t : ℝ), |z - t| ≤ 100 * L ^ 2 → |t| ≤ 20 * sqrt k * L →
        |z ^ 2 - t ^ 2| ≤ 6000 * sqrt k * L ^ 3 := by
      intro z t hzt ht
      have h2 : 100 * L ^ 2 ≤ 10 * sqrt k * L := by
        have h1 := validMF_pow_le hV 1 (by omega)
        rw [pow_one, div_le_div_iff₀ hsq_pos (by norm_num)] at h1
        have hmul := mR h1 (by linarith only [hL10] : 0 ≤ L)
        change L * 10 ^ 6 * L ≤ 1 * sqrt k * L at hmul
        linarith only [hmul, hnn_sqL]
      have hz : |z + t| ≤ 50 * sqrt k * L := by
        rw [show z + t = (z - t) + 2 * t by ring]
        have htri := abs_add_le (z - t) (2 * t)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
        linarith only [htri, hzt, ht, h2]
      rw [show z ^ 2 - t ^ 2 = (z - t) * (z + t) by ring, abs_mul]
      have hmul := mul_le_mul hzt hz (abs_nonneg _) (by positivity)
      have hnn : 0 ≤ sqrt k * L ^ 3 := by positivity
      linarith only [hmul, hnn]
    have h2e : |2 * εj| ≤ 20 * sqrt k * L := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith only [ha_box]
    have hs1 := hsq_diff (v1 - ηm * u1) (2 * εj) hq1 h2e
    have hs2 := hsq_diff (v2 - ηm * u2) (-2 * εj) hq2
      (by rw [show -(2 : ℝ) * εj = -(2 * εj) by ring, abs_neg]; exact h2e)
    let Dm : ℝ := 2 * ηm * (1 - ηm) * Nm
    have hDm_lo : (3 / 10 : ℝ) * k ≤ Dm := by
      dsimp [Dm]
      have h1 : (2 / 10 : ℝ) ≤ ηm * (1 - ηm) := by nlinarith only [hηm_lo, hηm_hi]
      have hmul := mul_le_mul h1 hNm_lo (by positivity) (by linarith only [h1])
      linarith only [hmul, hk_pos]
    have hDm_diff : |Dm - (4 / 9 : ℝ) * k| ≤ 10 * sqrt k * L := by
      have h1 : Dm - (4 / 9 : ℝ) * k =
          2 * (ηm * (1 - ηm) - 2 / 9) * Nm + (4 / 9) * (Nm - k) := by
        dsimp [Dm]; ring
      have hη_quad : |ηm * (1 - ηm) - 2 / 9| ≤ 2 * L / sqrt k := by
        have heq : ηm * (1 - ηm) - 2 / 9 = (ηm - 2 / 3) * (1 / 3 - ηm) := by ring
        rw [heq, abs_mul]
        have h2 : |1 / 3 - ηm| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        exact (mul_le_mul hb.2.2.2.2.2 h2 (abs_nonneg _) (by positivity)).trans (by linarith)
      have hNm_diff : |Nm - k| ≤ sqrt k * L := by
        have heq : Nm - k = (1 / 2) * ((m : ℝ) - 2 * k) := by dsimp [Nm]; ring
        rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith
      rw [h1]
      have htri := abs_add_le (2 * (ηm * (1 - ηm) - 2 / 9) * Nm) ((4 / 9) * (Nm - k))
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hNm_pos,
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 9)] at htri
      have hmul : 2 * (2 * L / sqrt k) * Nm ≤ 6 * sqrt k * L := by
        have h2 : (2 * L / sqrt k) * ((11 / 10 : ℝ) * k) =
            (22 / 10) * sqrt k * L := by
          calc (2 * L / sqrt k) * ((11 / 10 : ℝ) * k)
              = (22 / 10) * L * ((sqrt k * sqrt k) / sqrt k) := by
                rw [mul_self_sqrt hk_pos.le]; ring
            _ = (22 / 10) * sqrt k * L := by field_simp [hsq_pos.ne']
        have h3 := mL hNm_hi (show 0 ≤ 2 * L / sqrt k by positivity)
        have hnn : 0 ≤ sqrt k * L := by positivity
        linarith only [h2, h3, hnn]
      have hterm1 : 2 * |ηm * (1 - ηm) - 2 / 9| * Nm ≤ 2 * (2 * L / sqrt k) * Nm :=
        mR (mL hη_quad (by norm_num)) hNm_pos.le
      have hnn : 0 ≤ sqrt k * L := by positivity
      linarith only [htri, hterm1, hmul, hNm_diff, hnn]
    have hDm_pos : 0 < Dm := by linarith only [hDm_lo, hk_pos]
    have hrew : (v1 - ηm * u1) ^ 2 / Dm + (v2 - ηm * u2) ^ 2 / Dm - 18 * εj ^ 2 / (k : ℝ) =
        ((v1 - ηm * u1) ^ 2 - (2 * εj) ^ 2) / Dm +
        ((v2 - ηm * u2) ^ 2 - (-2 * εj) ^ 2) / Dm +
        8 * εj ^ 2 * ((4 / 9 : ℝ) * k - Dm) / (Dm * ((4 / 9 : ℝ) * k)) := by
      field_simp [hDm_pos.ne', hk_pos.ne']; ring
    change |(v1 - ηm * u1) ^ 2 / Dm + (v2 - ηm * u2) ^ 2 / Dm - 18 * εj ^ 2 / (k : ℝ)| ≤ _
    rw [hrew]
    have htri := abs_add3_le (((v1 - ηm * u1) ^ 2 - (2 * εj) ^ 2) / Dm)
      (((v2 - ηm * u2) ^ 2 - (-2 * εj) ^ 2) / Dm)
      (8 * εj ^ 2 * ((4 / 9 : ℝ) * k - Dm) / (Dm * ((4 / 9 : ℝ) * k)))
    have hp1 : |((v1 - ηm * u1) ^ 2 - (2 * εj) ^ 2) / Dm| ≤ 20000 * (L ^ 3 / sqrt k) := by
      rw [abs_div, abs_of_pos hDm_pos, div_le_iff₀ hDm_pos]
      have h2 : 20000 * (L ^ 3 / sqrt k) * ((3 / 10 : ℝ) * k) =
          6000 * sqrt k * L ^ 3 := by
        calc 20000 * (L ^ 3 / sqrt k) * ((3 / 10 : ℝ) * k)
            = 6000 * L ^ 3 * ((sqrt k * sqrt k) / sqrt k) := by
              rw [mul_self_sqrt hk_pos.le]; ring
          _ = 6000 * sqrt k * L ^ 3 := by field_simp [hsq_pos.ne']
      have h3 := mL hDm_lo
        (show 0 ≤ 20000 * (L ^ 3 / sqrt k) by positivity)
      linarith only [hs1, h2, h3]
    have hp2 : |((v2 - ηm * u2) ^ 2 - (-2 * εj) ^ 2) / Dm| ≤ 20000 * (L ^ 3 / sqrt k) := by
      rw [abs_div, abs_of_pos hDm_pos, div_le_iff₀ hDm_pos]
      have h2 : 20000 * (L ^ 3 / sqrt k) * ((3 / 10 : ℝ) * k) =
          6000 * sqrt k * L ^ 3 := by
        calc 20000 * (L ^ 3 / sqrt k) * ((3 / 10 : ℝ) * k)
            = 6000 * L ^ 3 * ((sqrt k * sqrt k) / sqrt k) := by
              rw [mul_self_sqrt hk_pos.le]; ring
          _ = 6000 * sqrt k * L ^ 3 := by field_simp [hsq_pos.ne']
      have h3 := mL hDm_lo
        (show 0 ≤ 20000 * (L ^ 3 / sqrt k) by positivity)
      linarith only [hs2, h2, h3]
    have hp3 : |8 * εj ^ 2 * ((4 / 9 : ℝ) * k - Dm) / (Dm * ((4 / 9 : ℝ) * k))| ≤
        100000 * (L ^ 3 / sqrt k) := by
      have hDm_k_pos : 0 < Dm * ((4 / 9 : ℝ) * k) := mul_pos hDm_pos (by positivity)
      rw [abs_div, abs_of_pos hDm_k_pos,
        abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8), abs_of_nonneg (sq_nonneg εj),
        abs_sub_comm]
      have he2' : εj ^ 2 ≤ 100 * (k : ℝ) * L ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg εj) ha_box 2
        rw [sq_abs, mul_pow, mul_pow, sq_sqrt hk_pos.le] at h; linarith only [h]
      have hnum : 8 * εj ^ 2 * |Dm - (4 / 9 : ℝ) * k| ≤
          8000 * ((k : ℝ) * sqrt k) * L ^ 3 := by
        have hmul := mul_le_mul he2' hDm_diff (abs_nonneg _) (by positivity)
        linarith only [hmul]
      have hden : (1 / 10 : ℝ) * (k : ℝ) ^ 2 ≤ Dm * ((4 / 9 : ℝ) * k) := by
        have := mR hDm_lo (show 0 ≤ (4 / 9 : ℝ) * k by positivity)
        have hk2 : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
        linarith only [this, hk2]
      rw [div_le_iff₀ hDm_k_pos]
      have h2 : 100000 * (L ^ 3 / sqrt k) * ((1 / 10 : ℝ) * (k : ℝ) ^ 2) =
          10000 * ((k : ℝ) * sqrt k) * L ^ 3 := by
        rw [show (k : ℝ) ^ 2 = (k : ℝ) * (sqrt k * sqrt k) by
          rw [mul_self_sqrt hk_pos.le]; ring]
        field_simp [hsq_pos.ne']; ring
      have h3 := mL hden
        (show 0 ≤ 100000 * (L ^ 3 / sqrt k) by positivity)
      have hnn : 0 ≤ ((k : ℝ) * sqrt k) * L ^ 3 := by positivity
      linarith only [hnum, h2, h3, hnn]
    have hnn3 : 0 ≤ L ^ 3 / sqrt k := by positivity
    linarith only [htri, hp1, hp2, hp3, hnn3]
  have hMj_pos : 0 < (j.choose (2 * a + d1) : ℝ) *
      ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) := by
    have h1 : 2 * a + d1 ≤ j := by
      have : ((2 * a + d1 : ℕ) : ℝ) ≤ j := by
        have ha' : ((2 * a + d1 : ℕ) : ℝ) = Rm + v1 := by linarith only [hv1_eq]
        have hj' : (j : ℝ) = Nm + u1 := by linarith only [hu1_eq]
        rw [ha', hj']
        dsimp [Rm]
        linarith only [(abs_le.mp hW_v1).2, (abs_le.mp hW_u1).1, hNm_lo, hb.2.2.2.1, hsqL, hk_pos]
      exact_mod_cast this
    have h2 : 2 * (f - a - d1) + 1 - d2 ≤ m - j - 1 := by
      have : ((2 * (f - a - d1) + 1 - d2 : ℕ) : ℝ) ≤ ((m - j - 1 : ℕ) : ℝ) := by
        have ha' : ((2 * (f - a - d1) + 1 - d2 : ℕ) : ℝ) = Rm + v2 := by linarith only [hv2_eq]
        have hj' : ((m - j - 1 : ℕ) : ℝ) = Nm + u2 := by linarith only [hu2_eq]
        rw [ha', hj']
        dsimp [Rm]
        linarith only [(abs_le.mp hW_v2).2, (abs_le.mp hW_u2).1, hNm_lo, hb.2.2.2.1, hsqL, hk_pos]
      exact_mod_cast this
    have hc1 : 0 < j.choose (2 * a + d1) := Nat.choose_pos h1
    have hc2 : 0 < (m - j - 1).choose (2 * (f - a - d1) + 1 - d2) := Nat.choose_pos h2
    positivity
  have hGM_eq : GM = exp (2 * logG Nm Rm +
      log ((if d1 = 0 then (1 - ηm) / ηm else 1) * (if d2 = 0 then 1 - ηm else ηm)) -
      18 * εj ^ 2 / (k : ℝ)) := by
    have hif1 : 0 < (if d1 = 0 then (1 - ηm) / ηm else 1) := by
      split_ifs <;> [exact div_pos (by linarith only [hηm_hi]) (by linarith only [hηm_lo]); norm_num]
    have hif2 : 0 < (if d2 = 0 then 1 - ηm else ηm) := by
      split_ifs <;> linarith only [hηm_lo, hηm_hi]
    rw [sub_eq_add_neg, exp_add, exp_add, exp_log (mul_pos hif1 hif2),
      show -(18 * εj ^ 2 / (k : ℝ)) = -18 * εj ^ 2 / (k : ℝ) by ring]
    change (if d1 = 0 then (1 - ηm) / ηm else 1) * exp (2 * logG Nm Rm) *
      (if d2 = 0 then 1 - ηm else ηm) * exp (-18 * εj ^ 2 / (k : ℝ)) = _
    ring
  have hlog_Mj : |log ((j.choose (2 * a + d1) : ℝ) *
      ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ)) -
      (2 * logG Nm Rm +
        log ((if d1 = 0 then (1 - ηm) / ηm else 1) * (if d2 = 0 then 1 - ηm else ηm)) -
        18 * εj ^ 2 / (k : ℝ))| ≤ 9e9 * (L ^ 3 / sqrt k) := by
    have hc1_pos : (0 : ℝ) < (j.choose (2 * a + d1) : ℝ) := by
      by_contra h; push Not at h
      have h0 : (j.choose (2 * a + d1) : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
      rw [h0, zero_mul] at hMj_pos; exact lt_irrefl 0 hMj_pos
    have hc2_pos : (0 : ℝ) < ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) := by
      by_contra h; push Not at h
      have h0 : ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) = 0 :=
        le_antisymm h (Nat.cast_nonneg _)
      rw [h0, mul_zero] at hMj_pos; exact lt_irrefl 0 hMj_pos
    rw [log_mul hc1_pos.ne' hc2_pos.ne']
    have hsplit : log (j.choose (2 * a + d1) : ℝ) +
        log ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) -
        (2 * logG Nm Rm +
          log ((if d1 = 0 then (1 - ηm) / ηm else 1) * (if d2 = 0 then 1 - ηm else ηm)) -
          18 * εj ^ 2 / (k : ℝ)) =
        (log (j.choose (2 * a + d1) : ℝ) - (logG Nm Rm + u1 * log (1 / (1 - ηm)) +
          v1 * log ((1 - ηm) / ηm) - (v1 - ηm * u1) ^ 2 / (2 * ηm * (1 - ηm) * Nm))) +
        (log ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) -
          (logG Nm Rm + u2 * log (1 / (1 - ηm)) + v2 * log ((1 - ηm) / ηm) -
            (v2 - ηm * u2) ^ 2 / (2 * ηm * (1 - ηm) * Nm))) -
        ((v1 - ηm * u1) ^ 2 / (2 * ηm * (1 - ηm) * Nm) +
          (v2 - ηm * u2) ^ 2 / (2 * ηm * (1 - ηm) * Nm) - 18 * εj ^ 2 / (k : ℝ)) := by
      rw [← hlin_sum]; ring
    rw [hsplit]
    have htri := abs_add_sub_le
      (log (j.choose (2 * a + d1) : ℝ) - (logG Nm Rm + u1 * log (1 / (1 - ηm)) +
        v1 * log ((1 - ηm) / ηm) - (v1 - ηm * u1) ^ 2 / (2 * ηm * (1 - ηm) * Nm)))
      (log ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) -
        (logG Nm Rm + u2 * log (1 / (1 - ηm)) + v2 * log ((1 - ηm) / ηm) -
          (v2 - ηm * u2) ^ 2 / (2 * ηm * (1 - ηm) * Nm)))
      ((v1 - ηm * u1) ^ 2 / (2 * ηm * (1 - ηm) * Nm) +
        (v2 - ηm * u2) ^ 2 / (2 * ηm * (1 - ηm) * Nm) - 18 * εj ^ 2 / (k : ℝ))
    have he1' : |log (j.choose (2 * a + d1) : ℝ) - (logG Nm Rm + u1 * log (1 / (1 - ηm)) +
        v1 * log ((1 - ηm) / ηm) - (v1 - ηm * u1) ^ 2 / (2 * ηm * (1 - ηm) * Nm))| ≤
        4e9 * (L ^ 3 / sqrt k) := he1
    have he2' : |log ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) -
        (logG Nm Rm + u2 * log (1 / (1 - ηm)) + v2 * log ((1 - ηm) / ηm) -
          (v2 - ηm * u2) ^ 2 / (2 * ηm * (1 - ηm) * Nm))| ≤
        4e9 * (L ^ 3 / sqrt k) := he2
    have hnn3 : 0 ≤ L ^ 3 / sqrt k := by positivity
    linarith only [htri, he1', he2', hquad_diff, hnn3]
  have hL3_tiny : 9e9 * (L ^ 3 / sqrt k) ≤ 1 / 2 := by
    have hL12 : (10 ^ 12 : ℝ) * L ^ 3 ≤ L ^ 15 := by
      have h1 := pow_le_pow_left₀ (by norm_num) hL10 12
      have h2 := mR h1 (pow_nonneg (by linarith only [hL10]) 3)
      rwa [← pow_add] at h2
    have hdiv : (10 ^ 12 : ℝ) * (L ^ 3 / sqrt k) ≤ L ^ 15 / sqrt k := by
      rw [mul_div_assoc']; exact dR hL12 hsq_pos.le
    have hL15 : L ^ 15 / sqrt k ≤ 1 / 10 ^ 6 := hV.2.2.1
    linarith only [hdiv, hL15]
  have h := abs_sub_exp_of_log_approx hMj_pos hlog_Mj hL3_tiny
  rw [← hGM_eq] at h
  have hGM_nn : 0 ≤ GM := by
    dsimp [GM]
    exact mul_nonneg (mul_nonneg (cK_cM_bounds hV hd1).2.2.1.le (cK_cM_bounds hV hd2).2.2.2.2.1.le)
      (exp_pos _).le
  have hle : 2 * (9e9 * (L ^ 3 / sqrt k)) ≤ (2e10 : ℝ) * (L ^ 3 / sqrt k) := by
    have : 0 ≤ L ^ 3 / sqrt k := by positivity
    linarith
  exact h.trans (mR hle hGM_nn)

private def InBox (k m f j t a b : ℕ) : Prop :=
  let L := log k
  |δ_coord m j| ≤ 40 * sqrt k * L ∧
  |δ_coord m t| ≤ 40 * sqrt k * L ∧
  |ε_coord m f j a| ≤ 10 * sqrt k * L ∧
  |(b : ℝ) - (a : ℝ) - ((t : ℝ) - (j : ℝ)) / 3| ≤ 20 * sqrt ((t - j - 1 : ℕ) : ℝ) * L

private lemma deltaK_universal_tail {k m f d j a : ℕ} (hV : ValidMF k m f)
    (hd : d ∈ ({0, 1} : Finset ℕ)) (hj : j < m) (ha : a + d ≤ f) :
    |deltaK k a (f - a - d) j (m - 1 - j)| ≤
      500 * (((2 * k + 1 + f).choose m : ℕ) : ℝ) *
        exp (-((j : ℝ) - ((k + a + 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ) /
          (((k + a + 1 : ℕ) : ℝ) + ((k + (f - a - d) + 1 : ℕ) : ℝ))) ^ 2 / (16 * (k : ℝ))) := by
  let A' : ℕ := k + a + 1
  let B' : ℕ := k + (f - a - d) + 1
  let μj : ℝ := (A' : ℝ) * ((m - 1 : ℕ) : ℝ) / ((A' : ℝ) + B')
  change |deltaK k a (f - a - d) j (m - 1 - j)| ≤
    500 * (((2 * k + 1 + f).choose m : ℕ) : ℝ) *
      exp (-((j : ℝ) - μj) ^ 2 / (16 * (k : ℝ)))
  have hb := validMF_eta_bounds hV
  have ⟨hk, _, _, _, _, _⟩ := hV
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hd_le1 : d ≤ 1 := by simp only [mem_insert, mem_singleton] at hd; rcases hd with rfl | rfl <;> omega
  have hdelta : deltaK k a (f - a - d) j (m - 1 - j) =
      (((m - 1 - j : ℕ) * (A' : ℝ) - (j : ℝ) * (B' : ℝ)) / ((A' : ℝ) * (B' : ℝ))) *
        ((A'.choose j : ℝ) * (B'.choose ((m - 1) - j) : ℝ)) := by
    unfold deltaK
    have := deltaK_exact_identity (k + a) (k + (f - a - d)) j (m - 1 - j)
    have hA' : k + 1 + a = A' := by omega
    have hB' : k + 1 + (f - a - d) = B' := by omega
    have hA'R : ((k + a : ℕ) : ℝ) + 1 = A' := by push_cast [A']; ring
    have hB'R : ((k + (f - a - d) : ℕ) : ℝ) + 1 = B' := by push_cast [B']; ring
    rw [hA', hB']
    simpa only [A', B', hA'R, hB'R, show k + a + 1 = A' by omega,
      show k + (f - a - d) + 1 = B' by omega] using this
  have hfac_le : |((m - 1 - j : ℕ) * (A' : ℝ) - (j : ℝ) * (B' : ℝ)) / ((A' : ℝ) * (B' : ℝ))| ≤ 4 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < A' * B'), div_le_iff₀ (by positivity)]
    have hA'1 : (k : ℝ) ≤ A' := by exact_mod_cast (show k ≤ A' by omega)
    have hB'1 : (k : ℝ) ≤ B' := by exact_mod_cast (show k ≤ B' by omega)
    have hm_le : (m : ℝ) ≤ 4 * k := by linarith [hb.2.1]
    have h1 : ((m - 1 - j : ℕ) : ℝ) ≤ m := by exact_mod_cast (show m - 1 - j ≤ m by omega)
    have h2 : (j : ℝ) ≤ m := by exact_mod_cast (le_of_lt hj)
    have h3 : ((m - 1 - j : ℕ) : ℝ) * A' ≤ 4 * (A' : ℝ) * B' := by nlinarith
    have h4 : (j : ℝ) * B' ≤ 4 * (A' : ℝ) * B' := by nlinarith
    rw [abs_le]; constructor <;> nlinarith
  have hut := hypergeom_universal_tail A' B' (m - 1) j (by omega) (by omega)
  have hA'_hi : (A' : ℝ) ≤ 2 * k := by
    have : (a : ℝ) ≤ f := by exact_mod_cast (show a ≤ f by omega)
    dsimp [A']; push_cast; linarith [hb.2.2.2.1]
  have hexp_mono : exp (-((j : ℝ) - μj) ^ 2 / (8 * (A' : ℝ))) ≤
      exp (-((j : ℝ) - μj) ^ 2 / (16 * (k : ℝ))) := by
    apply exp_le_exp.mpr
    have hA'_pos : (0 : ℝ) < 8 * A' := by positivity
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hA'_pos (by linarith)
  have hch_le : (((A' + B').choose (m - 1) : ℕ) : ℝ) ≤ 60 * (((2 * k + 1 + f).choose m : ℕ) : ℝ) := by
    have hN_le : m + 1 ≤ 2 * k + 1 + f := by
      have : (m : ℝ) + 1 ≤ (2 * k + 1 + f : ℕ) := by push_cast; linarith [hb.2.1, hb.2.2.1]
      exact_mod_cast this
    have hN_gap : 5 * (2 * k + 1 + f - m) ≥ 2 * k + 1 + f := by
      have hle : m ≤ 2 * k + 1 + f := by omega
      have hR : ((2 * k + 1 + f : ℕ) : ℝ) ≤ 5 * (((2 * k + 1 + f - m : ℕ) : ℝ)) := by
        rw [Nat.cast_sub hle]; push_cast; linarith [hb.2.1, hb.2.2.1]
      exact_mod_cast hR
    have hnear := choose_nearby_le (2 * k + 1 + f) m hN_le hN_gap
    have hcases : A' + B' = 2 * k + 1 + f ∨ A' + B' = (2 * k + 1 + f) + 1 := by omega
    rcases hcases with h | h
    · rw [h]; linarith [hnear.1, Nat.cast_nonneg (α := ℝ) ((2 * k + 1 + f).choose m)]
    · rw [h]; exact hnear.2
  rw [hdelta, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (A'.choose j : ℝ) * (B'.choose (m - 1 - j) : ℝ))]
  calc |((m - 1 - j : ℕ) * (A' : ℝ) - (j : ℝ) * (B' : ℝ)) / ((A' : ℝ) * (B' : ℝ))| *
        ((A'.choose j : ℝ) * (B'.choose (m - 1 - j) : ℝ))
      ≤ 4 * (2 * (((A' + B').choose (m - 1) : ℕ) : ℝ) *
          exp (-((j : ℝ) - μj) ^ 2 / (8 * (A' : ℝ)))) :=
        mul_le_mul hfac_le hut (by positivity) (by norm_num)
    _ ≤ 4 * (2 * (60 * (((2 * k + 1 + f).choose m : ℕ) : ℝ)) *
          exp (-((j : ℝ) - μj) ^ 2 / (8 * (A' : ℝ)))) := by
        apply mL _ (by norm_num)
        apply mR _ (exp_pos _).le
        exact mL hch_le (by norm_num)
    _ ≤ 4 * (2 * (60 * (((2 * k + 1 + f).choose m : ℕ) : ℝ)) *
          exp (-((j : ℝ) - μj) ^ 2 / (16 * (k : ℝ)))) := by
        apply mL _ (by norm_num)
        exact mL hexp_mono (by positivity)
    _ ≤ 500 * (((2 * k + 1 + f).choose m : ℕ) : ℝ) *
          exp (-((j : ℝ) - μj) ^ 2 / (16 * (k : ℝ))) := by
        have : 0 ≤ (((2 * k + 1 + f).choose m : ℕ) : ℝ) *
            exp (-((j : ℝ) - μj) ^ 2 / (16 * (k : ℝ))) := by positivity
        linarith

private lemma choose_le_choose_succ_left (n r : ℕ) : n.choose r ≤ (n + 1).choose r := by
  cases r with
  | zero => simp
  | succ r' => rw [Nat.choose_succ_succ]; simp only [Nat.succ_eq_add_one]; omega

private lemma choose_le_choose_succ_both (n r : ℕ) : n.choose r ≤ (n + 1).choose (r + 1) := by
  rw [Nat.choose_succ_succ]; omega

private lemma choose_mul_choose_le (A B S r : ℕ) (hr : r ≤ S) :
    A.choose r * B.choose (S - r) ≤ (A + B).choose S := by
  have hR : (A.choose r : ℝ) * (B.choose (S - r) : ℝ) ≤ ((A + B).choose S : ℝ) := by
    rw [← sum_hypergeom A B S]
    exact single_le_sum (f := fun i => (A.choose i : ℝ) * (B.choose (S - i) : ℝ))
      (fun _ _ => by positivity) (mem_range.mpr (by omega))
  exact_mod_cast (by simpa only [Nat.cast_mul] using hR :
    ((A.choose r * B.choose (S - r) : ℕ) : ℝ) ≤ ((A + B).choose S : ℕ))

set_option maxHeartbeats 1600000 in
private lemma regime2_outside_box_pointwise {k m f d1 d2 j t a b : ℕ} (hV : ValidMF k m f)
    (hd1 : d1 ∈ ({0, 1} : Finset ℕ)) (hd2 : d2 ∈ ({0, 1} : Finset ℕ))
    (hj : 1 ≤ j) (hjt : j + ⌊log k ^ 7⌋₊ < t) (htm : t < m)
    (ha : a + d1 ≤ b) (hb_le : b + d2 ≤ f)
    (hout : ¬ InBox k m f j t a b) :
    ((j.choose (2 * a + d1) * (t - j - 1).choose (2 * (b - a - d1) + d2) *
        (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) *
      |deltaK k a (f - a - d1) j (m - 1 - j)| *
      |deltaK k b (f - b - d2) t (m - 1 - t)| ≤
      (1 / (k : ℝ) ^ 6) * (((m + 1).choose (2 * f + 1) : ℕ) : ℝ) *
        (((2 * k + 1 + f).choose m : ℕ) : ℝ) ^ 2 := by
  have hba := validMF_eta_bounds hV
  have hsqL := validMF_sqL_le hV
  have ⟨hk, hL, hL15, hexpL, hm_box, hf_box⟩ := hV
  let L := log k
  change 10 ^ 20 ≤ L at hL
  have hL10 : (10 : ℝ) ≤ L := by linarith only [hL]
  change L ^ 15 / sqrt k ≤ 1 / 10 ^ 6 at hL15
  change (k : ℝ) ^ 10 * exp (-L ^ 2) ≤ 1 at hexpL
  change |(m : ℝ) - 2 * k| ≤ sqrt k * L at hm_box
  change |(f : ℝ) - 2 * (k : ℝ) / 3| ≤ sqrt k * L at hf_box
  change sqrt k * L ≤ (k : ℝ) / 10 ^ 6 at hsqL
  let B0 : ℝ := ((2 * k + 1 + f).choose m : ℝ)
  let N0 : ℝ := ((m + 1).choose (2 * f + 1) : ℝ)
  let Cval : ℝ := ((j.choose (2 * a + d1) * (t - j - 1).choose (2 * (b - a - d1) + d2) *
      (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ)
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hsq_ge1 : (1 : ℝ) ≤ sqrt k := by
    rw [le_sqrt (by norm_num) hk_pos.le]; linarith only [hkR]
  have hsqL_ge10 : (10 : ℝ) ≤ sqrt k * L := by
    have := mul_le_mul hsq_ge1 hL10 (by norm_num) hsq_pos.le
    linarith only [this]
  have hB0_nn : 0 ≤ B0 := Nat.cast_nonneg _
  have hN0_nn : 0 ≤ N0 := Nat.cast_nonneg _
  have hd1_le1 : d1 ≤ 1 := by simp only [mem_insert, mem_singleton] at hd1; rcases hd1 with rfl | rfl <;> omega
  have hd2_le1 : d2 ≤ 1 := by simp only [mem_insert, mem_singleton] at hd2; rcases hd2 with rfl | rfl <;> omega
  have hwin_exp : (10 ^ 6 : ℝ) * N0 * B0 ^ 2 * exp (-9 * L ^ 2) ≤ (1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2 := by
    have h1 : exp (-9 * L ^ 2) ≤ exp (-L ^ 2) := exp_le_exp.mpr (by nlinarith)
    have h2 : (10 ^ 6 : ℝ) * exp (-L ^ 2) ≤ 1 / (k : ℝ) ^ 6 := by
      rw [le_div_iff₀ (by positivity)]
      have hk4 : (10 ^ 6 : ℝ) * (k : ℝ) ^ 6 ≤ (k : ℝ) ^ 10 := by
        have hk24 : (10 ^ 6 : ℝ) ≤ (k : ℝ) ^ 4 := by
          have : (k : ℝ) ^ 1 ≤ (k : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by omega)
          linarith
        have := mR hk24 (pow_nonneg hk_pos.le 6)
        rwa [← pow_add] at this
      have := mR hk4 (exp_pos (-L ^ 2)).le
      linarith
    have h3 := mL (h1.trans (by linarith [exp_pos (-L ^ 2)] :
      exp (-L ^ 2) ≤ exp (-L ^ 2))) (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
    have h4 : (10 ^ 6 : ℝ) * exp (-9 * L ^ 2) ≤ 1 / (k : ℝ) ^ 6 :=
      (mL h1 (by norm_num)).trans h2
    have hmul := mR h4 (show 0 ≤ N0 * B0 ^ 2 by positivity)
    linarith
  have hexp_le1 : ∀ (x : ℝ), 500 * B0 * exp (-x ^ 2 / (16 * (k : ℝ))) ≤ 500 * B0 := fun x => by
    have h1 : exp (-x ^ 2 / (16 * (k : ℝ))) ≤ 1 :=
      exp_le_one_iff.mpr (by rw [neg_div, neg_nonpos]; positivity)
    simpa only [mul_one] using mL h1 (by positivity : 0 ≤ 500 * B0)
  have hdj_tail := deltaK_universal_tail hV hd1 (by omega : j < m) (by omega : a + d1 ≤ f)
  have hdt_tail := deltaK_universal_tail hV hd2 htm (by omega : b + d2 ≤ f)
  have hdj_base : |deltaK k a (f - a - d1) j (m - 1 - j)| ≤ 500 * B0 :=
    hdj_tail.trans (hexp_le1 _)
  have hdt_base : |deltaK k b (f - b - d2) t (m - 1 - t)| ≤ 500 * B0 :=
    hdt_tail.trans (hexp_le1 _)
  have hC_j_le : Cval ≤ (j.choose (2 * a + d1) : ℝ) * ((m - j).choose (2 * (f - a - d1) + 1) : ℝ) := by
    let D := t - j - 1
    let M2 := m - t
    let S2 := 2 * (f - a - d1) + 1 - d2
    let r := 2 * (b - a - d1) + d2
    have hS2r : S2 - r = 2 * (f - b - d2) + 1 := by omega
    have hDM : D + M2 = m - j - 1 := by omega
    have hpair_le : D.choose r * M2.choose (2 * (f - b - d2) + 1) ≤ (D + M2).choose S2 := by
      rw [← hS2r]
      exact choose_mul_choose_le D M2 S2 r (by omega)
    have hpas : (m - j - 1).choose S2 ≤ (m - j).choose (2 * (f - a - d1) + 1) := by
      have hm1 : m - j - 1 + 1 = m - j := by omega
      simp only [mem_insert, mem_singleton] at hd2
      rcases hd2 with rfl | rfl
      · have hS2' : S2 = 2 * (f - a - d1) + 1 := by omega
        rw [hS2', ← hm1]; exact choose_le_choose_succ_left _ _
      · have hS2' : S2 + 1 = 2 * (f - a - d1) + 1 := by omega
        rw [← hS2', ← hm1]; exact choose_le_choose_succ_both _ _
    have hnat : j.choose (2 * a + d1) * (D.choose r * M2.choose (2 * (f - b - d2) + 1)) ≤
        j.choose (2 * a + d1) * (m - j).choose (2 * (f - a - d1) + 1) :=
      Nat.mul_le_mul_left _ (hpair_le.trans (by rwa [hDM] at *))
    dsimp [Cval]; push_cast
    have hR : ((j.choose (2 * a + d1) * D.choose r * M2.choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) ≤
        ((j.choose (2 * a + d1) * (m - j).choose (2 * (f - a - d1) + 1) : ℕ) : ℝ) := by
      exact_mod_cast (by simpa only [Nat.mul_assoc] using hnat)
    push_cast at hR; exact hR
  have hC_t_le : Cval ≤ (t.choose (2 * b + d2) : ℝ) * ((m - t).choose (2 * (f - b - d2) + 1) : ℝ) := by
    let D := t - j - 1
    let r1 := 2 * a + d1
    let r2 := 2 * (b - a - d1) + d2
    have hsum_r : r1 + r2 = 2 * b + d2 - d1 := by omega
    have hjD : j + D = t - 1 := by omega
    have hpair_le : j.choose r1 * D.choose r2 ≤ (j + D).choose (r1 + r2) := by
      simpa only [Nat.add_sub_cancel_left] using choose_mul_choose_le j D (r1 + r2) r1 (by omega)
    have hpas : (t - 1).choose (r1 + r2) ≤ t.choose (2 * b + d2) := by
      have ht1 : t - 1 + 1 = t := by omega
      simp only [mem_insert, mem_singleton] at hd1
      rcases hd1 with rfl | rfl
      · have : r1 + r2 = 2 * b + d2 := by omega
        rw [this, ← ht1]; exact choose_le_choose_succ_left _ _
      · have : r1 + r2 + 1 = 2 * b + d2 := by omega
        rw [← this, ← ht1]; exact choose_le_choose_succ_both _ _
    have hnat : j.choose r1 * D.choose r2 * (m - t).choose (2 * (f - b - d2) + 1) ≤
        t.choose (2 * b + d2) * (m - t).choose (2 * (f - b - d2) + 1) :=
      Nat.mul_le_mul_right _ (hpair_le.trans (by rwa [hjD] at *))
    dsimp [Cval]; push_cast
    have hR : ((j.choose r1 * D.choose r2 * (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) ≤
        ((t.choose (2 * b + d2) * (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hR; exact hR
  have hpair_N0 : ∀ (pos c d : ℕ), 1 ≤ pos → pos < m → c + d ≤ f → d ∈ ({0, 1} : Finset ℕ) →
      (pos.choose (2 * c + d) : ℝ) * ((m - pos).choose (2 * (f - c - d) + 1) : ℝ) ≤
        2 * N0 * exp (-(((2 * c + d : ℕ) : ℝ) -
          (pos : ℝ) * ((2 * f + 1 - d : ℕ) : ℝ) / (m : ℝ)) ^ 2 / (24 * (k : ℝ))) := by
    intro pos c d hpos1 hposm hcf hd'
    have hd'_le1 : d ≤ 1 := by simp only [mem_insert, mem_singleton] at hd'; rcases hd' with rfl | rfl <;> omega
    let S := 2 * f + 1 - d
    have hSsub : S - (2 * c + d) = 2 * (f - c - d) + 1 := by omega
    have hpm : pos + (m - pos) = m := by omega
    have hle_S : 2 * c + d ≤ S := by omega
    have hut := hypergeom_universal_tail pos (m - pos) S (2 * c + d) hpos1 hle_S
    rw [hSsub, hpm] at hut
    have hm_cast : (pos : ℝ) + ((m - pos : ℕ) : ℝ) = m := by rw [Nat.cast_sub (le_of_lt hposm)]; ring
    rw [hm_cast] at hut
    have hch_N0 : (m.choose S : ℝ) ≤ N0 := by
      have hnat : m.choose S ≤ (m + 1).choose (2 * f + 1) := by
        simp only [mem_insert, mem_singleton] at hd'
        rcases hd' with rfl | rfl
        · have : S = 2 * f + 1 := by omega
          rw [this]; exact choose_le_choose_succ_left _ _
        · have : S + 1 = 2 * f + 1 := by omega
          rw [← this]; exact choose_le_choose_succ_both _ _
      dsimp [N0]; exact_mod_cast hnat
    have hexp_mono : exp (-(((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)) ^ 2 / (8 * (pos : ℝ))) ≤
        exp (-(((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)) ^ 2 / (24 * (k : ℝ))) := by
      apply exp_le_exp.mpr
      have hpos_le : (pos : ℝ) ≤ 3 * k := by
        have : (pos : ℝ) ≤ m := by exact_mod_cast (le_of_lt hposm)
        linarith [hba.2.1]
      have hpos_p : (0 : ℝ) < 8 * pos := by
        have : (0 : ℝ) < pos := by exact_mod_cast (show 0 < pos by omega)
        linarith
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hpos_p (by linarith)
    calc (pos.choose (2 * c + d) : ℝ) * ((m - pos).choose (2 * (f - c - d) + 1) : ℝ)
        ≤ 2 * (m.choose S : ℝ) *
            exp (-(((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)) ^ 2 / (8 * (pos : ℝ))) := hut
      _ ≤ 2 * N0 *
            exp (-(((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)) ^ 2 / (8 * (pos : ℝ))) := by
          apply mR _ (exp_pos _).le
          exact mL hch_N0 (by norm_num)
      _ ≤ 2 * N0 *
            exp (-(((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)) ^ 2 / (24 * (k : ℝ))) := by
          exact mL hexp_mono (by positivity)
  have hC_base : Cval ≤ 2 * N0 := by
    have h1 := hC_j_le.trans (hpair_N0 j a d1 hj (by omega) (by omega) hd1)
    have hexp24 : ∀ (x : ℝ), 2 * N0 * exp (-x ^ 2 / (24 * (k : ℝ))) ≤ 2 * N0 := fun x => by
      have hle : exp (-x ^ 2 / (24 * (k : ℝ))) ≤ 1 :=
        exp_le_one_iff.mpr (by rw [neg_div, neg_nonpos]; positivity)
      simpa only [mul_one] using mL hle (by positivity : 0 ≤ 2 * N0)
    exact h1.trans (hexp24 _)
  have hpos_box_or_win : ∀ (pos c d : ℕ), 1 ≤ pos → pos < m → c + d ≤ f → d ∈ ({0, 1} : Finset ℕ) →
      Cval ≤ (pos.choose (2 * c + d) : ℝ) * ((m - pos).choose (2 * (f - c - d) + 1) : ℝ) →
      (|δ_coord m pos| ≤ 40 * sqrt k * L ∧ |ε_coord m f pos c| ≤ 10 * sqrt k * L) ∨
      Cval * |deltaK k c (f - c - d) pos (m - 1 - pos)| ≤ 1000 * N0 * B0 * exp (-9 * L ^ 2) := by
    intro pos c d hpos1 hposm hcf hd' hC_pos
    have hd'_le1 : (d : ℝ) ≤ 1 := by
      simp only [mem_insert, mem_singleton] at hd'; rcases hd' with rfl | rfl <;> norm_num
    let S := 2 * f + 1 - d
    by_cases h1 : 15 * sqrt k * L < |((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)|
    · right
      have hpn := hC_pos.trans (hpair_N0 pos c d hpos1 hposm hcf hd')
      have hdk := deltaK_universal_tail hV hd' hposm hcf
      have hdk_b : |deltaK k c (f - c - d) pos (m - 1 - pos)| ≤ 500 * B0 :=
        hdk.trans (hexp_le1 _)
      have hexp : exp (-(((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)) ^ 2 / (24 * (k : ℝ))) ≤
          exp (-9 * L ^ 2) := by
        apply exp_le_exp.mpr
        have hsq : (15 * sqrt k * L) ^ 2 ≤
            (((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)) ^ 2 := by
          rw [← sq_abs (((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ))]
          exact pow_le_pow_left₀ (by positivity) h1.le 2
        have h225 : (15 * sqrt k * L) ^ 2 = 225 * (k : ℝ) * L ^ 2 := by
          rw [mul_pow, mul_pow, sq_sqrt hk_pos.le]; ring
        rw [show (-9 : ℝ) * L ^ 2 = -(9 * L ^ 2) by ring, neg_div, neg_le_neg_iff,
          le_div_iff₀ (by positivity : (0 : ℝ) < 24 * k)]
        have hnn : 0 ≤ (k : ℝ) * L ^ 2 := by positivity
        linarith only [hsq, h225, hnn]
      have hC_exp : Cval ≤ 2 * N0 * exp (-9 * L ^ 2) :=
        hpn.trans (mL hexp (by positivity))
      have hmul := mul_le_mul hC_exp hdk_b (abs_nonneg _) (by positivity)
      linarith
    · push Not at h1
      by_cases h2 : 40 * sqrt k * L < |δ_coord m pos|
      · right
        let A' : ℕ := k + c + 1
        let B' : ℕ := k + (f - c - d) + 1
        let μp : ℝ := (A' : ℝ) * ((m - 1 : ℕ) : ℝ) / ((A' : ℝ) + B')
        have hdk := deltaK_universal_tail hV hd' hposm hcf
        have hm_pos : (0 : ℝ) < m := by linarith [hba.1]
        have hAB_eq : (A' : ℝ) + B' = 2 * k + 2 + f - d := by
          dsimp [A', B']
          have hnat : k + c + 1 + (k + (f - c - d) + 1) + d = 2 * k + 2 + f := by omega
          have hR : ((k + c + 1 + (k + (f - c - d) + 1) + d : ℕ) : ℝ) = ((2 * k + 2 + f : ℕ) : ℝ) := by
            exact_mod_cast hnat
          push_cast at hR ⊢; linarith only [hR]
        have hAB_pos : (0 : ℝ) < (A' : ℝ) + B' := by linarith [hba.2.2.1]
        have hAB_hi : (A' : ℝ) + B' ≤ (27 / 10 : ℝ) * k := by linarith [hba.2.2.2.1]
        have hS_cast : (S : ℝ) = 2 * (f : ℝ) + 1 - d := by
          dsimp [S]; rw [Nat.cast_sub (by omega : d ≤ 2 * f + 1)]; push_cast; ring
        have hc_approx : |(c : ℝ) - (pos : ℝ) * (f : ℝ) / (m : ℝ)| ≤ 8 * sqrt k * L := by
          have heq : (c : ℝ) - (pos : ℝ) * (f : ℝ) / (m : ℝ) =
              (1 / 2) * ((((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)) +
                ((pos : ℝ) * (1 - d) / (m : ℝ) - d)) := by
            rw [hS_cast]; push_cast; field_simp [hm_pos.ne']; ring
          rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          have hpm_le : (pos : ℝ) / (m : ℝ) ≤ 1 := by
            rw [div_le_one hm_pos]; exact_mod_cast (le_of_lt hposm)
          have hrem : |(pos : ℝ) * (1 - d) / (m : ℝ) - d| ≤ 2 := by
            have h0 : 0 ≤ (pos : ℝ) * (1 - d) / (m : ℝ) := by
              apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hm_pos.le
            have hle1 : (pos : ℝ) * (1 - d) / (m : ℝ) ≤ 1 := by
              rw [div_le_iff₀ hm_pos]
              have : (pos : ℝ) ≤ m := by exact_mod_cast (le_of_lt hposm)
              nlinarith [Nat.cast_nonneg (α := ℝ) d]
            rw [abs_le]; constructor <;> linarith
          have h2sq : (2 : ℝ) ≤ sqrt k * L := by linarith only [hsqL_ge10]
          have htri := abs_add_le (((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ))
            ((pos : ℝ) * (1 - d) / (m : ℝ) - d)
          linarith
        have hdist_μp : 16 * sqrt k * L ≤ |(pos : ℝ) - μp| := by
          have hclean : ((A' : ℝ) + B') * ((pos : ℝ) - μp) =
              (2 * (k : ℝ) + 2 - d) * δ_coord m pos -
              (m : ℝ) * ((c : ℝ) - (pos : ℝ) * (f : ℝ) / (m : ℝ)) +
              ((A' : ℝ) - (m : ℝ) * d / 2) := by
            have hm1_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring
            dsimp [μp, δ_coord]
            rw [hm1_cast, hAB_eq]
            have hA'c : (A' : ℝ) = (k : ℝ) + c + 1 := by dsimp [A']; push_cast; ring
            have hden_ne : (2 * (k : ℝ) + 2 + f - d) ≠ 0 := by linarith only [hkR, hd'_le1, hba.2.2.1]
            have heq : ((2 * (k : ℝ) + 2 + f - d) * ((pos : ℝ) -
                (A' : ℝ) * ((m : ℝ) - 1) / (2 * (k : ℝ) + 2 + f - d))) =
                (2 * (k : ℝ) + 2 + f - d) * (pos : ℝ) - (A' : ℝ) * ((m : ℝ) - 1) := by
              rw [mul_sub, mul_div_cancel₀ _ hden_ne]
            rw [heq, hA'c]; field_simp [hm_pos.ne']; ring
          have hrem_le : |(A' : ℝ) - (m : ℝ) * d / 2| ≤ 3 * k := by
            have hA'hi : (A' : ℝ) ≤ 2 * k := by
              have : (c : ℝ) ≤ f := by exact_mod_cast (show c ≤ f by omega)
              dsimp [A']; push_cast; linarith [hba.2.2.2.1]
            have hA'nn : (0 : ℝ) ≤ A' := Nat.cast_nonneg _
            have hmd : 0 ≤ (m : ℝ) * d / 2 ∧ (m : ℝ) * d / 2 ≤ 2 * k := by
              constructor
              · positivity
              · have := mul_le_mul hba.2.1 hd'_le1 (Nat.cast_nonneg d) (by positivity)
                linarith only [this, hk_pos]
            rw [abs_le]; constructor <;> linarith only [hA'hi, hA'nn, hmd.1, hmd.2]
          have h3k_le : 3 * (k : ℝ) ≤ (k : ℝ) * sqrt k * L := by
            have h1 : (3 : ℝ) ≤ sqrt k * L := by linarith only [hsqL_ge10]
            have := mL h1 hk_pos.le
            linarith only [this]
          have hterm_c : |(m : ℝ) * ((c : ℝ) - (pos : ℝ) * (f : ℝ) / (m : ℝ))| ≤
              17 * (k : ℝ) * sqrt k * L := by
            rw [abs_mul, abs_of_pos hm_pos]
            have hmul := mul_le_mul hba.2.1 hc_approx (abs_nonneg _) (by positivity)
            have hnn : 0 ≤ (k : ℝ) * sqrt k * L := by positivity
            linarith only [hmul, hnn]
          have hterm_δ : 80 * (k : ℝ) * sqrt k * L ≤
              |(2 * (k : ℝ) + 2 - d) * δ_coord m pos| := by
            have h2k_pos : 0 < 2 * (k : ℝ) + 2 - d := by linarith only [hkR, hd'_le1]
            rw [abs_mul, abs_of_pos h2k_pos]
            have hmul := mul_le_mul (show 2 * (k : ℝ) ≤ 2 * (k : ℝ) + 2 - d by linarith only [hd'_le1]) h2.le
              (by positivity) h2k_pos.le
            linarith only [hmul]
          have hAB_abs : 60 * (k : ℝ) * sqrt k * L ≤ ((A' : ℝ) + B') * |(pos : ℝ) - μp| := by
            rw [← abs_of_pos hAB_pos, ← abs_mul, hclean]
            have htri1 : |(2 * (k : ℝ) + 2 - d) * δ_coord m pos| ≤
                |(2 * (k : ℝ) + 2 - d) * δ_coord m pos -
                  (m : ℝ) * ((c : ℝ) - (pos : ℝ) * (f : ℝ) / (m : ℝ)) +
                  ((A' : ℝ) - (m : ℝ) * d / 2)| +
                |(m : ℝ) * ((c : ℝ) - (pos : ℝ) * (f : ℝ) / (m : ℝ))| +
                |(A' : ℝ) - (m : ℝ) * d / 2| := by
              have ha := abs_sub ((2 * (k : ℝ) + 2 - d) * δ_coord m pos -
                (m : ℝ) * ((c : ℝ) - (pos : ℝ) * (f : ℝ) / (m : ℝ)) +
                ((A' : ℝ) - (m : ℝ) * d / 2)) ((A' : ℝ) - (m : ℝ) * d / 2)
              have hb' := abs_add_le ((2 * (k : ℝ) + 2 - d) * δ_coord m pos -
                (m : ℝ) * ((c : ℝ) - (pos : ℝ) * (f : ℝ) / (m : ℝ)))
                ((m : ℝ) * ((c : ℝ) - (pos : ℝ) * (f : ℝ) / (m : ℝ)))
              ring_nf at ha hb' ⊢
              linarith only [ha, hb']
            linarith only [htri1, hterm_δ, hterm_c, hrem_le, h3k_le]
          have hmul_hi := mR hAB_hi (abs_nonneg ((pos : ℝ) - μp))
          have hcomb : (k : ℝ) * (60 * sqrt k * L) ≤
              (k : ℝ) * ((27 / 10 : ℝ) * |(pos : ℝ) - μp|) := by
            have h1 : 60 * (k : ℝ) * sqrt k * L = (k : ℝ) * (60 * sqrt k * L) := by ring
            have h2' : (27 / 10 : ℝ) * (k : ℝ) * |(pos : ℝ) - μp| =
                (k : ℝ) * ((27 / 10 : ℝ) * |(pos : ℝ) - μp|) := by ring
            linarith only [hAB_abs, hmul_hi, h1, h2']
          have hcan := le_of_mul_le_mul_left hcomb hk_pos
          have hnn : 0 ≤ sqrt k * L := by positivity
          linarith only [hcan, hnn]
        have hexp : exp (-((pos : ℝ) - μp) ^ 2 / (16 * (k : ℝ))) ≤ exp (-9 * L ^ 2) := by
          apply exp_le_exp.mpr
          have hsq : (16 * sqrt k * L) ^ 2 ≤ ((pos : ℝ) - μp) ^ 2 := by
            rw [← sq_abs ((pos : ℝ) - μp)]; exact pow_le_pow_left₀ (by positivity) hdist_μp 2
          have h256 : (16 * sqrt k * L) ^ 2 = 256 * (k : ℝ) * L ^ 2 := by
            rw [mul_pow, mul_pow, sq_sqrt hk_pos.le]; ring
          rw [show (-9 : ℝ) * L ^ 2 = -(9 * L ^ 2) by ring, neg_div, neg_le_neg_iff,
            le_div_iff₀ (by positivity : (0 : ℝ) < 16 * k)]
          have hnn : 0 ≤ (k : ℝ) * L ^ 2 := by positivity
          linarith only [hsq, h256, hnn]
        have hdk_exp : |deltaK k c (f - c - d) pos (m - 1 - pos)| ≤ 500 * B0 * exp (-9 * L ^ 2) :=
          hdk.trans (mL hexp (by positivity))
        have hmul := mul_le_mul hC_base hdk_exp (abs_nonneg _) (by positivity)
        linarith only [hmul]
      · push Not at h2
        left
        refine ⟨h2, ?_⟩
        have hm_pos : (0 : ℝ) < m := by linarith [hba.1]
        have hS_cast : (S : ℝ) = 2 * (f : ℝ) + 1 - d := by
          dsimp [S]; rw [Nat.cast_sub (by omega : d ≤ 2 * f + 1)]; push_cast; ring
        have h2e_eq : 2 * ε_coord m f pos c =
            (((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)) +
            ((2 * (f : ℝ) / (m : ℝ) - 2 / 3) * δ_coord m pos) +
            ((pos : ℝ) * (1 - d) / (m : ℝ) - d) := by
          dsimp [ε_coord, δ_coord]; rw [hS_cast]; push_cast
          field_simp [hm_pos.ne']; ring
        have hη_eq : 2 * (f : ℝ) / (m : ℝ) = (f : ℝ) / ((m : ℝ) / 2) := by
          field_simp [hm_pos.ne']
        have hterm2 : |(2 * (f : ℝ) / (m : ℝ) - 2 / 3) * δ_coord m pos| ≤ 80 * L ^ 2 := by
          rw [hη_eq, abs_mul]
          have hmul := mul_le_mul hba.2.2.2.2.2 h2 (abs_nonneg _) (by positivity)
          have hsimp : (2 * L / sqrt k) * (40 * sqrt k * L) = 80 * L ^ 2 := by
            field_simp [hsq_pos.ne']; ring
          linarith
        have hterm3 : |(pos : ℝ) * (1 - d) / (m : ℝ) - d| ≤ 2 := by
          have h0 : 0 ≤ (pos : ℝ) * (1 - d) / (m : ℝ) := by
            apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hm_pos.le
          have hle1 : (pos : ℝ) * (1 - d) / (m : ℝ) ≤ 1 := by
            rw [div_le_iff₀ hm_pos]
            have : (pos : ℝ) ≤ m := by exact_mod_cast (le_of_lt hposm)
            nlinarith [Nat.cast_nonneg (α := ℝ) d]
          rw [abs_le]; constructor <;> linarith
        have h80L2 : 80 * L ^ 2 + 2 ≤ 5 * sqrt k * L := by
          have hL1 := validMF_pow_le hV 1 (by omega)
          rw [pow_one, div_le_div_iff₀ hsq_pos (by norm_num)] at hL1
          have h1sq : (1 : ℝ) ≤ sqrt k * L := by linarith only [hsqL_ge10]
          have hmul := mR hL1 (by linarith only [hL10] : 0 ≤ L)
          change L * 10 ^ 6 * L ≤ 1 * sqrt k * L at hmul
          linarith only [hmul, h1sq]
        have htri : |2 * ε_coord m f pos c| ≤
            |((2 * c + d : ℕ) : ℝ) - (pos : ℝ) * (S : ℝ) / (m : ℝ)| +
            |(2 * (f : ℝ) / (m : ℝ) - 2 / 3) * δ_coord m pos| +
            |(pos : ℝ) * (1 - d) / (m : ℝ) - d| := by
          rw [h2e_eq]
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
        linarith
  rcases hpos_box_or_win j a d1 hj (by omega) (by omega) hd1 hC_j_le with ⟨hδj, hεj⟩ | hwin_j
  · rcases hpos_box_or_win t b d2 (by omega) htm hb_le hd2 hC_t_le with ⟨hδt, _⟩ | hwin_t
    · -- Both (j, a) and (t, b) are in box, so the b-deviation |h| > 20 √D L must fail!
      let D := t - j - 1
      let M2 := m - t
      let S2 := 2 * (f - a - d1) + 1 - d2
      let r := 2 * (b - a - d1) + d2
      have hh_gt : 20 * sqrt D * L < |(b : ℝ) - a - ((t : ℝ) - j) / 3| := by
        by_contra hle; exact hout ⟨hδj, hδt, hεj, not_lt.mp hle⟩
      have hD_ge_D0 : ⌊L ^ 7⌋₊ ≤ D := by dsimp [D, L]; omega
      have hD_lb : L ^ 7 / 2 ≤ (D : ℝ) := by
        have h1 : L ^ 7 - 1 ≤ (⌊L ^ 7⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one (L ^ 7)]
        have h2 : (⌊L ^ 7⌋₊ : ℝ) ≤ D := by exact_mod_cast hD_ge_D0
        have hL7 : (2 : ℝ) ≤ L ^ 7 := by
          have : (10 : ℝ) ^ 7 ≤ L ^ 7 := pow_le_pow_left₀ (by norm_num) hL10 7
          linarith only [this]
        linarith only [h1, h2, hL7]
      have hD_pos : (0 : ℝ) < D := by
        have : (0 : ℝ) < L ^ 7 := by positivity
        linarith
      have hD_hi : (D : ℝ) ≤ 80 * sqrt k * L := by
        have h1 : (D : ℝ) = δ_coord m t - δ_coord m j - 1 := by
          dsimp [D, δ_coord]
          have : D + j + 1 = t := by omega
          have hR : ((D + j + 1 : ℕ) : ℝ) = t := by exact_mod_cast this
          push_cast at hR; linarith
        linarith [(abs_le.mp hδt).2, (abs_le.mp hδj).1]
      let μr : ℝ := (D : ℝ) * (S2 : ℝ) / ((D : ℝ) + M2)
      have hDM_eq : (D : ℝ) + M2 = (m : ℝ) - j - 1 := by
        dsimp [D, M2]
        have : D + M2 + j + 1 = m := by omega
        have hR : ((D + M2 + j + 1 : ℕ) : ℝ) = m := by exact_mod_cast this
        push_cast at hR; linarith
      have hDM_lo : (9 / 10 : ℝ) * k ≤ (D : ℝ) + M2 := by
        rw [hDM_eq]
        have hj_eq : (j : ℝ) = (m : ℝ) / 2 + δ_coord m j := by dsimp [δ_coord]; ring
        linarith [(abs_le.mp hδj).2, hba.1]
      have hDM_pos : 0 < (D : ℝ) + M2 := by linarith
      have hη2_diff : |(S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3| ≤ 30 * L / sqrt k := by
        have hS2_eq : (S2 : ℝ) = 2 * ((f : ℝ) - a - d1) + 1 - d2 := by
          dsimp [S2]
          have h1 : d2 ≤ 2 * (f - a - d1) + 1 := by omega
          rw [Nat.cast_sub h1, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_two]
          have h2 : f - a - d1 = f - (a + d1) := by omega
          rw [h2, Nat.cast_sub (by omega : a + d1 ≤ f), Nat.cast_add]; ring
        have hnum_eq : (S2 : ℝ) - (2 / 3) * ((D : ℝ) + M2) =
            (f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k) - 2 * ε_coord m f j a +
              (5 / 3 - 2 * (d1 : ℝ) - d2) := by
          rw [hS2_eq, hDM_eq]; dsimp [ε_coord]; ring
        have heq : (S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3 =
            ((S2 : ℝ) - (2 / 3) * ((D : ℝ) + M2)) / ((D : ℝ) + M2) := by
          field_simp [hDM_pos.ne']
        rw [heq, abs_div, abs_of_pos hDM_pos, hnum_eq]
        have hnum_le : |(f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k) - 2 * ε_coord m f j a +
            (5 / 3 - 2 * (d1 : ℝ) - d2)| ≤ 25 * sqrt k * L := by
          have hc : |5 / 3 - 2 * (d1 : ℝ) - d2| ≤ 4 := by
            rw [abs_le]; constructor <;>
              linarith [Nat.cast_nonneg (α := ℝ) d1, Nat.cast_nonneg (α := ℝ) d2,
                (show (d1 : ℝ) ≤ 1 by exact_mod_cast hd1_le1),
                (show (d2 : ℝ) ≤ 1 by exact_mod_cast hd2_le1)]
          have h1sq : (4 : ℝ) ≤ sqrt k * L := by linarith only [hsqL_ge10]
          have htri : |(f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k) - 2 * ε_coord m f j a +
              (5 / 3 - 2 * (d1 : ℝ) - d2)| ≤
              |(f : ℝ) - 2 * k / 3| + |(1 / 3 : ℝ) * ((m : ℝ) - 2 * k)| +
              |2 * ε_coord m f j a| + |5 / 3 - 2 * (d1 : ℝ) - d2| := by
            have t1 := abs_add_le ((f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k) - 2 * ε_coord m f j a)
              (5 / 3 - 2 * (d1 : ℝ) - d2)
            have t2 := abs_sub ((f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k)) (2 * ε_coord m f j a)
            have t3 := abs_sub ((f : ℝ) - 2 * k / 3) ((1 / 3 : ℝ) * ((m : ℝ) - 2 * k))
            linarith only [t1, t2, t3]
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3),
            abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
          have hnn : 0 ≤ sqrt k * L := by positivity
          linarith only [htri, hf_box, hm_box, hεj, hc, h1sq, hnn]
        rw [div_le_div_iff₀ hDM_pos hsq_pos]
        have hmul : (25 * sqrt k * L) * sqrt k = 25 * (k : ℝ) * L := by
          calc (25 * sqrt k * L) * sqrt k
              = 25 * (sqrt k * sqrt k) * L := by ring
            _ = 25 * (k : ℝ) * L := by rw [mul_self_sqrt hk_pos.le]
        have h1 := mR hnum_le hsq_pos.le
        have h2 := mL hDM_lo (show 0 ≤ 30 * L by positivity)
        have h27 : 30 * L * (9 / 10 * (k : ℝ)) = 27 * (k : ℝ) * L := by ring
        have hnn : 0 ≤ (k : ℝ) * L := by positivity
        linarith only [h1, h2, hmul, h27, hnn]
      have hdist_r : 30 * sqrt D * L ≤ |(r : ℝ) - μr| := by
        have hr_eq : (r : ℝ) = 2 * ((b : ℝ) - a - ((t : ℝ) - j) / 3) + (2 / 3) * D +
            (2 / 3 - 2 * (d1 : ℝ) + d2) := by
          dsimp [r, D]
          have hb_sub : b - a - d1 = b - (a + d1) := by omega
          have hD_cast : (D : ℝ) = (t : ℝ) - j - 1 := by
            have : D + j + 1 = t := by omega
            have hR : ((D + j + 1 : ℕ) : ℝ) = t := by exact_mod_cast this
            push_cast at hR; linarith
          rw [hb_sub, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_sub ha, Nat.cast_add, hD_cast]
          ring
        have hdiff_eq : (r : ℝ) - μr =
            2 * ((b : ℝ) - a - ((t : ℝ) - j) / 3) -
            (D : ℝ) * ((S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3) +
            (2 / 3 - 2 * (d1 : ℝ) + d2) := by
          rw [hr_eq]; dsimp [μr]; ring
        have hDη : |(D : ℝ) * ((S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3)| ≤ 2400 * L ^ 2 := by
          rw [abs_mul, abs_of_pos hD_pos]
          have hmul := mul_le_mul hD_hi hη2_diff (abs_nonneg _) (by positivity)
          have hsimp : (80 * sqrt k * L) * (30 * L / sqrt k) = 2400 * L ^ 2 := by
            field_simp [hsq_pos.ne']; ring
          linarith
        have hconst : |2 / 3 - 2 * (d1 : ℝ) + d2| ≤ 4 := by
          rw [abs_le]; constructor <;>
            linarith [Nat.cast_nonneg (α := ℝ) d1, Nat.cast_nonneg (α := ℝ) d2,
              (show (d1 : ℝ) ≤ 1 by exact_mod_cast hd1_le1),
              (show (d2 : ℝ) ≤ 1 by exact_mod_cast hd2_le1)]
        have h2404 : 2400 * L ^ 2 + 4 ≤ 10 * sqrt D * L := by
          have hsq : (250 * L) ^ 2 ≤ (D : ℝ) := by
            have hL5 : (10 ^ 5 : ℝ) * L ^ 2 ≤ L ^ 7 := by
              have h1' := pow_le_pow_left₀ (by norm_num) hL10 5
              have h2' := mR h1' (sq_nonneg L)
              rwa [← pow_add] at h2'
            have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
            have h250 : (250 * L) ^ 2 = 62500 * L ^ 2 := by ring
            have h105 : (10 ^ 5 : ℝ) / 2 = 50000 := by norm_num
            have hL5_big : (10 ^ 6 : ℝ) * L ^ 2 ≤ L ^ 7 := by
              have h1' : (10 ^ 2 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith only [hL]) 5
              have h2' := mR h1' hL2nn
              rw [← pow_add, show (5 + 2 : ℕ) = 7 by norm_num,
                show ((10 ^ 2 : ℝ) ^ 5) = 10 ^ 10 by norm_num] at h2'
              linarith only [h2', hL2nn]
            rw [h250]; linarith only [hD_lb, hL5_big, hL2nn]
          have h1' : 250 * L ≤ sqrt D := by
            rw [le_sqrt (by positivity) hD_pos.le]; exact hsq
          have h2' := mR h1' (by linarith only [hL10] : (0 : ℝ) ≤ L)
          have hL2 : (100 : ℝ) ≤ L ^ 2 := by
            have := pow_le_pow_left₀ (by norm_num) hL10 2; linarith only [this]
          linarith only [h2', hL2]
        have htri : |2 * ((b : ℝ) - a - ((t : ℝ) - j) / 3)| ≤
            |(r : ℝ) - μr| + |(D : ℝ) * ((S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3)| +
            |2 / 3 - 2 * (d1 : ℝ) + d2| := by
          have ha' := abs_sub ((r : ℝ) - μr) (2 / 3 - 2 * (d1 : ℝ) + d2)
          have hb' := abs_add_le ((r : ℝ) - μr - (2 / 3 - 2 * (d1 : ℝ) + d2))
            ((D : ℝ) * ((S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3))
          rw [show (r : ℝ) - μr - (2 / 3 - 2 * (d1 : ℝ) + d2) +
              (D : ℝ) * ((S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3) =
              2 * ((b : ℝ) - a - ((t : ℝ) - j) / 3) by linarith [hdiff_eq]] at hb'
          linarith
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
        linarith
      have hD1 : 1 ≤ D := by
        have hposN : 0 < D := by exact_mod_cast hD_pos
        omega
      have hr_le_S2 : r ≤ S2 := by omega
      have hut := hypergeom_universal_tail D M2 S2 r hD1 hr_le_S2
      have hS2r : S2 - r = 2 * (f - b - d2) + 1 := by omega
      rw [hS2r] at hut
      have hexp : exp (-((r : ℝ) - μr) ^ 2 / (8 * (D : ℝ))) ≤ exp (-9 * L ^ 2) := by
        apply exp_le_exp.mpr
        have hsq : (30 * sqrt D * L) ^ 2 ≤ ((r : ℝ) - μr) ^ 2 := by
          rw [← sq_abs ((r : ℝ) - μr)]; exact pow_le_pow_left₀ (by positivity) hdist_r 2
        have h900 : (30 * sqrt D * L) ^ 2 = 900 * (D : ℝ) * L ^ 2 := by
          rw [mul_pow, mul_pow, sq_sqrt hD_pos.le]; ring
        rw [show (-9 : ℝ) * L ^ 2 = -(9 * L ^ 2) by ring, neg_div, neg_le_neg_iff,
          le_div_iff₀ (by positivity : (0 : ℝ) < 8 * D)]
        have hnn : 0 ≤ (D : ℝ) * L ^ 2 := by positivity
        linarith only [hsq, h900, hnn]
      have hch_N0 : (j.choose (2 * a + d1) : ℝ) * (((D + M2).choose S2 : ℕ) : ℝ) ≤ N0 := by
        have hDM : D + M2 = m - j - 1 := by omega
        have hpas : (m - j - 1).choose S2 ≤ (m - j).choose (2 * (f - a - d1) + 1) := by
          have hm1 : m - j - 1 + 1 = m - j := by omega
          simp only [mem_insert, mem_singleton] at hd2
          rcases hd2 with rfl | rfl
          · have : S2 = 2 * (f - a - d1) + 1 := by omega
            rw [this, ← hm1]; exact choose_le_choose_succ_left _ _
          · have : S2 + 1 = 2 * (f - a - d1) + 1 := by omega
            rw [← this, ← hm1]; exact choose_le_choose_succ_both _ _
        have hpair : j.choose (2 * a + d1) * (m - j).choose (2 * (f - a - d1) + 1) ≤
            m.choose (2 * f + 1 - d1) := by
          have h1 : j + (m - j) = m := Nat.add_sub_of_le (by omega : j ≤ m)
          have h2 : (2 * f + 1 - d1) - (2 * a + d1) = 2 * (f - a - d1) + 1 := by omega
          have hcm := choose_mul_choose_le j (m - j) (2 * f + 1 - d1) (2 * a + d1) (by omega)
          rwa [h1, h2] at hcm
        have hpas2 : m.choose (2 * f + 1 - d1) ≤ (m + 1).choose (2 * f + 1) := by
          simp only [mem_insert, mem_singleton] at hd1
          rcases hd1 with rfl | rfl
          · exact choose_le_choose_succ_left _ _
          · have : 2 * f + 1 - 1 + 1 = 2 * f + 1 := by omega
            rw [← this]; exact choose_le_choose_succ_both _ _
        have hnat : j.choose (2 * a + d1) * (D + M2).choose S2 ≤ (m + 1).choose (2 * f + 1) := by
          rw [hDM]; exact (Nat.mul_le_mul_left _ hpas).trans (hpair.trans hpas2)
        have hR : ((j.choose (2 * a + d1) * (D + M2).choose S2 : ℕ) : ℝ) ≤ N0 := by
          dsimp [N0]; exact_mod_cast hnat
        push_cast at hR; exact hR
      have hC_exp : Cval ≤ 2 * N0 * exp (-9 * L ^ 2) := by
        have h1 : Cval = (j.choose (2 * a + d1) : ℝ) *
            ((D.choose r : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ)) := by
          dsimp [Cval, D, M2, r]; push_cast; ring
        rw [h1]
        calc (j.choose (2 * a + d1) : ℝ) * ((D.choose r : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ))
            ≤ (j.choose (2 * a + d1) : ℝ) * (2 * (((D + M2).choose S2 : ℕ) : ℝ) *
                exp (-((r : ℝ) - μr) ^ 2 / (8 * (D : ℝ)))) :=
              mL hut (Nat.cast_nonneg _)
          _ = 2 * ((j.choose (2 * a + d1) : ℝ) * (((D + M2).choose S2 : ℕ) : ℝ)) *
                exp (-((r : ℝ) - μr) ^ 2 / (8 * (D : ℝ))) := by ring
          _ ≤ 2 * N0 * exp (-9 * L ^ 2) :=
              mul_le_mul (mL hch_N0 (by norm_num)) hexp
                (exp_pos _).le (by positivity)
      have hprod : Cval * |deltaK k a (f - a - d1) j (m - 1 - j)| *
          |deltaK k b (f - b - d2) t (m - 1 - t)| ≤
          (10 ^ 6 : ℝ) * N0 * B0 ^ 2 * exp (-9 * L ^ 2) := by
        have h1 := mul_le_mul hC_exp hdj_base (abs_nonneg _) (by positivity)
        have h2 := mul_le_mul h1 hdt_base (abs_nonneg _) (by positivity)
        have hnn : 0 ≤ N0 * B0 ^ 2 * exp (-9 * L ^ 2) := by positivity
        linarith
      exact hprod.trans hwin_exp
    · -- hwin_t: Cval * |deltaK_t| ≤ 1000 * N0 * B0 * exp(-9 L^2)
      have h1 : Cval * |deltaK k a (f - a - d1) j (m - 1 - j)| *
          |deltaK k b (f - b - d2) t (m - 1 - t)| =
          (Cval * |deltaK k b (f - b - d2) t (m - 1 - t)|) *
            |deltaK k a (f - a - d1) j (m - 1 - j)| := by ring
      rw [h1]
      have hmul := mul_le_mul hwin_t hdj_base (abs_nonneg _) (by positivity)
      have hnn : 0 ≤ N0 * B0 ^ 2 * exp (-9 * L ^ 2) := by positivity
      exact (by linarith : _ ≤ (10 ^ 6 : ℝ) * N0 * B0 ^ 2 * exp (-9 * L ^ 2)).trans hwin_exp
  · -- hwin_j: Cval * |deltaK_j| ≤ 1000 * N0 * B0 * exp(-9 L^2)
    have hmul := mul_le_mul hwin_j hdt_base (abs_nonneg _) (by positivity)
    have hnn : 0 ≤ N0 * B0 ^ 2 * exp (-9 * L ^ 2) := by positivity
    exact (by linarith : _ ≤ (10 ^ 6 : ℝ) * N0 * B0 ^ 2 * exp (-9 * L ^ 2)).trans hwin_exp

-- ============================================================================
-- Section 6B: Inner b-sum approximation, InBox double cancellation, Regime 2
-- ============================================================================

private lemma logG_hypergeom {D M2 η : ℝ} (hD : 0 < D) (hM2 : 0 < M2) (hη0 : 0 < η) (hη1 : η < 1) :
    logG D (D * η) + logG M2 (M2 * η) - logG (D + M2) ((D + M2) * η) =
      (1 / 2) * log ((D + M2) / (2 * Real.pi * η * (1 - η) * D * M2)) := by
  have h1m : 0 < 1 - η := sub_pos.mpr hη1
  have hDM : 0 < D + M2 := add_pos hD hM2
  have hpi : 0 < Real.pi := pi_pos
  have hlogG_sc : ∀ {N : ℝ}, 0 < N →
      logG N (N * η) =
        N * (-η * log η - (1 - η) * log (1 - η)) -
        (1 / 2) * log (2 * Real.pi * η * (1 - η) * N) := fun {N} hN => by
    unfold logG
    have hsub : N - N * η = N * (1 - η) := by ring
    have harg : 2 * Real.pi * (N * η) * (N * (1 - η)) / N = 2 * Real.pi * η * (1 - η) * N := by
      field_simp [hN.ne']
    rw [hsub, harg, log_mul hN.ne' hη0.ne', log_mul hN.ne' h1m.ne']
    ring
  rw [hlogG_sc hD, hlogG_sc hM2, hlogG_sc hDM]
  have hC : 0 < 2 * Real.pi * η * (1 - η) := by positivity
  rw [log_mul hC.ne' hD.ne', log_mul hC.ne' hM2.ne', log_mul hC.ne' hDM.ne',
    log_div hDM.ne' (by positivity),
    log_mul (by positivity : (2 * Real.pi * η * (1 - η) * D) ≠ 0) hM2.ne',
    log_mul hC.ne' hD.ne']
  ring

set_option maxHeartbeats 800000 in
private lemma phiG_taylor_h_approx {k m f : ℕ} (hV : ValidMF k m f) {y h : ℝ}
    (hy : |y| ≤ 60 * sqrt k * log k)
    (hh : h ^ 2 ≤ 32000 * sqrt k * log k ^ 3) :
    |phiG (αk_val k) (y - h) -
      (phiG (αk_val k) y + ((2 * αk_val k * y ^ 2 - 1) * exp (-αk_val k * y ^ 2)) * h)| ≤
      2e7 * log k ^ 3 * exp (-αk_val k * y ^ 2 / 2) ∧
    exp (-αk_val k * (y - h) ^ 2) ≤ 2 * exp (-αk_val k * y ^ 2) := by
  let L : ℝ := log k
  let α : ℝ := αk_val k
  let z : ℝ := 2 * α * y * h - α * h ^ 2
  have ⟨hk, hL, hL15, _, _, _⟩ := hV
  change 10 ^ 20 ≤ L at hL
  change L ^ 15 / sqrt k ≤ 1 / 10 ^ 6 at hL15
  change |y| ≤ 60 * sqrt k * L at hy
  change h ^ 2 ≤ 32000 * sqrt k * L ^ 3 at hh
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hL10 : (10 : ℝ) ≤ L := by linarith only [hL]
  have hα_pos : 0 < α := by dsimp [α, αk_val]; positivity
  have hL5_tiny : L ^ 5 / sqrt k ≤ 1 / 10 ^ 100 := by
    have hL10_pow : (10 ^ 100 : ℝ) * L ^ 5 ≤ L ^ 15 := by
      have h1 : (10 ^ 10 : ℝ) ^ 10 ≤ L ^ 10 := pow_le_pow_left₀ (by norm_num) (by linarith only [hL]) 10
      have h2 := mR h1 (pow_nonneg (by linarith only [hL10]) 5)
      rw [← pow_add, show (10 + 5 : ℕ) = 15 by norm_num,
        show ((10 ^ 10 : ℝ) ^ 10) = 10 ^ 100 by norm_num] at h2
      exact h2
    have hdiv : (10 ^ 100 : ℝ) * (L ^ 5 / sqrt k) ≤ L ^ 15 / sqrt k := by
      rw [mul_div_assoc']; exact dR hL10_pow hsq_pos.le
    linarith only [hdiv, hL15]
  have hL3_tiny : L ^ 3 / sqrt k ≤ 1 / 10 ^ 100 := by
    have h1 : L ^ 3 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith only [hL10]) (by omega)
    exact (dR h1 hsq_pos.le).trans hL5_tiny
  have hαh2 : α * h ^ 2 ≤ 72000 * L ^ 3 / sqrt k := by
    have h1 : α * (32000 * sqrt k * L ^ 3) = 72000 * L ^ 3 / sqrt k := by
      dsimp [α, αk_val]
      calc 9 / (4 * (k : ℝ)) * (32000 * sqrt k * L ^ 3)
          = 9 / (4 * (sqrt k * sqrt k)) * (32000 * sqrt k * L ^ 3) := by
            rw [mul_self_sqrt hk_pos.le]
        _ = 72000 * L ^ 3 / sqrt k := by field_simp [hsq_pos.ne']; ring
    have h2 := mL hh hα_pos.le
    linarith only [h1, h2]
  have hαh2_le : α * h ^ 2 ≤ 1 / 4 := by
    have hnn : 0 ≤ L ^ 3 / sqrt k := by positivity
    have h1 : 72000 * (L ^ 3 / sqrt k) = 72000 * L ^ 3 / sqrt k := by ring
    linarith only [hαh2, hL3_tiny, h1, hnn]
  have h2αyh_le : |2 * α * y * h| ≤ 1 / 4 := by
    have hsq_le : (2 * α * y * h) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      have hy2 : y ^ 2 ≤ 3600 * (k : ℝ) * L ^ 2 := by
        have h1 := pow_le_pow_left₀ (abs_nonneg y) hy 2
        rw [sq_abs, mul_pow, mul_pow, sq_sqrt hk_pos.le] at h1; linarith only [h1]
      have hyh2 : y ^ 2 * h ^ 2 ≤ (3600 * (k : ℝ) * L ^ 2) * (32000 * sqrt k * L ^ 3) :=
        mul_le_mul hy2 hh (sq_nonneg h) (by positivity)
      have hαsq : (2 * α) ^ 2 = 81 / (4 * (k : ℝ) ^ 2) := by dsimp [α, αk_val]; ring
      have heq : (2 * α * y * h) ^ 2 = (2 * α) ^ 2 * (y ^ 2 * h ^ 2) := by ring
      rw [heq, hαsq]
      have hmul := mL hyh2 (show 0 ≤ 81 / (4 * (k : ℝ) ^ 2) by positivity)
      have hsimp : (81 / (4 * (k : ℝ) ^ 2)) * ((3600 * (k : ℝ) * L ^ 2) * (32000 * sqrt k * L ^ 3)) =
          2332800000 * (L ^ 5 / sqrt k) := by
        rw [show (k : ℝ) ^ 2 = (k : ℝ) * (sqrt k * sqrt k) by
          rw [mul_self_sqrt hk_pos.le]; ring]
        field_simp [hk_pos.ne', hsq_pos.ne']; ring
      linarith only [hmul, hsimp, hL5_tiny]
    have habs_sq : |2 * α * y * h| ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by rwa [sq_abs]
    nlinarith only [habs_sq, abs_nonneg (2 * α * y * h)]
  have hz_le : |z| ≤ 1 / 2 := by
    dsimp [z]
    have htri := abs_sub (2 * α * y * h) (α * h ^ 2)
    rw [abs_of_nonneg (show 0 ≤ α * h ^ 2 by positivity)] at htri
    linarith only [htri, h2αyh_le, hαh2_le]
  have hexp_split : exp (-α * (y - h) ^ 2) = exp (-α * y ^ 2) * exp z := by
    rw [← exp_add]; congr 1; dsimp [z]; ring
  have hpart2 : exp (-α * (y - h) ^ 2) ≤ 2 * exp (-α * y ^ 2) := by
    rw [hexp_split]
    have hz2 : exp z ≤ 2 :=
      (exp_le_exp.mpr (abs_le.mp hz_le).2).trans exp_half_lt_two.le
    have := mL hz2 (exp_pos (-α * y ^ 2)).le
    linarith only [this]
  have hrem_eq : phiG α (y - h) - (phiG α y + ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) * h) =
      exp (-α * y ^ 2) * (y * (-α * h ^ 2) + y * (exp z - 1 - z) - h * (exp z - 1)) := by
    dsimp [phiG]; rw [hexp_split]; dsimp [z]; ring
  let u : ℝ := sqrt (α / 2) * |y|
  have hu_nn : 0 ≤ u := by dsimp [u]; positivity
  have hu_sq : u ^ 2 = (α / 2) * y ^ 2 := by
    dsimp [u]; rw [mul_pow, sq_sqrt (by positivity), sq_abs]
  have hexp_y_split : exp (-α * y ^ 2) = exp (-u ^ 2) * exp (-α * y ^ 2 / 2) := by
    rw [← exp_add]; congr 1; rw [hu_sq]; ring
  have hu1_exp : u * exp (-u ^ 2) ≤ 1 := by
    have h1 : u ≤ 1 + u ^ 2 := by nlinarith only [sq_nonneg (u - 1)]
    have h2 : 1 + u ^ 2 ≤ exp (u ^ 2) := by linarith only [add_one_le_exp (u ^ 2)]
    have h3 := mR (h1.trans h2) (exp_pos (-u ^ 2)).le
    rwa [← exp_add, add_neg_cancel, exp_zero] at h3
  have hu3_exp : u ^ 3 * exp (-u ^ 2) ≤ 4 := by
    have h1 : u * exp (-(u ^ 2 / 2)) ≤ 2 := by
      have ha : u ≤ 2 * (1 + u ^ 2 / 2) := by nlinarith only [sq_nonneg (u - 1)]
      have hb : 1 + u ^ 2 / 2 ≤ exp (u ^ 2 / 2) := by linarith only [add_one_le_exp (u ^ 2 / 2)]
      have hle : u ≤ 2 * exp (u ^ 2 / 2) := by linarith only [ha, hb]
      calc u * exp (-(u ^ 2 / 2))
          ≤ (2 * exp (u ^ 2 / 2)) * exp (-(u ^ 2 / 2)) :=
            mR hle (exp_pos (-(u ^ 2 / 2))).le
        _ = 2 * (exp (u ^ 2 / 2) * exp (-(u ^ 2 / 2))) := by ring
        _ = 2 := by rw [← exp_add, add_neg_cancel, exp_zero, mul_one]
    have h2 : (u ^ 2 / 2) * exp (-(u ^ 2 / 2)) ≤ 1 := by
      have ha : u ^ 2 / 2 ≤ exp (u ^ 2 / 2) := by linarith only [add_one_le_exp (u ^ 2 / 2)]
      have hb := mR ha (exp_pos (-(u ^ 2 / 2))).le
      rwa [← exp_add, add_neg_cancel, exp_zero] at hb
    have hprod := mul_le_mul h1 h2 (by positivity) (by norm_num)
    have hcomb : u * exp (-(u ^ 2 / 2)) * ((u ^ 2 / 2) * exp (-(u ^ 2 / 2))) =
        (u ^ 3 * exp (-u ^ 2)) / 2 := by
      have he : exp (-(u ^ 2 / 2)) * exp (-(u ^ 2 / 2)) = exp (-u ^ 2) := by
        rw [← exp_add]; congr 1; ring
      calc u * exp (-(u ^ 2 / 2)) * ((u ^ 2 / 2) * exp (-(u ^ 2 / 2)))
          = (u ^ 3 * (exp (-(u ^ 2 / 2)) * exp (-(u ^ 2 / 2)))) / 2 := by ring
        _ = (u ^ 3 * exp (-u ^ 2)) / 2 := by rw [he]
    linarith only [hprod, hcomb]
  have hinv_sq : 1 / sqrt (α / 2) ≤ sqrt k := by
    have hsq_pos' : 0 < sqrt (α / 2) := sqrt_pos.mpr (by positivity)
    rw [div_le_iff₀ hsq_pos']
    have h1 : (1 : ℝ) ≤ (k : ℝ) * (α / 2) := by dsimp [α, αk_val]; field_simp [hk_pos.ne']; norm_num
    rw [← sqrt_mul hk_pos.le, le_sqrt (by norm_num) (by positivity)]
    linarith only [h1]
  have hy_u : |y| ≤ sqrt k * u := by
    have heq : |y| = (1 / sqrt (α / 2)) * u := by
      dsimp [u]; field_simp [(sqrt_pos.mpr (by positivity : 0 < α / 2)).ne']
    rw [heq]; exact mR hinv_sq hu_nn
  have hy_exp : |y| * exp (-u ^ 2) ≤ sqrt k := by
    calc |y| * exp (-u ^ 2)
        ≤ (sqrt k * u) * exp (-u ^ 2) :=
          mR hy_u (exp_pos _).le
      _ = sqrt k * (u * exp (-u ^ 2)) := by ring
      _ ≤ sqrt k * 1 := mL hu1_exp hsq_pos.le
      _ = sqrt k := mul_one _
  have hαy3_exp : α * |y| ^ 3 * exp (-u ^ 2) ≤ 8 * sqrt k := by
    have hrew : α * |y| ^ 3 = 2 * u ^ 2 * |y| := by rw [hu_sq, ← sq_abs y]; ring
    calc α * |y| ^ 3 * exp (-u ^ 2)
        = 2 * u ^ 2 * |y| * exp (-u ^ 2) := by rw [hrew]
      _ ≤ 2 * u ^ 2 * (sqrt k * u) * exp (-u ^ 2) := by
          apply mR _ (exp_pos _).le
          exact mL hy_u (by positivity)
      _ = 2 * sqrt k * (u ^ 3 * exp (-u ^ 2)) := by ring
      _ ≤ 2 * sqrt k * 4 := mL hu3_exp (by positivity)
      _ = 8 * sqrt k := by ring
  have hh_abs : |h| ≤ 20 * sqrt k := by
    have hsq : |h| ^ 2 ≤ (20 * sqrt k) ^ 2 := by
      rw [sq_abs, mul_pow, sq_sqrt hk_pos.le]
      have h1 : 32000 * sqrt k * L ^ 3 = 32000 * (k : ℝ) * (L ^ 3 / sqrt k) := by
        calc 32000 * sqrt k * L ^ 3
            = 32000 * (sqrt k * sqrt k) * (L ^ 3 / sqrt k) := by
              field_simp [hsq_pos.ne']
          _ = 32000 * (k : ℝ) * (L ^ 3 / sqrt k) := by rw [mul_self_sqrt hk_pos.le]
      have h2 := mL hL3_tiny (show 0 ≤ 32000 * (k : ℝ) by positivity)
      linarith only [hh, h1, h2, hk_pos]
    nlinarith only [hsq, abs_nonneg h, hsq_pos]
  have hT1 : |y * (-α * h ^ 2)| * exp (-u ^ 2) ≤ 72000 * L ^ 3 := by
    rw [show -α * h ^ 2 = -(α * h ^ 2) by ring, abs_mul, abs_neg, abs_of_nonneg (show 0 ≤ α * h ^ 2 by positivity)]
    have hmul := mul_le_mul hy_exp hαh2 (by positivity) hsq_pos.le
    have hsimp : sqrt k * (72000 * L ^ 3 / sqrt k) = 72000 * L ^ 3 := by
      field_simp [hsq_pos.ne']
    have hass : |y| * (α * h ^ 2) * exp (-u ^ 2) = (|y| * exp (-u ^ 2)) * (α * h ^ 2) := by ring
    linarith only [hmul, hsimp, hass]
  have hT2 : |y * (exp z - 1 - z)| * exp (-u ^ 2) ≤ 1e7 * L ^ 3 := by
    rw [abs_mul]
    have hez := abs_exp_sub_one_sub_le hz_le
    have hzsq : z ^ 2 ≤ 8 * α ^ 2 * y ^ 2 * h ^ 2 + 2 * α ^ 2 * h ^ 4 := by
      dsimp [z]
      have h1 : 0 ≤ (2 * α * y * h + α * h ^ 2) ^ 2 := sq_nonneg _
      nlinarith only [h1]
    have hpA : 16 * (α * |y| ^ 3 * exp (-u ^ 2)) * (α * h ^ 2) ≤ 9.3e6 * L ^ 3 := by
      have hmul := mul_le_mul hαy3_exp hαh2 (by positivity) (by positivity)
      have hsimp : (8 * sqrt k) * (72000 * L ^ 3 / sqrt k) = 576000 * L ^ 3 := by
        field_simp [hsq_pos.ne']; ring
      have hnn : 0 ≤ L ^ 3 := pow_nonneg (by linarith only [hL10]) 3
      linarith only [hmul, hsimp, hnn]
    have hpB : 4 * (|y| * exp (-u ^ 2)) * (α * h ^ 2) * (α * h ^ 2) ≤ 72000 * L ^ 3 := by
      have h1 : 4 * (α * h ^ 2) ≤ 1 := by linarith only [hαh2_le]
      have h2 := mL h1 (show 0 ≤ (|y| * exp (-u ^ 2)) * (α * h ^ 2) by positivity)
      have h3 : (|y| * exp (-u ^ 2)) * (α * h ^ 2) ≤ 72000 * L ^ 3 := by
        have hmul := mul_le_mul hy_exp hαh2 (by positivity) hsq_pos.le
        have hsimp : sqrt k * (72000 * L ^ 3 / sqrt k) = 72000 * L ^ 3 := by
          field_simp [hsq_pos.ne']
        linarith only [hmul, hsimp]
      linarith only [h2, h3]
    calc |y| * |exp z - 1 - z| * exp (-u ^ 2)
        ≤ |y| * (2 * z ^ 2) * exp (-u ^ 2) :=
          mR (mL hez (abs_nonneg y)) (exp_pos _).le
      _ ≤ |y| * (2 * (8 * α ^ 2 * y ^ 2 * h ^ 2 + 2 * α ^ 2 * h ^ 4)) * exp (-u ^ 2) :=
          mR (mL
            (mL hzsq (by norm_num)) (abs_nonneg y)) (exp_pos _).le
      _ = 16 * (α * |y| ^ 3 * exp (-u ^ 2)) * (α * h ^ 2) +
          4 * (|y| * exp (-u ^ 2)) * (α * h ^ 2) * (α * h ^ 2) := by
            rw [← sq_abs y]; ring
      _ ≤ 9.3e6 * L ^ 3 + 72000 * L ^ 3 := add_le_add hpA hpB
      _ ≤ 1e7 * L ^ 3 := by
            have hnn : 0 ≤ L ^ 3 := pow_nonneg (by linarith only [hL10]) 3
            linarith only [hnn]
  have hT3 : |h * (exp z - 1)| * exp (-u ^ 2) ≤ 4e6 * L ^ 3 := by
    rw [abs_mul]
    have hez := abs_exp_sub_one_le hz_le
    have hz_abs : |z| ≤ 2 * α * |y| * |h| + α * h ^ 2 := by
      dsimp [z]
      have htri := abs_sub (2 * α * y * h) (α * h ^ 2)
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos hα_pos, abs_of_nonneg (show 0 ≤ α * h ^ 2 by positivity)] at htri
      exact htri
    have hpA : 4 * (|y| * exp (-u ^ 2)) * (α * h ^ 2) ≤ 288000 * L ^ 3 := by
      have hmul := mul_le_mul hy_exp hαh2 (by positivity) hsq_pos.le
      have hsimp : sqrt k * (72000 * L ^ 3 / sqrt k) = 72000 * L ^ 3 := by
        field_simp [hsq_pos.ne']
      linarith only [hmul, hsimp]
    have hpB : 2 * |h| * (α * h ^ 2) * exp (-u ^ 2) ≤ 3e6 * L ^ 3 := by
      have hexp1 : exp (-u ^ 2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith only [sq_nonneg u])
      have hmul := mul_le_mul hh_abs hαh2 (by positivity) (by positivity)
      have hsimp : (20 * sqrt k) * (72000 * L ^ 3 / sqrt k) = 1440000 * L ^ 3 := by
        field_simp [hsq_pos.ne']; ring
      have h1 : 2 * (|h| * (α * h ^ 2)) ≤ 2880000 * L ^ 3 := by linarith only [hmul, hsimp]
      have h2 := mL hexp1 (show 0 ≤ 2 * |h| * (α * h ^ 2) by positivity)
      have hnn : 0 ≤ L ^ 3 := pow_nonneg (by linarith only [hL10]) 3
      linarith only [h1, h2, hnn]
    calc |h| * |exp z - 1| * exp (-u ^ 2)
        ≤ |h| * (2 * |z|) * exp (-u ^ 2) :=
          mR (mL hez (abs_nonneg h)) (exp_pos _).le
      _ ≤ |h| * (2 * (2 * α * |y| * |h| + α * h ^ 2)) * exp (-u ^ 2) :=
          mR (mL
            (mL hz_abs (by norm_num)) (abs_nonneg h)) (exp_pos _).le
      _ = 4 * (|y| * exp (-u ^ 2)) * (α * h ^ 2) +
          2 * |h| * (α * h ^ 2) * exp (-u ^ 2) := by rw [← sq_abs h]; ring
      _ ≤ 288000 * L ^ 3 + 3e6 * L ^ 3 := add_le_add hpA hpB
      _ ≤ 4e6 * L ^ 3 := by
            have hnn : 0 ≤ L ^ 3 := pow_nonneg (by linarith only [hL10]) 3
            linarith only [hnn]
  have hpart1 : |phiG α (y - h) -
      (phiG α y + ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) * h)| ≤
      2e7 * L ^ 3 * exp (-α * y ^ 2 / 2) := by
    rw [hrem_eq, abs_mul, abs_of_pos (exp_pos _), hexp_y_split]
    have htri := abs_add_sub_le (y * (-α * h ^ 2)) (y * (exp z - 1 - z)) (h * (exp z - 1))
    have hmul1 := mR htri (exp_pos (-u ^ 2)).le
    have hsum : (|y * (-α * h ^ 2)| + |y * (exp z - 1 - z)| + |h * (exp z - 1)|) *
        exp (-u ^ 2) ≤ 2e7 * L ^ 3 := by
      have hnn : 0 ≤ L ^ 3 := pow_nonneg (by linarith only [hL10]) 3
      linarith only [hT1, hT2, hT3, hnn]
    have htot := mR (hmul1.trans hsum) (exp_pos (-α * y ^ 2 / 2)).le
    calc exp (-u ^ 2) * exp (-α * y ^ 2 / 2) *
          |y * (-α * h ^ 2) + y * (exp z - 1 - z) - h * (exp z - 1)|
        = |y * (-α * h ^ 2) + y * (exp z - 1 - z) - h * (exp z - 1)| *
          exp (-u ^ 2) * exp (-α * y ^ 2 / 2) := by ring
      _ ≤ 2e7 * L ^ 3 * exp (-α * y ^ 2 / 2) := htot
  exact ⟨hpart1, hpart2⟩

private lemma box_eta2_bounds {k m f d1 d2 j t a : ℕ} (hV : ValidMF k m f)
    (hd1 : d1 ∈ ({0, 1} : Finset ℕ)) (hd2 : d2 ∈ ({0, 1} : Finset ℕ))
    (hjt : j + ⌊log k ^ 7⌋₊ < t) (htm : t < m)
    (hδj : |δ_coord m j| ≤ 40 * sqrt k * log k)
    (hδt : |δ_coord m t| ≤ 40 * sqrt k * log k)
    (hεj : |ε_coord m f j a| ≤ 10 * sqrt k * log k) :
    log k ^ 7 / 2 ≤ ((t - j - 1 : ℕ) : ℝ) ∧
    (100 : ℝ) ≤ ((t - j - 1 : ℕ) : ℝ) ∧
    ((t - j - 1 : ℕ) : ℝ) ≤ 80 * sqrt k * log k ∧
    (9 / 10 : ℝ) * k ≤ ((m - t : ℕ) : ℝ) ∧
    ((t - j - 1 : ℕ) : ℝ) ≤ ((m - t : ℕ) : ℝ) ∧
    ((t - j - 1 : ℕ) : ℝ) + ((m - t : ℕ) : ℝ) = (m : ℝ) - j - 1 ∧
    (9 / 10 : ℝ) * k ≤ ((t - j - 1 : ℕ) : ℝ) + ((m - t : ℕ) : ℝ) ∧
    (a : ℝ) = (f : ℝ) / 2 + δ_coord m j / 3 + ε_coord m f j a ∧
    a + d1 ≤ f ∧
    |((2 * (f - a - d1) + 1 - d2 : ℕ) : ℝ) / (((t - j - 1 : ℕ) : ℝ) + ((m - t : ℕ) : ℝ)) - 2 / 3| ≤
      30 * log k / sqrt k ∧
    (6 / 10 : ℝ) ≤ ((2 * (f - a - d1) + 1 - d2 : ℕ) : ℝ) / (((t - j - 1 : ℕ) : ℝ) + ((m - t : ℕ) : ℝ)) ∧
    ((2 * (f - a - d1) + 1 - d2 : ℕ) : ℝ) / (((t - j - 1 : ℕ) : ℝ) + ((m - t : ℕ) : ℝ)) ≤ (7 / 10 : ℝ) := by
  let L : ℝ := log k
  let D : ℕ := t - j - 1
  let M2 : ℕ := m - t
  let S2 : ℕ := 2 * (f - a - d1) + 1 - d2
  have hba := validMF_eta_bounds hV
  have hsqL := validMF_sqL_le hV
  have ⟨hk, hL, _, _, hm_box, hf_box⟩ := hV
  change 10 ^ 20 ≤ L at hL
  change |(m : ℝ) - 2 * k| ≤ sqrt k * L at hm_box
  change |(f : ℝ) - 2 * (k : ℝ) / 3| ≤ sqrt k * L at hf_box
  change sqrt k * L ≤ (k : ℝ) / 10 ^ 6 at hsqL
  change |δ_coord m j| ≤ 40 * sqrt k * L at hδj
  change |δ_coord m t| ≤ 40 * sqrt k * L at hδt
  change |ε_coord m f j a| ≤ 10 * sqrt k * L at hεj
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hL10 : (10 : ℝ) ≤ L := by linarith only [hL]
  have hd1_le1 : d1 ≤ 1 := by simp only [mem_insert, mem_singleton] at hd1; rcases hd1 with rfl | rfl <;> omega
  have hd2_le1 : d2 ≤ 1 := by simp only [mem_insert, mem_singleton] at hd2; rcases hd2 with rfl | rfl <;> omega
  have hd1R : (d1 : ℝ) ≤ 1 := by exact_mod_cast hd1_le1
  have hd2R : (d2 : ℝ) ≤ 1 := by exact_mod_cast hd2_le1
  have hD_lb : L ^ 7 / 2 ≤ (D : ℝ) := by
    have hD_ge : ⌊L ^ 7⌋₊ ≤ D := by dsimp [D, L]; omega
    have h1 : L ^ 7 - 1 ≤ (⌊L ^ 7⌋₊ : ℝ) := by linarith only [Nat.lt_floor_add_one (L ^ 7)]
    have h2 : (⌊L ^ 7⌋₊ : ℝ) ≤ D := by exact_mod_cast hD_ge
    have hL7 : (2 : ℝ) ≤ L ^ 7 := by have := pow_le_pow_left₀ (by norm_num) hL10 7; linarith only [this]
    linarith only [h1, h2, hL7]
  have hD_ge100 : (100 : ℝ) ≤ D := by
    have hL7 : (10 ^ 7 : ℝ) ≤ L ^ 7 := pow_le_pow_left₀ (by norm_num) hL10 7
    linarith only [hD_lb, hL7]
  have hD_hi : (D : ℝ) ≤ 80 * sqrt k * L := by
    have h1 : (D : ℝ) = δ_coord m t - δ_coord m j - 1 := by
      dsimp [D, δ_coord]; have : D + j + 1 = t := by omega
      have hR : ((D + j + 1 : ℕ) : ℝ) = t := by exact_mod_cast this
      push_cast at hR; linarith only [hR]
    linarith only [h1, (abs_le.mp hδt).2, (abs_le.mp hδj).1]
  have hM2_lo : (9 / 10 : ℝ) * k ≤ M2 := by
    have h1 : (M2 : ℝ) = (m : ℝ) / 2 - δ_coord m t := by
      dsimp [M2, δ_coord]; rw [Nat.cast_sub (le_of_lt htm)]; ring
    linarith only [h1, hba.1, (abs_le.mp hδt).2, hsqL, hk_pos]
  have hD_le_M2 : (D : ℝ) ≤ M2 := by linarith only [hD_hi, hM2_lo, hsqL, hk_pos]
  have hDM_eq : (D : ℝ) + M2 = (m : ℝ) - j - 1 := by
    have : D + M2 + j + 1 = m := by dsimp [D, M2]; omega
    have hR : ((D + M2 + j + 1 : ℕ) : ℝ) = m := by exact_mod_cast this
    push_cast at hR; linarith only [hR]
  have hDM_lo : (9 / 10 : ℝ) * k ≤ (D : ℝ) + M2 := by
    have h1 : (j : ℝ) = (m : ℝ) / 2 + δ_coord m j := by dsimp [δ_coord]; ring
    linarith only [hDM_eq, h1, hba.1, (abs_le.mp hδj).2, hsqL, hkR]
  have hDM_pos : 0 < (D : ℝ) + M2 := by linarith only [hDM_lo, hk_pos]
  have ha_eq : (a : ℝ) = (f : ℝ) / 2 + δ_coord m j / 3 + ε_coord m f j a := by dsimp [δ_coord, ε_coord]; ring
  have ha_le_f : a + d1 ≤ f := by
    have : (a : ℝ) + d1 ≤ f := by
      linarith only [ha_eq, (abs_le.mp hδj).2, (abs_le.mp hεj).2, hba.2.2.1, hsqL, hkR, hd1R]
    exact_mod_cast this
  have hη_diff : |(S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3| ≤ 30 * L / sqrt k := by
    have hS2_eq : (S2 : ℝ) = 2 * ((f : ℝ) - a - d1) + 1 - d2 := by
      dsimp [S2]; have h1 : d2 ≤ 2 * (f - a - d1) + 1 := by omega
      rw [Nat.cast_sub h1, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_two]
      rw [show f - a - d1 = f - (a + d1) by omega, Nat.cast_sub ha_le_f, Nat.cast_add]; ring
    have hnum_eq : (S2 : ℝ) - (2 / 3) * ((D : ℝ) + M2) =
        (f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k) - 2 * ε_coord m f j a +
          (5 / 3 - 2 * (d1 : ℝ) - d2) := by
      rw [hS2_eq, hDM_eq]; dsimp [ε_coord]; ring
    have heq : (S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3 = ((S2 : ℝ) - (2 / 3) * ((D : ℝ) + M2)) / ((D : ℝ) + M2) := by
      field_simp [hDM_pos.ne']
    rw [heq, abs_div, abs_of_pos hDM_pos, hnum_eq]
    have h1sq : (4 : ℝ) ≤ sqrt k * L := by
      have hsq1 : (1 : ℝ) ≤ sqrt k := by rw [le_sqrt (by norm_num) hk_pos.le]; linarith only [hkR]
      have := mul_le_mul hsq1 hL10 (by norm_num) hsq_pos.le; linarith only [this]
    have hnum_le : |(f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k) - 2 * ε_coord m f j a +
        (5 / 3 - 2 * (d1 : ℝ) - d2)| ≤ 25 * sqrt k * L := by
      have hc : |5 / 3 - 2 * (d1 : ℝ) - d2| ≤ 4 := by
        rw [abs_le]; constructor <;> linarith only [Nat.cast_nonneg (α := ℝ) d1, Nat.cast_nonneg (α := ℝ) d2, hd1R, hd2R]
      have htri : |(f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k) - 2 * ε_coord m f j a +
          (5 / 3 - 2 * (d1 : ℝ) - d2)| ≤
          |(f : ℝ) - 2 * k / 3| + |(1 / 3 : ℝ) * ((m : ℝ) - 2 * k)| +
          |2 * ε_coord m f j a| + |5 / 3 - 2 * (d1 : ℝ) - d2| := by
        have t1 := abs_add_le ((f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k) - 2 * ε_coord m f j a)
          (5 / 3 - 2 * (d1 : ℝ) - d2)
        have t2 := abs_sub ((f : ℝ) - 2 * k / 3 - (1 / 3) * ((m : ℝ) - 2 * k)) (2 * ε_coord m f j a)
        have t3 := abs_sub ((f : ℝ) - 2 * k / 3) ((1 / 3 : ℝ) * ((m : ℝ) - 2 * k))
        linarith only [t1, t2, t3]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3),
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
      have hnn : 0 ≤ sqrt k * L := by positivity
      linarith only [htri, hf_box, hm_box, hεj, hc, h1sq, hnn]
    rw [div_le_div_iff₀ hDM_pos hsq_pos]
    have hmul : (25 * sqrt k * L) * sqrt k = 25 * (k : ℝ) * L := by
      calc (25 * sqrt k * L) * sqrt k
          = 25 * (sqrt k * sqrt k) * L := by ring
        _ = 25 * (k : ℝ) * L := by rw [mul_self_sqrt hk_pos.le]
    have h1 := mR hnum_le hsq_pos.le
    have h2 := mL hDM_lo (show 0 ≤ 30 * L by positivity)
    have h27 : 30 * L * (9 / 10 * (k : ℝ)) = 27 * (k : ℝ) * L := by ring
    have hnn : 0 ≤ (k : ℝ) * L := by positivity
    linarith only [h1, h2, hmul, h27, hnn]
  have h30 : 30 * L / sqrt k ≤ 30 / 10 ^ 6 := by
    have hL1 := validMF_pow_le hV 1 (by omega); rw [pow_one] at hL1
    rw [mul_div_assoc]; change 30 * (log k / sqrt k) ≤ _; linarith only [hL1]
  exact ⟨hD_lb, hD_ge100, hD_hi, hM2_lo, hD_le_M2, hDM_eq, hDM_lo, ha_eq, ha_le_f, hη_diff,
    by linarith only [(abs_le.mp hη_diff).1, h30], by linarith only [(abs_le.mp hη_diff).2, h30]⟩

private lemma sum_B_set_le_tot (D M2 f a d1 d2 : ℕ) (B_set : Finset ℕ)
    (hB : ∀ b ∈ B_set, a + d1 ≤ b ∧ b + d2 ≤ f) :
    ∑ b ∈ B_set, (D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) ≤
      (((D + M2).choose (2 * (f - a - d1) + 1 - d2) : ℕ) : ℝ) := by
  let S2 : ℕ := 2 * (f - a - d1) + 1 - d2
  let g : ℕ → ℕ := fun b => 2 * (b - a - d1) + d2
  have hinj : ∀ b1 ∈ B_set, ∀ b2 ∈ B_set, g b1 = g b2 → b1 = b2 := by
    intro b1 h1 b2 h2 heq
    have ha1 := (hB b1 h1).1; have ha2 := (hB b2 h2).1; dsimp [g] at heq; omega
  have hsub_img : B_set.image g ⊆ range (S2 + 1) := by
    intro r hr; obtain ⟨b, hb, rfl⟩ := mem_image.mp hr
    have hb' := hB b hb; exact mem_range.mpr (by dsimp [g, S2]; omega)
  have heq_img : ∑ b ∈ B_set,
      (D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) =
      ∑ r ∈ B_set.image g, (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ) := by
    rw [sum_image hinj]
    refine sum_congr rfl fun b hb => ?_
    have hb' := hB b hb; rw [show S2 - g b = 2 * (f - b - d2) + 1 by dsimp [S2, g]; omega]
  rw [heq_img]
  calc ∑ r ∈ B_set.image g, (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ)
      ≤ ∑ r ∈ range (S2 + 1), (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub_img (fun _ _ _ => by positivity)
    _ = (((D + M2).choose S2 : ℕ) : ℝ) := sum_hypergeom D M2 S2

set_option maxHeartbeats 1600000 in
private lemma hypergeom_odd_moment_bound {k m f d1 d2 j t a : ℕ} (hV : ValidMF k m f)
    (hd1 : d1 ∈ ({0, 1} : Finset ℕ)) (hd2 : d2 ∈ ({0, 1} : Finset ℕ))
    (hjt : j + ⌊log k ^ 7⌋₊ < t) (htm : t < m)
    (hδj : |δ_coord m j| ≤ 40 * sqrt k * log k)
    (hδt : |δ_coord m t| ≤ 40 * sqrt k * log k)
    (hεj : |ε_coord m f j a| ≤ 10 * sqrt k * log k) :
    let L : ℝ := log k
    let D : ℕ := t - j - 1
    let M2 : ℕ := m - t
    let S2 : ℕ := 2 * (f - a - d1) + 1 - d2
    let B_set : Finset ℕ := (range (f + 1)).filter
      (fun b => a + d1 ≤ b ∧ b + d2 ≤ f ∧
        |(b : ℝ) - a - ((t : ℝ) - j) / 3| ≤ 20 * sqrt D * L)
    |∑ b ∈ B_set,
      ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ)) *
        ((b : ℝ) - a - ((t : ℝ) - j) / 3)| ≤
      1e11 * L ^ 3 * (((D + M2).choose S2 : ℕ) : ℝ) := by
  intro L D M2 S2 B_set
  have hba := validMF_eta_bounds hV
  have hsqL := validMF_sqL_le hV
  have ⟨hD_lb, hD_ge100, hD_hi, hM2_lo, hD_le_M2, hDM_eq, hDM_lo, ha_eq, ha_le_f, hη_diff, hη_lo, hη_hi⟩ :=
    box_eta2_bounds hV hd1 hd2 hjt htm hδj hδt hεj
  have ⟨hk, hL, hL15, hexpL, hm_box, hf_box⟩ := hV
  change 10 ^ 20 ≤ L at hL
  change (k : ℝ) ^ 10 * exp (-L ^ 2) ≤ 1 at hexpL
  change sqrt k * L ≤ (k : ℝ) / 10 ^ 6 at hsqL
  change |δ_coord m j| ≤ 40 * sqrt k * L at hδj
  change |δ_coord m t| ≤ 40 * sqrt k * L at hδt
  change |ε_coord m f j a| ≤ 10 * sqrt k * L at hεj
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hL10 : (10 : ℝ) ≤ L := by linarith only [hL]
  have hd1_le1 : d1 ≤ 1 := by simp only [mem_insert, mem_singleton] at hd1; rcases hd1 with rfl | rfl <;> omega
  have hd2_le1 : d2 ≤ 1 := by simp only [mem_insert, mem_singleton] at hd2; rcases hd2 with rfl | rfl <;> omega
  have hd1R : (d1 : ℝ) ≤ 1 := by exact_mod_cast hd1_le1
  have hd2R : (d2 : ℝ) ≤ 1 := by exact_mod_cast hd2_le1
  have hD_pos : (0 : ℝ) < D := by linarith only [hD_ge100]
  have hsqD_pos : 0 < sqrt D := sqrt_pos.mpr hD_pos
  have hM2_pos : (0 : ℝ) < M2 := by linarith only [hM2_lo, hk_pos]
  have hDM_pos : 0 < (D : ℝ) + M2 := by linarith only [hDM_lo, hk_pos]
  let η : ℝ := (S2 : ℝ) / ((D : ℝ) + M2)
  let μr : ℝ := (D : ℝ) * η
  have hL3_sqD : (4 * 10 ^ 9 : ℝ) * L ^ 3 ≤ sqrt D := by
    rw [le_sqrt (by positivity) hD_pos.le]
    have hL6nn : 0 ≤ L ^ 6 := pow_nonneg (by linarith only [hL10]) 6
    have h1 : (10 ^ 20 : ℝ) * L ^ 6 ≤ L ^ 7 := by
      have hmul := mR hL hL6nn
      rw [show L * L ^ 6 = L ^ 7 by ring] at hmul; exact hmul
    have h2 : ((4 * 10 ^ 9 : ℝ) * L ^ 3) ^ 2 = (16 * 10 ^ 18 : ℝ) * L ^ 6 := by ring
    rw [h2]; linarith only [h1, hD_lb, hL6nn]
  have hL2_sqD : 3000 * L ^ 2 ≤ sqrt D * L := by
    have h1 : 3000 * L ≤ (4 * 10 ^ 9 : ℝ) * L ^ 3 := by
      have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
      have hmul := mL hL2 (show 0 ≤ 3000 * L by positivity)
      rw [show 3000 * L * L ^ 2 = 3000 * L ^ 3 by ring] at hmul
      have hnn : 0 ≤ L ^ 3 := pow_nonneg (by linarith only [hL10]) 3
      linarith only [hmul, hnn]
    have hmul := mR (h1.trans hL3_sqD) (by linarith only [hL10] : 0 ≤ L)
    linarith only [hmul]
  have h41_D40 : 41 * sqrt D * L ≤ (D : ℝ) / 40 := by
    have h1 : 1640 * L ≤ sqrt D := by
      have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
      have hmul := mL hL2 (show 0 ≤ 1640 * L by positivity)
      rw [show 1640 * L * L ^ 2 = 1640 * L ^ 3 by ring] at hmul
      have hnn : 0 ≤ L ^ 3 := pow_nonneg (by linarith only [hL10]) 3
      linarith only [hmul, hL3_sqD, hnn]
    have hmul := mL h1 hsqD_pos.le
    rw [mul_self_sqrt hD_pos.le] at hmul
    linarith only [hmul]
  let shift : ℝ := (1 / 2) * ((D : ℝ) * (η - 2 / 3) - (2 / 3 - 2 * (d1 : ℝ) + d2))
  have hshift_le : |shift| ≤ 1300 * L ^ 2 := by
    dsimp [shift]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hDη : |(D : ℝ) * (η - 2 / 3)| ≤ 2400 * L ^ 2 := by
      rw [abs_mul, abs_of_pos hD_pos]
      have hmul := mul_le_mul hD_hi hη_diff (abs_nonneg _) (by positivity)
      have hsimp : (80 * sqrt k * L) * (30 * L / sqrt k) = 2400 * L ^ 2 := by
        field_simp [hsq_pos.ne']; ring
      linarith only [hmul, hsimp]
    have hc : |2 / 3 - 2 * (d1 : ℝ) + d2| ≤ 4 := by
      rw [abs_le]; constructor <;>
        linarith only [Nat.cast_nonneg (α := ℝ) d1, Nat.cast_nonneg (α := ℝ) d2, hd1R, hd2R]
    have h4L2 : (4 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
    have htri := abs_sub ((D : ℝ) * (η - 2 / 3)) (2 / 3 - 2 * (d1 : ℝ) + d2)
    have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
    linarith only [htri, hDη, hc, h4L2, hL2nn]
  let tot : ℝ := (((D + M2).choose S2 : ℕ) : ℝ)
  have hS2_le_DM : S2 ≤ D + M2 := by
    have : (S2 : ℝ) ≤ (D : ℝ) + M2 := by
      have h1 : (S2 : ℝ) = η * ((D : ℝ) + M2) := by dsimp [η]; field_simp [hDM_pos.ne']
      nlinarith only [h1, hη_hi, hDM_pos]
    exact_mod_cast this
  have htot_pos : 0 < tot := by dsimp [tot]; exact_mod_cast Nat.choose_pos hS2_le_DM
  have hhr_eq : ∀ b ∈ B_set,
      (b : ℝ) - a - ((t : ℝ) - j) / 3 =
        (1 / 2) * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) + shift := by
    intro b hb
    have hb_mem := (mem_filter.mp hb).2
    have hsub : b - a - d1 = b - (a + d1) := by omega
    have hD_cast : (D : ℝ) = (t : ℝ) - j - 1 := by
      have : D + j + 1 = t := by dsimp [D]; omega
      have hR : ((D + j + 1 : ℕ) : ℝ) = t := by exact_mod_cast this
      push_cast at hR; linarith only [hR]
    rw [hsub, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_sub hb_mem.1, Nat.cast_add]
    dsimp [μr, shift]; rw [hD_cast]; ring
  have hsum_T_le : ∑ b ∈ B_set,
      (D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) ≤ tot :=
    sum_B_set_le_tot D M2 f a d1 d2 B_set (fun b hb => ⟨(mem_filter.mp hb).2.1, (mem_filter.mp hb).2.2.1⟩)
  let c_b : ℝ := (a : ℝ) + ((t : ℝ) - j) / 3
  have hc_b_lo : (a : ℝ) + 1 + 20 * sqrt D * L ≤ c_b := by
    have h1 : (t : ℝ) - j = (D : ℝ) + 1 := by
      have : D + j + 1 = t := by dsimp [D]; omega
      have hR : ((D + j + 1 : ℕ) : ℝ) = t := by exact_mod_cast this
      push_cast at hR; linarith only [hR]
    dsimp [c_b]; rw [h1]; linarith only [h41_D40, hD_ge100]
  have hc_b_hi : c_b + 20 * sqrt D * L + 1 ≤ (f : ℝ) - 1 := by
    have h1 : c_b = (f : ℝ) / 2 + δ_coord m t / 3 + ε_coord m f j a := by
      dsimp [c_b]; rw [ha_eq]; dsimp [δ_coord]; ring
    have hD_le_k : sqrt D ≤ sqrt k :=
      sqrt_le_sqrt (by linarith only [hD_hi, hsqL, hk_pos])
    have h20D : 20 * sqrt D * L ≤ 20 * sqrt k * L := by
      have hmul := mR hD_le_k (by linarith only [hL10] : 0 ≤ L)
      linarith only [hmul]
    linarith only [h1, h20D, (abs_le.mp hδt).2, (abs_le.mp hεj).2, hba.2.2.1, hsqL, hkR]
  let b_lo : ℕ := Nat.ceil (c_b - 20 * sqrt D * L)
  let b_hi : ℕ := ⌊c_b + 20 * sqrt D * L⌋₊ + 1
  have hcb_sub_nn : 0 ≤ c_b - 20 * sqrt D * L := by
    linarith only [hc_b_lo, Nat.cast_nonneg (α := ℝ) a]
  have hcb_add_nn : 0 ≤ c_b + 20 * sqrt D * L := by
    have hnn : 0 ≤ sqrt D * L := by positivity
    linarith only [hcb_sub_nn, hnn]
  have hB_eq_Ico : B_set = Ico b_lo b_hi := by
    ext b
    simp only [B_set, mem_filter, mem_range, mem_Ico]
    have h1 : b_lo ≤ b ↔ c_b - 20 * sqrt D * L ≤ (b : ℝ) := Nat.ceil_le
    have h2 : b < b_hi ↔ (b : ℝ) ≤ c_b + 20 * sqrt D * L := by
      dsimp [b_hi]
      rw [Nat.lt_succ_iff, Nat.le_floor_iff hcb_add_nn]
    have h3 : |(b : ℝ) - a - ((t : ℝ) - j) / 3| ≤ 20 * sqrt D * L ↔
        c_b - 20 * sqrt D * L ≤ (b : ℝ) ∧ (b : ℝ) ≤ c_b + 20 * sqrt D * L := by
      rw [show (b : ℝ) - a - ((t : ℝ) - j) / 3 = (b : ℝ) - c_b by dsimp [c_b]; ring, abs_le]
      constructor <;> (intro ⟨p, q⟩; exact ⟨by linarith only [p], by linarith only [q]⟩)
    rw [h1, h2, h3]
    constructor
    · rintro ⟨_, _, _, h⟩; exact h
    · rintro ⟨hlo, hhi⟩
      refine ⟨?_, ?_, ?_, ⟨hlo, hhi⟩⟩
      · have : (b : ℝ) < (f : ℝ) + 1 := by linarith only [hhi, hc_b_hi]
        exact_mod_cast this
      · have : (a : ℝ) + d1 ≤ (b : ℝ) := by linarith only [hlo, hc_b_lo, hd1R]
        exact_mod_cast this
      · have : (b : ℝ) + d2 ≤ (f : ℝ) := by linarith only [hhi, hc_b_hi, hd2R]
        exact_mod_cast this
  have hblo_le_bhi : b_lo ≤ b_hi := by
    have hlt : c_b - 20 * sqrt D * L ≤ c_b + 20 * sqrt D * L := by
      have hnn : 0 ≤ sqrt D * L := by positivity
      linarith only [hnn]
    have h1 : (b_lo : ℝ) < c_b - 20 * sqrt D * L + 1 := Nat.ceil_lt_add_one hcb_sub_nn
    have h2 : c_b + 20 * sqrt D * L < (b_hi : ℝ) := by
      dsimp [b_hi]; push_cast; exact Nat.lt_floor_add_one _
    have h3 : (b_lo : ℝ) < (b_hi : ℝ) + 1 := by linarith only [h1, h2, hlt]
    have h4 : b_lo < b_hi + 1 := by exact_mod_cast h3
    omega
  let αr : ℝ := ((D : ℝ) + M2) / (2 * η * (1 - η) * D * M2)
  let Cnorm : ℝ := sqrt (αr / Real.pi)
  have h1mη_pos : 0 < 1 - η := by linarith only [hη_hi]
  have hη_pos : 0 < η := by linarith only [hη_lo]
  have hη_prod_lo : (21 / 100 : ℝ) ≤ η * (1 - η) := by nlinarith only [hη_lo, hη_hi]
  have hη_prod_hi : η * (1 - η) ≤ 1 / 4 := by nlinarith only [sq_nonneg (η - 1 / 2)]
  have hαr_lo : 2 / (D : ℝ) ≤ αr := by
    dsimp [αr]
    rw [div_le_div_iff₀ hD_pos (by positivity)]
    have h1 : 2 * (2 * η * (1 - η) * (D : ℝ) * M2) ≤ (D : ℝ) * M2 := by
      have h2 := mR hη_prod_hi (show 0 ≤ 4 * (D : ℝ) * M2 by positivity)
      linarith only [h2]
    have h2 : (D : ℝ) * M2 ≤ ((D : ℝ) + M2) * D := by nlinarith only [hD_pos, hD_le_M2]
    linarith only [h1, h2]
  have hαr_hi : αr ≤ 5 / (D : ℝ) := by
    dsimp [αr]
    rw [div_le_div_iff₀ (by positivity) hD_pos]
    have h1 : ((D : ℝ) + M2) * D ≤ 2 * M2 * D := by nlinarith only [hD_le_M2, hD_pos]
    have h2 : 2 * M2 * D ≤ 5 * (2 * η * (1 - η) * D * M2) := by
      have h3 := mR hη_prod_lo (show 0 ≤ 10 * (D : ℝ) * M2 by positivity)
      have h4 : 5 * (2 * η * (1 - η) * (D : ℝ) * M2) = η * (1 - η) * (10 * (D : ℝ) * M2) := by ring
      have h5 : (21 / 100 : ℝ) * (10 * (D : ℝ) * M2) = (21 / 10 : ℝ) * ((D : ℝ) * M2) := by ring
      have h6 : 2 * (M2 : ℝ) * D = 2 * ((D : ℝ) * M2) := by ring
      have hnn : 0 ≤ (D : ℝ) * M2 := by positivity
      linarith only [h3, h4, h5, h6, hnn]
    linarith only [h1, h2]
  have hαr_pos : 0 < αr := lt_of_lt_of_le (by positivity) hαr_lo
  have hCnorm_le : Cnorm ≤ sqrt αr := by
    dsimp [Cnorm]
    apply sqrt_le_sqrt
    rw [div_le_iff₀ pi_pos]
    have hpi : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num) pi_gt_three.le
    nlinarith only [hpi, hαr_pos]
  have hT_approx : ∀ b ∈ B_set,
      let r : ℕ := 2 * (b - a - d1) + d2
      let v : ℝ := (r : ℝ) - μr
      |(D.choose r : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) -
        tot * Cnorm * exp (-αr * v ^ 2)| ≤
        (1.4e9 * L ^ 3 / sqrt D) * tot * Cnorm * exp (-αr * v ^ 2) := by
    intro b hb r v
    have hb' := (mem_filter.mp hb).2
    have hsr : S2 - r = 2 * (f - b - d2) + 1 := by dsimp [S2, r]; omega
    rw [← hsr]
    have hv_abs : |v| ≤ 41 * sqrt D * L := by
      have h1 := hhr_eq b hb
      have hveq : v = 2 * ((b : ℝ) - a - ((t : ℝ) - j) / 3) - 2 * shift := by dsimp [v, r]; linarith only [h1]
      rw [hveq]
      have htri := abs_sub (2 * ((b : ℝ) - a - ((t : ℝ) - j) / 3)) (2 * shift)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
      have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
      have h1' : 40 * sqrt D * L + sqrt D * L = 41 * sqrt D * L := by ring
      linarith only [htri, hb'.2.2, hshift_le, hL2_sqD, hL2nn, h1']
    have hv_D40 : |v| ≤ (D : ℝ) / 40 := hv_abs.trans h41_D40
    have hv_M40 : |v| ≤ (M2 : ℝ) / 40 := hv_D40.trans (by linarith only [hD_le_M2])
    have hr_le_S2 : r ≤ S2 := by dsimp [r, S2]; omega
    have hv2_eq : ((S2 - r : ℕ) : ℝ) - (M2 : ℝ) * η = -v := by
      rw [Nat.cast_sub hr_le_S2]
      have hS2η : (S2 : ℝ) = ((D : ℝ) + M2) * η := by dsimp [η]; field_simp [hDM_pos.ne']
      dsimp [v, μr]; linarith only [hS2η]
    have hmD := log_choose_master D r (N0 := D) (R0 := (D : ℝ) * η)
      (by linarith only [hD_ge100]) (by nlinarith only [hη_lo, hD_pos]) (by nlinarith only [hη_hi, hD_pos])
      (by rw [sub_self, abs_zero]; positivity) (by change |v| ≤ _; exact hv_D40)
    have hmM := log_choose_master M2 (S2 - r) (N0 := M2) (R0 := (M2 : ℝ) * η)
      (by linarith only [hD_ge100, hD_le_M2]) (by nlinarith only [hη_lo, hM2_pos]) (by nlinarith only [hη_hi, hM2_pos])
      (by rw [sub_self, abs_zero]; positivity) (by rw [hv2_eq, abs_neg]; exact hv_M40)
    have hmDM := log_choose_master (D + M2) S2 (N0 := (D : ℝ) + M2) (R0 := ((D : ℝ) + M2) * η)
      (by linarith only [hD_ge100, hM2_pos]) (by nlinarith only [hη_lo, hDM_pos]) (by nlinarith only [hη_hi, hDM_pos])
      (by push_cast; rw [sub_self, abs_zero]; positivity)
      (by
        have hS2η : (S2 : ℝ) = ((D : ℝ) + M2) * η := by dsimp [η]; field_simp [hDM_pos.ne']
        rw [hS2η, sub_self, abs_zero]; positivity)
    dsimp only at hmD hmM hmDM
    have hηD : (D : ℝ) * η / (D : ℝ) = η := by field_simp [hD_pos.ne']
    have hηM : (M2 : ℝ) * η / (M2 : ℝ) = η := by field_simp [hM2_pos.ne']
    have hηDM : ((D : ℝ) + M2) * η / ((D : ℝ) + M2) = η := by field_simp [hDM_pos.ne']
    have hS2η : (S2 : ℝ) = ((D : ℝ) + M2) * η := by dsimp [η]; field_simp [hDM_pos.ne']
    rw [sub_self, hηD] at hmD
    rw [sub_self, hv2_eq, hηM] at hmM
    rw [Nat.cast_add, sub_self, hS2η, sub_self, hηDM] at hmDM
    simp only [zero_mul, mul_zero, zero_add, add_zero, sub_zero, abs_zero, zero_pow (by norm_num : 3 ≠ 0),
      abs_neg] at hmD hmM hmDM
    have herr_v : ∀ {N : ℝ}, (D : ℝ) ≤ N →
        4000 * (|v| ^ 3 / N ^ 2 + (|v| + 1) / N) ≤ 3e8 * (L ^ 3 / sqrt D) := fun {N} hDN => by
      have hN_pos : 0 < N := lt_of_lt_of_le hD_pos hDN
      have h1 : |v| ^ 3 ≤ 41 ^ 3 * ((D : ℝ) * sqrt D) * L ^ 3 := by
        have hp := pow_le_pow_left₀ (abs_nonneg v) hv_abs 3
        have hrew : (41 * sqrt D * L) ^ 3 =
            41 ^ 3 * (sqrt D ^ 2 * sqrt D) * L ^ 3 := by ring
        rw [hrew, sq_sqrt hD_pos.le] at hp; exact hp
      have hcub : |v| ^ 3 / N ^ 2 ≤ 41 ^ 3 * (L ^ 3 / sqrt D) := by
        have hDN2 : (D : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hD_pos.le hDN 2
        rw [div_le_iff₀ (by positivity)]
        have h2 : 41 ^ 3 * (L ^ 3 / sqrt D) * (D : ℝ) ^ 2 =
            41 ^ 3 * ((D : ℝ) * sqrt D) * L ^ 3 := by
          rw [show (D : ℝ) ^ 2 = (D : ℝ) * (sqrt D * sqrt D) by
            rw [mul_self_sqrt hD_pos.le]; ring]
          field_simp [hsqD_pos.ne']
        have h3 := mL hDN2 (show 0 ≤ 41 ^ 3 * (L ^ 3 / sqrt D) by positivity)
        linarith only [h1, h2, h3]
      have hlin : (|v| + 1) / N ≤ 50 * (L ^ 3 / sqrt D) := by
        have hL13 : L ≤ L ^ 3 := by
          have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ L by linarith only [hL10]) (show 1 ≤ 3 by omega)
          simpa only [pow_one] using h
        have h1sqD : (1 : ℝ) ≤ sqrt D * L := by
          have : (1 : ℝ) ≤ sqrt D := by rw [le_sqrt (by norm_num) hD_pos.le]; linarith only [hD_ge100]
          have := mul_le_mul this hL10 (by norm_num) hsqD_pos.le; linarith only [this]
        have hnum : |v| + 1 ≤ 50 * sqrt D * L ^ 3 := by
          have hmul := mL hL13 hsqD_pos.le
          have h1' : 42 * (sqrt D * L) ≤ 42 * (sqrt D * L ^ 3) := by linarith only [hmul]
          have h2' : 42 * (sqrt D * L ^ 3) = 42 * sqrt D * L ^ 3 := by ring
          have h3' : 41 * sqrt D * L + sqrt D * L = 42 * (sqrt D * L) := by ring
          have hnn : 0 ≤ sqrt D * L ^ 3 := by positivity
          linarith only [hv_abs, h1sqD, h1', h2', h3', hnn]
        rw [div_le_iff₀ hN_pos]
        have h2 : 50 * (L ^ 3 / sqrt D) * (D : ℝ) = 50 * sqrt D * L ^ 3 := by
          calc 50 * (L ^ 3 / sqrt D) * (D : ℝ)
              = 50 * (L ^ 3 / sqrt D) * (sqrt D * sqrt D) := by
                rw [mul_self_sqrt hD_pos.le]
            _ = 50 * sqrt D * L ^ 3 := by field_simp [hsqD_pos.ne']
        have h3 := mL hDN (show 0 ≤ 50 * (L ^ 3 / sqrt D) by positivity)
        linarith only [hnum, h2, h3]
      have hnn : 0 ≤ L ^ 3 / sqrt D := by positivity
      linarith only [hcub, hlin, hnn]
    have heD : |log (D.choose r : ℝ) - (logG (D : ℝ) ((D : ℝ) * η) + v * log ((1 - η) / η) -
        v ^ 2 / (2 * η * (1 - η) * (D : ℝ)))| ≤ 3e8 * (L ^ 3 / sqrt D) :=
      hmD.trans (herr_v le_rfl)
    have heM : |log (M2.choose (S2 - r) : ℝ) - (logG (M2 : ℝ) ((M2 : ℝ) * η) + (-v) * log ((1 - η) / η) -
        v ^ 2 / (2 * η * (1 - η) * (M2 : ℝ)))| ≤ 3e8 * (L ^ 3 / sqrt D) := by
      have hmM' : |log (M2.choose (S2 - r) : ℝ) - (logG (M2 : ℝ) ((M2 : ℝ) * η) + (-v) * log ((1 - η) / η) -
          (-v) ^ 2 / (2 * η * (1 - η) * (M2 : ℝ)))| ≤
          4000 * (|v| ^ 3 / (M2 : ℝ) ^ 2 + (|v| + 1) / (M2 : ℝ)) := hmM
      rw [neg_sq] at hmM'
      exact hmM'.trans (herr_v hD_le_M2)
    have heDM : |log (((D + M2).choose S2 : ℕ) : ℝ) - logG ((D : ℝ) + M2) (((D : ℝ) + M2) * η)| ≤
        1e5 * (L ^ 3 / sqrt D) := by
      have h1 : 4000 * (0 / ((D : ℝ) + M2) ^ 2 + 1 / ((D : ℝ) + M2)) ≤ 1e5 * (L ^ 3 / sqrt D) := by
        rw [zero_div, zero_add]
        have hsq1 : sqrt D ≤ (D : ℝ) + M2 := by
          have : sqrt D ≤ (D : ℝ) := by
            rw [sqrt_le_left hD_pos.le]; nlinarith only [hD_ge100]
          linarith only [this, hM2_pos]
        have hL3_1 : (1 : ℝ) ≤ L ^ 3 := by
          have := pow_le_pow_left₀ (by norm_num) hL10 3; linarith only [this]
        have hdiv : 1 / ((D : ℝ) + M2) ≤ L ^ 3 / sqrt D := by
          rw [div_le_div_iff₀ hDM_pos hsqD_pos]
          have := mul_le_mul hL3_1 hsq1 hsqD_pos.le (by linarith only [hL3_1])
          linarith only [this]
        have hnn : 0 ≤ L ^ 3 / sqrt D := by positivity
        linarith only [hdiv, hnn]
      have hmDM' : |log (((D + M2).choose S2 : ℕ) : ℝ) -
          (logG ((D : ℝ) + M2) (((D : ℝ) + M2) * η) - 0 ^ 2 / (2 * η * (1 - η) * ((D : ℝ) + M2)))| ≤
          4000 * (0 / ((D : ℝ) + M2) ^ 2 + 1 / ((D : ℝ) + M2)) := hmDM
      rw [show (0 : ℝ) ^ 2 / (2 * η * (1 - η) * ((D : ℝ) + M2)) = 0 by ring, sub_zero] at hmDM'
      exact hmDM'.trans h1
    have hr_le_D : r ≤ D := by
      have : (r : ℝ) ≤ D := by
        have h1 : (r : ℝ) = μr + v := by dsimp [v]; ring
        have h2 : μr ≤ (7 / 10 : ℝ) * D := by dsimp [μr]; nlinarith only [hη_hi, hD_pos]
        linarith only [h1, h2, (abs_le.mp hv_D40).2, hD_pos]
      exact_mod_cast this
    have hSr_le_M2 : S2 - r ≤ M2 := by
      have : ((S2 - r : ℕ) : ℝ) ≤ M2 := by
        have h1 : ((S2 - r : ℕ) : ℝ) = (M2 : ℝ) * η - v := by linarith only [hv2_eq]
        have h2 : (M2 : ℝ) * η ≤ (7 / 10 : ℝ) * M2 := by nlinarith only [hη_hi, hM2_pos]
        linarith only [h1, h2, (abs_le.mp hv_M40).1, hM2_pos]
      exact_mod_cast this
    have hDr_pos : (0 : ℝ) < (D.choose r : ℝ) := by exact_mod_cast Nat.choose_pos hr_le_D
    have hMS_pos : (0 : ℝ) < (M2.choose (S2 - r) : ℝ) := by exact_mod_cast Nat.choose_pos hSr_le_M2
    have hX_pos : 0 < (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ) / tot := by positivity
    have hlogG_id := logG_hypergeom hD_pos hM2_pos hη_pos (by linarith only [hη_hi])
    have hquad_id : v ^ 2 / (2 * η * (1 - η) * (D : ℝ)) + v ^ 2 / (2 * η * (1 - η) * (M2 : ℝ)) = αr * v ^ 2 := by
      dsimp [αr]; field_simp [hη_pos.ne', h1mη_pos.ne', hD_pos.ne', hM2_pos.ne']; ring
    have hY_eq : exp ((1 / 2) * log (((D : ℝ) + M2) / (2 * Real.pi * η * (1 - η) * D * M2)) - αr * v ^ 2) =
        Cnorm * exp (-αr * v ^ 2) := by
      have harg : ((D : ℝ) + M2) / (2 * Real.pi * η * (1 - η) * D * M2) = αr / Real.pi := by
        dsimp [αr]; field_simp [pi_pos.ne', hη_pos.ne', h1mη_pos.ne', hD_pos.ne', hM2_pos.ne']
      rw [harg, sub_eq_add_neg, exp_add,
        show (1 / 2 : ℝ) * log (αr / Real.pi) = log (αr / Real.pi) * (1 / 2) by ring,
        ← rpow_def_of_pos (div_pos hαr_pos pi_pos), ← sqrt_eq_rpow]
      dsimp [Cnorm]; rw [show -(αr * v ^ 2) = -αr * v ^ 2 by ring]
    have hlog_err : |log ((D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ) / tot) -
        ((1 / 2) * log (((D : ℝ) + M2) / (2 * Real.pi * η * (1 - η) * D * M2)) - αr * v ^ 2)| ≤
        7e8 * (L ^ 3 / sqrt D) := by
      rw [log_div (mul_pos hDr_pos hMS_pos).ne' htot_pos.ne',
        log_mul hDr_pos.ne' hMS_pos.ne', ← hlogG_id]
      have hrew : log (D.choose r : ℝ) + log (M2.choose (S2 - r) : ℝ) - log tot -
          (logG (D : ℝ) ((D : ℝ) * η) + logG (M2 : ℝ) ((M2 : ℝ) * η) -
            logG ((D : ℝ) + M2) (((D : ℝ) + M2) * η) - αr * v ^ 2) =
          (log (D.choose r : ℝ) - (logG (D : ℝ) ((D : ℝ) * η) + v * log ((1 - η) / η) -
            v ^ 2 / (2 * η * (1 - η) * (D : ℝ)))) +
          (log (M2.choose (S2 - r) : ℝ) - (logG (M2 : ℝ) ((M2 : ℝ) * η) + (-v) * log ((1 - η) / η) -
            v ^ 2 / (2 * η * (1 - η) * (M2 : ℝ)))) -
          (log tot - logG ((D : ℝ) + M2) (((D : ℝ) + M2) * η)) := by
        rw [← hquad_id]; ring
      rw [hrew]
      have htri := abs_add_sub_le
        (log (D.choose r : ℝ) - (logG (D : ℝ) ((D : ℝ) * η) + v * log ((1 - η) / η) -
          v ^ 2 / (2 * η * (1 - η) * (D : ℝ))))
        (log (M2.choose (S2 - r) : ℝ) - (logG (M2 : ℝ) ((M2 : ℝ) * η) + (-v) * log ((1 - η) / η) -
          v ^ 2 / (2 * η * (1 - η) * (M2 : ℝ))))
        (log tot - logG ((D : ℝ) + M2) (((D : ℝ) + M2) * η))
      have hnn : 0 ≤ L ^ 3 / sqrt D := by positivity
      linarith only [htri, heD, heM, heDM, hnn]
    have htiny : 7e8 * (L ^ 3 / sqrt D) ≤ 1 / 2 := by
      have hdiv : L ^ 3 / sqrt D ≤ 1 / (4 * 10 ^ 9) := by
        rw [div_le_div_iff₀ hsqD_pos (by norm_num)]; linarith only [hL3_sqD]
      linarith only [hdiv]
    have hexp_app := abs_sub_exp_of_log_approx hX_pos hlog_err htiny
    rw [hY_eq] at hexp_app
    have hmul_tot := mL hexp_app htot_pos.le
    have hlhs : tot * |(D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ) / tot - Cnorm * exp (-αr * v ^ 2)| =
        |(D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ) - tot * Cnorm * exp (-αr * v ^ 2)| := by
      rw [← abs_of_pos htot_pos, ← abs_mul, abs_of_pos htot_pos]
      congr 1; field_simp [htot_pos.ne']
    have hrhs_eq : tot * (2 * (7e8 * (L ^ 3 / sqrt D)) * (Cnorm * exp (-αr * v ^ 2))) =
        (1.4e9 * L ^ 3 / sqrt D) * tot * Cnorm * exp (-αr * v ^ 2) := by ring
    linarith only [hmul_tot, hlhs, hrhs_eq]
  let Q : ℕ := b_hi - b_lo
  let a0 : ℝ := 2 * ((b_lo : ℝ) - a - d1) + d2 - μr
  have hQ_bij : ∀ (f_b : ℕ → ℝ), ∑ b ∈ B_set, f_b b = ∑ q ∈ range Q, f_b (b_lo + q) := by
    intro f_b
    rw [hB_eq_Ico]
    have hIco : Ico b_lo b_hi = (range Q).image (fun q => b_lo + q) := by
      ext b; simp only [mem_Ico, mem_image, mem_range]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨b - b_lo, by dsimp [Q]; omega, by omega⟩
      · rintro ⟨q, hq, rfl⟩; dsimp [Q] at hq; omega
    rw [hIco, sum_image (fun x _ y _ h => by omega)]
  have hv_q : ∀ q ∈ range Q,
      (((2 * ((b_lo + q) - a - d1) + d2 : ℕ) : ℝ) - μr) = a0 + 2 * (q : ℝ) := by
    intro q hq
    have hmem : b_lo + q ∈ B_set := by
      rw [hB_eq_Ico, mem_Ico]; have hq' := mem_range.mp hq; dsimp [Q] at hq'; omega
    have hge : a + d1 ≤ b_lo + q := (mem_filter.mp hmem).2.1
    have hge0 : a + d1 ≤ b_lo := by
      have : (a : ℝ) + d1 ≤ (b_lo : ℝ) := by
        have h1 : c_b - 20 * sqrt D * L ≤ (b_lo : ℝ) := Nat.le_ceil _
        linarith only [h1, hc_b_lo, hd1R]
      exact_mod_cast this
    have hsub1 : (b_lo + q) - a - d1 = (b_lo + q) - (a + d1) := by omega
    rw [hsub1, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_sub hge, Nat.cast_add, Nat.cast_add]
    dsimp [a0]; ring
  have hsum_err : ∑ b ∈ B_set,
      |(D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) -
        tot * Cnorm * exp (-αr * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2)| *
      |((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr| ≤
      3e10 * L ^ 3 * tot := by
    have hpt_v : ∀ x : ℝ, Cnorm * (|x| * exp (-αr * x ^ 2)) ≤ 2 * exp (-(αr / 2) * x ^ 2) := by
      intro x
      let u : ℝ := sqrt (αr / 2) * |x|
      have hu_nn : 0 ≤ u := by dsimp [u]; positivity
      have hu_sq : u ^ 2 = (αr / 2) * x ^ 2 := by
        dsimp [u]; rw [mul_pow, sq_sqrt (by positivity), sq_abs]
      have hu_le : u * exp (-u ^ 2) ≤ 1 := by
        have h1 : u ≤ 1 + u ^ 2 := by nlinarith only [sq_nonneg (u - 1)]
        have h2 : 1 + u ^ 2 ≤ exp (u ^ 2) := by linarith only [add_one_le_exp (u ^ 2)]
        have h3 := mR (h1.trans h2) (exp_pos (-u ^ 2)).le
        rwa [← exp_add, add_neg_cancel, exp_zero] at h3
      have hC_sq : Cnorm / sqrt (αr / 2) ≤ 2 := by
        rw [div_le_iff₀ (sqrt_pos.mpr (by positivity))]
        have h1 : sqrt αr ≤ 2 * sqrt (αr / 2) := by
          rw [sqrt_div hαr_pos.le]
          have hsq2 : sqrt 2 ≤ 2 := by rw [sqrt_le_left (by norm_num)]; norm_num
          rw [mul_div_assoc', le_div_iff₀ (sqrt_pos.mpr (by norm_num))]
          nlinarith only [hsq2, sqrt_nonneg αr]
        exact hCnorm_le.trans h1
      have hsplit : exp (-αr * x ^ 2) = exp (-u ^ 2) * exp (-(αr / 2) * x ^ 2) := by
        rw [← exp_add]; congr 1; rw [hu_sq]; ring
      have hxu : |x| = u / sqrt (αr / 2) := by
        dsimp [u]; field_simp [(sqrt_pos.mpr (by positivity : 0 < αr / 2)).ne']
      rw [hsplit, hxu]
      calc Cnorm * (u / sqrt (αr / 2) * (exp (-u ^ 2) * exp (-(αr / 2) * x ^ 2)))
          = (Cnorm / sqrt (αr / 2)) * (u * exp (-u ^ 2)) * exp (-(αr / 2) * x ^ 2) := by ring
        _ ≤ 2 * 1 * exp (-(αr / 2) * x ^ 2) :=
            mR (mul_le_mul hC_sq hu_le (by positivity) (by norm_num))
              (exp_pos _).le
        _ = 2 * exp (-(αr / 2) * x ^ 2) := by ring
    have hsum_gauss : ∑ b ∈ B_set,
        exp (-(αr / 2) * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2) ≤ 10 * sqrt D := by
      rw [hQ_bij]
      have hcongr : ∑ q ∈ range Q,
          exp (-(αr / 2) * (((2 * ((b_lo + q) - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2) =
          ∑ q ∈ range Q, exp (-(αr / 2) * (a0 + 2 * (q : ℝ)) ^ 2) :=
        sum_congr rfl fun q hq => by rw [hv_q q hq]
      rw [hcongr]
      have hs := sum_exp_sq_of_step_ge_one Q (fun q => a0 + 2 * (q : ℝ)) (by positivity : 0 < αr / 2)
        (fun q => by push_cast; linarith)
      have hsq_le : 4 / sqrt (αr / 2) ≤ 4 * sqrt D := by
        rw [div_le_iff₀ (sqrt_pos.mpr (by positivity))]
        have h1 : (1 : ℝ) ≤ (D : ℝ) * (αr / 2) := by
          have := mL hαr_lo hD_pos.le
          rw [mul_div_cancel₀ _ hD_pos.ne'] at this; linarith only [this]
        have h2 : (1 : ℝ) ≤ sqrt D * sqrt (αr / 2) := by
          rw [← sqrt_mul hD_pos.le, le_sqrt (by norm_num) (by positivity)]
          simpa only [one_pow] using h1
        linarith only [h2]
      have h6 : (6 : ℝ) ≤ 6 * sqrt D := by
        have : (1 : ℝ) ≤ sqrt D := by rw [le_sqrt (by norm_num) hD_pos.le]; linarith only [hD_ge100]
        linarith only [this]
      linarith only [hs, hsq_le, h6]
    calc ∑ b ∈ B_set,
          |(D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) -
            tot * Cnorm * exp (-αr * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2)| *
          |((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr|
        ≤ ∑ b ∈ B_set, (1.4e9 * L ^ 3 / sqrt D) * tot *
            (2 * exp (-(αr / 2) * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2)) := by
          apply sum_le_sum; intro b hb
          have h1 := mR (hT_approx b hb)
            (abs_nonneg (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr))
          have h2 : (1.4e9 * L ^ 3 / sqrt D) * tot * Cnorm *
              exp (-αr * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2) *
              |((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr| =
              (1.4e9 * L ^ 3 / sqrt D) * tot *
              (Cnorm * (|((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr| *
                exp (-αr * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2))) := by ring
          rw [h2] at h1
          exact h1.trans (mL (hpt_v _) (by positivity))
      _ = (2.8e9 * L ^ 3 / sqrt D) * tot *
          ∑ b ∈ B_set, exp (-(αr / 2) * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2) := by
          rw [mul_sum]; refine sum_congr rfl fun b _ => by ring
      _ ≤ (2.8e9 * L ^ 3 / sqrt D) * tot * (10 * sqrt D) :=
          mL hsum_gauss (by positivity)
      _ = 2.8e10 * L ^ 3 * tot := by field_simp [hsqD_pos.ne']; ring
      _ ≤ 3e10 * L ^ 3 * tot := by
          have hnn : 0 ≤ L ^ 3 * tot := by positivity
          linarith only [hnn]
  have hmain_odd : |tot * Cnorm * ∑ b ∈ B_set,
      phiG αr (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr)| ≤ 1000 * tot := by
    rw [hQ_bij]
    have hcongr : ∑ q ∈ range Q, phiG αr (((2 * ((b_lo + q) - a - d1) + d2 : ℕ) : ℝ) - μr) =
        ∑ q ∈ range Q, phiG αr (a0 + 2 * (q : ℝ)) :=
      sum_congr rfl fun q hq => by rw [hv_q q hq]
    rw [hcongr]
    have hαs : αr * (2 : ℝ) ^ 2 ≤ 1 := by
      have h0 : 4 * (5 / (D : ℝ)) = 20 / (D : ℝ) := by ring
      have h1 : 4 * αr ≤ 20 / (D : ℝ) := by linarith only [hαr_hi, h0]
      have h2 : 20 / (D : ℝ) ≤ 1 := by rw [div_le_one hD_pos]; linarith only [hD_ge100]
      linarith only [h1, h2]
    have hmvt := odd_gaussian_sum_mvt hαr_pos (by norm_num : (0 : ℝ) < 2) hαs a0 Q
    have ha0_dist : 30 * sqrt D * L ≤ |a0| := by
      have hblo_lt : (b_lo : ℝ) < c_b - 20 * sqrt D * L + 1 := Nat.ceil_lt_add_one hcb_sub_nn
      have ha0_eq : a0 = 2 * ((b_lo : ℝ) - c_b) - 2 * shift := by
        have hD_cast : (D : ℝ) = (t : ℝ) - j - 1 := by
          have : D + j + 1 = t := by dsimp [D]; omega
          have hR : ((D + j + 1 : ℕ) : ℝ) = t := by exact_mod_cast this
          push_cast at hR; linarith only [hR]
        dsimp [a0, c_b, μr, shift]; rw [hD_cast]; ring
      have h1sqD : (2 : ℝ) ≤ sqrt D * L := by
        have : (1 : ℝ) ≤ sqrt D := by rw [le_sqrt (by norm_num) hD_pos.le]; linarith only [hD_ge100]
        have := mul_le_mul this hL10 (by norm_num) hsqD_pos.le; linarith only [this]
      have hneg : a0 ≤ -(30 * sqrt D * L) := by
        linarith only [ha0_eq, hblo_lt, (abs_le.mp hshift_le).1, hL2_sqD, h1sqD]
      have hpos : 30 * sqrt D * L ≤ -a0 := by linarith only [hneg]
      exact hpos.trans (neg_le_abs a0)
    have ha1_dist : 30 * sqrt D * L ≤ |a0 + 2 * (Q : ℝ)| := by
      have hbhi_gt : c_b + 20 * sqrt D * L < (b_hi : ℝ) := by
        dsimp [b_hi]; push_cast; exact Nat.lt_floor_add_one _
      have ha1_eq : a0 + 2 * (Q : ℝ) = 2 * ((b_hi : ℝ) - c_b) - 2 * shift := by
        have hD_cast : (D : ℝ) = (t : ℝ) - j - 1 := by
          have : D + j + 1 = t := by dsimp [D]; omega
          have hR : ((D + j + 1 : ℕ) : ℝ) = t := by exact_mod_cast this
          push_cast at hR; linarith only [hR]
        have hQ_cast : (Q : ℝ) = (b_hi : ℝ) - b_lo := by dsimp [Q]; exact Nat.cast_sub hblo_le_bhi
        dsimp [a0, c_b, μr, shift]; rw [hQ_cast, hD_cast]; ring
      have hpos : 30 * sqrt D * L ≤ a0 + 2 * (Q : ℝ) := by
        have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
        have hDnn : 0 ≤ sqrt D * L := by positivity
        have h1' : 40 * sqrt D * L - sqrt D * L = 39 * sqrt D * L := by ring
        linarith only [ha1_eq, hbhi_gt, (abs_le.mp hshift_le).2, hL2_sqD, hL2nn, hDnn, h1']
      exact hpos.trans (le_abs_self _)
    have hexp_bdy : ∀ x : ℝ, 30 * sqrt D * L ≤ |x| →
        exp (-αr * x ^ 2) ≤ exp (-L ^ 2) := fun x hx => by
      apply exp_le_exp.mpr
      have hsq : 900 * (D : ℝ) * L ^ 2 ≤ x ^ 2 := by
        have h1 := pow_le_pow_left₀ (by positivity) hx 2
        rw [sq_abs, mul_pow, mul_pow, sq_sqrt hD_pos.le] at h1; linarith only [h1]
      have hmul := mul_le_mul hαr_lo hsq (by positivity) (by positivity)
      have hsimp : (2 / (D : ℝ)) * (900 * (D : ℝ) * L ^ 2) = 1800 * L ^ 2 := by field_simp [hD_pos.ne']; ring
      have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
      linarith only [hmul, hsimp, hL2nn]
    have hsum_abs : |∑ q ∈ range Q, phiG αr (a0 + 2 * (q : ℝ))| ≤
        (2 * exp (-L ^ 2)) / (4 * αr) + (120 + 80 / sqrt αr) := by
      have htri := abs_add_le
        ((∑ q ∈ range Q, phiG αr (a0 + 2 * (q : ℝ))) -
          (exp (-αr * a0 ^ 2) - exp (-αr * (a0 + 2 * (Q : ℝ)) ^ 2)) / (2 * αr * 2))
        ((exp (-αr * a0 ^ 2) - exp (-αr * (a0 + 2 * (Q : ℝ)) ^ 2)) / (2 * αr * 2))
      rw [sub_add_cancel] at htri
      have hbnd : |(exp (-αr * a0 ^ 2) - exp (-αr * (a0 + 2 * (Q : ℝ)) ^ 2)) / (2 * αr * 2)| ≤
          (2 * exp (-L ^ 2)) / (4 * αr) := by
        rw [show 2 * αr * 2 = 4 * αr by ring, abs_div, abs_of_pos (by positivity : 0 < 4 * αr)]
        apply dR _ (by positivity)
        have h1 := abs_sub (exp (-αr * a0 ^ 2)) (exp (-αr * (a0 + 2 * (Q : ℝ)) ^ 2))
        rw [abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)] at h1
        linarith only [h1, hexp_bdy a0 ha0_dist, hexp_bdy (a0 + 2 * (Q : ℝ)) ha1_dist]
      linarith only [htri, hmvt, hbnd]
    rw [abs_mul, abs_mul, abs_of_pos htot_pos, abs_of_nonneg (sqrt_nonneg _)]
    have hC_mul : Cnorm * ((2 * exp (-L ^ 2)) / (4 * αr) + (120 + 80 / sqrt αr)) ≤ 1000 := by
      have hsqα_pos : 0 < sqrt αr := sqrt_pos.mpr hαr_pos
      have hsqα_le1 : sqrt αr ≤ 1 := by
        rw [sqrt_le_one]; have h1 : 5 / (D : ℝ) ≤ 1 := by rw [div_le_one hD_pos]; linarith only [hD_ge100]
        exact hαr_hi.trans h1
      have hinv_sqα : 1 / sqrt αr ≤ sqrt D := by
        rw [div_le_iff₀ hsqα_pos]
        have h1 : (1 : ℝ) ≤ (D : ℝ) * αr := by
          have := mL hαr_lo hD_pos.le
          rw [mul_div_cancel₀ _ hD_pos.ne'] at this; linarith only [this]
        rw [← sqrt_mul hD_pos.le, le_sqrt (by norm_num) (by positivity)]
        simpa only [one_pow] using h1
      have hpart1 : sqrt αr * ((2 * exp (-L ^ 2)) / (4 * αr)) ≤ 1 := by
        have heq : sqrt αr * ((2 * exp (-L ^ 2)) / (4 * αr)) =
            (1 / sqrt αr) * exp (-L ^ 2) / 2 := by
          calc sqrt αr * ((2 * exp (-L ^ 2)) / (4 * αr))
              = sqrt αr * ((2 * exp (-L ^ 2)) / (4 * (sqrt αr * sqrt αr))) := by
                rw [mul_self_sqrt hαr_pos.le]
            _ = (1 / sqrt αr) * exp (-L ^ 2) / 2 := by field_simp [hsqα_pos.ne']; ring
        rw [heq]
        have hD_k10 : sqrt D ≤ (k : ℝ) ^ 10 := by
          have h1 : sqrt D ≤ (k : ℝ) := by
            rw [sqrt_le_left hk_pos.le]
            have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hkR]
            linarith only [hD_hi, hsqL, hkR, hk2]
          have h2 : (k : ℝ) ^ 1 ≤ (k : ℝ) ^ 10 := pow_le_pow_right₀ (by linarith only [hkR]) (by omega)
          linarith only [h1, h2]
        have hmul := mR (hinv_sqα.trans hD_k10) (exp_pos (-L ^ 2)).le
        linarith only [hmul, hexpL]
      have hpart2 : sqrt αr * (120 + 80 / sqrt αr) ≤ 200 := by
        have heq : sqrt αr * (120 + 80 / sqrt αr) = 120 * sqrt αr + 80 := by
          field_simp [hsqα_pos.ne']
        rw [heq]; linarith only [hsqα_le1]
      calc Cnorm * ((2 * exp (-L ^ 2)) / (4 * αr) + (120 + 80 / sqrt αr))
          ≤ sqrt αr * ((2 * exp (-L ^ 2)) / (4 * αr) + (120 + 80 / sqrt αr)) :=
            mR hCnorm_le (by positivity)
        _ = sqrt αr * ((2 * exp (-L ^ 2)) / (4 * αr)) +
            sqrt αr * (120 + 80 / sqrt αr) := by ring
        _ ≤ 1 + 200 := add_le_add hpart1 hpart2
        _ ≤ 1000 := by norm_num
    calc tot * Cnorm * |∑ q ∈ range Q, phiG αr (a0 + 2 * (q : ℝ))|
        ≤ tot * Cnorm * ((2 * exp (-L ^ 2)) / (4 * αr) + (120 + 80 / sqrt αr)) :=
          mL hsum_abs (by positivity)
      _ = tot * (Cnorm * ((2 * exp (-L ^ 2)) / (4 * αr) + (120 + 80 / sqrt αr))) := by ring
      _ ≤ tot * 1000 := mL hC_mul htot_pos.le
      _ = 1000 * tot := by ring
  have hsplit_tot :
      (∑ b ∈ B_set,
        ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ)) *
          ((b : ℝ) - a - ((t : ℝ) - j) / 3)) =
      (1 / 2) * (∑ b ∈ B_set,
        ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) -
          tot * Cnorm * exp (-αr * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2)) *
        (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr)) +
      (1 / 2) * (tot * Cnorm * ∑ b ∈ B_set,
        phiG αr (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr)) +
      shift * ∑ b ∈ B_set,
        ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ)) := by
    rw [mul_sum, mul_sum, mul_sum, mul_sum,
      ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun b hb => ?_
    rw [hhr_eq b hb]; dsimp [phiG]; ring
  rw [hsplit_tot]
  have htri := abs_add3_le
    ((1 / 2) * (∑ b ∈ B_set,
      ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) -
        tot * Cnorm * exp (-αr * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2)) *
      (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr)))
    ((1 / 2) * (tot * Cnorm * ∑ b ∈ B_set,
      phiG αr (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr)))
    (shift * ∑ b ∈ B_set,
      ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ)))
  have hp1 : |(1 / 2 : ℝ) * (∑ b ∈ B_set,
      ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) -
        tot * Cnorm * exp (-αr * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2)) *
      (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr))| ≤ 1.5e10 * L ^ 3 * tot := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h1 : |∑ b ∈ B_set,
        ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) -
          tot * Cnorm * exp (-αr * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2)) *
        (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr)| ≤ 3e10 * L ^ 3 * tot := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have heq : ∀ b ∈ B_set,
          |((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) -
            tot * Cnorm * exp (-αr * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2)) *
          (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr)| =
          |(D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) -
            tot * Cnorm * exp (-αr * (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr) ^ 2)| *
          |((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr| := fun b _ => abs_mul _ _
      rw [sum_congr rfl heq]; exact hsum_err
    linarith only [h1]
  have hp2 : |(1 / 2 : ℝ) * (tot * Cnorm * ∑ b ∈ B_set,
      phiG αr (((2 * (b - a - d1) + d2 : ℕ) : ℝ) - μr))| ≤ 500 * L ^ 3 * tot := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hL3 : (1 : ℝ) ≤ L ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hL10 3; linarith only [this]
    have h1 : 500 * tot ≤ 500 * L ^ 3 * tot := by
      have := mL hL3 (show 0 ≤ 500 * tot by positivity)
      linarith only [this]
    linarith only [hmain_odd, h1]
  have hp3 : |shift * ∑ b ∈ B_set,
      ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ))| ≤
      1300 * L ^ 3 * tot := by
    have hT_nn : 0 ≤ ∑ b ∈ B_set,
        ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ)) :=
      sum_nonneg fun _ _ => by positivity
    rw [abs_mul, abs_of_nonneg hT_nn]
    have hL23 : L ^ 2 ≤ L ^ 3 := by
      have := mL (by linarith only [hL10] : (1 : ℝ) ≤ L) (sq_nonneg L)
      linarith only [this]
    have h1 := mul_le_mul hshift_le hsum_T_le hT_nn (by positivity)
    have h2 := mR (mL hL23 (by norm_num : (0 : ℝ) ≤ 1300)) htot_pos.le
    linarith only [h1, h2]
  have hnn : 0 ≤ L ^ 3 * tot := by positivity
  linarith only [htri, hp1, hp2, hp3, hnn]

set_option maxHeartbeats 1600000 in
private lemma inner_b_sum_approx {k m f d1 d2 j t a : ℕ} (hV : ValidMF k m f)
    (hd1 : d1 ∈ ({0, 1} : Finset ℕ)) (hd2 : d2 ∈ ({0, 1} : Finset ℕ))
    (hjt : j + ⌊log k ^ 7⌋₊ < t) (htm : t < m)
    (hδj : |δ_coord m j| ≤ 40 * sqrt k * log k)
    (hδt : |δ_coord m t| ≤ 40 * sqrt k * log k)
    (hεj : |ε_coord m f j a| ≤ 10 * sqrt k * log k) :
    let L : ℝ := log k
    let D : ℕ := t - j - 1
    let M2 : ℕ := m - t
    let S2 : ℕ := 2 * (f - a - d1) + 1 - d2
    let y : ℝ := δ_coord m t - ε_coord m f j a
    let B_set : Finset ℕ := (range (f + 1)).filter
      (fun b => a + d1 ≤ b ∧ b + d2 ≤ f ∧
        |(b : ℝ) - a - ((t : ℝ) - j) / 3| ≤ 20 * sqrt D * L)
    |∑ b ∈ B_set,
      ((D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ)) *
        deltaK k b (f - b - d2) t (m - 1 - t) -
      (1 / 2) * (((D + M2).choose S2 : ℕ) : ℝ) *
        ((-18 / (k : ℝ)) * cK_val k m f d2 * phiG (αk_val k) y)| ≤
      (((D + M2).choose S2 : ℕ) : ℝ) * cK_val k m f d2 *
        ((2e14 * L ^ 4 / (k : ℝ)) * exp (-αk_val k * y ^ 2 / 2) +
         (2e7 * L ^ 2 / ((k : ℝ) * (D : ℝ))) * |phiG (αk_val k) y|) := by
  intro L D M2 S2 y B_set
  have hba := validMF_eta_bounds hV
  have hsqL := validMF_sqL_le hV
  have ⟨hD_lb, hD_ge100, hD_hi, hM2_lo, hD_le_M2, hDM_eq, hDM_lo, ha_eq, ha_le_f, hη_diff, hη_lo, hη_hi⟩ :=
    box_eta2_bounds hV hd1 hd2 hjt htm hδj hδt hεj
  have ⟨hk, hL, _, hexpL, _, _⟩ := hV
  change 10 ^ 20 ≤ L at hL
  change (k : ℝ) ^ 10 * exp (-L ^ 2) ≤ 1 at hexpL
  change sqrt k * L ≤ (k : ℝ) / 10 ^ 6 at hsqL
  change |δ_coord m j| ≤ 40 * sqrt k * L at hδj
  change |δ_coord m t| ≤ 40 * sqrt k * L at hδt
  change |ε_coord m f j a| ≤ 10 * sqrt k * L at hεj
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hL10 : (10 : ℝ) ≤ L := by linarith only [hL]
  have hd1_le1 : d1 ≤ 1 := by simp only [mem_insert, mem_singleton] at hd1; rcases hd1 with rfl | rfl <;> omega
  have hd2_le1 : d2 ≤ 1 := by simp only [mem_insert, mem_singleton] at hd2; rcases hd2 with rfl | rfl <;> omega
  have hd1R : (d1 : ℝ) ≤ 1 := by exact_mod_cast hd1_le1
  have hd2R : (d2 : ℝ) ≤ 1 := by exact_mod_cast hd2_le1
  let tot : ℝ := (((D + M2).choose S2 : ℕ) : ℝ)
  let cK2 : ℝ := cK_val k m f d2
  let α : ℝ := αk_val k
  have hcK2_pos : 0 < cK2 := (cK_cM_bounds hV hd2).1
  have hα_pos : 0 < α := by dsimp [α, αk_val]; positivity
  have hD_pos : (0 : ℝ) < D := by linarith only [hD_ge100]
  have hsqD_pos : 0 < sqrt D := sqrt_pos.mpr hD_pos
  have hDM_pos : 0 < (D : ℝ) + M2 := by linarith only [hDM_lo, hk_pos]
  have htot_nn : 0 ≤ tot := Nat.cast_nonneg _
  have hsum_T_le : ∑ b ∈ B_set,
      (D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ) ≤ tot :=
    sum_B_set_le_tot D M2 f a d1 d2 B_set (fun b hb => ⟨(mem_filter.mp hb).2.1, (mem_filter.mp hb).2.2.1⟩)
  have hy_abs : |y| ≤ 60 * sqrt k * L := by
    dsimp [y]
    have hnn : 0 ≤ sqrt k * L := by positivity
    exact (abs_sub (δ_coord m t) (ε_coord m f j a)).trans (by linarith only [hδt, hεj, hnn])
  have h20D_le : 20 * sqrt D * L ≤ 10 * sqrt k * L := by
    have hD_le_k4 : (D : ℝ) ≤ (k : ℝ) / 4 := by linarith only [hD_hi, hsqL, hk_pos]
    have h1 : sqrt D ≤ sqrt k / 2 := by
      have hsq4 : sqrt ((k : ℝ) / 4) = sqrt k / 2 := by
        rw [sqrt_div hk_pos.le, show sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      rw [← hsq4]; exact sqrt_le_sqrt hD_le_k4
    have hmul := mR h1 (by linarith only [hL10] : 0 ≤ L)
    linarith only [hmul]
  let T (b : ℕ) : ℝ := (D.choose (2 * (b - a - d1) + d2) : ℝ) * (M2.choose (2 * (f - b - d2) + 1) : ℝ)
  let hb_fn (b : ℕ) : ℝ := (b : ℝ) - a - ((t : ℝ) - j) / 3
  have hPartA : |∑ b ∈ B_set, T b * (deltaK k b (f - b - d2) t (m - 1 - t) -
      (-18 / (k : ℝ)) * cK2 * phiG α (y - hb_fn b))| ≤
      tot * cK2 * ((4e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hpt : ∀ b ∈ B_set,
        |T b * (deltaK k b (f - b - d2) t (m - 1 - t) -
          (-18 / (k : ℝ)) * cK2 * phiG α (y - hb_fn b))| ≤
        T b * (cK2 * ((4e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2))) := by
      intro b hb
      have hb' := (mem_filter.mp hb).2
      have hεt_eq : ε_coord m f t b = ε_coord m f j a + hb_fn b := by
        dsimp [ε_coord, hb_fn]; ring
      have hεt_box : |ε_coord m f t b| ≤ 20 * sqrt k * L := by
        rw [hεt_eq]
        exact (abs_add_le _ _).trans (by linarith only [hεj, hb'.2.2, h20D_le])
      have hyt_eq : δ_coord m t - ε_coord m f t b = y - hb_fn b := by
        rw [hεt_eq]; dsimp [y]; ring
      have hdk := (deltaK_gaussian_approx hV hd2 hδt hεt_box).2
      rw [hyt_eq] at hdk
      have hhh2 : (hb_fn b) ^ 2 ≤ 32000 * sqrt k * L ^ 3 := by
        have h1 := pow_le_pow_left₀ (abs_nonneg (hb_fn b)) hb'.2.2 2
        rw [sq_abs, mul_pow, mul_pow, sq_sqrt hD_pos.le] at h1
        have h2 := mR hD_hi (show 0 ≤ 400 * L ^ 2 by positivity)
        have heq1 : (20 : ℝ) ^ 2 * (D : ℝ) * L ^ 2 = (D : ℝ) * (400 * L ^ 2) := by ring
        have heq2 : (80 * sqrt k * L) * (400 * L ^ 2) = 32000 * sqrt k * L ^ 3 := by ring
        linarith only [h1, h2, heq1, heq2]
      have hexp2 := (phiG_taylor_h_approx hV hy_abs hhh2).2
      have hexp_half : exp (-α * y ^ 2) ≤ exp (-α * y ^ 2 / 2) :=
        exp_le_exp.mpr (by nlinarith only [hα_pos, sq_nonneg y])
      rw [abs_mul, abs_of_nonneg (by dsimp [T]; positivity)]
      apply mL _ (by dsimp [T]; positivity)
      calc |deltaK k b (f - b - d2) t (m - 1 - t) - (-18 / (k : ℝ)) * cK2 * phiG α (y - hb_fn b)|
          ≤ (2e13 : ℝ) * (L ^ 4 / (k : ℝ)) * (cK2 * exp (-α * (y - hb_fn b) ^ 2)) := hdk
        _ ≤ (2e13 : ℝ) * (L ^ 4 / (k : ℝ)) * (cK2 * (2 * exp (-α * y ^ 2))) :=
            mL (mL hexp2 hcK2_pos.le) (by positivity)
        _ ≤ (2e13 : ℝ) * (L ^ 4 / (k : ℝ)) * (cK2 * (2 * exp (-α * y ^ 2 / 2))) :=
            mL
              (mL (mL hexp_half (by norm_num)) hcK2_pos.le)
              (by positivity)
        _ = cK2 * ((4e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by ring
    calc ∑ b ∈ B_set, |T b * (deltaK k b (f - b - d2) t (m - 1 - t) -
            (-18 / (k : ℝ)) * cK2 * phiG α (y - hb_fn b))|
        ≤ ∑ b ∈ B_set, T b * (cK2 * ((4e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2))) :=
          sum_le_sum hpt
      _ = (∑ b ∈ B_set, T b) * (cK2 * ((4e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2))) :=
          (sum_mul _ _ _).symm
      _ ≤ tot * (cK2 * ((4e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2))) :=
          mR hsum_T_le (by positivity)
      _ = tot * cK2 * ((4e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by ring
  have hPartB : |(-18 / (k : ℝ)) * cK2 * ∑ b ∈ B_set, T b *
      (phiG α (y - hb_fn b) -
        (phiG α y + ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) * hb_fn b))| ≤
      tot * cK2 * ((1e9 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by
    rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 18),
      abs_of_pos hk_pos, abs_of_pos hcK2_pos]
    have hsum_le : |∑ b ∈ B_set, T b * (phiG α (y - hb_fn b) -
        (phiG α y + ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) * hb_fn b))| ≤
        tot * (2e7 * L ^ 3 * exp (-α * y ^ 2 / 2)) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ b ∈ B_set, |T b * (phiG α (y - hb_fn b) -
              (phiG α y + ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) * hb_fn b))|
          ≤ ∑ b ∈ B_set, T b * (2e7 * L ^ 3 * exp (-α * y ^ 2 / 2)) := by
            apply sum_le_sum; intro b hb
            have hb' := (mem_filter.mp hb).2
            have hhh2 : (hb_fn b) ^ 2 ≤ 32000 * sqrt k * L ^ 3 := by
              have h1 := pow_le_pow_left₀ (abs_nonneg (hb_fn b)) hb'.2.2 2
              rw [sq_abs, mul_pow, mul_pow, sq_sqrt hD_pos.le] at h1
              have h2 := mR hD_hi (show 0 ≤ 400 * L ^ 2 by positivity)
              have heq1 : (20 : ℝ) ^ 2 * (D : ℝ) * L ^ 2 = (D : ℝ) * (400 * L ^ 2) := by ring
              have heq2 : (80 * sqrt k * L) * (400 * L ^ 2) = 32000 * sqrt k * L ^ 3 := by ring
              linarith only [h1, h2, heq1, heq2]
            rw [abs_mul, abs_of_nonneg (by dsimp [T]; positivity)]
            exact mL (phiG_taylor_h_approx hV hy_abs hhh2).1 (by dsimp [T]; positivity)
        _ = (∑ b ∈ B_set, T b) * (2e7 * L ^ 3 * exp (-α * y ^ 2 / 2)) := (sum_mul _ _ _).symm
        _ ≤ tot * (2e7 * L ^ 3 * exp (-α * y ^ 2 / 2)) :=
            mR hsum_T_le (by positivity)
    have hL34 : L ^ 3 ≤ L ^ 4 := by
      have := mL (by linarith only [hL10] : (1 : ℝ) ≤ L)
        (pow_nonneg (by linarith only [hL10]) 3)
      linarith only [this]
    calc 18 / (k : ℝ) * cK2 * |∑ b ∈ B_set, T b * (phiG α (y - hb_fn b) -
            (phiG α y + ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) * hb_fn b))|
        ≤ 18 / (k : ℝ) * cK2 * (tot * (2e7 * L ^ 3 * exp (-α * y ^ 2 / 2))) :=
          mL hsum_le (by positivity)
      _ = tot * cK2 * ((3.6e8 * L ^ 3 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by ring
      _ ≤ tot * cK2 * ((1e9 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by
          apply mL _ (by positivity)
          apply mR _ (exp_pos _).le
          apply dR _ hk_pos.le
          have hnn : 0 ≤ L ^ 4 := pow_nonneg (by linarith only [hL10]) 4
          linarith only [hL34, hnn]
  have hPartC : |(-18 / (k : ℝ)) * cK2 * ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) *
      ∑ b ∈ B_set, T b * hb_fn b| ≤
      tot * cK2 * ((1e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 18),
      abs_of_pos hk_pos, abs_of_pos hcK2_pos]
    have hder : |(2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)| ≤ 5 * exp (-α * y ^ 2 / 2) := by
      have heq : (2 * α * y ^ 2 - 1) * exp (-α * y ^ 2) = -((1 - 2 * α * y ^ 2) * exp (-α * y ^ 2)) := by ring
      rw [heq, abs_neg]; exact abs_deriv_phiG_le α y hα_pos
    have hmom := hypergeom_odd_moment_bound hV hd1 hd2 hjt htm hδj hδt hεj
    have hL34 : L ^ 3 ≤ L ^ 4 := by
      have := mL (by linarith only [hL10] : (1 : ℝ) ≤ L)
        (pow_nonneg (by linarith only [hL10]) 3)
      linarith only [this]
    calc 18 / (k : ℝ) * cK2 * |(2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)| *
          |∑ b ∈ B_set, T b * hb_fn b|
        ≤ 18 / (k : ℝ) * cK2 * (5 * exp (-α * y ^ 2 / 2)) * (1e11 * L ^ 3 * tot) :=
          mul_le_mul (mL hder (by positivity)) hmom (abs_nonneg _) (by positivity)
      _ = tot * cK2 * ((9e12 * L ^ 3 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by ring
      _ ≤ tot * cK2 * ((1e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by
          apply mL _ (by positivity)
          apply mR _ (exp_pos _).le
          apply dR _ hk_pos.le
          have hnn : 0 ≤ L ^ 4 := pow_nonneg (by linarith only [hL10]) 4
          linarith only [hL34, hnn]
  have hPartD : |(-18 / (k : ℝ)) * cK2 * phiG α y * ((∑ b ∈ B_set, T b) - (1 / 2) * tot)| ≤
      tot * cK2 * ((2e7 * L ^ 2 / ((k : ℝ) * (D : ℝ))) * |phiG α y|) := by
    let R_par : Finset ℕ := (range (D + 1)).filter (fun r => r % 2 = d2)
    have hD_nat : 100 ≤ D := by exact_mod_cast hD_ge100
    have hDM_nat : D ≤ M2 := by exact_mod_cast hD_le_M2
    have hS2_nat : S2 ≤ D + M2 := by
      have h1 : (S2 : ℝ) ≤ (7 / 10 : ℝ) * ((D : ℝ) + M2) := by
        have := (div_le_iff₀ hDM_pos).mp hη_hi; linarith only [this]
      have : (S2 : ℝ) ≤ ((D + M2 : ℕ) : ℝ) := by push_cast; linarith only [h1, hDM_pos]
      exact_mod_cast this
    have hW40 : 40 * sqrt D * L ≤ (D : ℝ) / 40 := by
      have h1 : 1600 * L ≤ sqrt D := by
        rw [le_sqrt (by positivity) hD_pos.le]
        have hL5 : (10 ^ 8 : ℝ) * L ^ 2 ≤ L ^ 7 := by
          have hp : (10 ^ 2 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith only [hL]) 5
          have hm := mR hp (sq_nonneg L)
          rw [← pow_add, show (5 + 2 : ℕ) = 7 by norm_num,
            show ((10 ^ 2 : ℝ) ^ 5) = 10 ^ 10 by norm_num] at hm
          have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
          linarith only [hm, hL2nn]
        have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
        rw [mul_pow]; linarith only [hD_lb, hL5, hL2nn]
      have hmul := mL h1 hsqD_pos.le
      rw [mul_self_sqrt hD_pos.le] at hmul
      linarith only [hmul]
    have hW10 : 10 * sqrt D * L ≤ (D : ℝ) / 10 := by
      have hnn : 0 ≤ sqrt D * L := by positivity
      linarith only [hW40, hnn, hD_pos]
    have htail_D : ((D + 3 : ℕ) : ℝ) * exp (-9 * L ^ 2) ≤ 1 / (D : ℝ) := by
      rw [le_div_iff₀ hD_pos]
      have hexp9 : exp (-9 * L ^ 2) ≤ exp (-L ^ 2) :=
        exp_le_exp.mpr (by nlinarith only [sq_nonneg L])
      have hD2 : ((D + 3 : ℕ) : ℝ) * (D : ℝ) ≤ (k : ℝ) ^ 10 := by
        have hDk : (D : ℝ) ≤ k := by linarith only [hD_hi, hsqL, hk_pos]
        have hD3k : ((D + 3 : ℕ) : ℝ) ≤ 2 * k := by push_cast; linarith only [hDk, hkR]
        have hmul := mul_le_mul hD3k hDk hD_pos.le (by positivity)
        have hk2 : 2 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 10 := by
          have h1 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 9 := pow_le_pow_right₀ (by linarith only [hkR]) (by omega)
          have h2 : 2 * (k : ℝ) ^ 9 ≤ (k : ℝ) ^ 10 := by
            rw [show (k : ℝ) ^ 10 = (k : ℝ) * (k : ℝ) ^ 9 by ring]
            exact mR (by linarith only [hkR]) (pow_nonneg hk_pos.le 9)
          linarith only [h1, h2]
        linarith only [hmul, hk2]
      have h1 := mul_le_mul hD2 hexp9 (exp_pos _).le (pow_nonneg hk_pos.le 10)
      linarith only [h1, hexpL]
    have hlem5 := lemma5_parity_sum D M2 S2 d2 hD_nat hDM_nat hS2_nat hd2
      (by linarith only [hL10]) hW10
      (by have := (le_div_iff₀ hDM_pos).mp hη_lo; linarith only [this, hDM_pos])
      (by have := (div_le_iff₀ hDM_pos).mp hη_hi; linarith only [this, hDM_pos])
      htail_D
    let g : ℕ → ℕ := fun b => 2 * (b - a - d1) + d2
    have hinj : ∀ b1 ∈ B_set, ∀ b2 ∈ B_set, g b1 = g b2 → b1 = b2 := by
      intro b1 h1 b2 h2 heq
      have ha1 := (mem_filter.mp h1).2.1; have ha2 := (mem_filter.mp h2).2.1
      dsimp [g] at heq; omega
    have hsub_R : B_set.image g ⊆ R_par := by
      intro r hr
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hr
      have hb' := (mem_filter.mp hb).2
      have hmod : g b % 2 = d2 := by
        dsimp [g]; simp only [mem_insert, mem_singleton] at hd2; rcases hd2 with rfl | rfl <;> omega
      have hle_D : g b ≤ D := by
        have hsub : b - a - d1 = b - (a + d1) := by omega
        have hD_cast : (D : ℝ) = (t : ℝ) - j - 1 := by
          have : D + j + 1 = t := by dsimp [D]; omega
          have hR : ((D + j + 1 : ℕ) : ℝ) = t := by exact_mod_cast this
          push_cast at hR; linarith only [hR]
        have hgR : (g b : ℝ) = 2 * hb_fn b + (2 / 3) * D + (2 / 3 - 2 * (d1 : ℝ) + d2) := by
          dsimp [g, hb_fn]
          rw [hsub, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_sub hb'.1, Nat.cast_add, hD_cast]; ring
        have hleR : (g b : ℝ) ≤ D := by
          have h40 : 2 * (20 * sqrt D * L) = 40 * sqrt D * L := by ring
          have hb_le : hb_fn b ≤ 20 * sqrt D * L := (abs_le.mp hb'.2.2).2
          have hD100 : (100 : ℝ) ≤ D := hD_ge100
          linarith only [hgR, hb_le, hW40, h40, hd1R, hd2R, Nat.cast_nonneg (α := ℝ) d1,
            Nat.cast_nonneg (α := ℝ) d2, hD100]
        exact_mod_cast hleR
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), hmod⟩
    have heq_img : ∑ b ∈ B_set, T b =
        ∑ r ∈ B_set.image g, (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ) := by
      rw [sum_image hinj]
      refine sum_congr rfl fun b hb => ?_
      have hb' := (mem_filter.mp hb).2
      dsimp [T]; rw [show S2 - g b = 2 * (f - b - d2) + 1 by dsimp [S2, g]; omega]
    have hdiff_tail : |(∑ r ∈ R_par, (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ)) -
        ∑ b ∈ B_set, T b| ≤ (2 / (D : ℝ)) * tot := by
      rw [heq_img, ← sum_sdiff hsub_R, add_sub_cancel_right,
        abs_of_nonneg (sum_nonneg fun _ _ => by positivity)]
      let μr : ℝ := (D : ℝ) * (S2 : ℝ) / ((D : ℝ) + M2)
      have hpt_sdiff : ∀ r ∈ R_par \ B_set.image g,
          (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ) ≤ 2 * tot * exp (-9 * L ^ 2) := by
        intro r hr
        have hr_in := (mem_sdiff.mp hr).1
        have hr_not := (mem_sdiff.mp hr).2
        have hr_lt : r < D + 1 := mem_range.mp (mem_filter.mp hr_in).1
        have hr_mod : r % 2 = d2 := (mem_filter.mp hr_in).2
        have hr_le_S2 : r ≤ S2 := by
          have h1 : (D : ℝ) ≤ S2 := by
            have := (le_div_iff₀ hDM_pos).mp hη_lo; linarith only [this, hD_le_M2, hD_pos]
          have : D ≤ S2 := by exact_mod_cast h1
          omega
        have hd2_le_r : d2 ≤ r := by
          simp only [mem_insert, mem_singleton] at hd2; rcases hd2 with rfl | rfl <;> omega
        let b0 : ℕ := a + d1 + (r - d2) / 2
        have hg_b0 : g b0 = r := by dsimp [g, b0]; omega
        have hb0_le_f : b0 + d2 ≤ f := by
          have h1 : (b0 : ℝ) + d2 ≤ (f : ℝ) := by
            have hb0R : (b0 : ℝ) ≤ (a : ℝ) + 1 + (D : ℝ) / 2 := by
              have hnat : 2 * b0 ≤ 2 * a + 2 * d1 + r := by dsimp [b0]; omega
              have hR : (2 : ℝ) * b0 ≤ 2 * a + 2 * d1 + r := by exact_mod_cast hnat
              have hrD : (r : ℝ) ≤ D := by exact_mod_cast (show r ≤ D by omega)
              linarith only [hR, hd1R, hrD]
            linarith only [hb0R, ha_eq, (abs_le.mp hδj).2, (abs_le.mp hεj).2, hD_hi,
              hba.2.2.1, hsqL, hkR, hd2R]
          exact_mod_cast h1
        have hh_gt : 20 * sqrt D * L < |hb_fn b0| := by
          by_contra hle; push Not at hle
          apply hr_not
          refine mem_image.mpr ⟨b0, mem_filter.mpr ⟨mem_range.mpr (by omega), by dsimp [b0]; omega, hb0_le_f, hle⟩, hg_b0⟩
        have hdist_r : 30 * sqrt D * L ≤ |(r : ℝ) - μr| := by
          have hD_cast : (D : ℝ) = (t : ℝ) - j - 1 := by
            have : D + j + 1 = t := by dsimp [D]; omega
            have hR : ((D + j + 1 : ℕ) : ℝ) = t := by exact_mod_cast this
            push_cast at hR; linarith only [hR]
          have hr_eq : (r : ℝ) = 2 * hb_fn b0 + (2 / 3) * D + (2 / 3 - 2 * (d1 : ℝ) + d2) := by
            have hr_nat : r + 2 * a + 2 * d1 = 2 * b0 + d2 := by dsimp [b0]; omega
            have hr_R : ((r + 2 * a + 2 * d1 : ℕ) : ℝ) = ((2 * b0 + d2 : ℕ) : ℝ) := by exact_mod_cast hr_nat
            push_cast at hr_R
            dsimp [hb_fn]; linarith only [hr_R, hD_cast]
          have hdiff_eq : (r : ℝ) - μr = 2 * hb_fn b0 - (D : ℝ) * ((S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3) +
              (2 / 3 - 2 * (d1 : ℝ) + d2) := by
            rw [hr_eq]; dsimp [μr]; ring
          have hDη : |(D : ℝ) * ((S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3)| ≤ 2400 * L ^ 2 := by
            rw [abs_mul, abs_of_pos hD_pos]
            have hmul := mul_le_mul hD_hi hη_diff (abs_nonneg _) (by positivity)
            have hsimp : (80 * sqrt k * L) * (30 * L / sqrt k) = 2400 * L ^ 2 := by
              field_simp [hsq_pos.ne']; ring
            linarith only [hmul, hsimp]
          have hconst : |2 / 3 - 2 * (d1 : ℝ) + d2| ≤ 4 := by
            rw [abs_le]; constructor <;>
              linarith only [Nat.cast_nonneg (α := ℝ) d1, Nat.cast_nonneg (α := ℝ) d2, hd1R, hd2R]
          have h2404 : 2400 * L ^ 2 + 4 ≤ 10 * sqrt D * L := by
            have hsq : (250 * L) ^ 2 ≤ (D : ℝ) := by
              have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
              have hL5_big : (10 ^ 6 : ℝ) * L ^ 2 ≤ L ^ 7 := by
                have h1' : (10 ^ 2 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith only [hL]) 5
                have h2' := mR h1' hL2nn
                rw [← pow_add, show (5 + 2 : ℕ) = 7 by norm_num,
                  show ((10 ^ 2 : ℝ) ^ 5) = 10 ^ 10 by norm_num] at h2'
                linarith only [h2', hL2nn]
              rw [show (250 * L) ^ 2 = 62500 * L ^ 2 by ring]; linarith only [hD_lb, hL5_big, hL2nn]
            have h1' : 250 * L ≤ sqrt D := by rw [le_sqrt (by positivity) hD_pos.le]; exact hsq
            have h2' := mR h1' (by linarith only [hL10] : 0 ≤ L)
            have hL2 : (100 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
            linarith only [h2', hL2]
          have htri : |2 * hb_fn b0| ≤ |(r : ℝ) - μr| +
              |(D : ℝ) * ((S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3)| + |2 / 3 - 2 * (d1 : ℝ) + d2| := by
            have h1 : 2 * hb_fn b0 = ((r : ℝ) - μr) + (D : ℝ) * ((S2 : ℝ) / ((D : ℝ) + M2) - 2 / 3) -
                (2 / 3 - 2 * (d1 : ℝ) + d2) := by linarith only [hdiff_eq]
            rw [h1]; exact abs_add_sub_le _ _ _
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
          linarith only [htri, hh_gt, hDη, hconst, h2404]
        have hut := hypergeom_universal_tail D M2 S2 r (by omega) hr_le_S2
        have hexp : exp (-((r : ℝ) - μr) ^ 2 / (8 * (D : ℝ))) ≤ exp (-9 * L ^ 2) := by
          apply exp_le_exp.mpr
          have hsq : (30 * sqrt D * L) ^ 2 ≤ ((r : ℝ) - μr) ^ 2 := by
            rw [← sq_abs ((r : ℝ) - μr)]; exact pow_le_pow_left₀ (by positivity) hdist_r 2
          have h900 : (30 * sqrt D * L) ^ 2 = 900 * (D : ℝ) * L ^ 2 := by
            rw [mul_pow, mul_pow, sq_sqrt hD_pos.le]; ring
          rw [show (-9 : ℝ) * L ^ 2 = -(9 * L ^ 2) by ring, neg_div, neg_le_neg_iff,
            le_div_iff₀ (by positivity : (0 : ℝ) < 8 * D)]
          have hnn : 0 ≤ (D : ℝ) * L ^ 2 := by positivity
          linarith only [hsq, h900, hnn]
        exact hut.trans (mL hexp (by positivity))
      calc ∑ r ∈ R_par \ B_set.image g, (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ)
          ≤ ∑ _r ∈ R_par \ B_set.image g, (2 * tot * exp (-9 * L ^ 2)) :=
            sum_le_sum hpt_sdiff
        _ = ((R_par \ B_set.image g).card : ℝ) * (2 * tot * exp (-9 * L ^ 2)) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ((D + 3 : ℕ) : ℝ) * (2 * tot * exp (-9 * L ^ 2)) := by
            have hc : (R_par \ B_set.image g).card ≤ D + 3 :=
              (card_le_card sdiff_subset).trans
                ((card_filter_le _ _).trans (by simp))
            have hcR : ((R_par \ B_set.image g).card : ℝ) ≤ (D + 3 : ℕ) := by exact_mod_cast hc
            exact mR hcR (by positivity)
        _ = 2 * (((D + 3 : ℕ) : ℝ) * exp (-9 * L ^ 2)) * tot := by ring
        _ ≤ 2 * (1 / (D : ℝ)) * tot :=
            mR (mL htail_D (by norm_num)) htot_nn
        _ = (2 / (D : ℝ)) * tot := by ring
    have hpar_tot : |(∑ b ∈ B_set, T b) - (1 / 2) * tot| ≤ (1.1e6 * L ^ 2 / (D : ℝ)) * tot := by
      have htri : |(∑ b ∈ B_set, T b) - (1 / 2) * tot| ≤
          |(∑ r ∈ R_par, (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ)) - (1 / 2) * tot| +
          |(∑ r ∈ R_par, (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ)) - ∑ b ∈ B_set, T b| := by
        have h1 : (∑ b ∈ B_set, T b) - (1 / 2) * tot =
            ((∑ r ∈ R_par, (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ)) - (1 / 2) * tot) -
            ((∑ r ∈ R_par, (D.choose r : ℝ) * (M2.choose (S2 - r) : ℝ)) - ∑ b ∈ B_set, T b) := by ring
        rw [h1]; exact abs_sub _ _
      have h2D : 2 / (D : ℝ) ≤ 100000 * L ^ 2 / (D : ℝ) := by
        apply dR _ hD_pos.le
        have : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hL10]
        linarith only [this]
      have hmul := mR h2D htot_nn
      have hadd : (1000000 * L ^ 2 / (D : ℝ)) * tot + (100000 * L ^ 2 / (D : ℝ)) * tot =
          (1.1e6 * L ^ 2 / (D : ℝ)) * tot := by ring
      linarith only [htri, hlem5, hdiff_tail, hmul, hadd]
    rw [abs_mul, abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 18),
      abs_of_pos hk_pos, abs_of_pos hcK2_pos]
    calc 18 / (k : ℝ) * cK2 * |phiG α y| * |(∑ b ∈ B_set, T b) - (1 / 2) * tot|
        ≤ 18 / (k : ℝ) * cK2 * |phiG α y| * ((1.1e6 * L ^ 2 / (D : ℝ)) * tot) :=
          mL hpar_tot (by positivity)
      _ = tot * cK2 * ((1.98e7 * L ^ 2 / ((k : ℝ) * (D : ℝ))) * |phiG α y|) := by ring
      _ ≤ tot * cK2 * ((2e7 * L ^ 2 / ((k : ℝ) * (D : ℝ))) * |phiG α y|) := by
          apply mL _ (by positivity)
          apply mR _ (abs_nonneg _)
          apply dR _ (by positivity)
          have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
          linarith only [hL2nn]
  have hsplit_all :
      (∑ b ∈ B_set, T b * deltaK k b (f - b - d2) t (m - 1 - t)) -
        (1 / 2) * tot * ((-18 / (k : ℝ)) * cK2 * phiG α y) =
      (∑ b ∈ B_set, T b * (deltaK k b (f - b - d2) t (m - 1 - t) -
        (-18 / (k : ℝ)) * cK2 * phiG α (y - hb_fn b))) +
      ((-18 / (k : ℝ)) * cK2 * ∑ b ∈ B_set, T b * (phiG α (y - hb_fn b) -
        (phiG α y + ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) * hb_fn b))) +
      ((-18 / (k : ℝ)) * cK2 * ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) *
        ∑ b ∈ B_set, T b * hb_fn b) +
      ((-18 / (k : ℝ)) * cK2 * phiG α y * ((∑ b ∈ B_set, T b) - (1 / 2) * tot)) := by
    rw [mul_sum, mul_sum, mul_sub, mul_sum]
    have h1 : ∀ (s : Finset ℕ) (f1 f2 f3 f4 : ℕ → ℝ) (c : ℝ),
        (∑ b ∈ s, f1 b) + (∑ b ∈ s, f2 b) + (∑ b ∈ s, f3 b) + ((∑ b ∈ s, f4 b) - c) =
        (∑ b ∈ s, (f1 b + f2 b + f3 b + f4 b)) - c := by
      intro s f1 f2 f3 f4 c
      simp only [sum_add_distrib]; ring
    rw [h1]
    have hsum_eq : ∑ b ∈ B_set, (T b * (deltaK k b (f - b - d2) t (m - 1 - t) -
        (-18 / (k : ℝ)) * cK2 * phiG α (y - hb_fn b)) +
        (-18 / (k : ℝ)) * cK2 * (T b * (phiG α (y - hb_fn b) -
          (phiG α y + ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) * hb_fn b))) +
        (-18 / (k : ℝ)) * cK2 * ((2 * α * y ^ 2 - 1) * exp (-α * y ^ 2)) * (T b * hb_fn b) +
        (-18 / (k : ℝ)) * cK2 * phiG α y * T b) =
        ∑ b ∈ B_set, T b * deltaK k b (f - b - d2) t (m - 1 - t) :=
      sum_congr rfl fun b _ => by ring
    rw [hsum_eq]; ring
  change |(∑ b ∈ B_set, T b * deltaK k b (f - b - d2) t (m - 1 - t)) -
      (1 / 2) * tot * ((-18 / (k : ℝ)) * cK2 * phiG α y)| ≤ _
  rw [hsplit_all]
  have htri4 : ∀ p q r s : ℝ, |p + q + r + s| ≤ |p| + |q| + |r| + |s| := fun p q r s =>
    (abs_add_le (p + q + r) s).trans (add_le_add (abs_add3_le p q r) le_rfl)
  have hcomb := (htri4 _ _ _ _).trans (add_le_add (add_le_add (add_le_add hPartA hPartB) hPartC) hPartD)
  have hfinal :
      tot * cK2 * ((4e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) +
      tot * cK2 * ((1e9 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) +
      tot * cK2 * ((1e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) +
      tot * cK2 * ((2e7 * L ^ 2 / ((k : ℝ) * (D : ℝ))) * |phiG α y|) ≤
      tot * cK2 *
        ((2e14 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2) +
         (2e7 * L ^ 2 / ((k : ℝ) * (D : ℝ))) * |phiG α y|) := by
    have hnn : 0 ≤ tot * cK2 * (L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2) := by positivity
    have heq1 : tot * cK2 * ((4e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) =
        4e13 * (tot * cK2 * (L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by ring
    have heq2 : tot * cK2 * ((1e9 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) =
        1e9 * (tot * cK2 * (L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by ring
    have heq3 : tot * cK2 * ((1e13 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) =
        1e13 * (tot * cK2 * (L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) := by ring
    have heq4 : tot * cK2 * ((2e14 * L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2) +
          (2e7 * L ^ 2 / ((k : ℝ) * (D : ℝ))) * |phiG α y|) =
        2e14 * (tot * cK2 * (L ^ 4 / (k : ℝ)) * exp (-α * y ^ 2 / 2)) +
        tot * cK2 * ((2e7 * L ^ 2 / ((k : ℝ) * (D : ℝ))) * |phiG α y|) := by ring
    linarith only [hnn, heq1, heq2, heq3, heq4]
  exact hcomb.trans hfinal

private lemma harmonic_sum_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ i ∈ range N, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ≤ 1 + log (N : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hN
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, sum_range_succ]
    have hpos1 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hpos2 : (0 : ℝ) < (m + 1 + 1 : ℕ) := by positivity
    have hstep : (1 : ℝ) / ((m + 1 + 1 : ℕ) : ℝ) ≤
        log ((m + 1 + 1 : ℕ) : ℝ) - log ((m + 1 : ℕ) : ℝ) := by
      have h1 := one_sub_inv_le_log_of_pos (div_pos hpos2 hpos1)
      rw [log_div hpos2.ne' hpos1.ne', inv_div] at h1
      have h2 : 1 - ((m + 1 : ℕ) : ℝ) / ((m + 1 + 1 : ℕ) : ℝ) =
          (1 : ℝ) / ((m + 1 + 1 : ℕ) : ℝ) := by
        push_cast; field_simp [show (m : ℝ) + 1 + 1 ≠ 0 by positivity]; ring
      linarith only [h1, h2]
    linarith only [ih (by omega), hstep]

set_option maxHeartbeats 1600000 in
private lemma regime2_in_box_bound {k m f d1 d2 : ℕ} (hV : ValidMF k m f)
    (hd1 : d1 ∈ ({0, 1} : Finset ℕ)) (hd2 : d2 ∈ ({0, 1} : Finset ℕ)) :
    let L : ℝ := log k
    let D0 : ℕ := ⌊L ^ 7⌋₊
    let J_box : Finset ℕ := (range m).filter (fun j => 1 ≤ j ∧ |δ_coord m j| ≤ 40 * sqrt k * L)
    let A_box (j : ℕ) : Finset ℕ := (range (f + 1)).filter (fun a => |ε_coord m f j a| ≤ 10 * sqrt k * L)
    let T_box (j : ℕ) : Finset ℕ := (range m).filter (fun t => j + D0 < t ∧ |δ_coord m t| ≤ 40 * sqrt k * L)
    let B_box (j t a : ℕ) : Finset ℕ := (range (f + 1)).filter
      (fun b => a + d1 ≤ b ∧ b + d2 ≤ f ∧
        |(b : ℝ) - a - ((t : ℝ) - j) / 3| ≤ 20 * sqrt ((t - j - 1 : ℕ) : ℝ) * L)
    |∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, ∑ b ∈ B_box j t a,
      ((j.choose (2 * a + d1) * (t - j - 1).choose (2 * (b - a - d1) + d2) *
        (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) *
      deltaK k a (f - a - d1) j (m - 1 - j) *
      deltaK k b (f - b - d2) t (m - 1 - t)| ≤
      (1e24 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) *
        (((m + 1).choose (2 * f + 1) : ℕ) : ℝ) *
        (((2 * k + 1 + f).choose m : ℕ) : ℝ) ^ 2 := by
  intro L D0 J_box A_box T_box B_box
  have hba := validMF_eta_bounds hV
  have hsqL := validMF_sqL_le hV
  have ⟨hk, hL, hL15, hexpL, hm_box, hf_box⟩ := hV
  change 10 ^ 20 ≤ L at hL
  change L ^ 15 / sqrt k ≤ 1 / 10 ^ 6 at hL15
  change (k : ℝ) ^ 10 * exp (-L ^ 2) ≤ 1 at hexpL
  change sqrt k * L ≤ (k : ℝ) / 10 ^ 6 at hsqL
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hL10 : (10 : ℝ) ≤ L := by linarith only [hL]
  have hL1 : (1 : ℝ) ≤ L := by linarith only [hL10]
  have hsq_ge1 : (1 : ℝ) ≤ sqrt k := by
    rw [le_sqrt (by norm_num) hk_pos.le]; linarith only [hkR]
  let B0 : ℝ := (((2 * k + 1 + f).choose m : ℕ) : ℝ)
  let N0 : ℝ := (((m + 1).choose (2 * f + 1) : ℕ) : ℝ)
  let α : ℝ := αk_val k
  let cK1 : ℝ := cK_val k m f d1
  let cK2 : ℝ := cK_val k m f d2
  let cM1 : ℝ := cM_val m f d1
  let cC2 : ℝ := cC_val m f d2
  have hα_pos : 0 < α := by dsimp [α, αk_val]; positivity
  have hc1 := cK_cM_bounds hV hd1
  have hc2 := cK_cM_bounds hV hd2
  have hpref_pos : 0 < cM1 * cC2 * cK1 * cK2 := by
    have := hc1.1; have := hc2.1; have := hc1.2.2.1; have := hc2.2.2.2.2.1; positivity
  have hpref_le : cM1 * cC2 * cK1 * cK2 ≤ 1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k) := by
    have h1 := mul_le_mul hc1.2.2.2.1 hc2.2.2.2.2.2 hc2.2.2.2.2.1.le (by positivity)
    have h2 := mul_le_mul hc1.2.1 hc2.2.1 hc2.1.le (by positivity)
    have h3 := mul_le_mul h1 h2 (mul_nonneg hc1.1.le hc2.1.le) (by positivity)
    have hrhs : (10 * N0 / sqrt k * 1) * (10 * B0 / sqrt k * (10 * B0 / sqrt k)) =
        1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k) := by
      calc (10 * N0 / sqrt k * 1) * (10 * B0 / sqrt k * (10 * B0 / sqrt k))
          = 1000 * N0 * B0 ^ 2 / ((sqrt k * sqrt k) * sqrt k) := by ring
        _ = 1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k) := by rw [mul_self_sqrt hk_pos.le]
    have h3' : cM1 * cC2 * (cK1 * cK2) ≤ _ := h3
    rw [hrhs] at h3'; linarith only [h3']
  have hLpow_tiny : ∀ p : ℕ, p ≤ 10 → L ^ p / sqrt k ≤ 1 / 10 ^ 100 := by
    intro p hp
    have h1 : (10 ^ 100 : ℝ) * L ^ p ≤ L ^ 15 := by
      have h5 : (10 ^ 20 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
      have h10 : L ^ p ≤ L ^ 10 := pow_le_pow_right₀ hL1 hp
      have hm := mul_le_mul h5 h10 (pow_nonneg (by linarith only [hL1]) p) (by positivity)
      rw [← pow_add, show (5 + 10 : ℕ) = 15 by norm_num,
        show ((10 ^ 20 : ℝ) ^ 5) = 10 ^ 100 by norm_num] at hm
      exact hm
    have hdiv : (10 ^ 100 : ℝ) * (L ^ p / sqrt k) ≤ L ^ 15 / sqrt k := by
      rw [mul_div_assoc']; exact dR h1 hsq_pos.le
    linarith only [hdiv, hL15]
  have hinv_sqα2 : 1 / sqrt (α / 2) ≤ sqrt k := by
    have hpos : 0 < sqrt (α / 2) := sqrt_pos.mpr (by positivity)
    rw [div_le_iff₀ hpos]
    have h1 : (1 : ℝ) ≤ (k : ℝ) * (α / 2) := by dsimp [α, αk_val]; field_simp [hk_pos.ne']; norm_num
    rw [← sqrt_mul hk_pos.le, le_sqrt (by norm_num) (by positivity)]; simpa only [one_pow] using h1
  have hphi_le : ∀ x : ℝ, |phiG α x| ≤ sqrt k * exp (-α * x ^ 2 / 2) := by
    intro x
    let u : ℝ := sqrt (α / 2) * |x|
    have hu_nn : 0 ≤ u := by dsimp [u]; positivity
    have hu_sq : u ^ 2 = (α / 2) * x ^ 2 := by dsimp [u]; rw [mul_pow, sq_sqrt (by positivity), sq_abs]
    have hu_le : u * exp (-u ^ 2) ≤ 1 := by
      have h1 : u ≤ 1 + u ^ 2 := by nlinarith only [sq_nonneg (u - 1)]
      have h2 : 1 + u ^ 2 ≤ exp (u ^ 2) := by linarith only [add_one_le_exp (u ^ 2)]
      have h3 := mR (h1.trans h2) (exp_pos (-u ^ 2)).le
      rwa [← exp_add, add_neg_cancel, exp_zero] at h3
    have hsplit : exp (-α * x ^ 2) = exp (-u ^ 2) * exp (-α * x ^ 2 / 2) := by
      rw [← exp_add]; congr 1; rw [hu_sq]; ring
    have hxu : |x| = (1 / sqrt (α / 2)) * u := by
      dsimp [u]; field_simp [(sqrt_pos.mpr (by positivity : 0 < α / 2)).ne']
    dsimp [phiG]; rw [abs_mul, abs_of_pos (exp_pos _), hsplit, hxu]
    calc (1 / sqrt (α / 2)) * u * (exp (-u ^ 2) * exp (-α * x ^ 2 / 2))
        = (1 / sqrt (α / 2)) * (u * exp (-u ^ 2)) * exp (-α * x ^ 2 / 2) := by ring
      _ ≤ sqrt k * 1 * exp (-α * x ^ 2 / 2) :=
          mR (mul_le_mul hinv_sqα2 hu_le (by positivity) hsq_pos.le) (exp_pos _).le
      _ = sqrt k * exp (-α * x ^ 2 / 2) := by ring
  have hsum_exp_t : ∀ (j : ℕ) (c : ℝ), ∑ t ∈ T_box j, exp (-α * ((t : ℝ) - c) ^ 2 / 2) ≤ 10 * sqrt k := by
    intro j c
    have hsub : T_box j ⊆ range m := filter_subset _ _
    have hrew : ∀ t : ℕ, exp (-α * ((t : ℝ) - c) ^ 2 / 2) = exp (-(α / 2) * ((t : ℝ) - c) ^ 2) :=
      fun t => by congr 1; ring
    simp_rw [hrew]
    have h1 := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (exp_pos _).le)).trans
      (sum_exp_sq_of_step_ge_one m (fun t => (t : ℝ) - c) (by positivity : 0 < α / 2) (fun t => by push_cast; linarith))
    have h4 : 4 / sqrt (α / 2) = 4 * (1 / sqrt (α / 2)) := by ring
    linarith only [h1, h4, hinv_sqα2, hsq_ge1]
  have hsum_exp_a : ∀ j : ℕ, ∑ a ∈ A_box j, exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) ≤ 10 * sqrt k := by
    intro j
    have hsub : A_box j ⊆ range (f + 1) := filter_subset _ _
    have hrew : ∀ a : ℕ, exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) =
        exp (-(18 / (k : ℝ)) * (ε_coord m f j a) ^ 2) := fun a => by congr 1; ring
    simp_rw [hrew]
    have h1 := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (exp_pos _).le)).trans
      (sum_exp_sq_of_step_ge_one (f + 1) (fun a => ε_coord m f j a) (by positivity : 0 < 18 / (k : ℝ))
        (fun a => by dsimp [ε_coord]; push_cast; linarith))
    have hinv : 1 / sqrt (18 / (k : ℝ)) ≤ sqrt k := by
      rw [div_le_iff₀ (sqrt_pos.mpr (by positivity)), ← sqrt_mul hk_pos.le,
        le_sqrt (by norm_num) (by positivity)]
      field_simp [hk_pos.ne']; norm_num
    have h4 : 4 / sqrt (18 / (k : ℝ)) = 4 * (1 / sqrt (18 / (k : ℝ))) := by ring
    linarith only [h1, h4, hinv, hsq_ge1]
  let J_lo : ℕ := Nat.ceil ((m : ℝ) / 2 - 40 * sqrt k * L)
  let J_hi : ℕ := ⌊(m : ℝ) / 2 + 40 * sqrt k * L⌋₊ + 1
  have hm_lo_sub : (100 : ℝ) ≤ (m : ℝ) / 2 - 40 * sqrt k * L := by
    linarith only [hba.1, hsqL, hkR]
  have hm_hi_add : (m : ℝ) / 2 + 40 * sqrt k * L + 2 ≤ (m : ℝ) := by
    linarith only [hba.1, hsqL, hkR]
  have hm_hi_nn : 0 ≤ (m : ℝ) / 2 + 40 * sqrt k * L := by
    have hnn : 0 ≤ sqrt k * L := by positivity
    linarith only [hm_lo_sub, hnn]
  have hJ_lo_ge : 100 ≤ J_lo := by
    have : (100 : ℝ) ≤ (J_lo : ℝ) := hm_lo_sub.trans (Nat.le_ceil _)
    exact_mod_cast this
  have hJ_hi_le : J_hi ≤ m := by
    have h1 : (J_hi : ℝ) ≤ (m : ℝ) / 2 + 40 * sqrt k * L + 1 := by
      dsimp [J_hi]; push_cast; linarith only [Nat.floor_le hm_hi_nn]
    have : (J_hi : ℝ) ≤ m := by linarith only [h1, hm_hi_add]
    exact_mod_cast this
  have hJ_eq : J_box = Ico J_lo J_hi := by
    ext j; simp only [J_box, mem_filter, mem_range, mem_Ico]
    have h1 : J_lo ≤ j ↔ (m : ℝ) / 2 - 40 * sqrt k * L ≤ (j : ℝ) := Nat.ceil_le
    have h2 : j < J_hi ↔ (j : ℝ) ≤ (m : ℝ) / 2 + 40 * sqrt k * L := by
      dsimp [J_hi]
      rw [Nat.lt_succ_iff, Nat.le_floor_iff hm_hi_nn]
    have h3 : |δ_coord m j| ≤ 40 * sqrt k * L ↔
        (m : ℝ) / 2 - 40 * sqrt k * L ≤ (j : ℝ) ∧ (j : ℝ) ≤ (m : ℝ) / 2 + 40 * sqrt k * L := by
      dsimp [δ_coord]; rw [abs_le]
      constructor <;> (intro ⟨p, q⟩; exact ⟨by linarith only [p], by linarith only [q]⟩)
    rw [h1, h2, h3]
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · rintro ⟨hlo, hhi⟩
      refine ⟨?_, ?_, ⟨hlo, hhi⟩⟩
      · have : j < J_hi := h2.mpr hhi; omega
      · have : J_lo ≤ j := h1.mpr hlo; omega
  have hT_eq : ∀ j ∈ J_box, T_box j = Ico (j + D0 + 1) J_hi := by
    intro j hj
    rw [hJ_eq, mem_Ico] at hj
    ext t; simp only [T_box, mem_filter, mem_range, mem_Ico]
    have h1 : J_lo ≤ t ↔ (m : ℝ) / 2 - 40 * sqrt k * L ≤ (t : ℝ) := Nat.ceil_le
    have h2 : t < J_hi ↔ (t : ℝ) ≤ (m : ℝ) / 2 + 40 * sqrt k * L := by
      dsimp [J_hi]; rw [Nat.lt_succ_iff, Nat.le_floor_iff hm_hi_nn]
    have h3 : |δ_coord m t| ≤ 40 * sqrt k * L ↔
        (m : ℝ) / 2 - 40 * sqrt k * L ≤ (t : ℝ) ∧ (t : ℝ) ≤ (m : ℝ) / 2 + 40 * sqrt k * L := by
      dsimp [δ_coord]; rw [abs_le]
      constructor <;> (intro ⟨p, q⟩; exact ⟨by linarith only [p], by linarith only [q]⟩)
    rw [h3]
    constructor
    · rintro ⟨_, hgt, _, hhi⟩; exact ⟨by omega, h2.mpr hhi⟩
    · rintro ⟨hgt, hlt⟩
      exact ⟨by omega, by omega, h1.mp (by omega), h2.mp hlt⟩
  have hJ_card : (J_box.card : ℝ) ≤ 82 * sqrt k * L := by
    rw [hJ_eq, Nat.card_Ico]
    have hlo : (m : ℝ) / 2 - 40 * sqrt k * L ≤ (J_lo : ℝ) := Nat.le_ceil _
    have hhi : (J_hi : ℝ) ≤ (m : ℝ) / 2 + 40 * sqrt k * L + 1 := by
      dsimp [J_hi]; push_cast
      linarith only [Nat.floor_le hm_hi_nn]
    have hdiff : ((J_hi - J_lo : ℕ) : ℝ) ≤ 80 * sqrt k * L + 1 := by
      by_cases h : J_lo ≤ J_hi
      · rw [Nat.cast_sub h]; linarith only [hlo, hhi]
      · have : J_hi - J_lo = 0 := by omega
        rw [this, Nat.cast_zero]; positivity
    have h1sqL : (1 : ℝ) ≤ sqrt k * L := by
      have := mul_le_mul hsq_ge1 hL10 (by norm_num) hsq_pos.le; linarith only [this]
    linarith only [hdiff, h1sqL]
  have hD0_ge : 100 ≤ D0 := by
    have h1 : (100 : ℝ) ≤ L ^ 7 := by
      have := pow_le_pow_left₀ (by norm_num) hL10 7; linarith only [this]
    exact Nat.le_floor h1
  have hD0_le : (D0 : ℝ) ≤ L ^ 7 := Nat.floor_le (pow_nonneg (by linarith only [hL10]) 7)
  have hsum_harm : ∀ j ∈ J_box, ∑ t ∈ T_box j, (1 : ℝ) / ((t - j - 1 : ℕ) : ℝ) ≤ 2 * L := by
    intro j hj
    have hJ_pos : 1 ≤ J_hi - J_lo := by
      have hlo_lt : (J_lo : ℝ) < (m : ℝ) / 2 - 40 * sqrt k * L + 1 :=
        Nat.ceil_lt_add_one (by linarith only [hm_lo_sub])
      have hhi_gt : (m : ℝ) / 2 + 40 * sqrt k * L < (J_hi : ℝ) := by
        dsimp [J_hi]; push_cast; exact Nat.lt_floor_add_one _
      have h1sqL : (1 : ℝ) ≤ sqrt k * L := by
        have := mul_le_mul hsq_ge1 hL10 (by norm_num) hsq_pos.le; linarith only [this]
      have : (J_lo : ℝ) + 1 ≤ (J_hi : ℝ) := by linarith only [hlo_lt, hhi_gt, h1sqL]
      have : J_lo + 1 ≤ J_hi := by exact_mod_cast this
      omega
    have hj_ico : j ∈ Ico J_lo J_hi := by rwa [← hJ_eq]
    have hj_lo : J_lo ≤ j := (mem_Ico.mp hj_ico).1
    let g : ℕ → ℕ := fun t => t - j - 2
    have hinj : ∀ t1 ∈ T_box j, ∀ t2 ∈ T_box j, g t1 = g t2 → t1 = t2 := by
      intro t1 ht1 t2 ht2 heq
      have h1 := (mem_filter.mp ht1).2.1; have h2 := (mem_filter.mp ht2).2.1
      dsimp [g] at heq; omega
    have hsub_img : (T_box j).image g ⊆ range (J_hi - J_lo) := by
      intro r hr; obtain ⟨t, ht, rfl⟩ := mem_image.mp hr
      rw [hT_eq j hj, mem_Ico] at ht
      exact mem_range.mpr (by dsimp [g]; omega)
    have heq_img : ∑ t ∈ T_box j, (1 : ℝ) / ((t - j - 1 : ℕ) : ℝ) =
        ∑ r ∈ (T_box j).image g, (1 : ℝ) / ((r + 1 : ℕ) : ℝ) := by
      rw [sum_image hinj]
      refine sum_congr rfl fun t ht => ?_
      have hgt := (mem_filter.mp ht).2.1
      have : g t + 1 = t - j - 1 := by dsimp [g]; omega
      rw [this]
    rw [heq_img]
    have hstep1 := (sum_le_sum_of_subset_of_nonneg hsub_img (fun _ _ _ => by positivity)).trans
      (harmonic_sum_le (J_hi - J_lo) hJ_pos)
    have hlog_le : log ((J_hi - J_lo : ℕ) : ℝ) ≤ L := by
      have hle : ((J_hi - J_lo : ℕ) : ℝ) ≤ (k : ℝ) := by
        have hc := hJ_card; rw [hJ_eq, Nat.card_Ico] at hc; linarith only [hc, hsqL, hk_pos]
      exact log_le_log (by exact_mod_cast (show 0 < J_hi - J_lo by omega)) hle
    linarith only [hstep1, hlog_le, hL10]
  have hMj_le : ∀ j ∈ J_box, ∀ a ∈ A_box j,
      (j.choose (2 * a + d1) : ℝ) * ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) ≤
        2 * (cM1 * cC2 * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ))) := by
    intro j hj a ha
    have hm := M_pair_gaussian_approx hV hd1 hd2 (mem_filter.mp hj).2.2 (mem_filter.mp ha).2
    have h2e10 : (2e10 : ℝ) * (L ^ 3 / sqrt k) ≤ 1 := by
      have := hLpow_tiny 3 (by omega); linarith only [this]
    have hGM_nn : 0 ≤ cM1 * cC2 * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
      have := hc1.2.2.1; have := hc2.2.2.2.2.1; positivity
    have h1 := (abs_le.mp hm).2
    have h2 := mR h2e10 hGM_nn
    linarith only [h1, h2]
  have hdkj_le : ∀ j ∈ J_box, ∀ a ∈ A_box j,
      |deltaK k a (f - a - d1) j (m - 1 - j)| ≤ (40 / sqrt k) * cK1 := by
    intro j hj a ha
    have ha20 : |ε_coord m f j a| ≤ 20 * sqrt k * L := by
      have h1 := (mem_filter.mp ha).2
      have hnn : 0 ≤ sqrt k * L := by positivity
      linarith only [h1, hnn]
    have hdk := (deltaK_gaussian_approx hV hd1 (mem_filter.mp hj).2.2 ha20).2
    have htri := abs_add_le
      (deltaK k a (f - a - d1) j (m - 1 - j) - (-18 / (k : ℝ)) * cK1 * phiG α (δ_coord m j - ε_coord m f j a))
      ((-18 / (k : ℝ)) * cK1 * phiG α (δ_coord m j - ε_coord m f j a))
    rw [sub_add_cancel] at htri
    have hexp1 : exp (-α * (δ_coord m j - ε_coord m f j a) ^ 2) ≤ 1 :=
      exp_le_one_iff.mpr (by nlinarith only [hα_pos, sq_nonneg (δ_coord m j - ε_coord m f j a)])
    have hexp1h : exp (-α * (δ_coord m j - ε_coord m f j a) ^ 2 / 2) ≤ 1 :=
      exp_le_one_iff.mpr (by nlinarith only [hα_pos, sq_nonneg (δ_coord m j - ε_coord m f j a)])
    have hmain : |(-18 / (k : ℝ)) * cK1 * phiG α (δ_coord m j - ε_coord m f j a)| ≤ (18 / sqrt k) * cK1 := by
      rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 18),
        abs_of_pos hk_pos, abs_of_pos hc1.1]
      have hp : |phiG α (δ_coord m j - ε_coord m f j a)| ≤ sqrt k := by
        have := (hphi_le (δ_coord m j - ε_coord m f j a)).trans
          (mL hexp1h hsq_pos.le)
        linarith only [this]
      calc 18 / (k : ℝ) * cK1 * |phiG α (δ_coord m j - ε_coord m f j a)|
          ≤ 18 / (k : ℝ) * cK1 * sqrt k :=
            mL hp (mul_nonneg (by positivity) hc1.1.le)
        _ = (18 / sqrt k) * cK1 := by
            calc 18 / (k : ℝ) * cK1 * sqrt k
                = 18 / (sqrt k * sqrt k) * cK1 * sqrt k := by
                  rw [mul_self_sqrt hk_pos.le]
              _ = (18 / sqrt k) * cK1 := by field_simp [hsq_pos.ne']
    have herr : (2e13 : ℝ) * (L ^ 4 / (k : ℝ)) * (cK1 * exp (-α * (δ_coord m j - ε_coord m f j a) ^ 2)) ≤
        (1 / sqrt k) * cK1 := by
      have h1 : (2e13 : ℝ) * (L ^ 4 / (k : ℝ)) ≤ 1 / sqrt k := by
        have hrew : (2e13 : ℝ) * (L ^ 4 / (k : ℝ)) = (2e13 * (L ^ 4 / sqrt k)) / sqrt k := by
          calc (2e13 : ℝ) * (L ^ 4 / (k : ℝ))
              = (2e13 : ℝ) * (L ^ 4 / (sqrt k * sqrt k)) := by
                rw [mul_self_sqrt hk_pos.le]
            _ = (2e13 * (L ^ 4 / sqrt k)) / sqrt k := by field_simp [hsq_pos.ne']
        rw [hrew]
        apply dR _ hsq_pos.le
        have := hLpow_tiny 4 (by omega); linarith only [this]
      have h2 := mL hexp1 hc1.1.le
      have h3 := mul_le_mul h1 (by linarith only [h2] : cK1 * exp _ ≤ cK1)
        (mul_nonneg hc1.1.le (exp_pos _).le) (by positivity)
      exact h3
    have hc1nn : 0 ≤ cK1 / sqrt k := by have := hc1.1; positivity
    have hrew1 : (18 / sqrt k) * cK1 = 18 * (cK1 / sqrt k) := by ring
    have hrew2 : (1 / sqrt k) * cK1 = 1 * (cK1 / sqrt k) := by ring
    have hrew3 : (40 / sqrt k) * cK1 = 40 * (cK1 / sqrt k) := by ring
    linarith only [htri, hdk, hmain, herr, hc1nn, hrew1, hrew2, hrew3]
  let M_val (j a : ℕ) : ℝ := (j.choose (2 * a + d1) : ℝ) * ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ)
  let GM_val (j a : ℕ) : ℝ := cM1 * cC2 * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ))
  let S0 : ℝ := ∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, ∑ b ∈ B_box j t a,
      ((j.choose (2 * a + d1) * (t - j - 1).choose (2 * (b - a - d1) + d2) *
        (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) *
      deltaK k a (f - a - d1) j (m - 1 - j) *
      deltaK k b (f - b - d2) t (m - 1 - t)
  let S1 : ℝ := ∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j,
      (1 / 2) * M_val j a * deltaK k a (f - a - d1) j (m - 1 - j) *
      ((-18 / (k : ℝ)) * cK2 * phiG α (δ_coord m t - ε_coord m f j a))
  let S2 : ℝ := ∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j,
      (1 / 2) * GM_val j a * deltaK k a (f - a - d1) j (m - 1 - j) *
      ((-18 / (k : ℝ)) * cK2 * phiG α (δ_coord m t - ε_coord m f j a))
  let S3 : ℝ := ∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j,
      (1 / 2) * GM_val j a * ((-18 / (k : ℝ)) * cK1 * phiG α (δ_coord m j - ε_coord m f j a)) *
      ((-18 / (k : ℝ)) * cK2 * phiG α (δ_coord m t - ε_coord m f j a))
  have hStep1 : |S0 - S1| ≤ 3e23 * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
    let E1 (j a t : ℕ) : ℝ :=
      (j.choose (2 * a + d1) : ℝ) * deltaK k a (f - a - d1) j (m - 1 - j) *
        ((∑ b ∈ B_box j t a,
          ((t - j - 1).choose (2 * (b - a - d1) + d2) : ℝ) *
            ((m - t).choose (2 * (f - b - d2) + 1) : ℝ) *
            deltaK k b (f - b - d2) t (m - 1 - t)) -
         (1 / 2) * ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) *
            ((-18 / (k : ℝ)) * cK2 * phiG α (δ_coord m t - ε_coord m f j a)))
    have hdiff_eq : S0 - S1 = ∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, E1 j a t := by
      dsimp [S0, S1, M_val, E1]
      simp_rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ => sum_congr rfl fun a _ => sum_congr rfl fun t _ => ?_
      rw [mul_sub, mul_sum]
      congr 1
      · refine sum_congr rfl fun b _ => ?_; push_cast; ring
      · ring
    rw [hdiff_eq]
    have hja : ∀ j ∈ J_box, ∀ a ∈ A_box j,
        |∑ t ∈ T_box j, E1 j a t| ≤
        (2e17 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
      intro j hj a ha
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have ht_pt : ∀ t ∈ T_box j,
          |E1 j a t| ≤
          (80 / sqrt k) * (cM1 * cC2 * cK1 * cK2) *
            exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
            ((2e14 * L ^ 4 / (k : ℝ)) * exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) +
             (2e7 * L ^ 2 / sqrt k) * ((1 : ℝ) / ((t - j - 1 : ℕ) : ℝ))) := by
        intro t ht
        dsimp [E1]
        have ht' := mem_filter.mp ht
        have hj' := mem_filter.mp hj
        have htm : t < m := mem_range.mp ht'.1
        have hDM : (t - j - 1) + (m - t) = m - j - 1 := by omega
        have hib := inner_b_sum_approx hV hd1 hd2 ht'.2.1 htm hj'.2.2 ht'.2.2 (mem_filter.mp ha).2
        dsimp only at hib
        rw [hDM] at hib
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        have hM_comb : (j.choose (2 * a + d1) : ℝ) * |deltaK k a (f - a - d1) j (m - 1 - j)| *
            (((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℕ) : ℝ) * cK2 ≤
            (80 / sqrt k) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
          have h1 := mul_le_mul (hMj_le j hj a ha) (hdkj_le j hj a ha) (abs_nonneg _) (by
            have := hc1.2.2.1; have := hc2.2.2.2.2.1; positivity)
          have h2 := mR h1 hc2.1.le
          have hl : (j.choose (2 * a + d1) : ℝ) * ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) *
              |deltaK k a (f - a - d1) j (m - 1 - j)| * cK2 =
              (j.choose (2 * a + d1) : ℝ) * |deltaK k a (f - a - d1) j (m - 1 - j)| *
              (((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℕ) : ℝ) * cK2 := by ring
          have hr : 2 * (cM1 * cC2 * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ))) *
              ((40 / sqrt k) * cK1) * cK2 =
              (80 / sqrt k) * (cM1 * cC2 * cK1 * cK2) *
              exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by ring
          linarith only [h2, hl, hr]
        have hphi_t : (2e7 * L ^ 2 / ((k : ℝ) * ((t - j - 1 : ℕ) : ℝ))) * |phiG α (δ_coord m t - ε_coord m f j a)| ≤
            (2e7 * L ^ 2 / sqrt k) * ((1 : ℝ) / ((t - j - 1 : ℕ) : ℝ)) := by
          have h1 : |phiG α (δ_coord m t - ε_coord m f j a)| ≤ sqrt k := by
            have he1 : exp (-α * (δ_coord m t - ε_coord m f j a) ^ 2 / 2) ≤ 1 :=
              exp_le_one_iff.mpr (by nlinarith only [hα_pos, sq_nonneg (δ_coord m t - ε_coord m f j a)])
            have := (hphi_le _).trans (mL he1 hsq_pos.le)
            linarith only [this]
          have hD_pos : (0 : ℝ) < ((t - j - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < t - j - 1 by omega)
          calc (2e7 * L ^ 2 / ((k : ℝ) * ((t - j - 1 : ℕ) : ℝ))) * |phiG α (δ_coord m t - ε_coord m f j a)|
              ≤ (2e7 * L ^ 2 / ((k : ℝ) * ((t - j - 1 : ℕ) : ℝ))) * sqrt k :=
                mL h1 (by positivity)
            _ = (2e7 * L ^ 2 / sqrt k) * ((1 : ℝ) / ((t - j - 1 : ℕ) : ℝ)) := by
                calc (2e7 * L ^ 2 / ((k : ℝ) * ((t - j - 1 : ℕ) : ℝ))) * sqrt k
                    = (2e7 * L ^ 2 / ((sqrt k * sqrt k) * ((t - j - 1 : ℕ) : ℝ))) *
                      sqrt k := by rw [mul_self_sqrt hk_pos.le]
                  _ = (2e7 * L ^ 2 / sqrt k) * ((1 : ℝ) / ((t - j - 1 : ℕ) : ℝ)) := by
                      field_simp [hsq_pos.ne', hD_pos.ne']
        have hy_rew : δ_coord m t - ε_coord m f j a = (t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a) := by
          dsimp [δ_coord]; ring
        calc (j.choose (2 * a + d1) : ℝ) * |deltaK k a (f - a - d1) j (m - 1 - j)| *
              |(∑ b ∈ B_box j t a, ((t - j - 1).choose (2 * (b - a - d1) + d2) : ℝ) *
                ((m - t).choose (2 * (f - b - d2) + 1) : ℝ) * deltaK k b (f - b - d2) t (m - 1 - t)) -
                (1 / 2) * ((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℝ) *
                ((-18 / (k : ℝ)) * cK2 * phiG α (δ_coord m t - ε_coord m f j a))|
            ≤ (j.choose (2 * a + d1) : ℝ) * |deltaK k a (f - a - d1) j (m - 1 - j)| *
              ((((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℕ) : ℝ) * cK2 *
                ((2e14 * L ^ 4 / (k : ℝ)) * exp (-α * (δ_coord m t - ε_coord m f j a) ^ 2 / 2) +
                 (2e7 * L ^ 2 / ((k : ℝ) * ((t - j - 1 : ℕ) : ℝ))) * |phiG α (δ_coord m t - ε_coord m f j a)|)) :=
              mL hib (by positivity)
          _ = ((j.choose (2 * a + d1) : ℝ) * |deltaK k a (f - a - d1) j (m - 1 - j)| *
                (((m - j - 1).choose (2 * (f - a - d1) + 1 - d2) : ℕ) : ℝ) * cK2) *
              ((2e14 * L ^ 4 / (k : ℝ)) * exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) +
               (2e7 * L ^ 2 / ((k : ℝ) * ((t - j - 1 : ℕ) : ℝ))) * |phiG α (δ_coord m t - ε_coord m f j a)|) := by
                rw [hy_rew]; ring
          _ ≤ (80 / sqrt k) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
              ((2e14 * L ^ 4 / (k : ℝ)) * exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) +
               (2e7 * L ^ 2 / sqrt k) * ((1 : ℝ) / ((t - j - 1 : ℕ) : ℝ))) :=
              mul_le_mul hM_comb (add_le_add le_rfl hphi_t) (by positivity) (by positivity)
      calc ∑ t ∈ T_box j, _
          ≤ ∑ t ∈ T_box j, (80 / sqrt k) * (cM1 * cC2 * cK1 * cK2) *
              exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
              ((2e14 * L ^ 4 / (k : ℝ)) * exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) +
               (2e7 * L ^ 2 / sqrt k) * ((1 : ℝ) / ((t - j - 1 : ℕ) : ℝ))) :=
            sum_le_sum ht_pt
        _ = (80 / sqrt k) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
            ((2e14 * L ^ 4 / (k : ℝ)) * ∑ t ∈ T_box j, exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) +
             (2e7 * L ^ 2 / sqrt k) * ∑ t ∈ T_box j, (1 : ℝ) / ((t - j - 1 : ℕ) : ℝ)) := by
              rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
        _ ≤ (80 / sqrt k) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
            ((2e14 * L ^ 4 / (k : ℝ)) * (10 * sqrt k) + (2e7 * L ^ 2 / sqrt k) * (2 * L)) :=
            mL
              (add_le_add (mL (hsum_exp_t j _) (by positivity))
                (mL (hsum_harm j hj) (by positivity))) (by positivity)
        _ ≤ (2e17 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
            have hfac : (80 / sqrt k) * ((2e14 * L ^ 4 / (k : ℝ)) * (10 * sqrt k) +
                (2e7 * L ^ 2 / sqrt k) * (2 * L)) ≤ 2e17 * L ^ 4 / (k : ℝ) := by
              have hrew : (80 / sqrt k) * ((2e14 * L ^ 4 / (k : ℝ)) * (10 * sqrt k) +
                  (2e7 * L ^ 2 / sqrt k) * (2 * L)) =
                  (1.6e17 * L ^ 4 + 3.2e9 * L ^ 3) / (k : ℝ) := by
                calc (80 / sqrt k) * ((2e14 * L ^ 4 / (k : ℝ)) * (10 * sqrt k) +
                      (2e7 * L ^ 2 / sqrt k) * (2 * L))
                    = 1.6e17 * L ^ 4 / (k : ℝ) + 3.2e9 * L ^ 3 / (sqrt k * sqrt k) := by
                      field_simp [hsq_pos.ne', hk_pos.ne']; ring
                  _ = (1.6e17 * L ^ 4 + 3.2e9 * L ^ 3) / (k : ℝ) := by
                      rw [mul_self_sqrt hk_pos.le, add_div]
              rw [hrew]; apply dR _ hk_pos.le
              have hL34 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by omega)
              have hnn : 0 ≤ L ^ 4 := pow_nonneg (by linarith only [hL1]) 4
              linarith only [hL34, hnn]
            have hmul := mR hfac
              (show 0 ≤ (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) by positivity)
            linarith only [hmul]
    have htot1 : |∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, E1 j a t| ≤
        (2e17 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * ((82 * sqrt k * L) * (10 * sqrt k)) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j ∈ J_box, |∑ a ∈ A_box j, ∑ t ∈ T_box j, E1 j a t|
          ≤ ∑ j ∈ J_box, ∑ a ∈ A_box j, |∑ t ∈ T_box j, E1 j a t| :=
            sum_le_sum fun j _ => abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ J_box, ∑ a ∈ A_box j,
              (2e17 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) :=
            sum_le_sum fun j hj => sum_le_sum fun a ha => hja j hj a ha
        _ = (2e17 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) *
            ∑ j ∈ J_box, ∑ a ∈ A_box j, exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
              rw [mul_sum]; refine sum_congr rfl fun j _ => by rw [mul_sum]
        _ ≤ (2e17 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * ((82 * sqrt k * L) * (10 * sqrt k)) := by
              apply mL _ (by positivity)
              calc ∑ j ∈ J_box, ∑ a ∈ A_box j, exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ))
                  ≤ ∑ _j ∈ J_box, (10 * sqrt k) := sum_le_sum fun j _ => hsum_exp_a j
                _ = (J_box.card : ℝ) * (10 * sqrt k) := by rw [sum_const, nsmul_eq_mul]
                _ ≤ (82 * sqrt k * L) * (10 * sqrt k) :=
                    mR hJ_card (by positivity)
    have hsimp1 : (2e17 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * ((82 * sqrt k * L) * (10 * sqrt k)) =
        (1.64e20 * L ^ 5) * (cM1 * cC2 * cK1 * cK2) := by
      calc (2e17 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * ((82 * sqrt k * L) * (10 * sqrt k))
          = ((1.64e20 * L ^ 5 / (k : ℝ)) * (sqrt k * sqrt k)) * (cM1 * cC2 * cK1 * cK2) := by ring
        _ = (1.64e20 * L ^ 5) * (cM1 * cC2 * cK1 * cK2) := by
            rw [mul_self_sqrt hk_pos.le]; field_simp [hk_pos.ne']
    have hL57 : L ^ 5 ≤ L ^ 7 := pow_le_pow_right₀ hL1 (by omega)
    calc |∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, E1 j a t|
        ≤ (1.64e20 * L ^ 5) * (cM1 * cC2 * cK1 * cK2) := by linarith only [htot1, hsimp1]
      _ ≤ (1.64e20 * L ^ 7) * (1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k)) :=
          mul_le_mul (mL hL57 (by norm_num)) hpref_le hpref_pos.le (by positivity)
      _ ≤ 3e23 * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
          have hnn : 0 ≤ (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by positivity
          have heq : (1.64e20 * L ^ 7) * (1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k)) =
              1.64e23 * ((L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2) := by ring
          linarith only [hnn, heq]
  have hStep2 : |S1 - S2| ≤ 1e21 * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
    let E2 (j a t : ℕ) : ℝ :=
      (1 / 2) * (M_val j a - GM_val j a) * deltaK k a (f - a - d1) j (m - 1 - j) *
        ((-18 / (k : ℝ)) * cK2 * phiG α (δ_coord m t - ε_coord m f j a))
    have hdiff : S1 - S2 = ∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, E2 j a t := by
      dsimp [S1, S2, E2]; simp_rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ => sum_congr rfl fun a _ => sum_congr rfl fun t _ => by ring
    rw [hdiff]
    have htot2 : |∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, E2 j a t| ≤
        (1e17 * L ^ 4) * (cM1 * cC2 * cK1 * cK2) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hja2 : ∀ j ∈ J_box, ∀ a ∈ A_box j,
          ∑ t ∈ T_box j, |E2 j a t| ≤
          (1e14 * L ^ 3 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
        intro j hj a ha
        have hMa' : |M_val j a - GM_val j a| ≤ (2e10 : ℝ) * (L ^ 3 / sqrt k) * GM_val j a :=
          M_pair_gaussian_approx hV hd1 hd2 (mem_filter.mp hj).2.2 (mem_filter.mp ha).2
        have hdka := hdkj_le j hj a ha
        have hcK1_pos : 0 < cK1 := hc1.1
        have hcK2_pos : 0 < cK2 := hc2.1
        have hL_nn : 0 ≤ L := by linarith only [hL1]
        have hGM_nn : 0 ≤ GM_val j a := by
          dsimp [GM_val]; have := hc1.2.2.1; have := hc2.2.2.2.2.1; positivity
        have ht_le : ∀ t ∈ T_box j,
            |E2 j a t| ≤
            (1e13 * L ^ 3 / ((k : ℝ) * sqrt k)) * (cM1 * cC2 * cK1 * cK2) *
              exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
              exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) := by
          intro t _
          dsimp [E2]
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
            abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 18), abs_of_pos hk_pos, abs_of_pos hcK2_pos]
          have h1 := mul_le_mul hMa' hdka (abs_nonneg _) (by positivity)
          have h2 := mL (hphi_le (δ_coord m t - ε_coord m f j a)) (by positivity : 0 ≤ 18 / (k : ℝ) * cK2)
          have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
          have h4 := mL h3 (by norm_num : (0 : ℝ) ≤ 1 / 2)
          have hy_rew : δ_coord m t - ε_coord m f j a = (t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a) := by dsimp [δ_coord]; ring
          have hsimp : (1 / 2) * ((2e10 : ℝ) * (L ^ 3 / sqrt k) * GM_val j a * ((40 / sqrt k) * cK1) *
              (18 / (k : ℝ) * cK2 * (sqrt k * exp (-α * (δ_coord m t - ε_coord m f j a) ^ 2 / 2)))) =
              7.2e12 * (L ^ 3 / ((k : ℝ) * sqrt k) * (cM1 * cC2 * cK1 * cK2) *
                exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
                exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2)) := by
            dsimp [GM_val]; rw [hy_rew]
            field_simp [hsq_pos.ne', hk_pos.ne']; ring
          have hgoal_eq : (1e13 * L ^ 3 / ((k : ℝ) * sqrt k)) * (cM1 * cC2 * cK1 * cK2) *
              exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
              exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) =
              1e13 * (L ^ 3 / ((k : ℝ) * sqrt k) * (cM1 * cC2 * cK1 * cK2) *
                exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
                exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2)) := by ring
          have hnn : 0 ≤ L ^ 3 / ((k : ℝ) * sqrt k) * (cM1 * cC2 * cK1 * cK2) *
              exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
              exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) := by positivity
          have hass : 1 / 2 * |M_val j a - GM_val j a| * |deltaK k a (f - a - d1) j (m - 1 - j)| *
              (18 / (k : ℝ) * cK2 * |phiG α (δ_coord m t - ε_coord m f j a)|) =
              1 / 2 * (|M_val j a - GM_val j a| * |deltaK k a (f - a - d1) j (m - 1 - j)| *
              (18 / (k : ℝ) * cK2 * |phiG α (δ_coord m t - ε_coord m f j a)|)) := by ring
          linarith only [h4, hsimp, hgoal_eq, hnn, hass]
        calc ∑ t ∈ T_box j, _
            ≤ (1e13 * L ^ 3 / ((k : ℝ) * sqrt k)) * (cM1 * cC2 * cK1 * cK2) *
                exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
                ∑ t ∈ T_box j, exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) := by
              rw [mul_sum]; exact sum_le_sum ht_le
          _ ≤ (1e13 * L ^ 3 / ((k : ℝ) * sqrt k)) * (cM1 * cC2 * cK1 * cK2) *
                exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) * (10 * sqrt k) :=
              mL (hsum_exp_t j _) (by positivity)
          _ = (1e14 * L ^ 3 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
              field_simp [hsq_pos.ne', hk_pos.ne']; ring
      calc ∑ j ∈ J_box, |∑ a ∈ A_box j, ∑ t ∈ T_box j, E2 j a t|
          ≤ ∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, |E2 j a t| :=
            sum_le_sum fun j _ => (abs_sum_le_sum_abs _ _).trans
              (sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)
        _ ≤ ∑ j ∈ J_box, ∑ a ∈ A_box j,
              (1e14 * L ^ 3 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) :=
            sum_le_sum fun j hj => sum_le_sum fun a ha => hja2 j hj a ha
        _ = (1e14 * L ^ 3 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) *
            ∑ j ∈ J_box, ∑ a ∈ A_box j, exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
              rw [mul_sum]; refine sum_congr rfl fun j _ => by rw [mul_sum]
        _ ≤ (1e14 * L ^ 3 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * ((82 * sqrt k * L) * (10 * sqrt k)) := by
              apply mL _ (by positivity)
              calc ∑ j ∈ J_box, ∑ a ∈ A_box j, exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ))
                  ≤ ∑ _j ∈ J_box, (10 * sqrt k) := sum_le_sum fun j _ => hsum_exp_a j
                _ = (J_box.card : ℝ) * (10 * sqrt k) := by rw [sum_const, nsmul_eq_mul]
                _ ≤ (82 * sqrt k * L) * (10 * sqrt k) :=
                    mR hJ_card (by positivity)
        _ ≤ (1e17 * L ^ 4) * (cM1 * cC2 * cK1 * cK2) := by
              have hs : (1e14 * L ^ 3 / (k : ℝ)) * ((82 * sqrt k * L) * (10 * sqrt k)) = 8.2e16 * L ^ 4 := by
                calc (1e14 * L ^ 3 / (k : ℝ)) * ((82 * sqrt k * L) * (10 * sqrt k))
                    = (8.2e16 * L ^ 4 / (k : ℝ)) * (sqrt k * sqrt k) := by ring
                  _ = 8.2e16 * L ^ 4 := by rw [mul_self_sqrt hk_pos.le]; field_simp [hk_pos.ne']
              have hnn : 0 ≤ L ^ 4 * (cM1 * cC2 * cK1 * cK2) := by positivity
              have hl : (1e14 * L ^ 3 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * ((82 * sqrt k * L) * (10 * sqrt k)) =
                  (1e14 * L ^ 3 / (k : ℝ)) * ((82 * sqrt k * L) * (10 * sqrt k)) * (cM1 * cC2 * cK1 * cK2) := by ring
              rw [hl, hs]; linarith only [hnn]
    have hL47 : L ^ 4 ≤ L ^ 7 := pow_le_pow_right₀ hL1 (by omega)
    calc |∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, E2 j a t|
        ≤ (1e17 * L ^ 4) * (cM1 * cC2 * cK1 * cK2) := htot2
      _ ≤ (1e17 * L ^ 7) * (1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k)) :=
          mul_le_mul (mL hL47 (by norm_num)) hpref_le hpref_pos.le (by positivity)
      _ ≤ 1e21 * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
          have hnn : 0 ≤ (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by positivity
          have heq : (1e17 * L ^ 7) * (1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k)) =
              1e20 * ((L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2) := by ring
          linarith only [hnn, heq]
  have hStep3 : |S2 - S3| ≤ 1e22 * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
    let E3 (j a t : ℕ) : ℝ :=
      (1 / 2) * GM_val j a *
        (deltaK k a (f - a - d1) j (m - 1 - j) - (-18 / (k : ℝ)) * cK1 * phiG α (δ_coord m j - ε_coord m f j a)) *
        ((-18 / (k : ℝ)) * cK2 * phiG α (δ_coord m t - ε_coord m f j a))
    have hdiff : S2 - S3 = ∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, E3 j a t := by
      dsimp [S2, S3, E3]; simp_rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ => sum_congr rfl fun a _ => sum_congr rfl fun t _ => by ring
    rw [hdiff]
    have htot3 : |∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, E3 j a t| ≤
        (2e18 * L ^ 5) * (cM1 * cC2 * cK1 * cK2) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hja3 : ∀ j ∈ J_box, ∀ a ∈ A_box j,
          ∑ t ∈ T_box j, |E3 j a t| ≤
          (2e15 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
        intro j hj a ha
        have ha20 : |ε_coord m f j a| ≤ 20 * sqrt k * L := by
          have h1 := (mem_filter.mp ha).2; have hnn : 0 ≤ sqrt k * L := by positivity
          linarith only [h1, hnn]
        have hdkj := (deltaK_gaussian_approx hV hd1 (mem_filter.mp hj).2.2 ha20).2
        have hexp1 : exp (-α * (δ_coord m j - ε_coord m f j a) ^ 2) ≤ 1 :=
          exp_le_one_iff.mpr (by nlinarith only [hα_pos, sq_nonneg (δ_coord m j - ε_coord m f j a)])
        have hdkj' : |deltaK k a (f - a - d1) j (m - 1 - j) - (-18 / (k : ℝ)) * cK1 * phiG α (δ_coord m j - ε_coord m f j a)| ≤
            (2e13 * L ^ 4 / (k : ℝ)) * cK1 := by
          have h1 := mL hexp1 hc1.1.le
          have h2 := mL (by linarith only [h1] : cK1 * exp _ ≤ cK1)
            (show 0 ≤ (2e13 : ℝ) * (L ^ 4 / (k : ℝ)) by positivity)
          have h3 : (2e13 : ℝ) * (L ^ 4 / (k : ℝ)) * cK1 = (2e13 * L ^ 4 / (k : ℝ)) * cK1 := by ring
          linarith only [hdkj, h2, h3]
        have hcK1_pos : 0 < cK1 := hc1.1
        have hcK2_pos : 0 < cK2 := hc2.1
        have hL_nn : 0 ≤ L := by linarith only [hL1]
        have ht_le : ∀ t ∈ T_box j,
            |E3 j a t| ≤
            (2e14 * L ^ 4 / ((k : ℝ) * sqrt k)) * (cM1 * cC2 * cK1 * cK2) *
              exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
              exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) := by
          intro t _
          dsimp [E3]
          have hGM_nn : 0 ≤ GM_val j a := by dsimp [GM_val]; have := hc1.2.2.1; have := hc2.2.2.2.2.1; positivity
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
            abs_of_nonneg hGM_nn, abs_mul, abs_mul, abs_div, abs_neg,
            abs_of_pos (by norm_num : (0 : ℝ) < 18), abs_of_pos hk_pos, abs_of_pos hcK2_pos]
          have h1 := mL hdkj' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hGM_nn)
          have h2 := mL (hphi_le (δ_coord m t - ε_coord m f j a)) (by positivity : 0 ≤ 18 / (k : ℝ) * cK2)
          have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
          have hy_rew : δ_coord m t - ε_coord m f j a = (t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a) := by dsimp [δ_coord]; ring
          have hsimp : 1 / 2 * GM_val j a * ((2e13 * L ^ 4 / (k : ℝ)) * cK1) *
              (18 / (k : ℝ) * cK2 * (sqrt k * exp (-α * (δ_coord m t - ε_coord m f j a) ^ 2 / 2))) =
              1.8e14 * (L ^ 4 / ((k : ℝ) * sqrt k) * (cM1 * cC2 * cK1 * cK2) *
                exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
                exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2)) := by
            dsimp [GM_val]; rw [hy_rew]
            calc 1 / 2 * (cM1 * cC2 * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ))) *
                  ((2e13 * L ^ 4 / (k : ℝ)) * cK1) *
                  (18 / (k : ℝ) * cK2 * (sqrt k * exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2)))
                = (1.8e14 * L ^ 4 * sqrt k / ((k : ℝ) * (sqrt k * sqrt k))) *
                  (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
                  exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) := by
                    rw [mul_self_sqrt hk_pos.le]; ring
              _ = 1.8e14 * (L ^ 4 / ((k : ℝ) * sqrt k) * (cM1 * cC2 * cK1 * cK2) *
                  exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
                  exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2)) := by
                    field_simp [hk_pos.ne', hsq_pos.ne']
          have hgoal_eq : (2e14 * L ^ 4 / ((k : ℝ) * sqrt k)) * (cM1 * cC2 * cK1 * cK2) *
              exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
              exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) =
              2e14 * (L ^ 4 / ((k : ℝ) * sqrt k) * (cM1 * cC2 * cK1 * cK2) *
                exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
                exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2)) := by ring
          have hnn : 0 ≤ L ^ 4 / ((k : ℝ) * sqrt k) * (cM1 * cC2 * cK1 * cK2) *
              exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
              exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) := by positivity
          linarith only [h3, hsimp, hgoal_eq, hnn]
        calc ∑ t ∈ T_box j, _
            ≤ (2e14 * L ^ 4 / ((k : ℝ) * sqrt k)) * (cM1 * cC2 * cK1 * cK2) *
                exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
                ∑ t ∈ T_box j, exp (-α * ((t : ℝ) - ((m : ℝ) / 2 + ε_coord m f j a)) ^ 2 / 2) := by
              rw [mul_sum]; exact sum_le_sum ht_le
          _ ≤ (2e14 * L ^ 4 / ((k : ℝ) * sqrt k)) * (cM1 * cC2 * cK1 * cK2) *
                exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) * (10 * sqrt k) :=
              mL (hsum_exp_t j _) (by positivity)
          _ = (2e15 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
              field_simp [hsq_pos.ne', hk_pos.ne']; ring
      calc ∑ j ∈ J_box, |∑ a ∈ A_box j, ∑ t ∈ T_box j, E3 j a t|
          ≤ ∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, |E3 j a t| :=
            sum_le_sum fun j _ => (abs_sum_le_sum_abs _ _).trans
              (sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)
        _ ≤ ∑ j ∈ J_box, ∑ a ∈ A_box j,
              (2e15 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) :=
            sum_le_sum fun j hj => sum_le_sum fun a ha => hja3 j hj a ha
        _ = (2e15 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) *
            ∑ j ∈ J_box, ∑ a ∈ A_box j, exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) := by
              rw [mul_sum]; refine sum_congr rfl fun j _ => by rw [mul_sum]
        _ ≤ (2e15 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * ((82 * sqrt k * L) * (10 * sqrt k)) := by
              apply mL _ (by positivity)
              calc ∑ j ∈ J_box, ∑ a ∈ A_box j, exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ))
                  ≤ ∑ _j ∈ J_box, (10 * sqrt k) := sum_le_sum fun j _ => hsum_exp_a j
                _ = (J_box.card : ℝ) * (10 * sqrt k) := by rw [sum_const, nsmul_eq_mul]
                _ ≤ (82 * sqrt k * L) * (10 * sqrt k) :=
                    mR hJ_card (by positivity)
        _ ≤ (2e18 * L ^ 5) * (cM1 * cC2 * cK1 * cK2) := by
              have hs : (2e15 * L ^ 4 / (k : ℝ)) * ((82 * sqrt k * L) * (10 * sqrt k)) = 1.64e18 * L ^ 5 := by
                calc (2e15 * L ^ 4 / (k : ℝ)) * ((82 * sqrt k * L) * (10 * sqrt k))
                    = (1.64e18 * L ^ 5 / (k : ℝ)) * (sqrt k * sqrt k) := by ring
                  _ = 1.64e18 * L ^ 5 := by rw [mul_self_sqrt hk_pos.le]; field_simp [hk_pos.ne']
              have hnn : 0 ≤ L ^ 5 * (cM1 * cC2 * cK1 * cK2) := by positivity
              have hl : (2e15 * L ^ 4 / (k : ℝ)) * (cM1 * cC2 * cK1 * cK2) * ((82 * sqrt k * L) * (10 * sqrt k)) =
                  (2e15 * L ^ 4 / (k : ℝ)) * ((82 * sqrt k * L) * (10 * sqrt k)) * (cM1 * cC2 * cK1 * cK2) := by ring
              rw [hl, hs]; linarith only [hnn]
    have hL57 : L ^ 5 ≤ L ^ 7 := pow_le_pow_right₀ hL1 (by omega)
    calc |∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j, E3 j a t|
        ≤ (2e18 * L ^ 5) * (cM1 * cC2 * cK1 * cK2) := htot3
      _ ≤ (2e18 * L ^ 7) * (1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k)) :=
          mul_le_mul (mL hL57 (by norm_num)) hpref_le hpref_pos.le (by positivity)
      _ ≤ 1e22 * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
          have hnn : 0 ≤ (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by positivity
          have heq : (2e18 * L ^ 7) * (1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k)) =
              2e21 * ((L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2) := by ring
          linarith only [hnn, heq]
  have hStep4 : |S3| ≤ 1e11 * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
    let ε_of_E (E : ℕ) : ℝ := ((E : ℝ) - (3 * (f : ℝ) + m) / 2) / 3
    let c_of_E (E : ℕ) : ℝ := (m : ℝ) / 2 + ε_of_E E
    let E_box : Finset ℕ := (range (3 * f + m + 1)).filter (fun E => |ε_of_E E| ≤ 10 * sqrt k * L)
    have hD0_le_sqL : (D0 : ℝ) ≤ sqrt k * L := by
      have h1 : L ^ 6 / sqrt k ≤ 1 := by have := hLpow_tiny 6 (by omega); linarith only [this]
      have h2 := (div_le_iff₀ hsq_pos).mp h1
      have h3 := mR h2 (by linarith only [hL10] : 0 ≤ L)
      rw [show L ^ 6 * L = L ^ 7 by ring, one_mul] at h3
      exact hD0_le.trans h3
    have hJ_lo_le_hiD0 : J_lo ≤ J_hi - D0 := by
      have hlo_lt : (J_lo : ℝ) < (m : ℝ) / 2 - 40 * sqrt k * L + 1 :=
        Nat.ceil_lt_add_one (by linarith only [hm_lo_sub])
      have hhi_gt : (m : ℝ) / 2 + 40 * sqrt k * L < (J_hi : ℝ) := by
        dsimp [J_hi]; push_cast; exact Nat.lt_floor_add_one _
      have h1sqL : (1 : ℝ) ≤ sqrt k * L := by
        have := mul_le_mul hsq_ge1 hL10 (by norm_num) hsq_pos.le; linarith only [this]
      have hR : (J_lo : ℝ) + D0 ≤ (J_hi : ℝ) := by linarith only [hlo_lt, hhi_gt, hD0_le_sqL, h1sqL]
      have hN : J_lo + D0 ≤ J_hi := by exact_mod_cast hR
      omega
    let innerE (E : ℕ) : ℝ :=
      let r0 : ℕ := (m + 3 - E % 3) % 3
      let q0 : ℕ := (J_lo - r0 + 2) / 3
      let q1 : ℕ := (J_hi - D0 - r0 + 2) / 3
      ∑ q ∈ range (q1 - q0),
        phiG α (((r0 + 3 * (q0 + q) : ℕ) : ℝ) - c_of_E E) *
          ∑ t ∈ Ico (r0 + 3 * (q0 + q) + D0 + 1) J_hi, phiG α ((t : ℝ) - c_of_E E)
    have hS3_eq : S3 = (162 / (k : ℝ) ^ 2) * (cM1 * cC2 * cK1 * cK2) *
        ∑ E ∈ E_box, exp (-18 * (ε_of_E E) ^ 2 / (k : ℝ)) * innerE E := by
      have hS3_fact : S3 = (162 / (k : ℝ) ^ 2) * (cM1 * cC2 * cK1 * cK2) *
          ∑ j ∈ Ico J_lo (J_hi - D0), ∑ a ∈ A_box j,
            exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
              phiG α (δ_coord m j - ε_coord m f j a) *
              ∑ t ∈ Ico (j + D0 + 1) J_hi, phiG α (δ_coord m t - ε_coord m f j a) := by
        dsimp [S3, GM_val]
        have hstep1 : (∑ j ∈ J_box, ∑ a ∈ A_box j, ∑ t ∈ T_box j,
            1 / 2 * (cM1 * cC2 * exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ))) *
              (-18 / (k : ℝ) * cK1 * phiG α (δ_coord m j - ε_coord m f j a)) *
              (-18 / (k : ℝ) * cK2 * phiG α (δ_coord m t - ε_coord m f j a))) =
            (162 / (k : ℝ) ^ 2) * (cM1 * cC2 * cK1 * cK2) *
            ∑ j ∈ J_box, ∑ a ∈ A_box j,
              exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
              phiG α (δ_coord m j - ε_coord m f j a) *
              ∑ t ∈ Ico (j + D0 + 1) J_hi, phiG α (δ_coord m t - ε_coord m f j a) := by
          rw [mul_sum]
          refine sum_congr rfl fun j hj => ?_
          rw [mul_sum]
          refine sum_congr rfl fun a _ => ?_
          rw [hT_eq j hj, mul_sum, mul_sum]
          refine sum_congr rfl fun t _ => by ring
        rw [hstep1]; congr 1
        rw [hJ_eq]; symm
        apply sum_subset (Ico_subset_Ico_right (Nat.sub_le J_hi D0))
        intro j hj hnot
        rw [mem_Ico] at hj hnot
        have hemp : Ico (j + D0 + 1) J_hi = ∅ := Ico_eq_empty (by omega)
        simp [hemp]
      rw [hS3_fact]; congr 1
      let P1 := (Ico J_lo (J_hi - D0)).sigma A_box
      let P2 := E_box.sigma (fun E =>
        let r0 := (m + 3 - E % 3) % 3
        range ((J_hi - D0 - r0 + 2) / 3 - (J_lo - r0 + 2) / 3))
      have hP1 : ∑ j ∈ Ico J_lo (J_hi - D0), ∑ a ∈ A_box j,
          exp (-18 * (ε_coord m f j a) ^ 2 / (k : ℝ)) *
            phiG α (δ_coord m j - ε_coord m f j a) *
            ∑ t ∈ Ico (j + D0 + 1) J_hi, phiG α (δ_coord m t - ε_coord m f j a) =
          ∑ p ∈ P1,
            exp (-18 * (ε_coord m f p.1 p.2) ^ 2 / (k : ℝ)) *
              phiG α (δ_coord m p.1 - ε_coord m f p.1 p.2) *
              ∑ t ∈ Ico (p.1 + D0 + 1) J_hi, phiG α (δ_coord m t - ε_coord m f p.1 p.2) := by
        dsimp [P1]; rw [sum_sigma]
      have hP2 : ∑ E ∈ E_box, exp (-18 * (ε_of_E E) ^ 2 / (k : ℝ)) * innerE E =
          ∑ p ∈ P2,
            let r0 := (m + 3 - p.1 % 3) % 3
            let j := r0 + 3 * ((J_lo - r0 + 2) / 3 + p.2)
            exp (-18 * (ε_of_E p.1) ^ 2 / (k : ℝ)) *
              phiG α ((j : ℝ) - c_of_E p.1) *
              ∑ t ∈ Ico (j + D0 + 1) J_hi, phiG α ((t : ℝ) - c_of_E p.1) := by
        rw [sum_sigma]
        refine sum_congr rfl fun E _ => ?_
        dsimp [innerE]; rw [mul_sum]
        refine sum_congr rfl fun q _ => by ring
      rw [hP1, hP2]
      refine sum_bij (fun p _ =>
        let E := 3 * p.2 + m - p.1
        let r0 := (m + 3 - E % 3) % 3
        ⟨E, (p.1 - r0) / 3 - (J_lo - r0 + 2) / 3⟩) ?_ ?_ ?_ ?_
      · intro ⟨j, a⟩ hp
        simp only [P1, P2, mem_sigma, mem_Ico, A_box, E_box, mem_filter, mem_range] at hp ⊢
        have hjm : j ≤ m := by omega
        have hE_cast : ((3 * a + m - j : ℕ) : ℝ) = 3 * (a : ℝ) + m - j := by
          rw [Nat.cast_sub (by omega : j ≤ 3 * a + m)]; push_cast; ring
        have hε_eq : ε_of_E (3 * a + m - j) = ε_coord m f j a := by
          dsimp [ε_of_E, ε_coord]; rw [hE_cast]; ring
        refine ⟨⟨by omega, by rw [hε_eq]; exact hp.2.2⟩, ?_⟩
        have hr0_mod : j % 3 = (m + 3 - (3 * a + m - j) % 3) % 3 := by omega
        have hr0_le : (m + 3 - (3 * a + m - j) % 3) % 3 ≤ J_lo := by omega
        omega
      · intro ⟨j1, a1⟩ hp1 ⟨j2, a2⟩ hp2 heq
        simp only [P1, mem_sigma, mem_Ico] at hp1 hp2
        have hE : 3 * a1 + m - j1 = 3 * a2 + m - j2 := congrArg Sigma.fst heq
        have hq : (j1 - (m + 3 - (3 * a1 + m - j1) % 3) % 3) / 3 -
            (J_lo - (m + 3 - (3 * a1 + m - j1) % 3) % 3 + 2) / 3 =
            (j2 - (m + 3 - (3 * a2 + m - j2) % 3) % 3) / 3 -
            (J_lo - (m + 3 - (3 * a2 + m - j2) % 3) % 3 + 2) / 3 := by
          have h2 := (Sigma.mk.inj_iff.mp heq).2
          dsimp only at h2
          exact eq_of_heq h2
        have hj_eq : j1 = j2 := by
          have hr1 : j1 % 3 = (m + 3 - (3 * a1 + m - j1) % 3) % 3 := by omega
          have hr2 : j2 % 3 = (m + 3 - (3 * a2 + m - j2) % 3) % 3 := by omega
          rw [hE] at hr1 hq; omega
        have ha_eq : a1 = a2 := by omega
        subst hj_eq; subst ha_eq; rfl
      · intro ⟨E, q⟩ hp
        simp only [P1, P2, mem_sigma, mem_Ico, A_box, E_box, mem_filter, mem_range] at hp ⊢
        let r0 := (m + 3 - E % 3) % 3
        let j := r0 + 3 * ((J_lo - r0 + 2) / 3 + q)
        have hj_bounds : J_lo ≤ j ∧ j < J_hi - D0 := by dsimp [j, r0]; omega
        have hj_box : |δ_coord m j| ≤ 40 * sqrt k * L := by
          have hj_in : j ∈ J_box := by rw [hJ_eq, mem_Ico]; omega
          exact (mem_filter.mp hj_in).2.2
        have hE_ge : m ≤ E + j := by
          have h1 : (E : ℝ) = (3 * (f : ℝ) + m) / 2 + 3 * ε_of_E E := by dsimp [ε_of_E]; ring
          have h2 : (j : ℝ) = (m : ℝ) / 2 + δ_coord m j := by dsimp [δ_coord]; ring
          have hR : (m : ℝ) ≤ (E : ℝ) + j := by
            linarith only [h1, h2, (abs_le.mp hp.1.2).1, (abs_le.mp hj_box).1, hba.2.2.1, hsqL, hkR]
          exact_mod_cast hR
        let a := (E + j - m) / 3
        have h3a : 3 * a = E + j - m := by dsimp [a, j, r0]; omega
        have ha_le_f : a < f + 1 := by
          have h1 : (E : ℝ) = (3 * (f : ℝ) + m) / 2 + 3 * ε_of_E E := by dsimp [ε_of_E]; ring
          have h2 : (j : ℝ) = (m : ℝ) / 2 + δ_coord m j := by dsimp [δ_coord]; ring
          have h3aR : (3 : ℝ) * a = (E : ℝ) + j - m := by
            have hnat : 3 * a + m = E + j := by omega
            have hR : ((3 * a + m : ℕ) : ℝ) = ((E + j : ℕ) : ℝ) := by exact_mod_cast hnat
            push_cast at hR; linarith only [hR]
          have hR : (a : ℝ) < (f : ℝ) + 1 := by
            linarith only [h3aR, h1, h2, (abs_le.mp hp.1.2).2, (abs_le.mp hj_box).2, hba.2.2.1, hsqL, hkR]
          exact_mod_cast hR
        have hE_rec : 3 * a + m - j = E := by omega
        have hε_eq : ε_coord m f j a = ε_of_E E := by
          have hE_cast : (E : ℝ) = 3 * (a : ℝ) + m - j := by
            have hnat : E + j = 3 * a + m := by omega
            have hR : ((E + j : ℕ) : ℝ) = ((3 * a + m : ℕ) : ℝ) := by exact_mod_cast hnat
            push_cast at hR; linarith only [hR]
          dsimp [ε_of_E, ε_coord]; rw [hE_cast]; ring
        refine ⟨⟨j, a⟩, ⟨hj_bounds, ha_le_f, by rw [hε_eq]; exact hp.1.2⟩, ?_⟩
        refine Sigma.ext hE_rec ?_
        rw [heq_eq_eq]
        dsimp [j, r0]; rw [hE_rec]; omega
      · intro ⟨j, a⟩ hp
        simp only [P1, mem_sigma, mem_Ico] at hp
        let E := 3 * a + m - j
        let r0 := (m + 3 - E % 3) % 3
        have hj_rec : r0 + 3 * ((J_lo - r0 + 2) / 3 + ((j - r0) / 3 - (J_lo - r0 + 2) / 3)) = j := by
          have : j % 3 = r0 := by dsimp [r0, E]; omega
          omega
        have hE_cast : (E : ℝ) = 3 * (a : ℝ) + m - j := by
          dsimp [E]; rw [Nat.cast_sub (by omega : j ≤ 3 * a + m)]; push_cast; ring
        have hε_eq : ε_coord m f j a = ε_of_E E := by dsimp [ε_of_E, ε_coord]; rw [hE_cast]; ring
        have hdj_eq : δ_coord m j - ε_of_E E = (j : ℝ) - c_of_E E := by
          dsimp [δ_coord, c_of_E]; ring
        have hdt_eq : ∀ t : ℕ, δ_coord m t - ε_of_E E = (t : ℝ) - c_of_E E := fun t => by
          dsimp [δ_coord, c_of_E]; ring
        dsimp only
        rw [show r0 + 3 * ((J_lo - r0 + 2) / 3 + ((j - r0) / 3 - (J_lo - r0 + 2) / 3)) = j from hj_rec,
          hε_eq, hdj_eq]
        congr 1; refine sum_congr rfl fun t _ => by rw [hdt_eq t]
    have hinner_le : ∀ E ∈ E_box, |innerE E| ≤ 8000 * L ^ 7 * ((k : ℝ) * sqrt k) := by
      intro E hE
      have hEε : |ε_of_E E| ≤ 10 * sqrt k * L := (mem_filter.mp hE).2
      let r0 : ℕ := (m + 3 - E % 3) % 3
      let q0 : ℕ := (J_lo - r0 + 2) / 3
      let q1 : ℕ := (J_hi - D0 - r0 + 2) / 3
      let Q : ℕ := q1 - q0
      have hα18 : 18 * α ≤ 1 := by
        dsimp [α, αk_val]; rw [mul_div_assoc', div_le_one (by positivity)]; linarith only [hkR]
      have hT2 : ∀ q < Q, r0 + 3 * (q0 + q) + D0 + 1 ≤ J_hi := by
        intro q hq; dsimp [Q, q1, q0, r0] at hq ⊢; omega
      have hdb := double_odd_gaussian_sum_bound hα_pos hα18 (c_of_E E) D0 r0 q0 Q J_hi hT2
      have hbdy : ∀ x : ℝ, 20 * sqrt k * L ≤ |x| → exp (-α * x ^ 2) ≤ exp (-L ^ 2) := fun x hx => by
        apply exp_le_exp.mpr
        have hsq : 400 * (k : ℝ) * L ^ 2 ≤ x ^ 2 := by
          have h1 := pow_le_pow_left₀ (by positivity) hx 2
          rw [sq_abs, mul_pow, mul_pow, sq_sqrt hk_pos.le] at h1; linarith only [h1]
        have h1 : α * x ^ 2 ≥ 900 * L ^ 2 := by
          have hm := mL hsq hα_pos.le
          have hs : α * (400 * (k : ℝ) * L ^ 2) = 900 * L ^ 2 := by dsimp [α, αk_val]; field_simp [hk_pos.ne']; ring
          linarith only [hm, hs]
        have hL2nn : 0 ≤ L ^ 2 := sq_nonneg L
        linarith only [h1, hL2nn]
      have h1sqL : (10 : ℝ) ≤ sqrt k * L := by
        have := mul_le_mul hsq_ge1 hL10 (by norm_num) hsq_pos.le; linarith only [this]
      have hxlo : 20 * sqrt k * L ≤ |((r0 + 3 * q0 : ℕ) : ℝ) - c_of_E E| := by
        have h1 : r0 + 3 * q0 ≤ J_lo + 2 := by dsimp [q0, r0]; omega
        have h1R : ((r0 + 3 * q0 : ℕ) : ℝ) ≤ (J_lo : ℝ) + 2 := by exact_mod_cast h1
        have hlo_lt : (J_lo : ℝ) < (m : ℝ) / 2 - 40 * sqrt k * L + 1 :=
          Nat.ceil_lt_add_one (by linarith only [hm_lo_sub])
        have hneg : ((r0 + 3 * q0 : ℕ) : ℝ) - c_of_E E ≤ -(20 * sqrt k * L) := by
          dsimp [c_of_E]; linarith only [h1R, hlo_lt, (abs_le.mp hEε).1, h1sqL]
        exact (by linarith only [hneg] : 20 * sqrt k * L ≤ -(((r0 + 3 * q0 : ℕ) : ℝ) - c_of_E E)).trans
          (neg_le_abs _)
      have hxhi : 20 * sqrt k * L ≤ |((r0 + 3 * (q0 + Q) : ℕ) : ℝ) - c_of_E E| := by
        have hq01 : q0 ≤ q1 := by dsimp [q0, q1]; omega
        have h1 : J_hi - D0 ≤ r0 + 3 * (q0 + Q) := by dsimp [Q, q1, q0, r0]; omega
        have h1R : (J_hi : ℝ) - D0 ≤ ((r0 + 3 * (q0 + Q) : ℕ) : ℝ) := by
          have : J_hi ≤ r0 + 3 * (q0 + Q) + D0 := by omega
          have hR : (J_hi : ℝ) ≤ ((r0 + 3 * (q0 + Q) + D0 : ℕ) : ℝ) := by exact_mod_cast this
          push_cast at hR ⊢; linarith only [hR]
        have hhi_gt : (m : ℝ) / 2 + 40 * sqrt k * L < (J_hi : ℝ) := by
          dsimp [J_hi]; push_cast; exact Nat.lt_floor_add_one _
        have hpos : 20 * sqrt k * L ≤ ((r0 + 3 * (q0 + Q) : ℕ) : ℝ) - c_of_E E := by
          dsimp [c_of_E]; linarith only [h1R, hhi_gt, hD0_le_sqL, (abs_le.mp hEε).2, h1sqL]
        exact hpos.trans (le_abs_self _)
      have hyhi : 20 * sqrt k * L ≤ |(J_hi : ℝ) - c_of_E E| := by
        have hhi_gt : (m : ℝ) / 2 + 40 * sqrt k * L < (J_hi : ℝ) := by
          dsimp [J_hi]; push_cast; exact Nat.lt_floor_add_one _
        have hpos : 20 * sqrt k * L ≤ (J_hi : ℝ) - c_of_E E := by
          dsimp [c_of_E]; linarith only [hhi_gt, (abs_le.mp hEε).2, h1sqL]
        exact hpos.trans (le_abs_self _)
      have hα_den : 1 / (α * sqrt α) ≤ (k : ℝ) * sqrt k := by
        have hsqα : sqrt α = 3 / (2 * sqrt k) := by
          dsimp [α, αk_val]
          rw [sqrt_div (by norm_num), sqrt_mul (by norm_num),
            show sqrt 9 = 3 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num)],
            show sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
        rw [hsqα]; dsimp [α, αk_val]
        have heq : 1 / (9 / (4 * (k : ℝ)) * (3 / (2 * sqrt k))) = (8 / 27) * ((k : ℝ) * sqrt k) := by
          field_simp [hk_pos.ne', hsq_pos.ne']; ring
        rw [heq]; have hnn : 0 ≤ (k : ℝ) * sqrt k := by positivity
        linarith only [hnn]
      have hterm1 : 3000 * ((D0 : ℝ) + 1) / (α * sqrt α) ≤ 6000 * L ^ 7 * ((k : ℝ) * sqrt k) := by
        have hD1 : (D0 : ℝ) + 1 ≤ 2 * L ^ 7 := by
          have h1 : (1 : ℝ) ≤ L ^ 7 := by simpa only [one_pow] using pow_le_pow_left₀ (by norm_num) hL1 7
          linarith only [hD0_le, h1]
        rw [div_eq_mul_one_div]
        have hm := mul_le_mul (mL hD1 (by norm_num : (0 : ℝ) ≤ 3000))
          hα_den (by positivity) (by positivity)
        linarith only [hm]
      have hterm2 : (100 / α ^ 2) * (exp (-α * (((r0 + 3 * q0 : ℕ) : ℝ) - c_of_E E) ^ 2) +
          exp (-α * (((r0 + 3 * (q0 + Q) : ℕ) : ℝ) - c_of_E E) ^ 2) +
          exp (-α * ((J_hi : ℝ) - c_of_E E) ^ 2)) ≤ 2000 * L ^ 7 * ((k : ℝ) * sqrt k) := by
        have hsum3 : exp (-α * (((r0 + 3 * q0 : ℕ) : ℝ) - c_of_E E) ^ 2) +
            exp (-α * (((r0 + 3 * (q0 + Q) : ℕ) : ℝ) - c_of_E E) ^ 2) +
            exp (-α * ((J_hi : ℝ) - c_of_E E) ^ 2) ≤ 3 * exp (-L ^ 2) := by
          linarith only [hbdy _ hxlo, hbdy _ hxhi, hbdy _ hyhi]
        have h100 : (100 / α ^ 2) * (3 * exp (-L ^ 2)) ≤ 1 := by
          have heq : 100 / α ^ 2 = (1600 / 81) * (k : ℝ) ^ 2 := by dsimp [α, αk_val]; field_simp [hk_pos.ne']; ring
          rw [heq]
          have hk2 : (1600 / 81 : ℝ) * (k : ℝ) ^ 2 * 3 ≤ (k : ℝ) ^ 10 := by
            have h1 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 9 := pow_le_pow_right₀ (by linarith only [hkR]) (by omega)
            have h2 : 100 * (k : ℝ) ^ 9 ≤ (k : ℝ) ^ 10 := by
              rw [show (k : ℝ) ^ 10 = (k : ℝ) * (k : ℝ) ^ 9 by ring]
              exact mR (by linarith only [hkR]) (pow_nonneg hk_pos.le 9)
            have hnn : 0 ≤ (k : ℝ) ^ 9 := pow_nonneg hk_pos.le 9
            linarith only [h1, h2, hnn]
          have hm := mR hk2 (exp_pos (-L ^ 2)).le
          linarith only [hm, hexpL]
        have hbig : (1 : ℝ) ≤ 2000 * L ^ 7 * ((k : ℝ) * sqrt k) := by
          have h1 : (1 : ℝ) ≤ L ^ 7 := by simpa only [one_pow] using pow_le_pow_left₀ (by norm_num) hL1 7
          have h2 : (1 : ℝ) ≤ (k : ℝ) * sqrt k := by nlinarith only [hkR, hsq_ge1]
          nlinarith only [h1, h2]
        exact (mL hsum3 (by positivity)).trans (h100.trans hbig)
      exact hdb.trans (by linarith only [hterm1, hterm2])
    have hsum_E : ∑ E ∈ E_box, exp (-18 * (ε_of_E E) ^ 2 / (k : ℝ)) ≤ 10 * sqrt k := by
      have hsub : E_box ⊆ range (3 * f + m + 1) := filter_subset _ _
      have hrew : ∀ E : ℕ, exp (-18 * (ε_of_E E) ^ 2 / (k : ℝ)) =
          exp (-(2 / (k : ℝ)) * ((E : ℝ) - (3 * (f : ℝ) + m) / 2) ^ 2) := fun E => by
        dsimp [ε_of_E]; congr 1; ring
      simp_rw [hrew]
      have h1 := (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (exp_pos _).le)).trans
        (sum_exp_sq_of_step_ge_one (3 * f + m + 1) (fun E => (E : ℝ) - (3 * (f : ℝ) + m) / 2)
          (by positivity : 0 < 2 / (k : ℝ)) (fun E => by push_cast; linarith))
      have hinv : 1 / sqrt (2 / (k : ℝ)) ≤ sqrt k := by
        rw [div_le_iff₀ (sqrt_pos.mpr (by positivity)), ← sqrt_mul hk_pos.le,
          le_sqrt (by norm_num) (by positivity)]
        field_simp [hk_pos.ne']; norm_num
      have h4 : 4 / sqrt (2 / (k : ℝ)) = 4 * (1 / sqrt (2 / (k : ℝ))) := by ring
      linarith only [h1, h4, hinv, hsq_ge1]
    rw [hS3_eq, abs_mul, abs_of_pos (by positivity : 0 < (162 / (k : ℝ) ^ 2) * (cM1 * cC2 * cK1 * cK2))]
    have hsum_tot : |∑ E ∈ E_box, exp (-18 * (ε_of_E E) ^ 2 / (k : ℝ)) * innerE E| ≤
        (10 * sqrt k) * (8000 * L ^ 7 * ((k : ℝ) * sqrt k)) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ E ∈ E_box, |exp (-18 * (ε_of_E E) ^ 2 / (k : ℝ)) * innerE E|
          ≤ ∑ E ∈ E_box, exp (-18 * (ε_of_E E) ^ 2 / (k : ℝ)) *
              (8000 * L ^ 7 * ((k : ℝ) * sqrt k)) := by
            apply sum_le_sum; intro E hE
            rw [abs_mul, abs_of_pos (exp_pos _)]
            exact mL (hinner_le E hE) (exp_pos _).le
        _ = (∑ E ∈ E_box, exp (-18 * (ε_of_E E) ^ 2 / (k : ℝ))) *
              (8000 * L ^ 7 * ((k : ℝ) * sqrt k)) := (sum_mul _ _ _).symm
        _ ≤ (10 * sqrt k) * (8000 * L ^ 7 * ((k : ℝ) * sqrt k)) :=
            mR hsum_E (by positivity)
    have hsimp4 : (162 / (k : ℝ) ^ 2) * ((10 * sqrt k) * (8000 * L ^ 7 * ((k : ℝ) * sqrt k))) =
        1.296e7 * L ^ 7 := by
      calc (162 / (k : ℝ) ^ 2) * ((10 * sqrt k) * (8000 * L ^ 7 * ((k : ℝ) * sqrt k)))
          = 1.296e7 * L ^ 7 * ((k : ℝ) * (sqrt k * sqrt k)) / (k : ℝ) ^ 2 := by ring
        _ = 1.296e7 * L ^ 7 := by rw [mul_self_sqrt hk_pos.le]; field_simp [hk_pos.ne']
    calc (162 / (k : ℝ) ^ 2) * (cM1 * cC2 * cK1 * cK2) *
          |∑ E ∈ E_box, exp (-18 * (ε_of_E E) ^ 2 / (k : ℝ)) * innerE E|
        ≤ (162 / (k : ℝ) ^ 2) * (cM1 * cC2 * cK1 * cK2) *
          ((10 * sqrt k) * (8000 * L ^ 7 * ((k : ℝ) * sqrt k))) :=
          mL hsum_tot (by positivity)
      _ = (1.296e7 * L ^ 7) * (cM1 * cC2 * cK1 * cK2) := by rw [← hsimp4]; ring
      _ ≤ (1.296e7 * L ^ 7) * (1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k)) :=
          mL hpref_le (by positivity)
      _ ≤ 1e11 * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
          have hnn : 0 ≤ (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by positivity
          have heq : (1.296e7 * L ^ 7) * (1000 * N0 * B0 ^ 2 / ((k : ℝ) * sqrt k)) =
              1.296e10 * ((L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2) := by ring
          linarith only [hnn, heq]
  have hS0_split : S0 = (S0 - S1) + (S1 - S2) + (S2 - S3) + S3 := by ring
  change |S0| ≤ _
  rw [hS0_split]
  have htri4 : |(S0 - S1) + (S1 - S2) + (S2 - S3) + S3| ≤ |S0 - S1| + |S1 - S2| + |S2 - S3| + |S3| :=
    (abs_add_le _ _).trans (add_le_add (abs_add3_le _ _ _) le_rfl)
  have hnn : 0 ≤ (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by positivity
  linarith only [htri4, hStep1, hStep2, hStep3, hStep4, hnn]

set_option maxHeartbeats 1200000 in
private lemma regime2_mf_bound {k m f : ℕ} (hV : ValidMF k m f) :
    let D0 : ℕ := ⌊log k ^ 7⌋₊
    |∑ w ∈ (allLists m).filter (fun w => cnt w = f),
      ∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
        A_val k w j * A_val k w t| ≤
      (1e25 : ℝ) * (log k ^ 7 / ((k : ℝ) * sqrt k)) *
        (((m + 1).choose (2 * f + 1) : ℕ) : ℝ) *
        (((2 * k + 1 + f).choose m : ℕ) : ℝ) ^ 2 := by
  intro D0
  classical
  let L : ℝ := log k
  let B0 : ℝ := (((2 * k + 1 + f).choose m : ℕ) : ℝ)
  let N0 : ℝ := (((m + 1).choose (2 * f + 1) : ℕ) : ℝ)
  have hba := validMF_eta_bounds hV
  have ⟨hk, hL, _, _, _, _⟩ := hV
  have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < k := by positivity
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hL10 : (10 : ℝ) ≤ L := by linarith only [hL]
  have hD0_ge : 100 ≤ D0 := by
    have h1 : (100 : ℝ) ≤ L ^ 7 := by have := pow_le_pow_left₀ (by norm_num) hL10 7; linarith only [this]
    exact Nat.le_floor h1
  have hm_ge1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith only [hba.1, hkR]
    exact_mod_cast this
  have hswap :
      (∑ w ∈ (allLists m).filter (fun w => cnt w = f),
        ∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + D0 < t), A_val k w j * A_val k w t) =
      ∑ d1 ∈ ({0, 1} : Finset ℕ), ∑ d2 ∈ ({0, 1} : Finset ℕ),
        ∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
          ∑ a ∈ range (f + 1),
            ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
              ((j.choose (2 * a + d1) * (t - j - 1).choose (2 * (b - a - d1) + d2) *
                (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) *
              deltaK k a (f - a - d1) j (m - 1 - j) *
              deltaK k b (f - b - d2) t (m - 1 - t) := by
    rw [sum_comm]
    have hdrop0 : (∑ j ∈ range m, ∑ w ∈ (allLists m).filter (fun w => cnt w = f),
        ∑ t ∈ (range m).filter (fun t => j + D0 < t), A_val k w j * A_val k w t) =
        ∑ j ∈ Ico 1 m, ∑ w ∈ (allLists m).filter (fun w => cnt w = f),
        ∑ t ∈ (range m).filter (fun t => j + D0 < t), A_val k w j * A_val k w t := by
      symm
      apply sum_subset (by intro j hj; rw [mem_Ico] at hj; exact mem_range.mpr hj.2)
      intro j hj hnot
      have hj0 : j = 0 := by rw [mem_range] at hj; rw [mem_Ico] at hnot; omega
      subst hj0
      apply sum_eq_zero; intro w hw
      have hw' := mem_filter.mp hw
      have hlen : w.length = m := mem_allLists_iff.mp hw'.1
      have hlt : k + 1 + cnt w < w.length - 1 := by
        rw [hlen, hw'.2]
        have : (k : ℝ) + 1 + f < (m : ℝ) - 1 := by linarith only [hba.1, hba.2.2.2.1, hkR]
        have hnat : k + 1 + f + 1 < m := by
          exact_mod_cast (by push_cast; linarith only [this] : ((k + 1 + f + 1 : ℕ) : ℝ) < m)
        omega
      simp [A_val_zero_eq_zero k w hlt]
    rw [hdrop0]
    have hinner : ∀ j ∈ Ico 1 m,
        (∑ w ∈ (allLists m).filter (fun w => cnt w = f),
          ∑ t ∈ (range m).filter (fun t => j + D0 < t), A_val k w j * A_val k w t) =
        ∑ t ∈ (range m).filter (fun t => j + D0 < t),
          ∑ d1 ∈ ({0, 1} : Finset ℕ), ∑ d2 ∈ ({0, 1} : Finset ℕ),
            ∑ a ∈ range (f + 1),
              ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
                ((j.choose (2 * a + d1) * (t - j - 1).choose (2 * (b - a - d1) + d2) *
                  (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) *
                deltaK k a (f - a - d1) j (m - 1 - j) *
                deltaK k b (f - b - d2) t (m - 1 - t) := by
      intro j hj; rw [sum_comm]
      refine sum_congr rfl fun t ht => ?_
      have hj1 := (mem_Ico.mp hj).1
      have ht' := mem_filter.mp ht
      exact sum_words_pair_eq_four_cases k m f j t hj1 (by omega) (mem_range.mp ht'.1)
    rw [sum_congr rfl hinner]
    simp_rw [sum_comm (s := (range m).filter _)]
    rw [sum_comm]; refine sum_congr rfl fun d1 _ => ?_
    rw [sum_comm]
  rw [hswap]
  have hcase : ∀ d1 ∈ ({0, 1} : Finset ℕ), ∀ d2 ∈ ({0, 1} : Finset ℕ),
      |∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
        ∑ a ∈ range (f + 1),
          ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
            ((j.choose (2 * a + d1) * (t - j - 1).choose (2 * (b - a - d1) + d2) *
              (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) *
            deltaK k a (f - a - d1) j (m - 1 - j) *
            deltaK k b (f - b - d2) t (m - 1 - t)| ≤
      (2e24 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
    intro d1 hd1 d2 hd2
    let term (j t a b : ℕ) : ℝ :=
      ((j.choose (2 * a + d1) * (t - j - 1).choose (2 * (b - a - d1) + d2) *
        (m - t).choose (2 * (f - b - d2) + 1) : ℕ) : ℝ) *
      deltaK k a (f - a - d1) j (m - 1 - j) *
      deltaK k b (f - b - d2) t (m - 1 - t)
    have hsplit : (∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
        ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f), term j t a b) =
        (∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
          ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
            if InBox k m f j t a b then term j t a b else 0) +
        (∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
          ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
            if InBox k m f j t a b then 0 else term j t a b) := by
      simp_rw [← sum_add_distrib]
      refine sum_congr rfl fun j _ => sum_congr rfl fun t _ =>
        sum_congr rfl fun a _ => sum_congr rfl fun b _ => by split_ifs <;> ring
    change |∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
      ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f), term j t a b| ≤ _
    rw [hsplit]
    have htri := abs_add_le
      (∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
        ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
          if InBox k m f j t a b then term j t a b else 0)
      (∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
        ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
          if InBox k m f j t a b then 0 else term j t a b)
    have hin : |∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
        ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
          if InBox k m f j t a b then term j t a b else 0| ≤
        (1e24 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
      have heq_box : (∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
          ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
            if InBox k m f j t a b then term j t a b else 0) =
          ∑ j ∈ (range m).filter (fun j => 1 ≤ j ∧ |δ_coord m j| ≤ 40 * sqrt k * L),
            ∑ a ∈ (range (f + 1)).filter (fun a => |ε_coord m f j a| ≤ 10 * sqrt k * L),
              ∑ t ∈ (range m).filter (fun t => j + D0 < t ∧ |δ_coord m t| ≤ 40 * sqrt k * L),
                ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f ∧
                  |(b : ℝ) - a - ((t : ℝ) - j) / 3| ≤ 20 * sqrt ((t - j - 1 : ℕ) : ℝ) * L),
                  term j t a b := by
        have hIco : Ico 1 m = (range m).filter (fun j => 1 ≤ j) := by
          ext j; simp only [mem_Ico, mem_filter, mem_range]; omega
        rw [hIco]
        have hstep : ∀ j ∈ (range m).filter (fun j => 1 ≤ j),
            (∑ t ∈ (range m).filter (fun t => j + D0 < t),
              ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
                if InBox k m f j t a b then term j t a b else 0) =
            if |δ_coord m j| ≤ 40 * sqrt k * L then
              ∑ a ∈ (range (f + 1)).filter (fun a => |ε_coord m f j a| ≤ 10 * sqrt k * L),
                ∑ t ∈ (range m).filter (fun t => j + D0 < t ∧ |δ_coord m t| ≤ 40 * sqrt k * L),
                  ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f ∧
                    |(b : ℝ) - a - ((t : ℝ) - j) / 3| ≤ 20 * sqrt ((t - j - 1 : ℕ) : ℝ) * L),
                    term j t a b
            else 0 := by
          intro j _
          by_cases hδj : |δ_coord m j| ≤ 40 * sqrt k * L
          · rw [if_pos hδj, sum_comm]
            conv_rhs => rw [sum_filter]
            refine sum_congr rfl fun a _ => ?_
            by_cases hεj : |ε_coord m f j a| ≤ 10 * sqrt k * L
            · rw [if_pos hεj]
              conv_rhs =>
                rw [show (range m).filter (fun t => j + D0 < t ∧ |δ_coord m t| ≤ 40 * sqrt k * L) =
                    ((range m).filter (fun t => j + D0 < t)).filter (fun t => |δ_coord m t| ≤ 40 * sqrt k * L) by
                      ext t; simp [and_assoc], sum_filter]
              refine sum_congr rfl fun t _ => ?_
              by_cases hδt : |δ_coord m t| ≤ 40 * sqrt k * L
              · rw [if_pos hδt]
                conv_rhs =>
                  rw [show (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f ∧
                      |(b : ℝ) - a - ((t : ℝ) - j) / 3| ≤ 20 * sqrt ((t - j - 1 : ℕ) : ℝ) * L) =
                      ((range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f)).filter
                        (fun (b : ℕ) => |(b : ℝ) - a - ((t : ℝ) - j) / 3| ≤ 20 * sqrt ((t - j - 1 : ℕ) : ℝ) * L) by
                        ext b; simp [and_assoc], sum_filter]
                refine sum_congr rfl fun b _ => ?_
                unfold InBox; dsimp only [L] at hδj hδt hεj ⊢; simp only [hδj, hδt, hεj, true_and]
              · rw [if_neg hδt]; apply sum_eq_zero; intro b _
                rw [if_neg]; intro h; exact hδt h.2.1
            · rw [if_neg hεj]; apply sum_eq_zero; intro t _
              apply sum_eq_zero; intro b _
              rw [if_neg]; intro h; exact hεj h.2.2.1
          · rw [if_neg hδj]; apply sum_eq_zero; intro t _
            apply sum_eq_zero; intro a _
            apply sum_eq_zero; intro b _
            rw [if_neg]; intro h; exact hδj h.1
        rw [sum_congr rfl hstep, ← sum_filter, filter_filter]
      rw [heq_box]
      exact regime2_in_box_bound hV hd1 hd2
    have hout : |∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
        ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
          if InBox k m f j t a b then 0 else term j t a b| ≤
        (1e24 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
      have hpt : ∀ j ∈ Ico 1 m, ∀ t ∈ (range m).filter (fun t => j + D0 < t),
          ∀ a ∈ range (f + 1), ∀ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
          |if InBox k m f j t a b then 0 else term j t a b| ≤ (1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2 := by
        intro j hj t ht a _ b hb
        by_cases h : InBox k m f j t a b
        · rw [if_pos h, abs_zero]; positivity
        · rw [if_neg h]; dsimp [term]
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          have hb' := (mem_filter.mp hb).2
          exact regime2_outside_box_pointwise hV hd1 hd2 (mem_Ico.mp hj).1 (mem_filter.mp ht).2
            (mem_range.mp (mem_filter.mp ht).1) hb'.1 hb'.2 h
      have hcard_prod : (m : ℝ) * (m : ℝ) * ((f + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ) ≤ 81 * (k : ℝ) ^ 4 := by
        have hm3 : (m : ℝ) ≤ 3 * k := by linarith only [hba.2.1, hk_pos]
        have hf3 : ((f + 1 : ℕ) : ℝ) ≤ 3 * k := by push_cast; linarith only [hba.2.2.2.1, hkR]
        have h1 := mul_le_mul hm3 hm3 (Nat.cast_nonneg m) (by positivity)
        have h2 := mul_le_mul hf3 hf3 (Nat.cast_nonneg (f + 1)) (by positivity)
        have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
        linarith only [h3]
      have hsum_out : |∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
          ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
            if InBox k m f j t a b then 0 else term j t a b| ≤
          ((m : ℝ) * (m : ℝ) * ((f + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ)) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2) := by
        have hstep1 : |∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
            ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
              if InBox k m f j t a b then 0 else term j t a b| ≤
            ∑ j ∈ Ico 1 m, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
              ∑ a ∈ range (f + 1), ∑ b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
                ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a ha => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b hb => hpt j hj t ht a ha b hb)
        refine hstep1.trans ?_
        have h1 : ∀ j, ∑ t ∈ (range m).filter (fun t => j + D0 < t),
            ∑ a ∈ range (f + 1), ∑ _b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
              ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2) ≤
            (m : ℝ) * ((f + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2) := by
          intro j
          have hsub1 : ∀ a, (((range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f)).card : ℝ) ≤ (f + 1 : ℕ) :=
            fun a => by exact_mod_cast ((card_filter_le _ _).trans (by simp))
          have hsub2 : (((range m).filter (fun t => j + D0 < t)).card : ℝ) ≤ m := by
            exact_mod_cast ((card_filter_le _ _).trans (by simp))
          calc ∑ t ∈ (range m).filter (fun t => j + D0 < t),
                ∑ a ∈ range (f + 1), ∑ _b ∈ (range (f + 1)).filter (fun b => a + d1 ≤ b ∧ b + d2 ≤ f),
                  ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2)
              ≤ ∑ _t ∈ (range m).filter (fun t => j + D0 < t),
                ∑ _a ∈ range (f + 1), ((f + 1 : ℕ) : ℝ) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2) := by
                apply sum_le_sum; intro t _
                apply sum_le_sum; intro a _
                rw [sum_const, nsmul_eq_mul]
                exact mR (hsub1 a) (by positivity)
            _ = (((range m).filter (fun t => j + D0 < t)).card : ℝ) *
                (((f + 1 : ℕ) : ℝ) * (((f + 1 : ℕ) : ℝ) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2))) := by
                simp only [sum_const, nsmul_eq_mul, Finset.card_range]
            _ ≤ (m : ℝ) * (((f + 1 : ℕ) : ℝ) * (((f + 1 : ℕ) : ℝ) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2))) :=
                mR hsub2 (by positivity)
            _ = (m : ℝ) * ((f + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2) := by ring
        calc ∑ j ∈ Ico 1 m, _
            ≤ ∑ _j ∈ Ico 1 m, (m : ℝ) * ((f + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2) :=
              sum_le_sum fun j _ => h1 j
          _ = ((Ico 1 m).card : ℝ) * ((m : ℝ) * ((f + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2)) := by
              rw [sum_const, nsmul_eq_mul]
          _ ≤ (m : ℝ) * ((m : ℝ) * ((f + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2)) := by
              have hc : ((Ico 1 m).card : ℝ) ≤ m := by rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le m 1
              exact mR hc (by positivity)
          _ = ((m : ℝ) * (m : ℝ) * ((f + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ)) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2) := by ring
      have hsmall : (81 * (k : ℝ) ^ 4) * (1 / (k : ℝ) ^ 6) ≤ (1e24 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) := by
        have hrew : (81 * (k : ℝ) ^ 4) * (1 / (k : ℝ) ^ 6) = 81 / (k : ℝ) ^ 2 := by field_simp [hk_pos.ne']
        rw [hrew]
        have h1 : 81 / (k : ℝ) ^ 2 ≤ 1 / ((k : ℝ) * sqrt k) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hsq100 : (81 : ℝ) ≤ sqrt k := by rw [le_sqrt (by norm_num) hk_pos.le]; linarith only [hkR]
          have hmul := mL hsq100 (show 0 ≤ (k : ℝ) * sqrt k by positivity)
          have hl : (k : ℝ) * sqrt k * sqrt k = (k : ℝ) ^ 2 := by
            rw [mul_assoc, mul_self_sqrt hk_pos.le, sq]
          linarith only [hmul, hl]
        have hL7 : (1 : ℝ) ≤ (1e24 : ℝ) * L ^ 7 := by
          have := pow_le_pow_left₀ (by norm_num) hL10 7; linarith only [this]
        have h2 : 1 / ((k : ℝ) * sqrt k) ≤ (1e24 : ℝ) * L ^ 7 / ((k : ℝ) * sqrt k) :=
          dR hL7 (by positivity)
        have h3 : (1e24 : ℝ) * L ^ 7 / ((k : ℝ) * sqrt k) =
            (1e24 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) := by ring
        linarith only [h1, h2, h3]
      calc |∑ j ∈ Ico 1 m, _|
          ≤ ((m : ℝ) * (m : ℝ) * ((f + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ)) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2) := hsum_out
        _ ≤ (81 * (k : ℝ) ^ 4) * ((1 / (k : ℝ) ^ 6) * N0 * B0 ^ 2) :=
            mR hcard_prod (by positivity)
        _ = ((81 * (k : ℝ) ^ 4) * (1 / (k : ℝ) ^ 6)) * (N0 * B0 ^ 2) := by ring
        _ ≤ ((1e24 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k))) * (N0 * B0 ^ 2) :=
            mR hsmall (by positivity)
        _ = (1e24 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by ring
    linarith only [htri, hin, hout]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d1 ∈ ({0, 1} : Finset ℕ), |∑ d2 ∈ ({0, 1} : Finset ℕ), _|
      ≤ ∑ d1 ∈ ({0, 1} : Finset ℕ), ∑ d2 ∈ ({0, 1} : Finset ℕ), |_| :=
        sum_le_sum fun d1 _ => abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d1 ∈ ({0, 1} : Finset ℕ), ∑ _d2 ∈ ({0, 1} : Finset ℕ),
          (2e24 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 :=
        sum_le_sum fun d1 hd1 => sum_le_sum fun d2 hd2 => hcase d1 hd1 d2 hd2
    _ = 4 * ((2e24 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2) := by
        simp [sum_pair (by norm_num : (0 : ℕ) ≠ 1)]; ring
    _ ≤ (1e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by
        have hnn : 0 ≤ (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * B0 ^ 2 := by positivity
        linarith only [hnn]

-- ============================================================================
-- Section 7: Eventual validity and final theorem OMA.solution
-- ============================================================================

private lemma eventually_validMF :
    ∀ᶠ k : ℕ in atTop, ∀ m f : ℕ,
      |(m : ℝ) - 2 * k| ≤ sqrt k * log k →
      |(f : ℝ) - 2 * (k : ℝ) / 3| ≤ sqrt k * log k →
      ValidMF k m f := by
  have h1 : ∀ᶠ k : ℕ in atTop, 10 ^ 6 ≤ k := eventually_ge_atTop (10 ^ 6)
  have h2 : ∀ᶠ k : ℕ in atTop, (10 ^ 20 : ℝ) ≤ log k :=
    (Filter.tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)) (10 ^ 20)
  have h3 : ∀ᶠ k : ℕ in atTop, (60 ^ 15 * 10 ^ 6) ^ 4 ≤ k :=
    eventually_ge_atTop ((60 ^ 15 * 10 ^ 6) ^ 4)
  filter_upwards [h1, h2, h3] with k hk1 hk2 hk3
  intro m f hm hf
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hL_nn : 0 ≤ log k := by linarith only [hk2]
  have hL15 : log k ^ 15 / sqrt k ≤ 1 / 10 ^ 6 := by
    let u : ℝ := (k : ℝ) ^ ((1 : ℝ) / 60)
    have hu_pos : 0 < u := rpow_pos_of_pos hk_pos _
    have hlog_u : log k ≤ 60 * u := by
      have hlu : log u = (1 / 60 : ℝ) * log k := by
        dsimp [u]; rw [log_rpow hk_pos]
      have hle := log_le_sub_one_of_pos hu_pos
      linarith only [hlu, hle]
    have hpow15 : log k ^ 15 ≤ 60 ^ 15 * (k : ℝ) ^ ((1 : ℝ) / 4) := by
      have h1' := pow_le_pow_left₀ hL_nn hlog_u 15
      rw [mul_pow] at h1'
      have hu15 : u ^ 15 = (k : ℝ) ^ ((1 : ℝ) / 4) := by
        dsimp [u]; rw [← rpow_natCast, ← rpow_mul hk_pos.le]
        norm_num
      rwa [hu15] at h1'
    have hsq_eq : sqrt k = (k : ℝ) ^ ((1 : ℝ) / 4) * (k : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [sqrt_eq_rpow, ← rpow_add hk_pos]; norm_num
    have hk14_ge : (60 ^ 15 * 10 ^ 6 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 4) := by
      have hk3R : ((60 ^ 15 * 10 ^ 6 : ℝ)) ^ 4 ≤ (k : ℝ) := by exact_mod_cast hk3
      have h4 := rpow_le_rpow (by positivity) hk3R (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rw [← rpow_natCast, ← rpow_mul (by positivity),
        show ((4 : ℕ) : ℝ) * (1 / 4 : ℝ) = 1 by norm_num, rpow_one] at h4
      exact h4
    have hk14_pos : 0 < (k : ℝ) ^ ((1 : ℝ) / 4) := rpow_pos_of_pos hk_pos _
    rw [hsq_eq, div_le_div_iff₀ (mul_pos hk14_pos hk14_pos) (by norm_num)]
    have hmul := mR hpow15 (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
    have hmul2 := mR hk14_ge hk14_pos.le
    linarith only [hmul, hmul2]
  have hexpL : (k : ℝ) ^ 10 * exp (-log k ^ 2) ≤ 1 := by
    have hk10 : (k : ℝ) ^ 10 = exp (10 * log k) := by
      calc (k : ℝ) ^ 10 = (exp (log k)) ^ 10 := by rw [exp_log hk_pos]
        _ = exp (10 * log k) := by rw [← exp_nat_mul]; push_cast; rfl
    rw [hk10, ← exp_add, exp_le_one_iff]
    nlinarith only [hk2]
  exact ⟨hk1, hk2, hL15, hexpL, hm, hf⟩

set_option maxHeartbeats 1600000 in
theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1_H2_R1.H2 := by
  classical
  refine ⟨(1e27 : ℝ), by norm_num, ?_⟩
  have hdiv_top : Tendsto (fun n : ℕ => n / 4) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b; exact ⟨4 * b, fun n hn => by omega⟩
  have hev_V := hdiv_top.eventually eventually_validMF
  filter_upwards [hev_V, eventually_ge_atTop (10 ^ 8)] with n hnV hn_big
  intro hn_mod
  dsimp only
  let k : ℕ := n / 4
  have hn_eq : n = 4 * k + 3 := by dsimp [k]; omega
  have hk_big : 10 ^ 6 ≤ k := by dsimp [k]; omega
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq_pos : 0 < sqrt k := sqrt_pos.mpr hk_pos
  have hV_ref : ValidMF k (2 * k) (2 * k / 3) := by
    apply hnV (2 * k) (2 * k / 3)
    · push_cast; rw [sub_self, abs_zero]
      have h1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      exact mul_nonneg (sqrt_nonneg _) (log_nonneg h1)
    · have h1 : |(↑(2 * k / 3) : ℝ) - 2 * (k : ℝ) / 3| ≤ 1 := by
        have hlo : 3 * (2 * k / 3) ≤ 2 * k := Nat.mul_div_le (2 * k) 3
        have hhi : 2 * k < 3 * (2 * k / 3) + 3 := by omega
        have hloR : 3 * (↑(2 * k / 3) : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hlo
        have hhiR : 2 * (k : ℝ) < 3 * (↑(2 * k / 3) : ℝ) + 3 := by exact_mod_cast hhi
        rw [abs_le]; constructor <;> linarith only [hloR, hhiR]
      have hsq1 : (1 : ℝ) ≤ sqrt k := by
        rw [le_sqrt (by norm_num) hk_pos.le]; exact_mod_cast (show 1 ≤ k by omega)
      have hL1 : (1 : ℝ) ≤ log k := by
        have hge : exp 1 ≤ (k : ℝ) := by
          have := exp_one_lt_d9
          have hkR : (10 ^ 6 : ℝ) ≤ k := by exact_mod_cast hk_big
          linarith only [this, hkR]
        calc (1 : ℝ) = log (exp 1) := (log_exp 1).symm
          _ ≤ log k := log_le_log (exp_pos 1) hge
      have hmul := mul_le_mul hsq1 hL1 (by norm_num) (sqrt_nonneg _)
      linarith only [h1, hmul]
  let L : ℝ := log k
  let D0 : ℕ := ⌊L ^ 7⌋₊
  have hL10 : (10 : ℝ) ≤ L := by have := hV_ref.2.1; linarith only [this]
  have hD0_ge : 100 ≤ D0 := by
    have h1 : (100 : ℝ) ≤ L ^ 7 := by have := pow_le_pow_left₀ (by norm_num) hL10 7; linarith only [this]
    exact Nat.le_floor h1
  have hD0_le : (D0 : ℝ) ≤ L ^ 7 := Nat.floor_le (pow_nonneg (by linarith only [hL10]) 7)
  let U : Finset (List Bool) := (range (n + 1)).biUnion allLists
  let E (w : List Bool) : Prop :=
    |(w.length : ℝ) - 2 * k| ≤ sqrt k * log k ∧
    |(cnt w : ℝ) - 2 * k / 3| ≤ sqrt k * log k
  let MF_set : Finset (ℕ × ℕ) :=
    ((range (n + 1)) ×ˢ (range (n + 1))).filter (fun p =>
      |(p.1 : ℝ) - 2 * k| ≤ sqrt k * log k ∧
      |(p.2 : ℝ) - 2 * k / 3| ≤ sqrt k * log k)
  let fib (p : ℕ × ℕ) : Finset (List Bool) := (allLists p.1).filter (fun w => cnt w = p.2)
  have hpart : U.filter E = MF_set.biUnion fib := by
    ext w
    simp only [U, E, MF_set, fib, mem_filter, mem_biUnion, mem_product, mem_range, mem_allLists_iff]
    constructor
    · rintro ⟨⟨m, hm, rfl⟩, hE⟩
      refine ⟨(w.length, cnt w), ⟨⟨hm, ?_⟩, hE⟩, rfl, rfl⟩
      have hV := hnV w.length (cnt w) hE.1 hE.2
      have hba := validMF_eta_bounds hV
      have hR : (cnt w : ℝ) < (n : ℝ) + 1 := by
        have hnR : (n : ℝ) = 4 * k + 3 := by exact_mod_cast hn_eq
        linarith only [hba.2.2.2.1, hnR, hk_pos]
      exact_mod_cast hR
    · rintro ⟨⟨m, f⟩, ⟨⟨hm, _⟩, hE⟩, hlen, hcnt⟩
      exact ⟨⟨m, hm, hlen⟩, by rwa [hlen, hcnt]⟩
  have hdisj : Set.PairwiseDisjoint (↑MF_set) fib := by
    intro p1 _ p2 _ hne
    change Disjoint (fib p1) (fib p2)
    rw [disjoint_left]
    intro w h1 h2
    simp only [fib, mem_filter, mem_allLists_iff] at h1 h2
    exact hne (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2))
  change (∑ w ∈ U.filter E,
    ∑ p ∈ ((range w.length).product (range w.length)).filter
      (fun p => ¬ (p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5)),
      A_val k w p.1 * A_val k w p.2 / ((2 : ℝ) ^ n * (max 1 (F (2 * k + 1) w) : ℕ))) ≤
    (1e27 : ℝ) * (log n) ^ 7 / (n : ℝ) ^ ((3 : ℝ) / 2)
  have hfib_bound : ∀ p ∈ MF_set,
      (∑ w ∈ fib p,
        ∑ q ∈ ((range w.length).product (range w.length)).filter
          (fun q => ¬ (q.1 ≤ q.2 + 5 ∧ q.2 ≤ q.1 + 5)),
          A_val k w q.1 * A_val k w q.2 / ((2 : ℝ) ^ n * (max 1 (F (2 * k + 1) w) : ℕ))) ≤
      (3e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) *
        ((∑ w ∈ fib p, (F (2 * k + 1) w : ℝ)) / (2 : ℝ) ^ n) := by
    intro ⟨m, f⟩ hp
    have hmf := (mem_filter.mp hp).2
    have hV : ValidMF k m f := hnV m f hmf.1 hmf.2
    have hba := validMF_eta_bounds hV
    let B0 : ℕ := (2 * k + 1 + f).choose m
    have hB0_ge1 : 1 ≤ B0 := by
      have hle : m ≤ 2 * k + 1 + f := by
        have : (m : ℝ) ≤ (2 * k + 1 + f : ℕ) := by push_cast; linarith only [hba.2.1, hba.2.2.1, hk_pos]
        exact_mod_cast this
      exact Nat.choose_pos hle
    have hB0_pos : (0 : ℝ) < B0 := by exact_mod_cast (show 0 < B0 by omega)
    have hfib_const : ∀ w ∈ fib (m, f), w.length = m ∧ cnt w = f ∧ F (2 * k + 1) w = B0 := by
      intro w hw; simp only [fib, mem_filter, mem_allLists_iff] at hw
      exact ⟨hw.1, hw.2, by unfold F; rw [hw.1, hw.2]⟩
    have hden_pull : (∑ w ∈ fib (m, f),
        ∑ q ∈ ((range w.length).product (range w.length)).filter
          (fun q => ¬ (q.1 ≤ q.2 + 5 ∧ q.2 ≤ q.1 + 5)),
          A_val k w q.1 * A_val k w q.2 / ((2 : ℝ) ^ n * (max 1 (F (2 * k + 1) w) : ℕ))) =
        (2 : ℝ) * ((∑ w ∈ fib (m, f),
            ∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0), A_val k w j * A_val k w t) +
          (∑ w ∈ fib (m, f),
            ∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + D0 < t), A_val k w j * A_val k w t)) /
        ((2 : ℝ) ^ n * (B0 : ℝ)) := by
      have h1 : ∀ w ∈ fib (m, f),
          (∑ q ∈ ((range w.length).product (range w.length)).filter
            (fun q => ¬ (q.1 ≤ q.2 + 5 ∧ q.2 ≤ q.1 + 5)),
            A_val k w q.1 * A_val k w q.2 / ((2 : ℝ) ^ n * (max 1 (F (2 * k + 1) w) : ℕ))) =
          ((2 : ℝ) * ((∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0), A_val k w j * A_val k w t) +
            (∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + D0 < t), A_val k w j * A_val k w t))) /
          ((2 : ℝ) ^ n * (B0 : ℝ)) := by
        intro w hw
        obtain ⟨hlen, _, hFw⟩ := hfib_const w hw
        rw [hlen, hFw, Nat.max_eq_right hB0_ge1, ← sum_div, sum_separated_eq_two_mul_ordered]
        congr 2
        rw [← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        have hunion : (range m).filter (fun t => j + 5 < t) =
            (range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0) ∪
            (range m).filter (fun t => j + D0 < t) := by
          ext t; simp only [mem_union, mem_filter, mem_range]; omega
        have hd : Disjoint ((range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0))
            ((range m).filter (fun t => j + D0 < t)) := by
          rw [disjoint_left]; intro t h1 h2; simp only [mem_filter] at h1 h2; omega
        rw [hunion, sum_union hd]
      rw [sum_congr rfl h1, ← sum_div, ← mul_sum, sum_add_distrib]
    rw [hden_pull]
    let N0 : ℝ := (((m + 1).choose (2 * f + 1) : ℕ) : ℝ)
    have hR1 : |∑ w ∈ fib (m, f),
        ∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0), A_val k w j * A_val k w t| ≤
        (4e12 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * (B0 : ℝ) ^ 2 := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hpt : ∀ w ∈ fib (m, f),
          |∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0), A_val k w j * A_val k w t| ≤
          (4e12 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * (B0 : ℝ) ^ 2 := by
        intro w hw
        obtain ⟨hlen, hcnt, hFw⟩ := hfib_const w hw
        have hr1 := regime1_sum_le m D0 (A_val k w)
        have hdiag := diag_sum_A_sq_le k w (by omega)
          (by rw [hlen]; have hsqL := validMF_sqL_le hV; linarith only [hmf.1, hsqL, hk_pos])
          (by rw [hcnt]; have hsqL := validMF_sqL_le hV; linarith only [hmf.2, hsqL, hk_pos])
        rw [hlen, hFw] at hdiag
        have hk32 : (k : ℝ) ^ ((3 : ℝ) / 2) = (k : ℝ) * sqrt k := by
          rw [show ((3 : ℝ) / 2) = 1 + (1 / 2 : ℝ) by norm_num, rpow_add hk_pos, rpow_one, sqrt_eq_rpow]
        rw [hk32] at hdiag
        calc |∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0), A_val k w j * A_val k w t|
            ≤ (D0 : ℝ) * ∑ j ∈ range m, (A_val k w j) ^ 2 := hr1
          _ ≤ L ^ 7 * ((4e12 : ℝ) / ((k : ℝ) * sqrt k) * (B0 : ℝ) ^ 2) :=
              mul_le_mul hD0_le hdiag (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
          _ = (4e12 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * (B0 : ℝ) ^ 2 := by ring
      calc ∑ w ∈ fib (m, f), |_|
          ≤ ∑ _w ∈ fib (m, f), ((4e12 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * (B0 : ℝ) ^ 2) :=
            sum_le_sum hpt
        _ = ((fib (m, f)).card : ℝ) * ((4e12 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * (B0 : ℝ) ^ 2) := by
            rw [sum_const, nsmul_eq_mul]
        _ = (4e12 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * (B0 : ℝ) ^ 2 := by
            have hc : (fib (m, f)).card = (m + 1).choose (2 * f + 1) := card_allLists_cnt m f
            rw [hc]; dsimp [N0]; ring
    have hR2 := regime2_mf_bound hV
    have hsum_F : ∑ w ∈ fib (m, f), (F (2 * k + 1) w : ℝ) = N0 * (B0 : ℝ) := by
      have h1 : ∑ w ∈ fib (m, f), (F (2 * k + 1) w : ℝ) = ∑ _w ∈ fib (m, f), (B0 : ℝ) :=
        sum_congr rfl fun w hw => by rw [(hfib_const w hw).2.2]
      rw [h1, sum_const, nsmul_eq_mul, card_allLists_cnt m f]
    rw [hsum_F]
    have hnum_le : (2 : ℝ) * ((∑ w ∈ fib (m, f),
          ∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + 5 < t ∧ t ≤ j + D0), A_val k w j * A_val k w t) +
        (∑ w ∈ fib (m, f),
          ∑ j ∈ range m, ∑ t ∈ (range m).filter (fun t => j + D0 < t), A_val k w j * A_val k w t)) ≤
        (3e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * (B0 : ℝ) ^ 2 := by
      have h1 := (abs_le.mp hR1).2
      have h2 := (abs_le.mp hR2).2
      have hnn : 0 ≤ (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * (B0 : ℝ) ^ 2 := by positivity
      linarith only [h1, h2, hnn]
    calc _ ≤ ((3e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * N0 * (B0 : ℝ) ^ 2) /
            ((2 : ℝ) ^ n * (B0 : ℝ)) := dR hnum_le (by positivity)
      _ = (3e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * (N0 * (B0 : ℝ) / (2 : ℝ) ^ n) := by
            field_simp [hB0_pos.ne', (by positivity : (2 : ℝ) ^ n ≠ 0)]
  have hsum_all : (∑ w ∈ U.filter E,
      ∑ q ∈ ((range w.length).product (range w.length)).filter
        (fun q => ¬ (q.1 ≤ q.2 + 5 ∧ q.2 ≤ q.1 + 5)),
        A_val k w q.1 * A_val k w q.2 / ((2 : ℝ) ^ n * (max 1 (F (2 * k + 1) w) : ℕ))) ≤
      (3e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) := by
    rw [hpart, sum_biUnion hdisj]
    have hF_tot : (∑ p ∈ MF_set, ∑ w ∈ fib p, (F (2 * k + 1) w : ℝ)) / (2 : ℝ) ^ n ≤ 1 := by
      rw [← sum_biUnion hdisj, ← hpart, div_le_one (by positivity)]
      have hnat := sum_F_le_pow (2 * k + 1) (U.filter E)
      have hR : (∑ w ∈ U.filter E, (F (2 * k + 1) w : ℝ)) ≤ (2 : ℝ) ^ (2 * (2 * k + 1)) := by
        exact_mod_cast hnat
      have hpow : (2 : ℝ) ^ (2 * (2 * k + 1)) ≤ (2 : ℝ) ^ n :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      exact hR.trans hpow
    calc ∑ p ∈ MF_set, ∑ w ∈ fib p, _
        ≤ ∑ p ∈ MF_set, (3e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) *
            ((∑ w ∈ fib p, (F (2 * k + 1) w : ℝ)) / (2 : ℝ) ^ n) := sum_le_sum hfib_bound
      _ = (3e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) *
            ((∑ p ∈ MF_set, ∑ w ∈ fib p, (F (2 * k + 1) w : ℝ)) / (2 : ℝ) ^ n) := by
            rw [← mul_sum, ← sum_div]
      _ ≤ (3e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) * 1 :=
            mL hF_tot (by positivity)
      _ = (3e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) := mul_one _
  refine hsum_all.trans ?_
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast (show k ≤ n by omega)
  have hlog_le : L ^ 7 ≤ (log n) ^ 7 :=
    pow_le_pow_left₀ (by linarith only [hL10]) (log_le_log hk_pos hkn) 7
  have hn32 : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ 15 * ((k : ℝ) * sqrt k) := by
    have hrew : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * sqrt n := by
      rw [show ((3 : ℝ) / 2) = 1 + (1 / 2 : ℝ) by norm_num, rpow_add hn_pos, rpow_one, sqrt_eq_rpow]
    rw [hrew]
    have hn5 : (n : ℝ) ≤ 5 * k := by
      have : n ≤ 5 * k := by omega
      exact_mod_cast this
    have hsqn : sqrt n ≤ 3 * sqrt k := by
      have h9 : (n : ℝ) ≤ 9 * k := by linarith only [hn5, hk_pos]
      calc sqrt n ≤ sqrt (9 * (k : ℝ)) := sqrt_le_sqrt h9
        _ = sqrt 9 * sqrt k := sqrt_mul (by norm_num) _
        _ = 3 * sqrt k := by
            rw [show sqrt 9 = 3 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    have hmul := mul_le_mul hn5 hsqn (sqrt_nonneg _) (by positivity)
    linarith only [hmul]
  have hinv_le : 1 / ((k : ℝ) * sqrt k) ≤ 15 / (n : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [div_le_div_iff₀ (by positivity) (rpow_pos_of_pos hn_pos _)]
    linarith only [hn32]
  have hprod := mul_le_mul hlog_le hinv_le (by positivity) (pow_nonneg (log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) 7)
  have hmul := mL hprod (by norm_num : (0 : ℝ) ≤ 3e25)
  have hlhs : (3e25 : ℝ) * (L ^ 7 * (1 / ((k : ℝ) * sqrt k))) =
      (3e25 : ℝ) * (L ^ 7 / ((k : ℝ) * sqrt k)) := by ring
  have hrhs : (3e25 : ℝ) * ((log n) ^ 7 * (15 / (n : ℝ) ^ ((3 : ℝ) / 2))) =
      (4.5e26 : ℝ) * ((log n) ^ 7 / (n : ℝ) ^ ((3 : ℝ) / 2)) := by ring
  have hgoal_eq : (1e27 : ℝ) * (log n) ^ 7 / (n : ℝ) ^ ((3 : ℝ) / 2) =
      (1e27 : ℝ) * ((log n) ^ 7 / (n : ℝ) ^ ((3 : ℝ) / 2)) := by ring
  have hnn : 0 ≤ (log n) ^ 7 / (n : ℝ) ^ ((3 : ℝ) / 2) := by
    apply div_nonneg (pow_nonneg (log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) 7)
      (rpow_pos_of_pos hn_pos _).le
  linarith only [hmul, hlhs, hrhs, hgoal_eq, hnn]

end Green92ChaseH2

