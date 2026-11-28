import OMAStatements.S_oeis_a094863

namespace OMA.S_oeis_a094863.Disproof

private def dropAfter (a : ℕ) : List ℕ → Option (List ℕ)
  | [] => none
  | b :: bs => if b = a then some bs else dropAfter a bs

private lemma cons_sublist_iff_dropAfter (a : ℕ) (w l : List ℕ) :
    List.Sublist (a :: w) l ↔ ∃ l', dropAfter a l = some l' ∧ List.Sublist w l' := by
  induction l with
  | nil => simp [dropAfter]
  | cons b bs ih =>
    by_cases hba : b = a
    · subst b
      simp only [dropAfter, ↓reduceIte, Option.some.injEq, exists_eq_left']
      constructor
      · intro h
        cases h with
        | cons _ h' => exact (List.sublist_cons_self a w).trans h'
        | cons_cons _ h' => exact h'
      · intro h
        exact List.Sublist.cons_cons a h
    · simp only [dropAfter, hba, ↓reduceIte, ← ih]
      constructor
      · intro h
        cases h with
        | cons _ h' => exact h'
        | cons_cons => exact absurd rfl hba
      · intro h
        exact List.Sublist.cons b h

private def lcsSet (x y : List ℕ) : Finset (List ℕ) :=
  (common x y).filter fun w => w.length = lcsLength x y

private lemma mem_common_iff (x y w : List ℕ) :
    w ∈ common x y ↔ List.Sublist w x ∧ List.Sublist w y := by
  simp [common, List.mem_sublists]

private lemma nil_mem_common (x y : List ℕ) : [] ∈ common x y := by
  simp [mem_common_iff]

private lemma length_le_lcsLength {x y w : List ℕ} (hw : w ∈ common x y) :
    w.length ≤ lcsLength x y :=
  Finset.le_sup (f := List.length) hw

private lemma exists_mem_common_lcsLength (x y : List ℕ) :
    ∃ w ∈ common x y, w.length = lcsLength x y := by
  obtain ⟨w, hw, hmax⟩ :=
    Finset.exists_mem_eq_sup (common x y) ⟨[], nil_mem_common x y⟩ List.length
  exact ⟨w, hw, hmax.symm⟩

private lemma lcsCount_of_lcsLength_zero {x y : List ℕ} (h : lcsLength x y = 0) :
    lcsCount x y = 1 := by
  change (lcsSet x y).card = 1
  have hset : lcsSet x y = {[]} := by
    ext w
    simp only [lcsSet, Finset.mem_filter, Finset.mem_singleton, h, List.length_eq_zero_iff]
    constructor
    · rintro ⟨_, rfl⟩
      rfl
    · rintro rfl
      exact ⟨nil_mem_common x y, rfl⟩
  rw [hset, Finset.card_singleton]

private lemma lcsLength_nil_left (y : List ℕ) : lcsLength [] y = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro w hw
  rw [mem_common_iff] at hw
  have : w = [] := List.sublist_nil.mp hw.1
  simp [this]

private lemma lcsLength_nil_right (x : List ℕ) : lcsLength x [] = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro w hw
  rw [mem_common_iff] at hw
  have : w = [] := List.sublist_nil.mp hw.2
  simp [this]

private def lcsPair (x y : List ℕ) : ℕ × ℕ := (lcsLength x y, lcsCount x y)

private lemma lcsPair_nil_left (y : List ℕ) : lcsPair [] y = (0, 1) := by
  simp [lcsPair, lcsLength_nil_left, lcsCount_of_lcsLength_zero]

private lemma lcsPair_nil_right (x : List ℕ) : lcsPair x [] = (0, 1) := by
  simp [lcsPair, lcsLength_nil_right, lcsCount_of_lcsLength_zero]

private def branchVal (a : ℕ) (x y : List ℕ) : ℕ × ℕ :=
  match dropAfter a x, dropAfter a y with
  | some x', some y' => (lcsLength x' y' + 1, lcsCount x' y')
  | _, _ => (0, 0)

private lemma branchVal_fst_le_lcsLength (a : ℕ) (x y : List ℕ) :
    (branchVal a x y).1 ≤ lcsLength x y := by
  unfold branchVal
  cases hx : dropAfter a x with
  | none => simp
  | some x' =>
    cases hy : dropAfter a y with
    | none => simp
    | some y' =>
      obtain ⟨w', hw', hlen⟩ := exists_mem_common_lcsLength x' y'
      rw [mem_common_iff] at hw'
      have hmem : (a :: w') ∈ common x y := by
        rw [mem_common_iff]
        exact ⟨(cons_sublist_iff_dropAfter a w' x).mpr ⟨x', hx, hw'.1⟩,
               (cons_sublist_iff_dropAfter a w' y).mpr ⟨y', hy, hw'.2⟩⟩
      have hle := length_le_lcsLength hmem
      simpa [hlen] using hle

private lemma lcsLength_eq_sup_branchVal {alpha x y : List ℕ} (hx : ∀ a ∈ x, a ∈ alpha) :
    lcsLength x y = alpha.toFinset.sup (fun a => (branchVal a x y).1) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro w hw
    cases w with
    | nil => simp
    | cons a w' =>
      rw [mem_common_iff] at hw
      have ha_mem : a ∈ x := hw.1.subset (by simp)
      have ha_alpha : a ∈ alpha.toFinset := List.mem_toFinset.mpr (hx a ha_mem)
      obtain ⟨x', hx', hwx'⟩ := (cons_sublist_iff_dropAfter a w' x).mp hw.1
      obtain ⟨y', hy', hwy'⟩ := (cons_sublist_iff_dropAfter a w' y).mp hw.2
      have hw'_mem : w' ∈ common x' y' := (mem_common_iff x' y' w').mpr ⟨hwx', hwy'⟩
      have hle : (a :: w').length ≤ (branchVal a x y).1 := by
        simp only [branchVal, hx', hy', List.length_cons]
        exact Nat.succ_le_succ (length_le_lcsLength hw'_mem)
      exact hle.trans (Finset.le_sup (f := fun a => (branchVal a x y).1) ha_alpha)
  · apply Finset.sup_le
    intro a _
    exact branchVal_fst_le_lcsLength a x y

private lemma branchCard_eq (a : ℕ) (ox oy : Option (List ℕ)) (L : ℕ) (hL : L ≠ 0) :
    (match ox, oy with
     | some x', some y' =>
       if lcsLength x' y' + 1 = L then (lcsSet x' y').image (a :: ·) else ∅
     | _, _ => ∅).card =
    if (match ox, oy with
        | some x', some y' => (lcsLength x' y' + 1, lcsCount x' y')
        | _, _ => (0, 0)).1 = L then
      (match ox, oy with
       | some x', some y' => (lcsLength x' y' + 1, lcsCount x' y')
       | _, _ => (0, 0)).2
    else 0 := by
  cases ox with
  | none => simp [Ne.symm hL]
  | some x' =>
    cases oy with
    | none => simp [Ne.symm hL]
    | some y' =>
      by_cases heq : lcsLength x' y' + 1 = L
      · simp only [heq, ↓reduceIte]
        exact Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
      · simp [heq]

private lemma lcsCount_eq_sum_branchVal {alpha x y : List ℕ}
    (hx : ∀ a ∈ x, a ∈ alpha) (hpos : lcsLength x y ≠ 0) :
    lcsCount x y = ∑ a ∈ alpha.toFinset,
      if (branchVal a x y).1 = lcsLength x y then (branchVal a x y).2 else 0 := by
  let branchSet : ℕ → Finset (List ℕ) := fun a =>
    match dropAfter a x, dropAfter a y with
    | some x', some y' =>
      if lcsLength x' y' + 1 = lcsLength x y then (lcsSet x' y').image (a :: ·) else ∅
    | _, _ => ∅
  have hbiUnion : lcsSet x y = alpha.toFinset.biUnion branchSet := by
    ext w
    simp only [Finset.mem_biUnion]
    constructor
    · intro hw
      simp only [lcsSet, Finset.mem_filter] at hw
      cases w with
      | nil =>
        simp only [List.length_nil] at hw
        exact absurd hw.2.symm hpos
      | cons a w' =>
        rw [mem_common_iff] at hw
        have ha_mem : a ∈ x := hw.1.1.subset (by simp)
        have ha_alpha : a ∈ alpha.toFinset := List.mem_toFinset.mpr (hx a ha_mem)
        obtain ⟨x', hx', hwx'⟩ := (cons_sublist_iff_dropAfter a w' x).mp hw.1.1
        obtain ⟨y', hy', hwy'⟩ := (cons_sublist_iff_dropAfter a w' y).mp hw.1.2
        have hw'_mem : w' ∈ common x' y' := (mem_common_iff x' y' w').mpr ⟨hwx', hwy'⟩
        have hle1 : w'.length ≤ lcsLength x' y' := length_le_lcsLength hw'_mem
        have hle2 : lcsLength x' y' + 1 ≤ lcsLength x y := by
          have := branchVal_fst_le_lcsLength a x y
          simpa [branchVal, hx', hy'] using this
        have hlen_cons : w'.length + 1 = lcsLength x y := by simpa using hw.2
        have heq1 : lcsLength x' y' + 1 = lcsLength x y := by omega
        have heq2 : w'.length = lcsLength x' y' := by omega
        refine ⟨a, ha_alpha, ?_⟩
        simp only [branchSet, hx', hy', heq1, ↓reduceIte, Finset.mem_image]
        exact ⟨w', Finset.mem_filter.mpr ⟨hw'_mem, heq2⟩, rfl⟩
    · rintro ⟨a, _, hw⟩
      simp only [branchSet] at hw
      cases hx' : dropAfter a x with
      | none => simp [hx'] at hw
      | some x' =>
        cases hy' : dropAfter a y with
        | none => simp [hx', hy'] at hw
        | some y' =>
          simp only [hx', hy'] at hw
          split_ifs at hw with heq
          · obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
            simp only [lcsSet, Finset.mem_filter] at hw' ⊢
            rw [mem_common_iff] at hw' ⊢
            refine ⟨⟨(cons_sublist_iff_dropAfter a w' x).mpr ⟨x', hx', hw'.1.1⟩,
                     (cons_sublist_iff_dropAfter a w' y).mpr ⟨y', hy', hw'.1.2⟩⟩, ?_⟩
            simp [hw'.2, heq]
          · simp at hw
  have hdisj : Set.PairwiseDisjoint (alpha.toFinset : Set ℕ) branchSet := by
    intro a₁ _ a₂ _ hne
    change Disjoint (branchSet a₁) (branchSet a₂)
    rw [Finset.disjoint_left]
    intro w hw₁ hw₂
    have head_eq : ∀ a, w ∈ branchSet a → w.head? = some a := by
      intro a hw
      simp only [branchSet] at hw
      cases hx' : dropAfter a x with
      | none => simp [hx'] at hw
      | some x' =>
        cases hy' : dropAfter a y with
        | none => simp [hx', hy'] at hw
        | some y' =>
          simp only [hx', hy'] at hw
          split_ifs at hw with heq
          · obtain ⟨w', _, rfl⟩ := Finset.mem_image.mp hw
            rfl
          · simp at hw
    have h1 := head_eq a₁ hw₁
    have h2 := head_eq a₂ hw₂
    rw [h1] at h2
    exact hne (Option.some.inj h2)
  change (lcsSet x y).card = _
  rw [hbiUnion, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro a _
  exact branchCard_eq a (dropAfter a x) (dropAfter a y) (lcsLength x y) hpos

private def maxFirst : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: ps => max p.1 (maxFirst ps)

private def sumAt (target : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: ps => (if p.1 = target then p.2 else 0) + sumAt target ps

private def combine (ps : List (ℕ × ℕ)) : ℕ × ℕ :=
  let m := maxFirst ps
  if m = 0 then (0, 1) else (m, sumAt m ps)

private lemma maxFirst_map (l : List ℕ) (f : ℕ → ℕ × ℕ) :
    maxFirst (l.map f) = l.toFinset.sup (fun a => (f a).1) := by
  induction l with
  | nil => simp [maxFirst]
  | cons a l ih =>
    simp [maxFirst, ih, Finset.sup_insert]

private lemma sumAt_map_of_nodup (target : ℕ) {l : List ℕ} (hl : l.Nodup) (f : ℕ → ℕ × ℕ) :
    sumAt target (l.map f) = ∑ a ∈ l.toFinset, if (f a).1 = target then (f a).2 else 0 := by
  induction l with
  | nil => simp [sumAt]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have ha : a ∉ l.toFinset := by simpa using hl.1
    simp [sumAt, ih hl.2, List.toFinset_cons, Finset.sum_insert ha]

private lemma combine_map_branchVal {alpha x y : List ℕ}
    (hnodup : alpha.Nodup) (hx : ∀ a ∈ x, a ∈ alpha) :
    combine (alpha.map fun a => branchVal a x y) = lcsPair x y := by
  unfold combine lcsPair
  have hm : maxFirst (alpha.map fun a => branchVal a x y) = lcsLength x y := by
    rw [maxFirst_map, lcsLength_eq_sup_branchVal hx]
  dsimp only
  rw [hm]
  by_cases h0 : lcsLength x y = 0
  · simp [h0, lcsCount_of_lcsLength_zero h0]
  · simp only [h0, ↓reduceIte]
    rw [sumAt_map_of_nodup _ hnodup, ← lcsCount_eq_sum_branchVal hx h0]

private def combineAcc (accL accC : ℕ) : List (ℕ × ℕ) → ℕ × ℕ
  | [] => if Nat.beq accL 0 then (0, 1) else (accL, accC)
  | (L, C) :: ps =>
    if Nat.beq L accL then combineAcc accL (Nat.add accC C) ps
    else if Nat.ble accL L then combineAcc L C ps
    else combineAcc accL accC ps

private lemma combineAcc_spec (ps : List (ℕ × ℕ)) (accL accC : ℕ) :
    let m := max accL (maxFirst ps)
    combineAcc accL accC ps =
      if m = 0 then (0, 1)
      else (m, (if accL = m then accC else 0) + sumAt m ps) := by
  induction ps generalizing accL accC with
  | nil =>
    simp only [combineAcc, maxFirst, sumAt, Nat.max_zero, Nat.beq_eq]
    split_ifs <;> simp
  | cons p ps ih =>
    rcases p with ⟨L, C⟩
    simp only [combineAcc, maxFirst, sumAt, Nat.beq_eq, Nat.ble_eq]
    by_cases h1 : L = accL
    · subst h1
      simp only [↓reduceIte, ih]
      have hm : max L (max L (maxFirst ps)) = max L (maxFirst ps) := by omega
      simp only [hm]
      by_cases h0 : max L (maxFirst ps) = 0
      · simp [h0]
      · simp only [h0, ↓reduceIte]
        have hadd : accC.add C = accC + C := rfl
        rw [hadd]
        by_cases hLm : L = max L (maxFirst ps)
        · rw [if_pos hLm, if_pos hLm, if_pos hLm]
          exact Prod.ext rfl (by omega)
        · rw [if_neg hLm, if_neg hLm, if_neg hLm]
          exact Prod.ext rfl (by omega)
    · simp only [h1, ↓reduceIte]
      by_cases h2 : accL ≤ L
      · simp only [h2, ↓reduceIte, ih]
        have hm : max accL (max L (maxFirst ps)) = max L (maxFirst ps) := by omega
        have hpos : max L (maxFirst ps) ≠ 0 := by omega
        have hne : accL ≠ max L (maxFirst ps) := by omega
        simp only [hm, hpos, hne, ↓reduceIte, Prod.mk.injEq, true_and]
        omega
      · simp only [h2, ↓reduceIte, ih]
        have hm : max accL (max L (maxFirst ps)) = max accL (maxFirst ps) := by omega
        have hpos : max accL (maxFirst ps) ≠ 0 := by omega
        have hne : L ≠ max accL (maxFirst ps) := by omega
        simp only [hm, hpos, hne, ↓reduceIte, Prod.mk.injEq, true_and]
        omega

private lemma combineAcc_zero (ps : List (ℕ × ℕ)) : combineAcc 0 0 ps = combine ps := by
  have h := combineAcc_spec ps 0 0
  simp only [Nat.zero_max] at h
  rw [h]
  unfold combine
  dsimp only
  split_ifs <;> simp

private def dropAfterOffset (a : ℕ) : List ℕ → Option ℕ
  | [] => none
  | b :: bs => if Nat.beq b a then some 1 else (dropAfterOffset a bs).map (· + 1)

private lemma dropAfterOffset_spec (a : ℕ) (l : List ℕ) :
    match dropAfterOffset a l with
    | some d => 0 < d ∧ d ≤ l.length ∧ dropAfter a l = some (l.drop d)
    | none => dropAfter a l = none := by
  induction l with
  | nil => simp [dropAfterOffset, dropAfter]
  | cons b bs ih =>
    simp only [dropAfterOffset, dropAfter, Nat.beq_eq]
    by_cases hba : b = a
    · simp [hba]
    · simp only [hba, ↓reduceIte]
      cases h : dropAfterOffset a bs with
      | none =>
        rw [h] at ih
        simpa using ih
      | some d =>
        rw [h] at ih
        rcases ih with ⟨hpos, hle, hdrop⟩
        simp only [Option.map_some, List.length_cons, List.drop_succ_cons]
        exact ⟨by omega, by omega, hdrop⟩

private def getOpt : List α → ℕ → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => getOpt as n

private lemma getOpt_eq_getElem? (l : List α) (n : ℕ) : getOpt l n = l[n]? := by
  induction l generalizing n with
  | nil => simp [getOpt]
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n => simpa [getOpt] using ih n

private def lookupAt (j : ℕ) : Option (List (ℕ × ℕ)) → Option ℕ → ℕ × ℕ
  | some row, some d =>
    match getOpt row (Nat.add j d) with
    | some (L, C) => (Nat.add L 1, C)
    | none => (0, 0)
  | _, _ => (0, 0)

private def evalCell (j : ℕ) (ys : List ℕ) (accL accC : ℕ) :
    List (ℕ × Option (List (ℕ × ℕ))) → ℕ × ℕ
  | [] => if Nat.beq accL 0 then (0, 1) else (accL, accC)
  | (a, optRow) :: rest =>
    match optRow, dropAfterOffset a ys with
    | some row, some d =>
      match getOpt row (Nat.add j d) with
      | some (L, C) =>
        let L1 := Nat.add L 1
        if Nat.beq L1 accL then evalCell j ys accL (Nat.add accC C) rest
        else if Nat.ble accL L1 then evalCell j ys L1 C rest
        else evalCell j ys accL accC rest
      | none => evalCell j ys accL accC rest
    | _, _ => evalCell j ys accL accC rest

private lemma combineAcc_zero_pair (accL accC : ℕ) (ps : List (ℕ × ℕ)) :
    combineAcc accL accC ((0, 0) :: ps) = combineAcc accL accC ps := by
  simp only [combineAcc, Nat.beq_eq, Nat.ble_eq]
  by_cases h0 : 0 = accL
  · subst h0
    simp
  · have hnot : ¬ accL ≤ 0 := by omega
    simp [h0, hnot]

private lemma lookupAt_none (j : ℕ) (o : Option ℕ) : lookupAt j none o = (0, 0) := rfl

private lemma lookupAt_some_none (j : ℕ) (r : List (ℕ × ℕ)) :
    lookupAt j (some r) none = (0, 0) := rfl

private lemma lookupAt_some_some (j : ℕ) (r : List (ℕ × ℕ)) (d : ℕ) :
    lookupAt j (some r) (some d) =
      match getOpt r (Nat.add j d) with
      | some (L, C) => (Nat.add L 1, C)
      | none => (0, 0) := rfl

private lemma evalCell_eq_combineAcc (j : ℕ) (ys : List ℕ)
    (targetRows : List (ℕ × Option (List (ℕ × ℕ)))) (accL accC : ℕ) :
    evalCell j ys accL accC targetRows =
      combineAcc accL accC
        (targetRows.map fun (a, optRow) => lookupAt j optRow (dropAfterOffset a ys)) := by
  induction targetRows generalizing accL accC with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨a, optRow⟩
    rw [List.map_cons]
    dsimp only
    cases optRow with
    | none =>
      rw [lookupAt_none, combineAcc_zero_pair]
      exact ih accL accC
    | some row =>
      cases hdy : dropAfterOffset a ys with
      | none =>
        rw [lookupAt_some_none, combineAcc_zero_pair]
        change (match some row, dropAfterOffset a ys with
          | some row, some d => _
          | _, _ => evalCell j ys accL accC rest) = _
        rw [hdy]
        exact ih accL accC
      | some d =>
        rw [lookupAt_some_some]
        change (match some row, dropAfterOffset a ys with
          | some row, some d =>
            match getOpt row (Nat.add j d) with
            | some (L, C) =>
              let L1 := Nat.add L 1
              if Nat.beq L1 accL then evalCell j ys accL (Nat.add accC C) rest
              else if Nat.ble accL L1 then evalCell j ys L1 C rest
              else evalCell j ys accL accC rest
            | none => evalCell j ys accL accC rest
          | _, _ => evalCell j ys accL accC rest) = _
        rw [hdy]
        dsimp only
        cases hget : getOpt row (Nat.add j d) with
        | none =>
          dsimp only
          rw [combineAcc_zero_pair]
          exact ih accL accC
        | some LC =>
          rcases LC with ⟨L, C⟩
          dsimp only [combineAcc]
          split_ifs <;> exact ih _ _

private def pairEq (p q : ℕ × ℕ) : Bool := Nat.beq p.1 q.1 && Nat.beq p.2 q.2

private lemma pairEq_eq_true (p q : ℕ × ℕ) : pairEq p q = true ↔ p = q := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  simp [pairEq, Nat.beq_eq]

private def checkNilRow : List (ℕ × ℕ) → ℕ → Bool
  | [p], 0 => pairEq p (0, 1)
  | p :: ps, n + 1 => pairEq p (0, 1) && checkNilRow ps n
  | _, _ => false

private lemma checkNilRow_sound (n : ℕ) (r : List (ℕ × ℕ)) (h : checkNilRow r n = true) :
    r = List.replicate (n + 1) (0, 1) := by
  induction n generalizing r with
  | zero =>
    cases r with
    | nil => simp [checkNilRow] at h
    | cons p ps =>
      cases ps with
      | nil =>
        simp only [checkNilRow, pairEq_eq_true] at h
        simp [h]
      | cons _ _ => simp [checkNilRow] at h
  | succ n ih =>
    cases r with
    | nil => simp [checkNilRow] at h
    | cons p ps =>
      simp only [checkNilRow, Bool.and_eq_true, pairEq_eq_true] at h
      rw [h.1, ih ps h.2]
      rfl

private def checkRow (targetRows : List (ℕ × Option (List (ℕ × ℕ)))) (j : ℕ) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], [p] => pairEq p (0, 1)
  | c :: ys, cell :: cells =>
    pairEq cell (evalCell j (c :: ys) 0 0 targetRows) &&
      checkRow targetRows (Nat.add j 1) ys cells
  | _, _ => false

private def checkTable (alpha : List ℕ) (y : List ℕ) : List ℕ → List (List (ℕ × ℕ)) → Bool
  | [], [r] => checkNilRow r y.length
  | b :: xs, r :: rs =>
    let targetRows := alpha.map fun a =>
      (a, (dropAfterOffset a (b :: xs)).bind fun d => getOpt (r :: rs) d)
    checkRow targetRows 0 y r && checkTable alpha y xs rs
  | _, _ => false

private def rowSpec (x : List ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => [lcsPair x []]
  | c :: ys => lcsPair x (c :: ys) :: rowSpec x ys

private lemma rowSpec_nil_left (y : List ℕ) :
    rowSpec [] y = List.replicate (y.length + 1) (0, 1) := by
  induction y with
  | nil => simp [rowSpec, lcsPair_nil_left]
  | cons c ys ih => simp [rowSpec, lcsPair_nil_left, ih, List.replicate_succ]

private lemma rowSpec_getElem? (x y : List ℕ) (j : ℕ) (hj : j ≤ y.length) :
    (rowSpec x y)[j]? = some (lcsPair x (y.drop j)) := by
  induction y generalizing j with
  | nil =>
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    rfl
  | cons c ys ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.length_cons] at hj
      simpa [rowSpec] using ih j (by omega)

private lemma checkRow_sound {alpha xs : List ℕ} (hnodup : alpha.Nodup)
    (hxs : ∀ a ∈ xs, a ∈ alpha) (y : List ℕ) :
    ∀ (ys : List ℕ) (j : ℕ) (r : List (ℕ × ℕ)),
      ys = y.drop j →
      j ≤ y.length →
      checkRow (alpha.map fun a => (a, (dropAfter a xs).map (fun x' => rowSpec x' y))) j ys r = true →
      r = rowSpec xs ys := by
  intro ys
  induction ys with
  | nil =>
    intro j r _ _ h
    cases r with
    | nil => simp [checkRow] at h
    | cons p ps =>
      cases ps with
      | nil =>
        simp only [checkRow, pairEq_eq_true] at h
        simp [rowSpec, lcsPair_nil_right, h]
      | cons _ _ => simp [checkRow] at h
  | cons c ys ih =>
    intro j r hys hj h
    cases r with
    | nil => simp [checkRow] at h
    | cons cell cells =>
      simp only [checkRow, Bool.and_eq_true, pairEq_eq_true] at h
      have hlen_ys : (c :: ys).length = y.length - j := by
        rw [hys, List.length_drop]
      have hys_tail : ys = y.drop (j + 1) := by
        have := congrArg List.tail hys
        simpa [List.tail_drop] using this
      have hj1 : j + 1 ≤ y.length := by
        simp only [List.length_cons] at hlen_ys
        omega
      have hcells : cells = rowSpec xs ys := ih (j + 1) cells hys_tail hj1 h.2
      have hcell : cell = lcsPair xs (c :: ys) := by
        rw [h.1, evalCell_eq_combineAcc, combineAcc_zero, List.map_map]
        have hmap :
            (alpha.map ((fun x => lookupAt j x.2 (dropAfterOffset x.1 (c :: ys))) ∘
              fun a => (a, (dropAfter a xs).map (fun x' => rowSpec x' y)))) =
            alpha.map fun a => branchVal a xs (c :: ys) := by
          apply List.map_congr_left
          intro a _
          dsimp only [Function.comp_apply, lookupAt, branchVal]
          cases hdx : dropAfter a xs with
          | none => rfl
          | some x' =>
            have hoff := dropAfterOffset_spec a (c :: ys)
            cases hdy : dropAfterOffset a (c :: ys) with
            | none =>
              rw [hdy] at hoff
              simp [hoff]
            | some d =>
              rw [hdy] at hoff
              rcases hoff with ⟨_, hdle, hdrop_y⟩
              have hjd : j + d ≤ y.length := by omega
              have hdrop_eq : (c :: ys).drop d = y.drop (j + d) := by
                rw [hys, List.drop_drop, Nat.add_comm]
              simp only [Option.map_some]
              rw [hdrop_y, hdrop_eq, getOpt_eq_getElem?]
              have hadd_jd : Nat.add j d = j + d := rfl
              rw [hadd_jd]
              change (match (rowSpec x' y)[j + d]? with
                | some (L, C) => (Nat.add L 1, C)
                | none => (0, 0)) = _
              rw [rowSpec_getElem? x' y (j + d) hjd]
              rfl
        rw [hmap, combine_map_branchVal hnodup hxs]
      rw [hcell, hcells]
      rfl

private def tableSpec (y : List ℕ) : List ℕ → List (List (ℕ × ℕ))
  | [] => [rowSpec [] y]
  | b :: xs => rowSpec (b :: xs) y :: tableSpec y xs

private lemma tableSpec_getElem? (y xs : List ℕ) (d : ℕ) (hd : d ≤ xs.length) :
    (tableSpec y xs)[d]? = some (rowSpec (xs.drop d) y) := by
  induction xs generalizing d with
  | nil =>
    have hd0 : d = 0 := by simpa using hd
    subst hd0
    rfl
  | cons b xs ih =>
    cases d with
    | zero => rfl
    | succ d =>
      simp only [List.length_cons] at hd
      simpa [tableSpec] using ih d (by omega)

private lemma checkTable_sound {alpha : List ℕ} (hnodup : alpha.Nodup) (y : List ℕ) :
    ∀ (xs : List ℕ) (T : List (List (ℕ × ℕ))),
      (∀ a ∈ xs, a ∈ alpha) →
      checkTable alpha y xs T = true →
      T = tableSpec y xs := by
  intro xs
  induction xs with
  | nil =>
    intro T _ h
    cases T with
    | nil => simp [checkTable] at h
    | cons r rs =>
      cases rs with
      | nil =>
        simp only [checkTable] at h
        rw [checkNilRow_sound y.length r h, ← rowSpec_nil_left y]
        rfl
      | cons _ _ => simp [checkTable] at h
  | cons b xs ih =>
    intro T hxs h
    cases T with
    | nil => simp [checkTable] at h
    | cons r rs =>
      simp only [checkTable, Bool.and_eq_true] at h
      have hxs' : ∀ a ∈ xs, a ∈ alpha := fun a ha => hxs a (List.mem_cons_of_mem b ha)
      have hrs : rs = tableSpec y xs := ih rs hxs' h.2
      have htarget :
          (alpha.map fun a => (a, (dropAfterOffset a (b :: xs)).bind fun d => getOpt (r :: rs) d)) =
          alpha.map fun a => (a, (dropAfter a (b :: xs)).map (fun x' => rowSpec x' y)) := by
        apply List.map_congr_left
        intro a _
        congr 1
        have hoff := dropAfterOffset_spec a (b :: xs)
        cases hd : dropAfterOffset a (b :: xs) with
        | none =>
          rw [hd] at hoff
          simp [hoff]
        | some d =>
          rw [hd] at hoff
          rcases hoff with ⟨hdpos, hdle, hdrop⟩
          rw [hdrop]
          simp only [Option.bind_some, Option.map_some, getOpt_eq_getElem?]
          cases d with
          | zero => omega
          | succ d' =>
            simp only [List.getElem?_cons_succ, List.length_cons, List.drop_succ_cons] at hdle ⊢
            rw [hrs, tableSpec_getElem? y xs d' (by omega)]
      rw [htarget] at h
      have hr : r = rowSpec (b :: xs) y :=
        checkRow_sound hnodup hxs y y 0 r (by simp) (by omega) h.1
      rw [hr, hrs]
      rfl

private def tableTopCount : List (List (ℕ × ℕ)) → ℕ
  | ((_, c) :: _) :: _ => c
  | _ => 0

private lemma lcsCount_of_checkTable (k : ℕ) (x y : List ℕ) (T : List (List (ℕ × ℕ)))
    (hx : ∀ a ∈ x, a < k) (hcheck : checkTable (List.range k) y x T = true) :
    lcsCount x y = tableTopCount T := by
  have hx' : ∀ a ∈ x, a ∈ List.range k := fun a ha => List.mem_range.mpr (hx a ha)
  have hT := checkTable_sound List.nodup_range y x T hx' hcheck
  rw [hT]
  cases x <;> cases y <;> rfl

private lemma mem_ascending_lt {k n : ℕ} (hk : 0 < k) : ∀ a ∈ ascending k n, a < k := by
  intro a ha
  simp only [ascending, List.mem_map, List.mem_range] at ha
  obtain ⟨i, _, rfl⟩ := ha
  exact Nat.mod_lt i hk

private def T5 : List (List (ℕ × ℕ)) := [
  [(15,219651640),(15,147078828),(15,72572812),(14,86211476),(14,67060630),(14,47909784),(14,29807622),(14,13638664),(13,15287468),(13,10853830),(13,7046520),(13,3974504),(13,1648804),(12,1757858),(12,1091884),(12,616870),(12,302104),(12,109054),(11,111881),(11,56386),(11,25486),(11,9889),(11,2827),(10,2837),(10,980),(10,284),(10,65),(10,10),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,147078828),(15,74506016),(14,90674974),(14,72572812),(14,53421966),(14,34271120),(14,16168958),(13,18494658),(13,13638664),(13,9205026),(13,5397716),(13,2325700),(12,2518750),(12,1648804),(12,982830),(12,507816),(12,193050),(11,200112),(11,109054),(11,53559),(11,22659),(11,7062),(10,7117),(10,2827),(10,970),(10,274),(10,55),(9,55),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,72572812),(14,90674974),(14,74506016),(14,56403854),(14,37253008),(14,18102162),(13,21174178),(13,16168958),(13,11312964),(13,6879326),(13,3072016),(12,3386782),(12,2325700),(12,1455754),(12,789780),(12,314766),(11,330363),(11,193050),(11,101992),(11,46497),(11,15597),(10,15816),(10,7062),(10,2772),(10,915),(10,219),(9,219),(9,55),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,86211476),(14,72572812),(14,56403854),(14,38301692),(14,19150846),(13,22958156),(13,18102162),(13,13096942),(13,8240948),(13,3807310),(12,4282324),(12,3072016),(12,2010934),(12,1140988),(12,475014),(11,505914),(11,314766),(11,177453),(11,86395),(11,30900),(10,31596),(10,15597),(10,6843),(10,2553),(10,696),(9,697),(9,219),(9,55),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,67060630),(14,53421966),(14,37253008),(14,19150846),(13,23584484),(13,19150846),(13,14294852),(13,9289632),(13,4433638),(12,5099612),(12,3807310),(12,2597002),(12,1535920),(12,665974),(11,721469),(11,475014),(11,283866),(11,146553),(11,55495),(10,57352),(10,30900),(10,14901),(10,6147),(10,1857),(9,1866),(9,696),(9,218),(9,54),(9,9),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,47909784),(14,34271120),(14,18102162),(13,22958156),(13,19150846),(13,14717208),(13,9861214),(13,4855994),(12,5725940),(12,4433638),(12,3141336),(12,1931028),(12,869946),(11,961004),(11,665974),(11,419519),(11,228371),(11,91058),(10,95348),(10,55495),(10,29043),(10,13044),(10,4290),(9,4335),(9,1857),(9,687),(9,209),(9,45),(8,45),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,29807622),(14,16168958),(13,21174178),(13,18102162),(13,14294852),(13,9861214),(13,5005220),(12,6066302),(12,4855994),(12,3563692),(12,2271390),(12,1061082),(11,1198395),(11,869946),(11,574916),(11,328461),(11,137313),(10,146067),(10,91058),(10,51205),(10,24753),(10,8754),(9,8918),(9,4290),(9,1812),(9,642),(9,164),(8,164),(8,45),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,13638664),(13,18494658),(13,16168958),(13,13096942),(13,9289632),(13,4855994),(12,6066302),(12,5005220),(12,3794912),(12,2502610),(12,1210308),(11,1401456),(11,1061082),(11,732633),(11,437603),(11,191148),(10,207147),(10,137313),(10,82304),(10,42451),(10,15999),(9,16477),(9,8754),(9,4126),(9,1648),(9,478),(8,479),(8,164),(8,45),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,15287468),(13,13638664),(13,11312964),(13,8240948),(13,4433638),(12,5725940),(12,4855994),(12,3794912),(12,2584604),(12,1292302),(11,1538757),(11,1210308),(11,869934),(11,541485),(11,246455),(10,272907),(10,191148),(10,121314),(10,66305),(10,26452),(9,27622),(9,15999),(9,8276),(9,3648),(9,1170),(8,1178),(8,478),(8,163),(8,44),(8,8),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,10853830),(13,9205026),(13,6879326),(13,3807310),(12,5099612),(12,4433638),(12,3563692),(12,2502610),(12,1292302),(11,1587332),(11,1292302),(11,963853),(11,623479),(11,295030),(10,334883),(10,246455),(10,164696),(10,94862),(10,39853),(9,42331),(9,26452),(9,14829),(9,7106),(9,2478),(8,2514),(8,1170),(8,470),(8,155),(8,36),(7,36),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,7046520),(13,5397716),(13,3072016),(12,4282324),(12,3807310),(12,3141336),(12,2271390),(12,1210308),(11,1538757),(11,1292302),(11,997272),(11,668823),(11,328449),(10,383458),(10,295030),(10,206602),(10,124843),(10,55009),(9,59637),(9,39853),(9,23974),(9,12351),(9,4628),(8,4747),(8,2478),(8,1134),(8,434),(8,119),(7,119),(7,36),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,3974504),(13,2325700),(12,3386782),(12,3072016),(12,2597002),(12,1931028),(12,1061082),(11,1401456),(11,1210308),(11,963853),(11,668823),(11,340374),(10,410208),(10,328449),(10,240021),(10,151593),(10,69834),(9,77557),(9,55009),(9,35225),(9,19346),(9,7723),(8,8038),(8,4628),(8,2359),(8,1015),(8,315),(7,316),(7,119),(7,36),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,1648804),(12,2518750),(12,2325700),(12,2010934),(12,1535920),(12,869946),(11,1198395),(11,1061082),(11,869934),(11,623479),(11,328449),(10,410208),(10,340374),(10,258615),(10,170187),(10,81759),(9,93382),(9,69834),(9,47286),(9,27502),(9,11623),(8,12323),(8,7723),(8,4313),(8,2044),(8,700),(7,707),(7,315),(7,118),(7,35),(7,7),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,1757858),(12,1648804),(12,1455754),(12,1140988),(12,665974),(11,961004),(11,869946),(11,732633),(11,541485),(11,295030),(10,383458),(10,328449),(10,258615),(10,176856),(10,88428),(9,104307),(9,81759),(9,58211),(9,35663),(9,15879),(8,17223),(8,11623),(8,7023),(8,3613),(8,1344),(7,1372),(7,700),(7,308),(7,111),(7,28),(6,28),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,1091884),(12,982830),(12,789780),(12,475014),(11,721469),(11,665974),(11,574916),(11,437603),(11,246455),(10,334883),(10,295030),(10,240021),(10,170187),(10,88428),(9,108212),(9,88428),(9,65880),(9,42332),(9,19784),(8,22053),(8,15879),(8,10279),(8,5679),(8,2269),(7,2352),(7,1344),(7,672),(7,280),(7,83),(6,83),(6,28),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,616870),(12,507816),(12,314766),(11,505914),(11,475014),(11,419519),(11,328461),(11,191148),(10,272907),(10,246455),(10,206602),(10,151593),(10,81759),(9,104307),(9,88428),(9,68644),(9,46096),(9,22548),(8,25958),(8,19784),(8,13610),(8,8010),(8,3410),(7,3607),(7,2269),(7,1261),(7,589),(7,197),(6,198),(6,83),(6,28),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,302104),(12,193050),(11,330363),(11,314766),(11,283866),(11,228371),(11,137313),(10,207147),(10,191148),(10,164696),(10,124843),(10,69834),(9,93382),(9,81759),(9,65880),(9,46096),(9,23548),(8,28148),(8,22548),(8,16374),(8,10200),(8,4600),(7,4992),(7,3410),(7,2072),(7,1064),(7,392),(6,398),(6,197),(6,82),(6,27),(6,6),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,109054),(11,200112),(11,193050),(11,177453),(11,146553),(11,91058),(10,146067),(10,137313),(10,121314),(10,94862),(10,55009),(9,77557),(9,69834),(9,58211),(9,42332),(9,22548),(8,28148),(8,23548),(8,17948),(8,11774),(8,5600),(7,6272),(7,4600),(7,3018),(7,1680),(7,672),(6,693),(6,392),(6,191),(6,76),(6,21),(5,21),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(11,111881),(11,109054),(11,101992),(11,86395),(11,55495),(10,95348),(10,91058),(10,82304),(10,66305),(10,39853),(9,59637),(9,55009),(9,47286),(9,35663),(9,19784),(8,25958),(8,22548),(8,17948),(8,12348),(8,6174),(7,7182),(7,5600),(7,3928),(7,2346),(7,1008),(6,1063),(6,672),(6,371),(6,170),(6,55),(5,55),(5,21),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(11,56386),(11,53559),(11,46497),(11,30900),(10,57352),(10,55495),(10,51205),(10,42451),(10,26452),(9,42331),(9,39853),(9,35225),(9,27502),(9,15879),(8,22053),(8,19784),(8,16374),(8,11774),(8,6174),(7,7512),(7,6174),(7,4592),(7,2920),(7,1338),(6,1453),(6,1008),(6,617),(6,316),(6,115),(5,116),(5,55),(5,21),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(11,25486),(11,22659),(11,15597),(10,31596),(10,30900),(10,29043),(10,24753),(10,15999),(9,27622),(9,26452),(9,23974),(9,19346),(9,11623),(8,17223),(8,15879),(8,13610),(8,10200),(8,5600),(7,7182),(7,6174),(7,4836),(7,3254),(7,1582),(6,1783),(6,1338),(6,893),(6,502),(6,201),(5,206),(5,115),(5,54),(5,20),(5,5),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(11,9889),(11,7062),(10,15816),(10,15597),(10,14901),(10,13044),(10,8754),(9,16477),(9,15999),(9,14829),(9,12351),(9,7723),(8,12323),(8,11623),(8,10279),(8,8010),(8,4600),(7,6272),(7,5600),(7,4592),(7,3254),(7,1672),(6,1973),(6,1582),(6,1137),(6,692),(6,301),(5,316),(5,201),(5,110),(5,49),(5,15),(4,15),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(11,2827),(10,7117),(10,7062),(10,6843),(10,6147),(10,4290),(9,8918),(9,8754),(9,8276),(9,7106),(9,4628),(8,8038),(8,7723),(8,7023),(8,5679),(8,3410),(7,4992),(7,4600),(7,3928),(7,2920),(7,1582),(6,1973),(6,1672),(6,1281),(6,836),(6,391),(5,425),(5,301),(5,186),(5,95),(5,34),(4,34),(4,15),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(10,2837),(10,2827),(10,2772),(10,2553),(10,1857),(9,4335),(9,4290),(9,4126),(9,3648),(9,2478),(8,4747),(8,4628),(8,4313),(8,3613),(8,2269),(7,3607),(7,3410),(7,3018),(7,2346),(7,1338),(6,1783),(6,1582),(6,1281),(6,890),(6,445),(5,506),(5,391),(5,267),(5,152),(5,61),(4,62),(4,34),(4,15),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(10,980),(10,970),(10,915),(10,696),(9,1866),(9,1857),(9,1812),(9,1648),(9,1170),(8,2514),(8,2478),(8,2359),(8,2044),(8,1344),(7,2352),(7,2269),(7,2072),(7,1680),(7,1008),(6,1453),(6,1338),(6,1137),(6,836),(6,445),(5,536),(5,445),(5,330),(5,206),(5,91),(4,95),(4,61),(4,33),(4,14),(4,4),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(10,284),(10,274),(10,219),(9,697),(9,696),(9,687),(9,642),(9,478),(8,1178),(8,1170),(8,1134),(8,1015),(8,700),(7,1372),(7,1344),(7,1261),(7,1064),(7,672),(6,1063),(6,1008),(6,893),(6,692),(6,391),(5,506),(5,445),(5,354),(5,239),(5,115),(4,125),(4,91),(4,57),(4,29),(4,10),(3,10),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(10,65),(10,55),(9,219),(9,219),(9,218),(9,209),(9,164),(8,479),(8,478),(8,470),(8,434),(8,315),(7,707),(7,700),(7,672),(7,589),(7,392),(6,693),(6,672),(6,617),(6,502),(6,301),(5,425),(5,391),(5,330),(5,239),(5,124),(4,143),(4,115),(4,81),(4,47),(4,19),(3,19),(3,10),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(10,10),(9,55),(9,55),(9,55),(9,54),(9,45),(8,164),(8,164),(8,163),(8,155),(8,119),(7,316),(7,315),(7,308),(7,280),(7,197),(6,398),(6,392),(6,371),(6,316),(6,201),(5,316),(5,301),(5,267),(5,206),(5,115),(4,143),(4,124),(4,96),(4,62),(4,28),(3,29),(3,19),(3,10),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(9,10),(9,10),(9,10),(9,10),(9,9),(8,45),(8,45),(8,45),(8,44),(8,36),(7,119),(7,119),(7,118),(7,111),(7,83),(6,198),(6,197),(6,191),(6,170),(6,115),(5,206),(5,201),(5,186),(5,152),(5,91),(4,125),(4,115),(4,96),(4,68),(4,34),(3,37),(3,28),(3,18),(3,9),(3,3),(2,3),(2,1),(1,1),(0,1)],
  [(9,1),(9,1),(9,1),(9,1),(8,9),(8,9),(8,9),(8,9),(8,8),(7,36),(7,36),(7,36),(7,35),(7,28),(6,83),(6,83),(6,82),(6,76),(6,55),(5,116),(5,115),(5,110),(5,95),(5,61),(4,95),(4,91),(4,81),(4,62),(4,34),(3,40),(3,34),(3,25),(3,15),(3,6),(2,6),(2,3),(2,1),(1,1),(0,1)],
  [(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(7,8),(7,8),(7,8),(7,8),(7,7),(6,28),(6,28),(6,28),(6,27),(6,21),(5,55),(5,55),(5,54),(5,49),(5,34),(4,62),(4,61),(4,57),(4,47),(4,28),(3,37),(3,34),(3,28),(3,19),(3,9),(2,9),(2,6),(2,3),(2,1),(1,1),(0,1)],
  [(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(6,7),(6,7),(6,7),(6,7),(6,6),(5,21),(5,21),(5,21),(5,20),(5,15),(4,34),(4,34),(4,33),(4,29),(4,19),(3,29),(3,28),(3,25),(3,19),(3,10),(2,11),(2,9),(2,6),(2,3),(2,1),(1,1),(0,1)],
  [(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(5,6),(5,6),(5,6),(5,6),(5,5),(4,15),(4,15),(4,15),(4,14),(4,10),(3,19),(3,19),(3,18),(3,15),(3,9),(2,11),(2,10),(2,8),(2,5),(2,2),(1,2),(1,1),(0,1)],
  [(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(4,5),(4,5),(4,5),(4,5),(4,4),(3,10),(3,10),(3,10),(3,9),(3,6),(2,9),(2,9),(2,8),(2,6),(2,3),(1,3),(1,2),(1,1),(0,1)],
  [(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(3,4),(3,4),(3,4),(3,4),(3,3),(2,6),(2,6),(2,6),(2,5),(2,3),(1,3),(1,3),(1,2),(1,1),(0,1)],
  [(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(2,3),(2,3),(2,3),(2,3),(2,2),(1,3),(1,3),(1,3),(1,2),(1,1),(0,1)],
  [(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(1,2),(1,2),(1,2),(1,2),(1,1),(0,1),(0,1)],
  [(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(0,1),(0,1),(0,1)],
  [(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1)]
]
private def T4_0 : List (List (ℕ × ℕ)) := [
  [(19,128996853),(18,166613280),(18,124191258),(18,80038449),(18,37616427),(17,45268059),(17,30759120),(17,17980968),(17,7651632),(16,8647848),(16,5182008),(16,2661672),(16,996216),(15,1068171),(15,536640),(15,229905),(15,71955),(14,74139),(14,28665),(14,9282),(14,2184),(13,2197),(13,546),(13,104),(13,13),(12,13),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,166613280),(18,128996853),(18,86574831),(18,42422022),(17,52751358),(17,37616427),(17,23107488),(17,10329336),(16,11994792),(16,7651632),(16,4185792),(16,1665456),(15,1823406),(15,996216),(15,464685),(15,157950),(14,165048),(14,71955),(14,26481),(14,7098),(13,7189),(13,2184),(13,533),(13,91),(12,91),(12,13),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,124191258),(18,86574831),(18,44152809),(17,56930961),(17,42422022),(17,27287091),(17,12778152),(16,15298488),(16,10329336),(16,5986176),(16,2520336),(15,2827071),(15,1665456),(15,838266),(15,306735),(14,326118),(14,157950),(14,64857),(14,19383),(13,19825),(13,7098),(13,2093),(13,442),(12,443),(12,91),(12,13),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,80038449),(18,42422022),(17,56930961),(17,44152809),(17,29643870),(17,14508939),(16,17974779),(16,12778152),(16,7809000),(16,3465840),(15,3997371),(15,2520336),(15,1358721),(15,531531),(14,577005),(14,306735),(14,138567),(14,45474),(13,47125),(13,19383),(13,6656),(13,1651),(12,1663),(12,442),(12,90),(12,12),(11,12),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,37616427),(17,52751358),(17,42422022),(17,29643870),(17,15134931),(16,19478091),(16,14508939),(16,9312312),(16,4343160),(15,5170350),(15,3465840),(15,1988805),(15,827190),(14,920283),(14,531531),(14,261261),(14,93093),(13,98098),(13,45474),(13,17732),(13,5005),(12,5083),(12,1651),(12,430),(12,78),(11,78),(11,12),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,45268059),(17,37616427),(17,27287091),(17,14508939),(16,19478091),(16,15134931),(16,10165779),(16,4969152),(15,6130767),(15,4343160),(15,2638650),(15,1161615),(14,1329783),(14,827190),(14,438438),(14,168168),(13,180895),(13,93093),(13,40469),(13,12727),(12,13079),(12,5005),(12,1573),(12,352),(11,353),(11,78),(11,12),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,30759120),(17,23107488),(17,12778152),(16,17974779),(16,14508939),(16,10165779),(16,5196627),(15,6673662),(15,4969152),(15,3181545),(15,1477035),(14,1747305),(14,1161615),(14,659022),(14,270270),(13,298012),(13,168168),(13,80366),(13,27742),(12,28963),(12,12727),(12,4653),(12,1221),(11,1232),(11,352),(11,77),(11,11),(10,11),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,17980968),(17,10329336),(16,15298488),(16,12778152),(16,9312312),(16,4969152),(15,6673662),(15,5196627),(15,3492117),(15,1704510),(14,2093262),(14,1477035),(14,891345),(14,388752),(13,441376),(13,270270),(13,140426),(13,52624),(12,56056),(12,27742),(12,11506),(12,3432),(11,3498),(11,1221),(11,341),(11,66),(10,66),(10,11),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,7651632),(16,11994792),(16,10329336),(16,7809000),(16,4343160),(15,6130767),(15,4969152),(15,3492117),(15,1787607),(14,2290200),(14,1704510),(14,1088283),(14,502593),(13,590395),(13,388752),(13,217646),(13,87802),(12,95876),(12,52624),(12,24310),(12,8074),(11,8349),(11,3432),(11,1155),(11,275),(10,276),(10,66),(10,11),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,8647848),(16,7651632),(16,5986176),(16,3465840),(15,5170350),(15,4343160),(15,3181545),(15,1704510),(14,2290200),(14,1787607),(14,1201917),(14,585690),(13,715534),(13,502593),(13,300950),(13,129844),(12,146080),(12,87802),(12,44550),(12,16236),(11,17116),(11,8074),(11,3157),(11,880),(10,890),(10,275),(10,65),(10,10),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,5182008),(16,4185792),(16,2520336),(15,3997371),(15,3465840),(15,2638650),(15,1477035),(14,2093262),(14,1704510),(14,1201917),(14,616227),(13,787333),(13,585690),(13,372749),(13,171106),(12,199420),(12,129844),(12,71566),(12,28314),(11,30591),(11,16236),(11,7194),(11,2277),(10,2332),(10,880),(10,265),(10,55),(9,55),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,2661672),(16,1665456),(15,2827071),(15,2520336),(15,1988805),(15,1161615),(14,1747305),(14,1477035),(14,1088283),(14,585690),(13,787333),(13,616227),(13,414584),(13,201643),(12,244895),(12,171106),(12,101530),(12,43252),(11,48169),(11,28314),(11,13959),(11,4917),(10,5127),(10,2277),(10,825),(10,210),(9,211),(9,55),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,996216),(15,1823406),(15,1665456),(15,1358721),(15,827190),(14,1329783),(14,1161615),(14,891345),(14,502593),(13,715534),(13,585690),(13,414584),(13,212941),(12,271219),(12,201643),(12,127854),(12,58278),(11,67320),(11,43252),(11,23397),(11,9042),(10,9657),(10,4917),(10,2067),(10,615),(9,624),(9,210),(9,54),(9,9),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,1068171),(15,996216),(15,838266),(15,531531),(14,920283),(14,827190),(14,659022),(14,388752),(13,590395),(13,502593),(13,372749),(13,201643),(12,271219),(12,212941),(12,143365),(12,69576),(11,83931),(11,58278),(11,34210),(11,14355),(10,15807),(10,9042),(10,4302),(10,1452),(9,1497),(9,615),(9,201),(9,45),(8,45),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,536640),(15,464685),(15,306735),(14,577005),(14,531531),(14,438438),(14,270270),(13,441376),(13,388752),(13,300950),(13,171106),(12,244895),(12,201643),(12,143365),(12,73789),(11,93644),(11,69576),(11,43923),(11,19855),(10,22705),(10,14355),(10,7590),(10,2850),(9,3006),(9,1452),(9,570),(9,156),(8,157),(8,45),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,229905),(15,157950),(14,326118),(14,306735),(14,261261),(14,168168),(13,298012),(13,270270),(13,217646),(13,129844),(12,199420),(12,171106),(12,127854),(12,69576),(11,93644),(11,73789),(11,49721),(11,24068),(10,28808),(10,19855),(10,11505),(10,4740),(9,5154),(9,2850),(9,1296),(9,414),(8,422),(8,156),(8,44),(8,8),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,71955),(14,165048),(14,157950),(14,138567),(14,93093),(13,180895),(13,168168),(13,140426),(13,87802),(12,146080),(12,129844),(12,101530),(12,58278),(11,83931),(11,69576),(11,49721),(11,25653),(10,32418),(10,24068),(10,15115),(10,6765),(9,7647),(9,4740),(9,2436),(9,882),(8,918),(8,414),(8,148),(8,36),(7,36),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,74139),(14,71955),(14,64857),(14,45474),(13,98098),(13,93093),(13,80366),(13,52624),(12,95876),(12,87802),(12,71566),(12,43252),(11,67320),(11,58278),(11,43923),(11,24068),(10,32418),(10,25653),(10,17303),(10,8350),(9,9904),(9,6765),(9,3858),(9,1554),(8,1666),(8,882),(8,378),(8,112),(7,113),(7,36),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,28665),(14,26481),(14,19383),(13,47125),(13,45474),(13,40469),(13,27742),(12,56056),(12,52624),(12,44550),(12,28314),(11,48169),(11,43252),(11,34210),(11,19855),(10,28808),(10,24068),(10,17303),(10,8953),(9,11257),(9,8350),(9,5211),(9,2304),(8,2570),(8,1554),(8,770),(8,266),(7,273),(7,112),(7,35),(7,7),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,9282),(14,7098),(13,19825),(13,19383),(13,17732),(13,12727),(12,28963),(12,27742),(12,24310),(12,16236),(11,30591),(11,28314),(11,23397),(11,14355),(10,22705),(10,19855),(10,15115),(10,8350),(9,11257),(9,8953),(9,6046),(9,2907),(8,3411),(8,2304),(8,1288),(8,504),(7,532),(7,266),(7,105),(7,28),(6,28),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,2184),(13,7189),(13,7098),(13,6656),(13,5005),(12,13079),(12,12727),(12,11506),(12,8074),(11,17116),(11,16236),(11,13959),(11,9042),(10,15807),(10,14355),(10,11505),(10,6765),(9,9904),(9,8350),(9,6046),(9,3139),(8,3923),(8,2907),(8,1800),(8,784),(7,861),(7,504),(7,238),(7,77),(6,78),(6,28),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,2197),(13,2184),(13,2093),(13,1651),(12,5083),(12,5005),(12,4653),(12,3432),(11,8349),(11,8074),(11,7194),(11,4917),(10,9657),(10,9042),(10,7590),(10,4740),(9,7647),(9,6765),(9,5211),(9,2907),(8,3923),(8,3139),(8,2123),(8,1016),(7,1177),(7,784),(7,427),(7,161),(6,167),(6,77),(6,27),(6,6),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,546),(13,533),(13,442),(12,1663),(12,1651),(12,1573),(12,1221),(11,3498),(11,3432),(11,3157),(11,2277),(10,5127),(10,4917),(10,4302),(10,2850),(9,5154),(9,4740),(9,3858),(9,2304),(8,3411),(8,2907),(8,2123),(8,1107),(7,1373),(7,1016),(7,623),(7,266),(6,287),(6,161),(6,71),(6,21),(5,21),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,104),(13,91),(12,443),(12,442),(12,430),(12,352),(11,1232),(11,1221),(11,1155),(11,880),(10,2332),(10,2277),(10,2067),(10,1452),(9,3006),(9,2850),(9,2436),(9,1554),(8,2570),(8,2304),(8,1800),(8,1016),(7,1373),(7,1107),(7,750),(7,357),(6,407),(6,266),(6,140),(6,50),(5,51),(5,21),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,13),(12,91),(12,91),(12,90),(12,78),(11,353),(11,352),(11,341),(11,275),(10,890),(10,880),(10,825),(10,615),(9,1497),(9,1452),(9,1296),(9,882),(8,1666),(8,1554),(8,1288),(8,784),(7,1177),(7,1016),(7,750),(7,393),(6,483),(6,357),(6,216),(6,90),(5,95),(5,50),(5,20),(5,5),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,13),(12,13),(12,13),(12,12),(11,78),(11,78),(11,77),(11,66),(10,276),(10,275),(10,265),(10,210),(9,624),(9,615),(9,570),(9,414),(8,918),(8,882),(8,770),(8,504),(7,861),(7,784),(7,623),(7,357),(6,483),(6,393),(6,267),(6,126),(5,141),(5,90),(5,45),(5,15),(4,15),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,1),(12,1),(12,1),(11,12),(11,12),(11,12),(11,11),(10,66),(10,66),(10,65),(10,55),(9,211),(9,210),(9,201),(9,156),(8,422),(8,414),(8,378),(8,266),(7,532),(7,504),(7,427),(7,266),(6,407),(6,357),(6,267),(6,141),(5,171),(5,126),(5,75),(5,30),(4,31),(4,15),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(11,1),(11,1),(11,1),(11,1),(11,1),(11,1),(10,11),(10,11),(10,11),(10,10),(9,55),(9,55),(9,54),(9,45),(8,157),(8,156),(8,148),(8,112),(7,273),(7,266),(7,238),(7,161),(6,287),(6,266),(6,216),(6,126),(5,171),(5,141),(5,96),(5,45),(4,49),(4,30),(4,14),(4,4),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(9,10),(9,10),(9,10),(9,9),(8,45),(8,45),(8,44),(8,36),(7,113),(7,112),(7,105),(7,77),(6,167),(6,161),(6,140),(6,90),(5,141),(5,126),(5,96),(5,51),(4,61),(4,45),(4,26),(4,10),(3,10),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(8,9),(8,9),(8,9),(8,8),(7,36),(7,36),(7,35),(7,28),(6,78),(6,77),(6,71),(6,50),(5,95),(5,90),(5,75),(5,45),(4,61),(4,51),(4,35),(4,16),(3,17),(3,10),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(7,8),(7,8),(7,8),(7,7),(6,28),(6,28),(6,27),(6,21),(5,51),(5,50),(5,45),(5,30),(4,49),(4,45),(4,35),(4,19),(3,22),(3,16),(3,9),(3,3),(2,3),(2,1),(1,1),(0,1)],
  [(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(6,7),(6,7),(6,7),(6,6),(5,21),(5,21),(5,20),(5,15),(4,31),(4,30),(4,26),(4,16),(3,22),(3,19),(3,13),(3,6),(2,6),(2,3),(2,1),(1,1),(0,1)],
  [(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(5,6),(5,6),(5,6),(5,5),(4,15),(4,15),(4,14),(4,10),(3,17),(3,16),(3,13),(3,7),(2,8),(2,6),(2,3),(2,1),(1,1),(0,1)],
  [(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(4,5),(4,5),(4,5),(4,4),(3,10),(3,10),(3,9),(3,6),(2,8),(2,7),(2,5),(2,2),(1,2),(1,1),(0,1)],
  [(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(3,4),(3,4),(3,4),(3,3),(2,6),(2,6),(2,5),(2,3),(1,3),(1,2),(1,1),(0,1)],
  [(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(2,3),(2,3),(2,3),(2,2),(1,3),(1,3),(1,2),(1,1),(0,1)],
  [(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(1,2),(1,2),(1,2),(1,1),(0,1),(0,1)],
  [(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(0,1),(0,1),(0,1)],
  [(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1)]
]
private def T4_1 : List (List (ℕ × ℕ)) := [
  [(19,173149662),(19,86574831),(18,109682319),(18,80038449),(18,50394579),(18,23107488),(17,27293280),(17,17980968),(17,10171968),(17,4185792),(16,4650477),(16,2661672),(16,1302951),(16,464685),(15,491166),(15,229905),(15,91338),(15,26481),(14,27014),(14,9282),(14,2626),(14,533),(13,534),(13,104),(13,14),(13,1),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(19,86574831),(18,113861922),(18,86574831),(18,56930961),(18,27287091),(17,33273267),(17,23107488),(17,13795176),(17,5986176),(16,6824442),(16,4185792),(16,2196987),(16,838266),(15,903123),(15,464685),(15,203424),(15,64857),(14,66950),(14,26481),(14,8749),(14,2093),(13,2106),(13,533),(13,103),(13,13),(12,13),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,109682319),(18,86574831),(18,59287740),(18,29643870),(17,37452870),(17,27287091),(17,17121312),(17,7809000),(16,9167721),(16,5986176),(16,3347526),(16,1358721),(15,1497288),(15,838266),(15,399828),(15,138567),(14,145223),(14,64857),(14,24388),(14,6656),(13,6746),(13,2093),(13,520),(13,90),(12,90),(12,13),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,80038449),(18,56930961),(18,29643870),(17,38956182),(17,29643870),(17,19478091),(17,9312312),(16,11301117),(16,7809000),(16,4627455),(16,1988805),(15,2250066),(15,1358721),(15,699699),(15,261261),(14,278993),(14,138567),(14,58201),(14,17732),(13,18162),(13,6656),(13,2003),(13,430),(12,431),(12,90),(12,13),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,50394579),(18,27287091),(17,37452870),(17,29643870),(17,20331558),(17,10165779),(16,12804429),(16,9312312),(16,5820195),(16,2638650),(15,3077088),(15,1988805),(15,1097460),(15,438438),(14,478907),(14,261261),(14,120835),(14,40469),(13,42042),(13,17732),(13,6226),(13,1573),(12,1585),(12,430),(12,89),(12,12),(11,12),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,23107488),(17,33273267),(17,27287091),(17,19478091),(17,10165779),(16,13347324),(16,10165779),(16,6673662),(16,3181545),(15,3840567),(15,2638650),(15,1550367),(15,659022),(14,739388),(14,438438),(14,220792),(14,80366),(13,85019),(13,40469),(13,16159),(13,4653),(12,4730),(12,1573),(12,418),(12,77),(11,77),(11,12),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,27293280),(17,23107488),(17,17121312),(17,9312312),(16,12804429),(16,10165779),(16,6984234),(16,3492117),(15,4383462),(15,3181545),(15,1979628),(15,891345),(14,1031771),(14,659022),(14,358072),(14,140426),(13,151932),(13,80366),(13,35816),(13,11506),(12,11847),(12,4653),(12,1496),(12,341),(11,342),(11,77),(11,12),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,17980968),(17,13795176),(17,7809000),(16,11301117),(16,9312312),(16,6673662),(16,3492117),(15,4580400),(15,3492117),(15,2290200),(15,1088283),(14,1305929),(14,891345),(14,518596),(14,217646),(13,241956),(13,140426),(13,68860),(13,24310),(12,25465),(12,11506),(12,4312),(12,1155),(11,1166),(11,341),(11,76),(11,11),(10,11),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,10171968),(17,5986176),(16,9167721),(16,7809000),(16,5820195),(16,3181545),(15,4383462),(15,3492117),(15,2403834),(15,1201917),(14,1502867),(14,1088283),(14,673699),(14,300950),(13,345500),(13,217646),(13,116116),(13,44550),(12,47707),(12,24310),(12,10351),(12,3157),(11,3222),(11,1155),(11,330),(11,65),(10,65),(10,11),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,4185792),(16,6824442),(16,5986176),(16,4627455),(16,2638650),(15,3840567),(15,3181545),(15,2290200),(15,1201917),(14,1574666),(14,1201917),(14,787333),(14,372749),(13,444315),(13,300950),(13,173096),(13,71566),(12,78760),(12,44550),(12,21153),(12,7194),(11,7459),(11,3157),(11,1090),(11,265),(10,266),(10,65),(10,11),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,4650477),(16,4185792),(16,3347526),(16,1988805),(15,3077088),(15,2638650),(15,1979628),(15,1088283),(14,1502867),(14,1201917),(14,829168),(14,414584),(13,516114),(13,372749),(13,229384),(13,101530),(12,115489),(12,71566),(12,37356),(12,13959),(11,14784),(11,7194),(11,2892),(11,825),(10,835),(10,265),(10,64),(10,10),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,2661672),(16,2196987),(16,1358721),(15,2250066),(15,1988805),(15,1550367),(15,891345),(14,1305929),(14,1088283),(14,787333),(14,414584),(13,542438),(13,414584),(13,271219),(13,127854),(12,151251),(12,101530),(12,57607),(12,23397),(11,25464),(11,13959),(11,6369),(11,2067),(10,2121),(10,825),(10,255),(10,54),(9,54),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,1302951),(16,838266),(15,1497288),(15,1358721),(15,1097460),(15,659022),(14,1031771),(14,891345),(14,673699),(14,372749),(13,516114),(13,414584),(13,286730),(13,143365),(12,177575),(12,127854),(12,78133),(12,34210),(11,38512),(11,23397),(11,11892),(11,4302),(10,4503),(10,2067),(10,771),(10,201),(9,202),(9,54),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,464685),(15,903123),(15,838266),(15,699699),(15,438438),(14,739388),(14,659022),(14,518596),(14,300950),(13,444315),(13,372749),(13,271219),(13,143365),(12,187288),(12,143365),(12,93644),(12,43923),(11,51513),(11,34210),(11,19095),(11,7590),(10,8160),(10,4302),(10,1866),(10,570),(9,579),(9,201),(9,53),(9,9),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,491166),(15,464685),(15,399828),(15,261261),(14,478907),(14,438438),(14,358072),(14,217646),(13,345500),(13,300950),(13,229384),(13,127854),(12,177575),(12,143365),(12,99442),(12,49721),(11,61226),(11,43923),(11,26620),(11,11505),(10,12801),(10,7590),(10,3732),(10,1296),(9,1340),(9,570),(9,192),(9,44),(8,44),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,229905),(15,203424),(15,138567),(14,278993),(14,261261),(14,220792),(14,140426),(13,241956),(13,217646),(13,173096),(13,101530),(12,151251),(12,127854),(12,93644),(12,49721),(11,64836),(11,49721),(11,32418),(11,15115),(10,17551),(10,11505),(10,6294),(10,2436),(9,2584),(9,1296),(9,526),(9,148),(8,149),(8,44),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,91338),(15,64857),(14,145223),(14,138567),(14,120835),(14,80366),(13,151932),(13,140426),(13,116116),(13,71566),(12,115489),(12,101530),(12,78133),(12,43923),(11,61226),(11,49721),(11,34606),(11,17303),(10,21161),(10,15115),(10,9069),(10,3858),(9,4236),(9,2436),(9,1148),(9,378),(8,386),(8,148),(8,43),(8,8),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,26481),(14,66950),(14,64857),(14,58201),(14,40469),(13,85019),(13,80366),(13,68860),(13,44550),(12,78760),(12,71566),(12,57607),(12,34210),(11,51513),(11,43923),(11,32418),(11,17303),(10,22514),(10,17303),(10,11257),(10,5211),(9,5981),(9,3858),(9,2058),(9,770),(8,805),(8,378),(8,140),(8,35),(7,35),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,27014),(14,26481),(14,24388),(14,17732),(13,42042),(13,40469),(13,35816),(13,24310),(12,47707),(12,44550),(12,37356),(12,23397),(11,38512),(11,34210),(11,26620),(11,15115),(10,21161),(10,17303),(10,12092),(10,6046),(9,7334),(9,5211),(9,3088),(9,1288),(8,1393),(8,770),(8,343),(8,105),(7,106),(7,35),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,9282),(14,8749),(14,6656),(13,18162),(13,17732),(13,16159),(13,11506),(12,25465),(12,24310),(12,21153),(12,13959),(11,25464),(11,23397),(11,19095),(11,11505),(10,17551),(10,15115),(10,11257),(10,6046),(9,7846),(9,6046),(9,3923),(9,1800),(8,2038),(8,1288),(8,665),(8,238),(7,245),(7,105),(7,34),(7,7),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,2626),(14,2093),(13,6746),(13,6656),(13,6226),(13,4653),(12,11847),(12,11506),(12,10351),(12,7194),(11,14784),(11,13959),(11,11892),(11,7590),(10,12801),(10,11505),(10,9069),(10,5211),(9,7334),(9,6046),(9,4246),(9,2123),(8,2550),(8,1800),(8,1050),(8,427),(7,454),(7,238),(7,98),(7,27),(6,27),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,533),(13,2106),(13,2093),(13,2003),(13,1573),(12,4730),(12,4653),(12,4312),(12,3157),(11,7459),(11,7194),(11,6369),(11,4302),(10,8160),(10,7590),(10,6294),(10,3858),(9,5981),(9,5211),(9,3923),(9,2123),(8,2746),(8,2123),(8,1373),(8,623),(7,694),(7,427),(7,211),(7,71),(6,72),(6,27),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,534),(13,533),(13,520),(13,430),(12,1585),(12,1573),(12,1496),(12,1155),(11,3222),(11,3157),(11,2892),(11,2067),(10,4503),(10,4302),(10,3732),(10,2436),(9,4236),(9,3858),(9,3088),(9,1800),(8,2550),(8,2123),(8,1500),(8,750),(7,890),(7,623),(7,356),(7,140),(6,146),(6,71),(6,26),(6,6),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,104),(13,103),(13,90),(12,431),(12,430),(12,418),(12,341),(11,1166),(11,1155),(11,1090),(11,825),(10,2121),(10,2067),(10,1866),(10,1296),(9,2584),(9,2436),(9,2058),(9,1288),(8,2038),(8,1800),(8,1373),(8,750),(7,966),(7,750),(7,483),(7,216),(6,236),(6,140),(6,65),(6,20),(5,20),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,14),(13,13),(12,90),(12,90),(12,89),(12,77),(11,342),(11,341),(11,330),(11,265),(10,835),(10,825),(10,771),(10,570),(9,1340),(9,1296),(9,1148),(9,770),(8,1393),(8,1288),(8,1050),(8,623),(7,890),(7,750),(7,534),(7,267),(6,312),(6,216),(6,120),(6,45),(5,46),(5,20),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,1),(12,13),(12,13),(12,13),(12,12),(11,77),(11,77),(11,76),(11,65),(10,266),(10,265),(10,255),(10,201),(9,579),(9,570),(9,526),(9,378),(8,805),(8,770),(8,665),(8,427),(7,694),(7,623),(7,483),(7,267),(6,342),(6,267),(6,171),(6,75),(5,80),(5,45),(5,19),(5,5),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,1),(12,1),(12,1),(12,1),(11,12),(11,12),(11,12),(11,11),(10,65),(10,65),(10,64),(10,54),(9,202),(9,201),(9,192),(9,148),(8,386),(8,378),(8,343),(8,238),(7,454),(7,427),(7,356),(7,216),(6,312),(6,267),(6,192),(6,96),(5,110),(5,75),(5,40),(5,14),(4,14),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(11,1),(11,1),(11,1),(11,1),(11,1),(11,1),(11,1),(10,11),(10,11),(10,11),(10,10),(9,54),(9,54),(9,53),(9,44),(8,149),(8,148),(8,140),(8,105),(7,245),(7,238),(7,211),(7,140),(6,236),(6,216),(6,171),(6,96),(5,122),(5,96),(5,61),(5,26),(4,27),(4,14),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(9,10),(9,10),(9,10),(9,9),(8,44),(8,44),(8,43),(8,35),(7,106),(7,105),(7,98),(7,71),(6,146),(6,140),(6,120),(6,75),(5,110),(5,96),(5,70),(5,35),(4,39),(4,26),(4,13),(4,4),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(8,9),(8,9),(8,9),(8,8),(7,35),(7,35),(7,34),(7,27),(6,72),(6,71),(6,65),(6,45),(5,80),(5,75),(5,61),(5,35),(4,44),(4,35),(4,22),(4,9),(3,9),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(7,8),(7,8),(7,8),(7,7),(6,27),(6,27),(6,26),(6,20),(5,46),(5,45),(5,40),(5,26),(4,39),(4,35),(4,26),(4,13),(3,14),(3,9),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(6,7),(6,7),(6,7),(6,6),(5,20),(5,20),(5,19),(5,14),(4,27),(4,26),(4,22),(4,13),(3,16),(3,13),(3,8),(3,3),(2,3),(2,1),(1,1),(0,1)],
  [(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(5,6),(5,6),(5,6),(5,5),(4,14),(4,14),(4,13),(4,9),(3,14),(3,13),(3,10),(3,5),(2,5),(2,3),(2,1),(1,1),(0,1)],
  [(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(4,5),(4,5),(4,5),(4,4),(3,9),(3,9),(3,8),(3,5),(2,6),(2,5),(2,3),(2,1),(1,1),(0,1)],
  [(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(3,4),(3,4),(3,4),(3,3),(2,5),(2,5),(2,4),(2,2),(1,2),(1,1),(0,1)],
  [(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(2,3),(2,3),(2,3),(2,2),(1,2),(1,2),(1,1),(0,1)],
  [(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(1,2),(1,2),(1,2),(1,1),(0,1)],
  [(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(0,1),(0,1)],
  [(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1)]
]
private def T4_2 : List (List (ℕ × ℕ)) := [
  [(19,128996853),(19,86574831),(19,42422022),(18,52751358),(18,37616427),(18,23107488),(18,10329336),(17,11994792),(17,7651632),(17,4185792),(17,1665456),(16,1823406),(16,996216),(16,464685),(16,157950),(15,165048),(15,71955),(15,26481),(15,7098),(14,7189),(14,2184),(14,533),(14,91),(13,91),(13,13),(13,1),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(19,86574831),(19,44152809),(18,56930961),(18,42422022),(18,27287091),(18,12778152),(17,15298488),(17,10329336),(17,5986176),(17,2520336),(16,2827071),(16,1665456),(16,838266),(16,306735),(15,326118),(15,157950),(15,64857),(15,19383),(14,19825),(14,7098),(14,2093),(14,442),(13,443),(13,91),(13,13),(13,1),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(19,42422022),(18,56930961),(18,44152809),(18,29643870),(18,14508939),(17,17974779),(17,12778152),(17,7809000),(17,3465840),(16,3997371),(16,2520336),(16,1358721),(16,531531),(15,577005),(15,306735),(15,138567),(15,45474),(14,47125),(14,19383),(14,6656),(14,1651),(13,1663),(13,442),(13,90),(13,12),(12,12),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,52751358),(18,42422022),(18,29643870),(18,15134931),(17,19478091),(17,14508939),(17,9312312),(17,4343160),(16,5170350),(16,3465840),(16,1988805),(16,827190),(15,920283),(15,531531),(15,261261),(15,93093),(14,98098),(14,45474),(14,17732),(14,5005),(13,5083),(13,1651),(13,430),(13,78),(12,78),(12,12),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,37616427),(18,27287091),(18,14508939),(17,19478091),(17,15134931),(17,10165779),(17,4969152),(16,6130767),(16,4343160),(16,2638650),(16,1161615),(15,1329783),(15,827190),(15,438438),(15,168168),(14,180895),(14,93093),(14,40469),(14,12727),(13,13079),(13,5005),(13,1573),(13,352),(12,353),(12,78),(12,12),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,23107488),(18,12778152),(17,17974779),(17,14508939),(17,10165779),(17,5196627),(16,6673662),(16,4969152),(16,3181545),(16,1477035),(15,1747305),(15,1161615),(15,659022),(15,270270),(14,298012),(14,168168),(14,80366),(14,27742),(13,28963),(13,12727),(13,4653),(13,1221),(12,1232),(12,352),(12,77),(12,11),(11,11),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,10329336),(17,15298488),(17,12778152),(17,9312312),(17,4969152),(16,6673662),(16,5196627),(16,3492117),(16,1704510),(15,2093262),(15,1477035),(15,891345),(15,388752),(14,441376),(14,270270),(14,140426),(14,52624),(13,56056),(13,27742),(13,11506),(13,3432),(12,3498),(12,1221),(12,341),(12,66),(11,66),(11,11),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,11994792),(17,10329336),(17,7809000),(17,4343160),(16,6130767),(16,4969152),(16,3492117),(16,1787607),(15,2290200),(15,1704510),(15,1088283),(15,502593),(14,590395),(14,388752),(14,217646),(14,87802),(13,95876),(13,52624),(13,24310),(13,8074),(12,8349),(12,3432),(12,1155),(12,275),(11,276),(11,66),(11,11),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,7651632),(17,5986176),(17,3465840),(16,5170350),(16,4343160),(16,3181545),(16,1704510),(15,2290200),(15,1787607),(15,1201917),(15,585690),(14,715534),(14,502593),(14,300950),(14,129844),(13,146080),(13,87802),(13,44550),(13,16236),(12,17116),(12,8074),(12,3157),(12,880),(11,890),(11,275),(11,65),(11,10),(10,10),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,4185792),(17,2520336),(16,3997371),(16,3465840),(16,2638650),(16,1477035),(15,2093262),(15,1704510),(15,1201917),(15,616227),(14,787333),(14,585690),(14,372749),(14,171106),(13,199420),(13,129844),(13,71566),(13,28314),(12,30591),(12,16236),(12,7194),(12,2277),(11,2332),(11,880),(11,265),(11,55),(10,55),(10,10),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,1665456),(16,2827071),(16,2520336),(16,1988805),(16,1161615),(15,1747305),(15,1477035),(15,1088283),(15,585690),(14,787333),(14,616227),(14,414584),(14,201643),(13,244895),(13,171106),(13,101530),(13,43252),(12,48169),(12,28314),(12,13959),(12,4917),(11,5127),(11,2277),(11,825),(11,210),(10,211),(10,55),(10,10),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,1823406),(16,1665456),(16,1358721),(16,827190),(15,1329783),(15,1161615),(15,891345),(15,502593),(14,715534),(14,585690),(14,414584),(14,212941),(13,271219),(13,201643),(13,127854),(13,58278),(12,67320),(12,43252),(12,23397),(12,9042),(11,9657),(11,4917),(11,2067),(11,615),(10,624),(10,210),(10,54),(10,9),(9,9),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,996216),(16,838266),(16,531531),(15,920283),(15,827190),(15,659022),(15,388752),(14,590395),(14,502593),(14,372749),(14,201643),(13,271219),(13,212941),(13,143365),(13,69576),(12,83931),(12,58278),(12,34210),(12,14355),(11,15807),(11,9042),(11,4302),(11,1452),(10,1497),(10,615),(10,201),(10,45),(9,45),(9,9),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,464685),(16,306735),(15,577005),(15,531531),(15,438438),(15,270270),(14,441376),(14,388752),(14,300950),(14,171106),(13,244895),(13,201643),(13,143365),(13,73789),(12,93644),(12,69576),(12,43923),(12,19855),(11,22705),(11,14355),(11,7590),(11,2850),(10,3006),(10,1452),(10,570),(10,156),(9,157),(9,45),(9,9),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,157950),(15,326118),(15,306735),(15,261261),(15,168168),(14,298012),(14,270270),(14,217646),(14,129844),(13,199420),(13,171106),(13,127854),(13,69576),(12,93644),(12,73789),(12,49721),(12,24068),(11,28808),(11,19855),(11,11505),(11,4740),(10,5154),(10,2850),(10,1296),(10,414),(9,422),(9,156),(9,44),(9,8),(8,8),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,165048),(15,157950),(15,138567),(15,93093),(14,180895),(14,168168),(14,140426),(14,87802),(13,146080),(13,129844),(13,101530),(13,58278),(12,83931),(12,69576),(12,49721),(12,25653),(11,32418),(11,24068),(11,15115),(11,6765),(10,7647),(10,4740),(10,2436),(10,882),(9,918),(9,414),(9,148),(9,36),(8,36),(8,8),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,71955),(15,64857),(15,45474),(14,98098),(14,93093),(14,80366),(14,52624),(13,95876),(13,87802),(13,71566),(13,43252),(12,67320),(12,58278),(12,43923),(12,24068),(11,32418),(11,25653),(11,17303),(11,8350),(10,9904),(10,6765),(10,3858),(10,1554),(9,1666),(9,882),(9,378),(9,112),(8,113),(8,36),(8,8),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,26481),(15,19383),(14,47125),(14,45474),(14,40469),(14,27742),(13,56056),(13,52624),(13,44550),(13,28314),(12,48169),(12,43252),(12,34210),(12,19855),(11,28808),(11,24068),(11,17303),(11,8953),(10,11257),(10,8350),(10,5211),(10,2304),(9,2570),(9,1554),(9,770),(9,266),(8,273),(8,112),(8,35),(8,7),(7,7),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,7098),(14,19825),(14,19383),(14,17732),(14,12727),(13,28963),(13,27742),(13,24310),(13,16236),(12,30591),(12,28314),(12,23397),(12,14355),(11,22705),(11,19855),(11,15115),(11,8350),(10,11257),(10,8953),(10,6046),(10,2907),(9,3411),(9,2304),(9,1288),(9,504),(8,532),(8,266),(8,105),(8,28),(7,28),(7,7),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,7189),(14,7098),(14,6656),(14,5005),(13,13079),(13,12727),(13,11506),(13,8074),(12,17116),(12,16236),(12,13959),(12,9042),(11,15807),(11,14355),(11,11505),(11,6765),(10,9904),(10,8350),(10,6046),(10,3139),(9,3923),(9,2907),(9,1800),(9,784),(8,861),(8,504),(8,238),(8,77),(7,78),(7,28),(7,7),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,2184),(14,2093),(14,1651),(13,5083),(13,5005),(13,4653),(13,3432),(12,8349),(12,8074),(12,7194),(12,4917),(11,9657),(11,9042),(11,7590),(11,4740),(10,7647),(10,6765),(10,5211),(10,2907),(9,3923),(9,3139),(9,2123),(9,1016),(8,1177),(8,784),(8,427),(8,161),(7,167),(7,77),(7,27),(7,6),(6,6),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,533),(14,442),(13,1663),(13,1651),(13,1573),(13,1221),(12,3498),(12,3432),(12,3157),(12,2277),(11,5127),(11,4917),(11,4302),(11,2850),(10,5154),(10,4740),(10,3858),(10,2304),(9,3411),(9,2907),(9,2123),(9,1107),(8,1373),(8,1016),(8,623),(8,266),(7,287),(7,161),(7,71),(7,21),(6,21),(6,6),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,91),(13,443),(13,442),(13,430),(13,352),(12,1232),(12,1221),(12,1155),(12,880),(11,2332),(11,2277),(11,2067),(11,1452),(10,3006),(10,2850),(10,2436),(10,1554),(9,2570),(9,2304),(9,1800),(9,1016),(8,1373),(8,1107),(8,750),(8,357),(7,407),(7,266),(7,140),(7,50),(6,51),(6,21),(6,6),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,91),(13,91),(13,90),(13,78),(12,353),(12,352),(12,341),(12,275),(11,890),(11,880),(11,825),(11,615),(10,1497),(10,1452),(10,1296),(10,882),(9,1666),(9,1554),(9,1288),(9,784),(8,1177),(8,1016),(8,750),(8,393),(7,483),(7,357),(7,216),(7,90),(6,95),(6,50),(6,20),(6,5),(5,5),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,13),(13,13),(13,12),(12,78),(12,78),(12,77),(12,66),(11,276),(11,275),(11,265),(11,210),(10,624),(10,615),(10,570),(10,414),(9,918),(9,882),(9,770),(9,504),(8,861),(8,784),(8,623),(8,357),(7,483),(7,393),(7,267),(7,126),(6,141),(6,90),(6,45),(6,15),(5,15),(5,5),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,1),(13,1),(12,12),(12,12),(12,12),(12,11),(11,66),(11,66),(11,65),(11,55),(10,211),(10,210),(10,201),(10,156),(9,422),(9,414),(9,378),(9,266),(8,532),(8,504),(8,427),(8,266),(7,407),(7,357),(7,267),(7,141),(6,171),(6,126),(6,75),(6,30),(5,31),(5,15),(5,5),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,1),(12,1),(12,1),(12,1),(12,1),(11,11),(11,11),(11,11),(11,10),(10,55),(10,55),(10,54),(10,45),(9,157),(9,156),(9,148),(9,112),(8,273),(8,266),(8,238),(8,161),(7,287),(7,266),(7,216),(7,126),(6,171),(6,141),(6,96),(6,45),(5,49),(5,30),(5,14),(5,4),(4,4),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(11,1),(11,1),(11,1),(11,1),(11,1),(11,1),(11,1),(11,1),(10,10),(10,10),(10,10),(10,9),(9,45),(9,45),(9,44),(9,36),(8,113),(8,112),(8,105),(8,77),(7,167),(7,161),(7,140),(7,90),(6,141),(6,126),(6,96),(6,51),(5,61),(5,45),(5,26),(5,10),(4,10),(4,4),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(9,9),(9,9),(9,9),(9,8),(8,36),(8,36),(8,35),(8,28),(7,78),(7,77),(7,71),(7,50),(6,95),(6,90),(6,75),(6,45),(5,61),(5,51),(5,35),(5,16),(4,17),(4,10),(4,4),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(8,8),(8,8),(8,8),(8,7),(7,28),(7,28),(7,27),(7,21),(6,51),(6,50),(6,45),(6,30),(5,49),(5,45),(5,35),(5,19),(4,22),(4,16),(4,9),(4,3),(3,3),(3,1),(2,1),(1,1),(0,1)],
  [(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(7,7),(7,7),(7,7),(7,6),(6,21),(6,21),(6,20),(6,15),(5,31),(5,30),(5,26),(5,16),(4,22),(4,19),(4,13),(4,6),(3,6),(3,3),(3,1),(2,1),(1,1),(0,1)],
  [(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(6,6),(6,6),(6,6),(6,5),(5,15),(5,15),(5,14),(5,10),(4,17),(4,16),(4,13),(4,7),(3,8),(3,6),(3,3),(3,1),(2,1),(1,1),(0,1)],
  [(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(5,5),(5,5),(5,5),(5,4),(4,10),(4,10),(4,9),(4,6),(3,8),(3,7),(3,5),(3,2),(2,2),(2,1),(1,1),(0,1)],
  [(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(4,4),(4,4),(4,4),(4,3),(3,6),(3,6),(3,5),(3,3),(2,3),(2,2),(2,1),(1,1),(0,1)],
  [(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(3,3),(3,3),(3,3),(3,2),(2,3),(2,3),(2,2),(2,1),(1,1),(0,1)],
  [(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(2,2),(2,2),(2,2),(2,1),(1,1),(1,1),(0,1)],
  [(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(1,1),(1,1),(1,1),(0,1)],
  [(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(0,1)],
  [(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1)]
]
private def T4_3 : List (List (ℕ × ℕ)) := [
  [(18,219364638),(18,166613280),(18,109682319),(18,52751358),(17,64746150),(17,45268059),(17,27293280),(17,11994792),(16,13818198),(16,8647848),(16,4650477),(16,1823406),(15,1988454),(15,1068171),(15,491166),(15,165048),(14,172237),(14,74139),(14,27014),(14,7189),(13,7280),(13,2197),(13,534),(13,91),(12,91),(12,13),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,166613280),(18,113861922),(18,56930961),(17,72229449),(17,52751358),(17,33273267),(17,15298488),(16,18125559),(16,11994792),(16,6824442),(16,2827071),(15,3153189),(15,1823406),(15,903123),(15,326118),(14,345943),(14,165048),(14,66950),(14,19825),(13,20268),(13,7189),(13,2106),(13,443),(12,444),(12,91),(12,13),(12,1),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,109682319),(18,56930961),(17,74905740),(17,56930961),(17,37452870),(17,17974779),(16,21972150),(16,15298488),(16,9167721),(16,3997371),(15,4574376),(15,2827071),(15,1497288),(15,577005),(14,624130),(14,326118),(14,145223),(14,47125),(13,48788),(13,19825),(13,6746),(13,1663),(12,1675),(12,443),(12,90),(12,12),(11,12),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(18,52751358),(17,72229449),(17,56930961),(17,38956182),(17,19478091),(16,24648441),(16,17974779),(16,11301117),(16,5170350),(15,6090633),(15,3997371),(15,2250066),(15,920283),(14,1018381),(14,577005),(14,278993),(14,98098),(13,103181),(13,47125),(13,18162),(13,5083),(12,5161),(12,1663),(12,431),(12,78),(11,78),(11,12),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,64746150),(17,52751358),(17,37452870),(17,19478091),(16,25608858),(16,19478091),(16,12804429),(16,6130767),(15,7460550),(15,5170350),(15,3077088),(15,1329783),(14,1510678),(14,920283),(14,478907),(14,180895),(13,193974),(13,98098),(13,42042),(13,13079),(12,13432),(12,5083),(12,1585),(12,353),(11,354),(11,78),(11,12),(11,1),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,45268059),(17,33273267),(17,17974779),(16,24648441),(16,19478091),(16,13347324),(16,6673662),(15,8420967),(15,6130767),(15,3840567),(15,1747305),(14,2045317),(14,1329783),(14,739388),(14,298012),(13,326975),(13,180895),(13,85019),(13,28963),(12,30195),(12,13079),(12,4730),(12,1232),(11,1243),(11,353),(11,77),(11,11),(10,11),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,27293280),(17,15298488),(16,21972150),(16,17974779),(16,12804429),(16,6673662),(15,8766924),(15,6673662),(15,4383462),(15,2093262),(14,2534638),(14,1747305),(14,1031771),(14,441376),(13,497432),(13,298012),(13,151932),(13,56056),(12,59554),(12,28963),(12,11847),(12,3498),(11,3564),(11,1232),(11,342),(11,66),(10,66),(10,11),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(17,11994792),(16,18125559),(16,15298488),(16,11301117),(16,6130767),(15,8420967),(15,6673662),(15,4580400),(15,2290200),(14,2880595),(14,2093262),(14,1305929),(14,590395),(13,686271),(13,441376),(13,241956),(13,95876),(12,104225),(12,56056),(12,25465),(12,8349),(11,8625),(11,3498),(11,1166),(11,276),(10,277),(10,66),(10,11),(10,1),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,13818198),(16,11994792),(16,9167721),(16,5170350),(15,7460550),(15,6130767),(15,4383462),(15,2290200),(14,3005734),(14,2290200),(14,1502867),(14,715534),(13,861614),(13,590395),(13,345500),(13,146080),(12,163196),(12,95876),(12,47707),(12,17116),(11,18006),(11,8349),(11,3222),(11,890),(10,900),(10,276),(10,65),(10,10),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,8647848),(16,6824442),(16,3997371),(15,6090633),(15,5170350),(15,3840567),(15,2093262),(14,2880595),(14,2290200),(14,1574666),(14,787333),(13,986753),(13,715534),(13,444315),(13,199420),(12,230011),(12,146080),(12,78760),(12,30591),(11,32923),(11,17116),(11,7459),(11,2332),(10,2387),(10,890),(10,266),(10,55),(9,55),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,4650477),(16,2827071),(15,4574376),(15,3997371),(15,3077088),(15,1747305),(14,2534638),(14,2093262),(14,1502867),(14,787333),(13,1032228),(13,787333),(13,516114),(13,244895),(12,293064),(12,199420),(12,115489),(12,48169),(11,53296),(11,30591),(11,14784),(11,5127),(10,5338),(10,2332),(10,835),(10,211),(9,212),(9,55),(9,10),(9,1),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(16,1823406),(15,3153189),(15,2827071),(15,2250066),(15,1329783),(14,2045317),(14,1747305),(14,1305929),(14,715534),(13,986753),(13,787333),(13,542438),(13,271219),(12,338539),(12,244895),(12,151251),(12,67320),(11,76977),(11,48169),(11,25464),(11,9657),(10,10281),(10,5127),(10,2121),(10,624),(9,633),(9,211),(9,54),(9,9),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,1988454),(15,1823406),(15,1497288),(15,920283),(14,1510678),(14,1329783),(14,1031771),(14,590395),(13,861614),(13,715534),(13,516114),(13,271219),(12,355150),(12,271219),(12,177575),(12,83931),(11,99738),(11,67320),(11,38512),(11,15807),(10,17304),(10,9657),(10,4503),(10,1497),(9,1542),(9,624),(9,202),(9,45),(8,45),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,1068171),(15,903123),(15,577005),(14,1018381),(14,920283),(14,739388),(14,441376),(13,686271),(13,590395),(13,444315),(13,244895),(12,338539),(12,271219),(12,187288),(12,93644),(11,116349),(11,83931),(11,51513),(11,22705),(10,25711),(10,15807),(10,8160),(10,3006),(9,3163),(9,1497),(9,579),(9,157),(8,158),(8,45),(8,9),(8,1),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,491166),(15,326118),(14,624130),(14,577005),(14,478907),(14,298012),(13,497432),(13,441376),(13,345500),(13,199420),(12,293064),(12,244895),(12,177575),(12,93644),(11,122452),(11,93644),(11,61226),(11,28808),(10,33962),(10,22705),(10,12801),(10,5154),(9,5576),(9,3006),(9,1340),(9,422),(8,430),(8,157),(8,44),(8,8),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(15,165048),(14,345943),(14,326118),(14,278993),(14,180895),(13,326975),(13,298012),(13,241956),(13,146080),(12,230011),(12,199420),(12,151251),(12,83931),(11,116349),(11,93644),(11,64836),(11,32418),(10,40065),(10,28808),(10,17551),(10,7647),(9,8565),(9,5154),(9,2584),(9,918),(8,954),(8,422),(8,149),(8,36),(7,36),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,172237),(14,165048),(14,145223),(14,98098),(13,193974),(13,180895),(13,151932),(13,95876),(12,163196),(12,146080),(12,115489),(12,67320),(11,99738),(11,83931),(11,61226),(11,32418),(10,42322),(10,32418),(10,21161),(10,9904),(9,11570),(9,7647),(9,4236),(9,1666),(8,1779),(8,918),(8,386),(8,113),(7,114),(7,36),(7,8),(7,1),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,74139),(14,66950),(14,47125),(13,103181),(13,98098),(13,85019),(13,56056),(12,104225),(12,95876),(12,78760),(12,48169),(11,76977),(11,67320),(11,51513),(11,28808),(10,40065),(10,32418),(10,22514),(10,11257),(9,13827),(9,9904),(9,5981),(9,2570),(8,2843),(8,1666),(8,805),(8,273),(7,280),(7,113),(7,35),(7,7),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,27014),(14,19825),(13,48788),(13,47125),(13,42042),(13,28963),(12,59554),(12,56056),(12,47707),(12,30591),(11,53296),(11,48169),(11,38512),(11,22705),(10,33962),(10,28808),(10,21161),(10,11257),(9,14668),(9,11257),(9,7334),(9,3411),(8,3943),(8,2570),(8,1393),(8,532),(7,560),(7,273),(7,106),(7,28),(6,28),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(14,7189),(13,20268),(13,19825),(13,18162),(13,13079),(12,30195),(12,28963),(12,25465),(12,17116),(11,32923),(11,30591),(11,25464),(11,15807),(10,25711),(10,22705),(10,17551),(10,9904),(9,13827),(9,11257),(9,7846),(9,3923),(8,4784),(8,3411),(8,2038),(8,861),(7,939),(7,532),(7,245),(7,78),(6,79),(6,28),(6,7),(6,1),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,7280),(13,7189),(13,6746),(13,5083),(12,13432),(12,13079),(12,11847),(12,8349),(11,18006),(11,17116),(11,14784),(11,9657),(10,17304),(10,15807),(10,12801),(10,7647),(9,11570),(9,9904),(9,7334),(9,3923),(8,5100),(8,3923),(8,2550),(8,1177),(7,1344),(7,861),(7,454),(7,167),(6,173),(6,78),(6,27),(6,6),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,2197),(13,2106),(13,1663),(12,5161),(12,5083),(12,4730),(12,3498),(11,8625),(11,8349),(11,7459),(11,5127),(10,10281),(10,9657),(10,8160),(10,5154),(9,8565),(9,7647),(9,5981),(9,3411),(8,4784),(8,3923),(8,2746),(8,1373),(7,1660),(7,1177),(7,694),(7,287),(6,308),(6,167),(6,72),(6,21),(5,21),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,534),(13,443),(12,1675),(12,1663),(12,1585),(12,1232),(11,3564),(11,3498),(11,3222),(11,2332),(10,5338),(10,5127),(10,4503),(10,3006),(9,5576),(9,5154),(9,4236),(9,2570),(8,3943),(8,3411),(8,2550),(8,1373),(7,1780),(7,1373),(7,890),(7,407),(6,458),(6,287),(6,146),(6,51),(5,52),(5,21),(5,6),(5,1),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(13,91),(12,444),(12,443),(12,431),(12,353),(11,1243),(11,1232),(11,1166),(11,890),(10,2387),(10,2332),(10,2121),(10,1497),(9,3163),(9,3006),(9,2584),(9,1666),(8,2843),(8,2570),(8,2038),(8,1177),(7,1660),(7,1373),(7,966),(7,483),(6,578),(6,407),(6,236),(6,95),(5,100),(5,51),(5,20),(5,5),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,91),(12,91),(12,90),(12,78),(11,354),(11,353),(11,342),(11,276),(10,900),(10,890),(10,835),(10,624),(9,1542),(9,1497),(9,1340),(9,918),(8,1779),(8,1666),(8,1393),(8,861),(7,1344),(7,1177),(7,890),(7,483),(6,624),(6,483),(6,312),(6,141),(5,156),(5,95),(5,46),(5,15),(4,15),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,13),(12,13),(12,12),(11,78),(11,78),(11,77),(11,66),(10,277),(10,276),(10,266),(10,211),(9,633),(9,624),(9,579),(9,422),(8,954),(8,918),(8,805),(8,532),(7,939),(7,861),(7,694),(7,407),(6,578),(6,483),(6,342),(6,171),(5,202),(5,141),(5,80),(5,31),(4,32),(4,15),(4,5),(4,1),(3,1),(2,1),(1,1),(0,1)],
  [(12,1),(12,1),(11,12),(11,12),(11,12),(11,11),(10,66),(10,66),(10,65),(10,55),(9,212),(9,211),(9,202),(9,157),(8,430),(8,422),(8,386),(8,273),(7,560),(7,532),(7,454),(7,287),(6,458),(6,407),(6,312),(6,171),(5,220),(5,171),(5,110),(5,49),(4,53),(4,31),(4,14),(4,4),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(11,1),(11,1),(11,1),(11,1),(11,1),(10,11),(10,11),(10,11),(10,10),(9,55),(9,55),(9,54),(9,45),(8,158),(8,157),(8,149),(8,113),(7,280),(7,273),(7,245),(7,167),(6,308),(6,287),(6,236),(6,141),(5,202),(5,171),(5,122),(5,61),(4,71),(4,49),(4,27),(4,10),(3,10),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(10,1),(9,10),(9,10),(9,10),(9,9),(8,45),(8,45),(8,44),(8,36),(7,114),(7,113),(7,106),(7,78),(6,173),(6,167),(6,146),(6,95),(5,156),(5,141),(5,110),(5,61),(4,78),(4,61),(4,39),(4,17),(3,18),(3,10),(3,4),(3,1),(2,1),(1,1),(0,1)],
  [(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(9,1),(8,9),(8,9),(8,9),(8,8),(7,36),(7,36),(7,35),(7,28),(6,79),(6,78),(6,72),(6,51),(5,100),(5,95),(5,80),(5,49),(4,71),(4,61),(4,44),(4,22),(3,25),(3,17),(3,9),(3,3),(2,3),(2,1),(1,1),(0,1)],
  [(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(8,1),(7,8),(7,8),(7,8),(7,7),(6,28),(6,28),(6,27),(6,21),(5,52),(5,51),(5,46),(5,31),(4,53),(4,49),(4,39),(4,22),(3,28),(3,22),(3,14),(3,6),(2,6),(2,3),(2,1),(1,1),(0,1)],
  [(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(7,1),(6,7),(6,7),(6,7),(6,6),(5,21),(5,21),(5,20),(5,15),(4,32),(4,31),(4,27),(4,17),(3,25),(3,22),(3,16),(3,8),(2,9),(2,6),(2,3),(2,1),(1,1),(0,1)],
  [(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(6,1),(5,6),(5,6),(5,6),(5,5),(4,15),(4,15),(4,14),(4,10),(3,18),(3,17),(3,14),(3,8),(2,10),(2,8),(2,5),(2,2),(1,2),(1,1),(0,1)],
  [(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(5,1),(4,5),(4,5),(4,5),(4,4),(3,10),(3,10),(3,9),(3,6),(2,9),(2,8),(2,6),(2,3),(1,3),(1,2),(1,1),(0,1)],
  [(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(4,1),(3,4),(3,4),(3,4),(3,3),(2,6),(2,6),(2,5),(2,3),(1,4),(1,3),(1,2),(1,1),(0,1)],
  [(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(3,1),(2,3),(2,3),(2,3),(2,2),(1,3),(1,3),(1,2),(1,1),(0,1),(0,1)],
  [(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(2,1),(1,2),(1,2),(1,2),(1,1),(0,1),(0,1),(0,1)],
  [(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(1,1),(0,1),(0,1),(0,1),(0,1)],
  [(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1)]
]

private def x5 : List ℕ :=
  [0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2]
private def y5 : List ℕ :=
  [2,1,0,4,3,2,1,0,4,3,2,1,0,4,3,2,1,0,4,3,2,1,0,4,3,2,1,0,4,3,2,1,0,4,3,2,1,0]
private def x4 : List ℕ :=
  [0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1]
private def y4_0 : List ℕ :=
  [0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3]
private def y4_1 : List ℕ :=
  [1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0]
private def y4_2 : List ℕ :=
  [2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1]
private def y4_3 : List ℕ :=
  [3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2,1,0,3,2]

private lemma ok_T5_lit : checkTable [0, 1, 2, 3, 4] y5 x5 T5 = true := rfl
private lemma ok_T4_0_lit : checkTable [0, 1, 2, 3] y4_0 x4 T4_0 = true := rfl
private lemma ok_T4_1_lit : checkTable [0, 1, 2, 3] y4_1 x4 T4_1 = true := rfl
private lemma ok_T4_2_lit : checkTable [0, 1, 2, 3] y4_2 x4 T4_2 = true := rfl
private lemma ok_T4_3_lit : checkTable [0, 1, 2, 3] y4_3 x4 T4_3 = true := rfl

private lemma ok_T5 : checkTable (List.range 5) (descending 5 2 38) (ascending 5 38) T5 = true := by
  have h1 : List.range 5 = [0, 1, 2, 3, 4] := rfl
  have h2 : descending 5 2 38 = y5 := rfl
  have h3 : ascending 5 38 = x5 := rfl
  rw [h1, h2, h3]
  exact ok_T5_lit

private lemma ok_T4_0 : checkTable (List.range 4) (descending 4 0 38) (ascending 4 38) T4_0 = true := by
  have h1 : List.range 4 = [0, 1, 2, 3] := rfl
  have h2 : descending 4 0 38 = y4_0 := rfl
  have h3 : ascending 4 38 = x4 := rfl
  rw [h1, h2, h3]
  exact ok_T4_0_lit

private lemma ok_T4_1 : checkTable (List.range 4) (descending 4 1 38) (ascending 4 38) T4_1 = true := by
  have h1 : List.range 4 = [0, 1, 2, 3] := rfl
  have h2 : descending 4 1 38 = y4_1 := rfl
  have h3 : ascending 4 38 = x4 := rfl
  rw [h1, h2, h3]
  exact ok_T4_1_lit

private lemma ok_T4_2 : checkTable (List.range 4) (descending 4 2 38) (ascending 4 38) T4_2 = true := by
  have h1 : List.range 4 = [0, 1, 2, 3] := rfl
  have h2 : descending 4 2 38 = y4_2 := rfl
  have h3 : ascending 4 38 = x4 := rfl
  rw [h1, h2, h3]
  exact ok_T4_2_lit

private lemma ok_T4_3 : checkTable (List.range 4) (descending 4 3 38) (ascending 4 38) T4_3 = true := by
  have h1 : List.range 4 = [0, 1, 2, 3] := rfl
  have h2 : descending 4 3 38 = y4_3 := rfl
  have h3 : ascending 4 38 = x4 := rfl
  rw [h1, h2, h3]
  exact ok_T4_3_lit

end OMA.S_oeis_a094863.Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a094863.main) := by
  intro h
  obtain ⟨phase, hphase⟩ := h 19 (by omega)
  have hle := hphase (OMA.S_oeis_a094863.ascending 5 38) (OMA.S_oeis_a094863.descending 5 2 38)
    (by simp [OMA.S_oeis_a094863.ascending]) (by simp [OMA.S_oeis_a094863.descending])
  have h5 : OMA.S_oeis_a094863.lcsCount (OMA.S_oeis_a094863.ascending 5 38)
      (OMA.S_oeis_a094863.descending 5 2 38) = 219651640 :=
    OMA.S_oeis_a094863.Disproof.lcsCount_of_checkTable 5 _ _ _
      (OMA.S_oeis_a094863.Disproof.mem_ascending_lt (by omega))
      OMA.S_oeis_a094863.Disproof.ok_T5
  rw [h5] at hle
  fin_cases phase
  · have h4 := OMA.S_oeis_a094863.Disproof.lcsCount_of_checkTable 4 _ _ _
      (OMA.S_oeis_a094863.Disproof.mem_ascending_lt (by omega))
      OMA.S_oeis_a094863.Disproof.ok_T4_0
    change 219651640 ≤ OMA.S_oeis_a094863.lcsCount (OMA.S_oeis_a094863.ascending 4 38)
      (OMA.S_oeis_a094863.descending 4 0 38) at hle
    rw [h4] at hle
    change 219651640 ≤ 128996853 at hle
    omega
  · have h4 := OMA.S_oeis_a094863.Disproof.lcsCount_of_checkTable 4 _ _ _
      (OMA.S_oeis_a094863.Disproof.mem_ascending_lt (by omega))
      OMA.S_oeis_a094863.Disproof.ok_T4_1
    change 219651640 ≤ OMA.S_oeis_a094863.lcsCount (OMA.S_oeis_a094863.ascending 4 38)
      (OMA.S_oeis_a094863.descending 4 1 38) at hle
    rw [h4] at hle
    change 219651640 ≤ 173149662 at hle
    omega
  · have h4 := OMA.S_oeis_a094863.Disproof.lcsCount_of_checkTable 4 _ _ _
      (OMA.S_oeis_a094863.Disproof.mem_ascending_lt (by omega))
      OMA.S_oeis_a094863.Disproof.ok_T4_2
    change 219651640 ≤ OMA.S_oeis_a094863.lcsCount (OMA.S_oeis_a094863.ascending 4 38)
      (OMA.S_oeis_a094863.descending 4 2 38) at hle
    rw [h4] at hle
    change 219651640 ≤ 128996853 at hle
    omega
  · have h4 := OMA.S_oeis_a094863.Disproof.lcsCount_of_checkTable 4 _ _ _
      (OMA.S_oeis_a094863.Disproof.mem_ascending_lt (by omega))
      OMA.S_oeis_a094863.Disproof.ok_T4_3
    change 219651640 ≤ OMA.S_oeis_a094863.lcsCount (OMA.S_oeis_a094863.ascending 4 38)
      (OMA.S_oeis_a094863.descending 4 3 38) at hle
    rw [h4] at hle
    change 219651640 ≤ 219364638 at hle
    omega
