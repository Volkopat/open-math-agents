import OMAStatements.S_opg_a_transversal_achievement_game_on_a_square_grid
import Mathlib

/-!
Optimal transversal play. The opening fills unused rows and columns, and the
endgame forces blocking moves before constructing two simultaneous threats.
-/

namespace TransversalGame

open OMA.S_opg_a_transversal_achievement_game_on_a_square_grid

theorem one_cell_win : firstWins 1 = true := by decide

theorem two_by_two_draw : firstWins 2 = false ∧ firstAvoidsLoss 2 = true := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
theorem three_by_three_draw : firstWins 3 = false ∧ firstAvoidsLoss 3 = true := by decide


theorem one_move_wins {n fuel : ℕ} {first second free : List (Cell n)} {a : Cell n}
    (hFirst : hasTransversal first = false) (hSecond : hasTransversal second = false)
    (ha : a ∈ free) (hWin : hasTransversal (a :: first) = true) :
    forceOutcome false free true first second (fuel + 1) = true := by
  have hFree : free.isEmpty = false := by
    cases free with
    | nil => simp at ha
    | cons _ _ => rfl
  rw [forceOutcome]
  simp only [hFirst, hSecond, hFree, Bool.false_eq_true, if_false, if_true]
  apply List.any_eq_true.mpr
  refine ⟨a, ha, ?_⟩
  simp [forceOutcome.eq_def, hWin]

theorem forced_reply {n fuel : ℕ} {first second free : List (Cell n)} {a : Cell n}
    (hFirst : hasTransversal first = false) (hSecond : hasTransversal second = false)
    (ha : a ∈ free) (hThreat : hasTransversal (a :: first) = true)
    (hNoCounter : ∀ c ∈ free, hasTransversal (c :: second) = false)
    (hDefense : forceOutcome false (free.erase a) true first (a :: second) (fuel + 1) = true) :
    forceOutcome false free false first second (fuel + 1 + 1) = true := by
  have hFree : free.isEmpty = false := by
    cases free with
    | nil => simp at ha
    | cons _ _ => rfl
  rw [forceOutcome]
  simp only [hFirst, hSecond, hFree, Bool.false_eq_true, if_false]
  apply List.all_eq_true.mpr
  intro c hc
  by_cases hca : c = a
  · simpa [hca] using hDefense
  · have hmem : a ∈ free.erase c := (List.mem_erase_of_ne (Ne.symm hca)).mpr ha
    exact one_move_wins hFirst (hNoCounter c hc) hmem hThreat

theorem double_threat {n fuel : ℕ} {first second free : List (Cell n)} {a b : Cell n}
    (hFirst : hasTransversal first = false) (hSecond : hasTransversal second = false)
    (ha : a ∈ free) (hb : b ∈ free) (hAB : a ≠ b)
    (hThreatA : hasTransversal (a :: first) = true)
    (hThreatB : hasTransversal (b :: first) = true)
    (hNoCounter : ∀ c ∈ free, hasTransversal (c :: second) = false) :
    forceOutcome false free false first second (fuel + 1 + 1) = true := by
  apply forced_reply hFirst hSecond ha hThreatA hNoCounter
  exact one_move_wins hFirst (hNoCounter a ha)
    ((List.mem_erase_of_ne hAB.symm).mpr hb) hThreatB


theorem transversal_iff {n : ℕ} (claimed : List (Cell n)) :
    hasTransversal claimed = true ↔
    ∃ p : Equiv.Perm (Fin n), ∀ i, (i, p i) ∈ claimed := by
  simp only [hasTransversal, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · exact And.right
  · rintro ⟨p, hp⟩
    refine ⟨List.all_eq_true.mpr ?_, p, hp⟩
    intro i _
    exact List.any_eq_true.mpr ⟨(i, p i), hp i, by simp⟩

theorem transversal_permute {n : ℕ} (rows cols : Equiv.Perm (Fin n))
    (claimed : List (Cell n)) :
    hasTransversal (claimed.map (Equiv.prodCongr rows cols)) = hasTransversal claimed := by
  apply Bool.eq_iff_iff.mpr
  simp only [transversal_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨rows.trans (p.trans cols.symm), ?_⟩
    intro i
    obtain ⟨b, hb, hpi⟩ := List.mem_map.mp (hp (rows i))
    have h₁ : b.1 = i := rows.injective (congrArg Prod.fst hpi)
    have h₂ : b.2 = cols.symm (p (rows i)) := by
      have h := congrArg Prod.snd hpi
      exact cols.injective (h.trans (cols.apply_symm_apply _).symm)
    have he : b = (i, (rows.trans (p.trans cols.symm)) i) := Prod.ext h₁ h₂
    exact he ▸ hb
  · rintro ⟨p, hp⟩
    refine ⟨rows.symm.trans (p.trans cols), ?_⟩
    intro i
    apply List.mem_map.mpr
    exact ⟨(rows.symm i, p (rows.symm i)), hp (rows.symm i), by simp⟩

theorem transversal_transpose {n : ℕ} (claimed : List (Cell n)) :
    hasTransversal (claimed.map Prod.swap) = hasTransversal claimed := by
  apply Bool.eq_iff_iff.mpr
  simp only [transversal_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.symm, ?_⟩
    intro i
    obtain ⟨b, hb, h⟩ := List.mem_map.mp (hp (p.symm i))
    have h₁ : b.1 = i := by simpa using congrArg Prod.snd h
    have h₂ : b.2 = p.symm i := congrArg Prod.fst h
    have he : b = (i, p.symm i) := Prod.ext h₁ h₂
    exact he ▸ hb
  · rintro ⟨p, hp⟩
    refine ⟨p.symm, ?_⟩
    intro i
    exact List.mem_map.mpr ⟨(p.symm i, p (p.symm i)), hp _, by simp⟩

private theorem erase_map {n : ℕ} (φ : Cell n ≃ Cell n) (a : Cell n)
    (xs : List (Cell n)) : (xs.map φ).erase (φ a) = (xs.erase a).map φ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = a
    · subst x
      simp
    · have h' : φ x ≠ φ a := fun he => h (φ.injective he)
      simp [List.erase_cons_tail, h, h', ih]

theorem forceOutcome_equiv {n : ℕ} (φ : Cell n ≃ Cell n)
    (hφ : ∀ claimed : List (Cell n), hasTransversal (claimed.map φ) = hasTransversal claimed)
    (drawsAcceptable oneTurn : Bool) (free first second : List (Cell n)) (fuel : ℕ) :
    forceOutcome drawsAcceptable (free.map φ) oneTurn (first.map φ) (second.map φ) fuel =
      forceOutcome drawsAcceptable free oneTurn first second fuel := by
  induction fuel generalizing free oneTurn first second with
  | zero =>
    simp [forceOutcome, hφ]
  | succ fuel ih =>
    cases oneTurn <;>
      simp [forceOutcome, hφ, List.any_map, List.all_map, erase_map, ← List.map_cons, ih, Function.comp_def]


theorem missing_columns_prevent_threat {n : ℕ} (claimed : List (Cell n))
    {j k : Fin n} (hjk : j ≠ k)
    (hj : ∀ a ∈ claimed, a.2 ≠ j) (hk : ∀ a ∈ claimed, a.2 ≠ k)
    (newCell : Cell n) :
    hasTransversal (newCell :: claimed) = false := by
  by_contra h
  have hw : hasTransversal (newCell :: claimed) = true := by
    cases hb : hasTransversal (newCell :: claimed) <;> simp_all
  obtain ⟨p, hp⟩ := (transversal_iff _).mp hw
  have hsecond (c : Fin n) (hc : ∀ a ∈ claimed, a.2 ≠ c) : newCell.2 = c := by
    obtain ⟨i, hi⟩ := p.surjective c
    have hmem : (i, c) ∈ newCell :: claimed := hi ▸ hp i
    rcases List.mem_cons.mp hmem with hsame | hprev
    · exact (congrArg Prod.snd hsame).symm
    · exact (hc _ hprev rfl).elim
  exact hjk ((hsecond j hj).symm.trans (hsecond k hk))

theorem fewer_than_rows_prevents_transversal {n : ℕ} (claimed : List (Cell n))
    (hshort : claimed.length < n) : hasTransversal claimed = false := by
  by_contra h
  have hw : hasTransversal claimed = true := by
    cases hb : hasTransversal claimed <;> simp_all
  obtain ⟨p, hp⟩ := (transversal_iff _).mp hw
  have hrows : claimed.toFinset.image Prod.fst = (Finset.univ : Finset (Fin n)) := by
    apply Finset.eq_univ_of_forall
    intro i
    exact Finset.mem_image.mpr ⟨(i, p i), List.mem_toFinset.mpr (hp i), rfl⟩
  have hcard : n ≤ claimed.toFinset.card := by
    simpa [hrows] using
      (Finset.card_image_le (s := claimed.toFinset) (f := Prod.fst))
  exact (not_le_of_gt hshort) (hcard.trans (List.toFinset_card_le claimed))


def OpeningInvariant {n : ℕ} (first second : List (Cell n)) : Prop :=
  (first.map Prod.fst).Nodup ∧ (first.map Prod.snd).Nodup ∧
    (∀ z ∈ second, z.1 ∈ first.map Prod.fst ∨ z.2 ∈ first.map Prod.snd) ∧
    ∃ z ∈ second, z.2 ∉ first.map Prod.snd

theorem opening_extend {n : ℕ} {first second : List (Cell n)}
    (h : OpeningInvariant first second)
    (hr : ∃ r : Fin n, r ∉ first.map Prod.fst)
    (hc : ∀ b : Fin n, ∃ c : Fin n, c ∉ first.map Prod.snd ∧ c ≠ b)
    (reply : Cell n) :
    ∃ move : Cell n, move ∉ first ∧ move ∉ reply :: second ∧
      OpeningInvariant (move :: first) (reply :: second) := by
  obtain ⟨hnr, hnc, hcovered, witness, hwitness, hwcol⟩ := h
  have extend (r c : Fin n) (hrow : r ∉ first.map Prod.fst)
      (hcol : c ∉ first.map Prod.snd)
      (hmove : (r, c) ≠ reply)
      (hcoveredReply : reply.1 = r ∨ reply.1 ∈ first.map Prod.fst ∨
        reply.2 = c ∨ reply.2 ∈ first.map Prod.snd)
      (z : Cell n) (hz : z ∈ reply :: second) (hzcol : z.2 ∉ first.map Prod.snd) (hzc : z.2 ≠ c) :
      ∃ move : Cell n, move ∉ first ∧ move ∉ reply :: second ∧
        OpeningInvariant (move :: first) (reply :: second) := by
    refine ⟨(r,c), ?_, ?_, ?_⟩
    · intro hm
      exact hrow (List.mem_map.mpr ⟨(r,c), hm, rfl⟩)
    · intro hm
      rcases List.mem_cons.mp hm with hs | hs
      · exact hmove hs
      · rcases hcovered (r,c) hs with hh | hh
        · exact hrow hh
        · exact hcol hh
    · refine ⟨List.nodup_cons.mpr ⟨hrow, hnr⟩, List.nodup_cons.mpr ⟨hcol, hnc⟩,
        ?_, z, hz, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simpa [List.map_cons, List.mem_cons, or_assoc] using hcoveredReply
        · rcases hcovered a ha with ha | ha
          · exact Or.inl (List.mem_cons_of_mem _ ha)
          · exact Or.inr (List.mem_cons_of_mem _ ha)
      · simpa using And.intro hzc hzcol
  by_cases ha : reply.1 ∈ first.map Prod.fst
  · obtain ⟨r, hrow⟩ := hr
    obtain ⟨c, hcol, hcw⟩ := hc witness.2
    have hn : (r,c) ≠ reply := by
      intro he
      have he' : r = reply.1 := congrArg Prod.fst he
      exact hrow (by rwa [he'])
    exact extend r c hrow hcol hn
      (Or.inr (Or.inl ha)) witness (List.mem_cons_of_mem _ hwitness) hwcol hcw.symm
  · by_cases hb : reply.2 ∈ first.map Prod.snd
    · obtain ⟨r, hrow⟩ := hr
      obtain ⟨c, hcol, hcw⟩ := hc witness.2
      have hn : (r,c) ≠ reply := by
        intro he
        have he' : c = reply.2 := congrArg Prod.snd he
        exact hcol (by rwa [he'])
      exact extend r c hrow hcol hn
        (Or.inr (Or.inr (Or.inr hb))) witness (List.mem_cons_of_mem _ hwitness) hwcol hcw.symm
    · obtain ⟨c, hcol, hcw⟩ := hc reply.2
      exact extend reply.1 c ha hcol (fun he => hcw (congrArg Prod.snd he))
        (Or.inl rfl) reply (List.mem_cons_self) hb hcw.symm


theorem diagonal_swap_completes {n : ℕ} (marks : List (Cell n)) {a b : Fin n}
    (h₁ : (a,b) ∈ marks) (h₂ : (b,a) ∈ marks)
    (hdiag : ∀ i, i ≠ a → i ≠ b → (i,i) ∈ marks) :
    hasTransversal marks = true := by
  apply (transversal_iff _).mpr
  refine ⟨Equiv.swap a b, ?_⟩
  intro i
  by_cases ha : i = a
  · subst i
    simpa using h₁
  · by_cases hb : i = b
    · subst i
      simpa using h₂
    · simpa [Equiv.swap_apply_of_ne_of_ne ha hb] using hdiag i ha hb

theorem diagonal_cycle_completes {n : ℕ} (marks : List (Cell n)) {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h₁ : (a,b) ∈ marks) (h₂ : (b,c) ∈ marks) (h₃ : (c,a) ∈ marks)
    (hdiag : ∀ i, i ≠ a → i ≠ b → i ≠ c → (i,i) ∈ marks) :
    hasTransversal marks = true := by
  apply (transversal_iff _).mpr
  let p := (Equiv.swap b c).trans (Equiv.swap a b)
  refine ⟨p, ?_⟩
  intro i
  by_cases ha : i = a
  · subst i
    simpa [p, Equiv.swap_apply_def, hab, hac] using h₁
  · by_cases hb : i = b
    · subst i
      simpa [p, Equiv.swap_apply_def, hab.symm, hac.symm, hbc.symm] using h₂
    · by_cases hc : i = c
      · subst i
        simpa [p, Equiv.swap_apply_def, hab.symm, hbc.symm] using h₃
      · simpa [p, Equiv.swap_apply_def, ha, hb, hc] using hdiag i ha hb hc


private theorem absent_column {n : ℕ} {marks : List (Cell n)} {j : Fin n}
    (hj : ∀ a ∈ marks, a.2 ≠ j) : hasTransversal marks = false := by
  by_contra h
  have ht : hasTransversal marks = true := by
    cases hmark : hasTransversal marks <;> simp_all
  obtain ⟨p, hp⟩ := (transversal_iff _).mp ht
  obtain ⟨i, hi⟩ := p.surjective j
  exact hj (i,p i) (hp i) hi

private theorem choose_move {n fuel : ℕ} {first second free : List (Cell n)} {a : Cell n}
    (hSecond : hasTransversal second = false) (ha : a ∈ free)
    (hNext : forceOutcome false (free.erase a) false (a :: first) second fuel = true) :
    forceOutcome false free true first second (fuel + 1) = true := by
  have hFree : free.isEmpty = false := by
    cases free with
    | nil => simp at ha
    | cons _ _ => rfl
  rw [forceOutcome]
  simp only [hSecond, hFree, Bool.false_eq_true, if_false, if_true]
  split
  · rfl
  · exact List.any_eq_true.mpr ⟨a, ha, hNext⟩

private theorem has_mark_or_false (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

/-- Closing strategy when two distinct indices have both incident corner cells free. -/
theorem finish_two_clean_indices {n fuel : ℕ} {first second free : List (Cell n)}
    {b c w j k : Fin n} (hb : b ≠ w) (hc : c ≠ w) (hbc : b ≠ c)
    (hjk : j ≠ k) (hwj : w ≠ j) (hwk : w ≠ k)
    (hj : ∀ a ∈ second, a.2 ≠ j) (hk : ∀ a ∈ second, a.2 ≠ k)
    (hdiag : ∀ i, i ≠ w → (i,i) ∈ first)
    (ha : (w,b) ∈ free) (hd : (b,w) ∈ free) (he : (c,w) ∈ free)
    (hr : (w,c) ∈ free) (hs : (b,c) ∈ free) :
    forceOutcome false free true first second (fuel + 1 + 1 + 1 + 1 + 1) = true := by
  let F₁ := free.erase (w,b)
  let F₂ := F₁.erase (b,w)
  let F₃ := F₂.erase (c,w)
  have hd' : (b,w) ∈ F₁ :=
    (List.mem_erase_of_ne (fun he => hb (congrArg Prod.fst he))).mpr hd
  have he' : (c,w) ∈ F₂ :=
    (List.mem_erase_of_ne (fun he => hbc.symm (congrArg Prod.fst he))).mpr
    ((List.mem_erase_of_ne (fun he => hc (congrArg Prod.fst he))).mpr he)
  have hr' : (w,c) ∈ F₃ :=
    (List.mem_erase_of_ne (fun he => hc.symm (congrArg Prod.fst he))).mpr
    ((List.mem_erase_of_ne (fun he => hb.symm (congrArg Prod.fst he))).mpr
    ((List.mem_erase_of_ne (fun he => hbc.symm (congrArg Prod.snd he))).mpr hr))
  have hs' : (b,c) ∈ F₃ :=
    (List.mem_erase_of_ne (fun he => hbc (congrArg Prod.fst he))).mpr
    ((List.mem_erase_of_ne (fun he => hc (congrArg Prod.snd he))).mpr
    ((List.mem_erase_of_ne (fun he => hb (congrArg Prod.fst he))).mpr hs))
  have hmain : hasTransversal ((b,w) :: (w,b) :: first) = true := by
    apply diagonal_swap_completes (a := b) (b := w) _ (by simp) (by simp)
    intro i _ hi
    simp [hdiag i hi]
  apply choose_move (absent_column hj) ha
  rcases has_mark_or_false (hasTransversal ((w,b) :: first)) with hf | hf
  · rw [forceOutcome]
    simp [hf]
  · apply forced_reply hf (absent_column hj) hd' hmain
    · intro newCell _
      exact missing_columns_prevent_threat second hjk hj hk newCell
    · have hj' : ∀ a ∈ (b,w) :: second, a.2 ≠ j := by
        intro cell hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hwj
        · exact hj _ hmem
      have hk' : ∀ a ∈ (b,w) :: second, a.2 ≠ k := by
        intro cell hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hwk
        · exact hk _ hmem
      apply choose_move (absent_column hj') he'
      rcases has_mark_or_false (hasTransversal ((c,w) :: (w,b) :: first)) with hnew | hnew
      · rw [forceOutcome]
        simp [hnew]
      · apply double_threat hnew (absent_column hj') hr' hs'
        · exact fun h => hb.symm (congrArg Prod.fst h)
        · apply diagonal_swap_completes (a := w) (b := c) _ (by simp) (by simp)
          intro i hi _
          simp [hdiag i hi]
        · apply diagonal_cycle_completes (a := w) (b := b) (c := c) _
            hb.symm hc.symm hbc (by simp) (by simp) (by simp)
          intro i hi _ _
          simp [hdiag i hi]
        · intro newCell _
          exact missing_columns_prevent_threat _ hjk hj' hk' newCell


theorem cover_prevents_threat {n : ℕ} (marks : List (Cell n)) (rows cols : Finset (Fin n))
    (hCover : ∀ a ∈ marks, a.1 ∈ rows ∨ a.2 ∈ cols)
    (hSize : rows.card + cols.card + 1 < n) (newCell : Cell n) :
    hasTransversal (newCell :: marks) = false := by
  by_contra h
  have hWin : hasTransversal (newCell :: marks) = true := by
    cases hmark : hasTransversal (newCell :: marks) <;> simp_all
  obtain ⟨p, hp⟩ := (transversal_iff _).mp hWin
  let cover := insert newCell.1 (rows ∪ cols.image p.symm)
  have hc : cover = (Finset.univ : Finset (Fin n)) := by
    apply Finset.eq_univ_of_forall
    intro i
    rcases List.mem_cons.mp (hp i) with hi | hi
    · exact Finset.mem_insert.mpr (Or.inl (congrArg Prod.fst hi))
    · rcases hCover (i,p i) hi with hr | hc
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hr)
      · have hci : i ∈ cols.image p.symm := Finset.mem_image.mpr ⟨p i, hc, p.symm_apply_apply i⟩
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hci)
  have hbound : cover.card ≤ rows.card + cols.card + 1 := by
    calc
      cover.card ≤ (rows ∪ cols.image p.symm).card + 1 := Finset.card_insert_le _ _
      _ ≤ rows.card + (cols.image p.symm).card + 1 := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ rows.card + cols.card + 1 := by
        have hc := Finset.card_image_le (s := cols) (f := p.symm)
        omega
  rw [hc, Finset.card_univ, Fintype.card_fin] at hbound
  omega

/-- Take a move that forces the prescribed defense before continuing the strategy. -/
private theorem choose_and_force {n fuel : ℕ} {first second free : List (Cell n)}
    {a b : Cell n} (hSecond : hasTransversal second = false)
    (ha : a ∈ free) (hb : b ∈ free.erase a)
    (hThreat : hasTransversal (b :: a :: first) = true)
    (hNoCounter : ∀ c ∈ free.erase a, hasTransversal (c :: second) = false)
    (hNext : forceOutcome false ((free.erase a).erase b) true (a :: first) (b :: second)
      (fuel + 1) = true) :
    forceOutcome false free true first second (fuel + 1 + 1 + 1) = true := by
  apply choose_move hSecond ha
  rcases has_mark_or_false (hasTransversal (a :: first)) with hf | hf
  · rw [forceOutcome]
    simp [hf]
  · exact forced_reply hf hSecond hb hThreat hNoCounter hNext


theorem diagonal_four_cycle {n : ℕ} (marks : List (Cell n)) {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h₁ : (a,b) ∈ marks) (h₂ : (b,c) ∈ marks) (h₃ : (c,d) ∈ marks) (h₄ : (d,a) ∈ marks)
    (hdiag : ∀ i, i ≠ a → i ≠ b → i ≠ c → i ≠ d → (i,i) ∈ marks) :
    hasTransversal marks = true := by
  apply (transversal_iff _).mpr
  let p := ((Equiv.swap b c).trans (Equiv.swap a b)).trans (Equiv.swap a d)
  refine ⟨p, ?_⟩
  intro i
  by_cases ha : i = a
  · subst i
    simpa [p, Equiv.swap_apply_def, hab, hac, hab.symm, hbd] using h₁
  · by_cases hb : i = b
    · subst i
      simpa [p, Equiv.swap_apply_def, hbc.symm, hac.symm, hcd] using h₂
    · by_cases hc : i = c
      · subst i
        simpa [p, Equiv.swap_apply_def, hbc.symm, hab.symm] using h₃
      · by_cases hd : i = d
        · subst i
          simpa [p, Equiv.swap_apply_def, hbd.symm, hcd.symm, had.symm] using h₄
        · simpa [p, Equiv.swap_apply_def, ha, hb, hc, hd] using hdiag i ha hb hc hd

private theorem no_current_win {n : ℕ} {marks : List (Cell n)} {a : Cell n}
    (h : hasTransversal (a :: marks) = false) : hasTransversal marks = false := by
  rcases has_mark_or_false (hasTransversal marks) with hm | hm
  · obtain ⟨p, hp⟩ := (transversal_iff _).mp hm
    have hwin := (transversal_iff (a :: marks)).mpr
      ⟨p, fun i => List.mem_cons_of_mem _ (hp i)⟩
    rw [h] at hwin
    contradiction
  · exact hm

private theorem finish_by_two_threats {n fuel : ℕ} {first second free : List (Cell n)}
    {a b c : Cell n} (ha : a ∈ free) (hb : b ∈ free.erase a) (hc : c ∈ free.erase a) (hbc : b ≠ c)
    (hThreatB : hasTransversal (b :: a :: first) = true)
    (hThreatC : hasTransversal (c :: a :: first) = true)
    (hNoCounter : ∀ r : Cell n, hasTransversal (r :: second) = false) :
    forceOutcome false free true first second (fuel + 1 + 1 + 1) = true := by
  have hsec := no_current_win (hNoCounter a)
  apply choose_move hsec ha
  rcases has_mark_or_false (hasTransversal (a :: first)) with hf | hf
  · rw [forceOutcome]
    simp [hf]
  · exact double_threat hf hsec hb hc hbc hThreatB hThreatC fun r _ => hNoCounter r


theorem finish_one_clean_index {n fuel : ℕ} {first second free : List (Cell n)}
    {u v w t : Fin n}
    (huv : u ≠ v) (huw : u ≠ w) (hut : u ≠ t) (hvw : v ≠ w) (hvt : v ≠ t) (hwt : w ≠ t)
    (hdiag : ∀ i, i ≠ w → (i,i) ∈ first)
    (hNo₀ : ∀ r : Cell n, hasTransversal (r :: second) = false)
    (hNo₁ : ∀ r : Cell n, hasTransversal (r :: (w,u) :: second) = false)
    (hNo₂ : ∀ r : Cell n, hasTransversal (r :: (v,u) :: (w,u) :: second) = false)
    (h₁ : (u,w) ∈ free) (h₂ : (w,u) ∈ free.erase (u,w))
    (h₃ : (w,v) ∈ (free.erase (u,w)).erase (w,u))
    (h₄ : (v,u) ∈ ((free.erase (u,w)).erase (w,u)).erase (w,v))
    (hEnd :
      let remaining := (((free.erase (u,w)).erase (w,u)).erase (w,v)).erase (v,u)
      ((t,u) ∈ remaining ∧ (w,t) ∈ remaining ∧ (v,t) ∈ remaining) ∨
      ((v,t) ∈ remaining ∧ (t,u) ∈ remaining ∧ (t,w) ∈ remaining)) :
    forceOutcome false free true first second (fuel + 1 + 1 + 1 + 1 + 1 + 1 + 1) = true := by
  have ht₁ : hasTransversal ((w,u) :: (u,w) :: first) = true := by
    apply diagonal_swap_completes (a := u) (b := w) _ (by simp) (by simp)
    intro i _ hi
    simp [hdiag i hi]
  have ht₂ : hasTransversal ((v,u) :: (w,v) :: (u,w) :: first) = true := by
    apply diagonal_cycle_completes (a := u) (b := w) (c := v) _
      huw huv hvw.symm (by simp) (by simp) (by simp)
    intro i _ hi _
    simp [hdiag i hi]
  apply choose_and_force (no_current_win (hNo₀ (u,w))) h₁ h₂ ht₁ (fun r _ => hNo₀ r)
  apply choose_and_force (no_current_win (hNo₁ (w,v))) h₃ h₄ ht₂ (fun r _ => hNo₁ r)
  let remaining := (((free.erase (u,w)).erase (w,u)).erase (w,v)).erase (v,u)
  rcases hEnd with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
  · have hb' : (w,t) ∈ remaining.erase (t,u) :=
      (List.mem_erase_of_ne (fun h => hwt (congrArg Prod.fst h))).mpr hb
    have hc' : (v,t) ∈ remaining.erase (t,u) :=
      (List.mem_erase_of_ne (fun h => hvt (congrArg Prod.fst h))).mpr hc
    apply finish_by_two_threats ha hb' hc' (fun h => hvw.symm (congrArg Prod.fst h)) _ _ hNo₂
    · apply diagonal_cycle_completes (a := t) (b := u) (c := w) _
        hut.symm hwt.symm huw (by simp) (by simp) (by simp)
      intro i _ _ hi
      simp [hdiag i hi]
    · apply diagonal_four_cycle (a := t) (b := u) (c := w) (d := v) _
        hut.symm hwt.symm hvt.symm huw huv hvw.symm (by simp) (by simp) (by simp) (by simp)
      intro i _ _ hi _
      simp [hdiag i hi]
  · have hb' : (t,u) ∈ remaining.erase (v,t) :=
      (List.mem_erase_of_ne (fun h => hvt.symm (congrArg Prod.fst h))).mpr hb
    have hc' : (t,w) ∈ remaining.erase (v,t) :=
      (List.mem_erase_of_ne (fun h => hvt.symm (congrArg Prod.fst h))).mpr hc
    apply finish_by_two_threats ha hb' hc' (fun h => huw (congrArg Prod.snd h)) _ _ hNo₂
    · apply diagonal_four_cycle (a := t) (b := u) (c := w) (d := v) _
        hut.symm hwt.symm hvt.symm huw huv hvw.symm (by simp) (by simp) (by simp) (by simp)
      intro i _ _ hi _
      simp [hdiag i hi]
    · apply diagonal_cycle_completes (a := v) (b := t) (c := w) _
        hvt hvw hwt.symm (by simp) (by simp) (by simp)
      intro i _ _ hi
      simp [hdiag i hi]


private def LegalState {n : ℕ} (free first second : List (Cell n)) : Prop :=
  free.Nodup ∧ ∀ a, a ∈ free ↔ a ∉ first ∧ a ∉ second

private theorem erase_removes_mark {n : ℕ} (a : Cell n) (free : List (Cell n))
    (hf : free.Nodup) : a ∉ free.erase a := by
  induction free with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hf
    by_cases h : x = a
    · subst x
      simpa using hx
    · simp [List.erase_cons_tail, h, Ne.symm h, ih hxs]

private theorem erase_legal {n : ℕ} {free : List (Cell n)} (hf : free.Nodup) (a b : Cell n) :
    b ∈ free.erase a ↔ b ∈ free ∧ b ≠ a := by
  by_cases h : b = a
  · subst b
    have hn : a ∉ free.erase a := erase_removes_mark a free hf
    simp [hn]
  · rw [List.mem_erase_of_ne h]
    exact (and_iff_left h).symm

private theorem first_legal {n : ℕ} {free first second : List (Cell n)} {a : Cell n}
    (h : LegalState free first second) : LegalState (free.erase a) (a :: first) second := by
  refine ⟨List.erase_sublist.nodup h.1, ?_⟩
  intro b
  rw [erase_legal h.1 a b, h.2 b]
  simp only [List.mem_cons, not_or]
  tauto

private theorem second_legal {n : ℕ} {free first second : List (Cell n)} {a : Cell n}
    (h : LegalState free first second) : LegalState (free.erase a) first (a :: second) := by
  refine ⟨List.erase_sublist.nodup h.1, ?_⟩
  intro b
  rw [erase_legal h.1 a b, h.2 b]
  simp only [List.mem_cons, not_or]
  tauto

private theorem exists_unused {n : ℕ} (marks : List (Fin n)) (hlen : marks.length < n) :
    ∃ a : Fin n, a ∉ marks := by
  by_contra h
  push Not at h
  have hall : marks.toFinset = (Finset.univ : Finset (Fin n)) :=
    Finset.eq_univ_of_forall fun a => List.mem_toFinset.mpr (h a)
  have hc := List.toFinset_card_le marks
  rw [hall, Finset.card_univ, Fintype.card_fin] at hc
  omega

private theorem exists_unused_other {n : ℕ} (marks : List (Fin n)) (hlen : marks.length+1 < n)
    (b : Fin n) : ∃ a : Fin n, a ∉ marks ∧ a ≠ b := by
  obtain ⟨a, ha⟩ := exists_unused (b :: marks) (by simpa using hlen)
  exact ⟨a, fun hm => ha (List.mem_cons_of_mem _ hm), fun he => ha (he ▸ List.mem_cons_self)⟩

private theorem phase_reply {n : ℕ} {free first second : List (Cell n)} {reply : Cell n}
    (hBoard : LegalState free first second) (hOpen : OpeningInvariant first second)
    (hlen : first.length + 1 < n) (_hReply : reply ∈ free) :
    ∃ move ∈ free.erase reply, OpeningInvariant (move :: first) (reply :: second) := by
  obtain ⟨a, hfirst, hsecond, hNext⟩ :=
    opening_extend hOpen (exists_unused _ (by simp; omega))
      (exists_unused_other _ (by simpa using hlen)) reply
  have hstate : LegalState (free.erase reply) first (reply :: second) := second_legal hBoard
  exact ⟨a, (hstate.2 a).mpr ⟨hfirst, hsecond⟩, hNext⟩


private def cleanIndices {n : ℕ} (second : List (Cell n)) (w : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ≠ w ∧ (i,w) ∉ second ∧ (w,i) ∉ second

private def cornerMarks {n : ℕ} (second : List (Cell n)) (w : Fin n) : Finset (Cell n) :=
  second.toFinset.filter fun a => a.1 = w ∨ a.2 = w

private def cornerIndex {n : ℕ} (w : Fin n) (a : Cell n) : Fin n :=
  if a.2 = w then a.1 else a.2

private theorem blocked_images {n : ℕ} (second : List (Cell n)) {w : Fin n}
    (hw : (w,w) ∈ second) :
    Finset.univ \ cleanIndices second w ⊆ (cornerMarks second w).image (cornerIndex w) := by
  intro i hi
  have hn : i ∉ cleanIndices second w := (Finset.mem_sdiff.mp hi).2
  by_cases h : i = w
  · subst i
    refine Finset.mem_image.mpr ⟨(w,w), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw, Or.inl rfl⟩
    · simp [cornerIndex]
  · have hblocked : (i,w) ∈ second ∨ (w,i) ∈ second := by
      by_contra h'
      have hpair : (i,w) ∉ second ∧ (w,i) ∉ second := not_or.mp h'
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hpair⟩)
    rcases hblocked with hc | hc
    · refine Finset.mem_image.mpr ⟨(i,w), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hc, Or.inr rfl⟩
      · simp [cornerIndex]
    · refine Finset.mem_image.mpr ⟨(w,i), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hc, Or.inl rfl⟩
      · simp [cornerIndex, h]

private theorem corner_count {n : ℕ} (second : List (Cell n)) {w : Fin n}
    (hw : (w,w) ∈ second) :
    n - (cleanIndices second w).card ≤ ((cornerMarks second w).image (cornerIndex w)).card := by
  have h := Finset.card_le_card (blocked_images second hw)
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin] at h
  exact h

private theorem outside_corner_count {n : ℕ} (second : List (Cell n)) {w : Fin n}
    (hw : (w,w) ∈ second) (hlen : second.length + 1 = n) :
    (cleanIndices second w).Nonempty ∧
    (second.toFinset \ cornerMarks second w).card + 1 ≤ (cleanIndices second w).card := by
  have hl := corner_count second hw
  have hu := Finset.card_image_le (s := cornerMarks second w) (f := cornerIndex w)
  have hO := List.toFinset_card_le second
  have hsub : cornerMarks second w ⊆ second.toFinset := Finset.filter_subset _ _
  have hc := Finset.card_le_card hsub
  have hle : (second.toFinset \ cornerMarks second w).card + 1 ≤ (cleanIndices second w).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    omega
  exact ⟨Finset.card_pos.mp (by omega), hle⟩

private theorem both_clean_or_one {n : ℕ} (second : List (Cell n)) {w : Fin n}
    (hw : (w,w) ∈ second) (hlen : second.length + 1 = n) :
    (∃ b c : Fin n, b ∈ cleanIndices second w ∧ c ∈ cleanIndices second w ∧
      b ≠ c ∧ (b,c) ∉ second) ∨
    ((cleanIndices second w).card = 1 ∧ second.toFinset = cornerMarks second w ∧
      Set.InjOn (cornerIndex w) (cornerMarks second w)) := by
  obtain ⟨hpos, hOut⟩ := outside_corner_count second hw hlen
  let S := cleanIndices second w
  change S.Nonempty at hpos
  change (second.toFinset \ cornerMarks second w).card + 1 ≤ S.card at hOut
  by_cases htwo : 2 ≤ S.card
  · left
    by_contra hn
    push Not at hn
    have hm (b c : Fin n) (hb : b ∈ S) (hc : c ∈ S) (hne : b ≠ c) :
        (b,c) ∈ second.toFinset \ cornerMarks second w := by
      have hbm := (Finset.mem_filter.mp hb).2.1
      have hcm := (Finset.mem_filter.mp hc).2.1
      exact Finset.mem_sdiff.mpr
        ⟨List.mem_toFinset.mpr (hn b c hb hc hne), fun ha => (Finset.mem_filter.mp ha).2.elim hbm hcm⟩
    obtain ⟨b, hb⟩ := hpos
    have hcount : (S.erase b).card = S.card-1 := Finset.card_erase_of_mem hb
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < (S.erase b).card by omega)
    have hc' := Finset.mem_erase.mp hc
    let row := (S.erase b).image (fun i => (b,i))
    have hrow : row.card = S.card-1 := by
      rw [show row.card = (S.erase b).card from Finset.card_image_of_injective _
        (fun _ _ he => congrArg Prod.snd he), hcount]
    have hnew : (c,b) ∉ row := by
      intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact hc'.1 (congrArg Prod.fst hi).symm
    have htotal : (insert (c,b) row).card = S.card := by
      rw [Finset.card_insert_of_notMem hnew, hrow]
      omega
    have hsubset : insert (c,b) row ⊆ second.toFinset \ cornerMarks second w := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hm c b hc'.2 hb hc'.1
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        have hp := Finset.mem_erase.mp hi
        exact hm b i hb hp.2 hp.1.symm
    have hc := Finset.card_le_card hsubset
    rw [htotal] at hc
    omega
  · right
    have hone : S.card = 1 := by
      have h := Finset.card_pos.mpr hpos
      omega
    have hout : second.toFinset \ cornerMarks second w = ∅ := by
      apply Finset.card_eq_zero.mp
      omega
    have hEq : second.toFinset = cornerMarks second w := by
      apply Finset.Subset.antisymm _ (Finset.filter_subset _ _)
      intro a ha
      by_contra hn
      have hm : a ∈ second.toFinset \ cornerMarks second w := Finset.mem_sdiff.mpr ⟨ha,hn⟩
      rw [hout] at hm
      simp at hm
    refine ⟨hone, hEq, ?_⟩
    apply Finset.card_image_iff.mp
    have hlow := corner_count second hw
    have hu := Finset.card_image_le (s := cornerMarks second w) (f := cornerIndex w)
    have hc := List.toFinset_card_le second
    rw [hEq] at hc
    change n - S.card ≤ _ at hlow
    omega


private theorem two_empty_columns {n : ℕ} (second : List (Cell n)) {v w : Fin n}
    (hv : v ≠ w) (hvw : (v,w) ∈ second) (hww : (w,w) ∈ second)
    (hlen : second.length + 1 = n) :
    ∃ j k : Fin n, j ≠ k ∧ w ≠ j ∧ w ≠ k ∧
      (∀ a ∈ second, a.2 ≠ j) ∧ (∀ a ∈ second, a.2 ≠ k) := by
  let marks := second.toFinset
  let distinctMarks := marks.erase (v,w)
  let columns := distinctMarks.image Prod.snd
  have hkeep (a : Cell n) (ha : a ∈ second) : a.2 ∈ columns := by
    by_cases he : a = (v,w)
    · subst a
      refine Finset.mem_image.mpr ⟨(w,w), ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => hv.symm (congrArg Prod.fst h),
        List.mem_toFinset.mpr hww⟩
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨he, List.mem_toFinset.mpr ha⟩, rfl⟩
  have hcol : columns.card ≤ distinctMarks.card := Finset.card_image_le
  have hlenMarks : marks.card ≤ second.length := List.toFinset_card_le second
  have hv' : (v,w) ∈ marks := List.mem_toFinset.mpr hvw
  have hpos : 0 < marks.card := Finset.card_pos.mpr ⟨(v,w),hv'⟩
  have hsize : distinctMarks.card = marks.card - 1 := Finset.card_erase_of_mem hv'
  let missing := (Finset.univ : Finset (Fin n)) \ columns
  have hm : missing.card = n-columns.card := by
    simp [missing, Finset.card_sdiff]
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < missing.card by omega)
  have herase : (missing.erase j).card = missing.card - 1 := Finset.card_erase_of_mem hj
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (show 0 < (missing.erase j).card by omega)
  have hk' := Finset.mem_erase.mp hk
  have hJ := (Finset.mem_sdiff.mp hj).2
  have hK := (Finset.mem_sdiff.mp hk'.2).2
  refine ⟨j,k,hk'.1.symm, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hJ (h ▸ hkeep (w,w) hww)
  · intro h
    exact hK (h ▸ hkeep (w,w) hww)
  · intro a ha h
    exact hJ (h ▸ hkeep a ha)
  · intro a ha h
    exact hK (h ▸ hkeep a ha)


private theorem unmarked_available {n : ℕ} {first second free : List (Cell n)}
    (hBoard : LegalState free first second)
    (hOnlyDiagonal : ∀ a ∈ first, a.1 = a.2) {i j : Fin n}
    (hne : i ≠ j) (hO : (i,j) ∉ second) : (i,j) ∈ free := by
  apply (hBoard.2 _).mpr
  exact ⟨fun hm => hne (hOnlyDiagonal _ hm), hO⟩

private theorem diagonal_position_two_clean {n fuel : ℕ} {first second free : List (Cell n)}
    {v w b c : Fin n} (hv : v ≠ w) (hvw : (v,w) ∈ second) (hww : (w,w) ∈ second)
    (hlen : second.length + 1 = n) (hBoard : LegalState free first second)
    (hOnlyDiagonal : ∀ a ∈ first, a.1 = a.2)
    (hdiag : ∀ i, i ≠ w → (i,i) ∈ first)
    (hb : b ∈ cleanIndices second w) (hc : c ∈ cleanIndices second w)
    (hbc : b ≠ c) (hFreeBC : (b,c) ∉ second) :
    forceOutcome false free true first second (fuel + 1 + 1 + 1 + 1 + 1) = true := by
  obtain ⟨j,k,hjk,hwj,hwk,hj,hk⟩ := two_empty_columns second hv hvw hww hlen
  obtain ⟨hbNe,hbN,hbS⟩ := (Finset.mem_filter.mp hb).2
  obtain ⟨hcNe,hcN,hcS⟩ := (Finset.mem_filter.mp hc).2
  have hAvail {i j : Fin n} (hne : i ≠ j) (hO : (i,j) ∉ second) : (i,j) ∈ free :=
    unmarked_available hBoard hOnlyDiagonal hne hO
  exact finish_two_clean_indices hbNe hcNe hbc hjk hwj hwk hj hk hdiag
    (hAvail hbNe.symm hbS) (hAvail hbNe hbN) (hAvail hcNe hcN) (hAvail hcNe.symm hcS)
    (hAvail hbc hFreeBC)

private theorem corner_transpose_absent {n : ℕ} {second : List (Cell n)} {w i : Fin n}
    (hInj : Set.InjOn (cornerIndex w) (cornerMarks second w)) (hne : i ≠ w)
    (hi : (i,w) ∈ second) : (w,i) ∉ second := by
  intro h
  have hh : (w,i) = (i,w) :=
    hInj (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr h, Or.inl rfl⟩)
      (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi, Or.inr rfl⟩)
      (by simp [cornerIndex, hne])
  exact hne (congrArg Prod.snd hh)

private theorem every_four {n : ℕ} {u v w t : Fin n} (hn : n = 4)
    (huv : u ≠ v) (huw : u ≠ w) (hut : u ≠ t)
    (hvw : v ≠ w) (hvt : v ≠ t) (hwt : w ≠ t) (i : Fin n) :
    i = u ∨ i = v ∨ i = w ∨ i = t := by
  let four : Finset (Fin n) := {u,v,w,t}
  have hcard : four.card = 4 := by
    unfold four
    rw [Finset.card_insert_of_notMem (by simp [huv,huw,hut]),
      Finset.card_insert_of_notMem (by simp [hvw,hvt]),
      Finset.card_insert_of_notMem (by simp [hwt]), Finset.card_singleton]
  have hAll : four = Finset.univ := Finset.eq_univ_of_card four (by simpa [hn] using hcard)
  have hi : i ∈ four := hAll.symm ▸ Finset.mem_univ i
  simpa [four] using hi


private theorem diagonal_position_one_clean {n fuel : ℕ} {first second free : List (Cell n)}
    {u v w : Fin n} (hn : 4 ≤ n) (hvw : v ≠ w) (hv : (v,w) ∈ second)
    (hBoard : LegalState free first second)
    (hOnlyDiagonal : ∀ a ∈ first, a.1 = a.2)
    (hdiag : ∀ i, i ≠ w → (i,i) ∈ first)
    (hClean : cleanIndices second w = {u})
    (hCorners : second.toFinset = cornerMarks second w)
    (hInj : Set.InjOn (cornerIndex w) (cornerMarks second w)) :
    forceOutcome false free true first second (fuel+1+1+1+1+1+1+1) = true := by
  have hu : u ∈ cleanIndices second w := by simp [hClean]
  obtain ⟨huw,huN,huS⟩ := (Finset.mem_filter.mp hu).2
  have huv : u ≠ v := fun he => huN (he.symm ▸ hv)
  have hvS : (w,v) ∉ second := corner_transpose_absent hInj hvw hv
  obtain ⟨t,ht⟩ := exists_unused [u,v,w] (by simp; omega)
  have hts : t ≠ u ∧ t ≠ v ∧ t ≠ w := by simpa using ht
  obtain ⟨htu,htv,htw⟩ := hts
  have hCorner (a : Cell n) (ha : a ∈ second) : a.1 = w ∨ a.2 = w := by
    have hm : a ∈ second.toFinset := List.mem_toFinset.mpr ha
    rw [hCorners] at hm
    exact (Finset.mem_filter.mp hm).2
  have hNo₀ (r : Cell n) : hasTransversal (r :: second) = false := by
    apply cover_prevents_threat second {w} {w} _ _ r
    · intro a ha
      simpa using hCorner a ha
    · simp
      omega
  have hNo₁ (r : Cell n) : hasTransversal (r :: (w,u) :: second) = false := by
    apply cover_prevents_threat ((w,u) :: second) {w} {w} _ _ r
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl (Finset.mem_singleton_self w)
      · simpa using hCorner a ha
    · simp
      omega
  have hNo₂ (hCase : (t,w) ∈ second ∨ (w,t) ∈ second) (r : Cell n) :
      hasTransversal (r :: (v,u) :: (w,u) :: second) = false := by
    by_cases hbig : 5 ≤ n
    · apply cover_prevents_threat ((v,u) :: (w,u) :: second) {w} {w,u} _ _ r
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact Or.inr (by simp)
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact Or.inl (by simp)
          · rcases hCorner a ha with h | h
            · exact Or.inl (by simp [h])
            · exact Or.inr (by simp [h])
      · simp [Finset.card_insert_of_notMem, huw.symm]
        omega
    · have hn₄ : n = 4 := by omega
      rcases hCase with hCol | hRow
      · have htS := corner_transpose_absent hInj htw hCol
        apply cover_prevents_threat ((v,u) :: (w,u) :: second) ∅ {w,u} _ _ r
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact Or.inr (by simp)
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact Or.inr (by simp)
            · right
              rcases a with ⟨i,j⟩
              have hs := hCorner (i,j) ha
              change i = w ∨ j = w at hs
              rcases hs with hi | hj
              · subst i
                rcases every_four hn₄ huv huw htu.symm hvw htv.symm htw.symm j with hj | hj | hj | hj
                · rw [hj] at ha
                  exact (huS ha).elim
                · rw [hj] at ha
                  exact (hvS ha).elim
                · exact Finset.mem_insert.mpr (Or.inl hj)
                · rw [hj] at ha
                  exact (htS ha).elim
              · exact Finset.mem_insert.mpr (Or.inl hj)
        · simp [Finset.card_insert_of_notMem, huw.symm, hn₄]
      · have htN : (t,w) ∉ second := fun h => corner_transpose_absent hInj htw h hRow
        apply cover_prevents_threat ((v,u) :: (w,u) :: second) {w,v} ∅ _ _ r
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact Or.inl (by simp)
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact Or.inl (by simp)
            · left
              rcases a with ⟨i,j⟩
              have hs := hCorner (i,j) ha
              change i = w ∨ j = w at hs
              rcases hs with hi | hj
              · exact Finset.mem_insert.mpr (Or.inl hi)
              · subst j
                rcases every_four hn₄ huv huw htu.symm hvw htv.symm htw.symm i with hi | hi | hi | hi
                · rw [hi] at ha
                  exact (huN ha).elim
                · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hi))
                · exact Finset.mem_insert.mpr (Or.inl hi)
                · rw [hi] at ha
                  exact (htN ha).elim
        · simp [Finset.card_insert_of_notMem, hvw.symm, hn₄]
  have htCase : (t,w) ∈ second ∨ (w,t) ∈ second := by
    by_contra h
    have hp := not_or.mp h
    have hmem : t ∈ cleanIndices second w :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,htw,hp⟩
    exact htu (by simpa [hClean] using hmem)
  have hNoOutside {i j : Fin n} (hi : i ≠ w) (hj : j ≠ w) : (i,j) ∉ second :=
    fun h => (hCorner (i,j) h).elim hi hj
  have hAvail {i j : Fin n} (hne : i ≠ j) (hO : (i,j) ∉ second) : (i,j) ∈ free :=
    unmarked_available hBoard hOnlyDiagonal hne hO
  have hA := hAvail huw huN
  have hB : (w,u) ∈ free.erase (u,w) :=
    (List.mem_erase_of_ne (fun h => huw.symm (congrArg Prod.fst h))).mpr (hAvail huw.symm huS)
  have hC : (w,v) ∈ (free.erase (u,w)).erase (w,u) :=
    (List.mem_erase_of_ne (fun h => huv.symm (congrArg Prod.snd h))).mpr
    ((List.mem_erase_of_ne (fun h => huw.symm (congrArg Prod.fst h))).mpr (hAvail hvw.symm hvS))
  have hD : (v,u) ∈ ((free.erase (u,w)).erase (w,u)).erase (w,v) :=
    (List.mem_erase_of_ne (fun h => hvw (congrArg Prod.fst h))).mpr
    ((List.mem_erase_of_ne (fun h => hvw (congrArg Prod.fst h))).mpr
    ((List.mem_erase_of_ne (fun h => huv.symm (congrArg Prod.fst h))).mpr
      (hAvail huv.symm (hNoOutside hvw huw))))
  refine finish_one_clean_index huv huw htu.symm hvw htv.symm htw.symm
    hdiag hNo₀ hNo₁ (hNo₂ htCase) hA hB hC hD ?_
  let remaining := (((free.erase (u,w)).erase (w,u)).erase (w,v)).erase (v,u)
  have keep {a : Cell n} (ha : a ∈ free) (he₁ : a ≠ (u,w)) (he₂ : a ≠ (w,u))
      (he₃ : a ≠ (w,v)) (he₄ : a ≠ (v,u)) : a ∈ remaining :=
    (List.mem_erase_of_ne he₄).mpr ((List.mem_erase_of_ne he₃).mpr
    ((List.mem_erase_of_ne he₂).mpr ((List.mem_erase_of_ne he₁).mpr ha)))
  rcases htCase with hCol | hRow
  · have htS := corner_transpose_absent hInj htw hCol
    left
    refine ⟨keep (hAvail htu (hNoOutside htw huw)) ?_ ?_ ?_ ?_,
      keep (hAvail htw.symm htS) ?_ ?_ ?_ ?_,
      keep (hAvail htv.symm (hNoOutside hvw htw)) ?_ ?_ ?_ ?_⟩ <;>
      simp [Prod.mk.injEq,htu,htv,htw,huw,hvw,huv]
  · have htN : (t,w) ∉ second := fun h => corner_transpose_absent hInj htw h hRow
    right
    refine ⟨keep (hAvail htv.symm (hNoOutside hvw htw)) ?_ ?_ ?_ ?_,
      keep (hAvail htu (hNoOutside htw huw)) ?_ ?_ ?_ ?_,
      keep (hAvail htw htN) ?_ ?_ ?_ ?_⟩ <;>
      simp [Prod.mk.injEq,htu,htv,htw,huw,hvw,huv]


private theorem mem_mapped_cell {n : ℕ} (φ : Cell n ≃ Cell n) (a : Cell n)
    (xs : List (Cell n)) : a ∈ xs.map φ ↔ φ.symm a ∈ xs := by
  constructor
  · rintro h
    obtain ⟨b,hb,he⟩ := List.mem_map.mp h
    have h := φ.injective (he.trans (φ.apply_symm_apply a).symm)
    exact h ▸ hb
  · intro h
    exact List.mem_map.mpr ⟨φ.symm a,h,φ.apply_symm_apply a⟩

private theorem mapped_state_legal {n : ℕ} (φ : Cell n ≃ Cell n)
    {free first second : List (Cell n)} (h : LegalState free first second) :
    LegalState (free.map φ) (first.map φ) (second.map φ) := by
  have hm : (free.map φ).Nodup := by
    have hn := h.1
    clear h
    induction free with
    | nil => simp
    | cons a free ih =>
      obtain ⟨ha,ht⟩ := List.nodup_cons.mp hn
      simp only [List.map_cons,List.nodup_cons]
      refine ⟨fun hm => ha ?_, ih ht⟩
      simpa using (mem_mapped_cell φ (φ a) free).mp hm
  exact ⟨hm, fun a => by simp only [mem_mapped_cell, h.2]⟩

private theorem grid_rows_nodup (n : ℕ) (rows : List (Fin n)) (hrows : rows.Nodup) :
    (rows.flatMap fun i => (List.finRange n).map fun j => (i,j)).Nodup := by
  induction rows with
  | nil => simp
  | cons i rows ih =>
    obtain ⟨hi,ht⟩ := List.nodup_cons.mp hrows
    rw [List.flatMap_cons, List.nodup_append]
    have hiRow : ((List.finRange n).map fun j => (i,j)).Nodup := by
      apply List.Nodup.map
      · intro a b he
        exact congrArg Prod.snd he
      · exact List.nodup_finRange n
    refine ⟨hiRow,ih ht,?_⟩
    intro a ha b hrest heq
    subst b
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨i',hi',h⟩ := List.mem_flatMap.mp hrest
    obtain ⟨j',_,he⟩ := List.mem_map.mp h
    have he' : i'= i := congrArg Prod.fst he
    exact hi (he' ▸ hi')

private theorem initial_legal (n : ℕ) : LegalState (emptyCells n) [] [] := by
  refine ⟨grid_rows_nodup n _ (List.nodup_finRange n), fun a => ?_⟩
  have ha : a ∈ emptyCells n := by
    apply List.mem_flatMap.mpr
    exact ⟨a.1,by simp, List.mem_map.mpr ⟨a.2,by simp,rfl⟩⟩
  simp [ha]


private theorem board_has_room {n : ℕ} {first second free : List (Cell n)}
    (hBoard : LegalState free first second) (hOpen : OpeningInvariant first second)
    (hlen : first.length < n) : free.isEmpty = false := by
  obtain ⟨r,hr⟩ := exists_unused (first.map Prod.fst) (by simpa using hlen)
  obtain ⟨c,hc⟩ := exists_unused (first.map Prod.snd) (by simpa using hlen)
  have hm : (r,c) ∈ free := (hBoard.2 _).mpr ⟨?_, ?_⟩
  · cases free with
    | nil => simp at hm
    | cons _ _ => rfl
  · intro h
    exact hr (List.mem_map.mpr ⟨(r,c),h,rfl⟩)
  · intro h
    exact (hOpen.2.2.1 _ h).elim hr hc

private theorem fill_to_two_left {n fuel : ℕ}
    (finish : ∀ (first second free : List (Cell n)),
      first.length + 2 = n → first.length = second.length + 1 →
      LegalState free first second → OpeningInvariant first second →
      forceOutcome false free false first second fuel = true) :
    ∀ (k : ℕ) (first second free : List (Cell n)),
      first.length + k + 2 = n → first.length = second.length + 1 →
      LegalState free first second → OpeningInvariant first second →
      forceOutcome false free false first second (fuel + 2*k) = true := by
  intro k
  induction k with
  | zero =>
    intro first second free hlen hdiff hlegal hinv
    exact finish first second free (by simpa using hlen) hdiff hlegal hinv
  | succ k ih =>
    intro first second free hlen hdiff hlegal hinv
    rw [show fuel+2*(k+1) = fuel+2*k+1+1 by omega, forceOutcome]
    rcases has_mark_or_false (hasTransversal first) with hFirst | hFirst
    · simp [hFirst]
    · have hSecond := fewer_than_rows_prevents_transversal second (by omega : second.length < n)
      have hFree := board_has_room hlegal hinv (by omega)
      simp only [hFirst,hSecond,hFree,Bool.false_eq_true,if_false]
      apply List.all_eq_true.mpr
      intro reply hReply
      obtain ⟨move,hMove,hInv⟩ := phase_reply hlegal hinv (by omega) hReply
      have hl' : (reply :: second).length < n := by simp; omega
      apply choose_move (fewer_than_rows_prevents_transversal _ hl') hMove
      exact ih (move :: first) (reply :: second) _ (by simp; omega)
        (by simp; omega) (first_legal (second_legal hlegal)) hInv

private theorem initial_extend_column {n : ℕ} {o : Fin n} {reply : Cell n}
    (hn : 3 ≤ n) (hReply : reply.2 ≠ o) :
    ∃ move : Cell n, move ≠ (o,o) ∧ move ≠ reply ∧
      OpeningInvariant [move,(o,o)] [reply] := by
  obtain ⟨c,hc⟩ := exists_unused [o,reply.2] (by simp; omega)
  have hcs : c ≠ o ∧ c ≠ reply.2 := by simpa using hc
  obtain ⟨ar,har⟩ := exists_unused [o] (by simp; omega)
  have h_ar : ar ≠ o := by simpa using har
  let r := if reply.1 = o then ar else reply.1
  have hr : r ≠ o := by
    by_cases h : reply.1 = o <;> simp [r,h,h_ar]
  have hre : reply.1 = r ∨ reply.1 = o := by
    by_cases h : reply.1 = o <;> simp [r,h]
  refine ⟨(r,c), fun he => hr (congrArg Prod.fst he),
    fun he => hcs.2 (congrArg Prod.snd he), ?_⟩
  refine ⟨by simp [hr], by simp [hcs.1], ?_, reply, by simp, ?_⟩
  · intro a ha
    have h : a = reply := by simpa using ha
    subst a
    left
    simpa using hre
  · simp [hcs.2.symm, hReply]


private theorem start_after_column_reply {n fuel : ℕ} (hn : 4 ≤ n)
    {o : Fin n} {reply : Cell n} {free : List (Cell n)}
    (hReply : reply.2 ≠ o) (hBoard : LegalState free [(o,o)] [reply])
    (finish : ∀ (first second free : List (Cell n)),
      first.length + 2 = n → first.length = second.length + 1 →
      LegalState free first second → OpeningInvariant first second →
      forceOutcome false free false first second fuel = true) :
    forceOutcome false free true [(o,o)] [reply] (fuel+2*(n-4)+1) = true := by
  obtain ⟨move,ha,hb,hInv⟩ := initial_extend_column (by omega) hReply
  have hMove : move ∈ free := (hBoard.2 _).mpr (by simp [ha,hb])
  have hSecond : hasTransversal [reply] = false :=
    fewer_than_rows_prevents_transversal _ (by simp; omega)
  apply choose_move hSecond hMove
  exact fill_to_two_left finish (n-4) _ _ _ (by simp; omega) (by simp)
    (first_legal hBoard) hInv

private theorem reach_opening_end {n fuel : ℕ} (hn : 4 ≤ n)
    (finish : ∀ (first second free : List (Cell n)),
      first.length + 2 = n → first.length = second.length + 1 →
      LegalState free first second → OpeningInvariant first second →
      forceOutcome false free false first second fuel = true) :
    forceOutcome false (emptyCells n) true [] [] (fuel+2*(n-4)+1+1+1) = true := by
  let o : Fin n := ⟨0,by omega⟩
  let F₁ := (emptyCells n).erase (o,o)
  have hBoard := initial_legal n
  have hFirst : (o,o) ∈ emptyCells n := (hBoard.2 _).mpr (by simp)
  have hb₁ : LegalState F₁ [(o,o)] [] := first_legal hBoard
  have hNoEmpty : hasTransversal ([] : List (Cell n)) = false :=
    fewer_than_rows_prevents_transversal _ (by simp; omega)
  apply choose_move hNoEmpty hFirst
  have hf₁ : hasTransversal [(o,o)] = false :=
    fewer_than_rows_prevents_transversal _ (by simp; omega)
  obtain ⟨i,hi⟩ := exists_unused [o] (by simp; omega)
  have hNonEmpty : F₁.isEmpty = false := by
    have hAvail : (i,o) ∈ F₁ := (hb₁.2 _).mpr (by simpa using hi)
    exact List.isEmpty_eq_false_iff.mpr (fun he => by simp [he] at hAvail)
  change forceOutcome false F₁ false [(o,o)] [] (fuel+2*(n-4)+1+1) = true
  rw [forceOutcome]
  simp only [hf₁,hNoEmpty,hNonEmpty,Bool.false_eq_true,if_false]
  apply List.all_eq_true.mpr
  intro reply hmem
  have hNe : reply ≠ (o,o) := by simpa using ((hb₁.2 reply).mp hmem).1
  have hb₂ : LegalState (F₁.erase reply) [(o,o)] [reply] := second_legal hb₁
  by_cases hCol : reply.2 = o
  · have hRow : reply.1 ≠ o := fun h => hNe (Prod.ext h hCol)
    let φ : Cell n ≃ Cell n := Equiv.prodComm _ _
    have hφ : ∀ L : List (Cell n), hasTransversal (L.map φ) = hasTransversal L :=
      transversal_transpose
    have hAfter : LegalState ((F₁.erase reply).map φ) [(o,o)] [(reply.2,reply.1)] := by
      simpa [φ,Prod.swap] using mapped_state_legal φ hb₂
    have hPlay := start_after_column_reply hn (o := o) (reply := (reply.2,reply.1))
      hRow hAfter finish
    exact (forceOutcome_equiv φ hφ false true _ _ _ _).symm.trans (by simpa [φ,Prod.swap] using hPlay)
  · exact start_after_column_reply hn hCol hb₂ finish


private theorem terminal_diagonal_win {n fuel : ℕ} {first second free : List (Cell n)}
    {v w : Fin n} (hn : 4 ≤ n) (hv : v ≠ w) (hvw : (v,w) ∈ second)
    (hww : (w,w) ∈ second) (hCount : second.length + 1 = n)
    (hBoard : LegalState free first second)
    (hOnlyDiagonal : ∀ a ∈ first, a.1 = a.2)
    (hdiag : ∀ i, i ≠ w → (i,i) ∈ first) :
    forceOutcome false free true first second (fuel+7) = true := by
  rcases both_clean_or_one second hww hCount with hTwo | hOne
  · obtain ⟨b,c,hb,hc,hbc,hFree⟩ := hTwo
    exact diagonal_position_two_clean (fuel := fuel+2) hv hvw hww hCount hBoard hOnlyDiagonal
      hdiag hb hc hbc hFree
  · obtain ⟨hone,hCorners,hInj⟩ := hOne
    obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hone
    exact diagonal_position_one_clean hn hv hvw hBoard hOnlyDiagonal hdiag hu hCorners hInj

private theorem bridge_normalized {n fuel : ℕ} {first second free : List (Cell n)}
    {u w v : Fin n} (hn : 4 ≤ n) (huw : u ≠ w) (hvu : v ≠ u) (hvw : v ≠ w)
    (hCountF : first.length + 2 = n) (hCountS : second.length + 3 = n)
    (hBoard : LegalState free first second) (hV : (v,u) ∈ second)
    (hMarks : ∀ a ∈ first, a.1 = a.2 ∧ a.1 ≠ u ∧ a.1 ≠ w)
    (hDiag : ∀ i, i ≠ u → i ≠ w → (i,i) ∈ first)
    (hNoTail : ∀ i j : Fin n, (i=u ∨ i=w) → (j=u ∨ j=w) → (i,j) ∉ second) :
    forceOutcome false free false first second (fuel+10) = true := by
  have hNoFirst (i j : Fin n) (hi : i=u ∨ i=w) : (i,j) ∉ first := by
    intro hm
    rcases hi with rfl | rfl
    · exact (hMarks _ hm).2.1 rfl
    · exact (hMarks _ hm).2.2 rfl
  have hRoom : free.isEmpty = false := by
    have hm : (u,u) ∈ free := (hBoard.2 _).mpr
      ⟨hNoFirst _ _ (Or.inl rfl),hNoTail _ _ (Or.inl rfl) (Or.inl rfl)⟩
    cases free with
    | nil => simp at hm
    | cons _ _ => rfl
  have hBeforeF := fewer_than_rows_prevents_transversal first (by omega : first.length < n)
  have hBeforeS := fewer_than_rows_prevents_transversal second (by omega : second.length < n)
  change forceOutcome false free false first second (fuel+9+1) = true
  rw [forceOutcome]
  simp only [hBeforeF,hBeforeS,hRoom,Bool.false_eq_true,if_false]
  apply List.all_eq_true.mpr
  intro reply _
  let F := free.erase reply
  have hNext : LegalState F first (reply :: second) := second_legal hBoard
  have hNo (a : Cell n) : hasTransversal (a :: reply :: second) = false :=
    fewer_than_rows_prevents_transversal _ (by simp; omega)
  have hCount (a : Cell n) : (a :: reply :: second).length + 1 = n := by simp; omega
  have hAvail (i j : Fin n) (hi : i=u ∨ i=w) (hj : j=u ∨ j=w)
      (hne : (i,j) ≠ reply) : (i,j) ∈ F := by
    apply (hNext.2 _).mpr
    exact ⟨hNoFirst i j hi, fun h => (List.mem_cons.mp h).elim hne (hNoTail i j hi hj)⟩
  by_cases hReply : reply = (w,u) ∨ reply = (u,w)
  · have hA : (w,w) ≠ reply := by
      rcases hReply with rfl | rfl
      · exact fun h => huw.symm (congrArg Prod.snd h)
      · exact fun h => huw.symm (congrArg Prod.fst h)
    have hB : (u,u) ≠ reply := by
      rcases hReply with rfl | rfl
      · exact fun h => huw (congrArg Prod.fst h)
      · exact fun h => huw (congrArg Prod.snd h)
    have ha := hAvail w w (Or.inr rfl) (Or.inr rfl) hA
    have hb : (u,u) ∈ F.erase (w,w) :=
      (List.mem_erase_of_ne (fun he => huw (congrArg Prod.fst he))).mpr
        (hAvail u u (Or.inl rfl) (Or.inl rfl) hB)
    have ht : hasTransversal ((u,u) :: (w,w) :: first) = true := by
      apply (transversal_iff _).mpr
      refine ⟨Equiv.refl _, ?_⟩
      intro i
      by_cases hu : i = u
      · subst i; simp
      · by_cases hw : i = w
        · subst i; simp
        · simp [hDiag i hu hw]
    apply choose_and_force (no_current_win (hNo (w,w))) ha hb ht (fun a _ => hNo a)
    have hAfter : LegalState ((F.erase (w,w)).erase (u,u)) ((w,w) :: first)
        ((u,u) :: reply :: second) :=
      second_legal (first_legal hNext)
    refine terminal_diagonal_win hn hvu (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hV))
      (by simp) (hCount _) hAfter ?_ ?_
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · rfl
      · exact (hMarks _ ha).1
    · intro i hi
      by_cases h : i = w
      · subst i; simp
      · simp [hDiag i hi h]
  · have hA : (u,w) ≠ reply := fun h => hReply (Or.inr h.symm)
    have hB : (w,u) ≠ reply := fun h => hReply (Or.inl h.symm)
    have ha := hAvail u w (Or.inl rfl) (Or.inr rfl) hA
    have hb : (w,u) ∈ F.erase (u,w) :=
      (List.mem_erase_of_ne (fun he => huw.symm (congrArg Prod.fst he))).mpr
        (hAvail w u (Or.inr rfl) (Or.inl rfl) hB)
    have ht : hasTransversal ((w,u) :: (u,w) :: first) = true := by
      apply diagonal_swap_completes _ (a := u) (b := w) (by simp) (by simp)
      intro i hu hw
      simp [hDiag i hu hw]
    apply choose_and_force (no_current_win (hNo (u,w))) ha hb ht (fun a _ => hNo a)
    let φ := Equiv.prodCongr (Equiv.refl (Fin n)) (Equiv.swap u w)
    let endFree := (F.erase (u,w)).erase (w,u)
    let endFirst := (u,w) :: first
    let endSecond := (w,u) :: reply :: second
    have hAfter : LegalState endFree endFirst endSecond := second_legal (first_legal hNext)
    have hφ := transversal_permute (Equiv.refl (Fin n)) (Equiv.swap u w)
    have hOnly (a : Cell n) (ha : a ∈ endFirst.map φ) : a.1 = a.2 := by
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      rcases List.mem_cons.mp hb with rfl | hb
      · simp [φ]
      · obtain ⟨he,hu,hw⟩ := hMarks _ hb
        have hs : (Equiv.swap u w) b.2 = b.2 :=
          Equiv.swap_apply_of_ne_of_ne (he ▸ hu) (he ▸ hw)
        simpa [φ,hs] using he
    have hDiag' (i : Fin n) (hi : i ≠ w) : (i,i) ∈ endFirst.map φ := by
      by_cases hu : i = u
      · subst i
        exact List.mem_map.mpr ⟨(u,w),by simp [endFirst],by simp [φ]⟩
      · exact List.mem_map.mpr ⟨(i,i),by simp [endFirst,hDiag i hu hi],
          by simp [φ,Equiv.swap_apply_of_ne_of_ne hu hi]⟩
    have hV' : (v,w) ∈ endSecond.map φ :=
      List.mem_map.mpr ⟨(v,u),by simp [endSecond,hV],by simp [φ]⟩
    have hW' : (w,w) ∈ endSecond.map φ :=
      List.mem_map.mpr ⟨(w,u),by simp [endSecond],by simp [φ]⟩
    have hCount' : (endSecond.map φ).length + 1 = n := by simpa [endSecond] using hCount (w,u)
    exact (forceOutcome_equiv φ hφ false true endFree endFirst endSecond (fuel+7)).symm.trans
      (terminal_diagonal_win hn hvw hV' hW' hCount' (mapped_state_legal φ hAfter) hOnly hDiag')


private def completeListing {n : ℕ} (xs : List (Fin n)) : List (Fin n) :=
  xs ++ (List.finRange n).filter (fun x => x ∉ xs)

private theorem completeListing_contains {n : ℕ} (xs : List (Fin n)) (a : Fin n) :
    a ∈ completeListing xs := by
  apply List.mem_append.mpr
  by_cases h : a ∈ xs
  · exact Or.inl h
  · exact Or.inr (List.mem_filter.mpr ⟨by simp,by simpa using h⟩)

private theorem completeListing_nodup {n : ℕ} {xs : List (Fin n)} (h : xs.Nodup) :
    (completeListing xs).Nodup := by
  unfold completeListing
  apply List.nodup_append.mpr
  refine ⟨h, (List.nodup_finRange n).filter _, ?_⟩
  intro a ha b hb he
  have hn : b ∉ xs := by simpa using (List.mem_filter.mp hb).2
  exact hn (he ▸ ha)

private theorem completeListing_length {n : ℕ} {xs : List (Fin n)} (h : xs.Nodup) :
    (completeListing xs).length = n := by
  have hu : (completeListing xs).toFinset = (Finset.univ : Finset (Fin n)) :=
    Finset.eq_univ_of_forall fun a => List.mem_toFinset.mpr (completeListing_contains xs a)
  rw [← List.toFinset_card_of_nodup (completeListing_nodup h), hu, Finset.card_univ, Fintype.card_fin]

private def positionInListing {n : ℕ} (xs : List (Fin n)) (h : xs.Nodup) (a : Fin n) : Fin n :=
  ⟨(completeListing xs).idxOf a,
    (List.idxOf_lt_length_iff.mpr (completeListing_contains xs a)).trans_le (completeListing_length h).le⟩

private noncomputable def markingLabels {n : ℕ} (xs : List (Fin n)) (h : xs.Nodup) :
    Equiv.Perm (Fin n) := by
  have hi : Function.Injective (positionInListing xs h) := by
    intro a b he
    exact (List.idxOf_inj (completeListing_contains xs a)).mp (congrArg Fin.val he)
  exact Equiv.ofBijective _ ⟨hi,Finite.surjective_of_injective hi⟩

private theorem marking_index {n : ℕ} (xs : List (Fin n)) (hn : xs.Nodup)
    (i : Fin xs.length) : (markingLabels xs hn (xs.get i)).val = i.val := by
  let a := xs.get i
  have ha : a ∈ xs := List.mem_of_getElem (i := i.val) (h := i.isLt) rfl
  change (completeListing xs).idxOf a = i.val
  rw [completeListing,List.idxOf_append_of_mem ha]
  have hi : xs.idxOf a < xs.length := List.idxOf_lt_length_iff.mpr ha
  have hget : xs.get ⟨xs.idxOf a,hi⟩ = xs.get i := List.getElem_idxOf hi
  exact congrArg Fin.val ((List.nodup_iff_injective_get.mp hn) hget)

private theorem marking_in_prefix {n : ℕ} (xs : List (Fin n)) (hn : xs.Nodup)
    (a : Fin n) : (markingLabels xs hn a).val < xs.length ↔ a ∈ xs := by
  change (completeListing xs).idxOf a < xs.length ↔ a ∈ xs
  constructor
  · intro hl
    have hi : (completeListing xs).idxOf a < (completeListing xs).length :=
      List.idxOf_lt_length_iff.mpr (completeListing_contains xs a)
    have hg := List.getElem_idxOf hi
    rw [show (completeListing xs)[(completeListing xs).idxOf a] =
        xs[(completeListing xs).idxOf a] from List.getElem_append_left hl] at hg
    exact List.mem_of_getElem hg
  · intro h
    rw [completeListing,List.idxOf_append_of_mem h]
    exact List.idxOf_lt_length_iff.mpr h

private theorem normalized_opening_wins {n fuel : ℕ} (hn : 4 ≤ n)
    (first second free : List (Cell n))
    (hCount : first.length + 2 = n) (hDiff : first.length = second.length + 1)
    (hBoard : LegalState free first second) (hInv : OpeningInvariant first second) :
    forceOutcome false free false first second (fuel+10) = true := by
  let rows := first.map Prod.fst
  let cols := first.map Prod.snd
  let rowLabels := markingLabels rows hInv.1
  let colLabels := markingLabels cols hInv.2.1
  let φ := Equiv.prodCongr rowLabels colLabels
  have hφ := transversal_permute rowLabels colLabels
  have hLabels (i : Fin first.length) :
      φ (first.get i) = (⟨i.val,by omega⟩,⟨i.val,by omega⟩) := by
    let ri : Fin rows.length := ⟨i.val,by simp [rows]⟩
    let ci : Fin cols.length := ⟨i.val,by simp [cols]⟩
    have hr : rows.get ri = (first.get i).1 := by simp [rows,ri]
    have hc : cols.get ci = (first.get i).2 := by simp [cols,ci]
    have hr' := marking_index rows hInv.1 ri
    have hc' := marking_index cols hInv.2.1 ci
    rw [hr] at hr'
    rw [hc] at hc'
    exact Prod.ext (Fin.ext hr') (Fin.ext hc')
  have hOnly (a : Cell n) (ha : a ∈ first.map φ) : a.1 = a.2 ∧ a.1.val < first.length := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, hi⟩ := List.get_of_mem hx
    rw [← hi, hLabels i]
    exact ⟨rfl, i.isLt⟩
  have hDiag (i : Fin n) (hi : i.val < first.length) : (i,i) ∈ first.map φ := by
    let k : Fin first.length := ⟨i.val,hi⟩
    refine List.mem_map.mpr ⟨first.get k, List.mem_of_getElem (i := k.val) (h := k.isLt) rfl, ?_⟩
    exact (hLabels k).trans (Prod.ext (Fin.ext rfl) (Fin.ext rfl))
  have hCover (a : Cell n) (ha : a ∈ second.map φ) :
      a.1.val < first.length ∨ a.2.val < first.length := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    rcases hInv.2.2.1 x hx with hrow | hcol
    · exact Or.inl (by simpa [rows,φ,rowLabels] using (marking_in_prefix rows hInv.1 x.1).mpr hrow)
    · exact Or.inr (by simpa [cols,φ,colLabels] using (marking_in_prefix cols hInv.2.1 x.2).mpr hcol)
  obtain ⟨x,hx,hxcol⟩ := hInv.2.2.2
  let u := colLabels x.2
  let v := rowLabels x.1
  have hu : first.length ≤ u.val := by
    apply le_of_not_gt
    intro hl
    apply hxcol
    exact (marking_in_prefix cols hInv.2.1 x.2).mp (by simpa [cols] using hl)
  have hvu : (v,u) ∈ second.map φ := List.mem_map.mpr ⟨x,hx,rfl⟩
  have hv : v.val < first.length := (hCover (v,u) hvu).resolve_right (not_lt_of_ge hu)
  let lo : Fin n := ⟨first.length,by omega⟩
  let hi : Fin n := ⟨first.length+1,by omega⟩
  have hSpare (i : Fin n) (hl : first.length ≤ i.val) : i = lo ∨ i = hi := by
    have hBound := i.isLt
    have hVal : i.val = first.length ∨ i.val = first.length+1 := by omega
    exact hVal.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
  let w := if u=lo then hi else lo
  have huw : u ≠ w := by
    have hne : lo ≠ hi := fun h => by
      have he := congrArg Fin.val h
      change first.length = first.length+1 at he
      omega
    rcases hSpare u hu with he | he
    · simp [w,he,hne]
    · simp [w,he,hne.symm]
  have hw : first.length ≤ w.val := by
    dsimp [w]
    split
    · change first.length ≤ first.length+1
      omega
    · exact le_rfl
  have hBoth (i : Fin n) (h : first.length ≤ i.val) : i = u ∨ i = w := by
    have hne : lo ≠ hi := fun he => by
      have hEq := congrArg Fin.val he
      change first.length = first.length+1 at hEq
      omega
    rcases hSpare u hu with hU | hU <;> rcases hSpare i h with hI | hI <;>
      simp [w,hU,hI,hne,hne.symm]
  have hNorm : forceOutcome false (free.map φ) false (first.map φ) (second.map φ) (fuel+10) = true := by
    refine bridge_normalized hn huw ?_ ?_ ?_ ?_ (mapped_state_legal φ hBoard) hvu ?_ ?_ ?_
    · intro he
      have h := congrArg Fin.val he
      omega
    · intro he
      have h := congrArg Fin.val he
      omega
    · simpa using hCount
    · simp
      omega
    · intro a ha
      obtain ⟨hd,hl⟩ := hOnly a ha
      exact ⟨hd,fun he => not_lt_of_ge hu (he ▸ hl),fun he => not_lt_of_ge hw (he ▸ hl)⟩
    · intro i hu' hw'
      exact hDiag i (lt_of_not_ge (fun h => (hBoth i h).elim hu' hw'))
    · intro i j hi hj hm
      have hI : first.length ≤ i.val := hi.elim (fun h => h.symm ▸ hu) (fun h => h.symm ▸ hw)
      have hJ : first.length ≤ j.val := hj.elim (fun h => h.symm ▸ hu) (fun h => h.symm ▸ hw)
      exact (hCover (i,j) hm).elim (not_lt_of_ge hI) (not_lt_of_ge hJ)
  exact (forceOutcome_equiv φ hφ false false free first second (fuel+10)).symm.trans hNorm

theorem wins_on_large_board (n : ℕ) (hn : 4 ≤ n) : firstWins n = true := by
  let spare := n*n - (2*n+5)
  have hle : 2*n+5 ≤ n*n := by
    have h := Nat.mul_le_mul_right n hn
    omega
  have hf : spare+10+2*(n-4)+1+1+1 = n*n := by
    dsimp [spare]
    omega
  unfold firstWins
  rw [← hf]
  apply reach_opening_end hn
  exact normalized_opening_wins hn

theorem full_outcome : ClaimedOutcome := by
  refine ⟨?_, two_by_two_draw, three_by_three_draw⟩
  intro n hn h₂ h₃
  by_cases h₁ : n = 1
  · subst n
    exact one_cell_win
  · exact wins_on_large_board n (by omega)

end TransversalGame

theorem OMA.solution : type_of% @OMA.S_opg_a_transversal_achievement_game_on_a_square_grid.main := by
  exact TransversalGame.full_outcome
