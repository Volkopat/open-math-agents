import OMAStatements.S_oeis_a211912

namespace OMA.S_oeis_a211912

open PowerSeries Finset






/-! ## The general coloring theorem -/

section Generic

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The values of x are introduced in order: every value below x c occurs at an earlier cell. -/
def RGS (x : α → ℕ) : Prop := ∀ c, ∀ u < x c, ∃ c', c' < c ∧ x c' = u

/-- No two neighbors have the same value. -/
def Proper (adj : α → α → Prop) (x : α → ℕ) : Prop := ∀ c c', adj c c' → x c ≠ x c'

/-! ## Positions in the order -/

/-- The position of a cell in the order, 0..N - 1. -/
noncomputable def pos (c : α) : ℕ := ((Fintype.orderIsoFinOfCardEq α rfl).symm c).val

lemma pos_lt (c : α) : pos c < Fintype.card α := ((Fintype.orderIsoFinOfCardEq α rfl).symm c).isLt

lemma lt_iff_pos (c c' : α) : c < c' ↔ pos c < pos c' := by
  unfold pos
  rw [← Fin.lt_def, OrderIso.lt_iff_lt]

lemma pos_inj : Function.Injective (@pos α _ _) := fun c c' h =>
  (Fintype.orderIsoFinOfCardEq α rfl).symm.injective (Fin.ext h)

lemma pos_surj (k : ℕ) (hk : k < Fintype.card α) : ∃ c : α, pos c = k :=
  ⟨Fintype.orderIsoFinOfCardEq α rfl ⟨k, hk⟩, by simp [pos]⟩

lemma rgs_iff (x : α → ℕ) : RGS x ↔ ∀ c, ∀ u < x c, ∃ c', pos c' < pos c ∧ x c' = u := by
  unfold RGS
  simp only [lt_iff_pos]

/-! ## The colorings that use at least N - 1 values -/

/-- The coloring that gives the cell b the value of the cell a and numbers the other cells in
order, skipping b. -/
noncomputable def rep (a b c : α) : ℕ :=
  if pos c < pos b then pos c else if pos c = pos b then pos a else pos c - 1

lemma rep_lt {a b c : α} (h : pos c < pos b) : rep a b c = pos c := by
  unfold rep; rw [if_pos h]

lemma rep_eq {a b c : α} (h : pos c = pos b) : rep a b c = pos a := by
  unfold rep; rw [if_neg (by omega), if_pos h]

lemma rep_gt {a b c : α} (h : pos b < pos c) : rep a b c = pos c - 1 := by
  unfold rep; rw [if_neg (by omega), if_neg (by omega)]

lemma le_pos (x : α → ℕ) (hx : ∀ c, ∀ u < x c, ∃ c', pos c' < pos c ∧ x c' = u)
    (c : α) : x c ≤ pos c := by
  induction hk : pos c using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    by_contra h
    obtain ⟨e, he, hxe⟩ := hx c k (by omega)
    have := ih (pos e) (by omega) e rfl
    omega

/-- A coloring whose values are introduced in order and which reaches N - 2 is the numbering of the
cells in order, or repeats the value of one cell once. -/
lemma rgs_cases (x : α → ℕ) (hx : ∀ c, ∀ u < x c, ∃ c', pos c' < pos c ∧ x c' = u)
    (c0 : α) (h0 : x c0 + 2 = Fintype.card α) :
    x = pos ∨ ∃ a b : α, pos a < pos b ∧ x = rep a b := by
  by_cases hall : ∀ c, x c = pos c
  · exact Or.inl (funext hall)
  push_neg at hall
  have hex : ∃ k, ∃ c, pos c = k ∧ x c ≠ pos c := let ⟨c, hc⟩ := hall; ⟨pos c, c, rfl, hc⟩
  obtain ⟨b, hbk, hbne⟩ := Nat.find_spec hex
  have hmin : ∀ c, pos c < pos b → x c = pos c := by
    intro c hc
    by_contra hne
    exact Nat.find_min hex (hbk ▸ hc) ⟨c, rfl, hne⟩
  have hblt : x b < pos b := lt_of_le_of_ne (le_pos x hx b) hbne
  obtain ⟨a, ha⟩ := pos_surj (α := α) (x b) (by have := pos_lt b; omega)
  have R2 : ∀ c, pos b ≤ pos c → x c + 1 ≤ pos c := by
    intro c
    induction hk : pos c using Nat.strong_induction_on generalizing c with
    | _ k ih =>
      intro hbc
      rcases Nat.eq_or_lt_of_le hbc with h | h
      · have : c = b := pos_inj (by omega)
        subst this; omega
      · by_contra hc
        have hxc := le_pos x hx c
        obtain ⟨e, he, hxe⟩ := hx c (k - 1) (by omega)
        by_cases heb : pos e < pos b
        · have := hmin e heb; omega
        · have := ih (pos e) (by omega) e rfl (by omega); omega
  have R3 : ∀ t, ∀ c, pos c + t + 1 = Fintype.card α → pos b < pos c → x c = pos c - 1 := by
    intro t
    induction t with
    | zero =>
      intro c hc hbc
      have hc0 : pos c0 + 1 = Fintype.card α := by
        by_cases h : pos c0 < pos b
        · have := hmin c0 h; omega
        · have := R2 c0 (by omega); have := pos_lt c0; omega
      have : c = c0 := pos_inj (by omega)
      subst this; omega
    | succ t ih =>
      intro c hc hbc
      obtain ⟨c', hc'⟩ := pos_surj (α := α) (pos c + 1) (by omega)
      have hx' := ih c' (by omega) (by omega)
      obtain ⟨e, he, hxe⟩ := hx c' (pos c - 1) (by omega)
      by_cases heb : pos e < pos b
      · have := hmin e heb; omega
      · by_cases hec : pos e < pos c
        · have := R2 e (by omega); omega
        · have : e = c := pos_inj (by omega)
          subst this; omega
  refine Or.inr ⟨a, b, by omega, funext fun c => ?_⟩
  rcases lt_trichotomy (pos c) (pos b) with h | h | h
  · rw [rep_lt h]; exact hmin c h
  · rw [rep_eq h, pos_inj h]; omega
  · rw [rep_gt h]; exact R3 (Fintype.card α - 1 - pos c) c (by have := pos_lt c; omega) h

lemma rgs_pos : ∀ c : α, ∀ u < pos c, ∃ c' : α, pos c' < pos c ∧ pos c' = u := by
  intro c u hu
  obtain ⟨c', hc'⟩ := pos_surj (α := α) u (lt_trans hu (pos_lt c))
  exact ⟨c', by omega, hc'⟩

lemma rgs_rep (a b : α) (hab : pos a < pos b) :
    ∀ c, ∀ u < rep a b c, ∃ c', pos c' < pos c ∧ rep a b c' = u := by
  intro c u hu
  have hc := pos_lt c
  rcases lt_trichotomy (pos c) (pos b) with h | h | h
  · rw [rep_lt h] at hu
    obtain ⟨e, he⟩ := pos_surj (α := α) u (by omega)
    exact ⟨e, by omega, by rw [rep_lt (by omega)]; exact he⟩
  · rw [rep_eq h] at hu
    obtain ⟨e, he⟩ := pos_surj (α := α) u (by omega)
    exact ⟨e, by omega, by rw [rep_lt (by omega)]; exact he⟩
  · rw [rep_gt h] at hu
    by_cases hub : u < pos b
    · obtain ⟨e, he⟩ := pos_surj (α := α) u (by omega)
      exact ⟨e, by omega, by rw [rep_lt (by omega)]; exact he⟩
    · obtain ⟨e, he⟩ := pos_surj (α := α) (u + 1) (by omega)
      exact ⟨e, by omega, by rw [rep_gt (by omega)]; omega⟩

lemma rep_top (a b : α) (hab : pos a < pos b) : ∃ c, rep a b c + 2 = Fintype.card α := by
  have hb := pos_lt b
  by_cases hlast : pos b + 1 = Fintype.card α
  · obtain ⟨c, hc⟩ := pos_surj (α := α) (Fintype.card α - 2) (by omega)
    exact ⟨c, by rw [rep_lt (by omega)]; omega⟩
  · obtain ⟨c, hc⟩ := pos_surj (α := α) (Fintype.card α - 1) (by omega)
    exact ⟨c, by rw [rep_gt (by omega)]; omega⟩

lemma rep_inj (a b : α) (hab : pos a < pos b) (c c' : α)
    (h : rep a b c = rep a b c') (hne : c ≠ c') : (c = a ∧ c' = b) ∨ (c = b ∧ c' = a) := by
  have hr : pos c ≠ pos c' := fun e => hne (pos_inj e)
  rcases lt_trichotomy (pos c) (pos b) with h1 | h1 | h1 <;>
    rcases lt_trichotomy (pos c') (pos b) with h2 | h2 | h2
  · rw [rep_lt h1, rep_lt h2] at h; omega
  · rw [rep_lt h1, rep_eq h2] at h
    exact Or.inl ⟨pos_inj h, pos_inj h2⟩
  · rw [rep_lt h1, rep_gt h2] at h; omega
  · rw [rep_eq h1, rep_lt h2] at h
    exact Or.inr ⟨pos_inj h1, pos_inj h.symm⟩
  · omega
  · rw [rep_eq h1, rep_gt h2] at h; omega
  · rw [rep_gt h1, rep_lt h2] at h; omega
  · rw [rep_gt h1, rep_eq h2] at h; omega
  · rw [rep_gt h1, rep_gt h2] at h; omega

section Adj

variable (adj : α → α → Prop) [DecidableRel adj]

lemma proper_pos (hirr : ∀ c, ¬ adj c c) : Proper adj (@pos α _ _) := fun c c' h e => by
  rw [pos_inj e] at h; exact hirr c' h

lemma proper_rep (hsymm : ∀ c c', adj c c' → adj c' c) (hirr : ∀ c, ¬ adj c c)
    (a b : α) (hab : pos a < pos b) : Proper adj (rep a b) ↔ ¬ adj a b := by
  constructor
  · intro h hn
    exact h a b hn (by rw [rep_lt hab, rep_eq rfl])
  · intro hn c c' hcc' heq
    have hne : c ≠ c' := fun e => by rw [e] at hcc'; exact hirr c' hcc'
    rcases rep_inj a b hab c c' heq hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hn hcc'
    · exact hn (hsymm _ _ hcc')

/-- The pairs a < b of cells that are not neighbors. -/
noncomputable def nonEdges : Finset (α × α) := (univ : Finset (α × α)).filter (fun p => p.1 < p.2 ∧ ¬ adj p.1 p.2)

/-- The pairs a < b of neighbors. -/
noncomputable def edges : Finset (α × α) := (univ : Finset (α × α)).filter (fun p => p.1 < p.2 ∧ adj p.1 p.2)

lemma set_eq (hsymm : ∀ c c', adj c c' → adj c' c) (hirr : ∀ c, ¬ adj c c)
    (hN : 2 ≤ Fintype.card α) :
    {x : α → ℕ | RGS x ∧ Proper adj x ∧ ∃ c, x c + 2 = Fintype.card α} =
      (fun o : Option (α × α) => o.elim pos (fun p => rep p.1 p.2)) ''
        ↑(insert none ((nonEdges adj).map Function.Embedding.some)) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, coe_insert, coe_map, nonEdges, coe_filter, mem_univ,
    true_and, Set.mem_insert_iff]
  constructor
  · rintro ⟨hr, hc, c0, h0⟩
    rw [rgs_iff] at hr
    rcases rgs_cases x hr c0 h0 with rfl | ⟨a, b, hab, rfl⟩
    · exact ⟨none, Or.inl rfl, rfl⟩
    · refine ⟨some (a, b), Or.inr ⟨(a, b), ⟨(lt_iff_pos a b).2 hab,
        (proper_rep adj hsymm hirr a b hab).1 hc⟩, rfl⟩, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    rcases ho with rfl | ⟨⟨a, b⟩, ⟨hab, hn⟩, rfl⟩
    · refine ⟨(rgs_iff _).2 rgs_pos, proper_pos adj hirr, ?_⟩
      obtain ⟨c, hc⟩ := pos_surj (α := α) (Fintype.card α - 2) (by omega)
      exact ⟨c, by simp only [Option.elim]; omega⟩
    · have hab' : pos a < pos b := (lt_iff_pos a b).1 hab
      refine ⟨(rgs_iff _).2 (rgs_rep a b hab'), (proper_rep adj hsymm hirr a b hab').2 hn, ?_⟩
      obtain ⟨c, hc⟩ := rep_top a b hab'
      exact ⟨c, by simp only [Option.elim, Function.Embedding.some_apply]; omega⟩

lemma injOn_opt :
    Set.InjOn (fun o : Option (α × α) => o.elim pos (fun p => rep p.1 p.2))
      ↑(insert none ((nonEdges adj).map Function.Embedding.some)) := by
  have key : ∀ a b : α, pos a < pos b → rep a b ≠ pos := fun a b hab e => by
    have := congrFun e b
    rw [rep_eq rfl] at this; omega
  intro o ho o' ho' h
  simp only [coe_insert, coe_map, nonEdges, coe_filter, mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_image, Set.mem_setOf_eq, Function.Embedding.some_apply] at ho ho'
  rcases ho with rfl | ⟨⟨a, b⟩, ⟨hab, _⟩, rfl⟩ <;> rcases ho' with rfl | ⟨⟨a', b'⟩, ⟨hab', _⟩, rfl⟩
  · rfl
  · exact absurd h.symm (key a' b' ((lt_iff_pos a' b').1 hab'))
  · exact absurd h (key a b ((lt_iff_pos a b).1 hab))
  · simp only [Option.elim] at h
    have h1 : pos a < pos b := (lt_iff_pos a b).1 hab
    have h2 : pos a' < pos b' := (lt_iff_pos a' b').1 hab'
    have hb : pos b = pos b' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · have := congrFun h b
        rw [rep_eq rfl, rep_lt hl] at this; omega
      · have := congrFun h b'
        rw [rep_eq rfl, rep_lt hl] at this; omega
    have hbb := pos_inj hb
    subst hbb
    have := congrFun h b
    rw [rep_eq rfl, rep_eq rfl] at this
    rw [pos_inj this]

/-- **The coloring theorem, N - 2.** For N ≥ 2 cells, the proper colorings with values introduced
in order that contain the value N - 2 number 1 + (the pairs of cells that are not neighbors). -/
theorem count_N2 (hsymm : ∀ c c', adj c c' → adj c' c) (hirr : ∀ c, ¬ adj c c)
    (hN : 2 ≤ Fintype.card α) :
    {x : α → ℕ | RGS x ∧ Proper adj x ∧ ∃ c, x c + 2 = Fintype.card α}.ncard =
      (nonEdges adj).card + 1 := by
  rw [set_eq adj hsymm hirr hN, (injOn_opt adj).ncard_image, Set.ncard_coe_finset,
    card_insert_of_notMem (by simp), card_map]

lemma card_lt_pairs :
    2 * ((univ : Finset (α × α)).filter (fun p => p.1 < p.2)).card =
      Fintype.card α * (Fintype.card α - 1) := by
  have h1 : ((univ : Finset (α × α)).filter (fun p => p.1 < p.2)).card =
      ((range (Fintype.card α) ×ˢ range (Fintype.card α)).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
    apply card_nbij (fun p => (pos p.1, pos p.2))
    · intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq]
      exact ⟨⟨pos_lt _, pos_lt _⟩, (lt_iff_pos _ _).1 hp⟩
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (pos_inj h.1) (pos_inj h.2)
    · rintro ⟨u, v⟩ h
      simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h
      obtain ⟨a, ha⟩ := pos_surj (α := α) u h.1.1
      obtain ⟨b, hb⟩ := pos_surj (α := α) v h.1.2
      refine ⟨(a, b), ?_, by simp only [ha, hb]⟩
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      rw [lt_iff_pos, ha, hb]; exact h.2
  rw [h1, card_filter, sum_product_right]
  have h : ∀ v ∈ range (Fintype.card α),
      (∑ u ∈ range (Fintype.card α), if (u, v).1 < (u, v).2 then 1 else 0) = v := by
    intro v hv
    rw [mem_range] at hv
    have e : (range (Fintype.card α)).filter (fun u => u < v) = range v := by
      ext u; simp only [mem_filter, mem_range]; omega
    simp only [sum_boole, e, card_range, Nat.cast_id]
  rw [sum_congr rfl h, mul_comm, sum_range_id_mul_two]

/-- Every pair a < b of cells is a pair of neighbors or not: 2 (P + E) = N (N - 1). -/
lemma card_nonEdges_add_edges :
    2 * ((nonEdges adj).card + (edges adj).card) = Fintype.card α * (Fintype.card α - 1) := by
  rw [← card_lt_pairs]
  congr 1
  rw [← card_filter_add_card_filter_not (s := (univ : Finset (α × α)).filter (fun p => p.1 < p.2))
    (fun p => adj p.1 p.2), filter_filter, filter_filter, add_comm]
  rfl

/-- The same count with the number E of pairs of neighbors: 2 (count - 1) = N (N - 1) - 2 E. -/
theorem count_N2_edges (hsymm : ∀ c c', adj c c' → adj c' c) (hirr : ∀ c, ¬ adj c c)
    (hN : 2 ≤ Fintype.card α) :
    2 * {x : α → ℕ | RGS x ∧ Proper adj x ∧ ∃ c, x c + 2 = Fintype.card α}.ncard + 2 * (edges adj).card =
      Fintype.card α * (Fintype.card α - 1) + 2 := by
  rw [count_N2 adj hsymm hirr hN, ← card_nonEdges_add_edges adj]
  ring

end Adj

/-! ## The colorings that use at least N - 2 values -/

/-- The coloring that gives b1 the value v1 and b2 the value v2 and numbers the other cells in
order, skipping b1 and b2. -/
noncomputable def rep2 (b1 : α) (v1 : ℕ) (b2 : α) (v2 : ℕ) (c : α) : ℕ :=
  if pos c < pos b1 then pos c else if pos c = pos b1 then v1 else
    if pos c < pos b2 then pos c - 1 else if pos c = pos b2 then v2 else pos c - 2

section Rep2

variable {b1 b2 : α} {v1 v2 : ℕ}

lemma rep2_a {c : α} (h : pos c < pos b1) : rep2 b1 v1 b2 v2 c = pos c := by
  unfold rep2; rw [if_pos h]

lemma rep2_b1 {c : α} (h : pos c = pos b1) : rep2 b1 v1 b2 v2 c = v1 := by
  unfold rep2; rw [if_neg (by omega), if_pos h]

lemma rep2_m {c : α} (h1 : pos b1 < pos c) (h2 : pos c < pos b2) : rep2 b1 v1 b2 v2 c = pos c - 1 := by
  unfold rep2; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

lemma rep2_b2 {c : α} (hb : pos b1 < pos b2) (h : pos c = pos b2) : rep2 b1 v1 b2 v2 c = v2 := by
  unfold rep2; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

lemma rep2_z {c : α} (hb : pos b1 < pos b2) (h : pos b2 < pos c) : rep2 b1 v1 b2 v2 c = pos c - 2 := by
  unfold rep2; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end Rep2

/-- A coloring whose values are introduced in order and which reaches N - 3 numbers the cells in
order, or repeats one earlier value once, or repeats earlier values twice. -/
lemma rgs_cases3 (x : α → ℕ) (hx : ∀ c, ∀ u < x c, ∃ c', pos c' < pos c ∧ x c' = u)
    (c0 : α) (h0 : x c0 + 3 = Fintype.card α) :
    x = pos ∨ (∃ a b : α, pos a < pos b ∧ x = rep a b) ∨
      ∃ b1 b2 : α, ∃ v1 v2 : ℕ, pos b1 < pos b2 ∧ v1 < pos b1 ∧ v2 + 2 ≤ pos b2 ∧
        x = rep2 b1 v1 b2 v2 := by
  by_cases hall : ∀ c, x c = pos c
  · exact Or.inl (funext hall)
  push_neg at hall
  have hex : ∃ k, ∃ c, pos c = k ∧ x c ≠ pos c := let ⟨c, hc⟩ := hall; ⟨pos c, c, rfl, hc⟩
  obtain ⟨b1, hbk, hbne⟩ := Nat.find_spec hex
  have hmin : ∀ c, pos c < pos b1 → x c = pos c := by
    intro c hc
    by_contra hne
    exact Nat.find_min hex (hbk ▸ hc) ⟨c, rfl, hne⟩
  have hb1 : x b1 < pos b1 := lt_of_le_of_ne (le_pos x hx b1) hbne
  have R2 : ∀ c, pos b1 ≤ pos c → x c + 1 ≤ pos c := by
    intro c
    induction hk : pos c using Nat.strong_induction_on generalizing c with
    | _ k ih =>
      intro hbc
      rcases Nat.eq_or_lt_of_le hbc with h | h
      · have : c = b1 := pos_inj (by omega)
        subst this; omega
      · by_contra hc
        have hxc := le_pos x hx c
        obtain ⟨e, he, hxe⟩ := hx c (k - 1) (by omega)
        by_cases heb : pos e < pos b1
        · have := hmin e heb; omega
        · have := ih (pos e) (by omega) e rfl (by omega); omega
  by_cases hall2 : ∀ c, pos b1 < pos c → x c = pos c - 1
  · obtain ⟨a, ha⟩ := pos_surj (α := α) (x b1) (by have := pos_lt b1; omega)
    refine Or.inr (Or.inl ⟨a, b1, by omega, funext fun c => ?_⟩)
    rcases lt_trichotomy (pos c) (pos b1) with h | h | h
    · rw [rep_lt h]; exact hmin c h
    · rw [rep_eq h, pos_inj h]; omega
    · rw [rep_gt h]; exact hall2 c h
  push_neg at hall2
  have hex2 : ∃ k, ∃ c, pos c = k ∧ pos b1 < pos c ∧ x c ≠ pos c - 1 :=
    let ⟨c, hc1, hc2⟩ := hall2; ⟨pos c, c, rfl, hc1, hc2⟩
  obtain ⟨b2, hbk2, hb12, hbne2⟩ := Nat.find_spec hex2
  have hmin2 : ∀ c, pos b1 < pos c → pos c < pos b2 → x c = pos c - 1 := by
    intro c hc1 hc2
    by_contra hne
    exact Nat.find_min hex2 (hbk2 ▸ hc2) ⟨c, rfl, hc1, hne⟩
  have hb2 : x b2 + 2 ≤ pos b2 := by have := R2 b2 (by omega); omega
  have R2' : ∀ c, pos b2 ≤ pos c → x c + 2 ≤ pos c := by
    intro c
    induction hk : pos c using Nat.strong_induction_on generalizing c with
    | _ k ih =>
      intro hbc
      rcases Nat.eq_or_lt_of_le hbc with h | h
      · have : c = b2 := pos_inj (by omega)
        subst this; omega
      · by_contra hc
        have hxc := R2 c (by omega)
        obtain ⟨e, he, hxe⟩ := hx c (k - 2) (by omega)
        by_cases h1 : pos e < pos b1
        · have := hmin e h1; omega
        · by_cases h2 : pos e = pos b1
          · have : e = b1 := pos_inj h2
            subst this; omega
          · by_cases h3 : pos e < pos b2
            · have := hmin2 e (by omega) h3; omega
            · by_cases h4 : pos e = pos b2
              · have : e = b2 := pos_inj h4
                subst this; omega
              · have := ih (pos e) (by omega) e rfl (by omega); omega
  have R3 : ∀ t, ∀ c, pos c + t + 1 = Fintype.card α → pos b2 < pos c → x c = pos c - 2 := by
    intro t
    induction t with
    | zero =>
      intro c hc hbc
      have hc0 : pos c0 + 1 = Fintype.card α := by
        by_cases h1 : pos c0 < pos b1
        · have := hmin c0 h1; omega
        · by_cases h2 : pos c0 = pos b1
          · have : c0 = b1 := pos_inj h2
            subst this; omega
          · by_cases h3 : pos c0 < pos b2
            · have := hmin2 c0 (by omega) h3; omega
            · by_cases h4 : pos c0 = pos b2
              · have : c0 = b2 := pos_inj h4
                subst this; omega
              · have := R2' c0 (by omega); have := pos_lt c0; omega
      have : c = c0 := pos_inj (by omega)
      subst this; omega
    | succ t ih =>
      intro c hc hbc
      obtain ⟨c', hc'⟩ := pos_surj (α := α) (pos c + 1) (by omega)
      have hx' := ih c' (by omega) (by omega)
      obtain ⟨e, he, hxe⟩ := hx c' (pos c - 2) (by omega)
      by_cases h1 : pos e < pos b1
      · have := hmin e h1; omega
      · by_cases h2 : pos e = pos b1
        · have : e = b1 := pos_inj h2
          subst this; omega
        · by_cases h3 : pos e < pos b2
          · have := hmin2 e (by omega) h3; omega
          · by_cases h4 : pos e = pos b2
            · have : e = b2 := pos_inj h4
              subst this; omega
            · by_cases h5 : pos e < pos c
              · have := R2' e (by omega); omega
              · have : e = c := pos_inj (by omega)
                subst this; omega
  refine Or.inr (Or.inr ⟨b1, b2, x b1, x b2, hb12, hb1, hb2, funext fun c => ?_⟩)
  rcases lt_trichotomy (pos c) (pos b1) with h | h | h
  · rw [rep2_a h]; exact hmin c h
  · rw [rep2_b1 h, pos_inj h]
  · rcases lt_trichotomy (pos c) (pos b2) with h' | h' | h'
    · rw [rep2_m h h']; exact hmin2 c h h'
    · rw [rep2_b2 hb12 h', pos_inj h']
    · rw [rep2_z hb12 h']; exact R3 (Fintype.card α - 1 - pos c) c (by have := pos_lt c; omega) h'

section Rep2Facts

variable {b1 b2 : α} {v1 v2 : ℕ}

lemma rgs_rep2 (hb : pos b1 < pos b2) (hv1 : v1 < pos b1) (hv2 : v2 + 2 ≤ pos b2) :
    ∀ c, ∀ u < rep2 b1 v1 b2 v2 c, ∃ c', pos c' < pos c ∧ rep2 b1 v1 b2 v2 c' = u := by
  intro c u hu
  have hc := pos_lt c
  have hb2 := pos_lt b2
  -- the cell holding the value u among the cells before position p (p ≤ pos b2 + ...)
  have below : ∀ p, p ≤ pos c → u + 2 < p + (if pos b2 < pos c then 1 else 2) →
      (u < pos b1 ∨ u + 1 < pos b2 ∨ pos b2 < pos c) → ∃ c', pos c' < pos c ∧ rep2 b1 v1 b2 v2 c' = u := by
    intro p _ _ _
    by_cases h1 : u < pos b1
    · obtain ⟨e, he⟩ := pos_surj (α := α) u (by omega)
      by_cases hcb : pos c ≤ u
      · exfalso
        rcases lt_trichotomy (pos c) (pos b1) with h | h | h
        · rw [rep2_a h] at hu; omega
        · omega
        · omega
      · exact ⟨e, by omega, by rw [rep2_a (by omega)]; exact he⟩
    · by_cases h2 : u + 1 < pos b2
      · obtain ⟨e, he⟩ := pos_surj (α := α) (u + 1) (by omega)
        refine ⟨e, ?_, by rw [rep2_m (by omega) (by omega)]; omega⟩
        rcases lt_trichotomy (pos c) (pos b1) with h | h | h
        · rw [rep2_a h] at hu; omega
        · rw [rep2_b1 h] at hu; omega
        · rcases lt_trichotomy (pos c) (pos b2) with h' | h' | h'
          · rw [rep2_m h h'] at hu; omega
          · rw [rep2_b2 hb h'] at hu; omega
          · omega
      · obtain ⟨e, he⟩ := pos_surj (α := α) (u + 2) (by
          rcases lt_trichotomy (pos c) (pos b1) with h | h | h
          · rw [rep2_a h] at hu; omega
          · rw [rep2_b1 h] at hu; omega
          · rcases lt_trichotomy (pos c) (pos b2) with h' | h' | h'
            · rw [rep2_m h h'] at hu; omega
            · rw [rep2_b2 hb h'] at hu; omega
            · rw [rep2_z hb h'] at hu; omega)
        refine ⟨e, ?_, by rw [rep2_z hb (by omega)]; omega⟩
        rcases lt_trichotomy (pos c) (pos b1) with h | h | h
        · rw [rep2_a h] at hu; omega
        · rw [rep2_b1 h] at hu; omega
        · rcases lt_trichotomy (pos c) (pos b2) with h' | h' | h'
          · rw [rep2_m h h'] at hu; omega
          · rw [rep2_b2 hb h'] at hu; omega
          · rw [rep2_z hb h'] at hu; omega
  exact below (pos c) le_rfl (by
    rcases lt_trichotomy (pos c) (pos b1) with h | h | h
    · rw [rep2_a h] at hu; split_ifs <;> omega
    · rw [rep2_b1 h] at hu; split_ifs <;> omega
    · rcases lt_trichotomy (pos c) (pos b2) with h' | h' | h'
      · rw [rep2_m h h'] at hu; split_ifs <;> omega
      · rw [rep2_b2 hb h'] at hu; split_ifs <;> omega
      · rw [rep2_z hb h'] at hu; split_ifs <;> omega) (by
    rcases lt_trichotomy (pos c) (pos b1) with h | h | h
    · rw [rep2_a h] at hu; omega
    · rw [rep2_b1 h] at hu; omega
    · rcases lt_trichotomy (pos c) (pos b2) with h' | h' | h'
      · rw [rep2_m h h'] at hu; omega
      · rw [rep2_b2 hb h'] at hu; omega
      · omega)

lemma rep2_top (hb : pos b1 < pos b2) (hv1 : v1 < pos b1) :
    ∃ c, rep2 b1 v1 b2 v2 c + 3 = Fintype.card α := by
  have hb2 := pos_lt b2
  by_cases hlast : pos b2 + 1 = Fintype.card α
  · by_cases hmid : pos b1 + 1 < pos b2
    · obtain ⟨c, hc⟩ := pos_surj (α := α) (Fintype.card α - 2) (by omega)
      exact ⟨c, by rw [rep2_m (by omega) (by omega)]; omega⟩
    · obtain ⟨c, hc⟩ := pos_surj (α := α) (Fintype.card α - 3) (by omega)
      exact ⟨c, by rw [rep2_a (by omega)]; omega⟩
  · obtain ⟨c, hc⟩ := pos_surj (α := α) (Fintype.card α - 1) (by omega)
    exact ⟨c, by rw [rep2_z hb (by omega)]; omega⟩

/-- Two different cells with the same value: b1 and the cell at position v1, or b2 and an earlier
cell with the value v2. -/
lemma rep2_same (hb : pos b1 < pos b2) (hv1 : v1 < pos b1) (hv2 : v2 + 2 ≤ pos b2) (c c' : α)
    (hcc : pos c < pos c') (h : rep2 b1 v1 b2 v2 c = rep2 b1 v1 b2 v2 c') :
    (pos c = v1 ∧ c' = b1) ∨ (c' = b2 ∧ rep2 b1 v1 b2 v2 c = v2) := by
  rcases lt_trichotomy (pos c') (pos b1) with h1 | h1 | h1
  · rw [rep2_a h1, rep2_a (by omega)] at h; omega
  · rw [rep2_b1 h1, rep2_a (by omega)] at h
    exact Or.inl ⟨h, pos_inj h1⟩
  · rcases lt_trichotomy (pos c') (pos b2) with h2 | h2 | h2
    · rw [rep2_m h1 h2] at h
      rcases lt_trichotomy (pos c) (pos b1) with h3 | h3 | h3
      · rw [rep2_a h3] at h; omega
      · rw [rep2_b1 h3] at h; omega
      · rw [rep2_m h3 (by omega)] at h; omega
    · right
      refine ⟨pos_inj h2, ?_⟩
      rw [h, rep2_b2 hb h2]
    · rw [rep2_z hb h2] at h
      rcases lt_trichotomy (pos c) (pos b1) with h3 | h3 | h3
      · rw [rep2_a h3] at h; omega
      · rw [rep2_b1 h3] at h; omega
      · rcases lt_trichotomy (pos c) (pos b2) with h4 | h4 | h4
        · rw [rep2_m h3 h4] at h; omega
        · rw [rep2_b2 hb h4] at h; omega
        · rw [rep2_z hb h4] at h; omega

end Rep2Facts

section Adj3

variable (adj : α → α → Prop) [DecidableRel adj]

lemma proper_rep2 (hsymm : ∀ c c', adj c c' → adj c' c) (hirr : ∀ c, ¬ adj c c)
    {b1 b2 : α} {v1 v2 : ℕ} (hb : pos b1 < pos b2) (hv1 : v1 < pos b1) (hv2 : v2 + 2 ≤ pos b2)
    (a1 : α) (ha1 : pos a1 = v1) :
    Proper adj (rep2 b1 v1 b2 v2) ↔
      ¬ adj a1 b1 ∧ ∀ w, pos w < pos b2 → rep2 b1 v1 b2 v2 w = v2 → ¬ adj w b2 := by
  constructor
  · intro h
    refine ⟨fun hn => h a1 b1 hn (by rw [rep2_a (by omega), rep2_b1 rfl, ha1]),
      fun w hw hwv hn => h w b2 hn (by rw [hwv, rep2_b2 hb rfl])⟩
  · rintro ⟨h1, h2⟩ c c' hcc heq
    have hne : c ≠ c' := fun e => by rw [e] at hcc; exact hirr c' hcc
    have key : ∀ d d' : α, adj d d' → pos d < pos d' → rep2 b1 v1 b2 v2 d = rep2 b1 v1 b2 v2 d' → False := by
      intro d d' hdd hlt hval
      rcases rep2_same hb hv1 hv2 d d' hlt hval with ⟨hd, rfl⟩ | ⟨rfl, hd⟩
      · exact h1 (by rw [pos_inj (hd.trans ha1.symm)] at hdd; exact hdd)
      · exact h2 d hlt hd hdd
    rcases lt_or_gt_of_ne (fun e : pos c = pos c' => hne (pos_inj e)) with hlt | hlt
    · exact key c c' hcc hlt heq
    · exact key c' c (hsymm _ _ hcc) hlt heq.symm

/-- The triples a < b < c of cells, no two neighbors. -/
noncomputable def indep3 : Finset (α × α × α) :=
  (univ : Finset (α × α × α)).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    ¬ adj t.1 t.2.1 ∧ ¬ adj t.1 t.2.2 ∧ ¬ adj t.2.1 t.2.2)

/-- The pairs of disjoint pairs a1 < b1, a2 < b2 of cells that are not neighbors, ordered by
b1 < b2. -/
noncomputable def pairs2 : Finset ((α × α) × (α × α)) :=
  (univ : Finset ((α × α) × (α × α))).filter (fun q => q.1.1 < q.1.2 ∧ q.2.1 < q.2.2 ∧
    q.1.2 < q.2.2 ∧ q.2.1 ≠ q.1.1 ∧ q.2.1 ≠ q.1.2 ∧ ¬ adj q.1.1 q.1.2 ∧ ¬ adj q.2.1 q.2.2)

/-- The colorings named by the options: the numbering, one repetition, a triple, two pairs. -/
noncomputable def col3 : Option (α × α) ⊕ (α × α × α) ⊕ ((α × α) × (α × α)) → α → ℕ
  | Sum.inl o => o.elim pos (fun p => rep p.1 p.2)
  | Sum.inr (Sum.inl t) => rep2 t.2.1 (pos t.1) t.2.2 (pos t.1)
  | Sum.inr (Sum.inr q) => rep2 q.1.2 (pos q.1.1) q.2.2 (rep q.1.1 q.1.2 q.2.1)

/-- Their domain. -/
noncomputable def dom3 : Finset (Option (α × α) ⊕ (α × α × α) ⊕ ((α × α) × (α × α))) :=
  (insert none ((nonEdges adj).map Function.Embedding.some)).disjSum ((indep3 adj).disjSum (pairs2 adj))

/-- The value of the cell a2 (not b1) in `rep a1 b1`, as an earlier value of `rep2`. -/
lemma rep_a2_le {a1 b1 a2 b2 : α} (h12 : pos a1 < pos b1) (hb : pos b1 < pos b2)
    (h22 : pos a2 < pos b2) (hne : a2 ≠ b1) : rep a1 b1 a2 + 2 ≤ pos b2 := by
  have : pos a2 ≠ pos b1 := fun e => hne (pos_inj e)
  rcases lt_or_gt_of_ne this with h | h
  · rw [rep_lt h]; omega
  · rw [rep_gt h]; omega

lemma rep2_at_a2 {a1 b1 a2 b2 : α} (hb : pos b1 < pos b2) (h22 : pos a2 < pos b2) (hne : a2 ≠ b1) :
    rep2 b1 (pos a1) b2 (rep a1 b1 a2) a2 = rep a1 b1 a2 := by
  have : pos a2 ≠ pos b1 := fun e => hne (pos_inj e)
  rcases lt_or_gt_of_ne this with h | h
  · rw [rep2_a h, rep_lt h]
  · rw [rep2_m h h22, rep_gt h]

lemma rep_a2_ne {a1 b1 a2 : α} (h12 : pos a1 < pos b1) (h1 : a2 ≠ a1) (h2 : a2 ≠ b1) :
    rep a1 b1 a2 ≠ pos a1 := by
  have : pos a2 ≠ pos b1 := fun e => h2 (pos_inj e)
  have : pos a2 ≠ pos a1 := fun e => h1 (pos_inj e)
  rcases lt_or_gt_of_ne (show pos a2 ≠ pos b1 by assumption) with h | h
  · rw [rep_lt h]; assumption
  · rw [rep_gt h]; omega

lemma rep_top3 {a b : α} (hab : pos a < pos b) (hN : 3 ≤ Fintype.card α) :
    ∃ c, rep a b c + 3 = Fintype.card α := by
  have hb := pos_lt b
  by_cases h : Fintype.card α - 3 < pos b
  · obtain ⟨c, hc⟩ := pos_surj (α := α) (Fintype.card α - 3) (by omega)
    exact ⟨c, by rw [rep_lt (by omega)]; omega⟩
  · obtain ⟨c, hc⟩ := pos_surj (α := α) (Fintype.card α - 2) (by omega)
    exact ⟨c, by rw [rep_gt (by omega)]; omega⟩

lemma pos_ne_rep2 {b1 b2 : α} {v1 v2 : ℕ} (hv1 : v1 < pos b1) : (@pos α _ _) ≠ rep2 b1 v1 b2 v2 :=
  fun e => by have := congrFun e b1; rw [rep2_b1 rfl] at this; omega

lemma rep_ne_rep2 {a b b1 b2 : α} {v1 v2 : ℕ} (hab : pos a < pos b) (hb : pos b1 < pos b2)
    (hv1 : v1 < pos b1) (hv2 : v2 + 2 ≤ pos b2) : rep a b ≠ rep2 b1 v1 b2 v2 := by
  intro e
  rcases lt_trichotomy (pos b) (pos b1) with h | h | h
  · have := congrFun e b
    rw [rep_eq rfl, rep2_a h] at this; omega
  · have := congrFun e b2
    rw [rep_gt (by omega), rep2_b2 hb rfl] at this; omega
  · have := congrFun e b1
    rw [rep_lt h, rep2_b1 rfl] at this; omega

lemma rep2_param {b1 b2 b1' b2' : α} {v1 v2 v1' v2' : ℕ} (hb : pos b1 < pos b2) (hv1 : v1 < pos b1)
    (hv2 : v2 + 2 ≤ pos b2) (hb' : pos b1' < pos b2') (hv1' : v1' < pos b1') (hv2' : v2' + 2 ≤ pos b2')
    (e : rep2 b1 v1 b2 v2 = rep2 b1' v1' b2' v2') : b1 = b1' ∧ v1 = v1' ∧ b2 = b2' ∧ v2 = v2' := by
  have hb1 : pos b1 = pos b1' := by
    rcases lt_trichotomy (pos b1) (pos b1') with h | h | h
    · have := congrFun e b1
      rw [rep2_b1 rfl, rep2_a h] at this; omega
    · exact h
    · have := congrFun e b1'
      rw [rep2_a h, rep2_b1 rfl] at this; omega
  have hv : v1 = v1' := by
    have := congrFun e b1
    rwa [rep2_b1 rfl, rep2_b1 hb1] at this
  have hb2 : pos b2 = pos b2' := by
    rcases lt_trichotomy (pos b2) (pos b2') with h | h | h
    · have := congrFun e b2
      rw [rep2_b2 hb rfl, rep2_m (by omega) h] at this; omega
    · exact h
    · have := congrFun e b2'
      rw [rep2_m (by omega) h, rep2_b2 hb' rfl] at this; omega
  refine ⟨pos_inj hb1, hv, pos_inj hb2, ?_⟩
  have := congrFun e b2
  rwa [rep2_b2 hb rfl, rep2_b2 hb' hb2] at this

lemma set_eq3 (hsymm : ∀ c c', adj c c' → adj c' c) (hirr : ∀ c, ¬ adj c c)
    (hN : 3 ≤ Fintype.card α) :
    {x : α → ℕ | RGS x ∧ Proper adj x ∧ ∃ c, x c + 3 = Fintype.card α} = col3 '' ↑(dom3 adj) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, mem_coe]
  constructor
  · rintro ⟨hr, hc, c0, h0⟩
    rw [rgs_iff] at hr
    rcases rgs_cases3 x hr c0 h0 with rfl | ⟨a, b, hab, rfl⟩ | ⟨b1, b2, v1, v2, hb, hv1, hv2, rfl⟩
    · exact ⟨Sum.inl none, inl_mem_disjSum.2 (mem_insert_self _ _), rfl⟩
    · refine ⟨Sum.inl (some (a, b)), inl_mem_disjSum.2 (mem_insert_of_mem (mem_map_of_mem _ ?_)), rfl⟩
      simp only [nonEdges, mem_filter, mem_univ, true_and]
      exact ⟨(lt_iff_pos a b).2 hab, (proper_rep adj hsymm hirr a b hab).1 hc⟩
    · obtain ⟨a1, ha1⟩ := pos_surj (α := α) v1 (by have := pos_lt b1; omega)
      have hp := (proper_rep2 adj hsymm hirr hb hv1 hv2 a1 ha1).1 hc
      -- the earlier cell with the value v2
      obtain ⟨w, hw, hwv⟩ : ∃ w : α, pos w < pos b2 ∧ rep2 b1 v1 b2 v2 w = v2 ∧
          (pos w < pos b1 ∨ pos b1 < pos w) := by
        by_cases h : v2 < pos b1
        · obtain ⟨w, hw⟩ := pos_surj (α := α) v2 (by have := pos_lt b1; omega)
          exact ⟨w, by omega, by rw [rep2_a (by omega)]; exact hw, Or.inl (by omega)⟩
        · obtain ⟨w, hw⟩ := pos_surj (α := α) (v2 + 1) (by have := pos_lt b2; omega)
          exact ⟨w, by omega, by rw [rep2_m (by omega) (by omega)]; omega, Or.inr (by omega)⟩
      obtain ⟨hwv, hwr⟩ := hwv
      by_cases hv : v2 = v1
      · subst hv
        refine ⟨Sum.inr (Sum.inl (a1, b1, b2)), inr_mem_disjSum.2 (inl_mem_disjSum.2 ?_),
          by simp only [col3, ha1]⟩
        simp only [indep3, mem_filter, mem_univ, true_and]
        refine ⟨(lt_iff_pos _ _).2 (by omega), (lt_iff_pos _ _).2 hb, hp.1,
          hp.2 a1 (by omega) (by rw [rep2_a (by omega), ha1]), hp.2 b1 hb (rep2_b1 rfl)⟩
      · have hwb1 : w ≠ b1 := fun e => by rw [e] at hwr; omega
        have hwa1 : w ≠ a1 := fun e => by
          rw [e, rep2_a (by omega), ha1] at hwv; exact hv hwv.symm
        have hrep : rep a1 b1 w = v2 := by
          rcases hwr with h | h
          · rw [rep_lt h]; rw [rep2_a h] at hwv; exact hwv
          · rw [rep_gt h]; rw [rep2_m h hw] at hwv; exact hwv
        refine ⟨Sum.inr (Sum.inr ((a1, b1), (w, b2))), inr_mem_disjSum.2 (inr_mem_disjSum.2 ?_),
          by simp only [col3, ha1, hrep]⟩
        simp only [pairs2, mem_filter, mem_univ, true_and]
        exact ⟨(lt_iff_pos _ _).2 (by omega), (lt_iff_pos _ _).2 hw, (lt_iff_pos _ _).2 hb, hwa1, hwb1,
          hp.1, hp.2 w hw hwv⟩
  · rintro ⟨d, hd, rfl⟩
    rcases d with o | t | q
    · rw [dom3, inl_mem_disjSum, mem_insert] at hd
      rcases hd with rfl | hd
      · refine ⟨(rgs_iff _).2 rgs_pos, proper_pos adj hirr, ?_⟩
        obtain ⟨c, hc⟩ := pos_surj (α := α) (Fintype.card α - 3) (by omega)
        exact ⟨c, by simp only [col3, Option.elim]; omega⟩
      · rw [mem_map] at hd
        obtain ⟨⟨a, b⟩, hab, rfl⟩ := hd
        simp only [nonEdges, mem_filter, mem_univ, true_and] at hab
        obtain ⟨hab, hn⟩ := hab
        have hab' : pos a < pos b := (lt_iff_pos a b).1 hab
        refine ⟨(rgs_iff _).2 (rgs_rep a b hab'), (proper_rep adj hsymm hirr a b hab').2 hn, ?_⟩
        obtain ⟨c, hc⟩ := rep_top3 hab' hN
        exact ⟨c, by simp only [col3, Option.elim, Function.Embedding.some_apply]; omega⟩
    · obtain ⟨a, b, c⟩ := t
      rw [dom3, inr_mem_disjSum, inl_mem_disjSum] at hd
      simp only [indep3, mem_filter, mem_univ, true_and] at hd
      obtain ⟨hab, hbc, hnab, hnac, hnbc⟩ := hd
      have hab' := (lt_iff_pos _ _).1 hab
      have hbc' := (lt_iff_pos _ _).1 hbc
      simp only [col3]
      refine ⟨(rgs_iff _).2 (rgs_rep2 hbc' hab' (by omega)),
        (proper_rep2 adj hsymm hirr hbc' hab' (by omega) a rfl).2 ⟨hnab, fun w hw hwv => ?_⟩,
        rep2_top hbc' hab'⟩
      -- the cells before c with the value pos a are a and b
      rcases lt_trichotomy (pos w) (pos b) with h | h | h
      · rw [rep2_a h] at hwv; rw [pos_inj hwv]; exact hnac
      · rw [pos_inj h]; exact hnbc
      · rw [rep2_m h hw] at hwv; omega
    · obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩ := q
      rw [dom3, inr_mem_disjSum, inr_mem_disjSum] at hd
      simp only [pairs2, mem_filter, mem_univ, true_and] at hd
      obtain ⟨h1, h2, hb, hne1, hne2, hn1, hn2⟩ := hd
      have h1' := (lt_iff_pos _ _).1 h1
      have h2' := (lt_iff_pos _ _).1 h2
      have hb' := (lt_iff_pos _ _).1 hb
      have hv2 := rep_a2_le h1' hb' h2' hne2
      simp only [col3]
      refine ⟨(rgs_iff _).2 (rgs_rep2 hb' h1' hv2),
        (proper_rep2 adj hsymm hirr hb' h1' hv2 a1 rfl).2 ⟨hn1, fun w hw hwv => ?_⟩, rep2_top hb' h1'⟩
      -- the only cell before b2 with the value of a2 is a2
      by_contra hn
      have hwa : w ≠ a2 := fun e => by rw [e] at hn; exact hn2 hn
      have hsame : rep2 b1 (pos a1) b2 (rep a1 b1 a2) w = rep2 b1 (pos a1) b2 (rep a1 b1 a2) a2 := by
        rw [hwv, rep2_at_a2 hb' h2' hne2]
      have hne := rep_a2_ne h1' hne1 hne2
      rcases lt_or_gt_of_ne (fun e : pos w = pos a2 => hwa (pos_inj e)) with hlt | hlt
      · rcases rep2_same hb' h1' hv2 w a2 hlt hsame with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact hne2 rfl
        · omega
      · rcases rep2_same hb' h1' hv2 a2 w hlt hsame.symm with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · rw [rep2_b1 rfl] at hwv; exact hne hwv.symm
        · omega

lemma mem_dom3_inl {o : Option (α × α)} :
    Sum.inl o ∈ dom3 adj ↔ o = none ∨ ∃ p : α × α, (p.1 < p.2 ∧ ¬ adj p.1 p.2) ∧ some p = o := by
  rw [dom3, inl_mem_disjSum, mem_insert, mem_map]
  simp only [nonEdges, mem_filter, mem_univ, true_and, Function.Embedding.some_apply]

lemma mem_dom3_t {t : α × α × α} :
    Sum.inr (Sum.inl t) ∈ dom3 adj ↔ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ ¬ adj t.1 t.2.1 ∧
      ¬ adj t.1 t.2.2 ∧ ¬ adj t.2.1 t.2.2 := by
  rw [dom3, inr_mem_disjSum, inl_mem_disjSum]
  simp only [indep3, mem_filter, mem_univ, true_and]

lemma mem_dom3_q {q : (α × α) × (α × α)} :
    Sum.inr (Sum.inr q) ∈ dom3 adj ↔ q.1.1 < q.1.2 ∧ q.2.1 < q.2.2 ∧ q.1.2 < q.2.2 ∧ q.2.1 ≠ q.1.1 ∧
      q.2.1 ≠ q.1.2 ∧ ¬ adj q.1.1 q.1.2 ∧ ¬ adj q.2.1 q.2.2 := by
  rw [dom3, inr_mem_disjSum, inr_mem_disjSum]
  simp only [pairs2, mem_filter, mem_univ, true_and]

lemma injOn3 :
    Set.InjOn col3 (↑(dom3 adj) : Set (Option (α × α) ⊕ (α × α × α) ⊕ ((α × α) × (α × α)))) := by
  intro d hd d' hd' e
  rw [mem_coe] at hd hd'
  rcases d with o | ⟨a, b, c⟩ | ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩ <;>
    rcases d' with o' | ⟨a', b', c'⟩ | ⟨⟨a1', b1'⟩, ⟨a2', b2'⟩⟩ <;>
    simp only [mem_dom3_inl, mem_dom3_t, mem_dom3_q] at hd hd'
  · -- the numbering and one repetition, as for N - 2
    have key : ∀ a b : α, pos a < pos b → rep a b ≠ pos := fun a b hab h => by
      have := congrFun h b
      rw [rep_eq rfl] at this; omega
    rcases hd with rfl | ⟨⟨a, b⟩, ⟨hab, _⟩, rfl⟩ <;> rcases hd' with rfl | ⟨⟨a', b'⟩, ⟨hab', _⟩, rfl⟩
    · rfl
    · exact absurd e.symm (key a' b' ((lt_iff_pos a' b').1 hab'))
    · exact absurd e (key a b ((lt_iff_pos a b).1 hab))
    · simp only [col3, Option.elim] at e
      have h1 : pos a < pos b := (lt_iff_pos a b).1 hab
      have h2 : pos a' < pos b' := (lt_iff_pos a' b').1 hab'
      have hb : pos b = pos b' := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hl | hl
        · have := congrFun e b
          rw [rep_eq rfl, rep_lt hl] at this; omega
        · have := congrFun e b'
          rw [rep_eq rfl, rep_lt hl] at this; omega
      have hbb := pos_inj hb
      subst hbb
      have := congrFun e b
      rw [rep_eq rfl, rep_eq rfl] at this
      rw [pos_inj this]
  · obtain ⟨hab', hbc', -⟩ := hd'
    have h1 := (lt_iff_pos _ _).1 hab'
    have h2 := (lt_iff_pos _ _).1 hbc'
    rcases hd with rfl | ⟨⟨a, b⟩, ⟨hab, _⟩, rfl⟩
    · exact absurd e (pos_ne_rep2 h1)
    · exact absurd e (rep_ne_rep2 ((lt_iff_pos a b).1 hab) h2 h1 (by simp only; omega))
  · obtain ⟨h1, h2, hb, -, hne2, -⟩ := hd'
    have h1' := (lt_iff_pos _ _).1 h1
    have h2' := (lt_iff_pos _ _).1 h2
    have hb' := (lt_iff_pos _ _).1 hb
    rcases hd with rfl | ⟨⟨a, b⟩, ⟨hab, _⟩, rfl⟩
    · exact absurd e (pos_ne_rep2 h1')
    · exact absurd e (rep_ne_rep2 ((lt_iff_pos a b).1 hab) hb' h1' (rep_a2_le h1' hb' h2' hne2))
  · obtain ⟨hab, hbc, -⟩ := hd
    have h1 := (lt_iff_pos _ _).1 hab
    have h2 := (lt_iff_pos _ _).1 hbc
    rcases hd' with rfl | ⟨⟨a', b'⟩, ⟨hab', _⟩, rfl⟩
    · exact absurd e.symm (pos_ne_rep2 h1)
    · exact absurd e.symm (rep_ne_rep2 ((lt_iff_pos a' b').1 hab') h2 h1 (by simp only; omega))
  · obtain ⟨hab, hbc, -⟩ := hd
    obtain ⟨hab', hbc', -⟩ := hd'
    have h1 := (lt_iff_pos _ _).1 hab
    have h2 := (lt_iff_pos _ _).1 hbc
    have h1' := (lt_iff_pos _ _).1 hab'
    have h2' := (lt_iff_pos _ _).1 hbc'
    simp only [col3] at e
    obtain ⟨rfl, hv, rfl, -⟩ := rep2_param h2 h1 (by omega) h2' h1' (by omega) e
    rw [pos_inj hv]
  · obtain ⟨hab, hbc, -⟩ := hd
    obtain ⟨g1, g2, gb, gne1, gne2, -⟩ := hd'
    have h1 := (lt_iff_pos _ _).1 hab
    have h2 := (lt_iff_pos _ _).1 hbc
    have g1' := (lt_iff_pos _ _).1 g1
    have g2' := (lt_iff_pos _ _).1 g2
    have gb' := (lt_iff_pos _ _).1 gb
    simp only [col3] at e
    obtain ⟨rfl, hv, rfl, hv2⟩ := rep2_param h2 h1 (by omega) gb' g1' (rep_a2_le g1' gb' g2' gne2) e
    rw [pos_inj hv] at hv2
    exact absurd hv2.symm (rep_a2_ne g1' gne1 gne2)
  · obtain ⟨h1, h2, hb, -, hne2, -⟩ := hd
    have h1' := (lt_iff_pos _ _).1 h1
    have h2' := (lt_iff_pos _ _).1 h2
    have hb' := (lt_iff_pos _ _).1 hb
    rcases hd' with rfl | ⟨⟨a, b⟩, ⟨hab, _⟩, rfl⟩
    · exact absurd e.symm (pos_ne_rep2 h1')
    · exact absurd e.symm (rep_ne_rep2 ((lt_iff_pos a b).1 hab) hb' h1' (rep_a2_le h1' hb' h2' hne2))
  · obtain ⟨g1, g2, gb, gne1, gne2, -⟩ := hd
    obtain ⟨hab, hbc, -⟩ := hd'
    have h1 := (lt_iff_pos _ _).1 hab
    have h2 := (lt_iff_pos _ _).1 hbc
    have g1' := (lt_iff_pos _ _).1 g1
    have g2' := (lt_iff_pos _ _).1 g2
    have gb' := (lt_iff_pos _ _).1 gb
    simp only [col3] at e
    obtain ⟨rfl, hv, rfl, hv2⟩ := rep2_param gb' g1' (rep_a2_le g1' gb' g2' gne2) h2 h1 (by omega) e
    rw [← pos_inj hv] at hv2
    exact absurd hv2 (rep_a2_ne g1' gne1 gne2)
  · obtain ⟨g1, g2, gb, gne1, gne2, -⟩ := hd
    obtain ⟨g1', g2', gb', gne1', gne2', -⟩ := hd'
    have p1 := (lt_iff_pos _ _).1 g1
    have p2 := (lt_iff_pos _ _).1 g2
    have pb := (lt_iff_pos _ _).1 gb
    have p1' := (lt_iff_pos _ _).1 g1'
    have p2' := (lt_iff_pos _ _).1 g2'
    have pb' := (lt_iff_pos _ _).1 gb'
    simp only [col3] at e
    obtain ⟨rfl, hv, rfl, hv2⟩ := rep2_param pb p1 (rep_a2_le p1 pb p2 gne2) pb' p1'
      (rep_a2_le p1' pb' p2' gne2') e
    obtain rfl := pos_inj hv
    by_contra hne
    have hne' : a2 ≠ a2' := fun h => hne (by rw [h])
    rcases rep_inj a1 b1 p1 a2 a2' hv2 hne' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact gne1 rfl
    · exact gne2 rfl

/-- **The coloring theorem, N - 3.** For N ≥ 3 cells, the proper colorings with values introduced
in order that contain the value N - 3 number 1 + (the pairs of cells that are not neighbors) +
(the triples of cells, no two neighbors) + (the pairs of disjoint pairs of cells that are not
neighbors). -/
theorem count_N3 (hsymm : ∀ c c', adj c c' → adj c' c) (hirr : ∀ c, ¬ adj c c)
    (hN : 3 ≤ Fintype.card α) :
    {x : α → ℕ | RGS x ∧ Proper adj x ∧ ∃ c, x c + 3 = Fintype.card α}.ncard =
      (nonEdges adj).card + 1 + (indep3 adj).card + (pairs2 adj).card := by
  rw [set_eq3 adj hsymm hirr hN, (injOn3 adj).ncard_image, Set.ncard_coe_finset, dom3, card_disjSum,
    card_disjSum, card_insert_of_notMem (by simp), card_map]
  ring

/-! ### Triples and pairs of pairs from edges and triangles -/

lemma mem_nonEdges (p : α × α) : p ∈ nonEdges adj ↔ p.1 < p.2 ∧ ¬ adj p.1 p.2 := by
  simp only [nonEdges, mem_filter, mem_univ, true_and]

/-- The sorted triples of cells. -/
noncomputable def triples : Finset (α × α × α) :=
  (univ : Finset (α × α × α)).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)

lemma mem_triples (t : α × α × α) :
    t ∈ (triples : Finset (α × α × α)) ↔ t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by
  simp only [triples, mem_filter, mem_univ, true_and]

/-- The triangles: the sorted triples of pairwise neighbors. -/
noncomputable def triangles : Finset (α × α × α) :=
  triples.filter (fun t => adj t.1 t.2.1 ∧ adj t.1 t.2.2 ∧ adj t.2.1 t.2.2)

lemma mem_triangles (t : α × α × α) : t ∈ triangles adj ↔
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ adj t.1 t.2.1 ∧ adj t.1 t.2.2 ∧ adj t.2.1 t.2.2 := by
  rw [triangles, mem_filter, mem_triples, and_assoc]

/-- The order of pairs of cells by their larger cell, then by their smaller cell. -/
abbrev plt (e f : α × α) : Prop := e.2 < f.2 ∨ (e.2 = f.2 ∧ e.1 < f.1)

lemma plt_asymm {e f : α × α} (h : plt e f) (h' : plt f e) : False := by
  rcases h with h | ⟨h1, h2⟩ <;> rcases h' with h' | ⟨h1', h2'⟩
  · exact lt_asymm h h'
  · rw [h1'] at h; exact lt_irrefl _ h
  · rw [h1] at h'; exact lt_irrefl _ h'
  · exact lt_asymm h2 h2'

lemma plt_total {e f : α × α} (h : e ≠ f) : plt e f ∨ plt f e := by
  rcases lt_trichotomy e.2 f.2 with h2 | h2 | h2
  · exact Or.inl (Or.inl h2)
  · rcases lt_trichotomy e.1 f.1 with h1 | h1 | h1
    · exact Or.inl (Or.inr ⟨h2, h1⟩)
    · exact absurd (Prod.ext h1 h2) h
    · exact Or.inr (Or.inr ⟨h2.symm, h1⟩)
  · exact Or.inr (Or.inl h2)

/-- Each two-element subset of s, listed once with its elements in `plt` order. -/
lemma card_plt (s : Finset (α × α)) :
    2 * ((s ×ˢ s).filter (fun q => plt q.1 q.2)).card = s.card * (s.card - 1) := by
  have h : ((s ×ˢ s).filter (fun q => plt q.1 q.2)).card = (s.powersetCard 2).card := by
    apply card_nbij (fun q => ({q.1, q.2} : Finset (α × α)))
    · intro q hq
      rw [mem_coe, mem_filter, mem_product] at hq
      rw [mem_coe, mem_powersetCard]
      refine ⟨insert_subset hq.1.1 (singleton_subset_iff.2 hq.1.2), card_pair_eq_two_iff.2 fun e => ?_⟩
      have hp := hq.2
      rw [e] at hp
      exact plt_asymm hp hp
    · intro q hq q' hq' e
      rw [mem_coe, mem_filter] at hq hq'
      have e' : ({q.1, q.2} : Finset (α × α)) = {q'.1, q'.2} := e
      have h1 : q.1 ∈ ({q'.1, q'.2} : Finset (α × α)) := by rw [← e']; exact mem_insert_self _ _
      have h2 : q.2 ∈ ({q'.1, q'.2} : Finset (α × α)) := by
        rw [← e']; exact mem_insert_of_mem (mem_singleton_self _)
      rw [mem_insert, mem_singleton] at h1 h2
      have hp := hq.2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at hp
      · exact (plt_asymm hp hp).elim
      · exact Prod.ext h1 h2
      · exact (plt_asymm hp hq'.2).elim
      · exact (plt_asymm hp hp).elim
    · intro t ht
      rw [mem_coe, mem_powersetCard] at ht
      obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 ht.2
      have hx : x ∈ s := ht.1 (mem_insert_self _ _)
      have hy : y ∈ s := ht.1 (mem_insert_of_mem (mem_singleton_self _))
      rcases plt_total hxy with h | h
      · exact ⟨(x, y), by rw [mem_coe, mem_filter, mem_product]; exact ⟨⟨hx, hy⟩, h⟩, rfl⟩
      · exact ⟨(y, x), by rw [mem_coe, mem_filter, mem_product]; exact ⟨⟨hy, hx⟩, h⟩, pair_comm _ _⟩
  rw [h, card_powersetCard, Nat.choose_two_right,
    Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd]

/-- The pairs e, f of non-edges with e before f in `plt` order. -/
noncomputable def nePairs : Finset ((α × α) × (α × α)) :=
  (nonEdges adj ×ˢ nonEdges adj).filter (fun q => plt q.1 q.2)

lemma mem_nePairs (q : (α × α) × (α × α)) : q ∈ nePairs adj ↔
    (q.1.1 < q.1.2 ∧ ¬ adj q.1.1 q.1.2) ∧ (q.2.1 < q.2.2 ∧ ¬ adj q.2.1 q.2.2) ∧ plt q.1 q.2 := by
  rw [nePairs, mem_filter, mem_product, mem_nonEdges, mem_nonEdges, and_assoc]

/-- Two distinct non-edges are disjoint (`pairs2`) or share a cell, and then they are two of the
three pairs of a sorted triple. -/
lemma card_nePairs :
    (nePairs adj).card = (pairs2 adj).card +
      (triples.filter (fun t => ¬ adj t.1 t.2.1 ∧ ¬ adj t.1 t.2.2)).card +
      (triples.filter (fun t => ¬ adj t.1 t.2.1 ∧ ¬ adj t.2.1 t.2.2)).card +
      (triples.filter (fun t => ¬ adj t.1 t.2.2 ∧ ¬ adj t.2.1 t.2.2)).card := by
  rw [← card_filter_add_card_filter_not (s := nePairs adj) (fun q => q.1.2 = q.2.2),
    ← card_filter_add_card_filter_not (s := (nePairs adj).filter (fun q => ¬ q.1.2 = q.2.2))
      (fun q => q.2.1 = q.1.1),
    ← card_filter_add_card_filter_not
      (s := ((nePairs adj).filter (fun q => ¬ q.1.2 = q.2.2)).filter (fun q => ¬ q.2.1 = q.1.1))
      (fun q => q.2.1 = q.1.2)]
  -- (a, c), (b, c)
  have e1 : ((nePairs adj).filter (fun q => q.1.2 = q.2.2)).card =
      (triples.filter (fun t => ¬ adj t.1 t.2.2 ∧ ¬ adj t.2.1 t.2.2)).card := by
    apply card_nbij' (fun q => (q.1.1, q.2.1, q.2.2)) (fun t => ((t.1, t.2.2), (t.2.1, t.2.2)))
    · rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩ h
      simp only [mem_coe, mem_filter, mem_nePairs] at h
      rw [mem_coe, mem_filter, mem_triples]
      obtain ⟨⟨⟨hac, nac⟩, ⟨hbd, nbd⟩, hp⟩, rfl⟩ := h
      rcases hp with hp | ⟨-, hab⟩
      · exact absurd hp (lt_irrefl _)
      · exact ⟨⟨hab, hbd⟩, nac, nbd⟩
    · rintro ⟨a, b, c⟩ h
      simp only [mem_coe, mem_filter, mem_triples] at h
      rw [mem_coe, mem_filter, mem_nePairs]
      obtain ⟨⟨hab, hbc⟩, nac, nbc⟩ := h
      exact ⟨⟨⟨lt_trans hab hbc, nac⟩, ⟨hbc, nbc⟩, Or.inr ⟨rfl, hab⟩⟩, rfl⟩
    · rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩ h
      simp only [mem_coe, mem_filter] at h
      obtain ⟨-, rfl⟩ := h
      rfl
    · rintro ⟨a, b, c⟩ -
      rfl
  -- (a, b), (a, c)
  have e2 : (((nePairs adj).filter (fun q => ¬ q.1.2 = q.2.2)).filter (fun q => q.2.1 = q.1.1)).card =
      (triples.filter (fun t => ¬ adj t.1 t.2.1 ∧ ¬ adj t.1 t.2.2)).card := by
    apply card_nbij' (fun q => (q.1.1, q.1.2, q.2.2)) (fun t => ((t.1, t.2.1), (t.1, t.2.2)))
    · rintro ⟨⟨a, b⟩, ⟨a', c⟩⟩ h
      simp only [mem_coe, mem_filter, mem_nePairs] at h
      rw [mem_coe, mem_filter, mem_triples]
      obtain ⟨⟨⟨⟨hab, nab⟩, ⟨hac, nac⟩, hp⟩, hbc⟩, rfl⟩ := h
      rcases hp with hp | ⟨hp, -⟩
      · exact ⟨⟨hab, hp⟩, nab, nac⟩
      · exact absurd hp hbc
    · rintro ⟨a, b, c⟩ h
      simp only [mem_coe, mem_filter, mem_triples] at h
      rw [mem_coe, mem_filter, mem_filter, mem_nePairs]
      obtain ⟨⟨hab, hbc⟩, nab, nac⟩ := h
      exact ⟨⟨⟨⟨hab, nab⟩, ⟨lt_trans hab hbc, nac⟩, Or.inl hbc⟩, hbc.ne⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨a', c⟩⟩ h
      simp only [mem_coe, mem_filter] at h
      obtain ⟨-, rfl⟩ := h
      rfl
    · rintro ⟨a, b, c⟩ -
      rfl
  -- (a, b), (b, c)
  have e3 : ((((nePairs adj).filter (fun q => ¬ q.1.2 = q.2.2)).filter (fun q => ¬ q.2.1 = q.1.1)).filter
      (fun q => q.2.1 = q.1.2)).card =
      (triples.filter (fun t => ¬ adj t.1 t.2.1 ∧ ¬ adj t.2.1 t.2.2)).card := by
    apply card_nbij' (fun q => (q.1.1, q.1.2, q.2.2)) (fun t => ((t.1, t.2.1), (t.2.1, t.2.2)))
    · rintro ⟨⟨a, b⟩, ⟨b', c⟩⟩ h
      simp only [mem_coe, mem_filter, mem_nePairs] at h
      rw [mem_coe, mem_filter, mem_triples]
      obtain ⟨⟨⟨⟨⟨hab, nab⟩, ⟨hbc, nbc⟩, -⟩, -⟩, -⟩, rfl⟩ := h
      exact ⟨⟨hab, hbc⟩, nab, nbc⟩
    · rintro ⟨a, b, c⟩ h
      simp only [mem_coe, mem_filter, mem_triples] at h
      rw [mem_coe, mem_filter, mem_filter, mem_filter, mem_nePairs]
      obtain ⟨⟨hab, hbc⟩, nab, nbc⟩ := h
      exact ⟨⟨⟨⟨⟨hab, nab⟩, ⟨hbc, nbc⟩, Or.inl hbc⟩, hbc.ne⟩, hab.ne'⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨b', c⟩⟩ h
      simp only [mem_coe, mem_filter] at h
      obtain ⟨-, rfl⟩ := h
      rfl
    · rintro ⟨a, b, c⟩ -
      rfl
  -- disjoint
  have e4 : ((((nePairs adj).filter (fun q => ¬ q.1.2 = q.2.2)).filter (fun q => ¬ q.2.1 = q.1.1)).filter
      (fun q => ¬ q.2.1 = q.1.2)) = pairs2 adj := by
    ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp only [mem_filter, mem_nePairs, pairs2, mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨⟨⟨hab, nab⟩, ⟨hcd, ncd⟩, hp⟩, hbd⟩, hca⟩, hcb⟩
      rcases hp with hp | ⟨hp, -⟩
      · exact ⟨hab, hcd, hp, hca, hcb, nab, ncd⟩
      · exact absurd hp hbd
    · rintro ⟨hab, hcd, hbd, hca, hcb, nab, ncd⟩
      exact ⟨⟨⟨⟨⟨hab, nab⟩, ⟨hcd, ncd⟩, Or.inl hbd⟩, hbd.ne⟩, hca⟩, hcb⟩
  rw [e1, e2, e3, e4]
  ring

/-- Per sorted triple with x, y, z its pairs that are not neighbors: xy + xz + yz + 1 =
x + y + z + xyz + (1 - x)(1 - y)(1 - z). -/
lemma card_triples_split :
    (triples.filter (fun t => ¬ adj t.1 t.2.1 ∧ ¬ adj t.1 t.2.2)).card +
      (triples.filter (fun t => ¬ adj t.1 t.2.1 ∧ ¬ adj t.2.1 t.2.2)).card +
      (triples.filter (fun t => ¬ adj t.1 t.2.2 ∧ ¬ adj t.2.1 t.2.2)).card +
      (triples : Finset (α × α × α)).card =
    (triples.filter (fun t => ¬ adj t.1 t.2.1)).card + (triples.filter (fun t => ¬ adj t.1 t.2.2)).card +
      (triples.filter (fun t => ¬ adj t.2.1 t.2.2)).card + (indep3 adj).card + (triangles adj).card := by
  have hI : indep3 adj =
      triples.filter (fun t => ¬ adj t.1 t.2.1 ∧ ¬ adj t.1 t.2.2 ∧ ¬ adj t.2.1 t.2.2) := by
    ext t
    simp only [indep3, triples, mem_filter, mem_univ, true_and, and_assoc]
  rw [hI, triangles, card_eq_sum_ones (triples : Finset (α × α × α))]
  simp only [card_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  by_cases h1 : adj t.1 t.2.1 <;> by_cases h2 : adj t.1 t.2.2 <;> by_cases h3 : adj t.2.1 t.2.2 <;>
    simp [h1, h2, h3]

/-- Each pair a < b of cells that are not neighbors lies in N - 2 sorted triples: with a third cell
after b, between a and b, or before a. -/
lemma card_triples_ne :
    (triples.filter (fun t => ¬ adj t.1 t.2.1)).card + (triples.filter (fun t => ¬ adj t.1 t.2.2)).card +
      (triples.filter (fun t => ¬ adj t.2.1 t.2.2)).card =
      (nonEdges adj).card * (Fintype.card α - 2) := by
  set D := ((nonEdges adj) ×ˢ (univ : Finset α)).filter (fun q => q.2 ≠ q.1.1 ∧ q.2 ≠ q.1.2) with hD
  have hcard : D.card = (nonEdges adj).card * (Fintype.card α - 2) := by
    rw [hD, card_filter, sum_product]
    apply sum_const_nat
    intro e he
    rw [mem_nonEdges] at he
    have hf : (univ : Finset α).filter (fun c => c ≠ e.1 ∧ c ≠ e.2) = (univ.erase e.1).erase e.2 := by
      ext c
      simp only [mem_filter, mem_erase, mem_univ, true_and, and_true]
      exact and_comm
    rw [sum_boole, Nat.cast_id, hf, card_erase_of_mem, card_erase_of_mem (mem_univ _), card_univ]
    · omega
    · rw [mem_erase]; exact ⟨he.1.ne', mem_univ _⟩
  rw [← hcard, ← card_filter_add_card_filter_not (s := D) (fun q => q.1.2 < q.2),
    ← card_filter_add_card_filter_not (s := D.filter (fun q => ¬ q.1.2 < q.2)) (fun q => q.1.1 < q.2)]
  have b1 : (D.filter (fun q => q.1.2 < q.2)).card = (triples.filter (fun t => ¬ adj t.1 t.2.1)).card := by
    apply card_nbij' (fun q => (q.1.1, q.1.2, q.2)) (fun t => ((t.1, t.2.1), t.2.2))
    · rintro ⟨⟨a, b⟩, c⟩ h
      simp only [mem_coe, mem_filter, hD, mem_product, mem_nonEdges, mem_univ, and_true] at h
      rw [mem_coe, mem_filter, mem_triples]
      exact ⟨⟨h.1.1.1, h.2⟩, h.1.1.2⟩
    · rintro ⟨a, b, c⟩ h
      simp only [mem_coe, mem_filter, mem_triples] at h
      rw [mem_coe, mem_filter, hD, mem_filter, mem_product, mem_nonEdges]
      exact ⟨⟨⟨⟨h.1.1, h.2⟩, mem_univ _⟩, (lt_trans h.1.1 h.1.2).ne', h.1.2.ne'⟩, h.1.2⟩
    · intro q _; rfl
    · intro t _; rfl
  have b2 : ((D.filter (fun q => ¬ q.1.2 < q.2)).filter (fun q => q.1.1 < q.2)).card =
      (triples.filter (fun t => ¬ adj t.1 t.2.2)).card := by
    apply card_nbij' (fun q => (q.1.1, q.2, q.1.2)) (fun t => ((t.1, t.2.2), t.2.1))
    · rintro ⟨⟨a, c⟩, b⟩ h
      simp only [mem_coe, mem_filter, hD, mem_product, mem_nonEdges, mem_univ, and_true] at h
      rw [mem_coe, mem_filter, mem_triples]
      exact ⟨⟨h.2, lt_of_le_of_ne (not_lt.1 h.1.2) h.1.1.2.2⟩, h.1.1.1.2⟩
    · rintro ⟨a, b, c⟩ h
      simp only [mem_coe, mem_filter, mem_triples] at h
      rw [mem_coe, mem_filter, mem_filter, hD, mem_filter, mem_product, mem_nonEdges]
      exact ⟨⟨⟨⟨⟨lt_trans h.1.1 h.1.2, h.2⟩, mem_univ _⟩, h.1.1.ne', h.1.2.ne⟩, not_lt.2 h.1.2.le⟩, h.1.1⟩
    · intro q _; rfl
    · intro t _; rfl
  have b3 : ((D.filter (fun q => ¬ q.1.2 < q.2)).filter (fun q => ¬ q.1.1 < q.2)).card =
      (triples.filter (fun t => ¬ adj t.2.1 t.2.2)).card := by
    apply card_nbij' (fun q => (q.2, q.1.1, q.1.2)) (fun t => ((t.2.1, t.2.2), t.1))
    · rintro ⟨⟨b, c⟩, a⟩ h
      simp only [mem_coe, mem_filter, hD, mem_product, mem_nonEdges, mem_univ, and_true] at h
      rw [mem_coe, mem_filter, mem_triples]
      exact ⟨⟨lt_of_le_of_ne (not_lt.1 h.2) h.1.1.2.1, h.1.1.1.1⟩, h.1.1.1.2⟩
    · rintro ⟨a, b, c⟩ h
      simp only [mem_coe, mem_filter, mem_triples] at h
      rw [mem_coe, mem_filter, mem_filter, hD, mem_filter, mem_product, mem_nonEdges]
      exact ⟨⟨⟨⟨⟨h.1.2, h.2⟩, mem_univ _⟩, h.1.1.ne, (lt_trans h.1.1 h.1.2).ne⟩,
        not_lt.2 (lt_trans h.1.1 h.1.2).le⟩, not_lt.2 h.1.1.le⟩
    · intro q _; rfl
    · intro t _; rfl
  rw [b1, b2, b3]
  ring

omit [DecidableRel adj] in
/-- The sorted triples: 6 T = N (N - 1) (N - 2), from `card_triples_ne` with no neighbors. -/
lemma card_triples :
    6 * (triples : Finset (α × α × α)).card =
      Fintype.card α * (Fintype.card α - 1) * (Fintype.card α - 2) := by
  have h := card_triples_ne (α := α) (fun _ _ => False)
  have hB : (triples : Finset (α × α × α)).filter (fun _ => ¬ False) = triples :=
    filter_true_of_mem (fun _ _ => not_false)
  have hL : (nonEdges (α := α) (fun _ _ => False)).card =
      ((univ : Finset (α × α)).filter (fun p => p.1 < p.2)).card := by
    unfold nonEdges
    congr 1
    ext p
    simp
  rw [hB, hL] at h
  have h2 := card_lt_pairs (α := α)
  calc 6 * (triples : Finset (α × α × α)).card
      = 2 * ((triples : Finset (α × α × α)).card + (triples : Finset (α × α × α)).card +
          (triples : Finset (α × α × α)).card) := by ring
    _ = 2 * ((univ : Finset (α × α)).filter (fun p => p.1 < p.2)).card * (Fintype.card α - 2) := by
          rw [h]; ring
    _ = _ := by rw [h2]

lemma choose_three_mul (m : ℕ) : m.choose 3 * 6 = m * (m - 1) * (m - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.succ_eq_add_one] at h
  rw [show m - 0 = m from rfl] at h
  calc m.choose 3 * 6 = (0 + 1) * (1 + 1) * (2 + 1) * m.choose 3 := by ring
    _ = _ := by rw [← h]; ring

/-- **The coloring theorem, N - 3, by edges and triangles.** For N ≥ 3 cells with P pairs that
are not neighbors and T triangles of neighbors, the proper colorings with values introduced in
order that contain N - 3 number 1 + P + C(P, 2) + C(N, 3) - P (N - 2) - T. -/
theorem count_N3_tri (hsymm : ∀ c c', adj c c' → adj c' c) (hirr : ∀ c, ¬ adj c c)
    (hN : 3 ≤ Fintype.card α) :
    {x : α → ℕ | RGS x ∧ Proper adj x ∧ ∃ c, x c + 3 = Fintype.card α}.ncard +
        (nonEdges adj).card * (Fintype.card α - 2) + (triangles adj).card =
      1 + (nonEdges adj).card + (nonEdges adj).card.choose 2 + (Fintype.card α).choose 3 := by
  have h1 := count_N3 adj hsymm hirr hN
  have h2 : 2 * (nePairs adj).card = (nonEdges adj).card * ((nonEdges adj).card - 1) :=
    card_plt (nonEdges adj)
  have h3 := card_nePairs adj
  have h4 := card_triples_split adj
  have h5 := card_triples_ne adj
  have h6 := card_triples (α := α)
  have c2 : (nonEdges adj).card.choose 2 * 2 = (nonEdges adj).card * ((nonEdges adj).card - 1) := by
    rw [Nat.choose_two_right]; exact Nat.div_mul_cancel (Nat.even_mul_pred_self _).two_dvd
  have c3 := choose_three_mul (Fintype.card α)
  omega

end Adj3

end Generic

/-! ## The lower triangular array in row major order -/

instance {n : ℕ} : Fintype (Cell n) := by unfold Cell; infer_instance

instance {n : ℕ} : DecidableEq (Cell n) := by unfold Cell; infer_instance

/-- The triangular numbers. -/
def tri : ℕ → ℕ
  | 0 => 0
  | k + 1 => tri k + k + 1

lemma tri_succ (k : ℕ) : tri (k + 1) = tri k + k + 1 := rfl

lemma two_mul_tri (k : ℕ) : 2 * tri k = k * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [tri_succ]; nlinarith [ih]

lemma tri_mono {i i' : ℕ} (h : i ≤ i') : tri i ≤ tri i' := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => rw [tri_succ]; omega

lemma tri_add_lt {i i' : ℕ} (h : i < i') : tri i + i < tri i' := by
  have := tri_mono (Nat.succ_le_of_lt h)
  rw [Nat.succ_eq_add_one, tri_succ] at this
  omega

/-- The position of a cell in row major order. -/
def rank {n : ℕ} (c : Cell n) : ℕ := tri c.1.1.val + c.1.2.val

lemma rank_lt {n : ℕ} (c : Cell n) : rank c < tri n := by
  have h1 : c.1.2.val ≤ c.1.1.val := c.2
  have h2 : tri (c.1.1.val + 1) ≤ tri n := tri_mono c.1.1.isLt
  rw [tri_succ] at h2
  unfold rank
  omega

lemma lex_iff_rank {n : ℕ} (c c' : Cell n) :
    (c.1.1 < c'.1.1 ∨ (c.1.1 = c'.1.1 ∧ c.1.2 < c'.1.2)) ↔ rank c < rank c' := by
  have hc : c.1.2.val ≤ c.1.1.val := c.2
  have hc' : c'.1.2.val ≤ c'.1.1.val := c'.2
  simp only [Fin.lt_def, Fin.ext_iff]
  unfold rank
  constructor
  · rintro (h | ⟨h, h'⟩)
    · have := tri_add_lt h; omega
    · rw [h]; omega
  · intro h
    rcases lt_trichotomy c.1.1.val c'.1.1.val with h1 | h1 | h1
    · exact Or.inl h1
    · right; refine ⟨h1, ?_⟩; rw [h1] at h; omega
    · have := tri_add_lt h1; omega

lemma rank_inj {n : ℕ} : Function.Injective (@rank n) := by
  intro c c' h
  rcases lt_trichotomy c.1.1.val c'.1.1.val with h1 | h1 | h1
  · have := (lex_iff_rank c c').1 (Or.inl h1); omega
  · rcases lt_trichotomy c.1.2.val c'.1.2.val with h2 | h2 | h2
    · have := (lex_iff_rank c c').1 (Or.inr ⟨Fin.ext h1, h2⟩); omega
    · exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))
    · have := (lex_iff_rank c' c).1 (Or.inr ⟨Fin.ext h1.symm, h2⟩); omega
  · have := (lex_iff_rank c' c).1 (Or.inl h1); omega

lemma rank_surj (n k : ℕ) (hk : k < tri n) : ∃ c : Cell n, rank c = k := by
  have hex : ∃ i, k < tri (i + 1) := ⟨n, lt_of_lt_of_le hk (tri_mono (Nat.le_succ n))⟩
  have hi : k < tri (Nat.find hex + 1) := Nat.find_spec hex
  have hlo : tri (Nat.find hex) ≤ k := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h]; exact Nat.zero_le _
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
      omega
  have hin : Nat.find hex < n := by
    by_contra h
    have := tri_mono (not_lt.mp h)
    omega
  rw [tri_succ] at hi
  exact ⟨⟨(⟨Nat.find hex, hin⟩, ⟨k - tri (Nat.find hex), by omega⟩), Fin.mk_le_mk.mpr (by omega)⟩,
    by show tri (Nat.find hex) + (k - tri (Nat.find hex)) = k; omega⟩

/-- Row major order on the cells. -/
instance {n : ℕ} : LinearOrder (Cell n) := LinearOrder.lift' rank rank_inj

lemma cell_lt_iff {n : ℕ} (c c' : Cell n) : c < c' ↔ rank c < rank c' := Iff.rfl

lemma card_cell (n : ℕ) : Fintype.card (Cell n) = tri n := by
  rw [← card_univ, ← card_range (tri n)]
  apply card_nbij rank
  · intro c _; simp only [coe_range, Set.mem_Iio]; exact rank_lt c
  · intro c _ c' _ h; exact rank_inj h
  · intro k hk
    simp only [coe_range, Set.mem_Iio] at hk
    obtain ⟨c, hc⟩ := rank_surj n k hk
    exact ⟨c, by simp, hc⟩

/-- The statement of Hardin's entries in this family, for a neighbor relation on the cells:
row major order written out, and the value n(n+1)/2 - k computed in the integers. -/
lemma hardin_eq {n : ℕ} (k : ℕ) (Nbr : Cell n → Cell n → Prop) :
    {x : Cell n → ℕ | (∀ c : Cell n, ∀ u < x c, ∃ c' : Cell n,
        (c'.1.1 < c.1.1 ∨ (c'.1.1 = c.1.1 ∧ c'.1.2 < c.1.2)) ∧ x c' = u) ∧
      (∀ c c' : Cell n, Nbr c c' → x c ≠ x c') ∧ ∃ c, (x c : ℤ) = (n : ℤ) * (n + 1) / 2 - k} =
    {x : Cell n → ℕ | RGS x ∧ Proper Nbr x ∧ ∃ c, x c + k = Fintype.card (Cell n)} := by
  have htri : ((n : ℤ) * (n + 1) / 2) = (tri n : ℤ) := by
    have h : ((n : ℤ) * (n + 1)) = 2 * (tri n : ℤ) := by exact_mod_cast (two_mul_tri n).symm
    rw [h, Int.mul_ediv_cancel_left _ (by norm_num)]
  ext x
  simp only [Set.mem_setOf_eq, RGS, Proper, lex_iff_rank, cell_lt_iff, htri, card_cell]
  refine and_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun c => ?_))
  omega

/-! ## Counting the pairs of neighbors by their offsets -/

/-- The cells as pairs (row, column) of naturals. -/
def Tri (n : ℕ) : Finset (ℕ × ℕ) := (range n ×ˢ range n).filter (fun p => p.2 ≤ p.1)

lemma mem_Tri {n : ℕ} {p : ℕ × ℕ} : p ∈ Tri n ↔ p.2 ≤ p.1 ∧ p.1 < n := by
  unfold Tri; simp only [mem_filter, mem_product, mem_range]; omega

lemma card_Tri (k : ℕ) : (Tri k).card = tri k := by
  induction k with
  | zero => simp [Tri, tri]
  | succ k ih =>
    have e : Tri (k + 1) = Tri k ∪ (range (k + 1)).image (fun j => (k, j)) := by
      ext ⟨i, j⟩
      simp only [mem_union, mem_image, mem_range, Prod.mk.injEq, mem_Tri]
      constructor
      · intro h
        by_cases hi : i < k
        · exact Or.inl ⟨h.1, hi⟩
        · exact Or.inr ⟨j, by omega, by omega, rfl⟩
      · rintro (h | ⟨j', hj', h1, h2⟩) <;> omega
    rw [e, card_union_of_disjoint, ih, card_image_of_injective _ (fun _ _ h => by simpa using h),
      card_range]
    · rfl
    · rw [disjoint_left]
      rintro ⟨i, j⟩ h1 h2
      simp only [mem_image, mem_range, Prod.mk.injEq, mem_Tri] at h1 h2
      omega

/-- The pairs of cells whose second cell is the first moved by (di, dj): a triangle with
n - max di dj rows. -/
lemma card_shift_pos (n di dj : ℕ) :
    ((Tri n ×ˢ Tri n).filter (fun pq : (ℕ × ℕ) × (ℕ × ℕ) =>
      pq.2.1 = pq.1.1 + di ∧ pq.2.2 = pq.1.2 + dj)).card = tri (n - max di dj) := by
  rw [← card_Tri]
  apply card_nbij' (fun pq => (pq.1.1 - (max di dj - di), pq.1.2))
    (fun p => ((p.1 + (max di dj - di), p.2), (p.1 + max di dj, p.2 + dj)))
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true] at h ⊢
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true] at h ⊢
    omega
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true]
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true]
    omega

/-- The pairs of cells whose second cell is the first moved by (di, -dj): a triangle with
n - (di + dj) rows. -/
lemma card_shift_neg (n di dj : ℕ) :
    ((Tri n ×ˢ Tri n).filter (fun pq : (ℕ × ℕ) × (ℕ × ℕ) =>
      pq.2.1 = pq.1.1 + di ∧ pq.2.2 + dj = pq.1.2)).card = tri (n - (di + dj)) := by
  rw [← card_Tri]
  apply card_nbij' (fun pq => (pq.1.1 - dj, pq.1.2 - dj))
    (fun p => ((p.1 + dj, p.2 + dj), (p.1 + dj + di, p.2)))
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true] at h ⊢
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true] at h ⊢
    omega
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true]
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true]
    omega

/-- A relation between cells read in coordinates. -/
lemma card_pairs_coord {n : ℕ} (R : ℕ × ℕ → ℕ × ℕ → Prop) [DecidableRel R] :
    (univ.filter (fun p : Cell n × Cell n =>
      R (p.1.1.1.val, p.1.1.2.val) (p.2.1.1.val, p.2.1.2.val))).card =
      ((Tri n ×ˢ Tri n).filter (fun pq => R pq.1 pq.2)).card := by
  apply card_nbij (fun p => ((p.1.1.1.val, p.1.1.2.val), (p.2.1.1.val, p.2.1.2.val)))
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
    simp only [coe_filter, mem_product, mem_Tri, Set.mem_setOf_eq]
    exact ⟨⟨⟨p.1.2, p.1.1.1.isLt⟩, ⟨p.2.2, p.2.1.1.isLt⟩⟩, hp⟩
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    exact Prod.ext (Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)))
      (Subtype.ext (Prod.ext (Fin.ext h3) (Fin.ext h4)))
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩⟩ h
    simp only [coe_filter, mem_product, mem_Tri, Set.mem_setOf_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hR⟩ := h
    refine ⟨(⟨(⟨i, h2⟩, ⟨j, by omega⟩), Fin.mk_le_mk.mpr h1⟩,
      ⟨(⟨i', h4⟩, ⟨j', by omega⟩), Fin.mk_le_mk.mpr h3⟩), ?_, rfl⟩
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact hR

lemma tri_q (k : ℕ) : (tri k : ℚ) = k * (k + 1) / 2 := by
  have h : ((2 * tri k : ℕ) : ℚ) = ((k * (k + 1) : ℕ) : ℚ) := by rw [two_mul_tri]
  push_cast at h
  linarith

/-- The count of a triangle family as a polynomial in n, from the number of pairs of neighbors. -/
lemma count_poly {n : ℕ} (hn : 2 ≤ n) (Nbr : Cell n → Cell n → Prop) [DecidableRel Nbr]
    (hsymm : ∀ c c', Nbr c c' → Nbr c' c) (hirr : ∀ c, ¬ Nbr c c) (E : ℚ)
    (hE : ((edges Nbr).card : ℚ) = E) :
    ({x : Cell n → ℕ | RGS x ∧ Proper Nbr x ∧ ∃ c, x c + 2 = Fintype.card (Cell n)}.ncard : ℚ) =
      1 + ((n : ℚ) * (n + 1) / 2) * ((n : ℚ) * (n + 1) / 2 - 1) / 2 - E := by
  have h2 : 2 ≤ Fintype.card (Cell n) := by
    rw [card_cell]; have := tri_mono hn; simp only [tri] at this; omega
  have h := count_N2_edges Nbr hsymm hirr h2
  have h1 : 1 ≤ tri n := by have := tri_mono (show 1 ≤ n by omega); simp only [tri] at this; omega
  rw [card_cell] at h
  have hq : ((2 * {x : Cell n → ℕ | RGS x ∧ Proper Nbr x ∧ ∃ c, x c + 2 = Fintype.card (Cell n)}.ncard +
      2 * (edges Nbr).card : ℕ) : ℚ) = ((tri n * (tri n - 1) + 2 : ℕ) : ℚ) := by
    rw [card_cell]; exact_mod_cast h
  push_cast [Nat.cast_sub h1] at hq
  rw [tri_q, hE] at hq
  linear_combination hq / 2

/-- The count of a triangle family containing n(n+1)/2 - 3, from the number E of pairs of neighbors
and the number T of triangles of neighbors, with N = n(n+1)/2 cells and P = N(N - 1)/2 - E pairs
of cells that are not neighbors. -/
lemma count3_poly {n : ℕ} (hn : 2 ≤ n) (Nbr : Cell n → Cell n → Prop) [DecidableRel Nbr]
    (hsymm : ∀ c c', Nbr c c' → Nbr c' c) (hirr : ∀ c, ¬ Nbr c c) (E T N P : ℚ)
    (hE : ((edges Nbr).card : ℚ) = E) (hT : ((triangles Nbr).card : ℚ) = T)
    (hN : N = n * (n + 1) / 2) (hP : P = N * (N - 1) / 2 - E) :
    ({x : Cell n → ℕ | RGS x ∧ Proper Nbr x ∧ ∃ c, x c + 3 = Fintype.card (Cell n)}.ncard : ℚ) =
      1 + P + P * (P - 1) / 2 + N * (N - 1) * (N - 2) / 6 - P * (N - 2) - T := by
  have h3 : 3 ≤ Fintype.card (Cell n) := by
    rw [card_cell]; have := tri_mono hn; simp only [tri] at this; omega
  have hK : (Fintype.card (Cell n) : ℚ) = n * (n + 1) / 2 := by rw [card_cell, tri_q]
  have q1 := congrArg (Nat.cast (R := ℚ)) (count_N3_tri Nbr hsymm hirr h3)
  have q2 := congrArg (Nat.cast (R := ℚ)) (card_nonEdges_add_edges Nbr)
  have q3 := congrArg (Nat.cast (R := ℚ)) (choose_three_mul (Fintype.card (Cell n)))
  push_cast [Nat.cast_sub (show 2 ≤ Fintype.card (Cell n) by omega),
    Nat.cast_sub (show 1 ≤ Fintype.card (Cell n) by omega), Nat.cast_choose_two] at q1 q2 q3
  rw [hK] at q1 q2 q3
  rw [hE] at q2
  rw [hT] at q1
  have hP' : ((nonEdges Nbr).card : ℚ) = P := by rw [hP, hN]; linear_combination q2 / 2
  rw [hP'] at q1
  subst hN
  linear_combination q1 + q3 / 6

/-- The pairs of neighbors in coordinates: `rel` is the neighbor relation together with row major
order, in coordinates. -/
lemma edges_eq {n : ℕ} (Nbr : Cell n → Cell n → Prop) [DecidableRel Nbr]
    (rel : ℕ × ℕ → ℕ × ℕ → Prop) [DecidableRel rel]
    (hrel : ∀ c c' : Cell n, (c < c' ∧ Nbr c c') ↔ rel (c.1.1.val, c.1.2.val) (c'.1.1.val, c'.1.2.val)) :
    (edges Nbr).card = ((Tri n ×ˢ Tri n).filter (fun pq => rel pq.1 pq.2)).card := by
  rw [← card_pairs_coord rel]
  unfold edges
  congr 1
  exact filter_congr (fun p _ => hrel p.1 p.2)

/-! ## Counting the triangles of neighbors by their shapes -/

/-- Row major order on the cells, in coordinates. -/
lemma lt_iff_coord {n : ℕ} (c c' : Cell n) :
    c < c' ↔ (c.1.1.val < c'.1.1.val ∨ (c.1.1.val = c'.1.1.val ∧ c.1.2.val < c'.1.2.val)) := by
  rw [cell_lt_iff, ← lex_iff_rank]
  simp only [Fin.lt_def, Fin.ext_iff]

/-- The triangles of neighbors in coordinates, for a neighbor relation that `R` describes in
coordinates between a cell and a later one. -/
lemma triangles_eq {n : ℕ} (Nbr : Cell n → Cell n → Prop) [DecidableRel Nbr]
    (R : ℕ × ℕ → ℕ × ℕ → Prop) [DecidableRel R]
    (hR : ∀ c c' : Cell n, c < c' → (Nbr c c' ↔ R (c.1.1.val, c.1.2.val) (c'.1.1.val, c'.1.2.val))) :
    (triangles Nbr).card = ((Tri n ×ˢ Tri n ×ˢ Tri n).filter (fun t =>
      (t.1.1 < t.2.1.1 ∨ (t.1.1 = t.2.1.1 ∧ t.1.2 < t.2.1.2)) ∧
      (t.2.1.1 < t.2.2.1 ∨ (t.2.1.1 = t.2.2.1 ∧ t.2.1.2 < t.2.2.2)) ∧
      R t.1 t.2.1 ∧ R t.1 t.2.2 ∧ R t.2.1 t.2.2)).card := by
  apply card_nbij (fun t : Cell n × Cell n × Cell n => ((t.1.1.1.val, t.1.1.2.val),
    (t.2.1.1.1.val, t.2.1.1.2.val), (t.2.2.1.1.val, t.2.2.1.2.val)))
  · rintro ⟨c, c', c''⟩ ht
    rw [mem_coe, mem_triangles] at ht
    obtain ⟨h1, h2, k1, k2, k3⟩ := ht
    rw [mem_coe, mem_filter, mem_product, mem_product, mem_Tri, mem_Tri, mem_Tri]
    exact ⟨⟨⟨c.2, c.1.1.isLt⟩, ⟨c'.2, c'.1.1.isLt⟩, ⟨c''.2, c''.1.1.isLt⟩⟩,
      (lt_iff_coord _ _).1 h1, (lt_iff_coord _ _).1 h2, (hR _ _ h1).1 k1,
      (hR _ _ (h1.trans h2)).1 k2, (hR _ _ h2).1 k3⟩
  · intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ := h
    exact Prod.ext (Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)))
      (Prod.ext (Subtype.ext (Prod.ext (Fin.ext h3) (Fin.ext h4)))
        (Subtype.ext (Prod.ext (Fin.ext h5) (Fin.ext h6))))
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩, ⟨i'', j''⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩, l1, l2, r1, r2, r3⟩ := h
    let c : Cell n := ⟨(⟨i, h2⟩, ⟨j, by omega⟩), Fin.mk_le_mk.mpr h1⟩
    let c' : Cell n := ⟨(⟨i', h4⟩, ⟨j', by omega⟩), Fin.mk_le_mk.mpr h3⟩
    let c'' : Cell n := ⟨(⟨i'', h6⟩, ⟨j'', by omega⟩), Fin.mk_le_mk.mpr h5⟩
    have g1 : c < c' := (lt_iff_coord c c').2 l1
    have g2 : c' < c'' := (lt_iff_coord c' c'').2 l2
    refine ⟨(c, c', c''), ?_, rfl⟩
    rw [mem_coe, mem_triangles]
    exact ⟨g1, g2, (hR _ _ g1).2 r1, (hR _ _ (g1.trans g2)).2 r2, (hR _ _ g2).2 r3⟩

/-- In the 2 X 2 block with top left corner (i, j), the triples without the bottom right cell:
(i, j), (i, j + 1), (i + 1, j). They fit in a triangle with n - 2 rows. -/
lemma card_noBR (n : ℕ) :
    ((Tri n ×ˢ Tri n ×ˢ Tri n).filter (fun t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) =>
      t.2.1.1 = t.1.1 ∧ t.2.1.2 = t.1.2 + 1 ∧ t.2.2.1 = t.1.1 + 1 ∧ t.2.2.2 = t.1.2)).card =
      tri (n - 2) := by
  rw [← card_Tri]
  apply card_nbij' (fun t => (t.1.1 - 1, t.1.2))
    (fun p => ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1), (p.1 + 2, p.2)))
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩, ⟨i'', j''⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true, true_and] at h ⊢
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true, true_and] at h ⊢
    omega
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩, ⟨i'', j''⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true, true_and]
    omega

/-- The triples without the bottom left cell: (i, j), (i, j + 1), (i + 1, j + 1), in a triangle
with n - 2 rows. -/
lemma card_noBL (n : ℕ) :
    ((Tri n ×ˢ Tri n ×ˢ Tri n).filter (fun t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) =>
      t.2.1.1 = t.1.1 ∧ t.2.1.2 = t.1.2 + 1 ∧ t.2.2.1 = t.1.1 + 1 ∧ t.2.2.2 = t.1.2 + 1)).card =
      tri (n - 2) := by
  rw [← card_Tri]
  apply card_nbij' (fun t => (t.1.1 - 1, t.1.2))
    (fun p => ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1), (p.1 + 2, p.2 + 1)))
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩, ⟨i'', j''⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true, true_and] at h ⊢
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true, true_and] at h ⊢
    omega
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩, ⟨i'', j''⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true, true_and]
    omega

/-- The triples without the top right cell: (i, j), (i + 1, j), (i + 1, j + 1), in a triangle
with n - 1 rows. -/
lemma card_noTR (n : ℕ) :
    ((Tri n ×ˢ Tri n ×ˢ Tri n).filter (fun t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) =>
      t.2.1.1 = t.1.1 + 1 ∧ t.2.1.2 = t.1.2 ∧ t.2.2.1 = t.1.1 + 1 ∧ t.2.2.2 = t.1.2 + 1)).card =
      tri (n - 1) := by
  rw [← card_Tri]
  apply card_nbij' (fun t => t.1) (fun p => (p, (p.1 + 1, p.2), (p.1 + 1, p.2 + 1)))
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩, ⟨i'', j''⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true, true_and] at h ⊢
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true, true_and] at h ⊢
    omega
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩, ⟨i'', j''⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · rintro ⟨i, j⟩ h
    rfl

/-- The triples without the top left cell: (i, j + 1), (i + 1, j), (i + 1, j + 1), written from
the first cell (i, j) as (i, j), (i + 1, j - 1), (i + 1, j); in a triangle with n - 2 rows. -/
lemma card_noTL (n : ℕ) :
    ((Tri n ×ˢ Tri n ×ˢ Tri n).filter (fun t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) =>
      t.2.1.1 = t.1.1 + 1 ∧ t.2.1.2 + 1 = t.1.2 ∧ t.2.2.1 = t.1.1 + 1 ∧ t.2.2.2 = t.1.2)).card =
      tri (n - 2) := by
  rw [← card_Tri]
  apply card_nbij' (fun t => (t.1.1 - 1, t.1.2 - 1))
    (fun p => ((p.1 + 1, p.2 + 1), (p.1 + 2, p.2), (p.1 + 2, p.2 + 1)))
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩, ⟨i'', j''⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true, true_and] at h ⊢
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri, and_true, true_and] at h ⊢
    omega
  · rintro ⟨⟨i, j⟩, ⟨i', j'⟩, ⟨i'', j''⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · rintro ⟨i, j⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Tri] at h
    simp only [Prod.mk.injEq, and_true, true_and]
    omega

/-! ## The entry: king neighbors on the lower triangular array -/

instance {n : ℕ} (c c' : Cell n) : Decidable (Nbr c c') := by unfold Nbr; infer_instance

lemma nbr_symm {n : ℕ} (c c' : Cell n) (h : Nbr c c') : Nbr c' c := by unfold Nbr at h ⊢; omega

lemma nbr_irr {n : ℕ} (c : Cell n) : ¬ Nbr c c := by unfold Nbr; omega

/-- The pairs of neighbors, by the offset from the earlier cell to the later one: (0, 1), (1, -1),
(1, 0) and (1, 1), which keep triangles with n - 1, n - 2, n - 1 and n - 1 rows. -/
lemma nbr_edges {n : ℕ} (hn : 2 ≤ n) :
    ((edges (@Nbr n)).card : ℚ) = ((n : ℚ) - 1) * n / 2 + ((n : ℚ) - 2) * (n - 1) / 2 +
      ((n : ℚ) - 1) * n / 2 + ((n : ℚ) - 1) * n / 2 := by
  rw [edges_eq _ (fun p q => (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)) ∧
      ((p.1 - q.1) + (q.1 - p.1) ≤ 1 ∧ (p.2 - q.2) + (q.2 - p.2) ≤ 1 ∧
        0 < (p.1 - q.1) + (q.1 - p.1) + ((p.2 - q.2) + (q.2 - p.2))))
    (fun c c' => by rw [cell_lt_iff, ← lex_iff_rank]; simp only [Fin.lt_def, Fin.ext_iff, Nbr])]
  have e2 : (Tri n ×ˢ Tri n).filter (fun pq : (ℕ × ℕ) × (ℕ × ℕ) =>
      (pq.1.1 < pq.2.1 ∨ (pq.1.1 = pq.2.1 ∧ pq.1.2 < pq.2.2)) ∧
        ((pq.1.1 - pq.2.1) + (pq.2.1 - pq.1.1) ≤ 1 ∧ (pq.1.2 - pq.2.2) + (pq.2.2 - pq.1.2) ≤ 1 ∧
          0 < (pq.1.1 - pq.2.1) + (pq.2.1 - pq.1.1) + ((pq.1.2 - pq.2.2) + (pq.2.2 - pq.1.2)))) =
      (Tri n ×ˢ Tri n).filter (fun pq : (ℕ × ℕ) × (ℕ × ℕ) =>
        (pq.2.1 = pq.1.1 + 0 ∧ pq.2.2 = pq.1.2 + 1) ∨ (pq.2.1 = pq.1.1 + 1 ∧ pq.2.2 + 1 = pq.1.2) ∨
          (pq.2.1 = pq.1.1 + 1 ∧ pq.2.2 = pq.1.2 + 0) ∨ (pq.2.1 = pq.1.1 + 1 ∧ pq.2.2 = pq.1.2 + 1)) := by
    refine filter_congr (fun pq h => ?_)
    obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := pq
    simp only [mem_product, mem_Tri] at h
    omega
  rw [e2, filter_or, card_union_of_disjoint (disjoint_filter.2 (fun _ _ h1 h2 => by omega)),
    filter_or, card_union_of_disjoint (disjoint_filter.2 (fun _ _ h1 h2 => by omega)),
    filter_or, card_union_of_disjoint (disjoint_filter.2 (fun _ _ h1 h2 => by omega)),
    card_shift_pos, card_shift_neg, card_shift_pos, card_shift_pos]
  simp only [show max 0 1 = 1 from rfl, show max 1 0 = 1 from rfl, show max 1 1 = 1 from rfl]
  push_cast [tri_q, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 1 + 1 ≤ n by omega)]
  ring

/-- A neighbor later in row major order, in coordinates. -/
lemma nbr_iff {n : ℕ} {c c' : Cell n} (h : c < c') : Nbr c c' ↔
    (c.1.1.val ≤ c'.1.1.val + 1 ∧ c'.1.1.val ≤ c.1.1.val + 1 ∧
      c.1.2.val ≤ c'.1.2.val + 1 ∧ c'.1.2.val ≤ c.1.2.val + 1) := by
  rw [lt_iff_coord] at h
  unfold Nbr
  omega

/-- The triangles of neighbors: three cells of a 2 X 2 block, in four shapes. -/
lemma nbr_triangles {n : ℕ} (hn : 2 ≤ n) :
    ((triangles (@Nbr n)).card : ℚ) = 3 * (((n : ℚ) - 2) * (n - 1) / 2) + ((n : ℚ) - 1) * n / 2 := by
  rw [triangles_eq _ (fun p q => p.1 ≤ q.1 + 1 ∧ q.1 ≤ p.1 + 1 ∧ p.2 ≤ q.2 + 1 ∧ q.2 ≤ p.2 + 1)
    (fun c c' h => nbr_iff h)]
  have e : (Tri n ×ˢ Tri n ×ˢ Tri n).filter (fun t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) =>
      (t.1.1 < t.2.1.1 ∨ (t.1.1 = t.2.1.1 ∧ t.1.2 < t.2.1.2)) ∧
      (t.2.1.1 < t.2.2.1 ∨ (t.2.1.1 = t.2.2.1 ∧ t.2.1.2 < t.2.2.2)) ∧
      (t.1.1 ≤ t.2.1.1 + 1 ∧ t.2.1.1 ≤ t.1.1 + 1 ∧ t.1.2 ≤ t.2.1.2 + 1 ∧ t.2.1.2 ≤ t.1.2 + 1) ∧
      (t.1.1 ≤ t.2.2.1 + 1 ∧ t.2.2.1 ≤ t.1.1 + 1 ∧ t.1.2 ≤ t.2.2.2 + 1 ∧ t.2.2.2 ≤ t.1.2 + 1) ∧
      (t.2.1.1 ≤ t.2.2.1 + 1 ∧ t.2.2.1 ≤ t.2.1.1 + 1 ∧ t.2.1.2 ≤ t.2.2.2 + 1 ∧
        t.2.2.2 ≤ t.2.1.2 + 1)) =
      (Tri n ×ˢ Tri n ×ˢ Tri n).filter (fun t : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) =>
        (t.2.1.1 = t.1.1 ∧ t.2.1.2 = t.1.2 + 1 ∧ t.2.2.1 = t.1.1 + 1 ∧ t.2.2.2 = t.1.2) ∨
        (t.2.1.1 = t.1.1 ∧ t.2.1.2 = t.1.2 + 1 ∧ t.2.2.1 = t.1.1 + 1 ∧ t.2.2.2 = t.1.2 + 1) ∨
        (t.2.1.1 = t.1.1 + 1 ∧ t.2.1.2 = t.1.2 ∧ t.2.2.1 = t.1.1 + 1 ∧ t.2.2.2 = t.1.2 + 1) ∨
        (t.2.1.1 = t.1.1 + 1 ∧ t.2.1.2 + 1 = t.1.2 ∧ t.2.2.1 = t.1.1 + 1 ∧ t.2.2.2 = t.1.2)) := by
    refine filter_congr (fun t _ => ?_)
    obtain ⟨⟨i, j⟩, ⟨i', j'⟩, ⟨i'', j''⟩⟩ := t
    dsimp only
    constructor
    · rintro ⟨l1, l2, ⟨-, a2, a3, a4⟩, ⟨-, b2, -, b4⟩, ⟨-, c2, c3, c4⟩⟩
      rcases l1 with l1 | ⟨l1, l1'⟩ <;> rcases l2 with l2 | ⟨l2, l2'⟩
      · omega
      · by_cases h : j' + 1 = j
        · exact Or.inr (Or.inr (Or.inr (by omega)))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
      · by_cases h : j'' = j
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
      · omega
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) <;> omega
  rw [e, filter_or, card_union_of_disjoint (disjoint_filter.2 (fun _ _ h1 h2 => by omega)),
    filter_or, card_union_of_disjoint (disjoint_filter.2 (fun _ _ h1 h2 => by omega)),
    filter_or, card_union_of_disjoint (disjoint_filter.2 (fun _ _ h1 h2 => by omega)),
    card_noBR, card_noBL, card_noTR, card_noTL]
  push_cast [tri_q, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega)]
  ring

/-- The entry's colorings are the proper colorings with values introduced in order that contain
N - 3, N = n(n+1)/2 the number of cells. -/
lemma a_eq (n : ℕ) :
    a n = {x : Cell n → ℕ | RGS x ∧ Proper Nbr x ∧ ∃ c, x c + 3 = Fintype.card (Cell n)}.ncard := by
  have htri : ((n : ℤ) * (n + 1) / 2) = (tri n : ℤ) := by
    have h : ((n : ℤ) * (n + 1)) = 2 * (tri n : ℤ) := by exact_mod_cast (two_mul_tri n).symm
    rw [h, Int.mul_ediv_cancel_left _ (by norm_num)]
  unfold a
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, RowMajorNew, Cond, RGS, Proper, lex_iff_rank, cell_lt_iff, htri, card_cell]
  refine and_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun c => ?_))
  omega

/-- Hardin's empirical formula, for n ≥ 2. -/
lemma a_poly (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = (1 / 128) * (n : ℚ) ^ 8 + (1 / 32) * (n : ℚ) ^ 7 - (53 / 192) * (n : ℚ) ^ 6 -
      (5 / 16) * (n : ℚ) ^ 5 + (513 / 128) * (n : ℚ) ^ 4 - (577 / 96) * (n : ℚ) ^ 3 -
      (215 / 96) * (n : ℚ) ^ 2 + (235 / 24) * (n : ℚ) - 4 := by
  rw [a_eq, count3_poly hn _ nbr_symm nbr_irr _ _ _ _ (nbr_edges hn) (nbr_triangles hn) rfl rfl]
  ring

lemma a_one : a 1 = 0 := by
  rw [a_eq]
  convert Set.ncard_empty (Cell 1 → ℕ)
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, card_cell]
  rintro - - ⟨c, hc⟩
  rw [show tri 1 = 1 from rfl] at hc
  omega

lemma a_two : a 2 = 1 := by
  have h := a_poly 2 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_three : a 3 = 10 := by
  have h := a_poly 3 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_four : a 4 = 214 := by
  have h := a_poly 4 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_five : a 5 = 1946 := by
  have h := a_poly 5 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_six : a 6 = 10431 := by
  have h := a_poly 6 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_seven : a 7 = 40561 := by
  have h := a_poly 7 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_eight : a 8 = 127275 := by
  have h := a_poly 8 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_nine : a 9 = 342434 := by
  have h := a_poly 9 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_ten : a 10 = 820396 := by
  have h := a_poly 10 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_rec (n : ℕ) :
    a (n + 11) + 36 * a (n + 9) + 126 * a (n + 7) + 84 * a (n + 5) + 9 * a (n + 3) =
      9 * a (n + 10) + 84 * a (n + 8) + 126 * a (n + 6) + 36 * a (n + 4) + a (n + 2) := by
  have h : ((a (n + 11) + 36 * a (n + 9) + 126 * a (n + 7) + 84 * a (n + 5) + 9 * a (n + 3) : ℕ) : ℚ) =
      ((9 * a (n + 10) + 84 * a (n + 8) + 126 * a (n + 6) + 36 * a (n + 4) + a (n + 2) : ℕ) : ℚ) := by
    push_cast
    rw [a_poly (n + 11) (by omega),
      a_poly (n + 10) (by omega),
      a_poly (n + 9) (by omega),
      a_poly (n + 8) (by omega),
      a_poly (n + 7) (by omega),
      a_poly (n + 6) (by omega),
      a_poly (n + 5) (by omega),
      a_poly (n + 4) (by omega),
      a_poly (n + 3) (by omega),
      a_poly (n + 2) (by omega)]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's recurrence. -/
theorem rec_int : ∀ n : ℕ, 10 < n → (a n : ℤ) =
      9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) -
        84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
  have h := a_rec m
  rw [show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega, show m + 11 - 9 = m + 2 by omega]
  have hz : ((a (m + 11) + 36 * a (m + 9) + 126 * a (m + 7) + 84 * a (m + 5) + 9 * a (m + 3) : ℕ) : ℤ) =
      ((9 * a (m + 10) + 84 * a (m + 8) + 126 * a (m + 6) + 36 * a (m + 4) + a (m + 2) : ℕ) : ℤ) := by rw [h]
  push_cast at hz
  linarith

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x^2(1 + x + 160x^2 + 296x^3 - 93x^4 - 104x^5 + 66x^6 -
13x^7 + x^8) / (1 - x)^9. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X ^ 2 * (1 + X + 160 * X ^ 2 + 296 * X ^ 3 - 93 * X ^ 4 - 104 * X ^ 5 + 66 * X ^ 6 -
        13 * X ^ 7 + X ^ 8) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 9 = A - A * X ^ 1 * C 9 + A * X ^ 2 * C 36 - A * X ^ 3 * C 84 + A * X ^ 4 * C 126 - A * X ^ 5 * C 126 + A * X ^ 6 * C 84 - A * X ^ 7 * C 36 + A * X ^ 8 * C 9 - A * X ^ 9 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9,
      show (C (36 : ℚ) : ℚ⟦X⟧) = 36 from map_ofNat C 36,
      show (C (84 : ℚ) : ℚ⟦X⟧) = 84 from map_ofNat C 84,
      show (C (126 : ℚ) : ℚ⟦X⟧) = 126 from map_ofNat C 126]
    ring
  have e2 : (X ^ 2 * (1 + X + 160 * X ^ 2 + 296 * X ^ 3 - 93 * X ^ 4 - 104 * X ^ 5 + 66 * X ^ 6 -
      13 * X ^ 7 + X ^ 8) : ℚ⟦X⟧) = X ^ 2 * C 1 + X ^ 3 * C 1 + X ^ 4 * C 160 + X ^ 5 * C 296 - X ^ 6 * C 93 - X ^ 7 * C 104 + X ^ 8 * C 66 - X ^ 9 * C 13 + X ^ 10 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (13 : ℚ) : ℚ⟦X⟧) = 13 from map_ofNat C 13,
      show (C (66 : ℚ) : ℚ⟦X⟧) = 66 from map_ofNat C 66,
      show (C (93 : ℚ) : ℚ⟦X⟧) = 93 from map_ofNat C 93,
      show (C (104 : ℚ) : ℚ⟦X⟧) = 104 from map_ofNat C 104,
      show (C (160 : ℚ) : ℚ⟦X⟧) = 160 from map_ofNat C 160,
      show (C (296 : ℚ) : ℚ⟦X⟧) = 296 from map_ofNat C 296]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · simp [a_one, a_two, a_three, a_four] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five, a_six] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five, a_six, a_seven] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten] <;> norm_num
  · have h := a_rec n
    have hq : (a (n + 11) : ℚ) + 36 * (a (n + 9) : ℚ) + 126 * (a (n + 7) : ℚ) + 84 * (a (n + 5) : ℚ) + 9 * (a (n + 3) : ℚ) =
        9 * (a (n + 10) : ℚ) + 84 * (a (n + 8) : ℚ) + 126 * (a (n + 6) : ℚ) + 36 * (a (n + 4) : ℚ) + (a (n + 2) : ℚ) := by exact_mod_cast h
    simp only [show ¬ (n + 11 = 0) by omega,
      if_false,
      if_true,
      show 1 ≤ n + 11 by omega,
      show n + 11 - 1 = n + 10 by omega,
      show ¬ (n + 10 = 0) by omega,
      show 2 ≤ n + 11 by omega,
      show n + 11 - 2 = n + 9 by omega,
      show ¬ (n + 9 = 0) by omega,
      show 3 ≤ n + 11 by omega,
      show n + 11 - 3 = n + 8 by omega,
      show ¬ (n + 8 = 0) by omega,
      show 4 ≤ n + 11 by omega,
      show n + 11 - 4 = n + 7 by omega,
      show ¬ (n + 7 = 0) by omega,
      show 5 ≤ n + 11 by omega,
      show n + 11 - 5 = n + 6 by omega,
      show ¬ (n + 6 = 0) by omega,
      show 6 ≤ n + 11 by omega,
      show n + 11 - 6 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 7 ≤ n + 11 by omega,
      show n + 11 - 7 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 8 ≤ n + 11 by omega,
      show n + 11 - 8 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 9 ≤ n + 11 by omega,
      show n + 11 - 9 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show ¬ (n + 11 = 1) by omega,
      show ¬ (n + 11 = 2) by omega,
      show ¬ (n + 11 = 3) by omega,
      show ¬ (n + 11 = 4) by omega,
      show ¬ (n + 11 = 5) by omega,
      show ¬ (n + 11 = 6) by omega,
      show ¬ (n + 11 = 7) by omega,
      show ¬ (n + 11 = 8) by omega,
      show ¬ (n + 11 = 9) by omega,
      show ¬ (n + 11 = 10) by omega]
    linear_combination hq

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X ^ 2 * (1 + X + 160 * X ^ 2 + 296 * X ^ 3 - 93 * X ^ 4 - 104 * X ^ 5 + 66 * X ^ 6 -
        13 * X ^ 7 + X ^ 8) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) =
      9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) -
        84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) :=
  ⟨gf, rec_int⟩

/-- Controls: the entry's terms a(1..10). -/
theorem controls : a 1 = 0 ∧ a 2 = 1 ∧ a 3 = 10 ∧ a 4 = 214 ∧ a 5 = 1946 ∧ a 6 = 10431 ∧ a 7 = 40561 ∧ a 8 = 127275 ∧ a 9 = 342434 ∧ a 10 = 820396 :=
  ⟨a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, a_nine, a_ten⟩

end OMA.S_oeis_a211912

theorem OMA.solution : type_of% @OMA.S_oeis_a211912.main :=
  OMA.S_oeis_a211912.conjecture
