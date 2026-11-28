import OMAStatements.S_oeis_a211911

namespace OMA.S_oeis_a211911

open PowerSeries Finset






instance {n : ℕ} : Fintype (Cell n) := by unfold Cell; infer_instance

instance {n : ℕ} : DecidableEq (Cell n) := by unfold Cell; infer_instance

instance {n : ℕ} (c c' : Cell n) : Decidable (Nbr c c') := by unfold Nbr; infer_instance

/-! ## Row major order -/

/-- The triangular numbers: tri k is the number of cells in the first k rows. -/
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

lemma before_iff {n : ℕ} (c c' : Cell n) :
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
  · have := (before_iff c c').1 (Or.inl h1); omega
  · rcases lt_trichotomy c.1.2.val c'.1.2.val with h2 | h2 | h2
    · have := (before_iff c c').1 (Or.inr ⟨Fin.ext h1, h2⟩); omega
    · exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))
    · have := (before_iff c' c).1 (Or.inr ⟨Fin.ext h1.symm, h2⟩); omega
  · have := (before_iff c' c).1 (Or.inl h1); omega

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

lemma rmn_iff {n : ℕ} (x : Cell n → ℕ) :
    RowMajorNew x ↔ ∀ c, ∀ u < x c, ∃ c', rank c' < rank c ∧ x c' = u := by
  unfold RowMajorNew
  simp only [before_iff]

/-! ## Colorings with at least n(n+1)/2 - 1 values -/

/-- The coloring that gives the cell b the value of the cell a and numbers the other cells in row
major order, skipping b. -/
def rep {n : ℕ} (a b c : Cell n) : ℕ :=
  if rank c < rank b then rank c else if rank c = rank b then rank a else rank c - 1

lemma rep_lt {n : ℕ} {a b c : Cell n} (h : rank c < rank b) : rep a b c = rank c := by
  unfold rep; rw [if_pos h]

lemma rep_eq {n : ℕ} {a b c : Cell n} (h : rank c = rank b) : rep a b c = rank a := by
  unfold rep; rw [if_neg (by omega), if_pos h]

lemma rep_gt {n : ℕ} {a b c : Cell n} (h : rank b < rank c) : rep a b c = rank c - 1 := by
  unfold rep; rw [if_neg (by omega), if_neg (by omega)]

lemma le_rank {n : ℕ} (x : Cell n → ℕ) (hx : ∀ c, ∀ u < x c, ∃ c', rank c' < rank c ∧ x c' = u)
    (c : Cell n) : x c ≤ rank c := by
  induction hk : rank c using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    by_contra h
    obtain ⟨e, he, hxe⟩ := hx c k (by omega)
    have := ih (rank e) (by omega) e rfl
    omega

/-- A coloring whose values are introduced in row major order and which reaches n(n+1)/2 - 2 is
the numbering of the cells in row major order, or repeats the value of one cell once. -/
lemma rgs_cases {n : ℕ} (x : Cell n → ℕ) (hx : ∀ c, ∀ u < x c, ∃ c', rank c' < rank c ∧ x c' = u)
    (c0 : Cell n) (h0 : x c0 + 2 = tri n) :
    x = rank ∨ ∃ a b : Cell n, rank a < rank b ∧ x = rep a b := by
  by_cases hall : ∀ c, x c = rank c
  · exact Or.inl (funext hall)
  push_neg at hall
  have hex : ∃ k, ∃ c, rank c = k ∧ x c ≠ rank c := let ⟨c, hc⟩ := hall; ⟨rank c, c, rfl, hc⟩
  obtain ⟨b, hbk, hbne⟩ := Nat.find_spec hex
  have hmin : ∀ c, rank c < rank b → x c = rank c := by
    intro c hc
    by_contra hne
    exact Nat.find_min hex (hbk ▸ hc) ⟨c, rfl, hne⟩
  have hblt : x b < rank b := lt_of_le_of_ne (le_rank x hx b) hbne
  obtain ⟨a, ha⟩ := rank_surj n (x b) (by have := rank_lt b; omega)
  have R2 : ∀ c, rank b ≤ rank c → x c + 1 ≤ rank c := by
    intro c
    induction hk : rank c using Nat.strong_induction_on generalizing c with
    | _ k ih =>
      intro hbc
      rcases Nat.eq_or_lt_of_le hbc with h | h
      · have : c = b := rank_inj (by omega)
        subst this; omega
      · by_contra hc
        have hxc := le_rank x hx c
        obtain ⟨e, he, hxe⟩ := hx c (k - 1) (by omega)
        by_cases heb : rank e < rank b
        · have := hmin e heb; omega
        · have := ih (rank e) (by omega) e rfl (by omega); omega
  have R3 : ∀ t, ∀ c, rank c + t + 1 = tri n → rank b < rank c → x c = rank c - 1 := by
    intro t
    induction t with
    | zero =>
      intro c hc hbc
      have hc0 : rank c0 + 1 = tri n := by
        by_cases h : rank c0 < rank b
        · have := hmin c0 h; omega
        · have := R2 c0 (by omega); have := rank_lt c0; omega
      have : c = c0 := rank_inj (by omega)
      subst this; omega
    | succ t ih =>
      intro c hc hbc
      obtain ⟨c', hc'⟩ := rank_surj n (rank c + 1) (by omega)
      have hx' := ih c' (by omega) (by omega)
      obtain ⟨e, he, hxe⟩ := hx c' (rank c - 1) (by omega)
      by_cases heb : rank e < rank b
      · have := hmin e heb; omega
      · by_cases hec : rank e < rank c
        · have := R2 e (by omega); omega
        · have : e = c := rank_inj (by omega)
          subst this; omega
  refine Or.inr ⟨a, b, by omega, funext fun c => ?_⟩
  rcases lt_trichotomy (rank c) (rank b) with h | h | h
  · rw [rep_lt h]; exact hmin c h
  · rw [rep_eq h, rank_inj h]; omega
  · rw [rep_gt h]; exact R3 (tri n - 1 - rank c) c (by have := rank_lt c; omega) h

lemma rgs_rank {n : ℕ} : ∀ c : Cell n, ∀ u < rank c, ∃ c' : Cell n, rank c' < rank c ∧ rank c' = u := by
  intro c u hu
  obtain ⟨c', hc'⟩ := rank_surj n u (lt_trans hu (rank_lt c))
  exact ⟨c', by omega, hc'⟩

lemma rgs_rep {n : ℕ} (a b : Cell n) (hab : rank a < rank b) :
    ∀ c, ∀ u < rep a b c, ∃ c', rank c' < rank c ∧ rep a b c' = u := by
  intro c u hu
  have hc := rank_lt c
  rcases lt_trichotomy (rank c) (rank b) with h | h | h
  · rw [rep_lt h] at hu
    obtain ⟨e, he⟩ := rank_surj n u (by omega)
    exact ⟨e, by omega, by rw [rep_lt (by omega)]; exact he⟩
  · rw [rep_eq h] at hu
    obtain ⟨e, he⟩ := rank_surj n u (by omega)
    exact ⟨e, by omega, by rw [rep_lt (by omega)]; exact he⟩
  · rw [rep_gt h] at hu
    by_cases hub : u < rank b
    · obtain ⟨e, he⟩ := rank_surj n u (by omega)
      exact ⟨e, by omega, by rw [rep_lt (by omega)]; exact he⟩
    · obtain ⟨e, he⟩ := rank_surj n (u + 1) (by omega)
      exact ⟨e, by omega, by rw [rep_gt (by omega)]; omega⟩

lemma rep_top {n : ℕ} (a b : Cell n) (hab : rank a < rank b) : ∃ c, rep a b c + 2 = tri n := by
  have hb := rank_lt b
  by_cases hlast : rank b + 1 = tri n
  · obtain ⟨c, hc⟩ := rank_surj n (tri n - 2) (by omega)
    exact ⟨c, by rw [rep_lt (by omega)]; omega⟩
  · obtain ⟨c, hc⟩ := rank_surj n (tri n - 1) (by omega)
    exact ⟨c, by rw [rep_gt (by omega)]; omega⟩

lemma rep_inj {n : ℕ} (a b : Cell n) (hab : rank a < rank b) (c c' : Cell n)
    (h : rep a b c = rep a b c') (hne : c ≠ c') : (c = a ∧ c' = b) ∨ (c = b ∧ c' = a) := by
  have hr : rank c ≠ rank c' := fun e => hne (rank_inj e)
  rcases lt_trichotomy (rank c) (rank b) with h1 | h1 | h1 <;>
    rcases lt_trichotomy (rank c') (rank b) with h2 | h2 | h2
  · rw [rep_lt h1, rep_lt h2] at h; omega
  · rw [rep_lt h1, rep_eq h2] at h
    exact Or.inl ⟨rank_inj h, rank_inj h2⟩
  · rw [rep_lt h1, rep_gt h2] at h; omega
  · rw [rep_eq h1, rep_lt h2] at h
    exact Or.inr ⟨rank_inj h1, rank_inj h.symm⟩
  · omega
  · rw [rep_eq h1, rep_gt h2] at h; omega
  · rw [rep_gt h1, rep_lt h2] at h; omega
  · rw [rep_gt h1, rep_eq h2] at h; omega
  · rw [rep_gt h1, rep_gt h2] at h; omega

/-! ## The neighbor condition on these colorings -/

lemma nbr_symm {n : ℕ} {c c' : Cell n} (h : Nbr c c') : Nbr c' c := by
  unfold Nbr at h ⊢; omega

lemma nbr_ne {n : ℕ} {c c' : Cell n} (h : Nbr c c') : c ≠ c' := by
  rintro rfl; unfold Nbr at h; omega

lemma cond_rank {n : ℕ} : Cond (@rank n) := fun c c' h e => nbr_ne h (rank_inj e)

lemma cond_rep {n : ℕ} (a b : Cell n) (hab : rank a < rank b) : Cond (rep a b) ↔ ¬ Nbr a b := by
  constructor
  · intro h hn
    exact h a b hn (by rw [rep_lt hab, rep_eq rfl])
  · intro hn c c' hcc' heq
    rcases rep_inj a b hab c c' heq (nbr_ne hcc') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hn hcc'
    · exact hn (nbr_symm hcc')

/-! ## The count as one plus the pairs of cells that are not neighbors -/

lemma tri_cast (n : ℕ) : ((n : ℤ) * (n + 1) / 2) = (tri n : ℤ) := by
  have h : ((n : ℤ) * (n + 1)) = 2 * (tri n : ℤ) := by exact_mod_cast (two_mul_tri n).symm
  rw [h, Int.mul_ediv_cancel_left _ (by norm_num)]

/-- The colorings counted: the images of none (all values distinct) and of some (a, b) (the cell b
repeats the value of the earlier cell a, which is not its neighbor). -/
lemma set_eq {n : ℕ} (hn : 2 ≤ n) :
    {x : Cell n → ℕ | RowMajorNew x ∧ Cond x ∧ ∃ c, (x c : ℤ) = (n : ℤ) * (n + 1) / 2 - 2} =
      (fun o : Option (Cell n × Cell n) => o.elim rank (fun p => rep p.1 p.2)) ''
        ↑(insert none ((univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2 ∧ ¬ Nbr p.1 p.2)).map
          Function.Embedding.some)) := by
  have htri : 3 ≤ tri n := by
    have := tri_mono hn
    simp only [tri] at this
    omega
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, coe_insert, coe_map, coe_filter, mem_univ, true_and,
    Set.mem_insert_iff, tri_cast]
  constructor
  · rintro ⟨hr, hc, c0, h0⟩
    rw [rmn_iff] at hr
    rcases rgs_cases x hr c0 (by omega) with rfl | ⟨a, b, hab, rfl⟩
    · exact ⟨none, Or.inl rfl, rfl⟩
    · exact ⟨some (a, b), Or.inr ⟨(a, b), ⟨hab, (cond_rep a b hab).1 hc⟩, rfl⟩, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    rcases ho with rfl | ⟨⟨a, b⟩, ⟨hab, hn⟩, rfl⟩
    · refine ⟨(rmn_iff _).2 rgs_rank, cond_rank, ?_⟩
      obtain ⟨c, hc⟩ := rank_surj n (tri n - 2) (by omega)
      exact ⟨c, by simp only [Option.elim]; omega⟩
    · refine ⟨(rmn_iff _).2 (rgs_rep a b hab), (cond_rep a b hab).2 hn, ?_⟩
      obtain ⟨c, hc⟩ := rep_top a b hab
      exact ⟨c, by simp only [Option.elim, Function.Embedding.some_apply]; omega⟩

lemma injOn_opt {n : ℕ} :
    Set.InjOn (fun o : Option (Cell n × Cell n) => o.elim rank (fun p => rep p.1 p.2))
      ↑(insert none ((univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2 ∧ ¬ Nbr p.1 p.2)).map
          Function.Embedding.some)) := by
  have key : ∀ a b : Cell n, rank a < rank b → rep a b ≠ rank := fun a b hab e => by
    have := congrFun e b
    rw [rep_eq rfl] at this; omega
  intro o ho o' ho' h
  simp only [coe_insert, coe_map, coe_filter, mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_image, Set.mem_setOf_eq, Function.Embedding.some_apply] at ho ho'
  rcases ho with rfl | ⟨⟨a, b⟩, ⟨hab, _⟩, rfl⟩ <;> rcases ho' with rfl | ⟨⟨a', b'⟩, ⟨hab', _⟩, rfl⟩
  · rfl
  · exact absurd h.symm (key a' b' hab')
  · exact absurd h (key a b hab)
  · simp only [Option.elim] at h
    have h1 : rank a < rank b := hab
    have h2 : rank a' < rank b' := hab'
    have hb : rank b = rank b' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · have := congrFun h b
        rw [rep_eq rfl, rep_lt hl] at this; omega
      · have := congrFun h b'
        rw [rep_eq rfl, rep_lt hl] at this; omega
    have hbb := rank_inj hb
    subst hbb
    have := congrFun h b
    rw [rep_eq rfl, rep_eq rfl] at this
    rw [rank_inj this]

lemma a_eq {n : ℕ} (hn : 2 ≤ n) :
    a n = (univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2 ∧ ¬ Nbr p.1 p.2)).card + 1 := by
  unfold a
  rw [set_eq hn, injOn_opt.ncard_image, Set.ncard_coe_finset, card_insert_of_notMem (by simp),
    card_map]

lemma a_one : a 1 = 0 := by
  unfold a
  convert Set.ncard_empty (Cell 1 → ℕ)
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro - - ⟨c, hc⟩
  norm_num at hc
  omega

/-! ## Counting pairs of cells -/

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

lemma card_lt_pairs (N : ℕ) :
    2 * ((range N ×ˢ range N).filter (fun p : ℕ × ℕ => p.1 < p.2)).card = N * (N - 1) := by
  rw [card_filter, sum_product_right]
  have h : ∀ v ∈ range N, (∑ u ∈ range N, if (u, v).1 < (u, v).2 then 1 else 0) = v := by
    intro v hv
    rw [mem_range] at hv
    have e : (range N).filter (fun u => u < v) = range v := by
      ext u; simp only [mem_filter, mem_range]; omega
    simp only [sum_boole, e, card_range, Nat.cast_id]
  rw [sum_congr rfl h, mul_comm, sum_range_id_mul_two]

/-- Twice the number of pairs of cells in row major order. -/
lemma card_before (n : ℕ) :
    2 * (univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2)).card = tri n * (tri n - 1) := by
  rw [← card_lt_pairs (tri n)]
  congr 1
  apply card_nbij (fun p => (rank p.1, rank p.2))
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq]
    exact ⟨⟨rank_lt _, rank_lt _⟩, hp⟩
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rank_inj h.1) (rank_inj h.2)
  · rintro ⟨u, v⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h
    obtain ⟨a, ha⟩ := rank_surj n u h.1.1
    obtain ⟨b, hb⟩ := rank_surj n v h.1.2
    refine ⟨(a, b), ?_, by simp only [ha, hb]⟩
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    rw [ha, hb]; exact h.2

lemma card_split (n : ℕ) :
    (univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2 ∧ ¬ Nbr p.1 p.2)).card +
      (univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2 ∧ Nbr p.1 p.2)).card =
      (univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2)).card := by
  rw [← card_filter_add_card_filter_not (s := univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2))
    (fun p => Nbr p.1 p.2), filter_filter, filter_filter, add_comm]

lemma tri_q (k : ℕ) : (tri k : ℚ) = k * (k + 1) / 2 := by
  have h : ((2 * tri k : ℕ) : ℚ) = ((k * (k + 1) : ℕ) : ℚ) := by rw [two_mul_tri]
  push_cast at h
  linarith

/-! ## The neighbors in coordinates -/

/-- Row major order and the neighbor relation, in coordinates. -/
def RelN (p q : ℕ × ℕ) : Prop :=
  (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)) ∧
    ((p.1 - q.1) + (q.1 - p.1) ≤ 1 ∧
    (p.2 - q.2) + (q.2 - p.2) ≤ 1 ∧
    0 < (p.1 - q.1) + (q.1 - p.1) +
      ((p.2 - q.2) + (q.2 - p.2)))

instance : DecidableRel RelN := fun p q => by unfold RelN; infer_instance

/-- The pairs of neighbors, counted by the offset from the earlier cell to the later one. -/
lemma card_adj (n : ℕ) :
    (univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2 ∧ Nbr p.1 p.2)).card =
      tri (n - 1) + (tri (n - 2) + (tri (n - 1) + tri (n - 1))) := by
  have e1 : univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2 ∧ Nbr p.1 p.2) =
      univ.filter (fun p : Cell n × Cell n =>
        RelN (p.1.1.1.val, p.1.1.2.val) (p.2.1.1.val, p.2.1.2.val)) := by
    refine filter_congr (fun p _ => ?_)
    rw [← before_iff]
    simp only [Fin.lt_def, Fin.ext_iff, RelN, Nbr]
  rw [e1, card_pairs_coord RelN]
  have e2 : (Tri n ×ˢ Tri n).filter (fun pq => RelN pq.1 pq.2) =
      (Tri n ×ˢ Tri n).filter (fun pq : (ℕ × ℕ) × (ℕ × ℕ) =>
        (pq.2.1 = pq.1.1 + 0 ∧ pq.2.2 = pq.1.2 + 1) ∨
          (pq.2.1 = pq.1.1 + 1 ∧ pq.2.2 + 1 = pq.1.2) ∨
          (pq.2.1 = pq.1.1 + 1 ∧ pq.2.2 = pq.1.2 + 0) ∨
          (pq.2.1 = pq.1.1 + 1 ∧ pq.2.2 = pq.1.2 + 1)) := by
    refine filter_congr (fun pq h => ?_)
    obtain ⟨⟨i, j⟩, ⟨i', j'⟩⟩ := pq
    simp only [mem_product, mem_Tri] at h
    simp only [RelN]
    omega
  rw [e2,
    filter_or, card_union_of_disjoint (disjoint_filter.2 (fun _ _ h1 h2 => by omega)),
    filter_or, card_union_of_disjoint (disjoint_filter.2 (fun _ _ h1 h2 => by omega)),
    filter_or, card_union_of_disjoint (disjoint_filter.2 (fun _ _ h1 h2 => by omega)),
    card_shift_pos, card_shift_neg, card_shift_pos, card_shift_pos]
  all_goals rfl

/-! ## The formula -/

lemma a_poly (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = 1 + ((n : ℚ) * (n + 1) / 2) * ((n : ℚ) * (n + 1) / 2 - 1) / 2 -
      (((n : ℚ) - 1) * ((n : ℚ) - 1 + 1) / 2 + (((n : ℚ) - 2) * ((n : ℚ) - 2 + 1) / 2 + (((n : ℚ) - 1) * ((n : ℚ) - 1 + 1) / 2 + ((n : ℚ) - 1) * ((n : ℚ) - 1 + 1) / 2))) := by
  have e1 := a_eq hn
  have e2 := card_split n
  have e3 := card_before n
  have e4 := card_adj n
  set A := (univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2 ∧ ¬ Nbr p.1 p.2)).card
  set B := (univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2 ∧ Nbr p.1 p.2)).card
  set P := (univ.filter (fun p : Cell n × Cell n => rank p.1 < rank p.2)).card
  have h1 : 1 ≤ tri n := by have := tri_mono (show 1 ≤ n by omega); simp only [tri] at this; omega
  have q1 : (a n : ℚ) = A + 1 := by exact_mod_cast e1
  have q2 : (A : ℚ) + B = P := by exact_mod_cast e2
  have q3 : 2 * (P : ℚ) = (tri n : ℚ) * ((tri n : ℚ) - 1) := by
    have := congrArg (Nat.cast (R := ℚ)) e3
    push_cast [Nat.cast_sub h1] at this
    exact this
  have q4 : (B : ℚ) = (tri (n - 1) : ℚ) + ((tri (n - 2) : ℚ) + ((tri (n - 1) : ℚ) + (tri (n - 1) : ℚ))) := by exact_mod_cast e4
  simp only [tri_q] at q3 q4
  push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega)] at q4
  linear_combination q1 + q2 + q3 / 2 - q4

lemma a_two : a 2 = 1 := by
  have h := a_poly 2 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_three : a 3 = 6 := by
  have h := a_poly 3 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_four : a 4 = 25 := by
  have h := a_poly 4 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_five : a 5 = 70 := by
  have h := a_poly 5 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_six : a 6 = 156 := by
  have h := a_poly 6 (by norm_num)
  norm_num at h
  exact_mod_cast h

lemma a_rec (n : ℕ) :
    a (n + 7) + 10 * a (n + 5) + 5 * a (n + 3) = 5 * a (n + 6) + 10 * a (n + 4) + a (n + 2) := by
  have h : ((a (n + 7) + 10 * a (n + 5) + 5 * a (n + 3) : ℕ) : ℚ) =
      ((5 * a (n + 6) + 10 * a (n + 4) + a (n + 2) : ℕ) : ℚ) := by
    push_cast
    rw [a_poly (n + 7) (by omega), a_poly (n + 6) (by omega), a_poly (n + 5) (by omega),
      a_poly (n + 4) (by omega), a_poly (n + 3) (by omega), a_poly (n + 2) (by omega)]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's recurrence. -/
theorem rec_int : ∀ n : ℕ, 6 < n → (a n : ℤ) =
      5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have h := a_rec m
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega,
    show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega]
  have hz : ((a (m + 7) + 10 * a (m + 5) + 5 * a (m + 3) : ℕ) : ℤ) =
      ((5 * a (m + 6) + 10 * a (m + 4) + a (m + 2) : ℕ) : ℤ) := by rw [h]
  push_cast at hz
  linarith

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x^2(1 + x + 5x^2 - 5x^3 + x^4) / (1 - x)^5. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X ^ 2 * (1 + X + 5 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 5 = A - A * X ^ 1 * C 5 + A * X ^ 2 * C 10 - A * X ^ 3 * C 10 + A * X ^ 4 * C 5 - A * X ^ 5 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5,
      show (C (10 : ℚ) : ℚ⟦X⟧) = 10 from map_ofNat C 10]
    ring
  have e2 : (X ^ 2 * (1 + X + 5 * X ^ 2 - 5 * X ^ 3 + X ^ 4) : ℚ⟦X⟧) = X ^ 2 * C 1 + X ^ 3 * C 1 + X ^ 4 * C 5 - X ^ 5 * C 5 + X ^ 6 * C 1 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · simp [a_one, a_two, a_three, a_four] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five] <;> norm_num
  · simp [a_one, a_two, a_three, a_four, a_five, a_six] <;> norm_num
  · have h := a_rec n
    have hq : (a (n + 7) : ℚ) + 10 * (a (n + 5) : ℚ) + 5 * (a (n + 3) : ℚ) =
        5 * (a (n + 6) : ℚ) + 10 * (a (n + 4) : ℚ) + (a (n + 2) : ℚ) := by exact_mod_cast h
    simp only [show ¬ (n + 7 = 0) by omega,
      if_false,
      if_true,
      show 1 ≤ n + 7 by omega,
      show n + 7 - 1 = n + 6 by omega,
      show ¬ (n + 6 = 0) by omega,
      show 2 ≤ n + 7 by omega,
      show n + 7 - 2 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 3 ≤ n + 7 by omega,
      show n + 7 - 3 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 4 ≤ n + 7 by omega,
      show n + 7 - 4 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 5 ≤ n + 7 by omega,
      show n + 7 - 5 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show ¬ (n + 7 = 1) by omega,
      show ¬ (n + 7 = 2) by omega,
      show ¬ (n + 7 = 3) by omega,
      show ¬ (n + 7 = 4) by omega,
      show ¬ (n + 7 = 5) by omega,
      show ¬ (n + 7 = 6) by omega]
    linear_combination hq

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X ^ 2 * (1 + X + 5 * X ^ 2 - 5 * X ^ 3 + X ^ 4) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) =
      5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) :=
  ⟨gf, rec_int⟩

/-- Controls: the entry's terms a(1..10). -/
theorem controls : a 1 = 0 ∧ a 2 = 1 ∧ a 3 = 6 ∧ a 4 = 25 ∧ a 5 = 70 ∧ a 6 = 156 ∧ a 7 = 301 ∧ a 8 = 526 ∧ a 9 = 855 ∧ a 10 = 1315 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3
  have h1 := a_one; have h2 := a_two; have h3 := a_three; have h4 := a_four; have h5 := a_five; have h6 := a_six
  norm_num at r0 r1 r2 r3
  omega

end OMA.S_oeis_a211911

theorem OMA.solution : type_of% @OMA.S_oeis_a211911.main :=
  OMA.S_oeis_a211911.conjecture
