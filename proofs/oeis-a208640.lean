import OMAStatements.S_oeis_a208640
import Mathlib

namespace OMA.Helpers_a208640
open OMA.S_oeis_a208640 Finset

def A {R n : ℕ} (x : Fin R → Fin n → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < R ∧ j < n then (x ⟨i, h.1⟩ ⟨j, h.2⟩).val else 2

lemma A_lt {R n : ℕ} (x : Fin R → Fin n → Fin 2) (i j : ℕ) (hi : i < R) (hj : j < n) :
    A x i j < 2 := by
  unfold A; rw [dif_pos ⟨hi, hj⟩]; exact (x _ _).isLt

lemma A_out {R n : ℕ} (x : Fin R → Fin n → Fin 2) (i j : ℕ) (h : ¬(i < R ∧ j < n)) :
    A x i j = 2 := by
  unfold A; rw [dif_neg h]

lemma A_fin {R n : ℕ} (x : Fin R → Fin n → Fin 2) (i : Fin R) (j : Fin n) :
    A x i.val j.val = (x i j).val := by
  unfold A; rw [dif_pos ⟨i.2, j.2⟩]

def Bad (v l u r : ℕ) : Prop := (l = v ∧ u = v) ∨ (l = v ∧ r = v) ∨ (u = v ∧ r = v)

instance (v l u r : ℕ) : Decidable (Bad v l u r) := by unfold Bad; infer_instance

def okAt {R n : ℕ} (x : Fin R → Fin n → Fin 2) (i j : ℕ) : Prop :=
  ¬Bad (A x i j) (if j = 0 then 2 else A x i (j - 1)) (if i = 0 then 2 else A x (i - 1) j)
    (if i = 0 then 2 else A x (i - 1) (j + 1))

lemma dsum_pt (R n a0 b0 : ℕ) (Q : Prop) [Decidable Q] :
    ∑ a ∈ range R, ∑ b ∈ range n, (if a = a0 ∧ b = b0 ∧ Q then 1 else 0) =
      if a0 < R ∧ b0 < n ∧ Q then 1 else 0 := by
  have : ∀ a b, (if a = a0 ∧ b = b0 ∧ Q then 1 else 0) =
      (if a = a0 then (if b = b0 then (if Q then 1 else 0) else 0) else 0) := by
    intro a b; by_cases h1 : a = a0 <;> by_cases h2 : b = b0 <;> simp [h1, h2]
  simp only [this]
  by_cases h1 : a0 < R <;> by_cases h2 : b0 < n <;> by_cases h3 : Q <;> simp [h1, h2, h3]

/-- the number of neighbours, as a sum of three indicators -/
lemma eqNbrs_eq {R n : ℕ} (x : Fin R → Fin n → Fin 2) (i : Fin R) (j : Fin n) :
    eqNbrs x i j = (if j.val ≠ 0 ∧ A x i.val (j.val - 1) = A x i.val j.val then 1 else 0) +
      (if i.val ≠ 0 ∧ A x (i.val - 1) j.val = A x i.val j.val then 1 else 0) +
      (if i.val ≠ 0 ∧ A x (i.val - 1) (j.val + 1) = A x i.val j.val then 1 else 0) := by
  unfold eqNbrs
  rw [Finset.card_filter, Fintype.sum_prod_type]
  obtain ⟨I, hI⟩ : ∃ I, I = i.val := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = j.val := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = A x I J := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ → ℕ, f = fun a b =>
    if ((a = I ∧ b + 1 = J) ∨ (a + 1 = I ∧ b = J) ∨ (a + 1 = I ∧ b = J + 1)) ∧ A x a b = v then 1 else 0 :=
    ⟨_, rfl⟩
  have hconv : ∀ (a : Fin R) (b : Fin n),
      (if ((a = i ∧ b.val + 1 = j.val) ∨ (a.val + 1 = i.val ∧ b = j) ∨
          (a.val + 1 = i.val ∧ b.val = j.val + 1)) ∧ x a b = x i j then 1 else 0) = f a.val b.val := by
    intro a b
    have hfin : x a b = x i j ↔ A x a.val b.val = v := by rw [hv, hI, hJ, A_fin, A_fin, Fin.val_eq_val]
    simp only [hf, Fin.ext_iff, hfin, hI, hJ]
  simp only [hconv]
  rw [Finset.sum_congr rfl (fun (a : Fin R) _ => Fin.sum_univ_eq_sum_range (f a.val) n)]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range n, f a b) R]
  have hsplit : ∀ a ∈ range R, ∀ b ∈ range n, f a b =
      (if a = I ∧ b = J - 1 ∧ (J ≠ 0 ∧ A x I (J - 1) = v) then 1 else 0) +
      (if a = I - 1 ∧ b = J ∧ (I ≠ 0 ∧ A x (I - 1) J = v) then 1 else 0) +
      (if a = I - 1 ∧ b = J + 1 ∧ (I ≠ 0 ∧ A x (I - 1) (J + 1) = v) then 1 else 0) := by
    intro a _ b _
    simp only [hf]
    by_cases h1 : a = I ∧ b + 1 = J
    · obtain ⟨rfl, rfl⟩ := h1
      simp [show b + 1 - 1 = b by omega]
      all_goals (try split_ifs)
      all_goals omega
    · by_cases h2 : a + 1 = I ∧ b = J
      · obtain ⟨rfl, rfl⟩ := h2
        simp [show a + 1 - 1 = a by omega]
        all_goals (try split_ifs)
        all_goals omega
      · by_cases h3 : a + 1 = I ∧ b = J + 1
        · obtain ⟨rfl, rfl⟩ := h3
          simp [show a + 1 - 1 = a by omega]
          all_goals (try split_ifs)
          all_goals omega
        · rw [if_neg (by tauto)]
          all_goals (try split_ifs)
          all_goals omega
  rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hsplit a ha b hb))]
  simp only [Finset.sum_add_distrib, dsum_pt]
  subst hv hI hJ
  have hIR : i.val < R := i.2
  have hJn : j.val < n := j.2
  have hv2 : A x i.val j.val < 2 := A_lt x _ _ hIR hJn
  congr 1
  · congr 1
    · by_cases h : j.val ≠ 0 ∧ A x i.val (j.val - 1) = A x i.val j.val <;> simp [h, hIR] <;> omega
    · by_cases h : i.val ≠ 0 ∧ A x (i.val - 1) j.val = A x i.val j.val <;> simp [h, hJn] <;> omega
  · by_cases h : i.val ≠ 0 ∧ A x (i.val - 1) (j.val + 1) = A x i.val j.val
    · have hj1 : j.val + 1 < n := by
        by_contra hc
        have := A_out x (i.val - 1) (j.val + 1) (by omega)
        omega
      simp [h, hj1]; omega
    · simp [h]

lemma cond_iff {R n : ℕ} (x : Fin R → Fin n → Fin 2) : Cond x ↔ ∀ i < R, ∀ j < n, okAt x i j := by
  unfold Cond
  constructor
  · intro h i hi j hj
    have := h ⟨i, hi⟩ ⟨j, hj⟩
    rw [eqNbrs_eq] at this
    simp only at this
    have hv := A_lt x i j hi hj
    unfold okAt Bad
    split_ifs at this ⊢ <;> omega
  · intro h i j
    have := h i.val i.2 j.val j.2
    rw [eqNbrs_eq]
    have hv := A_lt x i.val j.val i.2 j.2
    unfold okAt Bad at this
    split_ifs at this ⊢ <;> omega

def absent (R : ℕ) : List ℕ := List.replicate R 2

def col {R n : ℕ} (x : Fin R → Fin n → Fin 2) (j : ℕ) : List ℕ := (List.range R).map (fun i => A x i j)

lemma col_getD {R n : ℕ} (x : Fin R → Fin n → Fin 2) (j i : ℕ) : (col x j).getD i 2 = A x i j := by
  unfold col
  by_cases hi : i < R
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega), A_out x i j (by omega)]

lemma absent_getD (R i : ℕ) : (absent R).getD i 2 = 2 := by
  unfold absent
  by_cases hi : i < R
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma col_ge {R n : ℕ} (x : Fin R → Fin n → Fin 2) (j : ℕ) (hj : n ≤ j) : col x j = absent R := by
  unfold col absent
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact A_out x i j (by omega)

def okCol (R : ℕ) (c p q : List ℕ) : Prop :=
  ∀ i < R, ¬Bad (p.getD i 2) (c.getD i 2) (if i = 0 then 2 else p.getD (i - 1) 2)
    (if i = 0 then 2 else q.getD (i - 1) 2)

instance (R : ℕ) (c p q : List ℕ) : Decidable (okCol R c p q) := by unfold okCol; infer_instance

lemma cond_iff_col {R n : ℕ} (x : Fin R → Fin n → Fin 2) :
    Cond x ↔ ∀ j < n, okCol R (if j = 0 then absent R else col x (j - 1)) (col x j) (col x (j + 1)) := by
  rw [cond_iff]
  constructor
  · intro h j hj i hi
    have := h i hi j hj
    unfold okAt at this
    have e : (if j = 0 then absent R else col x (j - 1)).getD i 2 = if j = 0 then 2 else A x i (j - 1) := by
      split_ifs <;> simp only [absent_getD, col_getD]
    rw [e, col_getD, col_getD, col_getD]
    convert this using 2
    try (split_ifs <;> rfl)
  · intro h i hi j hj
    have := h j hj i hi
    have e : (if j = 0 then absent R else col x (j - 1)).getD i 2 = if j = 0 then 2 else A x i (j - 1) := by
      split_ifs <;> simp only [absent_getD, col_getD]
    rw [e, col_getD, col_getD, col_getD] at this
    unfold okAt
    convert this using 2
    try (split_ifs <;> rfl)

def consA {R n : ℕ} (c : Fin R → Fin 2) (w : Fin R → Fin n → Fin 2) : Fin R → Fin (n + 1) → Fin 2 :=
  fun i => Fin.cons (c i) (w i)

def colOf {R : ℕ} (c : Fin R → Fin 2) : List ℕ :=
  (List.range R).map (fun i => if h : i < R then (c ⟨i, h⟩).val else 2)

lemma A_cons_succ {R n : ℕ} (c : Fin R → Fin 2) (w : Fin R → Fin n → Fin 2) (i j : ℕ) :
    A (consA c w) i (j + 1) = A w i j := by
  unfold A consA
  by_cases h : i < R ∧ j < n
  · rw [dif_pos ⟨h.1, by omega⟩, dif_pos h]
    exact congrArg Fin.val (Fin.cons_succ (α := fun _ => Fin 2) (c ⟨i, h.1⟩) (w ⟨i, h.1⟩) ⟨j, h.2⟩)
  · rw [dif_neg (by omega), dif_neg h]

lemma col_cons_succ {R n : ℕ} (c : Fin R → Fin 2) (w : Fin R → Fin n → Fin 2) (j : ℕ) :
    col (consA c w) (j + 1) = col w j := by
  unfold col; simp only [A_cons_succ]

lemma col_cons_zero {R n : ℕ} (c : Fin R → Fin 2) (w : Fin R → Fin n → Fin 2) :
    col (consA c w) 0 = colOf c := by
  unfold col colOf A consA
  refine List.map_congr_left (fun i hi => ?_)
  rw [List.mem_range] at hi
  rw [dif_pos ⟨hi, by omega⟩, dif_pos hi]
  rfl

def T {R n : ℕ} (w : Fin R → Fin n → Fin 2) : Prop :=
  ∀ j, 1 ≤ j → j < n → okCol R (col w (j - 1)) (col w j) (col w (j + 1))

instance {R n : ℕ} (w : Fin R → Fin n → Fin 2) : Decidable (T w) := by unfold T; infer_instance

lemma cond_T {R n : ℕ} (hn : 1 ≤ n) (w : Fin R → Fin n → Fin 2) :
    Cond w ↔ okCol R (absent R) (col w 0) (col w 1) ∧ T w := by
  rw [cond_iff_col]
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by omega), fun j hj1 hj2 => ?_⟩
    have := h j hj2
    rwa [if_neg (by omega)] at this
  · rintro ⟨h0, h1⟩ j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simpa using h0
    · rw [if_neg (by omega)]; exact h1 j hpos hj

lemma T_cons {R n : ℕ} (c : Fin R → Fin 2) (w : Fin R → Fin n → Fin 2) :
    T (consA c w) ↔ (n = 0 ∨ okCol R (colOf c) (col w 0) (col w 1)) ∧ T w := by
  unfold T
  constructor
  · intro h
    refine ⟨?_, fun j hj1 hj2 => ?_⟩
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · left; exact hn
      · right
        have := h 1 le_rfl (by omega)
        simpa [col_cons_zero, col_cons_succ] using this
    · have := h (j + 1) (by omega) (by omega)
      rw [show j + 1 - 1 = (j - 1) + 1 by omega, col_cons_succ, col_cons_succ, col_cons_succ] at this
      exact this
  · rintro ⟨h0, h1⟩ j hj1 hj2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rcases h0 with h0 | h0
      · omega
      · simpa [col_cons_zero, col_cons_succ] using h0
    · rw [show k + 1 - 1 = (k - 1) + 1 by omega, col_cons_succ, col_cons_succ, col_cons_succ]
      exact h1 k hk (by omega)

def consEquiv (R n : ℕ) : (Fin R → Fin 2) × (Fin R → Fin n → Fin 2) ≃ (Fin R → Fin (n + 1) → Fin 2) where
  toFun cw := consA cw.1 cw.2
  invFun x := (fun i => x i 0, fun i => Fin.tail (x i))
  left_inv cw := by
    obtain ⟨c, w⟩ := cw
    simp only [consA, Fin.cons_zero, Fin.tail_cons]
  right_inv x := by
    funext i
    simp only [consA, Fin.cons_self_tail]

lemma sum_cons {R n : ℕ} (F : (Fin R → Fin (n + 1) → Fin 2) → ℕ) :
    ∑ x, F x = ∑ c : Fin R → Fin 2, ∑ w : Fin R → Fin n → Fin 2, F (consA c w) := by
  rw [← (consEquiv R n).sum_comp, Fintype.sum_prod_type]; rfl

def binCols : ℕ → List (List ℕ)
  | 0 => [[]]
  | R + 1 => (binCols R).flatMap (fun l => [0 :: l, 1 :: l])

def allCols (R : ℕ) : List (List ℕ) := binCols R ++ [absent R]

lemma mem_binCols : ∀ (R : ℕ) (l : List ℕ), l.length = R → (∀ a ∈ l, a < 2) → l ∈ binCols R := by
  intro R
  induction R with
  | zero => intro l hl _; simp [binCols, List.length_eq_zero_iff.mp hl]
  | succ R ih =>
    intro l hl ha
    obtain ⟨b, t, rfl⟩ : ∃ b t, l = b :: t := by
      cases l with
      | nil => simp at hl
      | cons b t => exact ⟨b, t, rfl⟩
    simp only [binCols, List.mem_flatMap, List.mem_cons]
    refine ⟨t, ih t (by simpa using hl) (fun a h => ha a (by simp [h])), ?_⟩
    have := ha b (by simp)
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp

lemma binCols_spec : ∀ (R : ℕ) (l : List ℕ), l ∈ binCols R → l.length = R ∧ ∀ a ∈ l, a < 2 := by
  intro R
  induction R with
  | zero => intro l hl; simp [binCols] at hl; subst hl; simp
  | succ R ih =>
    intro l hl
    simp only [binCols, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at hl
    obtain ⟨t, ht, rfl | rfl⟩ := hl <;>
    · obtain ⟨h1, h2⟩ := ih t ht
      refine ⟨by simp [h1], fun a ha => ?_⟩
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · norm_num
      · exact h2 a ha

lemma col_mem {R n : ℕ} (x : Fin R → Fin n → Fin 2) (j : ℕ) : col x j ∈ allCols R := by
  unfold allCols
  by_cases hj : j < n
  · apply List.mem_append_left
    apply mem_binCols _ _ (by simp [col])
    intro a ha
    simp only [col, List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact A_lt x i j hi hj
  · rw [col_ge x j (by omega)]; simp

lemma colOf_unique {R : ℕ} (c : List ℕ) (hc : c ∈ binCols R) :
    ((Finset.univ : Finset (Fin R → Fin 2)).filter (fun c' => colOf c' = c)).card = 1 := by
  obtain ⟨hl, h2⟩ := binCols_spec R c hc
  rw [Finset.card_eq_one]
  refine ⟨fun i => ⟨c.getD i.val 0, ?_⟩, ?_⟩
  · have hi : i.val < c.length := by omega
    rw [List.getD_eq_getElem _ _ hi]; exact h2 _ (List.getElem_mem hi)
  · ext c'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro rfl
      funext i
      apply Fin.ext
      simp only [colOf]
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    · rintro rfl
      unfold colOf
      apply List.ext_getElem (by simp [hl])
      intro i h1 h2'
      simp only [List.getElem_map, List.getElem_range]
      rw [dif_pos (by simpa using h1)]
      exact List.getD_eq_getElem _ _ (by simpa [hl] using h1)

def S (R n : ℕ) (p q : List ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin R → Fin n → Fin 2)).filter
    (fun w => T w ∧ col w 0 = p ∧ col w 1 = q)).card

lemma S_sum (R n : ℕ) (p q : List ℕ) : S R n p q =
    ∑ w : Fin R → Fin n → Fin 2, if T w ∧ col w 0 = p ∧ col w 1 = q then 1 else 0 := by
  unfold S; rw [Finset.card_filter]

lemma collapse {R : ℕ} (c : List ℕ) (hc : c ∈ binCols R) (G : ℕ) :
    ∑ c' : Fin R → Fin 2, (if colOf c' = c then G else 0) = G := by
  rw [← Finset.sum_filter, Finset.sum_const, colOf_unique c hc, one_smul]

lemma fiber {R n : ℕ} (P : (Fin R → Fin n → Fin 2) → Prop) [DecidablePred P] (c p : List ℕ) :
    ∑ w : Fin R → Fin n → Fin 2, (if okCol R c p (col w 1) ∧ P w then 1 else 0) =
      ∑ q ∈ (allCols R).toFinset, if okCol R c p q then
        ∑ w : Fin R → Fin n → Fin 2, (if P w ∧ col w 1 = q then 1 else 0) else 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := (allCols R).toFinset)
    (g := fun w => col w 1) (fun w _ => by simpa using col_mem w 1)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_filter]
  split_ifs with hq
  · refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : col w 1 = q
    · simp [h, hq]
    · simp [h]
  · apply Finset.sum_eq_zero
    intro w _
    by_cases h : col w 1 = q
    · simp [h, hq]
    · simp [h]

lemma S_succ (R n : ℕ) (hn : 1 ≤ n) (c : List ℕ) (hc : c ∈ binCols R) (p : List ℕ) :
    S R (n + 1) c p = ∑ q ∈ (allCols R).toFinset, if okCol R c p q then S R n p q else 0 := by
  rw [S_sum, sum_cons]
  have h1 : ∀ (c' : Fin R → Fin 2) (w : Fin R → Fin n → Fin 2),
      (if T (consA c' w) ∧ col (consA c' w) 0 = c ∧ col (consA c' w) 1 = p then 1 else 0) =
      if colOf c' = c then (if okCol R c p (col w 1) ∧ (T w ∧ col w 0 = p) then 1 else 0) else 0 := by
    intro c' w
    have e1 : col (consA c' w) 1 = col w 0 := col_cons_succ c' w 0
    simp only [T_cons, col_cons_zero, e1, show n ≠ 0 by omega, false_or]
    by_cases hc' : colOf c' = c
    · subst hc'
      by_cases h2 : col w 0 = p
      · subst h2; simp
      · simp [h2]
    · simp [hc']
  simp only [h1]
  have h2 : ∀ c' : Fin R → Fin 2, (∑ w : Fin R → Fin n → Fin 2, if colOf c' = c then
      (if okCol R c p (col w 1) ∧ (T w ∧ col w 0 = p) then 1 else 0) else 0) =
      if colOf c' = c then ∑ w : Fin R → Fin n → Fin 2,
        (if okCol R c p (col w 1) ∧ (T w ∧ col w 0 = p) then 1 else 0) else 0 := by
    intro c'; split_ifs <;> simp
  simp only [h2, collapse c hc]
  rw [fiber (fun w => T w ∧ col w 0 = p)]
  simp only [S_sum, and_assoc]

lemma S_one (R : ℕ) (c : List ℕ) (hc : c ∈ binCols R) (p : List ℕ) :
    S R 1 c p = if p = absent R then 1 else 0 := by
  rw [S_sum, sum_cons]
  have h1 : ∀ (c' : Fin R → Fin 2) (w : Fin R → Fin 0 → Fin 2),
      (if T (consA c' w) ∧ col (consA c' w) 0 = c ∧ col (consA c' w) 1 = p then 1 else 0) =
      if colOf c' = c then (if p = absent R then 1 else 0) else 0 := by
    intro c' w
    have e1 : col (consA c' w) 1 = col w 0 := col_cons_succ c' w 0
    have hT : T w := fun j hj1 hj2 => by omega
    simp only [T_cons, col_cons_zero, e1, col_ge w 0 le_rfl, hT, true_or, true_and]
    by_cases hc' : colOf c' = c <;> by_cases hp : p = absent R <;> simp [hc', hp] <;> (try exact fun h => hp h.symm)
  simp only [h1, Fintype.sum_unique]
  exact collapse c hc _

lemma rmn_iff {R n : ℕ} (hR : 1 ≤ R) (hn : 1 ≤ n) (x : Fin R → Fin n → Fin 2) :
    RowMajorNew x ↔ A x 0 0 = 0 := by
  have hA : A x 0 0 = (x ⟨0, by omega⟩ ⟨0, by omega⟩).val := A_fin x ⟨0, by omega⟩ ⟨0, by omega⟩
  constructor
  · intro h
    by_contra hne
    obtain ⟨i', j', hij, _⟩ := h ⟨0, by omega⟩ ⟨0, by omega⟩ 0 (by
      rw [Fin.lt_def]; simp only [Fin.val_zero]; omega)
    rcases hij with h1 | ⟨_, h2⟩
    · exact absurd h1 (by simp [Fin.lt_def])
    · exact absurd h2 (by simp [Fin.lt_def])
  · intro h0 i j u hu
    refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ?_, ?_⟩
    · by_contra hc
      have hi : i.val = 0 := by
        by_contra hi'; exact hc (Or.inl (by rw [Fin.lt_def]; simp; omega))
      have hj : j.val = 0 := by
        by_contra hj'; exact hc (Or.inr ⟨Fin.ext (by simp [hi]), by rw [Fin.lt_def]; simp; omega⟩)
      have : x i j = x ⟨0, by omega⟩ ⟨0, by omega⟩ := by
        congr 1 <;> apply Fin.ext <;> simp [hi, hj]
      rw [Fin.lt_def, this] at hu
      omega
    · have := u.isLt; have := (x i j).isLt
      rw [Fin.lt_def] at hu
      apply Fin.ext; omega

lemma fiber2 {R n : ℕ} (P : List ℕ → List ℕ → Prop) [∀ p q, Decidable (P p q)] :
    ∑ x : Fin R → Fin n → Fin 2, (if P (col x 0) (col x 1) ∧ T x then 1 else 0) =
      ∑ p ∈ (allCols R).toFinset, ∑ q ∈ (allCols R).toFinset, if P p q then S R n p q else 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := (allCols R).toFinset)
    (g := fun x => col x 0) (fun x _ => by simpa using col_mem x 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x => col x 0 = p))
    (t := (allCols R).toFinset) (g := fun x => col x 1) (fun x _ => by simpa using col_mem x 1)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.filter_filter, Finset.sum_filter, S_sum]
  split_ifs with hpq
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h0 : col x 0 = p <;> by_cases h1 : col x 1 = q
    · subst h0 h1; simp [hpq]
    all_goals simp [h0, h1]
  · rw [Finset.sum_eq_zero]
    intro x _
    by_cases h0 : col x 0 = p <;> by_cases h1 : col x 1 = q
    · subst h0 h1; simp [hpq]
    all_goals simp [h0, h1]

/-- the computable transfer -/
def Sv (R : ℕ) : ℕ → List ℕ → List ℕ → ℕ
  | 0, _, _ => 0
  | 1, _, p => if p = absent R then 1 else 0
  | n + 2, c, p => ((allCols R).map (fun q => if okCol R c p q then Sv R (n + 1) p q else 0)).sum

lemma okCol_absent (R : ℕ) (hR : 1 ≤ R) (c q : List ℕ) : ¬okCol R c (absent R) q := by
  intro h
  have := h 0 (by omega)
  simp only [absent_getD, if_true] at this
  exact this (Or.inr (Or.inr ⟨rfl, rfl⟩))

lemma S_eq_Sv (R : ℕ) (hR : 1 ≤ R) (hnd : (allCols R).Nodup) :
    ∀ n, 1 ≤ n → ∀ c ∈ binCols R, ∀ p ∈ allCols R, S R n c p = Sv R n c p := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro c hc p _; rw [S_one R c hc]; rfl
  | succ n hn ih =>
    intro c hc p hp
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [S_succ R (m + 1) hn c hc p]
    show _ = ((allCols R).map (fun q => if okCol R c p q then Sv R (m + 1) p q else 0)).sum
    rw [← List.sum_toFinset _ hnd]
    refine Finset.sum_congr rfl fun q hq => ?_
    split_ifs with hok
    · have hpb : p ∈ binCols R := by
        unfold allCols at hp
        rcases List.mem_append.mp hp with h | h
        · exact h
        · simp at h; subst h; exact absurd hok (okCol_absent R hR c q)
      exact ih p hpb q (by simpa using hq)
    · rfl

def cc : ℕ → ℤ := fun k => [1, -6, 14, -16, 9, -2].getD k 0

def Wv (m : ℕ) (c p : List ℕ) : ℤ := ∑ k ∈ range 6, cc k * (Sv 5 (m + 5 - k) c p : ℤ)

def aLv (n : ℕ) : ℕ := ((allCols 5).map (fun p => ((allCols 5).map (fun q =>
  if p.getD 0 2 = 0 ∧ okCol 5 (absent 5) p q then Sv 5 n p q else 0)).sum)).sum

lemma nd5 : (allCols 5).Nodup := by decide +kernel

lemma W4 : ∀ c ∈ allCols 5, ∀ p ∈ allCols 5, Wv 4 c p = 0 := by decide +kernel

lemma vals : aLv 1 = 16 ∧ aLv 2 = 89 ∧ aLv 3 = 284 ∧ aLv 4 = 722 ∧ aLv 5 = 1652 ∧ aLv 6 = 3577 ∧
    aLv 7 = 7504 ∧ aLv 8 = 15448 := by
  decide +kernel

lemma Sv_step (n : ℕ) (c p : List ℕ) : (Sv 5 (n + 2) c p : ℤ) =
    ∑ q ∈ (allCols 5).toFinset, if okCol 5 c p q then (Sv 5 (n + 1) p q : ℤ) else 0 := by
  show (((allCols 5).map (fun q => if okCol 5 c p q then Sv 5 (n + 1) p q else 0)).sum : ℤ) = _
  rw [← List.sum_toFinset _ nd5]
  push_cast
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

lemma Wv_succ (m : ℕ) (hm : 1 ≤ m) (c p : List ℕ) :
    Wv (m + 1) c p = ∑ q ∈ (allCols 5).toFinset, if okCol 5 c p q then Wv m p q else 0 := by
  unfold Wv
  have h : ∀ k ∈ range 6, cc k * (Sv 5 (m + 1 + 5 - k) c p : ℤ) = ∑ q ∈ (allCols 5).toFinset,
      cc k * (if okCol 5 c p q then (Sv 5 (m + 5 - k) p q : ℤ) else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show m + 1 + 5 - k = (m + 4 - k) + 2 by omega, Sv_step, show m + 4 - k + 1 = m + 5 - k by omega,
      Finset.mul_sum]
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

lemma W_zero : ∀ m, 4 ≤ m → ∀ c ∈ allCols 5, ∀ p ∈ allCols 5, Wv m c p = 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact W4
  | succ m hm ih =>
    intro c _ p hp
    rw [Wv_succ m (by omega)]
    apply Finset.sum_eq_zero
    intro q hq
    split_ifs
    · exact ih p hp q (by simpa using hq)
    · rfl

lemma aLv_fin (n : ℕ) : (aLv n : ℤ) = ∑ p ∈ (allCols 5).toFinset, ∑ q ∈ (allCols 5).toFinset,
    if p.getD 0 2 = 0 ∧ okCol 5 (absent 5) p q then (Sv 5 n p q : ℤ) else 0 := by
  have e : aLv n = ∑ p ∈ (allCols 5).toFinset, ∑ q ∈ (allCols 5).toFinset,
      (if p.getD 0 2 = 0 ∧ okCol 5 (absent 5) p q then Sv 5 n p q else 0) := by
    unfold aLv
    rw [← List.sum_toFinset _ nd5]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← List.sum_toFinset _ nd5]
  rw [e]
  push_cast
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

lemma aLv_rec (m : ℕ) (hm : 4 ≤ m) : ∑ k ∈ range 6, cc k * (aLv (m + 5 - k) : ℤ) = 0 := by
  simp only [aLv_fin, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro q hq
  by_cases h : p.getD 0 2 = 0 ∧ okCol 5 (absent 5) p q
  · simp only [h, and_self, if_true]
    have := W_zero m hm p (by simpa using hp) q (by simpa using hq)
    unfold Wv at this
    exact this
  · simp only [h, if_false, mul_zero, Finset.sum_const_zero]

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = aLv n := by
  have h1 : a n = ∑ x : Fin 5 → Fin n → Fin 2,
      (if (fun p q => p.getD 0 2 = 0 ∧ okCol 5 (absent 5) p q) (col x 0) (col x 1) ∧ T x then 1 else 0) := by
    unfold a
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e : (Cond x ∧ RowMajorNew x) ↔ ((col x 0).getD 0 2 = 0 ∧ okCol 5 (absent 5) (col x 0) (col x 1)) ∧ T x := by
      rw [cond_T hn, rmn_iff (by norm_num) hn, col_getD]; tauto
    simp only [e]
  rw [h1, fiber2 (fun p q => p.getD 0 2 = 0 ∧ okCol 5 (absent 5) p q)]
  have : (aLv n : ℤ) = ((∑ p ∈ (allCols 5).toFinset, ∑ q ∈ (allCols 5).toFinset,
      if p.getD 0 2 = 0 ∧ okCol 5 (absent 5) p q then S 5 n p q else 0 : ℕ) : ℤ) := by
    rw [aLv_fin]
    push_cast
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    split_ifs with h
    · have hpb : p ∈ binCols 5 := by
        have hp' : p ∈ allCols 5 := by simpa using hp
        unfold allCols at hp'
        rcases List.mem_append.mp hp' with h' | h'
        · exact h'
        · simp at h'; subst h'; rw [absent_getD] at h; omega
      rw [S_eq_Sv 5 (by norm_num) nd5 n hn p hpb q (by simpa using hq)]
    · rfl
  exact_mod_cast this.symm

end OMA.Helpers_a208640

open OMA.S_oeis_a208640 OMA.Helpers_a208640 in
theorem OMA.solution : type_of% @OMA.S_oeis_a208640.main := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := vals
  have hrec : ∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 14 * a (n - 2) + 16 * a (n - 3) -
      9 * a (n - 4) + 2 * a (n - 5) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h := aLv_rec m (by omega)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cc, List.getD_cons_zero,
      List.getD_cons_succ, Nat.sub_zero] at h
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega,
      show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega] at h ⊢
    rw [a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega),
      a_eq _ (by omega)]
    linear_combination h
  have hcf : ∀ n : ℕ, 2 < n → (a n : ℚ) = -84 + 63 * 2 ^ n - 191 * n / 6 - 4 * n ^ 2 - n ^ 3 / 6 := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | h9
      · rw [a_eq 3 (by norm_num), v3]; norm_num
      · rw [a_eq 4 (by norm_num), v4]; norm_num
      · rw [a_eq 5 (by norm_num), v5]; norm_num
      · rw [a_eq 6 (by norm_num), v6]; norm_num
      · rw [a_eq 7 (by norm_num), v7]; norm_num
      · rw [a_eq 8 (by norm_num), v8]; norm_num
      · have h := hrec n h9
        have h' : (a n : ℚ) = 6 * a (n - 1) - 14 * a (n - 2) + 16 * a (n - 3) - 9 * a (n - 4) +
            2 * a (n - 5) := by exact_mod_cast h
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
        rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
          show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega] at h'
        rw [h', ih (m + 4) (by omega) (by omega), ih (m + 3) (by omega) (by omega),
          ih (m + 2) (by omega) (by omega), ih (m + 1) (by omega) (by omega), ih m (by omega) (by omega)]
        push_cast
        ring
  refine ⟨?_, hcf⟩
  have a1 : (a 1 : ℚ) = 16 := by rw [a_eq 1 le_rfl, v1]; norm_num
  have a2 : (a 2 : ℚ) = 89 := by rw [a_eq 2 (by norm_num), v2]; norm_num
  have a3 : (a 3 : ℚ) = 284 := by rw [a_eq 3 (by norm_num), v3]; norm_num
  have a4 : (a 4 : ℚ) = 722 := by rw [a_eq 4 (by norm_num), v4]; norm_num
  have a5 : (a 5 : ℚ) = 1652 := by rw [a_eq 5 (by norm_num), v5]; norm_num
  have a6 : (a 6 : ℚ) = 3577 := by rw [a_eq 6 (by norm_num), v6]; norm_num
  have a7 : (a 7 : ℚ) = 7504 := by rw [a_eq 7 (by norm_num), v7]; norm_num
  have a8 : (a 8 : ℚ) = 15448 := by rw [a_eq 8 (by norm_num), v8]; norm_num
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hF
  have hL : F * ((1 - PowerSeries.X) ^ 4 * (1 - 2 * PowerSeries.X)) = F - 6 * (F * PowerSeries.X ^ 1) +
      14 * (F * PowerSeries.X ^ 2) - 16 * (F * PowerSeries.X ^ 3) + 9 * (F * PowerSeries.X ^ 4) -
      2 * (F * PowerSeries.X ^ 5) := by ring
  have hR : (PowerSeries.X * (16 - 7 * PowerSeries.X - 26 * PowerSeries.X ^ 2 + 8 * PowerSeries.X ^ 3 +
      16 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 - 4 * PowerSeries.X ^ 6) : PowerSeries ℚ) =
      16 * PowerSeries.X ^ 1 - 7 * PowerSeries.X ^ 2 - 26 * PowerSeries.X ^ 3 + 8 * PowerSeries.X ^ 4 +
        16 * PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 6 - 4 * PowerSeries.X ^ 7 := by ring
  rw [hL, hR]
  ext d
  simp only [map_add, map_sub, ← map_ofNat PowerSeries.C, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow', hF, PowerSeries.coeff_mk]
  rcases (show d ≤ 8 ∨ 9 ≤ d by omega) with hd | hd
  · interval_cases d <;> simp only [PowerSeries.coeff_C, a1, a2, a3, a4, a5, a6, a7, a8] <;>
      norm_num [a1, a2, a3, a4, a5, a6, a7, a8]
  · have h := hrec d hd
    have h' : (a d : ℚ) = 6 * a (d - 1) - 14 * a (d - 2) + 16 * a (d - 3) - 9 * a (d - 4) +
        2 * a (d - 5) := by exact_mod_cast h
    have c1 : 1 ≤ d := by omega
    have c2 : 2 ≤ d := by omega
    have c3 : 3 ≤ d := by omega
    have c4 : 4 ≤ d := by omega
    have c5 : 5 ≤ d := by omega
    have n0 : d ≠ 0 := by omega
    have n1 : d - 1 ≠ 0 := by omega
    have n2 : d - 2 ≠ 0 := by omega
    have n3 : d - 3 ≠ 0 := by omega
    have n4 : d - 4 ≠ 0 := by omega
    have n5 : d - 5 ≠ 0 := by omega
    have z6 : d - 6 ≠ 0 := by omega
    have z7 : d - 7 ≠ 0 := by omega
    have m1 : d ≠ 1 := by omega
    have m2 : d ≠ 2 := by omega
    have m3 : d ≠ 3 := by omega
    have m4 : d ≠ 4 := by omega
    have m5 : d ≠ 5 := by omega
    have m6 : d ≠ 6 := by omega
    have m7 : d ≠ 7 := by omega
    simp only [c1, c2, c3, c4, c5, n0, n1, n2, n3, n4, n5, z6, z7,
      PowerSeries.coeff_C, ↓reduceIte, ite_self]
    linear_combination h'
