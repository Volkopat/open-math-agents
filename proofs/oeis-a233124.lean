import OMAStatements.S_oeis_a233124

open OMA.S_oeis_a233124 PowerSeries

namespace A233124Proof

-- A row of the array: one letter of the row by row scan.
abbrev Row := Fin 3 → Fin 6

-- The value u must appear before the value v.
def Req (u v : Fin 6) : Prop :=
  (u.val = 1 ∧ 2 ≤ v.val ∧ v.val ≤ 4) ∨ (u.val = 2 ∧ v.val = 3)

instance (u v : Fin 6) : Decidable (Req u v) := by unfold Req; infer_instance

theorem req_bounds {u v : Fin 6} (h : Req u v) : 1 ≤ u.val ∧ u.val ≤ 2 := by
  unfold Req at h; omega

-- The conditions linking a row r to the row p above it (none for the top row).
def upOK (p : Option Row) (r : Row) : Prop :=
  match p with
  | none => r 0 = 0
  | some q => ∀ j, ¬ Clash (q j) (r j)

instance (p : Option Row) (r : Row) : Decidable (upOK p r) := by
  cases p <;> unfold upOK <;> infer_instance

-- A new row r below the row p, when the values 1..t have been seen already.
def rowOK (t : ℕ) (p : Option Row) (r : Row) : Prop :=
  (∀ j j' : Fin 3, j.val + 1 = j'.val → ¬ Clash (r j) (r j')) ∧ upOK p r ∧ ∀ j u, Req u (r j) → u.val ≤ t ∨ ∃ j' < j, r j' = u

instance (t : ℕ) (p : Option Row) (r : Row) : Decidable (rowOK t p r) := by
  unfold rowOK; infer_instance

def lvl (v : Fin 6) : ℕ := if v.val ≤ 2 then v.val else 0

-- The level of seen values after the row r.
def newT (t : ℕ) (r : Row) : ℕ := max t (max (lvl (r 0)) (max (lvl (r 1)) (lvl (r 2))))

-- The conditions on a block of rows below the row p, the values 1..t being seen already.
def ExtOK (t : ℕ) (p : Option Row) {n : ℕ} (A : Fin n → Row) : Prop :=
  (∀ i, ∀ j j' : Fin 3, j.val + 1 = j'.val → ¬ Clash (A i j) (A i j')) ∧
  (∀ i i' : Fin n, i.val + 1 = i'.val → ∀ j, ¬ Clash (A i j) (A i' j)) ∧
  (∀ i : Fin n, i.val = 0 → upOK p (A i)) ∧
  (∀ i j u, Req u (A i j) → u.val ≤ t ∨ Before A i j u)

theorem order_iff {n : ℕ} (A : Fin n → Row) :
    OrderOK A ↔ ∀ i j u, Req u (A i j) → u.val ≤ 0 ∨ Before A i j u := by
  constructor
  · intro h i j u hu
    obtain ⟨h1, h2⟩ := h i j
    right
    rcases hu with ⟨hu, a, b⟩ | ⟨hu, a⟩
    · rw [show u = 1 from Fin.ext hu]; exact h1 a b
    · rw [show u = 2 from Fin.ext hu]; exact h2 a
  · intro h i j
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rcases h i j 1 (Or.inl ⟨rfl, a, b⟩) with h' | h'
      · exact absurd h' (by decide)
      · exact h'
    · rcases h i j 2 (Or.inr ⟨rfl, a⟩) with h' | h'
      · exact absurd h' (by decide)
      · exact h'

theorem valid_iff {n : ℕ} (A : Fin n → Row) : Valid A ↔ ExtOK 0 none A := by
  unfold Valid NoClash ExtOK
  rw [order_iff]
  simp only [upOK]
  constructor
  · rintro ⟨⟨h1, h2⟩, h4, h5⟩
    exact ⟨h1, h2, h4, h5⟩
  · rintro ⟨h1, h2, h4, h5⟩
    exact ⟨⟨h1, h2⟩, h4, h5⟩

theorem hor_cons {n : ℕ} (r : Row) (B : Fin n → Row) :
    (∀ i : Fin (n + 1), ∀ j j' : Fin 3, j.val + 1 = j'.val →
      ¬ Clash ((Fin.cons r B : Fin (n + 1) → Row) i j) ((Fin.cons r B : Fin (n + 1) → Row) i j')) ↔
    (∀ j j' : Fin 3, j.val + 1 = j'.val → ¬ Clash (r j) (r j')) ∧
      ∀ i, ∀ j j' : Fin 3, j.val + 1 = j'.val → ¬ Clash (B i j) (B i j') := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem ver_cons {n : ℕ} (r : Row) (B : Fin n → Row) :
    (∀ i i' : Fin (n + 1), i.val + 1 = i'.val → ∀ j,
      ¬ Clash ((Fin.cons r B : Fin (n + 1) → Row) i j) ((Fin.cons r B : Fin (n + 1) → Row) i' j)) ↔
    (∀ i : Fin n, i.val = 0 → ∀ j, ¬ Clash (r j) (B i j)) ∧
      (∀ i i' : Fin n, i.val + 1 = i'.val → ∀ j, ¬ Clash (B i j) (B i' j)) := by
  constructor
  · intro h
    refine ⟨fun i hi j => ?_, fun i i' hii' j => ?_⟩
    · have := h 0 i.succ (by simp [hi]) j
      simpa using this
    · have := h i.succ i'.succ (by simp [hii']) j
      simpa using this
  · rintro ⟨h1, h2⟩ i i' hii' j
    cases i using Fin.cases with
    | zero =>
      cases i' using Fin.cases with
      | zero => simp at hii'
      | succ k =>
        simp only [Fin.val_zero, Fin.val_succ] at hii'
        simpa using h1 k (by omega) j
    | succ k =>
      cases i' using Fin.cases with
      | zero => simp at hii'
      | succ k' =>
        simp only [Fin.val_succ] at hii'
        simpa using h2 k k' (by omega) j

theorem up_cons (p : Option Row) {n : ℕ} (r : Row) (B : Fin n → Row) :
    (∀ i : Fin (n + 1), i.val = 0 → upOK p ((Fin.cons r B : Fin (n + 1) → Row) i)) ↔
      upOK p r := by
  rw [Fin.forall_fin_succ]
  simp

theorem ord_cons (t : ℕ) {n : ℕ} (r : Row) (B : Fin n → Row) :
    (∀ (i : Fin (n + 1)) j u, Req u ((Fin.cons r B : Fin (n + 1) → Row) i j) →
      u.val ≤ t ∨ Before (Fin.cons r B : Fin (n + 1) → Row) i j u) ↔
    (∀ j u, Req u (r j) → u.val ≤ t ∨ ∃ j' < j, r j' = u) ∧
    (∀ i j u, Req u (B i j) → (u.val ≤ t ∨ ∃ j', r j' = u) ∨ Before B i j u) := by
  simp only [Before]
  simp only [Fin.forall_fin_succ (n := n), Fin.exists_fin_succ (n := n), Fin.cons_zero,
    Fin.cons_succ]
  simp [Fin.succ_lt_succ_iff, Fin.succ_pos, or_assoc]

theorem newT_spec (t : ℕ) (r : Row) (h : ∀ j u, Req u (r j) → u.val ≤ t ∨ ∃ j' < j, r j' = u)
    (u : Fin 6) (hu : 1 ≤ u.val ∧ u.val ≤ 2) :
    (u.val ≤ t ∨ ∃ j', r j' = u) ↔ u.val ≤ newT t r := by
  by_cases ht : 2 ≤ t
  · have : t ≤ newT t r := le_max_left _ _
    exact ⟨fun _ => by omega, fun _ => Or.inl (by omega)⟩
  · have key : ∀ t : Fin 2, ∀ r : Row,
        (∀ j u, Req u (r j) → u.val ≤ t.val ∨ ∃ j' < j, r j' = u) →
        ∀ u : Fin 6, 1 ≤ u.val ∧ u.val ≤ 2 →
          ((u.val ≤ t.val ∨ ∃ j', r j' = u) ↔ u.val ≤ newT t.val r) := by
      decide +kernel
    exact key ⟨t, by omega⟩ r h u hu

theorem ext_cons (t : ℕ) (p : Option Row) {n : ℕ} (r : Row) (B : Fin n → Row) :
    ExtOK t p (Fin.cons r B : Fin (n + 1) → Row) ↔ rowOK t p r ∧ ExtOK (newT t r) (some r) B := by
  unfold ExtOK rowOK
  rw [hor_cons, ver_cons, up_cons, ord_cons]
  simp only [upOK]
  constructor
  · rintro ⟨⟨h1, h1'⟩, ⟨h3, h3'⟩, h4, ⟨h5, h5'⟩⟩
    refine ⟨⟨h1, h4, h5⟩, h1', h3', h3, fun i j u hu => ?_⟩
    rcases h5' i j u hu with h | h
    · exact Or.inl ((newT_spec t r h5 u (req_bounds hu)).1 h)
    · exact Or.inr h
  · rintro ⟨⟨h1, h4, h5⟩, h1', h3', h6, h5'⟩
    refine ⟨⟨h1, h1'⟩, ⟨h6, h3'⟩, h4, ⟨h5, fun i j u hu => ?_⟩⟩
    rcases h5' i j u hu with h | h
    · exact Or.inl ((newT_spec t r h5 u (req_bounds hu)).2 h)
    · exact Or.inr h

instance (t : ℕ) (p : Option Row) {n : ℕ} (A : Fin n → Row) : Decidable (ExtOK t p A) := by
  unfold ExtOK; infer_instance

def F (t : ℕ) (p : Option Row) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n → Row => ExtOK t p A).card


theorem F_succ (t : ℕ) (p : Option Row) (n : ℕ) :
    F t p (n + 1) = ∑ r : Row, if rowOK t p r then F (newT t r) (some r) n else 0 := by
  rw [F, Finset.card_filter, ← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, ext_cons]
  by_cases h : rowOK t p r
  · rw [if_pos h, F, Finset.card_filter]
    exact Finset.sum_congr rfl fun B _ => by simp [h]
  · simp [h]

def cnt : ℕ → ℕ → Option Row → ℕ
  | 0, _, _ => 1
  | n + 1, t, p => ∑ r : Row, if rowOK t p r then cnt n (newT t r) (some r) else 0

theorem cnt_succ (n t : ℕ) (p : Option Row) :
    cnt (n + 1) t p = ∑ r : Row, if rowOK t p r then cnt n (newT t r) (some r) else 0 := by
  rw [cnt]

theorem F_eq (n : ℕ) : ∀ t p, F t p n = cnt n t p := by
  induction n with
  | zero =>
    intro t p
    rw [F, Finset.filter_true_of_mem (fun A _ => ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩)]
    simp [cnt]
  | succ n ih =>
    intro t p
    rw [F_succ, cnt_succ]
    simp only [ih]

theorem a_eq (n : ℕ) : a n = cnt n 0 none := by
  rw [← F_eq, a, F, Finset.filter_congr (fun A _ => valid_iff A)]

def W (n t : ℕ) (p : Option Row) : ℤ :=
  (cnt (n + 3) t p : ℤ) - 48 * cnt (n + 2) t p + 448 * cnt (n + 1) t p - 1024 * cnt n t p

theorem W_succ (n t : ℕ) (p : Option Row) :
    W (n + 1) t p = ∑ r : Row, if rowOK t p r then W n (newT t r) (some r) else 0 := by
  simp only [W, show n + 1 + 3 = n + 3 + 1 by ring, show n + 1 + 2 = n + 2 + 1 by ring]
  rw [cnt_succ (n + 3) t p, cnt_succ (n + 2) t p, cnt_succ (n + 1) t p, cnt_succ n t p]
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : rowOK t p r
  · simp only [if_pos h]
  · simp only [if_neg h]; ring

-- The states that occur: the previous row uses values allowed at level t and reaching at most t.
def P (t : ℕ) (q : Row) : Prop := ∀ j, (∀ u, Req u (q j) → u.val ≤ t) ∧ lvl (q j) ≤ t

instance (t : ℕ) (q : Row) : Decidable (P t q) := by unfold P; infer_instance

theorem P_next_key : ∀ t : Fin 3, ∀ r : Row,
    (∀ j u, Req u (r j) → u.val ≤ t.val ∨ ∃ j' < j, r j' = u) →
      P (newT t.val r) r ∧ newT t.val r ≤ 2 := by
  decide +kernel

theorem P_next (t : ℕ) (p : Option Row) (r : Row) (h : rowOK t p r) (h1 : 1 ≤ t) (h3 : t ≤ 2) :
    1 ≤ newT t r ∧ newT t r ≤ 2 ∧ P (newT t r) r :=
  ⟨le_trans h1 (le_max_left _ _), (P_next_key ⟨t, by omega⟩ r h.2.2).2,
    (P_next_key ⟨t, by omega⟩ r h.2.2).1⟩

theorem top_next : ∀ r : Row, rowOK 0 none r →
    1 ≤ newT 0 r ∧ newT 0 r ≤ 2 ∧ P (newT 0 r) r := by
  decide +kernel

def tbl1L : List (List (List (List ℕ))) :=
  [[[[8, 12, 0, 0, 12, 8], [24, 12, 0, 0, 12, 24], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [24, 12, 0, 0, 12, 24], [8, 12, 0, 0, 12, 8]],
    [[12, 24, 0, 0, 24, 12], [12, 8, 0, 0, 8, 12], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [12, 8, 0, 0, 8, 12], [12, 24, 0, 0, 24, 12]],
    [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]],
    [[12, 24, 0, 0, 24, 12], [12, 8, 0, 0, 8, 12], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [12, 8, 0, 0, 8, 12], [12, 24, 0, 0, 24, 12]],
    [[8, 12, 0, 0, 12, 8], [24, 12, 0, 0, 12, 24], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [24, 12, 0, 0, 12, 24], [8, 12, 0, 0, 12, 8]]],
  [[[16, 24, 24, 24, 24, 16], [40, 24, 32, 32, 24, 40], [40, 32, 24, 24, 32, 40], [40, 32, 24, 24, 32, 40], [40, 24, 32, 32, 24, 40], [16, 24, 24, 24, 24, 16]],
    [[24, 40, 32, 32, 40, 24], [24, 16, 24, 24, 16, 24], [32, 40, 24, 24, 40, 32], [32, 40, 24, 24, 40, 32], [24, 16, 24, 24, 16, 24], [24, 40, 32, 32, 40, 24]],
    [[24, 32, 40, 40, 32, 24], [32, 24, 40, 40, 24, 32], [24, 24, 16, 16, 24, 24], [24, 24, 16, 16, 24, 24], [32, 24, 40, 40, 24, 32], [24, 32, 40, 40, 32, 24]],
    [[24, 32, 40, 40, 32, 24], [32, 24, 40, 40, 24, 32], [24, 24, 16, 16, 24, 24], [24, 24, 16, 16, 24, 24], [32, 24, 40, 40, 24, 32], [24, 32, 40, 40, 32, 24]],
    [[24, 40, 32, 32, 40, 24], [24, 16, 24, 24, 16, 24], [32, 40, 24, 24, 40, 32], [32, 40, 24, 24, 40, 32], [24, 16, 24, 24, 16, 24], [24, 40, 32, 32, 40, 24]],
    [[16, 24, 24, 24, 24, 16], [40, 24, 32, 32, 24, 40], [40, 32, 24, 24, 32, 40], [40, 32, 24, 24, 32, 40], [40, 24, 32, 32, 24, 40], [16, 24, 24, 24, 24, 16]]]]

def tbl2L : List (List (List (List ℕ))) :=
  [[[[320, 416, 0, 0, 416, 320], [768, 416, 0, 0, 416, 768], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [768, 416, 0, 0, 416, 768], [320, 416, 0, 0, 416, 320]],
    [[416, 768, 0, 0, 768, 416], [416, 320, 0, 0, 320, 416], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [416, 320, 0, 0, 320, 416], [416, 768, 0, 0, 768, 416]],
    [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]],
    [[416, 768, 0, 0, 768, 416], [416, 320, 0, 0, 320, 416], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [416, 320, 0, 0, 320, 416], [416, 768, 0, 0, 768, 416]],
    [[320, 416, 0, 0, 416, 320], [768, 416, 0, 0, 416, 768], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [768, 416, 0, 0, 416, 768], [320, 416, 0, 0, 416, 320]]],
  [[[640, 832, 832, 832, 832, 640], [1472, 832, 1152, 1152, 832, 1472], [1472, 1152, 832, 832, 1152, 1472], [1472, 1152, 832, 832, 1152, 1472], [1472, 832, 1152, 1152, 832, 1472], [640, 832, 832, 832, 832, 640]],
    [[832, 1472, 1152, 1152, 1472, 832], [832, 640, 832, 832, 640, 832], [1152, 1472, 832, 832, 1472, 1152], [1152, 1472, 832, 832, 1472, 1152], [832, 640, 832, 832, 640, 832], [832, 1472, 1152, 1152, 1472, 832]],
    [[832, 1152, 1472, 1472, 1152, 832], [1152, 832, 1472, 1472, 832, 1152], [832, 832, 640, 640, 832, 832], [832, 832, 640, 640, 832, 832], [1152, 832, 1472, 1472, 832, 1152], [832, 1152, 1472, 1472, 1152, 832]],
    [[832, 1152, 1472, 1472, 1152, 832], [1152, 832, 1472, 1472, 832, 1152], [832, 832, 640, 640, 832, 832], [832, 832, 640, 640, 832, 832], [1152, 832, 1472, 1472, 832, 1152], [832, 1152, 1472, 1472, 1152, 832]],
    [[832, 1472, 1152, 1152, 1472, 832], [832, 640, 832, 832, 640, 832], [1152, 1472, 832, 832, 1472, 1152], [1152, 1472, 832, 832, 1472, 1152], [832, 640, 832, 832, 640, 832], [832, 1472, 1152, 1152, 1472, 832]],
    [[640, 832, 832, 832, 832, 640], [1472, 832, 1152, 1152, 832, 1472], [1472, 1152, 832, 832, 1152, 1472], [1472, 1152, 832, 832, 1152, 1472], [1472, 832, 1152, 1152, 832, 1472], [640, 832, 832, 832, 832, 640]]]]

def tbl3L : List (List (List (List ℕ))) :=
  [[[[11776, 15104, 0, 0, 15104, 11776], [27136, 15104, 0, 0, 15104, 27136], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [27136, 15104, 0, 0, 15104, 27136], [11776, 15104, 0, 0, 15104, 11776]],
    [[15104, 27136, 0, 0, 27136, 15104], [15104, 11776, 0, 0, 11776, 15104], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [15104, 11776, 0, 0, 11776, 15104], [15104, 27136, 0, 0, 27136, 15104]],
    [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]],
    [[15104, 27136, 0, 0, 27136, 15104], [15104, 11776, 0, 0, 11776, 15104], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [15104, 11776, 0, 0, 11776, 15104], [15104, 27136, 0, 0, 27136, 15104]],
    [[11776, 15104, 0, 0, 15104, 11776], [27136, 15104, 0, 0, 15104, 27136], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [27136, 15104, 0, 0, 15104, 27136], [11776, 15104, 0, 0, 15104, 11776]]],
  [[[23552, 30208, 30208, 30208, 30208, 23552], [53760, 30208, 41984, 41984, 30208, 53760], [53760, 41984, 30208, 30208, 41984, 53760], [53760, 41984, 30208, 30208, 41984, 53760], [53760, 30208, 41984, 41984, 30208, 53760], [23552, 30208, 30208, 30208, 30208, 23552]],
    [[30208, 53760, 41984, 41984, 53760, 30208], [30208, 23552, 30208, 30208, 23552, 30208], [41984, 53760, 30208, 30208, 53760, 41984], [41984, 53760, 30208, 30208, 53760, 41984], [30208, 23552, 30208, 30208, 23552, 30208], [30208, 53760, 41984, 41984, 53760, 30208]],
    [[30208, 41984, 53760, 53760, 41984, 30208], [41984, 30208, 53760, 53760, 30208, 41984], [30208, 30208, 23552, 23552, 30208, 30208], [30208, 30208, 23552, 23552, 30208, 30208], [41984, 30208, 53760, 53760, 30208, 41984], [30208, 41984, 53760, 53760, 41984, 30208]],
    [[30208, 41984, 53760, 53760, 41984, 30208], [41984, 30208, 53760, 53760, 30208, 41984], [30208, 30208, 23552, 23552, 30208, 30208], [30208, 30208, 23552, 23552, 30208, 30208], [41984, 30208, 53760, 53760, 30208, 41984], [30208, 41984, 53760, 53760, 41984, 30208]],
    [[30208, 53760, 41984, 41984, 53760, 30208], [30208, 23552, 30208, 30208, 23552, 30208], [41984, 53760, 30208, 30208, 53760, 41984], [41984, 53760, 30208, 30208, 53760, 41984], [30208, 23552, 30208, 30208, 23552, 30208], [30208, 53760, 41984, 41984, 53760, 30208]],
    [[23552, 30208, 30208, 30208, 30208, 23552], [53760, 30208, 41984, 41984, 30208, 53760], [53760, 41984, 30208, 30208, 41984, 53760], [53760, 41984, 30208, 30208, 41984, 53760], [53760, 30208, 41984, 41984, 30208, 53760], [23552, 30208, 30208, 30208, 30208, 23552]]]]

def look (L : List (List (List (List ℕ)))) (t : ℕ) (q : Row) : ℕ :=
  (((L.getD (t - 1) []).getD (q 0).val []).getD (q 1).val []).getD (q 2).val 0

def tbl1 (t : ℕ) (q : Row) : ℕ := look tbl1L t q
def tbl2 (t : ℕ) (q : Row) : ℕ := look tbl2L t q
def tbl3 (t : ℕ) (q : Row) : ℕ := look tbl3L t q

theorem c1_key : ∀ t : Fin 2, ∀ q : Row, P (t.val + 1) q →
    cnt 1 (t.val + 1) (some q) = tbl1 (t.val + 1) q := by
  decide +kernel

theorem c2_key : ∀ t : Fin 2, ∀ q : Row, P (t.val + 1) q →
    (∑ r : Row, if rowOK (t.val + 1) (some q) r then tbl1 (newT (t.val + 1) r) r else 0) =
      tbl2 (t.val + 1) q := by
  decide +kernel

theorem c3_key : ∀ t : Fin 2, ∀ q : Row, P (t.val + 1) q →
    (∑ r : Row, if rowOK (t.val + 1) (some q) r then tbl2 (newT (t.val + 1) r) r else 0) =
      tbl3 (t.val + 1) q := by
  decide +kernel

theorem W1_key : ∀ t : Fin 2, ∀ q : Row, P (t.val + 1) q →
    (∑ r : Row, if rowOK (t.val + 1) (some q) r then
      ((tbl3 (newT (t.val + 1) r) r : ℤ) - 48 * tbl2 (newT (t.val + 1) r) r +
        448 * tbl1 (newT (t.val + 1) r) r - 1024) else 0) = 0 := by
  decide +kernel

theorem a4_key :
    (∑ r : Row, if rowOK 0 none r then tbl3 (newT 0 r) r else 0) = 96256 := by
  decide +kernel

theorem c1_eq (t : ℕ) (q : Row) (h1 : 1 ≤ t) (h3 : t ≤ 2) (hP : P t q) :
    cnt 1 t (some q) = tbl1 t q := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  exact c1_key ⟨s, by omega⟩ q hP

theorem c2_eq (t : ℕ) (q : Row) (h1 : 1 ≤ t) (h3 : t ≤ 2) (hP : P t q) :
    cnt 2 t (some q) = tbl2 t q := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [cnt_succ, ← c2_key ⟨s, by omega⟩ q hP]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : rowOK (s + 1) (some q) r
  · rw [if_pos h, if_pos h]
    obtain ⟨a1, a2, a3⟩ := P_next _ _ r h h1 h3
    exact c1_eq _ r a1 a2 a3
  · rw [if_neg h, if_neg h]

theorem c3_eq (t : ℕ) (q : Row) (h1 : 1 ≤ t) (h3 : t ≤ 2) (hP : P t q) :
    cnt 3 t (some q) = tbl3 t q := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [cnt_succ, ← c3_key ⟨s, by omega⟩ q hP]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : rowOK (s + 1) (some q) r
  · rw [if_pos h, if_pos h]
    obtain ⟨a1, a2, a3⟩ := P_next _ _ r h h1 h3
    exact c2_eq _ r a1 a2 a3
  · rw [if_neg h, if_neg h]

theorem W0_eq (t : ℕ) (q : Row) (h1 : 1 ≤ t) (h3 : t ≤ 2) (hP : P t q) :
    W 0 t (some q) = (tbl3 t q : ℤ) - 48 * tbl2 t q + 448 * tbl1 t q - 1024 := by
  simp only [W, c1_eq t q h1 h3 hP, c2_eq t q h1 h3 hP, c3_eq t q h1 h3 hP]
  simp [cnt]

theorem W_base (t : ℕ) (q : Row) (h1 : 1 ≤ t) (h3 : t ≤ 2) (hP : P t q) :
    W 1 t (some q) = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [W_succ]
  refine (Finset.sum_congr rfl fun r _ => ?_).trans (W1_key ⟨s, by omega⟩ q hP)
  by_cases h : rowOK (s + 1) (some q) r
  · rw [if_pos h, if_pos h]
    obtain ⟨a1, a2, a3⟩ := P_next _ _ r h h1 h3
    exact W0_eq _ r a1 a2 a3
  · rw [if_neg h, if_neg h]

theorem W_zero (n : ℕ) : ∀ t q, 1 ≤ t → t ≤ 2 → P t q → W (n + 1) t (some q) = 0 := by
  induction n with
  | zero => exact W_base
  | succ n ih =>
    intro t q h1 h3 hP
    rw [W_succ]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases h : rowOK t (some q) r
    · rw [if_pos h]
      obtain ⟨a1, a2, a3⟩ := P_next _ _ r h h1 h3
      exact ih _ _ a1 a2 a3
    · rw [if_neg h]

theorem a1 : a 1 = 3 := by rw [a_eq]; decide +kernel
theorem a2 : a 2 = 80 := by rw [a_eq]; decide +kernel
theorem a3 : a 3 = 2688 := by rw [a_eq]; decide +kernel

theorem a4 : a 4 = 96256 := by
  rw [a_eq, cnt_succ, ← a4_key]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : rowOK 0 none r
  · rw [if_pos h, if_pos h]
    obtain ⟨a1, a2, a3⟩ := top_next r h
    exact c3_eq _ r a1 a2 a3
  · rw [if_neg h, if_neg h]

theorem a_rec (n : ℕ) :
    (a (n + 5) : ℤ) = 48 * a (n + 4) - 448 * a (n + 3) + 1024 * a (n + 2) := by
  have h : W (n + 2) 0 none = 0 := by
    rw [W_succ]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : rowOK 0 none r
    · rw [if_pos hr]
      obtain ⟨a1, a2, a3⟩ := top_next r hr
      exact W_zero n _ _ a1 a2 a3
    · rw [if_neg hr]
  simp only [W] at h
  rw [a_eq, a_eq, a_eq, a_eq]
  rw [show n + 5 = n + 2 + 3 by ring, show n + 4 = n + 2 + 2 by ring,
    show n + 3 = n + 2 + 1 by ring]
  linarith

theorem gf :
    (1 - 8 * X) * (1 - 40 * X + 128 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (3 - 64 * X + 192 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 8 * X) * (1 - 40 * X + 128 * X ^ 2) * s =
      s - (s * C (48 : ℤ)) * X ^ 1 + (s * C (448 : ℤ)) * X ^ 2 - (s * C (1024 : ℤ)) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (X * (3 - 64 * X + 192 * X ^ 2) : PowerSeries ℤ) =
      C (3 : ℤ) * X ^ 1 - C (64 : ℤ) * X ^ 2 + C (192 : ℤ) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with h | h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · subst h; simp [a1, a2, a3, a4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have := a_rec m
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega]
    simp
    omega

noncomputable def u (n : ℕ) : ℝ :=
  (20 - 4 * Real.sqrt 17) ^ n * (-3 + Real.sqrt 17) +
    (3 + Real.sqrt 17) * (4 * (5 + Real.sqrt 17)) ^ n

theorem u_rec (j : ℕ) : u (j + 2) = 40 * u (j + 1) - 128 * u j := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have ha : (20 - 4 * Real.sqrt 17) ^ 2 = 40 * (20 - 4 * Real.sqrt 17) - 128 := by
    linear_combination 16 * hs
  have hb : (4 * (5 + Real.sqrt 17)) ^ 2 = 40 * (4 * (5 + Real.sqrt 17)) - 128 := by
    linear_combination 16 * hs
  unfold u
  linear_combination (20 - 4 * Real.sqrt 17) ^ j * (-3 + Real.sqrt 17) * ha +
    (3 + Real.sqrt 17) * (4 * (5 + Real.sqrt 17)) ^ j * hb

noncomputable def R (n : ℕ) : ℝ := (8 : ℝ) ^ n / 8 + u n / (32 * Real.sqrt 17)

theorem R_eq (n : ℕ) : (8 : ℝ) ^ (-1 + (n : ℤ)) +
    ((20 - 4 * Real.sqrt 17) ^ n * (-3 + Real.sqrt 17) +
      (3 + Real.sqrt 17) * (4 * (5 + Real.sqrt 17)) ^ n) / (32 * Real.sqrt 17) = R n := by
  rw [R, u, zpow_add₀ (by norm_num), zpow_neg_one, zpow_natCast]
  ring

theorem R_rec (j : ℕ) : R (j + 3) = 48 * R (j + 2) - 448 * R (j + 1) + 1024 * R j := by
  have h1 := u_rec (j + 1)
  have h0 := u_rec j
  unfold R
  rw [show j + 1 + 2 = j + 3 by ring, show j + 1 + 1 = j + 2 by ring] at h1
  rw [h1, h0]
  ring

theorem R_val (c : ℝ) (n : ℕ) (h : u n = c * Real.sqrt 17) : R n = (8 : ℝ) ^ n / 8 + c / 32 := by
  have hpos : Real.sqrt 17 ≠ 0 := by positivity
  rw [R, h]
  field_simp

theorem u0 : u 0 = 2 * Real.sqrt 17 := by unfold u; ring
theorem u1 : u 1 = 64 * Real.sqrt 17 := by unfold u; ring
theorem u2 : u 2 = 2304 * Real.sqrt 17 := by rw [u_rec 0, u1, u0]; ring
theorem u3 : u 3 = 83968 * Real.sqrt 17 := by rw [u_rec 1, u2, u1]; ring

theorem closed (m : ℕ) : (a (m + 1) : ℝ) = R (m + 1) ∧ (a (m + 2) : ℝ) = R (m + 2) ∧
    (a (m + 3) : ℝ) = R (m + 3) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [R_val _ _ u1, a1]; norm_num
    · rw [R_val _ _ u2, a2]; norm_num
    · rw [R_val _ _ u3, a3]; norm_num
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have key : (a (m + 4) : ℝ) = 48 * (a (m + 3) : ℝ) - 448 * (a (m + 2) : ℝ) +
        1024 * (a (m + 1) : ℝ) := by
      rcases m with _ | k
      · rw [a4, a3, a2, a1]; norm_num
      · show (a (k + 5) : ℝ) = 48 * (a (k + 4) : ℝ) - 448 * (a (k + 3) : ℝ) +
          1024 * (a (k + 2) : ℝ)
        exact_mod_cast a_rec k
    have hR := R_rec (m + 1)
    simp only [show m + 1 + 3 = m + 4 from rfl, show m + 1 + 2 = m + 3 from rfl,
      show m + 1 + 1 = m + 2 from rfl] at hR
    show (a (m + 4) : ℝ) = R (m + 4)
    rw [key, h1, h2, h3, hR]

end A233124Proof

open A233124Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a233124.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [R_eq, (closed m).1]

