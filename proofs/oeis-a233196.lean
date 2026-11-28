import OMAStatements.S_oeis_a233196

open OMA.S_oeis_a233196 PowerSeries

namespace A233196Proof

-- A row of the array: one letter of the row by row scan.
abbrev Row := Fin 2 → Fin 8

-- The value u must appear before the value v.
def Req (u v : Fin 8) : Prop :=
  (u.val = 1 ∧ 2 ≤ v.val ∧ v.val ≤ 6) ∨ (u.val = 2 ∧ 3 ≤ v.val ∧ v.val ≤ 5) ∨
    (u.val = 3 ∧ v.val = 4)

instance (u v : Fin 8) : Decidable (Req u v) := by unfold Req; infer_instance

theorem req_bounds {u v : Fin 8} (h : Req u v) : 1 ≤ u.val ∧ u.val ≤ 3 := by
  unfold Req at h; omega

-- The conditions linking a row r to the row p above it (none for the top row).
def upOK (p : Option Row) (r : Row) : Prop :=
  match p with
  | none => r 0 = 0
  | some q => ¬ Clash (q 0) (r 0) ∧ ¬ Clash (q 1) (r 1) ∧ ¬ Clash (q 1) (r 0)

instance (p : Option Row) (r : Row) : Decidable (upOK p r) := by
  cases p <;> unfold upOK <;> infer_instance

-- A new row r below the row p, when the values 1..t have been seen already.
def rowOK (t : ℕ) (p : Option Row) (r : Row) : Prop :=
  ¬ Clash (r 0) (r 1) ∧ upOK p r ∧ ∀ j u, Req u (r j) → u.val ≤ t ∨ ∃ j' < j, r j' = u

instance (t : ℕ) (p : Option Row) (r : Row) : Decidable (rowOK t p r) := by
  unfold rowOK; infer_instance

def lvl (v : Fin 8) : ℕ := if v.val ≤ 3 then v.val else 0

-- The level of seen values after the row r.
def newT (t : ℕ) (r : Row) : ℕ := max t (max (lvl (r 0)) (lvl (r 1)))

-- The conditions on a block of rows below the row p, the values 1..t being seen already.
def ExtOK (t : ℕ) (p : Option Row) {n : ℕ} (A : Fin n → Row) : Prop :=
  (∀ i, ¬ Clash (A i 0) (A i 1)) ∧
  (∀ i i' : Fin n, i.val + 1 = i'.val → ∀ j, ¬ Clash (A i j) (A i' j)) ∧
  (∀ i i' : Fin n, i.val + 1 = i'.val → ¬ Clash (A i 1) (A i' 0)) ∧
  (∀ i : Fin n, i.val = 0 → upOK p (A i)) ∧
  (∀ i j u, Req u (A i j) → u.val ≤ t ∨ Before A i j u)

theorem order_iff {n : ℕ} (A : Fin n → Row) :
    OrderOK A ↔ ∀ i j u, Req u (A i j) → u.val ≤ 0 ∨ Before A i j u := by
  constructor
  · intro h i j u hu
    obtain ⟨h1, h2, h3⟩ := h i j
    right
    rcases hu with ⟨hu, a, b⟩ | ⟨hu, a, b⟩ | ⟨hu, a⟩
    · rw [show u = 1 from Fin.ext hu]; exact h1 a b
    · rw [show u = 2 from Fin.ext hu]; exact h2 a b
    · rw [show u = 3 from Fin.ext hu]; exact h3 a
  · intro h i j
    refine ⟨fun a b => ?_, fun a b => ?_, fun a => ?_⟩
    · rcases h i j 1 (Or.inl ⟨rfl, a, b⟩) with h' | h'
      · exact absurd h' (by decide)
      · exact h'
    · rcases h i j 2 (Or.inr (Or.inl ⟨rfl, a, b⟩)) with h' | h'
      · exact absurd h' (by decide)
      · exact h'
    · rcases h i j 3 (Or.inr (Or.inr ⟨rfl, a⟩)) with h' | h'
      · exact absurd h' (by decide)
      · exact h'

theorem valid_iff {n : ℕ} (A : Fin n → Row) : Valid A ↔ ExtOK 0 none A := by
  unfold Valid NoClash ExtOK
  rw [order_iff]
  simp only [upOK]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h3⟩, h4, h5⟩

theorem hor_cons {n : ℕ} (r : Row) (B : Fin n → Row) :
    (∀ i : Fin (n + 1), ¬ Clash ((Fin.cons r B : Fin (n + 1) → Row) i 0)
      ((Fin.cons r B : Fin (n + 1) → Row) i 1)) ↔
    ¬ Clash (r 0) (r 1) ∧ ∀ i, ¬ Clash (B i 0) (B i 1) := by
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

theorem anti_cons {n : ℕ} (r : Row) (B : Fin n → Row) :
    (∀ i i' : Fin (n + 1), i.val + 1 = i'.val →
      ¬ Clash ((Fin.cons r B : Fin (n + 1) → Row) i 1) ((Fin.cons r B : Fin (n + 1) → Row) i' 0)) ↔
    (∀ i : Fin n, i.val = 0 → ¬ Clash (r 1) (B i 0)) ∧
      (∀ i i' : Fin n, i.val + 1 = i'.val → ¬ Clash (B i 1) (B i' 0)) := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i i' hii' => ?_⟩
    · have := h 0 i.succ (by simp [hi])
      simpa using this
    · have := h i.succ i'.succ (by simp [hii'])
      simpa using this
  · rintro ⟨h1, h2⟩ i i' hii'
    cases i using Fin.cases with
    | zero =>
      cases i' using Fin.cases with
      | zero => simp at hii'
      | succ k =>
        simp only [Fin.val_zero, Fin.val_succ] at hii'
        simpa using h1 k (by omega)
    | succ k =>
      cases i' using Fin.cases with
      | zero => simp at hii'
      | succ k' =>
        simp only [Fin.val_succ] at hii'
        simpa using h2 k k' (by omega)

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
    (u : Fin 8) (hu : 1 ≤ u.val ∧ u.val ≤ 3) :
    (u.val ≤ t ∨ ∃ j', r j' = u) ↔ u.val ≤ newT t r := by
  by_cases ht : 3 ≤ t
  · have : t ≤ newT t r := le_max_left _ _
    exact ⟨fun _ => by omega, fun _ => Or.inl (by omega)⟩
  · have key : ∀ t : Fin 3, ∀ r : Row,
        (∀ j u, Req u (r j) → u.val ≤ t.val ∨ ∃ j' < j, r j' = u) →
        ∀ u : Fin 8, 1 ≤ u.val ∧ u.val ≤ 3 →
          ((u.val ≤ t.val ∨ ∃ j', r j' = u) ↔ u.val ≤ newT t.val r) := by
      decide +kernel
    exact key ⟨t, by omega⟩ r h u hu

theorem ext_cons (t : ℕ) (p : Option Row) {n : ℕ} (r : Row) (B : Fin n → Row) :
    ExtOK t p (Fin.cons r B : Fin (n + 1) → Row) ↔ rowOK t p r ∧ ExtOK (newT t r) (some r) B := by
  unfold ExtOK rowOK
  rw [hor_cons, ver_cons, anti_cons, up_cons, ord_cons]
  simp only [upOK]
  constructor
  · rintro ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩, ⟨h3, h3'⟩, h4, ⟨h5, h5'⟩⟩
    refine ⟨⟨h1, h4, h5⟩, h1', h2', h3', fun i hi => ⟨h2 i hi 0, h2 i hi 1, h3 i hi⟩,
      fun i j u hu => ?_⟩
    rcases h5' i j u hu with h | h
    · exact Or.inl ((newT_spec t r h5 u (req_bounds hu)).1 h)
    · exact Or.inr h
  · rintro ⟨⟨h1, h4, h5⟩, h1', h2', h3', h6, h5'⟩
    refine ⟨⟨h1, h1'⟩, ⟨fun i hi j => ?_, h2'⟩, ⟨fun i hi => (h6 i hi).2.2, h3'⟩, h4,
      ⟨h5, fun i j u hu => ?_⟩⟩
    · fin_cases j
      · exact (h6 i hi).1
      · exact (h6 i hi).2.1
    · rcases h5' i j u hu with h | h
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
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩)]
    simp [cnt]
  | succ n ih =>
    intro t p
    rw [F_succ, cnt_succ]
    simp only [ih]

theorem a_eq (n : ℕ) : a n = cnt n 0 none := by
  rw [← F_eq, a, F, Finset.filter_congr (fun A _ => valid_iff A)]

def W (n t : ℕ) (p : Option Row) : ℤ :=
  (cnt (n + 2) t p : ℤ) - 20 * cnt (n + 1) t p + 64 * cnt n t p

theorem W_succ (n t : ℕ) (p : Option Row) :
    W (n + 1) t p = ∑ r : Row, if rowOK t p r then W n (newT t r) (some r) else 0 := by
  simp only [W, show n + 1 + 2 = n + 2 + 1 by ring]
  rw [cnt_succ (n + 2) t p, cnt_succ (n + 1) t p, cnt_succ n t p]
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : rowOK t p r
  · simp only [if_pos h]
  · simp only [if_neg h]; ring

-- The states that occur: the previous row uses values allowed at level t and reaching at most t.
def P (t : ℕ) (q : Row) : Prop := ∀ j, (∀ u, Req u (q j) → u.val ≤ t) ∧ lvl (q j) ≤ t

instance (t : ℕ) (q : Row) : Decidable (P t q) := by unfold P; infer_instance

theorem P_next_key : ∀ t : Fin 4, ∀ r : Row,
    (∀ j u, Req u (r j) → u.val ≤ t.val ∨ ∃ j' < j, r j' = u) →
      P (newT t.val r) r ∧ newT t.val r ≤ 3 := by
  decide +kernel

theorem P_next (t : ℕ) (p : Option Row) (r : Row) (h : rowOK t p r) (h1 : 1 ≤ t) (h3 : t ≤ 3) :
    1 ≤ newT t r ∧ newT t r ≤ 3 ∧ P (newT t r) r :=
  ⟨le_trans h1 (le_max_left _ _), (P_next_key ⟨t, by omega⟩ r h.2.2).2,
    (P_next_key ⟨t, by omega⟩ r h.2.2).1⟩

theorem top_next : ∀ r : Row, rowOK 0 none r →
    1 ≤ newT 0 r ∧ newT 0 r ≤ 3 ∧ P (newT 0 r) r := by
  decide +kernel

def tbl1L : List ℕ :=
  [5, 3, 0, 0, 0, 0, 3, 5, 3, 5, 0, 0, 0, 0, 5, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 5, 0, 0, 0, 0, 5, 3, 5, 3, 0, 0,
    0, 0, 3, 5, 16, 10, 10, 0, 0, 10, 10, 16, 10, 16, 10, 0, 0, 10, 16, 10, 10, 10, 16, 0, 0,
    16, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 16, 0, 0, 16, 10, 10,
    10, 16, 10, 0, 0, 10, 16, 10, 16, 10, 10, 0, 0, 10, 10, 16, 24, 16, 16, 16, 16, 16, 16, 24,
    16, 24, 16, 16, 16, 16, 24, 16, 16, 16, 24, 16, 16, 24, 16, 16, 16, 16, 16, 24, 24, 16, 16,
    16, 16, 16, 16, 24, 24, 16, 16, 16, 16, 16, 24, 16, 16, 24, 16, 16, 16, 24, 16, 16, 16, 16,
    24, 16, 24, 16, 16, 16, 16, 16, 16, 24]

def tbl2L : List ℕ :=
  [56, 36, 0, 0, 0, 0, 36, 56, 36, 56, 0, 0, 0, 0, 56, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 56, 0, 0, 0, 0, 56, 36, 56,
    36, 0, 0, 0, 0, 36, 56, 208, 136, 136, 0, 0, 136, 136, 208, 136, 208, 136, 0, 0, 136, 208,
    136, 136, 136, 208, 0, 0, 208, 136, 136, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    136, 136, 208, 0, 0, 208, 136, 136, 136, 208, 136, 0, 0, 136, 208, 136, 208, 136, 136, 0,
    0, 136, 136, 208, 384, 256, 256, 256, 256, 256, 256, 384, 256, 384, 256, 256, 256, 256,
    384, 256, 256, 256, 384, 256, 256, 384, 256, 256, 256, 256, 256, 384, 384, 256, 256, 256,
    256, 256, 256, 384, 384, 256, 256, 256, 256, 256, 384, 256, 256, 384, 256, 256, 256, 384,
    256, 256, 256, 256, 384, 256, 384, 256, 256, 256, 256, 256, 256, 384]

def tbl1 (t : ℕ) (q : Row) : ℕ := tbl1L.getD (64 * (t - 1) + 8 * (q 0).val + (q 1).val) 0
def tbl2 (t : ℕ) (q : Row) : ℕ := tbl2L.getD (64 * (t - 1) + 8 * (q 0).val + (q 1).val) 0

theorem c1_key : ∀ t : Fin 3, ∀ q : Row, P (t.val + 1) q →
    cnt 1 (t.val + 1) (some q) = tbl1 (t.val + 1) q := by
  decide +kernel

theorem c2_key : ∀ t : Fin 3, ∀ q : Row, P (t.val + 1) q →
    (∑ r : Row, if rowOK (t.val + 1) (some q) r then tbl1 (newT (t.val + 1) r) r else 0) =
      tbl2 (t.val + 1) q := by
  decide +kernel

theorem W1_key : ∀ t : Fin 3, ∀ q : Row, P (t.val + 1) q →
    (∑ r : Row, if rowOK (t.val + 1) (some q) r then
      ((tbl2 (newT (t.val + 1) r) r : ℤ) - 20 * tbl1 (newT (t.val + 1) r) r + 64) else 0) = 0 := by
  decide +kernel

theorem c1_eq (t : ℕ) (q : Row) (h1 : 1 ≤ t) (h3 : t ≤ 3) (hP : P t q) :
    cnt 1 t (some q) = tbl1 t q := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  exact c1_key ⟨s, by omega⟩ q hP

theorem c2_eq (t : ℕ) (q : Row) (h1 : 1 ≤ t) (h3 : t ≤ 3) (hP : P t q) :
    cnt 2 t (some q) = tbl2 t q := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [cnt_succ, ← c2_key ⟨s, by omega⟩ q hP]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : rowOK (s + 1) (some q) r
  · rw [if_pos h, if_pos h]
    obtain ⟨a1, a2, a3⟩ := P_next _ _ r h h1 h3
    exact c1_eq _ r a1 a2 a3
  · rw [if_neg h, if_neg h]

theorem W0_eq (t : ℕ) (q : Row) (h1 : 1 ≤ t) (h3 : t ≤ 3) (hP : P t q) :
    W 0 t (some q) = (tbl2 t q : ℤ) - 20 * tbl1 t q + 64 := by
  simp only [W, c1_eq t q h1 h3 hP, c2_eq t q h1 h3 hP]
  simp [cnt]

theorem W_base (t : ℕ) (q : Row) (h1 : 1 ≤ t) (h3 : t ≤ 3) (hP : P t q) :
    W 1 t (some q) = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [W_succ]
  refine (Finset.sum_congr rfl fun r _ => ?_).trans (W1_key ⟨s, by omega⟩ q hP)
  by_cases h : rowOK (s + 1) (some q) r
  · rw [if_pos h, if_pos h]
    obtain ⟨a1, a2, a3⟩ := P_next _ _ r h h1 h3
    exact W0_eq _ r a1 a2 a3
  · rw [if_neg h, if_neg h]

theorem W_zero (n : ℕ) : ∀ t q, 1 ≤ t → t ≤ 3 → P t q → W (n + 1) t (some q) = 0 := by
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

theorem a1 : a 1 = 1 := by rw [a_eq]; decide +kernel
theorem a2 : a 2 = 3 := by rw [a_eq]; decide +kernel
theorem a3 : a 3 = 36 := by rw [a_eq]; decide +kernel

theorem a_rec (n : ℕ) : (a (n + 4) : ℤ) = 20 * a (n + 3) - 64 * a (n + 2) := by
  have h : W (n + 2) 0 none = 0 := by
    rw [W_succ]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : rowOK 0 none r
    · rw [if_pos hr]
      obtain ⟨a1, a2, a3⟩ := top_next r hr
      exact W_zero n _ _ a1 a2 a3
    · rw [if_neg hr]
  simp only [W] at h
  rw [a_eq, a_eq, a_eq]
  rw [show n + 4 = n + 2 + 2 by ring, show n + 3 = n + 2 + 1 by ring]
  linarith

theorem gf :
    (1 - 4 * X) * (1 - 16 * X) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (1 - 17 * X + 40 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 4 * X) * (1 - 16 * X) * s =
      s - (s * C (20 : ℤ)) * X ^ 1 + (s * C (64 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (X * (1 - 17 * X + 40 * X ^ 2) : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 1 - C (17 : ℤ) * X ^ 2 + C (40 : ℤ) * X ^ 3 := by
    simp only [pow_one, map_ofNat, map_one]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have := a_rec m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega]
    simp
    omega

noncomputable def R (n : ℕ) : ℝ := ((16 : ℝ) ^ n + 8 * 4 ^ n) / 128

theorem R_eq (n : ℕ) : (2 : ℝ) ^ (2 * (n : ℤ) - 7) * (4 ^ n + 8) = R n := by
  have h : (2 : ℝ) ^ (2 * (n : ℤ) - 7) = 4 ^ n / 128 := by
    rw [zpow_sub₀ (by norm_num), zpow_mul]
    norm_num
  rw [h, R, show (16 : ℝ) = 4 * 4 by norm_num, mul_pow]
  ring

theorem R_rec (j : ℕ) : R (j + 2) = 20 * R (j + 1) - 64 * R j := by
  unfold R
  rw [pow_succ, pow_succ, pow_succ, pow_succ]
  ring

theorem closed (m : ℕ) : (a (m + 2) : ℝ) = R (m + 2) ∧ (a (m + 3) : ℝ) = R (m + 3) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a2, R]; norm_num
    · rw [a3, R]; norm_num
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 4) : ℝ) = 20 * (a (m + 3) : ℝ) - 64 * (a (m + 2) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 3 = m + 4 by ring, hr, show m + 4 = (m + 2) + 2 by ring, R_rec, h1, h2]

end A233196Proof

open A233196Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a233196.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [(closed m).1, R_eq]

