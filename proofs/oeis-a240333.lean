import OMAStatements.S_oeis_a240333

namespace OMA.S_oeis_a240333

open PowerSeries Finset




lemma sum_Iio {m : ℕ} (j : Fin m) (h : Fin m → ℕ) :
    ∑ x ∈ Iio j, h x = ∑ x, if x < j then h x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

lemma sum_Iio_zero {m : ℕ} (h : Fin (m + 1) → ℕ) : ∑ x ∈ Iio (0 : Fin (m + 1)), h x = 0 := by
  rw [sum_Iio]
  simp [Fin.not_lt_zero]

lemma sum_Iio_succ {m : ℕ} (t : Fin m) (h : Fin (m + 1) → ℕ) :
    ∑ x ∈ Iio t.succ, h x = h 0 + ∑ x ∈ Iio t, h x.succ := by
  rw [sum_Iio, sum_Iio, Fin.sum_univ_succ]
  simp only [Fin.succ_pos, if_true, Fin.succ_lt_succ_iff]

/-- Entry p of D as a natural number, 0 past the end. -/
def dget (D : Fin 2 → Fin 4) (p : ℕ) : ℕ := if h : p < 2 then (D ⟨p, h⟩).val else 0

lemma dget_fin (D : Fin 2 → Fin 4) (s : Fin 2) : dget D s.val = (D s).val := by
  unfold dget
  rw [dif_pos s.isLt]

/-- The northwest-diagonal sum entering (t, s) when the slices g start from the diagonal sums D. -/
def dg (D : Fin 2 → Fin 4) {m : ℕ} (g : Fin m → Fin 2 → Fin 4) (t : Fin m) (s : Fin 2) : ℕ :=
  (if t.val ≤ s.val then dget D (s.val - t.val) else 0) +
    ∑ t' ∈ Iio t, ∑ s' ∈ Iio s, if t.val - t'.val = s.val - s'.val then (g t' s').val else 0

/-- The running sums after the slice v. -/
def nxt (A v : Fin 2 → Fin 4) : Fin 2 → Fin 4 := fun s => A s + v s

/-- The diagonal sums entering the slice after v. -/
def nxtD (D v : Fin 2 → Fin 4) : Fin 2 → Fin 4 := ![0, D 0 + v 0]

lemma dget_nxtD (D v : Fin 2 → Fin 4) (p : ℕ) (hp : p < 2) :
    dget (nxtD D v) p = if p = 0 then 0 else (dget D (p - 1) + dget v (p - 1)) % 4 := by
  interval_cases p <;> rfl

lemma diag_step (D v : Fin 2 → Fin 4) (t : ℕ) (s : Fin 2) :
    ((if t + 1 ≤ s.val then dget D (s.val - (t + 1)) else 0) +
      ∑ s' ∈ Iio s, (if t + 1 = s.val - s'.val then (v s').val else 0)) % 4 =
    (if t ≤ s.val then dget (nxtD D v) (s.val - t) else 0) % 4 := by
  have hs := s.isLt
  by_cases h : t + 1 ≤ s.val
  · have hsum : ∑ s' ∈ Iio s, (if t + 1 = s.val - s'.val then (v s').val else 0) =
        dget v (s.val - (t + 1)) := by
      rw [Finset.sum_eq_single_of_mem (⟨s.val - (t + 1), by omega⟩ : Fin 2)]
      · rw [if_pos]
        · simp [dget, show s.val - (t + 1) < 2 by omega]
        · simp only [Fin.val_mk]
          omega
      · simp only [Finset.mem_Iio, Fin.lt_def, Fin.val_mk]
        omega
      · intro b hb hne
        rw [if_neg]
        intro hc
        apply hne
        ext
        simp only [Finset.mem_Iio, Fin.lt_def] at hb
        simp only [Fin.val_mk]
        omega
    rw [if_pos h, if_pos (by omega : t ≤ s.val), hsum, dget_nxtD D v (s.val - t) (by omega),
      if_neg (by omega : ¬ s.val - t = 0), show s.val - t - 1 = s.val - (t + 1) by omega]
    omega
  · have hsum : ∑ s' ∈ Iio s, (if t + 1 = s.val - s'.val then (v s').val else 0) = 0 :=
      Finset.sum_eq_zero (fun s' _ => if_neg (by omega))
    rw [if_neg h, hsum]
    by_cases h2 : t ≤ s.val
    · rw [if_pos h2, show s.val - t = 0 by omega, dget_nxtD D v 0 (by omega), if_pos rfl]
    · rw [if_neg h2]

/-- The conditions on a slice v of any length when the running sums along the growing dimension
are A, the diagonal sums are D and the sums across start from off. -/
def colOKo {j : ℕ} (A D : Fin j → Fin 4) (off : ℕ) (v : Fin j → Fin 4) : Prop :=
  ∀ s : Fin j, (v s).val ≠ (2 + (A s).val) % 4 ∧ (v s).val ≠ (off + ∑ s' ∈ Iio s, (v s').val) % 4 ∧
    (v s).val ≠ (1 + (D s).val) % 4

instance {j : ℕ} (A D : Fin j → Fin 4) (off : ℕ) : DecidablePred (colOKo A D off) := fun v => by
  unfold colOKo; infer_instance

lemma sum_cons {j : ℕ} (G : (Fin (j + 1) → Fin 4) → ℕ) :
    ∑ v, G v = ∑ x : Fin 4, ∑ w : Fin j → Fin 4, G (Fin.cons x w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 4) _ _ (fun p => rfl)).symm

lemma colOKo_cons {j : ℕ} (A D : Fin (j + 1) → Fin 4) (off : ℕ) (x : Fin 4) (w : Fin j → Fin 4) :
    colOKo A D off (Fin.cons x w : Fin (j + 1) → Fin 4) ↔
      (x.val ≠ (2 + (A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (1 + (D 0).val) % 4) ∧
        colOKo (Fin.tail A) (Fin.tail D) (off + x.val) w := by
  have key : ∀ s : Fin j, (off + ∑ s' ∈ Iio s.succ, ((Fin.cons x w : Fin (j + 1) → Fin 4) s').val) % 4 =
      (off + x.val + ∑ s' ∈ Iio s, (w s').val) % 4 := by
    intro s
    rw [sum_Iio_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega
  have key0 : (off + ∑ s' ∈ Iio (0 : Fin (j + 1)), ((Fin.cons x w : Fin (j + 1) → Fin 4) s').val) % 4 =
      off % 4 := by
    rw [sum_Iio_zero, Nat.add_zero]
  constructor
  · intro h
    refine ⟨?_, fun s => ?_⟩
    · have e := h 0
      rw [key0] at e
      simpa using e
    · have e := h s.succ
      rw [key] at e
      simpa [Fin.tail] using e
  · rintro ⟨h0, h1⟩ s
    induction s using Fin.cases with
    | zero =>
      rw [key0]
      simpa using h0
    | succ s =>
      rw [key]
      simpa [Fin.tail] using h1 s

/-- The allowed slices enumerated entry by entry: each entry runs over its allowed values, and the
finished slice goes to F. -/
def nest : (j : ℕ) → (Fin j → Fin 4) → (Fin j → Fin 4) → ℕ → ((Fin j → Fin 4) → ℕ) → ℕ
  | 0, _, _, _, F => F Fin.elim0
  | j + 1, A, D, off, F => ∑ x : Fin 4,
      if x.val ≠ (2 + (A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (1 + (D 0).val) % 4 then
        nest j (Fin.tail A) (Fin.tail D) (off + x.val) (fun w => F (Fin.cons x w))
      else 0

lemma ssum_nest : ∀ (j : ℕ) (A D : Fin j → Fin 4) (off : ℕ) (F : (Fin j → Fin 4) → ℕ),
    (∑ v : Fin j → Fin 4, if colOKo A D off v then F v else 0) = nest j A D off F := by
  intro j
  induction j with
  | zero =>
    intro A D off F
    rw [Fintype.sum_unique]
    simp only [nest]
    split_ifs with hc
    · exact congrArg F (Subsingleton.elim _ _)
    · exact absurd (fun s => Fin.elim0 s) hc
  | succ j ih =>
    intro A D off F
    rw [sum_cons]
    simp only [nest]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hc : x.val ≠ (2 + (A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (1 + (D 0).val) % 4
    · rw [if_pos hc, ← ih (Fin.tail A) (Fin.tail D) (off + x.val) (fun w => F (Fin.cons x w))]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      simp only [colOKo_cons, hc, true_and, ne_eq, not_false_eq_true]
    · rw [if_neg hc]
      refine Finset.sum_eq_zero (fun w _ => ?_)
      rw [if_neg]
      rw [colOKo_cons]
      exact fun h => hc h.1

/-- An array of slices is valid when started from the running sums A and the diagonal sums D. -/
def V (A D : Fin 2 → Fin 4) {m : ℕ} (g : Fin m → Fin 2 → Fin 4) : Prop :=
  ∀ t : Fin m, ∀ s : Fin 2,
    (g t s).val ≠ (2 + ((A s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 4 ∧
    (g t s).val ≠ (2 + ∑ s' ∈ Iio s, (g t s').val) % 4 ∧
    (g t s).val ≠ (1 + dg D g t s) % 4

instance (A D : Fin 2 → Fin 4) {m : ℕ} : DecidablePred (@V A D m) := fun g => by
  unfold V; infer_instance

lemma V_cons (A D : Fin 2 → Fin 4) {m : ℕ} (v : Fin 2 → Fin 4) (g : Fin m → Fin 2 → Fin 4) :
    V A D (Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 4) ↔ colOKo A D 2 v ∧ V (nxt A v) (nxtD D v) g := by
  have key : ∀ (t : Fin m) (s : Fin 2),
      (2 + ((A s).val + ∑ t' ∈ Iio t.succ, ((Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 4) t' s).val)) % 4 =
      (2 + ((nxt A v s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 4 := by
    intro t s
    rw [sum_Iio_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, nxt, Fin.val_add]
    omega
  have key0 : ∀ s : Fin 2,
      (2 + ((A s).val + ∑ t' ∈ Iio (0 : Fin (m + 1)), ((Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 4) t' s).val)) % 4 =
      (2 + (A s).val) % 4 := by
    intro s
    rw [sum_Iio_zero, Nat.add_zero]
  have dkey0 : ∀ s : Fin 2, dg D (Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 4) 0 s = (D s).val := by
    intro s
    unfold dg
    rw [sum_Iio_zero, Nat.add_zero, Fin.val_zero, if_pos (Nat.zero_le _), Nat.sub_zero, dget_fin]
  have dkey : ∀ (t : Fin m) (s : Fin 2),
      (1 + dg D (Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 4) t.succ s) % 4 =
      (1 + dg (nxtD D v) g t s) % 4 := by
    intro t s
    unfold dg
    rw [sum_Iio_succ]
    simp only [Fin.val_succ, Fin.val_zero, Nat.sub_zero, Nat.add_sub_add_right, Fin.cons_zero,
      Fin.cons_succ]
    have h := diag_step D v t.val s
    omega
  constructor
  · intro h
    refine ⟨fun s => ?_, fun t s => ?_⟩
    · have e := h 0 s
      rw [key0, dkey0] at e
      simpa using e
    · have e := h t.succ s
      rw [key, dkey] at e
      simpa using e
  · rintro ⟨h0, h1⟩ t s
    induction t using Fin.cases with
    | zero =>
      rw [key0, dkey0]
      simpa using h0 s
    | succ t =>
      rw [key, dkey]
      simpa using h1 t s

/-- W(m, A, D): the arrays of m slices valid from the state (A, D). -/
def W (m : ℕ) (A D : Fin 2 → Fin 4) : ℕ :=
  ((univ : Finset (Fin m → Fin 2 → Fin 4)).filter (V A D)).card

lemma W_zero (A D : Fin 2 → Fin 4) : W 0 A D = 1 := by
  have e : (univ : Finset (Fin 0 → Fin 2 → Fin 4)).filter (V A D) = univ :=
    Finset.filter_true_of_mem (fun g _ t => Fin.elim0 t)
  rw [W, e]
  simp

lemma W_succ (m : ℕ) (A D : Fin 2 → Fin 4) :
    W (m + 1) A D = ∑ v : Fin 2 → Fin 4, if colOKo A D 2 v then W m (nxt A v) (nxtD D v) else 0 := by
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · refine Finset.card_bij' (fun g _ => Fin.tail g) (fun g' _ => Fin.cons v g') ?_ ?_ ?_ ?_
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg ⊢
      have e : g = Fin.cons v (Fin.tail g) := by
        rw [← hg.2]
        exact (Fin.cons_self_tail g).symm
      have h1 := hg.1
      rw [e, V_cons] at h1
      exact h1.2
    · intro g' hg'
      simp only [mem_filter, mem_univ, true_and] at hg' ⊢
      exact ⟨(V_cons A D v g').2 ⟨hv, hg'⟩, by simp⟩
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg
      rw [← hg.2]
      exact Fin.cons_self_tail g
    · intro g' _
      simp
  · rw [Finset.card_eq_zero]
    ext g
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
    intro hg h0
    have e : g = Fin.cons v (Fin.tail g) := by
      rw [← h0]
      exact (Fin.cons_self_tail g).symm
    rw [e, V_cons] at hg
    exact hv hg.1

lemma a_eq (n : ℕ) : a n = W n 0 0 := by
  unfold a W
  congr 1
  ext f
  simp only [mem_filter, mem_univ, true_and, good, V, dg, dget, Pi.zero_apply, Fin.val_zero,
      zero_add, dite_eq_ite, ite_self]
  exact forall_congr' fun i => forall_congr' fun j => and_left_comm

/-- The reachable states, by A 0, ..., A 1, D 1, ..., D 1 (D 0 = 0). -/
def reach : Fin 4 → Fin 4 → Fin 4 → Bool :=
  ![![![true, false, false, false],
      ![true, false, false, false],
      ![true, false, false, false],
      ![true, false, false, false]],
    ![![false, false, false, true],
      ![true, false, false, true],
      ![true, false, false, true],
      ![true, false, false, true]],
    ![![false, false, false, true],
      ![false, false, false, true],
      ![false, false, false, true],
      ![false, false, false, true]],
    ![![false, false, false, true],
      ![true, false, false, true],
      ![true, false, false, true],
      ![true, false, false, true]]]

def T1 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![4, 0, 0, 0],
      ![3, 0, 0, 0],
      ![3, 0, 0, 0],
      ![5, 0, 0, 0]],
    ![![0, 0, 0, 2],
      ![1, 0, 0, 1],
      ![1, 0, 0, 2],
      ![2, 0, 0, 1]],
    ![![0, 0, 0, 1],
      ![0, 0, 0, 1],
      ![0, 0, 0, 2],
      ![0, 0, 0, 2]],
    ![![0, 0, 0, 3],
      ![3, 0, 0, 2],
      ![3, 0, 0, 4],
      ![5, 0, 0, 3]]]

def T2 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![15, 0, 0, 0],
      ![8, 0, 0, 0],
      ![8, 0, 0, 0],
      ![17, 0, 0, 0]],
    ![![0, 0, 0, 3],
      ![1, 0, 0, 1],
      ![1, 0, 0, 3],
      ![3, 0, 0, 1]],
    ![![0, 0, 0, 1],
      ![0, 0, 0, 1],
      ![0, 0, 0, 3],
      ![0, 0, 0, 3]],
    ![![0, 0, 0, 10],
      ![6, 0, 0, 5],
      ![5, 0, 0, 10],
      ![13, 0, 0, 6]]]

def T3 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![48, 0, 0, 0],
      ![19, 0, 0, 0],
      ![23, 0, 0, 0],
      ![46, 0, 0, 0]],
    ![![0, 0, 0, 4],
      ![1, 0, 0, 1],
      ![1, 0, 0, 4],
      ![4, 0, 0, 1]],
    ![![0, 0, 0, 1],
      ![0, 0, 0, 1],
      ![0, 0, 0, 4],
      ![0, 0, 0, 4]],
    ![![0, 0, 0, 22],
      ![10, 0, 0, 8],
      ![8, 0, 0, 21],
      ![25, 0, 0, 9]]]

def T4 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![125, 0, 0, 0],
      ![36, 0, 0, 0],
      ![49, 0, 0, 0],
      ![107, 0, 0, 0]],
    ![![0, 0, 0, 5],
      ![1, 0, 0, 1],
      ![1, 0, 0, 5],
      ![5, 0, 0, 1]],
    ![![0, 0, 0, 1],
      ![0, 0, 0, 1],
      ![0, 0, 0, 5],
      ![0, 0, 0, 5]],
    ![![0, 0, 0, 39],
      ![15, 0, 0, 12],
      ![12, 0, 0, 37],
      ![42, 0, 0, 13]]]

def T5 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![284, 0, 0, 0],
      ![61, 0, 0, 0],
      ![87, 0, 0, 0],
      ![218, 0, 0, 0]],
    ![![0, 0, 0, 6],
      ![1, 0, 0, 1],
      ![1, 0, 0, 6],
      ![6, 0, 0, 1]],
    ![![0, 0, 0, 1],
      ![0, 0, 0, 1],
      ![0, 0, 0, 6],
      ![0, 0, 0, 6]],
    ![![0, 0, 0, 62],
      ![21, 0, 0, 17],
      ![17, 0, 0, 59],
      ![65, 0, 0, 18]]]

def T6 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![582, 0, 0, 0],
      ![96, 0, 0, 0],
      ![140, 0, 0, 0],
      ![399, 0, 0, 0]],
    ![![0, 0, 0, 7],
      ![1, 0, 0, 1],
      ![1, 0, 0, 7],
      ![7, 0, 0, 1]],
    ![![0, 0, 0, 1],
      ![0, 0, 0, 1],
      ![0, 0, 0, 7],
      ![0, 0, 0, 7]],
    ![![0, 0, 0, 92],
      ![28, 0, 0, 23],
      ![23, 0, 0, 88],
      ![95, 0, 0, 24]]]

def T7 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![1097, 0, 0, 0],
      ![143, 0, 0, 0],
      ![211, 0, 0, 0],
      ![674, 0, 0, 0]],
    ![![0, 0, 0, 8],
      ![1, 0, 0, 1],
      ![1, 0, 0, 8],
      ![8, 0, 0, 1]],
    ![![0, 0, 0, 1],
      ![0, 0, 0, 1],
      ![0, 0, 0, 8],
      ![0, 0, 0, 8]],
    ![![0, 0, 0, 130],
      ![36, 0, 0, 30],
      ![30, 0, 0, 125],
      ![133, 0, 0, 31]]]

def T8 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![1932, 0, 0, 0],
      ![204, 0, 0, 0],
      ![303, 0, 0, 0],
      ![1071, 0, 0, 0]],
    ![![0, 0, 0, 9],
      ![1, 0, 0, 1],
      ![1, 0, 0, 9],
      ![9, 0, 0, 1]],
    ![![0, 0, 0, 1],
      ![0, 0, 0, 1],
      ![0, 0, 0, 9],
      ![0, 0, 0, 9]],
    ![![0, 0, 0, 177],
      ![45, 0, 0, 38],
      ![38, 0, 0, 171],
      ![180, 0, 0, 39]]]

set_option maxHeartbeats 4000000 in
lemma closure : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 2
      (fun v => (fun B E => if reach (B 0) (B 1) (E 1) = true then 0 else 1) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check1 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 2 (fun v => (fun _ _ => 1) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T1 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check2 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 2 (fun v => (fun B E => T1 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T2 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check3 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 2 (fun v => (fun B E => T2 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T3 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check4 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 2 (fun v => (fun B E => T3 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T4 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check5 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 2 (fun v => (fun B E => T4 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T5 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check6 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 2 (fun v => (fun B E => T5 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T6 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check7 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 2 (fun v => (fun B E => T6 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T7 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check8 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 2 (fun v => (fun B E => T7 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T8 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 2 (fun v => (fun B E => T8 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) + T3 a0 a1 d1 + 15 * T5 a0 a1 d1 + 15 * T7 a0 a1 d1 = 6 * T4 a0 a1 d1 + 20 * T6 a0 a1 d1 + 6 * T8 a0 a1 d1 := by
  decide +kernel

lemma vec_eta (A : Fin 2 → Fin 4) : A = ![A 0, A 1] := by
  ext s
  fin_cases s <;> rfl

lemma vec_etaD (D : Fin 2 → Fin 4) (h : D 0 = 0) : D = ![0, D 1] := by
  funext s
  fin_cases s
  · exact h
  · rfl

/-- Reachable states. -/
def R (A D : Fin 2 → Fin 4) : Prop := D 0 = 0 ∧ reach (A 0) (A 1) (D 1) = true

lemma R_nxt (A D v : Fin 2 → Fin 4) (hA : R A D) (hv : colOKo A D 2 v) : R (nxt A v) (nxtD D v) := by
  have h := closure (A 0) (A 1) (D 1) hA.2
  rw [← ssum_nest, ← vec_eta A, ← vec_etaD D hA.1] at h
  have e := (Finset.sum_eq_zero_iff.mp h) v (Finset.mem_univ v)
  rw [if_pos hv] at e
  try dsimp only at e
  unfold R
  refine ⟨rfl, ?_⟩
  by_contra hc
  rw [if_neg hc] at e
  exact one_ne_zero e

lemma W_succ_R (m : ℕ) (A D : Fin 2 → Fin 4) (F : (Fin 2 → Fin 4) → (Fin 2 → Fin 4) → ℕ)
    (hF : ∀ B E, R B E → W m B E = F B E) (hA : R A D) :
    W (m + 1) A D = nest 2 A D 2 (fun v => F (nxt A v) (nxtD D v)) := by
  rw [W_succ, ← ssum_nest]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · exact hF _ _ (R_nxt A D v hA hv)
  · rfl

lemma W1 (A D : Fin 2 → Fin 4) (hA : R A D) : W 1 A D = T1 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 0 A D (fun _ _ => 1) (fun B E _ => W_zero B E) hA, vec_eta A, vec_etaD D hA.1]
  exact check1 _ _ _ hA.2

lemma W2 (A D : Fin 2 → Fin 4) (hA : R A D) : W 2 A D = T2 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 1 A D (fun B E => T1 (B 0) (B 1) (E 1)) W1 hA, vec_eta A, vec_etaD D hA.1]
  exact check2 _ _ _ hA.2

lemma W3 (A D : Fin 2 → Fin 4) (hA : R A D) : W 3 A D = T3 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 2 A D (fun B E => T2 (B 0) (B 1) (E 1)) W2 hA, vec_eta A, vec_etaD D hA.1]
  exact check3 _ _ _ hA.2

lemma W4 (A D : Fin 2 → Fin 4) (hA : R A D) : W 4 A D = T4 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 3 A D (fun B E => T3 (B 0) (B 1) (E 1)) W3 hA, vec_eta A, vec_etaD D hA.1]
  exact check4 _ _ _ hA.2

lemma W5 (A D : Fin 2 → Fin 4) (hA : R A D) : W 5 A D = T5 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 4 A D (fun B E => T4 (B 0) (B 1) (E 1)) W4 hA, vec_eta A, vec_etaD D hA.1]
  exact check5 _ _ _ hA.2

lemma W6 (A D : Fin 2 → Fin 4) (hA : R A D) : W 6 A D = T6 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 5 A D (fun B E => T5 (B 0) (B 1) (E 1)) W5 hA, vec_eta A, vec_etaD D hA.1]
  exact check6 _ _ _ hA.2

lemma W7 (A D : Fin 2 → Fin 4) (hA : R A D) : W 7 A D = T7 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 6 A D (fun B E => T6 (B 0) (B 1) (E 1)) W6 hA, vec_eta A, vec_etaD D hA.1]
  exact check7 _ _ _ hA.2

lemma W8 (A D : Fin 2 → Fin 4) (hA : R A D) : W 8 A D = T8 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 7 A D (fun B E => T7 (B 0) (B 1) (E 1)) W7 hA, vec_eta A, vec_etaD D hA.1]
  exact check8 _ _ _ hA.2

lemma W_rec (n : ℕ) (A D : Fin 2 → Fin 4) (hA : R A D) :
    W (n + 9) A D + W (n + 3) A D + 15 * W (n + 5) A D + 15 * W (n + 7) A D = 6 * W (n + 4) A D + 20 * W (n + 6) A D + 6 * W (n + 8) A D := by
  induction n generalizing A D with
  | zero =>
    rw [show (0 : ℕ) + 9 = 8 + 1 from rfl, W_succ_R 8 A D (fun B E => T8 (B 0) (B 1) (E 1)) W8 hA, show (0 : ℕ) + 3 = 3 from rfl, W3 A D hA, show (0 : ℕ) + 5 = 5 from rfl, W5 A D hA, show (0 : ℕ) + 7 = 7 from rfl, W7 A D hA, show (0 : ℕ) + 4 = 4 from rfl, W4 A D hA, show (0 : ℕ) + 6 = 6 from rfl, W6 A D hA, show (0 : ℕ) + 8 = 8 from rfl, W8 A D hA, vec_eta A, vec_etaD D hA.1]
    exact base_check _ _ _ hA.2
  | succ n ih =>
    rw [W_succ (n + 9), W_succ (n + 3), W_succ (n + 5), W_succ (n + 7), W_succ (n + 4), W_succ (n + 6), W_succ (n + 8)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : colOKo A D 2 v
    · simp only [if_pos hv]
      exact ih _ _ (R_nxt A D v hA hv)
    · simp [hv]

lemma R_zero : R 0 0 := by
  unfold R
  decide +kernel

lemma a_rec (n : ℕ) : a (n + 9) + a (n + 3) + 15 * a (n + 5) + 15 * a (n + 7) = 6 * a (n + 4) + 20 * a (n + 6) + 6 * a (n + 8) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  exact W_rec n 0 0 R_zero

lemma a_zero : a 0 = 1 := by rw [a_eq, W_zero]
lemma a_1 : a 1 = 4 := by rw [a_eq, W1 0 0 R_zero]; rfl
lemma a_2 : a 2 = 15 := by rw [a_eq, W2 0 0 R_zero]; rfl
lemma a_3 : a 3 = 48 := by rw [a_eq, W3 0 0 R_zero]; rfl
lemma a_4 : a 4 = 125 := by rw [a_eq, W4 0 0 R_zero]; rfl
lemma a_5 : a 5 = 284 := by rw [a_eq, W5 0 0 R_zero]; rfl
lemma a_6 : a 6 = 582 := by rw [a_eq, W6 0 0 R_zero]; rfl
lemma a_7 : a 7 = 1097 := by rw [a_eq, W7 0 0 R_zero]; rfl
lemma a_8 : a 8 = 1932 := by rw [a_eq, W8 0 0 R_zero]; rfl

lemma a_rec_z (n : ℕ) : (a (n + 9) : ℤ) + (a (n + 3) : ℤ) + 15 * (a (n + 5) : ℤ) + 15 * (a (n + 7) : ℤ) = 6 * (a (n + 4) : ℤ) + 20 * (a (n + 6) : ℤ) + 6 * (a (n + 8) : ℤ) := by
  exact_mod_cast a_rec n

/-- The recurrence of the entry, for n > 8. -/
theorem recur : ∀ n : ℕ, 8 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 9 := ⟨n - 9, by omega⟩
  have h := a_rec_z j
  simp only [show j + 9 - 1 = j + 8 by omega, show j + 9 - 2 = j + 7 by omega, show j + 9 - 3 = j + 6 by omega, show j + 9 - 4 = j + 5 by omega, show j + 9 - 5 = j + 4 by omega, show j + 9 - 6 = j + 3 by omega]
  linear_combination h

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 6 = X * (4 - 9 * X + 18 * X ^ 2 - 18 * X ^ 3 + 14 * X ^ 4 - 6 * X ^ 5 - X ^ 6 + 2 * X ^ 7) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 6 = A - A * X ^ 1 * C 6 + A * X ^ 2 * C 15 - A * X ^ 3 * C 20 + A * X ^ 4 * C 15 - A * X ^ 5 * C 6 + A * X ^ 6 := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6, show (C (15 : ℚ) : ℚ⟦X⟧) = 15 from map_ofNat C 15, show (C (20 : ℚ) : ℚ⟦X⟧) = 20 from map_ofNat C 20]
    ring
  have e2 : (X * (4 - 9 * X + 18 * X ^ 2 - 18 * X ^ 3 + 14 * X ^ 4 - 6 * X ^ 5 - X ^ 6 + 2 * X ^ 7) : ℚ⟦X⟧) = X ^ 1 * C 4 - X ^ 2 * C 9 + X ^ 3 * C 18 - X ^ 4 * C 18 + X ^ 5 * C 14 - X ^ 6 * C 6 - X ^ 7 + X ^ 8 * C 2 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2, show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6, show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9, show (C (14 : ℚ) : ℚ⟦X⟧) = 14 from map_ofNat C 14, show (C (18 : ℚ) : ℚ⟦X⟧) = 18 from map_ofNat C 18]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_1] <;> norm_num
  · simp [a_1, a_2] <;> norm_num
  · simp [a_1, a_2, a_3] <;> norm_num
  · simp [a_1, a_2, a_3, a_4] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8] <;> norm_num
  · have hz := a_rec_z (n + 0)
    have hq : (a (n + 0 + 9) : ℚ) + (a (n + 0 + 3) : ℚ) + 15 * (a (n + 0 + 5) : ℚ) + 15 * (a (n + 0 + 7) : ℚ) = 6 * (a (n + 0 + 4) : ℚ) + 20 * (a (n + 0 + 6) : ℚ) + 6 * (a (n + 0 + 8) : ℚ) := by
      exact_mod_cast hz
    simp only [show n + 0 + 9 = n + 9 by omega, show n + 0 + 3 = n + 3 by omega, show n + 0 + 5 = n + 5 by omega, show n + 0 + 7 = n + 7 by omega, show n + 0 + 4 = n + 4 by omega, show n + 0 + 6 = n + 6 by omega, show n + 0 + 8 = n + 8 by omega] at hq
    simp only [if_false, if_true, show ¬ (n + 9 = 0) by omega,
      show 1 ≤ n + 9 by omega,
      show ¬ (n + 9 - 1 = 0) by omega,
      show n + 9 - 1 = n + 8 by omega,
      show ¬ (n + 8 = 0) by omega,
      show 2 ≤ n + 9 by omega,
      show ¬ (n + 9 - 2 = 0) by omega,
      show n + 9 - 2 = n + 7 by omega,
      show ¬ (n + 7 = 0) by omega,
      show 3 ≤ n + 9 by omega,
      show ¬ (n + 9 - 3 = 0) by omega,
      show n + 9 - 3 = n + 6 by omega,
      show ¬ (n + 6 = 0) by omega,
      show 4 ≤ n + 9 by omega,
      show ¬ (n + 9 - 4 = 0) by omega,
      show n + 9 - 4 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 5 ≤ n + 9 by omega,
      show ¬ (n + 9 - 5 = 0) by omega,
      show n + 9 - 5 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 6 ≤ n + 9 by omega,
      show ¬ (n + 9 - 6 = 0) by omega,
      show n + 9 - 6 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show ¬ (n + 9 = 1) by omega,
      show ¬ (n + 9 = 2) by omega,
      show ¬ (n + 9 = 3) by omega,
      show ¬ (n + 9 = 4) by omega,
      show ¬ (n + 9 = 5) by omega,
      show ¬ (n + 9 = 6) by omega,
      show ¬ (n + 9 = 7) by omega,
      show ¬ (n + 9 = 8) by omega]
    linear_combination hq

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 6 = X * (4 - 9 * X + 18 * X ^ 2 - 18 * X ^ 3 + 14 * X ^ 4 - 6 * X ^ 5 - X ^ 6 + 2 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a240333

theorem OMA.solution : type_of% @OMA.S_oeis_a240333.main :=
  OMA.S_oeis_a240333.conjecture
