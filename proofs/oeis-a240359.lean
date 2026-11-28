import OMAStatements.S_oeis_a240359

namespace OMA.S_oeis_a240359

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
    (v s).val ≠ (2 + (D s).val) % 4

instance {j : ℕ} (A D : Fin j → Fin 4) (off : ℕ) : DecidablePred (colOKo A D off) := fun v => by
  unfold colOKo; infer_instance

lemma sum_cons {j : ℕ} (G : (Fin (j + 1) → Fin 4) → ℕ) :
    ∑ v, G v = ∑ x : Fin 4, ∑ w : Fin j → Fin 4, G (Fin.cons x w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 4) _ _ (fun p => rfl)).symm

lemma colOKo_cons {j : ℕ} (A D : Fin (j + 1) → Fin 4) (off : ℕ) (x : Fin 4) (w : Fin j → Fin 4) :
    colOKo A D off (Fin.cons x w : Fin (j + 1) → Fin 4) ↔
      (x.val ≠ (2 + (A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (2 + (D 0).val) % 4) ∧
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
      if x.val ≠ (2 + (A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (2 + (D 0).val) % 4 then
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
    by_cases hc : x.val ≠ (2 + (A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (2 + (D 0).val) % 4
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
    (g t s).val ≠ (1 + ∑ s' ∈ Iio s, (g t s').val) % 4 ∧
    (g t s).val ≠ (2 + dg D g t s) % 4

instance (A D : Fin 2 → Fin 4) {m : ℕ} : DecidablePred (@V A D m) := fun g => by
  unfold V; infer_instance

lemma V_cons (A D : Fin 2 → Fin 4) {m : ℕ} (v : Fin 2 → Fin 4) (g : Fin m → Fin 2 → Fin 4) :
    V A D (Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 4) ↔ colOKo A D 1 v ∧ V (nxt A v) (nxtD D v) g := by
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
      (2 + dg D (Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 4) t.succ s) % 4 =
      (2 + dg (nxtD D v) g t s) % 4 := by
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
    W (m + 1) A D = ∑ v : Fin 2 → Fin 4, if colOKo A D 1 v then W m (nxt A v) (nxtD D v) else 0 := by
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
    ![![true, false, false, true],
      ![true, false, false, true],
      ![true, false, false, true],
      ![true, false, false, true]],
    ![![false, false, false, true],
      ![false, false, false, true],
      ![false, false, false, true],
      ![false, false, false, true]],
    ![![true, false, false, false],
      ![true, false, false, true],
      ![true, false, false, true],
      ![true, false, false, true]]]

def T1 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![4, 0, 0, 0],
      ![2, 0, 0, 0],
      ![3, 0, 0, 0],
      ![3, 0, 0, 0]],
    ![![2, 0, 0, 2],
      ![1, 0, 0, 2],
      ![1, 0, 0, 2],
      ![2, 0, 0, 3]],
    ![![0, 0, 0, 1],
      ![0, 0, 0, 1],
      ![0, 0, 0, 2],
      ![0, 0, 0, 2]],
    ![![4, 0, 0, 0],
      ![2, 0, 0, 3],
      ![3, 0, 0, 4],
      ![3, 0, 0, 5]]]

def T2 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![15, 0, 0, 0],
      ![6, 0, 0, 0],
      ![10, 0, 0, 0],
      ![10, 0, 0, 0]],
    ![![4, 0, 0, 4],
      ![1, 0, 0, 3],
      ![1, 0, 0, 3],
      ![3, 0, 0, 4]],
    ![![0, 0, 0, 3],
      ![0, 0, 0, 3],
      ![0, 0, 0, 4],
      ![0, 0, 0, 4]],
    ![![10, 0, 0, 0],
      ![4, 0, 0, 7],
      ![5, 0, 0, 8],
      ![8, 0, 0, 11]]]

def T3 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![43, 0, 0, 0],
      ![14, 0, 0, 0],
      ![24, 0, 0, 0],
      ![28, 0, 0, 0]],
    ![![7, 0, 0, 7],
      ![1, 0, 0, 4],
      ![1, 0, 0, 5],
      ![4, 0, 0, 5]],
    ![![0, 0, 0, 4],
      ![0, 0, 0, 4],
      ![0, 0, 0, 7],
      ![0, 0, 0, 6]],
    ![![25, 0, 0, 0],
      ![8, 0, 0, 16],
      ![11, 0, 0, 20],
      ![17, 0, 0, 24]]]

def T4 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![111, 0, 0, 0],
      ![34, 0, 0, 0],
      ![54, 0, 0, 0],
      ![72, 0, 0, 0]],
    ![![11, 0, 0, 11],
      ![1, 0, 0, 5],
      ![1, 0, 0, 8],
      ![5, 0, 0, 6]],
    ![![0, 0, 0, 5],
      ![0, 0, 0, 5],
      ![0, 0, 0, 11],
      ![0, 0, 0, 9]],
    ![![52, 0, 0, 0],
      ![15, 0, 0, 31],
      ![18, 0, 0, 41],
      ![35, 0, 0, 47]]]

def T5 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![261, 0, 0, 0],
      ![75, 0, 0, 0],
      ![112, 0, 0, 0],
      ![167, 0, 0, 0]],
    ![![16, 0, 0, 16],
      ![1, 0, 0, 6],
      ![1, 0, 0, 12],
      ![6, 0, 0, 7]],
    ![![0, 0, 0, 6],
      ![0, 0, 0, 6],
      ![0, 0, 0, 16],
      ![0, 0, 0, 13]],
    ![![101, 0, 0, 0],
      ![26, 0, 0, 59],
      ![29, 0, 0, 77],
      ![64, 0, 0, 84]]]

def T6 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![571, 0, 0, 0],
      ![152, 0, 0, 0],
      ![218, 0, 0, 0],
      ![356, 0, 0, 0]],
    ![![22, 0, 0, 22],
      ![1, 0, 0, 7],
      ![1, 0, 0, 17],
      ![7, 0, 0, 8]],
    ![![0, 0, 0, 7],
      ![0, 0, 0, 7],
      ![0, 0, 0, 22],
      ![0, 0, 0, 18]],
    ![![184, 0, 0, 0],
      ![42, 0, 0, 103],
      ![45, 0, 0, 139],
      ![109, 0, 0, 141]]]

def T7 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![1171, 0, 0, 0],
      ![291, 0, 0, 0],
      ![396, 0, 0, 0],
      ![713, 0, 0, 0]],
    ![![29, 0, 0, 29],
      ![1, 0, 0, 8],
      ![1, 0, 0, 23],
      ![8, 0, 0, 9]],
    ![![0, 0, 0, 8],
      ![0, 0, 0, 8],
      ![0, 0, 0, 29],
      ![0, 0, 0, 24]],
    ![![318, 0, 0, 0],
      ![64, 0, 0, 169],
      ![67, 0, 0, 240],
      ![176, 0, 0, 225]]]

def T8 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![2278, 0, 0, 0],
      ![531, 0, 0, 0],
      ![685, 0, 0, 0],
      ![1349, 0, 0, 0]],
    ![![37, 0, 0, 37],
      ![1, 0, 0, 9],
      ![1, 0, 0, 30],
      ![9, 0, 0, 10]],
    ![![0, 0, 0, 9],
      ![0, 0, 0, 9],
      ![0, 0, 0, 37],
      ![0, 0, 0, 31]],
    ![![526, 0, 0, 0],
      ![93, 0, 0, 264],
      ![96, 0, 0, 398],
      ![272, 0, 0, 344]]]

def T9 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![4235, 0, 0, 0],
      ![929, 0, 0, 0],
      ![1139, 0, 0, 0],
      ![2432, 0, 0, 0]],
    ![![46, 0, 0, 46],
      ![1, 0, 0, 10],
      ![1, 0, 0, 38],
      ![10, 0, 0, 11]],
    ![![0, 0, 0, 10],
      ![0, 0, 0, 10],
      ![0, 0, 0, 46],
      ![0, 0, 0, 39]],
    ![![838, 0, 0, 0],
      ![130, 0, 0, 396],
      ![133, 0, 0, 637],
      ![405, 0, 0, 507]]]

def T10 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![7570, 0, 0, 0],
      ![1566, 0, 0, 0],
      ![1832, 0, 0, 0],
      ![4208, 0, 0, 0]],
    ![![56, 0, 0, 56],
      ![1, 0, 0, 11],
      ![1, 0, 0, 47],
      ![11, 0, 0, 12]],
    ![![0, 0, 0, 11],
      ![0, 0, 0, 11],
      ![0, 0, 0, 56],
      ![0, 0, 0, 48]],
    ![![1292, 0, 0, 0],
      ![176, 0, 0, 574],
      ![179, 0, 0, 988],
      ![584, 0, 0, 724]]]

def T11 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![13076, 0, 0, 0],
      ![2554, 0, 0, 0],
      ![2864, 0, 0, 0],
      ![7028, 0, 0, 0]],
    ![![67, 0, 0, 67],
      ![1, 0, 0, 12],
      ![1, 0, 0, 57],
      ![12, 0, 0, 13]],
    ![![0, 0, 0, 12],
      ![0, 0, 0, 12],
      ![0, 0, 0, 67],
      ![0, 0, 0, 58]],
    ![![1935, 0, 0, 0],
      ![232, 0, 0, 808],
      ![235, 0, 0, 1490],
      ![819, 0, 0, 1006]]]

def T12 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![21918, 0, 0, 0],
      ![4044, 0, 0, 0],
      ![4368, 0, 0, 0],
      ![11382, 0, 0, 0]],
    ![![79, 0, 0, 79],
      ![1, 0, 0, 13],
      ![1, 0, 0, 68],
      ![13, 0, 0, 14]],
    ![![0, 0, 0, 13],
      ![0, 0, 0, 13],
      ![0, 0, 0, 79],
      ![0, 0, 0, 69]],
    ![![2824, 0, 0, 0],
      ![299, 0, 0, 1109],
      ![302, 0, 0, 2191],
      ![1121, 0, 0, 1365]]]

def T13 : Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![35774, 0, 0, 0],
      ![6235, 0, 0, 0],
      ![6518, 0, 0, 0],
      ![17941, 0, 0, 0]],
    ![![92, 0, 0, 92],
      ![1, 0, 0, 14],
      ![1, 0, 0, 80],
      ![14, 0, 0, 15]],
    ![![0, 0, 0, 14],
      ![0, 0, 0, 14],
      ![0, 0, 0, 92],
      ![0, 0, 0, 81]],
    ![![4027, 0, 0, 0],
      ![378, 0, 0, 1489],
      ![381, 0, 0, 3149],
      ![1502, 0, 0, 1814]]]

set_option maxHeartbeats 4000000 in
lemma closure : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1
      (fun v => (fun B E => if reach (B 0) (B 1) (E 1) = true then 0 else 1) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check1 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun _ _ => 1) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T1 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check2 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T1 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T2 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check3 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T2 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T3 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check4 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T3 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T4 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check5 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T4 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T5 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check6 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T5 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T6 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check7 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T6 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T7 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check8 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T7 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T8 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check9 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T8 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T9 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check10 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T9 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T10 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check11 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T10 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T11 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check12 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T11 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T12 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check13 : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T12 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) = T13 a0 a1 d1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ a0 a1 d1 : Fin 4, reach a0 a1 d1 = true →
    nest 2 ![a0, a1] ![0, d1] 1 (fun v => (fun B E => T13 (B 0) (B 1) (E 1)) (nxt ![a0, a1] v) (nxtD ![0, d1] v)) + 9 * T6 a0 a1 d1 + 84 * T8 a0 a1 d1 + 126 * T10 a0 a1 d1 + 36 * T12 a0 a1 d1 = T5 a0 a1 d1 + 36 * T7 a0 a1 d1 + 126 * T9 a0 a1 d1 + 84 * T11 a0 a1 d1 + 9 * T13 a0 a1 d1 := by
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

lemma R_nxt (A D v : Fin 2 → Fin 4) (hA : R A D) (hv : colOKo A D 1 v) : R (nxt A v) (nxtD D v) := by
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
    W (m + 1) A D = nest 2 A D 1 (fun v => F (nxt A v) (nxtD D v)) := by
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

lemma W9 (A D : Fin 2 → Fin 4) (hA : R A D) : W 9 A D = T9 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 8 A D (fun B E => T8 (B 0) (B 1) (E 1)) W8 hA, vec_eta A, vec_etaD D hA.1]
  exact check9 _ _ _ hA.2

lemma W10 (A D : Fin 2 → Fin 4) (hA : R A D) : W 10 A D = T10 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 9 A D (fun B E => T9 (B 0) (B 1) (E 1)) W9 hA, vec_eta A, vec_etaD D hA.1]
  exact check10 _ _ _ hA.2

lemma W11 (A D : Fin 2 → Fin 4) (hA : R A D) : W 11 A D = T11 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 10 A D (fun B E => T10 (B 0) (B 1) (E 1)) W10 hA, vec_eta A, vec_etaD D hA.1]
  exact check11 _ _ _ hA.2

lemma W12 (A D : Fin 2 → Fin 4) (hA : R A D) : W 12 A D = T12 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 11 A D (fun B E => T11 (B 0) (B 1) (E 1)) W11 hA, vec_eta A, vec_etaD D hA.1]
  exact check12 _ _ _ hA.2

lemma W13 (A D : Fin 2 → Fin 4) (hA : R A D) : W 13 A D = T13 (A 0) (A 1) (D 1) := by
  rw [W_succ_R 12 A D (fun B E => T12 (B 0) (B 1) (E 1)) W12 hA, vec_eta A, vec_etaD D hA.1]
  exact check13 _ _ _ hA.2

lemma W_rec (n : ℕ) (A D : Fin 2 → Fin 4) (hA : R A D) :
    W (n + 14) A D + 9 * W (n + 6) A D + 84 * W (n + 8) A D + 126 * W (n + 10) A D + 36 * W (n + 12) A D = W (n + 5) A D + 36 * W (n + 7) A D + 126 * W (n + 9) A D + 84 * W (n + 11) A D + 9 * W (n + 13) A D := by
  induction n generalizing A D with
  | zero =>
    rw [show (0 : ℕ) + 14 = 13 + 1 from rfl, W_succ_R 13 A D (fun B E => T13 (B 0) (B 1) (E 1)) W13 hA, show (0 : ℕ) + 6 = 6 from rfl, W6 A D hA, show (0 : ℕ) + 8 = 8 from rfl, W8 A D hA, show (0 : ℕ) + 10 = 10 from rfl, W10 A D hA, show (0 : ℕ) + 12 = 12 from rfl, W12 A D hA, show (0 : ℕ) + 5 = 5 from rfl, W5 A D hA, show (0 : ℕ) + 7 = 7 from rfl, W7 A D hA, show (0 : ℕ) + 9 = 9 from rfl, W9 A D hA, show (0 : ℕ) + 11 = 11 from rfl, W11 A D hA, show (0 : ℕ) + 13 = 13 from rfl, W13 A D hA, vec_eta A, vec_etaD D hA.1]
    exact base_check _ _ _ hA.2
  | succ n ih =>
    rw [W_succ (n + 14), W_succ (n + 6), W_succ (n + 8), W_succ (n + 10), W_succ (n + 12), W_succ (n + 5), W_succ (n + 7), W_succ (n + 9), W_succ (n + 11), W_succ (n + 13)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : colOKo A D 1 v
    · simp only [if_pos hv]
      exact ih _ _ (R_nxt A D v hA hv)
    · simp [hv]

lemma R_zero : R 0 0 := by
  unfold R
  decide +kernel

lemma a_rec (n : ℕ) : a (n + 14) + 9 * a (n + 6) + 84 * a (n + 8) + 126 * a (n + 10) + 36 * a (n + 12) = a (n + 5) + 36 * a (n + 7) + 126 * a (n + 9) + 84 * a (n + 11) + 9 * a (n + 13) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  exact W_rec n 0 0 R_zero

lemma a_zero : a 0 = 1 := by rw [a_eq, W_zero]
lemma a_1 : a 1 = 4 := by rw [a_eq, W1 0 0 R_zero]; rfl
lemma a_2 : a 2 = 15 := by rw [a_eq, W2 0 0 R_zero]; rfl
lemma a_3 : a 3 = 43 := by rw [a_eq, W3 0 0 R_zero]; rfl
lemma a_4 : a 4 = 111 := by rw [a_eq, W4 0 0 R_zero]; rfl
lemma a_5 : a 5 = 261 := by rw [a_eq, W5 0 0 R_zero]; rfl
lemma a_6 : a 6 = 571 := by rw [a_eq, W6 0 0 R_zero]; rfl
lemma a_7 : a 7 = 1171 := by rw [a_eq, W7 0 0 R_zero]; rfl
lemma a_8 : a 8 = 2278 := by rw [a_eq, W8 0 0 R_zero]; rfl
lemma a_9 : a 9 = 4235 := by rw [a_eq, W9 0 0 R_zero]; rfl
lemma a_10 : a 10 = 7570 := by rw [a_eq, W10 0 0 R_zero]; rfl
lemma a_11 : a 11 = 13076 := by rw [a_eq, W11 0 0 R_zero]; rfl
lemma a_12 : a 12 = 21918 := by rw [a_eq, W12 0 0 R_zero]; rfl
lemma a_13 : a 13 = 35774 := by rw [a_eq, W13 0 0 R_zero]; rfl

lemma a_rec_z (n : ℕ) : (a (n + 14) : ℤ) + 9 * (a (n + 6) : ℤ) + 84 * (a (n + 8) : ℤ) + 126 * (a (n + 10) : ℤ) + 36 * (a (n + 12) : ℤ) = (a (n + 5) : ℤ) + 36 * (a (n + 7) : ℤ) + 126 * (a (n + 9) : ℤ) + 84 * (a (n + 11) : ℤ) + 9 * (a (n + 13) : ℤ) := by
  exact_mod_cast a_rec n

/-- The recurrence of the entry, for n > 13. -/
theorem recur : ∀ n : ℕ, 13 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 14 := ⟨n - 14, by omega⟩
  have h := a_rec_z j
  simp only [show j + 14 - 1 = j + 13 by omega, show j + 14 - 2 = j + 12 by omega, show j + 14 - 3 = j + 11 by omega, show j + 14 - 4 = j + 10 by omega, show j + 14 - 5 = j + 9 by omega, show j + 14 - 6 = j + 8 by omega, show j + 14 - 7 = j + 7 by omega, show j + 14 - 8 = j + 6 by omega, show j + 14 - 9 = j + 5 by omega]
  linear_combination h

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 9 = X * (4 - 21 * X + 52 * X ^ 2 - 72 * X ^ 3 + 54 * X ^ 4 - 8 * X ^ 5 - 32 * X ^ 6 + 55 * X ^ 7 - 67 * X ^ 8 + 66 * X ^ 9 - 46 * X ^ 10 + 20 * X ^ 11 - 4 * X ^ 12) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 9 = A - A * X ^ 1 * C 9 + A * X ^ 2 * C 36 - A * X ^ 3 * C 84 + A * X ^ 4 * C 126 - A * X ^ 5 * C 126 + A * X ^ 6 * C 84 - A * X ^ 7 * C 36 + A * X ^ 8 * C 9 - A * X ^ 9 := by
    rw [show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9, show (C (36 : ℚ) : ℚ⟦X⟧) = 36 from map_ofNat C 36, show (C (84 : ℚ) : ℚ⟦X⟧) = 84 from map_ofNat C 84, show (C (126 : ℚ) : ℚ⟦X⟧) = 126 from map_ofNat C 126]
    ring
  have e2 : (X * (4 - 21 * X + 52 * X ^ 2 - 72 * X ^ 3 + 54 * X ^ 4 - 8 * X ^ 5 - 32 * X ^ 6 + 55 * X ^ 7 - 67 * X ^ 8 + 66 * X ^ 9 - 46 * X ^ 10 + 20 * X ^ 11 - 4 * X ^ 12) : ℚ⟦X⟧) = X ^ 1 * C 4 - X ^ 2 * C 21 + X ^ 3 * C 52 - X ^ 4 * C 72 + X ^ 5 * C 54 - X ^ 6 * C 8 - X ^ 7 * C 32 + X ^ 8 * C 55 - X ^ 9 * C 67 + X ^ 10 * C 66 - X ^ 11 * C 46 + X ^ 12 * C 20 - X ^ 13 * C 4 := by
    rw [show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8, show (C (20 : ℚ) : ℚ⟦X⟧) = 20 from map_ofNat C 20, show (C (21 : ℚ) : ℚ⟦X⟧) = 21 from map_ofNat C 21, show (C (32 : ℚ) : ℚ⟦X⟧) = 32 from map_ofNat C 32, show (C (46 : ℚ) : ℚ⟦X⟧) = 46 from map_ofNat C 46, show (C (52 : ℚ) : ℚ⟦X⟧) = 52 from map_ofNat C 52, show (C (54 : ℚ) : ℚ⟦X⟧) = 54 from map_ofNat C 54, show (C (55 : ℚ) : ℚ⟦X⟧) = 55 from map_ofNat C 55, show (C (66 : ℚ) : ℚ⟦X⟧) = 66 from map_ofNat C 66, show (C (67 : ℚ) : ℚ⟦X⟧) = 67 from map_ofNat C 67, show (C (72 : ℚ) : ℚ⟦X⟧) = 72 from map_ofNat C 72]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_1] <;> norm_num
  · simp [a_1, a_2] <;> norm_num
  · simp [a_1, a_2, a_3] <;> norm_num
  · simp [a_1, a_2, a_3, a_4] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12, a_13] <;> norm_num
  · have hz := a_rec_z (n + 0)
    have hq : (a (n + 0 + 14) : ℚ) + 9 * (a (n + 0 + 6) : ℚ) + 84 * (a (n + 0 + 8) : ℚ) + 126 * (a (n + 0 + 10) : ℚ) + 36 * (a (n + 0 + 12) : ℚ) = (a (n + 0 + 5) : ℚ) + 36 * (a (n + 0 + 7) : ℚ) + 126 * (a (n + 0 + 9) : ℚ) + 84 * (a (n + 0 + 11) : ℚ) + 9 * (a (n + 0 + 13) : ℚ) := by
      exact_mod_cast hz
    simp only [show n + 0 + 14 = n + 14 by omega, show n + 0 + 6 = n + 6 by omega, show n + 0 + 8 = n + 8 by omega, show n + 0 + 10 = n + 10 by omega, show n + 0 + 12 = n + 12 by omega, show n + 0 + 5 = n + 5 by omega, show n + 0 + 7 = n + 7 by omega, show n + 0 + 9 = n + 9 by omega, show n + 0 + 11 = n + 11 by omega, show n + 0 + 13 = n + 13 by omega] at hq
    simp only [if_false, if_true, show ¬ (n + 14 = 0) by omega,
      show 1 ≤ n + 14 by omega,
      show ¬ (n + 14 - 1 = 0) by omega,
      show n + 14 - 1 = n + 13 by omega,
      show ¬ (n + 13 = 0) by omega,
      show 2 ≤ n + 14 by omega,
      show ¬ (n + 14 - 2 = 0) by omega,
      show n + 14 - 2 = n + 12 by omega,
      show ¬ (n + 12 = 0) by omega,
      show 3 ≤ n + 14 by omega,
      show ¬ (n + 14 - 3 = 0) by omega,
      show n + 14 - 3 = n + 11 by omega,
      show ¬ (n + 11 = 0) by omega,
      show 4 ≤ n + 14 by omega,
      show ¬ (n + 14 - 4 = 0) by omega,
      show n + 14 - 4 = n + 10 by omega,
      show ¬ (n + 10 = 0) by omega,
      show 5 ≤ n + 14 by omega,
      show ¬ (n + 14 - 5 = 0) by omega,
      show n + 14 - 5 = n + 9 by omega,
      show ¬ (n + 9 = 0) by omega,
      show 6 ≤ n + 14 by omega,
      show ¬ (n + 14 - 6 = 0) by omega,
      show n + 14 - 6 = n + 8 by omega,
      show ¬ (n + 8 = 0) by omega,
      show 7 ≤ n + 14 by omega,
      show ¬ (n + 14 - 7 = 0) by omega,
      show n + 14 - 7 = n + 7 by omega,
      show ¬ (n + 7 = 0) by omega,
      show 8 ≤ n + 14 by omega,
      show ¬ (n + 14 - 8 = 0) by omega,
      show n + 14 - 8 = n + 6 by omega,
      show ¬ (n + 6 = 0) by omega,
      show 9 ≤ n + 14 by omega,
      show ¬ (n + 14 - 9 = 0) by omega,
      show n + 14 - 9 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show ¬ (n + 14 = 1) by omega,
      show ¬ (n + 14 = 2) by omega,
      show ¬ (n + 14 = 3) by omega,
      show ¬ (n + 14 = 4) by omega,
      show ¬ (n + 14 = 5) by omega,
      show ¬ (n + 14 = 6) by omega,
      show ¬ (n + 14 = 7) by omega,
      show ¬ (n + 14 = 8) by omega,
      show ¬ (n + 14 = 9) by omega,
      show ¬ (n + 14 = 10) by omega,
      show ¬ (n + 14 = 11) by omega,
      show ¬ (n + 14 = 12) by omega,
      show ¬ (n + 14 = 13) by omega]
    linear_combination hq

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 9 = X * (4 - 21 * X + 52 * X ^ 2 - 72 * X ^ 3 + 54 * X ^ 4 - 8 * X ^ 5 - 32 * X ^ 6 + 55 * X ^ 7 - 67 * X ^ 8 + 66 * X ^ 9 - 46 * X ^ 10 + 20 * X ^ 11 - 4 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a240359

theorem OMA.solution : type_of% @OMA.S_oeis_a240359.main :=
  OMA.S_oeis_a240359.conjecture
