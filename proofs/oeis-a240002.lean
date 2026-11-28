import OMAStatements.S_oeis_a240002

namespace OMA.S_oeis_a240002

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
def dget (D : Fin 3 → Fin 4) (p : ℕ) : ℕ := if h : p < 3 then (D ⟨p, h⟩).val else 0

lemma dget_fin (D : Fin 3 → Fin 4) (s : Fin 3) : dget D s.val = (D s).val := by
  unfold dget
  rw [dif_pos s.isLt]

/-- The northwest-diagonal sum entering (t, s) when the slices g start from the diagonal sums D. -/
def dg (D : Fin 3 → Fin 4) {m : ℕ} (g : Fin m → Fin 3 → Fin 4) (t : Fin m) (s : Fin 3) : ℕ :=
  (if t.val ≤ s.val then dget D (s.val - t.val) else 0) +
    ∑ t' ∈ Iio t, ∑ s' ∈ Iio s, if t.val - t'.val = s.val - s'.val then (g t' s').val else 0

/-- The running sums after the slice v. -/
def nxt (A v : Fin 3 → Fin 4) : Fin 3 → Fin 4 := fun s => A s + v s

/-- The diagonal sums entering the slice after v. -/
def nxtD (D v : Fin 3 → Fin 4) : Fin 3 → Fin 4 := ![0, D 0 + v 0, D 1 + v 1]

lemma dget_nxtD (D v : Fin 3 → Fin 4) (p : ℕ) (hp : p < 3) :
    dget (nxtD D v) p = if p = 0 then 0 else (dget D (p - 1) + dget v (p - 1)) % 4 := by
  interval_cases p <;> rfl

lemma diag_step (D v : Fin 3 → Fin 4) (t : ℕ) (s : Fin 3) :
    ((if t + 1 ≤ s.val then dget D (s.val - (t + 1)) else 0) +
      ∑ s' ∈ Iio s, (if t + 1 = s.val - s'.val then (v s').val else 0)) % 4 =
    (if t ≤ s.val then dget (nxtD D v) (s.val - t) else 0) % 4 := by
  have hs := s.isLt
  by_cases h : t + 1 ≤ s.val
  · have hsum : ∑ s' ∈ Iio s, (if t + 1 = s.val - s'.val then (v s').val else 0) =
        dget v (s.val - (t + 1)) := by
      rw [Finset.sum_eq_single_of_mem (⟨s.val - (t + 1), by omega⟩ : Fin 3)]
      · rw [if_pos]
        · simp [dget, show s.val - (t + 1) < 3 by omega]
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

lemma diag_T {n : ℕ} (f : Fin 3 → Fin n → Fin 4) (i : Fin 3) (j : Fin n) :
    (∑ i' ∈ Iio i, ∑ j' ∈ Iio j, if i.val - i'.val = j.val - j'.val then (f i' j').val else 0) =
      ∑ j' ∈ Iio j, ∑ i' ∈ Iio i, if j.val - j'.val = i.val - i'.val then (f i' j').val else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j' _ => Finset.sum_congr rfl (fun i' _ => ?_))
  split_ifs <;> omega

/-- The conditions on a slice v of any length when the running sums along the growing dimension
are A, the diagonal sums are D and the sums across start from off. -/
def colOKo {j : ℕ} (A D : Fin j → Fin 4) (off : ℕ) (v : Fin j → Fin 4) : Prop :=
  ∀ s : Fin j, (v s).val ≠ (1 + (A s).val) % 4 ∧ (v s).val ≠ (off + ∑ s' ∈ Iio s, (v s').val) % 4 ∧
    (v s).val ≠ (1 + (D s).val) % 4

instance {j : ℕ} (A D : Fin j → Fin 4) (off : ℕ) : DecidablePred (colOKo A D off) := fun v => by
  unfold colOKo; infer_instance

lemma sum_cons {j : ℕ} (G : (Fin (j + 1) → Fin 4) → ℕ) :
    ∑ v, G v = ∑ x : Fin 4, ∑ w : Fin j → Fin 4, G (Fin.cons x w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 4) _ _ (fun p => rfl)).symm

lemma colOKo_cons {j : ℕ} (A D : Fin (j + 1) → Fin 4) (off : ℕ) (x : Fin 4) (w : Fin j → Fin 4) :
    colOKo A D off (Fin.cons x w : Fin (j + 1) → Fin 4) ↔
      (x.val ≠ (1 + (A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (1 + (D 0).val) % 4) ∧
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

/-- The sum over Fin 4 written out, so that the kernel checks below avoid the Finset machinery. -/
def sumq (g : Fin 4 → ℕ) : ℕ := g 0 + g 1 + g 2 + g 3

lemma sumq_eq (g : Fin 4 → ℕ) : sumq g = ∑ x, g x := by
  unfold sumq
  rw [Fin.sum_univ_four]

/-- The allowed slices enumerated entry by entry: each entry runs over its allowed values, and the
finished slice goes to F. -/
def nest : (j : ℕ) → (Fin j → Fin 4) → (Fin j → Fin 4) → ℕ → ((Fin j → Fin 4) → ℕ) → ℕ
  | 0, _, _, _, F => F Fin.elim0
  | j + 1, A, D, off, F => sumq fun x =>
      if x.val ≠ (1 + (A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (1 + (D 0).val) % 4 then
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
    rw [sumq_eq]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hc : x.val ≠ (1 + (A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (1 + (D 0).val) % 4
    · rw [if_pos hc, ← ih (Fin.tail A) (Fin.tail D) (off + x.val) (fun w => F (Fin.cons x w))]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      simp only [colOKo_cons, hc, true_and, ne_eq, not_false_eq_true]
    · rw [if_neg hc]
      refine Finset.sum_eq_zero (fun w _ => ?_)
      rw [if_neg]
      rw [colOKo_cons]
      exact fun h => hc h.1

/-- An array of slices is valid when started from the running sums A and the diagonal sums D. -/
def V (A D : Fin 3 → Fin 4) {m : ℕ} (g : Fin m → Fin 3 → Fin 4) : Prop :=
  ∀ t : Fin m, ∀ s : Fin 3,
    (g t s).val ≠ (1 + ((A s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 4 ∧
    (g t s).val ≠ (2 + ∑ s' ∈ Iio s, (g t s').val) % 4 ∧
    (g t s).val ≠ (1 + dg D g t s) % 4

instance (A D : Fin 3 → Fin 4) {m : ℕ} : DecidablePred (@V A D m) := fun g => by
  unfold V; infer_instance

lemma V_cons (A D : Fin 3 → Fin 4) {m : ℕ} (v : Fin 3 → Fin 4) (g : Fin m → Fin 3 → Fin 4) :
    V A D (Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 4) ↔ colOKo A D 2 v ∧ V (nxt A v) (nxtD D v) g := by
  have key : ∀ (t : Fin m) (s : Fin 3),
      (1 + ((A s).val + ∑ t' ∈ Iio t.succ, ((Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 4) t' s).val)) % 4 =
      (1 + ((nxt A v s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 4 := by
    intro t s
    rw [sum_Iio_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, nxt, Fin.val_add]
    omega
  have key0 : ∀ s : Fin 3,
      (1 + ((A s).val + ∑ t' ∈ Iio (0 : Fin (m + 1)), ((Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 4) t' s).val)) % 4 =
      (1 + (A s).val) % 4 := by
    intro s
    rw [sum_Iio_zero, Nat.add_zero]
  have dkey0 : ∀ s : Fin 3, dg D (Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 4) 0 s = (D s).val := by
    intro s
    unfold dg
    rw [sum_Iio_zero, Nat.add_zero, Fin.val_zero, if_pos (Nat.zero_le _), Nat.sub_zero, dget_fin]
  have dkey : ∀ (t : Fin m) (s : Fin 3),
      (1 + dg D (Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 4) t.succ s) % 4 =
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
def W (m : ℕ) (A D : Fin 3 → Fin 4) : ℕ :=
  ((univ : Finset (Fin m → Fin 3 → Fin 4)).filter (V A D)).card

lemma W_zero (A D : Fin 3 → Fin 4) : W 0 A D = 1 := by
  have e : (univ : Finset (Fin 0 → Fin 3 → Fin 4)).filter (V A D) = univ :=
    Finset.filter_true_of_mem (fun g _ t => Fin.elim0 t)
  rw [W, e]
  simp

lemma W_succ (m : ℕ) (A D : Fin 3 → Fin 4) :
    W (m + 1) A D = ∑ v : Fin 3 → Fin 4, if colOKo A D 2 v then W m (nxt A v) (nxtD D v) else 0 := by
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
  refine Finset.card_bij' (fun f _ => fun t s => f s t) (fun g _ => fun i j => g j i) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_filter, mem_univ, true_and, good, V, dg, dget, Pi.zero_apply, Fin.val_zero,
      zero_add, dite_eq_ite, ite_self] at hf ⊢
    intro t s
    obtain ⟨h1, h2, h3⟩ := hf s t
    exact ⟨h1, h2, by rwa [diag_T] at h3⟩
  · intro g hg
    simp only [mem_filter, mem_univ, true_and, good, V, dg, dget, Pi.zero_apply, Fin.val_zero,
      zero_add, dite_eq_ite, ite_self] at hg ⊢
    intro i j
    obtain ⟨h1, h2, h3⟩ := hg j i
    exact ⟨h1, h2, by rwa [diag_T]⟩
  · intro f _
    rfl
  · intro g _
    rfl

/-- The reachable states, by A 0, ..., A 2, D 1, ..., D 2 (D 0 = 0). -/
def reach : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Bool :=
  ![![![![![true, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]]],
    ![![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]]],
    ![![![![true, false, true, false], ![false, false, false, false], ![false, false, false, false], ![false, true, true, false]], ![![true, false, true, false], ![false, false, false, false], ![false, false, false, false], ![false, true, true, false]], ![![true, false, true, false], ![false, false, false, false], ![false, false, false, false], ![false, true, true, false]], ![![true, false, true, false], ![false, false, false, false], ![false, false, false, false], ![false, true, true, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, true, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, true, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, true, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, true, false, false]]],
      ![![![true, false, true, true], ![false, false, false, false], ![false, false, false, false], ![false, true, true, false]], ![![true, false, true, true], ![false, false, false, false], ![false, false, false, false], ![false, true, true, false]], ![![true, false, true, true], ![false, false, false, false], ![false, false, false, false], ![false, true, true, false]], ![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, true, true, false]]],
      ![![![true, false, true, true], ![false, false, false, false], ![false, false, false, false], ![false, false, true, false]], ![![true, false, true, true], ![false, false, false, false], ![false, false, false, false], ![false, false, true, false]], ![![true, false, true, true], ![false, false, false, false], ![false, false, false, false], ![false, false, true, false]], ![![true, false, true, true], ![false, false, false, false], ![false, false, false, false], ![false, false, true, false]]]],
    ![![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![true, false, true, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![true, false, true, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![true, false, true, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![true, false, true, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, true, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, true, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, true, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, true, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![true, false, true, true]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![true, false, true, true]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![true, false, true, true]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![true, false, false, true]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, true]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, true]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, true]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, true]]]]]
abbrev u : Fin 4 → Fin 4 → ℕ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


def T1 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![12, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![8, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![8, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![7, 0, 0, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![5, 0, 0, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![4, 0, 0, 6], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 5], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 5], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 7], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![5, 0, 3, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 2, 0]], ![![4, 0, 3, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 1, 0]], ![![3, 0, 4, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 2, 0]], ![![3, 0, 2, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 1, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 3, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 4, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 3, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 0, 0]]],
      ![![![2, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 2, 0]], ![![2, 0, 2, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 2, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 3, 0]], ![![1, 0, 0, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 2, 0]]],
      ![![![3, 0, 2, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![2, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 3, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 5, 0]], ![![2, 0, 1, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 3, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![4, 0, 3, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 3, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![3, 0, 5, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![3, 0, 4, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 2, 1]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 2, 1]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 3, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 2]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 3]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 3]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 4]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 5]]]]]

def T2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![61, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![33, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![31, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![24, 0, 0, 12], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 19], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![17, 0, 0, 13], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![11, 0, 0, 21], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 16], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 9], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 10], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 14], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![13, 0, 8, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 3, 4, 0]], ![![12, 0, 8, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 3, 1, 0]], ![![6, 0, 9, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![5, 0, 6, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 1, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 7, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 9, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 6, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 6, 0, 0]]],
      ![![![3, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 3, 5, 0]], ![![4, 0, 3, 3], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 4, 4, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 4, 7, 0]], ![![1, 0, 0, 3], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 3, 5, 0]]],
      ![![![4, 0, 2, 3], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 11, 0]], ![![3, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 9, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 14, 0]], ![![3, 0, 2, 3], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 11, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![11, 0, 8, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![6, 0, 9, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![7, 0, 11, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![10, 0, 10, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 3, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 3, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![3, 0, 3, 1]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 3, 1]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![3, 0, 4, 3]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2, 0, 0, 4]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 8]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 8]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 9]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 14]]]]]

def T3 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![190, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![92, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![85, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![62, 0, 0, 27], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 55], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![42, 0, 0, 32], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![31, 0, 0, 63], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 44], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 19], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 22], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 41], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![25, 0, 17, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 4, 4, 0]], ![![29, 0, 19, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 4, 2, 0]], ![![10, 0, 15, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![8, 0, 14, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 2, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 17, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 21, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 11, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 12, 0, 0]]],
      ![![![4, 0, 3, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 4, 6, 0]], ![![7, 0, 5, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 5, 5, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 5, 9, 0]], ![![1, 0, 0, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 4, 7, 0]]],
      ![![![5, 0, 2, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 23, 0]], ![![4, 0, 3, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 21, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 28, 0]], ![![4, 0, 3, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 28, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![32, 0, 21, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![15, 0, 22, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![18, 0, 32, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![27, 0, 27, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 5, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 5, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![5, 0, 5, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![3, 0, 5, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![5, 0, 7, 5]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![3, 0, 0, 6]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 18]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 18]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 23]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 32]]]]]

def T4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![526, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![238, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![212, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![159, 0, 0, 71], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 141], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![105, 0, 0, 84], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![72, 0, 0, 155], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 111], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 39], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 44], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 104], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![42, 0, 30, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 5, 4, 0]], ![![59, 0, 40, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 5, 3, 0]], ![![15, 0, 23, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![12, 0, 26, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 3, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 35, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 44, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 17, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 19, 0, 0]]],
      ![![![5, 0, 4, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 5, 7, 0]], ![![11, 0, 8, 5], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 6, 6, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 6, 11, 0]], ![![1, 0, 0, 5], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 5, 9, 0]]],
      ![![![6, 0, 2, 5], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 40, 0]], ![![5, 0, 4, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 44, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 48, 0]], ![![5, 0, 4, 5], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 59, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![65, 0, 37, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![28, 0, 38, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![32, 0, 64, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![54, 0, 53, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 6, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 6, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![6, 0, 6, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![4, 0, 6, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![6, 0, 8, 6]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![4, 0, 0, 8]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 27]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 26]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 42]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 58]]]]]

def T5 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![1262, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![531, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![455, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![348, 0, 0, 146], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 334], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![218, 0, 0, 168], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![153, 0, 0, 349], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 259], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 85], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 91], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 243], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![65, 0, 48, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 6, 4, 0]], ![![107, 0, 75, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 6, 4, 0]], ![![21, 0, 33, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![17, 0, 43, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 61, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 82, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 25, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 28, 0, 0]]],
      ![![![6, 0, 5, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 6, 8, 0]], ![![16, 0, 12, 6], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 7, 7, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 7, 13, 0]], ![![1, 0, 0, 6], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 6, 11, 0]]],
      ![![![7, 0, 2, 6], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 63, 0]], ![![6, 0, 5, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 82, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 75, 0]], ![![6, 0, 5, 6], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 109, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![118, 0, 59, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![46, 0, 60, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![51, 0, 115, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![98, 0, 95, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 7, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 7, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![7, 0, 7, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![5, 0, 7, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![7, 0, 9, 7]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![5, 0, 0, 10]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 37]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 35]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 70]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 103]]]]]

def T6 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![2766, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![1103, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![916, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![694, 0, 0, 280], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 688], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![406, 0, 0, 314], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![290, 0, 0, 697], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 541], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 162], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 169], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 521], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![95, 0, 72, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 7, 4, 0]], ![![179, 0, 129, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 7, 5, 0]], ![![28, 0, 45, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![23, 0, 66, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 5, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 97, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 140, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 35, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 39, 0, 0]]],
      ![![![7, 0, 6, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 7, 9, 0]], ![![22, 0, 17, 7], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 8, 8, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 8, 15, 0]], ![![1, 0, 0, 7], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 7, 13, 0]]],
      ![![![8, 0, 2, 7], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 93, 0]], ![![7, 0, 6, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 140, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 110, 0]], ![![7, 0, 6, 7], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 184, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![197, 0, 88, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![70, 0, 89, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![76, 0, 191, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![164, 0, 158, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 8, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 8, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![8, 0, 8, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![6, 0, 8, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![8, 0, 10, 8]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![6, 0, 0, 12]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 49]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 46]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 108]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 171]]]]]

def T7 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![5647, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![2153, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![1742, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![1285, 0, 0, 495], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1299], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![701, 0, 0, 544], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![509, 0, 0, 1291], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 1039], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 298], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 306], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1022], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![133, 0, 103, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 8, 4, 0]], ![![282, 0, 208, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 8, 6, 0]], ![![36, 0, 59, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![30, 0, 96, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 6, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 145, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 224, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 47, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 52, 0, 0]]],
      ![![![8, 0, 7, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 8, 10, 0]], ![![29, 0, 23, 8], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 9, 9, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 9, 17, 0]], ![![1, 0, 0, 8], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 8, 15, 0]]],
      ![![![9, 0, 2, 8], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 131, 0]], ![![8, 0, 7, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 224, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 154, 0]], ![![8, 0, 7, 8], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 291, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![309, 0, 125, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![101, 0, 126, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![108, 0, 299, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![258, 0, 248, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 9, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 9, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![9, 0, 9, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![7, 0, 9, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![9, 0, 11, 9]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![7, 0, 0, 14]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 63]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 59]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 158]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 269]]]]]

def T8 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![10878, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![3998, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![3192, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![2243, 0, 0, 824], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 2294], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![1143, 0, 0, 891], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![843, 0, 0, 2253], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 1867], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 515], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 524], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1864], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![180, 0, 142, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 9, 4, 0]], ![![424, 0, 319, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 9, 7, 0]], ![![45, 0, 75, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![38, 0, 134, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 7, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 207, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 341, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 61, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 67, 0, 0]]],
      ![![![9, 0, 8, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 9, 11, 0]], ![![37, 0, 30, 9], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 10, 10, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 10, 19, 0]], ![![1, 0, 0, 9], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 9, 17, 0]]],
      ![![![10, 0, 2, 9], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 178, 0]], ![![9, 0, 8, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 341, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 208, 0]], ![![9, 0, 8, 9], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 438, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![462, 0, 171, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![140, 0, 172, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![148, 0, 447, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![387, 0, 372, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 10, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 10, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![10, 0, 10, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![8, 0, 10, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![10, 0, 12, 10]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![8, 0, 0, 16]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 79]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 74]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 222]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 405]]]]]

def T9 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![19971, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![7100, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![5631, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![3732, 0, 0, 1308], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 3843], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![1781, 0, 0, 1396], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![1333, 0, 0, 3747], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 3180], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 846], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 856], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 3207], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![237, 0, 190, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 10, 4, 0]], ![![614, 0, 470, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 10, 8, 0]], ![![55, 0, 93, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![47, 0, 181, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 8, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 285, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 499, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 77, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 84, 0, 0]]],
      ![![![10, 0, 9, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 10, 12, 0]], ![![46, 0, 38, 10], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 11, 11, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 11, 21, 0]], ![![1, 0, 0, 10], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 10, 19, 0]]],
      ![![![11, 0, 2, 10], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 235, 0]], ![![10, 0, 9, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 499, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 273, 0]], ![![10, 0, 9, 10], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 634, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![665, 0, 227, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![188, 0, 228, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![197, 0, 644, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![559, 0, 538, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 11, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 11, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![11, 0, 11, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![9, 0, 11, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![11, 0, 13, 11]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![9, 0, 0, 18]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 97]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 91]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 302]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 588]]]]]

def T10 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![35180, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![12119, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![9591, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![5967, 0, 0, 1997], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 6168], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2674, 0, 0, 2109], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2029, 0, 0, 5988], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 5183], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1332], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1343], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 5262], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![305, 0, 248, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 11, 4, 0]], ![![862, 0, 670, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 11, 9, 0]], ![![66, 0, 113, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![57, 0, 238, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 9, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 381, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 707, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 95, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 103, 0, 0]]],
      ![![![11, 0, 10, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 11, 13, 0]], ![![56, 0, 47, 11], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 12, 12, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 12, 23, 0]], ![![1, 0, 0, 11], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 11, 21, 0]]],
      ![![![12, 0, 2, 11], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 303, 0]], ![![11, 0, 10, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 707, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 350, 0]], ![![11, 0, 10, 11], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 889, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![928, 0, 294, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![246, 0, 295, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![256, 0, 900, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![783, 0, 755, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 12, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 12, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![12, 0, 12, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![10, 0, 12, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![12, 0, 14, 12]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![10, 0, 0, 20]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 117]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 110]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 400]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 828]]]]]

def T11 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![59780, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![19972, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![15818, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![9224, 0, 0, 2951], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 9553], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![3892, 0, 0, 3090], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2991, 0, 0, 9252], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 8141], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 2023], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 2035], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 8301], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![385, 0, 317, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 12, 4, 0]], ![![1179, 0, 929, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 12, 10, 0]], ![![78, 0, 135, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![68, 0, 306, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 10, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 497, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 975, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 115, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 124, 0, 0]]],
      ![![![12, 0, 11, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 12, 14, 0]], ![![67, 0, 57, 12], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 13, 13, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 13, 25, 0]], ![![1, 0, 0, 12], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 12, 23, 0]]],
      ![![![13, 0, 2, 12], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 383, 0]], ![![12, 0, 11, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 975, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 440, 0]], ![![12, 0, 11, 12], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1214, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1262, 0, 373, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![315, 0, 374, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![326, 0, 1226, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1069, 0, 1033, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 13, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 13, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![13, 0, 13, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![11, 0, 13, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![13, 0, 15, 13]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![11, 0, 0, 22]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 139]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 131]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 518]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1136]]]]]

def T12 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![98414, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![31903, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![25333, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![13851, 0, 0, 4241], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 14355], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![5517, 0, 0, 4410], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![4290, 0, 0, 13887], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 12390], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 2979], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 2992], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 12668], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![478, 0, 398, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 13, 4, 0]], ![![1577, 0, 1258, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 13, 11, 0]], ![![91, 0, 159, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![80, 0, 386, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 11, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 635, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1314, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 137, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 147, 0, 0]]],
      ![![![13, 0, 12, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 13, 15, 0]], ![![79, 0, 68, 13], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 14, 14, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 14, 27, 0]], ![![1, 0, 0, 13], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 13, 25, 0]]],
      ![![![14, 0, 2, 13], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 476, 0]], ![![13, 0, 12, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1314, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 544, 0]], ![![13, 0, 12, 13], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1621, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1679, 0, 465, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![396, 0, 466, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![408, 0, 1634, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1428, 0, 1383, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 14, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 14, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![14, 0, 14, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![12, 0, 14, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![14, 0, 16, 14]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![12, 0, 0, 24]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 163]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 154]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 658]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1524]]]]]

def T13 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![157524, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![49565, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![39504, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![20280, 0, 0, 5950], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 21016], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![7644, 0, 0, 6152], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![6009, 0, 0, 20325], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 18349], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 4271], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 4285], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 18791], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![585, 0, 492, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 14, 4, 0]], ![![2069, 0, 1669, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 14, 12, 0]], ![![105, 0, 185, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![93, 0, 479, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 12, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 797, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1736, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 161, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 172, 0, 0]]],
      ![![![14, 0, 13, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 14, 16, 0]], ![![92, 0, 80, 14], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 15, 15, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 15, 29, 0]], ![![1, 0, 0, 14], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 14, 27, 0]]],
      ![![![15, 0, 2, 14], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 583, 0]], ![![14, 0, 13, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1736, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 663, 0]], ![![14, 0, 13, 14], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2123, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2192, 0, 571, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![490, 0, 572, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![503, 0, 2137, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1872, 0, 1817, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 15, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 15, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![15, 0, 15, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![13, 0, 15, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![15, 0, 17, 15]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![13, 0, 0, 26]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 189]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 179]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 822]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2005]]]]]

def T14 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![245879, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![75115, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![60130, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![29040, 0, 0, 8174], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 30076], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![10382, 0, 0, 8412], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![8244, 0, 0, 29095], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 26533], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 5982], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 5997], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 27195], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![707, 0, 600, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 15, 4, 0]], ![![2669, 0, 2175, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 15, 13, 0]], ![![120, 0, 213, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![107, 0, 586, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 13, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 985, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2254, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 187, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 199, 0, 0]]],
      ![![![15, 0, 14, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 15, 17, 0]], ![![106, 0, 93, 15], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 16, 16, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 16, 31, 0]], ![![1, 0, 0, 15], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 15, 29, 0]]],
      ![![![16, 0, 2, 15], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 705, 0]], ![![15, 0, 14, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2254, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 798, 0]], ![![15, 0, 14, 15], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2734, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2815, 0, 692, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![598, 0, 693, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![612, 0, 2749, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2414, 0, 2348, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 16, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 16, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![16, 0, 16, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![14, 0, 16, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![16, 0, 18, 16]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![14, 0, 0, 28]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 217]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 206]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1012]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2593]]]]]

def T15 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![375214, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], u, ![![111323, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![89538, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![u, u, u, u],
      ![![![40771, 0, 0, 11023], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 42187], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![13855, 0, 0, 11300], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![11105, 0, 0, 40837], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 37567], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 8208], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 8224], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 38516], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u],
      ![u, u, u, u]],
    ![![![![845, 0, 723, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 16, 4, 0]], ![![3392, 0, 2790, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 16, 14, 0]], ![![136, 0, 243, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 4, 0]], ![![122, 0, 708, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2, 14, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1201, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 2882, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 215, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 228, 0, 0]]],
      ![![![16, 0, 15, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 16, 18, 0]], ![![121, 0, 107, 16], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 17, 17, 0]], ![![1, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 17, 33, 0]], ![![1, 0, 0, 16], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 16, 31, 0]]],
      ![![![17, 0, 2, 16], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 843, 0]], ![![16, 0, 15, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 2882, 0]], ![![2, 0, 2, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 950, 0]], ![![16, 0, 15, 16], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 3469, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![3563, 0, 829, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![721, 0, 830, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![736, 0, 3485, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![3068, 0, 2990, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 4, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 17, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 17, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![17, 0, 17, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![15, 0, 17, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![17, 0, 19, 17]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![15, 0, 0, 30]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 247]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 235]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1230]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 3303]]]]]

set_option maxHeartbeats 4000000 in
/-- Every kernel computation, in one pass over the reachable states: the allowed slices lead to
reachable states, the tables are W(1), ..., W(15), and the base relation holds. -/
lemma check_all : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2
      (fun v => (fun B E => if reach (B 0) (B 1) (B 2) (E 1) (E 2) = true then 0 else 1) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = 0) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun _ _ => 1) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T1 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T1 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T2 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T2 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T3 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T3 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T4 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T4 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T5 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T5 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T6 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T6 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T7 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T7 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T8 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T8 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T9 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T9 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T10 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T10 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T11 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T11 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T12 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T12 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T13 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T13 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T14 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T14 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T15 a0 a1 a2 d1 d2) ∧
    (nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T15 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) + 9 * T8 a0 a1 a2 d1 d2 + 84 * T10 a0 a1 a2 d1 d2 + 126 * T12 a0 a1 a2 d1 d2 + 36 * T14 a0 a1 a2 d1 d2 = T7 a0 a1 a2 d1 d2 + 36 * T9 a0 a1 a2 d1 d2 + 126 * T11 a0 a1 a2 d1 d2 + 84 * T13 a0 a1 a2 d1 d2 + 9 * T15 a0 a1 a2 d1 d2) := by
  decide +kernel

lemma vec_eta (A : Fin 3 → Fin 4) : A = ![A 0, A 1, A 2] := by
  ext s
  fin_cases s <;> rfl

lemma vec_etaD (D : Fin 3 → Fin 4) (h : D 0 = 0) : D = ![0, D 1, D 2] := by
  funext s
  fin_cases s
  · exact h
  · rfl
  · rfl

/-- Reachable states. -/
def R (A D : Fin 3 → Fin 4) : Prop := D 0 = 0 ∧ reach (A 0) (A 1) (A 2) (D 1) (D 2) = true

lemma R_nxt (A D v : Fin 3 → Fin 4) (hA : R A D) (hv : colOKo A D 2 v) : R (nxt A v) (nxtD D v) := by
  have h := (check_all (A 0) (A 1) (A 2) (D 1) (D 2) hA.2).1
  rw [← ssum_nest, ← vec_eta A, ← vec_etaD D hA.1] at h
  have e := (Finset.sum_eq_zero_iff.mp h) v (Finset.mem_univ v)
  rw [if_pos hv] at e
  try dsimp only at e
  unfold R
  refine ⟨rfl, ?_⟩
  by_contra hc
  rw [if_neg hc] at e
  exact one_ne_zero e

lemma W_succ_R (m : ℕ) (A D : Fin 3 → Fin 4) (F : (Fin 3 → Fin 4) → (Fin 3 → Fin 4) → ℕ)
    (hF : ∀ B E, R B E → W m B E = F B E) (hA : R A D) :
    W (m + 1) A D = nest 3 A D 2 (fun v => F (nxt A v) (nxtD D v)) := by
  rw [W_succ, ← ssum_nest]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · exact hF _ _ (R_nxt A D v hA hv)
  · rfl

lemma W1 (A D : Fin 3 → Fin 4) (hA : R A D) : W 1 A D = T1 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 0 A D (fun _ _ => 1) (fun B E _ => W_zero B E) hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.1

lemma W2 (A D : Fin 3 → Fin 4) (hA : R A D) : W 2 A D = T2 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 1 A D (fun B E => T1 (B 0) (B 1) (B 2) (E 1) (E 2)) W1 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.1

lemma W3 (A D : Fin 3 → Fin 4) (hA : R A D) : W 3 A D = T3 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 2 A D (fun B E => T2 (B 0) (B 1) (B 2) (E 1) (E 2)) W2 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.1

lemma W4 (A D : Fin 3 → Fin 4) (hA : R A D) : W 4 A D = T4 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 3 A D (fun B E => T3 (B 0) (B 1) (B 2) (E 1) (E 2)) W3 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.1

lemma W5 (A D : Fin 3 → Fin 4) (hA : R A D) : W 5 A D = T5 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 4 A D (fun B E => T4 (B 0) (B 1) (B 2) (E 1) (E 2)) W4 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.1

lemma W6 (A D : Fin 3 → Fin 4) (hA : R A D) : W 6 A D = T6 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 5 A D (fun B E => T5 (B 0) (B 1) (B 2) (E 1) (E 2)) W5 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.1

lemma W7 (A D : Fin 3 → Fin 4) (hA : R A D) : W 7 A D = T7 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 6 A D (fun B E => T6 (B 0) (B 1) (B 2) (E 1) (E 2)) W6 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.2.1

lemma W8 (A D : Fin 3 → Fin 4) (hA : R A D) : W 8 A D = T8 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 7 A D (fun B E => T7 (B 0) (B 1) (B 2) (E 1) (E 2)) W7 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.2.2.1

lemma W9 (A D : Fin 3 → Fin 4) (hA : R A D) : W 9 A D = T9 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 8 A D (fun B E => T8 (B 0) (B 1) (B 2) (E 1) (E 2)) W8 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.2.2.2.1

lemma W10 (A D : Fin 3 → Fin 4) (hA : R A D) : W 10 A D = T10 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 9 A D (fun B E => T9 (B 0) (B 1) (B 2) (E 1) (E 2)) W9 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.2.2.2.2.1

lemma W11 (A D : Fin 3 → Fin 4) (hA : R A D) : W 11 A D = T11 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 10 A D (fun B E => T10 (B 0) (B 1) (B 2) (E 1) (E 2)) W10 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.2.2.2.2.2.1

lemma W12 (A D : Fin 3 → Fin 4) (hA : R A D) : W 12 A D = T12 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 11 A D (fun B E => T11 (B 0) (B 1) (B 2) (E 1) (E 2)) W11 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.2.2.2.2.2.2.1

lemma W13 (A D : Fin 3 → Fin 4) (hA : R A D) : W 13 A D = T13 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 12 A D (fun B E => T12 (B 0) (B 1) (B 2) (E 1) (E 2)) W12 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma W14 (A D : Fin 3 → Fin 4) (hA : R A D) : W 14 A D = T14 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 13 A D (fun B E => T13 (B 0) (B 1) (B 2) (E 1) (E 2)) W13 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma W15 (A D : Fin 3 → Fin 4) (hA : R A D) : W 15 A D = T15 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 14 A D (fun B E => T14 (B 0) (B 1) (B 2) (E 1) (E 2)) W14 hA, vec_eta A, vec_etaD D hA.1]
  exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma W_rec (n : ℕ) (A D : Fin 3 → Fin 4) (hA : R A D) :
    W (n + 16) A D + 9 * W (n + 8) A D + 84 * W (n + 10) A D + 126 * W (n + 12) A D + 36 * W (n + 14) A D = W (n + 7) A D + 36 * W (n + 9) A D + 126 * W (n + 11) A D + 84 * W (n + 13) A D + 9 * W (n + 15) A D := by
  induction n generalizing A D with
  | zero =>
    rw [show (0 : ℕ) + 16 = 15 + 1 from rfl, W_succ_R 15 A D (fun B E => T15 (B 0) (B 1) (B 2) (E 1) (E 2)) W15 hA, show (0 : ℕ) + 8 = 8 from rfl, W8 A D hA, show (0 : ℕ) + 10 = 10 from rfl, W10 A D hA, show (0 : ℕ) + 12 = 12 from rfl, W12 A D hA, show (0 : ℕ) + 14 = 14 from rfl, W14 A D hA, show (0 : ℕ) + 7 = 7 from rfl, W7 A D hA, show (0 : ℕ) + 9 = 9 from rfl, W9 A D hA, show (0 : ℕ) + 11 = 11 from rfl, W11 A D hA, show (0 : ℕ) + 13 = 13 from rfl, W13 A D hA, show (0 : ℕ) + 15 = 15 from rfl, W15 A D hA, vec_eta A, vec_etaD D hA.1]
    exact (check_all _ _ _ _ _ hA.2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | succ n ih =>
    rw [W_succ (n + 16), W_succ (n + 8), W_succ (n + 10), W_succ (n + 12), W_succ (n + 14), W_succ (n + 7), W_succ (n + 9), W_succ (n + 11), W_succ (n + 13), W_succ (n + 15)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : colOKo A D 2 v
    · simp only [if_pos hv]
      exact ih _ _ (R_nxt A D v hA hv)
    · simp [hv]

lemma R_zero : R 0 0 := by
  unfold R
  decide +kernel

lemma a_rec (n : ℕ) : a (n + 16) + 9 * a (n + 8) + 84 * a (n + 10) + 126 * a (n + 12) + 36 * a (n + 14) = a (n + 7) + 36 * a (n + 9) + 126 * a (n + 11) + 84 * a (n + 13) + 9 * a (n + 15) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  exact W_rec n 0 0 R_zero

lemma a_zero : a 0 = 1 := by rw [a_eq, W_zero]
lemma a_1 : a 1 = 12 := by rw [a_eq, W1 0 0 R_zero]; rfl
lemma a_2 : a 2 = 61 := by rw [a_eq, W2 0 0 R_zero]; rfl
lemma a_3 : a 3 = 190 := by rw [a_eq, W3 0 0 R_zero]; rfl
lemma a_4 : a 4 = 526 := by rw [a_eq, W4 0 0 R_zero]; rfl
lemma a_5 : a 5 = 1262 := by rw [a_eq, W5 0 0 R_zero]; rfl
lemma a_6 : a 6 = 2766 := by rw [a_eq, W6 0 0 R_zero]; rfl
lemma a_7 : a 7 = 5647 := by rw [a_eq, W7 0 0 R_zero]; rfl
lemma a_8 : a 8 = 10878 := by rw [a_eq, W8 0 0 R_zero]; rfl
lemma a_9 : a 9 = 19971 := by rw [a_eq, W9 0 0 R_zero]; rfl
lemma a_10 : a 10 = 35180 := by rw [a_eq, W10 0 0 R_zero]; rfl
lemma a_11 : a 11 = 59780 := by rw [a_eq, W11 0 0 R_zero]; rfl
lemma a_12 : a 12 = 98414 := by rw [a_eq, W12 0 0 R_zero]; rfl
lemma a_13 : a 13 = 157524 := by rw [a_eq, W13 0 0 R_zero]; rfl
lemma a_14 : a 14 = 245879 := by rw [a_eq, W14 0 0 R_zero]; rfl
lemma a_15 : a 15 = 375214 := by rw [a_eq, W15 0 0 R_zero]; rfl

lemma a_rec_z (n : ℕ) : (a (n + 16) : ℤ) + 9 * (a (n + 8) : ℤ) + 84 * (a (n + 10) : ℤ) + 126 * (a (n + 12) : ℤ) + 36 * (a (n + 14) : ℤ) = (a (n + 7) : ℤ) + 36 * (a (n + 9) : ℤ) + 126 * (a (n + 11) : ℤ) + 84 * (a (n + 13) : ℤ) + 9 * (a (n + 15) : ℤ) := by
  exact_mod_cast a_rec n

/-- The recurrence of the entry, for n > 15. -/
theorem recur : ∀ n : ℕ, 15 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 16 := ⟨n - 16, by omega⟩
  have h := a_rec_z j
  simp only [show j + 16 - 1 = j + 15 by omega, show j + 16 - 2 = j + 14 by omega, show j + 16 - 3 = j + 13 by omega, show j + 16 - 4 = j + 12 by omega, show j + 16 - 5 = j + 11 by omega, show j + 16 - 6 = j + 10 by omega, show j + 16 - 7 = j + 9 by omega, show j + 16 - 8 = j + 8 by omega, show j + 16 - 9 = j + 7 by omega]
  linear_combination h

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 9 = X * (12 - 47 * X + 73 * X ^ 2 + 4 * X ^ 3 - 244 * X ^ 4 + 558 * X ^ 5 - 737 * X ^ 6 + 651 * X ^ 7 - 375 * X ^ 8 + 86 * X ^ 9 + 91 * X ^ 10 - 128 * X ^ 11 + 80 * X ^ 12 - 27 * X ^ 13 + 4 * X ^ 14) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 9 = A - A * X ^ 1 * C 9 + A * X ^ 2 * C 36 - A * X ^ 3 * C 84 + A * X ^ 4 * C 126 - A * X ^ 5 * C 126 + A * X ^ 6 * C 84 - A * X ^ 7 * C 36 + A * X ^ 8 * C 9 - A * X ^ 9 := by
    rw [show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9, show (C (36 : ℚ) : ℚ⟦X⟧) = 36 from map_ofNat C 36, show (C (84 : ℚ) : ℚ⟦X⟧) = 84 from map_ofNat C 84, show (C (126 : ℚ) : ℚ⟦X⟧) = 126 from map_ofNat C 126]
    ring
  have e2 : (X * (12 - 47 * X + 73 * X ^ 2 + 4 * X ^ 3 - 244 * X ^ 4 + 558 * X ^ 5 - 737 * X ^ 6 + 651 * X ^ 7 - 375 * X ^ 8 + 86 * X ^ 9 + 91 * X ^ 10 - 128 * X ^ 11 + 80 * X ^ 12 - 27 * X ^ 13 + 4 * X ^ 14) : ℚ⟦X⟧) = X ^ 1 * C 12 - X ^ 2 * C 47 + X ^ 3 * C 73 + X ^ 4 * C 4 - X ^ 5 * C 244 + X ^ 6 * C 558 - X ^ 7 * C 737 + X ^ 8 * C 651 - X ^ 9 * C 375 + X ^ 10 * C 86 + X ^ 11 * C 91 - X ^ 12 * C 128 + X ^ 13 * C 80 - X ^ 14 * C 27 + X ^ 15 * C 4 := by
    rw [show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (12 : ℚ) : ℚ⟦X⟧) = 12 from map_ofNat C 12, show (C (27 : ℚ) : ℚ⟦X⟧) = 27 from map_ofNat C 27, show (C (47 : ℚ) : ℚ⟦X⟧) = 47 from map_ofNat C 47, show (C (73 : ℚ) : ℚ⟦X⟧) = 73 from map_ofNat C 73, show (C (80 : ℚ) : ℚ⟦X⟧) = 80 from map_ofNat C 80, show (C (86 : ℚ) : ℚ⟦X⟧) = 86 from map_ofNat C 86, show (C (91 : ℚ) : ℚ⟦X⟧) = 91 from map_ofNat C 91, show (C (128 : ℚ) : ℚ⟦X⟧) = 128 from map_ofNat C 128, show (C (244 : ℚ) : ℚ⟦X⟧) = 244 from map_ofNat C 244, show (C (375 : ℚ) : ℚ⟦X⟧) = 375 from map_ofNat C 375, show (C (558 : ℚ) : ℚ⟦X⟧) = 558 from map_ofNat C 558, show (C (651 : ℚ) : ℚ⟦X⟧) = 651 from map_ofNat C 651, show (C (737 : ℚ) : ℚ⟦X⟧) = 737 from map_ofNat C 737]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
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
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12, a_13, a_14] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12, a_13, a_14, a_15] <;> norm_num
  · have hz := a_rec_z (n + 0)
    have hq : (a (n + 0 + 16) : ℚ) + 9 * (a (n + 0 + 8) : ℚ) + 84 * (a (n + 0 + 10) : ℚ) + 126 * (a (n + 0 + 12) : ℚ) + 36 * (a (n + 0 + 14) : ℚ) = (a (n + 0 + 7) : ℚ) + 36 * (a (n + 0 + 9) : ℚ) + 126 * (a (n + 0 + 11) : ℚ) + 84 * (a (n + 0 + 13) : ℚ) + 9 * (a (n + 0 + 15) : ℚ) := by
      exact_mod_cast hz
    simp only [show n + 0 + 16 = n + 16 by omega, show n + 0 + 8 = n + 8 by omega, show n + 0 + 10 = n + 10 by omega, show n + 0 + 12 = n + 12 by omega, show n + 0 + 14 = n + 14 by omega, show n + 0 + 7 = n + 7 by omega, show n + 0 + 9 = n + 9 by omega, show n + 0 + 11 = n + 11 by omega, show n + 0 + 13 = n + 13 by omega, show n + 0 + 15 = n + 15 by omega] at hq
    simp only [if_false, if_true, show ¬ (n + 16 = 0) by omega,
      show 1 ≤ n + 16 by omega,
      show ¬ (n + 16 - 1 = 0) by omega,
      show n + 16 - 1 = n + 15 by omega,
      show ¬ (n + 15 = 0) by omega,
      show 2 ≤ n + 16 by omega,
      show ¬ (n + 16 - 2 = 0) by omega,
      show n + 16 - 2 = n + 14 by omega,
      show ¬ (n + 14 = 0) by omega,
      show 3 ≤ n + 16 by omega,
      show ¬ (n + 16 - 3 = 0) by omega,
      show n + 16 - 3 = n + 13 by omega,
      show ¬ (n + 13 = 0) by omega,
      show 4 ≤ n + 16 by omega,
      show ¬ (n + 16 - 4 = 0) by omega,
      show n + 16 - 4 = n + 12 by omega,
      show ¬ (n + 12 = 0) by omega,
      show 5 ≤ n + 16 by omega,
      show ¬ (n + 16 - 5 = 0) by omega,
      show n + 16 - 5 = n + 11 by omega,
      show ¬ (n + 11 = 0) by omega,
      show 6 ≤ n + 16 by omega,
      show ¬ (n + 16 - 6 = 0) by omega,
      show n + 16 - 6 = n + 10 by omega,
      show ¬ (n + 10 = 0) by omega,
      show 7 ≤ n + 16 by omega,
      show ¬ (n + 16 - 7 = 0) by omega,
      show n + 16 - 7 = n + 9 by omega,
      show ¬ (n + 9 = 0) by omega,
      show 8 ≤ n + 16 by omega,
      show ¬ (n + 16 - 8 = 0) by omega,
      show n + 16 - 8 = n + 8 by omega,
      show ¬ (n + 8 = 0) by omega,
      show 9 ≤ n + 16 by omega,
      show ¬ (n + 16 - 9 = 0) by omega,
      show n + 16 - 9 = n + 7 by omega,
      show ¬ (n + 7 = 0) by omega,
      show ¬ (n + 16 = 1) by omega,
      show ¬ (n + 16 = 2) by omega,
      show ¬ (n + 16 = 3) by omega,
      show ¬ (n + 16 = 4) by omega,
      show ¬ (n + 16 = 5) by omega,
      show ¬ (n + 16 = 6) by omega,
      show ¬ (n + 16 = 7) by omega,
      show ¬ (n + 16 = 8) by omega,
      show ¬ (n + 16 = 9) by omega,
      show ¬ (n + 16 = 10) by omega,
      show ¬ (n + 16 = 11) by omega,
      show ¬ (n + 16 = 12) by omega,
      show ¬ (n + 16 = 13) by omega,
      show ¬ (n + 16 = 14) by omega,
      show ¬ (n + 16 = 15) by omega]
    linear_combination hq

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 9 = X * (12 - 47 * X + 73 * X ^ 2 + 4 * X ^ 3 - 244 * X ^ 4 + 558 * X ^ 5 - 737 * X ^ 6 + 651 * X ^ 7 - 375 * X ^ 8 + 86 * X ^ 9 + 91 * X ^ 10 - 128 * X ^ 11 + 80 * X ^ 12 - 27 * X ^ 13 + 4 * X ^ 14) ∧
    ∀ n : ℕ, 15 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a240002

theorem OMA.solution : type_of% @OMA.S_oeis_a240002.main :=
  OMA.S_oeis_a240002.conjecture
