import OMAStatements.S_oeis_a239987

namespace OMA.S_oeis_a239987

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
  ∀ s : Fin j, (v s).val ≠ ((A s).val) % 4 ∧ (v s).val ≠ (off + ∑ s' ∈ Iio s, (v s').val) % 4 ∧
    (v s).val ≠ (1 + (D s).val) % 4

instance {j : ℕ} (A D : Fin j → Fin 4) (off : ℕ) : DecidablePred (colOKo A D off) := fun v => by
  unfold colOKo; infer_instance

lemma sum_cons {j : ℕ} (G : (Fin (j + 1) → Fin 4) → ℕ) :
    ∑ v, G v = ∑ x : Fin 4, ∑ w : Fin j → Fin 4, G (Fin.cons x w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 4) _ _ (fun p => rfl)).symm

lemma colOKo_cons {j : ℕ} (A D : Fin (j + 1) → Fin 4) (off : ℕ) (x : Fin 4) (w : Fin j → Fin 4) :
    colOKo A D off (Fin.cons x w : Fin (j + 1) → Fin 4) ↔
      (x.val ≠ ((A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (1 + (D 0).val) % 4) ∧
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
      if x.val ≠ ((A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (1 + (D 0).val) % 4 then
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
    by_cases hc : x.val ≠ ((A 0).val) % 4 ∧ x.val ≠ off % 4 ∧ x.val ≠ (1 + (D 0).val) % 4
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
    (g t s).val ≠ (((A s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 4 ∧
    (g t s).val ≠ (2 + ∑ s' ∈ Iio s, (g t s').val) % 4 ∧
    (g t s).val ≠ (1 + dg D g t s) % 4

instance (A D : Fin 3 → Fin 4) {m : ℕ} : DecidablePred (@V A D m) := fun g => by
  unfold V; infer_instance

lemma V_cons (A D : Fin 3 → Fin 4) {m : ℕ} (v : Fin 3 → Fin 4) (g : Fin m → Fin 3 → Fin 4) :
    V A D (Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 4) ↔ colOKo A D 2 v ∧ V (nxt A v) (nxtD D v) g := by
  have key : ∀ (t : Fin m) (s : Fin 3),
      (((A s).val + ∑ t' ∈ Iio t.succ, ((Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 4) t' s).val)) % 4 =
      (((nxt A v s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 4 := by
    intro t s
    rw [sum_Iio_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, nxt, Fin.val_add]
    omega
  have key0 : ∀ s : Fin 3,
      (((A s).val + ∑ t' ∈ Iio (0 : Fin (m + 1)), ((Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 4) t' s).val)) % 4 =
      ((A s).val) % 4 := by
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
  ![![![![![true, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]]],
    ![![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]]],
    ![![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]]],
    ![![![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![true, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, true, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, true, false]], ![![false, false, false, false], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]],
      ![![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]], ![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, true]], ![![true, false, false, true], ![false, false, false, false], ![false, false, false, false], ![false, false, false, true]]]]]

def T1 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![3, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![2, 0, 0, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![3, 0, 0, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![3, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![5, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![4, 0, 3, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![3, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 3, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![1, 0, 0, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]], ![![1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]]]]]

def T2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![6, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![3, 0, 0, 3], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![4, 0, 0, 3], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![5, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![13, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![12, 0, 8, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![6, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 6, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![1, 0, 0, 3], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![3, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![4, 0, 0, 3], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 5]]]]]

def T3 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![13, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![4, 0, 0, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![5, 0, 0, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![8, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![25, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![29, 0, 19, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![10, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 13, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![1, 0, 0, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![4, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![7, 0, 0, 4], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 7]]]]]

def T4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![22, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![5, 0, 0, 5], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![6, 0, 0, 5], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![12, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![42, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![59, 0, 40, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![15, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 27, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![1, 0, 0, 5], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![5, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![11, 0, 0, 5], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 9]]]]]

def T5 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![38, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![6, 0, 0, 6], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![7, 0, 0, 6], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![17, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![65, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![107, 0, 75, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![21, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 52, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![1, 0, 0, 6], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![6, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![16, 0, 0, 6], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 11]]]]]

def T6 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![65, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![7, 0, 0, 7], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![8, 0, 0, 7], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![23, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![95, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![179, 0, 129, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![28, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 92, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![1, 0, 0, 7], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![7, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![22, 0, 0, 7], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 13]]]]]

def T7 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![107, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![8, 0, 0, 8], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![9, 0, 0, 8], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![30, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![133, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![282, 0, 208, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![36, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 152, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![1, 0, 0, 8], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![8, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![29, 0, 0, 8], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 15]]]]]

def T8 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![![169, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]],
    ![![![![9, 0, 0, 9], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![10, 0, 0, 9], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![38, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![180, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![424, 0, 319, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![45, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 238, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
      ![![![1, 0, 0, 9], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![9, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![37, 0, 0, 9], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 17]]]]]

set_option maxHeartbeats 4000000 in
lemma closure : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    nest 3 ![a0, a1, a2] ![0, d1, d2] 2
      (fun v => (fun B E => if reach (B 0) (B 1) (B 2) (E 1) (E 2) = true then 0 else 1) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check1 : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun _ _ => 1) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T1 a0 a1 a2 d1 d2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check2 : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T1 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T2 a0 a1 a2 d1 d2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check3 : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T2 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T3 a0 a1 a2 d1 d2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check4 : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T3 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T4 a0 a1 a2 d1 d2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check5 : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T4 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T5 a0 a1 a2 d1 d2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check6 : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T5 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T6 a0 a1 a2 d1 d2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check7 : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T6 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T7 a0 a1 a2 d1 d2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check8 : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T7 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) = T8 a0 a1 a2 d1 d2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ a0 a1 a2 d1 d2 : Fin 4, reach a0 a1 a2 d1 d2 = true →
    nest 3 ![a0, a1, a2] ![0, d1, d2] 2 (fun v => (fun B E => T8 (B 0) (B 1) (B 2) (E 1) (E 2)) (nxt ![a0, a1, a2] v) (nxtD ![0, d1, d2] v)) + 5 * T5 a0 a1 a2 d1 d2 + 10 * T7 a0 a1 a2 d1 d2 = T4 a0 a1 a2 d1 d2 + 10 * T6 a0 a1 a2 d1 d2 + 5 * T8 a0 a1 a2 d1 d2 := by
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
  have h := closure (A 0) (A 1) (A 2) (D 1) (D 2) hA.2
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
  exact check1 _ _ _ _ _ hA.2

lemma W2 (A D : Fin 3 → Fin 4) (hA : R A D) : W 2 A D = T2 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 1 A D (fun B E => T1 (B 0) (B 1) (B 2) (E 1) (E 2)) W1 hA, vec_eta A, vec_etaD D hA.1]
  exact check2 _ _ _ _ _ hA.2

lemma W3 (A D : Fin 3 → Fin 4) (hA : R A D) : W 3 A D = T3 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 2 A D (fun B E => T2 (B 0) (B 1) (B 2) (E 1) (E 2)) W2 hA, vec_eta A, vec_etaD D hA.1]
  exact check3 _ _ _ _ _ hA.2

lemma W4 (A D : Fin 3 → Fin 4) (hA : R A D) : W 4 A D = T4 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 3 A D (fun B E => T3 (B 0) (B 1) (B 2) (E 1) (E 2)) W3 hA, vec_eta A, vec_etaD D hA.1]
  exact check4 _ _ _ _ _ hA.2

lemma W5 (A D : Fin 3 → Fin 4) (hA : R A D) : W 5 A D = T5 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 4 A D (fun B E => T4 (B 0) (B 1) (B 2) (E 1) (E 2)) W4 hA, vec_eta A, vec_etaD D hA.1]
  exact check5 _ _ _ _ _ hA.2

lemma W6 (A D : Fin 3 → Fin 4) (hA : R A D) : W 6 A D = T6 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 5 A D (fun B E => T5 (B 0) (B 1) (B 2) (E 1) (E 2)) W5 hA, vec_eta A, vec_etaD D hA.1]
  exact check6 _ _ _ _ _ hA.2

lemma W7 (A D : Fin 3 → Fin 4) (hA : R A D) : W 7 A D = T7 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 6 A D (fun B E => T6 (B 0) (B 1) (B 2) (E 1) (E 2)) W6 hA, vec_eta A, vec_etaD D hA.1]
  exact check7 _ _ _ _ _ hA.2

lemma W8 (A D : Fin 3 → Fin 4) (hA : R A D) : W 8 A D = T8 (A 0) (A 1) (A 2) (D 1) (D 2) := by
  rw [W_succ_R 7 A D (fun B E => T7 (B 0) (B 1) (B 2) (E 1) (E 2)) W7 hA, vec_eta A, vec_etaD D hA.1]
  exact check8 _ _ _ _ _ hA.2

lemma W_rec (n : ℕ) (A D : Fin 3 → Fin 4) (hA : R A D) :
    W (n + 9) A D + 5 * W (n + 5) A D + 10 * W (n + 7) A D = W (n + 4) A D + 10 * W (n + 6) A D + 5 * W (n + 8) A D := by
  induction n generalizing A D with
  | zero =>
    rw [show (0 : ℕ) + 9 = 8 + 1 from rfl, W_succ_R 8 A D (fun B E => T8 (B 0) (B 1) (B 2) (E 1) (E 2)) W8 hA, show (0 : ℕ) + 5 = 5 from rfl, W5 A D hA, show (0 : ℕ) + 7 = 7 from rfl, W7 A D hA, show (0 : ℕ) + 4 = 4 from rfl, W4 A D hA, show (0 : ℕ) + 6 = 6 from rfl, W6 A D hA, show (0 : ℕ) + 8 = 8 from rfl, W8 A D hA, vec_eta A, vec_etaD D hA.1]
    exact base_check _ _ _ _ _ hA.2
  | succ n ih =>
    rw [W_succ (n + 9), W_succ (n + 5), W_succ (n + 7), W_succ (n + 4), W_succ (n + 6), W_succ (n + 8)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : colOKo A D 2 v
    · simp only [if_pos hv]
      exact ih _ _ (R_nxt A D v hA hv)
    · simp [hv]

lemma R_zero : R 0 0 := by
  unfold R
  decide +kernel

lemma a_rec (n : ℕ) : a (n + 9) + 5 * a (n + 5) + 10 * a (n + 7) = a (n + 4) + 10 * a (n + 6) + 5 * a (n + 8) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  exact W_rec n 0 0 R_zero

lemma a_zero : a 0 = 1 := by rw [a_eq, W_zero]
lemma a_1 : a 1 = 3 := by rw [a_eq, W1 0 0 R_zero]; rfl
lemma a_2 : a 2 = 6 := by rw [a_eq, W2 0 0 R_zero]; rfl
lemma a_3 : a 3 = 13 := by rw [a_eq, W3 0 0 R_zero]; rfl
lemma a_4 : a 4 = 22 := by rw [a_eq, W4 0 0 R_zero]; rfl
lemma a_5 : a 5 = 38 := by rw [a_eq, W5 0 0 R_zero]; rfl
lemma a_6 : a 6 = 65 := by rw [a_eq, W6 0 0 R_zero]; rfl
lemma a_7 : a 7 = 107 := by rw [a_eq, W7 0 0 R_zero]; rfl
lemma a_8 : a 8 = 169 := by rw [a_eq, W8 0 0 R_zero]; rfl

lemma a_rec_z (n : ℕ) : (a (n + 9) : ℤ) + 5 * (a (n + 5) : ℤ) + 10 * (a (n + 7) : ℤ) = (a (n + 4) : ℤ) + 10 * (a (n + 6) : ℤ) + 5 * (a (n + 8) : ℤ) := by
  exact_mod_cast a_rec n

/-- The recurrence of the entry, for n > 8. -/
theorem recur : ∀ n : ℕ, 8 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 9 := ⟨n - 9, by omega⟩
  have h := a_rec_z j
  simp only [show j + 9 - 1 = j + 8 by omega, show j + 9 - 2 = j + 7 by omega, show j + 9 - 3 = j + 6 by omega, show j + 9 - 4 = j + 5 by omega, show j + 9 - 5 = j + 4 by omega]
  linear_combination h

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 5 = X * (3 - 9 * X + 13 * X ^ 2 - 13 * X ^ 3 + 13 * X ^ 4 - 8 * X ^ 5 + X ^ 6 + X ^ 7) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 5 = A - A * X ^ 1 * C 5 + A * X ^ 2 * C 10 - A * X ^ 3 * C 10 + A * X ^ 4 * C 5 - A * X ^ 5 := by
    rw [show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (10 : ℚ) : ℚ⟦X⟧) = 10 from map_ofNat C 10]
    ring
  have e2 : (X * (3 - 9 * X + 13 * X ^ 2 - 13 * X ^ 3 + 13 * X ^ 4 - 8 * X ^ 5 + X ^ 6 + X ^ 7) : ℚ⟦X⟧) = X ^ 1 * C 3 - X ^ 2 * C 9 + X ^ 3 * C 13 - X ^ 4 * C 13 + X ^ 5 * C 13 - X ^ 6 * C 8 + X ^ 7 + X ^ 8 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8, show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9, show (C (13 : ℚ) : ℚ⟦X⟧) = 13 from map_ofNat C 13]
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
    have hq : (a (n + 0 + 9) : ℚ) + 5 * (a (n + 0 + 5) : ℚ) + 10 * (a (n + 0 + 7) : ℚ) = (a (n + 0 + 4) : ℚ) + 10 * (a (n + 0 + 6) : ℚ) + 5 * (a (n + 0 + 8) : ℚ) := by
      exact_mod_cast hz
    simp only [show n + 0 + 9 = n + 9 by omega, show n + 0 + 5 = n + 5 by omega, show n + 0 + 7 = n + 7 by omega, show n + 0 + 4 = n + 4 by omega, show n + 0 + 6 = n + 6 by omega, show n + 0 + 8 = n + 8 by omega] at hq
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
      (1 - X) ^ 5 = X * (3 - 9 * X + 13 * X ^ 2 - 13 * X ^ 3 + 13 * X ^ 4 - 8 * X ^ 5 + X ^ 6 + X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a239987

theorem OMA.solution : type_of% @OMA.S_oeis_a239987.main :=
  OMA.S_oeis_a239987.conjecture
