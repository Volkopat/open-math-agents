import OMAStatements.S_oeis_a239032

namespace OMA.S_oeis_a239032

open PowerSeries Finset




lemma sum_Iio {m : ℕ} (j : Fin m) (h : Fin m → ℕ) :
    ∑ x ∈ Iio j, h x = ∑ x, if x < j then h x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

/-- The conditions on a slice v of any length when the running sums along the growing dimension
are A and the sums across start from off. -/
def colOKo {j : ℕ} (A : Fin j → Fin 3) (off : ℕ) (v : Fin j → Fin 3) : Prop :=
  ∀ s : Fin j, (v s).val ≠ (0 + (A s).val) % 3 ∧ (v s).val ≠ (off + ∑ s' ∈ Iio s, (v s').val) % 3

instance {j : ℕ} (A : Fin j → Fin 3) (off : ℕ) : DecidablePred (colOKo A off) := fun v => by
  unfold colOKo; infer_instance

/-- The running sums after the slice v. -/
def nxt {j : ℕ} (A v : Fin j → Fin 3) : Fin j → Fin 3 := fun s => A s + v s

lemma sum_cons {j : ℕ} (G : (Fin (j + 1) → Fin 3) → ℕ) :
    ∑ v, G v = ∑ x : Fin 3, ∑ w : Fin j → Fin 3, G (Fin.cons x w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3) _ _ (fun p => rfl)).symm

lemma colOKo_cons {j : ℕ} (A : Fin (j + 1) → Fin 3) (off : ℕ) (x : Fin 3) (w : Fin j → Fin 3) :
    colOKo A off (Fin.cons x w : Fin (j + 1) → Fin 3) ↔
      (x.val ≠ (0 + (A 0).val) % 3 ∧ x.val ≠ off % 3) ∧ colOKo (Fin.tail A) (off + x.val) w := by
  have key : ∀ s : Fin j, (off + ∑ s' ∈ Iio s.succ, ((Fin.cons x w : Fin (j + 1) → Fin 3) s').val) % 3 =
      (off + x.val + ∑ s' ∈ Iio s, (w s').val) % 3 := by
    intro s
    rw [sum_Iio, sum_Iio, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff]
    omega
  have key0 : (off + ∑ s' ∈ Iio (0 : Fin (j + 1)), ((Fin.cons x w : Fin (j + 1) → Fin 3) s').val) % 3 =
      off % 3 := by
    rw [sum_Iio]
    simp [Fin.not_lt_zero]
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

lemma nxt_cons {j : ℕ} (A : Fin (j + 1) → Fin 3) (x : Fin 3) (w : Fin j → Fin 3) :
    nxt A (Fin.cons x w : Fin (j + 1) → Fin 3) =
      (Fin.cons (A 0 + x) (nxt (Fin.tail A) w) : Fin (j + 1) → Fin 3) := by
  funext s
  induction s using Fin.cases with
  | zero => simp [nxt]
  | succ s => simp [nxt, Fin.tail]

/-- The allowed slices enumerated entry by entry: each entry runs over its allowed values. -/
def nest : (j : ℕ) → (Fin j → Fin 3) → ℕ → ((Fin j → Fin 3) → ℕ) → ℕ
  | 0, _, _, F => F Fin.elim0
  | j + 1, A, off, F => ∑ x : Fin 3,
      if x.val ≠ (0 + (A 0).val) % 3 ∧ x.val ≠ off % 3 then
        nest j (Fin.tail A) (off + x.val) (fun w => F (Fin.cons (A 0 + x) w : Fin (j + 1) → Fin 3))
      else 0

lemma ssum_nest : ∀ (j : ℕ) (A : Fin j → Fin 3) (off : ℕ) (F : (Fin j → Fin 3) → ℕ),
    (∑ v : Fin j → Fin 3, if colOKo A off v then F (nxt A v) else 0) = nest j A off F := by
  intro j
  induction j with
  | zero =>
    intro A off F
    rw [Fintype.sum_unique]
    simp only [nest]
    split_ifs with hc
    · congr 1
      funext s
      exact Fin.elim0 s
    · exact absurd (fun s => Fin.elim0 s) hc
  | succ j ih =>
    intro A off F
    rw [sum_cons]
    simp only [nest]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hc : x.val ≠ (0 + (A 0).val) % 3 ∧ x.val ≠ off % 3
    · rw [if_pos hc, ← ih (Fin.tail A) (off + x.val) (fun w => F (Fin.cons (A 0 + x) w))]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      simp only [colOKo_cons, nxt_cons, hc, true_and, ne_eq, not_false_eq_true]
    · rw [if_neg hc]
      refine Finset.sum_eq_zero (fun w _ => ?_)
      rw [if_neg]
      rw [colOKo_cons]
      exact fun h => hc h.1

/-- An array of slices is valid when started from the running sums A. -/
def V (A : Fin 5 → Fin 3) {m : ℕ} (g : Fin m → Fin 5 → Fin 3) : Prop :=
  ∀ t : Fin m, ∀ s : Fin 5,
    (g t s).val ≠ (((A s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 3 ∧
    (g t s).val ≠ (1 + ∑ s' ∈ Iio s, (g t s').val) % 3

instance (A : Fin 5 → Fin 3) {m : ℕ} : DecidablePred (@V A m) := fun g => by
  unfold V; infer_instance

lemma V_cons (A : Fin 5 → Fin 3) {m : ℕ} (v : Fin 5 → Fin 3) (g : Fin m → Fin 5 → Fin 3) :
    V A (Fin.cons v g : Fin (m + 1) → Fin 5 → Fin 3) ↔ colOKo A 1 v ∧ V (nxt A v) g := by
  have key : ∀ (t : Fin m) (s : Fin 5),
      (((A s).val + ∑ t' ∈ Iio t.succ, ((Fin.cons v g : Fin (m + 1) → Fin 5 → Fin 3) t' s).val)) % 3 =
      (((nxt A v s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 3 := by
    intro t s
    rw [sum_Iio, sum_Iio, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff, nxt,
      Fin.val_add]
    omega
  have key0 : ∀ s : Fin 5,
      (((A s).val + ∑ t' ∈ Iio (0 : Fin (m + 1)), ((Fin.cons v g : Fin (m + 1) → Fin 5 → Fin 3) t' s).val)) % 3 =
      ((A s).val) % 3 := by
    intro s
    rw [sum_Iio]
    simp [Fin.not_lt_zero]
  constructor
  · intro h
    refine ⟨fun s => ?_, fun t s => ?_⟩
    · have e := h 0 s
      rw [key0] at e
      simpa using e
    · have e := h t.succ s
      rw [key] at e
      simpa using e
  · rintro ⟨h0, h1⟩ t s
    induction t using Fin.cases with
    | zero =>
      rw [key0]
      simpa using h0 s
    | succ t =>
      rw [key]
      simpa using h1 t s

/-- W(m, A): the arrays of m slices valid from the running sums A. -/
def W (m : ℕ) (A : Fin 5 → Fin 3) : ℕ :=
  ((univ : Finset (Fin m → Fin 5 → Fin 3)).filter (V A)).card

lemma W_zero (A : Fin 5 → Fin 3) : W 0 A = 1 := by
  have e : (univ : Finset (Fin 0 → Fin 5 → Fin 3)).filter (V A) = univ :=
    Finset.filter_true_of_mem (fun g _ t => Fin.elim0 t)
  rw [W, e]
  simp

lemma W_succ (m : ℕ) (A : Fin 5 → Fin 3) :
    W (m + 1) A = ∑ v : Fin 5 → Fin 3, if colOKo A 1 v then W m (nxt A v) else 0 := by
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
      exact ⟨(V_cons A v g').2 ⟨hv, hg'⟩, by simp⟩
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

lemma a_eq (n : ℕ) : a n = W n 0 := by
  unfold a W
  refine Finset.card_bij' (fun f _ => fun t s => f s t) (fun g _ => fun i j => g j i) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_filter, mem_univ, true_and, good, V, Pi.zero_apply, Fin.val_zero,
      zero_add] at hf ⊢
    intro t s
    exact hf s t
  · intro g hg
    simp only [mem_filter, mem_univ, true_and, good, V, Pi.zero_apply, Fin.val_zero,
      zero_add] at hg ⊢
    intro i j
    exact hg j i
  · intro f _
    rfl
  · intro g _
    rfl

/-- The reachable running sums. -/
def reach : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Bool :=
  ![![![![![true, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]],
      ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]],
      ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]]],
    ![![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]],
      ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]],
      ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]]],
    ![![![![true, false, false], ![false, false, true], ![true, true, true]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]],
      ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![true, false, false], ![false, false, true], ![true, true, true]]],
      ![![![true, true, true], ![false, false, true], ![false, true, false]], ![![true, false, false], ![false, false, true], ![true, true, true]], ![![true, true, true], ![true, true, true], ![true, true, true]]]]]
abbrev u : Fin 3 → Fin 3 → ℕ := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]


def T1 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![4, 0, 0], ![0, 0, 0], ![0, 0, 0]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![4, 0, 0], ![0, 0, 4], ![4, 4, 4]], u, u],
      ![u, u, ![![4, 0, 0], ![0, 0, 4], ![2, 4, 2]]],
      ![![![2, 3, 3], ![0, 0, 2], ![0, 2, 0]], ![![4, 0, 0], ![0, 0, 4], ![2, 4, 2]], ![![2, 1, 1], ![3, 3, 2], ![1, 2, 1]]]]]

def T2 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![16, 0, 0], ![0, 0, 0], ![0, 0, 0]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![11, 0, 0], ![0, 0, 13], ![6, 10, 6]], u, u],
      ![u, u, ![![14, 0, 0], ![0, 0, 16], ![6, 14, 6]]],
      ![![![4, 8, 4], ![0, 0, 3], ![0, 3, 0]], ![![10, 0, 0], ![0, 0, 13], ![5, 11, 5]], ![![3, 1, 1], ![4, 8, 4], ![1, 3, 1]]]]]

def T3 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![54, 0, 0], ![0, 0, 0], ![0, 0, 0]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![28, 0, 0], ![0, 0, 31], ![10, 22, 10]], u, u],
      ![u, u, ![![36, 0, 0], ![0, 0, 54], ![12, 36, 12]]],
      ![![![7, 15, 6], ![0, 0, 4], ![0, 4, 0]], ![![22, 0, 0], ![0, 0, 31], ![9, 28, 9]], ![![4, 1, 1], ![6, 15, 7], ![1, 4, 1]]]]]

def T4 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![149, 0, 0], ![0, 0, 0], ![0, 0, 0]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![59, 0, 0], ![0, 0, 66], ![15, 45, 15]], u, u],
      ![u, u, ![![80, 0, 0], ![0, 0, 149], ![22, 80, 22]]],
      ![![![11, 25, 9], ![0, 0, 5], ![0, 5, 0]], ![![45, 0, 0], ![0, 0, 66], ![15, 59, 15]], ![![5, 1, 1], ![9, 25, 11], ![1, 5, 1]]]]]

def T5 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![354, 0, 0], ![0, 0, 0], ![0, 0, 0]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![110, 0, 0], ![0, 0, 131], ![22, 84, 22]], u, u],
      ![u, u, ![![162, 0, 0], ![0, 0, 354], ![37, 162, 37]]],
      ![![![16, 39, 13], ![0, 0, 6], ![0, 6, 0]], ![![84, 0, 0], ![0, 0, 131], ![24, 110, 24]], ![![6, 1, 1], ![13, 39, 16], ![1, 6, 1]]]]]

def T6 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![757, 0, 0], ![0, 0, 0], ![0, 0, 0]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![189, 0, 0], ![0, 0, 244], ![32, 146, 32]], u, u],
      ![u, u, ![![305, 0, 0], ![0, 0, 757], ![59, 305, 59]]],
      ![![![22, 58, 18], ![0, 0, 7], ![0, 7, 0]], ![![146, 0, 0], ![0, 0, 244], ![37, 189, 37]], ![![7, 1, 1], ![18, 58, 22], ![1, 7, 1]]]]]

def T7 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![1495, 0, 0], ![0, 0, 0], ![0, 0, 0]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![306, 0, 0], ![0, 0, 430], ![46, 240, 46]], u, u],
      ![u, u, ![![542, 0, 0], ![0, 0, 1495], ![91, 542, 91]]],
      ![![![29, 83, 24], ![0, 0, 8], ![0, 8, 0]], ![![240, 0, 0], ![0, 0, 430], ![55, 306, 55]], ![![8, 1, 1], ![24, 83, 29], ![1, 8, 1]]]]]

def T8 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![2773, 0, 0], ![0, 0, 0], ![0, 0, 0]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![473, 0, 0], ![0, 0, 723], ![65, 377, 65]], u, u],
      ![u, u, ![![919, 0, 0], ![0, 0, 2773], ![137, 919, 137]]],
      ![![![37, 115, 31], ![0, 0, 9], ![0, 9, 0]], ![![377, 0, 0], ![0, 0, 723], ![79, 473, 79]], ![![9, 1, 1], ![31, 115, 37], ![1, 9, 1]]]]]

set_option maxHeartbeats 4000000 in
lemma closure : ∀ a0 a1 a2 a3 a4 : Fin 3, reach a0 a1 a2 a3 a4 = true →
    nest 5 ![a0, a1, a2, a3, a4] 1 (fun B => if reach (B 0) (B 1) (B 2) (B 3) (B 4) = true then 0 else 1) = 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check1 : ∀ a0 a1 a2 a3 a4 : Fin 3, reach a0 a1 a2 a3 a4 = true →
    nest 5 ![a0, a1, a2, a3, a4] 1 (fun _ => 1) = T1 a0 a1 a2 a3 a4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check2 : ∀ a0 a1 a2 a3 a4 : Fin 3, reach a0 a1 a2 a3 a4 = true →
    nest 5 ![a0, a1, a2, a3, a4] 1 (fun B => T1 (B 0) (B 1) (B 2) (B 3) (B 4)) = T2 a0 a1 a2 a3 a4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check3 : ∀ a0 a1 a2 a3 a4 : Fin 3, reach a0 a1 a2 a3 a4 = true →
    nest 5 ![a0, a1, a2, a3, a4] 1 (fun B => T2 (B 0) (B 1) (B 2) (B 3) (B 4)) = T3 a0 a1 a2 a3 a4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check4 : ∀ a0 a1 a2 a3 a4 : Fin 3, reach a0 a1 a2 a3 a4 = true →
    nest 5 ![a0, a1, a2, a3, a4] 1 (fun B => T3 (B 0) (B 1) (B 2) (B 3) (B 4)) = T4 a0 a1 a2 a3 a4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check5 : ∀ a0 a1 a2 a3 a4 : Fin 3, reach a0 a1 a2 a3 a4 = true →
    nest 5 ![a0, a1, a2, a3, a4] 1 (fun B => T4 (B 0) (B 1) (B 2) (B 3) (B 4)) = T5 a0 a1 a2 a3 a4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check6 : ∀ a0 a1 a2 a3 a4 : Fin 3, reach a0 a1 a2 a3 a4 = true →
    nest 5 ![a0, a1, a2, a3, a4] 1 (fun B => T5 (B 0) (B 1) (B 2) (B 3) (B 4)) = T6 a0 a1 a2 a3 a4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check7 : ∀ a0 a1 a2 a3 a4 : Fin 3, reach a0 a1 a2 a3 a4 = true →
    nest 5 ![a0, a1, a2, a3, a4] 1 (fun B => T6 (B 0) (B 1) (B 2) (B 3) (B 4)) = T7 a0 a1 a2 a3 a4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check8 : ∀ a0 a1 a2 a3 a4 : Fin 3, reach a0 a1 a2 a3 a4 = true →
    nest 5 ![a0, a1, a2, a3, a4] 1 (fun B => T7 (B 0) (B 1) (B 2) (B 3) (B 4)) = T8 a0 a1 a2 a3 a4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ a0 a1 a2 a3 a4 : Fin 3, reach a0 a1 a2 a3 a4 = true →
    nest 5 ![a0, a1, a2, a3, a4] 1 (fun B => T8 (B 0) (B 1) (B 2) (B 3) (B 4)) + 7 * T3 a0 a1 a2 a3 a4 + 35 * T5 a0 a1 a2 a3 a4 + 21 * T7 a0 a1 a2 a3 a4 = T2 a0 a1 a2 a3 a4 + 21 * T4 a0 a1 a2 a3 a4 + 35 * T6 a0 a1 a2 a3 a4 + 7 * T8 a0 a1 a2 a3 a4 := by
  decide +kernel

lemma vec_eta (A : Fin 5 → Fin 3) : A = ![A 0, A 1, A 2, A 3, A 4] := by
  ext s
  fin_cases s <;> rfl

/-- Reachable running sums. -/
def R (A : Fin 5 → Fin 3) : Prop := reach (A 0) (A 1) (A 2) (A 3) (A 4) = true

lemma R_nxt (A v : Fin 5 → Fin 3) (hA : R A) (hv : colOKo A 1 v) : R (nxt A v) := by
  have h := closure (A 0) (A 1) (A 2) (A 3) (A 4) hA
  rw [← ssum_nest, ← vec_eta A] at h
  have e := (Finset.sum_eq_zero_iff.mp h) v (Finset.mem_univ v)
  rw [if_pos hv] at e
  try dsimp only at e
  unfold R
  by_contra hc
  rw [if_neg hc] at e
  exact one_ne_zero e

lemma W_succ_R (m : ℕ) (A : Fin 5 → Fin 3) (F : (Fin 5 → Fin 3) → ℕ) (hF : ∀ B, R B → W m B = F B) (hA : R A) :
    W (m + 1) A = nest 5 A 1 F := by
  rw [W_succ, ← ssum_nest]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · exact hF _ (R_nxt A v hA hv)
  · rfl

lemma W1 (A : Fin 5 → Fin 3) (hA : R A) : W 1 A = T1 (A 0) (A 1) (A 2) (A 3) (A 4) := by
  rw [W_succ_R 0 A (fun _ => 1) (fun B _ => W_zero B) hA, vec_eta A]
  exact check1 _ _ _ _ _ hA

lemma W2 (A : Fin 5 → Fin 3) (hA : R A) : W 2 A = T2 (A 0) (A 1) (A 2) (A 3) (A 4) := by
  rw [W_succ_R 1 A (fun B => T1 (B 0) (B 1) (B 2) (B 3) (B 4)) W1 hA, vec_eta A]
  exact check2 _ _ _ _ _ hA

lemma W3 (A : Fin 5 → Fin 3) (hA : R A) : W 3 A = T3 (A 0) (A 1) (A 2) (A 3) (A 4) := by
  rw [W_succ_R 2 A (fun B => T2 (B 0) (B 1) (B 2) (B 3) (B 4)) W2 hA, vec_eta A]
  exact check3 _ _ _ _ _ hA

lemma W4 (A : Fin 5 → Fin 3) (hA : R A) : W 4 A = T4 (A 0) (A 1) (A 2) (A 3) (A 4) := by
  rw [W_succ_R 3 A (fun B => T3 (B 0) (B 1) (B 2) (B 3) (B 4)) W3 hA, vec_eta A]
  exact check4 _ _ _ _ _ hA

lemma W5 (A : Fin 5 → Fin 3) (hA : R A) : W 5 A = T5 (A 0) (A 1) (A 2) (A 3) (A 4) := by
  rw [W_succ_R 4 A (fun B => T4 (B 0) (B 1) (B 2) (B 3) (B 4)) W4 hA, vec_eta A]
  exact check5 _ _ _ _ _ hA

lemma W6 (A : Fin 5 → Fin 3) (hA : R A) : W 6 A = T6 (A 0) (A 1) (A 2) (A 3) (A 4) := by
  rw [W_succ_R 5 A (fun B => T5 (B 0) (B 1) (B 2) (B 3) (B 4)) W5 hA, vec_eta A]
  exact check6 _ _ _ _ _ hA

lemma W7 (A : Fin 5 → Fin 3) (hA : R A) : W 7 A = T7 (A 0) (A 1) (A 2) (A 3) (A 4) := by
  rw [W_succ_R 6 A (fun B => T6 (B 0) (B 1) (B 2) (B 3) (B 4)) W6 hA, vec_eta A]
  exact check7 _ _ _ _ _ hA

lemma W8 (A : Fin 5 → Fin 3) (hA : R A) : W 8 A = T8 (A 0) (A 1) (A 2) (A 3) (A 4) := by
  rw [W_succ_R 7 A (fun B => T7 (B 0) (B 1) (B 2) (B 3) (B 4)) W7 hA, vec_eta A]
  exact check8 _ _ _ _ _ hA

lemma W_rec (n : ℕ) (A : Fin 5 → Fin 3) (hA : R A) :
    W (n + 9) A + 7 * W (n + 3) A + 35 * W (n + 5) A + 21 * W (n + 7) A = W (n + 2) A + 21 * W (n + 4) A + 35 * W (n + 6) A + 7 * W (n + 8) A := by
  induction n generalizing A with
  | zero =>
    rw [show (0 : ℕ) + 9 = 8 + 1 from rfl, W_succ_R 8 A (fun B => T8 (B 0) (B 1) (B 2) (B 3) (B 4)) W8 hA, show (0 : ℕ) + 3 = 3 from rfl, W3 A hA, show (0 : ℕ) + 5 = 5 from rfl, W5 A hA, show (0 : ℕ) + 7 = 7 from rfl, W7 A hA, show (0 : ℕ) + 2 = 2 from rfl, W2 A hA, show (0 : ℕ) + 4 = 4 from rfl, W4 A hA, show (0 : ℕ) + 6 = 6 from rfl, W6 A hA, show (0 : ℕ) + 8 = 8 from rfl, W8 A hA, vec_eta A]
    exact base_check _ _ _ _ _ hA
  | succ n ih =>
    rw [W_succ (n + 9), W_succ (n + 3), W_succ (n + 5), W_succ (n + 7), W_succ (n + 2), W_succ (n + 4), W_succ (n + 6), W_succ (n + 8)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : colOKo A 1 v
    · simp only [if_pos hv]
      exact ih _ (R_nxt A v hA hv)
    · simp [hv]

lemma R_zero : R 0 := by
  unfold R
  decide +kernel

lemma a_rec (n : ℕ) : a (n + 9) + 7 * a (n + 3) + 35 * a (n + 5) + 21 * a (n + 7) = a (n + 2) + 21 * a (n + 4) + 35 * a (n + 6) + 7 * a (n + 8) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  exact W_rec n 0 R_zero

lemma a_zero : a 0 = 1 := by rw [a_eq, W_zero]
lemma a_1 : a 1 = 4 := by rw [a_eq, W1 0 R_zero]; rfl
lemma a_2 : a 2 = 16 := by rw [a_eq, W2 0 R_zero]; rfl
lemma a_3 : a 3 = 54 := by rw [a_eq, W3 0 R_zero]; rfl
lemma a_4 : a 4 = 149 := by rw [a_eq, W4 0 R_zero]; rfl
lemma a_5 : a 5 = 354 := by rw [a_eq, W5 0 R_zero]; rfl
lemma a_6 : a 6 = 757 := by rw [a_eq, W6 0 R_zero]; rfl
lemma a_7 : a 7 = 1495 := by rw [a_eq, W7 0 R_zero]; rfl
lemma a_8 : a 8 = 2773 := by rw [a_eq, W8 0 R_zero]; rfl

lemma a_rec_z (n : ℕ) : (a (n + 9) : ℤ) + 7 * (a (n + 3) : ℤ) + 35 * (a (n + 5) : ℤ) + 21 * (a (n + 7) : ℤ) = (a (n + 2) : ℤ) + 21 * (a (n + 4) : ℤ) + 35 * (a (n + 6) : ℤ) + 7 * (a (n + 8) : ℤ) := by
  exact_mod_cast a_rec n

/-- The recurrence of the entry, for n > 8. -/
theorem recur : ∀ n : ℕ, 8 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 9 := ⟨n - 9, by omega⟩
  have h := a_rec_z j
  simp only [show j + 9 - 1 = j + 8 by omega, show j + 9 - 2 = j + 7 by omega, show j + 9 - 3 = j + 6 by omega, show j + 9 - 4 = j + 5 by omega, show j + 9 - 5 = j + 4 by omega, show j + 9 - 6 = j + 3 by omega, show j + 9 - 7 = j + 2 by omega]
  linear_combination h

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 7 = X * (4 - 12 * X + 26 * X ^ 2 - 33 * X ^ 3 + 25 * X ^ 4 - 6 * X ^ 5 - 3 * X ^ 6 + 4 * X ^ 7) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 7 = A - A * X ^ 1 * C 7 + A * X ^ 2 * C 21 - A * X ^ 3 * C 35 + A * X ^ 4 * C 35 - A * X ^ 5 * C 21 + A * X ^ 6 * C 7 - A * X ^ 7 := by
    rw [show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7, show (C (21 : ℚ) : ℚ⟦X⟧) = 21 from map_ofNat C 21, show (C (35 : ℚ) : ℚ⟦X⟧) = 35 from map_ofNat C 35]
    ring
  have e2 : (X * (4 - 12 * X + 26 * X ^ 2 - 33 * X ^ 3 + 25 * X ^ 4 - 6 * X ^ 5 - 3 * X ^ 6 + 4 * X ^ 7) : ℚ⟦X⟧) = X ^ 1 * C 4 - X ^ 2 * C 12 + X ^ 3 * C 26 - X ^ 4 * C 33 + X ^ 5 * C 25 - X ^ 6 * C 6 - X ^ 7 * C 3 + X ^ 8 * C 4 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6, show (C (12 : ℚ) : ℚ⟦X⟧) = 12 from map_ofNat C 12, show (C (25 : ℚ) : ℚ⟦X⟧) = 25 from map_ofNat C 25, show (C (26 : ℚ) : ℚ⟦X⟧) = 26 from map_ofNat C 26, show (C (33 : ℚ) : ℚ⟦X⟧) = 33 from map_ofNat C 33]
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
    have hq : (a (n + 0 + 9) : ℚ) + 7 * (a (n + 0 + 3) : ℚ) + 35 * (a (n + 0 + 5) : ℚ) + 21 * (a (n + 0 + 7) : ℚ) = (a (n + 0 + 2) : ℚ) + 21 * (a (n + 0 + 4) : ℚ) + 35 * (a (n + 0 + 6) : ℚ) + 7 * (a (n + 0 + 8) : ℚ) := by
      exact_mod_cast hz
    simp only [show n + 0 + 9 = n + 9 by omega, show n + 0 + 3 = n + 3 by omega, show n + 0 + 5 = n + 5 by omega, show n + 0 + 7 = n + 7 by omega, show n + 0 + 2 = n + 2 by omega, show n + 0 + 4 = n + 4 by omega, show n + 0 + 6 = n + 6 by omega, show n + 0 + 8 = n + 8 by omega] at hq
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
      show 7 ≤ n + 9 by omega,
      show ¬ (n + 9 - 7 = 0) by omega,
      show n + 9 - 7 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
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
      (1 - X) ^ 7 = X * (4 - 12 * X + 26 * X ^ 2 - 33 * X ^ 3 + 25 * X ^ 4 - 6 * X ^ 5 - 3 * X ^ 6 + 4 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a239032

theorem OMA.solution : type_of% @OMA.S_oeis_a239032.main :=
  OMA.S_oeis_a239032.conjecture
