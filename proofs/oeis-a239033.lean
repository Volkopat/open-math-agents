import OMAStatements.S_oeis_a239033

namespace OMA.S_oeis_a239033

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
def V (A : Fin 6 → Fin 3) {m : ℕ} (g : Fin m → Fin 6 → Fin 3) : Prop :=
  ∀ t : Fin m, ∀ s : Fin 6,
    (g t s).val ≠ (((A s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 3 ∧
    (g t s).val ≠ (1 + ∑ s' ∈ Iio s, (g t s').val) % 3

instance (A : Fin 6 → Fin 3) {m : ℕ} : DecidablePred (@V A m) := fun g => by
  unfold V; infer_instance

lemma V_cons (A : Fin 6 → Fin 3) {m : ℕ} (v : Fin 6 → Fin 3) (g : Fin m → Fin 6 → Fin 3) :
    V A (Fin.cons v g : Fin (m + 1) → Fin 6 → Fin 3) ↔ colOKo A 1 v ∧ V (nxt A v) g := by
  have key : ∀ (t : Fin m) (s : Fin 6),
      (((A s).val + ∑ t' ∈ Iio t.succ, ((Fin.cons v g : Fin (m + 1) → Fin 6 → Fin 3) t' s).val)) % 3 =
      (((nxt A v s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 3 := by
    intro t s
    rw [sum_Iio, sum_Iio, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff, nxt,
      Fin.val_add]
    omega
  have key0 : ∀ s : Fin 6,
      (((A s).val + ∑ t' ∈ Iio (0 : Fin (m + 1)), ((Fin.cons v g : Fin (m + 1) → Fin 6 → Fin 3) t' s).val)) % 3 =
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
def W (m : ℕ) (A : Fin 6 → Fin 3) : ℕ :=
  ((univ : Finset (Fin m → Fin 6 → Fin 3)).filter (V A)).card

lemma W_zero (A : Fin 6 → Fin 3) : W 0 A = 1 := by
  have e : (univ : Finset (Fin 0 → Fin 6 → Fin 3)).filter (V A) = univ :=
    Finset.filter_true_of_mem (fun g _ t => Fin.elim0 t)
  rw [W, e]
  simp

lemma W_succ (m : ℕ) (A : Fin 6 → Fin 3) :
    W (m + 1) A = ∑ v : Fin 6 → Fin 3, if colOKo A 1 v then W m (nxt A v) else 0 := by
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
def reach : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Bool :=
  ![![![![![![true, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]]],
      ![![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]]],
      ![![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]]]],
    ![![![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]]],
      ![![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]]],
      ![![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]]]],
    ![![![![![true, true, true], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![true, true, true]], ![![true, true, true], ![true, true, true], ![true, true, true]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]]],
      ![![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![false, false, false]]], ![![![true, true, true], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![true, true, true]], ![![true, true, true], ![true, true, true], ![true, true, true]]]],
      ![![![![true, true, true], ![true, true, true], ![true, true, true]], ![![false, false, false], ![false, false, false], ![true, true, true]], ![![false, false, false], ![true, true, true], ![false, false, false]]], ![![![true, true, true], ![false, false, false], ![false, false, false]], ![![false, false, false], ![false, false, false], ![true, true, true]], ![![true, true, true], ![true, true, true], ![true, true, true]]], ![![![true, true, true], ![true, true, true], ![true, true, true]], ![![true, true, true], ![true, true, true], ![true, true, true]], ![![true, true, true], ![true, true, true], ![true, true, true]]]]]]
abbrev u : Fin 3 → Fin 3 → Fin 3 → ℕ := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]]


def T1 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![8, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![4, 6, 6], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![5, 6, 5]], ![![6, 5, 5], ![5, 5, 6], ![5, 6, 5]]], u, u],
      ![u, u, ![![![4, 6, 6], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![4, 8, 4]], ![![4, 2, 2], ![6, 6, 4], ![2, 4, 2]]]],
      ![![![![4, 2, 2], ![4, 4, 4], ![4, 4, 4]], ![![0, 0, 0], ![0, 0, 0], ![3, 2, 3]], ![![0, 0, 0], ![3, 3, 2], ![0, 0, 0]]], ![![![6, 5, 5], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![5, 6, 5]], ![![4, 2, 2], ![6, 6, 4], ![2, 4, 2]]], ![![![2, 3, 3], ![1, 1, 2], ![1, 2, 1]], ![![4, 4, 4], ![4, 4, 4], ![2, 4, 2]], ![![2, 1, 1], ![3, 3, 2], ![1, 2, 1]]]]]]

def T2 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![43, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![16, 28, 16], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![22, 30, 18]], ![![15, 9, 9], ![14, 22, 18], ![9, 15, 9]]], u, u],
      ![u, u, ![![![20, 32, 24], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![21, 43, 21]], ![![17, 7, 7], ![24, 32, 20], ![7, 17, 7]]]],
      ![![![![11, 5, 5], ![15, 15, 13], ![6, 10, 6]], ![![0, 0, 0], ![0, 0, 0], ![8, 4, 4]], ![![0, 0, 0], ![8, 4, 4], ![0, 0, 0]]], ![![![18, 22, 14], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![18, 30, 22]], ![![14, 6, 6], ![16, 28, 16], ![6, 14, 6]]], ![![![4, 8, 4], ![1, 1, 3], ![1, 3, 1]], ![![10, 6, 6], ![15, 15, 13], ![5, 11, 5]], ![![3, 1, 1], ![4, 8, 4], ![1, 3, 1]]]]]]

def T3 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![212, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![54, 99, 51], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![59, 109, 56]], ![![38, 15, 15], ![44, 74, 46], ![15, 38, 15]]], u, u],
      ![u, u, ![![![70, 124, 70], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![79, 212, 79]], ![![48, 16, 16], ![70, 124, 70], ![16, 48, 16]]]],
      ![![![![28, 9, 9], ![33, 48, 31], ![10, 22, 10]], ![![0, 0, 0], ![0, 0, 0], ![15, 7, 6]], ![![0, 0, 0], ![15, 6, 7], ![0, 0, 0]]], ![![![46, 74, 44], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![56, 109, 59]], ![![36, 12, 12], ![51, 99, 54], ![12, 36, 12]]], ![![![7, 15, 6], ![1, 1, 4], ![1, 4, 1]], ![![22, 10, 10], ![33, 48, 31], ![9, 28, 9]], ![![4, 1, 1], ![6, 15, 7], ![1, 4, 1]]]]]]

def T4 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![806, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![149, 295, 127], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![151, 335, 143]], ![![78, 24, 24], ![108, 216, 116], ![24, 78, 24]]], u, u],
      ![u, u, ![![![202, 398, 178], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![256, 806, 256]], ![![117, 31, 31], ![178, 398, 202], ![31, 117, 31]]]],
      ![![![![59, 15, 15], ![66, 118, 66], ![15, 45, 15]], ![![0, 0, 0], ![0, 0, 0], ![25, 11, 9]], ![![0, 0, 0], ![25, 9, 11], ![0, 0, 0]]], ![![![116, 216, 108], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![143, 335, 151]], ![![80, 22, 22], ![127, 295, 149], ![22, 80, 22]]], ![![![11, 25, 9], ![1, 1, 5], ![1, 5, 1]], ![![45, 15, 15], ![66, 118, 66], ![15, 59, 15]], ![![5, 1, 1], ![9, 25, 11], ![1, 5, 1]]]]]]

def T5 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![2592, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![354, 745, 289], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![348, 914, 334]], ![![148, 38, 38], ![243, 552, 269], ![38, 148, 38]]], u, u],
      ![u, u, ![![![513, 1095, 428], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![704, 2592, 704]], ![![250, 55, 55], ![428, 1095, 513], ![55, 250, 55]]]],
      ![![![![110, 24, 24], ![121, 254, 131], ![22, 84, 22]], ![![0, 0, 0], ![0, 0, 0], ![39, 16, 13]], ![![0, 0, 0], ![39, 13, 16], ![0, 0, 0]]], ![![![269, 552, 243], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![334, 914, 348]], ![![162, 37, 37], ![289, 745, 354], ![37, 162, 37]]], ![![![16, 39, 13], ![1, 1, 6], ![1, 6, 1]], ![![84, 22, 22], ![121, 254, 131], ![24, 110, 24]], ![![6, 1, 1], ![13, 39, 16], ![1, 6, 1]]]]]]

def T6 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![7265, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![757, 1681, 607], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![745, 2263, 723]], ![![266, 58, 58], ![506, 1274, 574], ![58, 266, 58]]], u, u],
      ![u, u, ![![![1180, 2716, 968], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1755, 7265, 1755]], ![![491, 93, 93], ![968, 2716, 1180], ![93, 491, 93]]]],
      ![![![![189, 37, 37], ![214, 498, 244], ![32, 146, 32]], ![![0, 0, 0], ![0, 0, 0], ![58, 22, 18]], ![![0, 0, 0], ![58, 18, 22], ![0, 0, 0]]], ![![![574, 1274, 506], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![723, 2263, 745]], ![![305, 59, 59], ![607, 1681, 757], ![59, 305, 59]]], ![![![22, 58, 18], ![1, 1, 7], ![1, 7, 1]], ![![146, 32, 32], ![214, 498, 244], ![37, 189, 37]], ![![7, 1, 1], ![18, 58, 22], ![1, 7, 1]]]]]]

def T7 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![18362, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![1495, 3494, 1193], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1504, 5169, 1471]], ![![458, 86, 86], ![991, 2709, 1142], ![86, 458, 86]]], u, u],
      ![u, u, ![![![2511, 6221, 2056], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![4053, 18362, 4053]], ![![908, 151, 151], ![2056, 6221, 2511], ![151, 908, 151]]]],
      ![![![![306, 55, 55], ![366, 916, 430], ![46, 240, 46]], ![![0, 0, 0], ![0, 0, 0], ![83, 29, 24]], ![![0, 0, 0], ![83, 24, 29], ![0, 0, 0]]], ![![![1142, 2709, 991], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1471, 5169, 1504]], ![![542, 91, 91], ![1193, 3494, 1495], ![91, 542, 91]]], ![![![29, 83, 24], ![1, 1, 8], ![1, 8, 1]], ![![240, 46, 46], ![366, 916, 430], ![55, 306, 55]], ![![8, 1, 1], ![24, 83, 29], ![1, 8, 1]]]]]]

def T8 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![42809, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![2773, 6817, 2217], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![2893, 11037, 2845]], ![![761, 125, 125], ![1843, 5395, 2143], ![125, 761, 125]]], u, u],
      ![u, u, ![![![5019, 13343, 4127], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![8773, 42809, 8773]], ![![1603, 237, 237], ![4127, 13343, 5019], ![237, 1603, 237]]]],
      ![![![![473, 79, 79], ![605, 1605, 723], ![65, 377, 65]], ![![0, 0, 0], ![0, 0, 0], ![115, 37, 31]], ![![0, 0, 0], ![115, 31, 37], ![0, 0, 0]]], ![![![2143, 5395, 1843], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![2845, 11037, 2893]], ![![919, 137, 137], ![2217, 6817, 2773], ![137, 919, 137]]], ![![![37, 115, 31], ![1, 1, 9], ![1, 9, 1]], ![![377, 65, 65], ![605, 1605, 723], ![79, 473, 79]], ![![9, 1, 1], ![31, 115, 37], ![1, 9, 1]]]]]]

def T9 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![93464, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![4888, 12636, 3928], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![5339, 22270, 5271]], ![![1226, 179, 179], ![3277, 10183, 3828], ![179, 1226, 179]]], u, u],
      ![u, u, ![![![9526, 27072, 7886], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![17962, 93464, 17962]], ![![2726, 362, 362], ![7886, 27072, 9526], ![362, 2726, 362]]]],
      ![![![![704, 110, 110], ![968, 2702, 1168], ![90, 570, 90]], ![![0, 0, 0], ![0, 0, 0], ![155, 46, 39]], ![![0, 0, 0], ![155, 39, 46], ![0, 0, 0]]], ![![![3828, 10183, 3277], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![5271, 22270, 5339]], ![![1498, 202, 202], ![3928, 12636, 4888], ![202, 1498, 202]]], ![![![46, 155, 39], ![1, 1, 10], ![1, 10, 1]], ![![570, 90, 90], ![968, 2702, 1168], ![110, 704, 110]], ![![10, 1, 1], ![39, 155, 46], ![1, 10, 1]]]]]]

def T10 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![193157, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![8258, 22436, 6680], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![9500, 42826, 9406]], ![![1921, 253, 253], ![5602, 18372, 6556], ![253, 1921, 253]]], u, u],
      ![u, u, ![![![17306, 52370, 14436], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![35047, 193157, 35047]], ![![4493, 541, 541], ![14436, 52370, 17306], ![541, 4493, 541]]]],
      ![![![![1015, 149, 149], ![1503, 4395, 1823], ![122, 834, 122]], ![![0, 0, 0], ![0, 0, 0], ![204, 56, 48]], ![![0, 0, 0], ![204, 48, 56], ![0, 0, 0]]], ![![![6556, 18372, 5602], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![9406, 42826, 9500]], ![![2360, 292, 292], ![6680, 22436, 8258], ![292, 2360, 292]]], ![![![56, 204, 48], ![1, 1, 11], ![1, 11, 1]], ![![834, 122, 122], ![1503, 4395, 1823], ![149, 1015, 149]], ![![11, 1, 1], ![48, 204, 56], ![1, 11, 1]]]]]]

def T11 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![380900, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![13456, 38389, 10963], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![16361, 79009, 16234]], ![![2934, 353, 353], ![9250, 31884, 10826], ![353, 2934, 353]]], u, u],
      ![u, u, ![![![30276, 97194, 25450], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![65569, 380900, 65569]], ![![7208, 794, 794], ![25450, 97194, 30276], ![794, 7208, 794]]]],
      ![![![![1424, 197, 197], ![2271, 6936, 2761], ![162, 1186, 162]], ![![0, 0, 0], ![0, 0, 0], ![263, 67, 58]], ![![0, 0, 0], ![263, 58, 67], ![0, 0, 0]]], ![![![10826, 31884, 9250], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![16234, 79009, 16361]], ![![3608, 414, 414], ![10963, 38389, 13456], ![414, 3608, 414]]], ![![![67, 263, 58], ![1, 1, 12], ![1, 12, 1]], ![![1186, 162, 162], ![2271, 6936, 2761], ![197, 1424, 197]], ![![12, 1, 1], ![58, 263, 67], ![1, 12, 1]]]]]]

def T12 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![![![721154, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]], u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![u, u, u],
      ![u, u, u],
      ![u, u, u]],
    ![![![![![21249, 63591, 17439], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![27359, 140563, 27191]], ![![4376, 486, 486], ![14810, 53486, 17314], ![486, 4376, 486]]], u, u],
      ![u, u, ![![![51244, 173920, 43396], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![118216, 721154, 118216]], ![![11289, 1147, 1147], ![43396, 173920, 51244], ![1147, 11289, 1147]]]],
      ![![![![1951, 255, 255], ![3348, 10656, 4072], ![211, 1645, 211]], ![![0, 0, 0], ![0, 0, 0], ![333, 79, 69]], ![![0, 0, 0], ![333, 69, 79], ![0, 0, 0]]], ![![![17314, 53486, 14810], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![27191, 140563, 27359]], ![![5370, 576, 576], ![17439, 63591, 21249], ![576, 5370, 576]]], ![![![79, 333, 69], ![1, 1, 13], ![1, 13, 1]], ![![1645, 211, 211], ![3348, 10656, 4072], ![255, 1951, 255]], ![![13, 1, 1], ![69, 333, 79], ![1, 13, 1]]]]]]

set_option maxHeartbeats 4000000 in
lemma closure : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => if reach (B 0) (B 1) (B 2) (B 3) (B 4) (B 5) = true then 0 else 1) = 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check1 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun _ => 1) = T1 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check2 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T1 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T2 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check3 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T2 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T3 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check4 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T3 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T4 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check5 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T4 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T5 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check6 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T5 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T6 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check7 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T6 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T7 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check8 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T7 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T8 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check9 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T8 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T9 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check10 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T9 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T10 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check11 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T10 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T11 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check12 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T11 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) = T12 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, reach a0 a1 a2 a3 a4 a5 = true →
    nest 6 ![a0, a1, a2, a3, a4, a5] 1 (fun B => T12 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) + T3 a0 a1 a2 a3 a4 a5 + 45 * T5 a0 a1 a2 a3 a4 a5 + 210 * T7 a0 a1 a2 a3 a4 a5 + 210 * T9 a0 a1 a2 a3 a4 a5 + 45 * T11 a0 a1 a2 a3 a4 a5 = 10 * T4 a0 a1 a2 a3 a4 a5 + 120 * T6 a0 a1 a2 a3 a4 a5 + 252 * T8 a0 a1 a2 a3 a4 a5 + 120 * T10 a0 a1 a2 a3 a4 a5 + 10 * T12 a0 a1 a2 a3 a4 a5 := by
  decide +kernel

lemma vec_eta (A : Fin 6 → Fin 3) : A = ![A 0, A 1, A 2, A 3, A 4, A 5] := by
  ext s
  fin_cases s <;> rfl

/-- Reachable running sums. -/
def R (A : Fin 6 → Fin 3) : Prop := reach (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) = true

lemma R_nxt (A v : Fin 6 → Fin 3) (hA : R A) (hv : colOKo A 1 v) : R (nxt A v) := by
  have h := closure (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) hA
  rw [← ssum_nest, ← vec_eta A] at h
  have e := (Finset.sum_eq_zero_iff.mp h) v (Finset.mem_univ v)
  rw [if_pos hv] at e
  try dsimp only at e
  unfold R
  by_contra hc
  rw [if_neg hc] at e
  exact one_ne_zero e

lemma W_succ_R (m : ℕ) (A : Fin 6 → Fin 3) (F : (Fin 6 → Fin 3) → ℕ) (hF : ∀ B, R B → W m B = F B) (hA : R A) :
    W (m + 1) A = nest 6 A 1 F := by
  rw [W_succ, ← ssum_nest]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · exact hF _ (R_nxt A v hA hv)
  · rfl

lemma W1 (A : Fin 6 → Fin 3) (hA : R A) : W 1 A = T1 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 0 A (fun _ => 1) (fun B _ => W_zero B) hA, vec_eta A]
  exact check1 _ _ _ _ _ _ hA

lemma W2 (A : Fin 6 → Fin 3) (hA : R A) : W 2 A = T2 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 1 A (fun B => T1 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W1 hA, vec_eta A]
  exact check2 _ _ _ _ _ _ hA

lemma W3 (A : Fin 6 → Fin 3) (hA : R A) : W 3 A = T3 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 2 A (fun B => T2 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W2 hA, vec_eta A]
  exact check3 _ _ _ _ _ _ hA

lemma W4 (A : Fin 6 → Fin 3) (hA : R A) : W 4 A = T4 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 3 A (fun B => T3 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W3 hA, vec_eta A]
  exact check4 _ _ _ _ _ _ hA

lemma W5 (A : Fin 6 → Fin 3) (hA : R A) : W 5 A = T5 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 4 A (fun B => T4 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W4 hA, vec_eta A]
  exact check5 _ _ _ _ _ _ hA

lemma W6 (A : Fin 6 → Fin 3) (hA : R A) : W 6 A = T6 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 5 A (fun B => T5 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W5 hA, vec_eta A]
  exact check6 _ _ _ _ _ _ hA

lemma W7 (A : Fin 6 → Fin 3) (hA : R A) : W 7 A = T7 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 6 A (fun B => T6 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W6 hA, vec_eta A]
  exact check7 _ _ _ _ _ _ hA

lemma W8 (A : Fin 6 → Fin 3) (hA : R A) : W 8 A = T8 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 7 A (fun B => T7 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W7 hA, vec_eta A]
  exact check8 _ _ _ _ _ _ hA

lemma W9 (A : Fin 6 → Fin 3) (hA : R A) : W 9 A = T9 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 8 A (fun B => T8 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W8 hA, vec_eta A]
  exact check9 _ _ _ _ _ _ hA

lemma W10 (A : Fin 6 → Fin 3) (hA : R A) : W 10 A = T10 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 9 A (fun B => T9 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W9 hA, vec_eta A]
  exact check10 _ _ _ _ _ _ hA

lemma W11 (A : Fin 6 → Fin 3) (hA : R A) : W 11 A = T11 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 10 A (fun B => T10 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W10 hA, vec_eta A]
  exact check11 _ _ _ _ _ _ hA

lemma W12 (A : Fin 6 → Fin 3) (hA : R A) : W 12 A = T12 (A 0) (A 1) (A 2) (A 3) (A 4) (A 5) := by
  rw [W_succ_R 11 A (fun B => T11 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W11 hA, vec_eta A]
  exact check12 _ _ _ _ _ _ hA

lemma W_rec (n : ℕ) (A : Fin 6 → Fin 3) (hA : R A) :
    W (n + 13) A + W (n + 3) A + 45 * W (n + 5) A + 210 * W (n + 7) A + 210 * W (n + 9) A + 45 * W (n + 11) A = 10 * W (n + 4) A + 120 * W (n + 6) A + 252 * W (n + 8) A + 120 * W (n + 10) A + 10 * W (n + 12) A := by
  induction n generalizing A with
  | zero =>
    rw [show (0 : ℕ) + 13 = 12 + 1 from rfl, W_succ_R 12 A (fun B => T12 (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)) W12 hA, show (0 : ℕ) + 3 = 3 from rfl, W3 A hA, show (0 : ℕ) + 5 = 5 from rfl, W5 A hA, show (0 : ℕ) + 7 = 7 from rfl, W7 A hA, show (0 : ℕ) + 9 = 9 from rfl, W9 A hA, show (0 : ℕ) + 11 = 11 from rfl, W11 A hA, show (0 : ℕ) + 4 = 4 from rfl, W4 A hA, show (0 : ℕ) + 6 = 6 from rfl, W6 A hA, show (0 : ℕ) + 8 = 8 from rfl, W8 A hA, show (0 : ℕ) + 10 = 10 from rfl, W10 A hA, show (0 : ℕ) + 12 = 12 from rfl, W12 A hA, vec_eta A]
    exact base_check _ _ _ _ _ _ hA
  | succ n ih =>
    rw [W_succ (n + 13), W_succ (n + 3), W_succ (n + 5), W_succ (n + 7), W_succ (n + 9), W_succ (n + 11), W_succ (n + 4), W_succ (n + 6), W_succ (n + 8), W_succ (n + 10), W_succ (n + 12)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : colOKo A 1 v
    · simp only [if_pos hv]
      exact ih _ (R_nxt A v hA hv)
    · simp [hv]

lemma R_zero : R 0 := by
  unfold R
  decide +kernel

lemma a_rec (n : ℕ) : a (n + 13) + a (n + 3) + 45 * a (n + 5) + 210 * a (n + 7) + 210 * a (n + 9) + 45 * a (n + 11) = 10 * a (n + 4) + 120 * a (n + 6) + 252 * a (n + 8) + 120 * a (n + 10) + 10 * a (n + 12) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  exact W_rec n 0 R_zero

lemma a_zero : a 0 = 1 := by rw [a_eq, W_zero]
lemma a_1 : a 1 = 8 := by rw [a_eq, W1 0 R_zero]; rfl
lemma a_2 : a 2 = 43 := by rw [a_eq, W2 0 R_zero]; rfl
lemma a_3 : a 3 = 212 := by rw [a_eq, W3 0 R_zero]; rfl
lemma a_4 : a 4 = 806 := by rw [a_eq, W4 0 R_zero]; rfl
lemma a_5 : a 5 = 2592 := by rw [a_eq, W5 0 R_zero]; rfl
lemma a_6 : a 6 = 7265 := by rw [a_eq, W6 0 R_zero]; rfl
lemma a_7 : a 7 = 18362 := by rw [a_eq, W7 0 R_zero]; rfl
lemma a_8 : a 8 = 42809 := by rw [a_eq, W8 0 R_zero]; rfl
lemma a_9 : a 9 = 93464 := by rw [a_eq, W9 0 R_zero]; rfl
lemma a_10 : a 10 = 193157 := by rw [a_eq, W10 0 R_zero]; rfl
lemma a_11 : a 11 = 380900 := by rw [a_eq, W11 0 R_zero]; rfl
lemma a_12 : a 12 = 721154 := by rw [a_eq, W12 0 R_zero]; rfl

lemma a_rec_z (n : ℕ) : (a (n + 13) : ℤ) + (a (n + 3) : ℤ) + 45 * (a (n + 5) : ℤ) + 210 * (a (n + 7) : ℤ) + 210 * (a (n + 9) : ℤ) + 45 * (a (n + 11) : ℤ) = 10 * (a (n + 4) : ℤ) + 120 * (a (n + 6) : ℤ) + 252 * (a (n + 8) : ℤ) + 120 * (a (n + 10) : ℤ) + 10 * (a (n + 12) : ℤ) := by
  exact_mod_cast a_rec n

/-- The recurrence of the entry, for n > 12. -/
theorem recur : ∀ n : ℕ, 12 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 13 := ⟨n - 13, by omega⟩
  have h := a_rec_z j
  simp only [show j + 13 - 1 = j + 12 by omega, show j + 13 - 2 = j + 11 by omega, show j + 13 - 3 = j + 10 by omega, show j + 13 - 4 = j + 9 by omega, show j + 13 - 5 = j + 8 by omega, show j + 13 - 6 = j + 7 by omega, show j + 13 - 7 = j + 6 by omega, show j + 13 - 8 = j + 5 by omega, show j + 13 - 9 = j + 4 by omega, show j + 13 - 10 = j + 3 by omega]
  linear_combination h

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 10 = X * (8 - 37 * X + 142 * X ^ 2 - 339 * X ^ 3 + 592 * X ^ 4 - 811 * X ^ 5 + 996 * X ^ 6 - 1020 * X ^ 7 + 792 * X ^ 8 - 377 * X ^ 9 + 88 * X ^ 10 + 8 * X ^ 11) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 10 = A - A * X ^ 1 * C 10 + A * X ^ 2 * C 45 - A * X ^ 3 * C 120 + A * X ^ 4 * C 210 - A * X ^ 5 * C 252 + A * X ^ 6 * C 210 - A * X ^ 7 * C 120 + A * X ^ 8 * C 45 - A * X ^ 9 * C 10 + A * X ^ 10 := by
    rw [show (C (10 : ℚ) : ℚ⟦X⟧) = 10 from map_ofNat C 10, show (C (45 : ℚ) : ℚ⟦X⟧) = 45 from map_ofNat C 45, show (C (120 : ℚ) : ℚ⟦X⟧) = 120 from map_ofNat C 120, show (C (210 : ℚ) : ℚ⟦X⟧) = 210 from map_ofNat C 210, show (C (252 : ℚ) : ℚ⟦X⟧) = 252 from map_ofNat C 252]
    ring
  have e2 : (X * (8 - 37 * X + 142 * X ^ 2 - 339 * X ^ 3 + 592 * X ^ 4 - 811 * X ^ 5 + 996 * X ^ 6 - 1020 * X ^ 7 + 792 * X ^ 8 - 377 * X ^ 9 + 88 * X ^ 10 + 8 * X ^ 11) : ℚ⟦X⟧) = X ^ 1 * C 8 - X ^ 2 * C 37 + X ^ 3 * C 142 - X ^ 4 * C 339 + X ^ 5 * C 592 - X ^ 6 * C 811 + X ^ 7 * C 996 - X ^ 8 * C 1020 + X ^ 9 * C 792 - X ^ 10 * C 377 + X ^ 11 * C 88 + X ^ 12 * C 8 := by
    rw [show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8, show (C (37 : ℚ) : ℚ⟦X⟧) = 37 from map_ofNat C 37, show (C (88 : ℚ) : ℚ⟦X⟧) = 88 from map_ofNat C 88, show (C (142 : ℚ) : ℚ⟦X⟧) = 142 from map_ofNat C 142, show (C (339 : ℚ) : ℚ⟦X⟧) = 339 from map_ofNat C 339, show (C (377 : ℚ) : ℚ⟦X⟧) = 377 from map_ofNat C 377, show (C (592 : ℚ) : ℚ⟦X⟧) = 592 from map_ofNat C 592, show (C (792 : ℚ) : ℚ⟦X⟧) = 792 from map_ofNat C 792, show (C (811 : ℚ) : ℚ⟦X⟧) = 811 from map_ofNat C 811, show (C (996 : ℚ) : ℚ⟦X⟧) = 996 from map_ofNat C 996, show (C (1020 : ℚ) : ℚ⟦X⟧) = 1020 from map_ofNat C 1020]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
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
  · have hz := a_rec_z (n + 0)
    have hq : (a (n + 0 + 13) : ℚ) + (a (n + 0 + 3) : ℚ) + 45 * (a (n + 0 + 5) : ℚ) + 210 * (a (n + 0 + 7) : ℚ) + 210 * (a (n + 0 + 9) : ℚ) + 45 * (a (n + 0 + 11) : ℚ) = 10 * (a (n + 0 + 4) : ℚ) + 120 * (a (n + 0 + 6) : ℚ) + 252 * (a (n + 0 + 8) : ℚ) + 120 * (a (n + 0 + 10) : ℚ) + 10 * (a (n + 0 + 12) : ℚ) := by
      exact_mod_cast hz
    simp only [show n + 0 + 13 = n + 13 by omega, show n + 0 + 3 = n + 3 by omega, show n + 0 + 5 = n + 5 by omega, show n + 0 + 7 = n + 7 by omega, show n + 0 + 9 = n + 9 by omega, show n + 0 + 11 = n + 11 by omega, show n + 0 + 4 = n + 4 by omega, show n + 0 + 6 = n + 6 by omega, show n + 0 + 8 = n + 8 by omega, show n + 0 + 10 = n + 10 by omega, show n + 0 + 12 = n + 12 by omega] at hq
    simp only [if_false, if_true, show ¬ (n + 13 = 0) by omega,
      show 1 ≤ n + 13 by omega,
      show ¬ (n + 13 - 1 = 0) by omega,
      show n + 13 - 1 = n + 12 by omega,
      show ¬ (n + 12 = 0) by omega,
      show 2 ≤ n + 13 by omega,
      show ¬ (n + 13 - 2 = 0) by omega,
      show n + 13 - 2 = n + 11 by omega,
      show ¬ (n + 11 = 0) by omega,
      show 3 ≤ n + 13 by omega,
      show ¬ (n + 13 - 3 = 0) by omega,
      show n + 13 - 3 = n + 10 by omega,
      show ¬ (n + 10 = 0) by omega,
      show 4 ≤ n + 13 by omega,
      show ¬ (n + 13 - 4 = 0) by omega,
      show n + 13 - 4 = n + 9 by omega,
      show ¬ (n + 9 = 0) by omega,
      show 5 ≤ n + 13 by omega,
      show ¬ (n + 13 - 5 = 0) by omega,
      show n + 13 - 5 = n + 8 by omega,
      show ¬ (n + 8 = 0) by omega,
      show 6 ≤ n + 13 by omega,
      show ¬ (n + 13 - 6 = 0) by omega,
      show n + 13 - 6 = n + 7 by omega,
      show ¬ (n + 7 = 0) by omega,
      show 7 ≤ n + 13 by omega,
      show ¬ (n + 13 - 7 = 0) by omega,
      show n + 13 - 7 = n + 6 by omega,
      show ¬ (n + 6 = 0) by omega,
      show 8 ≤ n + 13 by omega,
      show ¬ (n + 13 - 8 = 0) by omega,
      show n + 13 - 8 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 9 ≤ n + 13 by omega,
      show ¬ (n + 13 - 9 = 0) by omega,
      show n + 13 - 9 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 10 ≤ n + 13 by omega,
      show ¬ (n + 13 - 10 = 0) by omega,
      show n + 13 - 10 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show ¬ (n + 13 = 1) by omega,
      show ¬ (n + 13 = 2) by omega,
      show ¬ (n + 13 = 3) by omega,
      show ¬ (n + 13 = 4) by omega,
      show ¬ (n + 13 = 5) by omega,
      show ¬ (n + 13 = 6) by omega,
      show ¬ (n + 13 = 7) by omega,
      show ¬ (n + 13 = 8) by omega,
      show ¬ (n + 13 = 9) by omega,
      show ¬ (n + 13 = 10) by omega,
      show ¬ (n + 13 = 11) by omega,
      show ¬ (n + 13 = 12) by omega]
    linear_combination hq

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 10 = X * (8 - 37 * X + 142 * X ^ 2 - 339 * X ^ 3 + 592 * X ^ 4 - 811 * X ^ 5 + 996 * X ^ 6 - 1020 * X ^ 7 + 792 * X ^ 8 - 377 * X ^ 9 + 88 * X ^ 10 + 8 * X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a239033

theorem OMA.solution : type_of% @OMA.S_oeis_a239033.main :=
  OMA.S_oeis_a239033.conjecture
