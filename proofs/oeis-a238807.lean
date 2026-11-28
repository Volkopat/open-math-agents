import OMAStatements.S_oeis_a238807

namespace OMA.S_oeis_a238807

open PowerSeries Finset




lemma sum_Iio {m : ℕ} (j : Fin m) (h : Fin m → ℕ) :
    ∑ x ∈ Iio j, h x = ∑ x, if x < j then h x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

/-- The conditions on one slice v when the running sums along the growing dimension are A. -/
def colOK (A v : Fin 3 → Fin 3) : Prop :=
  ∀ s : Fin 3, (v s).val ≠ (1 + (A s).val) % 3 ∧
    (v s).val ≠ (1 + ∑ s' ∈ Iio s, (v s').val) % 3

instance : DecidableRel colOK := fun A v => by unfold colOK; infer_instance

/-- The running sums after the slice v. -/
def nxt (A v : Fin 3 → Fin 3) : Fin 3 → Fin 3 := fun s => A s + v s

/-- An array of slices is valid when started from the running sums A. -/
def V (A : Fin 3 → Fin 3) {m : ℕ} (g : Fin m → Fin 3 → Fin 3) : Prop :=
  ∀ t : Fin m, ∀ s : Fin 3,
    (g t s).val ≠ (1 + ((A s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 3 ∧
    (g t s).val ≠ (1 + ∑ s' ∈ Iio s, (g t s').val) % 3

instance (A : Fin 3 → Fin 3) {m : ℕ} : DecidablePred (@V A m) := fun g => by
  unfold V; infer_instance

lemma V_cons (A : Fin 3 → Fin 3) {m : ℕ} (v : Fin 3 → Fin 3) (g : Fin m → Fin 3 → Fin 3) :
    V A (Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 3) ↔ colOK A v ∧ V (nxt A v) g := by
  have key : ∀ (t : Fin m) (s : Fin 3),
      (1 + ((A s).val + ∑ t' ∈ Iio t.succ, ((Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 3) t' s).val)) % 3 =
      (1 + ((nxt A v s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 3 := by
    intro t s
    rw [sum_Iio, sum_Iio, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff, nxt,
      Fin.val_add]
    omega
  have key0 : ∀ s : Fin 3,
      (1 + ((A s).val + ∑ t' ∈ Iio (0 : Fin (m + 1)), ((Fin.cons v g : Fin (m + 1) → Fin 3 → Fin 3) t' s).val)) % 3 =
      (1 + (A s).val) % 3 := by
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
def W (m : ℕ) (A : Fin 3 → Fin 3) : ℕ :=
  ((univ : Finset (Fin m → Fin 3 → Fin 3)).filter (V A)).card

lemma W_zero (A : Fin 3 → Fin 3) : W 0 A = 1 := by
  have e : (univ : Finset (Fin 0 → Fin 3 → Fin 3)).filter (V A) = univ :=
    Finset.filter_true_of_mem (fun g _ t => Fin.elim0 t)
  rw [W, e]
  simp

lemma W_succ (m : ℕ) (A : Fin 3 → Fin 3) :
    W (m + 1) A = ∑ v : Fin 3 → Fin 3, if colOK A v then W m (nxt A v) else 0 := by
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
  congr 1
  ext f
  simp only [mem_filter, mem_univ, true_and, good, V, Pi.zero_apply, Fin.val_zero, zero_add]
  exact forall_congr' fun i => forall_congr' fun j => and_comm

/-- The sum, over the slices allowed after the running sums A, of F at the next running sums. -/
def ssum (A : Fin 3 → Fin 3) (F : Fin 3 → Fin 3 → Fin 3 → ℕ) : ℕ :=
  ∑ v : Fin 3 → Fin 3, if colOK A v then F (nxt A v 0) (nxt A v 1) (nxt A v 2) else 0

/-- The reachable running sums. -/
def reach : Fin 3 → Fin 3 → Fin 3 → Bool :=
  ![![![true, true, true],
      ![true, true, true],
      ![true, true, true]],
    ![![true, true, true],
      ![true, true, true],
      ![true, true, true]],
    ![![true, true, true],
      ![true, true, true],
      ![true, true, true]]]

def T1 : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![4, 4, 4],
      ![4, 2, 2],
      ![4, 4, 4]],
    ![![3, 2, 3],
      ![2, 1, 1],
      ![1, 1, 2]],
    ![![1, 2, 1],
      ![2, 1, 1],
      ![3, 3, 2]]]

def T2 : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![15, 13, 15],
      ![11, 5, 5],
      ![6, 6, 10]],
    ![![8, 4, 4],
      ![3, 1, 1],
      ![1, 1, 3]],
    ![![1, 3, 1],
      ![3, 1, 1],
      ![8, 4, 4]]]

def T3 : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![48, 31, 33],
      ![28, 9, 9],
      ![10, 10, 22]],
    ![![15, 7, 6],
      ![4, 1, 1],
      ![1, 1, 4]],
    ![![1, 4, 1],
      ![4, 1, 1],
      ![15, 6, 7]]]

def T4 : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![118, 66, 66],
      ![59, 15, 15],
      ![15, 15, 45]],
    ![![25, 11, 9],
      ![5, 1, 1],
      ![1, 1, 5]],
    ![![1, 5, 1],
      ![5, 1, 1],
      ![25, 9, 11]]]

def T5 : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![254, 131, 121],
      ![110, 24, 24],
      ![22, 22, 84]],
    ![![39, 16, 13],
      ![6, 1, 1],
      ![1, 1, 6]],
    ![![1, 6, 1],
      ![6, 1, 1],
      ![39, 13, 16]]]

def T6 : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![498, 244, 214],
      ![189, 37, 37],
      ![32, 32, 146]],
    ![![58, 22, 18],
      ![7, 1, 1],
      ![1, 1, 7]],
    ![![1, 7, 1],
      ![7, 1, 1],
      ![58, 18, 22]]]

def T7 : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![916, 430, 366],
      ![306, 55, 55],
      ![46, 46, 240]],
    ![![83, 29, 24],
      ![8, 1, 1],
      ![1, 1, 8]],
    ![![1, 8, 1],
      ![8, 1, 1],
      ![83, 24, 29]]]

def T8 : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![1605, 723, 605],
      ![473, 79, 79],
      ![65, 65, 377]],
    ![![115, 37, 31],
      ![9, 1, 1],
      ![1, 1, 9]],
    ![![1, 9, 1],
      ![9, 1, 1],
      ![115, 31, 37]]]

def T9 : Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![2702, 1168, 968],
      ![704, 110, 110],
      ![90, 90, 570]],
    ![![155, 46, 39],
      ![10, 1, 1],
      ![1, 1, 10]],
    ![![1, 10, 1],
      ![10, 1, 1],
      ![155, 39, 46]]]

set_option maxHeartbeats 4000000 in
lemma closure : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true → ∀ v : Fin 3 → Fin 3, colOK ![a0, a1, a2] v →
    reach (nxt ![a0, a1, a2] v 0) (nxt ![a0, a1, a2] v 1) (nxt ![a0, a1, a2] v 2) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check1 : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true → ssum ![a0, a1, a2] (fun _ _ _ => 1) = T1 a0 a1 a2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check2 : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true → ssum ![a0, a1, a2] T1 = T2 a0 a1 a2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check3 : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true → ssum ![a0, a1, a2] T2 = T3 a0 a1 a2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check4 : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true → ssum ![a0, a1, a2] T3 = T4 a0 a1 a2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check5 : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true → ssum ![a0, a1, a2] T4 = T5 a0 a1 a2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check6 : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true → ssum ![a0, a1, a2] T5 = T6 a0 a1 a2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check7 : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true → ssum ![a0, a1, a2] T6 = T7 a0 a1 a2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check8 : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true → ssum ![a0, a1, a2] T7 = T8 a0 a1 a2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check9 : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true → ssum ![a0, a1, a2] T8 = T9 a0 a1 a2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ a0 a1 a2 : Fin 3, reach a0 a1 a2 = true →
    ssum ![a0, a1, a2] T9 + 7 * T4 a0 a1 a2 + 35 * T6 a0 a1 a2 + 21 * T8 a0 a1 a2 = T3 a0 a1 a2 + 21 * T5 a0 a1 a2 + 35 * T7 a0 a1 a2 + 7 * T9 a0 a1 a2 := by
  decide +kernel

lemma vec_eta (A : Fin 3 → Fin 3) : A = ![A 0, A 1, A 2] := by
  ext s
  fin_cases s <;> rfl

/-- Reachable running sums. -/
def R (A : Fin 3 → Fin 3) : Prop := reach (A 0) (A 1) (A 2) = true

lemma R_nxt (A v : Fin 3 → Fin 3) (hA : R A) (hv : colOK A v) : R (nxt A v) := by
  rw [vec_eta A] at hv ⊢
  exact closure _ _ _ hA v hv

lemma W_succ_R (m : ℕ) (A : Fin 3 → Fin 3) (F : Fin 3 → Fin 3 → Fin 3 → ℕ)
    (hF : ∀ B, R B → W m B = F (B 0) (B 1) (B 2)) (hA : R A) :
    W (m + 1) A = ssum A F := by
  rw [W_succ, ssum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · exact hF _ (R_nxt A v hA hv)
  · rfl

lemma W1 (A : Fin 3 → Fin 3) (hA : R A) : W 1 A = T1 (A 0) (A 1) (A 2) := by
  rw [W_succ_R 0 A (fun _ _ _ => 1) (fun B _ => W_zero B) hA, vec_eta A]
  exact check1 _ _ _ hA

lemma W2 (A : Fin 3 → Fin 3) (hA : R A) : W 2 A = T2 (A 0) (A 1) (A 2) := by
  rw [W_succ_R 1 A T1 W1 hA, vec_eta A]
  exact check2 _ _ _ hA

lemma W3 (A : Fin 3 → Fin 3) (hA : R A) : W 3 A = T3 (A 0) (A 1) (A 2) := by
  rw [W_succ_R 2 A T2 W2 hA, vec_eta A]
  exact check3 _ _ _ hA

lemma W4 (A : Fin 3 → Fin 3) (hA : R A) : W 4 A = T4 (A 0) (A 1) (A 2) := by
  rw [W_succ_R 3 A T3 W3 hA, vec_eta A]
  exact check4 _ _ _ hA

lemma W5 (A : Fin 3 → Fin 3) (hA : R A) : W 5 A = T5 (A 0) (A 1) (A 2) := by
  rw [W_succ_R 4 A T4 W4 hA, vec_eta A]
  exact check5 _ _ _ hA

lemma W6 (A : Fin 3 → Fin 3) (hA : R A) : W 6 A = T6 (A 0) (A 1) (A 2) := by
  rw [W_succ_R 5 A T5 W5 hA, vec_eta A]
  exact check6 _ _ _ hA

lemma W7 (A : Fin 3 → Fin 3) (hA : R A) : W 7 A = T7 (A 0) (A 1) (A 2) := by
  rw [W_succ_R 6 A T6 W6 hA, vec_eta A]
  exact check7 _ _ _ hA

lemma W8 (A : Fin 3 → Fin 3) (hA : R A) : W 8 A = T8 (A 0) (A 1) (A 2) := by
  rw [W_succ_R 7 A T7 W7 hA, vec_eta A]
  exact check8 _ _ _ hA

lemma W9 (A : Fin 3 → Fin 3) (hA : R A) : W 9 A = T9 (A 0) (A 1) (A 2) := by
  rw [W_succ_R 8 A T8 W8 hA, vec_eta A]
  exact check9 _ _ _ hA

lemma W_rec (n : ℕ) (A : Fin 3 → Fin 3) (hA : R A) :
    W (n + 10) A + 7 * W (n + 4) A + 35 * W (n + 6) A + 21 * W (n + 8) A = W (n + 3) A + 21 * W (n + 5) A + 35 * W (n + 7) A + 7 * W (n + 9) A := by
  induction n generalizing A with
  | zero =>
    rw [show (0 : ℕ) + 10 = 9 + 1 from rfl, W_succ_R 9 A T9 W9 hA, show (0 : ℕ) + 4 = 4 from rfl, W4 A hA, show (0 : ℕ) + 6 = 6 from rfl, W6 A hA, show (0 : ℕ) + 8 = 8 from rfl, W8 A hA, show (0 : ℕ) + 3 = 3 from rfl, W3 A hA, show (0 : ℕ) + 5 = 5 from rfl, W5 A hA, show (0 : ℕ) + 7 = 7 from rfl, W7 A hA, show (0 : ℕ) + 9 = 9 from rfl, W9 A hA, vec_eta A]
    exact base_check _ _ _ hA
  | succ n ih =>
    rw [W_succ (n + 10), W_succ (n + 4), W_succ (n + 6), W_succ (n + 8), W_succ (n + 3), W_succ (n + 5), W_succ (n + 7), W_succ (n + 9)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : colOK A v
    · simp only [if_pos hv]
      exact ih _ (R_nxt A v hA hv)
    · simp [hv]

lemma R_zero : R 0 := by
  unfold R
  decide +kernel

lemma a_rec (n : ℕ) : a (n + 10) + 7 * a (n + 4) + 35 * a (n + 6) + 21 * a (n + 8) = a (n + 3) + 21 * a (n + 5) + 35 * a (n + 7) + 7 * a (n + 9) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  exact W_rec n 0 R_zero

lemma a_zero : a 0 = 1 := by rw [a_eq, W_zero]
lemma a_1 : a 1 = 4 := by rw [a_eq, W1 0 R_zero]; rfl
lemma a_2 : a 2 = 15 := by rw [a_eq, W2 0 R_zero]; rfl
lemma a_3 : a 3 = 48 := by rw [a_eq, W3 0 R_zero]; rfl
lemma a_4 : a 4 = 118 := by rw [a_eq, W4 0 R_zero]; rfl
lemma a_5 : a 5 = 254 := by rw [a_eq, W5 0 R_zero]; rfl
lemma a_6 : a 6 = 498 := by rw [a_eq, W6 0 R_zero]; rfl
lemma a_7 : a 7 = 916 := by rw [a_eq, W7 0 R_zero]; rfl
lemma a_8 : a 8 = 1605 := by rw [a_eq, W8 0 R_zero]; rfl
lemma a_9 : a 9 = 2702 := by rw [a_eq, W9 0 R_zero]; rfl

lemma a_rec_z (n : ℕ) : (a (n + 10) : ℤ) + 7 * (a (n + 4) : ℤ) + 35 * (a (n + 6) : ℤ) + 21 * (a (n + 8) : ℤ) = (a (n + 3) : ℤ) + 21 * (a (n + 5) : ℤ) + 35 * (a (n + 7) : ℤ) + 7 * (a (n + 9) : ℤ) := by
  exact_mod_cast a_rec n

/-- The recurrence of the entry, for n > 9. -/
theorem recur : ∀ n : ℕ, 9 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 10 := ⟨n - 10, by omega⟩
  have h := a_rec_z j
  simp only [show j + 10 - 1 = j + 9 by omega, show j + 10 - 2 = j + 8 by omega, show j + 10 - 3 = j + 7 by omega, show j + 10 - 4 = j + 6 by omega, show j + 10 - 5 = j + 5 by omega, show j + 10 - 6 = j + 4 by omega, show j + 10 - 7 = j + 3 by omega]
  linear_combination h

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 7 = X * (4 - 13 * X + 27 * X ^ 2 - 43 * X ^ 3 + 51 * X ^ 4 - 41 * X ^ 5 + 27 * X ^ 6 - 16 * X ^ 7 + 6 * X ^ 8) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 7 = A - A * X ^ 1 * C 7 + A * X ^ 2 * C 21 - A * X ^ 3 * C 35 + A * X ^ 4 * C 35 - A * X ^ 5 * C 21 + A * X ^ 6 * C 7 - A * X ^ 7 := by
    rw [show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7, show (C (21 : ℚ) : ℚ⟦X⟧) = 21 from map_ofNat C 21, show (C (35 : ℚ) : ℚ⟦X⟧) = 35 from map_ofNat C 35]
    ring
  have e2 : (X * (4 - 13 * X + 27 * X ^ 2 - 43 * X ^ 3 + 51 * X ^ 4 - 41 * X ^ 5 + 27 * X ^ 6 - 16 * X ^ 7 + 6 * X ^ 8) : ℚ⟦X⟧) = X ^ 1 * C 4 - X ^ 2 * C 13 + X ^ 3 * C 27 - X ^ 4 * C 43 + X ^ 5 * C 51 - X ^ 6 * C 41 + X ^ 7 * C 27 - X ^ 8 * C 16 + X ^ 9 * C 6 := by
    rw [show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6, show (C (13 : ℚ) : ℚ⟦X⟧) = 13 from map_ofNat C 13, show (C (16 : ℚ) : ℚ⟦X⟧) = 16 from map_ofNat C 16, show (C (27 : ℚ) : ℚ⟦X⟧) = 27 from map_ofNat C 27, show (C (41 : ℚ) : ℚ⟦X⟧) = 41 from map_ofNat C 41, show (C (43 : ℚ) : ℚ⟦X⟧) = 43 from map_ofNat C 43, show (C (51 : ℚ) : ℚ⟦X⟧) = 51 from map_ofNat C 51]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
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
  · have hz := a_rec_z (n + 0)
    have hq : (a (n + 0 + 10) : ℚ) + 7 * (a (n + 0 + 4) : ℚ) + 35 * (a (n + 0 + 6) : ℚ) + 21 * (a (n + 0 + 8) : ℚ) = (a (n + 0 + 3) : ℚ) + 21 * (a (n + 0 + 5) : ℚ) + 35 * (a (n + 0 + 7) : ℚ) + 7 * (a (n + 0 + 9) : ℚ) := by
      exact_mod_cast hz
    simp only [show n + 0 + 10 = n + 10 by omega, show n + 0 + 4 = n + 4 by omega, show n + 0 + 6 = n + 6 by omega, show n + 0 + 8 = n + 8 by omega, show n + 0 + 3 = n + 3 by omega, show n + 0 + 5 = n + 5 by omega, show n + 0 + 7 = n + 7 by omega, show n + 0 + 9 = n + 9 by omega] at hq
    simp only [if_false, if_true, show ¬ (n + 10 = 0) by omega,
      show 1 ≤ n + 10 by omega,
      show ¬ (n + 10 - 1 = 0) by omega,
      show n + 10 - 1 = n + 9 by omega,
      show ¬ (n + 9 = 0) by omega,
      show 2 ≤ n + 10 by omega,
      show ¬ (n + 10 - 2 = 0) by omega,
      show n + 10 - 2 = n + 8 by omega,
      show ¬ (n + 8 = 0) by omega,
      show 3 ≤ n + 10 by omega,
      show ¬ (n + 10 - 3 = 0) by omega,
      show n + 10 - 3 = n + 7 by omega,
      show ¬ (n + 7 = 0) by omega,
      show 4 ≤ n + 10 by omega,
      show ¬ (n + 10 - 4 = 0) by omega,
      show n + 10 - 4 = n + 6 by omega,
      show ¬ (n + 6 = 0) by omega,
      show 5 ≤ n + 10 by omega,
      show ¬ (n + 10 - 5 = 0) by omega,
      show n + 10 - 5 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 6 ≤ n + 10 by omega,
      show ¬ (n + 10 - 6 = 0) by omega,
      show n + 10 - 6 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 7 ≤ n + 10 by omega,
      show ¬ (n + 10 - 7 = 0) by omega,
      show n + 10 - 7 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show ¬ (n + 10 = 1) by omega,
      show ¬ (n + 10 = 2) by omega,
      show ¬ (n + 10 = 3) by omega,
      show ¬ (n + 10 = 4) by omega,
      show ¬ (n + 10 = 5) by omega,
      show ¬ (n + 10 = 6) by omega,
      show ¬ (n + 10 = 7) by omega,
      show ¬ (n + 10 = 8) by omega,
      show ¬ (n + 10 = 9) by omega]
    linear_combination hq

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 7 = X * (4 - 13 * X + 27 * X ^ 2 - 43 * X ^ 3 + 51 * X ^ 4 - 41 * X ^ 5 + 27 * X ^ 6 - 16 * X ^ 7 + 6 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a238807

theorem OMA.solution : type_of% @OMA.S_oeis_a238807.main :=
  OMA.S_oeis_a238807.conjecture
