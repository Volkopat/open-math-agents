import OMAStatements.S_oeis_a239031

namespace OMA.S_oeis_a239031

open PowerSeries Finset




lemma sum_Iio {m : ℕ} (j : Fin m) (h : Fin m → ℕ) :
    ∑ x ∈ Iio j, h x = ∑ x, if x < j then h x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

/-- The conditions on one slice v when the running sums along the growing dimension are A. -/
def colOK (A v : Fin 4 → Fin 3) : Prop :=
  ∀ s : Fin 4, (v s).val ≠ ((A s).val) % 3 ∧
    (v s).val ≠ (1 + ∑ s' ∈ Iio s, (v s').val) % 3

instance : DecidableRel colOK := fun A v => by unfold colOK; infer_instance

/-- The running sums after the slice v. -/
def nxt (A v : Fin 4 → Fin 3) : Fin 4 → Fin 3 := fun s => A s + v s

/-- An array of slices is valid when started from the running sums A. -/
def V (A : Fin 4 → Fin 3) {m : ℕ} (g : Fin m → Fin 4 → Fin 3) : Prop :=
  ∀ t : Fin m, ∀ s : Fin 4,
    (g t s).val ≠ (((A s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 3 ∧
    (g t s).val ≠ (1 + ∑ s' ∈ Iio s, (g t s').val) % 3

instance (A : Fin 4 → Fin 3) {m : ℕ} : DecidablePred (@V A m) := fun g => by
  unfold V; infer_instance

lemma V_cons (A : Fin 4 → Fin 3) {m : ℕ} (v : Fin 4 → Fin 3) (g : Fin m → Fin 4 → Fin 3) :
    V A (Fin.cons v g : Fin (m + 1) → Fin 4 → Fin 3) ↔ colOK A v ∧ V (nxt A v) g := by
  have key : ∀ (t : Fin m) (s : Fin 4),
      (((A s).val + ∑ t' ∈ Iio t.succ, ((Fin.cons v g : Fin (m + 1) → Fin 4 → Fin 3) t' s).val)) % 3 =
      (((nxt A v s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 3 := by
    intro t s
    rw [sum_Iio, sum_Iio, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff, nxt,
      Fin.val_add]
    omega
  have key0 : ∀ s : Fin 4,
      (((A s).val + ∑ t' ∈ Iio (0 : Fin (m + 1)), ((Fin.cons v g : Fin (m + 1) → Fin 4 → Fin 3) t' s).val)) % 3 =
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
def W (m : ℕ) (A : Fin 4 → Fin 3) : ℕ :=
  ((univ : Finset (Fin m → Fin 4 → Fin 3)).filter (V A)).card

lemma W_zero (A : Fin 4 → Fin 3) : W 0 A = 1 := by
  have e : (univ : Finset (Fin 0 → Fin 4 → Fin 3)).filter (V A) = univ :=
    Finset.filter_true_of_mem (fun g _ t => Fin.elim0 t)
  rw [W, e]
  simp

lemma W_succ (m : ℕ) (A : Fin 4 → Fin 3) :
    W (m + 1) A = ∑ v : Fin 4 → Fin 3, if colOK A v then W m (nxt A v) else 0 := by
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

/-- The sum, over the slices allowed after the running sums A, of F at the next running sums. -/
def ssum (A : Fin 4 → Fin 3) (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ) : ℕ :=
  ∑ v : Fin 4 → Fin 3, if colOK A v then F (nxt A v 0) (nxt A v 1) (nxt A v 2) (nxt A v 3) else 0

/-- The reachable running sums. -/
def reach : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Bool :=
  ![![![![true, false, false], ![false, false, false], ![false, false, false]],
      ![![false, false, false], ![false, false, false], ![false, false, false]],
      ![![false, false, false], ![false, false, false], ![false, false, false]]],
    ![![![false, false, false], ![false, false, false], ![false, false, false]],
      ![![false, false, false], ![false, false, false], ![false, false, false]],
      ![![false, false, false], ![false, false, false], ![false, false, false]]],
    ![![![true, true, true], ![false, false, false], ![false, false, false]],
      ![![false, false, false], ![false, false, false], ![true, true, true]],
      ![![true, true, true], ![true, true, true], ![true, true, true]]]]

def T1 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![4, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]],
    ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]],
    ![![![2, 3, 3], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![2, 4, 2]],
      ![![2, 1, 1], ![3, 3, 2], ![1, 2, 1]]]]

def T2 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![11, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]],
    ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]],
    ![![![4, 8, 4], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![5, 11, 5]],
      ![![3, 1, 1], ![4, 8, 4], ![1, 3, 1]]]]

def T3 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![28, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]],
    ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]],
    ![![![7, 15, 6], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![9, 28, 9]],
      ![![4, 1, 1], ![6, 15, 7], ![1, 4, 1]]]]

def T4 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![59, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]],
    ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]],
    ![![![11, 25, 9], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![15, 59, 15]],
      ![![5, 1, 1], ![9, 25, 11], ![1, 5, 1]]]]

def T5 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![![![![110, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]],
    ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]],
    ![![![16, 39, 13], ![0, 0, 0], ![0, 0, 0]],
      ![![0, 0, 0], ![0, 0, 0], ![24, 110, 24]],
      ![![6, 1, 1], ![13, 39, 16], ![1, 6, 1]]]]

set_option maxHeartbeats 4000000 in
lemma closure : ∀ a0 a1 a2 a3 : Fin 3, reach a0 a1 a2 a3 = true → ∀ v : Fin 4 → Fin 3, colOK ![a0, a1, a2, a3] v →
    reach (nxt ![a0, a1, a2, a3] v 0) (nxt ![a0, a1, a2, a3] v 1) (nxt ![a0, a1, a2, a3] v 2) (nxt ![a0, a1, a2, a3] v 3) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check1 : ∀ a0 a1 a2 a3 : Fin 3, reach a0 a1 a2 a3 = true → ssum ![a0, a1, a2, a3] (fun _ _ _ _ => 1) = T1 a0 a1 a2 a3 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check2 : ∀ a0 a1 a2 a3 : Fin 3, reach a0 a1 a2 a3 = true → ssum ![a0, a1, a2, a3] T1 = T2 a0 a1 a2 a3 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check3 : ∀ a0 a1 a2 a3 : Fin 3, reach a0 a1 a2 a3 = true → ssum ![a0, a1, a2, a3] T2 = T3 a0 a1 a2 a3 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check4 : ∀ a0 a1 a2 a3 : Fin 3, reach a0 a1 a2 a3 = true → ssum ![a0, a1, a2, a3] T3 = T4 a0 a1 a2 a3 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check5 : ∀ a0 a1 a2 a3 : Fin 3, reach a0 a1 a2 a3 = true → ssum ![a0, a1, a2, a3] T4 = T5 a0 a1 a2 a3 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ a0 a1 a2 a3 : Fin 3, reach a0 a1 a2 a3 = true →
    ssum ![a0, a1, a2, a3] T5 + 5 * T2 a0 a1 a2 a3 + 10 * T4 a0 a1 a2 a3 = T1 a0 a1 a2 a3 + 10 * T3 a0 a1 a2 a3 + 5 * T5 a0 a1 a2 a3 := by
  decide +kernel

lemma vec_eta (A : Fin 4 → Fin 3) : A = ![A 0, A 1, A 2, A 3] := by
  ext s
  fin_cases s <;> rfl

/-- Reachable running sums. -/
def R (A : Fin 4 → Fin 3) : Prop := reach (A 0) (A 1) (A 2) (A 3) = true

lemma R_nxt (A v : Fin 4 → Fin 3) (hA : R A) (hv : colOK A v) : R (nxt A v) := by
  rw [vec_eta A] at hv ⊢
  exact closure _ _ _ _ hA v hv

lemma W_succ_R (m : ℕ) (A : Fin 4 → Fin 3) (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ)
    (hF : ∀ B, R B → W m B = F (B 0) (B 1) (B 2) (B 3)) (hA : R A) :
    W (m + 1) A = ssum A F := by
  rw [W_succ, ssum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · exact hF _ (R_nxt A v hA hv)
  · rfl

lemma W1 (A : Fin 4 → Fin 3) (hA : R A) : W 1 A = T1 (A 0) (A 1) (A 2) (A 3) := by
  rw [W_succ_R 0 A (fun _ _ _ _ => 1) (fun B _ => W_zero B) hA, vec_eta A]
  exact check1 _ _ _ _ hA

lemma W2 (A : Fin 4 → Fin 3) (hA : R A) : W 2 A = T2 (A 0) (A 1) (A 2) (A 3) := by
  rw [W_succ_R 1 A T1 W1 hA, vec_eta A]
  exact check2 _ _ _ _ hA

lemma W3 (A : Fin 4 → Fin 3) (hA : R A) : W 3 A = T3 (A 0) (A 1) (A 2) (A 3) := by
  rw [W_succ_R 2 A T2 W2 hA, vec_eta A]
  exact check3 _ _ _ _ hA

lemma W4 (A : Fin 4 → Fin 3) (hA : R A) : W 4 A = T4 (A 0) (A 1) (A 2) (A 3) := by
  rw [W_succ_R 3 A T3 W3 hA, vec_eta A]
  exact check4 _ _ _ _ hA

lemma W5 (A : Fin 4 → Fin 3) (hA : R A) : W 5 A = T5 (A 0) (A 1) (A 2) (A 3) := by
  rw [W_succ_R 4 A T4 W4 hA, vec_eta A]
  exact check5 _ _ _ _ hA

lemma W_rec (n : ℕ) (A : Fin 4 → Fin 3) (hA : R A) :
    W (n + 6) A + 5 * W (n + 2) A + 10 * W (n + 4) A = W (n + 1) A + 10 * W (n + 3) A + 5 * W (n + 5) A := by
  induction n generalizing A with
  | zero =>
    rw [show (0 : ℕ) + 6 = 5 + 1 from rfl, W_succ_R 5 A T5 W5 hA, show (0 : ℕ) + 2 = 2 from rfl, W2 A hA, show (0 : ℕ) + 4 = 4 from rfl, W4 A hA, show (0 : ℕ) + 1 = 1 from rfl, W1 A hA, show (0 : ℕ) + 3 = 3 from rfl, W3 A hA, show (0 : ℕ) + 5 = 5 from rfl, W5 A hA, vec_eta A]
    exact base_check _ _ _ _ hA
  | succ n ih =>
    rw [W_succ (n + 6), W_succ (n + 2), W_succ (n + 4), W_succ (n + 1), W_succ (n + 3), W_succ (n + 5)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : colOK A v
    · simp only [if_pos hv]
      exact ih _ (R_nxt A v hA hv)
    · simp [hv]

lemma R_zero : R 0 := by
  unfold R
  decide +kernel

lemma a_rec (n : ℕ) : a (n + 6) + 5 * a (n + 2) + 10 * a (n + 4) = a (n + 1) + 10 * a (n + 3) + 5 * a (n + 5) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  exact W_rec n 0 R_zero

lemma a_zero : a 0 = 1 := by rw [a_eq, W_zero]
lemma a_1 : a 1 = 4 := by rw [a_eq, W1 0 R_zero]; rfl
lemma a_2 : a 2 = 11 := by rw [a_eq, W2 0 R_zero]; rfl
lemma a_3 : a 3 = 28 := by rw [a_eq, W3 0 R_zero]; rfl
lemma a_4 : a 4 = 59 := by rw [a_eq, W4 0 R_zero]; rfl
lemma a_5 : a 5 = 110 := by rw [a_eq, W5 0 R_zero]; rfl

lemma a_rec_z (n : ℕ) : (a (n + 6) : ℤ) + 5 * (a (n + 2) : ℤ) + 10 * (a (n + 4) : ℤ) = (a (n + 1) : ℤ) + 10 * (a (n + 3) : ℤ) + 5 * (a (n + 5) : ℤ) := by
  exact_mod_cast a_rec n

/-- The recurrence of the entry, for n > 5. -/
theorem recur : ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  have h := a_rec_z j
  simp only [show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega]
  linear_combination h

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 5 = X * (4 - 9 * X + 13 * X ^ 2 - 11 * X ^ 3 + 5 * X ^ 4) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 5 = A - A * X ^ 1 * C 5 + A * X ^ 2 * C 10 - A * X ^ 3 * C 10 + A * X ^ 4 * C 5 - A * X ^ 5 := by
    rw [show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (10 : ℚ) : ℚ⟦X⟧) = 10 from map_ofNat C 10]
    ring
  have e2 : (X * (4 - 9 * X + 13 * X ^ 2 - 11 * X ^ 3 + 5 * X ^ 4) : ℚ⟦X⟧) = X ^ 1 * C 4 - X ^ 2 * C 9 + X ^ 3 * C 13 - X ^ 4 * C 11 + X ^ 5 * C 5 := by
    rw [show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9, show (C (11 : ℚ) : ℚ⟦X⟧) = 11 from map_ofNat C 11, show (C (13 : ℚ) : ℚ⟦X⟧) = 13 from map_ofNat C 13]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_1] <;> norm_num
  · simp [a_1, a_2] <;> norm_num
  · simp [a_1, a_2, a_3] <;> norm_num
  · simp [a_1, a_2, a_3, a_4] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5] <;> norm_num
  · have hz := a_rec_z (n + 0)
    have hq : (a (n + 0 + 6) : ℚ) + 5 * (a (n + 0 + 2) : ℚ) + 10 * (a (n + 0 + 4) : ℚ) = (a (n + 0 + 1) : ℚ) + 10 * (a (n + 0 + 3) : ℚ) + 5 * (a (n + 0 + 5) : ℚ) := by
      exact_mod_cast hz
    simp only [show n + 0 + 6 = n + 6 by omega, show n + 0 + 2 = n + 2 by omega, show n + 0 + 4 = n + 4 by omega, show n + 0 + 1 = n + 1 by omega, show n + 0 + 3 = n + 3 by omega, show n + 0 + 5 = n + 5 by omega] at hq
    simp only [if_false, if_true, show ¬ (n + 6 = 0) by omega,
      show 1 ≤ n + 6 by omega,
      show ¬ (n + 6 - 1 = 0) by omega,
      show n + 6 - 1 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 2 ≤ n + 6 by omega,
      show ¬ (n + 6 - 2 = 0) by omega,
      show n + 6 - 2 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 3 ≤ n + 6 by omega,
      show ¬ (n + 6 - 3 = 0) by omega,
      show n + 6 - 3 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 4 ≤ n + 6 by omega,
      show ¬ (n + 6 - 4 = 0) by omega,
      show n + 6 - 4 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show 5 ≤ n + 6 by omega,
      show ¬ (n + 6 - 5 = 0) by omega,
      show n + 6 - 5 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 6 = 1) by omega,
      show ¬ (n + 6 = 2) by omega,
      show ¬ (n + 6 = 3) by omega,
      show ¬ (n + 6 = 4) by omega,
      show ¬ (n + 6 = 5) by omega]
    linear_combination hq

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 5 = X * (4 - 9 * X + 13 * X ^ 2 - 11 * X ^ 3 + 5 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a239031

theorem OMA.solution : type_of% @OMA.S_oeis_a239031.main :=
  OMA.S_oeis_a239031.conjecture
