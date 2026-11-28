import OMAStatements.S_oeis_a239024

namespace OMA.S_oeis_a239024

open PowerSeries Finset




/-! ### Slices and running sums -/

lemma sum_Iio {m : ℕ} (j : Fin m) (h : Fin m → ℕ) :
    ∑ x ∈ Iio j, h x = ∑ x, if x < j then h x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

/-- The conditions on one slice v (a row) when the running sums along the other direction are A. -/
def colOK (A v : Fin 2 → Fin 3) : Prop :=
  ∀ s : Fin 2, (v s).val ≠ (1 + (A s).val) % 3 ∧ (v s).val ≠ (∑ s' ∈ Iio s, (v s').val) % 3

instance : DecidableRel colOK := fun A v => by unfold colOK; infer_instance

/-- The running sums after the slice v. -/
def nxt (A v : Fin 2 → Fin 3) : Fin 2 → Fin 3 := fun s => A s + v s

/-- An array of slices is valid when started from the running sums A. -/
def V (A : Fin 2 → Fin 3) {m : ℕ} (g : Fin m → Fin 2 → Fin 3) : Prop :=
  ∀ t : Fin m, ∀ s : Fin 2,
    (g t s).val ≠ (1 + ((A s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 3 ∧
    (g t s).val ≠ (∑ s' ∈ Iio s, (g t s').val) % 3

instance (A : Fin 2 → Fin 3) {m : ℕ} : DecidablePred (@V A m) := fun g => by
  unfold V; infer_instance

lemma V_cons (A : Fin 2 → Fin 3) {m : ℕ} (v : Fin 2 → Fin 3) (g : Fin m → Fin 2 → Fin 3) :
    V A (Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 3) ↔ colOK A v ∧ V (nxt A v) g := by
  have key : ∀ (t : Fin m) (s : Fin 2),
      (1 + ((A s).val + ∑ t' ∈ Iio t.succ,
        ((Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 3) t' s).val)) % 3 =
      (1 + ((nxt A v s).val + ∑ t' ∈ Iio t, (g t' s).val)) % 3 := by
    intro t s
    rw [sum_Iio, sum_Iio, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff, nxt,
      Fin.val_add]
    omega
  have key0 : ∀ s : Fin 2,
      (1 + ((A s).val + ∑ t' ∈ Iio (0 : Fin (m + 1)),
        ((Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 3) t' s).val)) % 3 = (1 + (A s).val) % 3 := by
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
def W (m : ℕ) (A : Fin 2 → Fin 3) : ℕ :=
  ((univ : Finset (Fin m → Fin 2 → Fin 3)).filter (V A)).card

lemma W_zero (A : Fin 2 → Fin 3) : W 0 A = 1 := by
  have e : (univ : Finset (Fin 0 → Fin 2 → Fin 3)).filter (V A) = univ :=
    Finset.filter_true_of_mem (fun g _ t => Fin.elim0 t)
  rw [W, e]
  simp

lemma W_succ (m : ℕ) (A : Fin 2 → Fin 3) :
    W (m + 1) A = ∑ v : Fin 2 → Fin 3, if colOK A v then W m (nxt A v) else 0 := by
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

/-! ### The per-state relation, by kernel computation on tables -/

/-- The sum, over the slices allowed after the running sums A, of F at the next running sums. -/
def ssum (A : Fin 2 → Fin 3) (F : Fin 3 → Fin 3 → ℕ) : ℕ :=
  ∑ v : Fin 2 → Fin 3, if colOK A v then F (nxt A v 0) (nxt A v 1) else 0

/-- The reachable running sums. -/
def reach : Fin 3 → Fin 3 → Bool := ![![true, true, true], ![true, true, true], ![true, true, true]]

def T1 : Fin 3 → Fin 3 → ℕ := ![![1, 2, 1], ![2, 1, 1], ![3, 3, 2]]
def T2 : Fin 3 → Fin 3 → ℕ := ![![3, 5, 3], ![5, 3, 3], ![4, 4, 4]]
def T3 : Fin 3 → Fin 3 → ℕ := ![![4, 8, 4], ![8, 4, 4], ![11, 11, 10]]

set_option maxHeartbeats 4000000 in
lemma closure : ∀ a0 a1 : Fin 3, reach a0 a1 = true → ∀ v : Fin 2 → Fin 3, colOK ![a0, a1] v →
    reach (nxt ![a0, a1] v 0) (nxt ![a0, a1] v 1) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check1 : ∀ a0 a1 : Fin 3, reach a0 a1 = true → ssum ![a0, a1] (fun _ _ => 1) = T1 a0 a1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check2 : ∀ a0 a1 : Fin 3, reach a0 a1 = true → ssum ![a0, a1] T1 = T2 a0 a1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma check3 : ∀ a0 a1 : Fin 3, reach a0 a1 = true → ssum ![a0, a1] T2 = T3 a0 a1 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ a0 a1 : Fin 3, reach a0 a1 = true →
    ssum ![a0, a1] T3 + 4 * 1 = 5 * T2 a0 a1 := by
  decide +kernel

lemma vec_eta (A : Fin 2 → Fin 3) : A = ![A 0, A 1] := by
  ext s
  fin_cases s <;> rfl

/-- Reachable running sums. -/
def R (A : Fin 2 → Fin 3) : Prop := reach (A 0) (A 1) = true

lemma R_nxt (A v : Fin 2 → Fin 3) (hA : R A) (hv : colOK A v) : R (nxt A v) := by
  rw [vec_eta A] at hv ⊢
  exact closure _ _ hA v hv

lemma W_succ_R (m : ℕ) (A : Fin 2 → Fin 3) (F : Fin 3 → Fin 3 → ℕ)
    (hF : ∀ B, R B → W m B = F (B 0) (B 1)) (hA : R A) : W (m + 1) A = ssum A F := by
  rw [W_succ, ssum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · exact hF _ (R_nxt A v hA hv)
  · rfl

lemma W1 (A : Fin 2 → Fin 3) (hA : R A) : W 1 A = T1 (A 0) (A 1) := by
  rw [W_succ_R 0 A (fun _ _ => 1) (fun B _ => W_zero B) hA, vec_eta A]
  exact check1 _ _ hA

lemma W2 (A : Fin 2 → Fin 3) (hA : R A) : W 2 A = T2 (A 0) (A 1) := by
  rw [W_succ_R 1 A T1 W1 hA, vec_eta A]
  exact check2 _ _ hA

lemma W3 (A : Fin 2 → Fin 3) (hA : R A) : W 3 A = T3 (A 0) (A 1) := by
  rw [W_succ_R 2 A T2 W2 hA, vec_eta A]
  exact check3 _ _ hA

lemma W_rec (n : ℕ) (A : Fin 2 → Fin 3) (hA : R A) :
    W (n + 4) A + 4 * W n A = 5 * W (n + 2) A := by
  induction n generalizing A with
  | zero =>
    rw [show (0 : ℕ) + 4 = 3 + 1 from rfl, W_succ_R 3 A T3 W3 hA, W_zero,
      show (0 : ℕ) + 2 = 2 from rfl, W2 A hA, vec_eta A]
    exact base_check _ _ hA
  | succ n ih =>
    rw [W_succ (n + 4), W_succ n, W_succ (n + 2), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : colOK A v
    · simp only [if_pos hv]
      exact ih _ (R_nxt A v hA hv)
    · simp [hv]

lemma R_zero : R 0 := by
  unfold R
  decide +kernel

lemma a_rec (n : ℕ) : a (n + 4) + 4 * a n = 5 * a (n + 2) := by
  rw [a_eq, a_eq, a_eq]
  exact W_rec n 0 R_zero

lemma a_zero : a 0 = 1 := by rw [a_eq, W_zero]
lemma a_one : a 1 = 1 := by rw [a_eq, W1 0 R_zero]; rfl
lemma a_two : a 2 = 3 := by rw [a_eq, W2 0 R_zero]; rfl
lemma a_three : a 3 = 4 := by rw [a_eq, W3 0 R_zero]; rfl

lemma a_rec_q (n : ℕ) : (a (n + 4) : ℚ) = 5 * a (n + 2) - 4 * a n := by
  have h := a_rec n
  have hz : ((a (n + 4) : ℕ) : ℚ) + 4 * a n = 5 * a (n + 2) := by exact_mod_cast h
  linarith

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) = (2 + (-2) ^ n + 2 * (-1) ^ n + 7 * 2 ^ n) / 12 := by
  have key : ∀ n, (a n : ℚ) = (2 + (-2) ^ n + 2 * (-1) ^ n + 7 * 2 ^ n) / 12 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | _ | _ | n
      · rw [a_zero]; norm_num
      · rw [a_one]; norm_num
      · rw [a_two]; norm_num
      · rw [a_three]; norm_num
      · show (a (n + 4) : ℚ) = _
        rw [a_rec_q, ih (n + 2) (by omega), ih n (by omega)]
        ring
  exact fun n _ => key n

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(1 + 3x - x^2 - 4x^3)/((1 - x)(1 + x)(1 - 2x)(1 + 2x)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) = X * (1 + 3 * X - X ^ 2 - 4 * X ^ 3) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      A - A * X ^ 2 * C 5 + A * X ^ 4 * C 4 := by
    rw [show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4]
    ring
  have e2 : (X * (1 + 3 * X - X ^ 2 - 4 * X ^ 3) : ℚ⟦X⟧) =
      X ^ 1 + X ^ 2 * C 3 - X ^ 3 - X ^ 4 * C 4 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | n
  · simp
  · simp [a_one]
  · simp [a_one, a_two]
  · simp [a_one, a_two, a_three] <;> norm_num
  · have h4 : a 4 = 11 := by
      have := a_rec 0
      simp only [Nat.zero_add, a_zero, a_two] at this
      omega
    simp [a_one, a_two, a_three, h4] <;> norm_num
  · have hq := a_rec_q (n + 1)
    simp only [if_false, if_true, show ¬ (n + 5 = 0) by omega, show 2 ≤ n + 5 by omega,
      show 4 ≤ n + 5 by omega, show n + 5 - 2 = n + 3 by omega, show n + 5 - 4 = n + 1 by omega,
      show ¬ (n + 3 = 0) by omega, show ¬ (n + 1 = 0) by omega, show ¬ (n + 5 = 1) by omega,
      show ¬ (n + 5 = 2) by omega, show ¬ (n + 5 = 3) by omega, show ¬ (n + 5 = 4) by omega]
    rw [show n + 1 + 4 = n + 5 by ring, show n + 1 + 2 = n + 3 by ring] at hq
    linear_combination hq

theorem conjecture : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) = X * (1 + 3 * X - X ^ 2 - 4 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2 + (-2) ^ n + 2 * (-1) ^ n + 7 * 2 ^ n) / 12 :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a239024

theorem OMA.solution : type_of% @OMA.S_oeis_a239024.main :=
  OMA.S_oeis_a239024.conjecture
