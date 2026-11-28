import OMAStatements.S_oeis_a126502

-- Credit: @Dariusthedoggie
-- Proof: 7-state transfer matrix recurrence and g.f. bridged to upstream List.IsChain encoding.

namespace OMA.P126502

open PowerSeries

/-- Two base-7 digits differ by at most 4. -/
def adjOk (x y : Fin 7) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 4

instance (x y : Fin 7) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A word of length `n` over `Fin 7` has all adjacent digits differing by at most 4. -/
def isValid (n : ℕ) (w : Fin n → Fin 7) : Prop :=
  ∀ i : Fin (n - 1), adjOk (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)

instance (n : ℕ) (w : Fin n → Fin 7) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A126502: the number of base 7 n-digit numbers with adjacent digits differing by 4 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card


open OMA.S_oeis_a126502 PowerSeries

abbrev Digit := Fin 7

def step (f : Digit → ℕ) (r : Digit) : ℕ :=
  ∑ s : Digit, if adjOk r s then f s else 0

def v : ℕ → Digit → ℕ
  | 0, _ => 1
  | m + 1, r => step (v m) r

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Digit) → ℕ) :
    ∑ w, f w = ∑ r : Digit, ∑ y : Fin (m + 1) → Digit, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Digit)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Digit) → ℕ) :
    ∑ y, g y = ∑ s : Digit, ∑ y : Fin (m + 1) → Digit, if y 0 = s then g y else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq]
  simp

lemma isValid_cons (m : ℕ) (r : Digit) (y : Fin (m + 1) → Digit) :
    isValid (m + 2) (Fin.cons r y) ↔ adjOk r (y 0) ∧ isValid (m + 1) y := by
  have hcs : ∀ (k : ℕ) (hk : k + 1 < m + 2),
      (Fin.cons r y : Fin (m + 2) → Digit) ⟨k + 1, hk⟩ = y ⟨k, by omega⟩ :=
    fun k hk => Fin.cons_succ (α := fun _ => Digit) r y ⟨k, by omega⟩
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h ⟨0, by omega⟩
      simpa [hcs] using h0
    · intro j
      have hj := h ⟨j.val + 1, by omega⟩
      rw [hcs, hcs] at hj
      exact hj
  · rintro ⟨h0, hy⟩ i
    rcases i with ⟨k, hk⟩
    cases k with
    | zero => simpa [hcs] using h0
    | succ k' =>
      rw [hcs, hcs]
      exact hy ⟨k', by omega⟩

def N (m : ℕ) (r : Digit) : ℕ :=
  ∑ w : Fin (m + 1) → Digit, if w 0 = r ∧ isValid (m + 1) w then 1 else 0

lemma N_zero (r : Digit) : N 0 r = 1 := by
  unfold N
  have hv : ∀ w : Fin 1 → Digit, isValid 1 w := fun _ i => Fin.elim0 i
  simp only [hv, and_true]
  rw [← (Equiv.funUnique (Fin 1) Digit).symm.sum_comp]
  simp

lemma N_succ (m : ℕ) (r : Digit) : N (m + 1) r = step (N m) r := by
  unfold N step
  rw [sum_cons]
  simp only [Fin.cons_zero]
  rw [Finset.sum_eq_single r (by intro b _ hb; simp [hb]) (by simp)]
  simp only [true_and, isValid_cons]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : adjOk r s
  · rw [if_pos hs]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y 0 = s <;> simp [hy, hs]
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y 0 = s <;> simp [hy, hs]

lemma N_eq_v (m : ℕ) (r : Digit) : N m r = v m r := by
  induction m generalizing r with
  | zero => exact N_zero r
  | succ m ih =>
    rw [N_succ, v]
    unfold step
    apply Finset.sum_congr rfl
    intro s _
    rw [ih s]

lemma a_zero : a 0 = 1 := by
  unfold a
  rw [Finset.card_filter]
  have hv : ∀ w : Fin 0 → Digit, isValid 0 w := fun _ i => Fin.elim0 i
  simp [hv]

lemma a_succ (m : ℕ) : a (m + 1) = ∑ r : Digit, v m r := by
  unfold a
  rw [Finset.card_filter, fiber]
  apply Finset.sum_congr rfl
  intro r _
  rw [← N_eq_v]
  unfold N
  apply Finset.sum_congr rfl
  intro y _
  rw [ite_and]

def err (m : ℕ) (r : Digit) : ℤ :=
  (v (m + 3) r : ℤ) - 6 * (v (m + 2) r : ℤ) - 2 * (v (m + 1) r : ℤ) + 3 * (v m r : ℤ)

lemma err_zero : ∀ r : Digit, err 0 r = 0 := by decide

lemma err_succ (m : ℕ) (r : Digit) :
    err (m + 1) r = ∑ s : Digit, if adjOk r s then err m s else 0 := by
  unfold err
  simp only [v, step, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> ring

lemma err_eq_zero (m : ℕ) (r : Digit) : err m r = 0 := by
  induction m generalizing r with
  | zero => exact err_zero r
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun s _ => by simp [ih s])

lemma a_rec_ge4 (m : ℕ) :
    (a (m + 4) : ℤ) = 6 * a (m + 3) + 2 * a (m + 2) - 3 * a (m + 1) := by
  have h : ∑ r : Digit, err m r = 0 := Finset.sum_eq_zero (fun r _ => err_eq_zero m r)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  simp only [a_succ, Nat.cast_sum]
  linarith

lemma a_1 : a 1 = 7 := by rw [a_succ]; decide
lemma a_2 : a 2 = 43 := by rw [a_succ]; decide
lemma a_3 : a 3 = 269 := by rw [a_succ]; decide

theorem main_proof_ours :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X - 2 * X ^ 2 + 3 * X ^ 3) =
      1 + X - X ^ 2) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 6 * a (n - 1) + 2 * a (n - 2) - 3 * a (n - 3)) := by
  have hrec : ∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 6 * a (n - 1) + 2 * a (n - 2) - 3 * a (n - 3) := by
    intro n hn
    rcases eq_or_lt_of_le hn with rfl | hlt
    · simp [a_zero, a_1, a_2, a_3]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      simpa using a_rec_ge4 m
  refine ⟨?_, hrec⟩
  have hl : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X - 2 * X ^ 2 + 3 * X ^ 3) =
      PowerSeries.mk (fun n => (a n : ℚ)) -
        C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) -
        C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) +
        C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
    simp only [map_ofNat]; ring
  have hr : (1 : PowerSeries ℚ) + X - X ^ 2 =
      C (1 : ℚ) + C (1 : ℚ) * X ^ 1 - C (1 : ℚ) * X ^ 2 := by
    simp only [map_one, pow_one, one_mul]
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [a_zero, a_1, a_2] <;> norm_num
  · have hq : (a n : ℚ) = 6 * a (n - 1) + 2 * a (n - 2) - 3 * a (n - 3) := by
      exact_mod_cast hrec n hn
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have e0 : n ≠ 0 := by omega
    have e1 : n - 1 ≠ 0 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    simp only [c1, c2, c3, e0, e1, e2, coeff_C, if_true, if_false]
    rw [hq]; ring


lemma valid_iff (n : ℕ) (w : Fin n → Fin 7) :
    (List.ofFn w).IsChain OMA.S_oeis_a126502.near ↔ isValid n w := by
  rw [List.isChain_ofFn]
  constructor
  · intro h i
    have := h i.val (by omega)
    unfold OMA.S_oeis_a126502.near at this
    unfold adjOk
    rw [Int.abs_eq_natAbs] at this
    omega
  · intro h i hi
    have := h ⟨i, by omega⟩
    unfold OMA.S_oeis_a126502.near
    unfold adjOk at this
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this

lemma a_eq (n : ℕ) : OMA.S_oeis_a126502.a n = a n := by
  unfold OMA.S_oeis_a126502.a a
  congr 1
  apply Finset.filter_congr
  intro w _
  exact valid_iff n w

theorem main_proof : type_of% @OMA.S_oeis_a126502.main := by
  obtain ⟨h1, h2⟩ := main_proof_ours
  simp only [a_eq]
  exact ⟨h1, fun n hn => h2 n hn⟩

end OMA.P126502

theorem OMA.solution : type_of% @OMA.S_oeis_a126502.main := OMA.P126502.main_proof
