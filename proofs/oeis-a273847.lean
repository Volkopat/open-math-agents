import OMAStatements.S_oeis_a273847

namespace OMA.S_oeis_a273847

open PowerSeries






/-- Barker's conjectures. -/
def Conjecture : Prop :=
  (∀ n : ℕ, 4 < n → a n = (1 + 2 * n) ^ 2) ∧
  (∀ n : ℕ, 7 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
  A = (1 + X + 12 * X ^ 2 - 7 * X ^ 3 + 7 * X ^ 5 - 11 * X ^ 6 + 5 * X ^ 7) * ((1 - X) ^ 3)⁻¹

def s0 : ℤ × ℤ → Bool := fun p => decide (p.1 = 0 ∧ p.2 = 0)
/-- ON except the origin and its four neighbors. -/
def s1 : ℤ × ℤ → Bool := fun p =>
  decide (¬((p.1 = 0 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1) ∨ (p.2 = 0 ∧ -1 ≤ p.1 ∧ p.1 ≤ 1)))
/-- ON except the four diagonal neighbors. -/
def s2 : ℤ × ℤ → Bool := fun p =>
  decide (¬((p.1 = 1 ∨ p.1 = -1) ∧ (p.2 = 1 ∨ p.2 = -1)))
/-- ON except the four neighbors. -/
def s3 : ℤ × ℤ → Bool := fun p =>
  decide (¬((p.1 = 0 ∧ (p.2 = 1 ∨ p.2 = -1)) ∨ (p.2 = 0 ∧ (p.1 = 1 ∨ p.1 = -1))))
/-- ON except the four diagonal neighbors and the origin. -/
def s4 : ℤ × ℤ → Bool := fun p =>
  decide (¬(((p.1 = 1 ∨ p.1 = -1) ∧ (p.2 = 1 ∨ p.2 = -1)) ∨ (p.1 = 0 ∧ p.2 = 0)))
/-- Every cell ON. -/
def s5 : ℤ × ℤ → Bool := fun _ => true

/-- A step from `s` (ON outside the 3 x 3 box) to `t` (ON outside the 5 x 5 box) holds
everywhere once it holds on the 5 x 5 box. -/
theorem step_eq {s t : ℤ × ℤ → Bool}
    (hbox : ∀ i j : Fin 5, step 969 s ((i : ℤ) - 2, (j : ℤ) - 2) = t ((i : ℤ) - 2, (j : ℤ) - 2))
    (hs : ∀ x y : ℤ, ¬(-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1) → s (x, y) = true)
    (ht : ∀ x y : ℤ, ¬(-2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2) → t (x, y) = true) :
    step 969 s = t := by
  funext ⟨x, y⟩
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨h1, h2, h3, h4⟩ := h
    have := hbox ⟨(x + 2).toNat, by omega⟩ ⟨(y + 2).toNat, by omega⟩
    simp only at this
    rwa [show (((x + 2).toNat : ℕ) : ℤ) - 2 = x by omega,
      show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by omega] at this
  · simp only [step]
    rw [hs x y (by omega), hs (x - 1) y (by omega), hs (x + 1) y (by omega),
      hs x (y - 1) (by omega), hs x (y + 1) (by omega), ht x y h]
    decide

/-- The same with `s` OFF outside the 3 x 3 box (used for the first step). -/
theorem step_eq0 {s t : ℤ × ℤ → Bool}
    (hbox : ∀ i j : Fin 5, step 969 s ((i : ℤ) - 2, (j : ℤ) - 2) = t ((i : ℤ) - 2, (j : ℤ) - 2))
    (hs : ∀ x y : ℤ, ¬(-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1) → s (x, y) = false)
    (ht : ∀ x y : ℤ, ¬(-2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2) → t (x, y) = true) :
    step 969 s = t := by
  funext ⟨x, y⟩
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨h1, h2, h3, h4⟩ := h
    have := hbox ⟨(x + 2).toNat, by omega⟩ ⟨(y + 2).toNat, by omega⟩
    simp only at this
    rwa [show (((x + 2).toNat : ℕ) : ℤ) - 2 = x by omega,
      show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by omega] at this
  · simp only [step]
    rw [hs x y (by omega), hs (x - 1) y (by omega), hs (x + 1) y (by omega),
      hs x (y - 1) (by omega), hs x (y + 1) (by omega), ht x y h]
    decide

theorem step01 : step 969 s0 = s1 :=
  step_eq0 (by decide +kernel) (fun x y h => by simp only [s0]; exact decide_eq_false (by omega))
    (fun x y h => by simp only [s1]; exact decide_eq_true (by omega))

theorem step12 : step 969 s1 = s2 :=
  step_eq (by decide +kernel) (fun x y h => by simp only [s1]; exact decide_eq_true (by omega))
    (fun x y h => by simp only [s2]; exact decide_eq_true (by omega))

theorem step23 : step 969 s2 = s3 :=
  step_eq (by decide +kernel) (fun x y h => by simp only [s2]; exact decide_eq_true (by omega))
    (fun x y h => by simp only [s3]; exact decide_eq_true (by omega))

theorem step34 : step 969 s3 = s4 :=
  step_eq (by decide +kernel) (fun x y h => by simp only [s3]; exact decide_eq_true (by omega))
    (fun x y h => by simp only [s4]; exact decide_eq_true (by omega))

theorem step45 : step 969 s4 = s5 :=
  step_eq (by decide +kernel) (fun x y h => by simp only [s4]; exact decide_eq_true (by omega))
    (fun x y h => rfl)

theorem step55 : step 969 s5 = s5 := by
  funext p
  simp only [step, s5, Bool.toNat_true]
  decide

theorem state_small :
    state 969 1 = s1 ∧ state 969 2 = s2 ∧ state 969 3 = s3 ∧ state 969 4 = s4 := by
  have h0 : state 969 0 = s0 := rfl
  have h1 : state 969 1 = s1 := by
    rw [show state 969 1 = step 969 (state 969 0) from rfl, h0, step01]
  have h2 : state 969 2 = s2 := by
    rw [show state 969 2 = step 969 (state 969 1) from rfl, h1, step12]
  have h3 : state 969 3 = s3 := by
    rw [show state 969 3 = step 969 (state 969 2) from rfl, h2, step23]
  have h4 : state 969 4 = s4 := by
    rw [show state 969 4 = step 969 (state 969 3) from rfl, h3, step34]
  exact ⟨h1, h2, h3, h4⟩

theorem state_ge (n : ℕ) (hn : 5 ≤ n) : state 969 n = s5 := by
  induction n, hn using Nat.le_induction with
  | base => rw [show state 969 5 = step 969 (state 969 4) from rfl, state_small.2.2.2, step45]
  | succ n hn ih => rw [show state 969 (n + 1) = step 969 (state 969 n) from rfl, ih, step55]

theorem card_square (n : ℕ) :
    (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).card = (2 * n + 1) ^ 2 := by
  rw [Finset.card_product, Int.card_Icc, sq]
  congr 1 <;> omega

/-- Count when the OFF cells of the square form a given explicit set. -/
theorem count_of {s : ℤ × ℤ → Bool} {n : ℕ} (F : Finset (ℤ × ℤ))
    (hF : ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter fun p => ¬ s p = true) = F) :
    count s n + F.card = (2 * n + 1) ^ 2 := by
  rw [count, ← hF, Finset.card_filter_add_card_filter_not, card_square]

theorem a_ge (n : ℕ) (hn : 5 ≤ n) : a n = (2 * n + 1) ^ 2 := by
  have h := count_of (s := state 969 n) (n := n) ∅ (by
    ext ⟨x, y⟩
    simp [state_ge n hn, s5])
  rw [Finset.card_empty, add_zero] at h
  exact h

theorem a_small : a 0 = 1 ∧ a 1 = 4 ∧ a 2 = 21 ∧ a 3 = 45 ∧ a 4 = 76 := by
  obtain ⟨h1, h2, h3, h4⟩ := state_small
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := count_of (s := state 969 0) (n := 0) ∅ (by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, state,
        Finset.notMem_empty, iff_false, not_and, decide_eq_true_eq]
      omega)
    unfold a
    simpa using h
  · have h := count_of (s := state 969 1) (n := 1) {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)} (by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, h1, s1,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, decide_eq_true_eq, not_not]
      omega)
    have hc : ({(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)).card = 5 := by decide
    rw [hc] at h
    unfold a
    omega
  · have h := count_of (s := state 969 2) (n := 2) {(1, 1), (1, -1), (-1, 1), (-1, -1)} (by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, h2, s2,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, decide_eq_true_eq, not_not]
      omega)
    have hc : ({(1, 1), (1, -1), (-1, 1), (-1, -1)} : Finset (ℤ × ℤ)).card = 4 := by decide
    rw [hc] at h
    unfold a
    omega
  · have h := count_of (s := state 969 3) (n := 3) {(1, 0), (-1, 0), (0, 1), (0, -1)} (by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, h3, s3,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, decide_eq_true_eq, not_not]
      omega)
    have hc : ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)).card = 4 := by decide
    rw [hc] at h
    unfold a
    omega
  · have h := count_of (s := state 969 4) (n := 4)
      {(0, 0), (1, 1), (1, -1), (-1, 1), (-1, -1)} (by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, h4, s4,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, decide_eq_true_eq, not_not]
      omega)
    have hc : ({(0, 0), (1, 1), (1, -1), (-1, 1), (-1, -1)} : Finset (ℤ × ℤ)).card = 5 := by
      decide
    rw [hc] at h
    unfold a
    omega

theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rw [a_ge n (by omega), a_ge (n - 1) (by omega), a_ge (n - 2) (by omega), a_ge (n - 3) (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  rw [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega,
    show k + 8 - 3 = k + 5 by omega]
  push_cast
  ring

theorem gf_mul :
    A * (1 - X) ^ 3 = 1 + X + 12 * X ^ 2 - 7 * X ^ 3 + 7 * X ^ 5 - 11 * X ^ 6 + 5 * X ^ 7 := by
  have hD : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - C 1 * (A * X ^ 3) := by
    simp only [map_one, map_ofNat]
    ring
  have hN : (1 + X + 12 * X ^ 2 - 7 * X ^ 3 + 7 * X ^ 5 - 11 * X ^ 6 + 5 * X ^ 7 : ℚ⟦X⟧) =
      C 1 * X ^ 0 + C 1 * X ^ 1 + C 12 * X ^ 2 - C 7 * X ^ 3 + C 7 * X ^ 5 - C 11 * X ^ 6 +
        C 5 * X ^ 7 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 8 with hm | hm
  · obtain ⟨e0, e1, e2, e3, e4⟩ := a_small
    have e5 := a_ge 5 le_rfl
    have e6 := a_ge 6 (by norm_num)
    have e7 := a_ge 7 (by norm_num)
    norm_num at e5 e6 e7
    interval_cases m <;> norm_num [e0, e1, e2, e3, e4, e5, e6, e7]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 3 * a (m - 1) - 3 * a (m - 2) + a (m - 3) := by exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have h5 : 5 ≤ m := by omega
    have h6 : 6 ≤ m := by omega
    have h7 : 7 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k1 : m - 1 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k3 : m - 3 ≠ 0 := by omega
    have k5 : m - 5 ≠ 0 := by omega
    have k6 : m - 6 ≠ 0 := by omega
    have k7 : m - 7 ≠ 0 := by omega
    simp only [h1, h2, h3, h5, h6, h7, Nat.zero_le, k0, k1, k2, k3, k5, k6, k7, coeff_C, if_true,
      if_false, hq]
    ring

theorem proof : Conjecture := by
  refine ⟨fun n hn => by rw [a_ge n (by omega)]; ring, recurrence, ?_⟩
  have h0 : constantCoeff ((1 - X) ^ 3 : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

end OMA.S_oeis_a273847

theorem OMA.solution : type_of% @OMA.S_oeis_a273847.main :=
  OMA.S_oeis_a273847.proof
