import OMAStatements.S_oeis_a201722

-- Problem: A201722: Number of n X 1 0..4 arrays with rows and columns lexicographically nondecreasing and no element equal to the number of horizontal and vertical neighbors equal to itself.
-- Credit: @EmadY (the owner of the agent is credited as the solver)
--
-- Proof idea (transfer matrix). Let C(n, p, r) count the columns l of length n with ok p r l.
-- Peeling the first entry of l gives a recursion, solved by induction:
--   C(n,4,r) = 1, C(n,3,r) = n + 1, C(n,2,0) = 2n + 1, C(n,2,1) = n + 1, C(n,1,1) = 0,
--   C(n+1,1,0) = 3(n+1), C(n+1,0,1) = 3(n+1)^2 + 2, C(n+1,0,0) = C(n,0,1).
-- Hence a(n+1) = sum_c C(n,c,0) gives a(1) = 4, a(2) = 10, a(m+3) = 3m^2 + 12m + 20, and both of
-- Barker's conjectures follow.

namespace OMA.S_oeis_a201722

open PowerSeries

/-- The number of columns of length `n` that pass a Boolean test. -/
def cnt (n : ℕ) (P : List (Fin 5) → Bool) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 5 => P (List.ofFn x) = true).card

lemma cnt_zero (P : List (Fin 5) → Bool) : cnt 0 P = if P [] = true then 1 else 0 := by
  unfold cnt
  rw [Finset.card_filter]
  simp

lemma cnt_succ (n : ℕ) (P : List (Fin 5) → Bool) :
    cnt (n + 1) P = ∑ c : Fin 5, cnt n (fun l => P (c :: l)) := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Fin 5)) _ _
    (fun q => by simp [Fin.consEquiv, List.ofFn_succ])).symm

lemma cnt_and (n : ℕ) (b : Bool) (Q : List (Fin 5) → Bool) :
    cnt n (fun l => b && Q l) = if b = true then cnt n Q else 0 := by
  cases b <;> simp [cnt]

lemma cnt_false (n : ℕ) : cnt n (fun _ => false) = 0 := by simp [cnt]

lemma step (n : ℕ) (p : Fin 5) (r : ℕ) :
    cnt (n + 1) (ok p r) = ∑ c : Fin 5, cnt n (fun l =>
      decide (p ≤ c) && (if c = p then decide (r + 1 ≠ p.val) && ok c 1 l
        else decide (r ≠ p.val) && ok c 0 l)) := by
  rw [cnt_succ]
  rfl

lemma C4 (n : ℕ) : cnt n (ok 4 0) = 1 ∧ cnt n (ok 4 1) = 1 := by
  induction n with
  | zero => simp [cnt_zero, ok]
  | succ n ih =>
    rw [step, step, Fin.sum_univ_five, Fin.sum_univ_five]
    simp [cnt_and, cnt_false, ih.2]

lemma C3 (n : ℕ) : cnt n (ok 3 0) = n + 1 ∧ cnt n (ok 3 1) = n + 1 := by
  induction n with
  | zero => simp [cnt_zero, ok]
  | succ n ih =>
    rw [step, step, Fin.sum_univ_five, Fin.sum_univ_five]
    simp [cnt_and, cnt_false, ih.2, (C4 n).1]

lemma C2 (n : ℕ) : cnt n (ok 2 0) = 2 * n + 1 ∧ cnt n (ok 2 1) = n + 1 := by
  induction n with
  | zero => simp [cnt_zero, ok]
  | succ n ih =>
    rw [step, step, Fin.sum_univ_five, Fin.sum_univ_five]
    simp [cnt_and, cnt_false, ih.2, (C3 n).1, (C4 n).1]
    omega

lemma C11 (n : ℕ) : cnt n (ok 1 1) = 0 := by
  induction n with
  | zero => simp [cnt_zero, ok]
  | succ n ih =>
    rw [step, Fin.sum_univ_five]
    simp [cnt_and, cnt_false, ih]

lemma C10 (n : ℕ) : cnt (n + 1) (ok 1 0) = 3 * (n + 1) := by
  rw [step, Fin.sum_univ_five]
  simp [cnt_and, cnt_false, (C2 n).1, (C3 n).1, (C4 n).1]
  omega

lemma C10' : cnt 0 (ok 1 0) = 1 := by simp [cnt_zero, ok]

lemma C01 (n : ℕ) : cnt (n + 1) (ok 0 1) = 3 * (n + 1) ^ 2 + 2 := by
  induction n with
  | zero =>
    rw [step, Fin.sum_univ_five]
    simp [cnt_and, cnt_false, cnt_zero, ok]
  | succ n ih =>
    rw [step, Fin.sum_univ_five]
    simp [cnt_and, cnt_false, ih, C10 n, (C2 (n + 1)).1, (C3 (n + 1)).1, (C4 (n + 1)).1]
    ring

lemma C00 (n : ℕ) : cnt (n + 1) (ok 0 0) = cnt n (ok 0 1) := by
  rw [step, Fin.sum_univ_five]
  simp [cnt_and, cnt_false]
  try rfl

lemma a_cnt (n : ℕ) : a (n + 1) = ∑ c : Fin 5, cnt n (ok c 0) := by
  show cnt (n + 1) valid = _
  rw [cnt_succ]
  rfl

lemma a_one : a 1 = 4 := by
  rw [a_cnt, Fin.sum_univ_five]
  simp [cnt_zero, ok]

lemma a_two : a 2 = 10 := by
  rw [a_cnt, Fin.sum_univ_five, C00, C10 0]
  simp [cnt_zero, ok, (C2 1).1, (C3 1).1, (C4 1).1]

lemma a_ge (m : ℕ) : a (m + 3) = 3 * m ^ 2 + 12 * m + 20 := by
  rw [a_cnt, Fin.sum_univ_five, C00, C01 m, C10 (m + 1), (C2 (m + 2)).1, (C3 (m + 2)).1,
    (C4 (m + 2)).1]
  ring

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = (m + 2) + 3 by omega, show m + 6 - 2 = (m + 1) + 3 by omega,
    show m + 6 - 3 = m + 3 by omega, show m + 6 = (m + 3) + 3 by omega,
    a_ge, a_ge, a_ge, a_ge]
  push_cast
  ring

theorem gf_eq : gf = X * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4) * ((1 - X) ^ 3)⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  have e1 : gf * (1 - X) ^ 3 =
      gf - gf * X ^ 1 - gf * X ^ 1 - gf * X ^ 1 + gf * X ^ 2 + gf * X ^ 2 + gf * X ^ 2 -
        gf * X ^ 3 := by ring
  have e2 : (X : ℚ⟦X⟧) * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4) =
      C 4 * X ^ 1 - C 2 * X ^ 2 + C 2 * X ^ 3 + X ^ 4 + X ^ 5 := by
    rw [map_ofNat, map_ofNat]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k gf = if k = 0 then (0 : ℚ) else (a k : ℚ) := fun k => by
    rw [gf, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', hc, coeff_C]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · have h3 : a 3 = 20 := a_ge 0
    have h4 : a 4 = 35 := a_ge 1
    have h5 : a 5 = 56 := a_ge 2
    interval_cases n <;> simp [a_one, a_two, h3, h4, h5] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 1 = (m + 2) + 3 by omega, show m + 6 - 2 = (m + 1) + 3 by omega,
      show m + 6 - 3 = m + 3 by omega, show ¬ m + 6 = 0 by omega,
      show ¬ (m + 2) + 3 = 0 by omega, show ¬ (m + 1) + 3 = 0 by omega,
      show ¬ m + 3 = 0 by omega, show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega,
      show 3 ≤ m + 6 by omega, if_true, if_false, show ¬ m + 6 = 1 by omega,
      show ¬ m + 6 = 2 by omega, show ¬ m + 6 = 3 by omega, show ¬ m + 6 = 4 by omega,
      show ¬ m + 6 = 5 by omega]
    rw [show m + 6 = (m + 3) + 3 by omega, a_ge, a_ge, a_ge, a_ge]
    push_cast
    ring

theorem conjecture :
    gf = X * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4) * ((1 - X) ^ 3)⁻¹ ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf_eq, recurrence⟩

end OMA.S_oeis_a201722

theorem OMA.solution : type_of% @OMA.S_oeis_a201722.main :=
  OMA.S_oeis_a201722.conjecture
