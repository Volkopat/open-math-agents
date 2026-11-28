import OMAStatements.S_oeis_a273313

namespace OMA.S_oeis_a273313

open PowerSeries




/-- The pattern: stages 0 and 1 explicitly, and from stage 2 on every cell is ON but the eight
cells around the origin. -/
def P : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | 1, x, y => !decide (x.natAbs + y.natAbs = 1)
  | _ + 2, x, y => !decide (x.natAbs ≤ 1 ∧ y.natAbs ≤ 1 ∧ ¬(x = 0 ∧ y = 0))

theorem P_two (m : ℕ) (x y : ℤ) :
    P (m + 2) x y = !decide (x.natAbs ≤ 1 ∧ y.natAbs ≤ 1 ∧ ¬(x = 0 ∧ y = 0)) := rfl

/-- Away from the origin every stage t >= 1 is ON. -/
theorem P_far (t : ℕ) (ht : 0 < t) (u v : ℤ) (h : 3 ≤ u.natAbs + v.natAbs) : P t u v = true := by
  rcases (by omega : t = 1 ∨ 2 ≤ t) with rfl | h2
  · show (!decide (u.natAbs + v.natAbs = 1)) = true
    rw [decide_eq_false (by omega)]; rfl
  · obtain ⟨m, rfl⟩ : ∃ m, t = m + 2 := ⟨t - 2, by omega⟩
    rw [P_two, decide_eq_false (by omega)]; rfl

/-- One step of each of the four rules maps the pattern at stage t to the pattern at stage t + 1. -/
theorem step (R : ℕ) (hR : R = 643 ∨ R = 651 ∨ R = 707 ∨ R = 715) (t : ℕ) (x y : ℤ) :
    Nat.testBit R ((P t x y).toNat + 2 * ((P t (x - 1) y).toNat + (P t (x + 1) y).toNat +
      (P t x (y - 1)).toNat + (P t x (y + 1)).toNat)) = P (t + 1) x y := by
  rcases (by omega : x.natAbs + y.natAbs ≤ 3 ∨ 4 ≤ x.natAbs + y.natAbs) with h | h
  · have hx1 : -3 ≤ x := by omega
    have hx2 : x ≤ 3 := by omega
    have hy1 : -3 ≤ y := by omega
    have hy2 : y ≤ 3 := by omega
    rcases (by omega : t < 2 ∨ 2 ≤ t) with ht | ht
    · rcases hR with rfl | rfl | rfl | rfl <;>
        interval_cases t <;> interval_cases x <;> interval_cases y <;> rfl
    · obtain ⟨m, rfl⟩ : ∃ m, t = m + 2 := ⟨t - 2, by omega⟩
      rw [show m + 2 + 1 = m + 1 + 2 by ring]
      simp only [P_two]
      rcases hR with rfl | rfl | rfl | rfl <;> interval_cases x <;> interval_cases y <;> rfl
  · rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      have e : ∀ u v : ℤ, 3 ≤ u.natAbs + v.natAbs → P 0 u v = false := fun u v huv =>
        decide_eq_false (by omega)
      rw [e x y (by omega), e (x - 1) y (by omega), e (x + 1) y (by omega),
        e x (y - 1) (by omega), e x (y + 1) (by omega),
        P_far 1 (by omega) x y (by omega)]
      rcases hR with rfl | rfl | rfl | rfl <;> rfl
    · rw [P_far t ht x y (by omega), P_far t ht (x - 1) y (by omega),
        P_far t ht (x + 1) y (by omega), P_far t ht x (y - 1) (by omega),
        P_far t ht x (y + 1) (by omega), P_far (t + 1) (by omega) x y (by omega)]
      rcases hR with rfl | rfl | rfl | rfl <;> rfl

/-- Stage t of each of the four rules is the pattern `P t`. -/
theorem state_eq (R : ℕ) (hR : R = 643 ∨ R = 651 ∨ R = 707 ∨ R = 715) (t : ℕ) :
    ∀ x y, state R t x y = P t x y := by
  induction t with
  | zero => intro x y; rfl
  | succ t ih =>
    intro x y
    show Nat.testBit R _ = _
    rw [ih, ih, ih, ih, ih]
    exact step R hR t x y

/-- The four rules have the same counts. -/
theorem count_eq (R : ℕ) (hR : R = 643 ∨ R = 651 ∨ R = 707 ∨ R = 715) (t : ℕ) :
    count R t = count 643 t := by
  unfold count
  simp only [state_eq R hR, state_eq 643 (Or.inl rfl)]

/-- From stage 2 on, the square has (2t + 1)^2 - 8 ON cells. -/
theorem count_big (t : ℕ) (ht : 2 ≤ t) : count 643 t + 8 = (2 * t + 1) ^ 2 := by
  have hs : ∀ x y : ℤ, state 643 t x y =
      !decide (x.natAbs ≤ 1 ∧ y.natAbs ≤ 1 ∧ ¬(x = 0 ∧ y = 0)) := by
    intro x y
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 2 := ⟨t - 2, by omega⟩
    rw [state_eq 643 (Or.inl rfl), P_two]
  have hs' : ∀ x y : ℤ, (state 643 t x y = true) ↔
      ¬(x.natAbs ≤ 1 ∧ y.natAbs ≤ 1 ∧ ¬(x = 0 ∧ y = 0)) := by
    intro x y
    rw [hs]
    by_cases hP : x.natAbs ≤ 1 ∧ y.natAbs ≤ 1 ∧ ¬(x = 0 ∧ y = 0)
    · rw [decide_eq_true hP]; simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_not]
      exact hP
    · rw [decide_eq_false hP]; simp only [Bool.not_false, true_iff]
      exact hP
  set S := Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t with hS
  have hK : S.filter (fun p => ¬(state 643 t p.1 p.2 = true)) =
      (Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1).erase (0, 0) := by
    ext ⟨x, y⟩
    simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_erase,
      ne_eq, Prod.mk.injEq, hs', not_not]
    constructor
    · intro h; omega
    · intro h; omega
  have hcard : ((Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1).erase (0, 0)).card = 8 := by
    decide
  have h := Finset.card_filter_add_card_filter_not
    (s := S) (fun p : ℤ × ℤ => state 643 t p.1 p.2 = true)
  rw [hK, hcard, hS, Finset.card_product, Int.card_Icc,
    show ((t : ℤ) + 1 - -(t : ℤ)).toNat = 2 * t + 1 by omega] at h
  unfold count
  rw [← hS] at h ⊢
  rw [h]
  ring

theorem count_small : count 643 0 = 1 ∧ count 643 1 = 5 := by
  have e : ∀ t, count 643 t = ((Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
      (fun p => P t p.1 p.2 = true)).card := by
    intro t; unfold count; simp only [state_eq 643 (Or.inl rfl)]
  have i0 : Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = {0} := by decide
  have i1 : Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  refine ⟨?_, ?_⟩
  · rw [e, i0]; decide
  · rw [e, i1]; decide

/-- Blomberg's closed form, for n > 1. -/
theorem closed (n : ℕ) (hn : 1 < n) : (a n : ℤ) = 4 * 4 ^ n - 4 * 2 ^ n - 7 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h1 := count_big (2 ^ (m + 2) - 1) (by rw [pow_add]; omega)
  have ht' : ((2 ^ (m + 2) - 1 : ℕ) : ℤ) = 4 * 2 ^ m - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
    push_cast
    ring
  have h1z : ((count 643 (2 ^ (m + 2) - 1) : ℕ) : ℤ) + 8 =
      (2 * ((2 ^ (m + 2) - 1 : ℕ) : ℤ) + 1) ^ 2 := by exact_mod_cast h1
  rw [ht'] at h1z
  have e4 : ((2 : ℤ) ^ m) ^ 2 = 4 ^ m := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  unfold a
  rw [pow_add (4 : ℤ) m 2, pow_add (2 : ℤ) m 2, ← e4]
  linear_combination h1z

theorem a_zero : a 0 = 1 := count_small.1

theorem a_one : a 1 = 5 := count_small.2

theorem val (n N : ℕ) (hn : 1 < n) (hN : (N : ℤ) = 4 * 4 ^ n - 4 * 2 ^ n - 7) : a n = N := by
  have h := (closed n hn).trans hN.symm
  exact_mod_cast h

/-- Controls: the entry's terms a(0..11). -/
theorem controls : a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 41 ∧ a 3 = 217 ∧ a 4 = 953 ∧ a 5 = 3961 ∧
    a 6 = 16121 ∧ a 7 = 65017 ∧ a 8 = 261113 ∧ a 9 = 1046521 ∧ a 10 = 4190201 ∧
    a 11 = 16769017 :=
  ⟨a_zero, a_one, val 2 41 (by norm_num) (by norm_num), val 3 217 (by norm_num) (by norm_num),
    val 4 953 (by norm_num) (by norm_num), val 5 3961 (by norm_num) (by norm_num),
    val 6 16121 (by norm_num) (by norm_num), val 7 65017 (by norm_num) (by norm_num),
    val 8 261113 (by norm_num) (by norm_num), val 9 1046521 (by norm_num) (by norm_num),
    val 10 4190201 (by norm_num) (by norm_num), val 11 16769017 (by norm_num) (by norm_num)⟩

/-- Barker's recurrence, for n > 4. -/
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, closed (m + 5) (by omega), closed (m + 4) (by omega),
    closed (m + 3) (by omega), closed (m + 2) (by omega)]
  ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
    1 - 2 * X + 20 * X ^ 2 - 8 * X ^ 3 - 32 * X ^ 4 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have c2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have c7 : (C (7 : ℤ) : PowerSeries ℤ) = 7 := map_ofNat C 7
  have c8 : (C (8 : ℤ) : PowerSeries ℤ) = 8 := map_ofNat C 8
  have c14 : (C (14 : ℤ) : PowerSeries ℤ) = 14 := map_ofNat C 14
  have c20 : (C (20 : ℤ) : PowerSeries ℤ) = 20 := map_ofNat C 20
  have c32 : (C (32 : ℤ) : PowerSeries ℤ) = 32 := map_ofNat C 32
  have hD : A * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      A - C 7 * (A * X ^ 1) + C 14 * (A * X ^ 2) - C 8 * (A * X ^ 3) := by
    rw [c7, c8, c14]; ring
  have hN : (1 - 2 * X + 20 * X ^ 2 - 8 * X ^ 3 - 32 * X ^ 4 : PowerSeries ℤ) =
      1 - X ^ 1 * C 2 + X ^ 2 * C 20 - X ^ 3 * C 8 - X ^ 4 * C 32 := by
    rw [c2, c8, c20, c32]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_one, coeff_X_pow]
  obtain ⟨v0, v1, v2, v3, v4, -⟩ := controls
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, if_false]
    linear_combination r

/-- Blomberg's two conjectures and Barker's two. -/
theorem conjecture :
    (∀ n : ℕ, count 651 (2 ^ n - 1) = a n ∧ count 707 (2 ^ n - 1) = a n ∧
      count 715 (2 ^ n - 1) = a n) ∧
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 4 * 4 ^ n - 4 * 2 ^ n - 7) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 - 2 * X + 20 * X ^ 2 - 8 * X ^ 3 - 32 * X ^ 4 :=
  ⟨fun n => ⟨count_eq 651 (by norm_num) _, count_eq 707 (by norm_num) _,
    count_eq 715 (by norm_num) _⟩, closed, recurrence, gf⟩

end OMA.S_oeis_a273313

theorem OMA.solution : type_of% @OMA.S_oeis_a273313.main :=
  OMA.S_oeis_a273313.conjecture
