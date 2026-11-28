import OMAStatements.S_oeis_a285777

namespace OMA.S_oeis_a285777

open PowerSeries



/-- The pattern: stages 0 to 3 explicitly, and from stage 4 on the plane is uniform, OFF at even
stages and ON at odd ones. -/
def P : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | 1, x, y => decide (2 ≤ x.natAbs + y.natAbs)
  | 2, x, y => decide (x.natAbs + y.natAbs ≤ 1)
  | 3, x, y => !decide ((x = 0 ∧ (y = 0 ∨ y.natAbs = 2)) ∨ (y = 0 ∧ x.natAbs = 2))
  | m + 4, _, _ => decide (m % 2 = 1)

theorem P_four (m : ℕ) (x y : ℤ) : P (m + 4) x y = decide (m % 2 = 1) := rfl

/-- Away from the origin every stage has the background value, ON exactly at odd stages. -/
theorem P_far (t : ℕ) (u v : ℤ) (h : 3 ≤ u.natAbs + v.natAbs) :
    P t u v = decide (t % 2 = 1) := by
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ 4 ≤ t) with rfl | rfl | rfl | rfl | h4
  · exact decide_eq_false (by omega)
  · exact decide_eq_true (by omega)
  · exact decide_eq_false (by omega)
  · show (!decide ((u = 0 ∧ (v = 0 ∨ v.natAbs = 2)) ∨ (v = 0 ∧ u.natAbs = 2))) = _
    rw [decide_eq_false (by omega)]; rfl
  · obtain ⟨m, rfl⟩ : ∃ m, t = m + 4 := ⟨t - 4, by omega⟩
    rw [P_four, show (m + 4) % 2 = m % 2 by omega]

/-- One step of Rule 89 maps the pattern at stage t to the pattern at stage t + 1. -/
theorem step (t : ℕ) (x y : ℤ) :
    Nat.testBit 89 ((P t x y).toNat + 2 * ((P t (x - 1) y).toNat + (P t (x + 1) y).toNat +
      (P t x (y - 1)).toNat + (P t x (y + 1)).toNat)) = P (t + 1) x y := by
  rcases (by omega : t < 4 ∨ 4 ≤ t) with ht | ht
  · rcases (by omega : x.natAbs + y.natAbs ≤ 3 ∨ 4 ≤ x.natAbs + y.natAbs) with h | h
    · have hx1 : -3 ≤ x := by omega
      have hx2 : x ≤ 3 := by omega
      have hy1 : -3 ≤ y := by omega
      have hy2 : y ≤ 3 := by omega
      interval_cases t <;> interval_cases x <;> interval_cases y <;> rfl
    · rw [P_far t x y (by omega), P_far t (x - 1) y (by omega), P_far t (x + 1) y (by omega),
        P_far t x (y - 1) (by omega), P_far t x (y + 1) (by omega),
        P_far (t + 1) x y (by omega), show (t + 1) % 2 = (t % 2 + 1) % 2 by omega]
      have hr : t % 2 < 2 := Nat.mod_lt _ (by norm_num)
      generalize t % 2 = r at *
      interval_cases r <;> rfl
  · obtain ⟨m, rfl⟩ : ∃ m, t = m + 4 := ⟨t - 4, by omega⟩
    rw [show m + 4 + 1 = m + 1 + 4 by ring]
    simp only [P_four]
    rw [show (m + 1) % 2 = (m % 2 + 1) % 2 by omega]
    have hr : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    generalize m % 2 = r at *
    interval_cases r <;> rfl

/-- Stage t is the pattern `P t`. -/
theorem state_eq (t : ℕ) : ∀ x y, state t x y = P t x y := by
  induction t with
  | zero => intro x y; rfl
  | succ t ih =>
    intro x y
    show Nat.testBit 89 _ = _
    rw [ih, ih, ih, ih, ih]
    exact step t x y

/-- From stage 4 on, every diagonal cell is ON exactly at odd stages. -/
theorem diag (n k : ℕ) (hn : 4 ≤ n) : state n (k : ℤ) (k : ℤ) = decide (n % 2 = 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [state_eq, P_four, show (m + 4) % 2 = m % 2 by omega]

theorem a_eq (n : ℕ) : a n = ∑ k ∈ Finset.range (n + 1), if P n (k : ℤ) (k : ℤ) then 2 ^ k else 0 := by
  simp only [a, state_eq]

/-- Controls: the entry's terms a(0..15). -/
theorem controls : (List.range 16).map a =
    [1, 2, 1, 14, 0, 63, 0, 255, 0, 1023, 0, 4095, 0, 16383, 0, 65535] := by
  rw [show a = fun n => ∑ k ∈ Finset.range (n + 1), if P n (k : ℤ) (k : ℤ) then 2 ^ k else 0
    from funext a_eq]
  decide

theorem geom (n : ℕ) : ∑ k ∈ Finset.range n, (2 : ℤ) ^ k = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem a_even (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) : a n = 0 := by
  unfold a
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [diag n k hn, he]
  rfl

theorem a_odd (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) : (a n : ℤ) = 2 ^ (n + 1) - 1 := by
  have e : a n = ∑ k ∈ Finset.range (n + 1), 2 ^ k := by
    unfold a
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [diag n k hn, ho]
    rfl
  rw [e, ← geom]
  push_cast
  rfl

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 2 = m + 6 by omega, show m + 8 - 4 = m + 4 by omega]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [a_even (m + 8) (by omega) (by omega), a_even (m + 6) (by omega) (by omega),
      a_even (m + 4) (by omega) (by omega)]
    norm_num
  · rw [a_odd (m + 8) (by omega) (by omega), a_odd (m + 6) (by omega) (by omega),
      a_odd (m + 4) (by omega) (by omega)]
    ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
    1 + 2 * X - 4 * X ^ 2 + 4 * X ^ 3 - X ^ 4 + X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have c2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have c4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
  have c5 : (C (5 : ℤ) : PowerSeries ℤ) = 5 := map_ofNat C 5
  have hD : A * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      A - C 5 * (A * X ^ 2) + C 4 * (A * X ^ 4) := by
    rw [c4, c5]; ring
  have hN : (1 + 2 * X - 4 * X ^ 2 + 4 * X ^ 3 - X ^ 4 + X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 :
      PowerSeries ℤ) = 1 + X ^ 1 * C 2 - X ^ 2 * C 4 + X ^ 3 * C 4 - X ^ 4 + X ^ 5 +
      X ^ 6 * C 4 - X ^ 7 * C 4 := by
    rw [c2, c4]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_one, coeff_X_pow]
  have c := controls
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq] at c
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, -⟩ := c
  rcases Nat.lt_or_ge n 8 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7]
  · have r := recurrence n (by omega)
    simp only [show 2 ≤ n by omega, show 4 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega,
      if_false]
    linear_combination r

/-- All four of Barker's conjectures. -/
theorem conjecture :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + 2 * X - 4 * X ^ 2 + 4 * X ^ 3 - X ^ 4 + X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 ∧
    (∀ n : ℕ, 3 < n → Even n → a n = 0) ∧
    (∀ n : ℕ, 3 < n → Odd n → (a n : ℤ) = 2 ^ (n + 1) - 1) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) :=
  ⟨gf, fun n hn he => a_even n hn (Nat.even_iff.mp he),
    fun n hn ho => a_odd n hn (Nat.odd_iff.mp ho), recurrence⟩

end OMA.S_oeis_a285777

theorem OMA.solution : type_of% @OMA.S_oeis_a285777.main :=
  OMA.S_oeis_a285777.conjecture
