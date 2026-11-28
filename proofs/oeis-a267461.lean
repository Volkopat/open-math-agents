import OMAStatements.S_oeis_a267461

namespace OMA.S_oeis_a267461

open PowerSeries





theorem eca133 (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    eca 133 (decide A) (decide B) (decide C) =
      decide ((A ∧ B ∧ C) ∨ (¬A ∧ B ∧ ¬C) ∨ (¬A ∧ ¬B ∧ ¬C)) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC] <;> decide

/-- The pattern of stage `t ≥ 2`. -/
def P (t : ℕ) (i : ℤ) : Prop :=
  i > t ∨ i < -(t : ℤ) ∨ (i % 2 = 0 ∧ -((t : ℤ) - 2 - ((t % 2 : ℕ) : ℤ)) ≤ i ∧
    i ≤ (t : ℤ) - 2 - ((t % 2 : ℕ) : ℤ))

instance (t : ℕ) (i : ℤ) : Decidable (P t i) := by unfold P; infer_instance

theorem state_one (i : ℤ) : state 1 i = decide (i ≠ 1 ∧ i ≠ -1) := by
  show eca 133 (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = _
  rw [eca133]
  apply Bool.decide_congr
  omega

theorem state_two (i : ℤ) : state 2 i = decide (P 2 i) := by
  show eca 133 (state 1 (i - 1)) (state 1 i) (state 1 (i + 1)) = _
  rw [state_one, state_one, state_one, eca133]
  apply Bool.decide_congr
  unfold P
  omega

theorem state_pattern (t : ℕ) (ht : 2 ≤ t) (i : ℤ) : state t i = decide (P t i) := by
  induction t, ht using Nat.le_induction generalizing i with
  | base => exact state_two i
  | succ t ht ih =>
    show eca 133 (state t (i - 1)) (state t i) (state t (i + 1)) = _
    rw [ih, ih, ih, eca133]
    apply Bool.decide_congr
    unfold P
    have : (t + 1) % 2 = 1 - t % 2 := by omega
    rw [this]
    rcases Nat.mod_two_eq_zero_or_one t with h | h <;> rw [h] <;> push_cast <;> omega

theorem white_zero : white 0 = 0 := by decide +kernel

theorem white_one : white 1 = 2 := by decide +kernel

theorem white_pattern (t : ℕ) (ht : 2 ≤ t) : white t = t + 2 + t % 2 := by
  have hon : ((Finset.range (2 * t + 1)).filter fun k : ℕ =>
      ¬ (state t ((k : ℤ) - (t : ℤ)) = false)) =
      (Finset.range (t - 2 - t % 2 + 1)).image (fun j => 2 + t % 2 + 2 * j) := by
    ext k
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_image, state_pattern t ht,
      Bool.not_eq_false, decide_eq_true_eq]
    unfold P
    constructor
    · rintro ⟨hk, h⟩
      have h2 : ((k : ℤ) - t) % 2 = 0 ∧ -((t : ℤ) - 2 - ((t % 2 : ℕ) : ℤ)) ≤ (k : ℤ) - t ∧
          (k : ℤ) - t ≤ (t : ℤ) - 2 - ((t % 2 : ℕ) : ℤ) := by omega
      push_cast at h2
      refine ⟨(k - 2 - t % 2) / 2, ?_, ?_⟩
      · rw [Finset.mem_range]; omega
      · omega
    · rintro ⟨j, hj, rfl⟩
      rw [Finset.mem_range] at hj
      refine ⟨by omega, Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩ <;> push_cast <;> omega
  have hinj : Set.InjOn (fun j => 2 + t % 2 + 2 * j) (Finset.range (t - 2 - t % 2 + 1)) := by
    intro x _ y _ h; simp only at h; omega
  have hcard := Finset.card_filter_add_card_filter_not
    (s := Finset.range (2 * t + 1)) (fun k : ℕ => state t ((k : ℤ) - (t : ℤ)) = false)
  rw [hon, Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_range] at hcard
  unfold white
  omega

/-- Barker's closed form, as `4 a(n) = 2n^2 + 12n - (-1)^n - 7` for `n > 0`. -/
theorem closed_form (n : ℕ) (hn : 0 < n) :
    4 * (a n : ℤ) = 2 * (n : ℤ) ^ 2 + 12 * n - (-1) ^ n - 7 := by
  induction n, hn using Nat.le_induction with
  | base => simp [a, Finset.sum_range_succ, white_zero, white_one]
  | succ n hn ih =>
    have hs : a (n + 1) = a n + white (n + 1) := Finset.sum_range_succ _ _
    rw [hs, white_pattern (n + 1) (by omega)]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have e1 : ((-1 : ℤ)) ^ n = 1 := by rw [hk, ← two_mul, pow_mul]; norm_num
      have e2 : ((-1 : ℤ)) ^ (n + 1) = -1 := by rw [pow_succ, e1]; norm_num
      have hm : (n + 1) % 2 = 1 := by omega
      rw [e1] at ih; rw [e2, hm]; push_cast; linear_combination ih
    · have e1 : ((-1 : ℤ)) ^ n = -1 := by rw [hk, pow_succ, pow_mul]; norm_num
      have e2 : ((-1 : ℤ)) ^ (n + 1) = 1 := by rw [pow_succ, e1]; norm_num
      have hm : (n + 1) % 2 = 0 := by omega
      rw [e1] at ih; rw [e2, hm]; push_cast; linear_combination ih

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 3 = k + 2 by omega,
    show k + 5 - 4 = k + 1 by omega]
  have c5 := closed_form (k + 5) (by omega)
  have c4 := closed_form (k + 4) (by omega)
  have c2 := closed_form (k + 2) (by omega)
  have c1 := closed_form (k + 1) (by omega)
  have p1 : ((-1 : ℤ)) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
  have p2 : ((-1 : ℤ)) ^ (k + 2) = (-1) ^ k := by rw [pow_add]; norm_num
  have p4 : ((-1 : ℤ)) ^ (k + 4) = (-1) ^ k := by rw [pow_add]; norm_num
  have p5 : ((-1 : ℤ)) ^ (k + 5) = -(-1) ^ k := by rw [pow_add]; norm_num
  rw [p5] at c5; rw [p4] at c4; rw [p2] at c2; rw [p1] at c1
  push_cast at c5 c4 c2 c1 ⊢
  have h4 : 4 * ((a (k + 5) : ℤ) - (2 * a (k + 4) - 2 * a (k + 2) + a (k + 1))) = 0 := by
    linear_combination c5 - 2 * c4 + 2 * c2 - c1
  have := (mul_eq_zero.mp h4).resolve_left (by norm_num)
  linarith

/-- Barker's g.f. with the denominator cleared: `A(x) (1-x)^3 (1+x) = 2x (1 + x - x^3)`. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X)) =
    (2 * X * (1 + X - X ^ 3) : PowerSeries ℤ) := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have hD : A * ((1 - X) ^ 3 * (1 + X)) =
      A - A * X ^ 1 - A * X ^ 1 + A * X ^ 3 + A * X ^ 3 - A * X ^ 4 := by ring
  have hN : (2 * X * (1 + X - X ^ 3) : PowerSeries ℤ) =
      X ^ 1 + X ^ 1 + X ^ 2 + X ^ 2 - X ^ 4 - X ^ 4 := by ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk, coeff_X_pow]
  have v : (List.range 5).map a = [0, 2, 6, 12, 18] := by
    have h : ∀ t, 2 ≤ t → white t = t + 2 + t % 2 := white_pattern
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.map_append]
    simp [a, Finset.sum_range_succ, white_zero, white_one, h]
  simp only [List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.cons.injEq, List.map_append, List.map_cons, List.map_nil] at v
  obtain ⟨v0, v1, v2, v3, v4, -⟩ := v
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, if_true,
      show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 4 by omega, if_false]
    linear_combination r

end OMA.S_oeis_a267461

theorem OMA.solution : type_of% @OMA.S_oeis_a267461.main :=
  ⟨OMA.S_oeis_a267461.closed_form, OMA.S_oeis_a267461.recurrence, OMA.S_oeis_a267461.gf⟩
