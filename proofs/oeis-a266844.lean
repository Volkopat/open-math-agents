import OMAStatements.S_oeis_a266844

namespace OMA.S_oeis_a266844

open PowerSeries




theorem eca70 (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    eca 70 (decide A) (decide B) (decide C) = decide ((B ∧ ¬C) ∨ (¬A ∧ ¬B ∧ C)) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC] <;> decide

/-- The ON cells of stage `t`. -/
def Q (t : ℕ) (i : ℤ) : Prop := -(t : ℤ) ≤ i ∧ i ≤ 0 ∧ (i % 2 = 0 ∨ i = -(t : ℤ))

instance (t : ℕ) (i : ℤ) : Decidable (Q t i) := by unfold Q; infer_instance

theorem state_pattern (t : ℕ) (i : ℤ) : state t i = decide (Q t i) := by
  induction t generalizing i with
  | zero =>
    show decide (i = 0) = _
    apply Bool.decide_congr; unfold Q; omega
  | succ t ih =>
    show eca 70 (state t (i - 1)) (state t i) (state t (i + 1)) = _
    rw [ih, ih, ih, eca70]
    apply Bool.decide_congr
    unfold Q
    push_cast
    omega

/-- The digits of stage `n` sit at the positions `n - 2j` and, for odd `n`, at `0`. -/
theorem support (n : ℕ) :
    (Finset.range (2 * n + 1)).filter (fun k : ℕ => Q n ((k : ℤ) - (n : ℤ))) =
      (Finset.range (n / 2 + 1)).image (fun j => n - 2 * j) ∪
        (if n % 2 = 1 then {0} else ∅) := by
  ext k
  rw [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
  unfold Q
  split_ifs with h
  · rw [Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h1, h2, h3⟩
      rcases h3 with h3 | h3
      · left; exact ⟨(n - k) / 2, by rw [Finset.mem_range]; omega, by omega⟩
      · right; omega
    · rintro (⟨j, hj, rfl⟩ | rfl)
      · rw [Finset.mem_range] at hj
        refine ⟨by omega, by omega, by omega, Or.inl ?_⟩; omega
      · refine ⟨by omega, by omega, by omega, Or.inr ?_⟩; omega
  · rw [or_iff_left (Finset.notMem_empty k)]
    constructor
    · rintro ⟨hk, h1, h2, h3⟩
      rcases h3 with h3 | h3
      · exact ⟨(n - k) / 2, by rw [Finset.mem_range]; omega, by omega⟩
      · exact ⟨n / 2, by rw [Finset.mem_range]; omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      rw [Finset.mem_range] at hj
      refine ⟨by omega, by omega, by omega, Or.inl ?_⟩; omega

theorem a_eq (n : ℕ) :
    a n = (∑ j ∈ Finset.range (n / 2 + 1), 10 ^ (n + 2 * j)) +
      (if n % 2 = 1 then 10 ^ (2 * n) else 0) := by
  unfold a
  simp only [state_pattern, decide_eq_true_eq]
  rw [← Finset.sum_filter, support]
  have hdisj : Disjoint ((Finset.range (n / 2 + 1)).image (fun j => n - 2 * j))
      (if n % 2 = 1 then ({0} : Finset ℕ) else ∅) := by
    split_ifs with h
    · rw [Finset.disjoint_singleton_right, Finset.mem_image]
      rintro ⟨j, hj, hj0⟩
      rw [Finset.mem_range] at hj
      omega
    · exact Finset.disjoint_empty_right _
  rw [Finset.sum_union hdisj]
  have hinj : Set.InjOn (fun j => n - 2 * j) (Finset.range (n / 2 + 1)) := by
    intro x hx y hy h
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    simp only at h
    omega
  rw [Finset.sum_image hinj]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    congr 1
    omega
  · split_ifs <;> simp

/-- Control: the first six terms. -/
theorem first_terms : (List.range 6).map a = [1, 110, 10100, 1101000, 101010000, 11010100000] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.map_append]
  simp [a_eq, Finset.sum_range_succ]

theorem geom (m : ℕ) : 99 * (∑ j ∈ Finset.range m, (100 : ℤ) ^ j) = 100 ^ m - 1 := by
  have := geom_sum_mul (100 : ℤ) m
  linarith

/-- Barker's closed form, as `198 a(n) = 209·100^n - 9·(-100)^n - 2·10^n`. -/
theorem closed_form (n : ℕ) :
    198 * (a n : ℤ) = 209 * 100 ^ n - 9 * (-100) ^ n - 2 * 10 ^ n := by
  rw [a_eq]
  push_cast
  have hs : ∀ j, (10 : ℤ) ^ (n + 2 * j) = 10 ^ n * 100 ^ j := by
    intro j; rw [pow_add, pow_mul]; norm_num
  simp only [hs, ← Finset.mul_sum]
  rcases Nat.even_or_odd n with hev | hod
  · obtain ⟨m, hm⟩ := hev
    have h1 : n / 2 = m := by omega
    rw [h1, if_neg (by omega)]
    have g := geom (m + 1)
    have e1 : (10 : ℤ) ^ n = 100 ^ m := by rw [hm, ← two_mul, pow_mul]; norm_num
    have e2 : (100 : ℤ) ^ n = 100 ^ m * 100 ^ m := by rw [hm, pow_add]
    have e3 : (-100 : ℤ) ^ n = 100 ^ m * 100 ^ m := by rw [Even.neg_pow ⟨m, hm⟩, e2]
    rw [e1, e2, e3]
    rw [pow_succ] at g
    push_cast
    linear_combination 2 * (100 : ℤ) ^ m * g
  · obtain ⟨m, hm⟩ := hod
    have h1 : n / 2 = m := by omega
    rw [h1, if_pos (by omega)]
    have g := geom (m + 1)
    have e1 : (10 : ℤ) ^ n = 10 * 100 ^ m := by
      rw [hm, pow_succ, pow_mul]; norm_num; ring
    have e2 : (100 : ℤ) ^ n = 100 * (100 ^ m * 100 ^ m) := by
      rw [hm, pow_succ, two_mul, pow_add]; ring
    have e3 : (-100 : ℤ) ^ n = -(100 * (100 ^ m * 100 ^ m)) := by
      rw [Odd.neg_pow ⟨m, hm⟩, e2]
    have e4 : (10 : ℤ) ^ (2 * n) = 100 * (100 ^ m * 100 ^ m) := by
      rw [pow_mul]; norm_num; exact e2
    push_cast
    rw [e4, e1, e2, e3]
    rw [pow_succ] at g
    linear_combination 20 * (100 : ℤ) ^ m * g

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = 10 * a (n - 1) + 10000 * a (n - 2) - 100000 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  have c3 := closed_form (k + 3)
  have c2 := closed_form (k + 2)
  have c1 := closed_form (k + 1)
  have c0 := closed_form k
  simp only [pow_succ] at c3 c2 c1
  have h : 198 * ((a (k + 3) : ℤ) - (10 * a (k + 2) + 10000 * a (k + 1) - 100000 * a k)) = 0 := by
    linear_combination c3 - 10 * c2 - 10000 * c1 + 100000 * c0
  have := (mul_eq_zero.mp h).resolve_left (by norm_num)
  linarith

/-- Barker's g.f. with the denominator cleared:
`A(x) (1 - 10x)(1 - 100x)(1 + 100x) = 1 + 100x - 1000x^2`. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X)) =
    (1 + 100 * X - 1000 * X ^ 2 : PowerSeries ℤ) := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have h10 : (C (10 : ℤ) : PowerSeries ℤ) = 10 := map_ofNat C 10
  have h100 : (C (100 : ℤ) : PowerSeries ℤ) = 100 := map_ofNat C 100
  have h1000 : (C (1000 : ℤ) : PowerSeries ℤ) = 1000 := map_ofNat C 1000
  have h10000 : (C (10000 : ℤ) : PowerSeries ℤ) = 10000 := map_ofNat C 10000
  have h100000 : (C (100000 : ℤ) : PowerSeries ℤ) = 100000 := map_ofNat C 100000
  have hD : A * ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X)) =
      A - C 10 * (A * X ^ 1) - C 10000 * (A * X ^ 2) + C 100000 * (A * X ^ 3) := by
    rw [h10, h10000, h100000]; ring
  have hN : (1 + 100 * X - 1000 * X ^ 2 : PowerSeries ℤ) =
      1 + C 100 * X ^ 1 - C 1000 * X ^ 2 := by rw [h100, h1000]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_one,
    coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge n 3 with h | h
  · have v0 : a 0 = 1 := by simp [a_eq]
    have v1 : a 1 = 110 := by simp [a_eq, Finset.sum_range_succ]
    have v2 : a 2 = 10100 := by simp [a_eq, Finset.sum_range_succ]
    interval_cases n
    · simp only [v0]; norm_num
    · simp only [v0, v1]; norm_num
    · simp only [v0, v1, v2]; norm_num
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, if_false]
    linear_combination r

end OMA.S_oeis_a266844

theorem OMA.solution : type_of% @OMA.S_oeis_a266844.main :=
  ⟨OMA.S_oeis_a266844.closed_form, OMA.S_oeis_a266844.recurrence, OMA.S_oeis_a266844.gf⟩
