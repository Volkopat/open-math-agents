import OMAStatements.S_oeis_a266790

namespace OMA.S_oeis_a266790

open PowerSeries




theorem eca61 (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    eca 61 (decide A) (decide B) (decide C) = decide (¬ ((A ∧ B) ∨ (¬A ∧ ¬B ∧ C))) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC] <;> decide

theorem step (t : ℕ) (P Q : ℤ → Prop) [∀ i, Decidable (P i)] [∀ i, Decidable (Q i)]
    (hP : ∀ i, state t i = decide (P i))
    (hQ : ∀ i, (Q i ↔ ¬ ((P (i - 1) ∧ P i) ∨ (¬ P (i - 1) ∧ ¬ P i ∧ P (i + 1))))) :
    ∀ i, state (t + 1) i = decide (Q i) := by
  intro i
  show eca 61 _ _ _ = _
  rw [hP, hP, hP, eca61]
  exact Bool.decide_congr (hQ i).symm

theorem stage1 : ∀ i, state 1 i = decide (¬ i = -1) :=
  step 0 (fun i => i = 0) _ (fun i => rfl) (fun i => by omega)

theorem stage2 : ∀ i, state 2 i = decide (i = -1 ∨ i = 0) :=
  step 1 _ _ stage1 (fun i => by omega)

theorem stage3 : ∀ i, state 3 i = decide (¬ (i = -2 ∨ i = 0)) :=
  step 2 _ _ stage2 (fun i => by omega)

theorem stage4 : ∀ i, state 4 i = decide (-2 ≤ i ∧ i ≤ 1) :=
  step 3 _ _ stage3 (fun i => by omega)

/-- Odd stages `2s+1`, `s ≥ 2`. -/
def Odd' (s : ℕ) (i : ℤ) : Prop := ¬ (i = -(s : ℤ) - 1 ∨ (-(s : ℤ) + 1 ≤ i ∧ i ≤ -(s : ℤ) + 3))
/-- Even stages `2s`, `s ≥ 3`. -/
def Even' (s : ℕ) (i : ℤ) : Prop := (-(s : ℤ) ≤ i ∧ i ≤ -(s : ℤ) + 3) ∨ i = -(s : ℤ) + 5

instance (s : ℕ) (i : ℤ) : Decidable (Odd' s i) := by unfold Odd'; infer_instance
instance (s : ℕ) (i : ℤ) : Decidable (Even' s i) := by unfold Even'; infer_instance

theorem stage5 : ∀ i, state 5 i = decide (Odd' 2 i) :=
  step 4 _ _ stage4 (fun i => by unfold Odd'; push_cast; omega)

theorem odd_to_even (s : ℕ) (hs : 2 ≤ s) (h : ∀ i, state (2 * s + 1) i = decide (Odd' s i)) :
    ∀ i, state (2 * (s + 1)) i = decide (Even' (s + 1) i) :=
  step (2 * s + 1) _ _ h (fun i => by unfold Odd' Even'; push_cast; omega)

theorem even_to_odd (s : ℕ) (hs : 3 ≤ s) (h : ∀ i, state (2 * s) i = decide (Even' s i)) :
    ∀ i, state (2 * s + 1) i = decide (Odd' s i) :=
  step (2 * s) _ _ h (fun i => by unfold Odd' Even'; push_cast; omega)

theorem pattern (s : ℕ) (hs : 2 ≤ s) :
    (∀ i, state (2 * s + 1) i = decide (Odd' s i)) ∧
      (∀ i, state (2 * (s + 1)) i = decide (Even' (s + 1) i)) := by
  induction s, hs using Nat.le_induction with
  | base => exact ⟨stage5, odd_to_even 2 le_rfl stage5⟩
  | succ s hs ih =>
    have h1 := even_to_odd (s + 1) (by omega) ih.2
    exact ⟨h1, odd_to_even (s + 1) (by omega) h1⟩

/-- The center column. -/
theorem center (t : ℕ) (ht : 11 ≤ t) : state t 0 = decide (t % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · obtain ⟨s, rfl⟩ : ∃ s, t = 2 * (s + 1) := ⟨t / 2 - 1, by omega⟩
    rw [(pattern s (by omega)).2]
    apply Bool.decide_congr; unfold Even'; push_cast; omega
  · obtain ⟨s, rfl⟩ : ∃ s, t = 2 * s + 1 := ⟨t / 2, by omega⟩
    rw [(pattern s (by omega)).1]
    apply Bool.decide_congr; unfold Odd'; push_cast; omega

theorem a_succ (n : ℕ) : a (n + 1) = 10 * a n + (if state (n + 1) 0 then 1 else 0) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  split_ifs
  · rw [show n + 1 - t = (n - t) + 1 by omega, pow_succ]; ring
  · simp

theorem c1 : state 1 0 = true := by rw [stage1]; decide
theorem c2 : state 2 0 = true := by rw [stage2]; decide
theorem c3 : state 3 0 = false := by rw [stage3]; decide
theorem c4 : state 4 0 = true := by rw [stage4]; decide
theorem c5 : state 5 0 = false := by rw [stage5]; decide
theorem c6 : state 6 0 = true := by rw [(pattern 2 le_rfl).2]; decide
theorem c7 : state 7 0 = false := by rw [(pattern 3 (by norm_num)).1]; decide
theorem c8 : state 8 0 = false := by rw [(pattern 3 (by norm_num)).2]; decide
theorem c9 : state 9 0 = true := by rw [(pattern 4 (by norm_num)).1]; decide
theorem c10 : state 10 0 = true := by rw [(pattern 4 (by norm_num)).2]; decide

theorem a0 : a 0 = 1 := by simp [a]; decide
theorem a1 : a 1 = 11 := by rw [a_succ, a0, c1]; rfl
theorem a2 : a 2 = 111 := by rw [a_succ, a1, c2]; rfl
theorem a3 : a 3 = 1110 := by rw [a_succ, a2, c3]; rfl
theorem a4 : a 4 = 11101 := by rw [a_succ, a3, c4]; rfl
theorem a5 : a 5 = 111010 := by rw [a_succ, a4, c5]; rfl
theorem a6 : a 6 = 1110101 := by rw [a_succ, a5, c6]; rfl
theorem a7 : a 7 = 11101010 := by rw [a_succ, a6, c7]; rfl
theorem a8 : a 8 = 111010100 := by rw [a_succ, a7, c8]; rfl
theorem a9 : a 9 = 1110101001 := by rw [a_succ, a8, c9]; rfl
theorem a10 : a 10 = 11101010011 := by rw [a_succ, a9, c10]; rfl
theorem a11 : a 11 = 111010100111 := by rw [a_succ, a10, center 11 le_rfl]; rfl
theorem a12 : a 12 = 1110101001110 := by rw [a_succ, a11, center 12 (by norm_num)]; rfl

/-- Barker's closed form for `n > 9`:
`198 a(n) = -9(-1)^n + 1098999991099·2^(n-9)·5^(n-10) - 11`. -/
theorem closed_form (n : ℕ) (hn : 9 < n) :
    198 * (a n : ℤ) = -9 * (-1) ^ n + 1098999991099 * 2 ^ (n - 9) * 5 ^ (n - 10) - 11 := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [a10]
    norm_num
  | succ n hn ih =>
    rw [a_succ, center (n + 1) (by omega)]
    rw [show n + 1 - 9 = (n - 9) + 1 by omega, show n + 1 - 10 = (n - 10) + 1 by omega,
      pow_succ (2 : ℤ) (n - 9), pow_succ (5 : ℤ) (n - 10)]
    rcases Nat.even_or_odd n with hev | hod
    · have h1 : (n + 1) % 2 = 1 := by have := Nat.even_iff.mp hev; omega
      have hneg : ((-1 : ℤ)) ^ (n + 1) = -1 := by
        rw [pow_succ, Even.neg_one_pow hev]; norm_num
      rw [Even.neg_one_pow hev] at ih
      rw [hneg]
      simp only [h1, decide_true, if_true]
      push_cast
      linear_combination 10 * ih
    · have h1 : ¬ (n + 1) % 2 = 1 := by have := Nat.odd_iff.mp hod; omega
      have hneg : ((-1 : ℤ)) ^ (n + 1) = 1 := by
        rw [pow_succ, Odd.neg_one_pow hod]; norm_num
      rw [Odd.neg_one_pow hod] at ih
      rw [hneg]
      simp only [h1, decide_false, if_false, Bool.false_eq_true]
      push_cast
      linear_combination 10 * ih

/-- Barker's g.f. with the denominator cleared:
`A(x) (1-x)(1+x)(1-10x) = 1 + x - x^3 - x^8 + x^9 + x^10 - x^12`. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X)) =
    (1 + X - X ^ 3 - X ^ 8 + X ^ 9 + X ^ 10 - X ^ 12 : PowerSeries ℤ) := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have h10 : (C (10 : ℤ) : PowerSeries ℤ) = 10 := map_ofNat C 10
  have hD : A * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      A - C 10 * (A * X ^ 1) - A * X ^ 2 + C 10 * (A * X ^ 3) := by rw [h10]; ring
  have hN : (1 + X - X ^ 3 - X ^ 8 + X ^ 9 + X ^ 10 - X ^ 12 : PowerSeries ℤ) =
      1 + X ^ 1 - X ^ 3 - X ^ 8 + X ^ 9 + X ^ 10 - X ^ 12 := by ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_one,
    coeff_X_pow]
  rcases Nat.lt_or_ge n 13 with h | h
  · interval_cases n <;> simp [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
  · have e1 : (a n : ℤ) = 10 * a (n - 1) + (if n % 2 = 1 then 1 else 0) := by
      have := a_succ (n - 1)
      rw [show n - 1 + 1 = n by omega, center n (by omega)] at this
      rw [this]; push_cast; simp
    have e3 : (a (n - 2) : ℤ) = 10 * a (n - 3) + (if n % 2 = 1 then 1 else 0) := by
      have := a_succ (n - 3)
      rw [show n - 3 + 1 = n - 2 by omega, center (n - 2) (by omega),
        show (n - 2) % 2 = n % 2 by omega] at this
      rw [this]; push_cast; simp
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega, show n ≠ 8 by omega,
      show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 12 by omega, if_false]
    linear_combination e1 - e3

end OMA.S_oeis_a266790

theorem OMA.solution : type_of% @OMA.S_oeis_a266790.main :=
  ⟨OMA.S_oeis_a266790.closed_form, OMA.S_oeis_a266790.gf⟩
