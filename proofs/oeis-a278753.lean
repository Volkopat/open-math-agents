import OMAStatements.S_oeis_a278753

namespace OMA.S_oeis_a278753

open PowerSeries

/-- State transition and axis lemmas adapted from jleguina’s merged proof of
A278755 (PR 22347). The present sequence uses decimal place values. -/
abbrev state := cell 65



theorem testBit65 (k : ℕ) : Nat.testBit 65 k = decide (k = 0 ∨ k = 6) := by
  rcases Nat.lt_or_ge k 10 with h | h
  · interval_cases k <;> decide
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num : 65 < 2 ^ 10)
      (Nat.pow_le_pow_right (by norm_num) h))]
    simp; omega

/-- Number of ON neighbors. -/
def nb (P : ℤ → ℤ → Prop) [∀ x y, Decidable (P x y)] (x y : ℤ) : ℕ :=
  (if P (x - 1) y then 1 else 0) + (if P (x + 1) y then 1 else 0) +
    (if P x (y - 1) then 1 else 0) + (if P x (y + 1) then 1 else 0)

/-- Rule 65: a cell is ON at the next stage iff it is OFF and has 0 or 3 ON neighbors. -/
theorem step (t : ℕ) (P Q : ℤ → ℤ → Prop) [∀ x y, Decidable (P x y)] [∀ x y, Decidable (Q x y)]
    (hP : ∀ x y, state t x y = decide (P x y))
    (hQ : ∀ x y, Q x y ↔ ¬ P x y ∧ (nb P x y = 0 ∨ nb P x y = 3)) :
    ∀ x y, state (t + 1) x y = decide (Q x y) := by
  intro x y
  show Nat.testBit 65 _ = _
  rw [testBit65]
  simp only [state] at hP
  rw [hP, hP, hP, hP, hP]
  apply Bool.decide_congr
  rw [hQ]
  unfold nb
  by_cases h1 : P x y <;> by_cases h2 : P (x - 1) y <;> by_cases h3 : P (x + 1) y <;>
    by_cases h4 : P x (y - 1) <;> by_cases h5 : P x (y + 1) <;> simp [h1, h2, h3, h4, h5]

def P0 (x y : ℤ) : Prop := x = 0 ∧ y = 0
/-- Odd stage `2r+1`. -/
def O (r : ℕ) (x y : ℤ) : Prop :=
  ¬ (((-1 ≤ x ∧ x ≤ 1) ∧ -(r : ℤ) ≤ y ∧ y ≤ r) ∨ ((-1 ≤ y ∧ y ≤ 1) ∧ -(r : ℤ) ≤ x ∧ x ≤ r) ∨
    (x = 0 ∧ (y = r + 1 ∨ y = -(r : ℤ) - 1)) ∨ (y = 0 ∧ (x = r + 1 ∨ x = -(r : ℤ) - 1)))
/-- The plus with arms `r` (stages 2 and 4). -/
def Pl (r : ℕ) (x y : ℤ) : Prop :=
  (y = 0 ∧ -(r : ℤ) ≤ x ∧ x ≤ r) ∨ (x = 0 ∧ -(r : ℤ) ≤ y ∧ y ≤ r)
/-- Even stage `2r`, `r ≥ 3`. -/
def E (r : ℕ) (x y : ℤ) : Prop :=
  (y = 0 ∧ -(r : ℤ) ≤ x ∧ x ≤ r) ∨ (x = 0 ∧ -(r : ℤ) ≤ y ∧ y ≤ r) ∨
    ((x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1))

instance (x y : ℤ) : Decidable (P0 x y) := by unfold P0; infer_instance
instance (r : ℕ) (x y : ℤ) : Decidable (O r x y) := by unfold O; infer_instance
instance (r : ℕ) (x y : ℤ) : Decidable (Pl r x y) := by unfold Pl; infer_instance
instance (r : ℕ) (x y : ℤ) : Decidable (E r x y) := by unfold E; infer_instance

/- Each transition: an ON cell turns OFF, so only the OFF cells near the pattern need their
neighbors; the region split substitutes a small coordinate before omega. -/

set_option maxHeartbeats 2000000 in
theorem stage1 : ∀ x y, state 1 x y = decide (O 0 x y) := by
  apply step 0 P0 (O 0) (fun x y => rfl)
  intro x y
  by_cases hc : P0 x y
  · have : ¬ O 0 x y := by unfold P0 O at *; push_cast; omega
    simp [hc, this]
  · simp only [hc, not_false_eq_true, true_and]
    have hreg : ((x ≤ -2 ∨ 2 ≤ x) ∨ (y ≤ -2 ∨ 2 ≤ y)) ∨ (x = -1 ∨ x = 0 ∨ x = 1) ∧
        (y = -1 ∨ y = 0 ∨ y = 1) := by omega
    unfold nb
    by_cases h2 : P0 (x - 1) y <;> by_cases h3 : P0 (x + 1) y <;>
      by_cases h4 : P0 x (y - 1) <;> by_cases h5 : P0 x (y + 1) <;>
      simp only [h2, h3, h4, h5, if_true, if_false] <;> norm_num <;>
      simp only [P0, O] at * <;> push_cast at * <;> omega

set_option maxHeartbeats 2000000 in
theorem O_to_Pl (t r : ℕ) (h : ∀ x y, state t x y = decide (O r x y)) (hr : r ≤ 1) :
    ∀ x y, state (t + 1) x y = decide (Pl (r + 1) x y) := by
  apply step t (O r) (Pl (r + 1)) h
  intro x y
  by_cases hc : O r x y
  · have : ¬ Pl (r + 1) x y := by unfold O Pl at *; push_cast at *; omega
    simp [hc, this]
  · simp only [hc, not_false_eq_true, true_and]
    have hreg : x = -1 ∨ x = 0 ∨ x = 1 ∨ y = -1 ∨ y = 0 ∨ y = 1 := by unfold O at hc; omega
    unfold nb
    by_cases h2 : O r (x - 1) y <;> by_cases h3 : O r (x + 1) y <;>
      by_cases h4 : O r x (y - 1) <;> by_cases h5 : O r x (y + 1) <;>
      simp only [h2, h3, h4, h5, if_true, if_false] <;> norm_num <;>
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [O, Pl] at * <;> push_cast at * <;> norm_num at * <;> omega

set_option maxHeartbeats 2000000 in
theorem Pl_to_O (t r : ℕ) (h : ∀ x y, state t x y = decide (Pl r x y)) (hr : 1 ≤ r) (hr' : r ≤ 2) :
    ∀ x y, state (t + 1) x y = decide (O r x y) := by
  apply step t (Pl r) (O r) h
  intro x y
  by_cases hc : Pl r x y
  · have : ¬ O r x y := by unfold O Pl at *; push_cast at *; omega
    simp [hc, this]
  · simp only [hc, not_false_eq_true, true_and]
    have hreg : ((x ≤ -2 ∨ 2 ≤ x) ∧ (y ≤ -2 ∨ 2 ≤ y)) ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ y = -1 ∨
        y = 0 ∨ y = 1 := by omega
    unfold nb
    by_cases h2 : Pl r (x - 1) y <;> by_cases h3 : Pl r (x + 1) y <;>
      by_cases h4 : Pl r x (y - 1) <;> by_cases h5 : Pl r x (y + 1) <;>
      simp only [h2, h3, h4, h5, if_true, if_false] <;> norm_num <;>
      rcases hreg with hfar | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [O, Pl] at * <;> push_cast at * <;> norm_num at * <;> omega

set_option maxHeartbeats 2000000 in
theorem O_to_E (t r : ℕ) (h : ∀ x y, state t x y = decide (O r x y)) (hr : 2 ≤ r) :
    ∀ x y, state (t + 1) x y = decide (E (r + 1) x y) := by
  apply step t (O r) (E (r + 1)) h
  intro x y
  by_cases hc : O r x y
  · have : ¬ E (r + 1) x y := by unfold O E at *; push_cast at *; omega
    simp [hc, this]
  · simp only [hc, not_false_eq_true, true_and]
    have hreg : x = -1 ∨ x = 0 ∨ x = 1 ∨ y = -1 ∨ y = 0 ∨ y = 1 := by unfold O at hc; omega
    unfold nb
    by_cases h2 : O r (x - 1) y <;> by_cases h3 : O r (x + 1) y <;>
      by_cases h4 : O r x (y - 1) <;> by_cases h5 : O r x (y + 1) <;>
      simp only [h2, h3, h4, h5, if_true, if_false] <;> norm_num <;>
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [O, E] at * <;> push_cast at * <;> norm_num at * <;> omega

set_option maxHeartbeats 2000000 in
theorem E_to_O (t r : ℕ) (h : ∀ x y, state t x y = decide (E r x y)) (hr : 3 ≤ r) :
    ∀ x y, state (t + 1) x y = decide (O r x y) := by
  apply step t (E r) (O r) h
  intro x y
  by_cases hc : E r x y
  · have : ¬ O r x y := by unfold O E at *; push_cast at *; omega
    simp [hc, this]
  · simp only [hc, not_false_eq_true, true_and]
    by_cases hfar : (x ≤ -2 ∨ 2 ≤ x) ∧ (y ≤ -2 ∨ 2 ≤ y)
    · have n1 : ¬ E r (x - 1) y := by unfold E; omega
      have n2 : ¬ E r (x + 1) y := by unfold E; omega
      have n3 : ¬ E r x (y - 1) := by unfold E; omega
      have n4 : ¬ E r x (y + 1) := by unfold E; omega
      have hO : O r x y := by unfold O; omega
      unfold nb
      simp [n1, n2, n3, n4, hO]
    · have hreg : x = -1 ∨ x = 0 ∨ x = 1 ∨ y = -1 ∨ y = 0 ∨ y = 1 := by omega
      unfold nb
      by_cases h2 : E r (x - 1) y <;> by_cases h3 : E r (x + 1) y <;>
        by_cases h4 : E r x (y - 1) <;> by_cases h5 : E r x (y + 1) <;>
        simp only [h2, h3, h4, h5, if_true, if_false] <;> norm_num <;>
        rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [O, E] at * <;> push_cast at * <;> norm_num at * <;> omega

theorem stage2 : ∀ x y, state 2 x y = decide (Pl 1 x y) := O_to_Pl 1 0 stage1 (by norm_num)
theorem stage3 : ∀ x y, state 3 x y = decide (O 1 x y) := Pl_to_O 2 1 stage2 le_rfl (by norm_num)
theorem stage4 : ∀ x y, state 4 x y = decide (Pl 2 x y) := O_to_Pl 3 1 stage3 le_rfl
theorem stage5 : ∀ x y, state 5 x y = decide (O 2 x y) :=
  Pl_to_O 4 2 stage4 (by norm_num) le_rfl

theorem pattern (r : ℕ) (hr : 2 ≤ r) :
    (∀ x y, state (2 * r + 1) x y = decide (O r x y)) ∧
      (∀ x y, state (2 * r + 2) x y = decide (E (r + 1) x y)) := by
  induction r, hr using Nat.le_induction with
  | base => exact ⟨stage5, O_to_E 5 2 stage5 le_rfl⟩
  | succ r hr ih =>
    have h1 := E_to_O (2 * r + 2) (r + 1) ih.2 (by omega)
    exact ⟨h1, O_to_E (2 * (r + 1) + 1) (r + 1) h1 (by omega)⟩

theorem pl_axis (r j : ℕ) : Pl r (-(j : ℤ)) 0 ↔ j ≤ r := by
  unfold Pl
  constructor
  · rintro (⟨-, h, -⟩ | ⟨h, -⟩) <;> omega
  · intro h; left; exact ⟨rfl, by omega, by omega⟩

theorem e_axis (r j : ℕ) : E r (-(j : ℤ)) 0 ↔ j ≤ r := by
  unfold E
  constructor
  · rintro (⟨-, h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩) <;> omega
  · intro h; left; exact ⟨rfl, by omega, by omega⟩

theorem o_axis (r j : ℕ) : O r (-(j : ℤ)) 0 ↔ r + 2 ≤ j := by
  unfold O
  constructor
  · intro h
    by_contra h2
    apply h
    rcases Nat.lt_or_ge j 2 with h3 | h3
    · left; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rcases Nat.lt_or_ge j (r + 1) with h4 | h4
      · right; left; exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      · right; right; right; exact ⟨rfl, Or.inr (by omega)⟩
  · intro h h2
    rcases h2 with ⟨⟨h3, -⟩, -⟩ | ⟨-, h3, -⟩ | ⟨h3, -⟩ | ⟨-, h3 | h3⟩ <;> omega

/-- On the negative axis: stage `2r` is ON at `-r..0`, stage `2r+1` from `-(r+2)` outwards. -/
theorem axis_even (r j : ℕ) : state (2 * r) (-(j : ℤ)) 0 = decide (j ≤ r) := by
  rcases Nat.lt_or_ge r 3 with h | h
  · rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
    · show decide (-(j : ℤ) = 0 ∧ (0 : ℤ) = 0) = _
      apply Bool.decide_congr
      constructor
      · rintro ⟨h1, -⟩; omega
      · intro h1; exact ⟨by omega, rfl⟩
    · have key : ∀ x y, state (2 * 1) x y = decide (Pl 1 x y) := stage2
      rw [key]; exact Bool.decide_congr (pl_axis 1 j)
    · have key : ∀ x y, state (2 * 2) x y = decide (Pl 2 x y) := stage4
      rw [key]; exact Bool.decide_congr (pl_axis 2 j)
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have key : ∀ x y, state (2 * (s + 1)) x y = decide (E (s + 1) x y) :=
      (pattern s (by omega)).2
    rw [key]; exact Bool.decide_congr (e_axis (s + 1) j)

theorem axis_odd (r j : ℕ) : state (2 * r + 1) (-(j : ℤ)) 0 = decide (r + 2 ≤ j) := by
  have key : ∀ x y, state (2 * r + 1) x y = decide (O r x y) := by
    rcases Nat.lt_or_ge r 2 with h | h
    · rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · exact stage1
      · exact stage3
    · exact (pattern r h).1
  rw [key]; exact Bool.decide_congr (o_axis r j)


theorem reflect_a (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n+1), if state n (-(j : ℤ)) 0 then (10 : ℤ)^j else 0 := by
  rw [← Finset.sum_range_reflect (fun j => if state n (-(j : ℤ)) 0 then (10 : ℤ)^j else 0)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  simp only [Nat.add_sub_cancel]
  have h : (k : ℤ) - n = -((n-k : ℕ) : ℤ) := by omega
  rw [h]

theorem geom10 (m : ℕ) : 9 * (∑ i ∈ Finset.range m, (10 : ℤ) ^ i) + 1 = 10 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, pow_succ]; linarith

theorem a_even (r : ℕ) : 9 * a (2 * r) + 1 = 10 ^ (r + 1) := by
  rw [reflect_a]
  rw [show 2 * r + 1 = (r + 1) + r by ring, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range r, (if state (2 * r) (-((r + 1 + x : ℕ) : ℤ)) 0 then
      (10 : ℤ) ^ (r + 1 + x) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [axis_even, if_neg (by simp; omega)]
  have h1 : ∑ x ∈ Finset.range (r + 1), (if state (2 * r) (-((x : ℕ) : ℤ)) 0 then
      (10 : ℤ) ^ x else 0) = ∑ x ∈ Finset.range (r + 1), (10 : ℤ) ^ x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [axis_even, if_pos (by simp; omega)]
  rw [h0, h1, add_zero]
  exact geom10 (r + 1)

/-- Odd stages contain the block of decimal powers from r+2 through 2r+1. -/
theorem a_odd (r : ℕ) : 9 * a (2 * r + 1) + 10 ^ (r + 2) = 10 ^ (2 * r + 2) := by
  rw [reflect_a]
  rw [show 2 * r + 1 + 1 = (r + 2) + r by ring, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range (r + 2), (if state (2 * r + 1) (-((x : ℕ) : ℤ)) 0 then
      (10 : ℤ) ^ x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    rw [axis_odd, if_neg (by simp; omega)]
  have h1 : ∑ x ∈ Finset.range r, (if state (2 * r + 1) (-((r + 2 + x : ℕ) : ℤ)) 0 then
      (10 : ℤ) ^ (r + 2 + x) else 0) = ∑ x ∈ Finset.range r, (10 : ℤ) ^ (r + 2) * (10 : ℤ) ^ x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [axis_odd, if_pos (by simp), pow_add]
  rw [h0, h1, zero_add, ← Finset.mul_sum]
  have g := geom10 r
  calc 9 * ((10 : ℤ) ^ (r + 2) * (∑ x ∈ Finset.range r, (10 : ℤ) ^ x)) + (10 : ℤ) ^ (r + 2)
      = (10 : ℤ) ^ (r + 2) * (9 * (∑ x ∈ Finset.range r, (10 : ℤ) ^ x) + 1) := by ring
    _ = (10 : ℤ) ^ (r + 2) * (10 : ℤ) ^ r := by rw [g]
    _ = (10 : ℤ) ^ (r + 2 + r) := by rw [← pow_add]


theorem closed_even (r : ℕ) : 9 * a (2*r) = 10 * 10^r - 1 := by
  have h := a_even r
  rw [pow_succ] at h
  linarith

theorem closed_odd (r : ℕ) : 9 * a (2*r+1) = 100 * 100^r - 100 * 10^r := by
  have h := a_odd r
  rw [show 2*r+2 = 2*(r+1) by omega, pow_mul, pow_add] at h
  norm_num at h
  rw [pow_succ] at h
  linarith

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 111 * a (n - 2) - 1110 * a (n - 4) + 1000 * a (n - 6) := by
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
    rw [hr, show s + 3 + (s + 3) - 2 = 2 * (s + 2) by omega,
      show s + 3 + (s + 3) - 4 = 2 * (s + 1) by omega,
      show s + 3 + (s + 3) - 6 = 2 * s by omega, show s + 3 + (s + 3) = 2 * (s + 3) by omega]
    have h0 := closed_even s
    have h1 := closed_even (s+1)
    have h2 := closed_even (s+2)
    have h3 := closed_even (s+3)
    simp only [pow_succ] at h1 h2 h3
    linarith
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
    rw [hr, show 2 * (s + 3) + 1 - 2 = 2 * (s + 2) + 1 by omega,
      show 2 * (s + 3) + 1 - 4 = 2 * (s + 1) + 1 by omega,
      show 2 * (s + 3) + 1 - 6 = 2 * s + 1 by omega]
    have h0 := closed_odd s
    have h1 := closed_odd (s+1)
    have h2 := closed_odd (s+2)
    have h3 := closed_odd (s+3)
    simp only [pow_succ] at h1 h2 h3
    linarith

/-- Wu’s generating function, with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℚ)) * (1000 * X ^ 6 - 1110 * X ^ 4 + 111 * X ^ 2 - 1) =
    (1000 * X ^ 5 - 1000 * X ^ 3 + 100 * X ^ 2 - 1 : PowerSeries ℚ) := by
  set A : PowerSeries ℚ := mk (fun n => (a n : ℚ)) with hA
  have h1000 : (C (1000 : ℚ) : PowerSeries ℚ) = 1000 := map_ofNat C 1000
  have h1110 : (C (1110 : ℚ) : PowerSeries ℚ) = 1110 := map_ofNat C 1110
  have h111 : (C (111 : ℚ) : PowerSeries ℚ) = 111 := map_ofNat C 111
  have h100 : (C (100 : ℚ) : PowerSeries ℚ) = 100 := map_ofNat C 100
  have hD : A * (1000 * X ^ 6 - 1110 * X ^ 4 + 111 * X ^ 2 - 1) =
      C 1000 * (A * X ^ 6) - C 1110 * (A * X ^ 4) + C 111 * (A * X ^ 2) - A := by
    rw [h1000, h1110, h111]; ring
  have hN : (1000 * X ^ 5 - 1000 * X ^ 3 + 100 * X ^ 2 - 1 : PowerSeries ℚ) =
      C 1000 * X ^ 5 - C 1000 * X ^ 3 + C 100 * X ^ 2 - 1 := by rw [h1000, h100]
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_one,
    coeff_C]
  have v0 : a 0 = 1 := by have := a_even 0; norm_num at this; omega
  have v1 : a 1 = 0 := by have := a_odd 0; norm_num at this; omega
  have v2 : a 2 = 11 := by have := a_even 1; norm_num at this; omega
  have v3 : a 3 = 1000 := by have := a_odd 1; norm_num at this; omega
  have v4 : a 4 = 111 := by have := a_even 2; norm_num at this; omega
  have v5 : a 5 = 110000 := by have := a_odd 2; norm_num at this; omega
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5]
  · have r := recurrence n (by omega)
    simp only [show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega, show 6 ≤ n by omega, if_true, show n ≠ 0 by omega,
      show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_false]
    have rq : (a n : ℚ) = 111 * (a (n-2) : ℚ) - 1110 * (a (n-4) : ℚ) + 1000 * (a (n-6) : ℚ) := by exact_mod_cast r
    linear_combination -rq


end OMA.S_oeis_a278753

theorem OMA.solution : type_of% @OMA.S_oeis_a278753.main := by
  refine ⟨?_, OMA.S_oeis_a278753.gf⟩
  intro n hn
  exact_mod_cast OMA.S_oeis_a278753.recurrence n hn
