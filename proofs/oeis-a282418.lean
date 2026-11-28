import OMAStatements.S_oeis_a282418

/-!
# The horizontal axis of rule 469

At generation 2m the active cells are confined to the diamond of radius m.
The axis is filled inside that diamond. At generation 2m+1 the same interval
is dark and its exterior is lit. The two patterns give the binary place
values, from which the recurrence and generating function follow.
-/

open OMA.S_oeis_a282418

namespace Rule469Axis

private def neighbors (e w n s : Bool) : ℕ := e.toNat + w.toNat + n.toNat + s.toNat

private theorem local_rule : ∀ c e w n s : Bool,
    (469 : ℕ).testBit (c.toNat + 2 * neighbors e w n s) =
      (!c || decide (neighbors e w n s = 3)) := by
  decide

private theorem step (t : ℕ) (x y : ℤ) :
    cell 469 (t+1) x y =
      (!cell 469 t x y || decide (neighbors (cell 469 t (x+1) y) (cell 469 t (x-1) y)
        (cell 469 t x (y+1)) (cell 469 t x (y-1)) = 3)) := by
  exact local_rule _ _ _ _ _

private theorem reflect_y (t : ℕ) (x y : ℤ) :
    cell 469 t x (-y) = cell 469 t x y := by
  induction t generalizing x y with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell, show -y + 1 = -(y-1) by ring, show -y - 1 = -(y+1) by ring, ih]
    ac_rfl

private theorem abs_neighbor (x : ℤ) :
    |x+1| ≤ |x|+1 ∧ |x-1| ≤ |x|+1 ∧ |x| ≤ |x+1|+1 ∧ |x| ≤ |x-1|+1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using abs_add_le x (1 : ℤ)
  · simpa [sub_eq_add_neg] using abs_add_le x (-1 : ℤ)
  · simpa using abs_add_le (x+1) (-1 : ℤ)
  · simpa using abs_add_le (x-1) (1 : ℤ)

private theorem turn_on (t : ℕ) (x y : ℤ) (h : cell 469 t x y = false) :
    cell 469 (t+1) x y = true := by
  simp only [step, h, Bool.not_false, Bool.true_or]

/-- In two generations, the support at even times can advance by one lattice edge. -/
private theorem even_support (m : ℕ) (x y : ℤ) (h : (m : ℤ) < |x| + |y|) :
    cell 469 (2*m) x y = false := by
  induction m generalizing x y with
  | zero =>
    change decide (x = 0 ∧ y = 0) = false
    rw [decide_eq_false_iff_not]
    rintro ⟨rfl, rfl⟩
    simp at h
  | succ m ih =>
    have odd_outside (u v : ℤ) (h' : (m : ℤ) < |u| + |v|) :
        cell 469 (2*m+1) u v = true := turn_on (2*m) u v (ih u v h')
    obtain ⟨_, _, hx_plus, hx_minus⟩ := abs_neighbor x
    obtain ⟨_, _, hy_plus, hy_minus⟩ := abs_neighbor y
    rw [show 2*(m+1) = (2*m+1)+1 by omega, step]
    rw [odd_outside x y (by omega), odd_outside (x+1) y (by omega),
      odd_outside (x-1) y (by omega), odd_outside x (y+1) (by omega),
      odd_outside x (y-1) (by omega)]
    decide

private theorem odd_outside (m : ℕ) (x y : ℤ) (h : (m : ℤ) < |x| + |y|) :
    cell 469 (2*m+1) x y = true := turn_on (2*m) x y (even_support m x y h)

/-- Inside the current axial interval, the number of ON neighbors is never three. -/
private theorem odd_axis_of (m : ℕ)
    (haxis : ∀ x : ℤ, cell 469 (2*m) x 0 = decide (|x| ≤ (m : ℤ))) (x : ℤ) :
    cell 469 (2*m+1) x 0 = decide ((m : ℤ) < |x|) := by
  by_cases hout : (m : ℤ) < |x|
  · simpa only [hout, decide_true] using odd_outside m x 0 (by simpa using hout)
  have hc : cell 469 (2*m) x 0 = true := by simp only [haxis, le_of_not_gt hout, decide_true]
  rw [step, hc, decide_eq_false hout]
  by_cases hint : |x| < (m : ℤ)
  · obtain ⟨hx_plus, hx_minus, _, _⟩ := abs_neighbor x
    have he : cell 469 (2*m) (x+1) 0 = true := by rw [haxis, decide_eq_true (by omega)]
    have hw : cell 469 (2*m) (x-1) 0 = true := by rw [haxis, decide_eq_true (by omega)]
    simp only [he, hw, zero_add, zero_sub, reflect_y]
    cases cell 469 (2*m) x 1 <;> rfl
  · have hn : cell 469 (2*m) x 1 = false := even_support m x 1 (by norm_num; omega)
    simp only [zero_add, zero_sub, reflect_y, hn]
    cases cell 469 (2*m) (x+1) 0 <;> cases cell 469 (2*m) (x-1) 0 <;> rfl

/-- Every even-time row meets the horizontal axis in the full interval of radius m. -/
private theorem even_axis (m : ℕ) (x : ℤ) :
    cell 469 (2*m) x 0 = decide (|x| ≤ (m : ℤ)) := by
  induction m generalizing x with
  | zero =>
    change decide (x = 0 ∧ (0 : ℤ) = 0) = decide (|x| ≤ (0 : ℤ))
    simp
  | succ m ih =>
    have ho := odd_axis_of m ih
    by_cases hout : ((m+1 : ℕ) : ℤ) < |x|
    · rw [even_support (m+1) x 0 (by simpa using hout), decide_eq_false (by omega)]
    rw [decide_eq_true (by omega)]
    by_cases hin : |x| ≤ (m : ℤ)
    · have hon : cell 469 (2*m+1) x 0 = false := by rw [ho, decide_eq_false (by omega)]
      simpa only [show 2*(m+1) = (2*m+1)+1 by omega] using turn_on (2*m+1) x 0 hon
    · have hy_plus : cell 469 (2*m+1) x 1 = true :=
        odd_outside m x 1 (by norm_num; omega)
      have hy_minus : cell 469 (2*m+1) x (-1) = true := by rw [reflect_y, hy_plus]
      have hc : cell 469 (2*m+1) x 0 = true := by rw [ho, decide_eq_true (by omega)]
      rw [show 2*(m+1) = (2*m+1)+1 by omega, step, hc, zero_add, zero_sub, hy_plus, hy_minus]
      by_cases hx : 0 ≤ x
      · have hx' : x = (m : ℤ) + 1 := by rw [abs_of_nonneg hx] at hout hin; omega
        have he : cell 469 (2*m+1) (x+1) 0 = true := by
          rw [ho, abs_of_nonneg (by omega), decide_eq_true (by omega)]
        have hw : cell 469 (2*m+1) (x-1) 0 = false := by
          rw [ho, abs_of_nonneg (by omega), decide_eq_false (by omega)]
        rw [he, hw]
        decide
      · have hx' : x = -((m : ℤ) + 1) := by rw [abs_of_nonpos (by omega)] at hout hin; omega
        have he : cell 469 (2*m+1) (x+1) 0 = false := by
          rw [ho, abs_of_nonpos (by omega), decide_eq_false (by omega)]
        have hw : cell 469 (2*m+1) (x-1) 0 = true := by
          rw [ho, abs_of_nonpos (by omega), decide_eq_true (by omega)]
        rw [he, hw]
        decide

private theorem odd_axis (m : ℕ) (x : ℤ) :
    cell 469 (2*m+1) x 0 = decide ((m : ℤ) < |x|) := odd_axis_of m (even_axis m) x


/-- Read from the least significant end of the binary word. -/
private theorem read_axis (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n+1),
      if cell 469 n ((n-j : ℕ) : ℤ) 0 then (2:ℤ)^j else 0 := by
  let digit (j : ℕ) : ℤ := if cell 469 n ((n-j : ℕ) : ℤ) 0 then (2:ℤ)^j else 0
  change a n = ∑ j ∈ Finset.range (n+1), digit j
  rw [← Finset.sum_range_reflect digit (n+1)]
  unfold a
  apply Finset.sum_congr rfl
  intro j hj
  have h := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp [digit, Nat.sub_sub_self h]

private def ones (k : ℕ) : ℤ := ∑ j ∈ Finset.range k, (2:ℤ)^j

private theorem ones_eq (k : ℕ) : ones k = (2:ℤ)^k-1 := by
  induction k with
  | zero => simp [ones]
  | succ k ih =>
    rw [show ones (k+1) = ones k+2^k by simp [ones, Finset.sum_range_succ], ih, pow_succ]
    ring

/-- The even binary word has m+1 ones followed by m zeros. -/
private theorem even_value (m : ℕ) : a (2*m) = (2:ℤ)*4^m-2^m := by
  have digit (j : ℕ) : cell 469 (2*m) ((2*m-j : ℕ) : ℤ) 0 = decide (m ≤ j) := by
    rw [even_axis, abs_of_nonneg (by positivity)]
    simp only [Nat.cast_le, show 2*m-j ≤ m ↔ m ≤ j by omega]
  rw [read_axis]
  simp only [digit, decide_eq_true_eq]
  rw [show 2*m+1 = m+(m+1) by omega, Finset.sum_range_add]
  have hz : (∑ j ∈ Finset.range m, if m ≤ j then (2:ℤ)^j else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => if_neg (Nat.not_le_of_lt (Finset.mem_range.mp hj))
  rw [hz, zero_add]
  simp (disch := omega) only [if_pos, pow_add, ← Finset.mul_sum]
  change 2^m * ones (m+1) = _
  rw [ones_eq, pow_succ, show (4:ℤ) = 2*2 by decide, mul_pow]
  ring

/-- The odd binary word ends in m+1 ones, with every earlier digit zero. -/
private theorem odd_value (m : ℕ) : a (2*m+1) = (2:ℤ)*2^m-1 := by
  have digit (j : ℕ) :
      cell 469 (2*m+1) ((2*m+1-j : ℕ) : ℤ) 0 = decide (j ≤ m) := by
    rw [odd_axis, abs_of_nonneg (by positivity)]
    simp only [Nat.cast_lt, show m < 2*m+1-j ↔ j ≤ m by omega]
  rw [read_axis]
  simp only [digit, decide_eq_true_eq]
  rw [show 2*m+1+1 = (m+1)+(m+1) by omega, Finset.sum_range_add]
  have hz : (∑ j ∈ Finset.range (m+1), if m+1+j ≤ m then (2:ℤ)^(m+1+j) else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ => if_neg (by omega)
  rw [hz, add_zero, ← show ones (m+1) = (2:ℤ)*2^m-1 by rw [ones_eq, pow_succ, mul_comm]]
  refine Finset.sum_congr rfl fun j hj => if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

private theorem linear_step (b : ℕ → ℤ) (A B C : ℤ)
    (hb : ∀ k, b k = A * 4^k + B * 2^k + C) (k : ℕ) :
    b (k+3) = 7 * b (k+2) - 14 * b (k+1) + 8 * b k := by
  simp only [hb, pow_succ]
  ring

private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℚ) = 7 * a (n-2) - 14 * a (n-4) + 8 * a (n-6) := by
  suffices h : a n = 7*a (n-2) - 14*a (n-4) + 8*a (n-6) by exact_mod_cast h
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (n-6)
  · rw [show n-2 = 2*(k+2) by omega, show n-4 = 2*(k+1) by omega,
        show n-6 = 2*k by omega, show n = 2*(k+3) by omega]
    apply linear_step (fun j => a (2*j)) 2 (-1) 0 _ k
    intro j
    simpa only [neg_one_mul, add_zero, sub_eq_add_neg] using even_value j
  · rw [show n-2 = 2*(k+2)+1 by omega, show n-4 = 2*(k+1)+1 by omega,
        show n-6 = 2*k+1 by omega, show n = 2*(k+3)+1 by omega]
    apply linear_step (fun j => a (2*j+1)) 0 2 (-1) _ k
    intro j
    simpa only [zero_mul, zero_add, sub_eq_add_neg] using odd_value j

private theorem initial_values :
    a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 6 ∧ a 3 = 3 ∧ a 4 = 28 ∧ a 5 = 7 := by
  have h₀ := even_value 0
  have h₁ := odd_value 0
  have h₂ := even_value 1
  have h₃ := odd_value 1
  have h₄ := even_value 2
  have h₅ := odd_value 2
  norm_num at h₀ h₁ h₂ h₃ h₄ h₅
  exact ⟨h₀,h₁,h₂,h₃,h₄,h₅⟩

open PowerSeries

private theorem generating :
    mk (fun n => (a n : ℚ)) * ((1-X)*(1+X)*(1-2*X)*(1+2*X)*(1-2*X^2))
      = 1 + X - X^2 - 4*X^3 := by
  let S := mk (fun n => (a n : ℚ))
  change S * _ = _
  rw [show S * ((1-X)*(1+X)*(1-2*X)*(1+2*X)*(1-2*X^2)) =
        S - C (7:ℚ) * (S * X^2) + C (14:ℚ) * (S * X^4) - C (8:ℚ) * (S * X^6) by
        simp only [map_ofNat]
        ring]
  rw [show (1 + X - X^2 - 4*X^3 : PowerSeries ℚ) =
       C (1:ℚ)*X^0 + C (1:ℚ)*X^1 - C (1:ℚ)*X^2 - C (4:ℚ)*X^3 by
         simp only [map_one, map_ofNat, pow_zero, pow_one, one_mul, mul_one]]
  ext n
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', S, coeff_mk]
  by_cases hn : 6 ≤ n
  · simp (disch := omega) only [if_pos, if_neg, add_zero, sub_zero]
    linarith only [recurrence n hn]
  · obtain ⟨h₀,h₁,h₂,h₃,h₄,h₅⟩ := initial_values
    interval_cases n <;> norm_num [h₀,h₁,h₂,h₃,h₄,h₅]

end Rule469Axis

theorem OMA.solution : type_of% @OMA.S_oeis_a282418.main :=
  ⟨Rule469Axis.recurrence, Rule469Axis.generating⟩
