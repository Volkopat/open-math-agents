import OMAStatements.S_oeis_a288661

/-!
# The diagonal of rule 493

At odd times all sites of odd coordinate sum are on. On the complementary
sublattice, rotated coordinates turn the diagonal into a coordinate axis.
The interval of holes there and the alternating row beside it determine the
digits at every time. Summing their place values gives both OEIS formulas.
-/

open OMA.S_oeis_a288661

namespace Rule493Diagonal

/-- The two colors of the square lattice in coordinates rotated by 45 degrees. -/
private def vertex (t : ℕ) (u v : ℤ) := cell 493 t (u + v) (u - v)
private def face (t : ℕ) (u v : ℤ) := cell 493 t (u + v + 1) (u - v)

private def rule (c e w n s : Bool) : Bool :=
  (493 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat))

private theorem vertex_step (t : ℕ) (u v : ℤ) :
    vertex (t + 1) u v = rule (vertex t u v) (face t u v) (face t (u-1) (v-1))
      (face t u (v-1)) (face t (u-1) v) := by
  simp only [vertex, face, cell, rule]
  repeat' first | (solve | omega) | congr 1

private theorem face_step (t : ℕ) (u v : ℤ) :
    face (t + 1) u v = rule (face t u v) (vertex t (u+1) (v+1)) (vertex t u v)
      (vertex t (u+1) v) (vertex t u (v+1)) := by
  simp only [vertex, face, cell, rule]
  repeat' first | (solve | omega) | congr 1

private def mixed (a b c d : Bool) : Bool := !((a == b) && (a == c) && (a == d))

private theorem complement_rule : ∀ c, rule c true true true true = !c := by decide
private theorem boundary_rule : ∀ a b c d : Bool,
    rule true (!d) (!a) (!b) (!c) = mixed a b c d := by decide
private theorem fill_rule : ∀ a b c d : Bool,
    rule (mixed a b c d) d a b c = true := by decide

/-- Marks are the holes on the vertex sublattice at odd times. -/
private def mark (m : ℕ) (u v : ℤ) : Bool := !(vertex (2*m+1) u v)

private theorem even_vertex_of (m : ℕ) (hf : ∀ u v, face (2*m+1) u v = true) (u v : ℤ) :
    vertex (2*m+2) u v = mark m u v := by
  rw [show 2*m+2 = (2*m+1)+1 by omega, vertex_step]
  simp only [hf, complement_rule, mark]

private theorem even_face_of (m : ℕ) (hf : ∀ u v, face (2*m+1) u v = true) (u v : ℤ) :
    face (2*m+2) u v = mixed (mark m u v) (mark m (u+1) v)
      (mark m u (v+1)) (mark m (u+1) (v+1)) := by
  rw [show 2*m+2 = (2*m+1)+1 by omega, face_step, hf]
  simpa only [mark, Bool.not_not] using boundary_rule (mark m u v) (mark m (u+1) v)
    (mark m u (v+1)) (mark m (u+1) (v+1))

private theorem face_zero (u v : ℤ) : face 0 u v = false := by
  simp [face, cell]
  omega

private theorem vertex_zero (u v : ℤ) : vertex 0 u v = decide (u = 0 ∧ v = 0) := by
  simp only [vertex, cell]
  congr 1
  exact propext (by omega)

private theorem initial_face (u v : ℤ) : face 1 u v = true := by
  rw [show 1 = 0 + 1 by decide, face_step]
  simp only [face_zero, vertex_zero]
  by_cases hu : u = 0 <;> by_cases hv : v = 0 <;>
    by_cases hx : u + 1 = 0 <;> by_cases hy : v + 1 = 0 <;>
    first | omega | (simp [rule, hu, hv, hx, hy] <;> rfl)

private theorem odd_face (m : ℕ) : ∀ u v : ℤ, face (2*m+1) u v = true := by
  induction m with
  | zero => exact initial_face
  | succ m ih =>
    intro u v
    rw [show 2*(m+1)+1 = (2*m+2)+1 by omega, face_step, even_face_of m ih]
    simp only [even_vertex_of m ih, fill_rule]

private theorem even_vertex (m : ℕ) (u v : ℤ) :
    vertex (2*m+2) u v = mark m u v := even_vertex_of m (odd_face m) u v

/-- One two-generation update on the vertex sublattice, displayed by rows. -/
private def advance (sw s se w c e nw n ne : Bool) : Bool :=
  !(rule c (mixed c e n ne) (mixed sw s w c) (mixed s se c e) (mixed w c nw n))

private theorem mark_step (m : ℕ) (u v : ℤ) :
    mark (m+1) u v =
      advance (mark m (u-1) (v-1)) (mark m u (v-1)) (mark m (u+1) (v-1))
        (mark m (u-1) v) (mark m u v) (mark m (u+1) v)
        (mark m (u-1) (v+1)) (mark m u (v+1)) (mark m (u+1) (v+1)) := by
  change (!(vertex (2*(m+1)+1) u v)) = _
  rw [show 2*(m+1)+1 = (2*m+2)+1 by omega, vertex_step, even_vertex]
  simp only [even_face_of m (odd_face m), sub_add_cancel, advance]

private theorem initial_mark (u v : ℤ) : mark 0 u v = decide (u = 0 ∧ v = 0) := by
  change (!(vertex (0+1) u v)) = _
  simp only [vertex_step, face_zero, vertex_zero]
  cases decide (u = 0 ∧ v = 0) <;> rfl

private theorem cell_swap (t : ℕ) (i j : ℤ) : cell 493 t j i = cell 493 t i j := by
  induction t generalizing i j with
  | zero => simp [cell, and_comm]
  | succ t ih =>
    simp only [cell, ih i j, ih i (j+1), ih i (j-1), ih (i+1) j, ih (i-1) j]
    ac_rfl

private theorem cell_neg_y (t : ℕ) (i j : ℤ) : cell 493 t i (-j) = cell 493 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell, show -j + 1 = -(j-1) by ring, show -j - 1 = -(j+1) by ring, ih]
    ac_rfl

private theorem mark_flip (m : ℕ) (u v : ℤ) : mark m u (-v) = mark m u v := by
  unfold mark vertex
  rw [show u + -v = u-v by ring, show u - -v = u+v by ring, cell_swap]

private theorem mark_swap (m : ℕ) (u v : ℤ) : mark m v u = mark m u v := by
  unfold mark vertex
  rw [add_comm v u, show v-u = -(u-v) by ring, cell_neg_y]

private theorem mark_left (m : ℕ) (u v : ℤ) : mark m (-u) v = mark m u v := by
  rw [mark_swap m v (-u), mark_flip, mark_swap m u v]

private theorem edge_empty : ∀ a : Bool, advance a false false false false false false false false = false := by decide

/-- Beyond the advancing front at most its southwest neighbor can be marked. -/
private theorem outside (m : ℕ) (u v : ℤ) (h : (m : ℤ) < u + v) :
    mark m u v = false := by
  induction m generalizing u v with
  | zero =>
    rw [initial_mark, decide_eq_false_iff_not]
    omega
  | succ m ih =>
    rw [mark_step]
    simp (disch := omega) only [ih, edge_empty]

private def axisValue (m : ℕ) (u : ℤ) : Bool :=
  if -(m : ℤ) ≤ u ∧ u ≤ m then true else false

private def stripValue (m : ℕ) (u : ℤ) : Bool :=
  if -(m : ℤ) < u ∧ u < m ∧ u % 2 = 0 then true else false

private theorem axis_update (m : ℕ) (u : ℤ) :
    advance (stripValue m (u-1)) (stripValue m u) (stripValue m (u+1))
      (axisValue m (u-1)) (axisValue m u) (axisValue m (u+1))
      (stripValue m (u-1)) (stripValue m u) (stripValue m (u+1)) = axisValue (m+1) u := by
  unfold axisValue stripValue
  push_cast
  repeat' first | (solve | rfl) | (solve | omega) | split

private theorem strip_stays_dark : ∀ a b c d e f : Bool,
    advance a b c true false true d e f = false := by decide
private theorem strip_stays_lit : ∀ a b c d e f : Bool,
    advance a b c false true false d e f = true := by decide
private theorem dark_at_edge : ∀ d : Bool,
    advance true true true true false false d false false = false := by decide

/-- Inside the alternating row, opposite neighbors preserve the center.
At the advancing end the two boundary positions must be checked separately. -/
private theorem strip_positive (m : ℕ)
    (ha : ∀ u, mark m u 0 = axisValue m u)
    (hs : ∀ u, mark m u 1 = stripValue m u) (u : ℤ) (hu : 0 < u) :
    mark (m+1) u 1 = stripValue (m+1) u := by
  by_cases hfar : (m : ℤ) < u
  · rw [outside (m+1) u 1 (by push_cast; omega)]
    simp [stripValue]
    omega
  rw [mark_step]
  simp only [show (1:ℤ)-1 = 0 by rfl, show (1:ℤ)+1 = 2 by rfl, ha, hs]
  by_cases hp : u % 2 = 0 <;>
    rcases lt_trichotomy (u+1) (m:ℤ) with h | h | h <;>
    simp (disch := omega) only [axisValue, stripValue, Nat.cast_succ, if_pos, if_neg,
      outside, strip_stays_dark, strip_stays_lit, dark_at_edge] <;> rfl

/-- The marked diagonal is an interval. The adjacent row marks its alternating interior sites.
These two rows and the front bound suffice to close the induction. -/
private theorem axis_strip (m : ℕ) :
    (∀ u, mark m u 0 = axisValue m u) ∧ (∀ u, mark m u 1 = stripValue m u) := by
  induction m with
  | zero =>
    constructor <;> intro u <;> rw [initial_mark]
    · by_cases h : u = 0
      · subst u
        decide
      · simp [axisValue, h]
        omega
    · simp [stripValue]
      omega
  | succ m ih =>
    obtain ⟨ha, hs⟩ := ih
    have ax (u : ℤ) : mark (m+1) u 0 = axisValue (m+1) u := by
      rw [mark_step]
      simp only [zero_sub, zero_add, mark_flip m _ 1, ha, hs, axis_update]
    refine ⟨ax, fun u => ?_⟩
    rcases lt_trichotomy u 0 with hu | rfl | hu
    · rw [← neg_neg u, mark_left, strip_positive m ha hs (-u) (by omega)]
      simp only [neg_neg]
      unfold stripValue
      split <;> split <;> first | rfl | omega
    · rw [mark_swap (m+1) 1 0, ax]
      rw [axisValue, stripValue, if_pos (by omega), if_pos (by norm_num; omega)]
    · exact strip_positive m ha hs u hu

private theorem diagonal_odd (m u : ℕ) :
    cell 493 (2*m+1) u u = decide (m < u) := by
  have h := (axis_strip m).1 (u:ℤ)
  by_cases le : u ≤ m
  · have lt : ¬m < u := by omega
    simpa (disch := omega) [mark, vertex, axisValue, le, lt] using h
  · have lt : m < u := by omega
    simpa (disch := omega) [mark, vertex, axisValue, le, lt] using h

private theorem diagonal_even (m u : ℕ) :
    cell 493 (2*m+2) u u = decide (u ≤ m) := by
  have h := (even_vertex m (u:ℤ) 0).trans ((axis_strip m).1 (u:ℤ))
  by_cases le : u ≤ m <;>
    simpa (disch := omega) [vertex, axisValue, le] using h

private theorem read_diagonal (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n+1), if cell 493 n (j:ℤ) j then (10:ℤ)^j else 0 := by
  let digit (j : ℕ) : ℤ := if cell 493 n (j:ℤ) j then (10:ℤ)^j else 0
  change a n = ∑ j ∈ Finset.range (n+1), digit j
  rw [← Finset.sum_range_reflect digit (n+1)]
  unfold a
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp [digit, Nat.cast_sub (show j ≤ n by omega)]

private def ones (k : ℕ) : ℤ := ∑ j ∈ Finset.range k, (10:ℤ)^j

private theorem nines (k : ℕ) : 9 * ones k = (10:ℤ)^k - 1 := by
  induction k with
  | zero => simp [ones]
  | succ k ih =>
    rw [show ones (k+1) = ones k + 10^k by simp [ones, Finset.sum_range_succ], pow_succ]
    linarith

private theorem odd_value (m : ℕ) : 9 * a (2*m+1) = (100:ℤ)^(m+1) - 10^(m+1) := by
  have hs : a (2*m+1) = 10^(m+1) * ones (m+1) := by
    rw [read_diagonal]
    simp only [diagonal_odd, decide_eq_true_eq]
    rw [show 2*m+1+1 = (m+1)+(m+1) by omega, Finset.sum_range_add]
    have hz : (∑ j ∈ Finset.range (m+1), if m < j then (10:ℤ)^j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (by have := Finset.mem_range.mp hj; omega)
    rw [hz, zero_add]
    simp (disch := omega) only [if_pos, pow_add, ones, Finset.mul_sum]
  rw [hs, mul_left_comm, nines, show (100:ℤ) = 10*10 by norm_num, mul_pow]
  ring

private theorem even_value (m : ℕ) : 9 * a (2*m+2) = (10:ℤ)^(m+1) - 1 := by
  suffices h : a (2*m+2) = ones (m+1) by rw [h, nines]
  rw [read_diagonal]
  simp only [diagonal_even, decide_eq_true_eq]
  rw [show 2*m+2+1 = (m+1)+(m+2) by omega, Finset.sum_range_add]
  have hz : (∑ j ∈ Finset.range (m+2), if m+1+j ≤ m then (10:ℤ)^(m+1+j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact if_neg (by omega)
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact if_pos (by have := Finset.mem_range.mp hj; omega)

/-- The characteristic roots for each of the two parity subsequences are 1, 10 and 100. -/
private theorem linear_step (b : ℕ → ℤ) (A B C : ℤ)
    (hb : ∀ k, 9 * b k = A * 100^(k+1) + B * 10^(k+1) + C) (k : ℕ) :
    b (k+3) = 111 * b (k+2) - 1110 * b (k+1) + 1000 * b k := by
  have h₀ := hb k
  have h₁ := hb (k+1)
  have h₂ := hb (k+2)
  have h₃ := hb (k+3)
  simp only [pow_succ] at h₀ h₁ h₂ h₃
  linarith only [h₀,h₁,h₂,h₃]

private theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = 111 * a (n-2) - 1110 * a (n-4) + 1000 * a (n-6) := by
  suffices h : a n = 111 * a (n-2) - 1110 * a (n-4) + 1000 * a (n-6) by exact_mod_cast h
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (n-7)
  · rw [show n-2 = 2*(k+2)+1 by omega, show n-4 = 2*(k+1)+1 by omega,
        show n-6 = 2*k+1 by omega, show n = 2*(k+3)+1 by omega]
    apply linear_step (fun j => a (2*j+1)) 1 (-1) 0 _ k
    intro j
    simpa only [one_mul, neg_one_mul, add_zero, sub_eq_add_neg] using odd_value j
  · rw [show n-2 = 2*(k+2)+2 by omega, show n-4 = 2*(k+1)+2 by omega,
        show n-6 = 2*k+2 by omega, show n = 2*(k+3)+2 by omega]
    apply linear_step (fun j => a (2*j+2)) 0 1 (-1) _ k
    intro j
    simpa only [zero_mul, zero_add, one_mul, sub_eq_add_neg] using even_value j

private theorem initial_values :
    a 0 = 1 ∧ a 1 = 10 ∧ a 2 = 1 ∧ a 3 = 1100 ∧ a 4 = 11 ∧
      a 5 = 111000 ∧ a 6 = 111 := by
  refine ⟨by decide, ?_⟩
  have h₁ := odd_value 0
  have h₂ := even_value 0
  have h₃ := odd_value 1
  have h₄ := even_value 1
  have h₅ := odd_value 2
  have h₆ := even_value 2
  norm_num at h₁ h₂ h₃ h₄ h₅ h₆
  omega

open PowerSeries

private theorem generating :
    mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10*X) * (1 + 10*X) * (1 - 10*X^2))
      = 1 + 10*X - 110*X^2 - 10*X^3 + 1010*X^4 - 1000*X^6 := by
  let S := mk (fun n => (a n : ℚ))
  change S * _ = _
  rw [show S * ((1-X)*(1+X)*(1-10*X)*(1+10*X)*(1-10*X^2)) =
        S - C (111:ℚ) * (S * X^2) + C (1110:ℚ) * (S * X^4) - C (1000:ℚ) * (S * X^6) by
        simp only [map_ofNat]
        ring]
  rw [show (1 + 10*X - 110*X^2 - 10*X^3 + 1010*X^4 - 1000*X^6 : PowerSeries ℚ) =
       C (1:ℚ)*X^0 + C (10:ℚ)*X^1 - C (110:ℚ)*X^2 - C (10:ℚ)*X^3 +
         C (1010:ℚ)*X^4 - C (1000:ℚ)*X^6 by
         simp only [map_one, map_ofNat, pow_zero, pow_one, mul_one]]
  ext n
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', S, coeff_mk]
  by_cases hn : 7 ≤ n
  · simp (disch := omega) only [if_pos, if_neg, add_zero, sub_zero]
    linarith only [recurrence n hn]
  · obtain ⟨h₀,h₁,h₂,h₃,h₄,h₅,h₆⟩ := initial_values
    interval_cases n <;> norm_num [h₀,h₁,h₂,h₃,h₄,h₅,h₆]

end Rule493Diagonal

theorem OMA.solution : type_of% @OMA.S_oeis_a288661.main :=
  ⟨Rule493Diagonal.generating, Rule493Diagonal.recurrence⟩
