import OMAStatements.S_oeis_a279872

/-!
Robert Price introduced A279872, and Chai Wah Wu conjectured the recurrence and the g.f.
Source: https://oeis.org/A279872

Proof idea: outside the light cone `|x| + |y| > t` every cell shows the background, which is ON at
odd stages and OFF at even ones; the automaton is symmetric under `y ↦ -y`, so the two neighbors
`(x, 1)` and `(x, -1)` of an axis cell agree; and with Rule 209 the new state of an axis cell then
does not depend on them. By induction the x-axis inside the light cone is all ON at even stages
and all OFF at odd ones, so a(n) = 2^(n+1) - 1 for even n and a(n) = 0 for odd n.
The shape of the generating-function argument follows the merged proof of A277936.
-/

namespace A279872Proof

open OMA.S_oeis_a279872 PowerSeries

/-- `true` at even stages. -/
def par (t : ℕ) : Bool := decide (t % 2 = 0)

lemma par_succ (t : ℕ) : par (t + 1) = !par t := by
  unfold par
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have : (t + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (t + 1) % 2 = 0 := by omega
    simp [h, this]

lemma state_succ (t : ℕ) (x y : ℤ) :
    state (t + 1) (x, y) = rule (state t (x, y))
      ((state t (x + 1, y)).toNat + (state t (x - 1, y)).toNat +
        (state t (x, y + 1)).toNat + (state t (x, y - 1)).toNat) := by
  show rule (state t (x, y)) ((nbrs (x, y)).countP (fun q => state t q)) = _
  congr 1
  simp only [nbrs, List.countP_cons, List.countP_nil]
  cases state t (x + 1, y) <;> cases state t (x - 1, y) <;> cases state t (x, y + 1) <;>
    cases state t (x, y - 1) <;> rfl

/-- `(x, y)` lies outside the light cone of the origin at stage `t`: `t < |x| + |y|`. -/
def far (t : ℕ) (x y : ℤ) : Prop :=
  (t : ℤ) < x + y ∨ (t : ℤ) < x - y ∨ (t : ℤ) < -x + y ∨ (t : ℤ) < -x - y

lemma light_cone (t : ℕ) : ∀ x y, far t x y → state t (x, y) = !par t := by
  induction t with
  | zero =>
    intro x y h
    show decide ((x, y) = ((0 : ℤ), (0 : ℤ))) = !par 0
    have : ¬ (x = 0 ∧ y = 0) := by unfold far at h; push_cast at h; omega
    simp only [Prod.mk.injEq, par]
    simpa using this
  | succ t ih =>
    intro x y h
    unfold far at h
    push_cast at h
    rw [state_succ, ih x y (by unfold far; omega), ih (x + 1) y (by unfold far; omega),
      ih (x - 1) y (by unfold far; omega), ih x (y + 1) (by unfold far; omega),
      ih x (y - 1) (by unfold far; omega), par_succ]
    cases par t <;> rfl

lemma symm (t : ℕ) : ∀ x y, state t (x, -y) = state t (x, y) := by
  induction t with
  | zero =>
    intro x y
    show decide ((x, -y) = ((0 : ℤ), (0 : ℤ))) = decide ((x, y) = ((0 : ℤ), (0 : ℤ)))
    simp only [Prod.mk.injEq, neg_eq_zero]
  | succ t ih =>
    intro x y
    rw [state_succ, state_succ, ih x y, ih (x + 1) y, ih (x - 1) y,
      show -y + 1 = -(y - 1) by ring, show -y - 1 = -(y + 1) by ring, ih x (y - 1), ih x (y + 1)]
    congr 1
    omega

lemma axis (t : ℕ) : ∀ x, state t (x, 0) =
    if -(t : ℤ) ≤ x ∧ x ≤ t then par t else !par t := by
  induction t with
  | zero =>
    intro x
    show decide ((x, (0 : ℤ)) = ((0 : ℤ), (0 : ℤ))) = _
    by_cases hx : x = 0
    · subst hx; rfl
    · rw [if_neg (by push_cast; omega)]
      simp [hx, par]
  | succ t ih =>
    intro x
    have hs : state t (x, -1) = state t (x, 1) := symm t x 1
    rw [state_succ]
    simp only [zero_add, zero_sub]
    rw [hs, ih x, ih (x + 1), ih (x - 1), par_succ]
    push_cast
    by_cases hf : far t x 1
    · rw [light_cone t x 1 hf]
      unfold far at hf
      cases hp : par t <;> (unfold par at hp; simp at hp) <;> split_ifs <;> first | rfl | omega
    · unfold far at hf
      cases state t (x, 1) <;> cases hp : par t <;> (unfold par at hp; simp at hp) <;> split_ifs <;>
        first | rfl | omega

lemma state_axis_even (n k : ℕ) (hk : k < n + 1) (he : n % 2 = 0) :
    state n ((k : ℤ) - n, 0) = true := by
  rw [axis, if_pos (by omega)]
  unfold par
  simp [he]

lemma state_axis_odd (n k : ℕ) (hk : k < n + 1) (ho : n % 2 = 1) :
    state n ((k : ℤ) - n, 0) = false := by
  rw [axis, if_pos (by omega)]
  unfold par
  simp [ho]

lemma odd_value (n : ℕ) (ho : n % 2 = 1) : (a n : ℚ) = 0 := by
  unfold a
  rw [Finset.sum_eq_zero (fun k hk => by rw [state_axis_odd n k (Finset.mem_range.mp hk) ho]; rfl)]
  simp

lemma even_value (n : ℕ) (he : n % 2 = 0) : (a n : ℚ) * 1 = 2 ^ (n + 1) - 1 := by
  unfold a
  rw [Finset.sum_congr rfl (fun k hk => by rw [state_axis_even n k (Finset.mem_range.mp hk) he])]
  simp only [if_true, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
  have hr : (∑ k ∈ Finset.range (n + 1), (2 : ℚ) ^ (n - k)) =
      ∑ k ∈ Finset.range (n + 1), (2 : ℚ) ^ k := by
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun k => (2 : ℚ) ^ k) (n + 1)
  rw [hr]
  have hs := geom_sum_mul (2 : ℚ) (n + 1)
  norm_num at hs
  rw [mul_one]
  exact hs

lemma recurrence_rat (n : ℕ) (hn : 3 < n) :
    (a n : ℚ) = 5 * a (n - 2) - 4 * a (n - 4) := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have h0 := even_value n he
    have h2 := even_value (n - 2) (by omega)
    have h4 := even_value (n - 4) (by omega)
    rw [show n + 1 = (n - 4 + 1) + 4 by omega] at h0
    rw [show n - 2 + 1 = (n - 4 + 1) + 2 by omega] at h2
    rw [pow_add] at h0 h2
    linarith
  · rw [odd_value n ho, odd_value (n - 2) (by omega), odd_value (n - 4) (by omega)]
    norm_num

lemma generating_function :
    A = (2 * X ^ 2 + 1) * (4 * X ^ 4 - 5 * X ^ 2 + 1)⁻¹ := by
  let D : ℚ⟦X⟧ := 4 * X ^ 4 - 5 * X ^ 2 + 1
  let N : ℚ⟦X⟧ := 2 * X ^ 2 + 1
  change A = N * D⁻¹
  suffices h : A * D = N by
    rw [← h, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp [D]), mul_one]
  have hC (k : ℕ) : C (k : ℚ) = (k : ℚ⟦X⟧) := map_natCast C k
  have h₁₀ : C (2 : ℚ) = (2 : ℚ⟦X⟧) := hC 2
  have h₁₀₀ : C (4 : ℚ) = (4 : ℚ⟦X⟧) := hC 4
  have h₁₀₁ : C (5 : ℚ) = (5 : ℚ⟦X⟧) := hC 5
  have hleft : A * D = A - C 5 * (X ^ 2 * A) + C 4 * (X ^ 4 * A) := by
    rw [h₁₀₀, h₁₀₁]
    dsimp [D]
    ring
  have hright : N = 1 + C 2 * X ^ 2 := by
    rw [h₁₀]
    dsimp [N]
    ring
  rw [hleft, hright]
  ext n
  by_cases hn : 3 < n
  · have h₂ : 2 ≤ n := by omega
    have h₄ : 4 ≤ n := by omega
    have hn₀ : n ≠ 0 := by omega
    have hn₂ : n ≠ 2 := by omega
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', if_pos h₂, if_pos h₄,
      coeff_one, coeff_X_pow, if_neg hn₀, if_neg hn₂, mul_zero, add_zero, A, coeff_mk]
    linarith [recurrence_rat n hn]
  · have a₀ : a 0 = 1 := by
      have h := even_value 0 (by decide)
      norm_num at h
      exact_mod_cast h
    have a₁ : a 1 = 0 := by exact_mod_cast odd_value 1 (by decide)
    have a₂ : a 2 = 7 := by
      have h := even_value 2 (by decide)
      norm_num at h
      exact_mod_cast (by linarith : (a 2 : ℚ) = 7)
    have a₃ : a 3 = 0 := by exact_mod_cast odd_value 3 (by decide)
    interval_cases n <;> simp [coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_one, A,
      a₀, a₁, a₂, a₃] <;> norm_num

end A279872Proof

open OMA.S_oeis_a279872 A279872Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a279872.main := by
  refine ⟨?_, generating_function⟩
  intro n hn
  exact_mod_cast recurrence_rat n hn
