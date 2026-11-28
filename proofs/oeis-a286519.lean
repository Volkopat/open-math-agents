import OMAStatements.S_oeis_a286519

/-!
# OEIS A286519: The decimal reading of the diagonal of Rule 659

Credit: @grp06.
Source: https://oeis.org/A286519 (OEIS Foundation, CC BY-SA 4.0).
Robert Price contributed the entry. Colin Barker proposed the three formulas.
The upstream formalization was submitted by @jleguina.

This proof adapts the Rule 659 diagonal proof for A286521 by @grp06
(https://oeis.org/A286521, OEIS Foundation, CC BY-SA 4.0).
The transition lemmas through `state_full` are adapted from the private Rule 659
proof for A273386 (https://oeis.org/A273386, OEIS Foundation, CC BY-SA 4.0).
-/

namespace OMA.Rule659DecimalDiagonal

open OMA.S_oeis_a286519 PowerSeries
private def once (p : ℤ × ℤ) : Bool :=
  !decide ((p.1 = 0 ∧ (p.2 = 1 ∨ p.2 = -1)) ∨
    (p.2 = 0 ∧ (p.1 = 1 ∨ p.1 = -1)))

private def twice (p : ℤ × ℤ) : Bool :=
  !decide (|p.1| ≤ 1 ∧ |p.2| ≤ 1 ∧ p ≠ (0,0))

private def advance (f : ℤ × ℤ → Bool) (p : ℤ × ℤ) : Bool :=
  rule (f p) ((nbrs p).countP f)

private theorem far_coordinate {x : ℤ} (h : ¬ (-2 ≤ x ∧ x ≤ 2)) :
    ∀ z ∈ ({x-1,x,x+1} : Set ℤ), z ≠ 0 ∧ z ≠ 1 ∧ z ≠ -1 ∧ ¬ |z| ≤ 1 := by
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  simp only [abs_le]
  omega

private theorem transition (x y : ℤ) :
    advance (state 0) (x,y) = once (x,y) ∧
    advance once (x,y) = twice (x,y) ∧
    advance twice (x,y) = true := by
  by_cases hx : -2 ≤ x ∧ x ≤ 2
  · by_cases hy : -2 ≤ y ∧ y ≤ 2
    · obtain ⟨hx₁, hx₂⟩ := hx
      obtain ⟨hy₁, hy₂⟩ := hy
      interval_cases x <;> interval_cases y <;> decide
    · obtain ⟨h0,hp,hm,h1⟩ := far_coordinate hy y (by simp)
      obtain ⟨h0p,hpp,hmp,h1p⟩ := far_coordinate hy (y+1) (by simp)
      obtain ⟨h0m,hpm,hmm,h1m⟩ := far_coordinate hy (y-1) (by simp)
      simp [advance, nbrs, state, once, twice, Prod.ext_iff,
        h0,hp,hm,h1,h0p,hpp,hmp,h1p,h0m,hpm,hmm,h1m,rule]
      decide
  · obtain ⟨h0,hp,hm,h1⟩ := far_coordinate hx x (by simp)
    obtain ⟨h0p,hpp,hmp,h1p⟩ := far_coordinate hx (x+1) (by simp)
    obtain ⟨h0m,hpm,hmm,h1m⟩ := far_coordinate hx (x-1) (by simp)
    simp [advance, nbrs, state, once, twice, Prod.ext_iff,
      h0,hp,hm,h1,h0p,hpp,hmp,h1p,h0m,hpm,hmm,h1m,rule]
    decide

private theorem state_one : state 1 = once := by
  funext p
  obtain ⟨x,y⟩ := p
  exact (transition x y).1

private theorem state_two : state 2 = twice := by
  funext p
  obtain ⟨x,y⟩ := p
  change advance (state 1) (x,y) = twice (x,y)
  rw [state_one]
  exact (transition x y).2.1

private theorem state_three : state 3 = fun _ => true := by
  funext p
  obtain ⟨x,y⟩ := p
  change advance (state 2) (x,y) = true
  rw [state_two]
  exact (transition x y).2.2

private theorem state_full (n : ℕ) (hn : 3 ≤ n) : state n = fun _ => true := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 2
    · subst n
      exact state_three
    · have hi := ih (by omega)
      funext p
      change advance (state n) p = true
      rw [hi]
      rcases p with ⟨x,y⟩
      simp [advance,nbrs,rule]
      decide

private theorem a_zero : a 0 = 1 := by decide
private theorem a_one : a 1 = 11 := by decide
private theorem a_two : a 2 = 101 := by decide +kernel

private theorem a_closed (n : ℕ) (hn : 2 < n) :
    (a n : ℚ) = (10 ^ (1 + n) - 1) / 9 := by
  have hsum : a n = ∑ k ∈ Finset.range (n + 1), (10 : ℕ) ^ k := by
    calc
      a n = ∑ k ∈ Finset.range (n + 1), (10 : ℕ) ^ (n - k) := by
        simp [a, state_full n (by omega)]
      _ = ∑ k ∈ Finset.range (n + 1), (10 : ℕ) ^ k :=
        Finset.sum_range_reflect (fun k => (10 : ℕ) ^ k) (n + 1)
  rw [hsum]
  push_cast
  apply (eq_div_iff (show (9 : ℚ) ≠ 0 by norm_num)).2
  simpa only [show (10 : ℚ) - 1 = 9 by norm_num, Nat.add_comm n 1] using
    (geom_sum_mul (10 : ℚ) (n + 1))

private theorem recurrence_rat (n : ℕ) (hn : 4 < n) :
    (a n : ℚ) = 11 * (a (n - 1) : ℚ) - 10 * (a (n - 2) : ℚ) := by
  rw [a_closed n (by omega), a_closed (n - 1) (by omega), a_closed (n - 2) (by omega)]
  have h0 : 1 + n = (1 + (n - 2)) + 2 := by omega
  have h1 : 1 + (n - 1) = (1 + (n - 2)) + 1 := by omega
  rw [h0, h1, pow_add (10 : ℚ) (1 + (n - 2)) 2, pow_add (10 : ℚ) (1 + (n - 2)) 1]
  ring

private theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2) := by
  exact_mod_cast recurrence_rat n hn

private theorem generating_function :
    A = (1 - 10 * X ^ 2 + 110 * X ^ 3 - 100 * X ^ 4) * ((1 - X) * (1 - 10 * X))⁻¹ := by
  have hd : constantCoeff ((1 - X) * (1 - 10 * X) : ℚ⟦X⟧) ≠ 0 := by simp
  apply (PowerSeries.eq_mul_inv_iff_mul_eq hd).2
  have hleft : A * ((1 - X) * (1 - 10 * X)) =
      A - (C 11 * A) * X ^ 1 + (C 10 * A) * X ^ 2 := by
    simp only [map_ofNat, pow_one]
    ring
  have hright : (1 - 10 * X ^ 2 + 110 * X ^ 3 - 100 * X ^ 4 : ℚ⟦X⟧) =
      1 - C 10 * X ^ 2 + C 110 * X ^ 3 - C 100 * X ^ 4 := by
    simp only [map_ofNat]
  have hcoeff (n : ℕ) :
      coeff n (1 - C 10 * X ^ 2 + C 110 * X ^ 3 - C 100 * X ^ 4 : ℚ⟦X⟧) =
        (if n = 0 then 1 else 0) - 10 * (if n = 2 then 1 else 0) +
          110 * (if n = 3 then 1 else 0) - 100 * (if n = 4 then 1 else 0) := by
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_one]
  rw [hleft, hright]
  ext n
  rw [hcoeff]
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, A, coeff_mk]
  by_cases hn : 4 < n
  · have h0 : n ≠ 0 := by omega
    have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by omega
    have h4 : n ≠ 4 := by omega
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, h0, h2, h3, h4, if_true,
      if_false, mul_zero, sub_zero, add_zero]
    linarith [recurrence_rat n hn]
  · have hn' : n ≤ 4 := by omega
    have a_three : (a 3 : ℚ) = 1111 := (a_closed 3 (by decide)).trans (by norm_num)
    have a_four : (a 4 : ℚ) = 11111 := (a_closed 4 (by decide)).trans (by norm_num)
    interval_cases n <;> norm_num [a_zero, a_one, a_two, a_three, a_four]

theorem solution : type_of% @OMA.S_oeis_a286519.main :=
  ⟨generating_function, a_closed, recurrence⟩

end OMA.Rule659DecimalDiagonal

theorem OMA.solution : type_of% @OMA.S_oeis_a286519.main :=
  OMA.Rule659DecimalDiagonal.solution
