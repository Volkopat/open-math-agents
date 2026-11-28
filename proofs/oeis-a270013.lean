import OMAStatements.S_oeis_a270013

/-!
# OEIS A270013

Source: https://oeis.org/A270013 (OEIS Foundation, CC BY-SA 4.0).
Robert Price submitted the sequence and Colin Barker conjectured the formulas.
The comparison sequence is https://oeis.org/A270009, also submitted by Robert Price.
The upstream Lean statement was submitted by @jleguina.
The generating function argument adapts the coefficient proof for
https://oeis.org/A273767 by @grp06.
Proof: @grp06.
-/

namespace OMA.S_oeis_a270013

open PowerSeries

private theorem state_specializes (t : ℕ) (p : ℤ × ℤ) : state t p = stateOf 7 t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih => simp only [state, stateOf, rule, ruleOf, ih]

-- For the first two steps it suffices to check which cells in the stencil
-- coincide with the origin. The coordinate splits work on the entire plane.
set_option maxHeartbeats 1000000 in
private theorem stage_one (p : ℤ × ℤ) :
    stateOf 7 1 p = true ∧ stateOf 5 1 p = !(decide (p = (0, 0))) := by
  obtain ⟨x, y⟩ := p
  by_cases hx : x = 0 <;> by_cases hxPlus : x + 1 = 0 <;> by_cases hxMinus : x - 1 = 0 <;>
    by_cases hy : y = 0 <;> by_cases hyPlus : y + 1 = 0 <;> by_cases hyMinus : y - 1 = 0
  all_goals
    first
    | omega
    | simp only [stateOf, nbrs, List.countP_cons, List.countP_nil, Prod.mk.injEq,
        hx, hxPlus, hxMinus, hy, hyPlus, hyMinus, true_and, and_true, false_and, and_false,
        decide_true, decide_false] <;> decide +kernel

set_option maxHeartbeats 1000000 in
private theorem stage_two_five (p : ℤ × ℤ) : stateOf 5 2 p = false := by
  change ruleOf 5 (stateOf 5 1 p) ((nbrs p).countP (stateOf 5 1)) = false
  rw [show stateOf 5 1 = (fun q => !(decide (q = (0, 0)))) from
    funext (fun q => (stage_one q).2)]
  obtain ⟨x, y⟩ := p
  by_cases hx : x = 0 <;> by_cases hxPlus : x + 1 = 0 <;> by_cases hxMinus : x - 1 = 0 <;>
    by_cases hy : y = 0 <;> by_cases hyPlus : y + 1 = 0 <;> by_cases hyMinus : y - 1 = 0
  all_goals
    first
    | omega
    | simp only [nbrs, List.countP_cons, List.countP_nil, Prod.mk.injEq,
        hx, hxPlus, hxMinus, hy, hyPlus, hyMinus, true_and, and_true, false_and, and_false,
        decide_true, decide_false] <;> decide +kernel

private def profile (t : ℕ) (_ : ℤ × ℤ) : Bool := decide (t % 2 = 1)

private theorem step_profile {r : ℕ} (hr : r = 5 ∨ r = 7) {t : ℕ}
    (ht : stateOf r t = profile t) : stateOf r (t + 1) = profile (t + 1) := by
  funext p
  change ruleOf r (stateOf r t p) ((nbrs p).countP (stateOf r t)) = profile (t + 1) p
  rw [ht]
  by_cases h : t % 2 = 1
  · have h' : ¬ ((t + 1) % 2 = 1) := by omega
    rcases hr with rfl | rfl <;>
      simp only [profile, h, h', decide_true, decide_false, nbrs,
        List.countP_cons, List.countP_nil] <;> decide +kernel
  · have h' : (t + 1) % 2 = 1 := by omega
    rcases hr with rfl | rfl <;>
      simp only [profile, h, h', decide_true, decide_false, nbrs,
        List.countP_cons, List.countP_nil] <;> decide +kernel

private theorem seven_profile (t : ℕ) (ht : 0 < t) : stateOf 7 t = profile t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases h : t = 0
    · subst t
      exact funext (fun p => (stage_one p).1)
    · exact step_profile (Or.inr rfl) (ih (by omega))

private theorem five_profile (t : ℕ) (ht : 1 < t) : stateOf 5 t = profile t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases h : t = 1
    · subst t
      exact funext stage_two_five
    · exact step_profile (Or.inl rfl) (ih (by omega))

private theorem same_differences (n : ℕ) (hn : 1 < n) : a n = aOf 5 n := by
  have hs : ∀ t : ℕ, 1 < t → ∀ p, state t p = stateOf 5 t p := by
    intro t ht p
    rw [state_specializes, seven_profile t (by omega), five_profile t ht]
  simp only [a, aOf, hs n hn, hs (n + 1) (by omega)]

private def window (t : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * t + 1), ∑ y ∈ Finset.range (2 * t + 1),
    if state t ((x : ℤ) - t, (y : ℤ) - t) then 1 else 0

private theorem window_positive (t : ℕ) (ht : 0 < t) :
    window t = if t % 2 = 1 then (2 * t + 1) ^ 2 else 0 := by
  have hs := seven_profile t ht
  by_cases h : t % 2 = 1 <;>
    simp [window, state_specializes, hs, profile, h, Finset.sum_const, pow_two]

private theorem small_zero : a 0 = 8 := by
  change (window 1 : ℤ) - (window 0 : ℤ) = 8
  have h0 : window 0 = 1 := by decide +kernel
  rw [window_positive 1 (by decide), h0] <;> decide +kernel

private theorem form (R : Type*) [CommRing R] (n : ℕ) (hn : 0 < n) :
    (a n : R) = if n % 2 = 1 then -(2 * (n : R) + 1) ^ 2 else (2 * (n : R) + 3) ^ 2 := by
  have ha : a n = (window (n + 1) : ℤ) - (window n : ℤ) := rfl
  rw [ha, window_positive (n + 1) (by omega), window_positive n hn]
  by_cases h : n % 2 = 1
  · have h' : ¬ ((n + 1) % 2 = 1) := by omega
    simp only [if_pos h, if_neg h']
    push_cast <;> ring
  · have h' : (n + 1) % 2 = 1 := by omega
    simp only [if_neg h, if_pos h']
    push_cast <;> ring

private theorem even_form (n : ℕ) (hn : 0 < n) (he : Even n) :
    (a n : ℚ) = 4 * n ^ 2 + 12 * n + 9 := by
  have h : ¬ (n % 2 = 1) := by obtain ⟨k, hk⟩ := he; omega
  rw [form ℚ n hn, if_neg h]
  ring

private theorem odd_form (n : ℕ) (hn : 0 < n) (ho : Odd n) :
    (a n : ℚ) = -4 * n ^ 2 - 4 * n - 1 := by
  have h : n % 2 = 1 := by obtain ⟨k, hk⟩ := ho; omega
  rw [form ℚ n hn, if_pos h]
  ring

private theorem barker_form (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = 4 + 5 * (-1) ^ n + (4 + 8 * (-1) ^ n) * n + 4 * (-1) ^ n * n ^ 2 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [even_form n hn he, he.neg_one_pow]
    ring
  · rw [odd_form n hn ho, ho.neg_one_pow]
    ring

private theorem recurrence_from (R : Type*) [CommRing R] (m : ℕ) (hm : 0 < m) :
    (a (m + 5) : R) = -(a (m + 4) : R) + 2 * a (m + 3) + 2 * a (m + 2) -
      a (m + 1) - a m := by
  rw [form R (m + 5) (by omega), form R (m + 4) (by omega), form R (m + 3) (by omega),
    form R (m + 2) (by omega), form R (m + 1) (by omega), form R m hm]
  by_cases h : m % 2 = 1
  · simp only [if_pos h, if_neg (show ¬ ((m + 1) % 2 = 1) by omega),
      if_pos (show (m + 2) % 2 = 1 by omega), if_neg (show ¬ ((m + 3) % 2 = 1) by omega),
      if_pos (show (m + 4) % 2 = 1 by omega), if_neg (show ¬ ((m + 5) % 2 = 1) by omega)]
    push_cast <;> ring
  · simp only [if_neg h, if_pos (show (m + 1) % 2 = 1 by omega),
      if_neg (show ¬ ((m + 2) % 2 = 1) by omega), if_pos (show (m + 3) % 2 = 1 by omega),
      if_neg (show ¬ ((m + 4) % 2 = 1) by omega), if_pos (show (m + 5) % 2 = 1 by omega)]
    push_cast <;> ring

private theorem recurrence (R : Type*) [CommRing R] (n : ℕ) (hn : 5 < n) :
    (a n : R) = -(a (n - 1) : R) + 2 * a (n - 2) + 2 * a (n - 3) -
      a (n - 4) - a (n - 5) := by
  have h := recurrence_from R (n - 5) (by omega)
  rwa [show n - 5 + 5 = n by omega, show n - 5 + 4 = n - 1 by omega,
    show n - 5 + 3 = n - 2 by omega, show n - 5 + 2 = n - 3 by omega,
    show n - 5 + 1 = n - 4 by omega] at h

set_option maxHeartbeats 1000000 in
private theorem generating :
    A = (8 - X + 24 * X ^ 2 + 2 * X ^ 3 - X ^ 5) * ((1 - X) ^ 2 * (1 + X) ^ 3)⁻¹ := by
  let D : ℚ⟦X⟧ := (1 - X) ^ 2 * (1 + X) ^ 3
  let N : ℚ⟦X⟧ := 8 - X + 24 * X ^ 2 + 2 * X ^ 3 - X ^ 5
  change A = N * D⁻¹
  have hD : A * D = A + A * X ^ 1 - C 2 * (A * X ^ 2) - C 2 * (A * X ^ 3) +
      A * X ^ 4 + A * X ^ 5 := by
    simp only [D, map_ofNat, pow_one]
    ring
  have hN : N = C 8 - C 1 * X ^ 1 + C 24 * X ^ 2 + C 2 * X ^ 3 - C 1 * X ^ 5 := by
    simp only [N, map_ofNat, map_one, one_mul, pow_one]
  have hprod : A * D = N := by
    apply PowerSeries.ext
    intro n
    rw [hD, hN]
    simp only [map_sub, map_add, coeff_C_mul_X_pow]
    simp only [coeff_C_mul, coeff_mul_X_pow', coeff_C, A, coeff_mk]
    by_cases hn : n < 6
    · have h1 : (a 1 : ℚ) = -9 := by norm_num [form ℚ 1 (by decide)]
      have h2 : (a 2 : ℚ) = 49 := by norm_num [form ℚ 2 (by decide)]
      have h3 : (a 3 : ℚ) = -49 := by norm_num [form ℚ 3 (by decide)]
      have h4 : (a 4 : ℚ) = 121 := by norm_num [form ℚ 4 (by decide)]
      have h5 : (a 5 : ℚ) = -121 := by norm_num [form ℚ 5 (by decide)]
      interval_cases n <;> norm_num [small_zero, h1, h2, h3, h4, h5]
    · have h := recurrence ℚ n (by omega)
      simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
        if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega),
        if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega),
        if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 5 by omega),
        mul_zero, add_zero, sub_zero]
      linarith only [h]
  have hD0 : constantCoeff D ≠ 0 := by simp [D]
  calc
    A = (A * D) * D⁻¹ := by rw [mul_assoc, PowerSeries.mul_inv_cancel D hD0, mul_one]
    _ = N * D⁻¹ := by rw [hprod]

end OMA.S_oeis_a270013

open OMA.S_oeis_a270013 in
theorem OMA.solution : type_of% @OMA.S_oeis_a270013.main := by
  exact ⟨barker_form, same_differences, even_form, odd_form, recurrence ℤ, generating⟩
