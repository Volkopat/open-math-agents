import OMAStatements.S_oeis_a382407

-- Problem: A382407: a(n) is the number of partitions n = x + y + z of positive integers such that x*y + y*z + x*z is a perfect square.
-- Upstream: formal-conjectures statements/oeis-a382407.lean:0 (declaration OMA.S_oeis_a382407.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: k = 10 is a counterexample. The partitions 10 = x + y + z with x <= y <= z give
-- x*y + y*z + x*z = 17, 23, 27, 29, 28, 31, 32, 33, none a square, so a(10) = 0; but 10 is
-- not 2, 4, 8 or 13, not a power of 3 and not 5 times a power of 3 (3 does not divide 10).

open OMA.S_oeis_a382407 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a382407.main) := by
  intro H
  have ha : a 10 = 0 := by
    unfold a
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨x, y, z⟩ hmem ⟨hxy, hyz, hs, r, hr⟩
    have hx1 : 1 ≤ x := (Finset.mem_Icc.mp (Finset.mem_product.mp hmem).1).1
    have hxy' : x ≤ y := hxy
    have hyz' : y ≤ z := hyz
    have hs' : x + y + z = 10 := hs
    have hr' : x * y + y * z + x * z = r * r := hr
    clear hxy hyz hs hr hmem
    have hx : x ≤ 3 := by omega
    have hy : y ≤ 4 := by omega
    have hr8 : r < 8 := by
      by_contra hge
      have h64 : 8 * 8 ≤ r * r := Nat.mul_le_mul (by omega) (by omega)
      interval_cases x <;> interval_cases y <;> omega
    interval_cases x <;> interval_cases y <;> interval_cases r <;> omega
  have h10 := (H 10 (by norm_num)).mp ha
  rcases h10 with h1 | ⟨j, hj⟩ | ⟨j, hj⟩
  · simp at h1
  · cases j with
    | zero => simp at hj
    | succ i =>
      rw [pow_succ] at hj
      omega
  · cases j with
    | zero => simp at hj
    | succ i =>
      rw [pow_succ] at hj
      omega
