import OMAStatements.S_oeis_a326326

-- Problem oeis-a326326: the coefficient of x^k in the sum of the rising factorials x(x+1)...(x+j-1) for
-- j = 0..n equals the sum of the unsigned Stirling numbers of the first kind c(i, k) for i = 0..n.
-- Upstream: statements/oeis-a326326.lean (declaration OMA.S_oeis_a326326.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Key lemma: the coefficient of x^k in the rising factorial of length j is the Stirling number c(j, k).
-- Induction on j: multiplying by (x + j) sends the coefficient list to
--   [x^(k+1)] = (previous [x^k]) + j * (previous [x^(k+1)]),
-- which is exactly the recurrence c(j+1, k+1) = j * c(j, k+1) + c(j, k); the constant terms match too.
-- The statement then follows coefficient by coefficient.

open Polynomial

private lemma stirlingFirst_zero_right_mul_a326326 (j : ℕ) : Nat.stirlingFirst j 0 * j = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    have h : Nat.stirlingFirst (j + 1) 0 = 0 := rfl
    rw [h, zero_mul]

private lemma coeff_ascPochhammer_a326326 :
    ∀ j k : ℕ, (ascPochhammer ℕ j).coeff k = Nat.stirlingFirst j k := by
  intro j
  induction j with
  | zero =>
    intro k
    rw [ascPochhammer_zero, coeff_one]
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ j ih =>
    intro k
    rw [ascPochhammer_succ_right, mul_add, coeff_add, coeff_mul_natCast]
    cases k with
    | zero =>
      rw [coeff_mul_X_zero, ih 0, Nat.cast_id, stirlingFirst_zero_right_mul_a326326]
      rfl
    | succ k =>
      rw [coeff_mul_X, ih k, ih (k + 1), Nat.stirlingFirst_succ_succ, Nat.cast_id]
      ring

theorem OMA.solution : type_of% @OMA.S_oeis_a326326.main := by
  intro n k _
  unfold OMA.S_oeis_a326326.T OMA.S_oeis_a326326.A132393
  rw [finset_sum_coeff]
  exact Finset.sum_congr rfl (fun j _ => coeff_ascPochhammer_a326326 j k)
