import OMAStatements.S_oeis_a380191

-- Problem: A380191: Triangle read by rows: Riordan array (2 - D(x), x * D(x)) where D(x) is g.f. of A001764.
-- Upstream: formal-conjectures statements/oeis-a380191.lean:0 (declaration OMA.S_oeis_a380191.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: Show D = 1 + X * D^3 by comparing coefficients via the 2nd-order linear ODE
-- X*(4 - 27*X)*Y'' + (6 - 54*X)*Y' - 6*Y = 0, and show (1 - 4*X)*B^2 = 1 for B(X) = sum C(2i,i) X^i
-- via its 1st-order ODE (1 - 4*X)*B' = 2*B. Form BD = B(X*D) directly by coefficients and deduce
-- (1 - 4*X*D)*BD^2 = 1, hence ((2 - D)*BD)^2 = D^2 and (2 - D)*BD = D. Extracting [X^n] of
-- (2 - D)*(X*D)^k * BD = D*(X*D)^k yields the identity.

set_option maxHeartbeats 800000 in
open OMA.S_oeis_a380191 in
theorem OMA.solution : type_of% @OMA.S_oeis_a380191.main := by
  have hcoeff_mul : ∀ (f g : PowerSeries ℚ) (n : ℕ),
      PowerSeries.coeff n (f * g) =
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * PowerSeries.coeff (n - i) g := by
    intro f g n
    rw [PowerSeries.coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g) n
  let deriv : PowerSeries ℚ → PowerSeries ℚ :=
    fun f => PowerSeries.mk (fun n => ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) f)
  have hderiv_coeff : ∀ (f : PowerSeries ℚ) (n : ℕ),
      PowerSeries.coeff n (deriv f) = ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) f := by
    intro f n
    exact PowerSeries.coeff_mk n _
  have hderiv_add : ∀ f g : PowerSeries ℚ, deriv (f + g) = deriv f + deriv g := by
    intro f g
    ext n
    rw [map_add, hderiv_coeff, hderiv_coeff, hderiv_coeff, map_add]
    ring
  have hderiv_sub : ∀ f g : PowerSeries ℚ, deriv (f - g) = deriv f - deriv g := by
    intro f g
    ext n
    rw [map_sub, hderiv_coeff, hderiv_coeff, hderiv_coeff, map_sub]
    ring
  have hderiv_C : ∀ c : ℚ, deriv (PowerSeries.C c) = 0 := by
    intro c
    ext n
    rw [hderiv_coeff, map_zero, PowerSeries.coeff_C, if_neg (by omega), mul_zero]
  have hderiv_X : deriv PowerSeries.X = 1 := by
    ext n
    rw [hderiv_coeff, PowerSeries.coeff_X, PowerSeries.coeff_one]
    cases n with
    | zero => simp
    | succ m =>
      rw [if_neg (by omega), if_neg (by omega), mul_zero]
  have hderiv_mul : ∀ f g : PowerSeries ℚ, deriv (f * g) = deriv f * g + f * deriv g := by
    intro f g
    ext n
    rw [hderiv_coeff, map_add, hcoeff_mul, hcoeff_mul, hcoeff_mul]
    rw [Finset.mul_sum]
    have hsplit : ∑ i ∈ Finset.range (n + 2),
        ((n + 1 : ℕ) : ℚ) * (PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g) =
        (∑ i ∈ Finset.range (n + 2),
          (i : ℚ) * PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g) +
        (∑ i ∈ Finset.range (n + 2),
          PowerSeries.coeff i f * (((n + 1 - i : ℕ) : ℚ) * PowerSeries.coeff (n + 1 - i) g)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hle : i ≤ n + 1 := by
        have := Finset.mem_range.mp hi
        omega
      have hcast : ((n + 1 : ℕ) : ℚ) = (i : ℚ) + ((n + 1 - i : ℕ) : ℚ) := by
        have : n + 1 = i + (n + 1 - i) := by omega
        exact_mod_cast this
      rw [hcast]
      ring
    rw [hsplit]
    have h1 : ∑ i ∈ Finset.range (n + 2),
        (i : ℚ) * PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g =
        ∑ i ∈ Finset.range (n + 1),
        PowerSeries.coeff i (deriv f) * PowerSeries.coeff (n - i) g := by
      rw [Finset.sum_range_succ'
        (fun i => (i : ℚ) * PowerSeries.coeff i f * PowerSeries.coeff (n + 1 - i) g) (n + 1)]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hderiv_coeff, show n + 1 - (i + 1) = n - i by omega]
    have h2 : ∑ i ∈ Finset.range (n + 2),
        PowerSeries.coeff i f * (((n + 1 - i : ℕ) : ℚ) * PowerSeries.coeff (n + 1 - i) g) =
        ∑ i ∈ Finset.range (n + 1),
        PowerSeries.coeff i f * PowerSeries.coeff (n - i) (deriv g) := by
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hle : i ≤ n := by
        have := Finset.mem_range.mp hi
        omega
      rw [hderiv_coeff, show n + 1 - i = n - i + 1 by omega]
    rw [h1, h2]
  have hderiv_smul : ∀ (c : ℚ) (f : PowerSeries ℚ),
      deriv (PowerSeries.C c * f) = PowerSeries.C c * deriv f := by
    intro c f
    rw [hderiv_mul, hderiv_C, zero_mul, zero_add]
  have hderiv_eq_zero : ∀ f : PowerSeries ℚ, deriv f = 0 →
      f = PowerSeries.C (PowerSeries.constantCoeff f) := by
    intro f hf
    ext n
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_C]
    | succ m =>
      rw [PowerSeries.coeff_C, if_neg (by omega)]
      have hm := congr_arg (PowerSeries.coeff m) hf
      rw [hderiv_coeff, map_zero] at hm
      have hne : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hm).resolve_left hne
  -- Step 1: Prove D = 1 + X * D^3 via recursive Y and 2nd-order ODE
  let recStep : (ℕ → ℚ) → ℕ → ℚ := fun f k =>
    match k with
    | 0 => 1
    | m + 1 => ∑ i ∈ Finset.range (m + 1),
        ∑ j ∈ Finset.range (m + 1 - i), f i * f j * f (m - i - j)
  let yIter : ℕ → ℕ → ℚ := fun N => Nat.rec (fun _ => 0) (fun _ prev => recStep prev) N
  have hyIter_stab : ∀ N k : ℕ, k < N → yIter (N + 1) k = yIter N k := by
    intro N
    induction N with
    | zero => intro k hk; omega
    | succ M ih =>
      intro k hk
      cases k with
      | zero => rfl
      | succ m =>
        change recStep (yIter (M + 1)) (m + 1) = recStep (yIter M) (m + 1)
        dsimp only [recStep]
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
        have hi' : i < M := by have := Finset.mem_range.mp hi; omega
        have hj' : j < M := by have := Finset.mem_range.mp hj; omega
        have hk' : m - i - j < M := by omega
        rw [ih i hi', ih j hj', ih (m - i - j) hk']
  have hyIter_ge : ∀ N₁ N₂ k : ℕ, k < N₁ → N₁ ≤ N₂ → yIter N₂ k = yIter N₁ k := by
    intro N₁ N₂ k hk hle
    induction N₂, hle using Nat.le_induction with
    | base => rfl
    | succ M hM ih =>
      rw [hyIter_stab M k (by omega), ih]
  let ySeq : ℕ → ℚ := fun n => yIter (n + 1) n
  have hy0 : ySeq 0 = 1 := rfl
  have hy_succ : ∀ m : ℕ, ySeq (m + 1) =
      ∑ i ∈ Finset.range (m + 1),
        ∑ j ∈ Finset.range (m + 1 - i), ySeq i * ySeq j * ySeq (m - i - j) := by
    intro m
    change recStep (yIter (m + 1)) (m + 1) = _
    dsimp only [recStep]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    have hi' : i < m + 1 := Finset.mem_range.mp hi
    have hj' : j < m + 1 - i := Finset.mem_range.mp hj
    rw [hyIter_ge (i + 1) (m + 1) i (by omega) (by omega),
      hyIter_ge (j + 1) (m + 1) j (by omega) (by omega),
      hyIter_ge (m - i - j + 1) (m + 1) (m - i - j) (by omega) (by omega)]
  let Y : PowerSeries ℚ := PowerSeries.mk ySeq
  have hY_eq : Y = 1 + PowerSeries.X * Y ^ 3 := by
    ext n
    rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one]
    cases n with
    | zero =>
      rw [if_pos rfl, PowerSeries.coeff_zero_X_mul, add_zero, hy0]
    | succ m =>
      rw [if_neg (by omega), zero_add, PowerSeries.coeff_succ_X_mul, pow_three,
        hcoeff_mul, hy_succ m]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hcoeff_mul, Finset.mul_sum]
      have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
      rw [show m + 1 - i = m - i + 1 by omega]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      ring
  have hE0 : PowerSeries.X * Y ^ 3 - Y + 1 = 0 := by
    linear_combination -hY_eq
  have hE1 : (1 - 3 * PowerSeries.X * Y ^ 2) * deriv Y - Y ^ 3 = 0 := by
    have h1 := congr_arg deriv hY_eq
    have h1c : deriv (1 : PowerSeries ℚ) = 0 := by
      have : (1 : PowerSeries ℚ) = PowerSeries.C 1 := by simp
      rw [this, hderiv_C]
    have hY3 : deriv (Y ^ 3) = 3 * Y ^ 2 * deriv Y := by
      rw [pow_three, hderiv_mul, hderiv_mul]
      ring
    rw [hderiv_add, h1c, zero_add, hderiv_mul, hderiv_X, one_mul, hY3] at h1
    linear_combination h1
  have hE2 : (1 - 3 * PowerSeries.X * Y ^ 2) * deriv (deriv Y) -
      6 * Y ^ 2 * deriv Y - 6 * PowerSeries.X * Y * (deriv Y) ^ 2 = 0 := by
    have h2 := congr_arg deriv hE1
    have h0c : deriv (0 : PowerSeries ℚ) = 0 := by
      have h := hderiv_C 0
      rwa [map_zero] at h
    have h1c : deriv (1 : PowerSeries ℚ) = 0 := by
      have : (1 : PowerSeries ℚ) = PowerSeries.C 1 := by simp
      rw [this, hderiv_C]
    have h3c : (3 : PowerSeries ℚ) = PowerSeries.C 3 :=
      (map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm
    have hY2 : deriv (Y ^ 2) = 2 * Y * deriv Y := by
      rw [pow_two, hderiv_mul]
      ring
    have hY3 : deriv (Y ^ 3) = 3 * Y ^ 2 * deriv Y := by
      rw [pow_three, hderiv_mul, hderiv_mul]
      ring
    rw [hderiv_sub, hderiv_mul, hderiv_sub, h1c, zero_sub,
      show 3 * PowerSeries.X * Y ^ 2 = PowerSeries.C 3 * (PowerSeries.X * Y ^ 2) by
        rw [h3c]; ring,
      hderiv_smul, hderiv_mul, hderiv_X, one_mul, hY2, hY3, h0c] at h2
    rw [← h3c] at h2
    linear_combination h2
  have hY_ode : PowerSeries.X * (4 - 27 * PowerSeries.X) * deriv (deriv Y) +
      (6 - 54 * PowerSeries.X) * deriv Y - 6 * Y = 0 := by
    set u : PowerSeries ℚ := 1 - 3 * PowerSeries.X * Y ^ 2
    have hmul0 : u ^ 3 * (PowerSeries.X * (4 - 27 * PowerSeries.X) * deriv (deriv Y) +
        (6 - 54 * PowerSeries.X) * deriv Y - 6 * Y) = 0 := by
      linear_combination
        (PowerSeries.X * (4 - 27 * PowerSeries.X) * u ^ 2) * hE2 +
        (6 * PowerSeries.X * (4 - 27 * PowerSeries.X) * Y ^ 2 * u +
         6 * PowerSeries.X ^ 2 * (4 - 27 * PowerSeries.X) * Y * (u * deriv Y + Y ^ 3) +
         (6 - 54 * PowerSeries.X) * u ^ 2) * hE1 +
        (6 * Y * (PowerSeries.X * Y ^ 3 - Y - 1)) * hE0
    have hu_ne : u ≠ 0 := by
      intro hu0
      have hc := congr_arg PowerSeries.constantCoeff hu0
      simp only [u, map_sub, map_one, map_mul, PowerSeries.constantCoeff_X, mul_zero, zero_mul,
        sub_zero, map_zero] at hc
      norm_num at hc
    exact (mul_eq_zero.mp hmul0).resolve_left (pow_ne_zero 3 hu_ne)
  have hYc : ∀ k : ℕ, PowerSeries.coeff k Y = ySeq k := fun k => PowerSeries.coeff_mk k ySeq
  have hX0 : ∀ f : PowerSeries ℚ, PowerSeries.coeff 0 (PowerSeries.X * f) = 0 :=
    fun f => PowerSeries.coeff_zero_X_mul f
  have hy_rec : ∀ n : ℕ, ((4 * n ^ 2 + 10 * n + 6 : ℕ) : ℚ) * ySeq (n + 1) =
      ((27 * n ^ 2 + 27 * n + 6 : ℕ) : ℚ) * ySeq n := by
    have hrew : PowerSeries.X * (4 - 27 * PowerSeries.X) * deriv (deriv Y) +
        (6 - 54 * PowerSeries.X) * deriv Y - 6 * Y =
        PowerSeries.C 4 * (PowerSeries.X * deriv (deriv Y)) -
        PowerSeries.C 27 * (PowerSeries.X * (PowerSeries.X * deriv (deriv Y))) +
        PowerSeries.C 6 * deriv Y -
        PowerSeries.C 54 * (PowerSeries.X * deriv Y) -
        PowerSeries.C 6 * Y := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 27,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 54]
      ring
    intro n
    have hcn := congr_arg (PowerSeries.coeff n) hY_ode
    rw [hrew] at hcn
    simp only [map_sub, map_add, map_zero, PowerSeries.coeff_C_mul] at hcn
    rcases n with _ | _ | m
    · simp only [hX0, hderiv_coeff, hYc] at hcn ⊢
      push_cast at hcn ⊢
      linarith
    · simp only [PowerSeries.coeff_succ_X_mul, hX0, hderiv_coeff, hYc] at hcn ⊢
      push_cast at hcn ⊢
      linarith
    · simp only [PowerSeries.coeff_succ_X_mul, hderiv_coeff, hYc] at hcn ⊢
      push_cast at hcn ⊢
      linarith
  have hD_rec : ∀ n : ℕ, ((4 * n ^ 2 + 10 * n + 6 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) D =
      ((27 * n ^ 2 + 27 * n + 6 : ℕ) : ℚ) * PowerSeries.coeff n D := by
    intro n
    unfold D
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    have hbin : Nat.choose (3 * (n + 1)) (n + 1) * ((n + 1) * (2 * n + 2) * (2 * n + 1)) =
        Nat.choose (3 * n) n * ((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
      have h2 := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 3 * (n + 1) by omega)
      rw [show 3 * n - n = 2 * n by omega] at h1
      rw [show 3 * (n + 1) - (n + 1) = 2 * n + 2 by omega,
        show 3 * (n + 1) = 3 * n + 3 by omega] at h2
      have hf1 : (3 * n + 3).factorial = (3 * n + 3) * (3 * n + 2) * (3 * n + 1) * (3 * n).factorial := by
        rw [Nat.factorial_succ (3 * n + 2), Nat.factorial_succ (3 * n + 1),
          Nat.factorial_succ (3 * n)]
        ring
      have hf2 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
      have hf3 : (2 * n + 2).factorial = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
        rw [Nat.factorial_succ (2 * n + 1), Nat.factorial_succ (2 * n)]
        ring
      have hfac_pos : 0 < n.factorial * (2 * n).factorial :=
        Nat.mul_pos (Nat.factorial_pos n) (Nat.factorial_pos (2 * n))
      apply Nat.eq_of_mul_eq_mul_right hfac_pos
      calc Nat.choose (3 * (n + 1)) (n + 1) * ((n + 1) * (2 * n + 2) * (2 * n + 1)) *
            (n.factorial * (2 * n).factorial)
          = Nat.choose (3 * n + 3) (n + 1) * (n + 1).factorial * (2 * n + 2).factorial := by
            rw [show 3 * (n + 1) = 3 * n + 3 by omega, hf2, hf3]; ring
        _ = (3 * n + 3).factorial := h2
        _ = (3 * n + 3) * (3 * n + 2) * (3 * n + 1) * (3 * n).factorial := hf1
        _ = (3 * n + 3) * (3 * n + 2) * (3 * n + 1) *
            (Nat.choose (3 * n) n * n.factorial * (2 * n).factorial) := by rw [← h1]
        _ = Nat.choose (3 * n) n * ((3 * n + 3) * (3 * n + 2) * (3 * n + 1)) *
            (n.factorial * (2 * n).factorial) := by ring
    have hbinQ : (Nat.choose (3 * (n + 1)) (n + 1) : ℚ) *
        (((n + 1 : ℕ) : ℚ) * ((2 * n + 2 : ℕ) : ℚ) * ((2 * n + 1 : ℕ) : ℚ)) =
        (Nat.choose (3 * n) n : ℚ) *
        (((3 * n + 3 : ℕ) : ℚ) * ((3 * n + 2 : ℕ) : ℚ) * ((3 * n + 1 : ℕ) : ℚ)) := by
      exact_mod_cast hbin
    have hd1 : ((2 * (n + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hd2 : ((2 * n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast at hbinQ ⊢
    have hR : (Nat.choose (3 * (n + 1)) (n + 1) : ℚ) * (2 * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1)) -
        (Nat.choose (3 * n) n : ℚ) * (3 * (3 * (n : ℚ) + 1) * (3 * (n : ℚ) + 2)) = 0 := by
      have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
      have h' : ((n : ℚ) + 1) * ((Nat.choose (3 * (n + 1)) (n + 1) : ℚ) *
          (2 * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1)) -
          (Nat.choose (3 * n) n : ℚ) * (3 * (3 * (n : ℚ) + 1) * (3 * (n : ℚ) + 2))) = 0 := by
        linear_combination hbinQ
      exact (mul_eq_zero.mp h').resolve_left hn1
    linear_combination (2 * (n : ℚ) + 3) * hR
  have hD_eq_Y : D = Y := by
    ext n
    rw [PowerSeries.coeff_mk]
    induction n with
    | zero =>
      unfold D
      rw [PowerSeries.coeff_mk, hy0]
      norm_num
    | succ m ih =>
      have h1 := hD_rec m
      have h2 := hy_rec m
      rw [ih] at h1
      have hne : ((4 * m ^ 2 + 10 * m + 6 : ℕ) : ℚ) ≠ 0 := by positivity
      exact mul_left_cancel₀ hne (h1.trans h2.symm)
  have hD_cubic : D = 1 + PowerSeries.X * D ^ 3 := by
    rw [hD_eq_Y]
    exact hY_eq
  -- Step 2: Prove (1 - 4*X) * B^2 = 1 and sum_{i=0}^n C(2i,i)*C(2(n-i),n-i) = 4^n
  let B : PowerSeries ℚ := PowerSeries.mk (fun n => (Nat.choose (2 * n) n : ℚ))
  have hB_ode : (1 - 4 * PowerSeries.X) * deriv B = 2 * B := by
    ext n
    have hrew : (1 - 4 * PowerSeries.X) * deriv B =
        deriv B - PowerSeries.C 4 * (PowerSeries.X * deriv B) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
      ring
    have hrew2 : 2 * B = PowerSeries.C 2 * B := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    rw [hrew, hrew2, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    have hbin : Nat.choose (2 * (n + 1)) (n + 1) * (n + 1) =
        Nat.choose (2 * n) n * (4 * n + 2) := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
      have h2 := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 2 * (n + 1) by omega)
      rw [show 2 * n - n = n by omega] at h1
      rw [show 2 * (n + 1) - (n + 1) = n + 1 by omega,
        show 2 * (n + 1) = 2 * n + 2 by omega] at h2
      have hf1 : (2 * n + 2).factorial = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
        rw [Nat.factorial_succ (2 * n + 1), Nat.factorial_succ (2 * n)]
        ring
      have hf2 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
      have hfac_pos : 0 < (n + 1) * (n.factorial * n.factorial) :=
        Nat.mul_pos (by omega) (Nat.mul_pos (Nat.factorial_pos n) (Nat.factorial_pos n))
      apply Nat.eq_of_mul_eq_mul_right hfac_pos
      calc Nat.choose (2 * (n + 1)) (n + 1) * (n + 1) * ((n + 1) * (n.factorial * n.factorial))
          = Nat.choose (2 * n + 2) (n + 1) * (n + 1).factorial * (n + 1).factorial := by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega, hf2]; ring
        _ = (2 * n + 2).factorial := h2
        _ = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := hf1
        _ = (2 * n + 2) * (2 * n + 1) * (Nat.choose (2 * n) n * n.factorial * n.factorial) := by
            rw [← h1]
        _ = Nat.choose (2 * n) n * (4 * n + 2) * ((n + 1) * (n.factorial * n.factorial)) := by ring
    have hbinQ : (Nat.choose (2 * (n + 1)) (n + 1) : ℚ) * ((n + 1 : ℕ) : ℚ) =
        (Nat.choose (2 * n) n : ℚ) * ((4 * n + 2 : ℕ) : ℚ) := by exact_mod_cast hbin
    cases n with
    | zero =>
      rw [hX0, mul_zero, sub_zero, hderiv_coeff]
      simp only [B, PowerSeries.coeff_mk]
      norm_num
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, hderiv_coeff, hderiv_coeff]
      simp only [B, PowerSeries.coeff_mk]
      push_cast at hbinQ ⊢
      linarith
  have hB_sq : (1 - 4 * PowerSeries.X) * B ^ 2 = 1 := by
    have hd : deriv ((1 - 4 * PowerSeries.X) * B ^ 2) = 0 := by
      have h1c : deriv (1 : PowerSeries ℚ) = 0 := by
        have : (1 : PowerSeries ℚ) = PowerSeries.C 1 := by simp
        rw [this, hderiv_C]
      have h4c : (4 : PowerSeries ℚ) = PowerSeries.C 4 :=
        (map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm
      have hB2 : deriv (B ^ 2) = 2 * B * deriv B := by
        rw [pow_two, hderiv_mul]
        ring
      rw [hderiv_mul, hderiv_sub, h1c, zero_sub, h4c, hderiv_smul, hderiv_X, mul_one, ← h4c, hB2]
      linear_combination 2 * B * hB_ode
    have hconst := hderiv_eq_zero _ hd
    have hcc : PowerSeries.constantCoeff ((1 - 4 * PowerSeries.X) * B ^ 2) = 1 := by
      simp only [B, map_mul, map_sub, map_one, map_pow, PowerSeries.constantCoeff_X, mul_zero,
        sub_zero, PowerSeries.constantCoeff_mk]
      norm_num
    rw [hconst, hcc]
    simp
  have hconv4 : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1),
      (Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * (m - i)) (m - i) : ℚ) = (4 : ℚ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have hc := congr_arg (PowerSeries.coeff (k + 1)) hB_sq
      have hrew : (1 - 4 * PowerSeries.X) * B ^ 2 = B ^ 2 - PowerSeries.C 4 * (PowerSeries.X * B ^ 2) := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
        ring
      rw [hrew, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_one, if_neg (by omega)] at hc
      rw [pow_two, hcoeff_mul, hcoeff_mul] at hc
      simp only [B, PowerSeries.coeff_mk] at hc
      rw [ih] at hc
      rw [pow_succ']
      linarith
  -- Step 3: Form BD = B(X * D) and prove (1 - 4 * X * D) * BD^2 = 1
  have hXD_pow_zero : ∀ (i n : ℕ), n < i → PowerSeries.coeff n ((PowerSeries.X * D) ^ i) = 0 := by
    intro i n hni
    rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hXD_mul_zero : ∀ (f : PowerSeries ℚ) (i n : ℕ), n < i →
      PowerSeries.coeff n (f * (PowerSeries.X * D) ^ i) = 0 := by
    intro f i n hni
    rw [mul_pow, show f * (PowerSeries.X ^ i * D ^ i) = PowerSeries.X ^ i * (f * D ^ i) by ring,
      PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  let BD : PowerSeries ℚ := PowerSeries.mk (fun n =>
    ∑ i ∈ Finset.range (n + 1), (Nat.choose (2 * i) i : ℚ) *
      PowerSeries.coeff n ((PowerSeries.X * D) ^ i))
  let P : ℕ → PowerSeries ℚ := fun N =>
    ∑ i ∈ Finset.range (N + 1), PowerSeries.C (Nat.choose (2 * i) i : ℚ) * (PowerSeries.X * D) ^ i
  have hBD_eq_P : ∀ (N m : ℕ), m ≤ N → PowerSeries.coeff m BD = PowerSeries.coeff m (P N) := by
    intro N m hm
    dsimp only [BD, P]
    rw [PowerSeries.coeff_mk, map_sum]
    have hsub : Finset.range (m + 1) ⊆ Finset.range (N + 1) :=
      Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [PowerSeries.coeff_C_mul]
    · intro i _ hi
      have hgt : m < i := by
        have : ¬ i < m + 1 := fun h => hi (Finset.mem_range.mpr h)
        omega
      rw [PowerSeries.coeff_C_mul, hXD_pow_zero i m hgt, mul_zero]
  have hBD_sq : (1 - 4 * PowerSeries.X * D) * BD ^ 2 = 1 := by
    ext N
    have hmul_eq : ∀ f g : PowerSeries ℚ,
        (∀ m ≤ N, PowerSeries.coeff m f = PowerSeries.coeff m g) →
        ∀ h : PowerSeries ℚ, PowerSeries.coeff N (h * f) = PowerSeries.coeff N (h * g) := by
      intro f g hfg h
      rw [hcoeff_mul, hcoeff_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hfg (N - i) (by omega)]
    have hsq_eq : ∀ m ≤ N, PowerSeries.coeff m (BD ^ 2) = PowerSeries.coeff m ((P N) ^ 2) := by
      intro m hm
      rw [pow_two, pow_two, hcoeff_mul, hcoeff_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ N := by have := Finset.mem_range.mp hi; omega
      rw [hBD_eq_P N i hi', hBD_eq_P N (m - i) (by omega)]
    rw [hmul_eq (BD ^ 2) ((P N) ^ 2) hsq_eq (1 - 4 * PowerSeries.X * D)]
    -- Expand (1 - 4*X*D) * (P N)^2
    have hP2 : (P N) ^ 2 =
        (∑ m ∈ Finset.range (N + 1), (4 * PowerSeries.X * D) ^ m) +
        ∑ i ∈ Finset.range (N + 1), ∑ j ∈ (Finset.range (N + 1)).filter (fun j => N < i + j),
          PowerSeries.C ((Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * j) j : ℚ)) *
            (PowerSeries.X * D) ^ (i + j) := by
      rw [pow_two]
      dsimp only [P]
      rw [Finset.sum_mul]
      have hterm : ∀ i ∈ Finset.range (N + 1),
          PowerSeries.C (Nat.choose (2 * i) i : ℚ) * (PowerSeries.X * D) ^ i *
            (∑ j ∈ Finset.range (N + 1),
              PowerSeries.C (Nat.choose (2 * j) j : ℚ) * (PowerSeries.X * D) ^ j) =
          (∑ j ∈ (Finset.range (N + 1)).filter (fun j => i + j ≤ N),
            PowerSeries.C ((Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * j) j : ℚ)) *
              (PowerSeries.X * D) ^ (i + j)) +
          (∑ j ∈ (Finset.range (N + 1)).filter (fun j => N < i + j),
            PowerSeries.C ((Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * j) j : ℚ)) *
              (PowerSeries.X * D) ^ (i + j)) := by
        intro i _
        rw [Finset.mul_sum]
        have heq : ∀ j : ℕ,
            PowerSeries.C (Nat.choose (2 * i) i : ℚ) * (PowerSeries.X * D) ^ i *
              (PowerSeries.C (Nat.choose (2 * j) j : ℚ) * (PowerSeries.X * D) ^ j) =
            PowerSeries.C ((Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * j) j : ℚ)) *
              (PowerSeries.X * D) ^ (i + j) := by
          intro j
          rw [map_mul, pow_add]
          ring
        simp_rw [heq]
        have hpart := (Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1))
          (fun j => i + j ≤ N)
          (fun j => PowerSeries.C ((Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * j) j : ℚ)) *
            (PowerSeries.X * D) ^ (i + j))).symm
        rw [hpart]
        congr 1
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext j
        simp only [Finset.mem_filter]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      congr 1
      -- Reindex the low-degree double sum by m = i + j
      have hlow : ∑ i ∈ Finset.range (N + 1),
          ∑ j ∈ (Finset.range (N + 1)).filter (fun j => i + j ≤ N),
            PowerSeries.C ((Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * j) j : ℚ)) *
              (PowerSeries.X * D) ^ (i + j) =
          ∑ m ∈ Finset.range (N + 1),
            (∑ i ∈ Finset.range (m + 1),
              PowerSeries.C ((Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * (m - i)) (m - i) : ℚ))) *
              (PowerSeries.X * D) ^ m := by
        have hl : ∀ i ∈ Finset.range (N + 1),
            ∑ j ∈ (Finset.range (N + 1)).filter (fun j => i + j ≤ N),
              PowerSeries.C ((Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * j) j : ℚ)) *
                (PowerSeries.X * D) ^ (i + j) =
            ∑ m ∈ Finset.range (N + 1),
              if i ≤ m then
                PowerSeries.C ((Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * (m - i)) (m - i) : ℚ)) *
                  (PowerSeries.X * D) ^ m
              else 0 := by
          intro i hi
          rw [← Finset.sum_filter]
          refine Finset.sum_bij (fun j _ => i + j) ?_ ?_ ?_ ?_
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
            omega
          · intro j₁ _ j₂ _ h
            omega
          · intro m hm
            simp only [Finset.mem_filter, Finset.mem_range] at hm
            refine ⟨m - i, ?_, by omega⟩
            simp only [Finset.mem_filter, Finset.mem_range]
            omega
          · intro j _
            rw [show i + j - i = j by omega]
        rw [Finset.sum_congr rfl hl, Finset.sum_comm]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.sum_mul]
        rw [← Finset.sum_filter]
        have hfilt : (Finset.range (N + 1)).filter (fun i => i ≤ m) = Finset.range (m + 1) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_range]
          have := Finset.mem_range.mp hm
          omega
        rw [hfilt]
      rw [hlow]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_sum, hconv4 m]
      have h4m : PowerSeries.C ((4 : ℚ) ^ m) * (PowerSeries.X * D) ^ m =
          (4 * PowerSeries.X * D) ^ m := by
        have hc4 : PowerSeries.C (4 : ℚ) = 4 := map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
        rw [map_pow, hc4]
        ring
      exact h4m
    rw [hP2, mul_add, map_add]
    have hgeom : (1 - 4 * PowerSeries.X * D) *
        (∑ m ∈ Finset.range (N + 1), (4 * PowerSeries.X * D) ^ m) =
        1 - (4 * PowerSeries.X * D) ^ (N + 1) := by
      have hgs := geom_sum_mul_neg (4 * PowerSeries.X * D) (N + 1)
      rw [mul_comm]
      exact hgs
    have htail : PowerSeries.coeff N ((1 - 4 * PowerSeries.X * D) *
        ∑ i ∈ Finset.range (N + 1), ∑ j ∈ (Finset.range (N + 1)).filter (fun j => N < i + j),
          PowerSeries.C ((Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * j) j : ℚ)) *
            (PowerSeries.X * D) ^ (i + j)) = 0 := by
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_eq_zero
      intro j hj
      have hij : N < i + j := (Finset.mem_filter.mp hj).2
      rw [← mul_assoc]
      exact hXD_mul_zero _ (i + j) N hij
    rw [hgeom, htail, add_zero, map_sub]
    have hpow_hi : PowerSeries.coeff N ((4 * PowerSeries.X * D) ^ (N + 1)) = 0 := by
      have hrew : (4 * PowerSeries.X * D) ^ (N + 1) =
          (4 : PowerSeries ℚ) ^ (N + 1) * (PowerSeries.X * D) ^ (N + 1) := by ring
      rw [hrew]
      exact hXD_mul_zero _ (N + 1) N (by omega)
    rw [hpow_hi, sub_zero]
  -- Step 4: Deduce (2 - D) * BD = D
  have hmain_ps : (2 - D) * BD = D := by
    have hsq : ((2 - D) * BD) ^ 2 * (1 - 4 * PowerSeries.X * D) =
        D ^ 2 * (1 - 4 * PowerSeries.X * D) := by
      calc ((2 - D) * BD) ^ 2 * (1 - 4 * PowerSeries.X * D)
          = (2 - D) ^ 2 * ((1 - 4 * PowerSeries.X * D) * BD ^ 2) := by ring
        _ = (2 - D) ^ 2 * 1 := by rw [hBD_sq]
        _ = (2 - D) ^ 2 := mul_one _
        _ = D ^ 2 - 4 * (D - 1) := by ring
        _ = D ^ 2 - 4 * (PowerSeries.X * D ^ 3) := by
            have : D - 1 = PowerSeries.X * D ^ 3 := by linear_combination hD_cubic
            rw [this]
        _ = D ^ 2 * (1 - 4 * PowerSeries.X * D) := by ring
    have h14_ne : (1 - 4 * PowerSeries.X * D : PowerSeries ℚ) ≠ 0 := by
      intro h0
      have hc := congr_arg PowerSeries.constantCoeff h0
      simp only [map_sub, map_one, map_mul, PowerSeries.constantCoeff_X, mul_zero, zero_mul,
        sub_zero, map_zero] at hc
      norm_num at hc
    have hsq2 : ((2 - D) * BD - D) * ((2 - D) * BD + D) = 0 := by
      have hmul : (((2 - D) * BD - D) * ((2 - D) * BD + D)) * (1 - 4 * PowerSeries.X * D) = 0 := by
        linear_combination hsq
      exact (mul_eq_zero.mp hmul).resolve_right h14_ne
    have hsum_ne : (2 - D) * BD + D ≠ 0 := by
      intro h0
      have hc := congr_arg PowerSeries.constantCoeff h0
      have hD0 : PowerSeries.constantCoeff D = 1 := by
        unfold D
        rw [PowerSeries.constantCoeff_mk]
        norm_num
      have hBD0 : PowerSeries.constantCoeff BD = 1 := by
        dsimp only [BD]
        rw [PowerSeries.constantCoeff_mk]
        simp
      simp only [map_add, map_mul, map_sub, map_ofNat, hD0, hBD0, map_zero] at hc
      norm_num at hc
    have hdiff := (mul_eq_zero.mp hsq2).resolve_right hsum_ne
    linear_combination hdiff
  -- Step 5: Extract coefficient [X^n] of (2 - D) * (X * D)^k * BD = D * (X * D)^k
  intro n k hk
  unfold A110616 T
  have hR : PowerSeries.coeff n (D * (PowerSeries.X * D) ^ k) =
      PowerSeries.coeff n ((2 - D) * BD * (PowerSeries.X * D) ^ k) := by
    rw [hmain_ps]
  rw [hR]
  have hmul_eq : PowerSeries.coeff n ((2 - D) * BD * (PowerSeries.X * D) ^ k) =
      PowerSeries.coeff n (((2 - D) * (PowerSeries.X * D) ^ k) * P n) := by
    rw [show (2 - D) * BD * (PowerSeries.X * D) ^ k =
        ((2 - D) * (PowerSeries.X * D) ^ k) * BD by ring]
    rw [hcoeff_mul, hcoeff_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hBD_eq_P n (n - i) (by omega)]
  rw [hmul_eq]
  dsimp only [P]
  rw [Finset.mul_sum, map_sum]
  have hsub : Finset.range (n - k + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hrew : (2 - D) * (PowerSeries.X * D) ^ k *
        (PowerSeries.C (Nat.choose (2 * i) i : ℚ) * (PowerSeries.X * D) ^ i) =
        PowerSeries.C (Nat.choose (2 * i) i : ℚ) * ((2 - D) * (PowerSeries.X * D) ^ (i + k)) := by
      rw [pow_add]
      ring
    rw [hrew, PowerSeries.coeff_C_mul]
  · intro i _ hi
    have hgt : n < i + k := by
      have : ¬ i < n - k + 1 := fun h => hi (Finset.mem_range.mpr h)
      omega
    have hrew : (2 - D) * (PowerSeries.X * D) ^ k *
        (PowerSeries.C (Nat.choose (2 * i) i : ℚ) * (PowerSeries.X * D) ^ i) =
        (PowerSeries.C (Nat.choose (2 * i) i : ℚ) * (2 - D)) * (PowerSeries.X * D) ^ (i + k) := by
      rw [pow_add]
      ring
    rw [hrew]
    exact hXD_mul_zero _ (i + k) n hgt
