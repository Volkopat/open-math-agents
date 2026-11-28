import OMAStatements.S_oeis_a027642

-- Problem: A027642, Gladkovskii's Bernoulli continued fraction.
-- Credit: @CubeJerry (agent: codex, model: gpt-6.2-astra)
-- Classical background: Lambert's continued fraction for the hyperbolic cotangent.
-- The explicit formal-series construction, tail uniqueness, and exact-conjecture
-- identification below were independently developed for this statement.


namespace A027642Proof
open PowerSeries

/-- The even coefficients of the auxiliary hypergeometric series. -/
def h (j n : ℕ) : ℚ :=
  ((j+n).factorial : ℚ) /
    ((4:ℚ)^n * (n.factorial : ℚ) * ((2*j+2*n).factorial : ℚ))

/-- A family of formal series giving the tails of Lambert's continued fraction. -/
noncomputable def H (j : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun m => if m % 2 = 0 then h j (m/2) else 0

/-- The tails of the continued fraction in A027642. -/
noncomputable def Q (k : ℕ) : ℚ⟦X⟧ :=
  X + H (2*k) * (H (2*k+1))⁻¹

theorem coeff_H_even (j n : ℕ) : coeff (2*n) (H j) = h j n := by
  simp [H, Nat.mul_comm]

theorem coeff_H_odd (j n : ℕ) : coeff (2*n+1) (H j) = 0 := by
  simp [H, Nat.add_mod]

theorem constantCoeff_H (j : ℕ) :
    constantCoeff (H j) = (j.factorial : ℚ) / ((2*j).factorial : ℚ) := by
  simp [H, h]

theorem constantCoeff_H_ne_zero (j : ℕ) : constantCoeff (H j) ≠ 0 := by
  rw [constantCoeff_H]
  exact div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero j)
    (by exact_mod_cast Nat.factorial_ne_zero (2*j))

theorem H_ne_zero (j : ℕ) : H j ≠ 0 := by
  intro hz
  have hc := constantCoeff_H_ne_zero j
  apply hc
  rw [hz, map_zero]

theorem isUnit_H (j : ℕ) : IsUnit (H j) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  exact isUnit_iff_ne_zero.mpr (constantCoeff_H_ne_zero j)

theorem h_recur_zero (j : ℕ) : h j 0 = (4*(j:ℚ)+2)*h (j+1) 0 := by
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  unfold h
  field_simp [hf]
  have hj : 2*(j+1)+2*0 = 2*j+1+1 := by omega
  simp only [hj, Nat.add_zero, Nat.mul_zero, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem h_recur_succ (j n : ℕ) :
    h j (n+1) = (4*(j:ℚ)+2)*h (j+1) (n+1) + h (j+2) n := by
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  unfold h
  field_simp [hf]
  have h1 : j+(n+1) = j+n+1 := by omega
  have h2 : j+1+(n+1) = j+n+1+1 := by omega
  have h3 : j+2+n = j+n+1+1 := by omega
  have h4 : 2*j+2*(n+1) = 2*j+2*n+1+1 := by omega
  have h5 : 2*(j+1)+2*(n+1) = 2*j+2*n+1+1+1+1 := by omega
  have h6 : 2*(j+2)+2*n = 2*j+2*n+1+1+1+1 := by omega
  simp only [h1, h2, h3, h4, h5, h6, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

theorem H_recur (j : ℕ) :
    H j = C (4*(j:ℚ)+2)*H (j+1) + X^2*H (j+2) := by
  ext m
  rw [map_add, coeff_C_mul, coeff_X_pow_mul']
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · obtain ⟨n, rfl⟩ : ∃ n, m = 2*n := ⟨m/2, by omega⟩
    cases n with
    | zero =>
      simp only [Nat.mul_zero, show ¬(2 ≤ 0) by omega, if_false, add_zero]
      simpa [H] using h_recur_zero j
    | succ n =>
      rw [if_pos (by omega), show 2*(n+1)-2 = 2*n by omega]
      simpa only [coeff_H_even] using h_recur_succ j n
  · obtain ⟨n, rfl⟩ : ∃ n, m = 2*n+1 := ⟨m/2, by omega⟩
    cases n with
    | zero => simp [H]
    | succ n =>
      rw [if_pos (by omega), show 2*(n+1)+1-2 = 2*n+1 by omega]
      simp [coeff_H_odd]

end A027642Proof



namespace A027642Proof
open PowerSeries OMA.S_oeis_a027642

noncomputable def ratio (j : ℕ) : ℚ⟦X⟧ := H j * (H (j+1))⁻¹

theorem constantCoeff_ratio (j : ℕ) :
    constantCoeff (ratio j) = 4*(j:ℚ)+2 := by
  have hc := congrArg constantCoeff (H_recur j)
  simp only [map_add, map_mul, map_pow, constantCoeff_C, constantCoeff_X,
    zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at hc
  simp only [ratio, map_mul, constantCoeff_inv]
  rw [hc, mul_assoc, mul_inv_cancel₀ (constantCoeff_H_ne_zero (j+1)), mul_one]

theorem ratio_step (j : ℕ) :
    (ratio j - C (4*(j:ℚ)+2)) *
      (C (4*((j+1:ℕ):ℚ)+2)*ratio (j+2) + X^2) = X^2*ratio (j+2) := by
  have h1 := H_recur j
  have h2 : H (j+1) = C (4*((j+1:ℕ):ℚ)+2)*H (j+2) + X^2*H (j+3) := by
    simpa only [Nat.add_assoc] using H_recur (j+1)
  have hv := PowerSeries.mul_inv_cancel (H (j+1)) (constantCoeff_H_ne_zero (j+1))
  have hz := PowerSeries.mul_inv_cancel (H (j+3)) (constantCoeff_H_ne_zero (j+3))
  have hd : ratio j - C (4*(j:ℚ)+2) = X^2*H (j+2)*(H (j+1))⁻¹ := by
    unfold ratio
    rw [h1]
    calc
      (C (4*(j:ℚ)+2)*H (j+1)+X^2*H (j+2))*(H (j+1))⁻¹ - C (4*(j:ℚ)+2)
          = C (4*(j:ℚ)+2)*(H (j+1)*(H (j+1))⁻¹) +
            X^2*H (j+2)*(H (j+1))⁻¹ - C (4*(j:ℚ)+2) := by ring
      _ = X^2*H (j+2)*(H (j+1))⁻¹ := by rw [hv]; ring
  have he : C (4*((j+1:ℕ):ℚ)+2)*ratio (j+2)+X^2 =
      H (j+1)*(H (j+3))⁻¹ := by
    unfold ratio
    rw [h2]
    simp only [Nat.add_assoc]
    calc
      C (4*((j+1:ℕ):ℚ)+2)*(H (j+2)*(H (j+3))⁻¹)+X^2
          = C (4*((j+1:ℕ):ℚ)+2)*H (j+2)*(H (j+3))⁻¹ +
            X^2*(H (j+3)*(H (j+3))⁻¹) := by rw [hz]; ring
      _ = (C (4*((j+1:ℕ):ℚ)+2)*H (j+2)+X^2*H (j+3))*(H (j+3))⁻¹ := by ring
  rw [hd, he]
  unfold ratio
  simp only [Nat.add_assoc]
  calc
    X^2*H (j+2)*(H (j+1))⁻¹*(H (j+1)*(H (j+3))⁻¹)
        = X^2*H (j+2)*(H (j+1)*(H (j+1))⁻¹)*(H (j+3))⁻¹ := by ring
    _ = X^2*(H (j+2)*(H (j+3))⁻¹) := by rw [hv]; ring

theorem tailFamily_Q : TailFamily Q := by
  intro k
  constructor
  · change constantCoeff (X + ratio (2*k)) = 8*(k:ℚ)+2
    rw [map_add, constantCoeff_X, zero_add, constantCoeff_ratio]
    push_cast
    ring
  · change ((X + ratio (2*k)) - C (8*(k:ℚ)+2)) *
        (C (8*(k:ℚ)+6)*(X + ratio (2*(k+1))) - C (8*(k:ℚ)+6)*X + X^2) =
      X * (C (8*(k:ℚ)+6)*(X + ratio (2*(k+1))) -
        C (8*(k:ℚ)+6)*X + X*(X + ratio (2*(k+1))))
    have hc := ratio_step (2*k)
    have hA : 4*((2*k:ℕ):ℚ)+2 = 8*(k:ℚ)+2 := by push_cast; ring
    have hB : 4*((2*k+1:ℕ):ℚ)+2 = 8*(k:ℚ)+6 := by push_cast; ring
    rw [hA, hB, show 2*k+2 = 2*(k+1) by omega] at hc
    linear_combination hc

end A027642Proof


namespace A027642Proof

open PowerSeries
open OMA.S_oeis_a027642

lemma coeff_mul_of_lower_zero (n : ℕ) (f g : ℚ⟦X⟧)
    (hf : ∀ i < n, coeff i f = 0) :
    coeff n (f * g) = coeff n f * coeff 0 g := by
  rw [coeff_mul]
  apply Finset.sum_eq_single (n, 0)
  · intro p hp hne
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hlt : p.1 < n := by
      by_contra h
      have he : p = (n, 0) := by
        apply Prod.ext <;> omega
      exact hne he
    rw [hf p.1 hlt, zero_mul]
  · intro hnot
    exact (hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp))).elim

/-- A positive coefficient shift cannot support a nonzero infinite tail family
when every multiplier has nonzero constant coefficient. -/
lemma shifted_chain_zero (d U : ℕ → ℚ⟦X⟧)
    (hU : ∀ k, coeff 0 (U k) ≠ 0)
    (hrec : ∀ k, d k * U k = X ^ 4 * d (k + 1)) :
    ∀ k, d k = 0 := by
  have hc : ∀ n k, coeff n (d k) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k
      have he := congrArg (coeff n) (hrec k)
      rw [coeff_mul_of_lower_zero n (d k) (U k)
        (fun i hi => ih i hi k), coeff_X_pow_mul'] at he
      have hz : (if 4 ≤ n then coeff (n - 4) (d (k + 1)) else 0) = 0 := by
        by_cases hn : 4 ≤ n
        · rw [if_pos hn]
          exact ih (n - 4) (by omega) (k + 1)
        · rw [if_neg hn]
      rw [hz] at he
      exact (mul_eq_zero.mp he).resolve_right (hU k)
  intro k
  apply PowerSeries.ext
  intro n
  simpa only [map_zero] using hc n k

noncomputable def tailDen (Q : ℕ → ℚ⟦X⟧) (k : ℕ) : ℚ⟦X⟧ :=
  C (8 * (k : ℚ) + 6) * Q (k + 1) -
    C (8 * (k : ℚ) + 6) * X + X ^ 2

lemma tailDen_constant_ne_zero (Q : ℕ → ℚ⟦X⟧) (hQ : TailFamily Q) (k : ℕ) :
    constantCoeff (tailDen Q k) ≠ 0 := by
  have hp : (0 : ℚ) < (8 * (k : ℚ) + 6) * (8 * ((k + 1 : ℕ) : ℚ) + 2) := by
    positivity
  simpa [tailDen, (hQ (k + 1)).1] using ne_of_gt hp

lemma tailFamily_contraction (Q R : ℕ → ℚ⟦X⟧)
    (hQ : TailFamily Q) (hR : TailFamily R) (k : ℕ) :
    (Q k - R k) * tailDen Q k * tailDen R k =
      X ^ 4 * (Q (k + 1) - R (k + 1)) := by
  let A : ℚ⟦X⟧ := C (8 * (k : ℚ) + 2)
  let B : ℚ⟦X⟧ := C (8 * (k : ℚ) + 6)
  have hq : (Q k - A) * tailDen Q k =
      X * (B * Q (k + 1) - B * X + X * Q (k + 1)) := (hQ k).2
  have hr : (R k - A) * tailDen R k =
      X * (B * R (k + 1) - B * X + X * R (k + 1)) := (hR k).2
  calc
    (Q k - R k) * tailDen Q k * tailDen R k =
        (Q k - A) * tailDen Q k * tailDen R k -
          (R k - A) * tailDen R k * tailDen Q k := by ring
    _ = X * (B * Q (k + 1) - B * X + X * Q (k + 1)) * tailDen R k -
          X * (B * R (k + 1) - B * X + X * R (k + 1)) * tailDen Q k := by
      rw [hq, hr]
    _ = X ^ 4 * (Q (k + 1) - R (k + 1)) := by
      dsimp [tailDen, A, B]
      ring

theorem tailFamily_unique (Q R : ℕ → ℚ⟦X⟧)
    (hQ : TailFamily Q) (hR : TailFamily R) : Q = R := by
  let d (k : ℕ) : ℚ⟦X⟧ := Q k - R k
  let U (k : ℕ) : ℚ⟦X⟧ := tailDen Q k * tailDen R k
  have hU (k : ℕ) : coeff 0 (U k) ≠ 0 := by
    change coeff 0 (tailDen Q k * tailDen R k) ≠ 0
    rw [coeff_zero_eq_constantCoeff, map_mul]
    exact mul_ne_zero (tailDen_constant_ne_zero Q hQ k) (tailDen_constant_ne_zero R hR k)
  have hrec (k : ℕ) : d k * U k = X ^ 4 * d (k + 1) := by
    simpa only [d, U, mul_assoc] using tailFamily_contraction Q R hQ hR k
  funext k
  exact sub_eq_zero.mp (shifted_chain_zero d U hU hrec k)

end A027642Proof


namespace A027642Proof

open PowerSeries OMA.S_oeis_a027642

lemma half_pow_even (n : ℕ) : (1 / 2 : ℚ) ^ (2 * n) = 1 / (4 : ℚ) ^ n := by
  calc
    _ = ((1 / 2 : ℚ) ^ 2) ^ n := pow_mul _ _ _
    _ = (1 / 4 : ℚ) ^ n := by norm_num
    _ = 1 / (4 : ℚ) ^ n := by simp only [one_div, inv_pow]

lemma h_zero_half (n : ℕ) :
    h 0 n = (1 / 2 : ℚ) ^ (2 * n) / ((2 * n).factorial : ℚ) := by
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2n : ((2 * n).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hp : (4 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [h, half_pow_even]
  simp only [Nat.zero_add, Nat.mul_zero]
  field_simp [hn, h2n, hp]

lemma h_one_half (n : ℕ) :
    h 1 n = (1 / 2 : ℚ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℚ) := by
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hg : ((2 * n + 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n + 1)
  have hp : (4 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hd : (2 * (n : ℚ) + 1 + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (2 * n + 1)
  rw [h, show 1 + n = n + 1 by omega,
    show 2 * 1 + 2 * n = (2 * n + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ, pow_succ, half_pow_even]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp [hn, hg, hp, hd]
  ring

lemma coeff_X_H1_even (n : ℕ) : coeff (2 * n) (X * H 1) = 0 := by
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff]
  | succ n =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      coeff_succ_X_mul, coeff_H_odd]

lemma coeff_X_H1_odd (n : ℕ) : coeff (2 * n + 1) (X * H 1) = h 1 n := by
  rw [coeff_succ_X_mul, coeff_H_even]

/-- The even and odd auxiliary series combine to the exponential at half the variable. -/
lemma H0_add_X_H1 : H 0 + X * H 1 = rescale (1 / 2 : ℚ) (exp ℚ) := by
  ext n
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · rw [hk]
    simpa [coeff_H_even, coeff_X_H1_even, div_eq_mul_inv] using h_zero_half k
  · rw [hk]
    simpa [coeff_H_odd, coeff_H_even, coeff_X_H1_odd, div_eq_mul_inv] using h_one_half k

@[simp] lemma rescale_neg_H (j : ℕ) : rescale (-1 : ℚ) (H j) = H j := by
  ext n
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · rw [hk]
    simp [coeff_H_even, pow_mul]
  · rw [hk]
    simp [coeff_H_odd]

lemma H0_sub_X_H1 : H 0 - X * H 1 = rescale (- (1 / 2 : ℚ)) (exp ℚ) := by
  have he := congrArg (rescale (-1 : ℚ)) H0_add_X_H1
  simpa [rescale_X, rescale_rescale, sub_eq_add_neg] using he

lemma bernoulliEgf_eq_standard : bernoulliEgf = bernoulliPowerSeries ℚ := by
  ext n
  simp [bernoulliEgf, bernoulliPowerSeries]

lemma exp_sub_one_ne_zero : exp ℚ - 1 ≠ 0 := by
  intro he
  have hc := congrArg (coeff 1) he
  norm_num at hc

/-- Identify the initial continued-fraction tail with the Bernoulli series. -/
theorem bernoulli_eq_Q : bernoulliEgf = (1 / 2 : ℚ) • Q 0 - X := by
  have hprod : (H 0 + X * H 1) * (H 0 - X * H 1) = 1 := by
    rw [H0_add_X_H1, H0_sub_X_H1, exp_mul_exp_eq_exp_add]
    norm_num
  have hsquare : (H 0 + X * H 1) ^ 2 = exp ℚ := by
    rw [pow_two, H0_add_X_H1, exp_mul_exp_eq_exp_add]
    norm_num
  have hinv : H 1 * (H 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (constantCoeff_H_ne_zero 1)
  have hhalf : (2 : ℚ⟦X⟧) * C (1 / 2 : ℚ) = 1 := by
    change C (2 : ℚ) * C (1 / 2 : ℚ) = 1
    rw [← map_mul]
    norm_num
  let K : ℚ⟦X⟧ := C (1 / 2 : ℚ) * (H 0 * (H 1)⁻¹ - X)
  have hsmall : K * (2 * X * H 1) = X * (H 0 - X * H 1) := by
    calc
      _ = (2 * C (1 / 2 : ℚ)) * X *
          (H 0 * (H 1 * (H 1)⁻¹) - X * H 1) := by dsimp [K]; ring
      _ = _ := by rw [hhalf, hinv]; ring
  have hfactor : exp ℚ - 1 = (2 * X * H 1) * (H 0 + X * H 1) := by
    rw [← hsquare, ← hprod]
    ring
  have hK : K * (exp ℚ - 1) = X := by
    calc
      _ = (K * (2 * X * H 1)) * (H 0 + X * H 1) := by
        rw [hfactor]
        ring
      _ = X * ((H 0 + X * H 1) * (H 0 - X * H 1)) := by rw [hsmall]; ring
      _ = X := by rw [hprod, mul_one]
  have hb : bernoulliEgf = K := by
    apply mul_right_cancel₀ exp_sub_one_ne_zero
    rw [bernoulliEgf_eq_standard, bernoulliPowerSeries_mul_exp_sub_one, hK]
  rw [hb, Q, smul_eq_C_mul]
  norm_num only [Nat.mul_zero, Nat.zero_add]
  change C (1 / 2 : ℚ) * (H 0 * (H 1)⁻¹ - X) =
    C (1 / 2 : ℚ) * (X + H 0 * (H 1)⁻¹) - X
  calc
    _ = C (1 / 2 : ℚ) * (X + H 0 * (H 1)⁻¹) -
        (2 * C (1 / 2 : ℚ)) * X := by ring
    _ = _ := by rw [hhalf, one_mul]

end A027642Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a027642.main := by
  exact ⟨A027642Proof.Q, A027642Proof.tailFamily_Q,
    fun R hR => A027642Proof.tailFamily_unique R A027642Proof.Q hR
      A027642Proof.tailFamily_Q,
    A027642Proof.bernoulli_eq_Q⟩
