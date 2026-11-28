import OMAStatements.S_oeis_a365777

/-!
The modulus-4 obstruction follows from Stephen Lamb,
"Corrected Modular Periodicity for a Weighted Stirling Family" (2026), Lemma 2.1 and
Theorem 3.1, since the two Stirling weights -2 and 2 agree modulo 4.
https://doi.org/10.5281/zenodo.23282887
-/

namespace A365777Proof

open OMA.S_oeis_a365777 PowerSeries

/-- The divided-power coefficients of the solution of `(2 - E) A' = 3 A`. -/
private def b : ℕ → ℤ
  | 0 => 1
  | n+1 => 3*b n +
      (∑ j ∈ Finset.range n, (n.choose (j+1) : ℤ)*2^(j+1)*b (n-j))
termination_by n => n
decreasing_by all_goals omega

private theorem bzero : b 0 = 1 := by rw [b]

private theorem brec (n : ℕ) :
    b (n+1) = 3*b n +
      (∑ j ∈ Finset.range n, (n.choose (j+1) : ℤ)*2^(j+1)*b (n-j)) := by
  rw [b]

private noncomputable def A : ℚ⟦X⟧ := mk fun n => (b n : ℚ)/(n.factorial : ℚ)

private def expConvolution (n : ℕ) (f : ℕ → ℚ) : ℚ :=
  ∑ j ∈ Finset.range (n+1), (n.choose j : ℚ) * 2^j * f (n-j)

private theorem coeff_exp2_mul (f : ℕ → ℚ) (B : ℚ⟦X⟧)
    (hB : ∀ n, coeff n B = f n / (n.factorial : ℚ)) (n : ℕ) :
    coeff n (exp2 * B) = expConvolution n f / (n.factorial : ℚ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => coeff j exp2 * coeff k B) n, expConvolution, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
  have hfac : (n.choose j : ℚ) * (j.factorial : ℚ) * ((n-j).factorial : ℚ) =
      (n.factorial : ℚ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  rw [hB, exp2, coeff_mk]
  have h0 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((n-j).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  rw [← hfac]
  ring

private theorem coeff_deriv_A (n : ℕ) :
    coeff n (derivative ℚ A) = (b (n+1) : ℚ) / (n.factorial : ℚ) := by
  rw [coeff_derivative, A, coeff_mk, Nat.factorial_succ]
  push_cast
  field_simp

private theorem ode : (2 - exp2) * derivative ℚ A = 3*A := by
  ext n
  have htail : expConvolution n (fun k => (b (k+1) : ℚ)) =
      (∑ j ∈ Finset.range n, (n.choose (j+1) : ℚ) * 2^(j+1) * (b (n-j) : ℚ)) +
      (b (n+1) : ℚ) := by
    rw [expConvolution, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have h : n-(j+1)+1 = n-j := by have := Finset.mem_range.mp hj; omega
    rw [h]
  have hrec := congrArg (fun z : ℤ => (z : ℚ)) (brec n)
  push_cast at hrec
  rw [sub_mul, map_sub, ← map_ofNat (C (R := ℚ)) 3, ← map_ofNat (C (R := ℚ)) 2,
    coeff_C_mul, coeff_C_mul, coeff_exp2_mul _ _ coeff_deriv_A, coeff_deriv_A, htail]
  rw [show coeff n A = (b n : ℚ)/(n.factorial : ℚ) by simp [A]]
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linarith

private theorem exp2_diff : derivative ℚ exp2 = 2*exp2 := by
  rw [show (2 : ℚ⟦X⟧) = C 2 by simp only [map_ofNat]]
  ext n
  simp only [coeff_derivative, coeff_C_mul, exp2, coeff_mk, pow_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_succ]
  field_simp

private theorem A0 : constantCoeff A = 1 := by simp [A,bzero]

private theorem quartic (A : ℚ⟦X⟧) (h0 : constantCoeff A = 1)
    (hode : (2-exp2) * derivative ℚ A = 3*A) :
    A^4 * (2-exp2)^3 = exp2^3 := by
  have hd : derivative ℚ (2-exp2) = -(2*exp2) := by
    rw [map_sub, show (2 : ℚ⟦X⟧) = C 2 by simp only [map_ofNat], derivative_C, zero_sub, exp2_diff, map_ofNat]
  let D := A^4 * (2-exp2)^3 - exp2^3
  have hD : derivative ℚ D = 6*D := by
    dsimp only [D]
    rw [map_sub, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      derivative_pow, derivative_pow, derivative_pow, hd, exp2_diff]
    linear_combination 4*A^3*(2-exp2)^2 * hode
  have vanish (n : ℕ) : coeff n D = 0 := by
    induction n with
    | zero => norm_num [D, coeff_zero_eq_constantCoeff, h0, exp2, map_ofNat]
    | succ n ih =>
      have h := congrArg (coeff n) hD
      rw [coeff_derivative, show (6 : ℚ⟦X⟧) = C 6 by simp only [map_ofNat], coeff_C_mul, ih, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (by positivity)
  apply sub_eq_zero.mp
  exact PowerSeries.ext fun n => (vanish n).trans (map_zero _).symm

private theorem modStep (n : ℕ) : (b (n+1) : ZMod 4) = (3+2*(n : ZMod 4))*b n := by
  obtain _ | n := n
  · norm_num [brec, bzero]
  · have h := congrArg (fun z : ℤ => (z : ZMod 4)) (brec (n+1))
    push_cast at h
    rw [Finset.sum_range_succ'] at h
    have twoSq : (2 : ZMod 4)^2 = 0 := by decide
    have tail (j : ℕ) : (2 : ZMod 4)^(j+1+1) = 0 := by
      rw [show j+1+1 = j+2 by omega, pow_add, twoSq, mul_zero]
    simp [tail] at h
    push_cast
    exact h.trans (by ring)

/-- The four residues 1, 3, 3, 1 are values of this polynomial. -/
private def residue (x : ZMod 4) : ZMod 4 := 1+x*(x+1)

private theorem residues (n : ℕ) : (b n : ZMod 4) = residue n := by
  induction n with
  | zero => simp [bzero,residue]
  | succ n ih =>
    rw [modStep, ih]
    push_cast
    exact (by decide : ∀ x : ZMod 4, (3+2*x)*residue x=residue (x+1)) _

private theorem period_false : ¬ ∃ N p : ℕ, 0 < p ∧ p ∣ Nat.totient 4 ∧
    ∀ n : ℕ, N ≤ n → b (n+p) ≡ b n [ZMOD (4 : ℤ)] := by
  rintro ⟨N,p,hp,hd,h⟩
  rw [show Nat.totient 4 = 2 by decide] at hd
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hd
  have h₂ : b (N+2) ≡ b N [ZMOD (4 : ℤ)] := by
    rcases (show p=1 ∨ p=2 by omega) with rfl | rfl
    · exact (h (N+1) (by omega)).trans (h N le_rfl)
    · exact h N le_rfl
  have he := (ZMod.intCast_eq_intCast_iff _ _ 4).2 h₂
  rw [residues, residues] at he
  push_cast at he
  exact (by decide : ∀ x : ZMod 4, residue (x+2) ≠ residue x) _ he

end A365777Proof

open A365777Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a365777.main) := by
  intro conjecture
  apply period_false
  exact conjecture A b A0 (quartic A A0 ode) (by intro n; simp [A]) 4 (by decide)
