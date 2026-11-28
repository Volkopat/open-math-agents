import OMAStatements.S_oeis_a159807

namespace OMA.S_oeis_a159807

open PowerSeries



/-- b(n) = 11^n H_n(3/22). -/
def b : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | n + 2 => 3 * b (n + 1) - 242 * (n + 1) * b n

lemma H_eq (n : ℕ) : H n (3 / 22) = (b n : ℚ) / 11 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [H, b]
    · simp [H, b]; norm_num
    · rw [H, ih (n + 1) (by omega), ih n (by omega), b]
      push_cast
      field_simp
      ring

lemma b_mod (n : ℕ) : b n % 11 = 3 ^ n % 11 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [b]
    · simp [b]
    · rw [b, pow_succ, pow_succ]
      have h1 := ih (n + 1) (by omega)
      rw [pow_succ] at h1
      have : (3 * b (n + 1) - 242 * (↑n + 1) * b n) % 11 = (3 * b (n + 1)) % 11 := by
        rw [show (3 * b (n + 1) - 242 * (↑n + 1) * b n) = 3 * b (n + 1) + 11 * (-(22 * (↑n + 1) * b n)) by
          ring]
        exact Int.add_mul_emod_self_left _ _ _
      rw [this, Int.mul_emod, h1, ← Int.mul_emod]
      ring_nf

lemma not_dvd_b (n : ℕ) : ¬ (11 : ℤ) ∣ b n := by
  intro h
  have h1 := b_mod n
  have h0 : b n % 11 = 0 := Int.emod_eq_zero_of_dvd h
  rw [h0] at h1
  have h3 : ¬ (11 : ℤ) ∣ 3 ^ n := by
    intro hd
    have hp : Prime (11 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
    have := hp.dvd_of_dvd_pow hd
    norm_num at this
  exact h3 (Int.dvd_of_emod_eq_zero h1.symm)

lemma a_eq_b (n : ℕ) : a n = b n := by
  unfold a
  rw [H_eq]
  have hcop : IsCoprime (b n) ((11 : ℤ) ^ n) := by
    apply IsCoprime.pow_right
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hp : Nat.Prime 11 := by norm_num
    rcases Int.gcd_dvd_right (b n) 11 with ⟨c, hc⟩
    have hg : Int.gcd (b n) 11 ∣ 11 := by
      exact_mod_cast Int.gcd_dvd_right (b n) 11
    rcases (Nat.dvd_prime hp).mp hg with h | h
    · exact h
    · exfalso
      apply not_dvd_b n
      have := Int.gcd_dvd_left (b n) 11
      rw [h] at this
      exact_mod_cast this
  have h11 : (0 : ℤ) < 11 ^ n := by positivity
  have := Rat.num_div_eq_of_coprime h11 (Int.isCoprime_iff_gcd_eq_one.mp hcop)
  push_cast at this ⊢
  exact this

/-- The recurrence a(n) = 3 a(n-1) - 242 (n-1) a(n-2) for n >= 2. -/
theorem recurrence (n : ℕ) (hn : 2 ≤ n) : a n = 3 * a (n - 1) - 242 * (n - 1 : ℕ) * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [a_eq_b, a_eq_b, a_eq_b, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, b]
  push_cast
  ring

/-! ## The e.g.f. -/

/-- The power series -x (121 x - 3). -/
noncomputable def g : ℚ⟦X⟧ := -(X * (121 * X - 3))

lemma g_const : constantCoeff g = 0 := by simp [g]

lemma g_hasSubst : HasSubst g := HasSubst.of_constantCoeff_zero' g_const

lemma derivative_g : d⁄dX ℚ g = 3 - 242 * X := by
  have e : g = C (3 : ℚ) * X - C (121 : ℚ) * X ^ 2 := by
    rw [g, show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3,
      show (C (121 : ℚ) : ℚ⟦X⟧) = 121 from map_ofNat C 121]
    ring
  rw [e, map_sub, Derivation.leibniz, Derivation.leibniz, derivative_pow]
  simp only [derivative_C, derivative_X, smul_zero, add_zero, smul_eq_mul, mul_one]
  rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3,
    show (C (121 : ℚ) : ℚ⟦X⟧) = 121 from map_ofNat C 121]
  push_cast
  ring

/-- E(x) = exp(-x(121x - 3)). -/
noncomputable def E : ℚ⟦X⟧ := (exp ℚ).subst g

lemma E_deriv : d⁄dX ℚ E = E * (3 - 242 * X) := by
  rw [E, derivative_subst g_hasSubst, derivative_exp, derivative_g]

lemma E_const : constantCoeff E = 1 := by
  have h1 : (exp ℚ - 1).subst g = E - (1 : ℚ⟦X⟧).subst g := by
    rw [E, subst_sub g_hasSubst]
  have h2 : (1 : ℚ⟦X⟧).subst g = 1 := by
    rw [show (1 : ℚ⟦X⟧) = C (1 : ℚ) from (map_one C).symm, subst_C]
    simp
  have h3 : constantCoeff ((exp ℚ - 1).subst g) = 0 :=
    constantCoeff_subst_eq_zero g_const _ (by simp [constantCoeff_exp])
  rw [h1, h2, map_sub, map_one] at h3
  linear_combination h3

/-- F(x) = Sum a(n) x^n / n!. -/
noncomputable def F : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ) / (n.factorial : ℚ)

lemma F_deriv : d⁄dX ℚ F = F * (3 - 242 * X) := by
  ext n
  have e : F * (3 - 242 * X) = C (3 : ℚ) * F - C (242 : ℚ) * (F * X ^ 1) := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3,
      show (C (242 : ℚ) : ℚ⟦X⟧) = 242 from map_ofNat C 242]
    ring
  rw [e, coeff_derivative, map_sub, coeff_C_mul, coeff_C_mul, coeff_mul_X_pow']
  simp only [F, coeff_mk]
  rcases n with _ | n
  · simp [a_eq_b, b]
  · simp only [show 1 ≤ n + 1 by omega, if_true, show n + 1 - 1 = n by omega]
    have hr : a (n + 2) = 3 * a (n + 1) - 242 * ((n + 1 : ℕ) : ℤ) * a n := by
      rw [a_eq_b, a_eq_b, a_eq_b, b]; push_cast; ring
    rw [show n + 1 + 1 = n + 2 by omega, hr]
    rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    push_cast
    field_simp

lemma F_const : constantCoeff F = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [F, a_eq_b, b]

/-- The linear equation P' = P (3 - 242x) has at most one solution with a given constant term. -/
lemma ode_unique (P Q : ℚ⟦X⟧) (hP : d⁄dX ℚ P = P * (3 - 242 * X))
    (hQ : d⁄dX ℚ Q = Q * (3 - 242 * X)) (h0 : constantCoeff P = constantCoeff Q) : P = Q := by
  obtain ⟨D, hDdef⟩ : ∃ D : ℚ⟦X⟧, D = P - Q := ⟨_, rfl⟩
  have hD : d⁄dX ℚ D = C (3 : ℚ) * D - C (242 : ℚ) * (D * X ^ 1) := by
    rw [hDdef, map_sub, hP, hQ, show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3,
      show (C (242 : ℚ) : ℚ⟦X⟧) = 242 from map_ofNat C 242]
    ring
  have hD0 : constantCoeff D = 0 := by rw [hDdef, map_sub, h0, sub_self]
  have key : ∀ n, coeff n D = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · rw [coeff_zero_eq_constantCoeff_apply, hD0]
      · have hc := congrArg (coeff n) hD
        rw [coeff_derivative, map_sub, coeff_C_mul, coeff_C_mul, coeff_mul_X_pow'] at hc
        have hn : coeff n D = 0 := ih n (by omega)
        rw [hn] at hc
        have hne : (n + 1 : ℚ) ≠ 0 := by positivity
        split_ifs at hc with h1
        · rw [ih (n - 1) (by omega)] at hc
          simp only [mul_zero, sub_zero, mul_eq_zero] at hc
          exact hc.resolve_right hne
        · simp only [mul_zero, sub_zero, mul_eq_zero] at hc
          exact hc.resolve_right hne
  have hDz : D = 0 := PowerSeries.ext fun n => by rw [key n, map_zero]
  rw [hDdef] at hDz
  exact sub_eq_zero.mp hDz

/-- The e.g.f.: Sum a(n) x^n/n! = exp(-x(121x - 3)). -/
theorem egf : PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
    (exp ℚ).subst (-(X * (121 * X - 3)) : ℚ⟦X⟧) :=
  ode_unique F E F_deriv E_deriv (by rw [F_const, E_const])

/-- Both parts of the entry's formula: the e.g.f. and the recurrence. -/
theorem conjecture : PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
      (exp ℚ).subst (-(X * (121 * X - 3)) : ℚ⟦X⟧) ∧
    ∀ n : ℕ, 2 ≤ n → a n = 3 * a (n - 1) - 242 * (n - 1 : ℕ) * a (n - 2) :=
  ⟨egf, recurrence⟩

/-- Controls: a(0..4) = 1, 3, -233, -2151, 162705. -/
lemma controls : a 0 = 1 ∧ a 1 = 3 ∧ a 2 = -233 ∧ a 3 = -2151 ∧ a 4 = 162705 := by
  simp only [a_eq_b]
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> simp [b]

end OMA.S_oeis_a159807

theorem OMA.solution : type_of% @OMA.S_oeis_a159807.main :=
  OMA.S_oeis_a159807.conjecture
