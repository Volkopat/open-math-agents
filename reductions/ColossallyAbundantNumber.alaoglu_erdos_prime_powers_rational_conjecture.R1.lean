import FormalConjectures.Wikipedia.ColossallyAbundantNumber

-- Reduction ColossallyAbundantNumber.alaoglu_erdos_prime_powers_rational_conjecture.R1
-- of the Alaoglu–Erdős rational prime-powers conjecture
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The Alaoglu–Erdős rational prime-powers conjecture from the four exponentials conjecture

Alaoglu and Erdős (1944) asked whether `p ^ x` and `q ^ x` rational, for distinct primes `p`, `q`
and real `x`, forces `x` to be an integer. This is the classical consequence of the four
exponentials conjecture (Lang, Ramachandra; see Waldschmidt, *Diophantine approximation on linear
algebraic groups*, section 1.3).

* `H1` (open, and STRONGER than the target): the four exponentials conjecture, with the same
  statement as the catalogue problem `Exponentials.four_exponentials_conjecture`. This is an
  upward reduction: the target is the special case `x = (log p, log q)`, `y = (1, x)`.
* `H2` (elementary): a rational power of a prime that is a rational number has an integer
  exponent (compare `p`-adic valuations).

`main`: if `x` is irrational then `1, x` are linearly independent over `ℚ`, and so are
`log p, log q` (a rational relation gives `q ^ n = p ^ m` with `n > 0`, so `q ∣ p`). By `H1` one
of `p`, `q`, `p ^ x`, `q ^ x` is transcendental, but all four are rational. So `x` is rational
and `H2` applies.
-/

namespace OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1

/-- The four exponentials conjecture. -/
def H1 : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 2 → ℂ), LinearIndependent ℚ x → LinearIndependent ℚ y →
    ∃ i j : Fin 2, Transcendental ℚ (Complex.exp (x i * y j))

/-- A rational power of a prime that is rational has an integer exponent. -/
def H2 : Prop :=
  ∀ (p : ℕ) (t : ℚ), p.Prime → (∃ r : ℚ, (p : ℝ) ^ (t : ℝ) = r) → ∃ k : ℤ, t = k

/-- The logarithms of two distinct primes are linearly independent over `ℚ`. -/
lemma log_indep {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (s t : ℚ)
    (h : (s : ℝ) * Real.log p + (t : ℝ) * Real.log q = 0) : s = 0 ∧ t = 0 := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  by_cases ht : t = 0
  · subst ht
    simp only [Rat.cast_zero, zero_mul, add_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact ⟨by exact_mod_cast h, rfl⟩
    · exact absurd h hlp.ne'
  exfalso
  -- log q = c * log p with c = -s / t a positive rational
  set c : ℚ := -s / t with hc
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hcq : Real.log q = (c : ℝ) * Real.log p := by
    rw [hc]
    push_cast
    field_simp
    linarith
  have hcpos : 0 < c := by
    have : 0 < (c : ℝ) := by
      by_contra hneg
      have : (c : ℝ) * Real.log p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hlp.le
      linarith
    exact_mod_cast this
  have hnum : 0 < c.num := Rat.num_pos.mpr hcpos
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hnum.le
  have hm0 : 0 < m := by omega
  have hcm : (c : ℝ) = (m : ℝ) / (c.den : ℝ) := by
    have h1 : (c : ℝ) = ((c.num : ℚ) / (c.den : ℚ) : ℚ) := by rw [Rat.num_div_den]
    rw [h1, hm]
    push_cast
    rfl
  have hden : (0 : ℝ) < c.den := by exact_mod_cast c.den_pos
  have hlog : Real.log ((q : ℝ) ^ c.den) = Real.log ((p : ℝ) ^ m) := by
    rw [Real.log_pow, Real.log_pow, hcq, hcm]
    field_simp
  have hpow : (q : ℝ) ^ c.den = (p : ℝ) ^ m :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by have := hq.pos; positivity))
      (Set.mem_Ioi.mpr (by have := hp.pos; positivity)) hlog
  have hnat : q ^ c.den = p ^ m := by exact_mod_cast hpow
  have hdvd : q ∣ p ^ m := by
    rw [← hnat]
    exact dvd_pow_self q c.den_pos.ne'
  have := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)
  exact hpq this.symm

theorem main : H1 → H2 →
    type_of% @ColossallyAbundantNumber.alaoglu_erdos_prime_powers_rational_conjecture := by
  intro four rat p q x hp hq hpq hr₁ hr₂
  by_cases hx : Irrational x
  · exfalso
    obtain ⟨r₁, h₁⟩ := hr₁
    obtain ⟨r₂, h₂⟩ := hr₂
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hX : LinearIndependent ℚ ![((Real.log p : ℝ) : ℂ), ((Real.log q : ℝ) : ℂ)] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      apply log_indep hp hq hpq s t
      have h' : (((s : ℝ) * Real.log p + (t : ℝ) * Real.log q : ℝ) : ℂ) = 0 := by
        rw [← hst]
        simp only [Rat.smul_def, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ratCast]
      exact Complex.ofReal_eq_zero.mp h'
    have hY : LinearIndependent ℚ ![(1 : ℂ), (x : ℂ)] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hre : (s : ℝ) + (t : ℝ) * x = 0 := by
        have h' : (((s : ℝ) + (t : ℝ) * x : ℝ) : ℂ) = 0 := by
          rw [← hst]
          simp only [Rat.smul_def, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ratCast,
            mul_one]
        exact Complex.ofReal_eq_zero.mp h'
      by_cases ht : t = 0
      · subst ht
        simp only [Rat.cast_zero, zero_mul, add_zero] at hre
        exact ⟨by exact_mod_cast hre, rfl⟩
      · exfalso
        have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
        apply hx
        refine ⟨-s / t, ?_⟩
        push_cast
        field_simp
        linarith
    obtain ⟨i, j, hij⟩ := four _ _ hX hY
    apply hij
    have key : ∀ r : ℚ, IsAlgebraic ℚ ((r : ℝ) : ℂ) := fun r => by
      have := isAlgebraic_algebraMap (R := ℚ) (A := ℂ) r
      simpa using this
    have e1 : Complex.exp ((Real.log p : ℝ) : ℂ) = (((p : ℚ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hp0]
      simp
    have e2 : Complex.exp ((Real.log q : ℝ) : ℂ) = (((q : ℚ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hq0]
      simp
    have e3 : Complex.exp (((Real.log p : ℝ) : ℂ) * (x : ℂ)) = ((r₁ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← h₁, Real.rpow_def_of_pos hp0]
    have e4 : Complex.exp (((Real.log q : ℝ) : ℂ) * (x : ℂ)) = ((r₂ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← h₂, Real.rpow_def_of_pos hq0]
    fin_cases i <;> fin_cases j
    · show IsAlgebraic ℚ (Complex.exp (((Real.log p : ℝ) : ℂ) * 1))
      rw [mul_one, e1]
      exact key p
    · show IsAlgebraic ℚ (Complex.exp (((Real.log p : ℝ) : ℂ) * (x : ℂ)))
      rw [e3]
      exact key r₁
    · show IsAlgebraic ℚ (Complex.exp (((Real.log q : ℝ) : ℂ) * 1))
      rw [mul_one, e2]
      exact key q
    · show IsAlgebraic ℚ (Complex.exp (((Real.log q : ℝ) : ℂ) * (x : ℂ)))
      rw [e4]
      exact key r₂
  · rw [Irrational, not_not] at hx
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨k, hk⟩ := rat p t hp hr₁
    exact ⟨k, by rw [hk]; push_cast; rfl⟩

end OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1
