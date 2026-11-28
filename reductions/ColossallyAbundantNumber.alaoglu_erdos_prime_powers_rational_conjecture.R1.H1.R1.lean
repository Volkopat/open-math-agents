import OMAReductions.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1

/-!
Separate the Gelfond-Schneider theorem from the four exponentials problem
with two transcendental ratios. The latter remains an open hypothesis.
-/

-- Reduction ColossallyAbundantNumber.alaoglu_erdos_prime_powers_rational_conjecture.R1.H1.R1
-- Credit: @John-A-McMahon

namespace OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1_H1_R1

/-- The two logarithms consequence of the Gelfond-Schneider theorem. -/
def H1 : Prop :=
  ∀ a z : ℂ, z ≠ 0 → IsAlgebraic ℚ a → (∀ q : ℚ, a ≠ (q : ℂ)) →
    IsAlgebraic ℚ (Complex.exp z) → Transcendental ℚ (Complex.exp (a * z))

/-- The normalized four exponentials problem with both ratios transcendental. -/
def H2 : Prop :=
  ∀ a b z : ℂ, z ≠ 0 → Transcendental ℚ a → Transcendental ℚ b →
    Transcendental ℚ (Complex.exp z) ∨
    Transcendental ℚ (Complex.exp (a * z)) ∨
    Transcendental ℚ (Complex.exp (b * z)) ∨
    Transcendental ℚ (Complex.exp (a * b * z))

lemma ratio_not_rational (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x) :
    ∀ q : ℚ, x 1 / x 0 ≠ (q : ℂ) := by
  intro q hq
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hpair : LinearIndependent ℚ ![x 0, x 1] := by
    convert hx using 1
    ext i
    fin_cases i <;> rfl
  have hrel : x 1 = (q : ℂ) * x 0 := (div_eq_iff hx0).mp hq
  have hzero : (-q) • x 0 + (1 : ℚ) • x 1 = 0 := by
    simp only [Rat.smul_def, Rat.cast_neg, Rat.cast_one, one_mul]
    rw [hrel]
    ring
  have hbad : (1 : ℚ) = 0 := ((LinearIndependent.pair_iff.mp hpair) (-q) 1 hzero).2
  norm_num at hbad

theorem main : H1 → H2 →
    OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1.H1 := by
  intro two four x y hx hy
  classical
  by_contra h
  have halg : ∀ i j, IsAlgebraic ℚ (Complex.exp (x i * y j)) := by
    intro i j
    by_contra ht
    exact h ⟨i, j, ht⟩
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hy0 : y 0 ≠ 0 := hy.ne_zero 0
  have hz : x 0 * y 0 ≠ 0 := mul_ne_zero hx0 hy0
  have ha : x 1 / x 0 * (x 0 * y 0) = x 1 * y 0 := by
    field_simp
  have hb : y 1 / y 0 * (x 0 * y 0) = x 0 * y 1 := by
    field_simp
  have hab : x 1 / x 0 * (y 1 / y 0) * (x 0 * y 0) = x 1 * y 1 := by
    field_simp
  have hta : Transcendental ℚ (x 1 / x 0) := by
    intro hia
    have ht := two _ _ hz hia (ratio_not_rational x hx) (halg 0 0)
    rw [ha] at ht
    exact ht (halg 1 0)
  have htb : Transcendental ℚ (y 1 / y 0) := by
    intro hib
    have ht := two _ _ hz hib (ratio_not_rational y hy) (halg 0 0)
    rw [hb] at ht
    exact ht (halg 0 1)
  rcases four _ _ _ hz hta htb with ht | ht | ht | ht
  · exact ht (halg 0 0)
  · rw [ha] at ht
    exact ht (halg 1 0)
  · rw [hb] at ht
    exact ht (halg 0 1)
  · rw [hab] at ht
    exact ht (halg 1 1)

end OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1_H1_R1
