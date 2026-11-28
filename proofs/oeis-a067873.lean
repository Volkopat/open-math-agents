import OMAStatements.S_oeis_a067873

/-!
For x = 170, E = 170² - 1 = 3² · 13² · 19 has just two prime factors
beyond its distinct factors. Two distinct square divisors already give
two Pell parameters. More generally, two such parameters always force
at least two excess prime factors, so the corrected lower bound is sharp.
-/

namespace MultiplePell

open OMA.S_oeis_a067873

private theorem distinct_le (n : ℕ) : littleOmega n ≤ bigOmega n :=
  List.toFinset_card_le _

private theorem big_mul {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0) :
    bigOmega (u*v) = bigOmega u + bigOmega v := by
  simpa [bigOmega] using (Nat.perm_primeFactorsList_mul hu hv).length_eq

private theorem composite_has_two {t : ℕ} (ht : 1 < t) (hc : ¬ t.Prime) : 2 ≤ bigOmega t := by
  change 2 ≤ ArithmeticFunction.cardFactors t
  have hpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr ht
  have hne := mt ArithmeticFunction.cardFactors_eq_one_iff_prime.mp hc
  omega

private theorem square_obstruction {E t : ℕ} (hE : 0 < E) (ht : 1 < t)
    (hcomp : ¬ t.Prime) (hd : t^2 ∣ E) : 2 ≤ bigOmega E - littleOmega E := by
  obtain ⟨k, hk⟩ := hd
  have ht0 : t ≠ 0 := by omega
  have hk0 : k ≠ 0 := by rintro rfl; simp_all
  have hs : t^2 ≠ 0 := pow_ne_zero _ ht0
  have hb : bigOmega E = bigOmega t + bigOmega t + bigOmega k := by
    rw [hk, big_mul hs hk0, pow_two, big_mul ht0 ht0]
  have hl : littleOmega E ≤ littleOmega t + littleOmega k := by
    unfold littleOmega
    rw [hk, Nat.primeFactors_mul hs hk0, Nat.primeFactors_pow t (by decide : 2 ≠ 0)]
    exact Finset.card_union_le _ _
  have h₂ := composite_has_two ht hcomp
  have h₁ := distinct_le t
  have h₃ := distinct_le k
  omega

/-- The sharp lower bound holds for either parity of the Pell solution. -/
theorem sharp_lower (x : ℕ) (h : InA067873 x) :
    2 ≤ bigOmega (x^2-1) - littleOmega (x^2-1) := by
  obtain ⟨hx, D₁, D₂, y₁, y₂, _, _, hy₁, hy₂, hD, hD₁, hD₂, eq₁, eq₂⟩ := h
  let E := x^2-1
  have hE : 0 < E := by
    have h : 1 < x^2 := by nlinarith
    exact Nat.sub_pos_of_lt h
  have e₁ : E = D₁*y₁^2 := by dsimp [E]; omega
  have e₂ : E = D₂*y₂^2 := by dsimp [E]; omega
  have lt₁ : 1 < y₁ := by
    by_contra! hle
    have : y₁ = 1 := by omega
    simp_all
  have lt₂ : 1 < y₂ := by
    by_contra! hle
    have : y₂ = 1 := by omega
    simp_all
  have d₁ : y₁^2 ∣ E := e₁ ▸ dvd_mul_left _ _
  have d₂ : y₂^2 ∣ E := e₂ ▸ dvd_mul_left _ _
  by_cases p₁ : y₁.Prime
  · by_cases p₂ : y₂.Prime
    · have ne : y₁ ≠ y₂ := by
        rintro rfl
        exact hD (Nat.eq_of_mul_eq_mul_right (by positivity : 0 < y₁^2) (e₁.symm.trans e₂))
      have cop := (Nat.coprime_primes p₁ p₂).mpr ne
      apply square_obstruction (t := y₁*y₂) hE (by nlinarith) (Nat.not_prime_mul (by omega) (by omega))
      rw [mul_pow]
      exact ((cop.pow_left 2).pow_right 2).mul_dvd_of_dvd_of_dvd d₁ d₂
    · exact square_obstruction hE lt₂ p₂ d₂
  · exact square_obstruction hE lt₁ p₁ d₁

theorem witness : InA067873 170 := by
  exact ⟨by decide, 3211, 171, 3, 13, by decide⟩

theorem excess_at_witness : bigOmega (170^2-1) - littleOmega (170^2-1) = 2 := by
  have f : Nat.primeFactorsList 28899 = [3, 3, 13, 13, 19] := by simp
  change (28899 : ℕ).primeFactorsList.length - (28899 : ℕ).primeFactorsList.toFinset.card = 2
  rw [f]
  decide

end MultiplePell

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a067873.main) := by
  intro claim
  have h := claim 170 MultiplePell.witness (by decide)
  rw [MultiplePell.excess_at_witness] at h
  omega
