import OMAReductions.R_oeis_a025064_R1

/-! A composite half-successor gives an explicit witness with first entry one. -/

namespace OMA.R_oeis_a025064_R1_H1_R1

open OMA.S_oeis_a025064

/-- The remaining case in which both the half-successor and the original number are prime. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 1848 < 2 * p - 1 → (2 * p - 1).Prime →
    Representable (2 * p - 1)

/-- The remaining case in which the half-successor is prime and the original number is composite. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 1848 < 2 * p - 1 → ¬ (2 * p - 1).Prime →
    Representable (2 * p - 1)

lemma of_factorization {m p r : ℕ} (hp : 3 ≤ p) (hpr : p ≤ r)
    (hm : m + 1 = 2 * (p * r)) : Representable m := by
  let b := p - 1
  let c := 2 * r - 1
  have hb : b + 1 = p := by dsimp [b]; omega
  have hc : c + 1 = 2 * r := by dsimp [c]; omega
  have hprod : m + 1 = (b + 1) * (c + 1) := by rw [hb, hc, hm]; ring
  refine ⟨1, b, c, by decide, by omega, by omega, ?_⟩
  nlinarith only [hprod]

theorem main : H1 → H2 → OMA.R_oeis_a025064_R1.H1 := by
  intro hPrime hComposite m hm hmod
  let q := (m + 1) / 2
  have hq : m + 1 = 2 * q := by dsimp [q]; omega
  have hOdd : q % 2 = 1 := by omega
  by_cases hqp : q.Prime
  · have heq : m = 2 * q - 1 := by omega
    rw [heq] at hm ⊢
    by_cases hp : (2 * q - 1).Prime
    · exact hPrime q hqp hm hp
    · exact hComposite q hqp hm hp
  · let p := q.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega : q ≠ 1)
    obtain ⟨r, hr⟩ := (show p ∣ q from Nat.minFac_dvd q)
    have hr₂ : 2 ≤ r := by
      by_contra! h
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · simp at hr
        omega
      · apply hqp
        rwa [hr, mul_one]
    have hpr : p ≤ r :=
      Nat.minFac_le_of_dvd hr₂ ⟨p, by rw [hr, mul_comm]⟩
    have hp₃ : 3 ≤ p := by
      have hp₂ := hp.two_le
      by_contra! h
      have heq : p = 2 := by omega
      rw [heq] at hr
      omega
    exact of_factorization hp₃ hpr (hq.trans (congrArg (2 * ·) hr))

end OMA.R_oeis_a025064_R1_H1_R1
