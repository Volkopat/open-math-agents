import OMAReductions.R_Superperfect_twoFivePerfect_R1

-- Reduction Superperfect.twoFivePerfect.R1.H3.R1 of step Superperfect.twoFivePerfect.R1.H3
-- Credit: @Ciphore
-- The `p ≡ 2, 3 (mod 5)` residue classes have order `4` modulo `5`, and the exponent
-- constraint `4 ∣ e + 1` makes the geometric sum factor cyclotomically: with `e + 1`
-- divisible by `4` the terms group into blocks `p^(4j) * (1 + p + p^2 + p^3)`, and
-- `1 + p + p^2 + p^3 = (1 + p)(1 + p^2)` is divisible by `5` exactly when `p` has order
-- `4`. The stripped number therefore carries a richer factor structure than in the
-- lower-order residue classes. As there, the equation separates by the coprime remainder.

namespace OMA.R_Superperfect_twoFivePerfect_R1_H3_R1

open ArithmeticFunction ArithmeticFunction.sigma

/-- The single-prime-power core of the order-four residue case. -/
def H1 : Prop := ∀ p e : ℕ, p.Prime → ((p : ZMod 5) = 2 ∨ (p : ZMod 5) = 3) → 4 ∣ e + 1 →
  σ 1 (σ 1 (p ^ e) / 5) ≠ p ^ e

/-- The coprime-interaction core of the order-four residue case. -/
def H2 : Prop := ∀ p e u : ℕ, p.Prime → p.Coprime u → 1 < u →
  ((p : ZMod 5) = 2 ∨ (p : ZMod 5) = 3) → 4 ∣ e + 1 →
  σ 1 ((σ 1 (p ^ e) / 5) * σ 1 u) ≠ p ^ e * u

theorem main : H1 → H2 → OMA.R_Superperfect_twoFivePerfect_R1.H3 := by
  intro hpure hinter p e u hp hu hu0 hp1 h5
  by_cases hu1 : u = 1
  · subst hu1
    simpa using hpure p e hp hp1 h5
  · exact hinter p e u hp hu (by omega) hp1 h5

end OMA.R_Superperfect_twoFivePerfect_R1_H3_R1
