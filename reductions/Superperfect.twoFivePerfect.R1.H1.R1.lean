import OMAReductions.R_Superperfect_twoFivePerfect_R1

-- Reduction Superperfect.twoFivePerfect.R1.H1.R1 of step Superperfect.twoFivePerfect.R1.H1
-- Credit: @Ciphore
-- The stripped equation `σ((σ(p^e)/5) * σ(u)) = p^e * u` separates by the coprime remainder.
-- When `u = 1` the unitary factor is trivial and the equation is a single-prime-power
-- sigma-preimage problem: `σ` of the stripped number `σ(p^e)/5` must not equal the prime
-- power `p^e`. Prime-power values of the divisor-sum function are the classical
-- Nagell--Ljunggren terrain, a self-contained arithmetic core.
-- When `1 < u` the coprime interaction between the stripped power and `σ(u)` is the
-- independent core.

namespace OMA.R_Superperfect_twoFivePerfect_R1_H1_R1

open ArithmeticFunction ArithmeticFunction.sigma

/-- The single-prime-power core of the `p ≡ 1 (mod 5)` residue case: with no coprime
    remainder, the equation asks `σ` of the stripped number `σ(p^e)/5` to be the prime
    power `p^e`. -/
def H1 : Prop := ∀ p e : ℕ, p.Prime → (p : ZMod 5) = 1 → 5 ∣ e + 1 →
  σ 1 (σ 1 (p ^ e) / 5) ≠ p ^ e

/-- The coprime-interaction core of the `p ≡ 1 (mod 5)` residue case: a nontrivial coprime
    remainder `u` makes the equation a genuine two-component interaction. -/
def H2 : Prop := ∀ p e u : ℕ, p.Prime → p.Coprime u → 1 < u →
  (p : ZMod 5) = 1 → 5 ∣ e + 1 → σ 1 ((σ 1 (p ^ e) / 5) * σ 1 u) ≠ p ^ e * u

theorem main : H1 → H2 → OMA.R_Superperfect_twoFivePerfect_R1.H1 := by
  intro hpure hinter p e u hp hu hu0 hp1 h5
  by_cases hu1 : u = 1
  · subst hu1
    simpa using hpure p e hp hp1 h5
  · exact hinter p e u hp hu (by omega) hp1 h5

end OMA.R_Superperfect_twoFivePerfect_R1_H1_R1
