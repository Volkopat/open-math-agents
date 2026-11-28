import OMAReductions.R_AgohGiuga_agoh_giuga_R1

/-!
Reduction of step AgohGiuga.agoh_giuga.R1.H2 along Giuga's characterization of strong
Giuga numbers as Carmichael numbers satisfying the Giuga divisibility condition.
-/

-- Reduction AgohGiuga.agoh_giuga.R1.H2.R1 of step AgohGiuga.agoh_giuga.R1.H2
-- Splits the no-strong-Giuga-number statement along Giuga's characterization:
-- every strong Giuga number is Carmichael and satisfies the Giuga divisibility
-- condition; the remaining core is the squarefree Korselt plus Giuga condition.

namespace OMA.R_AgohGiuga_agoh_giuga_R1_H2_R1

open AgohGiuga

-- Giuga (1950): every strong Giuga number is a Carmichael number.
def H1 : Prop :=
  ∀ n : ℕ, IsStrongGiuga n → IsCarmichael n

-- Giuga (1950): every strong Giuga number satisfies p ∣ (n / p - 1) for each prime factor p.
def H2 : Prop :=
  ∀ n : ℕ, IsStrongGiuga n → ∀ p ∈ n.primeFactors, p ∣ (n / p - 1)

-- Open arithmetic core: no composite squarefree integer satisfies both
-- Korselt's criterion and Giuga's divisibility condition.
def H3 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n →
    (∀ p ∈ n.primeFactors, (p - 1 : ℕ) ∣ (n - 1 : ℕ)) →
    (∀ p ∈ n.primeFactors, p ∣ (n / p - 1)) → False

theorem main : H1 → H2 → H3 → OMA.R_AgohGiuga_agoh_giuga_R1.H2 := by
  intro h1 h2 h3 n hsg
  have hcarm : IsCarmichael n := h1 n hsg
  have hkorselt := (AgohGiuga.korselts_criterion n hsg.1).mp hcarm
  exact h3 n hsg.1 hkorselt.1 (fun p hp => by
    exact hkorselt.2 p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1) (h2 n hsg)

end OMA.R_AgohGiuga_agoh_giuga_R1_H2_R1
