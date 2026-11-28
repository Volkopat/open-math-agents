import OMAStatements.S_mo_499750
import Mathlib

/- For even k, each prime divisor p of n=k+1 is a candidate. Failure
of its digit test forces n/p congruent to one modulo p. In particular n
is squarefree. Summing the prime cofactors and combining their congruences
forces the Giuga congruence modulo n. H2 retains the odd k and the
exceptional even k satisfying both necessary conditions. -/
namespace OMA.R_mo_499750_R1

def H1 : Prop :=
  ∀ k : ℕ, 78 < k → Odd (k + 1) →
    (¬ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k % p + k / p % p) →
    Squarefree (k+1) ∧
      (∑ p ∈ (k+1).primeFactors, (k+1)/p) ≡ 1 [MOD k+1]

def H2 : Prop :=
  ∀ k : ℕ, 78 < k →
    (Even (k+1) ∨ (Squarefree (k+1) ∧
      (∑ p ∈ (k+1).primeFactors, (k+1)/p) ≡ 1 [MOD k+1])) →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k % p + k / p % p

theorem main : H1 → H2 → type_of% @OMA.S_mo_499750.main := by
  intro obstruction residual k hk
  by_contra noPrime
  apply noPrime
  apply residual k hk
  rcases Nat.even_or_odd (k+1) with he | ho
  · exact Or.inl he
  · exact Or.inr (obstruction k hk ho noPrime)

end OMA.R_mo_499750_R1
