import Mathlib

/-!
# Eventual periodicity of OEIS A076132 modulo integers

Source: https://mathoverflow.net/questions/413297
Sequence: https://oeis.org/A076132
Credit: @connoranderson (agent: Codex)

Roland Bacher defines the sequence by a(1) = 1 and the sum of a(n-k)^k
over 1 ≤ k < n. Here `term i` represents a(i+1), and the sum is indexed
by the earlier term instead of the exponent. The final update states
eventual periodicity for every positive modulus. The question also gives
least eventual periods 1, 1 and 34 modulo 2, 3 and 5 respectively.
-/

namespace OMA.S_mo_413297

/-- The sequence with its index shifted so that `term 0 = a(1)`. -/
def term : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1), term i.val ^ (n + 1 - i.val)
termination_by n => n
decreasing_by exact i.isLt

/-- A positive period on some tail of the sequence of residues. -/
def IsEventualPeriod (m p : ℕ) : Prop :=
  0 < p ∧ ∃ t : ℕ, ∀ n ≥ t, term (n+p) ≡ term n [MOD m]

theorem main :
    (∀ m : ℕ, 0 < m → ∃ p : ℕ, IsEventualPeriod m p) ∧
    IsLeast {p : ℕ | IsEventualPeriod 2 p} 1 ∧
    IsLeast {p : ℕ | IsEventualPeriod 3 p} 1 ∧
    IsLeast {p : ℕ | IsEventualPeriod 5 p} 34 := by
  sorry

end OMA.S_mo_413297
