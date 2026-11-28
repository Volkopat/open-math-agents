import Mathlib

/-!
# A019335: Primes with primitive root 5

Source: https://oeis.org/A019335
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (OEIS entry):
Let `Pi(N, b)` be the number of primes `p ≤ N` with `p ≡ b (mod 5)`, and let
`Q(N, b)` be the number of primes `p ≤ N` with `p ≡ b (mod 5)` having `5` as a primitive root.
Let `C` be Artin's constant `∏_{p prime} (1 - 1 / (p * (p - 1)))`.
Then as `N → ∞`:
  `Q(N, 2) ~ (20 / 19) * C * Pi(N, 2)` and `Q(N, 3) ~ (20 / 19) * C * Pi(N, 3)`.

Conventions:
- `5` is a primitive root modulo prime `p` iff `orderOf (5 : ZMod p) = p - 1`.
- Asymptotic equivalence `f(N) ~ g(N)` is stated as `f(N) / g(N) → 1` as `N → ∞`.
-/

namespace OMA.S_oeis_a019335

noncomputable def artinConst : ℝ :=
  ∏' p : {p : ℕ // Nat.Prime p}, (1 - 1 / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)))

noncomputable def piMod5 (N b : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun p => Nat.Prime p ∧ p % 5 = b).card

noncomputable def qMod5 (N b : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun p =>
    Nat.Prime p ∧ p % 5 = b ∧ orderOf (5 : ZMod p) = p - 1).card

theorem main :
    Filter.Tendsto
        (fun N : ℕ => (qMod5 N 2 : ℝ) / ((20 / 19 : ℝ) * artinConst * (piMod5 N 2 : ℝ)))
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto
        (fun N : ℕ => (qMod5 N 3 : ℝ) / ((20 / 19 : ℝ) * artinConst * (piMod5 N 3 : ℝ)))
        Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a019335
