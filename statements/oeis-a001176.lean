import Mathlib

/-!
# A001176: Density conjecture for zeros in the fundamental period of Fibonacci numbers mod p

Source: https://oeis.org/A001176
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A001176: Number of zeros in fundamental period of Fibonacci numbers mod n.

Statement:
Conjecture: 1/6 of the primes congruent to 1 or 9 mod 40 satisfy a(p^e) = 1, 2/3 of them
satisfy a(p^e) = 2 and 1/6 of them satisfy a(p^e) = 4; also, 1/2 of the primes congruent to
21 or 29 mod 40 satisfy a(p^e) = 1 and 1/2 of them satisfy a(p^e) = 4.

Conventions:
- For any odd prime `p` and `e >= 1`, `a(p^e) = a(p)`, so we state the natural densities
  over primes `p` in the respective residue classes modulo 40.
-/

namespace OMA.S_oeis_a001176

/-- The Pisano period modulo `m`. -/
noncomputable def pisanoPeriod (m : ℕ) : ℕ :=
  sInf {p : ℕ | 0 < p ∧ ∀ n : ℕ, Nat.fib (n + p) % m = Nat.fib n % m}

/-- `A001176(m)`: number of zeros in one fundamental period of Fibonacci numbers mod `m`. -/
noncomputable def fibZeros (m : ℕ) : ℕ :=
  ((Finset.range (pisanoPeriod m)).filter (fun k => Nat.fib k % m = 0)).card

/-- Primes `< x` congruent to `r₁` or `r₂` modulo 40. -/
noncomputable def primesMod40 (r₁ r₂ x : ℕ) : Finset ℕ :=
  (Finset.range x).filter (fun p => Nat.Prime p ∧ (p % 40 = r₁ ∨ p % 40 = r₂))

/-- Proportion of primes `< x` in residue classes `r₁, r₂ (mod 40)` with `fibZeros p = val`. -/
noncomputable def densityMod40 (r₁ r₂ val x : ℕ) : ℝ :=
  (((primesMod40 r₁ r₂ x).filter (fun p => fibZeros p = val)).card : ℝ) /
    ((primesMod40 r₁ r₂ x).card : ℝ)

theorem main :
    Filter.Tendsto (densityMod40 1 9 1) Filter.atTop (nhds (1 / 6)) ∧
    Filter.Tendsto (densityMod40 1 9 2) Filter.atTop (nhds (2 / 3)) ∧
    Filter.Tendsto (densityMod40 1 9 4) Filter.atTop (nhds (1 / 6)) ∧
    Filter.Tendsto (densityMod40 21 29 1) Filter.atTop (nhds (1 / 2)) ∧
    Filter.Tendsto (densityMod40 21 29 4) Filter.atTop (nhds (1 / 2)) := by
  sorry

end OMA.S_oeis_a001176
