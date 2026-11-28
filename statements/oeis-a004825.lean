import Mathlib

/-!
# A004825: Numbers that are the sum of at most 3 positive cubes

Source: https://oeis.org/A004825
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Deshouillers, Hennecart, and Landreau):
The set of positive integers representable as the sum of at most 3 positive cubes has
asymptotic density equal to 1 minus
  lim_{m -> ∞} (1 / K_m) * Sum_{k=1..K_m} exp(c * rho(k, K_m) / K_m^2),
where c = -Gamma(4/3)^3 / 6, K_m = lcm(1, 2, ..., m) (A003418), and rho(k0, K) is the
number of triples (k1, k2, k3) in {1, ..., K}^3 such that k1^3 + k2^3 + k3^3 ≡ k0 (mod K).
(The OEIS text omits the 1 minus: the limit itself is about 0.9, the density of the
non-representable numbers, while the stated density is 0.0999425.)
-/

namespace OMA.S_oeis_a004825

open Classical Filter

/-- Set of natural numbers expressible as a sum of at most 3 positive cubes. -/
def sumAtMost3PosCubes : Set ℕ :=
  {n : ℕ | ∃ k ≤ 3, ∃ f : Fin k → ℕ, (∀ i, 0 < f i) ∧ ∑ i, (f i) ^ 3 = n}

/-- K(m) = lcm(1, 2, ..., m) = A003418(m). -/
def lcmUpTo (m : ℕ) : ℕ :=
  (Finset.Icc 1 m).lcm id

/-- Number of triples (k1, k2, k3) in {1..M}^3 with k1^3 + k2^3 + k3^3 ≡ k0 (mod M). -/
def rho (k0 M : ℕ) : ℕ :=
  ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
    (fun t => (t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3) % M = k0 % M)).card

/-- The constant c = -Gamma(4/3)^3 / 6. -/
noncomputable def cConst : ℝ :=
  -(Real.Gamma (4 / 3)) ^ 3 / 6

/-- The Deshouillers-Hennecart-Landreau density approximant at m. -/
noncomputable def dhlApprox (m : ℕ) : ℝ :=
  let M := lcmUpTo m
  (∑ k ∈ Finset.Icc 1 M, Real.exp (cConst * (rho k M : ℝ) / ((M : ℝ) ^ 2))) / (M : ℝ)

/-- Conjecture: the density of sums of at most 3 positive cubes is 1 - lim dhlApprox(m); the sum in OEIS is the density of non-representable numbers (it tends to about 0.9), so the representable density 0.0999425 is its complement. -/
theorem main :
    ∃ L : ℝ,
      Tendsto dhlApprox atTop (nhds L) ∧
      Tendsto
        (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => n ∈ sumAtMost3PosCubes)).card : ℝ) / (N : ℝ))
        atTop (nhds (1 - L)) := by
  sorry

end OMA.S_oeis_a004825
