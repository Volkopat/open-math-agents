import Mathlib

/-!
# A000928: Irregular primes: primes p such that at least one of the numerators of the Bernoulli numbers B2, B4, ..., B_{p-3} (A000367) is div

Source: https://oeis.org/A000928
Credit: @mattdorman

The source quotes Ribenboim: it is known that there exist infinitely many irregular primes; in
fact it is a plausible conjecture that only an asymptotic fraction `1/√e ≈ 0.6` of all primes are
regular.

Reading used here: a prime `p` is irregular, as in this sequence's definition, when `p` divides
the numerator of at least one of `B₂, B₄, …, B_{p-3}` (Bernoulli numbers, `bernoulli` in Mathlib;
the even-index values do not depend on the sign convention for `B₁`), and regular otherwise.
"An asymptotic fraction `1/√e` of all primes are regular" is stated as: the number of regular
primes `≤ x` divided by the number of primes `≤ x` tends to `1/√e = exp(-1/2)`.
-/

open Filter Topology

namespace OMA.S_oeis_a000928

/-- `p` is irregular: it divides the numerator of some `B_k` with `k` even, `2 ≤ k ≤ p - 3`. -/
def IsIrregular (p : ℕ) : Prop :=
  ∃ k ∈ Finset.Icc 2 (p - 3), Even k ∧ (p : ℤ) ∣ (bernoulli k).num

open Classical in
/-- The number of regular primes `≤ x`. -/
noncomputable def regularCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun p => p.Prime ∧ ¬ IsIrregular p).card

theorem main :
    Tendsto (fun x : ℕ => (regularCount x : ℝ) / Nat.primeCounting x) atTop
      (𝓝 (Real.exp (-1 / 2))) := by
  sorry

end OMA.S_oeis_a000928
