import Mathlib

/-!
# A049591: Cloitre's largest-prime-factor sequence

Source: https://oeis.org/A049591
Credit: @jagraj28

A049591 lists the odd primes `p` such that `p + 2` is composite (7, 13, 19, 23, ...). The entry
records conjectures of Benoit Cloitre (2003): start from any initial value `f(1) ≥ 2` and define
`f(n)` to be the largest prime factor of `f(1) + f(2) + ... + f(n-1)`; then
1. `f(n) = n/2 + O(log n)`;
2. there are infinitely many primes `p` such that `f(2p) = p`;
3. the current sequence gives the primes satisfying `f(2p) = p` when `f(1) = 3`.

`main` is the conjunction of the three, stated for every function `f` that satisfies the
recursion (the recursion determines `f(n)` for `n ≥ 1`; `f 0` is not part of the sequence).

Conventions:
* `gpf m` is the largest prime factor of `m` (the sum is at least 2, so it has one).
* Conjecture 1 is `fun n => f(n) - n/2` is `O(log n)` as `n → ∞`, in `ℝ`.
* Conjecture 3 reads: for `f(1) = 3`, a prime `p` satisfies `f(2p) = p` exactly when `p` is odd
  and `p + 2` is not prime (`p + 2 ≥ 5`, so not prime is composite). A computation for
  `f(1) = 3` and `p ≤ 2000` agrees.
-/

namespace OMA.S_oeis_a049591

open Asymptotics Filter

/-- `gpf m`: the largest prime factor of `m` (0 if there is none). -/
def gpf (m : ℕ) : ℕ := m.primeFactors.sup id

/-- `f` follows Cloitre's recursion with initial value `s`. -/
def IsCloitre (s : ℕ) (f : ℕ → ℕ) : Prop :=
  f 1 = s ∧ ∀ n, 2 ≤ n → f n = gpf (∑ i ∈ Finset.Icc 1 (n - 1), f i)

/-- Cloitre's three conjectures in OEIS A049591. -/
theorem main :
    (∀ s : ℕ, 2 ≤ s → ∀ f : ℕ → ℕ, IsCloitre s f →
      (fun n : ℕ => (f n : ℝ) - (n : ℝ) / 2) =O[atTop] (fun n : ℕ => Real.log n)) ∧
    (∀ s : ℕ, 2 ≤ s → ∀ f : ℕ → ℕ, IsCloitre s f →
      {p : ℕ | p.Prime ∧ f (2 * p) = p}.Infinite) ∧
    (∀ f : ℕ → ℕ, IsCloitre 3 f →
      ∀ p : ℕ, p.Prime → (f (2 * p) = p ↔ p ≠ 2 ∧ ¬ (p + 2).Prime)) := by
  sorry

end OMA.S_oeis_a049591
