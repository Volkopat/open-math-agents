import Mathlib

/-!
# A218483: Fermat pseudoprimes to base 2 which are congruent to 1 (mod 8).

Source: https://oeis.org/A218483
Credit: @luciusacarr

Data: 561, 1105, 1729, 1905, 2465, 4033, 4369, 4681, 6601, 8321, 8481, 10585, ...
(Old name: Fermat pseudoprimes to base 2 of the form 8*p*n + p^2, where p is prime and n natural.)

The entry's comments record four conjectures (all about Fermat pseudoprimes to base 2 in general,
not only the terms of this sequence); `main` states their conjunction:
1. There are no pseudoprimes to base 2 of the form 40*n + 15.
2. If a Fermat pseudoprime to base 2 can be written as 8*p*n + p^2, where n is an integer and p one
   of its prime factors, then it can be written this way for any of its prime factors.
3. If a Fermat pseudoprime to base 2 with two prime factors can be written as 8*p1*n + p1^2, where
   n is a natural number and p1 one of its two prime factors, then it can also be written as
   8*p2*(-n) + p2^2, where p2 is the other prime factor.
4. If a Fermat pseudoprime to base 2 cannot be written as 8*p*n + p^2, where n is an integer and p
   one of its prime factors, then it cannot be written this way for any of its prime factors.
(The entry adds: "All three conjectures are true (obvious from new characterization)." - C. R.
Greathouse IV.)

Reading of the source:
* A Fermat pseudoprime to base 2 (A001567) is a composite `N > 1` with `2^(N-1) ≡ 1 (mod N)`;
  this is Mathlib's `Nat.FermatPsp N 2` (`N ∣ 2^(N-1) - 1`, `N` not prime, `1 < N`).
* "Of the form 40*n + 15" means `N % 40 = 15`.
* "Can be written as 8*p*n + p^2 with n an integer" is `∃ n : ℤ, N = 8*p*n + p^2` in `ℤ`.
* "With two prime factors" is read as `N = p1 * p2` with `p1`, `p2` prime (counted with
  multiplicity, so `p1 = p2` is not excluded; this only makes the statement stronger); then
  `p2` is "the other prime factor".
* In 4, "cannot be written ... for p one of its prime factors" is read as: for some prime factor
  `p` there is no such integer `n`; the conclusion is that for every prime factor `q` there is none.
-/

namespace OMA.S_oeis_a218483

/-- `N` can be written as `8*p*n + p^2` for some integer `n`. -/
def Writable (N p : ℕ) : Prop :=
  ∃ n : ℤ, (N : ℤ) = 8 * p * n + (p : ℤ) ^ 2

theorem main :
    -- 1. no Fermat pseudoprime to base 2 is ≡ 15 (mod 40)
    (∀ N : ℕ, Nat.FermatPsp N 2 → N % 40 ≠ 15) ∧
    -- 2. writable for one prime factor ⇒ writable for every prime factor
    (∀ N : ℕ, Nat.FermatPsp N 2 → ∀ p : ℕ, p.Prime → p ∣ N → Writable N p →
      ∀ q : ℕ, q.Prime → q ∣ N → Writable N q) ∧
    -- 3. two prime factors: N = 8*p1*n + p1^2 with n natural ⇒ N = 8*p2*(-n) + p2^2
    (∀ N : ℕ, Nat.FermatPsp N 2 → ∀ p1 p2 : ℕ, p1.Prime → p2.Prime → N = p1 * p2 →
      ∀ n : ℕ, N = 8 * p1 * n + p1 ^ 2 →
        (N : ℤ) = 8 * p2 * (-(n : ℤ)) + (p2 : ℤ) ^ 2) ∧
    -- 4. not writable for one prime factor ⇒ not writable for any prime factor
    (∀ N : ℕ, Nat.FermatPsp N 2 → ∀ p : ℕ, p.Prime → p ∣ N → ¬ Writable N p →
      ∀ q : ℕ, q.Prime → q ∣ N → ¬ Writable N q) := by
  sorry

end OMA.S_oeis_a218483
