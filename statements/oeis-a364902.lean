import Mathlib

/-!
# A364902: a greedy sequence driven by the greatest powers of 2 and 3 not exceeding n

Source: https://oeis.org/A364902
Credit: @avivorly

A364902 (offset 1): Let x, y  be the greatest exponents of 2, 3 respectively such that 2^x, 3^y do not exceed n
and let k_2, k_3 be n - 2^x, and n - 3^y respectively. Then for n such that k_2 = 0 or k_3 = 0, a(n) = n, else
a(n) is the least novel number Min{p*a(k_2), q*a(k_3)}, where p, q are primes not equal to either 2 or 3.

Claim in the entry: Conjectures: (i). This is a permutation of A047253 with primes in order; (ii). All terms
between consecutive prime terms, prime(k), prime(k+1) are prime(k)-smooth.
Only conjecture (i) is stated here; conjecture (ii) is not part of this statement.

Conventions:
- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms, and `a n` is its last entry. So `a 0 = 0` is
  a junk value outside the offset; only `n ≥ 1` is used.
- For the index `N = n + 1 ≥ 1`, `Nat.log 2 N` is the greatest `x` with `2^x ≤ N` and `Nat.log 3 N` is the
  greatest `y` with `3^y ≤ N`; so `k2 N = N - 2^x` and `k3 N = N - 3^y`. Thus `k2 N = 0` exactly when `N` is a
  power of 2, and `k3 N = 0` exactly when `N` is a power of 3; then `a(N) = N`.
- Otherwise both `k2 N` and `k3 N` lie in `[1, N - 1]`, and `a(k)` for such `k` is read from the list of earlier
  terms as `(pre n).getD (k - 1) 0`.
- The least novel number Min{p*a(k_2), q*a(k_3)}, where p, q are primes not equal to either 2 or 3, is read as:
  the least number not yet in the sequence (`v ∉ pre n`) that is of the form `p * a(k_2)` or `q * a(k_3)` for
  some prime other than 2 and 3, that is, a prime `≥ 5`. This is the same as the minimum of the least novel
  `p * a(k_2)` and the least novel `q * a(k_3)`. It is written as `sInf` of that set of naturals. The set is
  nonempty (take `p` a prime larger than every earlier term; all terms are positive), so `sInf` is its least
  element. This reading reproduces the 68 data terms of the entry, for example a(17) = 11 from
  17 = 16 + 1 = 9 + 8, where Min{p*a(1), q*a(8)} = Min{p, 8*q} over unused values is 11.
- A047253 is the sequence of the positive integers not divisible by 6. A permutation of A047253 (offset 1)
  means: every `a n` with `n ≥ 1` is `≥ 1` and not divisible by 6, `a` is injective on the indices `n ≥ 1`, and
  every `m ≥ 1` not divisible by 6 equals `a n` for some `n ≥ 1`.
- Primes in order: whenever `1 ≤ i < j` and `a i` and `a j` are both prime, `a i < a j`.
-/

namespace OMA.S_oeis_a364902

/-- `k2 N = N - 2^x`, where `2^x` is the greatest power of 2 not exceeding `N`. -/
def k2 (N : ℕ) : ℕ := N - 2 ^ Nat.log 2 N

/-- `k3 N = N - 3^y`, where `3^y` is the greatest power of 3 not exceeding `N`. -/
def k3 (N : ℕ) : ℕ := N - 3 ^ Nat.log 3 N

/-- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms; the next term is the one for the index
`n + 1`. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | n + 1 => pre n ++
      [if k2 (n + 1) = 0 ∨ k3 (n + 1) = 0 then n + 1
       else sInf {v : ℕ | v ∉ pre n ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
         (v = p * (pre n).getD (k2 (n + 1) - 1) 0 ∨ v = p * (pre n).getD (k3 (n + 1) - 1) 0)}]

/-- `a n` is the `n`-th term (offset 1): the last entry of `pre n`. -/
noncomputable def a (n : ℕ) : ℕ := (pre n).getLastD 0

theorem main :
    (∀ n : ℕ, 1 ≤ n → 1 ≤ a n ∧ ¬ 6 ∣ a n) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → a i = a j → i = j) ∧
    (∀ m : ℕ, 1 ≤ m → ¬ 6 ∣ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m) ∧
    (∀ i j : ℕ, 1 ≤ i → i < j → (a i).Prime → (a j).Prime → a i < a j) := by
  sorry

end OMA.S_oeis_a364902
