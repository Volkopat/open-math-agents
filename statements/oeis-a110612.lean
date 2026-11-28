import Mathlib

/-!
# A110612: the least `k` with `k/P > P^n` is the least `k` with `A346418(k) = n + 1`

Source: https://oeis.org/A110612
Credit: @avivorly

A110612 (offset 1): a(n) is least number k such that k/P > P^n, with n and P (=P(k)) as in A051283.

A051283: Numbers k such that if one writes k = Product p_i^e_i (p_i primes) and P = max p_i^e_i, then k/P > P.

A346418 (offset 1): a(n) is the exponent of the largest power of n that divides the least common multiple of
{1,2,...,n} (A003418). a(1) = 1.

Claim (Amiram Eldar, Jul 16 2021, a comment in A110612): a(n) is the least number k such that A346418(k) = n+1
(conjectured).

Conventions:
- `P k` is the largest prime power exactly dividing `k`: the maximum of `p ^ (k.factorization p)` over the primes
  `p ∣ k`, that is `max p_i^e_i` for `k = Product p_i^e_i` (this is A034699 for `k ≥ 2`). For `k = 1` the empty
  maximum gives the junk value `P 1 = 0` (OEIS takes `P(1) = 1`). Either way `k = 1` meets no condition below when
  `n ≥ 1`: with `P(1) = 1`, `1/1 > 1^n` fails, and with `P 1 = 0`, `1 / 0 = 0 > 0 ^ n` fails.
- `k / P k` is division in `ℕ`; it is exact, since `P k ∣ k` for `k ≥ 1`.
- `A346418 k` for `k ≥ 2` is the supremum of the exponents `m` with `k ^ m ∣ lcm(1, ..., k)`. This set contains `0`
  and is bounded (`k ^ m ≤ lcm(1, ..., k)`, as the lcm is positive), so the supremum is the largest such exponent.
  `A346418 1 = 1` as in the entry. `A346418 0` is junk and never used, since only `k ≥ 1` is considered.
- `A110612 n` is the least number `k ≥ 1` with the condition, taken as `sInf` in `ℕ`; the least `k` with
  `A346418 k = n + 1` is an `sInf` as well. Both sets are also stated to be nonempty, so the identity is not one
  between empty sets (`sInf ∅ = 0` in `ℕ`).
- `n ≥ 1`, the offset of A110612.
-/

namespace OMA.S_oeis_a110612

/-- The largest prime power exactly dividing `k` (the `P` of A051283, A034699 for `k ≥ 2`); junk `P 1 = 0`. -/
noncomputable def P (k : ℕ) : ℕ :=
  k.primeFactors.sup (fun p => p ^ k.factorization p)

/-- `A346418 k`: the exponent of the largest power of `k` dividing `lcm(1, ..., k)`, with `A346418 1 = 1`. -/
noncomputable def A346418 (k : ℕ) : ℕ :=
  if k = 1 then 1 else sSup {m : ℕ | k ^ m ∣ (Finset.Icc 1 k).lcm id}

/-- The defining condition of A110612 at `n`: `k ≥ 1` and `k / P > P ^ n`, with `P = P k`. -/
def A110612Cond (n k : ℕ) : Prop :=
  1 ≤ k ∧ k / P k > P k ^ n

/-- `A110612 n`: the least number `k` such that `k / P > P ^ n`. -/
noncomputable def A110612 (n : ℕ) : ℕ :=
  sInf {k : ℕ | A110612Cond n k}

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (∃ k : ℕ, A110612Cond n k) ∧ (∃ k : ℕ, 1 ≤ k ∧ A346418 k = n + 1) ∧
        A110612 n = sInf {k : ℕ | 1 ≤ k ∧ A346418 k = n + 1} := by
  sorry

end OMA.S_oeis_a110612
