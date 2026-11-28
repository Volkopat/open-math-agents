import Mathlib

/-!
# Ramanujan-type congruences for overpartitions modulo 7, 17, 19 and 23

Xuanling Wei, "New Ramanujan-type congruences for overpartitions modulo 11 and 13",
arXiv:2603.08510, Conjecture 4.1, Conjecture 4.2 and the two conjectural congruences
displayed in Section 4 (Closing remarks).
Source: https://arxiv.org/abs/2603.08510

With p̄(n) the number of overpartitions of n, the paper conjectures, from numerical evidence:
* p̄(2^4 n) ≡ 0 (mod 7) when n ≡ 3 (mod 8) and (n/7) = 1 (Conjecture 4.1);
* p̄(17^2 · 4 n) ≡ 0 (mod 19) when n ≡ 3 (mod 8), (n/17) = -1 and (n/19) = 1 (Conjecture 4.2);
* p̄(17 · 11^2 n) ≡ 0 (mod 17) when n ≡ 3 (mod 8) and (n/11) = -1;
* p̄(23 · 13^2 n) ≡ 0 (mod 23) when n ≡ 5 (mod 8) and (n/13) = 1.
`main` states all four as a conjunction. The Legendre symbols are `jacobiSym` with a prime
denominator. An overpartition is a partition in which the first occurrence of each part size may
be overlined, so p̄(n) sums 2^(number of distinct part sizes) over the partitions of n.

Literature: searches (March–November 2026) found no proof; Ryan, Sirolli, Villegas-Morales and
Zheng (Ramanujan J. 65 (2024)) give other explicit families. A C computation of p̄ modulo
7·17·19·23 up to 3·10^6 confirmed all four congruences in that range (10045, 73, 83, 43 instances).
-/

namespace OMA.S_arxiv_2603_08510

/-- The number of overpartitions of `n`. -/
def overpartitionCount (n : ℕ) : ℕ :=
  ∑ π : Nat.Partition n, 2 ^ π.parts.toFinset.card

theorem main :
    (∀ n : ℕ, n % 8 = 3 → jacobiSym n 7 = 1 → 7 ∣ overpartitionCount (2 ^ 4 * n)) ∧
    (∀ n : ℕ, n % 8 = 3 → jacobiSym n 17 = -1 → jacobiSym n 19 = 1 →
      19 ∣ overpartitionCount (17 ^ 2 * 4 * n)) ∧
    (∀ n : ℕ, n % 8 = 3 → jacobiSym n 11 = -1 →
      17 ∣ overpartitionCount (17 * 11 ^ 2 * n)) ∧
    (∀ n : ℕ, n % 8 = 5 → jacobiSym n 13 = 1 →
      23 ∣ overpartitionCount (23 * 13 ^ 2 * n)) := by
  sorry

end OMA.S_arxiv_2603_08510
