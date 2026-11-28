import Mathlib

/-!
# A377110: coefficient of sqrt(2) in (2 + sqrt(2) + sqrt(3))^n

Source: https://oeis.org/A377110
Credit: @xor2k
Sibling of OEIS A377109 (same conjecture wording); statement modelled on the accepted one for that entry.

OEIS conjecture (offset 0): every prime divides a(n) for infinitely many n, and if
K(p) = (k(1), k(2), ...) is the maximal subsequence of indices n such that p divides a(n), then
the difference sequence of K(p) is eventually periodic; indeed, K(p) is purely periodic for the
first 7 primes, with respective period lengths 1, 8, 18, 17, 3, 11, 50 and these periods:
p = 2: (4); p = 3: (4,2,6,6,1,1,3,1); p = 5: (12,2,10,7,3,2,3,9,12,1,8,2,1,12,12,5,7,12);
p = 7: (5,16,26,22,13,2,1,24,16,57,2,30,9,19,6,28,12); p = 11: (29,70,61);
p = 13: (21,3,24,15,9,24,9,15,24,3,21); p = 17: a block of length 50 (transcribed below).

Conventions:
* The ordered basis is 1, sqrt 2, sqrt 3, sqrt 6; multiplication by 2 + sqrt 2 + sqrt 3 in this
  basis gives the four-coordinate recurrence, starting from the power 1 at n = 0. `a n` is the
  second coordinate (the coefficient of sqrt 2); the indices start at 0 as in the entry.
* K(p) is an increasing enumeration `k` of all hit indices (including n = 0, where a(0) = 0),
  so infinitude of hits is encoded by `k` being defined on all of ℕ. The gap sequence uses
  consecutive hits.
* For each displayed block `w` the statement asserts: the gaps run through `w` cyclically from
  some starting position (the phase), `w.length` is a period of the gaps from the start, and no
  smaller positive period exists. The blocks and their lengths are transcribed as printed.
-/

namespace OMA.S_oeis_a377110

/-- Coordinates of `(2 + √2 + √3)^n` in the basis `1, √2, √3, √6`. -/
def coords : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 0, 0, 0)
  | n+1 =>
    let (a, b, c, d) := coords n
    (2*a + 2*b + 3*c, a + 2*b + 3*d, a + 2*c + 2*d, b + c + 2*d)

/-- A377110: the coefficient of `√2`. -/
def a (n : ℕ) : ℕ := (coords n).2.1

/-- The seven displayed periods, keyed by the prime. -/
def displayed : List (ℕ × List ℕ) := [
  (2, [4]),
  (3, [4, 2, 6, 6, 1, 1, 3, 1]),
  (5, [12, 2, 10, 7, 3, 2, 3, 9, 12, 1, 8, 2, 1, 12, 12, 5, 7, 12]),
  (7, [5, 16, 26, 22, 13, 2, 1, 24, 16, 57, 2, 30, 9, 19, 6, 28, 12]),
  (11, [29, 70, 61]),
  (13, [21, 3, 24, 15, 9, 24, 9, 15, 24, 3, 21]),
  (17, [19, 11, 30, 4, 21, 2, 3, 22, 8, 7, 23, 24, 6, 30, 30, 11, 10, 9, 26, 4, 30, 18, 12, 30,
    30, 15, 15, 30, 30, 8, 4, 11, 7, 30, 30, 9, 7, 14, 30, 5, 9, 16, 6, 24, 30, 30, 3, 27, 30, 30])]

def gap (k : ℕ → ℕ) (j : ℕ) : ℕ := k (j+1) - k j

def purePeriod (k : ℕ → ℕ) (d : ℕ) : Prop :=
  0 < d ∧ ∀ j : ℕ, gap k (j+d) = gap k j

/-- The infinitude, eventual-period and seven explicit pure-period claims. -/
theorem main : ∀ p : ℕ, Nat.Prime p → ∃ k : ℕ → ℕ,
    StrictMono k ∧ (∀ n : ℕ, p ∣ a n ↔ ∃ j : ℕ, k j = n) ∧
    (∃ N d : ℕ, 0 < d ∧ ∀ j : ℕ, N ≤ j → gap k (j+d) = gap k j) ∧
    ∀ w : List ℕ, (p, w) ∈ displayed →
      (∃ phase : ℕ, ∀ j : ℕ, gap k j = w.getD ((j+phase) % w.length) 0) ∧
      purePeriod k w.length ∧ (∀ d : ℕ, purePeriod k d → w.length ≤ d) := by
  sorry

end OMA.S_oeis_a377110
