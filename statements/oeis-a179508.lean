import Mathlib

/-!
# OEIS A179508 (Sun-Zagier Theorem)

`a(n)` is the unique integer such that
`Sum_{k = 0..p - 1} b(k) / (-n)^k ≡ a(n) (mod p)`
for every prime `p` not dividing `n`, where `b(0), b(1), ...` are the Bell numbers.

Conjectures (Zhi-Wei Sun, Jul 17 2010):
1. For every `n >= 1`, there exists a unique integer `a(n)` such that for every prime `p`
   not dividing `n`, `Sum_{k = 0..p - 1} (b(k) : ZMod p) / (-(n : ZMod p))^k = (a(n) : ZMod p)`.
2. Specific values: `a(1) = 2`, `a(2) = 1`, `a(3) = 2`, `a(4) = -1`, `a(5) = 10`,
   `a(6) = -43`, `a(7) = 266`, `a(8) = -1853`, `a(9) = 14834`, `a(10) = -133495`.
3. Sign alternation: `(-1)^(n - 1) * a(n) > 0` for all `n >= 3`.
-/

namespace OMA.S_oeis_a179508

/-- Bell numbers `b(0) = 1`, `b(n + 1) = Sum_{j = 0..n} C(n, j) * b(n - j)`. -/
def bell : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ j ∈ Finset.range (n + 1), Nat.choose n j * bell (n - j)
termination_by n => n
decreasing_by omega

/-- Congruence property defining `a(n)` in OEIS A179508. -/
def SatisfiesCongruence (n : ℕ) (x : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ n →
    (∑ k ∈ Finset.range p, (bell k : ZMod p) * (-(n : ZMod p))⁻¹ ^ k) = (x : ZMod p)

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃! x : ℤ, SatisfiesCongruence n x) ∧
    (SatisfiesCongruence 1 2 ∧ SatisfiesCongruence 2 1 ∧ SatisfiesCongruence 3 2 ∧
     SatisfiesCongruence 4 (-1) ∧ SatisfiesCongruence 5 10 ∧ SatisfiesCongruence 6 (-43) ∧
     SatisfiesCongruence 7 266 ∧ SatisfiesCongruence 8 (-1853) ∧
     SatisfiesCongruence 9 14834 ∧ SatisfiesCongruence 10 (-133495)) ∧
    (∀ n : ℕ, 3 ≤ n → ∀ x : ℤ, SatisfiesCongruence n x → 0 < (-1 : ℤ) ^ (n - 1) * x) := by
  sorry

end OMA.S_oeis_a179508
