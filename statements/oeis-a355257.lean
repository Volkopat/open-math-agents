import Mathlib

/-!
# OEIS A355257

Array `A(n, k) = k! * [x^k] log((1 - x) / (1 - 2*x)) / (1 - x)^n`
`= Sum_{j=1..k} (k! / j) * (2^j - 1) * C(n + k - j - 1, k - j)`.

Conjectures (Mélika Tebni, Jul 04 2022):
1. For `p` prime and `n >= 0`, `A(n, p) ≡ p - 1 [MOD p]` (i.e. `≡ -1 (mod p)`).
2. For `n >= 0`, `k >= 1`, `k ≠ 4`, `k ∣ A(n, k) ↔ ¬ k.Prime`.
3. For every `k >= 0`, the unique Lagrange interpolating polynomial of degree `<= k`
   through `(n, A(n, k + 1))` for `n = 0..k` (OEIS A355259) generates column `k + 1`,
   i.e., evaluates to `A(n, k + 1)` for all `n >= 0`.
4. For `p` prime and `n` even, `(p - 1) ∣ A(n, p)` and `A(n, p) / (p - 1) ≡ 1 [MOD p]`.
-/

namespace OMA.S_oeis_a355257

/-- `A(n, k) = Sum_{j=1..k} (k! / j) * (2^j - 1) * C(n + k - j - 1, k - j)`. -/
def A (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 k, (k.factorial / j) * (2 ^ j - 1) * Nat.choose (n + k - j - 1) (k - j)

theorem main :
    (∀ p n : ℕ, p.Prime → A n p ≡ p - 1 [MOD p]) ∧
    (∀ n k : ℕ, 1 ≤ k → k ≠ 4 → (k ∣ A n k ↔ ¬ k.Prime)) ∧
    (∀ k : ℕ, ∀ n : ℕ,
      (Lagrange.interpolate (Finset.range (k + 1)) (Nat.cast (R := ℚ))
        (fun m => (A m (k + 1) : ℚ))).eval (n : ℚ) = (A n (k + 1) : ℚ)) ∧
    (∀ p n : ℕ, p.Prime → Even n → (p - 1) ∣ A n p ∧ A n p / (p - 1) ≡ 1 [MOD p]) := by
  sorry

end OMA.S_oeis_a355257
