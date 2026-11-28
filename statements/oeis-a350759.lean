import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a350759

/-- Signed Stirling numbers of the first kind `s(n, k)` satisfying
`∏_{i=0}^{n-1} (x - i) = ∑_{k=0}^n s(n, k) x^k`. -/
def stirling1 : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, k + 1 => stirling1 n k - (n : ℤ) * stirling1 n (k + 1)

/-- EGF coefficients of `F(x) = -1 + (1 + x) * exp(-x)`. -/
def F (n : ℕ) : ℤ :=
  if n = 0 then 0 else (-1 : ℤ) ^ n * (1 - (n : ℤ))

/-- Exponential `[x^n / n!] exp(G(x))` for an e.g.f. `G` with `G 0 = 0`. -/
def egfExp (G : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
    ∑ j : Fin (n + 1), (Nat.choose n j.1 : ℤ) * G (j.1 + 1) * egfExp G (n - j.1)
termination_by n => n

/-- OEIS A345652: `b(n) = [x^n / n!] exp(-1 + (1 + x) * exp(-x))`. -/
def b (n : ℕ) : ℤ :=
  egfExp F n

/-- OEIS A350759: `a(n) = ∑_{k=0}^n (-1)^k * A345652(k) * s(n, k)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * b k * stirling1 n k

/-- Conjecture on OEIS A350759: for every prime `p`,
`a(p) + a(p + 1) - 2 ≡ 0 (mod p)`. -/
theorem main :
    ∀ p : ℕ, p.Prime → a p + a (p + 1) - 2 ≡ 0 [ZMOD (p : ℤ)] := by
  sorry

end OMA.S_oeis_a350759
