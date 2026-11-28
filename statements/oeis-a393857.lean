import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a393857

/-- Coefficient of `x^n` in `g(x)^k` for a formal power series `g` with `g(0) = 0`. -/
def powSeq {R : Type*} [CommRing R] (g : ℕ → R) : ℕ → ℕ → R
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ i ∈ Finset.range (n + 1), g i * powSeq g k (n - i)

/-- Coefficient of `x^n` in the formal power series composition `f(g(x))` (when `g(0) = 0`). -/
def comp {R : Type*} [CommRing R] (f g : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), f k * powSeq g k n

/-- Inner series `x - x * A(5*x) / 5 = x - ∑_{k ≥ 1} a(k) * 5^(k - 1) * x^(k + 1)`. -/
def innerSeq (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => -(5 : ℤ) ^ n * a (n + 1)

/-- OEIS A393857: G.f. `A(x) = ∑_{n ≥ 1} a(n) * x^n` satisfies `A(x - x * A(5*x) / 5) = x`.
Conjecture: `a(n) ≡ 1 (mod 6)` for all `n ≥ 1`. -/
theorem main :
    ∀ a : ℕ → ℤ, a 0 = 0 →
      (∀ n : ℕ, comp a (innerSeq a) n = if n = 1 then 1 else 0) →
      ∀ n : ℕ, 1 ≤ n → a n ≡ 1 [ZMOD 6] := by
  sorry

end OMA.S_oeis_a393857
