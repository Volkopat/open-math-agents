import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a378575

/-- Coefficient of `x^n` in `g(x)^k` for a formal power series `g` with `g(0) = 0`. -/
def powSeq {R : Type*} [CommRing R] (g : ℕ → R) : ℕ → ℕ → R
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ i ∈ Finset.range (n + 1), g i * powSeq g k (n - i)

/-- Coefficient of `x^n` in the formal power series composition `f(g(x))` (when `g(0) = 0`). -/
def comp {R : Type*} [CommRing R] (f g : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), f k * powSeq g k n

/-- `r`-fold formal composition `f^[r](x)` of a series `f` with `f(0) = 0`. -/
def iterComp {R : Type*} [CommRing R] (f : ℕ → R) : ℕ → ℕ → R
  | 0, n => if n = 1 then 1 else 0
  | r + 1, n => comp f (iterComp f r) n

/-- OEIS A378575: G.f. `A(x)` satisfies `A(x) = x + x * A(A(A(A(A(x)))))` (with `A(0) = 0`).
Conjecture: `a(n) ≡ 1 (mod 4)` for all `n ≥ 1`. -/
theorem main :
    ∀ a : ℕ → ℤ, a 0 = 0 →
      (∀ n : ℕ, a (n + 1) = (if n = 0 then 1 else 0) + iterComp a 5 n) →
      ∀ n : ℕ, 1 ≤ n → a n ≡ 1 [ZMOD 4] := by
  sorry

end OMA.S_oeis_a378575
