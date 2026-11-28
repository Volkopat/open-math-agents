import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a396794

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

/-- Cauchy product of two formal power series `u` and `v`. -/
def mulSeq {R : Type*} [CommRing R] (u v : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (n + 1), u i * v (n - i)

/-- OEIS A396794: G.f. `A(x) = ∑_{n ≥ 1} a(n) * x^n` (with `a(0) = 0, a(1) = 1`) satisfies
`A(x) * A(A(A(x))) = x^2 + 16 * x^3`.
Conjecture: `a(n) ≡ 0 (mod 4)` for all `n > 1`. -/
theorem main :
    ∀ a : ℕ → ℤ, a 0 = 0 → a 1 = 1 →
      (∀ n : ℕ, mulSeq (iterComp a 1) (iterComp a 3) n =
        (if n = 2 then 1 else 0) + (if n = 3 then 16 else 0)) →
      ∀ n : ℕ, 2 ≤ n → a n ≡ 0 [ZMOD 4] := by
  sorry

end OMA.S_oeis_a396794
