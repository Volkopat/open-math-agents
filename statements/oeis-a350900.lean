import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Nat

/-!
# Gcd ratio sums and Dirichlet convolution (OEIS A350900)

Source: https://oeis.org/A350900 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

For each arithmetic function f, the source conjectures that the sum of f
of the gcd ratio over all pairs of indices in {1, ..., n} equals the
Dirichlet convolution of f times Euler's totient and A057660. It also
states that the resulting function is multiplicative when f is. The
source A057660 gives its value as the divisor sum of d times phi(d).
The ordinary row sums use f(d) = d and the factor phi(d^2),
which is A002618.
-/

namespace OMA.S_oeis_a350900

def weightedRowSum (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
    f (Nat.gcd i n / Nat.gcd (Nat.gcd i k) n)

def orderSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d * d.totient

def IsMultiplicative (f : ℕ → ℂ) : Prop :=
  f 1 = 1 ∧ ∀ a b : ℕ, a.Coprime b → f (a * b) = f a * f b

theorem main :
    (∀ (f : ℕ → ℂ) (n : ℕ), 0 < n →
      weightedRowSum f n = ∑ d ∈ n.divisors, f d * (d.totient : ℂ) * (orderSum (n / d) : ℂ)) ∧
    (∀ f : ℕ → ℂ, IsMultiplicative f → IsMultiplicative (weightedRowSum f)) ∧
    (∀ n : ℕ, 0 < n → weightedRowSum (fun d => (d : ℂ)) n =
      ∑ d ∈ n.divisors, ((d ^ 2).totient : ℂ) * (orderSum (n / d) : ℂ)) := by
  sorry

end OMA.S_oeis_a350900
