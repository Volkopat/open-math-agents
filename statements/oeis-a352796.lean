import Mathlib

/-!
# Bipronics and consecutive divisor-pair sums

A352796 consists of the positive integers m for which the set of sums
d + m/d over the positive divisors d has no two consecutive members.
A072389 is defined independently as the products of two pronics,
x(x+1)y(y+1), for nonnegative x and y. The complement is taken among
the nonnegative integers; zero is a bipronic.

Yifan Xie recorded the description of bipronics by two factorizations
with neighboring sums in A072389 in June 2024.
Sources: https://oeis.org/A352796 and https://oeis.org/A072389
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a352796

def sums (m : ℕ) : Finset ℕ := m.divisors.image fun d => d + m/d

def adjacent (m : ℕ) : Prop := ∃ s, s ∈ sums m ∧ s+1 ∈ sums m

def bipronic (m : ℕ) : Prop := ∃ x y : ℕ, m = x*(x+1)*y*(y+1)

theorem main : ∀ m : ℕ, (0 < m ∧ ¬ adjacent m) ↔ ¬ bipronic m := by
  sorry

end OMA.S_oeis_a352796
