import Mathlib

/-!
# A322070: permutations f of {1,...,n} with Sum_{k=1..n-1} 1/(f(k)+f(k+1)) = 1

Source: https://oeis.org/A322070
Credit: @rpabani

a(n) is the number of permutations f of {1,...,n} with f(1) < f(n) such that
Sum_{k=1..n-1} 1/(f(k)+f(k+1)) = 1.

Conjecture 1 (Zhi-Wei Sun, in OEIS A322070): a(n) > 0 for all n > 6.

a(n) > 0 says that at least one such permutation exists, which is what is stated. A permutation
of {1,...,n} is a function on the naturals that maps the interval [1, n] bijectively to itself;
its values outside the interval play no role. The sum is taken in the rationals. Conjectures 2
to 4 of the source are separate statements and are not included.
-/

namespace OMA.S_oeis_a322070

theorem main : ∀ n : ℕ, 6 < n →
    ∃ f : ℕ → ℕ, Set.BijOn f (Set.Icc 1 n) (Set.Icc 1 n) ∧ f 1 < f n ∧
      ∑ k ∈ Finset.Icc 1 (n - 1), (1 : ℚ) / ((f k : ℚ) + (f (k + 1) : ℚ)) = 1 := by
  sorry

end OMA.S_oeis_a322070
