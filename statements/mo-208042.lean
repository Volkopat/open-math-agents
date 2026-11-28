import Mathlib

/-!
# MathOverflow 208042: infinitely many cubes that are not a sum of three positive cubes?

Source: https://mathoverflow.net/questions/208042 (CC BY-SA 3.0).

Most cubes `N³` are sums of three positive cubes (OEIS A023042 lists those `N`), but e.g.
`a³ + b³ + c³ = 999959³` has no solution in positive integers. Question: are there infinitely
many `N³` (especially for prime `N`) that cannot be expressed as a sum of three positive cubes?
We state the main question, without the parenthetical restriction to primes; `main` asserts
that there are infinitely many such `N` (a disproof shows there are only finitely many).
-/

namespace OMA.S_mo_208042

theorem main : {N : ℕ | ¬ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 3 + b ^ 3 + c ^ 3 = N ^ 3}.Infinite := by
  sorry

end OMA.S_mo_208042
