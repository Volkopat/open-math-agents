import Mathlib

/-!
# Anti-twin primes

Source: https://mathoverflow.net/questions/509908
Credit: @datdzrgb

Index nonempty primorials by their largest prime factor.
-/

namespace OMA.S_mo_509908

theorem main :
    {q : ℕ | q.Prime ∧ ¬ ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ q = p + primorial r}.Infinite := by
  sorry

end OMA.S_mo_509908
