import Mathlib

/-!
# A prime q < p whose inverse modulo p is an integer square

Source: https://mathoverflow.net/questions/332255 (Zhi-Wei Sun, CC BY-SA 4.0).

For a prime `p` and `k ∈ {1, …, p-1}` let `k̄ ∈ {1, …, p-1}` be the inverse of `k` modulo `p`.
Conjecture (Sun, 2014): for any prime `p > 5` there is a prime `q < p` such that `q̄` is an
integer square. Saying `q̄ = m²` amounts to `m² < p` and `q · m² ≡ 1 (mod p)` (then `m² ≥ 1`).
-/

namespace OMA.S_mo_332255

theorem main : ∀ p : ℕ, p.Prime → 5 < p →
    ∃ q m : ℕ, q.Prime ∧ q < p ∧ m ^ 2 < p ∧ q * m ^ 2 ≡ 1 [MOD p] := by
  sorry

end OMA.S_mo_332255
