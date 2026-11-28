import OMAStatements.S_mo_181683
import Mathlib

/-! For a nonunit difference d, the original quartic divisibility yields
r² ∣ u(u+1) with u = (d²-1)/2. Both factors are positive and smaller than r².
Consequently each shares a prime with r, and consecutiveness separates those
primes. This excludes all prime powers r. The remaining size inequality for
solutions with these two prime witnesses is open. -/

namespace OMA.R_mo_181683_R1

def H1 : Prop := ∀ r s : ℕ, 1 ≤ s → s < r → r - s ≠ 1 →
    (4 * (r : ℤ) ^ 2 * s ∣ ((r : ℤ) - s) ^ 4 - 1) →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ r ∧ q ∣ r ∧
      p ∣ ((r - s) ^ 2 / 2) ∧ q ∣ ((r - s) ^ 2 / 2 + 1)

def H2 : Prop := ∀ r s p q : ℕ, 1 ≤ s → s < r → Nat.Coprime r s →
    (4 * (r : ℤ) ^ 2 * s ∣ ((r : ℤ) - s) ^ 4 - 1) →
    p.Prime → q.Prime → p ≠ q → p ∣ r → q ∣ r →
    p ∣ ((r - s) ^ 2 / 2) → q ∣ ((r - s) ^ 2 / 2 + 1) → 3 * s < 2 * r

theorem main : H1 → H2 → type_of% @OMA.S_mo_181683.main := by
  intro h1 h2 r s hs hsr hc hd
  by_cases he : r - s = 1
  · exact Or.inl he
  · obtain ⟨p, q, hp, hq, hn, hrp, hrq, hu, hv⟩ := h1 r s hs hsr he hd
    exact Or.inr (h2 r s p q hs hsr hc hd hp hq hn hrp hrq hu hv)

end OMA.R_mo_181683_R1
