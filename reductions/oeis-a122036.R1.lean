import OMAStatements.S_oeis_a122036
import Mathlib

/-! No odd weird numbers, reduced to primitive odd abundant numbers with three prime factors.

Two classical facts carry the reduction. `H1`: an odd number with at most two distinct prime
factors is deficient, because `σ(n) / n < ∏ p / (p - 1) ≤ (3 / 2) (5 / 4) < 2` over its prime
factors (so odd abundant numbers have at least three distinct prime factors). `H2`: a multiple of
a semiperfect number is semiperfect (scale the subset of divisors). With them, strong induction
moves any odd abundant number that has a perfect or abundant proper divisor down to that divisor.
These are classical partial results, not progress on the conjecture.

`H3` is the open rest: every odd abundant number whose proper divisors are all deficient (a
primitive abundant number), necessarily with at least three distinct prime factors, is
semiperfect.
-/

namespace OMA.R_oeis_a122036_R1

/-- Odd numbers with at most two distinct prime factors are deficient. -/
def H1 : Prop := ∀ n : ℕ, Odd n → n.primeFactors.card ≤ 2 → ∑ d ∈ n.properDivisors, d < n

/-- Multiples of semiperfect numbers are semiperfect. -/
def H2 : Prop := ∀ d k : ℕ, 0 < k → (∃ s ⊆ d.properDivisors, ∑ x ∈ s, x = d) →
  ∃ s ⊆ (d * k).properDivisors, ∑ x ∈ s, x = d * k

/-- The open rest: primitive odd abundant numbers (with at least three prime factors) are
semiperfect. -/
def H3 : Prop := ∀ n : ℕ, Odd n → n < ∑ d ∈ n.properDivisors, d → 3 ≤ n.primeFactors.card →
  (∀ d ∈ n.properDivisors, ∑ e ∈ d.properDivisors, e < d) →
  ∃ s ⊆ n.properDivisors, ∑ d ∈ s, d = n

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a122036.main := by
  intro h1 h2 h3 n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hodd hab
    have hn : n ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
    by_cases hex : ∃ d ∈ n.properDivisors, d ≤ ∑ e ∈ d.properDivisors, e
    · obtain ⟨d, hd, hle⟩ := hex
      obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
      have hd0 : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hdvd)
      have hsd : ∃ s ⊆ d.properDivisors, ∑ x ∈ s, x = d := by
        rcases Nat.lt_or_eq_of_le hle with h | h
        · exact ih d hlt (Odd.of_dvd_nat hodd hdvd) h
        · exact ⟨d.properDivisors, subset_rfl, h.symm⟩
      have hk : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd)
        (Nat.pos_of_ne_zero hd0)
      have := h2 d (n / d) hk hsd
      rwa [Nat.mul_div_cancel' hdvd] at this
    · push Not at hex
      have hc : 3 ≤ n.primeFactors.card := by
        by_contra hc
        have := h1 n hodd (by omega)
        omega
      exact h3 n hodd hab hc hex

end OMA.R_oeis_a122036_R1
