import OMAStatements.S_oeis_a000978
import Mathlib

/-! The Vrba–Reix test recorded at OEIS A000978 is an equivalence. Its forward direction is
classical: for a prime `p > 3` with `W = (2^p + 1)/3` prime, `W ≡ 3 (mod 8)` and
`W ≡ 1, 4 (mod 7)`, so `-2` is a square mod `W` and, by quadratic reciprocity, `7` and `2` are
non-squares, hence `14` is a square. Their roots give `β` with `β² + β⁻² = 3/2` in `ZMod W`;
then `S i = β^(2^(i+1)) + β^(-2^(i+1))`, and `2^p = 3W - 1` with Fermat's little theorem gives
`S (p - 1) = β² + β⁻² = S 0`. The open rest is the backward direction (the congruence forces
`W` to be prime) and Ordowski's conjecture on least prime factors. -/

namespace OMA.R_oeis_a000978_R1

open OMA.S_oeis_a000978

/-- The forward direction of the Vrba–Reix test: Wagstaff primes pass it. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 3 < p → (W p).Prime → S (W p) (p - 1) = S (W p) 0

/-- The open rest: the backward direction of the test, and Ordowski's conjecture. -/
def H2 : Prop :=
  (∀ p : ℕ, p.Prime → 3 < p → S (W p) (p - 1) = S (W p) 0 → (W p).Prime) ∧
    (a 1 = 3 ∧ ∀ n : ℕ, 0 < n →
      IsLeast {k : ℕ | 3 ≤ k ∧ Odd k ∧ (W (a n)).minFac < (W k).minFac} (a (n + 1)))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000978.main := by
  intro h1 h2
  exact ⟨fun p hp h3 => ⟨h1 p hp h3, h2.1 p hp h3⟩, h2.2⟩

end OMA.R_oeis_a000978_R1
