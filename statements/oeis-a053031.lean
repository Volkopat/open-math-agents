import Mathlib

namespace OMA.S_oeis_a053031

/-- Existence of a positive Pisano period for Fibonacci numbers modulo any `m ≥ 1`. -/
def IsPisanoPeriod (m p : ℕ) : Prop :=
  0 < p ∧ Nat.fib p % m = 0 ∧ Nat.fib (p + 1) % m = 1 % m

/-- The Pisano period `π(m)` (A001175): the least positive integer `p` such that
`F(p) ≡ 0 (mod m)` and `F(p + 1) ≡ 1 (mod m)`. -/
noncomputable def pisanoPeriod (m : ℕ) : ℕ :=
  sInf { p : ℕ | IsPisanoPeriod m p }

/-- `fibZeros m` (A001176): the number of zeros in one Pisano period of Fibonacci numbers
modulo `m`, i.e., `#{k ∈ [0, π(m)) | m ∣ F(k)}`. -/
noncomputable def fibZeros (m : ℕ) : ℕ :=
  ((Finset.range (pisanoPeriod m)).filter (fun k => Nat.fib k % m = 0)).card

/-- OEIS A053031: Numbers `m ≥ 1` with `1` zero in one Pisano period of Fibonacci numbers mod `m`
(equivalently `π(m) = z(m)`).
Conjecture: `m` is on this list (`fibZeros m = 1`) if and only if either `m` is an odd integer
all of whose prime factors are on this list, or `m = 2 * k` or `m = 4 * k` for such an odd
integer `k`. -/
theorem main :
    ∀ m : ℕ, 1 ≤ m →
      (fibZeros m = 1 ↔
        (Odd m ∧ ∀ p : ℕ, p.Prime → p ∣ m → fibZeros p = 1) ∨
        (∃ k : ℕ, (m = 2 * k ∨ m = 4 * k) ∧ Odd k ∧
          ∀ p : ℕ, p.Prime → p ∣ k → fibZeros p = 1)) := by
  sorry

end OMA.S_oeis_a053031
