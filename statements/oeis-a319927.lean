import Mathlib

/-!
# A319927. Power sums over nonunitary divisors

Source: https://oeis.org/A319927
Credit: @etaubman
Peter Munn listed 9216 as a sequence member. The TrureTuring project used
the same member to refute the conjecture at exponent 1:
https://www.trureturing.org/research/oeis-a319927-odd-nonunitary-power-sum-refutation/

The source's displayed sequence only uses members with odd nonunitary
divisors. The nonzero sum condition makes that convention explicit.
-/

namespace OMA.S_oeis_a319927

def divisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.gcd d (n / d) ≠ 1)

def sums (n p : ℕ) : ℕ × ℕ :=
  ((divisors n).sum (fun d => if d % 2 = 1 then d^p else 0),
   (divisors n).sum (fun d => d^p))

def member (n : ℕ) : Prop :=
  0 < n ∧ 0 < (sums n 2).1 ∧ (sums n 2).1 ∣ (sums n 2).2

def conjecture : Prop :=
  ∀ n : ℕ, member n → ∀ p : ℕ, (sums n p).1 ∣ (sums n p).2

theorem main : conjecture := by
  sorry

end OMA.S_oeis_a319927
