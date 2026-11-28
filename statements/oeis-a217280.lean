import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Digits.Defs

/-!
# The residues modulo five of a weighted binomial cube sum

The sum includes both endpoints. The source gives the positions of
residue one as precisely the numbers formed with base-five digits 0
and 2. All other indices have residue zero. At n=0 the digit test is
true and the sum is one, as in the table.

Source: https://oeis.org/A217280
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a217280

def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n+1), n.choose k ^ 3 * 2^k * 3^(n-k)

def allowed (n : ℕ) : Bool :=
  (Nat.digits 5 n).all (fun d => d == 0 || d == 2)

theorem main : ∀ n : ℕ, a n % 5 = if allowed n then 1 else 0 := by
  sorry

end OMA.S_oeis_a217280
