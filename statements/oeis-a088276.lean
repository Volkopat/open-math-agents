import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.CompleteLattice.Basic

/-!
# Primes consisting of a power of ten plus an allowed suffix

Quantifying over all positive odd r not divisible by five is equivalent
to running through the source sequence's suffixes. The remainder condition
uses the full decimal length of r. The least qualifying k is zero by
convention when the set is empty.

Source: https://oeis.org/A088276
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a088276

def allowed (r : ℕ) : Prop := 0 < r ∧ Odd r ∧ ¬ 5 ∣ r

def eligible (r k : ℕ) : Prop :=
  Nat.Prime (10^k+r) ∧ (10^k+r) % (10^(Nat.digits 10 r).length) = r

noncomputable def entry (r : ℕ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, eligible r k then Nat.find h else 0

theorem main :
    (∀ r : ℕ, allowed r → entry r = 0 → r % 3 = 2) ∧
    (∀ r : ℕ, allowed r → r % 3 ≠ 2 → Set.Infinite {k : ℕ | Nat.Prime (10^k+r)}) := by
  sorry

end OMA.S_oeis_a088276
