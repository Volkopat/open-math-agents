import Mathlib.Data.Rat.Init

/-!
# OEIS A207872

The conjecture at https://oeis.org/A207872 identifies the reduced denominator
of the Zeckendorf polynomial at 1/2 with the binary value of the reversed
Zeckendorf representation. The list of digits below starts at the units end.
-/

namespace OMA.S_oeis_a207872

/-- Test that two consecutive Fibonacci weights are never selected. -/
def noAdjacent : List Bool → Bool
  | [] => true
  | [_] => true
  | b :: c :: bs => !(b && c) && noAdjacent (c :: bs)

/-- Sum the selected Fibonacci weights, starting from the given pair. -/
def fibValue : List Bool → Nat → Nat → Nat
  | [], _, _ => 0
  | b :: bs, f, g => (if b then f else 0) + fibValue bs g (f + g)

/-- Evaluate the polynomial with these coefficients at the rational 1/2. -/
def atHalf : List Bool → ℚ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + atHalf bs / 2

/-- Read the low-to-high coefficient list as a high-to-low binary numeral. -/
def reversedBinary (bs : List Bool) : Nat :=
  bs.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0

/-- For every positive index, the denominator equals the reversed binary word. -/
theorem main : ∀ n : Nat, 1 ≤ n → ∀ bs : List Bool,
    bs.getLast? = some true → noAdjacent bs = true → fibValue bs 1 2 = n →
    (atHalf bs).den = reversedBinary bs := by
  sorry

end OMA.S_oeis_a207872
