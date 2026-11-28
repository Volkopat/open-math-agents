import Mathlib

/-!
# Unique partitions into parts of prescribed binary weight

Mikhail Kurkov's conjecture of October 3, 2022 in OEIS A091892.
Binary digits are stored least significant first. The criterion applies
once the binary expansion of k+1 has a second digit. The entry also
lists zero, whose unique partition is empty.
-/
namespace OMA.S_oeis_a091892

def weight (n : ℕ) := ((2 : ℕ).digits n).count 1

def member (k : ℕ) : Prop :=
  ∃! p : Nat.Partition k, ∀ j ∈ p.parts, weight j = weight k

def threshold (k : ℕ) : Prop :=
  let digits := (2 : ℕ).digits (k+1)
  let trailing := (digits.takeWhile (· == 0)).length
  let f := digits.count 0 - trailing
  if digits.reverse[1]? = some 0 then
    2*trailing ≥ 2^f + 2*f
  else
    trailing ≥ 2^f

theorem main : member 0 ∧ ∀ k : ℕ, 1 ≤ k → (member k ↔ threshold k) := by
  sorry

end OMA.S_oeis_a091892
