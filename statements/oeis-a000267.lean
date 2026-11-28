import Mathlib

/-!
# OEIS A000267

Source: https://oeis.org/A000267
Credit: @willperacchio

Antti Karttunen's conjecture concerns the binary length (A070939) of the
least code in A227368 for a partition of size `n + 1`. The partition-size
decoder is defined by A227183.
-/

namespace OMA.S_oeis_a000267

/-- Read runs from the low bits upward, then sum the partial sums of the
run lengths after decrementing each run length beyond the first. -/
def partitionWeight (code : ℕ) : ℕ :=
  if code = 0 then 0 else
    let bits := (List.range (code.log2 + 1)).map code.testBit
    match (bits.splitBy (· == ·)).map List.length with
    | [] => 0
    | first :: rest => (rest.scanl (fun part run => part + (run - 1)) first).sum

theorem main : ∀ n : ℕ,
    ∃ code : ℕ, partitionWeight code = n + 1 ∧
      (∀ k < code, partitionWeight k ≠ n + 1) ∧
      code.log2 + 1 = Nat.sqrt (4 * n + 1) := by
  sorry

end OMA.S_oeis_a000267
