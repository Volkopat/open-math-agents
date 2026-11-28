import OMAStatements.S_oeis_a084017

-- Reduction oeis-a084017.R1 of OEIS A084017: no term is zero (Murthy and Srikanth, 2003)

/-!
# Split of the A084017 proof by the divisibility of the index by 10

The merged proof `proofs/oeis-a084017.lean` (1 068 065 bytes) exceeded the
512 KiB submission limit. It is split along the natural case distinction
used inside it: every `n != 0` either satisfies `10 | n` or not.

* `H1` : every nonzero `n` with `10` not dividing it admits a qualifying
  palindromic multiple - the Murthy-Srikanth construction; itself reduced
  further in `oeis-a084017.R1.H1.R1` (finite-certificate cases, open cases,
  the `11 | m`/`101 | m` hard family, and the residue dispatcher).
* `H2` : every nonzero `n` with `10 | n` admits a qualifying palindromic
  multiple - the pinned-tens construction `PinnedTen.pinned_A084017_ten`.

`main` is the case split.
-/

namespace OMA.R_oeis_a084017_R1

/-- The `10` does not divide `n` direction: Murthy-Srikanth construction. -/
def H1 : Prop :=
  ∀ n : ℕ, n ≠ 0 → ¬ 10 ∣ n → OMA.S_oeis_a084017.qualifies n

/-- The `10` divides `n` direction: pinned-tens construction. -/
def H2 : Prop :=
  ∀ n : ℕ, n ≠ 0 → 10 ∣ n → OMA.S_oeis_a084017.qualifies n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a084017.main := by
  intro h1 h2 n hn
  by_cases h10 : 10 ∣ n
  · exact h2 n hn h10
  · exact h1 n hn h10

end OMA.R_oeis_a084017_R1
