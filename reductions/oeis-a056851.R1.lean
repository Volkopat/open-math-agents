import OMAStatements.S_oeis_a056851

-- Reduction oeis-a056851.R1 of A056851: Integers n such that the number of digits in n! is a cube.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a056851_R1

/-- Even `n`: `n^3 - n` is never `k!` with `k ≥ 8`. -/
def H1 : Prop :=
  ∀ n k : ℕ, 8 ≤ k → Even n → n ^ 3 - n ≠ k.factorial

/-- Odd `n`: `n^3 - n` is never `k!` with `k ≥ 8`. -/
def H2 : Prop :=
  ∀ n k : ℕ, 8 ≤ k → Odd n → n ^ 3 - n ≠ k.factorial

/-- All solutions with `k ≤ 7`: then `n^3 - n ≤ 7! = 5040`, so `n ≤ 17`, and a finite check
leaves only `n = 2, 3, 5, 9`. -/
theorem small (n k : ℕ) (hk : k ≤ 7) (h : n ^ 3 - n = k.factorial) :
    n ∈ ({2, 3, 5, 9} : Finset ℕ) := by
  have hf : k.factorial ≤ 5040 := (Nat.factorial_le hk).trans (by decide)
  have hn : n ≤ 17 := by
    by_contra hc
    have h18 : 18 * 18 ≤ n * n := Nat.mul_le_mul (by omega : 18 ≤ n) (by omega : 18 ≤ n)
    have : 324 * n ≤ n ^ 3 := by
      calc 324 * n = (18 * 18) * n := by norm_num
        _ ≤ (n * n) * n := Nat.mul_le_mul_right n h18
        _ = n ^ 3 := by ring
    omega
  revert h
  interval_cases n <;> interval_cases k <;> decide

/-- The reverse direction is a direct computation (`3! , 4!, 5!, 6!`) and every solution with
`k ≤ 7` is found by a finite check; the open part, `k ≥ 8`, is split by the parity of `n`. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a056851.main := by
  intro h1 h2 n
  constructor
  · rintro ⟨k, h⟩
    by_cases hk : k ≤ 7
    · exact small n k hk h
    · rcases Nat.even_or_odd n with he | ho
      · exact absurd h (h1 n k (by omega) he)
      · exact absurd h (h2 n k (by omega) ho)
  · intro hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨3, by decide⟩
    · exact ⟨4, by decide⟩
    · exact ⟨5, by decide⟩
    · exact ⟨6, by decide⟩

end OMA.R_oeis_a056851_R1
