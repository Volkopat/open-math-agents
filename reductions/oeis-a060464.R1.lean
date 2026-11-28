import OMAStatements.S_oeis_a060464

-- Reduction oeis-a060464.R1 of A060464: Numbers that are not congruent to 4 or 5 mod 9.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a060464_R1

/-- Residues `0, 3, 6 (mod 9)`: every such `n` is a sum of three integer cubes. -/
def H1 : Prop :=
  ∀ n : ℕ, n % 3 = 0 → ∃ x y z : ℤ, (n : ℤ) = x ^ 3 + y ^ 3 + z ^ 3

/-- Residues `1, 2, 7, 8 (mod 9)`: every such `n` is a sum of three integer cubes. -/
def H2 : Prop :=
  ∀ n : ℕ, (n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 7 ∨ n % 9 = 8) →
    ∃ x y z : ℤ, (n : ℤ) = x ^ 3 + y ^ 3 + z ^ 3

/-- Cubes are `0, 1, 8 (mod 9)`, so three of them never sum to `4` or `5 (mod 9)`. -/
theorem key : ∀ a b c : ZMod 9, a ^ 3 + b ^ 3 + c ^ 3 ≠ 4 ∧ a ^ 3 + b ^ 3 + c ^ 3 ≠ 5 := by
  decide

/-- The mod 9 obstruction (the `only if` direction) is proved here; the open `if` direction is split
by residue class into `H1` (`3 ∣ n`) and `H2` (`n ≡ ±1, ±2 mod 9`). -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a060464.main := by
  intro h1 h2 n
  constructor
  · rintro ⟨x, y, z, h⟩
    have hn : (n : ZMod 9) = (x : ZMod 9) ^ 3 + (y : ZMod 9) ^ 3 + (z : ZMod 9) ^ 3 := by
      have := congrArg (Int.cast : ℤ → ZMod 9) h
      push_cast at this
      exact this
    constructor <;> intro hm
    · have h4 : ((n % 9 : ℕ) : ZMod 9) = 4 := by rw [hm]; rfl
      rw [ZMod.natCast_mod] at h4
      exact (key _ _ _).1 (hn.symm.trans h4)
    · have h5 : ((n % 9 : ℕ) : ZMod 9) = 5 := by rw [hm]; rfl
      rw [ZMod.natCast_mod] at h5
      exact (key _ _ _).2 (hn.symm.trans h5)
  · rintro ⟨h4, h5⟩
    by_cases h3 : n % 3 = 0
    · exact h1 n h3
    · exact h2 n (by omega)

end OMA.R_oeis_a060464_R1
