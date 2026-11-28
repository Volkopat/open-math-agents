import Mathlib

namespace OMA.S_mo_131233

/-- A family of permutations of the nonzero residues whose pairwise
differences are also permutations is obtained by relabeling the rows and
columns of the multiplication table. -/
theorem main :
    ∀ (p : ℕ) [Fact p.Prime]
      (a : (ZMod p)ˣ → Equiv.Perm ((ZMod p)ˣ)),
      (∀ i j, i ≠ j →
        ∃ d : Equiv.Perm ((ZMod p)ˣ), ∀ k : (ZMod p)ˣ,
          (d k : ZMod p) = (a i k : ZMod p) - (a j k : ZMod p)) →
      ∃ b c : Equiv.Perm ((ZMod p)ˣ), ∀ i k, a i k = c i * b k := by
  sorry

end OMA.S_mo_131233
