import Mathlib

/-! Source: https://mathoverflow.net/questions/104161 -/

namespace OMA.S_mo_104161

/-- Read a binary word at a cyclic offset from a specified index. -/
def cyclicBit {n : ℕ} (u : Fin n → Bool) (i : Fin n) (offset : ℕ) : Bool :=
  u ⟨(i.val + offset) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Count the ones in a contiguous block of a cyclic shift. -/
def cyclicBlockWeight {n : ℕ} (u : Fin n → Bool) (i : Fin n) (start len : ℕ) : ℕ :=
  ((List.range len).filter fun j => cyclicBit u i (start + j)).length

/-- The exponent triples of the monomials in P(u;p,q,r), with multiplicity.
Each index gives one cyclic shift, and equal triples contribute the same monomial. -/
def cyclicBlockCounts {n : ℕ} (u : Fin n → Bool) (p q r : ℕ) : Multiset (ℕ × ℕ × ℕ) :=
  ↑((List.finRange n).map fun i =>
    (cyclicBlockWeight u i 0 p, cyclicBlockWeight u i p q, cyclicBlockWeight u i (p + q) r))

/-- Does the array of triple-block polynomials determine the word up to cyclic shift? -/
theorem main :
    ∀ (n : ℕ) (u v : Fin n → Bool),
      (∀ p q r : ℕ, p + q + r = n →
        cyclicBlockCounts u p q r = cyclicBlockCounts v p q r) →
      ∃ t : ℕ, ∀ i : Fin n, cyclicBit u i t = v i := by
  sorry

end OMA.S_mo_104161
