import FormalConjectures.OEIS.«239957»

/-!
Sun's conjecture that every prime has a primitive root of the form k^2 + 1.
Classical slice: for a safe prime p = 2q + 1 with q an odd prime, every
quadratic non-residue other than -1 is a primitive root (its order divides
2q and is not 1, 2 or q by Euler's criterion). Hence 2 = 1^2 + 1 works when
p = 3 mod 8 (second supplement), and 5 = 2^2 + 1 works when p = 2 or 3 mod 5
(quadratic reciprocity with 5). H1 is this infinite family; H2 is every
other prime, where the conjecture is still open.
-/

namespace OMA.R_OeisA239957_conjecture_R1

def H1 : Prop := ∀ q : ℕ, q.Prime → 2 < q → (2 * q + 1).Prime →
    ((2 * q + 1) % 8 = 3 ∨ (2 * q + 1) % 5 = 2 ∨ (2 * q + 1) % 5 = 3) →
    OeisA239957.A (2 * q + 1)

def H2 : Prop := ∀ p : ℕ, p.Prime →
    (∀ q : ℕ, q.Prime → 2 < q → p = 2 * q + 1 → ¬ (p % 8 = 3 ∨ p % 5 = 2 ∨ p % 5 = 3)) →
    OeisA239957.A p

theorem main : H1 → H2 → type_of% @OeisA239957.conjecture := by
  intro h₁ h₂ p hp
  by_cases h : ∃ q : ℕ, q.Prime ∧ 2 < q ∧ p = 2 * q + 1 ∧
      (p % 8 = 3 ∨ p % 5 = 2 ∨ p % 5 = 3)
  · obtain ⟨q, hq, hq2, rfl, hc⟩ := h
    exact h₁ q hq hq2 hp hc
  · exact h₂ p hp (fun q hq hq2 he hc => h ⟨q, hq, hq2, he, hc⟩)

end OMA.R_OeisA239957_conjecture_R1
