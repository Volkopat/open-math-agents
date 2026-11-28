import Mathlib

/-!
# Can a discrete logarithm be computed in polynomial time?

Source: https://en.wikipedia.org/wiki/Discrete_logarithm
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Open problem (Wikipedia, list of unsolved problems in computer science): can the discrete
logarithm be computed in polynomial time on a classical computer?

Conventions:
* The discrete logarithm problem is taken in its classical form, in the multiplicative group of
  `ZMod p` for a prime `p`: given `p`, a generator `g` and an element `h` (as naturals `< p`, with
  `h` nonzero mod `p`), output some `x` with `g ^ x ≡ h (mod p)`.
* "Polynomial time on a classical computer": a deterministic polynomial-time Turing machine
  (Mathlib's `Turing.TM2ComputableInPolyTime`) on binary encodings. Inputs are the
  concatenation of self-delimiting binary encodings of `p`, `g`, `h`; the output is the binary
  expansion (least significant bit first) of `x`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_wp_can_a_discrete_logarithm_be_computed_in_polynomial_time

/-- Self-delimiting binary encoding of a natural number. -/
def encNat (k : ℕ) : List Bool := (Nat.bits k).flatMap (fun b => [true, b]) ++ [false, false]

/-- The natural number with binary expansion `l` (least significant bit first). -/
def ofBits (l : List Bool) : ℕ := l.foldr (fun b n => 2 * n + b.toNat) 0

theorem main :
    ∃ f : List Bool → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
        (id : List Bool → List Bool) f) ∧
      ∀ p g h : ℕ, p.Prime → g < p → h < p →
        orderOf (g : ZMod p) = p - 1 → (h : ZMod p) ≠ 0 →
          (g : ZMod p) ^ ofBits (f (encNat p ++ encNat g ++ encNat h)) = (h : ZMod p) := by
  sorry

end OMA.S_wp_can_a_discrete_logarithm_be_computed_in_polynomial_time
