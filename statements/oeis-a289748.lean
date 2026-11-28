import Mathlib

/-!
# A289748: the Thue-Morse constant converted to base -2

Source: https://oeis.org/A289748
Credit: @avivorly

A289748 (offset 1): Thue-Morse constant converted to base -2.

The entry's comment: Base -2 is also called negabinary. Interpreting the sequence as a binary number with the first
'1' at place 2^0 gives 1.101111101110... which in decimal equals M = 1.745787366973...

Formula (in the entry): M = Thue-Morse + 4/3 (conjectured).

Conventions:
- `tm k` is the Thue-Morse sequence A010060: the parity of the sum of the binary digits of `k` (so `tm 0 = 0`).
- `tau` is the Thue-Morse constant (A014571), `tau = Sum_{k ≥ 0} tm k / 2^(k+1) = 0.4124540336...`; the word
  Thue-Morse in the formula means this constant.
- A base -2 (negabinary) expansion of `tau` with digits 0 and 1 is a digit sequence `d : ℕ → ℕ` with every `d i ≤ 1`
  and `tau = Sum_{i ≥ 0} d i * (-2)^(-i)`, i.e. `HasSum (fun i => d i * (-1/2)^i) tau`. The term `a(i+1)` of the
  sequence is `d i` (offset 1: the first term sits at place `(-2)^0`).
- `M` is the number obtained by reading the same digits in base 2 with the first one at place `2^0`, as in the
  comment: `M = Sum_{i ≥ 0} d i * 2^(-i)`.
- `main` states both that such an expansion of `tau` exists and that EVERY such expansion gives `M = tau + 4/3`.
  So the claim does not depend on whether the expansion is unique (it is in fact unique, but `main` does not assume
  it), and the first half keeps the second half from being vacuous.
-/

namespace OMA.S_oeis_a289748

/-- The Thue-Morse sequence A010060: the parity of the binary digit sum of `k`. -/
def tm (k : ℕ) : ℕ := (Nat.digits 2 k).sum % 2

/-- The Thue-Morse constant `Sum_{k ≥ 0} tm k / 2^(k+1)` (A014571). -/
noncomputable def tau : ℝ := ∑' k : ℕ, (tm k : ℝ) / 2 ^ (k + 1)

/-- `d` is a base -2 expansion of `tau` with digits 0 and 1: `tau = Sum_{i ≥ 0} d i * (-2)^(-i)`. -/
def IsNegabinary (d : ℕ → ℕ) : Prop :=
  (∀ i, d i ≤ 1) ∧ HasSum (fun i : ℕ => (d i : ℝ) * (-1/2 : ℝ) ^ i) tau

theorem main :
    (∃ d : ℕ → ℕ, IsNegabinary d) ∧
      ∀ d : ℕ → ℕ, IsNegabinary d →
        HasSum (fun i : ℕ => (d i : ℝ) * (1/2 : ℝ) ^ i) (tau + 4/3) := by
  sorry

end OMA.S_oeis_a289748
