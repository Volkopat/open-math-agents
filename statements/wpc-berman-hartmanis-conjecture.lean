import Mathlib

/-!
# Berman–Hartmanis conjecture

Source: https://en.wikipedia.org/wiki/Berman%E2%80%93Hartmanis_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Berman–Hartmanis): all NP-complete languages are polynomial-time isomorphic: for
any two of them there is a bijection `f` on strings, with `f` and `f⁻¹` computable in
polynomial time, such that `x ∈ A ↔ f x ∈ B`.

Conventions (as in earlier merged statements of this repository, e.g. mo-47956).
* Languages are sets of bit strings `List Bool`; polynomial-time computability is Mathlib's
  `Turing.TM2ComputableInPolyTime` with the identity-style encodings below.
* NP: membership is witnessed by a polynomially bounded certificate checked by a polynomial
  time verifier. NP-hard: every NP language many-one reduces to it in polynomial time.
  NP-complete: in NP and NP-hard.
-/

namespace OMA.S_wpc_berman_hartmanis_conjecture

abbrev Bits := List Bool

/-- Self-delimiting prefix used to encode pairs. -/
def framed (s : Bits) : Bits := List.replicate s.length true ++ [false] ++ s

/-- Polynomial-time computability for the given encodings. -/
def poly {α β : Type} (ea : α → Bits) (eb : β → Bits) (f : α → β) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

/-- `L ∈ NP`. -/
def inNP (L : Set Bits) : Prop :=
  ∃ (v : Bits × Bits → Bool) (k c : ℕ),
    poly (fun p => framed p.1 ++ p.2) (fun b => [b]) v ∧
    ∀ x, x ∈ L ↔ ∃ w : Bits, w.length ≤ c * (x.length + 1) ^ k ∧ v (x, w) = true

/-- `H` is NP-hard under polynomial-time many-one reductions. -/
def hard (H : Set Bits) : Prop :=
  ∀ L : Set Bits, inNP L → ∃ r : Bits → Bits, poly id id r ∧ ∀ x, x ∈ L ↔ r x ∈ H

/-- `L` is NP-complete. -/
def NPComplete (L : Set Bits) : Prop := inNP L ∧ hard L

/-- The Berman–Hartmanis conjecture. -/
theorem main :
    ∀ A B : Set Bits, NPComplete A → NPComplete B →
      ∃ f : Bits ≃ Bits, poly id id f ∧ poly id id f.symm ∧ ∀ x, x ∈ A ↔ f x ∈ B := by
  sorry

end OMA.S_wpc_berman_hartmanis_conjecture
