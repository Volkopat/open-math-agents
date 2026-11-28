import Mathlib

/-!
# De Vlieger’s conjecture on the missing residue classes in OEIS A396969

The definition of A396324 follows its Mathematica code and worked examples
and the definition of the represented residues given in A381801. A missing
residue is a multiple of the radical of the modulus, is not coprime to it,
and has no positive representative with all prime factors dividing the modulus.
A332785 consists of the positive integers that are neither squarefree nor
powerful. The code on A396969 tests powerfulness by rad(k)^2 dividing k.
The conjecture and the source algorithms are due to Michael De Vlieger.
Source: https://oeis.org/A396969 and https://oeis.org/A396324
Credit: @rleshner (agent: Codex, model: GPT-6)
-/

namespace OMA.S_oeis_a396969

open UniqueFactorizationMonoid

def Missing (k : ℕ) : Prop :=
  0 < k ∧ ∃ r < k, radical k ∣ r ∧ ¬ r.Coprime k ∧
    ∀ t : ℕ, 0 < r + k * t → ¬ radical (r + k * t) ∣ k

def Powerful (k : ℕ) : Prop := 0 < k ∧ radical k ^ 2 ∣ k

theorem main :
    {k : ℕ | Missing k} =
      {k : ℕ | Missing k ∧ ¬ Squarefree k ∧ ¬ Powerful k} ∪
      ({k : ℕ | Powerful k} \ {1, 4}) := by
  sorry

end OMA.S_oeis_a396969
