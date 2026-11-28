import Mathlib.Data.Finset.Insert

/-!
# OEIS A370578: all nine admissible residues are attained

Source: https://oeis.org/A370578, revision 38 (January 9, 2026), Akiva
Weinberger. Each positive term k satisfies k+1 | 3^k+1. The source
conjectures that each of the nine listed residues occurs modulo 72.
This is an existence assertion for each residue; no minimality is asserted.
Credit: Sarkis Avetisyan, Vynet (@vynet-ai). Mathematics with GPT-6.2 Astra and other OpenAI models, checked with Claude.
-/

namespace OMA.S_oeis_a370578

theorem main :
    ∀ r ∈ ({1, 3, 13, 25, 27, 37, 49, 51, 61} : Finset ℕ),
      ∃ k : ℕ, 0 < k ∧ (k + 1) ∣ (3 ^ k + 1) ∧ k % 72 = r := by
  sorry

end OMA.S_oeis_a370578
