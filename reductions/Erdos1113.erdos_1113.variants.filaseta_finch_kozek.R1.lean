import FormalConjectures.ErdosProblems.«1113»
/-! The Filaseta–Finch–Kozek conjecture minus two classical covering families.

Every `k ≡ 78557 (mod 3·5·7·13·19·37·73)` has the covering set `{3, 5, 7, 13, 19, 37, 73}`
(Selfridge 1962), and every `k ≡ 271129 (mod 3·5·7·13·17·241)` has the covering set
`{3, 5, 7, 13, 17, 241}`: in each case two has period dividing 36 (resp. 24) modulo every prime
of the set, and the residues of the exponent are covered (H1). The open part is the conjecture for
Sierpiński numbers outside these two residue classes (H2).
This is a classical case, not progress on the conjecture. -/
namespace OMA.R_Erdos1113_erdos_1113_variants_filaseta_finch_kozek_R1
open Erdos1113

/-- The two classical covering families of Selfridge (78557) and of 271129. -/
def H1 : Prop := ∀ k : ℕ,
    (k ≡ 78557 [MOD 70050435] ∨ k ≡ 271129 [MOD 5592405]) → HasFinitePrimeCoveringSet k

/-- The open core: the conjecture for Sierpiński numbers outside the two families. -/
def H2 : Prop := ∀ k : ℕ, k.IsSierpinskiNumber →
    ¬ k ≡ 78557 [MOD 70050435] → ¬ k ≡ 271129 [MOD 5592405] →
    k.IsPerfectPower ∨ HasFinitePrimeCoveringSet k

theorem main : H1 → H2 →
    type_of% @Erdos1113.erdos_1113.variants.filaseta_finch_kozek := by
  intro h₁ h₂ k hk
  by_cases ha : k ≡ 78557 [MOD 70050435]
  · exact Or.inr (h₁ k (Or.inl ha))
  by_cases hb : k ≡ 271129 [MOD 5592405]
  · exact Or.inr (h₁ k (Or.inr hb))
  exact h₂ k hk ha hb

end OMA.R_Erdos1113_erdos_1113_variants_filaseta_finch_kozek_R1
