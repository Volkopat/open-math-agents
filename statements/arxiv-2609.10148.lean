import Mathlib

namespace OMA.S_arxiv_2609_10148

/-- The restricted sumset `A ∔ B = {a + b | a ∈ A, b ∈ B, a ≠ b}` in `ZMod p`. -/
def restrictedSumset {p : ℕ} (A B : Finset (ZMod p)) : Finset (ZMod p) :=
  ((A ×ˢ B).filter fun x => x.1 ≠ x.2).image fun x => x.1 + x.2

/-- A subset `S ⊆ ZMod p` is an arithmetic progression if there exist `a, d ∈ ZMod p` with
`d ≠ 0` such that `S = {a + k • d | 0 ≤ k < |S|}`. -/
def IsArithProg {p : ℕ} (S : Finset (ZMod p)) : Prop :=
  ∃ a d : ZMod p, d ≠ 0 ∧
    S = (Finset.range S.card).image (fun k : ℕ => a + (k : ZMod p) * d)

/-- Liu and Qian's conjecture on critical pairs for restricted sumsets in `ℤ_p` (refuted in
arXiv:2609.10148): for any prime `p` and subsets `A, B ⊆ ℤ_p` with `|A|, |B| ≥ 4`, `|A| ≠ |B|`,
and `|A| + |B| ≤ p`, attaining equality `|A ∔ B| = |A| + |B| - 2` in the Alon–Nathanson–Ruzsa
bound forces both `A` and `B` to be arithmetic progressions with a common difference. -/
theorem main :
    ∀ (p : ℕ), Nat.Prime p →
      ∀ (A B : Finset (ZMod p)),
        4 ≤ A.card → 4 ≤ B.card → A.card ≠ B.card → A.card + B.card ≤ p →
        (restrictedSumset A B).card = A.card + B.card - 2 →
        IsArithProg A ∧ IsArithProg B := by
  sorry

end OMA.S_arxiv_2609_10148
