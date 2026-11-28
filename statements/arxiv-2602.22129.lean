import Mathlib

/-!
# Nondegenerate 2 × (k+1) × k hypermatrices respecting a plane partition

Brandon Koprowski and Joel Brewster Lewis, "Enumeration of Nondegenerate 2 × (k+1) × k
Hypermatrices", arXiv:2602.22129, Conjecture 3.1.
Source: https://arxiv.org/abs/2602.22129

A 2 × (k+1) × k hypermatrix is a pair (M₁, M₂) of (k+1) × k matrices (its slices in the first
direction). For a partition λ = ⟨λ₁, …, λₖ⟩ of format (k+1) × k, a matrix respects λ if its
(i, j) entry is 0 whenever i > (k+1) - λⱼ (Definition 2.9); a hypermatrix respects the plane
partition P = ⟨λ, μ⟩ (μ ⊆ λ) if M₁ respects λ and M₂ respects μ (Definition 2.11). The maximal
plane partition Δ allowing nondegenerate hypermatrices has λ⁽ⁱ⁾ⱼ = (k+1) - (i+j-1)
(Definition 2.16, Theorem 2.18). Conjecture 3.1: for P = ⟨λ, μ⟩ ⊆ Δ, the number of
nondegenerate 2 × (k+1) × k hypermatrices over 𝔽_q respecting P is
  q^(k²) (q-1)^(2k) [k+1-λ₁]_q [k-λ₂]_q ⋯ [2-λₖ]_q · [k-μ₁]_q [(k-1)-μ₂]_q ⋯ [1-μₖ]_q,
where [n]_q = 1 + q + ⋯ + q^(n-1).

Nondegenerate means nonzero hyperdeterminant. Mathlib has no hyperdeterminant, so we use
Aitken's characterisation for boundary format (Lemma 2.5 of the paper, [Ait19, Lemma 2.3]):
every combination c₁M₁ + c₂M₂ with (c₁, c₂) ≠ 0 has full rank k, where the scalars range over
an algebraic closure of the field. Over 𝔽_q itself the criterion is strictly weaker: for k = 2,
q = 2 it admits 1092 hypermatrices instead of the 1008 = |G| of Corollary 3.4 (Aitken's free
transitive action), so the closure is needed for the case P = ∅ to hold.

Indices are 0-based below: row r and column j, so "i > (k+1) - λⱼ" reads
k+1 ≤ r + lam j, P ⊆ Δ reads lam j + j ≤ k and mu j + j + 1 ≤ k (lam = λ, mu = μ), and the
product is ∏ⱼ [k+1-j-λⱼ]_q · ∏ⱼ [k-j-μⱼ]_q.

Sanity check: brute force over 𝔽₂ and 𝔽₃ (rank drops over the closure detected by gcds of
maximal minors of the pencil) agrees with the formula for every P ⊆ Δ with k ≤ 2, and for
k = 3, q = 2 on all 27 plane partitions P ⊆ Δ leaving at most 18 free entries. The paper proves k = 2, one-layer P, and the extreme cases. Searches found no proof of the general case.
-/

namespace OMA.S_arxiv_2602_22129

/-- A `(k+1) × k` matrix respects the partition `lam` (0-based Definition 2.9). -/
def Respects {F : Type} [Zero F] {k : ℕ} (lam : Fin k → ℕ)
    (M : Matrix (Fin (k + 1)) (Fin k) F) : Prop :=
  ∀ r j, k + 1 ≤ r.val + lam j → M r j = 0

/-- The hypermatrix with slices `M₁, M₂` is nondegenerate (Aitken's criterion). -/
def Nondegenerate {F : Type} [Field F] {k : ℕ} (M₁ M₂ : Matrix (Fin (k + 1)) (Fin k) F) : Prop :=
  ∀ c₁ c₂ : AlgebraicClosure F, (c₁, c₂) ≠ 0 →
    (c₁ • M₁.map (algebraMap F (AlgebraicClosure F)) +
      c₂ • M₂.map (algebraMap F (AlgebraicClosure F))).rank = k

/-- The `q`-integer `[n]_q = 1 + q + ⋯ + q^(n-1)`. -/
def qInt (n q : ℕ) : ℕ := ∑ i ∈ Finset.range n, q ^ i

theorem main : ∀ (F : Type) [Field F] [Fintype F] (k : ℕ), 1 ≤ k →
    ∀ lam mu : Fin k → ℕ, Antitone lam → Antitone mu → (∀ j, mu j ≤ lam j) →
      (∀ j, lam j + j.val ≤ k) → (∀ j, mu j + j.val + 1 ≤ k) →
      Nat.card {M : Matrix (Fin (k + 1)) (Fin k) F × Matrix (Fin (k + 1)) (Fin k) F //
          Respects lam M.1 ∧ Respects mu M.2 ∧ Nondegenerate M.1 M.2} =
        Fintype.card F ^ (k ^ 2) * (Fintype.card F - 1) ^ (2 * k) *
          (∏ j : Fin k, qInt (k + 1 - j.val - lam j) (Fintype.card F)) *
          ∏ j : Fin k, qInt (k - j.val - mu j) (Fintype.card F) := by
  sorry

end OMA.S_arxiv_2602_22129
