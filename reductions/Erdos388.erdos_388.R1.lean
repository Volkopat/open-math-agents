import FormalConjectures.ErdosProblems.«388»

-- Reduction Erdos388.erdos_388.R1 of Erdős Problem 388
-- Credit: @sntntHb (agent: Claude Code, model claude-opus-5-5)
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Sketch. The finiteness of all solutions of
`(m₁+1)⋯(m₁+k₁) = (m₂+1)⋯(m₂+k₂)` (disjoint blocks, `k₁, k₂ > 3`) splits into two
genuinely different statements:

* `H1` (fixed lengths): for each fixed pair `k₁, k₂ > 3` there are only finitely many
  `(m₁, m₂)`. This is a statement about the single fixed curve `P_{k₁}(x) = P_{k₂}(y)`
  (Siegel-type finiteness of integer points; the equal-products equation for fixed lengths
  is studied by Beukers, Shorey and Tijdeman via irreducibility of the curve).
* `H2` (uniform length bound): there is `K` such that every solution has `k₁, k₂ ≤ K`.
  This is the part where the lengths grow, handled by prime-factor / Sylvester-type arguments.

`main`: under `H2` the solution set lies in the finite union over `4 ≤ k₁, k₂ ≤ K` of the
images of the finite sets from `H1`. No computer search.
-/

namespace OMA.R_Erdos388_erdos_388_R1

def H1 : Prop :=
  ∀ k₁ k₂ : ℕ, 3 < k₁ → 3 < k₂ →
    {p : ℕ × ℕ | p.1 + k₁ ≤ p.2 ∧
      ∏ i ∈ Finset.Icc 1 k₁, (p.1 + i) = ∏ j ∈ Finset.Icc 1 k₂, (p.2 + j)}.Finite

def H2 : Prop :=
  ∃ K : ℕ, ∀ m₁ k₁ m₂ k₂ : ℕ, 3 < k₁ → 3 < k₂ → m₁ + k₁ ≤ m₂ →
    ∏ i ∈ Finset.Icc 1 k₁, (m₁ + i) = ∏ j ∈ Finset.Icc 1 k₂, (m₂ + j) →
    k₁ ≤ K ∧ k₂ ≤ K

theorem main : H1 → H2 → type_of% @Erdos388.erdos_388 := by
  intro h1 h2
  unfold H1 at h1
  unfold H2 at h2
  obtain ⟨K, hK⟩ := h2
  have hfin : (⋃ k₁ ∈ Set.Icc 4 K, ⋃ k₂ ∈ Set.Icc 4 K,
      (fun p : ℕ × ℕ => (p.1, k₁, p.2, k₂)) ''
        {p : ℕ × ℕ | p.1 + k₁ ≤ p.2 ∧
          ∏ i ∈ Finset.Icc 1 k₁, (p.1 + i) = ∏ j ∈ Finset.Icc 1 k₂, (p.2 + j)}).Finite := by
    refine Set.Finite.biUnion (Set.finite_Icc 4 K) (fun k₁ hk₁ => ?_)
    refine Set.Finite.biUnion (Set.finite_Icc 4 K) (fun k₂ hk₂ => ?_)
    exact (h1 k₁ k₂ (by simp only [Set.mem_Icc] at hk₁; omega)
      (by simp only [Set.mem_Icc] at hk₂; omega)).image _
  apply hfin.subset
  rintro ⟨m₁, k₁, m₂, k₂⟩ ⟨hk₁, hk₂, ho, he⟩
  obtain ⟨b₁, b₂⟩ := hK m₁ k₁ m₂ k₂ hk₁ hk₂ ho he
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Icc]
  exact ⟨k₁, ⟨by omega, b₁⟩, k₂, ⟨by omega, b₂⟩, (m₁, m₂), ⟨ho, he⟩, rfl⟩

end OMA.R_Erdos388_erdos_388_R1
