import OMAReductions.R_Erdos774_erdos_774_R1
import Mathlib

/-!
# Bounded-length relations in the finite Sidon decomposition problem

Bourgain's Proposition 3.2 in *Propriétés de décomposition pour les ensembles
de Sidon* (1983) partitions a Sidon set into pieces without relations of any
given bounded length. The first hypothesis is its finite quantitative form
under proportional dissociation. The second asks for a uniform full cover
only on sets where all sufficiently short relations have already been removed.
The length threshold may depend on the extraction proportion.
-/
-- Credit: @VestigeClub

open Finset

namespace OMA.R_Erdos774_erdos_774_R1_H2_R1

/-- Extension by zero passes the weighted extraction property to every
subset, with exactly the same proportion. -/
private theorem restrict_weights {δ : ℝ} {F B : Finset ℕ} (sub : B ⊆ F)
    (extract : ∀ w : ℕ → ℝ, (∀ n ∈ F, 0 ≤ w n) →
      ∃ S ⊆ F, Set.IsDissociated (↑S : Set ℕ) ∧
        (∑ n ∈ S, w n) ≥ δ * (∑ n ∈ F, w n)) :
    ∀ w : ℕ → ℝ, (∀ n ∈ B, 0 ≤ w n) →
      ∃ S ⊆ B, Set.IsDissociated (↑S : Set ℕ) ∧
        (∑ n ∈ S, w n) ≥ δ * (∑ n ∈ B, w n) := by
  classical
  intro w positive
  let v (n : ℕ) := if n ∈ B then w n else 0
  have nonneg (n : ℕ) (_ : n ∈ F) : 0 ≤ v n := by
    by_cases hn : n ∈ B
    · simpa [v, hn] using positive n hn
    · simp [v, hn]
  obtain ⟨S, _, indep, heavy⟩ := extract v nonneg
  have restrict_sum (T : Finset ℕ) : (∑ n ∈ T, v n) =
      ∑ n ∈ T.filter (· ∈ B), w n := by
    rw [Finset.sum_filter]
  have whole : F.filter (· ∈ B) = B := by
    ext n
    exact Finset.mem_filter.trans ⟨And.right, fun h => ⟨sub h, h⟩⟩
  refine ⟨S.filter (· ∈ B), fun _ h => (mem_filter.mp h).2, ?_, ?_⟩
  · intro X hX Y hY equal
    exact indep (fun n hn => (mem_filter.mp (hX hn)).1)
      (fun n hn => (mem_filter.mp (hY hn)).1) equal
  · simpa only [restrict_sum, whole] using heavy

/-- Finite quantitative bounded-length decomposition. The input uses just
cardinalities. A relation of support at most r would lie in one of the
tested subsets of size at most r. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ r : ℕ, 3 ≤ r → ∃ k : ℕ, 0 < k ∧ ∀ F : Finset ℕ,
    (∀ B ⊆ F, ∃ S ⊆ B, Set.IsDissociated (↑S : Set ℕ) ∧
      (S.card : ℝ) ≥ δ * B.card) →
    ∃ B : Fin k → Finset ℕ, (∀ i, B i ⊆ F) ∧
      (∀ n ∈ F, ∃ i, n ∈ B i) ∧
      ∀ i, ∀ T ⊆ B i, T.card ≤ r → Set.IsDissociated (↑T : Set ℕ)

/-- Uniform fully dissociated cover on weighted sets having no short
relation. Both constants are independent of the size and entries of F. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ r k : ℕ, 3 ≤ r ∧ 0 < k ∧ ∀ F : Finset ℕ,
    (∀ T ⊆ F, T.card ≤ r → Set.IsDissociated (↑T : Set ℕ)) →
    (∀ w : ℕ → ℝ, (∀ n ∈ F, 0 ≤ w n) →
      ∃ S ⊆ F, Set.IsDissociated (↑S : Set ℕ) ∧
        (∑ n ∈ S, w n) ≥ δ * (∑ n ∈ F, w n)) →
    ∃ D : Fin k → Set ℕ, (∀ i, Set.IsDissociated (D i)) ∧
      (↑F : Set ℕ) ⊆ ⋃ i, D i

theorem main : H1 → H2 → OMA.R_Erdos774_erdos_774_R1.H2 := by
  classical
  intro prune finish δ pos
  obtain ⟨r,k,hr,hk,cover⟩ := finish δ pos
  obtain ⟨m,hm,blocks⟩ := prune δ pos r hr
  refine ⟨m*k, Nat.mul_pos hm hk, ?_⟩
  intro F extract
  have smaller (B : Finset ℕ) (sub : B ⊆ F) :
      ∃ S ⊆ B, Set.IsDissociated (↑S : Set ℕ) ∧ (S.card : ℝ) ≥ δ * B.card := by
    obtain ⟨S,hS,indep,heavy⟩ :=
      restrict_weights sub extract (fun _ => 1) (fun _ _ => zero_le_one)
    exact ⟨S,hS,indep,by simpa using heavy⟩
  obtain ⟨B,inside,all,short⟩ := blocks F smaller
  choose D good covers using fun i => cover (B i) (short i) (restrict_weights (inside i) extract)
  let e : Fin m × Fin k ≃ Fin (m*k) := finProdFinEquiv
  refine ⟨fun a => D (e.symm a).1 (e.symm a).2, fun a => good _ _, ?_⟩
  intro n hn
  obtain ⟨i,hi⟩ := all n hn
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (covers i hi)
  exact Set.mem_iUnion.mpr ⟨e (i,j), by simpa using hj⟩

end OMA.R_Erdos774_erdos_774_R1_H2_R1
