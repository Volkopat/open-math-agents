import FormalConjectures.ErdosProblems.«722»
import Mathlib

/-!
# Erdős 722: separate absorption components from the final design assembly

Keevash's existence proof has a clean high-level interface.  The deep construction
produces, for every large admissible order, an integral omni-absorber together with a
covering decomposition whose leave lies in the reserve.  The remaining endgame is
deterministic: integral divisibility of the complete host plus those components yields
the Steiner system.  Rank one is the elementary equipartition case.
-/

open Filter Finset

namespace OMA.R_Erdos722_erdos_722_R1

/-- Deep construction input: for every rank at least two, all sufficiently large
admissible orders have integral absorption components. -/
def H1 : Prop :=
  ∀ k r : ℕ, 1 < r → r < k →
    ∃ n₀ : ℕ, k + r ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
      (∀ i < r, (k - i).choose (r - i) ∣ (n - i).choose (r - i)) →
        let U : ℕ → Finset (Finset (Fin n)) := fun t ↦
          (Finset.univ : Finset (Fin n)).powersetCard t
        let ID : Finset (Finset (Fin n)) → Prop := fun host ↦
          ∃ φ : Finset (Fin n) → ℤ, ∀ A ∈ U r,
            (∑ B ∈ U k, if A ⊆ B then φ B else 0) =
              if A ∈ host then 1 else 0
        let BD : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) → Prop :=
          fun host blocks ↦ (∀ B ∈ blocks, B.card = k) ∧
            (∀ B ∈ blocks, B.powersetCard r ⊆ host) ∧
            ∀ A ∈ host,
              (blocks.filter fun B ↦ A ∈ B.powersetCard r).card = 1
        ∃ a R c u : Finset (Finset (Fin n)),
          a ⊆ U r ∧ R ⊆ U r ∧ Disjoint a R ∧ ID a ∧
          (∀ L : Finset (Finset (Fin n)), L ⊆ R → ID L →
            ∃ b : Finset (Finset (Fin n)), BD (a ∪ L) b) ∧
          BD c u ∧ c ⊆ U r \ a ∧ (U r \ a) \ c ⊆ R

/-- Deterministic absorption endgame: integral divisibility of the complete host
plus absorption components yields the desired block design. -/
def H2 : Prop :=
  ∀ n k r : ℕ, r ≤ k →
    let U : ℕ → Finset (Finset (Fin n)) := fun t ↦
      (Finset.univ : Finset (Fin n)).powersetCard t
    let ID : Finset (Finset (Fin n)) → Prop := fun host ↦
      ∃ φ : Finset (Fin n) → ℤ, ∀ A ∈ U r,
        (∑ B ∈ U k, if A ⊆ B then φ B else 0) =
          if A ∈ host then 1 else 0
    let BD : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) → Prop :=
      fun host blocks ↦ (∀ B ∈ blocks, B.card = k) ∧
        (∀ B ∈ blocks, B.powersetCard r ⊆ host) ∧
        ∀ A ∈ host,
          (blocks.filter fun B ↦ A ∈ B.powersetCard r).card = 1
    ID (U r) →
    (∃ a R c u : Finset (Finset (Fin n)),
      a ⊆ U r ∧ R ⊆ U r ∧ Disjoint a R ∧ ID a ∧
      (∀ L : Finset (Finset (Fin n)), L ⊆ R → ID L →
        ∃ b : Finset (Finset (Fin n)), BD (a ∪ L) b) ∧
      BD c u ∧ c ⊆ U r \ a ∧ (U r \ a) \ c ⊆ R) →
    ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign r k

/-- Integral lattice input: the standard divisibility conditions imply integral
decomposability of the complete uniform host once there is enough room. -/
def H3 : Prop :=
  ∀ n k r : ℕ, r ≤ k → k + r ≤ n →
    (∀ i < r, (k - i).choose (r - i) ∣ (n - i).choose (r - i)) →
    let U : ℕ → Finset (Finset (Fin n)) := fun t ↦
      (Finset.univ : Finset (Fin n)).powersetCard t
    ∃ φ : Finset (Fin n) → ℤ, ∀ A ∈ U r,
      (∑ B ∈ U k, if A ⊆ B then φ B else 0) =
        if A ∈ U r then 1 else 0

/-- Elementary rank-one input: admissible rank-one orders have an equipartition
into blocks of size `k`. -/
def H4 : Prop :=
  ∀ n k : ℕ, 0 < k → k ≤ n →
    (∀ i < 1, (k - i).choose (1 - i) ∣ (n - i).choose (1 - i)) →
    ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 1 k

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos722.erdos_722 := by
  intro hcomponents habsorb hintegral hrankone r k hr hrk
  by_cases hr1 : r = 1
  · subst r
    filter_upwards [eventually_ge_atTop k] with n hn hadm
    exact hrankone n k (by omega) hn hadm
  · have hr2 : 1 < r := by omega
    obtain ⟨n₀, hkn₀, hn₀⟩ := hcomponents k r hr2 hrk
    filter_upwards [eventually_ge_atTop n₀] with n hn hadm
    have hroom : k + r ≤ n := hkn₀.trans hn
    exact habsorb n k r hrk.le
      (hintegral n k r hrk.le hroom hadm) (hn₀ n hn hadm)

end OMA.R_Erdos722_erdos_722_R1
