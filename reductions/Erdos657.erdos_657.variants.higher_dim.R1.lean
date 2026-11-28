import FormalConjectures.ErdosProblems.«657»
import Mathlib.Algebra.Order.Chebyshev

/-! Equal-length ordered edges split into parallel pairs (translations up to reversal)
and pairs in distinct directions. Subcubic bounds for the two counts suffice. -/

namespace OMA.R_Erdos657_erdos_657_variants_higher_dim_R1

open Filter Finset
open scoped EuclideanGeometry Classical

/-- Equal displacement up to reversal. This part concerns additive energy. -/
def H1 : Prop := ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, ∃ N : ℕ, ∀ A : Finset (ℝ^k),
  N ≤ A.card → (A : Set (ℝ^k)).IsIsoscelesFree →
    let F := fun d : ℝ => A.offDiag.filter fun e => dist e.1 e.2 = d
    t * (∑ d ∈ distanceSet A, (((F d) ×ˢ (F d)).filter fun p =>
      p.1.1 - p.1.2 = p.2.1 - p.2.2 ∨ p.1.1 - p.1.2 = p.2.2 - p.2.1).card) ≤ A.card ^ 3

/-- Equal lengths in different directions. This part concerns geometric incidences. -/
def H2 : Prop := ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, ∃ N : ℕ, ∀ A : Finset (ℝ^k),
  N ≤ A.card → (A : Set (ℝ^k)).IsIsoscelesFree →
    let F := fun d : ℝ => A.offDiag.filter fun e => dist e.1 e.2 = d
    t * (∑ d ∈ distanceSet A, (((F d) ×ˢ (F d)).filter fun p =>
      ¬ (p.1.1 - p.1.2 = p.2.1 - p.2.2 ∨ p.1.1 - p.1.2 = p.2.2 - p.2.1)).card) ≤ A.card ^ 3

theorem count_bound {k : ℕ} (A : Finset (ℝ^k))
    (P : ((ℝ^k) × (ℝ^k)) × ((ℝ^k) × (ℝ^k)) → Prop) [DecidablePred P] :
    let F := fun d : ℝ => A.offDiag.filter fun e => dist e.1 e.2 = d
    A.offDiag.card ^ 2 ≤ distinctDistances A *
      ((∑ d ∈ distanceSet A, (((F d) ×ˢ (F d)).filter P).card) +
       (∑ d ∈ distanceSet A, (((F d) ×ˢ (F d)).filter fun p => ¬ P p).card)) := by
  intro F
  have hsum : A.offDiag.card = ∑ d ∈ distanceSet A, (F d).card :=
    card_eq_sum_card_image (fun p : (ℝ^k) × (ℝ^k) => dist p.1 p.2) A.offDiag
  rw [hsum]
  apply (sq_sum_le_card_mul_sum_sq (s := distanceSet A)
    (f := fun d => (F d).card)).trans
  apply Nat.mul_le_mul_left
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  rw [card_filter_add_card_filter_not, card_product, pow_two]

private theorem uniform_bound (h₁ : H1) (h₂ : H2) (k : ℕ) (hk : 1 ≤ k) (t : ℕ) :
    ∃ N : ℕ, ∀ A : Finset (ℝ^k), N ≤ A.card → (A : Set (ℝ^k)).IsIsoscelesFree →
      t * A.card ≤ distinctDistances A := by
  obtain ⟨N₁, hN₁⟩ := h₁ k hk (8*t)
  obtain ⟨N₂, hN₂⟩ := h₂ k hk (8*t)
  refine ⟨max 2 (max N₁ N₂), fun A hn hfree => ?_⟩
  have hn₂ : 2 ≤ A.card := (le_max_left ..).trans hn
  have hN := (le_max_right ..).trans hn
  let F := fun d : ℝ => A.offDiag.filter fun e => dist e.1 e.2 = d
  let P := fun p : ((ℝ^k) × (ℝ^k)) × ((ℝ^k) × (ℝ^k)) =>
    p.1.1 - p.1.2 = p.2.1 - p.2.2 ∨ p.1.1 - p.1.2 = p.2.2 - p.2.1
  let L := ∑ d ∈ distanceSet A, (((F d) ×ˢ (F d)).filter P).card
  let T := ∑ d ∈ distanceSet A, (((F d) ×ˢ (F d)).filter fun p => ¬ P p).card
  let E := L + T
  have hb₁ := hN₁ A ((le_max_left ..).trans hN) hfree
  have hb₂ := hN₂ A ((le_max_right ..).trans hN) hfree
  change 8*t*L ≤ A.card^3 at hb₁
  change 8*t*T ≤ A.card^3 at hb₂
  have hE : 4*t*E ≤ A.card^3 := by change 4*t*(L+T) ≤ _; nlinarith only [hb₁, hb₂]
  have hhalf : A.card ^ 2 ≤ 2 * A.offDiag.card := by
    rw [offDiag_card, pow_two]
    have h := Nat.mul_le_mul_right A.card hn₂
    omega
  have hc : A.offDiag.card^2 ≤ distinctDistances A * E := count_bound A P
  have hfour : A.card ^ 4 ≤ 4 * (distinctDistances A * E) := calc
    A.card ^ 4 = (A.card^2)^2 := by ring
    _ ≤ (2 * A.offDiag.card)^2 := Nat.pow_le_pow_left hhalf _
    _ = 4 * A.offDiag.card^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 hc
  have hprod : t * A.card * A.card^3 ≤ distinctDistances A * A.card^3 := calc
    t * A.card * A.card^3 = t * A.card^4 := by ring
    _ ≤ t * (4 * (distinctDistances A * E)) := Nat.mul_le_mul_left t hfour
    _ = distinctDistances A * (4*t*E) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hE
  exact Nat.le_of_mul_le_mul_right hprod (by positivity)

theorem main : H1 → H2 → type_of% @Erdos657.erdos_657.variants.higher_dim := by
  intro h₁ h₂ k hk
  let S (n : ℕ) : Set ℕ := {m | ∃ A : Finset (ℝ^k), A.card = n ∧
      (A : Set (ℝ^k)).IsIsoscelesFree ∧ distinctDistances A = m}
  let f (n : ℕ) : ℝ := if (S n).Nonempty then ((sInf (S n) : ℕ) : ℝ) / n else n
  refine ⟨f, tendsto_atTop.2 (fun C => ?_), ?_⟩
  · obtain ⟨t, ht⟩ := exists_nat_gt C
    obtain ⟨N, hN⟩ := uniform_bound h₁ h₂ k hk t
    filter_upwards [eventually_ge_atTop (max (t+1) N)] with n hn
    have ht' := (le_max_left ..).trans hn
    have hn' := (le_max_right ..).trans hn
    by_cases h : (S n).Nonempty
    · obtain ⟨A, hcard, hfree, hdist⟩ := Nat.sInf_mem h
      have hpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      simp only [f, if_pos h]
      apply ht.le.trans
      rw [le_div_iff₀ hpos, ← hdist, ← hcard]
      exact_mod_cast hN A (by omega) hfree
    · simp only [f, if_neg h]
      exact ht.le.trans (by exact_mod_cast (show t ≤ n by omega))
  · intro n A hcard hfree
    have hm : distinctDistances A ∈ S n := ⟨A, hcard, hfree, rfl⟩
    simp only [f, if_pos (show (S n).Nonempty from ⟨_, hm⟩)]
    by_cases hn : n = 0
    · simp [hn]
    · rw [div_mul_cancel₀ _ (by exact_mod_cast hn : (n : ℝ) ≠ 0)]
      exact_mod_cast Nat.sInf_le hm

end OMA.R_Erdos657_erdos_657_variants_higher_dim_R1
