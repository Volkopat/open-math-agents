import OMAReductions.R_Erdos344_erdos_344_variants_sqrt_two_R1
import Mathlib

/-! The count immediately before the next term is exactly the prefix
size. The resulting quadratic bound also gives an interval-extension
criterion for finite subset sums. -/

open Filter Finset

namespace OMA.Erdos344Quadratic

private theorem square_count {A : Set ℕ} {N : ℕ}
    (h : Real.sqrt (2 * N) ≤ A.countUpTo N) : 2 * N ≤ A.countUpTo N ^ 2 := by
  exact_mod_cast (Real.sqrt_le_iff.mp h).2

theorem ordered_enumeration (A : Set ℕ)
    (hA : ∀ᶠ N : ℕ in atTop, Real.sqrt (2 * N) ≤ A.countUpTo N) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, a n ∈ A ∧ 0 < a n) ∧
      ∀ᶠ n : ℕ in atTop, 2 * a n ≤ n ^ 2 + 2 := by
  classical
  let p : ℕ → Prop := fun n => n ∈ A ∧ 0 < n
  obtain ⟨N, hN⟩ := eventually_atTop.mp hA
  have hinf : (Set.ofPred p).Infinite := by
    intro hfin
    let m := (Set.ofPred p).ncard
    let K := max N (m ^ 2 + 1)
    have hsub : A ∩ Set.Icc 1 K ⊆ Set.ofPred p := by
      rintro x ⟨hx, hpos, _⟩
      exact ⟨hx, hpos⟩
    have hm : A.countUpTo K ≤ m := Set.ncard_le_ncard hsub hfin
    have hm2 : A.countUpTo K ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
    have hK := square_count (hN K (le_max_left _ _))
    have hKm : m ^ 2 + 1 ≤ K := le_max_right _ _
    omega
  let a := Nat.nth p
  have hmono : StrictMono a := Nat.nth_strictMono hinf
  have hmem (n : ℕ) : a n ∈ A ∧ 0 < a n := Nat.nth_mem_of_infinite hinf n
  have hbound (n : ℕ) : n + 1 ≤ a n := by
    induction n with
    | zero => exact (hmem 0).2
    | succ n ih =>
      have hs : a n < a (n + 1) := hmono (Nat.lt_succ_self n)
      omega
  refine ⟨a, hmono, hmem, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcount : A.countUpTo (a n - 1) = n := by
    have hp := (hmem n).2
    have he : A ∩ Set.Icc 1 (a n - 1) =
        (↑((Finset.range (a n)).filter p) : Set ℕ) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range, p]
      constructor
      · rintro ⟨hx, h1, h2⟩
        exact ⟨by omega, hx, h1⟩
      · rintro ⟨hlt, hx, h1⟩
        exact ⟨hx, h1, by omega⟩
    rw [Set.countUpTo, he, Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range]
    exact Nat.count_nth_of_infinite hinf n
  have hcrit := square_count (hN (a n - 1) (by have := hbound n; omega))
  rw [hcount] at hcrit
  have hp := (hmem n).2
  omega

end OMA.Erdos344Quadratic

theorem OMA.solution : OMA.R_Erdos344_erdos_344_variants_sqrt_two_R1.H1 :=
  OMA.Erdos344Quadratic.ordered_enumeration
