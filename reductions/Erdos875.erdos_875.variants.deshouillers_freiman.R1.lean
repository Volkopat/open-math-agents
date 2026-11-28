import FormalConjectures.ErdosProblems.«875»

/-!
# Three-step reduction for the Deshouillers–Freiman bound on Erdős Problem 875

Reduces `Erdos875.erdos_875.variants.deshouillers_freiman` (`|A| ≤ 2 √(N + 1/4) - 1`
for sufficiently large `N` and admissible `A ⊆ {1, …, N}`) to three cleanly separated
components reflecting the Deshouillers–Freiman (1995, 1999) architecture:

- `H1`: exclusion of primitive admissible sets (`gcd(A) = 1`) lying in a single residue
  class modulo `d ≥ 2` above the non-vacuous threshold `4 N ≤ |A| (|A| + 3)` (satisfied by
  extremal consecutive intervals `{N - k + 1, …, N}`, while single-class sets mod `d ≥ 2`
  have size at most `2 √N - d + o(1)`).
- `H2`: diameter localization (`20 * (b - a) ≤ 21 * |A|`) for primitive admissible sets
  near the extremal bound `100 N ≤ |A| (25 |A| + 51)` (Deshouillers–Freiman 1995).
- `H3`: a pure finite-combinatorics hole bound on the middle restricted sumset `S_r(B)`
  of dense subsets `B ⊂ ℕ` (density `≥ 10/11` in their bounding interval).

Inside `main`, we prove directly:
1. Equivalence of `|A| ≤ 2 √(N + 1/4) - 1` with `|A| (|A| + 2) ≤ 4 N`, and passage to a
   minimally-exceeding admissible subset.
2. The restricted sumset lower bound `|S_r(A)| ≥ r (|A| - r) + 1`.
3. Straus's `4/√3 · √N` packing bound and the resulting elimination of `gcd(A) ≥ 2`.
4. The exact arithmetic bound `a₁ + g ≤ r (m - r)` and the pigeonhole difference collision
   closing `H1 → H2 → H3 → target`.
-/

namespace OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1

open Finset Erdos875

/-- For sufficiently large `N`, an admissible subset `A ⊆ {1, …, N}` with
`4 * N ≤ |A| * (|A| + 3)` and `gcd(A) = 1` cannot lie in a single residue class modulo any
`d ≥ 2`. -/
def H1 : Prop :=
  ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ A : Finset ℕ, (A : Set ℕ) ⊆ Set.Icc 1 N →
    IsAdmissible (A : Set ℕ) → 4 * N ≤ A.card * (A.card + 3) →
    (∀ g : ℕ, 2 ≤ g → ∃ a ∈ A, ¬ g ∣ a) →
    ∀ d : ℕ, 2 ≤ d → ∃ a ∈ A, ∃ b ∈ A, a % d ≠ b % d

/-- For sufficiently large `N`, an admissible subset `A ⊆ {1, …, N}` near the extremal size
(`100 * N ≤ |A| * (25 * |A| + 51)` and `(|A| - 1) * (|A| + 1) ≤ 4 * N`) with
`gcd(A - min A) = 1` has diameter at most `(21 / 20) * |A|`. -/
def H2 : Prop :=
  ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → ∀ A : Finset ℕ, (A : Set ℕ) ⊆ Set.Icc 1 N →
    IsAdmissible (A : Set ℕ) →
    100 * N ≤ A.card * (25 * A.card + 51) → (A.card - 1) * (A.card + 1) ≤ 4 * N →
    (∀ d : ℕ, 2 ≤ d → ∃ a ∈ A, ∃ b ∈ A, a % d ≠ b % d) →
    ∀ a ∈ A, ∀ b ∈ A, 20 * (b - a) ≤ 21 * A.card

/-- Pure combinatorial hole bound for dense restricted sumsets: if `B ⊂ ℕ` has size `m ≥ 20`
and missing-element count `g = (max B - min B) - (m - 1) ≤ m / 10`, then for `r = m / 2`
the number of integers missing from `S_r(B)` inside its bounding interval `[L, M]` satisfies
`2 * ((M - L + 1) - |S_r(B)|) ≤ (M - L) - r * (m - r) + g`. -/
def H3 : Prop :=
  ∀ (B : Finset ℕ) (hB : B.Nonempty), 20 ≤ B.card →
    ∀ L M : ℕ,
    (∀ T ∈ B.powersetCard (B.card / 2), L ≤ ∑ x ∈ T, x ∧ ∑ x ∈ T, x ≤ M) →
    (∃ T ∈ B.powersetCard (B.card / 2), ∑ x ∈ T, x = L) →
    (∃ T ∈ B.powersetCard (B.card / 2), ∑ x ∈ T, x = M) →
    10 * ((B.max' hB - B.min' hB) - (B.card - 1)) ≤ B.card →
    2 * ((M - L + 1) - ((B.powersetCard (B.card / 2)).image (fun T => ∑ x ∈ T, x)).card) ≤
      (M - L) - (B.card / 2) * (B.card - B.card / 2) +
        ((B.max' hB - B.min' hB) - (B.card - 1))

lemma admissible_subset {A B : Finset ℕ} (hsub : B ⊆ A)
    (hadm : IsAdmissible (A : Set ℕ)) : IsAdmissible (B : Set ℕ) := by
  intro r hr s hs hrs
  refine Set.disjoint_left.mpr fun x hxr hxs => ?_
  obtain ⟨T₁, hT₁, hc₁, hs₁⟩ := hxr
  obtain ⟨T₂, hT₂, hc₂, hs₂⟩ := hxs
  exact Set.disjoint_left.mp (hadm hr hs hrs)
    ⟨T₁, hT₁.trans (Finset.coe_subset.mpr hsub), hc₁, hs₁⟩
    ⟨T₂, hT₂.trans (Finset.coe_subset.mpr hsub), hc₂, hs₂⟩

lemma exists_min_excess_subset {A : Finset ℕ} {N : ℕ}
    (hgt : 4 * N < A.card * (A.card + 2)) :
    ∃ B ⊆ A, 4 * N < B.card * (B.card + 2) ∧ (B.card - 1) * (B.card + 1) ≤ 4 * N := by
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | h n ih =>
    subst hn
    by_cases hle : (A.card - 1) * (A.card + 1) ≤ 4 * N
    · exact ⟨A, Subset.rfl, hgt, hle⟩
    · have hne : A.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        simp [h] at hgt
      obtain ⟨a, ha⟩ := hne
      have hcard : (A.erase a).card = A.card - 1 := Finset.card_erase_of_mem ha
      have hpos : 0 < A.card := Finset.card_pos.mpr ⟨a, ha⟩
      have hlt : (A.erase a).card < A.card := by omega
      have hgt' : 4 * N < (A.erase a).card * ((A.erase a).card + 2) := by
        rw [hcard]
        have h1 : A.card - 1 + 2 = A.card + 1 := by omega
        rw [h1]
        omega
      obtain ⟨B, hBsub, hBgt, hBle⟩ := ih (A.erase a).card hlt hgt' rfl
      exact ⟨B, hBsub.trans (Finset.erase_subset a A), hBgt, hBle⟩

lemma card_rSums_ge (A : Finset ℕ) :
    ∀ r ≤ A.card, r * (A.card - r) + 1 ≤ ((A.powersetCard r).image (fun T => ∑ x ∈ T, x)).card := by
  induction A using Finset.induction_on_max with
  | empty =>
    intro r hr
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    simp
  | insert a A hmax ih =>
    intro r hr
    have ha : a ∉ A := fun h => (hmax a h).false
    have hcard : (insert a A).card = A.card + 1 := Finset.card_insert_of_notMem ha
    rw [hcard] at hr ⊢
    by_cases hr0 : r = 0
    · subst hr0; simp
    by_cases hrmax : r = A.card + 1
    · subst hrmax
      have hne : ((insert a A).powersetCard (A.card + 1)).Nonempty :=
        Finset.powersetCard_nonempty.mpr (by rw [hcard])
      have hpos := Finset.card_pos.mpr (hne.image (fun T => ∑ x ∈ T, x))
      simp only [Nat.sub_self, Nat.mul_zero, zero_add]
      exact hpos
    have hrA : r ≤ A.card := by omega
    set S := ((insert a A).powersetCard r).image (fun T => ∑ x ∈ T, x)
    set S0 := (A.powersetCard r).image (fun T => ∑ x ∈ T, x)
    have hS0_sub : S0 ⊆ S := by
      intro s hs
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hs
      rw [Finset.mem_powersetCard] at hT
      exact Finset.mem_image.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨hT.1.trans (Finset.subset_insert a A), hT.2⟩, rfl⟩
    -- Build `r` elements of `S` strictly larger than `max S0` by taking a max-sum `r`-subset of `A`
    -- and replacing one of its elements by `a`.
    have hS0_ne : S0.Nonempty := (Finset.powersetCard_nonempty.mpr hrA).image _
    set m0 := S0.max' hS0_ne
    obtain ⟨T0, hT0_mem, hT0_sum⟩ := Finset.mem_image.mp (Finset.max'_mem S0 hS0_ne)
    change ∑ x ∈ T0, x = m0 at hT0_sum
    rw [Finset.mem_powersetCard] at hT0_mem
    let E := T0.image (fun b => a + (m0 - b))
    have hE_card : E.card = r := by
      rw [Finset.card_image_of_injOn]
      · exact hT0_mem.2
      · intro x hx y hy hxy
        dsimp only at hxy
        have hbx : x ≤ m0 := by
          rw [← hT0_sum]
          exact Finset.single_le_sum (f := fun z => z) (fun _ _ => Nat.zero_le _) hx
        have hby : y ≤ m0 := by
          rw [← hT0_sum]
          exact Finset.single_le_sum (f := fun z => z) (fun _ _ => Nat.zero_le _) hy
        omega
    have hE_sub : E ⊆ S := by
      intro s hs
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
      have hba : a ∉ T0.erase b := fun h => ha (hT0_mem.1 (Finset.mem_of_mem_erase h))
      refine Finset.mem_image.mpr ⟨insert a (T0.erase b), Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hT0_mem.1 (Finset.mem_of_mem_erase hz'))
      · rw [Finset.card_insert_of_notMem hba, Finset.card_erase_of_mem hb, hT0_mem.2]
        omega
      · rw [Finset.sum_insert hba]
        have hsum := Finset.add_sum_erase T0 (fun x => x) hb
        omega
    have hdisj : Disjoint S0 E := by
      refine Finset.disjoint_left.mpr fun s hs0 hsE => ?_
      have hle : s ≤ m0 := Finset.le_max' S0 s hs0
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hsE
      have hbA : b ∈ A := hT0_mem.1 hb
      have hlt : b < a := hmax b hbA
      have hbm : b ≤ m0 := by
        rw [← hT0_sum]
        exact Finset.single_le_sum (f := fun z => z) (fun _ _ => Nat.zero_le _) hb
      omega
    have hstep : S0.card + E.card ≤ S.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset hS0_sub hE_sub)
    have hih : r * (A.card - r) + 1 ≤ S0.card := ih r hrA
    rw [hE_card] at hstep
    have hmul : r * (A.card + 1 - r) = r * (A.card - r) + r := by
      have : A.card + 1 - r = (A.card - r) + 1 := by omega
      rw [this, Nat.mul_add, Nat.mul_one]
    omega

lemma straus_packing_bound {A : Finset ℕ} {N : ℕ}
    (hsub : (A : Set ℕ) ⊆ Set.Icc 1 N) (hadm : IsAdmissible (A : Set ℕ))
    (t : ℕ) (ht : t ≤ A.card) :
    ∑ r ∈ Finset.Icc 1 t, (r * (A.card - r) + 1) ≤ t * N := by
  let S (r : ℕ) : Finset ℕ := (A.powersetCard r).image (fun T => ∑ x ∈ T, x)
  have hS_sub : ∀ r ∈ Finset.Icc 1 t, S r ⊆ Finset.Icc 1 (t * N) := by
    intro r hr s hs
    rw [Finset.mem_Icc] at hr
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hs
    rw [Finset.mem_powersetCard] at hT
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x₀, hx₀⟩ := hTne
    have h1 : 1 ≤ ∑ x ∈ T, x := by
      have hx1 : 1 ≤ x₀ := (hsub (hT.1 hx₀)).1
      exact le_trans hx1 (Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hx₀)
    have h2 : ∑ x ∈ T, x ≤ t * N := calc
      ∑ x ∈ T, x ≤ ∑ _x ∈ T, N := Finset.sum_le_sum fun x hx => (hsub (hT.1 hx)).2
      _ = T.card * N := by simp
      _ = r * N := by rw [hT.2]
      _ ≤ t * N := Nat.mul_le_mul_right N hr.2
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hdisj : (Finset.Icc 1 t : Set ℕ).PairwiseDisjoint S := by
    intro r hr s hs hrs
    rw [Finset.mem_coe, Finset.mem_Icc] at hr hs
    refine Finset.disjoint_left.mpr fun x hxr hxs => ?_
    obtain ⟨T₁, hT₁, rfl⟩ := Finset.mem_image.mp hxr
    obtain ⟨T₂, hT₂, hsum⟩ := Finset.mem_image.mp hxs
    rw [Finset.mem_powersetCard] at hT₁ hT₂
    have hdisj_set := hadm hr.1 hs.1 hrs
    exact Set.disjoint_left.mp hdisj_set
      ⟨T₁, Finset.coe_subset.mpr hT₁.1, hT₁.2, rfl⟩
      ⟨T₂, Finset.coe_subset.mpr hT₂.1, hT₂.2, hsum⟩
  have hcard_biUnion :
      ∑ r ∈ Finset.Icc 1 t, (S r).card ≤ t * N := by
    rw [← Finset.card_biUnion hdisj]
    calc ((Finset.Icc 1 t).biUnion S).card
      _ ≤ (Finset.Icc 1 (t * N)).card := Finset.card_le_card (Finset.biUnion_subset.mpr hS_sub)
      _ = t * N := by simp
  calc ∑ r ∈ Finset.Icc 1 t, (r * (A.card - r) + 1)
    _ ≤ ∑ r ∈ Finset.Icc 1 t, (S r).card := by
        apply Finset.sum_le_sum
        intro r hr
        rw [Finset.mem_Icc] at hr
        exact card_rSums_ge A r (hr.2.trans ht)
    _ ≤ t * N := hcard_biUnion

lemma sum_Icc_quadratic (k t : ℕ) (ht : t ≤ k) :
    6 * ∑ r ∈ Finset.Icc 1 t, (r * (k - r) + 1) =
      3 * k * t * (t + 1) - t * (t + 1) * (2 * t + 1) + 6 * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have htk : t ≤ k := by omega
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos t), Nat.mul_add, ih htk]
    have hle1 : t * (t + 1) * (2 * t + 1) ≤ 3 * k * t * (t + 1) := by
      rcases t with _ | t
      · simp
      · calc (t + 1) * (t + 1 + 1) * (2 * (t + 1) + 1)
          _ ≤ (t + 1) * (t + 1 + 1) * (3 * k) := Nat.mul_le_mul_left _ (by omega)
          _ = 3 * k * (t + 1) * (t + 1 + 1) := by ring
    have hle2 : (t + 1) * (t + 2) * (2 * (t + 1) + 1) ≤ 3 * k * (t + 1) * (t + 2) := by
      calc (t + 1) * (t + 2) * (2 * (t + 1) + 1)
        _ ≤ (t + 1) * (t + 2) * (3 * k) := Nat.mul_le_mul_left _ (by omega)
        _ = 3 * k * (t + 1) * (t + 2) := by ring
    zify [hle1, hle2, ht, htk]
    ring

lemma straus_bound {A : Finset ℕ} {N : ℕ}
    (hsub : (A : Set ℕ) ⊆ Set.Icc 1 N) (hadm : IsAdmissible (A : Set ℕ)) :
    3 * A.card ^ 2 ≤ 16 * N + 27 := by
  set k := A.card
  by_cases hk : k < 4
  · nlinarith
  set t := 3 * k / 4
  have ht_le : t ≤ k := by omega
  have ht_ge : 3 * k ≤ 4 * t + 3 := by omega
  have ht_up : 4 * t ≤ 3 * k := by omega
  have hpack : ∑ r ∈ Finset.Icc 1 t, (r * (k - r) + 1) ≤ t * N :=
    straus_packing_bound hsub hadm t ht_le
  have hquad := sum_Icc_quadratic k t ht_le
  have hle : t * (t + 1) * (2 * t + 1) ≤ 3 * k * t * (t + 1) := by
    calc t * (t + 1) * (2 * t + 1)
      _ ≤ t * (t + 1) * (3 * k) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * k * t * (t + 1) := by ring
  have h6 : 3 * k * t * (t + 1) - t * (t + 1) * (2 * t + 1) ≤ 6 * t * N := by
    have hmul : 6 * ∑ r ∈ Finset.Icc 1 t, (r * (k - r) + 1) ≤ 6 * t * N := by
      calc 6 * ∑ r ∈ Finset.Icc 1 t, (r * (k - r) + 1)
        _ ≤ 6 * (t * N) := Nat.mul_le_mul_left 6 hpack
        _ = 6 * t * N := by ring
    omega
  have hdiv : t * (3 * k * (t + 1) - (t + 1) * (2 * t + 1)) ≤ t * (6 * N) := by
    have hmul1 : t * (3 * k * (t + 1)) = 3 * k * t * (t + 1) := by ring
    have hmul2 : t * ((t + 1) * (2 * t + 1)) = t * (t + 1) * (2 * t + 1) := by ring
    have hmul3 : t * (6 * N) = 6 * t * N := by ring
    rw [Nat.mul_sub_left_distrib, hmul1, hmul2, hmul3]
    exact h6
  have ht_pos : 0 < t := by omega
  have hcancel : 3 * k * (t + 1) - (t + 1) * (2 * t + 1) ≤ 6 * N :=
    Nat.le_of_mul_le_mul_left hdiv ht_pos
  have hsub_le : (t + 1) * (2 * t + 1) ≤ 3 * k * (t + 1) := by
    calc (t + 1) * (2 * t + 1)
      _ ≤ (t + 1) * (3 * k) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * k * (t + 1) := by ring
  have hlin : 3 * k * (t + 1) ≤ 6 * N + (t + 1) * (2 * t + 1) := by omega
  have hlin_z : 3 * (k : ℤ) * ((t : ℤ) + 1) ≤ 6 * (N : ℤ) + ((t : ℤ) + 1) * (2 * (t : ℤ) + 1) := by
    exact_mod_cast hlin
  have hprod : (0 : ℤ) ≤ (3 * (k : ℤ) - 4 * (t : ℤ)) * (4 * (t : ℤ) + 3 - 3 * (k : ℤ)) :=
    mul_nonneg (by omega) (by omega)
  have h9 : (9 : ℤ) * (k : ℤ) ^ 2 ≤ 48 * (N : ℤ) + 8 := by nlinarith
  have h9_nat : 9 * k ^ 2 ≤ 48 * N + 8 := by exact_mod_cast h9
  omega

lemma gcd_one_of_admissible {A : Finset ℕ} {N : ℕ} (hN : 400 ≤ N)
    (hsub : (A : Set ℕ) ⊆ Set.Icc 1 N) (hadm : IsAdmissible (A : Set ℕ))
    (hgt : 4 * N < A.card * (A.card + 2)) :
    ∀ g : ℕ, 2 ≤ g → ∃ a ∈ A, ¬ g ∣ a := by
  intro g hg
  by_contra hdiv
  push Not at hdiv
  have hg_pos : 0 < g := by omega
  let A' := A.image (· / g)
  have hcard : A'.card = A.card := by
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    dsimp only at hxy
    rw [← Nat.mul_div_cancel' (hdiv x hx), ← Nat.mul_div_cancel' (hdiv y hy), hxy]
  have hsub' : (A' : Set ℕ) ⊆ Set.Icc 1 (N / g) := by
    intro y hy
    rw [Finset.mem_coe] at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxIcc := hsub hx
    have hxd := hdiv x hx
    exact ⟨Nat.div_pos (Nat.le_of_dvd hxIcc.1 hxd) hg_pos, Nat.div_le_div_right hxIcc.2⟩
  have hadm' : IsAdmissible (A' : Set ℕ) := by
    intro r hr s hs hrs
    refine Set.disjoint_left.mpr fun z hzr hzs => ?_
    obtain ⟨T₁, hT₁, hc₁, hs₁⟩ := hzr
    obtain ⟨T₂, hT₂, hc₂, hs₂⟩ := hzs
    let U₁ := T₁.image (g * ·)
    let U₂ := T₂.image (g * ·)
    have hUsub : ∀ T : Finset ℕ, (T : Set ℕ) ⊆ (A' : Set ℕ) → (T.image (g * ·) : Set ℕ) ⊆ (A : Set ℕ) := by
      intro T hT u hu
      rw [Finset.mem_coe] at hu ⊢
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu
      have hyA' : y ∈ A' := hT hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyA'
      rw [Nat.mul_div_cancel' (hdiv x hx)]
      exact hx
    have hUcard : ∀ T : Finset ℕ, (T.image (g * ·)).card = T.card := fun T =>
      Finset.card_image_of_injective T (fun x y h => Nat.eq_of_mul_eq_mul_left hg_pos h)
    have hUsum : ∀ T : Finset ℕ, ∑ u ∈ T.image (g * ·), u = g * ∑ y ∈ T, y := fun T => by
      rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hg_pos h), Finset.mul_sum]
    have hdisj := hadm hr hs hrs
    exact Set.disjoint_left.mp hdisj
      ⟨U₁, hUsub T₁ hT₁, by rw [hUcard, hc₁], by rw [hUsum, hs₁]⟩
      ⟨U₂, hUsub T₂ hT₂, by rw [hUcard, hc₂], by rw [hUsum, hs₂]⟩
  have hstraus := straus_bound hsub' hadm'
  rw [hcard] at hstraus
  have hNg : N / g ≤ N / 2 := Nat.div_le_div_left hg (by decide)
  have hN2 : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
  have hk_big : 200 ≤ A.card := by nlinarith
  nlinarith

theorem main : H1 → H2 → H3 → type_of% @Erdos875.erdos_875.variants.deshouillers_freiman := by
  intro h1 h2 h3
  obtain ⟨N₁, hN₁⟩ := h1
  obtain ⟨N₂, hN₂⟩ := h2
  refine ⟨max (max N₁ N₂) 2500, fun N hN A hAsub hAadm => ?_⟩
  have hN_N1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN_N2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN_2500 : 2500 ≤ N := le_trans (le_max_right _ _) hN
  by_contra hnot
  push Not at hnot
  have hgt_nat : 4 * N < A.card * (A.card + 2) := by
    have hsq : (2 * Real.sqrt ((N : ℝ) + 1 / 4)) ^ 2 < ((A.card : ℝ) + 1) ^ 2 := by
      have hpos : 0 ≤ 2 * Real.sqrt ((N : ℝ) + 1 / 4) := by positivity
      nlinarith only [hnot, hpos]
    have hrt : (2 * Real.sqrt ((N : ℝ) + 1 / 4)) ^ 2 = 4 * (N : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ (N : ℝ) + 1 / 4 := by positivity
      calc (2 * Real.sqrt ((N : ℝ) + 1 / 4)) ^ 2
        _ = 4 * (Real.sqrt ((N : ℝ) + 1 / 4)) ^ 2 := by ring
        _ = 4 * ((N : ℝ) + 1 / 4) := by rw [Real.sq_sqrt hnn]
        _ = 4 * (N : ℝ) + 1 := by ring
    have hreal : (4 * N : ℝ) < (A.card * (A.card + 2) : ℝ) := by
      nlinarith only [hsq, hrt]
    exact_mod_cast hreal
  obtain ⟨A', hA'sub, hA'gt, hA'le⟩ := exists_min_excess_subset hgt_nat
  have hA'Icc : (A' : Set ℕ) ⊆ Set.Icc 1 N := (Finset.coe_subset.mpr hA'sub).trans hAsub
  have hA'adm : IsAdmissible (A' : Set ℕ) := admissible_subset hA'sub hAadm
  have hgcd : ∀ g : ℕ, 2 ≤ g → ∃ a ∈ A', ¬ g ∣ a :=
    gcd_one_of_admissible (by omega) hA'Icc hA'adm hA'gt
  have hA'gt3 : 4 * N ≤ A'.card * (A'.card + 3) := by
    have hmul : A'.card * (A'.card + 2) ≤ A'.card * (A'.card + 3) :=
      Nat.mul_le_mul_left A'.card (by omega)
    omega
  have hA'gt100 : 100 * N ≤ A'.card * (25 * A'.card + 51) := by
    have heq : A'.card * (25 * A'.card + 51) = 25 * (A'.card * (A'.card + 2)) + A'.card := by ring
    omega
  have hprim : ∀ d : ℕ, 2 ≤ d → ∃ a ∈ A', ∃ b ∈ A', a % d ≠ b % d :=
    hN₁ N hN_N1 A' hA'Icc hA'adm hA'gt3 hgcd
  have hdiam : ∀ a ∈ A', ∀ b ∈ A', 20 * (b - a) ≤ 21 * A'.card :=
    hN₂ N hN_N2 A' hA'Icc hA'adm hA'gt100 hA'le hprim
  have hk_ge : 99 ≤ A'.card := by
    by_contra hlt
    have hle : A'.card * (A'.card + 2) ≤ 98 * 100 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hA'ne : A'.Nonempty := Finset.card_pos.mp (by omega)
  let a₁ := A'.min' hA'ne
  have ha₁_mem : a₁ ∈ A' := Finset.min'_mem A' hA'ne
  let B := A'.erase a₁
  have hB_card : B.card = A'.card - 1 := Finset.card_erase_of_mem ha₁_mem
  have hm_ge : 98 ≤ B.card := by omega
  have hB_ne : B.Nonempty := Finset.card_pos.mp (by omega)
  set m := B.card
  set r := m / 2
  set g := (B.max' hB_ne - B.min' hB_ne) - (m - 1)
  have hB_sub : B ⊆ A' := Finset.erase_subset a₁ A'
  have hg_bound : 10 * g ≤ m := by
    have hd := hdiam (B.min' hB_ne) (hB_sub (Finset.min'_mem B hB_ne))
      (B.max' hB_ne) (hB_sub (Finset.max'_mem B hB_ne))
    have hm1 : m + 1 = A'.card := by omega
    have hgap_le : B.max' hB_ne - B.min' hB_ne ≥ m - 1 := by
      have hsub_icc : B ⊆ Finset.Icc (B.min' hB_ne) (B.max' hB_ne) := fun x hx =>
        Finset.mem_Icc.mpr ⟨Finset.min'_le B x hx, Finset.le_max' B x hx⟩
      have hc := Finset.card_le_card hsub_icc
      rw [Nat.card_Icc] at hc
      have hminle : B.min' hB_ne ≤ B.max' hB_ne := Finset.min'_le B _ (Finset.max'_mem B hB_ne)
      omega
    omega
  -- Boundedness of S = S_r(B)
  let S := (B.powersetCard r).image (fun T => ∑ x ∈ T, x)
  have hr_le : r ≤ m := Nat.div_le_self m 2
  have hS_ne : S.Nonempty := (Finset.powersetCard_nonempty.mpr hr_le).image _
  let L := S.min' hS_ne
  let M := S.max' hS_ne
  have hLM_bounds : ∀ T ∈ B.powersetCard r, L ≤ ∑ x ∈ T, x ∧ ∑ x ∈ T, x ≤ M := by
    intro T hT
    have hmem : ∑ x ∈ T, x ∈ S := Finset.mem_image.mpr ⟨T, hT, rfl⟩
    exact ⟨Finset.min'_le S _ hmem, Finset.le_max' S _ hmem⟩
  have hL_ex : ∃ T ∈ B.powersetCard r, ∑ x ∈ T, x = L :=
    Finset.mem_image.mp (Finset.min'_mem S hS_ne)
  have hM_ex : ∃ T ∈ B.powersetCard r, ∑ x ∈ T, x = M :=
    Finset.mem_image.mp (Finset.max'_mem S hS_ne)
  have hholes : 2 * ((M - L + 1) - S.card) ≤ (M - L) - r * (m - r) + g :=
    h3 B hB_ne (by omega) L M hLM_bounds hL_ex hM_ex hg_bound
  -- Lower bound M - L ≥ r * (m - r)
  have hS_lb : r * (m - r) + 1 ≤ S.card := card_rSums_ge B r hr_le
  have hS_sub_icc : S ⊆ Finset.Icc L M := fun s hs =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le S s hs, Finset.le_max' S s hs⟩
  have hS_ub : S.card ≤ M - L + 1 := by
    have := Finset.card_le_card hS_sub_icc
    rw [Nat.card_Icc] at this
    have hLleM : L ≤ M := Finset.min'_le S M (Finset.max'_mem S hS_ne)
    omega
  have hspan_lb : r * (m - r) ≤ M - L := by omega
  -- Exact arithmetic bound: a₁ + g ≤ r * (m - r)
  have ha₁_lt : a₁ < B.min' hB_ne := by
    have hmemB : B.min' hB_ne ∈ B := Finset.min'_mem B hB_ne
    have hne : B.min' hB_ne ≠ a₁ := (Finset.mem_erase.mp hmemB).1
    have hle : a₁ ≤ B.min' hB_ne := Finset.min'_le A' _ (hB_sub hmemB)
    omega
  have hBmax_le : B.max' hB_ne ≤ N := (hA'Icc (hB_sub (Finset.max'_mem B hB_ne))).2
  have hgap_ge : m - 1 ≤ B.max' hB_ne - B.min' hB_ne := by
    have hsub_icc : B ⊆ Finset.Icc (B.min' hB_ne) (B.max' hB_ne) := fun x hx =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le B x hx, Finset.le_max' B x hx⟩
    have hc := Finset.card_le_card hsub_icc
    rw [Nat.card_Icc] at hc
    have hminle : B.min' hB_ne ≤ B.max' hB_ne := Finset.min'_le B _ (Finset.max'_mem B hB_ne)
    omega
  have ha1_m_g : a₁ + m + g ≤ N := by
    have hminle : B.min' hB_ne ≤ B.max' hB_ne := Finset.min'_le B _ (Finset.max'_mem B hB_ne)
    omega
  have hN_le : N ≤ r * (m - r) + m := by
    have hm1 : A'.card = m + 1 := by omega
    rw [hm1] at hA'gt
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hr_eq : r = t := by omega
      have hmr_eq : m - r = t := by omega
      rw [hmr_eq, hr_eq]
      have heq : (m + 1) * (m + 1 + 2) = 4 * (t * t + m) + 3 := by rw [ht]; ring
      omega
    · have hr_eq : r = t := by omega
      have hmr_eq : m - r = t + 1 := by omega
      rw [hmr_eq, hr_eq]
      have heq : (m + 1) * (m + 1 + 2) = 4 * (t * (t + 1) + m) + 4 := by rw [ht]; ring
      omega
  have ha1_g_le : a₁ + g ≤ r * (m - r) := by omega
  -- Pigeonhole difference collision: S and S.image (· + a₁) cannot be disjoint inside Icc L (M + a₁)
  have hcard_sum : M + a₁ - L + 1 < S.card + (S.image (· + a₁)).card := by
    have hinj : (S.image (· + a₁)).card = S.card :=
      Finset.card_image_of_injective S (fun x y h => by omega)
    have hLleM : L ≤ M := Finset.min'_le S M (Finset.max'_mem S hS_ne)
    rw [hinj]
    omega
  have hS_big : S ⊆ Finset.Icc L (M + a₁) := fun s hs => by
    have h := Finset.mem_Icc.mp (hS_sub_icc hs)
    exact Finset.mem_Icc.mpr ⟨h.1, by omega⟩
  have hSa_big : S.image (· + a₁) ⊆ Finset.Icc L (M + a₁) := fun s hs => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    have h := Finset.mem_Icc.mp (hS_sub_icc hx)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hnot_disj : ¬ Disjoint S (S.image (· + a₁)) := by
    intro hdisj
    have hu := Finset.card_le_card (Finset.union_subset hS_big hSa_big)
    rw [Finset.card_union_of_disjoint hdisj, Nat.card_Icc] at hu
    have hLleM : L ≤ M := Finset.min'_le S M (Finset.max'_mem S hS_ne)
    omega
  rw [Finset.not_disjoint_iff] at hnot_disj
  obtain ⟨y, hyS, hySa⟩ := hnot_disj
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hySa
  obtain ⟨T₁, hT₁, hsum₁⟩ := Finset.mem_image.mp hxS
  obtain ⟨T₂, hT₂, hsum₂⟩ := Finset.mem_image.mp hyS
  rw [Finset.mem_powersetCard] at hT₁ hT₂
  have ha₁_not_T₁ : a₁ ∉ T₁ := fun h => (Finset.mem_erase.mp (hT₁.1 h)).1 rfl
  have hr_pos : 1 ≤ r := by omega
  have hdisj_adm := hA'adm hr_pos (show 1 ≤ r + 1 by omega) (show r ≠ r + 1 by omega)
  exact Set.disjoint_left.mp hdisj_adm
    ⟨T₂, Finset.coe_subset.mpr (hT₂.1.trans hB_sub), hT₂.2, hsum₂⟩
    ⟨insert a₁ T₁,
      fun z hz => by
        rw [Finset.mem_coe] at hz ⊢
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact ha₁_mem
        · exact hB_sub (hT₁.1 hz'),
      by rw [Finset.card_insert_of_notMem ha₁_not_T₁, hT₁.2],
      by rw [Finset.sum_insert ha₁_not_T₁, hsum₁, Nat.add_comm]⟩

end OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1
