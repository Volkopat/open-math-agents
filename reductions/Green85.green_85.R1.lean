import FormalConjectures.GreensOpenProblems.«85»
import Mathlib.Tactic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Order.Preorder.Finite

/-!
Reduction of Green85 to the integer matrix problem of Carbery, Christ and
Wright, Multidimensional van der Corput and sublevel set estimates,
J. Amer. Math. Soc. 12 (1999), 981-1015, Problems 1.1 and 6.3,
DOI 10.1090/S0894-0347-99-00309-4 (refereed).

H1 retains the open bound for matrices with crossing row sets and a row hole.
The laminar row case is proved here with K=4, and interval rows with K=64,
using a radius/layer-cake argument, finite Cauchy-Schwarz and dyadic extraction.
These are known positive settings related to CCW Section 3.2.
H2 is standard inner grid
approximation. The analytic H2 is proved in our separate companion step source.
No new bound or solution of the open conjecture is claimed. The transfer uses
closed cells and gives constant 1/(4(K+64)) from the residual bound K. All code in this submission was written
for this run; no other agent's proof code or substantive note was used.
Credit: @MattGaiser.
-/

namespace OMA.R_Green85_green_85_R1

namespace D6Layer

open Finset

lemma sum_odds (n : ℕ) : ∑ k ∈ range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring

lemma sum_sq_eq_levels {ι : Type*} [DecidableEq ι] (R : Finset ι)
    (f : ι → ℕ) (W : ℕ) (hf : ∀ i ∈ R, f i ≤ W) :
    ∑ i ∈ R, f i ^ 2 =
      ∑ k ∈ range W, (2 * k + 1) * (R.filter fun i => k < f i).card := by
  classical
  calc
    ∑ i ∈ R, f i ^ 2 =
        ∑ i ∈ R, ∑ k ∈ range W, if k < f i then 2 * k + 1 else 0 := by
      apply sum_congr rfl
      intro i hi
      have hfi := hf i hi
      have hfilter : (range W).filter (fun k => k < f i) = range (f i) := by
        ext k
        simp only [mem_filter, mem_range]
        omega
      rw [← sum_filter, hfilter, sum_odds]
    _ = ∑ k ∈ range W, ∑ i ∈ R, if k < f i then 2 * k + 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      rw [← sum_filter]
      simp [mul_comm]

lemma sum_sq_le_of_level_counts {ι : Type*} [DecidableEq ι] (R : Finset ι)
    (f : ι → ℕ) (W M : ℕ) (hf : ∀ i ∈ R, f i ≤ W)
    (hc : ∀ k < W, (k + 1) * (R.filter fun i => k < f i).card ≤ 2 * M) :
    ∑ i ∈ R, f i ^ 2 ≤ 4 * M * W := by
  rw [sum_sq_eq_levels R f W hf]
  calc
    ∑ k ∈ range W, (2 * k + 1) * (R.filter fun i => k < f i).card
        ≤ ∑ _k ∈ range W, 4 * M := by
      apply sum_le_sum
      intro k hk
      have hcount := hc k (mem_range.mp hk)
      calc
        (2 * k + 1) * (R.filter fun i => k < f i).card
            ≤ (2 * (k + 1)) * (R.filter fun i => k < f i).card := by gcongr; omega
        _ = 2 * ((k + 1) * (R.filter fun i => k < f i).card) := by ring
        _ ≤ 2 * (2 * M) := Nat.mul_le_mul_left _ hcount
        _ = 4 * M := by ring
    _ = 4 * M * W := by simp [mul_comm]

lemma card_le_twice_radius (R : Finset ℕ) (r q : ℕ)
    (hR : ∀ i ∈ R, Nat.dist i r < q) : R.card ≤ 2 * q := by
  have hsub : R.image (fun i : ℕ => (i : ℤ)) ⊆
      Icc ((r : ℤ) - q + 1) ((r : ℤ) + q) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    have hd := hR i hi
    by_cases hir : i ≤ r
    · rw [Nat.dist_eq_sub_of_le hir] at hd
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [Nat.dist_eq_sub_of_le_right (by omega : r ≤ i)] at hd
      exact mem_Icc.mpr ⟨by omega, by omega⟩
  calc
    R.card = (R.image fun i : ℕ => (i : ℤ)).card :=
      (card_image_of_injective _ Nat.cast_injective).symm
    _ ≤ (Icc ((r : ℤ) - q + 1) ((r : ℤ) + q)).card := card_le_card hsub
    _ = 2 * q := by
      rw [Int.card_Icc]
      have heq : (r : ℤ) + q + 1 - ((r : ℤ) - q + 1) = ((2 * q : ℕ) : ℤ) := by
        push_cast
        ring
      rw [heq, Int.toNat_natCast]

lemma weighted_radius_count (R : Finset ℕ) (r k M : ℕ) (hk : 0 < k)
    (hR : ∀ i ∈ R, k * (Nat.dist i r + 1) ≤ M) : k * R.card ≤ 2 * M := by
  have hd : ∀ i ∈ R, Nat.dist i r < M / k := by
    intro i hi
    have h := (Nat.le_div_iff_mul_le hk).mpr (by simpa only [mul_comm] using hR i hi)
    omega
  calc
    k * R.card ≤ k * (2 * (M / k)) := Nat.mul_le_mul_left _ (card_le_twice_radius R r _ hd)
    _ = 2 * ((M / k) * k) := by ring
    _ ≤ 2 * M := Nat.mul_le_mul_left _ (Nat.div_mul_le_self M k)

lemma sum_sq_le_of_radius (R : Finset ℕ) (f : ℕ → ℕ) (r W M : ℕ)
    (hf : ∀ i ∈ R, f i ≤ W)
    (hb : ∀ i ∈ R, f i * (Nat.dist i r + 1) ≤ M) :
    ∑ i ∈ R, f i ^ 2 ≤ 4 * M * W := by
  apply sum_sq_le_of_level_counts R f W M hf
  intro k hk
  apply weighted_radius_count (R.filter fun i => k < f i) r (k + 1) M (by omega)
  intro i hi
  have hi' := mem_filter.mp hi
  exact le_trans (Nat.mul_le_mul_right _ (by omega : k + 1 ≤ f i)) (hb i hi'.1)

lemma sum_sq_laminar {α : Type*} [DecidableEq α] (R : Finset ℕ)
    (F : ℕ → Finset α) (U : Finset α) (M : ℕ)
    (hFU : ∀ i ∈ R, F i ⊆ U)
    (hlam : ∀ i ∈ R, ∀ j ∈ R,
      F i ⊆ F j ∨ F j ⊆ F i ∨ Disjoint (F i) (F j))
    (hb : ∀ i ∈ R, ∀ j ∈ R,
      (F i ∩ F j).card * (Nat.dist i j + 1) ≤ M) :
    ∑ i ∈ R, (F i).card ^ 2 ≤ 4 * M * U.card := by
  classical
  let T := R.image F
  let roots := T.filter fun A => ∀ B ∈ T, A ⊆ B → B ⊆ A
  have hroot_mem : ∀ A ∈ roots, A ∈ T := fun A hA => (mem_filter.mp hA).1
  have hroot_max : ∀ A ∈ roots, ∀ B ∈ T, A ⊆ B → B ⊆ A :=
    fun A hA => (mem_filter.mp hA).2
  have hroot_subset : ∀ A ∈ roots, A ⊆ U := by
    intro A hA
    obtain ⟨i, hi, rfl⟩ := mem_image.mp (hroot_mem A hA)
    exact hFU i hi
  have hroot_disj : ∀ A ∈ roots, ∀ B ∈ roots, A ≠ B → Disjoint A B := by
    intro A hA B hB hne
    obtain ⟨i, hi, hiA⟩ := mem_image.mp (hroot_mem A hA)
    obtain ⟨j, hj, hjB⟩ := mem_image.mp (hroot_mem B hB)
    rcases hlam i hi j hj with hij | hji | hd
    · have hAB : A ⊆ B := by simpa only [hiA, hjB] using hij
      exact (hne (Subset.antisymm hAB (hroot_max A hA B (hroot_mem B hB) hAB))).elim
    · have hBA : B ⊆ A := by simpa only [hiA, hjB] using hji
      exact (hne (Subset.antisymm (hroot_max B hB A (hroot_mem A hA) hBA) hBA)).elim
    · simpa only [hiA, hjB] using hd
  have hroot_card : ∑ A ∈ roots, A.card ≤ U.card := by
    have hsub : roots.biUnion id ⊆ U := by
      intro a ha
      obtain ⟨A, hA, haA⟩ := mem_biUnion.mp ha
      exact hroot_subset A hA haA
    rw [← card_biUnion]
    · exact card_le_card hsub
    · exact hroot_disj
  have hroot_bound : ∀ A ∈ roots,
      ∑ i ∈ R.filter (fun i => F i ⊆ A), (F i).card ^ 2 ≤ 4 * M * A.card := by
    intro A hA
    obtain ⟨r, hr, hrA⟩ := mem_image.mp (hroot_mem A hA)
    apply sum_sq_le_of_radius (R.filter fun i => F i ⊆ A)
      (fun i => (F i).card) r A.card M
    · intro i hi
      exact card_le_card (mem_filter.mp hi).2
    · intro i hi
      have hip := mem_filter.mp hi
      have hsub : F i ⊆ F r := by simpa only [hrA] using hip.2
      simpa only [inter_eq_left.mpr hsub] using hb i hip.1 r hr
  have hcover : ∀ i ∈ R, ∃ A ∈ roots, F i ⊆ A := by
    intro i hi
    obtain ⟨A, hiA, hmax⟩ := T.exists_le_maximal (mem_image_of_mem F hi)
    exact ⟨A, mem_filter.mpr ⟨hmax.1, fun B hB hAB => hmax.2 hB hAB⟩, hiA⟩
  calc
    ∑ i ∈ R, (F i).card ^ 2
        ≤ ∑ i ∈ R, ∑ A ∈ roots, if F i ⊆ A then (F i).card ^ 2 else 0 := by
      apply sum_le_sum
      intro i hi
      obtain ⟨A, hA, hiA⟩ := hcover i hi
      have hle := single_le_sum (s := roots)
        (f := fun B => if F i ⊆ B then (F i).card ^ 2 else 0)
        (fun _ _ => Nat.zero_le _) hA
      simpa only [if_pos hiA] using hle
    _ = ∑ A ∈ roots, ∑ i ∈ R.filter (fun i => F i ⊆ A), (F i).card ^ 2 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro A hA
      exact (sum_filter _ _).symm
    _ ≤ ∑ A ∈ roots, 4 * M * A.card := sum_le_sum hroot_bound
    _ = 4 * M * ∑ A ∈ roots, A.card := by rw [mul_sum]
    _ ≤ 4 * M * U.card := Nat.mul_le_mul_left _ hroot_card

lemma sq_sum_laminar {α : Type*} [DecidableEq α] (R : Finset ℕ)
    (F : ℕ → Finset α) (U : Finset α) (M : ℕ)
    (hFU : ∀ i ∈ R, F i ⊆ U)
    (hlam : ∀ i ∈ R, ∀ j ∈ R,
      F i ⊆ F j ∨ F j ⊆ F i ∨ Disjoint (F i) (F j))
    (hb : ∀ i ∈ R, ∀ j ∈ R,
      (F i ∩ F j).card * (Nat.dist i j + 1) ≤ M) :
    (∑ i ∈ R, (F i).card) ^ 2 ≤ 4 * M * R.card * U.card := by
  calc
    (∑ i ∈ R, (F i).card) ^ 2 ≤ R.card * ∑ i ∈ R, (F i).card ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ R.card * (4 * M * U.card) :=
      Nat.mul_le_mul_left _ (sum_sq_laminar R F U M hFU hlam hb)
    _ = _ := by ring

end D6Layer

namespace D6Grid

open Finset

lemma card_le_span (S : Finset ℕ) (hS : S.Nonempty) :
    S.card ≤ S.max' hS - S.min' hS + 1 := by
  have hsub : S ⊆ Icc (S.min' hS) (S.max' hS) := by
    intro x hx
    exact mem_Icc.mpr ⟨min'_le S x hx, le_max' S x hx⟩
  have hcard := card_le_card hsub
  have hminmax : S.min' hS ≤ S.max' hS := min'_le S _ (max'_mem S hS)
  rw [Nat.card_Icc] at hcard
  omega

lemma row_intersection_bound (N : ℕ) (S : Finset (ℕ × ℕ)) (i j M : ℕ)
    (hM : ∀ p ∈ S, ∀ q ∈ S, (p.1, q.2) ∈ S → (q.1, p.2) ∈ S →
      (Nat.dist p.1 q.1 + 1) * (Nat.dist p.2 q.2 + 1) ≤ M) :
    ((range N).filter (fun x => (i, x) ∈ S) ∩
      (range N).filter (fun x => (j, x) ∈ S)).card * (Nat.dist i j + 1) ≤ M := by
  classical
  let C := (range N).filter (fun x => (i, x) ∈ S) ∩
    (range N).filter (fun x => (j, x) ∈ S)
  change C.card * (Nat.dist i j + 1) ≤ M
  by_cases hC : C.Nonempty
  · have hmin := min'_mem C hC
    have hmax := max'_mem C hC
    have himin : (i, C.min' hC) ∈ S := (mem_filter.mp (mem_inter.mp hmin).1).2
    have hjmin : (j, C.min' hC) ∈ S := (mem_filter.mp (mem_inter.mp hmin).2).2
    have himax : (i, C.max' hC) ∈ S := (mem_filter.mp (mem_inter.mp hmax).1).2
    have hjmax : (j, C.max' hC) ∈ S := (mem_filter.mp (mem_inter.mp hmax).2).2
    have hminmax : C.min' hC ≤ C.max' hC := min'_le C _ hmax
    have hspan := card_le_span C hC
    calc
      C.card * (Nat.dist i j + 1)
          ≤ (C.max' hC - C.min' hC + 1) * (Nat.dist i j + 1) :=
        Nat.mul_le_mul_right _ hspan
      _ = (Nat.dist i j + 1) * (Nat.dist (C.min' hC) (C.max' hC) + 1) := by
        rw [Nat.dist_eq_sub_of_le hminmax]
        ring
      _ ≤ M := hM (i, C.min' hC) himin (j, C.max' hC) hjmax himax hjmin
  · have hz : C = ∅ := not_nonempty_iff_eq_empty.mp hC
    simp only [hz, card_empty, zero_mul, Nat.zero_le]

lemma grid_card_eq_rows (N : ℕ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ range N ×ˢ range N) :
    S.card = ∑ i ∈ range N, ((range N).filter fun j => (i, j) ∈ S).card := by
  classical
  have hfiber (i : ℕ) : (S.filter fun p => p.1 = i).card =
      ((range N).filter fun j => (i, j) ∈ S).card := by
    refine card_bij (fun p _ => p.2) ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      have hp' := mem_filter.mp hp
      have ha : a = i := hp'.2
      subst a
      exact mem_filter.mpr ⟨(mem_product.mp (hS hp'.1)).2, hp'.1⟩
    · intro p hp q hq heq
      exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) heq
    · intro j hj
      exact ⟨(i, j), mem_filter.mpr ⟨(mem_filter.mp hj).2, rfl⟩, rfl⟩
  calc
    S.card = ∑ i ∈ range N, (S.filter fun p => p.1 = i).card :=
      card_eq_sum_card_fiberwise fun p hp => (mem_product.mp (hS hp)).1
    _ = _ := sum_congr rfl fun i _ => hfiber i

lemma laminar_matrix_bound (N M : ℕ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ range N ×ˢ range N)
    (hlam : ∀ i ∈ range N, ∀ j ∈ range N,
      ((range N).filter fun x => (i, x) ∈ S) ⊆ ((range N).filter fun x => (j, x) ∈ S) ∨
      ((range N).filter fun x => (j, x) ∈ S) ⊆ ((range N).filter fun x => (i, x) ∈ S) ∨
      Disjoint ((range N).filter fun x => (i, x) ∈ S)
        ((range N).filter fun x => (j, x) ∈ S))
    (hM : ∀ p ∈ S, ∀ q ∈ S, (p.1, q.2) ∈ S → (q.1, p.2) ∈ S →
      (Nat.dist p.1 q.1 + 1) * (Nat.dist p.2 q.2 + 1) ≤ M) :
    S.card ^ 2 ≤ 4 * M * N ^ 2 := by
  classical
  have hbound := D6Layer.sq_sum_laminar (range N)
    (fun i => (range N).filter fun x => (i, x) ∈ S) (range N) M
    (fun i _ => filter_subset _ _) hlam
    (fun i _ j _ => row_intersection_bound N S i j M hM)
  rw [← grid_card_eq_rows N S hS, card_range] at hbound
  convert hbound using 1
  ring

lemma normalized_corners (S : Finset (ℕ × ℕ)) (p q : ℕ × ℕ)
    (hp : p ∈ S) (hq : q ∈ S) (hpq : (p.1, q.2) ∈ S) (hqp : (q.1, p.2) ∈ S) :
    (min p.1 q.1, min p.2 q.2) ∈ S ∧
    (max p.1 q.1, min p.2 q.2) ∈ S ∧
    (max p.1 q.1, max p.2 q.2) ∈ S ∧
    (min p.1 q.1, max p.2 q.2) ∈ S := by
  rcases le_total p.1 q.1 with hi | hi <;> rcases le_total p.2 q.2 with hj | hj
  · simpa only [min_eq_left hi, max_eq_right hi, min_eq_left hj, max_eq_right hj]
      using And.intro hp (And.intro hqp (And.intro hq hpq))
  · simpa only [min_eq_left hi, max_eq_right hi, min_eq_right hj, max_eq_left hj]
      using And.intro hpq (And.intro hq (And.intro hqp hp))
  · simpa only [min_eq_right hi, max_eq_left hi, min_eq_left hj, max_eq_right hj]
      using And.intro hqp (And.intro hp (And.intro hpq hq))
  · simpa only [min_eq_right hi, max_eq_left hi, min_eq_right hj, max_eq_left hj]
      using And.intro hq (And.intro hpq (And.intro hp hqp))

lemma laminar_grid_bound (N : ℕ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ range N ×ˢ range N) (hne : S.Nonempty)
    (hlam : ∀ i ∈ range N, ∀ j ∈ range N,
      ((range N).filter fun x => (i, x) ∈ S) ⊆ ((range N).filter fun x => (j, x) ∈ S) ∨
      ((range N).filter fun x => (j, x) ∈ S) ⊆ ((range N).filter fun x => (i, x) ∈ S) ∨
      Disjoint ((range N).filter fun x => (i, x) ∈ S)
        ((range N).filter fun x => (j, x) ∈ S)) :
    ∃ i₁ i₂ j₁ j₂ : ℕ, i₁ ≤ i₂ ∧ j₁ ≤ j₂ ∧
      (i₁, j₁) ∈ S ∧ (i₂, j₁) ∈ S ∧ (i₂, j₂) ∈ S ∧ (i₁, j₂) ∈ S ∧
      S.card ^ 2 ≤ 4 * N ^ 2 * (i₂ - i₁ + 1) * (j₂ - j₁ + 1) := by
  classical
  let Q := (S ×ˢ S).filter fun pq => (pq.1.1, pq.2.2) ∈ S ∧ (pq.2.1, pq.1.2) ∈ S
  let w : (ℕ × ℕ) × (ℕ × ℕ) → ℕ := fun pq =>
    (Nat.dist pq.1.1 pq.2.1 + 1) * (Nat.dist pq.1.2 pq.2.2 + 1)
  have hQ : Q.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨(p, p), mem_filter.mpr ⟨mem_product.mpr ⟨hp, hp⟩, hp, hp⟩⟩
  obtain ⟨⟨p, q⟩, hpq, hmax⟩ := Q.exists_max_image w hQ
  have hM : ∀ a ∈ S, ∀ b ∈ S, (a.1, b.2) ∈ S → (b.1, a.2) ∈ S →
      (Nat.dist a.1 b.1 + 1) * (Nat.dist a.2 b.2 + 1) ≤ w (p, q) := by
    intro a ha b hb hab hba
    exact hmax (a, b) (mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩, hab, hba⟩)
  have hb := laminar_matrix_bound N (w (p, q)) S hS hlam hM
  have hpq' := mem_filter.mp hpq
  have hp := (mem_product.mp hpq'.1).1
  have hq := (mem_product.mp hpq'.1).2
  obtain ⟨h11, h21, h22, h12⟩ := normalized_corners S p q hp hq hpq'.2.1 hpq'.2.2
  refine ⟨min p.1 q.1, max p.1 q.1, min p.2 q.2, max p.2 q.2,
    min_le_max, min_le_max, h11, h21, h22, h12, ?_⟩
  calc
    S.card ^ 2 ≤ 4 * w (p, q) * N ^ 2 := hb
    _ = _ := by
      dsimp only [w]
      rw [Nat.dist_eq_max_sub_min, Nat.dist_eq_max_sub_min]
      ring

end D6Grid


namespace D6Dyadic

open Finset

lemma mem_block_iff {x d m : ℕ} (hd : 0 < d) :
    x ∈ Ico (m * d) ((m + 1) * d) ↔ x / d = m := by
  rw [mem_Ico, Nat.div_eq_iff hd]
  rw [add_mul, one_mul]
  omega

lemma block_subset_or_disjoint_of_dvd (d D m n : ℕ) (hd : 0 < d) (hD : 0 < D)
    (hdiv : d ∣ D) :
    Ico (m * d) ((m + 1) * d) ⊆ Ico (n * D) ((n + 1) * D) ∨
      Disjoint (Ico (m * d) ((m + 1) * d)) (Ico (n * D) ((n + 1) * D)) := by
  by_cases hdisj : Disjoint (Ico (m * d) ((m + 1) * d)) (Ico (n * D) ((n + 1) * D))
  · exact Or.inr hdisj
  · left
    obtain ⟨x, hx, hx'⟩ := not_disjoint_iff.mp hdisj
    obtain ⟨t, ht⟩ := hdiv
    intro y hy
    apply (mem_block_iff hD).mpr
    have hxsmall := (mem_block_iff hd).mp hx
    have hysmall := (mem_block_iff hd).mp hy
    have hxbig := (mem_block_iff hD).mp hx'
    calc
      y / D = (y / d) / t := by rw [ht, Nat.div_div_eq_div_mul]
      _ = (x / d) / t := by rw [hxsmall, hysmall]
      _ = x / D := by rw [ht, Nat.div_div_eq_div_mul]
      _ = n := hxbig

lemma dyadic_blocks_laminar (k l m n : ℕ) :
    Ico (m * 2 ^ k) ((m + 1) * 2 ^ k) ⊆ Ico (n * 2 ^ l) ((n + 1) * 2 ^ l) ∨
    Ico (n * 2 ^ l) ((n + 1) * 2 ^ l) ⊆ Ico (m * 2 ^ k) ((m + 1) * 2 ^ k) ∨
    Disjoint (Ico (m * 2 ^ k) ((m + 1) * 2 ^ k))
      (Ico (n * 2 ^ l) ((n + 1) * 2 ^ l)) := by
  rcases le_total k l with hkl | hlk
  · rcases block_subset_or_disjoint_of_dvd (2 ^ k) (2 ^ l) m n
      (by positivity) (by positivity) (Nat.pow_dvd_pow 2 hkl) with hsub | hd
    · exact Or.inl hsub
    · exact Or.inr (Or.inr hd)
  · rcases block_subset_or_disjoint_of_dvd (2 ^ l) (2 ^ k) n m
      (by positivity) (by positivity) (Nat.pow_dvd_pow 2 hlk) with hsub | hd
    · exact Or.inr (Or.inl hsub)
    · exact Or.inr (Or.inr hd.symm)

lemma dyadic_block_card (k m : ℕ) :
    (Ico (m * 2 ^ k) ((m + 1) * 2 ^ k)).card = 2 ^ k := by
  simp [Nat.card_Ico, add_mul]

lemma exists_dyadic_subinterval (a b : ℕ) (hab : a < b) :
    ∃ k m : ℕ, Ico (m * 2 ^ k) ((m + 1) * 2 ^ k) ⊆ Ico a b ∧
      b - a ≤ 4 * 2 ^ k := by
  let L := b - a
  have hL : 0 < L := by dsimp [L]; omega
  by_cases hLone : L = 1
  · refine ⟨0, a, ?_, ?_⟩
    · intro x hx
      simp only [pow_zero, mul_one, mem_Ico] at hx ⊢
      exact ⟨hx.1, by dsimp [L] at hLone; omega⟩
    · dsimp [L] at hLone
      simpa only [hLone, pow_zero, mul_one] using (by decide : 1 ≤ 4)
  · have hLtwo : 2 ≤ L := by omega
    let k := Nat.log 2 L - 1
    let d := 2 ^ k
    have hd : 0 < d := by dsimp [d]; positivity
    have hlogpos : 0 < Nat.log 2 L := Nat.log_pos (by decide) hLtwo
    have hk : k + 1 = Nat.log 2 L := by dsimp [k]; omega
    have hpow : 2 ^ Nat.log 2 L = 2 * d := by
      rw [← hk, pow_succ]
      dsimp only [d]
      ring
    have htwod : 2 * d ≤ L := by
      rw [← hpow]
      exact Nat.pow_log_le_self 2 (by omega)
    have hfour : L < 4 * d := by
      have ht := Nat.lt_pow_succ_log_self (by decide : 1 < 2) L
      rw [pow_succ, hpow] at ht
      nlinarith
    let m := a / d + 1
    have hlo : a ≤ m * d := by
      have hh := Nat.lt_mul_div_succ a hd
      dsimp only [m]
      nlinarith
    have hlen : a + 2 * d ≤ b := by dsimp [L] at htwod; omega
    have hhi : (m + 1) * d ≤ b := by
      have hh := Nat.div_mul_le_self a d
      dsimp only [m]
      nlinarith
    refine ⟨k, m, ?_, ?_⟩
    · intro x hx
      exact mem_Ico.mpr ⟨hlo.trans (mem_Ico.mp hx).1, (mem_Ico.mp hx).2.trans_le hhi⟩
    · exact hfour.le

end D6Dyadic

namespace D6Interval

open Finset

lemma exists_dyadic_subset (F : Finset ℕ)
    (hc : ∀ a ∈ F, ∀ b ∈ F, ∀ x : ℕ, a ≤ x → x ≤ b → x ∈ F) :
    ∃ G : Finset ℕ, G ⊆ F ∧ F.card ≤ 4 * G.card ∧
      (G = ∅ ∨ ∃ k m : ℕ, G = Ico (m * 2 ^ k) ((m + 1) * 2 ^ k)) := by
  classical
  by_cases hF : F.Nonempty
  · let a := F.min' hF
    let b := F.max' hF + 1
    have hmin := min'_mem F hF
    have hmax := max'_mem F hF
    have hab : a < b := by
      have hh := min'_le F _ hmax
      dsimp only [a, b]
      omega
    have heq : F = Ico a b := by
      ext x
      constructor
      · intro hx
        exact mem_Ico.mpr ⟨min'_le F _ hx, by
          have hh := le_max' F x hx
          dsimp only [b]
          omega⟩
      · intro hx
        have hh := mem_Ico.mp hx
        exact hc _ hmin _ hmax x hh.1 (by dsimp only [b] at hh; omega)
    obtain ⟨k, m, hsub, hcard⟩ := D6Dyadic.exists_dyadic_subinterval a b hab
    refine ⟨Ico (m * 2 ^ k) ((m + 1) * 2 ^ k), ?_, ?_, Or.inr ⟨k, m, rfl⟩⟩
    · rw [heq]
      exact hsub
    · rw [D6Dyadic.dyadic_block_card, heq, Nat.card_Ico]
      exact hcard
  · have hz : F = ∅ := not_nonempty_iff_eq_empty.mp hF
    subst F
    exact ⟨∅, subset_rfl, by simp, Or.inl rfl⟩

lemma sq_sum_interval_rows (R : Finset ℕ) (F : ℕ → Finset ℕ) (U : Finset ℕ) (M : ℕ)
    (hFU : ∀ i ∈ R, F i ⊆ U)
    (hc : ∀ i ∈ R, ∀ a ∈ F i, ∀ b ∈ F i, ∀ x : ℕ, a ≤ x → x ≤ b → x ∈ F i)
    (hb : ∀ i ∈ R, ∀ j ∈ R,
      (F i ∩ F j).card * (Nat.dist i j + 1) ≤ M) :
    (∑ i ∈ R, (F i).card) ^ 2 ≤ 64 * M * R.card * U.card := by
  classical
  have hex : ∀ i : ℕ, ∃ G : Finset ℕ,
      (i ∈ R → G ⊆ F i ∧ (F i).card ≤ 4 * G.card) ∧
      (G = ∅ ∨ ∃ k m : ℕ, G = Ico (m * 2 ^ k) ((m + 1) * 2 ^ k)) := by
    intro i
    by_cases hi : i ∈ R
    · obtain ⟨G, hsub, hcard, hshape⟩ := exists_dyadic_subset (F i) (hc i hi)
      exact ⟨G, fun _ => ⟨hsub, hcard⟩, hshape⟩
    · exact ⟨∅, fun h => (hi h).elim, Or.inl rfl⟩
  choose G hG hshape using hex
  have hlam : ∀ i ∈ R, ∀ j ∈ R,
      G i ⊆ G j ∨ G j ⊆ G i ∨ Disjoint (G i) (G j) := by
    intro i hi j hj
    rcases hshape i with hiz | ⟨k, m, hik⟩
    · exact Or.inl (hiz ▸ empty_subset _)
    rcases hshape j with hjz | ⟨l, n, hjl⟩
    · exact Or.inr (Or.inl (hjz ▸ empty_subset _))
    simpa only [hik, hjl] using D6Dyadic.dyadic_blocks_laminar k l m n
  have hGU : ∀ i ∈ R, G i ⊆ U := fun i hi => ((hG i hi).1).trans (hFU i hi)
  have hGb : ∀ i ∈ R, ∀ j ∈ R,
      (G i ∩ G j).card * (Nat.dist i j + 1) ≤ M := by
    intro i hi j hj
    have hsub : G i ∩ G j ⊆ F i ∩ F j := inter_subset_inter (hG i hi).1 (hG j hj).1
    exact (Nat.mul_le_mul_right _ (card_le_card hsub)).trans (hb i hi j hj)
  have hsq := D6Layer.sq_sum_laminar R G U M hGU hlam hGb
  have hsum : ∑ i ∈ R, (F i).card ≤ 4 * ∑ i ∈ R, (G i).card := by
    calc
      ∑ i ∈ R, (F i).card ≤ ∑ i ∈ R, 4 * (G i).card :=
        sum_le_sum fun i hi => (hG i hi).2
      _ = _ := (mul_sum ..).symm
  calc
    (∑ i ∈ R, (F i).card) ^ 2 ≤ (4 * ∑ i ∈ R, (G i).card) ^ 2 :=
      Nat.pow_le_pow_left hsum 2
    _ = 16 * (∑ i ∈ R, (G i).card) ^ 2 := by ring
    _ ≤ 16 * (4 * M * R.card * U.card) := Nat.mul_le_mul_left _ hsq
    _ = _ := by ring

lemma interval_matrix_bound (N M : ℕ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ range N ×ˢ range N)
    (hc : ∀ i ∈ range N, ∀ a b x : ℕ,
      (i, a) ∈ S → (i, b) ∈ S → a ≤ x → x ≤ b → (i, x) ∈ S)
    (hM : ∀ p ∈ S, ∀ q ∈ S, (p.1, q.2) ∈ S → (q.1, p.2) ∈ S →
      (Nat.dist p.1 q.1 + 1) * (Nat.dist p.2 q.2 + 1) ≤ M) :
    S.card ^ 2 ≤ 64 * M * N ^ 2 := by
  classical
  have hconv : ∀ i ∈ range N, ∀ a ∈ (range N).filter (fun x => (i, x) ∈ S),
      ∀ b ∈ (range N).filter (fun x => (i, x) ∈ S), ∀ x : ℕ,
      a ≤ x → x ≤ b → x ∈ (range N).filter (fun x => (i, x) ∈ S) := by
    intro i hi a ha b hb x hax hxb
    have ha' := mem_filter.mp ha
    have hb' := mem_filter.mp hb
    exact mem_filter.mpr ⟨mem_range.mpr (hxb.trans_lt (mem_range.mp hb'.1)),
      hc i hi a b x ha'.2 hb'.2 hax hxb⟩
  have hbound := sq_sum_interval_rows (range N)
    (fun i => (range N).filter fun x => (i, x) ∈ S) (range N) M
    (fun i _ => filter_subset _ _) hconv
    (fun i _ j _ => D6Grid.row_intersection_bound N S i j M hM)
  rw [← D6Grid.grid_card_eq_rows N S hS, card_range] at hbound
  convert hbound using 1
  ring

lemma interval_grid_bound (N : ℕ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ range N ×ˢ range N) (hne : S.Nonempty)
    (hc : ∀ i ∈ range N, ∀ a b x : ℕ,
      (i, a) ∈ S → (i, b) ∈ S → a ≤ x → x ≤ b → (i, x) ∈ S) :
    ∃ i₁ i₂ j₁ j₂ : ℕ, i₁ ≤ i₂ ∧ j₁ ≤ j₂ ∧
      (i₁, j₁) ∈ S ∧ (i₂, j₁) ∈ S ∧ (i₂, j₂) ∈ S ∧ (i₁, j₂) ∈ S ∧
      S.card ^ 2 ≤ 64 * N ^ 2 * (i₂ - i₁ + 1) * (j₂ - j₁ + 1) := by
  classical
  let Q := (S ×ˢ S).filter fun pq => (pq.1.1, pq.2.2) ∈ S ∧ (pq.2.1, pq.1.2) ∈ S
  let w : (ℕ × ℕ) × (ℕ × ℕ) → ℕ := fun pq =>
    (Nat.dist pq.1.1 pq.2.1 + 1) * (Nat.dist pq.1.2 pq.2.2 + 1)
  have hQ : Q.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨(p, p), mem_filter.mpr ⟨mem_product.mpr ⟨hp, hp⟩, hp, hp⟩⟩
  obtain ⟨⟨p, q⟩, hpq, hmax⟩ := Q.exists_max_image w hQ
  have hM : ∀ a ∈ S, ∀ b ∈ S, (a.1, b.2) ∈ S → (b.1, a.2) ∈ S →
      (Nat.dist a.1 b.1 + 1) * (Nat.dist a.2 b.2 + 1) ≤ w (p, q) := by
    intro a ha b hb hab hba
    exact hmax (a, b) (mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩, hab, hba⟩)
  have hb := interval_matrix_bound N (w (p, q)) S hS hc hM
  have hpq' := mem_filter.mp hpq
  have hp := (mem_product.mp hpq'.1).1
  have hq := (mem_product.mp hpq'.1).2
  obtain ⟨h11, h21, h22, h12⟩ := D6Grid.normalized_corners S p q hp hq hpq'.2.1 hpq'.2.2
  refine ⟨min p.1 q.1, max p.1 q.1, min p.2 q.2, max p.2 q.2,
    min_le_max, min_le_max, h11, h21, h22, h12, ?_⟩
  calc
    S.card ^ 2 ≤ 64 * w (p, q) * N ^ 2 := hb
    _ = _ := by
      dsimp only [w]
      rw [Nat.dist_eq_max_sub_min, Nat.dist_eq_max_sub_min]
      ring


end D6Interval

open Set MeasureTheory

def H1 : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∀ N : ℕ, 0 < N → ∀ S : Finset (ℕ × ℕ),
    S.Nonempty → S ⊆ Finset.range N ×ˢ Finset.range N →
    (∃ i ∈ Finset.range N, ∃ j ∈ Finset.range N,
      ¬ ((Finset.range N).filter fun x => (i, x) ∈ S) ⊆ ((Finset.range N).filter fun x => (j, x) ∈ S) ∧
      ¬ ((Finset.range N).filter fun x => (j, x) ∈ S) ⊆ ((Finset.range N).filter fun x => (i, x) ∈ S) ∧
      ¬ Disjoint ((Finset.range N).filter fun x => (i, x) ∈ S) ((Finset.range N).filter fun x => (j, x) ∈ S)) →
    (∃ i ∈ Finset.range N, ∃ a b x : ℕ,
      (i, a) ∈ S ∧ (i, b) ∈ S ∧ a ≤ x ∧ x ≤ b ∧ (i, x) ∉ S) →
    ∃ i₁ i₂ j₁ j₂ : ℕ, i₁ ≤ i₂ ∧ j₁ ≤ j₂ ∧
      (i₁, j₁) ∈ S ∧ (i₂, j₁) ∈ S ∧ (i₂, j₂) ∈ S ∧ (i₁, j₂) ∈ S ∧
      S.card ^ 2 ≤ K * N ^ 2 * (i₂ - i₁ + 1) * (j₂ - j₁ + 1)

def H2 : Prop :=
  ∀ A : Set (ℝ × ℝ), IsOpen A →
    A ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 →
    ∀ r : ℝ, 0 ≤ r → r < (volume A).toReal →
    ∃ N : ℕ, 0 < N ∧ ∃ S : Finset (ℕ × ℕ),
      S ⊆ Finset.range N ×ˢ Finset.range N ∧
      (∀ ij ∈ S, Icc ((ij.1 : ℝ) / N) (((ij.1 : ℝ) + 1) / N) ×ˢ
        Icc ((ij.2 : ℝ) / N) (((ij.2 : ℝ) + 1) / N) ⊆ A) ∧
      r ≤ (S.card : ℝ) / (N : ℝ) ^ 2

lemma integer_grid_bound (h : H1) :
  ∃ K : ℕ, 0 < K ∧ ∀ N : ℕ, 0 < N → ∀ S : Finset (ℕ × ℕ),
    S.Nonempty → S ⊆ Finset.range N ×ˢ Finset.range N →
    ∃ i₁ i₂ j₁ j₂ : ℕ, i₁ ≤ i₂ ∧ j₁ ≤ j₂ ∧
      (i₁, j₁) ∈ S ∧ (i₂, j₁) ∈ S ∧ (i₂, j₂) ∈ S ∧ (i₁, j₂) ∈ S ∧
      S.card ^ 2 ≤ K * N ^ 2 * (i₂ - i₁ + 1) * (j₂ - j₁ + 1) := by
  classical
  obtain ⟨K, hK, hgrid⟩ := h
  refine ⟨K + 64, by omega, ?_⟩
  intro N hN S hne hsub
  by_cases hlam : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N,
      ((Finset.range N).filter fun x => (i, x) ∈ S) ⊆ ((Finset.range N).filter fun x => (j, x) ∈ S) ∨
      ((Finset.range N).filter fun x => (j, x) ∈ S) ⊆ ((Finset.range N).filter fun x => (i, x) ∈ S) ∨
      Disjoint ((Finset.range N).filter fun x => (i, x) ∈ S) ((Finset.range N).filter fun x => (j, x) ∈ S)
  · obtain ⟨i₁, i₂, j₁, j₂, hi, hj, h11, h21, h22, h12, hb⟩ :=
      D6Grid.laminar_grid_bound N S hsub hne hlam
    refine ⟨i₁, i₂, j₁, j₂, hi, hj, h11, h21, h22, h12, hb.trans ?_⟩
    gcongr
    omega
  · by_cases hc : ∀ i ∈ Finset.range N, ∀ a b x : ℕ,
        (i, a) ∈ S → (i, b) ∈ S → a ≤ x → x ≤ b → (i, x) ∈ S
    · obtain ⟨i₁, i₂, j₁, j₂, hi, hj, h11, h21, h22, h12, hb⟩ :=
        D6Interval.interval_grid_bound N S hsub hne hc
      refine ⟨i₁, i₂, j₁, j₂, hi, hj, h11, h21, h22, h12, hb.trans ?_⟩
      gcongr
      omega
    · have hcross : ∃ i ∈ Finset.range N, ∃ j ∈ Finset.range N,
          ¬ ((Finset.range N).filter fun x => (i, x) ∈ S) ⊆ ((Finset.range N).filter fun x => (j, x) ∈ S) ∧
          ¬ ((Finset.range N).filter fun x => (j, x) ∈ S) ⊆ ((Finset.range N).filter fun x => (i, x) ∈ S) ∧
          ¬ Disjoint ((Finset.range N).filter fun x => (i, x) ∈ S) ((Finset.range N).filter fun x => (j, x) ∈ S) := by
        by_contra hnone
        apply hlam
        intro i hi j hj
        by_cases hij : ((Finset.range N).filter fun x => (i, x) ∈ S) ⊆ ((Finset.range N).filter fun x => (j, x) ∈ S)
        · exact Or.inl hij
        by_cases hji : ((Finset.range N).filter fun x => (j, x) ∈ S) ⊆ ((Finset.range N).filter fun x => (i, x) ∈ S)
        · exact Or.inr (Or.inl hji)
        apply Or.inr ∘ Or.inr
        by_contra hd
        exact hnone ⟨i, hi, j, hj, hij, hji, hd⟩
      push Not at hc
      obtain ⟨i₁, i₂, j₁, j₂, hi, hj, h11, h21, h22, h12, hb⟩ :=
        hgrid N hN S hne hsub hcross hc
      refine ⟨i₁, i₂, j₁, j₂, hi, hj, h11, h21, h22, h12, hb.trans ?_⟩
      gcongr
      omega

lemma grid_rectangle {A : Set (ℝ × ℝ)} (N : ℕ) (hN : 0 < N)
    (i₁ i₂ j₁ j₂ : ℕ) (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂)
    (h11 : Icc ((i₁ : ℝ) / N) (((i₁ : ℝ) + 1) / N) ×ˢ
      Icc ((j₁ : ℝ) / N) (((j₁ : ℝ) + 1) / N) ⊆ A)
    (h21 : Icc ((i₂ : ℝ) / N) (((i₂ : ℝ) + 1) / N) ×ˢ
      Icc ((j₁ : ℝ) / N) (((j₁ : ℝ) + 1) / N) ⊆ A)
    (h22 : Icc ((i₂ : ℝ) / N) (((i₂ : ℝ) + 1) / N) ×ˢ
      Icc ((j₂ : ℝ) / N) (((j₂ : ℝ) + 1) / N) ⊆ A)
    (h12 : Icc ((i₁ : ℝ) / N) (((i₁ : ℝ) + 1) / N) ×ˢ
      Icc ((j₂ : ℝ) / N) (((j₂ : ℝ) + 1) / N) ⊆ A) :
    ∃ x₁ x₂ y₁ y₂ : ℝ,
      {(x₁, y₁), (x₂, y₁), (x₂, y₂), (x₁, y₂)} ⊆ A ∧
      (((i₂ : ℝ) - i₁ + 1) * ((j₂ : ℝ) - j₁ + 1)) / (N : ℝ) ^ 2 =
        |x₁ - x₂| * |y₁ - y₂| := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have haxis (i : ℕ) : (i : ℝ) / N ≤ ((i : ℝ) + 1) / N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    linarith
  refine ⟨(i₁ : ℝ) / N, ((i₂ : ℝ) + 1) / N,
    (j₁ : ℝ) / N, ((j₂ : ℝ) + 1) / N, ?_, ?_⟩
  · intro p hp
    simp only [mem_insert_iff, mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h11 ⟨⟨le_rfl, haxis _⟩, ⟨le_rfl, haxis _⟩⟩
    · exact h21 ⟨⟨haxis _, le_rfl⟩, ⟨le_rfl, haxis _⟩⟩
    · exact h22 ⟨⟨haxis _, le_rfl⟩, ⟨haxis _, le_rfl⟩⟩
    · exact h12 ⟨⟨le_rfl, haxis _⟩, ⟨haxis _, le_rfl⟩⟩
  · have hi' : (i₁ : ℝ) ≤ i₂ := Nat.cast_le.mpr hi
    have hj' : (j₁ : ℝ) ≤ j₂ := Nat.cast_le.mpr hj
    have hxi : (i₁ : ℝ) / N ≤ ((i₂ : ℝ) + 1) / N :=
      div_le_div_of_nonneg_right (by linarith) hNr.le
    have hyj : (j₁ : ℝ) / N ≤ ((j₂ : ℝ) + 1) / N :=
      div_le_div_of_nonneg_right (by linarith) hNr.le
    rw [abs_of_nonpos (sub_nonpos.mpr hxi), abs_of_nonpos (sub_nonpos.mpr hyj)]
    ring

lemma transfer_algebra {α s n k m : ℝ} (hα : 0 ≤ α) (hn : 0 < n) (hk : 0 < k)
    (hd : α / 2 ≤ s / n ^ 2) (hb : s ^ 2 ≤ k * n ^ 2 * m) :
    (1 / (4 * k)) * α ^ 2 ≤ m / n ^ 2 := by
  have hp : (α / 2) ^ 2 ≤ (s / n ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hd 2
  calc
    (1 / (4 * k)) * α ^ 2 = (α / 2) ^ 2 / k := by ring
    _ ≤ (s / n ^ 2) ^ 2 / k := div_le_div_of_nonneg_right hp hk.le
    _ = s ^ 2 / (k * n ^ 4) := by ring
    _ ≤ (k * n ^ 2 * m) / (k * n ^ 4) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = m / n ^ 2 := by field_simp

theorem main : H1 → H2 → type_of% @Green85.green_85 := by
  intro h1 h2
  obtain ⟨K, hK, hgrid⟩ := integer_grid_bound h1
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  refine ⟨1 / (4 * (K : ℝ)), by positivity, ?_⟩
  intro A hA hsub hne
  by_cases hp : 0 < (volume A).toReal
  · obtain ⟨N, hN, S, hSsub, hcells, hd⟩ := h2 A hA hsub ((volume A).toReal / 2) (by positivity) (by linarith)
    have hS : S.Nonempty := by
      apply Finset.card_pos.mp
      by_contra hn
      have hc : S.card = 0 := by omega
      simp only [hc, Nat.cast_zero, zero_div] at hd
      linarith
    obtain ⟨i₁, i₂, j₁, j₂, hi, hj, h11, h21, h22, h12, hb⟩ :=
      hgrid N hN S hS hSsub
    obtain ⟨x₁, x₂, y₁, y₂, hcorners, harea⟩ :=
      grid_rectangle (A := A) N hN i₁ i₂ j₁ j₂ hi hj
        (hcells (i₁, j₁) h11) (hcells (i₂, j₁) h21)
        (hcells (i₂, j₂) h22) (hcells (i₁, j₂) h12)
    have hbr : (S.card : ℝ) ^ 2 ≤ (K : ℝ) * (N : ℝ) ^ 2 *
        (((i₂ - i₁ : ℕ) : ℝ) + 1) * (((j₂ - j₁ : ℕ) : ℝ) + 1) := by
      exact_mod_cast hb
    rw [Nat.cast_sub hi, Nat.cast_sub hj] at hbr
    have hbr' : (S.card : ℝ) ^ 2 ≤ (K : ℝ) * (N : ℝ) ^ 2 *
        (((i₂ : ℝ) - i₁ + 1) * ((j₂ : ℝ) - j₁ + 1)) := by
      simpa only [mul_assoc] using hbr
    have hbound := transfer_algebra (α := (volume A).toReal) (s := (S.card : ℝ))
      (n := (N : ℝ)) (k := (K : ℝ))
      (m := ((i₂ : ℝ) - i₁ + 1) * ((j₂ : ℝ) - j₁ + 1))
      hp.le (Nat.cast_pos.mpr hN) hKr hd hbr'
    rw [harea] at hbound
    exact ⟨x₁, x₂, y₁, y₂, hcorners, hbound⟩
  · have hz : (volume A).toReal = 0 := le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
    obtain ⟨⟨x, y⟩, hxy⟩ := hne
    refine ⟨x, x, y, y, ?_, by simp only [hz, zero_pow (by decide : 2 ≠ 0),
      mul_zero, sub_self, abs_zero, le_refl]⟩
    simpa only [insert_eq_of_mem (mem_singleton _), singleton_subset_iff] using hxy

end OMA.R_Green85_green_85_R1
