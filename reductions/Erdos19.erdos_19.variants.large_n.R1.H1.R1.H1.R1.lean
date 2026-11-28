import OMAReductions.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1
import Mathlib.Data.Fintype.EquivFin

-- Reduction Erdos19.erdos_19.variants.large_n.R1.H1.R1.H1.R1 of step Erdos19.erdos_19.variants.large_n.R1.H1.R1.H1
-- Credit: @mucoucah
-- Proved here: the critical-family step is implied by eventual n-colourability of every linear
-- family of ranks in [2, R] on Fin n. Split such a family L by the pair deficit of a point x
-- (the number of y with the pair x y not a 2-block of L). If every point has deficit at least
-- 2 (n / q), pair-budget counting gives maximum degree at most n - n / q, and an asymptotic
-- (1 + 1/q) D colouring bound finishes (pair completion supplies the design).
-- H1: Kahn 1996 / Pippenger-Spencer for linear bounded-rank hypergraphs: for fixed R and q,
--     maximum degree D at least D0 gives a proper colouring with D + D / q colours.
-- H2: the tight case: for each R, some q at least 2 such that eventually every linear family of
--     ranks in [2, R] with a point of pair deficit below 2 (n / q) (an almost full pair star)
--     is properly coloured with n colours.

namespace OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1_H1_R1

open Filter Finset
open scoped BigOperators
open OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1

private theorem point_rank_budget {n : ℕ} {K L : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hLK : L ⊆ K) (hsize : ∀ B ∈ L, 2 ≤ B.card) (x : Fin n) :
    (L.filter (fun B => x ∈ B)).card +
      ∑ B ∈ L.filter (fun B => x ∈ B), (B.card - 2) ≤ n - 1 := by
  classical
  calc
    _ = ∑ B ∈ L.filter (fun B => x ∈ B), (1 + (B.card - 2)) := by
      rw [sum_add_distrib]
      simp
    _ = ∑ B ∈ L.filter (fun B => x ∈ B), (B.card - 1) := by
      apply sum_congr rfl
      intro B hB
      have := hsize B (mem_filter.mp hB).1
      omega
    _ ≤ ∑ B ∈ K.filter (fun B => x ∈ B), (B.card - 1) :=
      sum_le_sum_of_subset (filter_subset_filter _ hLK)
    _ = n - 1 := link_weight_eq hpair x

private theorem pair_label_inj {n : ℕ} (x : Fin n) {y z : Fin n}
    (hy : y ≠ x)
    (h : ({x, y} : Finset (Fin n)) = {x, z}) : y = z := by
  have hy' : y ∈ ({x, z} : Finset (Fin n)) := h ▸ (by simp)
  simpa [hy] using hy'

private theorem large_degree_le_excess {n : ℕ} (L : Finset (Finset (Fin n))) (x : Fin n) :
    ((L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)).card ≤
      ∑ A ∈ L.filter (fun A => x ∈ A), (A.card - 2) := by
  let I := (L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)
  have hsub : I ⊆ L.filter (fun A => x ∈ A) := by
    intro A hA
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hA).1).1, (mem_filter.mp hA).2⟩
  calc
    _ = ∑ _A ∈ I, 1 := by simp [I]
    _ ≤ ∑ A ∈ I, (A.card - 2) := by
      apply sum_le_sum
      intro A hA
      have h := (mem_filter.mp (mem_filter.mp hA).1).2
      omega
    _ ≤ _ := sum_le_sum_of_subset hsub

private theorem bounded_pair_completion {n R : ℕ} (L : Finset (Finset (Fin n)))
    (hR : 2 ≤ R)
    (hsize : ∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R)
    (hlin : ∀ A ∈ L, ∀ B ∈ L, ∀ ⦃x y : Fin n⦄,
      x ≠ y → x ∈ A → y ∈ A → x ∈ B → y ∈ B → A = B) :
    ∃ C, L ⊆ C ∧ (∀ A ∈ C, 2 ≤ A.card ∧ A.card ≤ R) ∧
      (∀ x y : Fin n, x ≠ y → ∃! A, A ∈ C ∧ x ∈ A ∧ y ∈ A) ∧
      C.filter (fun A => 3 ≤ A.card) = L.filter (fun A => 3 ≤ A.card) ∧
      (∀ x y : Fin n, x ≠ y → {x,y} ∉ C.filter (fun A => A.card = 2) →
        ∃ A ∈ L.filter (fun A => 3 ≤ A.card), x ∈ A ∧ y ∈ A) := by
  classical
  let H := L.filter (fun A => 3 ≤ A.card)
  let P := ((univ : Finset (Fin n)).powersetCard 2).filter
    (fun B => ∀ A ∈ H, ¬ B ⊆ A)
  let C := H ∪ P
  have hHL (A : Finset (Fin n)) (hA : A ∈ H) : A ∈ L := (mem_filter.mp hA).1
  have hP (B : Finset (Fin n)) : B ∈ P ↔ B.card = 2 ∧ ∀ A ∈ H, ¬ B ⊆ A := by
    simp [P, mem_powersetCard]
  have hLC : L ⊆ C := by
    intro B hB
    by_cases hBH : B ∈ H
    · exact mem_union_left _ hBH
    · have hbc : B.card = 2 := by
        have hlow := (hsize B hB).1
        by_contra hb
        exact hBH (mem_filter.mpr ⟨hB, by omega⟩)
      apply mem_union_right
      refine (hP B).mpr ⟨hbc, ?_⟩
      intro A hA hsub
      obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (show 1 < B.card by omega)
      have he := hlin B hB A (hHL A hA) hxy hx hy (hsub hx) (hsub hy)
      exact hBH (he.symm ▸ hA)
  have hsizeC (A : Finset (Fin n)) (hA : A ∈ C) : 2 ≤ A.card ∧ A.card ≤ R := by
    rcases mem_union.mp hA with hA | hA
    · exact hsize A (mem_filter.mp hA).1
    · simpa only [(hP A).mp hA |>.1] using And.intro (le_refl 2) hR
  have hCover (x y : Fin n) (hxy : x ≠ y) :
      ∃! A, A ∈ C ∧ x ∈ A ∧ y ∈ A := by
    let e : Finset (Fin n) := {x,y}
    have he₂ : e.card = 2 := card_pair hxy
    have heq (B : Finset (Fin n)) (hB : B ∈ P) (hx : x ∈ B) (hy : y ∈ B) : B = e :=
      (eq_of_subset_of_card_le (insert_subset hx (singleton_subset_iff.mpr hy))
        (le_of_eq (((hP B).mp hB).1.trans he₂.symm))).symm
    by_cases hc : ∃ A ∈ H, x ∈ A ∧ y ∈ A
    · obtain ⟨A, hA, hx, hy⟩ := hc
      refine ⟨A, ⟨mem_union_left _ hA, hx, hy⟩, ?_⟩
      rintro B ⟨hB, hxB, hyB⟩
      rcases mem_union.mp hB with hB | hB
      · exact hlin B (hHL B hB) A (hHL A hA) hxy hxB hyB hx hy
      · exact (((hP B).mp hB).2 A hA (heq B hB hxB hyB ▸
            insert_subset hx (singleton_subset_iff.mpr hy))).elim
    · have hp : e ∈ P := (hP e).mpr ⟨he₂, fun A hA hs => hc ⟨A, hA, hs (by simp [e]),
        hs (by simp [e])⟩⟩
      refine ⟨e, ⟨mem_union_right _ hp, by simp [e], by simp [e]⟩, ?_⟩
      rintro B ⟨hB, hxB, hyB⟩
      rcases mem_union.mp hB with hB | hB
      · exact (hc ⟨B, hB, hxB, hyB⟩).elim
      · exact heq B hB hxB hyB
  have hHC : C.filter (fun A => 3 ≤ A.card) = H := by
    ext A
    constructor
    · intro ha
      obtain ⟨hu, hr⟩ := mem_filter.mp ha
      rcases mem_union.mp hu with hm | hm
      · exact hm
      · have hh := ((hP A).mp hm).1
        omega
    · intro ha
      exact mem_filter.mpr ⟨mem_union_left _ ha, (mem_filter.mp ha).2⟩
  refine ⟨C, hLC, hsizeC, hCover, hHC, ?_⟩
  intro x y hxy hno
  by_contra hc
  have hs : ({x,y} : Finset (Fin n)) ∈ P := (hP _).mpr
    ⟨card_pair hxy, fun A hA hs => hc ⟨A, hA, hs (by simp), hs (by simp)⟩⟩
  exact hno (mem_filter.mpr ⟨mem_union_right _ hs, card_pair hxy⟩)

private theorem pair_star_and_deficit {n : ℕ} (L : Finset (Finset (Fin n))) (x : Fin n) :
    ((L.filter (fun A => A.card = 2)).filter (fun A => x ∈ A)).card +
      ((univ : Finset (Fin n)).filter
        (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card = n - 1 := by
  classical
  let G := L.filter (fun A => A.card = 2)
  let U := (univ : Finset (Fin n)).erase x
  let S := U.filter (fun y => ({x,y} : Finset (Fin n)) ∈ G)
  have hS : S.image (fun y => ({x,y} : Finset (Fin n))) = G.filter (fun A => x ∈ A) := by
    ext A
    constructor
    · intro hA
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hA
      exact mem_filter.mpr ⟨(mem_filter.mp hy).2, by simp⟩
    · intro hA
      obtain ⟨hA, hx⟩ := mem_filter.mp hA
      obtain ⟨y, hy, rfl⟩ := pair_of_mem_of_card_two hx (mem_filter.mp hA).2
      exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_erase.mpr ⟨hy, mem_univ _⟩, hA⟩)
  have hcard := card_image_of_injOn (s := S) (f := fun y => ({x,y} : Finset (Fin n))) (by
    intro y hy z _ h
    have hne := (mem_erase.mp (mem_filter.mp (mem_coe.mp hy)).1).1
    exact pair_label_inj x hne h)
  rw [hS] at hcard
  have hpart := card_filter_add_card_filter_not (s := U)
    (fun y => ({x,y} : Finset (Fin n)) ∈ G)
  change S.card + (U.filter (fun y => ({x,y} : Finset (Fin n)) ∉ G)).card = U.card at hpart
  have hu : U.card = n - 1 := by
    simp [U, card_erase_of_mem (mem_univ x)]
  have heq : U.filter (fun y => ({x,y} : Finset (Fin n)) ∉ G) =
      (univ : Finset (Fin n)).filter (fun y => y ≠ x ∧ {x,y} ∉ G) := by
    ext y
    simp [U]
  rw [hcard, ← heq, hpart, hu]

private theorem total_degree_lt_from_pair_deficit {n : ℕ} {K L : Finset (Finset (Fin n))}
    (hLK : L ⊆ K)
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hsize : ∀ A ∈ L, 2 ≤ A.card) (x : Fin n) :
    2 * (L.filter (fun A => x ∈ A)).card +
      ((univ : Finset (Fin n)).filter
        (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card ≤ 2 * (n - 1) := by
  let T := L.filter (fun A => x ∈ A)
  let G := (L.filter (fun A => A.card = 2)).filter (fun A => x ∈ A)
  let H := (L.filter (fun A => 3 ≤ A.card)).filter (fun A => x ∈ A)
  have hcover : G ∪ H = T := by
    ext A
    simp only [G, H, T, mem_union, mem_filter]
    constructor
    · rintro (⟨⟨hA, _⟩, hx⟩ | ⟨⟨hA, _⟩, hx⟩) <;> exact ⟨hA, hx⟩
    · rintro ⟨hA, hx⟩
      have ha := hsize A hA
      by_cases he : A.card = 2
      · exact Or.inl ⟨⟨hA, he⟩, hx⟩
      · exact Or.inr ⟨⟨hA, by omega⟩, hx⟩
  have hdisj : Disjoint G H := by
    apply disjoint_left.mpr
    intro A hg hh
    have h₂ := (mem_filter.mp (mem_filter.mp hg).1).2
    have h₃ := (mem_filter.mp (mem_filter.mp hh).1).2
    omega
  have hcount : T.card = G.card + H.card := by
    rw [← hcover, card_union_of_disjoint hdisj]
  have hbudget := point_rank_budget hpair hLK hsize x
  have hlarge := large_degree_le_excess L x
  have hstar := pair_star_and_deficit L x
  change T.card + _ ≤ _ at hbudget
  change H.card ≤ _ at hlarge
  change G.card + _ = _ at hstar
  change 2 * T.card + _ ≤ _
  omega

private theorem color_of_uniform_pair_deficit_of_approx {n R q D₀ : ℕ}
    (hq : 2 ≤ q) (hn : 2 * D₀ ≤ n)
    (happrox : ∀ D : ℕ, D₀ ≤ D → ∀ H : Finset (Finset (Fin n)),
      (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ R) →
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ x : Fin n, (H.filter (fun A => x ∈ A)).card ≤ D) →
      ∃ c : Finset (Fin n) → Fin (D + D / q), (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B))
    {K L : Finset (Finset (Fin n))}
    (hLK : L ⊆ K)
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hsize : ∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R)
    (hdeficit : ∀ x : Fin n, 2 * (n / q) ≤ ((univ : Finset (Fin n)).filter
      (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card) :
    ∃ c : Finset (Fin n) → Fin n, (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) := by
  let D := n - n / q
  have hhalf : n / q * 2 ≤ n :=
    (Nat.mul_le_mul_left (n / q) hq).trans (Nat.div_mul_le_self n q)
  have hD₀ : D₀ ≤ D := by dsimp [D]; omega
  have hD : ∀ x : Fin n, (L.filter (fun A => x ∈ A)).card ≤ D := by
    intro x
    have hb := total_degree_lt_from_pair_deficit hLK hpair (fun A hA => (hsize A hA).1) x
    have hd := hdeficit x
    dsimp [D]
    omega
  have hlinear : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).card ≤ 1 := by
    intro A hA B hB hAB
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hne
    exact hAB (block_eq_of_pair hpair (hLK hA) (hLK hB) hne
      (mem_inter.mp hi).1 (mem_inter.mp hj).1 (mem_inter.mp hi).2 (mem_inter.mp hj).2)
  obtain ⟨c, hc⟩ := happrox D hD₀ L hsize hlinear hD
  have hfit : D + D / q ≤ n := by
    have hd : D ≤ n := Nat.sub_le _ _
    have hdiv : D / q ≤ n / q := Nat.div_le_div_right hd
    dsimp [D] at *
    omega
  refine ⟨fun A => Fin.castLE hfit (c A), ?_⟩
  intro A hA B hB hAB hmeet he
  have heq := congrArg (fun i : Fin n => i.val) he
  exact hc A hA B hB hAB hmeet (Fin.ext heq)

def H1 : Prop :=
  ∀ R q : ℕ, 2 ≤ q → ∃ D₀ : ℕ, ∀ n D : ℕ, D₀ ≤ D → ∀ H : Finset (Finset (Fin n)),
    (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ R) →
    (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ x : Fin n, (H.filter (fun A => x ∈ A)).card ≤ D) →
    ∃ c : Finset (Fin n) → Fin (D + D / q),
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B

def H2 : Prop :=
  ∀ R : ℕ, ∃ q : ℕ, 2 ≤ q ∧ ∀ᶠ n in atTop, ∀ L : Finset (Finset (Fin n)),
    (∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R) →
    (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).card ≤ 1) →
    (∃ x : Fin n, ((univ : Finset (Fin n)).filter
      (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card < 2 * (n / q)) →
    ∃ c : Finset (Fin n) → Fin n,
      ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B


theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1.H1 := by
  classical
  intro h1 h2 R
  obtain ⟨q, hq, hev⟩ := h2 R
  obtain ⟨D₀, hD₀⟩ := h1 R q hq
  filter_upwards [hev, Filter.eventually_ge_atTop (2 * D₀)] with n hn hnD
  intro K L hsize hpair hLK hR hbad _ _ _ _ _
  apply hbad
  have hlin : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).card ≤ 1 := by
    intro A hA B hB hAB
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hne
    exact hAB (block_eq_of_pair hpair (hLK hA) (hLK hB) hne
      (mem_inter.mp hi).1 (mem_inter.mp hj).1 (mem_inter.mp hi).2 (mem_inter.mp hj).2)
  have hsz : ∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R := fun A hA => ⟨(hsize A (hLK hA)).1, hR A hA⟩
  by_cases hx : ∃ x : Fin n, ((univ : Finset (Fin n)).filter
      (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card < 2 * (n / q)
  · exact hn L hsz hlin hx
  · push Not at hx
    exact color_of_uniform_pair_deficit_of_approx hq hnD (hD₀ n) hLK hpair hsz hx

end OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1_H1_R1
