import OMAReductions.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1

/-!
# Reduction `Erdos19.erdos_19.R1.H2.R1.H2.R1.H1.R1.H2.R1` — Complement-Fisher bound & 5-cycle blossom isolation

Strengthens the 5-cycle step `Erdos19.erdos_19.R1.H2.R1.H2.R1.H1.R1.H2` by proving unconditionally:

1. **Complement-Fisher upper bound (`card_le_complement_fisher`)**: For any linear hypergraph `K`
   on `Fin n` with `|A| ≥ r ≥ 3`, a block `T ∈ K` of size `r`, and no three pairwise disjoint
   blocks, at most `r * ((n - r) / (r - 1))` blocks intersect `T` and at most `n - r` blocks are
   disjoint from `T` (by Fisher's inequality on `Finset.univ \ T`), yielding
   `K.card ≤ 1 + r * ((n - r) / (r - 1)) + (n - r)`. In particular, `K.card = 2 * n + 1` forces
   `n + r ≤ r * ((n - r) / (r - 1))` and `2 * r * r - r ≤ n`.
2. **7-edge alternating path augmentation (`augment_seven`)**: Given an induced 5-cycle
   `C5 = {x, R i, L i, L j, R j}` in the disjointness graph, any third pair `(L k, R k)`
   (`k ∉ {i, j}`) reaching `y ∈ U \ {x}` through `R k` and hitting `R i` or `R j` through `L k`
   yields a 7-edge augmenting path and a matching of size `m + 1`. Combined with `E19Five.augment`
   for `L i`, `L j`, and general disjoint pairs `(L a, L b)`, if no `(m + 1)`-matching exists then
   every `k ∉ {i, j}` either has `R k` intersecting all of `U \ {x}` or has `L k` intersecting all
   vertices of `C5`.

Splits into two sharply separated subgoals:
* `H1` (`U.card = 1`, i.e., `K.card = 2 * n + 1`): pure unweighted `ν(K) ≤ 2` extremal problem
  (with `2 * r * r - r ≤ n` and `n + r ≤ r * ((n - r) / (r - 1))`) ruling out `|K| = 2n + 1`.
* `H2` (`2 ≤ U.card`): non-trivial unmatched set `U \ {x}` with induced `C5` chords, complete `C5`
  blossom isolation for every `k ∉ {i, j}`, and global 5-edge augmentation exclusion.
-/

-- Credit: @sanchan (extending OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1 by @zarnab222-dev)

namespace OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1_H2_R1

open Finset
open scoped Classical

-- ### Part 1: Complement-Fisher upper bound on |K|

theorem card_le_complement_fisher {n r : ℕ} (K : Finset (Finset (Fin n))) (hr : 3 ≤ r)
    (T : Finset (Fin n)) (hT : T ∈ K) (hTcard : T.card = r)
    (size : ∀ A ∈ K, r ≤ A.card)
    (linear : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1)
    (tri : ¬ ∃ S ⊆ K, S.card = 3 ∧ ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint A B) :
    K.card ≤ 1 + r * ((n - r) / (r - 1)) + (n - r) := by
  let Hit := (K.erase T).filter (fun A => (T ∩ A).Nonempty)
  let Disj := (K.erase T).filter (fun A => Disjoint T A)
  have hpart : (K.erase T).card = Hit.card + Disj.card := by
    have hdisj_eq : Disj = (K.erase T).filter (fun A => ¬ (T ∩ A).Nonempty) := by
      ext A
      simp only [Disj, Finset.mem_filter, Finset.not_nonempty_iff_eq_empty,
        Finset.disjoint_iff_inter_eq_empty]
    rw [hdisj_eq]
    exact (Finset.card_filter_add_card_filter_not (s := K.erase T)
      (p := fun A => (T ∩ A).Nonempty)).symm
  have hKcard : K.card = 1 + Hit.card + Disj.card := by
    have h1 := Finset.card_erase_add_one hT
    omega
  -- Bound 1: Hit.card ≤ r * ((n - r) / (r - 1))
  let Star : Fin n → Finset (Finset (Fin n)) := fun p => (K.erase T).filter (fun A => p ∈ A)
  have hHit_sub : Hit ⊆ T.biUnion Star := by
    intro A hA
    obtain ⟨hAe, hne⟩ := Finset.mem_filter.mp hA
    obtain ⟨p, hp⟩ := hne
    obtain ⟨hpT, hpA⟩ := Finset.mem_inter.mp hp
    exact Finset.mem_biUnion.mpr ⟨p, hpT, Finset.mem_filter.mpr ⟨hAe, hpA⟩⟩
  have hStar_le : ∀ p ∈ T, (Star p).card ≤ (n - r) / (r - 1) := by
    intro p hpT
    have hComp_card : (Finset.univ \ T).card = n - r := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
        Fintype.card_fin, hTcard]
    have hpw : ((Star p : Set (Finset (Fin n)))).PairwiseDisjoint (fun A => A.erase p) := by
      intro A hA B hB hAB
      have hAK : A ∈ K := Finset.mem_of_mem_erase (Finset.mem_filter.mp hA).1
      have hBK : B ∈ K := Finset.mem_of_mem_erase (Finset.mem_filter.mp hB).1
      have hpA : p ∈ A := (Finset.mem_filter.mp hA).2
      have hpB : p ∈ B := (Finset.mem_filter.mp hB).2
      change Disjoint (A.erase p) (B.erase p)
      rw [Finset.disjoint_left]
      intro q hqA hqB
      obtain ⟨hqp, hqA'⟩ := Finset.mem_erase.mp hqA
      obtain ⟨_, hqB'⟩ := Finset.mem_erase.mp hqB
      have hsub : ({p, q} : Finset (Fin n)) ⊆ A ∩ B := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hpA, hpB⟩
        · exact Finset.mem_inter.mpr ⟨hqA', hqB'⟩
      have h2 : 2 ≤ (A ∩ B).card := by
        have hpair : ({p, q} : Finset (Fin n)).card = 2 := Finset.card_pair (Ne.symm hqp)
        exact hpair ▸ Finset.card_le_card hsub
      have hlin := linear A hAK B hBK hAB
      omega
    have hbiU_sub : (Star p).biUnion (fun A => A.erase p) ⊆ Finset.univ \ T := by
      intro q hq
      obtain ⟨A, hA, hqA⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨hAe, hpA⟩ := Finset.mem_filter.mp hA
      obtain ⟨hAT, hAK⟩ := Finset.mem_erase.mp hAe
      obtain ⟨hqp, hqA'⟩ := Finset.mem_erase.mp hqA
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, ?_⟩
      intro hqT
      have hsub : ({p, q} : Finset (Fin n)) ⊆ T ∩ A := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hpT, hpA⟩
        · exact Finset.mem_inter.mpr ⟨hqT, hqA'⟩
      have h2 : 2 ≤ (T ∩ A).card := by
        have hpair : ({p, q} : Finset (Fin n)).card = 2 := Finset.card_pair (Ne.symm hqp)
        exact hpair ▸ Finset.card_le_card hsub
      have hlin := linear T hT A hAK hAT.symm
      omega
    have hmul : (Star p).card * (r - 1) ≤ n - r := by
      calc (Star p).card * (r - 1)
          = ∑ _A ∈ Star p, (r - 1) := by simp
        _ ≤ ∑ A ∈ Star p, (A.erase p).card := by
            refine Finset.sum_le_sum fun A hA => ?_
            have hAK : A ∈ K := Finset.mem_of_mem_erase (Finset.mem_filter.mp hA).1
            have hpA : p ∈ A := (Finset.mem_filter.mp hA).2
            have hsize := size A hAK
            have hcard := Finset.card_erase_of_mem hpA
            omega
        _ = ((Star p).biUnion (fun A => A.erase p)).card := (Finset.card_biUnion hpw).symm
        _ ≤ (Finset.univ \ T).card := Finset.card_le_card hbiU_sub
        _ = n - r := hComp_card
    exact (Nat.le_div_iff_mul_le (by omega : 0 < r - 1)).mpr hmul
  have hHit_le : Hit.card ≤ r * ((n - r) / (r - 1)) := by
    calc Hit.card
        ≤ (T.biUnion Star).card := Finset.card_le_card hHit_sub
      _ ≤ ∑ p ∈ T, (Star p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ T, ((n - r) / (r - 1)) := Finset.sum_le_sum hStar_le
      _ = r * ((n - r) / (r - 1)) := by simp [hTcard]
  -- Bound 2: Disj.card ≤ n - r via Fisher's inequality on univ \ T
  let Comp : Finset (Fin n) := Finset.univ \ T
  have hComp_card : Fintype.card {v : Fin n // v ∈ Comp} = n - r := by
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ T),
      Finset.card_univ, Fintype.card_fin, hTcard]
  let e : {v : Fin n // v ∈ Comp} ≃ Fin (n - r) := Fintype.equivFinOfCardEq hComp_card
  let phi : Finset (Fin n) → Finset (Fin (n - r)) :=
    fun A => Finset.univ.filter (fun u : Fin (n - r) => (e.symm u).1 ∈ A)
  have hsubComp : ∀ A ∈ Disj, A ⊆ Comp := by
    intro A hA v hv
    have hd : Disjoint T A := (Finset.mem_filter.mp hA).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, fun hvT => Finset.disjoint_left.mp hd hvT hv⟩
  have hphi_card : ∀ A ⊆ Comp, (phi A).card = A.card := by
    intro A hA
    refine Finset.card_bij (fun u _ => (e.symm u).1) ?_ ?_ ?_
    · intro u hu; exact (Finset.mem_filter.mp hu).2
    · intro u₁ _ u₂ _ hEq
      exact e.symm.injective (Subtype.ext hEq)
    · intro v hv
      refine ⟨e ⟨v, hA hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩ <;>
        simp [hv]
  have hphi_inter : ∀ A B : Finset (Fin n), phi (A ∩ B) = phi A ∩ phi B := by
    intro A B
    ext u
    simp [phi]
  have hphi_inj : Set.InjOn phi (Disj : Set (Finset (Fin n))) := by
    intro A hA B hB hEq
    ext v
    constructor
    · intro hvA
      have hvC : v ∈ Comp := hsubComp A hA hvA
      have hu : e ⟨v, hvC⟩ ∈ phi A := by simp [phi, hvA]
      rw [hEq] at hu
      simpa [phi] using hu
    · intro hvB
      have hvC : v ∈ Comp := hsubComp B hB hvB
      have hu : e ⟨v, hvC⟩ ∈ phi B := by simp [phi, hvB]
      rw [← hEq] at hu
      simpa [phi] using hu
  have hDisj_inter : ∀ A ∈ Disj, ∀ B ∈ Disj, A ≠ B → (A ∩ B).Nonempty := by
    intro A hA B hB hAB
    by_contra hnot
    have hAB_disj : Disjoint A B :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hnot)
    obtain ⟨hAe, hTA⟩ := Finset.mem_filter.mp hA
    obtain ⟨hBe, hTB⟩ := Finset.mem_filter.mp hB
    obtain ⟨hAT, hAK⟩ := Finset.mem_erase.mp hAe
    obtain ⟨hBT, hBK⟩ := Finset.mem_erase.mp hBe
    apply tri
    refine ⟨{T, A, B}, ?_, ?_, ?_⟩
    · intro Z hZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
      rcases hZ with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [hAT.symm, hBT.symm]),
        Finset.card_pair hAB]
    · intro X hX Y hY hXY
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
      rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
      · exact (hXY rfl).elim
      · exact hTA
      · exact hTB
      · exact hTA.symm
      · exact (hXY rfl).elim
      · exact hAB_disj
      · exact hTB.symm
      · exact hAB_disj.symm
      · exact (hXY rfl).elim
  have hFisher : (Disj.image phi).card ≤ n - r := by
    apply E19FiveFisher.fisher_bound (Disj.image phi)
    · intro X hX
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hX
      rw [hphi_card A (hsubComp A hA)]
      have hAK : A ∈ K := Finset.mem_of_mem_erase (Finset.mem_filter.mp hA).1
      have hsize := size A hAK
      omega
    · intro X hX Y hY hXY
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hY
      have hAB : A ≠ B := fun h => hXY (congrArg phi h)
      rw [← hphi_inter, hphi_card (A ∩ B) (Finset.inter_subset_left.trans (hsubComp A hA))]
      exact linear A (Finset.mem_of_mem_erase (Finset.mem_filter.mp hA).1)
        B (Finset.mem_of_mem_erase (Finset.mem_filter.mp hB).1) hAB
    · intro X hX Y hY hXY
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hY
      have hAB : A ≠ B := fun h => hXY (congrArg phi h)
      obtain ⟨v, hv⟩ := hDisj_inter A hA B hB hAB
      have hvC : v ∈ Comp := hsubComp A hA (Finset.mem_inter.mp hv).1
      refine ⟨e ⟨v, hvC⟩, ?_⟩
      rw [← hphi_inter]
      simp [phi, Finset.mem_inter.mp hv]
  have hDisj_le : Disj.card ≤ n - r := by
    rwa [Finset.card_image_of_injOn hphi_inj] at hFisher
  omega

-- ### Part 2: 7-edge alternating path augmentation through the 5-cycle

theorem augment_seven {V : Type*} [DecidableEq V] (K : Finset (Finset V)) {m : ℕ}
    (L R : Fin m → Finset V) (lK : ∀ t, L t ∈ K) (rK : ∀ t, R t ∈ K)
    (il : Function.Injective L) (ir : Function.Injective R)
    (apart : ∀ a b, L a ≠ R b) (matched : ∀ t, Disjoint (L t) (R t))
    (i j k : Fin m) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
    (x y : Finset V) (xK : x ∈ K) (yK : y ∈ K) (xy : x ≠ y)
    (xl : ∀ t, x ≠ L t) (xr : ∀ t, x ≠ R t) (yl : ∀ t, y ≠ L t) (yr : ∀ t, y ≠ R t)
    (e1 : Disjoint x (R j)) (e2 : Disjoint (L i) (L j))
    (e3 : Disjoint (L k) (R i)) (e4 : Disjoint y (R k)) :
    ∃ l r : Fin (m + 1) → Finset V, (∀ t, l t ∈ K) ∧ (∀ t, r t ∈ K) ∧
      Function.Injective l ∧ Function.Injective r ∧ (∀ a b, l a ≠ r b) ∧
      ∀ t, Disjoint (l t) (r t) := by
  let g (t : Fin m) :=
    if t = i then L k else if t = j then x else if t = k then y else L t
  have gi : Function.Injective g := by
    intro a b h
    dsimp [g] at h
    split_ifs at h <;> grind
  have fresh (t : Fin m) : L i ≠ g t ∧ L j ≠ g t := by
    dsimp [g]
    split_ifs <;> grind
  have home (t : Fin m) : g t ∈ K := by
    dsimp [g]
    split_ifs <;> grind
  have sep (a b : Fin m) : g a ≠ R b := by
    dsimp [g]
    split_ifs <;> grind
  have good (t : Fin m) : Disjoint (g t) (R t) := by
    dsimp [g]
    split_ifs <;> grind
  refine ⟨Fin.cons (L i) g, Fin.cons (L j) R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.cases (lK i) home
  · exact Fin.cases (lK j) rK
  · intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp [Fin.cons_zero, Fin.cons_succ, gi.eq_iff, (fresh _).1, Ne.symm (fresh _).1]
  · intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp [Fin.cons_zero, Fin.cons_succ, ir.eq_iff, apart, fun t => Ne.symm (apart j t)]
  · intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp [Fin.cons_zero, Fin.cons_succ, il.ne ij, apart, fun t => Ne.symm (fresh t).2, sep]
  · exact Fin.cases e2 good

theorem no_triangle_edge {n : ℕ} (K : Finset (Finset (Fin n)))
    (tri : ¬ ∃ S ⊆ K, S.card = 3 ∧ ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint A B)
    {A B C : Finset (Fin n)} (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (dAB : Disjoint A B) (dAC : Disjoint A C) : ¬ Disjoint B C := by
  intro dBC
  apply tri
  refine ⟨{A, B, C}, ?_, ?_, ?_⟩
  · intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl | rfl <;> assumption
  · rw [Finset.card_insert_of_notMem (by simp [hAB, hAC]), Finset.card_pair hBC]
  · intro X hX Y hY hXY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact (hXY rfl).elim
    · exact dAB
    · exact dAC
    · exact dAB.symm
    · exact (hXY rfl).elim
    · exact dBC
    · exact dAC.symm
    · exact dBC.symm
    · exact (hXY rfl).elim

-- ### Part 3: Hypotheses H1 and H2

/-- Extremal `U.card = 1` case (`K.card = 2 * n + 1`): pure unweighted `ν(K) ≤ 2` linear
hypergraph extremal bound, strengthened by Complement-Fisher (`n + r ≤ r * ((n - r)/(r - 1))`
and `2 * r * r - r ≤ n`). -/
def H1 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → 2 * r * r - r ≤ n →
    n + r ≤ r * ((n - r) / (r - 1)) →
    (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →
    (¬ ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧
      (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)) →
    (¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) →
    K.card ≠ 2 * n + 1

/-- Non-trivial unmatched set (`2 ≤ U.card`) with induced 5-cycle chords, complete 5-cycle
blossom isolation for every `k ∉ {i, j}`, and global 5-edge augmentation exclusion. -/
def H2 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r * r + r - 1 ≤ n →
    n ≤ r * ((n - r) / (r - 1)) → (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →
    (¬ ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧
      (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)) →
    (¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) →
    ∀ (m : ℕ) (L R : Fin m → Finset (Fin n)) (U : Finset (Finset (Fin n))),
    (∀ i, L i ∈ K) → (∀ i, R i ∈ K) → Function.Injective L → Function.Injective R →
    (∀ i j, L i ≠ R j) → (∀ i, Disjoint (L i) (R i)) → U ⊆ K → 2 ≤ U.card →
    (∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B) → (∀ i, ∀ A ∈ U, ¬ Disjoint (L i) A) →
    (∀ i, L i ∉ U) → (∀ i, R i ∉ U) → K.card = U.card + 2 * m →
    (U.card + m = n + 1) → (2 * (r - 1) < m) →
    (¬ ∃ w : Fin n → ℝ, ∀ A ∈ U ∪ univ.image L, ∑ i ∈ A, w i = 1) →
    (∀ a b, a ≠ b → Disjoint (L a) (L b) → ∀ y₁ ∈ U, ∀ y₂ ∈ U, y₁ ≠ y₂ →
      ¬ (Disjoint y₁ (R a) ∧ Disjoint y₂ (R b))) →
    (∃ i j, i ≠ j ∧ Disjoint (L i) (L j) ∧ ¬ Disjoint (R i) (R j) ∧
      ¬ Disjoint (R i) (L j) ∧ ¬ Disjoint (L i) (R j) ∧ ∃ x ∈ U,
      (∀ y ∈ U, (Disjoint y (R i) ↔ y = x) ∧ (Disjoint y (R j) ↔ y = x)) ∧
      (∀ k, k ≠ i → k ≠ j → (∀ y ∈ U, y ≠ x → ¬ Disjoint y (R k)) ∨
        (¬ Disjoint (L k) (L i) ∧ ¬ Disjoint (L k) (L j) ∧
         ¬ Disjoint (L k) (R i) ∧ ¬ Disjoint (L k) (R j)))) →
    ∃ l r' : Fin (m + 1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)

-- ### Part 4: Main reduction proof

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro h1 h2 n r K hr gap pack witness size linear degree many disorder nonsplit tri
    m L R U lk rk il ir apart matched sub um lm lo ro count total band weight c5
  obtain ⟨i, j, ij, mid, x, hx, hxy⟩ := c5
  have hUpos : 1 ≤ U.card := Finset.card_pos.mpr ⟨x, hx⟩
  by_cases hU1 : U.card = 1
  · exfalso
    have hK2n1 : K.card = 2 * n + 1 := by omega
    obtain ⟨T, hT, hTcard⟩ := witness
    have hcf := card_le_complement_fisher K hr T hT hTcard size linear tri
    have hnr : n + r ≤ r * ((n - r) / (r - 1)) := by omega
    have h2r2 : 2 * r * r - r ≤ n := by
      have hdiv : (r - 1) * ((n - r) / (r - 1)) ≤ n - r := Nat.mul_div_le (n - r) (r - 1)
      have hmul : (r - 1) * (n + r) ≤ (r - 1) * (r * ((n - r) / (r - 1))) :=
        Nat.mul_le_mul_left (r - 1) hnr
      have hrhs : (r - 1) * (r * ((n - r) / (r - 1))) ≤ r * (n - r) := by
        calc (r - 1) * (r * ((n - r) / (r - 1)))
            = r * ((r - 1) * ((n - r) / (r - 1))) := by ring
          _ ≤ r * (n - r) := Nat.mul_le_mul_left r hdiv
      have hle : (r - 1) * (n + r) ≤ r * (n - r) := hmul.trans hrhs
      have hrr : r ≤ r * r := Nat.le_mul_self r
      have hnr_le : r ≤ n := by omega
      have hlin : (r - 1) * (n + r) + (n + r) = r * n + r * r := by
        calc (r - 1) * (n + r) + (n + r)
            = ((r - 1) + 1) * (n + r) := by ring
          _ = r * (n + r) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ r)]
          _ = r * n + r * r := by ring
      have hsub : r * (n - r) + r * r = r * n := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hnr_le]
      have h2rr : 2 * r * r = r * r + r * r := by ring
      omega
    exact h1 n r K hr h2r2 hnr ⟨T, hT, hTcard⟩ size linear degree many disorder nonsplit tri hK2n1
  · have hU2 : 2 ≤ U.card := by omega
    by_cases hfive : ∃ a b : Fin m, a ≠ b ∧ Disjoint (L a) (L b) ∧
        ∃ y₁ ∈ U, ∃ y₂ ∈ U, y₁ ≠ y₂ ∧ Disjoint y₁ (R a) ∧ Disjoint y₂ (R b)
    · obtain ⟨a, b, hab, hLab, y₁, hy₁, y₂, hy₂, hy12, h1a, h2b⟩ := hfive
      exact E19Five.augment K L R lk rk il ir apart matched a b hab y₁ y₂
        (sub hy₁) (sub hy₂) hy12
        (fun t h => lo t (h ▸ hy₁)) (fun t h => ro t (h ▸ hy₁))
        (fun t h => lo t (h ▸ hy₂)) (fun t h => ro t (h ▸ hy₂))
        h1a hLab h2b
    · push Not at hfive
      have hfive' : ∀ a b : Fin m, a ≠ b → Disjoint (L a) (L b) →
          ∀ y₁ ∈ U, ∀ y₂ ∈ U, y₁ ≠ y₂ → ¬ (Disjoint y₁ (R a) ∧ Disjoint y₂ (R b)) := by
        intro a b hab hLab y₁ hy₁ y₂ hy₂ hy12 ⟨h1a, h2b⟩
        exact hfive a b hab hLab y₁ hy₁ y₂ hy₂ hy12 h1a h2b
      have hxRi : Disjoint x (R i) := (hxy x hx).1.mpr rfl
      have hxRj : Disjoint x (R j) := (hxy x hx).2.mpr rfl
      have hch_RR : ¬ Disjoint (R i) (R j) :=
        no_triangle_edge K tri (sub hx) (rk i) (rk j)
          (fun h => ro i (h ▸ hx)) (fun h => ro j (h ▸ hx)) (ir.ne ij) hxRi hxRj
      have hch_RiLj : ¬ Disjoint (R i) (L j) :=
        no_triangle_edge K tri (lk i) (rk i) (lk j)
          (apart i i) (il.ne ij) (apart j i).symm (matched i) mid
      have hch_LiRj : ¬ Disjoint (L i) (R j) :=
        no_triangle_edge K tri (lk j) (lk i) (rk j)
          (il.ne ij.symm) (apart j j) (apart i j) mid.symm (matched j)
      by_cases hbridge : ∃ k : Fin m, k ≠ i ∧ k ≠ j ∧
          (∃ y ∈ U, y ≠ x ∧ Disjoint y (R k)) ∧
          (Disjoint (L k) (L i) ∨ Disjoint (L k) (L j) ∨
           Disjoint (L k) (R i) ∨ Disjoint (L k) (R j))
      · obtain ⟨k, hki, hkj, ⟨y, hy, hyx, hyRk⟩, hhit⟩ := hbridge
        rcases hhit with hLi | hLj | hRi | hRj
        · exact E19Five.augment K L R lk rk il ir apart matched i k hki.symm x y
            (sub hx) (sub hy) hyx.symm
            (fun t h => lo t (h ▸ hx)) (fun t h => ro t (h ▸ hx))
            (fun t h => lo t (h ▸ hy)) (fun t h => ro t (h ▸ hy))
            hxRi hLi.symm hyRk
        · exact E19Five.augment K L R lk rk il ir apart matched j k hkj.symm x y
            (sub hx) (sub hy) hyx.symm
            (fun t h => lo t (h ▸ hx)) (fun t h => ro t (h ▸ hx))
            (fun t h => lo t (h ▸ hy)) (fun t h => ro t (h ▸ hy))
            hxRj hLj.symm hyRk
        · exact augment_seven K L R lk rk il ir apart matched i j k ij hki.symm hkj.symm x y
            (sub hx) (sub hy) hyx.symm
            (fun t h => lo t (h ▸ hx)) (fun t h => ro t (h ▸ hx))
            (fun t h => lo t (h ▸ hy)) (fun t h => ro t (h ▸ hy))
            hxRj mid hRi hyRk
        · exact augment_seven K L R lk rk il ir apart matched j i k ij.symm hkj.symm hki.symm x y
            (sub hx) (sub hy) hyx.symm
            (fun t h => lo t (h ▸ hx)) (fun t h => ro t (h ▸ hx))
            (fun t h => lo t (h ▸ hy)) (fun t h => ro t (h ▸ hy))
            hxRi mid.symm hRj hyRk
      · push Not at hbridge
        have hiso : ∀ k : Fin m, k ≠ i → k ≠ j →
            (∀ y ∈ U, y ≠ x → ¬ Disjoint y (R k)) ∨
            (¬ Disjoint (L k) (L i) ∧ ¬ Disjoint (L k) (L j) ∧
             ¬ Disjoint (L k) (R i) ∧ ¬ Disjoint (L k) (R j)) := by
          intro k hki hkj
          by_cases hact : ∃ y ∈ U, y ≠ x ∧ Disjoint y (R k)
          · exact Or.inr (hbridge k hki hkj hact)
          · push Not at hact
            exact Or.inl hact
        exact h2 n r K hr gap pack witness size linear degree many disorder nonsplit tri
          m L R U lk rk il ir apart matched sub hU2 um lm lo ro count total band weight hfive'
          ⟨i, j, ij, mid, hch_RR, hch_RiLj, hch_LiRj, x, hx, hxy, hiso⟩

end OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1_H2_R1
