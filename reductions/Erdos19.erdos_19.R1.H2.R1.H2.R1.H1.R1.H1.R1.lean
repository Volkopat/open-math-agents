import OMAReductions.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1

/-!
# Reduction `Erdos19.erdos_19.R1.H2.R1.H2.R1.H1.R1.H1.R1` — Complement-Fisher bound, swapped-family Fisher obstruction, and 7-edge dead-mate augmentation

Strengthens the dead-mate step `Erdos19.erdos_19.R1.H2.R1.H2.R1.H1.R1.H1` by proving unconditionally:

1. **Complement-Fisher upper bound (`card_le_complement_fisher`)**: For any linear hypergraph `K`
   on `Fin n` with `|A| ≥ r ≥ 3`, an `r`-block `T ∈ K`, and no three pairwise disjoint blocks,
   `K.card ≤ 1 + r * ((n - r) / (r - 1)) + (n - r)`. Whenever `U.card ≤ 1` (hence `2 * n + 1 ≤ K.card`),
   this forces `n + r ≤ r * ((n - r) / (r - 1))` and `2 * r * r - r ≤ n`.
2. **Swapped-family Fisher obstruction (`dead_mate_fisher_swap`)**: Replacing `L i` by the dead mate
   `R i` in `U ∪ univ.image L` produces a family of `n + 1` blocks in which every member of `U` meets
   every other member. Applying `E19Five.critical_pair` (Fisher's inequality) together with
   triangle-freeness (`¬ Disjoint (R i) (L j)`) forces either a third index `k ∉ {i, j}` with
   `Disjoint (L k) (R i)` or a second disjoint pair `(L a, L b)` avoiding `i`.
3. **7-edge alternating path augmentation (`augment_seven`)**: If `R j` reaches `y ∈ U` and some
   `k ∉ {i, j}` satisfies `Disjoint (L k) (R i)` and reaches `z ∈ U \ {y}` through `R k`, then the
   7-edge path `z - R k - L k - R i - L i - L j - R j - y` augments the matching to size `m + 1`.

Splits cleanly into three disjoint subgoals:
* `H1` (`U.card ≤ 1`, i.e., `2 * n + 1 ≤ K.card`): pure unweighted `ν(K) ≤ 2` extremal bound
  (`K.card ≤ 2 * n`) with `2 * r * r - r ≤ n` and `n + r ≤ r * ((n - r) / (r - 1))`.
* `H2` (`2 ≤ U.card`, both `R i` and `R j` dead to `U`): swapped-family Fisher obstruction and
  global 5-edge augmentation exclusion.
* `H3` (`2 ≤ U.card`, `R i` dead to `U`, `R j` live at `y ∈ U`): swapped-family Fisher obstruction,
  7-edge dead-mate augmentation exclusion, and global 5-edge augmentation exclusion.
-/

-- Credit: @sanchan (extending OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1 by @zarnab222-dev)

namespace OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1_H1_R1

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

-- ### Part 2: Swapped-family Fisher obstruction and 7-edge alternating path

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

theorem dead_mate_fisher_swap {n m : ℕ} (K U : Finset (Finset (Fin n)))
    (L R : Fin m → Finset (Fin n)) (lk : ∀ t, L t ∈ K) (rk : ∀ t, R t ∈ K)
    (il : Function.Injective L) (apart : ∀ a b, L a ≠ R b) (matched : ∀ t, Disjoint (L t) (R t))
    (sub : U ⊆ K) (um : ∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B)
    (lm : ∀ t, ∀ A ∈ U, ¬ Disjoint (L t) A) (lo : ∀ t, L t ∉ U) (ro : ∀ t, R t ∉ U)
    (size : ∀ A ∈ K, 2 ≤ A.card) (linear : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1)
    (tri : ¬ ∃ S ⊆ K, S.card = 3 ∧ ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint A B)
    (large : n < U.card + m) (i j : Fin m) (ij : i ≠ j) (mid : Disjoint (L i) (L j))
    (dead : ∀ x ∈ U, ¬ Disjoint x (R i)) :
    (∃ k, k ≠ i ∧ k ≠ j ∧ Disjoint (L k) (R i)) ∨
    (∃ a b, a ≠ i ∧ b ≠ i ∧ a ≠ b ∧ Disjoint (L a) (L b)) := by
  let L' : Fin m → Finset (Fin n) := fun t => if t = i then R i else L t
  have hL'K : ∀ t, L' t ∈ K := fun t => by dsimp [L']; split_ifs <;> [exact rk i; exact lk t]
  have hL'inj : Function.Injective L' := by
    intro a b h
    dsimp [L'] at h
    split_ifs at h with ha hb hb
    · rw [ha, hb]
    · exact absurd h.symm (apart b i)
    · exact absurd h (apart a i)
    · exact il h
  have hL'out : ∀ t, L' t ∉ U := fun t => by dsimp [L']; split_ifs <;> [exact ro i; exact lo t]
  have hL'meet : ∀ t, ∀ A ∈ U, ¬ Disjoint (L' t) A := by
    intro t A hA
    dsimp [L']
    split_ifs
    · exact fun h => dead A hA h.symm
    · exact lm t A hA
  obtain ⟨a, b, hab, hdisj⟩ :=
    E19Five.critical_pair K U L' hL'K hL'inj sub hL'out um hL'meet size linear large
  have hRiLj : ¬ Disjoint (R i) (L j) :=
    no_triangle_edge K tri (lk i) (rk i) (lk j)
      (apart i i) (il.ne ij) (apart j i).symm (matched i) mid
  by_cases ha : a = i
  · have hbi : b ≠ i := fun h => hab (ha.trans h.symm)
    dsimp [L'] at hdisj
    rw [if_pos ha, if_neg hbi] at hdisj
    have hbj : b ≠ j := fun h => hRiLj (h ▸ hdisj)
    exact Or.inl ⟨b, hbi, hbj, hdisj.symm⟩
  · by_cases hb : b = i
    · dsimp [L'] at hdisj
      rw [if_neg ha, if_pos hb] at hdisj
      have haj : a ≠ j := fun h => hRiLj (h ▸ hdisj.symm)
      exact Or.inl ⟨a, ha, haj, hdisj⟩
    · dsimp [L'] at hdisj
      rw [if_neg ha, if_neg hb] at hdisj
      exact Or.inr ⟨a, b, ha, hb, hab, hdisj⟩

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

-- ### Part 3: Hypotheses H1, H2, H3

/-- Extremal `U.card ≤ 1` case (`2 * n + 1 ≤ K.card`): pure unweighted `ν(K) ≤ 2` linear hypergraph
bound (`K.card ≤ 2 * n`), strengthened by Complement-Fisher (`2 * r * r - r ≤ n` and
`n + r ≤ r * ((n - r) / (r - 1))`). -/
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
    K.card ≤ 2 * n

/-- Doubly-dead critical pair (`2 ≤ U.card`): both `R i` and `R j` meet every element of `U`,
equipped with the swapped-family Fisher obstruction and global 5-edge exclusion. -/
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
    (∃ i j, i ≠ j ∧ Disjoint (L i) (L j) ∧
      (∀ x ∈ U, ¬ Disjoint x (R i) ∧ ¬ Disjoint x (R j)) ∧
      ((∃ k, k ≠ i ∧ k ≠ j ∧ Disjoint (L k) (R i)) ∨
       (∃ a b, a ≠ i ∧ b ≠ i ∧ a ≠ b ∧ Disjoint (L a) (L b)))) →
    ∃ l r' : Fin (m + 1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)

/-- Half-dead critical pair (`2 ≤ U.card`): `R i` meets all of `U` while `R j` reaches some
`y ∈ U`, equipped with the swapped-family Fisher obstruction, 7-edge exclusion through `R i`,
and global 5-edge exclusion. -/
def H3 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r * r + r - 1 ≤ n →
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
    (∃ i j, i ≠ j ∧ Disjoint (L i) (L j) ∧ (∀ x ∈ U, ¬ Disjoint x (R i)) ∧
      (∃ y ∈ U, Disjoint y (R j) ∧
        ∀ k, k ≠ i → k ≠ j → Disjoint (L k) (R i) → ∀ z ∈ U, z ≠ y → ¬ Disjoint z (R k)) ∧
      ((∃ k, k ≠ i ∧ k ≠ j ∧ Disjoint (L k) (R i)) ∨
       (∃ a b, a ≠ i ∧ b ≠ i ∧ a ≠ b ∧ Disjoint (L a) (L b)))) →
    ∃ l r' : Fin (m + 1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)

-- ### Part 4: Main reduction proof

theorem main : H1 → H2 → H3 → OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1.H1 := by
  intro h1 h2 h3 n r K hr gap pack witness size linear degree many disorder nonsplit tri
    m L R U lk rk il ir apart matched sub um lm lo ro count total band weight deadPair
  obtain ⟨i, j, ij, mid, hdead⟩ := deadPair
  by_cases hUsmall : U.card ≤ 1
  · exfalso
    have hKbig : 2 * n + 1 ≤ K.card := by omega
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
    have hle2n := h1 n r K hr h2r2 hnr ⟨T, hT, hTcard⟩ size linear degree many disorder nonsplit tri
    omega
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
      have hswap := dead_mate_fisher_swap K U L R lk rk il apart matched sub um lm lo ro
        (fun A hA => by have := size A hA; omega) linear tri (by omega) i j ij mid hdead
      by_cases hlive : ∃ y ∈ U, Disjoint y (R j)
      · obtain ⟨y, hy, hyRj⟩ := hlive
        by_cases hseven : ∃ k : Fin m, k ≠ i ∧ k ≠ j ∧ Disjoint (L k) (R i) ∧
            ∃ z ∈ U, z ≠ y ∧ Disjoint z (R k)
        · obtain ⟨k, hki, hkj, hLkRi, z, hz, hzy, hzRk⟩ := hseven
          exact augment_seven K L R lk rk il ir apart matched i j k ij hki.symm hkj.symm y z
            (sub hy) (sub hz) hzy.symm
            (fun t h => lo t (h ▸ hy)) (fun t h => ro t (h ▸ hy))
            (fun t h => lo t (h ▸ hz)) (fun t h => ro t (h ▸ hz))
            hyRj mid hLkRi hzRk
        · push Not at hseven
          exact h3 n r K hr gap pack witness size linear degree many disorder nonsplit tri
            m L R U lk rk il ir apart matched sub hU2 um lm lo ro count total band weight hfive'
            ⟨i, j, ij, mid, hdead, ⟨y, hy, hyRj, hseven⟩, hswap⟩
      · push Not at hlive
        exact h2 n r K hr gap pack witness size linear degree many disorder nonsplit tri
          m L R U lk rk il ir apart matched sub hU2 um lm lo ro count total band weight hfive'
          ⟨i, j, ij, mid, fun x hx => ⟨hdead x hx, hlive x hx⟩, hswap⟩

end OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1_H1_R1
