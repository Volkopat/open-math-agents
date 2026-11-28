import OMAReductions.R_Erdos722_erdos_722_R1

/-!
# Integral Designs (Wilson 1973 / Graver–Jurkat 1973)

We prove `OMA.R_Erdos722_erdos_722_R1.H3`: whenever `r ≤ k`, `k + r ≤ n`, and
`(k - i).choose (r - i) ∣ (n - i).choose (r - i)` for all `i < r`, there exists an
integer-valued weight function `φ : Finset (Fin n) → ℤ` on `k`-subsets of `Fin n`
whose shadow on every `r`-subset is `1`.

More generally, every integer-valued vector `v` on `r`-subsets satisfying the shadow
divisibility conditions lies in the integer column space of the `(r, k)` inclusion
matrix. The proof proceeds by induction on `r` and `n - (k + r)`, with the square
base case `n = k + r` solved explicitly by Boolean Möbius inversion on complements.
-/

namespace OMA.Erdos722H3

open Finset

private def U (n t : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard t

private def IsAdmissible (n k r : ℕ) (v : Finset (Fin n) → ℤ) : Prop :=
  ∀ i ≤ r, ∀ I ∈ U n i,
    ((k - i).choose (r - i) : ℤ) ∣ ∑ A ∈ U n r, if I ⊆ A then v A else 0

private lemma sum_powerset_neg_one_pow {α : Type*} [DecidableEq α] (D : Finset α) :
    ∑ I ∈ D.powerset, (-1 : ℤ) ^ I.card = if D = ∅ then 1 else 0 := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · have hneg : ∑ x ∈ s.powerset, (-1 : ℤ) ^ (insert a x).card =
            - ∑ x ∈ s.powerset, (-1 : ℤ) ^ x.card := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hax : a ∉ x := fun h => ha (Finset.mem_powerset.mp hx h)
          rw [Finset.card_insert_of_notMem hax, pow_succ, mul_neg_one]
        rw [hneg, add_neg_cancel, if_neg (Finset.insert_ne_empty a s)]
      · intro x hx y hy hxy
        have hax : a ∉ x := fun h => ha (Finset.mem_powerset.mp hx h)
        have hay : a ∉ y := fun h => ha (Finset.mem_powerset.mp hy h)
        have := congrArg (fun t => t.erase a) hxy
        simpa [Finset.erase_insert hax, Finset.erase_insert hay] using this
    · rw [Finset.disjoint_left]
      intro x hx hy
      rcases Finset.mem_image.mp hy with ⟨y, _, rfl⟩
      exact ha (Finset.mem_powerset.mp hx (Finset.mem_insert_self a y))

private lemma card_powersetCard_filter_subset {α : Type*} [DecidableEq α]
    (B I : Finset α) (t : ℕ) (hIB : I ⊆ B) (hIt : I.card ≤ t) :
    ((B.powersetCard t).filter (fun A => I ⊆ A)).card =
      (B.card - I.card).choose (t - I.card) := by
  have hbij : ((B.powersetCard t).filter (fun A => I ⊆ A)).card =
      ((B \ I).powersetCard (t - I.card)).card := by
    refine Finset.card_bij (fun A _ => A \ I) ?_ ?_ ?_
    · intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hA1, hIA⟩
      rcases Finset.mem_powersetCard.mp hA1 with ⟨hAB, hAc⟩
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.sdiff_subset_sdiff hAB (Finset.Subset.refl I), ?_⟩
      rw [Finset.card_sdiff_of_subset hIA, hAc]
    · intro A₁ hA₁ A₂ hA₂ heq
      have h1 : I ⊆ A₁ := (Finset.mem_filter.mp hA₁).2
      have h2 : I ⊆ A₂ := (Finset.mem_filter.mp hA₂).2
      rw [← Finset.union_sdiff_of_subset h1, ← Finset.union_sdiff_of_subset h2, heq]
    · intro S hS
      rcases Finset.mem_powersetCard.mp hS with ⟨hSsub, hSc⟩
      have hdisj : Disjoint I S :=
        Finset.disjoint_left.mpr fun x hxI hxS => (Finset.mem_sdiff.mp (hSsub hxS)).2 hxI
      refine ⟨I ∪ S, ?_, Finset.union_sdiff_cancel_left hdisj⟩
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.union_subset hIB (hSsub.trans Finset.sdiff_subset), ?_⟩,
        Finset.subset_union_left⟩
      rw [Finset.card_union_of_disjoint hdisj, hSc]
      omega
  rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset hIB]

private lemma card_U_filter_subset {n t : ℕ} (I : Finset (Fin n)) (hIt : I.card ≤ t) :
    ((U n t).filter (fun A => I ⊆ A)).card = (n - I.card).choose (t - I.card) := by
  simpa [U] using card_powersetCard_filter_subset (Finset.univ : Finset (Fin n)) I t
    (Finset.subset_univ I) hIt

private lemma card_U_filter_disjoint_subset {n k r : ℕ} (hn : k + r = n)
    (A I : Finset (Fin n)) (hA : A.card = r) (hdisj : Disjoint A I) (hIr : I.card ≤ r) :
    ((U n r).filter (fun C => Disjoint A C ∧ I ⊆ C)).card =
      (k - I.card).choose (r - I.card) := by
  have hsub : I ⊆ Aᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    exact Finset.disjoint_right.mp hdisj hx
  have heq : (U n r).filter (fun C => Disjoint A C ∧ I ⊆ C) =
      (Aᶜ.powersetCard r).filter (fun C => I ⊆ C) := by
    ext C
    simp only [U, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨hC, hAC, hIC⟩
      exact ⟨⟨Finset.subset_compl_iff_disjoint_left.mpr hAC, hC⟩, hIC⟩
    · rintro ⟨⟨hCsub, hC⟩, hIC⟩
      exact ⟨hC, Finset.subset_compl_iff_disjoint_left.mp hCsub, hIC⟩
  rw [heq, card_powersetCard_filter_subset Aᶜ I r hsub hIr, Finset.card_compl, Fintype.card_fin, hA]
  have : n - r = k := by omega
  rw [this]

private lemma isAdmissible_image {n k r : ℕ} (φ : Finset (Fin n) → ℤ) :
    IsAdmissible n k r (fun A => ∑ B ∈ U n k, if A ⊆ B then φ B else 0) := by
  intro i hi I hI
  have hIc : I.card = i := (Finset.mem_powersetCard.mp hI).2
  have hswap : (∑ A ∈ U n r, if I ⊆ A then (∑ B ∈ U n k, if A ⊆ B then φ B else 0) else 0) =
      ∑ B ∈ U n k, if I ⊆ B then
        ((B.powersetCard r).filter (fun A => I ⊆ A)).card * φ B else 0 := by
    calc
      (∑ A ∈ U n r, if I ⊆ A then (∑ B ∈ U n k, if A ⊆ B then φ B else 0) else 0)
          = ∑ A ∈ U n r, ∑ B ∈ U n k, if I ⊆ A ∧ A ⊆ B then φ B else 0 := by
              refine Finset.sum_congr rfl fun A _ => ?_
              by_cases h : I ⊆ A <;> simp [h]
      _ = ∑ B ∈ U n k, ∑ A ∈ U n r, if I ⊆ A ∧ A ⊆ B then φ B else 0 := Finset.sum_comm
      _ = ∑ B ∈ U n k, if I ⊆ B then
            ((B.powersetCard r).filter (fun A => I ⊆ A)).card * φ B else 0 := by
            refine Finset.sum_congr rfl fun B hB => ?_
            by_cases hIB : I ⊆ B
            · rw [if_pos hIB]
              have hfilt : (U n r).filter (fun A => I ⊆ A ∧ A ⊆ B) =
                  (B.powersetCard r).filter (fun A => I ⊆ A) := by
                ext A
                simp only [U, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
                  true_and]
                tauto
              rw [← Finset.sum_filter, hfilt, Finset.sum_const, nsmul_eq_mul]
            · rw [if_neg hIB]
              refine Finset.sum_eq_zero fun A _ => ?_
              rw [if_neg]
              rintro ⟨h1, h2⟩
              exact hIB (h1.trans h2)
  rw [hswap]
  refine Finset.dvd_sum fun B hB => ?_
  by_cases hIB : I ⊆ B
  · rw [if_pos hIB]
    have hBc : B.card = k := (Finset.mem_powersetCard.mp hB).2
    rw [card_powersetCard_filter_subset B I r hIB (by omega), hBc, hIc]
    exact dvd_mul_right _ _
  · rw [if_neg hIB]
    exact dvd_zero _

private lemma isAdmissible_sub {n k r : ℕ} {v₁ v₂ : Finset (Fin n) → ℤ}
    (h1 : IsAdmissible n k r v₁) (h2 : IsAdmissible n k r v₂) :
    IsAdmissible n k r (fun A => v₁ A - v₂ A) := by
  intro i hi I hI
  have hsplit : (∑ A ∈ U n r, if I ⊆ A then (v₁ A - v₂ A) else 0) =
      (∑ A ∈ U n r, if I ⊆ A then v₁ A else 0) - (∑ A ∈ U n r, if I ⊆ A then v₂ A else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    split_ifs <;> ring
  rw [hsplit]
  exact dvd_sub (h1 i hi I hI) (h2 i hi I hI)

private lemma solve_base_eq {n k r : ℕ} (hn : k + r = n)
    (v : Finset (Fin n) → ℤ) (hv : IsAdmissible n k r v) :
    ∃ φ : Finset (Fin n) → ℤ, ∀ A ∈ U n r,
      (∑ B ∈ U n k, if A ⊆ B then φ B else 0) = v A := by
  let S : Finset (Fin n) → ℤ := fun I => ∑ A ∈ U n r, if I ⊆ A then v A else 0
  let T : Finset (Fin n) → ℤ := fun I => S I / ((k - I.card).choose (r - I.card) : ℤ)
  let φ : Finset (Fin n) → ℤ := fun B => ∑ I ∈ Bᶜ.powerset, (-1 : ℤ) ^ I.card * T I
  refine ⟨φ, fun A hA => ?_⟩
  have hAc : A.card = r := (Finset.mem_powersetCard.mp hA).2
  have hcompl : (∑ B ∈ U n k, if A ⊆ B then φ B else 0) =
      ∑ C ∈ U n r, if Disjoint A C then ∑ I ∈ C.powerset, (-1 : ℤ) ^ I.card * T I else 0 := by
    refine Finset.sum_bij (fun B _ => Bᶜ) ?_ ?_ ?_ ?_
    · intro B hB
      have hBc : B.card = k := (Finset.mem_powersetCard.mp hB).2
      rw [U, Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_compl, Fintype.card_fin, hBc]
      omega
    · intro B₁ _ B₂ _ h
      exact compl_injective h
    · intro C hC
      have hCc : C.card = r := (Finset.mem_powersetCard.mp hC).2
      refine ⟨Cᶜ, ?_, compl_compl C⟩
      rw [U, Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_compl, Fintype.card_fin, hCc]
      omega
    · intro B _
      have hiff : A ⊆ B ↔ Disjoint A Bᶜ := by
        rw [← Finset.subset_compl_iff_disjoint_right, compl_compl]
      simp only [φ, hiff]
  rw [hcompl]
  let P : Finset (Finset (Fin n)) := Aᶜ.powerset.filter (fun I => I.card ≤ r)
  have hstep1 :
      (∑ C ∈ U n r, if Disjoint A C then ∑ I ∈ C.powerset, (-1 : ℤ) ^ I.card * T I else 0) =
      ∑ I ∈ P, (-1 : ℤ) ^ I.card * S I := by
    calc
      (∑ C ∈ U n r, if Disjoint A C then ∑ I ∈ C.powerset, (-1 : ℤ) ^ I.card * T I else 0)
          = ∑ C ∈ U n r, ∑ I ∈ P,
              if Disjoint A C ∧ I ⊆ C then (-1 : ℤ) ^ I.card * T I else 0 := by
            refine Finset.sum_congr rfl fun C hC => ?_
            have hCc : C.card = r := (Finset.mem_powersetCard.mp hC).2
            by_cases hAC : Disjoint A C
            · rw [if_pos hAC]
              have hsub : C.powerset ⊆ P := by
                intro I hI
                have hIC : I ⊆ C := Finset.mem_powerset.mp hI
                rw [Finset.mem_filter, Finset.mem_powerset]
                refine ⟨hIC.trans (Finset.subset_compl_iff_disjoint_left.mpr hAC), ?_⟩
                exact (Finset.card_le_card hIC).trans hCc.le
              rw [← Finset.sum_subset hsub]
              · refine Finset.sum_congr rfl fun I hI => ?_
                rw [if_pos ⟨hAC, Finset.mem_powerset.mp hI⟩]
              · intro I _ hInot
                rw [if_neg]
                rintro ⟨_, hIC⟩
                exact hInot (Finset.mem_powerset.mpr hIC)
            · rw [if_neg hAC]
              symm
              refine Finset.sum_eq_zero fun I _ => ?_
              rw [if_neg (fun h => hAC h.1)]
      _ = ∑ I ∈ P, ∑ C ∈ U n r,
            if Disjoint A C ∧ I ⊆ C then (-1 : ℤ) ^ I.card * T I else 0 := Finset.sum_comm
      _ = ∑ I ∈ P, (-1 : ℤ) ^ I.card * S I := by
            refine Finset.sum_congr rfl fun I hI => ?_
            rcases Finset.mem_filter.mp hI with ⟨hIAc, hIr⟩
            have hdisjAI : Disjoint A I :=
              Finset.subset_compl_iff_disjoint_left.mp (Finset.mem_powerset.mp hIAc)
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
              card_U_filter_disjoint_subset hn A I hAc hdisjAI hIr]
            have hIinU : I ∈ U n I.card := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ I, rfl⟩
            have hdvd : ((k - I.card).choose (r - I.card) : ℤ) ∣ S I := hv I.card hIr I hIinU
            have hmul : T I * ((k - I.card).choose (r - I.card) : ℤ) = S I :=
              Int.ediv_mul_cancel hdvd
            calc
              (((k - I.card).choose (r - I.card) : ℕ) : ℤ) * ((-1 : ℤ) ^ I.card * T I)
                  = (-1 : ℤ) ^ I.card * (T I * ((k - I.card).choose (r - I.card) : ℤ)) := by ring
              _ = (-1 : ℤ) ^ I.card * S I := by rw [hmul]
  rw [hstep1]
  have hstep2 : (∑ I ∈ P, (-1 : ℤ) ^ I.card * S I) =
      ∑ A' ∈ U n r, v A' * (∑ I ∈ (A' \ A).powerset, (-1 : ℤ) ^ I.card) := by
    calc
      (∑ I ∈ P, (-1 : ℤ) ^ I.card * S I)
          = ∑ I ∈ P, ∑ A' ∈ U n r, if I ⊆ A' then (-1 : ℤ) ^ I.card * v A' else 0 := by
            refine Finset.sum_congr rfl fun I _ => ?_
            simp only [S, Finset.mul_sum]
            refine Finset.sum_congr rfl fun A' _ => ?_
            split_ifs <;> ring
      _ = ∑ A' ∈ U n r, ∑ I ∈ P, if I ⊆ A' then (-1 : ℤ) ^ I.card * v A' else 0 := Finset.sum_comm
      _ = ∑ A' ∈ U n r, v A' * (∑ I ∈ (A' \ A).powerset, (-1 : ℤ) ^ I.card) := by
            refine Finset.sum_congr rfl fun A' hA' => ?_
            have hA'c : A'.card = r := (Finset.mem_powersetCard.mp hA').2
            have hsub : (A' \ A).powerset ⊆ P := by
              intro I hI
              have hIsdiff : I ⊆ A' \ A := Finset.mem_powerset.mp hI
              rw [Finset.mem_filter, Finset.mem_powerset]
              refine ⟨?_, (Finset.card_le_card (hIsdiff.trans Finset.sdiff_subset)).trans hA'c.le⟩
              intro x hx
              rw [Finset.mem_compl]
              exact (Finset.mem_sdiff.mp (hIsdiff hx)).2
            rw [Finset.mul_sum, ← Finset.sum_subset hsub]
            · refine Finset.sum_congr rfl fun I hI => ?_
              have hIA' : I ⊆ A' := (Finset.mem_powerset.mp hI).trans Finset.sdiff_subset
              rw [if_pos hIA', mul_comm]
            · intro I hIP hInot
              rw [if_neg]
              intro hIA'
              apply hInot
              rw [Finset.mem_powerset]
              have hIAc : I ⊆ Aᶜ := Finset.mem_powerset.mp (Finset.mem_filter.mp hIP).1
              intro x hx
              exact Finset.mem_sdiff.mpr ⟨hIA' hx, Finset.mem_compl.mp (hIAc hx)⟩
  rw [hstep2]
  have hstep3 : (∑ A' ∈ U n r, v A' * (∑ I ∈ (A' \ A).powerset, (-1 : ℤ) ^ I.card)) =
      ∑ A' ∈ U n r, if A' = A then v A' else 0 := by
    refine Finset.sum_congr rfl fun A' hA' => ?_
    rw [sum_powerset_neg_one_pow]
    have hA'c : A'.card = r := (Finset.mem_powersetCard.mp hA').2
    have hiff : A' \ A = ∅ ↔ A' = A := by
      rw [Finset.sdiff_eq_empty_iff_subset]
      exact ⟨fun h => Finset.eq_of_subset_of_card_le h (by omega), fun h => h ▸ Finset.Subset.refl A⟩
    by_cases hEq : A' = A
    · rw [if_pos (hiff.mpr hEq), if_pos hEq, mul_one]
    · rw [if_neg (fun h => hEq (hiff.mp h)), if_neg hEq, mul_zero]
  rw [hstep3, Finset.sum_ite_eq' (U n r) A v, if_pos hA]

private def liftWith {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  insert (Fin.last n) (S.map Fin.castSuccEmb)

private def liftWithout {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.map Fin.castSuccEmb

private noncomputable def dropTop {n : ℕ} (A : Finset (Fin (n + 1))) : Finset (Fin n) :=
  A.preimage Fin.castSucc (Fin.castSucc_injective n).injOn

private lemma last_notMem_liftWithout {n : ℕ} (S : Finset (Fin n)) :
    Fin.last n ∉ liftWithout S := by
  simp [liftWithout, Fin.castSucc_ne_last]

private lemma card_liftWithout {n : ℕ} (S : Finset (Fin n)) :
    (liftWithout S).card = S.card :=
  Finset.card_map _

private lemma card_liftWith {n : ℕ} (S : Finset (Fin n)) :
    (liftWith S).card = S.card + 1 := by
  have hnot : Fin.last n ∉ S.map Fin.castSuccEmb := last_notMem_liftWithout S
  rw [liftWith, Finset.card_insert_of_notMem hnot, Finset.card_map]

private lemma dropTop_liftWithout {n : ℕ} (S : Finset (Fin n)) :
    dropTop (liftWithout S) = S := by
  ext x
  simp [dropTop, liftWithout]

private lemma dropTop_liftWith {n : ℕ} (S : Finset (Fin n)) :
    dropTop (liftWith S) = S := by
  ext x
  simp [dropTop, liftWith, (Fin.castSucc_ne_last x)]

private lemma liftWithout_dropTop {n : ℕ} {A : Finset (Fin (n + 1))} (h : Fin.last n ∉ A) :
    liftWithout (dropTop A) = A := by
  ext y
  refine Fin.lastCases ?_ (fun i => ?_) y
  · simp [liftWithout, h, Fin.castSucc_ne_last]
  · simp [liftWithout, dropTop]

private lemma liftWith_dropTop {n : ℕ} {A : Finset (Fin (n + 1))} (h : Fin.last n ∈ A) :
    liftWith (dropTop A) = A := by
  ext y
  refine Fin.lastCases ?_ (fun i => ?_) y
  · simp [liftWith, h]
  · simp [liftWith, dropTop, Fin.castSucc_ne_last]

private lemma liftWithout_subset_liftWithout {n : ℕ} {S T : Finset (Fin n)} :
    liftWithout S ⊆ liftWithout T ↔ S ⊆ T := by
  simp [liftWithout]

private lemma liftWith_subset_liftWith {n : ℕ} {S T : Finset (Fin n)} :
    liftWith S ⊆ liftWith T ↔ S ⊆ T := by
  constructor
  · intro h x hx
    have hmem : Fin.castSucc x ∈ liftWith T :=
      h (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨x, hx, rfl⟩))
    rcases Finset.mem_insert.mp hmem with heq | hmap
    · exact absurd heq (Fin.castSucc_ne_last x)
    · rcases Finset.mem_map.mp hmap with ⟨y, hy, hyx⟩
      exact (Fin.castSucc_injective n hyx) ▸ hy
  · intro h
    exact Finset.insert_subset_insert _ (Finset.map_subset_map.mpr h)

private lemma liftWithout_subset_liftWith {n : ℕ} {S T : Finset (Fin n)} :
    liftWithout S ⊆ liftWith T ↔ S ⊆ T := by
  constructor
  · intro h x hx
    have hmem : Fin.castSucc x ∈ liftWith T := h (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
    rcases Finset.mem_insert.mp hmem with heq | hmap
    · exact absurd heq (Fin.castSucc_ne_last x)
    · rcases Finset.mem_map.mp hmap with ⟨y, hy, hyx⟩
      exact (Fin.castSucc_injective n hyx) ▸ hy
  · intro h
    exact (Finset.map_subset_map.mpr h).trans (Finset.subset_insert _ _)

private lemma sum_U_split_top {n t : ℕ} (ht : 1 ≤ t) (f : Finset (Fin (n + 1)) → ℤ) :
    (∑ A ∈ U (n + 1) t, f A) =
      (∑ A' ∈ U n (t - 1), f (liftWith A')) + (∑ A' ∈ U n t, f (liftWithout A')) := by
  rw [← Finset.sum_filter_add_sum_filter_not (U (n + 1) t) (fun A => Fin.last n ∈ A)]
  congr 1
  · refine Finset.sum_bij (fun A _ => dropTop A) ?_ ?_ ?_ ?_
    · intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hAU, htop⟩
      have hAc : A.card = t := (Finset.mem_powersetCard.mp hAU).2
      rw [U, Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      have hcard := card_liftWith (dropTop A)
      rw [liftWith_dropTop htop, hAc] at hcard
      omega
    · intro A₁ hA₁ A₂ hA₂ heq
      rw [← liftWith_dropTop (Finset.mem_filter.mp hA₁).2,
        ← liftWith_dropTop (Finset.mem_filter.mp hA₂).2, heq]
    · intro A' hA'
      have hA'c : A'.card = t - 1 := (Finset.mem_powersetCard.mp hA').2
      refine ⟨liftWith A', ?_, dropTop_liftWith A'⟩
      rw [Finset.mem_filter, U, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self _ _⟩
      rw [card_liftWith, hA'c]
      omega
    · intro A hA
      rw [liftWith_dropTop (Finset.mem_filter.mp hA).2]
  · refine Finset.sum_bij (fun A _ => dropTop A) ?_ ?_ ?_ ?_
    · intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hAU, htop⟩
      have hAc : A.card = t := (Finset.mem_powersetCard.mp hAU).2
      rw [U, Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      have hcard := card_liftWithout (dropTop A)
      rw [liftWithout_dropTop htop, hAc] at hcard
      exact hcard.symm
    · intro A₁ hA₁ A₂ hA₂ heq
      rw [← liftWithout_dropTop (Finset.mem_filter.mp hA₁).2,
        ← liftWithout_dropTop (Finset.mem_filter.mp hA₂).2, heq]
    · intro A' hA'
      have hA'c : A'.card = t := (Finset.mem_powersetCard.mp hA').2
      refine ⟨liftWithout A', ?_, dropTop_liftWithout A'⟩
      rw [Finset.mem_filter, U, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, (card_liftWithout A').trans hA'c⟩, last_notMem_liftWithout A'⟩
    · intro A hA
      rw [liftWithout_dropTop (Finset.mem_filter.mp hA).2]

private lemma solve_general :
    ∀ r m k : ℕ, r ≤ k → ∀ v : Finset (Fin (k + r + m)) → ℤ,
      IsAdmissible (k + r + m) k r v →
      ∃ φ : Finset (Fin (k + r + m)) → ℤ, ∀ A ∈ U (k + r + m) r,
        (∑ B ∈ U (k + r + m) k, if A ⊆ B then φ B else 0) = v A := by
  intro r
  induction r with
  | zero =>
    intro m k _ v _
    have hk : k ≤ (Finset.univ : Finset (Fin (k + 0 + m))).card := by
      simp
    obtain ⟨B₀, _, hB₀c⟩ := Finset.exists_subset_card_eq hk
    have hB₀U : B₀ ∈ U (k + 0 + m) k := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ B₀, hB₀c⟩
    refine ⟨fun B => if B = B₀ then v ∅ else 0, fun A hA => ?_⟩
    have hAempty : A = ∅ := Finset.card_eq_zero.mp (Finset.mem_powersetCard.mp hA).2
    subst hAempty
    have hsimp : (∑ B ∈ U (k + 0 + m) k, if ∅ ⊆ B then (if B = B₀ then v ∅ else 0) else 0) =
        ∑ B ∈ U (k + 0 + m) k, if B = B₀ then v ∅ else 0 :=
      Finset.sum_congr rfl fun B _ => by simp
    rw [hsimp, Finset.sum_ite_eq', if_pos hB₀U]
  | succ r ihr =>
    intro m
    induction m with
    | zero =>
      intro k _ v hv
      exact solve_base_eq (by omega) v hv
    | succ m ihm =>
      intro k hrk v hv
      have hk1 : 1 ≤ k := by omega
      let n' := k + (r + 1) + m
      have hn'_eq : k + (r + 1) + (m + 1) = n' + 1 := by dsimp [n']; omega
      let k' := k - 1
      have hk'_eq : k' + 1 = k := by dsimp [k']; omega
      have h_inner_n : k' + r + (m + 2) = n' := by dsimp [n', k']; omega
      -- Step 1: Solve the top link at (n', k - 1, r)
      let vTop : Finset (Fin n') → ℤ := fun A' => v (liftWith A')
      have hvTop : IsAdmissible n' k' r vTop := by
        intro i hi I' hI'
        have hI'c : I'.card = i := (Finset.mem_powersetCard.mp hI').2
        have hI_in : liftWith I' ∈ U (n' + 1) (i + 1) := by
          rw [U, Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, by rw [card_liftWith, hI'c]⟩
        have hdvd := hv (i + 1) (by omega) (liftWith I') hI_in
        have hchoose : (k - (i + 1)).choose (r + 1 - (i + 1)) = (k' - i).choose (r - i) := by
          congr 1 <;> omega
        rw [hchoose] at hdvd
        have hsum_eq : (∑ A ∈ U (n' + 1) (r + 1), if liftWith I' ⊆ A then v A else 0) =
            ∑ A' ∈ U n' r, if I' ⊆ A' then vTop A' else 0 := by
          rw [sum_U_split_top (by omega)]
          have hzero : (∑ A' ∈ U n' (r + 1), if liftWith I' ⊆ liftWithout A' then
              v (liftWithout A') else 0) = 0 := by
            refine Finset.sum_eq_zero fun A' _ => ?_
            rw [if_neg]
            intro hsub
            exact last_notMem_liftWithout A' (hsub (Finset.mem_insert_self _ _))
          rw [hzero, add_zero]
          refine Finset.sum_congr rfl fun A' _ => ?_
          simp only [vTop, liftWith_subset_liftWith]
        rwa [← hsum_eq]
      have h_ihr := ihr (m + 2) k' (by omega)
      rw [h_inner_n] at h_ihr
      obtain ⟨ψ, hψ⟩ := h_ihr vTop hvTop
      -- Step 2: Lift ψ to φ₁ on sets containing top
      let φ₁ : Finset (Fin (n' + 1)) → ℤ := fun B => if Fin.last n' ∈ B then ψ (dropTop B) else 0
      let w : Finset (Fin (n' + 1)) → ℤ :=
        fun A => v A - ∑ B ∈ U (n' + 1) k, if A ⊆ B then φ₁ B else 0
      have hw_top_zero : ∀ A' ∈ U n' r, w (liftWith A') = 0 := by
        intro A' hA'
        dsimp only [w]
        have hsum : (∑ B ∈ U (n' + 1) k, if liftWith A' ⊆ B then φ₁ B else 0) = vTop A' := by
          rw [sum_U_split_top hk1]
          have hzero : (∑ B' ∈ U n' k,
              if liftWith A' ⊆ liftWithout B' then φ₁ (liftWithout B') else 0) = 0 := by
            refine Finset.sum_eq_zero fun B' _ => ?_
            rw [if_neg]
            intro hsub
            exact last_notMem_liftWithout B' (hsub (Finset.mem_insert_self _ _))
          rw [hzero, add_zero]
          have hcong : (∑ B' ∈ U n' (k - 1),
              if liftWith A' ⊆ liftWith B' then φ₁ (liftWith B') else 0) =
              ∑ B' ∈ U n' k', if A' ⊆ B' then ψ B' else 0 := by
            refine Finset.sum_congr rfl fun B' _ => ?_
            have hmem : Fin.last n' ∈ liftWith B' := Finset.mem_insert_self _ _
            simp only [φ₁, if_pos hmem, liftWith_subset_liftWith, dropTop_liftWith]
          rw [hcong]
          exact hψ A' hA'
        rw [hsum]
        dsimp only [vTop]
        ring
      have hw_adm : IsAdmissible (n' + 1) k (r + 1) w :=
        isAdmissible_sub hv (isAdmissible_image φ₁)
      -- Step 3: Restrict w to Fin n' and solve by inner IH
      let wBot : Finset (Fin n') → ℤ := fun A' => w (liftWithout A')
      have hwBot_adm : IsAdmissible n' k (r + 1) wBot := by
        intro i hi I' hI'
        have hI'c : I'.card = i := (Finset.mem_powersetCard.mp hI').2
        have hI_in : liftWithout I' ∈ U (n' + 1) i := by
          rw [U, Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, (card_liftWithout I').trans hI'c⟩
        have hdvd := hw_adm i hi (liftWithout I') hI_in
        have hsum_eq : (∑ A ∈ U (n' + 1) (r + 1), if liftWithout I' ⊆ A then w A else 0) =
            ∑ A' ∈ U n' (r + 1), if I' ⊆ A' then wBot A' else 0 := by
          rw [sum_U_split_top (by omega)]
          have hsub1 : r + 1 - 1 = r := rfl
          rw [hsub1]
          have hzero : (∑ A' ∈ U n' r,
              if liftWithout I' ⊆ liftWith A' then w (liftWith A') else 0) = 0 := by
            refine Finset.sum_eq_zero fun A' hA' => ?_
            rw [hw_top_zero A' hA', ite_self]
          rw [hzero, zero_add]
          refine Finset.sum_congr rfl fun A' _ => ?_
          simp only [wBot, liftWithout_subset_liftWithout]
        rwa [← hsum_eq]
      obtain ⟨φ₂, hφ₂⟩ := ihm k hrk wBot hwBot_adm
      -- Step 4: Lift φ₂ to φ₂' on sets avoiding top, and combine φ = φ₁ + φ₂'
      let φ₂' : Finset (Fin (n' + 1)) → ℤ := fun B => if Fin.last n' ∉ B then φ₂ (dropTop B) else 0
      refine ⟨fun B => φ₁ B + φ₂' B, fun A hA => ?_⟩
      change (∑ B ∈ U (n' + 1) k, if A ⊆ B then φ₁ B + φ₂' B else 0) = v A
      have hsplit_sum : (∑ B ∈ U (n' + 1) k, if A ⊆ B then (φ₁ B + φ₂' B) else 0) =
          (∑ B ∈ U (n' + 1) k, if A ⊆ B then φ₁ B else 0) +
          (∑ B ∈ U (n' + 1) k, if A ⊆ B then φ₂' B else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun B _ => ?_
        split_ifs <;> ring
      rw [hsplit_sum]
      by_cases htop : Fin.last n' ∈ A
      · have hA' : dropTop A ∈ U n' r := by
          rw [U, Finset.mem_powersetCard]
          refine ⟨Finset.subset_univ _, ?_⟩
          have hAc : A.card = r + 1 := (Finset.mem_powersetCard.mp hA).2
          have hc := card_liftWith (dropTop A)
          rw [liftWith_dropTop htop, hAc] at hc
          omega
        have h1 : (∑ B ∈ U (n' + 1) k, if A ⊆ B then φ₁ B else 0) = v A := by
          have h0 := hw_top_zero (dropTop A) hA'
          rw [liftWith_dropTop htop] at h0
          dsimp only [w] at h0
          linarith
        have h2 : (∑ B ∈ U (n' + 1) k, if A ⊆ B then φ₂' B else 0) = 0 := by
          refine Finset.sum_eq_zero fun B _ => ?_
          by_cases hAB : A ⊆ B
          · rw [if_pos hAB]
            simp [φ₂', hAB htop]
          · rw [if_neg hAB]
        rw [h1, h2, add_zero]
      · have hA' : dropTop A ∈ U n' (r + 1) := by
          rw [U, Finset.mem_powersetCard]
          refine ⟨Finset.subset_univ _, ?_⟩
          have hAc : A.card = r + 1 := (Finset.mem_powersetCard.mp hA).2
          have hc := card_liftWithout (dropTop A)
          rw [liftWithout_dropTop htop, hAc] at hc
          exact hc.symm
        have h2 : (∑ B ∈ U (n' + 1) k, if A ⊆ B then φ₂' B else 0) = w A := by
          rw [sum_U_split_top hk1]
          have hzero : (∑ B' ∈ U n' (k - 1),
              if A ⊆ liftWith B' then φ₂' (liftWith B') else 0) = 0 := by
            refine Finset.sum_eq_zero fun B' _ => ?_
            simp [φ₂', liftWith]
          rw [hzero, zero_add]
          have hcong : (∑ B' ∈ U n' k,
              if A ⊆ liftWithout B' then φ₂' (liftWithout B') else 0) =
              ∑ B' ∈ U n' k, if dropTop A ⊆ B' then φ₂ B' else 0 := by
            refine Finset.sum_congr rfl fun B' _ => ?_
            have hiff : A ⊆ liftWithout B' ↔ dropTop A ⊆ B' := by
              conv_lhs => rw [← liftWithout_dropTop htop]
              exact liftWithout_subset_liftWithout
            simp only [hiff, φ₂', last_notMem_liftWithout, not_false_eq_true, ↓reduceIte,
              dropTop_liftWithout]
          rw [hcong, hφ₂ (dropTop A) hA']
          dsimp only [wBot]
          rw [liftWithout_dropTop htop]
        rw [h2]
        dsimp only [w]
        ring

end OMA.Erdos722H3

theorem OMA.solution : OMA.R_Erdos722_erdos_722_R1.H3 := by
  intro n k r hrk hkrn hdvd
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkrn
  have hadm : OMA.Erdos722H3.IsAdmissible (k + r + m) k r (fun _ => 1) := by
    intro i hi I hI
    have hIc : I.card = i := (Finset.mem_powersetCard.mp hI).2
    have hsum : (∑ A ∈ OMA.Erdos722H3.U (k + r + m) r, if I ⊆ A then (1 : ℤ) else 0) =
        (((k + r + m) - i).choose (r - i) : ℤ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
        OMA.Erdos722H3.card_U_filter_subset I (by omega), hIc]
    rw [hsum]
    by_cases hir : i < r
    · exact Int.ofNat_dvd.mpr (hdvd i hir)
    · have hieq : i = r := by omega
      subst hieq
      simp
  obtain ⟨φ, hφ⟩ := OMA.Erdos722H3.solve_general r m k hrk (fun _ => 1) hadm
  refine ⟨φ, fun A hA => ?_⟩
  rw [if_pos hA]
  exact hφ A hA
