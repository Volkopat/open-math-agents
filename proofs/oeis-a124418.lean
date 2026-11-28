import OMAStatements.S_oeis_a124418
import Mathlib

namespace OMA.S_oeis_a124418

open BigOperators

private lemma mem_setPartitions_iff {α : Type*} [DecidableEq α]
    (S : Finset α) (P : Finset (Finset α)) :
    P ∈ setPartitions S ↔ isSetPartition S P := by
  unfold setPartitions
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  intro B hB
  rw [Finset.mem_powerset]
  intro x hx
  rw [← h.2.2]
  exact Finset.mem_biUnion.mpr ⟨B, hB, hx⟩

private lemma setPartitions_empty {α : Type*} [DecidableEq α] :
    setPartitions (∅ : Finset α) = {∅} := by
  ext P
  rw [mem_setPartitions_iff, Finset.mem_singleton]
  constructor
  · intro ⟨hne, _, hunion⟩
    by_contra hP
    obtain ⟨B, hB⟩ := Finset.nonempty_iff_ne_empty.mpr hP
    obtain ⟨x, hx⟩ := hne B hB
    have : x ∈ (∅ : Finset α) := by
      rw [← hunion]
      exact Finset.mem_biUnion.mpr ⟨B, hB, hx⟩
    exact Finset.notMem_empty x this
  · rintro rfl
    refine ⟨by simp, by simp, by simp⟩

/-- Card of set partitions of `S` with exactly `i` blocks is `stirling2 S.card i`. -/
private lemma card_setPartitions_filter_card {α : Type*} [DecidableEq α] :
    ∀ (S : Finset α) (i : ℕ),
      ((setPartitions S).filter fun P => P.card = i).card = stirling2 S.card i := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro i
      rw [setPartitions_empty, Finset.card_empty]
      cases i with
      | zero => simp [stirling2, Finset.filter_singleton]
      | succ i => simp [stirling2]
  | @insert a s has ih =>
      intro i
      rw [Finset.card_insert_of_notMem has]
      cases i with
      | zero =>
          simp only [stirling2]
          refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun P hP => ?_)
          intro hcard
          have hP0 : P = ∅ := Finset.card_eq_zero.mp hcard
          have hunion := ((mem_setPartitions_iff _ _).mp hP).2.2
          rw [hP0, Finset.biUnion_empty] at hunion
          have : a ∈ (∅ : Finset α) := hunion.symm ▸ Finset.mem_insert_self a s
          exact Finset.notMem_empty a this
      | succ i =>
          simp only [stirling2]
          set All := (setPartitions (insert a s)).filter fun P => P.card = i + 1
          set A := All.filter fun P => ({a} : Finset α) ∈ P
          set B := All.filter fun P => ({a} : Finset α) ∉ P
          have hAB : All.card = A.card + B.card := by
            rw [← Finset.card_filter_add_card_filter_not (fun P => ({a} : Finset α) ∈ P)]
          rw [hAB, add_comm]
          congr 1
          · -- `B.card = (i + 1) * stirling2 s.card (i + 1)`
            -- Bijection between `B` and `Σ Q ∈ (setPartitions s).filter (card = i+1), Q`
            -- sending `(Q, blk)` to `insert (insert a blk) (Q.erase blk)`!
            have hcardB :
                B.card =
                  ∑ Q ∈ (setPartitions s).filter (fun Q => Q.card = i + 1), Q.card := by
              have hdisj :
                  B = ((setPartitions s).filter fun Q => Q.card = i + 1).biUnion fun Q =>
                    Q.image fun blk => insert (insert a blk) (Q.erase blk) := by
                ext P
                simp only [B, All, Finset.mem_filter, mem_setPartitions_iff, Finset.mem_biUnion,
                  Finset.mem_image]
                constructor
                · rintro ⟨⟨⟨hne, hpw, hunion⟩, hcard⟩, hnotSing⟩
                  have haU : a ∈ P.biUnion id := hunion.symm ▸ Finset.mem_insert_self a s
                  obtain ⟨blk, hblkP, hablk⟩ := Finset.mem_biUnion.mp haU
                  set blk' := blk.erase a
                  have hblk'_ne : blk'.Nonempty := by
                    by_contra h
                    rw [Finset.not_nonempty_iff_eq_empty] at h
                    have heq : blk = {a} := by
                      ext x
                      simp only [Finset.mem_singleton]
                      constructor
                      · intro hx
                        by_contra hxa
                        have : x ∈ blk' := Finset.mem_erase.mpr ⟨hxa, hx⟩
                        rw [h] at this; exact Finset.notMem_empty x this
                      · rintro rfl; exact hablk
                    exact hnotSing (heq ▸ hblkP)
                  have ha_not_other : ∀ C ∈ P.erase blk, a ∉ C := by
                    intro C hC haC
                    have hneC : C ≠ blk := (Finset.mem_erase.mp hC).1
                    have hCP : C ∈ P := (Finset.mem_erase.mp hC).2
                    exact Finset.disjoint_left.mp (hpw C hCP blk hblkP hneC) haC hablk
                  have hblk'_not : blk' ∉ P.erase blk := by
                    intro hmem
                    obtain ⟨x, hx⟩ := hblk'_ne
                    have hxblk : x ∈ blk := Finset.mem_of_mem_erase hx
                    have hne' : blk' ≠ blk := by
                      intro heq
                      have : a ∈ blk' := heq.symm ▸ hablk
                      exact (Finset.mem_erase.mp this).1 rfl
                    exact Finset.disjoint_left.mp
                      (hpw blk' (Finset.mem_of_mem_erase hmem) blk hblkP hne') hx hxblk
                  set Q := insert blk' (P.erase blk)
                  refine ⟨Q, ⟨⟨?_, ?_, ?_⟩, ?_⟩, blk', Finset.mem_insert_self _ _, ?_⟩
                  · intro C hC
                    rcases Finset.mem_insert.mp hC with rfl | hC'
                    · exact hblk'_ne
                    · exact hne C (Finset.mem_of_mem_erase hC')
                  · intro C₁ hC₁ C₂ hC₂ hne12
                    rcases Finset.mem_insert.mp hC₁ with rfl | hC₁' <;>
                    rcases Finset.mem_insert.mp hC₂ with rfl | hC₂'
                    · exact absurd rfl hne12
                    · exact Finset.disjoint_of_subset_left (Finset.erase_subset a blk)
                        (hpw blk hblkP C₂ (Finset.mem_of_mem_erase hC₂') (Finset.mem_erase.mp hC₂').1.symm)
                    · exact Finset.disjoint_of_subset_right (Finset.erase_subset a blk)
                        (hpw C₁ (Finset.mem_of_mem_erase hC₁') blk hblkP (Finset.mem_erase.mp hC₁').1)
                    · exact hpw C₁ (Finset.mem_of_mem_erase hC₁') C₂ (Finset.mem_of_mem_erase hC₂') hne12
                  · ext x
                    simp only [Q, Finset.mem_biUnion, id_eq, Finset.mem_insert]
                    constructor
                    · rintro ⟨C, rfl | hC', hx⟩
                      · have hxa : x ≠ a := (Finset.mem_erase.mp hx).1
                        have hxs : x ∈ insert a s := hunion ▸ Finset.mem_biUnion.mpr
                          ⟨blk, hblkP, Finset.mem_of_mem_erase hx⟩
                        exact (Finset.mem_insert.mp hxs).resolve_left hxa
                      · have hxa : x ≠ a := fun h => ha_not_other C hC' (h ▸ hx)
                        have hxs : x ∈ insert a s := hunion ▸ Finset.mem_biUnion.mpr
                          ⟨C, Finset.mem_of_mem_erase hC', hx⟩
                        exact (Finset.mem_insert.mp hxs).resolve_left hxa
                    · intro hxs
                      have hxa : x ≠ a := fun h => has (h ▸ hxs)
                      have hxU : x ∈ P.biUnion id := hunion.symm ▸ Finset.mem_insert_of_mem hxs
                      obtain ⟨C, hCP, hxC⟩ := Finset.mem_biUnion.mp hxU
                      by_cases hC : C = blk
                      · subst hC
                        exact ⟨blk', Or.inl rfl, Finset.mem_erase.mpr ⟨hxa, hxC⟩⟩
                      · exact ⟨C, Or.inr (Finset.mem_erase.mpr ⟨hC, hCP⟩), hxC⟩
                  · rw [Finset.card_insert_of_notMem hblk'_not, Finset.card_erase_of_mem hblkP, hcard]
                    omega
                  · rw [Finset.erase_insert hblk'_not]
                    have hablk' : a ∈ blk := hablk
                    rw [show insert a blk' = blk from Finset.insert_erase hablk',
                        Finset.insert_erase hblkP]
                · rintro ⟨Q, ⟨⟨hneQ, hpwQ, hunionQ⟩, hcardQ⟩, blk', hblk'Q, rfl⟩
                  have ha_not_C : ∀ C ∈ Q, a ∉ C := by
                    intro C hC haC
                    exact has (hunionQ ▸ Finset.mem_biUnion.mpr ⟨C, hC, haC⟩)
                  have hnot_mem : insert a blk' ∉ Q.erase blk' := by
                    intro hmem
                    exact ha_not_C (insert a blk') (Finset.mem_of_mem_erase hmem)
                      (Finset.mem_insert_self a blk')
                  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
                  · intro C hC
                    rcases Finset.mem_insert.mp hC with rfl | hC'
                    · exact Finset.insert_nonempty a blk'
                    · exact hneQ C (Finset.mem_of_mem_erase hC')
                  · intro C₁ hC₁ C₂ hC₂ hne12
                    rcases Finset.mem_insert.mp hC₁ with rfl | hC₁' <;>
                    rcases Finset.mem_insert.mp hC₂ with rfl | hC₂'
                    · exact absurd rfl hne12
                    · rw [Finset.disjoint_insert_left]
                      exact ⟨ha_not_C C₂ (Finset.mem_of_mem_erase hC₂'),
                        hpwQ blk' hblk'Q C₂ (Finset.mem_of_mem_erase hC₂') (Finset.mem_erase.mp hC₂').1.symm⟩
                    · rw [Finset.disjoint_insert_right]
                      exact ⟨ha_not_C C₁ (Finset.mem_of_mem_erase hC₁'),
                        hpwQ C₁ (Finset.mem_of_mem_erase hC₁') blk' hblk'Q (Finset.mem_erase.mp hC₁').1⟩
                    · exact hpwQ C₁ (Finset.mem_of_mem_erase hC₁') C₂ (Finset.mem_of_mem_erase hC₂') hne12
                  · ext x
                    simp only [Finset.mem_biUnion, id_eq, Finset.mem_insert]
                    constructor
                    · rintro ⟨C, rfl | hC', hx⟩
                      · rcases Finset.mem_insert.mp hx with rfl | hx'
                        · exact Or.inl rfl
                        · exact Or.inr (hunionQ ▸ Finset.mem_biUnion.mpr ⟨blk', hblk'Q, hx'⟩)
                      · exact Or.inr (hunionQ ▸ Finset.mem_biUnion.mpr ⟨C, Finset.mem_of_mem_erase hC', hx⟩)
                    · intro hx
                      rcases hx with hxa | hxs
                      · rw [hxa]; exact ⟨insert a blk', Or.inl rfl, Finset.mem_insert_self a blk'⟩
                      · obtain ⟨C, hCQ, hxC⟩ := Finset.mem_biUnion.mp (hunionQ.symm ▸ hxs)
                        by_cases hC : C = blk'
                        · subst hC
                          exact ⟨insert a C, Or.inl rfl, Finset.mem_insert_of_mem hxC⟩
                        · exact ⟨C, Or.inr (Finset.mem_erase.mpr ⟨hC, hCQ⟩), hxC⟩
                  · rw [Finset.card_insert_of_notMem hnot_mem, Finset.card_erase_of_mem hblk'Q, hcardQ]
                    omega
                  · intro hsing
                    rcases Finset.mem_insert.mp hsing with heq | hmem
                    · obtain ⟨x, hx⟩ := hneQ blk' hblk'Q
                      have hxa : x ≠ a := fun h => ha_not_C blk' hblk'Q (h ▸ hx)
                      have : x ∈ ({a} : Finset α) := heq ▸ Finset.mem_insert_of_mem hx
                      exact hxa (Finset.mem_singleton.mp this)
                    · exact ha_not_C {a} (Finset.mem_of_mem_erase hmem) (Finset.mem_singleton_self a)
              rw [hdisj, Finset.card_biUnion]
              · refine Finset.sum_congr rfl fun Q hQ => ?_
                have hQpart := (mem_setPartitions_iff s Q).mp (Finset.mem_filter.mp hQ).1
                have ha_not_C : ∀ C ∈ Q, a ∉ C := fun C hC haC =>
                  has (hQpart.2.2 ▸ Finset.mem_biUnion.mpr ⟨C, hC, haC⟩)
                refine Finset.card_image_of_injOn fun b₁ hb₁ b₂ hb₂ heq => ?_
                have hmem1 : insert a b₁ ∈ insert (insert a b₂) (Q.erase b₂) :=
                  heq ▸ Finset.mem_insert_self _ _
                rcases Finset.mem_insert.mp hmem1 with h12 | h1Q
                · ext x
                  constructor
                  · intro hx
                    have hxa : x ≠ a := fun h => ha_not_C b₁ hb₁ (h ▸ hx)
                    have : x ∈ insert a b₂ := h12 ▸ Finset.mem_insert_of_mem hx
                    exact (Finset.mem_insert.mp this).resolve_left hxa
                  · intro hx
                    have hxa : x ≠ a := fun h => ha_not_C b₂ hb₂ (h ▸ hx)
                    have : x ∈ insert a b₁ := h12.symm ▸ Finset.mem_insert_of_mem hx
                    exact (Finset.mem_insert.mp this).resolve_left hxa
                · exfalso
                  exact ha_not_C (insert a b₁) (Finset.mem_of_mem_erase h1Q) (Finset.mem_insert_self a b₁)
              · intro Q₁ hQ₁ Q₂ hQ₂ hne12
                dsimp only [Function.onFun]
                rw [Finset.disjoint_left]
                intro P hP1 hP2
                obtain ⟨b₁, hb₁, rfl⟩ := Finset.mem_image.mp hP1
                obtain ⟨b₂, hb₂, heq⟩ := Finset.mem_image.mp hP2
                have hQ₁p := (mem_setPartitions_iff s Q₁).mp (Finset.mem_filter.mp hQ₁).1
                have hQ₂p := (mem_setPartitions_iff s Q₂).mp (Finset.mem_filter.mp hQ₂).1
                have ha1 : ∀ C ∈ Q₁, a ∉ C := fun C hC haC =>
                  has (hQ₁p.2.2 ▸ Finset.mem_biUnion.mpr ⟨C, hC, haC⟩)
                have ha2 : ∀ C ∈ Q₂, a ∉ C := fun C hC haC =>
                  has (hQ₂p.2.2 ▸ Finset.mem_biUnion.mpr ⟨C, hC, haC⟩)
                have h12 : insert a b₁ = insert a b₂ := by
                  have hm : insert a b₁ ∈ insert (insert a b₂) (Q₂.erase b₂) :=
                    heq.symm ▸ Finset.mem_insert_self _ _
                  rcases Finset.mem_insert.mp hm with h | h
                  · exact h
                  · exfalso; exact ha2 _ (Finset.mem_of_mem_erase h) (Finset.mem_insert_self a b₁)
                have hb12 : b₁ = b₂ := by
                  have h1 : (insert a b₁).erase a = b₁ := Finset.erase_insert (ha1 b₁ hb₁)
                  have h2 : (insert a b₂).erase a = b₂ := Finset.erase_insert (ha2 b₂ hb₂)
                  rw [← h1, h12, h2]
                subst hb12
                have hnot1 : insert a b₁ ∉ Q₁.erase b₁ := fun h =>
                  ha1 _ (Finset.mem_of_mem_erase h) (Finset.mem_insert_self a b₁)
                have hnot2 : insert a b₁ ∉ Q₂.erase b₁ := fun h =>
                  ha2 _ (Finset.mem_of_mem_erase h) (Finset.mem_insert_self a b₁)
                have her : Q₁.erase b₁ = Q₂.erase b₁ := by
                  have h := congr_arg (fun X => X.erase (insert a b₁)) heq
                  simpa [Finset.erase_insert hnot1, Finset.erase_insert hnot2] using h.symm
                apply hne12
                rw [← Finset.insert_erase hb₁, ← Finset.insert_erase hb₂, her]
            rw [hcardB]
            calc
              ∑ Q ∈ (setPartitions s).filter (fun Q => Q.card = i + 1), Q.card
                = ∑ _Q ∈ (setPartitions s).filter (fun Q => Q.card = i + 1), (i + 1) :=
                    Finset.sum_congr rfl fun Q hQ => (Finset.mem_filter.mp hQ).2
              _ = ((setPartitions s).filter (fun Q => Q.card = i + 1)).card * (i + 1) := by simp
              _ = (i + 1) * stirling2 s.card (i + 1) := by rw [ih (i + 1), mul_comm]
          · -- `A.card = stirling2 s.card i` via `Q ↦ insert {a} Q`!
            have himg : A = ((setPartitions s).filter fun Q => Q.card = i).image (insert ({a} : Finset α)) := by
              ext P
              simp only [A, All, Finset.mem_filter, mem_setPartitions_iff, Finset.mem_image]
              constructor
              · rintro ⟨⟨⟨hne, hpw, hunion⟩, hcard⟩, hsing⟩
                refine ⟨P.erase {a}, ⟨⟨?_, ?_, ?_⟩, ?_⟩, Finset.insert_erase hsing⟩
                · intro C hC; exact hne C (Finset.mem_of_mem_erase hC)
                · intro C₁ hC₁ C₂ hC₂ hne12
                  exact hpw C₁ (Finset.mem_of_mem_erase hC₁) C₂ (Finset.mem_of_mem_erase hC₂) hne12
                · ext x
                  simp only [Finset.mem_biUnion, id_eq, Finset.mem_erase]
                  constructor
                  · rintro ⟨C, ⟨hneC, hCP⟩, hxC⟩
                    have hxa : x ≠ a := fun h =>
                      Finset.disjoint_left.mp (hpw C hCP {a} hsing hneC) (h ▸ hxC) (Finset.mem_singleton_self a)
                    have hxs : x ∈ insert a s := hunion ▸ Finset.mem_biUnion.mpr ⟨C, hCP, hxC⟩
                    exact (Finset.mem_insert.mp hxs).resolve_left hxa
                  · intro hxs
                    have hxa : x ≠ a := fun h => has (h ▸ hxs)
                    obtain ⟨C, hCP, hxC⟩ := Finset.mem_biUnion.mp (hunion.symm ▸ Finset.mem_insert_of_mem hxs)
                    have hneC : C ≠ {a} := fun h => hxa (Finset.mem_singleton.mp (h ▸ hxC))
                    exact ⟨C, ⟨hneC, hCP⟩, hxC⟩
                · rw [Finset.card_erase_of_mem hsing, hcard]; omega
              · rintro ⟨Q, ⟨⟨hneQ, hpwQ, hunionQ⟩, hcardQ⟩, rfl⟩
                have ha_not_C : ∀ C ∈ Q, a ∉ C := fun C hC haC =>
                  has (hunionQ ▸ Finset.mem_biUnion.mpr ⟨C, hC, haC⟩)
                have hnotQ : ({a} : Finset α) ∉ Q := fun h => ha_not_C {a} h (Finset.mem_singleton_self a)
                refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, Finset.mem_insert_self _ _⟩
                · intro C hC
                  rcases Finset.mem_insert.mp hC with rfl | hC'
                  · exact Finset.singleton_nonempty a
                  · exact hneQ C hC'
                · intro C₁ hC₁ C₂ hC₂ hne12
                  rcases Finset.mem_insert.mp hC₁ with rfl | hC₁' <;>
                  rcases Finset.mem_insert.mp hC₂ with rfl | hC₂'
                  · exact absurd rfl hne12
                  · exact Finset.disjoint_singleton_left.mpr (ha_not_C C₂ hC₂')
                  · exact Finset.disjoint_singleton_right.mpr (ha_not_C C₁ hC₁')
                  · exact hpwQ C₁ hC₁' C₂ hC₂' hne12
                · ext x
                  simp only [Finset.mem_biUnion, id_eq, Finset.mem_insert]
                  constructor
                  · rintro ⟨C, rfl | hC', hx⟩
                    · exact Or.inl (Finset.mem_singleton.mp hx)
                    · exact Or.inr (hunionQ ▸ Finset.mem_biUnion.mpr ⟨C, hC', hx⟩)
                  · intro hx
                    rcases hx with hxa | hxs
                    · rw [hxa]; exact ⟨{a}, Or.inl rfl, Finset.mem_singleton_self a⟩
                    · obtain ⟨C, hCQ, hxC⟩ := Finset.mem_biUnion.mp (hunionQ.symm ▸ hxs)
                      exact ⟨C, Or.inr hCQ, hxC⟩
                · rw [Finset.card_insert_of_notMem hnotQ, hcardQ]
            rw [himg, Finset.card_image_of_injOn, ih i]
            intro Q₁ hQ₁ Q₂ hQ₂ heq
            have hQ₁p := (mem_setPartitions_iff s Q₁).mp (Finset.mem_filter.mp hQ₁).1
            have hQ₂p := (mem_setPartitions_iff s Q₂).mp (Finset.mem_filter.mp hQ₂).1
            have h1 : ({a} : Finset α) ∉ Q₁ := fun h =>
              has (hQ₁p.2.2 ▸ Finset.mem_biUnion.mpr ⟨{a}, h, Finset.mem_singleton_self a⟩)
            have h2 : ({a} : Finset α) ∉ Q₂ := fun h =>
              has (hQ₂p.2.2 ▸ Finset.mem_biUnion.mpr ⟨{a}, h, Finset.mem_singleton_self a⟩)
            have h := congr_arg (fun X => X.erase ({a} : Finset α)) heq
            simpa [Finset.erase_insert h1, Finset.erase_insert h2] using h

/-- The number of pairs `(P, M)` with `P ∈ setPartitions S` and `M ⊆ P`, `|M| = k`,
equals `a049020 S.card k`. -/
private lemma card_partition_subset_pairs {α : Type*} [DecidableEq α] (S : Finset α) (k : ℕ) :
    (∑ P ∈ setPartitions S, (P.powersetCard k).card) = a049020 S.card k := by
  have hle : ∀ P ∈ setPartitions S, P.card ≤ S.card := by
    intro P hP
    have hp := (mem_setPartitions_iff S P).mp hP
    have hbi : (P.biUnion id).card = ∑ B ∈ P, B.card :=
      Finset.card_biUnion fun B₁ hB₁ B₂ hB₂ hne => hp.2.1 B₁ hB₁ B₂ hB₂ hne
    rw [← hp.2.2, hbi]
    calc
      P.card = ∑ _B ∈ P, 1 := by simp
      _ ≤ ∑ B ∈ P, B.card := Finset.sum_le_sum fun B hB => Finset.card_pos.mpr (hp.1 B hB)
  have hgroup :
      ∑ P ∈ setPartitions S, (P.powersetCard k).card =
      ∑ i ∈ Finset.range (S.card + 1),
        ∑ P ∈ (setPartitions S).filter (fun P => P.card = i), Nat.choose i k := by
    rw [Finset.sum_sigma']
    have hbij :
        (∑ P ∈ setPartitions S, (P.powersetCard k).card) =
        ∑ P ∈ setPartitions S, Nat.choose P.card k :=
      Finset.sum_congr rfl fun P _ => Finset.card_powersetCard k P
    rw [hbij]
    symm
    refine Finset.sum_nbij (fun x => x.2) ?_ ?_ ?_ ?_
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).1
    · intro x hx y hy hxy
      have hx2 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2
      have hy2 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).2).2
      dsimp at hxy
      exact Sigma.ext (by rw [← hx2, ← hy2, hxy]) (heq_of_eq hxy)
    · intro P hP
      refine ⟨⟨P.card, P⟩, ?_, rfl⟩
      exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hle P hP)),
        Finset.mem_filter.mpr ⟨hP, rfl⟩⟩
    · intro x hx
      rw [(Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2]
  rw [hgroup]
  unfold a049020
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_const, smul_eq_mul, card_setPartitions_filter_card]

/-- Cardinality of even numbers in `{1, ..., n}` is `n / 2`. -/
private lemma card_even_Icc (n : ℕ) :
    ((Finset.Icc 1 n).filter Even).card = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
      rw [hIcc, Finset.filter_insert]
      by_cases he : Even (n + 1)
      · rw [if_pos he, Finset.card_insert_of_notMem (by simp [hnot]), ih]
        obtain ⟨m, hm⟩ := he
        omega
      · rw [if_neg he, ih]
        have ho : Odd (n + 1) := Nat.not_even_iff_odd.mp he
        obtain ⟨m, hm⟩ := ho
        omega

/-- Cardinality of odd numbers in `{1, ..., n}` is `(n + 1) / 2`. -/
private lemma card_odd_Icc (n : ℕ) :
    ((Finset.Icc 1 n).filter Odd).card = (n + 1) / 2 := by
  have hdisj : Disjoint ((Finset.Icc 1 n).filter Even) ((Finset.Icc 1 n).filter Odd) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Nat.not_even_iff_odd.mpr (Finset.mem_filter.mp h2).2) (Finset.mem_filter.mp h1).2
  have hunion : (Finset.Icc 1 n).filter Even ∪ (Finset.Icc 1 n).filter Odd = Finset.Icc 1 n := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases he : Even x
      · exact Or.inl ⟨h, he⟩
      · exact Or.inr ⟨h, Nat.not_even_iff_odd.mp he⟩
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, card_even_Icc, Nat.card_Icc] at hcard
  omega

/-- Key bijection for mixed blocks on any two disjoint finite sets `E, O` of `ℕ`
where every element of `E` is even and every element of `O` is odd. -/
private lemma card_mixed_partitions (E O : Finset ℕ)
    (hE : ∀ x ∈ E, Even x) (hO : ∀ x ∈ O, Odd x) (k : ℕ) :
    ((setPartitions (E ∪ O)).filter fun P => (P.filter isMixedBlock).card = k).card =
      Nat.factorial k * a049020 E.card k * a049020 O.card k := by
  have hEO_disj : Disjoint E O := by
    rw [Finset.disjoint_left]
    intro x hxE hxO
    exact (Nat.not_even_iff_odd.mpr (hO x hxO)) (hE x hxE)
  -- Helper: `isMixedBlock B ↔ (B ∩ E).Nonempty ∧ (B ∩ O).Nonempty` for `B ⊆ E ∪ O`
  have hmixed_iff : ∀ B : Finset ℕ, B ⊆ E ∪ O →
      (isMixedBlock B ↔ (B ∩ E).Nonempty ∧ (B ∩ O).Nonempty) := by
    intro B hB
    unfold isMixedBlock
    constructor
    · rintro ⟨⟨x, hxB, hxe⟩, ⟨y, hyB, hyo⟩⟩
      have hxE : x ∈ E := by
        rcases Finset.mem_union.mp (hB hxB) with h | h
        · exact h
        · exact absurd hxe (Nat.not_even_iff_odd.mpr (hO x h))
      have hyO : y ∈ O := by
        rcases Finset.mem_union.mp (hB hyB) with h | h
        · exact absurd (hE y h) (Nat.not_even_iff_odd.mpr hyo)
        · exact h
      exact ⟨⟨x, Finset.mem_inter.mpr ⟨hxB, hxE⟩⟩, ⟨y, Finset.mem_inter.mpr ⟨hyB, hyO⟩⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨⟨x, (Finset.mem_inter.mp hx).1, hE x (Finset.mem_inter.mp hx).2⟩,
             ⟨y, (Finset.mem_inter.mp hy).1, hO y (Finset.mem_inter.mp hy).2⟩⟩
  -- Define the Sigma type of `(P_E, M_E)`, `(P_O, M_O)`, and `f : M_E ≃ M_O`
  let XE := Σ P : { P // P ∈ setPartitions E }, { M // M ∈ P.1.powersetCard k }
  let XO := Σ P : { P // P ∈ setPartitions O }, { M // M ∈ P.1.powersetCard k }
  let Dom := Σ (x : XE) (y : XO), (x.2.1 ≃ y.2.1)
  let Cod := { P // P ∈ (setPartitions (E ∪ O)).filter fun P => (P.filter isMixedBlock).card = k }
  -- Forward map `Dom → Cod`
  let toCod : Dom → Cod := fun ⟨⟨⟨PE, hPE⟩, ⟨ME, hME⟩⟩, ⟨⟨PO, hPO⟩, ⟨MO, hMO⟩⟩, f⟩ =>
    let PEp := (mem_setPartitions_iff E PE).mp hPE
    let POp := (mem_setPartitions_iff O PO).mp hPO
    let hME_sub : ME ⊆ PE := (Finset.mem_powersetCard.mp hME).1
    let hMO_sub : MO ⊆ PO := (Finset.mem_powersetCard.mp hMO).1
    let hME_card : ME.card = k := (Finset.mem_powersetCard.mp hME).2
    let mixedBlks : Finset (Finset ℕ) := ME.attach.image fun B => B.1 ∪ (f B).1
    let P : Finset (Finset ℕ) := (PE \ ME) ∪ (PO \ MO) ∪ mixedBlks
    have hsubE : ∀ B ∈ PE, B ⊆ E := fun B hB x hx =>
      PEp.2.2 ▸ Finset.mem_biUnion.mpr ⟨B, hB, hx⟩
    have hsubO : ∀ B ∈ PO, B ⊆ O := fun B hB x hx =>
      POp.2.2 ▸ Finset.mem_biUnion.mpr ⟨B, hB, hx⟩
    have hdisj_EO_blk : ∀ A ∈ PE, ∀ B ∈ PO, Disjoint A B := fun A hA B hB =>
      hEO_disj.mono (hsubE A hA) (hsubO B hB)
    have hP_part : isSetPartition (E ∪ O) P := by
      refine ⟨?_, ?_, ?_⟩
      · intro B hB
        rcases Finset.mem_union.mp hB with h1 | h2
        · rcases Finset.mem_union.mp h1 with hE' | hO'
          · exact PEp.1 B (Finset.mem_sdiff.mp hE').1
          · exact POp.1 B (Finset.mem_sdiff.mp hO').1
        · obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp h2
          exact (PEp.1 A.1 (hME_sub A.2)).mono Finset.subset_union_left
      · intro B₁ hB₁ B₂ hB₂ hne12
        have hcase : ∀ B ∈ P,
            (B ∈ PE \ ME) ∨ (B ∈ PO \ MO) ∨ (∃ A : ME, B = A.1 ∪ (f A).1) := by
          intro B hB
          rcases Finset.mem_union.mp hB with h1 | h2
          · rcases Finset.mem_union.mp h1 with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp h2
            exact Or.inr (Or.inr ⟨A, rfl⟩)
        rcases hcase B₁ hB₁ with h1 | h1 | ⟨A₁, rfl⟩ <;>
        rcases hcase B₂ hB₂ with h2 | h2 | ⟨A₂, rfl⟩
        · exact PEp.2.1 B₁ (Finset.mem_sdiff.mp h1).1 B₂ (Finset.mem_sdiff.mp h2).1 hne12
        · exact hdisj_EO_blk B₁ (Finset.mem_sdiff.mp h1).1 B₂ (Finset.mem_sdiff.mp h2).1
        · rw [Finset.disjoint_union_right]
          refine ⟨PEp.2.1 B₁ (Finset.mem_sdiff.mp h1).1 A₂.1 (hME_sub A₂.2) ?_,
                  hdisj_EO_blk B₁ (Finset.mem_sdiff.mp h1).1 (f A₂).1 (hMO_sub (f A₂).2)⟩
          intro heq; exact (Finset.mem_sdiff.mp h1).2 (heq ▸ A₂.2)
        · exact (hdisj_EO_blk B₂ (Finset.mem_sdiff.mp h2).1 B₁ (Finset.mem_sdiff.mp h1).1).symm
        · exact POp.2.1 B₁ (Finset.mem_sdiff.mp h1).1 B₂ (Finset.mem_sdiff.mp h2).1 hne12
        · rw [Finset.disjoint_union_right]
          refine ⟨(hdisj_EO_blk A₂.1 (hME_sub A₂.2) B₁ (Finset.mem_sdiff.mp h1).1).symm,
                  POp.2.1 B₁ (Finset.mem_sdiff.mp h1).1 (f A₂).1 (hMO_sub (f A₂).2) ?_⟩
          intro heq; exact (Finset.mem_sdiff.mp h1).2 (heq ▸ (f A₂).2)
        · rw [Finset.disjoint_union_left]
          refine ⟨PEp.2.1 A₁.1 (hME_sub A₁.2) B₂ (Finset.mem_sdiff.mp h2).1 ?_,
                  (hdisj_EO_blk B₂ (Finset.mem_sdiff.mp h2).1 (f A₁).1 (hMO_sub (f A₁).2)).symm⟩
          intro heq; exact (Finset.mem_sdiff.mp h2).2 (heq ▸ A₁.2)
        · rw [Finset.disjoint_union_left]
          refine ⟨hdisj_EO_blk A₁.1 (hME_sub A₁.2) B₂ (Finset.mem_sdiff.mp h2).1,
                  POp.2.1 (f A₁).1 (hMO_sub (f A₁).2) B₂ (Finset.mem_sdiff.mp h2).1 ?_⟩
          intro heq; exact (Finset.mem_sdiff.mp h2).2 (heq ▸ (f A₁).2)
        · have hneA : A₁ ≠ A₂ := fun h => hne12 (by subst h; rfl)
          have hneA1 : A₁.1 ≠ A₂.1 := fun h => hneA (Subtype.ext h)
          have hnef : (f A₁).1 ≠ (f A₂).1 := fun h => hneA (f.injective (Subtype.ext h))
          rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
          exact ⟨⟨PEp.2.1 A₁.1 (hME_sub A₁.2) A₂.1 (hME_sub A₂.2) hneA1,
                  hdisj_EO_blk A₁.1 (hME_sub A₁.2) (f A₂).1 (hMO_sub (f A₂).2)⟩,
                 ⟨(hdisj_EO_blk A₂.1 (hME_sub A₂.2) (f A₁).1 (hMO_sub (f A₁).2)).symm,
                  POp.2.1 (f A₁).1 (hMO_sub (f A₁).2) (f A₂).1 (hMO_sub (f A₂).2) hnef⟩⟩
      · ext x
        simp only [P, Finset.mem_biUnion, id_eq, Finset.mem_union, Finset.mem_sdiff,
          mixedBlks, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
        constructor
        · rintro ⟨B, (⟨hB, _⟩ | ⟨hB, _⟩) | ⟨A, hA, rfl⟩, hxB⟩
          · exact Or.inl (hsubE B hB hxB)
          · exact Or.inr (hsubO B hB hxB)
          · rcases Finset.mem_union.mp hxB with hxA | hxf
            · exact Or.inl (hsubE A (hME_sub hA) hxA)
            · exact Or.inr (hsubO (f ⟨A, hA⟩).1 (hMO_sub (f ⟨A, hA⟩).2) hxf)
        · rintro (hxE | hxO)
          · obtain ⟨A, hAPE, hxA⟩ := Finset.mem_biUnion.mp (PEp.2.2.symm ▸ hxE)
            by_cases hAME : A ∈ ME
            · exact ⟨A ∪ (f ⟨A, hAME⟩).1, Or.inr ⟨A, hAME, rfl⟩, Finset.mem_union_left _ hxA⟩
            · exact ⟨A, Or.inl (Or.inl ⟨hAPE, hAME⟩), hxA⟩
          · obtain ⟨B, hBPO, hxB⟩ := Finset.mem_biUnion.mp (POp.2.2.symm ▸ hxO)
            by_cases hBMO : B ∈ MO
            · let A := f.symm ⟨B, hBMO⟩
              have hfA : f A = ⟨B, hBMO⟩ := f.apply_symm_apply ⟨B, hBMO⟩
              exact ⟨A.1 ∪ (f A).1, Or.inr ⟨A.1, A.2, rfl⟩,
                Finset.mem_union_right _ (by rw [hfA]; exact hxB)⟩
            · exact ⟨B, Or.inl (Or.inr ⟨hBPO, hBMO⟩), hxB⟩
    have hmixed_eq : P.filter isMixedBlock = mixedBlks := by
      ext B
      simp only [Finset.mem_filter, P, Finset.mem_union]
      constructor
      · rintro ⟨(h1 | h2), hm⟩
        · exfalso
          rcases h1 with hE' | hO'
          · obtain ⟨_, ⟨y, hyB, hyo⟩⟩ := hm
            exact (Nat.not_even_iff_odd.mpr hyo) (hE y (hsubE B (Finset.mem_sdiff.mp hE').1 hyB))
          · obtain ⟨⟨x, hxB, hxe⟩, _⟩ := hm
            exact (Nat.not_even_iff_odd.mpr (hO x (hsubO B (Finset.mem_sdiff.mp hO').1 hxB))) hxe
        · exact h2
      · intro hB
        refine ⟨Or.inr hB, ?_⟩
        obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hB
        obtain ⟨x, hx⟩ := PEp.1 A.1 (hME_sub A.2)
        obtain ⟨y, hy⟩ := POp.1 (f A).1 (hMO_sub (f A).2)
        exact ⟨⟨x, Finset.mem_union_left _ hx, hE x (hsubE A.1 (hME_sub A.2) hx)⟩,
               ⟨y, Finset.mem_union_right _ hy, hO y (hsubO (f A).1 (hMO_sub (f A).2) hy)⟩⟩
    have hmixed_card : (P.filter isMixedBlock).card = k := by
      rw [hmixed_eq, Finset.card_image_of_injective]
      · rw [Finset.card_attach, hME_card]
      · intro A₁ A₂ heq
        dsimp only at heq
        apply Subtype.ext
        have h1 : (A₁.1 ∪ (f A₁).1) ∩ E = A₁.1 := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr (hsubE A₁.1 (hME_sub A₁.2)),
              Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left (hsubO _ (hMO_sub (f A₁).2)) hEO_disj.symm),
              Finset.union_empty]
        have h2 : (A₂.1 ∪ (f A₂).1) ∩ E = A₂.1 := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr (hsubE A₂.1 (hME_sub A₂.2)),
              Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left (hsubO _ (hMO_sub (f A₂).2)) hEO_disj.symm),
              Finset.union_empty]
        rw [← h1, heq, h2]
    ⟨P, Finset.mem_filter.mpr ⟨(mem_setPartitions_iff _ _).mpr hP_part, hmixed_card⟩⟩
  -- Prove `toCod` is bijective!
  have hbij : Function.Bijective toCod := by
    constructor
    · -- Injective
      rintro ⟨⟨⟨PE₁, hPE₁⟩, ⟨ME₁, hME₁⟩⟩, ⟨⟨PO₁, hPO₁⟩, ⟨MO₁, hMO₁⟩⟩, f₁⟩
             ⟨⟨⟨PE₂, hPE₂⟩, ⟨ME₂, hME₂⟩⟩, ⟨⟨PO₂, hPO₂⟩, ⟨MO₂, hMO₂⟩⟩, f₂⟩ hEq
      have hPeq : (toCod ⟨⟨⟨PE₁, hPE₁⟩, ⟨ME₁, hME₁⟩⟩, ⟨⟨PO₁, hPO₁⟩, ⟨MO₁, hMO₁⟩⟩, f₁⟩).1 =
                  (toCod ⟨⟨⟨PE₂, hPE₂⟩, ⟨ME₂, hME₂⟩⟩, ⟨⟨PO₂, hPO₂⟩, ⟨MO₂, hMO₂⟩⟩, f₂⟩).1 :=
        congr_arg Subtype.val hEq
      -- Helper to recover `PE`, `ME`, `PO`, `MO`, and `f` from `P`!
      have hrec : ∀ (PE : Finset (Finset ℕ)) (hPE : PE ∈ setPartitions E)
          (ME : Finset (Finset ℕ)) (hME : ME ∈ PE.powersetCard k)
          (PO : Finset (Finset ℕ)) (hPO : PO ∈ setPartitions O)
          (MO : Finset (Finset ℕ)) (hMO : MO ∈ PO.powersetCard k)
          (f : ME ≃ MO),
          let P := (toCod ⟨⟨⟨PE, hPE⟩, ⟨ME, hME⟩⟩, ⟨⟨PO, hPO⟩, ⟨MO, hMO⟩⟩, f⟩).1
          ((P.image (· ∩ E)).filter Finset.Nonempty = PE) ∧
          ((P.filter isMixedBlock).image (· ∩ E) = ME) ∧
          ((P.image (· ∩ O)).filter Finset.Nonempty = PO) ∧
          ((P.filter isMixedBlock).image (· ∩ O) = MO) ∧
          (∀ A : ME, A.1 ∪ (f A).1 ∈ P) := by
        intro PE hPE ME hME PO hPO MO hMO f
        dsimp only [toCod]
        have PEp := (mem_setPartitions_iff E PE).mp hPE
        have POp := (mem_setPartitions_iff O PO).mp hPO
        have hME_sub : ME ⊆ PE := (Finset.mem_powersetCard.mp hME).1
        have hMO_sub : MO ⊆ PO := (Finset.mem_powersetCard.mp hMO).1
        have hsubE : ∀ B ∈ PE, B ⊆ E := fun B hB x hx =>
          PEp.2.2 ▸ Finset.mem_biUnion.mpr ⟨B, hB, hx⟩
        have hsubO : ∀ B ∈ PO, B ⊆ O := fun B hB x hx =>
          POp.2.2 ▸ Finset.mem_biUnion.mpr ⟨B, hB, hx⟩
        have hcapE_O : ∀ B ∈ PO, B ∩ E = ∅ := fun B hB =>
          Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left (hsubO B hB) hEO_disj.symm)
        have hcapO_E : ∀ B ∈ PE, B ∩ O = ∅ := fun B hB =>
          Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left (hsubE B hB) hEO_disj)
        have hmix : ((PE \ ME) ∪ (PO \ MO) ∪ ME.attach.image (fun B => B.1 ∪ (f B).1)).filter isMixedBlock =
            ME.attach.image (fun B => B.1 ∪ (f B).1) := by
          ext B
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨(h1 | h2), hm⟩
            · exfalso
              rcases h1 with hE' | hO'
              · obtain ⟨_, ⟨y, hyB, hyo⟩⟩ := hm
                exact (Nat.not_even_iff_odd.mpr hyo) (hE y (hsubE B (Finset.mem_sdiff.mp hE').1 hyB))
              · obtain ⟨⟨x, hxB, hxe⟩, _⟩ := hm
                exact (Nat.not_even_iff_odd.mpr (hO x (hsubO B (Finset.mem_sdiff.mp hO').1 hxB))) hxe
            · exact h2
          · intro hB
            refine ⟨Or.inr hB, ?_⟩
            obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hB
            obtain ⟨x, hx⟩ := PEp.1 A.1 (hME_sub A.2)
            obtain ⟨y, hy⟩ := POp.1 (f A).1 (hMO_sub (f A).2)
            exact ⟨⟨x, Finset.mem_union_left _ hx, hE x (hsubE A.1 (hME_sub A.2) hx)⟩,
                   ⟨y, Finset.mem_union_right _ hy, hO y (hsubO (f A).1 (hMO_sub (f A).2) hy)⟩⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · ext A
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_union, Finset.mem_sdiff,
            Finset.mem_attach, true_and, Subtype.exists]
          constructor
          · rintro ⟨⟨B, (⟨hB, _⟩ | ⟨hB, _⟩) | ⟨C, hC, rfl⟩, rfl⟩, hne⟩
            · rwa [Finset.inter_eq_left.mpr (hsubE B hB)]
            · rw [hcapE_O B hB] at hne; exact absurd hne (by simp)
            · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr (hsubE C (hME_sub hC)),
                  hcapE_O _ (hMO_sub (f ⟨C, hC⟩).2), Finset.union_empty]
              exact hME_sub hC
          · intro hA
            refine ⟨?_, PEp.1 A hA⟩
            by_cases hAM : A ∈ ME
            · refine ⟨A ∪ (f ⟨A, hAM⟩).1, Or.inr ⟨A, hAM, rfl⟩, ?_⟩
              rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr (hsubE A hA),
                  hcapE_O _ (hMO_sub (f ⟨A, hAM⟩).2), Finset.union_empty]
            · exact ⟨A, Or.inl (Or.inl ⟨hA, hAM⟩), Finset.inter_eq_left.mpr (hsubE A hA)⟩
        · rw [hmix]
          ext A
          simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
          constructor
          · rintro ⟨_, ⟨C, hC, rfl⟩, rfl⟩
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr (hsubE C (hME_sub hC)),
                hcapE_O _ (hMO_sub (f ⟨C, hC⟩).2), Finset.union_empty]
            exact hC
          · intro hA
            refine ⟨A ∪ (f ⟨A, hA⟩).1, ⟨A, hA, rfl⟩, ?_⟩
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr (hsubE A (hME_sub hA)),
                hcapE_O _ (hMO_sub (f ⟨A, hA⟩).2), Finset.union_empty]
        · ext B
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_union, Finset.mem_sdiff,
            Finset.mem_attach, true_and, Subtype.exists]
          constructor
          · rintro ⟨⟨C, (⟨hC, _⟩ | ⟨hC, _⟩) | ⟨A, hA, rfl⟩, rfl⟩, hne⟩
            · rw [hcapO_E C hC] at hne; exact absurd hne (by simp)
            · rwa [Finset.inter_eq_left.mpr (hsubO C hC)]
            · rw [Finset.union_inter_distrib_right, hcapO_E A (hME_sub hA),
                  Finset.inter_eq_left.mpr (hsubO _ (hMO_sub (f ⟨A, hA⟩).2)), Finset.empty_union]
              exact hMO_sub (f ⟨A, hA⟩).2
          · intro hB
            refine ⟨?_, POp.1 B hB⟩
            by_cases hBM : B ∈ MO
            · let A := f.symm ⟨B, hBM⟩
              have hfA : f A = ⟨B, hBM⟩ := f.apply_symm_apply ⟨B, hBM⟩
              refine ⟨A.1 ∪ (f A).1, Or.inr ⟨A.1, A.2, rfl⟩, ?_⟩
              rw [Finset.union_inter_distrib_right, hcapO_E A.1 (hME_sub A.2),
                  Finset.empty_union, hfA, Finset.inter_eq_left.mpr (hsubO B hB)]
            · exact ⟨B, Or.inl (Or.inr ⟨hB, hBM⟩), Finset.inter_eq_left.mpr (hsubO B hB)⟩
        · rw [hmix]
          ext B
          simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
          constructor
          · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
            rw [Finset.union_inter_distrib_right, hcapO_E A (hME_sub hA),
                Finset.inter_eq_left.mpr (hsubO _ (hMO_sub (f ⟨A, hA⟩).2)), Finset.empty_union]
            exact (f ⟨A, hA⟩).2
          · intro hB
            let A := f.symm ⟨B, hB⟩
            have hfA : f A = ⟨B, hB⟩ := f.apply_symm_apply ⟨B, hB⟩
            refine ⟨A.1 ∪ (f A).1, ⟨A.1, A.2, rfl⟩, ?_⟩
            rw [Finset.union_inter_distrib_right, hcapO_E A.1 (hME_sub A.2),
                Finset.empty_union, hfA, Finset.inter_eq_left.mpr (hsubO B (hMO_sub hB))]
        · intro A
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨A, Finset.mem_attach _ A, rfl⟩)
      have r1 := hrec PE₁ hPE₁ ME₁ hME₁ PO₁ hPO₁ MO₁ hMO₁ f₁
      have r2 := hrec PE₂ hPE₂ ME₂ hME₂ PO₂ hPO₂ MO₂ hMO₂ f₂
      have hPE_eq : PE₁ = PE₂ := by rw [← r1.1, hPeq, r2.1]
      have hME_eq : ME₁ = ME₂ := by rw [← r1.2.1, hPeq, r2.2.1]
      have hPO_eq : PO₁ = PO₂ := by rw [← r1.2.2.1, hPeq, r2.2.2.1]
      have hMO_eq : MO₁ = MO₂ := by rw [← r1.2.2.2.1, hPeq, r2.2.2.2.1]
      subst hPE_eq; subst hME_eq; subst hPO_eq; subst hMO_eq
      have hf_eq : f₁ = f₂ := by
        ext A : 1
        apply Subtype.ext
        have hP2p := (mem_setPartitions_iff (E ∪ O) _).mp
          (Finset.mem_filter.mp (toCod ⟨⟨⟨PE₁, hPE₁⟩, ⟨ME₁, hME₁⟩⟩, ⟨⟨PO₁, hPO₁⟩, ⟨MO₁, hMO₁⟩⟩, f₂⟩).2).1
        have hmem1 : A.1 ∪ (f₁ A).1 ∈ (toCod ⟨⟨⟨PE₁, hPE₁⟩, ⟨ME₁, hME₁⟩⟩, ⟨⟨PO₁, hPO₁⟩, ⟨MO₁, hMO₁⟩⟩, f₂⟩).1 :=
          hPeq ▸ r1.2.2.2.2 A
        have hmem2 : A.1 ∪ (f₂ A).1 ∈ (toCod ⟨⟨⟨PE₁, hPE₁⟩, ⟨ME₁, hME₁⟩⟩, ⟨⟨PO₁, hPO₁⟩, ⟨MO₁, hMO₁⟩⟩, f₂⟩).1 :=
          r2.2.2.2.2 A
        have hblkeq : A.1 ∪ (f₁ A).1 = A.1 ∪ (f₂ A).1 := by
          by_contra hne
          have hdisj := hP2p.2.1 _ hmem1 _ hmem2 hne
          have hPE1p := (mem_setPartitions_iff E PE₁).mp hPE₁
          obtain ⟨x, hx⟩ := hPE1p.1 A.1 ((Finset.mem_powersetCard.mp hME₁).1 A.2)
          exact Finset.disjoint_left.mp hdisj (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hx)
        have hPE1p := (mem_setPartitions_iff E PE₁).mp hPE₁
        have hPO1p := (mem_setPartitions_iff O PO₁).mp hPO₁
        have hsubE : A.1 ⊆ E := fun x hx =>
          hPE1p.2.2 ▸ Finset.mem_biUnion.mpr ⟨A.1, (Finset.mem_powersetCard.mp hME₁).1 A.2, hx⟩
        have hsubO1 : (f₁ A).1 ⊆ O := fun x hx =>
          hPO1p.2.2 ▸ Finset.mem_biUnion.mpr ⟨(f₁ A).1, (Finset.mem_powersetCard.mp hMO₁).1 (f₁ A).2, hx⟩
        have hsubO2 : (f₂ A).1 ⊆ O := fun x hx =>
          hPO1p.2.2 ▸ Finset.mem_biUnion.mpr ⟨(f₂ A).1, (Finset.mem_powersetCard.mp hMO₁).1 (f₂ A).2, hx⟩
        have hcapO : A.1 ∩ O = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_of_subset_left hsubE hEO_disj)
        have h1 : (A.1 ∪ (f₁ A).1) ∩ O = (f₁ A).1 := by
          rw [Finset.union_inter_distrib_right, hcapO, Finset.empty_union, Finset.inter_eq_left.mpr hsubO1]
        have h2 : (A.1 ∪ (f₂ A).1) ∩ O = (f₂ A).1 := by
          rw [Finset.union_inter_distrib_right, hcapO, Finset.empty_union, Finset.inter_eq_left.mpr hsubO2]
        rw [← h1, hblkeq, h2]
      subst hf_eq
      rfl
    · -- Surjective
      rintro ⟨P, hP⟩
      have hPp := (mem_setPartitions_iff (E ∪ O) P).mp (Finset.mem_filter.mp hP).1
      have hPmix_card : (P.filter isMixedBlock).card = k := (Finset.mem_filter.mp hP).2
      have hsubP : ∀ B ∈ P, B ⊆ E ∪ O := fun B hB x hx =>
        hPp.2.2 ▸ Finset.mem_biUnion.mpr ⟨B, hB, hx⟩
      let PE : Finset (Finset ℕ) := (P.image (· ∩ E)).filter Finset.Nonempty
      let PO : Finset (Finset ℕ) := (P.image (· ∩ O)).filter Finset.Nonempty
      let Pmix := P.filter isMixedBlock
      let ME : Finset (Finset ℕ) := Pmix.image (· ∩ E)
      let MO : Finset (Finset ℕ) := Pmix.image (· ∩ O)
      have hinjE : Set.InjOn (· ∩ E) (Pmix : Set (Finset ℕ)) := by
        intro B₁ hB₁ B₂ hB₂ heq
        dsimp only at heq
        have hB₁P : B₁ ∈ P := (Finset.mem_filter.mp hB₁).1
        have hB₂P : B₂ ∈ P := (Finset.mem_filter.mp hB₂).1
        have hne1 : (B₁ ∩ E).Nonempty := ((hmixed_iff B₁ (hsubP B₁ hB₁P)).mp (Finset.mem_filter.mp hB₁).2).1
        by_contra hne
        obtain ⟨x, hx⟩ := hne1
        have hx2 : x ∈ B₂ ∩ E := heq ▸ hx
        exact Finset.disjoint_left.mp (hPp.2.1 B₁ hB₁P B₂ hB₂P hne)
          (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx2).1
      have hinjO : Set.InjOn (· ∩ O) (Pmix : Set (Finset ℕ)) := by
        intro B₁ hB₁ B₂ hB₂ heq
        dsimp only at heq
        have hB₁P : B₁ ∈ P := (Finset.mem_filter.mp hB₁).1
        have hB₂P : B₂ ∈ P := (Finset.mem_filter.mp hB₂).1
        have hne1 : (B₁ ∩ O).Nonempty := ((hmixed_iff B₁ (hsubP B₁ hB₁P)).mp (Finset.mem_filter.mp hB₁).2).2
        by_contra hne
        obtain ⟨x, hx⟩ := hne1
        have hx2 : x ∈ B₂ ∩ O := heq ▸ hx
        exact Finset.disjoint_left.mp (hPp.2.1 B₁ hB₁P B₂ hB₂P hne)
          (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx2).1
      have hPE : PE ∈ setPartitions E := by
        rw [mem_setPartitions_iff]
        refine ⟨fun A hA => (Finset.mem_filter.mp hA).2, ?_, ?_⟩
        · intro A₁ hA₁ A₂ hA₂ hne12
          obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hA₁).1
          obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hA₂).1
          have hBne : B₁ ≠ B₂ := fun h => hne12 (by subst h; rfl)
          exact (hPp.2.1 B₁ hB₁ B₂ hB₂ hBne).mono Finset.inter_subset_left Finset.inter_subset_left
        · ext x
          simp only [PE, Finset.mem_biUnion, id_eq, Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨A, ⟨⟨B, _, rfl⟩, _⟩, hxA⟩
            exact (Finset.mem_inter.mp hxA).2
          · intro hxE
            obtain ⟨B, hBP, hxB⟩ := Finset.mem_biUnion.mp (hPp.2.2.symm ▸ Finset.mem_union_left O hxE)
            exact ⟨B ∩ E, ⟨⟨B, hBP, rfl⟩, ⟨x, Finset.mem_inter.mpr ⟨hxB, hxE⟩⟩⟩,
              Finset.mem_inter.mpr ⟨hxB, hxE⟩⟩
      have hPO : PO ∈ setPartitions O := by
        rw [mem_setPartitions_iff]
        refine ⟨fun A hA => (Finset.mem_filter.mp hA).2, ?_, ?_⟩
        · intro A₁ hA₁ A₂ hA₂ hne12
          obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hA₁).1
          obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hA₂).1
          have hBne : B₁ ≠ B₂ := fun h => hne12 (by subst h; rfl)
          exact (hPp.2.1 B₁ hB₁ B₂ hB₂ hBne).mono Finset.inter_subset_left Finset.inter_subset_left
        · ext x
          simp only [PO, Finset.mem_biUnion, id_eq, Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨A, ⟨⟨B, _, rfl⟩, _⟩, hxA⟩
            exact (Finset.mem_inter.mp hxA).2
          · intro hxO
            obtain ⟨B, hBP, hxB⟩ := Finset.mem_biUnion.mp (hPp.2.2.symm ▸ Finset.mem_union_right E hxO)
            exact ⟨B ∩ O, ⟨⟨B, hBP, rfl⟩, ⟨x, Finset.mem_inter.mpr ⟨hxB, hxO⟩⟩⟩,
              Finset.mem_inter.mpr ⟨hxB, hxO⟩⟩
      have hME : ME ∈ PE.powersetCard k := by
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro A hA
          obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
          have hBP : B ∈ P := (Finset.mem_filter.mp hB).1
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_image.mpr ⟨B, hBP, rfl⟩,
             ((hmixed_iff B (hsubP B hBP)).mp (Finset.mem_filter.mp hB).2).1⟩
        · rw [Finset.card_image_of_injOn hinjE, hPmix_card]
      have hMO : MO ∈ PO.powersetCard k := by
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro A hA
          obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
          have hBP : B ∈ P := (Finset.mem_filter.mp hB).1
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_image.mpr ⟨B, hBP, rfl⟩,
             ((hmixed_iff B (hsubP B hBP)).mp (Finset.mem_filter.mp hB).2).2⟩
        · rw [Finset.card_image_of_injOn hinjO, hPmix_card]
      -- Construct `f : ME ≃ MO` via `Pmix`!
      let eE : Pmix ≃ ME :=
        Equiv.ofBijective (fun B => ⟨B.1 ∩ E, Finset.mem_image.mpr ⟨B.1, B.2, rfl⟩⟩)
          ⟨fun B₁ B₂ h => Subtype.ext (hinjE B₁.2 B₂.2 (congr_arg Subtype.val h)),
           fun A => by
             obtain ⟨B, hB, hAB⟩ := Finset.mem_image.mp A.2
             exact ⟨⟨B, hB⟩, Subtype.ext hAB⟩⟩
      let eO : Pmix ≃ MO :=
        Equiv.ofBijective (fun B => ⟨B.1 ∩ O, Finset.mem_image.mpr ⟨B.1, B.2, rfl⟩⟩)
          ⟨fun B₁ B₂ h => Subtype.ext (hinjO B₁.2 B₂.2 (congr_arg Subtype.val h)),
           fun A => by
             obtain ⟨B, hB, hAB⟩ := Finset.mem_image.mp A.2
             exact ⟨⟨B, hB⟩, Subtype.ext hAB⟩⟩
      let f : ME ≃ MO := eE.symm.trans eO
      refine ⟨⟨⟨⟨PE, hPE⟩, ⟨ME, hME⟩⟩, ⟨⟨PO, hPO⟩, ⟨MO, hMO⟩⟩, f⟩, ?_⟩
      apply Subtype.ext
      dsimp only [toCod]
      ext B
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists]
      constructor
      · rintro ((⟨hBPE, hBnotME⟩ | ⟨hBPO, hBnotMO⟩) | ⟨A, hAME, rfl⟩)
        · obtain ⟨C, hCP, hCE⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hBPE).1
          have hCne : (C ∩ E).Nonempty := hCE.symm ▸ (Finset.mem_filter.mp hBPE).2
          have hCnotMix : ¬ isMixedBlock C := fun hm =>
            hBnotME (Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨hCP, hm⟩, hCE⟩)
          have hCO_emp : C ∩ O = ∅ := by
            by_contra hne
            exact hCnotMix ((hmixed_iff C (hsubP C hCP)).mpr ⟨hCne, Finset.nonempty_iff_ne_empty.mpr hne⟩)
          have hBC : B = C := by
            rw [← hCE]
            have hCunion : C = (C ∩ E) ∪ (C ∩ O) := by
              rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr (hsubP C hCP)]
            rw [hCO_emp, Finset.union_empty] at hCunion
            exact hCunion.symm
          exact hBC ▸ hCP
        · obtain ⟨C, hCP, hCO⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hBPO).1
          have hCne : (C ∩ O).Nonempty := hCO.symm ▸ (Finset.mem_filter.mp hBPO).2
          have hCnotMix : ¬ isMixedBlock C := fun hm =>
            hBnotMO (Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨hCP, hm⟩, hCO⟩)
          have hCE_emp : C ∩ E = ∅ := by
            by_contra hne
            exact hCnotMix ((hmixed_iff C (hsubP C hCP)).mpr ⟨Finset.nonempty_iff_ne_empty.mpr hne, hCne⟩)
          have hBC : B = C := by
            rw [← hCO]
            have hCunion : C = (C ∩ E) ∪ (C ∩ O) := by
              rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr (hsubP C hCP)]
            rw [hCE_emp, Finset.empty_union] at hCunion
            exact hCunion.symm
          exact hBC ▸ hCP
        · set C := eE.symm ⟨A, hAME⟩
          have hCA : C.1 ∩ E = A := congr_arg Subtype.val (eE.apply_symm_apply ⟨A, hAME⟩)
          have hCf : (f ⟨A, hAME⟩).1 = C.1 ∩ O := rfl
          have hCeq : A ∪ (f ⟨A, hAME⟩).1 = C.1 := by
            rw [hCf, ← hCA, ← Finset.inter_union_distrib_left,
                Finset.inter_eq_left.mpr (hsubP C.1 (Finset.mem_filter.mp C.2).1)]
          rw [hCeq]
          exact (Finset.mem_filter.mp C.2).1
      · intro hBP
        by_cases hm : isMixedBlock B
        · have hBmix : B ∈ Pmix := Finset.mem_filter.mpr ⟨hBP, hm⟩
          have hA : B ∩ E ∈ ME := Finset.mem_image.mpr ⟨B, hBmix, rfl⟩
          refine Or.inr ⟨B ∩ E, hA, ?_⟩
          have heqC : eE.symm ⟨B ∩ E, hA⟩ = ⟨B, hBmix⟩ := eE.symm_apply_eq.mpr rfl
          have hfB : (f ⟨B ∩ E, hA⟩).1 = B ∩ O := by
            change (eO (eE.symm ⟨B ∩ E, hA⟩)).1 = B ∩ O
            rw [heqC]; rfl
          rw [hfB, ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr (hsubP B hBP)]
        · have hBne := hPp.1 B hBP
          have hBunion : B = (B ∩ E) ∪ (B ∩ O) := by
            rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr (hsubP B hBP)]
          by_cases hBE : (B ∩ E).Nonempty
          · have hBO : B ∩ O = ∅ := by
              by_contra hne
              exact hm ((hmixed_iff B (hsubP B hBP)).mpr ⟨hBE, Finset.nonempty_iff_ne_empty.mpr hne⟩)
            have hBeq : B ∩ E = B := by rw [hBO, Finset.union_empty] at hBunion; exact hBunion.symm
            refine Or.inl (Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨B, hBP, hBeq⟩, hBne⟩, ?_⟩)
            intro hBME
            obtain ⟨C, hCmix, hCE⟩ := Finset.mem_image.mp hBME
            have hCP : C ∈ P := (Finset.mem_filter.mp hCmix).1
            have hBC : B = C := by
              by_contra hne
              obtain ⟨x, hx⟩ := hBne
              have hxC : x ∈ C ∩ E := hCE.symm ▸ hx
              exact Finset.disjoint_left.mp (hPp.2.1 B hBP C hCP hne) hx (Finset.mem_inter.mp hxC).1
            exact hm (hBC ▸ (Finset.mem_filter.mp hCmix).2)
          · have hBE_emp : B ∩ E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hBE
            have hBeq : B ∩ O = B := by rw [hBE_emp, Finset.empty_union] at hBunion; exact hBunion.symm
            refine Or.inl (Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨B, hBP, hBeq⟩, hBne⟩, ?_⟩)
            intro hBMO
            obtain ⟨C, hCmix, hCO⟩ := Finset.mem_image.mp hBMO
            have hCP : C ∈ P := (Finset.mem_filter.mp hCmix).1
            have hBC : B = C := by
              by_contra hne
              obtain ⟨x, hx⟩ := hBne
              have hxC : x ∈ C ∩ O := hCO.symm ▸ hx
              exact Finset.disjoint_left.mp (hPp.2.1 B hBP C hCP hne) hx (Finset.mem_inter.mp hxC).1
            exact hm (hBC ▸ (Finset.mem_filter.mp hCmix).2)
  -- Compute cardinalities using `Fintype.card_congr`!
  let : Fintype Cod :=
    inferInstanceAs (Fintype { P // P ∈ (setPartitions (E ∪ O)).filter fun P => (P.filter isMixedBlock).card = k })
  have hcard_eq : Fintype.card Cod = Fintype.card Dom :=
    (Fintype.card_congr (Equiv.ofBijective toCod hbij)).symm
  rw [show Fintype.card Cod = ((setPartitions (E ∪ O)).filter fun P => (P.filter isMixedBlock).card = k).card from
    Fintype.card_coe _] at hcard_eq
  rw [hcard_eq]
  simp only [Dom, Fintype.card_sigma]
  have hequiv_card : ∀ (x : XE) (y : XO), Fintype.card (x.2.1 ≃ y.2.1) = Nat.factorial k := by
    intro x y
    have hx : Fintype.card x.2.1 = k := by
      rw [Fintype.card_coe]; exact (Finset.mem_powersetCard.mp x.2.2).2
    have hy : Fintype.card y.2.1 = k := by
      rw [Fintype.card_coe]; exact (Finset.mem_powersetCard.mp y.2.2).2
    have e : x.2.1 ≃ y.2.1 := Fintype.equivOfCardEq (hx.trans hy.symm)
    rw [Fintype.card_congr (Equiv.equivCongr (Equiv.refl _) e.symm), Fintype.card_perm, hx]
  have hsum : ∑ x : XE, ∑ y : XO, Fintype.card (x.2.1 ≃ y.2.1) =
      Nat.factorial k * Fintype.card XE * Fintype.card XO := by
    simp only [hequiv_card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  rw [hsum]
  have hXE : Fintype.card XE = a049020 E.card k := by
    simp only [XE, Fintype.card_sigma, Fintype.card_coe]
    have : (∑ x : { P // P ∈ setPartitions E }, (x.1.powersetCard k).card) =
        ∑ x ∈ (setPartitions E).attach, (x.1.powersetCard k).card := rfl
    rw [this, Finset.sum_attach (setPartitions E) (fun P => (P.powersetCard k).card),
        card_partition_subset_pairs]
  have hXO : Fintype.card XO = a049020 O.card k := by
    simp only [XO, Fintype.card_sigma, Fintype.card_coe]
    have : (∑ x : { P // P ∈ setPartitions O }, (x.1.powersetCard k).card) =
        ∑ x ∈ (setPartitions O).attach, (x.1.powersetCard k).card := rfl
    rw [this, Finset.sum_attach (setPartitions O) (fun P => (P.powersetCard k).card),
        card_partition_subset_pairs]
  rw [hXE, hXO]

theorem main_proof :
    ∀ n k : ℕ,
      a124418 n k = Nat.factorial k * a049020 (n / 2) k * a049020 ((n + 1) / 2) k := by
  intro n k
  unfold a124418
  set E := (Finset.Icc 1 n).filter Even
  set O := (Finset.Icc 1 n).filter Odd
  have hunion : E ∪ O = Finset.Icc 1 n := by
    ext x
    simp only [E, O, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases he : Even x
      · exact Or.inl ⟨h, he⟩
      · exact Or.inr ⟨h, Nat.not_even_iff_odd.mp he⟩
  rw [← hunion, card_mixed_partitions E O
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx => (Finset.mem_filter.mp hx).2) k,
    card_even_Icc, card_odd_Icc]

end OMA.S_oeis_a124418

theorem OMA.solution : type_of% @OMA.S_oeis_a124418.main :=
  OMA.S_oeis_a124418.main_proof
