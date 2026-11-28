import OMAStatements.S_oeis_a386580

/-!
Gus Wiseman's conjecture on OEIS A386580. A block carries its letter and its
positive length. If a letter has more blocks than all other letters plus one,
one can merge two of its blocks and preserve distinct lengths. Once balanced,
the blocks can be arranged with different letters at each boundary.
Lean proof by KoaOkano, assisted by OpenAI Codex.
-/

namespace A386580Proof

variable {α : Type*} [DecidableEq α]

private abbrev blocksOf (s : Finset (α × ℕ)) (i : α) := s.filter fun p => p.1 = i

private theorem two_counts (s : Finset (α × ℕ)) {i j : α} (h : i ≠ j) :
    (blocksOf s i).card + (blocksOf s j).card ≤ s.card := by
  have hd : Disjoint (blocksOf s i) (blocksOf s j) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact h ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)
  rw [← Finset.card_union_of_disjoint hd]
  exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset ..) (Finset.filter_subset ..))

private theorem choose_block (s : Finset (α × ℕ)) (ns : s.Nonempty) (prev : Option α)
    (hp : ∀ i, prev = some i → 2 * (blocksOf s i).card ≤ s.card) :
    ∃ p ∈ s, prev ≠ some p.1 ∧ ∀ j, j ≠ p.1 → 2 * (blocksOf s j).card ≤ s.card := by
  classical
  by_cases h : ∃ i, s.card < 2 * (blocksOf s i).card
  · obtain ⟨i, hi⟩ := h
    have hn : (blocksOf s i).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hps, rfl⟩ := Finset.Nonempty.exists_mem hn |>.imp (fun p h => Finset.mem_filter.mp h)
    refine ⟨p, hps, fun e => (not_lt_of_ge (hp _ e)) hi, ?_⟩
    intro j hj
    have := two_counts s hj
    omega
  · push Not at h
    obtain ⟨p, hps⟩ := ns
    by_cases e : prev = some p.1
    · have other : ∃ q ∈ s, p.1 ≠ q.1 := by
        by_contra! he
        have eq : blocksOf s p.1 = s := Finset.filter_true_of_mem (fun q hq => (he q hq).symm)
        have := hp _ e
        rw [eq] at this
        have := Finset.card_pos.mpr ⟨p, hps⟩
        omega
      obtain ⟨q, hq, hne⟩ := other
      exact ⟨q, hq, by simpa [e] using hne, fun j _ => h j⟩
    · exact ⟨p, hps, e, fun j _ => h j⟩

private theorem arrange (s : Finset (α × ℕ)) (prev : Option α)
    (hb : ∀ i, 2 * (blocksOf s i).card ≤ s.card + 1)
    (hp : ∀ i, prev = some i → 2 * (blocksOf s i).card ≤ s.card) :
    ∃ l : List (α × ℕ), l.Nodup ∧ (∀ q, q ∈ l ↔ q ∈ s) ∧
      l.IsChain (fun a b => a.1 ≠ b.1) ∧ ∀ q ∈ l.head?, prev ≠ some q.1 := by
  classical
  by_cases ns : s.Nonempty
  · obtain ⟨p, hs, hprev, hother⟩ := choose_block s ns prev hp
    have hspos := Finset.card_pos.mpr ns
    have hsize := Finset.card_erase_of_mem hs
    have hown : (blocksOf (s.erase p) p.1).card = (blocksOf s p.1).card - 1 := by
      rw [blocksOf, Finset.filter_erase, Finset.card_erase_of_mem (by simpa using hs)]
    have hmem : p ∈ blocksOf s p.1 := by simpa using hs
    have hpos := Finset.card_pos.mpr ⟨p, hmem⟩
    have hold := hb p.1
    have hsmall : 2 * (blocksOf (s.erase p) p.1).card ≤ (s.erase p).card := by omega
    have hbalance : ∀ j, 2 * (blocksOf (s.erase p) j).card ≤ (s.erase p).card + 1 := by
      intro j
      by_cases e : j = p.1
      · subst j; omega
      · have hn : p ∉ blocksOf s j := by simp [blocksOf, Ne.symm e]
        have eq : blocksOf (s.erase p) j = blocksOf s j := by
          rw [blocksOf, Finset.filter_erase, Finset.erase_eq_of_notMem hn]
        have := hother j e
        rw [eq]
        omega
    obtain ⟨l, hnd, hm, hc, hf⟩ := arrange (s.erase p) (some p.1) hbalance (by
      intro i hi; cases hi; exact hsmall)
    refine ⟨p :: l, List.nodup_cons.mpr ⟨by simp [hm], hnd⟩, ?_, ?_, ?_⟩
    · intro q; simp [hm, Finset.mem_erase]; grind
    · exact List.isChain_cons.mpr ⟨fun q hq => by simpa using hf q hq, hc⟩
    · simpa using hprev
  · have eq := Finset.not_nonempty_iff_eq_empty.mp ns
    exact ⟨[], by simp, by simp [eq], by simp, by simp⟩
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem hs

private def Valid (s : Finset (α × ℕ)) : Prop :=
  (∀ p ∈ s, 0 < p.2) ∧ Set.InjOn Prod.snd (s : Set (α × ℕ))

private def mass (s : Finset (α × ℕ)) (i : α) : ℕ :=
  ∑ p ∈ s, if p.1 = i then p.2 else 0

private theorem merge_pair {s : Finset (α × ℕ)} (v : Valid s) (i : α)
    (h : s.card + 1 < 2 * (blocksOf s i).card) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ a.1 = i ∧ b.1 = i ∧
      ∀ p ∈ s, p.2 ≠ a.2 + b.2 := by
  classical
  let t := s.filter fun p => p.1 ≠ i
  have ht : (blocksOf s i).card + t.card = s.card :=
    Finset.card_filter_add_card_filter_not _
  have hn : (blocksOf s i).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (blocksOf s i) Prod.snd hn
  let u := (blocksOf s i).erase a
  have hu : u.card = (blocksOf s i).card - 1 := Finset.card_erase_of_mem ha
  let shifts := u.image fun b => a.2 + b.2
  have hc : shifts.card = u.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy e
    apply v.2 (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx)).1
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase hy)).1
    exact Nat.add_left_cancel e
  have hsmall := Finset.card_image_le (s := t) (f := Prod.snd)
  have hns : ¬ shifts ⊆ t.image Prod.snd := by
    intro hs
    have := Finset.card_le_card hs
    omega
  obtain ⟨x, hx, hnot⟩ := Finset.not_subset.mp hns
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hne, hbi⟩ := Finset.mem_erase.mp hb
  obtain ⟨has, hai⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbs, hbc⟩ := Finset.mem_filter.mp hbi
  refine ⟨a, has, b, hbs, hne.symm, hai, hbc, ?_⟩
  intro p hps eq
  by_cases hi : p.1 = i
  · have := hmax p (Finset.mem_filter.mpr ⟨hps, hi⟩)
    have := v.1 b hbs
    omega
  · exact hnot (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hps, hi⟩, eq⟩)

private theorem balance (s : Finset (α × ℕ)) (v : Valid s) :
    ∃ t : Finset (α × ℕ), Valid t ∧ (∀ i, mass t i = mass s i) ∧
      ∀ i, 2 * (blocksOf t i).card ≤ t.card + 1 := by
  classical
  by_cases h : ∀ i, 2 * (blocksOf s i).card ≤ s.card + 1
  · exact ⟨s, v, fun _ => rfl, h⟩
  · push Not at h
    obtain ⟨i, hi⟩ := h
    obtain ⟨a, ha, b, hb, hab, hai, hbi, fresh⟩ := merge_pair v i hi
    let z : α × ℕ := (i, a.2 + b.2)
    let u := (s.erase a).erase b
    let t := insert z u
    have hu : u ⊆ s := (Finset.erase_subset ..).trans (Finset.erase_subset ..)
    have hzu : z ∉ u := fun hz => fresh z (hu hz) rfl
    have hbe : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    have small : t.card < s.card := by
      have h₁ := Finset.card_erase_add_one ha
      have h₂ := Finset.card_erase_add_one hbe
      rw [Finset.card_insert_of_notMem hzu]
      dsimp [u]; omega
    have vt : Valid t := by
      refine ⟨?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hpu
        · exact add_pos (v.1 a ha) (v.1 b hb)
        · exact v.1 p (hu hpu)
      · intro p hp q hq eq
        rcases Finset.mem_insert.mp hp with rfl | hpu <;>
          rcases Finset.mem_insert.mp hq with rfl | hqu
        · rfl
        · exact (fresh q (hu hqu) eq.symm).elim
        · exact (fresh p (hu hpu) eq).elim
        · exact v.2 (hu hpu) (hu hqu) eq
    have same (j : α) : mass t j = mass s j := by
      let f := fun p : α × ℕ => if p.1 = j then p.2 else 0
      have h₁ := Finset.sum_erase_add s f ha
      have h₂ := Finset.sum_erase_add (s.erase a) f hbe
      change t.sum f = s.sum f
      rw [Finset.sum_insert hzu, ← h₁, ← h₂]
      change f z + u.sum f = u.sum f + f b + f a
      simp only [f, z, hai, hbi]
      split <;> omega
    obtain ⟨t', vt', he, hc⟩ := balance t vt
    exact ⟨t', vt', fun j => (he j).trans (same j), hc⟩
termination_by s.card

private abbrev sizes (s : Finset (α × ℕ)) (i : α) := (blocksOf s i).image Prod.snd

private theorem mem_sizes {s : Finset (α × ℕ)} {i : α} {k : ℕ} :
    k ∈ sizes s i ↔ (i, k) ∈ s := by
  constructor
  · intro h
    obtain ⟨⟨j, l⟩, hp, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hs, rfl⟩ := Finset.mem_filter.mp hp
    exact hs
  · intro h
    exact Finset.mem_image.mpr ⟨(i,k), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

private theorem mass_sizes (s : Finset (α × ℕ)) (i : α) :
    mass s i = ∑ x ∈ sizes s i, x := by
  rw [sizes, Finset.sum_image]
  · exact (Finset.sum_filter ..).symm
  · intro p hp q hq e
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) e

open OMA.S_oeis_a386580

private theorem family_iff {n : ℕ} (c : Composition n) :
    HasDisjointStrictParts c ↔ ∃ s : Finset (Fin c.length × ℕ), Valid s ∧
      ∀ i, mass s i = c.blocks.get (i.cast c.blocks_length.symm) := by
  classical
  constructor
  · rintro ⟨S, hpos, hs, hd⟩
    let s := Finset.univ.biUnion fun i => (S i).image (Prod.mk i)
    have hm (i : Fin c.length) (k : ℕ) : (i,k) ∈ s ↔ k ∈ S i := by
      simp [s, Finset.mem_biUnion, Finset.mem_image, Prod.ext_iff]
    refine ⟨s, ⟨?_, ?_⟩, ?_⟩
    · rintro ⟨i,k⟩ hk
      have h := (hm i k).mp hk
      exact Nat.pos_of_ne_zero (fun eq => hpos i (eq ▸ h))
    · rintro ⟨i,k⟩ hp ⟨j,l⟩ hq e
      change k = l at e; subst l
      have hi := (hm i k).mp hp
      have hj := (hm j k).mp hq
      by_cases hij : i = j
      · cases hij; rfl
      · exact (Finset.disjoint_left.mp (hd i j hij) hi hj).elim
    · intro i
      have eq : sizes s i = S i := Finset.ext fun _ => mem_sizes.trans (hm i _)
      rw [mass_sizes, eq, hs]
  · rintro ⟨s, v, h⟩
    refine ⟨sizes s, ?_, fun i => (mass_sizes s i).symm.trans (h i), ?_⟩
    · intro i hi
      have := v.1 _ (mem_sizes.mp hi)
      exact (Nat.lt_irrefl 0) this
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro k hi hj
      have eq := v.2 (mem_sizes.mp hi) (mem_sizes.mp hj) (by rfl)
      exact hij (congrArg Prod.fst eq)

private def expand (p : α × ℕ) : List α := List.replicate p.2 p.1

private theorem count_word (l : List (α × ℕ)) (nd : l.Nodup) (i : α) :
    ((l.map expand).flatten).count i = mass l.toFinset i := by
  classical
  rw [mass, List.sum_toFinset _ nd]
  induction l with
  | nil => simp
  | cons p l ih =>
    have tail := ih (List.nodup_cons.mp nd).2
    simp only [List.map_cons, List.flatten_cons, List.count_append, List.sum_cons, tail]
    by_cases e : p.1 = i
    · simp [expand, e]
    · simp [expand, List.count_replicate, e]

private theorem split_word (l : List (α × ℕ)) (pos : ∀ p ∈ l, 0 < p.2)
    (chain : l.IsChain fun p q => p.1 ≠ q.1) :
    (l.map expand).flatten.splitBy (· == ·) = l.map expand := by
  apply List.splitBy_flatten
  · rintro h
    obtain ⟨p, hp, eq⟩ := List.mem_map.mp h
    have := pos p hp
    simp [expand, Nat.ne_of_gt this] at eq
  · intro row h
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    exact List.isChain_replicate_of_rel _ (by simp)
  · rw [List.isChain_map]
    apply chain.imp_of_mem_imp
    intro p q hp hq hne
    have ep : expand p ≠ [] := by simp [expand, Nat.ne_of_gt (pos p hp)]
    have eq : expand q ≠ [] := by simp [expand, Nat.ne_of_gt (pos q hq)]
    exact ⟨ep, eq, by simpa [expand] using hne⟩

private theorem expand_run {w row : List α} (h : row ∈ w.splitBy (· == ·)) :
    List.replicate row.length (row.head (List.ne_nil_of_mem_splitBy h)) = row := by
  have hc : row.IsChain (· = ·) := (List.isChain_of_mem_splitBy h).imp (by simp)
  apply Eq.symm
  apply List.isChain_eq_iff_eq_replicate.mp hc
  cases row with
  | nil => exact (List.nil_notMem_splitBy _ _ h).elim
  | cons => simp

private theorem equivalence {n : ℕ} (c : Composition n) :
    HasDistinctRunPerm c ↔ HasDisjointStrictParts c := by
  classical
  rw [family_iff]
  constructor
  · rintro ⟨w, counts, lengths⟩
    let rows := w.splitBy (· == ·)
    let tag : {r // r ∈ rows} → Fin c.length × ℕ := fun b =>
      (b.val.head (List.ne_nil_of_mem_splitBy b.property), b.val.length)
    let l := rows.attach.map tag
    have lens : l.map Prod.snd = rows.map List.length := by
      simp [l, tag, List.map_map, Function.comp_def]
    have nd : (l.map Prod.snd).Nodup := lens ▸ lengths
    have pos (p) (hp : p ∈ l) : 0 < p.2 := by
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
      exact List.length_pos_iff.mpr (List.ne_nil_of_mem_splitBy b.property)
    have exp : l.map expand = rows := by
      calc
        l.map expand = rows.attach.map (fun b => b.val) := by
          rw [show l = rows.attach.map tag from rfl, List.map_map]
          apply List.map_congr_left
          intro b _
          exact expand_run b.property
        _ = rows := by simp
    refine ⟨l.toFinset, ⟨?_, ?_⟩, ?_⟩
    · exact fun p hp => pos p (List.mem_toFinset.mp hp)
    · intro p hp q hq hlen
      exact List.inj_on_of_nodup_map nd (List.mem_toFinset.mp hp) (List.mem_toFinset.mp hq) hlen
    · intro i
      rw [← count_word l (List.Nodup.of_map _ nd), exp, List.flatten_splitBy]
      exact counts i
  · rintro ⟨s, vs, mass_s⟩
    obtain ⟨t, vt, mass_t, hb⟩ := balance s vs
    obtain ⟨l, nd, mem, chain, _⟩ := arrange t none hb (by simp)
    have eq : l.toFinset = t := Finset.ext fun p => List.mem_toFinset.trans (mem p)
    have hlen : (l.map Prod.snd).Nodup := nd.map_on (fun p hp q hq h =>
      vt.2 ((mem p).mp hp) ((mem q).mp hq) h)
    refine ⟨(l.map expand).flatten, ?_, ?_⟩
    · intro i
      rw [count_word l nd, eq, mass_t, mass_s]
    · rw [split_word l (fun p hp => vt.1 p ((mem p).mp hp)) chain]
      simpa [List.map_map, Function.comp_def, expand] using hlen

end A386580Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a386580.main := by
  intro n
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun c => A386580Proof.equivalence c
