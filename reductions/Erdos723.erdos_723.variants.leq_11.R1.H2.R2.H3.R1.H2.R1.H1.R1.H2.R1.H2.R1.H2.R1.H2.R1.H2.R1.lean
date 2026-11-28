import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1_H2_R1_H2_R1

/-! Project the tetrahedra packing to the heavy blocks and five blocks on a secant. -/

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1

open Finset

open scoped Classical

def H1 : Prop :=
  let Q := {e : Fin 8 × Fin 8 // e.1 < e.2}
  let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
  let pt (i j : Fin 8) (h : i < j) : P := .inl (.inl ⟨(i,j),h⟩)
  let S := ((univ : Finset Q).filter (fun e =>
    (0xfc02187 : ℕ).testBit (e.1.1.val*(15-e.1.1.val)/2+e.1.2.val-e.1.1.val-1) = false)).image
    (fun e => (Sum.inl (Sum.inl e) : P))
  let star (a : Fin 8) := S.filter (fun p => Sum.elim (Sum.elim
    (fun e : Q => decide (a = e.1.1 ∨ a = e.1.2))
    (fun t : Fin 8 × Fin 4 => decide (a = t.1))) (fun _ => false) p = true)
  let C := S.powersetCard 2 \ (univ : Finset (Fin 8)).biUnion (fun a => (star a).powersetCard 2)
  let row : Fin 8 ⊕ ↥C → Finset P := Sum.elim star Subtype.val
  ¬ ∃ b : ↥C, b.val = {pt 0 4 (by decide), pt 1 5 (by decide)} ∧
    let pivot : Fin 8 ⊕ ↥C := .inr b
    ∃ F : Finset (Finset (Fin 8 ⊕ ↥C)),
    (F.filter (fun t => t.card = 6)).card = 12 ∧
    (F.filter (fun t => t.card = 7)).card = 32 ∧
    (F.filter (fun t => t.card = 8)).card = 5 ∧
    (∀ t ∈ F, t.card = 6 ∨ t.card = 7 ∨ (t.card = 8 ∧ pivot ∈ t)) ∧
    (∀ t ∈ F, ∀ s ∈ S, ∃! l, l ∈ t ∧ s ∈ row l) ∧
    (∀ t ∈ F, ∀ u ∈ F, t ≠ u → ∀ l ∈ t, ∀ m ∈ t, l ∈ u → m ∈ u → l = m) ∧
    (∀ a l, Sum.inl a ≠ l → Disjoint (star a) (row l) →
      ∃! t, t ∈ F ∧ Sum.inl a ∈ t ∧ l ∈ t) ∧
    (∃ t ∈ F, t.card = 6 ∧ pivot ∈ t)


def H2 : Prop :=
  let Q := {e : Fin 8 × Fin 8 // e.1 < e.2}
  let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
  let pt (i j : Fin 8) (h : i < j) : P := .inl (.inl ⟨(i,j),h⟩)
  let S := ((univ : Finset Q).filter (fun e =>
    (0xfc02187 : ℕ).testBit (e.1.1.val*(15-e.1.1.val)/2+e.1.2.val-e.1.1.val-1) = false)).image
    (fun e => (Sum.inl (Sum.inl e) : P))
  let star (a : Fin 8) := S.filter (fun p => Sum.elim (Sum.elim
    (fun e : Q => decide (a = e.1.1 ∨ a = e.1.2))
    (fun t : Fin 8 × Fin 4 => decide (a = t.1))) (fun _ => false) p = true)
  let C := S.powersetCard 2 \ (univ : Finset (Fin 8)).biUnion (fun a => (star a).powersetCard 2)
  let row : Fin 8 ⊕ ↥C → Finset P := Sum.elim star Subtype.val
  ¬ ∃ b : ↥C, b.val = {pt 0 4 (by decide), pt 1 5 (by decide)} ∧
    let pivot : Fin 8 ⊕ ↥C := .inr b
    ∃ F : Finset (Finset (Fin 8 ⊕ ↥C)),
    (F.filter (fun t => t.card = 6)).card = 12 ∧
    (F.filter (fun t => t.card = 7)).card = 32 ∧
    (F.filter (fun t => t.card = 8)).card = 5 ∧
    (∀ t ∈ F, t.card = 6 ∨ t.card = 7 ∨ (t.card = 8 ∧ pivot ∈ t)) ∧
    (∀ t ∈ F, ∀ s ∈ S, ∃! l, l ∈ t ∧ s ∈ row l) ∧
    (∀ t ∈ F, ∀ u ∈ F, t ≠ u → ∀ l ∈ t, ∀ m ∈ t, l ∈ u → m ∈ u → l = m) ∧
    (∀ a l, Sum.inl a ≠ l → Disjoint (star a) (row l) →
      ∃! t, t ∈ F ∧ Sum.inl a ∈ t ∧ l ∈ t) ∧
    (∀ t ∈ F, t.card = 6 → pivot ∉ t)

section Projection


private theorem one_cover_pair {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {row : β → Finset α} {F : Finset (Finset β)}
    (cover : ∀ t ∈ F, ∀ s ∈ S, ∃! l, l ∈ t ∧ s ∈ row l)
    (closed : ∀ l, row l ⊆ S)
    {t : Finset β} (ht : t ∈ F) {l m : β} (hl : l ∈ t) (hm : m ∈ t) (ne : l ≠ m) :
    Disjoint (row l) (row m) := by
  rw [Finset.disjoint_left]
  intro s hls hms
  exact ne ((cover t ht s (closed l hls)).unique ⟨hl,hls⟩ ⟨hm,hms⟩)

private theorem through_line_card {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    {S : Finset α} {row : β → Finset α} {F : Finset (Finset β)}
    (cover : ∀ t ∈ F, ∀ s ∈ S, ∃! l, l ∈ t ∧ s ∈ row l)
    (closed : ∀ l, row l ⊆ S)
    (meet : ∀ l m, l ≠ m → Disjoint (row l) (row m) → ∃! t, t ∈ F ∧ l ∈ t ∧ m ∈ t)
    (l : β) {s : α} (hs : s ∈ S) (hout : s ∉ row l) :
    (F.filter (fun t => l ∈ t)).card =
      (univ.filter (fun m => s ∈ row m ∧ Disjoint (row l) (row m))).card := by
  classical
  choose f hf huniq using fun t (ht : t ∈ F) => cover t ht s hs
  let blocks := F.filter (fun t => l ∈ t)
  let mates := univ.filter (fun m => s ∈ row m ∧ Disjoint (row l) (row m))
  change blocks.card = mates.card
  apply card_bij (fun t ht => f t (mem_filter.mp ht).1)
  · intro t ht
    obtain ⟨hF,hl⟩ := mem_filter.mp ht
    have h := hf t hF
    have ne : l ≠ f t hF := fun e => hout (e ▸ h.2)
    exact mem_filter.mpr ⟨mem_univ _, h.2, one_cover_pair cover closed hF hl h.1 ne⟩
  · intro t ht u hu eq
    obtain ⟨hF,hl⟩ := mem_filter.mp ht
    obtain ⟨hG,hl'⟩ := mem_filter.mp hu
    have h := hf t hF
    have ne : l ≠ f t hF := fun e => hout (e ▸ h.2)
    have h' : f t hF ∈ u := eq ▸ (hf u hG).1
    exact (meet l (f t hF) ne (one_cover_pair cover closed hF hl h.1 ne)).unique
      ⟨hF,hl,h.1⟩ ⟨hG,hl',h'⟩
  · intro m hm
    obtain ⟨_, hms, hd⟩ := mem_filter.mp hm
    have ne : l ≠ m := fun e => hout (e ▸ hms)
    obtain ⟨t, ⟨ht, hl, hm'⟩, _⟩ := meet l m ne hd
    exact ⟨t, mem_filter.mpr ⟨ht, hl⟩, (huniq t ht m ⟨hm', hms⟩).symm⟩

private theorem cover_weight {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {row : β → Finset α} {t : Finset β}
    (closed : ∀ l, row l ⊆ S)
    (cover : ∀ s ∈ S, ∃! l, l ∈ t ∧ s ∈ row l) :
    ∑ l ∈ t, (row l).card = S.card := by
  have union : t.biUnion row = S := by
    ext s
    constructor
    · intro hs
      obtain ⟨l, _, hls⟩ := mem_biUnion.mp hs
      exact closed l hls
    · intro hs
      obtain ⟨l, h, _⟩ := cover s hs
      exact mem_biUnion.mpr ⟨l, h⟩
  rw [← card_biUnion, union]
  intro l hl m hm ne
  change Disjoint (row l) (row m)
  rw [Finset.disjoint_left]
  intro s hls hms
  exact ne ((cover s (closed l hls)).unique ⟨hl,hls⟩ ⟨hm,hms⟩)

private theorem project {P D : Type*} [DecidableEq P] [Fintype D]
    (S : Finset P) (star : Fin 8 → Finset P) (light : D → Finset P) (base : D) (s : P)
    (F : Finset (Finset (Fin 8 ⊕ D)))
    (hF : F.card = 95)
    (n6 : (F.filter fun t => t.card = 6).card = 12)
    (n7 : (F.filter fun t => t.card = 7).card = 32)
    (n8 : (F.filter fun t => t.card = 8).card = 51)
    (sizeS : S.card = 16)
    (sizeStar : ∀ a, (star a).card = 4)
    (sizeLight : ∀ b, (light b).card = 2)
    (mark : s ∈ S) :
    let L := Fin 8 ⊕ D
    let row : L → Finset P := Sum.elim star light
    let pivot : L := .inr base
    (∀ l, row l ⊆ S) →
    s ∉ row pivot →
    (univ.filter (fun m : L => s ∈ row m ∧ Disjoint (row pivot) (row m))).card = 9 →
    ((univ : Finset (Fin 8)).filter (fun a => Disjoint (row pivot) (star a))).card = 4 →
    (∀ t ∈ F, ∀ p ∈ S, ∃! l, l ∈ t ∧ p ∈ row l) →
    (∀ t ∈ F, ∀ u ∈ F, t ≠ u → ∀ l ∈ t, ∀ m ∈ t, l ∈ u → m ∈ u → l = m) →
    (∀ l m : L, l ≠ m → Disjoint (row l) (row m) → ∃! t, t ∈ F ∧ l ∈ t ∧ m ∈ t) →
    ∃ G : Finset (Finset L),
      (G.filter (fun t => t.card = 6)).card = 12 ∧
      (G.filter (fun t => t.card = 7)).card = 32 ∧
      (G.filter (fun t => t.card = 8)).card = 5 ∧
      (∀ t ∈ G, t.card = 6 ∨ t.card = 7 ∨ (t.card = 8 ∧ pivot ∈ t)) ∧
      (∀ t ∈ G, ∀ p ∈ S, ∃! l, l ∈ t ∧ p ∈ row l) ∧
      (∀ t ∈ G, ∀ u ∈ G, t ≠ u → ∀ l ∈ t, ∀ m ∈ t, l ∈ u → m ∈ u → l = m) ∧
      ∀ a l, Sum.inl a ≠ l → Disjoint (star a) (row l) →
        ∃! t, t ∈ G ∧ Sum.inl a ∈ t ∧ l ∈ t := by
  intro L row pivot closed off mates four cover linear meet
  have neHeavy (a : Fin 8) : pivot ≠ Sum.inl a := by
    change (Sum.inr base : L) ≠ Sum.inl a
    intro e
    cases e
  have through : (F.filter (fun t => pivot ∈ t)).card = 9 :=
    (through_line_card cover closed meet pivot mark off).trans mates
  let short := F.filter (fun t => t.card = 6 ∨ t.card = 7)
  let long := F.filter (fun t => t.card = 8)
  have allBlocks : short ∪ long = F := by
    have shortEq : short = F.filter (fun t => t.card = 6) ∪ F.filter (fun t => t.card = 7) := by
      ext t
      simp only [short, mem_union, mem_filter]
      tauto
    have ds : Disjoint (F.filter (fun t => t.card = 6)) (F.filter (fun t => t.card = 7)) := by
      rw [Finset.disjoint_left]
      intro t ht hu
      exact (by decide : (6 : ℕ) ≠ 7) ((mem_filter.mp ht).2.symm.trans (mem_filter.mp hu).2)
    have dl : Disjoint short long := by
      rw [Finset.disjoint_left]
      intro t ht hu
      have h := (mem_filter.mp hu).2
      rcases (mem_filter.mp ht).2 with hf | hf <;> omega
    have count : (short ∪ long).card = F.card := by
      rw [card_union_of_disjoint dl, shortEq, card_union_of_disjoint ds, n6, n7, n8, hF]
    apply eq_of_subset_of_card_le _ count.ge
    exact union_subset (filter_subset _ _) (filter_subset _ _)
  have shortIff (t : Finset L) (ht : t ∈ F) :
      t ∈ short ↔ ∃ a : Fin 8, Sum.inl a ∈ t := by
    have weight (l : L) : (row l).card = 2 + Sum.elim (fun _ : Fin 8 => 2) (fun _ : D => 0) l := by
      rcases l with a | b
      · exact sizeStar a
      · exact sizeLight b
    have split (l : L) :
        (row l).card = 2 + (if ∃ a : Fin 8, l = Sum.inl a then 2 else 0) := by
      rw [weight]
      rcases l with a | b <;> simp
    let large := t.filter (fun l => ∃ a : Fin 8, l = Sum.inl a)
    have sums : 2 * t.card + 2 * large.card = 16 := by
      have h := (cover_weight closed (cover t ht)).trans sizeS
      simp_rw [split] at h
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_filter,
        Finset.sum_const, nsmul_eq_mul] at h
      change t.card * 2 + large.card * 2 = 16 at h
      omega
    have largePos : 0 < large.card ↔ ∃ a : Fin 8, Sum.inl a ∈ t := by
      rw [card_pos]
      constructor
      · rintro ⟨l, hl⟩
        obtain ⟨hl, a, rfl⟩ := mem_filter.mp hl
        exact ⟨a,hl⟩
      · rintro ⟨a, ha⟩
        exact ⟨_, mem_filter.mpr ⟨ha,a,rfl⟩⟩
    have tr := show t ∈ short ∨ t ∈ long from mem_union.mp (allBlocks.symm ▸ ht)
    constructor
    · intro h
      rcases (mem_filter.mp h).2 with k | k <;> exact largePos.mp (by omega)
    · intro h
      rcases tr with h' | h'
      · exact h'
      · have hpos := largePos.mpr h
        have k := (mem_filter.mp h').2
        omega
  let shortThrough := short.filter (fun t => pivot ∈ t)
  let longThrough := long.filter (fun t => pivot ∈ t)
  have shortBound : shortThrough.card ≤ 4 := by
    have existsHeavy (t : Finset L) (ht : t ∈ shortThrough) : ∃ a : Fin 8, Sum.inl a ∈ t :=
      (shortIff t (mem_filter.mp (mem_filter.mp ht).1).1).mp (mem_filter.mp ht).1
    choose heavy hh using existsHeavy
    let allowed := (univ : Finset (Fin 8)).filter (fun a => Disjoint (row pivot) (star a))
    have allowedHeavy (t : Finset L) (ht : t ∈ shortThrough) : heavy t ht ∈ allowed := by
      obtain ⟨ht', hp⟩ := mem_filter.mp ht
      have hf := (mem_filter.mp ht').1
      exact mem_filter.mpr ⟨mem_univ _, one_cover_pair cover closed hf hp (hh t ht) (neHeavy _)⟩
    have allowedCard : allowed.card = 4 := four
    rw [← allowedCard]
    apply card_le_card_of_injective (f := fun t => ⟨heavy t.val t.property, allowedHeavy _ _⟩)
    rintro ⟨t, ht⟩ ⟨u, hu⟩ same
    apply Subtype.ext
    have eq : heavy t ht = heavy u hu := congrArg Subtype.val same
    obtain ⟨ht', hp⟩ := mem_filter.mp ht
    obtain ⟨hu', hq⟩ := mem_filter.mp hu
    have hf := (mem_filter.mp ht').1
    have hg := (mem_filter.mp hu').1
    have dis := one_cover_pair cover closed hf hp (hh t ht) (neHeavy _)
    have e : Sum.inl (heavy t ht) ∈ u := by rw [eq]; exact hh u hu
    exact (meet pivot _ (neHeavy _) dis).unique ⟨hf,hp,hh t ht⟩ ⟨hg,hq,e⟩
  have longBound : 5 ≤ longThrough.card := by
    have eq : shortThrough ∪ longThrough = F.filter (fun t => pivot ∈ t) := by
      dsimp only [shortThrough, longThrough]
      rw [← filter_union, allBlocks]
    have dis : Disjoint shortThrough longThrough := by
      rw [Finset.disjoint_left]
      intro t ht hu
      have hl := (mem_filter.mp (mem_filter.mp hu).1).2
      rcases (mem_filter.mp (mem_filter.mp ht).1).2 with k | k <;> omega
    rw [← eq, card_union_of_disjoint dis] at through
    omega
  obtain ⟨extra, subExtra, countExtra⟩ := exists_subset_card_eq longBound
  let G := short ∪ extra
  have extraProp (t) (ht : t ∈ extra) : t ∈ F ∧ t.card = 8 ∧ pivot ∈ t := by
    obtain ⟨hl, hp⟩ := mem_filter.mp (subExtra ht)
    exact ⟨(mem_filter.mp hl).1, (mem_filter.mp hl).2, hp⟩
  have subG : G ⊆ F := union_subset (filter_subset _ _) (fun t ht => (extraProp t ht).1)
  have onlyG (t) (ht : t ∈ G) :
      t.card = 6 ∨ t.card = 7 ∨ (t.card = 8 ∧ pivot ∈ t) := by
    rcases mem_union.mp ht with hm | hm
    · exact (mem_filter.mp hm).2.imp id Or.inl
    · exact Or.inr (Or.inr (extraProp t hm).2)
  have retain (t) (ht : t ∈ F) (hs : t.card = 6 ∨ t.card = 7) : t ∈ G :=
    mem_union_left _ (mem_filter.mpr ⟨ht,hs⟩)
  have counts (k : ℕ) (hk : k = 6 ∨ k = 7) : G.filter (fun t => t.card = k) = F.filter (fun t => t.card = k) := by
    ext t
    rw [mem_filter, mem_filter]
    refine ⟨fun h => ⟨subG h.1, h.2⟩, fun h => ⟨retain t h.1 ?_, h.2⟩⟩
    exact hk.imp (h.2.trans) (h.2.trans)
  have c8 : G.filter (fun t => t.card = 8) = extra := by
    ext t
    rw [mem_filter]
    constructor
    · rintro ⟨ht, he⟩
      rcases mem_union.mp ht with h | h
      · rcases (mem_filter.mp h).2 with k | k <;> omega
      · exact h
    · intro ht
      exact ⟨mem_union_right _ ht, (extraProp t ht).2.1⟩
  have req (a : Fin 8) (l : L) (ne : Sum.inl a ≠ l) (d : Disjoint (star a) (row l)) :
      ∃! t, t ∈ G ∧ Sum.inl a ∈ t ∧ l ∈ t := by
    obtain ⟨t, ht, uniq⟩ := meet (Sum.inl a) l ne d
    exact ⟨t, ⟨mem_union_left _ ((shortIff t ht.1).mpr ⟨a,ht.2.1⟩),ht.2⟩,
      fun u hu => uniq u ⟨subG hu.1,hu.2⟩⟩
  have c6 := (congrArg Finset.card (counts 6 (Or.inl rfl))).trans n6
  have c7 := (congrArg Finset.card (counts 7 (Or.inr rfl))).trans n7
  have c8' := (congrArg Finset.card c8).trans countExtra
  exact ⟨G, c6, c7, c8', onlyG, fun t ht => cover t (subG ht),
    fun t ht u hu => linear t (subG ht) u (subG hu), req⟩

end Projection

set_option maxRecDepth 12000 in
set_option maxHeartbeats 500000 in
theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro h1 h2 w hw
  simp only [List.mem_singleton] at hw
  subst w
  intro Q P S A star C row
  let pointEq : DecidableEq P := by
    dsimp +zetaDelta only [P, Q]
    infer_instance
  letI : DecidableEq P := pointEq
  let pt (i j : Fin 8) (h : i < j) : P := .inl (.inl ⟨(i,j),h⟩)
  let L := Fin 8 ⊕ ↥C
  let base : ↥C := ⟨{pt 0 4 (by decide), pt 1 5 (by decide)}, by
    dsimp +zetaDelta only [pt, C, star, A, S, P, Q]
    decide⟩
  let pivot : L := .inr base
  let s : P := pt 2 6 (by decide)
  rintro ⟨F, hF, cover, linear, meet, n6, n7, n8⟩
  have lin (t : Finset L) (ht : t ∈ F) (u : Finset L) (hu : u ∈ F)
      (ne : t ≠ u) (l : L) (hl : l ∈ t) (m : L) (hm : m ∈ t) (lu : l ∈ u) (mu : m ∈ u) :
      l = m := by
    letI : DecidableEq (↥C) := Classical.decEq _
    apply (Finset.card_le_one.mp (linear t ht u hu ne))
    · rw [Finset.mem_inter]
      exact ⟨hl, lu⟩
    · rw [Finset.mem_inter]
      exact ⟨hm, mu⟩
  have closed (l : L) : row l ⊆ S := by
    rcases l with a | b
    · exact filter_subset _ _
    · exact (mem_powersetCard.mp (mem_sdiff.mp b.property).1).1
  have sizeLight (b : ↥C) : (row (.inr b)).card = 2 :=
    (mem_powersetCard.mp (mem_sdiff.mp b.property).1).2
  have sizeStar : ∀ a : Fin 8, (star a).card = 4 := by
    dsimp +zetaDelta only [star, A, S, P, Q]
    decide +kernel
  have sizeS : S.card = 16 := by
    dsimp +zetaDelta only [S, P, Q]
    decide +kernel
  have mark : s ∈ S := by
    dsimp +zetaDelta only [s, pt, S, P, Q]
    decide
  have off : s ∉ row pivot := by
    dsimp +zetaDelta only [row, pivot, base, s, pt, C, star, A, S, P, Q]
    decide
  have mates : (univ.filter (fun m : L => s ∈ row m ∧ Disjoint (row pivot) (row m))).card = 9 := by
    dsimp +zetaDelta only [L, row, pivot, base, pt, s, C, star, A, S, P, Q]
    decide +kernel
  have four : ((univ : Finset (Fin 8)).filter (fun a => Disjoint (row pivot) (star a))).card = 4 := by
    dsimp +zetaDelta only [row, pivot, base, pt, C, star, A, S, P, Q]
    decide +kernel
  obtain ⟨G, c6, c7, c8', onlyG, coverG, linearG, req⟩ :=
    project (D := ↥C) S star Subtype.val base s F hF n6 n7 n8 sizeS sizeStar sizeLight mark
      closed off mates four cover lin meet
  rcases Classical.em (∃ t ∈ G, t.card = 6 ∧ pivot ∈ t) with hd | hd
  · exact h1 ⟨base, rfl, G, c6, c7, c8', onlyG, coverG, linearG, req, hd⟩
  · exact h2 ⟨base, rfl, G, c6, c7, c8', onlyG, coverG, linearG, req,
      fun t ht hsize hp => hd ⟨t,ht,hsize,hp⟩⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
