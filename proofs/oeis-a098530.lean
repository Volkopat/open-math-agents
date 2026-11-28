import OMAStatements.S_oeis_a098530
import Mathlib

/-!
OEIS A098530: T(n, 1) = tau_4(n + 1).

A solid partition S of n + 1 is a finite down-closed subset of N^4 with n + 1 points. Removing a
maximal point of S leaves a solid partition of n contained in S, and distinct maximal points give
distinct results. So if S can be shrunk in exactly one way, it has exactly one maximal point m;
then every point of S lies below m and S is the box of all points below m.
Conversely a box with side lengths t1, t2, t3, t4 >= 1 and t1 t2 t3 t4 = n + 1 points is a solid
partition of n + 1 whose only shrinking removes its top corner: a down-closed subset containing
the top corner is the whole box.
Boxes with positive side lengths correspond bijectively to their side lengths, so the solid
partitions counted by T(n, 1) correspond to the ordered factorizations counted by tau_4(n + 1).
-/

namespace OMA.A098530

open OMA.S_oeis_a098530

abbrev Q := ℕ × ℕ × ℕ × ℕ

def box (t : Q) : Finset Q :=
  Finset.range t.1 ×ˢ (Finset.range t.2.1 ×ˢ (Finset.range t.2.2.1 ×ˢ Finset.range t.2.2.2))

lemma mem_box (t x : Q) :
    x ∈ box t ↔ x.1 < t.1 ∧ x.2.1 < t.2.1 ∧ x.2.2.1 < t.2.2.1 ∧ x.2.2.2 < t.2.2.2 := by
  simp [box, Finset.mem_product]

lemma card_box (t : Q) : (box t).card = t.1 * t.2.1 * t.2.2.1 * t.2.2.2 := by
  simp [box, Finset.card_product, mul_assoc]

lemma solid_iff (n : ℕ) (S : Finset Q) :
    IsSolidPartition n S ↔ S.card = n ∧ ∀ x ∈ S, ∀ y : Q, y ≤ x → y ∈ S := by
  unfold IsSolidPartition
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro ⟨a, b, c, d⟩ hx ⟨a', b', c', d'⟩ hy
    simp only [Prod.mk_le_mk] at hy
    exact h2 a b c d a' b' c' d' hx hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro a b c d a' b' c' d' hx ha hb hc hd
    exact h2 (a, b, c, d) hx (a', b', c', d') (by
      simp only [Prod.mk_le_mk]
      exact ⟨ha, hb, hc, hd⟩)

lemma erase_solid {n : ℕ} {S : Finset Q} (hS : IsSolidPartition (n + 1) S) {m : Q} (hm : m ∈ S)
    (hmax : ∀ w ∈ S, m ≤ w → w = m) : IsSolidPartition n (S.erase m) ∧ S.erase m ⊆ S := by
  rw [solid_iff] at hS ⊢
  refine ⟨⟨by rw [Finset.card_erase_of_mem hm, hS.1]; rfl, ?_⟩, Finset.erase_subset _ _⟩
  intro x hx y hy
  rw [Finset.mem_erase] at hx ⊢
  refine ⟨?_, hS.2 x hx.2 y hy⟩
  rintro rfl
  exact hx.1 (hmax x hx.2 hy)

lemma shrink_box {n : ℕ} (t : Q) (h1 : 0 < t.1) (h2 : 0 < t.2.1) (h3 : 0 < t.2.2.1)
    (h4 : 0 < t.2.2.2) (hprod : t.1 * t.2.1 * t.2.2.1 * t.2.2.2 = n + 1) :
    IsSolidPartition (n + 1) (box t) ∧ numShrinkings n (box t) = 1 := by
  obtain ⟨t1, t2, t3, t4⟩ := t
  simp only at h1 h2 h3 h4 hprod
  have htopmem : ((t1 - 1, t2 - 1, t3 - 1, t4 - 1) : Q) ∈ box (t1, t2, t3, t4) := by
    rw [mem_box]
    simp only
    omega
  have hle : ∀ y ∈ box (t1, t2, t3, t4), y ≤ ((t1 - 1, t2 - 1, t3 - 1, t4 - 1) : Q) := by
    rintro ⟨a, b, c, d⟩ hy
    rw [mem_box] at hy
    simp only at hy
    simp only [Prod.mk_le_mk]
    omega
  have hsolid : IsSolidPartition (n + 1) (box (t1, t2, t3, t4)) := by
    rw [solid_iff]
    refine ⟨by rw [card_box]; exact hprod, ?_⟩
    rintro ⟨a, b, c, d⟩ hx ⟨a', b', c', d'⟩ hy
    rw [mem_box] at hx ⊢
    simp only [Prod.mk_le_mk] at hy
    simp only at hx ⊢
    omega
  refine ⟨hsolid, ?_⟩
  unfold numShrinkings
  have hset : {T : Finset Q | IsSolidPartition n T ∧ T ⊆ box (t1, t2, t3, t4)} =
      {(box (t1, t2, t3, t4)).erase (t1 - 1, t2 - 1, t3 - 1, t4 - 1)} := by
    ext T
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hT, hsub⟩
      rw [solid_iff] at hT
      have hnot : ((t1 - 1, t2 - 1, t3 - 1, t4 - 1) : Q) ∉ T := by
        intro htop'
        have hsub' : box (t1, t2, t3, t4) ⊆ T := fun y hy => hT.2 _ htop' y (hle y hy)
        have hc := Finset.card_le_card hsub'
        rw [card_box, hT.1] at hc
        simp only at hc
        omega
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        rw [Finset.mem_erase]
        exact ⟨fun h => hnot (h ▸ hy), hsub hy⟩
      · rw [Finset.card_erase_of_mem htopmem, card_box, hT.1]
        simp only
        omega
    · rintro rfl
      exact erase_solid hsolid htopmem (fun w hw hmw => le_antisymm (hle w hw) hmw)
  rw [hset, Set.ncard_singleton]

lemma box_of_unique {n : ℕ} {S : Finset Q} (hS : IsSolidPartition (n + 1) S)
    (h1 : numShrinkings n S = 1) :
    ∃ t : Q, (0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
      t.1 * t.2.1 * t.2.2.1 * t.2.2.2 = n + 1) ∧ box t = S := by
  have hS' := (solid_iff _ _).mp hS
  have hne : S.Nonempty := by
    rw [← Finset.card_pos, hS'.1]
    omega
  obtain ⟨x, hx⟩ := hne
  obtain ⟨m, -, hm⟩ := S.exists_le_maximal hx
  unfold numShrinkings at h1
  obtain ⟨T0, hT0⟩ := Set.ncard_eq_one.mp h1
  have hall : ∀ y ∈ S, y ≤ m := by
    intro y hy
    obtain ⟨m', hym', hm'⟩ := S.exists_le_maximal hy
    have e1 : S.erase m ∈ {T : Finset Q | IsSolidPartition n T ∧ T ⊆ S} :=
      erase_solid hS hm.prop (fun w hw hmw => le_antisymm (hm.le_of_ge hw hmw) hmw)
    have e2 : S.erase m' ∈ {T : Finset Q | IsSolidPartition n T ∧ T ⊆ S} :=
      erase_solid hS hm'.prop (fun w hw hmw => le_antisymm (hm'.le_of_ge hw hmw) hmw)
    rw [hT0, Set.mem_singleton_iff] at e1 e2
    have e : S.erase m = S.erase m' := by rw [e1, e2]
    have hmm : m' = m := by
      by_contra hne'
      have hmem : m ∈ S.erase m' := Finset.mem_erase.mpr ⟨fun h => hne' h.symm, hm.prop⟩
      rw [← e] at hmem
      exact Finset.notMem_erase m S hmem
    rw [← hmm]
    exact hym'
  have hbox : box (m.1 + 1, m.2.1 + 1, m.2.2.1 + 1, m.2.2.2 + 1) = S := by
    obtain ⟨m1, m2, m3, m4⟩ := m
    ext ⟨a, b, c, d⟩
    rw [mem_box]
    simp only
    constructor
    · intro h
      exact hS'.2 _ hm.prop (a, b, c, d) (by
        simp only [Prod.mk_le_mk]
        omega)
    · intro h
      have hle := hall _ h
      simp only [Prod.mk_le_mk] at hle
      omega
  refine ⟨(m.1 + 1, m.2.1 + 1, m.2.2.1 + 1, m.2.2.2 + 1), ⟨?_, ?_, ?_, ?_, ?_⟩, hbox⟩
  · simp
  · simp
  · simp
  · simp
  · rw [← card_box, hbox, hS'.1]

end OMA.A098530

open OMA.S_oeis_a098530 OMA.A098530 in
theorem OMA.solution : type_of% @OMA.S_oeis_a098530.main := by
  intro n _
  unfold T tau4
  have himg : {S : Finset Q | IsSolidPartition (n + 1) S ∧ numShrinkings n S = 1} =
      box '' {t : Q | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
        t.1 * t.2.1 * t.2.2.1 * t.2.2.2 = n + 1} := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hS, h1⟩
      obtain ⟨t, ht, rfl⟩ := box_of_unique hS h1
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ⟨a1, a2, a3, a4, hp⟩, rfl⟩
      exact shrink_box t a1 a2 a3 a4 hp
  rw [himg]
  apply Set.ncard_image_of_injOn
  rintro ⟨t1, t2, t3, t4⟩ ⟨a1, a2, a3, a4, -⟩ ⟨s1, s2, s3, s4⟩ ⟨b1, b2, b3, b4, -⟩ h
  simp only at a1 a2 a3 a4 b1 b2 b3 b4
  have m1 : ((t1 - 1, t2 - 1, t3 - 1, t4 - 1) : Q) ∈ box (s1, s2, s3, s4) := by
    rw [← h, mem_box]
    simp only
    omega
  have m2 : ((s1 - 1, s2 - 1, s3 - 1, s4 - 1) : Q) ∈ box (t1, t2, t3, t4) := by
    rw [h, mem_box]
    simp only
    omega
  rw [mem_box] at m1 m2
  simp only at m1 m2
  simp only [Prod.mk.injEq]
  omega
