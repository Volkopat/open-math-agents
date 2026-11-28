import OMAStatements.S_oeis_a337484

-- Problem: A337484: Number of ordered triples of positive integers summing to n that are neither strictly increasing nor strictly decreasing.
-- Upstream: formal-conjectures statements/oeis-a337484.lean:0 (declaration OMA.S_oeis_a337484.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with comp(m) the number of triples of positive integers summing to m and inc(m), dec(m)
-- the strictly increasing and strictly decreasing ones, a(m) + inc(m) + dec(m) = comp(m), and
-- dec(m) = inc(m) by reversing the triple. Splitting off the triples with first part 1 gives
-- comp(m) = comp(m-1) + (m-2) (subtract 1 from the first part) and inc(m) = inc(m-3) + floor((m-4)/2)
-- (subtract 1 from every part). These four facts at the indices n-6, ..., n give the recurrence.

open OMA.S_oeis_a337484 in
theorem OMA.solution : type_of% @OMA.S_oeis_a337484.main := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Finset (ℕ × ℕ × ℕ),
      ∀ m, B m = Finset.Icc 1 m ×ˢ Finset.Icc 1 m ×ˢ Finset.Icc 1 m := ⟨_, fun _ => rfl⟩
  obtain ⟨comp, hcomp⟩ : ∃ f : ℕ → ℕ, ∀ m,
      f m = ((B m).filter (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = m)).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨inc, hinc⟩ : ∃ f : ℕ → ℕ, ∀ m,
      f m = ((B m).filter (fun t : ℕ × ℕ × ℕ =>
        t.1 + t.2.1 + t.2.2 = m ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2)).card := ⟨_, fun _ => rfl⟩
  obtain ⟨dec, hdec⟩ : ∃ f : ℕ → ℕ, ∀ m,
      f m = ((B m).filter (fun t : ℕ × ℕ × ℕ =>
        t.1 + t.2.1 + t.2.2 = m ∧ t.1 > t.2.1 ∧ t.2.1 > t.2.2)).card := ⟨_, fun _ => rfl⟩
  have memP : ∀ m x y z : ℕ,
      (x, y, z) ∈ (B m).filter (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = m) ↔
        1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x + y + z = m := by
    intro m x y z
    simp only [hB, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    omega
  have memI : ∀ m x y z : ℕ,
      (x, y, z) ∈ (B m).filter (fun t : ℕ × ℕ × ℕ =>
        t.1 + t.2.1 + t.2.2 = m ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2) ↔
        1 ≤ x ∧ x < y ∧ y < z ∧ x + y + z = m := by
    intro m x y z
    simp only [hB, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    omega
  have memD : ∀ m x y z : ℕ,
      (x, y, z) ∈ (B m).filter (fun t : ℕ × ℕ × ℕ =>
        t.1 + t.2.1 + t.2.2 = m ∧ t.1 > t.2.1 ∧ t.2.1 > t.2.2) ↔
        1 ≤ z ∧ z < y ∧ y < x ∧ x + y + z = m := by
    intro m x y z
    simp only [hB, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    omega
  have memF : ∀ (S : Finset (ℕ × ℕ × ℕ)) (x y z : ℕ),
      (x, y, z) ∈ S.filter (fun t => t.1 = 1) ↔ (x, y, z) ∈ S ∧ x = 1 :=
    fun _ _ _ _ => Finset.mem_filter
  have memG : ∀ (S : Finset (ℕ × ℕ × ℕ)) (x y z : ℕ),
      (x, y, z) ∈ S.filter (fun t => ¬ t.1 = 1) ↔ (x, y, z) ∈ S ∧ ¬ x = 1 :=
    fun _ _ _ _ => Finset.mem_filter
  have split : ∀ S : Finset (ℕ × ℕ × ℕ),
      S.card = (S.filter (fun t => t.1 = 1)).card + (S.filter (fun t => ¬ t.1 = 1)).card :=
    fun _ => (Finset.card_filter_add_card_filter_not (fun t : ℕ × ℕ × ℕ => t.1 = 1)).symm
  -- a(m) + inc(m) + dec(m) = comp(m)
  have L1 : ∀ m, a m + inc m + dec m = comp m := by
    intro m
    rw [hcomp, hinc, hdec, hB]
    unfold a
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> omega
  -- dec(m) = inc(m): reverse the triple
  have L2 : ∀ m, dec m = inc m := by
    intro m
    rw [hdec, hinc]
    apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => (t.2.2, t.2.1, t.1))
      (fun t : ℕ × ℕ × ℕ => (t.2.2, t.2.1, t.1))
    · rintro ⟨x, y, z⟩ ht
      rw [Finset.mem_coe, memD] at ht
      rw [Finset.mem_coe]
      show (z, y, x) ∈ _
      rw [memI]
      omega
    · rintro ⟨x, y, z⟩ ht
      rw [Finset.mem_coe, memI] at ht
      rw [Finset.mem_coe]
      show (z, y, x) ∈ _
      rw [memD]
      omega
    · rintro ⟨x, y, z⟩ _
      rfl
    · rintro ⟨x, y, z⟩ _
      rfl
  -- comp(p+1) = comp(p) + (p+1-2)
  have L3 : ∀ m p : ℕ, p + 1 = m → 2 ≤ m → comp m = comp p + (m - 2) := by
    intro m p hp hm
    subst hp
    have e1 : (((B (p + 1)).filter (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = p + 1)).filter
        (fun t => t.1 = 1)).card = (Finset.Icc 1 (p - 1)).card := by
      apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => t.2.1) (fun y => (1, y, p - y))
      · rintro ⟨x, y, z⟩ ht
        rw [Finset.mem_coe, memF, memP] at ht
        rw [Finset.mem_coe]
        show y ∈ Finset.Icc 1 (p - 1)
        rw [Finset.mem_Icc]
        omega
      · intro y hy
        rw [Finset.mem_coe, Finset.mem_Icc] at hy
        rw [Finset.mem_coe]
        show (1, y, p - y) ∈ _
        rw [memF, memP]
        omega
      · rintro ⟨x, y, z⟩ ht
        rw [Finset.mem_coe, memF, memP] at ht
        show (1, y, p - y) = (x, y, z)
        rw [Prod.mk.injEq, Prod.mk.injEq]
        omega
      · intro y _
        rfl
    have e2 : (((B (p + 1)).filter (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = p + 1)).filter
        (fun t => ¬ t.1 = 1)).card =
        ((B p).filter (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = p)).card := by
      apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => (t.1 - 1, t.2.1, t.2.2))
        (fun t : ℕ × ℕ × ℕ => (t.1 + 1, t.2.1, t.2.2))
      · rintro ⟨x, y, z⟩ ht
        rw [Finset.mem_coe, memG, memP] at ht
        rw [Finset.mem_coe]
        show (x - 1, y, z) ∈ _
        rw [memP]
        omega
      · rintro ⟨x, y, z⟩ ht
        rw [Finset.mem_coe, memP] at ht
        rw [Finset.mem_coe]
        show (x + 1, y, z) ∈ _
        rw [memG, memP]
        omega
      · rintro ⟨x, y, z⟩ ht
        rw [Finset.mem_coe, memG, memP] at ht
        show (x - 1 + 1, y, z) = (x, y, z)
        rw [Prod.mk.injEq, Prod.mk.injEq]
        omega
      · rintro ⟨x, y, z⟩ _
        show (x + 1 - 1, y, z) = (x, y, z)
        rw [Prod.mk.injEq, Prod.mk.injEq]
        omega
    rw [hcomp (p + 1), hcomp p,
      split ((B (p + 1)).filter (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = p + 1)),
      e1, e2, Nat.card_Icc]
    omega
  -- inc(p+3) = inc(p) + floor((p+3-4)/2)
  have L4 : ∀ m p : ℕ, p + 3 = m → inc m = inc p + (m - 4) / 2 := by
    intro m p hp
    subst hp
    have e1 : (((B (p + 3)).filter (fun t : ℕ × ℕ × ℕ =>
        t.1 + t.2.1 + t.2.2 = p + 3 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2)).filter
        (fun t => t.1 = 1)).card = (Finset.Icc 2 ((p + 1) / 2)).card := by
      apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => t.2.1) (fun y => (1, y, p + 2 - y))
      · rintro ⟨x, y, z⟩ ht
        rw [Finset.mem_coe, memF, memI] at ht
        rw [Finset.mem_coe]
        show y ∈ Finset.Icc 2 ((p + 1) / 2)
        rw [Finset.mem_Icc]
        omega
      · intro y hy
        rw [Finset.mem_coe, Finset.mem_Icc] at hy
        rw [Finset.mem_coe]
        show (1, y, p + 2 - y) ∈ _
        rw [memF, memI]
        omega
      · rintro ⟨x, y, z⟩ ht
        rw [Finset.mem_coe, memF, memI] at ht
        show (1, y, p + 2 - y) = (x, y, z)
        rw [Prod.mk.injEq, Prod.mk.injEq]
        omega
      · intro y _
        rfl
    have e2 : (((B (p + 3)).filter (fun t : ℕ × ℕ × ℕ =>
        t.1 + t.2.1 + t.2.2 = p + 3 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2)).filter
        (fun t => ¬ t.1 = 1)).card =
        ((B p).filter (fun t : ℕ × ℕ × ℕ =>
          t.1 + t.2.1 + t.2.2 = p ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2)).card := by
      apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => (t.1 - 1, t.2.1 - 1, t.2.2 - 1))
        (fun t : ℕ × ℕ × ℕ => (t.1 + 1, t.2.1 + 1, t.2.2 + 1))
      · rintro ⟨x, y, z⟩ ht
        rw [Finset.mem_coe, memG, memI] at ht
        rw [Finset.mem_coe]
        show (x - 1, y - 1, z - 1) ∈ _
        rw [memI]
        omega
      · rintro ⟨x, y, z⟩ ht
        rw [Finset.mem_coe, memI] at ht
        rw [Finset.mem_coe]
        show (x + 1, y + 1, z + 1) ∈ _
        rw [memG, memI]
        omega
      · rintro ⟨x, y, z⟩ ht
        rw [Finset.mem_coe, memG, memI] at ht
        show (x - 1 + 1, y - 1 + 1, z - 1 + 1) = (x, y, z)
        rw [Prod.mk.injEq, Prod.mk.injEq]
        omega
      · rintro ⟨x, y, z⟩ _
        show (x + 1 - 1, y + 1 - 1, z + 1 - 1) = (x, y, z)
        rw [Prod.mk.injEq, Prod.mk.injEq]
        omega
    rw [hinc (p + 3), hinc p,
      split ((B (p + 3)).filter (fun t : ℕ × ℕ × ℕ =>
        t.1 + t.2.1 + t.2.2 = p + 3 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2)),
      e1, e2, Nat.card_Icc]
    omega
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
    show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega,
    show k + 7 - 6 = k + 1 by omega]
  have e7 := L1 (k + 7)
  have e6 := L1 (k + 6)
  have e5 := L1 (k + 5)
  have e3 := L1 (k + 3)
  have e2 := L1 (k + 2)
  have e1 := L1 (k + 1)
  have d7 := L2 (k + 7)
  have d6 := L2 (k + 6)
  have d5 := L2 (k + 5)
  have d3 := L2 (k + 3)
  have d2 := L2 (k + 2)
  have d1 := L2 (k + 1)
  have c7 := L3 (k + 7) (k + 6) (by omega) (by omega)
  have c6 := L3 (k + 6) (k + 5) (by omega) (by omega)
  have c5 := L3 (k + 5) (k + 4) (by omega) (by omega)
  have c4 := L3 (k + 4) (k + 3) (by omega) (by omega)
  have c3 := L3 (k + 3) (k + 2) (by omega) (by omega)
  have c2 := L3 (k + 2) (k + 1) (by omega) (by omega)
  have i7 := L4 (k + 7) (k + 4) (by omega)
  have i6 := L4 (k + 6) (k + 3) (by omega)
  have i5 := L4 (k + 5) (k + 2) (by omega)
  have i4 := L4 (k + 4) (k + 1) (by omega)
  omega
