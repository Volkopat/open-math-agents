import OMAStatements.S_oeis_a189807

namespace OMA.S_oeis_a189807

open Finset




/-! ## Right angles -/

instance {k m : ℕ} (p q r : Fin k × Fin m) : Decidable (Perp p q r) := by
  unfold Perp; infer_instance

lemma perp_symm {k m : ℕ} {p q r : Fin k × Fin m} (h : Perp p q r) : Perp p r q := by
  unfold Perp at h ⊢
  linarith

/-- A triangle has at most one right angle. -/
lemma eq_of_perp {k m : ℕ} {p q r : Fin k × Fin m} (h1 : Perp p q r) (h2 : Perp q p r) :
    p = q := by
  unfold Perp at h1 h2
  have h : ((q.1 : ℤ) - p.1) ^ 2 + ((q.2 : ℤ) - p.2) ^ 2 = 0 := by linear_combination h1 + h2
  have h3 : (q.1 : ℤ) - p.1 = 0 := by
    nlinarith [sq_nonneg ((q.1 : ℤ) - p.1), sq_nonneg ((q.2 : ℤ) - p.2)]
  have h4 : (q.2 : ℤ) - p.2 = 0 := by
    nlinarith [sq_nonneg ((q.1 : ℤ) - p.1), sq_nonneg ((q.2 : ℤ) - p.2)]
  ext <;> omega

/-- The row-major index of a point. -/
def ix {k m : ℕ} (p : Fin k × Fin m) : ℕ := p.2 * k + p.1

lemma ix_inj {k m : ℕ} {p q : Fin k × Fin m} (h : ix p = ix q) : p = q := by
  unfold ix at h
  have hp := p.1.2
  have hq := q.1.2
  rcases lt_trichotomy (p.2 : ℕ) q.2 with h1 | h1 | h1
  · have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt h1)
    rw [Nat.succ_mul] at this
    omega
  · have h2 : (p.1 : ℕ) = q.1 := by rw [h1] at h; omega
    exact Prod.ext (Fin.ext h2) (Fin.ext h1)
  · have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt h1)
    rw [Nat.succ_mul] at this
    omega

/-- Right triangles as triples: the right-angle vertex first, the other two by index. -/
def Canon {k m : ℕ} (t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m)) : Prop :=
  t.2.1 ≠ t.1 ∧ t.2.2 ≠ t.1 ∧ ix t.2.1 < ix t.2.2 ∧ Perp t.1 t.2.1 t.2.2

instance {k m : ℕ} : DecidablePred (Canon (k := k) (m := m)) := fun t => by
  unfold Canon; infer_instance

lemma card_right (k m : ℕ) :
    Nat.card {T : Finset (Fin k × Fin m) // IsRight T} =
      (univ.filter (Canon (k := k) (m := m))).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  symm
  apply Finset.card_bij (fun t _ => ({t.1, t.2.1, t.2.2} : Finset (Fin k × Fin m)))
  · rintro ⟨p, q, r⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Canon] at ht ⊢
    obtain ⟨hqp, hrp, hix, hperp⟩ := ht
    have hqr : q ≠ r := fun h => by rw [h] at hix; omega
    refine ⟨Finset.card_eq_three.2 ⟨p, q, r, Ne.symm hqp, Ne.symm hrp, hqr, rfl⟩, p, by simp,
      q, by simp, r, by simp, Ne.symm hqp, Ne.symm hrp, hqr, hperp⟩
  · rintro ⟨p, q, r⟩ ht ⟨p', q', r'⟩ ht' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Canon] at ht ht'
    obtain ⟨hqp, hrp, hix, hperp⟩ := ht
    obtain ⟨hqp', hrp', hix', hperp'⟩ := ht'
    have hqr' : q' ≠ r' := fun h => by rw [h] at hix'; omega
    have mem : ∀ x, x ∈ ({p', q', r'} : Finset (Fin k × Fin m)) → x = p ∨ x = q ∨ x = r := by
      intro x hx
      rw [← h] at hx
      simpa using hx
    have hp' := mem p' (by simp)
    have hq' := mem q' (by simp)
    have hr' := mem r' (by simp)
    rcases hp' with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl <;>
      rcases hr' with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hqp' | exact absurd rfl hrp' | exact absurd rfl hqr'
      | rfl
      | (exfalso; omega)
      | (exfalso; exact hqp (eq_of_perp hperp hperp').symm)
      | (exfalso; exact hqp (eq_of_perp hperp (perp_symm hperp')).symm)
      | (exfalso; exact hrp (eq_of_perp (perp_symm hperp) hperp').symm)
      | (exfalso; exact hrp (eq_of_perp (perp_symm hperp) (perp_symm hperp')).symm)
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨hcard, p, hp, q, hq, r, hr, hpq, hpr, hqr, hperp⟩ := hT
    have hsub : ({p, q, r} : Finset (Fin k × Fin m)) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hT3 : ({p, q, r} : Finset (Fin k × Fin m)) = T :=
      Finset.eq_of_subset_of_card_le hsub
        (by rw [hcard, Finset.card_eq_three.2 ⟨p, q, r, hpq, hpr, hqr, rfl⟩])
    have hne : ix q ≠ ix r := fun h => hqr (ix_inj h)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(p, q, r), by simp [Canon, Ne.symm hpq, Ne.symm hpr, hlt, hperp], hT3⟩
    · refine ⟨(p, r, q), by simp [Canon, Ne.symm hpq, Ne.symm hpr, hgt, perp_symm hperp], ?_⟩
      rw [← hT3]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto

/-! ## Triangles with a horizontal and a vertical side -/

/-- Both sides at the right angle are oblique (no coordinate difference vanishes). -/
def Obl {k m : ℕ} (t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m)) : Prop :=
  (t.2.1.1 : ℕ) ≠ t.1.1 ∧ (t.2.1.2 : ℕ) ≠ t.1.2 ∧ (t.2.2.1 : ℕ) ≠ t.1.1 ∧ (t.2.2.2 : ℕ) ≠ t.1.2

instance {k m : ℕ} : DecidablePred (Obl (k := k) (m := m)) := fun t => by
  unfold Obl; infer_instance

/-- The axis-parallel right triangle with the right angle at (x0, y0) and its other corners
in column x1 and row y1. -/
def axisTri {k m : ℕ} (a : (Fin k × Fin k) × (Fin m × Fin m)) :
    (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) :=
  if (a.2.1 : ℕ) < a.2.2 then ((a.1.1, a.2.1), (a.1.2, a.2.1), (a.1.1, a.2.2))
  else ((a.1.1, a.2.1), (a.1.1, a.2.2), (a.1.2, a.2.1))

lemma card_axis (k m : ℕ) :
    (univ.filter (fun t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) =>
      Canon t ∧ ¬ Obl t)).card = (k * k - k) * (m * m - m) := by
  have hc : ((univ : Finset (Fin k)).offDiag ×ˢ (univ : Finset (Fin m)).offDiag).card =
      (k * k - k) * (m * m - m) := by
    rw [Finset.card_product, Finset.offDiag_card, Finset.offDiag_card, Finset.card_univ,
      Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  rw [← hc]
  symm
  apply Finset.card_bij (fun a _ => axisTri a)
  · rintro ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ ha
    simp only [Finset.mem_product, Finset.mem_offDiag, Finset.mem_univ, true_and] at ha
    obtain ⟨hx, hy⟩ := ha
    have hx' : (x0 : ℕ) ≠ x1 := fun h => hx (Fin.ext h)
    have hy' : (y0 : ℕ) ≠ y1 := fun h => hy (Fin.ext h)
    have hx0 := x0.2
    have hx1 := x1.2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold axisTri
    dsimp only
    split_ifs with h
    · have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at this
      refine ⟨⟨fun e => hx (Prod.ext_iff.1 e).1.symm, fun e => hy (Prod.ext_iff.1 e).2.symm,
        by unfold ix; dsimp only; omega, by unfold Perp; ring⟩, fun ho => ho.2.1 rfl⟩
    · have h' : (y1 : ℕ) < y0 := by omega
      have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt h')
      rw [Nat.succ_mul] at this
      refine ⟨⟨fun e => hy (Prod.ext_iff.1 e).2.symm, fun e => hx (Prod.ext_iff.1 e).1.symm,
        by unfold ix; dsimp only; omega, by unfold Perp; ring⟩, fun ho => ho.1 rfl⟩
  · rintro ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ ha ⟨⟨x0', x1'⟩, ⟨y0', y1'⟩⟩ ha' h
    simp only [Finset.mem_product, Finset.mem_offDiag, Finset.mem_univ, true_and] at ha ha'
    simp only [axisTri] at h
    split_ifs at h with h1 h2 h2 <;> simp only [Prod.mk.injEq] at h
    · obtain ⟨⟨e1, e2⟩, ⟨e3, -⟩, -, e4⟩ := h
      subst e1 e2 e3 e4
      rfl
    · obtain ⟨⟨e1, -⟩, ⟨e3, -⟩, -, -⟩ := h
      exact absurd (e3.trans e1.symm) (Ne.symm ha.1)
    · obtain ⟨⟨e1, -⟩, ⟨e3, -⟩, -, -⟩ := h
      exact absurd (e1.symm.trans e3) ha'.1
    · obtain ⟨⟨e1, e2⟩, ⟨-, e3⟩, e4, -⟩ := h
      subst e1 e2 e3 e4
      rfl
  · rintro ⟨⟨x0, y0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Canon, Obl, Perp, ix, ne_eq,
      Prod.mk.injEq, not_and] at ht
    obtain ⟨⟨hq, hr, hix, hperp⟩, hob⟩ := ht
    have ha1 := a1.2
    have ha2 := a2.2
    -- case A: q is in the column of p and r in its row; case B: the other way round
    have caseA : (a1 : ℕ) = x0 → (b2 : ℕ) = y0 →
        ∃ a, ∃ (_ : a ∈ ((univ : Finset (Fin k)).offDiag ×ˢ (univ : Finset (Fin m)).offDiag)),
          axisTri a = ((x0, y0), (a1, b1), (a2, b2)) := by
      intro e1 e2
      have hb1 : (b1 : ℕ) ≠ y0 := fun h => hq (Fin.ext e1) (Fin.ext h)
      have ha2' : (a2 : ℕ) ≠ x0 := fun h => hr (Fin.ext h) (Fin.ext e2)
      have hlt : (b1 : ℕ) < y0 := by
        by_contra hc
        have h' : (y0 : ℕ) < b1 := by omega
        have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt h')
        rw [Nat.succ_mul] at this
        rw [e2] at hix
        omega
      refine ⟨((x0, a2), (y0, b1)), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_offDiag, Finset.mem_univ, true_and]
        exact ⟨fun h => ha2' (by rw [← h]), fun h => hb1 (by rw [← h])⟩
      · have : ¬ ((y0 : ℕ) < b1) := by omega
        simp only [axisTri, if_neg this]
        rw [show a1 = x0 from Fin.ext e1, show b2 = y0 from Fin.ext e2]
    have caseB : (b1 : ℕ) = y0 → (a2 : ℕ) = x0 →
        ∃ a, ∃ (_ : a ∈ ((univ : Finset (Fin k)).offDiag ×ˢ (univ : Finset (Fin m)).offDiag)),
          axisTri a = ((x0, y0), (a1, b1), (a2, b2)) := by
      intro e1 e2
      have ha1' : (a1 : ℕ) ≠ x0 := fun h => hq (Fin.ext h) (Fin.ext e1)
      have hb2 : (b2 : ℕ) ≠ y0 := fun h => hr (Fin.ext e2) (Fin.ext h)
      have hlt : (y0 : ℕ) < b2 := by
        by_contra hc
        have h' : (b2 : ℕ) < y0 := by omega
        have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt h')
        rw [Nat.succ_mul] at this
        rw [e1] at hix
        omega
      refine ⟨((x0, a1), (y0, b2)), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_offDiag, Finset.mem_univ, true_and]
        exact ⟨fun h => ha1' (by rw [← h]), fun h => hb2 (by rw [← h])⟩
      · simp only [axisTri, if_pos hlt]
        rw [show b1 = y0 from Fin.ext e1, show a2 = x0 from Fin.ext e2]
    have hz : ∀ u v : ℤ, u * v = 0 → u ≠ 0 → v = 0 := fun u v h hu =>
      (mul_eq_zero.1 h).resolve_left hu
    by_cases e1 : (a1 : ℕ) = x0
    · apply caseA e1
      have h0 : ((b1 : ℤ) - y0) * ((b2 : ℤ) - y0) = 0 := by rw [e1] at hperp; simpa using hperp
      have hb1 : ((b1 : ℤ) - y0) ≠ 0 := fun h => hq (Fin.ext e1) (Fin.ext (by omega))
      have := hz _ _ h0 hb1
      omega
    by_cases e2 : (b1 : ℕ) = y0
    · apply caseB e2
      have h0 : ((a1 : ℤ) - x0) * ((a2 : ℤ) - x0) = 0 := by rw [e2] at hperp; simpa using hperp
      have ha1 : ((a1 : ℤ) - x0) ≠ 0 := fun h => e1 (by omega)
      have := hz _ _ h0 ha1
      omega
    by_cases e3 : (a2 : ℕ) = x0
    · apply caseB _ e3
      have h0 : ((b1 : ℤ) - y0) * ((b2 : ℤ) - y0) = 0 := by rw [e3] at hperp; simpa using hperp
      have hb2 : ((b2 : ℤ) - y0) ≠ 0 := fun h => hr (Fin.ext e3) (Fin.ext (by omega))
      have := hz _ _ (by rw [mul_comm]; exact h0) hb2
      omega
    · have e4 : (b2 : ℕ) = y0 := by
        by_contra e4
        exact hob e1 e2 e3 e4
      apply caseA _ e4
      have h0 : ((a1 : ℤ) - x0) * ((a2 : ℤ) - x0) = 0 := by rw [e4] at hperp; simpa using hperp
      have ha2 : ((a2 : ℤ) - x0) ≠ 0 := fun h => e3 (by omega)
      have := hz _ _ (by rw [mul_comm]; exact h0) ha2
      omega

/-! ## Triangles with both sides at the right angle oblique -/

/-- The spread (largest minus smallest) of 0, a and b. -/
def wd (a b : ℤ) : ℕ := (max 0 (max a b) - min 0 (min a b)).toNat

/-- The offsets of the second and third points from the first. -/
def off {k m : ℕ} (t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m)) :
    (ℤ × ℤ) × (ℤ × ℤ) :=
  (((t.2.1.1 : ℤ) - t.1.1, (t.2.1.2 : ℤ) - t.1.2), ((t.2.2.1 : ℤ) - t.1.1, (t.2.2.2 : ℤ) - t.1.2))

/-- Offset pairs of an oblique right angle, in index order, of horizontal spread below k. -/
def OblO (k : ℕ) (o : (ℤ × ℤ) × (ℤ × ℤ)) : Prop :=
  o.1.1 ≠ 0 ∧ o.1.2 ≠ 0 ∧ o.2.1 ≠ 0 ∧ o.2.2 ≠ 0 ∧ o.1.1 * o.2.1 + o.1.2 * o.2.2 = 0 ∧
    o.1.2 * k + o.1.1 < o.2.2 * k + o.2.1 ∧ wd o.1.1 o.2.1 < k

instance (k : ℕ) : DecidablePred (OblO k) := fun o => by unfold OblO; infer_instance

noncomputable def box (k Q : ℕ) : Finset (ℤ × ℤ) :=
  Icc (-((k : ℤ) - 1)) ((k : ℤ) - 1) ×ˢ Icc (-(Q : ℤ)) Q

/-- All oblique offset pairs, for vertical offsets up to Q. -/
noncomputable def Ob (k Q : ℕ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (box k Q ×ˢ box k Q).filter (OblO k)

/-- The positions x of a line of length N with x + a and x + b on the line. -/
def line3 (N : ℕ) (a b : ℤ) : Finset (Fin N) :=
  univ.filter (fun x => 0 ≤ (x : ℤ) + a ∧ (x : ℤ) + a < N ∧ 0 ≤ (x : ℤ) + b ∧ (x : ℤ) + b < N)

lemma max3 (a b : ℤ) : 0 ≤ max 0 (max a b) ∧ a ≤ max 0 (max a b) ∧ b ≤ max 0 (max a b) ∧
    (max 0 (max a b) = 0 ∨ max 0 (max a b) = a ∨ max 0 (max a b) = b) := by
  refine ⟨le_max_left _ _, le_trans (le_max_left a b) (le_max_right _ _),
    le_trans (le_max_right a b) (le_max_right _ _), ?_⟩
  rcases max_choice 0 (max a b) with h | h
  · exact Or.inl h
  · rcases max_choice a b with h' | h'
    · exact Or.inr (Or.inl (h.trans h'))
    · exact Or.inr (Or.inr (h.trans h'))

lemma min3 (a b : ℤ) : min 0 (min a b) ≤ 0 ∧ min 0 (min a b) ≤ a ∧ min 0 (min a b) ≤ b ∧
    (min 0 (min a b) = 0 ∨ min 0 (min a b) = a ∨ min 0 (min a b) = b) := by
  refine ⟨min_le_left _ _, le_trans (min_le_right _ _) (min_le_left a b),
    le_trans (min_le_right _ _) (min_le_right a b), ?_⟩
  rcases min_choice 0 (min a b) with h | h
  · exact Or.inl h
  · rcases min_choice a b with h' | h'
    · exact Or.inr (Or.inl (h.trans h'))
    · exact Or.inr (Or.inr (h.trans h'))

lemma card_line3 (N : ℕ) (a b : ℤ) : (line3 N a b).card = N - wd a b := by
  obtain ⟨s1, s2, s3, s4⟩ := max3 a b
  obtain ⟨i1, i2, i3, i4⟩ := min3 a b
  unfold wd
  generalize max 0 (max a b) = S at *
  generalize min 0 (min a b) = I at *
  have e : (line3 N a b).map Fin.valEmbedding = Finset.Ico (-I).toNat (N - S.toNat) := by
    ext x
    simp only [line3, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨y, ⟨h1, h2, h3, h4⟩, rfl⟩
      constructor
      · rcases i4 with h | h | h <;> omega
      · rcases s4 with h | h | h <;> omega
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, by omega⟩, ?_, rfl⟩
      simp only [Fin.val_mk]
      refine ⟨by omega, by omega, by omega, by omega⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Nat.card_Ico]
  omega

lemma wd_le (a b L U : ℤ) (hL : L ≤ 0) (hU : 0 ≤ U) (ha : L ≤ a ∧ a ≤ U) (hb : L ≤ b ∧ b ≤ U) :
    (wd a b : ℤ) ≤ U - L := by
  obtain ⟨s1, s2, s3, s4⟩ := max3 a b
  obtain ⟨i1, i2, i3, i4⟩ := min3 a b
  unfold wd
  have hS : max 0 (max a b) ≤ U := by rcases s4 with h | h | h <;> omega
  have hI : L ≤ min 0 (min a b) := by rcases i4 with h | h | h <;> omega
  omega

/-- Perpendicular oblique sides of horizontal extent below k have vertical extent at most
(k - 1)^2. -/
lemma bound_y (k : ℕ) {a1 b1 a2 b2 : ℤ} (h1 : |a1| ≤ (k : ℤ) - 1) (h2 : |a2| ≤ (k : ℤ) - 1)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0) (h : a1 * a2 + b1 * b2 = 0) :
    |b1| ≤ ((k : ℤ) - 1) ^ 2 ∧ |b2| ≤ ((k : ℤ) - 1) ^ 2 := by
  have e : |b1| * |b2| = |a1| * |a2| := by
    rw [← abs_mul, ← abs_mul, show b1 * b2 = -(a1 * a2) by linarith, abs_neg]
  have c1 : 1 ≤ |b1| := Int.one_le_abs hb1
  have c2 : 1 ≤ |b2| := Int.one_le_abs hb2
  have p1 := abs_nonneg a1
  have p2 := abs_nonneg a2
  have hk : |a1| * |a2| ≤ ((k : ℤ) - 1) ^ 2 := by nlinarith
  constructor <;> nlinarith

lemma off_mem (k m : ℕ) (t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m))
    (ht : Canon t ∧ Obl t) : off t ∈ Ob k ((k - 1) ^ 2) := by
  obtain ⟨p, q, r⟩ := t
  obtain ⟨⟨hqp, hrp, hix, hperp⟩, hob⟩ := ht
  unfold Obl at hob
  unfold Perp at hperp
  unfold ix at hix
  obtain ⟨o1, o2, o3, o4⟩ := hob
  dsimp only at o1 o2 o3 o4 hix hperp
  have hp1 := p.1.2
  have hq1 := q.1.2
  have hr1 := r.1.2
  have hk : 1 ≤ k := by omega
  have ha1 : |(q.1 : ℤ) - p.1| ≤ (k : ℤ) - 1 := by rw [abs_le]; constructor <;> omega
  have ha2 : |(r.1 : ℤ) - p.1| ≤ (k : ℤ) - 1 := by rw [abs_le]; constructor <;> omega
  obtain ⟨hb1, hb2⟩ := bound_y k ha1 ha2 (by omega) (by omega) hperp
  have hQ : (((k - 1) ^ 2 : ℕ) : ℤ) = ((k : ℤ) - 1) ^ 2 := by push_cast [Nat.cast_sub hk]; ring
  simp only [Ob, box, off, OblO, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  rw [abs_le] at ha1 ha2 hb1 hb2
  rw [hQ]
  have hix' : ((q.2 : ℕ) * k + q.1 : ℤ) < (r.2 : ℕ) * k + r.1 := by exact_mod_cast hix
  refine ⟨⟨⟨⟨by omega, by omega⟩, ⟨by linarith, by linarith⟩⟩, ⟨⟨by omega, by omega⟩,
    ⟨by linarith, by linarith⟩⟩⟩, by omega, by omega, by omega, by omega, hperp,
    by push_cast at hix' ⊢; nlinarith, ?_⟩
  have := wd_le ((q.1 : ℤ) - p.1) ((r.1 : ℤ) - p.1) (-(p.1 : ℤ)) ((k : ℤ) - 1 - p.1)
    (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  omega

lemma card_fiber (k m : ℕ) (o : (ℤ × ℤ) × (ℤ × ℤ)) (ho : OblO k o) :
    (univ.filter (fun t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) =>
      (Canon t ∧ Obl t) ∧ off t = o)).card = (k - wd o.1.1 o.2.1) * (m - wd o.1.2 o.2.2) := by
  obtain ⟨⟨u1, u2⟩, ⟨v1, v2⟩⟩ := o
  obtain ⟨n1, n2, n3, n4, hperp, hord, -⟩ := ho
  dsimp only at n1 n2 n3 n4 hperp hord ⊢
  rw [← card_line3, ← card_line3, ← Finset.card_product]
  apply Finset.card_bij (fun t _ => (t.1.1, t.1.2))
  · rintro ⟨p, q, r⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, off, Prod.mk.injEq] at ht
    obtain ⟨-, ⟨e1, e2⟩, e3, e4⟩ := ht
    have := q.1.2
    have := q.2.2
    have := r.1.2
    have := r.2.2
    simp only [Finset.mem_product, line3, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> refine ⟨by omega, by omega, by omega, by omega⟩
  · rintro ⟨p, q, r⟩ ht ⟨p', q', r'⟩ ht' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, off, Prod.mk.injEq] at ht ht' h
    obtain ⟨-, ⟨e1, e2⟩, e3, e4⟩ := ht
    obtain ⟨-, ⟨e1', e2'⟩, e3', e4'⟩ := ht'
    obtain ⟨h1, h2⟩ := h
    have hp : p = p' := Prod.ext h1 h2
    subst hp
    have hq : q = q' := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    have hr : r = r' := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    rw [hq, hr]
  · rintro ⟨x, y⟩ hxy
    simp only [Finset.mem_product, line3, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩ := hxy
    obtain ⟨qx, hq1⟩ : ∃ z : Fin k, ((z : ℕ) : ℤ) = x + u1 :=
      ⟨⟨((x : ℤ) + u1).toNat, by omega⟩, by simp only; omega⟩
    obtain ⟨qy, hq2⟩ : ∃ z : Fin m, ((z : ℕ) : ℤ) = y + u2 :=
      ⟨⟨((y : ℤ) + u2).toNat, by omega⟩, by simp only; omega⟩
    obtain ⟨rx, hr1⟩ : ∃ z : Fin k, ((z : ℕ) : ℤ) = x + v1 :=
      ⟨⟨((x : ℤ) + v1).toNat, by omega⟩, by simp only; omega⟩
    obtain ⟨ry, hr2⟩ : ∃ z : Fin m, ((z : ℕ) : ℤ) = y + v2 :=
      ⟨⟨((y : ℤ) + v2).toNat, by omega⟩, by simp only; omega⟩
    refine ⟨((x, y), (qx, qy), (rx, ry)), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨⟨fun h => n1 ?_, fun h => n3 ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · have := congrArg (fun z : Fin k × Fin m => ((z.1 : ℕ) : ℤ)) h
      simp only at this
      omega
    · have := congrArg (fun z : Fin k × Fin m => ((z.1 : ℕ) : ℤ)) h
      simp only at this
      omega
    · show (qy : ℕ) * k + qx < (ry : ℕ) * k + rx
      have : ((qy : ℕ) * k + qx : ℤ) < (ry : ℕ) * k + rx := by
        rw [hq1, hq2, hr1, hr2]
        nlinarith
      exact_mod_cast this
    · show ((qx : ℤ) - x) * ((rx : ℤ) - x) + ((qy : ℤ) - y) * ((ry : ℤ) - y) = 0
      rw [hq1, hq2, hr1, hr2]
      linear_combination hperp
    · show (qx : ℕ) ≠ x
      omega
    · show (qy : ℕ) ≠ y
      omega
    · show (rx : ℕ) ≠ x
      omega
    · show (ry : ℕ) ≠ y
      omega
    · show (((qx : ℤ) - x, (qy : ℤ) - y), ((rx : ℤ) - x, (ry : ℤ) - y)) = ((u1, u2), (v1, v2))
      rw [hq1, hq2, hr1, hr2]
      simp

lemma card_obl (k m : ℕ) :
    (univ.filter (fun t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) =>
      Canon t ∧ Obl t)).card =
      ∑ o ∈ Ob k ((k - 1) ^ 2), (k - wd o.1.1 o.2.1) * (m - wd o.1.2 o.2.2) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := off) (t := Ob k ((k - 1) ^ 2))
    (fun t ht => off_mem k m t (Finset.mem_filter.1 ht).2)]
  apply Finset.sum_congr rfl
  intro o ho
  rw [Finset.filter_filter]
  exact card_fiber k m o (Finset.mem_filter.1 ho).2

/-- Right triangles on the grid of k columns and m rows. -/
theorem card_tri (k m : ℕ) :
    Nat.card {T : Finset (Fin k × Fin m) // IsRight T} = (k * k - k) * (m * m - m) +
      ∑ o ∈ Ob k ((k - 1) ^ 2), (k - wd o.1.1 o.2.1) * (m - wd o.1.2 o.2.2) := by
  rw [card_right, ← Finset.card_filter_add_card_filter_not (fun t => Obl t),
    Finset.filter_filter, Finset.filter_filter, add_comm, card_axis, card_obl]

/-- The oblique offset pairs, as the kernel lists them. -/
def obl : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-2, -4), (-2, 1)),
   ((-2, -2), (-2, 2)),
   ((-2, -2), (-1, 1)),
   ((-2, -1), (-2, 4)),
   ((-2, -1), (-1, 2)),
   ((-1, -2), (-2, 1)),
   ((-1, -1), (-2, 2)),
   ((-1, -1), (-1, 1)),
   ((-1, -1), (1, -1)),
   ((-1, 1), (1, 1)),
   ((1, -2), (2, 1)),
   ((1, -1), (1, 1)),
   ((1, -1), (2, 2)),
   ((2, -4), (2, 1)),
   ((2, -2), (1, 1)),
   ((2, -2), (2, 2)),
   ((2, -1), (1, 2)),
   ((2, -1), (2, 4))]

lemma ob_eq : Ob 3 ((3 - 1) ^ 2) = obl.toFinset := by
  decide +kernel

lemma obl_nodup : obl.Nodup := by
  decide +kernel

lemma obl_w : obl.map (fun o => (3 - wd o.1.1 o.2.1, wd o.1.2 o.2.2)) = [(1, 5), (1, 4), (1, 3), (1, 5), (1, 3), (1, 3), (1, 3), (2, 2), (1, 1), (1, 1), (1, 3), (2, 2), (1, 3), (1, 5), (1, 3), (1, 4), (1, 3), (1, 5)] := by
  decide +kernel

/-- a(n) from the axis-parallel and the oblique triangles. -/
theorem a_expand (n : ℕ) : a n = 6 * ((n + 1) * n) + (1 * (n + 1 - 5) + (1 * (n + 1 - 4) + (1 * (n + 1 - 3) + (1 * (n + 1 - 5) + (1 * (n + 1 - 3) + (1 * (n + 1 - 3) + (1 * (n + 1 - 3) + (2 * (n + 1 - 2) + (1 * (n + 1 - 1) + (1 * (n + 1 - 1) + (1 * (n + 1 - 3) + (2 * (n + 1 - 2) + (1 * (n + 1 - 3) + (1 * (n + 1 - 5) + (1 * (n + 1 - 3) + (1 * (n + 1 - 4) + (1 * (n + 1 - 3) + (1 * (n + 1 - 5) + 0)))))))))))))))))) := by
  unfold a
  rw [card_tri, show (3 * 3 - 3 : ℕ) = 6 from rfl,
    show (n + 1) * (n + 1) - (n + 1) = (n + 1) * n by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]; ring,
    ob_eq, List.sum_toFinset _ obl_nodup]
  have e : obl.map (fun o => (3 - wd o.1.1 o.2.1) * (n + 1 - wd o.1.2 o.2.2)) =
      (obl.map (fun o => (3 - wd o.1.1 o.2.1, wd o.1.2 o.2.2))).map
        (fun p : ℕ × ℕ => p.1 * (n + 1 - p.2)) := by
    rw [List.map_map]
    rfl
  rw [e, obl_w]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

/-- Hardin's polynomial for n ≥ 4. -/
theorem poly_large (p : ℕ) : (a (4 + p) : ℚ) = 6 * ((4 + p : ℕ) : ℚ) ^ 2 + 26 * ((4 + p : ℕ) : ℚ) - 42 := by
  rw [a_expand]
  rw [show 4 + p + 1 - 1 = 4 + p by omega, show 4 + p + 1 - 2 = 3 + p by omega, show 4 + p + 1 - 3 = 2 + p by omega, show 4 + p + 1 - 4 = 1 + p by omega, show 4 + p + 1 - 5 = 0 + p by omega]
  push_cast
  ring

/-- The values a(0..T), from the explicit count. -/
theorem small : a 0 = 0 ∧ a 1 = 14 ∧ a 2 = 44 ∧ a 3 = 94 ∧ a 4 = 158 ∧ a 5 = 238 ∧ a 6 = 330 ∧ a 7 = 434 ∧ a 8 = 550 ∧ a 9 = 678 ∧ a 10 = 818 ∧ a 11 = 970 ∧ a 12 = 1134 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | (rw [a_expand]; decide +kernel) | rw [a_expand]

/-- Barker's recurrence, for n > 6. -/
theorem recurrence (n : ℕ) (hn : 6 < n) : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rcases Nat.lt_or_ge n 7 with h | h
  · omega
  · obtain ⟨p, rfl⟩ : ∃ p, n = 4 + (3 + p) := ⟨n - (4 + 3), by omega⟩
    rw [show 4 + (3 + p) - 1 = 4 + (2 + p) by omega, show 4 + (3 + p) - 2 = 4 + (1 + p) by omega, show 4 + (3 + p) - 3 = 4 + (0 + p) by omega]
    have hq : (a (4 + (3 + p)) : ℚ) = 3 * (a (4 + (2 + p)) : ℚ) - 3 * (a (4 + (1 + p)) : ℚ) + (a (4 + (0 + p)) : ℚ) := by
      rw [poly_large (3 + p), poly_large (2 + p), poly_large (1 + p), poly_large (0 + p)]
      push_cast
      ring
    exact_mod_cast hq

open PowerSeries in
/-- Barker's g.f., with a(0) = 0. -/
theorem gf : mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 = 2 * X * (7 + X + 2 * X ^ 2 - 3 * X ^ 3 + X ^ 4 - 2 * X ^ 5) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have hD : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - A * X ^ 3 := by
    simp only [map_ofNat]; ring
  have hN : (2 * X * (7 + X + 2 * X ^ 2 - 3 * X ^ 3 + X ^ 4 - 2 * X ^ 5) : PowerSeries ℤ) =
      C 14 * X ^ 1 + C 2 * X ^ 2 + C 4 * X ^ 3 - C 6 * X ^ 4 + C 2 * X ^ 5 - C 4 * X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge n 13 with h | h
  · interval_cases n <;>
      simp only [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, coeff_C, pow_zero, Nat.zero_le, Nat.sub_zero, Nat.sub_self, if_true, if_false] <;> norm_num
  · have hq := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show n ≠ 1 by omega, show n - 1 ≠ 0 by omega, show n ≠ 2 by omega, show n - 2 ≠ 0 by omega, show n ≠ 3 by omega, show n - 3 ≠ 0 by omega, show n ≠ 4 by omega, show 4 ≤ n by omega, show n - 4 ≠ 0 by omega, show n ≠ 5 by omega, show 5 ≤ n by omega, show n - 5 ≠ 0 by omega, show n ≠ 6 by omega, show 6 ≤ n by omega, show n - 6 ≠ 0 by omega, coeff_C, if_true, if_false, ite_self]
    linear_combination hq

/-- Controls: the entry's terms a(1..12). -/
theorem controls : a 1 = 14 ∧ a 2 = 44 ∧ a 3 = 94 ∧ a 4 = 158 ∧ a 5 = 238 ∧ a 6 = 330 ∧ a 7 = 434 ∧ a 8 = 550 ∧ a 9 = 678 ∧ a 10 = 818 ∧ a 11 = 970 ∧ a 12 = 1134 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩

/-- The problem as the site states it. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 2 * PowerSeries.X * (7 + PowerSeries.X + 2 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a189807

theorem OMA.solution : type_of% @OMA.S_oeis_a189807.main :=
  OMA.S_oeis_a189807.conjecture
