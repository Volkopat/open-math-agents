import OMAStatements.S_oeis_a190092

namespace OMA.S_oeis_a190092

open Finset




/-! ## Diagonals -/

lemma sq_sum_pos (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) : 0 < a ^ 2 + b ^ 2 := by
  rcases h with h | h
  · have := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 h))
    have := sq_nonneg b
    linarith
  · have := lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 h))
    have := sq_nonneg a
    linarith

/-- A vector orthogonal to two orthogonal nonzero vectors of the plane is zero. -/
lemma vec2 (a1 a2 b1 b2 m1 m2 : ℤ) (hA : a1 ≠ 0 ∨ a2 ≠ 0) (hB : b1 ≠ 0 ∨ b2 ≠ 0)
    (hAB : a1 * b1 + a2 * b2 = 0) (hAM : a1 * m1 + a2 * m2 = 0) (hBM : b1 * m1 + b2 * m2 = 0) :
    m1 = 0 ∧ m2 = 0 := by
  have hdet : (a1 * b2 - a2 * b1) ^ 2 = (a1 ^ 2 + a2 ^ 2) * (b1 ^ 2 + b2 ^ 2) := by
    linear_combination (-(a1 * b1 + a2 * b2)) * hAB
  have hd : a1 * b2 - a2 * b1 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
    rcases hdet with h' | h'
    · linarith [sq_sum_pos a1 a2 hA]
    · linarith [sq_sum_pos b1 b2 hB]
  have hM1 : m1 * (a1 * b2 - a2 * b1) = 0 := by linear_combination b2 * hAM - a2 * hBM
  have hM2 : m2 * (a1 * b2 - a2 * b1) = 0 := by linear_combination a1 * hBM - b1 * hAM
  exact ⟨(mul_eq_zero.1 hM1).resolve_right hd, (mul_eq_zero.1 hM2).resolve_right hd⟩

/-- The diagonals of an equilateral quadrilateral bisect each other at a right angle. -/
lemma dg_int (p1 p2 q1 q2 r1 r2 s1 s2 : ℤ) (hA : p1 - r1 ≠ 0 ∨ p2 - r2 ≠ 0)
    (hB : q1 - s1 ≠ 0 ∨ q2 - s2 ≠ 0)
    (h1 : (p1 - q1) ^ 2 + (p2 - q2) ^ 2 = (q1 - r1) ^ 2 + (q2 - r2) ^ 2)
    (h2 : (q1 - r1) ^ 2 + (q2 - r2) ^ 2 = (r1 - s1) ^ 2 + (r2 - s2) ^ 2)
    (h3 : (r1 - s1) ^ 2 + (r2 - s2) ^ 2 = (s1 - p1) ^ 2 + (s2 - p2) ^ 2) :
    p1 + r1 = q1 + s1 ∧ p2 + r2 = q2 + s2 ∧ (p1 - r1) * (q1 - s1) + (p2 - r2) * (q2 - s2) = 0 := by
  have hAM2 : 2 * ((p1 - r1) * (p1 + r1 - q1 - s1) + (p2 - r2) * (p2 + r2 - q2 - s2)) = 0 := by
    linear_combination h1 - h3
  have hAB2 : 2 * ((p1 - r1) * (q1 - s1) + (p2 - r2) * (q2 - s2)) = 0 := by
    linear_combination -h1 - h3
  have hBM2 : 2 * ((q1 - s1) * (p1 + r1 - q1 - s1) + (q2 - s2) * (p2 + r2 - q2 - s2)) = 0 := by
    linear_combination -h1 - 2 * h2 - h3
  have hAB : (p1 - r1) * (q1 - s1) + (p2 - r2) * (q2 - s2) = 0 := by omega
  obtain ⟨e1, e2⟩ := vec2 (p1 - r1) (p2 - r2) (q1 - s1) (q2 - s2) (p1 + r1 - q1 - s1)
    (p2 + r2 - q2 - s2) hA hB hAB (by omega) (by omega)
  exact ⟨by omega, by omega, hAB⟩

/-- Conversely, two segments that bisect each other at a right angle are the diagonals of an
equilateral quadrilateral. -/
lemma sides_int (p1 p2 q1 q2 r1 r2 s1 s2 : ℤ) (e1 : p1 + r1 = q1 + s1) (e2 : p2 + r2 = q2 + s2)
    (hAB : (p1 - r1) * (q1 - s1) + (p2 - r2) * (q2 - s2) = 0) :
    (p1 - q1) ^ 2 + (p2 - q2) ^ 2 = (q1 - r1) ^ 2 + (q2 - r2) ^ 2 ∧
    (q1 - r1) ^ 2 + (q2 - r2) ^ 2 = (r1 - s1) ^ 2 + (r2 - s2) ^ 2 ∧
    (r1 - s1) ^ 2 + (r2 - s2) ^ 2 = (s1 - p1) ^ 2 + (s2 - p2) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (p1 - r1) * e1 + (p2 - r2) * e2 - hAB
  · linear_combination (-(q1 - s1)) * e1 + (-(q2 - s2)) * e2 + hAB
  · linear_combination (-(p1 - r1)) * e1 + (-(p2 - r2)) * e2 - hAB

/-- The segments pr and qs bisect each other at a right angle (integer coordinates). -/
def Dg {k m : ℕ} (p r q s : Fin k × Fin m) : Prop :=
  (p.1 : ℤ) + r.1 = q.1 + s.1 ∧ (p.2 : ℤ) + r.2 = q.2 + s.2 ∧
    ((p.1 : ℤ) - r.1) * ((q.1 : ℤ) - s.1) + ((p.2 : ℤ) - r.2) * ((q.2 : ℤ) - s.2) = 0

instance {k m : ℕ} (p r q s : Fin k × Fin m) : Decidable (Dg p r q s) := by
  unfold Dg; infer_instance

lemma dg_swap1 {k m : ℕ} {p r q s : Fin k × Fin m} (h : Dg p r q s) : Dg r p q s := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by linarith, by linarith, by linear_combination -h3⟩

lemma dg_swap2 {k m : ℕ} {p r q s : Fin k × Fin m} (h : Dg p r q s) : Dg p r s q := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by linarith, by linarith, by linear_combination -h3⟩

lemma dg_swap3 {k m : ℕ} {p r q s : Fin k × Fin m} (h : Dg p r q s) : Dg q s p r := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by linarith, by linarith, by linear_combination h3⟩

lemma ne_int {k m : ℕ} {p r : Fin k × Fin m} (h : p ≠ r) :
    (p.1 : ℤ) - r.1 ≠ 0 ∨ (p.2 : ℤ) - r.2 ≠ 0 := by
  by_cases h1 : (p.1 : ℤ) - r.1 = 0
  · right
    intro h2
    exact h (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  · exact Or.inl h1

/-! ## Rhombuses as canonical tuples -/

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

/-- A rhombus as a tuple: its diagonals pr and qs, p the first of the four points in row-major
order, and q before s. -/
def CanR {k m : ℕ}
    (t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m)) : Prop :=
  Dg t.1 t.2.1 t.2.2.1 t.2.2.2 ∧ ix t.1 < ix t.2.1 ∧ ix t.1 < ix t.2.2.1 ∧ ix t.2.2.1 < ix t.2.2.2

instance {k m : ℕ} : DecidablePred (CanR (k := k) (m := m)) := fun t => by
  unfold CanR; infer_instance

lemma canR_ne {k m : ℕ} {p r q s : Fin k × Fin m} (h : CanR (p, r, q, s)) :
    p ≠ r ∧ p ≠ q ∧ p ≠ s ∧ r ≠ q ∧ r ≠ s ∧ q ≠ s := by
  obtain ⟨⟨d1, d2, -⟩, h1, h2, h3⟩ := h
  dsimp only at d1 d2 h1 h2 h3
  have nr : p ≠ r := fun e => by rw [e] at h1; omega
  have nq : p ≠ q := fun e => by rw [e] at h2; omega
  have ns : p ≠ s := fun e => by rw [e] at h2; omega
  have nqs : q ≠ s := fun e => by rw [e] at h3; omega
  refine ⟨nr, nq, ns, fun e => ns ?_, fun e => nq ?_, nqs⟩
  · rw [e] at d1 d2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · rw [e] at d1 d2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

lemma sum_four {k m : ℕ} (f : Fin k × Fin m → ℤ) {a b c d : Fin k × Fin m} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∑ x ∈ ({a, b, c, d} : Finset (Fin k × Fin m)), f x = f a + f b + f c + f d := by
  rw [Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_pair hcd]
  ring

/-- A tuple of a rhombus whose diagonals are p r and q s with p before r and q before s. -/
lemma can_of {k m : ℕ} (p r q s : Fin k × Fin m) (hD : Dg p r q s) (h1 : ix p < ix r)
    (h2 : ix q < ix s) (hne : ix p ≠ ix q) :
    ∃ t ∈ univ.filter (CanR (k := k) (m := m)),
      ({t.1, t.2.1, t.2.2.1, t.2.2.2} : Finset (Fin k × Fin m)) = {p, r, q, s} := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨(p, r, q, s), by simp [CanR, hD, h1, h2, h], rfl⟩
  · refine ⟨(q, s, p, r), by simp [CanR, dg_swap3 hD, h1, h2, h], ?_⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

lemma card_rh (k m : ℕ) :
    Nat.card {T : Finset (Fin k × Fin m) // IsRhombus T} =
      (univ.filter (CanR (k := k) (m := m))).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  symm
  apply Finset.card_bij (fun t _ => ({t.1, t.2.1, t.2.2.1, t.2.2.2} : Finset (Fin k × Fin m)))
  · rintro ⟨p, r, q, s⟩ ht
    rw [Finset.mem_filter] at ht
    obtain ⟨-, hc⟩ := ht
    obtain ⟨nr, nq, ns, nrq, nrs, nqs⟩ := canR_ne hc
    obtain ⟨⟨d1, d2, d3⟩, -⟩ := hc
    dsimp only at d1 d2 d3
    obtain ⟨s1, s2, s3⟩ := sides_int _ _ _ _ _ _ _ _ d1 d2 d3
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Finset.card_eq_four.2 ⟨p, r, q, s, nr, nq, ns, nrq, nrs, nqs, rfl⟩,
      p, by simp, q, by simp, r, by simp, s, by simp, nq, nr, ns, Ne.symm nrq, nqs, nrs,
      by unfold sqd; exact s1, by unfold sqd; exact s2, by unfold sqd; exact s3⟩
  · rintro ⟨p, r, q, s⟩ ht ⟨p', r', q', s'⟩ ht' h
    rw [Finset.mem_filter] at ht ht'
    obtain ⟨-, hc⟩ := ht
    obtain ⟨-, hc'⟩ := ht'
    obtain ⟨nr, nq, ns, nrq, nrs, nqs⟩ := canR_ne hc
    obtain ⟨nr', nq', ns', nrq', nrs', nqs'⟩ := canR_ne hc'
    obtain ⟨⟨d1, d2, -⟩, h1, h2, h3⟩ := hc
    obtain ⟨⟨d1', d2', -⟩, h1', h2', h3'⟩ := hc'
    dsimp only at d1 d2 h1 h2 h3 d1' d2' h1' h2' h3' h
    have mem : ∀ x, x ∈ ({p', r', q', s'} : Finset (Fin k × Fin m)) → x = p ∨ x = r ∨ x = q ∨ x = s := by
      intro x hx
      rw [← h] at hx
      simpa using hx
    have mem' : ∀ x, x ∈ ({p, r, q, s} : Finset (Fin k × Fin m)) → x = p' ∨ x = r' ∨ x = q' ∨ x = s' := by
      intro x hx
      rw [h] at hx
      simpa using hx
    have hp : p' = p := by
      rcases mem p' (by simp) with e | e | e | e
      · exact e
      · rcases mem' p (by simp) with e' | e' | e' | e' <;> subst e e' <;> omega
      · rcases mem' p (by simp) with e' | e' | e' | e' <;> subst e e' <;> omega
      · rcases mem' p (by simp) with e' | e' | e' | e' <;> subst e e' <;> omega
    subst hp
    have hs1 := sum_four (fun x => ((x.1 : ℕ) : ℤ)) nr nq ns nrq nrs nqs
    have hs2 := sum_four (fun x => ((x.2 : ℕ) : ℤ)) nr nq ns nrq nrs nqs
    have hs1' := sum_four (fun x => ((x.1 : ℕ) : ℤ)) nr' nq' ns' nrq' nrs' nqs'
    have hs2' := sum_four (fun x => ((x.2 : ℕ) : ℤ)) nr' nq' ns' nrq' nrs' nqs'
    rw [h] at hs1 hs2
    rw [hs1'] at hs1
    rw [hs2'] at hs2
    have hr : r' = r := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    subst hr
    have hq := mem q' (by simp)
    have hs := mem s' (by simp)
    rcases hq with e | e | e | e
    · exact absurd e.symm nq'
    · exact absurd e.symm nrq'
    · rcases hs with e' | e' | e' | e'
      · exact absurd e'.symm ns'
      · exact absurd e'.symm nrs'
      · exact absurd (e.trans e'.symm) nqs'
      · rw [e, e']
    · rcases hs with e' | e' | e' | e'
      · exact absurd e'.symm ns'
      · exact absurd e'.symm nrs'
      · subst e e'
        omega
      · exact absurd (e.trans e'.symm) nqs'
  · intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨-, hcard, p, hp, q, hq, r, hr, s, hs, npq, npr, nps, nqr, nqs, nrs, e1, e2, e3⟩ := hT
    unfold sqd at e1 e2 e3
    obtain ⟨d1, d2, d3⟩ := dg_int _ _ _ _ _ _ _ _ (ne_int npr) (ne_int nqs) e1 e2 e3
    have hD : Dg p r q s := ⟨d1, d2, d3⟩
    have hsub : ({p, r, q, s} : Finset (Fin k × Fin m)) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hT4 : ({p, r, q, s} : Finset (Fin k × Fin m)) = T :=
      Finset.eq_of_subset_of_card_le hsub
        (by rw [hcard, Finset.card_eq_four.2 ⟨p, r, q, s, npr, npq, nps, Ne.symm nqr, nrs, nqs, rfl⟩])
    have ix_ne : ∀ a b : Fin k × Fin m, a ≠ b → ix a ≠ ix b := fun a b h e => h (ix_inj e)
    have key : ∀ a b c d : Fin k × Fin m, Dg a b c d → ix a < ix b → ix c < ix d →
        ({a, b, c, d} : Finset (Fin k × Fin m)) = T → a ≠ c →
        ∃ t, ∃ (_ : t ∈ univ.filter (CanR (k := k) (m := m))),
          ({t.1, t.2.1, t.2.2.1, t.2.2.2} : Finset (Fin k × Fin m)) = T := by
      intro a b c d hd hab hcd he hac
      obtain ⟨t, ht, ht'⟩ := can_of a b c d hd hab hcd (ix_ne a c hac)
      exact ⟨t, ht, ht'.trans he⟩
    rcases Nat.lt_or_gt_of_ne (ix_ne p r npr) with h1 | h1 <;>
      rcases Nat.lt_or_gt_of_ne (ix_ne q s nqs) with h2 | h2
    · exact key p r q s hD h1 h2 hT4 npq
    · exact key p r s q (dg_swap2 hD) h1 h2 (by rw [← hT4]; ext x; simp; tauto) nps
    · exact key r p q s (dg_swap1 hD) h1 h2 (by rw [← hT4]; ext x; simp; tauto) (Ne.symm nqr)
    · exact key r p s q (dg_swap2 (dg_swap1 hD)) h1 h2 (by rw [← hT4]; ext x; simp; tauto)
        (by intro e; exact nrs e)

/-! ## Rhombuses with a vertical diagonal -/

/-- Pairs of positions on a line of length N, the first smaller, with an even sum. -/
def EvP (N : ℕ) : Finset (Fin N × Fin N) :=
  univ.filter (fun z => z.1 < z.2 ∧ ((z.1 : ℕ) + z.2) % 2 = 0)

lemma axis_facts {k m : ℕ} {p r q s : Fin k × Fin m} (hc : CanR (p, r, q, s))
    (hpr : (r.1 : ℕ) = p.1) :
    (q.2 : ℕ) = s.2 ∧ 2 * (p.1 : ℕ) = q.1 + s.1 ∧ 2 * (q.2 : ℕ) = p.2 + r.2 ∧ (p.2 : ℕ) < r.2 ∧
      (q.1 : ℕ) < s.1 := by
  obtain ⟨nr, -, -, -, -, -⟩ := canR_ne hc
  obtain ⟨⟨d1, d2, d3⟩, h1, h2, h3⟩ := hc
  dsimp only at d1 d2 d3 h1 h2 h3
  unfold ix at h1 h3
  have hpr' : ((r.1 : ℕ) : ℤ) = p.1 := by exact_mod_cast hpr
  rw [hpr', sub_self, zero_mul, zero_add] at d3
  have hy : (p.2 : ℤ) - r.2 ≠ 0 := fun h => nr (Prod.ext (Fin.ext hpr.symm) (Fin.ext (by omega)))
  have hq : (q.2 : ℤ) - s.2 = 0 := (mul_eq_zero.1 d3).resolve_left hy
  have hq' : (q.2 : ℕ) = s.2 := by omega
  refine ⟨hq', by omega, by omega, ?_, ?_⟩
  · rw [hpr] at h1
    by_contra hc
    have := Nat.mul_le_mul_right k (not_lt.1 hc)
    omega
  · rw [hq'] at h3
    omega

lemma card_axisR (k m : ℕ) :
    (univ.filter (fun t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) =>
      CanR t ∧ (t.2.1.1 : ℕ) = t.1.1)).card = (EvP k).card * (EvP m).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun t _ => ((t.2.2.1.1, t.2.2.2.1), (t.1.2, t.2.1.2)))
  · rintro ⟨p, r, q, s⟩ ht
    rw [Finset.mem_filter] at ht
    obtain ⟨-, hc, hpr⟩ := ht
    obtain ⟨e1, e2, e3, e4, e5⟩ := axis_facts hc hpr
    simp only [EvP, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.lt_def]
    exact ⟨⟨e5, by omega⟩, e4, by omega⟩
  · rintro ⟨p, r, q, s⟩ ht ⟨p', r', q', s'⟩ ht' h
    simp only [Prod.mk.injEq, Fin.ext_iff] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    rw [Finset.mem_filter] at ht ht'
    obtain ⟨-, hc, hpr⟩ := ht
    obtain ⟨-, hc', hpr'⟩ := ht'
    obtain ⟨e1, e2, e3, -, -⟩ := axis_facts hc hpr
    obtain ⟨e1', e2', e3', -, -⟩ := axis_facts hc' hpr'
    dsimp only at hpr hpr'
    simp only [Prod.mk.injEq]
    refine ⟨Prod.ext (Fin.ext (by omega)) (Fin.ext h3), Prod.ext (Fin.ext (by omega)) (Fin.ext h4),
      Prod.ext (Fin.ext h1) (Fin.ext (by omega)), Prod.ext (Fin.ext h2) (Fin.ext (by omega))⟩
  · rintro ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ hz
    simp only [EvP, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.lt_def] at hz
    obtain ⟨⟨hx, ex⟩, hy, ey⟩ := hz
    have hx2 := x2.2
    have hy2 := y2.2
    refine ⟨((⟨((x1 : ℕ) + x2) / 2, by omega⟩, y1), (⟨((x1 : ℕ) + x2) / 2, by omega⟩, y2),
      (x1, ⟨((y1 : ℕ) + y2) / 2, by omega⟩), (x2, ⟨((y1 : ℕ) + y2) / 2, by omega⟩)), ?_, rfl⟩
    rw [Finset.mem_filter]
    have h1 : (y1 : ℕ) + 1 ≤ y2 := hy
    have h2 : (y1 : ℕ) + 1 ≤ ((y1 : ℕ) + y2) / 2 := by omega
    have m1 := Nat.mul_le_mul_right k h1
    have m2 := Nat.mul_le_mul_right k h2
    rw [add_mul, one_mul] at m1 m2
    refine ⟨Finset.mem_univ _, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, rfl⟩ <;>
      simp only [ix, Fin.val_mk, sub_self, mul_zero, zero_mul, add_zero] <;> omega

/-- hs m = (EvP m).card, the sum of i / 2 for i < m. -/
def hs (m : ℕ) : ℕ := ∑ i ∈ range m, i / 2

lemma hs_succ (m : ℕ) : hs (m + 1) = hs m + m / 2 := Finset.sum_range_succ _ _

lemma hs_odd (j : ℕ) : hs (2 * j + 1) = j * j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, hs_succ, hs_succ, ih,
      show (2 * j + 1) / 2 = j by omega, show (2 * j + 1 + 1) / 2 = j + 1 by omega]
    ring

lemma hs_even (j : ℕ) : hs (2 * j + 1 + 1) = j * j + j := by
  rw [hs_succ, hs_odd, show (2 * j + 1) / 2 = j by omega]

lemma card_evp (N : ℕ) : (EvP N).card = hs N := by
  unfold hs
  rw [Finset.card_eq_sum_card_fiberwise (f := fun z : Fin N × Fin N => z.2) (t := univ)
    (fun _ _ => Finset.mem_univ _), ← Fin.sum_univ_eq_sum_range (fun i => i / 2) N]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.card_range ((y : ℕ) / 2)]
  apply Finset.card_bij (fun z _ => (z.1 : ℕ) / 2)
  · rintro ⟨z1, z2⟩ hz
    rw [Finset.mem_filter, EvP, Finset.mem_filter] at hz
    obtain ⟨⟨-, h1, h2⟩, h3⟩ := hz
    change z1 < z2 at h1
    change ((z1 : ℕ) + z2) % 2 = 0 at h2
    change z2 = y at h3
    rw [Fin.lt_def] at h1
    have h3' : (z2 : ℕ) = y := by rw [h3]
    rw [Finset.mem_range]
    change (z1 : ℕ) / 2 < (y : ℕ) / 2
    omega
  · rintro ⟨z1, z2⟩ hz ⟨z1', z2'⟩ hz' h
    rw [Finset.mem_filter, EvP, Finset.mem_filter] at hz hz'
    obtain ⟨⟨-, h1, h2⟩, h3⟩ := hz
    obtain ⟨⟨-, h1', h2'⟩, h3'⟩ := hz'
    change z1 < z2 at h1
    change ((z1 : ℕ) + z2) % 2 = 0 at h2
    change z2 = y at h3
    change z1' < z2' at h1'
    change ((z1' : ℕ) + z2') % 2 = 0 at h2'
    change z2' = y at h3'
    change (z1 : ℕ) / 2 = (z1' : ℕ) / 2 at h
    rw [Fin.lt_def] at h1 h1'
    have e : z2 = z2' := h3.trans h3'.symm
    subst e
    exact Prod.ext (Fin.ext (show (z1 : ℕ) = z1' by omega)) rfl
  · intro t ht
    rw [Finset.mem_range] at ht
    have hy := y.2
    refine ⟨(⟨2 * t + (y : ℕ) % 2, by omega⟩, y), ?_, ?_⟩
    · rw [Finset.mem_filter, EvP, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, rfl⟩
      · rw [Fin.lt_def]
        show 2 * t + (y : ℕ) % 2 < y
        omega
      · show (2 * t + (y : ℕ) % 2 + y) % 2 = 0
        omega
    · show (2 * t + (y : ℕ) % 2) / 2 = t
      omega

/-! ## Rhombuses with no vertical diagonal -/

/-- The offsets of r and q from p in a tuple (p, r, q, s). -/
def offR {k m : ℕ}
    (t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m)) :
    (ℤ × ℤ) × (ℤ × ℤ) :=
  (((t.2.1.1 : ℤ) - t.1.1, (t.2.1.2 : ℤ) - t.1.2),
    ((t.2.2.1.1 : ℤ) - t.1.1, (t.2.2.1.2 : ℤ) - t.1.2))

/-- Offsets (E, u) of a tuple with no vertical diagonal, r = p + E, q = p + u, s = p + E - u,
with r - q and s - q of horizontal size below k. -/
def OblR (k : ℕ) (o : (ℤ × ℤ) × (ℤ × ℤ)) : Prop :=
  o.1.1 ≠ 0 ∧ o.1.1 * (o.1.1 - 2 * o.2.1) + o.1.2 * (o.1.2 - 2 * o.2.2) = 0 ∧
    0 < o.2.2 * k + o.2.1 ∧ 0 < (o.1.2 - 2 * o.2.2) * k + (o.1.1 - 2 * o.2.1) ∧
    0 ≤ o.2.2 ∧ 2 * o.2.2 < o.1.2 ∧
    -((k : ℤ) - 1) ≤ o.1.1 - o.2.1 ∧ o.1.1 - o.2.1 ≤ (k : ℤ) - 1 ∧
    -((k : ℤ) - 1) ≤ o.1.1 - 2 * o.2.1 ∧ o.1.1 - 2 * o.2.1 ≤ (k : ℤ) - 1

instance (k : ℕ) : DecidablePred (OblR k) := fun o => by unfold OblR; infer_instance

/-- All offset pairs of tuples with no vertical diagonal, for vertical offsets up to Q. -/
noncomputable def ObR (k Q : ℕ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  ((Icc (-((k : ℤ) - 1)) ((k : ℤ) - 1) ×ˢ Icc 1 (Q : ℤ)) ×ˢ
    (Icc (-((k : ℤ) - 1)) ((k : ℤ) - 1) ×ˢ Icc 0 ((Q : ℤ) / 2))).filter (OblR k)

/-- The positions x of a line of length N with x + a, x + b and x + c on the line. -/
def line4 (N : ℕ) (a b c : ℤ) : Finset (Fin N) :=
  univ.filter (fun x => 0 ≤ (x : ℤ) + a ∧ (x : ℤ) + a < N ∧ 0 ≤ (x : ℤ) + b ∧
    (x : ℤ) + b < N ∧ 0 ≤ (x : ℤ) + c ∧ (x : ℤ) + c < N)

lemma card_lineY (m e : ℕ) : (univ.filter (fun y : Fin m => (y : ℕ) + e < m)).card = m - e := by
  rw [← Finset.card_range (m - e)]
  apply Finset.card_bij (fun (y : Fin m) _ => (y : ℕ))
  · intro y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_range]
    omega
  · intro y _ y' _ h
    exact Fin.ext h
  · intro t ht
    rw [Finset.mem_range] at ht
    refine ⟨⟨t, by omega⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, show t + e < m by omega⟩

/-- An offset b * k + a in index order with |a| < k has b ≥ 0. -/
lemma dpos {k a b : ℤ} (ha : -(k - 1) ≤ a ∧ a ≤ k - 1) (h : 0 < b * k + a) : 0 ≤ b := by
  by_contra hb
  have hk : 1 ≤ k := by linarith [ha.1, ha.2]
  have : b * k ≤ -k := by nlinarith
  linarith [ha.2]

/-- Perpendicular offsets with horizontal parts of size below k and positive vertical parts
have vertical parts at most (k - 1)^2. -/
lemma bound_r (k : ℤ) {a1 b1 a2 b2 : ℤ} (h1 : |a1| ≤ k - 1) (h2 : |a2| ≤ k - 1)
    (hb1 : 1 ≤ b1) (hb2 : 1 ≤ b2) (h : a1 * a2 + b1 * b2 = 0) :
    b1 ≤ (k - 1) ^ 2 ∧ b2 ≤ (k - 1) ^ 2 := by
  have e : b1 * b2 = |a1| * |a2| := by
    rw [← abs_mul, show b1 * b2 = -(a1 * a2) by linarith, abs_of_nonpos (by nlinarith)]
  have p1 := abs_nonneg a1
  have p2 := abs_nonneg a2
  have hk : |a1| * |a2| ≤ (k - 1) ^ 2 := by nlinarith
  constructor <;> nlinarith

lemma off_memR (k m : ℕ)
    (t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m))
    (ht : CanR t ∧ ¬ ((t.2.1.1 : ℕ) = t.1.1)) : offR t ∈ ObR k ((k - 1) ^ 2) := by
  obtain ⟨p, r, q, s⟩ := t
  obtain ⟨⟨⟨d1, d2, d3⟩, -, h2, h3⟩, hpr⟩ := ht
  dsimp only at d1 d2 d3 h2 h3 hpr
  unfold ix at h2 h3
  have hp1 := p.1.2
  have hq1 := q.1.2
  have hr1 := r.1.2
  have hs1 := s.1.2
  have hk : 1 ≤ k := by omega
  have hS1 : (s.1 : ℤ) = p.1 + r.1 - q.1 := by linarith
  have hS2 : (s.2 : ℤ) = p.2 + r.2 - q.2 := by linarith
  have h2' : ((p.2 : ℕ) * k + p.1 : ℤ) < (q.2 : ℕ) * k + q.1 := by exact_mod_cast h2
  have h3' : ((q.2 : ℕ) * k + q.1 : ℤ) < (s.2 : ℕ) * k + s.1 := by exact_mod_cast h3
  have hu : 0 < ((q.2 : ℤ) - p.2) * k + ((q.1 : ℤ) - p.1) := by
    have e : ((q.2 : ℤ) - p.2) * k + ((q.1 : ℤ) - p.1) =
        ((q.2 : ℕ) * k + q.1 : ℤ) - ((p.2 : ℕ) * k + p.1 : ℤ) := by ring
    rw [e]
    linarith
  have hF : 0 < ((s.2 : ℤ) - q.2) * k + ((s.1 : ℤ) - q.1) := by
    have e : ((s.2 : ℤ) - q.2) * k + ((s.1 : ℤ) - q.1) =
        ((s.2 : ℕ) * k + s.1 : ℤ) - ((q.2 : ℕ) * k + q.1 : ℤ) := by ring
    rw [e]
    linarith
  have hperp : ((r.1 : ℤ) - p.1) * ((s.1 : ℤ) - q.1) + ((r.2 : ℤ) - p.2) * ((s.2 : ℤ) - q.2) = 0 := by
    rw [hS1, hS2]
    linear_combination d3 - ((p.1 : ℤ) - r.1) * d1 - ((p.2 : ℤ) - r.2) * d2 + 0 * hS1
  have hu0 : 0 ≤ (q.2 : ℤ) - p.2 := dpos ⟨by omega, by omega⟩ hu
  have hF0 : 0 ≤ (s.2 : ℤ) - q.2 := dpos ⟨by omega, by omega⟩ hF
  have hEx : (r.1 : ℤ) - p.1 ≠ 0 := by omega
  have hF1 : 1 ≤ (s.2 : ℤ) - q.2 := by
    by_contra hc
    have e0 : (s.2 : ℤ) - q.2 = 0 := by omega
    rw [e0, mul_zero, add_zero] at hperp
    rw [e0, zero_mul, zero_add] at hF
    have := (mul_eq_zero.1 hperp).resolve_left hEx
    omega
  have hQ : (((k - 1) ^ 2 : ℕ) : ℤ) = ((k : ℤ) - 1) ^ 2 := by push_cast [Nat.cast_sub hk]; ring
  obtain ⟨b1, b2⟩ := bound_r (k : ℤ) (a1 := (r.1 : ℤ) - p.1) (a2 := (s.1 : ℤ) - q.1)
    (b1 := (r.2 : ℤ) - p.2) (b2 := (s.2 : ℤ) - q.2) (by rw [abs_le]; constructor <;> omega)
    (by rw [abs_le]; constructor <;> omega) (by omega) hF1 hperp
  simp only [ObR, offR, OblR, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  rw [hQ]
  refine ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, b1⟩⟩, ⟨⟨by omega, by omega⟩, ⟨hu0, by omega⟩⟩⟩,
    hEx, ?_, hu, ?_, hu0, by omega, by omega, by omega, by omega, by omega⟩
  · have e1 : (r.1 : ℤ) - p.1 - 2 * ((q.1 : ℤ) - p.1) = (s.1 : ℤ) - q.1 := by omega
    have e2 : (r.2 : ℤ) - p.2 - 2 * ((q.2 : ℤ) - p.2) = (s.2 : ℤ) - q.2 := by omega
    rw [e1, e2]
    exact hperp
  · have e1 : (r.1 : ℤ) - p.1 - 2 * ((q.1 : ℤ) - p.1) = (s.1 : ℤ) - q.1 := by omega
    have e2 : (r.2 : ℤ) - p.2 - 2 * ((q.2 : ℤ) - p.2) = (s.2 : ℤ) - q.2 := by omega
    rw [e1, e2]
    exact hF

lemma card_fiberR (k m : ℕ) (o : (ℤ × ℤ) × (ℤ × ℤ)) (ho : o ∈ ObR k ((k - 1) ^ 2)) :
    (univ.filter
      (fun t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) =>
        (CanR t ∧ ¬ ((t.2.1.1 : ℕ) = t.1.1)) ∧ offR t = o)).card =
      (line4 k o.1.1 o.2.1 (o.1.1 - o.2.1)).card * (m - o.1.2.toNat) := by
  obtain ⟨⟨ex, ey⟩, ⟨ux, uy⟩⟩ := o
  simp only [ObR, OblR, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ho
  obtain ⟨⟨⟨⟨bx1, bx2⟩, ⟨by1, by2⟩⟩, ⟨⟨bu1, bu2⟩, ⟨bv1, bv2⟩⟩⟩, n1, hperp, hu, hF, hu0, hu2,
    -, -, -, -⟩ := ho
  dsimp only
  rw [← card_lineY m ey.toNat, ← Finset.card_product]
  apply Finset.card_bij (fun t _ => (t.1.1, t.1.2))
  · rintro ⟨p, r, q, s⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, offR, Prod.mk.injEq] at ht
    obtain ⟨⟨⟨⟨d1, d2, -⟩, -⟩, -⟩, ⟨e1, e2⟩, e3, e4⟩ := ht
    try dsimp only at d1 d2
    have := q.1.2
    have := q.2.2
    have := r.1.2
    have := r.2.2
    have := s.1.2
    have := s.2.2
    simp only [Finset.mem_product, line4, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, by omega⟩
  · rintro ⟨p, r, q, s⟩ ht ⟨p', r', q', s'⟩ ht' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, offR, Prod.mk.injEq] at ht ht' h
    obtain ⟨⟨⟨⟨d1, d2, -⟩, -⟩, -⟩, ⟨e1, e2⟩, e3, e4⟩ := ht
    obtain ⟨⟨⟨⟨d1', d2', -⟩, -⟩, -⟩, ⟨e1', e2'⟩, e3', e4'⟩ := ht'
    try dsimp only at d1 d2 d1' d2'
    obtain ⟨h1, h2⟩ := h
    have hp : p = p' := Prod.ext h1 h2
    subst hp
    have hr : r = r' := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    have hq : q = q' := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    have hs : s = s' := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    rw [hr, hq, hs]
  · rintro ⟨x, y⟩ hxy
    simp only [Finset.mem_product, line4, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, b1⟩ := hxy
    obtain ⟨rx, hr1⟩ : ∃ z : Fin k, ((z : ℕ) : ℤ) = x + ex :=
      ⟨⟨((x : ℤ) + ex).toNat, by omega⟩, by simp only; omega⟩
    obtain ⟨ry, hr2⟩ : ∃ z : Fin m, ((z : ℕ) : ℤ) = y + ey :=
      ⟨⟨((y : ℤ) + ey).toNat, by omega⟩, by simp only; omega⟩
    obtain ⟨qx, hq1⟩ : ∃ z : Fin k, ((z : ℕ) : ℤ) = x + ux :=
      ⟨⟨((x : ℤ) + ux).toNat, by omega⟩, by simp only; omega⟩
    obtain ⟨qy, hq2⟩ : ∃ z : Fin m, ((z : ℕ) : ℤ) = y + uy :=
      ⟨⟨((y : ℤ) + uy).toNat, by omega⟩, by simp only; omega⟩
    obtain ⟨sx, hs1⟩ : ∃ z : Fin k, ((z : ℕ) : ℤ) = x + (ex - ux) :=
      ⟨⟨((x : ℤ) + (ex - ux)).toNat, by omega⟩, by simp only; omega⟩
    obtain ⟨sy, hs2⟩ : ∃ z : Fin m, ((z : ℕ) : ℤ) = y + (ey - uy) :=
      ⟨⟨((y : ℤ) + (ey - uy)).toNat, by omega⟩, by simp only; omega⟩
    refine ⟨((x, y), (rx, ry), (qx, qy), (sx, sy)), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · show ((x : ℕ) : ℤ) + (rx : ℕ) = (qx : ℕ) + (sx : ℕ)
      rw [hr1, hq1, hs1]
      ring
    · show ((y : ℕ) : ℤ) + (ry : ℕ) = (qy : ℕ) + (sy : ℕ)
      rw [hr2, hq2, hs2]
      ring
    · show (((x : ℕ) : ℤ) - (rx : ℕ)) * (((qx : ℕ) : ℤ) - (sx : ℕ)) +
          (((y : ℕ) : ℤ) - (ry : ℕ)) * (((qy : ℕ) : ℤ) - (sy : ℕ)) = 0
      rw [hr1, hq1, hs1, hr2, hq2, hs2]
      linear_combination hperp
    · show (y : ℕ) * k + x < (ry : ℕ) * k + rx
      have : (((y : ℕ) * k + x : ℕ) : ℤ) < (((ry : ℕ) * k + rx : ℕ) : ℤ) := by
        push_cast
        rw [hr1, hr2]
        nlinarith
      exact_mod_cast this
    · show (y : ℕ) * k + x < (qy : ℕ) * k + qx
      have : (((y : ℕ) * k + x : ℕ) : ℤ) < (((qy : ℕ) * k + qx : ℕ) : ℤ) := by
        push_cast
        rw [hq1, hq2]
        nlinarith
      exact_mod_cast this
    · show (qy : ℕ) * k + qx < (sy : ℕ) * k + sx
      have : (((qy : ℕ) * k + qx : ℕ) : ℤ) < (((sy : ℕ) * k + sx : ℕ) : ℤ) := by
        push_cast
        rw [hq1, hq2, hs1, hs2]
        nlinarith
      exact_mod_cast this
    · show ¬ ((rx : ℕ) = x)
      omega
    · show ((((rx : ℕ) : ℤ) - (x : ℕ), ((ry : ℕ) : ℤ) - (y : ℕ)),
          (((qx : ℕ) : ℤ) - (x : ℕ), ((qy : ℕ) : ℤ) - (y : ℕ))) = ((ex, ey), (ux, uy))
      rw [hr1, hr2, hq1, hq2]
      simp

lemma card_oblR (k m : ℕ) :
    (univ.filter
      (fun t : (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) × (Fin k × Fin m) =>
        CanR t ∧ ¬ ((t.2.1.1 : ℕ) = t.1.1))).card =
      ∑ o ∈ ObR k ((k - 1) ^ 2), (line4 k o.1.1 o.2.1 (o.1.1 - o.2.1)).card * (m - o.1.2.toNat) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := offR) (t := ObR k ((k - 1) ^ 2))
    (fun t ht => off_memR k m t (Finset.mem_filter.1 ht).2)]
  apply Finset.sum_congr rfl
  intro o ho
  rw [Finset.filter_filter]
  exact card_fiberR k m o ho

/-- Rhombuses on the grid of k columns and m rows. -/
theorem card_rhombi (k m : ℕ) :
    Nat.card {T : Finset (Fin k × Fin m) // IsRhombus T} = (EvP k).card * hs m +
      ∑ o ∈ ObR k ((k - 1) ^ 2), (line4 k o.1.1 o.2.1 (o.1.1 - o.2.1)).card * (m - o.1.2.toNat) := by
  rw [card_rh, ← Finset.card_filter_add_card_filter_not (fun t => (t.2.1.1 : ℕ) = t.1.1),
    Finset.filter_filter, Finset.filter_filter, card_axisR, card_oblR, card_evp m]

/-- The offset pairs of the tuples with no vertical diagonal, as the kernel lists them. -/
def obl : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((-3, 3), (-2, 1)),
   ((-3, 9), (-3, 4)),
   ((-1, 3), (-2, 1)),
   ((1, 1), (1, 0)),
   ((1, 3), (2, 1)),
   ((2, 2), (2, 0)),
   ((3, 3), (2, 1)),
   ((3, 3), (3, 0)),
   ((3, 9), (3, 4))]

lemma ob_eq : ObR 4 ((4 - 1) ^ 2) = obl.toFinset := by
  decide +kernel

lemma obl_nodup : obl.Nodup := by
  decide +kernel

lemma obl_w : obl.map (fun o => ((line4 4 o.1.1 o.2.1 (o.1.1 - o.2.1)).card, o.1.2.toNat)) =
    [(1, 3), (1, 9), (1, 3), (3, 1), (1, 3), (2, 2), (1, 3), (1, 3), (1, 9)] := by
  decide +kernel

lemma evp_k : (EvP 4).card = 2 := by
  decide +kernel

/-- a(n) from the rhombuses with a vertical diagonal and the others. -/
theorem a_expand (n : ℕ) : a n = 2 * hs (n + 1) + (1 * (n + 1 - 3) + (1 * (n + 1 - 9) + (1 * (n + 1 - 3) + (3 * (n + 1 - 1) + (1 * (n + 1 - 3) + (2 * (n + 1 - 2) + (1 * (n + 1 - 3) + (1 * (n + 1 - 3) + (1 * (n + 1 - 9) + 0))))))))) := by
  unfold a
  rw [card_rhombi, evp_k, ob_eq, List.sum_toFinset _ obl_nodup]
  have e : obl.map (fun o => (line4 4 o.1.1 o.2.1 (o.1.1 - o.2.1)).card * (n + 1 - o.1.2.toNat)) =
      (obl.map (fun o => ((line4 4 o.1.1 o.2.1 (o.1.1 - o.2.1)).card, o.1.2.toNat))).map
        (fun p : ℕ × ℕ => p.1 * (n + 1 - p.2)) := by
    rw [List.map_map]
    rfl
  rw [e, obl_w]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

/-- Barker's closed form for even n > 7. -/
theorem even_form : (∀ n : ℕ, 7 < n → Even n → (a n : ℚ) = ((n : ℚ) ^ 2 + 24 * (n : ℚ) - 56) / 2) := by
  intro n hn he
  obtain ⟨j, rfl⟩ := he
  obtain ⟨p, rfl⟩ : ∃ p, j = 4 + p := ⟨j - 4, by omega⟩
  rw [show 4 + p + (4 + p) = 2 * (4 + p) by ring, a_expand, hs_odd]
  rw [show 2 * (4 + p) + 1 - 1 = 8 + 2 * p by omega, show 2 * (4 + p) + 1 - 2 = 7 + 2 * p by omega, show 2 * (4 + p) + 1 - 3 = 6 + 2 * p by omega, show 2 * (4 + p) + 1 - 9 = 0 + 2 * p by omega]
  push_cast
  ring

/-- Barker's closed form for odd n > 7. -/
theorem odd_form : (∀ n : ℕ, 7 < n → Odd n → (a n : ℚ) = ((n : ℚ) ^ 2 + 24 * (n : ℚ) - 57) / 2) := by
  intro n hn he
  obtain ⟨j, rfl⟩ := he
  obtain ⟨p, rfl⟩ : ∃ p, j = 4 + p := ⟨j - 4, by omega⟩
  rw [a_expand, hs_even]
  rw [show 2 * (4 + p) + 1 + 1 - 1 = 9 + 2 * p by omega, show 2 * (4 + p) + 1 + 1 - 2 = 8 + 2 * p by omega, show 2 * (4 + p) + 1 + 1 - 3 = 7 + 2 * p by omega, show 2 * (4 + p) + 1 + 1 - 9 = 1 + 2 * p by omega]
  push_cast
  ring

/-- The values a(0..T), from the explicit count. -/
theorem small : a 0 = 0 ∧ a 1 = 3 ∧ a 2 = 10 ∧ a 3 = 22 ∧ a 4 = 36 ∧ a 5 = 50 ∧ a 6 = 66 ∧ a 7 = 82 ∧ a 8 = 100 ∧ a 9 = 120 ∧ a 10 = 142 ∧ a 11 = 164 ∧ a 12 = 188 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | (rw [a_expand]; decide +kernel) | rw [a_expand]

/-- a(n) = 2 a(n-1) - 2 a(n-3) + a(n-4) for n ≥ 12. -/
theorem rec4 (n : ℕ) (hn : 12 ≤ n) : (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = 12 + p := ⟨n - 12, by omega⟩
  rw [show 12 + p - 1 = 11 + p by omega, show 12 + p - 3 = 9 + p by omega,
    show 12 + p - 4 = 8 + p by omega, a_expand, a_expand, a_expand, a_expand]
  have f1 : hs (9 + p + 1) = hs (8 + p + 1) + (8 + p + 1) / 2 := by
    rw [show 9 + p + 1 = 8 + p + 1 + 1 by ring]
    exact hs_succ _
  have f2 : hs (10 + p + 1) = hs (9 + p + 1) + (9 + p + 1) / 2 := by
    rw [show 10 + p + 1 = 9 + p + 1 + 1 by ring]
    exact hs_succ _
  have f3 : hs (11 + p + 1) = hs (10 + p + 1) + (10 + p + 1) / 2 := by
    rw [show 11 + p + 1 = 10 + p + 1 + 1 by ring]
    exact hs_succ _
  have f4 : hs (12 + p + 1) = hs (11 + p + 1) + (11 + p + 1) / 2 := by
    rw [show 12 + p + 1 = 11 + p + 1 + 1 by ring]
    exact hs_succ _
  omega

open PowerSeries in
/-- Barker's g.f., with a(0) = 0. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X)) = X * (3 + 4 * X + 2 * X ^ 2 - 2 * X ^ 3 - 5 * X ^ 4 + 2 * X ^ 8 - 2 * X ^ 10) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have hD : A * ((1 - X) ^ 3 * (1 + X)) = A - C 2 * (A * X ^ 1) + C 2 * (A * X ^ 3) - A * X ^ 4 := by
    simp only [map_ofNat]; ring
  have hN : (X * (3 + 4 * X + 2 * X ^ 2 - 2 * X ^ 3 - 5 * X ^ 4 + 2 * X ^ 8 - 2 * X ^ 10) : PowerSeries ℤ) =
      C 3 * X ^ 1 + C 4 * X ^ 2 + C 2 * X ^ 3 - C 2 * X ^ 4 - C 5 * X ^ 5 + C 2 * X ^ 9 - C 2 * X ^ 11 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge n 13 with h | h
  · interval_cases n <;>
      simp only [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, coeff_C, pow_zero, Nat.zero_le, Nat.sub_zero, Nat.sub_self, if_true, if_false] <;> norm_num
  · have hq := rec4 n (by omega)
    simp only [show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show n ≠ 1 by omega, show n - 1 ≠ 0 by omega, show n ≠ 2 by omega, show 2 ≤ n by omega, show n - 2 ≠ 0 by omega, show n ≠ 3 by omega, show n - 3 ≠ 0 by omega, show n ≠ 4 by omega, show n - 4 ≠ 0 by omega, show n ≠ 5 by omega, show 5 ≤ n by omega, show n - 5 ≠ 0 by omega, show n ≠ 9 by omega, show 9 ≤ n by omega, show n - 9 ≠ 0 by omega, show n ≠ 11 by omega, show 11 ≤ n by omega, show n - 11 ≠ 0 by omega, coeff_C, if_true, if_false, ite_self]
    linear_combination hq

/-- Controls: the entry's terms a(1..12). -/
theorem controls : a 1 = 3 ∧ a 2 = 10 ∧ a 3 = 22 ∧ a 4 = 36 ∧ a 5 = 50 ∧ a 6 = 66 ∧ a 7 = 82 ∧ a 8 = 100 ∧ a 9 = 120 ∧ a 10 = 142 ∧ a 11 = 164 ∧ a 12 = 188 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩

/-- The problem as the site states it. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X)) = PowerSeries.X * (3 + 4 * PowerSeries.X + 2 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 - 5 * PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 8 - 2 * PowerSeries.X ^ 10) ∧
    (∀ n : ℕ, 7 < n → Even n → (a n : ℚ) = ((n : ℚ) ^ 2 + 24 * (n : ℚ) - 56) / 2) ∧
    (∀ n : ℕ, 7 < n → Odd n → (a n : ℚ) = ((n : ℚ) ^ 2 + 24 * (n : ℚ) - 57) / 2) :=
  ⟨gf, even_form, odd_form⟩

end OMA.S_oeis_a190092

theorem OMA.solution : type_of% @OMA.S_oeis_a190092.main :=
  OMA.S_oeis_a190092.conjecture
