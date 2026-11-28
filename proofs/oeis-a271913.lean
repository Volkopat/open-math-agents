import OMAStatements.S_oeis_a271913
import Mathlib.Tactic

namespace OMA.P_oeis_a271913

open OMA.S_oeis_a271913

/-! ### Part 1: Canonical lex-ordered triples and span decomposition -/

private def ptLt {n : ℕ} (p q : Fin 4 × Fin n) : Prop :=
  p.2.1 < q.2.1 ∨ (p.2.1 = q.2.1 ∧ p.1.1 < q.1.1)

private instance {n : ℕ} (p q : Fin 4 × Fin n) : Decidable (ptLt p q) := by
  unfold ptLt; infer_instance

private lemma ptLt_trans {n : ℕ} {p q r : Fin 4 × Fin n}
    (h1 : ptLt p q) (h2 : ptLt q r) : ptLt p r := by
  unfold ptLt at *; omega

private lemma ptLt_irrefl {n : ℕ} (p : Fin 4 × Fin n) : ¬ ptLt p p := by
  unfold ptLt; omega

private lemma ptLt_ne {n : ℕ} {p q : Fin 4 × Fin n} (h : ptLt p q) : p ≠ q := by
  intro heq; subst heq; exact ptLt_irrefl p h

private lemma ptLt_trichotomy {n : ℕ} (p q : Fin 4 × Fin n) :
    ptLt p q ∨ p = q ∨ ptLt q p := by
  rcases lt_trichotomy p.2.1 q.2.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy p.1.1 q.1.1 with h1 | h1 | h1
    · exact Or.inl (Or.inr ⟨h, h1⟩)
    · exact Or.inr (Or.inl (Prod.ext (Fin.ext h1) (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h1⟩))
  · exact Or.inr (Or.inr (Or.inl h))

private lemma isIsoscelesTriple_symm12 {p q r : ℤ × ℤ}
    (h : IsIsoscelesTriple p q r) : IsIsoscelesTriple q p r := by
  unfold IsIsoscelesTriple sqDist at *
  refine ⟨?_, ?_⟩
  · intro heq; apply h.1; linear_combination -heq
  · rcases h.2 with h1 | h2 | h3
    · right; right; linear_combination -h1
    · right; left; linear_combination -h2
    · left; linear_combination -h3

private lemma isIsoscelesTriple_symm23 {p q r : ℤ × ℤ}
    (h : IsIsoscelesTriple p q r) : IsIsoscelesTriple p r q := by
  unfold IsIsoscelesTriple sqDist at *
  refine ⟨?_, ?_⟩
  · intro heq; apply h.1; linear_combination -heq
  · rcases h.2 with h1 | h2 | h3
    · right; left; linear_combination -h1
    · left; linear_combination -h2
    · right; right; linear_combination -h3

private lemma isIsoscelesTriple_perm {p q r p' q' r' : ℤ × ℤ}
    (h : IsIsoscelesTriple p q r)
    (hset : ({p, q, r} : Finset (ℤ × ℤ)) = {p', q', r'})
    (hnd : p' ≠ q' ∧ q' ≠ r' ∧ p' ≠ r') :
    IsIsoscelesTriple p' q' r' := by
  have hp' : p' ∈ ({p, q, r} : Finset (ℤ × ℤ)) := by rw [hset]; simp
  have hq' : q' ∈ ({p, q, r} : Finset (ℤ × ℤ)) := by rw [hset]; simp
  have hr' : r' ∈ ({p, q, r} : Finset (ℤ × ℤ)) := by rw [hset]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp' hq' hr'
  rcases hp' with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl <;>
    rcases hr' with rfl | rfl | rfl
  all_goals try (exfalso; tauto)
  · exact h
  · exact isIsoscelesTriple_symm23 h
  · exact isIsoscelesTriple_symm12 h
  · exact isIsoscelesTriple_symm23 (isIsoscelesTriple_symm12 h)
  · exact isIsoscelesTriple_symm12 (isIsoscelesTriple_symm23 h)
  · exact isIsoscelesTriple_symm12 (isIsoscelesTriple_symm23 (isIsoscelesTriple_symm12 h))

private def isIsoTripFin {n : ℕ} (p q r : Fin 4 × Fin n) : Prop :=
  ptLt p q ∧ ptLt q r ∧
  IsIsoscelesTriple (p.1.1, p.2.1) (q.1.1, q.2.1) (r.1.1, r.2.1)

private instance {n : ℕ} (p q r : Fin 4 × Fin n) : Decidable (isIsoTripFin p q r) := by
  unfold isIsoTripFin IsIsoscelesTriple sqDist; infer_instance

private lemma A271913_eq_card_ordered (n : ℕ) :
    A271913 n =
      (Finset.univ.filter (fun t : (Fin 4 × Fin n) × (Fin 4 × Fin n) × (Fin 4 × Fin n) =>
        isIsoTripFin t.1 t.2.1 t.2.2)).card := by
  classical
  unfold A271913
  symm
  refine Finset.card_bij (fun t _ => ({t.1, t.2.1, t.2.2} : Finset (Fin 4 × Fin n))) ?_ ?_ ?_
  · rintro ⟨p, q, r⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rcases ht with ⟨hpq, hqr, hiso⟩
    have hpr : ptLt p r := ptLt_trans hpq hqr
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    refine ⟨?_, p, by simp, q, by simp, r, by simp, rfl, hiso⟩
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [ptLt_ne hqr]
    · simp [ptLt_ne hpq, ptLt_ne hpr]
  · rintro ⟨p1, q1, r1⟩ ht1 ⟨p2, q2, r2⟩ ht2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
    rcases ht1 with ⟨hpq1, hqr1, _⟩
    rcases ht2 with ⟨hpq2, hqr2, _⟩
    have hpr1 := ptLt_trans hpq1 hqr1
    have hpr2 := ptLt_trans hpq2 hqr2
    have hmem : ∀ x, x ∈ ({p1, q1, r1} : Finset _) ↔ x ∈ ({p2, q2, r2} : Finset _) := by
      intro x; rw [heq]
    have hp : p1 = p2 := by
      have h1 := (hmem p1).mp (by simp)
      have h2 := (hmem p2).mpr (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      have hle1 : p1 = p2 ∨ ptLt p2 p1 := by
        rcases h1 with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr hpq2
        · exact Or.inr hpr2
      have hle2 : p2 = p1 ∨ ptLt p1 p2 := by
        rcases h2 with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr hpq1
        · exact Or.inr hpr1
      rcases hle1 with h | h
      · exact h
      · rcases hle2 with h' | h'
        · exact h'.symm
        · exfalso; exact ptLt_irrefl p2 (ptLt_trans h h')
    subst hp
    have hr : r1 = r2 := by
      have h1 := (hmem r1).mp (by simp)
      have h2 := (hmem r2).mpr (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      rcases h1 with h1 | h1 | rfl
      · exfalso; exact ptLt_ne hpr1 h1.symm
      · rcases h2 with h2 | h2 | h2
        · exfalso; exact ptLt_ne hpr2 h2.symm
        · exfalso
          have ha : ptLt r1 r2 := by rw [h1]; exact hqr2
          have hb : ptLt r2 r1 := by rw [h2]; exact hqr1
          exact ptLt_irrefl r1 (ptLt_trans ha hb)
        · exact h2.symm
      · rfl
    subst hr
    have hq : q1 = q2 := by
      have h1 := (hmem q1).mp (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with h | h | h
      · exfalso; exact ptLt_ne hpq1 h.symm
      · exact h
      · exfalso; exact ptLt_ne hqr1 h
    subst hq; rfl
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS
    rcases hS with ⟨hcard, p, _, q, _, r, _, hSeq, hiso⟩
    have hnd : p ≠ q ∧ q ≠ r ∧ p ≠ r := by
      refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> subst hSeq
      · have : ({p, p, r} : Finset (Fin 4 × Fin n)).card ≤ 2 := by
          rw [Finset.insert_eq_of_mem (by simp)]; exact Finset.card_le_two
        omega
      · have : ({p, q, q} : Finset (Fin 4 × Fin n)).card ≤ 2 := by
          rw [show ({p, q, q} : Finset (Fin 4 × Fin n)) = {p, q} by ext x; simp]; exact Finset.card_le_two
        omega
      · have : ({p, q, p} : Finset (Fin 4 × Fin n)).card ≤ 2 := by
          rw [show ({p, q, p} : Finset (Fin 4 × Fin n)) = {p, q} by ext x; simp; tauto]; exact Finset.card_le_two
        omega
    have hsort : ∃ a b c : Fin 4 × Fin n, ptLt a b ∧ ptLt b c ∧
        ({a, b, c} : Finset (Fin 4 × Fin n)) = {p, q, r} := by
      rcases ptLt_trichotomy p q with hpq | rfl | hqp
      · rcases ptLt_trichotomy q r with hqr | rfl | hrq
        · exact ⟨p, q, r, hpq, hqr, rfl⟩
        · exact (hnd.2.1 rfl).elim
        · rcases ptLt_trichotomy p r with hpr | rfl | hrp
          · exact ⟨p, r, q, hpr, hrq, by ext x; simp; tauto⟩
          · exact (hnd.2.2 rfl).elim
          · exact ⟨r, p, q, hrp, hpq, by ext x; simp; tauto⟩
      · exact (hnd.1 rfl).elim
      · rcases ptLt_trichotomy p r with hpr | rfl | hrp
        · exact ⟨q, p, r, hqp, hpr, by ext x; simp; tauto⟩
        · exact (hnd.2.2 rfl).elim
        · rcases ptLt_trichotomy q r with hqr | rfl | hrq
          · exact ⟨q, r, p, hqr, hrp, by ext x; simp; tauto⟩
          · exact (hnd.2.1 rfl).elim
          · exact ⟨r, q, p, hrq, hqp, by ext x; simp; tauto⟩
    rcases hsort with ⟨a, b, c, hab, hbc, habc⟩
    have hac := ptLt_trans hab hbc
    have hmap : ({((p.1.1 : ℤ), (p.2.1 : ℤ)), ((q.1.1 : ℤ), (q.2.1 : ℤ)),
        ((r.1.1 : ℤ), (r.2.1 : ℤ))} : Finset (ℤ × ℤ)) =
        {((a.1.1 : ℤ), (a.2.1 : ℤ)), ((b.1.1 : ℤ), (b.2.1 : ℤ)), ((c.1.1 : ℤ), (c.2.1 : ℤ))} := by
      have := congrArg (Finset.image (fun x : Fin 4 × Fin n => ((x.1.1 : ℤ), (x.2.1 : ℤ)))) habc.symm
      simpa [Finset.image_insert, Finset.image_singleton] using this
    have hnd_z : ((a.1.1 : ℤ), (a.2.1 : ℤ)) ≠ ((b.1.1 : ℤ), (b.2.1 : ℤ)) ∧
        ((b.1.1 : ℤ), (b.2.1 : ℤ)) ≠ ((c.1.1 : ℤ), (c.2.1 : ℤ)) ∧
        ((a.1.1 : ℤ), (a.2.1 : ℤ)) ≠ ((c.1.1 : ℤ), (c.2.1 : ℤ)) := by
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Prod.mk.injEq, Nat.cast_inj] at h
      · exact ptLt_ne hab (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
      · exact ptLt_ne hbc (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
      · exact ptLt_ne hac (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
    refine ⟨(a, b, c), ?_, by rw [habc, hSeq]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hab, hbc, isIsoscelesTriple_perm hiso hmap hnd_z⟩

/-- Canonical span-`w` ordered isosceles triangles: `x_1 = 0`, `0 ≤ x_2 ≤ w`, `x_3 = w`. -/
private def isSpanIso (w : ℕ) (t : Fin 4 × (Fin 4 × ℕ) × Fin 4) : Prop :=
  t.2.1.2 ≤ w ∧
  (0 < t.2.1.2 ∨ (0 = t.2.1.2 ∧ t.1.1 < t.2.1.1.1)) ∧
  (t.2.1.2 < w ∨ (t.2.1.2 = w ∧ t.2.1.1.1 < t.2.2.1)) ∧
  IsIsoscelesTriple (t.1.1, 0) (t.2.1.1.1, t.2.1.2) (t.2.2.1, w)

private instance (w : ℕ) (t : Fin 4 × (Fin 4 × ℕ) × Fin 4) :
    Decidable (isSpanIso w t) := by
  unfold isSpanIso IsIsoscelesTriple sqDist; infer_instance

private def spanSpace (w : ℕ) : Finset (Fin 4 × (Fin 4 × ℕ) × Fin 4) :=
  (Finset.univ : Finset (Fin 4)) ×ˢ
    (((Finset.univ : Finset (Fin 4)) ×ˢ Finset.range (w + 1)) ×ˢ (Finset.univ : Finset (Fin 4)))

private def spanCount (w : ℕ) : ℕ :=
  ((spanSpace w).filter (isSpanIso w)).card

private lemma mem_spanSpace {w : ℕ} {t : Fin 4 × (Fin 4 × ℕ) × Fin 4} :
    t ∈ spanSpace w ↔ t.2.1.2 ≤ w := by
  simp only [spanSpace, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and, and_true]
  omega

private lemma A271913_eq_sum_spanCount (n : ℕ) :
    A271913 n = ∑ w ∈ Finset.range n, (n - w) * spanCount w := by
  rw [A271913_eq_card_ordered]
  have hsum : ∑ w ∈ Finset.range n, (n - w) * spanCount w =
      ((Finset.range n).sigma (fun w =>
        (Finset.range (n - w)) ×ˢ ((spanSpace w).filter (isSpanIso w)))).card := by
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.card_product, Finset.card_range, spanCount]
  rw [hsum]
  refine Finset.card_bij
    (fun t _ =>
      ⟨t.2.2.2.1 - t.1.2.1,
       (t.1.2.1,
        (t.1.1, (t.2.1.1, t.2.1.2.1 - t.1.2.1), t.2.2.1))⟩) ?_ ?_ ?_
  · rintro ⟨p, q, r⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rcases ht with ⟨hpq, hqr, hiso⟩
    unfold ptLt at hpq hqr
    have hpx := p.2.isLt
    have hqx := q.2.isLt
    have hrx := r.2.isLt
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product, Finset.mem_filter,
      mem_spanSpace, isSpanIso]
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rcases hpq with h | ⟨h1, h2⟩
      · left; omega
      · right; exact ⟨by omega, h2⟩
    · rcases hqr with h | ⟨h1, h2⟩
      · left; omega
      · right; exact ⟨by omega, h2⟩
    · unfold IsIsoscelesTriple sqDist at hiso ⊢
      have h1 : ((q.2.1 - p.2.1 : ℕ) : ℤ) = (q.2.1 : ℤ) - (p.2.1 : ℤ) := Nat.cast_sub (by omega)
      have h2 : ((r.2.1 - p.2.1 : ℕ) : ℤ) = (r.2.1 : ℤ) - (p.2.1 : ℤ) := Nat.cast_sub (by omega)
      rw [h1, h2]
      refine ⟨?_, ?_⟩
      · intro heq; apply hiso.1; linear_combination heq
      · rcases hiso.2 with hc | hc | hc
        · left; linear_combination hc
        · right; left; linear_combination hc
        · right; right; linear_combination hc
  · rintro ⟨p1, q1, r1⟩ ht1 ⟨p2, q2, r2⟩ ht2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
    rcases ht1 with ⟨hpq1, hqr1, _⟩
    rcases ht2 with ⟨hpq2, hqr2, _⟩
    unfold ptLt at hpq1 hqr1 hpq2 hqr2
    have hw : r1.2.1 - p1.2.1 = r2.2.1 - p2.2.1 := congrArg Sigma.fst heq
    have hsnd : (p1.2.1, (p1.1, (q1.1, q1.2.1 - p1.2.1), r1.1)) =
        (p2.2.1, (p2.1, (q2.1, q2.2.1 - p2.2.1), r2.1)) := eq_of_heq (Sigma.ext_iff.mp heq).2
    simp only [Prod.mk.injEq] at hsnd
    rcases hsnd with ⟨hx0, hy1, ⟨hy2, hqsub⟩, hy3⟩
    have hp : p1 = p2 := Prod.ext hy1 (Fin.ext hx0)
    have hq : q1 = q2 := Prod.ext hy2 (Fin.ext (by omega))
    have hr : r1 = r2 := Prod.ext hy3 (Fin.ext (by omega))
    rw [hp, hq, hr]
  · rintro ⟨w, ⟨x0, ⟨y1, ⟨y2, dx⟩, y3⟩⟩⟩ hmem
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product, Finset.mem_filter,
      mem_spanSpace, isSpanIso] at hmem
    rcases hmem with ⟨hw, hx0, hdx, _, hlt1, hlt2, hiso⟩
    let p : Fin 4 × Fin n := (y1, ⟨x0, by omega⟩)
    let q : Fin 4 × Fin n := (y2, ⟨x0 + dx, by omega⟩)
    let r : Fin 4 × Fin n := (y3, ⟨x0 + w, by omega⟩)
    refine ⟨(p, q, r), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · unfold ptLt; rcases hlt1 with h | ⟨h1, h2⟩
        · left; simp only [p, q]; omega
        · right; simp only [p, q]; exact ⟨by omega, h2⟩
      · unfold ptLt; rcases hlt2 with h | ⟨h1, h2⟩
        · left; simp only [q, r]; omega
        · right; simp only [q, r]; exact ⟨by omega, h2⟩
      · unfold IsIsoscelesTriple sqDist at hiso ⊢
        simp only [p, q, r]
        push_cast
        refine ⟨?_, ?_⟩
        · intro heq; apply hiso.1; linear_combination heq
        · rcases hiso.2 with hc | hc | hc
          · left; linear_combination hc
          · right; left; linear_combination hc
          · right; right; linear_combination hc
    · refine Sigma.ext (by simp only [p, r]; omega) (heq_of_eq ?_)
      simp only [p, q, r, Nat.add_sub_cancel_left]

/-! ### Part 2: Exact values of `spanCount w` -/

private lemma spanCount_small :
    spanCount 0 = 0 ∧ spanCount 1 = 16 ∧ spanCount 2 = 36 ∧
    spanCount 3 = 28 ∧ spanCount 4 = 20 ∧ spanCount 5 = 12 ∧
    spanCount 6 = 16 ∧ spanCount 7 = 4 ∧ spanCount 8 = 16 ∧
    spanCount 9 = 8 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

private lemma spanCount_ge10 (w : ℕ) (hw : 10 ≤ w) :
    spanCount w = if Even w then 16 else 4 := by
  let tL1 : Fin 4 × (Fin 4 × ℕ) × Fin 4 := (0, (2, 0), 1)
  let tL2 : Fin 4 × (Fin 4 × ℕ) × Fin 4 := (1, (3, 0), 2)
  let tR1 : Fin 4 × (Fin 4 × ℕ) × Fin 4 := (1, (0, w), 2)
  let tR2 : Fin 4 × (Fin 4 × ℕ) × Fin 4 := (2, (1, w), 3)
  have htL1 : isSpanIso w tL1 := by
    unfold isSpanIso IsIsoscelesTriple sqDist tL1
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    refine ⟨by omega, Or.inr ⟨trivial, by omega⟩, Or.inl (by omega), ?_, ?_⟩
    · norm_num; omega
    · right; left; norm_num
  have htL2 : isSpanIso w tL2 := by
    unfold isSpanIso IsIsoscelesTriple sqDist tL2
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [Fin.val_one, Fin.val_two, h3]
    refine ⟨by omega, Or.inr ⟨trivial, by omega⟩, Or.inl (by omega), ?_, ?_⟩
    · norm_num; omega
    · right; left; norm_num
  have htR1 : isSpanIso w tR1 := by
    unfold isSpanIso IsIsoscelesTriple sqDist tR1
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    refine ⟨by omega, Or.inl (by omega), Or.inr ⟨trivial, by omega⟩, ?_, ?_⟩
    · norm_num; omega
    · right; right; norm_num
  have htR2 : isSpanIso w tR2 := by
    unfold isSpanIso IsIsoscelesTriple sqDist tR2
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [Fin.val_one, Fin.val_two, h3]
    refine ⟨by omega, Or.inl (by omega), Or.inr ⟨trivial, by omega⟩, ?_, ?_⟩
    · norm_num; omega
    · right; right; norm_num
  have hclass : ∀ t : Fin 4 × (Fin 4 × ℕ) × Fin 4,
      isSpanIso w t ↔
        t = tL1 ∨ t = tL2 ∨ t = tR1 ∨ t = tR2 ∨
        (Even w ∧ t.2.1.2 = w / 2 ∧ t.1 = t.2.2 ∧ t.1 ≠ t.2.1.1) := by
    rintro ⟨y1, ⟨y2, dx⟩, y3⟩
    constructor
    · rintro ⟨hdx_le, hlt1, hlt2, hnc, hdist⟩
      dsimp only at hdx_le hlt1 hlt2 hnc hdist
      have hy1 := y1.isLt; have hy2 := y2.isLt; have hy3 := y3.isLt
      have hdx_cases : dx = 0 ∨ dx = w ∨ (Even w ∧ dx = w / 2) := by
        unfold sqDist at hdist
        dsimp only at hdist
        rcases hdist with h1 | h2 | h3
        · have hsub : ((dx : ℤ) - ((w : ℤ) - (dx : ℤ))) * (w : ℤ) =
              ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 - ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 := by
            linear_combination h1
          have hbd1 : ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd2 : ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd3 : 0 ≤ ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 := sq_nonneg _
          have hbd4 : 0 ≤ ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 := sq_nonneg _
          have heq : (dx : ℤ) = (w : ℤ) - (dx : ℤ) := by nlinarith
          right; right
          exact ⟨⟨dx, by omega⟩, by omega⟩
        · have hsub : (-(dx : ℤ)) * (2 * (w : ℤ) - (dx : ℤ)) =
              ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 - ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 := by
            linear_combination h2
          have hbd1 : ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd2 : ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd3 : 0 ≤ ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 := sq_nonneg _
          have hbd4 : 0 ≤ ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 := sq_nonneg _
          have hdx0 : dx = 0 := by nlinarith
          exact Or.inl hdx0
        · have hsub : ((w : ℤ) - (dx : ℤ)) * ((w : ℤ) + (dx : ℤ)) =
              ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 - ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 := by
            linear_combination h3
          have hbd1 : ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd2 : ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd3 : 0 ≤ ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 := sq_nonneg _
          have hbd4 : 0 ≤ ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 := sq_nonneg _
          have hdxw : dx = w := by nlinarith
          exact Or.inr (Or.inl hdxw)
      rcases hdx_cases with h0 | hw' | ⟨hev, hmid⟩
      · have hy12 : y1.1 < y2.1 := by rw [h0] at hlt1; rcases hlt1 with h | ⟨_, h⟩ <;> omega
        have heq_y : ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 = ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 := by
          unfold sqDist at hdist; dsimp only at hdist; rw [h0] at hdist
          have hbd : ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd' : ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd'' : ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hnn1 : 0 ≤ ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 := sq_nonneg _
          have hnn2 : 0 ≤ ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 := sq_nonneg _
          have hnn3 : 0 ≤ ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 := sq_nonneg _
          rcases hdist with h1 | h2 | h3
          · exfalso; push_cast at h1; nlinarith
          · linear_combination h2
          · exfalso; push_cast at h3; nlinarith
        have hsum : y1.1 + y2.1 = 2 * y3.1 := by
          have hfac : ((y2.1 : ℤ) - (y1.1 : ℤ)) * ((y1.1 : ℤ) + (y2.1 : ℤ) - 2 * (y3.1 : ℤ)) = 0 := by
            linear_combination heq_y
          rcases mul_eq_zero.mp hfac with h | h <;> omega
        have hvals : (y1.1 = 0 ∧ y2.1 = 2 ∧ y3.1 = 1) ∨ (y1.1 = 1 ∧ y2.1 = 3 ∧ y3.1 = 2) := by
          omega
        rcases hvals with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
        · left
          exact Prod.ext (Fin.ext ha) (Prod.ext (Prod.ext (Fin.ext hb) h0) (Fin.ext hc))
        · right; left
          exact Prod.ext (Fin.ext ha) (Prod.ext (Prod.ext (Fin.ext hb) h0) (Fin.ext hc))
      · have hy23 : y2.1 < y3.1 := by rw [hw'] at hlt2; rcases hlt2 with h | ⟨_, h⟩ <;> omega
        have heq_y : ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 = ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 := by
          unfold sqDist at hdist; dsimp only at hdist; rw [hw'] at hdist
          have hbd : ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd' : ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd'' : ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hnn1 : 0 ≤ ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 := sq_nonneg _
          have hnn2 : 0 ≤ ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 := sq_nonneg _
          have hnn3 : 0 ≤ ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 := sq_nonneg _
          rcases hdist with h1 | h2 | h3
          · exfalso; nlinarith
          · exfalso; nlinarith
          · linear_combination h3
        have hsum : y2.1 + y3.1 = 2 * y1.1 := by
          have hfac : ((y3.1 : ℤ) - (y2.1 : ℤ)) * ((y2.1 : ℤ) + (y3.1 : ℤ) - 2 * (y1.1 : ℤ)) = 0 := by
            linear_combination heq_y
          rcases mul_eq_zero.mp hfac with h | h <;> omega
        have hvals : (y1.1 = 1 ∧ y2.1 = 0 ∧ y3.1 = 2) ∨ (y1.1 = 2 ∧ y2.1 = 1 ∧ y3.1 = 3) := by
          omega
        rcases hvals with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
        · right; right; left
          exact Prod.ext (Fin.ext ha) (Prod.ext (Prod.ext (Fin.ext hb) hw') (Fin.ext hc))
        · right; right; right; left
          exact Prod.ext (Fin.ext ha) (Prod.ext (Prod.ext (Fin.ext hb) hw') (Fin.ext hc))
      · right; right; right; right
        have heq_y : ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 = ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 := by
          unfold sqDist at hdist; dsimp only at hdist
          obtain ⟨m, rfl⟩ := hev
          have hdxm : dx = m := by omega
          rw [hdxm] at hdist; push_cast at hdist
          have hbd1 : ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd2 : ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hbd3 : ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 ≤ 9 := by nlinarith
          have hnn1 : 0 ≤ ((y2.1 : ℤ) - (y3.1 : ℤ)) ^ 2 := sq_nonneg _
          have hnn2 : 0 ≤ ((y1.1 : ℤ) - (y2.1 : ℤ)) ^ 2 := sq_nonneg _
          have hnn3 : 0 ≤ ((y3.1 : ℤ) - (y1.1 : ℤ)) ^ 2 := sq_nonneg _
          rcases hdist with h1 | h2 | h3
          · linear_combination h1
          · exfalso; nlinarith
          · exfalso; nlinarith
        have hy13 : y1.1 = y3.1 := by
          by_contra hne
          have hsum : (y1.1 : ℤ) + (y3.1 : ℤ) = 2 * (y2.1 : ℤ) := by
            have hfac : ((y1.1 : ℤ) - (y3.1 : ℤ)) * ((y1.1 : ℤ) + (y3.1 : ℤ) - 2 * (y2.1 : ℤ)) = 0 := by
              linear_combination heq_y
            rcases mul_eq_zero.mp hfac with h | h <;> omega
          apply hnc
          obtain ⟨m, rfl⟩ := hev
          have hdxm : dx = m := by omega
          rw [hdxm]; push_cast; linear_combination -(m : ℤ) * hsum
        refine ⟨hev, hmid, Fin.ext hy13, ?_⟩
        intro heq
        dsimp only at heq
        apply hnc
        rw [← heq, hy13]; ring
    · rintro (h | h | h | h | ⟨hev, hmid, hy13, hy12⟩)
      · rw [h]; exact htL1
      · rw [h]; exact htL2
      · rw [h]; exact htR1
      · rw [h]; exact htR2
      · dsimp only at hmid hy13 hy12
        have hy13' : y1 = y3 := hy13
        subst hy13'
        obtain ⟨m, rfl⟩ := hev
        have hdxm : dx = m := by omega
        unfold isSpanIso IsIsoscelesTriple sqDist
        refine ⟨by dsimp; omega, Or.inl (by dsimp; omega), Or.inl (by dsimp; omega), ?_, ?_⟩
        · rw [hdxm]
          intro heq
          have hne : (y2.1 : ℤ) ≠ (y1.1 : ℤ) := fun h => hy12 (Fin.ext (by omega)).symm
          have hmpos : (m : ℤ) ≠ 0 := by omega
          have h0 : ((y2.1 : ℤ) - (y1.1 : ℤ)) * (2 * (m : ℤ)) = 0 := by
            push_cast at heq; linear_combination heq
          rcases mul_eq_zero.mp h0 with h | h <;> omega
        · left; rw [hdxm]; push_cast; ring
  have hcard4 : ({tL1, tL2, tR1, tR2} : Finset _).card = 4 := by
    have h12 : tL1 ≠ tL2 := by intro h; have := congrArg (fun x => x.1.1) h; dsimp [tL1, tL2] at this; omega
    have h13 : tL1 ≠ tR1 := by intro h; have := congrArg (fun x => x.2.1.2) h; dsimp [tL1, tR1] at this; omega
    have h14 : tL1 ≠ tR2 := by intro h; have := congrArg (fun x => x.2.1.2) h; dsimp [tL1, tR2] at this; omega
    have h23 : tL2 ≠ tR1 := by intro h; have := congrArg (fun x => x.2.1.2) h; dsimp [tL2, tR1] at this; omega
    have h24 : tL2 ≠ tR2 := by intro h; have := congrArg (fun x => x.2.1.2) h; dsimp [tL2, tR2] at this; omega
    have h34 : tR1 ≠ tR2 := by intro h; have := congrArg (fun x => x.1.1) h; dsimp [tR1, tR2] at this; omega
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h34]
    · simp [h23, h24]
    · simp [h12, h13, h14]
  unfold spanCount
  by_cases hev : Even w
  · rw [if_pos hev]
    let S_mid : Finset (Fin 4 × (Fin 4 × ℕ) × Fin 4) :=
      (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 ≠ p.2)).image
        (fun p => (p.1, (p.2, w / 2), p.1))
    have hset : (spanSpace w).filter (isSpanIso w) = {tL1, tL2, tR1, tR2} ∪ S_mid := by
      ext t
      simp only [Finset.mem_filter, mem_spanSpace, hclass t, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton, S_mid, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, rfl | rfl | rfl | rfl | ⟨_, hmid, hy13, hy12⟩⟩
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
        · right
          rcases t with ⟨a, ⟨b, d⟩, c⟩
          refine ⟨(a, b), hy12, ?_⟩
          exact Prod.ext rfl (Prod.ext (Prod.ext rfl hmid.symm) hy13)
      · rintro ((rfl | rfl | rfl | rfl) | ⟨⟨a, b⟩, hab, rfl⟩)
        · exact ⟨by simp [tL1], Or.inl rfl⟩
        · exact ⟨by simp [tL2], Or.inr (Or.inl rfl)⟩
        · exact ⟨by simp [tR1], Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨by simp [tR2], Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
        · exact ⟨by dsimp; omega, Or.inr (Or.inr (Or.inr (Or.inr ⟨hev, rfl, rfl, hab⟩)))⟩
    have hdisj : Disjoint ({tL1, tL2, tR1, tR2} : Finset _) S_mid := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht1
      simp only [S_mid, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ht2
      rcases ht2 with ⟨⟨a, b⟩, _, rfl⟩
      rcases ht1 with h | h | h | h <;>
        have := congrArg (fun x => x.2.1.2) h <;> dsimp [tL1, tL2, tR1, tR2] at this <;> omega
    have hcard_mid : S_mid.card = 12 := by
      rw [Finset.card_image_of_injective]
      · decide
      · intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 h.2.1.1
    rw [hset, Finset.card_union_of_disjoint hdisj, hcard4, hcard_mid]
  · rw [if_neg hev]
    have hset : (spanSpace w).filter (isSpanIso w) = {tL1, tL2, tR1, tR2} := by
      ext t
      simp only [Finset.mem_filter, mem_spanSpace, hclass t,
        Finset.mem_insert, Finset.mem_singleton, hev, false_and, or_false]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨by simp [tL1], Or.inl rfl⟩
        · exact ⟨by simp [tL2], Or.inr (Or.inl rfl)⟩
        · exact ⟨by simp [tR1], Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨by simp [tR2], Or.inr (Or.inr (Or.inr rfl))⟩
    rw [hset, hcard4]

/-! ### Part 3: Closed form, recurrence, and rational g.f. -/

private lemma A271913_step (n : ℕ) :
    A271913 (n + 1) = A271913 n + ∑ w ∈ Finset.range (n + 1), spanCount w := by
  rw [A271913_eq_sum_spanCount (n + 1), A271913_eq_sum_spanCount n, Finset.sum_range_succ,
    Finset.sum_range_succ]
  have h0 : (n + 1 - n) * spanCount n = spanCount n := by simp
  rw [h0, ← add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_range] at hw
  have h1 : n + 1 - w = (n - w) + 1 := by omega
  rw [h1]; ring

private lemma sum_spanCount_ge10 (n : ℕ) (hn : 10 ≤ n) :
    (∑ w ∈ Finset.range n, (spanCount w : ℤ)) =
      if Even n then 10 * (n : ℤ) + 56 else 10 * (n : ℤ) + 62 := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm10 : m < 10
    · have hm9 : m = 9 := by omega
      subst hm9
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := spanCount_small
      have h10 : Even 10 := by decide
      rw [if_pos h10, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    · rw [Finset.sum_range_succ, ih (by omega), spanCount_ge10 m (by omega)]
      by_cases hm : Even m
      · have hms : ¬ Even (m + 1) := by rwa [Nat.even_add_one, not_not]
        rw [if_pos hm, if_pos hm, if_neg hms]; push_cast; ring
      · have hms : Even (m + 1) := by rwa [Nat.even_add_one]
        rw [if_neg hm, if_neg hm, if_pos hms]; push_cast; ring

private lemma A271913_small :
    A271913 1 = 0 ∧ A271913 2 = 16 ∧ A271913 3 = 68 ∧ A271913 4 = 148 ∧
    A271913 5 = 248 ∧ A271913 6 = 360 ∧ A271913 7 = 488 ∧ A271913 8 = 620 ∧
    A271913 9 = 768 ∧ A271913 10 = 924 ∧ A271913 11 = 1096 ∧ A271913 12 = 1272 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := spanCount_small
  have h10 : spanCount 10 = 16 := by rw [spanCount_ge10 10 (le_refl _)]; decide
  have h11 : spanCount 11 = 4 := by rw [spanCount_ge10 11 (by omega)]; decide
  have ha1 : A271913 1 = 0 := by rw [A271913_eq_sum_spanCount 1, Finset.sum_range_one]; simp [h0]
  have ha2 : A271913 2 = 16 := by
    rw [A271913_step 1, ha1, Finset.sum_range_succ, Finset.sum_range_one]; simp [h0, h1]
  have ha3 : A271913 3 = 68 := by
    rw [A271913_step 2, ha2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [h0, h1, h2]
  have ha4 : A271913 4 = 148 := by
    rw [A271913_step 3, ha3, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]; simp [h0, h1, h2, h3]
  have ha5 : A271913 5 = 248 := by
    rw [A271913_step 4, ha4, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]; simp [h0, h1, h2, h3, h4]
  have ha6 : A271913 6 = 360 := by
    rw [A271913_step 5, ha5, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [h0, h1, h2, h3, h4, h5]
  have ha7 : A271913 7 = 488 := by
    rw [A271913_step 6, ha6, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [h0, h1, h2, h3, h4, h5, h6]
  have ha8 : A271913 8 = 620 := by
    rw [A271913_step 7, ha7, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]; simp [h0, h1, h2, h3, h4, h5, h6, h7]
  have ha9 : A271913 9 = 768 := by
    rw [A271913_step 8, ha8, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have ha10 : A271913 10 = 924 := by
    rw [A271913_step 9, ha9, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have ha11 : A271913 11 = 1096 := by
    rw [A271913_step 10, ha10, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  have ha12 : A271913 12 = 1272 := by
    rw [A271913_step 11, ha11, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  exact ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12⟩

private lemma A271913_closed (n : ℕ) (hn : 8 < n) :
    (A271913 n : ℤ) =
      if Even n then 5 * (n : ℤ) ^ 2 + 64 * n - 216 else 5 * (n : ℤ) ^ 2 + 64 * n - 213 := by
  induction n with
  | zero => omega
  | succ m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, h9, h10, _, _⟩ := A271913_small
    by_cases hm10 : m < 10
    · have hm8 : 8 ≤ m := by omega
      interval_cases m <;> norm_num [h9, h10]
    · have hstep := congrArg (Nat.cast (R := ℤ)) (A271913_step m)
      push_cast at hstep
      have hsum := sum_spanCount_ge10 (m + 1) (by omega)
      have ihm := ih (by omega)
      by_cases hm : Even m
      · have hms : ¬ Even (m + 1) := by rwa [Nat.even_add_one, not_not]
        rw [if_pos hm] at ihm
        rw [if_neg hms] at hsum ⊢
        push_cast at hsum ⊢
        linarith
      · have hms : Even (m + 1) := by rwa [Nat.even_add_one]
        rw [if_neg hm] at ihm
        rw [if_pos hms] at hsum ⊢
        push_cast at hsum ⊢
        linarith

private lemma A271913_rec (n : ℕ) (hn : 12 < n) :
    (A271913 n : ℤ) = 2 * A271913 (n - 1) - 2 * A271913 (n - 3) + A271913 (n - 4) := by
  have h0 := A271913_closed n (by omega)
  have h1 := A271913_closed (n - 1) (by omega)
  have h3 := A271913_closed (n - 3) (by omega)
  have h4 := A271913_closed (n - 4) (by omega)
  have hs1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Nat.cast_sub (by omega)
  have hs3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := Nat.cast_sub (by omega)
  have hs4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := Nat.cast_sub (by omega)
  by_cases hev : Even n
  · have h1o : ¬ Even (n - 1) := by rw [Nat.even_iff] at hev ⊢; omega
    have h3o : ¬ Even (n - 3) := by rw [Nat.even_iff] at hev ⊢; omega
    have h4e : Even (n - 4) := by rw [Nat.even_iff] at hev ⊢; omega
    rw [if_pos hev] at h0; rw [if_neg h1o, hs1] at h1
    rw [if_neg h3o, hs3] at h3; rw [if_pos h4e, hs4] at h4
    linarith
  · have h1e : Even (n - 1) := by rw [Nat.even_iff] at hev ⊢; omega
    have h3e : Even (n - 3) := by rw [Nat.even_iff] at hev ⊢; omega
    have h4o : ¬ Even (n - 4) := by rw [Nat.even_iff] at hev ⊢; omega
    rw [if_neg hev] at h0; rw [if_pos h1e, hs1] at h1
    rw [if_pos h3e, hs3] at h3; rw [if_neg h4o, hs4] at h4
    linarith

private lemma coeff_X_pow_mul_eq (k : ℕ) (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ k * f) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with hk
  · rw [Finset.sum_eq_single (k, n - k)]
    · rw [PowerSeries.coeff_X_pow, if_pos rfl, one_mul]
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have hne1 : p.1 ≠ k := fun h => hne (Prod.ext h (by omega))
      rw [PowerSeries.coeff_X_pow, if_neg hne1, zero_mul]
    · intro hnot; exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega
  · apply Finset.sum_eq_zero
    intro p hp; rw [Finset.mem_antidiagonal] at hp
    rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]

private lemma A271913_gf :
    (PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 3 *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A271913 (n + 1) : ℤ)) =
      4 * PowerSeries.X *
        (PowerSeries.X ^ 10 - PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 5 +
          4 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 2 -
          9 * PowerSeries.X - 4) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A271913 (n + 1) : ℤ))
  have hlhs : (PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 3 * F =
      -F + PowerSeries.C 2 * (PowerSeries.X ^ 1 * F) -
        PowerSeries.C 2 * (PowerSeries.X ^ 3 * F) + PowerSeries.X ^ 4 * F := by
    have h2 : PowerSeries.C (2 : ℤ) = (2 : PowerSeries ℤ) := rfl
    rw [h2, pow_one]; ring
  have hrhs : 4 * (PowerSeries.X : PowerSeries ℤ) *
        (PowerSeries.X ^ 10 - PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 5 +
          4 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 2 -
          9 * PowerSeries.X - 4) =
      PowerSeries.C 4 * PowerSeries.X ^ 11 - PowerSeries.C 4 * PowerSeries.X ^ 9 +
      PowerSeries.C 8 * PowerSeries.X ^ 7 + PowerSeries.C 4 * PowerSeries.X ^ 6 +
      PowerSeries.C 16 * PowerSeries.X ^ 5 + PowerSeries.C 16 * PowerSeries.X ^ 4 -
      PowerSeries.C 12 * PowerSeries.X ^ 3 - PowerSeries.C 36 * PowerSeries.X ^ 2 -
      PowerSeries.C 16 * PowerSeries.X := by
    have h4 : PowerSeries.C (4 : ℤ) = (4 : PowerSeries ℤ) := rfl
    have h8 : PowerSeries.C (8 : ℤ) = (8 : PowerSeries ℤ) := rfl
    have h12 : PowerSeries.C (12 : ℤ) = (12 : PowerSeries ℤ) := rfl
    have h16 : PowerSeries.C (16 : ℤ) = (16 : PowerSeries ℤ) := rfl
    have h36 : PowerSeries.C (36 : ℤ) = (36 : PowerSeries ℤ) := rfl
    rw [h4, h8, h12, h16, h36]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨_, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := A271913_small
  have h13 : A271913 13 = 1464 := by
    have hc := A271913_closed 13 (by omega)
    have ho : ¬ Even 13 := by decide
    rw [if_neg ho] at hc; omega
  by_cases hn12 : n ≤ 12
  · interval_cases n <;> simp [F, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 9 by omega, show n ≠ 11 by omega,
      show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
      ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hrec := A271913_rec (n + 1) (by omega)
    simp only [show n + 1 - 1 = n by omega, show n + 1 - 3 = n - 2 by omega,
      show n + 1 - 4 = n - 3 by omega, show n - 1 + 1 = n by omega,
      show n - 3 + 1 = n - 2 by omega, show n - 4 + 1 = n - 3 by omega] at hrec ⊢
    linarith

end OMA.P_oeis_a271913

theorem OMA.solution : type_of% @OMA.S_oeis_a271913.main :=
  ⟨OMA.P_oeis_a271913.A271913_closed, OMA.P_oeis_a271913.A271913_rec, OMA.P_oeis_a271913.A271913_gf⟩
