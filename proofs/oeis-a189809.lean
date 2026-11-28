import OMAStatements.S_oeis_a189809
import Mathlib.Tactic

namespace OMA.P_oeis_a189809

open OMA.S_oeis_a189809

/-! ### Part 1: Canonical lex-ordered triples and span decomposition -/

private def ptLt {m : ℕ} (p q : Fin 5 × Fin m) : Prop :=
  p.2.1 < q.2.1 ∨ (p.2.1 = q.2.1 ∧ p.1.1 < q.1.1)

private instance {m : ℕ} (p q : Fin 5 × Fin m) : Decidable (ptLt p q) := by
  unfold ptLt; infer_instance

private lemma ptLt_trans {m : ℕ} {p q r : Fin 5 × Fin m}
    (h1 : ptLt p q) (h2 : ptLt q r) : ptLt p r := by
  unfold ptLt at *; omega

private lemma ptLt_irrefl {m : ℕ} (p : Fin 5 × Fin m) : ¬ ptLt p p := by
  unfold ptLt; omega

private lemma ptLt_ne {m : ℕ} {p q : Fin 5 × Fin m} (h : ptLt p q) : p ≠ q := by
  intro heq; subst heq; exact ptLt_irrefl p h

private lemma ptLt_trichotomy {m : ℕ} (p q : Fin 5 × Fin m) :
    ptLt p q ∨ p = q ∨ ptLt q p := by
  rcases lt_trichotomy p.2.1 q.2.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy p.1.1 q.1.1 with h1 | h1 | h1
    · exact Or.inl (Or.inr ⟨h, h1⟩)
    · exact Or.inr (Or.inl (Prod.ext (Fin.ext h1) (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h1⟩))
  · exact Or.inr (Or.inr (Or.inl h))

private lemma isRightTriple_symm12 {p q r : ℤ × ℤ}
    (h : IsRightTriple p q r) : IsRightTriple q p r := by
  unfold IsRightTriple at *
  refine ⟨?_, ?_⟩
  · intro heq; apply h.1; linear_combination -heq
  · rcases h.2 with h1 | h2 | h3
    · right; left; linear_combination h1
    · left; linear_combination h2
    · right; right; linear_combination h3

private lemma isRightTriple_symm23 {p q r : ℤ × ℤ}
    (h : IsRightTriple p q r) : IsRightTriple p r q := by
  unfold IsRightTriple at *
  refine ⟨?_, ?_⟩
  · intro heq; apply h.1; linear_combination -heq
  · rcases h.2 with h1 | h2 | h3
    · left; linear_combination h1
    · right; right; linear_combination h2
    · right; left; linear_combination h3

private lemma isRightTriple_perm {p q r p' q' r' : ℤ × ℤ}
    (h : IsRightTriple p q r)
    (hset : ({p, q, r} : Finset (ℤ × ℤ)) = {p', q', r'})
    (hnd : p' ≠ q' ∧ q' ≠ r' ∧ p' ≠ r') :
    IsRightTriple p' q' r' := by
  have hp' : p' ∈ ({p, q, r} : Finset (ℤ × ℤ)) := by rw [hset]; simp
  have hq' : q' ∈ ({p, q, r} : Finset (ℤ × ℤ)) := by rw [hset]; simp
  have hr' : r' ∈ ({p, q, r} : Finset (ℤ × ℤ)) := by rw [hset]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp' hq' hr'
  rcases hp' with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl <;>
    rcases hr' with rfl | rfl | rfl
  all_goals try (exfalso; tauto)
  · exact h
  · exact isRightTriple_symm23 h
  · exact isRightTriple_symm12 h
  · exact isRightTriple_symm23 (isRightTriple_symm12 h)
  · exact isRightTriple_symm12 (isRightTriple_symm23 h)
  · exact isRightTriple_symm12 (isRightTriple_symm23 (isRightTriple_symm12 h))

private def isRightTripFin {m : ℕ} (p q r : Fin 5 × Fin m) : Prop :=
  ptLt p q ∧ ptLt q r ∧
  IsRightTriple (p.1.1, p.2.1) (q.1.1, q.2.1) (r.1.1, r.2.1)

private instance {m : ℕ} (p q r : Fin 5 × Fin m) : Decidable (isRightTripFin p q r) := by
  unfold isRightTripFin IsRightTriple; infer_instance

private lemma A189809_eq_card_ordered (n : ℕ) :
    A189809 n =
      (Finset.univ.filter (fun t : (Fin 5 × Fin (n + 1)) × (Fin 5 × Fin (n + 1)) × (Fin 5 × Fin (n + 1)) =>
        isRightTripFin t.1 t.2.1 t.2.2)).card := by
  classical
  unfold A189809
  symm
  refine Finset.card_bij (fun t _ => ({t.1, t.2.1, t.2.2} : Finset (Fin 5 × Fin (n + 1)))) ?_ ?_ ?_
  · rintro ⟨p, q, r⟩ ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rcases ht with ⟨hpq, hqr, hrt⟩
    have hpr : ptLt p r := ptLt_trans hpq hqr
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    refine ⟨?_, p, by simp, q, by simp, r, by simp, rfl, hrt⟩
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
    rcases hS with ⟨hcard, p, _, q, _, r, _, hSeq, hrt⟩
    have hnd : p ≠ q ∧ q ≠ r ∧ p ≠ r := by
      refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> subst heq <;> subst hSeq
      · have : ({p, p, r} : Finset (Fin 5 × Fin (n + 1))).card ≤ 2 := by
          rw [Finset.insert_eq_of_mem (by simp)]; exact Finset.card_le_two
        omega
      · have : ({p, q, q} : Finset (Fin 5 × Fin (n + 1))).card ≤ 2 := by
          rw [show ({p, q, q} : Finset (Fin 5 × Fin (n + 1))) = {p, q} by ext x; simp]; exact Finset.card_le_two
        omega
      · have : ({p, q, p} : Finset (Fin 5 × Fin (n + 1))).card ≤ 2 := by
          rw [show ({p, q, p} : Finset (Fin 5 × Fin (n + 1))) = {p, q} by ext x; simp; tauto]; exact Finset.card_le_two
        omega
    have hsort : ∃ a b c : Fin 5 × Fin (n + 1), ptLt a b ∧ ptLt b c ∧
        ({a, b, c} : Finset (Fin 5 × Fin (n + 1))) = {p, q, r} := by
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
      have := congrArg (Finset.image (fun x : Fin 5 × Fin (n + 1) => ((x.1.1 : ℤ), (x.2.1 : ℤ)))) habc.symm
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
    exact ⟨hab, hbc, isRightTriple_perm hrt hmap hnd_z⟩

/-- Canonical span-`w` ordered right triangles: `x_1 = 0`, `0 ≤ x_2 ≤ w`, `x_3 = w`. -/
private def isSpanRight (w : ℕ) (t : Fin 5 × (Fin 5 × ℕ) × Fin 5) : Prop :=
  t.2.1.2 ≤ w ∧
  (0 < t.2.1.2 ∨ (0 = t.2.1.2 ∧ t.1.1 < t.2.1.1.1)) ∧
  (t.2.1.2 < w ∨ (t.2.1.2 = w ∧ t.2.1.1.1 < t.2.2.1)) ∧
  IsRightTriple (t.1.1, 0) (t.2.1.1.1, t.2.1.2) (t.2.2.1, w)

private instance (w : ℕ) (t : Fin 5 × (Fin 5 × ℕ) × Fin 5) :
    Decidable (isSpanRight w t) := by
  unfold isSpanRight IsRightTriple; infer_instance

private def spanSpace (w : ℕ) : Finset (Fin 5 × (Fin 5 × ℕ) × Fin 5) :=
  (Finset.univ : Finset (Fin 5)) ×ˢ
    (((Finset.univ : Finset (Fin 5)) ×ˢ Finset.range (w + 1)) ×ˢ (Finset.univ : Finset (Fin 5)))

private def spanCount (w : ℕ) : ℕ :=
  ((spanSpace w).filter (isSpanRight w)).card

private lemma mem_spanSpace {w : ℕ} {t : Fin 5 × (Fin 5 × ℕ) × Fin 5} :
    t ∈ spanSpace w ↔ t.2.1.2 ≤ w := by
  simp only [spanSpace, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and, and_true]
  omega

private lemma A189809_eq_sum_spanCount (n : ℕ) :
    A189809 n = ∑ w ∈ Finset.range (n + 1), (n + 1 - w) * spanCount w := by
  rw [A189809_eq_card_ordered]
  have hsum : ∑ w ∈ Finset.range (n + 1), (n + 1 - w) * spanCount w =
      ((Finset.range (n + 1)).sigma (fun w =>
        (Finset.range (n + 1 - w)) ×ˢ ((spanSpace w).filter (isSpanRight w)))).card := by
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
    rcases ht with ⟨hpq, hqr, hrt⟩
    unfold ptLt at hpq hqr
    have hpx := p.2.isLt
    have hqx := q.2.isLt
    have hrx := r.2.isLt
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product, Finset.mem_filter,
      mem_spanSpace, isSpanRight]
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rcases hpq with h | ⟨h1, h2⟩
      · left; omega
      · right; exact ⟨by omega, h2⟩
    · rcases hqr with h | ⟨h1, h2⟩
      · left; omega
      · right; exact ⟨by omega, h2⟩
    · unfold IsRightTriple at hrt ⊢
      have h1 : ((q.2.1 - p.2.1 : ℕ) : ℤ) = (q.2.1 : ℤ) - (p.2.1 : ℤ) := Nat.cast_sub (by omega)
      have h2 : ((r.2.1 - p.2.1 : ℕ) : ℤ) = (r.2.1 : ℤ) - (p.2.1 : ℤ) := Nat.cast_sub (by omega)
      rw [h1, h2]
      refine ⟨?_, ?_⟩
      · intro heq; apply hrt.1; linear_combination heq
      · rcases hrt.2 with hc | hc | hc
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
      mem_spanSpace, isSpanRight] at hmem
    rcases hmem with ⟨hw, hx0, hdx, _, hlt1, hlt2, hrt⟩
    let p : Fin 5 × Fin (n + 1) := (y1, ⟨x0, by omega⟩)
    let q : Fin 5 × Fin (n + 1) := (y2, ⟨x0 + dx, by omega⟩)
    let r : Fin 5 × Fin (n + 1) := (y3, ⟨x0 + w, by omega⟩)
    refine ⟨(p, q, r), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · unfold ptLt; rcases hlt1 with h | ⟨h1, h2⟩
        · left; simp only [p, q]; omega
        · right; simp only [p, q]; exact ⟨by omega, h2⟩
      · unfold ptLt; rcases hlt2 with h | ⟨h1, h2⟩
        · left; simp only [q, r]; omega
        · right; simp only [q, r]; exact ⟨by omega, h2⟩
      · unfold IsRightTriple at hrt ⊢
        simp only [p, q, r]
        push_cast
        refine ⟨?_, ?_⟩
        · intro heq; apply hrt.1; linear_combination heq
        · rcases hrt.2 with hc | hc | hc
          · left; linear_combination hc
          · right; left; linear_combination hc
          · right; right; linear_combination hc
    · refine Sigma.ext (by simp only [p, r]; omega) (heq_of_eq ?_)
      simp only [p, q, r, Nat.add_sub_cancel_left]

/-! ### Part 2: Exact values of `spanCount w` -/

private lemma spanCount_eq_sum (w : ℕ) :
    spanCount w = ∑ dx ∈ Finset.range (w + 1),
      (((Finset.univ : Finset (Fin 5)) ×ˢ
        ((Finset.univ : Finset (Fin 5)) ×ˢ (Finset.univ : Finset (Fin 5)))).filter
        (fun p => isSpanRight w (p.1, (p.2.1, dx), p.2.2))).card := by
  unfold spanCount spanSpace
  rw [← Finset.card_sigma]
  refine Finset.card_bij
    (fun t _ => ⟨t.2.1.2, (t.1, (t.2.1.1, t.2.2))⟩) ?_ ?_ ?_
  · rintro ⟨y1, ⟨y2, dx⟩, y3⟩ ht
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_range,
      true_and, and_true] at ht
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    exact ht
  · rintro ⟨a1, ⟨b1, d1⟩, c1⟩ _ ⟨a2, ⟨b2, d2⟩, c2⟩ _ h
    have hd : d1 = d2 := congrArg Sigma.fst h
    have h2 : (a1, (b1, c1)) = (a2, (b2, c2)) := eq_of_heq (Sigma.ext_iff.mp h).2
    simp only [Prod.mk.injEq] at h2
    rcases h2 with ⟨rfl, rfl, rfl⟩; subst hd; rfl
  · rintro ⟨dx, ⟨y1, ⟨y2, y3⟩⟩⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and] at h
    refine ⟨(y1, (y2, dx), y3), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_range,
      true_and, and_true]
    exact h

private lemma spanCount_small1 :
    spanCount 0 = 0 ∧ spanCount 1 = 46 ∧ spanCount 2 = 66 ∧
    spanCount 3 = 72 ∧ spanCount 4 = 70 ∧ spanCount 5 = 76 ∧
    spanCount 6 = 52 ∧ spanCount 7 = 64 ∧ spanCount 8 = 50 := by
  simp only [spanCount_eq_sum]
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

private lemma spanCount_9 : spanCount 9 = 48 := by rw [spanCount_eq_sum]; decide
private lemma spanCount_10 : spanCount 10 = 52 := by rw [spanCount_eq_sum]; decide
private lemma spanCount_11 : spanCount 11 = 40 := by rw [spanCount_eq_sum]; decide
private lemma spanCount_12 : spanCount 12 = 40 := by rw [spanCount_eq_sum]; decide
private lemma spanCount_13 : spanCount 13 = 48 := by rw [spanCount_eq_sum]; decide
private lemma spanCount_14 : spanCount 14 = 40 := by rw [spanCount_eq_sum]; decide
private lemma spanCount_15 : spanCount 15 = 40 := by rw [spanCount_eq_sum]; decide
private lemma spanCount_16 : spanCount 16 = 40 := by rw [spanCount_eq_sum]; decide
private lemma spanCount_17 : spanCount 17 = 44 := by rw [spanCount_eq_sum]; decide

private lemma spanCount_small2 :
    spanCount 9 = 48 ∧ spanCount 10 = 52 ∧ spanCount 11 = 40 ∧
    spanCount 12 = 40 ∧ spanCount 13 = 48 ∧ spanCount 14 = 40 ∧
    spanCount 15 = 40 ∧ spanCount 16 = 40 ∧ spanCount 17 = 44 :=
  ⟨spanCount_9, spanCount_10, spanCount_11, spanCount_12,
   spanCount_13, spanCount_14, spanCount_15, spanCount_16, spanCount_17⟩

private lemma spanCount_ge18 (w : ℕ) (hw : 18 ≤ w) : spanCount w = 40 := by
  have hclass : ∀ t : Fin 5 × (Fin 5 × ℕ) × Fin 5,
      isSpanRight w t ↔
        (t.2.1.2 = 0 ∧ t.1.1 < t.2.1.1.1 ∧ (t.2.2 = t.1 ∨ t.2.2 = t.2.1.1)) ∨
        (t.2.1.2 = w ∧ t.2.1.1.1 < t.2.2.1 ∧ (t.1 = t.2.1.1 ∨ t.1 = t.2.2)) := by
    rintro ⟨y1, ⟨y2, dx⟩, y3⟩
    constructor
    · rintro ⟨hdx_le, hlt1, hlt2, hnc, hdot⟩
      dsimp only at hdx_le hlt1 hlt2 hnc hdot
      have hy1 := y1.isLt; have hy2 := y2.isLt; have hy3 := y3.isLt
      have hdx0w : dx = 0 ∨ dx = w := by
        rcases hdot with h1 | h2 | h3
        · left
          have hbd : -16 ≤ ((y2.1 : ℤ) - (y1.1 : ℤ)) * ((y3.1 : ℤ) - (y1.1 : ℤ)) := by nlinarith
          have hprod : (dx : ℤ) * (w : ℤ) ≤ 16 := by linarith
          by_contra hne
          have hpos : (1 : ℤ) ≤ (dx : ℤ) := by omega
          nlinarith
        · by_contra hne
          push Not at hne
          have h1 : (1 : ℤ) ≤ (dx : ℤ) := by omega
          have h2' : (1 : ℤ) ≤ (w : ℤ) - (dx : ℤ) := by omega
          have hprod : (dx : ℤ) * ((w : ℤ) - (dx : ℤ)) ≥ (w : ℤ) - 1 := by nlinarith
          have hbd : ((y1.1 : ℤ) - (y2.1 : ℤ)) * ((y3.1 : ℤ) - (y2.1 : ℤ)) ≤ 16 := by nlinarith
          linarith
        · right
          have hbd : -16 ≤ ((y1.1 : ℤ) - (y3.1 : ℤ)) * ((y2.1 : ℤ) - (y3.1 : ℤ)) := by nlinarith
          have hprod : (w : ℤ) * ((w : ℤ) - (dx : ℤ)) ≤ 16 := by linarith
          by_contra hne
          have hpos : (1 : ℤ) ≤ (w : ℤ) - (dx : ℤ) := by omega
          nlinarith
      rcases hdx0w with h0 | hw'
      · left
        have hy12 : y1.1 < y2.1 := by rw [h0] at hlt1; rcases hlt1 with h | ⟨_, h⟩ <;> omega
        refine ⟨h0, hy12, ?_⟩
        rw [h0] at hdot
        push_cast at hdot
        rcases hdot with h1 | h2 | h3
        · left
          have hmul : ((y2.1 : ℤ) - (y1.1 : ℤ)) * ((y3.1 : ℤ) - (y1.1 : ℤ)) = 0 := by linarith
          rcases mul_eq_zero.mp hmul with h | h
          · omega
          · exact Fin.ext (by dsimp; omega)
        · right
          have hmul : ((y1.1 : ℤ) - (y2.1 : ℤ)) * ((y3.1 : ℤ) - (y2.1 : ℤ)) = 0 := by linarith
          rcases mul_eq_zero.mp hmul with h | h
          · omega
          · exact Fin.ext (by dsimp; omega)
        · exfalso
          have hbd : -16 ≤ ((y1.1 : ℤ) - (y3.1 : ℤ)) * ((y2.1 : ℤ) - (y3.1 : ℤ)) := by nlinarith
          nlinarith
      · right
        have hy23 : y2.1 < y3.1 := by rw [hw'] at hlt2; rcases hlt2 with h | ⟨_, h⟩ <;> omega
        refine ⟨hw', hy23, ?_⟩
        rw [hw'] at hdot
        rcases hdot with h1 | h2 | h3
        · exfalso
          have hbd : -16 ≤ ((y2.1 : ℤ) - (y1.1 : ℤ)) * ((y3.1 : ℤ) - (y1.1 : ℤ)) := by nlinarith
          nlinarith
        · left
          have hmul : ((y1.1 : ℤ) - (y2.1 : ℤ)) * ((y3.1 : ℤ) - (y2.1 : ℤ)) = 0 := by linarith
          rcases mul_eq_zero.mp hmul with h | h
          · exact Fin.ext (by dsimp; omega)
          · omega
        · right
          have hmul : ((y1.1 : ℤ) - (y3.1 : ℤ)) * ((y2.1 : ℤ) - (y3.1 : ℤ)) = 0 := by linarith
          rcases mul_eq_zero.mp hmul with h | h
          · exact Fin.ext (by dsimp; omega)
          · omega
    · rintro (⟨h0, hy12, hy3 | hy3⟩ | ⟨hw', hy23, hy1 | hy1⟩)
      · dsimp only at h0 hy12 hy3
        unfold isSpanRight IsRightTriple
        dsimp only
        rw [h0, hy3]
        refine ⟨by omega, Or.inr ⟨rfl, hy12⟩, Or.inl (by omega), ?_, Or.inl (by push_cast; ring)⟩
        intro heq
        have h0' : ((y2.1 : ℤ) - (y1.1 : ℤ)) * (w : ℤ) = 0 := by push_cast at heq; linear_combination heq
        rcases mul_eq_zero.mp h0' with h | h <;> omega
      · dsimp only at h0 hy12 hy3
        unfold isSpanRight IsRightTriple
        dsimp only
        rw [h0, hy3]
        refine ⟨by omega, Or.inr ⟨rfl, hy12⟩, Or.inl (by omega), ?_, Or.inr (Or.inl (by push_cast; ring))⟩
        intro heq
        have h0' : ((y2.1 : ℤ) - (y1.1 : ℤ)) * (w : ℤ) = 0 := by push_cast at heq; linear_combination heq
        rcases mul_eq_zero.mp h0' with h | h <;> omega
      · dsimp only at hw' hy23 hy1
        unfold isSpanRight IsRightTriple
        dsimp only
        rw [hw', hy1]
        refine ⟨by omega, Or.inl (by omega), Or.inr ⟨rfl, hy23⟩, ?_, Or.inr (Or.inl (by ring))⟩
        intro heq
        have h0' : (w : ℤ) * ((y3.1 : ℤ) - (y2.1 : ℤ)) = 0 := by linear_combination -heq
        rcases mul_eq_zero.mp h0' with h | h <;> omega
      · dsimp only at hw' hy23 hy1
        unfold isSpanRight IsRightTriple
        dsimp only
        rw [hw', hy1]
        refine ⟨by omega, Or.inl (by omega), Or.inr ⟨rfl, hy23⟩, ?_, Or.inr (Or.inr (by ring))⟩
        intro heq
        have h0' : (w : ℤ) * ((y3.1 : ℤ) - (y2.1 : ℤ)) = 0 := by linear_combination -heq
        rcases mul_eq_zero.mp h0' with h | h <;> omega
  let S_L : Finset (Fin 5 × (Fin 5 × ℕ) × Fin 5) :=
    (Finset.univ.filter (fun p : Fin 5 × Fin 5 × Fin 5 =>
      p.1.1 < p.2.1.1 ∧ (p.2.2 = p.1 ∨ p.2.2 = p.2.1))).image
      (fun p => (p.1, (p.2.1, 0), p.2.2))
  let S_R : Finset (Fin 5 × (Fin 5 × ℕ) × Fin 5) :=
    (Finset.univ.filter (fun p : Fin 5 × Fin 5 × Fin 5 =>
      p.2.1.1 < p.2.2.1 ∧ (p.1 = p.2.1 ∨ p.1 = p.2.2))).image
      (fun p => (p.1, (p.2.1, w), p.2.2))
  have hset : (spanSpace w).filter (isSpanRight w) = S_L ∪ S_R := by
    ext ⟨a, ⟨b, d⟩, c⟩
    simp only [Finset.mem_filter, mem_spanSpace, hclass, Finset.mem_union,
      S_L, S_R, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨rfl, hlt, hc⟩ | ⟨rfl, hlt, ha⟩⟩
      · left; exact ⟨(a, b, c), ⟨hlt, hc⟩, rfl⟩
      · right; exact ⟨(a, b, c), ⟨hlt, ha⟩, rfl⟩
    · rintro (⟨⟨a', b', c'⟩, ⟨hlt, hc⟩, heq⟩ | ⟨⟨a', b', c'⟩, ⟨hlt, ha⟩, heq⟩)
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, ⟨rfl, rfl⟩, rfl⟩
        exact ⟨by omega, Or.inl ⟨rfl, hlt, hc⟩⟩
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, ⟨rfl, rfl⟩, rfl⟩
        exact ⟨by omega, Or.inr ⟨rfl, hlt, ha⟩⟩
  have hdisj : Disjoint S_L S_R := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    simp only [S_L, S_R, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
    rcases ht1 with ⟨p1, _, rfl⟩
    rcases ht2 with ⟨p2, _, h⟩
    have := congrArg (fun x => x.2.1.2) h
    dsimp at this; omega
  have hcardL : S_L.card = 20 := by
    rw [Finset.card_image_of_injective]
    · decide
    · intro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2.1.1 h.2.2)
  have hcardR : S_R.card = 20 := by
    rw [Finset.card_image_of_injective]
    · decide
    · intro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2.1.1 h.2.2)
  unfold spanCount
  rw [hset, Finset.card_union_of_disjoint hdisj, hcardL, hcardR]

/-! ### Part 3: Third difference identity and rational generating function -/

private lemma A189809_step (n : ℕ) :
    A189809 (n + 1) = A189809 n + ∑ w ∈ Finset.range (n + 2), spanCount w := by
  rw [A189809_eq_sum_spanCount (n + 1), A189809_eq_sum_spanCount n]
  conv_lhs => rw [Finset.sum_range_succ]
  conv_rhs => arg 2; rw [Finset.sum_range_succ]
  have h0 : (n + 1 + 1 - (n + 1)) * spanCount (n + 1) = spanCount (n + 1) := by simp
  rw [h0, ← add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_range] at hw
  have h1 : n + 1 + 1 - w = (n + 1 - w) + 1 := by omega
  rw [h1]; ring

private lemma A189809_third_diff (n : ℕ) (hn : 3 ≤ n) :
    (A189809 n : ℤ) - 3 * A189809 (n - 1) + 3 * A189809 (n - 2) - A189809 (n - 3) =
      (spanCount n : ℤ) - spanCount (n - 1) := by
  have h1 := congrArg (Nat.cast (R := ℤ)) (A189809_step (n - 1))
  have h2 := congrArg (Nat.cast (R := ℤ)) (A189809_step (n - 2))
  have h3 := congrArg (Nat.cast (R := ℤ)) (A189809_step (n - 3))
  simp only [show n - 1 + 1 = n by omega, show n - 2 + 1 = n - 1 by omega,
    show n - 3 + 1 = n - 2 by omega, show n - 1 + 2 = n + 1 by omega,
    show n - 2 + 2 = n by omega, show n - 3 + 2 = n - 1 by omega] at h1 h2 h3
  push_cast at h1 h2 h3
  have hs1 : (∑ w ∈ Finset.range (n + 1), (spanCount w : ℤ)) =
      (∑ w ∈ Finset.range n, (spanCount w : ℤ)) + spanCount n := by
    rw [Finset.sum_range_succ]
  have hs2 : (∑ w ∈ Finset.range n, (spanCount w : ℤ)) =
      (∑ w ∈ Finset.range (n - 1), (spanCount w : ℤ)) + spanCount (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
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

private lemma A189809_gf :
    (1 - PowerSeries.X) ^ 3 *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A189809 n : ℤ)) =
      2 * PowerSeries.X *
        (23 + 10 * PowerSeries.X + 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 +
          3 * PowerSeries.X ^ 4 - 12 * PowerSeries.X ^ 5 + 6 * PowerSeries.X ^ 6 -
          7 * PowerSeries.X ^ 7 - PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 9 -
          6 * PowerSeries.X ^ 10 + 4 * PowerSeries.X ^ 12 - 4 * PowerSeries.X ^ 13 +
          2 * PowerSeries.X ^ 16 - 2 * PowerSeries.X ^ 17) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A189809 n : ℤ))
  have hlhs : (1 - PowerSeries.X) ^ 3 * F =
      F - PowerSeries.C 3 * (PowerSeries.X ^ 1 * F) +
        PowerSeries.C 3 * (PowerSeries.X ^ 2 * F) - PowerSeries.X ^ 3 * F := by
    have h3 : PowerSeries.C (3 : ℤ) = (3 : PowerSeries ℤ) := rfl
    rw [h3, pow_one]; ring
  have hrhs : 2 * (PowerSeries.X : PowerSeries ℤ) *
        (23 + 10 * PowerSeries.X + 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 +
          3 * PowerSeries.X ^ 4 - 12 * PowerSeries.X ^ 5 + 6 * PowerSeries.X ^ 6 -
          7 * PowerSeries.X ^ 7 - PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 9 -
          6 * PowerSeries.X ^ 10 + 4 * PowerSeries.X ^ 12 - 4 * PowerSeries.X ^ 13 +
          2 * PowerSeries.X ^ 16 - 2 * PowerSeries.X ^ 17) =
      PowerSeries.C 46 * PowerSeries.X + PowerSeries.C 20 * PowerSeries.X ^ 2 +
      PowerSeries.C 6 * PowerSeries.X ^ 3 - PowerSeries.C 2 * PowerSeries.X ^ 4 +
      PowerSeries.C 6 * PowerSeries.X ^ 5 - PowerSeries.C 24 * PowerSeries.X ^ 6 +
      PowerSeries.C 12 * PowerSeries.X ^ 7 - PowerSeries.C 14 * PowerSeries.X ^ 8 -
      PowerSeries.C 2 * PowerSeries.X ^ 9 + PowerSeries.C 4 * PowerSeries.X ^ 10 -
      PowerSeries.C 12 * PowerSeries.X ^ 11 + PowerSeries.C 8 * PowerSeries.X ^ 13 -
      PowerSeries.C 8 * PowerSeries.X ^ 14 + PowerSeries.C 4 * PowerSeries.X ^ 17 -
      PowerSeries.C 4 * PowerSeries.X ^ 18 := by
    have h2 : PowerSeries.C (2 : ℤ) = (2 : PowerSeries ℤ) := rfl
    have h4 : PowerSeries.C (4 : ℤ) = (4 : PowerSeries ℤ) := rfl
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h8 : PowerSeries.C (8 : ℤ) = (8 : PowerSeries ℤ) := rfl
    have h12 : PowerSeries.C (12 : ℤ) = (12 : PowerSeries ℤ) := rfl
    have h14 : PowerSeries.C (14 : ℤ) = (14 : PowerSeries ℤ) := rfl
    have h20 : PowerSeries.C (20 : ℤ) = (20 : PowerSeries ℤ) := rfl
    have h24 : PowerSeries.C (24 : ℤ) = (24 : PowerSeries ℤ) := rfl
    have h46 : PowerSeries.C (46 : ℤ) = (46 : PowerSeries ℤ) := rfl
    rw [h2, h4, h6, h8, h12, h14, h20, h24, h46]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := spanCount_small1
  obtain ⟨h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := spanCount_small2
  have h18 : spanCount 18 = 40 := spanCount_ge18 18 (le_refl _)
  have ha0 : A189809 0 = 0 := by rw [A189809_eq_sum_spanCount 0, Finset.sum_range_one]; simp [h0]
  have ha1 : A189809 1 = 46 := by
    rw [A189809_step 0, ha0, Finset.sum_range_succ, Finset.sum_range_one]; simp [h0, h1]
  have ha2 : A189809 2 = 158 := by
    rw [A189809_step 1, ha1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp [h0, h1, h2]
  by_cases hn3 : n < 3
  · interval_cases n <;> simp [F, ha1, ha2]
  · by_cases hn18 : n ≤ 18
    · have htd := A189809_third_diff n (by omega)
      interval_cases n
      all_goals
        simp only [F, PowerSeries.coeff_mk, ↓reduceIte, mul_zero, sub_zero, add_zero,
          Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceLeDiff,
          OfNat.ofNat_ne_zero, Nat.one_ne_zero] at htd ⊢
        try simp only [ha0, Nat.cast_zero] at htd
        linarith [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
    · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
        show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
        show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega,
        show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 13 by omega, show n ≠ 14 by omega,
        show n ≠ 17 by omega, show n ≠ 18 by omega,
        show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
        ↓reduceIte, mul_zero, sub_zero, add_zero]
      have htd := A189809_third_diff n (by omega)
      rw [spanCount_ge18 n (by omega), spanCount_ge18 (n - 1) (by omega)] at htd
      linarith

end OMA.P_oeis_a189809

theorem OMA.solution : type_of% @OMA.S_oeis_a189809.main :=
  OMA.P_oeis_a189809.A189809_gf
