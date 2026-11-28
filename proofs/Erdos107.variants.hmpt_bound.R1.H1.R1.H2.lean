import OMAReductions.R_Erdos107_variants_hmpt_bound_R1_H1_R1

-- Step Erdos107.variants.hmpt_bound.R1.H1.R1.H2: hypothesis H2 of reduction Erdos107.variants.hmpt_bound.R1.H1.R1
-- Credit: @<handle>

/-!
# Positive-fraction Erdos-Szekeres theorem with exponential fraction (k >= 4)

Proof of `OMA.R_Erdos107_variants_hmpt_bound_R1_H1_R1.H2` with constant `A = 36`.
We shear the point set by a unit-determinant linear map to obtain distinct x-coordinates
without changing signed areas, apply the Erdos-Szekeres cups-caps theorem to `(4k+1)`-chains,
double-count via supersaturation over `2k` gaps to find an anchor chain with large product of
gap sizes, select `k` gaps of size at least `N / 2^(36k)`, and verify uniform orientation for
every transversal via an elementary polynomial identity.
-/

open Finset

namespace OMA.Erdos107HmptH2

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def orient (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def orientE (a b c : E2) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

def turn (up : Bool) (a b c : ℝ × ℝ) : Prop :=
  0 < (if up then (1 : ℝ) else -1) * orient a b c

def shear (t : ℝ) (p : E2) : ℝ × ℝ :=
  (p 0 + t * p 1, p 1)

lemma orient_shear (t : ℝ) (a b c : E2) :
    orient (shear t a) (shear t b) (shear t c) = orientE a b c := by
  unfold orient orientE shear
  ring

lemma exists_shear_injOn (X : Finset E2) :
    ∃ t : ℝ, Set.InjOn (fun p => (shear t p).1) (X : Set E2) := by
  classical
  let bad : Finset ℝ := (X ×ˢ X).image (fun pq => (pq.2 0 - pq.1 0) / (pq.1 1 - pq.2 1))
  obtain ⟨t, ht⟩ := bad.exists_notMem
  refine ⟨t, fun p hp q hq heq => ?_⟩
  have hpX : p ∈ X := hp
  have hqX : q ∈ X := hq
  by_cases h1 : p 1 = q 1
  · apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = q 0
      simp only [shear] at heq
      rw [h1] at heq
      linarith
    · exact h1
  · exfalso
    apply ht
    refine mem_image.mpr ⟨(p, q), mem_product.mpr ⟨hpX, hqX⟩, ?_⟩
    simp only [shear] at heq
    apply (div_eq_iff (sub_ne_zero.mpr h1)).mpr
    nlinarith only [heq]

lemma orient_ne_zero_in_shear (X : Finset E2)
    (hX : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, x ≠ y → y ≠ z → x ≠ z →
      ¬ Collinear ℝ ({x, y, z} : Set E2))
    (t : ℝ) :
    ∀ u ∈ X.image (shear t), ∀ v ∈ X.image (shear t), ∀ w ∈ X.image (shear t),
      u.1 < v.1 → v.1 < w.1 → orient u v w ≠ 0 := by
  intro u hu v hv w hw huv hvw h0
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hv
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hw
  have hab : a ≠ b := fun h => huv.ne (congrArg (fun p => (shear t p).1) h)
  have hbc : b ≠ c := fun h => hvw.ne (congrArg (fun p => (shear t p).1) h)
  have hac : a ≠ c := fun h => (huv.trans hvw).ne (congrArg (fun p => (shear t p).1) h)
  apply hX a ha b hb c hc hab hbc hac
  let r := ((shear t b).1 - (shear t a).1) / ((shear t c).1 - (shear t b).1)
  have hden : (shear t c).1 - (shear t b).1 ≠ 0 := sub_ne_zero.mpr hvw.ne'
  have hx : (shear t b).1 - (shear t a).1 = r * ((shear t c).1 - (shear t b).1) := by
    dsimp [r]
    rw [div_mul_cancel₀ _ hden]
  have hy : (shear t b).2 - (shear t a).2 = r * ((shear t c).2 - (shear t b).2) := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).mpr
    unfold orient at h0
    nlinarith only [h0]
  have hdiff : b - a = r • (c - b) := by
    apply PiLp.ext
    intro i
    fin_cases i
    · change b 0 - a 0 = r * (c 0 - b 0)
      simp only [shear] at hx hy
      linear_combination hx - t * hy
    · change b 1 - a 1 = r * (c 1 - b 1)
      simpa only [shear] using hy
  apply (collinear_iff_of_mem (show b ∈ ({a, b, c} : Set E2) by simp)).mpr
  refine ⟨c - b, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp
  · refine ⟨-r, ?_⟩
    rw [hp, neg_smul, vadd_eq_add]
    have := congrArg (fun z => -z + b) hdiff
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
  · rw [hp]; exact ⟨0, by simp⟩
  · rw [hp]; exact ⟨1, by simp [vadd_eq_add]⟩

lemma orient_id1 (a b c d : ℝ × ℝ) :
    (c.1 - b.1) * orient a b d =
      (d.1 - b.1) * orient a b c + (b.1 - a.1) * orient b c d := by
  unfold orient
  ring

lemma orient_id2 (a b c d : ℝ × ℝ) :
    (c.1 - b.1) * orient a c d =
      (d.1 - c.1) * orient a b c + (c.1 - a.1) * orient b c d := by
  unfold orient
  ring

lemma orient_gap_id (p1 a p2 b p3 : ℝ × ℝ) :
    (b.1 - a.1) * orient p1 p2 p3 =
      (p3.1 - p2.1) * (orient p1 a b + orient a p2 b) +
      (p2.1 - p1.1) * (orient a p2 b + orient a b p3) := by
  unfold orient
  ring

lemma turn_abd {up : Bool} {a b c d : ℝ × ℝ}
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (h1 : turn up a b c) (h2 : turn up b c d) : turn up a b d := by
  unfold turn at h1 h2 ⊢
  have hid := orient_id1 a b c d
  have hmul : (c.1 - b.1) * ((if up then (1 : ℝ) else -1) * orient a b d) =
      (d.1 - b.1) * ((if up then (1 : ℝ) else -1) * orient a b c) +
      (b.1 - a.1) * ((if up then (1 : ℝ) else -1) * orient b c d) := by
    calc (c.1 - b.1) * ((if up then (1 : ℝ) else -1) * orient a b d)
        = (if up then (1 : ℝ) else -1) * ((c.1 - b.1) * orient a b d) := by ring
      _ = (if up then (1 : ℝ) else -1) *
            ((d.1 - b.1) * orient a b c + (b.1 - a.1) * orient b c d) := by rw [hid]
      _ = _ := by ring
  have hpos : 0 < (c.1 - b.1) * ((if up then (1 : ℝ) else -1) * orient a b d) := by
    rw [hmul]
    nlinarith
  nlinarith

lemma turn_acd {up : Bool} {a b c d : ℝ × ℝ}
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (h1 : turn up a b c) (h2 : turn up b c d) : turn up a c d := by
  unfold turn at h1 h2 ⊢
  have hid := orient_id2 a b c d
  have hmul : (c.1 - b.1) * ((if up then (1 : ℝ) else -1) * orient a c d) =
      (d.1 - c.1) * ((if up then (1 : ℝ) else -1) * orient a b c) +
      (c.1 - a.1) * ((if up then (1 : ℝ) else -1) * orient b c d) := by
    calc (c.1 - b.1) * ((if up then (1 : ℝ) else -1) * orient a c d)
        = (if up then (1 : ℝ) else -1) * ((c.1 - b.1) * orient a c d) := by ring
      _ = (if up then (1 : ℝ) else -1) *
            ((d.1 - c.1) * orient a b c + (c.1 - a.1) * orient b c d) := by rw [hid]
      _ = _ := by ring
  have hpos : 0 < (c.1 - b.1) * ((if up then (1 : ℝ) else -1) * orient a c d) := by
    rw [hmul]
    nlinarith
  nlinarith

lemma turn_gap {up : Bool} {p1 a p2 b p3 : ℝ × ℝ}
    (h1 : p1.1 < a.1) (h2 : a.1 < p2.1) (h3 : p2.1 < b.1) (h4 : b.1 < p3.1)
    (ht1 : turn up p1 a b) (ht2 : turn up a p2 b) (ht3 : turn up a b p3) :
    turn up p1 p2 p3 := by
  unfold turn at ht1 ht2 ht3 ⊢
  have hid := orient_gap_id p1 a p2 b p3
  have hmul : (b.1 - a.1) * ((if up then (1 : ℝ) else -1) * orient p1 p2 p3) =
      (p3.1 - p2.1) * ((if up then (1 : ℝ) else -1) * orient p1 a b +
        (if up then (1 : ℝ) else -1) * orient a p2 b) +
      (p2.1 - p1.1) * ((if up then (1 : ℝ) else -1) * orient a p2 b +
        (if up then (1 : ℝ) else -1) * orient a b p3) := by
    calc (b.1 - a.1) * ((if up then (1 : ℝ) else -1) * orient p1 p2 p3)
        = (if up then (1 : ℝ) else -1) * ((b.1 - a.1) * orient p1 p2 p3) := by ring
      _ = (if up then (1 : ℝ) else -1) *
            ((p3.1 - p2.1) * (orient p1 a b + orient a p2 b) +
             (p2.1 - p1.1) * (orient a p2 b + orient a b p3)) := by rw [hid]
      _ = _ := by ring
  have hpos : 0 < (b.1 - a.1) * ((if up then (1 : ℝ) else -1) * orient p1 p2 p3) := by
    rw [hmul]
    nlinarith
  nlinarith

def IsChain (up : Bool) (U : Finset (ℝ × ℝ)) {k : ℕ} (e : Fin k → ℝ × ℝ) : Prop :=
  (∀ i, e i ∈ U) ∧ StrictMono (fun i => (e i).1) ∧
    ∀ i j l, i < j → j < l → turn up (e i) (e j) (e l)

lemma extend_right {U : Finset (ℝ × ℝ)} {r : ℕ} (hr : 2 ≤ r) {e : Fin r → ℝ × ℝ}
    (he : IsChain true U e) {q : ℝ × ℝ} (hqU : q ∈ U)
    (hx : (e ⟨r - 1, by omega⟩).1 < q.1)
    (ht : turn true (e ⟨r - 2, by omega⟩) (e ⟨r - 1, by omega⟩) q) :
    ∃ e' : Fin (r + 1) → ℝ × ℝ, IsChain true U e' := by
  let e' : Fin (r + 1) → ℝ × ℝ := fun i =>
    if h : i.val < r then e ⟨i.val, h⟩ else q
  have ht_last : ∀ i : Fin r, i.val < r - 1 → turn true (e i) (e ⟨r - 1, by omega⟩) q := by
    intro i hi
    by_cases h2 : i.val = r - 2
    · have : i = ⟨r - 2, by omega⟩ := Fin.ext h2
      rw [this]
      exact ht
    · have hilt : i < ⟨r - 2, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
      have hlt2 : (⟨r - 2, by omega⟩ : Fin r) < ⟨r - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
      exact turn_acd (he.2.1 hilt) (he.2.1 hlt2) hx (he.2.2 i _ _ hilt hlt2) ht
  refine ⟨e', ?_, ?_, ?_⟩
  · intro i
    dsimp [e']
    split_ifs with h
    · exact he.1 ⟨i.val, h⟩
    · exact hqU
  · intro i j hij
    have hijv : i.val < j.val := hij
    dsimp [e']
    split_ifs with hi hj hj
    · exact he.2.1 (Fin.mk_lt_mk.mpr hijv)
    · have hle : (⟨i.val, hi⟩ : Fin r) ≤ ⟨r - 1, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
      exact lt_of_le_of_lt (he.2.1.monotone hle) hx
    · exfalso; omega
    · exfalso; omega
  · intro i j l hij hjl
    have hijv : i.val < j.val := hij
    have hjlv : j.val < l.val := hjl
    have hi : i.val < r := by omega
    have hj : j.val < r := by omega
    by_cases hl : l.val < r
    · simp only [e', dif_pos hi, dif_pos hj, dif_pos hl]
      exact he.2.2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨l.val, hl⟩ (Fin.mk_lt_mk.mpr hijv) (Fin.mk_lt_mk.mpr hjlv)
    · simp only [e', dif_pos hi, dif_pos hj, dif_neg hl]
      by_cases hjlast : j.val = r - 1
      · have hj' : (⟨j.val, hj⟩ : Fin r) = ⟨r - 1, by omega⟩ := Fin.ext hjlast
        rw [hj']
        exact ht_last ⟨i.val, hi⟩ (by dsimp; omega)
      · have hij' : (⟨i.val, hi⟩ : Fin r) < ⟨j.val, hj⟩ := Fin.mk_lt_mk.mpr hijv
        have hjlt : (⟨j.val, hj⟩ : Fin r) < ⟨r - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
        exact turn_abd (he.2.1 hij') (he.2.1 hjlt) hx
          (he.2.2 _ _ _ hij' hjlt) (ht_last ⟨j.val, hj⟩ (by dsimp; omega))

lemma extend_left {U : Finset (ℝ × ℝ)} {s : ℕ} (hs : 2 ≤ s) {f : Fin s → ℝ × ℝ}
    (hf : IsChain false U f) {p : ℝ × ℝ} (hpU : p ∈ U)
    (hx : p.1 < (f ⟨0, by omega⟩).1)
    (ht : turn false p (f ⟨0, by omega⟩) (f ⟨1, by omega⟩)) :
    ∃ f' : Fin (s + 1) → ℝ × ℝ, IsChain false U f' := by
  let f' : Fin (s + 1) → ℝ × ℝ := fun i =>
    if h : i.val = 0 then p else f ⟨i.val - 1, by omega⟩
  have ht_first : ∀ l : Fin s, 0 < l.val → turn false p (f ⟨0, by omega⟩) (f l) := by
    intro l hl
    by_cases h1 : l.val = 1
    · have : l = ⟨1, by omega⟩ := Fin.ext h1
      rw [this]
      exact ht
    · have h01 : (⟨0, by omega⟩ : Fin s) < ⟨1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
      have h1l : (⟨1, by omega⟩ : Fin s) < l := Fin.mk_lt_mk.mpr (by omega)
      exact turn_abd hx (hf.2.1 h01) (hf.2.1 h1l) ht (hf.2.2 _ _ _ h01 h1l)
  refine ⟨f', ?_, ?_, ?_⟩
  · intro i
    dsimp [f']
    split_ifs with h
    · exact hpU
    · exact hf.1 ⟨i.val - 1, by omega⟩
  · intro i j hij
    have hijv : i.val < j.val := hij
    dsimp [f']
    split_ifs with hi hj hj
    · exfalso; omega
    · have hle : (⟨0, by omega⟩ : Fin s) ≤ ⟨j.val - 1, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
      exact lt_of_lt_of_le hx (hf.2.1.monotone hle)
    · exfalso; omega
    · exact hf.2.1 (Fin.mk_lt_mk.mpr (by omega))
  · intro i j l hij hjl
    have hijv : i.val < j.val := hij
    have hjlv : j.val < l.val := hjl
    have hj : j.val ≠ 0 := by omega
    have hl : l.val ≠ 0 := by omega
    by_cases hi : i.val = 0
    · simp only [f', dif_pos hi, dif_neg hj, dif_neg hl]
      by_cases hj1 : j.val = 1
      · have hj' : (⟨j.val - 1, by omega⟩ : Fin s) = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hj']
        exact ht_first ⟨l.val - 1, by omega⟩ (by dsimp; omega)
      · have h0j : (⟨0, by omega⟩ : Fin s) < ⟨j.val - 1, by omega⟩ :=
          Fin.mk_lt_mk.mpr (by omega)
        have hjl' : (⟨j.val - 1, by omega⟩ : Fin s) < ⟨l.val - 1, by omega⟩ :=
          Fin.mk_lt_mk.mpr (by omega)
        exact turn_acd hx (hf.2.1 h0j) (hf.2.1 hjl')
          (ht_first ⟨j.val - 1, by omega⟩ (by dsimp; omega)) (hf.2.2 _ _ _ h0j hjl')
    · simp only [f', dif_neg hi, dif_neg hj, dif_neg hl]
      exact hf.2.2 ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ ⟨l.val - 1, by omega⟩
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

lemma erdos_szekeres_cups_caps :
    ∀ n : ℕ, ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → r + s = n →
      ∀ U : Finset (ℝ × ℝ), Set.InjOn Prod.fst (U : Set (ℝ × ℝ)) →
        (∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0) →
        (r + s - 4).choose (r - 2) < U.card →
        (∃ e : Fin r → ℝ × ℝ, IsChain true U e) ∨ (∃ f : Fin s → ℝ × ℝ, IsChain false U f) := by
  intro n
  induction n with
  | zero => intro r s hr; omega
  | succ n ih =>
    intro r s hr hs hrs U hinj hgen hcard
    by_cases hr2 : r = 2
    · subst hr2
      have h2 : 1 < U.card := by simpa using hcard
      obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.mp h2
      have hne : p.1 ≠ q.1 := fun h => hpq (hinj hp hq h)
      left
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · refine ⟨![p, q], fun i => by fin_cases i <;> assumption, ?_, fun i j l hij hjl => by
          have := Fin.lt_def.mp hij; have := Fin.lt_def.mp hjl; omega⟩
        intro i j hij
        have hi0 : i = 0 := Fin.ext (by have := Fin.lt_def.mp hij; omega)
        have hj1 : j = 1 := Fin.ext (by have := Fin.lt_def.mp hij; omega)
        subst hi0; subst hj1; exact hlt
      · refine ⟨![q, p], fun i => by fin_cases i <;> assumption, ?_, fun i j l hij hjl => by
          have := Fin.lt_def.mp hij; have := Fin.lt_def.mp hjl; omega⟩
        intro i j hij
        have hi0 : i = 0 := Fin.ext (by have := Fin.lt_def.mp hij; omega)
        have hj1 : j = 1 := Fin.ext (by have := Fin.lt_def.mp hij; omega)
        subst hi0; subst hj1; exact hlt
    · by_cases hs2 : s = 2
      · subst hs2
        have hch : (r + 2 - 4).choose (r - 2) = 1 := by
          have : r + 2 - 4 = r - 2 := by omega
          rw [this, Nat.choose_self]
        have h2 : 1 < U.card := hch ▸ hcard
        obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.mp h2
        have hne : p.1 ≠ q.1 := fun h => hpq (hinj hp hq h)
        right
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · refine ⟨![p, q], fun i => by fin_cases i <;> assumption, ?_, fun i j l hij hjl => by
            have := Fin.lt_def.mp hij; have := Fin.lt_def.mp hjl; omega⟩
          intro i j hij
          have hi0 : i = 0 := Fin.ext (by have := Fin.lt_def.mp hij; omega)
          have hj1 : j = 1 := Fin.ext (by have := Fin.lt_def.mp hij; omega)
          subst hi0; subst hj1; exact hlt
        · refine ⟨![q, p], fun i => by fin_cases i <;> assumption, ?_, fun i j l hij hjl => by
            have := Fin.lt_def.mp hij; have := Fin.lt_def.mp hjl; omega⟩
          intro i j hij
          have hi0 : i = 0 := Fin.ext (by have := Fin.lt_def.mp hij; omega)
          have hj1 : j = 1 := Fin.ext (by have := Fin.lt_def.mp hij; omega)
          subst hi0; subst hj1; exact hlt
      · classical
        have hr3 : 3 ≤ r := by omega
        have hs3 : 3 ≤ s := by omega
        let L := U.filter (fun p => ∃ e : Fin (r - 1) → ℝ × ℝ,
          IsChain true U e ∧ e ⟨r - 2, by omega⟩ = p)
        let U' := U \ L
        have hLU : L ⊆ U := filter_subset _ _
        have hU'U : U' ⊆ U := sdiff_subset
        have hsum : U'.card + L.card = U.card := by
          rw [← card_union_of_disjoint disjoint_sdiff_self_left, sdiff_union_of_subset hLU]
        have hpascal : (r + s - 4).choose (r - 2) =
            ((r - 1) + s - 4).choose ((r - 1) - 2) + (r + (s - 1) - 4).choose (r - 2) := by
          have h1 : r + s - 4 = (r + s - 5) + 1 := by omega
          have h2 : r - 2 = (r - 3) + 1 := by omega
          have h3 : (r - 1) + s - 4 = r + s - 5 := by omega
          have h4 : (r - 1) - 2 = r - 3 := by omega
          have h5 : r + (s - 1) - 4 = r + s - 5 := by omega
          rw [h1, h2, h3, h4, h5, Nat.choose_succ_succ]
        by_cases hU' : ((r - 1) + s - 4).choose ((r - 1) - 2) < U'.card
        · rcases ih (r - 1) s (by omega) hs (by omega) U' (hinj.mono hU'U)
            (fun a ha b hb c hc => hgen a (hU'U ha) b (hU'U hb) c (hU'U hc)) hU' with
            ⟨e, he⟩ | ⟨f, hf⟩
          · exfalso
            have hmemU' : e ⟨r - 2, by omega⟩ ∈ U' := he.1 _
            have hmemL : e ⟨r - 2, by omega⟩ ∈ L := mem_filter.mpr
              ⟨hU'U hmemU', e, ⟨fun i => hU'U (he.1 i), he.2.1, he.2.2⟩, rfl⟩
            exact (mem_sdiff.mp hmemU').2 hmemL
          · exact Or.inr ⟨f, fun i => hU'U (hf.1 i), hf.2.1, hf.2.2⟩
        · have hLcard : (r + (s - 1) - 4).choose (r - 2) < L.card := by omega
          rcases ih r (s - 1) hr (by omega) (by omega) L (hinj.mono hLU)
            (fun a ha b hb c hc => hgen a (hLU ha) b (hLU hb) c (hLU hc)) hLcard with
            ⟨e, he⟩ | ⟨f, hf⟩
          · exact Or.inl ⟨e, fun i => hLU (he.1 i), he.2.1, he.2.2⟩
          · have hf0L : f ⟨0, by omega⟩ ∈ L := hf.1 ⟨0, by omega⟩
            obtain ⟨_, e, he, hend⟩ := mem_filter.mp hf0L
            have haU : e ⟨r - 3, by omega⟩ ∈ U := he.1 _
            have hbU : f ⟨0, by omega⟩ ∈ U := hLU (hf.1 _)
            have hcU : f ⟨1, by omega⟩ ∈ U := hLU (hf.1 _)
            have hab : (e ⟨r - 3, by omega⟩).1 < (f ⟨0, by omega⟩).1 := by
              rw [← hend]
              exact he.2.1 (Fin.mk_lt_mk.mpr (by omega))
            have hbc : (f ⟨0, by omega⟩).1 < (f ⟨1, by omega⟩).1 :=
              hf.2.1 (Fin.mk_lt_mk.mpr (by omega))
            have hne := hgen _ haU _ hbU _ hcU hab hbc
            rcases lt_or_gt_of_ne hne with hneg | hpos
            · right
              have hfU : IsChain false U f := ⟨fun i => hLU (hf.1 i), hf.2.1, hf.2.2⟩
              have ht : turn false (e ⟨r - 3, by omega⟩) (f ⟨0, by omega⟩) (f ⟨1, by omega⟩) := by
                unfold turn
                simp only [Bool.false_eq_true, ↓reduceIte]
                linarith
              obtain ⟨f', hf'⟩ := extend_left (by omega : 2 ≤ s - 1) hfU haU hab ht
              have hseq : s - 1 + 1 = s := by omega
              exact ⟨f' ∘ finCongr hseq.symm, fun i => hf'.1 _,
                fun i j hij => hf'.2.1 (by simpa using hij),
                fun i j l hij hjl => hf'.2.2 _ _ _ (by simpa using hij) (by simpa using hjl)⟩
            · left
              have ht : turn true (e ⟨r - 3, by omega⟩) (e ⟨r - 2, by omega⟩) (f ⟨1, by omega⟩) := by
                rw [hend]
                unfold turn
                simp only [↓reduceIte, one_mul]
                exact hpos
              have hx : (e ⟨r - 2, by omega⟩).1 < (f ⟨1, by omega⟩).1 := by
                rw [hend]
                exact hbc
              obtain ⟨e', he'⟩ := extend_right (by omega : 2 ≤ r - 1) he hcU hx ht
              have hreq : r - 1 + 1 = r := by omega
              exact ⟨e' ∘ finCongr hreq.symm, fun i => he'.1 _,
                fun i j hij => he'.2.1 (by simpa using hij),
                fun i j l hij hjl => he'.2.2 _ _ _ (by simpa using hij) (by simpa using hjl)⟩

lemma dense_subsets {α : Type*} (S : Finset α) {d m : ℕ}
    (hdm : d ≤ m) (hmS : m ≤ S.card) (good : Finset α → Prop) [DecidablePred good]
    (hit : ∀ U ⊆ S, U.card = m → ∃ T ⊆ U, T.card = d ∧ good T) :
    S.card.choose d ≤ ((S.powersetCard d).filter good).card * m.choose d := by
  classical
  let G := (S.powersetCard d).filter good
  have hcount :
      (S.powersetCard m).card * 1 ≤ G.card * (S.card - d).choose (m - d) := by
    apply Finset.card_mul_le_card_mul (fun U T : Finset α => T ⊆ U)
    · intro U hU
      obtain ⟨hUS, hUm⟩ := mem_powersetCard.mp hU
      obtain ⟨T, hTU, hTd, hg⟩ := hit U hUS hUm
      exact card_pos.mpr ⟨T, mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_powersetCard.mpr ⟨hTU.trans hUS, hTd⟩, hg⟩, hTU⟩⟩
    · intro T hT
      obtain ⟨hTS, hTd⟩ := mem_powersetCard.mp (mem_filter.mp hT).1
      change ((S.powersetCard m).filter (T ⊆ ·)).card ≤ _
      rw [card_filter_powersetCard_subset T S m hTS (hTd ▸ hdm), hTd]
  rw [card_powersetCard, mul_one] at hcount
  have hp : 0 < (S.card - d).choose (m - d) := Nat.choose_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ hp
  calc
    S.card.choose d * (S.card - d).choose (m - d) =
        S.card.choose m * m.choose d := (Nat.choose_mul hdm).symm
    _ ≤ (G.card * (S.card - d).choose (m - d)) * m.choose d :=
      Nat.mul_le_mul_right _ hcount
    _ = (G.card * m.choose d) * (S.card - d).choose (m - d) := by ac_rfl

lemma inGap_of_chain {K : ℕ} {up : Bool} {e : Fin (2 * K + 1) → ℝ × ℝ}
    (he : StrictMono (fun i => (e i).1) ∧
      ∀ i j l, i < j → j < l → turn up (e i) (e j) (e l)) (i : Fin K) :
    (e ⟨2 * i.val, by omega⟩).1 < (e ⟨2 * i.val + 1, by omega⟩).1 ∧
      (e ⟨2 * i.val + 1, by omega⟩).1 < (e ⟨2 * (i.val + 1), by omega⟩).1 ∧
      ∀ j l : Fin (K + 1), j < l →
        if l.val ≤ i.val then turn up (e ⟨2 * j.val, by omega⟩) (e ⟨2 * l.val, by omega⟩)
          (e ⟨2 * i.val + 1, by omega⟩)
        else if i.val < j.val then turn up (e ⟨2 * i.val + 1, by omega⟩)
          (e ⟨2 * j.val, by omega⟩) (e ⟨2 * l.val, by omega⟩)
        else turn up (e ⟨2 * j.val, by omega⟩) (e ⟨2 * i.val + 1, by omega⟩)
          (e ⟨2 * l.val, by omega⟩) := by
  refine ⟨he.1 (Fin.mk_lt_mk.mpr (by omega)), he.1 (Fin.mk_lt_mk.mpr (by omega)), ?_⟩
  intro j l hjl
  have hjl' : (⟨2 * j.val, by omega⟩ : Fin (2 * K + 1)) < ⟨2 * l.val, by omega⟩ :=
    Fin.mk_lt_mk.mpr (by have := Fin.lt_def.mp hjl; omega)
  by_cases hl : l.val ≤ i.val
  · simp only [if_pos hl]
    exact he.2 _ _ _ hjl' (Fin.mk_lt_mk.mpr (by omega))
  · by_cases hj : i.val < j.val
    · simp only [if_neg hl, if_pos hj]
      exact he.2 _ _ _ (Fin.mk_lt_mk.mpr (by omega)) hjl'
    · simp only [if_neg hl, if_neg hj]
      exact he.2 _ _ _ (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

lemma even_odd_determine {α : Type*} {K : ℕ} {e f : Fin (2 * K + 1) → α}
    (he : ∀ i : Fin (K + 1), e ⟨2 * i.val, by omega⟩ = f ⟨2 * i.val, by omega⟩)
    (ho : ∀ i : Fin K, e ⟨2 * i.val + 1, by omega⟩ = f ⟨2 * i.val + 1, by omega⟩) :
    e = f := by
  funext i
  by_cases h : i.val % 2 = 0
  · have hj : (⟨2 * (i.val / 2), by omega⟩ : Fin (2 * K + 1)) = i := by
      apply Fin.ext; change 2 * (i.val / 2) = i.val; omega
    simpa only [hj] using he ⟨i.val / 2, by omega⟩
  · have hj : (⟨2 * (i.val / 2) + 1, by omega⟩ : Fin (2 * K + 1)) = i := by
      apply Fin.ext; change 2 * (i.val / 2) + 1 = i.val; omega
    simpa only [hj] using ho ⟨i.val / 2, by omega⟩

lemma image_eq_of_strictMono {d : ℕ} {e : Fin d → ℝ × ℝ} {T : Finset (ℝ × ℝ)}
    (hTd : T.card = d) (hsub : ∀ i, e i ∈ T) (he : StrictMono (fun i => (e i).1)) :
    Finset.univ.image e = T := by
  classical
  have hi : Function.Injective e := fun i j hij => he.injective (congrArg Prod.fst hij)
  have hs : Finset.univ.image e ⊆ T := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact hsub i
  apply eq_of_subset_of_card_le hs
  rw [card_image_of_injective _ hi, card_univ, Fintype.card_fin, hTd]

lemma nat_prod_lt_prod_of_nonempty {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (hs : s.Nonempty) {f g : ι → ℕ} (h : ∀ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => exact (not_nonempty_empty hs).elim
  | @insert a t hat ih =>
    rw [prod_insert hat, prod_insert hat]
    have ha : f a < g a := h a (mem_insert_self a t)
    by_cases ht : t.Nonempty
    · have htp : ∏ i ∈ t, f i < ∏ i ∈ t, g i :=
        ih ht (fun i hi => h i (mem_insert_of_mem hi))
      have hga : 0 < g a := by omega
      have hgt : 0 < ∏ i ∈ t, g i := by omega
      calc f a * ∏ i ∈ t, f i ≤ f a * ∏ i ∈ t, g i := Nat.mul_le_mul_left _ htp.le
        _ < g a * ∏ i ∈ t, g i := Nat.mul_lt_mul_of_pos_right ha hgt
    · rw [not_nonempty_iff_eq_empty] at ht
      subst ht
      simpa using ha

lemma nat_le_choose : ∀ n r : ℕ, 1 ≤ r → r < n → n ≤ n.choose r := by
  intro n
  induction n with
  | zero => intro r _ h; omega
  | succ n ih =>
    intro r hr1 hrn
    by_cases h1 : r = 1
    · subst h1; simp
    · by_cases hn : r = n
      · subst hn; rw [Nat.choose_succ_self_right]
      · have hpos : 0 < n.choose (r - 1) := Nat.choose_pos (by omega)
        have hih : n ≤ n.choose r := ih r (by omega) (by omega)
        have hEq : (n + 1).choose r = n.choose (r - 1) + n.choose r := by
          have : r = (r - 1) + 1 := by omega
          conv_lhs => rw [this]
          rw [Nat.choose_succ_succ]
          congr 1
          congr 1
          omega
        omega

open scoped Classical in
lemma exists_max_prod_anchor {K m : ℕ} (S : Finset (ℝ × ℝ))
    (hm : 2 * K + 1 ≤ m) (hmS : m ≤ S.card) (h2d : 2 * (2 * K + 1) ≤ S.card)
    (hit : ∀ U ⊆ S, U.card = m → ∃ (up : Bool) (e : Fin (2 * K + 1) → ℝ × ℝ),
      IsChain up U e) :
    ∃ (up : Bool) (a : Fin (K + 1) → ℝ × ℝ),
      StrictMono (fun i => (a i).1) ∧
      S.card ^ K ≤ 2 * (2 * m) ^ (2 * K + 1) *
        ∏ i : Fin K, (S.filter (fun p =>
          (a ⟨i.val, by omega⟩).1 < p.1 ∧ p.1 < (a ⟨i.val + 1, by omega⟩).1 ∧
          ∀ j l : Fin (K + 1), j < l →
            if l.val ≤ i.val then turn up (a j) (a l) p
            else if i.val < j.val then turn up p (a j) (a l)
            else turn up (a j) p (a l))).card := by
  classical
  set d := 2 * K + 1 with hd
  let good : Finset (ℝ × ℝ) → Prop := fun T =>
    ∃ (up : Bool) (e : Fin d → ℝ × ℝ), IsChain up T e
  have hit' : ∀ U ⊆ S, U.card = m → ∃ T ⊆ U, T.card = d ∧ good T := by
    intro U hUS hUm
    obtain ⟨up, e, he⟩ := hit U hUS hUm
    have hi : Function.Injective e := fun i j hij => he.2.1.injective (congrArg Prod.fst hij)
    refine ⟨univ.image e, ?_, by simp [card_image_of_injective _ hi], up, e,
      fun i => mem_image.mpr ⟨i, mem_univ _, rfl⟩, he.2.1, he.2.2⟩
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact he.1 i
  let G := (S.powersetCard d).filter good
  have hdense : S.card.choose d ≤ G.card * m.choose d := dense_subsets S hm hmS good hit'
  have hpowN : S.card ^ d ≤ G.card * (2 * m) ^ d := by
    have h1 : S.card ≤ 2 * (S.card + 1 - d) := by omega
    have hdesc : S.card.descFactorial d ≤ G.card * m.descFactorial d := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
      calc d.factorial * S.card.choose d
          ≤ d.factorial * (G.card * m.choose d) := Nat.mul_le_mul_left _ hdense
        _ = G.card * (d.factorial * m.choose d) := by ac_rfl
    calc S.card ^ d
        ≤ (2 * (S.card + 1 - d)) ^ d := Nat.pow_le_pow_left h1 d
      _ = 2 ^ d * (S.card + 1 - d) ^ d := Nat.mul_pow _ _ _
      _ ≤ 2 ^ d * S.card.descFactorial d :=
          Nat.mul_le_mul_left _ (S.card.pow_sub_le_descFactorial d)
      _ ≤ 2 ^ d * (G.card * m.descFactorial d) := Nat.mul_le_mul_left _ hdesc
      _ ≤ 2 ^ d * (G.card * m ^ d) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow m d))
      _ = G.card * (2 ^ d * m ^ d) := by ac_rfl
      _ = G.card * (2 * m) ^ d := by rw [Nat.mul_pow]
  have hNpos : 0 < S.card := by omega
  have hGpos : 0 < G.card := by
    by_contra h0
    have hGe : G.card = 0 := by omega
    rw [hGe, zero_mul] at hpowN
    have : 0 < S.card ^ d := Nat.pow_pos hNpos
    omega
  have hgood (T : ↑G) : good T.val := (mem_filter.mp T.property).2
  let upT (T : ↑G) := (hgood T).choose
  let eT (T : ↑G) := (hgood T).choose_spec.choose
  have heT (T : ↑G) : IsChain (upT T) T.val (eT T) := (hgood T).choose_spec.choose_spec
  have hT (T : ↑G) := mem_powersetCard.mp (mem_filter.mp T.property).1
  let anchor (T : ↑G) : Bool × (Fin (K + 1) → ℝ × ℝ) :=
    (upT T, fun i : Fin (K + 1) => eT T ⟨2 * i.val, by omega⟩)
  let completion (T : ↑G) : Fin K → ℝ × ℝ := fun i => eT T ⟨2 * i.val + 1, by omega⟩
  let A := G.attach.image anchor
  let A₀ := (univ : Finset Bool) ×ˢ Fintype.piFinset (fun _ : Fin (K + 1) => S)
  let R (a : Bool × (Fin (K + 1) → ℝ × ℝ)) (i : Fin K) : Finset (ℝ × ℝ) :=
    S.filter (fun p =>
      (a.2 ⟨i.val, by omega⟩).1 < p.1 ∧ p.1 < (a.2 ⟨i.val + 1, by omega⟩).1 ∧
      ∀ j l : Fin (K + 1), j < l →
        if l.val ≤ i.val then turn a.1 (a.2 j) (a.2 l) p
        else if i.val < j.val then turn a.1 p (a.2 j) (a.2 l)
        else turn a.1 (a.2 j) p (a.2 l))
  have hAA₀ : A ⊆ A₀ := by
    intro a ha
    obtain ⟨T, _, rfl⟩ := mem_image.mp ha
    exact mem_product.mpr ⟨mem_univ _, Fintype.mem_piFinset.mpr
      (fun i => (hT T).1 ((heT T).1 _))⟩
  have hAc : A.card ≤ 2 * S.card ^ (K + 1) := by
    simpa [A₀, Fintype.card_piFinset_const] using card_le_card hAA₀
  have hAne : A.Nonempty := (card_pos.mp (by rw [card_attach]; exact hGpos)).image anchor
  obtain ⟨a, haA, hmax⟩ := exists_max_image A (fun a => ∏ i : Fin K, (R a i).card) hAne
  have hfib : ∀ b ∈ A, (G.attach.filter (fun T => anchor T = b)).card ≤
      ∏ i : Fin K, (R b i).card := by
    intro b _
    have hinjF : Set.InjOn completion (G.attach.filter (fun T => anchor T = b) : Set ↑G) := by
      intro T hTf U hUf hc
      have hTa : anchor T = b := (mem_filter.mp hTf).2
      have hUa : anchor U = b := (mem_filter.mp hUf).2
      have haeq : anchor T = anchor U := hTa.trans hUa.symm
      have hfun : eT T = eT U := even_odd_determine
        (fun i => congrFun (congrArg Prod.snd haeq) i) (fun i => congrFun hc i)
      apply Subtype.ext
      rw [← image_eq_of_strictMono (hT T).2 (heT T).1 (heT T).2.1,
          ← image_eq_of_strictMono (hT U).2 (heT U).1 (heT U).2.1, hfun]
    have hmap : Set.MapsTo completion (G.attach.filter (fun T => anchor T = b) : Set ↑G)
        (Fintype.piFinset (R b) : Set (Fin K → ℝ × ℝ)) := by
      intro T hTf
      have hTa : anchor T = b := (mem_filter.mp hTf).2
      rw [mem_coe, Fintype.mem_piFinset]
      intro i
      rw [← hTa]
      exact mem_filter.mpr ⟨(hT T).1 ((heT T).1 _),
        inGap_of_chain ⟨(heT T).2.1, (heT T).2.2⟩ i⟩
    calc (G.attach.filter (fun T => anchor T = b)).card
        ≤ (Fintype.piFinset (R b)).card := card_le_card_of_injOn completion hmap hinjF
      _ = ∏ i : Fin K, (R b i).card := Fintype.card_piFinset _
  have hGcard : G.card ≤ A.card * ∏ i : Fin K, (R a i).card := by
    have hpart : G.attach.card = ∑ b ∈ A, (G.attach.filter (fun T => anchor T = b)).card := by
      rw [card_eq_sum_card_fiberwise (f := anchor) (fun T hT' => mem_image.mpr ⟨T, hT', rfl⟩)]
    rw [← card_attach, hpart]
    calc ∑ b ∈ A, (G.attach.filter (fun T => anchor T = b)).card
        ≤ ∑ b ∈ A, ∏ i : Fin K, (R b i).card := sum_le_sum hfib
      _ ≤ ∑ _b ∈ A, ∏ i : Fin K, (R a i).card := sum_le_sum (fun b hb => hmax b hb)
      _ = A.card * ∏ i : Fin K, (R a i).card := by rw [sum_const, smul_eq_mul]
  have hmain : S.card ^ (K + 1) * S.card ^ K ≤
      S.card ^ (K + 1) * (2 * (2 * m) ^ d * ∏ i : Fin K, (R a i).card) := by
    have hsplit : S.card ^ d = S.card ^ (K + 1) * S.card ^ K := by
      rw [← pow_add]; congr 1; omega
    rw [← hsplit]
    calc S.card ^ d
        ≤ G.card * (2 * m) ^ d := hpowN
      _ ≤ (A.card * ∏ i : Fin K, (R a i).card) * (2 * m) ^ d :=
          Nat.mul_le_mul_right _ hGcard
      _ ≤ (2 * S.card ^ (K + 1) * ∏ i : Fin K, (R a i).card) * (2 * m) ^ d :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hAc)
      _ = S.card ^ (K + 1) * (2 * (2 * m) ^ d * ∏ i : Fin K, (R a i).card) := by ac_rfl
  have hcancel : S.card ^ K ≤ 2 * (2 * m) ^ d * ∏ i : Fin K, (R a i).card :=
    Nat.le_of_mul_le_mul_left hmain (Nat.pow_pos hNpos)
  obtain ⟨T, _, rfl⟩ := mem_image.mp haA
  refine ⟨upT T, fun i : Fin (K + 1) => eT T ⟨2 * i.val, by omega⟩, ?_, hcancel⟩
  intro i j hij
  exact (heT T).2.1 (Fin.mk_lt_mk.mpr (by have := Fin.lt_def.mp hij; omega))

end OMA.Erdos107HmptH2

open OMA.Erdos107HmptH2 in
theorem OMA.solution : OMA.R_Erdos107_variants_hmpt_bound_R1_H1_R1.H2 := by
  classical
  refine ⟨36, ?_⟩
  intro k hk X hX hcard
  obtain ⟨t, ht_inj⟩ := exists_shear_injOn X
  have hshear_inj : Set.InjOn (shear t) (X : Set E2) :=
    fun p hp q hq h => ht_inj hp hq (congrArg Prod.fst h)
  let S := X.image (shear t)
  have hScard : S.card = X.card := card_image_of_injOn hshear_inj
  have hSfst : Set.InjOn Prod.fst (S : Set (ℝ × ℝ)) := by
    intro u hu v hv heq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp (mem_coe.mp hu)
    obtain ⟨q, hq, rfl⟩ := mem_image.mp (mem_coe.mp hv)
    exact congrArg (shear t) (ht_inj hp hq heq)
  have hSgen : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0 :=
    orient_ne_zero_in_shear X hX t
  let K := 2 * k
  let d := 2 * K + 1
  let m := (2 * d - 4).choose (d - 2) + 1
  have hm_le_pow : m ≤ 2 ^ (8 * k) := by
    have hch : (2 * d - 4).choose (d - 2) ≤ 2 ^ (2 * d - 4) := Nat.choose_le_two_pow _ _
    have h1 : 2 * d - 4 = 8 * k - 2 := by dsimp [d, K]; omega
    rw [h1] at hch
    have h2 : 2 ^ (8 * k - 2) + 1 ≤ 2 ^ (8 * k) := by
      have hpow : 2 ^ (8 * k) = 4 * 2 ^ (8 * k - 2) := by
        calc 2 ^ (8 * k) = 2 ^ ((8 * k - 2) + 2) := by congr 1; omega
          _ = 2 ^ (8 * k - 2) * 2 ^ 2 := pow_add 2 _ 2
          _ = 4 * 2 ^ (8 * k - 2) := by ring
      have hpos : 1 ≤ 2 ^ (8 * k - 2) := Nat.one_le_two_pow
      omega
    dsimp [m]
    rw [h1]
    omega
  have hd_le_m : d ≤ m := by
    have h1 : 2 * d - 4 = 8 * k - 2 := by dsimp [d, K]; omega
    have h2 : d - 2 = 4 * k - 1 := by dsimp [d, K]; omega
    have h3 : 8 * k - 2 ≤ (8 * k - 2).choose (4 * k - 1) :=
      nat_le_choose (8 * k - 2) (4 * k - 1) (by omega) (by omega)
    dsimp [m]
    rw [h1, h2]
    dsimp [d, K]
    omega
  have hpow_le : 2 ^ (8 * k) ≤ S.card := by
    rw [hScard]
    exact (Nat.pow_le_pow_right (by norm_num) (by omega : 8 * k ≤ 36 * k)).trans hcard
  have hmS : m ≤ S.card := hm_le_pow.trans hpow_le
  have h2dS : 2 * d ≤ S.card := by
    have hlin : 2 * d ≤ 2 ^ (8 * k) := by
      have hpow : 2 ^ (8 * k) = 2 ^ 3 * 2 ^ (8 * k - 3) := by
        calc 2 ^ (8 * k) = 2 ^ (3 + (8 * k - 3)) := by congr 1; omega
          _ = 2 ^ 3 * 2 ^ (8 * k - 3) := pow_add 2 3 _
      have hlt := Nat.lt_two_pow_self (n := 8 * k - 3)
      dsimp [d, K]
      omega
    exact hlin.trans hpow_le
  have hhit : ∀ U ⊆ S, U.card = m → ∃ (up : Bool) (e : Fin d → ℝ × ℝ), IsChain up U e := by
    intro U hUS hUm
    have hgt : (d + d - 4).choose (d - 2) < U.card := by
      rw [hUm]; dsimp [m]; have : d + d - 4 = 2 * d - 4 := by omega
      rw [this]; omega
    rcases erdos_szekeres_cups_caps (d + d) d d (by dsimp [d, K]; omega)
      (by dsimp [d, K]; omega) rfl U (hSfst.mono hUS)
      (fun a ha b hb c hc => hSgen a (hUS ha) b (hUS hb) c (hUS hc)) hgt with
      ⟨e, he⟩ | ⟨f, hf⟩
    · exact ⟨true, e, he⟩
    · exact ⟨false, f, hf⟩
  obtain ⟨up, anc, hanc_mono, hprod⟩ := exists_max_prod_anchor S hd_le_m hmS h2dS hhit
  let R (i : Fin K) : Finset (ℝ × ℝ) :=
    S.filter (fun p =>
      (anc ⟨i.val, by omega⟩).1 < p.1 ∧ p.1 < (anc ⟨i.val + 1, by omega⟩).1 ∧
      ∀ j l : Fin (K + 1), j < l →
        if l.val ≤ i.val then turn up (anc j) (anc l) p
        else if i.val < j.val then turn up p (anc j) (anc l)
        else turn up (anc j) p (anc l))
  have hfactor : 2 * (2 * m) ^ d ≤ (2 ^ (18 * k)) ^ K := by
    have h2m : 2 * m ≤ 2 ^ (8 * k + 1) := by
      calc 2 * m ≤ 2 * 2 ^ (8 * k) := Nat.mul_le_mul_left 2 hm_le_pow
        _ = 2 ^ (8 * k + 1) := by rw [pow_succ']
    have hexp : (8 * k + 1) * d + 1 ≤ 18 * k * K := by
      dsimp [d, K]
      nlinarith
    calc 2 * (2 * m) ^ d
        ≤ 2 * (2 ^ (8 * k + 1)) ^ d := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h2m d)
      _ = 2 ^ ((8 * k + 1) * d + 1) := by rw [← pow_mul, ← pow_succ']
      _ ≤ 2 ^ (18 * k * K) := Nat.pow_le_pow_right (by norm_num) hexp
      _ = (2 ^ (18 * k)) ^ K := by rw [pow_mul]
  have hprod2 : S.card ^ K ≤ (2 ^ (18 * k)) ^ K * ∏ i : Fin K, (R i).card :=
    hprod.trans (Nat.mul_le_mul_right _ hfactor)
  let C := 2 ^ (36 * k)
  let G_idx := (univ : Finset (Fin K)).filter (fun i => S.card ≤ C * (R i).card)
  let B_idx := (univ : Finset (Fin K)).filter (fun i => ¬ S.card ≤ C * (R i).card)
  have hdisj : Disjoint B_idx G_idx := by
    rw [disjoint_left]
    intro i hiB hiG
    exact (mem_filter.mp hiB).2 (mem_filter.mp hiG).2
  have hunion : B_idx ∪ G_idx = univ := by
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and, iff_true, B_idx, G_idx]
    exact em' _
  have hcards : B_idx.card + G_idx.card = K := by
    have := card_union_of_disjoint hdisj
    rw [hunion, card_univ, Fintype.card_fin] at this
    exact this.symm
  have hGcard_ge : k ≤ G_idx.card := by
    by_contra hlt
    have hBge : k + 1 ≤ B_idx.card := by dsimp [K] at hcards; omega
    have hBne : B_idx.Nonempty := card_pos.mp (by omega)
    have hCpow : (2 ^ (18 * k)) ^ K ≤ C ^ B_idx.card := by
      have h1 : (2 ^ (18 * k)) ^ K = C ^ k := by
        dsimp [C, K]
        rw [← pow_mul, ← pow_mul]
        congr 1; ring
      rw [h1]
      exact Nat.pow_le_pow_right (Nat.one_le_two_pow) (by omega)
    have hBprod : C ^ B_idx.card * ∏ i ∈ B_idx, (R i).card < S.card ^ B_idx.card := by
      have h1 : C ^ B_idx.card * ∏ i ∈ B_idx, (R i).card = ∏ i ∈ B_idx, (C * (R i).card) := by
        rw [prod_mul_distrib, prod_const]
      have h2 : S.card ^ B_idx.card = ∏ _i ∈ B_idx, S.card := by rw [prod_const]
      rw [h1, h2]
      exact nat_prod_lt_prod_of_nonempty hBne (fun i hi => by
        have := (mem_filter.mp hi).2; omega)
    have hGprod : ∏ i ∈ G_idx, (R i).card ≤ S.card ^ G_idx.card := by
      calc ∏ i ∈ G_idx, (R i).card ≤ ∏ _i ∈ G_idx, S.card :=
            prod_le_prod' (fun i _ => card_le_card (filter_subset _ _))
        _ = S.card ^ G_idx.card := by rw [prod_const]
    have hfull : ∏ i : Fin K, (R i).card =
        (∏ i ∈ B_idx, (R i).card) * (∏ i ∈ G_idx, (R i).card) := by
      rw [← prod_union hdisj, hunion]
    have hNpos : 0 < S.card := by omega
    have hGpowpos : 0 < S.card ^ G_idx.card := Nat.pow_pos hNpos
    have hcontr : S.card ^ K < S.card ^ K := calc
      S.card ^ K ≤ (2 ^ (18 * k)) ^ K * ∏ i : Fin K, (R i).card := hprod2
      _ ≤ C ^ B_idx.card * ∏ i : Fin K, (R i).card := Nat.mul_le_mul_right _ hCpow
      _ = (C ^ B_idx.card * ∏ i ∈ B_idx, (R i).card) * (∏ i ∈ G_idx, (R i).card) := by
          rw [hfull, mul_assoc]
      _ ≤ (C ^ B_idx.card * ∏ i ∈ B_idx, (R i).card) * S.card ^ G_idx.card :=
          Nat.mul_le_mul_left _ hGprod
      _ < S.card ^ B_idx.card * S.card ^ G_idx.card :=
          Nat.mul_lt_mul_of_pos_right hBprod hGpowpos
      _ = S.card ^ K := by rw [← pow_add, hcards]
    exact lt_irrefl _ hcontr
  obtain ⟨I, hIG, hIcard⟩ := exists_subset_card_eq hGcard_ge
  let idx : Fin k ↪o Fin K := I.orderEmbOfFin hIcard
  let T (r : Fin k) : Finset E2 := X.filter (fun p => shear t p ∈ R (idx r))
  refine ⟨T, fun r => filter_subset _ _, ?_, ?_⟩
  · intro r
    have himg : (T r).image (shear t) = R (idx r) := by
      ext q
      constructor
      · intro hq
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
        exact (mem_filter.mp hp).2
      · intro hq
        have hqS : q ∈ S := (filter_subset _ _) hq
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hqS
        exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hq⟩, rfl⟩
    have hTcard : (T r).card = (R (idx r)).card := by
      rw [← himg, card_image_of_injOn (hshear_inj.mono (filter_subset _ _))]
    have hidxG : idx r ∈ G_idx := hIG (orderEmbOfFin_mem I hIcard r)
    rw [← hScard, hTcard]
    exact (mem_filter.mp hidxG).2
  · intro g hg
    have hturn : ∀ i j l : Fin k, i < j → j < l →
        turn up (shear t (g i)) (shear t (g j)) (shear t (g l)) := by
      intro i j l hij hjl
      have hij' : idx i < idx j := idx.strictMono hij
      have hjl' : idx j < idx l := idx.strictMono hjl
      have hgi : shear t (g i) ∈ R (idx i) := (mem_filter.mp (hg i)).2
      have hgj : shear t (g j) ∈ R (idx j) := (mem_filter.mp (hg j)).2
      have hgl : shear t (g l) ∈ R (idx l) := (mem_filter.mp (hg l)).2
      obtain ⟨_, _, hpi_hi, hpi_t⟩ := mem_filter.mp hgi
      obtain ⟨_, hpj_lo, hpj_hi, hpj_t⟩ := mem_filter.mp hgj
      obtain ⟨_, hpl_lo, _, hpl_t⟩ := mem_filter.mp hgl
      let aj : Fin (K + 1) := ⟨(idx j).val, by omega⟩
      let aj1 : Fin (K + 1) := ⟨(idx j).val + 1, by omega⟩
      have hajlt : aj < aj1 := Fin.mk_lt_mk.mpr (by omega)
      have h1 : (shear t (g i)).1 < (anc aj).1 := by
        have hle : (⟨(idx i).val + 1, by omega⟩ : Fin (K + 1)) ≤ aj :=
          Fin.mk_le_mk.mpr (by have := Fin.lt_def.mp hij'; omega)
        exact lt_of_lt_of_le hpi_hi (hanc_mono.monotone hle)
      have h4 : (anc aj1).1 < (shear t (g l)).1 := by
        have hle : aj1 ≤ (⟨(idx l).val, by omega⟩ : Fin (K + 1)) :=
          Fin.mk_le_mk.mpr (by have := Fin.lt_def.mp hjl'; omega)
        exact lt_of_le_of_lt (hanc_mono.monotone hle) hpl_lo
      have ht1 : turn up (shear t (g i)) (anc aj) (anc aj1) := by
        have h := hpi_t aj aj1 hajlt
        have hn1 : ¬ aj1.val ≤ (idx i).val := by
          have := Fin.lt_def.mp hij'; dsimp [aj1]; omega
        have hp2 : (idx i).val < aj.val := by
          have := Fin.lt_def.mp hij'; dsimp [aj]; omega
        simpa only [if_neg hn1, if_pos hp2] using h
      have ht2 : turn up (anc aj) (shear t (g j)) (anc aj1) := by
        have h := hpj_t aj aj1 hajlt
        have hn1 : ¬ aj1.val ≤ (idx j).val := by dsimp [aj1]; omega
        have hn2 : ¬ (idx j).val < aj.val := by dsimp [aj]; omega
        simpa only [if_neg hn1, if_neg hn2] using h
      have ht3 : turn up (anc aj) (anc aj1) (shear t (g l)) := by
        have h := hpl_t aj aj1 hajlt
        have hp1 : aj1.val ≤ (idx l).val := by
          have := Fin.lt_def.mp hjl'; dsimp [aj1]; omega
        simpa only [if_pos hp1] using h
      exact turn_gap h1 hpj_lo hpj_hi h4 ht1 ht2 ht3
    cases up
    · right
      intro i j l hij hjl
      have h := hturn i j l hij hjl
      unfold turn at h
      rw [orient_shear] at h
      unfold orientE at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      linarith
    · left
      intro i j l hij hjl
      have h := hturn i j l hij hjl
      unfold turn at h
      rw [orient_shear] at h
      unfold orientE at h
      simp only [↓reduceIte, one_mul] at h
      exact h
