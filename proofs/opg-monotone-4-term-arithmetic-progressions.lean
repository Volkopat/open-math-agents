import OMAStatements.S_opg_monotone_4_term_arithmetic_progressions

namespace OPGMonotone4APProof

open OMA.S_opg_monotone_4_term_arithmetic_progressions
open Classical

/-! ### Part 1: Reverse colexicographic binary order on ℕ -/

private def rlex (m n : ℕ) : Prop :=
  ∃ k : ℕ, (∀ j < k, m.testBit j = n.testBit j) ∧ m.testBit k = true ∧ n.testBit k = false

private lemma rlex_irrefl (m : ℕ) : ¬ rlex m m := by
  rintro ⟨k, _, hm, hn⟩
  rw [hm] at hn
  cases hn

private lemma rlex_asymm {m n : ℕ} (h1 : rlex m n) : ¬ rlex n m := by
  rintro ⟨k2, heq2, hn2, hm2⟩
  rcases h1 with ⟨k1, heq1, hm1, hn1⟩
  rcases lt_trichotomy k1 k2 with hlt | rfl | hgt
  · have := heq2 k1 hlt
    rw [hm1, hn1] at this
    cases this
  · rw [hm1] at hm2
    cases hm2
  · have := heq1 k2 hgt
    rw [hm2, hn2] at this
    cases this

private lemma rlex_trans {a b c : ℕ} (h1 : rlex a b) (h2 : rlex b c) : rlex a c := by
  rcases h1 with ⟨k1, heq1, ha1, hb1⟩
  rcases h2 with ⟨k2, heq2, hb2, hc2⟩
  rcases lt_trichotomy k1 k2 with hlt | rfl | hgt
  · refine ⟨k1, fun j hj => (heq1 j hj).trans (heq2 j (lt_trans hj hlt)), ha1, ?_⟩
    rw [← heq2 k1 hlt, hb1]
  · rw [hb1] at hb2
    cases hb2
  · refine ⟨k2, fun j hj => (heq1 j (lt_trans hj hgt)).trans (heq2 j hj), ?_, hc2⟩
    rw [heq1 k2 hgt, hb2]

private lemma rlex_total {m n : ℕ} (hne : m ≠ n) : rlex m n ∨ rlex n m := by
  have hex : ∃ k : ℕ, m.testBit k ≠ n.testBit k := by
    by_contra h
    push Not at h
    exact hne (Nat.eq_of_testBit_eq h)
  let k := Nat.find hex
  have hne_k : m.testBit k ≠ n.testBit k := Nat.find_spec hex
  have hlt : ∀ j < k, m.testBit j = n.testBit j := fun j hj => by
    by_contra h
    exact Nat.find_min hex hj h
  cases hm : m.testBit k <;> cases hn : n.testBit k
  · exact absurd (hm.trans hn.symm) hne_k
  · exact Or.inr ⟨k, fun j hj => (hlt j hj).symm, hn, hm⟩
  · exact Or.inl ⟨k, hlt, hm, hn⟩
  · exact absurd (hm.trans hn.symm) hne_k

private lemma rlex_zero {m : ℕ} (hm : m ≠ 0) : rlex m 0 := by
  rcases rlex_total hm with h | ⟨k, _, h0, _⟩
  · exact h
  · simp at h0

private lemma rlex_odd_even (x y : ℕ) : rlex (2 * x + 1) (2 * y) := by
  refine ⟨0, fun j hj => absurd hj (Nat.not_lt_zero j), ?_, ?_⟩
  · simp [Nat.testBit_zero]
  · simp [Nat.testBit_zero]

private lemma testBit_two_mul_add_one (x k : ℕ) :
    (2 * x + 1).testBit (k + 1) = x.testBit k := by
  rw [Nat.testBit_succ]
  have : (2 * x + 1) / 2 = x := by omega
  rw [this]

private lemma testBit_two_mul_succ (x k : ℕ) :
    (2 * x).testBit (k + 1) = x.testBit k := by
  rw [Nat.testBit_succ]
  have : (2 * x) / 2 = x := by omega
  rw [this]

private lemma rlex_two_mul (x y : ℕ) : rlex (2 * x) (2 * y) ↔ rlex x y := by
  constructor
  · rintro ⟨k, heq, hx, hy⟩
    cases k with
    | zero =>
        simp [Nat.testBit_zero] at hx
    | succ k =>
        refine ⟨k, fun j hj => ?_, ?_, ?_⟩
        · have := heq (j + 1) (Nat.succ_lt_succ hj)
          simpa [testBit_two_mul_succ] using this
        · simpa [testBit_two_mul_succ] using hx
        · simpa [testBit_two_mul_succ] using hy
  · rintro ⟨k, heq, hx, hy⟩
    refine ⟨k + 1, fun j hj => ?_, ?_, ?_⟩
    · cases j with
      | zero => simp [Nat.testBit_zero]
      | succ j =>
          simp only [testBit_two_mul_succ]
          exact heq j (Nat.lt_of_succ_lt_succ hj)
    · simpa [testBit_two_mul_succ] using hx
    · simpa [testBit_two_mul_succ] using hy

private lemma rlex_two_mul_add_one (x y : ℕ) :
    rlex (2 * x + 1) (2 * y + 1) ↔ rlex x y := by
  constructor
  · rintro ⟨k, heq, hx, hy⟩
    cases k with
    | zero =>
        simp [Nat.testBit_zero] at hy
    | succ k =>
        refine ⟨k, fun j hj => ?_, ?_, ?_⟩
        · have := heq (j + 1) (Nat.succ_lt_succ hj)
          simpa [testBit_two_mul_add_one] using this
        · simpa [testBit_two_mul_add_one] using hx
        · simpa [testBit_two_mul_add_one] using hy
  · rintro ⟨k, heq, hx, hy⟩
    refine ⟨k + 1, fun j hj => ?_, ?_, ?_⟩
    · cases j with
      | zero => simp [Nat.testBit_zero]
      | succ j =>
          simp only [testBit_two_mul_add_one]
          exact heq j (Nat.lt_of_succ_lt_succ hj)
    · simpa [testBit_two_mul_add_one] using hx
    · simpa [testBit_two_mul_add_one] using hy

private lemma rlex_ap_flip :
    ∀ d : ℕ, 0 < d → ∀ a : ℕ, rlex a (a + d) ↔ ¬ rlex (a + d) (a + 2 * d) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro hd a
    by_cases hodd : d % 2 = 1
    · by_cases ha : a % 2 = 0
      · have h1 : ¬ rlex a (a + d) := by
          have ha' : a = 2 * (a / 2) := by omega
          have had' : a + d = 2 * ((a + d) / 2) + 1 := by omega
          rw [had', ha']
          exact rlex_asymm (rlex_odd_even _ _)
        have h2 : rlex (a + d) (a + 2 * d) := by
          have had' : a + d = 2 * ((a + d) / 2) + 1 := by omega
          have ha2d' : a + 2 * d = 2 * ((a + 2 * d) / 2) := by omega
          rw [ha2d', had']
          exact rlex_odd_even _ _
        simp [h1, h2]
      · have h1 : rlex a (a + d) := by
          have ha' : a = 2 * (a / 2) + 1 := by omega
          have had' : a + d = 2 * ((a + d) / 2) := by omega
          rw [had', ha']
          exact rlex_odd_even _ _
        have h2 : ¬ rlex (a + d) (a + 2 * d) := by
          have had' : a + d = 2 * ((a + d) / 2) := by omega
          have ha2d' : a + 2 * d = 2 * ((a + 2 * d) / 2) + 1 := by omega
          rw [ha2d', had']
          exact rlex_asymm (rlex_odd_even _ _)
        simp [h1, h2]
    · have hd2 : d = 2 * (d / 2) := by omega
      have hpos : 0 < d / 2 := by omega
      have hlt : d / 2 < d := by omega
      by_cases ha : a % 2 = 0
      · have ha0 : 2 * (a / 2) = a := by omega
        have h1 : 2 * (a / 2 + d / 2) = a + d := by omega
        have h2 : 2 * (a / 2 + 2 * (d / 2)) = a + 2 * d := by omega
        have h := ih (d / 2) hlt hpos (a / 2)
        rw [← rlex_two_mul (a / 2) (a / 2 + d / 2),
            ← rlex_two_mul (a / 2 + d / 2) (a / 2 + 2 * (d / 2)), ha0, h1, h2] at h
        exact h
      · have ha1 : 2 * (a / 2) + 1 = a := by omega
        have h1 : 2 * (a / 2 + d / 2) + 1 = a + d := by omega
        have h2 : 2 * (a / 2 + 2 * (d / 2)) + 1 = a + 2 * d := by omega
        have h := ih (d / 2) hlt hpos (a / 2)
        rw [← rlex_two_mul_add_one (a / 2) (a / 2 + d / 2),
            ← rlex_two_mul_add_one (a / 2 + d / 2) (a / 2 + 2 * (d / 2)), ha1, h1, h2] at h
        exact h

private def Is4AP (a b c d : ℕ) : Prop :=
  a ≠ b ∧ a + c = 2 * b ∧ b + d = 2 * c

private lemma rlex_no_3ap {a b c : ℕ} (hne : a ≠ b) (hap : a + c = 2 * b) :
    ¬ (rlex a b ∧ rlex b c) ∧ ¬ (rlex c b ∧ rlex b a) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · set d := b - a
    have hd : 0 < d := by omega
    have hb : b = a + d := by omega
    have hc : c = a + 2 * d := by omega
    rw [hb, hc]
    have hflip := rlex_ap_flip d hd a
    constructor
    · rintro ⟨h1, h2⟩; exact (hflip.mp h1) h2
    · rintro ⟨h1, h2⟩
      have h3 : ¬ rlex a (a + d) := rlex_asymm h2
      have h4 : rlex (a + d) (a + 2 * d) := by
        by_contra hnot
        exact h3 (hflip.mpr hnot)
      exact rlex_asymm h4 h1
  · set d := a - b
    have hd : 0 < d := by omega
    have hb : b = c + d := by omega
    have ha : a = c + 2 * d := by omega
    rw [ha, hb]
    have hflip := rlex_ap_flip d hd c
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : ¬ rlex c (c + d) := rlex_asymm h2
      have h4 : rlex (c + d) (c + 2 * d) := by
        by_contra hnot
        exact h3 (hflip.mpr hnot)
      exact rlex_asymm h4 h1
    · rintro ⟨h1, h2⟩; exact (hflip.mp h1) h2

private lemma rlex_4ap_iff {a b c d : ℕ} (h : Is4AP a b c d) :
    rlex a b ↔ rlex c d := by
  rcases h with ⟨hne, habc, hbcd⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · set r := b - a
    have hr : 0 < r := by omega
    have hb : b = a + r := by omega
    have hc : c = a + 2 * r := by omega
    have hd' : d = a + 3 * r := by omega
    have h1 := rlex_ap_flip r hr a
    have h2 := rlex_ap_flip r hr (a + r)
    have h3 : a + r + r = a + 2 * r := by omega
    have h4 : a + r + 2 * r = a + 3 * r := by omega
    rw [h3, h4] at h2
    rw [hb, hc, hd']
    tauto
  · set r := a - b
    have hr : 0 < r := by omega
    have hc : c = d + r := by omega
    have hb : b = d + 2 * r := by omega
    have ha : a = d + 3 * r := by omega
    have h1 := rlex_ap_flip r hr d
    have h2 := rlex_ap_flip r hr (d + r)
    have h3 : d + r + r = d + 2 * r := by omega
    have h4 : d + r + 2 * r = d + 3 * r := by omega
    rw [h3, h4] at h2
    rw [ha, hb, hc]
    have hba : rlex (d + 3 * r) (d + 2 * r) ↔ ¬ rlex (d + 2 * r) (d + 3 * r) :=
      ⟨rlex_asymm, fun hn => (rlex_total (by omega)).resolve_left hn⟩
    have hdc : rlex (d + r) d ↔ ¬ rlex d (d + r) :=
      ⟨rlex_asymm, fun hn => (rlex_total (by omega)).resolve_left hn⟩
    rw [hba, hdc]
    tauto

/-! ### Part 2: Completion order and safe finite words -/

private def compLT (P : List ℕ) (x y : ℕ) : Prop :=
  (x ∈ P ∧ y ∈ P ∧ P.idxOf x < P.idxOf y) ∨
  (x ∈ P ∧ y ∉ P) ∨
  (x ∉ P ∧ y ∉ P ∧ rlex x y)

private def Is4APFree (R : ℕ → ℕ → Prop) : Prop :=
  ∀ a b c d : ℕ, Is4AP a b c d → ¬ (R a b ∧ R b c ∧ R c d)

private def Safe (P : List ℕ) : Prop :=
  P.Nodup ∧ Is4APFree (compLT P)

private lemma compLT_prefix_left {P Q : List ℕ} (hpre : P <+: Q) {x y : ℕ}
    (hy : y ∈ P) (hxy : compLT Q x y) : x ∈ P ∧ compLT P x y := by
  rcases hpre with ⟨R, rfl⟩
  have hyQ : y ∈ P ++ R := List.mem_append_left R hy
  have hidx_y : (P ++ R).idxOf y = P.idxOf y := List.idxOf_append_of_mem hy
  rcases hxy with ⟨hxQ, _, hlt⟩ | ⟨_, hyNot⟩ | ⟨_, hyNot, _⟩
  · have hxP : x ∈ P := by
      by_contra hxNot
      have hidx_x : P.length ≤ (P ++ R).idxOf x := by
        rw [List.idxOf_append_of_notMem hxNot]
        omega
      have hy_lt : P.idxOf y < P.length := List.idxOf_lt_length_of_mem hy
      omega
    have hidx_x : (P ++ R).idxOf x = P.idxOf x := List.idxOf_append_of_mem hxP
    rw [hidx_x, hidx_y] at hlt
    exact ⟨hxP, Or.inl ⟨hxP, hy, hlt⟩⟩
  · exact absurd hyQ hyNot
  · exact absurd hyQ hyNot

private lemma compLT_prefix_right {P Q : List ℕ} (hpre : P <+: Q) {x y : ℕ}
    (hx : x ∈ P) (hy : y ∉ P) : compLT Q x y := by
  rcases hpre with ⟨R, rfl⟩
  have hxQ : x ∈ P ++ R := List.mem_append_left R hx
  by_cases hyQ : y ∈ P ++ R
  · refine Or.inl ⟨hxQ, hyQ, ?_⟩
    rw [List.idxOf_append_of_mem hx, List.idxOf_append_of_notMem hy]
    have hx_lt : P.idxOf x < P.length := List.idxOf_lt_length_of_mem hx
    omega
  · exact Or.inr (Or.inl ⟨hxQ, hyQ⟩)

/-! ### Part 3: Lemma 1 — Finite sets sorted in reverse rlex order are safe -/

private noncomputable def insertRev (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if rlex y x then x :: y :: ys else y :: insertRev x ys

private noncomputable def sortRev : List ℕ → List ℕ
  | [] => []
  | x :: xs => insertRev x (sortRev xs)

private lemma insertRev_perm (x : ℕ) : ∀ xs : List ℕ, (insertRev x xs).Perm (x :: xs)
  | [] => List.Perm.refl _
  | y :: ys => by
      unfold insertRev
      split_ifs
      · exact List.Perm.refl _
      · exact ((insertRev_perm x ys).cons y).trans (List.Perm.swap x y ys)

private lemma sortRev_perm : ∀ xs : List ℕ, (sortRev xs).Perm xs
  | [] => List.Perm.refl _
  | x :: xs => (insertRev_perm x _).trans ((sortRev_perm xs).cons x)

private lemma insertRev_pairwise (x : ℕ) :
    ∀ {xs : List ℕ}, xs.Nodup → x ∉ xs → xs.Pairwise (fun a b => rlex b a) →
      (insertRev x xs).Pairwise (fun a b => rlex b a)
  | [], _, _, _ => List.pairwise_singleton _ _
  | y :: ys, hnd, hxnot, hpw => by
      unfold insertRev
      have hxy_ne : x ≠ y := fun h => hxnot (h ▸ List.mem_cons_self ..)
      have hxys : x ∉ ys := fun h => hxnot (List.mem_cons_of_mem y h)
      rcases List.nodup_cons.mp hnd with ⟨_, hys_nd⟩
      rcases List.pairwise_cons.mp hpw with ⟨hy_all, hys_pw⟩
      split_ifs with hyx
      · refine List.pairwise_cons.mpr ⟨fun z hz => ?_, hpw⟩
        rcases List.mem_cons.mp hz with rfl | hzy
        · exact hyx
        · exact rlex_trans (hy_all z hzy) hyx
      · have hxy : rlex x y := (rlex_total hxy_ne).resolve_right hyx
        refine List.pairwise_cons.mpr ⟨fun z hz => ?_, insertRev_pairwise x hys_nd hxys hys_pw⟩
        have hmem : z ∈ x :: ys := (insertRev_perm x ys).subset hz
        rcases List.mem_cons.mp hmem with rfl | hzy
        · exact hxy
        · exact hy_all z hzy

private lemma sortRev_pairwise :
    ∀ {xs : List ℕ}, xs.Nodup → (sortRev xs).Pairwise (fun a b => rlex b a)
  | [], _ => List.Pairwise.nil
  | x :: xs, hnd => by
      rcases List.nodup_cons.mp hnd with ⟨hxnot, hxs_nd⟩
      have hperm := sortRev_perm xs
      exact insertRev_pairwise x (hperm.nodup_iff.mpr hxs_nd)
        (fun h => hxnot (hperm.mem_iff.mp h)) (sortRev_pairwise hxs_nd)

private lemma idxOf_lt_imp_pairwise {P : List ℕ} {R : ℕ → ℕ → Prop}
    (hpw : P.Pairwise R) {x y : ℕ} (hx : x ∈ P) (hy : y ∈ P)
    (hlt : P.idxOf x < P.idxOf y) : R x y := by
  have hx_lt : P.idxOf x < P.length := List.idxOf_lt_length_of_mem hx
  have hy_lt : P.idxOf y < P.length := List.idxOf_lt_length_of_mem hy
  have hget := List.pairwise_iff_getElem.mp hpw (P.idxOf x) (P.idxOf y) hx_lt hy_lt hlt
  rwa [List.getElem_idxOf hx_lt, List.getElem_idxOf hy_lt] at hget

private lemma safe_of_pairwise_rev {P : List ℕ} (hnd : P.Nodup)
    (hpw : P.Pairwise (fun a b => rlex b a)) : Safe P := by
  refine ⟨hnd, fun a b c d hap ⟨hab, hbc, hcd⟩ => ?_⟩
  have h1 : ∀ u v, compLT P u v → v ∈ P → u ∈ P := fun u v huv hv => by
    rcases huv with ⟨hu, _, _⟩ | ⟨_, hnv⟩ | ⟨_, hnv, _⟩
    · exact hu
    · exact absurd hv hnv
    · exact absurd hv hnv
  by_cases hcP : c ∈ P
  · have hbP : b ∈ P := h1 b c hbc hcP
    have haP : a ∈ P := h1 a b hab hbP
    have hba : rlex b a := by
      rcases hab with ⟨_, _, hlt⟩ | ⟨_, hnb⟩ | ⟨_, hnb, _⟩
      · exact idxOf_lt_imp_pairwise hpw haP hbP hlt
      · exact absurd hbP hnb
      · exact absurd hbP hnb
    have hcb : rlex c b := by
      rcases hbc with ⟨_, _, hlt⟩ | ⟨_, hnc⟩ | ⟨_, hnc, _⟩
      · exact idxOf_lt_imp_pairwise hpw hbP hcP hlt
      · exact absurd hcP hnc
      · exact absurd hcP hnc
    exact (rlex_no_3ap hap.1 hap.2.1).2 ⟨hcb, hba⟩
  · by_cases hbP : b ∈ P
    · have haP : a ∈ P := h1 a b hab hbP
      have hdP : d ∉ P := fun hdP => hcP (h1 c d hcd hdP)
      have hba : rlex b a := by
        rcases hab with ⟨_, _, hlt⟩ | ⟨_, hnb⟩ | ⟨_, hnb, _⟩
        · exact idxOf_lt_imp_pairwise hpw haP hbP hlt
        · exact absurd hbP hnb
        · exact absurd hbP hnb
      have hcd_r : rlex c d := by
        rcases hcd with ⟨hc', _, _⟩ | ⟨hc', _⟩ | ⟨_, _, hr⟩
        · exact absurd hc' hcP
        · exact absurd hc' hcP
        · exact hr
      have hab_r : rlex a b := (rlex_4ap_iff hap).mpr hcd_r
      exact rlex_asymm hab_r hba
    · have hdP : d ∉ P := fun hdP => hcP (h1 c d hcd hdP)
      have hbc_r : rlex b c := by
        rcases hbc with ⟨hb', _, _⟩ | ⟨hb', _⟩ | ⟨_, _, hr⟩
        · exact absurd hb' hbP
        · exact absurd hb' hbP
        · exact hr
      have hcd_r : rlex c d := by
        rcases hcd with ⟨hc', _, _⟩ | ⟨hc', _⟩ | ⟨_, _, hr⟩
        · exact absurd hc' hcP
        · exact absurd hc' hcP
        · exact hr
      have hbc_ne : b ≠ c := by
        rcases hap with ⟨hne, habc, _⟩; omega
      exact (rlex_no_3ap hbc_ne hap.2.2).1 ⟨hbc_r, hcd_r⟩

/-! ### Part 4: Parity decomposition lemmas for lists -/

private def evenPart (P : List ℕ) : List ℕ :=
  (P.filter (fun x => x % 2 == 0)).map (· / 2)

private def oddPart (P : List ℕ) : List ℕ :=
  (P.filter (fun x => x % 2 == 1)).map (· / 2)

private lemma mem_evenPart (P : List ℕ) (x : ℕ) : x ∈ evenPart P ↔ 2 * x ∈ P := by
  simp only [evenPart, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨y, ⟨hyP, hy0⟩, rfl⟩
    have : 2 * (y / 2) = y := by omega
    rwa [this]
  · intro hx
    exact ⟨2 * x, ⟨hx, by omega⟩, by omega⟩

private lemma mem_oddPart (P : List ℕ) (x : ℕ) : x ∈ oddPart P ↔ 2 * x + 1 ∈ P := by
  simp only [oddPart, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨y, ⟨hyP, hy1⟩, rfl⟩
    have : 2 * (y / 2) + 1 = y := by omega
    rwa [this]
  · intro hx
    exact ⟨2 * x + 1, ⟨hx, by omega⟩, by omega⟩

private lemma nodup_evenPart {P : List ℕ} (hnd : P.Nodup) : (evenPart P).Nodup := by
  unfold evenPart
  refine List.Nodup.map_on ?_ (hnd.filter _)
  intro a ha b hb hab
  simp only [List.mem_filter, beq_iff_eq] at ha hb
  omega

private lemma nodup_oddPart {P : List ℕ} (hnd : P.Nodup) : (oddPart P).Nodup := by
  unfold oddPart
  refine List.Nodup.map_on ?_ (hnd.filter _)
  intro a ha b hb hab
  simp only [List.mem_filter, beq_iff_eq] at ha hb
  omega

private lemma idxOf_filter_lt {p : ℕ → Bool} :
    ∀ (P : List ℕ) {x y : ℕ}, x ∈ P → y ∈ P → p x = true → p y = true →
      ((P.filter p).idxOf x < (P.filter p).idxOf y ↔ P.idxOf x < P.idxOf y)
  | [], _, _, hx, _, _, _ => by simp at hx
  | a :: as, x, y, hx, hy, hpx, hpy => by
      by_cases hxa : a = x
      · subst hxa
        simp only [List.filter_cons, hpx, ite_true, List.idxOf_cons_self]
        by_cases hya : a = y
        · subst hya; simp
        · have hyas : y ∈ as := (List.mem_cons.mp hy).resolve_left (Ne.symm hya)
          simp only [List.idxOf_cons_ne _ hya]
          have : 0 < (as.filter p).idxOf y + 1 := Nat.succ_pos _
          have : 0 < as.idxOf y + 1 := Nat.succ_pos _
          simp
      · by_cases hya : a = y
        · subst hya
          simp only [List.filter_cons, hpy, ite_true, List.idxOf_cons_self,
            List.idxOf_cons_ne _ hxa]
          simp
        · have hxas : x ∈ as := (List.mem_cons.mp hx).resolve_left (Ne.symm hxa)
          have hyas : y ∈ as := (List.mem_cons.mp hy).resolve_left (Ne.symm hya)
          simp only [List.filter_cons, List.idxOf_cons_ne _ hxa, List.idxOf_cons_ne _ hya]
          split_ifs
          · simp only [List.idxOf_cons_ne _ hxa, List.idxOf_cons_ne _ hya, Nat.succ_lt_succ_iff]
            exact idxOf_filter_lt as hxas hyas hpx hpy
          · simp only [Nat.succ_lt_succ_iff]
            exact idxOf_filter_lt as hxas hyas hpx hpy

private lemma idxOf_map_lt {f : ℕ → ℕ} :
    ∀ (L : List ℕ) {x y : ℕ}, (∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) → x ∈ L → y ∈ L →
      ((L.map f).idxOf (f x) < (L.map f).idxOf (f y) ↔ L.idxOf x < L.idxOf y)
  | [], _, _, _, hx, _ => by simp at hx
  | a :: as, x, y, hinj, hx, hy => by
      have hfa_x : f a = f x ↔ a = x :=
        ⟨fun h => hinj a (List.mem_cons_self ..) x hx h, congrArg f⟩
      have hfa_y : f a = f y ↔ a = y :=
        ⟨fun h => hinj a (List.mem_cons_self ..) y hy h, congrArg f⟩
      by_cases hxa : a = x
      · subst hxa
        simp only [List.map_cons, List.idxOf_cons_self]
        by_cases hya : a = y
        · subst hya; simp
        · have hfya : f a ≠ f y := fun h => hya (hfa_y.mp h)
          simp [List.idxOf_cons_ne _ hya, List.idxOf_cons_ne _ hfya]
      · by_cases hya : a = y
        · subst hya
          have hfxa : f a ≠ f x := fun h => hxa (hfa_x.mp h)
          simp [List.map_cons, List.idxOf_cons_self, List.idxOf_cons_ne _ hxa,
            List.idxOf_cons_ne _ hfxa]
        · have hxas : x ∈ as := (List.mem_cons.mp hx).resolve_left (Ne.symm hxa)
          have hyas : y ∈ as := (List.mem_cons.mp hy).resolve_left (Ne.symm hya)
          have hfxa : f a ≠ f x := fun h => hxa (hfa_x.mp h)
          have hfya : f a ≠ f y := fun h => hya (hfa_y.mp h)
          simp only [List.map_cons, List.idxOf_cons_ne _ hxa, List.idxOf_cons_ne _ hya,
            List.idxOf_cons_ne _ hfxa, List.idxOf_cons_ne _ hfya, Nat.succ_lt_succ_iff]
          exact idxOf_map_lt as
            (fun u hu v hv => hinj u (List.mem_cons_of_mem a hu) v (List.mem_cons_of_mem a hv))
            hxas hyas

private lemma compLT_evenPart (P : List ℕ) (x y : ℕ) :
    compLT (evenPart P) x y ↔ compLT P (2 * x) (2 * y) := by
  unfold compLT
  rw [mem_evenPart, mem_evenPart, rlex_two_mul]
  constructor
  · rintro (⟨hx, hy, hlt⟩ | h | h)
    · refine Or.inl ⟨hx, hy, ?_⟩
      have hx' : (2 * x) / 2 = x := by omega
      have hy' : (2 * y) / 2 = y := by omega
      rw [← hx', ← hy'] at hlt
      unfold evenPart at hlt
      rw [idxOf_map_lt (f := (· / 2)) (P.filter (fun z => z % 2 == 0))
        (fun a ha b hb hab => by
          simp only [List.mem_filter, beq_iff_eq] at ha hb; omega)
        (List.mem_filter.mpr ⟨hx, by simp⟩)
        (List.mem_filter.mpr ⟨hy, by simp⟩)] at hlt
      exact (idxOf_filter_lt P hx hy (by simp) (by simp)).mp hlt
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨hx, hy, hlt⟩ | h | h)
    · refine Or.inl ⟨hx, hy, ?_⟩
      have hx' : (2 * x) / 2 = x := by omega
      have hy' : (2 * y) / 2 = y := by omega
      rw [← hx', ← hy']
      unfold evenPart
      rw [idxOf_map_lt (f := (· / 2)) (P.filter (fun z => z % 2 == 0))
        (fun a ha b hb hab => by
          simp only [List.mem_filter, beq_iff_eq] at ha hb; omega)
        (List.mem_filter.mpr ⟨hx, by simp⟩)
        (List.mem_filter.mpr ⟨hy, by simp⟩)]
      exact (idxOf_filter_lt P hx hy (by simp) (by simp)).mpr hlt
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

private lemma compLT_oddPart (P : List ℕ) (x y : ℕ) :
    compLT (oddPart P) x y ↔ compLT P (2 * x + 1) (2 * y + 1) := by
  unfold compLT
  rw [mem_oddPart, mem_oddPart, rlex_two_mul_add_one]
  constructor
  · rintro (⟨hx, hy, hlt⟩ | h | h)
    · refine Or.inl ⟨hx, hy, ?_⟩
      have hx' : (2 * x + 1) / 2 = x := by omega
      have hy' : (2 * y + 1) / 2 = y := by omega
      rw [← hx', ← hy'] at hlt
      unfold oddPart at hlt
      rw [idxOf_map_lt (f := (· / 2)) (P.filter (fun z => z % 2 == 1))
        (fun a ha b hb hab => by
          simp only [List.mem_filter, beq_iff_eq] at ha hb; omega)
        (List.mem_filter.mpr ⟨hx, by simp⟩)
        (List.mem_filter.mpr ⟨hy, by simp⟩)] at hlt
      exact (idxOf_filter_lt P hx hy (by simp) (by simp)).mp hlt
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨hx, hy, hlt⟩ | h | h)
    · refine Or.inl ⟨hx, hy, ?_⟩
      have hx' : (2 * x + 1) / 2 = x := by omega
      have hy' : (2 * y + 1) / 2 = y := by omega
      rw [← hx', ← hy']
      unfold oddPart
      rw [idxOf_map_lt (f := (· / 2)) (P.filter (fun z => z % 2 == 1))
        (fun a ha b hb hab => by
          simp only [List.mem_filter, beq_iff_eq] at ha hb; omega)
        (List.mem_filter.mpr ⟨hx, by simp⟩)
        (List.mem_filter.mpr ⟨hy, by simp⟩)]
      exact (idxOf_filter_lt P hx hy (by simp) (by simp)).mpr hlt
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

private lemma safe_evenPart {P : List ℕ} (hP : Safe P) : Safe (evenPart P) := by
  refine ⟨nodup_evenPart hP.1, fun a b c d hap ⟨hab, hbc, hcd⟩ => ?_⟩
  rw [compLT_evenPart] at hab hbc hcd
  have hap2 : Is4AP (2 * a) (2 * b) (2 * c) (2 * d) := by
    rcases hap with ⟨hne, h1, h2⟩
    exact ⟨by omega, by omega, by omega⟩
  exact hP.2 _ _ _ _ hap2 ⟨hab, hbc, hcd⟩

private lemma safe_oddPart {P : List ℕ} (hP : Safe P) : Safe (oddPart P) := by
  refine ⟨nodup_oddPart hP.1, fun a b c d hap ⟨hab, hbc, hcd⟩ => ?_⟩
  rw [compLT_oddPart] at hab hbc hcd
  have hap2 : Is4AP (2 * a + 1) (2 * b + 1) (2 * c + 1) (2 * d + 1) := by
    rcases hap with ⟨hne, h1, h2⟩
    exact ⟨by omega, by omega, by omega⟩
  exact hP.2 _ _ _ _ hap2 ⟨hab, hbc, hcd⟩

private lemma evenPart_append (A B : List ℕ) : evenPart (A ++ B) = evenPart A ++ evenPart B := by
  simp [evenPart, List.filter_append, List.map_append]

private lemma oddPart_append (A B : List ℕ) : oddPart (A ++ B) = oddPart A ++ oddPart B := by
  simp [oddPart, List.filter_append, List.map_append]

private lemma evenPart_map_two_mul (L : List ℕ) : evenPart (L.map (2 * ·)) = L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      simp only [evenPart, List.map_cons, List.filter_cons] at ih ⊢
      have hmod : (2 * x % 2 == 0) = true := by simp
      rw [hmod]
      simp only [ite_true, List.map_cons]
      have hdiv : 2 * x / 2 = x := by omega
      rw [hdiv, ih]

private lemma oddPart_map_two_mul (L : List ℕ) : oddPart (L.map (2 * ·)) = [] := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      simp only [oddPart, List.map_cons, List.filter_cons] at ih ⊢
      have hmod : (2 * x % 2 == 1) = false := by simp
      rw [hmod]
      simp [ih]

private lemma oddPart_map_two_mul_add_one (L : List ℕ) : oddPart (L.map (fun x => 2 * x + 1)) = L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      simp only [oddPart, List.map_cons, List.filter_cons] at ih ⊢
      have hmod : ((2 * x + 1) % 2 == 1) = true := by simp
      rw [hmod]
      simp only [ite_true, List.map_cons]
      have hdiv : (2 * x + 1) / 2 = x := by omega
      rw [hdiv, ih]

private lemma evenPart_map_two_mul_add_one (L : List ℕ) : evenPart (L.map (fun x => 2 * x + 1)) = [] := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      simp only [evenPart, List.map_cons, List.filter_cons] at ih ⊢
      have hmod : ((2 * x + 1) % 2 == 0) = false := by simp
      rw [hmod]
      simp [ih]

/-! ### Part 5: Lemma 2 — Safe extension lemma (Boon Suan Ho, arXiv:2609.12780) -/

private lemma exists_safe_extension :
    ∀ m : ℕ, ∀ P : List ℕ, Safe P → (∀ x ∈ P, x ≤ m) → ∀ T : Finset ℕ,
      ∃ Q : List ℕ, Safe Q ∧ P <+: Q ∧ ∀ t ∈ T, t ∈ Q := by
  intro m
  induction m with
  | zero =>
      intro P hP hle T
      let S : Finset ℕ := P.toFinset ∪ T
      let Q : List ℕ := sortRev S.toList
      have hQ_perm : Q.Perm S.toList := sortRev_perm S.toList
      have hQ_nd : Q.Nodup := hQ_perm.nodup_iff.mpr S.nodup_toList
      have hQ_pw : Q.Pairwise (fun a b => rlex b a) := sortRev_pairwise S.nodup_toList
      have hQ_mem : ∀ x, x ∈ Q ↔ x ∈ P ∨ x ∈ T := fun x => by
        rw [hQ_perm.mem_iff, Finset.mem_toList]
        simp [S]
      have hpre : P <+: Q := by
        cases P with
        | nil => exact List.nil_prefix
        | cons x xs =>
            have hx0 : x = 0 := Nat.le_zero.mp (hle x (List.mem_cons_self ..))
            subst hx0
            have hxs_nil : xs = [] := by
              cases xs with
              | nil => rfl
              | cons y ys =>
                  have hy0 : y = 0 := Nat.le_zero.mp (hle y (List.mem_cons_of_mem 0 (List.mem_cons_self ..)))
                  subst hy0
                  exact absurd (List.mem_cons_self ..) (List.nodup_cons.mp hP.1).1
            subst hxs_nil
            have h0Q : 0 ∈ Q := (hQ_mem 0).mpr (Or.inl (List.mem_cons_self ..))
            cases hQeq : Q with
            | nil => rw [hQeq] at h0Q; simp at h0Q
            | cons q qs =>
                have hq0 : q = 0 := by
                  by_contra hne
                  rw [hQeq] at h0Q hQ_pw
                  have h0qs : 0 ∈ qs := (List.mem_cons.mp h0Q).resolve_left (Ne.symm hne)
                  have hrel : rlex 0 q := (List.pairwise_cons.mp hQ_pw).1 0 h0qs
                  exact rlex_asymm (rlex_zero hne) hrel
                subst hq0
                exact ⟨qs, rfl⟩
      exact ⟨Q, safe_of_pairwise_rev hQ_nd hQ_pw, hpre, fun t ht => (hQ_mem t).mpr (Or.inr ht)⟩
  | succ m ih =>
      intro P hP hle T
      let P0 := evenPart P
      let P1 := oddPart P
      have hP0_safe : Safe P0 := safe_evenPart hP
      have hP1_safe : Safe P1 := safe_oddPart hP
      have hP0_le : ∀ x ∈ P0, x ≤ m := by
        intro x hx
        have := hle (2 * x) ((mem_evenPart P x).mp hx)
        omega
      have hP1_le : ∀ x ∈ P1, x ≤ m := by
        intro x hx
        have := hle (2 * x + 1) ((mem_oddPart P x).mp hx)
        omega
      -- Extend even part
      let T0 : Finset ℕ := (T.filter (fun t => t % 2 = 0)).image (· / 2)
      rcases ih P0 hP0_safe hP0_le T0 with ⟨R0, hR0_safe, ⟨E0, hR0_eq⟩, hT0_mem⟩
      let E : List ℕ := E0.map (2 * ·)
      let h : ℕ := E.foldr max 0
      have hE_le : ∀ x ∈ E, x ≤ h := by
        have hgo : ∀ L : List ℕ, ∀ x ∈ L, x ≤ L.foldr max 0 := by
          intro L
          induction L with
          | nil => intro x hx; simp at hx
          | cons a as iha =>
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hmem
              · exact le_max_left _ _
              · exact le_trans (iha x hmem) (le_max_right _ _)
        exact hgo E
      -- Extend odd part with extra targets < h
      let T1 : Finset ℕ := (T.filter (fun t => t % 2 = 1)).image (· / 2) ∪ Finset.range h
      rcases ih P1 hP1_safe hP1_le T1 with ⟨R1, hR1_safe, ⟨O1, hR1_eq⟩, hT1_mem⟩
      let O : List ℕ := O1.map (fun x => 2 * x + 1)
      let Q : List ℕ := P ++ O ++ E
      have hE0_nd : E0.Nodup := by
        have := hR0_safe.1; rw [← hR0_eq, List.nodup_append] at this; exact this.2.1
      have hO1_nd : O1.Nodup := by
        have := hR1_safe.1; rw [← hR1_eq, List.nodup_append] at this; exact this.2.1
      have hE0_disj : ∀ x ∈ E0, x ∉ P0 := by
        have := hR0_safe.1; rw [← hR0_eq, List.nodup_append] at this
        intro x hxE hxP; exact this.2.2 x hxP x hxE rfl
      have hO1_disj : ∀ x ∈ O1, x ∉ P1 := by
        have := hR1_safe.1; rw [← hR1_eq, List.nodup_append] at this
        intro x hxO hxP; exact this.2.2 x hxP x hxO rfl
      have hE_nd : E.Nodup := hE0_nd.map (fun a b hab => by omega)
      have hO_nd : O.Nodup := hO1_nd.map (fun a b hab => by omega)
      have hO_even_odd : ∀ y ∈ O, y % 2 = 1 := by
        intro y hy
        rcases List.mem_map.mp hy with ⟨k, _, rfl⟩; omega
      have hE_even : ∀ x ∈ E, x % 2 = 0 := by
        intro x hx
        rcases List.mem_map.mp hx with ⟨k, _, rfl⟩; omega
      have hO_notP : ∀ y ∈ O, y ∉ P := by
        intro y hy hyP
        rcases List.mem_map.mp hy with ⟨k, hk, rfl⟩
        exact hO1_disj k hk ((mem_oddPart P k).mpr hyP)
      have hE_notP : ∀ x ∈ E, x ∉ P := by
        intro x hx hxP
        rcases List.mem_map.mp hx with ⟨k, hk, rfl⟩
        exact hE0_disj k hk ((mem_evenPart P k).mpr hxP)
      have hQ_nd : Q.Nodup := by
        rw [show Q = P ++ (O ++ E) by simp [Q, List.append_assoc], List.nodup_append]
        refine ⟨hP.1, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨hO_nd, hE_nd, fun a ha b hb hab => ?_⟩
          have h1 := hO_even_odd a ha
          have h2 := hE_even b hb
          omega
        · intro a ha b hb hab
          subst hab
          rcases List.mem_append.mp hb with hO | hE
          · exact hO_notP a hO ha
          · exact hE_notP a hE ha
      have hQ_even : evenPart Q = R0 := by
        simp only [Q, O, E, evenPart_append, evenPart_map_two_mul_add_one, evenPart_map_two_mul,
          List.append_nil, ← hR0_eq, P0]
      have hQ_odd : oddPart Q = R1 := by
        simp only [Q, O, E, oddPart_append, oddPart_map_two_mul_add_one, oddPart_map_two_mul,
          List.append_nil, ← hR1_eq, P1]
      have hP_pre_Q : P <+: Q := ⟨O ++ E, by simp [Q, List.append_assoc]⟩
      -- Key Property (2): for x, y ∉ P with x even, y odd, y ≤ 2 * x, y precedes x in compLT Q
      have hprop2 : ∀ x y : ℕ, x ∉ P → y ∉ P → x % 2 = 0 → y % 2 = 1 → y ≤ 2 * x →
          compLT Q y x := by
        intro x y hxP hyP hx_ev hy_od hyx
        by_cases hxE : x ∈ E
        · have hx_le : x ≤ h := hE_le x hxE
          have hy_div : y / 2 < h := by omega
          have hy_R1 : y / 2 ∈ R1 := hT1_mem (y / 2) (Finset.mem_union_right _ (Finset.mem_range.mpr hy_div))
          rw [← hR1_eq, List.mem_append] at hy_R1
          have hy_O1 : y / 2 ∈ O1 := hy_R1.resolve_left (fun hP1 => hyP (by
            have hmem := (mem_oddPart P (y / 2)).mp hP1
            have : 2 * (y / 2) + 1 = y := by omega
            rwa [this] at hmem))
          have hyO : y ∈ O := List.mem_map.mpr ⟨y / 2, hy_O1, by omega⟩
          have hyQ : y ∈ Q := by simp [Q, hyO]
          have hxQ : x ∈ Q := by simp [Q, hxE]
          refine Or.inl ⟨hyQ, hxQ, ?_⟩
          have hyPO : y ∈ P ++ O := List.mem_append_right P hyO
          have hxPO : x ∉ P ++ O := by
            intro hmem
            rcases List.mem_append.mp hmem with h1 | h2
            · exact hxP h1
            · have := hO_even_odd x h2; omega
          change (P ++ O ++ E).idxOf y < (P ++ O ++ E).idxOf x
          rw [List.idxOf_append_of_mem hyPO, List.idxOf_append_of_notMem hxPO]
          have := List.idxOf_lt_length_of_mem hyPO
          omega
        · have hxQ : x ∉ Q := by
            simp only [Q, List.mem_append, not_or]
            refine ⟨⟨hxP, fun hxO => ?_⟩, hxE⟩
            have := hO_even_odd x hxO; omega
          by_cases hyQ : y ∈ Q
          · exact Or.inr (Or.inl ⟨hyQ, hxQ⟩)
          · refine Or.inr (Or.inr ⟨hyQ, hxQ, ?_⟩)
            have hx2 : x = 2 * (x / 2) := by omega
            have hy2 : y = 2 * (y / 2) + 1 := by omega
            rw [hy2, hx2]
            exact rlex_odd_even _ _
      -- Verify Q is safe
      have hQ_safe : Safe Q := by
        refine ⟨hQ_nd, fun a b c d hap ⟨hab, hbc, hcd⟩ => ?_⟩
        by_cases hpar : a % 2 = b % 2
        · -- Same parity: reduce to R0 or R1
          have hc_par : c % 2 = a % 2 := by rcases hap with ⟨_, h1, _⟩; omega
          have hd_par : d % 2 = a % 2 := by rcases hap with ⟨_, _, h2⟩; omega
          by_cases ha0 : a % 2 = 0
          · have ha2 : a = 2 * (a / 2) := by omega
            have hb2 : b = 2 * (b / 2) := by omega
            have hc2 : c = 2 * (c / 2) := by omega
            have hd2 : d = 2 * (d / 2) := by omega
            rw [ha2, hb2] at hab; rw [hb2, hc2] at hbc; rw [hc2, hd2] at hcd
            rw [← compLT_evenPart, hQ_even] at hab hbc hcd
            have hap' : Is4AP (a / 2) (b / 2) (c / 2) (d / 2) := by
              rcases hap with ⟨hne, h1, h2⟩; exact ⟨by omega, by omega, by omega⟩
            exact hR0_safe.2 _ _ _ _ hap' ⟨hab, hbc, hcd⟩
          · have ha2 : a = 2 * (a / 2) + 1 := by omega
            have hb2 : b = 2 * (b / 2) + 1 := by omega
            have hc2 : c = 2 * (c / 2) + 1 := by omega
            have hd2 : d = 2 * (d / 2) + 1 := by omega
            rw [ha2, hb2] at hab; rw [hb2, hc2] at hbc; rw [hc2, hd2] at hcd
            rw [← compLT_oddPart, hQ_odd] at hab hbc hcd
            have hap' : Is4AP (a / 2) (b / 2) (c / 2) (d / 2) := by
              rcases hap with ⟨hne, h1, h2⟩; exact ⟨by omega, by omega, by omega⟩
            exact hR1_safe.2 _ _ _ _ hap' ⟨hab, hbc, hcd⟩
        · -- Alternating parity
          have hc_notP : c ∉ P := by
            intro hcP
            rcases compLT_prefix_left hP_pre_Q hcP hbc with ⟨hbP, hbcP⟩
            rcases compLT_prefix_left hP_pre_Q hbP hab with ⟨haP, habP⟩
            have hcdP : compLT P c d := by
              by_cases hdP : d ∈ P
              · exact (compLT_prefix_left hP_pre_Q hdP hcd).2
              · exact Or.inr (Or.inl ⟨hcP, hdP⟩)
            exact hP.2 a b c d hap ⟨habP, hbcP, hcdP⟩
          have hd_notP : d ∉ P := by
            intro hdP
            exact hc_notP (compLT_prefix_left hP_pre_Q hdP hcd).1
          have hcomp_asymm : ∀ u v, compLT Q u v → ¬ compLT Q v u := by
            intro u v h1 h2
            rcases h1 with ⟨hu, hv, hlt1⟩ | ⟨hu, hnv⟩ | ⟨hnu, hnv, hr1⟩
            · rcases h2 with ⟨_, _, hlt2⟩ | ⟨_, hnu⟩ | ⟨_, hnu, _⟩
              · omega
              · exact hnu hu
              · exact hnu hu
            · rcases h2 with ⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨_, hnu, _⟩
              · exact hnv hv
              · exact hnv hv
              · exact hnu hu
            · rcases h2 with ⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨_, _, hr2⟩
              · exact hnv hv
              · exact hnv hv
              · exact rlex_asymm hr1 hr2
          by_cases hc_ev : c % 2 = 0
          · have hd_od : d % 2 = 1 := by rcases hap with ⟨_, h1, h2⟩; omega
            have hd_le : d ≤ 2 * c := by rcases hap with ⟨_, _, h2⟩; omega
            exact hcomp_asymm c d hcd (hprop2 c d hc_notP hd_notP hc_ev hd_od hd_le)
          · have hc_od : c % 2 = 1 := by omega
            have hb_ev : b % 2 = 0 := by rcases hap with ⟨_, h1, _⟩; omega
            have hd_ev : d % 2 = 0 := by rcases hap with ⟨_, _, h2⟩; omega
            have hb_notP : b ∉ P := by
              intro hbP
              rcases compLT_prefix_left hP_pre_Q hbP hab with ⟨haP, habP⟩
              have hbcP : compLT P b c := Or.inr (Or.inl ⟨hbP, hc_notP⟩)
              have hcdP : compLT P c d := by
                refine Or.inr (Or.inr ⟨hc_notP, hd_notP, ?_⟩)
                have hc2 : c = 2 * (c / 2) + 1 := by omega
                have hd2 : d = 2 * (d / 2) := by omega
                rw [hc2, hd2]
                exact rlex_odd_even _ _
              exact hP.2 a b c d hap ⟨habP, hbcP, hcdP⟩
            have hc_le : c ≤ 2 * b := by rcases hap with ⟨_, h1, _⟩; omega
            exact hcomp_asymm b c hbc (hprop2 b c hb_notP hc_notP hb_ev hc_od hc_le)
      -- Verify T ⊆ Q
      have hT_sub : ∀ t ∈ T, t ∈ Q := by
        intro t ht
        by_cases ht0 : t % 2 = 0
        · have ht_R0 : t / 2 ∈ R0 :=
            hT0_mem (t / 2) (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, ht0⟩, rfl⟩)
          rw [← hQ_even, mem_evenPart] at ht_R0
          have : 2 * (t / 2) = t := by omega
          rwa [this] at ht_R0
        · have ht1 : t % 2 = 1 := by omega
          have ht_R1 : t / 2 ∈ R1 :=
            hT1_mem (t / 2) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, ht1⟩, rfl⟩))
          rw [← hQ_odd, mem_oddPart] at ht_R1
          have : 2 * (t / 2) + 1 = t := by omega
          rwa [this] at ht_R1
      exact ⟨Q, hQ_safe, hP_pre_Q, hT_sub⟩

/-! ### Part 6: Constructing the 4AP-free permutation of ℕ and shifting to ℕ+ -/

private lemma safe_nil : Safe [] := by
  refine ⟨List.nodup_nil, fun a b c d hap ⟨hab, hbc, _⟩ => ?_⟩
  rcases hab with ⟨h, _, _⟩ | ⟨h, _⟩ | ⟨_, _, hr1⟩
  · simp at h
  · simp at h
  · rcases hbc with ⟨h, _, _⟩ | ⟨h, _⟩ | ⟨_, _, hr2⟩
    · simp at h
    · simp at h
    · exact (rlex_no_3ap hap.1 hap.2.1).1 ⟨hr1, hr2⟩

private noncomputable def extendOne (P : {L : List ℕ // Safe L}) (n : ℕ) :
    {Q : List ℕ // Safe Q ∧ P.1 <+: Q ∧ n ∈ Q} :=
  let m := P.1.foldr max 0
  have hle : ∀ x ∈ P.1, x ≤ m := by
    have hgo : ∀ L : List ℕ, ∀ x ∈ L, x ≤ L.foldr max 0 := by
      intro L
      induction L with
      | nil => intro x hx; simp at hx
      | cons a as iha =>
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hmem
          · exact le_max_left _ _
          · exact le_trans (iha x hmem) (le_max_right _ _)
    exact hgo P.1
  let h := exists_safe_extension m P.1 P.2 hle {n}
  ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2.1,
    (Classical.choose_spec h).2.2 n (Finset.mem_singleton_self n)⟩

private noncomputable def stage : ℕ → {L : List ℕ // Safe L}
  | 0 => ⟨[], safe_nil⟩
  | n + 1 =>
      let res := extendOne (stage n) n
      ⟨res.1, res.2.1⟩

private lemma stage_prefix_succ (n : ℕ) : (stage n).1 <+: (stage (n + 1)).1 :=
  (extendOne (stage n) n).2.2.1

private lemma mem_stage_succ (n : ℕ) : n ∈ (stage (n + 1)).1 :=
  (extendOne (stage n) n).2.2.2

private lemma stage_prefix_mono {m n : ℕ} (h : m ≤ n) : (stage m).1 <+: (stage n).1 := by
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.mp h
      subst this; exact List.prefix_refl _
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact List.prefix_refl _
      · exact (ih (Nat.le_of_lt_succ hlt)).trans (stage_prefix_succ n)

private lemma mem_stage_of_lt {k n : ℕ} (h : k < n) : k ∈ (stage n).1 :=
  (stage_prefix_mono h).subset (mem_stage_succ k)

private lemma stage_length_ge (n : ℕ) : n ≤ (stage n).1.length := by
  have hsub : Finset.range n ⊆ (stage n).1.toFinset := by
    intro k hk
    exact List.mem_toFinset.mpr (mem_stage_of_lt (Finset.mem_range.mp hk))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range, List.toFinset_card_of_nodup (stage n).2.1] at hcard
  exact hcard

private lemma prefix_getElem {P Q : List ℕ} (hpre : P <+: Q) {i : ℕ} (hi : i < P.length) :
    Q[i]'(lt_of_lt_of_le hi hpre.length_le) = P[i] := by
  rcases hpre with ⟨R, rfl⟩
  exact List.getElem_append_left hi

private lemma prefix_idxOf {P Q : List ℕ} (hpre : P <+: Q) {x : ℕ} (hx : x ∈ P) :
    Q.idxOf x = P.idxOf x := by
  rcases hpre with ⟨R, rfl⟩
  exact List.idxOf_append_of_mem hx

private noncomputable def permNat : Equiv.Perm ℕ where
  toFun i := (stage (i + 1)).1[i]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (stage_length_ge (i + 1)))
  invFun x := (stage (x + 1)).1.idxOf x
  left_inv i := by
    dsimp only
    set x := (stage (i + 1)).1[i]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (stage_length_ge (i + 1)))
    set N := max (i + 1) (x + 1)
    have h1 : (stage (x + 1)).1.idxOf x = (stage N).1.idxOf x :=
      (prefix_idxOf (stage_prefix_mono (le_max_right _ _)) (mem_stage_succ x)).symm
    have hi1 : i < (stage (i + 1)).1.length :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (stage_length_ge (i + 1))
    have hpre1 : (stage (i + 1)).1 <+: (stage N).1 := stage_prefix_mono (le_max_left _ _)
    have hiN : i < (stage N).1.length := lt_of_lt_of_le hi1 hpre1.length_le
    have hgetN : (stage N).1[i]'hiN = x := prefix_getElem hpre1 hi1
    rw [h1, ← hgetN, List.Nodup.idxOf_getElem (stage N).2.1 i hiN]
  right_inv x := by
    dsimp only
    set i := (stage (x + 1)).1.idxOf x
    have hi_lt : i < (stage (x + 1)).1.length := List.idxOf_lt_length_of_mem (mem_stage_succ x)
    set N := max (i + 1) (x + 1)
    have hi1 : i < (stage (i + 1)).1.length :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (stage_length_ge (i + 1))
    have hpre1 : (stage (i + 1)).1 <+: (stage N).1 := stage_prefix_mono (le_max_left _ _)
    have hpre2 : (stage (x + 1)).1 <+: (stage N).1 := stage_prefix_mono (le_max_right _ _)
    have hget1 := prefix_getElem hpre1 hi1
    have hget2 := prefix_getElem hpre2 hi_lt
    rw [← hget1, hget2]
    exact List.getElem_idxOf hi_lt

private lemma permNat_4ap_free :
    ∀ a b c d : ℕ, Is4AP a b c d →
      ¬ (permNat.symm a < permNat.symm b ∧ permNat.symm b < permNat.symm c ∧
          permNat.symm c < permNat.symm d) := by
  intro a b c d hap ⟨h1, h2, h3⟩
  set N := max (max a b) (max c d) + 1
  have ha : a ∈ (stage N).1 := mem_stage_of_lt (by omega)
  have hb : b ∈ (stage N).1 := mem_stage_of_lt (by omega)
  have hc : c ∈ (stage N).1 := mem_stage_of_lt (by omega)
  have hd : d ∈ (stage N).1 := mem_stage_of_lt (by omega)
  have hia : permNat.symm a = (stage N).1.idxOf a :=
    (prefix_idxOf (stage_prefix_mono (by omega : a + 1 ≤ N)) (mem_stage_succ a)).symm
  have hib : permNat.symm b = (stage N).1.idxOf b :=
    (prefix_idxOf (stage_prefix_mono (by omega : b + 1 ≤ N)) (mem_stage_succ b)).symm
  have hic : permNat.symm c = (stage N).1.idxOf c :=
    (prefix_idxOf (stage_prefix_mono (by omega : c + 1 ≤ N)) (mem_stage_succ c)).symm
  have hid : permNat.symm d = (stage N).1.idxOf d :=
    (prefix_idxOf (stage_prefix_mono (by omega : d + 1 ≤ N)) (mem_stage_succ d)).symm
  rw [hia, hib] at h1
  rw [hib, hic] at h2
  rw [hic, hid] at h3
  exact (stage N).2.2 a b c d hap ⟨Or.inl ⟨ha, hb, h1⟩, Or.inl ⟨hb, hc, h2⟩, Or.inl ⟨hc, hd, h3⟩⟩

private def natEquivPNat : ℕ ≃ ℕ+ where
  toFun n := ⟨n + 1, Nat.succ_pos n⟩
  invFun p := p.val - 1
  left_inv n := by simp
  right_inv p := by
    rcases p with ⟨n, hn⟩
    apply PNat.eq
    show n - 1 + 1 = n
    omega

private noncomputable def permPNat : Equiv.Perm ℕ+ :=
  natEquivPNat.symm.trans (permNat.trans natEquivPNat)

private lemma permPNat_symm_lt (p q : ℕ+) :
    permPNat.symm p < permPNat.symm q ↔ permNat.symm (p.val - 1) < permNat.symm (q.val - 1) := by
  change (⟨permNat.symm (p.val - 1) + 1, _⟩ : ℕ+) < ⟨permNat.symm (q.val - 1) + 1, _⟩ ↔ _
  change permNat.symm (p.val - 1) + 1 < permNat.symm (q.val - 1) + 1 ↔ _
  omega

end OPGMonotone4APProof

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_monotone_4_term_arithmetic_progressions.main) := by
  intro hmain
  rcases hmain OPGMonotone4APProof.permPNat with ⟨a, d, hap⟩
  set x := a.val - 1
  set r := d.val
  have ha1 : 1 ≤ a.val := a.pos
  have hr : 0 < r := d.pos
  have h0 : a.val - 1 = x := rfl
  have h1 : (a + d).val - 1 = x + r := by
    change a.val + d.val - 1 = x + r; omega
  have h2 : (a + 2 * d).val - 1 = x + 2 * r := by
    change a.val + 2 * d.val - 1 = x + 2 * r; omega
  have h3 : (a + 3 * d).val - 1 = x + 3 * r := by
    change a.val + 3 * d.val - 1 = x + 3 * r; omega
  rcases hap with ⟨hab, hbc, hcd⟩ | ⟨hdc, hcb, hba⟩
  · rw [OPGMonotone4APProof.permPNat_symm_lt, h0, h1] at hab
    rw [OPGMonotone4APProof.permPNat_symm_lt, h1, h2] at hbc
    rw [OPGMonotone4APProof.permPNat_symm_lt, h2, h3] at hcd
    exact OPGMonotone4APProof.permNat_4ap_free x (x + r) (x + 2 * r) (x + 3 * r)
      ⟨by omega, by omega, by omega⟩ ⟨hab, hbc, hcd⟩
  · rw [OPGMonotone4APProof.permPNat_symm_lt, h3, h2] at hdc
    rw [OPGMonotone4APProof.permPNat_symm_lt, h2, h1] at hcb
    rw [OPGMonotone4APProof.permPNat_symm_lt, h1, h0] at hba
    exact OPGMonotone4APProof.permNat_4ap_free (x + 3 * r) (x + 2 * r) (x + r) x
      ⟨by omega, by omega, by omega⟩ ⟨hdc, hcb, hba⟩
