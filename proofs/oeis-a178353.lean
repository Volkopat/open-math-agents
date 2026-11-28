import OMAStatements.S_oeis_a178353

/-!
Double-counting proof of Mathar's closed form for collinear 4-point subsets
of the 7^n grid (OEIS A178353): classifying collinear 4-subsets by the
reduced common denominator q in {3, 4, 5, 6} of their collinear ratios
(accounting for (0, 2, 4, 6) belonging to q = 3 with step plus or minus 2) gives an exact
2-to-1 correspondence from directed parameterizations onto collinear 4-subsets.
-/

private def x03 : Fin 17 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 3, 3, 4, 5, 6, 0, 6]
private def d3 : Fin 17 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, -1, -1, -1, -1, 2, -2]
private def rev3 : Fin 17 → Fin 17 := ![0, 1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 7, 8, 9, 10, 16, 15]

private def step3 (c : Fin 17) (k : Fin 4) : Fin 7 :=
  ⟨(((x03 c : ℕ) : ℤ) + (k : ℕ) * d3 c).toNat, by
    fin_cases c <;> fin_cases k <;> decide⟩

private def x04 : Fin 13 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6, 0, 1, 2, 4, 5, 6]
private def d4 : Fin 13 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, -1, -1]
private def rev4 : Fin 13 → Fin 13 := ![0, 1, 2, 3, 4, 5, 6, 10, 11, 12, 7, 8, 9]
private def idx4 : Fin 3 → Fin 4 → ℤ
  | ⟨0, _⟩ => ![0, 2, 3, 4]
  | ⟨1, _⟩ => ![0, 1, 3, 4]
  | ⟨2, _⟩ => ![0, 1, 2, 4]
private def revM4 : Fin 3 → Fin 3 := ![2, 1, 0]

private def step4 (c : Fin 13) (m : Fin 3) (k : Fin 4) : Fin 7 :=
  ⟨(((x04 c : ℕ) : ℤ) + idx4 m k * d4 c).toNat, by
    fin_cases c <;> fin_cases m <;> fin_cases k <;> decide⟩

private def x05 : Fin 11 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6, 0, 1, 5, 6]
private def d5 : Fin 11 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1]
private def rev5 : Fin 11 → Fin 11 := ![0, 1, 2, 3, 4, 5, 6, 9, 10, 7, 8]
private def idx5 : Fin 6 → Fin 4 → ℤ
  | ⟨0, _⟩ => ![0, 1, 2, 5]
  | ⟨1, _⟩ => ![0, 1, 3, 5]
  | ⟨2, _⟩ => ![0, 1, 4, 5]
  | ⟨3, _⟩ => ![0, 2, 3, 5]
  | ⟨4, _⟩ => ![0, 2, 4, 5]
  | ⟨5, _⟩ => ![0, 3, 4, 5]
private def revM5 : Fin 6 → Fin 6 := ![5, 4, 2, 3, 1, 0]

private def step5 (c : Fin 11) (m : Fin 6) (k : Fin 4) : Fin 7 :=
  ⟨(((x05 c : ℕ) : ℤ) + idx5 m k * d5 c).toNat, by
    fin_cases c <;> fin_cases m <;> fin_cases k <;> decide⟩

private def x06 : Fin 9 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6, 0, 6]
private def d6 : Fin 9 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 1, -1]
private def rev6 : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 8, 7]
private def idx6 : Fin 9 → Fin 4 → ℤ
  | ⟨0, _⟩ => ![0, 1, 2, 6]
  | ⟨1, _⟩ => ![0, 1, 3, 6]
  | ⟨2, _⟩ => ![0, 1, 4, 6]
  | ⟨3, _⟩ => ![0, 1, 5, 6]
  | ⟨4, _⟩ => ![0, 2, 3, 6]
  | ⟨5, _⟩ => ![0, 2, 5, 6]
  | ⟨6, _⟩ => ![0, 3, 4, 6]
  | ⟨7, _⟩ => ![0, 3, 5, 6]
  | ⟨8, _⟩ => ![0, 4, 5, 6]
private def revM6 : Fin 9 → Fin 9 := ![8, 7, 5, 3, 6, 2, 4, 1, 0]

private def step6 (c : Fin 9) (m : Fin 9) (k : Fin 4) : Fin 7 :=
  ⟨(((x06 c : ℕ) : ℤ) + idx6 m k * d6 c).toNat, by
    fin_cases c <;> fin_cases m <;> fin_cases k <;> decide⟩

private lemma step3_val (c : Fin 17) (k : Fin 4) :
    ((step3 c k : ℕ) : ℤ) = ((x03 c : ℕ) : ℤ) + (k : ℕ) * d3 c := by
  fin_cases c <;> fin_cases k <;> decide

private lemma step4_val (c : Fin 13) (m : Fin 3) (k : Fin 4) :
    ((step4 c m k : ℕ) : ℤ) = ((x04 c : ℕ) : ℤ) + idx4 m k * d4 c := by
  fin_cases c <;> fin_cases m <;> fin_cases k <;> decide

private lemma step5_val (c : Fin 11) (m : Fin 6) (k : Fin 4) :
    ((step5 c m k : ℕ) : ℤ) = ((x05 c : ℕ) : ℤ) + idx5 m k * d5 c := by
  fin_cases c <;> fin_cases m <;> fin_cases k <;> decide

private lemma step6_val (c : Fin 9) (m : Fin 9) (k : Fin 4) :
    ((step6 c m k : ℕ) : ℤ) = ((x06 c : ℕ) : ℤ) + idx6 m k * d6 c := by
  fin_cases c <;> fin_cases m <;> fin_cases k <;> decide

private lemma rev3_invol (c : Fin 17) : rev3 (rev3 c) = c := by fin_cases c <;> decide
private lemma rev4_invol (c : Fin 13) : rev4 (rev4 c) = c := by fin_cases c <;> decide
private lemma rev5_invol (c : Fin 11) : rev5 (rev5 c) = c := by fin_cases c <;> decide
private lemma rev6_invol (c : Fin 9) : rev6 (rev6 c) = c := by fin_cases c <;> decide
private lemma revM4_invol (m : Fin 3) : revM4 (revM4 m) = m := by fin_cases m <;> decide
private lemma revM5_invol (m : Fin 6) : revM5 (revM5 m) = m := by fin_cases m <;> decide
private lemma revM6_invol (m : Fin 9) : revM6 (revM6 m) = m := by fin_cases m <;> decide

private lemma step3_rev (c : Fin 17) (k : Fin 4) :
    step3 (rev3 c) ⟨3 - k.val, by omega⟩ = step3 c k := by
  fin_cases c <;> fin_cases k <;> decide

private lemma step4_rev (c : Fin 13) (m : Fin 3) (k : Fin 4) :
    step4 (rev4 c) (revM4 m) ⟨3 - k.val, by omega⟩ = step4 c m k := by
  fin_cases c <;> fin_cases m <;> fin_cases k <;> decide

private lemma step5_rev (c : Fin 11) (m : Fin 6) (k : Fin 4) :
    step5 (rev5 c) (revM5 m) ⟨3 - k.val, by omega⟩ = step5 c m k := by
  fin_cases c <;> fin_cases m <;> fin_cases k <;> decide

private lemma step6_rev (c : Fin 9) (m : Fin 9) (k : Fin 4) :
    step6 (rev6 c) (revM6 m) ⟨3 - k.val, by omega⟩ = step6 c m k := by
  fin_cases c <;> fin_cases m <;> fin_cases k <;> decide

private lemma d3_rev (c : Fin 17) : d3 (rev3 c) = -d3 c := by fin_cases c <;> decide
private lemma d4_rev (c : Fin 13) : d4 (rev4 c) = -d4 c := by fin_cases c <;> decide
private lemma d5_rev (c : Fin 11) : d5 (rev5 c) = -d5 c := by fin_cases c <;> decide
private lemma d6_rev (c : Fin 9) : d6 (rev6 c) = -d6 c := by fin_cases c <;> decide

private lemma d3_cases (c : Fin 17) :
    d3 c = 0 ∨ d3 c = 1 ∨ d3 c = 2 ∨ d3 c = -1 ∨ d3 c = -2 := by fin_cases c <;> decide
private lemma d4_cases (c : Fin 13) : d4 c = 0 ∨ d4 c = 1 ∨ d4 c = -1 := by fin_cases c <;> decide
private lemma d5_cases (c : Fin 11) : d5 c = 0 ∨ d5 c = 1 ∨ d5 c = -1 := by fin_cases c <;> decide
private lemma d6_cases (c : Fin 9) : d6 c = 0 ∨ d6 c = 1 ∨ d6 c = -1 := by fin_cases c <;> decide

private lemma rev3_ne (c : Fin 17) (hc : d3 c ≠ 0) : rev3 c ≠ c := by
  fin_cases c <;> simp_all [d3, rev3]
private lemma rev4_ne (c : Fin 13) (hc : d4 c ≠ 0) : rev4 c ≠ c := by
  fin_cases c <;> simp_all [d4, rev4]
private lemma rev5_ne (c : Fin 11) (hc : d5 c ≠ 0) : rev5 c ≠ c := by
  fin_cases c <;> simp_all [d5, rev5]
private lemma rev6_ne (c : Fin 9) (hc : d6 c ≠ 0) : rev6 c ≠ c := by
  fin_cases c <;> simp_all [d6, rev6]

private lemma step3_inj_of_d_ne (c : Fin 17) (hc : d3 c ≠ 0) :
    Function.Injective (step3 c) := by
  fin_cases c <;> simp_all [d3] <;> decide

private lemma step4_inj_of_d_ne (c : Fin 13) (m : Fin 3) (hc : d4 c ≠ 0) :
    Function.Injective (step4 c m) := by
  fin_cases c <;> fin_cases m <;> simp_all [d4] <;> decide

private lemma step5_inj_of_d_ne (c : Fin 11) (m : Fin 6) (hc : d5 c ≠ 0) :
    Function.Injective (step5 c m) := by
  fin_cases c <;> fin_cases m <;> simp_all [d5] <;> decide

private lemma step6_inj_of_d_ne (c : Fin 9) (m : Fin 9) (hc : d6 c ≠ 0) :
    Function.Injective (step6 c m) := by
  fin_cases c <;> fin_cases m <;> simp_all [d6] <;> decide

private lemma d3_zero_iff (c : Fin 17) : d3 c = 0 ↔ c.val < 7 := by fin_cases c <;> decide
private lemma d4_zero_iff (c : Fin 13) : d4 c = 0 ↔ c.val < 7 := by fin_cases c <;> decide
private lemma d5_zero_iff (c : Fin 11) : d5 c = 0 ↔ c.val < 7 := by fin_cases c <;> decide
private lemma d6_zero_iff (c : Fin 9) : d6 c = 0 ↔ c.val < 7 := by fin_cases c <;> decide

private lemma exists_u3_of (a b : Fin 7) (h : ∃ k : ℤ, (b : ℤ) - (a : ℤ) = 3 * k) :
    ∃ c : Fin 17, x03 c = a ∧ 3 * d3 c = (b : ℤ) - (a : ℤ) := by
  rcases h with ⟨k, hk⟩
  fin_cases a <;> fin_cases b <;> first | (simp at hk; omega) | decide

private lemma uniq_u3 (c1 c2 : Fin 17) (hx : x03 c1 = x03 c2) (hd : 3 * d3 c1 = 3 * d3 c2) :
    c1 = c2 := by
  fin_cases c1 <;> fin_cases c2 <;> simp_all [x03, d3]

private lemma exists_u4_of (a b : Fin 7) (h : ∃ k : ℤ, (b : ℤ) - (a : ℤ) = 4 * k) :
    ∃ c : Fin 13, x04 c = a ∧ 4 * d4 c = (b : ℤ) - (a : ℤ) := by
  rcases h with ⟨k, hk⟩
  fin_cases a <;> fin_cases b <;> first | (simp at hk; omega) | decide

private lemma uniq_u4 (c1 c2 : Fin 13) (hx : x04 c1 = x04 c2) (hd : 4 * d4 c1 = 4 * d4 c2) :
    c1 = c2 := by
  fin_cases c1 <;> fin_cases c2 <;> simp_all [x04, d4]

private lemma exists_u5_of (a b : Fin 7) (h : ∃ k : ℤ, (b : ℤ) - (a : ℤ) = 5 * k) :
    ∃ c : Fin 11, x05 c = a ∧ 5 * d5 c = (b : ℤ) - (a : ℤ) := by
  rcases h with ⟨k, hk⟩
  fin_cases a <;> fin_cases b <;> first | (simp at hk; omega) | decide

private lemma uniq_u5 (c1 c2 : Fin 11) (hx : x05 c1 = x05 c2) (hd : 5 * d5 c1 = 5 * d5 c2) :
    c1 = c2 := by
  fin_cases c1 <;> fin_cases c2 <;> simp_all [x05, d5]

private lemma exists_u6_of (a b : Fin 7) (h : ∃ k : ℤ, (b : ℤ) - (a : ℤ) = 6 * k) :
    ∃ c : Fin 9, x06 c = a ∧ 6 * d6 c = (b : ℤ) - (a : ℤ) := by
  rcases h with ⟨k, hk⟩
  fin_cases a <;> fin_cases b <;> first | (simp at hk; omega) | decide

private lemma uniq_u6 (c1 c2 : Fin 9) (hx : x06 c1 = x06 c2) (hd : 6 * d6 c1 = 6 * d6 c2) :
    c1 = c2 := by
  fin_cases c1 <;> fin_cases c2 <;> simp_all [x06, d6]

private lemma fin4_strictMono_eq {f g : Fin 4 → ℕ} (hf : StrictMono f) (hg : StrictMono g)
    (him : Finset.univ.image f = Finset.univ.image g) : ∀ k : Fin 4, f k = g k := by
  have haux : ∀ n : ℕ, (hn : n < 4) → f ⟨n, hn⟩ = g ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have hfm : f ⟨n, hn⟩ ∈ Finset.univ.image g := by
        rw [← him]
        exact Finset.mem_image_of_mem f (Finset.mem_univ _)
      obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hfm
      have hgm : g ⟨n, hn⟩ ∈ Finset.univ.image f := by
        rw [him]
        exact Finset.mem_image_of_mem g (Finset.mem_univ _)
      obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hgm
      have hmn : m.val = n := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have heq := ih m.val hlt m.isLt
          have hltf : f m < f ⟨n, hn⟩ := hf (Fin.mk_lt_mk.mpr hlt)
          rw [heq, hm] at hltf
          exact lt_irrefl _ hltf
        · have hln : n ≤ l.val := by
            by_contra hln_lt
            push Not at hln_lt
            have heq := ih l.val hln_lt l.isLt
            have hltg : g l < g ⟨n, hn⟩ := hg (Fin.mk_lt_mk.mpr hln_lt)
            rw [← heq, hl] at hltg
            exact lt_irrefl _ hltg
          have hle : f ⟨n, hn⟩ ≤ f l := hf.monotone (Fin.mk_le_mk.mpr hln)
          have hltg : g ⟨n, hn⟩ < g m := hg (Fin.mk_lt_mk.mpr hgt)
          rw [hl] at hle
          rw [hm] at hltg
          omega
      have hmeq : m = ⟨n, hn⟩ := Fin.ext hmn
      rw [hmeq] at hm
      exact hm.symm
  intro k
  exact haux k.val k.isLt

private lemma idx4_inj (a b : Fin 3) (h1 : idx4 a 1 = idx4 b 1) (h2 : idx4 a 2 = idx4 b 2) :
    a = b := by
  fin_cases a <;> fin_cases b <;> revert h1 h2 <;> decide

private lemma idx5_inj (a b : Fin 6) (h1 : idx5 a 1 = idx5 b 1) (h2 : idx5 a 2 = idx5 b 2) :
    a = b := by
  fin_cases a <;> fin_cases b <;> revert h1 h2 <;> decide

private lemma idx6_inj (a b : Fin 9) (h1 : idx6 a 1 = idx6 b 1) (h2 : idx6 a 2 = idx6 b 2) :
    a = b := by
  fin_cases a <;> fin_cases b <;> revert h1 h2 <;> decide

private lemma idx6_ne_two_four (m : Fin 9) : ¬ (idx6 m 1 = 2 ∧ idx6 m 2 = 4) := by
  fin_cases m <;> decide

private def mkM5 (a b : ℕ) : Fin 6 :=
  if a = 1 then
    if b = 2 then 0 else if b = 3 then 1 else 2
  else if a = 2 then
    if b = 3 then 3 else 4
  else 5

private lemma idx5_mkM5 (a b : ℕ) (h1 : 0 < a) (h2 : a < b) (h3 : b < 5) :
    idx5 (mkM5 a b) 0 = 0 ∧ idx5 (mkM5 a b) 1 = (a : ℤ) ∧
    idx5 (mkM5 a b) 2 = (b : ℤ) ∧ idx5 (mkM5 a b) 3 = 5 := by
  have ha : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  have hb : b = 2 ∨ b = 3 ∨ b = 4 := by omega
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | omega | decide

private def mkM6 (a b : ℕ) : Fin 9 :=
  if a = 1 then
    if b = 2 then 0 else if b = 3 then 1 else if b = 4 then 2 else 3
  else if a = 2 then
    if b = 3 then 4 else 5
  else if a = 3 then
    if b = 4 then 6 else 7
  else 8

private lemma idx6_mkM6 (a b : ℕ) (h1 : 0 < a) (h2 : a < b) (h3 : b < 6)
    (hne : ¬ (a = 2 ∧ b = 4)) :
    idx6 (mkM6 a b) 0 = 0 ∧ idx6 (mkM6 a b) 1 = (a : ℤ) ∧
    idx6 (mkM6 a b) 2 = (b : ℤ) ∧ idx6 (mkM6 a b) 3 = 6 := by
  have ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
  have hb : b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    first | omega | decide

private abbrev WCode (n : ℕ) :=
  (Fin n → Fin 17) ⊕ ((Fin n → Fin 13) × Fin 3) ⊕
    ((Fin n → Fin 11) × Fin 6) ⊕ ((Fin n → Fin 9) × Fin 9)

private def p3 {n : ℕ} (u : Fin n → Fin 17) (k : Fin 4) (i : Fin n) : Fin 7 := step3 (u i) k
private def p4 {n : ℕ} (w : (Fin n → Fin 13) × Fin 3) (k : Fin 4) (i : Fin n) : Fin 7 :=
  step4 (w.1 i) w.2 k
private def p5 {n : ℕ} (w : (Fin n → Fin 11) × Fin 6) (k : Fin 4) (i : Fin n) : Fin 7 :=
  step5 (w.1 i) w.2 k
private def p6 {n : ℕ} (w : (Fin n → Fin 9) × Fin 9) (k : Fin 4) (i : Fin n) : Fin 7 :=
  step6 (w.1 i) w.2 k

private def Φ {n : ℕ} : WCode n → Finset (Fin n → Fin 7)
  | Sum.inl u => Finset.univ.image (p3 u)
  | Sum.inr (Sum.inl w) => Finset.univ.image (p4 w)
  | Sum.inr (Sum.inr (Sum.inl w)) => Finset.univ.image (p5 w)
  | Sum.inr (Sum.inr (Sum.inr w)) => Finset.univ.image (p6 w)

private def revW {n : ℕ} : WCode n → WCode n
  | Sum.inl u => Sum.inl (fun i => rev3 (u i))
  | Sum.inr (Sum.inl (u, m)) => Sum.inr (Sum.inl (fun i => rev4 (u i), revM4 m))
  | Sum.inr (Sum.inr (Sum.inl (u, m))) => Sum.inr (Sum.inr (Sum.inl (fun i => rev5 (u i), revM5 m)))
  | Sum.inr (Sum.inr (Sum.inr (u, m))) => Sum.inr (Sum.inr (Sum.inr (fun i => rev6 (u i), revM6 m)))

private lemma phi_rev {n : ℕ} (w : WCode n) : Φ (revW w) = Φ w := by
  rcases w with u | (⟨u, m⟩ | (⟨u, m⟩ | ⟨u, m⟩))
  · ext x
    simp only [Φ, revW, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨⟨3 - k.val, by omega⟩, funext fun i => ?_⟩
      have h := step3_rev (rev3 (u i)) k
      rwa [rev3_invol] at h
    · rintro ⟨k, rfl⟩
      refine ⟨⟨3 - k.val, by omega⟩, funext fun i => ?_⟩
      exact step3_rev (u i) k
  · ext x
    simp only [Φ, revW, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨⟨3 - k.val, by omega⟩, funext fun i => ?_⟩
      have h := step4_rev (rev4 (u i)) (revM4 m) k
      rwa [rev4_invol, revM4_invol] at h
    · rintro ⟨k, rfl⟩
      refine ⟨⟨3 - k.val, by omega⟩, funext fun i => ?_⟩
      exact step4_rev (u i) m k
  · ext x
    simp only [Φ, revW, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨⟨3 - k.val, by omega⟩, funext fun i => ?_⟩
      have h := step5_rev (rev5 (u i)) (revM5 m) k
      rwa [rev5_invol, revM5_invol] at h
    · rintro ⟨k, rfl⟩
      refine ⟨⟨3 - k.val, by omega⟩, funext fun i => ?_⟩
      exact step5_rev (u i) m k
  · ext x
    simp only [Φ, revW, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨⟨3 - k.val, by omega⟩, funext fun i => ?_⟩
      have h := step6_rev (rev6 (u i)) (revM6 m) k
      rwa [rev6_invol, revM6_invol] at h
    · rintro ⟨k, rfl⟩
      refine ⟨⟨3 - k.val, by omega⟩, funext fun i => ?_⟩
      exact step6_rev (u i) m k

private lemma hu3_ne_of_aux {n : ℕ} {s : Finset (Fin n → Fin 7)} {i₀ : Fin n}
    (hT_card : (s.image fun y => y i₀).card = 4)
    (u' : Fin n → Fin 17) (hPhi' : Φ (Sum.inl u') = s) : d3 (u' i₀) ≠ 0 := by
  intro hd0
  have himg : s.image (fun y => y i₀) ⊆ {x03 (u' i₀)} := by
    intro z hz
    rw [← hPhi'] at hz
    simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with ⟨y, ⟨k, rfl⟩, rfl⟩
    simp only [Finset.mem_singleton]
    apply Fin.ext
    have := step3_val (u' i₀) k
    rw [hd0, mul_zero, add_zero] at this
    exact_mod_cast this
  have := Finset.card_le_card himg
  rw [Finset.card_singleton] at this
  omega

private lemma hu4_ne_of_aux {n : ℕ} {s : Finset (Fin n → Fin 7)} {i₀ : Fin n}
    (hT_card : (s.image fun y => y i₀).card = 4)
    (u' : Fin n → Fin 13) (m' : Fin 3) (hPhi' : Φ (Sum.inr (Sum.inl (u', m'))) = s) :
    d4 (u' i₀) ≠ 0 := by
  intro hd0
  have himg : s.image (fun y => y i₀) ⊆ {x04 (u' i₀)} := by
    intro z hz
    rw [← hPhi'] at hz
    simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with ⟨y, ⟨k, rfl⟩, rfl⟩
    simp only [Finset.mem_singleton]
    apply Fin.ext
    have := step4_val (u' i₀) m' k
    rw [hd0, mul_zero, add_zero] at this
    exact_mod_cast this
  have := Finset.card_le_card himg
  rw [Finset.card_singleton] at this
  omega

private lemma hu5_ne_of_aux {n : ℕ} {s : Finset (Fin n → Fin 7)} {i₀ : Fin n}
    (hT_card : (s.image fun y => y i₀).card = 4)
    (u' : Fin n → Fin 11) (m' : Fin 6) (hPhi' : Φ (Sum.inr (Sum.inr (Sum.inl (u', m')))) = s) :
    d5 (u' i₀) ≠ 0 := by
  intro hd0
  have himg : s.image (fun y => y i₀) ⊆ {x05 (u' i₀)} := by
    intro z hz
    rw [← hPhi'] at hz
    simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with ⟨y, ⟨k, rfl⟩, rfl⟩
    simp only [Finset.mem_singleton]
    apply Fin.ext
    have := step5_val (u' i₀) m' k
    rw [hd0, mul_zero, add_zero] at this
    exact_mod_cast this
  have := Finset.card_le_card himg
  rw [Finset.card_singleton] at this
  omega

private lemma hu6_ne_of_aux {n : ℕ} {s : Finset (Fin n → Fin 7)} {i₀ : Fin n}
    (hT_card : (s.image fun y => y i₀).card = 4)
    (u' : Fin n → Fin 9) (m' : Fin 9) (hPhi' : Φ (Sum.inr (Sum.inr (Sum.inr (u', m')))) = s) :
    d6 (u' i₀) ≠ 0 := by
  intro hd0
  have himg : s.image (fun y => y i₀) ⊆ {x06 (u' i₀)} := by
    intro z hz
    rw [← hPhi'] at hz
    simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with ⟨y, ⟨k, rfl⟩, rfl⟩
    simp only [Finset.mem_singleton]
    apply Fin.ext
    have := step6_val (u' i₀) m' k
    rw [hd0, mul_zero, add_zero] at this
    exact_mod_cast this
  have := Finset.card_le_card himg
  rw [Finset.card_singleton] at this
  omega

private lemma w3_span_inv {n : ℕ} {s : Finset (Fin n → Fin 7)} (i₀ : Fin n)
    {x : Fin 4 → (Fin n → Fin 7)}
    (hx_mono : StrictMono (fun k : Fin 4 => (x k i₀ : ℕ)))
    (hs_eq : s = Finset.univ.image x)
    (hT_card : (s.image fun y => y i₀).card = 4)
    (u' : Fin n → Fin 17) (hPhi' : Φ (Sum.inl u') = s) :
    ((x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 3 ∨ (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 6) ∧
      3 * ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ)) = (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) ∧
      3 * ((x 2 i₀ : ℕ) - (x 0 i₀ : ℕ)) = 2 * ((x 3 i₀ : ℕ) - (x 0 i₀ : ℕ)) := by
  have hu'_ne := hu3_ne_of_aux hT_card u' hPhi'
  have hpos_lemma : ∀ v : Fin n → Fin 17, Φ (Sum.inl v) = s → 0 < d3 (v i₀) →
      ((x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 3 ∨ (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 6) ∧
        3 * ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ)) = (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) ∧
        3 * ((x 2 i₀ : ℕ) - (x 0 i₀ : ℕ)) = 2 * ((x 3 i₀ : ℕ) - (x 0 i₀ : ℕ)) := by
    intro v hPhiv hvpos
    have hv_step : ∀ k : Fin 4, (p3 v k i₀ : ℕ) = (x k i₀ : ℕ) := by
      have hmonov : StrictMono (fun k : Fin 4 => (p3 v k i₀ : ℕ)) := by
        intro a b hab
        dsimp [p3]
        have ha := step3_val (v i₀) a
        have hb := step3_val (v i₀) b
        have hab' : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := Int.ofNat_lt.mpr hab
        nlinarith
      have himg_eq : Finset.univ.image (fun k : Fin 4 => (p3 v k i₀ : ℕ)) =
          Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) := by
        have h1 : Finset.univ.image (fun k : Fin 4 => (p3 v k i₀ : ℕ)) =
            (Φ (Sum.inl v)).image (fun y => (y i₀ : ℕ)) := by ext z; simp [Φ]
        have h2 : Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) =
            s.image (fun y => (y i₀ : ℕ)) := by ext z; simp [hs_eq]
        rw [h1, h2, hPhiv]
      exact fin4_strictMono_eq hmonov hx_mono himg_eq
    have h0 := step3_val (v i₀) 0
    have h1 := step3_val (v i₀) 1
    have h2 := step3_val (v i₀) 2
    have h3 := step3_val (v i₀) 3
    dsimp [p3] at hv_step
    have hd : d3 (v i₀) = 1 ∨ d3 (v i₀) = 2 := by
      rcases d3_cases (v i₀) with h | h | h | h | h <;> omega
    rcases hd with hd | hd <;> rw [hd] at h0 h1 h2 h3 <;>
      have := hv_step 0 <;> have := hv_step 1 <;> have := hv_step 2 <;> have := hv_step 3 <;> omega
  rcases d3_cases (u' i₀) with h | h | h | h | h
  · exact absurd h hu'_ne
  · exact hpos_lemma u' hPhi' (by omega)
  · exact hpos_lemma u' hPhi' (by omega)
  · have hrev_pos : 0 < d3 (rev3 (u' i₀)) := by rw [d3_rev, h]; norm_num
    exact hpos_lemma (fun i => rev3 (u' i)) ((phi_rev (Sum.inl u')).trans hPhi') hrev_pos
  · have hrev_pos : 0 < d3 (rev3 (u' i₀)) := by rw [d3_rev, h]; norm_num
    exact hpos_lemma (fun i => rev3 (u' i)) ((phi_rev (Sum.inl u')).trans hPhi') hrev_pos

private lemma w4_span_inv {n : ℕ} {s : Finset (Fin n → Fin 7)} (i₀ : Fin n)
    {x : Fin 4 → (Fin n → Fin 7)}
    (hx_mono : StrictMono (fun k : Fin 4 => (x k i₀ : ℕ)))
    (hs_eq : s = Finset.univ.image x)
    (hT_card : (s.image fun y => y i₀).card = 4)
    (u' : Fin n → Fin 13) (m' : Fin 3) (hPhi' : Φ (Sum.inr (Sum.inl (u', m'))) = s) :
    (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 4 := by
  have hu'_ne := hu4_ne_of_aux hT_card u' m' hPhi'
  have hpos_lemma : ∀ (v : Fin n → Fin 13) (mv : Fin 3),
      Φ (Sum.inr (Sum.inl (v, mv))) = s → d4 (v i₀) = 1 →
      (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 4 := by
    intro v mv hPhiv hv1
    have hidx_mono : StrictMono (idx4 mv) := by fin_cases mv <;> decide
    have hv_step : ∀ k : Fin 4, (p4 (v, mv) k i₀ : ℕ) = (x k i₀ : ℕ) := by
      have hmonov : StrictMono (fun k : Fin 4 => (p4 (v, mv) k i₀ : ℕ)) := by
        intro a b hab
        dsimp [p4]
        have ha := step4_val (v i₀) mv a
        have hb := step4_val (v i₀) mv b
        rw [hv1] at ha hb
        have hlt := hidx_mono hab
        omega
      have himg_eq : Finset.univ.image (fun k : Fin 4 => (p4 (v, mv) k i₀ : ℕ)) =
          Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) := by
        have h1 : Finset.univ.image (fun k : Fin 4 => (p4 (v, mv) k i₀ : ℕ)) =
            (Φ (Sum.inr (Sum.inl (v, mv)))).image (fun y => (y i₀ : ℕ)) := by ext z; simp [Φ]
        have h2 : Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) =
            s.image (fun y => (y i₀ : ℕ)) := by ext z; simp [hs_eq]
        rw [h1, h2, hPhiv]
      exact fin4_strictMono_eq hmonov hx_mono himg_eq
    have h0 := step4_val (v i₀) mv 0
    have h3 := step4_val (v i₀) mv 3
    have hi0 : idx4 mv 0 = 0 := by fin_cases mv <;> rfl
    have hi3 : idx4 mv 3 = 4 := by fin_cases mv <;> rfl
    rw [hv1, hi0] at h0
    rw [hv1, hi3] at h3
    dsimp [p4] at hv_step
    have := hv_step 0
    have := hv_step 3
    omega
  rcases d4_cases (u' i₀) with h | h | h
  · exact absurd h hu'_ne
  · exact hpos_lemma u' m' hPhi' h
  · have hrev_d : d4 (rev4 (u' i₀)) = 1 := by rw [d4_rev, h]; norm_num
    exact hpos_lemma (fun i => rev4 (u' i)) (revM4 m')
      ((phi_rev (Sum.inr (Sum.inl (u', m')))).trans hPhi') hrev_d

private lemma w5_span_inv {n : ℕ} {s : Finset (Fin n → Fin 7)} (i₀ : Fin n)
    {x : Fin 4 → (Fin n → Fin 7)}
    (hx_mono : StrictMono (fun k : Fin 4 => (x k i₀ : ℕ)))
    (hs_eq : s = Finset.univ.image x)
    (hT_card : (s.image fun y => y i₀).card = 4)
    (u' : Fin n → Fin 11) (m' : Fin 6)
    (hPhi' : Φ (Sum.inr (Sum.inr (Sum.inl (u', m')))) = s) :
    (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 5 := by
  have hu'_ne := hu5_ne_of_aux hT_card u' m' hPhi'
  have hpos_lemma : ∀ (v : Fin n → Fin 11) (mv : Fin 6),
      Φ (Sum.inr (Sum.inr (Sum.inl (v, mv)))) = s → d5 (v i₀) = 1 →
      (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 5 := by
    intro v mv hPhiv hv1
    have hidx_mono : StrictMono (idx5 mv) := by fin_cases mv <;> decide
    have hv_step : ∀ k : Fin 4, (p5 (v, mv) k i₀ : ℕ) = (x k i₀ : ℕ) := by
      have hmonov : StrictMono (fun k : Fin 4 => (p5 (v, mv) k i₀ : ℕ)) := by
        intro a b hab
        dsimp [p5]
        have ha := step5_val (v i₀) mv a
        have hb := step5_val (v i₀) mv b
        rw [hv1] at ha hb
        have hlt := hidx_mono hab
        omega
      have himg_eq : Finset.univ.image (fun k : Fin 4 => (p5 (v, mv) k i₀ : ℕ)) =
          Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) := by
        have h1 : Finset.univ.image (fun k : Fin 4 => (p5 (v, mv) k i₀ : ℕ)) =
            (Φ (Sum.inr (Sum.inr (Sum.inl (v, mv))))).image (fun y => (y i₀ : ℕ)) := by
          ext z; simp [Φ]
        have h2 : Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) =
            s.image (fun y => (y i₀ : ℕ)) := by ext z; simp [hs_eq]
        rw [h1, h2, hPhiv]
      exact fin4_strictMono_eq hmonov hx_mono himg_eq
    have h0 := step5_val (v i₀) mv 0
    have h3 := step5_val (v i₀) mv 3
    have hi0 : idx5 mv 0 = 0 := by fin_cases mv <;> rfl
    have hi3 : idx5 mv 3 = 5 := by fin_cases mv <;> rfl
    rw [hv1, hi0] at h0
    rw [hv1, hi3] at h3
    dsimp [p5] at hv_step
    have := hv_step 0
    have := hv_step 3
    omega
  rcases d5_cases (u' i₀) with h | h | h
  · exact absurd h hu'_ne
  · exact hpos_lemma u' m' hPhi' h
  · have hrev_d : d5 (rev5 (u' i₀)) = 1 := by rw [d5_rev, h]; norm_num
    exact hpos_lemma (fun i => rev5 (u' i)) (revM5 m')
      ((phi_rev (Sum.inr (Sum.inr (Sum.inl (u', m'))))).trans hPhi') hrev_d

private lemma w6_span_inv {n : ℕ} {s : Finset (Fin n → Fin 7)} (i₀ : Fin n)
    {x : Fin 4 → (Fin n → Fin 7)}
    (hx_mono : StrictMono (fun k : Fin 4 => (x k i₀ : ℕ)))
    (hs_eq : s = Finset.univ.image x)
    (hT_card : (s.image fun y => y i₀).card = 4)
    (u' : Fin n → Fin 9) (m' : Fin 9)
    (hPhi' : Φ (Sum.inr (Sum.inr (Sum.inr (u', m')))) = s) :
    (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 6 ∧
      ¬ ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ) = 2 ∧ (x 2 i₀ : ℕ) - (x 0 i₀ : ℕ) = 4) := by
  have hu'_ne := hu6_ne_of_aux hT_card u' m' hPhi'
  have hpos_lemma : ∀ (v : Fin n → Fin 9) (mv : Fin 9),
      Φ (Sum.inr (Sum.inr (Sum.inr (v, mv)))) = s → d6 (v i₀) = 1 →
      (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 6 ∧
        ¬ ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ) = 2 ∧ (x 2 i₀ : ℕ) - (x 0 i₀ : ℕ) = 4) := by
    intro v mv hPhiv hv1
    have hidx_mono : StrictMono (idx6 mv) := by fin_cases mv <;> decide
    have hv_step : ∀ k : Fin 4, (p6 (v, mv) k i₀ : ℕ) = (x k i₀ : ℕ) := by
      have hmonov : StrictMono (fun k : Fin 4 => (p6 (v, mv) k i₀ : ℕ)) := by
        intro a b hab
        dsimp [p6]
        have ha := step6_val (v i₀) mv a
        have hb := step6_val (v i₀) mv b
        rw [hv1] at ha hb
        have hlt := hidx_mono hab
        omega
      have himg_eq : Finset.univ.image (fun k : Fin 4 => (p6 (v, mv) k i₀ : ℕ)) =
          Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) := by
        have h1 : Finset.univ.image (fun k : Fin 4 => (p6 (v, mv) k i₀ : ℕ)) =
            (Φ (Sum.inr (Sum.inr (Sum.inr (v, mv))))).image (fun y => (y i₀ : ℕ)) := by
          ext z; simp [Φ]
        have h2 : Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) =
            s.image (fun y => (y i₀ : ℕ)) := by ext z; simp [hs_eq]
        rw [h1, h2, hPhiv]
      exact fin4_strictMono_eq hmonov hx_mono himg_eq
    have h0 := step6_val (v i₀) mv 0
    have h1 := step6_val (v i₀) mv 1
    have h2 := step6_val (v i₀) mv 2
    have h3 := step6_val (v i₀) mv 3
    have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
    have hi3 : idx6 mv 3 = 6 := by fin_cases mv <;> rfl
    rw [hv1, hi0] at h0
    rw [hv1, hi3] at h3
    rw [hv1] at h1 h2
    dsimp [p6] at hv_step
    have := hv_step 0
    have := hv_step 1
    have := hv_step 2
    have := hv_step 3
    have hne := idx6_ne_two_four mv
    omega
  rcases d6_cases (u' i₀) with h | h | h
  · exact absurd h hu'_ne
  · exact hpos_lemma u' m' hPhi' h
  · have hrev_d : d6 (rev6 (u' i₀)) = 1 := by rw [d6_rev, h]; norm_num
    exact hpos_lemma (fun i => rev6 (u' i)) (revM6 m')
      ((phi_rev (Sum.inr (Sum.inr (Sum.inr (u', m'))))).trans hPhi') hrev_d

private lemma fiber_span3 {n : ℕ} {s : Finset (Fin n → Fin 7)} {i₀ : Fin n}
    {x : Fin 4 → (Fin n → Fin 7)}
    (hcoord_inj : Set.InjOn (fun y : Fin n → Fin 7 => y i₀) (s : Set (Fin n → Fin 7)))
    (hx_mem : ∀ k : Fin 4, x k ∈ s)
    (hx_mono : StrictMono (fun k : Fin 4 => (x k i₀ : ℕ)))
    (hs_eq : s = Finset.univ.image x)
    (hT_card : (s.image fun y => y i₀).card = 4)
    (hline : ∀ (k : Fin 4) (i : Fin n),
      (((x k i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) * (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) =
      (((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) * (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)))
    (h0lt3 : (x 0 i₀ : ℕ) < (x 3 i₀ : ℕ))
    (h31 : 3 * ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ)) = (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ))
    (h32 : 3 * ((x 2 i₀ : ℕ) - (x 0 i₀ : ℕ)) = 2 * ((x 3 i₀ : ℕ) - (x 0 i₀ : ℕ)))
    (hD : (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 3 ∨ (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 6) :
    ∃ u : Fin n → Fin 17, d3 (u i₀) ≠ 0 ∧ Φ (Sum.inl u) = s ∧
      ∀ w', Φ w' = s → w' = Sum.inl u ∨ w' = revW (Sum.inl u) := by
  have hline3 : ∀ (k : Fin 4) (i : Fin n),
      3 * (((x k i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) = (k : ℤ) * (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) := by
    intro k i
    have hlk := hline k i
    have hpk : 3 * (((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) =
        (k : ℤ) * (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) := by
      fin_cases k <;> simp <;> omega
    have hmul : 3 * (((x k i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) *
          (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) =
        (k : ℤ) * (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) *
          (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) := by
      calc 3 * (((x k i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) *
            (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ))
          = 3 * ((((x k i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) *
              (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ))) := by ring
        _ = 3 * ((((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) *
              (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ))) := by rw [hlk]
        _ = (3 * (((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ))) *
              (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) := by ring
        _ = (k : ℤ) * (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) *
              (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) := by rw [hpk]
        _ = (k : ℤ) * (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) *
              (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) := by ring
    exact mul_right_cancel₀ (by omega : (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) ≠ 0) hmul
  have hdvd3 : ∀ i : Fin n, ∃ q : ℤ, ((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) = 3 * q := by
    intro i
    have h1 := hline3 1 i
    simp at h1
    exact ⟨((x 1 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ), by linarith⟩
  let u : Fin n → Fin 17 := fun i => Classical.choose (exists_u3_of (x 0 i) (x 3 i) (hdvd3 i))
  have hu_spec : ∀ i : Fin n, x03 (u i) = x 0 i ∧
      3 * d3 (u i) = ((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) :=
    fun i => Classical.choose_spec (exists_u3_of (x 0 i) (x 3 i) (hdvd3 i))
  have hud0 : d3 (u i₀) ≠ 0 := by have h := (hu_spec i₀).2; omega
  have hu_step : ∀ k : Fin 4, p3 u k = x k := by
    intro k
    ext i
    have hlk := hline3 k i
    have hsv := step3_val (u i) k
    have hsp := hu_spec i
    have h0_eq : ((x03 (u i) : ℕ) : ℤ) = ((x 0 i : ℕ) : ℤ) := by rw [hsp.1]
    rw [← hsp.2] at hlk
    have h3_eq : ((x k i : ℕ) : ℤ) = ((step3 (u i) k : ℕ) : ℤ) := by
      linarith [show (k : ℤ) * (3 * d3 (u i)) = 3 * (((k : ℕ) : ℤ) * d3 (u i)) by
        have hk : (k : ℤ) = ((k : ℕ) : ℤ) := rfl
        rw [hk]; ring]
    exact_mod_cast h3_eq.symm
  have hPhi_u : Φ (Sum.inl u) = s := by
    rw [hs_eq]
    dsimp [Φ]
    exact Finset.image_congr fun k _ => hu_step k
  refine ⟨u, hud0, hPhi_u, ?_⟩
  rintro (u' | (⟨u', m'⟩ | (⟨u', m'⟩ | ⟨u', m'⟩))) hPhi'
  · have hu'_ne := hu3_ne_of_aux hT_card u' hPhi'
    have hcheck_pos : ∀ v : Fin n → Fin 17, Φ (Sum.inl v) = s → 0 < d3 (v i₀) → v = u := by
      intro v hPhiv hvpos
      have hv_step : ∀ k : Fin 4, p3 v k = x k := by
        have hmonov : StrictMono (fun k : Fin 4 => (p3 v k i₀ : ℕ)) := by
          intro a b hab
          dsimp [p3]
          have ha := step3_val (v i₀) a
          have hb := step3_val (v i₀) b
          have hab' : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := Int.ofNat_lt.mpr hab
          nlinarith
        have himg_eq : Finset.univ.image (fun k : Fin 4 => (p3 v k i₀ : ℕ)) =
            Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) := by
          have h1 : Finset.univ.image (fun k : Fin 4 => (p3 v k i₀ : ℕ)) =
              (Φ (Sum.inl v)).image (fun y => (y i₀ : ℕ)) := by ext z; simp [Φ]
          have h2 : Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) =
              s.image (fun y => (y i₀ : ℕ)) := by ext z; simp [hs_eq]
          rw [h1, h2, hPhiv]
        have hcoord_eq : ∀ k : Fin 4, p3 v k i₀ = x k i₀ := by
          have hc := fin4_strictMono_eq hmonov hx_mono himg_eq
          intro k; exact Fin.ext (hc k)
        intro k
        have hmem : p3 v k ∈ s := by
          rw [← hPhiv]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
        exact hcoord_inj hmem (hx_mem k) (hcoord_eq k)
      funext i
      refine uniq_u3 (v i) (u i) ?_ ?_
      · have h0 := congrFun (hv_step 0) i
        have hv0 := step3_val (v i) 0
        have hk0 : (((0 : Fin 4) : ℕ) : ℤ) = 0 := rfl
        rw [hk0, zero_mul, add_zero] at hv0
        rw [(hu_spec i).1, ← h0]
        exact Fin.ext (by dsimp [p3]; exact_mod_cast hv0.symm)
      · have h0 := congrFun (hv_step 0) i
        have h3 := congrFun (hv_step 3) i
        have hv0 := step3_val (v i) 0
        have hv3 := step3_val (v i) 3
        have hk0 : (((0 : Fin 4) : ℕ) : ℤ) = 0 := rfl
        have hk3 : (((3 : Fin 4) : ℕ) : ℤ) = 3 := rfl
        rw [hk0, zero_mul, add_zero] at hv0
        rw [hk3] at hv3
        have h0_z : ((x 0 i : ℕ) : ℤ) = ((x03 (v i) : ℕ) : ℤ) := by
          dsimp [p3] at h0; rw [← h0]; exact_mod_cast hv0
        have h3_z : ((x 3 i : ℕ) : ℤ) = ((step3 (v i) 3 : ℕ) : ℤ) := by
          dsimp [p3] at h3; rw [← h3]
        rw [(hu_spec i).2]; linarith
    rcases d3_cases (u' i₀) with h | h | h | h | h
    · exact absurd h hu'_ne
    · exact Or.inl (congrArg Sum.inl (hcheck_pos u' hPhi' (by omega)))
    · exact Or.inl (congrArg Sum.inl (hcheck_pos u' hPhi' (by omega)))
    · have hrev_pos : 0 < d3 (rev3 (u' i₀)) := by rw [d3_rev, h]; norm_num
      have hrev_eq := hcheck_pos (fun i => rev3 (u' i))
        ((phi_rev (Sum.inl u')).trans hPhi') hrev_pos
      right
      congr 1
      funext i
      have := congrFun hrev_eq i
      rw [← this, rev3_invol]
    · have hrev_pos : 0 < d3 (rev3 (u' i₀)) := by rw [d3_rev, h]; norm_num
      have hrev_eq := hcheck_pos (fun i => rev3 (u' i))
        ((phi_rev (Sum.inl u')).trans hPhi') hrev_pos
      right
      congr 1
      funext i
      have := congrFun hrev_eq i
      rw [← this, rev3_invol]
  · exfalso; have := w4_span_inv i₀ hx_mono hs_eq hT_card u' m' hPhi'; omega
  · exfalso; have := w5_span_inv i₀ hx_mono hs_eq hT_card u' m' hPhi'; omega
  · exfalso; have := w6_span_inv i₀ hx_mono hs_eq hT_card u' m' hPhi'; omega

private lemma fiber_span4 {n : ℕ} {s : Finset (Fin n → Fin 7)} {i₀ : Fin n}
    {x : Fin 4 → (Fin n → Fin 7)}
    (hcoord_inj : Set.InjOn (fun y : Fin n → Fin 7 => y i₀) (s : Set (Fin n → Fin 7)))
    (hx_mem : ∀ k : Fin 4, x k ∈ s)
    (hx_mono : StrictMono (fun k : Fin 4 => (x k i₀ : ℕ)))
    (hs_eq : s = Finset.univ.image x)
    (hT_card : (s.image fun y => y i₀).card = 4)
    (hline : ∀ (k : Fin 4) (i : Fin n),
      (((x k i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) * (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) =
      (((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) * (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)))
    (h0lt1 : (x 0 i₀ : ℕ) < (x 1 i₀ : ℕ))
    (h1lt2 : (x 1 i₀ : ℕ) < (x 2 i₀ : ℕ))
    (h2lt3 : (x 2 i₀ : ℕ) < (x 3 i₀ : ℕ))
    (hA4 : (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 4) :
    ∃ u : Fin n → Fin 13, ∃ m : Fin 3, d4 (u i₀) ≠ 0 ∧ Φ (Sum.inr (Sum.inl (u, m))) = s ∧
      ∀ w', Φ w' = s → w' = Sum.inr (Sum.inl (u, m)) ∨ w' = revW (Sum.inr (Sum.inl (u, m))) := by
  have hdvd4 : ∀ i : Fin n, ∃ q : ℤ, ((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) = 4 * q := by
    intro i
    have hA_z : ((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 4 := by omega
    by_cases hx1 : (x 1 i₀ : ℕ) - (x 0 i₀ : ℕ) = 1
    · have h1 := hline 1 i
      have hp1_z : ((x 1 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 1 := by omega
      rw [hA_z, hp1_z, one_mul] at h1
      exact ⟨((x 1 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ), by linarith⟩
    · have hx2 : (x 2 i₀ : ℕ) - (x 0 i₀ : ℕ) = 3 := by omega
      have h2 := hline 2 i
      have hp2_z : ((x 2 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 3 := by omega
      rw [hA_z, hp2_z] at h2
      exact ⟨((x 3 i : ℕ) : ℤ) - ((x 2 i : ℕ) : ℤ), by linarith⟩
  let m : Fin 3 :=
    if (x 1 i₀ : ℕ) - (x 0 i₀ : ℕ) = 2 then 0
    else if (x 2 i₀ : ℕ) - (x 0 i₀ : ℕ) = 3 then 1
    else 2
  have hm_spec : ∀ k : Fin 4, idx4 m k = ((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) := by
    intro k
    dsimp [m]
    split_ifs <;> fin_cases k <;> simp [idx4] <;> omega
  let u : Fin n → Fin 13 := fun i => Classical.choose (exists_u4_of (x 0 i) (x 3 i) (hdvd4 i))
  have hu_spec : ∀ i : Fin n, x04 (u i) = x 0 i ∧
      4 * d4 (u i) = ((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) :=
    fun i => Classical.choose_spec (exists_u4_of (x 0 i) (x 3 i) (hdvd4 i))
  have hud0 : d4 (u i₀) ≠ 0 := by have h := (hu_spec i₀).2; omega
  have hu_step : ∀ k : Fin 4, p4 (u, m) k = x k := by
    intro k
    ext i
    have hlk := hline k i
    have hA_z : ((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 4 := by omega
    rw [hA_z, ← hm_spec k] at hlk
    have hsv := step4_val (u i) m k
    have hsp := hu_spec i
    have h0_eq : ((x04 (u i) : ℕ) : ℤ) = ((x 0 i : ℕ) : ℤ) := by rw [hsp.1]
    rw [← hsp.2] at hlk
    have h4_eq : ((x k i : ℕ) : ℤ) = ((step4 (u i) m k : ℕ) : ℤ) := by
      linarith [show idx4 m k * (4 * d4 (u i)) = 4 * (idx4 m k * d4 (u i)) by ring]
    exact_mod_cast h4_eq.symm
  have hPhi_u : Φ (Sum.inr (Sum.inl (u, m))) = s := by
    rw [hs_eq]
    dsimp [Φ]
    exact Finset.image_congr fun k _ => hu_step k
  refine ⟨u, m, hud0, hPhi_u, ?_⟩
  rintro (u' | (⟨u', m'⟩ | (⟨u', m'⟩ | ⟨u', m'⟩))) hPhi'
  · exfalso; have := w3_span_inv i₀ hx_mono hs_eq hT_card u' hPhi'; omega
  · have hu'_ne := hu4_ne_of_aux hT_card u' m' hPhi'
    have hor : d4 (u' i₀) = 1 ∨ d4 (u' i₀) = -1 := by
      rcases d4_cases (u' i₀) with h0 | h1 | h2
      · exact absurd h0 hu'_ne
      · exact Or.inl h1
      · exact Or.inr h2
    have hcheck_pos : ∀ (v : Fin n → Fin 13) (mv : Fin 3),
        Φ (Sum.inr (Sum.inl (v, mv))) = s → d4 (v i₀) = 1 → (v, mv) = (u, m) := by
      intro v mv hPhiv hv1
      have hidx_mono : StrictMono (idx4 mv) := by fin_cases mv <;> decide
      have hmonov : StrictMono (fun k : Fin 4 => (p4 (v, mv) k i₀ : ℕ)) := by
        intro a b hab
        dsimp [p4]
        have ha := step4_val (v i₀) mv a
        have hb := step4_val (v i₀) mv b
        rw [hv1] at ha hb
        have hlt : idx4 mv a < idx4 mv b := hidx_mono hab
        omega
      have himg_eq : Finset.univ.image (fun k : Fin 4 => (p4 (v, mv) k i₀ : ℕ)) =
          Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) := by
        have h1 : Finset.univ.image (fun k : Fin 4 => (p4 (v, mv) k i₀ : ℕ)) =
            (Φ (Sum.inr (Sum.inl (v, mv)))).image (fun y => (y i₀ : ℕ)) := by ext z; simp [Φ]
        have h2 : Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) =
            s.image (fun y => (y i₀ : ℕ)) := by ext z; simp [hs_eq]
        rw [h1, h2, hPhiv]
      have hv_step : ∀ k : Fin 4, p4 (v, mv) k = x k := by
        have hc := fin4_strictMono_eq hmonov hx_mono himg_eq
        intro k
        have hmem : p4 (v, mv) k ∈ s := by
          rw [← hPhiv]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
        exact hcoord_inj hmem (hx_mem k) (Fin.ext (hc k))
      have hmv_eq : mv = m := by
        have h1 : idx4 mv 1 = idx4 m 1 := by
          have hst1 := step4_val (v i₀) mv 1
          have hst0 := step4_val (v i₀) mv 0
          have h0_eq : ((p4 (v, mv) 0 i₀ : ℕ) : ℤ) = ((x 0 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 0) i₀]
          have h1_eq : ((p4 (v, mv) 1 i₀ : ℕ) : ℤ) = ((x 1 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 1) i₀]
          have hi0 : idx4 mv 0 = 0 := by fin_cases mv <;> rfl
          rw [hv1] at hst1 hst0; rw [hi0] at hst0
          dsimp [p4] at h0_eq h1_eq; rw [hm_spec 1]; linarith
        have h2 : idx4 mv 2 = idx4 m 2 := by
          have hst2 := step4_val (v i₀) mv 2
          have hst0 := step4_val (v i₀) mv 0
          have h0_eq : ((p4 (v, mv) 0 i₀ : ℕ) : ℤ) = ((x 0 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 0) i₀]
          have h2_eq : ((p4 (v, mv) 2 i₀ : ℕ) : ℤ) = ((x 2 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 2) i₀]
          have hi0 : idx4 mv 0 = 0 := by fin_cases mv <;> rfl
          rw [hv1] at hst2 hst0; rw [hi0] at hst0
          dsimp [p4] at h0_eq h2_eq; rw [hm_spec 2]; linarith
        exact idx4_inj mv m h1 h2
      refine Prod.ext (funext fun i => ?_) hmv_eq
      refine uniq_u4 (v i) (u i) ?_ ?_
      · have h0 := congrFun (hv_step 0) i
        have hv0 := step4_val (v i) mv 0
        have hi0 : idx4 mv 0 = 0 := by fin_cases mv <;> rfl
        rw [hi0, zero_mul, add_zero] at hv0
        rw [(hu_spec i).1, ← h0]
        exact Fin.ext (by dsimp [p4]; exact_mod_cast hv0.symm)
      · have h0 := congrFun (hv_step 0) i
        have h3 := congrFun (hv_step 3) i
        have hv0 := step4_val (v i) mv 0
        have hv3 := step4_val (v i) mv 3
        have hi0 : idx4 mv 0 = 0 := by fin_cases mv <;> rfl
        have hi3 : idx4 mv 3 = 4 := by fin_cases mv <;> rfl
        rw [hi0, zero_mul, add_zero] at hv0
        rw [hi3] at hv3
        have h0_z : ((x 0 i : ℕ) : ℤ) = ((x04 (v i) : ℕ) : ℤ) := by
          dsimp [p4] at h0; rw [← h0]; exact_mod_cast hv0
        have h3_z : ((x 3 i : ℕ) : ℤ) = ((step4 (v i) mv 3 : ℕ) : ℤ) := by
          dsimp [p4] at h3; rw [← h3]
        rw [(hu_spec i).2]; linarith
    rcases hor with hv1 | hv_neg
    · exact Or.inl (congrArg Sum.inr (congrArg Sum.inl (hcheck_pos u' m' hPhi' hv1)))
    · have hrev_d : d4 (rev4 (u' i₀)) = 1 := by rw [d4_rev, hv_neg]; norm_num
      have hrev_eq := hcheck_pos (fun i => rev4 (u' i)) (revM4 m')
        ((phi_rev (Sum.inr (Sum.inl (u', m')))).trans hPhi') hrev_d
      right
      have h1 := congrArg Prod.fst hrev_eq
      have h2 := congrArg Prod.snd hrev_eq
      dsimp only at h1 h2
      refine congrArg Sum.inr (congrArg Sum.inl (Prod.ext ?_ ?_))
      · funext i; dsimp only; have := congrFun h1 i; rw [← this, rev4_invol]
      · dsimp only; rw [← h2, revM4_invol]
  · exfalso; have := w5_span_inv i₀ hx_mono hs_eq hT_card u' m' hPhi'; omega
  · exfalso; have := w6_span_inv i₀ hx_mono hs_eq hT_card u' m' hPhi'; omega

private lemma fiber_span5 {n : ℕ} {s : Finset (Fin n → Fin 7)} {i₀ : Fin n}
    {x : Fin 4 → (Fin n → Fin 7)}
    (hcoord_inj : Set.InjOn (fun y : Fin n → Fin 7 => y i₀) (s : Set (Fin n → Fin 7)))
    (hx_mem : ∀ k : Fin 4, x k ∈ s)
    (hx_mono : StrictMono (fun k : Fin 4 => (x k i₀ : ℕ)))
    (hs_eq : s = Finset.univ.image x)
    (hT_card : (s.image fun y => y i₀).card = 4)
    (hline : ∀ (k : Fin 4) (i : Fin n),
      (((x k i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) * (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) =
      (((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) * (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)))
    (h0lt1 : (x 0 i₀ : ℕ) < (x 1 i₀ : ℕ))
    (h1lt2 : (x 1 i₀ : ℕ) < (x 2 i₀ : ℕ))
    (h2lt3 : (x 2 i₀ : ℕ) < (x 3 i₀ : ℕ))
    (hA5 : (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 5) :
    ∃ u : Fin n → Fin 11, ∃ m : Fin 6, d5 (u i₀) ≠ 0 ∧
      Φ (Sum.inr (Sum.inr (Sum.inl (u, m)))) = s ∧
      ∀ w', Φ w' = s →
        w' = Sum.inr (Sum.inr (Sum.inl (u, m))) ∨
        w' = revW (Sum.inr (Sum.inr (Sum.inl (u, m)))) := by
  have hdvd5 : ∀ i : Fin n, ∃ q : ℤ, ((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) = 5 * q := by
    intro i
    have hA_z : ((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 5 := by omega
    by_cases hx1 : (x 1 i₀ : ℕ) - (x 0 i₀ : ℕ) = 1
    · have h1 := hline 1 i
      have hp1_z : ((x 1 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 1 := by omega
      rw [hA_z, hp1_z, one_mul] at h1
      exact ⟨((x 1 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ), by linarith⟩
    · by_cases hx2 : (x 2 i₀ : ℕ) - (x 0 i₀ : ℕ) = 4
      · have h2 := hline 2 i
        have hp2_z : ((x 2 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 4 := by omega
        rw [hA_z, hp2_z] at h2
        exact ⟨((x 3 i : ℕ) : ℤ) - ((x 2 i : ℕ) : ℤ), by linarith⟩
      · have h1 := hline 1 i
        have h2 := hline 2 i
        have hdiff : ((x 2 i₀ : ℕ) : ℤ) - ((x 1 i₀ : ℕ) : ℤ) = 1 := by omega
        have h12 : (((x 2 i : ℕ) : ℤ) - ((x 1 i : ℕ) : ℤ)) *
            (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) =
            (((x 2 i₀ : ℕ) : ℤ) - ((x 1 i₀ : ℕ) : ℤ)) *
            (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) := by linarith
        rw [hA_z, hdiff, one_mul] at h12
        exact ⟨((x 2 i : ℕ) : ℤ) - ((x 1 i : ℕ) : ℤ), by linarith⟩
  let m : Fin 6 := mkM5 ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ)) ((x 2 i₀ : ℕ) - (x 0 i₀ : ℕ))
  have hm5 := idx5_mkM5 ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ)) ((x 2 i₀ : ℕ) - (x 0 i₀ : ℕ))
    (by omega) (by omega) (by omega)
  have hm_spec : ∀ k : Fin 4, idx5 m k = ((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) := by
    intro k
    fin_cases k
    · change idx5 m 0 = ((x 0 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ); exact hm5.1.trans (by omega)
    · change idx5 m 1 = ((x 1 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ); exact hm5.2.1.trans (by omega)
    · change idx5 m 2 = ((x 2 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ); exact hm5.2.2.1.trans (by omega)
    · change idx5 m 3 = ((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ); exact hm5.2.2.2.trans (by omega)
  let u : Fin n → Fin 11 := fun i => Classical.choose (exists_u5_of (x 0 i) (x 3 i) (hdvd5 i))
  have hu_spec : ∀ i : Fin n, x05 (u i) = x 0 i ∧
      5 * d5 (u i) = ((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) :=
    fun i => Classical.choose_spec (exists_u5_of (x 0 i) (x 3 i) (hdvd5 i))
  have hud0 : d5 (u i₀) ≠ 0 := by have h := (hu_spec i₀).2; omega
  have hu_step : ∀ k : Fin 4, p5 (u, m) k = x k := by
    intro k
    ext i
    have hlk := hline k i
    have hA_z : ((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 5 := by omega
    rw [hA_z, ← hm_spec k] at hlk
    have hsv := step5_val (u i) m k
    have hsp := hu_spec i
    have h0_eq : ((x05 (u i) : ℕ) : ℤ) = ((x 0 i : ℕ) : ℤ) := by rw [hsp.1]
    rw [← hsp.2] at hlk
    have h5_eq : ((x k i : ℕ) : ℤ) = ((step5 (u i) m k : ℕ) : ℤ) := by
      linarith [show idx5 m k * (5 * d5 (u i)) = 5 * (idx5 m k * d5 (u i)) by ring]
    exact_mod_cast h5_eq.symm
  have hPhi_u : Φ (Sum.inr (Sum.inr (Sum.inl (u, m)))) = s := by
    rw [hs_eq]
    dsimp [Φ]
    exact Finset.image_congr fun k _ => hu_step k
  refine ⟨u, m, hud0, hPhi_u, ?_⟩
  rintro (u' | (⟨u', m'⟩ | (⟨u', m'⟩ | ⟨u', m'⟩))) hPhi'
  · exfalso; have := w3_span_inv i₀ hx_mono hs_eq hT_card u' hPhi'; omega
  · exfalso; have := w4_span_inv i₀ hx_mono hs_eq hT_card u' m' hPhi'; omega
  · have hu'_ne := hu5_ne_of_aux hT_card u' m' hPhi'
    have hor : d5 (u' i₀) = 1 ∨ d5 (u' i₀) = -1 := by
      rcases d5_cases (u' i₀) with h0 | h1 | h2
      · exact absurd h0 hu'_ne
      · exact Or.inl h1
      · exact Or.inr h2
    have hcheck_pos : ∀ (v : Fin n → Fin 11) (mv : Fin 6),
        Φ (Sum.inr (Sum.inr (Sum.inl (v, mv)))) = s → d5 (v i₀) = 1 → (v, mv) = (u, m) := by
      intro v mv hPhiv hv1
      have hidx_mono : StrictMono (idx5 mv) := by fin_cases mv <;> decide
      have hmonov : StrictMono (fun k : Fin 4 => (p5 (v, mv) k i₀ : ℕ)) := by
        intro a b hab
        dsimp [p5]
        have ha := step5_val (v i₀) mv a
        have hb := step5_val (v i₀) mv b
        rw [hv1] at ha hb
        have hlt : idx5 mv a < idx5 mv b := hidx_mono hab
        omega
      have himg_eq : Finset.univ.image (fun k : Fin 4 => (p5 (v, mv) k i₀ : ℕ)) =
          Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) := by
        have h1 : Finset.univ.image (fun k : Fin 4 => (p5 (v, mv) k i₀ : ℕ)) =
            (Φ (Sum.inr (Sum.inr (Sum.inl (v, mv))))).image (fun y => (y i₀ : ℕ)) := by
          ext z; simp [Φ]
        have h2 : Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) =
            s.image (fun y => (y i₀ : ℕ)) := by ext z; simp [hs_eq]
        rw [h1, h2, hPhiv]
      have hv_step : ∀ k : Fin 4, p5 (v, mv) k = x k := by
        have hc := fin4_strictMono_eq hmonov hx_mono himg_eq
        intro k
        have hmem : p5 (v, mv) k ∈ s := by
          rw [← hPhiv]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
        exact hcoord_inj hmem (hx_mem k) (Fin.ext (hc k))
      have hmv_eq : mv = m := by
        have h1 : idx5 mv 1 = idx5 m 1 := by
          have hst1 := step5_val (v i₀) mv 1
          have hst0 := step5_val (v i₀) mv 0
          have h0_eq : ((p5 (v, mv) 0 i₀ : ℕ) : ℤ) = ((x 0 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 0) i₀]
          have h1_eq : ((p5 (v, mv) 1 i₀ : ℕ) : ℤ) = ((x 1 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 1) i₀]
          have hi0 : idx5 mv 0 = 0 := by fin_cases mv <;> rfl
          rw [hv1] at hst1 hst0; rw [hi0] at hst0
          dsimp [p5] at h0_eq h1_eq; rw [hm_spec 1]; linarith
        have h2 : idx5 mv 2 = idx5 m 2 := by
          have hst2 := step5_val (v i₀) mv 2
          have hst0 := step5_val (v i₀) mv 0
          have h0_eq : ((p5 (v, mv) 0 i₀ : ℕ) : ℤ) = ((x 0 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 0) i₀]
          have h2_eq : ((p5 (v, mv) 2 i₀ : ℕ) : ℤ) = ((x 2 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 2) i₀]
          have hi0 : idx5 mv 0 = 0 := by fin_cases mv <;> rfl
          rw [hv1] at hst2 hst0; rw [hi0] at hst0
          dsimp [p5] at h0_eq h2_eq; rw [hm_spec 2]; linarith
        exact idx5_inj mv m h1 h2
      refine Prod.ext (funext fun i => ?_) hmv_eq
      refine uniq_u5 (v i) (u i) ?_ ?_
      · have h0 := congrFun (hv_step 0) i
        have hv0 := step5_val (v i) mv 0
        have hi0 : idx5 mv 0 = 0 := by fin_cases mv <;> rfl
        rw [hi0, zero_mul, add_zero] at hv0
        rw [(hu_spec i).1, ← h0]
        exact Fin.ext (by dsimp [p5]; exact_mod_cast hv0.symm)
      · have h0 := congrFun (hv_step 0) i
        have h3 := congrFun (hv_step 3) i
        have hv0 := step5_val (v i) mv 0
        have hv3 := step5_val (v i) mv 3
        have hi0 : idx5 mv 0 = 0 := by fin_cases mv <;> rfl
        have hi3 : idx5 mv 3 = 5 := by fin_cases mv <;> rfl
        rw [hi0, zero_mul, add_zero] at hv0
        rw [hi3] at hv3
        have h0_z : ((x 0 i : ℕ) : ℤ) = ((x05 (v i) : ℕ) : ℤ) := by
          dsimp [p5] at h0; rw [← h0]; exact_mod_cast hv0
        have h3_z : ((x 3 i : ℕ) : ℤ) = ((step5 (v i) mv 3 : ℕ) : ℤ) := by
          dsimp [p5] at h3; rw [← h3]
        rw [(hu_spec i).2]; linarith
    rcases hor with hv1 | hv_neg
    · exact Or.inl (congrArg Sum.inr (congrArg Sum.inr (congrArg Sum.inl (hcheck_pos u' m' hPhi' hv1))))
    · have hrev_d : d5 (rev5 (u' i₀)) = 1 := by rw [d5_rev, hv_neg]; norm_num
      have hrev_eq := hcheck_pos (fun i => rev5 (u' i)) (revM5 m')
        ((phi_rev (Sum.inr (Sum.inr (Sum.inl (u', m'))))).trans hPhi') hrev_d
      right
      have h1 := congrArg Prod.fst hrev_eq
      have h2 := congrArg Prod.snd hrev_eq
      dsimp only at h1 h2
      refine congrArg Sum.inr (congrArg Sum.inr (congrArg Sum.inl (Prod.ext ?_ ?_)))
      · funext i; dsimp only; have := congrFun h1 i; rw [← this, rev5_invol]
      · dsimp only; rw [← h2, revM5_invol]
  · exfalso; have := w6_span_inv i₀ hx_mono hs_eq hT_card u' m' hPhi'; omega

private lemma fiber_span6 {n : ℕ} {s : Finset (Fin n → Fin 7)} {i₀ : Fin n}
    {x : Fin 4 → (Fin n → Fin 7)}
    (hcoord_inj : Set.InjOn (fun y : Fin n → Fin 7 => y i₀) (s : Set (Fin n → Fin 7)))
    (hx_mem : ∀ k : Fin 4, x k ∈ s)
    (hx_mono : StrictMono (fun k : Fin 4 => (x k i₀ : ℕ)))
    (hs_eq : s = Finset.univ.image x)
    (hT_card : (s.image fun y => y i₀).card = 4)
    (hline : ∀ (k : Fin 4) (i : Fin n),
      (((x k i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) * (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) =
      (((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) * (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)))
    (h0lt1 : (x 0 i₀ : ℕ) < (x 1 i₀ : ℕ))
    (h1lt2 : (x 1 i₀ : ℕ) < (x 2 i₀ : ℕ))
    (h2lt3 : (x 2 i₀ : ℕ) < (x 3 i₀ : ℕ))
    (hA6 : (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 6)
    (hne24 : ¬ ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ) = 2 ∧ (x 2 i₀ : ℕ) - (x 0 i₀ : ℕ) = 4)) :
    ∃ u : Fin n → Fin 9, ∃ m : Fin 9, d6 (u i₀) ≠ 0 ∧
      Φ (Sum.inr (Sum.inr (Sum.inr (u, m)))) = s ∧
      ∀ w', Φ w' = s →
        w' = Sum.inr (Sum.inr (Sum.inr (u, m))) ∨
        w' = revW (Sum.inr (Sum.inr (Sum.inr (u, m)))) := by
  have hdvd6 : ∀ i : Fin n, ∃ q : ℤ, ((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) = 6 * q := by
    intro i
    have hA_z : ((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 6 := by omega
    by_cases hx1 : (x 1 i₀ : ℕ) - (x 0 i₀ : ℕ) = 1
    · have h1 := hline 1 i
      have hp1_z : ((x 1 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 1 := by omega
      rw [hA_z, hp1_z, one_mul] at h1
      exact ⟨((x 1 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ), by linarith⟩
    · by_cases hx2 : (x 2 i₀ : ℕ) - (x 0 i₀ : ℕ) = 5
      · have h2 := hline 2 i
        have hp2_z : ((x 2 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 5 := by omega
        rw [hA_z, hp2_z] at h2
        exact ⟨((x 3 i : ℕ) : ℤ) - ((x 2 i : ℕ) : ℤ), by linarith⟩
      · have h1 := hline 1 i
        have h2 := hline 2 i
        have hdiff : ((x 2 i₀ : ℕ) : ℤ) - ((x 1 i₀ : ℕ) : ℤ) = 1 := by omega
        have h12 : (((x 2 i : ℕ) : ℤ) - ((x 1 i : ℕ) : ℤ)) *
            (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) =
            (((x 2 i₀ : ℕ) : ℤ) - ((x 1 i₀ : ℕ) : ℤ)) *
            (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) := by linarith
        rw [hA_z, hdiff, one_mul] at h12
        exact ⟨((x 2 i : ℕ) : ℤ) - ((x 1 i : ℕ) : ℤ), by linarith⟩
  let m : Fin 9 := mkM6 ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ)) ((x 2 i₀ : ℕ) - (x 0 i₀ : ℕ))
  have hm6 := idx6_mkM6 ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ)) ((x 2 i₀ : ℕ) - (x 0 i₀ : ℕ))
    (by omega) (by omega) (by omega) hne24
  have hm_spec : ∀ k : Fin 4, idx6 m k = ((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) := by
    intro k
    fin_cases k
    · change idx6 m 0 = ((x 0 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ); exact hm6.1.trans (by omega)
    · change idx6 m 1 = ((x 1 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ); exact hm6.2.1.trans (by omega)
    · change idx6 m 2 = ((x 2 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ); exact hm6.2.2.1.trans (by omega)
    · change idx6 m 3 = ((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ); exact hm6.2.2.2.trans (by omega)
  let u : Fin n → Fin 9 := fun i => Classical.choose (exists_u6_of (x 0 i) (x 3 i) (hdvd6 i))
  have hu_spec : ∀ i : Fin n, x06 (u i) = x 0 i ∧
      6 * d6 (u i) = ((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ) :=
    fun i => Classical.choose_spec (exists_u6_of (x 0 i) (x 3 i) (hdvd6 i))
  have hud0 : d6 (u i₀) ≠ 0 := by have h := (hu_spec i₀).2; omega
  have hu_step : ∀ k : Fin 4, p6 (u, m) k = x k := by
    intro k
    ext i
    have hlk := hline k i
    have hA_z : ((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ) = 6 := by omega
    rw [hA_z, ← hm_spec k] at hlk
    have hsv := step6_val (u i) m k
    have hsp := hu_spec i
    have h0_eq : ((x06 (u i) : ℕ) : ℤ) = ((x 0 i : ℕ) : ℤ) := by rw [hsp.1]
    rw [← hsp.2] at hlk
    have h6_eq : ((x k i : ℕ) : ℤ) = ((step6 (u i) m k : ℕ) : ℤ) := by
      linarith [show idx6 m k * (6 * d6 (u i)) = 6 * (idx6 m k * d6 (u i)) by ring]
    exact_mod_cast h6_eq.symm
  have hPhi_u : Φ (Sum.inr (Sum.inr (Sum.inr (u, m)))) = s := by
    rw [hs_eq]
    dsimp [Φ]
    exact Finset.image_congr fun k _ => hu_step k
  refine ⟨u, m, hud0, hPhi_u, ?_⟩
  rintro (u' | (⟨u', m'⟩ | (⟨u', m'⟩ | ⟨u', m'⟩))) hPhi'
  · exfalso; have := w3_span_inv i₀ hx_mono hs_eq hT_card u' hPhi'; omega
  · exfalso; have := w4_span_inv i₀ hx_mono hs_eq hT_card u' m' hPhi'; omega
  · exfalso; have := w5_span_inv i₀ hx_mono hs_eq hT_card u' m' hPhi'; omega
  · have hu'_ne := hu6_ne_of_aux hT_card u' m' hPhi'
    have hor : d6 (u' i₀) = 1 ∨ d6 (u' i₀) = -1 := by
      rcases d6_cases (u' i₀) with h0 | h1 | h2
      · exact absurd h0 hu'_ne
      · exact Or.inl h1
      · exact Or.inr h2
    have hcheck_pos : ∀ (v : Fin n → Fin 9) (mv : Fin 9),
        Φ (Sum.inr (Sum.inr (Sum.inr (v, mv)))) = s → d6 (v i₀) = 1 → (v, mv) = (u, m) := by
      intro v mv hPhiv hv1
      have hidx_mono : StrictMono (idx6 mv) := by fin_cases mv <;> decide
      have hmonov : StrictMono (fun k : Fin 4 => (p6 (v, mv) k i₀ : ℕ)) := by
        intro a b hab
        dsimp [p6]
        have ha := step6_val (v i₀) mv a
        have hb := step6_val (v i₀) mv b
        rw [hv1] at ha hb
        have hlt : idx6 mv a < idx6 mv b := hidx_mono hab
        omega
      have himg_eq : Finset.univ.image (fun k : Fin 4 => (p6 (v, mv) k i₀ : ℕ)) =
          Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) := by
        have h1 : Finset.univ.image (fun k : Fin 4 => (p6 (v, mv) k i₀ : ℕ)) =
            (Φ (Sum.inr (Sum.inr (Sum.inr (v, mv))))).image (fun y => (y i₀ : ℕ)) := by
          ext z; simp [Φ]
        have h2 : Finset.univ.image (fun k : Fin 4 => (x k i₀ : ℕ)) =
            s.image (fun y => (y i₀ : ℕ)) := by ext z; simp [hs_eq]
        rw [h1, h2, hPhiv]
      have hv_step : ∀ k : Fin 4, p6 (v, mv) k = x k := by
        have hc := fin4_strictMono_eq hmonov hx_mono himg_eq
        intro k
        have hmem : p6 (v, mv) k ∈ s := by
          rw [← hPhiv]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
        exact hcoord_inj hmem (hx_mem k) (Fin.ext (hc k))
      have hmv_eq : mv = m := by
        have h1 : idx6 mv 1 = idx6 m 1 := by
          have hst1 := step6_val (v i₀) mv 1
          have hst0 := step6_val (v i₀) mv 0
          have h0_eq : ((p6 (v, mv) 0 i₀ : ℕ) : ℤ) = ((x 0 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 0) i₀]
          have h1_eq : ((p6 (v, mv) 1 i₀ : ℕ) : ℤ) = ((x 1 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 1) i₀]
          have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
          rw [hv1] at hst1 hst0; rw [hi0] at hst0
          dsimp [p6] at h0_eq h1_eq; rw [hm_spec 1]; linarith
        have h2 : idx6 mv 2 = idx6 m 2 := by
          have hst2 := step6_val (v i₀) mv 2
          have hst0 := step6_val (v i₀) mv 0
          have h0_eq : ((p6 (v, mv) 0 i₀ : ℕ) : ℤ) = ((x 0 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 0) i₀]
          have h2_eq : ((p6 (v, mv) 2 i₀ : ℕ) : ℤ) = ((x 2 i₀ : ℕ) : ℤ) := by
            rw [congrFun (hv_step 2) i₀]
          have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
          rw [hv1] at hst2 hst0; rw [hi0] at hst0
          dsimp [p6] at h0_eq h2_eq; rw [hm_spec 2]; linarith
        exact idx6_inj mv m h1 h2
      refine Prod.ext (funext fun i => ?_) hmv_eq
      refine uniq_u6 (v i) (u i) ?_ ?_
      · have h0 := congrFun (hv_step 0) i
        have hv0 := step6_val (v i) mv 0
        have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
        rw [hi0, zero_mul, add_zero] at hv0
        rw [(hu_spec i).1, ← h0]
        exact Fin.ext (by dsimp [p6]; exact_mod_cast hv0.symm)
      · have h0 := congrFun (hv_step 0) i
        have h3 := congrFun (hv_step 3) i
        have hv0 := step6_val (v i) mv 0
        have hv3 := step6_val (v i) mv 3
        have hi0 : idx6 mv 0 = 0 := by fin_cases mv <;> rfl
        have hi3 : idx6 mv 3 = 6 := by fin_cases mv <;> rfl
        rw [hi0, zero_mul, add_zero] at hv0
        rw [hi3] at hv3
        have h0_z : ((x 0 i : ℕ) : ℤ) = ((x06 (v i) : ℕ) : ℤ) := by
          dsimp [p6] at h0; rw [← h0]; exact_mod_cast hv0
        have h3_z : ((x 3 i : ℕ) : ℤ) = ((step6 (v i) mv 3 : ℕ) : ℤ) := by
          dsimp [p6] at h3; rw [← h3]
        rw [(hu_spec i).2]; linarith
    rcases hor with hv1 | hv_neg
    · exact Or.inl (congrArg Sum.inr (congrArg Sum.inr (congrArg Sum.inr (hcheck_pos u' m' hPhi' hv1))))
    · have hrev_d : d6 (rev6 (u' i₀)) = 1 := by rw [d6_rev, hv_neg]; norm_num
      have hrev_eq := hcheck_pos (fun i => rev6 (u' i)) (revM6 m')
        ((phi_rev (Sum.inr (Sum.inr (Sum.inr (u', m'))))).trans hPhi') hrev_d
      right
      have h1 := congrArg Prod.fst hrev_eq
      have h2 := congrArg Prod.snd hrev_eq
      dsimp only at h1 h2
      refine congrArg Sum.inr (congrArg Sum.inr (congrArg Sum.inr (Prod.ext ?_ ?_)))
      · funext i; dsimp only; have := congrFun h1 i; rw [← this, rev6_invol]
      · dsimp only; rw [← h2, revM6_invol]

theorem OMA.solution : type_of% @OMA.S_oeis_a178353.main := by
  classical
  intro n
  let G : Finset (Finset (Fin n → Fin 7)) :=
    Finset.univ.filter fun s =>
      s.card = 4 ∧ Collinear ℝ (OMA.S_oeis_a178353.toReal '' (s : Set (Fin n → Fin 7)))
  have ha_eq : OMA.S_oeis_a178353.a n = G.card := by
    dsimp [OMA.S_oeis_a178353.a]
    rw [← Set.ncard_coe_finset G]
    congr 1
    ext s
    simp [G]
  let W3 : Finset (Fin n → Fin 17) :=
    Finset.univ.filter fun u => ∃ i : Fin n, d3 (u i) ≠ 0
  let W4 : Finset (Fin n → Fin 13) :=
    Finset.univ.filter fun u => ∃ i : Fin n, d4 (u i) ≠ 0
  let W5 : Finset (Fin n → Fin 11) :=
    Finset.univ.filter fun u => ∃ i : Fin n, d5 (u i) ≠ 0
  let W6 : Finset (Fin n → Fin 9) :=
    Finset.univ.filter fun u => ∃ i : Fin n, d6 (u i) ≠ 0
  have hW3_card : W3.card + 7 ^ n = 17 ^ n := by
    let Z3 : Finset (Fin n → Fin 17) := Finset.univ.filter fun u => ∀ i : Fin n, d3 (u i) = 0
    have hZ3_eq : Z3 = (Finset.univ : Finset (Fin n → Fin 7)).image
        (fun f i => ⟨(f i).val, by omega⟩) := by
      ext u
      simp only [Z3, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, d3_zero_iff]
      constructor
      · intro hu; refine ⟨fun i => ⟨(u i).val, hu i⟩, funext fun i => Fin.ext rfl⟩
      · rintro ⟨f, rfl⟩ i; exact (f i).isLt
    have hZ3_card : Z3.card = 7 ^ n := by
      rw [hZ3_eq, Finset.card_image_of_injective]
      · simp
      · intro f g hfg; ext i; exact congrArg (fun h => (h i).val) hfg
    have hpart : W3.card + Z3.card = (Finset.univ : Finset (Fin n → Fin 17)).card := by
      dsimp [W3, Z3]
      simpa [not_exists] using Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → Fin 17))) (p := fun u => ∃ i : Fin n, d3 (u i) ≠ 0)
    rw [hZ3_card] at hpart
    simpa using hpart
  have hW4_card : W4.card + 7 ^ n = 13 ^ n := by
    let Z4 : Finset (Fin n → Fin 13) := Finset.univ.filter fun u => ∀ i : Fin n, d4 (u i) = 0
    have hZ4_eq : Z4 = (Finset.univ : Finset (Fin n → Fin 7)).image
        (fun f i => ⟨(f i).val, by omega⟩) := by
      ext u
      simp only [Z4, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, d4_zero_iff]
      constructor
      · intro hu; refine ⟨fun i => ⟨(u i).val, hu i⟩, funext fun i => Fin.ext rfl⟩
      · rintro ⟨f, rfl⟩ i; exact (f i).isLt
    have hZ4_card : Z4.card = 7 ^ n := by
      rw [hZ4_eq, Finset.card_image_of_injective]
      · simp
      · intro f g hfg; ext i; exact congrArg (fun h => (h i).val) hfg
    have hpart : W4.card + Z4.card = (Finset.univ : Finset (Fin n → Fin 13)).card := by
      dsimp [W4, Z4]
      simpa [not_exists] using Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → Fin 13))) (p := fun u => ∃ i : Fin n, d4 (u i) ≠ 0)
    rw [hZ4_card] at hpart
    simpa using hpart
  have hW5_card : W5.card + 7 ^ n = 11 ^ n := by
    let Z5 : Finset (Fin n → Fin 11) := Finset.univ.filter fun u => ∀ i : Fin n, d5 (u i) = 0
    have hZ5_eq : Z5 = (Finset.univ : Finset (Fin n → Fin 7)).image
        (fun f i => ⟨(f i).val, by omega⟩) := by
      ext u
      simp only [Z5, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, d5_zero_iff]
      constructor
      · intro hu; refine ⟨fun i => ⟨(u i).val, hu i⟩, funext fun i => Fin.ext rfl⟩
      · rintro ⟨f, rfl⟩ i; exact (f i).isLt
    have hZ5_card : Z5.card = 7 ^ n := by
      rw [hZ5_eq, Finset.card_image_of_injective]
      · simp
      · intro f g hfg; ext i; exact congrArg (fun h => (h i).val) hfg
    have hpart : W5.card + Z5.card = (Finset.univ : Finset (Fin n → Fin 11)).card := by
      dsimp [W5, Z5]
      simpa [not_exists] using Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → Fin 11))) (p := fun u => ∃ i : Fin n, d5 (u i) ≠ 0)
    rw [hZ5_card] at hpart
    simpa using hpart
  have hW6_card : W6.card + 7 ^ n = 9 ^ n := by
    let Z6 : Finset (Fin n → Fin 9) := Finset.univ.filter fun u => ∀ i : Fin n, d6 (u i) = 0
    have hZ6_eq : Z6 = (Finset.univ : Finset (Fin n → Fin 7)).image
        (fun f i => ⟨(f i).val, by omega⟩) := by
      ext u
      simp only [Z6, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, d6_zero_iff]
      constructor
      · intro hu; refine ⟨fun i => ⟨(u i).val, hu i⟩, funext fun i => Fin.ext rfl⟩
      · rintro ⟨f, rfl⟩ i; exact (f i).isLt
    have hZ6_card : Z6.card = 7 ^ n := by
      rw [hZ6_eq, Finset.card_image_of_injective]
      · simp
      · intro f g hfg; ext i; exact congrArg (fun h => (h i).val) hfg
    have hpart : W6.card + Z6.card = (Finset.univ : Finset (Fin n → Fin 9)).card := by
      dsimp [W6, Z6]
      simpa [not_exists] using Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n → Fin 9))) (p := fun u => ∃ i : Fin n, d6 (u i) ≠ 0)
    rw [hZ6_card] at hpart
    simpa using hpart
  let W : Finset (WCode n) :=
    W3.disjSum ((W4 ×ˢ (Finset.univ : Finset (Fin 3))).disjSum
      ((W5 ×ˢ (Finset.univ : Finset (Fin 6))).disjSum
        (W6 ×ˢ (Finset.univ : Finset (Fin 9)))))
  have hW_card : W.card = W3.card + 3 * W4.card + 6 * W5.card + 9 * W6.card := by
    dsimp [W]
    rw [Finset.card_disjSum, Finset.card_disjSum, Finset.card_disjSum,
      Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_fin, Finset.card_fin, Finset.card_fin]
    ring
  have hrev_mem : ∀ w ∈ W, revW w ∈ W := by
    intro w hw
    rcases Finset.mem_disjSum.mp hw with ⟨u, hu, rfl⟩ | ⟨w1, hw1, rfl⟩
    · refine Finset.mem_disjSum.mpr (Or.inl ⟨fun i => rev3 (u i), ?_, rfl⟩)
      simp only [W3, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      obtain ⟨i, hi⟩ := hu
      exact ⟨i, by rw [d3_rev]; omega⟩
    · rcases Finset.mem_disjSum.mp hw1 with ⟨⟨u, m⟩, hwm, rfl⟩ | ⟨w2, hw2, rfl⟩
      · refine Finset.mem_disjSum.mpr (Or.inr ⟨Sum.inl (fun i => rev4 (u i), revM4 m),
          Finset.mem_disjSum.mpr (Or.inl ⟨(fun i => rev4 (u i), revM4 m), ?_, rfl⟩), rfl⟩)
        simp only [Finset.mem_product, W4, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
          at hwm ⊢
        obtain ⟨i, hi⟩ := hwm
        exact ⟨i, by rw [d4_rev]; omega⟩
      · rcases Finset.mem_disjSum.mp hw2 with ⟨⟨u, m⟩, hwm, rfl⟩ | ⟨⟨u, m⟩, hwm, rfl⟩
        · refine Finset.mem_disjSum.mpr (Or.inr ⟨Sum.inr (Sum.inl (fun i => rev5 (u i), revM5 m)),
            Finset.mem_disjSum.mpr (Or.inr ⟨Sum.inl (fun i => rev5 (u i), revM5 m),
              Finset.mem_disjSum.mpr (Or.inl ⟨(fun i => rev5 (u i), revM5 m), ?_, rfl⟩), rfl⟩), rfl⟩)
          simp only [Finset.mem_product, W5, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
            at hwm ⊢
          obtain ⟨i, hi⟩ := hwm
          exact ⟨i, by rw [d5_rev]; omega⟩
        · refine Finset.mem_disjSum.mpr (Or.inr ⟨Sum.inr (Sum.inr (fun i => rev6 (u i), revM6 m)),
            Finset.mem_disjSum.mpr (Or.inr ⟨Sum.inr (fun i => rev6 (u i), revM6 m),
              Finset.mem_disjSum.mpr (Or.inr ⟨(fun i => rev6 (u i), revM6 m), ?_, rfl⟩), rfl⟩), rfl⟩)
          simp only [Finset.mem_product, W6, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
            at hwm ⊢
          obtain ⟨i, hi⟩ := hwm
          exact ⟨i, by rw [d6_rev]; omega⟩
  have hrev_ne : ∀ w ∈ W, revW w ≠ w := by
    intro w hw heq
    rcases Finset.mem_disjSum.mp hw with ⟨u, hu, rfl⟩ | ⟨w1, hw1, rfl⟩
    · simp only [W3, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨i, hi⟩ := hu
      have h1 : rev3 (u i) = u i :=
        congrArg (fun x => match x with | Sum.inl v => v i | _ => u i) heq
      exact rev3_ne (u i) hi h1
    · rcases Finset.mem_disjSum.mp hw1 with ⟨⟨u, m⟩, hwm, rfl⟩ | ⟨w2, hw2, rfl⟩
      · simp only [Finset.mem_product, W4, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
          at hwm
        obtain ⟨i, hi⟩ := hwm
        have h1 : rev4 (u i) = u i :=
          congrArg (fun x => match x with | Sum.inr (Sum.inl p) => p.1 i | _ => u i) heq
        exact rev4_ne (u i) hi h1
      · rcases Finset.mem_disjSum.mp hw2 with ⟨⟨u, m⟩, hwm, rfl⟩ | ⟨⟨u, m⟩, hwm, rfl⟩
        · simp only [Finset.mem_product, W5, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
            at hwm
          obtain ⟨i, hi⟩ := hwm
          have h1 : rev5 (u i) = u i :=
            congrArg (fun x => match x with | Sum.inr (Sum.inr (Sum.inl p)) => p.1 i | _ => u i) heq
          exact rev5_ne (u i) hi h1
        · simp only [Finset.mem_product, W6, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
            at hwm
          obtain ⟨i, hi⟩ := hwm
          have h1 : rev6 (u i) = u i :=
            congrArg (fun x => match x with | Sum.inr (Sum.inr (Sum.inr p)) => p.1 i | _ => u i) heq
          exact rev6_ne (u i) hi h1
  have hPhi_mem : ∀ w ∈ W, Φ w ∈ G := by
    intro w hw
    rcases Finset.mem_disjSum.mp hw with ⟨u, hu, rfl⟩ | ⟨w1, hw1, rfl⟩
    · simp only [W3, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨i₀, hi₀⟩ := hu
      have hinj : Function.Injective (p3 u) := fun j k hjk =>
        step3_inj_of_d_ne (u i₀) hi₀ (congrFun hjk i₀)
      have hcard : (Φ (Sum.inl u)).card = 4 := by
        dsimp [Φ]; rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
      have hcol : Collinear ℝ
          (OMA.S_oeis_a178353.toReal '' (Φ (Sum.inl u) : Set (Fin n → Fin 7))) := by
        rw [collinear_iff_exists_forall_eq_smul_vadd]
        refine ⟨fun i => ((x03 (u i) : ℕ) : ℝ), fun i => (d3 (u i) : ℝ), ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        simp only [Φ, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨k, rfl⟩ := hx
        refine ⟨(k : ℝ), funext fun i => ?_⟩
        dsimp [OMA.S_oeis_a178353.toReal, p3]
        have hv : ((step3 (u i) k : ℕ) : ℝ) = ((x03 (u i) : ℕ) : ℝ) + (k : ℝ) * (d3 (u i) : ℝ) := by
          exact_mod_cast step3_val (u i) k
        simpa [vadd_eq_add, add_comm] using hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, hcol⟩
    · rcases Finset.mem_disjSum.mp hw1 with ⟨⟨u, m⟩, hwm, rfl⟩ | ⟨w2, hw2, rfl⟩
      · simp only [Finset.mem_product, W4, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
          at hwm
        obtain ⟨i₀, hi₀⟩ := hwm
        have hinj : Function.Injective (p4 (u, m)) := fun j k hjk =>
          step4_inj_of_d_ne (u i₀) m hi₀ (congrFun hjk i₀)
        have hcard : (Φ (Sum.inr (Sum.inl (u, m)))).card = 4 := by
          dsimp [Φ]; rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
        have hcol : Collinear ℝ (OMA.S_oeis_a178353.toReal ''
            (Φ (Sum.inr (Sum.inl (u, m))) : Set (Fin n → Fin 7))) := by
          rw [collinear_iff_exists_forall_eq_smul_vadd]
          refine ⟨fun i => ((x04 (u i) : ℕ) : ℝ), fun i => (d4 (u i) : ℝ), ?_⟩
          rintro _ ⟨x, hx, rfl⟩
          simp only [Φ, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hx
          obtain ⟨k, rfl⟩ := hx
          refine ⟨(idx4 m k : ℝ), funext fun i => ?_⟩
          dsimp [OMA.S_oeis_a178353.toReal, p4]
          have hv : ((step4 (u i) m k : ℕ) : ℝ) =
              ((x04 (u i) : ℕ) : ℝ) + (idx4 m k : ℝ) * (d4 (u i) : ℝ) := by
            exact_mod_cast step4_val (u i) m k
          simpa [vadd_eq_add, add_comm] using hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, hcol⟩
      · rcases Finset.mem_disjSum.mp hw2 with ⟨⟨u, m⟩, hwm, rfl⟩ | ⟨⟨u, m⟩, hwm, rfl⟩
        · simp only [Finset.mem_product, W5, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
            at hwm
          obtain ⟨i₀, hi₀⟩ := hwm
          have hinj : Function.Injective (p5 (u, m)) := fun j k hjk =>
            step5_inj_of_d_ne (u i₀) m hi₀ (congrFun hjk i₀)
          have hcard : (Φ (Sum.inr (Sum.inr (Sum.inl (u, m))))).card = 4 := by
            dsimp [Φ]; rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
          have hcol : Collinear ℝ (OMA.S_oeis_a178353.toReal ''
              (Φ (Sum.inr (Sum.inr (Sum.inl (u, m)))) : Set (Fin n → Fin 7))) := by
            rw [collinear_iff_exists_forall_eq_smul_vadd]
            refine ⟨fun i => ((x05 (u i) : ℕ) : ℝ), fun i => (d5 (u i) : ℝ), ?_⟩
            rintro _ ⟨x, hx, rfl⟩
            simp only [Φ, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hx
            obtain ⟨k, rfl⟩ := hx
            refine ⟨(idx5 m k : ℝ), funext fun i => ?_⟩
            dsimp [OMA.S_oeis_a178353.toReal, p5]
            have hv : ((step5 (u i) m k : ℕ) : ℝ) =
                ((x05 (u i) : ℕ) : ℝ) + (idx5 m k : ℝ) * (d5 (u i) : ℝ) := by
              exact_mod_cast step5_val (u i) m k
            simpa [vadd_eq_add, add_comm] using hv
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, hcol⟩
        · simp only [Finset.mem_product, W6, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
            at hwm
          obtain ⟨i₀, hi₀⟩ := hwm
          have hinj : Function.Injective (p6 (u, m)) := fun j k hjk =>
            step6_inj_of_d_ne (u i₀) m hi₀ (congrFun hjk i₀)
          have hcard : (Φ (Sum.inr (Sum.inr (Sum.inr (u, m))))).card = 4 := by
            dsimp [Φ]; rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
          have hcol : Collinear ℝ (OMA.S_oeis_a178353.toReal ''
              (Φ (Sum.inr (Sum.inr (Sum.inr (u, m)))) : Set (Fin n → Fin 7))) := by
            rw [collinear_iff_exists_forall_eq_smul_vadd]
            refine ⟨fun i => ((x06 (u i) : ℕ) : ℝ), fun i => (d6 (u i) : ℝ), ?_⟩
            rintro _ ⟨x, hx, rfl⟩
            simp only [Φ, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hx
            obtain ⟨k, rfl⟩ := hx
            refine ⟨(idx6 m k : ℝ), funext fun i => ?_⟩
            dsimp [OMA.S_oeis_a178353.toReal, p6]
            have hv : ((step6 (u i) m k : ℕ) : ℝ) =
                ((x06 (u i) : ℕ) : ℝ) + (idx6 m k : ℝ) * (d6 (u i) : ℝ) := by
              exact_mod_cast step6_val (u i) m k
            simpa [vadd_eq_add, add_comm] using hv
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, hcol⟩
  have hfiber_pair : ∀ s ∈ G, ∃ w ∈ W, Φ w = s ∧ ∀ w' ∈ W, Φ w' = s → w' = w ∨ w' = revW w := by
    intro s hs
    obtain ⟨hs_card, hs_col⟩ := (Finset.mem_filter.mp hs).2
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hs_col
    obtain ⟨p₀, v, hv⟩ := hs_col
    have hv_ne : v ≠ 0 := by
      intro hv0
      have hsub1 : s.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        obtain ⟨ra, hra⟩ := hv _ ⟨a, ha, rfl⟩
        obtain ⟨rb, hrb⟩ := hv _ ⟨b, hb, rfl⟩
        have htr : OMA.S_oeis_a178353.toReal a = OMA.S_oeis_a178353.toReal b := by
          rw [hra, hrb, hv0, smul_zero, smul_zero]
        exact funext fun i => Fin.ext (by
          have := congrFun htr i
          dsimp [OMA.S_oeis_a178353.toReal] at this
          exact_mod_cast this)
      omega
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, v i₀ ≠ 0 := by
      by_contra h0
      push Not at h0
      exact hv_ne (funext h0)
    have hcoord_inj : Set.InjOn (fun x : Fin n → Fin 7 => x i₀) (s : Set (Fin n → Fin 7)) := by
      intro a ha b hb hab
      obtain ⟨ra, hra⟩ := hv _ ⟨a, ha, rfl⟩
      obtain ⟨rb, hrb⟩ := hv _ ⟨b, hb, rfl⟩
      have ha0 := congrFun hra i₀
      have hb0 := congrFun hrb i₀
      have hab0 : a i₀ = b i₀ := hab
      have htr0 : OMA.S_oeis_a178353.toReal a i₀ = OMA.S_oeis_a178353.toReal b i₀ := by
        dsimp [OMA.S_oeis_a178353.toReal]
        rw [hab0]
      rw [ha0, hb0] at htr0
      have hr : ra = rb := by
        have : (ra - rb) * v i₀ = 0 := by
          simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at htr0
          linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact absurd h hi₀
      have htr : OMA.S_oeis_a178353.toReal a = OMA.S_oeis_a178353.toReal b := by
        rw [hra, hrb, hr]
      exact funext fun i => Fin.ext (by
        have := congrFun htr i
        dsimp [OMA.S_oeis_a178353.toReal] at this
        exact_mod_cast this)
    let T : Finset (Fin 7) := s.image (fun x => x i₀)
    have hT_card : T.card = 4 := by
      dsimp [T]
      rw [Finset.card_image_of_injOn hcoord_inj, hs_card]
    let eT : Fin 4 ≃o T := T.orderIsoOfFin hT_card
    have hx_ex : ∀ k : Fin 4, ∃! x ∈ s, x i₀ = (eT k).1 := by
      intro k
      have hkT : (eT k).1 ∈ T := (eT k).2
      dsimp [T] at hkT
      obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hkT
      exact ⟨x, ⟨hx, hxi⟩, fun y ⟨hy, hyi⟩ => hcoord_inj hy hx (hyi.trans hxi.symm)⟩
    let x : Fin 4 → (Fin n → Fin 7) := fun k => Classical.choose (hx_ex k)
    have hx_mem : ∀ k : Fin 4, x k ∈ s := fun k => (Classical.choose_spec (hx_ex k)).1.1
    have hx_coord : ∀ k : Fin 4, x k i₀ = (eT k).1 := fun k => (Classical.choose_spec (hx_ex k)).1.2
    have hx_mono : StrictMono (fun k : Fin 4 => (x k i₀ : ℕ)) := by
      intro j k hjk
      dsimp only
      rw [hx_coord j, hx_coord k]
      exact eT.strictMono hjk
    have hs_eq : s = Finset.univ.image x := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        have hyT : y i₀ ∈ T := Finset.mem_image_of_mem _ hy
        let k := eT.symm ⟨y i₀, hyT⟩
        have hk : (eT k).1 = y i₀ := congrArg Subtype.val (eT.apply_symm_apply ⟨y i₀, hyT⟩)
        have hxy : x k = y := hcoord_inj (hx_mem k) hy ((hx_coord k).trans hk)
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hxy⟩
      · rw [hs_card, Finset.card_image_of_injective]
        · rw [Finset.card_fin]
        · intro j k hjk
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact (hx_mono h).ne (congrArg (fun f => (f i₀ : ℕ)) hjk)
          · exact (hx_mono h).ne.symm (congrArg (fun f => (f i₀ : ℕ)) hjk)
    have hline : ∀ (k : Fin 4) (i : Fin n),
        (((x k i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) * (((x 3 i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) =
        (((x k i₀ : ℕ) : ℤ) - ((x 0 i₀ : ℕ) : ℤ)) * (((x 3 i : ℕ) : ℤ) - ((x 0 i : ℕ) : ℤ)) := by
      intro k i
      obtain ⟨r0, hr0⟩ := hv _ ⟨x 0, hx_mem 0, rfl⟩
      obtain ⟨rk, hrk⟩ := hv _ ⟨x k, hx_mem k, rfl⟩
      obtain ⟨r3, hr3⟩ := hv _ ⟨x 3, hx_mem 3, rfl⟩
      have h0i := congrFun hr0 i
      have hki := congrFun hrk i
      have h3i := congrFun hr3 i
      have h00 := congrFun hr0 i₀
      have hk0 := congrFun hrk i₀
      have h30 := congrFun hr3 i₀
      simp only [OMA.S_oeis_a178353.toReal, vadd_eq_add, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] at h0i hki h3i h00 hk0 h30
      have hreal : ((((x k i : ℕ) : ℝ) - ((x 0 i : ℕ) : ℝ)) *
            (((x 3 i₀ : ℕ) : ℝ) - ((x 0 i₀ : ℕ) : ℝ))) =
          ((((x k i₀ : ℕ) : ℝ) - ((x 0 i₀ : ℕ) : ℝ)) *
            (((x 3 i : ℕ) : ℝ) - ((x 0 i : ℕ) : ℝ))) := by
        rw [hki, h0i, h30, h00, hk0, h3i]
        ring
      exact_mod_cast hreal
    have h0lt1 : (x 0 i₀ : ℕ) < (x 1 i₀ : ℕ) := hx_mono (by decide : (0 : Fin 4) < 1)
    have h1lt2 : (x 1 i₀ : ℕ) < (x 2 i₀ : ℕ) := hx_mono (by decide : (1 : Fin 4) < 2)
    have h2lt3 : (x 2 i₀ : ℕ) < (x 3 i₀ : ℕ) := hx_mono (by decide : (2 : Fin 4) < 3)
    have h3le6 : (x 3 i₀ : ℕ) ≤ 6 := Nat.lt_succ_iff.mp (x 3 i₀).isLt
    by_cases h3case : (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 3 ∨
        ((x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 6 ∧
          (x 1 i₀ : ℕ) - (x 0 i₀ : ℕ) = 2 ∧ (x 2 i₀ : ℕ) - (x 0 i₀ : ℕ) = 4)
    · have h0lt3 : (x 0 i₀ : ℕ) < (x 3 i₀ : ℕ) := by omega
      have h31 : 3 * ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ)) = (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) := by omega
      have h32 : 3 * ((x 2 i₀ : ℕ) - (x 0 i₀ : ℕ)) = 2 * ((x 3 i₀ : ℕ) - (x 0 i₀ : ℕ)) := by omega
      have hD : (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 3 ∨ (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 6 := by omega
      obtain ⟨u, hud0, hPhi_u, huniq⟩ := fiber_span3 hcoord_inj hx_mem hx_mono hs_eq hT_card
        hline h0lt3 h31 h32 hD
      refine ⟨Sum.inl u, Finset.mem_disjSum.mpr (Or.inl ⟨u, ?_, rfl⟩), hPhi_u,
        fun w' _ hPhi' => huniq w' hPhi'⟩
      simp only [W3, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i₀, hud0⟩
    · by_cases hA4 : (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 4
      · obtain ⟨u, m, hud0, hPhi_u, huniq⟩ := fiber_span4 hcoord_inj hx_mem hx_mono hs_eq hT_card
          hline h0lt1 h1lt2 h2lt3 hA4
        refine ⟨Sum.inr (Sum.inl (u, m)), Finset.mem_disjSum.mpr (Or.inr ⟨Sum.inl (u, m),
          Finset.mem_disjSum.mpr (Or.inl ⟨(u, m), ?_, rfl⟩), rfl⟩), hPhi_u,
          fun w' _ hPhi' => huniq w' hPhi'⟩
        simp only [Finset.mem_product, W4, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact ⟨i₀, hud0⟩
      · by_cases hA5 : (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 5
        · obtain ⟨u, m, hud0, hPhi_u, huniq⟩ := fiber_span5 hcoord_inj hx_mem hx_mono hs_eq hT_card
            hline h0lt1 h1lt2 h2lt3 hA5
          refine ⟨Sum.inr (Sum.inr (Sum.inl (u, m))),
            Finset.mem_disjSum.mpr (Or.inr ⟨Sum.inr (Sum.inl (u, m)),
              Finset.mem_disjSum.mpr (Or.inr ⟨Sum.inl (u, m),
                Finset.mem_disjSum.mpr (Or.inl ⟨(u, m), ?_, rfl⟩), rfl⟩), rfl⟩),
            hPhi_u, fun w' _ hPhi' => huniq w' hPhi'⟩
          simp only [Finset.mem_product, W5, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
          exact ⟨i₀, hud0⟩
        · have hA6 : (x 3 i₀ : ℕ) - (x 0 i₀ : ℕ) = 6 := by omega
          have hne24 : ¬ ((x 1 i₀ : ℕ) - (x 0 i₀ : ℕ) = 2 ∧
              (x 2 i₀ : ℕ) - (x 0 i₀ : ℕ) = 4) := by omega
          obtain ⟨u, m, hud0, hPhi_u, huniq⟩ := fiber_span6 hcoord_inj hx_mem hx_mono hs_eq hT_card
            hline h0lt1 h1lt2 h2lt3 hA6 hne24
          refine ⟨Sum.inr (Sum.inr (Sum.inr (u, m))),
            Finset.mem_disjSum.mpr (Or.inr ⟨Sum.inr (Sum.inr (u, m)),
              Finset.mem_disjSum.mpr (Or.inr ⟨Sum.inr (u, m),
                Finset.mem_disjSum.mpr (Or.inr ⟨(u, m), ?_, rfl⟩), rfl⟩), rfl⟩),
            hPhi_u, fun w' _ hPhi' => huniq w' hPhi'⟩
          simp only [Finset.mem_product, W6, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
          exact ⟨i₀, hud0⟩
  have hcard_eq : W.card = 2 * G.card := by
    rw [Finset.card_eq_sum_card_fiberwise hPhi_mem]
    have hfib2 : ∀ s ∈ G, (W.filter fun w => Φ w = s).card = 2 := by
      intro s hs
      obtain ⟨w, hw, hPhiw, huniq⟩ := hfiber_pair s hs
      have hset : W.filter (fun w' => Φ w' = s) = {w, revW w} := by
        ext w'
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hw', hPhiw'⟩
          exact huniq w' hw' hPhiw'
        · rintro (rfl | rfl)
          · exact ⟨hw, hPhiw⟩
          · exact ⟨hrev_mem w hw, (phi_rev w).trans hPhiw⟩
      rw [hset, Finset.card_pair (hrev_ne w hw).symm]
    rw [Finset.sum_congr rfl hfib2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hz3 : (W3.card : ℤ) + 7 ^ n = 17 ^ n := by exact_mod_cast hW3_card
  have hz4 : (W4.card : ℤ) + 7 ^ n = 13 ^ n := by exact_mod_cast hW4_card
  have hz5 : (W5.card : ℤ) + 7 ^ n = 11 ^ n := by exact_mod_cast hW5_card
  have hz6 : (W6.card : ℤ) + 7 ^ n = 9 ^ n := by exact_mod_cast hW6_card
  have hzW : (W.card : ℤ) = (W3.card : ℤ) + 3 * (W4.card : ℤ) + 6 * (W5.card : ℤ) +
      9 * (W6.card : ℤ) := by exact_mod_cast hW_card
  have hzc : (W.card : ℤ) = 2 * (G.card : ℤ) := by exact_mod_cast hcard_eq
  rw [ha_eq]
  linarith
