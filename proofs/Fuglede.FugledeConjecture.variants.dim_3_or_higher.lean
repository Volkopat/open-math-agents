import FormalConjectures.Wikipedia.Fuglede
import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircleMulti

open MeasureTheory

namespace FugledeScratch

/-- Tiling of a group by a set A with complement B (unique representation). -/
def TilesWith {G : Type*} [Add G] (A B : Set G) : Prop :=
  ∀ z : G, ∃! p : G × G, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = z

def boxSet (F : Set (ℤ × ℤ)) : Set (Fin 2 → ℝ) := {x | (⌊x 0⌋, ⌊x 1⌋) ∈ F}

lemma key (F : Set (ℤ × ℤ)) (x t : Fin 2 → ℝ) (n : ℤ × ℤ) :
    (x + ![(n.1 : ℝ), (n.2 : ℝ)]) ∈ translateSet (boxSet F) t ↔
      n - (-⌊x 0 - t 0⌋, -⌊x 1 - t 1⌋) ∈ F := by
  simp only [translateSet, boxSet, Set.mem_setOf_eq, Pi.sub_apply, Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : x 0 + (n.1 : ℝ) - t 0 = (x 0 - t 0) + (n.1 : ℝ) := by ring
  have h1 : x 1 + (n.2 : ℝ) - t 1 = (x 1 - t 1) + (n.2 : ℝ) := by ring
  rw [h0, h1, Int.floor_add_intCast, Int.floor_add_intCast]
  have : n - (-⌊x 0 - t 0⌋, -⌊x 1 - t 1⌋) = (⌊x 0 - t 0⌋ + n.1, ⌊x 1 - t 1⌋ + n.2) := by
    ext <;> simp <;> ring
  rw [this]

abbrev G := ZMod 60 × ZMod 12

def Alist : List G := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (4, 4), (8, 4), (8, 10), (9, 9), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (13, 2), (13, 8), (14, 2), (19, 7), (24, 0), (28, 2), (28, 8), (29, 5), (33, 0), (33, 6), (34, 10), (36, 0), (36, 1), (36, 2), (36, 3), (36, 4), (36, 5), (36, 6), (36, 7), (36, 8), (36, 9), (36, 10), (36, 11), (39, 3), (44, 8), (48, 0), (48, 6), (49, 1), (53, 4), (53, 10), (54, 6), (59, 11)]

def emb (u : ZMod 12) : ZMod 60 := 5 * (u.val : ZMod 60)

lemma L0 : ∀ k : ZMod 12, ∀ t : ZMod 60, (t = 0 ∨ t = 36 ∨ t = 12) → (t, k) ∈ Alist := by
  decide +kernel

lemma L4 : ∀ k : ZMod 12, (25 * (k.val : ZMod 60) + 24, k) ∈ Alist := by decide +kernel

lemma Xcases : ∀ X : ZMod 60, 12 * X ≠ 0 → ∃ t : ZMod 60, (t = 0 ∨ t = 36 ∨ t = 12) ∧
    ∃ k : ZMod 12, 25 * (k.val : ZMod 60) + 24 - t = X ∨ t - (25 * (k.val : ZMod 60) + 24) = X := by
  decide +kernel

lemma G1 (d : G) (hd : 12 * d.1 ≠ 0) : ∃ a ∈ Alist, a + d ∈ Alist := by
  obtain ⟨t, ht, k, hk | hk⟩ := Xcases d.1 hd
  · refine ⟨(t, k - d.2), L0 _ _ ht, ?_⟩
    have : (t, k - d.2) + d = (25 * (k.val : ZMod 60) + 24, k) := by
      ext
      · simp only [Prod.fst_add]; rw [← hk]; ring
      · simp
    rw [this]; exact L4 k
  · refine ⟨(25 * (k.val : ZMod 60) + 24, k), L4 k, ?_⟩
    have : (25 * (k.val : ZMod 60) + 24, k) + d = (t, k + d.2) := by
      ext
      · simp only [Prod.fst_add]; rw [← hk]; ring
      · simp
    rw [this]; exact L0 _ _ ht

lemma G2 : ∀ a ∈ Alist, 12 * a.1 = 0 → a.1 = 0 := by decide +kernel

lemma hemb12 : ∀ u : ZMod 12, 12 * emb u = 0 := by decide +kernel
lemma hemb_sub : ∀ u u' : ZMod 12, emb (u - u') = emb u - emb u' := by decide +kernel
lemma hemb_inj : ∀ u u' : ZMod 12, emb u = emb u' → u = u' := by decide +kernel

def c6 : ZMod 12 →+* ZMod 6 := ZMod.castHom (by norm_num) (ZMod 6)

def ev (x : ZMod 6) : ℕ := if x.val % 2 = 0 then 1 else 0
def ev12 (x : ZMod 12) : ℕ := if x.val % 2 = 0 then 1 else 0

lemma CI : ∀ du dy : ZMod 12, (du = 4 ∨ du = 8) → c6 (dy - du) = 0 →
    ∃ a ∈ Alist, a + (emb du, dy) ∈ Alist := by decide +kernel

lemma CII : ∀ du dy : ZMod 12, (du = 1 ∨ du = 5 ∨ du = 9) → c6 (dy - du) = 3 →
    ∃ a ∈ Alist, a + (emb du, dy) ∈ Alist := by decide +kernel

lemma CV1 : ∀ du : ZMod 12, du ≠ 0 → ∃ a ∈ Alist, a + (emb du, 5 * du) ∈ Alist := by
  decide +kernel

lemma par : ∀ a b : ZMod 12, ev12 (a - 5 * b) = ev (c6 (a - b)) := by decide +kernel

lemma sum_ev12 : ∑ v : ZMod 12, ev12 v = 6 := by decide +kernel

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 10000 in
lemma localLemma : ∀ t0 t1 t2 s0 s1 s2 : ZMod 6, (t0 ≠ t1 ∧ t0 ≠ t2 ∧ t1 ≠ t2 ∧
    s0 ≠ s1 ∧ s0 ≠ s2 ∧ s1 ≠ s2 ∧
    t0 - s0 ≠ 3 ∧ t0 - s1 ≠ 3 ∧ t0 - s2 ≠ 3 ∧ t1 - s0 ≠ 3 ∧ t1 - s1 ≠ 3 ∧ t1 - s2 ≠ 3 ∧
    t2 - s0 ≠ 3 ∧ t2 - s1 ≠ 3 ∧ t2 - s2 ≠ 3) →
    ev t0 + ev t1 + ev t2 = ev s0 + ev s1 + ev s2 := by decide +kernel

lemma sum12 (f : ZMod 12 → ℕ) : ∑ u, f u =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  have : (Finset.univ : Finset (ZMod 12)) = {0,1,2,3,4,5,6,7,8,9,10,11} := by decide
  rw [this]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  ring

theorem H2_proof : ¬ ∃ B : Set G, TilesWith {p | p ∈ Alist} B := by
  rintro ⟨B, hB⟩
  have uniq : ∀ a, a ∈ Alist → ∀ a', a' ∈ Alist → ∀ b ∈ B, ∀ b' ∈ B,
      a + b = a' + b' → b = b' := by
    intro a ha a' ha' b hb b' hb' h
    obtain ⟨p, -, hp⟩ := hB (a + b)
    have e1 := hp (a, b) ⟨ha, hb, rfl⟩
    have e2 := hp (a', b') ⟨ha', hb', h.symm⟩
    have := e1.trans e2.symm
    exact (Prod.ext_iff.1 this).2
  obtain ⟨⟨a0, b0⟩, ⟨-, hb0, -⟩, -⟩ := hB 0
  have h1 : ∀ b ∈ B, 12 * (b - b0).1 = 0 := by
    intro b hb
    by_contra hne
    obtain ⟨a, ha, ha'⟩ := G1 (b - b0) hne
    have := uniq a ha (a + (b - b0)) ha' b hb b0 hb0 (by abel)
    apply hne
    rw [this]
    simp
  have h2 : ∀ u : ZMod 12, ∃ b ∈ B, (b - b0).1 = emb u := by
    intro u
    obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, -⟩ := hB ((emb u, 0) + b0)
    refine ⟨b, hb, ?_⟩
    have hb1 := h1 b hb
    have hab1 : a.1 + b.1 = emb u + b0.1 := by
      have := congrArg Prod.fst hab
      simpa using this
    have ha1 : a.1 = emb u - (b - b0).1 := by
      simp only [Prod.fst_sub]
      linear_combination hab1
    have h12 : 12 * a.1 = 0 := by rw [ha1, mul_sub, hemb12, hb1, sub_zero]
    have := G2 a ha h12
    rw [ha1] at this
    linear_combination -this
  choose bf hbf hbf1 using h2
  set g : ZMod 12 → ZMod 12 := fun u => (bf u - b0).2 with hg
  have h3 : ∀ u u', u ≠ u' → ∀ a ∈ Alist, a + (emb (u - u'), g u - g u') ∉ Alist := by
    intro u u' hne a ha ha'
    have hd : (emb (u - u'), g u - g u') = bf u - bf u' := by
      ext
      · rw [hemb_sub, ← hbf1 u, ← hbf1 u']
        simp only [Prod.fst_sub]
        ring
      · simp only [hg, Prod.snd_sub]
        ring
    rw [hd] at ha'
    have := uniq a ha _ ha' (bf u) (hbf u) (bf u') (hbf u') (by abel)
    apply hne
    apply hemb_inj
    calc emb u = (bf u - b0).1 := (hbf1 u).symm
      _ = (bf u' - b0).1 := by rw [this]
      _ = emb u' := hbf1 u'
  set σ : ZMod 12 → ZMod 6 := fun u => c6 (g u - u) with hσ
  have hcs : ∀ u u', c6 ((g u - g u') - (u - u')) = σ u - σ u' := by
    intro u u'
    simp only [hσ, ← map_sub]
    congr 1
    ring
  have hI : ∀ u u', (u - u' = 4 ∨ u - u' = 8) → σ u ≠ σ u' := by
    intro u u' hd heq
    have hne : u ≠ u' := by
      intro h
      rw [h, sub_self] at hd
      revert hd
      decide
    obtain ⟨a, ha, ha'⟩ := CI (u - u') (g u - g u') hd (by rw [hcs, heq, sub_self])
    exact h3 u u' hne a ha ha'
  have hII : ∀ u u', (u - u' = 1 ∨ u - u' = 5 ∨ u - u' = 9) → σ u - σ u' ≠ 3 := by
    intro u u' hd heq
    have hne : u ≠ u' := by
      intro h
      rw [h, sub_self] at hd
      revert hd
      decide
    obtain ⟨a, ha, ha'⟩ := CII (u - u') (g u - g u') hd (by rw [hcs, heq])
    exact h3 u u' hne a ha ha'
  have hV1 : Function.Injective (fun u => g u - 5 * u) := by
    intro u u' h
    by_contra hne
    simp only at h
    obtain ⟨a, ha, ha'⟩ := CV1 (u - u') (sub_ne_zero.2 hne)
    have h5 : g u - g u' = 5 * (u - u') := by linear_combination h
    apply h3 u u' hne a ha
    rw [h5]
    exact ha'
  have hsum : ∑ u, ev (σ u) = 6 := by
    have : ∑ u, ev12 (g u - 5 * u) = 6 := by
      rw [← sum_ev12]
      exact Fintype.sum_bijective _ (Finite.injective_iff_bijective.1 hV1) _ _ (fun _ => rfl)
    rw [← this]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [par]
  have e1 := localLemma (σ 1) (σ 5) (σ 9) (σ 0) (σ 4) (σ 8)
    ⟨hI _ _ (by decide), hI _ _ (by decide), hI _ _ (by decide),
     hI _ _ (by decide), hI _ _ (by decide), hI _ _ (by decide),
     hII _ _ (by decide), hII _ _ (by decide), hII _ _ (by decide),
     hII _ _ (by decide), hII _ _ (by decide), hII _ _ (by decide),
     hII _ _ (by decide), hII _ _ (by decide), hII _ _ (by decide)⟩
  have e2 := localLemma (σ 2) (σ 6) (σ 10) (σ 1) (σ 5) (σ 9)
    ⟨hI _ _ (by decide), hI _ _ (by decide), hI _ _ (by decide),
     hI _ _ (by decide), hI _ _ (by decide), hI _ _ (by decide),
     hII _ _ (by decide), hII _ _ (by decide), hII _ _ (by decide),
     hII _ _ (by decide), hII _ _ (by decide), hII _ _ (by decide),
     hII _ _ (by decide), hII _ _ (by decide), hII _ _ (by decide)⟩
  have e3 := localLemma (σ 3) (σ 7) (σ 11) (σ 2) (σ 6) (σ 10)
    ⟨hI _ _ (by decide), hI _ _ (by decide), hI _ _ (by decide),
     hI _ _ (by decide), hI _ _ (by decide), hI _ _ (by decide),
     hII _ _ (by decide), hII _ _ (by decide), hII _ _ (by decide),
     hII _ _ (by decide), hII _ _ (by decide), hII _ _ (by decide),
     hII _ _ (by decide), hII _ _ (by decide), hII _ _ (by decide)⟩
  rw [sum12] at hsum
  omega


def Aplus : Finset (ZMod 60 × ZMod 12) := Alist.toFinset

lemma Aplus_card : Aplus.card = 60 := by
  rw [Aplus, List.toFinset_card_of_nodup (by decide +kernel)]
  rfl

def Fplus : Set (ℤ × ℤ) :=
  {z | 0 ≤ z.1 ∧ z.1 < 97 * 60 ∧ 0 ≤ z.2 ∧ z.2 < 97 * 12 ∧
    (((z.1 : ZMod 60)), ((z.2 : ZMod 12))) ∈ Aplus}

def H2 : Prop := ¬ ∃ B : Set (ZMod 60 × ZMod 12), TilesWith (Aplus : Set (ZMod 60 × ZMod 12)) B

def H3 : Prop := ∀ (n₁ n₂ k : ℕ) (A : Finset (ZMod n₁ × ZMod n₂)), 0 < n₁ → 0 < n₂ → 3 ≤ k →
    8 * n₁ * n₂ < A.card * k →
    (∃ B : Set (ℤ × ℤ), TilesWith {z : ℤ × ℤ | 0 ≤ z.1 ∧ z.1 < (k : ℤ) * n₁ ∧ 0 ≤ z.2 ∧
      z.2 < (k : ℤ) * n₂ ∧ (((z.1 : ZMod n₁)), ((z.2 : ZMod n₂))) ∈ A} B) →
    ∃ B : Set (ZMod n₁ × ZMod n₂), TilesWith (A : Set (ZMod n₁ × ZMod n₂)) B

def proj (n₁ n₂ : ℕ) (z : ℤ × ℤ) : ZMod n₁ × ZMod n₂ := ((z.1 : ZMod n₁), (z.2 : ZMod n₂))

noncomputable def box (a₁ b₁ a₂ b₂ : ℤ) : Finset (ℤ × ℤ) := Finset.Ico a₁ b₁ ×ˢ Finset.Ico a₂ b₂

lemma card_box (a₁ b₁ a₂ b₂ : ℤ) : (box a₁ b₁ a₂ b₂).card = (b₁ - a₁).toNat * (b₂ - a₂).toNat := by
  simp [box, Finset.card_product, Int.card_Ico]

noncomputable def Ffin (n₁ n₂ k : ℕ) (A : Finset (ZMod n₁ × ZMod n₂)) : Finset (ℤ × ℤ) :=
  (box 0 ((k : ℤ) * n₁) 0 ((k : ℤ) * n₂)).filter (fun z => proj n₁ n₂ z ∈ A)

lemma card_Ffin (n₁ n₂ k : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) (A : Finset (ZMod n₁ × ZMod n₂)) :
    A.card * k * k ≤ (Ffin n₁ n₂ k A).card := by
  haveI : NeZero n₁ := ⟨by omega⟩
  haveI : NeZero n₂ := ⟨by omega⟩
  have hc : (A ×ˢ (Finset.range k ×ˢ Finset.range k)).card = A.card * k * k := by
    simp [Finset.card_product, mul_assoc]
  rw [← hc]
  apply Finset.card_le_card_of_injOn
    (fun p => (((p.1.1.val + n₁ * p.2.1 : ℕ) : ℤ), ((p.1.2.val + n₂ * p.2.2 : ℕ) : ℤ)))
  · rintro ⟨a, i, j⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp
    obtain ⟨ha, hi, hj⟩ := hp
    have v1 := ZMod.val_lt a.1
    have v2 := ZMod.val_lt a.2
    have m1 : n₁ * i + n₁ ≤ k * n₁ := by nlinarith
    have m2 : n₂ * j + n₂ ≤ k * n₂ := by nlinarith
    have hp : proj n₁ n₂ (((a.1.val + n₁ * i : ℕ) : ℤ), ((a.2.val + n₂ * j : ℕ) : ℤ)) = a := by
      simp [proj, Prod.ext_iff]
    simp only [Ffin, box, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
      Finset.mem_Ico]
    refine ⟨⟨⟨by positivity, by push_cast; exact_mod_cast (by omega : a.1.val + n₁ * i < k * n₁)⟩,
      ⟨by positivity, by push_cast; exact_mod_cast (by omega : a.2.val + n₂ * j < k * n₂)⟩⟩, ?_⟩
    rw [hp]
    exact ha
  · rintro ⟨a, i, j⟩ hp ⟨a', i', j'⟩ hp' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp hp'
    simp only [Prod.mk.injEq, Nat.cast_inj] at heq
    obtain ⟨e1, e2⟩ := heq
    have v1 := ZMod.val_lt a.1
    have v2 := ZMod.val_lt a.2
    have v1' := ZMod.val_lt a'.1
    have v2' := ZMod.val_lt a'.2
    have d1 : a.1.val = a'.1.val ∧ i = i' := by
      have hm : (a.1.val + n₁ * i) % n₁ = (a'.1.val + n₁ * i') % n₁ := by rw [e1]
      have hd : (a.1.val + n₁ * i) / n₁ = (a'.1.val + n₁ * i') / n₁ := by rw [e1]
      rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v1,
        Nat.mod_eq_of_lt v1'] at hm
      rw [Nat.add_mul_div_left _ _ h₁, Nat.add_mul_div_left _ _ h₁, Nat.div_eq_of_lt v1,
        Nat.div_eq_of_lt v1', zero_add, zero_add] at hd
      exact ⟨hm, hd⟩
    have d2 : a.2.val = a'.2.val ∧ j = j' := by
      have hm : (a.2.val + n₂ * j) % n₂ = (a'.2.val + n₂ * j') % n₂ := by rw [e2]
      have hd : (a.2.val + n₂ * j) / n₂ = (a'.2.val + n₂ * j') / n₂ := by rw [e2]
      rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v2,
        Nat.mod_eq_of_lt v2'] at hm
      rw [Nat.add_mul_div_left _ _ h₂, Nat.add_mul_div_left _ _ h₂, Nat.div_eq_of_lt v2,
        Nat.div_eq_of_lt v2', zero_add, zero_add] at hd
      exact ⟨hm, hd⟩
    have ea : a = a' := Prod.ext (ZMod.val_injective _ d1.1) (ZMod.val_injective _ d2.1)
    rw [ea, d1.2, d2.2]


lemma mem_box {a₁ b₁ a₂ b₂ : ℤ} {z : ℤ × ℤ} :
    z ∈ box a₁ b₁ a₂ b₂ ↔ a₁ ≤ z.1 ∧ z.1 < b₁ ∧ a₂ ≤ z.2 ∧ z.2 < b₂ := by
  simp [box, Finset.mem_product, and_assoc]

/-- Final arithmetic. -/
lemma arith (Q R c M : ℤ) (hQ1 : 1 ≤ Q) (hR : Q + 1 ≤ R) (hc : 0 ≤ c) (hM : M = 3 * Q * c + 1)
    (h : M * M * R ≤ Q * ((M + c) * (M + c))) : False := by
  have hQ : 0 ≤ Q := by omega
  have hM0 : 0 < M := by subst hM; positivity
  have h1 : M * M ≤ 2 * Q * M * c + Q * c * c := by nlinarith
  have h2 : Q * c * c ≤ Q * M * c := by
    have : c ≤ M := by subst hM; nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ 3*Q - 1) hc]
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hQ hc)
    nlinarith
  have h3 : 3 * Q * c * M < M * M := by
    have : 3 * Q * c < M := by omega
    nlinarith
  nlinarith


def liftSet (n₁ n₂ k : ℕ) (A : Finset (ZMod n₁ × ZMod n₂)) : Set (ℤ × ℤ) :=
  {z : ℤ × ℤ | 0 ≤ z.1 ∧ z.1 < (k : ℤ) * n₁ ∧ 0 ≤ z.2 ∧
      z.2 < (k : ℤ) * n₂ ∧ (((z.1 : ZMod n₁)), ((z.2 : ZMod n₂))) ∈ A}

def cell (n₁ n₂ : ℕ) (x : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {p | x.1 ≤ p.1 ∧ p.1 < x.1 + n₁ ∧ x.2 ≤ p.2 ∧ p.2 < x.2 + n₂}

lemma mem_Ffin (n₁ n₂ k : ℕ) (A : Finset (ZMod n₁ × ZMod n₂)) (z : ℤ × ℤ) :
    z ∈ Ffin n₁ n₂ k A ↔ z ∈ liftSet n₁ n₂ k A := by
  rw [Ffin, Finset.mem_filter, mem_box]
  simp only [liftSet, Set.mem_setOf_eq, proj]
  tauto

set_option maxHeartbeats 2000000 in
theorem exists_good (n₁ n₂ k : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) (hk : 3 ≤ k)
    (A : Finset (ZMod n₁ × ZMod n₂)) (hα : 8 * n₁ * n₂ < A.card * k)
    (B : Set (ℤ × ℤ)) (hB : TilesWith (liftSet n₁ n₂ k A) B) :
    ∃ x : ℤ × ℤ, ∀ σ ∈ B, ∀ f ∈ liftSet n₁ n₂ k A, f + σ ∈ cell n₁ n₂ x →
      ∀ p ∈ cell n₁ n₂ x, 0 ≤ (p - σ).1 ∧ (p - σ).1 < (k : ℤ) * n₁ ∧
        0 ≤ (p - σ).2 ∧ (p - σ).2 < (k : ℤ) * n₂ := by
  classical
  by_contra hcon
  push_neg at hcon
  have hFc := card_Ffin n₁ n₂ k h₁ h₂ A
  set Ff := Ffin n₁ n₂ k A with hFf
  set F := liftSet n₁ n₂ k A with hF
  set N₁ : ℤ := (n₁ : ℤ) with hN₁
  set N₂ : ℤ := (n₂ : ℤ) with hN₂
  set K : ℤ := (k : ℤ) with hK
  set P₁ : ℤ := K * N₁ with hP₁
  set P₂ : ℤ := K * N₂ with hP₂
  have hN₁p : 1 ≤ N₁ := by omega
  have hN₂p : 1 ≤ N₂ := by omega
  have hK3 : 3 ≤ K := by omega
  have hP₁b : 3 * N₁ ≤ P₁ := by rw [hP₁]; nlinarith
  have hP₂b : 3 * N₂ ≤ P₂ := by rw [hP₂]; nlinarith
  set Q : ℤ := (6 * K + 3) * N₁ * N₂ with hQ
  set R : ℤ := (A.card : ℤ) * K * K with hR
  set c : ℤ := 2 * N₁ + 2 * P₁ + 2 * N₂ + 2 * P₂ with hc
  set M : ℤ := 3 * Q * c + 1 with hM
  have hPe₁ : (k : ℤ) * (n₁ : ℤ) = P₁ := rfl
  have hPe₂ : (k : ℤ) * (n₂ : ℤ) = P₂ := rfl
  have hNe₁ : (n₁ : ℤ) = N₁ := rfl
  have hNe₂ : (n₂ : ℤ) = N₂ := rfl
  clear_value M c R Q P₁ P₂ K N₁ N₂
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hRQ : Q + 1 ≤ R := by
    have h8 : 8 * N₁ * N₂ + 1 ≤ (A.card : ℤ) * K := by
      rw [hN₁, hN₂, hK]; exact_mod_cast hα
    rw [hQ, hR]
    nlinarith
  have hc0 : 0 ≤ c := by omega
  have hM0 : 0 ≤ M := by rw [hM]; nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ Q) hc0]
  -- the ring of bad offsets
  set Outer := box (-N₁) (P₁ + N₁) (-N₂) (P₂ + N₂) with hOuter
  set Inner := box 0 (P₁ - N₁ + 1) 0 (P₂ - N₂ + 1) with hInner
  have hIO : Inner ⊆ Outer := by
    intro z hz
    rw [mem_box] at hz ⊢
    omega
  set Ring := Outer \ Inner with hRing
  have geo : ∀ x, ∃ σ ∈ B, x - σ ∈ Ring := by
    intro x
    obtain ⟨σ, hσ, f, hf, hfc, p, hp, hbad⟩ := hcon x
    refine ⟨σ, hσ, ?_⟩
    obtain ⟨f1, f2, f3, f4, -⟩ := hf
    simp only [cell, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at hfc hp
    rw [Finset.mem_sdiff, mem_box, mem_box]
    simp only [Prod.fst_sub, Prod.snd_sub] at hbad ⊢
    constructor
    · omega
    · intro hin
      have := hbad (by omega) (by omega) (by omega)
      omega
  choose sel hselB hsel using geo
  set W := box 0 M 0 M with hW
  set S := (box (-P₁ - N₁) (M + N₁) (-P₂ - N₂) (M + N₂)).filter (· ∈ B) with hS
  have hselS : ∀ x ∈ W, sel x ∈ S := by
    intro x hx
    have h1 := hsel x
    rw [Finset.mem_sdiff, mem_box] at h1
    rw [mem_box] at hx
    rw [hS, Finset.mem_filter, mem_box]
    simp only [Prod.fst_sub, Prod.snd_sub] at h1
    refine ⟨by omega, hselB x⟩
  -- covering bound
  have hcov : W.card ≤ S.card * Ring.card := by
    have hsub : W ⊆ S.biUnion (fun σ => Ring.image (· + σ)) := by
      intro x hx
      rw [Finset.mem_biUnion]
      refine ⟨sel x, hselS x hx, Finset.mem_image.2 ⟨x - sel x, hsel x, by abel⟩⟩
    calc W.card ≤ (S.biUnion (fun σ => Ring.image (· + σ))).card := Finset.card_le_card hsub
      _ ≤ S.card * Ring.card := Finset.card_biUnion_le_card_mul _ _ _
          (fun σ _ => Finset.card_image_le)
  -- packing bound
  have hpack : S.card * Ff.card ≤ (box (-P₁ - N₁) (M + N₁ + P₁) (-P₂ - N₂) (M + N₂ + P₂)).card := by
    have hdisj : (S : Set (ℤ × ℤ)).PairwiseDisjoint (fun σ => Ff.image (· + σ)) := by
      intro σ hσ σ' hσ' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨f', hf', heq⟩ := Finset.mem_image.1 hy'
      rw [mem_Ffin] at hf hf'
      have hσB : σ ∈ B := (Finset.mem_filter.1 hσ).2
      have hσB' : σ' ∈ B := (Finset.mem_filter.1 hσ').2
      obtain ⟨p, -, hp⟩ := hB (f + σ)
      have e1 := hp (f, σ) ⟨hf, hσB, rfl⟩
      have e2 := hp (f', σ') ⟨hf', hσB', heq⟩
      exact hne (Prod.ext_iff.1 (e2.trans e1.symm)).2.symm
    have hsub : S.biUnion (fun σ => Ff.image (· + σ)) ⊆
        box (-P₁ - N₁) (M + N₁ + P₁) (-P₂ - N₂) (M + N₂ + P₂) := by
      intro y hy
      obtain ⟨σ, hσ, hy⟩ := Finset.mem_biUnion.1 hy
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hy
      rw [mem_Ffin] at hf
      obtain ⟨f1, f2, f3, f4, -⟩ := hf
      have := (Finset.mem_filter.1 hσ).1
      rw [mem_box] at this ⊢
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    calc S.card * Ff.card = ∑ σ ∈ S, (Ff.image (· + σ)).card := by
          rw [Finset.sum_congr rfl (fun σ _ => Finset.card_image_of_injective _ (add_left_injective σ))]
          simp
      _ = (S.biUnion (fun σ => Ff.image (· + σ))).card := (Finset.card_biUnion hdisj).symm
      _ ≤ _ := Finset.card_le_card hsub
  -- cards as integers
  have cW : (W.card : ℤ) = M * M := by
    rw [hW, card_box]; push_cast; rw [Int.toNat_of_nonneg (by omega)]; ring
  have cR : (Ring.card : ℤ) + ((P₁ - N₁ + 1) * (P₂ - N₂ + 1)) = (P₁ + 2 * N₁) * (P₂ + 2 * N₂) := by
    have := Finset.card_sdiff_add_card_eq_card hIO
    rw [← hRing, hInner, hOuter, card_box, card_box] at this
    have := congrArg (fun n : ℕ => (n : ℤ)) this
    push_cast at this
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
      Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)] at this
    linear_combination this
  have cT : ((box (-P₁ - N₁) (M + N₁ + P₁) (-P₂ - N₂) (M + N₂ + P₂)).card : ℤ) =
      (M + 2 * N₁ + 2 * P₁) * (M + 2 * N₂ + 2 * P₂) := by
    rw [card_box]; push_cast
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]; ring
  have hcovZ : M * M ≤ (S.card : ℤ) * Ring.card := by rw [← cW]; exact_mod_cast hcov
  have hpackZ : (S.card : ℤ) * R ≤ (M + 2 * N₁ + 2 * P₁) * (M + 2 * N₂ + 2 * P₂) := by
    rw [← cT]
    have : (S.card : ℤ) * (A.card * k * k : ℕ) ≤ (S.card : ℤ) * Ff.card := by
      exact_mod_cast Nat.mul_le_mul_left _ hFc
    have h2 : ((S.card * Ff.card : ℕ) : ℤ) ≤
        ((box (-P₁ - N₁) (M + N₁ + P₁) (-P₂ - N₂) (M + N₂ + P₂)).card : ℤ) := by
      exact_mod_cast hpack
    push_cast at this h2
    rw [hR, hK]
    linarith
  have hRingQ : (Ring.card : ℤ) ≤ Q := by
    rw [hQ]
    have : (Ring.card : ℤ) = (P₁ + 2 * N₁) * (P₂ + 2 * N₂) - (P₁ - N₁ + 1) * (P₂ - N₂ + 1) := by
      linarith
    rw [this, hP₁, hP₂]
    nlinarith
  have hS0 : (0 : ℤ) ≤ S.card := by positivity
  have hR0 : (0 : ℤ) ≤ R := by omega
  apply arith Q R c M hQ1 hRQ hc0 hM
  have h1 : M * M * R ≤ (S.card : ℤ) * Q * R := by
    have := mul_le_mul_of_nonneg_right hcovZ hR0
    have h2 : (S.card : ℤ) * Ring.card * R ≤ S.card * Q * R := by
      apply mul_le_mul_of_nonneg_right _ hR0
      exact mul_le_mul_of_nonneg_left hRingQ hS0
    linarith
  have h2 : (S.card : ℤ) * Q * R ≤ Q * ((M + c) * (M + c)) := by
    have : (M + 2 * N₁ + 2 * P₁) * (M + 2 * N₂ + 2 * P₂) ≤ (M + c) * (M + c) := by
      apply mul_le_mul <;> omega
    have hQ0 : (0 : ℤ) ≤ Q := by omega
    nlinarith
  linarith



lemma proj_add (n₁ n₂ : ℕ) (z w : ℤ × ℤ) : proj n₁ n₂ (z + w) = proj n₁ n₂ z + proj n₁ n₂ w := by
  simp [proj]

lemma proj_sub (n₁ n₂ : ℕ) (z w : ℤ × ℤ) : proj n₁ n₂ (z - w) = proj n₁ n₂ z - proj n₁ n₂ w := by
  simp [proj]

/-- Every residue class has a representative in the cell at x. -/
lemma exists_rep (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) (x : ℤ × ℤ) (g : ZMod n₁ × ZMod n₂) :
    ∃ z ∈ cell n₁ n₂ x, proj n₁ n₂ z = g := by
  haveI : NeZero n₁ := ⟨by omega⟩
  haveI : NeZero n₂ := ⟨by omega⟩
  refine ⟨(x.1 + ((g.1.val : ℤ) - x.1) % n₁, x.2 + ((g.2.val : ℤ) - x.2) % n₂), ?_, ?_⟩
  · have a1 := Int.emod_nonneg ((g.1.val : ℤ) - x.1) (by omega : (n₁ : ℤ) ≠ 0)
    have a2 := Int.emod_lt_of_pos ((g.1.val : ℤ) - x.1) (by omega : (0 : ℤ) < n₁)
    have b1 := Int.emod_nonneg ((g.2.val : ℤ) - x.2) (by omega : (n₂ : ℤ) ≠ 0)
    have b2 := Int.emod_lt_of_pos ((g.2.val : ℤ) - x.2) (by omega : (0 : ℤ) < n₂)
    simp only [cell, Set.mem_setOf_eq]
    omega
  · ext
    · simp only [proj]
      push_cast
      rw [add_sub_cancel]
      simp
    · simp only [proj]
      push_cast
      rw [add_sub_cancel]
      simp

/-- Matolcsi, second half: a good window gives a tiling of the finite group. -/
theorem tiling_of_good (n₁ n₂ k : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (A : Finset (ZMod n₁ × ZMod n₂)) (B : Set (ℤ × ℤ))
    (hB : TilesWith (liftSet n₁ n₂ k A) B) (x : ℤ × ℤ)
    (hgood : ∀ σ ∈ B, ∀ f ∈ liftSet n₁ n₂ k A, f + σ ∈ cell n₁ n₂ x →
      ∀ p ∈ cell n₁ n₂ x, 0 ≤ (p - σ).1 ∧ (p - σ).1 < (k : ℤ) * n₁ ∧
        0 ≤ (p - σ).2 ∧ (p - σ).2 < (k : ℤ) * n₂) :
    ∃ B' : Set (ZMod n₁ × ZMod n₂), TilesWith (A : Set (ZMod n₁ × ZMod n₂)) B' := by
  set F := liftSet n₁ n₂ k A
  set I : Set (ℤ × ℤ) := {σ | σ ∈ B ∧ ∃ f ∈ F, f + σ ∈ cell n₁ n₂ x}
  refine ⟨proj n₁ n₂ '' I, ?_⟩
  -- key: for z in the cell and σ ∈ I, z - σ ∈ F iff its projection is in A
  have key : ∀ σ ∈ I, ∀ z ∈ cell n₁ n₂ x, proj n₁ n₂ (z - σ) ∈ A → z - σ ∈ F := by
    rintro σ ⟨hσB, f, hf, hfc⟩ z hz hA
    obtain ⟨c1, c2, c3, c4⟩ := hgood σ hσB f hf hfc z hz
    exact ⟨c1, c2, c3, c4, hA⟩
  intro g
  obtain ⟨z, hz, hzg⟩ := exists_rep n₁ n₂ h₁ h₂ x g
  obtain ⟨⟨f, σ⟩, ⟨hf, hσ, hfσ⟩, huniq⟩ := hB z
  simp only at hf hσ hfσ
  have hσI : σ ∈ I := ⟨hσ, f, hf, hfσ ▸ hz⟩
  refine ⟨(proj n₁ n₂ f, proj n₁ n₂ σ), ⟨hf.2.2.2.2, ⟨σ, hσI, rfl⟩, ?_⟩, ?_⟩
  · simp only
    rw [← proj_add, hfσ, hzg]
  · rintro ⟨a, β⟩ ⟨ha, ⟨σ', hσ'I, rfl⟩, hsum⟩
    simp only at ha hsum
    have hA : proj n₁ n₂ (z - σ') ∈ A := by
      rw [proj_sub, hzg, ← hsum]
      simpa using ha
    have hzF := key σ' hσ'I z hz hA
    have e := huniq (z - σ', σ') ⟨hzF, hσ'I.1, by simp⟩
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    subst e2
    refine Prod.ext ?_ rfl
    show a = proj n₁ n₂ f
    rw [← e1, proj_sub, hzg, ← hsum]
    simp


theorem H3_holds : H3 := by
  intro n₁ n₂ k A h₁ h₂ hk hα hT
  obtain ⟨B, hB⟩ := hT
  obtain ⟨x, hx⟩ := exists_good n₁ n₂ k h₁ h₂ hk A hα B hB
  exact tiling_of_good n₁ n₂ k h₁ h₂ A B hB x hx

theorem H2_holds : H2 := by
  have e : ((Aplus : Finset (ZMod 60 × ZMod 12)) : Set (ZMod 60 × ZMod 12)) = {p | p ∈ Alist} := by
    ext p; simp [Aplus]
  unfold H2; rw [e]; exact H2_proof

/-- General analytic transference (KM06 Thm 4.2, forward direction). -/
def H1a : Prop := ∀ (F : Finset (ℤ × ℤ)) (Λ₀ : Finset (Fin 2 → ℝ)), F.Nonempty →
    Λ₀.card = F.card →
    (∀ μ ∈ Λ₀, ∀ μ' ∈ Λ₀, μ ≠ μ' →
      ∑ f ∈ F, exponentialCharacter (μ - μ') ![(f.1 : ℝ), (f.2 : ℝ)] = 0) →
    isSpectral (boxSet (F : Set (ℤ × ℤ)))

/-- Concrete finite exponential-sum orthogonality for A_+[97]. -/
def H1b : Prop := ∃ Λ₀ : Finset (Fin 2 → ℝ), Λ₀.card = (Ffin 60 12 97 Aplus).card ∧
    ∀ μ ∈ Λ₀, ∀ μ' ∈ Λ₀, μ ≠ μ' →
      ∑ f ∈ Ffin 60 12 97 Aplus, exponentialCharacter (μ - μ') ![(f.1 : ℝ), (f.2 : ℝ)] = 0

lemma Fplus_eq : Fplus = ((Ffin 60 12 97 Aplus : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
  ext z
  rw [Finset.mem_coe, mem_Ffin]
  simp only [Fplus, liftSet, Set.mem_setOf_eq]
  norm_num

open Real



def Inv (L : List G) (M : G → ZMod 60) (g : ZMod 60) : Prop :=
  ∀ m : ZMod 60, L.countP (fun a => decide (M a = m)) = L.countP (fun a => decide (M a = m + g))

noncomputable def ζ : ℂ := Complex.exp (2 * π * Complex.I / 60)

noncomputable def χ (m : ZMod 60) : ℂ := ζ ^ m.val

lemma ζ_prim : IsPrimitiveRoot ζ 60 := Complex.isPrimitiveRoot_exp 60 (by norm_num)

lemma ζ_pow_mod (n : ℕ) : ζ ^ n = ζ ^ (n % 60) := by
  conv_lhs => rw [← Nat.div_add_mod n 60, pow_add, pow_mul, ζ_prim.pow_eq_one, one_pow, one_mul]

lemma χ_add (m g : ZMod 60) : χ (m + g) = χ m * χ g := by
  simp only [χ]
  rw [ZMod.val_add, ← ζ_pow_mod, pow_add]

lemma χ_ne_one (g : ZMod 60) (hg : g ≠ 0) : χ g ≠ 1 := by
  intro h
  have := (ζ_prim.pow_eq_one_iff_dvd g.val).1 h
  have hlt := ZMod.val_lt g
  have hpos : 0 < g.val := by
    rcases Nat.eq_zero_or_pos g.val with h0 | h0
    · exact absurd ((ZMod.val_eq_zero g).1 h0) hg
    · exact h0
  obtain ⟨c, hc⟩ := this
  rcases c with _ | c
  · omega
  · nlinarith

lemma χ_int (k : ℤ) : Complex.exp (2 * π * Complex.I * ((k : ℂ) / 60)) = χ (k : ZMod 60) := by
  have h1 : 2 * π * Complex.I * ((k : ℂ) / 60) = (k : ℂ) * (2 * π * Complex.I / 60) := by ring
  rw [h1, Complex.exp_int_mul]
  change ζ ^ k = χ (k : ZMod 60)
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hk : k = 60 * (k / 60) + k % 60 := (Int.mul_ediv_add_emod k 60).symm
  have hnn : 0 ≤ k % 60 := Int.emod_nonneg k (by norm_num)
  rw [hk, zpow_add₀ hζ0, zpow_mul]
  have : ζ ^ (60 : ℤ) = 1 := by
    rw [show (60 : ℤ) = ((60 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact ζ_prim.pow_eq_one
  rw [this, one_zpow, one_mul]
  simp only [χ]
  have hv : (((k : ZMod 60).val : ℕ) : ℤ) = k % 60 := ZMod.val_intCast k
  rw [← hk, ← hv, zpow_natCast]

lemma sum_fiber (L : List G) (M : G → ZMod 60) (h : ZMod 60 → ℂ) :
    (L.map (fun a => h (M a))).sum = ∑ m : ZMod 60, (L.countP (fun a => decide (M a = m)) : ℂ) * h m := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.countP_cons]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    simp [Finset.sum_ite_eq]

lemma vanish (L : List G) (M : G → ZMod 60) (g : ZMod 60) (hg : g ≠ 0) (hI : Inv L M g) :
    (L.map (fun a => χ (M a))).sum = 0 := by
  rw [sum_fiber]
  set S := ∑ m : ZMod 60, (L.countP (fun a => decide (M a = m)) : ℂ) * χ m with hS
  have key : S = S * χ g := by
    have : S = ∑ m : ZMod 60, (L.countP (fun a => decide (M a = m + g)) : ℂ) * χ (m + g) := by
      rw [hS]
      exact (Fintype.sum_equiv (Equiv.addRight g) _ _ (fun m => rfl)).symm
    calc S = _ := this
      _ = ∑ m : ZMod 60, (L.countP (fun a => decide (M a = m)) : ℂ) * χ m * χ g := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [← hI m, χ_add]
          ring
      _ = S * χ g := by rw [hS, Finset.sum_mul]
  have h1 : S * (1 - χ g) = 0 := by rw [mul_sub, mul_one, ← key, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exact h
  · exact absurd (sub_eq_zero.1 h).symm (χ_ne_one g hg)

lemma emb_int (z : ℤ) : (((5 * z : ℤ)) : ZMod 60) = emb (z : ZMod 12) := by
  have hv : (((z : ZMod 12).val : ℕ) : ℤ) = z % 12 := ZMod.val_intCast z
  have hz : z = 12 * (z / 12) + z % 12 := (Int.mul_ediv_add_emod z 12).symm
  simp only [emb]
  have : ((((z : ZMod 12).val : ℕ) : ZMod 60)) = (((z % 12 : ℤ)) : ZMod 60) := by
    rw [← hv]; push_cast; rfl
  rw [this]
  conv_lhs => rw [hz]
  push_cast
  have h60 : ((60 : ℤ) : ZMod 60) = 0 := by decide
  have : (5 : ZMod 60) * (12 * ((z / 12 : ℤ) : ZMod 60) + ((z % 12 : ℤ) : ZMod 60)) =
      ((60 : ℤ) : ZMod 60) * ((z / 12 : ℤ) : ZMod 60) + 5 * ((z % 12 : ℤ) : ZMod 60) := by
    push_cast; ring
  rw [this, h60, zero_mul, zero_add]

/-- Geometric sums of 97th roots of unity. -/
lemma geom97 (n : ℤ) (s s' : ℕ) (hs : s < 97) (hs' : s' < 97) (hne : s ≠ s') :
    ∑ i ∈ Finset.range 97,
      Complex.exp (2 * π * Complex.I * ((n : ℂ) + ((s : ℂ) - s') / 97)) ^ i = 0 := by
  set Y := Complex.exp (2 * π * Complex.I * ((n : ℂ) + ((s : ℂ) - s') / 97)) with hY
  have hY97 : Y ^ 97 = 1 := by
    rw [hY, ← Complex.exp_nat_mul]
    have : ((97 : ℕ) : ℂ) * (2 * π * Complex.I * ((n : ℂ) + ((s : ℂ) - s') / 97)) =
        ((97 * n + s - s' : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hY1 : Y ≠ 1 := by
    intro h
    rw [hY, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have h2 : (2 * π * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : ((n : ℂ) + ((s : ℂ) - s') / 97) = (m : ℂ) := by
      have := hm
      rw [mul_comm (m : ℂ)] at this
      exact mul_left_cancel₀ h2 this
    have h4 : ((s : ℤ) - s' : ℂ) = ((97 * (m - n) : ℤ) : ℂ) := by
      push_cast
      linear_combination 97 * h3
    have h5 : (s : ℤ) - s' = 97 * (m - n) := by exact_mod_cast h4
    omega
  rw [geom_sum_eq hY1, hY97, sub_self, zero_div]




def Lamlist : List G := [(0, 0), (12, 0), (24, 0), (36, 0), (48, 0), (25, 1), (37, 1), (49, 1), (1, 1), (13, 1), (0, 2), (12, 2), (24, 2), (36, 2), (48, 2), (35, 3), (47, 3), (59, 3), (11, 3), (23, 3), (45, 4), (57, 4), (9, 4), (21, 4), (33, 4), (10, 5), (22, 5), (34, 5), (46, 5), (58, 5), (50, 6), (2, 6), (14, 6), (26, 6), (38, 6), (20, 7), (32, 7), (44, 7), (56, 7), (8, 7), (35, 8), (47, 8), (59, 8), (11, 8), (23, 8), (40, 9), (52, 9), (4, 9), (16, 9), (28, 9), (50, 10), (2, 10), (14, 10), (26, 10), (38, 10), (50, 11), (2, 11), (14, 11), (26, 11), (38, 11)]

def fz : List (ZMod 12) := [0, 5, 0, 7, 9, 2, 10, 4, 7, 8, 10, 10]

def Lay0 : List G := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11)]
def Lay1 : List G := [(36, 0), (36, 1), (36, 2), (36, 3), (36, 4), (36, 5), (36, 6), (36, 7), (36, 8), (36, 9), (36, 10), (36, 11)]
def Lay2 : List G := [(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11)]
def Lay3 : List G := [(8, 4), (8, 10), (13, 2), (13, 8), (28, 2), (28, 8), (33, 0), (33, 6), (48, 0), (48, 6), (53, 4), (53, 10)]
def Lay4 : List G := [(4, 4), (9, 9), (14, 2), (19, 7), (24, 0), (29, 5), (34, 10), (39, 3), (44, 8), (49, 1), (54, 6), (59, 11)]

instance (L : List G) (M : G → ZMod 60) (g : ZMod 60) : Decidable (Inv L M g) := by
  unfold Inv; infer_instance

def fv (y : ZMod 12) : ZMod 12 := fz.getD y.val 0

lemma lam_param : ∀ l ∈ Lamlist, ∃ y : ZMod 12, ∃ r : ZMod 60,
    (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) ∧ l = (emb (fv y) + 12 * r, y) := by
  decide +kernel

lemma perm_layers : Alist.Perm (Lay0 ++ Lay1 ++ Lay2 ++ Lay3 ++ Lay4) := by decide +kernel

lemma lay_t : (∀ a ∈ Lay0, 12 * a.1 = 12 * 0) ∧ (∀ a ∈ Lay1, 12 * a.1 = 12 * 1) ∧
    (∀ a ∈ Lay2, 12 * a.1 = 12 * 2) ∧ (∀ a ∈ Lay3, 12 * a.1 = 12 * 3) ∧
    (∀ a ∈ Lay4, 12 * a.1 = 12 * 4) := by decide +kernel

lemma rcase : ∀ r r' : ZMod 60, (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) →
    (r' = 0 ∨ r' = 1 ∨ r' = 2 ∨ r' = 3 ∨ r' = 4) → r ≠ r' →
    Inv Alist (fun a => 12 * (r - r') * a.1) 12 := by decide +kernel

lemma ycase0 : ∀ y y' : ZMod 12, y ≠ y' → ∃ g : ZMod 60, (g = 30 ∨ g = 20 ∨ g = 40) ∧
    Inv Lay0 (fun a => emb (fv y - fv y') * a.1 + emb ((y - y') * a.2)) g := by decide +kernel


lemma ycase1 : ∀ y y' : ZMod 12, y ≠ y' → ∃ g : ZMod 60, (g = 30 ∨ g = 20 ∨ g = 40) ∧
    Inv Lay1 (fun a => emb (fv y - fv y') * a.1 + emb ((y - y') * a.2)) g := by decide +kernel

lemma ycase2 : ∀ y y' : ZMod 12, y ≠ y' → ∃ g : ZMod 60, (g = 30 ∨ g = 20 ∨ g = 40) ∧
    Inv Lay2 (fun a => emb (fv y - fv y') * a.1 + emb ((y - y') * a.2)) g := by decide +kernel

lemma ycase3 : ∀ y y' : ZMod 12, y ≠ y' → ∃ g : ZMod 60, (g = 30 ∨ g = 20 ∨ g = 40) ∧
    Inv Lay3 (fun a => emb (fv y - fv y') * a.1 + emb ((y - y') * a.2)) g := by decide +kernel

lemma ycase4 : ∀ y y' : ZMod 12, y ≠ y' → ∃ g : ZMod 60, (g = 30 ∨ g = 20 ∨ g = 40) ∧
    Inv Lay4 (fun a => emb (fv y - fv y') * a.1 + emb ((y - y') * a.2)) g := by decide +kernel

lemma emb_sub : ∀ u v : ZMod 12, emb u - emb v = emb (u - v) := by decide +kernel

lemma emb_zero : emb 0 = 0 := by decide

lemma Lamlist_nodup : Lamlist.Nodup := by decide +kernel

lemma Alist_nodup' : Alist.Nodup := by decide +kernel

lemma layer_zero (L : List G) (c : ZMod 60) (M M' : G → ZMod 60)
    (hM : ∀ a ∈ L, M a = c + M' a) (g : ZMod 60) (hg : g ≠ 0) (hI : Inv L M' g) :
    (L.map (fun a => χ (M a))).sum = 0 := by
  rw [List.map_congr_left (fun a ha => by rw [hM a ha, χ_add])]
  rw [List.sum_map_mul_left, vanish L M' g hg hI, mul_zero]

lemma g_ne (g : ZMod 60) (hg : g = 30 ∨ g = 20 ∨ g = 40) : g ≠ 0 := by
  rcases hg with rfl | rfl | rfl <;> decide

theorem core_sum : ∀ l ∈ Lamlist, ∀ l' ∈ Lamlist, l ≠ l' →
    (Alist.map (fun a => χ ((l - l').1 * a.1 + emb ((l - l').2 * a.2)))).sum = 0 := by
  intro l hl l' hl' hne
  obtain ⟨y, r, hr, rfl⟩ := lam_param l hl
  obtain ⟨y', r', hr', rfl⟩ := lam_param l' hl'
  simp only [Prod.fst_sub, Prod.snd_sub]
  by_cases hy : y = y'
  · subst hy
    have hrr : r ≠ r' := fun h => hne (by rw [h])
    have hM : ∀ a : G, (emb (fv y) + 12 * r - (emb (fv y) + 12 * r')) * a.1 + emb ((y - y) * a.2)
        = 12 * (r - r') * a.1 := by
      intro a
      rw [sub_self, zero_mul, emb_zero]
      ring
    simp_rw [hM]
    exact vanish _ _ 12 (by decide) (rcase r r' hr hr' hrr)
  · rw [(perm_layers.map _).sum_eq]
    simp only [List.map_append, List.sum_append]
    obtain ⟨h0, h1, h2, h3, h4⟩ := lay_t
    have hlay : ∀ (L : List G) (t : ZMod 60), (∀ a ∈ L, 12 * a.1 = 12 * t) →
        (∃ g : ZMod 60, (g = 30 ∨ g = 20 ∨ g = 40) ∧
          Inv L (fun a => emb (fv y - fv y') * a.1 + emb ((y - y') * a.2)) g) →
        (L.map (fun a => χ ((emb (fv y) + 12 * r - (emb (fv y') + 12 * r')) * a.1 +
          emb ((y - y') * a.2)))).sum = 0 := by
      intro L t ht hex
      obtain ⟨g, hg, hI⟩ := hex
      refine layer_zero L (12 * (r - r') * t) _ _ (fun a ha => ?_) g (g_ne g hg) hI
      have := ht a ha
      rw [← emb_sub]
      linear_combination (r - r') * this
    rw [hlay _ _ h0 (ycase0 y y' hy), hlay _ _ h1 (ycase1 y y' hy), hlay _ _ h2 (ycase2 y y' hy),
      hlay _ _ h3 (ycase3 y y' hy), hlay _ _ h4 (ycase4 y y' hy)]
    simp


def φm (p : G × ℕ × ℕ) : ℤ × ℤ :=
  (((p.1.1.val + 60 * p.2.1 : ℕ) : ℤ), ((p.1.2.val + 12 * p.2.2 : ℕ) : ℤ))

noncomputable def ψm (p : G × ℕ × ℕ) : Fin 2 → ℝ :=
  ![((p.1.1.val : ℝ) + (p.2.1 : ℝ) / 97) / 60, ((p.1.2.val : ℝ) + (p.2.2 : ℝ) / 97) / 12]

lemma φm_inj : Function.Injective φm := by
  rintro ⟨a, i, j⟩ ⟨a', i', j'⟩ h
  simp only [φm, Prod.mk.injEq, Nat.cast_inj] at h
  obtain ⟨e1, e2⟩ := h
  have v1 := ZMod.val_lt a.1
  have v2 := ZMod.val_lt a.2
  have v1' := ZMod.val_lt a'.1
  have v2' := ZMod.val_lt a'.2
  have h1 : a.1.val = a'.1.val := by omega
  have h2 : a.2.val = a'.2.val := by omega
  have h3 : i = i' := by omega
  have h4 : j = j' := by omega
  have ea : a = a' := Prod.ext (ZMod.val_injective _ h1) (ZMod.val_injective _ h2)
  rw [ea, h3, h4]

set_option maxRecDepth 20000 in
lemma Ffin_eq : Ffin 60 12 97 Aplus =
    (Aplus ×ˢ (Finset.range 97 ×ˢ Finset.range 97)).image φm := by
  ext z
  rw [mem_Ffin, Finset.mem_image]
  constructor
  · rintro ⟨z1, z2, z3, z4, hA⟩
    refine ⟨(proj 60 12 z, (z.1 / 60).toNat, (z.2 / 12).toNat), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      refine ⟨hA, by omega, by omega⟩
    · have hv1 : (((z.1 : ZMod 60)).val : ℤ) = z.1 % 60 := ZMod.val_intCast _
      have hv2 : (((z.2 : ZMod 12)).val : ℤ) = z.2 % 12 := ZMod.val_intCast _
      simp only [φm, proj]
      ext
      · push_cast
        rw [hv1]
        omega
      · push_cast
        rw [hv2]
        omega
  · rintro ⟨⟨a, i, j⟩, hp, rfl⟩
    simp only [Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨ha, hi, hj⟩ := hp
    have v1 := ZMod.val_lt a.1
    have v2 := ZMod.val_lt a.2
    refine ⟨by simp only [φm]; positivity, ?_, by simp only [φm]; positivity, ?_, ?_⟩
    · simp only [φm]; push_cast; omega
    · simp only [φm]; push_cast; omega
    · have : proj 60 12 (φm (a, i, j)) = a := by
        simp [proj, φm, Prod.ext_iff]
        exact ⟨by simp [show (60 : ZMod 60) = 0 from by decide],
          by simp [show (12 : ZMod 12) = 0 from by decide]⟩
      have h' : proj 60 12 (φm (a, i, j)) ∈ Aplus := by rw [this]; exact ha
      exact h'

lemma sum_factor (S : Finset G) (X : G → ℂ) (Y Z : ℂ) :
    ∑ q ∈ S ×ˢ (Finset.range 97 ×ˢ Finset.range 97), X q.1 * Y ^ q.2.1 * Z ^ q.2.2 =
      (∑ a ∈ S, X a) * (∑ i ∈ Finset.range 97, Y ^ i) * (∑ j ∈ Finset.range 97, Z ^ j) := by
  calc _ = ∑ a ∈ S, ∑ i ∈ Finset.range 97, ∑ j ∈ Finset.range 97, X a * Y ^ i * Z ^ j := by
        rw [Finset.sum_product]
        exact Finset.sum_congr rfl (fun a _ => by rw [Finset.sum_product])
    _ = ∑ a ∈ S, X a * ((∑ i ∈ Finset.range 97, Y ^ i) * ∑ j ∈ Finset.range 97, Z ^ j) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

set_option maxRecDepth 20000 in
theorem H1b_holds : H1b := by
  set D := Aplus ×ˢ (Finset.range 97 ×ˢ Finset.range 97) with hD
  set DL := Lamlist.toFinset ×ˢ (Finset.range 97 ×ˢ Finset.range 97) with hDL
  have hLc : Lamlist.toFinset.card = 60 := by
    rw [List.toFinset_card_of_nodup Lamlist_nodup]; rfl
  have hψ : Set.InjOn ψm DL := by
    rintro ⟨l, s, t⟩ hp ⟨l', s', t'⟩ hp' h
    simp only [hDL, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp hp'
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [ψm, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have e0 : ((97 * l.1.val + s : ℕ) : ℝ) = ((97 * l'.1.val + s' : ℕ) : ℝ) := by
      push_cast; linear_combination 5820 * h0
    have e1 : ((97 * l.2.val + t : ℕ) : ℝ) = ((97 * l'.2.val + t' : ℕ) : ℝ) := by
      push_cast; linear_combination 1164 * h1
    have f0 := Nat.cast_injective e0
    have f1 := Nat.cast_injective e1
    have u1 : l.1.val = l'.1.val := by omega
    have u2 : l.2.val = l'.2.val := by omega
    have u3 : s = s' := by omega
    have u4 : t = t' := by omega
    have el : l = l' := Prod.ext (ZMod.val_injective _ u1) (ZMod.val_injective _ u2)
    rw [el, u3, u4]
  refine ⟨DL.image ψm, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hψ, Ffin_eq, Finset.card_image_of_injective _ φm_inj]
    simp only [hD, hDL, Finset.card_product, Finset.card_range, hLc, Aplus_card]
  · intro μ hμ μ' hμ' hne
    obtain ⟨⟨l, s, t⟩, hp, rfl⟩ := Finset.mem_image.1 hμ
    obtain ⟨⟨l', s', t'⟩, hp', rfl⟩ := Finset.mem_image.1 hμ'
    simp only [hDL, Finset.mem_product, Finset.mem_range, List.mem_toFinset] at hp hp'
    rw [Ffin_eq, Finset.sum_image (fun x _ y _ h => φm_inj h)]
    set D0 : ℝ := ((l.1.val : ℝ) + (s : ℝ) / 97) / 60 - ((l'.1.val : ℝ) + (s' : ℝ) / 97) / 60
      with hD0
    set D1 : ℝ := ((l.2.val : ℝ) + (t : ℝ) / 97) / 12 - ((l'.2.val : ℝ) + (t' : ℝ) / 97) / 12
      with hD1
    have hterm : ∀ q : G × ℕ × ℕ, exponentialCharacter (ψm (l, s, t) - ψm (l', s', t'))
        ![((φm q).1 : ℝ), ((φm q).2 : ℝ)] =
        Complex.exp (2 * π * Complex.I * ((D0 : ℂ) * (q.1.1.val : ℂ) + (D1 : ℂ) * (q.1.2.val : ℂ))) *
        Complex.exp (2 * π * Complex.I * (60 * (D0 : ℂ))) ^ q.2.1 *
        Complex.exp (2 * π * Complex.I * (12 * (D1 : ℂ))) ^ q.2.2 := by
      rintro ⟨a, i, j⟩
      simp only [exponentialCharacter, Fin.sum_univ_two, Pi.sub_apply, ψm, φm,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [hD0, hD1]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun q _ => hterm q), sum_factor Aplus
      (fun a => Complex.exp (2 * π * Complex.I * ((D0 : ℂ) * (a.1.val : ℂ) + (D1 : ℂ) * (a.2.val : ℂ))))
      (Complex.exp (2 * π * Complex.I * (60 * (D0 : ℂ))))
      (Complex.exp (2 * π * Complex.I * (12 * (D1 : ℂ))))]
    by_cases hs : s = s'
    · by_cases ht : t = t'
      · subst hs
        subst ht
        have hl : l ≠ l' := fun h => hne (by rw [h])
        have hX : ∀ a ∈ Aplus, Complex.exp (2 * π * Complex.I * ((D0 : ℂ) * (a.1.val : ℂ) +
            (D1 : ℂ) * (a.2.val : ℂ))) = χ ((l - l').1 * a.1 + emb ((l - l').2 * a.2)) := by
          intro a _
          set k : ℤ := ((l.1.val : ℤ) - l'.1.val) * a.1.val +
            5 * (((l.2.val : ℤ) - l'.2.val) * a.2.val) with hk
          have e1 : 2 * π * Complex.I * ((D0 : ℂ) * (a.1.val : ℂ) + (D1 : ℂ) * (a.2.val : ℂ)) =
              2 * π * Complex.I * ((k : ℂ) / 60) := by
            rw [hD0, hD1, hk]
            push_cast
            ring
          rw [e1, χ_int]
          congr 1
          rw [hk, Int.cast_add, emb_int]
          push_cast
          simp [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id']
        rw [Finset.sum_congr rfl hX, Aplus, List.sum_toFinset _ Alist_nodup',
          core_sum l hp.1 l' hp'.1 hl]
        ring
      · have hY : Complex.exp (2 * π * Complex.I * (12 * (D1 : ℂ))) =
            Complex.exp (2 * π * Complex.I * ((((l.2.val : ℤ) - l'.2.val : ℤ) : ℂ) +
              ((t : ℂ) - t') / 97)) := by
          congr 1; rw [hD1]; push_cast; ring
        rw [hY, geom97 _ t t' hp.2.2 hp'.2.2 ht]
        ring
    · have hY : Complex.exp (2 * π * Complex.I * (60 * (D0 : ℂ))) =
          Complex.exp (2 * π * Complex.I * ((((l.1.val : ℤ) - l'.1.val : ℤ) : ℂ) +
            ((s : ℂ) - s') / 97)) := by
        congr 1; rw [hD0]; push_cast; ring
      rw [hY, geom97 _ s s' hp.2.1 hp'.2.1 hs]
      ring


end FugledeScratch


open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace FugledeGen

variable {d : ℕ}

def boxSet (F : Set (Fin d → ℤ)) : Set (Fin d → ℝ) := {x | (fun i => ⌊x i⌋) ∈ F}

/-- General analytic transference (KM06 Thm 4.2, forward direction). -/
def H1a (d : ℕ) : Prop := ∀ (F : Finset (Fin d → ℤ)) (Λ₀ : Finset (Fin d → ℝ)), F.Nonempty →
    Λ₀.card = F.card →
    (∀ μ ∈ Λ₀, ∀ μ' ∈ Λ₀, μ ≠ μ' →
      ∑ f ∈ F, exponentialCharacter (μ - μ') (fun i => (f i : ℝ)) = 0) →
    isSpectral (boxSet (F : Set (Fin d → ℤ)))

noncomputable def zv (f : Fin d → ℤ) : Fin d → ℝ := fun i => (f i : ℝ)

noncomputable def ic (n : Fin d → ℤ) : Fin d → ℝ := fun i => (n i : ℝ)

def Sq : Set (Fin d → ℝ) := Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)

def piece (f : Fin d → ℤ) : Set (Fin d → ℝ) := {x | (fun i => ⌊x i⌋) = f}

noncomputable abbrev μT : Measure (UnitAddTorus (Fin d)) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)

noncomputable def ψ (θ : UnitAddTorus (Fin d)) : Fin d → ℝ :=
  ((UnitAddTorus.measurableEquivPiIoc (0 : Fin d → ℝ)) θ).1

lemma ec_add_right (ξ x y : Fin d → ℝ) :
    exponentialCharacter ξ (x + y) = exponentialCharacter ξ x * exponentialCharacter ξ y := by
  unfold exponentialCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

lemma ec_add_left (ξ η x : Fin d → ℝ) :
    exponentialCharacter (ξ + η) x = exponentialCharacter ξ x * exponentialCharacter η x := by
  unfold exponentialCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add]

lemma ec_conj (ξ x : Fin d → ℝ) :
    conj (exponentialCharacter ξ x) = exponentialCharacter (-ξ) x := by
  unfold exponentialCharacter
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_sum, map_ofNat, Finset.sum_neg_distrib]

lemma ec_int (n : Fin d → ℤ) (f : Fin d → ℤ) : exponentialCharacter (ic n) (zv f) = 1 := by
  unfold exponentialCharacter
  rw [Complex.exp_eq_one_iff]
  refine ⟨∑ i, n i * f i, ?_⟩
  simp only [ic, zv]
  push_cast
  ring

lemma ec_ne_zero (ξ x : Fin d → ℝ) : exponentialCharacter ξ x ≠ 0 := by
  unfold exponentialCharacter
  exact Complex.exp_ne_zero _

lemma mFourier_eq (n : Fin d → ℤ) (θ : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier n θ = exponentialCharacter (ic n) (ψ θ) := by
  have hθ : θ = fun i => ((ψ θ i : ℝ) : UnitAddCircle) := by
    conv_lhs => rw [← (UnitAddTorus.measurableEquivPiIoc (0 : Fin d → ℝ)).symm_apply_apply θ]
    rfl
  generalize ψ θ = y at hθ ⊢
  subst hθ
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    exponentialCharacter, ic]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

lemma ψ_mp : MeasurePreserving (ψ (d := d)) μT (volume.restrict (Sq (d := d))) := by
  have h1 := UnitAddTorus.measurePreserving_equivPiIoc (0 : Fin d → ℝ)
  have hS : MeasurableSet {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin d → ℝ) i) ((0 : Fin d → ℝ) i + 1)} := by
    convert (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc) :
      MeasurableSet (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) 1)) using 1
    ext x
    simp
  have h2 : MeasurePreserving
      (Subtype.val : {x : Fin d → ℝ // ∀ i, x i ∈ Set.Ioc ((0 : Fin d → ℝ) i) ((0 : Fin d → ℝ) i + 1)} → _)
      (Measure.comap Subtype.val volume) (volume.restrict _) :=
    ⟨measurable_subtype_coe, map_comap_subtype_coe hS volume⟩
  have h3 := h2.comp h1
  have hset : volume.restrict {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin d → ℝ) i) ((0 : Fin d → ℝ) i + 1)}
      = volume.restrict Sq := by
    apply Measure.restrict_congr_set
    have e1 : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin d → ℝ) i) ((0 : Fin d → ℝ) i + 1)} =
        Set.univ.pi (fun i => Set.Ioc ((fun _ : Fin d => (0 : ℝ)) i) ((fun _ : Fin d => (1 : ℝ)) i)) := by
      ext x
      simp
    rw [e1, Sq]
    exact Measure.univ_pi_Ioc_ae_eq_Icc.trans
      (Measure.univ_pi_Ico_ae_eq_Icc (f := fun _ : Fin d => (0 : ℝ)) (g := fun _ => (1 : ℝ))).symm
  rw [hset] at h3
  exact h3

lemma integral_Sq_eq (φ : (Fin d → ℝ) → ℂ) (hφ : AEStronglyMeasurable φ (volume.restrict Sq)) :
    ∫ y in Sq, φ y = ∫ θ, φ (ψ θ) ∂μT := by
  rw [← ψ_mp.map_eq] at hφ ⊢
  exact integral_map ψ_mp.measurable.aemeasurable hφ

lemma integral_Sq_ec (k : Fin d → ℤ) (hk : k ≠ 0) :
    ∫ y in Sq, exponentialCharacter (ic k) y = 0 := by
  rw [integral_Sq_eq _ (continuous_exponentialCharacter _).aestronglyMeasurable]
  simp_rw [← mFourier_eq]
  have h : ⟪UnitAddTorus.mFourierLp 2 (0 : Fin d → ℤ), UnitAddTorus.mFourierLp 2 k⟫_ℂ = 0 :=
    (UnitAddTorus.orthonormal_mFourier (d := Fin d)).2 (Ne.symm hk : (0 : Fin d → ℤ) ≠ k)
  simp only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp] at h
  simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] at h
  exact h

lemma fourier_complete (G : (Fin d → ℝ) → ℂ) (hG : MemLp G 2 (volume.restrict Sq))
    (h : ∀ n : Fin d → ℤ, ∫ y in Sq, conj (exponentialCharacter (ic n) y) * G y = 0) :
    G =ᵐ[volume.restrict Sq] 0 := by
  have hGψ : MemLp (G ∘ ψ) 2 μT := hG.comp_measurePreserving ψ_mp
  set Gt : Lp ℂ 2 μT := hGψ.toLp (G ∘ ψ) with hGt
  have hcoef : ∀ n : Fin d → ℤ, ⟪UnitAddTorus.mFourierLp 2 n, Gt⟫_ℂ = 0 := by
    intro n
    rw [L2.inner_def]
    have h1 : ∫ a, ⟪(UnitAddTorus.mFourierLp 2 n : UnitAddTorus (Fin d) → ℂ) a,
        (Gt : UnitAddTorus (Fin d) → ℂ) a⟫_ℂ ∂μT
        = ∫ θ, conj (exponentialCharacter (ic n) (ψ θ)) * G (ψ θ) ∂μT := by
      apply integral_congr_ae
      filter_upwards [UnitAddTorus.coeFn_mFourierLp 2 n, hGψ.coeFn_toLp] with θ h1 h2
      rw [h1, h2, RCLike.inner_apply, mul_comm, mFourier_eq]
      rfl
    refine h1.trans ?_
    rw [← integral_Sq_eq (fun y => conj (exponentialCharacter (ic n) y) * G y) ?_]
    · exact h n
    · exact (Complex.continuous_conj.comp
        (continuous_exponentialCharacter _)).aestronglyMeasurable.mul hG.1
  have hzero : Gt = 0 := by
    apply (UnitAddTorus.mFourierBasis (d := Fin d)).repr.injective
    rw [map_zero]
    ext n
    rw [HilbertBasis.repr_apply_apply, UnitAddTorus.coe_mFourierBasis, hcoef n]
    rfl
  have hae : G ∘ ψ =ᵐ[μT] 0 := by
    have := hGψ.coeFn_toLp
    rw [← hGt, hzero] at this
    exact this.symm.trans (Lp.coeFn_zero _ _ _)
  have h2 : eLpNorm G 2 (volume.restrict Sq) = 0 := by
    rw [← eLpNorm_comp_measurePreserving hG.1 ψ_mp, eLpNorm_congr_ae hae, eLpNorm_zero]
  exact (eLpNorm_eq_zero_iff hG.1 two_ne_zero).1 h2

lemma Sq_measurable : MeasurableSet (Sq (d := d)) := by
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma volume_Sq : volume (Sq (d := d)) = 1 := by
  rw [Sq, Real.volume_pi_Ico (a := fun _ => 0) (b := fun _ => 1)]
  simp

lemma preimage_piece (f : Fin d → ℤ) : (fun y => y + zv f) ⁻¹' piece f = Sq := by
  ext y
  simp only [piece, Sq, zv, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ_pi,
    Pi.add_apply, funext_iff, Int.floor_add_intCast, add_eq_right, Int.floor_eq_zero_iff]

lemma piece_measurable (f : Fin d → ℤ) : MeasurableSet (piece f) := by
  have : piece f = (fun x => x - zv f) ⁻¹' Sq := by
    rw [← preimage_piece f]
    ext x
    simp
  rw [this]
  exact Sq_measurable.preimage (measurable_id.sub_const _)

lemma boxSet_eq (F : Finset (Fin d → ℤ)) : boxSet (F : Set (Fin d → ℤ)) = ⋃ f ∈ F, piece f := by
  ext x
  simp [boxSet, piece]

lemma piece_disjoint (F : Finset (Fin d → ℤ)) : (F : Set (Fin d → ℤ)).PairwiseDisjoint piece := by
  intro f _ f' _ hff'
  exact Set.disjoint_left.2 fun x h1 h2 => hff' (h1.symm.trans h2)

lemma mp_piece (f : Fin d → ℤ) :
    MeasurePreserving (fun y => y + zv f) (volume.restrict Sq) (volume.restrict (piece f)) := by
  have h := (measurePreserving_add_right volume (zv f)).restrict_preimage_emb
    (MeasurableEquiv.addRight (zv f)).measurableEmbedding (piece f)
  rwa [preimage_piece] at h

lemma volume_piece (f : Fin d → ℤ) : volume (piece f) = 1 := by
  rw [← measure_preimage_add_right volume (zv f) (piece f), preimage_piece, volume_Sq]

lemma volume_boxSet (F : Finset (Fin d → ℤ)) : volume (boxSet (F : Set (Fin d → ℤ))) = F.card := by
  rw [boxSet_eq, measure_biUnion_finset (piece_disjoint F) (fun f _ => piece_measurable f)]
  simp [volume_piece]

lemma integral_boxSet (F : Finset (Fin d → ℤ)) (h : (Fin d → ℝ) → ℂ)
    (hint : IntegrableOn h (boxSet (F : Set (Fin d → ℤ)))) :
    ∫ x in boxSet (F : Set (Fin d → ℤ)), h x = ∑ f ∈ F, ∫ y in Sq, h (y + zv f) := by
  rw [boxSet_eq] at hint ⊢
  rw [integral_biUnion_finset F (fun f _ => piece_measurable f) (piece_disjoint F)
    (fun f hf => hint.mono_set (Set.subset_biUnion_of_mem (u := piece) hf))]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h := (measurePreserving_add_right volume (zv f)).setIntegral_preimage_emb
    (MeasurableEquiv.addRight (zv f)).measurableEmbedding h (piece f)
  rw [preimage_piece] at h
  exact h.symm

lemma memLp_shift (F : Finset (Fin d → ℤ)) {f : Fin d → ℤ} (hf : f ∈ F) (g : (Fin d → ℝ) → ℂ)
    (hg : MemLp g 2 (volume.restrict (boxSet (F : Set (Fin d → ℤ))))) :
    MemLp (fun y => g (y + zv f)) 2 (volume.restrict Sq) := by
  have hsub : piece f ⊆ boxSet (F : Set (Fin d → ℤ)) := by
    rw [boxSet_eq]
    exact Set.subset_biUnion_of_mem (u := piece) hf
  exact (hg.mono_measure (Measure.restrict_mono hsub le_rfl)).comp_measurePreserving (mp_piece f)

lemma ae_boxSet (F : Finset (Fin d → ℤ)) (g : (Fin d → ℝ) → ℂ)
    (h : ∀ f ∈ F, ∀ᵐ y ∂(volume.restrict Sq), g (y + zv f) = 0) :
    g =ᵐ[volume.restrict (boxSet (F : Set (Fin d → ℤ)))] 0 := by
  show ∀ᵐ x ∂(volume.restrict (boxSet (F : Set (Fin d → ℤ)))), g x = 0
  rw [boxSet_eq, ae_restrict_biUnion_finset_iff]
  intro f hf
  have hemb : MeasurableEmbedding (fun y : Fin d → ℝ => y + zv f) :=
    (MeasurableEquiv.addRight (zv f)).measurableEmbedding
  rw [← (mp_piece f).map_eq, hemb.ae_map_iff]
  exact h f hf

lemma ec_zero (x : Fin d → ℝ) : exponentialCharacter 0 x = 1 := by
  simp [exponentialCharacter]

lemma Sq_finite : IsFiniteMeasure (volume.restrict (Sq (d := d))) :=
  isFiniteMeasure_restrict.2 (by rw [volume_Sq]; exact ENNReal.one_ne_top)

lemma memLp_mul_unit {φ u : (Fin d → ℝ) → ℂ} {ν : Measure (Fin d → ℝ)} (hφ : MemLp φ 2 ν)
    (hu : Continuous u) (hn : ∀ x, ‖u x‖ = 1) : MemLp (fun x => u x * φ x) 2 ν :=
  hφ.congr_norm (hu.aestronglyMeasurable.mul hφ.1) (ae_of_all _ fun x => by simp [hn])

lemma linalg (F : Finset (Fin d → ℤ)) (Λ₀ : Finset (Fin d → ℝ)) (hcard : Λ₀.card = F.card)
    (horth : ∀ μ ∈ Λ₀, ∀ μ' ∈ Λ₀, μ ≠ μ' →
      ∑ f ∈ F, exponentialCharacter (μ - μ') (zv f) = 0)
    (w : (Fin d → ℤ) → ℂ) (hw : ∀ μ ∈ Λ₀, ∑ f ∈ F, conj (exponentialCharacter μ (zv f)) * w f = 0) :
    ∀ f ∈ F, w f = 0 := by
  classical
  rcases F.eq_empty_or_nonempty with hF | hF
  · simp [hF]
  have hc : (F.card : ℂ) ≠ 0 := by exact_mod_cast hF.card_pos.ne'
  let M : Matrix Λ₀ F ℂ := fun μ f => (F.card : ℂ)⁻¹ * conj (exponentialCharacter μ.1 (zv f.1))
  let N : Matrix F Λ₀ ℂ := fun f μ => exponentialCharacter μ.1 (zv f.1)
  have hMN : M * N = 1 := by
    ext μ μ'
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [M, N]
    simp_rw [ec_conj, mul_assoc, ← ec_add_left]
    rw [← Finset.mul_sum, Finset.sum_coe_sort F (fun f => exponentialCharacter (-μ.1 + μ'.1) (zv f))]
    split_ifs with h
    · subst h
      simp [ec_zero, hc]
    · have := horth μ'.1 μ'.2 μ.1 μ.2 (fun h' => h (Subtype.ext h'.symm))
      rw [show -μ.1 + μ'.1 = μ'.1 - μ.1 by abel, this, mul_zero]
  have e : Λ₀ ≃ F := Fintype.equivOfCardEq (by simp [hcard])
  have hNM : N * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hMN
  have hMw : Matrix.mulVec M (fun f : F => w f.1) = 0 := by
    funext μ
    rw [Matrix.mulVec, Pi.zero_apply]
    simp only [dotProduct, M, mul_assoc]
    rw [← Finset.mul_sum,
      Finset.sum_coe_sort F (fun f => conj (exponentialCharacter μ.1 (zv f)) * w f), hw μ.1 μ.2,
      mul_zero]
  have hw0 : (fun f : F => w f.1) = 0 := by
    have := congrArg (Matrix.mulVec N) hMw
    simp only [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  intro f hf
  exact congrFun hw0 ⟨f, hf⟩

lemma inner_toLp_eq {Ω : Set (Fin d → ℝ)} (u v : (Fin d → ℝ) → ℂ)
    (hu : MemLp u 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω)) :
    ⟪hu.toLp u, hv.toLp v⟫_ℂ = ∫ x in Ω, conj (u x) * v x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

theorem H1a_holds : H1a d := by
  intro F Λ₀ hne hcard horth
  have horth' : ∀ μ ∈ Λ₀, ∀ μ' ∈ Λ₀, μ ≠ μ' →
      ∑ f ∈ F, exponentialCharacter (μ - μ') (zv f) = 0 := horth
  have hfin : volume (boxSet (F : Set (Fin d → ℤ))) ≠ ⊤ := by
    rw [volume_boxSet]
    exact ENNReal.natCast_ne_top _
  have hfm : IsFiniteMeasure (volume.restrict (boxSet (F : Set (Fin d → ℤ)))) :=
    isFiniteMeasure_restrict.2 hfin
  have := Sq_finite (d := d)
  refine ⟨{ξ | ∃ μ ∈ Λ₀, ∃ n : Fin d → ℤ, ξ = μ + ic n}, ?_, ?_, hfin, ?_⟩
  · rw [boxSet_eq]
    exact (MeasurableSet.biUnion F.countable_toSet fun f _ => piece_measurable f).nullMeasurableSet
  · rw [volume_boxSet]
    exact_mod_cast hne.card_pos
  intro e
  refine ⟨?_, ?_⟩
  · rintro ξ₁ ⟨μ, hμ, n, rfl⟩ ξ₂ ⟨μ', hμ', n', rfl⟩ h12
    simp only [e]
    rw [inner_toLp_eq]
    have hpt : ∀ x, conj (exponentialCharacter (μ + ic n) x) * exponentialCharacter (μ' + ic n') x
        = exponentialCharacter ((μ' - μ) + ic (n' - n)) x := by
      intro x
      rw [ec_conj, ← ec_add_left]
      congr 1
      ext i
      simp only [ic, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Int.cast_sub]
      ring
    simp_rw [hpt]
    rw [integral_boxSet F _ ((exponentialCharacter_memLp hfin _).integrable one_le_two)]
    simp_rw [ec_add_right, integral_mul_const]
    rw [← Finset.mul_sum]
    by_cases hμμ : μ = μ'
    · subst hμμ
      have hk : n' - n ≠ 0 := by
        intro h
        apply h12
        rw [sub_eq_zero] at h
        rw [h]
      rw [sub_self, zero_add, integral_Sq_ec _ hk, zero_mul]
    · have : ∑ f ∈ F, exponentialCharacter (μ' - μ + ic (n' - n)) (zv f) = 0 := by
        simp_rw [ec_add_left, ec_int, mul_one]
        exact horth' μ' hμ' μ hμ (Ne.symm hμμ)
      rw [this, mul_zero]
  · rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro g hg
    rw [Submodule.mem_orthogonal] at hg
    have hgm : MemLp (g : (Fin d → ℝ) → ℂ) 2 (volume.restrict (boxSet (F : Set (Fin d → ℤ)))) :=
      Lp.memLp g
    have hg' : ∀ μ ∈ Λ₀, ∀ n : Fin d → ℤ,
        ∫ x in boxSet (F : Set (Fin d → ℤ)), conj (exponentialCharacter (μ + ic n) x) * g x = 0 := by
      intro μ hμ n
      have h1 := inner_toLp_eq _ _ (exponentialCharacter_memLp hfin (μ + ic n)) hgm
      rw [Lp.toLp_coeFn] at h1
      rw [← h1]
      exact hg _ (Submodule.subset_span ⟨⟨μ + ic n, μ, hμ, n, rfl⟩, rfl⟩)
    rw [Lp.eq_zero_iff_ae_eq_zero]
    apply ae_boxSet
    have hunit : ∀ ξ v : Fin d → ℝ, Continuous (fun y => conj (exponentialCharacter ξ (y + v))) :=
      fun ξ v => Complex.continuous_conj.comp
        ((continuous_exponentialCharacter ξ).comp (continuous_id.add continuous_const))
    have hunit' : ∀ ξ v y : Fin d → ℝ, ‖conj (exponentialCharacter ξ (y + v))‖ = 1 := by
      intro ξ v y
      rw [Complex.norm_conj, norm_exponentialCharacter]
    have key : ∀ μ ∈ Λ₀, (fun y => ∑ f ∈ F, conj (exponentialCharacter μ (y + zv f)) *
        g (y + zv f)) =ᵐ[volume.restrict Sq] 0 := by
      intro μ hμ
      apply fourier_complete
      · apply memLp_finsetSum F
        intro f hf
        exact memLp_mul_unit (memLp_shift F hf g hgm) (hunit μ (zv f)) (hunit' μ (zv f))
      · intro n
        have hint : IntegrableOn (fun x => conj (exponentialCharacter (μ + ic n) x) * g x)
            (boxSet (F : Set (Fin d → ℤ))) := by
          have := memLp_mul_unit hgm (hunit (μ + ic n) 0) (hunit' (μ + ic n) 0)
          simp only [add_zero] at this
          exact this.integrable one_le_two
        rw [← hg' μ hμ n, integral_boxSet F _ hint, ← integral_finsetSum]
        · congr 1
          funext y
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [ec_add_left, map_mul, ec_add_right (ic n), ec_int, mul_one]
          ring
        · intro f hf
          have := memLp_mul_unit (memLp_shift F hf g hgm) (hunit (μ + ic n) (zv f))
            (hunit' (μ + ic n) (zv f))
          exact this.integrable one_le_two
    have key2 := (Filter.eventually_all_finset Λ₀).2 key
    have hall : ∀ᵐ y ∂(volume.restrict Sq), ∀ f ∈ F, g (y + zv f) = 0 := by
      filter_upwards [key2] with y hy
      apply linalg F Λ₀ hcard horth' (fun f => g (y + zv f))
      intro μ hμ
      have h0 : ∑ f ∈ F, conj (exponentialCharacter μ (y + zv f)) * g (y + zv f) = 0 := hy μ hμ
      simp_rw [ec_add_right, map_mul, mul_assoc] at h0
      rw [← Finset.mul_sum] at h0
      exact (mul_eq_zero.1 h0).resolve_left (by simpa using ec_ne_zero μ y)
    intro f hf
    filter_upwards [hall] with y hy using hy f hf

end FugledeGen

namespace FugledeD3

open MeasureTheory

def ιz (m : ℕ) (z : ℤ × ℤ) : Fin (m + 2) → ℤ := Fin.cons z.1 (Fin.cons z.2 0)

noncomputable def κ (m : ℕ) (μ : Fin 2 → ℝ) : Fin (m + 2) → ℝ := Fin.cons (μ 0) (Fin.cons (μ 1) 0)

lemma ιz_inj (m : ℕ) : Function.Injective (ιz m) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h (Fin.succ 0)
  simp only [ιz, Fin.cons_zero, Fin.cons_succ] at h0 h1
  exact Prod.ext h0 h1

lemma ιz_add (m : ℕ) (a b : ℤ × ℤ) : ιz m (a + b) = ιz m a + ιz m b := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [ιz]

lemma ιz_sub (m : ℕ) (a b : ℤ × ℤ) : ιz m (a - b) = ιz m a - ιz m b := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [ιz]

lemma κ_inj (m : ℕ) : Function.Injective (κ m) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h (Fin.succ 0)
  simp only [κ, Fin.cons_zero, Fin.cons_succ] at h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

lemma ec_transfer (m : ℕ) (μ μ' : Fin 2 → ℝ) (z : ℤ × ℤ) :
    exponentialCharacter (κ m μ - κ m μ') (fun i => ((ιz m z i : ℤ) : ℝ)) =
      exponentialCharacter (μ - μ') ![(z.1 : ℝ), (z.2 : ℝ)] := by
  unfold exponentialCharacter
  congr 2
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_two]
  simp [κ, ιz]

noncomputable def FN (m : ℕ) : Finset (Fin (m + 2) → ℤ) :=
  (FugledeScratch.Ffin 60 12 97 FugledeScratch.Aplus).image (ιz m)

lemma mem_FN (m : ℕ) (f : Fin (m + 2) → ℤ) :
    f ∈ FN m ↔ ∃ w ∈ FugledeScratch.Ffin 60 12 97 FugledeScratch.Aplus, ιz m w = f := by
  rw [FN, Finset.mem_image]

def ΩN (m : ℕ) : Set (Fin (m + 2) → ℝ) := FugledeGen.boxSet ((FN m : Finset _) : Set (Fin (m + 2) → ℤ))

set_option maxRecDepth 200000 in
lemma mem00 : ((0 : ℤ), (0 : ℤ)) ∈ FugledeScratch.Ffin 60 12 97 FugledeScratch.Aplus := by
  rw [FugledeScratch.mem_Ffin]
  refine ⟨le_refl _, by norm_num, le_refl _, by norm_num, ?_⟩
  simp only [Int.cast_zero]
  rw [FugledeScratch.Aplus, List.mem_toFinset]
  decide

set_option maxRecDepth 200000 in
lemma specN (m : ℕ) : isSpectral (ΩN m) := by
  obtain ⟨Λ₀, hcard, horth⟩ := FugledeScratch.H1b_holds
  apply FugledeGen.H1a_holds (FN m) (Λ₀.image (κ m))
  · exact ⟨ιz m (0, 0), (mem_FN m _).2 ⟨_, mem00, rfl⟩⟩
  · rw [Finset.card_image_of_injective _ (κ_inj m), FN,
      Finset.card_image_of_injective _ (ιz_inj m), hcard]
  · intro μ hμ μ' hμ' hne
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hμ
    obtain ⟨ν', hν', rfl⟩ := Finset.mem_image.1 hμ'
    rw [FN, Finset.sum_image (fun x _ y _ h => ιz_inj m h)]
    simp_rw [ec_transfer]
    exact horth ν hν ν' hν' (fun h => hne (by rw [h]))

lemma keyN {d : ℕ} (F : Set (Fin d → ℤ)) (x t : Fin d → ℝ) (n : Fin d → ℤ) :
    (x + fun i => (n i : ℝ)) ∈ translateSet (FugledeGen.boxSet F) t ↔
      n - (fun i => -⌊x i - t i⌋) ∈ F := by
  simp only [translateSet, FugledeGen.boxSet, Set.mem_setOf_eq, Pi.sub_apply, Pi.add_apply]
  have : (fun i => ⌊x i + (n i : ℝ) - t i⌋) = n - (fun i => -⌊x i - t i⌋) := by
    funext i
    rw [show x i + (n i : ℝ) - t i = (x i - t i) + (n i : ℝ) by ring, Int.floor_add_intCast]
    simp only [Pi.sub_apply]
    ring
  rw [this]

theorem tile_transferN {d : ℕ} (F : Set (Fin d → ℤ)) (h : tilesByTranslation (FugledeGen.boxSet F)) :
    ∃ B : Set (Fin d → ℤ), FugledeScratch.TilesWith F B := by
  obtain ⟨T, hTc, hcov, hdisj⟩ := h
  have : Countable T := hTc.to_subtype
  set Ω := FugledeGen.boxSet F
  set U : Set (Fin d → ℝ) := Set.univ \ ⋃ t ∈ T, translateSet Ω t
  set O : Set (Fin d → ℝ) :=
    ⋃ p : T × T, ⋃ (_ : p.1 ≠ p.2), translateSet Ω p.1 ∩ translateSet Ω p.2
  have hO : volume O = 0 := by
    apply measure_iUnion_null; intro p
    apply measure_iUnion_null; intro hp
    exact hdisj p.1.2 p.2.2 (fun h => hp (Subtype.ext h))
  set v : (Fin d → ℤ) → (Fin d → ℝ) := fun n => fun i => (n i : ℝ)
  set Bad : Set (Fin d → ℝ) := ⋃ n : Fin d → ℤ, (fun y => y + v n) ⁻¹' (U ∪ O)
  have hBad : volume Bad = 0 := by
    apply measure_iUnion_null; intro n
    rw [measure_preimage_add_right]
    exact measure_union_null hcov hO
  have hne : (Badᶜ).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hc
    have hu : volume (Set.univ : Set (Fin d → ℝ)) = 0 := hc ▸ hBad
    have h1 : volume (Set.univ.pi fun _ : Fin d => Set.Ico (0 : ℝ) 1) = 1 := by
      rw [Real.volume_pi_Ico]; simp
    have h2 := measure_mono_null (Set.subset_univ (Set.univ.pi fun _ : Fin d => Set.Ico (0 : ℝ) 1)) hu
    rw [h1] at h2
    exact one_ne_zero h2
  obtain ⟨x, hx⟩ := hne
  have hx' : ∀ n, x + v n ∉ U ∪ O := by
    intro n hn; apply hx; exact Set.mem_iUnion.2 ⟨n, hn⟩
  set b : (Fin d → ℝ) → (Fin d → ℤ) := fun t => fun i => -⌊x i - t i⌋
  refine ⟨b '' T, ?_⟩
  intro z
  have hcz : x + v z ∈ ⋃ t ∈ T, translateSet Ω t := by
    by_contra hc; exact hx' z (Or.inl ⟨Set.mem_univ _, hc⟩)
  obtain ⟨t, htT, hzt⟩ := Set.mem_iUnion₂.1 hcz
  refine ⟨(z - b t, b t), ⟨(keyN F x t z).1 hzt, ⟨t, htT, rfl⟩, by simp⟩, ?_⟩
  rintro ⟨f, b'⟩ ⟨hf, ⟨t', ht'T, rfl⟩, hsum⟩
  simp only at hf hsum
  have hft : f = z - b t' := by rw [← hsum]; abel
  have hzt' : x + v z ∈ translateSet Ω t' := (keyN F x t' z).2 (hft ▸ hf)
  have htt : t' = t := by
    by_contra hne'
    apply hx' z
    right
    exact Set.mem_iUnion.2 ⟨(⟨t', ht'T⟩, ⟨t, htT⟩), Set.mem_iUnion.2
      ⟨fun h => hne' (congrArg Subtype.val h), hzt', hzt⟩⟩
  subst htt
  simp [hft]

set_option maxRecDepth 200000 in
lemma slice (m : ℕ) (B : Set (Fin (m + 2) → ℤ))
    (hB : FugledeScratch.TilesWith ((FN m : Finset _) : Set (Fin (m + 2) → ℤ)) B) :
    FugledeScratch.TilesWith FugledeScratch.Fplus {p | ιz m p ∈ B} := by
  intro z
  obtain ⟨⟨f, b⟩, ⟨hf, hb, hfb⟩, huniq⟩ := hB (ιz m z)
  simp only at hf hb hfb
  obtain ⟨w, hw, rfl⟩ := (mem_FN m f).1 (Finset.mem_coe.1 hf)
  have hb' : b = ιz m (z - w) := by rw [ιz_sub, ← hfb]; abel
  refine ⟨(w, z - w), ⟨by rw [FugledeScratch.Fplus_eq]; exact hw,
    by simp only [Set.mem_setOf_eq]; rw [← hb']; exact hb, by simp⟩, ?_⟩
  rintro ⟨w', c⟩ ⟨hw', hc, hsum⟩
  simp only [Set.mem_setOf_eq] at hw' hc hsum
  rw [FugledeScratch.Fplus_eq] at hw'
  have e := huniq (ιz m w', ιz m c) ⟨Finset.mem_coe.2 ((mem_FN m _).2 ⟨w', hw', rfl⟩), hc, by
    simp only; rw [← ιz_add, hsum]⟩
  simp only [Prod.mk.injEq] at e
  have hww : w' = w := ιz_inj m e.1
  subst hww
  have : c = z - w' := by rw [← hsum]; abel
  rw [this]

set_option maxRecDepth 200000 in
lemma no_tile_Fplus : ¬ ∃ B : Set (ℤ × ℤ), FugledeScratch.TilesWith FugledeScratch.Fplus B := by
  rintro ⟨B, hB⟩
  apply FugledeScratch.H2_holds
  refine FugledeScratch.H3_holds 60 12 97 FugledeScratch.Aplus (by norm_num) (by norm_num)
    (by norm_num) (by rw [FugledeScratch.Aplus_card]; norm_num) ⟨B, ?_⟩
  simpa [FugledeScratch.Fplus] using hB

set_option maxRecDepth 200000 in
lemma measN (m : ℕ) : MeasurableSet (ΩN m) := by
  have hm : Measurable (fun x : Fin (m + 2) → ℝ => fun i => ⌊x i⌋) :=
    measurable_pi_lambda _ (fun i => Int.measurable_floor.comp (measurable_pi_apply i))
  exact hm (Set.to_countable _).measurableSet

set_option maxRecDepth 200000 in
lemma boundedN (m : ℕ) : Bornology.IsBounded (ΩN m) := by
  apply (Metric.isBounded_Icc (0 : Fin (m + 2) → ℝ) (fun _ => 5820)).subset
  intro x hx
  obtain ⟨w, hw, hwx⟩ := (mem_FN m _).1 (Finset.mem_coe.1 hx)
  rw [FugledeScratch.mem_Ffin] at hw
  obtain ⟨w1, w2, w3, w4, -⟩ := hw
  have hb : ∀ i, 0 ≤ ιz m w i ∧ ιz m w i < 5820 := by
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simp only [ιz, Fin.cons_zero]; push_cast at w2; omega
    · simp only [ιz, Fin.cons_succ, Fin.cons_zero]; push_cast at w4; omega
    · simp [ιz]
  have hxi : ∀ i, 0 ≤ x i ∧ x i < 5820 := by
    intro i
    have h1 : ⌊x i⌋ = ιz m w i := (congrFun hwx i).symm
    obtain ⟨c1, c2⟩ := hb i
    constructor
    · exact Int.floor_nonneg.1 (by rw [h1]; exact c1)
    · have := Int.floor_lt.1 (show ⌊x i⌋ < ((5820 : ℤ)) by rw [h1]; exact c2)
      exact_mod_cast this
  exact ⟨fun i => (hxi i).1, fun i => (hxi i).2.le⟩

set_option maxRecDepth 200000 in
theorem notFC (m : ℕ) : ¬ Fuglede.FugledeConjectureFor (m + 2) := by
  intro hF
  have hs := specN m
  have hpos : 0 < volume (ΩN m) := by
    obtain ⟨Λ, _, h, _⟩ := hs
    exact h
  have ht := (hF _ (boundedN m) (measN m) hpos).1 hs
  obtain ⟨B, hB⟩ := tile_transferN _ ht
  exact no_tile_Fplus ⟨_, slice m B hB⟩

end FugledeD3

theorem OMA.solution : type_of% @Fuglede.FugledeConjecture.variants.dim_3_or_higher := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact FugledeD3.notFC m
