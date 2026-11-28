import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

-- Step Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H1.R1.H3: hypothesis H3 of reduction Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H1.R1
-- Credit: @KevinBigham

namespace Erdos1160H3Proof

open CategoryTheory Erdos1160

private abbrev UpperPairs (d : ℕ) := {p : Fin d × Fin d // p.1 ≤ p.2}

private lemma card_upperPairs (d : ℕ) : Fintype.card (UpperPairs d) = d * (d + 1) / 2 := by
  classical
  have h1 : Fintype.card (UpperPairs d) =
      (Finset.univ.filter (fun p : Fin d × Fin d => p.1 ≤ p.2)).card := by
    rw [Fintype.card_subtype]
  rw [h1]
  have hfiber : (Finset.univ.filter (fun p : Fin d × Fin d => p.1 ≤ p.2)).card =
      ∑ j : Fin d, ((Finset.univ.filter (fun p : Fin d × Fin d => p.1 ≤ p.2)).filter
        (fun p => p.2 = j)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp
    · intro j₁ _ j₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      simp only [Finset.mem_filter] at hp₁ hp₂
      exact hne (hp₁.2.symm.trans hp₂.2)
  rw [hfiber]
  have hslice : ∀ j : Fin d,
      ((Finset.univ.filter (fun p : Fin d × Fin d => p.1 ≤ p.2)).filter
        (fun p => p.2 = j)).card = j.val + 1 := by
    intro j
    have heq : (Finset.univ.filter (fun p : Fin d × Fin d => p.1 ≤ p.2)).filter
        (fun p => p.2 = j) = (Finset.Iic j).image (fun i : Fin d => (i, j)) := by
      ext ⟨i, j'⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_Iic, Prod.mk.injEq]
      constructor
      · rintro ⟨hij, rfl⟩
        exact ⟨i, hij, rfl, rfl⟩
      · rintro ⟨i', hi', rfl, rfl⟩
        exact ⟨hi', rfl⟩
    rw [heq, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
    have hIic : (Finset.Iic j).card = (Finset.range (j.val + 1)).card := by
      refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_Iic] at hi
        simp only [Finset.mem_range]
        exact Nat.lt_succ_of_le hi
      · intro i₁ _ i₂ _ h
        exact Fin.ext h
      · intro a ha
        simp only [Finset.mem_range] at ha
        exact ⟨⟨a, Nat.lt_of_lt_of_le ha j.isLt⟩,
          by simp [Finset.mem_Iic, Fin.le_def, Nat.le_of_lt_succ ha], rfl⟩
    rw [hIic, Finset.card_range]
  simp_rw [hslice]
  have hsum : ∑ j : Fin d, (j.val + 1) = ∑ i ∈ Finset.range (d + 1), i := by
    rw [Finset.sum_range_succ']
    simp only [add_zero]
    rw [Fin.sum_univ_eq_sum_range (fun x => x + 1) d]
  rw [hsum, Finset.sum_range_id]
  simp [Nat.mul_comm]

private abbrev Param (d k : ℕ) := UpperPairs d → (Fin k → ZMod 2)

private lemma card_param (d k : ℕ) : Fintype.card (Param d k) = 2 ^ (k * (d * (d + 1) / 2)) := by
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, card_upperPairs, ← pow_mul]

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

private lemma vec_add_self {n : ℕ} (u : Fin n → ZMod 2) : u + u = 0 :=
  funext fun i => zmod2_add_self (u i)

private def beta {d k : ℕ} (B : Param d k) (v₁ v₂ : Fin d → ZMod 2) : Fin k → ZMod 2 :=
  fun r => ∑ p : UpperPairs d, v₁ p.1.1 * v₂ p.1.2 * B p r

private lemma beta_zero_left {d k : ℕ} (B : Param d k) (v : Fin d → ZMod 2) :
    beta B 0 v = 0 := by
  funext r
  simp [beta]

private lemma beta_zero_right {d k : ℕ} (B : Param d k) (v : Fin d → ZMod 2) :
    beta B v 0 = 0 := by
  funext r
  simp [beta]

private lemma beta_add_left {d k : ℕ} (B : Param d k) (v₁ v₂ v₃ : Fin d → ZMod 2) :
    beta B (v₁ + v₂) v₃ = beta B v₁ v₃ + beta B v₂ v₃ := by
  funext r
  simp only [beta, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma beta_add_right {d k : ℕ} (B : Param d k) (v₁ v₂ v₃ : Fin d → ZMod 2) :
    beta B v₁ (v₂ + v₃) = beta B v₁ v₂ + beta B v₁ v₃ := by
  funext r
  simp only [beta, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private structure C2G {d k : ℕ} (B : Param d k) where
  v : Fin d → ZMod 2
  w : Fin k → ZMod 2

private lemma C2G.ext_iff {d k : ℕ} {B : Param d k} {x y : C2G B} :
    x = y ↔ x.v = y.v ∧ x.w = y.w := by
  cases x; cases y; simp

private def C2G.equivProd {d k : ℕ} (B : Param d k) :
    C2G B ≃ (Fin d → ZMod 2) × (Fin k → ZMod 2) where
  toFun x := (x.v, x.w)
  invFun p := ⟨p.1, p.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by cases p; rfl

private instance instFintypeC2G {d k : ℕ} (B : Param d k) : Fintype (C2G B) :=
  Fintype.ofEquiv _ (C2G.equivProd B).symm

private lemma card_C2G {d k : ℕ} (B : Param d k) : Nat.card (C2G B) = 2 ^ (d + k) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (C2G.equivProd B), Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin, pow_add]

private instance instGroupC2G {d k : ℕ} (B : Param d k) : Group (C2G B) where
  one := ⟨0, 0⟩
  mul x y := ⟨x.v + y.v, x.w + y.w + beta B x.v y.v⟩
  inv x := ⟨x.v, x.w + beta B x.v x.v⟩
  mul_assoc x y z := by
    change (⟨(x.v + y.v) + z.v,
      (x.w + y.w + beta B x.v y.v) + z.w + beta B (x.v + y.v) z.v⟩ : C2G B) =
      ⟨x.v + (y.v + z.v),
        x.w + (y.w + z.w + beta B y.v z.v) + beta B x.v (y.v + z.v)⟩
    rw [C2G.ext_iff]
    refine ⟨add_assoc _ _ _, ?_⟩
    simp only [beta_add_left, beta_add_right]
    abel
  one_mul x := by
    change (⟨0 + x.v, 0 + x.w + beta B 0 x.v⟩ : C2G B) = x
    rw [C2G.ext_iff]
    simp [beta_zero_left]
  mul_one x := by
    change (⟨x.v + 0, x.w + 0 + beta B x.v 0⟩ : C2G B) = x
    rw [C2G.ext_iff]
    simp [beta_zero_right]
  inv_mul_cancel x := by
    change (⟨x.v + x.v, (x.w + beta B x.v x.v) + x.w + beta B x.v x.v⟩ : C2G B) = ⟨0, 0⟩
    rw [C2G.ext_iff]
    refine ⟨vec_add_self x.v, ?_⟩
    dsimp only
    have h1 : x.w + beta B x.v x.v + x.w + beta B x.v x.v =
        (x.w + x.w) + (beta B x.v x.v + beta B x.v x.v) := by abel
    rw [h1, vec_add_self x.w, vec_add_self (beta B x.v x.v), add_zero]

private def basisV (d : ℕ) (i : Fin d) : Fin d → ZMod 2 :=
  fun t => if t = i then 1 else 0

private def basisW (k : ℕ) (r : Fin k) : Fin k → ZMod 2 :=
  fun s => if s = r then 1 else 0

private lemma beta_basisV_of_le {d k : ℕ} (B : Param d k) {i j : Fin d} (hij : i ≤ j) :
    beta B (basisV d i) (basisV d j) = B ⟨(i, j), hij⟩ := by
  funext r
  unfold beta
  rw [Finset.sum_eq_single (⟨(i, j), hij⟩ : UpperPairs d)]
  · simp [basisV]
  · intro p _ hp
    have hne : p.1.1 ≠ i ∨ p.1.2 ≠ j := by
      by_contra h
      push Not at h
      apply hp
      exact Subtype.ext (Prod.ext h.1 h.2)
    rcases hne with h1 | h2
    · simp [basisV, h1]
    · simp [basisV, h2]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma beta_basisV_of_lt_rev {d k : ℕ} (B : Param d k) {i j : Fin d} (hij : i < j) :
    beta B (basisV d j) (basisV d i) = 0 := by
  funext r
  unfold beta
  apply Finset.sum_eq_zero
  intro p _
  by_cases h1 : p.1.1 = j
  · by_cases h2 : p.1.2 = i
    · have hle : j ≤ i := h1 ▸ h2 ▸ p.2
      exact absurd (lt_of_lt_of_le hij hle) (lt_irrefl _)
    · simp [basisV, h2]
  · simp [basisV, h1]

private lemma sq_basisV {d k : ℕ} (B : Param d k) (i : Fin d) :
    (⟨basisV d i, 0⟩ : C2G B) * ⟨basisV d i, 0⟩ = ⟨0, B ⟨(i, i), le_rfl⟩⟩ := by
  change (⟨basisV d i + basisV d i, 0 + 0 + beta B (basisV d i) (basisV d i)⟩ : C2G B) = _
  rw [C2G.ext_iff]
  exact ⟨vec_add_self _, by simp [beta_basisV_of_le]⟩

private lemma comm_basisV {d k : ℕ} (B : Param d k) {i j : Fin d} (hij : i < j) :
    ((⟨basisV d j, 0⟩ : C2G B) * ⟨basisV d i, 0⟩)⁻¹ *
      ((⟨basisV d i, 0⟩ : C2G B) * ⟨basisV d j, 0⟩) = ⟨0, B ⟨(i, j), hij.le⟩⟩ := by
  rw [inv_mul_eq_iff_eq_mul]
  change (⟨basisV d i + basisV d j, 0 + 0 + beta B (basisV d i) (basisV d j)⟩ : C2G B) =
    ⟨basisV d j + basisV d i + 0,
      0 + 0 + beta B (basisV d j) (basisV d i) + B ⟨(i, j), hij.le⟩ +
        beta B (basisV d j + basisV d i) 0⟩
  rw [C2G.ext_iff]
  refine ⟨by dsimp only; rw [add_zero, add_comm], ?_⟩
  dsimp only
  rw [beta_basisV_of_le B hij.le, beta_basisV_of_lt_rev B hij, beta_zero_right]
  simp

private lemma mul_zero_w {d k : ℕ} (B : Param d k) (w₁ w₂ : Fin k → ZMod 2) :
    (⟨0, w₁⟩ : C2G B) * ⟨0, w₂⟩ = ⟨0, w₁ + w₂⟩ := by
  change (⟨0 + 0, w₁ + w₂ + beta B 0 0⟩ : C2G B) = _
  rw [C2G.ext_iff]
  simp [beta_zero_left]

private lemma zero_w_eq_list_prod {d k : ℕ} (B : Param d k) (w : Fin k → ZMod 2) :
    (⟨0, w⟩ : C2G B) =
      ((List.finRange k).map fun r =>
        if w r = 1 then (⟨0, basisW k r⟩ : C2G B) else 1).prod := by
  have haux : ∀ l : List (Fin k), l.Nodup →
      (l.map fun r => if w r = 1 then (⟨0, basisW k r⟩ : C2G B) else 1).prod =
        ⟨0, fun t => if t ∈ l then w t else 0⟩ := by
    intro l hl
    induction l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, List.not_mem_nil, ↓reduceIte]
      rfl
    | cons a l ih =>
      rw [List.nodup_cons] at hl
      rw [List.map_cons, List.prod_cons, ih hl.2]
      by_cases hwa : w a = 1
      · rw [if_pos hwa, mul_zero_w, C2G.ext_iff]
        refine ⟨rfl, funext fun t => ?_⟩
        simp only [Pi.add_apply, basisW, List.mem_cons]
        by_cases hta : t = a
        · subst hta
          simp [hl.1, hwa]
        · simp [hta]
      · rw [if_neg hwa, one_mul, C2G.ext_iff]
        refine ⟨rfl, funext fun t => ?_⟩
        simp only [List.mem_cons]
        by_cases hta : t = a
        · subst hta
          have hwa0 : w t = 0 := by
            generalize hz : w t = z at hwa ⊢
            fin_cases z
            · rfl
            · exact absurd rfl hwa
          simp [hl.1, hwa0]
        · simp [hta]
  rw [haux (List.finRange k) (List.nodup_finRange k), C2G.ext_iff]
  exact ⟨rfl, funext fun t => by simp [List.mem_finRange]⟩

private def centralElem2 (H : Type*) [Group H] : Subgroup H where
  carrier := {c : H | c ∈ Subgroup.center H ∧ c * c = 1}
  one_mem' := ⟨Subgroup.one_mem _, mul_one 1⟩
  mul_mem' {a b} ha hb := by
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_⟩
    have hba : b * a = a * b := Subgroup.mem_center_iff.mp ha.1 b
    calc
      a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha.2, hb.2, mul_one]
  inv_mem' {a} ha := by
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.2
    rw [hinv]
    exact ha

private instance centralElem2_normal (H : Type*) [Group H] : (centralElem2 H).Normal where
  conj_mem n hn g := by
    have hgn : g * n = n * g := Subgroup.mem_center_iff.mp hn.1 g
    have hconj : g * n * g⁻¹ = n := by rw [hgn, mul_inv_cancel_right]
    rw [hconj]
    exact hn

private lemma zero_w_mem_centralElem2 {d k : ℕ} (B : Param d k) (w : Fin k → ZMod 2) :
    (⟨0, w⟩ : C2G B) ∈ centralElem2 (C2G B) := by
  refine ⟨Subgroup.mem_center_iff.mpr fun x => ?_, ?_⟩
  · change (⟨x.v + 0, x.w + w + beta B x.v 0⟩ : C2G B) = ⟨0 + x.v, w + x.w + beta B 0 x.v⟩
    rw [C2G.ext_iff]
    simp [beta_zero_left, beta_zero_right, add_comm]
  · rw [mul_zero_w, vec_add_self]
    rfl

private lemma map_mem_centralElem2 {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    {x : G} (hx : x ∈ centralElem2 G) : φ x ∈ centralElem2 H := by
  refine ⟨Subgroup.mem_center_iff.mpr fun y => ?_, ?_⟩
  · have h := Subgroup.mem_center_iff.mp hx.1 (φ.symm y)
    have h' := congrArg φ h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  · rw [← map_mul, hx.2, map_one]

private lemma sq_shift_centralElem2 {H : Type*} [Group H] (x : H) {c : H}
    (hc : c ∈ centralElem2 H) : (x * c) * (x * c) = x * x := by
  have hcx : x * c = c * x := Subgroup.mem_center_iff.mp hc.1 x
  calc
    x * c * (x * c) = x * (c * x) * c := by group
    _ = x * (x * c) * c := by rw [← hcx]
    _ = x * x * (c * c) := by group
    _ = x * x := by rw [hc.2, mul_one]

private lemma comm_shift_centralElem2 {H : Type*} [Group H] (x y : H) {c₁ c₂ : H}
    (hc₁ : c₁ ∈ centralElem2 H) (hc₂ : c₂ ∈ centralElem2 H) :
    ((y * c₂) * (x * c₁))⁻¹ * ((x * c₁) * (y * c₂)) = (y * x)⁻¹ * (x * y) := by
  rw [inv_mul_eq_iff_eq_mul]
  have h1 : ∀ z : H, z * c₁ = c₁ * z := fun z => Subgroup.mem_center_iff.mp hc₁.1 z
  have h2 : ∀ z : H, z * c₂ = c₂ * z := fun z => Subgroup.mem_center_iff.mp hc₂.1 z
  have hprod1 : (y * c₂) * (x * c₁) = (c₂ * c₁) * (y * x) := by
    calc
      (y * c₂) * (x * c₁) = (c₂ * y) * (c₁ * x) := by rw [h2 y, h1 x]
      _ = c₂ * (y * c₁) * x := by group
      _ = c₂ * (c₁ * y) * x := by rw [h1 y]
      _ = (c₂ * c₁) * (y * x) := by group
  have hprod2 : (x * c₁) * (y * c₂) = (c₂ * c₁) * (x * y) := by
    calc
      (x * c₁) * (y * c₂) = (c₁ * x) * (c₂ * y) := by rw [h1 x, h2 y]
      _ = c₁ * (x * c₂) * y := by group
      _ = c₁ * (c₂ * x) * y := by rw [h2 x]
      _ = (c₁ * c₂) * (x * y) := by group
      _ = (c₂ * c₁) * (x * y) := by rw [← h2 c₁]
  rw [hprod1, hprod2]
  group

open scoped Classical in
private lemma fiber_card_le {d k : ℕ} (hkd : k ≤ d) (H : FiniteGrp.{0})
    (hHcard : Nat.card H = 2 ^ (d + k)) :
    (Finset.univ.filter fun B : Param d k => Nonempty (C2G B ≃* H)).card ≤
      2 ^ (d ^ 2 + k ^ 2) := by
  set F : Finset (Param d k) := Finset.univ.filter fun B : Param d k => Nonempty (C2G B ≃* H)
  by_cases hne : F.Nonempty
  · obtain ⟨B₀, hB₀⟩ := hne
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hB₀
    obtain ⟨φ₀⟩ := hB₀
    let A : Subgroup H := centralElem2 H
    have hA_inj : Function.Injective (fun w : Fin k → ZMod 2 =>
        (⟨φ₀ ⟨0, w⟩, map_mem_centralElem2 φ₀ (zero_w_mem_centralElem2 B₀ w)⟩ : A)) := by
      intro w₁ w₂ h
      have h' : φ₀ ⟨0, w₁⟩ = φ₀ ⟨0, w₂⟩ := congrArg Subtype.val h
      have h'' := φ₀.injective h'
      exact (C2G.ext_iff.mp h'').2
    have h2k_le_A : 2 ^ k ≤ Nat.card A := by
      have hc := Nat.card_le_card_of_injective _ hA_inj
      have hw : Nat.card (Fin k → ZMod 2) = 2 ^ k := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      rwa [hw] at hc
    have hLagrange : Nat.card (H ⧸ A) * Nat.card A = 2 ^ (d + k) := by
      rw [← hHcard]
      have hidx := Subgroup.card_mul_index A
      rw [Subgroup.index_eq_card] at hidx
      rw [mul_comm]
      exact hidx
    have hq_le : Nat.card (H ⧸ A) ≤ 2 ^ d := by
      have hmul : Nat.card (H ⧸ A) * 2 ^ k ≤ 2 ^ d * 2 ^ k := by
        calc
          Nat.card (H ⧸ A) * 2 ^ k ≤ Nat.card (H ⧸ A) * Nat.card A :=
            Nat.mul_le_mul_left _ h2k_le_A
          _ = 2 ^ (d + k) := hLagrange
          _ = 2 ^ d * 2 ^ k := pow_add 2 d k
      exact Nat.le_of_mul_le_mul_right hmul (by positivity)
    let _ : Fintype H := Fintype.ofFinite H
    let _ : Fintype A := Fintype.ofFinite A
    let _ : Fintype (H ⧸ A) := Fintype.ofFinite (H ⧸ A)
    let enc (x : F) : (Fin d → H ⧸ A) × (Fin k → A) :=
      let φ : C2G x.1 ≃* H := (Finset.mem_filter.mp x.2).2.some
      (fun i => QuotientGroup.mk (φ ⟨basisV d i, 0⟩),
       fun r => ⟨φ ⟨0, basisW k r⟩, map_mem_centralElem2 φ (zero_w_mem_centralElem2 x.1 _)⟩)
    have henc_inj : Function.Injective enc := by
      intro x₁ x₂ heq
      apply Subtype.ext
      set φ₁ : C2G x₁.1 ≃* H := (Finset.mem_filter.mp x₁.2).2.some
      set φ₂ : C2G x₂.1 ≃* H := (Finset.mem_filter.mp x₂.2).2.some
      have hv_eq : ∀ i : Fin d,
          (QuotientGroup.mk (φ₁ ⟨basisV d i, 0⟩) : H ⧸ A) =
            QuotientGroup.mk (φ₂ ⟨basisV d i, 0⟩) :=
        fun i => congrFun (congrArg Prod.fst heq) i
      have hw_basis : ∀ r : Fin k, φ₁ ⟨0, basisW k r⟩ = φ₂ ⟨0, basisW k r⟩ :=
        fun r => congrArg Subtype.val (congrFun (congrArg Prod.snd heq) r)
      have hw_all : ∀ w : Fin k → ZMod 2, φ₁ ⟨0, w⟩ = φ₂ ⟨0, w⟩ := by
        intro w
        rw [zero_w_eq_list_prod x₁.1 w, zero_w_eq_list_prod x₂.1 w, map_list_prod, map_list_prod]
        congr 1
        simp only [List.map_map]
        refine List.map_congr_left fun r _ => ?_
        dsimp only [Function.comp_apply]
        by_cases hwr : w r = 1
        · rw [if_pos hwr, if_pos hwr, hw_basis r]
        · rw [if_neg hwr, if_neg hwr, map_one, map_one]
      have hshift : ∀ i : Fin d, ∃ c ∈ A, φ₂ ⟨basisV d i, 0⟩ = φ₁ ⟨basisV d i, 0⟩ * c := by
        intro i
        have hq := QuotientGroup.eq.mp (hv_eq i)
        refine ⟨(φ₁ ⟨basisV d i, 0⟩)⁻¹ * φ₂ ⟨basisV d i, 0⟩, hq, ?_⟩
        group
      funext p
      rcases p with ⟨⟨i, j⟩, hij⟩
      dsimp only at hij
      have hphi_eq : φ₁ ⟨0, x₁.1 ⟨(i, j), hij⟩⟩ = φ₁ ⟨0, x₂.1 ⟨(i, j), hij⟩⟩ := by
        rw [hw_all (x₂.1 ⟨(i, j), hij⟩)]
        rcases eq_or_lt_of_le hij with rfl | hlt
        · obtain ⟨c, hc, hce⟩ := hshift i
          rw [← sq_basisV x₁.1 i, ← sq_basisV x₂.1 i, map_mul, map_mul, hce,
            sq_shift_centralElem2 _ hc]
        · obtain ⟨c₁, hc₁, hce₁⟩ := hshift i
          obtain ⟨c₂, hc₂, hce₂⟩ := hshift j
          rw [← comm_basisV x₁.1 hlt, ← comm_basisV x₂.1 hlt,
            map_mul, map_inv, map_mul, map_mul,
            map_mul, map_inv, map_mul, map_mul,
            hce₁, hce₂, comm_shift_centralElem2 _ _ hc₁ hc₂]
      exact (C2G.ext_iff.mp (φ₁.injective hphi_eq)).2
    have hcard_le : F.card ≤ Nat.card ((Fin d → H ⧸ A) × (Fin k → A)) := by
      have h := Nat.card_le_card_of_injective enc henc_inj
      rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at h
    have htarget : Nat.card ((Fin d → H ⧸ A) × (Fin k → A)) ≤ 2 ^ (d ^ 2 + k ^ 2) := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin]
      set q := Nat.card (H ⧸ A)
      set a := Nat.card A
      have hdecomp : q ^ d * a ^ k = q ^ (d - k) * (q * a) ^ k := by
        rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hkd]
      rw [hdecomp, hLagrange]
      calc
        q ^ (d - k) * (2 ^ (d + k)) ^ k
            ≤ (2 ^ d) ^ (d - k) * (2 ^ (d + k)) ^ k :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hq_le _)
        _ = 2 ^ (d * (d - k) + (d + k) * k) := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
        _ = 2 ^ (d ^ 2 + k ^ 2) := by
          congr 1
          zify [hkd]
          ring
    exact hcard_le.trans htarget
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

private lemma exp_ineq (m : ℕ) (hm : 3 ≤ m) :
    let k := (m + 2) / 3
    let d := m - k
    2 * m ^ 3 + 27 * (d ^ 2 + k ^ 2) ≤ 27 * (k * (d * (d + 1) / 2)) + 12 * m ^ 2 := by
  intro k d
  set q := m / 3
  set r := m % 3
  have hm_eq : m = 3 * q + r := (Nat.div_add_mod m 3).symm
  have hr : r < 3 := Nat.mod_lt m (by decide)
  have hq : 1 ≤ q := by omega
  interval_cases r
  · have hk : k = q := by dsimp [k]; omega
    have hd : d = 2 * q := by dsimp [d]; omega
    have htri : d * (d + 1) / 2 = q * (2 * q + 1) := by
      rw [hd]
      have : 2 * q * (2 * q + 1) = 2 * (q * (2 * q + 1)) := by ring
      omega
    rw [htri, hm_eq, hk, hd]
    nlinarith
  · have hk : k = q + 1 := by dsimp [k]; omega
    have hd : d = 2 * q := by dsimp [d]; omega
    have htri : d * (d + 1) / 2 = q * (2 * q + 1) := by
      rw [hd]
      have : 2 * q * (2 * q + 1) = 2 * (q * (2 * q + 1)) := by ring
      omega
    rw [htri, hm_eq, hk, hd]
    nlinarith
  · have hk : k = q + 1 := by dsimp [k]; omega
    have hd : d = 2 * q + 1 := by dsimp [d]; omega
    have htri : d * (d + 1) / 2 = (2 * q + 1) * (q + 1) := by
      rw [hd]
      have : (2 * q + 1) * (2 * q + 1 + 1) = 2 * ((2 * q + 1) * (q + 1)) := by ring
      omega
    rw [htri, hm_eq, hk, hd]
    nlinarith

theorem H3_proof : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1.H3 := by
  classical
  intro m hm
  let k := (m + 2) / 3
  let d := m - k
  have hdk_add : d + k = m := by dsimp [k, d]; omega
  have hkd : k ≤ d := by dsimp [k, d]; omega
  let S : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = 2 ^ m}
  let OrderClasses := ↥S
  let rep (i : OrderClasses) : FiniteGrp.{0} := i.property.choose
  have rep_spec (i : OrderClasses) :
      Nat.card (rep i) = 2 ^ m ∧
        Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep i) = i.val :=
    i.property.choose_spec
  have hS_fin : S.Finite := by
    change Finite OrderClasses
    let _ (i : OrderClasses) : Fintype (rep i) := Fintype.ofFinite _
    let e (i : OrderClasses) : rep i ≃ Fin (2 ^ m) :=
      Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, (rep_spec i).1])
    let tbl (i : OrderClasses) (a b : Fin (2 ^ m)) := e i ((e i).symm a * (e i).symm b)
    apply Finite.of_injective tbl
    intro i j h
    let u := (e i).trans (e j).symm
    have hequiv : rep i ≃* rep j :=
      { toEquiv := u
        map_mul' := fun x y => by
          apply (e j).injective
          have hh := congrFun (congrFun h (e i x)) (e i y)
          simpa [tbl, u] using hh }
    apply Subtype.ext
    rw [← (rep_spec i).2, ← (rep_spec j).2]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (rep i).toGrp) (Y := (rep j).toGrp) hequiv)⟩
  let _ : Fintype OrderClasses := hS_fin.fintype
  have hg_eq : g (2 ^ m) = Fintype.card OrderClasses := by
    change S.ncard = Fintype.card ↥S
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  let cls (B : Param d k) : OrderClasses :=
    ⟨Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (FiniteGrp.of (C2G B)),
      FiniteGrp.of (C2G B), by change Nat.card (C2G B) = 2 ^ m; rw [card_C2G, hdk_add], rfl⟩
  have hcount : Fintype.card (Param d k) ≤ Fintype.card OrderClasses * 2 ^ (d ^ 2 + k ^ 2) := by
    calc
      Fintype.card (Param d k)
          = (Finset.univ : Finset (Param d k)).card := rfl
      _ = ∑ i : OrderClasses, (Finset.univ.filter fun B : Param d k => cls B = i).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := cls) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)]
      _ ≤ ∑ i : OrderClasses, 2 ^ (d ^ 2 + k ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hsub : (Finset.univ.filter fun B : Param d k => cls B = i) ⊆
              (Finset.univ.filter fun B : Param d k => Nonempty (C2G B ≃* rep i)) := by
            intro B hB
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
            have hq : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (FiniteGrp.of (C2G B)) =
                Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep i) := by
              have hval := congrArg Subtype.val hB
              exact hval.trans (rep_spec i).2.symm
            obtain ⟨v⟩ := Quotient.exact hq
            exact ⟨Iso.groupIsoToMulEquiv ((inducedFunctor FiniteGrp.toGrp).mapIso v)⟩
          exact (Finset.card_le_card hsub).trans
            (fiber_card_le hkd (rep i) (by rw [(rep_spec i).1, hdk_add]))
      _ = Fintype.card OrderClasses * 2 ^ (d ^ 2 + k ^ 2) := by
          simp
  rw [card_param, ← hg_eq] at hcount
  have hpow27 : 2 ^ (27 * (k * (d * (d + 1) / 2))) ≤
      g (2 ^ m) ^ 27 * 2 ^ (27 * (d ^ 2 + k ^ 2)) := by
    calc
      2 ^ (27 * (k * (d * (d + 1) / 2)))
          = (2 ^ (k * (d * (d + 1) / 2))) ^ 27 := by rw [← pow_mul, mul_comm]
      _ ≤ (g (2 ^ m) * 2 ^ (d ^ 2 + k ^ 2)) ^ 27 := Nat.pow_le_pow_left hcount 27
      _ = g (2 ^ m) ^ 27 * 2 ^ (27 * (d ^ 2 + k ^ 2)) := by
          rw [mul_pow, ← pow_mul, mul_comm (d ^ 2 + k ^ 2) 27]
  have hexp := exp_ineq m hm
  have hmul : 2 ^ (2 * m ^ 3) * 2 ^ (27 * (d ^ 2 + k ^ 2)) ≤
      (g (2 ^ m) ^ 27 * 2 ^ (12 * m ^ 2)) * 2 ^ (27 * (d ^ 2 + k ^ 2)) := by
    calc
      2 ^ (2 * m ^ 3) * 2 ^ (27 * (d ^ 2 + k ^ 2))
          = 2 ^ (2 * m ^ 3 + 27 * (d ^ 2 + k ^ 2)) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (27 * (k * (d * (d + 1) / 2)) + 12 * m ^ 2) :=
          Nat.pow_le_pow_right (by decide) hexp
      _ = 2 ^ (27 * (k * (d * (d + 1) / 2))) * 2 ^ (12 * m ^ 2) := pow_add _ _ _
      _ ≤ (g (2 ^ m) ^ 27 * 2 ^ (27 * (d ^ 2 + k ^ 2))) * 2 ^ (12 * m ^ 2) :=
          Nat.mul_le_mul_right _ hpow27
      _ = (g (2 ^ m) ^ 27 * 2 ^ (12 * m ^ 2)) * 2 ^ (27 * (d ^ 2 + k ^ 2)) := by ring
  exact Nat.le_of_mul_le_mul_right hmul (by positivity)

end Erdos1160H3Proof

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1.H3 :=
  Erdos1160H3Proof.H3_proof
