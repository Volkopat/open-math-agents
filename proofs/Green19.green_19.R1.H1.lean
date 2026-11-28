import OMAReductions.R_Green19_green_19_R1
import Mathlib

-- Step Green19.green_19.R1.H1: hypothesis H1 of reduction Green19.green_19.R1
-- Credit: @peyton-thalman

/-!
# Popular corners from finite triforce bounds (Mandache 2021)

Formalization of `Green19.green_19.R1.H1`: lifting a finite unweighted triforce lower bound
to popular corners in `𝔽₂ n × 𝔽₂ n` via deterministic cyclic blow-up and Mandache's
dual-energy regular boxing lemma.
-/

open Finset Filter Real Topology
open scoped Classical BigOperators

namespace Green19H1

/- Section 1: Fractional Triforce Transfer -/

lemma card_filter_mod_add_lt {L : ℕ} (hL : 0 < L) (s k : ℕ) (hk : k ≤ L) :
    ((univ : Finset (Fin L)).filter (fun r : Fin L => (s + r.val) % L < k)).card = k := by
  have hbij :
      ((univ : Finset (Fin L)).filter (fun r : Fin L => (s + r.val) % L < k)).card =
      ((univ : Finset (Fin L)).filter (fun t : Fin L => t.val < k)).card := by
    refine Finset.card_bij (fun r _ => ⟨(s + r.val) % L, Nat.mod_lt _ hL⟩) ?_ ?_ ?_
    · intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr ⊢
      exact hr
    · intro r₁ _ r₂ _ heq
      have hmod : (s + r₁.val) % L = (s + r₂.val) % L := congrArg Fin.val heq
      have h1 : (s + r₁.val) % L = (s % L + r₁.val) % L := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt r₁.isLt]
      have h2 : (s + r₂.val) % L = (s % L + r₂.val) % L := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt r₂.isLt]
      rw [h1, h2] at hmod
      have hlt1 := r₁.isLt
      have hlt2 := r₂.isLt
      have hs := Nat.mod_lt s hL
      have hmod_step : ∀ a b : ℕ, a < L → b < L → (a + b) % L = if a + b < L then a + b else a + b - L := by
        intro a b ha hb
        split_ifs with hlt
        · exact Nat.mod_eq_of_lt hlt
        · rw [Nat.mod_eq_sub_mod (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
      rw [hmod_step (s % L) r₁.val hs hlt1, hmod_step (s % L) r₂.val hs hlt2] at hmod
      apply Fin.ext
      split_ifs at hmod <;> omega
    · intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht
      let rval := (t.val + (L - s % L)) % L
      have hsum : (s + rval) % L = t.val := by
        dsimp only [rval]
        have hs := Nat.mod_lt s hL
        have h1 : (s + (t.val + (L - s % L)) % L) % L = (s % L + (t.val + (L - s % L))) % L := by
          simp only [Nat.add_mod, Nat.mod_mod]
        rw [h1]
        have h2 : s % L + (t.val + (L - s % L)) = t.val + L := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt t.isLt]
      refine ⟨⟨rval, Nat.mod_lt _ hL⟩, ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        rw [hsum]
        exact ht
      · exact Fin.ext hsum
  rw [hbij]
  have hbij2 : ((univ : Finset (Fin L)).filter (fun t : Fin L => t.val < k)).card = (Finset.range k).card := by
    refine Finset.card_bij (fun t _ => t.val) ?_ ?_ ?_
    · intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht
      exact Finset.mem_range.mpr ht
    · intro t₁ _ t₂ _ h; exact Fin.ext h
    · intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      exact ⟨⟨i, lt_of_lt_of_le hik hk⟩, by simp [hik], rfl⟩
  rw [hbij2, Finset.card_range]

lemma fractional_triforce_fin {c b : ℝ} (hc : 1 ≤ c) (hb : 0 < b)
    (htrif : ∀ q : ℕ, 0 < q → ∀ H : Finset (Fin q × Fin q × Fin q),
      let xy (e : Fin q × Fin q × Fin q) := (e.1, e.2.1)
      let xz (e : Fin q × Fin q × Fin q) := (e.1, e.2.2)
      let yz (e : Fin q × Fin q × Fin q) := (e.2.1, e.2.2)
      let deg (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (x : Fin q × Fin q) : ℝ :=
        (H.filter (fun e => proj e = x)).card
      let density : ℝ := H.card / (q : ℝ) ^ 3
      let triforce := (∑ e : Fin q × Fin q × Fin q,
        deg xy (xy e) * deg xz (xz e) * deg yz (yz e)) / (q : ℝ) ^ 6
      b * density ^ c ≤ triforce)
    {Q : ℕ} (hQ : 0 < Q)
    (F : Fin Q × Fin Q × Fin Q → ℝ)
    (h0 : ∀ e, 0 ≤ F e) (h1 : ∀ e, F e ≤ 1) :
    let mXY (x y : Fin Q) : ℝ := (∑ z : Fin Q, F (x, y, z)) / (Q : ℝ)
    let mXZ (x z : Fin Q) : ℝ := (∑ y : Fin Q, F (x, y, z)) / (Q : ℝ)
    let mYZ (y z : Fin Q) : ℝ := (∑ x : Fin Q, F (x, y, z)) / (Q : ℝ)
    let μ : ℝ := (∑ e : Fin Q × Fin Q × Fin Q, F e) / (Q : ℝ) ^ 3
    b * μ ^ c ≤
      (∑ e : Fin Q × Fin Q × Fin Q, mXY e.1 e.2.1 * mXZ e.1 e.2.2 * mYZ e.2.1 e.2.2) / (Q : ℝ) ^ 3 := by
  intro mXY mXZ mYZ μ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  let FL (L : ℕ) (e : Fin Q × Fin Q × Fin Q) : ℝ := (Nat.floor ((L : ℝ) * F e) : ℝ) / (L : ℝ)
  have hFL_bound : ∀ L : ℕ, 0 < L →
      let mXY_L (x y : Fin Q) : ℝ := (∑ z : Fin Q, FL L (x, y, z)) / (Q : ℝ)
      let mXZ_L (x z : Fin Q) : ℝ := (∑ y : Fin Q, FL L (x, y, z)) / (Q : ℝ)
      let mYZ_L (y z : Fin Q) : ℝ := (∑ x : Fin Q, FL L (x, y, z)) / (Q : ℝ)
      let μ_L : ℝ := (∑ e : Fin Q × Fin Q × Fin Q, FL L e) / (Q : ℝ) ^ 3
      b * μ_L ^ c ≤
        (∑ e : Fin Q × Fin Q × Fin Q, mXY_L e.1 e.2.1 * mXZ_L e.1 e.2.2 * mYZ_L e.2.1 e.2.2) / (Q : ℝ) ^ 3 := by
    intro L hL mXY_L mXZ_L mYZ_L μ_L
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    let q := Q * L
    have hq : 0 < q := Nat.mul_pos hQ hL
    let eql : Fin Q × Fin L ≃ Fin q := finProdFinEquiv
    let P3 : (Fin Q × Fin L) × (Fin Q × Fin L) × (Fin Q × Fin L) ≃ Fin q × Fin q × Fin q :=
      Equiv.prodCongr eql (Equiv.prodCongr eql eql)
    let H0 : Finset ((Fin Q × Fin L) × (Fin Q × Fin L) × (Fin Q × Fin L)) :=
      univ.filter (fun t =>
        (t.1.2.val + t.2.1.2.val + t.2.2.2.val) % L < Nat.floor ((L : ℝ) * F (t.1.1, t.2.1.1, t.2.2.1)))
    let H : Finset (Fin q × Fin q × Fin q) := H0.map P3.toEmbedding
    have hk_le : ∀ x y z : Fin Q, Nat.floor ((L : ℝ) * F (x, y, z)) ≤ L := by
      intro x y z
      exact Nat.floor_le_of_le (by nlinarith [h1 (x, y, z)])
    have hspec := htrif q hq H
    dsimp only at hspec
    -- Compute degrees in H via H0
    have hdegXY : ∀ x y : Fin Q, ∀ a b' : Fin L,
        ((H.filter (fun e => (e.1, e.2.1) = (eql (x, a), eql (y, b')))).card : ℝ) =
          (L : ℝ) * (Q : ℝ) * mXY_L x y := by
      intro x y a b'
      have hcard : (H.filter (fun e => (e.1, e.2.1) = (eql (x, a), eql (y, b')))).card =
          ∑ z : Fin Q, Nat.floor ((L : ℝ) * F (x, y, z)) := by
        have h1' : (H.filter (fun e => (e.1, e.2.1) = (eql (x, a), eql (y, b')))).card =
            (H0.filter (fun t => t.1 = (x, a) ∧ t.2.1 = (y, b'))).card := by
          refine Finset.card_bij (fun e _ => P3.symm e) ?_ ?_ ?_
          · intro e he
            simp only [mem_filter, H, Finset.mem_map] at he ⊢
            obtain ⟨⟨t, ht, rfl⟩, hpair⟩ := he
            simp only [P3, Equiv.coe_toEmbedding, Equiv.symm_apply_apply, Prod.mk.injEq] at hpair ⊢
            exact ⟨ht, eql.injective hpair.1, eql.injective hpair.2⟩
          · intro e₁ _ e₂ _ h; exact P3.symm.injective h
          · intro t ht
            simp only [mem_filter] at ht
            refine ⟨P3 t, ?_, P3.symm_apply_apply t⟩
            simp only [mem_filter, H, Finset.mem_map]
            exact ⟨⟨t, ht.1, rfl⟩, Prod.ext (congrArg eql ht.2.1) (congrArg eql ht.2.2)⟩
        rw [h1']
        have h2' : (H0.filter (fun t => t.1 = (x, a) ∧ t.2.1 = (y, b'))).card =
            ((univ : Finset (Fin Q × Fin L)).filter (fun p =>
              (a.val + b'.val + p.2.val) % L < Nat.floor ((L : ℝ) * F (x, y, p.1)))).card := by
          refine Finset.card_bij (fun t _ => t.2.2) ?_ ?_ ?_
          · intro t ht
            simp only [mem_filter, H0, mem_univ, true_and] at ht ⊢
            obtain ⟨hcond, ht1, ht2⟩ := ht
            rw [ht1, ht2] at hcond
            exact hcond
          · intro t₁ ht₁ t₂ ht₂ h
            simp only [mem_filter] at ht₁ ht₂
            exact Prod.ext (ht₁.2.1.trans ht₂.2.1.symm) (Prod.ext (ht₁.2.2.trans ht₂.2.2.symm) h)
          · intro p hp
            simp only [mem_filter, mem_univ, true_and] at hp
            exact ⟨((x, a), (y, b'), p), by simp [H0, hp], rfl⟩
        rw [h2', ← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.card_filter]
        exact card_filter_mod_add_lt hL (a.val + b'.val) _ (hk_le x y z)
      rw [hcard]
      dsimp only [mXY_L, FL]
      rw [← Finset.sum_div]
      push_cast
      field_simp
    have hdegXZ : ∀ x z : Fin Q, ∀ a r : Fin L,
        ((H.filter (fun e => (e.1, e.2.2) = (eql (x, a), eql (z, r)))).card : ℝ) =
          (L : ℝ) * (Q : ℝ) * mXZ_L x z := by
      intro x z a r
      have hcard : (H.filter (fun e => (e.1, e.2.2) = (eql (x, a), eql (z, r)))).card =
          ∑ y : Fin Q, Nat.floor ((L : ℝ) * F (x, y, z)) := by
        have h1' : (H.filter (fun e => (e.1, e.2.2) = (eql (x, a), eql (z, r)))).card =
            (H0.filter (fun t => t.1 = (x, a) ∧ t.2.2 = (z, r))).card := by
          refine Finset.card_bij (fun e _ => P3.symm e) ?_ ?_ ?_
          · intro e he
            simp only [mem_filter, H, Finset.mem_map] at he ⊢
            obtain ⟨⟨t, ht, rfl⟩, hpair⟩ := he
            simp only [P3, Equiv.coe_toEmbedding, Equiv.symm_apply_apply, Prod.mk.injEq] at hpair ⊢
            exact ⟨ht, eql.injective hpair.1, eql.injective hpair.2⟩
          · intro e₁ _ e₂ _ h; exact P3.symm.injective h
          · intro t ht
            simp only [mem_filter] at ht
            refine ⟨P3 t, ?_, P3.symm_apply_apply t⟩
            simp only [mem_filter, H, Finset.mem_map]
            exact ⟨⟨t, ht.1, rfl⟩, Prod.ext (congrArg eql ht.2.1) (congrArg eql ht.2.2)⟩
        rw [h1']
        have h2' : (H0.filter (fun t => t.1 = (x, a) ∧ t.2.2 = (z, r))).card =
            ((univ : Finset (Fin Q × Fin L)).filter (fun p =>
              (a.val + r.val + p.2.val) % L < Nat.floor ((L : ℝ) * F (x, p.1, z)))).card := by
          refine Finset.card_bij (fun t _ => t.2.1) ?_ ?_ ?_
          · intro t ht
            simp only [mem_filter, H0, mem_univ, true_and] at ht ⊢
            obtain ⟨hcond, ht1, ht2⟩ := ht
            rw [ht1, ht2] at hcond
            have hadd : a.val + t.2.1.2.val + r.val = a.val + r.val + t.2.1.2.val := by omega
            rwa [hadd] at hcond
          · intro t₁ ht₁ t₂ ht₂ h
            simp only [mem_filter] at ht₁ ht₂
            exact Prod.ext (ht₁.2.1.trans ht₂.2.1.symm) (Prod.ext h (ht₁.2.2.trans ht₂.2.2.symm))
          · intro p hp
            simp only [mem_filter, mem_univ, true_and] at hp
            refine ⟨((x, a), p, (z, r)), ?_, rfl⟩
            simp only [mem_filter, H0, mem_univ, true_and]
            have hadd : a.val + p.2.val + r.val = a.val + r.val + p.2.val := by omega
            exact ⟨hadd ▸ hp, trivial⟩
        rw [h2', ← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.card_filter]
        exact card_filter_mod_add_lt hL (a.val + r.val) _ (hk_le x y z)
      rw [hcard]
      dsimp only [mXZ_L, FL]
      rw [← Finset.sum_div]
      push_cast
      field_simp
    have hdegYZ : ∀ y z : Fin Q, ∀ b' r : Fin L,
        ((H.filter (fun e => (e.2.1, e.2.2) = (eql (y, b'), eql (z, r)))).card : ℝ) =
          (L : ℝ) * (Q : ℝ) * mYZ_L y z := by
      intro y z b' r
      have hcard : (H.filter (fun e => (e.2.1, e.2.2) = (eql (y, b'), eql (z, r)))).card =
          ∑ x : Fin Q, Nat.floor ((L : ℝ) * F (x, y, z)) := by
        have h1' : (H.filter (fun e => (e.2.1, e.2.2) = (eql (y, b'), eql (z, r)))).card =
            (H0.filter (fun t => t.2.1 = (y, b') ∧ t.2.2 = (z, r))).card := by
          refine Finset.card_bij (fun e _ => P3.symm e) ?_ ?_ ?_
          · intro e he
            simp only [mem_filter, H, Finset.mem_map] at he ⊢
            obtain ⟨⟨t, ht, rfl⟩, hpair⟩ := he
            simp only [P3, Equiv.coe_toEmbedding, Equiv.symm_apply_apply, Prod.mk.injEq] at hpair ⊢
            exact ⟨ht, eql.injective hpair.1, eql.injective hpair.2⟩
          · intro e₁ _ e₂ _ h; exact P3.symm.injective h
          · intro t ht
            simp only [mem_filter] at ht
            refine ⟨P3 t, ?_, P3.symm_apply_apply t⟩
            simp only [mem_filter, H, Finset.mem_map]
            exact ⟨⟨t, ht.1, rfl⟩, Prod.ext (congrArg eql ht.2.1) (congrArg eql ht.2.2)⟩
        rw [h1']
        have h2' : (H0.filter (fun t => t.2.1 = (y, b') ∧ t.2.2 = (z, r))).card =
            ((univ : Finset (Fin Q × Fin L)).filter (fun p =>
              (b'.val + r.val + p.2.val) % L < Nat.floor ((L : ℝ) * F (p.1, y, z)))).card := by
          refine Finset.card_bij (fun t _ => t.1) ?_ ?_ ?_
          · intro t ht
            simp only [mem_filter, H0, mem_univ, true_and] at ht ⊢
            obtain ⟨hcond, ht1, ht2⟩ := ht
            rw [ht1, ht2] at hcond
            have hadd : t.1.2.val + b'.val + r.val = b'.val + r.val + t.1.2.val := by omega
            rwa [hadd] at hcond
          · intro t₁ ht₁ t₂ ht₂ h
            simp only [mem_filter] at ht₁ ht₂
            exact Prod.ext h (Prod.ext (ht₁.2.1.trans ht₂.2.1.symm) (ht₁.2.2.trans ht₂.2.2.symm))
          · intro p hp
            simp only [mem_filter, mem_univ, true_and] at hp
            refine ⟨(p, (y, b'), (z, r)), ?_, rfl⟩
            simp only [mem_filter, H0, mem_univ, true_and]
            have hadd : p.2.val + b'.val + r.val = b'.val + r.val + p.2.val := by omega
            exact ⟨hadd ▸ hp, trivial⟩
        rw [h2', ← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.card_filter]
        exact card_filter_mod_add_lt hL (b'.val + r.val) _ (hk_le x y z)
      rw [hcard]
      dsimp only [mYZ_L, FL]
      rw [← Finset.sum_div]
      push_cast
      field_simp
    -- Density of H equals μ_L
    have hdens : (H.card : ℝ) / (q : ℝ) ^ 3 = μ_L := by
      have hHcard : H.card = L ^ 2 * ∑ e : Fin Q × Fin Q × Fin Q, Nat.floor ((L : ℝ) * F e) := by
        rw [Finset.card_map]
        have hstep : H0.card =
            ∑ x : Fin Q, ∑ y : Fin Q, ∑ z : Fin Q, ∑ a : Fin L, ∑ b' : Fin L,
              ((univ : Finset (Fin L)).filter (fun r : Fin L =>
                (a.val + b'.val + r.val) % L < Nat.floor ((L : ℝ) * F (x, y, z)))).card := by
          dsimp only [H0]
          rw [Finset.card_filter]
          simp only [Fintype.sum_prod_type]
          rw [Finset.sum_comm]
          -- swap directly via equiv
          have hsum_eq :
              (∑ x : Fin Q, ∑ a : Fin L, ∑ y : Fin Q, ∑ b' : Fin L, ∑ z : Fin Q, ∑ r : Fin L,
                if (a.val + b'.val + r.val) % L < Nat.floor ((L : ℝ) * F (x, y, z)) then 1 else 0) =
              (∑ x : Fin Q, ∑ y : Fin Q, ∑ z : Fin Q, ∑ a : Fin L, ∑ b' : Fin L, ∑ r : Fin L,
                if (a.val + b'.val + r.val) % L < Nat.floor ((L : ℝ) * F (x, y, z)) then 1 else 0) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun y _ => ?_
            trans (∑ a : Fin L, ∑ z : Fin Q, ∑ b' : Fin L, ∑ r : Fin L,
              if (a.val + b'.val + r.val) % L < Nat.floor ((L : ℝ) * F (x, y, z)) then 1 else 0)
            · refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
            · rw [Finset.sum_comm]
          rw [← Finset.sum_comm]
          rw [hsum_eq]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b' _ => (Finset.card_filter _ _).symm
        rw [hstep]
        have hinner : ∀ x y z : Fin Q,
            (∑ a : Fin L, ∑ b' : Fin L,
              ((univ : Finset (Fin L)).filter (fun r : Fin L =>
                (a.val + b'.val + r.val) % L < Nat.floor ((L : ℝ) * F (x, y, z)))).card) =
            L ^ 2 * Nat.floor ((L : ℝ) * F (x, y, z)) := by
          intro x y z
          simp_rw [card_filter_mod_add_lt hL _ _ (hk_le x y z)]
          simp [sq, mul_assoc]
        simp_rw [hinner]
        simp only [Fintype.sum_prod_type, ← Finset.mul_sum]
      rw [hHcard]
      dsimp only [μ_L, FL, q]
      rw [← Finset.sum_div]
      push_cast
      field_simp
    -- Triforce of H equals the L-approximated triforce of F
    have htrif_eq :
        (∑ e : Fin q × Fin q × Fin q,
          ((H.filter (fun f => (f.1, f.2.1) = (e.1, e.2.1))).card : ℝ) *
          ((H.filter (fun f => (f.1, f.2.2) = (e.1, e.2.2))).card : ℝ) *
          ((H.filter (fun f => (f.2.1, f.2.2) = (e.2.1, e.2.2))).card : ℝ)) / (q : ℝ) ^ 6 =
        (∑ e : Fin Q × Fin Q × Fin Q, mXY_L e.1 e.2.1 * mXZ_L e.1 e.2.2 * mYZ_L e.2.1 e.2.2) / (Q : ℝ) ^ 3 := by
      have hreidx :
          (∑ e : Fin q × Fin q × Fin q,
            ((H.filter (fun f => (f.1, f.2.1) = (e.1, e.2.1))).card : ℝ) *
            ((H.filter (fun f => (f.1, f.2.2) = (e.1, e.2.2))).card : ℝ) *
            ((H.filter (fun f => (f.2.1, f.2.2) = (e.2.1, e.2.2))).card : ℝ)) =
          ∑ t : (Fin Q × Fin L) × (Fin Q × Fin L) × (Fin Q × Fin L),
            ((H.filter (fun f => (f.1, f.2.1) = (eql t.1, eql t.2.1))).card : ℝ) *
            ((H.filter (fun f => (f.1, f.2.2) = (eql t.1, eql t.2.2))).card : ℝ) *
            ((H.filter (fun f => (f.2.1, f.2.2) = (eql t.2.1, eql t.2.2))).card : ℝ) := by
        exact (Fintype.sum_equiv P3 _ _ (fun _ => rfl)).symm
      rw [hreidx]
      have hterm : ∀ t : (Fin Q × Fin L) × (Fin Q × Fin L) × (Fin Q × Fin L),
          ((H.filter (fun f => (f.1, f.2.1) = (eql t.1, eql t.2.1))).card : ℝ) *
          ((H.filter (fun f => (f.1, f.2.2) = (eql t.1, eql t.2.2))).card : ℝ) *
          ((H.filter (fun f => (f.2.1, f.2.2) = (eql t.2.1, eql t.2.2))).card : ℝ) =
          (L : ℝ) ^ 3 * (Q : ℝ) ^ 3 * (mXY_L t.1.1 t.2.1.1 * mXZ_L t.1.1 t.2.2.1 * mYZ_L t.2.1.1 t.2.2.1) := by
        rintro ⟨⟨x, a⟩, ⟨y, b'⟩, ⟨z, r⟩⟩
        rw [hdegXY x y a b', hdegXZ x z a r, hdegYZ y z b' r]
        ring
      simp_rw [hterm]
      have hsumL :
          (∑ t : (Fin Q × Fin L) × (Fin Q × Fin L) × (Fin Q × Fin L),
            (L : ℝ) ^ 3 * (Q : ℝ) ^ 3 * (mXY_L t.1.1 t.2.1.1 * mXZ_L t.1.1 t.2.2.1 * mYZ_L t.2.1.1 t.2.2.1)) =
          (L : ℝ) ^ 6 * (Q : ℝ) ^ 3 *
            ∑ e : Fin Q × Fin Q × Fin Q, mXY_L e.1 e.2.1 * mXZ_L e.1 e.2.2 * mYZ_L e.2.1 e.2.2 := by
        simp only [Fintype.sum_prod_type]
        have hswap :
            (∑ x : Fin Q, ∑ a : Fin L, ∑ y : Fin Q, ∑ b' : Fin L, ∑ z : Fin Q, ∑ r : Fin L,
              (L : ℝ) ^ 3 * (Q : ℝ) ^ 3 * (mXY_L x y * mXZ_L x z * mYZ_L y z)) =
            (∑ x : Fin Q, ∑ y : Fin Q, ∑ z : Fin Q,
              (L : ℝ) ^ 6 * (Q : ℝ) ^ 3 * (mXY_L x y * mXZ_L x z * mYZ_L y z)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          trans (∑ a : Fin L, ∑ z : Fin Q, ∑ b' : Fin L, ∑ r : Fin L,
            (L : ℝ) ^ 3 * (Q : ℝ) ^ 3 * (mXY_L x y * mXZ_L x z * mYZ_L y z))
          · refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z _ => ?_
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
        rw [hswap]
        simp only [← Finset.mul_sum]
      rw [hsumL]
      dsimp only [q]
      push_cast
      field_simp
    rw [← hdens, ← htrif_eq]
    exact hspec
  -- Pass to the limit L → ∞
  have hFL_tendsto : ∀ e : Fin Q × Fin Q × Fin Q, Tendsto (fun L : ℕ => FL L e) atTop (𝓝 (F e)) := by
    intro e
    have hlo : ∀ᶠ L : ℕ in atTop, F e - 1 / (L : ℝ) ≤ FL L e := by
      filter_upwards [eventually_gt_atTop 0] with L hL
      have hLr : (0 : ℝ) < L := by exact_mod_cast hL
      dsimp only [FL]
      have hlt := Nat.lt_floor_add_one ((L : ℝ) * F e)
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hLr]
      linarith
    have hhi : ∀ᶠ L : ℕ in atTop, FL L e ≤ F e := by
      filter_upwards [eventually_gt_atTop 0] with L hL
      have hLr : (0 : ℝ) < L := by exact_mod_cast hL
      dsimp only [FL]
      rw [div_le_iff₀ hLr]
      have hnonneg : 0 ≤ (L : ℝ) * F e := mul_nonneg hLr.le (h0 e)
      have := Nat.floor_le hnonneg
      linarith
    have h1div : Tendsto (fun L : ℕ => F e - 1 / (L : ℝ)) atTop (𝓝 (F e)) := by
      have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using tendsto_const_nhds.sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h1div tendsto_const_nhds hlo hhi
  have hμ_tendsto : Tendsto (fun L : ℕ => (∑ e : Fin Q × Fin Q × Fin Q, FL L e) / (Q : ℝ) ^ 3) atTop (𝓝 μ) := by
    exact (tendsto_finsetSum _ fun e _ => hFL_tendsto e).div_const _
  have hlhs_tendsto : Tendsto (fun L : ℕ => b * ((∑ e : Fin Q × Fin Q × Fin Q, FL L e) / (Q : ℝ) ^ 3) ^ c)
      atTop (𝓝 (b * μ ^ c)) := by
    have hcont : Continuous (fun t : ℝ => t ^ c) := Real.continuous_rpow_const (by linarith)
    exact tendsto_const_nhds.mul ((hcont.tendsto μ).comp hμ_tendsto)
  have hmXY_t : ∀ x y : Fin Q, Tendsto (fun L : ℕ => (∑ z : Fin Q, FL L (x, y, z)) / (Q : ℝ)) atTop (𝓝 (mXY x y)) :=
    fun x y => (tendsto_finsetSum _ fun z _ => hFL_tendsto (x, y, z)).div_const _
  have hmXZ_t : ∀ x z : Fin Q, Tendsto (fun L : ℕ => (∑ y : Fin Q, FL L (x, y, z)) / (Q : ℝ)) atTop (𝓝 (mXZ x z)) :=
    fun x z => (tendsto_finsetSum _ fun y _ => hFL_tendsto (x, y, z)).div_const _
  have hmYZ_t : ∀ y z : Fin Q, Tendsto (fun L : ℕ => (∑ x : Fin Q, FL L (x, y, z)) / (Q : ℝ)) atTop (𝓝 (mYZ y z)) :=
    fun y z => (tendsto_finsetSum _ fun x _ => hFL_tendsto (x, y, z)).div_const _
  have hrhs_tendsto :
      Tendsto (fun L : ℕ =>
        (∑ e : Fin Q × Fin Q × Fin Q,
          ((∑ z : Fin Q, FL L (e.1, e.2.1, z)) / (Q : ℝ)) *
          ((∑ y : Fin Q, FL L (e.1, y, e.2.2)) / (Q : ℝ)) *
          ((∑ x : Fin Q, FL L (x, e.2.1, e.2.2)) / (Q : ℝ))) / (Q : ℝ) ^ 3)
        atTop
        (𝓝 ((∑ e : Fin Q × Fin Q × Fin Q, mXY e.1 e.2.1 * mXZ e.1 e.2.2 * mYZ e.2.1 e.2.2) / (Q : ℝ) ^ 3)) := by
    refine (tendsto_finsetSum _ fun e _ => ?_).div_const _
    exact ((hmXY_t e.1 e.2.1).mul (hmXZ_t e.1 e.2.2)).mul (hmYZ_t e.2.1 e.2.2)
  exact le_of_tendsto_of_tendsto' hlhs_tendsto hrhs_tendsto fun L => by
    by_cases hL : 0 < L
    · exact hFL_bound L hL
    · have hL0 : L = 0 := by omega
      subst hL0
      have h0sum : ∀ e, FL 0 e = 0 := fun e => by simp [FL]
      simp only [h0sum, sum_const_zero, zero_div, mul_zero]
      rw [Real.zero_rpow (by linarith)]
      simp

lemma fractional_triforce {c b : ℝ} (hc : 1 ≤ c) (hb : 0 < b)
    (htrif : ∀ q : ℕ, 0 < q → ∀ H : Finset (Fin q × Fin q × Fin q),
      let xy (e : Fin q × Fin q × Fin q) := (e.1, e.2.1)
      let xz (e : Fin q × Fin q × Fin q) := (e.1, e.2.2)
      let yz (e : Fin q × Fin q × Fin q) := (e.2.1, e.2.2)
      let deg (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (x : Fin q × Fin q) : ℝ :=
        (H.filter (fun e => proj e = x)).card
      let density : ℝ := H.card / (q : ℝ) ^ 3
      let triforce := (∑ e : Fin q × Fin q × Fin q,
        deg xy (xy e) * deg xz (xz e) * deg yz (yz e)) / (q : ℝ) ^ 6
      b * density ^ c ≤ triforce)
    {α : Type*} [Fintype α] [Nonempty α]
    (F : α × α × α → ℝ) (h0 : ∀ e, 0 ≤ F e) (h1 : ∀ e, F e ≤ 1) :
    let Q : ℝ := Fintype.card α
    let mXY (x y : α) : ℝ := (∑ z : α, F (x, y, z)) / Q
    let mXZ (x z : α) : ℝ := (∑ y : α, F (x, y, z)) / Q
    let mYZ (y z : α) : ℝ := (∑ x : α, F (x, y, z)) / Q
    let μ : ℝ := (∑ e : α × α × α, F e) / Q ^ 3
    b * μ ^ c ≤
      (∑ e : α × α × α, mXY e.1 e.2.1 * mXZ e.1 e.2.2 * mYZ e.2.1 e.2.2) / Q ^ 3 := by
  intro Q mXY mXZ mYZ μ
  let eA : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let e3 : (α × α × α) ≃ (Fin (Fintype.card α) × Fin (Fintype.card α) × Fin (Fintype.card α)) :=
    Equiv.prodCongr eA (Equiv.prodCongr eA eA)
  let F' : Fin (Fintype.card α) × Fin (Fintype.card α) × Fin (Fintype.card α) → ℝ :=
    fun t => F (e3.symm t)
  have hspec := fractional_triforce_fin hc hb htrif Fintype.card_pos F'
    (fun t => h0 (e3.symm t)) (fun t => h1 (e3.symm t))
  dsimp only at hspec
  have hμ : (∑ t, F' t) / (Fintype.card α : ℝ) ^ 3 = μ := by
    dsimp only [μ, Q, F']
    rw [Fintype.sum_equiv e3.symm _ F (fun _ => rfl)]
  have hmXY : ∀ x y : α, (∑ z : Fin (Fintype.card α), F' (eA x, eA y, z)) / (Fintype.card α : ℝ) = mXY x y := by
    intro x y
    dsimp only [mXY, Q, F', e3]
    congr 1
    exact Fintype.sum_equiv eA.symm _ (fun z => F (x, y, z)) (fun z => by simp)
  have hmXZ : ∀ x z : α, (∑ y : Fin (Fintype.card α), F' (eA x, y, eA z)) / (Fintype.card α : ℝ) = mXZ x z := by
    intro x z
    dsimp only [mXZ, Q, F', e3]
    congr 1
    exact Fintype.sum_equiv eA.symm _ (fun y => F (x, y, z)) (fun y => by simp)
  have hmYZ : ∀ y z : α, (∑ x : Fin (Fintype.card α), F' (x, eA y, eA z)) / (Fintype.card α : ℝ) = mYZ y z := by
    intro y z
    dsimp only [mYZ, Q, F', e3]
    congr 1
    exact Fintype.sum_equiv eA.symm _ (fun x => F (x, y, z)) (fun x => by simp)
  have hrhs :
      (∑ t : Fin (Fintype.card α) × Fin (Fintype.card α) × Fin (Fintype.card α),
        ((∑ z, F' (t.1, t.2.1, z)) / (Fintype.card α : ℝ)) *
        ((∑ y, F' (t.1, y, t.2.2)) / (Fintype.card α : ℝ)) *
        ((∑ x, F' (x, t.2.1, t.2.2)) / (Fintype.card α : ℝ))) / (Fintype.card α : ℝ) ^ 3 =
      (∑ e : α × α × α, mXY e.1 e.2.1 * mXZ e.1 e.2.2 * mYZ e.2.1 e.2.2) / Q ^ 3 := by
    dsimp only [Q]
    congr 1
    exact (Fintype.sum_equiv e3
      (fun e => mXY e.1 e.2.1 * mXZ e.1 e.2.2 * mYZ e.2.1 e.2.2)
      (fun t =>
        ((∑ z, F' (t.1, t.2.1, z)) / (Fintype.card α : ℝ)) *
        ((∑ y, F' (t.1, y, t.2.2)) / (Fintype.card α : ℝ)) *
        ((∑ x, F' (x, t.2.1, t.2.2)) / (Fintype.card α : ℝ)))
      (fun ⟨x, y, z⟩ => by
        change mXY x y * mXZ x z * mYZ y z =
          ((∑ z', F' (eA x, eA y, z')) / (Fintype.card α : ℝ)) *
          ((∑ y', F' (eA x, y', eA z)) / (Fintype.card α : ℝ)) *
          ((∑ x', F' (x', eA y, eA z)) / (Fintype.card α : ℝ))
        rw [hmXY, hmXZ, hmYZ])).symm
  rw [hμ, hrhs] at hspec
  exact hspec

/- Section 2: Finite Fourier Analysis on ZMod 2 Vector Spaces -/

section Fourier

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

lemma add_self_eq_zero_f2 (x : W) : x + x = 0 := by
  have h1 : x + x = ((1 : ZMod 2) + 1) • x := by rw [add_smul, one_smul]
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [h1, h2, zero_smul]

lemma neg_eq_self_f2 (x : W) : -x = x := by
  have h := add_self_eq_zero_f2 x
  have h2 := eq_neg_of_add_eq_zero_left h
  exact h2.symm

lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

noncomputable def chi (r : Module.Dual (ZMod 2) W) (x : W) : ℝ :=
  if r x = 0 then 1 else -1

lemma chi_zero_left (x : W) : chi (0 : Module.Dual (ZMod 2) W) x = 1 := by
  simp [chi]

lemma chi_zero_right (r : Module.Dual (ZMod 2) W) : chi r 0 = 1 := by
  simp [chi]

lemma chi_add_right (r : Module.Dual (ZMod 2) W) (x y : W) :
    chi r (x + y) = chi r x * chi r y := by
  simp only [chi, map_add]
  rcases zmod2_eq_zero_or_one (r x) with hx | hx <;>
  rcases zmod2_eq_zero_or_one (r y) with hy | hy <;>
  simp [hx, hy]
  have : (1 : ZMod 2) + 1 = 0 := by decide
  simp [this]

lemma chi_add_left (r s : Module.Dual (ZMod 2) W) (x : W) :
    chi (r + s) x = chi r x * chi s x := by
  simp only [chi, LinearMap.add_apply]
  rcases zmod2_eq_zero_or_one (r x) with hr | hr <;>
  rcases zmod2_eq_zero_or_one (s x) with hs | hs <;>
  simp [hr, hs]
  have : (1 : ZMod 2) + 1 = 0 := by decide
  simp [this]

lemma chi_mul_self (r : Module.Dual (ZMod 2) W) (x : W) : chi r x * chi r x = 1 := by
  simp only [chi]
  split_ifs <;> ring

lemma abs_chi (r : Module.Dual (ZMod 2) W) (x : W) : |chi r x| = 1 := by
  simp only [chi]
  split_ifs <;> norm_num

variable [Fintype W]

noncomputable local instance instFintypeDual (W : Type*) [AddCommGroup W] [Module (ZMod 2) W] [Fintype W] :
    Fintype (Module.Dual (ZMod 2) W) :=
  letI : Finite (Module.Dual (ZMod 2) W) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  Fintype.ofFinite (Module.Dual (ZMod 2) W)

lemma sum_chi_right (r : Module.Dual (ZMod 2) W) :
    (∑ x : W, chi r x) = if r = 0 then (Fintype.card W : ℝ) else 0 := by
  by_cases hr : r = 0
  · subst hr
    simp [chi_zero_left]
  · rw [if_neg hr]
    have hex : ∃ a : W, r a ≠ 0 := by
      by_contra h
      push Not at h
      exact hr (LinearMap.ext fun a => by simpa using h a)
    obtain ⟨a, ha⟩ := hex
    have hchia : chi r a = -1 := by simp [chi, ha]
    have hshift : (∑ x : W, chi r x) = ∑ x : W, chi r (x + a) := by
      exact (Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)).symm
    have hneg : (∑ x : W, chi r (x + a)) = -(∑ x : W, chi r x) := by
      simp_rw [chi_add_right, hchia, mul_neg_one, Finset.sum_neg_distrib]
    linarith

lemma card_dual_eq_card : Fintype.card (Module.Dual (ZMod 2) W) = Fintype.card W := by
  have : Module.Finite (ZMod 2) W := inferInstance
  have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
  have h2 := Module.card_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) W)
  rw [Subspace.dual_finrank_eq] at h2
  rw [h2, ← h1]

lemma exists_dual_ne_zero {x : W} (hx : x ≠ 0) :
    ∃ r : Module.Dual (ZMod 2) W, r x ≠ 0 := by
  let b := Module.Basis.ofVectorSpace (ZMod 2) W
  have hne : ∃ i, b.repr x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    apply b.repr.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hne
  exact ⟨b.coord i, hi⟩

lemma sum_chi_left (x : W) :
    (∑ r : Module.Dual (ZMod 2) W, chi r x) = if x = 0 then (Fintype.card W : ℝ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [chi_zero_right, card_dual_eq_card]
  · rw [if_neg hx]
    obtain ⟨r₀, hr₀⟩ := exists_dual_ne_zero hx
    have hchir : chi r₀ x = -1 := by simp [chi, hr₀]
    have hshift : (∑ r : Module.Dual (ZMod 2) W, chi r x) = ∑ r : Module.Dual (ZMod 2) W, chi (r + r₀) x :=
      (Fintype.sum_equiv (Equiv.addRight r₀) _ _ (fun _ => rfl)).symm
    have hneg : (∑ r : Module.Dual (ZMod 2) W, chi (r + r₀) x) = -(∑ r : Module.Dual (ZMod 2) W, chi r x) := by
      simp_rw [chi_add_left, hchir, mul_neg_one, Finset.sum_neg_distrib]
    linarith

noncomputable def fHat (g : W → ℝ) (r : Module.Dual (ZMod 2) W) : ℝ :=
  (∑ x : W, g x * chi r x) / (Fintype.card W : ℝ)

noncomputable def indW (S : Finset W) (x : W) : ℝ :=
  if x ∈ S then 1 else 0

lemma fHat_indW_zero (S : Finset W) :
    fHat (indW S) 0 = (S.card : ℝ) / (Fintype.card W : ℝ) := by
  simp [fHat, indW, chi_zero_left]

lemma parseval (g : W → ℝ) :
    (∑ r : Module.Dual (ZMod 2) W, (fHat g r) ^ 2) =
      (∑ x : W, (g x) ^ 2) / (Fintype.card W : ℝ) := by
  have hWpos : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos (α := W)
  simp only [fHat, div_pow, ← Finset.sum_div]
  rw [div_eq_div_iff (pow_ne_zero 2 hWpos.ne') hWpos.ne']
  have hexp :
      (∑ r : Module.Dual (ZMod 2) W, (∑ x : W, g x * chi r x) ^ 2) =
      ∑ x : W, ∑ y : W, g x * g y * (∑ r : Module.Dual (ZMod 2) W, chi r (x + y)) := by
    calc
      (∑ r : Module.Dual (ZMod 2) W, (∑ x : W, g x * chi r x) ^ 2)
          = ∑ r : Module.Dual (ZMod 2) W, ∑ x : W, ∑ y : W, g x * g y * chi r (x + y) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [sq, Finset.sum_mul_sum]
              refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
              rw [chi_add_right]; ring
      _ = ∑ x : W, ∑ r : Module.Dual (ZMod 2) W, ∑ y : W, g x * g y * chi r (x + y) := Finset.sum_comm
      _ = ∑ x : W, ∑ y : W, ∑ r : Module.Dual (ZMod 2) W, g x * g y * chi r (x + y) :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
  rw [hexp]
  have hinner : ∀ x : W,
      (∑ y : W, g x * g y * (∑ r : Module.Dual (ZMod 2) W, chi r (x + y))) =
      (g x) ^ 2 * (Fintype.card W : ℝ) := by
    intro x
    have heq : ∀ y : W, (x + y = 0) ↔ y = x := fun y => by
      constructor
      · intro h
        have := congrArg (x + ·) h
        simp only [add_zero, ← add_assoc, add_self_eq_zero_f2, zero_add] at this
        exact this
      · rintro rfl; exact add_self_eq_zero_f2 y
    simp_rw [sum_chi_left, heq]
    simp [sq]
  simp_rw [hinner]
  rw [← Finset.sum_mul]
  ring

lemma triple_sum_eq_fourier (B C D : Finset W) :
    (((B ×ˢ C ×ˢ D).filter (fun t : W × W × W => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) =
      (Fintype.card W : ℝ) ^ 2 *
        ∑ r : Module.Dual (ZMod 2) W, fHat (indW B) r * fHat (indW C) r * fHat (indW D) r := by
  have hWpos : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos (α := W)
  have h1 :
      (((B ×ˢ C ×ˢ D).filter (fun t : W × W × W => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) =
      ∑ x : W, ∑ y : W, ∑ z : W, indW B x * indW C y * indW D z *
        (if x + y + z = 0 then (1 : ℝ) else 0) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    simp_rw [Finset.sum_product]
    rw [← Finset.sum_subset (Finset.subset_univ B)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.sum_subset (Finset.subset_univ C)]
      · refine Finset.sum_congr rfl fun y hy => ?_
        rw [← Finset.sum_subset (Finset.subset_univ D)]
        · refine Finset.sum_congr rfl fun z hz => ?_
          simp [indW, hx, hy, hz]
        · intro z _ hz; simp [indW, hz]
      · intro y _ hy; simp [indW, hy]
    · intro x _ hx; simp [indW, hx]
  rw [h1]
  have h2 :
      (∑ x : W, ∑ y : W, ∑ z : W, indW B x * indW C y * indW D z *
        (if x + y + z = 0 then (1 : ℝ) else 0)) =
      (∑ x : W, ∑ y : W, ∑ z : W, indW B x * indW C y * indW D z *
        (∑ r : Module.Dual (ZMod 2) W, chi r (x + y + z))) / (Fintype.card W : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [sum_chi_left]
    split_ifs <;> simp [hWpos.ne']
  rw [h2]
  have h3 :
      (∑ x : W, ∑ y : W, ∑ z : W, indW B x * indW C y * indW D z *
        (∑ r : Module.Dual (ZMod 2) W, chi r (x + y + z))) =
      ∑ r : Module.Dual (ZMod 2) W,
        (∑ x : W, indW B x * chi r x) * (∑ y : W, indW C y * chi r y) * (∑ z : W, indW D z * chi r z) := by
    have hsplit : ∀ x y z : W,
        indW B x * indW C y * indW D z * (∑ r : Module.Dual (ZMod 2) W, chi r (x + y + z)) =
        ∑ r : Module.Dual (ZMod 2) W, (indW B x * chi r x) * (indW C y * chi r y) * (indW D z * chi r z) := by
      intro x y z
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [chi_add_right, chi_add_right]; ring
    simp_rw [hsplit]
    calc
      (∑ x : W, ∑ y : W, ∑ z : W, ∑ r : Module.Dual (ZMod 2) W,
          (indW B x * chi r x) * (indW C y * chi r y) * (indW D z * chi r z))
          = ∑ x : W, ∑ y : W, ∑ r : Module.Dual (ZMod 2) W, ∑ z : W,
              (indW B x * chi r x) * (indW C y * chi r y) * (indW D z * chi r z) :=
                Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_comm
      _ = ∑ x : W, ∑ r : Module.Dual (ZMod 2) W, ∑ y : W, ∑ z : W,
              (indW B x * chi r x) * (indW C y * chi r y) * (indW D z * chi r z) :=
                Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ r : Module.Dual (ZMod 2) W, ∑ x : W, ∑ y : W, ∑ z : W,
              (indW B x * chi r x) * (indW C y * chi r y) * (indW D z * chi r z) := Finset.sum_comm
      _ = _ := by
            refine Finset.sum_congr rfl fun r _ => ?_
            simp_rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_mul_sum]
  rw [h3]
  simp only [fHat]
  have hdiv :
      (∑ r : Module.Dual (ZMod 2) W,
        ((∑ x : W, indW B x * chi r x) / (Fintype.card W : ℝ)) *
        ((∑ y : W, indW C y * chi r y) / (Fintype.card W : ℝ)) *
        ((∑ z : W, indW D z * chi r z) / (Fintype.card W : ℝ))) =
      (∑ r : Module.Dual (ZMod 2) W,
        (∑ x : W, indW B x * chi r x) * (∑ y : W, indW C y * chi r y) * (∑ z : W, indW D z * chi r z)) /
        (Fintype.card W : ℝ) ^ 3 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [hdiv]
  field_simp

lemma triple_sum_le_of_uniform (B C D : Finset W) {η : ℝ} (hη : 0 ≤ η)
    (hunif : ∀ r : Module.Dual (ZMod 2) W, r ≠ 0 → |fHat (indW B) r| ≤ η) :
    (((B ×ˢ C ×ˢ D).filter (fun t : W × W × W => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) ≤
      (B.card : ℝ) * C.card * D.card / (Fintype.card W : ℝ) + η * (Fintype.card W : ℝ) ^ 2 := by
  have hWpos : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos (α := W)
  rw [triple_sum_eq_fourier]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Module.Dual (ZMod 2) W))]
  have h0 :
      (Fintype.card W : ℝ) ^ 2 * (fHat (indW B) 0 * fHat (indW C) 0 * fHat (indW D) 0) =
      (B.card : ℝ) * C.card * D.card / (Fintype.card W : ℝ) := by
    rw [fHat_indW_zero, fHat_indW_zero, fHat_indW_zero]
    field_simp
  rw [mul_add, h0]
  refine add_le_add le_rfl ?_
  have htail :
      (∑ r ∈ univ.erase (0 : Module.Dual (ZMod 2) W),
        fHat (indW B) r * fHat (indW C) r * fHat (indW D) r) ≤ η := by
    calc
      (∑ r ∈ univ.erase (0 : Module.Dual (ZMod 2) W),
          fHat (indW B) r * fHat (indW C) r * fHat (indW D) r)
          ≤ ∑ r ∈ univ.erase (0 : Module.Dual (ZMod 2) W),
              |fHat (indW B) r| * (|fHat (indW C) r| * |fHat (indW D) r|) := by
                refine Finset.sum_le_sum fun r _ => ?_
                have hle := le_abs_self (fHat (indW B) r * fHat (indW C) r * fHat (indW D) r)
                rw [abs_mul, abs_mul] at hle
                linarith
      _ ≤ ∑ r ∈ univ.erase (0 : Module.Dual (ZMod 2) W),
            η * (|fHat (indW C) r| * |fHat (indW D) r|) := by
              refine Finset.sum_le_sum fun r hr => ?_
              have hne : r ≠ 0 := (Finset.mem_erase.mp hr).1
              exact mul_le_mul_of_nonneg_right (hunif r hne) (by positivity)
      _ = η * ∑ r ∈ univ.erase (0 : Module.Dual (ZMod 2) W), |fHat (indW C) r| * |fHat (indW D) r| :=
            (Finset.mul_sum _ _ _).symm
      _ ≤ η * ∑ r : Module.Dual (ZMod 2) W, |fHat (indW C) r| * |fHat (indW D) r| := by
            gcongr
            exact Finset.erase_subset _ _
      _ ≤ η * 1 := by
            gcongr
            have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Module.Dual (ZMod 2) W))
              (fun r => |fHat (indW C) r|) (fun r => |fHat (indW D) r|)
            simp only [sq_abs] at hcs
            have hC : (∑ r : Module.Dual (ZMod 2) W, (fHat (indW C) r) ^ 2) ≤ 1 := by
              rw [parseval, div_le_one hWpos]
              calc
                (∑ x : W, (indW C x) ^ 2) ≤ ∑ _x : W, (1 : ℝ) := by
                  refine Finset.sum_le_sum fun x _ => ?_
                  dsimp [indW]; split_ifs <;> norm_num
                _ = Fintype.card W := by simp
            have hD : (∑ r : Module.Dual (ZMod 2) W, (fHat (indW D) r) ^ 2) ≤ 1 := by
              rw [parseval, div_le_one hWpos]
              calc
                (∑ x : W, (indW D x) ^ 2) ≤ ∑ _x : W, (1 : ℝ) := by
                  refine Finset.sum_le_sum fun x _ => ?_
                  dsimp [indW]; split_ifs <;> norm_num
                _ = Fintype.card W := by simp
            have hprod : (∑ r : Module.Dual (ZMod 2) W, |fHat (indW C) r| * |fHat (indW D) r|) ^ 2 ≤ 1 := by
              have hC0 : 0 ≤ ∑ r : Module.Dual (ZMod 2) W, (fHat (indW C) r) ^ 2 :=
                Finset.sum_nonneg fun _ _ => sq_nonneg _
              nlinarith [mul_le_mul hC hD (Finset.sum_nonneg fun _ _ => sq_nonneg _) zero_le_one]
            nlinarith [Finset.sum_nonneg (s := (univ : Finset (Module.Dual (ZMod 2) W)))
              (f := fun r => |fHat (indW C) r| * |fHat (indW D) r|) (fun _ _ => by positivity)]
      _ = η := mul_one η
  calc
    (Fintype.card W : ℝ) ^ 2 * ∑ r ∈ univ.erase 0, fHat (indW B) r * fHat (indW C) r * fHat (indW D) r
        ≤ (Fintype.card W : ℝ) ^ 2 * η := by gcongr
    _ = η * (Fintype.card W : ℝ) ^ 2 := mul_comm _ _

end Fourier

/- Section 3: Variance Increment & Triangle Counting Lemma -/

lemma variance_identity {ι α : Type*} [Fintype ι] [DecidableEq α]
    (U M : Finset α) (P : ι → Finset α)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hcov : univ.biUnion P = U) :
    let μ : ℝ := ((M ∩ U).card : ℝ) / (U.card : ℝ)
    let d (i : ι) : ℝ := ((M ∩ P i).card : ℝ) / ((P i).card : ℝ)
    (∑ i : ι, ((P i).card : ℝ) * (d i) ^ 2) - (U.card : ℝ) * μ ^ 2 =
      ∑ i : ι, ((P i).card : ℝ) * (d i - μ) ^ 2 := by
  intro μ d
  have hsumP : (∑ i : ι, ((P i).card : ℝ)) = (U.card : ℝ) := by
    have h1 : U.card = ∑ i : ι, (P i).card := by
      rw [← hcov, Finset.card_biUnion (fun i _ j _ hij => hdisj hij)]
    exact_mod_cast h1.symm
  have hsumM : (∑ i : ι, ((M ∩ P i).card : ℝ)) = ((M ∩ U).card : ℝ) := by
    have hcovM : univ.biUnion (fun i => M ∩ P i) = M ∩ U := by
      ext x
      simp only [mem_biUnion, mem_univ, true_and, mem_inter, ← hcov]
      tauto
    have hdisjM : Pairwise (fun i j => Disjoint (M ∩ P i) (M ∩ P j)) := fun i j hij =>
      (hdisj hij).mono inter_subset_right inter_subset_right
    have h1 : (M ∩ U).card = ∑ i : ι, (M ∩ P i).card := by
      rw [← hcovM, Finset.card_biUnion (fun i _ j _ hij => hdisjM hij)]
    exact_mod_cast h1.symm
  have hmuld : ∀ i : ι, ((P i).card : ℝ) * d i = ((M ∩ P i).card : ℝ) := by
    intro i
    dsimp only [d]
    by_cases h0 : (P i).card = 0
    · have hempty : P i = ∅ := Finset.card_eq_zero.mp h0
      simp [hempty]
    · field_simp
  have hmulμ : (U.card : ℝ) * μ = ((M ∩ U).card : ℝ) := by
    dsimp only [μ]
    by_cases h0 : U.card = 0
    · have hempty : U = ∅ := Finset.card_eq_zero.mp h0
      simp [hempty]
    · field_simp
  have hexp :
      (∑ i : ι, ((P i).card : ℝ) * (d i - μ) ^ 2) =
      (∑ i : ι, ((P i).card : ℝ) * (d i) ^ 2) -
        2 * μ * (∑ i : ι, ((P i).card : ℝ) * d i) +
        μ ^ 2 * (∑ i : ι, ((P i).card : ℝ)) := by
    have hterm : ∀ i : ι,
        ((P i).card : ℝ) * (d i - μ) ^ 2 =
        ((P i).card : ℝ) * (d i) ^ 2 - 2 * μ * (((P i).card : ℝ) * d i) + μ ^ 2 * ((P i).card : ℝ) := by
      intro i; ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexp]
  simp_rw [hmuld]
  rw [hsumM, hsumP, ← hmulμ]
  ring

lemma variance_nonneg {ι α : Type*} [Fintype ι] [DecidableEq α]
    (U M : Finset α) (P : ι → Finset α)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hcov : univ.biUnion P = U) :
    (U.card : ℝ) * (((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2 ≤
      ∑ i : ι, ((P i).card : ℝ) * (((M ∩ P i).card : ℝ) / ((P i).card : ℝ)) ^ 2 := by
  have hid := variance_identity U M P hdisj hcov
  have hnn : 0 ≤ ∑ i : ι, ((P i).card : ℝ) *
      (((M ∩ P i).card : ℝ) / ((P i).card : ℝ) - ((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  linarith

lemma variance_increment {ι α : Type*} [Fintype ι] [DecidableEq α]
    (U M : Finset α) (P : ι → Finset α)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hcov : univ.biUnion P = U)
    (i₀ : ι) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hsize : c₁ * (U.card : ℝ) ≤ ((P i₀).card : ℝ))
    (hdev : c₂ ≤ |((M ∩ P i₀).card : ℝ) / ((P i₀).card : ℝ) - ((M ∩ U).card : ℝ) / (U.card : ℝ)|) :
    (U.card : ℝ) * (((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2 + c₁ * c₂ ^ 2 * (U.card : ℝ) ≤
      ∑ i : ι, ((P i).card : ℝ) * (((M ∩ P i).card : ℝ) / ((P i).card : ℝ)) ^ 2 := by
  have hid := variance_identity U M P hdisj hcov
  have hsingle :
      ((P i₀).card : ℝ) *
        (((M ∩ P i₀).card : ℝ) / ((P i₀).card : ℝ) - ((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2 ≤
      ∑ i : ι, ((P i).card : ℝ) *
        (((M ∩ P i).card : ℝ) / ((P i).card : ℝ) - ((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2 :=
    Finset.single_le_sum
      (f := fun i => ((P i).card : ℝ) * (((M ∩ P i).card : ℝ) / ((P i).card : ℝ) - ((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2)
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Finset.mem_univ i₀)
  have hsq : c₂ ^ 2 ≤
      (((M ∩ P i₀).card : ℝ) / ((P i₀).card : ℝ) - ((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2 := by
    rw [← sq_abs (((M ∩ P i₀).card : ℝ) / ((P i₀).card : ℝ) - ((M ∩ U).card : ℝ) / (U.card : ℝ))]
    exact pow_le_pow_left₀ hc₂ hdev 2
  have hlow : c₁ * c₂ ^ 2 * (U.card : ℝ) ≤
      ((P i₀).card : ℝ) *
        (((M ∩ P i₀).card : ℝ) / ((P i₀).card : ℝ) - ((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2 := by
    calc
      c₁ * c₂ ^ 2 * (U.card : ℝ) = (c₁ * (U.card : ℝ)) * c₂ ^ 2 := by ring
      _ ≤ ((P i₀).card : ℝ) *
            (((M ∩ P i₀).card : ℝ) / ((P i₀).card : ℝ) - ((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2 :=
        mul_le_mul hsize hsq (sq_nonneg _) (Nat.cast_nonneg _)
  linarith

/- Quasirandomness and Triangle Counting Lemma -/

noncomputable def edgeCount {α β : Type*} (E : α → β → Prop) (X : Finset α) (Y : Finset β) : ℕ :=
  ((X ×ˢ Y).filter (fun p => E p.1 p.2)).card

noncomputable def pairDensity {α β : Type*} (E : α → β → Prop) (X : Finset α) (Y : Finset β) : ℝ :=
  (edgeCount E X Y : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))

def IsQuasirandom {α β : Type*} (ε : ℝ) (E : α → β → Prop) (X : Finset α) (Y : Finset β) : Prop :=
  ∀ X' ⊆ X, ∀ Y' ⊆ Y,
    ε * (X.card : ℝ) ≤ (X'.card : ℝ) →
    ε * (Y.card : ℝ) ≤ (Y'.card : ℝ) →
    |(edgeCount E X' Y' : ℝ) - pairDensity E X Y * (X'.card : ℝ) * (Y'.card : ℝ)| ≤
      ε * (X'.card : ℝ) * (Y'.card : ℝ)

lemma pairDensity_nonneg {α β : Type*} (E : α → β → Prop) (X : Finset α) (Y : Finset β) :
    0 ≤ pairDensity E X Y := by
  dsimp [pairDensity]; positivity

lemma pairDensity_le_one {α β : Type*} (E : α → β → Prop) (X : Finset α) (Y : Finset β) :
    pairDensity E X Y ≤ 1 := by
  dsimp [pairDensity, edgeCount]
  by_cases h : (X.card : ℝ) * (Y.card : ℝ) = 0
  · simp [h]
  · have hpos : 0 < (X.card : ℝ) * (Y.card : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [div_le_one hpos]
    have hle : ((X ×ˢ Y).filter (fun p => E p.1 p.2)).card ≤ (X ×ˢ Y).card := Finset.card_filter_le _ _
    rw [Finset.card_product] at hle
    exact_mod_cast hle

lemma triangle_counting_lemma {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (EXY : α → β → Prop) (EXZ : α → γ → Prop) (EYZ : β → γ → Prop)
    (X : Finset α) (Y : Finset β) (Z : Finset γ)
    (hXY : IsQuasirandom ε EXY X Y) (hXZ : IsQuasirandom ε EXZ X Z) (hYZ : IsQuasirandom ε EYZ Y Z) :
    (pairDensity EXY X Y * pairDensity EXZ X Z * pairDensity EYZ Y Z - 5 * ε) *
      (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ≤
      (((X ×ˢ Y ×ˢ Z).filter (fun t => EXY t.1 t.2.1 ∧ EXZ t.1 t.2.2 ∧ EYZ t.2.1 t.2.2)).card : ℝ) := by
  set dXY := pairDensity EXY X Y
  set dXZ := pairDensity EXZ X Z
  set dYZ := pairDensity EYZ Y Z
  have hdXY0 : 0 ≤ dXY := pairDensity_nonneg _ _ _
  have hdXZ0 : 0 ≤ dXZ := pairDensity_nonneg _ _ _
  have hdYZ0 : 0 ≤ dYZ := pairDensity_nonneg _ _ _
  have hdXY1 : dXY ≤ 1 := pairDensity_le_one _ _ _
  have hdXZ1 : dXZ ≤ 1 := pairDensity_le_one _ _ _
  have hdYZ1 : dYZ ≤ 1 := pairDensity_le_one _ _ _
  by_cases hsmall : dXY < 2 * ε ∨ dXZ < 2 * ε ∨ dYZ < 2 * ε
  · have hprod_le : dXY * dXZ * dYZ ≤ 2 * ε := by
      rcases hsmall with h | h | h
      · calc dXY * dXZ * dYZ ≤ (2 * ε) * 1 * 1 :=
              mul_le_mul (mul_le_mul h.le hdXZ1 hdXZ0 (by linarith)) hdYZ1 hdYZ0 (by positivity)
          _ = 2 * ε := by ring
      · calc dXY * dXZ * dYZ ≤ 1 * (2 * ε) * 1 :=
              mul_le_mul (mul_le_mul hdXY1 h.le hdXZ0 zero_le_one) hdYZ1 hdYZ0 (by positivity)
          _ = 2 * ε := by ring
      · calc dXY * dXZ * dYZ ≤ (1 * 1) * (2 * ε) :=
              mul_le_mul (mul_le_mul hdXY1 hdXZ1 hdXZ0 zero_le_one) h.le hdYZ0 (by norm_num)
          _ = 2 * ε := by ring
    have hnonpos : (dXY * dXZ * dYZ - 5 * ε) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) ≤ 0 := by
      have hsub : dXY * dXZ * dYZ - 5 * ε ≤ 0 := by linarith
      have hxyz : 0 ≤ (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by positivity
      calc
        (dXY * dXZ * dYZ - 5 * ε) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)
            = (dXY * dXZ * dYZ - 5 * ε) * ((X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) := by ring
        _ ≤ 0 * ((X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) := mul_le_mul_of_nonneg_right hsub hxyz
        _ = 0 := zero_mul _
    exact hnonpos.trans (Nat.cast_nonneg _)
  push Not at hsmall
  obtain ⟨hXY2, hXZ2, hYZ2⟩ := hsmall
  by_cases hX0 : X.card = 0
  · simp [hX0]
  by_cases hY0 : Y.card = 0
  · simp [hY0]
  by_cases hZ0 : Z.card = 0
  · simp [hZ0]
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast Nat.pos_of_ne_zero hX0
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast Nat.pos_of_ne_zero hY0
  have hZpos : (0 : ℝ) < Z.card := by exact_mod_cast Nat.pos_of_ne_zero hZ0
  have h2ε : 2 * ε ≤ 1 := by linarith
  let NY (x : α) : Finset β := Y.filter (fun y => EXY x y)
  let NZ (x : α) : Finset γ := Z.filter (fun z => EXZ x z)
  let B1 : Finset α := X.filter (fun x => ((NY x).card : ℝ) < (dXY - ε) * (Y.card : ℝ))
  let B2 : Finset α := X.filter (fun x => ((NZ x).card : ℝ) < (dXZ - ε) * (Z.card : ℝ))
  have hB1 : (B1.card : ℝ) < ε * (X.card : ℝ) := by
    by_contra hge
    push Not at hge
    have hB1pos : 0 < B1.card := by
      have : (0 : ℝ) < B1.card := lt_of_lt_of_le (mul_pos hε hXpos) hge
      exact_mod_cast this
    have hq := hXY B1 (filter_subset _ _) Y Subset.rfl hge (by nlinarith only [hε1, hYpos])
    have hlo : (dXY - ε) * (B1.card : ℝ) * (Y.card : ℝ) ≤ (edgeCount EXY B1 Y : ℝ) := by
      have := (abs_le.mp hq).1; linarith
    have hsum_eq : (edgeCount EXY B1 Y : ℝ) = ∑ x ∈ B1, ((NY x).card : ℝ) := by
      dsimp only [edgeCount, NY]
      rw [Finset.card_filter, Finset.sum_product, Nat.cast_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.card_filter, Nat.cast_sum]
    have hlt : (∑ x ∈ B1, ((NY x).card : ℝ)) < ∑ _x ∈ B1, (dXY - ε) * (Y.card : ℝ) := by
      refine Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hB1pos) fun x hx => ?_
      exact (Finset.mem_filter.mp hx).2
    rw [Finset.sum_const, nsmul_eq_mul] at hlt
    linarith
  have hB2 : (B2.card : ℝ) < ε * (X.card : ℝ) := by
    by_contra hge
    push Not at hge
    have hB2pos : 0 < B2.card := by
      have : (0 : ℝ) < B2.card := lt_of_lt_of_le (mul_pos hε hXpos) hge
      exact_mod_cast this
    have hq := hXZ B2 (filter_subset _ _) Z Subset.rfl hge (by nlinarith only [hε1, hZpos])
    have hlo : (dXZ - ε) * (B2.card : ℝ) * (Z.card : ℝ) ≤ (edgeCount EXZ B2 Z : ℝ) := by
      have := (abs_le.mp hq).1; linarith
    have hsum_eq : (edgeCount EXZ B2 Z : ℝ) = ∑ x ∈ B2, ((NZ x).card : ℝ) := by
      dsimp only [edgeCount, NZ]
      rw [Finset.card_filter, Finset.sum_product, Nat.cast_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.card_filter, Nat.cast_sum]
    have hlt : (∑ x ∈ B2, ((NZ x).card : ℝ)) < ∑ _x ∈ B2, (dXZ - ε) * (Z.card : ℝ) := by
      refine Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hB2pos) fun x hx => ?_
      exact (Finset.mem_filter.mp hx).2
    rw [Finset.sum_const, nsmul_eq_mul] at hlt
    linarith
  let Xg : Finset α := X \ (B1 ∪ B2)
  have hXg_card : (1 - 2 * ε) * (X.card : ℝ) ≤ (Xg.card : ℝ) := by
    have hsub : B1 ∪ B2 ⊆ X := Finset.union_subset (filter_subset _ _) (filter_subset _ _)
    have hcard : Xg.card + (B1 ∪ B2).card = X.card := Finset.card_sdiff_add_card_eq_card hsub
    have hunion : (B1 ∪ B2).card ≤ B1.card + B2.card := Finset.card_union_le B1 B2
    have h1 : (Xg.card : ℝ) + ((B1 ∪ B2).card : ℝ) = (X.card : ℝ) := by exact_mod_cast hcard
    have h2 : ((B1 ∪ B2).card : ℝ) ≤ (B1.card : ℝ) + (B2.card : ℝ) := by exact_mod_cast hunion
    linarith
  have htri_eq :
      (((X ×ˢ Y ×ˢ Z).filter (fun t => EXY t.1 t.2.1 ∧ EXZ t.1 t.2.2 ∧ EYZ t.2.1 t.2.2)).card : ℝ) =
      ∑ x ∈ X, (edgeCount EYZ (NY x) (NZ x) : ℝ) := by
    rw [Finset.card_filter, Finset.sum_product, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only [edgeCount, NY, NZ]
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_product]
    simp only [Finset.sum_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h1 : EXY x y
    · simp only [h1, true_and, ↓reduceIte, Nat.cast_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases h2 : EXZ x z <;> by_cases h3 : EYZ y z <;> simp [h2, h3]
    · simp [h1]
  rw [htri_eq]
  have hgood_bound : ∀ x ∈ Xg,
      (dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ) ≤
        (edgeCount EYZ (NY x) (NZ x) : ℝ) := by
    intro x hx
    have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
    have hxnot : x ∉ B1 ∪ B2 := (Finset.mem_sdiff.mp hx).2
    have hNY : (dXY - ε) * (Y.card : ℝ) ≤ ((NY x).card : ℝ) := by
      by_contra hlt; push Not at hlt
      exact hxnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxX, hlt⟩))
    have hNZ : (dXZ - ε) * (Z.card : ℝ) ≤ ((NZ x).card : ℝ) := by
      by_contra hlt; push Not at hlt
      exact hxnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxX, hlt⟩))
    have hNYε : ε * (Y.card : ℝ) ≤ ((NY x).card : ℝ) := by
      have : ε * (Y.card : ℝ) ≤ (dXY - ε) * (Y.card : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hYpos.le
      linarith
    have hNZε : ε * (Z.card : ℝ) ≤ ((NZ x).card : ℝ) := by
      have : ε * (Z.card : ℝ) ≤ (dXZ - ε) * (Z.card : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hZpos.le
      linarith
    have hq := hYZ (NY x) (filter_subset _ _) (NZ x) (filter_subset _ _) hNYε hNZε
    have hlo : (dYZ - ε) * ((NY x).card : ℝ) * ((NZ x).card : ℝ) ≤ (edgeCount EYZ (NY x) (NZ x) : ℝ) := by
      have := (abs_le.mp hq).1; linarith
    have hmul :
        (dXY - ε) * (dXZ - ε) * (Y.card : ℝ) * (Z.card : ℝ) ≤ ((NY x).card : ℝ) * ((NZ x).card : ℝ) := by
      have h1 := mul_le_mul hNY hNZ (mul_nonneg (by linarith) hZpos.le) (Nat.cast_nonneg _)
      linarith
    have hYZ0 : 0 ≤ dYZ - ε := by linarith
    calc
      (dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ)
          = (dYZ - ε) * ((dXY - ε) * (dXZ - ε) * (Y.card : ℝ) * (Z.card : ℝ)) := by ring
      _ ≤ (dYZ - ε) * (((NY x).card : ℝ) * ((NZ x).card : ℝ)) := mul_le_mul_of_nonneg_left hmul hYZ0
      _ = (dYZ - ε) * ((NY x).card : ℝ) * ((NZ x).card : ℝ) := by ring
      _ ≤ (edgeCount EYZ (NY x) (NZ x) : ℝ) := hlo
  have hsum_Xg :
      (Xg.card : ℝ) * ((dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ)) ≤
        ∑ x ∈ X, (edgeCount EYZ (NY x) (NZ x) : ℝ) := by
    calc
      (Xg.card : ℝ) * ((dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ))
          = ∑ _x ∈ Xg, (dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ Xg, (edgeCount EYZ (NY x) (NZ x) : ℝ) := Finset.sum_le_sum hgood_bound
      _ ≤ ∑ x ∈ X, (edgeCount EYZ (NY x) (NZ x) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
  have halg : dXY * dXZ * dYZ - 5 * ε ≤ (1 - 2 * ε) * ((dXY - ε) * (dXZ - ε) * (dYZ - ε)) := by
    have h1 : dXY * dXZ - 2 * ε ≤ (dXY - ε) * (dXZ - ε) := by
      have hsq : 0 ≤ ε * ε := mul_nonneg hε.le hε.le
      nlinarith only [hdXY1, hdXZ1, hε, hsq]
    have hprod1 : dXY * dXZ ≤ 1 := by
      calc dXY * dXZ ≤ 1 * 1 := mul_le_mul hdXY1 hdXZ1 hdXZ0 zero_le_one
        _ = 1 := one_mul 1
    have h3 : dXY * dXZ * dYZ - 3 * ε ≤ (dXY - ε) * (dXZ - ε) * (dYZ - ε) := by
      have hmul : (dXY * dXZ - 2 * ε) * (dYZ - ε) ≤ (dXY - ε) * (dXZ - ε) * (dYZ - ε) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
      have h2e : 0 ≤ 2 * ε * ε := by positivity
      nlinarith only [hmul, hprod1, hdYZ1, hε, h2e]
    have h4 : dXY * dXZ * dYZ ≤ 1 := by
      calc dXY * dXZ * dYZ ≤ 1 * 1 := mul_le_mul hprod1 hdYZ1 hdYZ0 zero_le_one
        _ = 1 := one_mul 1
    have h6e : 0 ≤ 6 * ε * ε := by positivity
    nlinarith only [h3, h4, hε, h2ε, h6e]
  have hprod_nonneg : 0 ≤ (dXY - ε) * (dXZ - ε) * (dYZ - ε) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hxyz : 0 ≤ (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ) := by positivity
  calc
    (dXY * dXZ * dYZ - 5 * ε) * (X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)
        = (dXY * dXZ * dYZ - 5 * ε) * ((X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) := by ring
    _ ≤ ((1 - 2 * ε) * ((dXY - ε) * (dXZ - ε) * (dYZ - ε))) *
          ((X.card : ℝ) * (Y.card : ℝ) * (Z.card : ℝ)) := mul_le_mul_of_nonneg_right halg hxyz
    _ = ((1 - 2 * ε) * (X.card : ℝ)) *
          ((dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ)) := by ring
    _ ≤ (Xg.card : ℝ) *
          ((dXY - ε) * (dXZ - ε) * (dYZ - ε) * (Y.card : ℝ) * (Z.card : ℝ)) :=
            mul_le_mul_of_nonneg_right hXg_card (mul_nonneg (mul_nonneg hprod_nonneg hYpos.le) hZpos.le)
    _ ≤ ∑ x ∈ X, (edgeCount EYZ (NY x) (NZ x) : ℝ) := hsum_Xg

/- Section 4: Mandache's Boxing, Dual Energies, and Regularity Lemma -/

section Boxing

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] [DecidableEq G]

lemma mk_out {W : Submodule (ZMod 2) G} (u : G ⧸ W) :
    Submodule.Quotient.mk (p := W) u.out = u :=
  Quotient.out_eq u

noncomputable def coset (W : Submodule (ZMod 2) G) (u : G ⧸ W) : Finset G :=
  univ.filter (fun x : G => Submodule.Quotient.mk x = u)

lemma mem_coset {W : Submodule (ZMod 2) G} {u : G ⧸ W} {x : G} :
    x ∈ coset W u ↔ Submodule.Quotient.mk x = u := by
  simp [coset]

lemma card_coset (W : Submodule (ZMod 2) G) (u : G ⧸ W) :
    (coset W u).card = Fintype.card W := by
  have hbij : (coset W u).card = (univ : Finset W).card := by
    refine Finset.card_bij (fun x hx => ⟨x + u.out, ?_⟩) ?_ ?_ ?_
    · rw [mem_coset] at hx
      have hsub : Submodule.Quotient.mk (p := W) (x - u.out) = 0 := by
        rw [Submodule.Quotient.mk_sub, hx, mk_out, sub_self]
      have hmem : x - u.out ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hsub
      rwa [sub_eq_add_neg, neg_eq_self_f2] at hmem
    · intro _ _; exact mem_univ _
    · intro x₁ _ x₂ _ heq
      have hval : x₁ + u.out = x₂ + u.out := congrArg Subtype.val heq
      exact add_right_cancel hval
    · intro a _
      refine ⟨u.out + a.1, ?_, ?_⟩
      · rw [mem_coset, Submodule.Quotient.mk_add, mk_out,
            (Submodule.Quotient.mk_eq_zero W).mpr a.2, add_zero]
      · apply Subtype.ext
        change (u.out + a.1) + u.out = a.1
        rw [add_comm u.out a.1, add_assoc, add_self_eq_zero_f2, add_zero]
  simpa using hbij

lemma coset_disjoint (W : Submodule (ZMod 2) G) :
    Pairwise (fun u v : G ⧸ W => Disjoint (coset W u) (coset W v)) := by
  intro u v huv
  rw [Finset.disjoint_left]
  intro x hxu hxv
  rw [mem_coset] at hxu hxv
  exact huv (hxu.symm.trans hxv)

lemma biUnion_coset (W : Submodule (ZMod 2) G) :
    (univ : Finset (G ⧸ W)).biUnion (coset W) = univ := by
  ext x
  simp [mem_coset]

lemma card_quotient_mul_card (W : Submodule (ZMod 2) G) :
    Fintype.card (G ⧸ W) * Fintype.card W = Fintype.card G := by
  have h1 : (univ : Finset G).card = ∑ u : G ⧸ W, (coset W u).card := by
    rw [← biUnion_coset W, Finset.card_biUnion (fun u _ v _ huv => coset_disjoint W huv)]
  simp_rw [card_coset, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
  simpa using h1.symm

lemma card_quotient_pos (W : Submodule (ZMod 2) G) : 0 < Fintype.card (G ⧸ W) :=
  Fintype.card_pos

lemma card_submodule_pos (W : Submodule (ZMod 2) G) : 0 < Fintype.card W :=
  Fintype.card_pos

noncomputable def shiftCoset (W : Submodule (ZMod 2) G) (u : G ⧸ W) (S : Finset G) : Finset W :=
  univ.filter (fun a : W => u.out + a.1 ∈ S)

lemma card_shiftCoset {W : Submodule (ZMod 2) G} {u : G ⧸ W} {S : Finset G}
    (hS : S ⊆ coset W u) : (shiftCoset W u S).card = S.card := by
  refine Finset.card_bij (fun a _ => u.out + a.1) ?_ ?_ ?_
  · intro a ha; exact (Finset.mem_filter.mp ha).2
  · intro a₁ _ a₂ _ h; exact Subtype.ext (add_left_cancel h)
  · intro x hx
    have hxu : Submodule.Quotient.mk (p := W) x = u := mem_coset.mp (hS hx)
    have hmem : x + u.out ∈ W := by
      have hsub : Submodule.Quotient.mk (p := W) (x - u.out) = 0 := by
        rw [Submodule.Quotient.mk_sub, hxu, mk_out, sub_self]
      have := (Submodule.Quotient.mk_eq_zero W).mp hsub
      rwa [sub_eq_add_neg, neg_eq_self_f2] at this
    have heq : u.out + (x + u.out) = x := by
      rw [add_comm x u.out, ← add_assoc, add_self_eq_zero_f2, zero_add]
    refine ⟨⟨x + u.out, hmem⟩, ?_, heq⟩
    simp only [shiftCoset, mem_filter, mem_univ, true_and]
    exact heq.symm ▸ hx

lemma triple_sum_coset_le {W : Submodule (ZMod 2) G} {u v : G ⧸ W}
    {B C D : Finset G} (hB : B ⊆ coset W u) (hC : C ⊆ coset W v) (hD : D ⊆ coset W (u + v))
    {η : ℝ} (hη : 0 ≤ η)
    (hunif : ∀ r : Module.Dual (ZMod 2) W, r ≠ 0 → |fHat (indW (shiftCoset W u B)) r| ≤ η) :
    (((B ×ˢ C ×ˢ D).filter (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) ≤
      (B.card : ℝ) * C.card * D.card / (Fintype.card W : ℝ) + η * (Fintype.card W : ℝ) ^ 2 := by
  let B' : Finset W := shiftCoset W u B
  let C' : Finset W := shiftCoset W v C
  let D' : Finset W := univ.filter (fun c : W => (u.out + v.out) + c.1 ∈ D)
  have hB' : B'.card = B.card := card_shiftCoset hB
  have hC' : C'.card = C.card := card_shiftCoset hC
  have hD' : D'.card = D.card := by
    refine Finset.card_bij (fun c _ => (u.out + v.out) + c.1) ?_ ?_ ?_
    · intro c hc; exact (Finset.mem_filter.mp hc).2
    · intro c₁ _ c₂ _ h; exact Subtype.ext (add_left_cancel h)
    · intro z hz
      have hzu : Submodule.Quotient.mk (p := W) z = u + v := mem_coset.mp (hD hz)
      have hmem : z + (u.out + v.out) ∈ W := by
        have hsub : Submodule.Quotient.mk (p := W) (z - (u.out + v.out)) = 0 := by
          rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add, hzu, mk_out, mk_out, sub_self]
        have := (Submodule.Quotient.mk_eq_zero W).mp hsub
        rwa [sub_eq_add_neg, neg_eq_self_f2] at this
      have heq : (u.out + v.out) + (z + (u.out + v.out)) = z := by
        rw [add_comm z (u.out + v.out), ← add_assoc, add_self_eq_zero_f2, zero_add]
      refine ⟨⟨z + (u.out + v.out), hmem⟩, ?_, heq⟩
      simp only [D', mem_filter, mem_univ, true_and]
      exact heq.symm ▸ hz
  have hcard_eq :
      ((B ×ˢ C ×ˢ D).filter (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0)).card =
      ((B' ×ˢ C' ×ˢ D').filter (fun t : W × W × W => t.1 + t.2.1 + t.2.2 = 0)).card := by
    refine (Finset.card_bij
      (fun t _ => (u.out + t.1.1, v.out + t.2.1.1, (u.out + v.out) + t.2.2.1)) ?_ ?_ ?_).symm
    · intro t ht
      simp only [mem_filter, mem_product, B', C', D', shiftCoset, mem_univ, true_and] at ht ⊢
      refine ⟨⟨ht.1.1, ht.1.2.1, ht.1.2.2⟩, ?_⟩
      have hsum : t.1.1 + t.2.1.1 + t.2.2.1 = 0 := congrArg Subtype.val ht.2
      calc
        (u.out + t.1.1) + (v.out + t.2.1.1) + ((u.out + v.out) + t.2.2.1)
            = ((u.out + v.out) + (u.out + v.out)) + (t.1.1 + t.2.1.1 + t.2.2.1) := by abel
        _ = 0 + 0 := by rw [add_self_eq_zero_f2, hsum]
        _ = 0 := add_zero 0
    · intro t₁ _ t₂ _ heq
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext (Subtype.ext (add_left_cancel heq.1))
        (Prod.ext (Subtype.ext (add_left_cancel heq.2.1)) (Subtype.ext (add_left_cancel heq.2.2)))
    · intro t ht
      simp only [mem_filter, mem_product] at ht
      obtain ⟨⟨hx, hy, hz⟩, hzero⟩ := ht
      have hmx : t.1 + u.out ∈ W := by
        have hsub : Submodule.Quotient.mk (p := W) (t.1 - u.out) = 0 := by
          rw [Submodule.Quotient.mk_sub, mem_coset.mp (hB hx), mk_out, sub_self]
        have := (Submodule.Quotient.mk_eq_zero W).mp hsub
        rwa [sub_eq_add_neg, neg_eq_self_f2] at this
      have hmy : t.2.1 + v.out ∈ W := by
        have hsub : Submodule.Quotient.mk (p := W) (t.2.1 - v.out) = 0 := by
          rw [Submodule.Quotient.mk_sub, mem_coset.mp (hC hy), mk_out, sub_self]
        have := (Submodule.Quotient.mk_eq_zero W).mp hsub
        rwa [sub_eq_add_neg, neg_eq_self_f2] at this
      have hmz : t.2.2 + (u.out + v.out) ∈ W := by
        have hsub : Submodule.Quotient.mk (p := W) (t.2.2 - (u.out + v.out)) = 0 := by
          rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add, mem_coset.mp (hD hz),
              mk_out, mk_out, sub_self]
        have := (Submodule.Quotient.mk_eq_zero W).mp hsub
        rwa [sub_eq_add_neg, neg_eq_self_f2] at this
      have hax : u.out + (t.1 + u.out) = t.1 := by
        rw [add_comm t.1 u.out, ← add_assoc, add_self_eq_zero_f2, zero_add]
      have hay : v.out + (t.2.1 + v.out) = t.2.1 := by
        rw [add_comm t.2.1 v.out, ← add_assoc, add_self_eq_zero_f2, zero_add]
      have haz : (u.out + v.out) + (t.2.2 + (u.out + v.out)) = t.2.2 := by
        rw [add_comm t.2.2 (u.out + v.out), ← add_assoc, add_self_eq_zero_f2, zero_add]
      refine ⟨(⟨t.1 + u.out, hmx⟩, ⟨t.2.1 + v.out, hmy⟩, ⟨t.2.2 + (u.out + v.out), hmz⟩), ?_, ?_⟩
      · simp only [mem_filter, mem_product, B', C', D', shiftCoset, mem_univ, true_and, hax, hay, haz]
        refine ⟨⟨hx, hy, hz⟩, ?_⟩
        apply Subtype.ext
        change (t.1 + u.out) + (t.2.1 + v.out) + (t.2.2 + (u.out + v.out)) = 0
        calc
          (t.1 + u.out) + (t.2.1 + v.out) + (t.2.2 + (u.out + v.out))
              = (t.1 + t.2.1 + t.2.2) + ((u.out + v.out) + (u.out + v.out)) := by abel
          _ = 0 + 0 := by rw [hzero, add_self_eq_zero_f2]
          _ = 0 := add_zero 0
      · exact Prod.ext hax (Prod.ext hay haz)
  rw [hcard_eq]
  have hle := triple_sum_le_of_uniform B' C' D' hη hunif
  rw [hB', hC', hD'] at hle
  convert hle

/- Boxing data structure and energies -/

structure Boxing (G : Type*) [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] where
  W : Submodule (ZMod 2) G
  m : ℕ
  hm : 0 < m
  idxB : (G ⧸ W) × (G ⧸ W) → G → Fin m
  idxC : (G ⧸ W) × (G ⧸ W) → G → Fin m
  idxD : (G ⧸ W) × (G ⧸ W) → G → Fin m

noncomputable def partB (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) (i : Fin B.m) : Finset G :=
  (coset B.W uv.1).filter (fun x => B.idxB uv x = i)

noncomputable def partC (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) (j : Fin B.m) : Finset G :=
  (coset B.W uv.2).filter (fun y => B.idxC uv y = j)

noncomputable def partD (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) (k : Fin B.m) : Finset G :=
  (coset B.W (uv.1 + uv.2)).filter (fun z => B.idxD uv z = k)

lemma partB_subset (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) (i : Fin B.m) :
    partB B uv i ⊆ coset B.W uv.1 := filter_subset _ _

lemma partC_subset (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) (j : Fin B.m) :
    partC B uv j ⊆ coset B.W uv.2 := filter_subset _ _

lemma partD_subset (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) (k : Fin B.m) :
    partD B uv k ⊆ coset B.W (uv.1 + uv.2) := filter_subset _ _

lemma partB_disjoint (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    Pairwise (fun i₁ i₂ : Fin B.m => Disjoint (partB B uv i₁) (partB B uv i₂)) := by
  intro i₁ i₂ hne
  rw [Finset.disjoint_left]
  intro x h1 h2
  exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)

lemma partC_disjoint (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    Pairwise (fun j₁ j₂ : Fin B.m => Disjoint (partC B uv j₁) (partC B uv j₂)) := by
  intro j₁ j₂ hne
  rw [Finset.disjoint_left]
  intro x h1 h2
  exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)

lemma partD_disjoint (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    Pairwise (fun k₁ k₂ : Fin B.m => Disjoint (partD B uv k₁) (partD B uv k₂)) := by
  intro k₁ k₂ hne
  rw [Finset.disjoint_left]
  intro x h1 h2
  exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)

lemma biUnion_partB (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    (univ : Finset (Fin B.m)).biUnion (partB B uv) = coset B.W uv.1 := by
  ext x; simp [partB]

lemma biUnion_partC (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    (univ : Finset (Fin B.m)).biUnion (partC B uv) = coset B.W uv.2 := by
  ext x; simp [partC]

lemma biUnion_partD (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    (univ : Finset (Fin B.m)).biUnion (partD B uv) = coset B.W (uv.1 + uv.2) := by
  ext x; simp [partD]

lemma sum_card_partB (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    (∑ i : Fin B.m, ((partB B uv i).card : ℝ)) = (Fintype.card B.W : ℝ) := by
  have h : (coset B.W uv.1).card = ∑ i : Fin B.m, (partB B uv i).card := by
    rw [← biUnion_partB B uv, Finset.card_biUnion (fun i _ j _ hij => partB_disjoint B uv hij)]
  rw [card_coset] at h
  exact_mod_cast h.symm

lemma sum_card_partC (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    (∑ j : Fin B.m, ((partC B uv j).card : ℝ)) = (Fintype.card B.W : ℝ) := by
  have h : (coset B.W uv.2).card = ∑ j : Fin B.m, (partC B uv j).card := by
    rw [← biUnion_partC B uv, Finset.card_biUnion (fun i _ j _ hij => partC_disjoint B uv hij)]
  rw [card_coset] at h
  exact_mod_cast h.symm

lemma sum_card_partD (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    (∑ k : Fin B.m, ((partD B uv k).card : ℝ)) = (Fintype.card B.W : ℝ) := by
  have h : (coset B.W (uv.1 + uv.2)).card = ∑ k : Fin B.m, (partD B uv k).card := by
    rw [← biUnion_partD B uv, Finset.card_biUnion (fun i _ j _ hij => partD_disjoint B uv hij)]
  rw [card_coset] at h
  exact_mod_cast h.symm

def relBC (A : Finset (G × G)) (x y : G) : Prop := (x, y) ∈ A
def relBD (A : Finset (G × G)) (x z : G) : Prop := (x, x + z) ∈ A
def relCD (A : Finset (G × G)) (y z : G) : Prop := (y + z, y) ∈ A

noncomputable def boxE1 (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) : ℝ :=
  ∑ i : Fin B.m, (((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2

noncomputable def E1 (B : Boxing G) : ℝ :=
  (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2

noncomputable def pairEnergy {α β : Type*} (E : α → β → Prop) (X : Finset α) (Y : Finset β) : ℝ :=
  ((X.card : ℝ) * (Y.card : ℝ)) * (pairDensity E X Y) ^ 2

noncomputable def boxE2 (A : Finset (G × G)) (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) : ℝ :=
  ((∑ i : Fin B.m, ∑ j : Fin B.m, pairEnergy (relBC A) (partB B uv i) (partC B uv j)) +
   (∑ i : Fin B.m, ∑ k : Fin B.m, pairEnergy (relBD A) (partB B uv i) (partD B uv k)) +
   (∑ j : Fin B.m, ∑ k : Fin B.m, pairEnergy (relCD A) (partC B uv j) (partD B uv k))) /
    (3 * (Fintype.card B.W : ℝ) ^ 2)

noncomputable def E2 (A : Finset (G × G)) (B : Boxing G) : ℝ :=
  (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE2 A B uv) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2

lemma E1_nonneg (B : Boxing G) : 0 ≤ E1 B := by
  dsimp [E1, boxE1]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)

lemma E1_le_one (B : Boxing G) : E1 B ≤ 1 := by
  have hq : (0 : ℝ) < Fintype.card (G ⧸ B.W) := by exact_mod_cast card_quotient_pos B.W
  have hw : (0 : ℝ) < Fintype.card B.W := by exact_mod_cast card_submodule_pos B.W
  dsimp [E1]
  rw [div_le_one (pow_pos hq 2)]
  have hbox : ∀ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv ≤ 1 := by
    intro uv
    dsimp [boxE1]
    calc
      (∑ i : Fin B.m, (((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2)
          ≤ ∑ i : Fin B.m, ((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have hle : ((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ) ≤ 1 := by
                rw [div_le_one hw]
                have := Finset.card_le_card (partB_subset B uv i)
                rw [card_coset] at this
                exact_mod_cast this
              nlinarith [div_nonneg (Nat.cast_nonneg (partB B uv i).card) hw.le]
      _ = (∑ i : Fin B.m, ((partB B uv i).card : ℝ)) / (Fintype.card B.W : ℝ) := (Finset.sum_div _ _ _).symm
      _ = 1 := by rw [sum_card_partB, div_self hw.ne']
  calc
    (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) ≤ ∑ _uv : (G ⧸ B.W) × (G ⧸ B.W), (1 : ℝ) :=
      Finset.sum_le_sum fun uv _ => hbox uv
    _ = (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 := by simp [Fintype.card_prod, sq]

lemma E2_nonneg (A : Finset (G × G)) (B : Boxing G) : 0 ≤ E2 A B := by
  dsimp [E2, boxE2, pairEnergy]
  refine div_nonneg (Finset.sum_nonneg fun uv _ => div_nonneg ?_ (by positivity)) (sq_nonneg _)
  have h1 : 0 ≤ ∑ i : Fin B.m, ∑ j : Fin B.m,
      ((partB B uv i).card : ℝ) * (partC B uv j).card * pairDensity (relBC A) (partB B uv i) (partC B uv j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have h2 : 0 ≤ ∑ i : Fin B.m, ∑ k : Fin B.m,
      ((partB B uv i).card : ℝ) * (partD B uv k).card * pairDensity (relBD A) (partB B uv i) (partD B uv k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have h3 : 0 ≤ ∑ j : Fin B.m, ∑ k : Fin B.m,
      ((partC B uv j).card : ℝ) * (partD B uv k).card * pairDensity (relCD A) (partC B uv j) (partD B uv k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith

lemma E2_le_one (A : Finset (G × G)) (B : Boxing G) : E2 A B ≤ 1 := by
  have hq : (0 : ℝ) < Fintype.card (G ⧸ B.W) := by exact_mod_cast card_quotient_pos B.W
  have hw : (0 : ℝ) < Fintype.card B.W := by exact_mod_cast card_submodule_pos B.W
  dsimp only [E2]
  rw [div_le_one (pow_pos hq 2)]
  have hpe : ∀ (E : G → G → Prop) (X Y : Finset G),
      ((X.card : ℝ) * (Y.card : ℝ)) * (pairDensity E X Y) ^ 2 ≤ (X.card : ℝ) * (Y.card : ℝ) := by
    intro E X Y
    have hd0 := pairDensity_nonneg E X Y
    have hd1 := pairDensity_le_one E X Y
    have hsq : (pairDensity E X Y) ^ 2 ≤ 1 := by
      rw [sq]
      calc pairDensity E X Y * pairDensity E X Y ≤ 1 * 1 := mul_le_mul hd1 hd1 hd0 zero_le_one
        _ = 1 := one_mul 1
    calc ((X.card : ℝ) * (Y.card : ℝ)) * (pairDensity E X Y) ^ 2
        ≤ ((X.card : ℝ) * (Y.card : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = (X.card : ℝ) * (Y.card : ℝ) := mul_one _
  have hpair : ∀ (E : G → G → Prop) (P Q : Fin B.m → Finset G),
      (∑ i : Fin B.m, ((P i).card : ℝ)) = (Fintype.card B.W : ℝ) →
      (∑ j : Fin B.m, ((Q j).card : ℝ)) = (Fintype.card B.W : ℝ) →
      (∑ i : Fin B.m, ∑ j : Fin B.m, pairEnergy E (P i) (Q j)) ≤ (Fintype.card B.W : ℝ) ^ 2 := by
    intro E P Q hP hQ
    calc
      (∑ i : Fin B.m, ∑ j : Fin B.m, pairEnergy E (P i) (Q j))
          ≤ ∑ i : Fin B.m, ∑ j : Fin B.m, ((P i).card : ℝ) * (Q j).card :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpe E (P i) (Q j)
      _ = (∑ i : Fin B.m, ((P i).card : ℝ)) * (∑ j : Fin B.m, ((Q j).card : ℝ)) := by
            simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = (Fintype.card B.W : ℝ) ^ 2 := by rw [hP, hQ, sq]
  have hbox : ∀ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE2 A B uv ≤ 1 := by
    intro uv
    dsimp only [boxE2]
    rw [div_le_one (by positivity)]
    have hBC := hpair (relBC A) (partB B uv) (partC B uv) (sum_card_partB B uv) (sum_card_partC B uv)
    have hBD := hpair (relBD A) (partB B uv) (partD B uv) (sum_card_partB B uv) (sum_card_partD B uv)
    have hCD := hpair (relCD A) (partC B uv) (partD B uv) (sum_card_partC B uv) (sum_card_partD B uv)
    linarith only [hBC, hBD, hCD]
  calc
    (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE2 A B uv) ≤ ∑ _uv : (G ⧸ B.W) × (G ⧸ B.W), (1 : ℝ) :=
      Finset.sum_le_sum fun uv _ => hbox uv
    _ = (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 := by simp [Fintype.card_prod, sq]

/- Regularity conditions -/

def IsBoxUniform (ε : ℝ) (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) : Prop :=
  ∀ i : Fin B.m, ∀ r : Module.Dual (ZMod 2) B.W, r ≠ 0 →
    |fHat (indW (shiftCoset B.W uv.1 (partB B uv i))) r| ≤ ε / (B.m : ℝ) ^ 3

noncomputable def badWeightBC (ε : ℝ) (A : Finset (G × G)) (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) : ℝ :=
  (∑ i : Fin B.m, ∑ j : Fin B.m,
    if IsQuasirandom ε (relBC A) (partB B uv i) (partC B uv j) then (0 : ℝ)
    else ((partB B uv i).card : ℝ) * (partC B uv j).card) / (Fintype.card B.W : ℝ) ^ 2

noncomputable def badWeightBD (ε : ℝ) (A : Finset (G × G)) (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) : ℝ :=
  (∑ i : Fin B.m, ∑ k : Fin B.m,
    if IsQuasirandom ε (relBD A) (partB B uv i) (partD B uv k) then (0 : ℝ)
    else ((partB B uv i).card : ℝ) * (partD B uv k).card) / (Fintype.card B.W : ℝ) ^ 2

noncomputable def badWeightCD (ε : ℝ) (A : Finset (G × G)) (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) : ℝ :=
  (∑ j : Fin B.m, ∑ k : Fin B.m,
    if IsQuasirandom ε (relCD A) (partC B uv j) (partD B uv k) then (0 : ℝ)
    else ((partC B uv j).card : ℝ) * (partD B uv k).card) / (Fintype.card B.W : ℝ) ^ 2

def IsBoxQuasirandom (ε : ℝ) (A : Finset (G × G)) (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W)) : Prop :=
  badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv ≤ 3 * ε

def Cond1 (ε : ℝ) (B : Boxing G) : Prop :=
  (((univ : Finset ((G ⧸ B.W) × (G ⧸ B.W))).filter (fun uv => ¬ IsBoxUniform ε B uv)).card : ℝ) ≤
    ε * (Fintype.card (G ⧸ B.W) : ℝ) ^ 2

def Cond2 (ε : ℝ) (A : Finset (G × G)) (B : Boxing G) : Prop :=
  (((univ : Finset ((G ⧸ B.W) × (G ⧸ B.W))).filter (fun uv => ¬ IsBoxQuasirandom ε A B uv)).card : ℝ) ≤
    ε * (Fintype.card (G ⧸ B.W) : ℝ) ^ 2

noncomputable def codim (W : Submodule (ZMod 2) G) : ℕ :=
  Module.finrank (ZMod 2) (G ⧸ W)

lemma card_quotient_eq_two_pow_codim (W : Submodule (ZMod 2) G) :
    Fintype.card (G ⧸ W) = 2 ^ codim W := by
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := G ⧸ W)
  simpa [Nat.card_eq_fintype_card, ZMod.card, codim] using h

lemma card_submodule_eq_two_pow (W : Submodule (ZMod 2) G) :
    Fintype.card W = 2 ^ Module.finrank (ZMod 2) W := by
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
  simpa [Nat.card_eq_fintype_card, ZMod.card] using h

lemma finrank_add_codim (W : Submodule (ZMod 2) G) :
    Module.finrank (ZMod 2) W + codim W = Module.finrank (ZMod 2) G := by
  have h := Submodule.finrank_quotient_add_finrank W
  dsimp [codim]; omega

lemma codim_inf_le (W₁ W₂ : Submodule (ZMod 2) G) :
    codim (W₁ ⊓ W₂) ≤ codim W₁ + codim W₂ := by
  have h1 := finrank_add_codim W₁
  have h2 := finrank_add_codim W₂
  have h3 := finrank_add_codim (W₁ ⊓ W₂)
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  have h5 : Module.finrank (ZMod 2) (W₁ ⊔ W₂ : Submodule (ZMod 2) G) ≤ Module.finrank (ZMod 2) G :=
    Submodule.finrank_le (W₁ ⊔ W₂)
  omega

lemma codim_ker_map_le (W : Submodule (ZMod 2) G) (r : Module.Dual (ZMod 2) W) :
    codim ((LinearMap.ker r).map W.subtype) ≤ codim W + 1 := by
  have hmap : Module.finrank (ZMod 2) ((LinearMap.ker r).map W.subtype) =
      Module.finrank (ZMod 2) (LinearMap.ker r) := by
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective W.subtype (Submodule.subtype_injective W) (LinearMap.ker r)).symm
  have hrk := LinearMap.finrank_range_add_finrank_ker r
  have hrng : Module.finrank (ZMod 2) (LinearMap.range r) ≤ 1 := by
    calc Module.finrank (ZMod 2) (LinearMap.range r) ≤ Module.finrank (ZMod 2) (ZMod 2) := Submodule.finrank_le _
      _ = 1 := Module.finrank_self (ZMod 2)
  have hW := finrank_add_codim W
  have hK := finrank_add_codim ((LinearMap.ker r).map W.subtype)
  omega

end Boxing

section Refinements

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] [DecidableEq G]

lemma factor_quot_mk {T W : Submodule (ZMod 2) G} (hTW : T ≤ W) (x : G) :
    Submodule.factor hTW (Submodule.Quotient.mk (p := T) x) = Submodule.Quotient.mk (p := W) x :=
  rfl

lemma mk_eq_mk_iff {W : Submodule (ZMod 2) G} {x y : G} :
    Submodule.Quotient.mk (p := W) x = Submodule.Quotient.mk (p := W) y ↔ x + y ∈ W := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero W,
    sub_eq_add_neg, neg_eq_self_f2]

lemma sum_subtype_mem {α β : Type*} [Fintype α] [AddCommMonoid β]
    (s : Finset α) (f : α → β) :
    (∑ a : {x : α // x ∈ s}, f a.1) = ∑ x ∈ s, f x := by
  refine Finset.sum_bij (fun a _ => a.1) (fun a _ => a.2)
    (fun _ _ _ _ h => Subtype.ext h) (fun x hx => ⟨⟨x, hx⟩, mem_univ _, rfl⟩)
    (fun _ _ => rfl)

lemma sum2_sum2_comm {α β γ δ M : Type*} [AddCommMonoid M]
    (s : Finset α) (t : Finset β) (p : Finset γ) (q : Finset δ)
    (f : α → β → γ → δ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ p, ∑ d ∈ q, f a b c d) =
    ∑ c ∈ p, ∑ d ∈ q, ∑ a ∈ s, ∑ b ∈ t, f a b c d := by
  calc
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ p, ∑ d ∈ q, f a b c d)
        = ∑ a ∈ s, ∑ c ∈ p, ∑ b ∈ t, ∑ d ∈ q, f a b c d :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c ∈ p, ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ q, f a b c d := Finset.sum_comm
    _ = ∑ c ∈ p, ∑ a ∈ s, ∑ d ∈ q, ∑ b ∈ t, f a b c d :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c ∈ p, ∑ d ∈ q, ∑ a ∈ s, ∑ b ∈ t, f a b c d :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma sum_fiberwise_type {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid γ]
    (proj : α → β) (f : α → γ) :
    (∑ a : α, f a) = ∑ b : β, ∑ a ∈ (univ : Finset α).filter (fun a => proj a = b), f a := by
  have hpart : (univ : Finset α) = (univ : Finset β).biUnion (fun b => univ.filter (fun a => proj a = b)) := by
    ext a; simp
  have hdisj : Pairwise (fun b₁ b₂ : β =>
      Disjoint (univ.filter (fun a : α => proj a = b₁)) (univ.filter (fun a : α => proj a = b₂))) := by
    intro b₁ b₂ hne
    rw [Finset.disjoint_left]
    intro a h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [← Finset.sum_biUnion (fun b₁ _ b₂ _ hne => hdisj hne), ← hpart]

lemma sum_bool_filter {α β : Type*} [AddCommMonoid β]
    (s : Finset α) (g : α → Bool) (f : α → β) :
    (∑ a : Bool, ∑ x ∈ s.filter (fun x => g x = a), f x) = ∑ x ∈ s, f x := by
  rw [Fintype.sum_bool, ← Finset.sum_union]
  · congr 1
    ext x
    simp only [mem_union, mem_filter]
    cases g x <;> simp
  · rw [Finset.disjoint_left]
    intro x h1 h2
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    rw [e1] at e2
    exact Bool.noConfusion e2

noncomputable def fib {T W : Submodule (ZMod 2) G} (hTW : T ≤ W) (u : G ⧸ W) : Finset (G ⧸ T) :=
  univ.filter (fun u' => Submodule.factor hTW u' = u)

lemma mem_fib {T W : Submodule (ZMod 2) G} {hTW : T ≤ W} {u : G ⧸ W} {u' : G ⧸ T} :
    u' ∈ fib hTW u ↔ Submodule.factor hTW u' = u := by
  simp [fib]

lemma biUnion_fib_coset {T W : Submodule (ZMod 2) G} (hTW : T ≤ W) (u : G ⧸ W) :
    (fib hTW u).biUnion (coset T) = coset W u := by
  ext x
  simp only [mem_biUnion, mem_fib, mem_coset]
  constructor
  · rintro ⟨u', hu', rfl⟩
    simpa [factor_quot_mk] using hu'
  · intro hx
    refine ⟨Submodule.Quotient.mk x, ?_, rfl⟩
    simpa [factor_quot_mk] using hx

lemma card_fib_mul_card {T W : Submodule (ZMod 2) G} (hTW : T ≤ W) (u : G ⧸ W) :
    (fib hTW u).card * Fintype.card T = Fintype.card W := by
  have h1 : (coset W u).card = ∑ u' ∈ fib hTW u, (coset T u').card := by
    rw [← biUnion_fib_coset hTW u, Finset.card_biUnion (fun a _ b _ hab => coset_disjoint T hab)]
  simp_rw [card_coset, Finset.sum_const, smul_eq_mul] at h1
  exact h1.symm

lemma card_fib_pos {T W : Submodule (ZMod 2) G} (hTW : T ≤ W) (u : G ⧸ W) :
    0 < (fib hTW u).card := by
  have h := card_fib_mul_card hTW u
  have hW := card_submodule_pos W
  by_contra h0
  push Not at h0
  have heq : (fib hTW u).card = 0 := Nat.eq_zero_of_le_zero h0
  rw [heq, zero_mul] at h
  omega

lemma card_fib_eq {T W : Submodule (ZMod 2) G} (hTW : T ≤ W) (u v : G ⧸ W) :
    (fib hTW u).card = (fib hTW v).card := by
  have h1 := card_fib_mul_card hTW u
  have h2 := card_fib_mul_card hTW v
  exact Nat.eq_of_mul_eq_mul_right (card_submodule_pos T) (h1.trans h2.symm)

lemma card_fib_mul_quotient {T W : Submodule (ZMod 2) G} (hTW : T ≤ W) (u : G ⧸ W) :
    (fib hTW u).card * Fintype.card (G ⧸ W) = Fintype.card (G ⧸ T) := by
  have hT := card_quotient_mul_card T
  have hW := card_quotient_mul_card W
  have hf := card_fib_mul_card hTW u
  have hTpos : 0 < Fintype.card T := card_submodule_pos T
  have hmul : (fib hTW u).card * Fintype.card (G ⧸ W) * Fintype.card T =
      Fintype.card (G ⧸ T) * Fintype.card T := by
    calc
      (fib hTW u).card * Fintype.card (G ⧸ W) * Fintype.card T
          = Fintype.card (G ⧸ W) * ((fib hTW u).card * Fintype.card T) := by ring
      _ = Fintype.card (G ⧸ W) * Fintype.card W := by rw [hf]
      _ = Fintype.card G := hW
      _ = Fintype.card (G ⧸ T) * Fintype.card T := hT.symm
  exact Nat.eq_of_mul_eq_mul_right hTpos hmul

lemma sum_univ_eq_sum_fib {T W : Submodule (ZMod 2) G} (hTW : T ≤ W) {β : Type*} [AddCommMonoid β]
    (f : G ⧸ T → β) :
    (∑ u' : G ⧸ T, f u') = ∑ u : G ⧸ W, ∑ u' ∈ fib hTW u, f u' :=
  sum_fiberwise_type (Submodule.factor hTW) f

lemma sum_univ_prod_eq_sum_fib {T W : Submodule (ZMod 2) G} (hTW : T ≤ W) {β : Type*} [AddCommMonoid β]
    (f : (G ⧸ T) × (G ⧸ T) → β) :
    (∑ uv' : (G ⧸ T) × (G ⧸ T), f uv') =
      ∑ uv : (G ⧸ W) × (G ⧸ W), ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2, f (u', v') := by
  simp only [Fintype.sum_prod_type]
  rw [sum_univ_eq_sum_fib hTW]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h1 : (∑ u' ∈ fib hTW u, ∑ v' : G ⧸ T, f (u', v')) =
      ∑ u' ∈ fib hTW u, ∑ v : G ⧸ W, ∑ v' ∈ fib hTW v, f (u', v') :=
    Finset.sum_congr rfl fun u' _ => sum_univ_eq_sum_fib hTW (fun v' => f (u', v'))
  rw [h1, Finset.sum_comm]

noncomputable def refineSubspace (B : Boxing G) (T : Submodule (ZMod 2) G) (hTW : T ≤ B.W) : Boxing G where
  W := T
  m := B.m
  hm := B.hm
  idxB := fun uv => B.idxB (Submodule.factor hTW uv.1, Submodule.factor hTW uv.2)
  idxC := fun uv => B.idxC (Submodule.factor hTW uv.1, Submodule.factor hTW uv.2)
  idxD := fun uv => B.idxD (Submodule.factor hTW uv.1, Submodule.factor hTW uv.2)

lemma partB_refineSubspace (B : Boxing G) {T : Submodule (ZMod 2) G} (hTW : T ≤ B.W)
    (u' v' : G ⧸ T) (i : Fin B.m) :
    partB (refineSubspace B T hTW) (u', v') i =
      partB B (Submodule.factor hTW u', Submodule.factor hTW v') i ∩ coset T u' := by
  ext x
  change x ∈ (coset T u').filter (fun y => B.idxB (Submodule.factor hTW u', Submodule.factor hTW v') y = i) ↔
    x ∈ (coset B.W (Submodule.factor hTW u')).filter (fun y => B.idxB (Submodule.factor hTW u', Submodule.factor hTW v') y = i) ∩ coset T u'
  simp only [Finset.mem_inter, Finset.mem_filter, mem_coset]
  constructor
  · rintro ⟨hx, hi⟩
    refine ⟨⟨?_, hi⟩, hx⟩
    rw [← hx, factor_quot_mk]
  · rintro ⟨⟨_, hi⟩, hx⟩
    exact ⟨hx, hi⟩

lemma partC_refineSubspace (B : Boxing G) {T : Submodule (ZMod 2) G} (hTW : T ≤ B.W)
    (u' v' : G ⧸ T) (j : Fin B.m) :
    partC (refineSubspace B T hTW) (u', v') j =
      partC B (Submodule.factor hTW u', Submodule.factor hTW v') j ∩ coset T v' := by
  ext x
  change x ∈ (coset T v').filter (fun y => B.idxC (Submodule.factor hTW u', Submodule.factor hTW v') y = j) ↔
    x ∈ (coset B.W (Submodule.factor hTW v')).filter (fun y => B.idxC (Submodule.factor hTW u', Submodule.factor hTW v') y = j) ∩ coset T v'
  simp only [Finset.mem_inter, Finset.mem_filter, mem_coset]
  constructor
  · rintro ⟨hx, hj⟩
    refine ⟨⟨?_, hj⟩, hx⟩
    rw [← hx, factor_quot_mk]
  · rintro ⟨⟨_, hj⟩, hx⟩
    exact ⟨hx, hj⟩

lemma partD_refineSubspace (B : Boxing G) {T : Submodule (ZMod 2) G} (hTW : T ≤ B.W)
    (u' v' : G ⧸ T) (k : Fin B.m) :
    partD (refineSubspace B T hTW) (u', v') k =
      partD B (Submodule.factor hTW u', Submodule.factor hTW v') k ∩ coset T (u' + v') := by
  ext x
  change x ∈ (coset T (u' + v')).filter (fun y => B.idxD (Submodule.factor hTW u', Submodule.factor hTW v') y = k) ↔
    x ∈ (coset B.W (Submodule.factor hTW u' + Submodule.factor hTW v')).filter (fun y => B.idxD (Submodule.factor hTW u', Submodule.factor hTW v') y = k) ∩ coset T (u' + v')
  simp only [Finset.mem_inter, Finset.mem_filter, mem_coset]
  constructor
  · rintro ⟨hx, hk⟩
    refine ⟨⟨?_, hk⟩, hx⟩
    rw [← map_add, ← hx, factor_quot_mk]
  · rintro ⟨⟨_, hk⟩, hx⟩
    exact ⟨hx, hk⟩

lemma sum_boxE1_refineSubspace_ge (B : Boxing G) {T : Submodule (ZMod 2) G} (hTW : T ≤ B.W)
    (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    ((fib hTW uv.1).card : ℝ) * ((fib hTW uv.2).card : ℝ) * boxE1 B uv ≤
      ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2, boxE1 (refineSubspace B T hTW) (u', v') := by
  have hTpos : (0 : ℝ) < Fintype.card T := by exact_mod_cast card_submodule_pos T
  have hfu : ((fib hTW uv.1).card : ℝ) * (Fintype.card T : ℝ) = (Fintype.card B.W : ℝ) := by
    exact_mod_cast card_fib_mul_card hTW uv.1
  have hfu' : ((fib hTW uv.1).card : ℝ) = (Fintype.card B.W : ℝ) / (Fintype.card T : ℝ) :=
    eq_div_of_mul_eq hTpos.ne' hfu
  dsimp only [boxE1, refineSubspace]
  rw [Finset.mul_sum]
  have hswap :
      (∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
        ∑ i : Fin B.m, (((partB (refineSubspace B T hTW) (u', v') i).card : ℝ) / (Fintype.card T : ℝ)) ^ 2) =
      ∑ i : Fin B.m, ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
        (((partB (refineSubspace B T hTW) (u', v') i).card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
    trans (∑ u' ∈ fib hTW uv.1, ∑ i : Fin B.m, ∑ v' ∈ fib hTW uv.2,
      (((partB (refineSubspace B T hTW) (u', v') i).card : ℝ) / (Fintype.card T : ℝ)) ^ 2)
    · refine Finset.sum_congr rfl fun u' _ => Finset.sum_comm
    · exact Finset.sum_comm
  change _ ≤ ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
      ∑ i : Fin B.m, (((partB (refineSubspace B T hTW) (u', v') i).card : ℝ) / (Fintype.card T : ℝ)) ^ 2
  rw [hswap]
  refine Finset.sum_le_sum fun i _ => ?_
  have hpart : ∀ u' ∈ fib hTW uv.1, ∀ v' ∈ fib hTW uv.2,
      partB (refineSubspace B T hTW) (u', v') i = partB B uv i ∩ coset T u' := by
    intro u' hu' v' hv'
    rw [partB_refineSubspace, mem_fib.mp hu', mem_fib.mp hv']
  have hsum_v :
      (∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
        (((partB (refineSubspace B T hTW) (u', v') i).card : ℝ) / (Fintype.card T : ℝ)) ^ 2) =
      ((fib hTW uv.2).card : ℝ) *
        ∑ u' ∈ fib hTW uv.1, (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    have hconst : (∑ v' ∈ fib hTW uv.2,
        (((partB (refineSubspace B T hTW) (u', v') i).card : ℝ) / (Fintype.card T : ℝ)) ^ 2) =
        ∑ _v' ∈ fib hTW uv.2, (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 :=
      Finset.sum_congr rfl fun v' hv' => by rw [hpart u' hu' v' hv']
    rw [hconst, Finset.sum_const, nsmul_eq_mul]
  rw [hsum_v]
  let ι := {u' : G ⧸ T // u' ∈ fib hTW uv.1}
  have hvn := variance_nonneg (ι := ι) (coset B.W uv.1) (partB B uv i)
    (fun a => coset T a.1)
    (fun a b hab => coset_disjoint T (fun h => hab (Subtype.ext h)))
    (by
      ext x
      rw [← biUnion_fib_coset hTW uv.1]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩, fun ⟨a, ha, hx⟩ => ⟨⟨a, ha⟩, hx⟩⟩)
  have hinter : partB B uv i ∩ coset B.W uv.1 = partB B uv i :=
    Finset.inter_eq_left.mpr (partB_subset B uv i)
  rw [hinter, card_coset] at hvn
  have hrhs_vn :
      (∑ a : ι, ((coset T a.1).card : ℝ) * (((partB B uv i ∩ coset T a.1).card : ℝ) / ((coset T a.1).card : ℝ)) ^ 2) =
      (Fintype.card T : ℝ) * ∑ u' ∈ fib hTW uv.1,
        (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
    simp_rw [card_coset]
    rw [← Finset.mul_sum]
    congr 1
    exact sum_subtype_mem (fib hTW uv.1) (fun u' => (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2)
  rw [hrhs_vn] at hvn
  have hscale : ((fib hTW uv.1).card : ℝ) * ((fib hTW uv.2).card : ℝ) *
      (((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2 =
      ((fib hTW uv.2).card : ℝ) / (Fintype.card T : ℝ) *
        ((Fintype.card B.W : ℝ) * (((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2) := by
    rw [hfu']
    ring
  rw [hscale]
  calc
    ((fib hTW uv.2).card : ℝ) / (Fintype.card T : ℝ) *
        ((Fintype.card B.W : ℝ) * (((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2)
        ≤ ((fib hTW uv.2).card : ℝ) / (Fintype.card T : ℝ) *
            ((Fintype.card T : ℝ) * ∑ u' ∈ fib hTW uv.1,
              (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hvn (by positivity)
    _ = ((fib hTW uv.2).card : ℝ) *
          ∑ u' ∈ fib hTW uv.1, (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
          rw [← mul_assoc, div_mul_cancel₀ _ hTpos.ne']

lemma sum_boxE1_refineSubspace_inc (B : Boxing G) {T : Submodule (ZMod 2) G} (hTW : T ≤ B.W)
    (uv : (G ⧸ B.W) × (G ⧸ B.W)) (i₀ : Fin B.m)
    (r : Module.Dual (ZMod 2) B.W) (hr : r ≠ 0)
    (hTK : T ≤ (LinearMap.ker r).map B.W.subtype) :
    ((fib hTW uv.1).card : ℝ) * ((fib hTW uv.2).card : ℝ) *
      (boxE1 B uv + (fHat (indW (shiftCoset B.W uv.1 (partB B uv i₀))) r) ^ 2) ≤
      ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2, boxE1 (refineSubspace B T hTW) (u', v') := by
  have hTpos : (0 : ℝ) < Fintype.card T := by exact_mod_cast card_submodule_pos T
  have hfu : ((fib hTW uv.1).card : ℝ) * (Fintype.card T : ℝ) = (Fintype.card B.W : ℝ) := by
    exact_mod_cast card_fib_mul_card hTW uv.1
  have hfu' : ((fib hTW uv.1).card : ℝ) = (Fintype.card B.W : ℝ) / (Fintype.card T : ℝ) :=
    eq_div_of_mul_eq hTpos.ne' hfu
  let K : Submodule (ZMod 2) G := (LinearMap.ker r).map B.W.subtype
  have hKW : K ≤ B.W := Submodule.map_subtype_le B.W (LinearMap.ker r)
  have hKpos : (0 : ℝ) < Fintype.card K := by exact_mod_cast card_submodule_pos K
  have hex_a : ∃ a : B.W, r a = 1 := by
    have hex : ∃ a : B.W, r a ≠ 0 := by
      by_contra h
      push Not at h
      exact hr (LinearMap.ext fun a => by simpa using h a)
    obtain ⟨a, ha⟩ := hex
    rcases zmod2_eq_zero_or_one (r a) with h0 | h1
    · exact absurd h0 ha
    · exact ⟨a, h1⟩
  obtain ⟨a₀, ha₀⟩ := hex_a
  let U0 : Finset G := (coset B.W uv.1).filter (fun x => x + uv.1.out ∈ K)
  let U1 : Finset G := (coset B.W uv.1).filter (fun x => x + uv.1.out ∉ K)
  have hcoset_U0 : U0 = coset K (Submodule.Quotient.mk uv.1.out) := by
    ext x
    simp only [U0, mem_filter, mem_coset]
    constructor
    · rintro ⟨_, hK⟩
      exact mk_eq_mk_iff.mpr hK
    · intro hq
      have hadd : x + uv.1.out ∈ K := mk_eq_mk_iff.mp hq
      refine ⟨?_, hadd⟩
      have hqW : Submodule.Quotient.mk (p := B.W) x = Submodule.Quotient.mk (p := B.W) uv.1.out :=
        mk_eq_mk_iff.mpr (hKW hadd)
      simpa [mk_out] using hqW
  have hcoset_U1 : U1 = coset K (Submodule.Quotient.mk (uv.1.out + a₀.1)) := by
    ext x
    simp only [U1, mem_filter, mem_coset]
    constructor
    · rintro ⟨hxW, hnotK⟩
      have hx_memW : x + uv.1.out ∈ B.W := by
        have hq : Submodule.Quotient.mk (p := B.W) x = Submodule.Quotient.mk (p := B.W) uv.1.out := by
          rw [hxW, mk_out]
        exact mk_eq_mk_iff.mp hq
      have hr1 : r ⟨x + uv.1.out, hx_memW⟩ = 1 := by
        rcases zmod2_eq_zero_or_one (r ⟨x + uv.1.out, hx_memW⟩) with h0 | h1
        · exfalso; apply hnotK
          exact ⟨⟨x + uv.1.out, hx_memW⟩, h0, rfl⟩
        · exact h1
      have hmemK : x + (uv.1.out + a₀.1) ∈ K := by
        have heq : x + (uv.1.out + a₀.1) = (x + uv.1.out) + a₀.1 := by abel
        rw [heq]
        refine ⟨⟨x + uv.1.out, hx_memW⟩ + a₀, ?_, rfl⟩
        show r (⟨x + uv.1.out, hx_memW⟩ + a₀) = 0
        rw [map_add, hr1, ha₀]
        decide
      exact mk_eq_mk_iff.mpr hmemK
    · intro hq
      have hadd : (x + uv.1.out) + a₀.1 ∈ K := by
        have h1 : x + (uv.1.out + a₀.1) ∈ K := mk_eq_mk_iff.mp hq
        have heq : x + (uv.1.out + a₀.1) = (x + uv.1.out) + a₀.1 := by abel
        rwa [← heq]
      have hxW : x + uv.1.out ∈ B.W := by
        have h1 : (x + uv.1.out) + a₀.1 ∈ B.W := hKW hadd
        have h2 : ((x + uv.1.out) + a₀.1) + a₀.1 ∈ B.W := B.W.add_mem h1 a₀.2
        rwa [add_assoc, add_self_eq_zero_f2, add_zero] at h2
      refine ⟨?_, ?_⟩
      · have hqW : Submodule.Quotient.mk (p := B.W) x = Submodule.Quotient.mk (p := B.W) uv.1.out :=
          mk_eq_mk_iff.mpr hxW
        simpa [mk_out] using hqW
      · intro hK
        have haK : a₀.1 ∈ K := by
          have := K.add_mem hadd hK
          have heq : (x + uv.1.out) + a₀.1 + (x + uv.1.out) = a₀.1 := by
            rw [add_comm (x + uv.1.out) a₀.1, add_assoc, add_self_eq_zero_f2, add_zero]
          rwa [heq] at this
        obtain ⟨b, hbker, hbeq⟩ := haK
        have hba : b = a₀ := Subtype.ext hbeq
        rw [hba] at hbker
        have : (1 : ZMod 2) = 0 := ha₀.symm.trans hbker
        exact one_ne_zero this
  have hU0_card : U0.card = Fintype.card K := by rw [hcoset_U0, card_coset]
  have hU1_card : U1.card = Fintype.card K := by rw [hcoset_U1, card_coset]
  have hU01_disj : Disjoint U0 U1 := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
  have hU01_union : U0 ∪ U1 = coset B.W uv.1 := by
    ext x; simp only [U0, U1, Finset.mem_union, Finset.mem_filter]; tauto
  have h2K : 2 * Fintype.card K = Fintype.card B.W := by
    have h := Finset.card_union_of_disjoint hU01_disj
    rw [hU01_union, card_coset, hU0_card, hU1_card] at h
    omega
  let M := partB B uv i₀
  have hMsub : M ⊆ coset B.W uv.1 := partB_subset B uv i₀
  have hfHat_eq :
      fHat (indW (shiftCoset B.W uv.1 M)) r =
      (((M ∩ U0).card : ℝ) - ((M ∩ U1).card : ℝ)) / (Fintype.card B.W : ℝ) := by
    dsimp only [fHat]
    congr 1
    have hsum_split :
        (∑ a : B.W, indW (shiftCoset B.W uv.1 M) a * chi r a) =
        (((shiftCoset B.W uv.1 M).filter (fun a : B.W => r a = 0)).card : ℝ) -
        (((shiftCoset B.W uv.1 M).filter (fun a : B.W => r a ≠ 0)).card : ℝ) := by
      have h1 : ∀ a : B.W, indW (shiftCoset B.W uv.1 M) a * chi r a =
          (if a ∈ (shiftCoset B.W uv.1 M).filter (fun a : B.W => r a = 0) then (1 : ℝ) else 0) -
          (if a ∈ (shiftCoset B.W uv.1 M).filter (fun a : B.W => r a ≠ 0) then (1 : ℝ) else 0) := by
        intro a
        dsimp only [indW, chi]
        by_cases hm : a ∈ shiftCoset B.W uv.1 M <;> by_cases hr0 : r a = 0 <;> simp [hm, hr0]
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul, mul_one]
      have hf_eq : ∀ s : Finset B.W, (univ.filter (fun a : B.W => a ∈ s)) = s := fun s => by ext a; simp
      rw [hf_eq, hf_eq]
    rw [hsum_split]
    have hc0 : ((shiftCoset B.W uv.1 M).filter (fun a : B.W => r a = 0)).card = (M ∩ U0).card := by
      refine Finset.card_bij (fun a _ => uv.1.out + a.1) ?_ ?_ ?_
      · intro a ha
        simp only [mem_filter, shiftCoset, mem_univ, true_and, mem_inter, U0] at ha ⊢
        refine ⟨ha.1, hMsub ha.1, ?_⟩
        have heq : uv.1.out + a.1 + uv.1.out = a.1 := by
          rw [add_comm uv.1.out a.1, add_assoc, add_self_eq_zero_f2, add_zero]
        rw [heq]
        exact ⟨a, ha.2, rfl⟩
      · intro a₁ _ a₂ _ h; exact Subtype.ext (add_left_cancel h)
      · intro x hx
        simp only [mem_inter, U0, mem_filter] at hx
        obtain ⟨hxM, _, hxK⟩ := hx
        obtain ⟨a, haker, haeq⟩ := hxK
        have haeq' : a.1 = x + uv.1.out := haeq
        refine ⟨a, ?_, ?_⟩
        · simp only [mem_filter, shiftCoset, mem_univ, true_and]
          have hxa : uv.1.out + a.1 = x := by
            rw [haeq', add_comm x uv.1.out, ← add_assoc, add_self_eq_zero_f2, zero_add]
          exact ⟨hxa.symm ▸ hxM, haker⟩
        · rw [haeq', add_comm x uv.1.out, ← add_assoc, add_self_eq_zero_f2, zero_add]
    have hc1 : ((shiftCoset B.W uv.1 M).filter (fun a : B.W => r a ≠ 0)).card = (M ∩ U1).card := by
      refine Finset.card_bij (fun a _ => uv.1.out + a.1) ?_ ?_ ?_
      · intro a ha
        simp only [mem_filter, shiftCoset, mem_univ, true_and, mem_inter, U1] at ha ⊢
        refine ⟨ha.1, hMsub ha.1, ?_⟩
        have heq : uv.1.out + a.1 + uv.1.out = a.1 := by
          rw [add_comm uv.1.out a.1, add_assoc, add_self_eq_zero_f2, add_zero]
        rw [heq]
        rintro ⟨b, hbker, hbeq⟩
        have hba : b = a := Subtype.ext hbeq
        exact ha.2 (hba ▸ hbker)
      · intro a₁ _ a₂ _ h; exact Subtype.ext (add_left_cancel h)
      · intro x hx
        simp only [mem_inter, U1, mem_filter] at hx
        obtain ⟨hxM, hxC, hxnotK⟩ := hx
        have hmemW : x + uv.1.out ∈ B.W := by
          have hq : Submodule.Quotient.mk (p := B.W) x = Submodule.Quotient.mk (p := B.W) uv.1.out := by
            rw [mem_coset.mp hxC, mk_out]
          exact mk_eq_mk_iff.mp hq
        have hxa : uv.1.out + (x + uv.1.out) = x := by
          rw [add_comm x uv.1.out, ← add_assoc, add_self_eq_zero_f2, zero_add]
        refine ⟨⟨x + uv.1.out, hmemW⟩, ?_, hxa⟩
        simp only [mem_filter, shiftCoset, mem_univ, true_and]
        exact ⟨hxa.symm ▸ hxM, fun h0 => hxnotK ⟨⟨x + uv.1.out, hmemW⟩, h0, rfl⟩⟩
    rw [hc0, hc1]
  have hM_inc :
      (Fintype.card B.W : ℝ) * (((M.card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2 +
        (fHat (indW (shiftCoset B.W uv.1 M)) r) ^ 2) ≤
      (Fintype.card T : ℝ) * ∑ u' ∈ fib hTW uv.1,
        (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
    have hK_step :
        (Fintype.card B.W : ℝ) * (((M.card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2 +
          (fHat (indW (shiftCoset B.W uv.1 M)) r) ^ 2) =
        (Fintype.card K : ℝ) * (((M ∩ U0).card : ℝ) / (Fintype.card K : ℝ)) ^ 2 +
        (Fintype.card K : ℝ) * (((M ∩ U1).card : ℝ) / (Fintype.card K : ℝ)) ^ 2 := by
      have hMcard : (M.card : ℝ) = ((M ∩ U0).card : ℝ) + ((M ∩ U1).card : ℝ) := by
        have h1 : M = (M ∩ U0) ∪ (M ∩ U1) := by
          rw [← Finset.inter_union_distrib_left, hU01_union, Finset.inter_eq_left.mpr hMsub]
        have h2 : Disjoint (M ∩ U0) (M ∩ U1) := hU01_disj.mono inter_subset_right inter_subset_right
        have h3 := Finset.card_union_of_disjoint h2
        rw [← h1] at h3
        exact_mod_cast h3
      have h2Kr : 2 * (Fintype.card K : ℝ) = (Fintype.card B.W : ℝ) := by exact_mod_cast h2K
      rw [hfHat_eq, hMcard, ← h2Kr]
      field_simp [hKpos.ne']
      ring
    rw [hK_step]
    let q0 : G ⧸ K := Submodule.Quotient.mk uv.1.out
    let q1 : G ⧸ K := Submodule.Quotient.mk (uv.1.out + a₀.1)
    have hq01 : q0 ≠ q1 := by
      intro h
      have h0 : coset K q0 = coset K q1 := by rw [h]
      rw [← hcoset_U0, ← hcoset_U1] at h0
      have hne : U0.Nonempty := Finset.card_pos.mp (by rw [hU0_card]; exact card_submodule_pos K)
      obtain ⟨x, hx⟩ := hne
      exact (Finset.disjoint_left.mp hU01_disj hx) (h0 ▸ hx)
    have hfib_disj : Disjoint (fib hTK q0) (fib hTK q1) := by
      rw [Finset.disjoint_left]
      intro u' h0 h1
      exact hq01 ((mem_fib.mp h0).symm.trans (mem_fib.mp h1))
    have hfib_union : fib hTK q0 ∪ fib hTK q1 ⊆ fib hTW uv.1 := by
      intro u' hu'
      rw [mem_fib]
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T u'
      rw [factor_quot_mk]
      rcases Finset.mem_union.mp hu' with h0 | h1
      · have hxU0 : x ∈ U0 := by
          rw [hcoset_U0, mem_coset]
          simpa [factor_quot_mk] using mem_fib.mp h0
        exact mem_coset.mp ((Finset.mem_filter.mp hxU0).1)
      · have hxU1 : x ∈ U1 := by
          rw [hcoset_U1, mem_coset]
          have h1' := mem_fib.mp h1
          rwa [factor_quot_mk] at h1'
        exact mem_coset.mp ((Finset.mem_filter.mp hxU1).1)
    have hvn0 := variance_nonneg (ι := {u' : G ⧸ T // u' ∈ fib hTK q0}) (coset K q0) (M ∩ U0)
      (fun a => coset T a.1)
      (fun a b hab => coset_disjoint T (fun h => hab (Subtype.ext h)))
      (by
        ext x; simp only [mem_biUnion, mem_univ, true_and, Subtype.exists]
        rw [← biUnion_fib_coset hTK q0]; simp)
    have hvn1 := variance_nonneg (ι := {u' : G ⧸ T // u' ∈ fib hTK q1}) (coset K q1) (M ∩ U1)
      (fun a => coset T a.1)
      (fun a b hab => coset_disjoint T (fun h => hab (Subtype.ext h)))
      (by
        ext x; simp only [mem_biUnion, mem_univ, true_and, Subtype.exists]
        rw [← biUnion_fib_coset hTK q1]; simp)
    have h0sub : M ∩ U0 ⊆ coset K q0 := by rw [← hcoset_U0]; exact inter_subset_right
    have h1sub : M ∩ U1 ⊆ coset K q1 := by rw [← hcoset_U1]; exact inter_subset_right
    rw [Finset.inter_eq_left.mpr h0sub, card_coset] at hvn0
    rw [Finset.inter_eq_left.mpr h1sub, card_coset] at hvn1
    have hsimp0 : ∀ u' ∈ fib hTK q0, (M ∩ U0) ∩ coset T u' = M ∩ coset T u' := by
      intro u' hu'
      have hsub : coset T u' ⊆ U0 := by
        rw [hcoset_U0, ← biUnion_fib_coset hTK q0]
        exact Finset.subset_biUnion_of_mem _ hu'
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hsub]
    have hsimp1 : ∀ u' ∈ fib hTK q1, (M ∩ U1) ∩ coset T u' = M ∩ coset T u' := by
      intro u' hu'
      have hsub : coset T u' ⊆ U1 := by
        rw [hcoset_U1, ← biUnion_fib_coset hTK q1]
        exact Finset.subset_biUnion_of_mem _ hu'
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hsub]
    have hr0 :
        (∑ a : {u' : G ⧸ T // u' ∈ fib hTK q0},
          ((coset T a.1).card : ℝ) * ((((M ∩ U0) ∩ coset T a.1).card : ℝ) / ((coset T a.1).card : ℝ)) ^ 2) =
        (Fintype.card T : ℝ) * ∑ u' ∈ fib hTK q0,
          (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
      simp_rw [card_coset]
      rw [← Finset.mul_sum]
      congr 1
      have hcon : ∀ a : {u' : G ⧸ T // u' ∈ fib hTK q0},
          ((((M ∩ U0) ∩ coset T a.1).card : ℝ) / (Fintype.card T : ℝ)) ^ 2 =
          (((M ∩ coset T a.1).card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := fun a => by rw [hsimp0 a.1 a.2]
      simp_rw [hcon]
      exact sum_subtype_mem (fib hTK q0) (fun u' => (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2)
    have hr1 :
        (∑ a : {u' : G ⧸ T // u' ∈ fib hTK q1},
          ((coset T a.1).card : ℝ) * ((((M ∩ U1) ∩ coset T a.1).card : ℝ) / ((coset T a.1).card : ℝ)) ^ 2) =
        (Fintype.card T : ℝ) * ∑ u' ∈ fib hTK q1,
          (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
      simp_rw [card_coset]
      rw [← Finset.mul_sum]
      congr 1
      have hcon : ∀ a : {u' : G ⧸ T // u' ∈ fib hTK q1},
          ((((M ∩ U1) ∩ coset T a.1).card : ℝ) / (Fintype.card T : ℝ)) ^ 2 =
          (((M ∩ coset T a.1).card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := fun a => by rw [hsimp1 a.1 a.2]
      simp_rw [hcon]
      exact sum_subtype_mem (fib hTK q1) (fun u' => (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2)
    rw [hr0] at hvn0
    rw [hr1] at hvn1
    calc
      (Fintype.card K : ℝ) * (((M ∩ U0).card : ℝ) / (Fintype.card K : ℝ)) ^ 2 +
        (Fintype.card K : ℝ) * (((M ∩ U1).card : ℝ) / (Fintype.card K : ℝ)) ^ 2
          ≤ (Fintype.card T : ℝ) * ∑ u' ∈ fib hTK q0, (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 +
            (Fintype.card T : ℝ) * ∑ u' ∈ fib hTK q1, (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 :=
              add_le_add hvn0 hvn1
      _ = (Fintype.card T : ℝ) * ∑ u' ∈ fib hTK q0 ∪ fib hTK q1,
            (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
              rw [← mul_add, Finset.sum_union hfib_disj]
      _ ≤ (Fintype.card T : ℝ) * ∑ u' ∈ fib hTW uv.1,
            (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum_of_subset_of_nonneg hfib_union (fun _ _ _ => sq_nonneg _)) hTpos.le
  have hswap :
      (∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
        boxE1 (refineSubspace B T hTW) (u', v')) =
      ∑ i : Fin B.m, ((fib hTW uv.2).card : ℝ) *
        ∑ u' ∈ fib hTW uv.1, (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
    dsimp only [boxE1]
    trans (∑ u' ∈ fib hTW uv.1, ∑ i : Fin B.m, ∑ v' ∈ fib hTW uv.2,
      (((partB (refineSubspace B T hTW) (u', v') i).card : ℝ) / (Fintype.card T : ℝ)) ^ 2)
    · refine Finset.sum_congr rfl fun u' _ => Finset.sum_comm
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u' hu' => ?_
      have hconst : (∑ v' ∈ fib hTW uv.2,
          (((partB (refineSubspace B T hTW) (u', v') i).card : ℝ) / (Fintype.card T : ℝ)) ^ 2) =
          ∑ _v' ∈ fib hTW uv.2, (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 :=
        Finset.sum_congr rfl fun v' hv' => by
          rw [partB_refineSubspace, mem_fib.mp hu', mem_fib.mp hv']
      rw [hconst, Finset.sum_const, nsmul_eq_mul]
  rw [hswap]
  have hterm_ge : ∀ i : Fin B.m,
      ((fib hTW uv.1).card : ℝ) * ((fib hTW uv.2).card : ℝ) *
        ((((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2 +
          if i = i₀ then (fHat (indW (shiftCoset B.W uv.1 M)) r) ^ 2 else 0) ≤
      ((fib hTW uv.2).card : ℝ) *
        ∑ u' ∈ fib hTW uv.1, (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      rw [if_pos rfl]
      have hscale :
          ((fib hTW uv.1).card : ℝ) * ((fib hTW uv.2).card : ℝ) *
            (((M.card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2 + (fHat (indW (shiftCoset B.W uv.1 M)) r) ^ 2) =
          ((fib hTW uv.2).card : ℝ) / (Fintype.card T : ℝ) *
            ((Fintype.card B.W : ℝ) * (((M.card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2 +
              (fHat (indW (shiftCoset B.W uv.1 M)) r) ^ 2)) := by
        rw [hfu']; ring
      rw [hscale]
      calc
        ((fib hTW uv.2).card : ℝ) / (Fintype.card T : ℝ) *
            ((Fintype.card B.W : ℝ) * (((M.card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2 +
              (fHat (indW (shiftCoset B.W uv.1 M)) r) ^ 2))
            ≤ ((fib hTW uv.2).card : ℝ) / (Fintype.card T : ℝ) *
              ((Fintype.card T : ℝ) * ∑ u' ∈ fib hTW uv.1,
                (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2) :=
              mul_le_mul_of_nonneg_left hM_inc (by positivity)
        _ = ((fib hTW uv.2).card : ℝ) *
              ∑ u' ∈ fib hTW uv.1, (((M ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
              rw [← mul_assoc, div_mul_cancel₀ _ hTpos.ne']
    · rw [if_neg hi, add_zero]
      let ι := {u' : G ⧸ T // u' ∈ fib hTW uv.1}
      have hvn := variance_nonneg (ι := ι) (coset B.W uv.1) (partB B uv i)
        (fun a => coset T a.1)
        (fun a b hab => coset_disjoint T (fun h => hab (Subtype.ext h)))
        (by
          ext x
          rw [← biUnion_fib_coset hTW uv.1]
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
          exact ⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩, fun ⟨a, ha, hx⟩ => ⟨⟨a, ha⟩, hx⟩⟩)
      rw [Finset.inter_eq_left.mpr (partB_subset B uv i), card_coset] at hvn
      have hrhs_vn :
          (∑ a : ι, ((coset T a.1).card : ℝ) * (((partB B uv i ∩ coset T a.1).card : ℝ) / ((coset T a.1).card : ℝ)) ^ 2) =
          (Fintype.card T : ℝ) * ∑ u' ∈ fib hTW uv.1,
            (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
        simp_rw [card_coset]; rw [← Finset.mul_sum]; congr 1
        exact sum_subtype_mem (fib hTW uv.1) (fun u' => (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2)
      rw [hrhs_vn] at hvn
      have hscale : ((fib hTW uv.1).card : ℝ) * ((fib hTW uv.2).card : ℝ) *
          (((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2 =
          ((fib hTW uv.2).card : ℝ) / (Fintype.card T : ℝ) *
            ((Fintype.card B.W : ℝ) * (((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2) := by
        rw [hfu']; ring
      rw [hscale]
      calc
        ((fib hTW uv.2).card : ℝ) / (Fintype.card T : ℝ) *
            ((Fintype.card B.W : ℝ) * (((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2)
            ≤ ((fib hTW uv.2).card : ℝ) / (Fintype.card T : ℝ) *
              ((Fintype.card T : ℝ) * ∑ u' ∈ fib hTW uv.1,
                (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2) :=
              mul_le_mul_of_nonneg_left hvn (by positivity)
        _ = ((fib hTW uv.2).card : ℝ) *
              ∑ u' ∈ fib hTW uv.1, (((partB B uv i ∩ coset T u').card : ℝ) / (Fintype.card T : ℝ)) ^ 2 := by
              rw [← mul_assoc, div_mul_cancel₀ _ hTpos.ne']
  have hsum_lhs :
      (∑ i : Fin B.m, ((fib hTW uv.1).card : ℝ) * ((fib hTW uv.2).card : ℝ) *
        ((((partB B uv i).card : ℝ) / (Fintype.card B.W : ℝ)) ^ 2 +
          if i = i₀ then (fHat (indW (shiftCoset B.W uv.1 M)) r) ^ 2 else 0)) =
      ((fib hTW uv.1).card : ℝ) * ((fib hTW uv.2).card : ℝ) *
        (boxE1 B uv + (fHat (indW (shiftCoset B.W uv.1 M)) r) ^ 2) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp [boxE1]
  rw [← hsum_lhs]
  exact Finset.sum_le_sum fun i _ => hterm_ge i

lemma E1_refineSubspace_ge (B : Boxing G) {T : Submodule (ZMod 2) G} (hTW : T ≤ B.W) :
    E1 B ≤ E1 (refineSubspace B T hTW) := by
  have hqW : (0 : ℝ) < Fintype.card (G ⧸ B.W) := by exact_mod_cast card_quotient_pos B.W
  let f : ℝ := ((fib hTW (0 : G ⧸ B.W)).card : ℝ)
  have hfpos : 0 < f := by dsimp only [f]; exact_mod_cast card_fib_pos hTW 0
  have hfq : f * (Fintype.card (G ⧸ B.W) : ℝ) = (Fintype.card (G ⧸ T) : ℝ) := by
    dsimp only [f]; exact_mod_cast card_fib_mul_quotient hTW 0
  have hfeq : ∀ u : G ⧸ B.W, ((fib hTW u).card : ℝ) = f := fun u => by
    dsimp only [f]; exact_mod_cast card_fib_eq hTW u 0
  change (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 ≤
    (∑ uv' : (G ⧸ T) × (G ⧸ T), boxE1 (refineSubspace B T hTW) uv') / (Fintype.card (G ⧸ T) : ℝ) ^ 2
  have hrew := sum_univ_prod_eq_sum_fib hTW (fun uv' : (G ⧸ T) × (G ⧸ T) => boxE1 (refineSubspace B T hTW) uv')
  rw [hrew]
  have hsum :
      f ^ 2 * (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) ≤
      ∑ uv : (G ⧸ B.W) × (G ⧸ B.W), ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
        boxE1 (refineSubspace B T hTW) (u', v') := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun uv _ => ?_
    have h := sum_boxE1_refineSubspace_ge B hTW uv
    rw [hfeq uv.1, hfeq uv.2, ← sq] at h
    exact h
  calc
    (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2
        = (f ^ 2 * ∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) / (Fintype.card (G ⧸ T) : ℝ) ^ 2 := by
            rw [← hfq]
            field_simp [hfpos.ne', hqW.ne']
    _ ≤ (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
          boxE1 (refineSubspace B T hTW) (u', v')) / (Fintype.card (G ⧸ T) : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hsum (sq_nonneg _)

/- Pair energy under product partitions and subspace refinement for E2 -/

lemma pairEnergy_le_sum_partition {α β ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq α] [DecidableEq β]
    (E : α → β → Prop) (X : Finset α) (Y : Finset β)
    (P : ι → Finset α) (Q : κ → Finset β)
    (hPdisj : Pairwise (fun i₁ i₂ => Disjoint (P i₁) (P i₂)))
    (hPcov : univ.biUnion P = X)
    (hQdisj : Pairwise (fun j₁ j₂ => Disjoint (Q j₁) (Q j₂)))
    (hQcov : univ.biUnion Q = Y) :
    pairEnergy E X Y ≤ ∑ i : ι, ∑ j : κ, pairEnergy E (P i) (Q j) := by
  let U : Finset (α × β) := X ×ˢ Y
  let M : Finset (α × β) := U.filter (fun p => E p.1 p.2)
  let R : ι × κ → Finset (α × β) := fun ik => P ik.1 ×ˢ Q ik.2
  have hRdisj : Pairwise (fun a b : ι × κ => Disjoint (R a) (R b)) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro p ha hb
    simp only [R, mem_product] at ha hb
    by_cases h1 : a.1 = b.1
    · have h2 : a.2 ≠ b.2 := fun h2 => hab (Prod.ext h1 h2)
      exact Finset.disjoint_left.mp (hQdisj h2) ha.2 hb.2
    · exact Finset.disjoint_left.mp (hPdisj h1) ha.1 hb.1
  have hRcov : (univ : Finset (ι × κ)).biUnion R = U := by
    ext ⟨x, y⟩
    simp only [R, U, mem_biUnion, mem_univ, true_and, mem_product, Prod.exists, ← hPcov, ← hQcov]
    constructor
    · rintro ⟨i, j, hx, hy⟩; exact ⟨⟨i, hx⟩, ⟨j, hy⟩⟩
    · rintro ⟨⟨i, hx⟩, ⟨j, hy⟩⟩; exact ⟨i, j, hx, hy⟩
  have hvn := variance_nonneg U M R hRdisj hRcov
  have hMU : M ∩ U = M := Finset.inter_eq_left.mpr (filter_subset _ _)
  have hlhs : (U.card : ℝ) * (((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2 = pairEnergy E X Y := by
    rw [hMU]
    dsimp only [pairEnergy, pairDensity, edgeCount, U, M]
    rw [Finset.card_product, Nat.cast_mul]
  have hMR : ∀ a : ι × κ, M ∩ R a = (R a).filter (fun p => E p.1 p.2) := by
    intro a
    have hsub : R a ⊆ U := by
      rw [← hRcov]
      exact Finset.subset_biUnion_of_mem R (mem_univ a)
    ext p
    simp only [M, mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨_, hpE⟩, hpR⟩; exact ⟨hpR, hpE⟩
    · rintro ⟨hpR, hpE⟩; exact ⟨⟨hsub hpR, hpE⟩, hpR⟩
  have hrhs :
      (∑ a : ι × κ, ((R a).card : ℝ) * (((M ∩ R a).card : ℝ) / ((R a).card : ℝ)) ^ 2) =
      ∑ i : ι, ∑ j : κ, pairEnergy E (P i) (Q j) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hMR (i, j)]
    dsimp only [pairEnergy, pairDensity, edgeCount, R]
    rw [Finset.card_product, Nat.cast_mul]
  rw [hlhs, hrhs] at hvn
  exact hvn

lemma pairEnergy_le_sum_fib_inter {T W : Submodule (ZMod 2) G} (hTW : T ≤ W)
    (E : G → G → Prop) {u v : G ⧸ W} {X Y : Finset G}
    (hX : X ⊆ coset W u) (hY : Y ⊆ coset W v) :
    pairEnergy E X Y ≤
      ∑ u' ∈ fib hTW u, ∑ v' ∈ fib hTW v, pairEnergy E (X ∩ coset T u') (Y ∩ coset T v') := by
  let ι := {u' : G ⧸ T // u' ∈ fib hTW u}
  let κ := {v' : G ⧸ T // v' ∈ fib hTW v}
  have h := pairEnergy_le_sum_partition (ι := ι) (κ := κ) E X Y
    (fun a => X ∩ coset T a.1) (fun b => Y ∩ coset T b.1)
    (fun a b hab => (coset_disjoint T (fun h => hab (Subtype.ext h))).mono inter_subset_right inter_subset_right)
    (by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · rintro ⟨_, hx, _⟩; exact hx
      · intro hx
        have hxc : x ∈ (fib hTW u).biUnion (coset T) := by rw [biUnion_fib_coset]; exact hX hx
        obtain ⟨u', hu', hxu'⟩ := Finset.mem_biUnion.mp hxc
        exact ⟨⟨u', hu'⟩, hx, hxu'⟩)
    (fun a b hab => (coset_disjoint T (fun h => hab (Subtype.ext h))).mono inter_subset_right inter_subset_right)
    (by
      ext y
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · rintro ⟨_, hy, _⟩; exact hy
      · intro hy
        have hyc : y ∈ (fib hTW v).biUnion (coset T) := by rw [biUnion_fib_coset]; exact hY hy
        obtain ⟨v', hv', hyv'⟩ := Finset.mem_biUnion.mp hyc
        exact ⟨⟨v', hv'⟩, hy, hyv'⟩)
  have hrhs :
      (∑ a : ι, ∑ b : κ, pairEnergy E (X ∩ coset T a.1) (Y ∩ coset T b.1)) =
      ∑ u' ∈ fib hTW u, ∑ v' ∈ fib hTW v, pairEnergy E (X ∩ coset T u') (Y ∩ coset T v') := by
    have h1 : ∀ a : ι, (∑ b : κ, pairEnergy E (X ∩ coset T a.1) (Y ∩ coset T b.1)) =
        ∑ v' ∈ fib hTW v, pairEnergy E (X ∩ coset T a.1) (Y ∩ coset T v') := fun a =>
      sum_subtype_mem (fib hTW v) (fun v' => pairEnergy E (X ∩ coset T a.1) (Y ∩ coset T v'))
    simp_rw [h1]
    exact sum_subtype_mem (fib hTW u) (fun u' => ∑ v' ∈ fib hTW v, pairEnergy E (X ∩ coset T u') (Y ∩ coset T v'))
  rwa [hrhs] at h

lemma sum_boxE2_refineSubspace_ge (A : Finset (G × G)) (B : Boxing G)
    {T : Submodule (ZMod 2) G} (hTW : T ≤ B.W) (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    ((fib hTW uv.1).card : ℝ) * ((fib hTW uv.2).card : ℝ) * boxE2 A B uv ≤
      ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2, boxE2 A (refineSubspace B T hTW) (u', v') := by
  have hTpos : (0 : ℝ) < Fintype.card T := by exact_mod_cast card_submodule_pos T
  have hWpos : (0 : ℝ) < Fintype.card B.W := by exact_mod_cast card_submodule_pos B.W
  have hfu : ((fib hTW uv.1).card : ℝ) = (Fintype.card B.W : ℝ) / (Fintype.card T : ℝ) :=
    eq_div_of_mul_eq hTpos.ne' (by exact_mod_cast card_fib_mul_card hTW uv.1)
  have hfv : ((fib hTW uv.2).card : ℝ) = (Fintype.card B.W : ℝ) / (Fintype.card T : ℝ) :=
    eq_div_of_mul_eq hTpos.ne' (by exact_mod_cast card_fib_mul_card hTW uv.2)
  let B' := refineSubspace B T hTW
  have hlhs_eq :
      ((fib hTW uv.1).card : ℝ) * ((fib hTW uv.2).card : ℝ) * boxE2 A B uv =
      ((∑ i : Fin B.m, ∑ j : Fin B.m, pairEnergy (relBC A) (partB B uv i) (partC B uv j)) +
       (∑ i : Fin B.m, ∑ k : Fin B.m, pairEnergy (relBD A) (partB B uv i) (partD B uv k)) +
       (∑ j : Fin B.m, ∑ k : Fin B.m, pairEnergy (relCD A) (partC B uv j) (partD B uv k))) /
        (3 * (Fintype.card T : ℝ) ^ 2) := by
    dsimp only [boxE2]
    rw [hfu, hfv]
    field_simp [hTpos.ne', hWpos.ne']
  have hrhs_eq :
      (∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2, boxE2 A B' (u', v')) =
      ((∑ i : Fin B.m, ∑ j : Fin B.m, ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
          pairEnergy (relBC A) (partB B' (u', v') i) (partC B' (u', v') j)) +
       (∑ i : Fin B.m, ∑ k : Fin B.m, ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
          pairEnergy (relBD A) (partB B' (u', v') i) (partD B' (u', v') k)) +
       (∑ j : Fin B.m, ∑ k : Fin B.m, ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
          pairEnergy (relCD A) (partC B' (u', v') j) (partD B' (u', v') k))) /
        (3 * (Fintype.card T : ℝ) ^ 2) := by
    dsimp only [boxE2, B', refineSubspace]
    simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
    congr 1
    congr 1
    · congr 1
      · exact sum2_sum2_comm (fib hTW uv.1) (fib hTW uv.2) univ univ _
      · exact sum2_sum2_comm (fib hTW uv.1) (fib hTW uv.2) univ univ _
    · exact sum2_sum2_comm (fib hTW uv.1) (fib hTW uv.2) univ univ _
  rw [hlhs_eq, hrhs_eq]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hBC :
      (∑ i : Fin B.m, ∑ j : Fin B.m, pairEnergy (relBC A) (partB B uv i) (partC B uv j)) ≤
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
        pairEnergy (relBC A) (partB B' (u', v') i) (partC B' (u', v') j) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hcongr :
        (∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
          pairEnergy (relBC A) (partB B' (u', v') i) (partC B' (u', v') j)) =
        ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
          pairEnergy (relBC A) (partB B uv i ∩ coset T u') (partC B uv j ∩ coset T v') := by
      refine Finset.sum_congr rfl fun u' hu' => Finset.sum_congr rfl fun v' hv' => ?_
      dsimp only [B']
      rw [partB_refineSubspace, partC_refineSubspace, mem_fib.mp hu', mem_fib.mp hv']
    rw [hcongr]
    exact pairEnergy_le_sum_fib_inter hTW (relBC A) (partB_subset B uv i) (partC_subset B uv j)
  have hBD :
      (∑ i : Fin B.m, ∑ k : Fin B.m, pairEnergy (relBD A) (partB B uv i) (partD B uv k)) ≤
      ∑ i : Fin B.m, ∑ k : Fin B.m, ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
        pairEnergy (relBD A) (partB B' (u', v') i) (partD B' (u', v') k) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
    have hcongr :
        (∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
          pairEnergy (relBD A) (partB B' (u', v') i) (partD B' (u', v') k)) =
        ∑ u' ∈ fib hTW uv.1, ∑ w' ∈ fib hTW (uv.1 + uv.2),
          pairEnergy (relBD A) (partB B uv i ∩ coset T u') (partD B uv k ∩ coset T w') := by
      refine Finset.sum_congr rfl fun u' hu' => ?_
      have hinner :
          (∑ v' ∈ fib hTW uv.2,
            pairEnergy (relBD A) (partB B' (u', v') i) (partD B' (u', v') k)) =
          ∑ v' ∈ fib hTW uv.2,
            pairEnergy (relBD A) (partB B uv i ∩ coset T u') (partD B uv k ∩ coset T (u' + v')) := by
        refine Finset.sum_congr rfl fun v' hv' => ?_
        dsimp only [B']
        rw [partB_refineSubspace, partD_refineSubspace, mem_fib.mp hu', mem_fib.mp hv']
      rw [hinner]
      refine Finset.sum_bij (fun v' _ => u' + v') ?_ ?_ ?_ ?_
      · intro v' hv'
        rw [mem_fib, map_add, mem_fib.mp hu', mem_fib.mp hv']
      · intro v₁ _ v₂ _ h; exact add_left_cancel h
      · intro w' hw'
        refine ⟨u' + w', ?_, ?_⟩
        · rw [mem_fib, map_add, mem_fib.mp hu', mem_fib.mp hw', ← add_assoc, add_self_eq_zero_f2, zero_add]
        · rw [← add_assoc, add_self_eq_zero_f2, zero_add]
      · intro _ _; rfl
    rw [hcongr]
    exact pairEnergy_le_sum_fib_inter hTW (relBD A) (partB_subset B uv i) (partD_subset B uv k)
  have hCD :
      (∑ j : Fin B.m, ∑ k : Fin B.m, pairEnergy (relCD A) (partC B uv j) (partD B uv k)) ≤
      ∑ j : Fin B.m, ∑ k : Fin B.m, ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
        pairEnergy (relCD A) (partC B' (u', v') j) (partD B' (u', v') k) := by
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
    have hcongr :
        (∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
          pairEnergy (relCD A) (partC B' (u', v') j) (partD B' (u', v') k)) =
        ∑ v' ∈ fib hTW uv.2, ∑ w' ∈ fib hTW (uv.1 + uv.2),
          pairEnergy (relCD A) (partC B uv j ∩ coset T v') (partD B uv k ∩ coset T w') := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v' hv' => ?_
      have hinner :
          (∑ u' ∈ fib hTW uv.1,
            pairEnergy (relCD A) (partC B' (u', v') j) (partD B' (u', v') k)) =
          ∑ u' ∈ fib hTW uv.1,
            pairEnergy (relCD A) (partC B uv j ∩ coset T v') (partD B uv k ∩ coset T (u' + v')) := by
        refine Finset.sum_congr rfl fun u' hu' => ?_
        dsimp only [B']
        rw [partC_refineSubspace, partD_refineSubspace, mem_fib.mp hu', mem_fib.mp hv']
      rw [hinner]
      refine Finset.sum_bij (fun u' _ => u' + v') ?_ ?_ ?_ ?_
      · intro u' hu'
        rw [mem_fib, map_add, mem_fib.mp hu', mem_fib.mp hv']
      · intro u₁ _ u₂ _ h; exact add_right_cancel h
      · intro w' hw'
        refine ⟨w' + v', ?_, ?_⟩
        · rw [mem_fib, map_add, mem_fib.mp hw', mem_fib.mp hv', add_assoc, add_self_eq_zero_f2, add_zero]
        · rw [add_assoc, add_self_eq_zero_f2, add_zero]
      · intro _ _; rfl
    rw [hcongr]
    exact pairEnergy_le_sum_fib_inter hTW (relCD A) (partC_subset B uv j) (partD_subset B uv k)
  exact add_le_add (add_le_add hBC hBD) hCD

lemma E2_refineSubspace_ge (A : Finset (G × G)) (B : Boxing G)
    {T : Submodule (ZMod 2) G} (hTW : T ≤ B.W) :
    E2 A B ≤ E2 A (refineSubspace B T hTW) := by
  have hqW : (0 : ℝ) < Fintype.card (G ⧸ B.W) := by exact_mod_cast card_quotient_pos B.W
  let f : ℝ := ((fib hTW (0 : G ⧸ B.W)).card : ℝ)
  have hfpos : 0 < f := by dsimp only [f]; exact_mod_cast card_fib_pos hTW 0
  have hfq : f * (Fintype.card (G ⧸ B.W) : ℝ) = (Fintype.card (G ⧸ T) : ℝ) := by
    dsimp only [f]; exact_mod_cast card_fib_mul_quotient hTW 0
  have hfeq : ∀ u : G ⧸ B.W, ((fib hTW u).card : ℝ) = f := fun u => by
    dsimp only [f]; exact_mod_cast card_fib_eq hTW u 0
  change (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE2 A B uv) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 ≤
    (∑ uv' : (G ⧸ T) × (G ⧸ T), boxE2 A (refineSubspace B T hTW) uv') / (Fintype.card (G ⧸ T) : ℝ) ^ 2
  have hrew := sum_univ_prod_eq_sum_fib hTW (fun uv' : (G ⧸ T) × (G ⧸ T) => boxE2 A (refineSubspace B T hTW) uv')
  rw [hrew]
  have hsum :
      f ^ 2 * (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE2 A B uv) ≤
      ∑ uv : (G ⧸ B.W) × (G ⧸ B.W), ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
        boxE2 A (refineSubspace B T hTW) (u', v') := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun uv _ => ?_
    have h := sum_boxE2_refineSubspace_ge A B hTW uv
    rw [hfeq uv.1, hfeq uv.2, ← sq] at h
    exact h
  calc
    (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE2 A B uv) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2
        = (f ^ 2 * ∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE2 A B uv) / (Fintype.card (G ⧸ T) : ℝ) ^ 2 := by
            rw [← hfq]
            field_simp [hfpos.ne', hqW.ne']
    _ ≤ (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2,
          boxE2 A (refineSubspace B T hTW) (u', v')) / (Fintype.card (G ⧸ T) : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hsum (sq_nonneg _)


/- Refinement (A): improving E1 by passing to a subspace of bounded codimension -/

lemma finrank_le_of_le {U V : Submodule (ZMod 2) G} (h : U ≤ V) :
    Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) V := by
  have hcard : Fintype.card U ≤ Fintype.card V :=
    Fintype.card_le_of_injective (fun x : U => (⟨x.1, h x.2⟩ : V))
      (fun _ _ hx => Subtype.ext (congrArg (fun z : V => z.1) hx))
  rw [card_submodule_eq_two_pow, card_submodule_eq_two_pow] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard

lemma codim_inf_ker_le {T W : Submodule (ZMod 2) G} (hTW : T ≤ W) (r : Module.Dual (ZMod 2) W) :
    codim (T ⊓ (LinearMap.ker r).map W.subtype) ≤ codim T + 1 := by
  set K : Submodule (ZMod 2) G := (LinearMap.ker r).map W.subtype
  have hKW : K ≤ W := Submodule.map_subtype_le W (LinearMap.ker r)
  have hsup : Module.finrank (ZMod 2) (T ⊔ K : Submodule (ZMod 2) G) ≤ Module.finrank (ZMod 2) W :=
    finrank_le_of_le (sup_le hTW hKW)
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq T K
  have hK : codim K ≤ codim W + 1 := codim_ker_map_le W r
  have hW := finrank_add_codim W
  have hT := finrank_add_codim T
  have hKc := finrank_add_codim K
  have hTK := finrank_add_codim (T ⊓ K)
  omega

lemma exists_subspace_le_kers (W : Submodule (ZMod 2) G) {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (r : ι → Module.Dual (ZMod 2) W) :
    ∃ T : Submodule (ZMod 2) G,
      T ≤ W ∧
      (∀ i ∈ S, T ≤ (LinearMap.ker (r i)).map W.subtype) ∧
      codim T ≤ codim W + S.card := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨W, le_rfl, fun _ h => by simp at h, by omega⟩
  | @insert a s ha ih =>
    obtain ⟨T, hTW, hTk, hcod⟩ := ih
    refine ⟨T ⊓ (LinearMap.ker (r a)).map W.subtype, inf_le_left.trans hTW, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · exact inf_le_right
      · exact inf_le_left.trans (hTk i his)
    · have h1 := codim_inf_ker_le hTW (r a)
      have hcard : (insert a s).card = s.card + 1 := by simp [ha]
      omega

lemma refineA_step {ε : ℝ} (hε : 0 < ε) (A : Finset (G × G)) (B : Boxing G)
    (hnot : ¬ Cond1 ε B) :
    ∃ B' : Boxing G,
      B'.m = B.m ∧
      E2 A B ≤ E2 A B' ∧
      E1 B + ε ^ 3 / (B.m : ℝ) ^ 6 ≤ E1 B' ∧
      codim B'.W ≤ codim B.W + 4 ^ codim B.W := by
  let bad : Finset ((G ⧸ B.W) × (G ⧸ B.W)) := univ.filter (fun uv => ¬ IsBoxUniform ε B uv)
  have hbad_gt : ε * (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 < (bad.card : ℝ) := lt_of_not_ge hnot
  have hbad_ex : ∀ uv ∈ bad,
      ∃ p : Fin B.m × Module.Dual (ZMod 2) B.W,
        p.2 ≠ 0 ∧ ε / (B.m : ℝ) ^ 3 < |fHat (indW (shiftCoset B.W uv.1 (partB B uv p.1))) p.2| := by
    intro uv huv
    have hnu : ¬ IsBoxUniform ε B uv := (Finset.mem_filter.mp huv).2
    unfold IsBoxUniform at hnu
    push Not at hnu
    obtain ⟨i, r, hr, hgt⟩ := hnu
    exact ⟨(i, r), hr, hgt⟩
  let pick (uv : (G ⧸ B.W) × (G ⧸ B.W)) : Fin B.m × Module.Dual (ZMod 2) B.W :=
    if h : uv ∈ bad then Classical.choose (hbad_ex uv h) else (⟨0, B.hm⟩, 0)
  obtain ⟨T, hTW, hTk, hcod⟩ := exists_subspace_le_kers B.W bad (fun uv => (pick uv).2)
  let B' := refineSubspace B T hTW
  refine ⟨B', rfl, E2_refineSubspace_ge A B hTW, ?_, ?_⟩
  · have hqW : (0 : ℝ) < Fintype.card (G ⧸ B.W) := by exact_mod_cast card_quotient_pos B.W
    have hmpos : (0 : ℝ) < B.m := by exact_mod_cast B.hm
    let f : ℝ := ((fib hTW (0 : G ⧸ B.W)).card : ℝ)
    have hfpos : 0 < f := by dsimp only [f]; exact_mod_cast card_fib_pos hTW 0
    have hfq : f * (Fintype.card (G ⧸ B.W) : ℝ) = (Fintype.card (G ⧸ T) : ℝ) := by
      dsimp only [f]; exact_mod_cast card_fib_mul_quotient hTW 0
    have hfeq : ∀ u : G ⧸ B.W, ((fib hTW u).card : ℝ) = f := fun u => by
      dsimp only [f]; exact_mod_cast card_fib_eq hTW u 0
    have hbox_ge : ∀ uv : (G ⧸ B.W) × (G ⧸ B.W),
        f ^ 2 * (boxE1 B uv + if uv ∈ bad then ε ^ 2 / (B.m : ℝ) ^ 6 else 0) ≤
        ∑ u' ∈ fib hTW uv.1, ∑ v' ∈ fib hTW uv.2, boxE1 B' (u', v') := by
      intro uv
      by_cases huv : uv ∈ bad
      · rw [if_pos huv]
        have hspec := Classical.choose_spec (hbad_ex uv huv)
        have hpick : pick uv = Classical.choose (hbad_ex uv huv) := dif_pos huv
        have hrne : (pick uv).2 ≠ 0 := hpick ▸ hspec.1
        have hgt : ε / (B.m : ℝ) ^ 3 < |fHat (indW (shiftCoset B.W uv.1 (partB B uv (pick uv).1))) (pick uv).2| :=
          hpick ▸ hspec.2
        have hsq : ε ^ 2 / (B.m : ℝ) ^ 6 ≤ (fHat (indW (shiftCoset B.W uv.1 (partB B uv (pick uv).1))) (pick uv).2) ^ 2 := by
          have h1 : (ε / (B.m : ℝ) ^ 3) ^ 2 ≤
              |fHat (indW (shiftCoset B.W uv.1 (partB B uv (pick uv).1))) (pick uv).2| ^ 2 :=
            pow_le_pow_left₀ (by positivity) hgt.le 2
          rw [sq_abs] at h1
          calc ε ^ 2 / (B.m : ℝ) ^ 6 = (ε / (B.m : ℝ) ^ 3) ^ 2 := by ring
            _ ≤ (fHat (indW (shiftCoset B.W uv.1 (partB B uv (pick uv).1))) (pick uv).2) ^ 2 := h1
        have hinc := sum_boxE1_refineSubspace_inc B hTW uv (pick uv).1 (pick uv).2 hrne (hTk uv huv)
        rw [hfeq uv.1, hfeq uv.2, ← sq] at hinc
        have hstep : f ^ 2 * (boxE1 B uv + ε ^ 2 / (B.m : ℝ) ^ 6) ≤
            f ^ 2 * (boxE1 B uv + (fHat (indW (shiftCoset B.W uv.1 (partB B uv (pick uv).1))) (pick uv).2) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hsq) (sq_nonneg f)
        exact hstep.trans hinc
      · rw [if_neg huv, add_zero]
        have h := sum_boxE1_refineSubspace_ge B hTW uv
        rw [hfeq uv.1, hfeq uv.2, ← sq] at h
        exact h
    have hsum :
        f ^ 2 * ((∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) + (bad.card : ℝ) * (ε ^ 2 / (B.m : ℝ) ^ 6)) ≤
        ∑ uv' : (G ⧸ T) × (G ⧸ T), boxE1 B' uv' := by
      have hrew := sum_univ_prod_eq_sum_fib hTW (fun uv' : (G ⧸ T) × (G ⧸ T) => boxE1 B' uv')
      rw [hrew]
      have hlhs :
          f ^ 2 * ((∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) + (bad.card : ℝ) * (ε ^ 2 / (B.m : ℝ) ^ 6)) =
          ∑ uv : (G ⧸ B.W) × (G ⧸ B.W),
            f ^ 2 * (boxE1 B uv + if uv ∈ bad then ε ^ 2 / (B.m : ℝ) ^ 6 else 0) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        congr 2
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        congr 1
        have : univ.filter (fun uv => uv ∈ bad) = bad := by ext uv; simp
        rw [this]
      rw [hlhs]
      exact Finset.sum_le_sum fun uv _ => hbox_ge uv
    have hdiv :
        E1 B + ((bad.card : ℝ) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2) * (ε ^ 2 / (B.m : ℝ) ^ 6) ≤ E1 B' := by
      change (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 +
          ((bad.card : ℝ) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2) * (ε ^ 2 / (B.m : ℝ) ^ 6) ≤
        (∑ uv' : (G ⧸ T) × (G ⧸ T), boxE1 B' uv') / (Fintype.card (G ⧸ T) : ℝ) ^ 2
      calc
        (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 +
            ((bad.card : ℝ) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2) * (ε ^ 2 / (B.m : ℝ) ^ 6)
            = (f ^ 2 * ((∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE1 B uv) +
                (bad.card : ℝ) * (ε ^ 2 / (B.m : ℝ) ^ 6))) / (Fintype.card (G ⧸ T) : ℝ) ^ 2 := by
              rw [← hfq]
              field_simp [hfpos.ne', hqW.ne']
        _ ≤ (∑ uv' : (G ⧸ T) × (G ⧸ T), boxE1 B' uv') / (Fintype.card (G ⧸ T) : ℝ) ^ 2 :=
              div_le_div_of_nonneg_right hsum (sq_nonneg _)
    have hbad_div : ε ≤ (bad.card : ℝ) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 :=
      (le_div_iff₀ (pow_pos hqW 2)).mpr hbad_gt.le
    have hinc_le : ε ^ 3 / (B.m : ℝ) ^ 6 ≤
        ((bad.card : ℝ) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2) * (ε ^ 2 / (B.m : ℝ) ^ 6) := by
      calc
        ε ^ 3 / (B.m : ℝ) ^ 6 = ε * (ε ^ 2 / (B.m : ℝ) ^ 6) := by ring
        _ ≤ ((bad.card : ℝ) / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2) * (ε ^ 2 / (B.m : ℝ) ^ 6) :=
          mul_le_mul_of_nonneg_right hbad_div (by positivity)
    linarith
  · have hbad_le : bad.card ≤ 4 ^ codim B.W := by
      calc bad.card ≤ (univ : Finset ((G ⧸ B.W) × (G ⧸ B.W))).card := Finset.card_le_card (subset_univ _)
        _ = Fintype.card (G ⧸ B.W) * Fintype.card (G ⧸ B.W) := by rw [Finset.card_univ, Fintype.card_prod]
        _ = 2 ^ codim B.W * 2 ^ codim B.W := by rw [card_quotient_eq_two_pow_codim]
        _ = 4 ^ codim B.W := by rw [← mul_pow]; norm_num
    change codim T ≤ codim B.W + 4 ^ codim B.W
    omega

/- Refinement (B): improving E2 by refining the inner partitions -/

lemma pairEnergy_inc_four {α β : Type*} [DecidableEq α] [DecidableEq β]
    {ε : ℝ} (hε : 0 < ε) (E : α → β → Prop) (X : Finset α) (Y : Finset β)
    (X' : Finset α) (Y' : Finset β)
    (hX'sub : X' ⊆ X) (hY'sub : Y' ⊆ Y)
    (hX'sz : ε * (X.card : ℝ) ≤ (X'.card : ℝ))
    (hY'sz : ε * (Y.card : ℝ) ≤ (Y'.card : ℝ))
    (hgt : ε * (X'.card : ℝ) * (Y'.card : ℝ) <
      |(edgeCount E X' Y' : ℝ) - pairDensity E X Y * (X'.card : ℝ) * (Y'.card : ℝ)|) :
    pairEnergy E X Y + ε ^ 4 * (X.card : ℝ) * (Y.card : ℝ) ≤
      ∑ a : Bool, ∑ b : Bool,
        pairEnergy E (if a then X' else X \ X') (if b then Y' else Y \ Y') := by
  have hXY'pos : 0 < (X'.card : ℝ) * (Y'.card : ℝ) := by
    by_contra hle
    push Not at hle
    have hzero : (X'.card : ℝ) * (Y'.card : ℝ) = 0 := le_antisymm hle (by positivity)
    have hnat : X'.card = 0 ∨ Y'.card = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    have hedge0 : edgeCount E X' Y' = 0 := by
      dsimp only [edgeCount]
      rcases hnat with h | h
      · rw [Finset.card_eq_zero.mp h]; simp
      · rw [Finset.card_eq_zero.mp h]; simp
    have h1 : ε * (X'.card : ℝ) * (Y'.card : ℝ) = 0 := by rw [mul_assoc, hzero, mul_zero]
    have h2 : pairDensity E X Y * (X'.card : ℝ) * (Y'.card : ℝ) = 0 := by rw [mul_assoc, hzero, mul_zero]
    rw [hedge0, Nat.cast_zero, h1, h2, sub_zero, abs_zero] at hgt
    exact lt_irrefl 0 hgt
  have hdev : ε ≤ |pairDensity E X' Y' - pairDensity E X Y| := by
    have hrew : (edgeCount E X' Y' : ℝ) - pairDensity E X Y * (X'.card : ℝ) * (Y'.card : ℝ) =
        (pairDensity E X' Y' - pairDensity E X Y) * ((X'.card : ℝ) * (Y'.card : ℝ)) := by
      have hd' : pairDensity E X' Y' * ((X'.card : ℝ) * (Y'.card : ℝ)) = (edgeCount E X' Y' : ℝ) := by
        dsimp only [pairDensity]
        exact div_mul_cancel₀ _ hXY'pos.ne'
      rw [sub_mul, hd']
      ring
    rw [hrew, abs_mul, abs_of_pos hXY'pos] at hgt
    have hgt' : ε * ((X'.card : ℝ) * (Y'.card : ℝ)) <
        |pairDensity E X' Y' - pairDensity E X Y| * ((X'.card : ℝ) * (Y'.card : ℝ)) := by
      linarith
    exact (lt_of_mul_lt_mul_right hgt' hXY'pos.le).le
  let P : Bool → Finset α := fun a => if a then X' else X \ X'
  let Q : Bool → Finset β := fun b => if b then Y' else Y \ Y'
  let U : Finset (α × β) := X ×ˢ Y
  let M : Finset (α × β) := U.filter (fun p => E p.1 p.2)
  let R : Bool × Bool → Finset (α × β) := fun ab => P ab.1 ×ˢ Q ab.2
  have hPdisj : Pairwise (fun a b : Bool => Disjoint (P a) (P b)) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro x h1 h2
    cases a <;> cases b <;> simp_all [P]
  have hQdisj : Pairwise (fun a b : Bool => Disjoint (Q a) (Q b)) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro y h1 h2
    cases a <;> cases b <;> simp_all [Q]
  have hPcov : (univ : Finset Bool).biUnion P = X := by
    ext x
    simp only [mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨b, hb⟩
      cases b
      · exact (Finset.mem_sdiff.mp hb).1
      · exact hX'sub hb
    · intro hx
      by_cases hx' : x ∈ X'
      · exact ⟨true, hx'⟩
      · exact ⟨false, Finset.mem_sdiff.mpr ⟨hx, hx'⟩⟩
  have hQcov : (univ : Finset Bool).biUnion Q = Y := by
    ext y
    simp only [mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨b, hb⟩
      cases b
      · exact (Finset.mem_sdiff.mp hb).1
      · exact hY'sub hb
    · intro hy
      by_cases hy' : y ∈ Y'
      · exact ⟨true, hy'⟩
      · exact ⟨false, Finset.mem_sdiff.mpr ⟨hy, hy'⟩⟩
  have hRdisj : Pairwise (fun a b : Bool × Bool => Disjoint (R a) (R b)) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro p ha hb
    simp only [R, mem_product] at ha hb
    by_cases h1 : a.1 = b.1
    · have h2 : a.2 ≠ b.2 := fun h2 => hab (Prod.ext h1 h2)
      exact Finset.disjoint_left.mp (hQdisj h2) ha.2 hb.2
    · exact Finset.disjoint_left.mp (hPdisj h1) ha.1 hb.1
  have hRcov : (univ : Finset (Bool × Bool)).biUnion R = U := by
    ext ⟨x, y⟩
    simp only [R, U, mem_biUnion, mem_univ, true_and, mem_product, Prod.exists, ← hPcov, ← hQcov]
    constructor
    · rintro ⟨a, b, hx, hy⟩; exact ⟨⟨a, hx⟩, ⟨b, hy⟩⟩
    · rintro ⟨⟨a, hx⟩, ⟨b, hy⟩⟩; exact ⟨a, b, hx, hy⟩
  have hMU : M ∩ U = M := Finset.inter_eq_left.mpr (filter_subset _ _)
  have hMR : ∀ ab : Bool × Bool, M ∩ R ab = (R ab).filter (fun p => E p.1 p.2) := by
    intro ab
    have hsub : R ab ⊆ U := by
      rw [← hRcov]
      exact Finset.subset_biUnion_of_mem R (mem_univ ab)
    ext p
    simp only [M, mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨_, hpE⟩, hpR⟩; exact ⟨hpR, hpE⟩
    · rintro ⟨hpR, hpE⟩; exact ⟨⟨hsub hpR, hpE⟩, hpR⟩
  have hsize : ε ^ 2 * (U.card : ℝ) ≤ ((R (true, true)).card : ℝ) := by
    dsimp only [U, R, P, Q]
    simp only [↓reduceIte, Finset.card_product, Nat.cast_mul]
    calc
      ε ^ 2 * ((X.card : ℝ) * (Y.card : ℝ)) = (ε * (X.card : ℝ)) * (ε * (Y.card : ℝ)) := by ring
      _ ≤ (X'.card : ℝ) * (Y'.card : ℝ) :=
        mul_le_mul hX'sz hY'sz (mul_nonneg hε.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hdev' : ε ≤ |((M ∩ R (true, true)).card : ℝ) / ((R (true, true)).card : ℝ) -
      ((M ∩ U).card : ℝ) / (U.card : ℝ)| := by
    rw [hMU, hMR (true, true)]
    dsimp only [U, M, R, P, Q]
    simp only [↓reduceIte, Finset.card_product, Nat.cast_mul]
    exact hdev
  have hvi := variance_increment U M R hRdisj hRcov (true, true) (sq_nonneg ε) hε.le hsize hdev'
  have hlhs :
      (U.card : ℝ) * (((M ∩ U).card : ℝ) / (U.card : ℝ)) ^ 2 + ε ^ 2 * ε ^ 2 * (U.card : ℝ) =
      pairEnergy E X Y + ε ^ 4 * (X.card : ℝ) * (Y.card : ℝ) := by
    rw [hMU]
    dsimp only [pairEnergy, pairDensity, edgeCount, U, M]
    rw [Finset.card_product, Nat.cast_mul]
    ring
  have hrhs :
      (∑ ab : Bool × Bool, ((R ab).card : ℝ) * (((M ∩ R ab).card : ℝ) / ((R ab).card : ℝ)) ^ 2) =
      ∑ a : Bool, ∑ b : Bool, pairEnergy E (P a) (Q b) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hMR (a, b)]
    dsimp only [pairEnergy, pairDensity, edgeCount, R]
    rw [Finset.card_product, Nat.cast_mul]
  rw [hlhs, hrhs] at hvi
  exact hvi

lemma sum_pairEnergy_refinement {m m' : ℕ} {ε : ℝ} (hε : 0 < ε)
    (E : G → G → Prop) (U_X U_Y : Finset G)
    (idxX : G → Fin m) (idxY : G → Fin m)
    (idxX' : G → Fin m') (idxY' : G → Fin m')
    (πX : Fin m' → Fin m) (πY : Fin m' → Fin m)
    (hπX : ∀ x, πX (idxX' x) = idxX x)
    (hπY : ∀ y, πY (idxY' y) = idxY y)
    (hsep : ∀ i j : Fin m,
      ¬ IsQuasirandom ε E (U_X.filter (fun x => idxX x = i)) (U_Y.filter (fun y => idxY y = j)) →
      ∃ (X' Y' : Finset G) (bX bY : Fin m' → Bool),
        X' ⊆ U_X.filter (fun x => idxX x = i) ∧
        Y' ⊆ U_Y.filter (fun y => idxY y = j) ∧
        ε * ((U_X.filter (fun x => idxX x = i)).card : ℝ) ≤ (X'.card : ℝ) ∧
        ε * ((U_Y.filter (fun y => idxY y = j)).card : ℝ) ≤ (Y'.card : ℝ) ∧
        ε * (X'.card : ℝ) * (Y'.card : ℝ) <
          |(edgeCount E X' Y' : ℝ) -
            pairDensity E (U_X.filter (fun x => idxX x = i)) (U_Y.filter (fun y => idxY y = j)) *
              (X'.card : ℝ) * (Y'.card : ℝ)| ∧
        (∀ x ∈ U_X.filter (fun x => idxX x = i), bX (idxX' x) = decide (x ∈ X')) ∧
        (∀ y ∈ U_Y.filter (fun y => idxY y = j), bY (idxY' y) = decide (y ∈ Y'))) :
    (∑ i : Fin m, ∑ j : Fin m,
      (pairEnergy E (U_X.filter (fun x => idxX x = i)) (U_Y.filter (fun y => idxY y = j)) +
        if IsQuasirandom ε E (U_X.filter (fun x => idxX x = i)) (U_Y.filter (fun y => idxY y = j)) then 0
        else ε ^ 4 * ((U_X.filter (fun x => idxX x = i)).card : ℝ) *
          ((U_Y.filter (fun y => idxY y = j)).card : ℝ))) ≤
      ∑ i' : Fin m', ∑ j' : Fin m',
        pairEnergy E (U_X.filter (fun x => idxX' x = i')) (U_Y.filter (fun y => idxY' y = j')) := by
  let P' : Fin m' → Finset G := fun i' => U_X.filter (fun x => idxX' x = i')
  let Q' : Fin m' → Finset G := fun j' => U_Y.filter (fun y => idxY' y = j')
  let fibX : Fin m → Finset (Fin m') := fun i => univ.filter (fun i' => πX i' = i)
  let fibY : Fin m → Finset (Fin m') := fun j => univ.filter (fun j' => πY j' = j)
  have hP'disj : Pairwise (fun i₁ i₂ : Fin m' => Disjoint (P' i₁) (P' i₂)) := by
    intro i₁ i₂ hne
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hQ'disj : Pairwise (fun j₁ j₂ : Fin m' => Disjoint (Q' j₁) (Q' j₂)) := by
    intro j₁ j₂ hne
    rw [Finset.disjoint_left]
    intro y h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hrhs_split :
      (∑ i' : Fin m', ∑ j' : Fin m', pairEnergy E (P' i') (Q' j')) =
      ∑ i : Fin m, ∑ j : Fin m, ∑ i' ∈ fibX i, ∑ j' ∈ fibY j, pairEnergy E (P' i') (Q' j') := by
    rw [sum_fiberwise_type πX]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (∑ i' ∈ fibX i, ∑ j' : Fin m', pairEnergy E (P' i') (Q' j')) =
        ∑ i' ∈ fibX i, ∑ j : Fin m, ∑ j' ∈ fibY j, pairEnergy E (P' i') (Q' j') :=
      Finset.sum_congr rfl fun i' _ => sum_fiberwise_type πY (fun j' => pairEnergy E (P' i') (Q' j'))
    rw [h1, Finset.sum_comm]
  change _ ≤ ∑ i' : Fin m', ∑ j' : Fin m', pairEnergy E (P' i') (Q' j')
  rw [hrhs_split]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  let X := U_X.filter (fun x => idxX x = i)
  let Y := U_Y.filter (fun y => idxY y = j)
  by_cases hqr : IsQuasirandom ε E X Y
  · rw [if_pos hqr, add_zero]
    have h := pairEnergy_le_sum_partition
      (ι := {i' : Fin m' // i' ∈ fibX i}) (κ := {j' : Fin m' // j' ∈ fibY j})
      E X Y (fun a => P' a.1) (fun b => Q' b.1)
      (fun a b hab => hP'disj (fun heq => hab (Subtype.ext heq)))
      (by
        ext x
        simp only [mem_biUnion, mem_univ, true_and, Subtype.exists, fibX, P', X, mem_filter]
        constructor
        · rintro ⟨i', hi', hxU, rfl⟩; exact ⟨hxU, (hπX x).symm.trans hi'⟩
        · rintro ⟨hxU, hx⟩; exact ⟨idxX' x, (hπX x).trans hx, hxU, rfl⟩)
      (fun a b hab => hQ'disj (fun heq => hab (Subtype.ext heq)))
      (by
        ext y
        simp only [mem_biUnion, mem_univ, true_and, Subtype.exists, fibY, Q', Y, mem_filter]
        constructor
        · rintro ⟨j', hj', hyU, rfl⟩; exact ⟨hyU, (hπY y).symm.trans hj'⟩
        · rintro ⟨hyU, hy⟩; exact ⟨idxY' y, (hπY y).trans hy, hyU, rfl⟩)
    have hrhs_sub :
        (∑ a : {i' : Fin m' // i' ∈ fibX i}, ∑ b : {j' : Fin m' // j' ∈ fibY j}, pairEnergy E (P' a.1) (Q' b.1)) =
        ∑ i' ∈ fibX i, ∑ j' ∈ fibY j, pairEnergy E (P' i') (Q' j') := by
      have h1 : ∀ a : {i' : Fin m' // i' ∈ fibX i},
          (∑ b : {j' : Fin m' // j' ∈ fibY j}, pairEnergy E (P' a.1) (Q' b.1)) =
          ∑ j' ∈ fibY j, pairEnergy E (P' a.1) (Q' j') := fun a =>
        sum_subtype_mem (fibY j) (fun j' => pairEnergy E (P' a.1) (Q' j'))
      simp_rw [h1]
      exact sum_subtype_mem (fibX i) (fun i' => ∑ j' ∈ fibY j, pairEnergy E (P' i') (Q' j'))
    rwa [hrhs_sub] at h
  · rw [if_neg hqr]
    obtain ⟨X', Y', bX, bY, hX'sub, hY'sub, hX'sz, hY'sz, hgt, hbX, hbY⟩ := hsep i j hqr
    have h4 := pairEnergy_inc_four hε E X Y X' Y' hX'sub hY'sub hX'sz hY'sz hgt
    let fibXa : Bool → Finset (Fin m') := fun a => (fibX i).filter (fun i' => bX i' = a)
    let fibYb : Bool → Finset (Fin m') := fun b => (fibY j).filter (fun j' => bY j' = b)
    have hsub_step : ∀ a b : Bool,
        pairEnergy E (if a then X' else X \ X') (if b then Y' else Y \ Y') ≤
        ∑ i' ∈ fibXa a, ∑ j' ∈ fibYb b, pairEnergy E (P' i') (Q' j') := by
      intro a b
      have h := pairEnergy_le_sum_partition
        (ι := {i' : Fin m' // i' ∈ fibXa a}) (κ := {j' : Fin m' // j' ∈ fibYb b})
        E (if a then X' else X \ X') (if b then Y' else Y \ Y')
        (fun u => P' u.1) (fun v => Q' v.1)
        (fun u v huv => hP'disj (fun heq => huv (Subtype.ext heq)))
        (by
          ext x
          simp only [mem_biUnion, mem_univ, true_and, Subtype.exists, fibXa, fibX, P', mem_filter]
          constructor
          · rintro ⟨i', ⟨hi', hba⟩, hxU, rfl⟩
            have hxX : x ∈ X := Finset.mem_filter.mpr ⟨hxU, (hπX x).symm.trans hi'⟩
            have hdec : decide (x ∈ X') = a := (hbX x hxX).symm.trans hba
            cases a
            · simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_sdiff]
              exact ⟨hxX, of_decide_eq_false hdec⟩
            · simp only [↓reduceIte]
              exact of_decide_eq_true hdec
          · intro hx
            cases a
            · simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_sdiff] at hx
              have hxU : x ∈ U_X := (Finset.mem_filter.mp hx.1).1
              have hxi : idxX x = i := (Finset.mem_filter.mp hx.1).2
              refine ⟨idxX' x, ⟨(hπX x).trans hxi, ?_⟩, hxU, rfl⟩
              rw [hbX x hx.1]
              exact decide_eq_false hx.2
            · simp only [↓reduceIte] at hx
              have hxX : x ∈ X := hX'sub hx
              have hxU : x ∈ U_X := (Finset.mem_filter.mp hxX).1
              have hxi : idxX x = i := (Finset.mem_filter.mp hxX).2
              refine ⟨idxX' x, ⟨(hπX x).trans hxi, ?_⟩, hxU, rfl⟩
              rw [hbX x hxX]
              exact decide_eq_true hx)
        (fun u v huv => hQ'disj (fun heq => huv (Subtype.ext heq)))
        (by
          ext y
          simp only [mem_biUnion, mem_univ, true_and, Subtype.exists, fibYb, fibY, Q', mem_filter]
          constructor
          · rintro ⟨j', ⟨hj', hbb⟩, hyU, rfl⟩
            have hyY : y ∈ Y := Finset.mem_filter.mpr ⟨hyU, (hπY y).symm.trans hj'⟩
            have hdec : decide (y ∈ Y') = b := (hbY y hyY).symm.trans hbb
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_sdiff]
              exact ⟨hyY, of_decide_eq_false hdec⟩
            · simp only [↓reduceIte]
              exact of_decide_eq_true hdec
          · intro hy
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_sdiff] at hy
              have hyU : y ∈ U_Y := (Finset.mem_filter.mp hy.1).1
              have hyj : idxY y = j := (Finset.mem_filter.mp hy.1).2
              refine ⟨idxY' y, ⟨(hπY y).trans hyj, ?_⟩, hyU, rfl⟩
              rw [hbY y hy.1]
              exact decide_eq_false hy.2
            · simp only [↓reduceIte] at hy
              have hyY : y ∈ Y := hY'sub hy
              have hyU : y ∈ U_Y := (Finset.mem_filter.mp hyY).1
              have hyj : idxY y = j := (Finset.mem_filter.mp hyY).2
              refine ⟨idxY' y, ⟨(hπY y).trans hyj, ?_⟩, hyU, rfl⟩
              rw [hbY y hyY]
              exact decide_eq_true hy)
      have hrhs_sub :
          (∑ u : {i' : Fin m' // i' ∈ fibXa a}, ∑ v : {j' : Fin m' // j' ∈ fibYb b}, pairEnergy E (P' u.1) (Q' v.1)) =
          ∑ i' ∈ fibXa a, ∑ j' ∈ fibYb b, pairEnergy E (P' i') (Q' j') := by
        have h1 : ∀ u : {i' : Fin m' // i' ∈ fibXa a},
            (∑ v : {j' : Fin m' // j' ∈ fibYb b}, pairEnergy E (P' u.1) (Q' v.1)) =
            ∑ j' ∈ fibYb b, pairEnergy E (P' u.1) (Q' j') := fun u =>
          sum_subtype_mem (fibYb b) (fun j' => pairEnergy E (P' u.1) (Q' j'))
        simp_rw [h1]
        exact sum_subtype_mem (fibXa a) (fun i' => ∑ j' ∈ fibYb b, pairEnergy E (P' i') (Q' j'))
      rwa [hrhs_sub] at h
    calc
      pairEnergy E X Y + ε ^ 4 * (X.card : ℝ) * (Y.card : ℝ)
          ≤ ∑ a : Bool, ∑ b : Bool,
              pairEnergy E (if a then X' else X \ X') (if b then Y' else Y \ Y') := h4
      _ ≤ ∑ a : Bool, ∑ b : Bool, ∑ i' ∈ fibXa a, ∑ j' ∈ fibYb b, pairEnergy E (P' i') (Q' j') :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hsub_step a b
      _ = ∑ a : Bool, ∑ i' ∈ fibXa a, ∑ b : Bool, ∑ j' ∈ fibYb b, pairEnergy E (P' i') (Q' j') :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a : Bool, ∑ i' ∈ fibXa a, ∑ j' ∈ fibY j, pairEnergy E (P' i') (Q' j') :=
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i' _ =>
              sum_bool_filter (fibY j) bY (fun j' => pairEnergy E (P' i') (Q' j'))
      _ = ∑ i' ∈ fibX i, ∑ j' ∈ fibY j, pairEnergy E (P' i') (Q' j') :=
            sum_bool_filter (fibX i) bX (fun i' => ∑ j' ∈ fibY j, pairEnergy E (P' i') (Q' j'))

lemma refineB_step {ε : ℝ} (hε : 0 < ε) (A : Finset (G × G)) (B : Boxing G)
    (hnot : ¬ Cond2 ε A B) :
    ∃ B' : Boxing G,
      B'.W = B.W ∧
      B'.m = B.m * 2 ^ (2 * B.m) ∧
      E2 A B + ε ^ 6 ≤ E2 A B' := by
  let L := Fin B.m × (Fin B.m → Bool) × (Fin B.m → Bool)
  have hcardL : Fintype.card L = B.m * 2 ^ (2 * B.m) := by
    dsimp only [L]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [← pow_add, ← two_mul]
  let eL : L ≃ Fin (B.m * 2 ^ (2 * B.m)) := (Fintype.equivFin L).trans (finCongr hcardL)
  have hex_wit : ∀ (E : G → G → Prop) (X Y : Finset G),
      ¬ IsQuasirandom ε E X Y →
      ∃ p : Finset G × Finset G,
        p.1 ⊆ X ∧ p.2 ⊆ Y ∧
        ε * (X.card : ℝ) ≤ (p.1.card : ℝ) ∧
        ε * (Y.card : ℝ) ≤ (p.2.card : ℝ) ∧
        ε * (p.1.card : ℝ) * (p.2.card : ℝ) <
          |(edgeCount E p.1 p.2 : ℝ) - pairDensity E X Y * (p.1.card : ℝ) * (p.2.card : ℝ)| := by
    intro E X Y hnq
    unfold IsQuasirandom at hnq
    push Not at hnq
    obtain ⟨X', hX', Y', hY', hszX, hszY, hgt⟩ := hnq
    exact ⟨(X', Y'), hX', hY', hszX, hszY, hgt⟩
  let witBC (uv : (G ⧸ B.W) × (G ⧸ B.W)) (i j : Fin B.m) : Finset G × Finset G :=
    if h : ¬ IsQuasirandom ε (relBC A) (partB B uv i) (partC B uv j) then
      Classical.choose (hex_wit (relBC A) (partB B uv i) (partC B uv j) h)
    else (∅, ∅)
  let witBD (uv : (G ⧸ B.W) × (G ⧸ B.W)) (i k : Fin B.m) : Finset G × Finset G :=
    if h : ¬ IsQuasirandom ε (relBD A) (partB B uv i) (partD B uv k) then
      Classical.choose (hex_wit (relBD A) (partB B uv i) (partD B uv k) h)
    else (∅, ∅)
  let witCD (uv : (G ⧸ B.W) × (G ⧸ B.W)) (j k : Fin B.m) : Finset G × Finset G :=
    if h : ¬ IsQuasirandom ε (relCD A) (partC B uv j) (partD B uv k) then
      Classical.choose (hex_wit (relCD A) (partC B uv j) (partD B uv k) h)
    else (∅, ∅)
  let lblB (uv : (G ⧸ B.W) × (G ⧸ B.W)) (x : G) : L :=
    (B.idxB uv x,
      fun j => decide (x ∈ (witBC uv (B.idxB uv x) j).1),
      fun k => decide (x ∈ (witBD uv (B.idxB uv x) k).1))
  let lblC (uv : (G ⧸ B.W) × (G ⧸ B.W)) (y : G) : L :=
    (B.idxC uv y,
      fun i => decide (y ∈ (witBC uv i (B.idxC uv y)).2),
      fun k => decide (y ∈ (witCD uv (B.idxC uv y) k).1))
  let lblD (uv : (G ⧸ B.W) × (G ⧸ B.W)) (z : G) : L :=
    (B.idxD uv z,
      fun i => decide (z ∈ (witBD uv i (B.idxD uv z)).2),
      fun j => decide (z ∈ (witCD uv j (B.idxD uv z)).2))
  let B' : Boxing G := {
    W := B.W
    m := B.m * 2 ^ (2 * B.m)
    hm := Nat.mul_pos B.hm (pow_pos (by norm_num) _)
    idxB := fun uv x => eL (lblB uv x)
    idxC := fun uv y => eL (lblC uv y)
    idxD := fun uv z => eL (lblD uv z)
  }
  refine ⟨B', rfl, rfl, ?_⟩
  let proj : Fin B'.m → Fin B.m := fun i' => (eL.symm i').1
  have hbox_inc : ∀ uv : (G ⧸ B.W) × (G ⧸ B.W),
      boxE2 A B uv +
        ε ^ 4 * (badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv) / 3 ≤
      boxE2 A B' uv := by
    intro uv
    have hBC := sum_pairEnergy_refinement hε (relBC A) (coset B.W uv.1) (coset B.W uv.2)
      (B.idxB uv) (B.idxC uv) (B'.idxB uv) (B'.idxC uv) proj proj
      (fun x => by simp [proj, B', lblB])
      (fun y => by simp [proj, B', lblC])
      (fun i j hnq => by
        have hspec := Classical.choose_spec (hex_wit (relBC A) (partB B uv i) (partC B uv j) hnq)
        have hw : witBC uv i j = Classical.choose (hex_wit (relBC A) (partB B uv i) (partC B uv j) hnq) :=
          dif_pos hnq
        refine ⟨(witBC uv i j).1, (witBC uv i j).2,
          fun i' => (eL.symm i').2.1 j, fun j' => (eL.symm j').2.1 i,
          hw ▸ hspec.1, hw ▸ hspec.2.1, hw ▸ hspec.2.2.1, hw ▸ hspec.2.2.2.1, hw ▸ hspec.2.2.2.2,
          ?_, ?_⟩
        · intro x hx
          have hxi : B.idxB uv x = i := (Finset.mem_filter.mp hx).2
          simp [B', lblB, hxi]
        · intro y hy
          have hyj : B.idxC uv y = j := (Finset.mem_filter.mp hy).2
          simp [B', lblC, hyj])
    have hBD := sum_pairEnergy_refinement hε (relBD A) (coset B.W uv.1) (coset B.W (uv.1 + uv.2))
      (B.idxB uv) (B.idxD uv) (B'.idxB uv) (B'.idxD uv) proj proj
      (fun x => by simp [proj, B', lblB])
      (fun z => by simp [proj, B', lblD])
      (fun i k hnq => by
        have hspec := Classical.choose_spec (hex_wit (relBD A) (partB B uv i) (partD B uv k) hnq)
        have hw : witBD uv i k = Classical.choose (hex_wit (relBD A) (partB B uv i) (partD B uv k) hnq) :=
          dif_pos hnq
        refine ⟨(witBD uv i k).1, (witBD uv i k).2,
          fun i' => (eL.symm i').2.2 k, fun k' => (eL.symm k').2.1 i,
          hw ▸ hspec.1, hw ▸ hspec.2.1, hw ▸ hspec.2.2.1, hw ▸ hspec.2.2.2.1, hw ▸ hspec.2.2.2.2,
          ?_, ?_⟩
        · intro x hx
          have hxi : B.idxB uv x = i := (Finset.mem_filter.mp hx).2
          simp [B', lblB, hxi]
        · intro z hz
          have hzk : B.idxD uv z = k := (Finset.mem_filter.mp hz).2
          simp [B', lblD, hzk])
    have hCD := sum_pairEnergy_refinement hε (relCD A) (coset B.W uv.2) (coset B.W (uv.1 + uv.2))
      (B.idxC uv) (B.idxD uv) (B'.idxC uv) (B'.idxD uv) proj proj
      (fun y => by simp [proj, B', lblC])
      (fun z => by simp [proj, B', lblD])
      (fun j k hnq => by
        have hspec := Classical.choose_spec (hex_wit (relCD A) (partC B uv j) (partD B uv k) hnq)
        have hw : witCD uv j k = Classical.choose (hex_wit (relCD A) (partC B uv j) (partD B uv k) hnq) :=
          dif_pos hnq
        refine ⟨(witCD uv j k).1, (witCD uv j k).2,
          fun j' => (eL.symm j').2.2 k, fun k' => (eL.symm k').2.2 j,
          hw ▸ hspec.1, hw ▸ hspec.2.1, hw ▸ hspec.2.2.1, hw ▸ hspec.2.2.2.1, hw ▸ hspec.2.2.2.2,
          ?_, ?_⟩
        · intro y hy
          have hyj : B.idxC uv y = j := (Finset.mem_filter.mp hy).2
          simp [B', lblC, hyj]
        · intro z hz
          have hzk : B.idxD uv z = k := (Finset.mem_filter.mp hz).2
          simp [B', lblD, hzk])
    have hWpos : (0 : ℝ) < Fintype.card B.W := by exact_mod_cast card_submodule_pos B.W
    have hBC' :
        (∑ i : Fin B.m, ∑ j : Fin B.m, pairEnergy (relBC A) (partB B uv i) (partC B uv j)) +
          ε ^ 4 * (Fintype.card B.W : ℝ) ^ 2 * badWeightBC ε A B uv ≤
        ∑ i' : Fin B'.m, ∑ j' : Fin B'.m, pairEnergy (relBC A) (partB B' uv i') (partC B' uv j') := by
      have hlhs :
          (∑ i : Fin B.m, ∑ j : Fin B.m, pairEnergy (relBC A) (partB B uv i) (partC B uv j)) +
            ε ^ 4 * (Fintype.card B.W : ℝ) ^ 2 * badWeightBC ε A B uv =
          ∑ i : Fin B.m, ∑ j : Fin B.m,
            (pairEnergy (relBC A) (partB B uv i) (partC B uv j) +
              if IsQuasirandom ε (relBC A) (partB B uv i) (partC B uv j) then 0
              else ε ^ 4 * ((partB B uv i).card : ℝ) * ((partC B uv j).card : ℝ)) := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        dsimp only [badWeightBC]
        rw [mul_assoc, mul_div_cancel₀ _ (pow_ne_zero 2 hWpos.ne'), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
      rw [hlhs]
      exact hBC
    have hBD' :
        (∑ i : Fin B.m, ∑ k : Fin B.m, pairEnergy (relBD A) (partB B uv i) (partD B uv k)) +
          ε ^ 4 * (Fintype.card B.W : ℝ) ^ 2 * badWeightBD ε A B uv ≤
        ∑ i' : Fin B'.m, ∑ k' : Fin B'.m, pairEnergy (relBD A) (partB B' uv i') (partD B' uv k') := by
      have hlhs :
          (∑ i : Fin B.m, ∑ k : Fin B.m, pairEnergy (relBD A) (partB B uv i) (partD B uv k)) +
            ε ^ 4 * (Fintype.card B.W : ℝ) ^ 2 * badWeightBD ε A B uv =
          ∑ i : Fin B.m, ∑ k : Fin B.m,
            (pairEnergy (relBD A) (partB B uv i) (partD B uv k) +
              if IsQuasirandom ε (relBD A) (partB B uv i) (partD B uv k) then 0
              else ε ^ 4 * ((partB B uv i).card : ℝ) * ((partD B uv k).card : ℝ)) := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        dsimp only [badWeightBD]
        rw [mul_assoc, mul_div_cancel₀ _ (pow_ne_zero 2 hWpos.ne'), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> ring
      rw [hlhs]
      exact hBD
    have hCD' :
        (∑ j : Fin B.m, ∑ k : Fin B.m, pairEnergy (relCD A) (partC B uv j) (partD B uv k)) +
          ε ^ 4 * (Fintype.card B.W : ℝ) ^ 2 * badWeightCD ε A B uv ≤
        ∑ j' : Fin B'.m, ∑ k' : Fin B'.m, pairEnergy (relCD A) (partC B' uv j') (partD B' uv k') := by
      have hlhs :
          (∑ j : Fin B.m, ∑ k : Fin B.m, pairEnergy (relCD A) (partC B uv j) (partD B uv k)) +
            ε ^ 4 * (Fintype.card B.W : ℝ) ^ 2 * badWeightCD ε A B uv =
          ∑ j : Fin B.m, ∑ k : Fin B.m,
            (pairEnergy (relCD A) (partC B uv j) (partD B uv k) +
              if IsQuasirandom ε (relCD A) (partC B uv j) (partD B uv k) then 0
              else ε ^ 4 * ((partC B uv j).card : ℝ) * ((partD B uv k).card : ℝ)) := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        dsimp only [badWeightCD]
        rw [mul_assoc, mul_div_cancel₀ _ (pow_ne_zero 2 hWpos.ne'), Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> ring
      rw [hlhs]
      exact hCD
    dsimp only [boxE2]
    have hsum3 :
        ((∑ i : Fin B.m, ∑ j : Fin B.m, pairEnergy (relBC A) (partB B uv i) (partC B uv j)) +
         (∑ i : Fin B.m, ∑ k : Fin B.m, pairEnergy (relBD A) (partB B uv i) (partD B uv k)) +
         (∑ j : Fin B.m, ∑ k : Fin B.m, pairEnergy (relCD A) (partC B uv j) (partD B uv k))) +
         ε ^ 4 * (Fintype.card B.W : ℝ) ^ 2 *
           (badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv) ≤
        ((∑ i' : Fin B'.m, ∑ j' : Fin B'.m, pairEnergy (relBC A) (partB B' uv i') (partC B' uv j')) +
         (∑ i' : Fin B'.m, ∑ k' : Fin B'.m, pairEnergy (relBD A) (partB B' uv i') (partD B' uv k')) +
         (∑ j' : Fin B'.m, ∑ k' : Fin B'.m, pairEnergy (relCD A) (partC B' uv j') (partD B' uv k'))) := by
      linarith
    have hdiv3 := div_le_div_of_nonneg_right hsum3 (by positivity : (0 : ℝ) ≤ 3 * (Fintype.card B.W : ℝ) ^ 2)
    have hrew :
        (((∑ i : Fin B.m, ∑ j : Fin B.m, pairEnergy (relBC A) (partB B uv i) (partC B uv j)) +
          (∑ i : Fin B.m, ∑ k : Fin B.m, pairEnergy (relBD A) (partB B uv i) (partD B uv k)) +
          (∑ j : Fin B.m, ∑ k : Fin B.m, pairEnergy (relCD A) (partC B uv j) (partD B uv k))) +
          ε ^ 4 * (Fintype.card B.W : ℝ) ^ 2 *
            (badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv)) /
            (3 * (Fintype.card B.W : ℝ) ^ 2) =
        ((∑ i : Fin B.m, ∑ j : Fin B.m, pairEnergy (relBC A) (partB B uv i) (partC B uv j)) +
         (∑ i : Fin B.m, ∑ k : Fin B.m, pairEnergy (relBD A) (partB B uv i) (partD B uv k)) +
         (∑ j : Fin B.m, ∑ k : Fin B.m, pairEnergy (relCD A) (partC B uv j) (partD B uv k))) /
          (3 * (Fintype.card B.W : ℝ) ^ 2) +
          ε ^ 4 * (badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv) / 3 := by
      field_simp [hWpos.ne']
    rw [hrew] at hdiv3
    exact hdiv3
  let bad : Finset ((G ⧸ B.W) × (G ⧸ B.W)) := univ.filter (fun uv => ¬ IsBoxQuasirandom ε A B uv)
  have hbad_gt : ε * (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 < (bad.card : ℝ) := lt_of_not_ge hnot
  have hqW : (0 : ℝ) < Fintype.card (G ⧸ B.W) := by exact_mod_cast card_quotient_pos B.W
  have hbw_nn : ∀ uv : (G ⧸ B.W) × (G ⧸ B.W),
      0 ≤ badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv := by
    intro uv
    have h1 : 0 ≤ badWeightBC ε A B uv := by
      dsimp only [badWeightBC]
      refine div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_) (sq_nonneg _)
      split_ifs <;> positivity
    have h2 : 0 ≤ badWeightBD ε A B uv := by
      dsimp only [badWeightBD]
      refine div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_) (sq_nonneg _)
      split_ifs <;> positivity
    have h3 : 0 ≤ badWeightCD ε A B uv := by
      dsimp only [badWeightCD]
      refine div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_) (sq_nonneg _)
      split_ifs <;> positivity
    linarith
  have hbox_step : ∀ uv : (G ⧸ B.W) × (G ⧸ B.W),
      boxE2 A B uv + (if uv ∈ bad then ε ^ 5 else 0) ≤ boxE2 A B' uv := by
    intro uv
    have hinc := hbox_inc uv
    by_cases huv : uv ∈ bad
    · rw [if_pos huv]
      have hnb : ¬ IsBoxQuasirandom ε A B uv := (Finset.mem_filter.mp huv).2
      have hgt3 : 3 * ε < badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv :=
        lt_of_not_ge hnb
      have he5 : ε ^ 5 ≤ ε ^ 4 * (badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv) / 3 := by
        have h1 : ε ^ 4 * (3 * ε) ≤
            ε ^ 4 * (badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv) :=
          mul_le_mul_of_nonneg_left hgt3.le (by positivity)
        linarith
      linarith
    · rw [if_neg huv, add_zero]
      have hnn : 0 ≤ ε ^ 4 * (badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv) / 3 :=
        div_nonneg (mul_nonneg (by positivity) (hbw_nn uv)) (by norm_num)
      linarith
  have hsum :
      (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE2 A B uv) + (bad.card : ℝ) * ε ^ 5 ≤
      ∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE2 A B' uv := by
    have hlhs :
        (∑ uv : (G ⧸ B.W) × (G ⧸ B.W), boxE2 A B uv) + (bad.card : ℝ) * ε ^ 5 =
        ∑ uv : (G ⧸ B.W) × (G ⧸ B.W), (boxE2 A B uv + if uv ∈ bad then ε ^ 5 else 0) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have : univ.filter (fun uv => uv ∈ bad) = bad := by ext uv; simp
      rw [this]
    rw [hlhs]
    exact Finset.sum_le_sum fun uv _ => hbox_step uv
  dsimp only [E2]
  have hdiv := div_le_div_of_nonneg_right hsum (sq_nonneg (Fintype.card (G ⧸ B.W) : ℝ))
  rw [add_div] at hdiv
  have hbad_e6 : ε ^ 6 ≤ (bad.card : ℝ) * ε ^ 5 / (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 := by
    rw [le_div_iff₀ (pow_pos hqW 2)]
    calc
      ε ^ 6 * (Fintype.card (G ⧸ B.W) : ℝ) ^ 2 = (ε * (Fintype.card (G ⧸ B.W) : ℝ) ^ 2) * ε ^ 5 := by ring
      _ ≤ (bad.card : ℝ) * ε ^ 5 := mul_le_mul_of_nonneg_right hbad_gt.le (by positivity)
  linarith

/- Dual-energy termination -/

def stepCodimA (c : ℕ) : ℕ := c + 4 ^ c

lemma stepCodimA_mono {c₁ c₂ : ℕ} (h : c₁ ≤ c₂) : stepCodimA c₁ ≤ stepCodimA c₂ := by
  dsimp only [stepCodimA]
  exact Nat.add_le_add h (Nat.pow_le_pow_right (by norm_num) h)

lemma stepCodimA_iterate_mono (k : ℕ) {c₁ c₂ : ℕ} (h : c₁ ≤ c₂) :
    stepCodimA^[k] c₁ ≤ stepCodimA^[k] c₂ := by
  induction k generalizing c₁ c₂ with
  | zero => exact h
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    exact ih (stepCodimA_mono h)

lemma le_stepCodimA (c : ℕ) : c ≤ stepCodimA c := Nat.le_add_right _ _

lemma le_stepCodimA_iterate (k c : ℕ) : c ≤ stepCodimA^[k] c := by
  induction k generalizing c with
  | zero => exact le_rfl
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    exact (le_stepCodimA c).trans (ih (stepCodimA c))

noncomputable def fuelA (ε : ℝ) (m : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) ^ 6 / ε ^ 3)

def stepM (m : ℕ) : ℕ := m * 2 ^ (2 * m)

noncomputable def boundCodim (ε : ℝ) : ℕ → ℕ → ℕ → ℕ
  | 0, m, c => stepCodimA^[fuelA ε m] c
  | k₂ + 1, m, c => boundCodim ε k₂ (stepM m) (stepCodimA^[fuelA ε m] c)

lemma boundCodim_mono (ε : ℝ) (k₂ : ℕ) :
    ∀ m c₁ c₂, c₁ ≤ c₂ → boundCodim ε k₂ m c₁ ≤ boundCodim ε k₂ m c₂ := by
  induction k₂ with
  | zero =>
    intro m c₁ c₂ h
    exact stepCodimA_iterate_mono _ h
  | succ k₂ ih =>
    intro m c₁ c₂ h
    exact ih (stepM m) _ _ (stepCodimA_iterate_mono _ h)

lemma le_boundCodim (ε : ℝ) (k₂ : ℕ) :
    ∀ m c, c ≤ boundCodim ε k₂ m c := by
  induction k₂ with
  | zero =>
    intro m c
    exact le_stepCodimA_iterate _ c
  | succ k₂ ih =>
    intro m c
    exact (le_stepCodimA_iterate _ c).trans (ih (stepM m) _)

lemma refine_to_cond1 {ε : ℝ} (hε : 0 < ε) (A : Finset (G × G)) :
    ∀ (k₁ : ℕ) (B : Boxing G),
      1 - E1 B ≤ (k₁ : ℝ) * (ε ^ 3 / (B.m : ℝ) ^ 6) →
      ∃ B' : Boxing G,
        Cond1 ε B' ∧
        B'.m = B.m ∧
        E2 A B ≤ E2 A B' ∧
        codim B'.W ≤ stepCodimA^[k₁] (codim B.W) := by
  intro k₁
  induction k₁ with
  | zero =>
    intro B hle
    simp only [Nat.cast_zero, zero_mul] at hle
    have hcond1 : Cond1 ε B := by
      by_contra hnot
      obtain ⟨B₁, _, _, hE1, _⟩ := refineA_step hε A B hnot
      have hpos : 0 < ε ^ 3 / (B.m : ℝ) ^ 6 := by
        have hmpos : (0 : ℝ) < B.m := by exact_mod_cast B.hm
        positivity
      have hle1 := E1_le_one B₁
      linarith
    exact ⟨B, hcond1, rfl, le_rfl, le_rfl⟩
  | succ k₁ ih =>
    intro B hle
    by_cases h1 : Cond1 ε B
    · exact ⟨B, h1, rfl, le_rfl, le_stepCodimA_iterate (k₁ + 1) (codim B.W)⟩
    · obtain ⟨B₁, hm1, hE2, hE1, hcod1⟩ := refineA_step hε A B h1
      have hle1 : 1 - E1 B₁ ≤ (k₁ : ℝ) * (ε ^ 3 / (B₁.m : ℝ) ^ 6) := by
        rw [hm1]
        rw [Nat.cast_succ, add_mul, one_mul] at hle
        linarith
      obtain ⟨B', hcond1', hm', hE2', hcod'⟩ := ih B₁ hle1
      refine ⟨B', hcond1', hm'.trans hm1, hE2.trans hE2', ?_⟩
      simp only [Function.iterate_succ, Function.comp_apply]
      exact hcod'.trans (stepCodimA_iterate_mono k₁ hcod1)

lemma fuelA_bound {ε : ℝ} (hε : 0 < ε) (B : Boxing G) :
    1 - E1 B ≤ (fuelA ε B.m : ℝ) * (ε ^ 3 / (B.m : ℝ) ^ 6) := by
  have hmpos : (0 : ℝ) < B.m := by exact_mod_cast B.hm
  have hceil : (B.m : ℝ) ^ 6 / ε ^ 3 ≤ (fuelA ε B.m : ℝ) := Nat.le_ceil _
  have hmul : 1 ≤ (fuelA ε B.m : ℝ) * (ε ^ 3 / (B.m : ℝ) ^ 6) := by
    calc
      (1 : ℝ) = ((B.m : ℝ) ^ 6 / ε ^ 3) * (ε ^ 3 / (B.m : ℝ) ^ 6) := by
        field_simp [hε.ne', hmpos.ne']
      _ ≤ (fuelA ε B.m : ℝ) * (ε ^ 3 / (B.m : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_right hceil (by positivity)
  linarith [E1_nonneg B]

lemma refine_to_cond1_cond2 {ε : ℝ} (hε : 0 < ε) (A : Finset (G × G)) :
    ∀ (k₂ : ℕ) (B : Boxing G),
      1 - E2 A B ≤ (k₂ : ℝ) * ε ^ 6 →
      ∃ B' : Boxing G,
        Cond1 ε B' ∧ Cond2 ε A B' ∧ codim B'.W ≤ boundCodim ε k₂ B.m (codim B.W) := by
  intro k₂
  induction k₂ with
  | zero =>
    intro B hle
    simp only [Nat.cast_zero, zero_mul] at hle
    obtain ⟨B₁, hcond1, _, hE2, hcod1⟩ := refine_to_cond1 hε A (fuelA ε B.m) B (fuelA_bound hε B)
    have hcond2 : Cond2 ε A B₁ := by
      by_contra hnot
      obtain ⟨B₂, _, _, hE2'⟩ := refineB_step hε A B₁ hnot
      have hpos : 0 < ε ^ 6 := by positivity
      have hle1 := E2_le_one A B₂
      linarith
    exact ⟨B₁, hcond1, hcond2, hcod1⟩
  | succ k₂ ih =>
    intro B hle
    obtain ⟨B₁, hcond1, hm1, hE2_1, hcod1⟩ := refine_to_cond1 hε A (fuelA ε B.m) B (fuelA_bound hε B)
    by_cases h2 : Cond2 ε A B₁
    · refine ⟨B₁, hcond1, h2, ?_⟩
      change codim B₁.W ≤ boundCodim ε k₂ (stepM B.m) (stepCodimA^[fuelA ε B.m] (codim B.W))
      exact hcod1.trans (le_boundCodim ε k₂ (stepM B.m) _)
    · obtain ⟨B₂, hW2, hm2, hE2_2⟩ := refineB_step hε A B₁ h2
      have hle2 : 1 - E2 A B₂ ≤ (k₂ : ℝ) * ε ^ 6 := by
        rw [Nat.cast_succ, add_mul, one_mul] at hle
        linarith
      obtain ⟨B', hcond1', hcond2', hcod'⟩ := ih B₂ hle2
      refine ⟨B', hcond1', hcond2', ?_⟩
      change codim B'.W ≤ boundCodim ε k₂ (stepM B.m) (stepCodimA^[fuelA ε B.m] (codim B.W))
      have hm2' : B₂.m = stepM B.m := by rw [hm2, hm1]; rfl
      rw [hm2', hW2] at hcod'
      exact hcod'.trans (boundCodim_mono ε k₂ (stepM B.m) _ _ hcod1)

lemma codim_top : codim (⊤ : Submodule (ZMod 2) G) = 0 := by
  have h1 := finrank_add_codim (⊤ : Submodule (ZMod 2) G)
  have h2 := finrank_top (ZMod 2) G
  omega

lemma regular_boxing_exists_general {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ : ℕ, ∀ (G : Type*) [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] [DecidableEq G]
      (A : Finset (G × G)),
      ∃ B : Boxing G, Cond1 ε B ∧ Cond2 ε A B ∧ codim B.W ≤ C₀ := by
  let k₂ : ℕ := Nat.ceil (1 / ε ^ 6)
  refine ⟨boundCodim ε k₂ 1 0, fun G _ _ _ _ A => ?_⟩
  let B₀ : Boxing G := {
    W := ⊤
    m := 1
    hm := Nat.one_pos
    idxB := fun _ _ => 0
    idxC := fun _ _ => 0
    idxD := fun _ _ => 0
  }
  have hle : 1 - E2 A B₀ ≤ (k₂ : ℝ) * ε ^ 6 := by
    have hceil : 1 / ε ^ 6 ≤ (k₂ : ℝ) := Nat.le_ceil _
    have hmul : 1 ≤ (k₂ : ℝ) * ε ^ 6 := by
      calc (1 : ℝ) = (1 / ε ^ 6) * ε ^ 6 := by field_simp [hε.ne']
        _ ≤ (k₂ : ℝ) * ε ^ 6 := mul_le_mul_of_nonneg_right hceil (by positivity)
    linarith [E2_nonneg A B₀]
  obtain ⟨B, h1, h2, hcod⟩ := refine_to_cond1_cond2 hε A k₂ B₀ hle
  have hcod0 : codim B₀.W = 0 := codim_top
  rw [hcod0] at hcod
  exact ⟨B, h1, h2, hcod⟩

end Refinements

theorem regular_boxing_exists {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C₀ : ℕ, ∀ (n : ℕ) (A : Finset (𝔽₂ n × 𝔽₂ n)),
      ∃ B : Boxing (𝔽₂ n), Cond1 ε B ∧ Cond2 ε A B ∧ codim B.W ≤ C₀ := by
  have _ := hε1
  obtain ⟨C₀, hC₀⟩ := regular_boxing_exists_general hε
  exact ⟨C₀, fun n A => hC₀ (𝔽₂ n) A⟩

section Counting

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G] [DecidableEq G]

private lemma eq_add_xz_of_sum_eq_zero {x y z : G} (h : x + y + z = 0) : x + z = y := by
  have h1 : (x + y + z) + (x + z) = y := by
    calc (x + y + z) + (x + z) = (x + x) + (z + z) + y := by abel
      _ = 0 + 0 + y := by rw [add_self_eq_zero_f2, add_self_eq_zero_f2]
      _ = y := by simp
  rw [h, zero_add] at h1
  exact h1

private lemma eq_add_yz_of_sum_eq_zero {x y z : G} (h : x + y + z = 0) : y + z = x := by
  have h1 : (x + y + z) + (y + z) = x := by
    calc (x + y + z) + (y + z) = (y + y) + (z + z) + x := by abel
      _ = 0 + 0 + x := by rw [add_self_eq_zero_f2, add_self_eq_zero_f2]
      _ = x := by simp
  rw [h, zero_add] at h1
  exact h1

private lemma sum_comp_fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (φ : α → β) (g : β → ℝ) :
    (∑ a : α, g (φ a)) =
      ∑ b : β, (((univ : Finset α).filter (fun a => φ a = b)).card : ℝ) * g b := by
  have h1 : ∀ a : α, g (φ a) = ∑ b : β, if φ a = b then g b else 0 := fun a => by simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- Number of corners in `A` with difference `d ∈ W`, summed over `d : W`,
equals the sum over all outer boxes `(u, v)` of `(relBC, relBD, relCD)`-triangles. -/
lemma sum_corners_in_subspace (W : Submodule (ZMod 2) G) (A : Finset (G × G)) :
    (∑ d : W, (Green19.S d.1 A).card) =
    ∑ uv : (G ⧸ W) × (G ⧸ W),
      (((coset W uv.1 ×ˢ coset W uv.2 ×ˢ coset W (uv.1 + uv.2)).filter
        (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card) := by
  have hlhs :
      (∑ d : W, (Green19.S d.1 A).card) =
      ((univ : Finset (G × G × G)).filter (fun t : G × G × G =>
        t.1 + t.2.1 + t.2.2 ∈ W ∧ relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij
      (fun (p : Σ _ : W, G × G) _ => (p.2.1, p.2.2, p.2.1 + p.2.2 + p.1.1)) ?_ ?_ ?_
    · rintro ⟨d, ⟨x, y⟩⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Green19.S, Finset.mem_filter] at hp
      dsimp only [Green19.IsCorner] at hp
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only [relBC, relBD, relCD]
      have hsum : x + y + (x + y + d.1) = d.1 := by
        rw [← add_assoc, add_self_eq_zero_f2, zero_add]
      have hxz : x + (x + y + d.1) = y + d.1 := by
        rw [← add_assoc, ← add_assoc, add_self_eq_zero_f2, zero_add]
      have hyz : y + (x + y + d.1) = x + d.1 := by
        calc y + (x + y + d.1) = (y + y) + (x + d.1) := by abel
          _ = 0 + (x + d.1) := by rw [add_self_eq_zero_f2]
          _ = x + d.1 := zero_add _
      rw [hsum, hxz, hyz]
      exact ⟨d.2, hp.1, hp.2.2, hp.2.1⟩
    · rintro ⟨d₁, ⟨x₁, y₁⟩⟩ _ ⟨d₂, ⟨x₂, y₂⟩⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, hd⟩ := heq
      have hd' : d₁ = d₂ := Subtype.ext (add_left_cancel hd)
      subst hd'
      rfl
    · rintro ⟨x, y, z⟩ ht
      rw [Finset.mem_filter] at ht
      obtain ⟨_, hW, h1, h2, h3⟩ := ht
      dsimp only [relBC, relBD, relCD] at h1 h2 h3
      let d : W := ⟨x + y + z, hW⟩
      have hxz : y + d.1 = x + z := by
        dsimp only [d]
        calc y + (x + y + z) = (y + y) + (x + z) := by abel
          _ = 0 + (x + z) := by rw [add_self_eq_zero_f2]
          _ = x + z := zero_add _
      have hyz : x + d.1 = y + z := by
        dsimp only [d]
        calc x + (x + y + z) = (x + x) + (y + z) := by abel
          _ = 0 + (y + z) := by rw [add_self_eq_zero_f2]
          _ = y + z := zero_add _
      have hback : x + y + d.1 = z := by
        dsimp only [d]
        rw [← add_assoc, add_self_eq_zero_f2, zero_add]
      refine ⟨⟨d, (x, y)⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Green19.S, Finset.mem_filter]
        dsimp only [Green19.IsCorner]
        rw [hxz, hyz]
        exact ⟨h1, h3, h2⟩
      · simp [hback]
  rw [hlhs]
  have hpart :
      ((univ : Finset ((G ⧸ W) × (G ⧸ W))).biUnion fun uv =>
        (coset W uv.1 ×ˢ coset W uv.2 ×ˢ coset W (uv.1 + uv.2)).filter
          (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)) =
      (univ : Finset (G × G × G)).filter (fun t : G × G × G =>
        t.1 + t.2.1 + t.2.2 ∈ W ∧ relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2) := by
    ext ⟨x, y, z⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_product, mem_coset]
    constructor
    · rintro ⟨⟨u, v⟩, ⟨⟨rfl, rfl, hz⟩, hrel⟩⟩
      refine ⟨?_, hrel⟩
      rw [← Submodule.Quotient.mk_eq_zero W, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, hz]
      exact add_self_eq_zero_f2 (Submodule.Quotient.mk x + Submodule.Quotient.mk y)
    · rintro ⟨hW, hrel⟩
      refine ⟨(Submodule.Quotient.mk x, Submodule.Quotient.mk y), ⟨⟨rfl, rfl, ?_⟩, hrel⟩⟩
      have h0 : Submodule.Quotient.mk (p := W) (x + y + z) = 0 :=
        (Submodule.Quotient.mk_eq_zero W).mpr hW
      rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add] at h0
      have h1 := congrArg ((Submodule.Quotient.mk (p := W) x + Submodule.Quotient.mk (p := W) y) + ·) h0
      simp only [add_zero, ← add_assoc, add_self_eq_zero_f2, zero_add] at h1
      exact h1
  rw [← hpart, Finset.card_biUnion]
  intro uv₁ _ uv₂ _ hne
  change Disjoint _ _
  rw [Finset.disjoint_left]
  rintro ⟨x, y, z⟩ h1 h2
  simp only [Finset.mem_filter, Finset.mem_product, mem_coset] at h1 h2
  exact hne (Prod.ext (h1.1.1.symm.trans h2.1.1) (h1.1.2.1.symm.trans h2.1.2.1))

/-- Density of `A` inside outer box `uv = (u, v)`:
`|A ∩ (coset W u × coset W v)| / |W|^2`. -/
noncomputable def boxDensity (W : Submodule (ZMod 2) G) (A : Finset (G × G))
    (uv : (G ⧸ W) × (G ⧸ W)) : ℝ :=
  (((coset W uv.1 ×ˢ coset W uv.2).filter (fun p => p ∈ A)).card : ℝ) / (Fintype.card W : ℝ) ^ 2

lemma avg_boxDensity (W : Submodule (ZMod 2) G) (A : Finset (G × G)) :
    (∑ uv : (G ⧸ W) × (G ⧸ W), boxDensity W A uv) / (Fintype.card (G ⧸ W) : ℝ) ^ 2 =
      (A.card : ℝ) / (Fintype.card G : ℝ) ^ 2 := by
  have hG : (Fintype.card (G ⧸ W) : ℝ) * (Fintype.card W : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast card_quotient_mul_card W
  have hpart :
      ((univ : Finset ((G ⧸ W) × (G ⧸ W))).biUnion fun uv =>
        (coset W uv.1 ×ˢ coset W uv.2).filter (fun p => p ∈ A)) = A := by
    ext ⟨x, y⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_product, mem_coset]
    constructor
    · rintro ⟨_, _, hA⟩; exact hA
    · intro hA; exact ⟨(Submodule.Quotient.mk x, Submodule.Quotient.mk y), ⟨rfl, rfl⟩, hA⟩
  have hsum :
      (∑ uv : (G ⧸ W) × (G ⧸ W), (((coset W uv.1 ×ˢ coset W uv.2).filter (fun p => p ∈ A)).card : ℝ)) =
      (A.card : ℝ) := by
    have h1 : A.card = ∑ uv : (G ⧸ W) × (G ⧸ W),
        ((coset W uv.1 ×ˢ coset W uv.2).filter (fun p => p ∈ A)).card := by
      conv_lhs => rw [← hpart]
      rw [Finset.card_biUnion]
      intro uv₁ _ uv₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [Finset.mem_filter, Finset.mem_product, mem_coset] at h1 h2
      exact hne (Prod.ext (h1.1.1.symm.trans h2.1.1) (h1.1.2.symm.trans h2.1.2))
    exact_mod_cast h1.symm
  dsimp only [boxDensity]
  rw [← Finset.sum_div, hsum, div_div, ← mul_pow, mul_comm, hG]

lemma boxDensity_nonneg (W : Submodule (ZMod 2) G) (A : Finset (G × G))
    (uv : (G ⧸ W) × (G ⧸ W)) : 0 ≤ boxDensity W A uv := by
  dsimp [boxDensity]; positivity

lemma boxDensity_le_one (W : Submodule (ZMod 2) G) (A : Finset (G × G))
    (uv : (G ⧸ W) × (G ⧸ W)) : boxDensity W A uv ≤ 1 := by
  have hw : (0 : ℝ) < Fintype.card W := by exact_mod_cast card_submodule_pos W
  dsimp [boxDensity]
  rw [div_le_one (pow_pos hw 2)]
  have hle : ((coset W uv.1 ×ˢ coset W uv.2).filter (fun p => p ∈ A)).card ≤
      (coset W uv.1 ×ˢ coset W uv.2).card := Finset.card_filter_le _ _
  rw [Finset.card_product, card_coset, card_coset, ← sq] at hle
  exact_mod_cast hle

/-- Convexity of `t ↦ (max (t - ε) 0) ^ c` for `c ≥ 1`. -/
lemma convexOn_max_sub_rpow {c : ℝ} (hc : 1 ≤ c) (ε : ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => (max (t - ε) 0) ^ c) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h1 : max (a * x + b * y - ε) 0 ≤ a * max (x - ε) 0 + b * max (y - ε) 0 := by
    rw [max_le_iff]
    constructor
    · have hx : x - ε ≤ max (x - ε) 0 := le_max_left _ _
      have hy : y - ε ≤ max (y - ε) 0 := le_max_left _ _
      have : a * x + b * y - ε = a * (x - ε) + b * (y - ε) := by
        calc a * x + b * y - ε = a * x + b * y - (a + b) * ε := by rw [hab, one_mul]
          _ = a * (x - ε) + b * (y - ε) := by ring
      rw [this]
      exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have hmono : (max (a * x + b * y - ε) 0) ^ c ≤ (a * max (x - ε) 0 + b * max (y - ε) 0) ^ c :=
    Real.rpow_le_rpow (le_max_right _ _) h1 (by linarith)
  have hconv := (convexOn_rpow hc).2 (Set.mem_Ici.mpr (le_max_right (x - ε) 0))
    (Set.mem_Ici.mpr (le_max_right (y - ε) 0)) ha hb hab
  simp only [smul_eq_mul] at hconv
  exact hmono.trans hconv

/-- Number of zero-sum triples in cell `(i, j, k)` with `(x, y) ∈ A`. -/
noncomputable def triCount (A : Finset (G × G)) (B : Boxing G)
    (uv : (G ⧸ B.W) × (G ⧸ B.W)) (i j k : Fin B.m) : ℝ :=
  (((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
    (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A)).card : ℝ)

lemma sum_triCount_k (A : Finset (G × G)) (B : Boxing G)
    (uv : (G ⧸ B.W) × (G ⧸ B.W)) (i j : Fin B.m) :
    (∑ k : Fin B.m, triCount A B uv i j k) =
      (edgeCount (relBC A) (partB B uv i) (partC B uv j) : ℝ) := by
  have hnat :
      (∑ k : Fin B.m,
        ((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
          (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A)).card) =
      edgeCount (relBC A) (partB B uv i) (partC B uv j) := by
    have hbiU :
        ((univ : Finset (Fin B.m)).biUnion fun k =>
          (partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
            (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A)) =
        (partB B uv i ×ˢ partC B uv j ×ˢ coset B.W (uv.1 + uv.2)).filter
          (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A) := by
      ext ⟨x, y, z⟩
      simp only [mem_biUnion, mem_univ, true_and, mem_filter, mem_product, partD]
      constructor
      · rintro ⟨k, ⟨hx, hy, hz, _⟩, hcond⟩; exact ⟨⟨hx, hy, hz⟩, hcond⟩
      · rintro ⟨⟨hx, hy, hz⟩, hcond⟩; exact ⟨B.idxD uv z, ⟨hx, hy, hz, rfl⟩, hcond⟩
    have hdisj : ∀ k₁ ∈ (univ : Finset (Fin B.m)), ∀ k₂ ∈ (univ : Finset (Fin B.m)), k₁ ≠ k₂ →
        Disjoint
          ((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k₁).filter
            (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A))
          ((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k₂).filter
            (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A)) := by
      intro k₁ _ k₂ _ hne
      rw [Finset.disjoint_left]
      rintro ⟨x, y, z⟩ h1 h2
      simp only [mem_filter, mem_product] at h1 h2
      exact Finset.disjoint_left.mp (partD_disjoint B uv hne) h1.1.2.2 h2.1.2.2
    rw [← Finset.card_biUnion hdisj, hbiU]
    dsimp only [edgeCount]
    refine Finset.card_bij (fun t _ => (t.1, t.2.1)) ?_ ?_ ?_
    · rintro ⟨x, y, z⟩ ht
      simp only [Finset.mem_filter, Finset.mem_product] at ht ⊢
      exact ⟨⟨ht.1.1, ht.1.2.1⟩, ht.2.2⟩
    · rintro ⟨x₁, y₁, z₁⟩ h1 ⟨x₂, y₂, z₂⟩ h2 heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Finset.mem_filter] at h1 h2
      have hz : z₁ = z₂ := add_left_cancel (h1.2.1.trans h2.2.1.symm)
      subst hz
      rfl
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hx, hy⟩, hA⟩ := hp
      dsimp only [relBC] at hA
      refine ⟨(x, y, x + y), ?_, rfl⟩
      simp only [mem_filter, mem_product]
      refine ⟨⟨hx, hy, ?_⟩, add_self_eq_zero_f2 (x + y), hA⟩
      rw [mem_coset, Submodule.Quotient.mk_add,
          mem_coset.mp (partB_subset B uv i hx), mem_coset.mp (partC_subset B uv j hy)]
  dsimp only [triCount]
  rw [← Nat.cast_sum, hnat]

lemma sum_triCount_j (A : Finset (G × G)) (B : Boxing G)
    (uv : (G ⧸ B.W) × (G ⧸ B.W)) (i k : Fin B.m) :
    (∑ j : Fin B.m, triCount A B uv i j k) =
      (edgeCount (relBD A) (partB B uv i) (partD B uv k) : ℝ) := by
  have hnat :
      (∑ j : Fin B.m,
        ((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
          (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A)).card) =
      edgeCount (relBD A) (partB B uv i) (partD B uv k) := by
    have hbiU :
        ((univ : Finset (Fin B.m)).biUnion fun j =>
          (partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
            (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A)) =
        (partB B uv i ×ˢ coset B.W uv.2 ×ˢ partD B uv k).filter
          (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A) := by
      ext ⟨x, y, z⟩
      simp only [mem_biUnion, mem_univ, true_and, mem_filter, mem_product, partC]
      constructor
      · rintro ⟨j, ⟨hx, ⟨hy, _⟩, hz⟩, hcond⟩; exact ⟨⟨hx, hy, hz⟩, hcond⟩
      · rintro ⟨⟨hx, hy, hz⟩, hcond⟩; exact ⟨B.idxC uv y, ⟨hx, ⟨hy, rfl⟩, hz⟩, hcond⟩
    have hdisj : ∀ j₁ ∈ (univ : Finset (Fin B.m)), ∀ j₂ ∈ (univ : Finset (Fin B.m)), j₁ ≠ j₂ →
        Disjoint
          ((partB B uv i ×ˢ partC B uv j₁ ×ˢ partD B uv k).filter
            (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A))
          ((partB B uv i ×ˢ partC B uv j₂ ×ˢ partD B uv k).filter
            (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A)) := by
      intro j₁ _ j₂ _ hne
      rw [Finset.disjoint_left]
      rintro ⟨x, y, z⟩ h1 h2
      simp only [mem_filter, mem_product] at h1 h2
      exact Finset.disjoint_left.mp (partC_disjoint B uv hne) h1.1.2.1 h2.1.2.1
    rw [← Finset.card_biUnion hdisj, hbiU]
    dsimp only [edgeCount]
    refine Finset.card_bij (fun t _ => (t.1, t.2.2)) ?_ ?_ ?_
    · rintro ⟨x, y, z⟩ ht
      simp only [Finset.mem_filter, Finset.mem_product] at ht ⊢
      refine ⟨⟨ht.1.1, ht.1.2.2⟩, ?_⟩
      dsimp only [relBD]
      rw [eq_add_xz_of_sum_eq_zero ht.2.1]
      exact ht.2.2
    · rintro ⟨x₁, y₁, z₁⟩ h1 ⟨x₂, y₂, z₂⟩ h2 heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Finset.mem_filter] at h1 h2
      have hy : y₁ = y₂ := (eq_add_xz_of_sum_eq_zero h1.2.1).symm.trans (eq_add_xz_of_sum_eq_zero h2.2.1)
      subst hy
      rfl
    · rintro ⟨x, z⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hx, hz⟩, hA⟩ := hp
      dsimp only [relBD] at hA
      refine ⟨(x, x + z, z), ?_, rfl⟩
      simp only [mem_filter, mem_product]
      refine ⟨⟨hx, ?_, hz⟩, ?_, hA⟩
      · rw [mem_coset, Submodule.Quotient.mk_add,
            mem_coset.mp (partB_subset B uv i hx), mem_coset.mp (partD_subset B uv k hz),
            ← add_assoc, add_self_eq_zero_f2, zero_add]
      · calc x + (x + z) + z = (x + x) + (z + z) := by abel
          _ = 0 + 0 := by rw [add_self_eq_zero_f2, add_self_eq_zero_f2]
          _ = 0 := add_zero 0
  dsimp only [triCount]
  rw [← Nat.cast_sum, hnat]

lemma sum_triCount_i (A : Finset (G × G)) (B : Boxing G)
    (uv : (G ⧸ B.W) × (G ⧸ B.W)) (j k : Fin B.m) :
    (∑ i : Fin B.m, triCount A B uv i j k) =
      (edgeCount (relCD A) (partC B uv j) (partD B uv k) : ℝ) := by
  have hnat :
      (∑ i : Fin B.m,
        ((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
          (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A)).card) =
      edgeCount (relCD A) (partC B uv j) (partD B uv k) := by
    have hbiU :
        ((univ : Finset (Fin B.m)).biUnion fun i =>
          (partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
            (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A)) =
        (coset B.W uv.1 ×ˢ partC B uv j ×ˢ partD B uv k).filter
          (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A) := by
      ext ⟨x, y, z⟩
      simp only [mem_biUnion, mem_univ, true_and, mem_filter, mem_product, partB]
      constructor
      · rintro ⟨i, ⟨⟨hx, _⟩, hy, hz⟩, hcond⟩; exact ⟨⟨hx, hy, hz⟩, hcond⟩
      · rintro ⟨⟨hx, hy, hz⟩, hcond⟩; exact ⟨B.idxB uv x, ⟨⟨hx, rfl⟩, hy, hz⟩, hcond⟩
    have hdisj : ∀ i₁ ∈ (univ : Finset (Fin B.m)), ∀ i₂ ∈ (univ : Finset (Fin B.m)), i₁ ≠ i₂ →
        Disjoint
          ((partB B uv i₁ ×ˢ partC B uv j ×ˢ partD B uv k).filter
            (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A))
          ((partB B uv i₂ ×ˢ partC B uv j ×ˢ partD B uv k).filter
            (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0 ∧ (t.1, t.2.1) ∈ A)) := by
      intro i₁ _ i₂ _ hne
      rw [Finset.disjoint_left]
      rintro ⟨x, y, z⟩ h1 h2
      simp only [mem_filter, mem_product] at h1 h2
      exact Finset.disjoint_left.mp (partB_disjoint B uv hne) h1.1.1 h2.1.1
    rw [← Finset.card_biUnion hdisj, hbiU]
    dsimp only [edgeCount]
    refine Finset.card_bij (fun t _ => (t.2.1, t.2.2)) ?_ ?_ ?_
    · rintro ⟨x, y, z⟩ ht
      simp only [Finset.mem_filter, Finset.mem_product] at ht ⊢
      refine ⟨⟨ht.1.2.1, ht.1.2.2⟩, ?_⟩
      dsimp only [relCD]
      rw [eq_add_yz_of_sum_eq_zero ht.2.1]
      exact ht.2.2
    · rintro ⟨x₁, y₁, z₁⟩ h1 ⟨x₂, y₂, z₂⟩ h2 heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Finset.mem_filter] at h1 h2
      have hx : x₁ = x₂ := (eq_add_yz_of_sum_eq_zero h1.2.1).symm.trans (eq_add_yz_of_sum_eq_zero h2.2.1)
      subst hx
      rfl
    · rintro ⟨y, z⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hy, hz⟩, hA⟩ := hp
      dsimp only [relCD] at hA
      refine ⟨(y + z, y, z), ?_, rfl⟩
      simp only [mem_filter, mem_product]
      refine ⟨⟨?_, hy, hz⟩, ?_, hA⟩
      · rw [mem_coset, Submodule.Quotient.mk_add,
            mem_coset.mp (partC_subset B uv j hy), mem_coset.mp (partD_subset B uv k hz)]
        calc uv.2 + (uv.1 + uv.2) = (uv.2 + uv.2) + uv.1 := by abel
          _ = 0 + uv.1 := by rw [add_self_eq_zero_f2]
          _ = uv.1 := zero_add _
      · calc (y + z) + y + z = (y + y) + (z + z) := by abel
          _ = 0 + 0 := by rw [add_self_eq_zero_f2, add_self_eq_zero_f2]
          _ = 0 := add_zero 0
  dsimp only [triCount]
  rw [← Nat.cast_sum, hnat]

lemma sum_triCount_all (A : Finset (G × G)) (B : Boxing G)
    (uv : (G ⧸ B.W) × (G ⧸ B.W)) :
    (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, triCount A B uv i j k) =
      boxDensity B.W A uv * (Fintype.card B.W : ℝ) ^ 2 := by
  have hWpos : (0 : ℝ) < Fintype.card B.W := by exact_mod_cast card_submodule_pos B.W
  simp_rw [sum_triCount_k]
  have hnat :
      (∑ i : Fin B.m, ∑ j : Fin B.m, edgeCount (relBC A) (partB B uv i) (partC B uv j)) =
      ((coset B.W uv.1 ×ˢ coset B.W uv.2).filter (fun p => p ∈ A)).card := by
    rw [← Fintype.sum_prod_type (f := fun ij : Fin B.m × Fin B.m => edgeCount (relBC A) (partB B uv ij.1) (partC B uv ij.2))]
    have hbiU :
        ((univ : Finset (Fin B.m × Fin B.m)).biUnion fun ij =>
          (partB B uv ij.1 ×ˢ partC B uv ij.2).filter (fun p => relBC A p.1 p.2)) =
        (coset B.W uv.1 ×ˢ coset B.W uv.2).filter (fun p => p ∈ A) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_product]
      simp only [partB, partC, Finset.mem_filter]
      dsimp only [relBC]
      constructor
      · rintro ⟨⟨i, j⟩, ⟨⟨hx, _⟩, ⟨hy, _⟩⟩, hA⟩; exact ⟨⟨hx, hy⟩, hA⟩
      · rintro ⟨⟨hx, hy⟩, hA⟩; exact ⟨(B.idxB uv x, B.idxC uv y), ⟨⟨hx, rfl⟩, ⟨hy, rfl⟩⟩, hA⟩
    have hdisj : ∀ ij₁ ∈ (univ : Finset (Fin B.m × Fin B.m)),
        ∀ ij₂ ∈ (univ : Finset (Fin B.m × Fin B.m)), ij₁ ≠ ij₂ →
        Disjoint
          ((partB B uv ij₁.1 ×ˢ partC B uv ij₁.2).filter (fun p => relBC A p.1 p.2))
          ((partB B uv ij₂.1 ×ˢ partC B uv ij₂.2).filter (fun p => relBC A p.1 p.2)) := by
      rintro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ hne
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [mem_filter, mem_product, partB, partC] at h1 h2
      exact hne (Prod.ext (h1.1.1.2.symm.trans h2.1.1.2) (h1.1.2.2.symm.trans h2.1.2.2))
    dsimp only [edgeCount]
    rw [← Finset.card_biUnion hdisj, hbiU]
  have hcast :
      (∑ i : Fin B.m, ∑ j : Fin B.m, (edgeCount (relBC A) (partB B uv i) (partC B uv j) : ℝ)) =
      (((coset B.W uv.1 ×ˢ coset B.W uv.2).filter (fun p => p ∈ A)).card : ℝ) := by
    exact_mod_cast hnat
  rw [hcast]
  dsimp only [boxDensity]
  exact (div_mul_cancel₀ _ (pow_ne_zero 2 hWpos.ne')).symm


/-- One-box corner lower bound on a regular outer box `uv`. -/
lemma box_corners_lower_bound {c b : ℝ} (hc : 1 ≤ c) (hb : 0 < b)
    (htrif : ∀ q : ℕ, 0 < q → ∀ H : Finset (Fin q × Fin q × Fin q),
      let xy (e : Fin q × Fin q × Fin q) := (e.1, e.2.1)
      let xz (e : Fin q × Fin q × Fin q) := (e.1, e.2.2)
      let yz (e : Fin q × Fin q × Fin q) := (e.2.1, e.2.2)
      let deg (proj : (Fin q × Fin q × Fin q) → Fin q × Fin q) (x : Fin q × Fin q) : ℝ :=
        (H.filter (fun e => proj e = x)).card
      let density : ℝ := H.card / (q : ℝ) ^ 3
      let triforce := (∑ e : Fin q × Fin q × Fin q,
        deg xy (xy e) * deg xz (xz e) * deg yz (yz e)) / (q : ℝ) ^ 6
      b * density ^ c ≤ triforce)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (A : Finset (G × G)) (B : Boxing G) (uv : (G ⧸ B.W) × (G ⧸ B.W))
    (hunif : IsBoxUniform ε B uv) (hqr : IsBoxQuasirandom ε A B uv) :
    (b * (max (boxDensity B.W A uv - ε) 0) ^ c - 8 * ε) * (Fintype.card B.W : ℝ) ^ 3 ≤
      (((coset B.W uv.1 ×ˢ coset B.W uv.2 ×ˢ coset B.W (uv.1 + uv.2)).filter
        (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card : ℝ) := by
  have hWpos : (0 : ℝ) < Fintype.card B.W := by exact_mod_cast card_submodule_pos B.W
  have hmpos : (0 : ℝ) < B.m := by exact_mod_cast B.hm
  let wB (i : Fin B.m) : ℝ := ((partB B uv i).card : ℝ)
  let wC (j : Fin B.m) : ℝ := ((partC B uv j).card : ℝ)
  let wD (k : Fin B.m) : ℝ := ((partD B uv k).card : ℝ)
  let dBC (i j : Fin B.m) : ℝ := pairDensity (relBC A) (partB B uv i) (partC B uv j)
  let dBD (i k : Fin B.m) : ℝ := pairDensity (relBD A) (partB B uv i) (partD B uv k)
  let dCD (j k : Fin B.m) : ℝ := pairDensity (relCD A) (partC B uv j) (partD B uv k)
  let f' (i j k : Fin B.m) : ℝ :=
    triCount A B uv i j k * (Fintype.card B.W : ℝ) / (wB i * wC j * wD k)
  let f (i j k : Fin B.m) : ℝ := min (f' i j k) 1
  have hmul_f' : ∀ i j k : Fin B.m,
      wB i * wC j * wD k * f' i j k = triCount A B uv i j k * (Fintype.card B.W : ℝ) := by
    intro i j k
    by_cases h0 : wB i * wC j * wD k = 0
    · have htri0 : triCount A B uv i j k = 0 := by
        dsimp only [wB, wC, wD] at h0
        have hdisj : (partB B uv i).card = 0 ∨ (partC B uv j).card = 0 ∨ (partD B uv k).card = 0 := by
          rcases mul_eq_zero.mp h0 with h12 | h3
          · rcases mul_eq_zero.mp h12 with h1 | h2
            · left; exact_mod_cast h1
            · right; left; exact_mod_cast h2
          · right; right; exact_mod_cast h3
        dsimp only [triCount]
        rcases hdisj with h1 | h2 | h3
        · rw [Finset.card_eq_zero.mp h1]; simp
        · rw [Finset.card_eq_zero.mp h2]; simp
        · rw [Finset.card_eq_zero.mp h3]; simp
      rw [h0, zero_mul, htri0, zero_mul]
    · dsimp only [f']
      exact mul_div_cancel₀ _ h0
  have htri_ub : ∀ i j k : Fin B.m,
      triCount A B uv i j k ≤
        wB i * wC j * wD k / (Fintype.card B.W : ℝ) +
          (ε / (B.m : ℝ) ^ 3) * (Fintype.card B.W : ℝ) ^ 2 := by
    intro i j k
    have hdrop : triCount A B uv i j k ≤
        (((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
          (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = 0)).card : ℝ) := by
      dsimp only [triCount]
      exact_mod_cast Finset.card_le_card
        (fun t ht => by simp only [mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.1⟩)
    exact hdrop.trans (triple_sum_coset_le (partB_subset B uv i) (partC_subset B uv j)
      (partD_subset B uv k) (by positivity) (hunif i))
  have hclip : ∀ i j k : Fin B.m,
      (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * (f' i j k - f i j k) ≤
        ε / (B.m : ℝ) ^ 3 := by
    intro i j k
    by_cases hle : f' i j k ≤ 1
    · rw [show f i j k = f' i j k from min_eq_left hle, sub_self, mul_zero]
      positivity
    · rw [show f i j k = 1 from min_eq_right (le_of_not_ge hle)]
      have hub := htri_ub i j k
      have hmulW : triCount A B uv i j k * (Fintype.card B.W : ℝ) ≤
          wB i * wC j * wD k + (ε / (B.m : ℝ) ^ 3) * (Fintype.card B.W : ℝ) ^ 3 := by
        have h1 := mul_le_mul_of_nonneg_right hub hWpos.le
        have hsimp : (wB i * wC j * wD k / (Fintype.card B.W : ℝ) +
            (ε / (B.m : ℝ) ^ 3) * (Fintype.card B.W : ℝ) ^ 2) * (Fintype.card B.W : ℝ) =
            wB i * wC j * wD k + (ε / (B.m : ℝ) ^ 3) * (Fintype.card B.W : ℝ) ^ 3 := by
          field_simp
        linarith
      have hdiff : wB i * wC j * wD k * f' i j k - wB i * wC j * wD k ≤
          (ε / (B.m : ℝ) ^ 3) * (Fintype.card B.W : ℝ) ^ 3 := by
        rw [hmul_f']; linarith
      have hdiv := div_le_div_of_nonneg_right hdiff (pow_nonneg hWpos.le 3)
      have hlhs : (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * (f' i j k - 1) =
          (wB i * wC j * wD k * f' i j k - wB i * wC j * wD k) / (Fintype.card B.W : ℝ) ^ 3 := by
        ring
      have hrhs : (ε / (B.m : ℝ) ^ 3) * (Fintype.card B.W : ℝ) ^ 3 / (Fintype.card B.W : ℝ) ^ 3 =
          ε / (B.m : ℝ) ^ 3 :=
        mul_div_cancel_right₀ _ (pow_ne_zero 3 hWpos.ne')
      rw [hlhs]
      exact hdiv.trans_eq hrhs
  have hsum_f' :
      (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * f' i j k) = boxDensity B.W A uv := by
    have hterm : ∀ i j k : Fin B.m,
        (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * f' i j k =
        triCount A B uv i j k * (Fintype.card B.W : ℝ) / (Fintype.card B.W : ℝ) ^ 3 := by
      intro i j k
      rw [← hmul_f' i j k]
      ring
    simp_rw [hterm, ← Finset.sum_div, ← Finset.sum_mul]
    rw [sum_triCount_all]
    calc boxDensity B.W A uv * (Fintype.card B.W : ℝ) ^ 2 * (Fintype.card B.W : ℝ) /
          (Fintype.card B.W : ℝ) ^ 3
        = boxDensity B.W A uv * ((Fintype.card B.W : ℝ) ^ 3 / (Fintype.card B.W : ℝ) ^ 3) := by ring
      _ = boxDensity B.W A uv := by rw [div_self (pow_ne_zero 3 hWpos.ne'), mul_one]
  have hsum_f_ge :
      max (boxDensity B.W A uv - ε) 0 ≤
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * f i j k := by
    rw [max_le_iff]
    constructor
    · have hsum_clip :
          (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
            (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * (f' i j k - f i j k)) ≤ ε := by
        calc
          (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
              (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * (f' i j k - f i j k))
              ≤ ∑ _i : Fin B.m, ∑ _j : Fin B.m, ∑ _k : Fin B.m, (ε / (B.m : ℝ) ^ 3) :=
                Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
                  Finset.sum_le_sum fun k _ => hclip i j k
          _ = ε := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                field_simp
      have hsplit :
          (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
            (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * (f' i j k - f i j k)) =
          (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
            (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * f' i j k) -
          (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
            (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * f i j k) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [hsplit, hsum_f'] at hsum_clip
      linarith
    · refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun k _ => mul_nonneg (by dsimp only [wB, wC, wD]; positivity)
          (le_min (by dsimp only [f', triCount, wB, wC, wD]; positivity) zero_le_one)
  -- Lift f to F : B.W × B.W × B.W → ℝ
  let φB : B.W → Fin B.m := fun a => B.idxB uv (uv.1.out + a.1)
  let φC : B.W → Fin B.m := fun b => B.idxC uv (uv.2.out + b.1)
  let φD : B.W → Fin B.m := fun c => B.idxD uv ((uv.1 + uv.2).out + c.1)
  let F : B.W × B.W × B.W → ℝ := fun t => f (φB t.1) (φC t.2.1) (φD t.2.2)
  have hfibB : ∀ i : Fin B.m, ((univ : Finset B.W).filter (fun a => φB a = i)).card = (partB B uv i).card := by
    intro i
    have heq : (univ : Finset B.W).filter (fun a => φB a = i) = shiftCoset B.W uv.1 (partB B uv i) := by
      ext a
      simp only [mem_filter, mem_univ, true_and, shiftCoset, partB, mem_coset, φB]
      have hmem : Submodule.Quotient.mk (p := B.W) (uv.1.out + a.1) = uv.1 := by
        rw [Submodule.Quotient.mk_add, mk_out, (Submodule.Quotient.mk_eq_zero B.W).mpr a.2, add_zero]
      simp [hmem]
    rw [heq, card_shiftCoset (partB_subset B uv i)]
  have hfibC : ∀ j : Fin B.m, ((univ : Finset B.W).filter (fun b => φC b = j)).card = (partC B uv j).card := by
    intro j
    have heq : (univ : Finset B.W).filter (fun b => φC b = j) = shiftCoset B.W uv.2 (partC B uv j) := by
      ext b
      simp only [mem_filter, mem_univ, true_and, shiftCoset, partC, mem_coset, φC]
      have hmem : Submodule.Quotient.mk (p := B.W) (uv.2.out + b.1) = uv.2 := by
        rw [Submodule.Quotient.mk_add, mk_out, (Submodule.Quotient.mk_eq_zero B.W).mpr b.2, add_zero]
      simp [hmem]
    rw [heq, card_shiftCoset (partC_subset B uv j)]
  have hfibD : ∀ k : Fin B.m, ((univ : Finset B.W).filter (fun c => φD c = k)).card = (partD B uv k).card := by
    intro k
    have heq : (univ : Finset B.W).filter (fun c => φD c = k) =
        shiftCoset B.W (uv.1 + uv.2) (partD B uv k) := by
      ext c
      simp only [mem_filter, mem_univ, true_and, shiftCoset, partD, mem_coset, φD]
      have hmem : Submodule.Quotient.mk (p := B.W) ((uv.1 + uv.2).out + c.1) = uv.1 + uv.2 := by
        rw [Submodule.Quotient.mk_add, mk_out, (Submodule.Quotient.mk_eq_zero B.W).mpr c.2, add_zero]
      simp [hmem]
    rw [heq, card_shiftCoset (partD_subset B uv k)]
  have hwB_pos : ∀ a : B.W, 0 < wB (φB a) := by
    intro a
    dsimp only [wB]
    have hpos : 0 < ((univ : Finset B.W).filter (fun x => φB x = φB a)).card :=
      Finset.card_pos.mpr ⟨a, by simp⟩
    rw [hfibB] at hpos
    exact_mod_cast hpos
  have hwC_pos : ∀ b : B.W, 0 < wC (φC b) := by
    intro b
    dsimp only [wC]
    have hpos : 0 < ((univ : Finset B.W).filter (fun x => φC x = φC b)).card :=
      Finset.card_pos.mpr ⟨b, by simp⟩
    rw [hfibC] at hpos
    exact_mod_cast hpos
  have hwD_pos : ∀ c : B.W, 0 < wD (φD c) := by
    intro c
    dsimp only [wD]
    have hpos : 0 < ((univ : Finset B.W).filter (fun x => φD x = φD c)).card :=
      Finset.card_pos.mpr ⟨c, by simp⟩
    rw [hfibD] at hpos
    exact_mod_cast hpos
  -- Average of F equals weighted average of f
  have hF_avg :
      (∑ t : B.W × B.W × B.W, F t) / (Fintype.card B.W : ℝ) ^ 3 =
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        (wB i * wC j * wD k / (Fintype.card B.W : ℝ) ^ 3) * f i j k := by
    have hsum : (∑ t : B.W × B.W × B.W, F t) =
        ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, wB i * wC j * wD k * f i j k := by
      simp only [Fintype.sum_prod_type, F]
      rw [sum_comp_fiber φB (fun i => ∑ b : B.W, ∑ c : B.W, f i (φC b) (φD c))]
      simp_rw [hfibB]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_comp_fiber φC (fun j => ∑ c : B.W, f i j (φD c))]
      simp_rw [hfibC]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sum_comp_fiber φD (fun k => f i j k)]
      simp_rw [hfibD]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by dsimp only [wB, wC, wD]; ring
    rw [hsum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => by ring
  -- Marginal upper bounds for F
  have hmXY_le : ∀ a b : B.W,
      (∑ c : B.W, F (a, b, c)) / (Fintype.card B.W : ℝ) ≤ dBC (φB a) (φC b) := by
    intro a b
    set i := φB a
    set j := φC b
    have hbi : 0 < wB i := hwB_pos a
    have hcj : 0 < wC j := hwC_pos b
    have hsumF : (∑ c : B.W, F (a, b, c)) = ∑ k : Fin B.m, wD k * f i j k := by
      have h := sum_comp_fiber φD (fun k => f i j k)
      simpa only [F, hfibD, wD] using h
    rw [hsumF]
    have hle1 : (∑ k : Fin B.m, wD k * f i j k) / (Fintype.card B.W : ℝ) ≤
        (∑ k : Fin B.m, wD k * f' i j k) / (Fintype.card B.W : ℝ) :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _))
        hWpos.le
    refine hle1.trans_eq ?_
    have hterm : ∀ k : Fin B.m, wD k * f' i j k / (Fintype.card B.W : ℝ) =
        triCount A B uv i j k / (wB i * wC j) := by
      intro k
      rw [div_eq_div_iff hWpos.ne' (mul_ne_zero hbi.ne' hcj.ne')]
      calc wD k * f' i j k * (wB i * wC j) = wB i * wC j * wD k * f' i j k := by ring
        _ = triCount A B uv i j k * (Fintype.card B.W : ℝ) := hmul_f' i j k
    rw [Finset.sum_div]
    simp_rw [hterm]
    rw [← Finset.sum_div, sum_triCount_k]
    dsimp only [dBC, pairDensity, wB, wC]
  have hmXZ_le : ∀ a c : B.W,
      (∑ b : B.W, F (a, b, c)) / (Fintype.card B.W : ℝ) ≤ dBD (φB a) (φD c) := by
    intro a c
    set i := φB a
    set k := φD c
    have hbi : 0 < wB i := hwB_pos a
    have hdk : 0 < wD k := hwD_pos c
    have hsumF : (∑ b : B.W, F (a, b, c)) = ∑ j : Fin B.m, wC j * f i j k := by
      have h := sum_comp_fiber φC (fun j => f i j k)
      simpa only [F, hfibC, wC] using h
    rw [hsumF]
    have hle1 : (∑ j : Fin B.m, wC j * f i j k) / (Fintype.card B.W : ℝ) ≤
        (∑ j : Fin B.m, wC j * f' i j k) / (Fintype.card B.W : ℝ) :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _))
        hWpos.le
    refine hle1.trans_eq ?_
    have hterm : ∀ j : Fin B.m, wC j * f' i j k / (Fintype.card B.W : ℝ) =
        triCount A B uv i j k / (wB i * wD k) := by
      intro j
      rw [div_eq_div_iff hWpos.ne' (mul_ne_zero hbi.ne' hdk.ne')]
      calc wC j * f' i j k * (wB i * wD k) = wB i * wC j * wD k * f' i j k := by ring
        _ = triCount A B uv i j k * (Fintype.card B.W : ℝ) := hmul_f' i j k
    rw [Finset.sum_div]
    simp_rw [hterm]
    rw [← Finset.sum_div, sum_triCount_j]
    dsimp only [dBD, pairDensity, wB, wD]
  have hmYZ_le : ∀ b c : B.W,
      (∑ a : B.W, F (a, b, c)) / (Fintype.card B.W : ℝ) ≤ dCD (φC b) (φD c) := by
    intro b c
    set j := φC b
    set k := φD c
    have hcj : 0 < wC j := hwC_pos b
    have hdk : 0 < wD k := hwD_pos c
    have hsumF : (∑ a : B.W, F (a, b, c)) = ∑ i : Fin B.m, wB i * f i j k := by
      have h := sum_comp_fiber φB (fun i => f i j k)
      simpa only [F, hfibB, wB] using h
    rw [hsumF]
    have hle1 : (∑ i : Fin B.m, wB i * f i j k) / (Fintype.card B.W : ℝ) ≤
        (∑ i : Fin B.m, wB i * f' i j k) / (Fintype.card B.W : ℝ) :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _))
        hWpos.le
    refine hle1.trans_eq ?_
    have hterm : ∀ i : Fin B.m, wB i * f' i j k / (Fintype.card B.W : ℝ) =
        triCount A B uv i j k / (wC j * wD k) := by
      intro i
      rw [div_eq_div_iff hWpos.ne' (mul_ne_zero hcj.ne' hdk.ne')]
      calc wB i * f' i j k * (wC j * wD k) = wB i * wC j * wD k * f' i j k := by ring
        _ = triCount A B uv i j k * (Fintype.card B.W : ℝ) := hmul_f' i j k
    rw [Finset.sum_div]
    simp_rw [hterm]
    rw [← Finset.sum_div, sum_triCount_i]
    dsimp only [dCD, pairDensity, wC, wD]
  -- Apply fractional triforce to F
  have hF0 : ∀ t : B.W × B.W × B.W, 0 ≤ F t := fun t =>
    le_min (by dsimp only [f', triCount, wB, wC, wD]; positivity) zero_le_one
  have hF1 : ∀ t : B.W × B.W × B.W, F t ≤ 1 := fun t => min_le_right _ _
  have hft := fractional_triforce hc hb htrif (α := B.W) F hF0 hF1
  dsimp only at hft
  have htrif_dens :
      b * (max (boxDensity B.W A uv - ε) 0) ^ c * (Fintype.card B.W : ℝ) ^ 3 ≤
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        dBC i j * dBD i k * dCD j k * wB i * wC j * wD k := by
    have hpow_le : b * (max (boxDensity B.W A uv - ε) 0) ^ c ≤
        b * ((∑ t : B.W × B.W × B.W, F t) / (Fintype.card B.W : ℝ) ^ 3) ^ c := by
      apply mul_le_mul_of_nonneg_left _ hb.le
      rw [hF_avg]
      exact Real.rpow_le_rpow (le_max_right _ _) hsum_f_ge (by linarith)
    have hrhs_le :
        (∑ t : B.W × B.W × B.W,
          ((∑ z : B.W, F (t.1, t.2.1, z)) / (Fintype.card B.W : ℝ)) *
          ((∑ y : B.W, F (t.1, y, t.2.2)) / (Fintype.card B.W : ℝ)) *
          ((∑ x : B.W, F (x, t.2.1, t.2.2)) / (Fintype.card B.W : ℝ))) ≤
        ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          dBC i j * dBD i k * dCD j k * wB i * wC j * wD k := by
      have hpt :
          (∑ t : B.W × B.W × B.W,
            ((∑ z : B.W, F (t.1, t.2.1, z)) / (Fintype.card B.W : ℝ)) *
            ((∑ y : B.W, F (t.1, y, t.2.2)) / (Fintype.card B.W : ℝ)) *
            ((∑ x : B.W, F (x, t.2.1, t.2.2)) / (Fintype.card B.W : ℝ))) ≤
          ∑ t : B.W × B.W × B.W,
            dBC (φB t.1) (φC t.2.1) * dBD (φB t.1) (φD t.2.2) * dCD (φC t.2.1) (φD t.2.2) := by
        refine Finset.sum_le_sum fun t _ => ?_
        have h1 : 0 ≤ (∑ z : B.W, F (t.1, t.2.1, z)) / (Fintype.card B.W : ℝ) :=
          div_nonneg (Finset.sum_nonneg fun z _ => hF0 _) hWpos.le
        have h2 : 0 ≤ (∑ y : B.W, F (t.1, y, t.2.2)) / (Fintype.card B.W : ℝ) :=
          div_nonneg (Finset.sum_nonneg fun y _ => hF0 _) hWpos.le
        have h3 : 0 ≤ (∑ x : B.W, F (x, t.2.1, t.2.2)) / (Fintype.card B.W : ℝ) :=
          div_nonneg (Finset.sum_nonneg fun x _ => hF0 _) hWpos.le
        have hd1 : 0 ≤ dBC (φB t.1) (φC t.2.1) := pairDensity_nonneg _ _ _
        have hd2 : 0 ≤ dBD (φB t.1) (φD t.2.2) := pairDensity_nonneg _ _ _
        exact mul_le_mul
          (mul_le_mul (hmXY_le t.1 t.2.1) (hmXZ_le t.1 t.2.2) h2 hd1)
          (hmYZ_le t.2.1 t.2.2) h3 (mul_nonneg hd1 hd2)
      refine hpt.trans_eq ?_
      simp only [Fintype.sum_prod_type]
      rw [sum_comp_fiber φB (fun i => ∑ b : B.W, ∑ c : B.W, dBC i (φC b) * dBD i (φD c) * dCD (φC b) (φD c))]
      simp_rw [hfibB]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_comp_fiber φC (fun j => ∑ c : B.W, dBC i j * dBD i (φD c) * dCD j (φD c))]
      simp_rw [hfibC]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sum_comp_fiber φD (fun k => dBC i j * dBD i k * dCD j k)]
      simp_rw [hfibD]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by dsimp only [wB, wC, wD]; ring
    have hchain := hpow_le.trans hft
    have hmul := mul_le_mul_of_nonneg_right hchain (pow_nonneg hWpos.le 3)
    rw [div_mul_cancel₀ _ (pow_ne_zero 3 hWpos.ne')] at hmul
    exact hmul.trans hrhs_le
  -- Partition triangles in the outer box over cells (i, j, k)
  have hpart_tri :
      (((coset B.W uv.1 ×ˢ coset B.W uv.2 ×ˢ coset B.W (uv.1 + uv.2)).filter
        (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card : ℝ) =
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        (((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
          (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card : ℝ) := by
    have hnat :
        ((coset B.W uv.1 ×ˢ coset B.W uv.2 ×ˢ coset B.W (uv.1 + uv.2)).filter
          (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card =
        ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          ((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
            (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card := by
      have hbiU :
          ((univ : Finset (Fin B.m × Fin B.m × Fin B.m)).biUnion fun ijk =>
            (partB B uv ijk.1 ×ˢ partC B uv ijk.2.1 ×ˢ partD B uv ijk.2.2).filter
              (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)) =
          (coset B.W uv.1 ×ˢ coset B.W uv.2 ×ˢ coset B.W (uv.1 + uv.2)).filter
            (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2) := by
        ext ⟨x, y, z⟩
        simp only [mem_biUnion, mem_univ, true_and, mem_filter, mem_product, partB, partC, partD]
        constructor
        · rintro ⟨⟨i, j, k⟩, ⟨⟨hx, _⟩, ⟨hy, _⟩, ⟨hz, _⟩⟩, hrel⟩; exact ⟨⟨hx, hy, hz⟩, hrel⟩
        · rintro ⟨⟨hx, hy, hz⟩, hrel⟩
          exact ⟨(B.idxB uv x, B.idxC uv y, B.idxD uv z), ⟨⟨hx, rfl⟩, ⟨hy, rfl⟩, ⟨hz, rfl⟩⟩, hrel⟩
      have hdisj : ∀ a ∈ (univ : Finset (Fin B.m × Fin B.m × Fin B.m)),
          ∀ b ∈ (univ : Finset (Fin B.m × Fin B.m × Fin B.m)), a ≠ b →
          Disjoint
            ((partB B uv a.1 ×ˢ partC B uv a.2.1 ×ˢ partD B uv a.2.2).filter
              (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2))
            ((partB B uv b.1 ×ˢ partC B uv b.2.1 ×ˢ partD B uv b.2.2).filter
              (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)) := by
        rintro ⟨i₁, j₁, k₁⟩ _ ⟨i₂, j₂, k₂⟩ _ hne
        rw [Finset.disjoint_left]
        rintro ⟨x, y, z⟩ h1 h2
        simp only [mem_filter, mem_product, partB, partC, partD] at h1 h2
        exact hne (Prod.ext (h1.1.1.2.symm.trans h2.1.1.2)
          (Prod.ext (h1.1.2.1.2.symm.trans h2.1.2.1.2) (h1.1.2.2.2.symm.trans h2.1.2.2.2)))
      rw [← hbiU, Finset.card_biUnion hdisj]
      simp only [Fintype.sum_prod_type]
    exact_mod_cast hnat
  -- Apply triangle_counting_lemma on quasirandom cells, bound bad cells by badWeight
  let badTerm (i j k : Fin B.m) : ℝ :=
    (if IsQuasirandom ε (relBC A) (partB B uv i) (partC B uv j) then (0 : ℝ) else wB i * wC j * wD k) +
    (if IsQuasirandom ε (relBD A) (partB B uv i) (partD B uv k) then (0 : ℝ) else wB i * wC j * wD k) +
    (if IsQuasirandom ε (relCD A) (partC B uv j) (partD B uv k) then (0 : ℝ) else wB i * wC j * wD k)
  have hcell : ∀ i j k : Fin B.m,
      (dBC i j * dBD i k * dCD j k - 5 * ε) * wB i * wC j * wD k - badTerm i j k ≤
      (((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
        (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card : ℝ) := by
    intro i j k
    have hw : 0 ≤ wB i * wC j * wD k :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hbad_case : wB i * wC j * wD k ≤ badTerm i j k →
        (dBC i j * dBD i k * dCD j k - 5 * ε) * wB i * wC j * wD k - badTerm i j k ≤
        (((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
          (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card : ℝ) := by
      intro hbt
      have h12 : dBC i j * dBD i k ≤ 1 := by
        calc dBC i j * dBD i k ≤ 1 * 1 :=
              mul_le_mul (pairDensity_le_one _ _ _) (pairDensity_le_one _ _ _)
                (pairDensity_nonneg _ _ _) zero_le_one
          _ = 1 := one_mul 1
      have hd : dBC i j * dBD i k * dCD j k ≤ 1 := by
        calc dBC i j * dBD i k * dCD j k ≤ 1 * 1 :=
              mul_le_mul h12 (pairDensity_le_one _ _ _) (pairDensity_nonneg _ _ _) zero_le_one
          _ = 1 := one_mul 1
      have hmul : (dBC i j * dBD i k * dCD j k - 5 * ε) * (wB i * wC j * wD k) ≤
          1 * (wB i * wC j * wD k) :=
        mul_le_mul_of_nonneg_right (by linarith only [hd, hε]) hw
      have hle0 : (dBC i j * dBD i k * dCD j k - 5 * ε) * wB i * wC j * wD k - badTerm i j k ≤ 0 := by
        have hrew : (dBC i j * dBD i k * dCD j k - 5 * ε) * wB i * wC j * wD k =
            (dBC i j * dBD i k * dCD j k - 5 * ε) * (wB i * wC j * wD k) := by ring
        linarith only [hmul, hbt, hrew]
      exact hle0.trans (Nat.cast_nonneg _)
    by_cases h1 : IsQuasirandom ε (relBC A) (partB B uv i) (partC B uv j)
    · by_cases h2 : IsQuasirandom ε (relBD A) (partB B uv i) (partD B uv k)
      · by_cases h3 : IsQuasirandom ε (relCD A) (partC B uv j) (partD B uv k)
        · have hbt : badTerm i j k = 0 := by
            dsimp only [badTerm]
            rw [if_pos h1, if_pos h2, if_pos h3]
            ring
          rw [hbt, sub_zero]
          exact triangle_counting_lemma hε hε1 (relBC A) (relBD A) (relCD A)
            (partB B uv i) (partC B uv j) (partD B uv k) h1 h2 h3
        · refine hbad_case ?_
          dsimp only [badTerm]
          rw [if_pos h1, if_pos h2, if_neg h3]
          linarith only []
      · refine hbad_case ?_
        dsimp only [badTerm]
        rw [if_pos h1, if_neg h2]
        have h3nn : 0 ≤ if IsQuasirandom ε (relCD A) (partC B uv j) (partD B uv k) then (0 : ℝ)
            else wB i * wC j * wD k := by
          split_ifs
          · exact le_rfl
          · exact hw
        linarith only [h3nn]
    · refine hbad_case ?_
      dsimp only [badTerm]
      rw [if_neg h1]
      have h2nn : 0 ≤ if IsQuasirandom ε (relBD A) (partB B uv i) (partD B uv k) then (0 : ℝ)
          else wB i * wC j * wD k := by
        split_ifs
        · exact le_rfl
        · exact hw
      have h3nn : 0 ≤ if IsQuasirandom ε (relCD A) (partC B uv j) (partD B uv k) then (0 : ℝ)
          else wB i * wC j * wD k := by
        split_ifs
        · exact le_rfl
        · exact hw
      linarith only [h2nn, h3nn]
  have hsum_w : (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, wB i * wC j * wD k) =
      (Fintype.card B.W : ℝ) ^ 3 := by
    simp_rw [← Finset.mul_sum]
    dsimp only [wB, wC, wD]
    simp_rw [sum_card_partD, ← Finset.sum_mul, ← Finset.mul_sum, sum_card_partC, ← Finset.sum_mul,
      sum_card_partB]
    ring
  have hsum_bad :
      (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, badTerm i j k) ≤
      3 * ε * (Fintype.card B.W : ℝ) ^ 3 := by
    have hpow3 : ∀ x : ℝ, x * (Fintype.card B.W : ℝ) = x / (Fintype.card B.W : ℝ) ^ 2 * (Fintype.card B.W : ℝ) ^ 3 := by
      intro x
      have h3 : (Fintype.card B.W : ℝ) ^ 3 = (Fintype.card B.W : ℝ) ^ 2 * (Fintype.card B.W : ℝ) := by ring
      rw [h3, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hWpos.ne')]
    have hBC :
        (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          if IsQuasirandom ε (relBC A) (partB B uv i) (partC B uv j) then (0 : ℝ) else wB i * wC j * wD k) =
        badWeightBC ε A B uv * (Fintype.card B.W : ℝ) ^ 3 := by
      have hfac : ∀ i j k : Fin B.m,
          (if IsQuasirandom ε (relBC A) (partB B uv i) (partC B uv j) then (0 : ℝ) else wB i * wC j * wD k) =
          (if IsQuasirandom ε (relBC A) (partB B uv i) (partC B uv j) then (0 : ℝ) else wB i * wC j) * wD k := by
        intro i j k; split_ifs <;> ring
      simp_rw [hfac, ← Finset.mul_sum]
      have hD : (∑ k : Fin B.m, wD k) = (Fintype.card B.W : ℝ) := sum_card_partD B uv
      simp_rw [hD, ← Finset.sum_mul]
      dsimp only [badWeightBC, wB, wC]
      exact hpow3 _
    have hBD :
        (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          if IsQuasirandom ε (relBD A) (partB B uv i) (partD B uv k) then (0 : ℝ) else wB i * wC j * wD k) =
        badWeightBD ε A B uv * (Fintype.card B.W : ℝ) ^ 3 := by
      have hswap :
          (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
            if IsQuasirandom ε (relBD A) (partB B uv i) (partD B uv k) then (0 : ℝ) else wB i * wC j * wD k) =
          ∑ i : Fin B.m, ∑ k : Fin B.m, ∑ j : Fin B.m,
            (if IsQuasirandom ε (relBD A) (partB B uv i) (partD B uv k) then (0 : ℝ) else wB i * wD k) * wC j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
      rw [hswap]
      simp_rw [← Finset.mul_sum]
      have hC : (∑ j : Fin B.m, wC j) = (Fintype.card B.W : ℝ) := sum_card_partC B uv
      simp_rw [hC, ← Finset.sum_mul]
      dsimp only [badWeightBD, wB, wD]
      exact hpow3 _
    have hCD :
        (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
          if IsQuasirandom ε (relCD A) (partC B uv j) (partD B uv k) then (0 : ℝ) else wB i * wC j * wD k) =
        badWeightCD ε A B uv * (Fintype.card B.W : ℝ) ^ 3 := by
      have hswap :
          (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
            if IsQuasirandom ε (relCD A) (partC B uv j) (partD B uv k) then (0 : ℝ) else wB i * wC j * wD k) =
          ∑ j : Fin B.m, ∑ k : Fin B.m, ∑ i : Fin B.m,
            (if IsQuasirandom ε (relCD A) (partC B uv j) (partD B uv k) then (0 : ℝ) else wC j * wD k) * wB i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
      rw [hswap]
      simp_rw [← Finset.mul_sum]
      have hB : (∑ i : Fin B.m, wB i) = (Fintype.card B.W : ℝ) := sum_card_partB B uv
      simp_rw [hB, ← Finset.sum_mul]
      dsimp only [badWeightCD, wC, wD]
      exact hpow3 _
    have hsplit :
        (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, badTerm i j k) =
        (badWeightBC ε A B uv + badWeightBD ε A B uv + badWeightCD ε A B uv) * (Fintype.card B.W : ℝ) ^ 3 := by
      dsimp only [badTerm]
      simp_rw [Finset.sum_add_distrib]
      rw [hBC, hBD, hCD]
      ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hqr (pow_nonneg hWpos.le 3)
  rw [hpart_tri]
  have hsum_cell :
      (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        ((dBC i j * dBD i k * dCD j k - 5 * ε) * wB i * wC j * wD k - badTerm i j k)) ≤
      ∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        (((partB B uv i ×ˢ partC B uv j ×ˢ partD B uv k).filter
          (fun t : G × G × G => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card : ℝ) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hcell i j k
  have hrearr :
      (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m,
        ((dBC i j * dBD i k * dCD j k - 5 * ε) * wB i * wC j * wD k - badTerm i j k)) =
      (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, dBC i j * dBD i k * dCD j k * wB i * wC j * wD k) -
      5 * ε * (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, wB i * wC j * wD k) -
      (∑ i : Fin B.m, ∑ j : Fin B.m, ∑ k : Fin B.m, badTerm i j k) := by
    have hpt : ∀ i j k : Fin B.m,
        (dBC i j * dBD i k * dCD j k - 5 * ε) * wB i * wC j * wD k - badTerm i j k =
        (dBC i j * dBD i k * dCD j k * wB i * wC j * wD k - 5 * ε * (wB i * wC j * wD k)) -
          badTerm i j k := by
      intro i j k; ring
    simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hrearr, hsum_w] at hsum_cell
  linarith

end Counting

/-- Main transfer theorem: assuming the regular boxing lemma, every convex power-law
triforce lower bound yields a valid popular-corners exponent (`H1`). -/
theorem solution_of_regularity
    (hreg : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∃ C₀ : ℕ, ∀ (n : ℕ) (A : Finset (𝔽₂ n × 𝔽₂ n)),
        ∃ B : Boxing (𝔽₂ n), Cond1 ε B ∧ Cond2 ε A B ∧ codim B.W ≤ C₀) :
    OMA.R_Green19_green_19_R1.H1 := by
  intro c hc b hb htrif
  refine ⟨b / 2, by positivity, ?_⟩
  intro α hα0 hα1
  have hαc : 0 < α ^ c := Real.rpow_pos_of_pos hα0 c
  have hgap : (0 : ℝ) < (1 / 4) * b * α ^ c := by positivity
  -- Pick ε > 0 small enough by continuity at 0
  let g : ℝ → ℝ := fun t => b * (α - t) ^ c - (2 * b + 8) * t
  have hg_cont : Continuous g :=
    (continuous_const.mul
      ((Real.continuous_rpow_const (by linarith)).comp (continuous_const.sub continuous_id))).sub
      (continuous_const.mul continuous_id)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp (hg_cont.continuousAt : ContinuousAt g 0)
    ((1 / 4) * b * α ^ c) hgap
  let ε : ℝ := min (δ / 2) (min 1 (α / 2))
  have hε : 0 < ε := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεα : ε ≤ α / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hε_good : (3 / 4) * b * α ^ c ≤ b * (α - ε) ^ c - (2 * b + 8) * ε := by
    have hdist : dist ε 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε]
      have : ε ≤ δ / 2 := min_le_left _ _
      linarith
    have hclose := hδ hdist
    rw [Real.dist_eq] at hclose
    have hg0 : g 0 = b * α ^ c := by simp [g]
    have habs := (abs_lt.mp hclose).1
    rw [hg0] at habs
    dsimp only [g] at habs
    linarith
  obtain ⟨C₀, hC₀⟩ := hreg hε hε1
  obtain ⟨k, hk⟩ := exists_nat_ge (4 / (b * α ^ c))
  have hle_two_pow : ∀ m : ℕ, m ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [pow_succ]; omega
  rw [Filter.eventually_atTop]
  refine ⟨C₀ + k + 1, fun n hn A => ?_⟩
  dsimp only
  intro hA
  let N : ℝ := (Fintype.card (𝔽₂ n) : ℝ)
  have hNpos : 0 < N := by
    dsimp only [N]
    exact_mod_cast (Fintype.card_pos (α := 𝔽₂ n))
  obtain ⟨B, hcond1, hcond2, hcodim⟩ := hC₀ n A
  let Q : ℝ := (Fintype.card (𝔽₂ n ⧸ B.W) : ℝ)
  let Wcard : ℝ := (Fintype.card B.W : ℝ)
  have hQpos : 0 < Q := by dsimp only [Q]; exact_mod_cast card_quotient_pos B.W
  have hWpos : 0 < Wcard := by dsimp only [Wcard]; exact_mod_cast card_submodule_pos B.W
  have hQW : Q * Wcard = N := by dsimp only [Q, Wcard, N]; exact_mod_cast card_quotient_mul_card B.W
  -- Lower bound |B.W| ≥ 2 ^ (n - C₀)
  have hcardG : Fintype.card (𝔽₂ n) = 2 ^ n := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hW_ge_nat : 2 ^ (n - C₀) ≤ Fintype.card B.W := by
    have hmul := card_quotient_mul_card B.W
    rw [card_quotient_eq_two_pow_codim, hcardG] at hmul
    have hpow_le : 2 ^ codim B.W ≤ 2 ^ C₀ := Nat.pow_le_pow_right (by norm_num) hcodim
    have h2n : 2 ^ C₀ * 2 ^ (n - C₀) = 2 ^ n := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    have h1 : 2 ^ C₀ * 2 ^ (n - C₀) ≤ 2 ^ C₀ * Fintype.card B.W := by
      calc 2 ^ C₀ * 2 ^ (n - C₀) = 2 ^ n := h2n
        _ = 2 ^ codim B.W * Fintype.card B.W := hmul.symm
        _ ≤ 2 ^ C₀ * Fintype.card B.W := Nat.mul_le_mul_right _ hpow_le
    exact Nat.le_of_mul_le_mul_left h1 (by positivity)
  have hW_ge2 : 2 ≤ Fintype.card B.W := by
    have h1 : 2 ^ 1 ≤ 2 ^ (n - C₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hW_big : 4 / (b * α ^ c) ≤ Wcard := by
    have hk_le : k ≤ Fintype.card B.W := by
      have h1 : k ≤ 2 ^ k := hle_two_pow k
      have h2 : 2 ^ k ≤ 2 ^ (n - C₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk_le_r : (k : ℝ) ≤ Wcard := by dsimp only [Wcard]; exact_mod_cast hk_le
    exact hk.trans hk_le_r
  -- Count irregular outer boxes
  let irreg : Finset ((𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W)) :=
    univ.filter (fun uv => ¬ (IsBoxUniform ε B uv ∧ IsBoxQuasirandom ε A B uv))
  have hirreg_card : (irreg.card : ℝ) ≤ 2 * ε * Q ^ 2 := by
    have hsub : irreg ⊆
        (univ.filter (fun uv => ¬ IsBoxUniform ε B uv)) ∪
        (univ.filter (fun uv => ¬ IsBoxQuasirandom ε A B uv)) := by
      intro uv huv
      simp only [irreg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at huv ⊢
      tauto
    have hnat : irreg.card ≤
        (univ.filter (fun uv => ¬ IsBoxUniform ε B uv)).card +
        (univ.filter (fun uv => ¬ IsBoxQuasirandom ε A B uv)).card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hr : (irreg.card : ℝ) ≤
        ((univ.filter (fun uv => ¬ IsBoxUniform ε B uv)).card : ℝ) +
        ((univ.filter (fun uv => ¬ IsBoxQuasirandom ε A B uv)).card : ℝ) := by
      exact_mod_cast hnat
    have hc1 : ((univ.filter (fun uv => ¬ IsBoxUniform ε B uv)).card : ℝ) ≤ ε * Q ^ 2 := hcond1
    have hc2 : ((univ.filter (fun uv => ¬ IsBoxQuasirandom ε A B uv)).card : ℝ) ≤ ε * Q ^ 2 := hcond2
    linarith
  -- Outer-box sum lower bound
  let φ : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W) → ℝ := fun uv => (max (boxDensity B.W A uv - ε) 0) ^ c
  have hφ_le_one : ∀ uv, φ uv ≤ 1 := by
    intro uv
    dsimp only [φ]
    have hle1 : max (boxDensity B.W A uv - ε) 0 ≤ 1 := by
      rw [max_le_iff]
      exact ⟨by linarith [boxDensity_le_one B.W A uv], zero_le_one⟩
    calc (max (boxDensity B.W A uv - ε) 0) ^ c ≤ (1 : ℝ) ^ c :=
          Real.rpow_le_rpow (le_max_right _ _) hle1 (by linarith)
      _ = 1 := Real.one_rpow c
  have hbox_pt : ∀ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W),
      (b * φ uv - 8 * ε - (if uv ∈ irreg then b else 0)) * Wcard ^ 3 ≤
      (((coset B.W uv.1 ×ˢ coset B.W uv.2 ×ˢ coset B.W (uv.1 + uv.2)).filter
        (fun t : 𝔽₂ n × 𝔽₂ n × 𝔽₂ n => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card : ℝ) := by
    intro uv
    by_cases hirr : uv ∈ irreg
    · rw [if_pos hirr]
      have h1 : b * φ uv ≤ b := by nlinarith [hφ_le_one uv, hb]
      have hle0 : (b * φ uv - 8 * ε - b) * Wcard ^ 3 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg hWpos.le 3)
      exact hle0.trans (Nat.cast_nonneg _)
    · rw [if_neg hirr, sub_zero]
      have hreg_uv : IsBoxUniform ε B uv ∧ IsBoxQuasirandom ε A B uv := by
        by_contra hnot
        exact hirr (Finset.mem_filter.mpr ⟨Finset.mem_univ uv, hnot⟩)
      exact box_corners_lower_bound hc hb htrif hε hε1 A B uv hreg_uv.1 hreg_uv.2
  -- Jensen on ∑ uv, φ uv
  have hsum_φ : Q ^ 2 * (α - ε) ^ c ≤ ∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), φ uv := by
    have hw_sum : (∑ _uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), (1 : ℝ) / Q ^ 2) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
      push_cast
      dsimp only [Q]
      field_simp
    have hjensen := (convexOn_max_sub_rpow hc ε).map_sum_le
      (t := (univ : Finset ((𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W))))
      (w := fun _ => (1 : ℝ) / Q ^ 2)
      (p := fun uv => boxDensity B.W A uv)
      (fun _ _ => by positivity)
      hw_sum
      (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hjensen
    have havg_eq : (∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), (1 : ℝ) / Q ^ 2 * boxDensity B.W A uv) =
        (A.card : ℝ) / N ^ 2 := by
      rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
      exact avg_boxDensity B.W A
    have hrhs_eq : (∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), (1 : ℝ) / Q ^ 2 * φ uv) =
        (∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), φ uv) / Q ^ 2 := by
      rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
    rw [havg_eq] at hjensen
    change (max ((A.card : ℝ) / N ^ 2 - ε) 0) ^ c ≤
      ∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), (1 : ℝ) / Q ^ 2 * φ uv at hjensen
    rw [hrhs_eq] at hjensen
    have hdens_ge : α ≤ (A.card : ℝ) / N ^ 2 := by
      rw [le_div_iff₀ (pow_pos hNpos 2)]
      exact hA
    have hmax_ge : α - ε ≤ max ((A.card : ℝ) / N ^ 2 - ε) 0 :=
      (by linarith : α - ε ≤ (A.card : ℝ) / N ^ 2 - ε).trans (le_max_left _ _)
    have hpow_ge : (α - ε) ^ c ≤ (max ((A.card : ℝ) / N ^ 2 - ε) 0) ^ c :=
      Real.rpow_le_rpow (by linarith) hmax_ge (by linarith)
    have hfinal := hpow_ge.trans hjensen
    rw [le_div_iff₀ (pow_pos hQpos 2)] at hfinal
    linarith
  -- Total corner sum over d : B.W
  have hsum_corners :
      (3 / 4) * b * α ^ c * N ^ 2 * Wcard ≤ ∑ d : B.W, ((Green19.S d.1 A).card : ℝ) := by
    have hsum_eq :
        (∑ d : B.W, ((Green19.S d.1 A).card : ℝ)) =
        ∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W),
          (((coset B.W uv.1 ×ˢ coset B.W uv.2 ×ˢ coset B.W (uv.1 + uv.2)).filter
            (fun t : 𝔽₂ n × 𝔽₂ n × 𝔽₂ n => relBC A t.1 t.2.1 ∧ relBD A t.1 t.2.2 ∧ relCD A t.2.1 t.2.2)).card : ℝ) := by
      exact_mod_cast sum_corners_in_subspace B.W A
    rw [hsum_eq]
    have hsum_le := Finset.sum_le_sum fun uv (_ : uv ∈ (univ : Finset ((𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W)))) =>
      hbox_pt uv
    have hirr_sum :
        (∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), (if uv ∈ irreg then b else 0)) =
        (irreg.card : ℝ) * b := by
      rw [← Finset.sum_filter]
      have hf : (univ : Finset ((𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W))).filter (fun uv => uv ∈ irreg) = irreg := by
        ext uv; simp
      rw [hf, Finset.sum_const, nsmul_eq_mul]
    have hconst_sum : (∑ _uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), (8 * ε : ℝ)) = Q ^ 2 * (8 * ε) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
      push_cast
      dsimp only [Q]
      ring
    have hlhs_simp :
        (∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W),
          (b * φ uv - 8 * ε - (if uv ∈ irreg then b else 0)) * Wcard ^ 3) =
        (b * (∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), φ uv) - Q ^ 2 * (8 * ε) - (irreg.card : ℝ) * b) *
          Wcard ^ 3 := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hconst_sum, hirr_sum]
    rw [hlhs_simp] at hsum_le
    have hbracket :
        (3 / 4) * b * α ^ c * Q ^ 2 ≤
        b * (∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), φ uv) - Q ^ 2 * (8 * ε) - (irreg.card : ℝ) * b := by
      have h1 : b * (Q ^ 2 * (α - ε) ^ c) ≤ b * (∑ uv : (𝔽₂ n ⧸ B.W) × (𝔽₂ n ⧸ B.W), φ uv) :=
        mul_le_mul_of_nonneg_left hsum_φ hb.le
      have h2 : (irreg.card : ℝ) * b ≤ (2 * ε * Q ^ 2) * b :=
        mul_le_mul_of_nonneg_right hirreg_card hb.le
      have h3 : (3 / 4) * b * α ^ c * Q ^ 2 ≤ (b * (α - ε) ^ c - (2 * b + 8) * ε) * Q ^ 2 :=
        mul_le_mul_of_nonneg_right hε_good (sq_nonneg Q)
      linarith
    have hmul_W := mul_le_mul_of_nonneg_right hbracket (pow_nonneg hWpos.le 3)
    have hNQ : (3 / 4) * b * α ^ c * Q ^ 2 * Wcard ^ 3 = (3 / 4) * b * α ^ c * N ^ 2 * Wcard := by
      rw [← hQW]; ring
    linarith
  -- Split off d = 0 and pigeonhole over nonzero d ∈ B.W
  have hzero_le : ((Green19.S (0 : B.W).1 A).card : ℝ) ≤ N ^ 2 := by
    have hnat : (Green19.S (0 : B.W).1 A).card ≤ Fintype.card (𝔽₂ n) * Fintype.card (𝔽₂ n) := by
      calc (Green19.S (0 : B.W).1 A).card ≤ (univ : Finset (𝔽₂ n × 𝔽₂ n)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card (𝔽₂ n) * Fintype.card (𝔽₂ n) := by rw [Finset.card_univ, Fintype.card_prod]
    have hr : ((Green19.S (0 : B.W).1 A).card : ℝ) ≤ N * N := by dsimp only [N]; exact_mod_cast hnat
    linarith [sq N]
  have hN2_small : N ^ 2 ≤ (1 / 4) * b * α ^ c * N ^ 2 * Wcard := by
    have h4 : 4 ≤ Wcard * (b * α ^ c) := (div_le_iff₀ (mul_pos hb hαc)).mp hW_big
    have h1 : 1 ≤ (1 / 4) * b * α ^ c * Wcard := by linarith
    have hmul := mul_le_mul_of_nonneg_right h1 (sq_nonneg N)
    linarith
  have herase_sum :
      (b / 2) * α ^ c * N ^ 2 * (Wcard - 1) ≤
      ∑ d ∈ (univ : Finset B.W).erase 0, ((Green19.S d.1 A).card : ℝ) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : B.W))] at hsum_corners
    have hnonneg : 0 ≤ (b / 2) * α ^ c * N ^ 2 := by positivity
    have hdrop1 : (b / 2) * α ^ c * N ^ 2 * (Wcard - 1) ≤ (b / 2) * α ^ c * N ^ 2 * Wcard :=
      mul_le_mul_of_nonneg_left (by linarith) hnonneg
    linarith
  have herase_card_nat : ((univ : Finset B.W).erase 0).card = Fintype.card B.W - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : B.W)), Finset.card_univ]
  have herase_ne : ((univ : Finset B.W).erase 0).Nonempty :=
    Finset.card_pos.mp (by omega)
  have herase_card_r : (((univ : Finset B.W).erase 0).card : ℝ) = Wcard - 1 := by
    rw [herase_card_nat, Nat.cast_sub (by omega : 1 ≤ Fintype.card B.W)]
    simp [Wcard]
  by_contra hno
  have hlt : ∀ d ∈ (univ : Finset B.W).erase 0,
      ((Green19.S d.1 A).card : ℝ) < (b / 2) * α ^ c * N ^ 2 := by
    intro d hd
    refine lt_of_not_ge fun hge => hno ⟨d.1, ?_, hge⟩
    intro h0
    exact (Finset.mem_erase.mp hd).1 (Subtype.ext h0)
  have hsum_lt := Finset.sum_lt_sum_of_nonempty herase_ne hlt
  rw [Finset.sum_const, nsmul_eq_mul, herase_card_r] at hsum_lt
  linarith

end Green19H1

theorem OMA.solution : OMA.R_Green19_green_19_R1.H1 :=
  Green19H1.solution_of_regularity Green19H1.regular_boxing_exists
