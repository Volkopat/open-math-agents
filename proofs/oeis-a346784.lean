import OMAStatements.S_oeis_a346784

/-!
Pure-kernel refutation of OEIS A346784 vs A346126 at (n = 10, k = 13, m = 14):
  recordSize pointsFit 13 ∧ recordRank pointsFit 13 = 10
  recordSize attainable 14 ∧ recordRank attainable 14 = 9 = 10 - 1
  yet 13 != 14.
-/

namespace OMA.S_oeis_a346784.Disproof

open Finset

-- ============================================================================
-- Step 1: Quadratic norm Q, bilinear form 2B, and incompatibility identities
-- ============================================================================

private def QR (u : Center) : ℝ :=
  u.1 ^ 2 + u.1 * u.2 + u.2 ^ 2

private def B2R (u v : Center) : ℝ :=
  2 * u.1 * v.1 + u.1 * v.2 + u.2 * v.1 + 2 * u.2 * v.2

private def QZ (u : Site) : ℤ :=
  u.1 ^ 2 + u.1 * u.2 + u.2 ^ 2

private def B2Z (u v : Site) : ℤ :=
  2 * u.1 * v.1 + u.1 * v.2 + u.2 * v.1 + 2 * u.2 * v.2

private def siteR (p : Site) : Center :=
  ((p.1 : ℝ), (p.2 : ℝ))

private def subC (u v : Center) : Center :=
  (u.1 - v.1, u.2 - v.2)

private lemma QR_nonneg (u : Center) : 0 ≤ QR u := by
  unfold QR
  nlinarith [sq_nonneg (2 * u.1 + u.2), sq_nonneg u.2]

private lemma QR_add_le (u v : Center) : QR (u.1 + v.1, u.2 + v.2) ≤ 2 * QR u + 2 * QR v := by
  have h := QR_nonneg (u.1 - v.1, u.2 - v.2)
  unfold QR at h ⊢
  nlinarith

private lemma cauchy_schwarz_R (u a : Center) : (B2R u a) ^ 2 ≤ 4 * QR u * QR a := by
  unfold QR B2R
  nlinarith [sq_nonneg (u.1 * a.2 - u.2 * a.1)]

private lemma QR_siteR_sub (p q : Site) :
    QR (subC (siteR p) (siteR q)) = (QZ (p.1 - q.1, p.2 - q.2) : ℝ) := by
  simp only [QR, QZ, subC, siteR]
  push_cast
  ring

private lemma pair_incompat (p₁ p₂ : Site) (o : Center) (s : ℝ)
    (h1 : QR (subC (siteR p₁) o) ≤ s) (h2 : QR (subC (siteR p₂) o) ≤ s) :
    (QZ (p₁.1 - p₂.1, p₁.2 - p₂.2) : ℝ) ≤ 4 * s := by
  have hdiff : QR (subC (siteR p₁) (siteR p₂)) = (QZ (p₁.1 - p₂.1, p₁.2 - p₂.2) : ℝ) :=
    QR_siteR_sub p₁ p₂
  have hm := QR_nonneg (o.1 - ((p₁.1 : ℝ) + (p₂.1 : ℝ)) / 2, o.2 - ((p₁.2 : ℝ) + (p₂.2 : ℝ)) / 2)
  rw [← hdiff]
  unfold QR at hm
  unfold QR subC siteR at h1 h2 ⊢
  dsimp only at hm h1 h2 ⊢
  nlinarith

private lemma pair_not_both_strict (p₁ p₂ : Site) (o : Center) (s : ℝ) (num den : ℤ)
    (hden : 0 < den) (hs : s < (num : ℝ) / (den : ℝ))
    (hd : 4 * num ≤ den * QZ (p₁.1 - p₂.1, p₁.2 - p₂.2)) :
    ¬ (QR (subC (siteR p₁) o) ≤ s ∧ QR (subC (siteR p₂) o) ≤ s) := by
  rintro ⟨h1, h2⟩
  have hle := pair_incompat p₁ p₂ o s h1 h2
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hdR : 4 * (num : ℝ) ≤ (den : ℝ) * (QZ (p₁.1 - p₂.1, p₁.2 - p₂.2) : ℝ) := by exact_mod_cast hd
  have hlt : (den : ℝ) * s < (num : ℝ) := by
    have := (lt_div_iff₀ hdenR).mp hs
    linarith
  nlinarith

private lemma triple_incompat (p₀ p₁ p₂ : Site) (o : Center) (s w₀ w₁ w₂ mx my R2 : ℝ)
    (hw0 : 0 ≤ w₀) (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂) (hwsum : w₀ + w₁ + w₂ = 1)
    (hmx : w₀ * (p₀.1 : ℝ) + w₁ * (p₁.1 : ℝ) + w₂ * (p₂.1 : ℝ) = mx)
    (hmy : w₀ * (p₀.2 : ℝ) + w₁ * (p₁.2 : ℝ) + w₂ * (p₂.2 : ℝ) = my)
    (hr0 : QR (subC (siteR p₀) (mx, my)) = R2)
    (hr1 : QR (subC (siteR p₁) (mx, my)) = R2)
    (hr2 : QR (subC (siteR p₂) (mx, my)) = R2)
    (h0 : QR (subC (siteR p₀) o) ≤ s)
    (h1 : QR (subC (siteR p₁) o) ≤ s)
    (h2 : QR (subC (siteR p₂) o) ≤ s) : R2 ≤ s := by
  have hQom := QR_nonneg (subC o (mx, my))
  have hid : w₀ * QR (subC (siteR p₀) o) + w₁ * QR (subC (siteR p₁) o) + w₂ * QR (subC (siteR p₂) o) =
      QR (subC o (mx, my)) + R2 := by
    have hbx : w₀ * ((p₀.1 : ℝ) - mx) + w₁ * ((p₁.1 : ℝ) - mx) + w₂ * ((p₂.1 : ℝ) - mx) = 0 := by
      calc w₀ * ((p₀.1 : ℝ) - mx) + w₁ * ((p₁.1 : ℝ) - mx) + w₂ * ((p₂.1 : ℝ) - mx)
          = (w₀ * (p₀.1 : ℝ) + w₁ * (p₁.1 : ℝ) + w₂ * (p₂.1 : ℝ)) - (w₀ + w₁ + w₂) * mx := by ring
        _ = mx - 1 * mx := by rw [hmx, hwsum]
        _ = 0 := by ring
    have hby : w₀ * ((p₀.2 : ℝ) - my) + w₁ * ((p₁.2 : ℝ) - my) + w₂ * ((p₂.2 : ℝ) - my) = 0 := by
      calc w₀ * ((p₀.2 : ℝ) - my) + w₁ * ((p₁.2 : ℝ) - my) + w₂ * ((p₂.2 : ℝ) - my)
          = (w₀ * (p₀.2 : ℝ) + w₁ * (p₁.2 : ℝ) + w₂ * (p₂.2 : ℝ)) - (w₀ + w₁ + w₂) * my := by ring
        _ = my - 1 * my := by rw [hmy, hwsum]
        _ = 0 := by ring
    have hexp : ∀ p : Site,
        QR (subC (siteR p) o) = QR (subC (siteR p) (mx, my)) + QR (subC o (mx, my)) -
          B2R (subC (siteR p) (mx, my)) (subC o (mx, my)) := by
      intro p; unfold QR B2R subC siteR; ring
    rw [hexp p₀, hexp p₁, hexp p₂, hr0, hr1, hr2]
    have hlin : w₀ * B2R (subC (siteR p₀) (mx, my)) (subC o (mx, my)) +
        w₁ * B2R (subC (siteR p₁) (mx, my)) (subC o (mx, my)) +
        w₂ * B2R (subC (siteR p₂) (mx, my)) (subC o (mx, my)) = 0 := by
      calc w₀ * B2R (subC (siteR p₀) (mx, my)) (subC o (mx, my)) +
            w₁ * B2R (subC (siteR p₁) (mx, my)) (subC o (mx, my)) +
            w₂ * B2R (subC (siteR p₂) (mx, my)) (subC o (mx, my))
          = (2 * (o.1 - mx) + (o.2 - my)) *
              (w₀ * ((p₀.1 : ℝ) - mx) + w₁ * ((p₁.1 : ℝ) - mx) + w₂ * ((p₂.1 : ℝ) - mx)) +
            ((o.1 - mx) + 2 * (o.2 - my)) *
              (w₀ * ((p₀.2 : ℝ) - my) + w₁ * ((p₁.2 : ℝ) - my) + w₂ * ((p₂.2 : ℝ) - my)) := by
              simp only [B2R, subC, siteR]; ring
        _ = 0 := by rw [hbx, hby]; ring
    calc w₀ * (R2 + QR (subC o (mx, my)) - B2R (subC (siteR p₀) (mx, my)) (subC o (mx, my))) +
          w₁ * (R2 + QR (subC o (mx, my)) - B2R (subC (siteR p₁) (mx, my)) (subC o (mx, my))) +
          w₂ * (R2 + QR (subC o (mx, my)) - B2R (subC (siteR p₂) (mx, my)) (subC o (mx, my)))
        = (w₀ + w₁ + w₂) * (R2 + QR (subC o (mx, my))) -
          (w₀ * B2R (subC (siteR p₀) (mx, my)) (subC o (mx, my)) +
           w₁ * B2R (subC (siteR p₁) (mx, my)) (subC o (mx, my)) +
           w₂ * B2R (subC (siteR p₂) (mx, my)) (subC o (mx, my))) := by ring
      _ = 1 * (R2 + QR (subC o (mx, my))) - 0 := by rw [hwsum, hlin]
      _ = QR (subC o (mx, my)) + R2 := by ring
  have hle0 := mul_le_mul_of_nonneg_left h0 hw0
  have hle1 := mul_le_mul_of_nonneg_left h1 hw1
  have hle2 := mul_le_mul_of_nonneg_left h2 hw2
  have hws : w₀ * s + w₁ * s + w₂ * s = s := by
    calc w₀ * s + w₁ * s + w₂ * s = (w₀ + w₁ + w₂) * s := by ring
      _ = s := by rw [hwsum, one_mul]
  linarith

-- The 5 explicit barycentric circumcenter triple exclusions
private lemma triple_excl_1 (o : Center) (s : ℝ) (hs : s < 1 / 3) :
    ¬ (QR (subC (siteR (0, 0)) o) ≤ s ∧ QR (subC (siteR (0, 1)) o) ≤ s ∧ QR (subC (siteR (1, 0)) o) ≤ s) := by
  rintro ⟨h0, h1, h2⟩
  have hle := triple_incompat (0, 0) (0, 1) (1, 0) o s (1/3) (1/3) (1/3) (1/3) (1/3) (1/3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by unfold QR subC siteR; norm_num) (by unfold QR subC siteR; norm_num) (by unfold QR subC siteR; norm_num)
    h0 h1 h2
  linarith

private lemma triple_excl_2 (o : Center) (s : ℝ) (hs : s < 49 / 25) :
    ¬ (QR (subC (siteR (-1, 0)) o) ≤ s ∧ QR (subC (siteR (1, 1)) o) ≤ s ∧ QR (subC (siteR (2, -1)) o) ≤ s) := by
  rintro ⟨h0, h1, h2⟩
  have hle := triple_incompat (-1, 0) (1, 1) (2, -1) o s (11/25) (7/25) (7/25) (2/5) 0 (49/25)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by unfold QR subC siteR; norm_num) (by unfold QR subC siteR; norm_num) (by unfold QR subC siteR; norm_num)
    h0 h1 h2
  linarith

private lemma triple_excl_3 (o : Center) (s : ℝ) (hs : s < 7 / 3) :
    ¬ (QR (subC (siteR (-1, 0)) o) ≤ s ∧ QR (subC (siteR (-1, 2)) o) ≤ s ∧ QR (subC (siteR (2, -1)) o) ≤ s) := by
  rintro ⟨h0, h1, h2⟩
  have hle := triple_incompat (-1, 0) (-1, 2) (2, -1) o s (1/6) (7/18) (4/9) (1/3) (1/3) (7/3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by unfold QR subC siteR; norm_num) (by unfold QR subC siteR; norm_num) (by unfold QR subC siteR; norm_num)
    h0 h1 h2
  linarith

private lemma triple_excl_4 (o : Center) (s : ℝ) (hs : s < 7 / 3) :
    ¬ (QR (subC (siteR (0, -1)) o) ≤ s ∧ QR (subC (siteR (0, 2)) o) ≤ s ∧ QR (subC (siteR (2, 0)) o) ≤ s) := by
  rintro ⟨h0, h1, h2⟩
  have hle := triple_incompat (0, -1) (0, 2) (2, 0) o s (4/9) (7/18) (1/6) (1/3) (1/3) (7/3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by unfold QR subC siteR; norm_num) (by unfold QR subC siteR; norm_num) (by unfold QR subC siteR; norm_num)
    h0 h1 h2
  linarith

private lemma triple_excl_5 (o : Center) (s : ℝ) (hs : s ≤ 13 / 4) :
    ¬ (QR (subC (siteR (-2, 1)) o) ≤ s ∧ QR (subC (siteR (-1, -1)) o) ≤ s ∧ QR (subC (siteR (2, 0)) o) ≤ s) := by
  rintro ⟨h0, h1, h2⟩
  have hle := triple_incompat (-2, 1) (-1, -1) (2, 0) o s (13/49) (13/49) (23/49) (1/7) 0 (169/49)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by unfold QR subC siteR; norm_num) (by unfold QR subC siteR; norm_num) (by unfold QR subC siteR; norm_num)
    h0 h1 h2
  linarith

-- ============================================================================
-- Step 2: Symmetry reduction (Z^2 semidirect D_6) to T_0 and universe U_31
-- ============================================================================

private def inT0 (o : Center) : Prop :=
  0 ≤ o.2 ∧ o.2 ≤ o.1 ∧ 2 * o.1 + o.2 ≤ 1

private structure Sym where
  mapZ : Site → Site
  mapR : Center → Center
  compat : ∀ p : Site, mapR (siteR p) = siteR (mapZ p)
  injZ : Function.Injective mapZ
  presQ : ∀ u v : Center, QR (subC (mapR u) (mapR v)) = QR (subC u v)

private def Sym.id : Sym where
  mapZ := fun p => p
  mapR := fun u => u
  compat := fun _ => rfl
  injZ := Function.injective_id
  presQ := fun _ _ => rfl

private def Sym.comp (g f : Sym) : Sym where
  mapZ := g.mapZ ∘ f.mapZ
  mapR := g.mapR ∘ f.mapR
  compat := fun p => by simp [f.compat, g.compat]
  injZ := g.injZ.comp f.injZ
  presQ := fun u v => by simp [g.presQ, f.presQ]

private def Sym.trans (a b : ℤ) : Sym where
  mapZ := fun p => (p.1 + a, p.2 + b)
  mapR := fun u => (u.1 + (a : ℝ), u.2 + (b : ℝ))
  compat := fun p => by simp [siteR]
  injZ := fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) (by omega)
  presQ := fun u v => by unfold QR subC; ring

private def Sym.flip11 : Sym where
  mapZ := fun p => (1 - p.1, 1 - p.2)
  mapR := fun u => (1 - u.1, 1 - u.2)
  compat := fun p => by simp [siteR]
  injZ := fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) (by omega)
  presQ := fun u v => by unfold QR subC; ring

private def Sym.swap : Sym where
  mapZ := fun p => (p.2, p.1)
  mapR := fun u => (u.2, u.1)
  compat := fun p => by simp [siteR]
  injZ := fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  presQ := fun u v => by unfold QR subC; ring

private def Sym.cyc : Sym where
  mapZ := fun p => (1 - p.1 - p.2, p.1)
  mapR := fun u => (1 - u.1 - u.2, u.1)
  compat := fun p => by simp [siteR]
  injZ := fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 (by omega)
  presQ := fun u v => by unfold QR subC; ring

private lemma Sym.pres_unitStep (g : Sym) (p q : Site) :
    unitStep (g.mapZ p) (g.mapZ q) ↔ unitStep p q := by
  have hq : (QZ ((g.mapZ p).1 - (g.mapZ q).1, (g.mapZ p).2 - (g.mapZ q).2) : ℝ) =
      (QZ (p.1 - q.1, p.2 - q.2) : ℝ) := by
    rw [← QR_siteR_sub, ← QR_siteR_sub, ← g.compat p, ← g.compat q, g.presQ]
  have hqi : QZ ((g.mapZ p).1 - (g.mapZ q).1, (g.mapZ p).2 - (g.mapZ q).2) =
      QZ (p.1 - q.1, p.2 - q.2) := by exact_mod_cast hq
  simp only [unitStep]
  change QZ ((g.mapZ p).1 - (g.mapZ q).1, (g.mapZ p).2 - (g.mapZ q).2) = 1 ↔
    QZ (p.1 - q.1, p.2 - q.2) = 1
  rw [hqi]

private lemma Sym.pres_valid (g : Sym) (m : ℕ) (p : ℕ → Site) (hv : valid m p) :
    valid m (fun i => g.mapZ (p i)) := by
  refine ⟨fun i hi => (g.pres_unitStep _ _).mpr (hv.1 i hi), ?_, ?_⟩
  · intro i j hij hjm heq
    exact hv.2.1 i j hij hjm (g.injZ heq)
  · intro heq
    exact hv.2.2 (g.injZ heq)

private lemma Sym.pres_fits (g : Sym) (m : ℕ) (p : ℕ → Site) (o : Center) (s : ℝ)
    (hf : fits m p o s) : fits m (fun i => g.mapZ (p i)) (g.mapR o) s := by
  intro i hi
  have h := hf i hi
  have heq : QR (subC (siteR (g.mapZ (p i))) (g.mapR o)) = QR (subC (siteR (p i)) o) := by
    rw [← g.compat (p i), g.presQ]
  simpa only [QR, subC, siteR] using heq.le.trans h

private lemma exists_sym_inT0 (o : Center) : ∃ g : Sym, inT0 (g.mapR o) := by
  -- Step 1: translate into [0, 1)^2
  set g1 : Sym := Sym.trans (-⌊o.1⌋) (-⌊o.2⌋)
  set u1 : Center := g1.mapR o
  have hu1_0 : 0 ≤ u1.1 ∧ 0 ≤ u1.2 ∧ u1.1 < 1 ∧ u1.2 < 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [u1, g1, Sym.trans, Int.cast_neg]
    · linarith [Int.floor_le o.1]
    · linarith [Int.floor_le o.2]
    · linarith [Int.lt_floor_add_one o.1]
    · linarith [Int.lt_floor_add_one o.2]
  -- Step 2: ensure x + y <= 1 using flip11 if needed
  have hstep2 : ∃ g2 : Sym, 0 ≤ (g2.mapR o).1 ∧ 0 ≤ (g2.mapR o).2 ∧ (g2.mapR o).1 + (g2.mapR o).2 ≤ 1 := by
    by_cases hsum : u1.1 + u1.2 ≤ 1
    · exact ⟨g1, hu1_0.1, hu1_0.2.1, hsum⟩
    · refine ⟨Sym.flip11.comp g1, ?_, ?_, ?_⟩ <;>
        simp only [Sym.comp, Function.comp_apply, Sym.flip11] <;> linarith
  obtain ⟨g2, hx2, hy2, hxy2⟩ := hstep2
  set u2 := g2.mapR o
  -- Step 3: permute (1 - x - y, x, y) so 1 - x' - y' is largest
  have hstep3 : ∃ g3 : Sym,
      0 ≤ (g3.mapR o).1 ∧ 0 ≤ (g3.mapR o).2 ∧
      (g3.mapR o).1 ≤ 1 - (g3.mapR o).1 - (g3.mapR o).2 ∧
      (g3.mapR o).2 ≤ 1 - (g3.mapR o).1 - (g3.mapR o).2 := by
    by_cases ha : u2.1 ≤ 1 - u2.1 - u2.2 ∧ u2.2 ≤ 1 - u2.1 - u2.2
    · exact ⟨g2, hx2, hy2, ha.1, ha.2⟩
    · by_cases hc : u2.1 ≤ u2.2 ∧ 1 - u2.1 - u2.2 ≤ u2.2
      · refine ⟨Sym.cyc.comp g2, ?_, ?_, ?_, ?_⟩ <;>
          simp only [Sym.comp, Function.comp_apply, Sym.cyc] <;> linarith
      · have hmax : u2.2 ≤ u2.1 ∧ 1 - u2.1 - u2.2 ≤ u2.1 := by
          constructor
          · by_contra hlt
            push Not at hlt
            by_cases h1 : 1 - u2.1 - u2.2 ≤ u2.2
            · exact hc ⟨hlt.le, h1⟩
            · exact ha ⟨by linarith, by linarith⟩
          · by_contra hlt
            push Not at hlt
            by_cases h2 : u2.2 ≤ 1 - u2.1 - u2.2
            · exact ha ⟨hlt.le, h2⟩
            · exact hc ⟨by linarith, by linarith⟩
        refine ⟨(Sym.cyc.comp Sym.cyc).comp g2, ?_, ?_, ?_, ?_⟩ <;>
          simp only [Sym.comp, Function.comp_apply, Sym.cyc] <;> linarith
  obtain ⟨g3, hx3, hy3, h1, h2⟩ := hstep3
  set u3 := g3.mapR o
  -- Step 4: swap if x < y
  by_cases hxy : u3.2 ≤ u3.1
  · exact ⟨g3, hy3, hxy, by linarith⟩
  · refine ⟨Sym.swap.comp g3, ?_, ?_, ?_⟩ <;>
      simp only [Sym.comp, Function.comp_apply, Sym.swap] <;> linarith

private lemma QR_le_one_third_of_inT0 {o : Center} (ho : inT0 o) : QR o ≤ 1 / 3 := by
  rcases ho with ⟨h0, hyx, h2xy⟩
  unfold QR
  nlinarith [sq_nonneg (o.1 - o.2), sq_nonneg (1 - 2 * o.1 - o.2)]

private def U31 : List Site :=
  [(-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3),
   (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3),
   (0, -2), (0, -1), (0, 0), (0, 1), (0, 2),
   (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2),
   (2, -3), (2, -2), (2, -1), (2, 0), (2, 1),
   (3, -2), (3, -1)]

private lemma mem_U31_of_QZ_le_7 (p : Site) (hp : QZ p ≤ 7) : p ∈ U31 := by
  rcases p with ⟨x, y⟩
  have h4y : (2 * x + y) ^ 2 + 3 * y ^ 2 ≤ 28 := by
    unfold QZ at hp; nlinarith
  have h4x : (2 * y + x) ^ 2 + 3 * x ^ 2 ≤ 28 := by
    unfold QZ at hp; nlinarith
  have hy3 : -3 ≤ y ∧ y ≤ 3 := by
    constructor <;> (by_contra h; nlinarith [sq_nonneg (2 * x + y)])
  have hx3 : -3 ≤ x ∧ x ≤ 3 := by
    constructor <;> (by_contra h; nlinarith [sq_nonneg (2 * y + x)])
  have hmem : ∀ a ∈ ([-3, -2, -1, 0, 1, 2, 3] : List ℤ),
      ∀ b ∈ ([-3, -2, -1, 0, 1, 2, 3] : List ℤ),
      QZ (a, b) ≤ 7 → (a, b) ∈ U31 := by decide
  have hxL : x ∈ ([-3, -2, -1, 0, 1, 2, 3] : List ℤ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  have hyL : y ∈ ([-3, -2, -1, 0, 1, 2, 3] : List ℤ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  exact hmem x hxL y hyL hp

private lemma mem_U31_of_inT0 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s ≤ 13 / 4)
    (p : Site) (hp : QR (subC (siteR p) o) ≤ s) : p ∈ U31 := by
  have hQo : QR o ≤ 1 / 3 := QR_le_one_third_of_inT0 ho
  have hadd := QR_add_le (subC (siteR p) o) o
  have hsub : ((subC (siteR p) o).1 + o.1, (subC (siteR p) o).2 + o.2) = siteR p := by
    ext <;> simp [subC, siteR]
  rw [hsub] at hadd
  have hQpR : (QZ p : ℝ) = QR (siteR p) := by
    simp only [QZ, QR, siteR]; push_cast; ring
  have hlt : (QZ p : ℝ) < 8 := by linarith
  have hle : QZ p ≤ 7 := by
    have hlti : QZ p < 8 := by exact_mod_cast hlt
    omega
  exact mem_U31_of_QZ_le_7 p hle

-- ============================================================================
-- Step 3: Generic triangle exclusion, midpoint subdivision, and capacity drop
-- ============================================================================

private def inTriZ (D : ℤ) (u₀ u₁ u₂ : Site) (o : Center) : Prop :=
  ∃ l₀ l₁ l₂ : ℝ, 0 ≤ l₀ ∧ 0 ≤ l₁ ∧ 0 ≤ l₂ ∧ l₀ + l₁ + l₂ = 1 ∧
    (D : ℝ) * o.1 = l₀ * (u₀.1 : ℝ) + l₁ * (u₁.1 : ℝ) + l₂ * (u₂.1 : ℝ) ∧
    (D : ℝ) * o.2 = l₀ * (u₀.2 : ℝ) + l₁ * (u₁.2 : ℝ) + l₂ * (u₂.2 : ℝ)

private lemma inTriZ_T0 {o : Center} (ho : inT0 o) : inTriZ 6 (0, 0) (3, 0) (2, 2) o := by
  rcases ho with ⟨h0, hyx, h2xy⟩
  refine ⟨1 - 2 * o.1 - o.2, 2 * (o.1 - o.2), 3 * o.2,
    by linarith, by linarith, by linarith, by ring, ?_, ?_⟩ <;> norm_num <;> ring

private lemma subdiv4_Z {D : ℤ} {u₀ u₁ u₂ : Site} {o : Center}
    (h : inTriZ D u₀ u₁ u₂ o) :
    inTriZ (2 * D) (2 * u₀.1, 2 * u₀.2) (u₀.1 + u₁.1, u₀.2 + u₁.2) (u₂.1 + u₀.1, u₂.2 + u₀.2) o ∨
    inTriZ (2 * D) (u₀.1 + u₁.1, u₀.2 + u₁.2) (2 * u₁.1, 2 * u₁.2) (u₁.1 + u₂.1, u₁.2 + u₂.2) o ∨
    inTriZ (2 * D) (u₂.1 + u₀.1, u₂.2 + u₀.2) (u₁.1 + u₂.1, u₁.2 + u₂.2) (2 * u₂.1, 2 * u₂.2) o ∨
    inTriZ (2 * D) (u₀.1 + u₁.1, u₀.2 + u₁.2) (u₁.1 + u₂.1, u₁.2 + u₂.2) (u₂.1 + u₀.1, u₂.2 + u₀.2) o := by
  rcases h with ⟨l₀, l₁, l₂, hl0, hl1, hl2, hsum, hx, hy⟩
  by_cases h0 : 1 / 2 ≤ l₀
  · left
    refine ⟨2 * l₀ - 1, 2 * l₁, 2 * l₂, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
    · push_cast; rw [mul_assoc, hx]; linear_combination -(2 * (u₀.1 : ℝ)) * hsum
    · push_cast; rw [mul_assoc, hy]; linear_combination -(2 * (u₀.2 : ℝ)) * hsum
  · by_cases h1 : 1 / 2 ≤ l₁
    · right; left
      refine ⟨2 * l₀, 2 * l₁ - 1, 2 * l₂, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
      · push_cast; rw [mul_assoc, hx]; linear_combination -(2 * (u₁.1 : ℝ)) * hsum
      · push_cast; rw [mul_assoc, hy]; linear_combination -(2 * (u₁.2 : ℝ)) * hsum
    · by_cases h2 : 1 / 2 ≤ l₂
      · right; right; left
        refine ⟨2 * l₀, 2 * l₁, 2 * l₂ - 1, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
        · push_cast; rw [mul_assoc, hx]; linear_combination -(2 * (u₂.1 : ℝ)) * hsum
        · push_cast; rw [mul_assoc, hy]; linear_combination -(2 * (u₂.2 : ℝ)) * hsum
      · right; right; right
        refine ⟨1 - 2 * l₂, 1 - 2 * l₀, 1 - 2 * l₁,
          by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
        · push_cast; rw [mul_assoc, hx]
          linear_combination 2 * ((u₀.1 : ℝ) + (u₁.1 : ℝ) + (u₂.1 : ℝ)) * hsum
        · push_cast; rw [mul_assoc, hy]
          linear_combination 2 * ((u₀.2 : ℝ) + (u₁.2 : ℝ) + (u₂.2 : ℝ)) * hsum

private def certOutsideZ (p : Site) (D : ℤ) (u₀ u₁ u₂ : Site) (num den : ℤ) (strict : Bool) : Bool :=
  let a : Site := (3 * D * p.1 - (u₀.1 + u₁.1 + u₂.1), 3 * D * p.2 - (u₀.2 + u₁.2 + u₂.2))
  let qa := QZ a
  let rhs := 4 * num * D * D * qa
  let chk (u : Site) : Bool :=
    let b := B2Z (D * p.1 - u.1, D * p.2 - u.2) a
    decide (0 < b) && (if strict then decide (rhs ≤ den * b * b) else decide (rhs < den * b * b))
  decide (0 < qa) && chk u₀ && chk u₁ && chk u₂

private lemma certOutsideZ_sound (p : Site) (D : ℤ) (u₀ u₁ u₂ : Site) (num den : ℤ)
    (strict : Bool) (hD : 0 < D) (hden : 0 < den)
    (o : Center) (s : ℝ) (ho : inTriZ D u₀ u₁ u₂ o)
    (hs : if strict then s < (num : ℝ) / (den : ℝ) else s ≤ (num : ℝ) / (den : ℝ))
    (hcert : certOutsideZ p D u₀ u₁ u₂ num den strict = true) :
    ¬ (QR (subC (siteR p) o) ≤ s) := by
  intro hle
  rcases ho with ⟨l₀, l₁, l₂, hl0, hl1, hl2, hsum, hx, hy⟩
  set a : Site := (3 * D * p.1 - (u₀.1 + u₁.1 + u₂.1), 3 * D * p.2 - (u₀.2 + u₁.2 + u₂.2))
  set qa := QZ a
  set rhs := 4 * num * D * D * qa
  set b₀ := B2Z (D * p.1 - u₀.1, D * p.2 - u₀.2) a
  set b₁ := B2Z (D * p.1 - u₁.1, D * p.2 - u₁.2) a
  set b₂ := B2Z (D * p.1 - u₂.1, D * p.2 - u₂.2) a
  have hcert' : (0 < qa) ∧
      ((0 < b₀) ∧ (if strict then rhs ≤ den * b₀ * b₀ else rhs < den * b₀ * b₀)) ∧
      ((0 < b₁) ∧ (if strict then rhs ≤ den * b₁ * b₁ else rhs < den * b₁ * b₁)) ∧
      ((0 < b₂) ∧ (if strict then rhs ≤ den * b₂ * b₂ else rhs < den * b₂ * b₂)) := by
    simp only [certOutsideZ, Bool.and_eq_true] at hcert
    rcases hcert with ⟨⟨⟨hqa, hb0, hc0⟩, hb1, hc1⟩, hb2, hc2⟩
    refine ⟨of_decide_eq_true hqa,
      ⟨of_decide_eq_true hb0, ?_⟩,
      ⟨of_decide_eq_true hb1, ?_⟩,
      ⟨of_decide_eq_true hb2, ?_⟩⟩
    · cases strict
      · exact of_decide_eq_true (by simpa using hc0)
      · exact of_decide_eq_true (by simpa using hc0)
    · cases strict
      · exact of_decide_eq_true (by simpa using hc1)
      · exact of_decide_eq_true (by simpa using hc1)
    · cases strict
      · exact of_decide_eq_true (by simpa using hc2)
      · exact of_decide_eq_true (by simpa using hc2)
  have hqaR : (0 : ℝ) < (qa : ℝ) := by exact_mod_cast hcert'.1
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hlin : (D : ℝ) * B2R (subC (siteR p) o) (siteR a) =
      l₀ * (b₀ : ℝ) + l₁ * (b₁ : ℝ) + l₂ * (b₂ : ℝ) := by
    have hdx : (D : ℝ) * ((p.1 : ℝ) - o.1) =
        l₀ * ((D : ℝ) * (p.1 : ℝ) - (u₀.1 : ℝ)) +
        l₁ * ((D : ℝ) * (p.1 : ℝ) - (u₁.1 : ℝ)) +
        l₂ * ((D : ℝ) * (p.1 : ℝ) - (u₂.1 : ℝ)) := by
      calc (D : ℝ) * ((p.1 : ℝ) - o.1)
          = (l₀ + l₁ + l₂) * ((D : ℝ) * (p.1 : ℝ)) - (D : ℝ) * o.1 := by rw [hsum]; ring
        _ = l₀ * ((D : ℝ) * (p.1 : ℝ) - (u₀.1 : ℝ)) +
            l₁ * ((D : ℝ) * (p.1 : ℝ) - (u₁.1 : ℝ)) +
            l₂ * ((D : ℝ) * (p.1 : ℝ) - (u₂.1 : ℝ)) := by rw [hx]; ring
    have hdy : (D : ℝ) * ((p.2 : ℝ) - o.2) =
        l₀ * ((D : ℝ) * (p.2 : ℝ) - (u₀.2 : ℝ)) +
        l₁ * ((D : ℝ) * (p.2 : ℝ) - (u₁.2 : ℝ)) +
        l₂ * ((D : ℝ) * (p.2 : ℝ) - (u₂.2 : ℝ)) := by
      calc (D : ℝ) * ((p.2 : ℝ) - o.2)
          = (l₀ + l₁ + l₂) * ((D : ℝ) * (p.2 : ℝ)) - (D : ℝ) * o.2 := by rw [hsum]; ring
        _ = l₀ * ((D : ℝ) * (p.2 : ℝ) - (u₀.2 : ℝ)) +
            l₁ * ((D : ℝ) * (p.2 : ℝ) - (u₁.2 : ℝ)) +
            l₂ * ((D : ℝ) * (p.2 : ℝ) - (u₂.2 : ℝ)) := by rw [hy]; ring
    calc (D : ℝ) * B2R (subC (siteR p) o) (siteR a)
        = (2 * (a.1 : ℝ) + (a.2 : ℝ)) * ((D : ℝ) * ((p.1 : ℝ) - o.1)) +
          ((a.1 : ℝ) + 2 * (a.2 : ℝ)) * ((D : ℝ) * ((p.2 : ℝ) - o.2)) := by
            simp only [B2R, subC, siteR]; ring
      _ = l₀ * (b₀ : ℝ) + l₁ * (b₁ : ℝ) + l₂ * (b₂ : ℝ) := by
            rw [hdx, hdy]; simp only [b₀, b₁, b₂, B2Z]; push_cast; ring
  have hcs : ((D : ℝ) * B2R (subC (siteR p) o) (siteR a)) ^ 2 ≤
      4 * s * (D : ℝ) ^ 2 * (qa : ℝ) := by
    have h1 := cauchy_schwarz_R (subC (siteR p) o) (siteR a)
    have h2 : QR (siteR a) = (qa : ℝ) := by simp only [qa, QR, QZ, siteR]; push_cast; ring
    rw [h2] at h1
    have h3 : 4 * QR (subC (siteR p) o) * (qa : ℝ) ≤ 4 * s * (qa : ℝ) := by
      have := mul_le_mul_of_nonneg_right hle hqaR.le
      linarith
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h3) (sq_nonneg (D : ℝ))
    linarith [show ((D : ℝ) * B2R (subC (siteR p) o) (siteR a)) ^ 2 =
      (D : ℝ) ^ 2 * (B2R (subC (siteR p) o) (siteR a)) ^ 2 by ring,
      show (D : ℝ) ^ 2 * (4 * s * (qa : ℝ)) = 4 * s * (D : ℝ) ^ 2 * (qa : ℝ) by ring]
  set B : ℝ := (D : ℝ) * B2R (subC (siteR p) o) (siteR a)
  set M : ℝ := min (b₀ : ℝ) (min (b₁ : ℝ) (b₂ : ℝ))
  have hB_ge : M ≤ B := by
    have hm0 : M ≤ (b₀ : ℝ) := min_le_left _ _
    have hm1 : M ≤ (b₁ : ℝ) := le_trans (min_le_right _ _) (min_le_left _ _)
    have hm2 : M ≤ (b₂ : ℝ) := le_trans (min_le_right _ _) (min_le_right _ _)
    have h0 := mul_le_mul_of_nonneg_left hm0 hl0
    have h1 := mul_le_mul_of_nonneg_left hm1 hl1
    have h2 := mul_le_mul_of_nonneg_left hm2 hl2
    have hMsum : l₀ * M + l₁ * M + l₂ * M = M := by
      calc l₀ * M + l₁ * M + l₂ * M = (l₀ + l₁ + l₂) * M := by ring
        _ = M := by rw [hsum, one_mul]
    linarith
  have hm_pos : 0 < M := by
    have hb0 : (0 : ℝ) < (b₀ : ℝ) := by exact_mod_cast hcert'.2.1.1
    have hb1 : (0 : ℝ) < (b₁ : ℝ) := by exact_mod_cast hcert'.2.2.1.1
    have hb2 : (0 : ℝ) < (b₂ : ℝ) := by exact_mod_cast hcert'.2.2.2.1
    exact lt_min hb0 (lt_min hb1 hb2)
  have hBsq_ge : M ^ 2 ≤ B ^ 2 := by
    have hposB : 0 ≤ M + B := by linarith
    have hsubB : 0 ≤ B - M := by linarith
    have hmul : 0 ≤ (B - M) * (M + B) := mul_nonneg hsubB hposB
    linarith [show (B - M) * (M + B) = B ^ 2 - M ^ 2 by ring]
  have hmin_cases : M = (b₀ : ℝ) ∨ M = (b₁ : ℝ) ∨ M = (b₂ : ℝ) := by
    rcases min_choice (b₀ : ℝ) (min (b₁ : ℝ) (b₂ : ℝ)) with h | h
    · exact Or.inl h
    · rcases min_choice (b₁ : ℝ) (b₂ : ℝ) with h' | h'
      · exact Or.inr (Or.inl (h.trans h'))
      · exact Or.inr (Or.inr (h.trans h'))
  have hrhsR : (rhs : ℝ) = 4 * (num : ℝ) * (D : ℝ) ^ 2 * (qa : ℝ) := by
    simp only [rhs]; push_cast; ring
  have hD2qa : 0 < 4 * (D : ℝ) ^ 2 * (qa : ℝ) := by positivity
  have hdenB : (den : ℝ) * M ^ 2 ≤ (den : ℝ) * B ^ 2 :=
    mul_le_mul_of_nonneg_left hBsq_ge hdenR.le
  have hdenCS : (den : ℝ) * B ^ 2 ≤ (den : ℝ) * (4 * s * (D : ℝ) ^ 2 * (qa : ℝ)) :=
    mul_le_mul_of_nonneg_left hcs hdenR.le
  cases strict with
  | true =>
    simp only [↓reduceIte] at hs hcert'
    have hden_s : (den : ℝ) * s < (num : ℝ) := by
      have := (lt_div_iff₀ hdenR).mp hs; linarith
    have hlt_rhs : (den : ℝ) * (4 * s * (D : ℝ) ^ 2 * (qa : ℝ)) < (rhs : ℝ) := by
      have h1 := mul_lt_mul_of_pos_right hden_s hD2qa
      linarith [show (den : ℝ) * s * (4 * (D : ℝ) ^ 2 * (qa : ℝ)) =
        (den : ℝ) * (4 * s * (D : ℝ) ^ 2 * (qa : ℝ)) by ring,
        show (num : ℝ) * (4 * (D : ℝ) ^ 2 * (qa : ℝ)) = (rhs : ℝ) by rw [hrhsR]; ring]
    have hM_rhs : (rhs : ℝ) ≤ (den : ℝ) * M ^ 2 := by
      rcases hmin_cases with hm | hm | hm
      · have h0 : (rhs : ℝ) ≤ (den : ℝ) * (b₀ : ℝ) * (b₀ : ℝ) := by exact_mod_cast hcert'.2.1.2
        rw [hm]; linarith [show (den : ℝ) * (b₀ : ℝ) * (b₀ : ℝ) = (den : ℝ) * (b₀ : ℝ) ^ 2 by ring]
      · have h1 : (rhs : ℝ) ≤ (den : ℝ) * (b₁ : ℝ) * (b₁ : ℝ) := by exact_mod_cast hcert'.2.2.1.2
        rw [hm]; linarith [show (den : ℝ) * (b₁ : ℝ) * (b₁ : ℝ) = (den : ℝ) * (b₁ : ℝ) ^ 2 by ring]
      · have h2 : (rhs : ℝ) ≤ (den : ℝ) * (b₂ : ℝ) * (b₂ : ℝ) := by exact_mod_cast hcert'.2.2.2.2
        rw [hm]; linarith [show (den : ℝ) * (b₂ : ℝ) * (b₂ : ℝ) = (den : ℝ) * (b₂ : ℝ) ^ 2 by ring]
    linarith
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hs hcert'
    have hden_s : (den : ℝ) * s ≤ (num : ℝ) := by
      have := (le_div_iff₀ hdenR).mp hs; linarith
    have hle_rhs : (den : ℝ) * (4 * s * (D : ℝ) ^ 2 * (qa : ℝ)) ≤ (rhs : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hden_s hD2qa.le
      linarith [show (den : ℝ) * s * (4 * (D : ℝ) ^ 2 * (qa : ℝ)) =
        (den : ℝ) * (4 * s * (D : ℝ) ^ 2 * (qa : ℝ)) by ring,
        show (num : ℝ) * (4 * (D : ℝ) ^ 2 * (qa : ℝ)) = (rhs : ℝ) by rw [hrhsR]; ring]
    have hM_rhs : (rhs : ℝ) < (den : ℝ) * M ^ 2 := by
      rcases hmin_cases with hm | hm | hm
      · have h0 : (rhs : ℝ) < (den : ℝ) * (b₀ : ℝ) * (b₀ : ℝ) := by exact_mod_cast hcert'.2.1.2
        rw [hm]; linarith [show (den : ℝ) * (b₀ : ℝ) * (b₀ : ℝ) = (den : ℝ) * (b₀ : ℝ) ^ 2 by ring]
      · have h1 : (rhs : ℝ) < (den : ℝ) * (b₁ : ℝ) * (b₁ : ℝ) := by exact_mod_cast hcert'.2.2.1.2
        rw [hm]; linarith [show (den : ℝ) * (b₁ : ℝ) * (b₁ : ℝ) = (den : ℝ) * (b₁ : ℝ) ^ 2 by ring]
      · have h2 : (rhs : ℝ) < (den : ℝ) * (b₂ : ℝ) * (b₂ : ℝ) := by exact_mod_cast hcert'.2.2.2.2
        rw [hm]; linarith [show (den : ℝ) * (b₂ : ℝ) * (b₂ : ℝ) = (den : ℝ) * (b₂ : ℝ) ^ 2 by ring]
    linarith

private def checkRem (rem : List Site) (D : ℤ) (u₀ u₁ u₂ : Site) (num den : ℤ) (strict : Bool) : Bool :=
  U31.all fun p => rem.contains p || certOutsideZ p D u₀ u₁ u₂ num den strict

private lemma subset_rem_of_checkRem (rem : List Site) (D : ℤ) (u₀ u₁ u₂ : Site) (num den : ℤ)
    (strict : Bool) (hD : 0 < D) (hden : 0 < den)
    (o : Center) (s : ℝ) (hoT : inT0 o) (hs13 : s ≤ 13 / 4) (ho : inTriZ D u₀ u₁ u₂ o)
    (hs : if strict then s < (num : ℝ) / (den : ℝ) else s ≤ (num : ℝ) / (den : ℝ))
    (hchk : checkRem rem D u₀ u₁ u₂ num den strict = true)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) :
    S ⊆ rem.toFinset := by
  intro p hpS
  have hpU : p ∈ U31 := mem_U31_of_inT0 hoT hs13 p (hS p hpS)
  have hall := List.all_eq_true.mp hchk p hpU
  rcases Bool.or_eq_true _ _ |>.mp hall with hmem | hcert
  · exact List.mem_toFinset.mpr (List.contains_iff_mem.mp hmem)
  · exact absurd (hS p hpS) (certOutsideZ_sound p D u₀ u₁ u₂ num den strict hD hden o s ho hs hcert)

private lemma card_le_of_blocks (rem : List Site) (Bs : List (List Site)) (S : Finset Site)
    (hsub : S ⊆ rem.toFinset)
    (hnodup : Bs.flatten.Nodup)
    (hin : ∀ x ∈ Bs.flatten, x ∈ rem)
    (hmiss : ∀ B ∈ Bs, ∃ x ∈ B, x ∉ S) :
    S.card + Bs.length ≤ rem.length := by
  have hchoose : ∀ i : Fin Bs.length, ∃ x : Site, x ∈ Bs[i] ∧ x ∉ S :=
    fun i => hmiss Bs[i] (List.getElem_mem i.2)
  choose f hf_mem hf_notS using hchoose
  have hfinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hdisj : ∀ a ∈ Bs[i], ∀ b ∈ Bs[j], a ≠ b := by
      have hp := List.nodup_flatten.mp hnodup
      have hpw : Bs.Pairwise List.Disjoint := hp.2
      have hne' : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · have hd := List.pairwise_iff_getElem.mp hpw i.1 j.1 i.2 j.2 hlt
        exact fun a ha b hb hab => hd ha (hab ▸ hb)
      · have hd := List.pairwise_iff_getElem.mp hpw j.1 i.1 j.2 i.2 hgt
        exact fun a ha b hb hab => hd hb (hab ▸ ha)
    exact hdisj (f i) (hf_mem i) (f j) (hf_mem j) hij
  have himg_sub : (Finset.univ.image f) ⊆ rem.toFinset \ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    rw [Finset.mem_sdiff, List.mem_toFinset]
    refine ⟨hin (f i) (List.mem_flatten.mpr ⟨Bs[i], List.getElem_mem i.2, hf_mem i⟩), hf_notS i⟩
  have hcard1 : Bs.length ≤ (rem.toFinset \ S).card := by
    have h1 := Finset.card_le_card himg_sub
    rwa [Finset.card_image_of_injective _ hfinj, Finset.card_fin] at h1
  have hcard2 : (rem.toFinset \ S).card + S.card = rem.toFinset.card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hcard3 : rem.toFinset.card ≤ rem.length := List.toFinset_card_le rem
  omega

private lemma card_le_of_pair_cert (rem : List Site) (pairs : List (Site × Site))
    (D : ℤ) (u₀ u₁ u₂ : Site) (num den : ℤ) (hD : 0 < D) (hden : 0 < den)
    (o : Center) (s : ℝ) (hoT : inT0 o) (hs13 : s ≤ 13 / 4) (ho : inTriZ D u₀ u₁ u₂ o)
    (hs : s < (num : ℝ) / (den : ℝ))
    (hchk : checkRem rem D u₀ u₁ u₂ num den true = true)
    (hnodup : (pairs.map (fun pr => [pr.1, pr.2])).flatten.Nodup)
    (hin : ∀ x ∈ (pairs.map (fun pr => [pr.1, pr.2])).flatten, x ∈ rem)
    (hpairs : ∀ pr ∈ pairs, 4 * num ≤ den * QZ (pr.1.1 - pr.2.1, pr.1.2 - pr.2.2))
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) :
    S.card + pairs.length ≤ rem.length := by
  have hsub := subset_rem_of_checkRem rem D u₀ u₁ u₂ num den true hD hden o s hoT hs13 ho
    (by simpa using hs) hchk S hS
  have hmiss : ∀ B ∈ pairs.map (fun pr => [pr.1, pr.2]), ∃ x ∈ B, x ∉ S := by
    intro B hB
    rcases List.mem_map.mp hB with ⟨⟨p₁, p₂⟩, hmem, rfl⟩
    by_contra hall
    push Not at hall
    have h1 : p₁ ∈ S := hall p₁ (by simp)
    have h2 : p₂ ∈ S := hall p₂ (by simp)
    exact pair_not_both_strict p₁ p₂ o s num den hden hs (hpairs (p₁, p₂) hmem) ⟨hS p₁ h1, hS p₂ h2⟩
  have hle := card_le_of_blocks rem (pairs.map (fun pr => [pr.1, pr.2])) S hsub hnodup hin hmiss
  simpa using hle

-- ============================================================================
-- Step 4: The 11 Exact Threshold Upper Bounds T1..T11 (20 triangles total)
-- ============================================================================

private def D13_list : List Site :=
  [(-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1),
   (1, -2), (1, -1), (1, 0), (1, 1), (2, -1)]

private lemma bound_T1 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s < 1 / 4)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) : S.card ≤ 1 := by
  have h := card_le_of_pair_cert [(0, 0), (1, 0)] [((0, 0), (1, 0))]
    6 (0, 0) (3, 0) (2, 2) 1 4 (by omega) (by omega) o s ho (by linarith) (inTriZ_T0 ho)
    (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
  simp only [List.length_cons, List.length_nil] at h; omega

private lemma bound_T2 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s < 1 / 3)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) : S.card ≤ 2 := by
  set rem : List Site := [(0, 0), (0, 1), (1, 0)]
  have hsub := subset_rem_of_checkRem rem 6 (0, 0) (3, 0) (2, 2) 1 3 true
    (by omega) (by omega) o s ho (by linarith) (inTriZ_T0 ho) (by simpa using hs) (by decide) S hS
  have hmiss : ∀ B ∈ ([[(0, 0), (0, 1), (1, 0)]] : List (List Site)), ∃ x ∈ B, x ∉ S := by
    intro B hB
    simp only [List.mem_singleton] at hB; subst hB
    by_contra hall; push Not at hall
    exact triple_excl_1 o s hs
      ⟨hS _ (hall (0, 0) (by simp)), hS _ (hall (0, 1) (by simp)), hS _ (hall (1, 0) (by simp))⟩
  have h := card_le_of_blocks rem [[(0, 0), (0, 1), (1, 0)]] S hsub (by decide) (by decide) hmiss
  simp only [rem, List.length_cons, List.length_nil] at h; omega

private lemma bound_T3 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s < 3 / 4)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) : S.card ≤ 3 := by
  have h := card_le_of_pair_cert [(0, 0), (0, 1), (1, -1), (1, 0)] [((0, 1), (1, -1))]
    6 (0, 0) (3, 0) (2, 2) 3 4 (by omega) (by omega) o s ho (by linarith) (inTriZ_T0 ho)
    (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
  simp only [List.length_cons, List.length_nil] at h; omega

private lemma bound_T4 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s < 1)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) : S.card ≤ 4 := by
  have h := card_le_of_pair_cert
    [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0)]
    [((-1, 0), (1, 0)), ((-1, 1), (1, -1)), ((0, -1), (0, 1))]
    6 (0, 0) (3, 0) (2, 2) 1 1 (by omega) (by omega) o s ho (by linarith) (inTriZ_T0 ho)
    (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
  simp only [List.length_cons, List.length_nil] at h; omega

private lemma bound_T5 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s < 7 / 4)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) : S.card ≤ 7 := by
  have h := card_le_of_pair_cert
    [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1)]
    [((-1, 0), (1, 1)), ((-1, 1), (2, -1))]
    6 (0, 0) (3, 0) (2, 2) 7 4 (by omega) (by omega) o s ho (by linarith) (inTriZ_T0 ho)
    (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
  simp only [List.length_cons, List.length_nil] at h; omega

private lemma bound_T6 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s < 49 / 25)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) : S.card ≤ 8 := by
  set rem : List Site := [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1)]
  have hsub := subset_rem_of_checkRem rem 6 (0, 0) (3, 0) (2, 2) 49 25 true
    (by omega) (by omega) o s ho (by linarith) (inTriZ_T0 ho) (by simpa using hs) (by decide) S hS
  have hmiss : ∀ B ∈ ([[(-1, 0), (1, 1), (2, -1)]] : List (List Site)), ∃ x ∈ B, x ∉ S := by
    intro B hB
    simp only [List.mem_singleton] at hB; subst hB
    by_contra hall; push Not at hall
    exact triple_excl_2 o s hs
      ⟨hS _ (hall (-1, 0) (by simp)), hS _ (hall (1, 1) (by simp)), hS _ (hall (2, -1) (by simp))⟩
  have h := card_le_of_blocks rem [[(-1, 0), (1, 1), (2, -1)]] S hsub (by decide) (by decide) hmiss
  simp only [rem, List.length_cons, List.length_nil] at h; omega

private lemma bound_T7 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s < 9 / 4)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) : S.card ≤ 9 := by
  have h := card_le_of_pair_cert
    [(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
    [((-1, 0), (2, 0))]
    6 (0, 0) (3, 0) (2, 2) 9 4 (by omega) (by omega) o s ho (by linarith) (inTriZ_T0 ho)
    (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
  simp only [List.length_cons, List.length_nil] at h; omega

private lemma bound_T8 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s < 7 / 3)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) : S.card ≤ 10 := by
  set rem : List Site :=
    [(-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
  have hsub := subset_rem_of_checkRem rem 6 (0, 0) (3, 0) (2, 2) 7 3 true
    (by omega) (by omega) o s ho (by linarith) (inTriZ_T0 ho) (by simpa using hs) (by decide) S hS
  set Bs : List (List Site) := [[(-1, 0), (-1, 2), (2, -1)], [(0, -1), (0, 2), (2, 0)]]
  have hmiss : ∀ B ∈ Bs, ∃ x ∈ B, x ∉ S := by
    intro B hB
    simp only [Bs, List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    · by_contra hall; push Not at hall
      exact triple_excl_3 o s hs
        ⟨hS _ (hall (-1, 0) (by simp)), hS _ (hall (-1, 2) (by simp)), hS _ (hall (2, -1) (by simp))⟩
    · by_contra hall; push Not at hall
      exact triple_excl_4 o s hs
        ⟨hS _ (hall (0, -1) (by simp)), hS _ (hall (0, 2) (by simp)), hS _ (hall (2, 0) (by simp))⟩
  have h := card_le_of_blocks rem Bs S hsub (by decide) (by decide) hmiss
  simp only [rem, Bs, List.length_cons, List.length_nil] at h; omega

private lemma bound_T9 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s < 3)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) : S.card ≤ 12 := by
  have h := card_le_of_pair_cert
    [(-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2),
     (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
    [((-2, 1), (2, -1)), ((-1, -1), (0, 2)), ((-1, 2), (1, -2))]
    6 (0, 0) (3, 0) (2, 2) 3 1 (by omega) (by omega) o s ho (by linarith) (inTriZ_T0 ho)
    (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
  simp only [List.length_cons, List.length_nil] at h; omega

private lemma bound_T10 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s < 13 / 4)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) :
    S.card ≤ 12 ∨ S ⊆ D13_list.toFinset := by
  have hsub1 := subdiv4_Z (inTriZ_T0 ho)
  simp only [show (2 : ℤ) * 6 = 12 by norm_num, show (2 : ℤ) * 0 = 0 by norm_num,
    show (2 : ℤ) * 3 = 6 by norm_num, show (2 : ℤ) * 2 = 4 by norm_num,
    show (0 : ℤ) + 3 = 3 by norm_num, show (0 : ℤ) + 0 = 0 by norm_num,
    show (2 : ℤ) + 0 = 2 by norm_num, show (3 : ℤ) + 2 = 5 by norm_num,
    show (0 : ℤ) + 2 = 2 by norm_num] at hsub1
  rcases hsub1 with hD0 | hD1 | hD2 | hD3
  · have hsub2 := subdiv4_Z hD0
    simp only [show (2 : ℤ) * 12 = 24 by norm_num, show (2 : ℤ) * 0 = 0 by norm_num,
      show (2 : ℤ) * 3 = 6 by norm_num, show (2 : ℤ) * 2 = 4 by norm_num,
      show (0 : ℤ) + 3 = 3 by norm_num, show (0 : ℤ) + 0 = 0 by norm_num,
      show (2 : ℤ) + 0 = 2 by norm_num, show (3 : ℤ) + 2 = 5 by norm_num,
      show (0 : ℤ) + 2 = 2 by norm_num] at hsub2
    rcases hsub2 with h00 | h01 | h02 | h03
    · right
      exact subset_rem_of_checkRem D13_list 24 (0, 0) (3, 0) (2, 2) 13 4 true
        (by omega) (by omega) o s ho (by linarith) h00 (by simpa using hs) (by decide) S hS
    · left
      have h := card_le_of_pair_cert
        [(-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
        [] 24 (3, 0) (6, 0) (5, 2) 13 4 (by omega) (by omega) o s ho (by linarith) h01
        (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
      simpa using h
    · left
      have h := card_le_of_pair_cert
        [(-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
        [] 24 (2, 2) (5, 2) (4, 4) 13 4 (by omega) (by omega) o s ho (by linarith) h02
        (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
      simpa using h
    · left
      have h := card_le_of_pair_cert
        [(-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
        [] 24 (3, 0) (5, 2) (2, 2) 13 4 (by omega) (by omega) o s ho (by linarith) h03
        (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
      simpa using h
  · left
    have h := card_le_of_pair_cert
      [(-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2),
       (1, -2), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0)]
      [((-1, 2), (2, -2)), ((0, 2), (1, -2))]
      12 (3, 0) (6, 0) (5, 2) 13 4 (by omega) (by omega) o s ho (by linarith) hD1
      (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
    simpa using h
  · left
    have h := card_le_of_pair_cert
      [(-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
      [] 12 (2, 2) (5, 2) (4, 4) 13 4 (by omega) (by omega) o s ho (by linarith) hD2
      (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
    simpa using h
  · left
    have h := card_le_of_pair_cert
      [(-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2),
       (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
      [((0, 2), (1, -2))]
      12 (3, 0) (5, 2) (2, 2) 13 4 (by omega) (by omega) o s ho (by linarith) hD3
      (by norm_num; linarith) (by decide) (by decide) (by decide) (by decide) S hS
    simp only [List.length_cons, List.length_nil] at h; omega

private lemma bound_T11 {o : Center} {s : ℝ} (ho : inT0 o) (hs : s ≤ 13 / 4)
    (S : Finset Site) (hS : ∀ p ∈ S, QR (subC (siteR p) o) ≤ s) : S.card ≤ 14 := by
  have hsub1 := subdiv4_Z (inTriZ_T0 ho)
  simp only [show (2 : ℤ) * 6 = 12 by norm_num, show (2 : ℤ) * 0 = 0 by norm_num,
    show (2 : ℤ) * 3 = 6 by norm_num, show (2 : ℤ) * 2 = 4 by norm_num,
    show (0 : ℤ) + 3 = 3 by norm_num, show (0 : ℤ) + 0 = 0 by norm_num,
    show (2 : ℤ) + 0 = 2 by norm_num, show (3 : ℤ) + 2 = 5 by norm_num,
    show (0 : ℤ) + 2 = 2 by norm_num] at hsub1
  rcases hsub1 with hD0 | hD1 | hD2 | hD3
  · set rem : List Site :=
      [(-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2),
       (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
    have hsub := subset_rem_of_checkRem rem 12 (0, 0) (3, 0) (2, 2) 13 4 false
      (by omega) (by omega) o s ho hs hD0 (by simpa using hs) (by decide) S hS
    have hmiss : ∀ B ∈ ([[(-2, 1), (-1, -1), (2, 0)]] : List (List Site)), ∃ x ∈ B, x ∉ S := by
      intro B hB
      simp only [List.mem_singleton] at hB; subst hB
      by_contra hall; push Not at hall
      exact triple_excl_5 o s hs
        ⟨hS _ (hall (-2, 1) (by simp)), hS _ (hall (-1, -1) (by simp)), hS _ (hall (2, 0) (by simp))⟩
    have h := card_le_of_blocks rem [[(-2, 1), (-1, -1), (2, 0)]] S hsub (by decide) (by decide) hmiss
    simp only [rem, List.length_cons, List.length_nil] at h; omega
  · set rem : List Site :=
      [(-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2),
       (1, -2), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0)]
    have hsub := subset_rem_of_checkRem rem 12 (3, 0) (6, 0) (5, 2) 13 4 false
      (by omega) (by omega) o s ho hs hD1 (by simpa using hs) (by decide) S hS
    have hle := Finset.card_le_card hsub
    have hcard : rem.toFinset.card ≤ 14 := by decide
    omega
  · set rem : List Site :=
      [(-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
    have hsub := subset_rem_of_checkRem rem 12 (2, 2) (5, 2) (4, 4) 13 4 false
      (by omega) (by omega) o s ho hs hD2 (by simpa using hs) (by decide) S hS
    have hle := Finset.card_le_card hsub
    have hcard : rem.toFinset.card ≤ 14 := by decide
    omega
  · set rem : List Site :=
      [(-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2),
       (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)]
    have hsub := subset_rem_of_checkRem rem 12 (3, 0) (5, 2) (2, 2) 13 4 false
      (by omega) (by omega) o s ho hs hD3 (by simpa using hs) (by decide) S hS
    have hle := Finset.card_le_card hsub
    have hcard : rem.toFinset.card ≤ 14 := by decide
    omega

-- Lift T_0 cardinality bounds to arbitrary centers via Sym
private lemma pointsFit_card_le_of_T0 {k N : ℕ} {s : ℝ}
    (hT0 : ∀ o : Center, inT0 o → ∀ S : Finset Site, (∀ p ∈ S, QR (subC (siteR p) o) ≤ s) → S.card ≤ N)
    (hpf : pointsFit k s) : k ≤ N := by
  rcases hpf with ⟨p, o, hinj, hfit⟩
  obtain ⟨g, ho'⟩ := exists_sym_inT0 o
  set p' : Fin k → Site := fun i => g.mapZ (p i)
  have hinj' : Function.Injective p' := g.injZ.comp hinj
  set S : Finset Site := Finset.univ.image p'
  have hcardS : S.card = k := by
    rw [Finset.card_image_of_injective _ hinj', Finset.card_fin]
  have hS : ∀ q ∈ S, QR (subC (siteR q) (g.mapR o)) ≤ s := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨i, _, rfl⟩
    rw [← g.compat (p i), g.presQ]
    exact hfit i
  rw [← hcardS]
  exact hT0 (g.mapR o) ho' S hS

private lemma not_pointsFit_of_T0 {k : ℕ} {s : ℝ}
    (hT0 : ∀ o : Center, inT0 o → ∀ S : Finset Site, (∀ p ∈ S, QR (subC (siteR p) o) ≤ s) → S.card ≤ k) :
    ¬ pointsFit (k + 1) s := fun h => by
  have := pointsFit_card_le_of_T0 hT0 h; omega

private lemma pointsFit_mono {k : ℕ} {s₁ s₂ : ℝ} (hle : s₁ ≤ s₂) (h : pointsFit k s₁) :
    pointsFit k s₂ := by
  rcases h with ⟨p, o, hinj, hfit⟩
  exact ⟨p, o, hinj, fun i => (hfit i).trans hle⟩

private lemma pointsFit_anti_k {k₁ k₂ : ℕ} {s : ℝ} (hle : k₁ ≤ k₂) (h : pointsFit k₂ s) :
    pointsFit k₁ s := by
  rcases h with ⟨p, o, hinj, hfit⟩
  refine ⟨fun i => p ⟨i.1, Nat.lt_of_lt_of_le i.2 hle⟩, o, ?_, fun i => hfit _⟩
  intro i j hij
  exact Fin.ext (by simpa using congrArg Fin.val (hinj hij))

private lemma attainable_mono {m : ℕ} {s₁ s₂ : ℝ} (hle : s₁ ≤ s₂) (h : attainable m s₁) :
    attainable m s₂ := by
  rcases h with ⟨p, o, hv, hf⟩
  exact ⟨p, o, hv, fun i hi => (hf i hi).trans hle⟩

private lemma pointsFit_of_attainable {m : ℕ} {s : ℝ} (h : attainable m s) :
    pointsFit m s := by
  rcases h with ⟨p, o, hv, hf⟩
  refine ⟨fun i : Fin m => p i.1, o, ?_, fun i => hf i.1 (Nat.le_of_lt i.2)⟩
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
  · have := hv.2.1 i.1 j.1 hlt (Nat.le_of_lt j.2) hij
    omega
  · have := hv.2.1 j.1 i.1 hgt (Nat.le_of_lt i.2) hij.symm
    omega

private lemma pointsFit_three_of_attainable_two {s : ℝ} (h : attainable 2 s) :
    pointsFit 3 s := by
  rcases h with ⟨p, o, hv, hf⟩
  refine ⟨fun i : Fin 3 => p i.1, o, ?_, fun i => hf i.1 (by omega)⟩
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
  · have h02 := hv.2.1 i.1 j.1 hlt (by omega) hij
    have := hv.2.2 (by rw [← h02.1, ← h02.2]; exact hij)
    omega
  · have h02 := hv.2.1 j.1 i.1 hgt (by omega) hij.symm
    have := hv.2.2 (by rw [← h02.1, ← h02.2]; exact hij.symm)
    omega

-- ============================================================================
-- Step 5: Non-Hamiltonicity of D_13(0) via 7-vertex independent set W_7
-- ============================================================================

private def W7_list : List Site :=
  [(0, 0), (1, 1), (-1, 2), (-2, 1), (-1, -1), (1, -2), (2, -1)]

private lemma W7_indep : ∀ u ∈ W7_list, ∀ v ∈ W7_list, ¬ unitStep u v := by
  have h : ∀ u ∈ W7_list, ∀ v ∈ W7_list, QZ (u.1 - v.1, u.2 - v.2) ≠ 1 := by decide
  intro u hu v hv hstep
  exact h u hu v hv hstep

private lemma not_attainable_13_of_lt {s : ℝ} (hs : s < 13 / 4) : ¬ attainable 13 s := by
  rintro ⟨p, o, hv, hf⟩
  obtain ⟨g, ho'⟩ := exists_sym_inT0 o
  set p' : ℕ → Site := fun i => g.mapZ (p i)
  have hv' : valid 13 p' := g.pres_valid 13 p hv
  have hf' : fits 13 p' (g.mapR o) s := g.pres_fits 13 p o s hf
  have hinj13 : Function.Injective (fun i : Fin 13 => p' i.1) := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
    · have := hv'.2.1 i.1 j.1 hlt (Nat.le_of_lt j.2) hij; omega
    · have := hv'.2.1 j.1 i.1 hgt (Nat.le_of_lt i.2) hij.symm; omega
  set S : Finset Site := Finset.univ.image (fun i : Fin 13 => p' i.1)
  have hcardS : S.card = 13 := by
    rw [Finset.card_image_of_injective _ hinj13, Finset.card_fin]
  have hSfit : ∀ q ∈ S, QR (subC (siteR q) (g.mapR o)) ≤ s := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨i, _, rfl⟩
    exact hf' i.1 (Nat.le_of_lt i.2)
  have hD13_sub : S ⊆ D13_list.toFinset := by
    rcases bound_T10 ho' hs S hSfit with hle | hsub
    · omega
    · exact hsub
  have hD13_card : D13_list.toFinset.card = 13 := by decide
  have hSeq : S = D13_list.toFinset :=
    Finset.eq_of_subset_of_card_le hD13_sub (by omega)
  -- Show p' 13 = p' 0 by including p' 13 in S_plus
  have hp13_mem : p' 13 ∈ S := by
    set Splus : Finset Site := insert (p' 13) S
    have hSpfit : ∀ q ∈ Splus, QR (subC (siteR q) (g.mapR o)) ≤ s := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqS
      · exact hf' 13 le_rfl
      · exact hSfit q hqS
    rcases bound_T10 ho' hs Splus hSpfit with hle | hsub
    · have : S.card ≤ Splus.card := Finset.card_le_card (Finset.subset_insert _ _)
      omega
    · rw [hSeq]
      exact hsub (Finset.mem_insert_self _ _)
  have hp013 : p' 0 = p' 13 := by
    rcases Finset.mem_image.mp hp13_mem with ⟨i, _, hi⟩
    have h0 := hv'.2.1 i.1 13 i.2 le_rfl hi
    rw [← h0.1]
    exact hi
  -- Every cyclic step i |-> (i + 1) % 13 is a unitStep
  have hcyc : ∀ i : Fin 13, unitStep (p' i.1) (p' ((i.1 + 1) % 13)) := by
    intro i
    by_cases h12 : i.1 < 12
    · rw [Nat.mod_eq_of_lt (by omega : i.1 + 1 < 13)]
      exact hv'.1 i.1 (by omega)
    · have hi12 : i.1 = 12 := by omega
      rw [hi12]
      simp only [show (12 + 1) % 13 = 0 by decide]
      rw [hp013]
      exact hv'.1 12 (by omega)
  -- Partition Fin 13 into IW and I_notW: |IW| = 7, |I_notW| = 6
  set IW : Finset (Fin 13) := Finset.univ.filter (fun i : Fin 13 => p' i.1 ∈ W7_list)
  set InotW : Finset (Fin 13) := Finset.univ.filter (fun i : Fin 13 => p' i.1 ∉ W7_list)
  have hWsub : W7_list.toFinset ⊆ D13_list.toFinset := by decide
  have hIW_card : IW.card = 7 := by
    have himg : IW.image (fun i : Fin 13 => p' i.1) = W7_list.toFinset := by
      ext q
      simp only [Finset.mem_image, IW, Finset.mem_filter, Finset.mem_univ, true_and,
        List.mem_toFinset]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hq
        have hqS : q ∈ S := by rw [hSeq]; exact hWsub (List.mem_toFinset.mpr hq)
        rcases Finset.mem_image.mp hqS with ⟨i, _, rfl⟩
        exact ⟨i, hq, rfl⟩
    have h1 : (IW.image (fun i : Fin 13 => p' i.1)).card = IW.card :=
      Finset.card_image_of_injective IW hinj13
    rw [himg] at h1
    have hW7 : W7_list.toFinset.card = 7 := by decide
    omega
  have hInotW_card : InotW.card = 6 := by
    have hdisj : Disjoint IW InotW := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [IW, InotW, Finset.mem_filter] at hi1 hi2
      exact hi2.2 hi1.2
    have hunion : IW ∪ InotW = Finset.univ := by
      ext i
      simp only [IW, InotW, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact em _
    have hadd : IW.card + InotW.card = (Finset.univ : Finset (Fin 13)).card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    simp only [Finset.card_fin] at hadd
    omega
  -- Map i |-> ⟨(i + 1) % 13, _⟩ sends IW injectively into InotW
  set nxt : Fin 13 → Fin 13 := fun i => ⟨(i.1 + 1) % 13, Nat.mod_lt _ (by decide)⟩
  have hnxt_inj : Function.Injective nxt := by
    intro i j hij
    have hmod : (i.1 + 1) % 13 = (j.1 + 1) % 13 := congrArg Fin.val hij
    apply Fin.ext
    omega
  have hnxt_maps : IW.image nxt ⊆ InotW := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    simp only [IW, InotW, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hnextW
    exact W7_indep (p' i.1) hi (p' ((i.1 + 1) % 13)) hnextW (hcyc i)
  have hle := Finset.card_le_card hnxt_maps
  rw [Finset.card_image_of_injective IW hnxt_inj, hIW_card, hInotW_card] at hle
  omega

-- ============================================================================
-- Step 6: Explicit Rational Disk & Cycle Witnesses
-- ============================================================================

private def checkPointsDisk (L : List Site) (D ox oy num den : ℤ) : Bool :=
  decide L.Nodup &&
  L.all (fun p => decide (den * QZ (D * p.1 - ox, D * p.2 - oy) ≤ num * D * D))

private lemma pointsFit_of_list (L : List Site) (D ox oy num den : ℤ)
    (hD : 0 < D) (hden : 0 < den)
    (hchk : checkPointsDisk L D ox oy num den = true) :
    pointsFit L.length ((num : ℝ) / (den : ℝ)) := by
  simp only [checkPointsDisk, Bool.and_eq_true, List.all_eq_true] at hchk
  have hnodup : L.Nodup := of_decide_eq_true hchk.1
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hden0 : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  refine ⟨fun i => L[i.1], ((ox : ℝ) / (D : ℝ), (oy : ℝ) / (D : ℝ)), ?_, ?_⟩
  · intro i j hij
    exact (List.nodup_iff_injective_getElem.mp hnodup) hij
  · intro i
    have hmem : L[i.1] ∈ L := List.getElem_mem i.2
    have hleZ : den * QZ (D * L[i.1].1 - ox, D * L[i.1].2 - oy) ≤ num * D * D :=
      of_decide_eq_true (hchk.2 L[i.1] hmem)
    have hleR : (den : ℝ) * (QZ (D * L[i.1].1 - ox, D * L[i.1].2 - oy) : ℝ) ≤
        (num : ℝ) * (D : ℝ) * (D : ℝ) := by exact_mod_cast hleZ
    have hscale : (D : ℝ) ^ 2 *
        (((L[i.1].1 : ℝ) - (ox : ℝ) / (D : ℝ)) ^ 2 +
         ((L[i.1].1 : ℝ) - (ox : ℝ) / (D : ℝ)) * ((L[i.1].2 : ℝ) - (oy : ℝ) / (D : ℝ)) +
         ((L[i.1].2 : ℝ) - (oy : ℝ) / (D : ℝ)) ^ 2) =
        (QZ (D * L[i.1].1 - ox, D * L[i.1].2 - oy) : ℝ) := by
      simp only [QZ]; push_cast; field_simp [hD0.ne']
    rw [le_div_iff₀ hden0]
    have hD2 : 0 < (D : ℝ) ^ 2 := by positivity
    nlinarith

private def checkCycleDisk (L : List Site) (D ox oy num den : ℤ) : Bool :=
  checkPointsDisk L D ox oy num den &&
  decide (3 ≤ L.length) &&
  (List.finRange L.length).all fun i =>
    let q := L.getD ((i.1 + 1) % L.length) (0, 0)
    decide (QZ (L[i.1].1 - q.1, L[i.1].2 - q.2) = 1)

private lemma attainable_of_cycle (L : List Site) (D ox oy num den : ℤ)
    (hD : 0 < D) (hden : 0 < den)
    (hchk : checkCycleDisk L D ox oy num den = true) :
    attainable L.length ((num : ℝ) / (den : ℝ)) := by
  simp only [checkCycleDisk, Bool.and_eq_true, List.all_eq_true] at hchk
  rcases hchk with ⟨⟨hpts, hlen3⟩, hsteps⟩
  have h3 : 3 ≤ L.length := of_decide_eq_true hlen3
  have hpos : 0 < L.length := by omega
  simp only [checkPointsDisk, Bool.and_eq_true, List.all_eq_true] at hpts
  have hnodup : L.Nodup := of_decide_eq_true hpts.1
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hden0 : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  set p : ℕ → Site := fun i => L[i % L.length]'(Nat.mod_lt i hpos)
  refine ⟨p, ((ox : ℝ) / (D : ℝ), (oy : ℝ) / (D : ℝ)), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    have hstep := of_decide_eq_true (hsteps ⟨i, hi⟩ (List.mem_finRange _))
    have hget : L.getD ((i + 1) % L.length) (0, 0) = L[(i + 1) % L.length]'(Nat.mod_lt _ hpos) :=
      List.getD_eq_getElem _ _ (Nat.mod_lt _ hpos)
    rw [hget] at hstep
    simpa only [p, unitStep, QZ, Nat.mod_eq_of_lt hi] using hstep
  · intro i j hij hjm heq
    have hinj := List.nodup_iff_injective_getElem.mp hnodup
    have hmod : i % L.length = j % L.length := by
      have h1 : (⟨i % L.length, Nat.mod_lt i hpos⟩ : Fin L.length) =
          ⟨j % L.length, Nat.mod_lt j hpos⟩ := hinj heq
      exact congrArg Fin.val h1
    have hi_lt : i < L.length := by omega
    rw [Nat.mod_eq_of_lt hi_lt] at hmod
    by_cases hj_lt : j < L.length
    · rw [Nat.mod_eq_of_lt hj_lt] at hmod; omega
    · have hj_eq : j = L.length := by omega
      rw [hj_eq, Nat.mod_self] at hmod
      exact ⟨hmod, hj_eq⟩
  · intro _; exact h3
  · intro i _
    have hmem : p i ∈ L := List.getElem_mem _
    have hleZ : den * QZ (D * (p i).1 - ox, D * (p i).2 - oy) ≤ num * D * D :=
      of_decide_eq_true (hpts.2 (p i) hmem)
    have hleR : (den : ℝ) * (QZ (D * (p i).1 - ox, D * (p i).2 - oy) : ℝ) ≤
        (num : ℝ) * (D : ℝ) * (D : ℝ) := by exact_mod_cast hleZ
    have hscale : (D : ℝ) ^ 2 *
        ((((p i).1 : ℝ) - (ox : ℝ) / (D : ℝ)) ^ 2 +
         (((p i).1 : ℝ) - (ox : ℝ) / (D : ℝ)) * (((p i).2 : ℝ) - (oy : ℝ) / (D : ℝ)) +
         (((p i).2 : ℝ) - (oy : ℝ) / (D : ℝ)) ^ 2) =
        (QZ (D * (p i).1 - ox, D * (p i).2 - oy) : ℝ) := by
      simp only [QZ]; push_cast; field_simp [hD0.ne']
    rw [le_div_iff₀ hden0]
    have hD2 : 0 < (D : ℝ) ^ 2 := by positivity
    nlinarith

private lemma attainable_prefix_of_cycle (L : List Site) (D ox oy num den : ℤ) (m : ℕ)
    (hm0 : 0 < m) (hm : m < L.length) (hD : 0 < D) (hden : 0 < den)
    (hchk : checkCycleDisk L D ox oy num den = true) :
    attainable m ((num : ℝ) / (den : ℝ)) := by
  simp only [checkCycleDisk, Bool.and_eq_true, List.all_eq_true] at hchk
  rcases hchk with ⟨⟨hpts, hlen3⟩, hsteps⟩
  have h3 : 3 ≤ L.length := of_decide_eq_true hlen3
  have hpos : 0 < L.length := by omega
  simp only [checkPointsDisk, Bool.and_eq_true, List.all_eq_true] at hpts
  have hnodup : L.Nodup := of_decide_eq_true hpts.1
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hden0 : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  set p : ℕ → Site := fun i => L[i % L.length]'(Nat.mod_lt i hpos)
  refine ⟨p, ((ox : ℝ) / (D : ℝ), (oy : ℝ) / (D : ℝ)), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    have hiL : i < L.length := by omega
    have hstep := of_decide_eq_true (hsteps ⟨i, hiL⟩ (List.mem_finRange _))
    have hget : L.getD ((i + 1) % L.length) (0, 0) = L[(i + 1) % L.length]'(Nat.mod_lt _ hpos) :=
      List.getD_eq_getElem _ _ (Nat.mod_lt _ hpos)
    rw [hget] at hstep
    simpa only [p, unitStep, QZ, Nat.mod_eq_of_lt hiL] using hstep
  · intro i j hij hjm heq
    have hinj := List.nodup_iff_injective_getElem.mp hnodup
    have hmod : i % L.length = j % L.length :=
      congrArg Fin.val (hinj (a₁ := ⟨i % L.length, Nat.mod_lt i hpos⟩)
        (a₂ := ⟨j % L.length, Nat.mod_lt j hpos⟩) heq)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  · intro heq
    have hinj := List.nodup_iff_injective_getElem.mp hnodup
    have hmod : 0 % L.length = m % L.length :=
      congrArg Fin.val (hinj (a₁ := ⟨0 % L.length, Nat.mod_lt 0 hpos⟩)
        (a₂ := ⟨m % L.length, Nat.mod_lt m hpos⟩) heq)
    rw [Nat.mod_eq_of_lt hpos, Nat.mod_eq_of_lt hm] at hmod
    omega
  · intro i _
    have hmem : p i ∈ L := List.getElem_mem _
    have hleZ : den * QZ (D * (p i).1 - ox, D * (p i).2 - oy) ≤ num * D * D :=
      of_decide_eq_true (hpts.2 (p i) hmem)
    have hleR : (den : ℝ) * (QZ (D * (p i).1 - ox, D * (p i).2 - oy) : ℝ) ≤
        (num : ℝ) * (D : ℝ) * (D : ℝ) := by exact_mod_cast hleZ
    have hscale : (D : ℝ) ^ 2 *
        ((((p i).1 : ℝ) - (ox : ℝ) / (D : ℝ)) ^ 2 +
         (((p i).1 : ℝ) - (ox : ℝ) / (D : ℝ)) * (((p i).2 : ℝ) - (oy : ℝ) / (D : ℝ)) +
         (((p i).2 : ℝ) - (oy : ℝ) / (D : ℝ)) ^ 2) =
        (QZ (D * (p i).1 - ox, D * (p i).2 - oy) : ℝ) := by
      simp only [QZ]; push_cast; field_simp [hD0.ne']
    rw [le_div_iff₀ hden0]
    have hD2 : 0 < (D : ℝ) ^ 2 := by positivity
    nlinarith

-- The 11 explicit rational witnesses
private lemma wit_pts_1 : pointsFit 1 0 := by
  simpa using pointsFit_of_list [(0, 0)] 1 0 0 0 1 (by omega) (by omega) (by decide)

private lemma wit_pts_2 : pointsFit 2 (1 / 4) := by
  simpa using pointsFit_of_list [(0, 0), (1, 0)] 2 1 0 1 4 (by omega) (by omega) (by decide)

private lemma wit_att_1 : attainable 1 (1 / 4) := by
  refine ⟨fun i => if i = 0 then (0, 0) else (1, 0), (1 / 2, 0), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i hi; have : i = 0 := by omega
    subst this; unfold unitStep; norm_num
  · intro i j hij hj1 heq
    have hi0 : i = 0 := by omega
    have hj : j = 1 := by omega
    subst hi0; subst hj; simp at heq
  · intro h; simp at h
  · intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> norm_num

private lemma wit_att_3 : attainable 3 (1 / 3) := by
  simpa using attainable_of_cycle [(0, 0), (1, 0), (0, 1)] 3 1 1 1 3 (by omega) (by omega) (by decide)

private lemma wit_att_4 : attainable 4 (3 / 4) := by
  simpa using attainable_of_cycle [(0, 0), (0, 1), (1, 0), (1, -1)] 2 1 0 3 4 (by omega) (by omega) (by decide)

private def cyc7 : List Site :=
  [(-1, 0), (0, 0), (-1, 1), (0, 1), (1, 0), (1, -1), (0, -1)]

private lemma wit_att_6 : attainable 6 1 := by
  simpa using attainable_prefix_of_cycle cyc7 1 0 0 1 1 6 (by omega) (by decide) (by omega) (by omega) (by decide)

private lemma wit_att_7 : attainable 7 1 := by
  simpa [cyc7] using attainable_of_cycle cyc7 1 0 0 1 1 (by omega) (by omega) (by decide)

private lemma wit_att_8 : attainable 8 (7 / 4) := by
  simpa using attainable_of_cycle
    [(-1, 0), (0, 0), (1, -1), (1, 0), (1, 1), (0, 1), (-1, 2), (-1, 1)]
    2 0 1 7 4 (by omega) (by omega) (by decide)

private lemma wit_att_9 : attainable 9 (49 / 25) := by
  simpa using attainable_of_cycle
    [(-1, 0), (0, 0), (-1, 1), (0, 1), (1, 1), (1, 0), (2, -1), (1, -1), (0, -1)]
    5 2 0 49 25 (by omega) (by omega) (by decide)

private lemma wit_att_10 : attainable 10 (9 / 4) := by
  simpa using attainable_of_cycle
    [(-1, 0), (0, 0), (-1, 1), (0, 1), (1, 1), (1, 0), (2, 0), (2, -1), (1, -1), (0, -1)]
    2 1 0 9 4 (by omega) (by omega) (by decide)

private lemma wit_att_12 : attainable 12 (7 / 3) := by
  simpa using attainable_of_cycle
    [(-1, 0), (0, 0), (1, 0), (0, 1), (-1, 1), (-1, 2), (0, 2), (1, 1), (2, 0), (2, -1), (1, -1), (0, -1)]
    3 1 1 7 3 (by omega) (by omega) (by decide)

private lemma wit_pts_13 : pointsFit 13 3 := by
  simpa [D13_list] using pointsFit_of_list D13_list 1 0 0 3 1 (by omega) (by omega) (by decide)

private lemma wit_att_14 : attainable 14 (13 / 4) := by
  simpa using attainable_of_cycle
    [(-1, 0), (0, 0), (1, 0), (0, 1), (-1, 1), (-1, 2), (0, 2), (1, 1),
     (2, 0), (2, -1), (1, -1), (2, -2), (1, -2), (0, -1)]
    2 1 0 13 4 (by omega) (by omega) (by decide)

-- ============================================================================
-- Step 7: Exact Record Classification on 0..14 and Final Refutation
-- ============================================================================

private lemma not_pts_2_at_0 : ¬ pointsFit 2 0 :=
  not_pointsFit_of_T0 fun _ ho S hS => bound_T1 ho (by norm_num) S hS

private lemma not_pts_3_at_1_4 : ¬ pointsFit 3 (1 / 4) :=
  not_pointsFit_of_T0 fun _ ho S hS => bound_T2 ho (by norm_num) S hS

private lemma not_pts_4_at_1_3 : ¬ pointsFit 4 (1 / 3) :=
  not_pointsFit_of_T0 fun _ ho S hS => bound_T3 ho (by norm_num) S hS

private lemma not_pts_5_at_3_4 : ¬ pointsFit 5 (3 / 4) :=
  not_pointsFit_of_T0 fun _ ho S hS => bound_T4 ho (by norm_num) S hS

private lemma not_pts_8_at_1 : ¬ pointsFit 8 1 :=
  not_pointsFit_of_T0 fun _ ho S hS => bound_T5 ho (by norm_num) S hS

private lemma not_pts_9_at_7_4 : ¬ pointsFit 9 (7 / 4) :=
  not_pointsFit_of_T0 fun _ ho S hS => bound_T6 ho (by norm_num) S hS

private lemma not_pts_10_at_49_25 : ¬ pointsFit 10 (49 / 25) :=
  not_pointsFit_of_T0 fun _ ho S hS => bound_T7 ho (by norm_num) S hS

private lemma not_pts_11_at_9_4 : ¬ pointsFit 11 (9 / 4) :=
  not_pointsFit_of_T0 fun _ ho S hS => bound_T8 ho (by norm_num) S hS

private lemma not_pts_13_at_7_3 : ¬ pointsFit 13 (7 / 3) :=
  not_pointsFit_of_T0 fun _ ho S hS => bound_T9 ho (by norm_num) S hS

private lemma not_pts_14_at_3 : ¬ pointsFit 14 3 :=
  not_pointsFit_of_T0 fun _ ho S hS => by
    rcases bound_T10 ho (by norm_num) S hS with hle | hsub
    · omega
    · have h1 := Finset.card_le_card hsub
      have h2 : D13_list.toFinset.card = 13 := by decide
      omega

private lemma not_pts_15_at_13_4 : ¬ pointsFit 15 (13 / 4) :=
  not_pointsFit_of_T0 fun _ ho S hS => bound_T11 ho (by norm_num) S hS

private lemma recordSize_pointsFit_set {inst : DecidablePred (recordSize pointsFit)} :
    @Finset.filter ℕ (recordSize pointsFit) inst (Finset.range 14) =
      ({1, 2, 3, 4, 7, 8, 9, 10, 12, 13} : Finset ℕ) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hrec⟩
    rcases hrec with ⟨hjpos, s, _, hfit, hnofit⟩
    interval_cases j
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; left; rfl
    · exfalso
      have hs1 : 1 ≤ s := by
        by_contra hlt; push Not at hlt
        exact not_pointsFit_of_T0 (fun _ ho S hS => bound_T4 ho hlt S hS) hfit
      exact hnofit (pointsFit_anti_k (by omega) (pointsFit_mono hs1 (pointsFit_of_attainable wit_att_7)))
    · exfalso
      have hs1 : 1 ≤ s := by
        by_contra hlt; push Not at hlt
        exact not_pointsFit_of_T0 (fun _ ho S hS => bound_T4 ho hlt S hS) (pointsFit_anti_k (by omega) hfit)
      exact hnofit (pointsFit_mono hs1 (pointsFit_of_attainable wit_att_7))
    · right; right; right; right; left; rfl
    · right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; left; rfl
    · exfalso
      have hs73 : 7 / 3 ≤ s := by
        by_contra hlt; push Not at hlt
        exact not_pointsFit_of_T0 (fun _ ho S hS => bound_T8 ho hlt S hS) hfit
      exact hnofit (pointsFit_mono hs73 (pointsFit_of_attainable wit_att_12))
    · right; right; right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨by omega, by omega, 0, by norm_num, wit_pts_1, not_pts_2_at_0⟩
    · exact ⟨by omega, by omega, 1 / 4, by norm_num, wit_pts_2, not_pts_3_at_1_4⟩
    · exact ⟨by omega, by omega, 1 / 3, by norm_num, pointsFit_of_attainable wit_att_3, not_pts_4_at_1_3⟩
    · exact ⟨by omega, by omega, 3 / 4, by norm_num, pointsFit_of_attainable wit_att_4, not_pts_5_at_3_4⟩
    · exact ⟨by omega, by omega, 1, by norm_num, pointsFit_of_attainable wit_att_7, not_pts_8_at_1⟩
    · exact ⟨by omega, by omega, 7 / 4, by norm_num, pointsFit_of_attainable wit_att_8, not_pts_9_at_7_4⟩
    · exact ⟨by omega, by omega, 49 / 25, by norm_num, pointsFit_of_attainable wit_att_9, not_pts_10_at_49_25⟩
    · exact ⟨by omega, by omega, 9 / 4, by norm_num, pointsFit_of_attainable wit_att_10, not_pts_11_at_9_4⟩
    · exact ⟨by omega, by omega, 7 / 3, by norm_num, pointsFit_of_attainable wit_att_12, not_pts_13_at_7_3⟩
    · exact ⟨by omega, by omega, 3, by norm_num, wit_pts_13, not_pts_14_at_3⟩

private lemma recordSize_attainable_set {inst : DecidablePred (recordSize attainable)} :
    @Finset.filter ℕ (recordSize attainable) inst (Finset.range 15) =
      ({1, 3, 4, 7, 8, 9, 10, 12, 14} : Finset ℕ) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hrec⟩
    rcases hrec with ⟨hjpos, s, _, hatt, hnoatt⟩
    interval_cases j
    · left; rfl
    · exfalso
      have hs13 : 1 / 3 ≤ s := by
        by_contra hlt; push Not at hlt
        exact not_pointsFit_of_T0 (fun _ ho S hS => bound_T2 ho hlt S hS)
          (pointsFit_three_of_attainable_two hatt)
      exact hnoatt (attainable_mono hs13 wit_att_3)
    · right; left; rfl
    · right; right; left; rfl
    · exfalso
      have hs1 : 1 ≤ s := by
        by_contra hlt; push Not at hlt
        exact not_pointsFit_of_T0 (fun _ ho S hS => bound_T4 ho hlt S hS)
          (pointsFit_of_attainable hatt)
      exact hnoatt (attainable_mono hs1 wit_att_6)
    · exfalso
      have hs1 : 1 ≤ s := by
        by_contra hlt; push Not at hlt
        exact not_pointsFit_of_T0 (fun _ ho S hS => bound_T4 ho hlt S hS)
          (pointsFit_anti_k (by omega) (pointsFit_of_attainable hatt))
      exact hnoatt (attainable_mono hs1 wit_att_7)
    · right; right; right; left; rfl
    · right; right; right; right; left; rfl
    · right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; left; rfl
    · exfalso
      have hs73 : 7 / 3 ≤ s := by
        by_contra hlt; push Not at hlt
        exact not_pointsFit_of_T0 (fun _ ho S hS => bound_T8 ho hlt S hS)
          (pointsFit_of_attainable hatt)
      exact hnoatt (attainable_mono hs73 wit_att_12)
    · right; right; right; right; right; right; right; left; rfl
    · exfalso
      have hs134 : 13 / 4 ≤ s := by
        by_contra hlt; push Not at hlt
        exact not_attainable_13_of_lt hlt hatt
      exact hnoatt (attainable_mono hs134 wit_att_14)
    · right; right; right; right; right; right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨by omega, by omega, 1 / 4, by norm_num, wit_att_1,
        fun h => not_pts_3_at_1_4 (pointsFit_three_of_attainable_two h)⟩
    · exact ⟨by omega, by omega, 1 / 3, by norm_num, wit_att_3,
        fun h => not_pts_4_at_1_3 (pointsFit_of_attainable h)⟩
    · exact ⟨by omega, by omega, 3 / 4, by norm_num, wit_att_4,
        fun h => not_pts_5_at_3_4 (pointsFit_of_attainable h)⟩
    · exact ⟨by omega, by omega, 1, by norm_num, wit_att_7,
        fun h => not_pts_8_at_1 (pointsFit_of_attainable h)⟩
    · exact ⟨by omega, by omega, 7 / 4, by norm_num, wit_att_8,
        fun h => not_pts_9_at_7_4 (pointsFit_of_attainable h)⟩
    · exact ⟨by omega, by omega, 49 / 25, by norm_num, wit_att_9,
        fun h => not_pts_10_at_49_25 (pointsFit_of_attainable h)⟩
    · exact ⟨by omega, by omega, 9 / 4, by norm_num, wit_att_10,
        fun h => not_pts_11_at_9_4 (pointsFit_of_attainable h)⟩
    · exact ⟨by omega, by omega, 7 / 3, by norm_num, wit_att_12,
        fun h => not_pts_13_at_7_3 (pointsFit_of_attainable h)⟩
    · exact ⟨by omega, by omega, 13 / 4, by norm_num, wit_att_14,
        fun h => not_pts_15_at_13_4 (pointsFit_of_attainable h)⟩

private lemma disproof_aux :
    ¬ (∀ n k m : ℕ, 2 < n →
      recordSize pointsFit k → recordRank pointsFit k = n →
      recordSize attainable m → recordRank attainable m = n - 1 → k = m) := by
  intro hmain
  have hrec13 : recordSize pointsFit 13 :=
    ⟨by omega, 3, by norm_num, wit_pts_13, not_pts_14_at_3⟩
  have hrank13 : recordRank pointsFit 13 = 10 := by
    unfold recordRank
    rw [recordSize_pointsFit_set]
    decide
  have hrec14 : recordSize attainable 14 :=
    ⟨by omega, 13 / 4, by norm_num, wit_att_14,
      fun h => not_pts_15_at_13_4 (pointsFit_of_attainable h)⟩
  have hrank14 : recordRank attainable 14 = 9 := by
    unfold recordRank
    rw [recordSize_attainable_set]
    decide
  have heq := hmain 10 13 14 (by omega) hrec13 hrank13 hrec14 hrank14
  omega

end OMA.S_oeis_a346784.Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a346784.main) :=
  OMA.S_oeis_a346784.Disproof.disproof_aux
