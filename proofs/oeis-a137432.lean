import OMAStatements.S_oeis_a137432

-- Problem: A137432: Number of ways to place n^2 nonattacking kings on a 2n X 2n cylindrical chessboard.
-- Upstream: formal-conjectures statements/oeis-a137432.lean:0 (declaration OMA.S_oeis_a137432.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped Nat

namespace A137432Proof

open Finset Filter Topology Real
open scoped Classical

/-! ### Section 1: Exact `2 × 2` block bijection for `n ≥ 3` -/

private def cNext {n : ℕ} (hn : 0 < n) (c : Fin n) : Fin n :=
  ⟨(c.1 + 1) % n, Nat.mod_lt _ hn⟩

private def cPrev {n : ℕ} (hn : 0 < n) (c : Fin n) : Fin n :=
  ⟨(c.1 + n - 1) % n, Nat.mod_lt _ hn⟩

private lemma cNext_cPrev {n : ℕ} (hn : 0 < n) (c : Fin n) :
    cNext hn (cPrev hn c) = c := by
  ext
  simp only [cNext, cPrev]
  by_cases h0 : c.1 = 0
  · simp [h0, show n - 1 + 1 = n by omega]
  · have hc := c.isLt
    have h1 : (c.1 + n - 1) % n = c.1 - 1 := by
      rw [show c.1 + n - 1 = (c.1 - 1) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [h1, show c.1 - 1 + 1 = c.1 by omega, Nat.mod_eq_of_lt hc]

private lemma cPrev_cNext {n : ℕ} (hn : 0 < n) (c : Fin n) :
    cPrev hn (cNext hn c) = c := by
  ext
  simp only [cNext, cPrev]
  have hc := c.isLt
  by_cases hlast : c.1 + 1 = n
  · rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hlt : c.1 + 1 < n := by omega
    rw [Nat.mod_eq_of_lt hlt, show c.1 + 1 + n - 1 = c.1 + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hc]

private def cNextPerm {n : ℕ} (hn : 0 < n) : Equiv.Perm (Fin n) where
  toFun := cNext hn
  invFun := cPrev hn
  left_inv := cPrev_cNext hn
  right_inv := cNext_cPrev hn

private def squareOf (n : ℕ) (r c : Fin n) (dy dx : Bool) : Fin (2 * n) × ZMod (2 * n) :=
  (⟨2 * r.1 + if dy then 1 else 0, by have := r.isLt; cases dy <;> dsimp <;> omega⟩,
   ((2 * c.1 + if dx then 1 else 0 : ℕ) : ZMod (2 * n)))

private def blockOf {n : ℕ} (hn : 0 < n) (p : Fin (2 * n) × ZMod (2 * n)) : Fin n × Fin n :=
  haveI : NeZero (2 * n) := ⟨by omega⟩
  (⟨p.1.1 / 2, by have := p.1.isLt; omega⟩,
   ⟨p.2.val / 2, by have := ZMod.val_lt p.2; omega⟩)

private lemma blockOf_squareOf {n : ℕ} (hn : 0 < n) (r c : Fin n) (dy dx : Bool) :
    blockOf hn (squareOf n r c dy dx) = (r, c) := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hlt : 2 * c.1 + (if dx then 1 else 0) < 2 * n := by
    have := c.isLt; cases dx <;> dsimp <;> omega
  ext
  · simp only [blockOf, squareOf]
    cases dy <;> dsimp <;> omega
  · simp only [blockOf, squareOf, ZMod.val_natCast_of_lt hlt]
    cases dx <;> dsimp <;> omega

private lemma squareOf_val_col {n : ℕ} (hn : 0 < n) (r c : Fin n) (dy dx : Bool) :
    haveI : NeZero (2 * n) := ⟨by omega⟩
    (squareOf n r c dy dx).2.val = 2 * c.1 + if dx then 1 else 0 := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hlt : 2 * c.1 + (if dx then 1 else 0) < 2 * n := by
    have := c.isLt; cases dx <;> dsimp <;> omega
  exact ZMod.val_natCast_of_lt hlt

private lemma squareOf_blockOf {n : ℕ} (hn : 0 < n) (p : Fin (2 * n) × ZMod (2 * n)) :
    haveI : NeZero (2 * n) := ⟨by omega⟩
    squareOf n (blockOf hn p).1 (blockOf hn p).2 (decide (p.1.1 % 2 = 1))
      (decide (p.2.val % 2 = 1)) = p := by
  have : NeZero (2 * n) := ⟨by omega⟩
  rcases p with ⟨row, col⟩
  apply Prod.ext
  · ext
    simp only [squareOf, blockOf]
    by_cases h : row.1 % 2 = 1 <;> simp [h] <;> omega
  · simp only [squareOf, blockOf]
    have hval : 2 * (col.val / 2) + (if decide (col.val % 2 = 1) then 1 else 0) = col.val := by
      by_cases h : col.val % 2 = 1 <;> simp [h] <;> omega
    rw [hval, ZMod.natCast_zmod_val]

private lemma attacks_same_block {n : ℕ} (hn : 0 < n) {p q : Fin (2 * n) × ZMod (2 * n)}
    (hne : p ≠ q) (hb : blockOf hn p = blockOf hn q) :
    OMA.S_oeis_a137432.Attacks n p q := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hr : p.1.1 / 2 = q.1.1 / 2 := congrArg (fun x => x.1.1) hb
  have hc : p.2.val / 2 = q.2.val / 2 := congrArg (fun x => x.2.1) hb
  refine ⟨hne, ⟨by omega, by omega⟩, ?_⟩
  have hp : ((p.2.val : ℕ) : ZMod (2 * n)) = p.2 := ZMod.natCast_zmod_val p.2
  have hq : ((q.2.val : ℕ) : ZMod (2 * n)) = q.2 := ZMod.natCast_zmod_val q.2
  rcases (by omega : p.2.val = q.2.val ∨ p.2.val = q.2.val + 1 ∨ q.2.val = p.2.val + 1) with
    h | h | h
  · left; rw [← hp, ← hq, h]
  · right; left; rw [← hp, ← hq, h, Nat.cast_add, Nat.cast_one]
  · right; right; rw [← hp, ← hq, h, Nat.cast_add, Nat.cast_one]

/-- Helper for adjacent columns in `ZMod (2 * n)` when `n ≥ 3`. -/
private lemma col_adj_iff {n : ℕ} (hn : 3 ≤ n) (c₁ c₂ : Fin n) (dx₁ dx₂ : Bool) :
    let a : ZMod (2 * n) := ((2 * c₁.1 + if dx₁ then 1 else 0 : ℕ) : ZMod (2 * n))
    let b : ZMod (2 * n) := ((2 * c₂.1 + if dx₂ then 1 else 0 : ℕ) : ZMod (2 * n))
    (a = b ∨ a = b + 1 ∨ b = a + 1) ↔
      (c₁ = c₂) ∨
      (dx₁ = true ∧ dx₂ = false ∧ c₂ = cNext (by omega) c₁) ∨
      (dx₂ = true ∧ dx₁ = false ∧ c₁ = cNext (by omega) c₂) := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have h1lt : 2 * c₁.1 + (if dx₁ then 1 else 0) < 2 * n := by
    have := c₁.isLt; cases dx₁ <;> dsimp <;> omega
  have h2lt : 2 * c₂.1 + (if dx₂ then 1 else 0) < 2 * n := by
    have := c₂.isLt; cases dx₂ <;> dsimp <;> omega
  set u := 2 * c₁.1 + if dx₁ then 1 else 0
  set v := 2 * c₂.1 + if dx₂ then 1 else 0
  have hu : ((u : ℕ) : ZMod (2 * n)).val = u := ZMod.val_natCast_of_lt h1lt
  have hv : ((v : ℕ) : ZMod (2 * n)).val = v := ZMod.val_natCast_of_lt h2lt
  have hMod : ∀ x y : ℕ, x < 2 * n → y < 2 * n →
      (((x : ℕ) : ZMod (2 * n)) = ((y : ℕ) : ZMod (2 * n)) + 1 ↔
        x = y + 1 ∨ (y = 2 * n - 1 ∧ x = 0)) := by
    intro x y hx hy
    have h1 : (((y : ℕ) : ZMod (2 * n)) + 1) = (((y + 1 : ℕ) : ZMod (2 * n))) := by push_cast; rfl
    rw [h1]
    constructor
    · intro heq
      have hval := congrArg ZMod.val heq
      rw [ZMod.val_natCast_of_lt hx, ZMod.val_natCast] at hval
      by_cases hyl : y + 1 < 2 * n
      · left; rwa [Nat.mod_eq_of_lt hyl] at hval
      · right
        have hyeq : y + 1 = 2 * n := by omega
        rw [hyeq, Nat.mod_self] at hval
        exact ⟨by omega, hval⟩
    · rintro (rfl | ⟨rfl, rfl⟩)
      · rfl
      · have : 2 * n - 1 + 1 = 2 * n := by omega
        rw [this, ZMod.natCast_self, Nat.cast_zero]
  dsimp only
  rw [hMod u v h1lt h2lt, hMod v u h2lt h1lt]
  have heq_iff : ((u : ℕ) : ZMod (2 * n)) = ((v : ℕ) : ZMod (2 * n)) ↔ u = v := by
    constructor
    · intro h; have := congrArg ZMod.val h; rwa [hu, hv] at this
    · intro h; rw [h]
  rw [heq_iff]
  have hc1 := c₁.isLt
  have hc2 := c₂.isLt
  constructor
  · rintro (h | (h | ⟨h1, h2⟩) | (h | ⟨h1, h2⟩))
    · left; ext; cases dx₁ <;> cases dx₂ <;> simp [u, v] at h <;> omega
    · cases dx₁ <;> cases dx₂ <;> simp [u, v] at h
      · omega
      · right; right; refine ⟨rfl, rfl, ?_⟩
        ext; simp only [cNext]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      · left; ext; omega
      · omega
    · right; right
      cases dx₁ <;> cases dx₂ <;> simp [u, v] at h1 h2
      · omega
      · refine ⟨rfl, rfl, ?_⟩
        ext; simp only [cNext]
        have : c₂.1 + 1 = n := by omega
        rw [this, Nat.mod_self]; omega
    · cases dx₁ <;> cases dx₂ <;> simp [u, v] at h
      · omega
      · left; ext; omega
      · right; left; refine ⟨rfl, rfl, ?_⟩
        ext; simp only [cNext]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      · omega
    · right; left
      cases dx₁ <;> cases dx₂ <;> simp [u, v] at h1 h2
      · omega
      · refine ⟨rfl, rfl, ?_⟩
        ext; simp only [cNext]
        have : c₁.1 + 1 = n := by omega
        rw [this, Nat.mod_self]; omega
  · rintro (rfl | ⟨rfl, rfl, hc⟩ | ⟨rfl, rfl, hc⟩)
    · cases dx₁ <;> cases dx₂ <;> simp [u, v]
    · right; right
      have hcv : c₂.1 = (c₁.1 + 1) % n := congrArg Fin.val hc
      by_cases hlast : c₁.1 + 1 < n
      · left; rw [Nat.mod_eq_of_lt hlast] at hcv; simp [u, v]; omega
      · right
        have h1 : c₁.1 + 1 = n := by omega
        rw [h1, Nat.mod_self] at hcv
        simp [u, v]; omega
    · right; left
      have hcv : c₁.1 = (c₂.1 + 1) % n := congrArg Fin.val hc
      by_cases hlast : c₂.1 + 1 < n
      · left; rw [Nat.mod_eq_of_lt hlast] at hcv; simp [u, v]; omega
      · right
        have h1 : c₂.1 + 1 = n := by omega
        rw [h1, Nat.mod_self] at hcv
        simp [u, v]; omega

/-- The valid `(h, x)` condition for the cylindrical `2n × 2n` king problem. -/
private def ValidHX {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) (x : Fin n → Bool) : Prop :=
  ∀ (c : Fin n) (r : ℕ) (hr : r + 1 < n),
    (x ⟨r, by omega⟩ = true ∧ x ⟨r + 1, hr⟩ = false →
      ¬ ((h c).1 ≤ r ∧ r + 2 ≤ (h (cNext hn c)).1)) ∧
    (x ⟨r, by omega⟩ = false ∧ x ⟨r + 1, hr⟩ = true →
      ¬ ((h (cNext hn c)).1 ≤ r ∧ r + 2 ≤ (h c).1))

private lemma card_a_eq_card_validHX {n : ℕ} (hn : 3 ≤ n) :
    OMA.S_oeis_a137432.a n =
      Fintype.card { p : (Fin n → Fin (n + 1)) × (Fin n → Bool) // ValidHX (by omega) p.1 p.2 } := by
  classical
  have hn0 : 0 < n := by omega
  have : NeZero (2 * n) := ⟨by omega⟩
  unfold OMA.S_oeis_a137432.a
  rw [Nat.card_eq_fintype_card]
  refine Fintype.card_congr ?_
  -- Build equivalence between valid king sets `S` and valid `(h, x)` pairs
  let toHX :
      { S : Finset (Fin (2 * n) × ZMod (2 * n)) //
        S.card = n ^ 2 ∧ ∀ p ∈ S, ∀ q ∈ S, ¬ OMA.S_oeis_a137432.Attacks n p q } →
      { p : (Fin n → Fin (n + 1)) × (Fin n → Bool) // ValidHX hn0 p.1 p.2 } := fun ⟨S, hcard, hno⟩ => by
    -- `blockOf` is injective on `S`, hence a bijection `S → Fin n × Fin n`
    have hinj : Set.InjOn (blockOf hn0) (S : Set _) := by
      intro p hp q hq hEq
      by_contra hne
      exact hno p hp q hq (attacks_same_block hn0 hne hEq)
    have himg : S.image (blockOf hn0) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn hinj, hcard, Fintype.card_prod, Fintype.card_fin]
      ring
    have hex : ∀ b : Fin n × Fin n, ∃ p ∈ S, blockOf hn0 p = b := by
      intro b
      have hb : b ∈ S.image (blockOf hn0) := himg.symm ▸ Finset.mem_univ b
      exact Finset.mem_image.mp hb
    let pick : Fin n → Fin n → Fin (2 * n) × ZMod (2 * n) := fun r c => Classical.choose (hex (r, c))
    have hpick_mem : ∀ r c, pick r c ∈ S := fun r c => (Classical.choose_spec (hex (r, c))).1
    have hpick_blk : ∀ r c, blockOf hn0 (pick r c) = (r, c) := fun r c =>
      (Classical.choose_spec (hex (r, c))).2
    let dy : Fin n → Fin n → Bool := fun r c => decide ((pick r c).1.1 % 2 = 1)
    let dx : Fin n → Fin n → Bool := fun r c => decide ((pick r c).2.val % 2 = 1)
    have hpick_eq : ∀ r c, pick r c = squareOf n r c (dy r c) (dx r c) := by
      intro r c
      have h1 := squareOf_blockOf hn0 (pick r c)
      rw [hpick_blk r c] at h1
      exact h1.symm
    -- Vertical monotonicity: `dy r c = true → dy (r+1) c = true`
    have hdy_mono : ∀ (c : Fin n) (r : ℕ) (hr : r + 1 < n),
        dy ⟨r, by omega⟩ c = true → dy ⟨r + 1, hr⟩ c = true := by
      intro c r hr h1
      by_contra h2
      have h2f : dy ⟨r + 1, hr⟩ c = false := Bool.eq_false_iff.mpr h2
      have hAtt : OMA.S_oeis_a137432.Attacks n (pick ⟨r, by omega⟩ c) (pick ⟨r + 1, hr⟩ c) := by
        rw [hpick_eq, hpick_eq]
        refine ⟨?_, ?_, ?_⟩
        · intro heq
          have hb := congrArg (blockOf hn0) heq
          rw [blockOf_squareOf, blockOf_squareOf] at hb
          have h1' := congrArg (fun z => z.1.1) hb
          dsimp at h1'; omega
        · simp only [squareOf, h1, h2f]; dsimp; omega
        · exact (col_adj_iff hn c c _ _).mpr (Or.inl rfl)
      exact hno _ (hpick_mem ⟨r, by omega⟩ c) _ (hpick_mem ⟨r + 1, hr⟩ c) hAtt
    have hdy_mono_le : ∀ (c : Fin n) (r₁ r₂ : Fin n), r₁ ≤ r₂ → dy r₁ c = true → dy r₂ c = true := by
      intro c r₁ r₂ hle h1
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      induction k generalizing r₂ with
      | zero =>
        have : r₂ = r₁ := Fin.ext (by omega)
        rwa [this]
      | succ k ih =>
        have hrk : r₁.1 + k < n := by have := r₂.isLt; omega
        have hprev : dy ⟨r₁.1 + k, hrk⟩ c = true := ih ⟨r₁.1 + k, hrk⟩ (by show r₁.1 ≤ r₁.1 + k; omega) rfl
        have hstep := hdy_mono c (r₁.1 + k) (by have := r₂.isLt; omega) hprev
        have heq : (⟨r₁.1 + k + 1, by have := r₂.isLt; omega⟩ : Fin n) = r₂ := Fin.ext (by dsimp; omega)
        rwa [heq] at hstep
    -- Horizontal constancy around the cylinder
    have hdx_step : ∀ (r c : Fin n), dx r c = true → dx r (cNext hn0 c) = true := by
      intro r c h1
      by_contra h2
      have h2f : dx r (cNext hn0 c) = false := Bool.eq_false_iff.mpr h2
      have hAtt : OMA.S_oeis_a137432.Attacks n (pick r c) (pick r (cNext hn0 c)) := by
        rw [hpick_eq, hpick_eq]
        refine ⟨?_, ?_, ?_⟩
        · intro heq
          have hb := congrArg (blockOf hn0) heq
          rw [blockOf_squareOf, blockOf_squareOf] at hb
          have hc := congrArg (fun z => z.2.1) hb
          simp only [cNext] at hc
          have := c.isLt
          by_cases hlast : c.1 + 1 < n
          · rw [Nat.mod_eq_of_lt hlast] at hc; omega
          · have : c.1 + 1 = n := by omega
            rw [this, Nat.mod_self] at hc; omega
        · simp only [squareOf]; cases dy r c <;> cases dy r (cNext hn0 c) <;> dsimp <;> omega
        · exact (col_adj_iff hn c (cNext hn0 c) _ _).mpr (Or.inr (Or.inl ⟨h1, h2f, rfl⟩))
      exact hno _ (hpick_mem r c) _ (hpick_mem r (cNext hn0 c)) hAtt
    have hdx_const : ∀ (r c : Fin n), dx r c = dx r ⟨0, hn0⟩ := by
      intro r
      have hiter : ∀ (k : ℕ) (c : Fin n), dx r c = true → dx r ((cNextPerm hn0)^[k] c) = true := by
        intro k
        induction k with
        | zero => intro c hc; simpa using hc
        | succ k ih =>
          intro c hc
          rw [Function.iterate_succ_apply']
          exact hdx_step r _ (ih c hc)
      have hiter_val : ∀ (k : ℕ) (c : Fin n), ((cNextPerm hn0)^[k] c).1 = (c.1 + k) % n := by
        intro k
        induction k with
        | zero => intro c; simp [Nat.mod_eq_of_lt c.isLt]
        | succ k ih =>
          intro c
          rw [Function.iterate_succ_apply']
          change ((((cNextPerm hn0)^[k] c).1 + 1) % n) = (c.1 + (k + 1)) % n
          rw [ih c, Nat.mod_add_mod, add_assoc]
      intro c
      cases h0 : dx r ⟨0, hn0⟩
      · cases hc : dx r c
        · rfl
        · have h1 := hiter (n - c.1) c hc
          have hpos : ((cNextPerm hn0)^[n - c.1] c) = ⟨0, hn0⟩ := by
            ext; rw [hiter_val]; have := c.isLt
            rw [show c.1 + (n - c.1) = n by omega, Nat.mod_self]
          rw [hpos, h0] at h1
          contradiction
      · have h1 := hiter c.1 ⟨0, hn0⟩ h0
        have hpos : ((cNextPerm hn0)^[c.1] ⟨0, hn0⟩) = c := by
          ext; rw [hiter_val]; simp [Nat.mod_eq_of_lt c.isLt]
        rwa [hpos] at h1
    -- Define `h` and `x`
    let hFun : Fin n → Fin (n + 1) := fun c =>
      ⟨(Finset.univ.filter (fun r : Fin n => dy r c = false)).card,
        Nat.lt_succ_of_le (le_trans (Finset.card_le_univ _) (by simp))⟩
    let xFun : Fin n → Bool := fun r => dx r ⟨0, hn0⟩
    -- Prove `dy r c = decide ((hFun c).1 ≤ r.1)`
    have hdy_iff : ∀ c r, dy r c = true ↔ (hFun c).1 ≤ r.1 := by
      intro c r
      let F := Finset.univ.filter (fun r' : Fin n => dy r' c = false)
      have hF_down : ∀ a b : Fin n, a ≤ b → b ∈ F → a ∈ F := by
        intro a b hle hb
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        by_contra ht
        have hat : dy a c = true := Bool.eq_true_of_not_eq_false ht
        have hbt := hdy_mono_le c a b hle hat
        rw [hbt] at hb; contradiction
      have hF_eq : F = Finset.univ.filter (fun r' : Fin n => r'.1 < F.card) := by
        apply Finset.eq_of_subset_of_card_le
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hsub : Finset.univ.filter (fun b : Fin n => b.1 ≤ a.1) ⊆ F := by
            intro b hb
            exact hF_down b a (Finset.mem_filter.mp hb).2 ha
          have hcard_le := Finset.card_le_card hsub
          have hcard_eq : (Finset.univ.filter (fun b : Fin n => b.1 ≤ a.1)).card = a.1 + 1 := by
            refine Finset.card_eq_of_bijective
              (fun i hi => ⟨i, by have := a.isLt; omega⟩) ?_ ?_ ?_
            · intro b hb
              have hle := (Finset.mem_filter.mp hb).2
              exact ⟨b.1, by omega, rfl⟩
            · intro i hi
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
            · intro i j _ _ h; exact congrArg Fin.val h
          omega
        · have hcard_lt : (Finset.univ.filter (fun r' : Fin n => r'.1 < F.card)).card = F.card := by
            have hle : F.card ≤ n := le_trans (Finset.card_le_univ _) (by simp)
            refine Finset.card_eq_of_bijective
              (fun i hi => ⟨i, by omega⟩) ?_ ?_ ?_
            · intro b hb; exact ⟨b.1, (Finset.mem_filter.mp hb).2, rfl⟩
            · intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
            · intro i j _ _ h; exact congrArg Fin.val h
          omega
      have hr_mem : r ∈ F ↔ r.1 < F.card := by
        conv_lhs => rw [hF_eq]
        simp
      have hFcard : (hFun c).1 = F.card := rfl
      rw [hFcard]
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hr_mem
      change dy r c = false ↔ r.1 < F.card at hr_mem
      change dy r c = true ↔ F.card ≤ r.1
      constructor
      · intro ht
        by_contra hlt
        have hf := hr_mem.mpr (by omega)
        rw [ht] at hf; contradiction
      · intro hle
        by_contra hnt
        have hf : dy r c = false := Bool.eq_false_iff.mpr hnt
        have := hr_mem.mp hf
        omega
    -- Verify `ValidHX`
    have hValid : ValidHX hn0 hFun xFun := by
      intro c r hr
      constructor
      · rintro ⟨hx1, hx2⟩ ⟨hh1, hh2⟩
        have hdy1 : dy ⟨r, by omega⟩ c = true := (hdy_iff c ⟨r, by omega⟩).mpr hh1
        have hdy2 : dy ⟨r + 1, hr⟩ (cNext hn0 c) = false := by
          by_contra hnt
          have ht : dy ⟨r + 1, hr⟩ (cNext hn0 c) = true := Bool.eq_true_of_not_eq_false hnt
          have := (hdy_iff (cNext hn0 c) ⟨r + 1, hr⟩).mp ht
          dsimp at this; omega
        have hdx1 : dx ⟨r, by omega⟩ c = true := by rw [hdx_const]; exact hx1
        have hdx2 : dx ⟨r + 1, hr⟩ (cNext hn0 c) = false := by rw [hdx_const]; exact hx2
        have hAtt : OMA.S_oeis_a137432.Attacks n (pick ⟨r, by omega⟩ c) (pick ⟨r + 1, hr⟩ (cNext hn0 c)) := by
          rw [hpick_eq, hpick_eq]
          refine ⟨?_, ?_, ?_⟩
          · intro heq
            have hb := congrArg (blockOf hn0) heq
            rw [blockOf_squareOf, blockOf_squareOf] at hb
            have h1' := congrArg (fun z => z.1.1) hb
            dsimp at h1'; omega
          · simp only [squareOf, hdy1, hdy2]; dsimp; omega
          · exact (col_adj_iff hn c (cNext hn0 c) _ _).mpr (Or.inr (Or.inl ⟨hdx1, hdx2, rfl⟩))
        exact hno _ (hpick_mem ⟨r, by omega⟩ c) _ (hpick_mem ⟨r + 1, hr⟩ (cNext hn0 c)) hAtt
      · rintro ⟨hx1, hx2⟩ ⟨hh1, hh2⟩
        have hdy1 : dy ⟨r, by omega⟩ (cNext hn0 c) = true := (hdy_iff (cNext hn0 c) ⟨r, by omega⟩).mpr hh1
        have hdy2 : dy ⟨r + 1, hr⟩ c = false := by
          by_contra hnt
          have ht : dy ⟨r + 1, hr⟩ c = true := Bool.eq_true_of_not_eq_false hnt
          have := (hdy_iff c ⟨r + 1, hr⟩).mp ht
          dsimp at this; omega
        have hdx1 : dx ⟨r, by omega⟩ (cNext hn0 c) = false := by rw [hdx_const]; exact hx1
        have hdx2 : dx ⟨r + 1, hr⟩ c = true := by rw [hdx_const]; exact hx2
        have hAtt : OMA.S_oeis_a137432.Attacks n (pick ⟨r, by omega⟩ (cNext hn0 c)) (pick ⟨r + 1, hr⟩ c) := by
          rw [hpick_eq, hpick_eq]
          refine ⟨?_, ?_, ?_⟩
          · intro heq
            have hb := congrArg (blockOf hn0) heq
            rw [blockOf_squareOf, blockOf_squareOf] at hb
            have h1' := congrArg (fun z => z.1.1) hb
            dsimp at h1'; omega
          · simp only [squareOf, hdy1, hdy2]; dsimp; omega
          · exact (col_adj_iff hn (cNext hn0 c) c _ _).mpr (Or.inr (Or.inr ⟨hdx2, hdx1, rfl⟩))
        exact hno _ (hpick_mem ⟨r, by omega⟩ (cNext hn0 c)) _ (hpick_mem ⟨r + 1, hr⟩ c) hAtt
    exact ⟨(hFun, xFun), hValid⟩
  let ofHX :
      { p : (Fin n → Fin (n + 1)) × (Fin n → Bool) // ValidHX hn0 p.1 p.2 } →
      { S : Finset (Fin (2 * n) × ZMod (2 * n)) //
        S.card = n ^ 2 ∧ ∀ p ∈ S, ∀ q ∈ S, ¬ OMA.S_oeis_a137432.Attacks n p q } := fun ⟨(hFun, xFun), hValid⟩ => by
    let f : Fin n × Fin n → Fin (2 * n) × ZMod (2 * n) := fun rc =>
      squareOf n rc.1 rc.2 (decide ((hFun rc.2).1 ≤ rc.1.1)) (xFun rc.1)
    have hf_inj : Function.Injective f := by
      intro a b hab
      have := congrArg (blockOf hn0) hab
      simpa [f, blockOf_squareOf] using this
    let S : Finset (Fin (2 * n) × ZMod (2 * n)) := Finset.univ.image f
    have hcard : S.card = n ^ 2 := by
      rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      ring
    have hno : ∀ p ∈ S, ∀ q ∈ S, ¬ OMA.S_oeis_a137432.Attacks n p q := by
      intro p hp q hq hAtt
      rcases Finset.mem_image.mp hp with ⟨⟨r₁, c₁⟩, _, rfl⟩
      rcases Finset.mem_image.mp hq with ⟨⟨r₂, c₂⟩, _, rfl⟩
      rcases hAtt with ⟨hne, ⟨hrow1, hrow2⟩, hcol⟩
      have hcol' := (col_adj_iff hn c₁ c₂ (xFun r₁) (xFun r₂)).mp hcol
      simp only [f, squareOf] at hrow1 hrow2
      rcases hcol' with rfl | ⟨hx1, hx2, hc⟩ | ⟨hx2, hx1, hc⟩
      · have hrne : r₁ ≠ r₂ := fun h => hne (by rw [h])
        by_cases hlt : r₁.1 < r₂.1
        · have h1 : decide ((hFun c₁).1 ≤ r₁.1) = true ∧ decide ((hFun c₁).1 ≤ r₂.1) = false := by
            cases hA : decide ((hFun c₁).1 ≤ r₁.1) <;> cases hB : decide ((hFun c₁).1 ≤ r₂.1) <;>
              simp [hA, hB] at hrow1 hrow2 ⊢ <;> omega
          have := of_decide_eq_true h1.1
          have := of_decide_eq_false h1.2
          omega
        · have hgt : r₂.1 < r₁.1 := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hrne (Fin.ext h.symm))
          have h1 : decide ((hFun c₁).1 ≤ r₂.1) = true ∧ decide ((hFun c₁).1 ≤ r₁.1) = false := by
            cases hA : decide ((hFun c₁).1 ≤ r₁.1) <;> cases hB : decide ((hFun c₁).1 ≤ r₂.1) <;>
              simp [hA, hB] at hrow1 hrow2 ⊢ <;> omega
          have := of_decide_eq_true h1.1
          have := of_decide_eq_false h1.2
          omega
      · have hrne : r₁ ≠ r₂ := fun h => by rw [h, hx2] at hx1; contradiction
        by_cases hlt : r₁.1 < r₂.1
        · have hstep : r₂.1 = r₁.1 + 1 ∧ decide ((hFun c₁).1 ≤ r₁.1) = true ∧
              decide ((hFun c₂).1 ≤ r₂.1) = false := by
            cases hA : decide ((hFun c₁).1 ≤ r₁.1) <;> cases hB : decide ((hFun c₂).1 ≤ r₂.1) <;>
              simp [hA, hB] at hrow1 hrow2 ⊢ <;> omega
          have hr2 : r₁.1 + 1 < n := by have := r₂.isLt; omega
          have hr2eq : r₂ = ⟨r₁.1 + 1, hr2⟩ := Fin.ext hstep.1
          rw [hr2eq] at hx2
          have hh1 : (hFun c₁).1 ≤ r₁.1 := of_decide_eq_true hstep.2.1
          have hh2 : r₁.1 + 2 ≤ (hFun (cNext hn0 c₁)).1 := by
            have := of_decide_eq_false hstep.2.2
            rw [hc, hstep.1] at this; omega
          exact (hValid c₁ r₁.1 hr2).1 ⟨hx1, hx2⟩ ⟨hh1, hh2⟩
        · have hgt : r₂.1 < r₁.1 := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hrne (Fin.ext h.symm))
          have hstep : r₁.1 = r₂.1 + 1 ∧ decide ((hFun c₂).1 ≤ r₂.1) = true ∧
              decide ((hFun c₁).1 ≤ r₁.1) = false := by
            cases hA : decide ((hFun c₁).1 ≤ r₁.1) <;> cases hB : decide ((hFun c₂).1 ≤ r₂.1) <;>
              simp [hA, hB] at hrow1 hrow2 ⊢ <;> omega
          have hr1 : r₂.1 + 1 < n := by have := r₁.isLt; omega
          have hr1eq : r₁ = ⟨r₂.1 + 1, hr1⟩ := Fin.ext hstep.1
          rw [hr1eq] at hx1
          have hh1 : (hFun (cNext hn0 c₁)).1 ≤ r₂.1 := by
            have := of_decide_eq_true hstep.2.1; rwa [← hc]
          have hh2 : r₂.1 + 2 ≤ (hFun c₁).1 := by
            have := of_decide_eq_false hstep.2.2; omega
          exact (hValid c₁ r₂.1 hr1).2 ⟨hx2, hx1⟩ ⟨hh1, hh2⟩
      · have hrne : r₁ ≠ r₂ := fun h => by rw [h, hx2] at hx1; contradiction
        by_cases hlt : r₁.1 < r₂.1
        · have hstep : r₂.1 = r₁.1 + 1 ∧ decide ((hFun c₁).1 ≤ r₁.1) = true ∧
              decide ((hFun c₂).1 ≤ r₂.1) = false := by
            cases hA : decide ((hFun c₁).1 ≤ r₁.1) <;> cases hB : decide ((hFun c₂).1 ≤ r₂.1) <;>
              simp [hA, hB] at hrow1 hrow2 ⊢ <;> omega
          have hr2 : r₁.1 + 1 < n := by have := r₂.isLt; omega
          have hr2eq : r₂ = ⟨r₁.1 + 1, hr2⟩ := Fin.ext hstep.1
          rw [hr2eq] at hx2
          have hh1 : (hFun (cNext hn0 c₂)).1 ≤ r₁.1 := by
            have := of_decide_eq_true hstep.2.1; rwa [← hc]
          have hh2 : r₁.1 + 2 ≤ (hFun c₂).1 := by
            have := of_decide_eq_false hstep.2.2; omega
          exact (hValid c₂ r₁.1 hr2).2 ⟨hx1, hx2⟩ ⟨hh1, hh2⟩
        · have hgt : r₂.1 < r₁.1 := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hrne (Fin.ext h.symm))
          have hstep : r₁.1 = r₂.1 + 1 ∧ decide ((hFun c₂).1 ≤ r₂.1) = true ∧
              decide ((hFun c₁).1 ≤ r₁.1) = false := by
            cases hA : decide ((hFun c₁).1 ≤ r₁.1) <;> cases hB : decide ((hFun c₂).1 ≤ r₂.1) <;>
              simp [hA, hB] at hrow1 hrow2 ⊢ <;> omega
          have hr1 : r₂.1 + 1 < n := by have := r₁.isLt; omega
          have hr1eq : r₁ = ⟨r₂.1 + 1, hr1⟩ := Fin.ext hstep.1
          rw [hr1eq] at hx1
          have hh1 : (hFun c₂).1 ≤ r₂.1 := of_decide_eq_true hstep.2.1
          have hh2 : r₂.1 + 2 ≤ (hFun (cNext hn0 c₂)).1 := by
            have := of_decide_eq_false hstep.2.2
            rw [hc, hstep.1] at this; omega
          exact (hValid c₂ r₂.1 hr1).1 ⟨hx2, hx1⟩ ⟨hh1, hh2⟩
    exact ⟨S, hcard, hno⟩
  refine
    { toFun := toHX
      invFun := ofHX
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨S, hcard, hno⟩
    apply Subtype.ext
    dsimp only [ofHX, toHX]
    have hinj : Set.InjOn (blockOf hn0) (S : Set _) := by
      intro p hp q hq hEq
      by_contra hne
      exact hno p hp q hq (attacks_same_block hn0 hne hEq)
    have hcard_eq : (Finset.univ.image (fun rc : Fin n × Fin n =>
        squareOf n rc.1 rc.2
          (decide (((toHX ⟨S, hcard, hno⟩).1.1 rc.2).1 ≤ rc.1.1))
          ((toHX ⟨S, hcard, hno⟩).1.2 rc.1))).card = S.card :=
      ((ofHX (toHX ⟨S, hcard, hno⟩)).2.1).trans hcard.symm
    apply Finset.eq_of_subset_of_card_le _ (le_of_eq hcard_eq.symm)
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨⟨r, c⟩, _, rfl⟩
    have himg : S.image (blockOf hn0) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn hinj, hcard, Fintype.card_prod, Fintype.card_fin]; ring
    obtain ⟨q, hqS, hqb⟩ := Finset.mem_image.mp (himg.symm ▸ Finset.mem_univ (r, c))
    suffices hEq : squareOf n r c
        (decide (((toHX ⟨S, hcard, hno⟩).1.1 c).1 ≤ r.1))
        ((toHX ⟨S, hcard, hno⟩).1.2 r) = q by rwa [hEq]
    have hq_sq := squareOf_blockOf hn0 q
    rw [hqb] at hq_sq
    rw [← hq_sq]
    congr 1
    · have hmem_pick : ∀ r' : Fin n, ∃ q' ∈ S, blockOf hn0 q' = (r', c) := fun r' =>
        Finset.mem_image.mp (himg.symm ▸ Finset.mem_univ (r', c))
      have huniq : ∀ {r' c' p₁ p₂}, p₁ ∈ S → p₂ ∈ S → blockOf hn0 p₁ = (r', c') →
          blockOf hn0 p₂ = (r', c') → p₁ = p₂ :=
        fun h1 h2 b1 b2 => hinj h1 h2 (b1.trans b2.symm)
      let dyc : Fin n → Bool := fun r' => decide ((Classical.choose (hmem_pick r')).1.1 % 2 = 1)
      have hdyc_mono : ∀ r₁ r₂ : Fin n, r₁ ≤ r₂ → dyc r₁ = true → dyc r₂ = true := by
        intro r₁ r₂ hle h1
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
        induction k generalizing r₂ with
        | zero =>
          have : r₂ = r₁ := Fin.ext (by omega); rwa [this]
        | succ k ih =>
          have hrk : r₁.1 + k < n := by have := r₂.isLt; omega
          have hprev := ih ⟨r₁.1 + k, hrk⟩ (by show r₁.1 ≤ r₁.1 + k; omega) rfl
          by_contra h2
          have h2f : dyc r₂ = false := Bool.eq_false_iff.mpr h2
          let p1 := Classical.choose (hmem_pick ⟨r₁.1 + k, hrk⟩)
          let p2 := Classical.choose (hmem_pick r₂)
          have hp1 := Classical.choose_spec (hmem_pick ⟨r₁.1 + k, hrk⟩)
          have hp2 := Classical.choose_spec (hmem_pick r₂)
          have hp1s := squareOf_blockOf hn0 p1; rw [hp1.2] at hp1s
          have hp2s := squareOf_blockOf hn0 p2; rw [hp2.2] at hp2s
          have hAtt : OMA.S_oeis_a137432.Attacks n p1 p2 := by
            rw [← hp1s, ← hp2s]
            refine ⟨?_, ?_, ?_⟩
            · intro heq
              have := congrArg (fun z => (blockOf hn0 z).1.1) heq
              rw [blockOf_squareOf, blockOf_squareOf] at this; dsimp at this; omega
            · have h1' : decide (p1.1.1 % 2 = 1) = true := hprev
              have h2' : decide (p2.1.1 % 2 = 1) = false := h2f
              simp only [squareOf, h1', h2']; dsimp; omega
            · exact (col_adj_iff hn c c _ _).mpr (Or.inl rfl)
          exact hno p1 hp1.1 p2 hp2.1 hAtt
      have hdyc_r : dyc r = decide (q.1.1 % 2 = 1) := by
        have hpq := huniq (Classical.choose_spec (hmem_pick r)).1 hqS
          (Classical.choose_spec (hmem_pick r)).2 hqb
        simp [dyc, hpq]
      have hfilt_eq :
          ((toHX ⟨S, hcard, hno⟩).1.1 c).1 =
          (Finset.univ.filter (fun r' : Fin n => dyc r' = false)).card := by
        change (Finset.univ.filter (fun r' : Fin n => _)).card = _
        congr 1
      rw [hfilt_eq, ← hdyc_r]
      let F := Finset.univ.filter (fun r' : Fin n => dyc r' = false)
      have hF_eq : F = Finset.univ.filter (fun r' : Fin n => r'.1 < F.card) := by
        apply Finset.eq_of_subset_of_card_le
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hsub : Finset.univ.filter (fun b : Fin n => b.1 ≤ a.1) ⊆ F := by
            intro b hb
            simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            by_contra ht
            have := hdyc_mono b a (Finset.mem_filter.mp hb).2 (Bool.eq_true_of_not_eq_false ht)
            rw [this] at ha; contradiction
          have hle := Finset.card_le_card hsub
          have heq : (Finset.univ.filter (fun b : Fin n => b.1 ≤ a.1)).card = a.1 + 1 := by
            refine Finset.card_eq_of_bijective (fun i hi => ⟨i, by have := a.isLt; omega⟩)
              (fun b hb => ⟨b.1, by have := (Finset.mem_filter.mp hb).2; omega, rfl⟩)
              (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩)
              (fun i j _ _ h => congrArg Fin.val h)
          omega
        · have heq : (Finset.univ.filter (fun r' : Fin n => r'.1 < F.card)).card = F.card := by
            have hle : F.card ≤ n := by simpa using Finset.card_le_univ F
            refine Finset.card_eq_of_bijective (fun i hi => ⟨i, by omega⟩)
              (fun b hb => ⟨b.1, (Finset.mem_filter.mp hb).2, rfl⟩)
              (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
              (fun i j _ _ h => congrArg Fin.val h)
          omega
      have hrF : dyc r = false ↔ r.1 < F.card := by
        have := Finset.ext_iff.mp hF_eq r
        simpa [F] using this
      cases hdv : dyc r
      · exact decide_eq_false (not_le.mpr (hrF.mp hdv))
      · have : ¬ r.1 < F.card := fun h => by rw [hdv] at hrF; exact absurd (hrF.mpr h) (by decide)
        exact decide_eq_true (not_lt.mp this)
    · -- `dx` matches by horizontal constancy around the cylinder
      have hmem_c : ∀ c' : Fin n, ∃ q' ∈ S, blockOf hn0 q' = (r, c') := fun c' =>
        Finset.mem_image.mp (himg.symm ▸ Finset.mem_univ (r, c'))
      have huniq : ∀ {c' p₁ p₂}, p₁ ∈ S → p₂ ∈ S → blockOf hn0 p₁ = (r, c') →
          blockOf hn0 p₂ = (r, c') → p₁ = p₂ :=
        fun h1 h2 b1 b2 => hinj h1 h2 (b1.trans b2.symm)
      let dxc : Fin n → Bool := fun c' => decide ((Classical.choose (hmem_c c')).2.val % 2 = 1)
      have hdxc_step : ∀ c' : Fin n, dxc c' = true → dxc (cNext hn0 c') = true := by
        intro c' h1
        by_contra h2
        have h2f : dxc (cNext hn0 c') = false := Bool.eq_false_iff.mpr h2
        let p1 := Classical.choose (hmem_c c')
        let p2 := Classical.choose (hmem_c (cNext hn0 c'))
        have hp1 := Classical.choose_spec (hmem_c c')
        have hp2 := Classical.choose_spec (hmem_c (cNext hn0 c'))
        have hp1s := squareOf_blockOf hn0 p1; rw [hp1.2] at hp1s
        have hp2s := squareOf_blockOf hn0 p2; rw [hp2.2] at hp2s
        have hAtt : OMA.S_oeis_a137432.Attacks n p1 p2 := by
          rw [← hp1s, ← hp2s]
          refine ⟨?_, ?_, ?_⟩
          · intro heq
            have hc := congrArg (fun z => (blockOf hn0 z).2.1) heq
            rw [blockOf_squareOf, blockOf_squareOf] at hc
            simp only [cNext] at hc
            have := c'.isLt
            by_cases hlast : c'.1 + 1 < n
            · rw [Nat.mod_eq_of_lt hlast] at hc; omega
            · have : c'.1 + 1 = n := by omega
              rw [this, Nat.mod_self] at hc; omega
          · simp only [squareOf]
            cases decide (p1.1.1 % 2 = 1) <;> cases decide (p2.1.1 % 2 = 1) <;> dsimp <;> omega
          · exact (col_adj_iff hn c' (cNext hn0 c') _ _).mpr (Or.inr (Or.inl ⟨h1, h2f, rfl⟩))
        exact hno p1 hp1.1 p2 hp2.1 hAtt
      have hdxc_iter : ∀ (k : ℕ) (c' : Fin n), dxc c' = true → dxc ((cNextPerm hn0)^[k] c') = true := by
        intro k
        induction k with
        | zero => intro c' hc'; simpa using hc'
        | succ k ih =>
          intro c' hc'
          rw [Function.iterate_succ_apply']
          exact hdxc_step _ (ih c' hc')
      have hiter_val : ∀ (k : ℕ) (c' : Fin n), ((cNextPerm hn0)^[k] c').1 = (c'.1 + k) % n := by
        intro k
        induction k with
        | zero => intro c'; simp [Nat.mod_eq_of_lt c'.isLt]
        | succ k ih =>
          intro c'
          rw [Function.iterate_succ_apply']
          change ((((cNextPerm hn0)^[k] c').1 + 1) % n) = (c'.1 + (k + 1)) % n
          rw [ih c', Nat.mod_add_mod, add_assoc]
      have hdxc_const : dxc c = dxc ⟨0, hn0⟩ := by
        cases h0 : dxc ⟨0, hn0⟩
        · cases hc : dxc c
          · rfl
          · have h1 := hdxc_iter (n - c.1) c hc
            have hpos : ((cNextPerm hn0)^[n - c.1] c) = ⟨0, hn0⟩ := by
              ext; rw [hiter_val]; have := c.isLt
              rw [show c.1 + (n - c.1) = n by omega, Nat.mod_self]
            rw [hpos, h0] at h1; contradiction
        · have h1 := hdxc_iter c.1 ⟨0, hn0⟩ h0
          have hpos : ((cNextPerm hn0)^[c.1] ⟨0, hn0⟩) = c := by
            ext; rw [hiter_val]; simp [Nat.mod_eq_of_lt c.isLt]
          rwa [hpos] at h1
      have hdxc_q : dxc c = decide (q.2.val % 2 = 1) := by
        have hpq := huniq (Classical.choose_spec (hmem_c c)).1 hqS
          (Classical.choose_spec (hmem_c c)).2 hqb
        simp [dxc, hpq]
      change dxc ⟨0, hn0⟩ = decide (q.2.val % 2 = 1)
      rw [← hdxc_const, hdxc_q]
  · rintro ⟨⟨hFun, xFun⟩, hValid⟩
    apply Subtype.ext
    apply Prod.ext
    · funext c
      ext
      dsimp only [toHX, ofHX]
      have hex_im : ∀ r : Fin n, ∃ p ∈ Finset.univ.image (fun rc : Fin n × Fin n =>
          squareOf n rc.1 rc.2 (decide ((hFun rc.2).1 ≤ rc.1.1)) (xFun rc.1)),
          blockOf hn0 p = (r, c) := fun r =>
        ⟨squareOf n r c (decide ((hFun c).1 ≤ r.1)) (xFun r),
          Finset.mem_image_of_mem _ (Finset.mem_univ (r, c)), blockOf_squareOf hn0 _ _ _ _⟩
      have hfilt :
          (Finset.univ.filter (fun r : Fin n =>
            decide ((Classical.choose (hex_im r)).1.1 % 2 = 1) = false)) =
          Finset.univ.filter (fun r : Fin n => r.1 < (hFun c).1) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hspec := Classical.choose_spec (hex_im r)
        rcases Finset.mem_image.mp hspec.1 with ⟨⟨r', c'⟩, _, heq⟩
        have hblk := hspec.2
        rw [← heq, blockOf_squareOf] at hblk
        have hr' : r' = r := congrArg Prod.fst hblk
        have hc' : c' = c := congrArg Prod.snd hblk
        rw [hr', hc'] at heq
        rw [← heq]
        simp only [squareOf]
        by_cases hle : (hFun c).1 ≤ r.1
        · simp [hle, show (2 * r.1 + 1) % 2 = 1 by omega, not_lt.mpr hle]
        · simp [hle, show (2 * r.1) % 2 = 0 by omega, Nat.lt_of_not_ge hle]
      change (Finset.univ.filter (fun r : Fin n =>
        decide ((Classical.choose (hex_im r)).1.1 % 2 = 1) = false)).card = (hFun c).1
      rw [hfilt]
      have hle : (hFun c).1 ≤ n := Nat.lt_succ_iff.mp (hFun c).isLt
      refine Finset.card_eq_of_bijective (fun i hi => ⟨i, by omega⟩)
        (fun b hb => ⟨b.1, (Finset.mem_filter.mp hb).2, rfl⟩)
        (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        (fun i j _ _ h => congrArg Fin.val h)
    · funext r
      dsimp only [toHX, ofHX]
      let c0 : Fin n := ⟨0, hn0⟩
      have hex_im0 : ∃ p ∈ Finset.univ.image (fun rc : Fin n × Fin n =>
          squareOf n rc.1 rc.2 (decide ((hFun rc.2).1 ≤ rc.1.1)) (xFun rc.1)),
          blockOf hn0 p = (r, c0) :=
        ⟨squareOf n r c0 (decide ((hFun c0).1 ≤ r.1)) (xFun r),
          Finset.mem_image_of_mem _ (Finset.mem_univ (r, c0)), blockOf_squareOf hn0 _ _ _ _⟩
      have hspec := Classical.choose_spec hex_im0
      rcases Finset.mem_image.mp hspec.1 with ⟨⟨r', c'⟩, _, heq⟩
      have hblk := hspec.2
      rw [← heq, blockOf_squareOf] at hblk
      have hr' : r' = r := congrArg Prod.fst hblk
      have hc' : c' = c0 := congrArg Prod.snd hblk
      rw [hr', hc'] at heq
      change decide ((Classical.choose hex_im0).2.val % 2 = 1) = xFun r
      rw [← heq, squareOf_val_col hn0]
      cases xFun r <;> simp

/-! ### Section 2: Decomposition into `Main`, `Const`, and `Err` -/

private def minH {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) : ℕ :=
  (Finset.univ.image (fun c : Fin n => (h c).1)).min'
    (Finset.Nonempty.image ⟨⟨0, hn⟩, Finset.mem_univ _⟩ _)

private def maxH {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) : ℕ :=
  (Finset.univ.image (fun c : Fin n => (h c).1)).max'
    (Finset.Nonempty.image ⟨⟨0, hn⟩, Finset.mem_univ _⟩ _)

private lemma minH_le {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) (c : Fin n) :
    minH hn h ≤ (h c).1 :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ c))

private lemma le_maxH {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) (c : Fin n) :
    (h c).1 ≤ maxH hn h :=
  Finset.le_max' (Finset.univ.image (fun c : Fin n => (h c).1)) (h c).1
    (Finset.mem_image_of_mem _ (Finset.mem_univ c))

private lemma minH_le_maxH {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) :
    minH hn h ≤ maxH hn h :=
  le_trans (minH_le hn h ⟨0, hn⟩) (le_maxH hn h ⟨0, hn⟩)

private lemma maxH_le_n {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) :
    maxH hn h ≤ n := by
  have hmem := Finset.max'_mem (Finset.univ.image (fun c : Fin n => (h c).1))
    (Finset.Nonempty.image ⟨⟨0, hn⟩, Finset.mem_univ _⟩ _)
  rcases Finset.mem_image.mp hmem with ⟨c, _, hc⟩
  unfold maxH
  rw [← hc]
  exact Nat.lt_succ_iff.mp (h c).isLt

private lemma exists_eq_minH {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) :
    ∃ c : Fin n, (h c).1 = minH hn h := by
  have hmem := Finset.min'_mem (Finset.univ.image (fun c : Fin n => (h c).1))
    (Finset.Nonempty.image ⟨⟨0, hn⟩, Finset.mem_univ _⟩ _)
  rcases Finset.mem_image.mp hmem with ⟨c, _, hc⟩
  exact ⟨c, hc⟩

private lemma exists_eq_maxH {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) :
    ∃ c : Fin n, (h c).1 = maxH hn h := by
  have hmem := Finset.max'_mem (Finset.univ.image (fun c : Fin n => (h c).1))
    (Finset.Nonempty.image ⟨⟨0, hn⟩, Finset.mem_univ _⟩ _)
  rcases Finset.mem_image.mp hmem with ⟨c, _, hc⟩
  exact ⟨c, hc⟩

/-- Interior values in `(minH h, maxH h)` never strictly jumped over in the forward cycle direction. -/
private def Uset {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) : Finset ℕ :=
  (Finset.Ioo (minH hn h) (maxH hn h)).filter
    (fun m => ¬ ∃ c : Fin n, (h c).1 < m ∧ m < (h (cNext hn c)).1)

/-- Interior values in `(minH h, maxH h)` never strictly jumped over in the backward cycle direction. -/
private def Dset {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) : Finset ℕ :=
  (Finset.Ioo (minH hn h) (maxH hn h)).filter
    (fun m => ¬ ∃ c : Fin n, (h (cNext hn c)).1 < m ∧ m < (h c).1)

private def revFin {n : ℕ} (_hn : 0 < n) (c : Fin n) : Fin n :=
  ⟨(n - 1 - c.1), by have := c.isLt; omega⟩

private lemma revFin_invol {n : ℕ} (hn : 0 < n) (c : Fin n) :
    revFin hn (revFin hn c) = c := by
  ext; simp only [revFin]; have := c.isLt; omega

private lemma cNext_revFin {n : ℕ} (hn : 0 < n) (c : Fin n) :
    cNext hn (revFin hn c) = revFin hn (cPrev hn c) := by
  ext
  simp only [cNext, revFin, cPrev]
  have hc := c.isLt
  by_cases h0 : c.1 = 0
  · simp only [h0, Nat.sub_zero, zero_add]
    rw [show n - 1 + 1 = n by omega, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
    omega
  · have h1 : (c.1 + n - 1) % n = c.1 - 1 := by
      rw [show c.1 + n - 1 = (c.1 - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1, Nat.mod_eq_of_lt (by omega)]
    omega

private lemma minH_comp_perm {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) : minH hn (h ∘ σ) = minH hn h := by
  unfold minH
  congr 1
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun ⟨c, hc⟩ => ⟨σ c, hc⟩, fun ⟨c, hc⟩ => ⟨σ.symm c, by simpa using hc⟩⟩

private lemma maxH_comp_perm {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) : maxH hn (h ∘ σ) = maxH hn h := by
  unfold maxH
  congr 1
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun ⟨c, hc⟩ => ⟨σ c, hc⟩, fun ⟨c, hc⟩ => ⟨σ.symm c, by simpa using hc⟩⟩

private lemma Dset_eq_Uset_rev {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) :
    Dset hn h = Uset hn (fun c => h (revFin hn c)) := by
  let revPerm : Equiv.Perm (Fin n) :=
    { toFun := revFin hn, invFun := revFin hn, left_inv := revFin_invol hn, right_inv := revFin_invol hn }
  have hmin : minH hn (fun c => h (revFin hn c)) = minH hn h := minH_comp_perm hn h revPerm
  have hmax : maxH hn (fun c => h (revFin hn c)) = maxH hn h := maxH_comp_perm hn h revPerm
  unfold Dset Uset
  rw [hmin, hmax]
  ext m
  simp only [Finset.mem_filter]
  refine and_congr_right fun _ => not_congr ?_
  constructor
  · rintro ⟨c, h1, h2⟩
    refine ⟨revFin hn (cNext hn c), ?_⟩
    rw [revFin_invol, cNext_revFin, cPrev_cNext, revFin_invol]
    exact ⟨h1, h2⟩
  · rintro ⟨c, h1, h2⟩
    refine ⟨cPrev hn (revFin hn c), ?_⟩
    rw [cNext_cPrev]
    have hrev : revFin hn (cNext hn c) = cPrev hn (revFin hn c) := by
      have := cNext_revFin hn (revFin hn (cNext hn c))
      rw [revFin_invol] at this
      have h' := congrArg (cPrev hn) (cNext_revFin hn (revFin hn c))
      rw [revFin_invol, cPrev_cNext] at h'
      -- directly check via cNext
      apply (cNextPerm hn).injective
      change cNext hn (revFin hn (cNext hn c)) = cNext hn (cPrev hn (revFin hn c))
      rw [cNext_revFin, cPrev_cNext, cNext_cPrev]
    rw [← hrev]
    exact ⟨h1, h2⟩

private noncomputable def mainCount (n : ℕ) (hn : 0 < n) : ℕ :=
  ∑ h ∈ (Finset.univ : Finset (Fin n → Fin (n + 1))).filter (fun h => minH hn h < maxH hn h),
    2 * 2 ^ (minH hn h + (n - maxH hn h))

private noncomputable def errCount (n : ℕ) (hn : 0 < n) : ℕ :=
  ∑ h ∈ (Finset.univ : Finset (Fin n → Fin (n + 1))).filter (fun h => minH hn h < maxH hn h),
    2 ^ (minH hn h + (n - maxH hn h)) * (4 ^ (Uset hn h).card - 1)

private lemma card_validX_lower {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1))
    (hnc : minH hn h < maxH hn h) :
    2 * 2 ^ (minH hn h + (n - maxH hn h)) ≤
      (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn h x)).card := by
  classical
  have hmax_le : maxH hn h ≤ n := maxH_le_n hn h
  let Dom := Bool × (Fin (minH hn h) → Bool) × (Fin (n - maxH hn h) → Bool)
  let mkX : Dom → (Fin n → Bool) := fun ⟨b, fL, fR⟩ i =>
    if h1 : i.1 < minH hn h then fL ⟨i.1, h1⟩
    else if h2 : maxH hn h ≤ i.1 then fR ⟨i.1 - maxH hn h, by have := i.isLt; omega⟩
    else b
  have hinj : Function.Injective mkX := by
    rintro ⟨b₁, fL₁, fR₁⟩ ⟨b₂, fL₂, fR₂⟩ heq
    have hb : b₁ = b₂ := by
      have := congrFun heq ⟨minH hn h, by omega⟩
      simp only [mkX, lt_irrefl, dite_false, not_le.mpr hnc] at this
      exact this
    have hfL : fL₁ = fL₂ := by
      funext ⟨i, hi⟩
      have := congrFun heq ⟨i, by omega⟩
      simpa [mkX, hi] using this
    have hfR : fR₁ = fR₂ := by
      funext ⟨i, hi⟩
      have := congrFun heq ⟨maxH hn h + i, by omega⟩
      have h1 : ¬ maxH hn h + i < minH hn h := by omega
      have h2 : maxH hn h ≤ maxH hn h + i := by omega
      simp only [mkX, dif_neg h1, dif_pos h2, Nat.add_sub_cancel_left] at this
      exact this
    simp [hb, hfL, hfR]
  have hmem : ∀ d : Dom, mkX d ∈ Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn h x) := by
    rintro ⟨b, fL, fR⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro c r hr
    constructor
    · rintro ⟨hx1, hx2⟩ ⟨hh1, hh2⟩
      have hm1 : minH hn h ≤ r := le_trans (minH_le hn h c) hh1
      have hm2 : r + 2 ≤ maxH hn h := le_trans hh2 (le_maxH hn h (cNext hn c))
      simp only [mkX, dif_neg (by omega : ¬ r < minH hn h),
        dif_neg (by omega : ¬ maxH hn h ≤ r),
        dif_neg (by omega : ¬ r + 1 < minH hn h),
        dif_neg (by omega : ¬ maxH hn h ≤ r + 1)] at hx1 hx2
      rw [hx1] at hx2; contradiction
    · rintro ⟨hx1, hx2⟩ ⟨hh1, hh2⟩
      have hm1 : minH hn h ≤ r := le_trans (minH_le hn h (cNext hn c)) hh1
      have hm2 : r + 2 ≤ maxH hn h := le_trans hh2 (le_maxH hn h c)
      simp only [mkX, dif_neg (by omega : ¬ r < minH hn h),
        dif_neg (by omega : ¬ maxH hn h ≤ r),
        dif_neg (by omega : ¬ r + 1 < minH hn h),
        dif_neg (by omega : ¬ maxH hn h ≤ r + 1)] at hx1 hx2
      rw [hx1] at hx2; contradiction
  calc
    2 * 2 ^ (minH hn h + (n - maxH hn h))
        = Fintype.card Dom := by
          simp [Dom, pow_add]
    _ = (Finset.univ.image mkX).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    _ ≤ (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn h x)).card := by
          refine Finset.card_le_card ?_
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨d, _, rfl⟩
          exact hmem d

private lemma card_validX_upper {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1))
    (_hnc : minH hn h < maxH hn h) :
    (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn h x)).card ≤
      2 * 2 ^ (minH hn h + (n - maxH hn h) + (Uset hn h).card + (Dset hn h).card) := by
  classical
  let FreeIdx : Finset (Fin (n - 1)) :=
    Finset.univ.filter (fun r =>
      r.1 < minH hn h ∨ maxH hn h ≤ r.1 + 1 ∨ (r.1 + 1) ∈ Uset hn h ∨ (r.1 + 1) ∈ Dset hn h)
  have hFree_card : FreeIdx.card ≤
      minH hn h + (n - maxH hn h) + (Uset hn h).card + (Dset hn h).card := by
    let F1 := (Finset.univ : Finset (Fin (n - 1))).filter (fun r => r.1 < minH hn h)
    let F2 := (Finset.univ : Finset (Fin (n - 1))).filter (fun r => maxH hn h ≤ r.1 + 1)
    let F3 := (Finset.univ : Finset (Fin (n - 1))).filter (fun r => r.1 + 1 ∈ Uset hn h)
    let F4 := (Finset.univ : Finset (Fin (n - 1))).filter (fun r => r.1 + 1 ∈ Dset hn h)
    have hsub : FreeIdx ⊆ ((F1 ∪ F2) ∪ F3) ∪ F4 := by
      intro r hr
      simp only [FreeIdx, F1, F2, F3, F4, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      tauto
    have h1 : F1.card ≤ minH hn h := by
      have hsub' : F1.image Fin.val ⊆ Finset.range (minH hn h) := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
      simpa [Finset.card_image_of_injective _ Fin.val_injective] using Finset.card_le_card hsub'
    have h2 : F2.card ≤ n - maxH hn h := by
      have hsub' : F2.image (fun r : Fin (n - 1) => r.1 + 1) ⊆ Finset.Ico (maxH hn h) n := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hr).2, by have := r.isLt; omega⟩
      have hinj : Function.Injective (fun r : Fin (n - 1) => r.1 + 1) :=
        fun a b hab => Fin.ext (by dsimp at hab; omega)
      simpa [Finset.card_image_of_injective _ hinj, Nat.card_Ico] using Finset.card_le_card hsub'
    have h3 : F3.card ≤ (Uset hn h).card := by
      have hsub' : F3.image (fun r : Fin (n - 1) => r.1 + 1) ⊆ Uset hn h := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
        exact (Finset.mem_filter.mp hr).2
      have hinj : Function.Injective (fun r : Fin (n - 1) => r.1 + 1) :=
        fun a b hab => Fin.ext (by dsimp at hab; omega)
      simpa [Finset.card_image_of_injective _ hinj] using Finset.card_le_card hsub'
    have h4 : F4.card ≤ (Dset hn h).card := by
      have hsub' : F4.image (fun r : Fin (n - 1) => r.1 + 1) ⊆ Dset hn h := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
        exact (Finset.mem_filter.mp hr).2
      have hinj : Function.Injective (fun r : Fin (n - 1) => r.1 + 1) :=
        fun a b hab => Fin.ext (by dsimp at hab; omega)
      simpa [Finset.card_image_of_injective _ hinj] using Finset.card_le_card hsub'
    have hU := Finset.card_le_card hsub
    have hU1 := Finset.card_union_le ((F1 ∪ F2) ∪ F3) F4
    have hU2 := Finset.card_union_le (F1 ∪ F2) F3
    have hU3 := Finset.card_union_le F1 F2
    omega
  -- Map valid `x` injectively into `Bool × (FreeIdx → Bool)`
  let enc : (Fin n → Bool) → Bool × (FreeIdx → Bool) := fun x =>
    (x ⟨0, hn⟩, fun r => x ⟨r.1.1 + 1, by have := r.1.isLt; omega⟩)
  have hstep_eq : ∀ {x : Fin n → Bool}, ValidHX hn h x →
      ∀ (r : Fin (n - 1)), r ∉ FreeIdx →
        x ⟨r.1, by have := r.isLt; omega⟩ = x ⟨r.1 + 1, by have := r.isLt; omega⟩ := by
    intro x hx r hrNot
    simp only [FreeIdx, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hrNot
    rcases hrNot with ⟨h1, h2, h3, h4⟩
    have hIoo : r.1 + 1 ∈ Finset.Ioo (minH hn h) (maxH hn h) :=
      Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
    have hUp : ∃ c : Fin n, (h c).1 < r.1 + 1 ∧ r.1 + 1 < (h (cNext hn c)).1 := by
      by_contra hno
      exact h3 (Finset.mem_filter.mpr ⟨hIoo, hno⟩)
    have hDn : ∃ c : Fin n, (h (cNext hn c)).1 < r.1 + 1 ∧ r.1 + 1 < (h c).1 := by
      by_contra hno
      exact h4 (Finset.mem_filter.mpr ⟨hIoo, hno⟩)
    have hrLt : r.1 + 1 < n := by have := r.isLt; omega
    cases hA : x ⟨r.1, by omega⟩ <;> cases hB : x ⟨r.1 + 1, hrLt⟩
    · rfl
    · rcases hDn with ⟨c, hc1, hc2⟩
      exact absurd ⟨by omega, by omega⟩ ((hx c r.1 hrLt).2 ⟨hA, hB⟩)
    · rcases hUp with ⟨c, hc1, hc2⟩
      exact absurd ⟨by omega, by omega⟩ ((hx c r.1 hrLt).1 ⟨hA, hB⟩)
    · rfl
  have hinj : Set.InjOn enc ((Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn h x)) : Set _) := by
    intro x₁ hx₁ x₂ hx₂ heq
    have hv₁ := (Finset.mem_filter.mp hx₁).2
    have hv₂ := (Finset.mem_filter.mp hx₂).2
    have h0 : x₁ ⟨0, hn⟩ = x₂ ⟨0, hn⟩ := congrArg Prod.fst heq
    have hF : ∀ r : FreeIdx, x₁ ⟨r.1.1 + 1, by have := r.1.isLt; omega⟩ =
        x₂ ⟨r.1.1 + 1, by have := r.1.isLt; omega⟩ := fun r =>
      congrFun (congrArg Prod.snd heq) r
    funext ⟨k, hk⟩
    induction k with
    | zero => exact h0
    | succ k ih =>
      let r : Fin (n - 1) := ⟨k, by omega⟩
      by_cases hr : r ∈ FreeIdx
      · exact hF ⟨r, hr⟩
      · rw [← hstep_eq hv₁ r hr, ← hstep_eq hv₂ r hr]
        exact ih (by omega)
  calc
    (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn h x)).card
        = ((Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn h x)).image enc).card :=
          (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Bool × (FreeIdx → Bool)) := Finset.card_le_univ _
    _ = 2 * 2 ^ FreeIdx.card := by simp
    _ ≤ 2 * 2 ^ (minH hn h + (n - maxH hn h) + (Uset hn h).card + (Dset hn h).card) :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) hFree_card)

private lemma a_bounds {n : ℕ} (hn : 3 ≤ n) :
    mainCount n (by omega) ≤ OMA.S_oeis_a137432.a n ∧
    OMA.S_oeis_a137432.a n ≤
      mainCount n (by omega) + (n + 1) * 2 ^ n + 2 * errCount n (by omega) := by
  classical
  have hn0 : 0 < n := by omega
  rw [card_a_eq_card_validHX hn]
  -- Rewrite card of valid `(h, x)` as sum over `h` of valid `x`
  have hSumH :
      Fintype.card { p : (Fin n → Fin (n + 1)) × (Fin n → Bool) // ValidHX hn0 p.1 p.2 } =
        ∑ h : Fin n → Fin (n + 1), (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn0 h x)).card := by
    let e : { p : (Fin n → Fin (n + 1)) × (Fin n → Bool) // ValidHX hn0 p.1 p.2 } ≃
        Σ h : Fin n → Fin (n + 1), { x : Fin n → Bool // ValidHX hn0 h x } :=
      { toFun := fun ⟨⟨h, x⟩, hv⟩ => ⟨h, ⟨x, hv⟩⟩
        invFun := fun ⟨h, ⟨x, hv⟩⟩ => ⟨⟨h, x⟩, hv⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Fintype.card_subtype]
  rw [hSumH]
  -- Split into non-constant (`minH < maxH`) and constant (`minH = maxH`)
  let NC := (Finset.univ : Finset (Fin n → Fin (n + 1))).filter (fun h => minH hn0 h < maxH hn0 h)
  let C := (Finset.univ : Finset (Fin n → Fin (n + 1))).filter (fun h => ¬ minH hn0 h < maxH hn0 h)
  have hSplit :
      (∑ h : Fin n → Fin (n + 1), (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn0 h x)).card) =
        (∑ h ∈ NC, (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn0 h x)).card) +
        (∑ h ∈ C, (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn0 h x)).card) := by
    simpa [NC, C] using (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun h : Fin n → Fin (n + 1) => minH hn0 h < maxH hn0 h) _).symm
  rw [hSplit]
  constructor
  · calc
      mainCount n hn0
          ≤ ∑ h ∈ NC, (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn0 h x)).card := by
            refine Finset.sum_le_sum fun h hh => card_validX_lower hn0 h (Finset.mem_filter.mp hh).2
      _ ≤ _ := Nat.le_add_right _ _
  · -- Bound constant `h` sum by `(n + 1) * 2 ^ n`
    have hC_card : C.card ≤ n + 1 := by
      have hinj : Set.InjOn (fun h : Fin n → Fin (n + 1) => h ⟨0, hn0⟩) (C : Set _) := by
        intro h₁ hh₁ h₂ hh₂ heq
        have h1eq : minH hn0 h₁ = maxH hn0 h₁ :=
          le_antisymm (minH_le_maxH hn0 h₁) (not_lt.mp (Finset.mem_filter.mp hh₁).2)
        have h2eq : minH hn0 h₂ = maxH hn0 h₂ :=
          le_antisymm (minH_le_maxH hn0 h₂) (not_lt.mp (Finset.mem_filter.mp hh₂).2)
        funext c
        apply Fin.ext
        have a1 := minH_le hn0 h₁ c; have b1 := le_maxH hn0 h₁ c
        have a2 := minH_le hn0 h₁ ⟨0, hn0⟩; have b2 := le_maxH hn0 h₁ ⟨0, hn0⟩
        have a3 := minH_le hn0 h₂ c; have b3 := le_maxH hn0 h₂ c
        have a4 := minH_le hn0 h₂ ⟨0, hn0⟩; have b4 := le_maxH hn0 h₂ ⟨0, hn0⟩
        have h0 : (h₁ ⟨0, hn0⟩).1 = (h₂ ⟨0, hn0⟩).1 := congrArg Fin.val heq
        omega
      calc
        C.card = (C.image (fun h : Fin n → Fin (n + 1) => h ⟨0, hn0⟩)).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ Fintype.card (Fin (n + 1)) := Finset.card_le_univ _
        _ = n + 1 := Fintype.card_fin _
    have hC_sum :
        (∑ h ∈ C, (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn0 h x)).card) ≤
          (n + 1) * 2 ^ n := by
      calc
        (∑ h ∈ C, (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn0 h x)).card)
            ≤ ∑ _h ∈ C, 2 ^ n := by
              refine Finset.sum_le_sum fun h _ => ?_
              calc
                (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn0 h x)).card
                    ≤ Fintype.card (Fin n → Bool) := Finset.card_le_univ _
                _ = 2 ^ n := by simp
        _ = C.card * 2 ^ n := by simp
        _ ≤ (n + 1) * 2 ^ n := Nat.mul_le_mul_right _ hC_card
    -- Bound non-constant `h` sum using `2 * 2^(u+d) ≤ 4^u + 4^d` and cycle reversal `D ↔ U`
    have hAMGM : ∀ u d : ℕ, 2 * 2 ^ (u + d) ≤ 2 + (4 ^ u - 1) + (4 ^ d - 1) := by
      intro u d
      have hu : 1 ≤ 4 ^ u := Nat.one_le_pow u 4 (by omega)
      have hd : 1 ≤ 4 ^ d := Nat.one_le_pow d 4 (by omega)
      have hsq : 2 * (2 ^ u * 2 ^ d) ≤ (2 ^ u) ^ 2 + (2 ^ d) ^ 2 := by
        zify
        nlinarith [sq_nonneg ((2 ^ u : ℤ) - (2 ^ d : ℤ))]
      have h4u : (2 ^ u) ^ 2 = 4 ^ u := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h4d : (2 ^ d) ^ 2 = 4 ^ d := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h4u, h4d] at hsq
      rw [pow_add]
      omega
    have hNC_sum :
        (∑ h ∈ NC, (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn0 h x)).card) ≤
          mainCount n hn0 + 2 * errCount n hn0 := by
      have hD_eq_U :
          (∑ h ∈ NC, 2 ^ (minH hn0 h + (n - maxH hn0 h)) * (4 ^ (Dset hn0 h).card - 1)) =
            errCount n hn0 := by
        let revPerm : Equiv.Perm (Fin n) :=
          { toFun := revFin hn0, invFun := revFin hn0,
            left_inv := revFin_invol hn0, right_inv := revFin_invol hn0 }
        unfold errCount
        refine Finset.sum_bij (fun h _ => h ∘ revPerm) ?_ ?_ ?_ ?_
        · intro h hh
          have hlt := (Finset.mem_filter.mp hh).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rwa [minH_comp_perm hn0 h revPerm, maxH_comp_perm hn0 h revPerm]
        · intro h₁ _ h₂ _ heq
          funext c
          have := congrFun heq (revFin hn0 c)
          simpa [revPerm, revFin_invol] using this
        · intro h hh
          refine ⟨h ∘ revPerm, ?_, ?_⟩
          · have hlt := (Finset.mem_filter.mp hh).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rwa [minH_comp_perm hn0 h revPerm, maxH_comp_perm hn0 h revPerm]
          · funext c; simp [revPerm, revFin_invol]
        · intro h _
          rw [minH_comp_perm hn0 h revPerm, maxH_comp_perm hn0 h revPerm, Dset_eq_Uset_rev]
          rfl
      calc
        (∑ h ∈ NC, (Finset.univ.filter (fun x : Fin n → Bool => ValidHX hn0 h x)).card)
            ≤ ∑ h ∈ NC, 2 * 2 ^ (minH hn0 h + (n - maxH hn0 h) + (Uset hn0 h).card + (Dset hn0 h).card) :=
              Finset.sum_le_sum fun h hh => card_validX_upper hn0 h (Finset.mem_filter.mp hh).2
        _ ≤ ∑ h ∈ NC, (2 * 2 ^ (minH hn0 h + (n - maxH hn0 h)) +
              2 ^ (minH hn0 h + (n - maxH hn0 h)) * (4 ^ (Uset hn0 h).card - 1) +
              2 ^ (minH hn0 h + (n - maxH hn0 h)) * (4 ^ (Dset hn0 h).card - 1)) := by
              refine Finset.sum_le_sum fun h _ => ?_
              have h1 := hAMGM (Uset hn0 h).card (Dset hn0 h).card
              have hpow : 2 * 2 ^ (minH hn0 h + (n - maxH hn0 h) + (Uset hn0 h).card + (Dset hn0 h).card) =
                  2 ^ (minH hn0 h + (n - maxH hn0 h)) * (2 * 2 ^ ((Uset hn0 h).card + (Dset hn0 h).card)) := by
                rw [show minH hn0 h + (n - maxH hn0 h) + (Uset hn0 h).card + (Dset hn0 h).card =
                  (minH hn0 h + (n - maxH hn0 h)) + ((Uset hn0 h).card + (Dset hn0 h).card) by omega,
                  pow_add]
                ring
              rw [hpow]
              calc
                2 ^ (minH hn0 h + (n - maxH hn0 h)) * (2 * 2 ^ ((Uset hn0 h).card + (Dset hn0 h).card))
                    ≤ 2 ^ (minH hn0 h + (n - maxH hn0 h)) *
                        (2 + (4 ^ (Uset hn0 h).card - 1) + (4 ^ (Dset hn0 h).card - 1)) :=
                      Nat.mul_le_mul_left _ h1
                _ = _ := by ring
        _ = mainCount n hn0 + errCount n hn0 + errCount n hn0 := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hD_eq_U]
              rfl
        _ = mainCount n hn0 + 2 * errCount n hn0 := by ring
    omega

/-! ### Section 3: Constrained `n`-cycle counting bound -/

private def IsSingleCycle {n : ℕ} (f : Equiv.Perm (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → ∃ i ∈ S, f i ∉ S

private def succPerm' {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) where
  toFun i := σ (cNext hn (σ.symm i))
  invFun i := σ (cPrev hn (σ.symm i))
  left_inv i := by simp [cPrev_cNext]
  right_inv i := by simp [cNext_cPrev]

private lemma isSingleCycle_succPerm' {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    IsSingleCycle (succPerm' hn σ) := by
  intro S ⟨x₀, hx₀⟩ hne
  by_contra hno
  push Not at hno
  have hiter : ∀ k : ℕ, (succPerm' hn σ)^[k] x₀ ∈ S := by
    intro k
    induction k with
    | zero => simpa using hx₀
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hno _ ih
  have hiter_eq : ∀ k : ℕ, (succPerm' hn σ)^[k] x₀ = σ ((cNextPerm hn)^[k] (σ.symm x₀)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      simp [succPerm', cNextPerm]
  have hiter_val : ∀ (k : ℕ) (c : Fin n), ((cNextPerm hn)^[k] c).1 = (c.1 + k) % n := by
    intro k
    induction k with
    | zero => intro c; simp [Nat.mod_eq_of_lt c.isLt]
    | succ k ih =>
      intro c
      rw [Function.iterate_succ_apply']
      change ((((cNextPerm hn)^[k] c).1 + 1) % n) = (c.1 + (k + 1)) % n
      rw [ih c, Nat.mod_add_mod, add_assoc]
  apply hne
  apply Finset.eq_univ_iff_forall.mpr
  intro y
  let a := (σ.symm x₀).1
  let b := (σ.symm y).1
  let k := (b + n - a) % n
  have hk : ((cNextPerm hn)^[k] (σ.symm x₀)) = σ.symm y := by
    ext
    rw [hiter_val]
    have ha := (σ.symm x₀).isLt
    have hb := (σ.symm y).isLt
    change (a + (b + n - a) % n) % n = b
    rw [Nat.add_mod_mod]
    have hsum : a + (b + n - a) = b + n := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  have hmem := hiter k
  rw [hiter_eq k, hk, Equiv.apply_symm_apply] at hmem
  exact hmem

private lemma succPerm'_inj_with_zero {n : ℕ} (hn : 0 < n) (σ₁ σ₂ : Equiv.Perm (Fin n))
    (h0 : σ₁ ⟨0, hn⟩ = σ₂ ⟨0, hn⟩) (hf : succPerm' hn σ₁ = succPerm' hn σ₂) :
    σ₁ = σ₂ := by
  ext ⟨k, hk⟩
  induction k with
  | zero => exact congrArg Fin.val h0
  | succ k ih =>
    have hprev : σ₁ ⟨k, by omega⟩ = σ₂ ⟨k, by omega⟩ := Fin.ext (ih (by omega))
    have hnext : cNext hn ⟨k, by omega⟩ = ⟨k + 1, hk⟩ := by
      ext; simp [cNext, Nat.mod_eq_of_lt hk]
    have h1 : σ₁ ⟨k + 1, hk⟩ = succPerm' hn σ₁ (σ₁ ⟨k, by omega⟩) := by
      simp [succPerm', hnext]
    have h2 : σ₂ ⟨k + 1, hk⟩ = succPerm' hn σ₂ (σ₂ ⟨k, by omega⟩) := by
      simp [succPerm', hnext]
    rw [h1, h2, hf, hprev]

/-- Backtrack from `x` along `f.symm` within `{0, ..., m - 1}` for `fuel` steps. -/
private def backPath {n : ℕ} (f : Equiv.Perm (Fin n)) (m : ℕ) : ℕ → Fin n → Fin n
  | 0, x => x
  | fuel + 1, x => if (f.symm x).1 < m then backPath f m fuel (f.symm x) else x

private lemma backPath_eq_of_agree {n : ℕ} {f₁ f₂ : Equiv.Perm (Fin n)} {m : ℕ}
    (hagree : ∀ j : Fin n, j.1 < m → f₁ j = f₂ j) :
    ∀ fuel x, backPath f₁ m fuel x = backPath f₂ m fuel x := by
  intro fuel
  induction fuel with
  | zero => intro x; rfl
  | succ fuel ih =>
    intro x
    simp only [backPath]
    by_cases h1 : (f₁.symm x).1 < m
    · have h2 : f₂ (f₁.symm x) = x := by rw [← hagree _ h1, Equiv.apply_symm_apply]
      have hsym : f₂.symm x = f₁.symm x := by
        apply f₂.injective; rw [Equiv.apply_symm_apply, h2]
      rw [if_pos h1, hsym, if_pos h1]
      exact ih (f₁.symm x)
    · have h2 : ¬ (f₂.symm x).1 < m := by
        intro hlt
        have h1' : f₁ (f₂.symm x) = x := by rw [hagree _ hlt, Equiv.apply_symm_apply]
        have hsym : f₁.symm x = f₂.symm x := by
          apply f₁.injective; rw [Equiv.apply_symm_apply, h1']
        rw [hsym] at h1
        exact h1 hlt
      rw [if_neg h1, if_neg h2]

private lemma backPath_le {n : ℕ} (f : Equiv.Perm (Fin n)) (m : ℕ) :
    ∀ fuel x, x.1 ≤ m → (backPath f m fuel x).1 ≤ m := by
  intro fuel
  induction fuel with
  | zero => intro x hx; exact hx
  | succ fuel ih =>
    intro x hx
    simp only [backPath]
    split_ifs with h
    · exact ih _ (by omega)
    · exact hx

/-- For any single cycle `f` and `m < n - 1`, `s = backPath f m m ⟨m, _⟩` satisfies
`s ≤ m`, `(f.symm s).1 ≥ m`, and `f ⟨m, _⟩ ≠ s`. -/
private lemma backPath_singleCycle {n : ℕ} {f : Equiv.Perm (Fin n)} (hf : IsSingleCycle f)
    {m : ℕ} (hm : m + 1 < n) :
    let s := backPath f m m ⟨m, by omega⟩
    s.1 ≤ m ∧ m ≤ (f.symm s).1 ∧ f ⟨m, by omega⟩ ≠ s := by
  let v : ℕ → Fin n := fun k => backPath f m k ⟨m, by omega⟩
  have hv_le : ∀ k, (v k).1 ≤ m := fun k => backPath_le f m k ⟨m, by omega⟩ le_rfl
  -- Prove that if `(f.symm (v k)).1 < m` then `v (k + 1) = f.symm (v k)` and `v` hits a fixed point in ≤ m steps
  have hv_step : ∀ k, v (k + 1) = if (f.symm (v k)).1 < m then f.symm (v k) else v k := by
    intro k
    have hgen : ∀ fuel x, backPath f m (fuel + 1) x =
        if (f.symm (backPath f m fuel x)).1 < m then f.symm (backPath f m fuel x) else backPath f m fuel x := by
      intro fuel
      induction fuel with
      | zero => intro x; rfl
      | succ fuel ih =>
        intro x
        change (if (f.symm x).1 < m then backPath f m (fuel + 1) (f.symm x) else x) = _
        by_cases hx : (f.symm x).1 < m
        · simp only [backPath, if_pos hx]
          exact ih (f.symm x)
        · simp only [backPath, if_neg hx]
    exact hgen k ⟨m, by omega⟩
  have hstop_exists : ∃ k ≤ m, m ≤ (f.symm (v k)).1 := by
    by_contra hno
    push Not at hno
    -- If it never stops for k ≤ m, all m+1 points v 0, ..., v m lie in `{0..m}` (size m+1)
    -- Wait: v 0 = m, and v (k+1) = f.symm (v k) < m for all k ≤ m, so v 1, ..., v (m+1) all lie in `{0..m-1}` (size m)!
    -- By pigeonhole among `{1, ..., m+1}` (m+1 elements) into `Fin m` (m elements), two are equal!
    have hlt_all : ∀ k ≤ m, (f.symm (v k)).1 < m := fun k hk => hno k hk
    have hv_eq_symm : ∀ k ≤ m, v (k + 1) = f.symm (v k) := by
      intro k hk; rw [hv_step k, if_pos (hlt_all k hk)]
    have hval_lt : ∀ i : Fin (m + 1), (v (i.1 + 1)).1 < m := by
      intro i
      rw [hv_eq_symm i.1 (Nat.lt_succ_iff.mp i.isLt)]
      exact hlt_all i.1 (Nat.lt_succ_iff.mp i.isLt)
    let g : Fin (m + 1) → Fin m := fun i => ⟨(v (i.1 + 1)).1, hval_lt i⟩
    have hnotinj : ¬ Function.Injective g := by
      intro hinj
      have := Fintype.card_le_of_injective g hinj
      simp at this
    rcases Function.not_injective_iff.mp hnotinj with ⟨i, j, hij, hne⟩
    wlog hlt_ij : i.1 < j.1 generalizing i j
    · exact this j i hij.symm hne.symm (lt_of_le_of_ne (not_lt.mp hlt_ij) (fun h => hne (Fin.ext h.symm)))
    have hveq : v (i.1 + 1) = v (j.1 + 1) := Fin.ext (congrArg (Fin.val : Fin m → ℕ) hij)
    -- The set `{ v (t + 1) | t ∈ Ico i.1 j.1 }` is a nonempty proper `f`-invariant subset!
    let S : Finset (Fin n) := (Finset.Ico i.1 j.1).image (fun t => v (t + 1))
    have hSne : S.Nonempty := ⟨v (i.1 + 1), Finset.mem_image_of_mem _ (Finset.mem_Ico.mpr ⟨le_rfl, hlt_ij⟩)⟩
    have hSneU : S ≠ Finset.univ := by
      intro hU
      have hcard : S.card ≤ m := by
        have hsub : S ⊆ Finset.univ.filter (fun x : Fin n => x.1 < m) := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
          have htlt : t < m + 1 := by have := (Finset.mem_Ico.mp ht).2; have := j.isLt; omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval_lt ⟨t, htlt⟩⟩
        have hcle := Finset.card_le_card hsub
        have hce : (Finset.univ.filter (fun x : Fin n => x.1 < m)).card = m := by
          refine Finset.card_eq_of_bijective (fun a ha => ⟨a, by omega⟩)
            (fun b hb => ⟨b.1, (Finset.mem_filter.mp hb).2, rfl⟩)
            (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
            (fun a b _ _ h => congrArg Fin.val h)
        omega
      rw [hU, Finset.card_univ, Fintype.card_fin] at hcard
      omega
    rcases hf S hSne hSneU with ⟨x, hxS, hfx⟩
    rcases Finset.mem_image.mp hxS with ⟨t, ht, rfl⟩
    have htI := Finset.mem_Ico.mp ht
    have htle : t ≤ m := by have := j.isLt; omega
    apply hfx
    by_cases hti : t = i.1
    · subst hti
      rw [hveq, hv_eq_symm (j.1) (by have := j.isLt; omega), Equiv.apply_symm_apply]
      have hj1 : j.1 - 1 ∈ Finset.Ico i.1 j.1 := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have heq : j.1 - 1 + 1 = j.1 := by omega
      rw [← heq]
      exact Finset.mem_image_of_mem _ hj1
    · rw [hv_eq_symm t htle, Equiv.apply_symm_apply]
      have ht1 : t - 1 ∈ Finset.Ico i.1 j.1 := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have heq : t - 1 + 1 = t := by omega
      rw [← heq]
      exact Finset.mem_image_of_mem _ ht1
  -- Since `v` stops at some `k ≤ m`, `v m = v k` satisfies `m ≤ (f.symm (v m)).1`!
  rcases hstop_exists with ⟨k, hk_le, hk_stop⟩
  have hv_const : ∀ d, v (k + d) = v k := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [← add_assoc, hv_step, ih, if_neg (not_lt.mpr hk_stop)]
  have hvm_eq : v m = v k := by
    have := hv_const (m - k)
    rwa [Nat.add_sub_cancel' hk_le] at this
  refine ⟨hv_le m, ?_, ?_⟩
  · change m ≤ (f.symm (v m)).1
    rwa [hvm_eq]
  -- Suppose `f ⟨m, _⟩ = v m`: then `{ v t | t ≤ k }` is a nonempty proper `f`-invariant subset!
  intro hfm
  let S : Finset (Fin n) := (Finset.range (k + 1)).image v
  have hSne : S.Nonempty := ⟨v 0, Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.zero_lt_succ k))⟩
  have hSneU : S ≠ Finset.univ := by
    intro hU
    have hcard : S.card ≤ k + 1 := le_trans Finset.card_image_le (by simp)
    rw [hU, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  rcases hf S hSne hSneU with ⟨x, hxS, hfx⟩
  rcases Finset.mem_image.mp hxS with ⟨t, ht, rfl⟩
  have htlt := Finset.mem_range.mp ht
  apply hfx
  have hex_min : ∃ t' ≤ k, v t' = v t ∧ ∀ r < t', v r ≠ v t := by
    let P : ℕ → Prop := fun r => r ≤ k ∧ v r = v t
    have hex : ∃ r, P r := ⟨t, by omega, rfl⟩
    have hspec := Nat.find_spec hex
    refine ⟨Nat.find hex, hspec.1, hspec.2, ?_⟩
    intro r hr heq
    exact Nat.find_min hex hr ⟨by omega, heq⟩
  rcases hex_min with ⟨t', ht'le, ht'eq, ht'min⟩
  rw [← ht'eq]
  cases t' with
  | zero =>
    change f ⟨m, by omega⟩ ∈ S
    have hfm' : f ⟨m, by omega⟩ = v m := hfm
    rw [hfm', hvm_eq]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_self k))
  | succ r =>
    have hstep_r := hv_step r
    by_cases hlt : (f.symm (v r)).1 < m
    · rw [if_pos hlt] at hstep_r
      rw [hstep_r, Equiv.apply_symm_apply]
      exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
    · rw [if_neg hlt] at hstep_r
      exact absurd (hstep_r.symm.trans ht'eq) (ht'min r (Nat.lt_succ_self r))

/-- Upper bound on single `n`-cycles constrained by a monotone upper bound `Q : Fin n → ℕ`. -/
private lemma card_constrained_singleCycles_le {n : ℕ} (hn : 2 ≤ n) (Q : Fin n → ℕ)
    (hQ_mono : Monotone Q)
    (hQ_gt : ∀ j : Fin n, j.1 + 1 < n → j.1 + 1 < Q j)
    (_hQ_le : ∀ j : Fin n, Q j ≤ n) :
    (Finset.univ.filter (fun f : Equiv.Perm (Fin n) =>
      IsSingleCycle f ∧ ∀ j : Fin n, j.1 + 1 < n → (f j).1 < Q j)).card ≤
      ∏ j : Fin (n - 1), (Q ⟨j.1, by have := j.isLt; omega⟩ - j.1 - 1) := by
  let Good := Finset.univ.filter (fun f : Equiv.Perm (Fin n) =>
    IsSingleCycle f ∧ ∀ j : Fin n, j.1 + 1 < n → (f j).1 < Q j)
  let pref (m : ℕ) (hm : m ≤ n - 1) : Equiv.Perm (Fin n) → (Fin m → Fin n) :=
    fun f i => f ⟨i.1, by have := i.isLt; omega⟩
  have hPref_bound : ∀ m (hm : m ≤ n - 1),
      (Good.image (pref m hm)).card ≤ ∏ j : Fin m, (Q ⟨j.1, by have := j.isLt; omega⟩ - j.1 - 1) := by
    intro m
    induction m with
    | zero =>
      intro hm
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact le_trans (Finset.card_le_univ _) (by simp)
    | succ m ih =>
      intro hm
      have hm' : m ≤ n - 1 := by omega
      have hmlt : m + 1 < n := by omega
      rw [Fin.prod_univ_castSucc]
      let restr : (Fin (m + 1) → Fin n) → (Fin m → Fin n) :=
        fun g i => g ⟨i.1, Nat.lt_succ_of_lt i.isLt⟩
      have hFiber : ∀ g₀ ∈ Good.image (pref m hm'),
          ((Good.image (pref (m + 1) hm)).filter (fun g => restr g = g₀)).card ≤
            Q ⟨m, by omega⟩ - m - 1 := by
        intro g₀ hg₀
        rcases Finset.mem_image.mp hg₀ with ⟨f₀, hf₀G, rfl⟩
        let s₀ := backPath f₀ m m ⟨m, by omega⟩
        let Forb : Finset ℕ := insert s₀.1 ((Finset.univ : Finset (Fin m)).image (fun i => (f₀ ⟨i.1, by have := i.isLt; omega⟩).1))
        have hForb_sub : Forb ⊆ Finset.range (Q ⟨m, by omega⟩) := by
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyI
          · have hs_le := (backPath_singleCycle (Finset.mem_filter.mp hf₀G).2.1 hmlt).1
            have hQm : m + 1 < Q ⟨m, by omega⟩ := hQ_gt ⟨m, by omega⟩ hmlt
            exact Finset.mem_range.mpr (by omega)
          · rcases Finset.mem_image.mp hyI with ⟨i, _, rfl⟩
            have hi_lt : i.1 + 1 < n := by have := i.isLt; omega
            have hf_lt := (Finset.mem_filter.mp hf₀G).2.2 ⟨i.1, by omega⟩ hi_lt
            have hQle : Q ⟨i.1, by omega⟩ ≤ Q ⟨m, by omega⟩ :=
              hQ_mono (show (⟨i.1, by omega⟩ : Fin n) ≤ ⟨m, by omega⟩ from le_of_lt i.isLt)
            exact Finset.mem_range.mpr (lt_of_lt_of_le hf_lt hQle)
        have hs₀_not : s₀.1 ∉ (Finset.univ : Finset (Fin m)).image (fun i => (f₀ ⟨i.1, by have := i.isLt; omega⟩).1) := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
          have h1 : f₀ ⟨i.1, by have := i.isLt; omega⟩ = s₀ := Fin.ext hi
          have h2 : f₀.symm s₀ = ⟨i.1, by have := i.isLt; omega⟩ := by
            rw [← h1, Equiv.symm_apply_apply]
          have hge := (backPath_singleCycle (Finset.mem_filter.mp hf₀G).2.1 hmlt).2.1
          rw [h2] at hge
          dsimp at hge
          have := i.isLt
          omega
        have hForb_card : Forb.card = m + 1 := by
          rw [Finset.card_insert_of_notMem hs₀_not]
          have hinj : Function.Injective (fun i : Fin m => (f₀ ⟨i.1, by have := i.isLt; omega⟩).1) := by
            intro a b hab
            have h := f₀.injective (Fin.ext hab)
            exact Fin.ext (congrArg (Fin.val : Fin n → ℕ) h)
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        let Fiber := (Good.image (pref (m + 1) hm)).filter (fun g => restr g = pref m hm' f₀)
        have hinj_ev : Set.InjOn (fun g : Fin (m + 1) → Fin n => (g ⟨m, Nat.lt_succ_self m⟩).1) (Fiber : Set _) := by
          intro g₁ hg₁ g₂ hg₂ heq
          have hr₁ := (Finset.mem_filter.mp hg₁).2
          have hr₂ := (Finset.mem_filter.mp hg₂).2
          funext ⟨k, hk⟩
          by_cases hkm : k < m
          · have := congrFun (hr₁.trans hr₂.symm) ⟨k, hkm⟩
            simpa [restr] using this
          · have hkeq : k = m := by omega
            subst hkeq
            exact Fin.ext heq
        have himg_sub : Fiber.image (fun g => (g ⟨m, Nat.lt_succ_self m⟩).1) ⊆
            Finset.range (Q ⟨m, by omega⟩) \ Forb := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨g, hgF, rfl⟩
          rcases Finset.mem_filter.mp hgF with ⟨hgI, hgr⟩
          rcases Finset.mem_image.mp hgI with ⟨f, hfG, rfl⟩
          have hagree : ∀ j : Fin n, j.1 < m → f j = f₀ j := by
            intro j hj
            have := congrFun hgr ⟨j.1, hj⟩
            simpa [restr, pref] using this
          have hfm_lt : (f ⟨m, by omega⟩).1 < Q ⟨m, by omega⟩ :=
            (Finset.mem_filter.mp hfG).2.2 ⟨m, by omega⟩ hmlt
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hfm_lt, ?_⟩
          intro hmemF
          rcases Finset.mem_insert.mp hmemF with hEqS | hmemI
          · have hback : backPath f m m ⟨m, by omega⟩ = s₀ :=
              backPath_eq_of_agree hagree m ⟨m, by omega⟩
            have hne := (backPath_singleCycle (Finset.mem_filter.mp hfG).2.1 hmlt).2.2
            rw [hback] at hne
            exact hne (Fin.ext hEqS)
          · rcases Finset.mem_image.mp hmemI with ⟨i, _, hi⟩
            have hi' : f ⟨i.1, by have := i.isLt; omega⟩ = f ⟨m, by omega⟩ := by
              rw [hagree ⟨i.1, by have := i.isLt; omega⟩ i.isLt]
              exact Fin.ext hi
            have hval := congrArg (Fin.val : Fin n → ℕ) (f.injective hi')
            dsimp at hval
            have := i.isLt
            omega
        calc
          Fiber.card = (Fiber.image (fun g => (g ⟨m, Nat.lt_succ_self m⟩).1)).card :=
            (Finset.card_image_of_injOn hinj_ev).symm
          _ ≤ (Finset.range (Q ⟨m, by omega⟩) \ Forb).card := Finset.card_le_card himg_sub
          _ = Q ⟨m, by omega⟩ - m - 1 := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hForb_sub, Finset.card_range, hForb_card]
            omega
      have hmaps : ∀ g ∈ Good.image (pref (m + 1) hm), restr g ∈ Good.image (pref m hm') := by
        intro g hg
        rcases Finset.mem_image.mp hg with ⟨f, hf, rfl⟩
        exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
      calc
        (Good.image (pref (m + 1) hm)).card
            = ∑ g₀ ∈ Good.image (pref m hm'),
                ((Good.image (pref (m + 1) hm)).filter (fun g => restr g = g₀)).card :=
              Finset.card_eq_sum_card_fiberwise hmaps
        _ ≤ ∑ _g₀ ∈ Good.image (pref m hm'), (Q ⟨m, by omega⟩ - m - 1) :=
              Finset.sum_le_sum hFiber
        _ = (Good.image (pref m hm')).card * (Q ⟨m, by omega⟩ - m - 1) := by simp
        _ ≤ (∏ j : Fin m, (Q ⟨j.1, by have := j.isLt; omega⟩ - j.1 - 1)) * (Q ⟨m, by omega⟩ - m - 1) :=
              Nat.mul_le_mul_right _ (ih hm')
  have hinj_last : Function.Injective (pref (n - 1) le_rfl) := by
    intro f₁ f₂ hEq
    have hlt : ∀ i : Fin n, i.1 < n - 1 → f₁ i = f₂ i := fun i hi =>
      congrFun hEq ⟨i.1, hi⟩
    ext i
    by_cases hi : i.1 < n - 1
    · exact congrArg Fin.val (hlt i hi)
    · have hieq : i = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp; have := i.isLt; omega)
      rw [hieq]
      let S₁ := (Finset.univ : Finset (Fin n)).erase ⟨n - 1, by omega⟩
      have hImgEq : S₁.image f₁ = S₁.image f₂ := by
        refine Finset.image_congr fun j hj => ?_
        have hjne := (Finset.mem_erase.mp hj).1
        exact hlt j (by
          have hjlt := j.isLt
          by_contra hge
          apply hjne
          exact Fin.ext (by dsimp; omega))
      have h1not : f₁ ⟨n - 1, by omega⟩ ∉ S₁.image f₁ := by
        intro hm
        rcases Finset.mem_image.mp hm with ⟨j, hj, hjEq⟩
        exact (Finset.mem_erase.mp hj).1 (f₁.injective hjEq)
      have h2mem : f₁ ⟨n - 1, by omega⟩ ∉ S₁.image f₂ := hImgEq ▸ h1not
      have hex : ∃ j : Fin n, f₂ j = f₁ ⟨n - 1, by omega⟩ := ⟨f₂.symm _, Equiv.apply_symm_apply _ _⟩
      rcases hex with ⟨j, hj⟩
      have hj_eq : j = ⟨n - 1, by omega⟩ := by
        by_contra hne
        exact h2mem (Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩, hj⟩)
      rw [hj_eq] at hj
      exact congrArg Fin.val hj.symm
  calc
    Good.card = (Good.image (pref (n - 1) le_rfl)).card :=
      (Finset.card_image_of_injective _ hinj_last).symm
    _ ≤ ∏ j : Fin (n - 1), (Q ⟨j.1, by have := j.isLt; omega⟩ - j.1 - 1) := hPref_bound (n - 1) le_rfl

/-! ### Section 4: Average of `4^|U(v ∘ σ)| - 1` over permutations `σ` -/

private noncomputable def fac (n a b q : ℕ) : ℝ :=
  ∏ j ∈ Finset.Ico a b, ((q - 1 - j : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ)

private lemma fac_nonneg (n a b q : ℕ) : 0 ≤ fac n a b q := by
  unfold fac
  exact Finset.prod_nonneg fun j _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private lemma fac_le_one {n a b q : ℕ} (hq : q ≤ n) : fac n a b q ≤ 1 := by
  unfold fac
  refine Finset.prod_le_one (fun j _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_
  intro j _
  by_cases hd : n - 1 - j = 0
  · have hq0 : q - 1 - j = 0 := by omega
    simp [hd, hq0]
  · rw [div_le_one (Nat.cast_pos.mpr (by omega))]
    exact_mod_cast (by omega : q - 1 - j ≤ n - 1 - j)

private lemma fac_anti_left {n a₁ a₂ b q : ℕ} (ha : a₁ ≤ a₂) (hb : a₂ ≤ b) (hq : q ≤ n) :
    fac n a₁ b q ≤ fac n a₂ b q := by
  have hsplit : Finset.Ico a₁ b = Finset.Ico a₁ a₂ ∪ Finset.Ico a₂ b :=
    (Finset.Ico_union_Ico_eq_Ico ha hb).symm
  have hdisj : Disjoint (Finset.Ico a₁ a₂) (Finset.Ico a₂ b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (Finset.mem_Ico.mp hx1).2
    have h2 := (Finset.mem_Ico.mp hx2).1
    omega
  unfold fac
  rw [hsplit, Finset.prod_union hdisj]
  have hle1 : fac n a₁ a₂ q ≤ 1 := fac_le_one hq
  have hnn : 0 ≤ fac n a₂ b q := fac_nonneg n a₂ b q
  calc
    fac n a₁ a₂ q * fac n a₂ b q ≤ 1 * fac n a₂ b q := mul_le_mul_of_nonneg_right hle1 hnn
    _ = fac n a₂ b q := one_mul _

private lemma fac_le_div {n a b q : ℕ} (hab : a < b) (hbq : b < q) (hqn : q ≤ n - 1) :
    fac n a b q ≤ ((q - b : ℕ) : ℝ) / ((n - 1 - a : ℕ) : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hab)
  induction k with
  | zero =>
    have hIco : Finset.Ico a (a + 1) = {a} := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    unfold fac
    simp only [add_zero, hIco, Finset.prod_singleton]
    have h1 : q - 1 - a = q - (a + 1) := by omega
    rw [h1]
  | succ k ih =>
    have hb_eq : a + 1 + (k + 1) = (a + 1 + k) + 1 := by omega
    rw [hb_eq]
    have hsplit : Finset.Ico a ((a + 1 + k) + 1) =
        Finset.Ico a (a + 1 + k) ∪ {a + 1 + k} := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]; omega
    have hnot : a + 1 + k ∉ Finset.Ico a (a + 1 + k) := by
      simp only [Finset.mem_Ico]; omega
    have hfac_step : fac n a ((a + 1 + k) + 1) q =
        fac n a (a + 1 + k) q *
          (((q - 1 - (a + 1 + k) : ℕ) : ℝ) / ((n - 1 - (a + 1 + k) : ℕ) : ℝ)) := by
      unfold fac
      rw [hsplit, Finset.prod_union (Finset.disjoint_singleton_right.mpr hnot), Finset.prod_singleton]
    rw [hfac_step]
    have hih := ih (by omega) (by omega)
    have hstep_nn : 0 ≤ ((q - 1 - (a + 1 + k) : ℕ) : ℝ) / ((n - 1 - (a + 1 + k) : ℕ) : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hq_eq : q - 1 - (a + 1 + k) = q - ((a + 1 + k) + 1) := by omega
    have hratio : ((q - (a + 1 + k) : ℕ) : ℝ) / ((n - 1 - (a + 1 + k) : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (Nat.cast_pos.mpr (by omega))]
      exact_mod_cast (by omega : q - (a + 1 + k) ≤ n - 1 - (a + 1 + k))
    calc
      fac n a (a + 1 + k) q * (((q - 1 - (a + 1 + k) : ℕ) : ℝ) / ((n - 1 - (a + 1 + k) : ℕ) : ℝ))
          ≤ (((q - (a + 1 + k) : ℕ) : ℝ) / ((n - 1 - a : ℕ) : ℝ)) *
              (((q - 1 - (a + 1 + k) : ℕ) : ℝ) / ((n - 1 - (a + 1 + k) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hih hstep_nn
      _ = (((q - ((a + 1 + k) + 1) : ℕ) : ℝ) / ((n - 1 - a : ℕ) : ℝ)) *
            (((q - (a + 1 + k) : ℕ) : ℝ) / ((n - 1 - (a + 1 + k) : ℕ) : ℝ)) := by
            rw [hq_eq]; ring
      _ ≤ (((q - ((a + 1 + k) + 1) : ℕ) : ℝ) / ((n - 1 - a : ℕ) : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hratio (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = ((q - ((a + 1 + k) + 1) : ℕ) : ℝ) / ((n - 1 - a : ℕ) : ℝ) := mul_one _

private lemma sum_fac_le {n b q : ℕ} (hb : 1 ≤ b) (hbq : b < q) (hqn : q ≤ n - 2) :
    ∑ a ∈ Finset.Ico 1 b, fac n a b q ≤ ((q - b : ℕ) : ℝ) / ((n - 1 - q : ℕ) : ℝ) := by
  let T : ℕ → ℝ := fun a => ((q - a : ℕ) : ℝ) * fac n a b q
  have hstep : ∀ a ∈ Finset.Ico 1 b,
      ((n - 1 - q : ℕ) : ℝ) * fac n a b q = T (a + 1) - T a := by
    intro a ha
    have ha1 := (Finset.mem_Ico.mp ha).1
    have hab := (Finset.mem_Ico.mp ha).2
    have hsplit : Finset.Ico a b = insert a (Finset.Ico (a + 1) b) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot : a ∉ Finset.Ico (a + 1) b := by simp only [Finset.mem_Ico]; omega
    have hfac_eq : fac n a b q =
        (((q - 1 - a : ℕ) : ℝ) / ((n - 1 - a : ℕ) : ℝ)) * fac n (a + 1) b q := by
      unfold fac
      rw [hsplit, Finset.prod_insert hnot]
    have hden_ne : ((n - 1 - a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hTsucc : T (a + 1) = ((n - 1 - a : ℕ) : ℝ) * fac n a b q := by
      simp only [T]
      rw [hfac_eq, show q - (a + 1) = q - 1 - a by omega]
      field_simp [hden_ne]
    rw [hTsucc]
    simp only [T]
    have hsub : ((n - 1 - a : ℕ) : ℝ) - ((q - a : ℕ) : ℝ) = ((n - 1 - q : ℕ) : ℝ) := by
      have : (n - 1 - q) + (q - a) = n - 1 - a := by omega
      have hcast : (((n - 1 - q : ℕ) : ℝ) + ((q - a : ℕ) : ℝ)) = ((n - 1 - a : ℕ) : ℝ) := by
        exact_mod_cast this
      linarith
    rw [← hsub]
    ring
  have htel : ∀ k, k ≤ b - 1 →
      ∑ a ∈ Finset.Ico 1 (1 + k), (T (a + 1) - T a) = T (1 + k) - T 1 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hsplit : Finset.Ico 1 (1 + (k + 1)) = Finset.Ico 1 (1 + k) ∪ {1 + k} := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]; omega
      have hnot : 1 + k ∉ Finset.Ico 1 (1 + k) := by simp only [Finset.mem_Ico]; omega
      rw [hsplit, Finset.sum_union (Finset.disjoint_singleton_right.mpr hnot),
        Finset.sum_singleton, ih (by omega)]
      have : 1 + k + 1 = 1 + (k + 1) := by omega
      rw [this]
      ring
  have hsum_eq :
      ((n - 1 - q : ℕ) : ℝ) * ∑ a ∈ Finset.Ico 1 b, fac n a b q = T b - T 1 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hstep]
    have hb_eq : 1 + (b - 1) = b := by omega
    have h := htel (b - 1) le_rfl
    rwa [hb_eq] at h
  have hT1_nn : 0 ≤ T 1 := mul_nonneg (Nat.cast_nonneg _) (fac_nonneg n 1 b q)
  have hTb : T b = ((q - b : ℕ) : ℝ) := by
    simp only [T, fac, Finset.Ico_self, Finset.prod_empty, mul_one]
  have hpos : (0 : ℝ) < ((n - 1 - q : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [le_div_iff₀ hpos, mul_comm, hsum_eq, hTb]
  linarith

private lemma fac_zero_dual {n b q : ℕ} (hbq : b < q) (hqn : q ≤ n) :
    fac n 0 b q = ∏ u ∈ Finset.range (n - q), ((q - b + u : ℕ) : ℝ) / ((q + u : ℕ) : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqn
  rw [Nat.add_sub_cancel_left]
  induction d with
  | zero =>
    simp only [add_zero, Finset.range_zero, Finset.prod_empty]
    unfold fac
    refine Finset.prod_eq_one fun j hj => ?_
    have hjlt := (Finset.mem_Ico.mp hj).2
    have hne : ((q - 1 - j : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact div_self hne
  | succ d ih =>
    rw [Finset.prod_range_succ, ← ih (by omega)]
    -- Show `fac (q + d + 1) 0 b q = fac (q + d) 0 b q * ((q - b + d) / (q + d))`
    have hIco : Finset.Ico 0 b = Finset.range b := Nat.Ico_zero_eq_range b
    unfold fac
    rw [hIco, Finset.prod_div_distrib, Finset.prod_div_distrib]
    -- Relate `∏ j ∈ range b, (q + d - j)` and `∏ j ∈ range b, (q + d - 1 - j)`
    have hden_rel :
        ((q - b + d : ℕ) : ℝ) * (∏ j ∈ Finset.range b, ((q + d - j : ℕ) : ℝ)) =
        ((q + d : ℕ) : ℝ) * (∏ j ∈ Finset.range b, ((q + d - 1 - j : ℕ) : ℝ)) := by
      cases b with
      | zero => simp
      | succ b' =>
        rw [Finset.prod_range_succ', Finset.prod_range_succ]
        have h0 : q + d - 0 = q + d := by omega
        have hlast : q + d - 1 - b' = q - (b' + 1) + d := by omega
        rw [h0, hlast]
        have hshift :
            (∏ x ∈ Finset.range b', ((q + d - (x + 1) : ℕ) : ℝ)) =
            (∏ x ∈ Finset.range b', ((q + d - 1 - x : ℕ) : ℝ)) := by
          refine Finset.prod_congr rfl fun x _ => ?_
          congr 1; omega
        rw [hshift]
        ring
    have hd1 : (∏ j ∈ Finset.range b, ((q + d - j : ℕ) : ℝ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      have := Finset.mem_range.mp hj
      exact Nat.cast_ne_zero.mpr (by omega)
    have hd2 : (∏ j ∈ Finset.range b, ((q + d - 1 - j : ℕ) : ℝ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      have := Finset.mem_range.mp hj
      exact Nat.cast_ne_zero.mpr (by omega)
    have hqd_ne : ((q + d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hsub1 : (∏ j ∈ Finset.range b, ((q + (d + 1) - 1 - j : ℕ) : ℝ)) =
        (∏ j ∈ Finset.range b, ((q + d - j : ℕ) : ℝ)) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      congr 1
    rw [hsub1]
    field_simp [hd1, hd2, hqd_ne]
    linear_combination (∏ j ∈ Finset.range b, ((q - 1 - j : ℕ) : ℝ)) * hden_rel.symm

private lemma fac_zero_le_sq {n b q M : ℕ} (hb2 : 2 ≤ b) (hbq : b < q) (hqn : q ≤ n - 2)
    (hM1 : 1 ≤ M) (hqb : q - b ≤ M) :
    fac n 0 b q ≤ 8 * (M : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  by_cases hhalf : 2 * b ≤ n
  · -- Take the last 2 factors `b - 2` and `b - 1`
    have hsplit : Finset.Ico 0 b = Finset.Ico 0 (b - 2) ∪ {b - 2, b - 1} := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hdisj : Disjoint (Finset.Ico 0 (b - 2)) {b - 2, b - 1} := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := (Finset.mem_Ico.mp hx1).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      omega
    have hne : b - 2 ≠ b - 1 := by omega
    have hfac_eq : fac n 0 b q =
        fac n 0 (b - 2) q *
          ((((q - 1 - (b - 2) : ℕ) : ℝ) / ((n - 1 - (b - 2) : ℕ) : ℝ)) *
           (((q - 1 - (b - 1) : ℕ) : ℝ) / ((n - 1 - (b - 1) : ℕ) : ℝ))) := by
      unfold fac
      rw [hsplit, Finset.prod_union hdisj, Finset.prod_pair hne]
    rw [hfac_eq]
    have hf1 : (((q - 1 - (b - 2) : ℕ) : ℝ) / ((n - 1 - (b - 2) : ℕ) : ℝ)) ≤
        (2 * (M : ℝ)) / ((n : ℝ) / 2) := by
      have hnum : ((q - 1 - (b - 2) : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
        have : q - 1 - (b - 2) ≤ 2 * M := by omega
        exact_mod_cast this
      have hden : (n : ℝ) / 2 ≤ ((n - 1 - (b - 2) : ℕ) : ℝ) := by
        have : n ≤ 2 * (n - 1 - (b - 2)) := by omega
        have hcast : (n : ℝ) ≤ 2 * ((n - 1 - (b - 2) : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    have hf2 : (((q - 1 - (b - 1) : ℕ) : ℝ) / ((n - 1 - (b - 1) : ℕ) : ℝ)) ≤
        (M : ℝ) / ((n : ℝ) / 2) := by
      have hnum : ((q - 1 - (b - 1) : ℕ) : ℝ) ≤ (M : ℝ) := by
        have : q - 1 - (b - 1) ≤ M := by omega
        exact_mod_cast this
      have hden : (n : ℝ) / 2 ≤ ((n - 1 - (b - 1) : ℕ) : ℝ) := by
        have : n ≤ 2 * (n - 1 - (b - 1)) := by omega
        have hcast : (n : ℝ) ≤ 2 * ((n - 1 - (b - 1) : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    have hprod_nn : 0 ≤ (((q - 1 - (b - 2) : ℕ) : ℝ) / ((n - 1 - (b - 2) : ℕ) : ℝ)) *
        (((q - 1 - (b - 1) : ℕ) : ℝ) / ((n - 1 - (b - 1) : ℕ) : ℝ)) := by positivity
    calc
      fac n 0 (b - 2) q * _ ≤ 1 * _ :=
        mul_le_mul_of_nonneg_right (fac_le_one (by omega)) hprod_nn
      _ = _ := one_mul _
      _ ≤ ((2 * (M : ℝ)) / ((n : ℝ) / 2)) * ((M : ℝ) / ((n : ℝ) / 2)) :=
        mul_le_mul hf1 hf2 (by positivity) (by positivity)
      _ = 8 * (M : ℝ) ^ 2 / (n : ℝ) ^ 2 := by ring
  · -- Case `n < 2 * b`: use `fac_zero_dual` and take `u = 0, 1`
    rw [fac_zero_dual hbq (by omega)]
    have hsplit : Finset.range (n - q) = {0, 1} ∪ Finset.Ico 2 (n - q) := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_Ico]; omega
    have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Ico 2 (n - q)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
      have h2 := (Finset.mem_Ico.mp hx2).1
      omega
    rw [hsplit, Finset.prod_union hdisj, Finset.prod_pair (by omega : (0 : ℕ) ≠ 1)]
    have htail_le1 : ∏ u ∈ Finset.Ico 2 (n - q), ((q - b + u : ℕ) : ℝ) / ((q + u : ℕ) : ℝ) ≤ 1 := by
      refine Finset.prod_le_one (fun u _ => by positivity) fun u _ => ?_
      rw [div_le_one (Nat.cast_pos.mpr (by omega))]
      exact_mod_cast (by omega : q - b + u ≤ q + u)
    have hf0 : ((q - b + 0 : ℕ) : ℝ) / ((q + 0 : ℕ) : ℝ) ≤ (M : ℝ) / ((n : ℝ) / 2) := by
      have hnum : ((q - b + 0 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : q - b + 0 ≤ M)
      have hden : (n : ℝ) / 2 ≤ ((q + 0 : ℕ) : ℝ) := by
        have : n ≤ 2 * (q + 0) := by omega
        have hcast : (n : ℝ) ≤ 2 * ((q + 0 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    have hf1 : ((q - b + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ) ≤ (2 * (M : ℝ)) / ((n : ℝ) / 2) := by
      have hnum : ((q - b + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
        exact_mod_cast (by omega : q - b + 1 ≤ 2 * M)
      have hden : (n : ℝ) / 2 ≤ ((q + 1 : ℕ) : ℝ) := by
        have : n ≤ 2 * (q + 1) := by omega
        have hcast : (n : ℝ) ≤ 2 * ((q + 1 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    calc
      (((q - b + 0 : ℕ) : ℝ) / ((q + 0 : ℕ) : ℝ) *
        (((q - b + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ))) * _
          ≤ (((q - b + 0 : ℕ) : ℝ) / ((q + 0 : ℕ) : ℝ) *
              (((q - b + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ))) * 1 :=
            mul_le_mul_of_nonneg_left htail_le1 (by positivity)
      _ = _ := mul_one _
      _ ≤ ((M : ℝ) / ((n : ℝ) / 2)) * ((2 * (M : ℝ)) / ((n : ℝ) / 2)) :=
            mul_le_mul hf0 hf1 (by positivity) (by positivity)
      _ = 8 * (M : ℝ) ^ 2 / (n : ℝ) ^ 2 := by ring

private lemma prod_sub_eq_factorial (m : ℕ) :
    ∏ j ∈ Finset.range m, (m - j) = m ! := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ', Nat.factorial_succ, Nat.sub_zero]
    have hshift : ∏ x ∈ Finset.range m, (m + 1 - (x + 1)) = ∏ x ∈ Finset.range m, (m - x) := by
      refine Finset.prod_congr rfl fun x _ => by omega
    rw [hshift, ih, mul_comm]

private lemma filter_eq_lt_card_of_downward {n : ℕ} (P : Finset (Fin n))
    (hdown : ∀ a b : Fin n, a ≤ b → b ∈ P → a ∈ P) :
    P = Finset.univ.filter (fun j : Fin n => j.1 < P.card) := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsub : Finset.univ.filter (fun b : Fin n => b.1 ≤ a.1) ⊆ P := fun b hb =>
      hdown b a (Finset.mem_filter.mp hb).2 ha
    have hle := Finset.card_le_card hsub
    have heq : (Finset.univ.filter (fun b : Fin n => b.1 ≤ a.1)).card = a.1 + 1 := by
      refine Finset.card_eq_of_bijective (fun i hi => ⟨i, by have := a.isLt; omega⟩)
        (fun b hb => ⟨b.1, by have := (Finset.mem_filter.mp hb).2; omega, rfl⟩)
        (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩)
        (fun i j _ _ h => congrArg Fin.val h)
    omega
  · have hcard : (Finset.univ.filter (fun j : Fin n => j.1 < P.card)).card = P.card := by
      have hle : P.card ≤ n := by simpa using Finset.card_le_univ P
      refine Finset.card_eq_of_bijective (fun i hi => ⟨i, by omega⟩)
        (fun b hb => ⟨b.1, (Finset.mem_filter.mp hb).2, rfl⟩)
        (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        (fun i j _ _ h => congrArg Fin.val h)
    omega

private lemma minH_of_monotone {n : ℕ} (hn : 0 < n) (v : Fin n → Fin (n + 1)) (hv : Monotone v) :
    minH hn v = (v ⟨0, hn⟩).1 := by
  apply le_antisymm
  · exact minH_le hn v ⟨0, hn⟩
  · rcases exists_eq_minH hn v with ⟨c, hc⟩
    rw [← hc]
    exact hv (show (⟨0, hn⟩ : Fin n) ≤ c from Nat.zero_le c.1)

private lemma maxH_of_monotone {n : ℕ} (hn : 0 < n) (v : Fin n → Fin (n + 1)) (hv : Monotone v) :
    maxH hn v = (v ⟨n - 1, by omega⟩).1 := by
  apply le_antisymm
  · rcases exists_eq_maxH hn v with ⟨c, hc⟩
    rw [← hc]
    exact hv (show c ≤ ⟨n - 1, by omega⟩ from Nat.le_sub_one_of_lt c.isLt)
  · exact le_maxH hn v ⟨n - 1, by omega⟩

private lemma four_pow_sub_one_eq_sum_powerset {α : Type*} [DecidableEq α] (S : Finset α) :
    ((4 ^ S.card - 1 : ℕ) : ℝ) =
      ∑ A ∈ S.powerset.filter Finset.Nonempty, (3 : ℝ) ^ A.card := by
  have h1 : (4 : ℝ) ^ S.card = ∑ A ∈ S.powerset, (3 : ℝ) ^ A.card := by
    have hadd := add_pow (3 : ℝ) 1 S.card
    rw [show (3 : ℝ) + 1 = 4 by norm_num] at hadd
    rw [hadd]
    have hpow : S.powerset = (Finset.range (S.card + 1)).biUnion (fun k => S.powersetCard k) := by
      ext A
      simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
      constructor
      · intro hA; exact ⟨A.card, Nat.lt_succ_of_le (Finset.card_le_card hA), hA, rfl⟩
      · rintro ⟨_, _, hA, _⟩; exact hA
    rw [hpow, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.sum_congr rfl (fun A hA => by rw [(Finset.mem_powersetCard.mp hA).2]),
        Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, one_pow, mul_one, mul_comm]
    · intro k₁ _ k₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro A hA1 hA2
      exact hne ((Finset.mem_powersetCard.mp hA1).2.symm.trans (Finset.mem_powersetCard.mp hA2).2)
  have hsplit : S.powerset = insert ∅ (S.powerset.filter Finset.Nonempty) := by
    ext A
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_powerset]
    by_cases hA : A = ∅
    · subst hA; simp
    · simp [hA, Finset.nonempty_iff_ne_empty.mpr hA]
  have hnot : (∅ : Finset α) ∉ S.powerset.filter Finset.Nonempty := by
    simp
  have hge : 1 ≤ 4 ^ S.card := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, h1]
  conv_lhs => rw [hsplit, Finset.sum_insert hnot]
  simp

/-- Pure algebraic bounds for the DP sequence `dp : Fin r → ℝ`. -/
private lemma dp_sum_bounds {n r : ℕ} (hn : 10 ≤ n) (p q : Fin r → ℕ)
    (hp_pos : ∀ i : Fin r, 1 ≤ p i) (hq_le : ∀ i : Fin r, q i ≤ n - 1)
    (hp_lt_q : ∀ i : Fin r, p i < q i) (hq_le_p : ∀ {k i : Fin r}, k < i → q k ≤ p i)
    (dp : Fin r → ℝ) (hdp_nonneg : ∀ i : Fin r, 0 ≤ dp i)
    (hdp_rec : ∀ i : Fin r,
      dp i = 3 * fac n 0 (p i) (q i) +
        3 * ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i), dp k * fac n (p k) (p i) (q i)) :
    (∑ i : Fin r, dp i ≤ 36864) ∧
    (∀ M : ℕ, 16 ≤ n → 1 ≤ M → (∀ i : Fin r, q i - p i ≤ M) →
      ∑ i : Fin r, dp i ≤
        4096 * (6 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) +
          24 * (M : ℝ) ^ 2 / (n : ℝ) +
          18 * (M : ℝ) * (Nat.sqrt n : ℝ) / ((n - 1 : ℕ) : ℝ) +
          18 * (M : ℝ) / ((Nat.sqrt n + 1 : ℕ) : ℝ))) := by
  let t : Fin r → ℕ := fun i => q i - p i
  have hp_strict : StrictMono p := fun k i hki => lt_of_lt_of_le (hp_lt_q k) (hq_le_p hki)
  have hq_strict : StrictMono q := fun k i hki => lt_of_le_of_lt (hq_le_p hki) (hp_lt_q i)
  have hsum_t_fac : ∀ i : Fin r, q i ≤ n - 2 →
      ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i),
        (t k : ℝ) * fac n (p k) (p i) (q i) ≤
        (t i : ℝ) / ((n - 1 - q i : ℕ) : ℝ) := by
    intro i hqi
    have hpiece : ∀ k ∈ Finset.univ.filter (fun k : Fin r => k < i),
        (t k : ℝ) * fac n (p k) (p i) (q i) ≤
          ∑ a ∈ Finset.Ico (p k) (q k), fac n a (p i) (q i) := by
      intro k hk
      have hki : k < i := (Finset.mem_filter.mp hk).2
      have hqk_le : q k ≤ p i := hq_le_p hki
      calc
        (t k : ℝ) * fac n (p k) (p i) (q i)
            = ∑ _a ∈ Finset.Ico (p k) (q k), fac n (p k) (p i) (q i) := by
              rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ ∑ a ∈ Finset.Ico (p k) (q k), fac n a (p i) (q i) := by
              refine Finset.sum_le_sum fun a ha => ?_
              exact fac_anti_left (Finset.mem_Ico.mp ha).1
                (le_trans (le_of_lt (Finset.mem_Ico.mp ha).2) hqk_le) (by omega)
    have hdisj : Set.PairwiseDisjoint
        ((Finset.univ.filter (fun k : Fin r => k < i)) : Set (Fin r))
        (fun k => Finset.Ico (p k) (q k)) := by
      intro k₁ _ k₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro a ha1 ha2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 := (Finset.mem_Ico.mp ha1).2
        have h2 := (Finset.mem_Ico.mp ha2).1
        have := hq_le_p hlt; omega
      · have h1 := (Finset.mem_Ico.mp ha2).2
        have h2 := (Finset.mem_Ico.mp ha1).1
        have := hq_le_p hgt; omega
    have hsub : (Finset.univ.filter (fun k : Fin r => k < i)).biUnion (fun k => Finset.Ico (p k) (q k)) ⊆
        Finset.Ico 1 (p i) := by
      intro a ha
      rcases Finset.mem_biUnion.mp ha with ⟨k, hk, hak⟩
      have hki : k < i := (Finset.mem_filter.mp hk).2
      exact Finset.mem_Ico.mpr ⟨le_trans (hp_pos k) (Finset.mem_Ico.mp hak).1,
        lt_of_lt_of_le (Finset.mem_Ico.mp hak).2 (hq_le_p hki)⟩
    calc
      ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i), (t k : ℝ) * fac n (p k) (p i) (q i)
          ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i),
              ∑ a ∈ Finset.Ico (p k) (q k), fac n a (p i) (q i) := Finset.sum_le_sum hpiece
      _ = ∑ a ∈ (Finset.univ.filter (fun k : Fin r => k < i)).biUnion (fun k => Finset.Ico (p k) (q k)),
            fac n a (p i) (q i) := (Finset.sum_biUnion hdisj).symm
      _ ≤ ∑ a ∈ Finset.Ico 1 (p i), fac n a (p i) (q i) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => fac_nonneg n a (p i) (q i)
      _ ≤ ((q i - p i : ℕ) : ℝ) / ((n - 1 - q i : ℕ) : ℝ) :=
            sum_fac_le (hp_pos i) (hp_lt_q i) hqi
      _ = (t i : ℝ) / ((n - 1 - q i : ℕ) : ℝ) := rfl
  have hdp_low : ∀ i : Fin r, q i ≤ n - 7 →
      dp i ≤ 6 * (t i : ℝ) / ((n - 1 : ℕ) : ℝ) := by
    intro ⟨idx, hidx⟩
    induction idx using Nat.strong_induction_on with
    | h idx ih =>
      intro hqi
      set i : Fin r := ⟨idx, hidx⟩
      rw [hdp_rec i]
      have hterm1 : 3 * fac n 0 (p i) (q i) ≤ 3 * (t i : ℝ) / ((n - 1 : ℕ) : ℝ) := by
        have h1 := fac_le_div (n := n) (a := 0) (by have := hp_pos i; omega) (hp_lt_q i) (hq_le i)
        simp only [Nat.sub_zero] at h1
        change fac n 0 (p i) (q i) ≤ (t i : ℝ) / ((n - 1 : ℕ) : ℝ) at h1
        have hring : 3 * (t i : ℝ) / ((n - 1 : ℕ) : ℝ) = 3 * ((t i : ℝ) / ((n - 1 : ℕ) : ℝ)) := by ring
        linarith
      have hterm2 : 3 * ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i),
          dp k * fac n (p k) (p i) (q i) ≤ 3 * (t i : ℝ) / ((n - 1 : ℕ) : ℝ) := by
        have hih_sum :
            ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i), dp k * fac n (p k) (p i) (q i) ≤
            (6 / ((n - 1 : ℕ) : ℝ)) *
              ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i), (t k : ℝ) * fac n (p k) (p i) (q i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k hk => ?_
          have hki : k < i := (Finset.mem_filter.mp hk).2
          have hqk_le7 : q k ≤ n - 7 := le_trans (le_of_lt (hq_strict hki)) hqi
          have hdpk := ih k.1 hki k.isLt hqk_le7
          calc
            dp k * fac n (p k) (p i) (q i)
                ≤ (6 * (t k : ℝ) / ((n - 1 : ℕ) : ℝ)) * fac n (p k) (p i) (q i) :=
                  mul_le_mul_of_nonneg_right hdpk (fac_nonneg _ _ _ _)
            _ = (6 / ((n - 1 : ℕ) : ℝ)) * ((t k : ℝ) * fac n (p k) (p i) (q i)) := by ring
        have hfac_sum := hsum_t_fac i (by omega)
        have hdiv6 : (t i : ℝ) / ((n - 1 - q i : ℕ) : ℝ) ≤ (t i : ℝ) / 6 := by
          have h6le : (6 : ℝ) ≤ ((n - 1 - q i : ℕ) : ℝ) := by exact_mod_cast (by omega : 6 ≤ n - 1 - q i)
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h6le
        have hpos : (0 : ℝ) ≤ 6 / ((n - 1 : ℕ) : ℝ) := by positivity
        calc
          3 * ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i), dp k * fac n (p k) (p i) (q i)
              ≤ 3 * ((6 / ((n - 1 : ℕ) : ℝ)) * ((t i : ℝ) / 6)) := by
                have h1 := le_trans hih_sum (mul_le_mul_of_nonneg_left (le_trans hfac_sum hdiv6) hpos)
                linarith
          _ = 3 * (t i : ℝ) / ((n - 1 : ℕ) : ℝ) := by ring
      have hring2 : 6 * (t i : ℝ) / ((n - 1 : ℕ) : ℝ) =
          3 * (t i : ℝ) / ((n - 1 : ℕ) : ℝ) + 3 * (t i : ℝ) / ((n - 1 : ℕ) : ℝ) := by ring
      linarith
  let Low : Finset (Fin r) := Finset.univ.filter (fun i : Fin r => q i ≤ n - 7)
  let High : Finset (Fin r) := Finset.univ.filter (fun i : Fin r => ¬ q i ≤ n - 7)
  have hHigh_card : High.card ≤ 6 := by
    have hsub : High.image q ⊆ Finset.Ico (n - 6) n := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
      have hnot := (Finset.mem_filter.mp hi).2
      have hle := hq_le i
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    calc
      High.card = (High.image q).card := (Finset.card_image_of_injective _ hq_strict.injective).symm
      _ ≤ (Finset.Ico (n - 6) n).card := Finset.card_le_card hsub
      _ = 6 := by rw [Nat.card_Ico]; omega
  have hLow_eq : Low = Finset.univ.filter (fun i : Fin r => i.1 < Low.card) := by
    refine filter_eq_lt_card_of_downward Low fun a b hle hb => ?_
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      le_trans (hq_strict.monotone hle) (Finset.mem_filter.mp hb).2⟩
  have hTail_prop : ∀ ε : ℝ, 0 ≤ ε →
      (∀ i ∈ High, 3 * fac n 0 (p i) (q i) ≤ ε) →
      ∑ i : Fin r, dp i ≤ 4096 * ((∑ i ∈ Low, dp i) + ε) := by
    intro ε hε hεHigh
    let m₀ := Low.card
    let F : ℕ → ℝ := fun m => ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.1 < m), dp i
    have hFm₀ : F m₀ = ∑ i ∈ Low, dp i := by
      dsimp only [F, m₀]; rw [← hLow_eq]
    have hFr : F r = ∑ i : Fin r, dp i := by
      dsimp only [F]
      have : (Finset.univ.filter (fun i : Fin r => i.1 < r)) = Finset.univ := by
        ext i; simp
      rw [this]
    have hstep_F : ∀ d : ℕ, m₀ + d ≤ r → F (m₀ + d) + ε ≤ (4 : ℝ) ^ d * (F m₀ + ε) := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hd
        have hlt : m₀ + d < r := by omega
        let idx : Fin r := ⟨m₀ + d, hlt⟩
        have hidx_High : idx ∈ High := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          intro hqle
          have hmem : idx ∈ Low := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqle⟩
          rw [hLow_eq] at hmem
          have := (Finset.mem_filter.mp hmem).2
          dsimp [idx, m₀] at this; omega
        have hF_split : F (m₀ + (d + 1)) = F (m₀ + d) + dp idx := by
          dsimp only [F]
          have hset : Finset.univ.filter (fun i : Fin r => i.1 < m₀ + (d + 1)) =
              insert idx (Finset.univ.filter (fun i : Fin r => i.1 < m₀ + d)) := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Fin.ext_iff, idx]; omega
          have hnot : idx ∉ Finset.univ.filter (fun i : Fin r => i.1 < m₀ + d) := by
            simp [idx]
          rw [hset, Finset.sum_insert hnot, add_comm]
        have hdp_idx : dp idx ≤ ε + 3 * F (m₀ + d) := by
          rw [hdp_rec idx]
          have h1 := hεHigh idx hidx_High
          have h2 : ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < idx), dp k * fac n (p k) (p idx) (q idx) ≤
              F (m₀ + d) := by
            have hset_eq : Finset.univ.filter (fun k : Fin r => k < idx) =
                Finset.univ.filter (fun k : Fin r => k.1 < m₀ + d) := by
              ext k; simp [Fin.lt_def, idx]
            rw [hset_eq]
            refine Finset.sum_le_sum fun k _ => ?_
            calc
              dp k * fac n (p k) (p idx) (q idx) ≤ dp k * 1 :=
                mul_le_mul_of_nonneg_left (fac_le_one (by have := hq_le idx; omega)) (hdp_nonneg k)
              _ = dp k := mul_one _
          linarith
        have hih := ih (by omega)
        rw [hF_split, pow_succ']
        linarith
    have hm₀_le : m₀ ≤ r := by
      have : Low.card ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_univ Low
      simpa [m₀] using this
    have hdiff_le : r - m₀ ≤ 6 := by
      have hsum_card : Low.card + High.card = r := by
        have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin r))
          (fun i : Fin r => q i ≤ n - 7) (fun _ => (1 : ℕ))
        simpa [Low, High] using h
      omega
    have hres := hstep_F (r - m₀) (by omega)
    rw [Nat.add_sub_cancel' hm₀_le, hFr, hFm₀] at hres
    have h4pow : (4 : ℝ) ^ (r - m₀) ≤ 4096 := by
      calc (4 : ℝ) ^ (r - m₀) ≤ (4 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hdiff_le
        _ = 4096 := by norm_num
    have hnn : 0 ≤ (∑ i ∈ Low, dp i) + ε :=
      add_nonneg (Finset.sum_nonneg fun i _ => hdp_nonneg i) hε
    calc
      ∑ i : Fin r, dp i ≤ (∑ i : Fin r, dp i) + ε := by linarith
      _ ≤ (4 : ℝ) ^ (r - m₀) * ((∑ i ∈ Low, dp i) + ε) := hres
      _ ≤ 4096 * ((∑ i ∈ Low, dp i) + ε) := mul_le_mul_of_nonneg_right h4pow hnn
  constructor
  · have hLow_sum : ∑ i ∈ Low, dp i ≤ 6 := by
      have ht_sum : ∑ i ∈ Low, t i ≤ n - 1 := by
        have hdisj : Set.PairwiseDisjoint (Low : Set (Fin r)) (fun i => Finset.Ico (p i) (q i)) := by
          intro k₁ _ k₂ _ hne
          rw [Function.onFun, Finset.disjoint_left]
          intro a ha1 ha2
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have := (Finset.mem_Ico.mp ha1).2; have := (Finset.mem_Ico.mp ha2).1
            have := hq_le_p hlt; omega
          · have := (Finset.mem_Ico.mp ha2).2; have := (Finset.mem_Ico.mp ha1).1
            have := hq_le_p hgt; omega
        have hsub : Low.biUnion (fun i => Finset.Ico (p i) (q i)) ⊆ Finset.range (n - 1) := by
          intro a ha
          rcases Finset.mem_biUnion.mp ha with ⟨i, _, hai⟩
          exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hai).2 (hq_le i))
        have h1 : (Low.biUnion (fun i => Finset.Ico (p i) (q i))).card = ∑ i ∈ Low, t i := by
          rw [Finset.card_biUnion hdisj]
          refine Finset.sum_congr rfl fun i _ => Nat.card_Ico _ _
        have h2 := Finset.card_le_card hsub
        rw [h1, Finset.card_range] at h2
        exact h2
      calc
        ∑ i ∈ Low, dp i ≤ ∑ i ∈ Low, 6 * (t i : ℝ) / ((n - 1 : ℕ) : ℝ) :=
          Finset.sum_le_sum fun i hi => hdp_low i (Finset.mem_filter.mp hi).2
        _ = 6 * ((∑ i ∈ Low, t i : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ) := by
          rw [← Finset.sum_div, ← Finset.mul_sum]; push_cast; rfl
        _ ≤ 6 * ((n - 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ) := by
          have hle : ((∑ i ∈ Low, t i : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast ht_sum
          exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ = 6 := by
          have hne : ((n - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          field_simp [hne]
    have hAll := hTail_prop 3 (by norm_num) fun i _ => by
      have := fac_le_one (n := n) (a := 0) (b := p i) (q := q i) (by have := hq_le i; omega)
      linarith
    calc
      ∑ i : Fin r, dp i ≤ 4096 * ((∑ i ∈ Low, dp i) + 3) := hAll
      _ ≤ 4096 * (6 + 3) := by linarith
      _ = 36864 := by norm_num
  · intro M hn16 hM1 ht_le_M
    have hε_bound : ∀ i : Fin r, 3 * fac n 0 (p i) (q i) ≤ 3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) := by
      intro i
      have h1 := fac_le_div (n := n) (a := 0) (by have := hp_pos i; omega) (hp_lt_q i) (hq_le i)
      simp only [Nat.sub_zero] at h1
      have htm : ((q i - p i : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast ht_le_M i
      have h2 := le_trans h1 (div_le_div_of_nonneg_right htm (Nat.cast_nonneg _))
      have hring : 3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) = 3 * ((M : ℝ) / ((n - 1 : ℕ) : ℝ)) := by ring
      linarith
    have hLow_rec : ∑ i ∈ Low, dp i ≤
        (∑ i ∈ Low, 3 * fac n 0 (p i) (q i)) +
        (∑ i ∈ Low, 18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i hi => ?_
      have hqi : q i ≤ n - 7 := (Finset.mem_filter.mp hi).2
      rw [hdp_rec i]
      refine add_le_add le_rfl ?_
      have h1 : ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i), dp k * fac n (p k) (p i) (q i) ≤
          (6 / ((n - 1 : ℕ) : ℝ)) *
            ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i), (t k : ℝ) * fac n (p k) (p i) (q i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k hk => ?_
        have hki : k < i := (Finset.mem_filter.mp hk).2
        have hdpk := hdp_low k (le_trans (le_of_lt (hq_strict hki)) hqi)
        calc
          dp k * fac n (p k) (p i) (q i)
              ≤ (6 * (t k : ℝ) / ((n - 1 : ℕ) : ℝ)) * fac n (p k) (p i) (q i) :=
                mul_le_mul_of_nonneg_right hdpk (fac_nonneg _ _ _ _)
          _ = (6 / ((n - 1 : ℕ) : ℝ)) * ((t k : ℝ) * fac n (p k) (p i) (q i)) := by ring
      have h2 := hsum_t_fac i (by omega)
      have htm : (t i : ℝ) ≤ (M : ℝ) := by exact_mod_cast ht_le_M i
      have h3 : (t i : ℝ) / ((n - 1 - q i : ℕ) : ℝ) ≤ (M : ℝ) / ((n - 1 - q i : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right htm (Nat.cast_nonneg _)
      calc
        3 * ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i), dp k * fac n (p k) (p i) (q i)
            ≤ 3 * ((6 / ((n - 1 : ℕ) : ℝ)) * ((M : ℝ) / ((n - 1 - q i : ℕ) : ℝ))) := by
              have hpos : (0 : ℝ) ≤ 6 / ((n - 1 : ℕ) : ℝ) := by positivity
              have := le_trans h1 (mul_le_mul_of_nonneg_left (le_trans h2 h3) hpos)
              linarith
        _ = 18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ)) := by ring
    have hPart1 : ∑ i ∈ Low, 3 * fac n 0 (p i) (q i) ≤
        3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) + 24 * (M : ℝ) ^ 2 / (n : ℝ) := by
      let L1 := Low.filter (fun i : Fin r => p i = 1)
      let L2 := Low.filter (fun i : Fin r => ¬ p i = 1)
      have hsp := (Finset.sum_filter_add_sum_filter_not Low (fun i : Fin r => p i = 1)
        (fun i => 3 * fac n 0 (p i) (q i))).symm
      rw [hsp]
      have hL1_card : L1.card ≤ 1 := by
        refine Finset.card_le_one.mpr fun a ha b hb => ?_
        exact hp_strict.injective ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
      have hsum1 : ∑ i ∈ L1, 3 * fac n 0 (p i) (q i) ≤ 3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) := by
        calc
          ∑ i ∈ L1, 3 * fac n 0 (p i) (q i)
              ≤ ∑ _i ∈ L1, (3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ)) :=
                Finset.sum_le_sum fun i _ => hε_bound i
          _ = (L1.card : ℝ) * (3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ)) := by simp
          _ ≤ 1 * (3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hL1_card) (by positivity)
          _ = 3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) := one_mul _
      have hL2_card : L2.card ≤ n := by
        have hsub : L2.image p ⊆ Finset.range n := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
          exact Finset.mem_range.mpr (by have := hp_lt_q i; have := hq_le i; omega)
        calc
          L2.card = (L2.image p).card := (Finset.card_image_of_injective _ hp_strict.injective).symm
          _ ≤ (Finset.range n).card := Finset.card_le_card hsub
          _ = n := Finset.card_range n
      have hsum2 : ∑ i ∈ L2, 3 * fac n 0 (p i) (q i) ≤ 24 * (M : ℝ) ^ 2 / (n : ℝ) := by
        have hterm : ∀ i ∈ L2, 3 * fac n 0 (p i) (q i) ≤ 24 * (M : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
          intro i hi
          have hiL := (Finset.mem_filter.mp hi).1
          have hne1 := (Finset.mem_filter.mp hi).2
          have hqi : q i ≤ n - 7 := (Finset.mem_filter.mp hiL).2
          have hp2 : 2 ≤ p i := by have := hp_pos i; omega
          have hsq := fac_zero_le_sq (n := n) hp2 (hp_lt_q i) (by omega) hM1 (ht_le_M i)
          have hring : 24 * (M : ℝ) ^ 2 / (n : ℝ) ^ 2 = 3 * (8 * (M : ℝ) ^ 2 / (n : ℝ) ^ 2) := by ring
          linarith
        calc
          ∑ i ∈ L2, 3 * fac n 0 (p i) (q i)
              ≤ ∑ _i ∈ L2, (24 * (M : ℝ) ^ 2 / (n : ℝ) ^ 2) := Finset.sum_le_sum hterm
          _ = (L2.card : ℝ) * (24 * (M : ℝ) ^ 2 / (n : ℝ) ^ 2) := by simp
          _ ≤ (n : ℝ) * (24 * (M : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hL2_card) (by positivity)
          _ = 24 * (M : ℝ) ^ 2 / (n : ℝ) := by
                have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
                field_simp [hn_ne]
      exact add_le_add hsum1 hsum2
    let s := Nat.sqrt n
    have hPart2 : ∑ i ∈ Low, 18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ)) ≤
        18 * (M : ℝ) * (s : ℝ) / ((n - 1 : ℕ) : ℝ) +
        18 * (M : ℝ) / ((s + 1 : ℕ) : ℝ) := by
      let S1 := Low.filter (fun i : Fin r => n - 1 - q i ≤ s)
      let S2 := Low.filter (fun i : Fin r => ¬ n - 1 - q i ≤ s)
      have hsp := (Finset.sum_filter_add_sum_filter_not Low (fun i : Fin r => n - 1 - q i ≤ s)
        (fun i => 18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ)))).symm
      rw [hsp]
      have hS1_card : S1.card ≤ s := by
        have hinj : Set.InjOn (fun i : Fin r => n - 1 - q i) (S1 : Set (Fin r)) := by
          intro a ha b hb heq
          dsimp only at heq
          have haq : q a ≤ n - 7 := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
          have hbq : q b ≤ n - 7 := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
          exact hq_strict.injective (by omega)
        have hsub : S1.image (fun i : Fin r => n - 1 - q i) ⊆ Finset.Icc 1 s := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
          have hqi : q i ≤ n - 7 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
          have hle : n - 1 - q i ≤ s := (Finset.mem_filter.mp hi).2
          exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
        calc
          S1.card = (S1.image (fun i : Fin r => n - 1 - q i)).card :=
            (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.Icc 1 s).card := Finset.card_le_card hsub
          _ = s := by rw [Nat.card_Icc]; omega
      have hS2_card : S2.card ≤ n - 1 := by
        have hsub : S2.image q ⊆ Finset.range (n - 1) := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
          have hqi : q i ≤ n - 7 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
          exact Finset.mem_range.mpr (by omega)
        calc
          S2.card = (S2.image q).card := (Finset.card_image_of_injective _ hq_strict.injective).symm
          _ ≤ (Finset.range (n - 1)).card := Finset.card_le_card hsub
          _ = n - 1 := Finset.card_range (n - 1)
      have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hsum1 : ∑ i ∈ S1, 18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ)) ≤
          18 * (M : ℝ) * (s : ℝ) / ((n - 1 : ℕ) : ℝ) := by
        calc
          ∑ i ∈ S1, 18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ))
              ≤ ∑ _i ∈ S1, 18 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) := by
                refine Finset.sum_le_sum fun i hi => ?_
                have hqi : q i ≤ n - 7 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
                have hge1 : (1 : ℝ) ≤ ((n - 1 - q i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - 1 - q i)
                have hden : ((n - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ) := by
                  calc ((n - 1 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) * 1 := (mul_one _).symm
                    _ ≤ ((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ) :=
                      mul_le_mul_of_nonneg_left hge1 (le_of_lt hn1_pos)
                exact div_le_div_of_nonneg_left (by positivity) hn1_pos hden
          _ = (S1.card : ℝ) * (18 * (M : ℝ) / ((n - 1 : ℕ) : ℝ)) := by simp
          _ ≤ (s : ℝ) * (18 * (M : ℝ) / ((n - 1 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hS1_card) (by positivity)
          _ = 18 * (M : ℝ) * (s : ℝ) / ((n - 1 : ℕ) : ℝ) := by ring
      have hsum2 : ∑ i ∈ S2, 18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ)) ≤
          18 * (M : ℝ) / ((s + 1 : ℕ) : ℝ) := by
        have hs1_pos : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        calc
          ∑ i ∈ S2, 18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ))
              ≤ ∑ _i ∈ S2, 18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) := by
                refine Finset.sum_le_sum fun i hi => ?_
                have hgt : s + 1 ≤ n - 1 - q i := by
                  have := (Finset.mem_filter.mp hi).2; omega
                have hge : ((s + 1 : ℕ) : ℝ) ≤ ((n - 1 - q i : ℕ) : ℝ) := by exact_mod_cast hgt
                have hden : ((n - 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) ≤
                    ((n - 1 : ℕ) : ℝ) * ((n - 1 - q i : ℕ) : ℝ) :=
                  mul_le_mul_of_nonneg_left hge (le_of_lt hn1_pos)
                exact div_le_div_of_nonneg_left (by positivity) (mul_pos hn1_pos hs1_pos) hden
          _ = (S2.card : ℝ) * (18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ))) := by simp
          _ ≤ ((n - 1 : ℕ) : ℝ) * (18 * (M : ℝ) / (((n - 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hS2_card) (by positivity)
          _ = 18 * (M : ℝ) / ((s + 1 : ℕ) : ℝ) := by
                have hne : ((n - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn1_pos
                field_simp [hne]
      exact add_le_add hsum1 hsum2
    have hAll := hTail_prop (3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ)) (by positivity) fun i _ => hε_bound i
    calc
      ∑ i : Fin r, dp i ≤ 4096 * ((∑ i ∈ Low, dp i) + 3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ)) := hAll
      _ ≤ 4096 * ((3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) + 24 * (M : ℝ) ^ 2 / (n : ℝ)) +
            (18 * (M : ℝ) * (s : ℝ) / ((n - 1 : ℕ) : ℝ) + 18 * (M : ℝ) / ((s + 1 : ℕ) : ℝ)) +
            3 * (M : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
            have hLow_tot := le_trans hLow_rec (add_le_add hPart1 hPart2)
            linarith
      _ = 4096 * (6 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) + 24 * (M : ℝ) ^ 2 / (n : ℝ) +
            18 * (M : ℝ) * (Nat.sqrt n : ℝ) / ((n - 1 : ℕ) : ℝ) +
            18 * (M : ℝ) / ((Nat.sqrt n + 1 : ℕ) : ℝ)) := by ring

/-- Core DP reduction for the permutation average of `4^|U(v ∘ σ)| - 1` on a monotone non-constant `v`. -/
private lemma perm_avg_Uset_dp_bounds {n : ℕ} (hn : 10 ≤ n) (v : Fin n → Fin (n + 1))
    (hv : Monotone v) (hnc : minH (by omega) v < maxH (by omega) v) :
    ((∑ σ : Equiv.Perm (Fin n), ((4 ^ (Uset (by omega) (v ∘ σ)).card - 1 : ℕ) : ℝ)) / (n ! : ℝ) ≤ 36864) ∧
    (∀ M : ℕ, 16 ≤ n → 1 ≤ M →
      (∀ u : Fin (n + 1), (Finset.univ.filter (fun c : Fin n => v c = u)).card ≤ M) →
      (∑ σ : Equiv.Perm (Fin n), ((4 ^ (Uset (by omega) (v ∘ σ)).card - 1 : ℕ) : ℝ)) / (n ! : ℝ) ≤
        4096 * (6 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) +
          24 * (M : ℝ) ^ 2 / (n : ℝ) +
          18 * (M : ℝ) * (Nat.sqrt n : ℝ) / ((n - 1 : ℕ) : ℝ) +
          18 * (M : ℝ) / ((Nat.sqrt n + 1 : ℕ) : ℝ))) := by
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  -- Distinct interior values of `v`
  let W : Finset ℕ := (Finset.univ.image (fun j : Fin n => (v j).1)).filter
    (fun m => minH hn0 v < m ∧ m < maxH hn0 v)
  let r := W.card
  let w : Fin r ↪o ℕ := W.orderEmbOfFin rfl
  let p : Fin r → ℕ := fun i => (Finset.univ.filter (fun j : Fin n => (v j).1 < w i)).card
  let q : Fin r → ℕ := fun i => (Finset.univ.filter (fun j : Fin n => (v j).1 ≤ w i)).card
  let t : Fin r → ℕ := fun i => q i - p i
  -- Basic structural properties of `w, p, q, t`
  have hw_mem : ∀ i : Fin r, w i ∈ W := fun i => Finset.orderEmbOfFin_mem W rfl i
  have hw_bounds : ∀ i : Fin r, minH hn0 v < w i ∧ w i < maxH hn0 v := fun i =>
    (Finset.mem_filter.mp (hw_mem i)).2
  have hp_iff : ∀ (m : ℕ) (j : Fin n),
      (v j).1 < m ↔ j.1 < (Finset.univ.filter (fun j' : Fin n => (v j').1 < m)).card := by
    intro m j
    have hdown : ∀ a b : Fin n, a ≤ b →
        b ∈ Finset.univ.filter (fun j' : Fin n => (v j').1 < m) →
        a ∈ Finset.univ.filter (fun j' : Fin n => (v j').1 < m) := by
      intro a b hle hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_lt (hv hle) (Finset.mem_filter.mp hb).2⟩
    have hEq := filter_eq_lt_card_of_downward _ hdown
    have hmem := Finset.ext_iff.mp hEq j
    simpa using hmem
  have hq_iff : ∀ (m : ℕ) (j : Fin n),
      (v j).1 ≤ m ↔ j.1 < (Finset.univ.filter (fun j' : Fin n => (v j').1 ≤ m)).card := by
    intro m j
    have hdown : ∀ a b : Fin n, a ≤ b →
        b ∈ Finset.univ.filter (fun j' : Fin n => (v j').1 ≤ m) →
        a ∈ Finset.univ.filter (fun j' : Fin n => (v j').1 ≤ m) := by
      intro a b hle hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        le_trans (hv hle) (Finset.mem_filter.mp hb).2⟩
    have hEq := filter_eq_lt_card_of_downward _ hdown
    have hmem := Finset.ext_iff.mp hEq j
    simpa using hmem
  have hp_pos : ∀ i : Fin r, 1 ≤ p i := by
    intro i
    have h0 : (v ⟨0, hn0⟩).1 < w i := by
      rw [← minH_of_monotone hn0 v hv]; exact (hw_bounds i).1
    have hmem := (hp_iff (w i) ⟨0, hn0⟩).mp h0
    dsimp at hmem
    change 1 ≤ (Finset.univ.filter (fun j' : Fin n => (v j').1 < w i)).card
    omega
  have hq_le : ∀ i : Fin r, q i ≤ n - 1 := by
    intro i
    have hlast : ¬ (v ⟨n - 1, by omega⟩).1 ≤ w i := by
      rw [← maxH_of_monotone hn0 v hv]; have := (hw_bounds i).2; omega
    have hnot : ¬ n - 1 < q i := fun hlt => hlast ((hq_iff (w i) ⟨n - 1, by omega⟩).mpr hlt)
    omega
  have hp_lt_q : ∀ i : Fin r, p i < q i := by
    intro i
    have hsub : Finset.univ.filter (fun j : Fin n => (v j).1 < w i) ⊂
        Finset.univ.filter (fun j : Fin n => (v j).1 ≤ w i) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt (Finset.mem_filter.mp hj).2⟩, ?_⟩
      intro heq
      rcases Finset.mem_image.mp (Finset.mem_filter.mp (hw_mem i)).1 with ⟨j₀, _, hj₀⟩
      have hm1 : j₀ ∈ Finset.univ.filter (fun j : Fin n => (v j).1 ≤ w i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_eq hj₀⟩
      rw [← heq] at hm1
      have := (Finset.mem_filter.mp hm1).2
      omega
    exact Finset.card_lt_card hsub
  have hq_le_p : ∀ {k i : Fin r}, k < i → q k ≤ p i := by
    intro k i hki
    have hwk : w k < w i := w.strictMono hki
    exact Finset.card_le_card fun j hj =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_lt (Finset.mem_filter.mp hj).2 hwk⟩
  have hp_strict : StrictMono p := fun k i hki => lt_of_lt_of_le (hp_lt_q k) (hq_le_p hki)
  have hq_strict : StrictMono q := fun k i hki => lt_of_le_of_lt (hq_le_p hki) (hp_lt_q i)
  have ht_eq_card : ∀ i : Fin r, t i = (Finset.univ.filter (fun j : Fin n => (v j).1 = w i)).card := by
    intro i
    have hdisj : Disjoint
        (Finset.univ.filter (fun j : Fin n => (v j).1 < w i))
        (Finset.univ.filter (fun j : Fin n => (v j).1 = w i)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have := (Finset.mem_filter.mp hj1).2
      have := (Finset.mem_filter.mp hj2).2
      omega
    have hunion : Finset.univ.filter (fun j : Fin n => (v j).1 ≤ w i) =
        Finset.univ.filter (fun j : Fin n => (v j).1 < w i) ∪
        Finset.univ.filter (fun j : Fin n => (v j).1 = w i) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]; omega
    have hcard := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    change q i = p i + _ at hcard
    dsimp only [t]; omega
  -- Key cycle property: every `m ∈ Uset (v ∘ σ)` lies in `W` and constrains `succPerm' σ`
  have hU_sub_W : ∀ σ : Equiv.Perm (Fin n), Uset hn0 (v ∘ σ) ⊆ W := by
    intro σ m hm
    have hmIoo := (Finset.mem_filter.mp hm).1
    have hno := (Finset.mem_filter.mp hm).2
    rw [minH_comp_perm, maxH_comp_perm] at hmIoo
    rcases Finset.mem_Ioo.mp hmIoo with ⟨hmlo, hmhi⟩
    refine Finset.mem_filter.mpr ⟨?_, hmlo, hmhi⟩
    by_contra hnotimg
    let P_m := Finset.univ.filter (fun j : Fin n => (v j).1 < m)
    have hPne : P_m.Nonempty := by
      refine ⟨⟨0, hn0⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rwa [← minH_of_monotone hn0 v hv]
    have hPneU : P_m ≠ Finset.univ := by
      intro hU
      have hmem : (⟨n - 1, by omega⟩ : Fin n) ∈ P_m := hU.symm ▸ Finset.mem_univ _
      have hlt := (Finset.mem_filter.mp hmem).2
      rw [← maxH_of_monotone hn0 v hv] at hlt
      omega
    rcases isSingleCycle_succPerm' hn0 σ P_m hPne hPneU with ⟨j, hjP, hfj⟩
    have hj_lt : (v j).1 < m := (Finset.mem_filter.mp hjP).2
    have hfj_ge : m ≤ (v (succPerm' hn0 σ j)).1 := by
      by_contra hlt; exact hfj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp hlt⟩)
    have hfj_ne : (v (succPerm' hn0 σ j)).1 ≠ m := fun heq =>
      hnotimg (Finset.mem_image.mpr ⟨succPerm' hn0 σ j, Finset.mem_univ _, heq⟩)
    apply hno
    refine ⟨σ.symm j, ?_, ?_⟩
    · simpa using hj_lt
    · change m < (v (σ (cNext hn0 (σ.symm j)))).1
      exact lt_of_le_of_ne hfj_ge hfj_ne.symm
  have hU_step : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin r),
      w i ∈ Uset hn0 (v ∘ σ) → ∀ j : Fin n, j.1 < p i → (succPerm' hn0 σ j).1 < q i := by
    intro σ i hmem j hjp
    have hno := (Finset.mem_filter.mp hmem).2
    have hjlt : (v j).1 < w i := (hp_iff (w i) j).mpr hjp
    apply (hq_iff (w i) (succPerm' hn0 σ j)).mp
    by_contra hgt
    apply hno
    refine ⟨σ.symm j, ?_, ?_⟩
    · simpa using hjlt
    · change w i < (v (σ (cNext hn0 (σ.symm j)))).1
      exact not_le.mp hgt
  -- Expand `∑ σ, (4^|U(v ∘ σ)| - 1)` over nonempty subsets `A : Finset (Fin r)`
  let NE : Finset (Finset (Fin r)) := Finset.univ.filter Finset.Nonempty
  have hExpand :
      (∑ σ : Equiv.Perm (Fin n), ((4 ^ (Uset hn0 (v ∘ σ)).card - 1 : ℕ) : ℝ)) =
        ∑ A ∈ NE, (3 : ℝ) ^ A.card *
          ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ A, w i ∈ Uset hn0 (v ∘ σ))).card : ℝ) := by
    have hper : ∀ σ : Equiv.Perm (Fin n),
        ((4 ^ (Uset hn0 (v ∘ σ)).card - 1 : ℕ) : ℝ) =
          ∑ A ∈ NE, if (∀ i ∈ A, w i ∈ Uset hn0 (v ∘ σ)) then (3 : ℝ) ^ A.card else 0 := by
      intro σ
      let S : Finset (Fin r) := Finset.univ.filter (fun i : Fin r => w i ∈ Uset hn0 (v ∘ σ))
      have hScard : S.card = (Uset hn0 (v ∘ σ)).card := by
        have himg : S.image w = Uset hn0 (v ∘ σ) := by
          ext m
          simp only [Finset.mem_image, S, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, rfl⟩; exact hi
          · intro hm
            have hmW : m ∈ (W : Set ℕ) := hU_sub_W σ hm
            rw [← Finset.range_orderEmbOfFin W rfl] at hmW
            rcases hmW with ⟨i, rfl⟩
            exact ⟨i, hm, rfl⟩
        rw [← himg, Finset.card_image_of_injective _ w.injective]
      rw [← hScard, four_pow_sub_one_eq_sum_powerset]
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext A
      simp only [Finset.mem_filter, Finset.mem_powerset, NE, Finset.mem_univ, true_and, S]
      constructor
      · rintro ⟨hsub, hne⟩; exact ⟨hne, fun i hi => (Finset.mem_filter.mp (hsub hi)).2⟩
      · rintro ⟨hne, hall⟩; exact ⟨fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall i hi⟩, hne⟩
    simp_rw [hper]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Define `Q_A` and `weight A` for nonempty `A : Finset (Fin r)`
  let QA : Finset (Fin r) → ℕ → ℕ := fun A j =>
    if h : (A.filter (fun i => j < p i)).Nonempty then q ((A.filter (fun i => j < p i)).min' h) else n
  let weight : Finset (Fin r) → ℝ := fun A =>
    (3 : ℝ) ^ A.card *
      ∏ j ∈ Finset.range (n - 1),
        (((QA A j - j - 1 : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ))
  -- Bound the fraction of permutations matching `A` by the product in `weight A`
  have hCount_le : ∀ A ∈ NE,
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ A, w i ∈ Uset hn0 (v ∘ σ))).card : ℝ) /
        (n ! : ℝ) ≤
        ∏ j ∈ Finset.range (n - 1),
          (((QA A j - j - 1 : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ)) := by
    intro A _
    have hQ_mono : Monotone (fun j : Fin n => QA A j.1) := by
      intro j₁ j₂ hle
      dsimp only [QA]
      split_ifs with h1 h2 h2
      · have hsub : A.filter (fun i => j₂.1 < p i) ⊆ A.filter (fun i => j₁.1 < p i) := by
          intro i hi
          rcases Finset.mem_filter.mp hi with ⟨hiA, hlt⟩
          exact Finset.mem_filter.mpr ⟨hiA, lt_of_le_of_lt hle hlt⟩
        have hmin : (A.filter (fun i => j₁.1 < p i)).min' h1 ≤
            (A.filter (fun i => j₂.1 < p i)).min' h2 :=
          Finset.min'_le _ _ (hsub (Finset.min'_mem _ h2))
        exact hq_strict.monotone hmin
      · exact le_trans (hq_le _) (by omega)
      · exfalso
        rcases h2 with ⟨i, hi⟩
        rcases Finset.mem_filter.mp hi with ⟨hiA, hlt⟩
        exact h1 ⟨i, Finset.mem_filter.mpr ⟨hiA, lt_of_le_of_lt hle hlt⟩⟩
      · exact le_rfl
    have hQ_gt : ∀ j : Fin n, j.1 + 1 < n → j.1 + 1 < QA A j.1 := by
      intro j hj
      dsimp only [QA]
      split_ifs with h1
      · have hmem := Finset.mem_filter.mp (Finset.min'_mem _ h1)
        have := hp_lt_q ((A.filter (fun i => j.1 < p i)).min' h1)
        omega
      · exact hj
    have hQ_le : ∀ j : Fin n, QA A j.1 ≤ n := by
      intro j; dsimp only [QA]; split_ifs with h1
      · exact le_trans (hq_le _) (by omega)
      · exact le_rfl
    let GoodA := Finset.univ.filter (fun f : Equiv.Perm (Fin n) =>
      IsSingleCycle f ∧ ∀ j : Fin n, j.1 + 1 < n → (f j).1 < QA A j.1)
    let PermA := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ A, w i ∈ Uset hn0 (v ∘ σ))
    have hPermA_le : PermA.card ≤ n * GoodA.card := by
      let enc : Equiv.Perm (Fin n) → Fin n × Equiv.Perm (Fin n) := fun σ => (σ ⟨0, hn0⟩, succPerm' hn0 σ)
      have hinj : Function.Injective enc := fun σ₁ σ₂ h =>
        succPerm'_inj_with_zero hn0 σ₁ σ₂ (congrArg Prod.fst h) (congrArg Prod.snd h)
      have hsub : PermA.image enc ⊆ Finset.univ ×ˢ GoodA := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨σ, hσ, rfl⟩
        have hσA := (Finset.mem_filter.mp hσ).2
        refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          isSingleCycle_succPerm' hn0 σ, fun j _ => ?_⟩⟩
        dsimp only [QA]
        split_ifs with h1
        · have hmem := Finset.mem_filter.mp (Finset.min'_mem _ h1)
          exact hU_step σ _ (hσA _ hmem.1) j hmem.2
        · exact (succPerm' hn0 σ j).isLt
      calc
        PermA.card = (PermA.image enc).card := (Finset.card_image_of_injective _ hinj).symm
        _ ≤ (Finset.univ ×ˢ GoodA).card := Finset.card_le_card hsub
        _ = n * GoodA.card := by simp [Finset.card_product]
    have hGoodA_le := card_constrained_singleCycles_le hn2 (fun j : Fin n => QA A j.1) hQ_mono hQ_gt hQ_le
    have hProd_eq :
        (∏ j : Fin (n - 1), (QA A j.1 - j.1 - 1)) =
        ∏ j ∈ Finset.range (n - 1), (QA A j - j - 1) :=
      Fin.prod_univ_eq_prod_range (fun j => QA A j - j - 1) (n - 1)
    have hFac_eq : (n ! : ℝ) = (n : ℝ) * ∏ j ∈ Finset.range (n - 1), ((n - 1 - j : ℕ) : ℝ) := by
      have h1 : n ! = n * (n - 1) ! := by
        cases n with
        | zero => omega
        | succ m => simp [Nat.factorial_succ]
      rw [h1, ← prod_sub_eq_factorial (n - 1)]
      push_cast
      rfl
    have hle_nat : PermA.card ≤ n * ∏ j ∈ Finset.range (n - 1), (QA A j - j - 1) := by
      calc PermA.card ≤ n * GoodA.card := hPermA_le
        _ ≤ n * ∏ j : Fin (n - 1), (QA A j.1 - j.1 - 1) :=
          Nat.mul_le_mul_left _ hGoodA_le
        _ = _ := by rw [hProd_eq]
    have hle_real : (PermA.card : ℝ) ≤
        (n : ℝ) * ∏ j ∈ Finset.range (n - 1), ((QA A j - j - 1 : ℕ) : ℝ) := by
      exact_mod_cast hle_nat
    have hnfac_pos : (0 : ℝ) < (n ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Finset.prod_div_distrib]
    calc
      (PermA.card : ℝ) / (n ! : ℝ)
          ≤ ((n : ℝ) * ∏ j ∈ Finset.range (n - 1), ((QA A j - j - 1 : ℕ) : ℝ)) /
              ((n : ℝ) * ∏ j ∈ Finset.range (n - 1), ((n - 1 - j : ℕ) : ℝ)) := by
            rw [← hFac_eq]
            exact div_le_div_of_nonneg_right hle_real (le_of_lt hnfac_pos)
      _ = (∏ j ∈ Finset.range (n - 1), ((QA A j - j - 1 : ℕ) : ℝ)) /
            (∏ j ∈ Finset.range (n - 1), ((n - 1 - j : ℕ) : ℝ)) :=
          mul_div_mul_left _ _ hn_ne
  -- Define `dp i` as the fiber sum of `weight A` over nonempty `A` with `max' A = i`
  let dp : Fin r → ℝ := fun i =>
    ∑ A ∈ NE.filter (fun A => ∃ hne : A.Nonempty, A.max' hne = i), weight A
  have hdp_nonneg : ∀ i : Fin r, 0 ≤ dp i := fun i =>
    Finset.sum_nonneg fun A _ => mul_nonneg (by positivity)
      (Finset.prod_nonneg fun j _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hAvg_le_dp :
      (∑ σ : Equiv.Perm (Fin n), ((4 ^ (Uset hn0 (v ∘ σ)).card - 1 : ℕ) : ℝ)) / (n ! : ℝ) ≤
        ∑ i : Fin r, dp i := by
    rw [hExpand, Finset.sum_div]
    have hstep1 :
        ∑ A ∈ NE, ((3 : ℝ) ^ A.card *
          ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ A, w i ∈ Uset hn0 (v ∘ σ))).card : ℝ)) /
          (n ! : ℝ) ≤ ∑ A ∈ NE, weight A := by
      refine Finset.sum_le_sum fun A hA => ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hCount_le A hA) (by positivity)
    refine le_trans hstep1 (le_of_eq ?_)
    -- Partition `NE` by `A.max'`
    have hpart : NE = Finset.univ.biUnion (fun i : Fin r =>
        NE.filter (fun A => ∃ hne : A.Nonempty, A.max' hne = i)) := by
      ext A
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, NE]
      constructor
      · intro hne; exact ⟨A.max' hne, hne, hne, rfl⟩
      · rintro ⟨_, hne, _, _⟩; exact hne
    conv_lhs => rw [hpart]
    rw [Finset.sum_biUnion]
    intro i₁ _ i₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro A hA1 hA2
    rcases (Finset.mem_filter.mp hA1).2 with ⟨hne1, h1⟩
    rcases (Finset.mem_filter.mp hA2).2 with ⟨hne2, h2⟩
    exact hne (h1.symm.trans h2)
  -- Helper: evaluate `weight {i}` and `weight (insert i A')` for `A'` with `max' A' = k < i`
  have hweight_singleton : ∀ i : Fin r, weight {i} = 3 * fac n 0 (p i) (q i) := by
    intro i
    dsimp only [weight]
    simp only [Finset.card_singleton, pow_one]
    congr 1
    have hsplit : Finset.range (n - 1) = Finset.Ico 0 (p i) ∪ Finset.Ico (p i) (n - 1) := by
      have hple : p i ≤ n - 1 := le_trans (le_of_lt (hp_lt_q i)) (hq_le i)
      ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.Ico 0 (p i)) (Finset.Ico (p i) (n - 1)) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      have := (Finset.mem_Ico.mp h1).2; have := (Finset.mem_Ico.mp h2).1; omega
    rw [hsplit, Finset.prod_union hdisj]
    have hfirst : (∏ j ∈ Finset.Ico 0 (p i),
        (((QA {i} j - j - 1 : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ))) = fac n 0 (p i) (q i) := by
      unfold fac
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjlt : j < p i := (Finset.mem_Ico.mp hj).2
      have hfilt : ({i} : Finset (Fin r)).filter (fun x => j < p x) = {i} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hjlt⟩⟩
      have hQA : QA {i} j = q i := by
        dsimp only [QA]
        have hne : (({i} : Finset (Fin r)).filter (fun x => j < p x)).Nonempty := by
          rw [hfilt]; exact Finset.singleton_nonempty i
        rw [dif_pos hne]
        have hmem : (({i} : Finset (Fin r)).filter (fun x => j < p x)).min' hne ∈ ({i} : Finset (Fin r)) :=
          (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
        rw [Finset.mem_singleton.mp hmem]
      rw [hQA, show q i - j - 1 = q i - 1 - j by omega]
    have hsecond : (∏ j ∈ Finset.Ico (p i) (n - 1),
        (((QA {i} j - j - 1 : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ))) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have hjge : p i ≤ j := (Finset.mem_Ico.mp hj).1
      have hjlt : j < n - 1 := (Finset.mem_Ico.mp hj).2
      have hQA : QA {i} j = n := by
        dsimp only [QA]
        have hnot : ¬ (({i} : Finset (Fin r)).filter (fun x => j < p x)).Nonempty := by
          rintro ⟨x, hx⟩
          rcases Finset.mem_filter.mp hx with ⟨hx1, hx2⟩
          rw [Finset.mem_singleton.mp hx1] at hx2
          omega
        rw [dif_neg hnot]
      rw [hQA, show n - j - 1 = n - 1 - j by omega]
      exact div_self (Nat.cast_ne_zero.mpr (by omega))
    rw [hfirst, hsecond, mul_one]
  have hweight_insert : ∀ (A' : Finset (Fin r)) (hne : A'.Nonempty) (i : Fin r),
      A'.max' hne < i →
      weight (insert i A') = 3 * weight A' * fac n (p (A'.max' hne)) (p i) (q i) := by
    intro A' hne i hlt
    let k := A'.max' hne
    have hnot : i ∉ A' := fun hi => not_lt_of_ge (Finset.le_max' A' i hi) hlt
    have hpk_lt_pi : p k < p i := hp_strict hlt
    have hpi_le : p i ≤ n - 1 := le_trans (le_of_lt (hp_lt_q i)) (hq_le i)
    have hsplit : Finset.range (n - 1) =
        Finset.Ico 0 (p k) ∪ Finset.Ico (p k) (p i) ∪ Finset.Ico (p i) (n - 1) := by
      ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj1 : Disjoint (Finset.Ico 0 (p k)) (Finset.Ico (p k) (p i)) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      have := (Finset.mem_Ico.mp h1).2; have := (Finset.mem_Ico.mp h2).1; omega
    have hdisj2 : Disjoint (Finset.Ico 0 (p k) ∪ Finset.Ico (p k) (p i)) (Finset.Ico (p i) (n - 1)) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp only [Finset.mem_union, Finset.mem_Ico] at h1
      have := (Finset.mem_Ico.mp h2).1; omega
    -- Compare `QA (insert i A')` vs `QA A'` on each of the 3 intervals
    have hQA_left : ∀ j < p k, QA (insert i A') j = QA A' j := by
      intro j hjlt
      dsimp only [QA]
      have hk_in : k ∈ A'.filter (fun x => j < p x) :=
        Finset.mem_filter.mpr ⟨Finset.max'_mem A' hne, hjlt⟩
      have hne1 : (A'.filter (fun x => j < p x)).Nonempty := ⟨k, hk_in⟩
      have hne2 : ((insert i A').filter (fun x => j < p x)).Nonempty :=
        ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (Finset.max'_mem A' hne), hjlt⟩⟩
      rw [dif_pos hne2, dif_pos hne1]
      congr 1
      apply le_antisymm
      · refine Finset.min'_le _ _ ?_
        have hm := Finset.mem_filter.mp (Finset.min'_mem _ hne1)
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hm.1, hm.2⟩
      · have hm := Finset.mem_filter.mp (Finset.min'_mem _ hne2)
        rcases Finset.mem_insert.mp hm.1 with heq | hmemA'
        · have hle : ((insert i A').filter (fun x => j < p x)).min' hne2 ≤ k :=
            Finset.min'_le _ k (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (Finset.max'_mem A' hne), hjlt⟩)
          rw [heq] at hle
          exact absurd hlt (not_lt_of_ge hle)
        · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hmemA', hm.2⟩)
    have hQA_mid_ins : ∀ j, p k ≤ j → j < p i → QA (insert i A') j = q i := by
      intro j hge hltj
      dsimp only [QA]
      have hfilt : (insert i A').filter (fun x => j < p x) = {i} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | hxA', hxp⟩
          · rfl
          · have hpx : p x ≤ p k := hp_strict.monotone (Finset.le_max' A' x hxA')
            omega
        · rintro rfl; exact ⟨Or.inl rfl, hltj⟩
      have hne2 : ((insert i A').filter (fun x => j < p x)).Nonempty := by
        rw [hfilt]; exact Finset.singleton_nonempty i
      rw [dif_pos hne2]
      have hmem : ((insert i A').filter (fun x => j < p x)).min' hne2 ∈ ({i} : Finset (Fin r)) := by
        rw [← hfilt]; exact Finset.min'_mem _ hne2
      rw [Finset.mem_singleton.mp hmem]
    have hQA_ge_A' : ∀ j, p k ≤ j → QA A' j = n := by
      intro j hge
      dsimp only [QA]
      have hnot2 : ¬ (A'.filter (fun x => j < p x)).Nonempty := by
        rintro ⟨x, hx⟩
        rcases Finset.mem_filter.mp hx with ⟨hxA', hxp⟩
        have hpx : p x ≤ p k := hp_strict.monotone (Finset.le_max' A' x hxA')
        omega
      rw [dif_neg hnot2]
    have hQA_right_ins : ∀ j, p i ≤ j → QA (insert i A') j = n := by
      intro j hge
      dsimp only [QA]
      have hnot2 : ¬ ((insert i A').filter (fun x => j < p x)).Nonempty := by
        rintro ⟨x, hx⟩
        rcases Finset.mem_filter.mp hx with ⟨hxI, hxp⟩
        rcases Finset.mem_insert.mp hxI with rfl | hxA'
        · omega
        · have hpx : p x ≤ p k := hp_strict.monotone (Finset.le_max' A' x hxA')
          omega
      rw [dif_neg hnot2]
    dsimp only [weight]
    rw [Finset.card_insert_of_notMem hnot, pow_succ', hsplit,
      Finset.prod_union hdisj2, Finset.prod_union hdisj1,
      Finset.prod_union hdisj2, Finset.prod_union hdisj1]
    have hL :
        (∏ j ∈ Finset.Ico 0 (p k), (((QA (insert i A') j - j - 1 : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ))) =
        (∏ j ∈ Finset.Ico 0 (p k), (((QA A' j - j - 1 : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ))) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [hQA_left j (Finset.mem_Ico.mp hj).2]
    have hM_ins :
        (∏ j ∈ Finset.Ico (p k) (p i), (((QA (insert i A') j - j - 1 : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ))) =
        fac n (p k) (p i) (q i) := by
      unfold fac
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [hQA_mid_ins j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2,
        show q i - j - 1 = q i - 1 - j by omega]
    have hM_A' :
        (∏ j ∈ Finset.Ico (p k) (p i), (((QA A' j - j - 1 : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ))) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      rw [hQA_ge_A' j (Finset.mem_Ico.mp hj).1, show n - j - 1 = n - 1 - j by omega]
      exact div_self (Nat.cast_ne_zero.mpr (by have := (Finset.mem_Ico.mp hj).2; omega))
    have hR_ins :
        (∏ j ∈ Finset.Ico (p i) (n - 1), (((QA (insert i A') j - j - 1 : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ))) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      rw [hQA_right_ins j (Finset.mem_Ico.mp hj).1, show n - j - 1 = n - 1 - j by omega]
      exact div_self (Nat.cast_ne_zero.mpr (by have := (Finset.mem_Ico.mp hj).2; omega))
    have hR_A' :
        (∏ j ∈ Finset.Ico (p i) (n - 1), (((QA A' j - j - 1 : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ))) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have hge : p k ≤ j := le_trans (le_of_lt hpk_lt_pi) (Finset.mem_Ico.mp hj).1
      rw [hQA_ge_A' j hge, show n - j - 1 = n - 1 - j by omega]
      exact div_self (Nat.cast_ne_zero.mpr (by have := (Finset.mem_Ico.mp hj).2; omega))
    rw [hL, hM_ins, hM_A', hR_ins, hR_A']
    ring
  -- Prove the DP recurrence for `dp i`
  have hdp_rec : ∀ i : Fin r,
      dp i = 3 * fac n 0 (p i) (q i) +
        3 * ∑ k ∈ Finset.univ.filter (fun k : Fin r => k < i), dp k * fac n (p k) (p i) (q i) := by
    intro i
    let F_i := NE.filter (fun A => ∃ hne : A.Nonempty, A.max' hne = i)
    let Rest := F_i.erase {i}
    have hsing_mem : ({i} : Finset (Fin r)) ∈ F_i :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.singleton_nonempty i⟩,
        Finset.singleton_nonempty i, Finset.max'_singleton i⟩
    have hsplit : F_i = insert {i} Rest := (Finset.insert_erase hsing_mem).symm
    dsimp only [dp]
    change ∑ A ∈ F_i, weight A = _
    rw [hsplit, Finset.sum_insert (Finset.notMem_erase _ _), hweight_singleton i]
    congr 1
    -- Bijection between `Rest` and pairs `(k < i, A' with max' A' = k)` via `A' ↦ insert i A'`
    let LowI := Finset.univ.filter (fun k : Fin r => k < i)
    have hRest_eq : Rest = LowI.biUnion (fun k =>
        (NE.filter (fun A' => ∃ hne : A'.Nonempty, A'.max' hne = k)).image (insert i)) := by
      ext A
      simp only [Rest, F_i, LowI, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_image, NE]
      constructor
      · rintro ⟨hneS, hneA, hneA', hmaxA⟩
        let A' := A.erase i
        have hiA : i ∈ A := hmaxA ▸ Finset.max'_mem A hneA'
        have hne_er : A'.Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty] at hempty
          apply hneS
          have : A = insert i A' := (Finset.insert_erase hiA).symm
          rw [this, hempty]
          rfl
        let k := A'.max' hne_er
        have hk_lt : k < i := by
          have hkA' := Finset.max'_mem A' hne_er
          have hkne := (Finset.mem_erase.mp hkA').1
          have hkA := (Finset.mem_erase.mp hkA').2
          exact lt_of_le_of_ne (hmaxA ▸ Finset.le_max' A k hkA) hkne
        exact ⟨k, hk_lt, A', ⟨hne_er, hne_er, rfl⟩, Finset.insert_erase hiA⟩
      · rintro ⟨k, hki, A', ⟨hneA', _, hmaxA'⟩, rfl⟩
        have hnot : i ∉ A' := fun hi => not_lt_of_ge (hmaxA' ▸ Finset.le_max' A' i hi) hki
        have hneIns : (insert i A').Nonempty := Finset.insert_nonempty i A'
        have hmaxIns : (insert i A').max' hneIns = i := by
          apply le_antisymm
          · refine Finset.max'_le _ _ _ fun x hx => ?_
            rcases Finset.mem_insert.mp hx with rfl | hxA'
            · exact le_rfl
            · exact le_of_lt (lt_of_le_of_lt (hmaxA' ▸ Finset.le_max' A' x hxA') hki)
          · exact Finset.le_max' _ i (Finset.mem_insert_self i A')
        refine ⟨?_, hneIns, hneIns, hmaxIns⟩
        intro heq
        rcases hneA' with ⟨x, hx⟩
        have hxI : x ∈ insert i A' := Finset.mem_insert_of_mem hx
        rw [heq, Finset.mem_singleton] at hxI
        exact hnot (hxI ▸ hx)
    change ∑ A ∈ Rest, weight A = _
    rw [hRest_eq, Finset.sum_biUnion, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hki : k < i := (Finset.mem_filter.mp hk).2
      have hinj : Set.InjOn (insert i)
          (↑(NE.filter (fun A' => ∃ hne : A'.Nonempty, A'.max' hne = k)) : Set (Finset (Fin r))) := by
        intro A₁ hA₁ A₂ hA₂ heq
        rcases (Finset.mem_filter.mp hA₁).2 with ⟨hne1, hmax1⟩
        rcases (Finset.mem_filter.mp hA₂).2 with ⟨hne2, hmax2⟩
        have h1 : i ∉ A₁ := fun hi => not_lt_of_ge (hmax1 ▸ Finset.le_max' A₁ i hi) hki
        have h2 : i ∉ A₂ := fun hi => not_lt_of_ge (hmax2 ▸ Finset.le_max' A₂ i hi) hki
        have h' := congrArg (fun S => S.erase i) heq
        rwa [Finset.erase_insert h1, Finset.erase_insert h2] at h'
      rw [Finset.sum_image hinj, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun A' hA' => ?_
      rcases (Finset.mem_filter.mp hA').2 with ⟨hneA', hmaxA'⟩
      rw [hweight_insert A' hneA' i (hmaxA'.symm ▸ hki), hmaxA']
      ring
    · intro k₁ hk₁ k₂ hk₂ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro A hA1 hA2
      rcases Finset.mem_image.mp hA1 with ⟨A₁, h1, rfl⟩
      rcases Finset.mem_image.mp hA2 with ⟨A₂, h2, heq⟩
      have hk1i : k₁ < i := (Finset.mem_filter.mp hk₁).2
      have hk2i : k₂ < i := (Finset.mem_filter.mp hk₂).2
      rcases (Finset.mem_filter.mp h1).2 with ⟨hne1, hmax1⟩
      rcases (Finset.mem_filter.mp h2).2 with ⟨hne2, hmax2⟩
      have h1not : i ∉ A₁ := fun hi => not_lt_of_ge (hmax1 ▸ Finset.le_max' A₁ i hi) hk1i
      have h2not : i ∉ A₂ := fun hi => not_lt_of_ge (hmax2 ▸ Finset.le_max' A₂ i hi) hk2i
      have hAeq : A₁ = A₂ := by
        have h' := congrArg (fun S => S.erase i) heq
        rw [Finset.erase_insert h2not, Finset.erase_insert h1not] at h'
        exact h'.symm
      subst hAeq
      exact hne (hmax1.symm.trans hmax2)
  have hdp_bounds := dp_sum_bounds hn p q hp_pos hq_le hp_lt_q hq_le_p dp hdp_nonneg hdp_rec
  refine ⟨le_trans hAvg_le_dp hdp_bounds.1, ?_⟩
  intro M hn16 hM1 hM
  have ht_le_M : ∀ i : Fin r, q i - p i ≤ M := by
    intro i
    change t i ≤ M
    rw [ht_eq_card i]
    have hwi_le : w i < n + 1 := by
      have := (hw_bounds i).2; have := maxH_le_n hn0 v; omega
    have heq : Finset.univ.filter (fun j : Fin n => (v j).1 = w i) =
        Finset.univ.filter (fun j : Fin n => v j = ⟨w i, hwi_le⟩) := by
      ext j; simp [Fin.ext_iff]
    rw [heq]
    exact hM ⟨w i, hwi_le⟩
  exact le_trans hAvg_le_dp (hdp_bounds.2 M hn16 hM1 ht_le_M)

/-! ### Section 5: Vanishing of `errCount n / n^n` -/

private lemma card_range_maps (n a b : ℕ) (hb : b ≤ n) :
    (Finset.univ.filter (fun h : Fin n → Fin (n + 1) => ∀ c : Fin n, a ≤ (h c).1 ∧ (h c).1 ≤ b)).card =
      (Finset.Icc a b).card ^ n := by
  let S := Finset.univ.filter (fun h : Fin n → Fin (n + 1) => ∀ c : Fin n, a ≤ (h c).1 ∧ (h c).1 ≤ b)
  let e : { h : Fin n → Fin (n + 1) // h ∈ S } ≃ (Fin n → { x : ℕ // x ∈ Finset.Icc a b }) :=
    { toFun := fun ⟨h, hh⟩ c => ⟨(h c).1, Finset.mem_Icc.mpr ((Finset.mem_filter.mp hh).2 c)⟩
      invFun := fun f =>
        ⟨fun c => ⟨(f c).1, by have := (Finset.mem_Icc.mp (f c).2).2; omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c => Finset.mem_Icc.mp (f c).2⟩⟩
      left_inv := fun ⟨h, _⟩ => by apply Subtype.ext; funext c; ext; rfl
      right_inv := fun f => by funext c; ext; rfl }
  have h1 : S.card = Fintype.card { h : Fin n → Fin (n + 1) // h ∈ S } := (Fintype.card_coe S).symm
  rw [h1, Fintype.card_congr e, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]

private lemma one_add_div_pow_le_exp {n s : ℕ} (hs : s < n) :
    (((n + 1 - s : ℕ) : ℝ) / (n : ℝ)) ^ n ≤ Real.exp (1 - (s : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcast : ((n + 1 - s : ℕ) : ℝ) = (n : ℝ) + (1 - (s : ℝ)) := by
    have h1 : (n + 1 - s) + s = n + 1 := by omega
    have h2 : ((n + 1 - s : ℕ) : ℝ) + (s : ℝ) = (n : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hrew : ((n + 1 - s : ℕ) : ℝ) / (n : ℝ) = (1 - (s : ℝ)) / (n : ℝ) + 1 := by
    rw [hcast]
    field_simp [ne_of_gt hn_pos]
    ring
  have hle := Real.add_one_le_exp ((1 - (s : ℝ)) / (n : ℝ))
  have hnn : 0 ≤ ((n + 1 - s : ℕ) : ℝ) / (n : ℝ) := by positivity
  calc
    (((n + 1 - s : ℕ) : ℝ) / (n : ℝ)) ^ n
        ≤ (Real.exp ((1 - (s : ℝ)) / (n : ℝ))) ^ n := by
          rw [hrew]; exact pow_le_pow_left₀ (by rw [← hrew]; exact hnn) hle n
    _ = Real.exp ((n : ℝ) * ((1 - (s : ℝ)) / (n : ℝ))) := (Real.exp_nat_mul _ n).symm
    _ = Real.exp (1 - (s : ℝ)) := by rw [mul_div_cancel₀ _ (ne_of_gt hn_pos)]

private noncomputable def boundSeq (s : ℕ) : ℝ :=
  2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * Real.exp (1 - (s : ℝ))

private lemma boundSeq_nonneg (s : ℕ) : 0 ≤ boundSeq s := by
  unfold boundSeq; positivity

private lemma summable_boundSeq : Summable boundSeq := by
  have hr_lt : ‖(2 : ℝ) / Real.exp 1‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity), div_lt_one (Real.exp_pos 1)]
    linarith [Real.exp_one_gt_d9]
  have hsum0 : Summable (fun s : ℕ => ((2 : ℝ) / Real.exp 1) ^ s) :=
    summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9])
  have hsum1 : Summable (fun s : ℕ => (s : ℝ) ^ 1 * ((2 : ℝ) / Real.exp 1) ^ s) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr_lt
  have hcomb : Summable (fun s : ℕ => (2 * Real.exp 1) * ((s : ℝ) ^ 1 * ((2 : ℝ) / Real.exp 1) ^ s + ((2 : ℝ) / Real.exp 1) ^ s)) :=
    (hsum1.add hsum0).mul_left (2 * Real.exp 1)
  refine hcomb.congr fun s => ?_
  unfold boundSeq
  rw [Real.exp_sub, div_pow, ← Real.exp_nat_mul, mul_one, pow_one]
  push_cast
  have hexp_ne : Real.exp (s : ℝ) ≠ 0 := ne_of_gt (Real.exp_pos _)
  field_simp [hexp_ne]

private lemma pow_five_le_factorial {k : ℕ} (hk : 12 ≤ k) : k ^ 5 ≤ k ! := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => decide
  | succ d ih =>
    set m := 12 + d
    have hm : 12 ≤ m := by omega
    have h2 : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
    have h4 : (m + 1) ^ 4 ≤ m ^ 5 := by
      calc
        (m + 1) ^ 4 = ((m + 1) ^ 2) ^ 2 := by ring
        _ ≤ (2 * m ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
        _ = 4 * m ^ 4 := by ring
        _ ≤ m * m ^ 4 := Nat.mul_le_mul_right _ (by omega)
        _ = m ^ 5 := by ring
    calc
      (12 + (d + 1)) ^ 5 = (m + 1) * (m + 1) ^ 4 := by dsimp [m]; ring
      _ ≤ (m + 1) * m ^ 5 := Nat.mul_le_mul_left _ h4
      _ ≤ (m + 1) * m ! := Nat.mul_le_mul_left _ ih
      _ = (12 + (d + 1)) ! := by rw [show 12 + (d + 1) = m + 1 by omega, Nat.factorial_succ]

private lemma card_heavy_div_pow_le {n : ℕ} (hn : 14641 ≤ n) :
    let M := Nat.sqrt (Nat.sqrt n)
    ((Finset.univ.filter (fun h : Fin n → Fin (n + 1) =>
      ∃ u : Fin (n + 1), M < (Finset.univ.filter (fun c : Fin n => h c = u)).card)).card : ℝ) /
      (n : ℝ) ^ n ≤ Real.exp 1 / ((M + 1 : ℕ) : ℝ) := by
  intro M
  have hM_ge : 11 ≤ M := by
    have h1 : 121 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
    exact Nat.le_sqrt.mpr (by omega)
  have hM1_le_n : M + 1 ≤ n := by
    have h1 : M * M ≤ Nat.sqrt n := Nat.sqrt_le _
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le _
    have h3 : M + 1 ≤ M * M := by nlinarith [hM_ge]
    have h4 : Nat.sqrt n ≤ Nat.sqrt n * Nat.sqrt n := Nat.le_mul_self _
    omega
  let Heavy := Finset.univ.filter (fun h : Fin n → Fin (n + 1) =>
    ∃ u : Fin (n + 1), M < (Finset.univ.filter (fun c : Fin n => h c = u)).card)
  let Fix (u : Fin (n + 1)) (S : Finset (Fin n)) : Finset (Fin n → Fin (n + 1)) :=
    Finset.univ.filter (fun h => ∀ c ∈ S, h c = u)
  have hFix_card : ∀ (u : Fin (n + 1)) (S : Finset (Fin n)),
      (Fix u S).card = (n + 1) ^ (n - S.card) := by
    intro u S
    let e : { h : Fin n → Fin (n + 1) // h ∈ Fix u S } ≃ ({ c : Fin n // c ∉ S } → Fin (n + 1)) :=
      { toFun := fun ⟨h, _⟩ c => h c.1
        invFun := fun f =>
          ⟨fun c => if hc : c ∈ S then u else f ⟨c, hc⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c hc => dif_pos hc⟩⟩
        left_inv := fun ⟨h, hh⟩ => by
          apply Subtype.ext; funext c
          by_cases hc : c ∈ S
          · simp [hc, (Finset.mem_filter.mp hh).2 c hc]
          · simp [hc]
        right_inv := fun f => by funext ⟨c, hc⟩; simp [hc] }
    have h1 : (Fix u S).card = Fintype.card { h : Fin n → Fin (n + 1) // h ∈ Fix u S } :=
      (Fintype.card_coe _).symm
    have hcompl : Fintype.card { c : Fin n // c ∉ S } = n - S.card := by
      simp [Fintype.card_subtype_compl, Fintype.card_fin]
    rw [h1, Fintype.card_congr e, Fintype.card_fun, hcompl, Fintype.card_fin]
  have hsub : Heavy ⊆
      ((Finset.univ : Finset (Fin (n + 1))) ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard (M + 1)).biUnion (fun p => Fix p.1 p.2) := by
    intro h hh
    rcases (Finset.mem_filter.mp hh).2 with ⟨u, hgt⟩
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hgt)
    refine Finset.mem_biUnion.mpr ⟨(u, S), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c hc => ?_⟩
      exact (Finset.mem_filter.mp (hSsub hc)).2
  have hHeavy_nat : Heavy.card ≤ (n + 1) * n.choose (M + 1) * (n + 1) ^ (n - (M + 1)) := by
    calc
      Heavy.card
          ≤ (((Finset.univ : Finset (Fin (n + 1))) ×ˢ
              (Finset.univ : Finset (Fin n)).powersetCard (M + 1)).biUnion (fun p => Fix p.1 p.2)).card :=
            Finset.card_le_card hsub
      _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin (n + 1))) ×ˢ
              (Finset.univ : Finset (Fin n)).powersetCard (M + 1), (Fix p.1 p.2).card :=
            Finset.card_biUnion_le
      _ = ∑ p ∈ (Finset.univ : Finset (Fin (n + 1))) ×ˢ
              (Finset.univ : Finset (Fin n)).powersetCard (M + 1), (n + 1) ^ (n - (M + 1)) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [hFix_card, (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).2).2]
      _ = ((n + 1) * n.choose (M + 1)) * (n + 1) ^ (n - (M + 1)) := by
            simp [Finset.card_product, Finset.card_powersetCard, Fintype.card_fin]
  have hchoose_le : (n.choose (M + 1) : ℝ) ≤ (n : ℝ) ^ (M + 1) / (((M + 1) ! : ℕ) : ℝ) := by
    have hnat : (M + 1)! * n.choose (M + 1) ≤ n ^ (M + 1) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow n (M + 1)
    have hreal : (((M + 1)! : ℕ) : ℝ) * (n.choose (M + 1) : ℝ) ≤ (n : ℝ) ^ (M + 1) := by
      exact_mod_cast hnat
    rw [le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _)), mul_comm]
    exact hreal
  have hpow_exp : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (n - (M + 1)) ≤ Real.exp 1 := by
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
      rw [one_le_div (Nat.cast_pos.mpr (by omega))]; exact_mod_cast (by omega : n ≤ n + 1)
    have h2 : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (n - (M + 1)) ≤ (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n :=
      pow_le_pow_right₀ h1 (Nat.sub_le n (M + 1))
    have h3 := one_add_div_pow_le_exp (n := n) (s := 0) (by omega)
    simpa using le_trans h2 h3
  have hn_lt_M4 : n + 1 ≤ (M + 1) ^ 4 := by
    have h1 : n < (Nat.sqrt n + 1) ^ 2 := by
      simpa [sq] using Nat.lt_succ_sqrt n
    have h2 : Nat.sqrt n < (M + 1) ^ 2 := by
      simpa [sq] using Nat.lt_succ_sqrt (Nat.sqrt n)
    have h3 : Nat.sqrt n + 1 ≤ (M + 1) ^ 2 := Nat.succ_le_of_lt h2
    have h4 : (Nat.sqrt n + 1) ^ 2 ≤ ((M + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h3 2
    have h5 : ((M + 1) ^ 2) ^ 2 = (M + 1) ^ 4 := by ring
    omega
  have hfac_ge : (M + 1) ^ 5 ≤ (M + 1) ! := pow_five_le_factorial (by omega)
  have hratio_le : ((n + 1 : ℕ) : ℝ) / (((M + 1) ! : ℕ) : ℝ) ≤ 1 / ((M + 1 : ℕ) : ℝ) := by
    have h1 : ((n + 1 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) ^ 4 := by exact_mod_cast hn_lt_M4
    have h2 : ((M + 1 : ℕ) : ℝ) ^ 5 ≤ (((M + 1) ! : ℕ) : ℝ) := by exact_mod_cast hfac_ge
    have hpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    calc
      ((n + 1 : ℕ) : ℝ) / (((M + 1) ! : ℕ) : ℝ)
          ≤ ((M + 1 : ℕ) : ℝ) ^ 4 / ((M + 1 : ℕ) : ℝ) ^ 5 :=
            div_le_div₀ (by positivity) h1 (by positivity) h2
      _ = 1 / ((M + 1 : ℕ) : ℝ) := by field_simp [ne_of_gt hpos]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hHeavy_real : (Heavy.card : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) * (n.choose (M + 1) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (n - (M + 1)) := by
    exact_mod_cast hHeavy_nat
  have hnpow_split : (n : ℝ) ^ n = (n : ℝ) ^ (M + 1) * (n : ℝ) ^ (n - (M + 1)) := by
    rw [← pow_add, Nat.add_sub_cancel' hM1_le_n]
  calc
    (Heavy.card : ℝ) / (n : ℝ) ^ n
        ≤ (((n + 1 : ℕ) : ℝ) * (n.choose (M + 1) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (n - (M + 1))) /
            ((n : ℝ) ^ (M + 1) * (n : ℝ) ^ (n - (M + 1))) := by
          rw [← hnpow_split]; exact div_le_div_of_nonneg_right hHeavy_real (by positivity)
    _ = ((n + 1 : ℕ) : ℝ) * ((n.choose (M + 1) : ℝ) / (n : ℝ) ^ (M + 1)) *
          (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (n - (M + 1)) := by
          rw [div_pow]; ring
    _ ≤ ((n + 1 : ℕ) : ℝ) * (1 / (((M + 1) ! : ℕ) : ℝ)) * Real.exp 1 := by
          have hc1 : (n.choose (M + 1) : ℝ) / (n : ℝ) ^ (M + 1) ≤ 1 / (((M + 1) ! : ℕ) : ℝ) := by
            rw [div_le_iff₀ (by positivity)]
            calc (n.choose (M + 1) : ℝ) ≤ (n : ℝ) ^ (M + 1) / (((M + 1) ! : ℕ) : ℝ) := hchoose_le
              _ = 1 / (((M + 1) ! : ℕ) : ℝ) * (n : ℝ) ^ (M + 1) := by ring
          have hstep1 : ((n + 1 : ℕ) : ℝ) * ((n.choose (M + 1) : ℝ) / (n : ℝ) ^ (M + 1)) ≤
              ((n + 1 : ℕ) : ℝ) * (1 / (((M + 1) ! : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hc1 (by positivity)
          exact mul_le_mul hstep1 hpow_exp (by positivity) (by positivity)
    _ = (((n + 1 : ℕ) : ℝ) / (((M + 1) ! : ℕ) : ℝ)) * Real.exp 1 := by ring
    _ ≤ (1 / ((M + 1 : ℕ) : ℝ)) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right hratio_le (le_of_lt (Real.exp_pos 1))
    _ = Real.exp 1 / ((M + 1 : ℕ) : ℝ) := by ring

private lemma sum_NC_tail_le {n : ℕ} (hn : 0 < n) (R : ℕ) :
    (∑ h ∈ (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
        (fun h => minH hn h < maxH hn h ∧ R ≤ minH hn h + (n - maxH hn h)),
      (2 : ℝ) ^ (minH hn h + (n - maxH hn h))) / (n : ℝ) ^ n ≤
    ∑ s ∈ Finset.Ico R n, boundSeq s := by
  let Tail := (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
    (fun h => minH hn h < maxH hn h ∧ R ≤ minH hn h + (n - maxH hn h))
  have hmaps : ∀ h ∈ Tail, minH hn h + (n - maxH hn h) ∈ Finset.Ico R n := by
    intro h hh
    have hcond := (Finset.mem_filter.mp hh).2
    have hmax := maxH_le_n hn h
    exact Finset.mem_Ico.mpr ⟨hcond.2, by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_div]
  refine Finset.sum_le_sum fun s hs => ?_
  have hslt : s < n := (Finset.mem_Ico.mp hs).2
  let Fib := Tail.filter (fun h => minH hn h + (n - maxH hn h) = s)
  have hsum_const : ∑ h ∈ Fib, (2 : ℝ) ^ (minH hn h + (n - maxH hn h)) = (Fib.card : ℝ) * (2 : ℝ) ^ s := by
    rw [Finset.sum_congr rfl fun h hh => by rw [(Finset.mem_filter.mp hh).2], Finset.sum_const, nsmul_eq_mul]
  rw [hsum_const]
  have hFib_card : Fib.card ≤ (s + 1) * (n + 1 - s) ^ n := by
    have hsub : Fib ⊆ (Finset.range (s + 1)).biUnion (fun a =>
        Finset.univ.filter (fun h : Fin n → Fin (n + 1) =>
          ∀ c : Fin n, a ≤ (h c).1 ∧ (h c).1 ≤ n - (s - a))) := by
      intro h hh
      rcases Finset.mem_filter.mp hh with ⟨hhT, hsum⟩
      have hmax := maxH_le_n hn h
      refine Finset.mem_biUnion.mpr ⟨minH hn h, Finset.mem_range.mpr (by omega),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c => ?_⟩⟩
      exact ⟨minH_le hn h c, le_trans (le_maxH hn h c) (by omega)⟩
    calc
      Fib.card ≤ ((Finset.range (s + 1)).biUnion (fun a =>
          Finset.univ.filter (fun h : Fin n → Fin (n + 1) =>
            ∀ c : Fin n, a ≤ (h c).1 ∧ (h c).1 ≤ n - (s - a)))).card := Finset.card_le_card hsub
      _ ≤ ∑ a ∈ Finset.range (s + 1),
          (Finset.univ.filter (fun h : Fin n → Fin (n + 1) =>
            ∀ c : Fin n, a ≤ (h c).1 ∧ (h c).1 ≤ n - (s - a))).card := Finset.card_biUnion_le
      _ = ∑ a ∈ Finset.range (s + 1), (n + 1 - s) ^ n := by
          refine Finset.sum_congr rfl fun a ha => ?_
          have halt := Finset.mem_range.mp ha
          rw [card_range_maps n a (n - (s - a)) (by omega), Nat.card_Icc]
          congr 1; omega
      _ = (s + 1) * (n + 1 - s) ^ n := by simp
  have hFib_real : (Fib.card : ℝ) ≤ ((s + 1 : ℕ) : ℝ) * ((n + 1 - s : ℕ) : ℝ) ^ n := by
    exact_mod_cast hFib_card
  have hpow := one_add_div_pow_le_exp hslt
  unfold boundSeq
  calc
    (Fib.card : ℝ) * (2 : ℝ) ^ s / (n : ℝ) ^ n
        ≤ (((s + 1 : ℕ) : ℝ) * ((n + 1 - s : ℕ) : ℝ) ^ n) * (2 : ℝ) ^ s / (n : ℝ) ^ n :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hFib_real (by positivity)) (by positivity)
    _ = ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * (((n + 1 - s : ℕ) : ℝ) / (n : ℝ)) ^ n := by
          rw [div_pow]; ring
    _ ≤ ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * Real.exp (1 - (s : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ 2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * Real.exp (1 - (s : ℝ)) := by
          have : 0 ≤ ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * Real.exp (1 - (s : ℝ)) := by positivity
          linarith

private noncomputable def avgU {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), ((4 ^ (Uset hn (h ∘ σ)).card - 1 : ℕ) : ℝ)) / (n ! : ℝ)

private lemma avgU_nonneg {n : ℕ} (hn : 0 < n) (h : Fin n → Fin (n + 1)) : 0 ≤ avgU hn h := by
  unfold avgU; positivity

private lemma errCount_eq_sum_avgU {n : ℕ} (hn0 : 0 < n) :
    (errCount n hn0 : ℝ) =
      ∑ h ∈ (Finset.univ : Finset (Fin n → Fin (n + 1))).filter (fun h => minH hn0 h < maxH hn0 h),
        (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h := by
  let NC := (Finset.univ : Finset (Fin n → Fin (n + 1))).filter (fun h => minH hn0 h < maxH hn0 h)
  have hper : ∀ σ : Equiv.Perm (Fin n),
      (errCount n hn0 : ℝ) =
        ∑ h ∈ NC, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * ((4 ^ (Uset hn0 (h ∘ σ)).card - 1 : ℕ) : ℝ) := by
    intro σ
    unfold errCount
    push_cast
    refine Finset.sum_bij (fun h _ => h ∘ σ.symm) ?_ ?_ ?_ ?_
    · intro h hh
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [minH_comp_perm, maxH_comp_perm]
      exact (Finset.mem_filter.mp hh).2
    · intro h₁ _ h₂ _ heq
      funext c
      have := congrFun heq (σ c)
      simpa using this
    · intro h hh
      refine ⟨h ∘ σ, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [minH_comp_perm, maxH_comp_perm]
        exact (Finset.mem_filter.mp hh).2
      · funext c; simp
    · intro h _
      rw [minH_comp_perm, maxH_comp_perm]
      have heq : (h ∘ σ.symm) ∘ σ = h := by funext c; simp
      rw [heq]
  have hsum_perm :
      (n ! : ℝ) * (errCount n hn0 : ℝ) =
        ∑ h ∈ NC, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) *
          ∑ σ : Equiv.Perm (Fin n), ((4 ^ (Uset hn0 (h ∘ σ)).card - 1 : ℕ) : ℝ) := by
    calc
      (n ! : ℝ) * (errCount n hn0 : ℝ)
          = ∑ _σ : Equiv.Perm (Fin n), (errCount n hn0 : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ h ∈ NC,
            (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * ((4 ^ (Uset hn0 (h ∘ σ)).card - 1 : ℕ) : ℝ) :=
            Finset.sum_congr rfl fun σ _ => hper σ
      _ = ∑ h ∈ NC, ∑ σ : Equiv.Perm (Fin n),
            (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * ((4 ^ (Uset hn0 (h ∘ σ)).card - 1 : ℕ) : ℝ) :=
            Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun h _ => (Finset.mul_sum _ _ _).symm
  have hnfac_ne : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hdiv := congrArg (fun x => x / (n ! : ℝ)) hsum_perm
  rw [mul_div_cancel_left₀ _ hnfac_ne, Finset.sum_div] at hdiv
  rw [hdiv]
  refine Finset.sum_congr rfl fun h _ => ?_
  unfold avgU; ring

private lemma avgU_comp_perm {n : ℕ} (hn0 : 0 < n) (h : Fin n → Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    avgU hn0 h = avgU hn0 (h ∘ τ) := by
  unfold avgU
  congr 1
  refine Finset.sum_bij (fun σ _ => τ.symm * σ) (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ heq => by simpa using congrArg (fun x => τ * x) heq)
    (fun σ _ => ⟨τ * σ, Finset.mem_univ _, by ext c; simp⟩) (fun σ _ => ?_)
  have hcomp : (h ∘ τ) ∘ ⇑(τ.symm * σ) = h ∘ ⇑σ := by
    funext c; change h (τ (τ.symm (σ c))) = h (σ c); simp
  rw [hcomp]

private lemma avgU_bounds_of_nc {n : ℕ} (hn16 : 16 ≤ n) (h : Fin n → Fin (n + 1))
    (hnc : minH (by omega) h < maxH (by omega) h) :
    let M := Nat.sqrt (Nat.sqrt n)
    avgU (by omega) h ≤ 36864 ∧
    ((∀ u : Fin (n + 1), (Finset.univ.filter (fun c : Fin n => h c = u)).card ≤ M) →
      avgU (by omega) h ≤ 368640 / (M : ℝ)) := by
  intro M
  have hn0 : 0 < n := by omega
  have hn10 : 10 ≤ n := by omega
  let τ := Tuple.sort h
  let v := h ∘ τ
  have hncv : minH hn0 v < maxH hn0 v := by
    rw [minH_comp_perm, maxH_comp_perm]; exact hnc
  have hdp := perm_avg_Uset_dp_bounds hn10 v (Tuple.monotone_sort h) hncv
  rw [avgU_comp_perm hn0 h τ]
  refine ⟨hdp.1, ?_⟩
  intro hM
  have hMv : ∀ u : Fin (n + 1), (Finset.univ.filter (fun c : Fin n => v c = u)).card ≤ M := by
    intro u
    have hcard_eq : (Finset.univ.filter (fun c : Fin n => v c = u)).card =
        (Finset.univ.filter (fun c : Fin n => h c = u)).card := by
      refine Finset.card_bij (fun c _ => τ c)
        (fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩)
        (fun _ _ _ _ heq => τ.injective heq)
        (fun c hc => ⟨τ.symm c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [v] using (Finset.mem_filter.mp hc).2⟩, by simp⟩)
    rw [hcard_eq]
    exact hM u
  have hM_ge2 : 2 ≤ M := by
    have h1 : 4 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
    exact Nat.le_sqrt.mpr (by omega)
  have hbound := hdp.2 M hn16 (by omega) hMv
  let s := Nat.sqrt n
  have hM2_le_s : M * M ≤ s := Nat.sqrt_le s
  have hs2_le_n : s * s ≤ n := Nat.sqrt_le n
  have hs_le_n : s ≤ n := le_trans (Nat.le_mul_self s) hs2_le_n
  have hn_sub : n ≤ 2 * (n - 1) := by omega
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have ht1 : 6 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ 12 / (M : ℝ) := by
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr (by omega)) hM_pos]
    have : 6 * (M * M) ≤ 12 * (n - 1) := by omega
    have hcast : 6 * ((M : ℝ) * (M : ℝ)) ≤ 12 * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have ht2 : 24 * (M : ℝ) ^ 2 / (n : ℝ) ≤ 24 / (M : ℝ) := by
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr (by omega)) hM_pos]
    have hMs : M ≤ s := le_trans (Nat.le_mul_self M) hM2_le_s
    have : M * M * M ≤ n := by nlinarith [hM2_le_s, hs2_le_n, hMs]
    have hcast : (M : ℝ) * (M : ℝ) * (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    nlinarith
  have ht3 : 18 * (M : ℝ) * (s : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ 36 / (M : ℝ) := by
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr (by omega)) hM_pos]
    have hmul : M * M * s ≤ s * s := Nat.mul_le_mul_right s hM2_le_s
    have : 18 * (M * M * s) ≤ 36 * (n - 1) := by omega
    have hcast : 18 * ((M : ℝ) * (M : ℝ) * (s : ℝ)) ≤ 36 * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have ht4 : 18 * (M : ℝ) / ((s + 1 : ℕ) : ℝ) ≤ 18 / (M : ℝ) := by
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr (by omega)) hM_pos]
    have : M * M ≤ s + 1 := by omega
    have hcast : (M : ℝ) * (M : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast this
    nlinarith
  calc
    avgU hn0 v ≤ 4096 * (6 * (M : ℝ) / ((n - 1 : ℕ) : ℝ) + 24 * (M : ℝ) ^ 2 / (n : ℝ) +
        18 * (M : ℝ) * (s : ℝ) / ((n - 1 : ℕ) : ℝ) + 18 * (M : ℝ) / ((s + 1 : ℕ) : ℝ)) := hbound
    _ ≤ 4096 * (12 / (M : ℝ) + 24 / (M : ℝ) + 36 / (M : ℝ) + 18 / (M : ℝ)) := by linarith
    _ = 368640 / (M : ℝ) := by ring

private lemma errCount_div_pow_tendsto_zero :
    Tendsto (fun n : ℕ => if hn : 0 < n then (errCount n hn : ℝ) / (n : ℝ) ^ n else 0)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsum_tend : Tendsto (fun R : ℕ => ∑ s ∈ Finset.range R, boundSeq s) atTop (𝓝 (∑' s, boundSeq s)) :=
    (hasSum_iff_tendsto_nat_of_nonneg boundSeq_nonneg _).mp summable_boundSeq.hasSum
  have htail_ev : ∃ R : ℕ, 36864 * (∑' s, boundSeq s - ∑ s ∈ Finset.range R, boundSeq s) < ε / 3 := by
    have h := (Metric.tendsto_atTop.mp hsum_tend) (ε / (3 * 36864 + 1)) (by positivity)
    rcases h with ⟨R, hR⟩
    refine ⟨R, ?_⟩
    have hdist := hR R le_rfl
    rw [Real.dist_eq, abs_lt] at hdist
    have hle : ∑ s ∈ Finset.range R, boundSeq s ≤ ∑' s, boundSeq s :=
      summable_boundSeq.sum_le_tsum (Finset.range R) (fun s _ => boundSeq_nonneg s)
    nlinarith
  rcases htail_ev with ⟨R, hR_tail⟩
  let C_tot : ℝ := ∑' s, boundSeq s
  have hC_nn : 0 ≤ C_tot := tsum_nonneg boundSeq_nonneg
  obtain ⟨K, hK⟩ := exists_nat_gt (max 11 (max (3 * 36864 * (2 : ℝ) ^ R * Real.exp 1 / ε) (3 * 368640 * C_tot / ε)))
  have hK11 : 11 ≤ K := by
    have : (11 : ℝ) < (K : ℝ) := lt_of_le_of_lt (le_max_left _ _) hK
    exact_mod_cast le_of_lt this
  have hK_heavy : 36864 * (2 : ℝ) ^ R * Real.exp 1 / ((K + 1 : ℕ) : ℝ) < ε / 3 := by
    have h1 : 3 * 36864 * (2 : ℝ) ^ R * Real.exp 1 / ε < (K : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hK
    have h2 : 3 * 36864 * (2 : ℝ) ^ R * Real.exp 1 < (K : ℝ) * ε := (div_lt_iff₀ hε).mp h1
    have hpos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [div_lt_iff₀ hpos]
    have hKlt : (K : ℝ) < ((K + 1 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith
  have hK_light : 368640 * C_tot / (K : ℝ) < ε / 3 := by
    have h1 : 3 * 368640 * C_tot / ε < (K : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hK
    have h2 : 3 * 368640 * C_tot < (K : ℝ) * ε := (div_lt_iff₀ hε).mp h1
    have hpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [div_lt_iff₀ hpos]
    linarith
  refine ⟨max 14641 (K ^ 4), fun n hn => ?_⟩
  have hn14 : 14641 ≤ n := le_trans (le_max_left _ _) hn
  have hnK4 : K ^ 4 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < n := by omega
  have hn16 : 16 ≤ n := by omega
  rw [dif_pos hn0, Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  let NC := (Finset.univ : Finset (Fin n → Fin (n + 1))).filter (fun h => minH hn0 h < maxH hn0 h)
  let M := Nat.sqrt (Nat.sqrt n)
  have hM_ge_K : K ≤ M := by
    have h1 : K ^ 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by nlinarith [hnK4])
    exact Nat.le_sqrt.mpr (by nlinarith [h1])
  let NC_tail := NC.filter (fun h => R ≤ minH hn0 h + (n - maxH hn0 h))
  let NC_rem := NC.filter (fun h => ¬ R ≤ minH hn0 h + (n - maxH hn0 h))
  let NC_heavy := NC_rem.filter (fun h => ∃ u : Fin (n + 1), M < (Finset.univ.filter (fun c => h c = u)).card)
  let NC_light := NC_rem.filter (fun h => ¬ ∃ u : Fin (n + 1), M < (Finset.univ.filter (fun c => h c = u)).card)
  have hsplit1 := (Finset.sum_filter_add_sum_filter_not NC (fun h => R ≤ minH hn0 h + (n - maxH hn0 h))
    (fun h => (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h)).symm
  have hsplit2 := (Finset.sum_filter_add_sum_filter_not NC_rem
    (fun h => ∃ u : Fin (n + 1), M < (Finset.univ.filter (fun c => h c = u)).card)
    (fun h => (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h)).symm
  rw [errCount_eq_sum_avgU hn0]
  change (∑ h ∈ NC, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h) / (n : ℝ) ^ n < ε
  rw [hsplit1, hsplit2, add_div, add_div]
  have hP1 : (∑ h ∈ NC_tail, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h) / (n : ℝ) ^ n < ε / 3 := by
    have h1 : (∑ h ∈ NC_tail, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h) / (n : ℝ) ^ n ≤
        36864 * ((∑ h ∈ NC_tail, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h))) / (n : ℝ) ^ n) := by
      rw [← mul_div_assoc, Finset.mul_sum]
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun h hh => ?_) (by positivity)
      have hu := (avgU_bounds_of_nc hn16 h (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).2).1
      have hpow_nn : 0 ≤ (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) := by positivity
      calc (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h
          ≤ (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * 36864 := mul_le_mul_of_nonneg_left hu hpow_nn
        _ = 36864 * (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) := mul_comm _ _
    have hNC_tail_eq : NC_tail = (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
        (fun h => minH hn0 h < maxH hn0 h ∧ R ≤ minH hn0 h + (n - maxH hn0 h)) := by
      ext h; simp [NC_tail, NC]
    have h2 : (∑ h ∈ NC_tail, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h))) / (n : ℝ) ^ n ≤
        ∑ s ∈ Finset.Ico R n, boundSeq s := by
      rw [hNC_tail_eq]; exact sum_NC_tail_le hn0 R
    have h3 : ∑ s ∈ Finset.Ico R n, boundSeq s ≤ C_tot - ∑ s ∈ Finset.range R, boundSeq s := by
      by_cases hRn : R ≤ n
      · have hsplit : Finset.range n = Finset.range R ∪ Finset.Ico R n := by
          ext s; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
        have hdisj : Disjoint (Finset.range R) (Finset.Ico R n) := by
          rw [Finset.disjoint_left]; intro s h1 h2
          have := Finset.mem_range.mp h1; have := (Finset.mem_Ico.mp h2).1; omega
        have hsum_rn : ∑ s ∈ Finset.range R, boundSeq s + ∑ s ∈ Finset.Ico R n, boundSeq s ≤ C_tot := by
          rw [← Finset.sum_union hdisj, ← hsplit]
          exact summable_boundSeq.sum_le_tsum (Finset.range n) (fun s _ => boundSeq_nonneg s)
        linarith
      · have hemp : Finset.Ico R n = ∅ := Finset.Ico_eq_empty_of_le (by omega)
        rw [hemp, Finset.sum_empty]
        have := summable_boundSeq.sum_le_tsum (Finset.range R) (fun s _ => boundSeq_nonneg s)
        linarith
    linarith [hR_tail]
  have hP2 : (∑ h ∈ NC_heavy, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h) / (n : ℝ) ^ n < ε / 3 := by
    let AllHeavy := Finset.univ.filter (fun h : Fin n → Fin (n + 1) =>
      ∃ u : Fin (n + 1), M < (Finset.univ.filter (fun c : Fin n => h c = u)).card)
    have hsub : NC_heavy ⊆ AllHeavy := fun h hh =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hh).2⟩
    have h1 : (∑ h ∈ NC_heavy, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h) / (n : ℝ) ^ n ≤
        (36864 * (2 : ℝ) ^ R) * ((AllHeavy.card : ℝ) / (n : ℝ) ^ n) := by
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc
        ∑ h ∈ NC_heavy, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h
            ≤ ∑ _h ∈ NC_heavy, (2 : ℝ) ^ R * 36864 := by
              refine Finset.sum_le_sum fun h hh => ?_
              have hrem := (Finset.mem_filter.mp hh).1
              have hltR : minH hn0 h + (n - maxH hn0 h) < R := not_le.mp (Finset.mem_filter.mp hrem).2
              have hpow : (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) ≤ (2 : ℝ) ^ R :=
                pow_le_pow_right₀ (by norm_num) (le_of_lt hltR)
              have hu := (avgU_bounds_of_nc hn16 h (Finset.mem_filter.mp (Finset.mem_filter.mp hrem).1).2).1
              exact mul_le_mul hpow hu (avgU_nonneg hn0 h) (by positivity)
        _ = (NC_heavy.card : ℝ) * ((2 : ℝ) ^ R * 36864) := by simp
        _ ≤ (AllHeavy.card : ℝ) * ((2 : ℝ) ^ R * 36864) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)
        _ = (36864 * (2 : ℝ) ^ R) * (AllHeavy.card : ℝ) := by ring
    have h2 := card_heavy_div_pow_le hn14
    have h3 : Real.exp 1 / ((M + 1 : ℕ) : ℝ) ≤ Real.exp 1 / ((K + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos 1)) (Nat.cast_pos.mpr (by omega))
        (by exact_mod_cast Nat.succ_le_succ hM_ge_K)
    have h4 : (36864 * (2 : ℝ) ^ R) * (Real.exp 1 / ((K + 1 : ℕ) : ℝ)) =
        36864 * (2 : ℝ) ^ R * Real.exp 1 / ((K + 1 : ℕ) : ℝ) := by ring
    calc
      (∑ h ∈ NC_heavy, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h) / (n : ℝ) ^ n
          ≤ (36864 * (2 : ℝ) ^ R) * ((AllHeavy.card : ℝ) / (n : ℝ) ^ n) := h1
      _ ≤ (36864 * (2 : ℝ) ^ R) * (Real.exp 1 / ((M + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (36864 * (2 : ℝ) ^ R) * (Real.exp 1 / ((K + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
      _ < ε / 3 := by rw [h4]; exact hK_heavy
  have hP3 : (∑ h ∈ NC_light, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h) / (n : ℝ) ^ n < ε / 3 := by
    have hsub : NC_light ⊆ NC := fun h hh => (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
    have h1 : (∑ h ∈ NC_light, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h) / (n : ℝ) ^ n ≤
        (368640 / (M : ℝ)) * ((∑ h ∈ NC, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h))) / (n : ℝ) ^ n) := by
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc
        ∑ h ∈ NC_light, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h
            ≤ ∑ h ∈ NC_light, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * (368640 / (M : ℝ)) := by
              refine Finset.sum_le_sum fun h hh => ?_
              have hnot := (Finset.mem_filter.mp hh).2
              have hM_le : ∀ u : Fin (n + 1), (Finset.univ.filter (fun c : Fin n => h c = u)).card ≤ M := by
                intro u; by_contra hgt; exact hnot ⟨u, not_le.mp hgt⟩
              have hl := (avgU_bounds_of_nc hn16 h (Finset.mem_filter.mp (hsub hh)).2).2 hM_le
              exact mul_le_mul_of_nonneg_left hl (by positivity)
        _ ≤ ∑ h ∈ NC, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * (368640 / (M : ℝ)) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = (368640 / (M : ℝ)) * ∑ h ∈ NC, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hNC_all : (∑ h ∈ NC, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h))) / (n : ℝ) ^ n ≤ C_tot := by
      have h0 := sum_NC_tail_le hn0 0
      have hfeq : (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
          (fun h => minH hn0 h < maxH hn0 h ∧ 0 ≤ minH hn0 h + (n - maxH hn0 h)) = NC := by
        ext h; simp [NC]
      rw [hfeq, Nat.Ico_zero_eq_range] at h0
      exact le_trans h0 (summable_boundSeq.sum_le_tsum (Finset.range n) (fun s _ => boundSeq_nonneg s))
    have hM_inv : 368640 / (M : ℝ) ≤ 368640 / (K : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hM_ge_K)
    calc
      (∑ h ∈ NC_light, (2 : ℝ) ^ (minH hn0 h + (n - maxH hn0 h)) * avgU hn0 h) / (n : ℝ) ^ n
          ≤ (368640 / (M : ℝ)) * C_tot := le_trans h1 (mul_le_mul_of_nonneg_left hNC_all (by positivity))
      _ ≤ (368640 / (K : ℝ)) * C_tot := mul_le_mul_of_nonneg_right hM_inv hC_nn
      _ = 368640 * C_tot / (K : ℝ) := by ring
      _ < ε / 3 := hK_light
  linarith

/-! ### Section 6: Exact asymptotics of `mainCount n / n^n` and final limit -/

private noncomputable def countAB (n a b : ℕ) (hn : 0 < n) : ℕ :=
  (Finset.univ.filter (fun h : Fin n → Fin (n + 1) => minH hn h = a ∧ maxH hn h = n - b)).card

private lemma countAB_ie {n a b : ℕ} (hn : 0 < n) (hab : a + b < n) :
    countAB n a b hn + 2 * (n - (a + b)) ^ n =
      (n + 1 - (a + b)) ^ n + (n - 1 - (a + b)) ^ n := by
  let All := (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
    (fun h => ∀ c : Fin n, a ≤ (h c).1 ∧ (h c).1 ≤ n - b)
  let A_hi := (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
    (fun h => ∀ c : Fin n, a + 1 ≤ (h c).1 ∧ (h c).1 ≤ n - b)
  let B_lo := (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
    (fun h => ∀ c : Fin n, a ≤ (h c).1 ∧ (h c).1 ≤ n - b - 1)
  let AB := (Finset.univ : Finset (Fin n → Fin (n + 1))).filter
    (fun h => ∀ c : Fin n, a + 1 ≤ (h c).1 ∧ (h c).1 ≤ n - b - 1)
  have hAll_card : All.card = (n + 1 - (a + b)) ^ n := by
    rw [card_range_maps n a (n - b) (by omega), Nat.card_Icc]; congr 1; omega
  have hA_card : A_hi.card = (n - (a + b)) ^ n := by
    rw [card_range_maps n (a + 1) (n - b) (by omega), Nat.card_Icc]; congr 1; omega
  have hB_card : B_lo.card = (n - (a + b)) ^ n := by
    rw [card_range_maps n a (n - b - 1) (by omega), Nat.card_Icc]; congr 1; omega
  have hAB_card : AB.card = (n - 1 - (a + b)) ^ n := by
    rw [card_range_maps n (a + 1) (n - b - 1) (by omega), Nat.card_Icc]
    congr 1; omega
  have hinter : A_hi ∩ B_lo = AB := by
    ext h; simp only [A_hi, B_lo, AB, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩ c; exact ⟨(h1 c).1, (h2 c).2⟩
    · intro h1; exact ⟨fun c => ⟨(h1 c).1, by have := (h1 c).2; omega⟩,
        fun c => ⟨by have := (h1 c).1; omega, (h1 c).2⟩⟩
  have hsub : A_hi ∪ B_lo ⊆ All := by
    intro h hh
    simp only [A_hi, B_lo, All, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    rcases hh with h1 | h2
    · intro c; exact ⟨by have := (h1 c).1; omega, (h1 c).2⟩
    · intro c; exact ⟨(h2 c).1, by have := (h2 c).2; omega⟩
  have hsdiff : All \ (A_hi ∪ B_lo) =
      Finset.univ.filter (fun h : Fin n → Fin (n + 1) => minH hn h = a ∧ maxH hn h = n - b) := by
    ext h
    simp only [All, A_hi, B_lo, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, not_or]
    constructor
    · rintro ⟨hAll, hnotA, hnotB⟩
      have hmin_ge : a ≤ minH hn h := by
        rcases exists_eq_minH hn h with ⟨c, hc⟩; rw [← hc]; exact (hAll c).1
      have hmax_le : maxH hn h ≤ n - b := by
        rcases exists_eq_maxH hn h with ⟨c, hc⟩; rw [← hc]; exact (hAll c).2
      have hmin_le : minH hn h ≤ a := by
        by_contra hgt
        apply hnotA; intro c
        exact ⟨by have := minH_le hn h c; omega, (hAll c).2⟩
      have hmax_ge : n - b ≤ maxH hn h := by
        by_contra hlt
        apply hnotB; intro c
        exact ⟨(hAll c).1, by have := le_maxH hn h c; omega⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨hmin, hmax⟩
      refine ⟨fun c => ⟨hmin ▸ minH_le hn h c, hmax ▸ le_maxH hn h c⟩, ?_, ?_⟩
      · intro hA
        rcases exists_eq_minH hn h with ⟨c, hc⟩
        have := (hA c).1; omega
      · intro hB
        rcases exists_eq_maxH hn h with ⟨c, hc⟩
        have := (hB c).2; omega
  have h1 : countAB n a b hn = (All \ (A_hi ∪ B_lo)).card := by unfold countAB; rw [hsdiff]
  have h2 := Finset.card_sdiff_add_card_eq_card hsub
  have h3 := Finset.card_union_add_card_inter A_hi B_lo
  rw [hAll_card] at h2
  rw [hinter, hA_card, hB_card, hAB_card] at h3
  omega

private lemma mainCount_div_pow_eq_tsum {n : ℕ} (hn : 0 < n) :
    (mainCount n hn : ℝ) / (n : ℝ) ^ n =
      ∑' s : ℕ, if _hs : s < n then
        2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * (countAB n 0 s hn : ℝ) / (n : ℝ) ^ n else 0 := by
  rw [tsum_eq_sum (s := Finset.range n) (fun s hs => by
    simp only [Finset.mem_range, not_lt] at hs; exact dif_neg (not_lt.mpr hs))]
  let NC := (Finset.univ : Finset (Fin n → Fin (n + 1))).filter (fun h => minH hn h < maxH hn h)
  have hmaps : ∀ h ∈ NC, minH hn h + (n - maxH hn h) ∈ Finset.range n := by
    intro h hh
    have hlt := (Finset.mem_filter.mp hh).2
    have hmax := maxH_le_n hn h
    exact Finset.mem_range.mpr (by omega)
  unfold mainCount
  push_cast
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_div]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hslt : s < n := Finset.mem_range.mp hs
  simp only [dif_pos hslt]
  let Fib := NC.filter (fun h => minH hn h + (n - maxH hn h) = s)
  have hconst : ∑ h ∈ Fib, (2 : ℝ) * (2 : ℝ) ^ (minH hn h + (n - maxH hn h)) =
      (Fib.card : ℝ) * (2 * (2 : ℝ) ^ s) := by
    rw [Finset.sum_congr rfl fun h hh => by rw [(Finset.mem_filter.mp hh).2], Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  have hFib_card : Fib.card = (s + 1) * countAB n 0 s hn := by
    have hpart : Fib = (Finset.range (s + 1)).biUnion (fun a =>
        Finset.univ.filter (fun h : Fin n → Fin (n + 1) => minH hn h = a ∧ maxH hn h = n - (s - a))) := by
      ext h
      simp only [Fib, NC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range]
      constructor
      · rintro ⟨hlt, hsum⟩
        have hmax := maxH_le_n hn h
        exact ⟨minH hn h, by omega, rfl, by omega⟩
      · rintro ⟨a, halt, hmin, hmax⟩
        exact ⟨by omega, by omega⟩
    have hdisj : Set.PairwiseDisjoint (Finset.range (s + 1) : Set ℕ)
        (fun a => Finset.univ.filter (fun h : Fin n → Fin (n + 1) => minH hn h = a ∧ maxH hn h = n - (s - a))) := by
      intro a₁ _ a₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro h h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)
    rw [hpart, Finset.card_biUnion hdisj]
    have hterm : ∀ a ∈ Finset.range (s + 1),
        (Finset.univ.filter (fun h : Fin n → Fin (n + 1) => minH hn h = a ∧ maxH hn h = n - (s - a))).card =
        countAB n 0 s hn := by
      intro a ha
      have halt : a ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have h1 := countAB_ie (a := a) (b := s - a) hn (by omega)
      have h2 := countAB_ie (a := 0) (b := s) hn (by omega)
      have hab : a + (s - a) = s := by omega
      rw [hab] at h1
      simp only [zero_add] at h2
      change countAB n a (s - a) hn = countAB n 0 s hn
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [hFib_card]
  push_cast
  ring

private lemma mainCount_div_pow_tendsto_pos :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => if hn : 0 < n then (mainCount n hn : ℝ) / (n : ℝ) ^ n else 0)
        atTop (𝓝 c) := by
  let f : ℕ → ℕ → ℝ := fun n s =>
    if hs : s < n then
      2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * (countAB n 0 s (by omega) : ℝ) / (n : ℝ) ^ n
    else 0
  let g : ℕ → ℝ := fun s =>
    2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s *
      (Real.exp (1 - (s : ℝ)) - 2 * Real.exp (-(s : ℝ)) + Real.exp (-(1 : ℝ) - (s : ℝ)))
  have hf_bound : ∀ n s : ℕ, ‖f n s‖ ≤ boundSeq s := by
    intro n s
    dsimp only [f]
    split_ifs with hs
    · have hnn : 0 ≤ 2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * (countAB n 0 s (by omega) : ℝ) / (n : ℝ) ^ n := by
        positivity
      rw [Real.norm_of_nonneg hnn]
      have hcount_le : countAB n 0 s (by omega) ≤ (n + 1 - s) ^ n := by
        have hsub : Finset.univ.filter (fun h : Fin n → Fin (n + 1) =>
            minH (by omega) h = 0 ∧ maxH (by omega) h = n - s) ⊆
            Finset.univ.filter (fun h : Fin n → Fin (n + 1) => ∀ c : Fin n, 0 ≤ (h c).1 ∧ (h c).1 ≤ n - s) := by
          intro h hh
          have hmax := (Finset.mem_filter.mp hh).2.2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c => ⟨Nat.zero_le _, hmax ▸ le_maxH _ h c⟩⟩
        have h1 := Finset.card_le_card hsub
        rw [card_range_maps n 0 (n - s) (by omega), Nat.card_Icc] at h1
        simpa [countAB, show n - s + 1 - 0 = n + 1 - s by omega] using h1
      have hcount_real : (countAB n 0 s (by omega) : ℝ) / (n : ℝ) ^ n ≤ Real.exp (1 - (s : ℝ)) := by
        calc
          (countAB n 0 s (by omega) : ℝ) / (n : ℝ) ^ n
              ≤ (((n + 1 - s : ℕ) : ℝ) ^ n) / (n : ℝ) ^ n :=
                div_le_div_of_nonneg_right (by exact_mod_cast hcount_le) (by positivity)
          _ = (((n + 1 - s : ℕ) : ℝ) / (n : ℝ)) ^ n := (div_pow _ _ _).symm
          _ ≤ Real.exp (1 - (s : ℝ)) := one_add_div_pow_le_exp hs
      unfold boundSeq
      calc
        2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * (countAB n 0 s (by omega) : ℝ) / (n : ℝ) ^ n
            = 2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * ((countAB n 0 s (by omega) : ℝ) / (n : ℝ) ^ n) := by ring
        _ ≤ 2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s * Real.exp (1 - (s : ℝ)) :=
              mul_le_mul_of_nonneg_left hcount_real (by positivity)
    · rw [norm_zero]; exact boundSeq_nonneg s
  have hf_lim : ∀ s : ℕ, Tendsto (fun n => f n s) atTop (𝓝 (g s)) := by
    intro s
    have h1 : Tendsto (fun n : ℕ => (1 + (1 - (s : ℝ)) / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp (1 - (s : ℝ)))) :=
      Real.tendsto_one_add_div_pow_exp (1 - (s : ℝ))
    have h2 : Tendsto (fun n : ℕ => (1 + (-(s : ℝ)) / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp (-(s : ℝ)))) :=
      Real.tendsto_one_add_div_pow_exp (-(s : ℝ))
    have h3 : Tendsto (fun n : ℕ => (1 + (-(1 : ℝ) - (s : ℝ)) / (n : ℝ)) ^ n) atTop
        (𝓝 (Real.exp (-(1 : ℝ) - (s : ℝ)))) :=
      Real.tendsto_one_add_div_pow_exp (-(1 : ℝ) - (s : ℝ))
    have hcomb : Tendsto (fun n : ℕ => 2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s *
        ((1 + (1 - (s : ℝ)) / (n : ℝ)) ^ n - 2 * (1 + (-(s : ℝ)) / (n : ℝ)) ^ n +
         (1 + (-(1 : ℝ) - (s : ℝ)) / (n : ℝ)) ^ n)) atTop (𝓝 (g s)) := by
      exact ((h1.sub (h2.const_mul 2)).add h3).const_mul (2 * ((s + 1 : ℕ) : ℝ) * (2 : ℝ) ^ s)
    refine hcomb.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (s + 2)] with n hn
    have hslt : s < n := by omega
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp only [f]
    rw [dif_pos hslt]
    have hie := countAB_ie (a := 0) (b := s) (by omega : 0 < n) (by omega)
    simp only [zero_add] at hie
    have hie_r : (countAB n 0 s (by omega) : ℝ) + 2 * ((n - s : ℕ) : ℝ) ^ n =
        ((n + 1 - s : ℕ) : ℝ) ^ n + ((n - 1 - s : ℕ) : ℝ) ^ n := by exact_mod_cast hie
    have hc_eq : (countAB n 0 s (by omega) : ℝ) / (n : ℝ) ^ n =
        (((n + 1 - s : ℕ) : ℝ) / (n : ℝ)) ^ n - 2 * (((n - s : ℕ) : ℝ) / (n : ℝ)) ^ n +
        (((n - 1 - s : ℕ) : ℝ) / (n : ℝ)) ^ n := by
      have hsub : (countAB n 0 s (by omega) : ℝ) =
          ((n + 1 - s : ℕ) : ℝ) ^ n - 2 * ((n - s : ℕ) : ℝ) ^ n + ((n - 1 - s : ℕ) : ℝ) ^ n := by linarith
      rw [hsub, add_div, sub_div, mul_div_assoc, div_pow, div_pow, div_pow]
    have ha1 : ((n + 1 - s : ℕ) : ℝ) / (n : ℝ) = 1 + (1 - (s : ℝ)) / (n : ℝ) := by
      have : ((n + 1 - s : ℕ) : ℝ) + (s : ℝ) = (n : ℝ) + 1 := by exact_mod_cast (by omega : n + 1 - s + s = n + 1)
      field_simp [hn_ne]; linarith
    have ha2 : ((n - s : ℕ) : ℝ) / (n : ℝ) = 1 + (-(s : ℝ)) / (n : ℝ) := by
      have : ((n - s : ℕ) : ℝ) + (s : ℝ) = (n : ℝ) := by exact_mod_cast (by omega : n - s + s = n)
      field_simp [hn_ne]; linarith
    have ha3 : ((n - 1 - s : ℕ) : ℝ) / (n : ℝ) = 1 + (-(1 : ℝ) - (s : ℝ)) / (n : ℝ) := by
      have : ((n - 1 - s : ℕ) : ℝ) + (s : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast (by omega : n - 1 - s + s + 1 = n)
      field_simp [hn_ne]; linarith
    rw [mul_div_assoc, hc_eq, ha1, ha2, ha3]
  have htsum_tend : Tendsto (fun n => ∑' s, f n s) atTop (𝓝 (∑' s, g s)) :=
    tendsto_tsum_of_dominated_convergence summable_boundSeq hf_lim (Filter.Eventually.of_forall hf_bound)
  have hg_nonneg : ∀ s : ℕ, 0 ≤ g s := fun s =>
    ge_of_tendsto (hf_lim s) (Filter.Eventually.of_forall fun n => by
      dsimp only [f]; split_ifs <;> positivity)
  have hg_le : ∀ s : ℕ, g s ≤ boundSeq s := fun s =>
    le_of_tendsto (hf_lim s) (Filter.Eventually.of_forall fun n =>
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hf_bound n s))
  have hg_sum : Summable g := Summable.of_nonneg_of_le hg_nonneg hg_le summable_boundSeq
  have hg0_pos : 0 < g 0 := by
    dsimp only [g]
    simp only [Nat.cast_zero, zero_add, Nat.cast_one, pow_zero, mul_one, sub_zero, neg_zero, Real.exp_zero]
    have hmul : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    have hgt : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hsq : 0 < (Real.exp 1 - 1) ^ 2 := sq_pos_of_pos (by linarith)
    have hid : Real.exp 1 * (Real.exp 1 - 2 + Real.exp (-1)) = (Real.exp 1 - 1) ^ 2 := by
      nlinarith [hmul]
    nlinarith
  have hc_pos : 0 < ∑' s, g s := by
    have hle : g 0 ≤ ∑' s, g s := by
      simpa using hg_sum.sum_le_tsum ({0} : Finset ℕ) (fun s _ => hg_nonneg s)
    linarith
  refine ⟨∑' s, g s, hc_pos, ?_⟩
  refine htsum_tend.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : 0 < n := by omega
  rw [dif_pos hn0, mainCount_div_pow_eq_tsum hn0]

private lemma const_term_tendsto_zero :
    Tendsto (fun n : ℕ => (((n + 1) * 2 ^ n : ℕ) : ℝ) / (n : ℝ) ^ n) atTop (𝓝 0) := by
  have hgeo : Tendsto (fun n : ℕ => ((2 : ℝ) / 3) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero_norm' ?_ hgeo
  filter_upwards [Filter.eventually_ge_atTop 6] with n hn
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 0
      · subst hm; norm_num
      · have h2m : m + 1 ≤ 2 ^ m := by
          clear ih hn
          induction m with
          | zero => norm_num
          | succ k ihk =>
            have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
            rw [pow_succ]; omega
        rw [pow_succ]; omega
  have h1r : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast h1
  have h6 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : ((2 : ℝ) / (n : ℝ)) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h3 : ((2 : ℝ) / (n : ℝ)) ^ n ≤ (1 / 3 : ℝ) ^ n :=
    pow_le_pow_left₀ (by positivity) h2 n
  push_cast
  calc
    ((n : ℝ) + 1) * (2 : ℝ) ^ n / (n : ℝ) ^ n
        = ((n : ℝ) + 1) * ((2 : ℝ) / (n : ℝ)) ^ n := by rw [div_pow]; ring
    _ ≤ (2 : ℝ) ^ n * (1 / 3 : ℝ) ^ n :=
          mul_le_mul (by exact_mod_cast h1) h3 (by positivity) (by positivity)
    _ = ((2 : ℝ) / 3) ^ n := by rw [← mul_pow]; norm_num

private lemma a_div_pow_tendsto_pos :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (OMA.S_oeis_a137432.a n : ℝ) / (n : ℝ) ^ n) atTop (𝓝 c) := by
  rcases mainCount_div_pow_tendsto_pos with ⟨c, hc_pos, hmain⟩
  refine ⟨c, hc_pos, ?_⟩
  let lo : ℕ → ℝ := fun n => if hn : 0 < n then (mainCount n hn : ℝ) / (n : ℝ) ^ n else 0
  let hi : ℕ → ℝ := fun n =>
    (if hn : 0 < n then (mainCount n hn : ℝ) / (n : ℝ) ^ n else 0) +
    (((n + 1) * 2 ^ n : ℕ) : ℝ) / (n : ℝ) ^ n +
    2 * (if hn : 0 < n then (errCount n hn : ℝ) / (n : ℝ) ^ n else 0)
  have hhi : Tendsto hi atTop (𝓝 c) := by
    have h := (hmain.add const_term_tendsto_zero).add (errCount_div_pow_tendsto_zero.const_mul 2)
    simpa [hi] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain hhi ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    have hn0 : 0 < n := by omega
    rw [dif_pos hn0]
    exact div_le_div_of_nonneg_right (by exact_mod_cast (a_bounds hn).1) (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    have hn0 : 0 < n := by omega
    dsimp only [hi]
    simp only [dif_pos hn0]
    have hub : (OMA.S_oeis_a137432.a n : ℝ) ≤
        (mainCount n hn0 : ℝ) + (((n + 1) * 2 ^ n : ℕ) : ℝ) + 2 * (errCount n hn0 : ℝ) := by
      exact_mod_cast (a_bounds hn).2
    calc
      (OMA.S_oeis_a137432.a n : ℝ) / (n : ℝ) ^ n
          ≤ ((mainCount n hn0 : ℝ) + (((n + 1) * 2 ^ n : ℕ) : ℝ) + 2 * (errCount n hn0 : ℝ)) / (n : ℝ) ^ n :=
            div_le_div_of_nonneg_right hub (by positivity)
      _ = (mainCount n hn0 : ℝ) / (n : ℝ) ^ n + (((n + 1) * 2 ^ n : ℕ) : ℝ) / (n : ℝ) ^ n +
            2 * ((errCount n hn0 : ℝ) / (n : ℝ) ^ n) := by ring

end A137432Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a137432.main := by
  rcases A137432Proof.a_div_pow_tendsto_pos with ⟨c, hc_pos, hlim⟩
  have hlim1 : Filter.Tendsto (fun n : ℕ =>
      (OMA.S_oeis_a137432.a (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (n + 1))
      Filter.atTop (nhds c) :=
    hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have hratio : Filter.Tendsto (fun n : ℕ =>
      ((OMA.S_oeis_a137432.a (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (n + 1)) /
      ((OMA.S_oeis_a137432.a n : ℝ) / (n : ℝ) ^ n))
      Filter.atTop (nhds 1) := by
    have h := hlim1.div hlim (ne_of_gt hc_pos)
    rw [div_self (ne_of_gt hc_pos)] at h
    exact h
  have hexp : Filter.Tendsto (fun n : ℕ => (1 + (1 : ℝ) / (n : ℝ)) ^ n)
      Filter.atTop (nhds (Real.exp 1)) :=
    Real.tendsto_one_add_div_pow_exp 1
  have hone : Filter.Tendsto (fun n : ℕ => 1 + (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hprod : Filter.Tendsto (fun n : ℕ =>
      (((OMA.S_oeis_a137432.a (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (n + 1)) /
       ((OMA.S_oeis_a137432.a n : ℝ) / (n : ℝ) ^ n)) *
      ((1 + (1 : ℝ) / (n : ℝ)) ^ n * (1 + (1 : ℝ) / (n : ℝ))))
      Filter.atTop (nhds (Real.exp 1)) := by
    simpa using hratio.mul (hexp.mul hone)
  refine hprod.congr' ?_
  have hev_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < (OMA.S_oeis_a137432.a n : ℝ) / (n : ℝ) ^ n :=
    hlim.eventually (Ioi_mem_nhds hc_pos)
  filter_upwards [hev_pos, Filter.eventually_ge_atTop 1] with n hpos hn1
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnp1_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ha_ne : (OMA.S_oeis_a137432.a n : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hpos; exact lt_irrefl 0 hpos
  have h1 : 1 + (1 : ℝ) / (n : ℝ) = ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    push_cast; field_simp [hn_ne]
  rw [h1, ← pow_succ, div_pow]
  field_simp [hn_ne, hnp1_ne, ha_ne]
  rw [pow_succ]
  ring
