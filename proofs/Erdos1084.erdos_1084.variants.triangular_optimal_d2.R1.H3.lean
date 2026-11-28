import OMAReductions.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1

open Finset Metric
open scoped EuclideanGeometry Classical

namespace Erdos1084H3

/-! ### Part 1: Box-peeling antichain inequality -/

private def IsAntichain3 (A : Finset (ℕ × ℕ × ℕ)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p.1 ≤ q.1 → p.2.1 ≤ q.2.1 → p.2.2 ≤ q.2.2 → p = q

private lemma peel_step (a b c m : ℤ) (ha : c ≤ a) (hb : c ≤ b)
    (h : 12 * m ≤ (a + b + c - 2) ^ 2 + 3) :
    12 * (m + c) ≤ (a + b + c) ^ 2 + 3 := by
  by_cases he : a + b = 2 * c
  · have h₁ : a = c := by omega
    have h₂ : b = c := by omega
    subst a
    subst b
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' c <;>
      ring_nf at h ⊢ <;> omega
  · have h' : 2 * c + 1 ≤ a + b := by omega
    linarith [show (a + b + c) ^ 2 - (a + b + c - 2) ^ 2 = 4 * (a + b + c) - 4 by ring]

private lemma antichain_box_bound :
    ∀ d a b c : ℕ, a + b + c = d →
    ∀ A : Finset (ℕ × ℕ × ℕ),
      (∀ p ∈ A, p.1 < a ∧ p.2.1 < b ∧ p.2.2 < c) →
      IsAntichain3 A →
      12 * A.card ≤ d ^ 2 + 3 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a b c habc A hbox hanti
    -- Reduce to the case `c ≤ a` and `c ≤ b` by permuting coordinates.
    suffices hmin : ∀ (a' b' c' : ℕ), a' + b' + c' = d → c' ≤ a' → c' ≤ b' →
        ∀ B : Finset (ℕ × ℕ × ℕ),
          (∀ p ∈ B, p.1 < a' ∧ p.2.1 < b' ∧ p.2.2 < c') →
          IsAntichain3 B → 12 * B.card ≤ d ^ 2 + 3 by
      by_cases hca : c ≤ a
      · by_cases hcb : c ≤ b
        · exact hmin a b c habc hca hcb A hbox hanti
        · -- `b < c ≤ a`: swap `b` and `c`
          let B := A.image (fun p => (p.1, p.2.2, p.2.1))
          have hcard : B.card = A.card := by
            apply Finset.card_image_of_injective
            intro p q h
            rcases p with ⟨p1, p2, p3⟩; rcases q with ⟨q1, q2, q3⟩
            simp only [Prod.mk.injEq] at h ⊢
            exact ⟨h.1, h.2.2, h.2.1⟩
          rw [← hcard]
          refine hmin a c b (by omega) (by omega) (by omega) B ?_ ?_
          · intro p hp
            rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
            have hq' := hbox q hq
            exact ⟨hq'.1, hq'.2.2, hq'.2.1⟩
          · intro p hp q hq h1 h2 h3
            rcases Finset.mem_image.mp hp with ⟨p', hp', rfl⟩
            rcases Finset.mem_image.mp hq with ⟨q', hq', rfl⟩
            have := hanti p' hp' q' hq' h1 h3 h2
            subst this; rfl
      · by_cases hab : a ≤ b
        · -- `a < c` and `a ≤ b`: swap `a` and `c`
          let B := A.image (fun p => (p.2.2, p.2.1, p.1))
          have hcard : B.card = A.card := by
            apply Finset.card_image_of_injective
            intro p q h
            rcases p with ⟨p1, p2, p3⟩; rcases q with ⟨q1, q2, q3⟩
            simp only [Prod.mk.injEq] at h ⊢
            exact ⟨h.2.2, h.2.1, h.1⟩
          rw [← hcard]
          refine hmin c b a (by omega) (by omega) (by omega) B ?_ ?_
          · intro p hp
            rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
            have hq' := hbox q hq
            exact ⟨hq'.2.2, hq'.2.1, hq'.1⟩
          · intro p hp q hq h1 h2 h3
            rcases Finset.mem_image.mp hp with ⟨p', hp', rfl⟩
            rcases Finset.mem_image.mp hq with ⟨q', hq', rfl⟩
            have := hanti p' hp' q' hq' h3 h2 h1
            subst this; rfl
        · -- `b < a < c`: swap `b` and `c`
          let B := A.image (fun p => (p.1, p.2.2, p.2.1))
          have hcard : B.card = A.card := by
            apply Finset.card_image_of_injective
            intro p q h
            rcases p with ⟨p1, p2, p3⟩; rcases q with ⟨q1, q2, q3⟩
            simp only [Prod.mk.injEq] at h ⊢
            exact ⟨h.1, h.2.2, h.2.1⟩
          rw [← hcard]
          refine hmin a c b (by omega) (by omega) (by omega) B ?_ ?_
          · intro p hp
            rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
            have hq' := hbox q hq
            exact ⟨hq'.1, hq'.2.2, hq'.2.1⟩
          · intro p hp q hq h1 h2 h3
            rcases Finset.mem_image.mp hp with ⟨p', hp', rfl⟩
            rcases Finset.mem_image.mp hq with ⟨q', hq', rfl⟩
            have := hanti p' hp' q' hq' h1 h3 h2
            subst this; rfl
    intro a' b' c' habc' hca hcb B hB hBanti
    by_cases hc0 : c' = 0
    · have hBe : B = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        have := (hB p hp).2.2
        omega
      simp [hBe]
    · have hc_pos : 1 ≤ c' := Nat.pos_of_ne_zero hc0
      have ha_pos : 1 ≤ a' := by omega
      have hb_pos : 1 ≤ b' := by omega
      let L := B.filter (fun p => p.2.1 = 0 ∨ p.1 = a' - 1)
      let R := B.filter (fun p => ¬ (p.2.1 = 0 ∨ p.1 = a' - 1))
      have hcard_split : L.card + R.card = B.card :=
        Finset.card_filter_add_card_filter_not _
      have hL_le : L.card ≤ c' := by
        have hsub : L.image (fun p => p.2.2) ⊆ Finset.range c' := by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
          exact Finset.mem_range.mpr (hB p (Finset.mem_filter.mp hp).1).2.2
        have hinj : Set.InjOn (fun p : ℕ × ℕ × ℕ => p.2.2) (L : Set (ℕ × ℕ × ℕ)) := by
          intro p hp q hq heq
          have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
          have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          have hpb := hB p hp'.1
          have hqb := hB q hq'.1
          -- On the L-shape `y = 0 ∨ x = a' - 1`, any two `(x, y)` are comparable!
          have hcomp : (p.1 ≤ q.1 ∧ p.2.1 ≤ q.2.1) ∨ (q.1 ≤ p.1 ∧ q.2.1 ≤ p.2.1) := by
            rcases hp'.2 with hpy | hpx <;> rcases hq'.2 with hqy | hqx
            · rcases le_total p.1 q.1 with h | h
              · exact Or.inl ⟨h, by omega⟩
              · exact Or.inr ⟨h, by omega⟩
            · exact Or.inl ⟨by omega, by omega⟩
            · exact Or.inr ⟨by omega, by omega⟩
            · rcases le_total p.2.1 q.2.1 with h | h
              · exact Or.inl ⟨by omega, h⟩
              · exact Or.inr ⟨by omega, h⟩
          rcases hcomp with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hBanti p hp'.1 q hq'.1 h1 h2 heq.le
          · exact (hBanti q hq'.1 p hp'.1 h1 h2 heq.ge).symm
        calc L.card = (L.image (fun p => p.2.2)).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.range c').card := Finset.card_le_card hsub
          _ = c' := Finset.card_range c'
      let R' := R.image (fun p => (p.1, p.2.1 - 1, p.2.2))
      have hR_card : R'.card = R.card := by
        apply Finset.card_image_of_injOn
        intro p hp q hq heq
        have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
        have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
        rcases p with ⟨p1, p2, p3⟩; rcases q with ⟨q1, q2, q3⟩
        simp only [Prod.mk.injEq] at heq ⊢
        refine ⟨heq.1, ?_, heq.2.2⟩
        have hp2 : p2 ≠ 0 := fun h => hp'.2 (Or.inl h)
        have hq2 : q2 ≠ 0 := fun h => hq'.2 (Or.inl h)
        omega
      have hR'_box : ∀ p ∈ R', p.1 < a' - 1 ∧ p.2.1 < b' - 1 ∧ p.2.2 < c' := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        have hq' := Finset.mem_filter.mp hq
        have hqb := hB q hq'.1
        have hq1 : q.1 ≠ a' - 1 := fun h => hq'.2 (Or.inr h)
        have hq2 : q.2.1 ≠ 0 := fun h => hq'.2 (Or.inl h)
        dsimp only
        exact ⟨by have := hqb.1; omega, by have := hqb.2.1; omega, hqb.2.2⟩
      have hR'_anti : IsAntichain3 R' := by
        intro p hp q hq h1 h2 h3
        rcases Finset.mem_image.mp hp with ⟨p', hp', rfl⟩
        rcases Finset.mem_image.mp hq with ⟨q', hq', rfl⟩
        have hp'' := Finset.mem_filter.mp hp'
        have hq'' := Finset.mem_filter.mp hq'
        have hp2 : p'.2.1 ≠ 0 := fun h => hp''.2 (Or.inl h)
        have hq2 : q'.2.1 ≠ 0 := fun h => hq''.2 (Or.inl h)
        dsimp only at h1 h2 h3
        have heq := hBanti p' hp''.1 q' hq''.1 h1 (by omega) h3
        subst heq; rfl
      have hih := ih (d - 2) (by omega) (a' - 1) (b' - 1) c' (by omega) R' hR'_box hR'_anti
      rw [hR_card] at hih
      have hpeel := peel_step (a' : ℤ) (b' : ℤ) (c' : ℤ) (R.card : ℤ)
        (by exact_mod_cast hca) (by exact_mod_cast hcb)
        (by
          have h1 : (a' : ℤ) + (b' : ℤ) + (c' : ℤ) - 2 = ((d - 2 : ℕ) : ℤ) := by omega
          rw [h1]
          exact_mod_cast hih)
      have hfinal : (12 : ℤ) * (B.card : ℤ) ≤ ((a' : ℤ) + (b' : ℤ) + (c' : ℤ)) ^ 2 + 3 := by
        have hbc : (B.card : ℤ) ≤ (R.card : ℤ) + (c' : ℤ) := by omega
        linarith
      have hd_eq : (a' : ℤ) + (b' : ℤ) + (c' : ℤ) = (d : ℤ) := by omega
      rw [hd_eq] at hfinal
      exact_mod_cast hfinal

/-! ### Part 2: Linear forms and local sector uniqueness -/

private noncomputable def lam (t : ℝ) (i : Fin 3) (p : ℝ²) : ℝ :=
  let X := p 0 - t * p 1
  let Y := p 1 + t * p 0
  match i with
  | 0 => 2 * X
  | 1 => -X + Real.sqrt 3 * Y
  | 2 => -X - Real.sqrt 3 * Y

private lemma lam_sum_zero (t : ℝ) (p : ℝ²) :
    lam t 0 p + lam t 1 p + lam t 2 p = 0 := by
  simp only [lam]
  ring

private lemma lam_sub (t : ℝ) (i : Fin 3) (p q : ℝ²) :
    lam t i (p - q) = lam t i p - lam t i q := by
  fin_cases i <;> simp only [lam, PiLp.sub_apply] <;> ring

private lemma F_lam_eq (t : ℝ) (i : Fin 3) (w : ℝ²) :
    let j : Fin 3 := i + 1
    let k : Fin 3 := i + 2
    (lam t j w) ^ 2 + (lam t j w) * (lam t k w) + (lam t k w) ^ 2 =
      3 * (1 + t ^ 2) * ‖w‖ ^ 2 := by
  have hnorm : ‖w‖ ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [hnorm]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  match i with
  | 0 => change (lam t 1 w) ^ 2 + lam t 1 w * lam t 2 w + (lam t 2 w) ^ 2 = _; dsimp only [lam]; ring_nf; rw [h3]; ring
  | 1 => change (lam t 2 w) ^ 2 + lam t 2 w * lam t 0 w + (lam t 0 w) ^ 2 = _; dsimp only [lam]; ring_nf; rw [h3]; ring
  | 2 => change (lam t 0 w) ^ 2 + lam t 0 w * lam t 1 w + (lam t 1 w) ^ 2 = _; dsimp only [lam]; ring_nf; rw [h3]; ring

private lemma sector_F_lt {u v s w D : ℝ} (hu : 0 < u) (hv : 0 < v) (hs : 0 < s) (hw : 0 < w)
    (h1 : u ^ 2 + u * v + v ^ 2 = D) (h2 : s ^ 2 + s * w + w ^ 2 = D) :
    (u - s) ^ 2 + (u - s) * (v - w) + (v - w) ^ 2 < D := by
  have huv : D < (u + v) ^ 2 := by nlinarith
  have hsw : D < (s + w) ^ 2 := by nlinarith
  have hprod : D < (u + v) * (s + w) := by
    rcases le_total (u + v) (s + w) with h | h
    · exact huv.trans_le (by nlinarith)
    · exact hsw.trans_le (by nlinarith)
  nlinarith

private lemma exists_generic_t (S : Finset ℝ²) :
    ∃ t : ℝ, ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ i : Fin 3, lam t i p ≠ lam t i q := by
  -- For each `p ≠ q` and `i : Fin 3`, `lam t i (p - q) = A_i(p - q) + t * B_i(p - q)`
  -- where `(A_i, B_i) ≠ (0, 0)`, so it has at most one root `t`.
  let badPair : ℝ² × ℝ² × Fin 3 → Finset ℝ := fun ⟨p, q, i⟩ =>
    let dx := p 0 - q 0
    let dy := p 1 - q 1
    let a := match i with
      | 0 => 2 * dx
      | 1 => -dx + Real.sqrt 3 * dy
      | 2 => -dx - Real.sqrt 3 * dy
    let b := match i with
      | 0 => -2 * dy
      | 1 => dy + Real.sqrt 3 * dx
      | 2 => dy - Real.sqrt 3 * dx
    if b = 0 then ∅ else {-a / b}
  let bad : Finset ℝ := (S.offDiag ×ˢ (Finset.univ : Finset (Fin 3))).biUnion
    (fun x => badPair (x.1.1, x.1.2, x.2))
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad
  refine ⟨t, fun p hp q hq hpq i heq => ht ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨((p, q), i), Finset.mem_product.mpr ⟨Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, Finset.mem_univ i⟩, ?_⟩
  have h0 : lam t i (p - q) = 0 := by rw [lam_sub, heq, sub_self]
  have hneq : p 0 - q 0 ≠ 0 ∨ p 1 - q 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hpq
    ext k
    fin_cases k
    · exact sub_eq_zero.mp h.1
    · exact sub_eq_zero.mp h.2
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  match i with
  | 0 =>
    dsimp only [badPair]
    have hlin : 2 * (p 0 - q 0) + t * (-2 * (p 1 - q 1)) = 0 := by
      dsimp only [lam] at h0; simp only [PiLp.sub_apply] at h0; linear_combination h0
    by_cases hb : -2 * (p 1 - q 1) = 0
    · exfalso
      rw [hb, mul_zero, add_zero] at hlin
      rcases hneq with hx | hy
      · exact hx (by linarith)
      · exact hy (by linarith)
    · rw [if_neg hb, Finset.mem_singleton]
      exact (eq_div_iff hb).mpr (by linear_combination hlin)
  | 1 =>
    dsimp only [badPair]
    have hlin : (-((p 0 - q 0)) + Real.sqrt 3 * (p 1 - q 1)) +
        t * ((p 1 - q 1) + Real.sqrt 3 * (p 0 - q 0)) = 0 := by
      dsimp only [lam] at h0; simp only [PiLp.sub_apply] at h0; linear_combination h0
    by_cases hb : (p 1 - q 1) + Real.sqrt 3 * (p 0 - q 0) = 0
    · exfalso
      rw [hb, mul_zero, add_zero] at hlin
      have hsq : 4 * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) = 0 := by
        have h1 : (-(p 0 - q 0) + Real.sqrt 3 * (p 1 - q 1)) ^ 2 = 0 := by rw [hlin]; ring
        have h2 : ((p 1 - q 1) + Real.sqrt 3 * (p 0 - q 0)) ^ 2 = 0 := by rw [hb]; ring
        linear_combination h1 + h2 - ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) * h3
      rcases hneq with hx | hy
      · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (p 1 - q 1)]
      · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (p 0 - q 0)]
    · rw [if_neg hb, Finset.mem_singleton]
      exact (eq_div_iff hb).mpr (by linear_combination hlin)
  | 2 =>
    dsimp only [badPair]
    have hlin : (-((p 0 - q 0)) - Real.sqrt 3 * (p 1 - q 1)) +
        t * ((p 1 - q 1) - Real.sqrt 3 * (p 0 - q 0)) = 0 := by
      dsimp only [lam] at h0; simp only [PiLp.sub_apply] at h0; linear_combination h0
    by_cases hb : (p 1 - q 1) - Real.sqrt 3 * (p 0 - q 0) = 0
    · exfalso
      rw [hb, mul_zero, add_zero] at hlin
      have hsq : 4 * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) = 0 := by
        have h1 : (-(p 0 - q 0) - Real.sqrt 3 * (p 1 - q 1)) ^ 2 = 0 := by rw [hlin]; ring
        have h2 : ((p 1 - q 1) - Real.sqrt 3 * (p 0 - q 0)) ^ 2 = 0 := by rw [hb]; ring
        linear_combination h1 + h2 - ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) * h3
      rcases hneq with hx | hy
      · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (p 1 - q 1)]
      · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (p 0 - q 0)]
    · rw [if_neg hb, Finset.mem_singleton]
      exact (eq_div_iff hb).mpr (by linear_combination hlin)

/-! ### Part 3: Chains, ranks, and edge-chain counting -/

private lemma chain_add_edges_le {V : Type*} [DecidableEq V]
    (S : Finset V) (Q R : V → V → Prop) (E : Finset (V × V))
    (hQ_trans : ∀ {x y z}, Q x y → Q y z → Q x z)
    (hQR_disj : ∀ {x y}, Q x y → ¬ R x y ∧ ¬ R y x)
    (hQ_irrefl : ∀ x, ¬ Q x x)
    (hE_mem : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S ∧ Q e.1 e.2)
    (hE_fst : Set.InjOn Prod.fst (E : Set (V × V)))
    (hE_snd : Set.InjOn Prod.snd (E : Set (V × V)))
    (C : Finset V) (hCS : C ⊆ S)
    (hC_chain : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → R x y ∨ R y x) :
    C.card + E.card ≤ S.card := by
  let D : Finset V := S.filter (fun x => x ∈ C ∨ ∃ c ∈ C, Q x c)
  let φ : V × V → V := fun e => if e.2 ∈ D then e.1 else e.2
  have hφ_maps : ∀ e ∈ E, φ e ∈ S \ C := by
    intro e he
    have he' := hE_mem e he
    dsimp only [φ]
    split_ifs with h2D
    · rw [Finset.mem_sdiff]
      refine ⟨he'.1, fun h1C => ?_⟩
      have h2' := (Finset.mem_filter.mp h2D).2
      rcases h2' with h2C | ⟨c, hcC, hQ2c⟩
      · have hne : e.1 ≠ e.2 := fun h => hQ_irrefl e.1 (h ▸ he'.2.2)
        rcases hC_chain e.1 h1C e.2 h2C hne with hR | hR
        · exact (hQR_disj he'.2.2).1 hR
        · exact (hQR_disj he'.2.2).2 hR
      · have hQ1c : Q e.1 c := hQ_trans he'.2.2 hQ2c
        have hne : e.1 ≠ c := fun h => hQ_irrefl e.1 (h ▸ hQ1c)
        rcases hC_chain e.1 h1C c hcC hne with hR | hR
        · exact (hQR_disj hQ1c).1 hR
        · exact (hQR_disj hQ1c).2 hR
    · rw [Finset.mem_sdiff]
      refine ⟨he'.2.1, fun h2C => h2D (Finset.mem_filter.mpr ⟨he'.2.1, Or.inl h2C⟩)⟩
  have h1_in_D : ∀ e ∈ E, e.2 ∈ D → e.1 ∈ D := by
    intro e he h2D
    have he' := hE_mem e he
    have h2' := (Finset.mem_filter.mp h2D).2
    refine Finset.mem_filter.mpr ⟨he'.1, Or.inr ?_⟩
    rcases h2' with h2C | ⟨c, hcC, hQ2c⟩
    · exact ⟨e.2, h2C, he'.2.2⟩
    · exact ⟨c, hcC, hQ_trans he'.2.2 hQ2c⟩
  have hφ_inj : Set.InjOn φ (E : Set (V × V)) := by
    intro e₁ he₁ e₂ he₂ heq
    dsimp only [φ] at heq
    by_cases h1 : e₁.2 ∈ D <;> by_cases h2 : e₂.2 ∈ D <;> simp only [h1, h2, ↓reduceIte] at heq
    · exact hE_fst he₁ he₂ heq
    · exact absurd (heq ▸ h1_in_D e₁ (Finset.mem_coe.mp he₁) h1) h2
    · exact absurd (heq.symm ▸ h1_in_D e₂ (Finset.mem_coe.mp he₂) h2) h1
    · exact hE_snd he₁ he₂ heq
  have hle : E.card ≤ (S \ C).card :=
    Finset.card_le_card_of_injOn φ (fun e he => Finset.mem_coe.mpr (hφ_maps e (Finset.mem_coe.mp he))) hφ_inj
  rw [Finset.card_sdiff_of_subset hCS] at hle
  have hC_le : C.card ≤ S.card := Finset.card_le_card hCS
  omega

private noncomputable def rk {V : Type*} [DecidableEq V] (S : Finset V) (R : V → V → Prop) (p : V) : ℕ :=
  (S.powerset.filter (fun C =>
    (∀ x ∈ C, ∀ y ∈ C, x ≠ y → R x y ∨ R y x) ∧ ∀ x ∈ C, R x p)).sup Finset.card

private lemma rk_exists_chain {V : Type*} [DecidableEq V] (S : Finset V) (R : V → V → Prop) (p : V) :
    ∃ C ⊆ S, (∀ x ∈ C, ∀ y ∈ C, x ≠ y → R x y ∨ R y x) ∧ (∀ x ∈ C, R x p) ∧ C.card = rk S R p := by
  let F := S.powerset.filter (fun C =>
    (∀ x ∈ C, ∀ y ∈ C, x ≠ y → R x y ∨ R y x) ∧ ∀ x ∈ C, R x p)
  have hne : F.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset S, by simp, by simp⟩⟩
  obtain ⟨C, hCF, hCmax⟩ := Finset.exists_mem_eq_sup F hne Finset.card
  have hCF' := Finset.mem_filter.mp hCF
  exact ⟨C, Finset.mem_powerset.mp hCF'.1, hCF'.2.1, hCF'.2.2, hCmax.symm⟩

private lemma rk_lt {V : Type*} [DecidableEq V] (S : Finset V) (R : V → V → Prop)
    (hR_irrefl : ∀ x, ¬ R x x) (hR_trans : ∀ {x y z}, R x y → R y z → R x z)
    {p q : V} (hp : p ∈ S) (hpq : R p q) : rk S R p < rk S R q := by
  obtain ⟨C, hCS, hCchain, hClt, hCcard⟩ := rk_exists_chain S R p
  have hpC : p ∉ C := fun h => hR_irrefl p (hClt p h)
  have hmem : insert p C ∈ S.powerset.filter (fun D =>
      (∀ x ∈ D, ∀ y ∈ D, x ≠ y → R x y ∨ R y x) ∧ ∀ x ∈ D, R x q) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hp hCS), ?_, ?_⟩
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx' <;> rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact absurd rfl hxy
      · exact Or.inr (hClt y hy')
      · exact Or.inl (hClt x hx')
      · exact hCchain x hx' y hy' hxy
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hpq
      · exact hR_trans (hClt x hx') hpq
  have hle : (insert p C).card ≤ rk S R q := Finset.le_sup (f := Finset.card) hmem
  rw [Finset.card_insert_of_notMem hpC, hCcard] at hle
  omega

private lemma rk_lt_sub {V : Type*} [DecidableEq V]
    (S : Finset V) (Q R : V → V → Prop) (E : Finset (V × V))
    (hQ_trans : ∀ {x y z}, Q x y → Q y z → Q x z)
    (hQR_disj : ∀ {x y}, Q x y → ¬ R x y ∧ ¬ R y x)
    (hQ_irrefl : ∀ x, ¬ Q x x)
    (hR_irrefl : ∀ x, ¬ R x x)
    (hE_mem : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S ∧ Q e.1 e.2)
    (hE_fst : Set.InjOn Prod.fst (E : Set (V × V)))
    (hE_snd : Set.InjOn Prod.snd (E : Set (V × V)))
    {p : V} (hp : p ∈ S) : rk S R p < S.card - E.card := by
  obtain ⟨C, hCS, hCchain, hClt, hCcard⟩ := rk_exists_chain S R p
  have hpC : p ∉ C := fun h => hR_irrefl p (hClt p h)
  have hbd := chain_add_edges_le S Q R E hQ_trans hQR_disj hQ_irrefl hE_mem hE_fst hE_snd
    (insert p C) (Finset.insert_subset hp hCS) (by
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx' <;> rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact absurd rfl hxy
      · exact Or.inr (hClt y hy')
      · exact Or.inl (hClt x hx')
      · exact hCchain x hx' y hy' hxy)
  rw [Finset.card_insert_of_notMem hpC, hCcard] at hbd
  omega

end Erdos1084H3

theorem OMA.solution : OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1.H3 := by
  classical
  intro S hsep
  have hdist_ge : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → (1 : ℝ) ≤ dist p q := by
    intro p hp q hq hpq
    have he : (1 : ENNReal) ≤ edist p q := hsep hp hq hpq
    rw [edist_dist] at he
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    rw [h1] at he
    exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp he
  obtain ⟨t, ht_gen⟩ := Erdos1084H3.exists_generic_t S
  let Q : Fin 3 → ℝ² → ℝ² → Prop := fun i p q =>
    Erdos1084H3.lam t (i + 1) p < Erdos1084H3.lam t (i + 1) q ∧
    Erdos1084H3.lam t (i + 2) p < Erdos1084H3.lam t (i + 2) q
  let R : Fin 3 → ℝ² → ℝ² → Prop := fun i p q =>
    Erdos1084H3.lam t (i + 1) p < Erdos1084H3.lam t (i + 1) q ∧
    Erdos1084H3.lam t (i + 2) q < Erdos1084H3.lam t (i + 2) p
  let E : Fin 3 → Finset (ℝ² × ℝ²) := fun i =>
    (S ×ˢ S).filter (fun e => dist e.1 e.2 = 1 ∧ Q i e.1 e.2)
  have hQ_trans : ∀ i {x y z}, Q i x y → Q i y z → Q i x z :=
    fun i _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  have hQ_irrefl : ∀ i x, ¬ Q i x x := fun i x h => lt_irrefl _ h.1
  have hR_trans : ∀ i {x y z}, R i x y → R i y z → R i x z :=
    fun i _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩
  have hR_irrefl : ∀ i x, ¬ R i x x := fun i x h => lt_irrefl _ h.1
  have hQR_disj : ∀ i {x y}, Q i x y → ¬ R i x y ∧ ¬ R i y x :=
    fun i _ _ hQ => ⟨fun hR => lt_asymm hQ.2 hR.2, fun hR => lt_asymm hQ.1 hR.1⟩
  have hE_mem : ∀ i e, e ∈ E i → e.1 ∈ S ∧ e.2 ∈ S ∧ Q i e.1 e.2 := by
    intro i e he
    have he' := Finset.mem_filter.mp he
    have hp := Finset.mem_product.mp he'.1
    exact ⟨hp.1, hp.2, he'.2.2⟩
  have hE_fst : ∀ i, Set.InjOn Prod.fst (E i : Set (ℝ² × ℝ²)) := by
    intro i e₁ he₁ e₂ he₂ heq
    have h1 := Finset.mem_filter.mp (Finset.mem_coe.mp he₁)
    have h2 := Finset.mem_filter.mp (Finset.mem_coe.mp he₂)
    have hp1 := Finset.mem_product.mp h1.1
    have hp2 := Finset.mem_product.mp h2.1
    rcases e₁ with ⟨p, q₁⟩; rcases e₂ with ⟨p', q₂⟩
    dsimp only at heq; subst heq
    by_contra hne
    have hqne : q₁ ≠ q₂ := fun h => hne (by rw [h])
    have hge : (1 : ℝ) ≤ dist q₁ q₂ := hdist_ge q₁ hp1.2 q₂ hp2.2 hqne
    have hu : 0 < Erdos1084H3.lam t (i + 1) (q₁ - p) := by
      rw [Erdos1084H3.lam_sub]; linarith [h1.2.2.1]
    have hv : 0 < Erdos1084H3.lam t (i + 2) (q₁ - p) := by
      rw [Erdos1084H3.lam_sub]; linarith [h1.2.2.2]
    have hs : 0 < Erdos1084H3.lam t (i + 1) (q₂ - p) := by
      rw [Erdos1084H3.lam_sub]; linarith [h2.2.2.1]
    have hw : 0 < Erdos1084H3.lam t (i + 2) (q₂ - p) := by
      rw [Erdos1084H3.lam_sub]; linarith [h2.2.2.2]
    have hF1 : (Erdos1084H3.lam t (i + 1) (q₁ - p)) ^ 2 +
        (Erdos1084H3.lam t (i + 1) (q₁ - p)) * (Erdos1084H3.lam t (i + 2) (q₁ - p)) +
        (Erdos1084H3.lam t (i + 2) (q₁ - p)) ^ 2 = 3 * (1 + t ^ 2) := by
      have := Erdos1084H3.F_lam_eq t i (q₁ - p)
      have hn : ‖q₁ - p‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact h1.2.1
      rw [hn] at this; linarith
    have hF2 : (Erdos1084H3.lam t (i + 1) (q₂ - p)) ^ 2 +
        (Erdos1084H3.lam t (i + 1) (q₂ - p)) * (Erdos1084H3.lam t (i + 2) (q₂ - p)) +
        (Erdos1084H3.lam t (i + 2) (q₂ - p)) ^ 2 = 3 * (1 + t ^ 2) := by
      have := Erdos1084H3.F_lam_eq t i (q₂ - p)
      have hn : ‖q₂ - p‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact h2.2.1
      rw [hn] at this; linarith
    have hlt := Erdos1084H3.sector_F_lt hu hv hs hw hF1 hF2
    have hdiff1 : Erdos1084H3.lam t (i + 1) (q₁ - p) - Erdos1084H3.lam t (i + 1) (q₂ - p) =
        Erdos1084H3.lam t (i + 1) (q₁ - q₂) := by
      rw [Erdos1084H3.lam_sub, Erdos1084H3.lam_sub, Erdos1084H3.lam_sub]; ring
    have hdiff2 : Erdos1084H3.lam t (i + 2) (q₁ - p) - Erdos1084H3.lam t (i + 2) (q₂ - p) =
        Erdos1084H3.lam t (i + 2) (q₁ - q₂) := by
      rw [Erdos1084H3.lam_sub, Erdos1084H3.lam_sub, Erdos1084H3.lam_sub]; ring
    rw [hdiff1, hdiff2, Erdos1084H3.F_lam_eq t i (q₁ - q₂)] at hlt
    have hn1 : (1 : ℝ) ≤ ‖q₁ - q₂‖ ^ 2 := by
      rw [← dist_eq_norm]; nlinarith
    nlinarith [sq_nonneg t]
  have hE_snd : ∀ i, Set.InjOn Prod.snd (E i : Set (ℝ² × ℝ²)) := by
    intro i e₁ he₁ e₂ he₂ heq
    have h1 := Finset.mem_filter.mp (Finset.mem_coe.mp he₁)
    have h2 := Finset.mem_filter.mp (Finset.mem_coe.mp he₂)
    have hp1 := Finset.mem_product.mp h1.1
    have hp2 := Finset.mem_product.mp h2.1
    rcases e₁ with ⟨p₁, q⟩; rcases e₂ with ⟨p₂, q'⟩
    dsimp only at heq; subst heq
    by_contra hne
    have hpne : p₁ ≠ p₂ := fun h => hne (by rw [h])
    have hge : (1 : ℝ) ≤ dist p₁ p₂ := hdist_ge p₁ hp1.1 p₂ hp2.1 hpne
    have hu : 0 < Erdos1084H3.lam t (i + 1) (q - p₁) := by
      rw [Erdos1084H3.lam_sub]; linarith [h1.2.2.1]
    have hv : 0 < Erdos1084H3.lam t (i + 2) (q - p₁) := by
      rw [Erdos1084H3.lam_sub]; linarith [h1.2.2.2]
    have hs : 0 < Erdos1084H3.lam t (i + 1) (q - p₂) := by
      rw [Erdos1084H3.lam_sub]; linarith [h2.2.2.1]
    have hw : 0 < Erdos1084H3.lam t (i + 2) (q - p₂) := by
      rw [Erdos1084H3.lam_sub]; linarith [h2.2.2.2]
    have hF1 : (Erdos1084H3.lam t (i + 1) (q - p₁)) ^ 2 +
        (Erdos1084H3.lam t (i + 1) (q - p₁)) * (Erdos1084H3.lam t (i + 2) (q - p₁)) +
        (Erdos1084H3.lam t (i + 2) (q - p₁)) ^ 2 = 3 * (1 + t ^ 2) := by
      have := Erdos1084H3.F_lam_eq t i (q - p₁)
      have hn : ‖q - p₁‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact h1.2.1
      rw [hn] at this; linarith
    have hF2 : (Erdos1084H3.lam t (i + 1) (q - p₂)) ^ 2 +
        (Erdos1084H3.lam t (i + 1) (q - p₂)) * (Erdos1084H3.lam t (i + 2) (q - p₂)) +
        (Erdos1084H3.lam t (i + 2) (q - p₂)) ^ 2 = 3 * (1 + t ^ 2) := by
      have := Erdos1084H3.F_lam_eq t i (q - p₂)
      have hn : ‖q - p₂‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact h2.2.1
      rw [hn] at this; linarith
    have hlt := Erdos1084H3.sector_F_lt hu hv hs hw hF1 hF2
    have hdiff1 : Erdos1084H3.lam t (i + 1) (q - p₁) - Erdos1084H3.lam t (i + 1) (q - p₂) =
        Erdos1084H3.lam t (i + 1) (p₂ - p₁) := by
      rw [Erdos1084H3.lam_sub, Erdos1084H3.lam_sub, Erdos1084H3.lam_sub]; ring
    have hdiff2 : Erdos1084H3.lam t (i + 2) (q - p₁) - Erdos1084H3.lam t (i + 2) (q - p₂) =
        Erdos1084H3.lam t (i + 2) (p₂ - p₁) := by
      rw [Erdos1084H3.lam_sub, Erdos1084H3.lam_sub, Erdos1084H3.lam_sub]; ring
    rw [hdiff1, hdiff2, Erdos1084H3.F_lam_eq t i (p₂ - p₁)] at hlt
    have hn1 : (1 : ℝ) ≤ ‖p₂ - p₁‖ ^ 2 := by
      rw [← dist_eq_norm, dist_comm]; nlinarith
    nlinarith [sq_nonneg t]
  -- Partition `unitDistNum S` into `E 0`, `E 1`, `E 2`.
  have hsum_edges : (E 0).card + (E 1).card + (E 2).card = unitDistNum S := by
    let allE : Finset (Σ i : Fin 3, ℝ² × ℝ²) := Finset.univ.sigma E
    have hcard_sigma : allE.card = (E 0).card + (E 1).card + (E 2).card := by
      rw [Finset.card_sigma, Fin.sum_univ_three]
    rw [← hcard_sigma]
    unfold unitDistNum
    refine Finset.card_bij (fun x _ => s(x.2.1, x.2.2)) ?_ ?_ ?_
    · intro x hx
      rcases Finset.mem_sigma.mp hx with ⟨_, hxe⟩
      have hxe' := Finset.mem_filter.mp hxe
      have hp := Finset.mem_product.mp hxe'.1
      refine Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr hp, ?_⟩
      have hout : s((s(x.2.1, x.2.2) : Sym2 ℝ²).out.1, (s(x.2.1, x.2.2) : Sym2 ℝ²).out.2) =
          s(x.2.1, x.2.2) := Quot.out_eq s(x.2.1, x.2.2)
      rcases Sym2.eq_iff.mp hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hxe'.2.1
      · rw [h1, h2, dist_comm]; exact hxe'.2.1
    · intro x hx y hy hxy
      rcases x with ⟨xi, x1, x2⟩
      rcases y with ⟨yi, y1, y2⟩
      rcases Finset.mem_sigma.mp hx with ⟨_, hxe⟩
      rcases Finset.mem_sigma.mp hy with ⟨_, hye⟩
      have hxe' := Finset.mem_filter.mp hxe
      have hye' := Finset.mem_filter.mp hye
      have hQneg : ∀ i p q, Q i p q → Erdos1084H3.lam t i q < Erdos1084H3.lam t i p := by
        intro i p q hQ
        have hs1 := Erdos1084H3.lam_sum_zero t p
        have hs2 := Erdos1084H3.lam_sum_zero t q
        match i with
        | 0 => change Erdos1084H3.lam t 1 p < Erdos1084H3.lam t 1 q ∧ Erdos1084H3.lam t 2 p < Erdos1084H3.lam t 2 q at hQ; linarith
        | 1 => change Erdos1084H3.lam t 2 p < Erdos1084H3.lam t 2 q ∧ Erdos1084H3.lam t 0 p < Erdos1084H3.lam t 0 q at hQ; linarith
        | 2 => change Erdos1084H3.lam t 0 p < Erdos1084H3.lam t 0 q ∧ Erdos1084H3.lam t 1 p < Erdos1084H3.lam t 1 q at hQ; linarith
      rcases Sym2.eq_iff.mp hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · dsimp only at h1 h2
        subst h1; subst h2
        have h1eq : xi = yi := by
          have hQx : Q xi x1 x2 := hxe'.2.2
          have hQy : Q yi x1 x2 := hye'.2.2
          by_contra hne
          have hnx := hQneg xi _ _ hQx
          match xi, yi with
          | 0, 0 | 1, 1 | 2, 2 => exact absurd rfl hne
          | 0, 1 => exact absurd hnx (not_lt.mpr (show Erdos1084H3.lam t 0 x1 < Erdos1084H3.lam t 0 x2 from hQy.2).le)
          | 0, 2 => exact absurd hnx (not_lt.mpr (show Erdos1084H3.lam t 0 x1 < Erdos1084H3.lam t 0 x2 from hQy.1).le)
          | 1, 0 => exact absurd hnx (not_lt.mpr (show Erdos1084H3.lam t 1 x1 < Erdos1084H3.lam t 1 x2 from hQy.1).le)
          | 1, 2 => exact absurd hnx (not_lt.mpr (show Erdos1084H3.lam t 1 x1 < Erdos1084H3.lam t 1 x2 from hQy.2).le)
          | 2, 0 => exact absurd hnx (not_lt.mpr (show Erdos1084H3.lam t 2 x1 < Erdos1084H3.lam t 2 x2 from hQy.2).le)
          | 2, 1 => exact absurd hnx (not_lt.mpr (show Erdos1084H3.lam t 2 x1 < Erdos1084H3.lam t 2 x2 from hQy.1).le)
        subst h1eq; rfl
      · exfalso
        dsimp only at h1 h2
        have hQx : Q xi x1 x2 := hxe'.2.2
        have hQy : Q yi x2 x1 := by rw [h1, h2]; exact hye'.2.2
        have hnx := hQneg xi _ _ hQx
        have hny := hQneg yi _ _ hQy
        match xi, yi with
        | 0, 0 => exact lt_asymm hQx.1 hQy.1
        | 1, 1 => exact lt_asymm hQx.1 hQy.1
        | 2, 2 => exact lt_asymm hQx.1 hQy.1
        | 0, 1 => exact lt_asymm (show Erdos1084H3.lam t 2 x1 < Erdos1084H3.lam t 2 x2 from hQx.2) (show Erdos1084H3.lam t 2 x2 < Erdos1084H3.lam t 2 x1 from hQy.1)
        | 0, 2 => exact lt_asymm (show Erdos1084H3.lam t 1 x1 < Erdos1084H3.lam t 1 x2 from hQx.1) (show Erdos1084H3.lam t 1 x2 < Erdos1084H3.lam t 1 x1 from hQy.2)
        | 1, 0 => exact lt_asymm (show Erdos1084H3.lam t 2 x1 < Erdos1084H3.lam t 2 x2 from hQx.1) (show Erdos1084H3.lam t 2 x2 < Erdos1084H3.lam t 2 x1 from hQy.2)
        | 1, 2 => exact lt_asymm (show Erdos1084H3.lam t 0 x1 < Erdos1084H3.lam t 0 x2 from hQx.2) (show Erdos1084H3.lam t 0 x2 < Erdos1084H3.lam t 0 x1 from hQy.1)
        | 2, 0 => exact lt_asymm (show Erdos1084H3.lam t 1 x1 < Erdos1084H3.lam t 1 x2 from hQx.2) (show Erdos1084H3.lam t 1 x2 < Erdos1084H3.lam t 1 x1 from hQy.1)
        | 2, 1 => exact lt_asymm (show Erdos1084H3.lam t 0 x1 < Erdos1084H3.lam t 0 x2 from hQx.1) (show Erdos1084H3.lam t 0 x2 < Erdos1084H3.lam t 0 x1 from hQy.2)
    · intro u hu
      have hu' := Finset.mem_filter.mp hu
      let p := u.out.1
      let q := u.out.2
      have hu_eq : s(p, q) = u := Quot.out_eq u
      have hpq_mem : p ∈ S ∧ q ∈ S := Finset.mk_mem_sym2_iff.mp (hu_eq ▸ hu'.1)
      have hdist : dist p q = 1 := hu'.2
      have hpq_ne : p ≠ q := fun h => by rw [h, dist_self] at hdist; norm_num at hdist
      have hd0 : Erdos1084H3.lam t 0 p ≠ Erdos1084H3.lam t 0 q := ht_gen p hpq_mem.1 q hpq_mem.2 hpq_ne 0
      have hd1 : Erdos1084H3.lam t 1 p ≠ Erdos1084H3.lam t 1 q := ht_gen p hpq_mem.1 q hpq_mem.2 hpq_ne 1
      have hd2 : Erdos1084H3.lam t 2 p ≠ Erdos1084H3.lam t 2 q := ht_gen p hpq_mem.1 q hpq_mem.2 hpq_ne 2
      have hsp := Erdos1084H3.lam_sum_zero t p
      have hsq := Erdos1084H3.lam_sum_zero t q
      have hcases : (∃ i : Fin 3, Q i p q) ∨ (∃ i : Fin 3, Q i q p) := by
        rcases lt_or_gt_of_ne hd0 with h0 | h0 <;>
          rcases lt_or_gt_of_ne hd1 with h1 | h1 <;>
          rcases lt_or_gt_of_ne hd2 with h2 | h2
        · linarith
        · exact Or.inl ⟨2, h0, h1⟩
        · exact Or.inl ⟨1, h2, h0⟩
        · exact Or.inr ⟨0, h1, h2⟩
        · exact Or.inl ⟨0, h1, h2⟩
        · exact Or.inr ⟨1, h2, h0⟩
        · exact Or.inr ⟨2, h0, h1⟩
        · linarith
      rcases hcases with ⟨i, hQ⟩ | ⟨i, hQ⟩
      · refine ⟨⟨i, (p, q)⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ i,
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hpq_mem, hdist, hQ⟩⟩, hu_eq⟩
      · refine ⟨⟨i, (q, p)⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ i,
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpq_mem.2, hpq_mem.1⟩,
            dist_comm p q ▸ hdist, hQ⟩⟩, by rw [Sym2.eq_swap]; exact hu_eq⟩
  -- Each `e_i ≤ n`.
  have he_le : ∀ i : Fin 3, (E i).card ≤ S.card := fun i => by
    have := Erdos1084H3.chain_add_edges_le S (Q i) (R i) (E i)
      (hQ_trans i) (hQR_disj i) (hQ_irrefl i) (hE_mem i) (hE_fst i) (hE_snd i)
      ∅ (Finset.empty_subset S) (by simp)
    simpa using this
  -- Map `S` into `[0, n - e₀) × [0, n - e₁) × [0, n - e₂)` via rank triples.
  let f : ℝ² → ℕ × ℕ × ℕ := fun p =>
    (Erdos1084H3.rk S (R 0) p, Erdos1084H3.rk S (R 1) p, Erdos1084H3.rk S (R 2) p)
  have hf_box : ∀ p ∈ S,
      (f p).1 < S.card - (E 0).card ∧
      (f p).2.1 < S.card - (E 1).card ∧
      (f p).2.2 < S.card - (E 2).card := by
    intro p hp
    exact ⟨Erdos1084H3.rk_lt_sub S (Q 0) (R 0) (E 0) (hQ_trans 0) (hQR_disj 0) (hQ_irrefl 0)
        (hR_irrefl 0) (hE_mem 0) (hE_fst 0) (hE_snd 0) hp,
      Erdos1084H3.rk_lt_sub S (Q 1) (R 1) (E 1) (hQ_trans 1) (hQR_disj 1) (hQ_irrefl 1)
        (hR_irrefl 1) (hE_mem 1) (hE_fst 1) (hE_snd 1) hp,
      Erdos1084H3.rk_lt_sub S (Q 2) (R 2) (E 2) (hQ_trans 2) (hQR_disj 2) (hQ_irrefl 2)
        (hR_irrefl 2) (hE_mem 2) (hE_fst 2) (hE_snd 2) hp⟩
  have hf_incomp : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      (∃ i : Fin 3, R i p q) ∧ (∃ j : Fin 3, R j q p) := by
    intro p hp q hq hpq
    have hd0 := ht_gen p hp q hq hpq 0
    have hd1 := ht_gen p hp q hq hpq 1
    have hd2 := ht_gen p hp q hq hpq 2
    have hsp := Erdos1084H3.lam_sum_zero t p
    have hsq := Erdos1084H3.lam_sum_zero t q
    rcases lt_or_gt_of_ne hd0 with h0 | h0 <;>
      rcases lt_or_gt_of_ne hd1 with h1 | h1 <;>
      rcases lt_or_gt_of_ne hd2 with h2 | h2
    · linarith
    · exact ⟨⟨0, h1, h2⟩, ⟨1, h2, h0⟩⟩
    · exact ⟨⟨2, h0, h1⟩, ⟨0, h1, h2⟩⟩
    · exact ⟨⟨2, h0, h1⟩, ⟨1, h2, h0⟩⟩
    · exact ⟨⟨1, h2, h0⟩, ⟨2, h0, h1⟩⟩
    · exact ⟨⟨0, h1, h2⟩, ⟨2, h0, h1⟩⟩
    · exact ⟨⟨1, h2, h0⟩, ⟨0, h1, h2⟩⟩
    · linarith
  have hf_inj : Set.InjOn f (S : Set ℝ²) := by
    intro p hp q hq heq
    by_contra hpq
    obtain ⟨⟨i, hR⟩, _⟩ := hf_incomp p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq) hpq
    have hlt := Erdos1084H3.rk_lt S (R i) (hR_irrefl i) (hR_trans i) (Finset.mem_coe.mp hp) hR
    fin_cases i
    · have h0 : Erdos1084H3.rk S (R 0) p < Erdos1084H3.rk S (R 0) q := hlt
      have := congrArg Prod.fst heq; dsimp only [f] at this; omega
    · have h1 : Erdos1084H3.rk S (R 1) p < Erdos1084H3.rk S (R 1) q := hlt
      have := congrArg (fun x => x.2.1) heq; dsimp only [f] at this; omega
    · have h2 : Erdos1084H3.rk S (R 2) p < Erdos1084H3.rk S (R 2) q := hlt
      have := congrArg (fun x => x.2.2) heq; dsimp only [f] at this; omega
  have hf_anti : Erdos1084H3.IsAntichain3 (S.image f) := by
    intro x hx y hy h1 h2 h3
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    by_contra hne
    have hpq : p ≠ q := fun h => hne (by rw [h])
    obtain ⟨_, ⟨j, hR⟩⟩ := hf_incomp p hp q hq hpq
    have hlt := Erdos1084H3.rk_lt S (R j) (hR_irrefl j) (hR_trans j) hq hR
    fin_cases j
    · have h0 : Erdos1084H3.rk S (R 0) q < Erdos1084H3.rk S (R 0) p := hlt
      dsimp only [f] at h1; omega
    · have h1' : Erdos1084H3.rk S (R 1) q < Erdos1084H3.rk S (R 1) p := hlt
      dsimp only [f] at h2; omega
    · have h2' : Erdos1084H3.rk S (R 2) q < Erdos1084H3.rk S (R 2) p := hlt
      dsimp only [f] at h3; omega
  have hbound := Erdos1084H3.antichain_box_bound
    (3 * S.card - unitDistNum S)
    (S.card - (E 0).card) (S.card - (E 1).card) (S.card - (E 2).card)
    (by
      have h0 := he_le 0; have h1 := he_le 1; have h2 := he_le 2
      omega)
    (S.image f)
    (by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
      exact hf_box p hp)
    hf_anti
  rwa [Finset.card_image_of_injOn hf_inj] at hbound
