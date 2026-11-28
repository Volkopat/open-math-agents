import OMAStatements.S_mo_341790
import Mathlib

/-!
MathOverflow 341790: the lower bound follows from `π x x = μ x - ∑_{y ≠ x} π x y` and
`π x y ≤ ν y`. For attainment, at most one `x₀` has `μ x₀ + ν x₀ > 1`; we put the excess
`μ x₀ + ν x₀ - 1` on `(x₀, x₀)` and couple what is left with no mass on the diagonal. A coupling
of weights of total mass `m` with no diagonal mass exists whenever `μ x + ν x ≤ m` for all `x`
(the condition from the answers of Mateusz Kwaśnicki and Bjørn Kjos-Hanssen); we prove this by
merging the two points with the smallest `μ + ν` (at least four points) and splitting the merged
row and column proportionally, with explicit couplings for at most three points.
-/

namespace OMA.P341790

open Finset OMA.S_mo_341790

section General

variable {α : Type*} [DecidableEq α]

/-- `π` is a coupling of `μ` and `ν` on `s` with no mass on the diagonal. -/
def ZD (s : Finset α) (μ ν : α → ℝ) (π : α → α → ℝ) : Prop :=
  (∀ x y, 0 ≤ π x y) ∧ (∀ x, π x x = 0) ∧ (∀ x ∈ s, ∑ y ∈ s, π x y = μ x) ∧
    (∀ y ∈ s, ∑ x ∈ s, π x y = ν y)

/-- The hypotheses: nonnegative weights of total mass `m` with `μ x + ν x ≤ m`. -/
def Hyp (s : Finset α) (m : ℝ) (μ ν : α → ℝ) : Prop :=
  (∀ x ∈ s, 0 ≤ μ x) ∧ (∀ x ∈ s, 0 ≤ ν x) ∧ ∑ x ∈ s, μ x = m ∧ ∑ x ∈ s, ν x = m ∧
    ∀ x ∈ s, μ x + ν x ≤ m

lemma sum_upd (s : Finset α) (f : α → ℝ) (i : α) (hi : i ∈ s) (v : ℝ) :
    ∑ x ∈ s, Function.update f i v x = v + ∑ x ∈ s.erase i, f x := by
  rw [← add_sum_erase s _ hi, Function.update_self]
  congr 1
  refine sum_congr rfl fun x hx => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hx)]

lemma two_le_sum (s : Finset α) (f : α → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) {x y : α} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) : f x + f y ≤ ∑ z ∈ s, f z := by
  rw [← add_sum_erase s _ hx, ← add_sum_erase (s.erase x) _ (mem_erase.2 ⟨hxy.symm, hy⟩)]
  have : 0 ≤ ∑ z ∈ (s.erase x).erase y, f z :=
    sum_nonneg fun z hz => hf z (mem_of_mem_erase (mem_of_mem_erase hz))
  linarith

/-- Splitting weight of a merged point. -/
noncomputable def wt (μ : α → ℝ) (b c x : α) : ℝ :=
  if x = b then μ b / (μ b + μ c) else if x = c then μ c / (μ b + μ c) else 1

/-- The merge map `c ↦ b`. -/
def rr (b c x : α) : α := if x = c then b else x

/-- Lift of a coupling on the merged instance. -/
noncomputable def lift (μ ν : α → ℝ) (b c : α) (π : α → α → ℝ) (x y : α) : ℝ :=
  wt μ b c x * wt ν b c y * π (rr b c x) (rr b c y)

lemma wt_nonneg (μ : α → ℝ) (b c x : α) (hb : 0 ≤ μ b) (hc : 0 ≤ μ c) : 0 ≤ wt μ b c x := by
  unfold wt; split_ifs
  · exact div_nonneg hb (add_nonneg hb hc)
  · exact div_nonneg hc (add_nonneg hb hc)
  · exact zero_le_one

lemma split_sum (s : Finset α) {b c : α} (hb : b ∈ s) (hc : c ∈ s) (hbc : b ≠ c)
    (w : α → ℝ) (hw : ∀ y, y ≠ b → y ≠ c → w y = 1) (g : α → ℝ)
    (hg : (w b + w c - 1) * g b = 0) :
    ∑ y ∈ s, w y * g (rr b c y) = ∑ y ∈ s.erase c, g y := by
  have hb' : b ∈ s.erase c := mem_erase.2 ⟨hbc, hb⟩
  rw [← add_sum_erase s _ hc, ← add_sum_erase (s.erase c) _ hb', ← add_sum_erase (s.erase c) _ hb']
  have e1 : ∑ y ∈ (s.erase c).erase b, w y * g (rr b c y) = ∑ y ∈ (s.erase c).erase b, g y := by
    refine sum_congr rfl fun y hy => ?_
    have h1 := ne_of_mem_erase hy
    have h2 := ne_of_mem_erase (mem_of_mem_erase hy)
    simp [rr, h2, hw y h1 h2]
  rw [e1]
  simp only [rr, if_neg hbc, ↓reduceIte]
  linear_combination hg

lemma rows (s : Finset α) {b c : α} (hb : b ∈ s) (hc : c ∈ s) (hbc : b ≠ c) (μ ν : α → ℝ)
    (hμ : ∀ x ∈ s, 0 ≤ μ x) (π : α → α → ℝ) (h0 : ∀ x y, 0 ≤ π x y)
    (hrow : ∀ x ∈ s.erase c, ∑ y ∈ s.erase c, π x y = Function.update μ b (μ b + μ c) x)
    (hcol : ∀ y ∈ s.erase c, ∑ x ∈ s.erase c, π x y = Function.update ν b (ν b + ν c) y) :
    ∀ x ∈ s, ∑ y ∈ s, lift μ ν b c π x y = μ x := by
  intro x hx
  have hb' : b ∈ s.erase c := mem_erase.2 ⟨hbc, hb⟩
  have hrx : rr b c x ∈ s.erase c := by
    unfold rr; split_ifs with h
    · exact hb'
    · exact mem_erase.2 ⟨h, hx⟩
  have hsum : ∑ y ∈ s, lift μ ν b c π x y =
      wt μ b c x * ∑ y ∈ s, wt ν b c y * π (rr b c x) (rr b c y) := by
    rw [mul_sum]; refine sum_congr rfl fun y _ => ?_; unfold lift; ring
  rw [hsum, split_sum s hb hc hbc (wt ν b c) (fun y h1 h2 => by simp [wt, h1, h2])]
  · rw [hrow _ hrx]
    by_cases hxc : x = c
    · subst hxc
      simp only [wt, rr, if_neg hbc.symm, ↓reduceIte, Function.update_self]
      by_cases hS : μ b + μ x = 0
      · have : μ x = 0 := by linarith [hμ b hb, hμ x hc]
        rw [hS, this]; simp
      · field_simp
    · by_cases hxb : x = b
      · subst hxb
        simp only [wt, rr, if_neg hxc, ↓reduceIte, Function.update_self]
        by_cases hS : μ x + μ c = 0
        · have : μ x = 0 := by linarith [hμ x hb, hμ c hc]
          rw [hS, this]; simp
        · field_simp
      · simp only [wt, rr, if_neg hxc, if_neg hxb, Function.update_of_ne hxb, one_mul]
  · by_cases hS : ν b + ν c = 0
    · have hcb := hcol b hb'
      rw [Function.update_self, hS] at hcb
      have := (sum_eq_zero_iff_of_nonneg (fun x _ => h0 x b)).1 hcb _ hrx
      rw [this, mul_zero]
    · have : wt ν b c b + wt ν b c c = 1 := by
        simp only [wt, ↓reduceIte, if_neg hbc.symm]
        rw [← add_div, div_self hS]
      rw [this]; ring

lemma lift_ZD (s : Finset α) {b c : α} (hb : b ∈ s) (hc : c ∈ s) (hbc : b ≠ c)
    (μ ν : α → ℝ) (hμ : ∀ x ∈ s, 0 ≤ μ x) (hν : ∀ x ∈ s, 0 ≤ ν x) (π : α → α → ℝ)
    (hπ : ZD (s.erase c) (Function.update μ b (μ b + μ c)) (Function.update ν b (ν b + ν c)) π) :
    ZD s μ ν (lift μ ν b c π) := by
  obtain ⟨h0, hd, hrow, hcol⟩ := hπ
  refine ⟨fun x y => ?_, fun x => ?_, rows s hb hc hbc μ ν hμ π h0 hrow hcol, fun y hy => ?_⟩
  · exact mul_nonneg (mul_nonneg (wt_nonneg μ b c x (hμ b hb) (hμ c hc))
      (wt_nonneg ν b c y (hν b hb) (hν c hc))) (h0 _ _)
  · simp [lift, hd]
  · have := rows s hb hc hbc ν μ hν (fun x y => π y x) (fun x y => h0 y x) hcol hrow y hy
    rw [← this]
    refine sum_congr rfl fun x _ => ?_
    unfold lift; ring

lemma base (s : Finset α) (m : ℝ) (μ ν : α → ℝ) (h : Hyp s m μ ν) (hs : s.card ≤ 3) :
    ∃ π, ZD s μ ν π := by
  obtain ⟨hμ, hν, sμ, sν, hc⟩ := h
  interval_cases hcard : s.card
  · rw [card_eq_zero] at hcard; subst hcard
    exact ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ => rfl, by simp, by simp⟩
  · obtain ⟨a, rfl⟩ := card_eq_one.1 hcard
    simp only [sum_singleton] at sμ sν
    have := hc a (mem_singleton_self a)
    have h1 : μ a = 0 := by linarith [hμ a (mem_singleton_self a), hν a (mem_singleton_self a)]
    have h2 : ν a = 0 := by linarith [hμ a (mem_singleton_self a), hν a (mem_singleton_self a)]
    refine ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ => rfl, ?_, ?_⟩ <;>
      intro x hx <;> rw [mem_singleton.1 hx] <;> simp [h1, h2]
  · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hcard
    have ma := hμ a (by simp); have mb := hμ b (by simp)
    have ca := hc a (by simp); have cb := hc b (by simp)
    rw [sum_pair hab] at sμ sν
    refine ⟨fun x y => if x = a ∧ y = b then μ a else if x = b ∧ y = a then μ b else 0,
      fun x y => ?_, fun x => ?_, fun x hx => ?_, fun y hy => ?_⟩
    · dsimp only; split_ifs <;> linarith
    · dsimp only; split_ifs with h1 h2
      · exact absurd (h1.1.symm.trans h1.2) hab
      · exact absurd (h2.2.symm.trans h2.1) hab
      · rfl
    · rcases mem_insert.1 hx with rfl | hx
      · simp [sum_pair hab, hab, Ne.symm hab]
      · rw [mem_singleton.1 hx]; simp [sum_pair hab, hab, Ne.symm hab]
    · rcases mem_insert.1 hy with rfl | hy
      · simp [sum_pair hab, hab, Ne.symm hab]; linarith
      · rw [mem_singleton.1 hy]; simp [sum_pair hab, hab, Ne.symm hab]; linarith
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.1 hcard
    have ma := hμ a (by simp); have mb := hμ b (by simp); have mc := hμ c (by simp)
    have na := hν a (by simp); have nb := hν b (by simp); have nc := hν c (by simp)
    have ca := hc a (by simp); have cb := hc b (by simp); have cc := hc c (by simp)
    have hbc' : b ∉ ({c} : Finset α) := by simp [hbc]
    have habc : a ∉ ({b, c} : Finset α) := by simp [hab, hac]
    rw [sum_insert habc, sum_insert hbc', sum_singleton] at sμ sν
    set t := max (max 0 (ν b - μ c)) (μ a - ν c) with ht
    have t0 : 0 ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
    have t1 : ν b - μ c ≤ t := le_trans (le_max_right _ _) (le_max_left _ _)
    have t2 : μ a - ν c ≤ t := le_max_right _ _
    have u1 : t ≤ μ a := max_le (max_le ma (by linarith)) (by linarith)
    have u2 : t ≤ ν b := max_le (max_le nb (by linarith)) (by linarith)
    have u3 : t ≤ ν a + ν b - μ c := max_le (max_le (by linarith) (by linarith)) (by linarith)
    refine ⟨fun x y => if x = a ∧ y = b then t else if x = a ∧ y = c then μ a - t else
      if x = c ∧ y = b then ν b - t else if x = c ∧ y = a then μ c - ν b + t else
      if x = b ∧ y = a then ν a - μ c + ν b - t else if x = b ∧ y = c then ν c - μ a + t else 0,
      fun x y => ?_, fun x => ?_, fun x hx => ?_, fun y hy => ?_⟩
    · dsimp only; split_ifs <;> linarith
    · dsimp only; split_ifs with h1 h2 h3 h4 h5 h6
      · exact absurd (h1.1.symm.trans h1.2) hab
      · exact absurd (h2.1.symm.trans h2.2) hac
      · exact absurd (h3.2.symm.trans h3.1) hbc
      · exact absurd (h4.2.symm.trans h4.1) hac
      · exact absurd (h5.2.symm.trans h5.1) hab
      · exact absurd (h6.1.symm.trans h6.2) hbc
      · rfl
    · rw [sum_insert habc, sum_insert hbc', sum_singleton]
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;>
        simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc] <;> linarith
    · rw [sum_insert habc, sum_insert hbc', sum_singleton]
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;>
        simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc] <;> linarith

theorem Z (n : ℕ) : ∀ (s : Finset α), s.card = n → ∀ (m : ℝ) (μ ν : α → ℝ), Hyp s m μ ν →
    ∃ π, ZD s μ ν π := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs m μ ν h
  by_cases h3 : n ≤ 3
  · exact base s m μ ν h (hs ▸ h3)
  obtain ⟨hμ, hν, sμ, sν, hc⟩ := h
  have hne : s.Nonempty := card_pos.1 (by omega)
  obtain ⟨b, hb, hbmin⟩ := s.exists_min_image (fun x => μ x + ν x) hne
  have hne' : (s.erase b).Nonempty := card_pos.1 (by rw [card_erase_of_mem hb]; omega)
  obtain ⟨c, hc', hcmin⟩ := (s.erase b).exists_min_image (fun x => μ x + ν x) hne'
  have hcb : c ≠ b := ne_of_mem_erase hc'
  have hcs : c ∈ s := mem_of_mem_erase hc'
  have hbc' : b ∈ s.erase c := mem_erase.2 ⟨hcb.symm, hb⟩
  -- the two smallest values of `μ + ν` add up to at most `m`
  have hsmall : (μ b + ν b) + (μ c + ν c) ≤ m := by
    have htot : ∑ x ∈ s, (μ x + ν x) = 2 * m := by rw [sum_add_distrib, sμ, sν]; ring
    have hcard : ((s.erase b).erase c).card = n - 2 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨hcb, hcs⟩), card_erase_of_mem hb, hs]; omega
    have hlow : ((s.erase b).erase c).card • (μ c + ν c) ≤
        ∑ x ∈ (s.erase b).erase c, (μ x + ν x) :=
      card_nsmul_le_sum _ _ _ fun x hx => hcmin x (mem_of_mem_erase hx)
    rw [hcard, nsmul_eq_mul] at hlow
    have h2 : (2 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by
      have : 2 ≤ n - 2 := by omega
      exact_mod_cast this
    have hcnn : 0 ≤ μ c + ν c := add_nonneg (hμ c hcs) (hν c hcs)
    rw [← add_sum_erase s _ hb, ← add_sum_erase (s.erase b) _ hc'] at htot
    have := hbmin c hcs
    nlinarith
  obtain ⟨π, hπ⟩ := ih (n - 1) (by omega) (s.erase c) (by rw [card_erase_of_mem hcs, hs]) m
    (Function.update μ b (μ b + μ c)) (Function.update ν b (ν b + ν c)) (by
      refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, ?_, fun x hx => ?_⟩
      · by_cases hxb : x = b
        · subst hxb; rw [Function.update_self]; linarith [hμ x hb, hμ c hcs]
        · rw [Function.update_of_ne hxb]; exact hμ x (mem_of_mem_erase hx)
      · by_cases hxb : x = b
        · subst hxb; rw [Function.update_self]; linarith [hν x hb, hν c hcs]
        · rw [Function.update_of_ne hxb]; exact hν x (mem_of_mem_erase hx)
      · rw [sum_upd _ _ _ hbc', ← sμ, ← add_sum_erase s _ hcs, ← add_sum_erase (s.erase c) _ hbc']
        ring
      · rw [sum_upd _ _ _ hbc', ← sν, ← add_sum_erase s _ hcs, ← add_sum_erase (s.erase c) _ hbc']
        ring
      · by_cases hxb : x = b
        · subst hxb; rw [Function.update_self, Function.update_self]; linarith
        · rw [Function.update_of_ne hxb, Function.update_of_ne hxb]
          exact hc x (mem_of_mem_erase hx))
  exact ⟨_, lift_ZD s hb hcs hcb.symm μ ν hμ hν π hπ⟩

end General

theorem proof_aux :
    ∀ (n : ℕ) (μ ν : Fin n → ℝ), (∀ x, 0 ≤ μ x) → (∀ x, 0 ≤ ν x) → ∑ x, μ x = 1 →
      ∑ x, ν x = 1 → IsLeast (diagonalMasses μ ν) (∑ x, max (μ x + ν x - 1) 0) := by
  intro n μ ν hμ hν sμ sν
  refine ⟨?_, ?_⟩
  · by_cases hall : ∀ x, μ x + ν x ≤ 1
    · obtain ⟨π, h0, hd, hr, hc⟩ := Z (univ : Finset (Fin n)).card univ rfl 1 μ ν
        ⟨fun x _ => hμ x, fun x _ => hν x, sμ, sν, fun x _ => hall x⟩
      refine ⟨π, h0, fun x => hr x (mem_univ x), fun y => hc y (mem_univ y), ?_⟩
      rw [sum_eq_zero fun x _ => max_eq_right (by linarith [hall x]),
        sum_eq_zero fun x _ => hd x]
    · push_neg at hall
      obtain ⟨x0, hx0⟩ := hall
      set e := μ x0 + ν x0 - 1 with he
      have hle : ∀ (f : Fin n → ℝ), (∀ x, 0 ≤ f x) → ∑ x, f x = 1 → ∀ x y, x ≠ y →
          f x + f y ≤ 1 := fun f hf sf x y hxy => by
        rw [← sf]; exact two_le_sum univ f (fun z _ => hf z) (mem_univ x) (mem_univ y) hxy
      have hle1 : ∀ (f : Fin n → ℝ), (∀ x, 0 ≤ f x) → ∑ x, f x = 1 → ∀ x, f x ≤ 1 :=
        fun f hf sf x => by rw [← sf]; exact single_le_sum (fun z _ => hf z) (mem_univ x)
      have hx0' : x0 ∈ (univ : Finset (Fin n)) := mem_univ x0
      obtain ⟨π, h0, hd, hr, hc⟩ := Z (univ : Finset (Fin n)).card univ rfl (1 - e)
        (Function.update μ x0 (1 - ν x0)) (Function.update ν x0 (1 - μ x0)) (by
          refine ⟨fun x _ => ?_, fun x _ => ?_, ?_, ?_, fun x _ => ?_⟩
          · by_cases hx : x = x0
            · subst hx; rw [Function.update_self]; linarith [hle1 ν hν sν x]
            · rw [Function.update_of_ne hx]; exact hμ x
          · by_cases hx : x = x0
            · subst hx; rw [Function.update_self]; linarith [hle1 μ hμ sμ x]
            · rw [Function.update_of_ne hx]; exact hν x
          · rw [sum_upd _ _ _ hx0', ← add_sum_erase univ _ hx0'] at *
            linarith
          · rw [sum_upd _ _ _ hx0']
            rw [← add_sum_erase univ _ hx0'] at sν
            linarith
          · by_cases hx : x = x0
            · subst hx; rw [Function.update_self, Function.update_self]; linarith
            · rw [Function.update_of_ne hx, Function.update_of_ne hx]
              linarith [hle μ hμ sμ x x0 hx, hle ν hν sν x x0 hx])
      refine ⟨fun x y => π x y + if x = x0 then (if y = x0 then e else 0) else 0,
        fun x y => ?_, fun x => ?_, fun y => ?_, ?_⟩
      · have := h0 x y
        dsimp only; split_ifs <;> linarith
      · rw [sum_add_distrib, hr x (mem_univ x)]
        by_cases hx : x = x0
        · subst hx; simp [Function.update_self]; linarith
        · simp [hx, Function.update_of_ne hx]
      · rw [sum_add_distrib, hc y (mem_univ y)]
        by_cases hy : y = x0
        · subst hy; simp [Function.update_self]; linarith
        · simp [hy, Function.update_of_ne hy]
      · rw [sum_add_distrib, sum_eq_zero fun x _ => hd x, zero_add, ← add_sum_erase univ _ hx0',
          ← add_sum_erase univ _ hx0', sum_eq_zero, sum_eq_zero]
        · simp only [↓reduceIte]
          rw [max_eq_left (by linarith), he]
        · intro x hx
          rw [if_neg (ne_of_mem_erase hx)]
        · intro x hx
          have hxx := ne_of_mem_erase hx
          rw [max_eq_right]
          linarith [hle μ hμ sμ x x0 hxx, hle ν hν sν x x0 hxx]
  · rintro d ⟨π, h0, hr, hc, rfl⟩
    refine sum_le_sum fun x _ => max_le ?_ (h0 x x)
    have hrow := hr x
    rw [← add_sum_erase univ _ (mem_univ x)] at hrow
    have hcol : ∑ y ∈ univ.erase x, ν y = 1 - ν x := by
      rw [← sν, ← add_sum_erase univ _ (mem_univ x)]; ring
    have : ∑ y ∈ univ.erase x, π x y ≤ ∑ y ∈ univ.erase x, ν y := by
      refine sum_le_sum fun y _ => ?_
      rw [← hc y]
      exact single_le_sum (fun z _ => h0 z y) (mem_univ x)
    linarith

end OMA.P341790

theorem OMA.solution : type_of% @OMA.S_mo_341790.main := OMA.P341790.proof_aux
