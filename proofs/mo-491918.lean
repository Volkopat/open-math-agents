import OMAStatements.S_mo_491918
import Mathlib

/-!
Disproof of mo-491918 as posed: n = 3, m = 5, the first player values the items 1, 1, 1, 0, 0 and the
other two players value every item 0. The first player opens with a worthless item and ends with value 1,
while he values the second player's bundle at 2. The proof: a one-shot deviation principle for this game
(spne_of_oneshot), then finite checks of the explicit profile sig by kernel evaluation.
-/

-- Original Lean proof by @tatashbar (PR #11264; statement #4758).
-- List extension and finite-universe witness arguments now use Mathlib.

namespace OMA.S_mo_491918

/-! ### One-shot deviation principle for this game -/

theorem finish_step {n m : ℕ} (hn : 0 < n) (σ : Fin n → Strategy m) (h : List (Fin m))
    (hlt : h.length < m) :
    finish hn σ h = finish hn σ (h ++ [σ (mover hn h) h]) := by
  unfold finish
  have e : m - h.length = (m - (h ++ [σ (mover hn h) h]).length) + 1 := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [e]; rfl

theorem finish_done {n m : ℕ} (hn : 0 < n) (σ : Fin n → Strategy m) (h : List (Fin m))
    (hlen : m ≤ h.length) : finish hn σ h = h := by
  unfold finish
  have e : m - h.length = 0 := by omega
  rw [e]; rfl

theorem spne_of_oneshot {n m : ℕ} (hn : 0 < n) (P : Fin n → Fin m → ℝ) (σ : Fin n → Strategy m)
    (hleg : ∀ i, Legal (σ i))
    (h1 : ∀ h : List (Fin m), h.Nodup → h.length < m → ∀ a : Fin m, a ∉ h →
      value P (mover hn h) (bundle (finish hn σ (h ++ [a])) (mover hn h)) ≤
        value P (mover hn h) (bundle (finish hn σ h) (mover hn h))) :
    IsSPNE hn P σ := by
  refine ⟨hleg, ?_⟩
  intro h hnd hle i s hs
  generalize hk : m - h.length = k
  induction k generalizing h with
  | zero =>
    have hlen : m ≤ h.length := by omega
    rw [finish_done hn _ h hlen, finish_done hn _ h hlen]
  | succ k ih =>
    have hlt : h.length < m := by omega
    by_cases hi : mover hn h = i
    · have ha : s h ∉ h := hs h hnd hlt
      have hnd' : (h ++ [s h]).Nodup := by
        simpa using List.Nodup.concat ha hnd
      have hlen' : (h ++ [s h]).length ≤ m := by
        simp only [List.length_append, List.length_singleton]; omega
      have hk' : m - (h ++ [s h]).length = k := by
        simp only [List.length_append, List.length_singleton]; omega
      have step1 := ih (h ++ [s h]) hnd' hlen' hk'
      have step2 := h1 h hnd hlt (s h) ha
      rw [hi] at step2
      rw [finish_step hn (Function.update σ i s) h hlt]
      have e : Function.update σ i s (mover hn h) h = s h := by
        rw [hi, Function.update_self]
      rw [e]
      exact le_trans step1 step2
    · have ha : σ (mover hn h) h ∉ h := hleg _ h hnd hlt
      have hnd' : (h ++ [σ (mover hn h) h]).Nodup := by
        simpa using List.Nodup.concat ha hnd
      have hlen' : (h ++ [σ (mover hn h) h]).length ≤ m := by
        simp only [List.length_append, List.length_singleton]; omega
      have hk' : m - (h ++ [σ (mover hn h) h]).length = k := by
        simp only [List.length_append, List.length_singleton]; omega
      have step1 := ih (h ++ [σ (mover hn h) h]) hnd' hlen' hk'
      rw [finish_step hn (Function.update σ i s) h hlt, finish_step hn σ h hlt]
      have e : Function.update σ i s (mover hn h) h = σ (mover hn h) h := by
        rw [Function.update_of_ne hi]
      rw [e]
      exact step1

/-! ### The counterexample -/

/-- first unclaimed item in the given order -/
def pick (order : List (Fin 5)) (h : List (Fin 5)) : Fin 5 :=
  (order.find? (fun j => decide (j ∉ h))).getD 0

def up : List (Fin 5) := [0, 1, 2, 3, 4]
def down : List (Fin 5) := [4, 3, 2, 1, 0]

def s0 : Strategy 5 := fun h => match h with
  | [] => 3
  | _ :: _ => pick up h

def s1 : Strategy 5 := fun h => pick up h

def s2 : Strategy 5 := fun h => match h with
  | [] => 0
  | x :: _ => if x.val < 3 then pick up h else pick down h

def sig : Fin 3 → Strategy 5 := fun i => match i with
  | 0 => s0
  | 1 => s1
  | 2 => s2

def Pex : Fin 3 → Fin 5 → ℝ := fun i j => if i = 0 ∧ j.val < 3 then 1 else 0

/-- number of the three valuable items in a bundle -/
def cnt (S : Finset (Fin 5)) : ℕ := (S.filter (fun j => j.val < 3)).card

theorem value_zero (S : Finset (Fin 5)) : value Pex 0 S = (cnt S : ℝ) := by
  unfold value cnt Pex
  simp [Finset.sum_ite]

theorem value_other (i : Fin 3) (hi : i ≠ 0) (S : Finset (Fin 5)) : value Pex i S = 0 := by
  unfold value Pex
  simp [hi]

theorem exists_free (h : List (Fin 5)) (hlt : h.length < 5) : ∃ j : Fin 5, j ∉ h := by
  exact Cardinal.exists_notMem_of_length_lt h (by simpa using hlt)

theorem pick_free (order : List (Fin 5)) (hall : ∀ j : Fin 5, j ∈ order) (h : List (Fin 5))
    (hnd : h.Nodup) (hlt : h.length < 5) : pick order h ∉ h := by
  obtain ⟨j, hj⟩ := exists_free h hlt
  unfold pick
  cases hf : order.find? (fun j => decide (j ∉ h)) with
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf j (hall j)
    simp [hj] at this
  | some x =>
    have := List.find?_some hf
    simpa using this

theorem up_all : ∀ j : Fin 5, j ∈ up := by decide
theorem down_all : ∀ j : Fin 5, j ∈ down := by decide

theorem legal_sig : ∀ i, Legal (sig i) := by
  intro i h hnd hlt
  fin_cases i
  · show s0 h ∉ h
    cases h with
    | nil => simp
    | cons x t => exact pick_free up up_all _ hnd hlt
  · exact pick_free up up_all _ hnd hlt
  · show s2 h ∉ h
    cases h with
    | nil => simp
    | cons x t =>
      show (if x.val < 3 then pick up (x :: t) else pick down (x :: t)) ∉ x :: t
      split
      · exact pick_free up up_all _ hnd hlt
      · exact pick_free down down_all _ hnd hlt

theorem check0 : ∀ d : Fin 5,
    cnt (bundle (finish (by decide : 0 < 3) sig [d]) (0 : Fin 3)) ≤
      cnt (bundle (finish (by decide : 0 < 3) sig []) (0 : Fin 3)) := by
  decide +kernel

theorem check3 : ∀ a b c d : Fin 5, [a, b, c].Nodup → d ∉ [a, b, c] →
    cnt (bundle (finish (by decide : 0 < 3) sig [a, b, c, d]) (0 : Fin 3)) ≤
      cnt (bundle (finish (by decide : 0 < 3) sig [a, b, c]) (0 : Fin 3)) := by
  decide +kernel

theorem spne_sig : IsSPNE (by decide : 0 < 3) Pex sig := by
  apply spne_of_oneshot _ _ _ legal_sig
  intro h hnd hlt a ha
  by_cases hm : mover (by decide : 0 < 3) h = (0 : Fin 3)
  · rw [hm, value_zero, value_zero, Nat.cast_le]
    have hmod : h.length % 3 = 0 := by
      have := congrArg Fin.val hm
      simpa [mover] using this
    have hcases : h.length = 0 ∨ h.length = 3 := by omega
    rcases hcases with h0 | h3
    · have : h = [] := List.length_eq_zero_iff.mp h0
      subst this
      exact check0 a
    · obtain ⟨x, y, z, rfl⟩ := List.length_eq_three.mp h3
      exact check3 x y z a hnd ha
  · rw [value_other _ hm, value_other _ hm]

theorem envy : cnt (bundle (finish (by decide : 0 < 3) sig []) (0 : Fin 3)) <
    cnt (bundle (finish (by decide : 0 < 3) sig []) (1 : Fin 3)) := by
  decide +kernel

end OMA.S_mo_491918

open OMA.S_mo_491918 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_491918.main) := by
  intro hc
  have h := hc 3 5 (by decide) Pex (by intro i j; unfold Pex; split <;> norm_num) sig spne_sig 1
    (by decide)
  have e0 : (⟨0, (by decide : 0 < 3)⟩ : Fin 3) = 0 := rfl
  rw [e0, value_zero, value_zero, Nat.cast_le] at h
  exact absurd h (not_le.mpr envy)

