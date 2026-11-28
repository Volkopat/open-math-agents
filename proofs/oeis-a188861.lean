import OMAStatements.S_oeis_a188861
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix on the 16 possible rows (Fin 4 -> Fin 2). Arrays are counted row by row
-- (Fin.init/Fin.snoc bijection); the dual vectors satisfy u4 + u2 = 2 u3 (decide +kernel),
-- so a(n) is linear from n = 3 on; base values 16, 41, 68, 95 by decide +kernel.

namespace OMA.S_oeis_a188861

abbrev St := Fin 4 → Fin 2

def ok (r s : St) : Prop :=
  ∀ c d : Fin 4, (d.val = c.val ∨ d.val = c.val + 1 ∨ c.val = d.val + 1) → ¬ (r c = 0 ∧ s d = 1)

instance (r s : St) : Decidable (ok r s) := by unfold ok; infer_instance

def w : ℕ → St → ℕ
  | 0, _ => 1
  | k + 1, s => ∑ r : St, if ok r s then w k r else 0

def u : ℕ → St → ℕ
  | 0, _ => 1
  | j + 1, r => ∑ s : St, if ok r s then u j s else 0

def Gd (k : ℕ) (x : Fin (k + 1) → St) : Prop := ∀ i : Fin k, ok (x i.castSucc) (x i.succ)

instance (k : ℕ) : DecidablePred (Gd k) := fun x => by unfold Gd; infer_instance

lemma hp_iff (k : ℕ) (x : Fin (k + 1) → St) : ¬ HasPattern x ↔ Gd k x := by
  unfold HasPattern Gd ok
  constructor
  · intro h i c d hcd hx
    exact h ⟨i.castSucc, i.succ, by simp, c, d, hcd, hx.1, hx.2⟩
  · rintro h ⟨i, j, hij, c, d, hcd, h1, h2⟩
    have hi : i.val < k := by omega
    have e1 : (⟨i.val, hi⟩ : Fin k).castSucc = i := Fin.ext rfl
    have e2 : (⟨i.val, hi⟩ : Fin k).succ = j := Fin.ext (by simp [hij])
    have := h ⟨i.val, hi⟩ c d hcd
    rw [e1, e2] at this
    exact this ⟨h1, h2⟩

lemma gd_succ (k : ℕ) (x : Fin (k + 2) → St) :
    Gd (k + 1) x ↔ Gd k (Fin.init x) ∧ ok (x (Fin.last k).castSucc) (x (Fin.last (k + 1))) := by
  unfold Gd
  rw [Fin.forall_fin_succ']
  simp only [Fin.init, Fin.succ_castSucc, Fin.succ_last]

def cnt (k : ℕ) (s : St) : ℕ :=
  (Finset.univ.filter (fun x : Fin (k + 1) → St => x (Fin.last k) = s ∧ Gd k x)).card

lemma cnt_zero (s : St) : cnt 0 s = 1 := by
  unfold cnt
  rw [Finset.card_eq_one]
  refine ⟨fun _ => s, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
  · rintro rfl; exact ⟨rfl, fun i => i.elim0⟩

lemma cnt_succ (k : ℕ) (s : St) :
    cnt (k + 1) s = ∑ r : St, if ok r s then cnt k r else 0 := by
  have e : cnt (k + 1) s = (Finset.univ.filter
      (fun g : Fin (k + 1) → St => Gd k g ∧ ok (g (Fin.last k)) s)).card := by
    unfold cnt
    apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g s)
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
      obtain ⟨hl, hg⟩ := hf
      rw [gd_succ] at hg
      refine ⟨hg.1, ?_⟩
      have := hg.2; rw [hl] at this; simpa [Fin.init] using this
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      obtain ⟨hg, ha⟩ := hg
      refine ⟨by simp, ?_⟩
      rw [gd_succ]
      refine ⟨by simpa using hg, ?_⟩
      simpa using ha
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf
      rw [← hf.1]; exact Fin.snoc_init_self f
    · intro g _; exact Fin.init_snoc _ _
  rw [e, Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → St => g (Fin.last k))
    (t := Finset.univ) (fun g _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.filter_filter]
  split_ifs with h
  · unfold cnt; congr 1; apply Finset.filter_congr
    intro g _
    constructor
    · rintro ⟨⟨hg, -⟩, hx⟩; exact ⟨hx, hg⟩
    · rintro ⟨hx, hg⟩; exact ⟨⟨hg, hx ▸ h⟩, hx⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨⟨-, ha⟩, hx⟩; exact h (hx ▸ ha)

lemma cnt_eq (k : ℕ) (s : St) : cnt k s = w k s := by
  induction k generalizing s with
  | zero => rw [cnt_zero]; rfl
  | succ k ih =>
    rw [cnt_succ k s, w]
    apply Finset.sum_congr rfl
    intro r _
    rw [ih r]

lemma a_w (k : ℕ) : a (k + 1) = ∑ s : St, w k s := by
  unfold a
  rw [Finset.filter_congr (fun x _ => hp_iff k x)]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → St => g (Fin.last k))
    (t := Finset.univ) (fun g _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [← cnt_eq, cnt, Finset.filter_filter]
  congr 1; apply Finset.filter_congr
  intro x _; exact and_comm

lemma dual (j k : ℕ) : ∑ s : St, w (k + j) s = ∑ r : St, w k r * u j r := by
  induction j generalizing k with
  | zero => simp [u]
  | succ j ih =>
    rw [show k + (j + 1) = (k + 1) + j by ring, ih (k + 1)]
    simp only [w, u, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    split_ifs <;> simp

set_option maxRecDepth 100000 in
lemma hU : ∀ r : St, u 4 r + u 2 r = 2 * u 3 r := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma hV : ∑ r : St, u 0 r = 16 ∧ ∑ r : St, u 1 r = 41 ∧ ∑ r : St, u 2 r = 68 ∧
    ∑ r : St, u 3 r = 95 := by
  decide +kernel

lemma a_u (j : ℕ) : a (j + 1) = ∑ r : St, u j r := by
  rw [a_w, show j = 0 + j by ring, dual j 0]
  simp [w]

lemma arec (k : ℕ) : a (k + 5) + a (k + 3) = 2 * a (k + 4) := by
  rw [show k + 5 = (k + 4) + 1 by ring, show k + 3 = (k + 2) + 1 by ring,
    show k + 4 = (k + 3) + 1 by ring, a_w, a_w, a_w, dual 4 k, dual 2 k, dual 3 k]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro r _
  have := hU r
  calc w k r * u 4 r + w k r * u 2 r = w k r * (u 4 r + u 2 r) := by ring
    _ = w k r * (2 * u 3 r) := by rw [this]
    _ = 2 * (w k r * u 3 r) := by ring

theorem main_proof : a 1 = 16 ∧ ∀ n : ℕ, 2 ≤ n → a n = 27 * n - 13  := by
  obtain ⟨v1, v2, v3, v4⟩ := hV
  have b1 : a 1 = 16 := by rw [a_u 0]; exact v1
  have b2 : a 2 = 41 := by rw [a_u 1]; exact v2
  have b3 : a 3 = 68 := by rw [a_u 2]; exact v3
  have b4 : a 4 = 95 := by rw [a_u 3]; exact v4
  refine ⟨b1, ?_⟩
  have key : ∀ m : ℕ, a (m + 3) = 27 * (m + 3) - 13 ∧ a (m + 4) = 27 * (m + 4) - 13 := by
    intro m
    induction m with
    | zero => exact ⟨b3, b4⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have := arec m
      rw [show m + 1 + 4 = m + 5 by ring]
      omega
  intro n hn
  rcases (show n = 2 ∨ 3 ≤ n by omega) with h | h
  · subst h; exact b2
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    exact (key m).1

end OMA.S_oeis_a188861

theorem OMA.solution : type_of% @OMA.S_oeis_a188861.main := OMA.S_oeis_a188861.main_proof
