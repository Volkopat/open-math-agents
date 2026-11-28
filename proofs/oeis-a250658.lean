import OMAStatements.S_oeis_a250658
import Mathlib

-- Problem: oeis-a250658 (OEIS A250658), the linear recurrence of R. H. Hardin and the generating
-- function of Colin Barker for the number of admissible arrays.
-- Statement: statements/oeis-a250658.lean
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof sketch (transfer matrix method).
-- 1. An admissible array is a sequence of columns (states) in which adjacent states are
--    related by the relation R (lemma good_iff). There are 32 states.
-- 2. The number of sequences with n+1 states that start in s is w n s, where w 0 s = 1 and
--    w (n+1) s is the sum of w n t over all t with R s t (lemmas ch_cons, cnt_eq, total).
-- 3. The states are coded by the numbers below 32. The kernel checks the table Tm of R and the
--    vectors V0, V1, ... of the values of w (lemmas hT, hV0, hV1, ...).
-- 4. The combination of the vectors w n0, ..., w (n0+d) with the coefficients of the recurrence
--    is the zero vector for n0 = 0 (lemma base). Each later vector is the image of the earlier
--    vector by the same linear map, thus the combination stays zero (lemmas comb_succ, comb_zero).
-- 5. The sum over all states gives the recurrence for a(n); the first terms are sums of V1, V2, ...

namespace OMA.A250658

open Finset

section Generic

variable {α : Type} [Fintype α] [DecidableEq α] (R : α → α → Prop) [DecidableRel R]

/-- A sequence of `n+1` states in which adjacent states are related by `R`. -/
def Ch (n : ℕ) (f : Fin (n + 1) → α) : Prop := ∀ i : Fin n, R (f i.castSucc) (f i.succ)

instance instDecCh (n : ℕ) : DecidablePred (Ch R n) := fun f => by unfold Ch; infer_instance

/-- `w n s` is the number of walks with `n` steps that start in `s` (transfer matrix recursion). -/
def w : ℕ → α → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then w n t else 0

lemma w_succ (n : ℕ) (s : α) : w R (n + 1) s = ∑ t, if R s t then w R n t else 0 := rfl

lemma ch_cons (n : ℕ) (a : α) (g : Fin (n + 1) → α) :
    Ch R (n + 1) (Fin.cons a g : Fin (n + 2) → α) ↔ R a (g 0) ∧ Ch R n g := by
  unfold Ch
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]

lemma cnt_eq (n : ℕ) (s : α) :
    (univ.filter (fun f : Fin (n + 1) → α => Ch R n f ∧ f 0 = s)).card = w R n s := by
  induction n generalizing s with
  | zero =>
    show _ = 1
    rw [Finset.card_eq_one]
    refine ⟨fun _ => s, ?_⟩
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      funext i
      have hi : i = 0 := by
        apply Fin.ext
        have := i.isLt
        simp only [Fin.val_zero]
        omega
      rw [hi]
      exact h
    · rintro rfl
      exact ⟨fun i => i.elim0, rfl⟩
  | succ n ih =>
    rw [w_succ, Finset.card_filter, ← (Fin.consEquiv (fun _ : Fin (n + 2) => α)).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, ch_cons, Fin.cons_zero]
    rw [Finset.sum_eq_single s (fun a _ ha => Finset.sum_eq_zero (fun g _ => if_neg (fun h => ha h.2)))
      (fun h => absurd (mem_univ s) h)]
    have e2 : ∀ t, (if R s t then w R n t else 0) =
        ∑ g : Fin (n + 1) → α, (if R s t ∧ Ch R n g ∧ g 0 = t then 1 else 0) := by
      intro t
      rw [← ih t, Finset.card_filter]
      by_cases h : R s t
      · simp [h]
      · simp [h]
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Finset.sum_eq_single (g 0)]
    · by_cases h1 : R s (g 0) <;> by_cases h2 : Ch R n g <;> simp [h1, h2]
    · intro t _ ht
      exact if_neg (fun h => ht h.2.2.symm)
    · intro h
      exact absurd (mem_univ _) h

lemma total (n : ℕ) :
    (univ.filter (fun f : Fin (n + 1) → α => Ch R n f)).card = ∑ s, w R n s := by
  simp only [← cnt_eq, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [Finset.sum_eq_single (f 0)]
  · by_cases h : Ch R n f <;> simp [h]
  · intro t _ ht
    exact if_neg (fun h => ht h.2.symm)
  · intro h
    exact absurd (mem_univ _) h

/-- A fixed integer combination of `w n`, `w (n+1)`, ... -/
def comb : List ℤ → ℕ → α → ℤ
  | [], _, _ => 0
  | c :: cs, n, s => c * (w R n s : ℤ) + comb cs (n + 1) s

lemma comb_succ (L : List ℤ) (n : ℕ) (s : α) :
    comb R L (n + 1) s = ∑ t, if R s t then comb R L n t else 0 := by
  induction L generalizing n with
  | nil => simp [comb]
  | cons c cs ih =>
    simp only [comb]
    rw [ih, w_succ]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h : R s t <;> simp [h]

lemma comb_zero (L : List ℤ) (n0 : ℕ) (h0 : ∀ s, comb R L n0 s = 0) :
    ∀ n, n0 ≤ n → ∀ s, comb R L n s = 0 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h0
  | succ n _ ih =>
    intro s
    rw [comb_succ]
    exact Finset.sum_eq_zero (fun t _ => by rw [ih t]; simp)

/-- The same combination of the totals. -/
def combA : List ℤ → ℕ → ℤ
  | [], _ => 0
  | c :: cs, n => c * ((∑ s, w R n s : ℕ) : ℤ) + combA cs (n + 1)

lemma combA_eq (L : List ℤ) (n : ℕ) : combA R L n = ∑ s, comb R L n s := by
  induction L generalizing n with
  | nil => simp [comb, combA]
  | cons c cs ih =>
    simp only [comb, combA]
    rw [ih, Finset.sum_add_distrib]
    push_cast
    rw [Finset.mul_sum]

/-- Dot product of a 0/1 row, coded by the binary digits of `msk`, with a vector. -/
def dotm : ℕ → List ℕ → ℕ
  | _, [] => 0
  | msk, x :: xs => (if msk % 2 = 1 then x else 0) + dotm (msk / 2) xs

/-- Binary digit `b` of `msk`. -/
def bit (msk b : ℕ) : Bool := decide (msk / 2 ^ b % 2 = 1)

lemma bit_succ (msk b : ℕ) : bit msk (b + 1) = bit (msk / 2) b := by
  unfold bit
  rw [pow_succ', ← Nat.div_div_eq_div_mul]

lemma dotm_eq (v : List ℕ) (msk : ℕ) :
    dotm msk v = ∑ b ∈ range v.length, if bit msk b then v.getD b 0 else 0 := by
  induction v generalizing msk with
  | nil => simp [dotm]
  | cons x xs ih =>
    simp only [dotm, List.length_cons]
    rw [Finset.sum_range_succ', ih]
    simp only [bit_succ, List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]
    congr 1
    simp [bit]

lemma sum_getD (v : List ℕ) : ∑ b ∈ range v.length, v.getD b 0 = v.sum := by
  induction v with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.sum_cons]
    rw [Finset.sum_range_succ', ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

variable (dec : ℕ → α) (m : ℕ) (hsum : ∀ F : α → ℕ, ∑ t, F t = ∑ b ∈ range m, F (dec b))
include hsum

lemma step_ok (Tm : List ℕ) (hTl : Tm.length = m)
    (hT : ∀ a < m, ∀ b < m, decide (R (dec a) (dec b)) = bit (Tm.getD a 0) b)
    (v v' : List ℕ) (hl : v.length = m) (hstep : Tm.map (fun msk => dotm msk v) = v') (i : ℕ)
    (hv : ∀ a < m, w R i (dec a) = v.getD a 0) :
    ∀ a < m, w R (i + 1) (dec a) = v'.getD a 0 := by
  intro a ha
  subst hstep
  have h1 : (Tm.map (fun msk => dotm msk v)).getD a 0 = dotm (Tm.getD a 0) v := by
    have ha' : a < Tm.length := by rw [hTl]; exact ha
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha']
  rw [h1, dotm_eq, hl, w_succ, hsum]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hb' := Finset.mem_range.1 hb
  rw [← hT a ha b hb', hv b hb']
  by_cases h : R (dec a) (dec b) <;> simp [h]

lemma tot_ok (v : List ℕ) (hl : v.length = m) (i : ℕ)
    (hv : ∀ a < m, w R i (dec a) = v.getD a 0) : ∑ s, w R i s = v.sum := by
  rw [hsum, ← sum_getD, hl]
  exact Finset.sum_congr rfl (fun b hb => hv b (Finset.mem_range.1 hb))

end Generic

/-! ### The concrete transfer matrix -/

open OMA.S_oeis_a250658 in
instance instDecBlk : ∀ a b c d : Fin 2, Decidable (Blk a b c d) := fun a b c d => by
  unfold Blk; infer_instance

/-- The state: one column of the array. -/
abbrev St : Type := Fin 5 → Fin 2

/-- Two adjacent columns are compatible. -/
def R (s t : St) : Prop :=
  ∀ i : Fin 4, OMA.S_oeis_a250658.Blk (s i.castSucc) (t i.castSucc) (s i.succ) (t i.succ)

instance instDecR : DecidableRel R := fun s t => by unfold R; infer_instance

/-- The state with code `b` (digits of `b` in base 2). -/
def dec (b : ℕ) : St := fun i => ⟨b / 2 ^ (i : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩

lemma hsum (F : St → ℕ) : ∑ t, F t = ∑ b ∈ range 32, F (dec b) := by
  rw [← Fin.sum_univ_eq_sum_range (fun b => F (dec b)) 32]
  exact ((finFunctionFinEquiv (m := 2) (n := 5)).symm.sum_comp F).symm

lemma dec_surj (s : St) : ∃ b, b < 32 ∧ dec b = s :=
  ⟨(finFunctionFinEquiv (m := 2) (n := 5) s : ℕ), (finFunctionFinEquiv (m := 2) (n := 5) s).isLt,
    (finFunctionFinEquiv (m := 2) (n := 5)).symm_apply_apply s⟩

/-- Row `a` of the transfer matrix, coded in binary. -/
def Tm : List ℕ := [3506503681, 4077060099, 1141112836, 2282225672, 269484048, 808452144, 1077936192, 2155872384, 16777472, 50332416, 67109888, 134219776, 268439552, 805318656, 1073758208, 2147516416, 65536, 196608, 262144, 524288, 1048576, 3145728, 4194304, 8388608, 16777216, 50331648, 67108864, 134217728, 268435456, 805306368, 1073741824, 2147483648]

lemma hT : ∀ a < 32, ∀ b < 32, decide (R (dec a) (dec b)) = bit (Tm.getD a 0) b := by
  have h : (List.range 32).all (fun a => (List.range 32).all
      (fun b => decide (R (dec a) (dec b)) == bit (Tm.getD a 0) b)) = true := by decide +kernel
  intro a ha b hb
  have h1 := List.all_eq_true.1 h a (List.mem_range.2 ha)
  have h2 := List.all_eq_true.1 h1 b (List.mem_range.2 hb)
  exact beq_iff_eq.1 h2
def V0 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def V1 : List ℕ := [6, 10, 4, 4, 3, 6, 3, 3, 2, 4, 2, 2, 2, 4, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1]
def V2 : List ℕ := [11, 27, 7, 7, 5, 15, 5, 5, 3, 9, 3, 3, 3, 9, 3, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1]
def V3 : List ℕ := [16, 52, 10, 10, 7, 28, 7, 7, 4, 16, 4, 4, 4, 16, 4, 4, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1]

lemma hV0 : ∀ a < 32, w R 0 (dec a) = V0.getD a 0 := by
  have h : ∀ a < 32, V0.getD a 0 = 1 := by decide +kernel
  intro a ha
  rw [h a ha]
  rfl
lemma hV1 : ∀ a < 32, w R 1 (dec a) = V1.getD a 0 :=
  step_ok R dec 32 hsum Tm (by decide +kernel) hT V0 V1 (by decide +kernel) (by decide +kernel) 0 hV0
lemma hV2 : ∀ a < 32, w R 2 (dec a) = V2.getD a 0 :=
  step_ok R dec 32 hsum Tm (by decide +kernel) hT V1 V2 (by decide +kernel) (by decide +kernel) 1 hV1
lemma hV3 : ∀ a < 32, w R 3 (dec a) = V3.getD a 0 :=
  step_ok R dec 32 hsum Tm (by decide +kernel) hT V2 V3 (by decide +kernel) (by decide +kernel) 2 hV2
lemma tot1 : ∑ s, w R 1 s = 79 := by
  rw [tot_ok R dec 32 hsum V1 (by decide +kernel) 1 hV1]
  decide +kernel
lemma tot2 : ∑ s, w R 2 s = 142 := by
  rw [tot_ok R dec 32 hsum V2 (by decide +kernel) 2 hV2]
  decide +kernel
lemma tot3 : ∑ s, w R 3 s = 221 := by
  rw [tot_ok R dec 32 hsum V3 (by decide +kernel) 3 hV3]
  decide +kernel

/-- The coefficients of the recurrence. -/
def Lc : List ℤ := [-1, 3, -3, 1]

lemma base : ∀ s : St, comb R Lc 0 s = 0 := by
  have h : (List.range 32).all (fun a => decide ((-1 : ℤ) * ((V0.getD a 0 : ℕ) : ℤ) + (3 : ℤ) * ((V1.getD a 0 : ℕ) : ℤ) + (-3 : ℤ) * ((V2.getD a 0 : ℕ) : ℤ) + (1 : ℤ) * ((V3.getD a 0 : ℕ) : ℤ) = 0)) = true := by decide +kernel
  intro s
  obtain ⟨a, ha, rfl⟩ := dec_surj s
  have h1 := of_decide_eq_true (List.all_eq_true.1 h a (List.mem_range.2 ha))
  simp only [Lc, comb]
  rw [hV0 a ha, hV1 a ha, hV2 a ha, hV3 a ha]
  linarith

lemma rec_tot (n : ℕ) (hn : 0 ≤ n) : combA R Lc n = 0 := by
  rw [combA_eq]
  exact Finset.sum_eq_zero (fun s _ => comb_zero R Lc 0 base n hn s)

lemma good_iff (n : ℕ) (x : Fin 5 → Fin (n + 1) → Fin 2) :
    OMA.S_oeis_a250658.Good n x ↔ Ch R n (fun j i => x i j) := ⟨fun h j i => h i j, fun h i j => h j i⟩

lemma a_eq (n : ℕ) : OMA.S_oeis_a250658.a n = ∑ s, w R n s := by
  classical
  rw [← total]
  unfold OMA.S_oeis_a250658.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij' (fun x _ => fun j i => x i j) (fun f _ => fun i j => f j i) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact (good_iff n x).1 hx
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf ⊢
    exact (good_iff n _).2 hf
  · intro x _
    rfl
  · intro f _
    rfl

end OMA.A250658

theorem OMA.solution : type_of% @OMA.S_oeis_a250658.main := by
  have v1 : OMA.S_oeis_a250658.a 1 = 79 := by rw [OMA.A250658.a_eq, OMA.A250658.tot1]
  have v2 : OMA.S_oeis_a250658.a 2 = 142 := by rw [OMA.A250658.a_eq, OMA.A250658.tot2]
  have v3 : OMA.S_oeis_a250658.a 3 = 221 := by rw [OMA.A250658.a_eq, OMA.A250658.tot3]
  have hrec : ∀ n : ℕ, 1 ≤ n → (OMA.S_oeis_a250658.a (n + 3) : ℤ) = 3 * OMA.S_oeis_a250658.a (n + 2) - 3 * OMA.S_oeis_a250658.a (n + 1) + OMA.S_oeis_a250658.a n := by
    intro n hn
    have h := OMA.A250658.rec_tot n (by omega)
    simp only [OMA.A250658.Lc, OMA.A250658.combA] at h
    simp only [OMA.A250658.a_eq]
    linarith
  have key : ∀ n : ℕ, 1 ≤ n → (1 * (OMA.S_oeis_a250658.a n : ℤ) = 8 * (n : ℤ) ^ 2 + 39 * n + 32) ∧ (1 * (OMA.S_oeis_a250658.a (n + 1) : ℤ) = 8 * (((n + 1) : ℕ) : ℤ) ^ 2 + 39 * (((n + 1) : ℕ) : ℤ) + 32) ∧ (1 * (OMA.S_oeis_a250658.a (n + 2) : ℤ) = 8 * (((n + 2) : ℕ) : ℤ) ^ 2 + 39 * (((n + 2) : ℕ) : ℤ) + 32) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num [v1, v2, v3]
    | succ n hn ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      have hr := hrec n hn
      push_cast at h0 h1 h2 hr ⊢
      linear_combination (1) * hr + (3) * h2 + (-3) * h1 + (1) * h0
  exact ⟨v1, v2, v3, hrec, fun n hn => (key n hn).1⟩
