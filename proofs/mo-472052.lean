import OMAStatements.S_mo_472052
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Growth of binary strings avoiding a translated four-position pattern

Complete proof of `OMA.S_mo_472052.main`:
1. Word characterization of `continuations` and `count`.
2. Submultiplicativity and buffered supermultiplicativity (with buffer `max t s + s`).
3. Uniform lower bound `(7 / 4) ^ n ≤ count s t n` via residue-class decomposition and `010`-avoidance.
4. Strict upper bound `count s t (L + 1) < 2 ^ (L + 1)` via an explicit forbidden word.
5. Fekete's subadditive lemma yielding the growth constant `c ∈ [7/4, 2)` and tight power bounds.
6. Exact degree-7 polynomial and interval characterization for `s = 2, t = 3` via a 9-class
   positive eigenvector of the 32-state transfer matrix.
-/

namespace OMA.MO472052

open OMA.S_mo_472052 Filter Topology
open scoped Classical

section WordModel

/-- Recursive validity matching `continuations s t n h`. -/
def ValidRec (s t : ℕ) : (n : ℕ) → (ℕ → Bool) → (Fin n → Bool) → Prop
  | 0, _, _ => True
  | n + 1, h, w =>
      (w 0 = true ∨ allowZero s t h = true) ∧
      ValidRec s t n (push (w 0) h) (fun i => w i.succ)

lemma card_validRec (s t : ℕ) :
    ∀ (n : ℕ) (h : ℕ → Bool),
      ((Finset.univ : Finset (Fin n → Bool)).filter (ValidRec s t n h)).card =
        continuations s t n h
  | 0, h => by
      simp [ValidRec, continuations]
  | n + 1, h => by
      let S := (Finset.univ : Finset (Fin (n + 1) → Bool)).filter (ValidRec s t (n + 1) h)
      let S1 := S.filter (fun w => w 0 = true)
      let S0 := S.filter (fun w => w 0 = false)
      have hdisj : Disjoint S1 S0 := by
        rw [Finset.disjoint_left]
        intro w hw1 hw0
        have h1 : w 0 = true := (Finset.mem_filter.mp hw1).2
        have h0 : w 0 = false := (Finset.mem_filter.mp hw0).2
        rw [h1] at h0
        exact Bool.noConfusion h0
      have hunion : S1 ∪ S0 = S := by
        ext w
        simp only [S1, S0, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
        · intro hw
          cases w 0
          · exact Or.inr ⟨hw, rfl⟩
          · exact Or.inl ⟨hw, rfl⟩
      have hS1 : S1.card = continuations s t n (push true h) := by
        rw [← card_validRec s t n (push true h)]
        refine Finset.card_bij (fun w _ => fun i : Fin n => w i.succ) ?_ ?_ ?_
        · intro w hw
          have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
          have hw0 : w 0 = true := (Finset.mem_filter.mp hw).2
          have hrec := (Finset.mem_filter.mp hwS).2
          rw [ValidRec, hw0] at hrec
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrec.2⟩
        · intro w1 hw1 w2 hw2 heq
          have h1 : w1 0 = true := (Finset.mem_filter.mp hw1).2
          have h2 : w2 0 = true := (Finset.mem_filter.mp hw2).2
          funext i
          refine Fin.cases ?_ ?_ i
          · rw [h1, h2]
          · intro j; exact congrFun heq j
        · intro v hv
          have hvrec : ValidRec s t n (push true h) v := (Finset.mem_filter.mp hv).2
          refine ⟨Fin.cons true v, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
            refine ⟨Or.inl rfl, ?_⟩
            simpa [Fin.cons_zero, Fin.cons_succ] using hvrec
          · funext i; simp [Fin.cons_succ]
      have hS0 : S0.card = if allowZero s t h then continuations s t n (push false h) else 0 := by
        by_cases haz : allowZero s t h = true
        · rw [if_pos haz, ← card_validRec s t n (push false h)]
          refine Finset.card_bij (fun w _ => fun i : Fin n => w i.succ) ?_ ?_ ?_
          · intro w hw
            have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
            have hw0 : w 0 = false := (Finset.mem_filter.mp hw).2
            have hrec := (Finset.mem_filter.mp hwS).2
            rw [ValidRec, hw0] at hrec
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrec.2⟩
          · intro w1 hw1 w2 hw2 heq
            have h1 : w1 0 = false := (Finset.mem_filter.mp hw1).2
            have h2 : w2 0 = false := (Finset.mem_filter.mp hw2).2
            funext i
            refine Fin.cases ?_ ?_ i
            · rw [h1, h2]
            · intro j; exact congrFun heq j
          · intro v hv
            have hvrec : ValidRec s t n (push false h) v := (Finset.mem_filter.mp hv).2
            refine ⟨Fin.cons false v, ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
              refine ⟨Or.inr haz, ?_⟩
              simpa [Fin.cons_zero, Fin.cons_succ] using hvrec
            · funext i; simp [Fin.cons_succ]
        · rw [if_neg haz]
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro w hw
          have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
          have hw0 : w 0 = false := (Finset.mem_filter.mp hw).2
          have hrec := (Finset.mem_filter.mp hwS).2
          rw [ValidRec, hw0] at hrec
          rcases hrec.1 with htf | hallow
          · exact Bool.noConfusion htf
          · exact haz hallow
      change S.card = continuations s t (n + 1) h
      rw [← hunion, Finset.card_union_of_disjoint hdisj, hS1, hS0, continuations]

/-- Extended tape value at integer position `z`, with history `h` on negative positions. -/
def extVal (h : ℕ → Bool) {n : ℕ} (w : Fin n → Bool) (z : ℤ) : Bool :=
  if _h0 : 0 ≤ z then
    if hn : z.toNat < n then w ⟨z.toNat, hn⟩ else true
  else
    h (-z - 1).toNat

lemma extVal_shift (h : ℕ → Bool) {n : ℕ} (w : Fin (n + 1) → Bool) (z : ℤ) :
    extVal (push (w 0) h) (fun i => w i.succ) (z - 1) = extVal h w z := by
  unfold extVal
  by_cases hz1 : 1 ≤ z
  · have h0 : 0 ≤ z := by omega
    have h0' : 0 ≤ z - 1 := by omega
    rw [dif_pos h0', dif_pos h0]
    by_cases hn : (z - 1).toNat < n
    · have hn' : z.toNat < n + 1 := by omega
      rw [dif_pos hn, dif_pos hn']
      dsimp only
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    · have hn' : ¬ z.toNat < n + 1 := by omega
      rw [dif_neg hn, dif_neg hn']
  · by_cases hz0 : z = 0
    · subst hz0
      simp [push]
    · have h0 : ¬ (0 ≤ z) := by omega
      have h0' : ¬ (0 ≤ z - 1) := by omega
      rw [dif_neg h0', dif_neg h0]
      have hidx : (-(z - 1) - 1).toNat = (-z - 1).toNat + 1 := by omega
      rw [hidx, push]

lemma validRec_iff_extVal (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    ∀ (n : ℕ) (h : ℕ → Bool) (w : Fin n → Bool),
      ValidRec s t n h w ↔
        ∀ j : Fin n, w j = false →
          extVal h w ((j.val : ℤ) - (t + s)) = true ∨
          extVal h w ((j.val : ℤ) - (s + s)) = true ∨
          extVal h w ((j.val : ℤ) - s) = false
  | 0, _, _ => by simp [ValidRec]
  | n + 1, h, w => by
      rw [ValidRec, validRec_iff_extVal s t hs ht n (push (w 0) h) (fun i => w i.succ)]
      have h0_allow :
          allowZero s t h = true ↔
            extVal h w ((0 : ℤ) - (t + s)) = true ∨
            extVal h w ((0 : ℤ) - (s + s)) = true ∨
            extVal h w ((0 : ℤ) - s) = false := by
        unfold allowZero extVal
        have h1 : ¬ (0 ≤ (0 : ℤ) - (t + s)) := by omega
        have h2 : ¬ (0 ≤ (0 : ℤ) - (s + s)) := by omega
        have h3 : ¬ (0 ≤ (0 : ℤ) - s) := by omega
        rw [dif_neg h1, dif_neg h2, dif_neg h3]
        have i1 : (-((0 : ℤ) - (t + s)) - 1).toNat = t + s - 1 := by omega
        have i2 : (-((0 : ℤ) - (s + s)) - 1).toNat = s + s - 1 := by omega
        have i3 : (-((0 : ℤ) - s) - 1).toNat = s - 1 := by omega
        rw [i1, i2, i3]
        simp [Bool.or_eq_true, or_assoc]
      constructor
      · rintro ⟨hhead, htail⟩ j hj
        refine Fin.cases ?_ ?_ j hj
        · intro hj0
          rcases hhead with hw0 | haz
          · rw [hw0] at hj0; exact Bool.noConfusion hj0
          · exact h0_allow.mp haz
        · intro i hi
          have hi' := htail i hi
          have e1 := extVal_shift h w ((i.succ.val : ℤ) - (t + s))
          have e2 := extVal_shift h w ((i.succ.val : ℤ) - (s + s))
          have e3 := extVal_shift h w ((i.succ.val : ℤ) - s)
          have a1 : ((i.succ.val : ℤ) - (t + s)) - 1 = (i.val : ℤ) - (t + s) := by
            simp [Fin.val_succ]; ring
          have a2 : ((i.succ.val : ℤ) - (s + s)) - 1 = (i.val : ℤ) - (s + s) := by
            simp [Fin.val_succ]; ring
          have a3 : ((i.succ.val : ℤ) - s) - 1 = (i.val : ℤ) - s := by
            simp [Fin.val_succ]; ring
          rw [a1] at e1; rw [a2] at e2; rw [a3] at e3
          rw [← e1, ← e2, ← e3]
          exact hi'
      · intro hall
        constructor
        · cases hb : w 0
          · exact Or.inr (h0_allow.mpr (hall 0 hb))
          · exact Or.inl rfl
        · intro i hi
          have hi' := hall i.succ hi
          have e1 := extVal_shift h w ((i.succ.val : ℤ) - (t + s))
          have e2 := extVal_shift h w ((i.succ.val : ℤ) - (s + s))
          have e3 := extVal_shift h w ((i.succ.val : ℤ) - s)
          have a1 : ((i.succ.val : ℤ) - (t + s)) - 1 = (i.val : ℤ) - (t + s) := by
            simp [Fin.val_succ]; ring
          have a2 : ((i.succ.val : ℤ) - (s + s)) - 1 = (i.val : ℤ) - (s + s) := by
            simp [Fin.val_succ]; ring
          have a3 : ((i.succ.val : ℤ) - s) - 1 = (i.val : ℤ) - s := by
            simp [Fin.val_succ]; ring
          rw [a1] at e1; rw [a2] at e2; rw [a3] at e3
          rw [e1, e2, e3]
          exact hi'

/-- Position-wise validity for words starting from the all-true history. -/
def Valid (s t n : ℕ) (w : Fin n → Bool) : Prop :=
  ∀ j : Fin n, w j = false →
    ∀ (_h1 : t + s ≤ j.val) (_h2 : s + s ≤ j.val),
      w ⟨j.val - (t + s), by omega⟩ = true ∨
      w ⟨j.val - (s + s), by omega⟩ = true ∨
      w ⟨j.val - s, by omega⟩ = false

lemma validRec_allTrue_iff_valid (s t n : ℕ) (hs : 0 < s) (ht : 0 < t) (w : Fin n → Bool) :
    ValidRec s t n (fun _ => true) w ↔ Valid s t n w := by
  rw [validRec_iff_extVal s t hs ht n (fun _ => true) w]
  unfold Valid
  constructor
  · intro hall j hj h1 h2
    have hstep := hall j hj
    unfold extVal at hstep
    have z1 : 0 ≤ (j.val : ℤ) - (t + s) := by omega
    have z2 : 0 ≤ (j.val : ℤ) - (s + s) := by omega
    have z3 : 0 ≤ (j.val : ℤ) - s := by omega
    have n1 : ((j.val : ℤ) - (t + s)).toNat < n := by omega
    have n2 : ((j.val : ℤ) - (s + s)).toNat < n := by omega
    have n3 : ((j.val : ℤ) - s).toNat < n := by omega
    rw [dif_pos z1, dif_pos n1, dif_pos z2, dif_pos n2, dif_pos z3, dif_pos n3] at hstep
    have e1 : (⟨((j.val : ℤ) - (t + s)).toNat, n1⟩ : Fin n) = ⟨j.val - (t + s), by omega⟩ := by
      apply Fin.ext; dsimp; omega
    have e2 : (⟨((j.val : ℤ) - (s + s)).toNat, n2⟩ : Fin n) = ⟨j.val - (s + s), by omega⟩ := by
      apply Fin.ext; dsimp; omega
    have e3 : (⟨((j.val : ℤ) - s).toNat, n3⟩ : Fin n) = ⟨j.val - s, by omega⟩ := by
      apply Fin.ext; dsimp; omega
    rw [e1, e2, e3] at hstep
    exact hstep
  · intro hval j hj
    by_cases h1 : t + s ≤ j.val
    · by_cases h2 : s + s ≤ j.val
      · have hv := hval j hj h1 h2
        unfold extVal
        have z1 : 0 ≤ (j.val : ℤ) - (t + s) := by omega
        have z2 : 0 ≤ (j.val : ℤ) - (s + s) := by omega
        have z3 : 0 ≤ (j.val : ℤ) - s := by omega
        have n1 : ((j.val : ℤ) - (t + s)).toNat < n := by omega
        have n2 : ((j.val : ℤ) - (s + s)).toNat < n := by omega
        have n3 : ((j.val : ℤ) - s).toNat < n := by omega
        rw [dif_pos z1, dif_pos n1, dif_pos z2, dif_pos n2, dif_pos z3, dif_pos n3]
        have e1 : (⟨((j.val : ℤ) - (t + s)).toNat, n1⟩ : Fin n) = ⟨j.val - (t + s), by omega⟩ := by
          apply Fin.ext; dsimp; omega
        have e2 : (⟨((j.val : ℤ) - (s + s)).toNat, n2⟩ : Fin n) = ⟨j.val - (s + s), by omega⟩ := by
          apply Fin.ext; dsimp; omega
        have e3 : (⟨((j.val : ℤ) - s).toNat, n3⟩ : Fin n) = ⟨j.val - s, by omega⟩ := by
          apply Fin.ext; dsimp; omega
        rw [e1, e2, e3]
        exact hv
      · right
        left
        unfold extVal
        have z2 : ¬ (0 ≤ (j.val : ℤ) - (s + s)) := by omega
        rw [dif_neg z2]
    · left
      unfold extVal
      have z1 : ¬ (0 ≤ (j.val : ℤ) - (t + s)) := by omega
      rw [dif_neg z1]

lemma card_valid (s t n : ℕ) (hs : 0 < s) (ht : 0 < t) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => Valid s t n w)).card = count s t n := by
  rw [count, ← card_validRec s t n (fun _ => true)]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (validRec_allTrue_iff_valid s t n hs ht w).symm

end WordModel

section CombinatorialBounds

lemma count_submul (s t m n : ℕ) (hs : 0 < s) (ht : 0 < t) :
    count s t (m + n) ≤ count s t m * count s t n := by
  classical
  rw [← card_valid s t (m + n) hs ht, ← card_valid s t m hs ht, ← card_valid s t n hs ht,
    ← Finset.card_product]
  let f : (Fin (m + n) → Bool) → (Fin m → Bool) × (Fin n → Bool) :=
    fun w => (fun i => w ⟨i.val, by omega⟩, fun j => w ⟨m + j.val, by omega⟩)
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro w hw
    have hvw : Valid s t (m + n) w := (Finset.mem_filter.mp hw).2
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    · intro j hj h1 h2
      exact hvw ⟨j.val, by omega⟩ hj h1 h2
    · intro j hj h1 h2
      have hv := hvw ⟨m + j.val, by omega⟩ hj (by dsimp; omega) (by dsimp; omega)
      have e1 : (⟨m + j.val - (t + s), by omega⟩ : Fin (m + n)) = ⟨m + (j.val - (t + s)), by omega⟩ := by
        apply Fin.ext; dsimp; omega
      have e2 : (⟨m + j.val - (s + s), by omega⟩ : Fin (m + n)) = ⟨m + (j.val - (s + s)), by omega⟩ := by
        apply Fin.ext; dsimp; omega
      have e3 : (⟨m + j.val - s, by omega⟩ : Fin (m + n)) = ⟨m + (j.val - s), by omega⟩ := by
        apply Fin.ext; dsimp; omega
      rw [e1, e2, e3] at hv
      exact hv
  · intro w1 _ w2 _ heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    funext i
    by_cases hi : i.val < m
    · have := congrFun h1 ⟨i.val, hi⟩
      dsimp only [f] at this
      simpa using this
    · have := congrFun h2 ⟨i.val - m, by omega⟩
      dsimp only [f] at this
      have he : (⟨m + (i.val - m), by omega⟩ : Fin (m + n)) = i := by
        apply Fin.ext; dsimp; omega
      simpa [he] using this

lemma count_supermul (s t m n : ℕ) (hs : 0 < s) (ht : 0 < t) :
    count s t m * count s t n ≤ count s t (m + (max t s + s) + n) := by
  classical
  set L := max t s + s
  rw [← card_valid s t m hs ht, ← card_valid s t n hs ht, ← card_valid s t (m + L + n) hs ht,
    ← Finset.card_product]
  let g : (Fin m → Bool) × (Fin n → Bool) → (Fin (m + L + n) → Bool) :=
    fun uv i =>
      if h1 : i.val < m then uv.1 ⟨i.val, h1⟩
      else if h2 : m + L ≤ i.val then uv.2 ⟨i.val - (m + L), by omega⟩
      else true
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro uv huv
    have hu : Valid s t m uv.1 := (Finset.mem_filter.mp (Finset.mem_product.mp huv).1).2
    have hv : Valid s t n uv.2 := (Finset.mem_filter.mp (Finset.mem_product.mp huv).2).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro j hj h1 h2
    dsimp only [g] at hj ⊢
    by_cases hjm : j.val < m
    · rw [dif_pos hjm] at hj
      have a1 : j.val - (t + s) < m := by omega
      have a2 : j.val - (s + s) < m := by omega
      have a3 : j.val - s < m := by omega
      rw [dif_pos a1, dif_pos a2, dif_pos a3]
      exact hu ⟨j.val, hjm⟩ hj h1 h2
    · rw [dif_neg hjm] at hj
      by_cases hjL : m + L ≤ j.val
      · rw [dif_pos hjL] at hj
        have htsL : t + s ≤ L := by dsimp [L]; omega
        have hssL : s + s ≤ L := by dsimp [L]; omega
        have b1 : ¬ (j.val - (t + s) < m) := by omega
        have b2 : ¬ (j.val - (s + s) < m) := by omega
        have b3 : ¬ (j.val - s < m) := by omega
        rw [dif_neg b1, dif_neg b2, dif_neg b3]
        by_cases c1 : m + L ≤ j.val - (t + s)
        · by_cases c2 : m + L ≤ j.val - (s + s)
          · have c3 : m + L ≤ j.val - s := by omega
            rw [dif_pos c1, dif_pos c2, dif_pos c3]
            have hstep := hv ⟨j.val - (m + L), by omega⟩ hj (by dsimp; omega) (by dsimp; omega)
            have e1 : (⟨j.val - (t + s) - (m + L), by omega⟩ : Fin n) =
                ⟨j.val - (m + L) - (t + s), by omega⟩ := by apply Fin.ext; dsimp; omega
            have e2 : (⟨j.val - (s + s) - (m + L), by omega⟩ : Fin n) =
                ⟨j.val - (m + L) - (s + s), by omega⟩ := by apply Fin.ext; dsimp; omega
            have e3 : (⟨j.val - s - (m + L), by omega⟩ : Fin n) =
                ⟨j.val - (m + L) - s, by omega⟩ := by apply Fin.ext; dsimp; omega
            rw [e1, e2, e3]
            exact hstep
          · rw [dif_neg c2]; exact Or.inr (Or.inl rfl)
        · rw [dif_neg c1]; exact Or.inl rfl
      · rw [dif_neg hjL] at hj
        exact Bool.noConfusion hj
  · intro uv1 _ uv2 _ heq
    apply Prod.ext
    · funext i
      have h := congrFun heq ⟨i.val, by omega⟩
      dsimp only [g] at h
      rw [dif_pos i.isLt, dif_pos i.isLt] at h
      exact h
    · funext j
      have h := congrFun heq ⟨m + L + j.val, by omega⟩
      dsimp only [g] at h
      have h1 : ¬ (m + L + j.val < m) := by omega
      have h2 : m + L ≤ m + L + j.val := by omega
      rw [dif_neg h1, dif_pos h2, dif_neg h1, dif_pos h2] at h
      have he : (⟨m + L + j.val - (m + L), by omega⟩ : Fin n) = j := by
        apply Fin.ext; dsimp; omega
      simpa [he] using h

lemma count_lt_two_pow (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    count s t (max t s + s + 1) < 2 ^ (max t s + s + 1) := by
  classical
  set L := max t s + s
  rw [← card_valid s t (L + 1) hs ht]
  have hcard_univ : (Finset.univ : Finset (Fin (L + 1) → Bool)).card = 2 ^ (L + 1) := by
    simp
  rw [← hcard_univ]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  let bad : Fin (L + 1) → Bool := fun i =>
    decide (i.val ≠ L - (t + s) ∧ i.val ≠ L - (s + s) ∧ i.val ≠ L)
  have hmem : bad ∈ (Finset.univ : Finset (Fin (L + 1) → Bool)).filter (Valid s t (L + 1)) := by
    rw [heq]; exact Finset.mem_univ bad
  have hval : Valid s t (L + 1) bad := (Finset.mem_filter.mp hmem).2
  have htsL : t + s ≤ L := by dsimp [L]; omega
  have hssL : s + s ≤ L := by dsimp [L]; omega
  have hbadL : bad ⟨L, by omega⟩ = false := by simp [bad]
  have hstep := hval ⟨L, by omega⟩ hbadL htsL hssL
  rcases hstep with h1 | h2 | h3
  · simp [bad] at h1
  · simp [bad] at h2
  · have hn1 : L - s ≠ L - (t + s) := by omega
    have hn2 : L - s ≠ L - (s + s) := by omega
    have hn3 : L - s ≠ L := by omega
    have ht' : bad ⟨L - s, by omega⟩ = true := by
      simp [bad, hn1, hn2, hn3]
    rw [ht'] at h3
    exact Bool.noConfusion h3

/-- Lower bound for `010`-avoiding words (`continuations 1 1`). -/
lemma continuations_one_one_lower (m : ℕ) :
    (∀ h : ℕ → Bool, h 0 = true → h 1 = true →
      (7 / 4 : ℝ) ^ m ≤ (continuations 1 1 m h : ℝ)) ∧
    (∀ h : ℕ → Bool, h 0 = false →
      (37 / 49 : ℝ) * (7 / 4 : ℝ) ^ m ≤ (continuations 1 1 m h : ℝ)) ∧
    (∀ h : ℕ → Bool, h 0 = true → h 1 = false →
      (4 / 7 : ℝ) * (7 / 4 : ℝ) ^ m ≤ (continuations 1 1 m h : ℝ)) := by
  induction m with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp [continuations] <;> norm_num
  | succ m ih =>
      obtain ⟨ihA, ihB, ihC⟩ := ih
      have hp : (0 : ℝ) ≤ (7 / 4 : ℝ) ^ m := by positivity
      refine ⟨?_, ?_, ?_⟩
      · intro h h0 h1
        have haz : allowZero 1 1 h = true := by simp [allowZero, h1]
        rw [continuations, if_pos haz, Nat.cast_add]
        have h1' := ihA (push true h) rfl h0
        have h2' := ihB (push false h) rfl
        rw [pow_succ]
        nlinarith
      · intro h h0
        have haz : allowZero 1 1 h = true := by simp [allowZero, h0]
        rw [continuations, if_pos haz, Nat.cast_add]
        have h1' := ihC (push true h) rfl h0
        have h2' := ihB (push false h) rfl
        rw [pow_succ]
        nlinarith
      · intro h h0 h1
        have haz : allowZero 1 1 h = false := by simp [allowZero, h0, h1]
        rw [continuations, if_neg (by simp [haz]), add_zero]
        have h1' := ihA (push true h) rfl h0
        rw [pow_succ]
        nlinarith

lemma count_one_one_lower (m : ℕ) : (7 / 4 : ℝ) ^ m ≤ (count 1 1 m : ℝ) :=
  (continuations_one_one_lower m).1 (fun _ => true) rfl rfl

/-- Length of residue class `r` modulo `s` inside `Fin n`. -/
def sliceLen (n s : ℕ) (r : Fin s) : ℕ :=
  if r.val < n then (n - 1 - r.val) / s + 1 else 0

lemma sum_sliceLen (n s : ℕ) (hs : 0 < s) :
    ∑ r : Fin s, sliceLen n s r = n := by
  have hbij :
      (Finset.univ : Finset (Fin n)).card =
        ∑ r : Fin s, ((Finset.univ : Finset (Fin n)).filter (fun i => i.val % s = r.val)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext i
      simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
      exact ⟨⟨i.val % s, Nat.mod_lt i.val hs⟩, rfl⟩
    · intro r1 _ r2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      have e1 : i.val % s = r1.val := (Finset.mem_filter.mp hi1).2
      have e2 : i.val % s = r2.val := (Finset.mem_filter.mp hi2).2
      exact hne (Fin.ext (e1.symm.trans e2))
  rw [Finset.card_fin] at hbij
  trans ∑ r : Fin s, ((Finset.univ : Finset (Fin n)).filter (fun i => i.val % s = r.val)).card
  swap
  · exact hbij.symm
  refine Finset.sum_congr rfl fun r _ => ?_
  symm
  rw [← Finset.card_fin (sliceLen n s r)]
  refine Finset.card_bij (fun i hi => ⟨i.val / s, ?_⟩) ?_ ?_ ?_
  · have hm : i.val % s = r.val := (Finset.mem_filter.mp hi).2
    have hr : r.val < n := hm ▸ lt_of_le_of_lt (Nat.mod_le i.val s) i.isLt
    dsimp [sliceLen]
    rw [if_pos hr]
    have hdiv := Nat.div_add_mod i.val s
    have hilt := i.isLt
    have hle : s * (i.val / s) ≤ n - 1 - r.val := by omega
    have hq : i.val / s ≤ (n - 1 - r.val) / s :=
      (Nat.le_div_iff_mul_le hs).mpr (by rw [Nat.mul_comm]; exact hle)
    omega
  · intro _ _; exact Finset.mem_univ _
  · intro i1 hi1 i2 hi2 heq
    have hm1 : i1.val % s = r.val := (Finset.mem_filter.mp hi1).2
    have hm2 : i2.val % s = r.val := (Finset.mem_filter.mp hi2).2
    have hd : i1.val / s = i2.val / s := congrArg Fin.val heq
    apply Fin.ext
    rw [← Nat.div_add_mod i1.val s, ← Nat.div_add_mod i2.val s, hd, hm1, hm2]
  · intro q _
    have hr : r.val < n := by
      by_contra hnr
      have h0 : sliceLen n s r = 0 := by simp [sliceLen, hnr]
      exact Nat.not_lt_zero q.val (h0 ▸ q.isLt)
    have hqlt : q.val ≤ (n - 1 - r.val) / s := by
      have hlt := q.isLt
      simp only [sliceLen, if_pos hr] at hlt
      omega
    have hmul : q.val * s ≤ n - 1 - r.val := (Nat.le_div_iff_mul_le hs).mp hqlt
    have hlt : q.val * s + r.val < n := by omega
    refine ⟨⟨q.val * s + r.val, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · dsimp
      rw [Nat.mul_add_mod_of_lt r.isLt]
    · apply Fin.ext
      dsimp
      rw [Nat.mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt r.isLt, add_zero]

lemma count_lower (s t n : ℕ) (hs : 0 < s) (ht : 0 < t) :
    (7 / 4 : ℝ) ^ n ≤ (count s t n : ℝ) := by
  classical
  have hprod : (∏ r : Fin s, count 1 1 (sliceLen n s r)) ≤ count s t n := by
    rw [← card_valid s t n hs ht]
    have hcards :
        (∏ r : Fin s, count 1 1 (sliceLen n s r)) =
          (Fintype.piFinset fun r : Fin s =>
            (Finset.univ : Finset (Fin (sliceLen n s r) → Bool)).filter
              (Valid 1 1 (sliceLen n s r))).card := by
      rw [Fintype.card_piFinset]
      refine Finset.prod_congr rfl fun r _ => ?_
      exact (card_valid 1 1 (sliceLen n s r) Nat.one_pos Nat.one_pos).symm
    rw [hcards]
    let merge : (∀ r : Fin s, Fin (sliceLen n s r) → Bool) → (Fin n → Bool) :=
      fun f i =>
        let r : Fin s := ⟨i.val % s, Nat.mod_lt i.val hs⟩
        have hr : r.val < n := lt_of_le_of_lt (Nat.mod_le i.val s) i.isLt
        have hq : i.val / s < sliceLen n s r := by
          dsimp [sliceLen, r]
          rw [if_pos hr]
          have hdiv := Nat.div_add_mod i.val s
          have hilt := i.isLt
          have hle : (i.val / s) * s ≤ n - 1 - i.val % s := by
            rw [Nat.mul_comm]; omega
          have := (Nat.le_div_iff_mul_le hs).mpr hle
          omega
        f r ⟨i.val / s, hq⟩
    have hmerge_apply :
        ∀ (f : ∀ r : Fin s, Fin (sliceLen n s r) → Bool)
          (i : Fin n) (r : Fin s) (q : Fin (sliceLen n s r)),
          i.val % s = r.val → i.val / s = q.val → merge f i = f r q := by
      intro f i r q hmod hdiv
      dsimp only [merge]
      have hr : (⟨i.val % s, Nat.mod_lt i.val hs⟩ : Fin s) = r := Fin.ext hmod
      subst hr
      congr 1
      exact Fin.ext hdiv
    refine Finset.card_le_card_of_injOn merge ?_ ?_
    · intro f hf
      have hf_val : ∀ r : Fin s, Valid 1 1 (sliceLen n s r) (f r) := fun r =>
        (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hf r)).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro j hj _ h2
      let r : Fin s := ⟨j.val % s, Nat.mod_lt j.val hs⟩
      have hr : r.val < n := lt_of_le_of_lt (Nat.mod_le j.val s) j.isLt
      have hqge : 2 ≤ j.val / s := by
        have hle : 2 * s ≤ j.val := by omega
        exact (Nat.le_div_iff_mul_le hs).mpr hle
      have hqlt : j.val / s < sliceLen n s r := by
        dsimp [sliceLen, r]
        rw [if_pos hr]
        have hdiv := Nat.div_add_mod j.val s
        have hjlt := j.isLt
        have hle : (j.val / s) * s ≤ n - 1 - j.val % s := by
          rw [Nat.mul_comm]; omega
        have := (Nat.le_div_iff_mul_le hs).mpr hle
        omega
      have hstep := hf_val r ⟨j.val / s, hqlt⟩ hj hqge hqge
      right
      have hmod1 : (j.val - (s + s)) % s = r.val := by
        have : j.val = (j.val - (s + s)) + 2 * s := by omega
        dsimp [r]
        conv_rhs => rw [this, Nat.add_mul_mod_self_right]
      have hdiv1 : (j.val - (s + s)) / s = j.val / s - 2 := by
        have h := Nat.add_mul_div_left (j.val - (s + s)) 2 hs
        have he : (j.val - (s + s)) + s * 2 = j.val := by omega
        rw [he] at h
        rw [h, Nat.add_sub_cancel]
      have hmod2 : (j.val - s) % s = r.val := by
        have : j.val = (j.val - s) + 1 * s := by omega
        dsimp [r]
        conv_rhs => rw [this, Nat.add_mul_mod_self_right]
      have hdiv2 : (j.val - s) / s = j.val / s - 1 := by
        have h := Nat.add_mul_div_left (j.val - s) 1 hs
        have he : (j.val - s) + s * 1 = j.val := by omega
        rw [he] at h
        rw [h, Nat.add_sub_cancel]
      have heq1 : merge f ⟨j.val - (s + s), by omega⟩ = f r ⟨j.val / s - 2, by omega⟩ :=
        hmerge_apply f ⟨j.val - (s + s), by omega⟩ r ⟨j.val / s - 2, by omega⟩ hmod1 hdiv1
      have heq2 : merge f ⟨j.val - s, by omega⟩ = f r ⟨j.val / s - 1, by omega⟩ :=
        hmerge_apply f ⟨j.val - s, by omega⟩ r ⟨j.val / s - 1, by omega⟩ hmod2 hdiv2
      rw [heq1, heq2]
      rcases hstep with hA | hB | hC
      · exact Or.inl hA
      · exact Or.inl hB
      · exact Or.inr hC
    · intro f1 _ f2 _ heq
      funext r q
      have hr : r.val < n := by
        by_contra hnr
        have h0 : sliceLen n s r = 0 := by simp [sliceLen, hnr]
        exact Nat.not_lt_zero q.val (h0 ▸ q.isLt)
      have hqle : q.val ≤ (n - 1 - r.val) / s := by
        have hlt := q.isLt
        simp only [sliceLen, if_pos hr] at hlt
        omega
      have hmul : q.val * s ≤ n - 1 - r.val := (Nat.le_div_iff_mul_le hs).mp hqle
      have hlt : q.val * s + r.val < n := by omega
      have hmod : (q.val * s + r.val) % s = r.val := Nat.mul_add_mod_of_lt r.isLt
      have hdiv : (q.val * s + r.val) / s = q.val := by
        rw [Nat.mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt r.isLt, add_zero]
      have hm := congrFun heq ⟨q.val * s + r.val, hlt⟩
      rw [hmerge_apply f1 ⟨q.val * s + r.val, hlt⟩ r q hmod hdiv,
        hmerge_apply f2 ⟨q.val * s + r.val, hlt⟩ r q hmod hdiv] at hm
      exact hm
  have hprod_real : (∏ r : Fin s, (count 1 1 (sliceLen n s r) : ℝ)) ≤ (count s t n : ℝ) := by
    exact_mod_cast hprod
  calc
    (7 / 4 : ℝ) ^ n = (7 / 4 : ℝ) ^ (∑ r : Fin s, sliceLen n s r) := by rw [sum_sliceLen n s hs]
    _ = ∏ r : Fin s, (7 / 4 : ℝ) ^ (sliceLen n s r) := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ r : Fin s, (count 1 1 (sliceLen n s r) : ℝ) := by
        refine Finset.prod_le_prod (fun r _ => by positivity) (fun r _ => count_one_one_lower _)
    _ ≤ (count s t n : ℝ) := hprod_real

end CombinatorialBounds

section FeketeGrowth

lemma count_pos (s t n : ℕ) (hs : 0 < s) (ht : 0 < t) : (0 : ℝ) < (count s t n : ℝ) :=
  lt_of_lt_of_le (by positivity : (0 : ℝ) < (7 / 4 : ℝ) ^ n) (count_lower s t n hs ht)

lemma log_count_subadditive (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    Subadditive (fun n => Real.log (count s t n : ℝ)) := by
  intro m n
  have hpos_m := count_pos s t m hs ht
  have hpos_n := count_pos s t n hs ht
  have hpos_mn := count_pos s t (m + n) hs ht
  have hmul : (count s t (m + n) : ℝ) ≤ (count s t m : ℝ) * (count s t n : ℝ) := by
    exact_mod_cast count_submul s t m n hs ht
  calc
    Real.log (count s t (m + n) : ℝ) ≤ Real.log ((count s t m : ℝ) * (count s t n : ℝ)) :=
      Real.log_le_log hpos_mn hmul
    _ = Real.log (count s t m : ℝ) + Real.log (count s t n : ℝ) :=
      Real.log_mul hpos_m.ne' hpos_n.ne'

lemma log_count_div_bddBelow (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    BddBelow (Set.range fun n : ℕ => Real.log (count s t n : ℝ) / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  have h1 : (1 : ℝ) ≤ (count s t n : ℝ) := by
    have hlow := count_lower s t n hs ht
    have hpow : (1 : ℝ) ≤ (7 / 4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    exact hpow.trans hlow
  exact div_nonneg (Real.log_nonneg h1) (Nat.cast_nonneg n)

lemma count_pow_le_buffered (s t n k : ℕ) (hs : 0 < s) (ht : 0 < t) :
    (count s t n) ^ k ≤ count s t (k * (n + (max t s + s))) := by
  set L := max t s + s
  induction k with
  | zero =>
      simp [count, continuations]
  | succ k ih =>
      have h1 := count_supermul s t (k * (n + L)) n hs ht
      have h2 : count s t (k * (n + L) + L + n) = count s t ((k + 1) * (n + L)) := by
        congr 1; ring
      rw [h2] at h1
      calc
        (count s t n) ^ (k + 1) = (count s t n) ^ k * count s t n := by rw [pow_succ]
        _ ≤ count s t (k * (n + L)) * count s t n := Nat.mul_le_mul_right _ ih
        _ ≤ count s t ((k + 1) * (n + L)) := h1

lemma exists_growth_rate (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    let hf := log_count_subadditive s t hs ht
    let c := Real.exp hf.lim
    7 / 4 ≤ c ∧ c < 2 ∧
      (∀ n : ℕ, c ^ n ≤ (count s t n : ℝ) ∧ (count s t n : ℝ) ≤ c ^ (n + max t s + s)) := by
  intro hf c
  have hbdd := log_count_div_bddBelow s t hs ht
  have htend := hf.tendsto_lim hbdd
  have hc_pos : 0 < c := Real.exp_pos hf.lim
  have hlow_lim : Real.log (7 / 4 : ℝ) ≤ hf.lim := by
    apply ge_of_tendsto htend
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 := count_lower s t n hs ht
    have hlog := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ hn_pos).mpr (by linarith)
  have h74 : (7 / 4 : ℝ) ≤ c := by
    calc
      (7 / 4 : ℝ) = Real.exp (Real.log (7 / 4 : ℝ)) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp hf.lim := Real.exp_le_exp.mpr hlow_lim
  have hcn_le : ∀ n : ℕ, c ^ n ≤ (count s t n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp [count, continuations]
    · have hdiv := hf.lim_le_div hbdd hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hmul : (n : ℝ) * hf.lim ≤ Real.log (count s t n : ℝ) := by
        have := (le_div_iff₀ hn_pos).mp hdiv
        linarith
      calc
        c ^ n = Real.exp ((n : ℝ) * hf.lim) := by
          rw [← Real.exp_nat_mul]
        _ ≤ Real.exp (Real.log (count s t n : ℝ)) := Real.exp_le_exp.mpr hmul
        _ = (count s t n : ℝ) := Real.exp_log (count_pos s t n hs ht)
  have hc_lt2 : c < 2 := by
    set L := max t s + s
    have h1 : c ^ (L + 1) ≤ (count s t (L + 1) : ℝ) := hcn_le (L + 1)
    have h2 : (count s t (L + 1) : ℝ) < (2 : ℝ) ^ (L + 1) := by
      exact_mod_cast count_lt_two_pow s t hs ht
    have hlt : c ^ (L + 1) < (2 : ℝ) ^ (L + 1) := lt_of_le_of_lt h1 h2
    by_contra hge
    push Not at hge
    have hpow : (2 : ℝ) ^ (L + 1) ≤ c ^ (L + 1) := pow_le_pow_left₀ (by norm_num) hge (L + 1)
    linarith
  have hle_cnL : ∀ n : ℕ, (count s t n : ℝ) ≤ c ^ (n + max t s + s) := by
    intro n
    set L := max t s + s
    have hstep_pos : 0 < n + L := by dsimp [L]; omega
    have hstep_rpos : (0 : ℝ) < ((n + L : ℕ) : ℝ) := by exact_mod_cast hstep_pos
    have hsub_tend :
        Tendsto (fun k : ℕ => Real.log (count s t (k * (n + L)) : ℝ) / ((k * (n + L) : ℕ) : ℝ))
          atTop (𝓝 hf.lim) := by
      have hmul_tend : Tendsto (fun k : ℕ => k * (n + L)) atTop atTop :=
        tendsto_atTop_atTop.mpr fun b =>
          ⟨b, fun k hk => le_trans hk (Nat.le_mul_of_pos_right k hstep_pos)⟩
      exact htend.comp hmul_tend
    have hlog_le : Real.log (count s t n : ℝ) / ((n + L : ℕ) : ℝ) ≤ hf.lim := by
      apply ge_of_tendsto hsub_tend
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hpow : (count s t n : ℝ) ^ k ≤ (count s t (k * (n + L)) : ℝ) := by
        exact_mod_cast count_pow_le_buffered s t n k hs ht
      have hlog := Real.log_le_log (pow_pos (count_pos s t n hs ht) k) hpow
      rw [Real.log_pow] at hlog
      rw [Nat.cast_mul, div_le_div_iff₀ hstep_rpos (mul_pos hk_pos hstep_rpos)]
      nlinarith
    have hmul : Real.log (count s t n : ℝ) ≤ ((n + L : ℕ) : ℝ) * hf.lim := by
      have := (div_le_iff₀ hstep_rpos).mp hlog_le
      linarith
    have hadd : n + max t s + s = n + L := by dsimp [L]; omega
    rw [hadd]
    calc
      (count s t n : ℝ) = Real.exp (Real.log (count s t n : ℝ)) :=
        (Real.exp_log (count_pos s t n hs ht)).symm
      _ ≤ Real.exp (((n + L : ℕ) : ℝ) * hf.lim) := Real.exp_le_exp.mpr hmul
      _ = c ^ (n + L) := by rw [← Real.exp_nat_mul]
  exact ⟨h74, hc_lt2, fun n => ⟨hcn_le n, hle_cnL n⟩⟩

end FeketeGrowth

section CaseTwoThree

/-- The characteristic polynomial for `s = 2, t = 3`. -/
def poly23 (x : ℝ) : ℝ :=
  x ^ 7 - 2 * x ^ 6 + 2 * x ^ 3 - x ^ 2 - 3 * x + 1

lemma exists_root_poly23 :
    ∃ lam : ℝ, 1884337 / 1000000 < lam ∧ lam < 1884338 / 1000000 ∧ poly23 lam = 0 := by
  let a : ℝ := 1884337 / 1000000
  let b : ℝ := 1884338 / 1000000
  have hab : a ≤ b := by norm_num [a, b]
  have ha : poly23 a < 0 := by norm_num [poly23, a]
  have hb : 0 < poly23 b := by norm_num [poly23, b]
  have hcont : ContinuousOn poly23 (Set.Icc a b) := by
    unfold poly23
    fun_prop
  have h0mem : (0 : ℝ) ∈ Set.Icc (poly23 a) (poly23 b) := ⟨ha.le, hb.le⟩
  obtain ⟨lam, ⟨hla, hlb⟩, hroot⟩ := intermediate_value_Icc hab hcont h0mem
  have hne_a : lam ≠ a := fun h => by rw [h] at hroot; linarith
  have hne_b : lam ≠ b := fun h => by rw [h] at hroot; linarith
  exact ⟨lam, lt_of_le_of_ne hla hne_a.symm, lt_of_le_of_ne hlb hne_b, hroot⟩

/-- Minimized 9-class state map from the 5 most recent bits `(h 0, h 1, h 2, h 3, h 4)`. -/
def stateCls (b0 b1 b2 b3 b4 : Bool) : Fin 9 :=
  match b0, b1, b2, b3, b4 with
  | false, false, false, false, false => 0
  | true,  false, false, false, false => 1
  | false, true,  false, false, false => 2
  | true,  true,  false, false, false => 3
  | false, false, true,  false, false => 4
  | true,  false, true,  false, false => 5
  | false, true,  true,  false, false => 2
  | true,  true,  true,  false, false => 2
  | false, false, false, true,  false => 0
  | true,  false, false, true,  false => 6
  | false, true,  false, true,  false => 7
  | true,  true,  false, true,  false => 5
  | false, false, true,  true,  false => 4
  | true,  false, true,  true,  false => 5
  | false, true,  true,  true,  false => 7
  | true,  true,  true,  true,  false => 5
  | false, false, false, false, true  => 0
  | true,  false, false, false, true  => 1
  | false, true,  false, false, true  => 7
  | true,  true,  false, false, true  => 8
  | false, false, true,  false, true  => 4
  | true,  false, true,  false, true  => 5
  | false, true,  true,  false, true  => 7
  | true,  true,  true,  false, true  => 5
  | false, false, false, true,  true  => 0
  | true,  false, false, true,  true  => 6
  | false, true,  false, true,  true  => 7
  | true,  true,  false, true,  true  => 5
  | false, false, true,  true,  true  => 4
  | true,  false, true,  true,  true  => 5
  | false, true,  true,  true,  true  => 7
  | true,  true,  true,  true,  true  => 5

/-- Explicit positive eigenvector in `ℤ[lam]` for the 9 minimized states. -/
def eigVal (lam : ℝ) : Fin 9 → ℝ
  | 0 => lam + 1
  | 1 => lam ^ 2 - 1
  | 2 => lam ^ 2 * (lam - 1)
  | 3 => lam * (lam - 1)
  | 4 => lam ^ 3 * (lam - 1) * (lam ^ 2 - lam - 1)
  | 5 => lam ^ 3 * (lam - 1)
  | 6 => 2 * (lam - 1) + lam ^ 2 * (lam - 1) ^ 2
  | 7 => lam ^ 3 * (lam - 1) ^ 2
  | 8 => 2 * lam * (lam - 1)

def histCls (h : ℕ → Bool) : Fin 9 :=
  stateCls (h 0) (h 1) (h 2) (h 3) (h 4)

lemma eigVal_bounds {lam : ℝ} (hlo : 1884337 / 1000000 < lam) (hhi : lam < 1884338 / 1000000)
    (i : Fin 9) : 1 ≤ eigVal lam i ∧ eigVal lam i ≤ 10 := by
  have h1 : (9 / 5 : ℝ) < lam := by linarith
  have h2 : lam < (19 / 10 : ℝ) := by linarith
  have hsq1 : (324 / 100 : ℝ) < lam ^ 2 := by nlinarith
  have hsq2 : lam ^ 2 < (361 / 100 : ℝ) := by nlinarith
  have hcu1 : (58 / 10 : ℝ) < lam ^ 3 := by nlinarith
  have hcu2 : lam ^ 3 < (7 : ℝ) := by nlinarith
  have hq1 : (4 / 10 : ℝ) < lam ^ 2 - lam - 1 := by nlinarith
  have hq2 : lam ^ 2 - lam - 1 < (8 / 10 : ℝ) := by nlinarith
  have hprod1 : (46 / 10 : ℝ) < lam ^ 3 * (lam - 1) := by nlinarith
  have hprod2 : lam ^ 3 * (lam - 1) < (64 / 10 : ℝ) := by nlinarith
  fin_cases i <;> simp only [eigVal] <;> constructor <;>
    nlinarith [sq_nonneg lam, sq_nonneg (lam - 1)]

lemma eig_step {lam : ℝ} (hroot : poly23 lam = 0) (h : ℕ → Bool) :
    eigVal lam (histCls (push true h)) +
      (if allowZero 2 3 h then eigVal lam (histCls (push false h)) else 0) =
      lam * eigVal lam (histCls h) := by
  unfold poly23 at hroot
  unfold histCls allowZero
  simp only [push]
  cases h 0 <;> cases h 1 <;> cases h 2 <;> cases h 3 <;> cases h 4 <;>
    simp only [stateCls, eigVal, Bool.or_false, Bool.or_true,
      Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true] <;>
    (ring_nf; try linarith [hroot])

lemma continuations_23_sandwich {lam : ℝ}
    (hlo : 1884337 / 1000000 < lam) (hhi : lam < 1884338 / 1000000) (hroot : poly23 lam = 0) :
    ∀ (n : ℕ) (h : ℕ → Bool),
      (1 / 10 : ℝ) * eigVal lam (histCls h) * lam ^ n ≤ (continuations 2 3 n h : ℝ) ∧
      (continuations 2 3 n h : ℝ) ≤ eigVal lam (histCls h) * lam ^ n
  | 0, h => by
      have hb := eigVal_bounds hlo hhi (histCls h)
      simp only [continuations, Nat.cast_one, pow_zero, mul_one]
      constructor <;> linarith
  | n + 1, h => by
      have ih1 := continuations_23_sandwich hlo hhi hroot n (push true h)
      have ih0 := continuations_23_sandwich hlo hhi hroot n (push false h)
      have hstep := eig_step hroot h
      rw [continuations, Nat.cast_add]
      by_cases haz : allowZero 2 3 h = true
      · rw [if_pos haz] at hstep ⊢
        constructor
        · calc
            (1 / 10 : ℝ) * eigVal lam (histCls h) * lam ^ (n + 1) =
                (1 / 10 : ℝ) * (lam * eigVal lam (histCls h)) * lam ^ n := by rw [pow_succ]; ring
            _ = (1 / 10 : ℝ) * eigVal lam (histCls (push true h)) * lam ^ n +
                  (1 / 10 : ℝ) * eigVal lam (histCls (push false h)) * lam ^ n := by
                  rw [← hstep]; ring
            _ ≤ (continuations 2 3 n (push true h) : ℝ) +
                  (continuations 2 3 n (push false h) : ℝ) := add_le_add ih1.1 ih0.1
        · calc
            (continuations 2 3 n (push true h) : ℝ) +
                (continuations 2 3 n (push false h) : ℝ) ≤
                eigVal lam (histCls (push true h)) * lam ^ n +
                  eigVal lam (histCls (push false h)) * lam ^ n := add_le_add ih1.2 ih0.2
            _ = (lam * eigVal lam (histCls h)) * lam ^ n := by rw [← add_mul, hstep]
            _ = eigVal lam (histCls h) * lam ^ (n + 1) := by rw [pow_succ]; ring
      · rw [if_neg haz] at hstep ⊢
        simp only [Nat.cast_zero, add_zero] at hstep ⊢
        constructor
        · calc
            (1 / 10 : ℝ) * eigVal lam (histCls h) * lam ^ (n + 1) =
                (1 / 10 : ℝ) * (lam * eigVal lam (histCls h)) * lam ^ n := by rw [pow_succ]; ring
            _ = (1 / 10 : ℝ) * eigVal lam (histCls (push true h)) * lam ^ n := by rw [← hstep]
            _ ≤ (continuations 2 3 n (push true h) : ℝ) := ih1.1
        · calc
            (continuations 2 3 n (push true h) : ℝ) ≤
                eigVal lam (histCls (push true h)) * lam ^ n := ih1.2
            _ = (lam * eigVal lam (histCls h)) * lam ^ n := by rw [hstep]
            _ = eigVal lam (histCls h) * lam ^ (n + 1) := by rw [pow_succ]; ring

lemma growth_rate_eq_root_23 :
    let hf := log_count_subadditive 2 3 (by decide) (by decide)
    let c := Real.exp hf.lim
    1884337 / 1000000 < c ∧ c < 1884338 / 1000000 ∧
      c ^ 7 - 2 * c ^ 6 + 2 * c ^ 3 - c ^ 2 - 3 * c + 1 = 0 := by
  intro hf c
  obtain ⟨lam, hlo, hhi, hroot⟩ := exists_root_poly23
  have hlam_pos : 0 < lam := by linarith
  have hbdd := log_count_div_bddBelow 2 3 (by decide) (by decide)
  have htend := hf.tendsto_lim hbdd
  have hbounds : ∀ n : ℕ,
      (1 / 10 : ℝ) * lam ^ n ≤ (count 2 3 n : ℝ) ∧ (count 2 3 n : ℝ) ≤ 10 * lam ^ n := by
    intro n
    have hs := continuations_23_sandwich hlo hhi hroot n (fun _ => true)
    have hb := eigVal_bounds hlo hhi (histCls (fun _ => true))
    have hpow : 0 ≤ lam ^ n := pow_nonneg hlam_pos.le n
    change (1 / 10 : ℝ) * lam ^ n ≤ (continuations 2 3 n (fun _ => true) : ℝ) ∧
      (continuations 2 3 n (fun _ => true) : ℝ) ≤ 10 * lam ^ n
    constructor <;> nlinarith
  have hlog_tend :
      Tendsto (fun n : ℕ => Real.log (count 2 3 n : ℝ) / (n : ℝ)) atTop (𝓝 (Real.log lam)) := by
    have ht1 : Tendsto (fun n : ℕ => Real.log (1 / 10 : ℝ) / (n : ℝ) + Real.log lam)
        atTop (𝓝 (0 + Real.log lam)) :=
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log (1 / 10 : ℝ))).add tendsto_const_nhds
    have ht2 : Tendsto (fun n : ℕ => Real.log (10 : ℝ) / (n : ℝ) + Real.log lam)
        atTop (𝓝 (0 + Real.log lam)) :=
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log (10 : ℝ))).add tendsto_const_nhds
    rw [zero_add] at ht1 ht2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ht1 ht2 ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h1 := (hbounds n).1
      have hlog := Real.log_le_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (pow_pos hlam_pos n).ne', Real.log_pow] at hlog
      have hdiv := div_le_div_of_nonneg_right hlog hn_pos.le
      rw [add_div, mul_div_cancel_left₀ _ hn_pos.ne'] at hdiv
      exact hdiv
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h2 := (hbounds n).2
      have hlog := Real.log_le_log (count_pos 2 3 n (by decide) (by decide)) h2
      rw [Real.log_mul (by norm_num) (pow_pos hlam_pos n).ne', Real.log_pow] at hlog
      have hdiv := div_le_div_of_nonneg_right hlog hn_pos.le
      rw [add_div, mul_div_cancel_left₀ _ hn_pos.ne'] at hdiv
      exact hdiv
  have hlim_eq : hf.lim = Real.log lam := tendsto_nhds_unique htend hlog_tend
  have hc_eq : c = lam := by
    dsimp [c]
    rw [hlim_eq, Real.exp_log hlam_pos]
  rw [hc_eq]
  exact ⟨hlo, hhi, hroot⟩

end CaseTwoThree

end OMA.MO472052

theorem OMA.solution : type_of% @OMA.S_mo_472052.main := by
  intro s t hs ht
  let hf := OMA.MO472052.log_count_subadditive s t hs ht
  refine ⟨Real.exp hf.lim, ?_⟩
  obtain ⟨h74, hlt2, hpow⟩ := OMA.MO472052.exists_growth_rate s t hs ht
  refine ⟨h74, hlt2, hpow, ?_⟩
  rintro rfl rfl
  exact OMA.MO472052.growth_rate_eq_root_23
