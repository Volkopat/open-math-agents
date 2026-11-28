import OMAStatements.S_oeis_a209861
import Mathlib

/-! Rank reversal for binary tree codes. The leading ones record Hamming weight.
At fixed weight, the remaining blocks compare in reverse input order. -/

namespace RowReflection
open OMA.S_oeis_a209861

def blocks : List Bool → List Bool
  | [] => []
  | true :: s => false :: blocks s
  | false :: s => false :: true :: blocks s

theorem fold_code (w s : List Bool) :
    w.foldl putBit s = List.replicate (w.count true) true ++ s ++ blocks w := by
  induction w generalizing s with
  | nil => simp [blocks]
  | cons b w ih =>
    cases b <;> simp [List.foldl, ih, putBit, blocks, List.replicate_succ', List.append_assoc]

def suffix (w : List Bool) := blocks w ++ [false]

theorem suffix_head (w : List Bool) : ∃ s, suffix w = false :: s := by
  cases w with
  | nil => exact ⟨[], rfl⟩
  | cons b w => cases b <;> exact ⟨_, rfl⟩

theorem blocks_order (u v : List Bool) (h : u.length = v.length) :
    suffix u < suffix v ↔ v < u := by
  induction u generalizing v with
  | nil => have : v = [] := List.length_eq_zero_iff.mp h.symm; subst v; simp
  | cons b u ih =>
    cases v with
    | nil => simp at h
    | cons c v =>
      have he := ih v (by simpa using h)
      obtain ⟨s, hs⟩ := suffix_head u
      obtain ⟨t, ht⟩ := suffix_head v
      have htrue (w : List Bool) : suffix (true :: w) = false :: suffix w := rfl
      have hfalse (w : List Bool) : suffix (false :: w) = false :: true :: suffix w := rfl
      cases b <;> cases c <;>
        simp [htrue, hfalse, List.cons_lt_cons_iff, hs, ht] at he ⊢ <;> tauto

theorem prefix_order (i j : ℕ) (s t : List Bool) :
    List.replicate i true ++ false :: s < List.replicate j true ++ false :: t ↔
      i < j ∨ i = j ∧ s < t := by
  induction i generalizing j with
  | zero => cases j <;> simp [List.replicate_succ, List.cons_lt_cons_iff]
  | succ i ih =>
    cases j with
    | zero => simp [List.replicate_succ, List.cons_lt_cons_iff]
    | succ j => simpa [List.replicate_succ, List.cons_lt_cons_iff] using ih j

theorem tree_order (u v : List Bool) (h : u.length = v.length) :
    treeCode u < treeCode v ↔
      u.count true < v.count true ∨ u.count true = v.count true ∧ v < u := by
  obtain ⟨s, hs⟩ := suffix_head u
  obtain ⟨t, ht⟩ := suffix_head v
  have he := blocks_order u v h
  rw [hs, ht] at he
  simp only [List.cons_lt_cons_iff, lt_self_iff_false, true_and, false_or] at he
  change blocks u ++ [false] = false :: s at hs
  change blocks v ++ [false] = false :: t at ht
  simp only [treeCode, fold_code, List.append_nil, List.append_assoc, hs, ht,
    List.cons_lt_cons_iff, lt_self_iff_false, true_and, false_or, prefix_order, he]

theorem neg_count (w : List Bool) :
    (w.map Bool.not).count true + w.count true = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp_all <;> omega

theorem neg_order (u v : List Bool) (h : u.length = v.length) :
    u.map Bool.not < v.map Bool.not ↔ v < u := by
  induction u generalizing v with
  | nil => have : v = [] := List.length_eq_zero_iff.mp h.symm; subst v; simp
  | cons b u ih =>
    cases v with
    | nil => simp at h
    | cons c v =>
      have he := ih v (by simpa using h)
      cases b <;> cases c <;> simp_all [List.cons_lt_cons_iff]

theorem reverse_codes (u v : List Bool) (h : u.length = v.length) :
    treeCode (u.map Bool.not) < treeCode (v.map Bool.not) ↔ treeCode v < treeCode u := by
  rw [tree_order (u.map Bool.not) (v.map Bool.not) (by simpa using h),
    tree_order v u h.symm, neg_order v u h.symm]
  have hu := neg_count u
  have hv := neg_count v
  have hlt : (u.map Bool.not).count true < (v.map Bool.not).count true ↔
      v.count true < u.count true := by omega
  have heq : (u.map Bool.not).count true = (v.map Bool.not).count true ↔
      v.count true = u.count true := by omega
  rw [hlt, heq]

end RowReflection

namespace RowReflection
open OMA.S_oeis_a209861

def code {k : ℕ} (f : Fin k → Bool) := treeCode (List.ofFn f)

theorem code_injective {k : ℕ} : Function.Injective (@code k) := by
  intro f g h
  apply List.ofFn_injective
  let u := List.ofFn f
  let v := List.ofFn g
  change u = v
  change treeCode u = treeCode v at h
  have len : u.length = v.length := by simp [u, v]
  have h₁ := tree_order u v len
  have h₂ := tree_order v u len.symm
  rw [h] at h₁ h₂
  simp only [lt_self_iff_false, false_iff, not_or] at h₁ h₂
  have wt : u.count true = v.count true := by omega
  exact le_antisymm (le_of_not_gt fun h => h₁.2 ⟨wt, h⟩)
    (le_of_not_gt fun h => h₂.2 ⟨wt.symm, h⟩)

def flip {k : ℕ} : (Fin k → Bool) ≃ (Fin k → Bool) where
  toFun f i := !(f i)
  invFun f i := !(f i)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

theorem flip_order {k : ℕ} (f g : Fin k → Bool) :
    code (flip f) < code (flip g) ↔ code g < code f := by
  simpa [code, List.map_ofFn, flip, Function.comp_def] using
    reverse_codes (List.ofFn f) (List.ofFn g) (by simp)

theorem rank_sum {k : ℕ} (f : Fin k → Bool) :
    rowRank f + rowRank (flip f) + 1 = 2 ^ k := by
  classical
  let all := (Finset.univ : Finset (Fin k → Bool))
  let lt := all.filter (fun g => code g < code f)
  let gt := all.filter (fun g => code f < code g)
  have hf : f ∉ lt := by simp [lt]
  have hrest : all.filter (fun g => ¬ code f < code g) = insert f lt := by
    ext g
    simp only [all, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, lt]
    constructor
    · intro hn
      rcases lt_or_eq_of_le (le_of_not_gt hn) with h | h
      · exact Or.inr h
      · exact Or.inl (code_injective h)
    · rintro (rfl | h)
      · exact lt_irrefl _
      · exact not_lt_of_gt h
  have hflip : gt.card = rowRank (flip f) := by
    apply Finset.card_equiv flip
    intro i
    change (i ∈ all.filter (fun g => code f < code g)) ↔
      flip i ∈ Finset.univ.filter (fun g => code g < code (flip f))
    simpa only [all, Finset.mem_filter, Finset.mem_univ, true_and] using (flip_order i f).symm
  have h := Finset.card_filter_add_card_filter_not (s := all) (fun g => code f < code g)
  rw [hrest, Finset.card_insert_of_notMem hf] at h
  change gt.card + (lt.card + 1) = all.card at h
  rw [hflip] at h
  have hall : all.card = 2 ^ k := by simp [all]
  change lt.card + rowRank (flip f) + 1 = 2 ^ k
  omega

end RowReflection

open OMA.S_oeis_a209861 in
theorem OMA.solution : type_of% @OMA.S_oeis_a209861.main := by
  intro k x
  have hf : bits (reversed x) = RowReflection.flip (bits x) := by
    funext i
    simpa [reversed, bits, RowReflection.flip, i.isLt] using
      Nat.testBit_two_pow_sub_succ x.isLt i.val
  have h := RowReflection.rank_sum (bits x)
  simp only [output, hf, pow_succ]
  omega
