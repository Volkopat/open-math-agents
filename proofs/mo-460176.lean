import OMAStatements.S_mo_460176
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

-- Problem: Elementary recursion for A258173.
-- Source: https://mathoverflow.net/questions/460176
-- Credit: @mmexicann

open OMA.S_mo_460176
open scoped BigOperators

private abbrev Good {n b : ℕ} (u : Fin n → Fin (b + 1)) : Prop :=
  ∀ i : Fin n, i.val + 1 ≤ upCount u (i.val + 1)

private def peakProd {n b : ℕ} (u : Fin n → Fin (b + 1)) : ℕ :=
  ∏ i : Fin n, if (u i).val = 0 then 1 else upCount u (i.val + 1) - i.val

private def weightAt {n b : ℕ} (u : Fin n → Fin (b + 1)) (q : ℕ) : ℕ :=
  if upCount u n = n + q ∧ Good u then peakProd u else 0

private abbrev appendRun {n b : ℕ} (u : Fin n → Fin (b + 1)) (t : Fin (b + 1)) :
    Fin (n + 1) → Fin (b + 1) :=
  Fin.snoc (α := fun _ => Fin (b + 1)) u t

private theorem count_append {n b : ℕ} (u : Fin n → Fin (b + 1)) (t : Fin (b + 1)) (j : ℕ) :
    upCount (appendRun u t) j = upCount u j + if n < j then t.val else 0 := by
  conv_lhs => rw [upCount, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.snoc_castSucc, Fin.val_last, Fin.snoc_last]
  rfl

private theorem good_append {n b : ℕ} (u : Fin n → Fin (b + 1)) (t : Fin (b + 1)) :
    Good (appendRun u t) ↔ Good u ∧ n + 1 ≤ upCount u (n + 1) + t.val := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := h i.castSucc
      simpa [count_append, show ¬ n < i.val + 1 by omega] using hi
    · simpa [count_append] using h (Fin.last n)
  · rintro ⟨h, hlast⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [count_append] using hlast
    · simpa [count_append, show ¬ n < j.val + 1 by omega] using h j

private theorem count_full {n b : ℕ} (u : Fin n → Fin (b + 1)) :
    upCount u (n + 1) = upCount u n := by
  unfold upCount
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val < n + 1 := by omega
  simp [hi, i.isLt]

private theorem prod_append {n b : ℕ} (u : Fin n → Fin (b + 1)) (t : Fin (b + 1)) :
    peakProd (appendRun u t) =
      peakProd u * (if t.val = 0 then 1 else upCount u n + t.val - n) := by
  conv_lhs => rw [peakProd, Fin.prod_univ_castSucc]
  simp only [Fin.val_last, Fin.snoc_last, count_append, Nat.lt_succ_self, ite_true, count_full]
  congr 1
  unfold peakProd
  apply Finset.prod_congr rfl
  intro i _
  simp [show ¬ n < i.val + 1 by omega]

private theorem count_ge {n b : ℕ} {u : Fin n → Fin (b + 1)} (h : Good u) :
    n ≤ upCount u n := by
  cases n with
  | zero => omega
  | succ n => simpa using h (Fin.last n)

-- Separate the possible last run lengths. A zero run adds no new peak.
private theorem last_run_sum {n b q : ℕ} (hb : n + 1 + q ≤ b) (u : Fin n → Fin (b + 1)) :
    (∑ t : Fin (b + 1), weightAt (appendRun u t) q) =
      weightAt u (q + 1) + (q + 1) * ∑ j ∈ Finset.range (q + 1), weightAt u j := by
  by_cases hg : Good u
  · let j := upCount u n - n
    have hu : upCount u n = n + j := by dsimp [j]; have := count_ge hg; omega
    have hprev (k : ℕ) : weightAt u k = if k = j then peakProd u else 0 := by
      have he : (upCount u n = n + k ∧ Good u) ↔ k = j := by
        rw [hu]
        exact ⟨fun h => by have := h.1; omega, fun h => ⟨by omega, hg⟩⟩
      simp only [weightAt, he]
    have hnext (t : Fin (b + 1)) :
        weightAt (appendRun u t) q =
          if t.val + j = q + 1 then peakProd u * (if t.val = 0 then 1 else q + 1) else 0 := by
      have hcount : upCount (appendRun u t) (n + 1) = n + j + t.val := by
        simp [count_append, count_full, hu]
      have hgood : (upCount (appendRun u t) (n + 1) = n + 1 + q ∧ Good (appendRun u t)) ↔
          t.val + j = q + 1 := by
        constructor
        · rintro ⟨h, _⟩
          omega
        · intro h
          refine ⟨by omega, (good_append u t).mpr ⟨hg, ?_⟩⟩
          rw [count_full]
          omega
      simp only [weightAt, hgood, prod_append]
      by_cases ht : t.val + j = q + 1
      · have hp : upCount u n + t.val - n = q + 1 := by omega
        simp [ht, hp]
      · simp [ht]
    have hsum : (∑ k ∈ Finset.range (q + 1), weightAt u k) =
        if j ≤ q then peakProd u else 0 := by
      simp only [hprev, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]
    rw [hsum, hprev (q + 1)]
    by_cases ht : j ≤ q + 1
    · let t₀ : Fin (b + 1) := ⟨q + 1 - j, by omega⟩
      have huniq (t : Fin (b + 1)) : t.val + j = q + 1 ↔ t = t₀ := by
        constructor
        · intro he
          apply Fin.ext
          change t.val = q + 1 - j
          omega
        · intro he
          subst t
          change q + 1 - j + j = q + 1
          omega
      simp only [hnext, huniq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      by_cases hej : j = q + 1
      · have hzero : t₀.val = 0 := by dsimp [t₀]; omega
        simp [hej, hzero]
      · have hnonzero : t₀.val ≠ 0 := by dsimp [t₀]; omega
        simp [show q + 1 ≠ j by omega, show j ≤ q by omega, hnonzero, Nat.mul_comm]
    · have hnone (t : Fin (b + 1)) : t.val + j ≠ q + 1 := by omega
      simp [hnext, hnone, show q + 1 ≠ j by omega, show ¬ j ≤ q by omega]
  · simp [weightAt, good_append, hg]

private def totalWeight (n b q : ℕ) : ℕ :=
  ∑ u : Fin n → Fin (b + 1), weightAt u q

private theorem total_step {n b q : ℕ} (hb : n + 1 + q ≤ b) :
    totalWeight (n + 1) b q =
      totalWeight n b (q + 1) + (q + 1) * ∑ j ∈ Finset.range (q + 1), totalWeight n b j := by
  calc
    _ = ∑ p : Fin (b + 1) × (Fin n → Fin (b + 1)), weightAt (appendRun p.2 p.1) q :=
      (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin (b + 1))) _ _
        fun _ => rfl).symm
    _ = ∑ u : Fin n → Fin (b + 1), ∑ t : Fin (b + 1), weightAt (appendRun u t) q :=
      Fintype.sum_prod_type_right _
    _ = ∑ u : Fin n → Fin (b + 1),
        (weightAt u (q + 1) + (q + 1) * ∑ j ∈ Finset.range (q + 1), weightAt u j) := by
      apply Finset.sum_congr rfl
      intro u _
      exact last_run_sum hb u
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      rfl

private theorem total_eq_r {n b q : ℕ} (hb : n + q ≤ b) : totalWeight n b q = r n q := by
  induction n generalizing q with
  | zero => simp [totalWeight, weightAt, upCount, peakProd, r, eq_comm]
  | succ n ih =>
    rw [total_step hb, r, ih (q := q + 1) (by omega)]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact ih (by omega)

theorem OMA.solution : type_of% @OMA.S_mo_460176.main := by
  intro n
  rw [← total_eq_r (n := n) (b := n) (q := 0) (by omega)]
  simp [totalWeight, weightAt, dyckWeight, peakProd]
