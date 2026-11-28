import OMAStatements.S_mo_309485
import Mathlib

-- Problem: An eigenvalue of certain family of matrices
-- Upstream: formal-conjectures statements/mo-309485.lean:0 (declaration OMA.S_mo_309485.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

namespace M309485

lemma lemA (m k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (Nat.choose (m + 1) j : ℂ) =
      (-1) ^ k * (Nat.choose m k : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    have hp : (Nat.choose (m + 1) (k + 1) : ℂ) = Nat.choose m k + Nat.choose m (k + 1) := by
      exact_mod_cast Nat.choose_succ_succ' m k
    rw [hp]
    ring

lemma lemB (m k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (j : ℂ) * (Nat.choose (m + 2) j : ℂ) =
      (-1) ^ k * ((m : ℂ) + 2) * ((Nat.choose (m + 1) k : ℂ) - Nat.choose m k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    have hp : (Nat.choose (m + 1) (k + 1) : ℂ) = Nat.choose m k + Nat.choose m (k + 1) := by
      exact_mod_cast Nat.choose_succ_succ' m k
    have h : ((k : ℂ) + 1) * (Nat.choose (m + 2) (k + 1) : ℂ) =
        ((m : ℂ) + 2) * Nat.choose (m + 1) k := by
      have := Nat.add_one_mul_choose_eq (m + 1) k
      have h2 : (((m + 1 + 1) * (m + 1).choose k : ℕ) : ℂ) =
          (((m + 1 + 1).choose (k + 1) * (k + 1) : ℕ) : ℂ) := by rw [this]
      push_cast at h2
      linear_combination -h2
    push_cast
    linear_combination (-1 : ℂ) ^ (k + 1) * h - (-1 : ℂ) ^ (k + 1) * ((m : ℂ) + 2) * hp

noncomputable def alt (p j : ℕ) : ℂ := (-1) ^ j * (2 * (j : ℂ) - (2 * (p : ℂ) + 3))

noncomputable def e (p j : ℕ) : ℂ :=
  (if j = 0 then -(2 * (p : ℂ) + 3) else 0) + (if j = 1 then 2 else 0)

noncomputable def v (p j : ℕ) : ℂ := alt p j + e p j

lemma sumE (p : ℕ) (c : ℕ → ℂ) :
    ∑ j ∈ range (p + 1 + 1), c j * e p j = -(2 * (p : ℂ) + 3) * c 0 + 2 * c 1 := by
  rw [sum_range_succ', sum_range_succ']
  simp [e]
  ring

lemma sumAlt (p m k : ℕ) :
    ∑ j ∈ range (k + 1), (Nat.choose (m + 2) j : ℂ) * ((-1) ^ j * (2 * (j : ℂ) - (2 * (p : ℂ) + 3))) =
      2 * ((-1) ^ k * ((m : ℂ) + 2) * ((Nat.choose (m + 1) k : ℂ) - Nat.choose m k)) -
        (2 * (p : ℂ) + 3) * ((-1) ^ k * (Nat.choose (m + 1) k : ℂ)) := by
  rw [← lemB, ← lemA (m + 1) k, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  ring

lemma hPE (p i d : ℕ) (h : i + d = p + 1) :
    ∑ j ∈ range (p + 1 + 1), (Nat.choose i j : ℂ) * alt p j +
      ∑ j ∈ range (p + 1 + 1), ((Nat.choose i j : ℂ) +
        (if i ≤ j then (Nat.choose (p + d + 2) (j - i) : ℂ) else 0) +
        (Nat.choose (p + d + 2) j : ℂ)) * e p j = 0 := by
  rw [sumE]
  rcases i with _ | _ | i
  · have hd : d = p + 1 := by omega
    subst hd
    rw [sum_range_succ']
    simp [alt]
    ring
  · have hd : d = p := by omega
    subst hd
    rw [sum_range_succ', sum_range_succ']
    have h0 : ∀ j : ℕ, Nat.choose 1 (j + 1 + 1) = 0 :=
      fun j => Nat.choose_eq_zero_of_lt (by omega)
    simp [alt, h0]
    ring
  · have h1 : ∑ j ∈ range (p + 1 + 1), (Nat.choose (i + 2) j : ℂ) * alt p j = 0 := by
      unfold alt
      rw [sumAlt p i (p + 1)]
      have c1 : Nat.choose (i + 1) (p + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have c2 : Nat.choose i (p + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [c1, c2]
    rw [h1]
    have hi : (i : ℂ) + 2 + d = p + 1 := by exact_mod_cast h
    simp
    linear_combination 2 * hi

lemma hR (p d : ℕ) :
    ∑ j ∈ range (p + 1 + 1), (Nat.choose (p + d + 2) j : ℂ) * alt p j =
      (-1) ^ (p + 1) * (2 * ((p : ℂ) + d + 2) *
        ((Nat.choose (p + d + 1) (p + 1) : ℂ) - Nat.choose (p + d) (p + 1)) -
        (2 * (p : ℂ) + 3) * Nat.choose (p + d + 1) (p + 1)) := by
  unfold alt
  rw [sumAlt p (p + d) (p + 1)]
  push_cast
  ring

lemma hQ (p i d : ℕ) (h : i + d = p + 1) :
    ∑ j ∈ range (p + 1 + 1),
        (if i ≤ j then (Nat.choose (p + d + 2) (j - i) : ℂ) else 0) * alt p j =
      (-1) ^ (p + 1) * ((2 * (i : ℂ) - (2 * (p : ℂ) + 3)) * Nat.choose (p + d + 1) (p + 1) +
        2 * ((p : ℂ) + d + 2) * Nat.choose (p + d) (p + 1)) := by
  have hr : p + 1 + 1 = i + (d + 1) := by omega
  rw [hr, sum_range_add]
  have hz : ∑ j ∈ range i,
      (if i ≤ j then (Nat.choose (p + d + 2) (j - i) : ℂ) else 0) * alt p j = 0 := by
    apply sum_eq_zero
    intro j hj
    have : ¬ i ≤ j := by have := mem_range.mp hj; omega
    rw [if_neg this, zero_mul]
  rw [hz, zero_add]
  have hs : ∑ k ∈ range (d + 1),
      (if i ≤ i + k then (Nat.choose (p + d + 2) (i + k - i) : ℂ) else 0) * alt p (i + k) =
      (-1) ^ i * ∑ k ∈ range (d + 1), (Nat.choose (p + d + 2) k : ℂ) *
        ((-1) ^ k * (2 * (k : ℂ) - (2 * (p : ℂ) + 3 - 2 * i))) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [if_pos (Nat.le_add_right i k), Nat.add_sub_cancel_left]
    unfold alt
    push_cast
    ring
  rw [hs]
  have hsplit : ∑ k ∈ range (d + 1), (Nat.choose (p + d + 2) k : ℂ) *
        ((-1) ^ k * (2 * (k : ℂ) - (2 * (p : ℂ) + 3 - 2 * i))) =
      2 * ((-1) ^ d * (((p + d : ℕ) : ℂ) + 2) *
          ((Nat.choose (p + d + 1) d : ℂ) - Nat.choose (p + d) d)) -
        (2 * (p : ℂ) + 3 - 2 * i) * ((-1) ^ d * (Nat.choose (p + d + 1) d : ℂ)) := by
    rw [← lemB, ← lemA (p + d + 1) d, mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  have s1 : Nat.choose (p + d + 1) d = Nat.choose (p + d + 1) (p + 1) := by
    have := Nat.choose_symm_add (a := d) (b := p + 1)
    have e1 : d + (p + 1) = p + d + 1 := by omega
    rw [e1] at this
    exact this
  have s2 : Nat.choose (p + d) d = Nat.choose (p + d) p := by
    have := Nat.choose_symm_add (a := d) (b := p)
    have e1 : d + p = p + d := by omega
    rw [e1] at this
    exact this
  have hp : (Nat.choose (p + d + 1) (p + 1) : ℂ) =
      Nat.choose (p + d) p + Nat.choose (p + d) (p + 1) := by
    exact_mod_cast Nat.choose_succ_succ' (p + d) p
  have hpow : (-1 : ℂ) ^ i * (-1) ^ d = (-1) ^ (p + 1) := by rw [← pow_add, h]
  rw [s1, s2]
  push_cast
  rw [← hpow, hp]
  ring

lemma key (p i d : ℕ) (h : i + d = p + 1) :
    ∑ j ∈ range (p + 1 + 1), ((Nat.choose i j : ℂ) +
        (if i ≤ j then (Nat.choose (2 * (p + 1) + 1 - i) (j - i) : ℂ) else 0) +
        (Nat.choose (2 * (p + 1) + 1 - i) j : ℂ)) * v p j = 0 := by
  have hm : 2 * (p + 1) + 1 - i = p + d + 2 := by omega
  rw [hm]
  have hsplit : ∀ j : ℕ, ((Nat.choose i j : ℂ) +
        (if i ≤ j then (Nat.choose (p + d + 2) (j - i) : ℂ) else 0) +
        (Nat.choose (p + d + 2) j : ℂ)) * v p j =
      (Nat.choose i j : ℂ) * alt p j +
        ((Nat.choose i j : ℂ) + (if i ≤ j then (Nat.choose (p + d + 2) (j - i) : ℂ) else 0) +
          (Nat.choose (p + d + 2) j : ℂ)) * e p j +
        (if i ≤ j then (Nat.choose (p + d + 2) (j - i) : ℂ) else 0) * alt p j +
        (Nat.choose (p + d + 2) j : ℂ) * alt p j := by
    intro j
    unfold v
    ring
  simp_rw [hsplit]
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, hPE p i d h, hQ p i d h, hR p d]
  have hi : (i : ℂ) + d = p + 1 := by exact_mod_cast h
  linear_combination (2 * (-1 : ℂ) ^ (p + 1) * (Nat.choose (p + d + 1) (p + 1) : ℂ)) * hi

end M309485

theorem OMA.solution : type_of% @OMA.S_mo_309485.main := by
  intro n
  constructor
  · intro h
    by_contra hn
    have h0 : n = 0 := by omega
    subst h0
    obtain ⟨w, hw⟩ := h.exists_hasEigenvector
    have h1 := hw.apply_eq_smul
    apply hw.2
    funext i
    have h2 := congrFun h1 i
    have hi : i = 0 := Fin.ext (by simp)
    subst hi
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, OMA.S_mo_309485.matrix] at h2
    rcases h2 with h3 | h3
    · norm_num at h3
    · simpa using h3
  · intro hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := fun j : Fin (p + 1 + 1) => M309485.v p j.val)
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, zero_smul]
      funext i
      have hk := M309485.key p i.val (p + 1 - i.val) (by omega)
      rw [← Fin.sum_univ_eq_sum_range] at hk
      simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, OMA.S_mo_309485.matrix] using hk
    · intro h0
      have h1 := congrFun h0 ⟨1, by omega⟩
      simp [M309485.v, M309485.alt, M309485.e] at h1
      have h2 : ((2 * p + 3 : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination h1
      have := Nat.cast_eq_zero.mp h2
      omega
