import OMAStatements.S_oeis_a208634
import Mathlib

namespace OMA.S_oeis_a208634
open Finset

section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

def Chain (n : ℕ) := {y : Fin (n + 1) → S // ∀ i : Fin n, R (y i.castSucc) (y i.succ)}

instance (n : ℕ) : Fintype (Chain R n) := by unfold Chain; infer_instance

def V : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V n t else 0

theorem cardStart (n : ℕ) (s : S) :
    Fintype.card {y : Chain R n // y.1 0 = s} = V R n s := by
  induction n generalizing s with
  | zero =>
    simp only [V]
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨fun _ => s, fun i => i.elim0⟩, rfl⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, h0⟩
    apply Subtype.ext; apply Subtype.ext
    funext j
    have : j = 0 := Fin.ext (by have := j.2; omega)
    subst this; exact h0
  | succ n ih =>
    have e : {y : Chain R (n + 1) // y.1 0 = s} ≃
        Σ t : S, {z : Chain R n // z.1 0 = t ∧ R s t} :=
      { toFun := fun y => ⟨y.1.1 1, ⟨⟨fun j => y.1.1 j.succ, fun i => y.1.2 i.succ⟩, rfl, by
          have h := y.1.2 0
          have h0 : y.1.1 (Fin.castSucc 0) = s := y.2
          rw [h0] at h
          exact h⟩⟩
        invFun := fun p => ⟨⟨Fin.cons s p.2.1.1, by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · have h2 := p.2.2.2
            rw [← p.2.2.1] at h2
            simpa using h2
          · simpa using p.2.1.2 j⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨y, hy⟩, h0⟩
          apply Subtype.ext; apply Subtype.ext
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa using h0.symm
          · simp
        right_inv := by
          rintro ⟨t, ⟨⟨z, hz⟩, h1, h2⟩⟩
          simp only [Fin.cons_succ]
          have : (Fin.cons s z : Fin (n + 2) → S) 1 = t := by
            have : (1 : Fin (n + 2)) = Fin.succ 0 := rfl
            rw [this, Fin.cons_succ]; exact h1
          subst this
          rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [V]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : R s t
    · simp only [h, if_true, and_true]
      exact ih t
    · simp only [h, if_false, and_false]
      simp [Fintype.card_eq_zero_iff]

theorem cardChain (n : ℕ) : Fintype.card (Chain R n) = ∑ s, V R n s := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun y : Chain R n => y.1 0)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact cardStart R n s

theorem rec_gen (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) :
    ∀ n s, ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro s
    have : ∀ j, (V R (n + 1 + j) s : ℤ) = ∑ t, if R s t then (V R (n + j) t : ℤ) else 0 := by
      intro j
      rw [show n + 1 + j = (n + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h : R s t
    · have := ih t
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

theorem rec_total (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, (V R (n + j) s : ℤ)) = 0 := by
  have h := Finset.sum_eq_zero (s := (Finset.univ : Finset S)) (fun s _ => rec_gen R m c h0 n s)
  rw [Finset.sum_comm] at h
  simpa [Finset.mul_sum] using h
end generic

theorem rec_w {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]
    (m : ℕ) (c : ℕ → ℤ) (w : S → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, w s * (V R (n + j) s : ℤ)) = 0 := by
  have h : ∑ s, w s * ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 :=
    Finset.sum_eq_zero (fun s _ => by rw [rec_gen R m c h0 n s, mul_zero])
  simp only [Finset.mul_sum] at h ⊢
  rw [Finset.sum_comm] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  ring

abbrev Rw := Fin 5 → Fin 2

def cnt (u v : Rw) (j : Fin 5) : ℕ :=
  (if ∃ j' : Fin 5, j'.val + 1 = j.val ∧ v j' = v j then 1 else 0) +
  (if u j = v j then 1 else 0) +
  (if ∃ j' : Fin 5, j'.val = j.val + 1 ∧ u j' = v j then 1 else 0)

def Rel (u v : Rw) : Prop := ∀ j, cnt u v j ≤ 1

instance : DecidableRel Rel := fun u v => by unfold Rel cnt; infer_instance

theorem eqNbrs_zero {m : ℕ} (x : Fin (m + 1) → Rw) (j : Fin 5) : eqNbrs x 0 j ≤ 1 := by
  unfold eqNbrs
  have h1 : ¬ ∃ i' : Fin (m + 1), i'.val + 1 = (0 : Fin (m + 1)).val ∧ x i' j = x 0 j := by
    rintro ⟨i', h, _⟩; simp at h
  have h2 : ¬ ∃ i' : Fin (m + 1), ∃ j' : Fin 5, i'.val + 1 = (0 : Fin (m + 1)).val ∧
      j'.val = j.val + 1 ∧ x i' j' = x 0 j := by
    rintro ⟨i', _, h, _⟩; simp at h
  simp only [h1, h2, if_false]
  split_ifs <;> omega

theorem eqNbrs_succ {m : ℕ} (x : Fin (m + 1) → Rw) (i : Fin m) (j : Fin 5) :
    eqNbrs x i.succ j = cnt (x i.castSucc) (x i.succ) j := by
  unfold eqNbrs cnt
  have e1 : (∃ i' : Fin (m + 1), i'.val + 1 = i.succ.val ∧ x i' j = x i.succ j) ↔
      x i.castSucc j = x i.succ j := by
    constructor
    · rintro ⟨i', h1, h2⟩
      have : i' = i.castSucc := Fin.ext (by simp at h1 ⊢; omega)
      rwa [this] at h2
    · intro h; exact ⟨i.castSucc, by simp, h⟩
  have e2 : (∃ i' : Fin (m + 1), ∃ j' : Fin 5, i'.val + 1 = i.succ.val ∧
      j'.val = j.val + 1 ∧ x i' j' = x i.succ j) ↔
      ∃ j' : Fin 5, j'.val = j.val + 1 ∧ x i.castSucc j' = x i.succ j := by
    constructor
    · rintro ⟨i', j', h1, h2, h3⟩
      have : i' = i.castSucc := Fin.ext (by simp at h1 ⊢; omega)
      rw [this] at h3
      exact ⟨j', h2, h3⟩
    · rintro ⟨j', h2, h3⟩; exact ⟨i.castSucc, j', by simp, h2, h3⟩
  simp only [e1, e2]

theorem nbr_iff {m : ℕ} (x : Fin (m + 1) → Rw) :
    NbrCond x ↔ ∀ i : Fin m, Rel (x i.castSucc) (x i.succ) := by
  constructor
  · intro h i j
    rw [← eqNbrs_succ]; exact h i.succ j
  · intro h i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · exact eqNbrs_zero x j
    · rw [eqNbrs_succ]; exact h i' j

theorem rmn_iff {m : ℕ} (x : Fin (m + 1) → Rw) : RowMajorNew x ↔ x 0 0 = 0 := by
  constructor
  · intro h
    by_contra hne
    have h1 : (0 : Fin 2) < x 0 0 := by
      rcases Fin.exists_fin_two.mp ⟨x 0 0, rfl⟩ with h | h
      · exact absurd h hne
      · rw [h]; decide
    obtain ⟨i', j', hh, _⟩ := h 0 0 0 h1
    rcases hh with hh | ⟨_, hh⟩ <;> simp at hh
  · intro h i j u hu
    have hu0 : u = 0 := by
      have : (x i j : ℕ) < 2 := (x i j).2
      have := hu
      rw [Fin.lt_def] at this
      apply Fin.ext; simp; omega
    subst hu0
    refine ⟨0, 0, ?_, h⟩
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · subst hj; rw [h] at hu; exact absurd hu (by decide)
      · right; refine ⟨rfl, ?_⟩; exact Fin.pos_iff_ne_zero.mpr hj
    · left; exact Fin.pos_iff_ne_zero.mpr hi

def W (m : ℕ) : ℕ := ∑ s : Rw, if s 0 = 0 then V Rel m s else 0

theorem a_eq (m : ℕ) : a (m + 1) = W m := by
  classical
  unfold a W
  have e : (Finset.univ.filter (fun x : Fin (m + 1) → Rw => NbrCond x ∧ RowMajorNew x)).card =
      (Finset.univ.filter (fun y : Chain Rel m => y.1 0 0 = 0)).card := by
    refine Finset.card_bij (fun x hx => ⟨x, (nbr_iff x).1 (Finset.mem_filter.1 hx).2.1⟩) ?_ ?_ ?_
    · intro x hx
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      exact (rmn_iff x).1 (Finset.mem_filter.1 hx).2.2
    · intro x _ y _ h
      exact congrArg Subtype.val h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact ⟨y.1, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(nbr_iff y.1).2 y.2, (rmn_iff y.1).2 hy⟩, rfl⟩
  rw [e]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun y : Chain Rel m => y.1 0)
    (t := Finset.univ.filter (fun s : Rw => s 0 = 0))]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hs : s 0 = 0
    · simp only [hs, if_true]
      rw [← cardStart Rel m s, Fintype.card_subtype]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by rw [h]; exact hs, h⟩
    · simp [hs]
  · intro y hy
    simpa using hy

def cc : ℕ → ℤ := fun j => [(0 : ℤ), 0, 0, 0, -4, 10, -6, 1].getD j 0

def ww : Rw → ℤ := fun s => if s 0 = 0 then 1 else 0

theorem W_eq (m : ℕ) : (W m : ℤ) = ∑ s, ww s * (V Rel m s : ℤ) := by
  unfold W ww
  push_cast
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs <;> simp

theorem hrec (m : ℕ) : (W (m + 7) : ℤ) = 6 * W (m + 6) - 10 * W (m + 5) + 4 * W (m + 4) := by
  have h := rec_w Rel 7 cc ww (by decide +kernel) m
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = 0 := rfl
  have e2 : cc 2 = 0 := rfl
  have e3 : cc 3 = 0 := rfl
  have e4 : cc 4 = -4 := rfl
  have e5 : cc 5 = 10 := rfl
  have e6 : cc 6 = -6 := rfl
  have e7 : cc 7 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7] at h
  simp only [W_eq]
  linarith

theorem w0 : W 0 = 16 := by unfold W; decide +kernel
theorem w1 : W 1 = 47 := by unfold W; decide +kernel
theorem w2 : W 2 = 150 := by unfold W; decide +kernel
theorem w3 : W 3 = 494 := by unfold W; decide +kernel
theorem w4 : W 4 = 1652 := by unfold W; decide +kernel
theorem w5 : W 5 = 5572 := by unfold W; decide +kernel
theorem w6 : W 6 = 18888 := by unfold W; decide +kernel

theorem W_cubic (m : ℕ) : (W (m + 3) : ℤ) = 6 * W (m + 2) - 10 * W (m + 1) + 4 * W m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h : m ≤ 3
    · interval_cases m
      · rw [w3, w2, w1, w0]; norm_num
      · rw [w4, w3, w2, w1]; norm_num
      · rw [w5, w4, w3, w2]; norm_num
      · rw [w6, w5, w4, w3]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      exact hrec k

theorem a_cubic (k : ℕ) : (a (k + 4) : ℚ) = 6 * a (k + 3) - 10 * a (k + 2) + 4 * a (k + 1) := by
  rw [a_eq (k + 3), a_eq (k + 2), a_eq (k + 1), a_eq k]
  have := W_cubic k
  exact_mod_cast this

theorem a1 : a 1 = 16 := by rw [a_eq 0, w0]
theorem a2 : a 2 = 47 := by rw [a_eq 1, w1]
theorem a3 : a 3 = 150 := by rw [a_eq 2, w2]

noncomputable def cl (n : ℕ) : ℝ :=
  (3 * 2 ^ (1 + n) + (11 - 2 * Real.sqrt 2) * (2 - Real.sqrt 2) ^ n +
    (2 + Real.sqrt 2) ^ n * (11 + 2 * Real.sqrt 2)) / 4

theorem cl_rec (n : ℕ) : cl (n + 3) = 6 * cl (n + 2) - 10 * cl (n + 1) + 4 * cl n := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : (2 - Real.sqrt 2) ^ 3 = 6 * (2 - Real.sqrt 2) ^ 2 - 10 * (2 - Real.sqrt 2) + 4 := by
    linear_combination (-Real.sqrt 2) * hs
  have hy : (2 + Real.sqrt 2) ^ 3 = 6 * (2 + Real.sqrt 2) ^ 2 - 10 * (2 + Real.sqrt 2) + 4 := by
    linear_combination (Real.sqrt 2) * hs
  unfold cl
  have hx' : (2 - Real.sqrt 2) ^ (n + 3) = 6 * (2 - Real.sqrt 2) ^ (n + 2)
      - 10 * (2 - Real.sqrt 2) ^ (n + 1) + 4 * (2 - Real.sqrt 2) ^ n := by
    calc (2 - Real.sqrt 2) ^ (n + 3) = (2 - Real.sqrt 2) ^ n * (2 - Real.sqrt 2) ^ 3 := by ring
      _ = _ := by rw [hx]; ring
  have hy' : (2 + Real.sqrt 2) ^ (n + 3) = 6 * (2 + Real.sqrt 2) ^ (n + 2)
      - 10 * (2 + Real.sqrt 2) ^ (n + 1) + 4 * (2 + Real.sqrt 2) ^ n := by
    calc (2 + Real.sqrt 2) ^ (n + 3) = (2 + Real.sqrt 2) ^ n * (2 + Real.sqrt 2) ^ 3 := by ring
      _ = _ := by rw [hy]; ring
  have h2 : (2 : ℝ) ^ (1 + (n + 3)) = 6 * 2 ^ (1 + (n + 2)) - 10 * 2 ^ (1 + (n + 1)) + 4 * 2 ^ (1 + n) := by
    ring
  rw [hx', hy', h2]
  ring

theorem cl1 : cl 1 = 16 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold cl; linear_combination 1 * hs
theorem cl2 : cl 2 = 47 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold cl; linear_combination (19 / 2 : ℝ) * hs
theorem cl3 : cl 3 = 150 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold cl; linear_combination (Real.sqrt 2 ^ 2 + 47) * hs

theorem closedR : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = cl n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 3
    · interval_cases n
      · rw [a1, cl1]; norm_num
      · rw [a2, cl2]; norm_num
      · rw [a3, cl3]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have r : (a (k + 4) : ℝ) = 6 * a (k + 3) - 10 * a (k + 2) + 4 * a (k + 1) := by
        have := a_cubic k
        exact_mod_cast this
      rw [r, ih (k + 3) (by omega) (by omega), ih (k + 2) (by omega) (by omega),
        ih (k + 1) (by omega) (by omega)]
      have := cl_rec (k + 1)
      rw [this]

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 2 * X) * (1 - 4 * X + 2 * X ^ 2)) = X * (16 - 49 * X + 28 * X ^ 2) := by
  set f := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hf
  have h6 : (C 6 : PowerSeries ℚ) = 6 := map_ofNat C 6
  have h10 : (C 10 : PowerSeries ℚ) = 10 := map_ofNat C 10
  have h4 : (C 4 : PowerSeries ℚ) = 4 := map_ofNat C 4
  have h16 : (C 16 : PowerSeries ℚ) = 16 := map_ofNat C 16
  have h49 : (C 49 : PowerSeries ℚ) = 49 := map_ofNat C 49
  have h28 : (C 28 : PowerSeries ℚ) = 28 := map_ofNat C 28
  have e : f * ((1 - 2 * X) * (1 - 4 * X + 2 * X ^ 2)) =
      f - C 6 * (f * X) + C 10 * (f * X ^ 2) - C 4 * (f * X ^ 3) := by
    rw [h6, h10, h4]; ring
  have e2 : (X : PowerSeries ℚ) * (16 - 49 * X + 28 * X ^ 2) = C 16 * X - C 49 * X ^ 2 + C 28 * X ^ 3 := by
    rw [h16, h49, h28]; ring
  rw [e, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_X, hf, coeff_mk]
  rcases n with _ | _ | _ | _ | k
  · simp
  · simp [a1]
  · simp [a1, a2]; norm_num
  · simp [a1, a2, a3]; norm_num
  · have h4 : (a (k + 1 + 1 + 1 + 1) : ℚ) = 6 * a (k + 3) - 10 * a (k + 2) + 4 * a (k + 1) :=
      a_cubic k
    simp
    linarith

end OMA.S_oeis_a208634

theorem OMA.solution : type_of% @OMA.S_oeis_a208634.main :=
  ⟨OMA.S_oeis_a208634.gf, fun n hn => OMA.S_oeis_a208634.closedR n hn⟩
