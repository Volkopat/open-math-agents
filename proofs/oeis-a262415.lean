import OMAStatements.S_oeis_a262415
import Mathlib.Tactic

namespace OMA.P_oeis_a262415

open OMA.S_oeis_a262415

private def b2n (b : Bool) : ℕ := if b then 1 else 0

private lemma colVal_zero (f : Fin 0 → Bool) : colVal f = 0 := by
  unfold colVal; simp

private lemma colVal_succ {m : ℕ} (f : Fin (m + 1) → Bool) :
    colVal f = 2 * colVal (fun i : Fin m => f ⟨i.1, by omega⟩) + b2n (f ⟨m, Nat.lt_succ_self m⟩) := by
  unfold colVal b2n
  rw [Fin.sum_univ_castSucc, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.val_castSucc, Nat.add_sub_cancel]
    have hcs : i.castSucc = ⟨i.1, by omega⟩ := rfl
    have hexp : m - i.1 = (m - 1 - i.1) + 1 := by omega
    rw [hcs, hexp, pow_succ]; ring
  · have hlast : Fin.last m = ⟨m, Nat.lt_succ_self m⟩ := rfl
    simp [hlast]

private lemma rowVal_mod3 (r : Fin 4 → Bool) :
    rowVal r % 3 = (2 * b2n (r 0) + b2n (r 1) + 2 * b2n (r 2) + b2n (r 3)) % 3 := by
  unfold rowVal b2n
  cases r 0 <;> cases r 1 <;> cases r 2 <;> cases r 3 <;> decide

private lemma row3_inv (r : Fin 4 → Bool) (hr : 3 ∣ rowVal r) :
    (b2n (r 0) + 2 * b2n (r 1) + b2n (r 2)) % 3 = b2n (r 3) % 3 := by
  have h0 : rowVal r % 3 = 0 := Nat.mod_eq_zero_of_dvd hr
  rw [rowVal_mod3] at h0
  unfold b2n at h0 ⊢
  generalize ha : r 0 = a at h0 ⊢
  generalize hb : r 1 = b at h0 ⊢
  generalize hc : r 2 = c at h0 ⊢
  generalize hd : r 3 = d at h0 ⊢
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private def colMod3 {m : ℕ} (A : Fin m × Fin 4 → Bool) : Fin 3 × Fin 3 × Fin 3 :=
  (⟨colVal (fun i => A (i, 0)) % 3, Nat.mod_lt _ (by omega)⟩,
   ⟨colVal (fun i => A (i, 1)) % 3, Nat.mod_lt _ (by omega)⟩,
   ⟨colVal (fun i => A (i, 2)) % 3, Nat.mod_lt _ (by omega)⟩)

private lemma col3_from_colMod3 {m : ℕ} (A : Fin m × Fin 4 → Bool)
    (hrows : ∀ i : Fin m, 3 ∣ rowVal (fun j => A (i, j))) :
    colVal (fun i => A (i, 3)) % 3 =
      ((colMod3 A).1.1 + 2 * (colMod3 A).2.1.1 + (colMod3 A).2.2.1) % 3 := by
  induction m with
  | zero => simp [colMod3, colVal_zero]
  | succ m ih =>
    let A' : Fin m × Fin 4 → Bool := fun p => A (⟨p.1.1, by omega⟩, p.2)
    have ih' := ih A' (fun i => hrows ⟨i.1, by omega⟩)
    have hr := row3_inv (fun j => A (⟨m, Nat.lt_succ_self m⟩, j)) (hrows ⟨m, Nat.lt_succ_self m⟩)
    dsimp only [colMod3] at ih' ⊢
    rw [colVal_succ (fun i => A (i, 0)), colVal_succ (fun i => A (i, 1)),
      colVal_succ (fun i => A (i, 2)), colVal_succ (fun i => A (i, 3))]
    dsimp only [A'] at ih'
    omega

private def goodState (s : Fin 3 × Fin 3 × Fin 3) : Bool :=
  decide (s.1.1 ≠ 0 ∧ s.2.1.1 ≠ 0 ∧ s.2.2.1 ≠ 0 ∧ (s.1.1 + 2 * s.2.1.1 + s.2.2.1) % 3 ≠ 0)

private def isValidRows (m : ℕ) (A : Fin m × Fin 4 → Bool) : Prop :=
  ∀ i : Fin m, 3 ∣ rowVal (fun j => A (i, j))

private instance (m : ℕ) (A : Fin m × Fin 4 → Bool) : Decidable (isValidRows m A) := by
  unfold isValidRows; infer_instance

private def stateCount (m : ℕ) (s : Fin 3 × Fin 3 × Fin 3) : ℤ :=
  ∑ A : Fin m × Fin 4 → Bool,
    if isValidRows m A ∧ colMod3 A = s then 1 else 0

private lemma A262415_eq_sum_stateCount (n : ℕ) :
    (A262415 n : ℤ) = ∑ s : Fin 3 × Fin 3 × Fin 3, if goodState s then stateCount (n + 1) s else 0 := by
  unfold A262415 stateCount
  have hcard : ∀ S : Finset (Fin (n + 1) × Fin 4 → Bool),
      (S.card : ℤ) = ∑ A : Fin (n + 1) × Fin 4 → Bool, if A ∈ S then (1 : ℤ) else 0 := by
    intro S; simp
  rw [hcard]
  trans ∑ A : Fin (n + 1) × Fin 4 → Bool, ∑ s : Fin 3 × Fin 3 × Fin 3,
      if goodState s = true ∧ isValidRows (n + 1) A ∧ colMod3 A = s then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun A _ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.sum_eq_single (colMod3 A)]
    · by_cases hr : isValidRows (n + 1) A
      · have hcol3 := col3_from_colMod3 A hr
        have hiff : (∀ j : Fin 4, ¬ (3 ∣ colVal (fun i => A (i, j)))) ↔ goodState (colMod3 A) = true := by
          unfold goodState colMod3 at hcol3 ⊢
          dsimp only at hcol3
          simp only [decide_eq_true_eq, Nat.dvd_iff_mod_eq_zero]
          constructor
          · intro h
            refine ⟨h 0, h 1, h 2, ?_⟩
            rw [← hcol3]; exact h 3
          · rintro ⟨h0, h1, h2, h3⟩ j
            fin_cases j
            · exact h0
            · exact h1
            · exact h2
            · dsimp only; change ¬ (colVal (fun i => A (i, 3)) % 3 = 0); rw [hcol3]; exact h3
        by_cases hg : goodState (colMod3 A) = true
        · rw [if_pos ⟨hr, hiff.mpr hg⟩, if_pos ⟨hg, hr, rfl⟩]
        · rw [if_neg (fun h => hg (hiff.mp h.2)), if_neg (fun h => hg h.1)]
      · rw [if_neg (fun h => hr h.1), if_neg (fun h => hr h.2.1)]
    · intro s _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hg : goodState s = true
    · simp [hg]
    · simp [hg]

private def stepVec (v : Fin 3 × Fin 3 × Fin 3 → ℤ) (s : Fin 3 × Fin 3 × Fin 3) : ℤ :=
  ∑ s' : Fin 3 × Fin 3 × Fin 3, ∑ r : Fin 4 → Bool,
    if 3 ∣ rowVal r ∧
       ((⟨(2 * s'.1.1 + b2n (r 0)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
        (⟨(2 * s'.2.1.1 + b2n (r 1)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
        (⟨(2 * s'.2.2.1 + b2n (r 2)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3)) = s
    then v s' else 0

private lemma stepVec_add (u v : Fin 3 × Fin 3 × Fin 3 → ℤ) (s : Fin 3 × Fin 3 × Fin 3) :
    stepVec (fun x => u x + v x) s = stepVec u s + stepVec v s := by
  unfold stepVec
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> ring

private lemma stepVec_sub (u v : Fin 3 × Fin 3 × Fin 3 → ℤ) (s : Fin 3 × Fin 3 × Fin 3) :
    stepVec (fun x => u x - v x) s = stepVec u s - stepVec v s := by
  unfold stepVec
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> ring

private lemma stepVec_smul (c : ℤ) (v : Fin 3 × Fin 3 × Fin 3 → ℤ) (s : Fin 3 × Fin 3 × Fin 3) :
    stepVec (fun x => c * v x) s = c * stepVec v s := by
  unfold stepVec
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> ring

private lemma stateCount_zero (s : Fin 3 × Fin 3 × Fin 3) :
    stateCount 0 s = if s = (0, 0, 0) then 1 else 0 := by
  unfold stateCount isValidRows colMod3
  have huniq : (Finset.univ : Finset (Fin 0 × Fin 4 → Bool)) = {fun p => Fin.elim0 p.1} := by
    ext A; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    funext ⟨i, _⟩; exact Fin.elim0 i
  rw [huniq, Finset.sum_singleton]
  have hv : ∀ i : Fin 0, 3 ∣ rowVal (fun j => Fin.elim0 i) := fun i => Fin.elim0 i
  have hm : ((⟨colVal (fun i : Fin 0 => Fin.elim0 i) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
      (⟨colVal (fun i : Fin 0 => Fin.elim0 i) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
      (⟨colVal (fun i : Fin 0 => Fin.elim0 i) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3)) = (0, 0, 0) := by
    simp [colVal_zero]
  simp only [hv, hm, eq_comm]; simp

private lemma stateCount_succ (m : ℕ) (s : Fin 3 × Fin 3 × Fin 3) :
    stateCount (m + 1) s = stepVec (stateCount m) s := by
  let e : (Fin (m + 1) × Fin 4 → Bool) ≃ ((Fin m × Fin 4 → Bool) × (Fin 4 → Bool)) :=
    { toFun := fun A => (fun p => A (⟨p.1.1, by omega⟩, p.2), fun j => A (⟨m, Nat.lt_succ_self m⟩, j))
      invFun := fun ⟨A', r⟩ p => if h : p.1.1 < m then A' (⟨p.1.1, h⟩, p.2) else r p.2
      left_inv := fun A => by
        funext ⟨i, j⟩
        by_cases h : i.1 < m
        · simp [h]
        · have hi : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
          subst hi; simp
      right_inv := fun ⟨A', r⟩ => by
        apply Prod.ext
        · funext ⟨i, j⟩; simp [i.isLt]
        · funext j; simp }
  have hiff : ∀ A : Fin (m + 1) × Fin 4 → Bool,
      (isValidRows (m + 1) A ∧ colMod3 A = s) ↔
      (isValidRows m (e A).1 ∧ 3 ∣ rowVal (e A).2 ∧
       ((⟨(2 * (colMod3 (e A).1).1.1 + b2n ((e A).2 0)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
        (⟨(2 * (colMod3 (e A).1).2.1.1 + b2n ((e A).2 1)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
        (⟨(2 * (colMod3 (e A).1).2.2.1 + b2n ((e A).2 2)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3)) = s) := by
    intro A
    have hcm : colMod3 A =
        ((⟨(2 * (colMod3 (e A).1).1.1 + b2n ((e A).2 0)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
         (⟨(2 * (colMod3 (e A).1).2.1.1 + b2n ((e A).2 1)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
         (⟨(2 * (colMod3 (e A).1).2.2.1 + b2n ((e A).2 2)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3)) := by
      simp only [colMod3, e, Equiv.coe_fn_mk, Prod.mk.injEq, Fin.ext_iff]
      refine ⟨?_, ?_, ?_⟩
      · rw [colVal_succ (fun i => A (i, 0))]; omega
      · rw [colVal_succ (fun i => A (i, 1))]; omega
      · rw [colVal_succ (fun i => A (i, 2))]; omega
    rw [hcm]
    simp only [e, Equiv.coe_fn_mk, isValidRows]
    constructor
    · rintro ⟨hA, hs⟩
      exact ⟨fun i => hA ⟨i.1, by omega⟩, hA ⟨m, Nat.lt_succ_self m⟩, hs⟩
    · rintro ⟨hA', hlast, hs⟩
      refine ⟨fun i => ?_, hs⟩
      by_cases hi : i.1 < m
      · exact hA' ⟨i.1, hi⟩
      · have hieq : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
        subst hieq; exact hlast
  unfold stateCount stepVec
  rw [Fintype.sum_equiv e _ (fun p =>
      if isValidRows m p.1 ∧ 3 ∣ rowVal p.2 ∧
         ((⟨(2 * (colMod3 p.1).1.1 + b2n (p.2 0)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
          (⟨(2 * (colMod3 p.1).2.1.1 + b2n (p.2 1)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
          (⟨(2 * (colMod3 p.1).2.2.1 + b2n (p.2 2)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3)) = s
      then (1 : ℤ) else 0)
      (fun A => by simp only [hiff A])]
  rw [Fintype.sum_prod_type]
  symm
  trans ∑ s' : Fin 3 × Fin 3 × Fin 3, ∑ r : Fin 4 → Bool, ∑ A' : Fin m × Fin 4 → Bool,
      if isValidRows m A' ∧ colMod3 A' = s' ∧ 3 ∣ rowVal r ∧
         ((⟨(2 * s'.1.1 + b2n (r 0)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
          (⟨(2 * s'.2.1.1 + b2n (r 1)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
          (⟨(2 * s'.2.2.1 + b2n (r 2)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3)) = s
      then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun r _ => ?_
    by_cases hc : 3 ∣ rowVal r ∧
        ((⟨(2 * s'.1.1 + b2n (r 0)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
         (⟨(2 * s'.2.1.1 + b2n (r 1)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3),
         (⟨(2 * s'.2.2.1 + b2n (r 2)) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3)) = s
    · simp [hc]
    · simp [hc]
  · rw [Finset.sum_comm]
    conv_lhs => arg 2; ext r; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A' _ => Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single (colMod3 A')]
    · simp
    · intro s' _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private def tab0 : Fin 3 × Fin 3 × Fin 3 → ℤ
  | (0, 0, 0) => 1
  | _ => 0

private def tab1 : Fin 3 × Fin 3 × Fin 3 → ℤ
  | (0, 0, 0) => 1
  | (0, 0, 1) => 1
  | (0, 1, 1) => 1
  | (1, 0, 0) => 1
  | (1, 1, 0) => 1
  | (1, 1, 1) => 1
  | _ => 0

private def tab2 : Fin 3 × Fin 3 × Fin 3 → ℤ
  | (0, 0, 0) => 6
  | (0, 0, 1) => 2
  | (0, 0, 2) => 2
  | (0, 1, 0) => 2
  | (0, 1, 1) => 2
  | (0, 1, 2) => 0
  | (0, 2, 0) => 2
  | (0, 2, 1) => 0
  | (0, 2, 2) => 2
  | (1, 0, 0) => 2
  | (1, 0, 1) => 0
  | (1, 0, 2) => 2
  | (1, 1, 0) => 2
  | (1, 1, 1) => 1
  | (1, 1, 2) => 1
  | (1, 2, 0) => 0
  | (1, 2, 1) => 0
  | (1, 2, 2) => 1
  | (2, 0, 0) => 2
  | (2, 0, 1) => 2
  | (2, 0, 2) => 0
  | (2, 1, 0) => 0
  | (2, 1, 1) => 1
  | (2, 1, 2) => 0
  | (2, 2, 0) => 2
  | (2, 2, 1) => 1
  | (2, 2, 2) => 1

private def tab3 : Fin 3 × Fin 3 × Fin 3 → ℤ
  | (0, 0, 0) => 15
  | (0, 0, 1) => 15
  | (0, 1, 1) => 15
  | (1, 0, 0) => 15
  | (1, 1, 0) => 15
  | (1, 1, 1) => 15
  | _ => 6

private def tab4 : Fin 3 × Fin 3 × Fin 3 → ℤ
  | (0, 0, 0) => 90
  | (0, 0, 1) => 54
  | (0, 0, 2) => 54
  | (0, 1, 0) => 54
  | (0, 1, 1) => 54
  | (0, 1, 2) => 36
  | (0, 2, 0) => 54
  | (0, 2, 1) => 36
  | (0, 2, 2) => 54
  | (1, 0, 0) => 54
  | (1, 0, 1) => 36
  | (1, 0, 2) => 54
  | (1, 1, 0) => 54
  | (1, 1, 1) => 45
  | (1, 1, 2) => 45
  | (1, 2, 0) => 36
  | (1, 2, 1) => 36
  | (1, 2, 2) => 45
  | (2, 0, 0) => 54
  | (2, 0, 1) => 54
  | (2, 0, 2) => 36
  | (2, 1, 0) => 36
  | (2, 1, 1) => 45
  | (2, 1, 2) => 36
  | (2, 2, 0) => 54
  | (2, 2, 1) => 45
  | (2, 2, 2) => 45

private lemma stateCount_0_eq : stateCount 0 = tab0 := by
  funext s; rw [stateCount_zero]; revert s; decide
private lemma stateCount_1_eq : stateCount 1 = tab1 := by
  funext s; rw [stateCount_succ, stateCount_0_eq]; revert s; decide
private lemma stateCount_2_eq : stateCount 2 = tab2 := by
  funext s; rw [stateCount_succ, stateCount_1_eq]; revert s; decide
private lemma stateCount_3_eq : stateCount 3 = tab3 := by
  funext s; rw [stateCount_succ, stateCount_2_eq]; revert s; decide
private lemma stateCount_4_eq : stateCount 4 = tab4 := by
  funext s; rw [stateCount_succ, stateCount_3_eq]; revert s; decide

private lemma stateCount_rec_base :
    stateCount 4 = fun s => 6 * stateCount 3 s + 9 * stateCount 2 s - 54 * stateCount 1 s := by
  rw [stateCount_4_eq, stateCount_3_eq, stateCount_2_eq, stateCount_1_eq]
  funext s; revert s; decide

private lemma stateCount_rec (m : ℕ) :
    stateCount (m + 4) = fun s =>
      6 * stateCount (m + 3) s + 9 * stateCount (m + 2) s - 54 * stateCount (m + 1) s := by
  induction m with
  | zero => exact stateCount_rec_base
  | succ m ih =>
    funext s
    conv_lhs =>
      rw [stateCount_succ (m + 4) s, ih, stepVec_sub, stepVec_add, stepVec_smul, stepVec_smul,
        stepVec_smul, ← stateCount_succ (m + 3) s, ← stateCount_succ (m + 2) s,
        ← stateCount_succ (m + 1) s]

private lemma A262415_rec (m : ℕ) :
    (A262415 (m + 4) : ℤ) = 6 * A262415 (m + 3) + 9 * A262415 (m + 2) - 54 * A262415 (m + 1) := by
  simp only [A262415_eq_sum_stateCount]
  rw [show m + 4 + 1 = (m + 1) + 4 by omega, show m + 3 + 1 = (m + 1) + 3 by omega,
    show m + 2 + 1 = (m + 1) + 2 by omega, show m + 1 + 1 = (m + 1) + 1 by omega,
    stateCount_rec (m + 1)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> ring

private lemma A262415_small : A262415 1 = 6 ∧ A262415 2 = 45 ∧ A262415 3 = 270 := by
  have h1 : (A262415 1 : ℤ) = 6 := by rw [A262415_eq_sum_stateCount 1, stateCount_2_eq]; decide
  have h2 : (A262415 2 : ℤ) = 45 := by rw [A262415_eq_sum_stateCount 2, stateCount_3_eq]; decide
  have h3 : (A262415 3 : ℤ) = 270 := by rw [A262415_eq_sum_stateCount 3, stateCount_4_eq]; decide
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

private lemma coeff_X_pow_mul_eq (k : ℕ) (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ k * f) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with hk
  · rw [Finset.sum_eq_single (k, n - k)]
    · rw [PowerSeries.coeff_X_pow, if_pos rfl, one_mul]
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have hne1 : p.1 ≠ k := fun h => hne (Prod.ext h (by omega))
      rw [PowerSeries.coeff_X_pow, if_neg hne1, zero_mul]
    · intro hnot; exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega
  · apply Finset.sum_eq_zero
    intro p hp; rw [Finset.mem_antidiagonal] at hp
    rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]

private lemma A262415_gf :
    (1 - 3 * PowerSeries.X) * (1 + 3 * PowerSeries.X) * (1 - 6 * PowerSeries.X) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A262415 n : ℤ)) =
      3 * PowerSeries.X * (2 + 3 * PowerSeries.X - 18 * PowerSeries.X ^ 2) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A262415 n : ℤ))
  have hlhs : (1 - 3 * PowerSeries.X) * (1 + 3 * PowerSeries.X) * (1 - 6 * PowerSeries.X) * F =
      F - PowerSeries.C 6 * (PowerSeries.X ^ 1 * F) -
        PowerSeries.C 9 * (PowerSeries.X ^ 2 * F) + PowerSeries.C 54 * (PowerSeries.X ^ 3 * F) := by
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h9 : PowerSeries.C (9 : ℤ) = (9 : PowerSeries ℤ) := rfl
    have h54 : PowerSeries.C (54 : ℤ) = (54 : PowerSeries ℤ) := rfl
    rw [h6, h9, h54, pow_one]; ring
  have hrhs : 3 * (PowerSeries.X : PowerSeries ℤ) *
        (2 + 3 * PowerSeries.X - 18 * PowerSeries.X ^ 2) =
      PowerSeries.C 6 * PowerSeries.X + PowerSeries.C 9 * PowerSeries.X ^ 2 -
      PowerSeries.C 54 * PowerSeries.X ^ 3 := by
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h9 : PowerSeries.C (9 : ℤ) = (9 : PowerSeries ℤ) := rfl
    have h54 : PowerSeries.C (54 : ℤ) = (54 : PowerSeries ℤ) := rfl
    rw [h6, h9, h54]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3⟩ := A262415_small
  by_cases hn3 : n ≤ 3
  · interval_cases n <;> simp [F, h1, h2, h3]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hrec := A262415_rec (n - 4)
    simp only [show n - 4 + 4 = n by omega, show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 2 = n - 2 by omega, show n - 4 + 1 = n - 3 by omega] at hrec
    linarith

private lemma A262415_closed (n : ℕ) (hn : 1 ≤ n) :
    2 * A262415 n =
      if Even n then 3 ^ (n - 1) * (2 ^ (n + 3) - 2)
      else 3 ^ (n - 1) * (2 ^ (n + 3) - 4) := by
  suffices h : ∀ k : ℕ,
      2 * (A262415 (k + 1) : ℤ) =
        if Even (k + 1) then (3 : ℤ) ^ k * ((2 : ℤ) ^ (k + 4) - 2)
        else (3 : ℤ) ^ k * ((2 : ℤ) ^ (k + 4) - 4) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hk := h k
    have hge : 4 ≤ 2 ^ (k + 4) := by
      have : 2 ^ 2 ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rw [Nat.add_sub_cancel, show k + 1 + 3 = k + 4 by omega]
    by_cases hev : Even (k + 1)
    · rw [if_pos hev] at hk ⊢
      have hcast : ((3 ^ k * (2 ^ (k + 4) - 2) : ℕ) : ℤ) =
          (3 : ℤ) ^ k * ((2 : ℤ) ^ (k + 4) - 2) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega)]; push_cast; rfl
      omega
    · rw [if_neg hev] at hk ⊢
      have hcast : ((3 ^ k * (2 ^ (k + 4) - 4) : ℕ) : ℤ) =
          (3 : ℤ) ^ k * ((2 : ℤ) ^ (k + 4) - 4) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega)]; push_cast; rfl
      omega
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2, h3⟩ := A262415_small
    rcases k with _ | _ | _ | m
    · simp [h1]
    · simp [h2]
    · have ho3 : ¬ Even 3 := by decide
      simp [h3, ho3]
    · have hrec := A262415_rec m
      have ih2 := ih (m + 2) (by omega)
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      rw [show m + 3 + 1 = m + 4 by omega, hrec]
      by_cases hev : Even (m + 4)
      · have h3o : ¬ Even (m + 3) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2e : Even (m + 2) := by rw [Nat.even_iff] at hev ⊢; omega
        have h1o : ¬ Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
        rw [if_pos hev]
        rw [show m + 2 + 1 = m + 3 by omega, if_neg h3o] at ih2
        rw [show m + 1 + 1 = m + 2 by omega, if_pos h2e] at ih1
        rw [if_neg h1o] at ih0
        have hp3 : (3 : ℤ) ^ (m + 3) = 27 * (3 : ℤ) ^ m := by rw [pow_add]; ring
        have hp2 : (3 : ℤ) ^ (m + 2) = 9 * (3 : ℤ) ^ m := by rw [pow_add]; ring
        have hp1 : (3 : ℤ) ^ (m + 1) = 3 * (3 : ℤ) ^ m := by rw [pow_add]; ring
        have hq3 : (2 : ℤ) ^ (m + 3 + 4) = 8 * (2 : ℤ) ^ (m + 4) := by
          rw [show m + 3 + 4 = (m + 4) + 3 by omega, pow_add]; ring
        have hq2 : (2 : ℤ) ^ (m + 2 + 4) = 4 * (2 : ℤ) ^ (m + 4) := by
          rw [show m + 2 + 4 = (m + 4) + 2 by omega, pow_add]; ring
        have hq1 : (2 : ℤ) ^ (m + 1 + 4) = 2 * (2 : ℤ) ^ (m + 4) := by
          rw [show m + 1 + 4 = (m + 4) + 1 by omega, pow_add]; ring
        rw [hp3, hq3]; rw [hp2, hq2] at ih2; rw [hp1, hq1] at ih1
        linarith
      · have h3e : Even (m + 3) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2o : ¬ Even (m + 2) := by rw [Nat.even_iff] at hev ⊢; omega
        have h1e : Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
        rw [if_neg hev]
        rw [show m + 2 + 1 = m + 3 by omega, if_pos h3e] at ih2
        rw [show m + 1 + 1 = m + 2 by omega, if_neg h2o] at ih1
        rw [if_pos h1e] at ih0
        have hp3 : (3 : ℤ) ^ (m + 3) = 27 * (3 : ℤ) ^ m := by rw [pow_add]; ring
        have hp2 : (3 : ℤ) ^ (m + 2) = 9 * (3 : ℤ) ^ m := by rw [pow_add]; ring
        have hp1 : (3 : ℤ) ^ (m + 1) = 3 * (3 : ℤ) ^ m := by rw [pow_add]; ring
        have hq3 : (2 : ℤ) ^ (m + 3 + 4) = 8 * (2 : ℤ) ^ (m + 4) := by
          rw [show m + 3 + 4 = (m + 4) + 3 by omega, pow_add]; ring
        have hq2 : (2 : ℤ) ^ (m + 2 + 4) = 4 * (2 : ℤ) ^ (m + 4) := by
          rw [show m + 2 + 4 = (m + 4) + 2 by omega, pow_add]; ring
        have hq1 : (2 : ℤ) ^ (m + 1 + 4) = 2 * (2 : ℤ) ^ (m + 4) := by
          rw [show m + 1 + 4 = (m + 4) + 1 by omega, pow_add]; ring
        rw [hp3, hq3]; rw [hp2, hq2] at ih2; rw [hp1, hq1] at ih1
        linarith

end OMA.P_oeis_a262415

theorem OMA.solution : type_of% @OMA.S_oeis_a262415.main :=
  ⟨OMA.P_oeis_a262415.A262415_gf, OMA.P_oeis_a262415.A262415_closed⟩
