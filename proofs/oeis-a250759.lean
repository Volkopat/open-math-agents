import OMAStatements.S_oeis_a250759
import Mathlib

namespace OMA.S_oeis_a250759

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

open PowerSeries in
theorem gf_gen (b : ℕ → ℚ) (m q : ℕ) (d p : ℕ → ℚ) (D N : PowerSeries ℚ)
    (hD : D = ∑ j ∈ Finset.range (m + 1), C (d j) * X ^ j)
    (hN : N = ∑ j ∈ Finset.range (q + 1), C (p j) * X ^ j) (hD0 : d 0 ≠ 0) (hp : ∀ n, q < n → p n = 0)
    (hb : ∀ n, ∑ j ∈ Finset.range (m + 1), d j * (if j ≤ n then b (n - j) else 0) =
      if n ≤ q then p n else 0) :
    mk b = N * D⁻¹ := by
  have hc : constantCoeff D ≠ 0 := by
    rw [hD]
    simp only [map_sum, map_mul, map_pow, constantCoeff_C, constantCoeff_X]
    rw [Finset.sum_eq_single 0]
    · simpa using hD0
    · intro j _ hj; simp [hj]
    · intro h; exfalso; exact h (by simp)
  rw [eq_mul_inv_iff_mul_eq hc, hD, hN]
  ext n
  simp only [Finset.mul_sum, map_sum]
  have : ∀ j ∈ Finset.range (m + 1), coeff n (mk b * (C (d j) * X ^ j)) =
      d j * (if j ≤ n then b (n - j) else 0) := by
    intro j _
    rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']
    simp
  rw [Finset.sum_congr rfl this, hb n]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n]
  · by_cases h : n ≤ q
    · simp [h]
    · simp [h, hp n (by omega)]
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; simp at h; simp [hp n (by omega)]

def Rel : (Fin 5 → Fin 3) → (Fin 5 → Fin 3) → Prop :=
  fun u v => ∀ i : Fin 4, CellOK (((u i.castSucc) : ℕ) : ℤ) (((v i.castSucc) : ℕ) : ℤ) (((u i.succ) : ℕ) : ℤ) (((v i.succ) : ℕ) : ℤ)

instance : DecidableRel Rel := fun u v => by unfold Rel CellOK; infer_instance

theorem a_eq (n : ℕ) : a n = ∑ s, V Rel n s := by
  unfold a
  have e : {x : Fin 5 → Fin (n + 1) → Fin 3 // ∀ i : Fin 4, ∀ j : Fin n,
      CellOK (((x i.castSucc j.castSucc) : ℕ) : ℤ) (((x i.castSucc j.succ) : ℕ) : ℤ) (((x i.succ j.castSucc) : ℕ) : ℤ) (((x i.succ j.succ) : ℕ) : ℤ)} ≃ Chain Rel n :=
    Equiv.subtypeEquiv (Equiv.piComm _) (by
      intro x
      constructor
      · intro h j i
        exact h i j
      · intro h i j
        exact h j i)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, cardChain]

def ix (s : Fin 5 → Fin 3) : ℕ := ∑ i : Fin 5, (s i).val * 3 ^ i.val

def tb0 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def tb1 : List ℕ := [21, 25, 21, 18, 22, 18, 10, 10, 10, 15, 18, 15, 15, 18, 15, 9, 9, 9, 6, 6, 6, 6, 6, 6, 6, 6, 6, 11, 13, 11, 11, 13, 11, 7, 7, 7, 11, 13, 11, 11, 13, 11, 7, 7, 7, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 7, 6, 6, 7, 6, 4, 4, 4, 6, 7, 6, 6, 7, 6, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 7, 6, 6, 7, 6, 4, 4, 4, 6, 7, 6, 6, 7, 6, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def tb2 : List ℕ := [67, 83, 67, 56, 70, 56, 28, 28, 28, 45, 55, 45, 45, 55, 45, 25, 25, 25, 15, 15, 15, 15, 15, 15, 15, 15, 15, 30, 36, 30, 30, 36, 30, 18, 18, 18, 30, 36, 30, 30, 36, 30, 18, 18, 18, 12, 12, 12, 12, 12, 12, 12, 12, 12, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 11, 13, 11, 11, 13, 11, 7, 7, 7, 11, 13, 11, 11, 13, 11, 7, 7, 7, 5, 5, 5, 5, 5, 5, 5, 5, 5, 11, 13, 11, 11, 13, 11, 7, 7, 7, 11, 13, 11, 11, 13, 11, 7, 7, 7, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def tb3 : List ℕ := [139, 175, 139, 115, 145, 115, 55, 55, 55, 91, 112, 91, 91, 112, 91, 49, 49, 49, 28, 28, 28, 28, 28, 28, 28, 28, 28, 58, 70, 58, 58, 70, 58, 34, 34, 34, 58, 70, 58, 58, 70, 58, 34, 34, 34, 22, 22, 22, 22, 22, 22, 22, 22, 22, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 16, 19, 16, 16, 19, 16, 10, 10, 10, 16, 19, 16, 16, 19, 16, 10, 10, 10, 7, 7, 7, 7, 7, 7, 7, 7, 7, 16, 19, 16, 16, 19, 16, 10, 10, 10, 16, 19, 16, 16, 19, 16, 10, 10, 10, 7, 7, 7, 7, 7, 7, 7, 7, 7, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def tbl (k : ℕ) : List ℕ := [tb0, tb1, tb2, tb3].getD k []

theorem split2 {n : ℕ} {α : Type} (P : (Fin (n + 2) → α) → Prop) (h : ∀ a b (s' : Fin n → α), P (Fin.cons a (Fin.cons b s'))) : ∀ s, P s := by
  intro s
  induction s using Fin.consCases with
  | _ a s =>
    induction s using Fin.consCases with
    | _ b s' => exact h a b s'

theorem Vstep (n : ℕ) (s : Fin 5 → Fin 3) : V Rel (n + 1) s = ∑ t, if Rel s t then V Rel n t else 0 := by simp [V]

theorem L0_c0_0 : ∀ s' : Fin 3 → Fin 3, V Rel 0 (Fin.cons (0 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb0.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c0_1 : ∀ s' : Fin 3 → Fin 3, V Rel 0 (Fin.cons (0 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb0.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c0_2 : ∀ s' : Fin 3 → Fin 3, V Rel 0 (Fin.cons (0 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb0.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c1_0 : ∀ s' : Fin 3 → Fin 3, V Rel 0 (Fin.cons (1 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb0.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c1_1 : ∀ s' : Fin 3 → Fin 3, V Rel 0 (Fin.cons (1 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb0.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c1_2 : ∀ s' : Fin 3 → Fin 3, V Rel 0 (Fin.cons (1 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb0.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c2_0 : ∀ s' : Fin 3 → Fin 3, V Rel 0 (Fin.cons (2 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb0.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c2_1 : ∀ s' : Fin 3 → Fin 3, V Rel 0 (Fin.cons (2 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb0.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0_c2_2 : ∀ s' : Fin 3 → Fin 3, V Rel 0 (Fin.cons (2 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb0.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'

  revert s'
  decide +kernel

theorem L0 : ∀ s : Fin 5 → Fin 3, V Rel 0 s = tb0.getD (ix s) 0 := by
  refine split2 (n := 3) (fun s => V Rel 0 s = tb0.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L0_c0_0
  · exact L0_c0_1
  · exact L0_c0_2
  · exact L0_c1_0
  · exact L0_c1_1
  · exact L0_c1_2
  · exact L0_c2_0
  · exact L0_c2_1
  · exact L0_c2_2

theorem L1_c0_0 : ∀ s' : Fin 3 → Fin 3, V Rel 1 (Fin.cons (0 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb1.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c0_1 : ∀ s' : Fin 3 → Fin 3, V Rel 1 (Fin.cons (0 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb1.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c0_2 : ∀ s' : Fin 3 → Fin 3, V Rel 1 (Fin.cons (0 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb1.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c1_0 : ∀ s' : Fin 3 → Fin 3, V Rel 1 (Fin.cons (1 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb1.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c1_1 : ∀ s' : Fin 3 → Fin 3, V Rel 1 (Fin.cons (1 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb1.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c1_2 : ∀ s' : Fin 3 → Fin 3, V Rel 1 (Fin.cons (1 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb1.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c2_0 : ∀ s' : Fin 3 → Fin 3, V Rel 1 (Fin.cons (2 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb1.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c2_1 : ∀ s' : Fin 3 → Fin 3, V Rel 1 (Fin.cons (2 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb1.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1_c2_2 : ∀ s' : Fin 3 → Fin 3, V Rel 1 (Fin.cons (2 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb1.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L0]
  revert s'
  decide +kernel

theorem L1 : ∀ s : Fin 5 → Fin 3, V Rel 1 s = tb1.getD (ix s) 0 := by
  refine split2 (n := 3) (fun s => V Rel 1 s = tb1.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L1_c0_0
  · exact L1_c0_1
  · exact L1_c0_2
  · exact L1_c1_0
  · exact L1_c1_1
  · exact L1_c1_2
  · exact L1_c2_0
  · exact L1_c2_1
  · exact L1_c2_2

theorem L2_c0_0 : ∀ s' : Fin 3 → Fin 3, V Rel 2 (Fin.cons (0 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb2.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c0_1 : ∀ s' : Fin 3 → Fin 3, V Rel 2 (Fin.cons (0 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb2.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c0_2 : ∀ s' : Fin 3 → Fin 3, V Rel 2 (Fin.cons (0 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb2.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c1_0 : ∀ s' : Fin 3 → Fin 3, V Rel 2 (Fin.cons (1 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb2.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c1_1 : ∀ s' : Fin 3 → Fin 3, V Rel 2 (Fin.cons (1 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb2.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c1_2 : ∀ s' : Fin 3 → Fin 3, V Rel 2 (Fin.cons (1 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb2.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c2_0 : ∀ s' : Fin 3 → Fin 3, V Rel 2 (Fin.cons (2 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb2.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c2_1 : ∀ s' : Fin 3 → Fin 3, V Rel 2 (Fin.cons (2 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb2.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2_c2_2 : ∀ s' : Fin 3 → Fin 3, V Rel 2 (Fin.cons (2 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb2.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L1]
  revert s'
  decide +kernel

theorem L2 : ∀ s : Fin 5 → Fin 3, V Rel 2 s = tb2.getD (ix s) 0 := by
  refine split2 (n := 3) (fun s => V Rel 2 s = tb2.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L2_c0_0
  · exact L2_c0_1
  · exact L2_c0_2
  · exact L2_c1_0
  · exact L2_c1_1
  · exact L2_c1_2
  · exact L2_c2_0
  · exact L2_c2_1
  · exact L2_c2_2

theorem L3_c0_0 : ∀ s' : Fin 3 → Fin 3, V Rel 3 (Fin.cons (0 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb3.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c0_1 : ∀ s' : Fin 3 → Fin 3, V Rel 3 (Fin.cons (0 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb3.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c0_2 : ∀ s' : Fin 3 → Fin 3, V Rel 3 (Fin.cons (0 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb3.getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c1_0 : ∀ s' : Fin 3 → Fin 3, V Rel 3 (Fin.cons (1 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb3.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c1_1 : ∀ s' : Fin 3 → Fin 3, V Rel 3 (Fin.cons (1 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb3.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c1_2 : ∀ s' : Fin 3 → Fin 3, V Rel 3 (Fin.cons (1 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb3.getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c2_0 : ∀ s' : Fin 3 → Fin 3, V Rel 3 (Fin.cons (2 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3) = tb3.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c2_1 : ∀ s' : Fin 3 → Fin 3, V Rel 3 (Fin.cons (2 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3) = tb3.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3_c2_2 : ∀ s' : Fin 3 → Fin 3, V Rel 3 (Fin.cons (2 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3) = tb3.getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 := by
  intro s'
  rw [Vstep]
  simp only [L2]
  revert s'
  decide +kernel

theorem L3 : ∀ s : Fin 5 → Fin 3, V Rel 3 s = tb3.getD (ix s) 0 := by
  refine split2 (n := 3) (fun s => V Rel 3 s = tb3.getD (ix s) 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact L3_c0_0
  · exact L3_c0_1
  · exact L3_c0_2
  · exact L3_c1_0
  · exact L3_c1_1
  · exact L3_c1_2
  · exact L3_c2_0
  · exact L3_c2_1
  · exact L3_c2_2

theorem key : ∀ j, j ≤ 3 → ∀ s : Fin 5 → Fin 3, V Rel j s = (tbl j).getD (ix s) 0 := by
  intro j hj s
  interval_cases j
  · exact L0 s
  · exact L1 s
  · exact L2 s
  · exact L3 s
def cc : ℕ → ℤ := fun j => [(-1 : ℤ), (3 : ℤ), (-3 : ℤ), (1 : ℤ)].getD j 0

theorem h0chk_c0_0 : ∀ s' : Fin 3 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c0_1 : ∀ s' : Fin 3 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c0_2 : ∀ s' : Fin 3 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix (Fin.cons (0 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c1_0 : ∀ s' : Fin 3 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c1_1 : ∀ s' : Fin 3 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c1_2 : ∀ s' : Fin 3 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix (Fin.cons (1 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c2_0 : ∀ s' : Fin 3 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (0 : Fin 3) s') : Fin 5 → Fin 3)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c2_1 : ∀ s' : Fin 3 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (1 : Fin 3) s') : Fin 5 → Fin 3)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk_c2_2 : ∀ s' : Fin 3 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix (Fin.cons (2 : Fin 3) (Fin.cons (2 : Fin 3) s') : Fin 5 → Fin 3)) 0 : ℕ) : ℤ) = 0 := by
  intro s'

  revert s'
  decide +kernel

theorem h0chk : ∀ s : Fin 5 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix s) 0 : ℕ) : ℤ) = 0 := by
  refine split2 (n := 3) (fun s => ∑ j ∈ Finset.range 4, cc j * (((tbl j).getD (ix s) 0 : ℕ) : ℤ) = 0) ?_
  intro a b
  fin_cases a <;> fin_cases b
  · exact h0chk_c0_0
  · exact h0chk_c0_1
  · exact h0chk_c0_2
  · exact h0chk_c1_0
  · exact h0chk_c1_1
  · exact h0chk_c1_2
  · exact h0chk_c2_0
  · exact h0chk_c2_1
  · exact h0chk_c2_2

theorem h0 : ∀ s : Fin 5 → Fin 3, ∑ j ∈ Finset.range 4, cc j * (V Rel j s : ℤ) = 0 := by
  intro s
  rw [Finset.sum_congr rfl (fun j hj => by rw [key j (by have := Finset.mem_range.1 hj; omega) s])]
  exact h0chk s

theorem hrec (k : ℕ) : (a (k + 3) : ℤ) = (1 : ℤ) * a (k + 0) + (-3 : ℤ) * a (k + 1) + (3 : ℤ) * a (k + 2) := by
  have h := rec_total Rel 3 cc h0 k
  have e0 : cc 0 = -1 := rfl
  have e1 : cc 1 = 3 := rfl
  have e2 : cc 2 = -3 := rfl
  have e3 : cc 3 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

theorem v1 : a 1 = 1029 := by
  rw [a_eq]
  simp only [L1]
  decide +kernel
theorem v2 : a 2 = 2361 := by
  rw [a_eq]
  simp only [L2]
  decide +kernel
theorem v3 : a 3 = 4239 := by
  rw [a_eq]
  simp only [L3]
  decide +kernel

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 273 * (n : ℚ) ^ 2 + 513 * (n : ℚ) + 243 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 3
    · interval_cases n
      · rw [v1]; norm_num
      · rw [v2]; norm_num
      · rw [v3]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have r : (a (k + 3) : ℚ) = (1 : ℚ) * a (k + 0) + (-3 : ℚ) * a (k + 1) + (3 : ℚ) * a (k + 2) := by exact_mod_cast hrec k
      have i0 := ih (k + 0) (by omega) (by omega)
      have i1 := ih (k + 1) (by omega) (by omega)
      have i2 := ih (k + 2) (by omega) (by omega)
      rw [r, i0, i1, i2]
      push_cast
      ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 3 3 (fun j => [(1 : ℚ), (-3 : ℚ), (3 : ℚ), (-1 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (1029 : ℚ), (-726 : ℚ), (243 : ℚ)].getD j 0)
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · norm_num
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | k <;> simp_all
  · intro n
    rcases n with _ | _ | _ | _ | k
    · simp [Finset.sum_range_succ]
    · simp [Finset.sum_range_succ, v1, v2, v3] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have c0 := closed (k + 4) (by omega)
      have c1 := closed (k + 3) (by omega)
      have c2 := closed (k + 2) (by omega)
      have c3 := closed (k + 1) (by omega)
      simp [c0, c1, c2, c3]
      ring

end OMA.S_oeis_a250759

open OMA.S_oeis_a250759 in
theorem OMA.solution : type_of% @OMA.S_oeis_a250759.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have e1 : k + 4 - 1 = k + 3 := by omega
    have e2 : k + 4 - 2 = k + 2 := by omega
    have e3 : k + 4 - 3 = k + 1 := by omega
    rw [e1, e2, e3]
    have c0 := closed (k + 4) (by omega)
    have c1 := closed (k + 3) (by omega)
    have c2 := closed (k + 2) (by omega)
    have c3 := closed (k + 1) (by omega)
    have hq : ((a (k + 4) : ℤ) : ℚ) = (((3 : ℤ) * (a (k + 3) : ℤ) + (-3 : ℤ) * (a (k + 2) : ℤ) + (1 : ℤ) * (a (k + 1) : ℤ) : ℤ) : ℚ) := by
      push_cast; rw [c0, c1, c2, c3]; push_cast; ring
    have hz : (a (k + 4) : ℤ) = (3 : ℤ) * (a (k + 3) : ℤ) + (-3 : ℤ) * (a (k + 2) : ℤ) + (1 : ℤ) * (a (k + 1) : ℤ) := by exact_mod_cast hq
    linarith
  · exact OMA.S_oeis_a250759.gf
  · intro n hn
    exact OMA.S_oeis_a250759.closed n (by omega)
