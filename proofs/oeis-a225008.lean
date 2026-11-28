import OMAStatements.S_oeis_a225008
import Mathlib

namespace OMA.S_oeis_a225008

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

def RowsOK (u : Fin 6 → Fin 2) : Prop :=
  ∀ (j₁ j₂ j₃ : Fin 6), j₁ < j₂ → j₂ < j₃ → ¬ (u j₂ < u j₁ ∧ u j₂ < u j₃)

instance (u : Fin 6 → Fin 2) : Decidable (RowsOK u) := by unfold RowsOK; infer_instance

abbrev St := {u : Fin 6 → Fin 2 // RowsOK u}

def Rel : St → St → Prop := fun u v => ∀ j, u.1 j ≤ v.1 j

instance : DecidableRel Rel := fun u v => by unfold Rel; infer_instance

def eqv (n : ℕ) : {x : Fin (n + 1) → Fin 6 → Fin 2 // good x} ≃ Chain Rel n where
  toFun x := ⟨fun i => ⟨x.1 i, x.2.1 i⟩, fun i j => x.2.2 i.castSucc i.succ j (by simp)⟩
  invFun y := ⟨fun i j => (y.1 i).1 j, ⟨fun i => (y.1 i).2, fun i i' j h => by
    have := y.2 ⟨i.val, by omega⟩ j
    have e1 : (Fin.castSucc ⟨i.val, by omega⟩ : Fin (n + 1)) = i := Fin.ext rfl
    have e2 : (Fin.succ ⟨i.val, by omega⟩ : Fin (n + 1)) = i' := Fin.ext (by simp [h])
    rw [e1, e2] at this
    exact this⟩⟩
  left_inv x := rfl
  right_inv y := rfl

theorem a_eq (n : ℕ) : a (n + 1) = ∑ s, V Rel n s := by
  unfold a
  rw [← Fintype.card_subtype, Fintype.card_congr (eqv n), cardChain]

def cc : ℕ → ℤ := fun j => [(-1 : ℤ), 7, -21, 35, -35, 21, -7, 1].getD j 0

theorem hrec (k : ℕ) : (a (k + 8) : ℤ) = 7 * a (k + 7) - 21 * a (k + 6) + 35 * a (k + 5)
    - 35 * a (k + 4) + 21 * a (k + 3) - 7 * a (k + 2) + a (k + 1) := by
  have h := rec_total Rel 7 cc (by decide +kernel) k
  have e0 : cc 0 = -1 := rfl
  have e1 : cc 1 = 7 := rfl
  have e2 : cc 2 = -21 := rfl
  have e3 : cc 3 = 35 := rfl
  have e4 : cc 4 = -35 := rfl
  have e5 : cc 5 = 21 := rfl
  have e6 : cc 6 = -7 := rfl
  have e7 : cc 7 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7] at h
  have f0 : (a (k + 1) : ℤ) = ∑ s, (V Rel k s : ℤ) := by rw [show k + 1 = k + 0 + 1 from rfl, a_eq]; push_cast; rfl
  have f1 : (a (k + 2) : ℤ) = ∑ s, (V Rel (k + 1) s : ℤ) := by rw [a_eq]; push_cast; rfl
  have f2 : (a (k + 3) : ℤ) = ∑ s, (V Rel (k + 2) s : ℤ) := by rw [a_eq]; push_cast; rfl
  have f3 : (a (k + 4) : ℤ) = ∑ s, (V Rel (k + 3) s : ℤ) := by rw [a_eq]; push_cast; rfl
  have f4 : (a (k + 5) : ℤ) = ∑ s, (V Rel (k + 4) s : ℤ) := by rw [a_eq]; push_cast; rfl
  have f5 : (a (k + 6) : ℤ) = ∑ s, (V Rel (k + 5) s : ℤ) := by rw [a_eq]; push_cast; rfl
  have f6 : (a (k + 7) : ℤ) = ∑ s, (V Rel (k + 6) s : ℤ) := by rw [a_eq]; push_cast; rfl
  have f7 : (a (k + 8) : ℤ) = ∑ s, (V Rel (k + 7) s : ℤ) := by rw [a_eq]; push_cast; rfl
  simp only [Nat.add_zero] at h
  linarith

theorem v1 : a 1 = 22 := by rw [a_eq]; decide +kernel
theorem v2 : a 2 = 148 := by rw [a_eq]; decide +kernel
theorem v3 : a 3 = 610 := by rw [a_eq]; decide +kernel
theorem v4 : a 4 = 1897 := by rw [a_eq]; decide +kernel
theorem v5 : a 5 = 4900 := by rw [a_eq]; decide +kernel
theorem v6 : a 6 = 11088 := by rw [a_eq]; decide +kernel
theorem v7 : a 7 = 22716 := by rw [a_eq]; decide +kernel
theorem v8 : a 8 = 43065 := by rw [a_eq]; decide +kernel

end OMA.S_oeis_a225008

open PowerSeries OMA.S_oeis_a225008 in
theorem OMA.solution : type_of% @OMA.S_oeis_a225008.main := by
  have hQ : ∀ k : ℕ, (a (k + 8) : ℚ) = 7 * a (k + 7) - 21 * a (k + 6) + 35 * a (k + 5)
      - 35 * a (k + 4) + 21 * a (k + 3) - 7 * a (k + 2) + a (k + 1) := by
    intro k
    have := hrec k
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · have hD : (1 - X : ℚ⟦X⟧) ^ 7 = ∑ j ∈ Finset.range 8, C ([(1 : ℚ), -7, 21, -35, 35, -21, 7, -1].getD j 0) * X ^ j := by
      simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
      ring
    have hN : X * (22 - 6 * X + 36 * X ^ 2 - 35 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + X ^ 6 : ℚ⟦X⟧)
        = ∑ j ∈ Finset.range 8, C ([(0 : ℚ), 22, -6, 36, -35, 21, -7, 1].getD j 0) * X ^ j := by
      simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
      ring
    have g := gf_gen (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) 7 7
      (fun j => [(1 : ℚ), -7, 21, -35, 35, -21, 7, -1].getD j 0)
      (fun j => [(0 : ℚ), 22, -6, 36, -35, 21, -7, 1].getD j 0) _ _ hD hN (by norm_num)
      (by intro n hn; simp only [List.getD_eq_getElem?_getD]; rcases n with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp_all)
      (by
        intro n
        rcases n with _ | _ | _ | _ | _ | _ | _ | _ | k
        · simp [Finset.sum_range_succ]
        · simp [Finset.sum_range_succ, v1]
        · simp [Finset.sum_range_succ, v1, v2]; norm_num
        · simp [Finset.sum_range_succ, v1, v2, v3]; norm_num
        · simp [Finset.sum_range_succ, v1, v2, v3, v4]; norm_num
        · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5]; norm_num
        · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6]; norm_num
        · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7]; norm_num
        · have h := hQ k
          simp only [Finset.sum_range_succ, Finset.sum_range_zero]
          simp
          linarith)
    have hc : constantCoeff ((1 - X : ℚ⟦X⟧) ^ 7) ≠ 0 := by simp
    rw [g, mul_assoc, PowerSeries.inv_mul_cancel _ hc, mul_one]
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    have e : ∀ j, j ≤ 7 → k + 8 - j = k + (8 - j) := fun j hj => by omega
    have h := hrec k
    simpa using h
