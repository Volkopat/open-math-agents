import OMAStatements.S_oeis_a250893
import Mathlib

namespace OMA.S_oeis_a250893

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

instance : DecidableRel BlockOK := fun u v => by unfold BlockOK; infer_instance

theorem a_eq (n : ℕ) : a n = ∑ s, V BlockOK n s := by
  unfold a
  have e : {x : Fin (n + 1) → Fin 4 → Fin 3 // Good x} ≃ Chain BlockOK n :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro x
      constructor
      · intro h i
        exact h i.castSucc i.succ (by simp)
      · intro h i j hij
        obtain ⟨k, hk⟩ : ∃ k : Fin n, k.castSucc = i := ⟨⟨i, by omega⟩, rfl⟩
        subst hk
        have : j = k.succ := Fin.ext (by simp [hij])
        subst this
        exact h k)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, cardChain]

abbrev Rel := BlockOK

def cc : ℕ → ℤ := fun j => [(0 : ℤ), (0 : ℤ), (0 : ℤ), (-24 : ℤ), (116 : ℤ), (-234 : ℤ), (255 : ℤ), (-162 : ℤ), (60 : ℤ), (-12 : ℤ), (1 : ℤ)].getD j 0

theorem hrec (k : ℕ) : (a (k + 10) : ℤ) = (24 : ℤ) * a (k + 3) + (-116 : ℤ) * a (k + 4) + (234 : ℤ) * a (k + 5) + (-255 : ℤ) * a (k + 6) + (162 : ℤ) * a (k + 7) + (-60 : ℤ) * a (k + 8) + (12 : ℤ) * a (k + 9) := by
  have h := rec_total Rel 10 cc (by decide +kernel) k
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = 0 := rfl
  have e2 : cc 2 = 0 := rfl
  have e3 : cc 3 = -24 := rfl
  have e4 : cc 4 = 116 := rfl
  have e5 : cc 5 = -234 := rfl
  have e6 : cc 6 = 255 := rfl
  have e7 : cc 7 = -162 := rfl
  have e8 : cc 8 = 60 := rfl
  have e9 : cc 9 = -12 := rfl
  have e10 : cc 10 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h
  linarith

theorem v1 : a 1 = 403 := by rw [a_eq]; decide +kernel
theorem v2 : a 2 = 1325 := by rw [a_eq]; decide +kernel
theorem v3 : a 3 = 4388 := by rw [a_eq]; decide +kernel
theorem v4 : a 4 = 14196 := by rw [a_eq]; decide +kernel
theorem v5 : a 5 = 44525 := by rw [a_eq]; decide +kernel
theorem v6 : a 6 = 136509 := by rw [a_eq]; decide +kernel
theorem v7 : a 7 = 412006 := by rw [a_eq]; decide +kernel
theorem v8 : a 8 = 1231112 := by rw [a_eq]; decide +kernel
theorem v9 : a 9 = 3657629 := by rw [a_eq]; decide +kernel

theorem closed (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = (-8 * (179 + 223 * (2 : ℚ) ^ n - 25 * (3 : ℚ) ^ (3 + n)) + (1104 - 845 * (2 : ℚ) ^ n) * (n : ℚ) + (32 + 375 * (2 : ℚ) ^ n) * (n : ℚ) ^ 2) / 32 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 9
    · interval_cases n
      · rw [v3]; norm_num
      · rw [v4]; norm_num
      · rw [v5]; norm_num
      · rw [v6]; norm_num
      · rw [v7]; norm_num
      · rw [v8]; norm_num
      · rw [v9]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
      have r : (a (k + 10) : ℚ) = (24 : ℚ) * a (k + 3) + (-116 : ℚ) * a (k + 4) + (234 : ℚ) * a (k + 5) + (-255 : ℚ) * a (k + 6) + (162 : ℚ) * a (k + 7) + (-60 : ℚ) * a (k + 8) + (12 : ℚ) * a (k + 9) := by exact_mod_cast hrec k
      have i3 := ih (k + 3) (by omega) (by omega)
      have i4 := ih (k + 4) (by omega) (by omega)
      have i5 := ih (k + 5) (by omega) (by omega)
      have i6 := ih (k + 6) (by omega) (by omega)
      have i7 := ih (k + 7) (by omega) (by omega)
      have i8 := ih (k + 8) (by omega) (by omega)
      have i9 := ih (k + 9) (by omega) (by omega)
      rw [r, i3, i4, i5, i6, i7, i8, i9]
      push_cast
      ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 7 9 (fun j => [(1 : ℚ), (-12 : ℚ), (60 : ℚ), (-162 : ℚ), (255 : ℚ), (-234 : ℚ), (116 : ℚ), (-24 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (403 : ℚ), (-3511 : ℚ), (12668 : ℚ), (-24246 : ℚ), (25568 : ℚ), (-13314 : ℚ), (1284 : ℚ), (1746 : ℚ), (-594 : ℚ)].getD j 0)
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · norm_num
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp_all
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · simp [Finset.sum_range_succ]
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have c0 := closed (k + 10) (by omega)
      have c1 := closed (k + 9) (by omega)
      have c2 := closed (k + 8) (by omega)
      have c3 := closed (k + 7) (by omega)
      have c4 := closed (k + 6) (by omega)
      have c5 := closed (k + 5) (by omega)
      have c6 := closed (k + 4) (by omega)
      have c7 := closed (k + 3) (by omega)
      simp [c0, c1, c2, c3, c4, c5, c6, c7]
      ring

end OMA.S_oeis_a250893

theorem OMA.solution : type_of% @OMA.S_oeis_a250893.main := by
  refine ⟨?_, OMA.S_oeis_a250893.gf, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have e1 : k + 10 - 1 = k + 9 := by omega
    have e2 : k + 10 - 2 = k + 8 := by omega
    have e3 : k + 10 - 3 = k + 7 := by omega
    have e4 : k + 10 - 4 = k + 6 := by omega
    have e5 : k + 10 - 5 = k + 5 := by omega
    have e6 : k + 10 - 6 = k + 4 := by omega
    have e7 : k + 10 - 7 = k + 3 := by omega
    rw [e1, e2, e3, e4, e5, e6, e7]
    linarith [OMA.S_oeis_a250893.hrec k]
  · intro n hn
    exact OMA.S_oeis_a250893.closed n (by omega)
