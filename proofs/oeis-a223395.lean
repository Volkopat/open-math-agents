import OMAStatements.S_oeis_a223395
import Mathlib

namespace OMA.S_oeis_a223395

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


def Rel : Fin 16 → Fin 16 → Prop := Adj
instance : DecidableRel Rel := fun u v => by unfold Rel Adj; infer_instance

theorem a_eq (n : ℕ) : a (n + 1) = ∑ s, V Rel n s := by
  unfold a
  have e : {x : Fin (n + 1) → Fin 1 → Fin 16 // ∀ i : Fin (n + 1), ∀ h : (i : ℕ) + 1 < n + 1,
      Adj (x i 0) (x ⟨(i : ℕ) + 1, h⟩ 0)} ≃ Chain Rel n :=
    { toFun := fun x => ⟨fun i => x.1 i 0, fun i => by
        exact x.2 i.castSucc (by simp)⟩
      invFun := fun y => ⟨fun i _ => y.1 i, fun i h => by
        exact y.2 ⟨i, by omega⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext i j
        have : j = 0 := Subsingleton.elim _ _
        subst this; rfl
      right_inv := by intro y; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, cardChain]

def cc : ℕ → ℤ := fun j => [(4 : ℤ), -2, -3, 1].getD j 0

theorem hrec (k : ℕ) : (a (k + 4) : ℤ) = 3 * a (k + 3) + 2 * a (k + 2) - 4 * a (k + 1) := by
  have h := rec_total Rel 3 cc (by decide +kernel) k
  have e0 : cc 0 = 4 := rfl
  have e1 : cc 1 = -2 := rfl
  have e2 : cc 2 = -3 := rfl
  have e3 : cc 3 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, Nat.add_zero] at h
  have c0 : (a (k + 1) : ℤ) = ∑ s, (V Rel k s : ℤ) := by rw [a_eq k]; push_cast; rfl
  have c1 : (a (k + 2) : ℤ) = ∑ s, (V Rel (k + 1) s : ℤ) := by rw [a_eq (k + 1)]; push_cast; rfl
  have c2 : (a (k + 3) : ℤ) = ∑ s, (V Rel (k + 2) s : ℤ) := by rw [a_eq (k + 2)]; push_cast; rfl
  have c3 : (a (k + 4) : ℤ) = ∑ s, (V Rel (k + 3) s : ℤ) := by rw [a_eq (k + 3)]; push_cast; rfl
  rw [c0, c1, c2, c3]
  linarith

theorem v1 : a 1 = 16 := by rw [a_eq]; decide +kernel
theorem v2 : a 2 = 48 := by rw [a_eq]; decide +kernel
theorem v3 : a 3 = 152 := by rw [a_eq]; decide +kernel

theorem root (t : ℝ) (h : t ^ 2 = 2 * t + 4) (n : ℕ) :
    t ^ (n + 4) = 3 * t ^ (n + 3) + 2 * t ^ (n + 2) - 4 * t ^ (n + 1) := by
  have : t ^ (n + 4) - (3 * t ^ (n + 3) + 2 * t ^ (n + 2) - 4 * t ^ (n + 1)) = 0 := by
    linear_combination (t ^ (n + 1) * (t - 1)) * h
  linarith

noncomputable def rhs (n : ℕ) : ℝ :=
  (8 + (11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ n + (1 + Real.sqrt 5) ^ n * (11 + 5 * Real.sqrt 5)) / 5

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = rhs n := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have key : ∀ k : ℕ, (a (k + 1) : ℝ) = rhs (k + 1) ∧ (a (k + 2) : ℝ) = rhs (k + 2) ∧
      (a (k + 3) : ℝ) = rhs (k + 3) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · rw [v1]; unfold rhs; push_cast; linear_combination (-2) * hs
      · rw [v2]; unfold rhs; push_cast; linear_combination (-42/5) * hs
      · rw [v3]; unfold rhs; push_cast; linear_combination (-(2 * Real.sqrt 5 ^ 2 + 146/5)) * hs
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨h2, h3, ?_⟩
      have r1 := root (1 + Real.sqrt 5) (by linear_combination hs) k
      have r2 := root (1 - Real.sqrt 5) (by linear_combination hs) k
      have h' : (a (k + 4) : ℝ) = 3 * a (k + 3) + 2 * a (k + 2) - 4 * a (k + 1) := by
        exact_mod_cast hrec k
      rw [show k + 1 + 3 = k + 4 by ring, h', h1, h2, h3]
      unfold rhs
      linear_combination (-((11 - 5 * Real.sqrt 5) / 5)) * r2 - ((11 + 5 * Real.sqrt 5) / 5) * r1
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (key k).1

theorem gfq : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  have hq : ∀ k : ℕ, (a (k + 4) : ℚ) = 3 * a (k + 3) + 2 * a (k + 2) - 4 * a (k + 1) := by
    intro k; exact_mod_cast hrec k
  have w1 : (a 1 : ℚ) = 16 := by rw [v1]; norm_num
  have w2 : (a 2 : ℚ) = 48 := by rw [v2]; norm_num
  have w3 : (a 3 : ℚ) = 152 := by rw [v3]; norm_num
  apply gf_gen _ 3 3 (fun j => [(1 : ℚ), -3, -2, 4].getD j 0) (fun j => [(0 : ℚ), 16, 0, -24].getD j 0)
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
    · simp [Finset.sum_range_succ, w1] <;> norm_num
    · simp [Finset.sum_range_succ, w1, w2] <;> norm_num
    · simp [Finset.sum_range_succ, w1, w2, w3]; norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have := hq k
      simp [List.getD_eq_getElem?_getD]
      linarith

end OMA.S_oeis_a223395

theorem OMA.solution : type_of% @OMA.S_oeis_a223395.main := by
  refine ⟨?_, OMA.S_oeis_a223395.gfq, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have := OMA.S_oeis_a223395.hrec k
    simpa [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega] using this
  · intro n hn
    exact OMA.S_oeis_a223395.closed n hn
