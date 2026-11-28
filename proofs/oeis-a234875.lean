import OMAStatements.S_oeis_a234875
import Mathlib

namespace OMA.S_oeis_a234875

section generic
variable {V : Type} [Fintype V] [DecidableEq V] (R : V → V → Prop) [DecidableRel R]

def cntG : ℕ → V → ℤ
  | 0, _ => 1
  | k + 1, v => ∑ w : V, if R v w then cntG k w else 0

theorem cntG_card (m : ℕ) : ∀ v : V,
    (Fintype.card {x : Fin (m + 1) → V // x 0 = v ∧ ∀ i : Fin m, R (x i.castSucc) (x i.succ)} : ℤ)
      = cntG R m v := by
  induction m with
  | zero =>
    intro v
    have : Fintype.card {x : Fin (0 + 1) → V // x 0 = v ∧ ∀ i : Fin 0, R (x i.castSucc) (x i.succ)} = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨fun _ => v, rfl, fun i => i.elim0⟩, ?_⟩
      rintro ⟨x, hx, -⟩
      apply Subtype.ext
      funext i
      have : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst this; exact hx
    rw [this]; simp [cntG]
  | succ m ih =>
    intro v
    let e : {x : Fin (m + 2) → V // x 0 = v ∧ ∀ i : Fin (m + 1), R (x i.castSucc) (x i.succ)} ≃
        Σ w : {w : V // R v w}, {y : Fin (m + 1) → V // y 0 = w.1 ∧ ∀ i : Fin m, R (y i.castSucc) (y i.succ)} :=
      { toFun := fun x => ⟨⟨x.1 1, by have h := x.2.2 0; have h0 : x.1 (Fin.castSucc 0) = v := x.2.1; rw [h0] at h; exact h⟩,
          ⟨Fin.tail x.1, rfl, fun i => by have := x.2.2 i.succ; simpa [Fin.tail] using this⟩⟩
        invFun := fun p => ⟨Fin.cons v p.2.1, by simp, by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [p.2.2.1]; exact p.1.2
          · simpa using p.2.2.2 j⟩
        left_inv := by
          rintro ⟨x, hx, -⟩
          apply Subtype.ext
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [hx]
          · simp [Fin.tail]
        right_inv := by
          rintro ⟨⟨w, hw⟩, ⟨y, hy, -⟩⟩
          have : (Fin.cons v y : Fin (m + 2) → V) 1 = w := by simpa using hy
          subst this
          simp }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    push_cast
    simp only [ih]
    rw [cntG, ← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (R v)) (by simp) (cntG R m)).symm

theorem cntG_tot (m : ℕ) :
    (Fintype.card {x : Fin (m + 1) → V // ∀ i : Fin m, R (x i.castSucc) (x i.succ)} : ℤ)
      = ∑ v : V, cntG R m v := by
  let e : {x : Fin (m + 1) → V // ∀ i : Fin m, R (x i.castSucc) (x i.succ)} ≃
      Σ v : V, {x : Fin (m + 1) → V // x 0 = v ∧ ∀ i : Fin m, R (x i.castSucc) (x i.succ)} :=
    { toFun := fun x => ⟨x.1 0, ⟨x.1, rfl, x.2⟩⟩
      invFun := fun p => ⟨p.2.1, p.2.2.2⟩
      left_inv := fun x => rfl
      right_inv := by
        rintro ⟨v, x, hx, hv⟩
        subst hx
        rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  push_cast
  exact Finset.sum_congr rfl (fun v _ => cntG_card R m v)
end generic

abbrev V := Fin 5 × Fin 5
def Rr (u v : V) : Prop := okBlock u.1 u.2 v.1 v.2
instance : DecidableRel Rr := fun u v => by unfold Rr; infer_instance

theorem a_eq (m : ℕ) (hm : 1 ≤ m) : (a m : ℤ) = ∑ v : V, cntG Rr m v := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [← cntG_tot]
  have h1 : a (n + 1) = Fintype.card {x : Fin (n + 2) → Fin 2 → Fin 5 // isValid (n + 1) x} := by
    simp only [a]; exact (Fintype.card_subtype _).symm
  rw [h1]
  congr 1
  let e : (Fin 2 → Fin 5) ≃ V := finTwoArrowEquiv (Fin 5)
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr (Equiv.refl _) e) ?_)
  intro x
  constructor
  · intro h i
    have := h i 0
    simpa [Rr, e, finTwoArrowEquiv] using this
  · intro h i j
    have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    subst hj
    have := h i
    simpa [Rr, e, finTwoArrowEquiv] using this

theorem cnt_rec : ∀ k : ℕ, ∀ v : V,
    cntG Rr (k + 5) v + 4 * cntG Rr (k + 1) v = 5 * cntG Rr (k + 3) v := by
  intro k
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    intro v
    have h1 : cntG Rr (k + 1 + 5) v = ∑ w : V, if Rr v w then cntG Rr (k + 5) w else 0 := rfl
    have h2 : cntG Rr (k + 1 + 1) v = ∑ w : V, if Rr v w then cntG Rr (k + 1) w else 0 := rfl
    have h3 : cntG Rr (k + 1 + 3) v = ∑ w : V, if Rr v w then cntG Rr (k + 3) w else 0 := rfl
    rw [h1, h2, h3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    split_ifs
    · exact ih w
    · simp

theorem a_rec (n : ℕ) (hn : 5 ≤ n) : (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have e1 : k + 5 - 2 = k + 3 := by omega
  have e2 : k + 5 - 4 = k + 1 := by omega
  rw [e1, e2, a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega)]
  have := fun v => cnt_rec k v
  have h2 : ∑ v : V, (cntG Rr (k + 5) v + 4 * cntG Rr (k + 1) v) = ∑ v : V, 5 * cntG Rr (k + 3) v :=
    Finset.sum_congr rfl (fun v _ => this v)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
  have e3 : k + 1 + 2 = k + 3 := by ring
  rw [e3]
  linarith

theorem a_vals : (a 1 : ℤ) = 32 ∧ (a 2 : ℤ) = 68 ∧ (a 3 : ℤ) = 128 ∧ (a 4 : ℤ) = 268 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [a_eq _ (by omega)] <;> decide +kernel

theorem a_closed : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) = ((if Even n then 4 else 0) + (-2 : ℚ) ^ n + 49 * 2 ^ n) / 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : n ≤ 4
    · obtain ⟨h1, h2, h3, h4⟩ := a_vals
      interval_cases n
      · have : (a 1 : ℚ) = 32 := by exact_mod_cast h1
        rw [this]; simp [Nat.even_iff]; norm_num
      · have : (a 2 : ℚ) = 68 := by exact_mod_cast h2
        rw [this]; simp [Nat.even_iff]; norm_num
      · have : (a 3 : ℚ) = 128 := by exact_mod_cast h3
        rw [this]; simp [Nat.even_iff]; norm_num
      · have : (a 4 : ℚ) = 268 := by exact_mod_cast h4
        rw [this]; simp [Nat.even_iff]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have hk : 1 ≤ k := by omega
      have h1 := a_rec (k + 4) (by omega)
      simp only [show k + 4 - 2 = k + 2 by omega, show k + 4 - 4 = k by omega] at h1
      have h1q : (a (k + 4) : ℚ) = 5 * a (k + 2) - 4 * a k := by exact_mod_cast h1
      rw [h1q, ih (k + 2) (by omega) (by omega), ih k (by omega) hk]
      have e4 : Even 4 := by decide
      have e2 : Even 2 := by decide
      have pe4 : Even (k + 4) ↔ Even k := by simp [Nat.even_add, e4]
      have pe2 : Even (k + 2) ↔ Even k := by simp [Nat.even_add, e2]
      simp only [pe4, pe2]
      split_ifs <;> ring

open PowerSeries in
theorem gf_gen (f : ℕ → ℚ) (q0 : f 0 = 0) (q1 : f 1 = 32) (q2 : f 2 = 68) (q3 : f 3 = 128)
    (q4 : f 4 = 268) (hrec : ∀ n, 5 ≤ n → f n = 5 * f (n - 2) - 4 * f (n - 4)) :
    PowerSeries.mk f * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
    4 * X * (8 + 17 * X - 8 * X ^ 2 - 18 * X ^ 3) := by
  have hP : ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) : PowerSeries ℚ) = 1 - 5 • X ^ 2 + 4 • X ^ 4 := by
    ring
  have hQ : (4 * X * (8 + 17 * X - 8 * X ^ 2 - 18 * X ^ 3) : PowerSeries ℚ) =
      32 • X + 68 • X ^ 2 - 32 • X ^ 3 - 72 • X ^ 4 := by ring
  have e : PowerSeries.mk f * (1 - 5 • X ^ 2 + 4 • X ^ 4) =
      PowerSeries.mk f - 5 • (X ^ 2 * PowerSeries.mk f)
        + 4 • (X ^ 4 * PowerSeries.mk f) := by ring
  rw [hP, hQ, e]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_X]
  rcases (by omega : n < 5 ∨ 5 ≤ n) with h | h
  · interval_cases n
    · simp [q0, q1, q2, q3, q4]
    · simp [q0, q1, q2, q3, q4] <;> norm_num
    · simp [q0, q1, q2, q3, q4] <;> norm_num
    · simp [q0, q1, q2, q3, q4] <;> norm_num
    · simp [q0, q1, q2, q3, q4] <;> norm_num
  · have hq := hrec n h
    have n1 : n ≠ 1 := by omega
    have n2 : n ≠ 2 := by omega
    have n3 : n ≠ 3 := by omega
    have n4 : n ≠ 4 := by omega
    simp [n1, n2, n3, n4, show 2 ≤ n by omega, show 4 ≤ n by omega, hq]

theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) *
    ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 + 2 * PowerSeries.X)) =
    4 * PowerSeries.X * (8 + 17 * PowerSeries.X - 8 * PowerSeries.X ^ 2 - 18 * PowerSeries.X ^ 3) := by
  obtain ⟨h1, h2, h3, h4⟩ := a_vals
  refine gf_gen (fun n => (a n : ℚ)) (by simp [a]) (by exact_mod_cast h1) (by exact_mod_cast h2)
    (by exact_mod_cast h3) (by exact_mod_cast h4) ?_
  intro n hn
  have := a_rec n hn
  exact_mod_cast this

theorem solution_aux : type_of% @OMA.S_oeis_a234875.main := by
  refine ⟨a_rec, gf, ?_, ?_⟩
  · intro n hn he
    rw [a_closed n hn]
    simp [he]
  · intro n hn ho
    rw [a_closed n hn]
    have : ¬ Even n := by simpa using ho
    simp [this]

end OMA.S_oeis_a234875

theorem OMA.solution : type_of% @OMA.S_oeis_a234875.main := OMA.S_oeis_a234875.solution_aux
