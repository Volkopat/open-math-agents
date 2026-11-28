import OMAStatements.S_oeis_a222993
import Mathlib

open OMA.S_oeis_a222993 PowerSeries

namespace P222993

abbrev Col := Fin 2 → Fin 3

def ok (r s : Col) : Prop := ((r 1 : ℕ) : ℤ) - ((r 0 : ℕ) : ℤ) ≤ ((s 1 : ℕ) : ℤ) - ((s 0 : ℕ) : ℤ)

instance (r s : Col) : Decidable (ok r s) := by unfold ok; infer_instance

def V (m : ℕ) (f : Fin (m + 1) → Col) : Prop := ∀ j : Fin m, ok (f j.castSucc) (f j.succ)

instance (m : ℕ) (f : Fin (m + 1) → Col) : Decidable (V m f) := by unfold V; infer_instance

theorem slope2 (v : Fin 2 → ℕ) : OMA.S_oeis_a222993.slope v = (v 1 : ℚ) - v 0 := by
  unfold OMA.S_oeis_a222993.slope
  rw [if_neg (by norm_num)]
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
  field_simp
  ring

theorem sum_centered (m : ℕ) (c : Fin (m + 1) → ℚ) (X Y : ℚ)
    (hX : X = (∑ i : Fin (m + 1), ((i : ℕ) : ℚ)) / ((m + 1 : ℕ) : ℚ)) :
    ∑ i : Fin (m + 1), (((i : ℕ) : ℚ) - X) * (c i - Y) =
      ∑ i : Fin (m + 1), (((i : ℕ) : ℚ) - X) * c i := by
  have h0 : ∑ i : Fin (m + 1), (((i : ℕ) : ℚ) - X) = 0 := by
    rw [Finset.sum_sub_distrib, hX]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have : ∀ i : Fin (m + 1), (((i : ℕ) : ℚ) - X) * (c i - Y) =
      (((i : ℕ) : ℚ) - X) * c i - Y * (((i : ℕ) : ℚ) - X) := fun i => by ring
  simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, h0, mul_zero, sub_zero]

theorem colslope (m : ℕ) (c0 c1 : Fin (m + 1) → ℕ)
    (hd : Monotone (fun i => (c1 i : ℚ) - c0 i)) : OMA.S_oeis_a222993.slope c0 ≤ OMA.S_oeis_a222993.slope c1 := by
  unfold OMA.S_oeis_a222993.slope
  split_ifs with h
  · exact le_rfl
  dsimp only
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  set X := (∑ i : Fin (m + 1), ((i : ℕ) : ℚ)) / ((m + 1 : ℕ) : ℚ) with hX
  rw [sum_centered m (fun i => (c0 i : ℚ)) X _ hX, sum_centered m (fun i => (c1 i : ℚ)) X _ hX]
  have hmono : Monovary (fun i : Fin (m + 1) => ((i : ℕ) : ℚ)) (fun i => (c1 i : ℚ) - c0 i) := by
    intro i j hij
    have : i ≤ j := by
      rcases le_or_gt i j with hc | hc
      · exact hc
      · exact absurd (hd hc.le) (not_le.mpr hij)
    show ((i : ℕ) : ℚ) ≤ ((j : ℕ) : ℚ)
    exact_mod_cast (Fin.le_iff_val_le_val.mp this)
  have cheb := hmono.sum_mul_sum_le_card_mul_sum
  simp only [Fintype.card_fin] at cheb
  have key : 0 ≤ ∑ i : Fin (m + 1), (((i : ℕ) : ℚ) - X) * ((c1 i : ℚ) - c0 i) := by
    have e : ∑ i : Fin (m + 1), (((i : ℕ) : ℚ) - X) * ((c1 i : ℚ) - c0 i) =
        (∑ i : Fin (m + 1), ((i : ℕ) : ℚ) * ((c1 i : ℚ) - c0 i)) -
          X * ∑ i : Fin (m + 1), ((c1 i : ℚ) - c0 i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, hX]
    have hpos : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := by positivity
    rw [div_mul_eq_mul_div, sub_nonneg, div_le_iff₀ hpos]
    push_cast at cheb ⊢
    linarith
  have e2 : ∑ i : Fin (m + 1), (((i : ℕ) : ℚ) - X) * ((c1 i : ℚ) - c0 i) =
      ∑ i : Fin (m + 1), (((i : ℕ) : ℚ) - X) * (c1 i : ℚ) -
        ∑ i : Fin (m + 1), (((i : ℕ) : ℚ) - X) * (c0 i : ℚ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

theorem good_iff (m : ℕ) (M : Fin (m + 1) → Fin 2 → Fin 3) : Good M ↔ V m M := by
  have key : ∀ j j' : Fin (m + 1), j'.val = j.val + 1 → ∃ k : Fin m, j = k.castSucc ∧ j' = k.succ := by
    intro j j' hj
    refine ⟨⟨j.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp [hj])⟩
  constructor
  · rintro ⟨hr, -⟩ j
    have := hr j.castSucc j.succ (by simp)
    rw [slope2, slope2] at this
    unfold ok
    exact_mod_cast this
  · intro hV
    refine ⟨fun i i' hii => ?_, fun j j' hjj => ?_⟩
    · obtain ⟨k, rfl, rfl⟩ := key i i' hii.symm
      have := hV k
      unfold ok at this
      rw [slope2, slope2]
      exact_mod_cast this
    · have hj : j = 0 := by ext; have := j'.isLt; omega
      have hj' : j' = 1 := by ext; have := j'.isLt; omega
      subst hj hj'
      apply colslope
      rw [Fin.monotone_iff_le_succ]
      intro k
      have := hV k
      unfold ok at this
      exact_mod_cast this

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Col) → ℕ) :
    ∑ f, F f = ∑ x : Col, ∑ g : Fin n → Col, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Col)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem V_cons (m : ℕ) (r : Col) (y : Fin (m + 1) → Col) :
    V (m + 1) (Fin.cons r y : Fin (m + 2) → Col) ↔ ok r (y 0) ∧ V m y := by
  unfold V
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]

def H (m : ℕ) (r : Col) : ℕ :=
  ∑ y : Fin m → Col, if V m (Fin.cons r y : Fin (m + 1) → Col) then 1 else 0

theorem H_succ (m : ℕ) (r : Col) :
    H (m + 1) r = ∑ s, if ok r s then H m s else 0 := by
  rw [H, sum_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : ok r s
  · rw [if_pos hs, H]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [V_cons, Fin.cons_zero, hs, true_and]
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [V_cons, Fin.cons_zero, hs]

theorem H0 (r : Col) : H 0 r = 1 := by
  rw [H, Fintype.sum_unique, if_pos]
  intro i
  exact i.elim0

def G : ℕ → Col → ℕ
  | 0, _ => 1
  | m + 1, r => ∑ s, if ok r s then G m s else 0

theorem HG (m : ℕ) : H m = G m := by
  induction m with
  | zero => funext r; rw [H0]; rfl
  | succ m ih => funext r; rw [H_succ, ih]; rfl

theorem a_eq (m : ℕ) : a (m + 1) = ∑ r, G m r := by
  unfold a T
  classical
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (good_iff m)), Fintype.card_subtype,
    Finset.card_filter, sum_cons]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← HG]
  rfl

theorem base : ∀ s, (G 5 s : ℤ) = 9 * G 4 s - 31 * G 3 s + 51 * G 2 s - 40 * G 1 s + 12 * G 0 s := by
  decide

theorem rec5 (m : ℕ) : ∀ s, (G (m + 5) s : ℤ) =
    9 * G (m + 4) s - 31 * G (m + 3) s + 51 * G (m + 2) s - 40 * G (m + 1) s + 12 * G m s := by
  induction m with
  | zero => exact base
  | succ m ih =>
    intro s
    show ((∑ t, if ok s t then G (m + 5) t else 0 : ℕ) : ℤ) =
      9 * ((∑ t, if ok s t then G (m + 4) t else 0 : ℕ) : ℤ) -
        31 * ((∑ t, if ok s t then G (m + 3) t else 0 : ℕ) : ℤ) +
        51 * ((∑ t, if ok s t then G (m + 2) t else 0 : ℕ) : ℤ) -
        40 * ((∑ t, if ok s t then G (m + 1) t else 0 : ℕ) : ℤ) +
        12 * ((∑ t, if ok s t then G m t else 0 : ℕ) : ℤ)
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · exact ih t
    · ring

def F (k : ℕ) : ℚ := (-13 - 2 ^ (7 + k) + 3 ^ (5 + k) - 2 * (1 + 2 ^ (5 + k)) * ((k : ℚ) + 1)) / 4

theorem hA0 : ∀ m, (a (m + 1) : ℚ) = F m ∧ (a (m + 2) : ℚ) = F (m + 1) ∧ (a (m + 3) : ℚ) = F (m + 2) ∧
    (a (m + 4) : ℚ) = F (m + 3) ∧ (a (m + 5) : ℚ) = F (m + 4) := by
  intro m
  induction m with
  | zero =>
    have e : ∀ k, a (k + 1) = ∑ r, G k r := a_eq
    rw [e 0, e 1, e 2, e 3, e 4]
    have v0 : ∑ r, G 0 r = 9 := by decide
    have v1 : ∑ r, G 1 r = 50 := by decide
    have v2 : ∑ r, G 2 r = 222 := by decide
    have v3 : ∑ r, G 3 r = 867 := by decide
    have v4 : ∑ r, G 4 r = 3123 := by decide
    rw [v0, v1, v2, v3, v4]
    norm_num [F]
  | succ m ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    refine ⟨h2, h3, h4, h5, ?_⟩
    have hz : (∑ r, G (m + 5) r : ℤ) = 9 * (∑ r, G (m + 4) r : ℤ) - 31 * (∑ r, G (m + 3) r : ℤ) +
        51 * (∑ r, G (m + 2) r : ℤ) - 40 * (∑ r, G (m + 1) r : ℤ) + 12 * (∑ r, G m r : ℤ) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => rec5 m t
    have hq : (∑ r, G (m + 5) r : ℚ) = 9 * (∑ r, G (m + 4) r : ℚ) - 31 * (∑ r, G (m + 3) r : ℚ) +
        51 * (∑ r, G (m + 2) r : ℚ) - 40 * (∑ r, G (m + 1) r : ℚ) + 12 * (∑ r, G m r : ℚ) := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hz
      push_cast at this
      exact this
    rw [a_eq] at h1 h2 h3 h4 h5 ⊢
    push_cast at h1 h2 h3 h4 h5 ⊢
    rw [hq, h1, h2, h3, h4, h5]
    simp only [F]
    push_cast
    ring

theorem hA (k j : ℕ) (h : j = k + 1) : (a j : ℚ) = F k := by
  subst h; exact (hA0 k).1

end P222993

open P222993 in
theorem P222993.gf : (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))) * ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X)) = X * (9 - 31 * X + 51 * X ^ 2 - 40 * X ^ 3 + 12 * X ^ 4) := by
  have v1 : (a 1 : ℚ) = 9 := by rw [hA 0 1 rfl]; norm_num [F]
  have v2 : (a 2 : ℚ) = 50 := by rw [hA 1 2 rfl]; norm_num [F]
  have v3 : (a 3 : ℚ) = 222 := by rw [hA 2 3 rfl]; norm_num [F]
  have v4 : (a 4 : ℚ) = 867 := by rw [hA 3 4 rfl]; norm_num [F]
  have v5 : (a 5 : ℚ) = 3123 := by rw [hA 4 5 rfl]; norm_num [F]
  have hL : ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X)) : PowerSeries ℚ) =
      (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) - C (9 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 1) + C (31 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 2) - C (51 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 3) + C (40 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 4) - C (12 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 5) := by
    (try simp only [map_ofNat]) <;> ring
  have hR : (X * (9 - 31 * X + 51 * X ^ 2 - 40 * X ^ 3 + 12 * X ^ 4) : PowerSeries ℚ) = C (9 : ℚ) * X ^ 1 - C (31 : ℚ) * X ^ 2 + C (51 : ℚ) * X ^ 3 - C (40 : ℚ) * X ^ 4 + C (12 : ℚ) * X ^ 5 := by
    (try simp only [map_ofNat, pow_one]) <;> ring
  rw [hL, hR]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
    coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · norm_num [v1, v2, v3, v4, v5]
  · norm_num [v1, v2, v3, v4, v5]
  · norm_num [v1, v2, v3, v4, v5]
  · norm_num [v1, v2, v3, v4, v5]
  · norm_num [v1, v2, v3, v4, v5]
  · norm_num [v1, v2, v3, v4, v5]
  · simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 = n + 6 by omega]
    have e : ∀ k : ℕ, k ≤ 5 → (n + 6 = k) = False := fun k hk => by
      simp only [eq_iff_iff, iff_false]; omega
    have e2 : ∀ k : ℕ, k ≤ 5 → (n + 6 - k = 0) = False := fun k hk => by
      simp only [eq_iff_iff, iff_false]; omega
    have e3 : ∀ k : ℕ, k ≤ 6 → (k ≤ n + 6) = True := fun k hk => by
      simp only [eq_iff_iff, iff_true]; omega
    simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega), e2 1 (by omega), e2 2 (by omega), e2 3 (by omega), e2 4 (by omega), e2 5 (by omega), e3 1 (by omega), e3 2 (by omega), e3 3 (by omega), e3 4 (by omega), e3 5 (by omega), if_true, if_false]
    rw [hA (n + 5) (n + 6) (by omega), hA (n + 4) (n + 6 - 1) (by omega), hA (n + 3) (n + 6 - 2) (by omega), hA (n + 2) (n + 6 - 3) (by omega), hA (n + 1) (n + 6 - 4) (by omega), hA (n + 0) (n + 6 - 5) (by omega)]
    simp only [F]
    push_cast
    ring


open P222993 in
theorem OMA.solution : type_of% @OMA.S_oeis_a222993.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hA k (k + 1) rfl]
  simp only [F]
  push_cast
  ring
