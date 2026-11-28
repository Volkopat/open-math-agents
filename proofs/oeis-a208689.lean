import OMAStatements.S_oeis_a208689

namespace OMA.A208689Proof

open OMA.S_oeis_a208689 Finset PowerSeries

private def valid (x : Fin 3 → Bool) : Prop :=
  Avoids [(false, true, true), (true, false, true)] (x 0) (x 1) (x 2)

private instance (x : Fin 3 → Bool) : Decidable (valid x) := by
  unfold valid Avoids
  infer_instance

private abbrev Col := {x : Fin 3 → Bool // valid x}

private def edge (x y : Col) : Prop := ∀ i, x.val i = true ∨ y.val i = true

private instance (x y : Col) : Decidable (edge x y) := by
  unfold edge
  infer_instance

private theorem avoids_first (x y z : Bool) :
    Avoids [(false, false, false), (false, false, true)] x y z ↔ x = true ∨ y = true := by
  unfold Avoids
  cases x <;> cases y <;> cases z <;> decide

private theorem counted_iff (n : ℕ) (A : Fin 3 → Fin n → Bool) :
    IsCounted n A ↔ (∀ j : Fin n, valid (fun i => A i j)) ∧
      ∀ (j : ℕ) (h : j + 2 < n) (i : Fin 3),
        A i ⟨j, by omega⟩ = true ∨ A i ⟨j + 1, by omega⟩ = true := by
  constructor
  · rintro ⟨hh, hv⟩
    exact ⟨fun j => hv 0 (by decide) j, fun j hj i => (avoids_first ..).1 (hh i j hj)⟩
  · rintro ⟨hv, hh⟩
    refine ⟨fun i j hj => (avoids_first ..).2 (hh j hj i), ?_⟩
    intro i hi j
    have hz : i = 0 := by omega
    subst i
    exact hv j

private abbrev Arr (n : ℕ) := {A : Fin 3 → Fin n → Bool // IsCounted n A}

private def column {n : ℕ} (A : Arr n) (j : Fin n) : Col :=
  ⟨fun i => A.val i j, (counted_iff n A.val).1 A.2 |>.1 j⟩

private def path {n : ℕ} (w : Fin (n + 1) → Col) : Prop :=
  ∀ i : Fin n, edge (w i.castSucc) (w i.succ)

private instance {n : ℕ} (w : Fin (n + 1) → Col) : Decidable (path w) := by
  unfold path
  infer_instance

private abbrev Word (n : ℕ) := {w : Fin (n + 1) → Col // path w}

/-- The final column is unrestricted by the horizontal condition. -/
private def extract (n : ℕ) : Arr (n + 2) ≃ Word n × Col where
  toFun A := (⟨fun j => column A j.castSucc, fun j =>
    (counted_iff _ _).1 A.2 |>.2 j.val (by have := j.isLt; omega)⟩, column A (Fin.last _))
  invFun p := by
    let w : Fin (n + 2) → Col := Fin.snoc p.1.val p.2
    refine ⟨fun i j => (w j).val i, (counted_iff _ _).2 ⟨fun j => (w j).2, ?_⟩⟩
    intro j hj i
    let t : Fin n := ⟨j, by omega⟩
    change (w t.castSucc.castSucc).val i = true ∨ (w t.succ.castSucc).val i = true
    simpa only [w, Fin.snoc_castSucc] using p.1.2 t i
  left_inv A := by
    apply Subtype.ext
    funext i j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [column]
    · simp [column]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      apply Subtype.ext
      simp [column]
    · apply Subtype.ext
      simp [column]

private theorem col_card : Fintype.card Col = 6 := by decide +kernel

private theorem one_column : a 1 = 6 := by
  let e : Arr 1 ≃ Col := {
    toFun := fun A => column A 0
    invFun := fun x => ⟨fun i _ => x.val i, (counted_iff _ _).2
      ⟨fun _ => x.2, fun j hj => by omega⟩⟩
    left_inv := fun A => Subtype.ext (funext fun i => funext fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl)
    right_inv := fun _ => rfl }
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, col_card]

private abbrev cons {n : ℕ} (u : Col) (w : Fin n → Col) : Fin (n + 1) → Col :=
  @Fin.cons n (fun _ ↦ Col) u w

private theorem path_cons {n : ℕ} (x y : Col) (w : Fin n → Col) :
    path (cons x (cons y w)) ↔ edge x y ∧ path (cons y w) := by
  unfold path
  rw [Fin.forall_fin_succ]
  have hcast (i : Fin n) : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  simp [cons, hcast]

private def step (f : Col → ℤ) (u : Col) : ℤ := ∑ v, if edge u v then f v else 0

private def weight : ℕ → Col → ℤ
  | 0, _ => 1
  | n + 1, u => step (weight n) u

private theorem weight_count (n : ℕ) (u : Col) :
    (∑ w : Fin n → Col, (if path (cons u w) then 1 else 0 : ℤ)) = weight n u := by
  induction n generalizing u with
  | zero => simp [path, weight]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Col)
    have hs :
        (∑ w : Fin (n + 1) → Col, (if path (cons u w) then 1 else 0 : ℤ)) =
          ∑ p : Col × (Fin n → Col), (if path (cons u (cons p.1 p.2)) then 1 else 0 : ℤ) :=
      (Fintype.sum_equiv e _ _ fun p ↦ rfl).symm
    rw [hs, Fintype.sum_prod_type, weight, step]
    apply sum_congr rfl
    intro v _
    simp only [path_cons]
    by_cases h : edge u v
    · simpa only [h, true_and, if_true] using ih v
    · simp only [h, false_and, if_false, sum_const_zero]

private theorem count_formula (n : ℕ) : (a (n + 2) : ℤ) = 6 * ∑ u : Col, weight n u := by
  have h := Nat.card_congr (extract n)
  change a (n + 2) = _ at h
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, col_card, Fintype.card_subtype] at h
  have ht : (a (n + 2) : ℤ) = (((univ : Finset (Fin (n + 1) → Col)).filter path).card : ℤ) * 6 := by
    exact_mod_cast h
  rw [ht, ← Finset.sum_boole path univ, mul_comm]
  congr 1
  let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Col)
  rw [← Fintype.sum_equiv e (fun p => if path (cons p.1 p.2) then (1 : ℤ) else 0) _ (fun _ => rfl),
    Fintype.sum_prod_type]
  exact sum_congr rfl (fun u _ => weight_count n u)

private theorem weight_relation (n : ℕ) (u : Col) :
    weight (n+3) u = 2 * weight (n+2) u + 4 * weight (n+1) u - 3 * weight n u := by
  induction n generalizing u with
  | zero =>
    have h : ∀ v : Col, weight 3 v = 2 * weight 2 v + 4 * weight 1 v - 3 * weight 0 v := by
      decide +kernel
    exact h u
  | succ n ih =>
    change step (weight (n+3)) u = 2 * step (weight (n+2)) u +
      4 * step (weight (n+1)) u - 3 * step (weight n) u
    simp only [step, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro v _
    split_ifs
    · exact ih v
    · ring

private lemma initial :
    a 1 = 6 ∧ (a 2 : ℤ) = 36 ∧ (a 3 : ℤ) = 78 ∧ (a 4 : ℤ) = 282 := by
  rw [one_column, count_formula 0, count_formula 1, count_formula 2]
  decide +kernel

private theorem recZ (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) = 2*a (n-1) + 4*a (n-2) - 3*a (n-3) := by
  by_cases h : n = 4
  · subst n
    norm_num [initial.1, initial.2.1, initial.2.2.1, initial.2.2.2]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n-5, by omega⟩
  rw [show k + 5 - 1 = (k+2)+2 by omega, show k+5-2=(k+1)+2 by omega,
    show k+5-3=k+2 by omega, count_formula (k+3), count_formula (k+2),
    count_formula (k+1), count_formula k]
  have hs := sum_congr rfl (fun u (_ : u ∈ (univ : Finset Col)) => weight_relation k u)
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at hs
  linarith

private lemma gf :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 3 * X) * (1 + X - X ^ 2)) =
      6 * X * (1 + 4 * X - 3 * X ^ 2)) := by
  let F : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ))
  change F * _ = _
  have lhs : F * ((1 - 3 * X) * (1 + X - X ^ 2)) =
      F - C 2 * (X ^ 1 * F) - C 4 * (X ^ 2 * F) + C 3 * (X ^ 3 * F) := by
    simp only [map_ofNat]
    ring
  have rhs : (6 * X * (1 + 4 * X - 3 * X ^ 2) : ℚ⟦X⟧) =
      C 6 * X ^ 1 + C 24 * X ^ 2 - C 18 * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, F, coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_neg (show n ≠ 0 by omega),
      if_neg (show n-1 ≠ 0 by omega), if_neg (show n-2 ≠ 0 by omega),
      if_neg (show n-3 ≠ 0 by omega), if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega),
      mul_zero, sub_zero, add_zero]
    have h : (a n : ℚ) = 2*a (n-1) + 4*a (n-2) - 3*a (n-3) := by exact_mod_cast recZ n hn
    linarith
  · have v2 : a 2 = 36 := by exact_mod_cast initial.2.1
    have v3 : a 3 = 78 := by exact_mod_cast initial.2.2.1
    interval_cases n <;> norm_num [one_column, v2, v3]

private noncomputable def alpha : ℝ := (-1 + Real.sqrt 5) / 2
private noncomputable def beta : ℝ := (-1 - Real.sqrt 5) / 2

private noncomputable def closed (n : ℕ) : ℝ :=
  (180 * 3 ^ n + (75 - 27 * Real.sqrt 5) * alpha ^ n +
    3 * (25 + 9 * Real.sqrt 5) * beta ^ n) / 55

private theorem expr_eq (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℤ)) * (5 * 6 ^ (2 + n) +
      (75 - 27 * Real.sqrt 5) * (-1 + Real.sqrt 5) ^ n +
      3 * (-1 - Real.sqrt 5) ^ n * (25 + 9 * Real.sqrt 5)) / 55 = closed n := by
  rw [zpow_neg, zpow_natCast]
  unfold closed alpha beta
  rw [div_pow, div_pow, pow_add, show (6 : ℝ) = 2 * 3 by norm_num, mul_pow]
  field_simp
  simp only [mul_pow]
  ring

private theorem power_rec (x : ℝ) (hx : x^3-2*x^2-4*x+3=0) (k : ℕ) :
    x ^ (k + 3) = 2*x^(k+2) + 4*x^(k+1) - 3*x^k := by
  simp only [pow_add, pow_one]
  linear_combination x^k * hx

private theorem closed_rec (n : ℕ) (hn : 4 ≤ n) :
    closed n = 2*closed (n-1) + 4*closed (n-2) - 3*closed (n-3) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have ha : alpha^2 + alpha - 1 = 0 := by unfold alpha; nlinarith [hs]
  have hb : beta^2 + beta - 1 = 0 := by unfold beta; nlinarith [hs]
  have har : alpha^3-2*alpha^2-4*alpha+3=0 := by linear_combination (alpha-3)*ha
  have hbr : beta^3-2*beta^2-4*beta+3=0 := by linear_combination (beta-3)*hb
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n-3, by omega⟩
  rw [show k+3-1=k+2 by omega, show k+3-2=k+1 by omega, show k+3-3=k by omega]
  unfold closed
  rw [power_rec 3 (by norm_num) k, power_rec alpha har k, power_rec beta hbr k]
  ring

private theorem closed_count (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = closed n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : 4 ≤ n
    · have hr : (a n : ℝ) = 2*a (n-1) + 4*a (n-2) - 3*a (n-3) := by
        exact_mod_cast recZ n h
      rw [hr, closed_rec n h, ih (n-1) (by omega) (by omega),
        ih (n-2) (by omega) (by omega), ih (n-3) (by omega) (by omega)]
    · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      have hfour : Real.sqrt 5 ^ 4 = 25 := by
        calc Real.sqrt 5 ^ 4 = (Real.sqrt 5 ^ 2) ^ 2 := by ring
          _ = 25 := by rw [hs]; norm_num
      have v2 : a 2 = 36 := by exact_mod_cast initial.2.1
      have v3 : a 3 = 78 := by exact_mod_cast initial.2.2.1
      interval_cases n <;> norm_num [one_column, v2, v3, closed, alpha, beta] <;> nlinarith [hs, hfour]

theorem result : type_of% @OMA.S_oeis_a208689.main := by
  refine ⟨gf, fun n hn => ?_⟩
  rw [expr_eq]
  exact closed_count n hn

end OMA.A208689Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a208689.main := OMA.A208689Proof.result
