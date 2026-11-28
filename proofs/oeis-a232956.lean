import OMAStatements.S_oeis_a232956

open OMA.S_oeis_a232956
open scoped BigOperators

namespace OEISA232956

private abbrev Col := Fin 4 × Fin 4

private def colVal (u : Col) (i : Fin 2) : Fin 4 :=
  if i = 0 then u.1 else u.2

private def Same (u : Col) : Prop := u.1 = u.2

private instance (u : Col) : Decidable (Same u) :=
  inferInstanceAs (Decidable (u.1 = u.2))

private def Step (u v : Col) : Prop :=
  ∀ i j : Fin 2, (colVal v j : ℕ) ≠ 3 - (colVal u i : ℕ)

private instance (u v : Col) : Decidable (Step u v) := by
  unfold Step
  infer_instance

private def Edge {n : ℕ} (x : Fin 2 → Fin (n + 1) → Fin 4) (j : Fin n)
    (i k : Fin 2) : Prop :=
  (x k j.succ : ℕ) ≠ 3 - (x i j.castSucc : ℕ)

private theorem adj_iff {n : ℕ} (p q : Fin 2 × Fin n) :
    Adj p q ↔ ((p.2 : ℕ) = q.2 + 1 ∨ (q.2 : ℕ) = p.2 + 1) := by
  have hp := p.1.isLt
  have hq := q.1.isLt
  unfold Adj
  omega

private theorem good_iff {n : ℕ} (x : Fin 2 → Fin (n + 1) → Fin 4) :
    Good x ↔ x 0 0 = 0 ∧ ∀ (j : Fin n) (i k : Fin 2), Edge x j i k := by
  constructor
  · rintro ⟨h, ht⟩
    exact ⟨ht (Nat.succ_pos n), fun j i k =>
      h (i, j.castSucc) (k, j.succ) ((adj_iff _ _).2 (Or.inr rfl))⟩
  · rintro ⟨ht, he⟩
    refine ⟨?_, fun _ => ht⟩
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    change (x k l : ℕ) ≠ 3 - (x i j : ℕ)
    rcases (adj_iff _ _).1 h with hj | hl
    · change j.val = l.val + 1 at hj
      let m : Fin n := ⟨l.val, by have := j.isLt; omega⟩
      have hm : m.castSucc = l := Fin.ext rfl
      have hm' : m.succ = j := Fin.ext hj.symm
      have he' := he m k i
      rw [Edge, hm, hm'] at he'
      have := (x k l).isLt
      have := (x i j).isLt
      omega
    · change l.val = j.val + 1 at hl
      let m : Fin n := ⟨j.val, by have := l.isLt; omega⟩
      have hm : m.castSucc = j := Fin.ext rfl
      have hm' : m.succ = l := Fin.ext hl.symm
      simpa only [Edge, hm, hm'] using he m i k

private abbrev Grid (n : ℕ) := Fin 2 → Fin (n + 1) → Fin 4

private def lastCol {n : ℕ} (x : Grid n) : Col :=
  (x 0 (Fin.last n), x 1 (Fin.last n))

private theorem colVal_lastCol {n : ℕ} (x : Grid n) (i : Fin 2) :
    colVal (lastCol x) i = x i (Fin.last n) := by
  fin_cases i <;> rfl

private def truncate {n : ℕ} (x : Grid (n + 1)) : Grid n :=
  fun i j => x i j.castSucc

private def extend {n : ℕ} (x : Grid n) (u : Col) : Grid (n + 1) :=
  fun i => Fin.snoc (x i) (colVal u i)

private theorem truncate_extend {n : ℕ} (x : Grid n) (u : Col) :
    truncate (extend x u) = x := by
  funext i j
  simp [truncate, extend]

private theorem lastCol_extend {n : ℕ} (x : Grid n) (u : Col) :
    lastCol (extend x u) = u := by
  rcases u with ⟨a, b⟩
  simp [lastCol, extend, colVal]

private theorem extend_truncate {n : ℕ} (x : Grid (n + 1)) :
    extend (truncate x) (lastCol x) = x := by
  funext i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [extend, colVal_lastCol]
  · simp [extend, truncate]

private theorem good_extend {n : ℕ} (x : Grid n) (u : Col) :
    Good (extend x u) ↔ Good x ∧ Step (lastCol x) u := by
  -- Appending a column preserves the old edges and adds the edge at the last index.
  have oldEdge (j : Fin n) (i k : Fin 2) :
      Edge (extend x u) j.castSucc i k ↔ Edge x j i k := by
    have h : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
    unfold Edge
    rw [h]
    simp only [extend, Fin.snoc_castSucc]
  have newEdge (i k : Fin 2) :
      Edge (extend x u) (Fin.last n) i k ↔
        (colVal u k : ℕ) ≠ 3 - (colVal (lastCol x) i : ℕ) := by
    have h : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext rfl
    unfold Edge
    rw [h]
    simp only [extend, Fin.snoc_castSucc, Fin.snoc_last, colVal_lastCol]
  simp only [good_iff, extend, Fin.snoc_apply_zero]
  change (x 0 0 = 0 ∧ ∀ j i k, Edge (extend x u) j i k) ↔
    (x 0 0 = 0 ∧ ∀ j i k, Edge x j i k) ∧ Step (lastCol x) u
  constructor
  · rintro ⟨ht, he⟩
    exact ⟨⟨ht, fun j i k => (oldEdge j i k).1 (he j.castSucc i k)⟩,
      fun i k => (newEdge i k).1 (he (Fin.last n) i k)⟩
  · rintro ⟨⟨ht, he⟩, hs⟩
    refine ⟨ht, fun j i k => ?_⟩
    refine Fin.lastCases ((newEdge i k).2 (hs i k)) (fun l => (oldEdge l i k).2 (he l i k)) j

private abbrev Valid (n : ℕ) := {x : Grid n // Good x}

private abbrev Ends (n : ℕ) (P : Col → Prop) :=
  {x : Valid n // P (lastCol x.1)}

private theorem truncate_step {n : ℕ} (x : Valid (n + 1)) :
    Good (truncate x.1) ∧ Step (lastCol (truncate x.1)) (lastCol x.1) := by
  apply (good_extend _ _).1
  simpa only [extend_truncate] using x.2

private def stepEquiv (n : ℕ) (P : Col → Prop) :
    (Σ x : Valid n, {u : Col // Step (lastCol x.1) u ∧ P u}) ≃ Ends (n + 1) P where
  toFun v := ⟨⟨extend v.1.1 v.2.1, (good_extend _ _).2 ⟨v.1.2, v.2.2.1⟩⟩,
    by simpa only [lastCol_extend] using v.2.2.2⟩
  invFun x := ⟨⟨truncate x.1.1, (truncate_step x.1).1⟩,
    ⟨lastCol x.1.1, (truncate_step x.1).2, x.2⟩⟩
  left_inv := by
    rintro ⟨x, u⟩
    refine Sigma.ext (Subtype.ext (truncate_extend x.1 u.1)) ?_
    refine (Subtype.heq_iff_coe_eq (fun v => ?_)).2 ?_
    · change (Step (lastCol (truncate (extend x.1 u.1))) v ∧ P v) ↔
        (Step (lastCol x.1) v ∧ P v)
      rw [truncate_extend]
    · exact lastCol_extend x.1 u.1
  right_inv x := Subtype.ext (Subtype.ext (extend_truncate x.1.1))

private def firstGrid (u : Col) : Grid 0 :=
  fun i _ => colVal u i

private theorem lastCol_firstGrid (u : Col) : lastCol (firstGrid u) = u := by
  cases u
  rfl

private def baseEquiv (P : Col → Prop) :
    Ends 0 P ≃ {u : Col // u.1 = 0 ∧ P u} where
  toFun x := ⟨lastCol x.1.1, ((good_iff _).1 x.1.2).1, x.2⟩
  invFun u := ⟨⟨firstGrid u.1, (good_iff _).2
    ⟨u.2.1, fun j => Fin.elim0 j⟩⟩, by simpa only [lastCol_firstGrid] using u.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    have hj : j = Fin.last 0 := Subsingleton.elim (α := Fin 1) _ _
    rw [hj]
    exact colVal_lastCol x.1.1 i
  right_inv u := Subtype.ext (lastCol_firstGrid u.1)

-- S n and D n count arrays of width n + 1.
private noncomputable def S (n : ℕ) : ℕ := Nat.card (Ends n Same)
private noncomputable def D (n : ℕ) : ℕ := Nat.card (Ends n fun u => ¬ Same u)

private theorem count_split (n : ℕ) : a (n + 1) = S n + D n := by
  classical
  change Nat.card (Valid n) = Nat.card (Ends n Same) + Nat.card (Ends n fun u => ¬ Same u)
  rw [← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl (fun x : Valid n => Same (lastCol x.1))).symm

private theorem s_base : S 0 = 1 := by
  rw [S, Nat.card_congr (baseEquiv Same), Nat.card_eq_fintype_card]
  decide

private theorem d_base : D 0 = 3 := by
  rw [D, Nat.card_congr (baseEquiv (fun u => ¬ Same u)), Nat.card_eq_fintype_card]
  decide

-- The only finite enumeration is over the four symbols in the columns.
private theorem step_same_fintype : ∀ u : Col,
    Fintype.card {v : Col // Step u v ∧ Same v} = if Same u then 3 else 2 := by
  decide

private theorem step_diff_fintype : ∀ u : Col,
    Fintype.card {v : Col // Step u v ∧ ¬ Same v} = if Same u then 6 else 2 := by
  decide

private theorem count_step (n : ℕ) (P : Col → Prop) (s d : ℕ)
    (hP : ∀ u : Col, Nat.card {v : Col // Step u v ∧ P v} = if Same u then s else d) :
    Nat.card (Ends (n + 1) P) = s * S n + d * D n := by
  classical
  let : Fintype (Valid n) := Fintype.ofFinite _
  let p : Valid n → Prop := fun x => Same (lastCol x.1)
  rw [← Nat.card_congr (stepEquiv n P), Nat.card_sigma]
  simp_rw [hP]
  change (∑ x : Valid n, if p x then s else d) = _
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun x => if p x then s else d)]
  have hs (x : {x // p x}) : (if p x.1 then s else d) = s := if_pos x.2
  have hd (x : {x // ¬ p x}) : (if p x.1 then s else d) = d := if_neg x.2
  simp only [hs, hd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [S, D, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  ac_rfl

private theorem s_step (n : ℕ) : S (n + 1) = 3 * S n + 2 * D n :=
  count_step n Same 3 2 fun u => by
    rw [Nat.card_eq_fintype_card]
    exact step_same_fintype u

private theorem d_step (n : ℕ) : D (n + 1) = 6 * S n + 2 * D n :=
  count_step n (fun u => ¬ Same u) 6 2 fun u => by
    rw [Nat.card_eq_fintype_card]
    exact step_diff_fintype u

private theorem a_one : a 1 = 4 := by
  simpa only [s_base, d_base] using count_split 0

private theorem a_two : a 2 = 21 := by
  simpa only [s_step, d_step, s_base, d_base] using count_split 1

private theorem recurrence_add (n : ℕ) :
    a (n + 1 + 2) = 5 * a (n + 1 + 1) + 6 * a (n + 1) := by
  change a (n + 2 + 1) = 5 * a (n + 1 + 1) + 6 * a (n + 1)
  rw [count_split (n + 2), count_split (n + 1), count_split n,
    s_step (n + 1), d_step (n + 1), s_step n, d_step n]
  ring

private theorem recurrence (n : ℕ) (hn : 3 ≤ n) :
    a n = 5 * a (n - 1) + 6 * a (n - 2) := by
  have h := recurrence_add (n - 3)
  rwa [show n - 3 + 1 + 2 = n by omega, show n - 3 + 1 + 1 = n - 1 by omega,
    show n - 3 + 1 = n - 2 by omega] at h

private theorem closed_add (n : ℕ) :
    42 * (a (n + 1) : ℚ) = 25 * 6 ^ (n + 1) - 18 * (-1) ^ (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [a_one]
  | one => norm_num [a_two]
  | more n h0 h1 =>
    change 42 * (a (n + 1 + 2) : ℚ) = 25 * 6 ^ (n + 1 + 2) - 18 * (-1) ^ (n + 1 + 2)
    have hr : (a (n + 1 + 2) : ℚ) = 5 * (a (n + 1 + 1) : ℚ) + 6 * (a (n + 1) : ℚ) := by
      exact_mod_cast recurrence_add n
    rw [hr, mul_add, show (42 : ℚ) * (5 * (a (n + 1 + 1) : ℚ)) =
      5 * (42 * (a (n + 1 + 1) : ℚ)) by ring,
      show (42 : ℚ) * (6 * (a (n + 1) : ℚ)) = 6 * (42 * (a (n + 1) : ℚ)) by ring, h1, h0]
    simp only [pow_add, pow_one]
    ring

private theorem closed (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (25 * 6 ^ n - 18 * (-1) ^ n) / 42 := by
  have h := closed_add (n - 1)
  rw [show n - 1 + 1 = n by omega] at h
  apply (eq_div_iff (by norm_num : (42 : ℚ) ≠ 0)).2
  simpa only [mul_comm (a n : ℚ) 42] using h

open PowerSeries in
private theorem generating :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ))
  let x : PowerSeries ℚ := X
  let den := (1 + x) * (1 - 6 * x)
  let num := x * (4 + x)
  have hc (n : ℕ) : coeff n F = if n = 0 then 0 else (a n : ℚ) := coeff_mk _ _
  have hx (n : ℕ) : coeff n (x * F) = if 1 ≤ n then coeff (n - 1) F else 0 := by
    simpa only [pow_one, x] using coeff_X_pow_mul' F 1 n
  have hxx (n : ℕ) : coeff n (x ^ 2 * F) = if 2 ≤ n then coeff (n - 2) F else 0 :=
    coeff_X_pow_mul' F 2 n
  have hexp : den * F = F - C (5 : ℚ) * (x * F) - C (6 : ℚ) * (x ^ 2 * F) := by
    simp only [den, map_ofNat]
    ring
  have hnexp : num = C (4 : ℚ) * x + x ^ 2 := by
    simp only [num, map_ofNat]
    ring
  -- The recurrence makes all coefficients from degree three onward vanish.
  have hprod : den * F = num := by
    ext n
    simp only [hexp, hnexp, map_add, map_sub, coeff_C_mul, hx, hxx, hc,
      x, coeff_X, coeff_X_pow]
    rcases n with _ | _ | _ | n
    · norm_num
    · norm_num [a_one]
    · norm_num [a_one, a_two]
    · have h : (a (n + 3) : ℚ) =
          5 * (a (n + 3 - 1) : ℚ) + 6 * (a (n + 3 - 2) : ℚ) := by
        exact_mod_cast recurrence (n + 3) (by omega)
      have h0 : n + 3 ≠ 0 := by omega
      have h1 : n + 3 ≠ 1 := by omega
      have h2 : n + 3 ≠ 2 := by omega
      have h3 : n + 3 - 1 ≠ 0 := by omega
      have h4 : n + 3 - 2 ≠ 0 := by omega
      have h5 : 1 ≤ n + 3 := by omega
      have h6 : 2 ≤ n + 3 := by omega
      simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
        if_pos h5, if_pos h6, mul_zero, add_zero]
      linarith
  have hden : constantCoeff den ≠ 0 := by
    simp [den, x]
  change F = num * den⁻¹
  rw [← hprod, mul_comm den F, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

end OEISA232956

open OEISA232956 in
theorem OMA.solution : type_of% @OMA.S_oeis_a232956.main := by
  refine ⟨recurrence, generating, ?_, ?_⟩
  · intro n hn he
    simpa [he.neg_one_pow] using closed n hn
  · intro n hn ho
    rw [closed n hn, ho.neg_one_pow]
    ring
