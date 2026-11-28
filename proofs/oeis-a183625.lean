import OMAStatements.S_oeis_a183625

namespace A183625Proof

open OMA.S_oeis_a183625

private abbrev Row := Fin 3 → Fin 3

private def compatible (r s : Row) : Prop :=
  ∀ j : Fin 2, (r j.castSucc : ℕ) + r j.succ + s j.castSucc + s j.succ = 4

private instance (r s : Row) : Decidable (compatible r s) := by
  unfold compatible
  infer_instance

private def degree (r : Row) : ℕ := (Finset.univ.filter (compatible r)).card

/-- Complementing every entry exchanges the two successive classes of rows.
In particular the number of choices for the next row stays constant. -/
private theorem same_degree : ∀ r s : Row, compatible r s → degree r = degree s := by
  decide +kernel

private def toRows {n : ℕ} (l : List Row) (h : l.length = n) : Fin n → Row :=
  fun i => l.get (i.cast h.symm)

private theorem recover {n : ℕ} (l : List Row) (h : l.length = n) :
    List.ofFn (toRows l h) = l := by
  subst n
  exact List.ofFn_get l

private def arraysEquiv (n : ℕ) :
    {l : List Row // l.length = n ∧ IsSolution l} ≃ {x : Fin n → Row // IsSolution (List.ofFn x)} where
  toFun l := ⟨toRows l.val l.prop.1, by rw [recover]; exact l.prop.2⟩
  invFun x := ⟨List.ofFn x.val, List.length_ofFn, x.prop⟩
  left_inv l := Subtype.ext (recover l.val l.prop.1)
  right_inv x := Subtype.ext (List.ofFn_injective (recover (List.ofFn x.val) List.length_ofFn))

private theorem sum_rows {n : ℕ} (f : (Fin (n+1) → Row) → ℕ) :
    (∑ x, f x) = ∑ r : Row, ∑ x : Fin n → Row, f (Fin.cons r x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Row)).sum_comp f, Fintype.sum_prod_type]
  rfl

private noncomputable def tails (n : ℕ) (r : Row) : ℕ := by
  classical
  exact ∑ x : Fin n → Row, if IsSolution (r :: List.ofFn x) then 1 else 0

private theorem solution_cons (r s : Row) (l : List Row) :
    IsSolution (r :: s :: l) ↔ compatible r s ∧ IsSolution (s :: l) := List.isChain_cons_cons

private theorem tails_eq (n : ℕ) (r : Row) : tails n r = (degree r)^n := by
  classical
  induction n generalizing r with
  | zero => simp [tails, IsSolution]
  | succ n ih =>
    unfold tails
    rw [sum_rows]
    simp only [List.ofFn_cons, solution_cons, ite_and,
      Finset.sum_ite_irrel, Finset.sum_const_zero]
    change (∑ s : Row, if compatible r s then tails n s else 0) = _
    simp only [ih]
    calc
      _ = ∑ s : Row, if compatible r s then (degree r)^n else 0 := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases h : compatible r s <;> simp [h, same_degree r s]
      _ = (degree r)^(n+1) := by
        rw [← Finset.sum_filter]
        simp [degree, pow_succ, Nat.mul_comm]

private theorem degree_cases : ∀ r : Row, degree r = 1 ∨ degree r = 2 ∨ degree r = 3 := by
  decide +kernel

private theorem histogram :
    (∑ r : Row, if degree r = 1 then 1 else 0) = 12 ∧
    (∑ r : Row, if degree r = 2 then 1 else 0) = 12 ∧
    (∑ r : Row, if degree r = 3 then 1 else 0) = 3 := by decide +kernel

theorem closed_count (n : ℕ) : a n = 12 + 12 * 2^n + 3 * 3^n := by
  classical
  rw [a, Nat.card_congr (arraysEquiv (n+1)), Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, sum_rows]
  simp only [List.ofFn_cons]
  change (∑ r : Row, tails n r) = _
  simp only [tails_eq]
  calc
    _ = ∑ r : Row, ((if degree r = 1 then 1 else 0) +
          (if degree r = 2 then 1 else 0) * 2^n + (if degree r = 3 then 1 else 0) * 3^n) := by
      apply Finset.sum_congr rfl
      intro r _
      rcases degree_cases r with h | h | h <;> simp [h]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        histogram.1, histogram.2.1, histogram.2.2]

end A183625Proof

open OMA.S_oeis_a183625 PowerSeries A183625Proof in
theorem OMA.solution :
    type_of% @OMA.S_oeis_a183625.main := by
  have recZ (k : ℕ) : (a (k+3) : ℤ) = 6*a (k+2) - 11*a (k+1) + 6*a k := by
    simp only [closed_count, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k,rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
    exact recZ k
  · let A : ℚ⟦X⟧ := mk fun n => (a (n+1) : ℚ)
    change A * _ = _
    rw [show A*((1-X)*(1-2*X)*(1-3*X)) =
          A - C 6 * (A*X^1) + C 11 * (A*X^2) - C 6 * (A*X^3) by
          simp only [map_ofNat]; ring,
        show (3*(15-61*X+54*X^2) : ℚ⟦X⟧) =
          C 45*X^0 - C 183*X^1 + C 162*X^2 by
          simp only [map_ofNat]; ring]
    ext n
    simp only [map_sub, map_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
    by_cases h : n ≤ 2
    · interval_cases n <;> norm_num [closed_count]
    · obtain ⟨k,rfl⟩ : ∃ k, n = k+3 := ⟨n-3, by omega⟩
      simp (disch := omega) only [coeff_C, if_pos, if_neg]
      have hr : (a (k+1+3) : ℚ) = 6*a (k+1+2) - 11*a (k+1+1) + 6*a (k+1) := by
        exact_mod_cast recZ (k+1)
      change (a (k+4) : ℚ) - 6*a (k+3) + 11*a (k+2) - 6*a (k+1) = 0-0+0
      change (a (k+4) : ℚ) = 6*a (k+3) - 11*a (k+2) + 6*a (k+1) at hr
      linarith
  · intro n _
    simp only [closed_count, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    ring
