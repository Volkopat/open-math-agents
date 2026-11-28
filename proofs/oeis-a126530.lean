import OMAStatements.S_oeis_a126530

namespace OMA.DigitWalks
open OMA.S_oeis_a126530 Finset PowerSeries

private abbrev Digit := Fin 9
private abbrev Word (n : ℕ) := Fin n → Digit

private def advance : (Digit → ℤ) →ₗ[ℤ] (Digit → ℤ) where
  toFun f d := ∑ e : Digit, (if adjOk d e then 1 else 0) * f e
  map_add' f g := by
    ext d
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' z f := by
    ext d
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
    exact sum_congr rfl fun i _ => by ring

private def counts : ℕ → Digit → ℤ
  | 0 => fun _ => 1
  | n+1 => advance (counts n)

private theorem counts_succ (n : ℕ) : counts (n+1) = advance (counts n) := rfl

private theorem sumHead {n : ℕ} (f : Word (n+1) → ℤ) :
    ∑ x, f x = ∑ d : Digit, ∑ y : Word n, f (Fin.cons d y) := by
  rw [← (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Digit)) f)]
  exact Fintype.sum_prod_type _

private def admissible (x : Word n) : Prop := (List.ofFn x).IsChain adjOk

private instance (x : Word n) : Decidable (admissible x) := by
  unfold admissible
  infer_instance

private theorem admissible_cons (d e : Digit) (x : Word n) :
    admissible (Fin.cons d (Fin.cons e x)) ↔ adjOk d e ∧ admissible (Fin.cons e x) := by
  simp only [admissible, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.isChain_cons_cons]

private theorem valid_iff (x : Word n) : isValid n x ↔ admissible x := by
  simp only [isValid, admissible, List.isChain_iff_getElem, List.length_ofFn, List.getElem_ofFn]
  constructor
  · intro h i hi
    exact h ⟨i, by omega⟩
  · intro h i
    exact h i.val (by have hi := i.isLt; omega)

private def countFrom (d : Digit) (n : ℕ) : ℤ :=
  ∑ x : Word n, if admissible (Fin.cons d x) then 1 else 0

private theorem countFrom_eq (n : ℕ) (d : Digit) : countFrom d n = counts n d := by
  induction n generalizing d with
  | zero => simp [countFrom, counts, admissible]
  | succ n ih =>
    unfold countFrom
    rw [sumHead]
    change _ = ∑ e : Digit, (if adjOk d e then 1 else 0) * counts n e
    apply sum_congr rfl
    intro e _
    simp only [admissible_cons]
    by_cases h : adjOk d e
    · simp [h, ← ih e, countFrom]
    · simp [h]

private theorem a_succ (n : ℕ) : (a (n+1) : ℤ) = ∑ d, counts n d := by
  simp only [a, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sumHead]
  apply sum_congr rfl
  intro d _
  rw [← countFrom_eq]
  apply sum_congr rfl
  intro x _
  exact if_congr (valid_iff _) rfl rfl

private theorem a_zero : a 0 = 1 := by decide +kernel

-- A linear transition preserves any recurrence satisfied by the initial vectors.
private def relationAt (n : ℕ) : Digit → ℤ :=
  counts (n+4) + (-7 : ℤ) • counts (n+3) + (-7 : ℤ) • counts (n+2) + (4 : ℤ) • counts (n+1) + (3 : ℤ) • counts (n)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem vectorRec (n : ℕ) : relationAt n = 0 := by
  induction n with
  | zero =>
    ext d
    fin_cases d <;> decide +kernel
  | succ n ih =>
    have h := congrArg (fun v => advance v) ih
    simpa only [relationAt, map_add, map_smul, map_zero, ← counts_succ] using h

private theorem shifted (m : ℕ) :
    (1) * (a (m+5) : ℤ) + (-7) * (a (m+4) : ℤ) + (-7) * (a (m+3) : ℤ) + (4) * (a (m+2) : ℤ) + (3) * (a (m+1) : ℤ) = 0 := by
  have h := congrArg (fun v : Digit → ℤ => ∑ d, v d) (vectorRec m)
  simp only [relationAt, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← a_succ, Finset.sum_const_zero] at h
  linear_combination h

private theorem a_rat (n : ℕ) :
    (a (n+1) : ℚ) = ((∑ d, counts n d : ℤ) : ℚ) := by
  exact_mod_cast a_succ n

private noncomputable def term (c : ℚ) (j : ℕ) : ℚ⟦X⟧ := C c * X ^ j

private theorem coeff_mulTerm (s : ℚ⟦X⟧) (c : ℚ) (n j : ℕ) :
    coeff n (s * term c j) = if j ≤ n then c * coeff (n-j) s else 0 := by
  rw [term, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
  split_ifs <;> ring

private theorem coeff_term (c : ℚ) (n j : ℕ) :
    coeff n (term c j) = if n = j then c else 0 := coeff_C_mul_X_pow c j n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem generating : mk (fun n => (a n : ℚ)) * ((1 + X) * (1 - 8 * X + X ^ 2 + 3 * X ^ 3)) = 1 + 2 * X - X ^ 2 - X ^ 3 := by
  have hD : (((1 + X) * (1 - 8 * X + X ^ 2 + 3 * X ^ 3)) : ℚ⟦X⟧) = term (1) 0 + term (-7) 1 + term (-7) 2 + term (4) 3 + term (3) 4 := by
    simp only [term,map_neg,map_ofNat,map_one]
    ring
  have hN : (1 + 2 * X - X ^ 2 - X ^ 3 : ℚ⟦X⟧) = term (1) 0 + term (2) 1 + term (-1) 2 + term (-1) 3 := by
    simp only [term,map_neg,map_ofNat,map_one]
    ring
  rw [hD,hN]
  ext n
  simp only [mul_add,map_add,coeff_mulTerm,coeff_term,coeff_mk]
  by_cases hn : n ≤ 4
  · interval_cases n <;> simp only [a_zero,a_rat] <;> decide +kernel
  · obtain ⟨m,rfl⟩ : ∃ m, n = m+5 := ⟨n-5, by omega⟩
    have h : (1) * (a (m+5) : ℚ) + (-7) * (a (m+4) : ℚ) + (-7) * (a (m+3) : ℚ) + (4) * (a (m+2) : ℚ) + (3) * (a (m+1) : ℚ) = 0 := by exact_mod_cast shifted m
    simp only [Nat.sub_zero, Nat.zero_le, if_true, if_false,
      show 1 ≤ m+5 by omega, show 2 ≤ m+5 by omega, show 3 ≤ m+5 by omega,
      show 4 ≤ m+5 by omega, show m+5 ≠ 0 by omega, show m+5 ≠ 1 by omega,
      show m+5 ≠ 2 by omega, show m+5 ≠ 3 by omega, show m+5-1=m+4 by omega,
      show m+5-2=m+3 by omega, show m+5-3=m+2 by omega, show m+5-4=m+1 by omega]
    linear_combination h

end OMA.DigitWalks

open OMA.S_oeis_a126530 in
theorem OMA.solution : type_of% @OMA.S_oeis_a126530.main := by
  refine ⟨OMA.DigitWalks.generating, ?_⟩
  intro n hn
  by_cases hs : n = 4
  · subst n
    simp only [OMA.DigitWalks.a_zero, OMA.DigitWalks.a_succ] <;> decide +kernel
  obtain ⟨m, rfl⟩ : ∃ m, n = m+5 := ⟨n-5, by omega⟩
  have h := OMA.DigitWalks.shifted m
  simp only [show m+5-1=m+4 by omega, show m+5-2=m+3 by omega, show m+5-3=m+2 by omega, show m+5-4=m+1 by omega]
  linear_combination h
