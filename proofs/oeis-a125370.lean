import OMAStatements.S_oeis_a125370

namespace OMA.CircularDigitWalks
open OMA.S_oeis_a125370 Finset PowerSeries

private abbrev Digit := Fin 7
private abbrev Word (n : ℕ) := Fin n → Digit

private def edge (u v : Digit) : Prop := adjOk u v

private instance (u v : Digit) : Decidable (edge u v) := by
  unfold edge
  infer_instance

private def transition : Matrix Digit Digit ℚ := fun u v => if edge u v then 1 else 0

private def path (u v : Digit) (w : Word n) : Prop :=
  (u :: (List.ofFn w ++ [v])).IsChain edge

private instance (u v : Digit) (w : Word n) : Decidable (path u v w) := by
  unfold path
  infer_instance

private theorem path_cons (u v d : Digit) (w : Word n) :
    path u v (Fin.cons d w) ↔ edge u d ∧ path d v w := by
  simp only [path, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.cons_append, List.isChain_cons_cons]

private theorem sum_head {n : ℕ} (f : Word (n+1) → ℚ) :
    ∑ w, f w = ∑ d : Digit, ∑ w : Word n, f (Fin.cons d w) := by
  rw [← (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Digit)) f)]
  exact Fintype.sum_prod_type _

private theorem path_sum (n : ℕ) (u v : Digit) :
    (∑ w : Word n, if path u v w then (1 : ℚ) else 0) = (transition ^ (n+1)) u v := by
  induction n generalizing u with
  | zero => simp [path, transition]
  | succ n ih =>
    rw [sum_head, pow_succ', Matrix.mul_apply]
    apply sum_congr rfl
    intro d _
    by_cases h : edge u d
    · simpa [path_cons, transition, h] using ih d
    · simp [path_cons, transition, h]

private theorem cyclic_next {n : ℕ} (w : Word (n+1)) (i : Fin (n+1)) :
    Fin.snoc (α := fun _ => Digit) w (w 0) i.succ = w ⟨(i.val+1) % (n+1), Nat.mod_lt _ (Nat.succ_pos _)⟩ := by
  by_cases hi : i.val+1 < n+1
  · have h : i.succ = (⟨(i.val+1) % (n+1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (n+1)).castSucc :=
      Fin.ext (by simp [Nat.mod_eq_of_lt hi])
    rw [h, Fin.snoc_castSucc]
  · have he : i.val+1 = n+1 := by omega
    rw [show i.succ = Fin.last (n+1) from Fin.ext he, Fin.snoc_last]
    congr 1
    exact Fin.ext (by simp [he])

private theorem cycle_path (d : Digit) (w : Word n) :
    path d d w ↔
      ∀ i : Fin (n+1), edge ((Fin.cons d w : Word (n+1)) i) ((Fin.cons d w : Word (n+1)) ⟨(i.val+1) % (n+1), Nat.mod_lt _ (Nat.succ_pos _)⟩) := by
  let z : Word (n+1) := Fin.cons d w
  let t : Word (n+2) := Fin.snoc z d
  have hz : List.ofFn t = d :: (List.ofFn w ++ [d]) := by
    rw [List.ofFn_succ']
    simp only [t, Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
    simp only [z, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.cons_append]
  rw [path, ← hz, List.isChain_iff_getElem]
  simp only [List.length_ofFn, List.getElem_ofFn]
  have hs (i : Fin (n+1)) : t i.succ = z ⟨(i.val+1) % (n+1), Nat.mod_lt _ (Nat.succ_pos _)⟩ := by
    simpa only [z, t, Fin.cons_zero] using cyclic_next z i
  have hcast (i : Fin (n+1)) : t i.castSucc = z i := Fin.snoc_castSucc ..
  constructor
  · intro h i
    have hi := h i.val (by have := i.isLt; omega)
    change edge (t i.castSucc) (t i.succ) at hi
    rw [hcast, hs] at hi
    exact hi
  · intro h j hj
    let i : Fin (n+1) := ⟨j, by omega⟩
    change edge (t i.castSucc) (t i.succ)
    rw [hcast, hs]
    exact h i

private theorem count_trace (n : ℕ) : (a (n+1) : ℚ) = Matrix.trace (transition^(n+1)) := by
  simp only [a, Finset.card_filter, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  rw [sum_head, Matrix.trace]
  change _ = ∑ d, (transition ^ (n+1)) d d
  apply sum_congr rfl
  intro d _
  rw [← path_sum]
  apply sum_congr rfl
  intro w _
  by_cases h : path d d w
  · have hv : (isValid (n+1) (Fin.cons d w)) := (cycle_path d w).mp h
    simp [h, hv]
  · have hv : ¬ (isValid (n+1) (Fin.cons d w)) := fun H => h ((cycle_path d w).mpr H)
    simp [h, hv]

private theorem a_zero : a 0 = 1 := by decide +kernel

set_option maxRecDepth 15000 in
private theorem matrixRelation : (1 : ℚ) • transition ^ 4 + (-7 : ℚ) • transition ^ 3 + (1 : ℚ) • transition ^ 2 + (5 : ℚ) • transition ^ 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem shifted (m : ℕ) : (1) * (a (m+4) : ℚ) + (-7) * (a (m+3) : ℚ) + (1) * (a (m+2) : ℚ) + (5) * (a (m+1) : ℚ) = 0 := by
  have h := congrArg (fun A : Matrix Digit Digit ℚ => (transition^m * A).trace) matrixRelation
  simp only [mul_add, mul_smul_comm, mul_zero, ← pow_add, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, Matrix.trace_zero, ← count_trace] at h
  linear_combination h

private noncomputable def term (c : ℚ) (j : ℕ) : ℚ⟦X⟧ := C c * X ^ j

private theorem coeff_mulTerm (s : ℚ⟦X⟧) (c : ℚ) (n j : ℕ) :
    coeff n (s * term c j) = if j ≤ n then c * coeff (n-j) s else 0 := by
  rw [term, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
  split_ifs <;> ring

private theorem coeff_term (c : ℚ) (n j : ℕ) :
    coeff n (term c j) = if n = j then c else 0 := coeff_C_mul_X_pow c j n

set_option maxRecDepth 15000 in
private theorem generating : mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 6 * X - 5 * X ^ 2)) = 1 - X ^ 2 - 10 * X ^ 3 := by
  have hD : (((1 - X) * (1 - 6 * X - 5 * X ^ 2)) : ℚ⟦X⟧) = term (1) 0 + term (-7) 1 + term (1) 2 + term (5) 3 := by simp only [term,map_neg,map_ofNat,map_one]; ring
  have hN : (1 - X ^ 2 - 10 * X ^ 3 : ℚ⟦X⟧) = term (1) 0 + term (-1) 2 + term (-10) 3 := by simp only [term,map_neg,map_ofNat,map_one]; ring
  rw [hD,hN]
  ext n
  simp only [mul_add,map_add,coeff_mulTerm,coeff_term,coeff_mk]
  by_cases hn : n ≤ 3
  · interval_cases n <;> simp only [a_zero,count_trace] <;> decide +kernel
  · obtain ⟨m,rfl⟩ : ∃ m, n = m+4 := ⟨n-4, by omega⟩
    simp only [Nat.zero_le, Nat.sub_zero, if_true, if_false,
      show 1 ≤ m+4 by omega, show 2 ≤ m+4 by omega, show 3 ≤ m+4 by omega,
      show m+4 ≠ 0 by omega, show m+4 ≠ 2 by omega, show m+4 ≠ 3 by omega,
      show m+4-1=m+3 by omega, show m+4-2=m+2 by omega, show m+4-3=m+1 by omega]
    linear_combination shifted m

private noncomputable def L : ℝ := (3 - Real.sqrt 14)
private noncomputable def R : ℝ := (3 + Real.sqrt 14)
private noncomputable def formula (n : ℕ) : ℝ := 1 + L ^ n + R ^ n

private theorem radicalSquare : Real.sqrt 14 ^ 2 = 14 := Real.sq_sqrt (by norm_num)

private theorem rootShift (x : ℝ) (hx : x^2 = 6*x+5) (m : ℕ) :
    x^(m+4) - 7*x^(m+3) + x^(m+2) + 5*x^(m+1) = 0 := by
  simp only [pow_add]
  linear_combination x^m * x * (x - 1) * hx

private theorem formulaRec (m : ℕ) :
    (1) * (formula (m+4) : ℝ) + (-7) * (formula (m+3) : ℝ) + (1) * (formula (m+2) : ℝ) + (5) * (formula (m+1) : ℝ) = 0 := by
  have hL : L^2 = 6*L+5 := by unfold L; nlinarith [radicalSquare]
  have hR : R^2 = 6*R+5 := by unfold R; nlinarith [radicalSquare]
  unfold formula
  linear_combination rootShift L hL m + rootShift R hR m

private theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = formula n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  suffices h : (a (m+1) : ℝ) = formula (m+1) ∧
      (a (m+2) : ℝ) = formula (m+2) ∧ (a (m+3) : ℝ) = formula (m+3) from h.1
  clear hn
  induction m with
  | zero =>
    have v1 : (a 1 : ℚ) = 7 := (count_trace 0).trans (by decide +kernel)
    have r1 : (a 1 : ℝ) = 7 := by exact_mod_cast v1
    have s1 : (a 1 : ℝ) = formula 1 := by
      rw [r1]; unfold formula L R; nlinarith [radicalSquare]
    have v2 : (a 2 : ℚ) = 47 := (count_trace 1).trans (by decide +kernel)
    have r2 : (a 2 : ℝ) = 47 := by exact_mod_cast v2
    have s2 : (a 2 : ℝ) = formula 2 := by
      rw [r2]; unfold formula L R; nlinarith [radicalSquare]
    have v3 : (a 3 : ℚ) = 307 := (count_trace 2).trans (by decide +kernel)
    have r3 : (a 3 : ℝ) = 307 := by exact_mod_cast v3
    have s3 : (a 3 : ℝ) = formula 3 := by
      rw [r3]; unfold formula L R; nlinarith [radicalSquare]
    exact ⟨s1,s2,s3⟩
  | succ m ih =>
    obtain ⟨h1,h2,h3⟩ := ih
    refine ⟨h2,h3,?_⟩
    have hA : (1) * (a (m+4) : ℝ) + (-7) * (a (m+3) : ℝ) + (1) * (a (m+2) : ℝ) + (5) * (a (m+1) : ℝ) = 0 := by exact_mod_cast shifted m
    rw [h1,h2,h3] at hA
    linarith [formulaRec m]

end OMA.CircularDigitWalks

open OMA.S_oeis_a125370 in
theorem OMA.solution : type_of% @OMA.S_oeis_a125370.main := by
  refine ⟨OMA.CircularDigitWalks.generating, OMA.CircularDigitWalks.closed, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m+4 := ⟨n-4, by omega⟩
  simp only [show m+4-1=m+3 by omega, show m+4-2=m+2 by omega, show m+4-3=m+1 by omega]
  have h : (1) * (a (m+4) : ℤ) + (-7) * (a (m+3) : ℤ) + (1) * (a (m+2) : ℤ) + (5) * (a (m+1) : ℤ) = 0 := by exact_mod_cast OMA.CircularDigitWalks.shifted m
  linear_combination h
