import OMAStatements.S_oeis_a124699

namespace OMA.CircularDigitWalks
open OMA.S_oeis_a124699 Finset PowerSeries

private abbrev Digit := Fin 6
private abbrev Word (n : ℕ) := Fin n → Digit

private def edge (u v : Digit) : Prop := Int.natAbs ((u : ℤ) - (v : ℤ)) ≤ 1

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
  classical
  let good (w : Word (n+1)) := ∀ i : Fin (n+1),
    edge (w i) (w ⟨(i.val+1) % (n+1), Nat.mod_lt _ (Nat.succ_pos _)⟩)
  have hcount : (a (n+1) : ℚ) = ∑ w : Word (n+1), if good w then 1 else 0 := by
    simp only [a, Int.cast_natCast, edge, decide_eq_true_eq, good]
    exact (Finset.sum_boole _ _).symm
  rw [hcount, sum_head, Matrix.trace]
  change _ = ∑ d, (transition^(n+1)) d d
  apply sum_congr rfl
  intro d _
  rw [← path_sum]
  apply sum_congr rfl
  intro w _
  exact if_congr (cycle_path d w).symm rfl rfl

private theorem a_zero : a 0 = 1 := by decide +kernel

set_option maxRecDepth 15000 in
private theorem matrixRelation : (1 : ℚ) • transition ^ 7 + (-6 : ℚ) • transition ^ 6 + (10 : ℚ) • transition ^ 5 + (-9 : ℚ) • transition ^ 3 + (2 : ℚ) • transition ^ 2 + (1 : ℚ) • transition ^ 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem shifted (m : ℕ) : (1) * (a (m+7) : ℚ) + (-6) * (a (m+6) : ℚ) + (10) * (a (m+5) : ℚ) + (-9) * (a (m+3) : ℚ) + (2) * (a (m+2) : ℚ) + (1) * (a (m+1) : ℚ) = 0 := by
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
private theorem generating : mk (fun n => (a n : ℚ)) * ((1 - 2 * X - X ^ 2 + X ^ 3) * (1 - 4 * X + 3 * X ^ 2 + X ^ 3)) = 1 - 10 * X ^ 2 + 27 * X ^ 4 - 8 * X ^ 5 - 5 * X ^ 6 := by
  have hD : (((1 - 2 * X - X ^ 2 + X ^ 3) * (1 - 4 * X + 3 * X ^ 2 + X ^ 3)) : ℚ⟦X⟧) = term (1) 0 + term (-6) 1 + term (10) 2 + term (-9) 4 + term (2) 5 + term (1) 6 := by simp only [term,map_neg,map_ofNat,map_one]; ring
  have hN : (1 - 10 * X ^ 2 + 27 * X ^ 4 - 8 * X ^ 5 - 5 * X ^ 6 : ℚ⟦X⟧) = term (1) 0 + term (-10) 2 + term (27) 4 + term (-8) 5 + term (-5) 6 := by simp only [term,map_neg,map_ofNat,map_one]; ring
  rw [hD,hN]
  ext n
  simp only [mul_add,map_add,coeff_mulTerm,coeff_term,coeff_mk]
  by_cases hn : n ≤ 6
  · interval_cases n <;> simp only [a_zero,count_trace] <;> decide +kernel
  · obtain ⟨m,rfl⟩ : ∃ m, n = m+7 := ⟨n-7, by omega⟩
    simp only [Nat.zero_le, Nat.sub_zero, if_true, if_false,
      show 1 ≤ m+7 by omega, show 2 ≤ m+7 by omega, show 4 ≤ m+7 by omega,
      show 5 ≤ m+7 by omega, show 6 ≤ m+7 by omega, show m+7 ≠ 0 by omega,
      show m+7 ≠ 2 by omega, show m+7 ≠ 4 by omega, show m+7 ≠ 5 by omega,
      show m+7 ≠ 6 by omega, show m+7-1=m+6 by omega, show m+7-2=m+5 by omega,
      show m+7-4=m+3 by omega, show m+7-5=m+2 by omega, show m+7-6=m+1 by omega]
    linear_combination shifted m

end OMA.CircularDigitWalks

open OMA.S_oeis_a124699 in
theorem OMA.solution : type_of% @OMA.S_oeis_a124699.main := by
  refine ⟨OMA.CircularDigitWalks.generating, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m+7 := ⟨n-7, by omega⟩
  simp only [show m+7-1=m+6 by omega, show m+7-2=m+5 by omega, show m+7-4=m+3 by omega, show m+7-5=m+2 by omega, show m+7-6=m+1 by omega]
  linear_combination OMA.CircularDigitWalks.shifted m
