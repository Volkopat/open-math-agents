import OMAStatements.S_oeis_a241937
import Mathlib

namespace OMA.Tuples241937

open Finset OMA.S_oeis_a241937 PowerSeries

private abbrev Simplex (t : ℕ) := {x : Fin 5 → ℕ // ∑ i, x i ≤ t}

private def slack (t : ℕ) : Simplex t ≃
    {x : Fin 6 → ℕ // ∑ i, x i = t} where
  toFun x := ⟨Fin.cons (t-∑ i, x.val i) x.val, by
    rw [Fin.sum_univ_succ]; simp [Nat.sub_add_cancel x.property]⟩
  invFun x := ⟨fun i => x.val i.succ, by
    change ∑ i : Fin 5, x.val i.succ ≤ t
    have h := x.property
    rw [Fin.sum_univ_succ] at h
    omega⟩
  left_inv x := by rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    change t - ∑ j : Fin 5, x.val j.succ = x.val 0
    have h := x.property
    rw [Fin.sum_univ_succ] at h
    omega

private noncomputable def exactSum (t : ℕ) :
    {x : Fin 6 → ℕ // ∑ i, x i = t} ≃
      ↥((univ : Finset (Fin 6)).finsuppAntidiag t) where
  toFun x := ⟨Finsupp.equivFunOnFinite.symm x.val, by simpa using x.property⟩
  invFun x := ⟨x.val, (Finset.mem_finsuppAntidiag.mp x.property).1⟩
  left_inv _ := by rfl
  right_inv _ := by ext; rfl

private noncomputable instance (t : ℕ) : Fintype (Simplex t) :=
  Fintype.ofEquiv _ ((slack t).trans (exactSum t)).symm

private theorem simplex_card (t : ℕ) : Fintype.card (Simplex t) = (t+5).choose 5 := by
  rw [Fintype.card_congr ((slack t).trans (exactSum t)),Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ,Fintype.card_fin]
  rw [show 6+t-1=t+5 by omega,Nat.choose_symm_add]

private theorem coord {t : ℕ} (x : Simplex t) (i : Fin 5) : x.val i ≤ t :=
  (single_le_sum (f := x.val) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans x.property

private def small {t : ℕ} (n : ℕ) (x : Simplex t) := ∀ i, x.val i ≤ n

private theorem valid {n : ℕ} (x : Fin 5 → Fin (n+1)) :
    good x = true ↔ ∑ i, (x i).val ≤ 2*n := by
  simp only [good,decide_eq_true_eq,Nat.lt_one_iff,forall_eq,zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  simp [OMA.S_oeis_a241937.get]

private def bounded (n : ℕ) :
    {x : Fin 5 → Fin (n+1) // good x = true} ≃ {x : Simplex (2*n) // small n x} where
  toFun x := ⟨⟨fun i => (x.val i).val,(valid x.val).mp x.property⟩,
    fun i => Nat.le_of_lt_succ (x.val i).isLt⟩
  invFun x := ⟨fun i => ⟨x.val.val i, Nat.lt_succ_of_le (x.property i)⟩,
    (valid _).mpr x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def inc (n : ℕ) (i : Fin 5) (x : Fin 5 → ℕ) (j : Fin 5) :=
  x j + if j = i then n+1 else 0

private theorem inc_sum (n : ℕ) (i : Fin 5) (x : Fin 5 → ℕ) :
    ∑ j, inc n i x j = (∑ j, x j) + (n+1) := by simp [inc,sum_add_distrib]

private def largeMap (n : ℕ) (hn : 0 < n) (z : Fin 5 × Simplex (n-1)) :
    {x : Simplex (2*n) // ¬ small n x} :=
  ⟨⟨inc n z.1 z.2.val,by
    rw [inc_sum]
    have := z.2.property
    omega⟩,by
    intro h
    have hh := h z.1
    change inc n z.1 z.2.val z.1 ≤ n at hh
    simp [inc] at hh
    omega⟩

private theorem large_bij (n : ℕ) (hn : 0 < n) : Function.Bijective (largeMap n hn) := by
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ hh
    have eqn (k : Fin 5) : inc n i x.val k = inc n j y.val k :=
      congrArg (fun z => z.val.val k) hh
    have hij : i=j := by
      by_contra ne
      have h := eqn i
      simp [inc,ne] at h
      have := coord y i
      omega
    subst j
    have hxy : x=y := Subtype.ext (funext fun k => Nat.add_right_cancel (eqn k))
    rw [hxy]
  · intro z
    obtain ⟨i,hi⟩ : ∃ i, n < z.val.val i := by
      simpa [small, not_forall] using z.property
    let y (j : Fin 5) := z.val.val j - if j=i then n+1 else 0
    have restore : inc n i y = z.val.val := by
      funext j
      by_cases h : j=i
      · subst j; simp [inc,y,Nat.sub_add_cancel hi]
      · simp [inc,y,h]
    have hy : ∑ j, y j ≤ n-1 := by
      have h := inc_sum n i y
      rw [restore] at h
      have := z.val.property
      omega
    exact ⟨⟨i,⟨y,hy⟩⟩,Subtype.ext (Subtype.ext restore)⟩

private theorem count (n : ℕ) (hn : 0 < n) :
    a n + 5*((n-1+5).choose 5 : ℤ) = (2*n+5).choose 5 := by
  classical
  have split := Fintype.card_congr (Equiv.sumCompl (small n (t := 2*n)))
  rw [Fintype.card_sum,← Fintype.card_congr (bounded n),
    ← Fintype.card_congr (Equiv.ofBijective _ (large_bij n hn)),Fintype.card_prod,
    Fintype.card_fin,simplex_card,simplex_card,Fintype.card_subtype] at split
  unfold a
  exact_mod_cast split

private def rise (x : ℚ) : ℚ := (x+1)*(x+2)*(x+3)*(x+4)*(x+5)

private theorem choose_five (k : ℕ) : 120*((k+5).choose 5 : ℚ) = rise k := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose k 5
  norm_num [Nat.ascFactorial,Nat.factorial] at h
  unfold rise
  exact_mod_cast (show 120*(k+5).choose 5 = _ from by rw [← h]; ring)

private def P (x : ℚ) : ℚ := (rise (2*x) - 5*rise (x-1))/120

private theorem value (k : ℕ) : (a (k+1) : ℚ) = P (k+1) := by
  have h : (a (k+1) : ℚ) + 5*((k+5).choose 5 : ℚ) = ((2*(k+1)+5).choose 5 : ℚ) := by
    exact_mod_cast count (k+1) (by omega)
  have h1 := choose_five (2*(k+1))
  have h2 := choose_five k
  push_cast at h1
  unfold P
  rw [add_sub_cancel_right]
  linarith

private theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = 6*a (n-1)-15*a (n-2)+20*a (n-3)-15*a (n-4)+6*a (n-5)-a (n-6) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+7 := ⟨n-7,by omega⟩
  simp [value,P,rise]
  ring

private theorem generating :
    mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1-X)^6 : PowerSeries ℚ) =
    X*(16+21*X^2-15*X^3+6*X^4-X^5) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^6 = S - (6:ℕ) • (S*X^1) + (15:ℕ) • (S*X^2)
      - (20:ℕ) • (S*X^3) + (15:ℕ) • (S*X^4) - (6:ℕ) • (S*X^5) + S*X^6 := by
    simp only [nsmul_eq_mul]; ring
  have rhs : (X*(16+21*X^2-15*X^3+6*X^4-X^5) : PowerSeries ℚ) =
      (16:ℕ) • X^1 + (21:ℕ) • X^3 - (15:ℕ) • X^4 + (6:ℕ) • X^5 - X^6 := by
    simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 7 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),if_pos (show 6 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 3 by omega),if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),if_neg (show n ≠ 6 by omega)]
    norm_num
    linarith
  · have e1 := value 0
    have e2 := value 1
    have e3 := value 2
    have e4 := value 3
    have e5 := value 4
    have e6 := value 5
    norm_num [P,rise] at e1 e2 e3 e4 e5 e6
    interval_cases n <;> norm_num [e1,e2,e3,e4,e5,e6]

theorem result : type_of% @OMA.S_oeis_a241937.main := ⟨generating,recurrence⟩

end OMA.Tuples241937

theorem OMA.solution : type_of% @OMA.S_oeis_a241937.main := OMA.Tuples241937.result
