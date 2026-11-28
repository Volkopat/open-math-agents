import OMAStatements.S_oeis_a127750

-- Credit: @oh-meh
open OMA.S_oeis_a127750 Matrix Finset

private def sumBefore : ℕ → ℤ
  | 0 => 0
  | n+1 => 2*n+1+sumBefore ((n+1)/2)

private def u (n : ℕ) : ℤ := sumBefore (n+1)-sumBefore n

private theorem sumBefore_succ (n : ℕ) : sumBefore (n+1) = 2*n+1+sumBefore ((n+1)/2) := by
  rw [sumBefore]

private theorem base_u : u 0 = 1 := by norm_num [u,sumBefore]

private theorem even_u (k : ℕ) (hk : 0<k) : u (2*k) = 2 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  unfold u
  rw [sumBefore_succ, show 2*(j+1)=2*j+1+1 by omega, sumBefore_succ (2*j+1)]
  rw [show (2*j+1+1+1)/2=j+1 by omega, show (2*j+1+1)/2=j+1 by omega]
  push_cast
  ring

private theorem odd_u (k : ℕ) : u (2*k+1) = 2+u k := by
  unfold u
  rw [sumBefore_succ (2*k+1), sumBefore_succ (2*k)]
  rw [show (2*k+1+1)/2=k+1 by omega,show (2*k+1)/2=k by omega]
  push_cast
  ring

private theorem rows (N : ℕ) (i : Fin N) : a N i = (u i.val : ℚ) := by
  classical
  let A := triangle N
  let v : Fin N → ℚ := fun k => u k.val
  have hsum (m : ℕ) : ∑ j ∈ range m, (u j:ℚ) = (sumBefore m:ℚ) := by
    induction m with
    | zero => simp [sumBefore]
    | succ m ih => rw [sum_range_succ,ih,u,Int.cast_sub]; ring
  have hdiag : A.IsLowerTriangular := by
    intro j k h
    have hk : ¬ k.val ≤ j.val := by exact not_le_of_gt (show j.val<k.val from h)
    simp [A,triangle,hk]
  have hunit : IsUnit A.det := by
    rw [A.det_of_isLowerTriangular hdiag, isUnit_iff_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    simp [A,triangle,show j.val≤2*j.val by omega]
    positivity
  have hv : A *ᵥ v = fun _ => 1 := by
    funext j
    change (∑ k : Fin N, (if k.val≤j.val ∧ j.val≤2*k.val then (1:ℚ)/(2*j.val+1) else 0) * (u k.val:ℚ))=1
    simp only [ite_mul,zero_mul]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k ≤ j.val ∧ j.val ≤ 2*k then
      (1:ℚ)/(2*j.val+1)*(u k:ℚ) else 0), ← Finset.sum_filter]
    have hf : (range N).filter (fun k => k ≤ j.val ∧ j.val ≤ 2*k) = Ico ((j.val+1)/2) (j.val+1) := by
      ext k
      simp only [mem_filter,mem_range,mem_Ico]
      have := j.isLt
      omega
    rw [hf, ← mul_sum, sum_Ico_eq_sub _ (by omega),hsum,hsum,sumBefore_succ j.val]
    push_cast
    field_simp
    ring
  have hinv := congrArg (fun w => A⁻¹ *ᵥ w) hv
  rw [mulVec_mulVec,nonsing_inv_mul _ hunit,one_mulVec] at hinv
  simpa [a,A,v,mulVec,dotProduct] using (congrFun hinv i).symm

private theorem parity (n : ℕ) : u n % 2 = (A036987 n:ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      simp [base_u,A036987,show ∃ m : ℕ, 0=2^m-1 from ⟨0,rfl⟩]
    rcases Nat.even_or_odd n with ⟨x,hx⟩ | ⟨x,hx⟩
    · have hx' : n=2*x := by omega
      have ha : ¬∃ m : ℕ, n=2^m-1 := by
        rintro ⟨m,hm⟩
        cases m with
        | zero => norm_num at hm; omega
        | succ m => rw [pow_succ] at hm; have := Nat.two_pow_pos m; omega
      rw [A036987, if_neg ha, hx', even_u _ (by omega)]
      decide
    · have hx' : n=2*x+1 := by omega
      have hind := ih x (by omega)
      have equiv : (∃ m : ℕ, n=2^m-1) ↔ (∃ m : ℕ, x=2^m-1) := by
        constructor
        · rintro ⟨m,hm⟩
          cases m with
          | zero => norm_num at hm; omega
          | succ m => refine ⟨m,?_⟩; rw [pow_succ] at hm; have := Nat.two_pow_pos m; omega
        · rintro ⟨m,hm⟩; refine ⟨m+1,?_⟩; rw [pow_succ]; have := Nat.two_pow_pos m; omega
      have ha : A036987 n = A036987 x := by
        by_cases yes : ∃ m : ℕ, x=2^m-1
        · simp [A036987,yes,equiv.mpr yes]
        · simp [A036987,yes,mt equiv.mp yes]
      rw [ha,← hind,hx',odd_u]
      omega

theorem OMA.solution : type_of% @OMA.S_oeis_a127750.main := by
  intro N n
  exact ⟨u n,rows N n,parity n⟩
