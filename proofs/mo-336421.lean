import OMAStatements.S_mo_336421

namespace OMA.S_mo_336421
open Polynomial Matrix
variable {K : Type*} [Field K] [CharZero K]
private lemma top_data {P : K[X]} (hP : P ≠ 0) {s : ℕ} (hs : s ≤ P.natDegree) :
    (derivative^[s] P).natDegree=P.natDegree-s ∧ (derivative^[s] P).leadingCoeff ≠ 0 := by
  have h : (derivative^[s] P).coeff (P.natDegree-s) ≠ 0 := by
    rw [coeff_iterate_derivative,Nat.sub_add_cancel hs,nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast (Nat.descFactorial_pos.mpr hs).ne') (leadingCoeff_ne_zero.mpr hP)
  exact ⟨le_antisymm (natDegree_iterate_derivative _ _) (le_natDegree_of_ne_zero h),
    leadingCoeff_ne_zero.mpr fun e => h (by simp [e])⟩
private noncomputable def entry (P : K[X]) (s : ℕ) (b c : K) : K[X] :=
  C (b^s*c^(P.natDegree-s)) * ((derivative^[s] P).reverse.comp (C c⁻¹ * X))
private lemma entry_zero (P : K[X]) {s : ℕ} (hs : s≤P.natDegree) (b c : K) (hc : c≠0) :
    (entry P s b c).eval 0 = (derivative^[s] P).leadingCoeff * (c^P.natDegree * (b/c)^s) := by
  simp only [entry,eval_mul,eval_C,eval_comp,eval_X,mul_zero,← coeff_zero_eq_eval_zero,coeff_zero_reverse]
  rw [pow_sub₀ c hc hs,div_pow]
  ring
private lemma entry_at (P : K[X]) (hP : P≠0) {s : ℕ} (hs : s≤P.natDegree) (b c t : K) (hc : c≠0) (ht : t≠0) :
    (entry P s b c).eval t = t^(P.natDegree-s) * (b^s*(derivative^[s] P).eval (c/t)) := by
  let Q := derivative^[s] P
  let q := P.natDegree-s
  have hd : Q.natDegree=q := (top_data hP hs).1
  have hc' : c/t≠0 := div_ne_zero hc ht
  let _ := invertibleOfNonzero hc'
  have hv := Polynomial.eval₂_reverse_mul_pow (RingHom.id K) (c/t) Q
  simp only [eval₂_id,invOf_eq_inv,inv_div,hd] at hv
  have hcq : c^q=(c/t)^q*t^q := by rw [←mul_pow,div_mul_cancel₀ _ ht]
  change (C (b^s*c^q) * (Q.reverse.comp (C c⁻¹*X))).eval t = t^q*(b^s*Q.eval (c/t))
  rw [eval_mul,eval_C,eval_comp,eval_mul,eval_C,eval_X,show c⁻¹*t=t/c by ring,hcq,←hv]
  ring
end OMA.S_mo_336421

namespace OMA.S_mo_336421
open Polynomial Matrix
variable {K : Type*} [Field K] [CharZero K]
lemma generic_minor {n r : ℕ} (P : K[X]) (hP : P ≠ 0) (b c : Fin n → K)
    (hr : r≤P.natDegree+1) (j : Fin r → Fin n × Fin n)
    (hc : ∀ k,c (j k).2 ≠ 0) (hj : Function.Injective (fun k => b (j k).1/c (j k).2)) :
    ∃ bad : Finset K, ∀ t ∉ bad,
      ((grid P b (fun k => c k/t)).submatrix (Fin.castLE hr) j).det ≠ 0 ∧
      r ≤ (grid P b (fun k => c k/t)).rank := by
  classical
  let a (i : Fin r) := (derivative^[i.val] P).leadingCoeff
  let z (k : Fin r) := c (j k).2
  let u (k : Fin r) := b (j k).1/z k
  let A : Matrix (Fin r) (Fin r) K[X] := Matrix.of fun i k => entry P i.val (b (j k).1) (z k)
  have hi (i : Fin r) : i.val ≤ P.natDegree := by have := i.isLt; omega
  have hz (k : Fin r) : z k ≠ 0 := hc k
  have h0 : (evalRingHom 0).mapMatrix A =
      Matrix.of (fun i k => a i * (Matrix.of (fun l m => z m^P.natDegree * (vandermonde u)ᵀ l m)) i k) := by
    ext i k
    exact entry_zero _ (hi i) _ _ (hz k)
  have hd : A.det ≠ 0 := by
    intro he
    have hspec := (evalRingHom (0:K)).map_det A
    rw [he,map_zero,h0,det_mul_column,det_mul_row,det_transpose] at hspec
    exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (top_data hP (hi i)).2)
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hz k))
        (det_vandermonde_ne_zero_iff.mpr hj))) hspec.symm
  refine ⟨insert 0 A.det.roots.toFinset,?_⟩
  intro t ht
  have ht0 : t≠0 := fun e => ht (by simp [e])
  have heval : (evalRingHom t) A.det ≠ 0 := by
    intro h
    exact ht (Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd).mpr h)))
  let row (i : Fin r) : Fin (P.natDegree+1) := ⟨i,by have := hi i; omega⟩
  let M := grid P b (fun k => c k/t)
  let N := M.submatrix row j
  have hat : (evalRingHom t).mapMatrix A =
      Matrix.of fun i k => t^(P.natDegree-i.val)*N i k := by
    ext i k
    exact entry_at _ hP (hi i) _ _ _ (hz k) ht0
  have hN : N.det ≠ 0 := by
    intro h
    apply heval
    rw [RingHom.map_det,hat,det_mul_column,h,mul_zero]
  have hrank := N.rank_of_isUnit (N.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hN))
  have hle := M.rank_submatrix_le row j
  change N.rank ≤ _ at hle
  exact ⟨hN,by simpa [hrank] using hle⟩
end OMA.S_mo_336421

namespace OMA.S_mo_336421

lemma quotient_grid (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    ∃ b c : Fin n → K, Function.Injective b ∧ Function.Injective c ∧ (∀ i,c i ≠ 0) ∧
      Function.Injective (fun j : Fin n × Fin n => b j.1 / c j.2) := by
  let p (e : ℕ) : K := (2 : K)^e
  have hp : Function.Injective p := by
    intro i j h
    have he : (2:ℕ)^i=2^j := by exact_mod_cast (show (2:K)^i=2^j from h)
    exact Nat.pow_right_injective (by decide : 2≤2) he
  have hne (j : ℕ) : p j≠0 := pow_ne_zero _ (by norm_num)
  refine ⟨fun i => p (n*i.val), fun j => p j.val, ?_, fun i j h => Fin.ext (hp h), fun i => hne _,?_⟩
  · intro i j h
    exact Fin.ext ((Nat.mul_left_cancel (Nat.zero_lt_of_lt i.isLt)) (hp h))
  · rintro ⟨i,j⟩ ⟨k,l⟩ h
    change p (n*i.val) / p j.val = p (n*k.val) / p l.val at h
    have hh := (div_eq_div_iff (hne _) (hne _)).mp h
    change (2:K)^(n*i.val) * 2^l.val = 2^(n*k.val) * 2^j.val at hh
    rw [←pow_add,←pow_add] at hh
    have he : n*i.val+l.val=n*k.val+j.val := hp hh
    have hj : l.val=j.val := by
      have hmod := congrArg (fun t => t % n) he
      simpa [Nat.add_mod,Nat.mod_eq_of_lt l.isLt,Nat.mod_eq_of_lt j.isLt] using hmod
    have hi : i.val=k.val := Nat.mul_left_cancel (Nat.zero_lt_of_lt i.isLt) (by omega)
    exact Prod.ext (Fin.ext hi) (Fin.ext hj.symm)

noncomputable def pairColumns (d n : ℕ) : Fin (min (d+1) (n*n)) ↪ Fin n × Fin n :=
  (Fin.castLEEmb (Nat.min_le_right _ _)).trans finProdFinEquiv.symm.toEmbedding

end OMA.S_mo_336421

namespace OMA.S_mo_336421
open Polynomial Matrix
variable {K : Type*} [Field K] [CharZero K]

lemma generic_rank (n : ℕ) (P : K[X]) (hP : P≠0) :
    ∃ D : MvPolynomial (Fin n ⊕ Fin n) K, D≠0 ∧
      (∀ b c : Fin n → K, MvPolynomial.eval (Sum.elim b c) D ≠ 0 →
        (grid P b c).rank=min (P.natDegree+1) (n*n)) ∧
      ∃ b c : Fin n → K, Function.Injective b ∧ Function.Injective c ∧
        MvPolynomial.eval (Sum.elim b c) D ≠ 0 := by
  classical
  let r := min (P.natDegree+1) (n*n)
  have hr : r≤P.natDegree+1 := Nat.min_le_left _ _
  let j := pairColumns P.natDegree n
  let A : Matrix (Fin r) (Fin r) (MvPolynomial (Fin n ⊕ Fin n) K) := Matrix.of fun i k =>
    MvPolynomial.X (Sum.inl (j k).1)^i.val *
    (derivative^[i.val] P).eval₂ MvPolynomial.C (MvPolynomial.X (Sum.inr (j k).2))
  have spec (b c : Fin n → K) : MvPolynomial.eval (Sum.elim b c) A.det =
      ((grid P b c).submatrix (Fin.castLE hr) j).det := by
    rw [RingHom.map_det]
    congr 1
    ext i k
    change MvPolynomial.eval (Sum.elim b c) (_ * _) = _
    rw [map_mul,map_pow,MvPolynomial.eval_X,Polynomial.hom_eval₂,MvPolynomial.eval_X]
    have he : (MvPolynomial.eval (Sum.elim b c)).comp MvPolynomial.C=RingHom.id K := by ext; simp
    rw [he]
    rfl
  obtain ⟨b,c,hb,hc,hcz,hbc⟩ := quotient_grid K n
  obtain ⟨bad,hbad⟩ := generic_minor P hP b c hr j (fun k => hcz _) (hbc.comp j.injective)
  obtain ⟨t,ht⟩ := (insert 0 bad).exists_notMem
  have ht0 : t≠0 := fun e => ht (by simp [e])
  have hminor := (hbad t (fun h => ht (Finset.mem_insert_of_mem h))).1
  have hgood : MvPolynomial.eval (Sum.elim b (fun k => c k/t)) A.det ≠ 0 := by rwa [spec]
  refine ⟨A.det,fun e => hgood (by simp [e]),?_,b,fun k => c k/t,hb,?_,hgood⟩
  · intro B C hv
    rw [spec] at hv
    let M := grid P B C
    let S := M.submatrix (Fin.castLE hr) j
    have hS := S.rank_of_isUnit (S.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hv))
    apply le_antisymm
    · apply le_min
      · simpa [M] using M.rank_le_card_height
      · simpa [M] using M.rank_le_card_width
    · have hh := M.rank_submatrix_le (Fin.castLE hr) j
      change S.rank ≤ M.rank at hh
      change r ≤ M.rank
      simpa only [hS,Fintype.card_fin] using hh
  · intro i k he
    exact hc ((div_left_inj' ht0).mp he)
end OMA.S_mo_336421

open OMA.S_mo_336421
theorem OMA.solution : type_of% @OMA.S_mo_336421.main := by
  intro K _ _ n P hP
  refine ⟨generic_rank n P hP,?_⟩
  intro b c r hr j hc hj
  obtain ⟨bad,h⟩ := generic_minor P hP b c hr j hc hj
  exact ⟨bad,fun t ht => (h t ht).2⟩
