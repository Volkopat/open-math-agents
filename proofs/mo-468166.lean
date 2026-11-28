import OMAStatements.S_mo_468166
import Mathlib

open MvPolynomial Finset OMA.S_mo_468166

private theorem small_monomial {d : ℕ} (m : Fin d →₀ ℕ)
    (h : ∑ i ∈ m.support, m i ≤ 1) :
    m=0 ∨ ∃ i, m=Finsupp.single i 1 := by
  by_cases h0 : m=0
  · exact Or.inl h0
  right
  have hcard : m.support.card ≤ 1 := by
    calc
      _ = ∑ _i ∈ m.support, (1:ℕ) := by simp
      _ ≤ ∑ i ∈ m.support, m i :=
        sum_le_sum (fun i hi => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
      _ ≤ 1 := h
  have hpos : 0 < m.support.card :=
    Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr h0)
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (show m.support.card=1 by omega)
  have hmj : m j = 1 := by
    have hz : m j ≠ 0 := Finsupp.mem_support_iff.mp (by simp [hj])
    rw [hj,Finset.sum_singleton] at h
    omega
  refine ⟨j, ?_⟩
  ext i
  by_cases hi : i=j
  · subst i
    simpa using hmj
  · have hni : i ∉ m.support := by simp [hj,hi]
    have hzi : m i = 0 := Finsupp.notMem_support_iff.mp hni
    simp [hi,hzi]

private theorem affine_expansion {d : ℕ} (g : MvPolynomial (Fin d) ℂ) (hg : g.totalDegree=1) :
    g = C (g.coeff 0) + ∑ i, C (g.coeff (Finsupp.single i 1)) * X i := by
  classical
  ext m
  simp only [coeff_add,coeff_sum,coeff_C_mul,coeff_C,coeff_X]
  by_cases hl : (∑ i ∈ m.support,m i) ≤ 1
  · rcases small_monomial m hl with h0 | ⟨j,hj⟩
    · subst m
      simp [Finsupp.single_eq_zero]
    · subst m
      have hj0 : Finsupp.single j (1:ℕ) ≠ 0 := by simp
      rw [if_neg (Ne.symm hj0),zero_add]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        have he : Finsupp.single i (1:ℕ) ≠ Finsupp.single j 1 := by
          intro h
          have h' := congrArg (fun x : Fin d →₀ ℕ => x i) h
          simp [Ne.symm hij] at h'
        simp [he]
      · simp
  · have h0 : m ≠ 0 := fun h => hl (by simp [h])
    have hs (i : Fin d) : Finsupp.single i (1:ℕ) ≠ m := by
      intro h
      exact hl (by rw [← h]; simp)
    have hz : g.coeff m=0 := coeff_eq_zero_of_totalDegree_lt (by rw [hg]; omega)
    simp [Ne.symm h0,hs,hz]

private theorem affine_eval {d : ℕ} (g : MvPolynomial (Fin d) ℂ) (hg : g.totalDegree=1) :
    ∃ c : ℂ, ∃ a : Fin d → ℂ, (∃ i,a i ≠ 0) ∧
      ∀ v, eval v g = c + ∑ i, a i*v i := by
  let c := g.coeff 0
  let a : Fin d → ℂ := fun i => g.coeff (Finsupp.single i 1)
  have he := affine_expansion g hg
  change g = C c + ∑ i, C (a i)*X i at he
  refine ⟨c,a,?_,?_⟩
  · by_contra! h
    rw [show g = C c by rw [he]; simp [h],totalDegree_C] at hg
    contradiction
  · intro v
    rw [he]
    simp

private def vector {d : ℕ} (i : Fin d) (s : Finset (Fin d)) (v : Fin d → ℂ) (z : ℂ) :
    Fin d → ℂ := fun j => if j=i then z else if j∈s then v j else 0

private theorem vector_sum {d : ℕ} {s : Finset (Fin d)} {i : Fin d}
    (hi : i ∉ s) (v : Fin d → ℂ) (z : ℂ)
    (f : Fin d → ℂ → ℂ) (h0 : ∀ j,f j 0 = 0) :
    (∑ j, f j (vector i s v z j)) = f i z + ∑ j ∈ s, f j (v j) := by
  classical
  calc
    _ = ∑ j ∈ insert i s, f j (vector i s v z j) := by
      symm
      apply sum_subset (subset_univ _)
      intro j _ hj
      have he : j ≠ i ∧ j ∉ s := by simpa using hj
      simp [vector,he.1,he.2,h0]
    _ = _ := by
      rw [sum_insert hi]
      rw [show vector i s v z i = z by simp [vector]]
      congr 1
      apply sum_congr rfl
      intro j hj
      have hji : j ≠ i := fun e => hi (e ▸ hj)
      simp [vector,hji,hj]

private theorem eval_form {d n : ℕ} (x : Fin d → ℂ) :
    eval x (form d n) = 2*(∑ j, x j^(2*n))-(∑ j, x j^n)^2 := by
  unfold form
  simp

theorem OMA.solution : type_of% @OMA.S_mo_468166.main := by
  classical
  intro m n hn sign
  rintro ⟨ls,hl,he⟩
  cases ls with
  | nil =>
    have hh := congrArg (eval (0 : Fin (4+m) → ℂ)) he
    have hz : eval (0 : Fin (4+m) → ℂ) (form (4+m) n) = 0 := by
      rw [eval_form]
      simp [zero_pow (by omega : 2*n ≠ 0),zero_pow hn.ne']
    cases sign
    · change eval (0 : Fin (4+m) → ℂ) 1 = eval (0 : Fin (4+m) → ℂ) (form (4+m) n) at hh
      rw [map_one,hz] at hh
      exact one_ne_zero hh
    · change eval (0 : Fin (4+m) → ℂ) 1 = eval (0 : Fin (4+m) → ℂ) (-form (4+m) n) at hh
      rw [map_one,map_neg,hz,neg_zero] at hh
      exact one_ne_zero hh
  | cons g ls =>
    obtain ⟨c,a,⟨i,hi⟩,ha⟩ := affine_eval g (hl g (by simp))
    have vanishes (x : Fin (4+m) → ℂ) (hx : eval x g=0) :
        eval x (form (4+m) n) = 0 := by
      have hh := congrArg (eval x) he
      rw [List.prod_cons,map_mul,hx,zero_mul] at hh
      cases sign <;> simpa using hh.symm
    have hc : c=0 := by
      let z : ℂ := -c/a i
      let x := vector i ∅ (fun _ => 0) z
      have hx : eval x g=0 := by
        rw [ha]
        change c + (∑ j, a j*vector i ∅ (fun _ => 0) z j)=0
        rw [vector_sum (by simp) _ _ (fun j v => a j*v) (fun _ => mul_zero _),sum_empty,add_zero]
        dsimp [z]
        field_simp [hi]
        ring
      have hh := vanishes x hx
      rw [eval_form] at hh
      change 2*(∑ j, vector i ∅ (fun _ => 0) z j^(2*n)) -
        (∑ j, vector i ∅ (fun _ => 0) z j^n)^2 = 0 at hh
      rw [vector_sum (by simp) _ _ (fun _ v => v^(2*n)) (fun _ => zero_pow (by omega)),
        vector_sum (by simp) _ _ (fun _ v => v^n) (fun _ => zero_pow hn.ne')] at hh
      simp only [sum_empty,add_zero,show 2*n=n*2 by omega,pow_mul] at hh
      have hz : (z^n)^2=0 := by linear_combination hh
      have hzero : z = 0 := by
        by_contra h
        exact pow_ne_zero _ (pow_ne_zero _ h) hz
      dsimp [z] at hzero
      exact neg_eq_zero.mp ((div_eq_zero_iff.mp hzero).resolve_right hi)
    let b : Fin (4+m) → ℂ := fun j => -a j/a i
    have root (j : Fin (4+m)) (hj : j ≠ i) : (b j)^n=1 := by
      let x := vector i {j} (fun _ => 1) (b j)
      have his : i ∉ ({j} : Finset (Fin (4+m))) := by simp [Ne.symm hj]
      have hx : eval x g=0 := by
        rw [ha,hc,zero_add]
        change (∑ k, a k*vector i {j} (fun _ => 1) (b j) k)=0
        rw [vector_sum his _ _ (fun k v => a k*v) (fun _ => mul_zero _),sum_singleton,mul_one]
        dsimp [b]
        field_simp [hi]
        ring
      have hh := vanishes x hx
      rw [eval_form] at hh
      change 2*(∑ k, vector i {j} (fun _ => 1) (b j) k^(2*n)) -
        (∑ k, vector i {j} (fun _ => 1) (b j) k^n)^2=0 at hh
      rw [vector_sum his _ _ (fun _ v => v^(2*n)) (fun _ => zero_pow (by omega)),
        vector_sum his _ _ (fun _ v => v^n) (fun _ => zero_pow hn.ne')] at hh
      simp only [sum_singleton,one_pow,show 2*n=n*2 by omega,pow_mul] at hh
      have hq : ((b j)^n-1)^2=0 := by linear_combination hh
      exact sub_eq_zero.mp (by
        by_contra h
        exact pow_ne_zero _ h hq)
    have card_test (S : Finset (Fin (4+m))) (his : i ∉ S) :
        2*(((S.card:ℂ)^n)^2+(S.card:ℂ))-((S.card:ℂ)^n+(S.card:ℂ))^2=0 := by
      let v : Fin (4+m) → ℂ := fun j => (b j)⁻¹
      let x := vector i S v (S.card:ℂ)
      have vpow (j : Fin (4+m)) (hj : j ∈ S) : (v j)^n=1 := by
        dsimp [v]
        rw [inv_pow,root j (fun e => his (e ▸ hj)),inv_one]
      have vc (j : Fin (4+m)) (hj : j ∈ S) : a j*v j = -a i := by
        have hb : b j ≠ 0 := by
          intro h
          have he := root j (fun e => his (e ▸ hj))
          simp [h,zero_pow hn.ne'] at he
        have he : a j = -(b j*a i) := by
          dsimp [b]
          field_simp [hi]
        rw [he]
        dsimp [v]
        field_simp [hb]
      have hx : eval x g=0 := by
        rw [ha,hc,zero_add]
        change (∑ j, a j*vector i S v (S.card:ℂ) j)=0
        rw [vector_sum his _ _ (fun j u => a j*u) (fun _ => mul_zero _)]
        have hsum : ∑ j ∈ S, a j*v j = ∑ _j ∈ S, -a i := sum_congr rfl vc
        rw [hsum,sum_const,nsmul_eq_mul]
        ring
      have hh := vanishes x hx
      rw [eval_form] at hh
      change 2*(∑ j, vector i S v (S.card:ℂ) j^(2*n)) -
        (∑ j, vector i S v (S.card:ℂ) j^n)^2=0 at hh
      rw [vector_sum his _ _ (fun _ u => u^(2*n)) (fun _ => zero_pow (by omega)),
        vector_sum his _ _ (fun _ u => u^n) (fun _ => zero_pow hn.ne')] at hh
      have h₁ : ∑ j ∈ S, (v j)^n = (S.card:ℂ) := by
        rw [sum_congr rfl (fun j hj => vpow j hj)]
        simp
      have h₂ : ∑ j ∈ S, (v j)^(2*n) = (S.card:ℂ) := by
        simp_rw [show 2*n=n*2 by omega,pow_mul]
        rw [sum_congr rfl (fun j hj => by rw [vpow j hj,one_pow])]
        simp
      rw [h₁,h₂,show 2*n=n*2 by omega,pow_mul] at hh
      exact hh
    let u : Finset (Fin (4+m)) := univ.erase i
    have hu : 3 ≤ u.card := by simp [u,Finset.card_erase_of_mem]
    obtain ⟨S,hSu,hS⟩ := Finset.exists_subset_card_eq (s:=u) (n:=2) (by omega)
    have hiS : i ∉ S := fun h => by simpa [u] using hSu h
    have htest := card_test S hiS
    rw [hS] at htest
    norm_num only [Nat.cast_ofNat] at htest
    have hm₂ : ((2:ℂ)^n)*((2:ℂ)^n-4)=0 := by linear_combination htest
    have hb₂ : (2:ℂ)^n = 4 := sub_eq_zero.mp
      ((mul_eq_zero.mp hm₂).resolve_left (pow_ne_zero _ (by norm_num)))
    have hn₂ : (2:ℕ)^n = 2^2 := by exact_mod_cast hb₂
    have he₂ : n=2 := (Nat.pow_right_injective (by decide : 1 < (2:ℕ))) hn₂
    obtain ⟨T,hTu,hT⟩ := Finset.exists_subset_card_eq (s:=u) (n:=3) hu
    have hiT : i ∉ T := fun h => by simpa [u] using hTu h
    have hf := card_test T hiT
    norm_num [he₂,hT] at hf