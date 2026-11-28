import OMAStatements.S_mo_348427

namespace OMA.S_mo_348427
open Matrix Finset
open scoped Matrix

private def flipAll {n : ℕ} (v : Vertex n) : Vertex n := fun j => !(v j)
private def neighbor {n : ℕ} (v : Vertex n) (i : Fin n) : Vertex n :=
  fun j => if j=i then !(v j) else v j
private def intSign (a : Bool) : ℤ := if a then 1 else -1
private def idot {n : ℕ} (v w : Vertex n) : ℤ := ∑ j, intSign (v j)*intSign (w j)

private lemma cover_small {n : ℕ} (hn : n ≤ 3) :
    ∀ a v : Vertex n, (v=a ∨ v=flipAll a) ∨
      ∃ i : Fin n, v=neighbor a i ∨ v=flipAll (neighbor a i) := by
  interval_cases n <;> decide

private lemma near_small {n : ℕ} (hn : n ≤ 3) :
    ∀ (a b u : Vertex n) (i : Fin n), idot b u=idot a (neighbor a i) →
      ∃ j : Fin n, u=neighbor b j := by
  interval_cases n <;> decide

private lemma s_inj {n : ℕ} : Function.Injective (@sign n) := by
  intro v w h
  funext j
  have hj := congrFun h j
  cases hv : v j <;> cases hw : w j <;> first | rfl | norm_num [sign,hv,hw] at hj
private lemma nb_inj {n : ℕ} (a : Vertex n) : Function.Injective (neighbor a) := by
  intro i j h
  by_contra hn
  have he := congrFun h i
  cases hv : a i <;> simp [neighbor,hn,hv] at he
private lemma sign_flip {n : ℕ} (v : Vertex n) : sign (flipAll v)= -sign v := by
  funext j
  cases h : v j <;> simp [sign,flipAll,h]
private lemma dot_int {n : ℕ} (v w : Vertex n) :
    (idot v w : ℝ)=sign v ⬝ᵥ sign w := by
  unfold idot dotProduct
  push_cast
  apply sum_congr rfl
  intro i _
  cases hv : v i <;> cases hw : w i <;> norm_num [intSign,sign,hv,hw]

private lemma orth_dot {n : ℕ} (Q : Mat n) (hQ : Qᵀ*Q=1) (u v : Fin n → ℝ) :
    (Q *ᵥ u) ⬝ᵥ (Q*ᵥ v) = u ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,Matrix.mulVec_mulVec,hQ,Matrix.one_mulVec]

private lemma axis_match {n : ℕ} (hn : n ≤ 3) (Q : Mat n) (hQ : Qᵀ*Q=1)
    (a b : Vertex n) (ha : Q*ᵥ sign a=sign b) (i : Fin n)
    (hc : ∃ w : Vertex n,Q*ᵥ sign (neighbor a i)=sign w) :
    ∃ j : Fin n, Q*ᵥ sign (neighbor a i)=sign (neighbor b j) := by
  obtain ⟨w,hw⟩ := hc
  have h := orth_dot Q hQ (sign a) (sign (neighbor a i))
  rw [ha,hw,← dot_int,← dot_int] at h
  obtain ⟨j,rfl⟩ := near_small hn a b w i (by exact_mod_cast h)
  exact ⟨j,hw⟩

private def shiftSigns {n : ℕ} (a b : Vertex n) (σ : Equiv.Perm (Fin n)) :
    Vertex n := fun j => b j == a (σ j)
private lemma shift_base {n : ℕ} (a b : Vertex n) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    sign b j=sign (shiftSigns a b σ) j * sign a (σ j) := by
  cases ha : a (σ j) <;> cases hb : b j <;> norm_num [sign,shiftSigns,ha,hb]
private lemma shift_near {n : ℕ} (a b : Vertex n) (σ : Equiv.Perm (Fin n))
    (i j l : Fin n) (hσ : σ j=i) :
    sign (neighbor b j) l = sign (shiftSigns a b σ) l * sign (neighbor a i) (σ l) := by
  subst i
  by_cases h : l=j
  · subst l
    cases ha : a (σ j) <;> cases hb : b j <;> norm_num [sign,shiftSigns,neighbor,ha,hb]
  · have h' := σ.injective.ne h
    simpa [sign,neighbor,h,h'] using shift_base a b σ l

theorem small {n : ℕ} (hn : n ≤ 3) (Q : Mat n) (S : Finset (Vertex n)) (hQ : Qᵀ * Q = 1)
    (hS : admissible Q S) : agrees Q S := by
  classical
  obtain hS0|⟨a,haS⟩ := S.eq_empty_or_nonempty
  · exact ⟨Equiv.refl _,fun _ => true,by simp [hS0]⟩
  obtain ⟨b,hab⟩ := hS a haS
  let used (i : Fin n) : Prop := ∃ j : Fin n, Q*ᵥ sign (neighbor a i)=sign (neighbor b j)
  let dest (i : {i // used i}) : Fin n := i.property.choose
  have dest_spec (i : {i // used i}) : Q *ᵥ sign (neighbor a i.val)=sign (neighbor b (dest i)) :=
    i.property.choose_spec
  have hQI : Function.Injective Q.mulVec := by
    intro x y he
    have h := congrArg Qᵀ.mulVec he
    simpa only [Matrix.mulVec_mulVec,hQ,Matrix.one_mulVec] using h
  have hinj : Function.Injective dest := by
    intro i j h
    apply Subtype.ext
    apply nb_inj a
    apply s_inj
    apply hQI
    rw [dest_spec i,dest_spec j,h]
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair dest Subtype.val hinj Subtype.val_injective
  refine ⟨σ,shiftSigns a b σ,?_⟩
  intro v hv
  let P (v : Vertex n) : Prop := ∀ l, (Q*ᵥ sign v) l =
    sign (shiftSigns a b σ) l * sign v (σ l)
  have hp : P a := by intro l;rw [hab,shift_base a b σ]
  have hf {w : Vertex n} (h : P w) : P (flipAll w) := by
    intro l
    simp only [sign_flip,Matrix.mulVec_neg,Pi.neg_apply,mul_neg]
    exact congrArg Neg.neg (h l)
  have hnbr (i : Fin n) (hu : used i) : P (neighbor a i) := by
    intro l
    let t : {i // used i} := ⟨i,hu⟩
    have eqn : Q *ᵥ sign (neighbor a i) = sign (neighbor b (dest t)) := dest_spec t
    rw [eqn,shift_near a b σ i (dest t) l (hσ t)]
  rcases cover_small hn a v with (rfl|rfl)|⟨i,rfl|rfl⟩
  · exact hp
  · exact hf hp
  · exact hnbr i (axis_match hn Q hQ a b hab i (hS _ hv))
  · apply hf
    apply hnbr
    apply axis_match hn Q hQ a b hab
    obtain ⟨w,hw⟩ := hS _ hv
    refine ⟨flipAll w,?_⟩
    rw [sign_flip,Matrix.mulVec_neg] at hw
    rw [sign_flip,← hw,neg_neg]

end OMA.S_mo_348427

namespace OMA.S_mo_348427
open Matrix Finset
noncomputable section

private def flipped {n : ℕ} (j : Fin n) (v : Vertex n) : Vertex n :=
  Function.update v j (!(v j))

private theorem flip_twice {n : ℕ} (j : Fin n) (v : Vertex n) :
    flipped j (flipped j v) = v := by
  funext i
  by_cases h : i=j <;> simp [flipped,Function.update_apply,h]

private theorem edge {n : ℕ} (S : Finset (Vertex n)) (h : 2^n < 2*S.card) (j : Fin n) :
    ∃ v ∈ S, flipped j v ∈ S := by
  classical
  have hf : Function.Involutive (@flipped n j) := flip_twice j
  let f : Vertex n ↪ Vertex n := ⟨flipped j,hf.injective⟩
  by_contra! hn
  have hd : Disjoint (S.map f) S := by
    rw [Finset.disjoint_left]
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
    exact hn w hw
  have hh := Finset.card_le_univ (S.map f ∪ S)
  rw [Finset.card_union_of_disjoint hd,Finset.card_map] at hh
  simp [Vertex] at hh
  omega

private theorem ternary {n : ℕ} (Q : Mat n) (S : Finset (Vertex n)) (hS : admissible Q S)
    (h : 2^n < 2*S.card) (i j : Fin n) : Q i j = -1 ∨ Q i j = 0 ∨ Q i j = 1 := by
  obtain ⟨v,hv,hv'⟩ := edge S h j
  obtain ⟨w,hw⟩ := hS v hv
  obtain ⟨w',hw'⟩ := hS (flipped j v) hv'
  have diff : sign v-sign (flipped j v) = Pi.single j (2*sign v j) := by
    funext k
    by_cases hk : k=j
    · subst k; cases hh : v j <;> norm_num [sign,flipped,hh]
    · simp [sign,flipped,hk,Pi.single_eq_of_ne]
  have hvv := congrFun (Matrix.mulVec_sub Q (sign v) (sign (flipped j v))) i
  rw [diff,hw,hw'] at hvv
  simp [Matrix.mulVec, dotProduct_single] at hvv
  cases hvj : v j <;> cases hwi : w i <;> cases hwi' : w' i <;>
    simp [sign,hvj,hwi,hwi'] at hvv <;> grind

private theorem signed_of_ternary {n : ℕ} (Q : Mat n) (S : Finset (Vertex n)) (hQ : Qᵀ*Q=1)
    (h : ∀ i j, Q i j = -1 ∨ Q i j = 0 ∨ Q i j = 1) : agrees Q S := by
  classical
  have hrow : Q*Qᵀ=1 := mul_eq_one_comm.mp hQ
  have sq (i : Fin n) : ∑ j, (Q i j)^2 = 1 := by
    simpa [Matrix.mul_apply,pow_two] using congrArg (fun M : Mat n => M i i) hrow
  have ex (i : Fin n) : ∃ j, Q i j = -1 ∨ Q i j = 1 := by
    by_contra! hn
    have hz (j : Fin n) : Q i j=0 := by rcases h i j with a|a|a <;> grind
    simpa [hz] using sq i
  choose c hc using ex
  have nz (i : Fin n) : Q i (c i) ≠ 0 := by rcases hc i with hh|hh <;> rw [hh] <;> norm_num
  have off (i j : Fin n) (hne : j≠c i) : Q i j=0 := by
    have hsum := Finset.sum_erase_add (f := fun k => (Q i k)^2) univ (mem_univ (c i))
    rw [sq] at hsum
    have hle := Finset.single_le_sum (f := fun k => (Q i k)^2) (fun k _ => sq_nonneg _) (mem_erase.mpr ⟨hne,mem_univ j⟩)
    rcases hc i with hh|hh <;> rw [hh] at hsum <;> nlinarith [sq_nonneg (Q i j)]
  have row (i : Fin n) (v : Fin n → ℝ) : (Q*ᵥv) i = Q i (c i)*v (c i) := by
    change (∑ j, Q i j*v j) = _
    apply Finset.sum_eq_single (c i)
    · intro j _ hj; rw [off i j hj,zero_mul]
    · simp
  have inj : Function.Injective c := by
    intro i j hij
    by_contra hn
    have hz := congrArg (fun M : Mat n => M i j) hrow
    change (Q*ᵥ(fun k => Q j k)) i = (1:Mat n) i j at hz
    rw [row,Matrix.one_apply,if_neg hn,hij] at hz
    exact (mul_ne_zero (hij ▸ nz i) (nz j)) hz
  refine ⟨Equiv.ofBijective c ((Finite.injective_iff_bijective).mp inj),fun i => decide (Q i (c i)=1),?_⟩
  intro v _ i
  rw [row]
  rcases hc i with hh|hh <;> cases hv : v (c i) <;> norm_num [sign,hh,Equiv.ofBijective_apply,hv]

private theorem upper {n : ℕ} (Q : Mat n) (S : Finset (Vertex n)) (hQ : Qᵀ*Q=1)
    (hS : admissible Q S) (hbad : ¬agrees Q S) : 2*S.card ≤ 2^n := by
  by_contra! h
  exact hbad (signed_of_ternary Q S hQ (ternary Q S hS h))

end
end OMA.S_mo_348427

namespace OMA.S_mo_348427
open Matrix Finset
noncomputable section

private def coeff (i j : Fin 4) : ℚ := (if i=j then 1 else 0)-1/2
private def core : Mat 4 := fun i j => (coeff i j : ℝ)
private def qsign (v : Vertex 4) (i : Fin 4) : ℚ := if v i then 1 else -1
private theorem sign_cast (v : Vertex 4) (i : Fin 4) : (qsign v i : ℝ) = sign v i := by
  cases h : v i <;> simp [qsign,sign,h]
private def even (v : Vertex 4) : Bool := !(v 0 ^^ v 1 ^^ v 2 ^^ v 3)
private def allowed : Finset (Vertex 4) := univ.filter (fun v => even v = true)
private def out (v : Vertex 4) (j : Fin 4) : Bool :=
  if v 0=v 1 ∧ v 1=v 2 ∧ v 2=v 3 then !(v j) else v j

private theorem core_orth : coreᵀ*core = 1 := by
  have h : ∀ i j : Fin 4, (∑ k, coeff k i*coeff k j) = (1:Matrix (Fin 4) (Fin 4) ℚ) i j := by
    simp only [Matrix.one_apply, Fin.sum_univ_four]
    decide +kernel
  ext i j
  change (∑ k, (coeff k i:ℝ)*(coeff k j:ℝ)) = _
  by_cases hij : i=j
  · simpa [Matrix.one_apply,hij] using congrArg (fun a : ℚ => (a:ℝ)) (h i j)
  · simpa [Matrix.one_apply,hij] using congrArg (fun a : ℚ => (a:ℝ)) (h i j)

private theorem core_action {v : Vertex 4} (hv : v ∈ allowed) :
    core*ᵥsign v = sign (out v) := by
  have h : ∀ v ∈ allowed, ∀ i : Fin 4, (∑ j, coeff i j*qsign v j)=qsign (out v) i := by
    simp only [allowed,Finset.mem_filter,mem_univ,true_and,Fin.sum_univ_four]
    decide +kernel
  funext i
  simpa [Matrix.mulVec,dotProduct,core,sign_cast] using congrArg (fun a : ℚ => (a:ℝ)) (h v hv i)

private def block (k : ℕ) : Matrix (Fin 4 ⊕ Fin k) (Fin 4 ⊕ Fin k) ℝ := fromBlocks core 0 0 1
private def rotation (k : ℕ) : Mat (4+k) := (block k).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

private theorem rotation_orth (k : ℕ) : (rotation k)ᵀ * rotation k = 1 := by
  have hb : (block k)ᵀ*block k=1 := by
    simp [block,Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,core_orth,Matrix.fromBlocks_one]
  unfold rotation
  rw [Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,hb]
  simp

private theorem rotation_action {k : ℕ} (v : Vertex 4) (w : Vertex k) (hv : v ∈ allowed) :
    rotation k*ᵥsign (Fin.append v w)=sign (Fin.append (out v) w) := by
  rw [rotation,Matrix.submatrix_mulVec_equiv,block,Matrix.fromBlocks_mulVec]
  have hleft : (sign (Fin.append v w) ∘ finSumFinEquiv) ∘ Sum.inl = sign v := by
    funext i; simp [Function.comp_apply,sign]
  have hright : (sign (Fin.append v w) ∘ finSumFinEquiv) ∘ Sum.inr = sign w := by
    funext i; simp [Function.comp_apply,sign]
  simp only [Equiv.symm_symm,hleft,hright,zero_mulVec,one_mulVec,add_zero,zero_add,core_action hv]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Function.comp_apply,sign]

private def appendEmb (k : ℕ) : (Vertex 4 × Vertex k) ↪ Vertex (4+k) where
  toFun a := Fin.append a.1 a.2
  inj' := by
    intro x y h
    apply Prod.ext
    · funext i; simpa using congrFun h (Fin.castAdd k i)
    · funext i; simpa using congrFun h (Fin.natAdd 4 i)

private def family (k : ℕ) : Finset (Vertex (4+k)) := (allowed ×ˢ univ).map (appendEmb k)

private theorem append_mem {k : ℕ} (v : Vertex 4) (w : Vertex k) (h : v ∈ allowed) :
    Fin.append v w ∈ family k := Finset.mem_map.mpr ⟨(v,w),Finset.mem_product.mpr ⟨h,mem_univ _⟩,rfl⟩

private theorem sharp (k : ℕ) : ∃ (Q : Mat (4+k)) (S : Finset (Vertex (4+k))),
    Qᵀ*Q=1 ∧ admissible Q S ∧ ¬agrees Q S ∧ 2*S.card=2^(4+k) := by
  refine ⟨rotation k,family k,rotation_orth k,?_,?_,?_⟩
  · intro x hx
    obtain ⟨⟨v,w⟩,hv,rfl⟩ := Finset.mem_map.mp hx
    exact ⟨Fin.append (out v) w,rotation_action v w (Finset.mem_product.mp hv).1⟩
  · rintro ⟨σ,e,h⟩
    let a : Fin (4+k) := (0 : Fin 4).castAdd k
    let w : Vertex k := fun _ => true
    have atRow (v : Vertex 4) (hv : v ∈ allowed) :
        sign (out v) 0 = sign e a * sign (Fin.append v w) (σ a) := by
      have hh := h _ (append_mem v w hv) a
      rw [rotation_action v w hv] at hh
      simpa [a,sign] using hh
    let ones : Vertex 4 := fun _ => true
    have hones : ones ∈ allowed := by decide
    have first := atRow ones hones
    have vw : Fin.append ones w = fun _ => true := by
      funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [ones,w]
    rw [vw] at first
    have he : sign e a = -1 := by simpa [ones,out,sign] using first.symm
    have tests : ∀ j : Fin 4, ∃ v ∈ allowed, v j=true ∧ out v 0=true := by decide
    have impossible (i : Fin (4+k)) : (∀ v ∈ allowed, sign (out v) 0 = -1 * sign (Fin.append v w) i) → False := by
      refine Fin.addCases (fun j hh => ?_) (fun j hh => ?_) i
      · obtain ⟨v,hv,hj,ho⟩ := tests j
        have eq := hh v hv
        norm_num [sign,hj,ho] at eq
      · obtain ⟨v,hv,_,ho⟩ := tests 0
        have eq := hh v hv
        norm_num [sign,w,ho] at eq
    exact impossible (σ a) (fun v hv => by rw [← he]; exact atRow v hv)
  · have hc : allowed.card = 8 := by decide
    simp [family,hc,Vertex,pow_add]
    ring

end
end OMA.S_mo_348427

open OMA.S_mo_348427 in
theorem OMA.solution : type_of% @OMA.S_mo_348427.main := by
  refine ⟨fun _ hn Q S hQ hS => small hn Q S hQ hS,?_⟩
  intro n hn
  refine ⟨fun Q S => upper Q S,?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  exact sharp k
