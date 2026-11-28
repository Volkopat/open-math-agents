import OMAStatements.S_oeis_a001405

-- Problem: A001405: a(n) = binomial(n, floor(n/2)).
-- Upstream: formal-conjectures statements/oeis-a001405.lean:0 (declaration OMA.S_oeis_a001405.main)
-- Credit: @timlantin (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P001405
open OMA.S_oeis_a001405

/-- Closed form for the dimension of the kernel of the k-th power of the strict-containment
operator on the Boolean lattice of rank m (walks of length m from height k staying positive). -/
def f (m k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m+1), if (m ≤ 2*j+k ∧ 2*j < m+k) then Nat.choose m j else 0

lemma f_one (m : ℕ) : f m 1 = Nat.choose m (m/2) := by
  unfold f
  rw [Finset.sum_eq_single (m/2)]
  · rw [if_pos]; omega
  · intro j _ hj; rw [if_neg]; omega
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

lemma f_zero (m : ℕ) : f m 0 = 0 := by
  unfold f; apply Finset.sum_eq_zero; intro j _; rw [if_neg]; omega

lemma f_base (k : ℕ) : f 0 (k+1) = 1 := by simp [f]

lemma f_succ (m k : ℕ) : f (m+1) (k+1) = f m k + f m (k+2) := by
  unfold f
  rw [Finset.sum_range_succ', ← Finset.sum_add_distrib]
  have h1 : ∀ j, (if (m+1 ≤ 2*(j+1)+(k+1) ∧ 2*(j+1) < m+1+(k+1)) then Nat.choose (m+1) (j+1) else 0)
     = (if (m ≤ 2*j+k+2 ∧ 2*j < m+k) then Nat.choose m j else 0)
       + (if (m ≤ 2*(j+1)+k ∧ 2*(j+1) < m+k+2) then Nat.choose m (j+1) else 0) := by
    intro j; rw [Nat.choose_succ_succ']; split_ifs <;> omega
  simp only [h1]
  rw [Finset.sum_add_distrib]
  have h2 := Finset.sum_range_succ'
    (fun j => if (m ≤ 2*j+k ∧ 2*j < m+k+2) then Nat.choose m j else 0) (m+1)
  have h3 := Finset.sum_range_succ
    (fun j => if (m ≤ 2*j+k ∧ 2*j < m+k+2) then Nat.choose m j else 0) (m+1)
  have h4 : (if (m ≤ 2*(m+1)+k ∧ 2*(m+1) < m+k+2) then Nat.choose m (m+1) else 0) = 0 := by
    simp
  have h5 : (if (m + 1 ≤ 2 * 0 + (k + 1) ∧ 2 * 0 < m + 1 + (k + 1)) then Nat.choose (m+1) 0 else 0)
      = (if (m ≤ 2*0+k ∧ 2*0 < m+k+2) then Nat.choose m 0 else 0) := by
    simp only [Nat.choose_zero_right]; split_ifs <;> omega
  rw [h5, add_assoc, ← h2, h3, h4, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> omega

section LA
variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

lemma finrank_ker_conj (Θ : V ≃ₗ[ℚ] W) (A : Module.End ℚ V) (B : Module.End ℚ W)
    (h : ∀ v, Θ (A v) = B (Θ v)) (k : ℕ) :
    Module.finrank ℚ (LinearMap.ker (A^k)) = Module.finrank ℚ (LinearMap.ker (B^k)) := by
  have hk : ∀ k : ℕ, ∀ v, Θ ((A^k) v) = (B^k) (Θ v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]
  have : LinearMap.ker (A^k) = (LinearMap.ker (B^k)).comap (Θ : V →ₗ[ℚ] W) := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_comap, LinearEquiv.coe_coe]
    rw [← hk k v]; simp
  rw [this]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' Θ _)

/-- The doubling of an endomorphism: (x, y) ↦ (A x, A x + x + A y). -/
def dbl (A : Module.End ℚ V) : Module.End ℚ (V × V) :=
  LinearMap.prod (A ∘ₗ LinearMap.fst ℚ V V)
    ((A + 1) ∘ₗ LinearMap.fst ℚ V V + A ∘ₗ LinearMap.snd ℚ V V)

lemma dbl_apply (A : Module.End ℚ V) (x y : V) : dbl A (x, y) = (A x, A x + x + A y) := by
  simp [dbl]

lemma dbl_pow (A : Module.End ℚ V) (k : ℕ) (x y : V) :
    (dbl A ^ (k+1)) (x, y)
      = ((A^(k+1)) x, ((k:ℚ)+1) • ((A^(k+1)) x + (A^k) x) + (A^(k+1)) y) := by
  induction k with
  | zero => simp [dbl_apply]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, dbl_apply]
    simp only [pow_succ', Module.End.mul_apply, map_add, map_smul]
    refine Prod.ext rfl ?_
    simp only
    push_cast
    module

lemma finrank_ker_prodMap [FiniteDimensional ℚ V] (F G : Module.End ℚ V) :
    Module.finrank ℚ (LinearMap.ker (F.prodMap G))
      = Module.finrank ℚ (LinearMap.ker F) + Module.finrank ℚ (LinearMap.ker G) := by
  rw [← Module.finrank_prod]
  refine LinearEquiv.finrank_eq
    { toFun := fun p =>
        (⟨p.1.1, by
            have h := p.2
            rw [LinearMap.mem_ker, LinearMap.prodMap_apply, Prod.mk_eq_zero] at h
            exact h.1⟩,
         ⟨p.1.2, by
            have h := p.2
            rw [LinearMap.mem_ker, LinearMap.prodMap_apply, Prod.mk_eq_zero] at h
            exact h.2⟩)
      invFun := fun q => ⟨(q.1.1, q.2.1), by
        rw [LinearMap.mem_ker, LinearMap.prodMap_apply, Prod.mk_eq_zero]
        exact ⟨q.1.2, q.2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma dbl_ker [FiniteDimensional ℚ V] (A : Module.End ℚ V) (k : ℕ) :
    Module.finrank ℚ (LinearMap.ker (dbl A ^ (k+1)))
      = Module.finrank ℚ (LinearMap.ker (A^k)) + Module.finrank ℚ (LinearMap.ker (A^(k+2))) := by
  have hc : ((k:ℚ)+1) ≠ 0 := by positivity
  let Ψ : (V × V) ≃ₗ[ℚ] (V × V) :=
    { toFun := fun p => (((k:ℚ)+1) • p.1 + A p.2, p.2)
      invFun := fun p => (((k:ℚ)+1)⁻¹ • (p.1 - A p.2), p.2)
      map_add' := by
        intro p q; refine Prod.ext ?_ rfl
        simp only [Prod.fst_add, Prod.snd_add, map_add]; module
      map_smul' := by
        intro c p; refine Prod.ext ?_ rfl
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]; module
      left_inv := by
        intro p; refine Prod.ext ?_ rfl
        simp only [add_sub_cancel_right]
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      right_inv := by
        intro p; refine Prod.ext ?_ rfl
        simp only
        rw [smul_smul, mul_inv_cancel₀ hc, one_smul]; abel }
  have hAA : ∀ (j : ℕ) (z : V), (A^(j+1)) z = (A^j) (A z) := by
    intro j z; rw [pow_succ, Module.End.mul_apply]
  have hAA' : ∀ (j : ℕ) (z : V), (A^(j+1)) z = A ((A^j) z) := by
    intro j z; rw [pow_succ', Module.End.mul_apply]
  have key : LinearMap.ker (dbl A ^ (k+1))
      = (LinearMap.ker ((A^k).prodMap (A^(k+2)))).comap (Ψ : (V × V) →ₗ[ℚ] (V × V)) := by
    ext ⟨x, y⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, LinearEquiv.coe_coe, dbl_pow,
      LinearMap.prodMap_apply, Prod.mk_eq_zero]
    change _ ↔ (A^k) (((k:ℚ)+1) • x + A y) = 0 ∧ (A^(k+2)) y = 0
    rw [map_add, map_smul, ← hAA]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1, zero_add] at h2
      refine ⟨h2, ?_⟩
      have h3 : (A^(k+1)) y = -(((k:ℚ)+1) • (A^k) x) := eq_neg_of_add_eq_zero_right h2
      rw [hAA' (k+1), h3, map_neg, map_smul, ← hAA', h1, smul_zero, neg_zero]
    · rintro ⟨g1, g2⟩
      have h1 : (A^(k+1)) x = 0 := by
        have : ((k:ℚ)+1) • (A^(k+1)) x = 0 := by
          have h3 : ((k:ℚ)+1) • (A^k) x = -((A^(k+1)) y) := eq_neg_of_add_eq_zero_left g1
          rw [hAA' k, ← map_smul, h3, map_neg, ← hAA', g2, neg_zero]
        exact (smul_eq_zero.mp this).resolve_left hc
      refine ⟨h1, ?_⟩
      rw [h1, zero_add]; exact g1
  rw [key, LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' Ψ _), finrank_ker_prodMap]

end LA

/-- Pointwise order on Boolean vectors (subsets of an m-set). -/
def le {m : ℕ} (g f : Fin m → Bool) : Prop := ∀ i, g i = true → f i = true

instance {m : ℕ} (g f : Fin m → Bool) : Decidable (le g f) := by
  unfold le; infer_instance

/-- The containment (zeta) matrix of the Boolean lattice of rank m. -/
def Zm (m : ℕ) : Matrix (Fin m → Bool) (Fin m → Bool) ℚ :=
  fun f g => if le g f then (1:ℚ) else 0

/-- The strict-containment operator on functions on the Boolean lattice of rank m. -/
def M (m : ℕ) : Module.End ℚ ((Fin m → Bool) → ℚ) :=
  Matrix.toLin' (Zm m) - 1

lemma M_apply (m : ℕ) (v : (Fin m → Bool) → ℚ) (f : Fin m → Bool) :
    M m v f = (∑ g, if le g f then v g else 0) - v f := by
  simp only [M, LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Zm, ite_mul, one_mul, zero_mul]

lemma le_cons {m : ℕ} (b c : Bool) (g f : Fin m → Bool) :
    le (Fin.cons b g : Fin (m+1) → Bool) (Fin.cons c f) ↔ (b = true → c = true) ∧ le g f := by
  unfold le
  rw [Fin.forall_fin_succ]
  simp

lemma sum_cons {m : ℕ} (F : (Fin (m+1) → Bool) → ℚ) :
    ∑ h, F h = (∑ g : Fin m → Bool, F (Fin.cons false g)) + ∑ g : Fin m → Bool, F (Fin.cons true g) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m+1) => Bool)) F, Fintype.sum_prod_type, Fintype.sum_bool,
    add_comm]
  rfl

/-- Splitting a function on the rank m+1 lattice according to the first coordinate. -/
def Th (m : ℕ) : ((Fin (m+1) → Bool) → ℚ) ≃ₗ[ℚ]
    (((Fin m → Bool) → ℚ) × ((Fin m → Bool) → ℚ)) :=
  { toFun := fun v => (fun g => v (Fin.cons false g), fun g => v (Fin.cons true g))
    invFun := fun p => fun f => if f 0 = true then p.2 (Fin.tail f) else p.1 (Fin.tail f)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := by
      intro v; funext f
      have hc : Fin.cons (f 0) (Fin.tail f) = f := Fin.cons_self_tail f
      change (if f 0 = true then v (Fin.cons true (Fin.tail f))
        else v (Fin.cons false (Fin.tail f))) = v f
      by_cases h : f 0 = true
      · rw [if_pos h]; rw [h] at hc; rw [hc]
      · rw [if_neg h]
        have h' : f 0 = false := by simpa using h
        rw [h'] at hc; rw [hc]
    right_inv := by
      intro p; refine Prod.ext ?_ ?_ <;> funext g <;> simp }

lemma Th_M (m : ℕ) (v : (Fin (m+1) → Bool) → ℚ) : Th m (M (m+1) v) = dbl (M m) (Th m v) := by
  have e : Th m v = ((fun g => v (Fin.cons false g)), (fun g => v (Fin.cons true g))) := rfl
  rw [e, dbl_apply]
  refine Prod.ext ?_ ?_
  · funext g
    change M (m+1) v (Fin.cons false g) = M m (fun g => v (Fin.cons false g)) g
    rw [M_apply, M_apply, sum_cons]
    simp [le_cons]
  · funext g
    change M (m+1) v (Fin.cons true g) = M m (fun g => v (Fin.cons false g)) g
      + v (Fin.cons false g) + M m (fun g => v (Fin.cons true g)) g
    rw [M_apply, M_apply, M_apply, sum_cons]
    simp [le_cons]
    ring

lemma M_zero : M 0 = 0 := by
  apply LinearMap.ext; intro v; funext f
  have h2 : le f f := fun _ h => h
  rw [M_apply, Finset.sum_eq_single f]
  · rw [if_pos h2]; simp
  · intro g _ hg; exact absurd (Subsingleton.elim g f) hg
  · intro h; exact absurd (Finset.mem_univ f) h

lemma ker_pow_zero (m : ℕ) : Module.finrank ℚ (LinearMap.ker (M m ^ 0)) = 0 := by
  rw [pow_zero, Module.End.one_eq_id, LinearMap.ker_id, finrank_bot]

lemma dker (m : ℕ) : ∀ k, Module.finrank ℚ (LinearMap.ker (M m ^ k)) = f m k := by
  induction m with
  | zero =>
    intro k
    cases k with
    | zero => rw [ker_pow_zero, f_zero]
    | succ k =>
      rw [M_zero, zero_pow (Nat.succ_ne_zero k), LinearMap.ker_zero, finrank_top,
        Module.finrank_fintype_fun_eq_card, f_base]
      simp
  | succ m ih =>
    intro k
    cases k with
    | zero => rw [ker_pow_zero, f_zero]
    | succ k =>
      rw [finrank_ker_conj (Th m) (M (m+1)) (dbl (M m)) (Th_M m) (k+1), dbl_ker, ih k,
        ih (k+2), f_succ]

/-- The Boolean vector of interior boundaries of a composition. -/
def bf (n : ℕ) (I : Composition n) : Fin (n-1) → Bool :=
  fun i => decide ((⟨1 + (i:ℕ), by have := i.isLt; omega⟩ : Fin (n+1)) ∈ I.boundaries)

lemma bf_le (n : ℕ) (I J : Composition n) :
    le (bf n J) (bf n I) ↔ J.boundaries ⊆ I.boundaries := by
  constructor
  · intro h x hx
    by_cases h0 : x = 0
    · rw [h0]; exact I.toCompositionAsSet.zero_mem
    by_cases hn : x = Fin.last n
    · rw [hn]; exact I.toCompositionAsSet.getLast_mem
    have hx0 : (x:ℕ) ≠ 0 := fun hh => h0 (Fin.ext hh)
    have hxn : (x:ℕ) ≠ n := fun hh => hn (Fin.ext hh)
    have hxl := x.isLt
    have hi : (x:ℕ) - 1 < n - 1 := by omega
    have hxe : (⟨1 + ((x:ℕ) - 1), by omega⟩ : Fin (n+1)) = x := Fin.ext (by simp; omega)
    have := h ⟨(x:ℕ) - 1, hi⟩ (by simp only [bf]; rw [hxe]; exact decide_eq_true hx)
    simp only [bf] at this
    rw [hxe] at this
    exact of_decide_eq_true this
  · intro h i hi
    simp only [bf] at hi ⊢
    exact decide_eq_true (h (of_decide_eq_true hi))

lemma bf_bij (n : ℕ) : Function.Bijective (bf n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro I J hIJ
    have h1 : J.boundaries ⊆ I.boundaries := (bf_le n I J).mp (by rw [hIJ]; exact fun _ h => h)
    have h2 : I.boundaries ⊆ J.boundaries := (bf_le n J I).mp (by rw [hIJ]; exact fun _ h => h)
    apply (compositionEquiv n).injective
    exact CompositionAsSet.ext (Finset.Subset.antisymm h2 h1)
  · rw [composition_card]; simp

lemma sign_aux (a b : ℕ) (h : b ≤ a) : (-1:ℚ)^a * (-1)^(a-b) = (-1)^b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← mul_pow]; simp

lemma sign_sq (a : ℕ) : (-1:ℚ)^a * (-1)^a = 1 := by
  rw [← mul_pow]; simp

/-- Reindexing by interior boundaries, twisted by the sign (-1)^length. -/
noncomputable def P (n : ℕ) : (Composition n → ℚ) ≃ₗ[ℚ] ((Fin (n-1) → Bool) → ℚ) :=
  { toFun := fun v f => (-1:ℚ)^((Equiv.ofBijective _ (bf_bij n)).symm f).length
      * v ((Equiv.ofBijective _ (bf_bij n)).symm f)
    invFun := fun w I => (-1:ℚ)^I.length * w (bf n I)
    map_add' := by intro v w; funext f; simp [mul_add]
    map_smul' := by intro c v; funext f; simp; ring
    left_inv := by
      intro v; funext I
      have h : (Equiv.ofBijective _ (bf_bij n)).symm (bf n I) = I :=
        (Equiv.ofBijective _ (bf_bij n)).symm_apply_apply I
      simp only [h]
      rw [← mul_assoc, sign_sq, one_mul]
    right_inv := by
      intro w; funext f
      have h : bf n ((Equiv.ofBijective _ (bf_bij n)).symm f) = f :=
        (Equiv.ofBijective _ (bf_bij n)).apply_symm_apply f
      simp only [h]
      rw [← mul_assoc, sign_sq, one_mul] }

lemma P_apply (n : ℕ) (v : Composition n → ℚ) (I : Composition n) :
    P n v (bf n I) = (-1:ℚ)^I.length * v I := by
  have h : (Equiv.ofBijective _ (bf_bij n)).symm (bf n I) = I :=
    (Equiv.ofBijective _ (bf_bij n)).symm_apply_apply I
  change (-1:ℚ)^((Equiv.ofBijective _ (bf_bij n)).symm (bf n I)).length
      * v ((Equiv.ofBijective _ (bf_bij n)).symm (bf n I)) = _
  rw [h]

lemma P_C (n : ℕ) (v : Composition n → ℚ) :
    P n (Matrix.toLin' (C n - 1) v) = M (n-1) (P n v) := by
  funext f
  obtain ⟨I, rfl⟩ := (bf_bij n).surjective f
  have hs : Matrix.toLin' (C n - 1) v = Matrix.toLin' (C n) v - v := by
    rw [map_sub, Matrix.toLin'_one]; rfl
  rw [P_apply, M_apply, P_apply, ← Equiv.sum_comp (Equiv.ofBijective _ (bf_bij n))]
  simp only [Equiv.ofBijective_apply, P_apply, bf_le, hs, Pi.sub_apply, mul_sub,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro J _
  unfold C
  by_cases hJ : J.boundaries ⊆ I.boundaries
  · have hl : J.length ≤ I.length := by
      have := Finset.card_le_card hJ
      rw [Composition.card_boundaries_eq_succ_length, Composition.card_boundaries_eq_succ_length]
        at this
      omega
    rw [if_pos hJ, if_pos hJ, ← mul_assoc, sign_aux _ _ hl]
  · rw [if_neg hJ, if_neg hJ]; simp

end OMA.P001405

open OMA.S_oeis_a001405 OMA.P001405 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001405.main := by
  intro n _
  have h := finrank_ker_conj (P n) (Matrix.toLin' (C n - 1)) (M (n-1)) (P_C n) 1
  rw [pow_one, pow_one] at h
  rw [h]
  have h2 := dker (n-1) 1
  rw [pow_one] at h2
  rw [h2, f_one]
  rfl
