import OMAReductions.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1
import Mathlib

/-! The relative ideal class norm and Dirichlet unit theorem give the two fiber bounds in Sawin Lemma 6. Both signs of each generator have norm one. -/

namespace SawinNormFibers
open scoped nonZeroDivisors NumberField
open NumberField

theorem sawin_class_norm (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] :
    ∃ T : ClassGroup (𝓞 K) →* ClassGroup (𝓞 F),
      ∀ I : (Ideal (𝓞 K))⁰, ∃ J : (Ideal (𝓞 F))⁰,
        J.val = Ideal.relNorm (𝓞 F) I.val ∧ T (ClassGroup.mk0 I)=ClassGroup.mk0 J := by
  classical
  let N (I : (Ideal (𝓞 K))⁰) : (Ideal (𝓞 F))⁰ :=
    ⟨Ideal.relNorm (𝓞 F) I.val, mem_nonZeroDivisors_iff_ne_zero.mpr
      (fun eq => (mem_nonZeroDivisors_iff_ne_zero.mp I.property) (Ideal.relNorm_eq_bot_iff.mp eq))⟩
  have respect {I J : (Ideal (𝓞 K))⁰} (h : ClassGroup.mk0 I=ClassGroup.mk0 J) :
      ClassGroup.mk0 (N I)=ClassGroup.mk0 (N J) := by
    obtain ⟨x,y,hx,hy,eq⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
    apply ClassGroup.mk0_eq_mk0_iff.mpr
    refine ⟨Algebra.intNorm (𝓞 F) (𝓞 K) x,Algebra.intNorm (𝓞 F) (𝓞 K) y,
      fun h => hx (Algebra.intNorm_eq_zero.mp h),fun h => hy (Algebra.intNorm_eq_zero.mp h),?_⟩
    simpa [N] using congrArg (Ideal.relNorm (𝓞 F)) eq
  choose rep hr using (ClassGroup.mk0_surjective : Function.Surjective (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ →* _))
  let f (c : ClassGroup (𝓞 K)) := ClassGroup.mk0 (N (rep c))
  have on (I : (Ideal (𝓞 K))⁰) : f (ClassGroup.mk0 I) = ClassGroup.mk0 (N I) := respect (hr _)
  have n1 : N 1=1 := Subtype.ext (map_one (Ideal.relNorm (𝓞 F)))
  have nm (I J : (Ideal (𝓞 K))⁰) : N (I*J)=N I*N J := Subtype.ext (map_mul (Ideal.relNorm (𝓞 F)) _ _)
  let T : ClassGroup (𝓞 K) →* ClassGroup (𝓞 F) :=
    { toFun := f
      map_one' := by simpa [n1] using on 1
      map_mul' := by
        intro a b
        obtain ⟨I,rfl⟩ := ClassGroup.mk0_surjective a
        obtain ⟨J,rfl⟩ := ClassGroup.mk0_surjective b
        rw [←map_mul,on,nm,map_mul,on,on] }
  exact ⟨T, fun I => ⟨N I,rfl,on I⟩⟩


open scoped NumberField BigOperators
open NumberField NumberField.Units

theorem sawin_unit_squares (F : Type) [Field F] [NumberField F] :
    ∃ S : Finset (𝓞 F)ˣ, S.card ≤ 2^(Module.finrank ℚ F) ∧
      ∀ x : (𝓞 F)ˣ, ∃ a ∈ S, ∃ y : (𝓞 F)ˣ, x=a*y^2 := by
  classical
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := torsion F)
  let parity (k : ℤ) : Fin 2 := if k%2=0 then 0 else 1
  have split (u : (𝓞 F)ˣ) (k : ℤ) :
      u^k = u^(parity k).val*(u^(k/2))^2 := by
    rw [← zpow_natCast u (parity k).val,←zpow_natCast (u^(k/2)) 2, ←zpow_mul, ←zpow_add]
    congr 1
    dsimp [parity]; split <;> simp_all <;> omega
  let rep (p : Fin 2 × (Fin (rank F) → Fin 2)) : (𝓞 F)ˣ :=
    (g.val)^p.1.val * ∏ i, (fundSystem F i)^(p.2 i).val
  refine ⟨Finset.univ.image rep,Finset.card_image_le.trans ?_,?_⟩
  · have r : rank F + 1 ≤ Module.finrank ℚ F := by
      unfold rank
      have h := InfinitePlace.card_add_two_mul_card_eq_rank F
      have c := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
      have pos := Module.finrank_pos (R := ℚ) (M := F)
      omega
    simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_fun]
    rw [mul_comm,← pow_succ]
    exact Nat.pow_le_pow_right (by decide) r
  · intro x
    obtain ⟨⟨z,e⟩,hx,_⟩ := exist_unique_eq_mul_prod F x
    obtain ⟨j,hj⟩ := hg z
    let p : Fin 2 × (Fin (rank F) → Fin 2) := (parity j,fun i => parity (e i))
    refine ⟨rep p,Finset.mem_image_of_mem _ (Finset.mem_univ _),
        g.val^(j/2) * ∏ i, (fundSystem F i)^(e i / 2),?_⟩
    have zz : z.val = g.val^j := congrArg Subtype.val hj.symm
    rw [hx]; change z.val * (∏ i, fundSystem F i ^ e i) = _
    rw [zz,split _ j]; simp_rw [split (fundSystem F _) (e _)]
    rw [Finset.prod_mul_distrib,Finset.prod_pow,mul_pow]
    dsimp [rep,p]
    exact mul_mul_mul_comm _ _ _ _


open scoped nonZeroDivisors NumberField
open NumberField FractionalIdeal

theorem sawin_principal (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (I J : (Ideal (𝓞 K))⁰) (hc : ClassGroup.mk0 I = ClassGroup.mk0 J)
    (hn : Ideal.relNorm (𝓞 F) I.val = Ideal.relNorm (𝓞 F) J.val) :
    ∃ b : K, b ≠ 0 ∧ spanSingleton (𝓞 K)⁰ b * I.val = (J.val : FractionalIdeal (𝓞 K)⁰ K) ∧
      ∃ u : (𝓞 F)ˣ, Algebra.norm F b = algebraMap (𝓞 F) F (u : 𝓞 F) := by
  obtain ⟨x,y,hx,hy,h⟩ := ClassGroup.mk0_eq_mk0_iff.mp hc
  have hy' : y ∈ (𝓞 K)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hy
  let b := IsLocalization.mk' K x ⟨y,hy'⟩
  have byx : b=algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K y := IsFractionRing.mk'_eq_div _
  have xi : Function.Injective (algebraMap (𝓞 K) K) := RingOfIntegers.coe_injective
  have nz (t : 𝓞 K) (ht : t ≠ 0) : algebraMap (𝓞 K) K t ≠ 0 := fun eq => ht (xi (eq.trans (map_zero _).symm))
  refine ⟨b,by rw [byx]; exact div_ne_zero (nz x hx) (nz y hy),
    (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal K hy').mpr h,?_⟩
  let N := Algebra.intNorm (𝓞 F) (𝓞 K)
  have jnz : Ideal.relNorm (𝓞 F) J.val ≠ 0 :=
    fun eq => mem_nonZeroDivisors_iff_ne_zero.mp J.property (Ideal.relNorm_eq_bot_iff.mp eq)
  have eq : Ideal.span {N x} * Ideal.relNorm (𝓞 F) J.val = Ideal.span {N y} * Ideal.relNorm (𝓞 F) J.val := by
    simpa [N,hn] using congrArg (Ideal.relNorm (𝓞 F)) h
  have assoc := Ideal.span_singleton_eq_span_singleton.mp (mul_right_cancel₀ jnz eq)
  obtain ⟨u,hu⟩ := assoc.symm
  refine ⟨u,?_⟩
  have bridge (z : 𝓞 K) : Algebra.norm F (algebraMap (𝓞 K) K z) = algebraMap (𝓞 F) F (N z) := by
    exact (Algebra.algebraMap_intNorm (L := K) ..).symm
  rw [byx,div_eq_mul_inv,map_mul,Algebra.norm_inv,bridge,bridge,←hu,map_mul]
  have fnz : algebraMap (𝓞 F) F (N y) ≠ 0 := by
    rw [←bridge]; exact fun h => hy ((Algebra.norm_eq_zero_iff.mp h) |> fun h => xi (h.trans (map_zero _).symm))
  field_simp


open scoped Classical NumberField nonZeroDivisors
open NumberField FractionalIdeal Finset

theorem sawin_heavy {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (f : A → B) : ∃ a : A, Fintype.card A ≤ Fintype.card B * Fintype.card {i // f i = f a} := by
  classical
  let size (b : B) := (Finset.univ.filter (fun i : A => f i=b)).card
  obtain ⟨a,_,ha⟩ := Finset.exists_max_image (Finset.univ : Finset A) (fun i => size (f i)) Finset.univ_nonempty
  have bound (b : B) : size b ≤ size (f a) := by
    by_cases h : ∃ i, f i=b
    · obtain ⟨i,rfl⟩ := h; exact ha i (Finset.mem_univ _)
    · have : ∀ i, f i ≠ b := fun i hi => h ⟨i,hi⟩
      simp [size,this]
  refine ⟨a,?_⟩
  have eq : Fintype.card A = ∑ b : B, size b := Finset.card_eq_sum_card_fiberwise (by simp)
  rw [eq,Fintype.card_subtype]
  simpa [size] using Finset.sum_le_sum (s := (Finset.univ : Finset B)) (fun i _ => bound i)

theorem sawin_span_unit (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (u : (𝓞 F)ˣ) : spanSingleton (𝓞 K)⁰ (algebraMap F K (algebraMap (𝓞 F) F (u:𝓞 F)))=1 := by
  let v : (𝓞 K)ˣ := Units.map (algebraMap (𝓞 F) (𝓞 K)) u
  have eq : algebraMap F K (algebraMap (𝓞 F) F (u:𝓞 F)) = algebraMap (𝓞 K) K (v : 𝓞 K) := by
    change _ = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (u:𝓞 F))
    rw [←IsScalarTower.algebraMap_apply, ←IsScalarTower.algebraMap_apply]
  rw [eq,← coeIdeal_span_singleton,Ideal.span_singleton_eq_top.mpr v.isUnit]
  rfl

theorem sawin_factor_units (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K] {I J : Ideal (𝓞 K)} (b : K)
    (nz : b ≠ 0) (eq : spanSingleton (𝓞 K)⁰ b * I = (J : FractionalIdeal (𝓞 K)⁰ K))
    (a y : (𝓞 F)ˣ) (hn : Algebra.norm F b = algebraMap (𝓞 F) F (a*y^2 : (𝓞 F)ˣ)) :
    ∃ t : K, t ≠ 0 ∧ spanSingleton (𝓞 K)⁰ t * I = (J : FractionalIdeal (𝓞 K)⁰ K) ∧
      Algebra.norm F t = algebraMap (𝓞 F) F (a : 𝓞 F) := by
  let v := algebraMap (𝓞 F) F ((y⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  have vu : IsUnit v := (y⁻¹).isUnit.map _
  refine ⟨algebraMap F K v * b,mul_ne_zero (vu.map (algebraMap F K)).ne_zero nz,?_,?_⟩
  · rw [←spanSingleton_mul_spanSingleton, sawin_span_unit F K y⁻¹,one_mul,eq]
  · rw [map_mul,Algebra.norm_algebraMap,Algebra.IsQuadraticExtension.finrank_eq_two F K,hn]
    dsimp [v]
    let φ := (algebraMap (𝓞 F) F).toMonoidHom.comp (Units.coeHom (𝓞 F))
    change (φ y⁻¹)^2 * φ (a*y^2)=φ a
    rw [←map_pow,←map_mul]; apply congrArg φ; simp [mul_comm, mul_assoc]


open scoped NumberField nonZeroDivisors
open NumberField FractionalIdeal

theorem sawin_signs (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K] {D : Type*} [Fintype D] (s : D)
    (I : Ideal (𝓞 K)) (J : D → Ideal (𝓞 K)) (inj : Function.Injective J)
    (t : D → K) (nz : ∀ j, t j ≠ 0)
    (moves : ∀ j, spanSingleton (𝓞 K)⁰ (t j) * I = (J j : FractionalIdeal (𝓞 K)⁰ K))
    (norm : ∀ j, Algebra.norm F (t j) = Algebra.norm F (t s)) :
    ∃ B : Finset K, 2*Fintype.card D = B.card ∧
      ∀ β ∈ B, (∀ a ∈ J s, ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = β * algebraMap (𝓞 K) K a) ∧
        Algebra.norm F β=1 := by
  classical
  let q (p : D × Bool) := (if p.2 then -1 else 1 : K) * (t p.1 / t s)
  have signspan (b : Bool) : spanSingleton (𝓞 K)⁰ (if b then -1 else 1 : K)=1 := by
    cases b
    · simp [spanSingleton_one]
    · change spanSingleton (𝓞 K)⁰ (-1 : K) = 1
      rw [show (-1 : K)=algebraMap (𝓞 K) K (-1) by simp,←coeIdeal_span_singleton,
          Ideal.span_singleton_eq_top.mpr (by simp)]
      rfl
  have scale (p : D × Bool) : spanSingleton (𝓞 K)⁰ (q p) * (J s : FractionalIdeal (𝓞 K)⁰ K) = J p.1 := by
    dsimp [q]
    rw [←spanSingleton_mul_spanSingleton, signspan,one_mul, ←moves s,←mul_assoc,
      spanSingleton_mul_spanSingleton,div_mul_cancel₀ _ (nz s),moves]
  have qi : Function.Injective q := by
    intro u v eq
    have eq' := (scale u).symm.trans ((congrArg (fun b => spanSingleton (𝓞 K)⁰ b * (J s : FractionalIdeal (𝓞 K)⁰ K)) eq).trans (scale v))
    have same := inj (FractionalIdeal.coeIdeal_inj.mp eq')
    apply Prod.ext same
    obtain ⟨i,b⟩ := u; obtain ⟨j,c⟩ := v
    change i=j at same; subst j
    have ne := div_ne_zero (nz i) (nz s)
    cases b <;> cases c <;> simp_all [q,neg_eq_self]
    exact (div_ne_zero (nz i) (nz s)) (neg_eq_self.mp eq.symm)
  refine ⟨Finset.univ.image q,by rw [Finset.card_image_of_injective _ qi]; simp [mul_comm],?_⟩
  intro β hβ
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hβ
  constructor
  · intro a ha
    have mem : q p * algebraMap (𝓞 K) K a ∈ (J p.1 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [←scale p]
      exact mem_singleton_mul.mpr ⟨_,mem_coeIdeal_of_mem _ ha,rfl⟩
    obtain ⟨b,_,hb⟩ := (mem_coeIdeal _).mp mem
    exact ⟨b,hb⟩
  · have nn : Algebra.norm F (t s) ≠ 0 := Algebra.norm_ne_zero_iff.mpr (nz s)
    have signnorm (b : Bool) : Algebra.norm F (if b then -1 else 1 : K)=1 := by
      cases b
      · simp
      · change Algebra.norm F (-1:K)=1
        rw [show (-1:K)=algebraMap F K (-1) by simp, Algebra.norm_algebraMap,
          Algebra.IsQuadraticExtension.finrank_eq_two F K]; norm_num
    dsimp only [q]; rw [map_mul,signnorm,one_mul,div_eq_mul_inv,map_mul,Algebra.norm_inv,norm p.1,mul_inv_cancel₀ nn]


end SawinNormFibers
open SawinNormFibers
open scoped Classical nonZeroDivisors NumberField
open NumberField FractionalIdeal

theorem OMA.solution : OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1.H1 := by
  classical
  intro F K _ _ _ _ _ _
  obtain ⟨T,spec⟩ := sawin_class_norm F K
  refine ⟨T,spec,?_⟩
  intro L nonempty nz hn
  let A := {j // j ∈ L}
  let : Nonempty A := nonempty.to_subtype
  let ideal (j : A) : (Ideal (𝓞 K))⁰ := ⟨j.val,mem_nonZeroDivisors_iff_ne_zero.mpr (nz _ j.property)⟩
  let c (j : A) := ClassGroup.mk0 (ideal j)
  let base : A := Classical.arbitrary A
  have norm_eq (i j : A) : T (c i) = T (c j) := by
    obtain ⟨I,hI,hi⟩ := spec (ideal i); obtain ⟨J,hJ,hj⟩ := spec (ideal j)
    have eq : I=J := Subtype.ext ((hI.trans (hn _ i.property _ j.property)).trans hJ.symm)
    exact hi.trans ((congrArg ClassGroup.mk0 eq).trans hj.symm)
  let color (j : A) : T.ker := ⟨c j / c base,by
    change T (c j / c base) = 1; rw [map_div,norm_eq j base, div_self']⟩
  obtain ⟨j₀,hclass⟩ := sawin_heavy color
  let E := {j : A // color j = color j₀}
  let e₀ : E := ⟨j₀,rfl⟩
  let : Nonempty E := ⟨e₀⟩
  have cls (i : E) : c j₀ = c i.val := by
    have h := congrArg Subtype.val i.property
    change c i.val / c base = c j₀ / c base at h
    simpa using h.symm
  obtain ⟨S,size,cover⟩ := sawin_unit_squares F
  have witness (i : E) : ∃ a : S, ∃ t : K, t ≠ 0 ∧
      spanSingleton (𝓞 K)⁰ t * (ideal j₀).val = ((ideal i.val).val : FractionalIdeal (𝓞 K)⁰ K) ∧
      Algebra.norm F t = algebraMap (𝓞 F) F (a.val : 𝓞 F) := by
    obtain ⟨b,hb,move,u,nu⟩ := sawin_principal F K (ideal j₀) (ideal i.val) (cls i) (hn _ j₀.property _ i.val.property)
    obtain ⟨a,ha,y,hu⟩ := cover u
    rw [hu] at nu
    exact ⟨⟨a,ha⟩,sawin_factor_units F K b hb move a y nu⟩
  choose label t ht mt nt using witness
  obtain ⟨e,hsquare⟩ := sawin_heavy label
  let D := {j : E // label j = label e}
  let root : D := ⟨e,rfl⟩
  let J (j : D) : Ideal (𝓞 K) := j.val.val.val
  have ji : Function.Injective J := fun i j h => Subtype.ext (Subtype.ext (Subtype.ext h))
  obtain ⟨B,count,good⟩ := sawin_signs F K root (ideal j₀).val J ji (fun j => t j.val)
    (fun j => ht j.val) (fun j => mt j.val) (fun j => by rw [nt,nt,j.property])
  refine ⟨J root,root.val.val.property,B,good,?_⟩
  have mass : L.card ≤ Fintype.card T.ker * (S.card * Fintype.card D) := by
    have first : L.card ≤ Fintype.card T.ker * Fintype.card E := by
      have ca : Nat.card A = L.card := by simp [Nat.card_eq_fintype_card,A]
      simpa only [←Nat.card_eq_fintype_card,ca,E] using hclass
    have second : Fintype.card E ≤ S.card * Fintype.card D := by
      have cb : Nat.card S = S.card := by simp [Nat.card_eq_fintype_card]
      simpa only [←Nat.card_eq_fintype_card,cb,D] using hsquare
    exact first.trans (Nat.mul_le_mul_left _ second)
  have kr := T.ker.card_mul_index
  rw [Subgroup.index_ker] at kr
  have rr := T.range.card_mul_index
  have iden : Fintype.card T.ker * classNumber F = classNumber K * T.range.index := by
    change Fintype.card T.ker * Fintype.card (ClassGroup (𝓞 F)) = Fintype.card (ClassGroup (𝓞 K)) * T.range.index
    simp only [Nat.card_eq_fintype_card] at kr rr
    rw [←rr,←kr,mul_assoc]
  calc
    2*L.card*classNumber F ≤ 2*(Fintype.card T.ker*(S.card*Fintype.card D))*classNumber F := by gcongr
    _ = (2*Fintype.card D)*S.card*(Fintype.card T.ker*classNumber F) := by ring
    _ ≤ B.card*2^(Module.finrank ℚ F)*(classNumber K*T.range.index) := by rw [count,iden]; gcongr
    _ = _ := by ring
