import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2

open scoped BigOperators
open Polynomial

namespace SharpTensorEven

private noncomputable def nodePoly {I : Type*} [Fintype I] (x : I → ℂ) : ℂ[X] :=
  ∏ i, (X - C (x i))

private lemma nodePoly_monic {I : Type*} [Fintype I] (x : I → ℂ) :
    (nodePoly x).Monic :=
  monic_prod_X_sub_C x _

private lemma nodePoly_degree {I : Type*} [Fintype I] (x : I → ℂ) :
    (nodePoly x).natDegree = Fintype.card I := by
  rw [nodePoly, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]

private lemma nodePoly_eval {I : Type*} [Fintype I] (x : I → ℂ) (z : ℂ) :
    (nodePoly x).eval z = ∏ i, (z-x i) := by
  simp only [nodePoly, eval_prod, eval_sub, eval_X, eval_C]

private lemma nodePoly_root {I : Type*} [Fintype I] (x : I → ℂ) (i : I) :
    (nodePoly x).eval (x i) = 0 := by
  classical
  rw [nodePoly_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

private lemma nodePoly_ne_zero_at {I : Type*} [Fintype I] (x : I → ℂ) (z : ℂ)
    (hne : ∀ i, z ≠ x i) : (nodePoly x).eval z ≠ 0 := by
  rw [nodePoly_eval]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hne i)

private lemma nodePoly_dvd {I : Type*} [Fintype I] {x : I → ℂ} (hx : Function.Injective x)
    {p : ℂ[X]} (roots : ∀ i, p.eval (x i) = 0) : nodePoly x ∣ p :=
  Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hx)
    (fun i => dvd_iff_isRoot.mpr (roots i))

private lemma equals_scalar_nodes {I : Type*} [Fintype I] {x : I → ℂ} (hx : Function.Injective x)
    {p : ℂ[X]} (deg : p.natDegree ≤ Fintype.card I) (roots : ∀ i, p.eval (x i)=0) :
    p = C p.leadingCoeff * nodePoly x := by
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (nodePoly_monic x) (nodePoly_dvd hx roots)
  simpa only [nodePoly_degree] using deg

private lemma zero_of_many_roots {I : Type*} [Fintype I] {x : I → ℂ} (hx : Function.Injective x)
    {p : ℂ[X]} (deg : p.natDegree < Fintype.card I) (roots : ∀ i, p.eval (x i)=0) :
    p = 0 :=
  eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hx roots deg

private noncomputable def quotientAt (p : ℂ[X]) (z : ℂ) : ℂ[X] :=
  p /ₘ (X - C z)

private lemma quotientAt_split (p : ℂ[X]) (z : ℂ) :
    C (p.eval z) + (X - C z) * quotientAt p z = p := by
  rw [quotientAt, ← modByMonic_X_sub_C_eq_C_eval, modByMonic_add_div]

private lemma quotientAt_degree (p : ℂ[X]) (z : ℂ) :
    (quotientAt p z).natDegree = p.natDegree - 1 := by
  simp only [quotientAt, natDegree_divByMonic p (monic_X_sub_C z), natDegree_X_sub_C]

private lemma quotientAt_coeff {p : ℂ[X]} {n : ℕ} (hp : p.natDegree ≤ n+1) (z : ℂ) :
    (quotientAt p z).coeff n = p.coeff (n+1) := by
  have hdeg : (quotientAt p z).natDegree ≤ n := by rw [quotientAt_degree]; omega
  have h := congrArg (fun q : ℂ[X] => q.coeff (n+1)) (quotientAt_split p z)
  simp only [coeff_add, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_C,
    Nat.succ_ne_zero, if_false, zero_add, coeff_eq_zero_of_natDegree_lt (show
      (quotientAt p z).natDegree < n+1 by omega), mul_zero, sub_zero] at h
  exact h

private lemma quotientAt_eval (p : ℂ[X]) {z x : ℂ} (hne : x ≠ z) :
    (quotientAt p z).eval x = (p.eval x - p.eval z) / (x-z) := by
  apply (eq_div_iff (sub_ne_zero.mpr hne)).mpr
  have h := congrArg (fun q : ℂ[X] => q.eval x) (quotientAt_split p z)
  simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X] at h
  linear_combination h

private noncomputable def numerator {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℂ) (v : I → ℂ) : ℂ[X] :=
  ∑ i, C (v i) * ∏ j ∈ Finset.univ.erase i, (X - C (s j))

private lemma numerator_degree {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℂ) (v : I → ℂ) : (numerator s v).natDegree ≤ Fintype.card I-1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]

private lemma numerator_coeff {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℂ) (v : I → ℂ) : (numerator s v).coeff (Fintype.card I-1) = ∑ i, v i := by
  simp only [numerator, finsetSum_coeff, coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  have monic := monic_prod_X_sub_C s (Finset.univ.erase i)
  have deg := natDegree_finsetProd_X_sub_C_eq_card (Finset.univ.erase i) s
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] at deg
  rw [← deg, monic.coeff_natDegree, mul_one]

private lemma numerator_eval {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℂ) (v : I → ℂ) {z : ℂ} (hne : ∀ i, z ≠ s i) :
    (numerator s v).eval z = (nodePoly s).eval z * ∑ i, v i/(z-s i) := by
  simp only [numerator, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X,
    nodePoly_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have fact := Finset.prod_erase_mul Finset.univ (fun j => z-s j) (Finset.mem_univ i)
  rw [← fact]
  field_simp [sub_ne_zero.mpr (hne i)]

private lemma numerator_at_root {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℂ) (v : I → ℂ) (i : I) :
    (numerator s v).eval (s i) = v i * ∏ j ∈ Finset.univ.erase i, (s i-s j) := by
  simp only [numerator, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  rw [Finset.sum_eq_single i]
  · intro j _ hj
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_univ i⟩) (sub_self _), mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, mul_eq_zero, IsEmpty.forall_iff]

private lemma rank_of_special_rows {m : ℕ} (hm : 2 ≤ m)
    (values : Fin (m+2) → Fin m → ℂ) (α : Fin m → ℂ) (β : ℂ)
    (matrix : ∀ a, (∑ g, values a g * α g) = (1-∏ g, (1-values a g))*β)
    (unit : ∀ i j, values (Fin.castLE (by omega) i) j = if i=j then 1 else 0)
    (two : ∀ j, values (⟨m, by omega⟩ : Fin (m+2)) j =
      if j.val=0 ∨ j.val=1 then 1 else 0) : α=0 ∧ β=0 := by
  classical
  have all (i : Fin m) : α i = β := by
    have r := matrix (Fin.castLE (by omega : m ≤ m+2) i)
    simp only [unit] at r
    have prod : (∏ g : Fin m, (1-(if i=g then 1 else 0) : ℂ)) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [↓reduceIte, sub_self])
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, prod,
      sub_zero] using r
  have r := matrix (⟨m, by omega⟩ : Fin (m+2))
  simp only [two, all] at r
  let z : Fin m := ⟨0, by omega⟩
  let o : Fin m := ⟨1, by omega⟩
  have diff : z ≠ o := by intro eq; have := congrArg Fin.val eq; norm_num [z,o] at this
  have terms (i : Fin m) : (if i.val=0 ∨ i.val=1 then (1:ℂ) else 0)*β =
      (if i=z then β else 0) + (if i=o then β else 0) := by
    have ziff : i.val=0 ↔ i=z := ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    have oiff : i.val=1 ↔ i=o := ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    by_cases iz : i=z <;> by_cases io : i=o <;> simp_all only [ite_mul, one_mul, zero_mul, ne_eq,
      iff_false, or_self, ↓reduceIte, add_zero, iff_true, zero_ne_one, not_false_eq_true, or_false,
      left_eq_add, not_true_eq_false, reduceCtorEq, false_iff, one_ne_zero, or_true, zero_add]
  have prod : (∏ g : Fin m, (1-(if g.val=0 ∨ g.val=1 then 1 else 0) : ℂ)) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ z) (by simp only [zero_ne_one, or_false, ↓reduceIte,
      sub_self, z])
  simp only [prod, terms, Finset.sum_add_distrib] at r
  have bzero : β=0 := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, sub_zero, one_mul, add_eq_left] at r
    exact r
  exact ⟨funext fun i => (all i).trans bzero, bzero⟩

end SharpTensorEven
namespace SharpTensorEven

private lemma coefficient_from_two_values {m : ℕ} (v : Fin m → ℂ)
    (distinct : Function.Injective v) {x : ℂ} (hx : x ≠ 0)
    (npos : (nodePoly v).eval x ≠ 0) (nneg : (nodePoly v).eval (-x) ≠ 0)
    (p : ℂ[X]) (deg : p.natDegree ≤ m+1) (roots : ∀ i,p.eval (v i)=0) :
    p.coeff (m+1) =
      (p.eval x / (nodePoly v).eval x - p.eval (-x) / (nodePoly v).eval (-x)) / (2*x) := by
  obtain ⟨q, rfl⟩ := nodePoly_dvd distinct roots
  by_cases hq : q=0
  · simp only [hq, mul_zero, coeff_zero, eval_zero, zero_div, sub_self]
  have dq : q.natDegree ≤ 1 := by
    rw [natDegree_mul (nodePoly_monic v).ne_zero hq, nodePoly_degree, Fintype.card_fin] at deg
    omega
  have hxq : (nodePoly v * q).eval x / (nodePoly v).eval x = q.eval x := by
    rw [eval_mul]
    field_simp
  have hyq : (nodePoly v * q).eval (-x) / (nodePoly v).eval (-x) = q.eval (-x) := by
    rw [eval_mul]
    field_simp
  rw [hxq,hyq,eq_X_add_C_of_natDegree_le_one dq]
  rw [show nodePoly v*(C (q.coeff 1)*X+C (q.coeff 0)) =
      X*(C (q.coeff 1)*nodePoly v)+C (q.coeff 0)*nodePoly v by ring]
  simp only [coeff_add, coeff_X_mul, coeff_C_mul, eval_add, eval_mul, eval_C, eval_X]
  have lead := (nodePoly_monic v).coeff_natDegree
  rw [nodePoly_degree, Fintype.card_fin] at lead
  have z : (nodePoly v).coeff (m+1)=0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [nodePoly_degree,Fintype.card_fin]; omega)
  rw [lead,z]
  field_simp
  ring

private noncomputable def residueCorrection (E D : ℂ[X]) (s : ℂ) : ℂ[X] :=
  quotientAt (E - C (E.eval (-s) / D.eval (-s)) * D) (-s)

private lemma residueCorrection_degree {m : ℕ} {E D : ℂ[X]}
    (e : E.natDegree ≤ m+2) (d : D.natDegree ≤ m+2) (s : ℂ) :
    (residueCorrection E D s).natDegree ≤ m+1 := by
  rw [residueCorrection, quotientAt_degree]
  have cap : (E - C (E.eval (-s) / D.eval (-s)) * D).natDegree ≤ m+2 := by
    simpa only [max_self] using natDegree_sub_le_of_le e ((natDegree_C_mul_le _ _).trans d)
  omega

private lemma residueCorrection_coeff {m : ℕ} {E D : ℂ[X]}
    (e : E.natDegree ≤ m+2) (d : D.natDegree ≤ m+2)
    (et : E.coeff (m+2)=1) (dt : D.coeff (m+2)=1) (s : ℂ) :
    (residueCorrection E D s).coeff (m+1)=1-E.eval (-s)/D.eval (-s) := by
  have cap : (E - C (E.eval (-s) / D.eval (-s)) * D).natDegree ≤ m+2 := by
    simpa only [max_self] using natDegree_sub_le_of_le e ((natDegree_C_mul_le _ _).trans d)
  rw [residueCorrection, quotientAt_coeff (n:=m+1) cap, coeff_sub, coeff_C_mul,
    et,dt,mul_one]

private lemma residueCorrection_eval {E D : ℂ[X]} {s x : ℂ}
    (good : D.eval (-s) ≠ 0) (root : D.eval x = 0) (hne : x ≠ -s) :
    (residueCorrection E D s).eval x=E.eval x/(x+s) := by
  unfold residueCorrection
  rw [quotientAt_eval _ hne, sub_neg_eq_add]
  simp only [eval_sub,eval_mul,eval_C,root,mul_zero,sub_zero]
  have e : E.eval (-s) - E.eval (-s) / D.eval (-s) * D.eval (-s) = 0 := by
    field_simp
    ring
  rw [e,sub_zero]

private lemma normalized_entry {x y s : ℂ} (hx : x-s ≠ 0) (hy : x+y ≠ 0) :
    ((-x - s)*(x-y))/((-x-y)*(x-s)) =
      1-2*x*(y-s)/((x+y)*(x-s)) := by
  have n : -x-y ≠ 0 := by
    rw [show -x-y = -(x+y) by ring]
    exact neg_ne_zero.mpr hy
  field_simp
  ring

private lemma degree_drop {p : ℂ[X]} {n : ℕ} (top : p.coeff (n+1)=0)
    (bound : p.natDegree ≤ n+1) : p.natDegree ≤ n := by
  by_contra! bad
  have eq : p.natDegree=n+1 := by omega
  have nz : p ≠ 0 := by intro h; simp only [h, natDegree_zero, Nat.right_eq_add, Nat.add_eq_zero_iff,
    one_ne_zero, and_false] at eq
  exact (leadingCoeff_ne_zero.mpr nz) (by rw [leadingCoeff,eq]; exact top)

end SharpTensorEven
namespace SharpTensorEven

private abbrev Group (m : ℕ) := Fin m
private abbrev Color (m : ℕ) := Fin (m+2)
private abbrev Mark (m : ℕ) := (Option (Group m) × Color m) ⊕ Group m

private def fullMark {m : ℕ} (g : Group m) : Option (Color m) → Mark m
  | none => .inr g
  | some a => .inl (some g,a)

private def smallMark {m : ℕ} (a : Color m) : Mark m := .inl (none,a)

private def node {m : ℕ} (s : Group m→ℂ) (v : Group m → Color m→ℂ)
    (x : Color m→ℂ) : Mark m→ℂ :=
  Sum.elim (fun p => p.1.elim (x p.2) (fun g => v g p.2)) s

private def read {m : ℕ} (f : Option (Color m)→ℂ) : Mark m→ℂ
  | .inr _ => f none
  | .inl (some _,a) => f (some a)
  | .inl (none,a) => f (some a)+f none

private lemma fullMark_injective {m : ℕ} (g : Group m) : Function.Injective (fullMark g) := by
  intro i j h
  cases i <;> cases j <;> simp_all only [fullMark, Sum.inl.injEq, Prod.mk.injEq, true_and, reduceCtorEq]

private lemma smallMark_injective {m : ℕ} : Function.Injective (@smallMark m) := by
  intro a b h
  simpa only [smallMark, Sum.inl.injEq, Prod.mk.injEq, true_and] using h

private noncomputable def moments {m : ℕ} (s : Group m→ℂ) (v : Group m → Color m→ℂ) (x : Color m→ℂ)
    (a : Color m) (g : Group m) : ℂ :=
  2*x a*(v g a-s g)/((x a+v g a)*(x a-s g))

private noncomputable def fullNumerator {m : ℕ} (t : Mark m→ℂ)
    (f : Mark m→Option (Color m)→ℂ) (g : Group m) (c : Option (Color m)) : ℂ[X] :=
  numerator (fun k => -t (fullMark g k)) (fun k => f (fullMark g k) c)

-- After clearing the simple poles, each coordinate of a full block has a prescribed set of roots.
private lemma full_numerator_shape {m : ℕ}
    (s : Group m→ℂ) (v : Group m → Color m→ℂ) (x : Color m→ℂ)
    (t : Mark m→ℂ) (ht : t = node s v x)
    (distinct : Function.Injective t) (regular : ∀ j i,t j+t i≠0)
    (f : Mark m→Option (Color m)→ℂ)
    (diagonal : ∀ i,read (f i) i=0)
    (mass : ∀ g c, (∑ i, f (fullMark g i) c)=0)
    (pole : ∀ g j, (∑ i, read (f (fullMark g i)) j/(t j+t (fullMark g i)))=0)
    (g : Group m) :
    let S := nodePoly s
    let P (a : Color m) := nodePoly (fun j => v j a)
    let U := fullNumerator t f g
    (U none = C (U none).leadingCoeff * (S*(X-C (-s g)))) ∧
    (∀ a, U (some a)=C (U (some a)).leadingCoeff * (P a*(X-C (-v g a)))) ∧
    (∀ a, (U (some a)).eval (x a)+(U none).eval (x a)=0) := by
  intro S P U
  have lower c : (U c).natDegree ≤ m+1 := by
    have size : Fintype.card (Option (Color m))-1=m+2 := by
      simp only [Fintype.card_option, Fintype.card_fin, add_tsub_cancel_right]
    apply degree_drop
    · change (numerator (fun k => -t (fullMark g k)) (fun k => f (fullMark g k) c)).coeff (m+2)=0
      have h := (numerator_coeff (fun k => -t (fullMark g k)) (fun k => f (fullMark g k) c)).trans (mass g c)
      simpa only [size] using h
    · change (numerator (fun k => -t (fullMark g k)) (fun k => f (fullMark g k) c)).natDegree ≤ m+2
      simpa only [size] using numerator_degree (fun k => -t (fullMark g k)) (fun k => f (fullMark g k) c)
  have posEval (j : Mark m) (c : Option (Color m)) :
      (U c).eval (t j) = (nodePoly (fun k => -t (fullMark g k))).eval (t j) *
        ∑ k, f (fullMark g k) c/(t j+t (fullMark g k)) := by
    simpa only [U,fullNumerator,sub_neg_eq_add] using
      numerator_eval (fun k => -t (fullMark g k)) (fun k => f (fullMark g k) c)
        (fun k eq => regular j _ ((congrArg (· + t (fullMark g k)) eq).trans (neg_add_cancel _)))
  have negative (k : Option (Color m)) : (U k).eval (-t (fullMark g k))=0 := by
    rw [show (U k).eval (-t (fullMark g k)) =
        f (fullMark g k) k * ∏ j ∈ Finset.univ.erase k, (-t (fullMark g k) - -t (fullMark g j)) from
          numerator_at_root (fun j => -t (fullMark g j)) (fun j => f (fullMark g j) k) k]
    have zero : f (fullMark g k) k=0 := by
      cases k with
      | none => exact diagonal (.inr g)
      | some a => exact diagonal (.inl (some g,a))
    rw [zero,zero_mul]
  have posShort (j : Group m) : (U none).eval (s j)=0 := by
    have e := posEval (.inr j) none
    have z := pole g (.inr j)
    simp only [read] at z
    rw [z,mul_zero] at e
    simpa only [ht, node, Sum.elim_inr] using e
  have posColor (j : Group m) (a : Color m) : (U (some a)).eval (v j a)=0 := by
    have e := posEval (.inl (some j,a)) (some a)
    have z := pole g (.inl (some j,a))
    simp only [read] at z
    rw [z,mul_zero] at e
    simpa only [ht, node, Sum.elim_inl, Option.elim_some] using e
  have factor {z : Group m→ℂ} {w : ℂ} {p : ℂ[X]}
      (inj : Function.Injective z) (opposite : ∀ j,w≠z j) (degree : p.natDegree ≤ m+1)
      (roots : ∀ j,p.eval (z j)=0) (extra : p.eval w=0) :
      p=C p.leadingCoeff*(nodePoly z*(X-C w)) := by
    let y : Option (Group m)→ℂ := fun q => q.elim w z
    have yinj : Function.Injective y := by
      intro i j eq
      cases i <;> cases j
      · rfl
      · exact (opposite _ eq).elim
      · exact (opposite _ eq.symm).elim
      · exact congrArg Option.some (inj eq)
    have core := equals_scalar_nodes yinj (p:=p) (by simpa only [Fintype.card_option,
      Fintype.card_fin] using degree)
      (fun i => match i with | none => extra | some j => roots j)
    simpa only [nodePoly, y, Fintype.prod_option, Option.elim_none, Option.elim_some,
      mul_comm (X - C w)] using core
  have negShort : (U none).eval (-s g) = 0 := by
    simpa only [ht, node, fullMark, Sum.elim_inr] using negative none
  have negColor (a : Color m) : (U (some a)).eval (-v g a) = 0 := by
    simpa only [ht, node, fullMark, Sum.elim_inl, Option.elim_some] using negative (some a)
  refine ⟨factor ?_ ?_ (lower none) posShort negShort,
    fun a => factor ?_ ?_ (lower (some a)) (fun j => posColor j a) (negColor a), ?_⟩
  · intro i j e
    exact Sum.inr.inj (distinct (by simpa only [ht,node,Sum.elim_inr] using e))
  · intro j e
    exact regular (.inr g) (.inr j) (by simp only [ht,node,Sum.elim_inr]; rw [←e,add_neg_cancel])
  · intro i j e
    exact Option.some.inj (congrArg Prod.fst (Sum.inl.inj
      (distinct (by simpa only [ht, node, Sum.elim_inl,
        Option.elim_some] using e) : (.inl (some i,a) : Mark m) = .inl (some j,a))))
  · intro j e
    exact regular (.inl (some g,a)) (.inl (some j,a)) (by simp only [ht, node, Sum.elim_inl,
      Option.elim_some, ← e, add_neg_cancel])
  · intro a
    have z := pole g (smallMark a)
    simp only [smallMark,read,add_div,Finset.sum_add_distrib] at z
    have p := posEval (smallMark a) (some a)
    have q := posEval (smallMark a) none
    have eq := congrArg₂ (· + ·) p q
    dsimp only [smallMark] at eq
    rw [← mul_add,z,mul_zero] at eq
    simpa only [ht, node, Sum.elim_inl, Option.elim_none] using eq

end SharpTensorEven
namespace SharpTensorEven

private noncomputable def smallNumerator {m : ℕ} (x : Color m→ℂ)
    (f : Mark m→Option (Color m)→ℂ) (c : Option (Color m)) : ℂ[X] :=
  numerator (fun a => -x a) (fun a => f (smallMark a) c)

-- The last relation samples the small block and each full block’s short node. Compare the leading coefficients after interpolation at each color.
private lemma small_numerator_moments {m : ℕ}
    (s : Group m→ℂ) (v : Group m → Color m→ℂ) (x : Color m→ℂ)
    (t : Mark m→ℂ) (ht : t = node s v x)
    (distinct : Function.Injective t) (regular : ∀ j i,t j+t i≠0)
    (f : Mark m→Option (Color m)→ℂ)
    (diagonal : ∀ i,read (f i) i=0)
    (short : ∀ g,f (.inr g) none=0)
    (mass : ∀ c,(∑ a,f (smallMark a) c)+(∑ g,f (.inr g) c)=0)
    (pole : ∀ j,(∑ a,read (f (smallMark a)) j/(t j+x a))+
      (∑ g,read (f (.inr g)) j/(t j+s g))=0) :
    let S := nodePoly s
    let P (a : Color m) := nodePoly (fun g => v g a)
    let E := nodePoly (fun a => -x a)
    let D (a : Color m) := P a*((X-C (x a))*(X-C (-x a)))
    let U := smallNumerator x f
    let β := (U none).leadingCoeff
    U none=C β*S ∧ ∀ a,
      (∑ g, f (.inr g) (some a)*E.eval (-s g)/(D a).eval (-s g)) =
        β*((S.eval (x a)/(P a).eval (x a)-S.eval (-x a)/(P a).eval (-x a))/(2*x a)) := by
  intro S P E D U β
  have tS (g : Group m) : t (.inr g)=s g := by simp only [ht, node, Sum.elim_inr]
  have tX (a : Color m) : t (smallMark a)=x a := by simp only [ht, node, smallMark, Sum.elim_inl,
    Option.elim_none]
  have tV (g : Group m) (a : Color m) : t (.inl (some g,a))=v g a := by simp only [ht, node, Sum.elim_inl,
    Option.elim_some]
  have differ {i j : Mark m} (ne : i≠j) : t i≠t j := distinct.ne ne
  have nz (j i : Mark m) : t j≠-t i := fun h =>
    regular j i ((congrArg (·+t i) h).trans (neg_add_cancel _))
  have xNonzero (a : Color m) : x a≠0 := fun h => regular (smallMark a) (smallMark a)
    (by simp only [tX, h, add_zero])
  have cap (c : Option (Color m)) : (U c).natDegree ≤ m+1 := by
    simpa only [U, smallNumerator, Fintype.card_fin, Nat.add_one_sub_one] using
      numerator_degree (fun a => -x a) (fun a => f (smallMark a) c)
  have top (c : Option (Color m)) : (U c).coeff (m+1)=-(∑ g,f (.inr g) c) := by
    have sm := numerator_coeff (fun a => -x a) (fun a => f (smallMark a) c)
    have ee : (U c).coeff (m+1)=∑ a,f (smallMark a) c := by
      simpa only [U,smallNumerator,Fintype.card_fin,show m+2-1=m+1 by omega] using sm
    linear_combination ee + mass c
  have posEval (j : Mark m) (c : Option (Color m)) :
      (U c).eval (t j) = E.eval (t j)*∑ a,f (smallMark a) c/(t j+x a) := by
    simp only [U,E,smallNumerator]
    simpa only [sub_neg_eq_add] using
      numerator_eval (fun a => -x a) (fun a => f (smallMark a) c)
        (fun a => by rw [←tX]; exact nz j _)
  have sInject : Function.Injective s := by
    intro g h eq
    exact Sum.inr.inj (distinct (by simpa only [tS] using eq))
  have sU : U none=C β*S := by
    apply equals_scalar_nodes sInject
    · simp only [Fintype.card_fin]
      apply degree_drop ?_ (cap none)
      simp only [top,short,Finset.sum_const_zero,neg_zero]
    · intro g
      have root := pole (.inr g)
      simp only [read,short,zero_div,Finset.sum_const_zero,add_zero] at root
      have z := posEval (.inr g) none
      rw [root,mul_zero] at z
      simpa only [tS] using z
  refine ⟨sU,fun a => ?_⟩
  let ρ (g : Group m) := f (.inr g) (some a)
  have degE : E.natDegree=m+2 := by simp only [nodePoly_degree, Fintype.card_fin, E]
  have monicD : (D a).Monic :=
    (nodePoly_monic _).mul ((monic_X_sub_C _).mul (monic_X_sub_C _))
  have degD : (D a).natDegree=m+2 := by
    change ((nodePoly (fun g => v g a))*((X-C (x a))*(X-C (-x a)))).natDegree=_
    rw [natDegree_mul (nodePoly_monic _).ne_zero
      ((monic_X_sub_C _).mul (monic_X_sub_C _)).ne_zero,
      natDegree_mul (monic_X_sub_C _).ne_zero (monic_X_sub_C _).ne_zero,
      nodePoly_degree,Fintype.card_fin,natDegree_X_sub_C,natDegree_X_sub_C]
  have evalD (z : ℂ) : (D a).eval z=(P a).eval z*((z-x a)*(z+x a)) := by
    simp only [D,eval_mul,eval_sub,eval_X,eval_C,sub_neg_eq_add]
  have good (g : Group m) : (D a).eval (-s g)≠0 := by
    rw [evalD]
    apply mul_ne_zero
    · apply nodePoly_ne_zero_at
      intro j
      rw [←tS,←tV]
      exact (Ne.symm (nz (.inl (some j,a)) (.inr g)))
    · apply mul_ne_zero
      · apply sub_ne_zero.mpr
        rw [←tS,←tX]
        exact (Ne.symm (nz (smallMark a) (.inr g)))
      · rw [← sub_neg_eq_add,ne_eq,sub_eq_zero,neg_inj]
        rw [←tS,←tX]
        exact differ (by simp only [smallMark, ne_eq, reduceCtorEq, not_false_eq_true])
  let W := U (some a)+∑ g,C (ρ g)*residueCorrection E (D a) (s g)
  have degW : W.natDegree ≤ m+1 := by
    apply (natDegree_add_le _ _).trans
    apply max_le (cap _)
    apply natDegree_sum_le_of_forall_le
    intro g _
    exact (natDegree_C_mul_le _ _).trans (residueCorrection_degree degE.le degD.le _)
  have evalW {z : ℂ} (root : (D a).eval z=0) (hne : ∀ g,z≠-s g) :
      W.eval z=(U (some a)).eval z+E.eval z*(∑ g,ρ g/(z+s g)) := by
    simp only [W,eval_add,eval_finsetSum,eval_mul,eval_C,
      residueCorrection_eval (good _) root (hne _),Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    ring
  have topW : W.coeff (m+1)= -(∑ g, ρ g*E.eval (-s g)/(D a).eval (-s g)) := by
    simp only [W,coeff_add,finsetSum_coeff,coeff_C_mul,top,residueCorrection_coeff degE.le degD.le
      (by rw [←degE]; exact (nodePoly_monic _).coeff_natDegree)
      (by rw [←degD]; exact monicD.coeff_natDegree)]
    change -(∑ g,ρ g)+∑ g,ρ g*(1-E.eval (-s g)/(D a).eval (-s g))=_
    simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib,div_eq_mul_inv,mul_assoc]
    ring
  have vgRoot (g : Group m) : (D a).eval (v g a)=0 := by
    rw [evalD,nodePoly_root (fun j => v j a) g,zero_mul]
  have rootsW (g : Group m) : W.eval (v g a)=0 := by
    have z := evalW (vgRoot g) (fun j => by rw [←tV,←tS]; exact nz _ _)
    have pe := posEval (.inl (some g,a)) (some a)
    have cp := pole (.inl (some g,a))
    simp only [tV,read] at pe cp
    rw [z,pe,← mul_add,cp,mul_zero]
  have xRoot : (D a).eval (x a)=0 := by rw [evalD,sub_self,zero_mul,mul_zero]
  have nxRoot : (D a).eval (-x a)=0 := by rw [evalD,neg_add_cancel,mul_zero,mul_zero]
  have atX : W.eval (x a)= -β*S.eval (x a) := by
    have z := evalW xRoot (fun j => by rw [←tX,←tS]; exact nz _ _)
    have ps := posEval (smallMark a) (some a)
    have sh := posEval (smallMark a) none
    have h := pole (smallMark a)
    rw [tX] at h
    simp only [smallMark,read,add_div,Finset.sum_add_distrib,short,add_zero] at h
    have shY : (U none).eval (x a)=β*S.eval (x a) := by rw [sU,eval_mul,eval_C]
    simp only [tX] at ps sh
    rw [shY] at sh
    rw [z,ps]
    have eq : (∑ a',f (smallMark a') (some a)/(x a+x a'))+
        (∑ a',f (smallMark a') none/(x a+x a'))+
        (∑ g,ρ g/(x a+s g))=0 := by simpa only [ρ,smallMark] using h
    linear_combination E.eval (x a)*eq + sh
  have atNX : W.eval (-x a)= -β*S.eval (-x a) := by
    have z := evalW nxRoot (fun j => by
      apply neg_injective.ne
      rw [←tX,←tS]
      exact differ (by simp only [smallMark, ne_eq, reduceCtorEq, not_false_eq_true]))
    have e : E.eval (-x a)=0 := nodePoly_root (fun k => -x k) a
    rw [z,e,zero_mul,add_zero]
    have h₁ := numerator_at_root (fun k => -x k) (fun k => f (smallMark k) (some a)) a
    have h₂ := numerator_at_root (fun k => -x k) (fun k => f (smallMark k) none) a
    have sum : (U (some a)).eval (-x a)+(U none).eval (-x a)=0 := by
      change (smallNumerator x f (some a)).eval (-x a)+(smallNumerator x f none).eval (-x a)=0
      unfold smallNumerator
      rw [h₁,h₂,← add_mul]
      have zero := diagonal (smallMark a)
      change f (smallMark a) (some a)+f (smallMark a) none=0 at zero
      rw [zero,zero_mul]
    rw [sU,eval_mul,eval_C] at sum
    linear_combination sum
  have coeff := coefficient_from_two_values (fun g => v g a)
    (fun i j he => Option.some.inj (congrArg Prod.fst (Sum.inl.inj
      (distinct (by simpa only [tV] using he) : (.inl (some i,a) : Mark m)=.inl (some j,a)))))
    (xNonzero a)
    (nodePoly_ne_zero_at _ _ (fun g => by rw [←tX,←tV]; exact differ (by simp only [smallMark, ne_eq,
      Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, and_true, not_false_eq_true])))
    (nodePoly_ne_zero_at _ _ (fun g => by rw [←tX,←tV]; exact (nz _ _).symm))
    W degW rootsW
  change W.coeff (m+1) = (W.eval (x a)/(P a).eval (x a) -
    W.eval (-x a)/(P a).eval (-x a))/(2*x a) at coeff
  rw [topW,atX,atNX] at coeff
  change (∑ g,ρ g*E.eval (-s g)/(D a).eval (-s g))=_
  linear_combination -coeff

end SharpTensorEven
namespace SharpTensorEven

private lemma zero_residues {I : Type*} [Fintype I] [DecidableEq I]
    (s : I→ℂ) (inj : Function.Injective s) (f : I→ℂ) (zero : numerator s f=0) :
    f=0 := by
  funext i
  have e := numerator_at_root s f i
  rw [zero,eval_zero] at e
  exact (mul_eq_zero.mp e.symm).resolve_right (Finset.prod_ne_zero_iff.mpr
    (fun j hj => sub_ne_zero.mpr (inj.ne (Ne.symm (Finset.ne_of_mem_erase hj)))))

-- Normalize the resulting equations using the nonzero node differences, then recover each residue.
private lemma block_kernel {m : ℕ}
    (s : Group m→ℂ) (v : Group m → Color m→ℂ) (x : Color m→ℂ)
    (test : ∀ α : Group m→ℂ, ∀ β : ℂ,
      (∀ a, (∑ g,moments s v x a g*α g)=(1-∏ g, (1-moments s v x a g))*β) →
      α=0 ∧ β=0)
    (t : Mark m→ℂ) (ht : t = node s v x)
    (distinct : Function.Injective t) (regular : ∀ j i,t j+t i≠0)
    (f : Mark m→Option (Color m)→ℂ)
    (diagonal : ∀ i,read (f i) i=0)
    (mass : ∀ g c, (∑ i, f (fullMark g i) c)=0)
    (pole : ∀ g j, (∑ i, read (f (fullMark g i)) j/(t j+t (fullMark g i)))=0)
    (massSmall : ∀ c,(∑ a,f (smallMark a) c)+(∑ g,f (.inr g) c)=0)
    (poleSmall : ∀ j,(∑ a,read (f (smallMark a)) j/(t j+x a))+
      (∑ g,read (f (.inr g)) j/(t j+s g))=0) :
    f=0 := by
  have tS (g : Group m) : t (.inr g)=s g := by simp only [ht, node, Sum.elim_inr]
  have tX (a : Color m) : t (smallMark a)=x a := by simp only [ht, node, smallMark, Sum.elim_inl,
    Option.elim_none]
  have tV (g : Group m) (a : Color m) : t (.inl (some g,a))=v g a := by simp only [ht, node, Sum.elim_inl,
    Option.elim_some]
  have differ {i j : Mark m} (ne : i≠j) : t i≠t j := distinct.ne ne
  have nz (j i : Mark m) : t j≠-t i := fun h =>
    regular j i ((congrArg (·+t i) h).trans (neg_add_cancel _))
  have xne (a : Color m) : x a≠0 := fun h => regular (smallMark a) (smallMark a) (by simp only [tX, h,
    add_zero])
  have regXV (a : Color m) (g : Group m) : x a+v g a≠0 := by
    rw [←tX,←tV]
    exact regular _ _
  have regXS (a : Color m) (g : Group m) : x a+s g≠0 := by
    rw [←tX,←tS]
    exact regular _ _
  have distinctXS (a : Color m) (g : Group m) : x a-s g≠0 := by
    apply sub_ne_zero.mpr
    rw [←tX,←tS]
    exact differ (by simp only [smallMark, ne_eq, reduceCtorEq, not_false_eq_true])
  have short (g : Group m) : f (.inr g) none=0 := diagonal (.inr g)
  let S := nodePoly s
  let P (a : Color m) := nodePoly (fun g => v g a)
  let E := nodePoly (fun a => -x a)
  let D (a : Color m) := P a*((X-C (x a))*(X-C (-x a)))
  let B (g : Group m) := fullNumerator t f g
  let U := smallNumerator x f
  let β := (U none).leadingCoeff
  let α (g : Group m) := (B g none).leadingCoeff
  let A (g : Group m) (a : Color m) := (B g (some a)).leadingCoeff
  let R (g : Group m) := ∏ a, (v g a-s g)
  let scaled (g : Group m) := α g*E.eval (-s g)/R g
  obtain ⟨smallShape, equations⟩ :=
    small_numerator_moments s v x t ht distinct regular f diagonal short massSmall poleSmall
  change U none=C β*S at smallShape
  change ∀ a, (∑ g, f (.inr g) (some a)*E.eval (-s g)/(D a).eval (-s g)) =
    β*((S.eval (x a)/(P a).eval (x a)-S.eval (-x a)/(P a).eval (-x a))/(2*x a)) at equations
  have shape (g : Group m) := full_numerator_shape s v x t ht distinct regular f diagonal mass pole g
  have normalShape (g : Group m) (a : Color m) :
      B g (some a)=C (A g a)*(P a*(X-C (-v g a))) := (shape g).2.1 a
  have shortShape (g : Group m) : B g none=C (α g)*(S*(X-C (-s g))) := (shape g).1
  have coeffX (a : Color m) : (P a).eval (x a)≠0 := by
    apply nodePoly_ne_zero_at
    intro j
    rw [←tX,←tV]
    exact differ (by simp only [smallMark, ne_eq, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, and_true,
      not_false_eq_true])
  have coeffNX (a : Color m) : (P a).eval (-x a)≠0 := by
    apply nodePoly_ne_zero_at
    intro j
    rw [←tX,←tV]
    exact (nz _ _).symm
  have coeffS (a : Color m) : S.eval (x a)≠0 :=
    nodePoly_ne_zero_at s (x a) (fun g => sub_ne_zero.mp (distinctXS a g))
  have coeffE (g : Group m) : E.eval (-s g)≠0 := by
    apply nodePoly_ne_zero_at
    intro a
    apply neg_injective.ne
    exact Ne.symm (sub_ne_zero.mp (distinctXS a g))
  have coeffR (g : Group m) : R g≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    apply sub_ne_zero.mpr
    rw [←tV,←tS]
    exact differ (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
  have mix (g : Group m) (a : Color m) :
      A g a*((P a).eval (x a)*(x a+v g a))+
        α g*(S.eval (x a)*(x a+s g))=0 := by
    have eq : (B g (some a)).eval (x a)+(B g none).eval (x a)=0 := (shape g).2.2 a
    simpa only [shortShape,normalShape,eval_mul,eval_C,eval_sub,eval_X,sub_neg_eq_add] using eq
  have amp (g : Group m) (a : Color m) :
      A g a=-(α g*(S.eval (x a)*(x a+s g)))/((P a).eval (x a)*(x a+v g a)) := by
    apply (eq_div_iff (mul_ne_zero (coeffX a) (regXV a g))).mpr
    linear_combination mix g a
  have residue (g : Group m) (a : Color m) :
      f (.inr g) (some a)*R g=A g a*((P a).eval (-s g)*(v g a-s g)) := by
    have eq := numerator_at_root (fun k => -t (fullMark g k))
      (fun k => f (fullMark g k) (some a)) none
    have erase : (∏ j ∈ Finset.univ.erase (none : Option (Color m)),
      (-t (fullMark g none) - -t (fullMark g j)))=R g := by
      let emb : Color m ↪ Option (Color m) := ⟨some,fun _ _ h => Option.some.inj h⟩
      have sets : Finset.univ.erase (none : Option (Color m))=Finset.univ.map emb := by
        ext i
        cases i with
        | none => simp only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.mem_univ, and_true,
          Finset.mem_map, reduceCtorEq, and_false, exists_const, emb]
        | some a =>
          simp only [Finset.mem_erase,Finset.mem_univ,and_true,Finset.mem_map,true_and]
          exact ⟨fun _ => ⟨a,rfl⟩,fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩
      rw [sets,Finset.prod_map]
      rw [show R g = ∏ a, (v g a-s g) from rfl]
      apply Finset.prod_congr rfl
      intro a _
      have ea : emb a=some a := rfl
      rw [ea]
      simp only [fullMark,tS,tV,sub_neg_eq_add]
      ring
    change (B g (some a)).eval (-t (fullMark g none))=
      f (fullMark g none) (some a)*_ at eq
    rw [erase,normalShape] at eq
    simp only [fullMark,tS,eval_mul,eval_C,eval_sub,eval_X,sub_neg_eq_add] at eq
    linear_combination -eq
  have weight (a : Color m) (g : Group m) :
    f (.inr g) (some a)*E.eval (-s g)/(D a).eval (-s g) =
      (S.eval (x a)/(P a).eval (x a)/(2*x a))*(moments s v x a g*scaled g) := by
    have pneg : (P a).eval (-s g)≠0 := by
      apply nodePoly_ne_zero_at
      intro j
      rw [←tS,←tV]
      exact (nz _ _).symm
    have valD : (D a).eval (-s g) =
        -((P a).eval (-s g)*(x a-s g)*(x a+s g)) := by
      simp only [D,eval_mul,eval_sub,eval_C,eval_X]
      ring
    have elim := (eq_div_iff (coeffR g)).mpr (residue g a)
    rw [elim,amp,valD,moments]
    dsimp only [scaled]
    field_simp [coeffX,coeffR,xne,distinctXS,regXS,regXV,pneg,two_ne_zero]
  have parity_free (a : Color m) :
      S.eval (-x a)/(P a).eval (-x a) =
        (S.eval (x a)/(P a).eval (x a))*(∏ g, (1-moments s v x a g)) := by
    have id g := normalized_entry (x:=x a) (y:=v g a) (s:=s g) (distinctXS a g) (regXV a g)
    simp only [S,P,nodePoly_eval,←Finset.prod_div_distrib,←Finset.prod_mul_distrib,moments]
    apply Finset.prod_congr rfl
    intro g _
    rw [← id g]
    have negv : -x a-v g a≠0 := by
      rw [show -x a-v g a=-(x a+v g a) by ring]
      exact neg_ne_zero.mpr (regXV a g)
    have diffv : x a-v g a≠0 := by
      apply sub_ne_zero.mpr
      rw [←tX,←tV]
      exact differ (by simp only [smallMark, ne_eq, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, and_true,
        not_false_eq_true])
    field_simp [negv,diffv,distinctXS]
  have killed := test scaled β (fun a => by
    have eq := equations a
    simp_rw [weight] at eq
    rw [← Finset.mul_sum,parity_free] at eq
    let scale := S.eval (x a)/(P a).eval (x a)/(2*x a)
    have scale_ne : scale ≠ 0 := div_ne_zero (div_ne_zero (coeffS a) (coeffX a))
      (mul_ne_zero two_ne_zero (xne a))
    apply mul_left_cancel₀ scale_ne
    calc
      _ = β*((S.eval (x a)/(P a).eval (x a)-
          S.eval (x a)/(P a).eval (x a)*(∏ g,(1-moments s v x a g)))/(2*x a)) := eq
      _ = _ := by dsimp only [scale]; ring)
  have αzero (g : Group m) : α g=0 := by
    have eh : scaled g=0 := congrFun killed.1 g
    dsimp only [scaled] at eh
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp eh).resolve_right (coeffR g))).resolve_right (coeffE g)
  have allFull (g : Group m) (k c : Option (Color m)) : f (fullMark g k) c=0 := by
    have z : B g c=0 := by
      cases c with
      | none => rw [shortShape,αzero,C_0,zero_mul]
      | some a =>
        have a0 : A g a=0 := by rw [amp,αzero,zero_mul,neg_zero,zero_div]
        rw [normalShape,a0,C_0,zero_mul]
    exact congrFun (zero_residues _ (neg_injective.comp (distinct.comp (fullMark_injective g))) _ z) k
  have allSmall (a : Color m) (c : Option (Color m)) : f (smallMark a) c=0 := by
    have z₀ : U none=0 := by rw [smallShape,killed.2,C_0,zero_mul]
    have Uzero : U c=0 := by
      cases c with
      | none => exact z₀
      | some j =>
        let points : Option (Option (Group m))→ℂ :=
          fun i => i.elim (-x j) (fun k => k.elim (x j) (fun g => v g j))
        have neq (g : Group m) : x j ≠ v g j := by
          rw [←tX,←tV]
          exact differ (by simp only [smallMark, ne_eq, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq,
            and_true, not_false_eq_true])
        have opp (g : Group m) : v g j ≠ -x j := by
          rw [←tX,←tV]
          exact nz _ _
        have posneg : x j ≠ -x j := by rw [←tX]; exact nz _ _
        have inject : Function.Injective points := by
          intro i k eq
          rcases i with (_|i) <;> rcases k with (_|k) <;> try rfl
          · rcases k with (_|g)
            · exact (posneg eq.symm).elim
            · exact (opp g eq.symm).elim
          · rcases i with (_|g)
            · exact (posneg eq).elim
            · exact (opp g eq).elim
          · rcases i with (_|g) <;> rcases k with (_|l) <;> try rfl
            · exact (neq l eq).elim
            · exact (neq g eq.symm).elim
            · have h : v g j=v l j := eq
              rw [←tV,←tV] at h
              have e : (.inl (some g,j) : Mark m) = .inl (some l,j) := distinct h
              simpa only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq, and_true] using e
        have cap : (U (some j)).natDegree < Fintype.card (Option (Option (Group m))) := by
          have h := numerator_degree (fun a => -x a) (fun a => f (smallMark a) (some j))
          simp only [Group,Color,Fintype.card_option,Fintype.card_fin] at h ⊢
          change (U (some j)).natDegree ≤ m+2-1 at h
          omega
        have negative : (U (some j)).eval (-x j)=0 := by
          have z := diagonal (smallMark j)
          change f (smallMark j) (some j)+f (smallMark j) none=0 at z
          have h := congrArg (Polynomial.eval (-x j)) z₀
          have hroot := numerator_at_root (fun k => -x k)
            (fun k => f (smallMark k) none) j
          change (U none).eval (-x j) = _ at hroot
          rw [hroot,eval_zero] at h
          have f0 : f (smallMark j) none=0 :=
            (mul_eq_zero.mp h).resolve_right (Finset.prod_ne_zero_iff.mpr fun k hk =>
              sub_ne_zero.mpr (neg_injective.ne (fun e => Finset.ne_of_mem_erase hk
                (smallMark_injective (distinct (by simpa only [tX] using e.symm))))))
          rw [f0,add_zero] at z
          have eval := numerator_at_root (fun k => -x k)
            (fun k => f (smallMark k) (some j)) j
          change (U (some j)).eval (-x j) = _ at eval
          rwa [z,zero_mul] at eval
        have evalSmall (i : Mark m) (c : Option (Color m)) :
            (U c).eval (t i)=(nodePoly (fun a => -x a)).eval (t i)*
              (∑ a, f (smallMark a) c/(t i+x a)) := by
          simpa only [U,smallNumerator,sub_neg_eq_add] using
            numerator_eval (fun a => -x a) (fun a => f (smallMark a) c)
              (fun a => by rw [←tX]; exact nz _ _)
        have pole' (i : Mark m) : (∑ a,read (f (smallMark a)) i/(t i+x a))=0 := by
          have h := poleSmall i
          have gone (g : Group m) : read (f (.inr g)) i = 0 := by
            change read (f (fullMark g none)) i = 0
            rcases i with ⟨q,a⟩|q
            · cases q <;> simp only [read, allFull, add_zero]
            · exact allFull g none none
          simpa only [gone,zero_div,Finset.sum_const_zero,add_zero] using h
        apply zero_of_many_roots inject cap
        intro i
        rcases i with _ | (_|g)
        · exact negative
        · have z := pole' (smallMark j)
          change (∑ a, (f (smallMark a) (some j)+f (smallMark a) none)/(t (smallMark j)+x a))=0 at z
          simp only [add_div,Finset.sum_add_distrib] at z
          have e := congrArg₂ (· + ·) (evalSmall (smallMark j) (some j))
            (evalSmall (smallMark j) none)
          rw [←mul_add,z,mul_zero,z₀,eval_zero,add_zero] at e
          simpa only [points, Option.elim_some, Option.elim_none, tX] using e
        · have e := evalSmall (.inl (some g,j)) (some j)
          have z := pole' (.inl (some g,j))
          simp only [read] at z
          rw [z,mul_zero] at e
          simpa only [points, Option.elim_some, tV] using e
    have inj : Function.Injective (fun i => -x i) := neg_injective.comp
      (fun i j h => smallMark_injective (distinct (by simpa only [tX] using h)))
    exact congrFun (zero_residues _ inj _ Uzero) a
  funext i c
  rcases i with ⟨g,a⟩ | g
  · cases g with
    | none => exact allSmall a c
    | some g => exact allFull g (some a) c
  · exact allFull g none c

end SharpTensorEven
open Filter
open scoped Topology

namespace SharpTensorEven

private def selectRow {m : ℕ} (q : Option (Group m)) : Color m :=
  q.elim ⟨m,by omega⟩ (Fin.castLE (by omega))

private noncomputable def testMatrix {m : ℕ} (d : Color m→Group m→ℂ) :
    Matrix (Option (Group m)) (Option (Group m)) ℂ :=
  fun q c => c.elim (-(1-∏ g, (1-d (selectRow q) g))) (d (selectRow q))

private lemma testMatrix_apply {m : ℕ} (d : Color m→Group m→ℂ) (α : Group m→ℂ) (β : ℂ)
    (q : Option (Group m)) :
    (testMatrix d).mulVec (fun c => c.elim β α) q =
      (∑ g,d (selectRow q) g*α g)-(1-∏ g,(1-d (selectRow q) g))*β := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_option,testMatrix,Option.elim_none,Option.elim_some]
  ring

-- At the initial parameters the selected rows are unit vectors and one row with two ones. Preserve this minor while perturbing to distinct positive nodes.
private lemma good_nodes {m : ℕ} (hm : 2 ≤ m) :
    ∃ s : Group m→ℂ, ∃ v : Group m → Color m→ℂ, ∃ x : Color m→ℂ,
      Function.Injective (node s v x) ∧ (∀ j i,node s v x j+node s v x i≠0) ∧
      ∀ α : Group m→ℂ, ∀ β : ℂ,
        (∀ a, (∑ g,moments s v x a g*α g)=(1-∏ g,(1-moments s v x a g))*β) →
          α=0 ∧ β=0 := by
  classical
  let active (a : Color m) (g : Group m) : Prop :=
    (a.val < m ∧ a.val=g.val) ∨ (a.val=m ∧ (g.val=0 ∨ g.val=1))
  let center : Mark m→ℝ := fun i => match i with
    | .inr _ => 1
    | .inl (none,_) => 2
    | .inl (some g,a) => if active a g then 2 else 1
  let e := Fintype.equivFin (Mark m)
  let p (z : ℝ) (i : Mark m) : ℝ := center i+z*(e i).val
  have p0 (i : Mark m) : p 0 i=center i := by simp only [zero_mul, add_zero, p]
  have hcenter (i : Mark m) : 0<center i := by
    rcases i with ⟨q,a⟩|g
    · cases q <;> simp only [Nat.ofNat_pos, center]
      split <;> norm_num
    · norm_num [center]
  have pContinuous (i : Mark m) : Continuous fun z => p z i := by
    exact continuous_const.add (continuous_id.mul continuous_const)
  let s (z : ℝ) (g : Group m) : ℂ := p z (.inr g)
  let v (z : ℝ) (g : Group m) (a : Color m) : ℂ := p z (.inl (some g,a))
  let x (z : ℝ) (a : Color m) : ℂ := p z (smallMark a)
  let d (z : ℝ) := moments (s z) (v z) (x z)
  have cs (g : Group m) : s 0 g=1 := by simp only [p0, Complex.ofReal_one, s, center]
  have cx (a : Color m) : x 0 a=2 := by simp only [smallMark, p0, Complex.ofReal_ofNat, x, center]
  have cv (g : Group m) (a : Color m) : v 0 g a=if active a g then 2 else 1 := by
    simp only [p0, apply_ite, Complex.ofReal_ofNat, Complex.ofReal_one, ite_eq_left_iff,
      OfNat.one_ne_ofNat, imp_false, Decidable.not_not, ite_eq_right_iff, OfNat.ofNat_ne_one,
      ite_then_self, imp_self, v, center]
  have d0 (a : Color m) (g : Group m) : d 0 a g = if active a g then 1 else 0 := by
    simp only [d,moments,cs,cx,cv]
    split <;> norm_num
  have atUnit (g j : Fin m) : d 0 (selectRow (some g)) j = if g=j then 1 else 0 := by
    rw [d0]
    have a : ((selectRow (some g) : Color m)).val=g.val := rfl
    simp only [a, g.isLt, show (g.val = j.val) ↔ g = j from ⟨Fin.ext, fun h => congrArg Fin.val h⟩,
      true_and, show g.val ≠ m by omega, false_and, or_false, active]
  have atTwo (j : Group m) : d 0 (selectRow none) j = if j.val=0 ∨ j.val=1 then 1 else 0 := by
    rw [d0]
    have a : (selectRow (none : Option (Group m))).val=m := rfl
    simp only [a, lt_self_iff_false, false_and, true_and, false_or, active]
  have noKernel (k : Option (Group m)→ℂ) (zero : (testMatrix (d 0)).mulVec k=0) : k=0 := by
    let α (g : Group m) := k (some g)
    let β := k none
    have hk : (fun q : Option (Group m) => q.elim β α)=k := by
      funext q
      cases q <;> rfl
    have z (q : Option (Group m)) :
        (∑ g,d 0 (selectRow q) g*α g)=(1-∏ g,(1-d 0 (selectRow q) g))*β := by
      have eq := testMatrix_apply (d 0) α β q
      rw [hk,zero,Pi.zero_apply] at eq
      exact sub_eq_zero.mp eq.symm
    have test (a : Color m) :
        (∑ g,d 0 a g*α g)=(1-∏ g,(1-d 0 a g))*β := by
      by_cases b : a.val < m
      · have he : selectRow (some (⟨a.val,b⟩ : Group m))=a := Fin.ext rfl
        simpa only [he] using z (some ⟨a.val,b⟩)
      · by_cases c : a.val=m
        · have he : selectRow (none : Option (Group m))=a := Fin.ext c.symm
          simpa only [he] using z none
        · have row (g : Group m) : d 0 a g=0 := by simp only [d0, b, false_and, c, or_self, ↓reduceIte,
          active]
          simp only [row, zero_mul, Finset.sum_const_zero, sub_zero, Finset.prod_const_one, sub_self]
    obtain ⟨az,bz⟩ := rank_of_special_rows hm (d 0) α β test atUnit atTwo
    rw [←hk,az,bz]
    funext q
    cases q <;> rfl
  have det0 : (testMatrix (d 0)).det≠0 := by
    have inj : Function.Injective (testMatrix (d 0)).mulVec := by
      intro f g eq
      apply sub_eq_zero.mp
      apply noKernel
      rw [Matrix.mulVec_sub,eq,sub_self]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp inj)).ne_zero
  have contD (a : Color m) (g : Group m) : ContinuousAt (fun z => d z a g) 0 := by
    have hc (i : Mark m) : Continuous fun z => ((p z i : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (pContinuous i)
    have hS : ContinuousAt (fun z => s z g) 0 := (hc (.inr g)).continuousAt
    have hX : ContinuousAt (fun z => x z a) 0 := (hc (smallMark a)).continuousAt
    have hV : ContinuousAt (fun z => v z g a) 0 := (hc (.inl (some g,a))).continuousAt
    exact ((continuousAt_const.mul hX).mul (hV.sub hS)).div
      ((hX.add hV).mul (hX.sub hS)) (by
        simp only [cx,cs,cv]
        split <;> norm_num)
  have contMat : ContinuousAt (fun z => testMatrix (d z)) 0 := by
    apply continuousAt_pi.2
    intro q
    apply continuousAt_pi.2
    intro c
    cases c with
    | none =>
      change ContinuousAt (fun z => -(1-∏ g, (1-d z (selectRow q) g))) 0
      apply ContinuousAt.neg (ContinuousAt.sub continuousAt_const ?_)
      have product (S : Finset (Group m)) :
          ContinuousAt (fun z => ∏ g ∈ S, (1-d z (selectRow q) g)) 0 := by
        induction S using Finset.induction_on with
        | empty =>
          simpa only [Finset.prod_empty] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1:ℂ)) 0)
        | @insert g S hg prev =>
          simpa only [Finset.prod_insert hg,Pi.mul_def,Pi.sub_def] using
            (continuousAt_const.sub (contD (selectRow q) g)).mul prev
      exact product Finset.univ
    | some g => exact contD _ _
  have detCont : ContinuousAt (fun z => (testMatrix (d z)).det) 0 :=
    (continuous_id.matrix_det.continuousAt).comp contMat
  have survives := detCont.eventually_ne det0
  let l := 𝓝[Set.Ioi (0:ℝ)] 0
  have : l.NeBot := nhdsWithin_Ioi_neBot le_rfl
  have positiveZ : ∀ᶠ z in l, 0<z := self_mem_nhdsWithin
  have different : ∀ᶠ z in l, Function.Injective (p z) := by
    apply eventually_all.2
    intro i
    apply eventually_all.2
    intro j
    by_cases ij : i=j
    · exact Filter.Eventually.of_forall (fun _ _ => ij)
    by_cases base : center i=center j
    · filter_upwards [positiveZ] with z hz eq
      exfalso
      have slopes : ((e i).val : ℝ) ≠ (e j).val := fun h =>
        ij (e.injective (Fin.ext (by exact_mod_cast h)))
      apply slopes
      apply mul_left_cancel₀ (ne_of_gt hz)
      dsimp only [p] at eq
      rw [base] at eq
      exact add_left_cancel eq
    · have cc := ((pContinuous i).sub (pContinuous j)).continuousAt.eventually_ne
        (show p 0 i-p 0 j≠0 by rwa [p0,p0,sub_ne_zero])
      filter_upwards [cc.filter_mono nhdsWithin_le_nhds] with z ne eq
      exact (ne (sub_eq_zero.mpr eq)).elim
  obtain ⟨z,hz,hd,hdet⟩ := (positiveZ.and (different.and
    (survives.filter_mono nhdsWithin_le_nhds))).exists
  have equal (i : Mark m) : node (s z) (v z) (x z) i = p z i := by
    rcases i with ⟨q,a⟩|g
    · cases q <;> rfl
    · rfl
  have pp (i : Mark m) : 0<p z i :=
    (hcenter i).trans_le (le_add_of_nonneg_right (mul_nonneg hz.le (Nat.cast_nonneg _)))
  refine ⟨s z,v z,x z,?_,?_,?_⟩
  · intro i j h
    rw [equal,equal] at h
    exact hd (Complex.ofReal_injective h)
  · intro i j h
    rw [equal,equal,←Complex.ofReal_add] at h
    exact (ne_of_gt (add_pos (pp i) (pp j))) (Complex.ofReal_eq_zero.mp h)
  · intro α β eq
    have zero : (testMatrix (d z)).mulVec (fun q => q.elim β α)=0 := by
      funext q
      rw [testMatrix_apply,eq,sub_self,Pi.zero_apply]
    have inj := Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
    have killed := inj (zero.trans (Matrix.mulVec_zero _).symm)
    exact ⟨funext fun g => congrFun killed (some g), congrFun killed none⟩

end SharpTensorEven
namespace SharpTensorEven

private def selector {m : ℕ} (q : Option (Group m)) (i : Mark m) : ℂ :=
  match q, i with
  | none, .inl (none,_) => 1
  | none, .inl (some _,_) => 0
  | none, .inr _ => 1
  | some _, .inl (none,_) => 0
  | some q, .inl (some g,_) => if q=g then 1 else 0
  | some q, .inr g => if q=g then 1 else 0

private lemma selector_full {m : ℕ} (g : Group m) (f : Mark m→ℂ) :
    (∑ i,selector (some g) i*f i) = ∑ k, f (fullMark g k) := by
  classical
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_option,selector,fullMark,
    zero_mul,Finset.sum_const_zero,zero_add,ite_mul,one_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    add_comm]

private lemma selector_small {m : ℕ} (f : Mark m→ℂ) :
    (∑ i,selector none i*f i)=(∑ a,f (smallMark a))+(∑ g,f (.inr g)) := by
  simp only [selector, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_option, one_mul, zero_mul,
    Finset.sum_const_zero, add_zero, smallMark]

-- Reindex the block system for the merged conic tangent criterion.
private lemma local_witness (m : ℕ) (hm : 2 ≤ m) :
    let h := m+3
    let b := h*(h-2)-1
    let u := h-2
    ∃ x : Fin b → Fin 3 → ℂ, ∃ y : Fin b → Fin b → ℂ, ∃ z : Fin b → Fin (b-u) → ℂ,
      ∃ x' : Fin (b-h) → Fin 3 → ℂ, ∃ y' : Fin (b-h) → Fin b → ℂ,
      ∀ T : Fin 3 → Fin b → Fin (b-u) → ℂ,
        ∃ U : Fin b → Fin 3 → ℂ, ∃ V : Fin b → Fin b → ℂ,
        ∃ W : Fin b → Fin (b-u) → ℂ, ∃ W' : Fin (b-h) → Fin (b-u) → ℂ, ∀ i j k,
          T i j k=(∑ t, (U t i*(y t j*z t k)+x t i*(V t j*z t k)+x t i*(y t j*W t k))) +
            ∑ t, x' t i*(y' t j*W' t k) := by
  classical
  intro h b u
  have cb : Fintype.card (Mark m) = b := by
    have bp : h-2=m+1 := by dsimp [h]; omega
    simp only [b,bp,h,Mark,Fintype.card_sum,Fintype.card_prod,Fintype.card_option,Fintype.card_fin]
    rw [show (m+3)*(m+1)=(m+1)*(m+2)+m+1 by ring]
    omega
  let e : Fin b ≃ Mark m := Fintype.equivOfCardEq (by simp only [Fintype.card_fin, cb])
  let ec : Fin h ≃ Option (Color m) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_option, h])
  let eq : Fin u ≃ Option (Group m) := Fintype.equivOfCardEq (by
    simp only [Nat.reduceSubDiff, Fintype.card_fin, Fintype.card_option, u, h])
  obtain ⟨s,v,x,distinct,regular,test⟩ := good_nodes hm
  let t := node s v x
  let M : Matrix (Fin b) (Fin h) ℂ := fun i c => read (Pi.single (ec c) 1) (e i)
  let Q : Matrix (Fin u) (Fin b) ℂ := fun q i => selector (eq q) (e i)
  have read_vec (f : Fin h→ℂ) (i : Fin b) :
      M.mulVec f i = read (f∘ec.symm) (e i) := by
    change (∑ c, read (Pi.single (ec c) 1) (e i)*f c)=_
    rw [←ec.symm.sum_comp (fun c => read (Pi.single (ec c) 1) (e i)*f c)]
    simp only [Equiv.apply_symm_apply]
    rcases e i with ⟨q,a⟩|g
    · cases q <;> simp only [read, Pi.single_apply, add_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Function.comp_apply]
    · simp only [read, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, Function.comp_apply]
  have inject : Function.Injective M.mulVec := by
    intro a c he
    apply eq_of_sub_eq_zero
    have hv (i : Fin b) : M.mulVec (a-c) i=0 := by
      rw [Matrix.mulVec_sub,he,sub_self,Pi.zero_apply]
    funext j
    obtain ⟨j',rfl⟩ := ec.symm.surjective j
    let g : Group m := ⟨0,by omega⟩
    cases j' with
    | none =>
      have er := hv (e.symm (.inr g))
      rw [read_vec,Equiv.apply_symm_apply] at er
      exact er
    | some k =>
      have er := hv (e.symm (.inl (some g,k)))
      rw [read_vec,Equiv.apply_symm_apply] at er
      exact er
  apply CriticalConic.local_component (t ∘ e) (distinct.comp e.injective)
    (fun i j => regular (e i) (e j)) M inject Q
  intro f diag mass pole
  let F (i : Mark m) (c : Option (Color m)) := f (e.symm i) (ec.symm c)
  have diagonal (i : Mark m) : read (F i) i=0 := by
    have h := diag (e.symm i)
    rwa [read_vec,Equiv.apply_symm_apply] at h
  have mass_all (q : Option (Group m)) (c : Option (Color m)) :
      (∑ i,selector q i*F i c)=0 := by
    have h := mass (eq.symm q) (ec.symm c)
    convert h using 1
    change (∑ i,selector q i*F i c)=
      ∑ i,selector (eq (eq.symm q)) (e i)*f i (ec.symm c)
    rw [←e.symm.sum_comp (fun i => selector (eq (eq.symm q)) (e i)*f i (ec.symm c))]
    simp only [Fintype.sum_sum_type, Equiv.apply_symm_apply, F]
  have poles_all (q : Option (Group m)) (j : Mark m) :
      (∑ i,selector q i*(read (F i) j/(t j+t i)))=0 := by
    have h := pole (eq.symm q) (e.symm j)
    simp only [read_vec,Function.comp_apply,Equiv.apply_symm_apply,Q,add_comm (t (e _)) (t j)] at h
    convert h using 1
    rw [←e.symm.sum_comp (fun i => selector q (e i)*
      (read (f i ∘ ec.symm) j/(t j+t (e i))))]
    simp only [Fintype.sum_sum_type, Equiv.apply_symm_apply, Function.comp_def, F]
  have all := block_kernel s v x test t rfl distinct regular F diagonal
    (fun g c => by simpa only [selector_full] using mass_all (some g) c)
    (fun g j => by simpa only [selector_full] using poles_all (some g) j)
    (fun c => by simpa only [selector_small] using mass_all none c)
    (fun j => by
      have h := poles_all none j
      rw [selector_small] at h
      simpa only [smallMark, node, Sum.elim_inl, Option.elim_none, Sum.elim_inr, t] using h)
  funext i c
  have z := congrFun (congrFun all (e i)) (ec c)
  simpa only [F, Pi.zero_apply, Equiv.symm_apply_apply] using z

end SharpTensorEven

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2.H2 := by
  intro h hh _
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, h=m+3 := ⟨h-3,by omega⟩
  exact CriticalConic.boundary_rank_of_local (m+3) (by omega)
    (SharpTensorEven.local_witness m (by omega))
