import OMAStatements.S_mo_429774

/-!
Complete proof by @connoranderson, linked from statement PR #25113 and desk DONE #115661.
Pinned source: https://github.com/connoranderson/open-math-agents/blob/ec4e4914aa2b2a625d938fdb10bd51eb4bda3a48/proofs/mo-429774.lean
All mathematical source unchanged; this port adds provenance and current-checker validation.
Source: KhashF, https://mathoverflow.net/questions/429774 (CC BY-SA 4.0).
The law is uniform over all transposition words of length at most k, including the empty word.
Port and validation: @rodolfoquint. No new mathematical discovery is claimed.
-/

namespace OMA.S_mo_429774
open Finset Equiv

lemma total_pos (n k : ℕ) : 0 < total n k := by
  have h := single_le_sum (s:=range (k+1)) (f:=fun t => (countEdges n)^t)
    (fun i _ => Nat.zero_le _) (show 0 ∈ range (k+1) by simp)
  change 1 ≤ _
  simpa [total] using h

lemma sum_paths (n t : ℕ) : ∑ g, paths n t g = (countEdges n)^t := by
  classical
  simpa [paths,countEdges] using sum_card_fiberwise_eq_card_filter
    (univ : Finset (Fin t → Edge n)) (univ : Finset (G n)) endpoint

lemma mass_nonneg (n k : ℕ) (g : G n) : 0 ≤ mass n k g := by unfold mass; positivity

lemma sum_mass (n k : ℕ) : ∑ g, mass n k g = 1 := by
  simp only [mass,←sum_div]
  rw [sum_comm]
  have hh (t : ℕ) : ∑ g, (paths n t g:ℝ) = ((countEdges n)^t:ℕ) := by exact_mod_cast sum_paths n t
  simp_rw [hh]
  rw [← Nat.cast_sum]
  exact div_self (by exact_mod_cast (total_pos n k).ne')

lemma sum_uniform (n : ℕ) : (∑ _g : G n, (Fintype.card (G n):ℝ)⁻¹)=1 := by
  simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

lemma test_le_tv (n k : ℕ) (S : Finset (G n)) :
    (∑ g ∈ S, mass n k g) - (∑ _g ∈ S, (Fintype.card (G n):ℝ)⁻¹) ≤ tv n k := by
  classical
  let d (g : G n) := mass n k g - (Fintype.card (G n):ℝ)⁻¹
  have zeroSum : ∑ g, d g = 0 := by simp [d,sum_sub_distrib,sum_mass]
  have splitD := Finset.sum_add_sum_compl S d
  have splitA := Finset.sum_add_sum_compl S (fun g => |d g|)
  have hp : ∑ g ∈ S, d g ≤ ∑ g ∈ S, |d g| :=
    Finset.sum_le_sum (fun g _ => le_abs_self _)
  have hn : -(∑ g ∈ Sᶜ, d g) ≤ ∑ g ∈ Sᶜ, |d g| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun g _ => neg_le_abs _)
  rw [←sum_sub_distrib]
  change ∑ g ∈ S, d g ≤ (∑ g, |d g|)/2
  linarith

lemma tv_le_one (n k : ℕ) : tv n k ≤ 1 := by
  have h : ∑ g : G n, |mass n k g - (Fintype.card (G n):ℝ)⁻¹| ≤
      ∑ g : G n, (mass n k g + (Fintype.card (G n):ℝ)⁻¹) := by
    apply sum_le_sum
    intro g _
    grw [abs_sub]
    simp [abs_of_nonneg (mass_nonneg n k g)]
  rw [sum_add_distrib,sum_mass,sum_uniform] at h
  unfold tv
  linarith

end OMA.S_mo_429774

namespace OMA.S_mo_429774
open Finset Equiv

private def firstEdge {n : ℕ} (hn : 2 ≤ n) : Edge n :=
  ⟨(⟨0,by omega⟩,⟨1,by omega⟩), by change (0:ℕ)<1; decide⟩

lemma edges_pos {n : ℕ} (hn : 2≤n) : 0 < countEdges n := Fintype.card_pos_iff.mpr ⟨firstEdge hn⟩

lemma edges_gt_one {n : ℕ} (hn : 3≤n) : 1 < countEdges n := by
  let a := firstEdge (show 2≤n by omega)
  let b : Edge n := ⟨(⟨0,by omega⟩,⟨2,by omega⟩),by change (0:ℕ)<2; decide⟩
  change 1 < (univ : Finset (Edge n)).card
  exact one_lt_card_iff.mpr ⟨a,b,mem_univ _,mem_univ _,fun h => by
    have := congrArg (fun e : Edge n => e.val.2.val) h
    change 1=2 at this
    omega⟩

noncomputable def chi {n : ℕ} (g : G n) : ℝ := ((Perm.sign g:ℤ):ℝ)

lemma chi_cases {n : ℕ} (g : G n) : chi g=1 ∨ chi g= -1 := by
  rcases Int.units_eq_one_or (Perm.sign g) with h|h <;> simp [chi,h]

lemma chi_abs {n : ℕ} (g : G n) : |chi g|=1 := by
  rcases chi_cases g with h|h <;> simp [h]

lemma chi_sum {n : ℕ} (hn : 2≤n) : (∑ g : G n, chi g)=0 := by
  let a := firstEdge hn
  have h (g : G n) : chi (step a * g) = -chi g := by
    simp [chi,step,Perm.sign_swap a.property.ne]
  have hh := Equiv.sum_comp (Equiv.mulLeft (step a)) (fun g => chi g)
  simp only [Equiv.coe_mulLeft,h,Finset.sum_neg_distrib] at hh
  linarith

lemma endpoint_sign {n t : ℕ} (w : Fin t → Edge n) :
    (Perm.sign (endpoint w) : ℤ) = (-1:ℤ)^t := by
  let l := List.ofFn (fun i => step (w i))
  have h := Perm.sign_prod_list_swap (l := l) (by
    intro f hf
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    exact ⟨(w i).val.1,(w i).val.2,(w i).property.ne,rfl⟩)
  simpa [endpoint,l] using congrArg (fun z : ℤˣ => (z:ℤ)) h

lemma paths_zero {n t : ℕ} {g : G n} (h : (Perm.sign g : ℤ) ≠ (-1:ℤ)^t) : paths n t g = 0 := by
  classical
  unfold paths
  rw [card_eq_zero,filter_eq_empty_iff]
  intro w _ hw
  exact h (hw ▸ endpoint_sign w)

lemma sign_indicator {n : ℕ} (g : G n) (t : ℕ) :
    2 * (if (Perm.sign g : ℤ) = (-1:ℤ)^t then (1:ℝ) else 0) =
      1+chi g*(-1:ℝ)^t := by
  rcases Int.units_eq_one_or (Perm.sign g) with hg|hg <;>
    rcases neg_one_pow_eq_or ℤ t with ht|ht <;>
    have hr := congrArg (fun z : ℤ => (z:ℝ)) ht <;>
    push_cast at hr <;> norm_num [hg,ht,chi,hr]

lemma sign_class {n : ℕ} (hn : 2≤n) (t : ℕ) :
    2 * ((univ.filter (fun g : G n => (Perm.sign g : ℤ) = (-1:ℤ)^t)).card : ℝ) =
      (Fintype.card (G n):ℝ) := by
  have h := congrArg (fun f : G n → ℝ => ∑ g, f g) (funext (fun g : G n => sign_indicator g t))
  simpa only [←mul_sum, sum_boole,sum_add_distrib, ←sum_mul,chi_sum hn,zero_mul,add_zero,
    sum_const,card_univ,nsmul_eq_mul,mul_one] using h

end OMA.S_mo_429774

namespace OMA.S_mo_429774
open Finset Equiv

noncomputable def bias (n k : ℕ) : ℝ :=
  (∑ t ∈ range (k+1), (-(countEdges n:ℝ))^t)/(total n k:ℝ)

lemma gap_eq (n k : ℕ) : parityGap n k = |bias n k|/2 := by
  have h : 0 ≤ (total n k : ℝ) := by positivity
  rw [parityGap,bias,abs_div,abs_of_nonneg h,div_div,mul_comm]

private lemma signed_paths (n t : ℕ) : (∑ g : G n, chi g * (paths n t g:ℝ)) =
    (-(countEdges n:ℝ))^t := by
  have term (g : G n) : chi g * (paths n t g:ℝ) = (-1:ℝ)^t * (paths n t g:ℝ) := by
    by_cases h : (Perm.sign g : ℤ) = (-1:ℤ)^t
    · have h' : chi g = (-1:ℝ)^t := by unfold chi; exact_mod_cast h
      rw [h']
    · simp [paths_zero h]
  simp_rw [term]
  rw [←mul_sum, ←Nat.cast_sum, sum_paths, Nat.cast_pow, ←mul_pow, neg_one_mul]

lemma signed_residual {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (∑ g : G n, chi g * (mass n k g - (Fintype.card (G n):ℝ)⁻¹)) = bias n k := by
  simp_rw [mul_sub]
  rw [sum_sub_distrib,←sum_mul,chi_sum hn,zero_mul,sub_zero]
  unfold mass bias
  simp_rw [←mul_div_assoc,mul_sum]
  rw [←sum_div,sum_comm]
  simp_rw [signed_paths]

lemma gap_le_tv {n : ℕ} (hn : 2≤n) (k : ℕ) : parityGap n k ≤ tv n k := by
  rw [gap_eq,←signed_residual hn k,tv]
  gcongr
  calc |∑ g : G n, chi g * (mass n k g - (Fintype.card (G n):ℝ)⁻¹)| ≤
      ∑ g : G n, |chi g * (mass n k g - (Fintype.card (G n):ℝ)⁻¹)| := abs_sum_le_sum_abs _ _
    _ = _ := by simp [abs_mul,chi_abs]

lemma tv_one (k : ℕ) : tv 1 k = 0 := by
  have h := sum_mass 1 k
  have hall : (univ : Finset (G 1)) = {1} := by decide +kernel
  simp only [hall,sum_singleton] at h
  simp [tv,h]

lemma tv_two (k : ℕ) : tv 2 k = parityGap 2 k := by
  classical
  let a : G 2 := 1
  let b : G 2 := Equiv.swap 0 1
  have hab : a≠b := by decide
  have hall : (univ : Finset (G 2)) = {a,b} := by decide +kernel
  have ha : chi a = 1 := by simp [chi,a]
  have hb : chi b = -1 := by simp [chi,b,Perm.sign_swap (by decide : (0:Fin 2)≠1)]
  have hcard : Fintype.card (G 2) = 2 := by decide +kernel
  let x := mass 2 k a - (Fintype.card (G 2):ℝ)⁻¹
  let y := mass 2 k b - (Fintype.card (G 2):ℝ)⁻¹
  have hm := sum_mass 2 k
  rw [hall,sum_pair hab] at hm
  have hxy : y = -x := by dsimp [x,y]; rw [hcard]; push_cast; linarith
  have hs := signed_residual (n:=2) (by decide) k
  rw [hall,sum_pair hab,ha,hb] at hs
  change 1*x + -1*y = _ at hs
  rw [hxy] at hs
  have hbias : bias 2 k = 2*x := by linarith
  rw [tv,gap_eq,hall,sum_pair hab,hbias]
  change (|x|+|y|)/2=|2*x|/2
  rw [hxy,abs_neg,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  ring

end OMA.S_mo_429774

namespace OMA.S_mo_429774
open Finset

private lemma total_geom (n k : ℕ) :
    (total n k : ℝ) * ((countEdges n:ℝ)-1) = (countEdges n:ℝ)^(k+1)-1 := by
  simpa [total] using geom_sum_mul (countEdges n:ℝ) (k+1)

private lemma alt_geom (n k : ℕ) :
    (∑ t ∈ range (k+1), (-(countEdges n:ℝ))^t) * ((countEdges n:ℝ)+1) =
    1-(-(countEdges n:ℝ))^(k+1) := by
  simpa [sub_neg_eq_add, add_comm] using geom_sum_mul_neg (-(countEdges n:ℝ)) (k+1)

lemma parityGap_odd {n : ℕ} (hn : 2≤n) (j : ℕ) :
    parityGap n (2*j+1) = minimumGap n := by
  let m : ℝ := countEdges n
  have hm : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast (show 1 ≤ countEdges n from edges_pos hn)
  have hpos : 0 < (total n (2*j+1) : ℝ) := by exact_mod_cast total_pos n _
  have hA := alt_geom n (2*j+1)
  have hT := total_geom n (2*j+1)
  change (∑ t ∈ range (2*j+1+1), (-m)^t) * (m+1) = 1-(-m)^(2*j+1+1) at hA
  have he : (-m)^(2*j+1+1) = m^(2*j+1+1) := by
    rw [show 2*j+1+1 = 2*(j+1) by omega, pow_mul, neg_sq, ← pow_mul]
  rw [he] at hA
  have hnon : (∑ t ∈ range (2*j+1+1), (-m)^t) ≤ 0 := by
    have hpow : 1 ≤ m^(2*j+1+1) := one_le_pow₀ hm
    by_contra! hx
    have := mul_pos hx (by linarith : 0 < m+1)
    linarith
  change |∑ t ∈ range (2*j+1+1), (-m)^t| / (2*_) = (m-1)/(2*(m+1))
  rw [abs_of_nonpos hnon, div_eq_div_iff (by positivity) (by positivity)]
  change (total n (2*j+1):ℝ)*(m-1) = m^(2*j+1+1)-1 at hT
  nlinarith

lemma parityGap_even {n : ℕ} (hn : 2≤n) (j : ℕ) :
    minimumGap n < parityGap n (2*j) := by
  let m : ℝ := countEdges n
  have hm : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast (show 1 ≤ countEdges n from edges_pos hn)
  have hpos : 0 < (total n (2*j):ℝ) := by exact_mod_cast total_pos n _
  have hA := alt_geom n (2*j)
  have hT := total_geom n (2*j)
  change (∑ t ∈ range (2*j+1), (-m)^t) * (m+1) = 1-(-m)^(2*j+1) at hA
  rw [pow_succ, pow_mul, neg_sq, ← pow_mul, mul_neg, sub_neg_eq_add, ← pow_succ] at hA
  have hnon : 0 ≤ ∑ t ∈ range (2*j+1), (-m)^t := by
    have hpow : 0 ≤ m^(2*j+1) := by positivity
    by_contra! hx
    have := mul_neg_of_neg_of_pos hx (by linarith : 0 < m+1)
    linarith
  change (m-1)/(2*(m+1)) < |∑ t ∈ range (2*j+1), (-m)^t| / (2*_)
  rw [abs_of_nonneg hnon, div_lt_div_iff₀ (by positivity) (by positivity)]
  change (total n (2*j):ℝ)*(m-1) = m^(2*j+1)-1 at hT
  nlinarith

lemma minimumGap_le {n : ℕ} (hn : 2≤n) (k : ℕ) : minimumGap n ≤ parityGap n k := by
  rcases Nat.even_or_odd k with ⟨j,h⟩ | ⟨j,h⟩
  · rw [show k = 2*j by omega]
    exact (parityGap_even hn j).le
  · rw [show k = 2*j+1 by omega, parityGap_odd hn]

end OMA.S_mo_429774

namespace OMA.S_mo_429774

private lemma edge_word {n : ℕ} (g : G n) : ∃ l : List (Edge n), (l.map step).prod = g := by
  classical
  induction g using Equiv.Perm.swap_induction_on with
  | one => exact ⟨[],rfl⟩
  | swap_mul g x y h ih =>
    obtain ⟨l,hl⟩ := ih
    rcases lt_or_gt_of_ne h with hxy | hyx
    · exact ⟨⟨(x,y),hxy⟩::l,by simp [step,hl]⟩
    · exact ⟨⟨(y,x),hyx⟩::l,by simpa [step,hl] using congrArg (· * g) (Equiv.swap_comm y x)⟩

private lemma even_word {n : ℕ} (l : List (Edge n)) (h : Equiv.Perm.sign (l.map step).prod = 1) :
    Even l.length := by
  have hs := Equiv.Perm.sign_prod_list_swap (l := l.map step) (by
    intro f hf
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hf
    exact ⟨e.val.1,e.val.2,e.property.ne,rfl⟩)
  rw [h,List.length_map] at hs
  have hh := congrArg (fun z : ℤˣ => (z:ℤ)) hs.symm
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1:ℤ) ≠ 1)).mp (by simpa using hh)

lemma positive_block {n : ℕ} (hn : 2 ≤ n) : ∃ L : ℕ, 0 < L ∧ Even L ∧
    ∀ g : G n, Equiv.Perm.sign g = 1 → 0 < paths n L g := by
  classical
  choose word hword using fun g : G n => edge_word g
  let K := 1 + Finset.univ.sup (fun g : G n => (word g).length)
  refine ⟨2*K,by dsimp [K]; omega, ⟨K,by omega⟩, ?_⟩
  intro g hsign
  obtain ⟨j,hj⟩ := even_word (word g) (by rw [hword,hsign])
  have hlen : (word g).length ≤ K := by
    have := Finset.le_sup (s := Finset.univ) (f := fun h : G n => (word h).length) (Finset.mem_univ g)
    dsimp [K]; omega
  let e : Edge n := ⟨(⟨0,by omega⟩,⟨1,by omega⟩), by change (0:ℕ)<1; decide⟩
  let p := word g ++ List.replicate (2*(K-j)) e
  have hp : p.length = 2*K := by simp only [p,List.length_append,List.length_replicate]; omega
  have hsq : step e ^ 2 = 1 := by simp [step, sq]
  have hpe : (p.map step).prod = g := by simp [p, List.prod_replicate, pow_mul, hsq, hword]
  rw [paths, Finset.card_pos]
  have hh : ∃ w : Fin p.length → Edge n, endpoint w = g := by
    refine ⟨p.get, ?_⟩
    simpa only [endpoint, ← Function.comp_def, ← List.map_ofFn, List.ofFn_get] using hpe
  rw [hp] at hh
  obtain ⟨w,hw⟩ := hh
  exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩⟩

end OMA.S_mo_429774

namespace OMA.S_mo_429774

open Finset

private def wordJoin (n s t : ℕ) :
    ((Fin s → Edge n) × (Fin t → Edge n)) ≃ (Fin (s+t) → Edge n) where
  toFun w := Fin.append w.1 w.2
  invFun w := (fun i => w (Fin.castAdd t i), fun j => w (Fin.natAdd s j))
  left_inv w := by simp
  right_inv w := Fin.append_castAdd_natAdd

lemma endpoint_append {n s t : ℕ} (u : Fin s → Edge n) (v : Fin t → Edge n) :
    endpoint (Fin.append u v) = endpoint u * endpoint v := by
  simp [endpoint, List.ofFn_add, Fin.append_left', Fin.append_right]

lemma paths_add (n s t : ℕ) (g : G n) :
    paths n (s+t) g = ∑ h : G n, paths n s h * paths n t (h⁻¹*g) := by
  classical
  have hsum (l : ℕ) (a : G n) : paths n l a =
      ∑ w : Fin l → Edge n, if endpoint w = a then 1 else 0 := by
    simp [paths, Finset.sum_boole]
  rw [hsum, ← (wordJoin n s t).sum_comp]
  simp only [wordJoin, Equiv.coe_fn_mk, endpoint_append, Fintype.sum_prod_type]
  calc (∑ u : Fin s → Edge n, ∑ v : Fin t → Edge n,
      if endpoint u * endpoint v = g then 1 else 0) =
      ∑ u : Fin s → Edge n, paths n t ((endpoint u)⁻¹ * g) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hsum]
        simp only [eq_inv_mul_iff_mul_eq]
    _ = ∑ h : G n, paths n s h * paths n t (h⁻¹*g) := by
        simp_rw [hsum s, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp

lemma paths_add_right (n s t : ℕ) (g : G n) :
    paths n (s+t) g = ∑ h : G n, paths n s (g*h⁻¹) * paths n t h := by
  classical
  rw [paths_add]
  let e : G n ≃ G n :=
    { toFun := fun h => h⁻¹*g
      invFun := fun h => g*h⁻¹
      left_inv := by intro h; simp
      right_inv := by intro h; simp }
  apply Fintype.sum_equiv e
  intro h
  simp [e]

end OMA.S_mo_429774

namespace OMA.S_mo_429774
open Finset Filter
open scoped Topology

private noncomputable def walkP (n t : ℕ) (g : G n) : ℝ :=
  (paths n t g : ℝ)/(countEdges n:ℝ)^t

private noncomputable def walkU (n t : ℕ) (g : G n) : ℝ :=
  if (Equiv.Perm.sign g : ℤ) = (-1:ℤ)^t then 2/(Fintype.card (G n):ℝ) else 0

private lemma walkP_nonneg (n t : ℕ) (g : G n) : 0 ≤ walkP n t g := by
  unfold walkP
  positivity

private lemma walkU_nonneg (n t : ℕ) (g : G n) : 0 ≤ walkU n t g := by
  unfold walkU
  split_ifs <;> positivity

private lemma walkP_sum {n : ℕ} (hn : 2≤n) (t : ℕ) : ∑ g, walkP n t g = 1 := by
  have h : (∑ g, (paths n t g : ℝ)) = (countEdges n:ℝ)^t := by exact_mod_cast sum_paths n t
  simp only [walkP, ← sum_div, h]
  exact div_self (pow_ne_zero _ (Nat.cast_ne_zero.mpr (edges_pos hn).ne'))

private lemma walkU_sum {n : ℕ} (hn : 2≤n) (t : ℕ) : ∑ g, walkU n t g = 1 := by
  classical
  have h := sign_class hn t
  simp only [walkU, ← sum_filter, sum_const, nsmul_eq_mul, ← mul_div_assoc]
  rw [mul_comm _ 2, h, div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

private lemma walkP_add {n : ℕ} (s t : ℕ) (g : G n) : walkP n (s+t) g =
    ∑ h, walkP n s h * walkP n t (h⁻¹*g) := by
  simp only [walkP,paths_add,Nat.cast_sum,Nat.cast_mul,pow_add,div_mul_div_comm,sum_div]

private lemma walk_even_iff {n : ℕ} (h g : G n) :
    ((Equiv.Perm.sign (h⁻¹*g) : ℤ) = 1) ↔ ((Equiv.Perm.sign h : ℤ) = Equiv.Perm.sign g) := by
  change (↑(Equiv.Perm.sign (h⁻¹*g)) : ℤ) = (↑(1 : ℤˣ) : ℤ) ↔ _
  simp only [Units.val_inj,map_mul,map_inv,inv_mul_eq_one]

private lemma walk_translate {n : ℕ} (f : G n → ℝ) (g : G n) :
    ∑ h : G n, f (h⁻¹*g) = ∑ h : G n, f h :=
  ((Equiv.inv _).trans (Equiv.mulRight g)).sum_comp f

private lemma walkP_zero {n t : ℕ} {g : G n}
    (h : (Equiv.Perm.sign g : ℤ) ≠ (-1:ℤ)^t) : walkP n t g = 0 := by
  simp [walkP,paths_zero h]

private lemma walkU_translate {n : ℕ} (hn : 2 ≤ n) {L : ℕ} (hL : Even L)
    (t : ℕ) (g : G n) : ∑ h, walkU n t h * walkP n L (h⁻¹*g) = walkU n t g := by
  calc (∑ h, walkU n t h * walkP n L (h⁻¹*g)) = ∑ h, walkU n t g * walkP n L (h⁻¹*g) := by
         apply sum_congr rfl
         intro h _
         by_cases hh : (Equiv.Perm.sign h : ℤ) = Equiv.Perm.sign g
         · simp only [walkU,hh]
         · have hz := mt (walk_even_iff h g).mp hh
           rw [walkP_zero (by simpa only [hL.neg_one_pow] using hz)]
           simp
    _ = _ := by rw [←mul_sum, walk_translate,walkP_sum hn,mul_one]

private lemma walkU_erase {n : ℕ} (hn : 2 ≤ n) {L : ℕ} (hL : Even L)
    (t : ℕ) (g : G n) :
    ∑ h, (walkP n t h-walkU n t h) * walkU n L (h⁻¹*g) = 0 := by
  let c := if (Equiv.Perm.sign g : ℤ)=(-1:ℤ)^t then 2/(Fintype.card (G n):ℝ) else 0
  calc (∑ h, (walkP n t h-walkU n t h) * walkU n L (h⁻¹*g)) =
      ∑ h, (walkP n t h-walkU n t h) * c := by
        apply sum_congr rfl
        intro h _
        by_cases hh : (Equiv.Perm.sign h : ℤ)=(-1:ℤ)^t
        · simp only [walkU, hL.neg_one_pow, walk_even_iff, hh, c, eq_comm (a:=(-1:ℤ)^t)]
        · simp [walkP_zero hh, walkU,hh]
    _ = 0 := by rw [← sum_mul, sum_sub_distrib, walkP_sum hn,walkU_sum hn,sub_self,zero_mul]

lemma walk_mixing {n : ℕ} (hn : 2≤n) (g : G n) : Tendsto
    (fun t => (paths n t g:ℝ)/(countEdges n:ℝ)^t -
      (if (Equiv.Perm.sign g : ℤ) = (-1:ℤ)^t then 2/(Fintype.card (G n):ℝ) else 0))
      atTop (𝓝 0) := by
  classical
  obtain ⟨L,hL,heL,hpos⟩ := positive_block hn
  let δ := ((countEdges n:ℝ)^L)⁻¹
  have hedge : 0 < (countEdges n:ℝ) := by exact_mod_cast edges_pos hn
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let R (h : G n) := walkP n L h - δ * walkU n L h
  have hR (h : G n) : 0 ≤ R h := by
    have hu : walkU n L h ≤ 1 := by
      rw [← walkU_sum hn L]
      exact single_le_sum (fun i _ => walkU_nonneg n L i) (mem_univ h)
    by_cases hs : Equiv.Perm.sign h = 1
    · have hw : δ ≤ walkP n L h := by
        rw [walkP,show δ = 1/(countEdges n:ℝ)^L by simp [δ]]
        apply div_le_div_of_nonneg_right _ (pow_nonneg hedge.le L)
        exact_mod_cast hpos h hs
      exact sub_nonneg.mpr ((mul_le_of_le_one_right hδ.le hu).trans hw)
    · simp [R,walkU,heL.neg_one_pow,hs,walkP_nonneg]
  have hsumR : ∑ h, R h = 1-δ := by simp [R,sum_sub_distrib,←mul_sum,walkP_sum hn,walkU_sum hn]
  have hcon : 0 ≤ 1-δ := hsumR ▸ sum_nonneg fun h _ => hR h
  let D (t : ℕ) (h : G n) := walkP n t h - walkU n t h
  have hstep (t : ℕ) (k : G n) : D (t+L) k = ∑ h, D t h * R (h⁻¹*k) := by
    have hu : walkU n (t+L) k = walkU n t k := by simp [walkU,pow_add,heL.neg_one_pow]
    have hzero := walkU_erase hn heL t k
    calc D (t+L) k = ∑ h, D t h * walkP n L (h⁻¹*k) := by
           dsimp [D]
           rw [walkP_add,hu,← walkU_translate hn heL t k]
           simp only [sub_mul,sum_sub_distrib]
      _ = _ := by
        dsimp only [R]
        simp only [mul_sub, sum_sub_distrib]
        have hzero' : ∑ h, D t h * (δ * walkU n L (h⁻¹*k)) = 0 := by
          simp only [mul_left_comm (D t _) δ, ←mul_sum, D, hzero, mul_zero]
        rw [hzero',sub_zero]
  have bound (j r : ℕ) (k : G n) : |D (r+j*L) k| ≤ (1-δ)^j := by
    induction j generalizing k with
    | zero =>
      simp only [zero_mul,add_zero,pow_zero,D]
      have hp := single_le_sum (s:=univ) (f:=walkP n r) (fun i _ => walkP_nonneg n r i) (mem_univ k)
      have hu := single_le_sum (s:=univ) (f:=walkU n r) (fun i _ => walkU_nonneg n r i) (mem_univ k)
      rw [walkP_sum hn] at hp
      rw [walkU_sum hn] at hu
      exact abs_le.mpr ⟨by linarith [walkP_nonneg n r k],by linarith [walkU_nonneg n r k]⟩
    | succ j ih =>
      rw [Nat.succ_mul,←add_assoc,hstep,pow_succ]
      calc |∑ h, D (r+j*L) h * R (h⁻¹*k)| ≤ ∑ h, |D (r+j*L) h * R (h⁻¹*k)| :=
             abs_sum_le_sum_abs _ _
        _ ≤ ∑ h, (1-δ)^j * R (h⁻¹*k) := by
          apply sum_le_sum
          intro h _
          rw [abs_mul,abs_of_nonneg (hR _)]
          exact mul_le_mul_of_nonneg_right (ih h) (hR _)
        _ = _ := by rw [←mul_sum,walk_translate,hsumR]
  have hdiv : Tendsto (fun t : ℕ => t/L) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b*L)] with t ht
    exact (Nat.le_div_iff_mul_le hL).mpr ht
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hcon (by linarith : 1-δ<1)).comp hdiv
  apply squeeze_zero_norm (fun t => ?_) hlim
  rw [Real.norm_eq_abs]
  change |D t g| ≤ (1-δ)^(t/L)
  simpa only [Nat.mod_add_div, Nat.mul_comm (t/L) L] using bound (t/L) (t%L) g

end OMA.S_mo_429774

namespace OMA.S_mo_429774
open Filter Finset Equiv
open scoped Topology

private lemma weighted_zero (a : ℝ) (ha : 1 ≤ a) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => (∑ t ∈ range (k+1), a^t * e t) / (∑ t ∈ range (k+1), a^t))
      atTop (𝓝 0) := by
  let W (k : ℕ) := ∑ t ∈ range (k+1), a^t
  have hW (k : ℕ) : (k:ℝ)+1 ≤ W k := by
    calc
      _ = ∑ _t ∈ range (k+1), (1:ℝ) := by simp
      _ ≤ _ := sum_le_sum fun t _ => one_le_pow₀ ha
  have htop : Tendsto W atTop atTop :=
    tendsto_atTop_mono (fun k => (le_add_of_nonneg_right zero_le_one).trans (hW k))
      tendsto_natCast_atTop_atTop
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp he (ε/2) (by positivity))
  let K := ∑ t ∈ range M, a^t * |e t|
  have hs : Tendsto (fun k => K / W k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop htop
  filter_upwards [eventually_ge_atTop M, hs.eventually_lt_const (show 0<ε/2 by positivity)] with k hk hK
  have hw : 0 < W k := lt_of_lt_of_le (by positivity) (hW k)
  have H (t : ℕ) : a^t * |e t| ≤ a^t*(ε/2) + (if t<M then a^t*|e t| else 0) := by
    have hat : 0≤a^t := pow_nonneg (zero_le_one.trans ha) _
    by_cases ht : t<M
    · rw [if_pos ht]
      linarith [mul_nonneg hat (half_pos hε).le]
    · have he' : |e t| < ε/2 := by simpa [Real.dist_eq] using hM t (by omega)
      simpa [ht] using mul_le_mul_of_nonneg_left he'.le hat
  have hfilter : (range (k+1)).filter (fun t => t < M) = range M := by
    ext t; simp; omega
  have hsum : |∑ t ∈ range (k+1), a^t * e t| ≤ W k*(ε/2)+K := calc
    _ ≤ ∑ t ∈ range (k+1), |a^t * e t| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ range (k+1), a^t * |e t| := by
      simp [abs_mul, abs_of_nonneg (zero_le_one.trans ha)]
    _ ≤ _ := (sum_le_sum (s := range (k+1)) (fun t _ => H t)).trans_eq (by
      rw [sum_add_distrib, ← sum_mul, ← sum_filter, hfilter])
  simp only [Real.dist_eq,sub_zero,abs_div]
  change |∑ t ∈ range (k+1), a^t * e t| / |W k| < ε
  rw [abs_of_pos hw]
  rw [div_lt_iff₀ hw] at hK ⊢
  linarith

lemma residual_limit {n : ℕ} (hn : 2≤n) (g : G n) :
    Tendsto (fun k => mass n k g - (Fintype.card (G n):ℝ)⁻¹ -
      chi g * (Fintype.card (G n):ℝ)⁻¹ * bias n k) atTop (𝓝 0) := by
  let a := (countEdges n:ℝ)
  let b := (Fintype.card (G n):ℝ)⁻¹
  have ha : 1 ≤ a := by
    dsimp [a];exact_mod_cast (show 1 ≤ countEdges n from edges_pos hn)
  let e (t : ℕ) := (paths n t g:ℝ)/a^t -
    (if (Perm.sign g:ℤ)=(-1:ℤ)^t then 2/(Fintype.card (G n):ℝ) else 0)
  have he : Tendsto e atTop (𝓝 0) := walk_mixing hn g
  have hc (t : ℕ) : a^t*e t = (paths n t g:ℝ) - a^t*b - (chi g*b)*(-a)^t := by
    have hnz : a^t ≠ 0 := pow_ne_zero _ (by linarith)
    have hind : (if (Perm.sign g:ℤ) = (-1:ℤ)^t then 2/(Fintype.card (G n):ℝ) else 0) =
        (1+chi g*(-1:ℝ)^t)*b := by
      rw [← sign_indicator]
      split_ifs <;> simp [b,div_eq_mul_inv]
    simp only [e,hind,mul_sub, mul_div_cancel₀ _ hnz]
    rw [← neg_one_mul a, mul_pow]
    ring
  apply (weighted_zero a ha e he).congr
  intro k
  have hw : (∑ t ∈ range (k+1), a^t) = (total n k:ℝ) := by simp [a,total]
  have hw0 : (total n k:ℝ) ≠ 0 := by exact_mod_cast (total_pos n k).ne'
  simp only [hc,sum_sub_distrib,← sum_mul, ← mul_sum,hw,mass,bias]
  change (_- (total n k:ℝ)*b - chi g*b*_)/(total n k:ℝ) = _/(total n k:ℝ)- b - chi g*b*(_/(total n k:ℝ))
  field_simp
  rfl
end OMA.S_mo_429774

namespace OMA.S_mo_429774
open Filter Finset Equiv
open scoped Topology Classical
namespace Coupons
private noncomputable def mean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ i, f i) / Fintype.card α

private lemma mean_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    mean (fun x => ∑ i, f x i) = ∑ i, mean (fun x => f x i) := by
  simp only [mean, ← sum_div]
  rw [sum_comm]

private lemma mean_mono {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := div_le_div_of_nonneg_right (sum_le_sum fun a _ => h a) (by positivity)

private lemma mean_ind {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) :
    mean (fun a => if a ∈ s then (1:ℝ) else 0) = (s.card:ℝ)/Fintype.card α := by
  classical
  simp [mean]

private def avoid {n t : ℕ} (s : Finset (Fin n)) (w : Fin t → Edge n) : Prop :=
  ∀ j, (w j).1.1 ∈ s ∧ (w j).1.2 ∈ s

private lemma edges_in {n : ℕ} (s : Finset (Fin n)) :
    (univ.filter (fun e : Edge n => e.1.1 ∈ s ∧ e.1.2 ∈ s)).card = s.card.choose 2 := by
  classical
  rw [← card_product_filter_lt]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    simpa using ⟨(mem_filter.mp he).2,e.prop⟩
  · exact fun _ _ _ _ h => Subtype.ext h
  · intro p hp
    obtain ⟨hs,hlt⟩ := mem_filter.mp hp
    exact ⟨⟨p,hlt⟩,mem_filter.mpr ⟨mem_univ _,mem_product.mp hs⟩,rfl⟩

private lemma count_edges (n : ℕ) : countEdges n = n.choose 2 := by
  simpa [countEdges] using edges_in (univ : Finset (Fin n))

private lemma words_avoid {n t : ℕ} (s : Finset (Fin n)) :
    mean (fun w : Fin t → Edge n => if avoid s w then 1 else 0) =
      ((s.card.choose 2 : ℝ) / (n.choose 2 : ℝ))^t := by
  classical
  let B := univ.filter (fun e : Edge n => e.1.1 ∈ s ∧ e.1.2 ∈ s)
  let S := Fintype.piFinset (fun _ : Fin t => B)
  have h (w : Fin t → Edge n) : avoid s w ↔ w ∈ S := by simp [avoid,S,B]
  simp only [h]
  unfold mean
  simp only [sum_boole, filter_mem_eq_inter, univ_inter]
  rw [div_pow]
  simp [S, B, edges_in, ← count_edges, countEdges]

private def miss {n t : ℕ} (w : Fin t → Edge n) (i : Fin n) : Prop :=
  avoid (univ.erase i) w
private noncomputable def indicator {n t : ℕ} (w : Fin t → Edge n) (i : Fin n) : ℝ := by
  exact if miss w i then 1 else 0
private noncomputable def untouched {n t : ℕ} (w : Fin t → Edge n) : ℝ := ∑ i, indicator w i

private lemma first {n t : ℕ} (i : Fin n) :
    mean (fun w : Fin t → Edge n => indicator w i) =
      (((n-1).choose 2 : ℝ) / (n.choose 2 : ℝ))^t := by
  classical
  convert words_avoid (t := t) (univ.erase i) using 1
  · congr 1
  · simp

private lemma joint {n t : ℕ} {i j : Fin n} (hij : i ≠ j) :
    mean (fun w : Fin t → Edge n => indicator w i * indicator w j) =
      (((n-2).choose 2 : ℝ) / (n.choose 2 : ℝ))^t := by
  classical
  let s := (univ.erase i).erase j
  have hc : s.card=n-2 := by simp [s,card_erase_of_mem, hij.symm];omega
  rw [← hc, ← words_avoid]
  congr 1
  funext w
  have hh : avoid s w ↔ miss w i ∧ miss w j := by
    simp [avoid, miss, s, forall_and, and_assoc, and_comm, and_left_comm]
  simp only [hh, indicator]
  split_ifs <;> simp_all

private lemma second_le {n t : ℕ} (hn : 4 ≤ n) :
    let p := (((n-1).choose 2 : ℝ)/(n.choose 2 : ℝ))^t
    mean (fun w : Fin t → Edge n => (untouched w)^2) ≤ n*p + (n*p)^2 := by
  classical
  intro p
  have hn' : (4:ℝ) ≤ n := by exact_mod_cast hn
  have ha : (0:ℝ) < n-1 := by linarith
  have hc : ((n-1).choose 2 : ℝ)/(n.choose 2 : ℝ) = ((n:ℝ)-2)/n := by
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub (by omega : 1≤n)]
    push_cast
    field_simp
    nlinarith
  have hc' : ((n-2).choose 2 : ℝ)/(n.choose 2 : ℝ) ≤ (((n-1).choose 2 : ℝ)/(n.choose 2 : ℝ))^2 := by
    rw [hc, Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub (by omega : 2≤n)]
    push_cast
    rw [div_pow]
    field_simp
    nlinarith
  have hij_le (i j : Fin n) : mean (fun w : Fin t → Edge n => indicator w i * indicator w j) ≤
      (if i=j then p else 0) + p^2 := by
    by_cases h : i=j
    · subst j
      have he (w : Fin t → Edge n) : indicator w i * indicator w i = indicator w i := by
        unfold indicator; split_ifs <;> simp
      simp only [he, first, if_true]
      nlinarith [sq_nonneg p]
    · rw [if_neg h, zero_add, joint h]
      simpa [p, ← pow_mul, Nat.mul_comm] using
        pow_le_pow_left₀ (by positivity) hc' t
  calc
    _ = ∑ i, ∑ j, mean (fun w : Fin t → Edge n => indicator w i * indicator w j) := by
      simp only [untouched, pow_two, sum_mul, mul_sum, mean_sum]
      rw [sum_comm]
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ((if i=j then p else 0) + p^2) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => hij_le i j
    _ = _ := by simp [sum_add_distrib];ring

private lemma minimum_prob {n t : ℕ} (hn : 8 ≤ n) (ht : t ≤ n) :
    (1/256 : ℝ) ≤ (((n-1).choose 2 : ℝ)/(n.choose 2 : ℝ))^t := by
  have hnr : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hn1 : (0:ℝ) < n-1 := by linarith
  have hc : ((n-1).choose 2 : ℝ)/(n.choose 2 : ℝ) = 1-2/n := by
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub (by omega : 1≤n)]
    push_cast
    field_simp
    ring
  rw [hc]
  let b := n/4+1
  have hb : (8*b : ℕ) ≤ 3*n := by dsimp [b];omega
  have hbr : 8*(b:ℝ) ≤ 3*n := by exact_mod_cast hb
  have htb : t ≤ b * 4 := by dsimp [b];omega
  have h0 : 0 ≤ 1-2/(n:ℝ) := by field_simp;linarith
  have h1 : 1-2/(n:ℝ) ≤ 1 := by linarith [show (0:ℝ) ≤ 2/n by positivity]
  have hl : (1/4:ℝ) ≤ (1-2/(n:ℝ))^b := by
    apply le_trans _ (one_add_mul_sub_le_pow (le_trans (by norm_num) h0) b)
    field_simp
    linarith
  calc
    _ = (1/4:ℝ)^4 := by norm_num
    _ ≤ ((1-2/(n:ℝ))^b)^4 := pow_le_pow_left₀ (by norm_num) hl 4
    _ = _ := (pow_mul ..).symm
    _ ≤ _ := pow_le_pow_of_le_one h0 h1 htb

private lemma mean_square_center {α : Type*} [Fintype α] [Nonempty α] (u : α → ℝ) (e : ℝ)
    (he : mean u=e) :
    mean (fun w => (u w-e)^2) = mean (fun w => (u w)^2) - e^2 := by
  unfold mean at *
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hp (w : α) : (u w-e)^2 = u w^2 - 2*e*u w + e^2 := by ring
  simp only [hp, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
    card_univ, nsmul_eq_mul]
  field_simp at he ⊢
  linear_combination -(2*e)*he

private noncomputable def fixed {n : ℕ} (g : G n) : ℝ :=
  (Fintype.card (MulAction.fixedBy (Fin n) g) : ℝ)
private lemma fixed_as_sum {n : ℕ} (g : G n) :
    fixed g = ∑ i : Fin n, if g i=i then (1:ℝ) else 0 := by
  classical
  simp only [fixed, sum_boole]
  congr 1
  exact Fintype.card_subtype (fun i => g i=i)

private lemma untouched_le {n t : ℕ} (w : Fin t → Edge n) : untouched w ≤ fixed (endpoint w) := by
  classical
  rw [fixed_as_sum]
  apply sum_le_sum
  intro i _
  by_cases h : miss w i
  · have hfix : endpoint w i=i := by
      change endpoint w ∈ MulAction.stabilizer (G n) i
      apply list_prod_mem
      intro g hg
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hg
      change Equiv.swap (w j).1.1 (w j).1.2 i=i
      exact Equiv.swap_apply_of_ne_of_ne (mem_erase.mp (h j).1).1.symm (mem_erase.mp (h j).2).1.symm
    simp [indicator,h,hfix]
  · simp [indicator,h];split_ifs <;> norm_num

private noncomputable def good (n : ℕ) : Finset (G n) := by
  classical exact univ.filter fun g => (n:ℝ)/512 ≤ fixed g

private lemma good_words {n t : ℕ} (hn : 8 ≤ n) (ht : t ≤ n) :
    1 - 1024/(n:ℝ) ≤ mean (fun w : Fin t → Edge n => if endpoint w ∈ good n then 1 else 0) := by
  classical
  let p := (((n-1).choose 2 : ℝ)/(n.choose 2 : ℝ))^t
  let e := (n:ℝ)*p
  have hnr : (8:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hemin : (n:ℝ)/256 ≤ e := by
    have h := mul_le_mul_of_nonneg_left (minimum_prob hn ht) hn0.le
    dsimp [e, p];linarith
  have he0 : 0<e := by linarith
  have hc : 0<countEdges n := by rw [count_edges];exact Nat.choose_pos (by omega)
  let : Nonempty (Edge n) := Fintype.card_pos_iff.mp hc
  have he : mean (@untouched n t)=e := by
    change mean (fun w : Fin t → Edge n => ∑ i, indicator w i) = _
    simp [mean_sum, first, e, p]
  have hv : mean (fun w : Fin t → Edge n => (untouched w-e)^2) ≤ e := by
    rw [mean_square_center _ _ he]
    linarith [second_le (t := t) (by omega : 4≤n)]
  let a (w : Fin t → Edge n) : ℝ := if endpoint w ∈ good n then 1 else 0
  have hpoint (w : Fin t → Edge n) : (1-a w)*e^2 ≤ 4*(untouched w-e)^2 := by
    by_cases h : endpoint w ∈ good n
    · simp [a,h,sq_nonneg]
    · have hsmall : fixed (endpoint w) < (n:ℝ)/512 := lt_of_not_ge (by simpa [good] using h)
      have hU := untouched_le w
      simp only [a,if_neg h,sub_zero,one_mul]
      nlinarith [mul_nonneg (show 0 ≤ e-2*untouched w by linarith)
        (show 0 ≤ 3*e-2*untouched w by linarith)]
  have hmean := mean_mono hpoint
  have hc0 : (Fintype.card (Fin t → Edge n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hlin : mean (fun w => (1-a w)*e^2) = (1-mean a)*e^2 := by
    simp only [mean, ← sum_mul, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  have hlin' : mean (fun w : Fin t → Edge n => 4*(untouched w-e)^2) =
      4*mean (fun w : Fin t → Edge n => (untouched w-e)^2) := by
    simp only [mean, ← mul_sum, mul_div_assoc]
  rw [hlin,hlin'] at hmean
  have hbad : (1-mean a)*e ≤ 4 := by
    apply le_of_mul_le_mul_right (a := e) _ he0
    nlinarith
  have hquot : (1-mean a) ≤ 4/e := (le_div_iff₀ he0).mpr hbad
  have hcomp : 4/e ≤ 1024/(n:ℝ) := by
    rw [div_le_div_iff₀ he0 hn0];linarith
  change 1-1024/(n:ℝ) ≤ mean a
  linarith


private lemma fixed_mean {n : ℕ} (hn : 0<n) : mean (@fixed n)=1 := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let : Unique (MulAction.orbitRel.Quotient (G n) (Fin n)) :=
    ((MulAction.pretransitive_iff_unique_quotient_of_nonempty ..).mp inferInstance).some
  have hs := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G n) (Fin n)
  have hh : (∑ g : G n, Fintype.card (MulAction.fixedBy (Fin n) g)) = Fintype.card (G n) := by
    simpa only [Fintype.card_unique,one_mul] using hs
  have hp : (Fintype.card (G n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [mean,fixed,← Nat.cast_sum, hh, div_self hp]

private lemma uniform_good {n : ℕ} (hn : 0<n) :
    (∑ _g ∈ good n, (Fintype.card (G n):ℝ)⁻¹) ≤ 512/(n:ℝ) := by
  classical
  let a (g : G n) : ℝ := if g ∈ good n then 1 else 0
  have hp (g : G n) : a g * ((n:ℝ)/512) ≤ fixed g := by
    by_cases h : g ∈ good n
    · simpa [a,h] using (mem_filter.mp h).2
    · simp [a,h,fixed]
  have hh := mean_mono hp
  rw [fixed_mean hn] at hh
  have he : mean (fun g => a g * ((n:ℝ)/512)) = (mean a)*((n:ℝ)/512) := by
    simp only [mean, ← sum_mul];ring
  rw [he] at hh
  change mean (fun g => if g ∈ good n then (1:ℝ) else 0) * ((n:ℝ)/512) ≤ 1 at hh
  rw [mean_ind] at hh
  simp only [sum_const, nsmul_eq_mul, ← div_eq_mul_inv]
  rw [le_div_iff₀ (by exact_mod_cast hn)]
  linarith

private lemma good_mass {n : ℕ} (hn : 8 ≤ n) :
    1-1024/(n:ℝ) ≤ ∑ g ∈ good n, mass n (n-1) g := by
  classical
  have hc : 0<countEdges n := by rw [count_edges];exact Nat.choose_pos (by omega)
  have H (t : ℕ) (ht : t ∈ range (n-1+1)) :
      (1-1024/(n:ℝ)) * ((countEdges n)^t:ℕ) ≤ ∑ g ∈ good n, (paths n t g:ℝ) := by
    have hw := good_words hn (show t ≤ n by have := mem_range.mp ht;omega)
    unfold mean at hw
    simp only [sum_boole, Fintype.card_fun, Fintype.card_fin] at hw
    change _ ≤ (_:ℝ)/((countEdges n)^t:ℕ) at hw
    have hcf : (0:ℝ) < ((countEdges n)^t:ℕ) := by exact_mod_cast pow_pos hc t
    apply (le_div_iff₀ hcf).mp at hw
    simpa only [paths, ← Nat.cast_sum, sum_card_fiberwise_eq_card_filter] using hw
  simp only [mass,← sum_div]
  rw [le_div_iff₀ (by exact_mod_cast total_pos n (n-1))]
  rw [sum_comm]
  simpa only [total,Nat.cast_sum,mul_sum] using
    (sum_le_sum H)

end Coupons

lemma coupon : Tendsto (fun n => tv n (n-1)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun n : ℕ => 1 - 1536/(n:ℝ))
    (h := fun _ : ℕ => (1:ℝ))
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).sub
      ((tendsto_const_nhds (x := (1536:ℝ))).div_atTop tendsto_natCast_atTop_atTop)
  · exact tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 8] with n hn
    have h := test_le_tv n (n-1) (Coupons.good n)
    have hf := Coupons.good_mass hn
    have hu := Coupons.uniform_good (by omega : 0<n)
    simp only [div_eq_mul_inv] at hf hu ⊢
    linarith
  · exact Eventually.of_forall (fun n => tv_le_one n (n-1))

end OMA.S_mo_429774

namespace OMA.S_mo_429774
open Filter Finset
open scoped Topology

lemma eventual_tv {n : ℕ} (hn : 2≤n) : ∀ᶠ k in atTop, tv n k = parityGap n k := by
  classical
  by_cases hn2 : n=2
  · subst n
    exact Eventually.of_forall tv_two
  have hm : (1:ℝ) < countEdges n := by exact_mod_cast edges_gt_one (show 3≤n by omega)
  have hmin : 0 < minimumGap n := by unfold minimumGap; positivity
  let u : ℝ := (Fintype.card (G n):ℝ)⁻¹
  have hu : 0<u := by dsimp [u]; positivity
  have hall : ∀ᶠ k in atTop, ∀ g : G n,
      |mass n k g - u - chi g * u * bias n k| < u * minimumGap n := by
    apply Filter.eventually_all.mpr
    intro g
    simpa only [Real.dist_eq,sub_zero] using
      (Metric.tendsto_nhds.mp (residual_limit hn g) _ (mul_pos hu hmin))
  filter_upwards [hall] with k hk
  have hg := minimumGap_le hn k
  rw [gap_eq] at hg
  let d (g : G n) := mass n k g - u
  have hs : (∑ g, chi g * d g) = bias n k := signed_residual hn k
  rw [gap_eq,tv]
  change (∑ g, |d g|)/2 = |bias n k|/2
  by_cases hp : 0 ≤ bias n k
  · rw [abs_of_nonneg hp] at hg ⊢
    have hmult : u * minimumGap n ≤ u * bias n k := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      linarith
    have hterm (g : G n) : |d g| = chi g * d g := by
      have h := abs_lt.mp (hk g)
      change -(u * minimumGap n) < d g - chi g * u * bias n k ∧ _ at h
      rcases chi_cases g with hc|hc
      · rw [hc,one_mul] at h ⊢
        exact abs_of_nonneg (by linarith [h.1])
      · rw [hc,neg_one_mul] at h ⊢
        exact abs_of_nonpos (by dsimp [d] at *; linarith [h.2])
    simp_rw [hterm]
    rw [hs]
  · have hneg : bias n k ≤ 0 := le_of_not_ge hp
    rw [abs_of_nonpos hneg] at hg ⊢
    have hmult : u * minimumGap n ≤ u * (-bias n k) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      linarith
    have hterm (g : G n) : |d g| = -(chi g * d g) := by
      have h := abs_lt.mp (hk g)
      change -(u * minimumGap n) < d g - chi g * u * bias n k ∧ _ at h
      rcases chi_cases g with hc|hc
      · rw [hc,one_mul] at h ⊢
        exact abs_of_nonpos (by dsimp [d] at *; linarith [h.2])
      · rw [hc,neg_one_mul,neg_neg] at ⊢
        simp only [hc,neg_mul] at h
        exact abs_of_nonneg (by linarith [h.1])
    simp_rw [hterm]
    rw [sum_neg_distrib,hs]

end OMA.S_mo_429774

open Filter
open scoped Topology
open OMA.S_mo_429774

theorem OMA.solution : type_of% @OMA.S_mo_429774.main := by
  refine ⟨tv_one, ?_, coupon⟩
  intro n hn
  refine ⟨fun k => ⟨minimumGap_le hn k,gap_le_tv hn k⟩,eventual_tv hn,?_,
    fun j => (parityGap_even hn j).trans_le (gap_le_tv hn _)⟩
  obtain ⟨K,hK⟩ := eventually_atTop.mp (eventual_tv hn)
  filter_upwards [eventually_ge_atTop K] with j hj
  rw [hK (2*j+1) (by omega),parityGap_odd hn]
