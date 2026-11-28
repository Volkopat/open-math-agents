import FormalConjectures.ErdosProblems.«821»
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.PSeries

/-!
A smooth shifted-prime supply and a power lower bound for totient fibers.
The affine sieve uses centered local functions and the Chinese remainder theorem.
Pairs of squarefree kernels give a lower bound for its normalizing sum.

The affine root count builds on the Erdős 16 Romanoff proof by Devin Robison
(PR 4564) and Steven Enamakel’s development (PR 2460). The singular-factor
estimate adapts Marcus Buffett’s Erdős 971 proof (PR 3352). The squarefree
subset, smooth-box, and collision arguments generalize the Erdős 821
reduction by zarnab222-dev (PR 1162).
-/

open scoped Classical

open Finset

namespace OMALib.Sieve

noncomputable def levelFamily (Q : Finset ℕ) (z : ℕ) : Finset (Finset ℕ) :=
  Q.powerset.filter (fun S => ∏ p ∈ S, p ≤ z)

theorem levelFamily_subset {Q : Finset ℕ} {z : ℕ} : ∀ S ∈ levelFamily Q z, S ⊆ Q :=
  fun _ hS => mem_powerset.mp (mem_filter.mp hS).1

theorem prime_product_inj {Q : Finset ℕ} (hQ : ∀ p ∈ Q,p.Prime) :
    Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S,p) Q.powerset := by
  intro S hS T hT he
  have h (U) (hU : U ∈ Q.powerset) := Nat.primeFactors_prod (s := U) fun p hp => hQ p (mem_powerset.mp hU hp)
  exact (h S hS).symm.trans ((congrArg Nat.primeFactors he).trans (h T hT))

theorem card_levelFamily_le {Q : Finset ℕ} (hQ : ∀ p ∈ Q,p.Prime) (z : ℕ) :
    (levelFamily Q z).card ≤ z := by
  simpa using card_le_card_of_injOn (s := levelFamily Q z) (t := Ioc 0 z) (fun S => ∏ p ∈ S,p)
    (fun S hS => mem_Ioc.mpr ⟨prod_pos fun p hp => (hQ p (levelFamily_subset S hS hp)).pos,(mem_filter.mp hS).2⟩)
    ((prime_product_inj hQ).mono (filter_subset ..))

theorem prime_product_union_le (S T : Finset ℕ) (hp : ∀ p ∈ S,0 < p) :
    (∏ p ∈ S ∪ T,p) ≤ (∏ p ∈ S,p)*(∏ p ∈ T,p) := by
  rw [← prod_union_inter]
  exact Nat.le_mul_of_pos_right _ (prod_pos fun p h => hp p (mem_inter.mp h).1)

-- The Chinese remainder theorem factors the sum over a complete period.
theorem sum_period_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (f : ℕ → ℕ → ℝ)
    (hf : ∀ p ∈ S, ∀ n, f p n = f p (n%p)) :
    ∑ n ∈ range (∏ p ∈ S,p), ∏ p ∈ S,f p n = ∏ p ∈ S, ∑ r ∈ range p,f p r := by
  let M := ∏ p ∈ S,p
  let r (n : Fin M) (p : S) : Fin p.val := ⟨n.val%p, Nat.mod_lt _ (hS p p.prop).pos⟩
  have hb : Function.Bijective r := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · intro n m he
      apply Fin.ext
      apply Nat.ModEq.eq_of_lt_of_lt _ n.isLt m.isLt
      have cop := S.nodup_toList.pairwise_of_forall_ne (r := Nat.Coprime)
        (fun p hp q hq => (Nat.coprime_primes (hS p (by simpa using hp)) (hS q (by simpa using hq))).mpr)
      suffices h : n.val ≡ m.val [MOD S.toList.prod] by simpa only [prod_toList] using h
      apply (Nat.modEq_list_prod_iff cop).mpr
      exact fun i => congrArg Fin.val (congrFun he ⟨_,Finset.mem_toList.mp (S.toList.get_mem i)⟩)
    · simp only [Fintype.card_fin,Fintype.card_pi]
      exact (Finset.prod_coe_sort S id).symm
  let g (v : ∀ p : S, Fin p.val) := ∏ p : S, f p (v p)
  have he := (Equiv.ofBijective r hb).sum_comp g
  rw [← Fin.sum_univ_eq_sum_range]
  calc _ = ∑ n : Fin M,g (r n) := by
            refine sum_congr rfl fun n _ => ?_
            rw [← Finset.prod_coe_sort S (fun p => f p n)]
            exact prod_congr rfl fun p _ => hf p p.prop n
       _ = ∑ v,g v := he
       _ = _ := by
         dsimp only [g]
         rw [← Fintype.prod_sum (fun (p : S) (r : Fin p.val) => f p r), ← Finset.prod_coe_sort S (fun p => ∑ r ∈ range p,f p r)]
         exact prod_congr rfl fun p _ => Fin.sum_univ_eq_sum_range _ _

theorem sum_period_le (f : ℕ → ℝ) (m N : ℕ) (hm : 0 < m) (A B : ℝ)
    (hper : ∀ n, f n = f (n%m)) (hfull : ∑ n ∈ range m,f n ≤ m*A)
    (ha : 0 ≤ A) (hb : 0 ≤ B) (hf : ∀ n, f n ≤ B) :
    ∑ n ∈ range N,f n ≤ N*A + m*B := by
  have shift (k i : ℕ) : f (m*k+i) = f i := by rw [hper (m*k+i),Nat.mul_add_mod,hper i]
  have blocks (k : ℕ) : ∑ n ∈ range (m*k), f n ≤ (m*k:ℕ)*A := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ,sum_range_add]; simp_rw [shift]; push_cast at ih ⊢; linarith
  have he := Nat.div_add_mod N m
  conv_lhs => rw [← he]
  rw [sum_range_add]
  refine (add_le_add_left (blocks _) _).trans ?_
  simp_rw [shift]
  have hsmall : ∑ i ∈ range (N%m),f i ≤ (N%m:ℕ)*B :=
    (sum_le_sum fun i _ => hf i).trans_eq (by simp)
  exact add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast (show m*(N/m) ≤ N by omega)) ha)
    (hsmall.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mod_lt N hm).le) hb))

-- Products of centered local functions have zero cross terms on each period.
theorem orthogonal_pair (S T : Finset ℕ) (hprime : ∀ p ∈ S ∪ T, p.Prime)
    (F : ℕ → ℕ → ℝ) (H : ℕ → ℝ)
    (hper : ∀ p n, F p n = F p (n%p))
    (hmean : ∀ p ∈ S ∪ T, ∑ r ∈ range p, F p r = 0)
    (hvar : ∀ p ∈ S ∪ T, ∑ r ∈ range p, F p r * F p r ≤ p*H p) :
    ∑ n ∈ range (∏ p ∈ S ∪ T,p), (∏ p ∈ S,F p n)*(∏ p ∈ T,F p n) ≤
      (∏ p ∈ S ∪ T,(p:ℝ))*(if S=T then ∏ p ∈ S,H p else 0) := by
  let f (p n : ℕ) := (if p ∈ S then F p n else 1)*(if p ∈ T then F p n else 1)
  have he (n) : (∏ p ∈ S ∪ T,f p n) = (∏ p ∈ S,F p n)*(∏ p ∈ T,F p n) := by
    dsimp only [f]
    rw [prod_mul_distrib,prod_ite_mem,prod_ite_mem]
    simp
  simp_rw [← he]
  rw [sum_period_prod _ hprime f (fun p _ n => by dsimp [f]; rw [hper p n])]
  split_ifs with eq
  · subst T
    simp only [union_self, ← prod_mul_distrib]
    apply prod_le_prod (fun p hp => sum_nonneg fun r _ => by simpa [f,hp] using mul_self_nonneg (F p r))
    exact fun p hp => by simpa [f,hp] using hvar p (mem_union_left _ hp)
  · rw [mul_zero]
    apply le_of_eq
    have ⟨p,hp⟩ := SetLike.ext_iff.not.mp eq |> Classical.not_forall.mp
    push Not at hp
    rcases hp with ⟨hS,hT⟩ | ⟨hT,hS⟩
    · have h := mem_union_left T hS
      exact prod_eq_zero h (by simpa [f,hS,hT] using hmean p h)
    · have h := mem_union_right S hS
      exact prod_eq_zero h (by simpa [f,hS,hT] using hmean p h)
def pairCond (d : ℕ) (p n : ℕ) : Prop := p ∣ n * (1 + d * n)

def pairOmega (d p : ℕ) : ℕ := if p ∣ d then 1 else 2

noncomputable def subsetMass (D : Finset (Finset ℕ)) (f : ℕ → ℝ) :=
  ∑ S ∈ D, ∏ p ∈ S,f p

noncomputable def pairH (d p : ℕ) : ℝ := (1+(p:ℝ)⁻¹)*((pairOmega d p:ℝ)/(p:ℝ))
noncomputable def pairG (d z : ℕ) :=
  subsetMass (levelFamily (Nat.primesLE z) z) (pairH d)

theorem omega_pairCond {d p : ℕ} (hp : p.Prime) : ((range p).filter (pairCond d p)).card = pairOmega d p := by
  have : Fact p.Prime := ⟨hp⟩
  let u := (-(d:ZMod p)⁻¹).val
  have hset : (range p).filter (pairCond d p) = {0,u} := by
    ext n
    by_cases hn : n < p
    · have he (r : ZMod p) : (n:ZMod p) = r ↔ n = r.val := by
        rw [← (ZMod.val_injective p).eq_iff,ZMod.val_natCast_of_lt hn]
      simp only [mem_filter,mem_range,hn,true_and,mem_insert,mem_singleton,pairCond,
        ← ZMod.natCast_eq_zero_iff,Nat.cast_mul,Nat.cast_one,Nat.cast_add,mul_eq_zero]
      by_cases hd : (d:ZMod p) = 0
      · simp [hd,u,he 0]
      · rw [show 1+(d:ZMod p)*n=0 ↔ (n:ZMod p) = -(d:ZMod p)⁻¹ by
              field_simp; constructor <;> intro h <;> linear_combination h,he,he]
        simp [u]
    · have := ZMod.val_lt (-(d:ZMod p)⁻¹)
      have := hp.pos
      simp [hn,u]; omega
  rw [hset,pairOmega]
  by_cases h : p ∣ d
  · simp [h,u,(ZMod.natCast_eq_zero_iff ..).mpr h]
  · have hd : (d:ZMod p) ≠ 0 := fun e => h ((ZMod.natCast_eq_zero_iff ..).mp e)
    have hz : u ≠ 0 := by simpa [u] using hd
    simp [h,Ne.symm hz]


theorem sum_local {d p : ℕ} (hp : p.Prime) (a b : ℝ) :
    ∑ r ∈ range p,(if pairCond d p r then a else b) =
      pairOmega d p*a + ((p:ℝ)-pairOmega d p)*b := by
  calc _ = ∑ r ∈ range p, ((if pairCond d p r then a-b else 0)+b) :=
             sum_congr rfl fun r _ => by split_ifs <;> ring
       _ = _ := by rw [sum_add_distrib,← sum_filter]; simp [omega_pairCond hp]; ring
def row (m x y : ℕ) : Finset ℕ :=
  (range (x + 1)).filter (fun q => y < q ∧ q.Prime ∧ (1 + m * q).Prime)

theorem affine_count_le_sieve (d x z : ℕ) (hd0 : 0 < d) (hz : 2 ≤ z) :
    ((row d x (z^6)).card:ℝ)*pairG d z ≤ x+1+(z:ℝ)^6 := by
  let Q := Nat.primesLE z
  have hQ (p) (hp : p ∈ Q) := (Nat.mem_primesLE.mp hp).2
  let H := pairH d
  let scale (p : ℕ) := 1+(p:ℝ)⁻¹
  let F (p n : ℕ) := if pairCond d p n then H p-scale p else H p
  have hH (p : ℕ) : 0 ≤ H p := by dsimp [H,pairH]; positivity
  have hF (p) (hp : p ∈ Q) (n) : |F p n| ≤ p := by
    have h : (2:ℝ) ≤ p := by exact_mod_cast (hQ p hp).two_le
    have hp0 : (0:ℝ) < p := by linarith
    dsimp only [F,scale,H,pairH,pairOmega]
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> field_simp <;> nlinarith [sq_nonneg ((p:ℝ)-2),mul_nonneg hp0.le (sq_nonneg ((p:ℝ)-2))]
  have moments (p) (hp : p ∈ Q) :
      (∑ r ∈ range p,F p r) = 0 ∧ (∑ r ∈ range p,F p r * F p r) ≤ p*H p := by
    have hp0 : (0:ℝ) < p := by exact_mod_cast (hQ p hp).pos
    have e : (p:ℝ)*H p = scale p*pairOmega d p := by dsimp [scale,H,pairH]; field_simp
    have le : scale p - H p ≤ 1 := by
      dsimp only [scale,H,pairH,pairOmega]; split_ifs <;> push_cast <;> field_simp <;> nlinarith
    constructor
    · dsimp only [F]; rw [sum_local (hQ p hp)]; linarith
    · have sq (r) : F p r*F p r = if pairCond d p r then (H p-scale p)^2 else (H p)^2 := by
        dsimp only [F]; split_ifs <;> ring
      simp_rw [sq,sum_local (hQ p hp)]
      nlinarith only [congrArg (· * H p) e,congrArg (· * scale p) e,
        mul_le_mul_of_nonneg_left le (mul_nonneg hp0.le (hH p))]
  have avoid (n) (hn : n ∈ row d x (z^6)) (p) (hp : p ∈ Q) : F p n = H p := by
    obtain ⟨_,hcut,hpr,hpartner⟩ := mem_filter.mp hn
    apply if_neg
    intro hdiv
    have ⟨hpz,hp'⟩ := Nat.mem_primesLE.mp hp
    have := Nat.le_self_pow (by decide : 6 ≠ 0) z
    rcases hp'.dvd_mul.mp hdiv with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp' hpr).mp h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hp' hpartner).mp h
      have := Nat.le_mul_of_pos_left n hd0; omega
  let A := row d x (z^6)
  let N := x+1
  let D := levelFamily Q z
  let G := ∑ S ∈ D,∏ p ∈ S,H p
  suffices h : (A.card:ℝ)*G ≤ N+(z:ℝ)^6 by simpa only [A,G,D,H,Q,N,pairG,subsetMass,Nat.cast_add,Nat.cast_one] using h
  have hper (p n) : F p n = F p (n%p) := by
    simp only [F,pairCond,Nat.dvd_iff_mod_eq_zero,Nat.mul_mod,Nat.add_mod,Nat.mod_mod]
  let w (S : Finset ℕ) (n : ℕ) := ∏ p ∈ S,F p n
  let v (S : Finset ℕ) := ∏ p ∈ S,H p
  have hsub (S) (hS : S ∈ D) : S ⊆ Q := levelFamily_subset _ hS
  have hv (S) (_ : S ∈ D) : 0 ≤ v S := prod_nonneg fun p _ => hH p
  have bound (S) (hS : S ∈ D) : (∏ p ∈ S,p) ≤ z := (mem_filter.mp hS).2
  have hG : 1 ≤ G := by simpa only [G,v,prod_empty] using single_le_sum hv (show ∅ ∈ D by simp [D,levelFamily]; omega)
  have habs (S) (hS : S ∈ D) (n) : |w S n| ≤ z := by
    dsimp only [w]; rw [abs_prod]
    exact (prod_le_prod (fun _ _ => abs_nonneg _) (fun p hp => hF p (hsub S hS hp) n)).trans
      (by rw [← Nat.cast_prod]; exact_mod_cast bound S hS)
  have pair (S) (hS : S ∈ D) (T) (hT : T ∈ D) :
      ∑ n ∈ range N,w S n*w T n ≤ N*(if S=T then v S else 0)+(z:ℝ)^4 := by
    let m := ∏ p ∈ S ∪ T,p
    have hu : S ∪ T ⊆ Q := union_subset (hsub S hS) (hsub T hT)
    have hm : 0 < m := prod_pos fun p hp => (hQ p (hu hp)).pos
    have hmle : m ≤ z*z := (prime_product_union_le S T (fun p hp => (hQ p (hsub S hS hp)).pos)).trans
      (Nat.mul_le_mul (bound S hS) (bound T hT))
    have period (U : Finset ℕ) (hU : U ⊆ S ∪ T) (n) : w U n = w U (n%m) :=
      prod_congr rfl fun p hp => by rw [hper p n,hper p (n%m),Nat.mod_mod_of_dvd n (show p ∣ m from dvd_prod_of_mem id (hU hp))]
    have full := orthogonal_pair S T (fun p hp => hQ p (hu hp)) F H hper
      (fun p hp => (moments p (hu hp)).1) (fun p hp => (moments p (hu hp)).2)
    have h := sum_period_le (fun n => w S n*w T n) m N hm (if S=T then v S else 0) ((z:ℝ)^2)
      (fun n => by rw [period S subset_union_left n,period T subset_union_right n])
      (by simpa only [m,Nat.cast_prod] using full)
      (by split_ifs <;> first | exact hv S hS | positivity) (sq_nonneg _)
      (fun n => (le_abs_self _).trans (by rw [abs_mul,sq]; exact mul_le_mul (habs S hS n) (habs T hT n) (abs_nonneg _) (by positivity)))
    refine h.trans (add_le_add_right ?_ _)
    nlinarith only [mul_le_mul_of_nonneg_right (show (m:ℝ) ≤ z*z by exact_mod_cast hmle) (sq_nonneg (z:ℝ))]
  have upper : (A.card:ℝ)*G^2 ≤ ∑ n ∈ range N,(∑ S ∈ D,w S n)^2 := by
    calc _ = ∑ n ∈ A,(∑ S ∈ D,w S n)^2 := by
              rw [← nsmul_eq_mul,← sum_const]
              refine sum_congr rfl fun n hn => congrArg (·^2) (sum_congr rfl fun S hS =>
                prod_congr rfl fun p hp => (avoid n hn p (hsub S hS hp)).symm)
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => sq_nonneg _)
  conv_rhs at upper =>
    simp only [sq,sum_mul,mul_sum]
    rw [sum_comm]
    arg 2; ext S; rw [sum_comm]
  have est := upper.trans (sum_le_sum fun S hS => sum_le_sum fun T hT => pair T hT S hS)
  simp_rw [sum_add_distrib,← mul_sum] at est
  simp only [sum_ite_eq',sum_const,nsmul_eq_mul] at est
  have diag : ∑ S ∈ D, (if S ∈ D then v S else 0) = G := sum_congr rfl fun S hS => if_pos hS
  have hc : (D.card:ℝ) ≤ z := by exact_mod_cast card_levelFamily_le hQ z
  have hmain : (A.card:ℝ)*G^2 ≤ N*G + (z:ℝ)^6 := by
    rw [diag] at est
    refine est.trans (add_le_add_right ?_ _)
    calc _ ≤ (z:ℝ)*(z*z^4) := mul_le_mul hc (mul_le_mul_of_nonneg_right hc (by positivity)) (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (Nat.cast_nonneg _)
         _ = _ := by ring
  apply le_of_mul_le_mul_right _ (by linarith : 0 < G)
  nlinarith only [hmain,mul_le_mul_of_nonneg_left hG (pow_nonneg (Nat.cast_nonneg (α := ℝ) z) 6)]

noncomputable def divisorWeight (d : ℕ) : ℝ :=
  ∑ a ∈ d.divisors, 1/(a:ℝ)

lemma weight_nonneg (m : ℕ) : 0 ≤ divisorWeight m :=
  sum_nonneg fun _ _ => by positivity

-- Multiplying squarefree products groups pairs of prime sets by their union.
theorem union_expansion (Q : Finset ℕ) (f g : ℕ → ℝ) (v : Finset ℕ → ℝ) :
    ∑ S ∈ Q.powerset, ∑ T ∈ Q.powerset, (∏ p ∈ S,f p)*(∏ p ∈ T,g p)*v (S ∪ T) =
      ∑ U ∈ Q.powerset,(∏ p ∈ U,(f p+g p+f p*g p))*v U := by
  induction Q using Finset.induction_on generalizing v with
  | empty => simp
  | insert p Q hp ih =>
    let w (U : Finset ℕ) := v U + (f p+g p+f p*g p)*v (insert p U)
    have e (S) (hs : S ∈ Q.powerset) : p ∉ S := fun h => hp (mem_powerset.mp hs h)
    calc _ = ∑ S ∈ Q.powerset,∑ T ∈ Q.powerset, (∏ i ∈ S,f i)*(∏ i ∈ T,g i)*w (S∪T) := by
              simp_rw [sum_powerset_insert hp,← sum_add_distrib]
              refine sum_congr rfl fun S hS => ?_
              refine sum_congr rfl fun T hT => ?_
              simp only [prod_insert (e S hS),prod_insert (e T hT),union_insert,insert_union,insert_idem,w]
              ring
         _ = _ := by
           rw [ih,sum_powerset_insert hp,← sum_add_distrib]
           refine sum_congr rfl fun U hU => ?_
           rw [prod_insert (e U hU)]
           dsimp [w]; ring

def unionFamily (Q : Finset ℕ) (D : Finset (Finset ℕ)) :=
  (Q.powerset ×ˢ Q.powerset).filter fun st => st.1 ∪ st.2 ∈ D

theorem mass_union (Q : Finset ℕ) (D : Finset (Finset ℕ)) (hD : D ⊆ Q.powerset) (f g : ℕ → ℝ) :
    subsetMass D (fun p => f p+g p+f p*g p) =
      ∑ st ∈ unionFamily Q D,(∏ p ∈ st.1,f p)*(∏ p ∈ st.2,g p) := by
  have h := union_expansion Q f g (fun U => if U ∈ D then 1 else 0)
  rw [unionFamily,sum_filter,sum_product]
  simpa only [mul_ite,mul_one,mul_zero,← sum_filter,
    filter_mem_eq_inter,inter_eq_right.mpr hD,subsetMass] using h.symm
theorem reciprocal_square_sum (N : ℕ) : ∑ m ∈ Ioc 0 N, 1/(m:ℝ)^2 ≤ 2 := by
  simpa [one_div,show Ioo 0 (N+1) = Ioc 0 N by ext; simp] using sum_Ioo_inv_sq_le (α := ℝ) 0 (N+1)

-- Split each integer into a square, a squarefree divisor of d, and a squarefree part coprime to d.
theorem log_le_squarefree (d Y : ℕ) (hd : d ≠ 0) (Q : Finset ℕ) (hQ : Nat.primesLE Y ⊆ Q) :
    Real.log Y ≤ 2 * subsetMass (levelFamily (Q.filter (fun p => ¬ p ∣ d)) Y)
      (fun p => (p:ℝ)⁻¹) * divisorWeight d := by
  let A := levelFamily (Q.filter (fun p => ¬ p ∣ d)) Y
  let I := Ioc 0 Y
  let prod (u : (ℕ × Finset ℕ) × ℕ) := u.1.1^2 * (∏ p ∈ u.1.2,p) * u.2
  have cov : I ⊆ ((I ×ˢ A) ×ˢ d.divisors).image prod := by
    intro n hn
    obtain ⟨hn0,hnY⟩ := mem_Ioc.mp hn
    obtain ⟨S,hS,b,he⟩ := Nat.eq_prod_primes_mul_sq_of_mem_smoothNumbers
      (Nat.mem_smoothNumbers_of_lt hn0 (Nat.lt_succ_of_le hnY))
    let T := S.filter (fun p => ¬ p ∣ d)
    let R := S.filter (· ∣ d)
    have hp (p) (h : p ∈ S) := Nat.prime_of_mem_primesBelow (mem_powerset.mp hS h)
    have e : T.prod id * R.prod id = S.prod id := by rw [mul_comm]; exact prod_filter_mul_prod_filter_not ..
    have hR : R ⊆ d.primeFactors := fun p h => Nat.mem_primeFactors.mpr ⟨hp p (mem_filter.mp h).1,(mem_filter.mp h).2,hd⟩
    have hb : 0 < b := by by_contra! h; simp_all
    have hT := one_le_prod' (s := T) (f := id) fun p h => (hp p (mem_filter.mp h).1).one_le
    have ha := one_le_prod' (s := R) (f := id) fun p h => (hp p (mem_filter.mp h).1).one_le
    rw [he,← e] at hnY
    have hbound : b ≤ Y ∧ T.prod id ≤ Y := ⟨(Nat.le_self_pow (by decide : 2 ≠ 0) b).trans
      ((Nat.le_mul_of_pos_right _ (Nat.mul_pos hT ha)).trans hnY),
      (Nat.le_mul_of_pos_right _ ha).trans ((Nat.le_mul_of_pos_left _ (pow_pos hb 2)).trans hnY)⟩
    refine mem_image.mpr ⟨((b,T),R.prod id),mem_product.mpr ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨hb,hbound.1⟩,
      mem_filter.mpr ⟨mem_powerset.mpr (fun p h => mem_filter.mpr ⟨hQ (mem_powerset.mp hS (mem_filter.mp h).1),(mem_filter.mp h).2⟩),
        hbound.2⟩⟩,Nat.mem_divisors.mpr ⟨(prod_dvd_prod_of_subset _ _ _ hR).trans (Nat.prod_primeFactors_dvd d),hd⟩⟩,?_⟩
    change b^2*T.prod id*R.prod id = n
    rw [mul_assoc,e,← he]
  have hh := log_le_harmonic_floor (Y:ℝ) (by positivity)
  rw [Nat.floor_natCast,harmonic_eq_sum_Icc,show Icc 1 Y = I by ext; simp [I]; omega] at hh
  push_cast at hh
  refine hh.trans ((sum_le_sum_of_subset_of_nonneg cov (fun _ _ _ => by positivity)).trans ?_)
  refine (sum_image_le_of_nonneg (fun _ _ => by positivity)).trans ?_
  have e (b a : ℕ) (S : Finset ℕ) : ((prod ((b,S),a):ℕ):ℝ)⁻¹ =
      (1/(b:ℝ)^2 * (∏ p ∈ S,(p:ℝ)⁻¹)) * (1/(a:ℝ)) := by simp [prod,one_div,prod_inv_distrib,mul_comm,mul_left_comm]
  simp only [sum_product,e,← mul_sum,← sum_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (reciprocal_square_sum Y)
    (show 0 ≤ subsetMass A (fun p => (p:ℝ)⁻¹) from sum_nonneg fun _ _ => prod_nonneg fun _ _ => by positivity))
    (show 0 ≤ divisorWeight d from sum_nonneg fun _ _ => by positivity)

theorem mass_rectangle (A B : Finset (Finset ℕ)) (f g : ℕ → ℝ) :
    subsetMass A f * subsetMass B g = ∑ st ∈ A ×ˢ B,(∏ p ∈ st.1,f p)*(∏ p ∈ st.2,g p) := by
  simp only [subsetMass,sum_product,← mul_sum,← sum_mul]
-- Every harmonic pair up to Y has squarefree kernels whose union costs at most Y².
theorem normalizer_square (d Y : ℕ) (hd0 : 0 < d) :
    Real.log Y ^ 2 ≤ (2:ℝ)^2 * (pairG d (Y^2)*divisorWeight d) := by
  let z := Y^2
  let Q := Nat.primesLE z
  let D := levelFamily Q z
  let A := levelFamily Q Y
  let f (p : ℕ) := (p:ℝ)⁻¹
  let B := levelFamily (Q.filter (fun p => ¬ p ∣ d)) Y
  let b (p : ℕ) := if p ∣ d then 0 else f p
  let H := pairH d
  have prime (p) (hp : p ∈ Q) := (Nat.mem_primesLE.mp hp).2
  have hf (p) : 0 ≤ f p := by dsimp [f]; positivity
  have hb (p) : 0 ≤ b p := by dsimp [b,f]; split_ifs <;> positivity
  have hA : A ⊆ Q.powerset := filter_subset ..
  have hD : D ⊆ Q.powerset := filter_subset ..
  have sub : B ⊆ A := fun S hS => mem_filter.mpr ⟨mem_powerset.mpr ((levelFamily_subset S hS).trans (filter_subset ..)),(mem_filter.mp hS).2⟩
  have small : Nat.primesLE Y ⊆ Q := Nat.primesLE_mono (Nat.le_self_pow (by decide) _)
  have hu (S) (hS : S ∈ A) (T) (hT : T ∈ A) : S∪T ∈ D := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (union_subset (levelFamily_subset S hS) (levelFamily_subset T hT)),?_⟩
    have hle := prime_product_union_le S T (fun p hp => (prime p (levelFamily_subset S hS hp)).pos)
    simpa only [z,sq] using hle.trans (Nat.mul_le_mul (mem_filter.mp hS).2 (mem_filter.mp hT).2)
  have weight : subsetMass B f = subsetMass B b := sum_congr rfl fun S hS => prod_congr rfl
    fun p hp => (if_neg (mem_filter.mp (levelFamily_subset S hS hp)).2).symm
  have lower : subsetMass A f * subsetMass B f ≤ subsetMass D H := by
    rw [weight,mass_rectangle]
    calc _ ≤ ∑ st ∈ unionFamily Q D,(∏ p ∈ st.1,f p)*(∏ p ∈ st.2,b p) := by
              apply sum_le_sum_of_subset_of_nonneg _ (fun st _ _ => mul_nonneg
                (prod_nonneg fun _ _ => hf _) (prod_nonneg fun _ _ => hb _))
              intro st hst
              obtain ⟨hs,ht⟩ := mem_product.mp hst
              exact mem_filter.mpr ⟨mem_product.mpr ⟨hA hs,hA (sub ht)⟩,hu _ hs _ (sub ht)⟩
         _ = _ := (mass_union Q D hD f b).symm
         _ ≤ _ := by
           apply sum_le_sum fun S _ => prod_le_prod (fun p _ => by dsimp [f,b]; split_ifs <;> positivity) ?_
           intro p _
           dsimp only [H,pairH,pairOmega,b,f]
           split_ifs <;> push_cast <;> rw [div_eq_mul_inv] <;> nlinarith [sq_nonneg (p:ℝ)⁻¹]
  have hu := log_le_squarefree 1 Y one_ne_zero Q small
  rw [filter_true_of_mem (fun p hp => (prime p hp).not_dvd_one)] at hu
  simp only [divisorWeight,Nat.divisors_one,sum_singleton,Nat.cast_one,div_one,mul_one] at hu
  have hv := log_le_squarefree d Y hd0.ne' Q small
  have hl : 0 ≤ Real.log (Y:ℝ) := by positivity
  change Real.log (Y:ℝ) ≤ 2*subsetMass A f at hu
  change Real.log (Y:ℝ) ≤ 2*subsetMass B f*divisorWeight d at hv
  change _ ≤ (2:ℝ)^2*(subsetMass D H*divisorWeight d)
  nlinarith only [mul_le_mul hu hv hl (hl.trans hu),mul_le_mul_of_nonneg_right lower (weight_nonneg d)]
end OMALib.Sieve

open Finset Filter Erdos821

namespace Erdos821Design
open OMALib.Sieve

def good (x y : ℕ) := (Nat.primesLE x).filter fun p => p-1 ∈ Nat.smoothNumbers (y+1)

def pool (x y : ℕ) := (good x y).prod (·-1)

def values (x y k : ℕ) := (pool x y).divisors.filter (· ≤ x^k)

lemma pool_smooth (x y : ℕ) : pool x y ∈ Nat.smoothNumbers (y+1) :=
  prod_induction (s := good x y) (fun p : ℕ => p-1) (· ∈ Nat.smoothNumbers (y+1)) (fun _ _ => Nat.mul_mem_smoothNumbers)
    (by simp [Nat.mem_smoothNumbers]) (fun p hp => (mem_filter.mp hp).2)
lemma weight_harmonic :
    ∀ M : ℕ, (∑ m ∈ Ioc 0 M, divisorWeight m / m) ≤ 2 * (1 + Real.log M) := by
  intro M
  let f : ArithmeticFunction ℝ := ⟨fun a => 1/(a:ℝ)^2, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun b => (b:ℝ)⁻¹, by simp⟩
  have hg (M : ℕ) : ∑ i ∈ Ioc 0 M, g i ≤ 1+Real.log M := by
    simpa [g,harmonic_eq_sum_Icc,show Ioc 0 M = Icc 1 M by ext i; simp only [mem_Ioc, mem_Icc]; rfl] using harmonic_le_one_add_log M
  calc _ = ∑ m ∈ Ioc 0 M, (f*g) m := by
         refine sum_congr rfl fun m _ => ?_
         unfold divisorWeight
         rw [sum_div,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
         refine sum_congr rfl fun a ha => ?_
         have h : (a:ℝ)*((m/a:ℕ):ℝ) = m := by exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)
         change 1/(a:ℝ)/(m:ℝ) = 1/(a:ℝ)^2 * ((m/a:ℕ):ℝ)⁻¹
         conv_lhs => rw [← h]
         simp [div_eq_mul_inv,sq,mul_comm,mul_assoc]
       _ ≤ (∑ a ∈ Ioc 0 M, f a) * ∑ b ∈ Ioc 0 M,g b := by
         rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter,sum_mul_sum]
         rw [← sum_product (f := fun v : ℕ × ℕ => f v.1 * g v.2)]
         exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => by dsimp [f,g]; positivity)
       _ ≤ _ := mul_le_mul (reciprocal_square_sum M) (hg M) (sum_nonneg fun _ _ => by dsimp [g]; positivity) (by norm_num)

-- No uniqueness of the large prime divisor is required.
lemma cover (y M : ℕ) (hy : 0 < y) :
    (Nat.primesLE (y*M)).card ≤ (good (y*M) y).card +
      ∑ m ∈ Ioc 0 M, (row m (y*M/m) y).card := by
  let bad := (Ioc 0 M).biUnion (fun m => (row m (y*M/m) y).image (fun q => 1+m*q))
  have hs : Nat.primesLE (y*M) ⊆ good (y*M) y ∪ bad := by
    intro p hp
    obtain ⟨hpx,hpr⟩ := Nat.mem_primesLE.mp hp
    by_cases hg : p-1 ∈ Nat.smoothNumbers (y+1)
    · exact mem_union_left _ (by simpa only [good,mem_filter] using And.intro hp hg)
    · rw [Nat.mem_smoothNumbers'] at hg
      push Not at hg
      obtain ⟨q,hqp,hdiv,hqy⟩ := hg
      obtain ⟨m, hm⟩ := hdiv
      have hp1 := hpr.one_lt
      have hm0 : 0 < m := by
        by_contra! hz
        simp [Nat.eq_zero_of_le_zero hz] at hm
        omega
      have heq : 1 + m*q = p := by rw [mul_comm m q, ← hm]; omega

      have hmle : m ≤ M := by
        apply le_of_mul_le_mul_left (a := y) _ (by omega)
        exact (Nat.mul_le_mul_right m (by omega : y ≤ q)).trans (hm ▸ (by omega : p-1 ≤ y*M))
      have hqbound : q ≤ y*M/m := (Nat.le_div_iff_mul_le hm0).mpr (hm ▸ (by omega : p-1 ≤ y*M))
      exact mem_union_right _ (mem_biUnion.mpr ⟨m,mem_Ioc.mpr ⟨hm0,hmle⟩, mem_image.mpr ⟨q,mem_filter.mpr
          ⟨mem_range.mpr (by omega),by omega,hqp,heq ▸ hpr⟩,heq⟩⟩)
  exact (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_left
    (card_biUnion_le.trans (sum_le_sum (fun _ _ => card_image_le))) _))

lemma aggregate (Y M : ℕ) (hY : 4 ≤ Y) :
    let y := Y^12
    ((Nat.primesLE (y*M)).card : ℝ)*Real.log Y^2 ≤ (good (y*M) y).card*Real.log Y^2 +
      (12 * ((y*M : ℕ) : ℝ)) * (2 * (1 + Real.log M)) := by
  intro y
  have hmrows (m : ℕ) (hm : m ∈ Ioc 0 M) :
      ((row m (y*M/m) y).card : ℝ)*Real.log Y^2 ≤
      (12*((y*M : ℕ):ℝ))*(divisorWeight m/m) := by
    obtain ⟨hm0,hmM⟩ := mem_Ioc.mp hm
    have hbound := (Nat.le_div_iff_mul_le hm0).mpr (Nat.mul_le_mul_left y hmM)
    have hz : 2 ≤ Y^2 := (by omega : 2 ≤ Y).trans (Nat.le_self_pow (by decide) _)
    have hs := affine_count_le_sieve m (y*M/m) (Y^2) hm0 hz
    rw [← pow_mul] at hs
    change ((row m (y*M/m) y).card:ℝ)*pairG m (Y^2) ≤ ((y*M/m:ℕ):ℝ)+1+((Y^2:ℕ):ℝ)^6 at hs
    push_cast at hs
    rw [← pow_mul,show 2*6=12 by decide] at hs
    have q : ((y*M/m:ℕ):ℝ) ≤ ((y*M:ℕ):ℝ)/m := Nat.cast_div_le
    have hy : (Y:ℝ)^12 ≤ ((y*M/m:ℕ):ℝ) := by exact_mod_cast hbound
    have hy1 : (1:ℝ) ≤ (Y:ℝ)^12 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ Y))
    have main := hs.trans (show _ ≤ 3*(((y*M:ℕ):ℝ)/m) by linarith)
    have h := mul_le_mul_of_nonneg_left (normalizer_square m Y hm0) (Nat.cast_nonneg (α := ℝ) (row m (y*M/m) y).card)
    rw [div_eq_mul_inv] at main ⊢
    nlinarith only [h,mul_le_mul_of_nonneg_right main (weight_nonneg m)]
  have hsum := sum_le_sum hmrows
  rw [← mul_sum] at hsum
  have hweight := weight_harmonic M
  have hc := Nat.cast_le (α := ℝ) |>.mpr (cover y M (pow_pos (by omega : 0 < Y) _))
  push_cast at hc
  have h := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.log (Y:ℝ)))
  rw [add_mul,sum_mul] at h
  exact h.trans (add_le_add_right (hsum.trans (mul_le_mul_of_nonneg_left hweight (by positivity))) _)

theorem pi_lower (y : ℕ) (hy : 100 ≤ y) : (y : ℝ) / 3 ≤ (Nat.primesLE y).card * Real.log y := by
  have h : (100 : ℝ) ≤ y := by exact_mod_cast hy
  have hl := Real.log_le_sub_one_of_pos (show 0 < ((y:ℝ)+1)/4 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at hl
  rw [Nat.primesLE_card_eq_primeCounting]
  linarith [Chebyshev.psi_ge y, Chebyshev.psi_le_primeCounting_mul_log y,
    Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num),
    mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg y)]

-- With these fixed powers the discarded rows account for at most X / (10⁷ log t).
theorem supply : ∀ᶠ t : ℕ in atTop, t^600003 ≤ (good (t^600004) (t^600000)).card := by
  have hlim := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ)<1/10000000))
  filter_upwards [hlim,(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 1),eventually_ge_atTop 100] with t ht hlog h0
  let L := Real.log (t:ℝ)
  let X : ℝ := (t^600004:ℕ)
  let N : ℝ := (good (t^600004) (t^600000)).card
  let P : ℝ := (Nat.primesLE (t^600004)).card
  change 1 ≤ L at hlog
  have hL : 0 < L := by linarith
  have hsmall := (Real.le_norm_self _).trans ht
  change L ≤ 1/10000000*‖(t:ℝ)‖ at hsmall
  rw [Real.norm_of_nonneg (Nat.cast_nonneg t)] at hsmall
  have h := aggregate (t^50000) (t^4) ((by omega : 4 ≤ t).trans (Nat.le_self_pow (by decide : 50000 ≠ 0) t))
  dsimp only at h
  rw [← pow_mul,← pow_add] at h
  change P*Real.log (t^50000:ℕ)^2 ≤ N*Real.log (t^50000:ℕ)^2+12*X*(2*(1+Real.log (t^4:ℕ))) at h
  have hπ := pi_lower _ (h0.trans (Nat.le_self_pow (by decide : 600004 ≠ 0) t))
  change X/3 ≤ P*Real.log (t^600004:ℕ) at hπ
  norm_num only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_mul] at h hπ
  change P*(50000*L)^2 ≤ N*(50000*L)^2+12*X*(2*(1+4*L)) at h
  change X/3 ≤ P*(600004*L) at hπ
  have hX : 0 ≤ X := Nat.cast_nonneg _
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have bound : P*L ≤ N*L+X/10000000 := by
    apply le_of_mul_le_mul_right _ hL
    nlinarith only [h,hX,mul_nonneg hX (sub_nonneg.mpr hlog)]
  have final : X ≤ N*t := by nlinarith only [hπ,bound,mul_nonneg hN hL.le,mul_le_mul_of_nonneg_left hsmall hN]
  change ((t^600004:ℕ):ℝ) ≤ N*t at final
  rw [pow_succ t 600003,Nat.cast_mul] at final
  dsimp only [N] at final
  exact_mod_cast le_of_mul_le_mul_right final (by positivity : (0:ℝ)<t)

lemma block_choose (b k : ℕ) (hb : 1 ≤ b) :
    b ^ k ≤ (b * k).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_mul_right (Nat.succ_ne_zero k), Nat.succ_sub_one, pow_succ']
    apply Nat.mul_le_mul_left
    apply ih.trans (Nat.choose_le_choose k ?_)
    rw [Nat.mul_succ]
    omega

-- Recover the subset of primes from the product before counting totients.
lemma many_products (b k x y : ℕ) (hb : 1 ≤ b) (hcard : b*k ≤ (good x y).card) :
    ∃ S : Finset ℕ, b^k ≤ S.card ∧ ∀ m ∈ S,
      m.totient ∈ values x y k := by
  let P := good x y
  have hmem (p) (hp : p ∈ P) := mem_filter.mp hp
  have hP (p) (hp : p ∈ P) := Nat.mem_primesLE.mp (hmem p hp).1
  let S := (P.powersetCard k).image (fun A => ∏ p ∈ A, p)
  have hS : S.card = P.card.choose k := by
    apply (Finset.card_image_of_injOn ?_).trans (Finset.card_powersetCard ..)
    exact (prime_product_inj (fun p hp => (hP p hp).2)).mono
      (fun A hA => mem_powerset.mpr (mem_powersetCard.mp hA).1)
  refine ⟨S, ?_, ?_⟩
  · rw [hS]
    exact (block_choose b k hb).trans (Nat.choose_le_choose _ hcard)
  · intro m hm
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hsub, hsize⟩ := Finset.mem_powersetCard.mp hA
    have hprime (p) (hp : p ∈ A) : Nat.Prime p := (hP p (hsub hp)).2
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_,(pool_smooth x y).1⟩,?_⟩
    · rw [Nat.totient_eq_div_primeFactors_mul,Nat.primeFactors_prod hprime,
        Nat.div_self (prod_pos fun p hp => (hprime p hp).pos),one_mul]
      exact prod_dvd_prod_of_subset A P (fun p => p-1) hsub
    · rw [← hsize]
      exact (Nat.totient_le _).trans (prod_le_pow_card _ _ _ (fun p hp => (hP p (hsub hp)).1))

lemma fiber_finite (n : ℕ) (hn : 0 < n) : {m : ℕ | Nat.totient m = n}.Finite := by
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (n + 2)
  have hpow : 1 < q ^ n := one_lt_pow₀ hp.one_lt hn.ne'
  apply (Set.finite_Iic (q ^ n - 1)).subset
  intro m hm
  change m.totient = n at hm
  have hc : q.Coprime m := hp.coprime_iff_not_dvd.mpr fun h => by
    have hd := Nat.totient_dvd_of_dvd h
    rw [Nat.totient_prime hp, hm] at hd
    have := Nat.le_of_dvd hn hd
    omega
  have he := Nat.ModEq.pow_totient hc
  rw [hm] at he
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hpow) ((Nat.modEq_iff_dvd' hpow.le).mp he.symm)


lemma few_values (D : ℕ) : ∀ᶠ t : ℕ in atTop,
    (values (t^(D+4)) (t^D) (t^(D+1))).card ≤ t^(t^(D+1)) := by
  filter_upwards [eventually_ge_atTop (2*D+9)] with t ht
  let x := t^(D+4)
  let y := t^D
  let L := pool x y
  have hL := pool_smooth x y
  have hI (p) (hp : p ∈ good x y) := Nat.mem_primesLE.mp (mem_filter.mp hp).1
  have hc : (good x y).card ≤ x := by
    simpa using card_le_card (show good x y ⊆ Icc 1 x from fun p hp => mem_Icc.mpr ⟨(hI p hp).2.one_le,(hI p hp).1⟩)
  have he (q : ℕ) : L.factorization q ≤ x*x := by
    dsimp only [L,pool]
    rw [Nat.factorization_prod_apply (fun p (hp : p ∈ good x y) => (mem_filter.mp hp).2.1)]
    calc _ ≤ ∑ _p ∈ good x y,x := sum_le_sum fun p hp => (Nat.factorization_lt q (mem_filter.mp hp).2.1).le.trans
          ((Nat.sub_le p 1).trans (hI p hp).1)
         _ ≤ _ := by simpa using Nat.mul_le_mul_right x hc
  have hs : L.primeFactors.card ≤ y := by
    refine (card_le_card (show L.primeFactors ⊆ Icc 1 y from fun q hq => ?_)).trans_eq (by simp)
    have h := Nat.mem_primesBelow.mp (Nat.primeFactors_subset_of_mem_smoothNumbers hL hq)
    exact mem_Icc.mpr ⟨h.2.one_le,Nat.le_of_lt_succ h.1⟩
  have ht1 : 1 < t := by omega
  calc _ ≤ L.divisors.card := card_le_card (filter_subset ..)
       _ ≤ (x*x+1)^y := by
         rw [Nat.card_divisors hL.1]
         exact (prod_le_pow_card _ _ _ (fun q _ => Nat.succ_le_succ (he q))).trans (Nat.pow_le_pow_right (by omega) hs)
       _ ≤ (t^(2*D+9))^y := by
         apply Nat.pow_le_pow_left; dsimp [x]; rw [← pow_add]; exact pow_lt_pow_right₀ ht1 (by omega)
       _ ≤ _ := by rw [← pow_mul,pow_succ t D,mul_comm (t^D)]; exact pow_le_pow_right₀ ht1.le (Nat.mul_le_mul_right _ ht)

-- Pigeonhole the products by totient and let their minimum fiber size tend to infinity.
theorem conclusion (D : ℕ)
    (hs : ∀ᶠ t : ℕ in atTop, t^(D+3) ≤ (good (t^(D+4)) (t^D)).card) :
    type_of% @Erdos821.erdos_821.variants.erdos := by
  refine ⟨1 / (((D+4 : ℕ) : ℝ) + 1), by positivity, ?_⟩
  by_contra hn
  obtain ⟨B, hB⟩ := ((Set.not_infinite.mp hn).image g).bddAbove
  obtain ⟨t,ht,hB',hP,hfew⟩ := ((eventually_ge_atTop 2).and
    ((eventually_gt_atTop B).and (hs.and (few_values D)))).exists
  let k := t^(D+1)
  let x := t^(D+4)
  let y := t^D
  have hcard : (t^2)*k ≤ (good x y).card := by
    simpa only [k, x, y, ← pow_add, show 2+(D+1) = D+3 by omega] using hP
  obtain ⟨S,hmany,hmap⟩ := many_products (t^2) k x y (one_le_pow₀ (by omega : 1 ≤ t)) hcard
  let T := values x y k

  let r := t^k
  have htr : t ≤ r := Nat.le_self_pow (by dsimp [k]; positivity) _
  have hr : 1 < r := by omega
  have hcount : T.card * r ≤ S.card := (Nat.mul_le_mul_right r hfew).trans (by
    simpa only [r,← pow_add,← pow_mul,two_mul] using hmany)
  obtain ⟨m,hm⟩ := card_pos.mp (lt_of_lt_of_le (by positivity) hmany)
  obtain ⟨n,hn,hf⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to hmap ⟨_,hmap m hm⟩ hcount
  obtain ⟨hdiv,hnx⟩ := mem_filter.mp hn
  have hsub : (↑(S.filter (fun m => m.totient = n)) : Set ℕ) ⊆ {m : ℕ | m.totient = n} :=
    fun _ h => (mem_filter.mp h).2
  have hrg : r ≤ g n := hf.trans (by
    simpa only [Set.ncard_coe_finset,g] using Set.ncard_le_ncard hsub (fiber_finite n (Nat.pos_of_mem_divisors hdiv)))
  apply hB'.not_ge ((htr.trans hrg).trans (hB ⟨n,?_,rfl⟩))
  apply lt_of_lt_of_le _ (by exact_mod_cast hrg : (r:ℝ) ≤ g n)
  apply (Real.rpow_lt_rpow_iff (by positivity) (by positivity)
    (by positivity : 0 < ((D+4 : ℕ):ℝ)+1)).mp
  rw [← Real.rpow_mul (by positivity),one_div_mul_cancel (by positivity : ((D+4:ℕ):ℝ)+1 ≠ 0),
    Real.rpow_one,← Nat.cast_succ,Real.rpow_natCast]
  have hnr : n ≤ r^(D+4) := by simpa only [r,x,← pow_mul,Nat.mul_comm k (D+4)] using hnx
  exact (show (n:ℝ) ≤ (r:ℝ)^(D+4) by exact_mod_cast hnr).trans_lt
    (pow_lt_pow_right₀ (by exact_mod_cast hr) (Nat.lt_succ_self _))

end Erdos821Design

theorem OMA.solution : type_of% @Erdos821.erdos_821.variants.erdos :=
  Erdos821Design.conclusion 600000 Erdos821Design.supply
