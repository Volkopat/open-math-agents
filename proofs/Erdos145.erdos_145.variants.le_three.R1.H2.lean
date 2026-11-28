import OMAReductions.R_Erdos145_erdos_145_variants_le_three_R1
/-! Hooley 1973 cubic moment of gaps between consecutive squarefree integers. -/
namespace Erdos145CubicGap
open Filter Finset Erdos145
open scoped Topology BigOperators
private abbrev nml:=@Nat.mul_le_mul_left
private abbrev nmr:=@Nat.mul_le_mul_right
private abbrev nmm:=@Nat.mul_le_mul
private abbrev npl:=@Nat.pow_le_pow_left
private abbrev npr:=@Nat.pow_le_pow_right
private abbrev dls:=@Nat.div_mul_le_self
private abbrev lmd:=@Nat.lt_mul_div_succ
private abbrev llp:=@Nat.le_log_of_pow_le
private abbrev lsl:=@Nat.lt_pow_succ_log_self
private abbrev pls:=@Nat.pow_log_le_self
private abbrev lmr:=@Nat.log_mono_right
private abbrev ldim:=@Nat.le_div_iff_mul_le
private abbrev o1p:=@Nat.one_le_pow
private abbrev ddll:=@Nat.div_le_div_left
private abbrev ddlr:=@Nat.div_le_div_right
private abbrev dvls:=@Nat.div_le_self
private abbrev ncs:=@Nat.cast_sub
private abbrev pnz:=@Nat.pos_of_ne_zero
private abbrev ml:=@mul_le_mul_of_nonneg_left
private abbrev mr:=@mul_le_mul_of_nonneg_right
private abbrev mlm:=@mul_le_mul
private abbrev lp0:=@le_of_pow_le_pow_left₀
private abbrev pr0:=@pow_le_pow_right₀
private abbrev pl0:=@pow_le_pow_left₀
private abbrev lsp:=@le_self_pow₀
private abbrev dli:=@div_le_iff₀
private abbrev ldi:=@le_div_iff₀
private abbrev ddi:=@div_le_div_iff₀
private abbrev ssub:=@sum_le_sum_of_subset_of_nonneg
private abbrev cbi:=@card_biUnion_le
private abbrev cfl:=@card_filter_le
private abbrev clc:=@card_le_card
private abbrev cul:=@card_union_le
private abbrev fsub:=@filter_subset
private abbrev ltr:=@le_trans
private abbrev lol:=@le_of_lt
private abbrev mf:=@mem_filter
private abbrev mioc:=@mem_Ioc
private abbrev micc:=@mem_Icc
private abbrev mico:=@mem_Ico
private abbrev mrng:=@mem_range
private abbrev mbu:=@mem_biUnion
private abbrev mun:=@mem_union
private abbrev mim:=@mem_image
private abbrev sls:=@sum_le_sum
private abbrev lml:=@le_max_left
private abbrev lmrt:=@le_max_right
private abbrev padd:=@pow_add
private abbrev pmul:=@pow_mul
private abbrev mpow:=@mul_pow
private abbrev dpow:=@div_pow
private abbrev mcom:=@mul_comm
private abbrev omul:=@one_mul
lemma su_nn {α:Type*} [DecidableEq α] (s t:Finset α)
  (f:α->ℝ) (hf:∀ x∈s∪t,0<=f x) :
  ∑ x∈s∪t,f x<=(∑ x∈s,f x)+∑ x∈t,f x:=by
 have h:=Finset.sum_union_inter (s₁:=s) (s₂:=t) (f:=f)
 have hnonneg:0<=∑ x∈s ∩ t,f x:=sum_nonneg (fun x hx => hf x (mem_union_left t (mem_inter.mp hx).1))
 linarith
lemma sbu_nn {α β:Type*} [DecidableEq α] [DecidableEq β]
  (s:Finset α) (t:α->Finset β) (f:β->ℝ) (hf:∀ a∈s,∀ b∈t a,0<=f b) :
  ∑ b∈s.biUnion t,f b<=∑ a∈s,∑ b∈t a,f b:=by
 induction s using Finset.induction_on with
 | empty => simp
 | insert a s ha ih =>
  rw [Finset.biUnion_insert,Finset.sum_insert ha]
  have hf1:∀ x∈t a∪s.biUnion t,0<=f x:=by
   intro x hx
   rcases mun.mp hx with h1 | h2
   · exact hf a (mem_insert_self a s) x h1
   ·
    rcases mbu.mp h2 with ⟨a',ha',hx'⟩
    exact hf a' (mem_insert_of_mem ha') x hx'
  have hih:=ih (fun a' ha' => hf a' (mem_insert_of_mem ha'))
  have hunion:=su_nn (t a) (s.biUnion t) f hf1
  linarith
lemma sum_inv_sq_Ioc_le_sub (a b:ℕ) (ha:1<=a) (hab:a<=b) :
  ∑ n∈Ioc a b,(1:ℝ)/(n:ℝ)^2<=1/(a:ℝ) - 1/(b:ℝ):=by
 induction b with
 | zero => omega
 | succ k ihk =>
  by_cases hk:a<=k
  ·
   have hI:Ioc a (k+1)=insert (k+1) (Ioc a k):=by
    ext x;simp only [mioc,mem_insert];omega
   have hn:k+1 ∉ Ioc a k:=by simp
   rw [hI,sum_insert hn]
   have hk_ih:=ihk hk
   have h1:(1:ℝ)/((k+1:ℕ):ℝ)^2<=1/(k:ℝ) - 1/((k+1:ℕ):ℝ):=by
    have hp1:(0:ℝ) < (k:ℝ):=by exact_mod_cast (by omega:0 < k)
    have hp2:(0:ℝ) < ((k+1:ℕ):ℝ):=by positivity
    rw [div_sub_div _ _ hp1.ne' hp2.ne']
    rw [ddi (by positivity) (by positivity)]
    push_cast
    nlinarith
   linarith
  ·
   have haeq:a=k+1:=by omega
   subst haeq
   simp
lemma sum_inv_sq_Ioc_le (a b:ℕ) (ha:1<=a) :
  ∑ n∈Ioc a b,(1:ℝ)/(n:ℝ)^2<=1/(a:ℝ):=by
 by_cases hab:a<=b
 ·
  have h:=sum_inv_sq_Ioc_le_sub a b ha hab
  have hpos:(0:ℝ)<=1/(b:ℝ):=by positivity
  linarith
 ·
  have hemp:Ioc a b=∅:=by
   ext x;simp only [mioc,notMem_empty,iff_false];omega
  rw [hemp,sum_empty]
  positivity
lemma sum_inv_sq_odd_tail (N:ℕ) :
  ∑ p∈(Icc 15 N).filter Nat.Prime,(1:ℝ)/(p:ℝ)^2<=1/28:=by
 have hsub:(Icc 15 N).filter Nat.Prime ⊆
   (Ioc 7 (N/2+1)).image (fun k => 2*k+1):=by
  intro p hp
  simp only [mf,micc] at hp
  have hp15:15<=p:=hp.1.1
  have hpN:p<=N:=hp.1.2
  simp only [mim,mioc]
  have hodd:p % 2=1:=by
   rcases hp.2.eq_two_or_odd with h2 | hodd
   · omega
   · exact hodd
  have hne15:p≠15:=by
   intro h15;subst h15;exact absurd hp.2 (by norm_num)
  have hp17:17<=p:=by omega
  exact ⟨p/2,⟨by omega,by omega⟩,by omega⟩
 have hinj:∀ a∈Ioc 7 (N/2+1),∀ b∈Ioc 7 (N/2+1),2*a+1=2*b+1->a=b:=fun _ _ _ _ h => by omega
 have himg_eq:∑ p∈(Ioc 7 (N/2+1)).image (fun k:ℕ => 2*k+1),(1:ℝ)/(p:ℝ)^2=∑ k∈Ioc 7 (N/2+1),(1:ℝ)/((2*k+1:ℕ):ℝ)^2:=sum_image hinj
 calc
  ∑ p∈(Icc 15 N).filter Nat.Prime,(1:ℝ)/(p:ℝ)^2
   <= ∑ p∈(Ioc 7 (N/2+1)).image (fun k:ℕ => 2*k+1),(1:ℝ)/(p:ℝ)^2:=ssub hsub (fun _ _ _ => by positivity)
  _=∑ k∈Ioc 7 (N/2+1),(1:ℝ)/((2*k+1:ℕ):ℝ)^2:=himg_eq
  _<=∑ k∈Ioc 7 (N/2+1),(1:ℝ)/(4*(k:ℝ)^2):=by
    apply sls
    intro k hk
    simp only [mioc] at hk
    have hkpos:(0:ℝ) < (k:ℝ):=by exact_mod_cast (by omega:0 < k)
    rw [ddi (by positivity) (by positivity)]
    push_cast
    nlinarith
  _=(1/4:ℝ)*∑ k∈Ioc 7 (N/2+1),(1:ℝ)/(k:ℝ)^2:=by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    ring
  _<=(1/4:ℝ)*(1/(7:ℝ)):=by
    have h:=sum_inv_sq_Ioc_le 7 (N/2+1) (by omega)
    nlinarith
  _=1/28:=by norm_num
lemma sum_prime_inv_sq_le (N:ℕ) :
  ∑ p∈(Icc 1 N).filter Nat.Prime,(1:ℝ)/(p:ℝ)^2<=48/100:=by
 have hsplit:(Icc 1 N).filter Nat.Prime ⊆
   ({2,3,5,7,11,13}:Finset ℕ)∪(Icc 15 N).filter Nat.Prime:=by
  intro p hp
  simp only [mf,micc] at hp
  simp only [mun,mem_insert,mem_singleton,mf,micc]
  by_cases h15:15<=p
  · exact Or.inr ⟨⟨h15,hp.1.2⟩,hp.2⟩
  ·
   left
   have hpr:=hp.2
   have hp1:1<=p:=hp.1.1
   interval_cases p
   all_goals try norm_num at hpr
   all_goals omega
 have h1:∑ p∈({2,3,5,7,11,13}:Finset ℕ),(1:ℝ)/(p:ℝ)^2<=44/100:=by
  norm_num
 have h2:=sum_inv_sq_odd_tail N
 calc
  ∑ p∈(Icc 1 N).filter Nat.Prime,(1:ℝ)/(p:ℝ)^2
   <= ∑ p∈({2,3,5,7,11,13}:Finset ℕ)∪(Icc 15 N).filter Nat.Prime,(1:ℝ)/(p:ℝ)^2:=ssub hsplit (fun _ _ _ => by positivity)
  _<=(∑ p∈({2,3,5,7,11,13}:Finset ℕ),(1:ℝ)/(p:ℝ)^2)+(∑ p∈(Icc 15 N).filter Nat.Prime,(1:ℝ)/(p:ℝ)^2):=su_nn _ _ _ (fun _ _ => by positivity)
  _<=44/100+1/28:=by linarith
  _<=48/100:=by norm_num
lemma harmonic_le_log2 (N:ℕ) (_hN:1<=N) :
  ∑ q∈Icc 1 N,(1:ℝ)/(q:ℝ)<=(Nat.log 2 N:ℝ)+1:=by
 have hsub:Icc 1 N ⊆
   (range (Nat.log 2 N+1)).biUnion
    (fun j:ℕ => Ico (2^j) (2^(j+1))):=by
  intro q hq
  simp only [micc] at hq
  simp only [mbu,mrng,mico]
  refine ⟨Nat.log 2 q,?_,?_,?_⟩
  ·
   have hle:Nat.log 2 q<=Nat.log 2 N:=lmr hq.2
   omega
  · exact pls 2 (by omega)
  · exact lsl (by omega) q
 calc
  ∑ q∈Icc 1 N,(1:ℝ)/(q:ℝ)
   <= ∑ q∈(range (Nat.log 2 N+1)).biUnion
     (fun j:ℕ => Ico (2^j:ℕ) (2^(j+1))),(1:ℝ)/(q:ℝ):=ssub hsub (fun _ _ _ => by positivity)
  _<=∑ j∈range (Nat.log 2 N+1),∑ q∈Ico (2^j:ℕ) (2^(j+1)),(1:ℝ)/(q:ℝ):=sbu_nn _ _ _ (fun _ _ _ _ => by positivity)
  _<=∑ _j∈range (Nat.log 2 N+1),(1:ℝ):=by
    apply sls
    intro j _
    calc
     ∑ q∈Ico (2^j:ℕ) (2^(j+1)),(1:ℝ)/(q:ℝ)
      <= ∑ _q∈Ico (2^j:ℕ) (2^(j+1)),(1:ℝ)/((2^j:ℕ):ℝ):=by
       apply sls
       intro q hq
       simp only [mico] at hq
       have hpos:(0:ℝ) < ((2^j:ℕ):ℝ):=by positivity
       exact one_div_le_one_div_of_le hpos (by exact_mod_cast hq.1)
     _=((Ico (2^j:ℕ) (2^(j+1))).card:ℝ)*(1/((2^j:ℕ):ℝ)):=by
       rw [sum_const,nsmul_eq_mul]
     _=1:=by
       rw [Nat.card_Ico]
       have hsub2:2^(j+1) - 2^j=2^j:=by
        rw [pow_succ];omega
       rw [hsub2]
       have hne:((2^j:ℕ):ℝ)≠0:=by positivity
       field_simp
  _=(Nat.log 2 N:ℝ)+1:=by
    rw [sum_const,card_range,nsmul_eq_mul,mul_one]
    push_cast
    ring
lemma tau_mul_le (u v:ℕ) (hu:0 < u) (hv:0 < v) :
  (u*v).divisors.card<=u.divisors.card*v.divisors.card:=by
 have hmul:(u.divisors ×ˢ v.divisors).card=u.divisors.card*v.divisors.card:=card_product _ _
 rw [← hmul]
 refine card_le_card_of_injOn (fun w => (Nat.gcd w u,w/Nat.gcd w u)) ?_ ?_
 ·
  intro w hw
  rw [mem_coe,Nat.mem_divisors] at hw
  rw [mem_coe,mem_product,Nat.mem_divisors,Nat.mem_divisors]
  have hg_pos:0 < Nat.gcd w u:=Nat.gcd_pos_of_pos_right w hu
  have hg_dvd_w:Nat.gcd w u∣w:=Nat.gcd_dvd_left w u
  have hg_dvd_u:Nat.gcd w u∣u:=Nat.gcd_dvd_right w u
  refine ⟨⟨hg_dvd_u,hu.ne'⟩,⟨?_,hv.ne'⟩⟩
  have hcop:Nat.Coprime (w/Nat.gcd w u) (u/Nat.gcd w u):=Nat.coprime_div_gcd_div_gcd hg_pos
  have hdvd:(w/Nat.gcd w u)∣(u/Nat.gcd w u)*v:=by
   rcases hw.1 with ⟨k,hk⟩
   refine ⟨k,?_⟩
   have h1:Nat.gcd w u*((u/Nat.gcd w u)*v)=Nat.gcd w u*((w/Nat.gcd w u)*k):=by
    calc
     Nat.gcd w u*((u/Nat.gcd w u)*v)
      = (Nat.gcd w u*(u/Nat.gcd w u))*v:=by ring
     _=u*v:=by rw [Nat.mul_div_cancel' hg_dvd_u]
     _=w*k:=hk
     _=(Nat.gcd w u*(w/Nat.gcd w u))*k:=by rw [Nat.mul_div_cancel' hg_dvd_w]
     _=Nat.gcd w u*((w/Nat.gcd w u)*k):=by ring
   exact Nat.eq_of_mul_eq_mul_left hg_pos h1
  exact hcop.dvd_of_dvd_mul_left hdvd
 ·
  intro w₁ _ w₂ _ heq
  simp only [Prod.mk.injEq] at heq
  have h1:Nat.gcd w₁ u*(w₁ / Nat.gcd w₁ u)=w₁:=Nat.mul_div_cancel' (Nat.gcd_dvd_left w₁ u)
  have h2:Nat.gcd w₂ u*(w₂ / Nat.gcd w₂ u)=w₂:=Nat.mul_div_cancel' (Nat.gcd_dvd_left w₂ u)
  calc
   w₁=Nat.gcd w₁ u*(w₁ / Nat.gcd w₁ u):=h1.symm
   _=Nat.gcd w₂ u*(w₂ / Nat.gcd w₂ u):=by rw [heq.2,heq.1]
   _=w₂:=h2
lemma sum_tau_le (N:ℕ) (hN:1<=N) :
  ∑ n∈Icc 1 N,(n.divisors.card:ℝ)<=(N:ℝ)*((Nat.log 2 N:ℝ)+1):=by
 have hdouble:∑ n∈Icc 1 N,n.divisors.card=∑ q∈Icc 1 N,((Icc 1 N).filter (fun n => q∣n)).card:=by
  have h1:∀ n∈Icc 1 N,n.divisors.card=∑ q∈Icc 1 N,if q∣n then 1 else 0:=by
   intro n hn
   simp only [micc] at hn
   rw [← card_filter]
   congr 1
   ext q
   simp only [Nat.mem_divisors,mf,micc]
   constructor
   ·
    rintro ⟨hd,_⟩
    refine ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),ltr (Nat.le_of_dvd (by omega) hd) hn.2⟩,hd⟩
   ·
    rintro ⟨⟨_,_⟩,hd⟩
    exact ⟨hd,by omega⟩
  rw [sum_congr rfl h1,sum_comm]
  apply sum_congr rfl
  intro q _
  rw [card_filter]
 have hcast:(∑ n∈Icc 1 N,(n.divisors.card:ℝ))=∑ q∈Icc 1 N,(((Icc 1 N).filter (fun n => q∣n)).card:ℝ):=by
  exact_mod_cast hdouble
 rw [hcast]
 calc
  ∑ q∈Icc 1 N,(((Icc 1 N).filter (fun n => q∣n)).card:ℝ)
   <= ∑ q∈Icc 1 N,(N:ℝ)/(q:ℝ):=by
    apply sls
    intro q hq
    simp only [micc] at hq
    have hcard:((Icc 1 N).filter (fun n => q∣n)).card<=N/q:=by
     have hsub:(Icc 1 N).filter (fun n => q∣n) ⊆
       (Icc 1 (N/q)).image (fun k => q*k):=by
      intro n hn
      simp only [mf,micc] at hn
      simp only [mim,micc]
      rcases hn.2 with ⟨k,rfl⟩
      refine ⟨k,⟨?_,?_⟩,rfl⟩
      ·
       by_contra hk
       push Not at hk
       have hk0:k=0:=by omega
       subst hk0;simp at hn
      · exact (ldim (by omega)).mpr (by rw [mcom];exact hn.1.2)
     calc
      ((Icc 1 N).filter (fun n => q∣n)).card
       <= ((Icc 1 (N/q)).image (fun k => q*k)).card:=clc hsub
      _<=(Icc 1 (N/q)).card:=card_image_le
      _=N/q:=by simp
    calc
     (((Icc 1 N).filter (fun n => q∣n)).card:ℝ)
      <= ((N/q:ℕ):ℝ):=by exact_mod_cast hcard
     _<=(N:ℝ)/(q:ℝ):=by
      rw [ldi (by exact_mod_cast (by omega:0 < q))]
      exact_mod_cast dls N q
  _=(N:ℝ)*∑ q∈Icc 1 N,(1:ℝ)/(q:ℝ):=by
    rw [mul_sum]
    apply sum_congr rfl
    intro q _
    ring
  _<=(N:ℝ)*((Nat.log 2 N:ℝ)+1):=by
    exact ml (harmonic_le_log2 N hN) (by positivity)
lemma cm_ioc (a h d:ℕ) (hd:0 < d) :
  ((Ioc a (a+h)).filter (fun n => d∣n)).card<=h/d+1:=by
 by_cases hemp:((Ioc a (a+h)).filter (fun n => d∣n)).Nonempty
 ·
  let m₀:=((Ioc a (a+h)).filter (fun n => d∣n)).min' hemp
  have hm₀_mem:m₀∈(Ioc a (a+h)).filter (fun n => d∣n):=min'_mem _ hemp
  simp only [mf,mioc] at hm₀_mem
  have hsub:(Ioc a (a+h)).filter (fun n => d∣n) ⊆
    (range (h/d+1)).image (fun k => m₀+k*d):=by
   intro n hn
   have hle:m₀<=n:=min'_le _ n hn
   simp only [mf,mioc] at hn
   have hdvd:d∣(n - m₀):=Nat.dvd_sub hn.2 hm₀_mem.2
   rcases hdvd with ⟨k,hk⟩
   simp only [mim,mrng]
   have hdk:d*k=k*d:=mcom d k
   refine ⟨k,?_,?_⟩
   ·
    have hkd:k*d<=h:=by
     have:n - m₀<=h:=by omega
     nlinarith
    have hk_le:k<=h/d:=(ldim hd).mpr hkd
    omega
   · omega
  calc
   ((Ioc a (a+h)).filter (fun n => d∣n)).card
    <= ((range (h/d+1)).image (fun k => m₀+k*d)).card:=clc hsub
   _<=(range (h/d+1)).card:=card_image_le
   _=h/d+1:=card_range _
 ·
  rw [not_nonempty_iff_eq_empty.mp hemp,card_empty]
  exact Nat.zero_le _
lemma cm_icc (N d:ℕ) (hd:0 < d) :
  ((Icc 1 N).filter (fun n => d∣n)).card<=N/d:=by
 have hsub:(Icc 1 N).filter (fun n => d∣n) ⊆
   (Icc 1 (N/d)).image (fun k => d*k):=by
  intro n hn
  simp only [mf,micc] at hn
  simp only [mim,micc]
  rcases hn.2 with ⟨k,rfl⟩
  refine ⟨k,⟨?_,?_⟩,rfl⟩
  ·
   by_contra hk;push Not at hk
   have hk0:k=0:=by omega
   subst hk0;simp at hn
  · exact (ldim hd).mpr (by rw [mcom];exact hn.1.2)
 calc
  ((Icc 1 N).filter (fun n => d∣n)).card
   <= ((Icc 1 (N/d)).image (fun k => d*k)).card:=clc hsub
  _<=(Icc 1 (N/d)).card:=card_image_le
  _=N/d:=by simp
lemma np_cop {α:Type*} [DecidableEq α] {s:Finset α} {f:α->ℕ} {n:ℕ}
  (hcop:∀ a∈s,∀ b∈s,a≠b->Nat.Coprime (f a) (f b))
  (hdvd:∀ a∈s,f a∣n):(∏ a∈s,f a)∣n:=by
 induction s using Finset.induction_on with
 | empty => simp
 | insert a s ha ih =>
  rw [Finset.prod_insert ha]
  have h1:f a∣n:=hdvd a (mem_insert_self a s)
  have h2:(∏ b∈s,f b)∣n:=ih (fun x hx y hy hne => hcop x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hne)
     (fun x hx => hdvd x (mem_insert_of_mem hx))
  have hc:Nat.Coprime (f a) (∏ b∈s,f b):=Nat.Coprime.prod_right (fun b hb => hcop a (mem_insert_self a s) b (mem_insert_of_mem hb)
    (fun h => ha (h ▸ hb)))
  exact hc.mul_dvd_of_dvd_of_dvd h1 h2
lemma ch_dy (k:ℕ) (_hk:1<=k) :
  ((Ioc (2^k) (2^(k+1))).filter Nat.Prime).card*k<=2*2^k:=by
 let S:=(Ioc (2^k) (2^(k+1))).filter Nat.Prime
 have hcop:∀ p∈S,∀ q∈S,p≠q->Nat.Coprime p q:=by
  intro p hp q hq hne
  exact (Nat.coprime_primes (mf.mp hp).2 (mf.mp hq).2).mpr hne
 have hdvd_each:∀ p∈S,p∣Nat.choose (2*2^k) (2^k):=by
  intro p hp
  simp only [S,mf,mioc] at hp
  have h2:2^(k+1)=2*2^k:=by rw [pow_succ];ring
  rw [h2] at hp
  have hlt:2^k < p:=hp.1.1
  have hle:p<=2*2^k:=hp.1.2
  have hpr:p.Prime:=hp.2
  have hmul:Nat.choose (2*2^k) (2^k)*(2^k).factorial*(2^k).factorial=(2*2^k).factorial:=by
   have h:=Nat.choose_mul_factorial_mul_factorial (show 2^k<=2*2^k by omega)
   have hsub:2*2^k - 2^k=2^k:=by omega
   rw [hsub] at h
   exact h
  have hdvd_num:p∣(2*2^k).factorial:=hpr.dvd_factorial.mpr hle
  have hndvd_den:¬ p∣(2^k).factorial:=by
   intro hd
   have:=hpr.dvd_factorial.mp hd
   omega
  rw [← hmul] at hdvd_num
  rcases hpr.dvd_mul.mp hdvd_num with h1 | h2'
  ·
   rcases hpr.dvd_mul.mp h1 with h3 | h4
   · exact h3
   · exact absurd h4 hndvd_den
  · exact absurd h2' hndvd_den
 have hprod_dvd:∏ p∈S,p∣Nat.choose (2*2^k) (2^k):=np_cop hcop hdvd_each
 have hchoose_pos:0 < Nat.choose (2*2^k) (2^k):=Nat.choose_pos (by omega)
 have hchoose_le:Nat.choose (2*2^k) (2^k)<=2^(2*2^k):=by
  have hsum:=Nat.sum_range_choose (2*2^k)
  have hmem:2^k∈range (2*2^k+1):=by
   simp only [mrng];omega
  exact ltr (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem) hsum.le
 have hprod_le:∏ p∈S,p<=2^(2*2^k):=ltr (Nat.le_of_dvd hchoose_pos hprod_dvd) hchoose_le
 have hprod_ge:(2^k)^S.card<=∏ p∈S,p:=by
  calc
   (2^k)^S.card=∏ _p∈S,2^k:=by rw [prod_const]
   _<=∏ p∈S,p:=by
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro p hp
    simp only [S,mf,mioc] at hp
    exact lol hp.1.1
 have hpow_le:2^(k*S.card)<=2^(2*2^k):=by
  rw [pmul]
  exact ltr hprod_ge hprod_le
 have hle:=(Nat.pow_le_pow_iff_right (by omega:1 < 2)).mp hpow_le
 linarith
lemma ch_cnt (N:ℕ) (hN:16<=N) :
  (((Icc 1 N).filter Nat.Prime).card:ℝ)<=18*(N:ℝ)/(Nat.log 2 N:ℝ):=by
 let m:=Nat.log 2 N
 have hm4:4<=m:=by
  change 4<=Nat.log 2 N
  exact llp (by omega) (by omega:2^4<=N)
 have h2m_le:2^m<=N:=pls 2 (by omega)
 let k0:=m/2
 have hk0_ge:2<=k0:=by omega
 have hsub:(Icc 1 N).filter Nat.Prime ⊆
   Icc 1 (2^k0) ∪
    (Ico k0 (m+1)).biUnion (fun k => (Ioc (2^k) (2^(k+1))).filter Nat.Prime):=by
  intro p hp
  simp only [mf,micc] at hp
  by_cases hle:p<=2^k0
  · exact mem_union_left _ (micc.mpr ⟨hp.1.1,hle⟩)
  ·
   apply mem_union_right
   simp only [mbu,mico,mf,mioc]
   refine ⟨Nat.log 2 p,⟨?_,?_⟩,⟨?_,?_⟩,hp.2⟩
   ·
    have:2^k0 < p:=by omega
    exact llp (by omega) (lol this)
   ·
    have:Nat.log 2 p<=m:=lmr hp.1.2
    omega
   ·
    have h1:2^Nat.log 2 p<=p:=pls 2 (by omega)
    have hne:p≠2^Nat.log 2 p:=by
     intro heq
     have hlog1:2<=Nat.log 2 p:=by
      have:2^k0 < p:=by omega
      have:=llp (by omega) (lol this)
      omega
     have h2dvd:2∣p:=by
      rw [heq]
      exact dvd_pow_self 2 (by omega)
     have h4le:4<=p:=by
      rw [heq]
      have:2^2<=2^Nat.log 2 p:=npr (by omega) hlog1
      omega
     rcases hp.2.eq_two_or_odd with rfl | hodd
     · omega
     · omega
    omega
   · exact lol (lsl (by omega) p)
 have hcard_le:((Icc 1 N).filter Nat.Prime).card<=2^k0+∑ k∈Ico k0 (m+1),((Ioc (2^k) (2^(k+1))).filter Nat.Prime).card:=by
  calc
   ((Icc 1 N).filter Nat.Prime).card
    <= (Icc 1 (2^k0) ∪
      (Ico k0 (m+1)).biUnion
       (fun k => (Ioc (2^k) (2^(k+1))).filter Nat.Prime)).card:=clc hsub
   _<=(Icc 1 (2^k0)).card+((Ico k0 (m+1)).biUnion
       (fun k => (Ioc (2^k) (2^(k+1))).filter Nat.Prime)).card:=cul _ _
   _<=2^k0+∑ k∈Ico k0 (m+1),((Ioc (2^k) (2^(k+1))).filter Nat.Prime).card:=by
     have h1:(Icc 1 (2^k0)).card=2^k0:=by simp
     rw [h1]
     exact Nat.add_le_add_left cbi _
 have hsum_bound:(∑ k∈Ico k0 (m+1),(((Ioc (2^k) (2^(k+1))).filter Nat.Prime).card:ℝ))<=(2:ℝ)*((2^(m+1):ℕ):ℝ)/(k0:ℝ):=by
  have hk0_pos:(0:ℝ) < (k0:ℝ):=by exact_mod_cast (by omega:0 < k0)
  calc
   ∑ k∈Ico k0 (m+1),(((Ioc (2^k) (2^(k+1))).filter Nat.Prime).card:ℝ)
    <= ∑ k∈Ico k0 (m+1),(2*((2^k:ℕ):ℝ))/(k0:ℝ):=by
     apply sls
     intro k hk
     simp only [mico] at hk
     have hch:=ch_dy k (by omega)
     have hchR:(((Ioc (2^k) (2^(k+1))).filter Nat.Prime).card:ℝ)*(k:ℝ)<=2*((2^k:ℕ):ℝ):=by exact_mod_cast hch
     have hk_le:(k0:ℝ)<=(k:ℝ):=by exact_mod_cast hk.1
     rw [ldi hk0_pos]
     nlinarith
   _=(2/(k0:ℝ))*∑ k∈Ico k0 (m+1),((2^k:ℕ):ℝ):=by
     rw [mul_sum]
     apply sum_congr rfl
     intro k _
     ring
   _<=(2/(k0:ℝ))*((2^(m+1):ℕ):ℝ):=by
     apply ml _ (by positivity)
     have hgeo:∀ n:ℕ,∑ k∈range n,2^k=2^n - 1:=by
      intro n
      induction n with
      | zero => simp
      | succ r ihr =>
       rw [sum_range_succ,ihr,pow_succ]
       have:1<=2^r:=Nat.one_le_two_pow
       omega
     have hsub2:Ico k0 (m+1)⊆range (m+1):=by
      intro x hx;simp only [mico] at hx;simp only [mrng];omega
     have hnat:∑ k∈Ico k0 (m+1),2^k<=2^(m+1):=by
      calc
       ∑ k∈Ico k0 (m+1),2^k
        <= ∑ k∈range (m+1),2^k:=sum_le_sum_of_subset hsub2
       _=2^(m+1) - 1:=hgeo (m+1)
       _<=2^(m+1):=Nat.sub_le _ _
     exact_mod_cast hnat
   _=2*((2^(m+1):ℕ):ℝ)/(k0:ℝ):=by ring
 have hm_pos:(0:ℝ) < (m:ℝ):=by exact_mod_cast (by omega:0 < m)
 have hk0_pos:(0:ℝ) < (k0:ℝ):=by exact_mod_cast (by omega:0 < k0)
 have h2mR:((2^m:ℕ):ℝ)<=(N:ℝ):=by exact_mod_cast h2m_le
 have h2m1R:((2^(m+1):ℕ):ℝ)<=2*(N:ℝ):=by
  have hnat:2^(m+1)<=2*N:=by rw [pow_succ];omega
  exact_mod_cast hnat
 have hk0_ge_m:(m:ℝ)<=3*(k0:ℝ):=by
  have:m<=3*k0:=by omega
  exact_mod_cast this
 have hsmall:((2^k0:ℕ):ℝ)*(m:ℝ)<=2*((2^m:ℕ):ℝ):=by
  have hnat:2^k0*m<=2*2^m:=by
   have hdiff:2<=m - k0:=by omega
   have hpow_m:m<=2^(m - k0+1):=by
    have hstep:∀ t:ℕ,2<=t->2*t+1<=2^(t+1):=by
     intro t ht
     induction t with
     | zero => omega
     | succ r ihr =>
      by_cases hr:2<=r
      ·
       have:=ihr hr
       rw [pow_succ]
       omega
      ·
       have:r=1:=by omega
       subst this;norm_num
    have h1:=hstep (m - k0) hdiff
    omega
   calc
    2^k0*m<=2^k0*2^(m - k0+1):=nml _ hpow_m
    _=2^(k0+(m - k0+1)):=(padd 2 _ _).symm
    _=2^(m+1):=by congr 1;omega
    _=2*2^m:=by rw [pow_succ];ring
  exact_mod_cast hnat
 have hcast:(((Icc 1 N).filter Nat.Prime).card:ℝ)<=((2^k0:ℕ):ℝ)+∑ k∈Ico k0 (m+1),(((Ioc (2^k) (2^(k+1))).filter Nat.Prime).card:ℝ):=by
  exact_mod_cast hcard_le
 rw [ldi hm_pos]
 have hterm2:(2*((2^(m+1):ℕ):ℝ)/(k0:ℝ))*(m:ℝ)<=12*(N:ℝ):=by
  have hdiv:(2*((2^(m+1):ℕ):ℝ)/(k0:ℝ))*(m:ℝ)=2*((2^(m+1):ℕ):ℝ)*((m:ℝ)/(k0:ℝ)):=by ring
  rw [hdiv]
  have hmk:(m:ℝ)/(k0:ℝ)<=3:=(dli hk0_pos).mpr (by linarith)
  nlinarith
 have hcomb:(((Icc 1 N).filter Nat.Prime).card:ℝ)*(m:ℝ)<=((2^k0:ℕ):ℝ)*(m:ℝ)+(2*((2^(m+1):ℕ):ℝ)/(k0:ℝ))*(m:ℝ):=by
  nlinarith [hcast,hsum_bound]
 linarith
lemma sp_dy (P:ℕ) (hP:16<=P) :
  ∑ p∈(Ioc P (2*P)).filter Nat.Prime,(1:ℝ)/(p:ℝ)^2<=36/((P:ℝ)*(Nat.log 2 P:ℝ)):=by
 have hPpos:(0:ℝ) < (P:ℝ):=by exact_mod_cast (by omega:0 < P)
 have hlog_ge:4<=Nat.log 2 P:=llp (by omega) (by omega:2^4<=P)
 have hlog_pos:(0:ℝ) < (Nat.log 2 P:ℝ):=by exact_mod_cast (by omega:0 < Nat.log 2 P)
 have hsub:(Ioc P (2*P)).filter Nat.Prime⊆(Icc 1 (2*P)).filter Nat.Prime:=by
  intro p hp;simp only [mf,mioc,micc] at hp ⊢;exact ⟨⟨by omega,hp.1.2⟩,hp.2⟩
 have hch:=ch_cnt (2*P) (by omega)
 have hlog2P:Nat.log 2 P<=Nat.log 2 (2*P):=lmr (by omega)
 have hlog2PR:(Nat.log 2 P:ℝ)<=(Nat.log 2 (2*P):ℝ):=by exact_mod_cast hlog2P
 calc
  ∑ p∈(Ioc P (2*P)).filter Nat.Prime,(1:ℝ)/(p:ℝ)^2
   <= ∑ _p∈(Ioc P (2*P)).filter Nat.Prime,(1:ℝ)/(P:ℝ)^2:=by
    apply sls
    intro p hp
    simp only [mf,mioc] at hp
    have hpR:(P:ℝ)<=(p:ℝ):=by exact_mod_cast lol hp.1.1
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  _=(((Ioc P (2*P)).filter Nat.Prime).card:ℝ)/(P:ℝ)^2:=by
    rw [sum_const,nsmul_eq_mul];ring
  _<=(((Icc 1 (2*P)).filter Nat.Prime).card:ℝ)/(P:ℝ)^2:=by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast clc hsub
  _<=(18*((2*P:ℕ):ℝ)/(Nat.log 2 (2*P):ℝ))/(P:ℝ)^2:=by
    exact div_le_div_of_nonneg_right hch (by positivity)
  _<=(18*(2*(P:ℝ))/(Nat.log 2 P:ℝ))/(P:ℝ)^2:=by
    apply div_le_div_of_nonneg_right _ (by positivity)
    push_cast
    exact div_le_div_of_nonneg_left (by positivity) hlog_pos hlog2PR
  _=36/((P:ℝ)*(Nat.log 2 P:ℝ)):=by
    field_simp
    ring
lemma pps_sub {S:Finset ℕ} (hS:∀ p∈S,p.Prime)
  {j:ℕ->ℕ} {m₁ m₂:ℕ} (hle:m₁<=m₂)
  (h₁:∀ p∈S,p^2∣m₁+j p) (h₂:∀ p∈S,p^2∣m₂+j p) :
  (∏ p∈S,p^2)∣(m₂ - m₁):=by
 refine np_cop ?_ ?_
 ·
  intro p hp q hq hne
  have hcop:Nat.Coprime p q:=(Nat.coprime_primes (hS p hp) (hS q hq)).mpr hne
  exact (hcop.pow_left 2).pow_right 2
 ·
  intro p hp
  have hd:p^2∣(m₂+j p) - (m₁+j p):=Nat.dvd_sub (h₂ p hp) (h₁ p hp)
  have hsub:(m₂+j p) - (m₁+j p)=m₂ - m₁:=by omega
  rwa [hsub] at hd
lemma crt_sq (Y:ℕ) (S:Finset ℕ) (hS:∀ p∈S,p.Prime) (j:ℕ->ℕ) :
  ((Icc 1 Y).filter (fun m => ∀ p∈S,p^2∣m+j p)).card<=Y/(∏ p∈S,p^2)+1:=by
 let D:=∏ p∈S,p^2
 have hDpos:0 < D:=Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos 2)
 let F:=(Icc 1 Y).filter (fun m => ∀ p∈S,p^2∣m+j p)
 change F.card<=Y/D+1
 by_cases hemp:F.Nonempty
 ·
  let m₀:=F.min' hemp
  have hm₀:m₀∈F:=min'_mem F hemp
  have hm₀_prop:∀ p∈S,p^2∣m₀+j p:=(mf.mp hm₀).2
  have hm₀_ge:1<=m₀:=(micc.mp (mf.mp hm₀).1).1
  have hsub:F⊆(range (Y/D+1)).image (fun k => m₀+k*D):=by
   intro m hm
   have hle:m₀<=m:=min'_le F m hm
   have hm_le:m<=Y:=(micc.mp (mf.mp hm).1).2
   have hm_prop:∀ p∈S,p^2∣m+j p:=(mf.mp hm).2
   have hdvd:D∣(m - m₀):=pps_sub hS hle hm₀_prop hm_prop
   rcases hdvd with ⟨k,hk⟩
   have hcomm:D*k=k*D:=mcom D k
   simp only [mim,mrng]
   refine ⟨k,?_,?_⟩
   ·
    have hkd:k*D<=Y:=by omega
    have hk_le:k<=Y/D:=(ldim hDpos).mpr hkd
    omega
   · omega
  calc
   F.card<=((range (Y/D+1)).image (fun k => m₀+k*D)).card:=clc hsub
   _<=(range (Y/D+1)).card:=card_image_le
   _=Y/D+1:=card_range _
 ·
  rw [not_nonempty_iff_eq_empty.mp hemp,card_empty]
  exact Nat.zero_le _
def isGood (T:Finset ℕ) (m:ℕ):Prop:=∀ j∈T,Squarefree (m+j)
def isGoodP (P:ℕ) (T:Finset ℕ) (m:ℕ):Prop:=∀ j∈T,∀ p∈(Icc 1 P).filter Nat.Prime,¬ p^2∣m+j
noncomputable instance (T:Finset ℕ):DecidablePred (isGood T):=Classical.decPred _
noncomputable instance (P:ℕ) (T:Finset ℕ):DecidablePred (isGoodP P T):=Classical.decPred _
def periodMod (P:ℕ):ℕ:=∏ p∈(Icc 1 P).filter Nat.Prime,p^2
lemma periodMod_pos (P:ℕ):0 < periodMod P:=by
 apply Finset.prod_pos
 intro p hp
 exact pow_pos (mf.mp hp).2.pos 2
lemma isGoodP_periodic (P:ℕ) (T:Finset ℕ) (m k:ℕ) :
  isGoodP P T (m+k*periodMod P)<->isGoodP P T m:=by
 have hdvd_mod:∀ p∈(Icc 1 P).filter Nat.Prime,p^2∣k*periodMod P:=by
  intro p hp
  exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) k
 constructor <;> intro h j hj p hp hd
 ·
  apply h j hj p hp
  have hadd:m+k*periodMod P+j=(m+j)+k*periodMod P:=by ring
  rw [hadd]
  exact dvd_add hd (hdvd_mod p hp)
 ·
  apply h j hj p hp
  have hadd:m+k*periodMod P+j=(m+j)+k*periodMod P:=by ring
  rw [hadd] at hd
  exact (Nat.dvd_add_left (hdvd_mod p hp)).mp hd
lemma cp_icc (M N:ℕ) (hM:0 < M) (P:ℕ->Prop) [DecidablePred P]
  (hper:∀ m k:ℕ,P (m+k*M)<->P m) :
  let c:=((range M).filter P).card
  (N/M)*c<=((Icc 1 N).filter P).card/\((Icc 1 N).filter P).card<=(N/M)*c+M:=by
 intro c
 let q:=N/M
 let r:=N % M
 have hN:N=q*M+r:=(Nat.div_add_mod N M).symm.trans (by ring)
 have hr:r < M:=Nat.mod_lt N hM
 have hblock:∀ k:ℕ,((Ico (k*M+1) ((k+1)*M+1)).filter P).card=c:=by
  intro k
  have h1:((Ico (k*M+1) ((k+1)*M+1)).filter P).card=((Icc 1 M).filter P).card:=by
   refine Finset.card_bij (fun x _ => x - k*M) ?_ ?_ ?_
   ·
    intro x hx
    simp only [mf,mico,micc] at hx ⊢
    have hkm:(k+1)*M=k*M+M:=by ring
    refine ⟨⟨by omega,by omega⟩,?_⟩
    have hx_eq:x=(x - k*M)+k*M:=by omega
    rw [hx_eq] at hx
    exact (hper _ k).mp hx.2
   ·
    intro x₁ hx₁ x₂ hx₂ heq
    simp only [mf,mico] at hx₁ hx₂
    omega
   ·
    intro y hy
    simp only [mf,micc] at hy
    have hkm:(k+1)*M=k*M+M:=by ring
    refine ⟨y+k*M,?_,by omega⟩
    simp only [mf,mico]
    exact ⟨⟨by omega,by omega⟩,(hper y k).mpr hy.2⟩
  rw [h1]
  have hM0:P M<->P 0:=by simpa using hper 0 1
  refine Finset.card_bij (fun x _ => if x=M then 0 else x) ?_ ?_ ?_
  ·
   intro x hx
   simp only [mf,micc,mrng] at hx ⊢
   split_ifs with h
   · subst h;exact ⟨hM,hM0.mp hx.2⟩
   · exact ⟨by omega,hx.2⟩
  ·
   intro x₁ hx₁ x₂ hx₂ heq
   simp only [mf,micc] at hx₁ hx₂
   split_ifs at heq with h1' h2' h2' <;> omega
  ·
   intro y hy
   simp only [mf,mrng] at hy
   by_cases hy0:y=0
   ·
    subst hy0
    refine ⟨M,?_,by simp⟩
    simp only [mf,micc]
    exact ⟨⟨hM,le_refl M⟩,hM0.mpr hy.2⟩
   ·
    refine ⟨y,?_,by simp [show y≠M by omega]⟩
    simp only [mf,micc]
    exact ⟨⟨by omega,by omega⟩,hy.2⟩
 have hmain:((Ico 1 (q*M+1)).filter P).card=q*c:=by
  have hunion:Ico 1 (q*M+1)=(range q).biUnion (fun k => Ico (k*M+1) ((k+1)*M+1)):=by
   ext x
   simp only [mico,mbu,mrng]
   constructor
   ·
    intro hx
    refine ⟨(x - 1)/M,?_,?_,?_⟩
    ·
     have:x - 1 < q*M:=by omega
     exact (Nat.div_lt_iff_lt_mul hM).mpr this
    ·
     have:=dls (x - 1) M
     omega
    ·
     have hlt:=lmd (x - 1) hM
     have hcomm:M*((x - 1)/M+1)=((x - 1)/M+1)*M:=mcom _ _
     omega
   ·
    rintro ⟨k,hk,h1,h2⟩
    refine ⟨by omega,?_⟩
    have:(k+1)*M<=q*M:=nmr M hk
    omega
  have hdisj:Set.PairwiseDisjoint (range q:Set ℕ)
    (fun k => (Ico (k*M+1) ((k+1)*M+1)).filter P):=by
   intro k₁ _ k₂ _ hne
   dsimp [Function.onFun]
   rw [disjoint_left]
   intro x hx₁ hx₂
   simp only [mf,mico] at hx₁ hx₂
   rcases lt_or_gt_of_ne hne with hlt | hgt
   ·
    have:(k₁+1)*M<=k₂*M:=nmr M hlt
    omega
   ·
    have:(k₂+1)*M<=k₁*M:=nmr M hgt
    omega
  rw [hunion,Finset.filter_biUnion,card_biUnion hdisj]
  simp only [hblock,sum_const,card_range,smul_eq_mul]
 constructor
 ·
  have hsub:(Ico 1 (q*M+1)).filter P⊆(Icc 1 N).filter P:=by
   intro x hx
   simp only [mf,mico,micc] at hx ⊢
   exact ⟨⟨hx.1.1,by omega⟩,hx.2⟩
  rw [← hmain]
  exact clc hsub
 ·
  have hsub:(Icc 1 N).filter P ⊆
    (Ico 1 (q*M+1)).filter P∪Ico (q*M+1) (N+1):=by
   intro x hx
   simp only [mf,micc,mun,mico] at hx ⊢
   by_cases hlt:x < q*M+1
   · exact Or.inl ⟨⟨hx.1.1,hlt⟩,hx.2⟩
   · exact Or.inr ⟨by omega,by omega⟩
  calc
   ((Icc 1 N).filter P).card
    <= ((Ico 1 (q*M+1)).filter P∪Ico (q*M+1) (N+1)).card:=clc hsub
   _<=((Ico 1 (q*M+1)).filter P).card+(Ico (q*M+1) (N+1)).card:=cul _ _
   _=q*c+(N+1 - (q*M+1)):=by rw [hmain,Nat.card_Ico]
   _<=q*c+M:=by omega
lemma sqf_iff {n:ℕ} :
  Squarefree n<->∀ p:ℕ,p.Prime->¬ p^2∣n:=by
 rw [Nat.squarefree_iff_prime_squarefree]
 constructor
 ·
  intro h p hp hd
  apply h p hp
  simpa [sq] using hd
 ·
  intro h p hp hd
  apply h p hp
  simpa [sq] using hd
lemma isGood_diff_bound (P N:ℕ) (hP:1<=P) (T:Finset ℕ) :
  let Tmax:=T.sup id
  (((Icc 1 N).filter (fun m => isGoodP P T m/\¬ isGood T m)).card:ℝ)<=(T.card:ℝ)*((N+Tmax:ℕ):ℝ)/(P:ℝ):=by
 intro Tmax
 let Bad:=(Icc 1 N).filter (fun m => isGoodP P T m/\¬ isGood T m)
 have hsub:Bad ⊆
   T.biUnion (fun j =>
    ((Ioc P (N+Tmax)).filter Nat.Prime).biUnion (fun p =>
     (Icc 1 N).filter (fun m => p^2∣m+j))):=by
  intro m hm
  simp only [Bad,mf,micc] at hm
  have hnot:¬ ∀ j∈T,Squarefree (m+j):=hm.2.2
  push Not at hnot
  rcases hnot with ⟨j,hj,hnsqf⟩
  rw [sqf_iff] at hnsqf
  push Not at hnsqf
  rcases hnsqf with ⟨p,hp,hdvd⟩
  have hp_gt:P < p:=by
   by_contra hle
   push Not at hle
   exact hm.2.1 j hj p (mf.mpr ⟨micc.mpr ⟨hp.one_lt.le,hle⟩,hp⟩) hdvd
  have hj_le:j<=Tmax:=le_sup (f:=id) hj
  have hp_le:p<=N+Tmax:=by
   have hp2_le:p^2<=m+j:=Nat.le_of_dvd (by omega) hdvd
   have hp_le_sq:p<=p^2:=by nlinarith [hp.one_lt]
   omega
  simp only [mbu,mf,mioc,micc]
  exact ⟨j,hj,p,⟨⟨hp_gt,hp_le⟩,hp⟩,⟨hm.1,hdvd⟩⟩
 have hcard_inner:∀ j∈T,∀ p∈(Ioc P (N+Tmax)).filter Nat.Prime,((Icc 1 N).filter (fun m => p^2∣m+j)).card<=(N+Tmax)/p^2:=by
  intro j hj p hp
  have hj_le:j<=Tmax:=le_sup (f:=id) hj
  have hp_pos:0 < p^2:=pow_pos (mf.mp hp).2.pos 2
  have himg:((Icc 1 N).filter (fun m => p^2∣m+j)).card<=((Icc 1 (N+Tmax)).filter (fun n => p^2∣n)).card:=by
   refine card_le_card_of_injOn (fun m => m+j) ?_ ?_
   ·
    intro m hm
    rw [mem_coe,mf,micc] at hm
    rw [mem_coe,mf,micc]
    dsimp only
    exact ⟨⟨by omega,by omega⟩,hm.2⟩
   ·
    intro m₁ _ m₂ _ h
    dsimp at h
    omega
  exact ltr himg (cm_icc (N+Tmax) (p^2) hp_pos)
 have hnat:Bad.card<=∑ j∈T,∑ p∈(Ioc P (N+Tmax)).filter Nat.Prime,(N+Tmax)/p^2:=by
  calc
   Bad.card<=(T.biUnion (fun j =>
     ((Ioc P (N+Tmax)).filter Nat.Prime).biUnion (fun p =>
      (Icc 1 N).filter (fun m => p^2∣m+j)))).card:=clc hsub
   _<=∑ j∈T,(((Ioc P (N+Tmax)).filter Nat.Prime).biUnion (fun p =>
      (Icc 1 N).filter (fun m => p^2∣m+j))).card:=cbi
   _<=∑ j∈T,∑ p∈(Ioc P (N+Tmax)).filter Nat.Prime,((Icc 1 N).filter (fun m => p^2∣m+j)).card:=sls (fun _ _ => cbi)
   _<=∑ j∈T,∑ p∈(Ioc P (N+Tmax)).filter Nat.Prime,(N+Tmax)/p^2:=sls (fun j hj => sls (fun p hp => hcard_inner j hj p hp))
 have hcast:(Bad.card:ℝ)<=∑ _j∈T,∑ p∈(Ioc P (N+Tmax)).filter Nat.Prime,(((N+Tmax)/p^2:ℕ):ℝ):=by exact_mod_cast hnat
 calc
  (Bad.card:ℝ)
   <= ∑ _j∈T,∑ p∈(Ioc P (N+Tmax)).filter Nat.Prime,((N+Tmax:ℕ):ℝ)/(p:ℝ)^2:=by
    refine ltr hcast (sls fun _ _ => sls fun p hp => ?_)
    have hp_pos:(0:ℝ) < (p:ℝ)^2:=by
     exact_mod_cast pow_pos (mf.mp hp).2.pos 2
    rw [ldi hp_pos]
    exact_mod_cast dls (N+Tmax) (p^2)
  _<=∑ _j∈T,((N+Tmax:ℕ):ℝ)*(1/(P:ℝ)):=by
    apply sls
    intro _ _
    have h1:∑ p∈(Ioc P (N+Tmax)).filter Nat.Prime,((N+Tmax:ℕ):ℝ)/(p:ℝ)^2=((N+Tmax:ℕ):ℝ)*∑ p∈(Ioc P (N+Tmax)).filter Nat.Prime,(1:ℝ)/(p:ℝ)^2:=by
     rw [mul_sum]
     apply sum_congr rfl;intro p _;ring
    rw [h1]
    apply ml _ (by positivity)
    calc
     ∑ p∈(Ioc P (N+Tmax)).filter Nat.Prime,(1:ℝ)/(p:ℝ)^2
      <= ∑ n∈Ioc P (N+Tmax),(1:ℝ)/(n:ℝ)^2:=ssub (fsub _ _) (fun _ _ _ => by positivity)
     _<=1/(P:ℝ):=sum_inv_sq_Ioc_le P (N+Tmax) hP
  _=(T.card:ℝ)*((N+Tmax:ℕ):ℝ)/(P:ℝ):=by
    rw [sum_const,nsmul_eq_mul];ring
lemma tendsto_isGood_density (T:Finset ℕ) :
  ∃ c:ℝ,Tendsto (fun x:ℝ => (1/x)*(((Icc 1 ⌊x⌋₊).filter (isGood T)).card:ℝ))
   atTop (𝓝 c):=by
 let f (x:ℝ):=(1/x)*(((Icc 1 ⌊x⌋₊).filter (isGood T)).card:ℝ)
 apply cauchySeq_tendsto_of_complete
 apply Metric.cauchySeq_iff.mpr
 intro ε hε
 let Tmax:=T.sup id
 obtain ⟨P,hP1,hPε⟩:∃ P:ℕ,1<=P/\(2*(T.card:ℝ)+1)/(P:ℝ) < ε / 4:=by
  obtain ⟨P,hP⟩:=exists_nat_gt ((2*(T.card:ℝ)+1)/(ε / 4))
  refine ⟨max P 1,lmrt _ _,?_⟩
  have hPpos:(0:ℝ) < ((max P 1:ℕ):ℝ):=by positivity
  rw [div_lt_iff₀ hPpos]
  have hle:(P:ℝ)<=((max P 1:ℕ):ℝ):=by exact_mod_cast lml P 1
  have hlt:(2*(T.card:ℝ)+1) < (P:ℝ)*(ε / 4):=(div_lt_iff₀ (by linarith)).mp hP
  nlinarith
 let M:=periodMod P
 have hMpos:0 < M:=periodMod_pos P
 have hMR:(0:ℝ) < (M:ℝ):=by exact_mod_cast hMpos
 let cP:ℝ:=(((range M).filter (isGoodP P T)).card:ℝ)/(M:ℝ)
 have happrox:∀ᶠ x:ℝ in atTop,|f x - cP| < ε / 2:=by
  have hX:∃ X:ℝ,1<=X/\(Tmax:ℝ)<=X/\(2*(M:ℝ)+2)/X < ε / 4:=by
   refine ⟨max (max 1 (Tmax:ℝ)) ((2*(M:ℝ)+2)/(ε / 4)+1),?_,?_,?_⟩
   · exact ltr (lml _ _) (lml _ _)
   · exact ltr (lmrt _ _) (lml _ _)
   ·
    have hpos:(0:ℝ) < max (max 1 (Tmax:ℝ)) ((2*(M:ℝ)+2)/(ε / 4)+1):=lt_of_lt_of_le (by norm_num) (ltr (lml _ _) (lml _ _))
    rw [div_lt_iff₀ hpos]
    have hgt:(2*(M:ℝ)+2)/(ε / 4) < max (max 1 (Tmax:ℝ)) ((2*(M:ℝ)+2)/(ε / 4)+1):=by
     have:=lmrt (max 1 (Tmax:ℝ)) ((2*(M:ℝ)+2)/(ε / 4)+1)
     linarith
    have:=(div_lt_iff₀ (by linarith)).mp hgt
    linarith
  obtain ⟨X,hX1,hXT,hXM⟩:=hX
  filter_upwards [eventually_ge_atTop X] with x hx
  have hxpos:0 < x:=by linarith
  let N:=⌊x⌋₊
  have hNx:(N:ℝ)<=x:=Nat.floor_le (lol hxpos)
  have hxN:x < (N:ℝ)+1:=Nat.lt_floor_add_one x
  have hper:=cp_icc M N hMpos (isGoodP P T) (isGoodP_periodic P T)
  let c0:=((range M).filter (isGoodP P T)).card
  have hc0_le:c0<=M:=by
   calc c0<=(range M).card:=cfl _ _
   _=M:=card_range M
  have hsub_good:(Icc 1 N).filter (isGood T)⊆(Icc 1 N).filter (isGoodP P T):=by
   intro m hm
   simp only [mf] at hm ⊢
   refine ⟨hm.1,fun j hj p hp hd => ?_⟩
   exact sqf_iff.mp (hm.2 j hj) p (mf.mp hp).2 hd
  have hdiff_eq:((Icc 1 N).filter (isGoodP P T)).card -
    ((Icc 1 N).filter (isGood T)).card=((Icc 1 N).filter (fun m => isGoodP P T m/\¬ isGood T m)).card:=by
   have hsdiff:((Icc 1 N).filter (isGoodP P T)) \ ((Icc 1 N).filter (isGood T))=(Icc 1 N).filter (fun m => isGoodP P T m/\¬ isGood T m):=by
    ext m;simp only [Finset.mem_sdiff,mf];tauto
   rw [← card_sdiff_of_subset hsub_good,hsdiff]
  have hdiff_le:(((Icc 1 N).filter (fun m => isGoodP P T m/\¬ isGood T m)).card:ℝ)<=(T.card:ℝ)*((N+Tmax:ℕ):ℝ)/(P:ℝ):=isGood_diff_bound P N hP1 T
  have hcard_le_P:(((Icc 1 N).filter (isGood T)).card:ℝ)<=(((Icc 1 N).filter (isGoodP P T)).card:ℝ):=by
   exact_mod_cast clc hsub_good
  have hcard_ge_P:(((Icc 1 N).filter (isGoodP P T)).card:ℝ) -
    (T.card:ℝ)*((N+Tmax:ℕ):ℝ)/(P:ℝ)<=(((Icc 1 N).filter (isGood T)).card:ℝ):=by
   have hcast:(((Icc 1 N).filter (isGoodP P T)).card:ℝ) -
     (((Icc 1 N).filter (isGood T)).card:ℝ)=(((Icc 1 N).filter (fun m => isGoodP P T m/\¬ isGood T m)).card:ℝ):=by
    have hle':=clc hsub_good
    rw [← hdiff_eq,ncs hle']
   linarith
  have hP_upper:(((Icc 1 N).filter (isGoodP P T)).card:ℝ)<=x*cP+(M:ℝ):=by
   have h1:(((Icc 1 N).filter (isGoodP P T)).card:ℝ)<=((N/M:ℕ):ℝ)*(c0:ℝ)+(M:ℝ):=by exact_mod_cast hper.2
   have h2:((N/M:ℕ):ℝ)*(M:ℝ)<=(N:ℝ):=by
    exact_mod_cast dls N M
   have h3:((N/M:ℕ):ℝ)*(c0:ℝ)<=x*cP:=by
    have hcP:cP=(c0:ℝ)/(M:ℝ):=rfl
    rw [hcP]
    have:((N/M:ℕ):ℝ)<=x/(M:ℝ):=(ldi hMR).mpr (by linarith)
    have h4:((N/M:ℕ):ℝ)*(c0:ℝ)<=(x/(M:ℝ))*(c0:ℝ):=mr this (by positivity)
    have h5:(x/(M:ℝ))*(c0:ℝ)=x*((c0:ℝ)/(M:ℝ)):=by ring
    linarith
   linarith
  have hP_lower:x*cP - (2*(M:ℝ)+1)<=(((Icc 1 N).filter (isGoodP P T)).card:ℝ):=by
   have h1:((N/M:ℕ):ℝ)*(c0:ℝ)<=(((Icc 1 N).filter (isGoodP P T)).card:ℝ):=by exact_mod_cast hper.1
   have h2:(N:ℝ) < ((N/M:ℕ):ℝ)*(M:ℝ)+(M:ℝ):=by
    have:=Nat.div_add_mod N M
    have hmod:=Nat.mod_lt N hMpos
    have hnat:N < (N/M)*M+M:=by nlinarith
    exact_mod_cast hnat
   have hcP_le1:cP<=1:=by
    change (c0:ℝ)/(M:ℝ)<=1
    rw [div_le_one hMR]
    exact_mod_cast hc0_le
   have h3:x - 1 - (M:ℝ)<=((N/M:ℕ):ℝ)*(M:ℝ):=by linarith
   have h4:(x - 1 - (M:ℝ))*cP<=((N/M:ℕ):ℝ)*(c0:ℝ):=by
    have hcP:cP=(c0:ℝ)/(M:ℝ):=rfl
    have hmul:((N/M:ℕ):ℝ)*(M:ℝ)*cP=((N/M:ℕ):ℝ)*(c0:ℝ):=by
     rw [hcP];field_simp
    rw [← hmul]
    exact mr h3 (by positivity)
   have h5:(1+(M:ℝ))*cP<=1+(M:ℝ):=by nlinarith
   linarith
  have htail_x:(T.card:ℝ)*((N+Tmax:ℕ):ℝ)/(P:ℝ)<=x*((2*(T.card:ℝ)+1)/(P:ℝ)):=by
   have hNT:((N+Tmax:ℕ):ℝ)<=2*x:=by push_cast;linarith
   have hPpos:(0:ℝ) < (P:ℝ):=by exact_mod_cast (by omega:0 < P)
   rw [dli hPpos]
   have:x*((2*(T.card:ℝ)+1)/(P:ℝ))*(P:ℝ)=x*(2*(T.card:ℝ)+1):=by
    field_simp
   rw [this]
   nlinarith
  have hf_upper:f x - cP<=(2*(M:ℝ)+2)/x:=by
   show (1/x)*(((Icc 1 N).filter (isGood T)).card:ℝ) - cP<=_
   have h1:(((Icc 1 N).filter (isGood T)).card:ℝ)<=x*cP+(2*(M:ℝ)+2):=by
    linarith
   have h2:(1/x)*(((Icc 1 N).filter (isGood T)).card:ℝ)<=(1/x)*(x*cP+(2*(M:ℝ)+2)):=ml h1 (by positivity)
   have h3:(1/x)*(x*cP+(2*(M:ℝ)+2))=cP+(2*(M:ℝ)+2)/x:=by
    field_simp
   linarith
  have hf_lower:cP - f x<=(2*(M:ℝ)+2)/x+(2*(T.card:ℝ)+1)/(P:ℝ):=by
   show cP - (1/x)*(((Icc 1 N).filter (isGood T)).card:ℝ)<=_
   have h1:x*cP - (2*(M:ℝ)+2) - x*((2*(T.card:ℝ)+1)/(P:ℝ))<=(((Icc 1 N).filter (isGood T)).card:ℝ):=by
    linarith
   have h2:(1/x)*(x*cP - (2*(M:ℝ)+2) - x*((2*(T.card:ℝ)+1)/(P:ℝ)))<=(1/x)*(((Icc 1 N).filter (isGood T)).card:ℝ):=ml h1 (by positivity)
   have h3:(1/x)*(x*cP - (2*(M:ℝ)+2) - x*((2*(T.card:ℝ)+1)/(P:ℝ)))=cP - (2*(M:ℝ)+2)/x - (2*(T.card:ℝ)+1)/(P:ℝ):=by
    field_simp
   linarith
  have hMx:(2*(M:ℝ)+2)/x < ε / 4:=lt_of_le_of_lt (div_le_div_of_nonneg_left (by positivity) (by linarith) hx) hXM
  rw [abs_lt]
  constructor <;> linarith
 obtain ⟨X₀,hX₀⟩:=eventually_atTop.mp happrox
 refine ⟨X₀,fun x hx y hy => ?_⟩
 have h1:=hX₀ x hx
 have h2:=hX₀ y hy
 rw [Real.dist_eq]
 rw [abs_lt] at h1 h2 ⊢
 constructor <;> linarith
lemma nth_add {n k:ℕ} (hk:1<=k) :
  s (n+1) - s n=k <->
   Squarefree (s n+k)/\∀ j∈Ioo 0 k,¬ Squarefree (s n+j):=by
 have hmono:StrictMono s:=Nat.nth_strictMono Nat.squarefree_infinite
 have hlt:s n < s (n+1):=hmono (Nat.lt_succ_self n)
 have hsqf_succ:Squarefree (s (n+1)):=Nat.nth_mem_of_infinite Nat.squarefree_infinite (n+1)
 have hbetween:∀ m:ℕ,s n < m->m < s (n+1)->¬ Squarefree m:=by
  intro m hm1 hm2 hsq
  let idx:=Nat.count Squarefree m
  have hidx_eq:s idx=m:=Nat.nth_count hsq
  have hlt1:n < idx:=by
   by_contra hle;push Not at hle
   have:s idx<=s n:=hmono.monotone hle
   omega
  have hlt2:idx < n+1:=by
   by_contra hle;push Not at hle
   have:s (n+1)<=s idx:=hmono.monotone hle
   omega
  omega
 constructor
 ·
  intro heq
  have hadd:s (n+1)=s n+k:=by omega
  refine ⟨by rwa [← hadd],fun j hj => ?_⟩
  simp only [mem_Ioo] at hj
  exact hbetween (s n+j) (by omega) (by omega)
 ·
  rintro ⟨hsq,hno⟩
  have hle:s (n+1)<=s n+k:=by
   let idx:=Nat.count Squarefree (s n+k)
   have hidx_eq:s idx=s n+k:=Nat.nth_count hsq
   have hlt1:n < idx:=by
    by_contra hle';push Not at hle'
    have:s idx<=s n:=hmono.monotone hle'
    omega
   have:s (n+1)<=s idx:=hmono.monotone hlt1
   omega
  have hge:s n+k<=s (n+1):=by
   by_contra hlt'
   push Not at hlt'
   have hj:s (n+1) - s n∈Ioo 0 k:=by
    simp only [mem_Ioo];omega
   have hns:=hno (s (n+1) - s n) hj
   have hrew:s n+(s (n+1) - s n)=s (n+1):=by omega
   rw [hrew] at hns
   exact hns hsqf_succ
  omega
lemma fixed_gap_density (k:ℕ) :
  ∃ d:ℝ,Tendsto (fun x:ℝ => (1/x)*(((A x).filter (fun n => s (n+1) - s n=k)).card:ℝ))
   atTop (𝓝 d):=by
 by_cases hk0:k=0
 ·
  subst hk0
  refine ⟨0,?_⟩
  have hemp (x:ℝ):(A x).filter (fun n => s (n+1) - s n=0)=∅:=by
   ext n
   simp only [mf,notMem_empty,iff_false,not_and]
   intro _
   have hlt:s n < s (n+1):=(Nat.nth_strictMono Nat.squarefree_infinite) (Nat.lt_succ_self n)
   omega
  simp [hemp]
 have hk1:1<=k:=by omega
 let I:=Ioo 0 k
 have hcount_eq (x:ℝ) :
   (((A x).filter (fun n => s (n+1) - s n=k)).card:ℝ)=∑ U∈I.powerset,(-1:ℝ)^U.card*(((Icc 1 ⌊x⌋₊).filter (isGood (insert 0 (insert k U)))).card:ℝ):=by
  have hbij:((A x).filter (fun n => s (n+1) - s n=k)).card=((Icc 1 ⌊x⌋₊).filter (fun m =>
     Squarefree m/\Squarefree (m+k)/\∀ j∈I,¬ Squarefree (m+j))).card:=by
   refine Finset.card_bij (fun n _ => s n) ?_ ?_ ?_
   ·
    intro n hn
    simp only [mf,A,mem_preimage,micc] at hn ⊢
    have hsqn:Squarefree (s n):=Nat.nth_mem_of_infinite Nat.squarefree_infinite n
    have hpos:1<=s n:=by
     by_contra h0;push Not at h0
     have:s n=0:=by omega
     rw [this] at hsqn
     exact not_squarefree_zero hsqn
    have hsucc:=(nth_add hk1).mp hn.2
    exact ⟨⟨hpos,hn.1.2⟩,hsqn,hsucc.1,hsucc.2⟩
   ·
    intro n₁ _ n₂ _ heq
    exact Nat.nth_injective Nat.squarefree_infinite heq
   ·
    intro m hm
    simp only [mf,micc] at hm
    let n:=Nat.count Squarefree m
    have hsn:s n=m:=Nat.nth_count hm.2.1
    refine ⟨n,?_,hsn⟩
    simp only [mf,A,mem_preimage,micc]
    refine ⟨⟨Nat.zero_le _,by omega⟩,?_⟩
    rw [nth_add hk1,hsn]
    exact ⟨hm.2.2.1,hm.2.2.2⟩
  rw [hbij]
  have hIE:∀ m∈Icc 1 ⌊x⌋₊,(if Squarefree m/\Squarefree (m+k)/\∀ j∈I,¬ Squarefree (m+j) then (1:ℝ) else 0)=∑ U∈I.powerset,(-1:ℝ)^U.card*(if isGood (insert 0 (insert k U)) m then (1:ℝ) else 0):=by
   intro m _
   by_cases h0k:Squarefree m/\Squarefree (m+k)
   ·
    let J:=I.filter (fun j => Squarefree (m+j))
    have hfilter_eq:∀ U∈I.powerset,(if isGood (insert 0 (insert k U)) m then (1:ℝ) else 0)=if U⊆J then 1 else 0:=by
     intro U hU
     have hiff:isGood (insert 0 (insert k U)) m<->U⊆J:=by
      simp only [isGood,mem_insert,forall_eq_or_imp,add_zero,J,subset_iff,mf]
      constructor
      ·
       rintro ⟨_,_,hall⟩ j hj
       exact ⟨(mem_powerset.mp hU) hj,hall j hj⟩
      ·
       intro hsub'
       exact ⟨h0k.1,h0k.2,fun j hj => (hsub' hj).2⟩
     by_cases h:U⊆J <;> simp [hiff,h]
    have hsum_J:∑ U∈I.powerset,(-1:ℝ)^U.card*(if isGood (insert 0 (insert k U)) m then (1:ℝ) else 0)=∑ U∈J.powerset,(-1:ℝ)^U.card:=by
     rw [sum_congr rfl (fun U hU => by rw [hfilter_eq U hU])]
     have hsub_pow:J.powerset⊆I.powerset:=powerset_mono.mpr (fsub _ _)
     rw [← sum_subset hsub_pow]
     ·
      apply sum_congr rfl
      intro U hU
      simp [mem_powerset.mp hU]
     ·
      intro U _ hUnot
      simp [mem_powerset.not.mp hUnot]
    rw [hsum_J]
    have hJemp:(∀ j∈I,¬ Squarefree (m+j))<->J=∅:=by
     simp only [J,filter_eq_empty_iff]
    have hpow_id:∑ U∈J.powerset,(-1:ℝ)^U.card=if J=∅ then 1 else 0:=by
     have hZ:∑ U∈J.powerset,(-1:ℤ)^U.card=if J=∅ then 1 else 0:=sum_powerset_neg_one_pow_card
     have hcast:(∑ U∈J.powerset,(-1:ℝ)^U.card)=((∑ U∈J.powerset,(-1:ℤ)^U.card:ℤ):ℝ):=by push_cast;rfl
     rw [hcast,hZ]
     split_ifs <;> simp
    rw [hpow_id]
    by_cases hJ:J=∅
    ·
     have hall:∀ j∈I,¬ Squarefree (m+j):=hJemp.mpr hJ
     rw [if_pos ⟨h0k.1,h0k.2,hall⟩,if_pos hJ]
    ·
     have hnotall:¬ ∀ j∈I,¬ Squarefree (m+j):=fun h => hJ (hJemp.mp h)
     rw [if_neg (fun h => hnotall h.2.2),if_neg hJ]
   ·
    have hnotgood:∀ U∈I.powerset,¬ isGood (insert 0 (insert k U)) m:=by
     intro U _ hg
     apply h0k
     exact ⟨by simpa using hg 0 (by simp),hg k (by simp)⟩
    have hnotlhs:¬ (Squarefree m/\Squarefree (m+k)/\∀ j∈I,¬ Squarefree (m+j)):=by
     tauto
    rw [if_neg hnotlhs]
    symm
    apply Finset.sum_eq_zero
    intro U hU
    simp [hnotgood U hU]
  have hcard_sum:(((Icc 1 ⌊x⌋₊).filter (fun m =>
    Squarefree m/\Squarefree (m+k)/\∀ j∈I,¬ Squarefree (m+j))).card:ℝ)=∑ m∈Icc 1 ⌊x⌋₊,if Squarefree m/\Squarefree (m+k)/\∀ j∈I,¬ Squarefree (m+j) then (1:ℝ) else 0:=by
   rw [Finset.sum_boole]
  rw [hcard_sum,sum_congr rfl hIE,sum_comm]
  apply sum_congr rfl
  intro U _
  rw [← mul_sum,Finset.sum_boole]
 choose c hc using (fun U:Finset ℕ => tendsto_isGood_density (insert 0 (insert k U)))
 refine ⟨∑ U∈I.powerset,(-1:ℝ)^U.card*c U,?_⟩
 have htend:Tendsto (fun x:ℝ => ∑ U∈I.powerset,(-1:ℝ)^U.card*((1/x)*(((Icc 1 ⌊x⌋₊).filter (isGood (insert 0 (insert k U)))).card:ℝ)))
   atTop (𝓝 (∑ U∈I.powerset,(-1:ℝ)^U.card*c U)):=tendsto_finsetSum _ (fun U _ => (hc U).const_mul _)
 refine htend.congr' ?_
 filter_upwards with x
 rw [hcount_eq x,mul_sum]
 apply sum_congr rfl
 intro U _
 ring
def noSqf (H m:ℕ):Prop:=∀ j∈Icc 1 H,¬ Squarefree (m+j)
noncomputable instance (H:ℕ):DecidablePred (noSqf H):=Classical.decPred _
noncomputable def Mstar (Y H:ℕ):ℕ:=((Ioc (Y/2) Y).filter (noSqf H)).card
lemma sp_cov (H m:ℕ) (hH:10000<=H) :
  (((Icc 1 H).filter (fun j =>
    ∃ p∈(Icc 1 (Nat.sqrt H)).filter Nat.Prime,p^2∣m+j)).card:ℝ)<=(49/100:ℝ)*(H:ℝ):=by
 let S:=(Icc 1 (Nat.sqrt H)).filter Nat.Prime
 have hsub:(Icc 1 H).filter (fun j => ∃ p∈S,p^2∣m+j) ⊆
   S.biUnion (fun p => (Icc 1 H).filter (fun j => p^2∣m+j)):=by
  intro j hj
  simp only [mf,mbu] at hj ⊢
  rcases hj.2 with ⟨p,hp,hd⟩
  exact ⟨p,hp,hj.1,hd⟩
 have hinner:∀ p∈S,((Icc 1 H).filter (fun j => p^2∣m+j)).card<=H/p^2+1:=by
  intro p hp
  have hp_pos:0 < p^2:=pow_pos (mf.mp hp).2.pos 2
  have himg:((Icc 1 H).filter (fun j => p^2∣m+j)).card<=((Ioc m (m+H)).filter (fun n => p^2∣n)).card:=by
   refine card_le_card_of_injOn (fun j => m+j) ?_ ?_
   ·
    intro j hj
    rw [mem_coe,mf,micc] at hj
    rw [mem_coe,mf,mioc]
    dsimp only
    exact ⟨⟨by omega,by omega⟩,hj.2⟩
   · intro j₁ _ j₂ _ h;dsimp at h;omega
  exact ltr himg (cm_ioc m H (p^2) hp_pos)
 have hnat:((Icc 1 H).filter (fun j => ∃ p∈S,p^2∣m+j)).card<=∑ p∈S,(H/p^2+1):=by
  calc
   ((Icc 1 H).filter (fun j => ∃ p∈S,p^2∣m+j)).card
    <= (S.biUnion (fun p => (Icc 1 H).filter (fun j => p^2∣m+j))).card:=clc hsub
   _<=∑ p∈S,((Icc 1 H).filter (fun j => p^2∣m+j)).card:=cbi
   _<=∑ p∈S,(H/p^2+1):=sls hinner
 have hcast:(((Icc 1 H).filter (fun j => ∃ p∈S,p^2∣m+j)).card:ℝ)<=∑ p∈S,(((H/p^2:ℕ):ℝ)+1):=by exact_mod_cast hnat
 have hS_card:(S.card:ℝ)<=(Nat.sqrt H:ℝ):=by
  have hle:S.card<=(Icc 1 (Nat.sqrt H)).card:=cfl _ _
  have hcard:(Icc 1 (Nat.sqrt H)).card=Nat.sqrt H:=by simp
  exact_mod_cast (hle.trans_eq hcard)
 have hsqrt_le:(Nat.sqrt H:ℝ)<=(1/100:ℝ)*(H:ℝ):=by
  have hnat_sq:100*Nat.sqrt H<=H:=by
   have hsq:Nat.sqrt H*Nat.sqrt H<=H:=Nat.sqrt_le H
   have h100:100<=Nat.sqrt H:=by
    exact (Nat.le_sqrt).mpr (by omega)
   nlinarith
  have hR:(100:ℝ)*(Nat.sqrt H:ℝ)<=(H:ℝ):=by exact_mod_cast hnat_sq
  linarith
 calc
  (((Icc 1 H).filter (fun j => ∃ p∈S,p^2∣m+j)).card:ℝ)
   <= (∑ p∈S,(H:ℝ)/(p:ℝ)^2)+(S.card:ℝ):=by
    have h1:∑ p∈S,(((H/p^2:ℕ):ℝ)+1)=(∑ p∈S,((H/p^2:ℕ):ℝ))+(S.card:ℝ):=by
     rw [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one]
    rw [h1] at hcast
    have h2:∑ p∈S,((H/p^2:ℕ):ℝ)<=∑ p∈S,(H:ℝ)/(p:ℝ)^2:=by
     apply sls
     intro p hp
     have hp_pos:(0:ℝ) < (p:ℝ)^2:=by
      exact_mod_cast pow_pos (mf.mp hp).2.pos 2
     rw [ldi hp_pos]
     exact_mod_cast dls H (p^2)
    linarith
  _=(H:ℝ)*(∑ p∈S,(1:ℝ)/(p:ℝ)^2)+(S.card:ℝ):=by
    congr 1
    rw [mul_sum]
    apply sum_congr rfl;intro p _;ring
  _<=(H:ℝ)*(48/100:ℝ)+(1/100:ℝ)*(H:ℝ):=by
    have hsum:=sum_prime_inv_sq_le (Nat.sqrt H)
    nlinarith
  _=(49/100:ℝ)*(H:ℝ):=by ring
lemma pgs_1 {H m p j₁ j₂:ℕ} (hp:Nat.sqrt H < p)
  (hj₁:j₁∈Icc 1 H) (hj₂:j₂∈Icc 1 H)
  (hd₁:p^2∣m+j₁) (hd₂:p^2∣m+j₂):j₁=j₂:=by
 simp only [micc] at hj₁ hj₂
 have hp2:H < p^2:=by
  have:=Nat.lt_succ_sqrt H
  nlinarith
 rcases le_total j₁ j₂ with hle | hle
 ·
  have hd:p^2∣(m+j₂) - (m+j₁):=Nat.dvd_sub hd₂ hd₁
  have hsub:(m+j₂) - (m+j₁)=j₂ - j₁:=by omega
  rw [hsub] at hd
  by_cases h0:j₂ - j₁=0
  · omega
  ·
   have:=Nat.le_of_dvd (by omega) hd
   omega
 ·
  have hd:p^2∣(m+j₁) - (m+j₂):=Nat.dvd_sub hd₁ hd₂
  have hsub:(m+j₁) - (m+j₂)=j₁ - j₂:=by omega
  rw [hsub] at hd
  by_cases h0:j₁ - j₂=0
  · omega
  ·
   have:=Nat.le_of_dvd (by omega) hd
   omega
lemma mp_gs (H m:ℕ) (hH:10000<=H) (hno:noSqf H m) :
  H/2<=((Ioc (Nat.sqrt H) (m+H)).filter (fun p =>
   p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card:=by
 let Jsmall:=(Icc 1 H).filter (fun j =>
   ∃ p∈(Icc 1 (Nat.sqrt H)).filter Nat.Prime,p^2∣m+j)
 let Jbig:=(Icc 1 H) \ Jsmall
 have hsmall:(Jsmall.card:ℝ)<=(49/100:ℝ)*(H:ℝ):=sp_cov H m hH
 have hsmall_nat:Jsmall.card<=H - H/2:=by
  have hR:(Jsmall.card:ℝ)<=((H - H/2:ℕ):ℝ):=by
   have hhalf:(H:ℝ)/2<=((H - H/2:ℕ):ℝ):=by
    have hnat:H<=2*(H - H/2):=by omega
    have hR2:(H:ℝ)<=2*((H - H/2:ℕ):ℝ):=by exact_mod_cast hnat
    linarith
   linarith
  exact_mod_cast hR
 have hbig_ge:H/2<=Jbig.card:=by
  have hsub:Jsmall⊆Icc 1 H:=fsub _ _
  have hcard:Jbig.card=(Icc 1 H).card - Jsmall.card:=card_sdiff_of_subset hsub
  have hIcc:(Icc 1 H).card=H:=by simp
  omega
 have hex:∀ j∈Jbig,∃ p∈(Ioc (Nat.sqrt H) (m+H)).filter (fun p =>
   p.Prime/\∃ j'∈Icc 1 H,p^2∣m+j'),p^2∣m+j:=by
  intro j hj
  rw [Finset.mem_sdiff] at hj
  have hjI:j∈Icc 1 H:=hj.1
  have hnsqf:¬ Squarefree (m+j):=hno j hjI
  rw [sqf_iff] at hnsqf
  push Not at hnsqf
  rcases hnsqf with ⟨p,hp,hdvd⟩
  have hp_gt:Nat.sqrt H < p:=by
   by_contra hle;push Not at hle
   apply hj.2
   exact mf.mpr ⟨hjI,p,mf.mpr ⟨micc.mpr ⟨hp.one_lt.le,hle⟩,hp⟩,hdvd⟩
  have hp_le:p<=m+H:=by
   have hm_pos:1<=m+j:=by simp only [micc] at hjI;omega
   have hp2_le:p^2<=m+j:=Nat.le_of_dvd hm_pos hdvd
   have hp_sq:p<=p^2:=by nlinarith [hp.one_lt]
   simp only [micc] at hjI
   omega
  exact ⟨p,mf.mpr ⟨mioc.mpr ⟨hp_gt,hp_le⟩,hp,j,hjI,hdvd⟩,hdvd⟩
 choose f hf_mem hf_dvd using hex
 have hinj:Jbig.card<=((Ioc (Nat.sqrt H) (m+H)).filter (fun p =>
   p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card:=by
  refine Finset.card_le_card_of_injOn (fun j => if h:j∈Jbig then f j h else 0) ?_ ?_
  ·
   intro j hj
   rw [mem_coe] at hj ⊢
   simp only [dif_pos hj]
   exact hf_mem j hj
  ·
   intro j₁ hj₁ j₂ hj₂ heq
   rw [mem_coe] at hj₁ hj₂
   simp only [dif_pos hj₁,dif_pos hj₂] at heq
   have hp1:Nat.sqrt H < f j₁ hj₁:=(mioc.mp (mf.mp (hf_mem j₁ hj₁)).1).1
   have hd1:(f j₁ hj₁)^2∣m+j₁:=hf_dvd j₁ hj₁
   have hd2:(f j₁ hj₁)^2∣m+j₂:=by rw [heq];exact hf_dvd j₂ hj₂
   exact pgs_1 hp1 (Finset.mem_sdiff.mp hj₁).1 (Finset.mem_sdiff.mp hj₂).1 hd1 hd2
 exact ltr hbig_ge hinj
lemma r4_van (Y H:ℕ) (hY:2^600<=Y) (hH:10^9*Y<=H^3) :
  Mstar Y H=0:=by
 have hH_big:2^200<=H:=by
  by_contra hlt;push Not at hlt
  have h1:H^3 < (2^200)^3:=Nat.pow_lt_pow_left hlt (by omega)
  have h2:(2^200:ℕ)^3=2^600:=by rw [← pmul]
  omega
 have hH10000:10000<=H:=by
  have:10000<=2^200:=by norm_num
  omega
 rw [Mstar,Finset.card_eq_zero,filter_eq_empty_iff]
 intro m hm hno
 simp only [mioc] at hm
 have hmany:=mp_gs H m hH10000 hno
 let Pset:=(Ioc (Nat.sqrt H) (m+H)).filter (fun p =>
   p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)
 change H/2<=Pset.card at hmany
 let P1:=Pset.filter (fun p => p<=H)
 let P2:=Pset.filter (fun p => H < p)
 have hsplit:Pset.card<=P1.card+P2.card:=by
  have hunion:Pset⊆P1∪P2:=by
   intro p hp
   simp only [P1,P2,mun,mf]
   by_cases h:p<=H
   · exact Or.inl ⟨hp,h⟩
   · exact Or.inr ⟨hp,by omega⟩
  exact ltr (clc hunion) (cul _ _)
 have hP1:(P1.card:ℝ)<=(18/200:ℝ)*(H:ℝ):=by
  have hsub:P1⊆(Icc 1 H).filter Nat.Prime:=by
   intro p hp
   simp only [P1,Pset,mf,mioc,micc] at hp ⊢
   exact ⟨⟨hp.1.2.1.one_lt.le,hp.2⟩,hp.1.2.1⟩
  have hch:=ch_cnt H (by omega)
  have hlog200:200<=Nat.log 2 H:=llp (by omega) hH_big
  have hlogR:(200:ℝ)<=(Nat.log 2 H:ℝ):=by exact_mod_cast hlog200
  calc
   (P1.card:ℝ)<=(((Icc 1 H).filter Nat.Prime).card:ℝ):=by
    exact_mod_cast clc hsub
   _<=18*(H:ℝ)/(Nat.log 2 H:ℝ):=hch
   _<=18*(H:ℝ)/200:=div_le_div_of_nonneg_left (by positivity) (by norm_num) hlogR
   _=(18/200:ℝ)*(H:ℝ):=by ring
 have hP2:P2.card<=H/10:=by
  by_cases hHY:Y<=H
  ·
   have hemp:P2=∅:=by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [P2,Pset,mf,mioc] at hp
    rcases hp.1.2.2 with ⟨j,hj,hdvd⟩
    simp only [micc] at hj
    have hle:p^2<=m+j:=Nat.le_of_dvd (by omega) hdvd
    have hp_gt:H < p:=hp.2
    have h2H:m+j<=2*H:=by omega
    have hsq_gt:2*H < p^2:=by
     have h1:2*H < H*H:=by nlinarith only [hH10000]
     have h2:H*H < p*p:=by nlinarith only [hp_gt]
     have h3:p^2=p*p:=sq p
     omega
    omega
   rw [hemp,card_empty];omega
  ·
   push Not at hHY
   have hex_a:∀ p∈P2,∃ a∈Icc 1 (2*Y/H^2),∃ j∈Icc 1 H,m+j=a*p^2:=by
    intro p hp
    simp only [P2,Pset,mf,mioc] at hp
    rcases hp.1.2.2 with ⟨j,hj,⟨a,ha⟩⟩
    simp only [micc] at hj
    have ha_pos:1<=a:=by
     by_contra h0;push Not at h0
     have:a=0:=by omega
     subst this;simp at ha;omega
    have ha_le:a<=2*Y/H^2:=by
     refine (ldim (by positivity)).mpr ?_
     have h1:a*H^2<=a*p^2:=nml a (npl (lol hp.2) 2)
     have h2:a*p^2=m+j:=by rw [mcom];exact ha.symm
     omega
    exact ⟨a,micc.mpr ⟨ha_pos,ha_le⟩,j,micc.mpr hj,by rw [mcom];exact ha⟩
   choose fa hfa_mem hfa_ex using hex_a
   have hinj:P2.card<=(Icc 1 (2*Y/H^2)).card:=by
    refine card_le_card_of_injOn (fun p => if h:p∈P2 then fa p h else 0) ?_ ?_
    ·
     intro p hp
     rw [mem_coe] at hp ⊢
     simp only [dif_pos hp]
     exact hfa_mem p hp
    ·
     intro p₁ hp₁ p₂ hp₂ heq
     rw [mem_coe] at hp₁ hp₂
     simp only [dif_pos hp₁,dif_pos hp₂] at heq
     rcases hfa_ex p₁ hp₁ with ⟨j₁,hj₁,hm₁⟩
     rcases hfa_ex p₂ hp₂ with ⟨j₂,hj₂,hm₂⟩
     rw [heq] at hm₁
     have ha_pos:1<=fa p₂ hp₂:=(micc.mp (hfa_mem p₂ hp₂)).1
     have hp1_gt:H < p₁:=(mf.mp hp₁).2
     have hp2_gt:H < p₂:=(mf.mp hp₂).2
     simp only [micc] at hj₁ hj₂
     by_contra hne
     rcases lt_or_gt_of_ne hne with hlt | hgt
     ·
      have hsq:p₁^2+2*H < p₂^2:=by nlinarith
      nlinarith
     ·
      have hsq:p₂^2+2*H < p₁^2:=by nlinarith
      nlinarith
   have hcard_le:(Icc 1 (2*Y/H^2)).card<=H/10:=by
    simp only [Nat.card_Icc,add_tsub_cancel_right]
    have h1:2*Y/H^2<=H/10:=by
     have hdiv:2*Y < (H/10)*H^2:=by
      have h10:H<=10*(H/10)+9:=by omega
      have hH_ge:20<=10*(H/10):=by omega
      have h3:H^3<=20*((H/10)*H^2):=by
       have hle20:H<=20*(H/10):=by omega
       have hmul20:H*H^2<=(20*(H/10))*H^2:=nmr (H^2) hle20
       have hpow3:H^3=H*H^2:=by ring
       have hassoc:(20*(H/10))*H^2=20*((H/10)*H^2):=by ring
       omega
      omega
     exact lol ((Nat.div_lt_iff_lt_mul (by positivity)).mpr hdiv)
    exact h1
   exact ltr hinj hcard_le
 have hP1_nat:P1.card<=H/10:=by
  have hR:(P1.card:ℝ)<=((H/10:ℕ):ℝ):=by
   have h10:(H:ℝ) - 10<=10*((H/10:ℕ):ℝ):=by
    have hnat:H - 10<=10*(H/10):=by omega
    have hR2:((H - 10:ℕ):ℝ)<=10*((H/10:ℕ):ℝ):=by exact_mod_cast hnat
    have hcast:((H - 10:ℕ):ℝ)=(H:ℝ) - 10:=ncs (by omega)
    linarith
   have hHR:(10000:ℝ)<=(H:ℝ):=by exact_mod_cast hH10000
   linarith
  exact_mod_cast hR
 omega
lemma det_pw (Y H m:ℕ) (hH:2^20<=H) (hH3:H^3 < 10^9*Y)
  (hm:m∈Ioc (Y/2) Y) (hno:noSqf H m) :
  let Z1:=H*Nat.log 2 H/1000
  let Z2:=10^5*(Nat.sqrt (Y/H)+1)
  H/4<=((Ioc Z1 Z2).filter (fun p =>
   p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card:=by
 intro Z1 Z2
 simp only [mioc] at hm
 have hH10000:10000<=H:=by omega
 have hlog20:20<=Nat.log 2 H:=llp (by omega) hH
 have hZ1_ge:H/50<=Z1:=by
  have:H*20<=H*Nat.log 2 H:=nml H hlog20
  omega
 have hZ1_ge16:16<=Z1:=by omega
 have hmany:=mp_gs H m hH10000 hno
 let Pset:=(Ioc (Nat.sqrt H) (m+H)).filter (fun p =>
   p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)
 change H/2<=Pset.card at hmany
 let Pmid:=(Ioc Z1 Z2).filter (fun p =>
   p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)
 let Plow:=Pset.filter (fun p => p<=Z1)
 let Phigh:=Pset.filter (fun p => Z2 < p)
 have hcover:Pset⊆Plow∪Pmid∪Phigh:=by
  intro p hp
  have hp':=hp
  simp only [Pset,mf,mioc] at hp'
  simp only [Plow,Pmid,Phigh,mun,mf,mioc]
  by_cases h1:p<=Z1
  · exact Or.inl (Or.inl ⟨hp,h1⟩)
  ·
   by_cases h2:p<=Z2
   · exact Or.inl (Or.inr ⟨⟨by omega,h2⟩,hp'.2⟩)
   · exact Or.inr ⟨hp,by omega⟩
 have hcard_split:Pset.card<=Plow.card+Pmid.card+Phigh.card:=by
  calc
   Pset.card<=(Plow∪Pmid∪Phigh).card:=clc hcover
   _<=(Plow∪Pmid).card+Phigh.card:=cul _ _
   _<=Plow.card+Pmid.card+Phigh.card:=Nat.add_le_add_right (cul _ _) _
 have hPlow:Plow.card<=H/10:=by
  have hsub:Plow⊆(Icc 1 Z1).filter Nat.Prime:=by
   intro p hp
   simp only [Plow,Pset,mf,mioc,micc] at hp ⊢
   exact ⟨⟨hp.1.2.1.one_lt.le,hp.2⟩,hp.1.2.1⟩
  have hch:=ch_cnt Z1 hZ1_ge16
  have hlog_half:Nat.log 2 H<=2*Nat.log 2 Z1:=by
   have hpow:2^(Nat.log 2 H - 6)<=Z1:=by
    have h2m:2^Nat.log 2 H<=H:=pls 2 (by omega)
    have h64:2^(Nat.log 2 H - 6)*64=2^Nat.log 2 H:=by
     have h6:64=2^6:=by norm_num
     rw [h6,← padd]
     congr 1;omega
    omega
   have hge:=llp (by omega) hpow
   omega
  have hZ1_le:(Z1:ℝ)<=(H:ℝ)*(Nat.log 2 H:ℝ)/1000:=by
   rw [ldi (by norm_num)]
   have hnat:Z1*1000<=H*Nat.log 2 H:=dls _ _
   exact_mod_cast hnat
  have hlogZ1_pos:(0:ℝ) < (Nat.log 2 Z1:ℝ):=by
   have:4<=Nat.log 2 Z1:=llp (by omega) hZ1_ge16
   exact_mod_cast (by omega:0 < Nat.log 2 Z1)
  have hlog_halfR:(Nat.log 2 H:ℝ)<=2*(Nat.log 2 Z1:ℝ):=by exact_mod_cast hlog_half
  have hR:(Plow.card:ℝ)<=(36/1000:ℝ)*(H:ℝ):=by
   calc
    (Plow.card:ℝ)<=(((Icc 1 Z1).filter Nat.Prime).card:ℝ):=by
     exact_mod_cast clc hsub
    _<=18*(Z1:ℝ)/(Nat.log 2 Z1:ℝ):=hch
    _<=18*((H:ℝ)*(Nat.log 2 H:ℝ)/1000)/((Nat.log 2 H:ℝ)/2):=by
     have h1:18*(Z1:ℝ)<=18*((H:ℝ)*(Nat.log 2 H:ℝ)/1000):=by linarith
     have h2:(Nat.log 2 H:ℝ)/2<=(Nat.log 2 Z1:ℝ):=by linarith
     have hposH:(0:ℝ) < (Nat.log 2 H:ℝ)/2:=by
      have:(20:ℝ)<=(Nat.log 2 H:ℝ):=by exact_mod_cast hlog20
      linarith
     exact div_le_div₀ (by positivity) h1 hposH h2
    _=(36/1000:ℝ)*(H:ℝ):=by
     have hne:(Nat.log 2 H:ℝ)≠0:=by
      have:(20:ℝ)<=(Nat.log 2 H:ℝ):=by exact_mod_cast hlog20
      linarith
     field_simp;ring
  have hnatR:(Plow.card:ℝ)<=((H/10:ℕ):ℝ):=by
   have h10:(H:ℝ) - 10<=10*((H/10:ℕ):ℝ):=by
    have hnat:H - 10<=10*(H/10):=by omega
    have hR2:((H - 10:ℕ):ℝ)<=10*((H/10:ℕ):ℝ):=by exact_mod_cast hnat
    have hcast:((H - 10:ℕ):ℝ)=(H:ℝ) - 10:=ncs (by omega)
    linarith
   have hHR:(10000:ℝ)<=(H:ℝ):=by exact_mod_cast hH10000
   linarith
  exact_mod_cast hnatR
 have hHY:H<=Y:=by
  by_contra hlt;push Not at hlt
  have h1:(2^20:ℕ)^2<=H^2:=npl hH 2
  have h2:10^9 < (2^20:ℕ)^2:=by norm_num
  nlinarith
 have hZ2_sq:10^10*Y < Z2^2*H:=by
  have hlt_sq:Y/H < (Nat.sqrt (Y/H)+1)^2:=Nat.lt_succ_sqrt' (Y/H)
  have hY_le:Y < (Y/H+1)*H:=by
   have:=lmd Y (by omega:0 < H)
   have hcomm:H*(Y/H+1)=(Y/H+1)*H:=mcom _ _
   omega
  have h1:Y/H+1<=(Nat.sqrt (Y/H)+1)^2:=hlt_sq
  have h2:Y < (Nat.sqrt (Y/H)+1)^2*H:=lt_of_lt_of_le hY_le (nmr H h1)
  have hZ2_eq:Z2^2=10^10*(Nat.sqrt (Y/H)+1)^2:=by dsimp [Z2];ring
  rw [hZ2_eq,mul_assoc]
  exact Nat.mul_lt_mul_of_pos_left h2 (by norm_num)
 have h2Z2_gt_H:H < 2*Z2:=by
  by_contra hle;push Not at hle
  have h1:(2*Z2)^2*H<=H^2*H:=nmr H (npl hle 2)
  have h1':H^2*H=H^3:=by ring
  have h2:(2*Z2)^2*H=4*(Z2^2*H):=by ring
  omega
 have hPhigh:Phigh.card<=H/10:=by
  have hex_a:∀ p∈Phigh,∃ a∈Icc 1 (H/10),∃ j∈Icc 1 H,m+j=a*p^2:=by
   intro p hp
   simp only [Phigh,Pset,mf,mioc] at hp
   rcases hp.1.2.2 with ⟨j,hj,⟨a,ha⟩⟩
   simp only [micc] at hj
   have ha_pos:1<=a:=by
    by_contra h0;push Not at h0
    have:a=0:=by omega
    subst this;simp at ha;omega
   have ha_eq:a*p^2=m+j:=by rw [mcom];exact ha.symm
   have ha_le:a<=H/10:=by
    have h1:a*Z2^2<=a*p^2:=nml a (npl (lol hp.2) 2)
    have h2:a*p^2<=2*Y:=by omega
    have h3:a*Z2^2*H<=2*Y*H:=nmr H (ltr h1 h2)
    have h4:a*(10^10*Y) < a*(Z2^2*H):=Nat.mul_lt_mul_of_pos_left hZ2_sq (by omega)
    have h5:a*10^10*Y < 2*H*Y:=by linarith
    have h6:a*10^10 < 2*H:=Nat.lt_of_mul_lt_mul_right h5
    omega
   exact ⟨a,micc.mpr ⟨ha_pos,ha_le⟩,j,micc.mpr hj,ha_eq.symm⟩
  choose fa hfa_mem hfa_ex using hex_a
  have hinj:Phigh.card<=(Icc 1 (H/10)).card:=by
   refine card_le_card_of_injOn (fun p => if h:p∈Phigh then fa p h else 0) ?_ ?_
   ·
    intro p hp
    rw [mem_coe] at hp ⊢
    simp only [dif_pos hp]
    exact hfa_mem p hp
   ·
    intro p₁ hp₁ p₂ hp₂ heq
    rw [mem_coe] at hp₁ hp₂
    simp only [dif_pos hp₁,dif_pos hp₂] at heq
    rcases hfa_ex p₁ hp₁ with ⟨j₁,hj₁,hm₁⟩
    rcases hfa_ex p₂ hp₂ with ⟨j₂,hj₂,hm₂⟩
    rw [heq] at hm₁
    have ha_pos:1<=fa p₂ hp₂:=(micc.mp (hfa_mem p₂ hp₂)).1
    have hp1_gt:Z2 < p₁:=(mf.mp hp₁).2
    have hp2_gt:Z2 < p₂:=(mf.mp hp₂).2
    simp only [micc] at hj₁ hj₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    ·
     have hsq:p₁^2+2*Z2 < p₂^2:=by
      have h1:p₁+1<=p₂:=hlt
      nlinarith only [h1,hp1_gt]
     have hmul:fa p₂ hp₂*p₁^2+H < fa p₂ hp₂*p₂^2:=by
      nlinarith only [hsq,h2Z2_gt_H,ha_pos]
     omega
    ·
     have hsq:p₂^2+2*Z2 < p₁^2:=by
      have h1:p₂+1<=p₁:=hgt
      nlinarith only [h1,hp2_gt]
     have hmul:fa p₂ hp₂*p₂^2+H < fa p₂ hp₂*p₁^2:=by
      nlinarith only [hsq,h2Z2_gt_H,ha_pos]
     omega
  simpa using hinj
 change H/4<=Pmid.card
 omega
lemma kt_crt (Y H k R:ℕ) (_hk:1<=k) (_hR:k<=R)
  (Pset:Finset ℕ) (hPset:∀ p∈Pset,p.Prime)
  (E:Finset ℕ) (hE_sub:E⊆Icc 1 Y)
  (hE_prop:∀ m∈E,R<=(Pset.filter (fun p => ∃ j∈Icc 1 H,p^2∣m+j)).card) :
  ((Nat.choose R k:ℕ):ℝ)*(E.card:ℝ)<=(H:ℝ)^k/(k.factorial:ℝ)*((Y:ℝ)*(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^k+(Pset.card:ℝ)^k):=by
 let PSub:=Pset.powersetCard k
 let hit (m:ℕ) (S:Finset ℕ):Prop:=∀ p∈S,∃ j∈Icc 1 H,p^2∣m+j
 let _inst:DecidableRel hit:=fun _ _ => Classical.propDecidable _
 have hLHS:Nat.choose R k*E.card<=∑ m∈E,(PSub.filter (hit m)).card:=by
  calc
   Nat.choose R k*E.card=∑ _m∈E,Nat.choose R k:=by rw [sum_const,smul_eq_mul,mcom]
   _<=∑ m∈E,(PSub.filter (hit m)).card:=by
    apply sls
    intro m hm
    let Pm:=Pset.filter (fun p => ∃ j∈Icc 1 H,p^2∣m+j)
    have hPm_sub:Pm.powersetCard k⊆PSub.filter (hit m):=by
     intro S hS
     rw [Finset.mem_powersetCard] at hS
     rw [mf,Finset.mem_powersetCard]
     refine ⟨⟨ltr hS.1 (fsub _ _),hS.2⟩,fun p hp => ?_⟩
     exact (mf.mp (hS.1 hp)).2
    calc
     Nat.choose R k<=Nat.choose Pm.card k:=Nat.choose_le_choose k (hE_prop m hm)
     _=(Pm.powersetCard k).card:=(Finset.card_powersetCard k Pm).symm
     _<=(PSub.filter (hit m)).card:=clc hPm_sub
 have hswap:∑ m∈E,(PSub.filter (hit m)).card=∑ S∈PSub,(E.filter (fun m => hit m S)).card:=by
  have h1:∀ m∈E,(PSub.filter (hit m)).card=∑ S∈PSub,if hit m S then 1 else 0:=by
   intro m _;rw [card_filter]
  have h2:∀ S∈PSub,(E.filter (fun m => hit m S)).card=∑ m∈E,if hit m S then 1 else 0:=by
   intro S _;rw [card_filter]
  rw [sum_congr rfl h1,sum_comm,sum_congr rfl h2]
 have hinner:∀ S∈PSub,((E.filter (fun m => hit m S)).card:ℝ)<=(H:ℝ)^k*((Y:ℝ)/(∏ p∈S,(p:ℝ)^2)+1):=by
  intro S hS
  rw [Finset.mem_powersetCard] at hS
  have hS_pr:∀ p∈S,p.Prime:=fun p hp => hPset p (hS.1 hp)
  let Funcs:Finset (∀ _p∈S,ℕ):=Finset.pi S (fun _ => Icc 1 H)
  have hFuncs_card:Funcs.card=H^k:=by
   rw [Finset.card_pi,prod_const,hS.2]
   simp
  have hcover:E.filter (fun m => hit m S) ⊆
    Funcs.biUnion (fun f =>
     (Icc 1 Y).filter (fun m => ∀ p,(hp:p∈S)->p^2∣m+f p hp)):=by
   intro m hm
   rw [mf] at hm
   rw [mbu]
   have hex:∀ p∈S,∃ j∈Icc 1 H,p^2∣m+j:=hm.2
   choose f hf_mem hf_dvd using hex
   refine ⟨f,Finset.mem_pi.mpr hf_mem,mf.mpr ⟨hE_sub hm.1,hf_dvd⟩⟩
  have hterm:∀ f∈Funcs,((Icc 1 Y).filter (fun m => ∀ p,(hp:p∈S)->p^2∣m+f p hp)).card<=Y/(∏ p∈S,p^2)+1:=by
   intro f _
   let jfn:ℕ->ℕ:=fun p => if hp:p∈S then f p hp else 0
   have heq:(Icc 1 Y).filter (fun m => ∀ p,(hp:p∈S)->p^2∣m+f p hp)=(Icc 1 Y).filter (fun m => ∀ p∈S,p^2∣m+jfn p):=by
    ext m;simp only [mf,jfn]
    constructor <;> intro ⟨h1,h2⟩ <;> refine ⟨h1,fun p hp => ?_⟩
    · simpa [dif_pos hp] using h2 p hp
    · simpa [dif_pos hp] using h2 p hp
   rw [heq]
   exact crt_sq Y S hS_pr jfn
  have hnat:(E.filter (fun m => hit m S)).card<=H^k*(Y/(∏ p∈S,p^2)+1):=by
   calc
    (E.filter (fun m => hit m S)).card
     <= (Funcs.biUnion (fun f =>
       (Icc 1 Y).filter (fun m => ∀ p,(hp:p∈S)->p^2∣m+f p hp))).card:=clc hcover
    _<=∑ f∈Funcs,((Icc 1 Y).filter (fun m => ∀ p,(hp:p∈S)->p^2∣m+f p hp)).card:=cbi
    _<=∑ _f∈Funcs,(Y/(∏ p∈S,p^2)+1):=sls hterm
    _=H^k*(Y/(∏ p∈S,p^2)+1):=by rw [sum_const,hFuncs_card,smul_eq_mul]
  have hcast:((E.filter (fun m => hit m S)).card:ℝ)<=(H:ℝ)^k*(((Y/(∏ p∈S,p^2):ℕ):ℝ)+1):=by exact_mod_cast hnat
  have hDpos:(0:ℝ) < ∏ p∈S,(p:ℝ)^2:=by
   apply Finset.prod_pos
   intro p hp
   exact pow_pos (by exact_mod_cast (hS_pr p hp).pos) 2
  have hdiv:((Y/(∏ p∈S,p^2):ℕ):ℝ)<=(Y:ℝ)/(∏ p∈S,(p:ℝ)^2):=by
   rw [ldi hDpos]
   have hcastD:((∏ p∈S,p^2:ℕ):ℝ)=∏ p∈S,(p:ℝ)^2:=by push_cast;rfl
   rw [← hcastD]
   exact_mod_cast dls Y (∏ p∈S,p^2)
  have hHk_nn:(0:ℝ)<=(H:ℝ)^k:=by positivity
  nlinarith
 have hsymm_gen:∀ (m:ℕ) (w:ℕ->ℝ),(∀ p,0<=w p)->(m.factorial:ℝ)*∑ S∈Pset.powersetCard m,∏ p∈S,w p<=(∑ p∈Pset,w p)^m:=by
  intro m w hw
  induction m with
  | zero => simp
  | succ m ih =>
   have hstep:((m+1:ℕ):ℝ)*∑ S∈Pset.powersetCard (m+1),∏ p∈S,w p<=(∑ p∈Pset,w p)*∑ T∈Pset.powersetCard m,∏ p∈T,w p:=by
    rw [mul_sum]
    have hlhs:∑ S∈Pset.powersetCard (m+1),((m+1:ℕ):ℝ)*∏ p∈S,w p=∑ S∈Pset.powersetCard (m+1),∑ a∈S,w a*∏ p∈S.erase a,w p:=by
     apply sum_congr rfl
     intro S hS
     rw [Finset.mem_powersetCard] at hS
     have h1:∀ a∈S,w a*∏ p∈S.erase a,w p=∏ p∈S,w p:=fun a ha => Finset.mul_prod_erase S w ha
     rw [sum_congr rfl h1,sum_const,hS.2,nsmul_eq_mul]
    rw [hlhs]
    have hswap_w:∑ S∈Pset.powersetCard (m+1),∑ a∈S,w a*∏ p∈S.erase a,w p=∑ a∈Pset,w a*∑ S∈(Pset.powersetCard (m+1)).filter (fun S => a∈S),∏ p∈S.erase a,w p:=by
     have h1:∀ S∈Pset.powersetCard (m+1),∑ a∈S,w a*∏ p∈S.erase a,w p=∑ a∈Pset,if a∈S then w a*∏ p∈S.erase a,w p else 0:=by
      intro S hS
      rw [← sum_subset (Finset.mem_powersetCard.mp hS).1]
      · apply sum_congr rfl;intro a ha;rw [if_pos ha]
      · intro a _ ha;rw [if_neg ha]
     rw [sum_congr rfl h1,sum_comm]
     apply sum_congr rfl
     intro a _
     rw [mul_sum,← Finset.sum_filter]
    rw [hswap_w,sum_mul]
    apply sls
    intro a ha
    apply ml _ (hw a)
    have hbij:∑ S∈(Pset.powersetCard (m+1)).filter (fun S => a∈S),∏ p∈S.erase a,w p=∑ T∈(Pset.erase a).powersetCard m,∏ p∈T,w p:=by
     refine Finset.sum_bij (fun S _ => S.erase a) ?_ ?_ ?_ ?_
     ·
      intro S hS
      rw [mf,Finset.mem_powersetCard] at hS
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.erase_subset_erase a hS.1.1,?_⟩
      rw [Finset.card_erase_of_mem hS.2,hS.1.2]
      omega
     ·
      intro S₁ hS₁ S₂ hS₂ heq
      rw [mf] at hS₁ hS₂
      rw [← Finset.insert_erase hS₁.2,← Finset.insert_erase hS₂.2,heq]
     ·
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      have ha_not:a ∉ T:=fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl
      refine ⟨insert a T,?_,Finset.erase_insert ha_not⟩
      rw [mf,Finset.mem_powersetCard]
      refine ⟨⟨Finset.insert_subset_iff.mpr ⟨ha,ltr hT.1 (Finset.erase_subset a Pset)⟩,?_⟩,mem_insert_self a T⟩
      rw [Finset.card_insert_of_notMem ha_not,hT.2]
     · intro _ _;rfl
    rw [hbij]
    exact ssub
     (Finset.powersetCard_mono (Finset.erase_subset a Pset))
     (fun _ _ _ => Finset.prod_nonneg (fun _ _ => hw _))
   rw [Nat.factorial_succ,pow_succ,Nat.cast_mul]
   have hmfac_nn:(0:ℝ)<=(m.factorial:ℝ):=by positivity
   have hsum_nn:(0:ℝ)<=∑ p∈Pset,w p:=sum_nonneg (fun _ _ => hw _)
   calc
    ((m+1:ℕ):ℝ)*(m.factorial:ℝ)*∑ S∈Pset.powersetCard (m+1),∏ p∈S,w p
     = (m.factorial:ℝ)*(((m+1:ℕ):ℝ)*∑ S∈Pset.powersetCard (m+1),∏ p∈S,w p):=by
      ring
    _<=(m.factorial:ℝ)*((∑ p∈Pset,w p)*∑ T∈Pset.powersetCard m,∏ p∈T,w p):=ml hstep hmfac_nn
    _=(∑ p∈Pset,w p)*((m.factorial:ℝ)*∑ T∈Pset.powersetCard m,∏ p∈T,w p):=by
      ring
    _<=(∑ p∈Pset,w p)*(∑ p∈Pset,w p)^m:=ml ih hsum_nn
    _=(∑ p∈Pset,w p)^m*∑ p∈Pset,w p:=by ring
 have hsymm:(k.factorial:ℝ)*∑ S∈PSub,(1:ℝ)/(∏ p∈S,(p:ℝ)^2)<=(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^k:=by
  have h:=hsymm_gen k (fun p => (1:ℝ)/(p:ℝ)^2) (fun _ => by positivity)
  have heq:∑ S∈PSub,(1:ℝ)/(∏ p∈S,(p:ℝ)^2)=∑ S∈Pset.powersetCard k,∏ p∈S,(1:ℝ)/(p:ℝ)^2:=by
   apply sum_congr rfl
   intro S _
   rw [Finset.prod_div_distrib,Finset.prod_const_one]
  rwa [heq]
 have hPSub_card:(k.factorial:ℝ)*(PSub.card:ℝ)<=(Pset.card:ℝ)^k:=by
  have hnat:k.factorial*PSub.card<=Pset.card^k:=by
   rw [Finset.card_powersetCard,← Nat.descFactorial_eq_factorial_mul_choose]
   exact Nat.descFactorial_le_pow Pset.card k
  exact_mod_cast hnat
 have hkfac_pos:(0:ℝ) < (k.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos k
 have hcastLHS:((Nat.choose R k:ℕ):ℝ)*(E.card:ℝ)<=∑ S∈PSub,((E.filter (fun m => hit m S)).card:ℝ):=by
  exact_mod_cast (hLHS.trans_eq hswap)
 calc
  ((Nat.choose R k:ℕ):ℝ)*(E.card:ℝ)
   <= ∑ S∈PSub,(H:ℝ)^k*((Y:ℝ)/(∏ p∈S,(p:ℝ)^2)+1):=ltr hcastLHS (sls hinner)
  _=(H:ℝ)^k*((Y:ℝ)*(∑ S∈PSub,(1:ℝ)/(∏ p∈S,(p:ℝ)^2))+(PSub.card:ℝ)):=by
    rw [← mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,mul_sum]
    congr 2
    apply sum_congr rfl;intro S _;ring
  _<=(H:ℝ)^k*((Y:ℝ)*((∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^k/(k.factorial:ℝ))+(Pset.card:ℝ)^k/(k.factorial:ℝ)):=by
    apply ml _ (by positivity)
    have h1:∑ S∈PSub,(1:ℝ)/(∏ p∈S,(p:ℝ)^2)<=(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^k/(k.factorial:ℝ):=(ldi hkfac_pos).mpr (by linarith)
    have h2:(PSub.card:ℝ)<=(Pset.card:ℝ)^k/(k.factorial:ℝ):=(ldi hkfac_pos).mpr (by linarith)
    have hYnn:(0:ℝ)<=(Y:ℝ):=by positivity
    nlinarith
  _=(H:ℝ)^k/(k.factorial:ℝ)*((Y:ℝ)*(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^k+(Pset.card:ℝ)^k):=by
    ring
lemma r1_bd (Y H:ℕ) (hH:10000<=H) (hHY:H^22<=Y) :
  (H:ℝ)^2*(Mstar Y H:ℝ)<=(2^32:ℝ)*(Y:ℝ)/(H:ℝ):=by
 let E:=(Ioc (Y/2) Y).filter (noSqf H)
 let E_mid:=E.filter (fun m =>
   H/4<=((Ioc (Nat.sqrt H) (H^3)).filter
    (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card)
 let E_gt:=E.filter (fun m =>
   H/4<=((Ioc (H^3) (2*Y)).filter
    (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card)
 have hHY_le:H<=Y:=by
  have:H<=H^22:=Nat.le_self_pow (by omega) H
  omega
 have hcover:E⊆E_mid∪E_gt:=by
  intro m hm
  have hno:noSqf H m:=(mf.mp hm).2
  have hm_le:m<=Y:=(mioc.mp (mf.mp hm).1).2
  have hmany:=mp_gs H m hH hno
  let P_all:=(Ioc (Nat.sqrt H) (m+H)).filter
    (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)
  let P_mid:=(Ioc (Nat.sqrt H) (H^3)).filter
    (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)
  let P_gt:=(Ioc (H^3) (2*Y)).filter
    (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)
  have hPsub:P_all⊆P_mid∪P_gt:=by
   intro p hp
   simp only [P_all,P_mid,P_gt,mun,mf,mioc] at hp ⊢
   by_cases hle:p<=H^3
   · exact Or.inl ⟨⟨hp.1.1,hle⟩,hp.2⟩
   · exact Or.inr ⟨⟨by omega,by omega⟩,hp.2⟩
  have hcard:H/2<=P_mid.card+P_gt.card:=ltr hmany (ltr (clc hPsub) (cul _ _))
  rw [mun]
  by_cases h1:H/4<=P_mid.card
  · exact Or.inl (mf.mpr ⟨hm,h1⟩)
  · exact Or.inr (mf.mpr ⟨hm,show H/4<=P_gt.card by omega⟩)
 have hEgt:(E_gt.card:ℝ)<=16*(Y:ℝ)/(H:ℝ)^3:=by
  let P_gt_all:=(Ioc (H^3) (2*Y)).filter Nat.Prime
  have hdouble:(H/4)*E_gt.card<=∑ p∈P_gt_all,((Icc 1 Y).filter (fun m => ∃ j∈Icc 1 H,p^2∣m+j)).card:=by
   calc
    (H/4)*E_gt.card=∑ _m∈E_gt,(H/4):=by rw [sum_const,smul_eq_mul,mcom]
    _<=∑ m∈E_gt,(P_gt_all.filter (fun p => ∃ j∈Icc 1 H,p^2∣m+j)).card:=by
     apply sls
     intro m hm
     have h1:=(mf.mp hm).2
     have heq:(Ioc (H^3) (2*Y)).filter
       (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)=P_gt_all.filter (fun p => ∃ j∈Icc 1 H,p^2∣m+j):=by
      ext p;simp only [P_gt_all,mf];tauto
     rwa [← heq]
    _=∑ p∈P_gt_all,(E_gt.filter (fun m => ∃ j∈Icc 1 H,p^2∣m+j)).card:=by
     have h1:∀ m∈E_gt,(P_gt_all.filter (fun p => ∃ j∈Icc 1 H,p^2∣m+j)).card=∑ p∈P_gt_all,if ∃ j∈Icc 1 H,p^2∣m+j then 1 else 0:=fun _ _ => by rw [card_filter]
     have h2:∀ p∈P_gt_all,(E_gt.filter (fun m => ∃ j∈Icc 1 H,p^2∣m+j)).card=∑ m∈E_gt,if ∃ j∈Icc 1 H,p^2∣m+j then 1 else 0:=fun _ _ => by rw [card_filter]
     rw [sum_congr rfl h1,sum_comm,sum_congr rfl h2]
    _<=∑ p∈P_gt_all,((Icc 1 Y).filter (fun m => ∃ j∈Icc 1 H,p^2∣m+j)).card:=by
     apply sls
     intro p _
     apply clc
     apply filter_subset_filter
     intro m hm
     have hmI:=(mf.mp (mf.mp hm).1).1
     simp only [mioc] at hmI
     exact micc.mpr ⟨by omega,hmI.2⟩
  have hinner:∀ p∈P_gt_all,((Icc 1 Y).filter (fun m => ∃ j∈Icc 1 H,p^2∣m+j)).card<=H*(2*Y/p^2):=by
   intro p hp
   have hp_pos:0 < p^2:=pow_pos (mf.mp hp).2.pos 2
   have hsub:(Icc 1 Y).filter (fun m => ∃ j∈Icc 1 H,p^2∣m+j) ⊆
     (Icc 1 H).biUnion (fun j => (Icc 1 Y).filter (fun m => p^2∣m+j)):=by
    intro m hm
    simp only [mf,mbu] at hm ⊢
    rcases hm.2 with ⟨j,hj,hd⟩
    exact ⟨j,hj,hm.1,hd⟩
   calc
    ((Icc 1 Y).filter (fun m => ∃ j∈Icc 1 H,p^2∣m+j)).card
     <= ∑ j∈Icc 1 H,((Icc 1 Y).filter (fun m => p^2∣m+j)).card:=ltr (clc hsub) cbi
    _<=∑ _j∈Icc 1 H,(2*Y/p^2):=by
      apply sls
      intro j hj
      simp only [micc] at hj
      have himg:((Icc 1 Y).filter (fun m => p^2∣m+j)).card<=((Icc 1 (2*Y)).filter (fun n => p^2∣n)).card:=by
       refine card_le_card_of_injOn (fun m => m+j) ?_ ?_
       ·
        intro m hm
        rw [mem_coe,mf,micc] at hm
        rw [mem_coe,mf,micc]
        dsimp only
        exact ⟨⟨by omega,by omega⟩,hm.2⟩
       · intro m₁ _ m₂ _ h;dsimp at h;omega
      exact ltr himg (cm_icc (2*Y) (p^2) hp_pos)
    _=H*(2*Y/p^2):=by simp [sum_const,smul_eq_mul]
  have hnat:(H/4)*E_gt.card<=∑ p∈P_gt_all,H*(2*Y/p^2):=ltr hdouble (sls hinner)
  have hcast:((H/4:ℕ):ℝ)*(E_gt.card:ℝ)<=∑ p∈P_gt_all,(H:ℝ)*(((2*Y/p^2:ℕ):ℝ)):=by exact_mod_cast hnat
  have hsumR:∑ p∈P_gt_all,(H:ℝ)*(((2*Y/p^2:ℕ):ℝ))<=(H:ℝ)*(2*(Y:ℝ))/(H:ℝ)^3:=by
   calc
    ∑ p∈P_gt_all,(H:ℝ)*(((2*Y/p^2:ℕ):ℝ))
     <= ∑ p∈P_gt_all,(H:ℝ)*(2*(Y:ℝ)/(p:ℝ)^2):=by
      apply sls
      intro p hp
      apply ml _ (by positivity)
      have hp_pos:(0:ℝ) < (p:ℝ)^2:=by
       exact_mod_cast pow_pos (mf.mp hp).2.pos 2
      rw [ldi hp_pos]
      have hnat2:(2*Y/p^2)*p^2<=2*Y:=dls _ _
      have hR2:((2*Y/p^2:ℕ):ℝ)*(p:ℝ)^2<=((2*Y:ℕ):ℝ):=by
       exact_mod_cast hnat2
      push_cast at hR2;linarith
    _=(H:ℝ)*(2*(Y:ℝ))*∑ p∈P_gt_all,(1:ℝ)/(p:ℝ)^2:=by
      rw [mul_sum];apply sum_congr rfl;intro p _;ring
    _<=(H:ℝ)*(2*(Y:ℝ))*(1/((H^3:ℕ):ℝ)):=by
      apply ml _ (by positivity)
      calc
       ∑ p∈P_gt_all,(1:ℝ)/(p:ℝ)^2
        <= ∑ n∈Ioc (H^3) (2*Y),(1:ℝ)/(n:ℝ)^2:=ssub (fsub _ _) (fun _ _ _ => by positivity)
       _<=1/((H^3:ℕ):ℝ):=sum_inv_sq_Ioc_le (H^3) (2*Y) (o1p 3 H (by omega))
    _=(H:ℝ)*(2*(Y:ℝ))/(H:ℝ)^3:=by push_cast;ring
  have hH4_ge:(H:ℝ)/8<=((H/4:ℕ):ℝ):=by
   have hnat2:H<=8*(H/4):=by omega
   have hR2:(H:ℝ)<=8*((H/4:ℕ):ℝ):=by exact_mod_cast hnat2
   linarith
  have hHpos:(0:ℝ) < (H:ℝ):=by exact_mod_cast (by omega:0 < H)
  have hmul:(H:ℝ)/8*(E_gt.card:ℝ)<=(H:ℝ)*(2*(Y:ℝ))/(H:ℝ)^3:=by
   nlinarith
  have hcancel:(E_gt.card:ℝ)<=16*(Y:ℝ)/(H:ℝ)^3:=by
   have h1:(H:ℝ)/8*(16*(Y:ℝ)/(H:ℝ)^3)=(H:ℝ)*(2*(Y:ℝ))/(H:ℝ)^3:=by
    field_simp;ring
   nlinarith
  exact hcancel
 have hEmid:(E_mid.card:ℝ)<=(2^31:ℝ)*(Y:ℝ)/(H:ℝ)^3:=by
  let Pset:=(Ioc (Nat.sqrt H) (H^3)).filter Nat.Prime
  have hPset:∀ p∈Pset,p.Prime:=fun _ hp => (mf.mp hp).2
  have hE_sub:E_mid⊆Icc 1 Y:=by
   intro m hm
   have hmI:=(mf.mp (mf.mp hm).1).1
   simp only [mioc] at hmI
   exact micc.mpr ⟨by omega,hmI.2⟩
  have hE_prop:∀ m∈E_mid,H/4<=(Pset.filter (fun p => ∃ j∈Icc 1 H,p^2∣m+j)).card:=by
   intro m hm
   have h1:=(mf.mp hm).2
   have heq:(Ioc (Nat.sqrt H) (H^3)).filter
     (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)=Pset.filter (fun p => ∃ j∈Icc 1 H,p^2∣m+j):=by
    ext p;simp only [Pset,mf];tauto
   rwa [← heq]
  have hcrt:=kt_crt Y H 6 (H/4) (by omega) (by omega) Pset hPset E_mid hE_sub hE_prop
  have hchoose_lb:((H:ℝ)/16)^6/((6:ℕ).factorial:ℝ)<=((Nat.choose (H/4) 6:ℕ):ℝ):=by
   have hdesc:(H/8)^6<=(H/4).descFactorial 6:=by
    have hstep:H/8<=H/4 - 5:=by omega
    have h0:H/4 - 5<=H/4:=by omega
    have h1:H/4 - 5<=H/4 - 1:=by omega
    have h2:H/4 - 5<=H/4 - 2:=by omega
    have h3:H/4 - 5<=H/4 - 3:=by omega
    have h4:H/4 - 5<=H/4 - 4:=by omega
    have hpow6:(H/4 - 5)^6=(H/4 - 5)*((H/4 - 5)*((H/4 - 5)*((H/4 - 5)*((H/4 - 5)*((H/4 - 5)*1))))):=by
     ring
    have hdesc_eq:(H/4).descFactorial 6=(H/4 - 5)*((H/4 - 4)*((H/4 - 3)*((H/4 - 2)*((H/4 - 1)*((H/4)*1))))):=by
     simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero]
    calc
     (H/8)^6<=(H/4 - 5)^6:=npl hstep 6
     _<=(H/4).descFactorial 6:=by
      rw [hpow6,hdesc_eq]
      gcongr
   have hfac_eq:(H/4).descFactorial 6=(6:ℕ).factorial*Nat.choose (H/4) 6:=Nat.descFactorial_eq_factorial_mul_choose (H/4) 6
   have hH16:(H:ℝ)/16<=((H/8:ℕ):ℝ):=by
    have hnat2:H<=16*(H/8):=by omega
    have hR2:(H:ℝ)<=16*((H/8:ℕ):ℝ):=by exact_mod_cast hnat2
    linarith
   have hpowR:((H:ℝ)/16)^6<=(((H/4).descFactorial 6:ℕ):ℝ):=by
    have h1:((H:ℝ)/16)^6<=((H/8:ℕ):ℝ)^6:=by
     gcongr
    have h2:((H/8:ℕ):ℝ)^6<=(((H/4).descFactorial 6:ℕ):ℝ):=by
     exact_mod_cast hdesc
    linarith
   rw [hfac_eq] at hpowR
   push_cast at hpowR
   rw [dli (by positivity:(0:ℝ) < ((6:ℕ).factorial:ℝ))]
   linarith
  have hsqrt_pos:1<=Nat.sqrt H:=Nat.le_sqrt.mpr (by omega)
  have hsum_inv:∑ p∈Pset,(1:ℝ)/(p:ℝ)^2<=2/Real.sqrt (H:ℝ):=by
   have h1:∑ p∈Pset,(1:ℝ)/(p:ℝ)^2<=1/(Nat.sqrt H:ℝ):=by
    calc
     ∑ p∈Pset,(1:ℝ)/(p:ℝ)^2
      <= ∑ n∈Ioc (Nat.sqrt H) (H^3),(1:ℝ)/(n:ℝ)^2:=ssub (fsub _ _) (fun _ _ _ => by positivity)
     _<=1/(Nat.sqrt H:ℝ):=sum_inv_sq_Ioc_le (Nat.sqrt H) (H^3) hsqrt_pos
   have hsq_ge:Real.sqrt (H:ℝ)<=2*(Nat.sqrt H:ℝ):=by
    have hnat:H < (Nat.sqrt H+1)^2:=Nat.lt_succ_sqrt' H
    have h2:(Nat.sqrt H+1)<=2*Nat.sqrt H:=by omega
    have hH_le:(H:ℝ)<=(2*(Nat.sqrt H:ℝ))^2:=by
     have hnat2:H<=(2*Nat.sqrt H)^2:=by nlinarith
     exact_mod_cast hnat2
    exact Real.sqrt_le_iff.mpr ⟨by positivity,hH_le⟩
   have hsqrtR_pos:(0:ℝ) < Real.sqrt (H:ℝ):=Real.sqrt_pos.mpr (by exact_mod_cast (by omega:0 < H))
   have hNsqrt_pos:(0:ℝ) < (Nat.sqrt H:ℝ):=by exact_mod_cast (by omega:0 < Nat.sqrt H)
   have h2:1/(Nat.sqrt H:ℝ)<=2/Real.sqrt (H:ℝ):=by
    rw [ddi hNsqrt_pos hsqrtR_pos]
    linarith
   linarith
  have hsum_pow6:(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^6<=64/(H:ℝ)^3:=by
   have h1:(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^6<=(2/Real.sqrt (H:ℝ))^6:=by
    gcongr
   have hsq:(Real.sqrt (H:ℝ))^2=(H:ℝ):=Real.sq_sqrt (by positivity)
   have hpow:(2/Real.sqrt (H:ℝ))^6=64/(H:ℝ)^3:=by
    rw [dpow]
    have h6:(Real.sqrt (H:ℝ))^6=((Real.sqrt (H:ℝ))^2)^3:=by ring
    rw [h6,hsq]
    norm_num
   linarith
  have hPcard:(Pset.card:ℝ)^6<=(Y:ℝ)/(H:ℝ)^3:=by
   have hle:Pset.card<=H^3:=by
    calc
     Pset.card<=(Ioc (Nat.sqrt H) (H^3)).card:=cfl _ _
     _=H^3 - Nat.sqrt H:=Nat.card_Ioc _ _
     _<=H^3:=Nat.sub_le _ _
   have hpow18:(Pset.card:ℝ)^6<=(H:ℝ)^18:=by
    have hnat:Pset.card^6<=H^18:=by
     calc
      Pset.card^6<=(H^3)^6:=npl hle 6
      _=H^18:=by ring
    exact_mod_cast hnat
   have hH21:(H:ℝ)^21<=(Y:ℝ):=by
    have hnat:H^21<=Y:=ltr (npr (by omega) (by omega:21<=22)) hHY
    exact_mod_cast hnat
   have hH3_pos:(0:ℝ) < (H:ℝ)^3:=by positivity
   have h1:(H:ℝ)^18<=(Y:ℝ)/(H:ℝ)^3:=by
    rw [ldi hH3_pos]
    have:(H:ℝ)^18*(H:ℝ)^3=(H:ℝ)^21:=by ring
    linarith
   linarith
  have hE_mul:((H:ℝ)/16)^6/((6:ℕ).factorial:ℝ)*(E_mid.card:ℝ)<=(H:ℝ)^6/((6:ℕ).factorial:ℝ)*(65*(Y:ℝ)/(H:ℝ)^3):=by
   have h1:((H:ℝ)/16)^6/((6:ℕ).factorial:ℝ)*(E_mid.card:ℝ)<=((Nat.choose (H/4) 6:ℕ):ℝ)*(E_mid.card:ℝ):=mr hchoose_lb (by positivity)
   have h2:(Y:ℝ)*(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^6+(Pset.card:ℝ)^6<=65*(Y:ℝ)/(H:ℝ)^3:=by
    have hYnn:(0:ℝ)<=(Y:ℝ):=by positivity
    have hmulY:(Y:ℝ)*(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^6<=(Y:ℝ)*(64/(H:ℝ)^3):=ml hsum_pow6 hYnn
    have:(Y:ℝ)*(64/(H:ℝ)^3)+(Y:ℝ)/(H:ℝ)^3=65*(Y:ℝ)/(H:ℝ)^3:=by ring
    linarith
   have h3:(H:ℝ)^6/((6:ℕ).factorial:ℝ)*((Y:ℝ)*(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^6+(Pset.card:ℝ)^6)<=(H:ℝ)^6/((6:ℕ).factorial:ℝ)*(65*(Y:ℝ)/(H:ℝ)^3):=ml h2 (by positivity)
   linarith
  have hcoeff_pos:(0:ℝ) < ((H:ℝ)/16)^6/((6:ℕ).factorial:ℝ):=by positivity
  have hrhs_eq:(H:ℝ)^6/((6:ℕ).factorial:ℝ)*(65*(Y:ℝ)/(H:ℝ)^3)=((H:ℝ)/16)^6/((6:ℕ).factorial:ℝ)*((16^6*65:ℝ)*(Y:ℝ)/(H:ℝ)^3):=by
   ring
  have hle1:(E_mid.card:ℝ)<=(16^6*65:ℝ)*(Y:ℝ)/(H:ℝ)^3:=by
   rw [hrhs_eq] at hE_mul
   exact le_of_mul_le_mul_left hE_mul hcoeff_pos
  have hconst:(16^6*65:ℝ)<=(2^31:ℝ):=by norm_num
  have hYH_nn:(0:ℝ)<=(Y:ℝ)/(H:ℝ)^3:=by positivity
  have h2:(16^6*65:ℝ)*((Y:ℝ)/(H:ℝ)^3)<=(2^31:ℝ)*((Y:ℝ)/(H:ℝ)^3):=mr hconst hYH_nn
  rw [mul_div_assoc] at hle1 ⊢
  linarith
 have hMstar:(Mstar Y H:ℝ)<=(E_mid.card:ℝ)+(E_gt.card:ℝ):=by
  have hnat:Mstar Y H<=E_mid.card+E_gt.card:=ltr (clc hcover) (cul _ _)
  exact_mod_cast hnat
 have hHpos:(0:ℝ) < (H:ℝ):=by exact_mod_cast (by omega:0 < H)
 have hcomb:(Mstar Y H:ℝ)<=((2^31:ℝ)+16)*(Y:ℝ)/(H:ℝ)^3:=by
  have:(2^31:ℝ)*(Y:ℝ)/(H:ℝ)^3+16*(Y:ℝ)/(H:ℝ)^3=((2^31:ℝ)+16)*(Y:ℝ)/(H:ℝ)^3:=by ring
  linarith
 have hmul:(H:ℝ)^2*(((2^31:ℝ)+16)*(Y:ℝ)/(H:ℝ)^3)=((2^31:ℝ)+16)*(Y:ℝ)/(H:ℝ):=by
  field_simp
 have h32:((2^31:ℝ)+16)*(Y:ℝ)/(H:ℝ)<=(2^32:ℝ)*(Y:ℝ)/(H:ℝ):=by
  apply div_le_div_of_nonneg_right _ (lol hHpos)
  have hYnn:(0:ℝ)<=(Y:ℝ):=by positivity
  nlinarith
 nlinarith
def natRoot (r N:ℕ):ℕ:=((range (N+2)).filter (fun k => k^r<=N)).sup id
lemma natRoot_pow_le (r N:ℕ) (hr:1<=r):(natRoot r N)^r<=N:=by
 unfold natRoot
 have hmem:0∈(range (N+2)).filter (fun k => k^r<=N):=by
  rw [mf,mrng]
  refine ⟨by omega,?_⟩
  rw [zero_pow (by omega)]
  exact Nat.zero_le N
 have hne:((range (N+2)).filter (fun k => k^r<=N)).Nonempty:=⟨0,hmem⟩
 obtain ⟨k,hk_mem,hk_eq⟩:=exists_mem_eq_sup _ hne id
 rw [hk_eq]
 exact (mf.mp hk_mem).2
lemma le_natRoot (r N k:ℕ) (hr:1<=r) (hk:k^r<=N):k<=natRoot r N:=by
 unfold natRoot
 have hk_le:k<=N:=ltr (Nat.le_self_pow (by omega) k) hk
 have hmem:k∈(range (N+2)).filter (fun j => j^r<=N):=by
  rw [mf,mrng]
  exact ⟨by omega,hk⟩
 exact le_sup (f:=id) hmem
lemma lt_succ_natRoot_pow (r N:ℕ) (hr:1<=r):N < (natRoot r N+1)^r:=by
 by_contra hle;push Not at hle
 have:=le_natRoot r N (natRoot r N+1) hr hle
 omega
lemma t1_pb (Y H P R:ℕ) (hP:16<=P) (hR:4<=R)
  (E:Finset ℕ) (hE_sub:E⊆Icc 1 Y)
  (hE_prop:∀ m∈E,R<=((Ioc P (2*P)).filter
   (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card) :
  (E.card:ℝ)<=(4*(H:ℝ)^2/(R:ℝ)^2)*((Y:ℝ)*(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2+(P:ℝ)^2):=by
 let Pset:=(Ioc P (2*P)).filter Nat.Prime
 have hPset:∀ p∈Pset,p.Prime:=fun _ hp => (mf.mp hp).2
 have hprop:∀ m∈E,R<=(Pset.filter (fun p => ∃ j∈Icc 1 H,p^2∣m+j)).card:=by
  intro m hm
  have h1:=hE_prop m hm
  have heq:(Ioc P (2*P)).filter (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)=Pset.filter (fun p => ∃ j∈Icc 1 H,p^2∣m+j):=by
   ext p;simp only [Pset,mf];tauto
  rwa [← heq]
 have hcrt:=kt_crt Y H 2 R (by omega) (by omega) Pset hPset E hE_sub hprop
 have hchoose_lb:(R:ℝ)^2/4<=((Nat.choose R 2:ℕ):ℝ):=by
  have h1:2*Nat.choose R 2=R*(R - 1):=by
   have hdesc:=Nat.descFactorial_eq_factorial_mul_choose R 2
   have h2:R.descFactorial 2=(R - 1)*R:=by
    simp [Nat.descFactorial_succ,Nat.descFactorial_zero]
   have hf:(2:ℕ).factorial=2:=by norm_num
   rw [h2,hf] at hdesc
   linarith
  have h2:R^2<=4*Nat.choose R 2:=by
   have hR4:2*(R - 1)>=R:=by omega
   nlinarith
  have hR2:(R:ℝ)^2<=4*((Nat.choose R 2:ℕ):ℝ):=by exact_mod_cast h2
  linarith
 have hsum_dyad:=sp_dy P hP
 have hsum_sq:(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^2<=(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2:=by
  gcongr
 have hPcard:(Pset.card:ℝ)^2<=(P:ℝ)^2:=by
  have hle:Pset.card<=P:=by
   calc
    Pset.card<=(Ioc P (2*P)).card:=cfl _ _
    _=2*P - P:=Nat.card_Ioc _ _
    _=P:=by omega
  have hleR:(Pset.card:ℝ)<=(P:ℝ):=by exact_mod_cast hle
  gcongr
 have hfac2:((2:ℕ).factorial:ℝ)=2:=by norm_num
 rw [hfac2] at hcrt
 have hRpos:(0:ℝ) < (R:ℝ)^2:=by exact_mod_cast (by positivity:0 < R^2)
 have hLHS:(R:ℝ)^2/4*(E.card:ℝ)<=(H:ℝ)^2/2*((Y:ℝ)*(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2+(P:ℝ)^2):=by
  have h1:(R:ℝ)^2/4*(E.card:ℝ)<=((Nat.choose R 2:ℕ):ℝ)*(E.card:ℝ):=mr hchoose_lb (by positivity)
  have h2:(Y:ℝ)*(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^2+(Pset.card:ℝ)^2<=(Y:ℝ)*(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2+(P:ℝ)^2:=by
   have hYnn:(0:ℝ)<=(Y:ℝ):=by positivity
   nlinarith
  have h3:(H:ℝ)^2/2*((Y:ℝ)*(∑ p∈Pset,(1:ℝ)/(p:ℝ)^2)^2+(Pset.card:ℝ)^2)<=(H:ℝ)^2/2*((Y:ℝ)*(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2+(P:ℝ)^2):=ml h2 (by positivity)
  linarith
 have hmul:(R:ℝ)^2/4*(E.card:ℝ)<=(R:ℝ)^2/4*((4*(H:ℝ)^2/(R:ℝ)^2)*((Y:ℝ)*(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2+(P:ℝ)^2)):=by
  have hrhs:(R:ℝ)^2/4*((4*(H:ℝ)^2/(R:ℝ)^2)*((Y:ℝ)*(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2+(P:ℝ)^2))=(H:ℝ)^2*((Y:ℝ)*(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2+(P:ℝ)^2):=by
   field_simp
  have hhalf:(H:ℝ)^2/2*((Y:ℝ)*(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2+(P:ℝ)^2)<=(H:ℝ)^2*((Y:ℝ)*(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2+(P:ℝ)^2):=by
   have hnn:0<=(H:ℝ)^2*((Y:ℝ)*(36/((P:ℝ)*(Nat.log 2 P:ℝ)))^2+(P:ℝ)^2):=by
    positivity
   linarith
  linarith
 exact le_of_mul_le_mul_left hmul (by positivity)
lemma sum_fin_diffs {n:ℕ} (f:Fin (n+1)->ℕ) (hmono:Monotone f) :
  ∑ i:Fin n,(f i.succ - f i.castSucc)=f (Fin.last n) - f 0:=by
 induction n with
 | zero => simp
 | succ k ih =>
  rw [Fin.sum_univ_castSucc]
  let f':Fin (k+1)->ℕ:=fun j => f j.castSucc
  have hf'_mono:Monotone f':=fun a b hab => hmono (Fin.castSucc_le_castSucc_iff.mpr hab)
  have hih:=ih f' hf'_mono
  have hcast_eq:∑ i:Fin k,(f i.castSucc.succ - f i.castSucc.castSucc)=∑ i:Fin k,(f' i.succ - f' i.castSucc):=by
   apply sum_congr rfl;intro i _;rfl
  rw [hcast_eq,hih]
  have h0:f 0<=f (Fin.last k).castSucc:=hmono (Fin.zero_le _)
  have h1:f (Fin.last k).castSucc<=f (Fin.last (k+1)):=hmono (Fin.le_last _)
  change (f (Fin.last k).castSucc - f 0)+(f (Fin.last (k+1)) - f (Fin.last k).castSucc)=f (Fin.last (k+1)) - f 0
  omega
lemma ring_identity_consec (p d b a2 h':ℤ)
  (hdiff:b*p^2 - a2*(2*p*d+d^2)=h') :
  (2*p+d)*(b*(2*p - d) - 4*a2*d)=4*h' - b*d^2:=by
 linear_combination 4*hdiff
def t2B (Y H P d:ℕ):ℕ:=12*Y*d/P^3+H/P^2+2
def t2Q (Y H P D:ℕ):Finset (((ℕ × ℕ) × ℕ) × ℕ):=(((Ioc P (2*P) ×ˢ Icc 1 D) ×ˢ Icc 1 (t2B Y H P D)) ×ˢ
  Icc 1 (2*Y/P^2)).filter (fun q =>
  let p:=q.1.1.1
  let d:=q.1.1.2
  let b:=q.1.2
  let a2:=q.2
  p+d<=2*P/\b<=t2B Y H P d/\Y<=9*a2*P^2 /\
  |((b:ℤ)*(p:ℤ)^2 - (a2:ℤ)*(2*(p:ℤ)*(d:ℤ)+(d:ℤ)^2))| < (H:ℤ))
def t2K (q:((ℕ × ℕ) × ℕ) × ℕ):ℤ:=(q.1.2:ℤ)*(2*(q.1.1.1:ℤ) - (q.1.1.2:ℤ)) - 4*(q.2:ℤ)*(q.1.1.2:ℤ)
lemma t2_dc (Y H P R:ℕ)
  (_hY:100<=Y) (_hH_pos:1<=H) (h2H:2*H<=Y)
  (hHP:H<=P) (hR4:4<=R) (hRH:R<=H)
  (E:Finset ℕ) (hE_sub:E⊆Ioc (Y/2) Y)
  (hE_prop:∀ m∈E,R<=((Ioc P (2*P)).filter
   (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card) :
  (R/4)*E.card<=H*(t2Q Y H P (2*P/R)).card:=by
 let D:=2*P/R
 have hP_pos:0 < P:=by omega
 have hD_ge:2<=D:=by
  have:2*R<=2*P:=by omega
  exact (ldim (by omega)).mpr (by linarith)
 let Qall:=t2Q Y H P D
 let hits (m:ℕ) (q:((ℕ × ℕ) × ℕ) × ℕ):Prop:=m < (q.2+q.1.2)*q.1.1.1^2/\(q.2+q.1.2)*q.1.1.1^2<=m+H
 let _instH:DecidableRel hits:=fun _ _ => Classical.propDecidable _
 have hE_hits:∀ m∈E,R/4<=(Qall.filter (hits m)).card:=by
  intro m hm
  have hmI:Y/2 < m/\m<=Y:=mioc.mp (hE_sub hm)
  let Pm:=(Ioc P (2*P)).filter (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)
  have hr:R<=Pm.card:=hE_prop m hm
  have hr1:1<=Pm.card:=by omega
  let n:=Pm.card - 1
  have hcard_eq:Pm.card=n+1:=by omega
  let e:Fin (n+1) ↪o ℕ:=Pm.orderEmbOfFin hcard_eq
  have he_mem:∀ idx:Fin (n+1),e idx∈Pm:=fun idx => Finset.orderEmbOfFin_mem Pm hcard_eq idx
  have he_Ioc:∀ idx:Fin (n+1),P < e idx/\e idx<=2*P:=fun idx => mioc.mp (mf.mp (he_mem idx)).1
  let gap (i:Fin n):ℕ:=e i.succ - e i.castSucc
  have hgap_pos:∀ i:Fin n,1<=gap i:=by
   intro i
   have hlt:e i.castSucc < e i.succ:=e.strictMono Fin.castSucc_lt_succ
   dsimp [gap];omega
  have hsum_gaps:∑ i:Fin n,gap i<=P:=by
   have htele:=sum_fin_diffs e e.monotone
   have h1:=he_Ioc 0
   have h2:=he_Ioc (Fin.last n)
   change ∑ i:Fin n,(e i.succ - e i.castSucc)<=P
   rw [htele]
   omega
  let GoodI:=Finset.univ.filter (fun i:Fin n => gap i<=D)
  let BadI:=Finset.univ.filter (fun i:Fin n => D < gap i)
  have hBad_card:2*BadI.card < R:=by
   have h1:BadI.card*(D+1)<=P:=by
    calc
     BadI.card*(D+1)=∑ _i∈BadI,(D+1):=by rw [sum_const,smul_eq_mul]
     _<=∑ i∈BadI,gap i:=sls (fun i hi => (mf.mp hi).2)
     _<=∑ i:Fin n,gap i:=sum_le_sum_of_subset (subset_univ _)
     _<=P:=hsum_gaps
   have hD_lt:2*P < R*(D+1):=lmd (2*P) (by omega:0 < R)
   by_cases hB0:BadI.card=0
   · omega
   ·
    have hlt2:BadI.card*(2*P) < BadI.card*(R*(D+1)):=Nat.mul_lt_mul_of_pos_left hD_lt (by omega)
    have h3:BadI.card*(R*(D+1))=R*(BadI.card*(D+1)):=by ring
    have h4:R*(BadI.card*(D+1))<=R*P:=nml R h1
    have hmul2:(2*BadI.card)*P < R*P:=by linarith only [hlt2,h3,h4]
    exact Nat.lt_of_mul_lt_mul_right hmul2
  have hGood_ge:R/4<=GoodI.card:=by
   have hpart:GoodI.card+BadI.card=n:=by
    have hdisj:Disjoint GoodI BadI:=by
     rw [disjoint_left]
     intro i h1 h2;simp only [GoodI,BadI,mf] at h1 h2;omega
    have hunion:GoodI∪BadI=Finset.univ:=by
     ext i;simp only [GoodI,BadI,mun,mf,mem_univ,true_and,iff_true]
     exact le_or_gt (gap i) D
    rw [← card_union_of_disjoint hdisj,hunion,card_univ,Fintype.card_fin]
   have hn_ge:R<=n+1:=by omega
   omega
  have hex_ja:∀ idx:Fin (n+1),∃ j∈Icc 1 H,∃ a:ℕ,m+j=a*(e idx)^2:=by
   intro idx
   rcases (mf.mp (he_mem idx)).2.2 with ⟨j,hj,⟨a,ha⟩⟩
   exact ⟨j,hj,a,by rw [mcom];exact ha⟩
  choose fj hfj_mem fa hfa_eq using hex_ja
  let mkQ (i:Fin n):((ℕ × ℕ) × ℕ) × ℕ:=(((e i.castSucc,gap i),fa i.castSucc - fa i.succ),fa i.succ)
  have hcard_le:GoodI.card<=(Qall.filter (hits m)).card:=by
   refine card_le_card_of_injOn mkQ ?_ ?_
   ·
    intro i hi
    rw [mem_coe] at hi ⊢
    have hi_le:gap i<=D:=(mf.mp hi).2
    let p:=e i.castSucc
    let q:=e i.succ
    let d:=gap i
    let a1:=fa i.castSucc
    let a2:=fa i.succ
    let j1:=fj i.castSucc
    let j2:=fj i.succ
    have hp_Ioc:P < p/\p<=2*P:=he_Ioc i.castSucc
    have hq_Ioc:P < q/\q<=2*P:=he_Ioc i.succ
    have hd_pos:1<=d:=hgap_pos i
    have hpq_lt:p < q:=e.strictMono Fin.castSucc_lt_succ
    have hpq:p+d=q:=by dsimp [p,q,d,gap];omega
    have hj1:1<=j1/\j1<=H:=micc.mp (hfj_mem i.castSucc)
    have hj2:1<=j2/\j2<=H:=micc.mp (hfj_mem i.succ)
    have hm1:m+j1=a1*p^2:=hfa_eq i.castSucc
    have hm2:m+j2=a2*q^2:=hfa_eq i.succ
    have ha2_pos:1<=a2:=by
     by_contra h0;push Not at h0
     have:a2=0:=by omega
     rw [this] at hm2;simp at hm2;omega
    have ha2_le:a2<=2*Y/P^2:=by
     refine (ldim (pow_pos hP_pos 2)).mpr ?_
     have h1:a2*P^2<=a2*q^2:=nml a2 (npl (lol hq_Ioc.1) 2)
     omega
    have ha2_lb:Y<=9*a2*P^2:=by
     have h1:a2*q^2<=a2*(2*P)^2:=nml a2 (npl hq_Ioc.2 2)
     have h2:a2*(2*P)^2=4*(a2*P^2):=by ring
     have h3:Y/2 < 4*(a2*P^2):=by omega
     have h4:Y<=2*(Y/2)+1:=by omega
     have h5:1<=a2*P^2:=Nat.mul_pos ha2_pos (pow_pos hP_pos 2)
     have h6:9*a2*P^2=9*(a2*P^2):=by ring
     omega
    have ha_lt:a2 < a1:=by
     by_contra hle;push Not at hle
     have hq2:p^2+2*P < q^2:=by
      have:p+1<=q:=by omega
      nlinarith only [this,hp_Ioc.1]
     have h1:a1*p^2+2*P < a2*q^2:=by nlinarith only [hq2,ha2_pos,hle]
     omega
    let b:=a1 - a2
    have hb_pos:1<=b:=by omega
    have hb_add:a2+b=a1:=by omega
    have hdiff_eq:(b:ℤ)*(p:ℤ)^2 - (a2:ℤ)*(2*(p:ℤ)*(d:ℤ)+(d:ℤ)^2)=(j1:ℤ) - (j2:ℤ):=by
     have hm1Z:(m:ℤ)+(j1:ℤ)=(a1:ℤ)*(p:ℤ)^2:=by exact_mod_cast hm1
     have hm2Z:(m:ℤ)+(j2:ℤ)=(a2:ℤ)*(q:ℤ)^2:=by exact_mod_cast hm2
     have hqZ:(q:ℤ)=(p:ℤ)+(d:ℤ):=by exact_mod_cast hpq.symm
     have hbZ:(a1:ℤ)=(a2:ℤ)+(b:ℤ):=by exact_mod_cast hb_add.symm
     rw [hqZ] at hm2Z
     rw [hbZ] at hm1Z
     linarith only [hm1Z,hm2Z]
    have hdiff_abs:|(b:ℤ)*(p:ℤ)^2 - (a2:ℤ)*(2*(p:ℤ)*(d:ℤ)+(d:ℤ)^2)| < (H:ℤ):=by
     rw [hdiff_eq,abs_lt]
     omega
    have hb_le_d:b<=t2B Y H P d:=by
     have hbp2:b*p^2<=a2*(2*p*d+d^2)+H:=by
      have h1:(b:ℤ)*(p:ℤ)^2<=(a2:ℤ)*(2*(p:ℤ)*(d:ℤ)+(d:ℤ)^2)+(H:ℤ):=by
       have:=(abs_lt.mp hdiff_abs).2
       linarith only [this]
      exact_mod_cast h1
     have h2pd:2*p*d+d^2<=6*P*d:=by
      have hdp:d<=2*P:=by omega
      nlinarith only [hp_Ioc.2,hdp,hd_pos]
     have ha2P2:a2*P^2<=2*Y:=by
      have h1:a2*P^2<=a2*q^2:=nml a2 (npl (lol hq_Ioc.1) 2)
      omega
     have hP4:b*P^4<=12*Y*P*d+H*P^2:=by
      have h1:b*P^2<=b*p^2:=nml b (npl (lol hp_Ioc.1) 2)
      have h2:a2*(2*p*d+d^2)<=a2*(6*P*d):=nml a2 h2pd
      have h2':b*P^2<=a2*(6*P*d)+H:=by omega
      have h3:b*P^2*P^2<=(a2*(6*P*d)+H)*P^2:=nmr (P^2) h2'
      have h4:b*P^2*P^2=b*P^4:=by ring
      have h5:(a2*(6*P*d)+H)*P^2=(a2*P^2)*(6*P*d)+H*P^2:=by ring
      have h6:(a2*P^2)*(6*P*d)<=(2*Y)*(6*P*d):=nmr _ ha2P2
      have h7:(2*Y)*(6*P*d)=12*Y*P*d:=by ring
      omega
     have hdiv1:12*Y*P*d < (12*Y*d/P^3+1)*P^4:=by
      have hlt:=lmd (12*Y*d) (pow_pos hP_pos 3)
      have hmul:=Nat.mul_lt_mul_of_pos_right hlt hP_pos
      have hl:12*Y*d*P=12*Y*P*d:=by ring
      have hr:P^3*(12*Y*d/P^3+1)*P=(12*Y*d/P^3+1)*P^4:=by ring
      omega
     have hdiv2:H*P^2 < (H/P^2+1)*P^4:=by
      have hlt:=lmd H (pow_pos hP_pos 2)
      have hmul:=Nat.mul_lt_mul_of_pos_right hlt (pow_pos hP_pos 2)
      have hr:P^2*(H/P^2+1)*P^2=(H/P^2+1)*P^4:=by ring
      omega
     have hsum_div:12*Y*P*d+H*P^2 < (12*Y*d/P^3+H/P^2+2)*P^4:=by
      have:(12*Y*d/P^3+1)*P^4+(H/P^2+1)*P^4=(12*Y*d/P^3+H/P^2+2)*P^4:=by ring
      omega
     have hlt_b:b*P^4 < (12*Y*d/P^3+H/P^2+2)*P^4:=lt_of_le_of_lt hP4 hsum_div
     exact lol (Nat.lt_of_mul_lt_mul_right hlt_b)
    have hb_le_D:b<=t2B Y H P D:=by
     dsimp [t2B] at hb_le_d ⊢
     have h1:12*Y*d<=12*Y*D:=nml _ hi_le
     have h2:12*Y*d/P^3<=12*Y*D/P^3:=ddlr h1
     omega
    rw [mf]
    refine ⟨?_,?_⟩
    ·
     dsimp only [Qall,t2Q]
     rw [mf]
     refine ⟨?_,hpq.le.trans hq_Ioc.2,hb_le_d,ha2_lb,hdiff_abs⟩
     rw [mem_product,mem_product,mem_product]
     exact ⟨⟨⟨mioc.mpr hp_Ioc,micc.mpr ⟨hd_pos,hi_le⟩⟩,micc.mpr ⟨hb_pos,hb_le_D⟩⟩,micc.mpr ⟨ha2_pos,ha2_le⟩⟩
    ·
     dsimp [hits,mkQ]
     change m < (a2+b)*p^2/\(a2+b)*p^2<=m+H
     rw [hb_add,← hm1]
     omega
   ·
    intro i₁ _ i₂ _ heq
    dsimp [mkQ] at heq
    have hp_eq:e i₁.castSucc=e i₂.castSucc:=congrArg (fun x => x.1.1.1) heq
    exact Fin.castSucc_injective _ (e.injective hp_eq)
  exact ltr hGood_ge hcard_le
 have hq_hits:∀ q∈Qall,(E.filter (fun m => hits m q)).card<=H:=by
  intro q _
  let N:=(q.2+q.1.2)*q.1.1.1^2
  have hsub:E.filter (fun m => hits m q)⊆Ico (N - H) N:=by
   intro m hm
   rw [mf] at hm
   rw [mico]
   dsimp [hits] at hm
   omega
  calc
   (E.filter (fun m => hits m q)).card<=(Ico (N - H) N).card:=clc hsub
   _=N - (N - H):=Nat.card_Ico _ _
   _<=H:=by omega
 calc
  (R/4)*E.card=∑ _m∈E,(R/4):=by rw [sum_const,smul_eq_mul,mcom]
  _<=∑ m∈E,(Qall.filter (hits m)).card:=sls hE_hits
  _=∑ q∈Qall,(E.filter (fun m => hits m q)).card:=by
    have h1:∀ m∈E,(Qall.filter (hits m)).card=∑ q∈Qall,if hits m q then 1 else 0:=fun _ _ => by rw [card_filter]
    have h2:∀ q∈Qall,(E.filter (fun m => hits m q)).card=∑ m∈E,if hits m q then 1 else 0:=fun _ _ => by rw [card_filter]
    rw [sum_congr rfl h1,sum_comm,sum_congr rfl h2]
  _<=∑ _q∈Qall,H:=sls hq_hits
  _=H*Qall.card:=by rw [sum_const,smul_eq_mul,mcom]
lemma t2_q0 (Y H P D:ℕ)
  (hY:100<=Y) (hH_pos:1<=H) (h2H:2*H<=Y) (hHP:H<=P) (hP_le:P<=Y) :
  let D0:=natRoot 3 (36*H*P^3/Y)+1
  let L:=Nat.log 2 (40*Y^2)+2
  (((t2Q Y H P D).filter (fun q => t2K q=0)).card:ℝ)<=12*(Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2:=by
 intro D0 L
 let Amax:=2*Y/P^2
 let Q0:=(t2Q Y H P D).filter (fun q => t2K q=0)
 let Target:=(Icc 1 Amax ×ˢ Icc 1 D0).sigma (fun ad => (4*ad.1*ad.2).divisors)
 have hQ0_le:Q0.card<=Target.card:=by
  refine card_le_card_of_injOn (fun q => ⟨(q.2,q.1.1.2),q.1.2⟩) ?_ ?_
  ·
   intro q hq
   rw [mem_coe,mf] at hq
   have hqall:=hq.1
   have hK0:t2K q=0:=hq.2
   rw [t2Q,mf,mem_product,mem_product,mem_product] at hqall
   rcases hqall with ⟨⟨⟨⟨hp,hd⟩,hb⟩,ha2⟩,hpd,_,ha2_lb,hdiff_abs⟩
   rw [mioc] at hp;rw [micc] at hd hb ha2
   let p:=q.1.1.1;let d:=q.1.1.2;let b:=q.1.2;let a2:=q.2
   let h':ℤ:=(b:ℤ)*(p:ℤ)^2 - (a2:ℤ)*(2*(p:ℤ)*(d:ℤ)+(d:ℤ)^2)
   have hring:=ring_identity_consec p d b a2 h' rfl
   have hK0':(b:ℤ)*(2*(p:ℤ) - (d:ℤ)) - 4*(a2:ℤ)*(d:ℤ)=0:=hK0
   rw [hK0',mul_zero] at hring
   have hbd2_lt:b*d^2 < 4*H:=by
    have hZ:(b:ℤ)*(d:ℤ)^2=4*h':=by linarith
    have hh':h' < (H:ℤ):=(abs_lt.mp hdiff_abs).2
    have hZ2:(b:ℤ)*(d:ℤ)^2 < 4*(H:ℤ):=by linarith
    exact_mod_cast hZ2
   have h2p_ge_d:d<=2*p:=by omega
   have hmul_eq:b*(2*p - d)=4*a2*d:=by
    have hZ:(b:ℤ)*((2*p - d:ℕ):ℤ)=4*(a2:ℤ)*(d:ℤ):=by
     rw [ncs h2p_ge_d];push_cast;linarith
    exact_mod_cast hZ
   have hd_le_D0:d<=D0:=by
    have h2pd_le:2*p - d<=4*P:=by omega
    have h1:4*(a2*d)<=4*(b*P):=by
     have:b*(2*p - d)<=b*(4*P):=nml b h2pd_le
     linarith only [hmul_eq,this]
    have h2:a2*d<=b*P:=by omega
    have h3:Y*d<=9*b*P^3:=by
     have h4:Y*d<=(9*a2*P^2)*d:=nmr d ha2_lb
     have h5:(9*a2*P^2)*d=9*(a2*d)*P^2:=by ring
     have h6:9*(a2*d)*P^2<=9*(b*P)*P^2:=by
      have:=nml 9 h2
      exact nmr (P^2) this
     have h7:9*(b*P)*P^2=9*b*P^3:=by ring
     omega
    have h4:Y*d^3<=36*H*P^3:=by
     have h5:Y*d*d^2<=(9*b*P^3)*d^2:=nmr (d^2) h3
     have h6:Y*d*d^2=Y*d^3:=by ring
     have h7:(9*b*P^3)*d^2=9*(b*d^2)*P^3:=by ring
     have h8:9*(b*d^2)*P^3<=9*(4*H)*P^3:=by
      have:=nml 9 (lol hbd2_lt)
      exact nmr (P^3) this
     have h9:9*(4*H)*P^3=36*H*P^3:=by ring
     omega
    have hdiv:d^3<=36*H*P^3/Y:=(ldim (by omega:0 < Y)).mpr (by rw [mcom];exact h4)
    have hrt:=le_natRoot 3 (36*H*P^3/Y) d (by omega) hdiv
    dsimp [D0];omega
   rw [mem_coe,Finset.mem_sigma,mem_product,micc,micc,Nat.mem_divisors]
   refine ⟨⟨ha2,⟨hd.1,hd_le_D0⟩⟩,⟨⟨2*p - d,hmul_eq.symm⟩,?_⟩⟩
   exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (by omega:0 < 4) ha2.1) hd.1)
  ·
   intro q₁ hq₁ q₂ hq₂ heq
   rw [mem_coe,mf] at hq₁ hq₂
   have h1:q₁.2=q₂.2:=congrArg (fun x => x.1.1) heq
   have h2:q₁.1.1.2=q₂.1.1.2:=congrArg (fun x => x.1.2) heq
   have h3:q₁.1.2=q₂.1.2:=congrArg (fun x => x.2) heq
   have hK1:t2K q₁=0:=hq₁.2
   have hK2:t2K q₂=0:=hq₂.2
   have hb1_pos:(q₁.1.2:ℤ)≠0:=by
    have hqall:=hq₁.1
    rw [t2Q,mf,mem_product,mem_product,mem_product] at hqall
    have:=(micc.mp hqall.1.1.2).1
    omega
   have hp_eq:q₁.1.1.1=q₂.1.1.1:=by
    have heqZ:(q₁.1.2:ℤ)*(2*(q₁.1.1.1:ℤ) - (q₁.1.1.2:ℤ))=(q₁.1.2:ℤ)*(2*(q₂.1.1.1:ℤ) - (q₁.1.1.2:ℤ)):=by
     dsimp [t2K] at hK1 hK2
     rw [← h1,← h2,← h3] at hK2
     linarith
    have hcancel:=mul_left_cancel₀ hb1_pos heqZ
    omega
   rcases q₁ with ⟨⟨⟨p1,d1⟩,b1⟩,a1⟩
   rcases q₂ with ⟨⟨⟨p2,d2⟩,b2⟩,a2⟩
   dsimp at h1 h2 h3 hp_eq
   subst h1;subst h2;subst h3;subst hp_eq;rfl
 have hTarget_card:(Target.card:ℝ)<=12*(Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2:=by
  rw [Finset.card_sigma,Finset.sum_product]
  have htau4:∀ a2∈Icc 1 Amax,∀ d∈Icc 1 D0,(4*a2*d).divisors.card<=3*a2.divisors.card*d.divisors.card:=by
   intro a2 ha2 d hd
   rw [micc] at ha2 hd
   have h1:=tau_mul_le (4*a2) d (by omega) (by omega)
   have h2:=tau_mul_le 4 a2 (by omega) (by omega)
   have h4:(4:ℕ).divisors.card=3:=by decide
   rw [h4] at h2
   calc
    (4*a2*d).divisors.card<=(4*a2).divisors.card*d.divisors.card:=h1
    _<=(3*a2.divisors.card)*d.divisors.card:=nmr _ h2
  have hnat:∑ a2∈Icc 1 Amax,∑ d∈Icc 1 D0,(4*a2*d).divisors.card<=3*(∑ a2∈Icc 1 Amax,a2.divisors.card)*(∑ d∈Icc 1 D0,d.divisors.card):=by
   calc
    ∑ a2∈Icc 1 Amax,∑ d∈Icc 1 D0,(4*a2*d).divisors.card
     <= ∑ a2∈Icc 1 Amax,∑ d∈Icc 1 D0,3*a2.divisors.card*d.divisors.card:=sls (fun a2 ha2 => sls (fun d hd => htau4 a2 ha2 d hd))
    _=3*(∑ a2∈Icc 1 Amax,a2.divisors.card)*(∑ d∈Icc 1 D0,d.divisors.card):=by
      symm
      calc
       3*(∑ a2∈Icc 1 Amax,a2.divisors.card)*(∑ d∈Icc 1 D0,d.divisors.card)
        = (∑ a2∈Icc 1 Amax,3*a2.divisors.card)*(∑ d∈Icc 1 D0,d.divisors.card):=by
         congr 1;rw [mul_sum]
       _=∑ a2∈Icc 1 Amax,(3*a2.divisors.card)*(∑ d∈Icc 1 D0,d.divisors.card):=sum_mul _ _ _
       _=∑ a2∈Icc 1 Amax,∑ d∈Icc 1 D0,3*a2.divisors.card*d.divisors.card:=by
         apply sum_congr rfl;intro a2 _;rw [mul_sum]
  have hcast:((∑ a2∈Icc 1 Amax,∑ d∈Icc 1 D0,(4*a2*d).divisors.card:ℕ):ℝ)<=3*(∑ a2∈Icc 1 Amax,(a2.divisors.card:ℝ))*(∑ d∈Icc 1 D0,(d.divisors.card:ℝ)):=by exact_mod_cast hnat
  have hA_sum:∑ a2∈Icc 1 Amax,(a2.divisors.card:ℝ)<=(2*(Y:ℝ)/(P:ℝ)^2)*(L:ℝ):=by
   by_cases hA0:Amax=0
   · simp [hA0];positivity
   ·
    have h1:=sum_tau_le Amax (pnz hA0)
    have hA_le_Y:Amax<=40*Y^2:=by
     have:Amax<=2*Y:=dvls _ _
     nlinarith only [this,hY]
    have hlogA:(Nat.log 2 Amax:ℝ)+1<=(L:ℝ):=by
     have:Nat.log 2 Amax<=Nat.log 2 (40*Y^2):=lmr hA_le_Y
     have:Nat.log 2 Amax+1<=L:=by dsimp [L];omega
     exact_mod_cast this
    have hA_div:(Amax:ℝ)<=2*(Y:ℝ)/(P:ℝ)^2:=by
     rw [ldi (by exact_mod_cast pow_pos (by omega:0 < P) 2)]
     have hnat2:Amax*P^2<=2*Y:=dls _ _
     have hR2:(Amax:ℝ)*(P:ℝ)^2<=((2*Y:ℕ):ℝ):=by exact_mod_cast hnat2
     push_cast at hR2;linarith only [hR2]
    have hnn:(0:ℝ)<=(Nat.log 2 Amax:ℝ)+1:=by positivity
    nlinarith only [h1,hlogA,hA_div,hnn]
  have hD0_sum:∑ d∈Icc 1 D0,(d.divisors.card:ℝ)<=(D0:ℝ)*(L:ℝ):=by
   have h1:=sum_tau_le D0 (by dsimp [D0];omega)
   have hD0_le:D0<=40*Y^2:=by
    have harg:36*H*P^3/Y<=36*Y^3:=by
     have hP3:P^3<=Y^3:=npl hP_le 3
     have hHY:H<=Y:=by omega
     have hmul:H*P^3<=Y*Y^3:=nmm hHY hP3
     have h36:36*(H*P^3)<=36*(Y*Y^3):=nml 36 hmul
     have hle_mul:36*H*P^3<=Y*(36*Y^3):=by
      have hl:36*H*P^3=36*(H*P^3):=by ring
      have hr:Y*(36*Y^3)=36*(Y*Y^3):=by ring
      omega
     exact Nat.div_le_of_le_mul hle_mul
    have hrt_le:natRoot 3 (36*H*P^3/Y)<=4*Y:=by
     by_contra hgt;push Not at hgt
     have hpow:=natRoot_pow_le 3 (36*H*P^3/Y) (by omega)
     have h64:(4*Y)^3 < natRoot 3 (36*H*P^3/Y)^3:=Nat.pow_lt_pow_left hgt (by omega)
     have h64':(4*Y)^3=64*Y^3:=by ring
     omega
    dsimp [D0];nlinarith only [hrt_le,hY]
   have hlogD0:(Nat.log 2 D0:ℝ)+1<=(L:ℝ):=by
    have:Nat.log 2 D0<=Nat.log 2 (40*Y^2):=lmr hD0_le
    have:Nat.log 2 D0+1<=L:=by dsimp [L];omega
    exact_mod_cast this
   have hD0nn:(0:ℝ)<=(D0:ℝ):=by positivity
   nlinarith only [h1,hlogD0,hD0nn]
  have hprod:3*(∑ a2∈Icc 1 Amax,(a2.divisors.card:ℝ))*(∑ d∈Icc 1 D0,(d.divisors.card:ℝ))<=3*((2*(Y:ℝ)/(P:ℝ)^2)*(L:ℝ))*((D0:ℝ)*(L:ℝ)):=by
   have h1:0<=∑ a2∈Icc 1 Amax,(a2.divisors.card:ℝ):=sum_nonneg (fun _ _ => by positivity)
   have h2:0<=∑ d∈Icc 1 D0,(d.divisors.card:ℝ):=sum_nonneg (fun _ _ => by positivity)
   nlinarith only [h1,h2,hA_sum,hD0_sum]
  have h6:3*((2*(Y:ℝ)/(P:ℝ)^2)*(L:ℝ))*((D0:ℝ)*(L:ℝ))<=12*(Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2:=by
   have hnn:0<=(Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2:=by positivity
   have heq1:3*((2*(Y:ℝ)/(P:ℝ)^2)*(L:ℝ))*((D0:ℝ)*(L:ℝ))=6*((Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2):=by ring
   have heq2:12*(Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2=12*((Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2):=by ring
   linarith only [heq1,heq2,hnn]
  linarith only [hcast,hprod,h6]
 have hQ0R:(Q0.card:ℝ)<=(Target.card:ℝ):=by exact_mod_cast hQ0_le
 linarith
lemma t2_fib (Y H P R:ℕ)
  (hH_pos:1<=H) (hHP:H<=P) (hR4:4<=R) :
  let D:=2*P/R
  let Bmax (d:ℕ):=t2B Y H P d
  let Kmax (d:ℕ):ℕ:=(Bmax d*d^2+4*H)/(2*P)
  (((t2Q Y H P D).filter (fun q => t2K q≠0)).card:ℝ)<=∑ d∈Icc 1 D,∑ _b∈Icc 1 (Bmax d),2*∑ k∈Icc 1 (Kmax d),(4*(H:ℝ)/(k:ℝ)+1):=by
 intro D Bmax Kmax
 let Qne:=(t2Q Y H P D).filter (fun q => t2K q≠0)
 let fkey (q:((ℕ × ℕ) × ℕ) × ℕ):((ℕ × ℕ) × ℕ) × Bool:=(((q.1.1.2,q.1.2),(t2K q).natAbs),decide (0<=t2K q))
 let Keys:Finset (((ℕ × ℕ) × ℕ) × Bool):=(Icc 1 D).biUnion (fun d =>
   ((Icc 1 (Bmax d)).biUnion (fun b =>
    (Icc 1 (Kmax d)).biUnion (fun k =>
     {(((d,b),k),true),(((d,b),k),false)}))))
 have hmaps:∀ q∈Qne,fkey q∈Keys:=by
  intro q hq
  rw [mf] at hq
  have hqall:=hq.1
  have hKne:t2K q≠0:=hq.2
  rw [t2Q,mf,mem_product,mem_product,mem_product] at hqall
  rcases hqall with ⟨⟨⟨⟨hp,hd⟩,hb⟩,ha2⟩,_,hb_d,_,hdiff_abs⟩
  rw [mioc] at hp;rw [micc] at hd hb ha2
  let p:=q.1.1.1;let d:=q.1.1.2;let b:=q.1.2;let a2:=q.2
  let h':ℤ:=(b:ℤ)*(p:ℤ)^2 - (a2:ℤ)*(2*(p:ℤ)*(d:ℤ)+(d:ℤ)^2)
  have hring:=ring_identity_consec p d b a2 h' rfl
  have hKabs_pos:1<=(t2K q).natAbs:=Int.natAbs_pos.mpr hKne
  have hKabs_le:(t2K q).natAbs<=Kmax d:=by
   have h1:(2*P)*(t2K q).natAbs<=(2*p+d)*(t2K q).natAbs:=nmr _ (by omega)
   have h2:(((2*p+d)*(t2K q).natAbs:ℕ):ℤ)=|(2*(p:ℤ)+(d:ℤ))*t2K q|:=by
    rw [abs_mul,abs_of_nonneg (by positivity:(0:ℤ)<=2*(p:ℤ)+(d:ℤ))]
    push_cast;rfl
   have h3:|(2*(p:ℤ)+(d:ℤ))*t2K q|<=(b:ℤ)*(d:ℤ)^2+4*(H:ℤ):=by
    change |(2*(p:ℤ)+(d:ℤ))*((b:ℤ)*(2*(p:ℤ) - (d:ℤ)) - 4*(a2:ℤ)*(d:ℤ))|<=_
    rw [hring]
    have hh:=abs_lt.mp hdiff_abs
    rw [abs_le]
    have hbdnn:(0:ℤ)<=(b:ℤ)*(d:ℤ)^2:=by positivity
    constructor <;> linarith only [hh.1,hh.2,hbdnn]
   have h4:(2*p+d)*(t2K q).natAbs<=b*d^2+4*H:=by
    have hZ:(((2*p+d)*(t2K q).natAbs:ℕ):ℤ)<=((b*d^2+4*H:ℕ):ℤ):=by
     rw [h2];push_cast;linarith only [h3]
    exact_mod_cast hZ
   have h5:(t2K q).natAbs*(2*P)<=Bmax d*d^2+4*H:=by
    have hbd:b*d^2<=Bmax d*d^2:=nmr (d^2) hb_d
    have hcomm:(t2K q).natAbs*(2*P)=2*P*(t2K q).natAbs:=mcom _ _
    omega
   exact (ldim (by omega:0 < 2*P)).mpr h5
  simp only [Keys,fkey,mbu,micc,mem_insert,mem_singleton]
  refine ⟨d,hd,b,⟨hb.1,hb_d⟩,(t2K q).natAbs,⟨hKabs_pos,hKabs_le⟩,?_⟩
  cases decide (0<=t2K q) <;> simp [d,b]
 have hfiber_card:∀ key∈Keys,(Qne.filter (fun q => fkey q=key)).card<=4*H/key.1.2+1:=by
  intro key hkey
  let F:=Qne.filter (fun q => fkey q=key)
  change F.card<=4*H/key.1.2+1
  have hk_pos:1<=key.1.2:=by
   simp only [Keys,mbu,micc,mem_insert,mem_singleton] at hkey
   rcases hkey with ⟨d,_,b,_,k,hk,hEq | hEq⟩ <;> subst hEq <;> exact hk.1
  by_cases hemp:F.Nonempty
  ·
   let Pvals:=F.image (fun q => q.1.1.1)
   have hPvals_ne:Pvals.Nonempty:=hemp.image _
   let pmin:=Pvals.min' hPvals_ne
   have hpmin_mem:pmin∈Pvals:=min'_mem Pvals hPvals_ne
   rcases mim.mp hpmin_mem with ⟨q0,hq0_F,hq0_p⟩
   have hF_inj:∀ q₁∈F,∀ q₂∈F,q₁.1.1.1=q₂.1.1.1->q₁=q₂:=by
    intro q₁ hq₁ q₂ hq₂ hp_eq
    have hk1:fkey q₁=key:=(mf.mp hq₁).2
    have hk2:fkey q₂=key:=(mf.mp hq₂).2
    have hd_eq:q₁.1.1.2=q₂.1.1.2:=congrArg (fun x => x.1.1.1) (hk1.trans hk2.symm)
    have hb_eq:q₁.1.2=q₂.1.2:=congrArg (fun x => x.1.1.2) (hk1.trans hk2.symm)
    have hK_eq:t2K q₁=t2K q₂:=by
     have habs:(t2K q₁).natAbs=(t2K q₂).natAbs:=congrArg (fun x => x.1.2) (hk1.trans hk2.symm)
     have hsgn:decide (0<=t2K q₁)=decide (0<=t2K q₂):=congrArg (fun x => x.2) (hk1.trans hk2.symm)
     by_cases h1:0<=t2K q₁
     ·
      have h2:0<=t2K q₂:=by simpa [h1] using hsgn.symm
      omega
     ·
      have h2:¬ 0<=t2K q₂:=by simpa [h1] using hsgn.symm
      omega
    have hd_pos:1<=q₁.1.1.2:=by
     have hqall:=(mf.mp (mf.mp hq₁).1).1
     rw [t2Q,mf,mem_product,mem_product,mem_product] at hqall
     exact (micc.mp hqall.1.1.1.2).1
    have ha2_eq:q₁.2=q₂.2:=by
     dsimp [t2K] at hK_eq
     rw [hp_eq,hd_eq,hb_eq] at hK_eq
     have hdZ:(4*(q₂.1.1.2:ℤ))≠0:=by omega
     have hmul:(q₁.2:ℤ)*(4*(q₂.1.1.2:ℤ))=(q₂.2:ℤ)*(4*(q₂.1.1.2:ℤ)):=by
      linarith only [hK_eq]
     have:=mul_right_cancel₀ hdZ hmul
     exact_mod_cast this
    rcases q₁ with ⟨⟨⟨p1,d1⟩,b1⟩,a1⟩
    rcases q₂ with ⟨⟨⟨p2,d2⟩,b2⟩,a2⟩
    dsimp at hp_eq hd_eq hb_eq ha2_eq
    subst hp_eq;subst hd_eq;subst hb_eq;subst ha2_eq;rfl
   have hPvals_sub:Pvals⊆Icc pmin (pmin+4*H/key.1.2):=by
    intro p hp
    have hge:pmin<=p:=min'_le Pvals p hp
    rcases mim.mp hp with ⟨q,hq_F,rfl⟩
    rw [micc]
    refine ⟨hge,?_⟩
    have hk0:fkey q0=key:=(mf.mp hq0_F).2
    have hkq:fkey q=key:=(mf.mp hq_F).2
    have hd_eq:q0.1.1.2=q.1.1.2:=congrArg (fun x => x.1.1.1) (hk0.trans hkq.symm)
    have hb_eq:q0.1.2=q.1.2:=congrArg (fun x => x.1.1.2) (hk0.trans hkq.symm)
    have hK_eq:t2K q0=t2K q:=by
     have habs:(t2K q0).natAbs=(t2K q).natAbs:=congrArg (fun x => x.1.2) (hk0.trans hkq.symm)
     have hsgn:decide (0<=t2K q0)=decide (0<=t2K q):=congrArg (fun x => x.2) (hk0.trans hkq.symm)
     by_cases h1:0<=t2K q0
     ·
      have h2:0<=t2K q:=by simpa [h1] using hsgn.symm
      omega
     ·
      have h2:¬ 0<=t2K q:=by simpa [h1] using hsgn.symm
      omega
    have hq0_all:=(mf.mp (mf.mp hq0_F).1).1
    have hq_all:=(mf.mp (mf.mp hq_F).1).1
    rw [t2Q,mf] at hq0_all hq_all
    let h0':ℤ:=(q0.1.2:ℤ)*(q0.1.1.1:ℤ)^2 -
      (q0.2:ℤ)*(2*(q0.1.1.1:ℤ)*(q0.1.1.2:ℤ)+(q0.1.1.2:ℤ)^2)
    let h1':ℤ:=(q.1.2:ℤ)*(q.1.1.1:ℤ)^2 -
      (q.2:ℤ)*(2*(q.1.1.1:ℤ)*(q.1.1.2:ℤ)+(q.1.1.2:ℤ)^2)
    have hr0:=ring_identity_consec q0.1.1.1 q0.1.1.2 q0.1.2 q0.2 h0' rfl
    have hr1:=ring_identity_consec q.1.1.1 q.1.1.2 q.1.2 q.2 h1' rfl
    have habs0:|h0'| < (H:ℤ):=hq0_all.2.2.2.2
    have habs1:|h1'| < (H:ℤ):=hq_all.2.2.2.2
    have hdiffK:2*((q.1.1.1:ℤ) - (q0.1.1.1:ℤ))*t2K q=4*(h1' - h0'):=by
     change (2*(q0.1.1.1:ℤ)+(q0.1.1.2:ℤ))*t2K q0=4*h0' - (q0.1.2:ℤ)*(q0.1.1.2:ℤ)^2 at hr0
     change (2*(q.1.1.1:ℤ)+(q.1.1.2:ℤ))*t2K q=4*h1' - (q.1.2:ℤ)*(q.1.1.2:ℤ)^2 at hr1
     rw [hd_eq,hb_eq,hK_eq] at hr0
     linarith only [hr0,hr1]
    have hlt_8H:2*((q.1.1.1 - pmin)*key.1.2) < 8*H:=by
     have hKabs_eq:(t2K q).natAbs=key.1.2:=congrArg (fun x => x.1.2) hkq
     have hZ:(2*(((q.1.1.1 - pmin:ℕ):ℤ)*((t2K q).natAbs:ℤ))) < 8*(H:ℤ):=by
      rw [ncs hge,← hq0_p]
      have h1:|2*((q.1.1.1:ℤ) - (q0.1.1.1:ℤ))*t2K q|=2*(((q.1.1.1:ℤ) - (q0.1.1.1:ℤ))*((t2K q).natAbs:ℤ)):=by
       rw [abs_mul,abs_of_nonneg (by omega),Int.natCast_natAbs];ring
      rw [← h1,hdiffK]
      have h2:=abs_lt.mp habs0
      have h3:=abs_lt.mp habs1
      rw [abs_lt];constructor <;> linarith only [h2.1,h2.2,h3.1,h3.2]
     rw [hKabs_eq] at hZ
     exact_mod_cast hZ
    have hle_div:q.1.1.1 - pmin<=4*H/key.1.2:=by
     have:(q.1.1.1 - pmin)*key.1.2<=4*H:=by omega
     exact (ldim (by omega:0 < key.1.2)).mpr this
    omega
   calc
    F.card=Pvals.card:=(Finset.card_image_of_injOn (fun q₁ hq₁ q₂ hq₂ h =>
     hF_inj q₁ (mem_coe.mp hq₁) q₂ (mem_coe.mp hq₂) h)).symm
    _<=(Icc pmin (pmin+4*H/key.1.2)).card:=clc hPvals_sub
    _=4*H/key.1.2+1:=by rw [Nat.card_Icc,add_assoc,Nat.add_sub_cancel_left]
  ·
   rw [not_nonempty_iff_eq_empty.mp hemp,card_empty]
   exact Nat.zero_le _
 have hQne_nat:Qne.card<=∑ key∈Keys,(4*H/key.1.2+1):=by
  have hfib:=Finset.card_eq_sum_card_fiberwise hmaps
  rw [hfib]
  exact sls hfiber_card
 have hQne_R:(Qne.card:ℝ)<=∑ key∈Keys,(4*(H:ℝ)/(key.1.2:ℝ)+1):=by
  have hcast:(Qne.card:ℝ)<=∑ key∈Keys,(((4*H/key.1.2:ℕ):ℝ)+1):=by
   exact_mod_cast hQne_nat
  refine ltr hcast (sls fun key hkey => ?_)
  have hk_pos:(0:ℝ) < (key.1.2:ℝ):=by
   simp only [Keys,mbu,micc,mem_insert,mem_singleton] at hkey
   rcases hkey with ⟨d,_,b,_,k,hk,hEq | hEq⟩ <;> subst hEq <;>
    exact_mod_cast (by omega:0 < k)
  have hdiv:((4*H/key.1.2:ℕ):ℝ)<=4*(H:ℝ)/(key.1.2:ℝ):=by
   rw [ldi hk_pos]
   have hnat2:(4*H/key.1.2)*key.1.2<=4*H:=dls _ _
   have hR2:((4*H/key.1.2:ℕ):ℝ)*(key.1.2:ℝ)<=((4*H:ℕ):ℝ):=by exact_mod_cast hnat2
   push_cast at hR2;linarith only [hR2]
  linarith only [hdiv]
 calc
  (Qne.card:ℝ)<=∑ key∈Keys,(4*(H:ℝ)/(key.1.2:ℝ)+1):=hQne_R
  _<=∑ d∈Icc 1 D,∑ key∈((Icc 1 (Bmax d)).biUnion (fun b =>
     (Icc 1 (Kmax d)).biUnion (fun k =>
      {(((d,b),k),true),(((d,b),k),false)}))),(4*(H:ℝ)/(key.1.2:ℝ)+1):=sbu_nn _ _ _ (fun _ _ _ _ => by positivity)
  _<=∑ d∈Icc 1 D,∑ b∈Icc 1 (Bmax d),∑ key∈((Icc 1 (Kmax d)).biUnion (fun k =>
      {(((d,b),k),true),(((d,b),k),false)})),(4*(H:ℝ)/(key.1.2:ℝ)+1):=sls (fun _ _ => sbu_nn _ _ _ (fun _ _ _ _ => by positivity))
  _<=∑ d∈Icc 1 D,∑ _b∈Icc 1 (Bmax d),∑ k∈Icc 1 (Kmax d),∑ key∈({(((d,_b),k),true),(((d,_b),k),false)}:Finset _),(4*(H:ℝ)/(key.1.2:ℝ)+1):=sls (fun _ _ => sls (fun _ _ => sbu_nn _ _ _ (fun _ _ _ _ => by positivity)))
  _=∑ d∈Icc 1 D,∑ _b∈Icc 1 (Bmax d),2*∑ k∈Icc 1 (Kmax d),(4*(H:ℝ)/(k:ℝ)+1):=by
    apply sum_congr rfl;intro d _
    apply sum_congr rfl;intro b _
    rw [mul_sum]
    apply sum_congr rfl;intro k _
    rw [Finset.sum_pair (by simp)]
    ring
lemma t2_qne (Y H P R:ℕ)
  (hY:100<=Y) (hH_pos:1<=H) (hHP:H<=P) (hP_le:P<=Y) (hR4:4<=R) (hRH:R<=H) :
  let L:=Nat.log 2 (40*Y^2)+2
  (((t2Q Y H P (2*P/R)).filter (fun q => t2K q≠0)).card:ℝ)<=5000*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)+(Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5)+(Y:ℝ)/(R:ℝ)^4+(H:ℝ)*(L:ℝ)*(P:ℝ)/(R:ℝ)+(P:ℝ)^2/(R:ℝ)^3):=by
 intro L
 let D:=2*P/R
 have hD_le:D<=2*P:=dvls _ _
 have hP_pos:0 < P:=by omega
 let Bmax (d:ℕ):=t2B Y H P d
 let Kmax (d:ℕ):ℕ:=(Bmax d*d^2+4*H)/(2*P)
 have hfib:=t2_fib Y H P R hH_pos hHP hR4
 have hinner_k:∀ d∈Icc 1 D,2*∑ k∈Icc 1 (Kmax d),(4*(H:ℝ)/(k:ℝ)+1)<=8*(H:ℝ)*(L:ℝ)+2*(Kmax d:ℝ):=by
  intro d hd
  rw [micc] at hd
  by_cases hK0:Kmax d=0
  · simp [hK0];positivity
  ·
   have hharm:=harmonic_le_log2 (Kmax d) (pnz hK0)
   have hKmax_le:Kmax d<=40*Y^2:=by
    have hd2P:d<=2*P:=ltr hd.2 hD_le
    have hB_le:Bmax d<=12*Y+3:=by
     dsimp [Bmax,t2B]
     have h1:12*Y*d/P^3<=12*Y:=by
      have hdP3:d<=P^3:=by
       have hP4:4<=P:=by omega
       have:2*P<=P*P*P:=by nlinarith only [hP4]
       have:P*P*P=P^3:=by ring
       omega
      have hle:12*Y*d<=P^3*(12*Y):=by
       have:=nml (12*Y) hdP3
       linarith only [this]
      exact Nat.div_le_of_le_mul hle
     have h2:H/P^2<=1:=by
      have:H<=P^2*1:=by nlinarith only [hHP,hP_pos]
      exact Nat.div_le_of_le_mul this
     omega
    dsimp [Kmax]
    have hnum:Bmax d*d^2+4*H<=(2*P)*(40*Y^2):=by
     have hd2:d^2<=4*P^2:=by nlinarith only [hd2P]
     have h1:Bmax d*d^2<=(12*Y+3)*(4*P^2):=nmm hB_le hd2
     have h3:4*P^2<=4*Y*P:=by nlinarith only [hP_le,hP_pos]
     have h4:(12*Y+3)*(4*P^2)<=(12*Y+3)*(4*Y*P):=nml _ h3
     have h5:(12*Y+3)*(4*Y*P)+4*H<=(2*P)*(40*Y^2):=by
      nlinarith only [hY,hHP,hP_le,hP_pos]
     omega
    exact Nat.div_le_of_le_mul hnum
   have hlogK:(Nat.log 2 (Kmax d):ℝ)+1<=(L:ℝ):=by
    have:Nat.log 2 (Kmax d)<=Nat.log 2 (40*Y^2):=lmr hKmax_le
    have:Nat.log 2 (Kmax d)+1<=L:=by dsimp [L];omega
    exact_mod_cast this
   have hsplit_sum:∑ k∈Icc 1 (Kmax d),(4*(H:ℝ)/(k:ℝ)+1)=4*(H:ℝ)*(∑ k∈Icc 1 (Kmax d),(1:ℝ)/(k:ℝ))+(Kmax d:ℝ):=by
    rw [sum_add_distrib,sum_const,Nat.card_Icc,add_tsub_cancel_right,nsmul_eq_mul,mul_one,mul_sum]
    congr 1;apply sum_congr rfl;intro k _;ring
   rw [hsplit_sum]
   have hHnn:(0:ℝ)<=(H:ℝ):=by positivity
   nlinarith only [hharm,hlogK,hHnn]
 have hPpos:(0:ℝ) < (P:ℝ):=by exact_mod_cast hP_pos
 have hRpos:(0:ℝ) < (R:ℝ):=by exact_mod_cast (by omega:0 < R)
 have hB_bound:∀ d∈Icc 1 D,(Bmax d:ℝ)<=12*(Y:ℝ)*(d:ℝ)/(P:ℝ)^3+3:=by
  intro d _
  dsimp [Bmax,t2B];push_cast
  have h1:((12*Y*d/P^3:ℕ):ℝ)<=12*(Y:ℝ)*(d:ℝ)/(P:ℝ)^3:=by
   rw [ldi (by positivity:(0:ℝ) < (P:ℝ)^3)]
   have hnat:=dls (12*Y*d) (P^3)
   have hR2:((12*Y*d/P^3:ℕ):ℝ)*(P:ℝ)^3<=((12*Y*d:ℕ):ℝ):=by exact_mod_cast hnat
   push_cast at hR2;linarith only [hR2]
  have h2:((H/P^2:ℕ):ℝ)<=1:=by
   have hnat:H/P^2<=1:=by
    have:H<=P^2:=by nlinarith only [hHP,hP_pos]
    exact (Nat.div_le_iff_le_mul_add_pred (pow_pos hP_pos 2)).mpr (by omega)
   exact_mod_cast hnat
  linarith only [h1,h2]
 have hK_bound:∀ d∈Icc 1 D,8*(H:ℝ)*(L:ℝ)+2*(Kmax d:ℝ)<=12*(H:ℝ)*(L:ℝ)+12*(Y:ℝ)*(d:ℝ)^3/(P:ℝ)^4+3*(d:ℝ)^2/(P:ℝ):=by
  intro d hd
  have h1:(Kmax d:ℝ)<=((Bmax d:ℝ)*(d:ℝ)^2+4*(H:ℝ))/(2*(P:ℝ)):=by
   rw [ldi (by positivity:(0:ℝ) < 2*(P:ℝ))]
   have hnat:=dls (Bmax d*d^2+4*H) (2*P)
   have hR2:(Kmax d:ℝ)*((2*P:ℕ):ℝ)<=((Bmax d*d^2+4*H:ℕ):ℝ):=by exact_mod_cast hnat
   push_cast at hR2;linarith only [hR2]
  have hB:=hB_bound d hd
  have h2:(Bmax d:ℝ)*(d:ℝ)^2+4*(H:ℝ)<=12*(Y:ℝ)*(d:ℝ)^3/(P:ℝ)^3+3*(d:ℝ)^2+4*(H:ℝ):=by
   have hmul:=mr hB (sq_nonneg (d:ℝ))
   have heq:(12*(Y:ℝ)*(d:ℝ)/(P:ℝ)^3+3)*(d:ℝ)^2=12*(Y:ℝ)*(d:ℝ)^3/(P:ℝ)^3+3*(d:ℝ)^2:=by ring
   linarith only [hmul,heq]
  have h3:2*(Kmax d:ℝ)<=12*(Y:ℝ)*(d:ℝ)^3/(P:ℝ)^4+3*(d:ℝ)^2/(P:ℝ)+4*(H:ℝ)/(P:ℝ):=by
   have hdiv:2*(((Bmax d:ℝ)*(d:ℝ)^2+4*(H:ℝ))/(2*(P:ℝ)))=((Bmax d:ℝ)*(d:ℝ)^2+4*(H:ℝ))/(P:ℝ):=by field_simp
   have hdiv2:(12*(Y:ℝ)*(d:ℝ)^3/(P:ℝ)^3+3*(d:ℝ)^2+4*(H:ℝ))/(P:ℝ)=12*(Y:ℝ)*(d:ℝ)^3/(P:ℝ)^4+3*(d:ℝ)^2/(P:ℝ)+4*(H:ℝ)/(P:ℝ):=by
    field_simp
   have hdiv_le:((Bmax d:ℝ)*(d:ℝ)^2+4*(H:ℝ))/(P:ℝ)<=(12*(Y:ℝ)*(d:ℝ)^3/(P:ℝ)^3+3*(d:ℝ)^2+4*(H:ℝ))/(P:ℝ):=div_le_div_of_nonneg_right h2 (lol hPpos)
   linarith only [h1,hdiv,hdiv2,hdiv_le]
  have hHP_le:4*(H:ℝ)/(P:ℝ)<=4*(H:ℝ)*(L:ℝ):=by
   have h1P:(1:ℝ)<=(P:ℝ):=by exact_mod_cast (by omega:1<=P)
   have h1L:(1:ℝ)<=(L:ℝ):=by exact_mod_cast (by dsimp [L];omega:1<=L)
   have hHnn:(0:ℝ)<=(H:ℝ):=by positivity
   have h4H:4*(H:ℝ)/(P:ℝ)<=4*(H:ℝ):=by
    rw [dli hPpos];nlinarith only [h1P,hHnn]
   nlinarith only [h4H,h1L,hHnn]
  linarith only [h3,hHP_le]
 have hDR:(D:ℝ)<=2*(P:ℝ)/(R:ℝ):=by
  rw [ldi hRpos]
  have hnat:=dls (2*P) R
  have hR2:(D:ℝ)*(R:ℝ)<=((2*P:ℕ):ℝ):=by exact_mod_cast hnat
  push_cast at hR2;linarith only [hR2]
 have hD_pow:∀ m:ℕ,∑ d∈Icc 1 D,(d:ℝ)^m<=(2*(P:ℝ)/(R:ℝ))^(m+1):=by
  intro m
  calc
   ∑ d∈Icc 1 D,(d:ℝ)^m
    <= ∑ _d∈Icc 1 D,(D:ℝ)^m:=by
     apply sls;intro d hd
     have hdle:(d:ℝ)<=(D:ℝ):=by exact_mod_cast (micc.mp hd).2
     gcongr
   _=(D:ℝ)^(m+1):=by
     rw [sum_const,Nat.card_Icc,add_tsub_cancel_right,nsmul_eq_mul,pow_succ']
   _<=(2*(P:ℝ)/(R:ℝ))^(m+1):=by gcongr
 have hsum_d:∑ d∈Icc 1 D,∑ _b∈Icc 1 (Bmax d),2*∑ k∈Icc 1 (Kmax d),(4*(H:ℝ)/(k:ℝ)+1)<=∑ d∈Icc 1 D,(12*(Y:ℝ)*(d:ℝ)/(P:ℝ)^3+3)*(12*(H:ℝ)*(L:ℝ)+12*(Y:ℝ)*(d:ℝ)^3/(P:ℝ)^4+3*(d:ℝ)^2/(P:ℝ)):=by
  apply sls
  intro d hd
  rw [sum_const,Nat.card_Icc,add_tsub_cancel_right,nsmul_eq_mul]
  have h1:=hB_bound d hd
  have h2:=ltr (hinner_k d hd) (hK_bound d hd)
  have hnn1:0<=2*∑ k∈Icc 1 (Kmax d),(4*(H:ℝ)/(k:ℝ)+1):=mul_nonneg (by norm_num) (sum_nonneg (fun _ _ => by positivity))
  have hnn2:0<=12*(Y:ℝ)*(d:ℝ)/(P:ℝ)^3+3:=by positivity
  exact mlm h1 h2 hnn1 hnn2
 have hexpand:∑ d∈Icc 1 D,(12*(Y:ℝ)*(d:ℝ)/(P:ℝ)^3+3)*(12*(H:ℝ)*(L:ℝ)+12*(Y:ℝ)*(d:ℝ)^3/(P:ℝ)^4+3*(d:ℝ)^2/(P:ℝ))=(144*(Y:ℝ)*(H:ℝ)*(L:ℝ)/(P:ℝ)^3)*(∑ d∈Icc 1 D,(d:ℝ)^1)+(144*(Y:ℝ)^2/(P:ℝ)^7)*(∑ d∈Icc 1 D,(d:ℝ)^4)+(72*(Y:ℝ)/(P:ℝ)^4)*(∑ d∈Icc 1 D,(d:ℝ)^3)+(36*(H:ℝ)*(L:ℝ))*(∑ d∈Icc 1 D,(d:ℝ)^0)+(9/(P:ℝ))*(∑ d∈Icc 1 D,(d:ℝ)^2):=by
  simp only [mul_sum,← sum_add_distrib]
  apply sum_congr rfl;intro d _;ring
 have ht1:(144*(Y:ℝ)*(H:ℝ)*(L:ℝ)/(P:ℝ)^3)*(∑ d∈Icc 1 D,(d:ℝ)^1)<=576*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)):=by
  have h:=ml (hD_pow 1) (by positivity:0<=144*(Y:ℝ)*(H:ℝ)*(L:ℝ)/(P:ℝ)^3)
  have heq:(144*(Y:ℝ)*(H:ℝ)*(L:ℝ)/(P:ℝ)^3)*(2*(P:ℝ)/(R:ℝ))^2=576*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)):=by field_simp;ring
  linarith only [h,heq]
 have ht2:(144*(Y:ℝ)^2/(P:ℝ)^7)*(∑ d∈Icc 1 D,(d:ℝ)^4)<=4608*((Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5)):=by
  have h:=ml (hD_pow 4) (by positivity:0<=144*(Y:ℝ)^2/(P:ℝ)^7)
  have heq:(144*(Y:ℝ)^2/(P:ℝ)^7)*(2*(P:ℝ)/(R:ℝ))^5=4608*((Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5)):=by field_simp;ring
  linarith only [h,heq]
 have ht3:(72*(Y:ℝ)/(P:ℝ)^4)*(∑ d∈Icc 1 D,(d:ℝ)^3)<=1152*((Y:ℝ)/(R:ℝ)^4):=by
  have h:=ml (hD_pow 3) (by positivity:0<=72*(Y:ℝ)/(P:ℝ)^4)
  have heq:(72*(Y:ℝ)/(P:ℝ)^4)*(2*(P:ℝ)/(R:ℝ))^4=1152*((Y:ℝ)/(R:ℝ)^4):=by field_simp;ring
  linarith only [h,heq]
 have ht4:(36*(H:ℝ)*(L:ℝ))*(∑ d∈Icc 1 D,(d:ℝ)^0)<=72*((H:ℝ)*(L:ℝ)*(P:ℝ)/(R:ℝ)):=by
  have h:=ml (hD_pow 0) (by positivity:0<=36*(H:ℝ)*(L:ℝ))
  have heq:(36*(H:ℝ)*(L:ℝ))*(2*(P:ℝ)/(R:ℝ))^1=72*((H:ℝ)*(L:ℝ)*(P:ℝ)/(R:ℝ)):=by field_simp;ring
  linarith only [h,heq]
 have ht5:(9/(P:ℝ))*(∑ d∈Icc 1 D,(d:ℝ)^2)<=72*((P:ℝ)^2/(R:ℝ)^3):=by
  have h:=ml (hD_pow 2) (by positivity:0<=9/(P:ℝ))
  have heq:(9/(P:ℝ))*(2*(P:ℝ)/(R:ℝ))^3=72*((P:ℝ)^2/(R:ℝ)^3):=by field_simp;ring
  linarith only [h,heq]
 have hnn1:0<=(Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2):=by positivity
 have hnn2:0<=(Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5):=by positivity
 have hnn3:0<=(Y:ℝ)/(R:ℝ)^4:=by positivity
 have hnn4:0<=(H:ℝ)*(L:ℝ)*(P:ℝ)/(R:ℝ):=by positivity
 have hnn5:0<=(P:ℝ)^2/(R:ℝ)^3:=by positivity
 linarith only [hfib,hsum_d,hexpand,ht1,ht2,ht3,ht4,ht5,hnn1,hnn2,hnn3,hnn4,hnn5]
lemma t2_ri (Y H P R:ℕ)
  (hY:100<=Y) (hH_pos:1<=H) (h2H:2*H<=Y)
  (hHP:H<=P) (hP_le:P<=Y) (hR4:4<=R) (hRH:R<=H)
  (E:Finset ℕ) (hE_sub:E⊆Ioc (Y/2) Y)
  (hE_prop:∀ m∈E,R<=((Ioc P (2*P)).filter
   (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card) :
  let D0:=natRoot 3 (36*H*P^3/Y)+1
  let L:=Nat.log 2 (40*Y^2)+2
  (E.card:ℝ)<=(8*(H:ℝ)/(R:ℝ))*(12*(Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2+5000*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)+(Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5)+(Y:ℝ)/(R:ℝ)^4+(H:ℝ)*(L:ℝ)*(P:ℝ)/(R:ℝ)+(P:ℝ)^2/(R:ℝ)^3)):=by
 intro D0 L
 let Qall:=t2Q Y H P (2*P/R)
 have hdouble:=t2_dc Y H P R hY hH_pos h2H hHP hR4 hRH E hE_sub hE_prop
 have hQ0:=t2_q0 Y H P (2*P/R) hY hH_pos h2H hHP hP_le
 have hQne:=t2_qne Y H P R hY hH_pos hHP hP_le hR4 hRH
 have hQsplit:Qall.card<=(Qall.filter (fun q => t2K q=0)).card+(Qall.filter (fun q => t2K q≠0)).card:=by
  have hu:Qall⊆Qall.filter (fun q => t2K q=0)∪Qall.filter (fun q => t2K q≠0):=by
   intro q hq;rw [mun,mf,mf]
   by_cases h:t2K q=0
   · exact Or.inl ⟨hq,h⟩
   · exact Or.inr ⟨hq,h⟩
  exact ltr (clc hu) (cul _ _)
 have hR4_ge:(R:ℝ)/8<=((R/4:ℕ):ℝ):=by
  have hnat:R<=8*(R/4):=by omega
  have hR2:(R:ℝ)<=8*((R/4:ℕ):ℝ):=by exact_mod_cast hnat
  linarith
 have hdoubleR:((R/4:ℕ):ℝ)*(E.card:ℝ)<=(H:ℝ)*(((Qall.filter (fun q => t2K q=0)).card:ℝ)+((Qall.filter (fun q => t2K q≠0)).card:ℝ)):=by
  have hnat:(R/4)*E.card<=H*((Qall.filter (fun q => t2K q=0)).card+(Qall.filter (fun q => t2K q≠0)).card):=ltr hdouble (nml H hQsplit)
  exact_mod_cast hnat
 have hRpos:(0:ℝ) < (R:ℝ):=by exact_mod_cast (by omega:0 < R)
 have hLHS:(R:ℝ)/8*(E.card:ℝ)<=(H:ℝ)*(12*(Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2+5000*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)+(Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5)+(Y:ℝ)/(R:ℝ)^4+(H:ℝ)*(L:ℝ)*(P:ℝ)/(R:ℝ)+(P:ℝ)^2/(R:ℝ)^3)):=by
  have h1:(R:ℝ)/8*(E.card:ℝ)<=((R/4:ℕ):ℝ)*(E.card:ℝ):=mr hR4_ge (by positivity)
  have h2:(H:ℝ)*(((Qall.filter (fun q => t2K q=0)).card:ℝ)+((Qall.filter (fun q => t2K q≠0)).card:ℝ))<=_:=ml (add_le_add hQ0 hQne) (by positivity)
  linarith
 have hcancel:(R:ℝ)/8*((8*(H:ℝ)/(R:ℝ))*(12*(Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2+5000*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)+(Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5)+(Y:ℝ)/(R:ℝ)^4+(H:ℝ)*(L:ℝ)*(P:ℝ)/(R:ℝ)+(P:ℝ)^2/(R:ℝ)^3)))=(H:ℝ)*(12*(Y:ℝ)/(P:ℝ)^2*(D0:ℝ)*(L:ℝ)^2+5000*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)+(Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5)+(Y:ℝ)/(R:ℝ)^4+(H:ℝ)*(L:ℝ)*(P:ℝ)/(R:ℝ)+(P:ℝ)^2/(R:ℝ)^3)):=by
  field_simp
 exact le_of_mul_le_mul_left (by rw [hcancel];exact hLHS) (by positivity:(0:ℝ) < (R:ℝ)/8)
lemma lp5k (Y:ℕ) (hY:2^100000<=Y) :
  (Nat.log 2 (40*Y^2)+2)^5000<=Y:=by
 have hY1:1<=Y:=ltr (o1p 100000 2 (by omega)) hY
 set t:=Nat.log 2 Y with ht_def
 have ht:100000<=t:=llp (by omega) hY
 set u:=t/5000 with hu_def
 have hu:20<=u:=by omega
 have h40k:∀ k:ℕ,20<=k->40000*k<=2^k:=by
  intro k hk
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
   have:40000*(m+1)<=2*(40000*m):=by omega
   have hpow:2^(m+1)=2*2^m:=by ring
   omega
 have h40Y:40*Y^2 < 2^(2*t+8):=by
  have hlt:Y < 2^(t+1):=lsl (by omega) Y
  have hY2:Y^2 < (2^(t+1))^2:=Nat.pow_lt_pow_left hlt (by omega)
  have h64:40*Y^2 < 64*(2^(t+1))^2:=by nlinarith only [hY2]
  have heq:64*(2^(t+1))^2=2^(2*t+8):=by
   have h6:(64:ℕ)=2^6:=by norm_num
   rw [h6,← pmul,← padd];congr 1;ring
  linarith only [h64,heq]
 have hlog_lt:Nat.log 2 (40*Y^2) < 2*t+8:=Nat.log_lt_of_lt_pow (by positivity) h40Y
 have hbase:Nat.log 2 (40*Y^2)+2<=2^u:=by
  have h1:Nat.log 2 (40*Y^2)+2<=40000*u:=by omega
  exact ltr h1 (h40k u hu)
 calc
  (Nat.log 2 (40*Y^2)+2)^5000<=(2^u)^5000:=npl hbase 5000
  _=2^(u*5000):=by rw [← pmul]
  _<=2^t:=npr (by omega) (by omega)
  _<=Y:=pls 2 (by omega)
lemma r2_p41 (H Y L:ℝ) (hY:0 < Y) (hL:1<=L) (hL5:L^5000<=Y)
  (hH41:H^41<=Y^10) (a b c:ℕ) (h1:10*a < 41*c) (h2:41*b<=5000*(41*c - 10*a))
  (hHnn:0<=H):H^a*L^b<=Y^c:=by
 have hY1:1<=Y:=ltr (one_le_pow₀ hL) hL5
 have hpow:(H^a*L^b)^41<=(Y^c)^41:=by
  rw [mpow,← pmul,← pmul,← pmul]
  have hA:H^(a*41)<=Y^(10*a):=by
   rw [mcom a 41,pmul,pmul]
   exact pl0 (by positivity) hH41 a
  have hB:L^(b*41)<=Y^(41*c - 10*a):=by
   calc L^(b*41)<=L^(5000*(41*c - 10*a)):=pr0 hL (by omega)
    _=(L^5000)^(41*c - 10*a):=by rw [pmul]
    _<=Y^(41*c - 10*a):=by gcongr
  calc H^(a*41)*L^(b*41)<=Y^(10*a)*Y^(41*c - 10*a):=mlm hA hB (by positivity) (by positivity)
   _=Y^(10*a+(41*c - 10*a)):=by rw [← padd]
   _=Y^(c*41):=by congr 1;omega
 exact lp0 (by omega) (by positivity) hpow
lemma r2_q45 (H Y P R L:ℝ)
  (hYpos:0 < Y) (hHpos:0 < H) (hRpos:0 < R) (hPpos:0 < P)
  (hLR:600<=L) (hL5000R:L^5000<=Y) (hL200H:L^200<=H) (hH41Y10:H^41<=Y^10)
  (hH1:1<=H) (hHR_ub:H/R<=16*L) (hP2_ubR:P^2<=8*(10^10:ℝ)*Y/H) :
  640000*H^2*L*(H*L*P/R)<=Y/L^4/\640000*H^2*L*(P^2/R^3)<=Y/L^4:=by
 have h1_le_L:(1:ℝ)<=L:=by linarith only [hLR]
 have hLpos:(0:ℝ) < L:=by linarith only [hLR]
 constructor
 ·
  have hpow2:(640000*H^2*L*(H*L*P/R))^2<=(Y/L^4)^2:=by
   have h1:640000*H^2*L*(H*L*P/R)=640000*H^2*L^2*P*(H/R):=by ring
   have h2:640000*H^2*L^2*P*(H/R)<=(640000*16)*H^2*L^3*P:=by
    have:=ml hHR_ub (by positivity:0<=640000*H^2*L^2*P)
    linarith only [this]
   have h3:(640000*H^2*L*(H*L*P/R))^2<=((640000*16)*H^2*L^3*P)^2:=by
    have hnn:0<=640000*H^2*L*(H*L*P/R):=by positivity
    nlinarith only [h1,h2,hnn]
   have h4:((640000*16)*H^2*L^3*P)^2=(640000*16:ℝ)^2*H^4*L^6*P^2:=by ring
   have h5:(640000*16:ℝ)^2*H^4*L^6*P^2<=((640000*16:ℝ)^2*8*10^10)*Y*H^3*L^6:=by
    have:=ml hP2_ubR (by positivity:0<=(640000*16:ℝ)^2*H^4*L^6)
    have hr:(640000*16:ℝ)^2*H^4*L^6*(8*(10^10:ℝ)*Y/H)=((640000*16:ℝ)^2*8*10^10)*Y*H^3*L^6:=by field_simp
    linarith only [this,hr]
   have h6:((640000*16:ℝ)^2*8*10^10)*H^3*L^14<=Y:=by
    have hc:((640000*16:ℝ)^2*8*10^10)<=L^10:=by
     have hA:(600:ℝ)^10<=L^10:=by gcongr
     have hB:((640000*16:ℝ)^2*8*10^10)<=(600:ℝ)^10:=by norm_num
     linarith only [hA,hB]
    have hA:((640000*16:ℝ)^2*8*10^10)*H^3*L^14<=H^3*L^24:=by
     have:=mr hc (by positivity:0<=H^3*L^14)
     linarith only [this]
    have hB2:=r2_p41 H Y L hYpos h1_le_L hL5000R hH41Y10 3 24 1 (by omega) (by omega) (lol hHpos)
    simp only [pow_one] at hB2;linarith only [hA,hB2]
   have h7:((640000*16:ℝ)^2*8*10^10)*Y*H^3*L^6<=(Y/L^4)^2:=by
    rw [dpow,ldi (by positivity)]
    have:=mr h6 (lol hYpos)
    linarith only [this]
   linarith only [h3,h4,h5,h7]
  exact lp0 (by omega) (by positivity) hpow2
 ·
  have h1:640000*H^2*L*(P^2/R^3)=640000*L/H*(P^2*(H/R)^3):=by field_simp
  have h2:(H/R)^3<=(16*L)^3:=by gcongr
  have h3:P^2*(H/R)^3<=(8*(10^10:ℝ)*Y/H)*(16*L)^3:=mlm hP2_ubR h2 (by positivity) (by positivity)
  have h4:640000*L/H*(P^2*(H/R)^3)<=(640000*8*10^10*16^3)*Y*L^4/H^2:=by
   have:=ml h3 (by positivity:0<=640000*L/H)
   have hr:640000*L/H*((8*(10^10:ℝ)*Y/H)*(16*L)^3)=(640000*8*10^10*16^3)*Y*L^4/H^2:=by field_simp
   linarith only [this,hr]
  have h5:(640000*8*10^10*16^3:ℝ)*L^8<=H^2:=by
   have hc:(640000*8*10^10*16^3:ℝ)<=L^8:=by
    have hA:(600:ℝ)^8<=L^8:=by gcongr
    have hB:(640000*8*10^10*16^3:ℝ)<=(600:ℝ)^8:=by norm_num
    linarith only [hA,hB]
   have hA:(640000*8*10^10*16^3:ℝ)*L^8<=L^16:=by
    have:=mr hc (by positivity:0<=L^8)
    linarith only [this]
   have hB:L^16<=H:=ltr (pr0 h1_le_L (by omega)) hL200H
   have hC:H<=H^2:=lsp hH1 (by omega)
   linarith only [hA,hB,hC]
  have h6:(640000*8*10^10*16^3)*Y*L^4/H^2<=Y/L^4:=by
   rw [ddi (by positivity) (by positivity)]
   have:=mr h5 (lol hYpos)
   linarith only [this]
  linarith only [h1,h4,h6]
lemma r2_ls (Y H P:ℕ)
  (hY600:2^600<=Y)
  (hL5000:(Nat.log 2 (40*Y^2)+2)^5000<=Y)
  (hH_lb:Y < H^22) (hH_ub:H^41<=Y^10)
  (hHP:H<=P) (hP_lb:Y < P^2*H^2*(Nat.log 2 (40*Y^2)+2)^6)
  (hP_ub:P<=10^5*(Nat.sqrt (Y/H)+1))
  (E:Finset ℕ) (hE_sub:E⊆Ioc (Y/2) Y)
  (hE_prop:∀ m∈E,H/(8*(Nat.log 2 (40*Y^2)+2))<=((Ioc P (2*P)).filter
   (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card) :
  let L:=Nat.log 2 (40*Y^2)+2
  (H:ℝ)^2*(E.card:ℝ)<=6*(Y:ℝ)/(L:ℝ)^4:=by
 intro L
 let R:=H/(8*L)
 have hY1:1<=Y:=ltr (o1p 600 2 (by omega)) hY600
 have hL600:600<=L:=by
  have h1:2^600<=40*Y^2:=by
   calc 2^600<=Y:=hY600
    _=1*Y:=(omul Y).symm
    _<=40*(Y*Y):=nmm (by omega) (Nat.le_mul_of_pos_left Y hY1)
    _=40*Y^2:=by ring
  have h2:600<=Nat.log 2 (40*Y^2):=llp (by omega) h1
  dsimp [L];omega
 have hY100:100<=Y:=by
  have h1:100<=2^7:=by norm_num
  exact ltr h1 (ltr (npr (by omega) (by omega)) hY600)
 have hL_pow_H:L^200<=H:=by
  by_contra hlt;push Not at hlt
  have h1:H^22 < (L^200)^22:=Nat.pow_lt_pow_left hlt (by omega)
  have h2:(L^200)^22=L^4400:=by rw [← pmul]
  have h3:L^4400<=L^5000:=npr (by omega) (by omega)
  have hbad:Y < Y:=lt_of_lt_of_le (lt_trans hH_lb h1) (ltr (le_of_eq h2) (ltr h3 hL5000))
  exact lt_irrefl Y hbad
 have hH_pos:1<=H:=ltr (o1p 200 L (by omega)) hL_pow_H
 have h2H:2*H<=Y:=by
  by_contra hlt;push Not at hlt
  have hY41:Y^41 < (2*H)^41:=Nat.pow_lt_pow_left (by omega) (by omega)
  have h241:2^41<=Y^31:=ltr (npr (by omega) (by omega:41<=600))
    (ltr hY600 (Nat.le_self_pow (by omega) Y))
  have hY10:Y^10*2^41<=Y^41:=by
   calc Y^10*2^41<=Y^10*Y^31:=nml _ h241
    _=Y^41:=by rw [← padd]
  have h2:(2*H)^41=2^41*H^41:=mpow 2 H 41
  have h3:2^41*H^41<=2^41*Y^10:=nml _ hH_ub
  have h4:Y^10*2^41=2^41*Y^10:=mcom _ _
  have hbad:2^41*Y^10 < 2^41*Y^10:=lt_of_le_of_lt (h4 ▸ hY10) (lt_of_lt_of_le hY41 (h2 ▸ h3))
  exact lt_irrefl _ hbad
 have hP_sq_ub:P^2<=4*10^10*(Y/H+1):=by
  have h1:P^2<=(10^5*(Nat.sqrt (Y/H)+1))^2:=npl hP_ub 2
  have hsq:Nat.sqrt (Y/H)^2<=Y/H:=Nat.sqrt_le' (Y/H)
  have h2:(Nat.sqrt (Y/H)+1)^2<=4*(Y/H+1):=by
   have:Nat.sqrt (Y/H)<=Y/H+1:=by
    have:=Nat.sqrt_le_self (Y/H);omega
   nlinarith only [hsq,this]
  have h3:(10^5*(Nat.sqrt (Y/H)+1))^2=10^10*(Nat.sqrt (Y/H)+1)^2:=by ring
  nlinarith only [h1,h2,h3]
 have hP_le_Y:P<=Y:=by
  by_contra hgt;push Not at hgt
  have h1:Y^2 < P^2:=Nat.pow_lt_pow_left hgt (by omega)
  have h2:Y/H+1<=Y:=by
   have hH2:2<=H:=by
    have hL2:2<=L^200:=ltr (by omega:2<=600) (ltr hL600 (Nat.le_self_pow (by omega) L))
    exact ltr hL2 hL_pow_H
   have:Y/H<=Y/2:=ddll hH2 (by omega)
   omega
  have h3:4*10^10*(Y/H+1)<=4*10^10*Y:=nml _ h2
  have h4:4*10^10 < Y:=by
   have h4a:4*10^10 < 600^10:=by norm_num
   have h4b:600^10<=L^10:=npl hL600 10
   have h4c:L^10<=L^5000:=npr (by omega) (by omega)
   exact lt_of_lt_of_le h4a (ltr h4b (ltr h4c hL5000))
  nlinarith only [h1,hP_sq_ub,h3,h4]
 have hR4:4<=R:=by
  have h1:32*L<=H:=by
   have h1a:32*L<=L^2:=by nlinarith only [hL600]
   have h1b:L^2<=L^200:=npr (by omega) (by omega)
   exact ltr h1a (ltr h1b hL_pow_H)
  exact (ldim (by omega:0 < 8*L)).mpr (by linarith only [h1])
 have hRH:R<=H:=dvls _ _
 have ht2:=t2_ri Y H P R hY100 hH_pos h2H hHP hP_le_Y hR4 hRH E hE_sub hE_prop
 have hLR:(600:ℝ)<=(L:ℝ):=by exact_mod_cast hL600
 have hLpos:(0:ℝ) < (L:ℝ):=by linarith only [hLR]
 have hHpos:(0:ℝ) < (H:ℝ):=by exact_mod_cast hH_pos
 have hPpos:(0:ℝ) < (P:ℝ):=by exact_mod_cast (by omega:0 < P)
 have hYpos:(0:ℝ) < (Y:ℝ):=by exact_mod_cast (by omega:0 < Y)
 have hRpos:(0:ℝ) < (R:ℝ):=by exact_mod_cast (by omega:0 < R)
 have hR_lb:(H:ℝ)/(16*(L:ℝ))<=(R:ℝ):=by
  rw [dli (by positivity)]
  have h1:H<=16*L*R:=by
   have hdiv:H < 8*L*(R+1):=lmd H (by omega:0 < 8*L)
   nlinarith only [hdiv,hR4]
  have hR2:(H:ℝ)<=((16*L*R:ℕ):ℝ):=by exact_mod_cast h1
  push_cast at hR2;linarith only [hR2]
 have hHR_ub:(H:ℝ)/(R:ℝ)<=16*(L:ℝ):=by
  rw [dli hRpos]
  have h1:(H:ℝ)<=(R:ℝ)*(16*(L:ℝ)):=by
   have:=(dli (by positivity:(0:ℝ) < 16*(L:ℝ))).mp hR_lb
   linarith only [this]
  linarith only [h1]
 have hinvR:1/(R:ℝ)<=16*(L:ℝ)/(H:ℝ):=by
  rw [ddi hRpos hHpos]
  have:=(dli hRpos).mp hHR_ub
  linarith only [this]
 have hYP2:(Y:ℝ)/(P:ℝ)^2<=(H:ℝ)^2*(L:ℝ)^6:=by
  rw [dli (by positivity)]
  have h1:(Y:ℝ)<=((P^2*H^2*L^6:ℕ):ℝ):=by exact_mod_cast lol hP_lb
  push_cast at h1;linarith only [h1]
 have hP2_ubR:(P:ℝ)^2<=8*(10^10:ℝ)*(Y:ℝ)/(H:ℝ):=by
  have h1:(P:ℝ)^2<=4*(10^10:ℝ)*(((Y/H:ℕ):ℝ)+1):=by
   have h2:((P^2:ℕ):ℝ)<=((4*10^10*(Y/H+1):ℕ):ℝ):=by exact_mod_cast hP_sq_ub
   push_cast at h2;linarith only [h2]
  have hdiv:((Y/H:ℕ):ℝ)<=(Y:ℝ)/(H:ℝ):=by
   rw [ldi hHpos];exact_mod_cast dls Y H
  have h1_le:(1:ℝ)<=(Y:ℝ)/(H:ℝ):=by
   rw [ldi hHpos,omul];exact_mod_cast (by omega:H<=Y)
  have hring:4*(10^10:ℝ)*((Y:ℝ)/(H:ℝ)+(Y:ℝ)/(H:ℝ))=8*(10^10:ℝ)*(Y:ℝ)/(H:ℝ):=by ring
  linarith only [h1,hdiv,h1_le,hring]
 have hY_ge1R:(1:ℝ)<=(Y:ℝ):=by exact_mod_cast hY1
 have hL5000R:(L:ℝ)^5000<=(Y:ℝ):=by exact_mod_cast hL5000
 have hL200H:(L:ℝ)^200<=(H:ℝ):=by exact_mod_cast hL_pow_H
 have hH41Y10:(H:ℝ)^41<=(Y:ℝ)^10:=by exact_mod_cast hH_ub
 have h1_le_L:(1:ℝ)<=(L:ℝ):=by linarith only [hLR]
 have hLpow:∀ a b:ℕ,a<=b->(L:ℝ)^a<=(L:ℝ)^b:=fun a b hab =>
  pr0 h1_le_L hab
 have hpref:(H:ℝ)^2*(8*(H:ℝ)/(R:ℝ))<=128*(H:ℝ)^2*(L:ℝ):=by
  have h1:=ml hHR_ub (by positivity:0<=8*(H:ℝ)^2)
  have hl:8*(H:ℝ)^2*((H:ℝ)/(R:ℝ))=(H:ℝ)^2*(8*(H:ℝ)/(R:ℝ)):=by ring
  have hr:8*(H:ℝ)^2*(16*(L:ℝ))=128*(H:ℝ)^2*(L:ℝ):=by ring
  linarith only [h1,hl,hr]
 let d0:=natRoot 3 (36*H*P^3/Y)
 have hd0_cub:(d0:ℝ)^3<=36*(H:ℝ)*(P:ℝ)^3/(Y:ℝ):=by
  have h1:=natRoot_pow_le 3 (36*H*P^3/Y) (by omega)
  have h2:d0^3*Y<=36*H*P^3:=ltr (nmr Y h1) (dls _ _)
  rw [ldi hYpos]
  have h3:((d0^3*Y:ℕ):ℝ)<=((36*H*P^3:ℕ):ℝ):=by exact_mod_cast h2
  push_cast at h3;linarith only [h3]
 have hT0:128*(H:ℝ)^2*(L:ℝ)*(12*(Y:ℝ)/(P:ℝ)^2*((d0+1:ℕ):ℝ)*(L:ℝ)^2)<=(Y:ℝ)/(L:ℝ)^4:=by
  push_cast
  have hsplit:128*(H:ℝ)^2*(L:ℝ)*(12*(Y:ℝ)/(P:ℝ)^2*((d0:ℝ)+1)*(L:ℝ)^2)=(1536*(H:ℝ)^2*(Y:ℝ)*(d0:ℝ)*(L:ℝ)^3/(P:ℝ)^2)+(1536*(H:ℝ)^2*(Y:ℝ)*(L:ℝ)^3/(P:ℝ)^2):=by ring
  rw [hsplit]
  have hT0_1:1536*(H:ℝ)^2*(Y:ℝ)*(L:ℝ)^3/(P:ℝ)^2<=(Y:ℝ)/(L:ℝ)^4/2:=by
   have h1:1536*(H:ℝ)^2*(Y:ℝ)*(L:ℝ)^3/(P:ℝ)^2<=1536*(H:ℝ)^4*(L:ℝ)^9:=by
    have hmul:=ml hYP2 (by positivity:0<=1536*(H:ℝ)^2*(L:ℝ)^3)
    have hl:1536*(H:ℝ)^2*(L:ℝ)^3*((Y:ℝ)/(P:ℝ)^2)=1536*(H:ℝ)^2*(Y:ℝ)*(L:ℝ)^3/(P:ℝ)^2:=by ring
    have hr:1536*(H:ℝ)^2*(L:ℝ)^3*((H:ℝ)^2*(L:ℝ)^6)=1536*(H:ℝ)^4*(L:ℝ)^9:=by ring
    linarith only [hmul,hl,hr]
   have h2:3072*(H:ℝ)^4*(L:ℝ)^13<=(Y:ℝ):=by
    have h3072:(3072:ℝ)<=(L:ℝ)^2:=by nlinarith only [hLR]
    have h3:3072*(H:ℝ)^4*(L:ℝ)^13<=(H:ℝ)^4*(L:ℝ)^15:=by
     have:=mr h3072 (by positivity:0<=(H:ℝ)^4*(L:ℝ)^13)
     linarith only [this]
    have h4:=r2_p41 H Y L hYpos h1_le_L hL5000R hH41Y10 4 15 1 (by omega) (by omega) (lol hHpos)
    simp only [pow_one] at h4;linarith only [h3,h4]
   rw [div_div,ldi (by positivity)]
   have hmul:=mr h1 (by positivity:0<=(L:ℝ)^4*2)
   have hr:1536*(H:ℝ)^4*(L:ℝ)^9*((L:ℝ)^4*2)=3072*(H:ℝ)^4*(L:ℝ)^13:=by ring
   linarith only [hmul,hr,h2]
  have hT0_2:1536*(H:ℝ)^2*(Y:ℝ)*(d0:ℝ)*(L:ℝ)^3/(P:ℝ)^2<=(Y:ℝ)/(L:ℝ)^4/2:=by
   have hpow6:(1536*(H:ℝ)^2*(Y:ℝ)*(d0:ℝ)*(L:ℝ)^3/(P:ℝ)^2)^6<=((Y:ℝ)/(L:ℝ)^4/2)^6:=by
    have hstep1:(1536*(H:ℝ)^2*(Y:ℝ)*(d0:ℝ)*(L:ℝ)^3/(P:ℝ)^2)^6=(1536:ℝ)^6*(H:ℝ)^12*(Y:ℝ)^6*((d0:ℝ)^3)^2*(L:ℝ)^18/(P:ℝ)^12:=by ring
    have hstep2:((d0:ℝ)^3)^2<=(36*(H:ℝ)*(P:ℝ)^3/(Y:ℝ))^2:=by gcongr
    have hstep3:(1536:ℝ)^6*(H:ℝ)^12*(Y:ℝ)^6*((d0:ℝ)^3)^2*(L:ℝ)^18/(P:ℝ)^12<=(1536:ℝ)^6*(H:ℝ)^12*(Y:ℝ)^6*(36*(H:ℝ)*(P:ℝ)^3/(Y:ℝ))^2*(L:ℝ)^18/(P:ℝ)^12:=by
     gcongr
    have hstep4:(1536:ℝ)^6*(H:ℝ)^12*(Y:ℝ)^6*(36*(H:ℝ)*(P:ℝ)^3/(Y:ℝ))^2*(L:ℝ)^18/(P:ℝ)^12=((1536:ℝ)^6*36^2)*(H:ℝ)^14*(Y:ℝ)*(L:ℝ)^18*((Y:ℝ)/(P:ℝ)^2)^3:=by
     field_simp
    have hstep5:((Y:ℝ)/(P:ℝ)^2)^3<=((H:ℝ)^2*(L:ℝ)^6)^3:=by gcongr
    have hstep6:((1536:ℝ)^6*36^2)*(H:ℝ)^14*(Y:ℝ)*(L:ℝ)^18*((Y:ℝ)/(P:ℝ)^2)^3<=((1536:ℝ)^6*36^2)*(H:ℝ)^20*(Y:ℝ)*(L:ℝ)^36:=by
     have:=ml hstep5 (by positivity:0<=((1536:ℝ)^6*36^2)*(H:ℝ)^14*(Y:ℝ)*(L:ℝ)^18)
     have hr:((1536:ℝ)^6*36^2)*(H:ℝ)^14*(Y:ℝ)*(L:ℝ)^18*((H:ℝ)^2*(L:ℝ)^6)^3=((1536:ℝ)^6*36^2)*(H:ℝ)^20*(Y:ℝ)*(L:ℝ)^36:=by ring
     linarith only [this,hr]
    have hstep7:((1536:ℝ)^6*36^2*64)*(H:ℝ)^20*(L:ℝ)^60<=(Y:ℝ)^5:=by
     have hc:((1536:ℝ)^6*36^2*64)<=(L:ℝ)^10:=by
      have h1:(600:ℝ)^10<=(L:ℝ)^10:=by gcongr
      have h2:((1536:ℝ)^6*36^2*64)<=(600:ℝ)^10:=by norm_num
      linarith only [h1,h2]
     have h1:((1536:ℝ)^6*36^2*64)*(H:ℝ)^20*(L:ℝ)^60<=(H:ℝ)^20*(L:ℝ)^70:=by
      have:=mr hc (by positivity:0<=(H:ℝ)^20*(L:ℝ)^60)
      linarith only [this]
     have h2:=r2_p41 H Y L hYpos h1_le_L hL5000R hH41Y10 20 70 5 (by omega) (by omega) (lol hHpos)
     linarith only [h1,h2]
    have hstep8:((1536:ℝ)^6*36^2)*(H:ℝ)^20*(Y:ℝ)*(L:ℝ)^36<=((Y:ℝ)/(L:ℝ)^4/2)^6:=by
     have hr:((Y:ℝ)/(L:ℝ)^4/2)^6=(Y:ℝ)^6/(64*(L:ℝ)^24):=by ring
     rw [hr,ldi (by positivity)]
     have hmul:=mr hstep7 (lol hYpos)
     linarith only [hmul]
    linarith only [hstep1,hstep3,hstep4,hstep6,hstep8]
   exact lp0 (by omega) (by positivity) hpow6
  linarith only [hT0_1,hT0_2]
 have hQne1:640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2))<=(Y:ℝ)/(L:ℝ)^4:=by
  have hpow2:(640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)))^2<=((Y:ℝ)/(L:ℝ)^4)^2:=by
   have h1:640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2))=640000*(Y:ℝ)*(H:ℝ)*(L:ℝ)^2/(P:ℝ)*((H:ℝ)/(R:ℝ))^2:=by ring
   have h2:((H:ℝ)/(R:ℝ))^2<=(16*(L:ℝ))^2:=by gcongr
   have h3:640000*(Y:ℝ)*(H:ℝ)*(L:ℝ)^2/(P:ℝ)*((H:ℝ)/(R:ℝ))^2<=(640000*256)*(Y:ℝ)*(H:ℝ)*(L:ℝ)^4/(P:ℝ):=by
    have:=ml h2 (by positivity:0<=640000*(Y:ℝ)*(H:ℝ)*(L:ℝ)^2/(P:ℝ))
    have hr:640000*(Y:ℝ)*(H:ℝ)*(L:ℝ)^2/(P:ℝ)*(16*(L:ℝ))^2=(640000*256)*(Y:ℝ)*(H:ℝ)*(L:ℝ)^4/(P:ℝ):=by ring
    linarith only [this,hr]
   have h4:(640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)))^2<=((640000*256)*(Y:ℝ)*(H:ℝ)*(L:ℝ)^4/(P:ℝ))^2:=by
    have hnn:0<=640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)):=by positivity
    nlinarith only [h1,h3,hnn]
   have h5:((640000*256)*(Y:ℝ)*(H:ℝ)*(L:ℝ)^4/(P:ℝ))^2=(640000*256:ℝ)^2*(Y:ℝ)*(H:ℝ)^2*(L:ℝ)^8*((Y:ℝ)/(P:ℝ)^2):=by ring
   have h6:(640000*256:ℝ)^2*(Y:ℝ)*(H:ℝ)^2*(L:ℝ)^8*((Y:ℝ)/(P:ℝ)^2)<=(640000*256:ℝ)^2*(Y:ℝ)*(H:ℝ)^4*(L:ℝ)^14:=by
    have:=ml hYP2 (by positivity:0<=(640000*256:ℝ)^2*(Y:ℝ)*(H:ℝ)^2*(L:ℝ)^8)
    have hr:(640000*256:ℝ)^2*(Y:ℝ)*(H:ℝ)^2*(L:ℝ)^8*((H:ℝ)^2*(L:ℝ)^6)=(640000*256:ℝ)^2*(Y:ℝ)*(H:ℝ)^4*(L:ℝ)^14:=by ring
    linarith only [this,hr]
   have h7:(640000*256:ℝ)^2*(H:ℝ)^4*(L:ℝ)^22<=(Y:ℝ):=by
    have hc:(640000*256:ℝ)^2<=(L:ℝ)^8:=by
     have h1':(600:ℝ)^8<=(L:ℝ)^8:=by gcongr
     have h2':(640000*256:ℝ)^2<=(600:ℝ)^8:=by norm_num
     linarith only [h1',h2']
    have hA:(640000*256:ℝ)^2*(H:ℝ)^4*(L:ℝ)^22<=(H:ℝ)^4*(L:ℝ)^30:=by
     have:=mr hc (by positivity:0<=(H:ℝ)^4*(L:ℝ)^22)
     linarith only [this]
    have hB2:=r2_p41 H Y L hYpos h1_le_L hL5000R hH41Y10 4 30 1 (by omega) (by omega) (lol hHpos)
    simp only [pow_one] at hB2;linarith only [hA,hB2]
   have h8:(640000*256:ℝ)^2*(Y:ℝ)*(H:ℝ)^4*(L:ℝ)^14<=((Y:ℝ)/(L:ℝ)^4)^2:=by
    rw [dpow,ldi (by positivity)]
    have:=mr h7 (lol hYpos)
    linarith only [this]
   linarith only [h4,h5,h6,h8]
  exact lp0 (by omega) (by positivity) hpow2
 have hQne2:640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5))<=(Y:ℝ)/(L:ℝ)^4:=by
  have h1:640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5))=640000*(Y:ℝ)*(L:ℝ)/(H:ℝ)^3*((Y:ℝ)/(P:ℝ)^2)*((H:ℝ)/(R:ℝ))^5:=by
   field_simp
  have h2:((H:ℝ)/(R:ℝ))^5<=(16*(L:ℝ))^5:=by gcongr
  have h3:((Y:ℝ)/(P:ℝ)^2)*((H:ℝ)/(R:ℝ))^5<=((H:ℝ)^2*(L:ℝ)^6)*(16*(L:ℝ))^5:=mlm hYP2 h2 (by positivity) (by positivity)
  have h4:640000*(Y:ℝ)*(L:ℝ)/(H:ℝ)^3*(((Y:ℝ)/(P:ℝ)^2)*((H:ℝ)/(R:ℝ))^5)<=(640000*16^5)*(Y:ℝ)*(L:ℝ)^12/(H:ℝ):=by
   have:=ml h3 (by positivity:0<=640000*(Y:ℝ)*(L:ℝ)/(H:ℝ)^3)
   have hr:640000*(Y:ℝ)*(L:ℝ)/(H:ℝ)^3*(((H:ℝ)^2*(L:ℝ)^6)*(16*(L:ℝ))^5)=(640000*16^5)*(Y:ℝ)*(L:ℝ)^12/(H:ℝ):=by field_simp
   linarith only [this,hr]
  have h5:(640000*16^5:ℝ)*(L:ℝ)^16<=(H:ℝ):=by
   have hc:(640000*16^5:ℝ)<=(L:ℝ)^6:=by
    have hA:(600:ℝ)^6<=(L:ℝ)^6:=by gcongr
    have hB:(640000*16^5:ℝ)<=(600:ℝ)^6:=by norm_num
    linarith only [hA,hB]
   have hA:(640000*16^5:ℝ)*(L:ℝ)^16<=(L:ℝ)^22:=by
    have:=mr hc (by positivity:0<=(L:ℝ)^16)
    linarith only [this]
   exact ltr hA (ltr (hLpow 22 200 (by omega)) hL200H)
  have h6:(640000*16^5)*(Y:ℝ)*(L:ℝ)^12/(H:ℝ)<=(Y:ℝ)/(L:ℝ)^4:=by
   rw [ddi hHpos (by positivity)]
   have:=mr h5 (lol hYpos)
   linarith only [this]
  have hl_assoc:640000*(Y:ℝ)*(L:ℝ)/(H:ℝ)^3*((Y:ℝ)/(P:ℝ)^2)*((H:ℝ)/(R:ℝ))^5=640000*(Y:ℝ)*(L:ℝ)/(H:ℝ)^3*(((Y:ℝ)/(P:ℝ)^2)*((H:ℝ)/(R:ℝ))^5):=by ring
  linarith only [h1,hl_assoc,h4,h6]
 have hQne3:640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)/(R:ℝ)^4)<=(Y:ℝ)/(L:ℝ)^4:=by
  have h1:640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)/(R:ℝ)^4)=640000*(Y:ℝ)*(L:ℝ)/(H:ℝ)^2*((H:ℝ)/(R:ℝ))^4:=by field_simp
  have h2:((H:ℝ)/(R:ℝ))^4<=(16*(L:ℝ))^4:=by gcongr
  have h3:640000*(Y:ℝ)*(L:ℝ)/(H:ℝ)^2*((H:ℝ)/(R:ℝ))^4<=(640000*16^4)*(Y:ℝ)*(L:ℝ)^5/(H:ℝ)^2:=by
   have:=ml h2 (by positivity:0<=640000*(Y:ℝ)*(L:ℝ)/(H:ℝ)^2)
   have hr:640000*(Y:ℝ)*(L:ℝ)/(H:ℝ)^2*(16*(L:ℝ))^4=(640000*16^4)*(Y:ℝ)*(L:ℝ)^5/(H:ℝ)^2:=by ring
   linarith only [this,hr]
  have h4:(640000*16^4:ℝ)*(L:ℝ)^9<=(H:ℝ)^2:=by
   have hc:(640000*16^4:ℝ)<=(L:ℝ)^5:=by
    have hA:(600:ℝ)^5<=(L:ℝ)^5:=by gcongr
    have hB:(640000*16^4:ℝ)<=(600:ℝ)^5:=by norm_num
    linarith only [hA,hB]
   have hA:(640000*16^4:ℝ)*(L:ℝ)^9<=(L:ℝ)^14:=by
    have:=mr hc (by positivity:0<=(L:ℝ)^9)
    linarith only [this]
   have hB:(L:ℝ)^14<=(H:ℝ):=ltr (hLpow 14 200 (by omega)) hL200H
   have hC:(H:ℝ)<=(H:ℝ)^2:=lsp (by exact_mod_cast hH_pos) (by omega)
   linarith only [hA,hB,hC]
  have h5:(640000*16^4)*(Y:ℝ)*(L:ℝ)^5/(H:ℝ)^2<=(Y:ℝ)/(L:ℝ)^4:=by
   rw [ddi (by positivity) (by positivity)]
   have:=mr h4 (lol hYpos)
   linarith only [this]
  linarith only [h1,h3,h5]
 obtain ⟨hQne4,hQne5⟩:=r2_q45 (H:ℝ) (Y:ℝ) (P:ℝ) (R:ℝ) (L:ℝ)
  hYpos hHpos hRpos hPpos hLR hL5000R hL200H hH41Y10 (by exact_mod_cast hH_pos) hHR_ub hP2_ubR
 let M_rhs:ℝ:=12*(Y:ℝ)/(P:ℝ)^2*((d0+1:ℕ):ℝ)*(L:ℝ)^2+5000*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2)+(Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5)+(Y:ℝ)/(R:ℝ)^4+(H:ℝ)*(L:ℝ)*(P:ℝ)/(R:ℝ)+(P:ℝ)^2/(R:ℝ)^3)
 have hM_nn:0<=M_rhs:=by positivity
 have hstep1:(H:ℝ)^2*(E.card:ℝ)<=(H:ℝ)^2*(8*(H:ℝ)/(R:ℝ))*M_rhs:=by
  have:=ml ht2 (by positivity:0<=(H:ℝ)^2)
  have hr:(H:ℝ)^2*((8*(H:ℝ)/(R:ℝ))*M_rhs)=(H:ℝ)^2*(8*(H:ℝ)/(R:ℝ))*M_rhs:=by ring
  linarith only [this,hr]
 have hstep2:(H:ℝ)^2*(8*(H:ℝ)/(R:ℝ))*M_rhs<=128*(H:ℝ)^2*(L:ℝ)*M_rhs:=mr hpref hM_nn
 have hexp:128*(H:ℝ)^2*(L:ℝ)*M_rhs=128*(H:ℝ)^2*(L:ℝ)*(12*(Y:ℝ)/(P:ℝ)^2*((d0+1:ℕ):ℝ)*(L:ℝ)^2)+640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)*(H:ℝ)*(L:ℝ)/((P:ℝ)*(R:ℝ)^2))+640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)^2/((P:ℝ)^2*(R:ℝ)^5))+640000*(H:ℝ)^2*(L:ℝ)*((Y:ℝ)/(R:ℝ)^4)+640000*(H:ℝ)^2*(L:ℝ)*((H:ℝ)*(L:ℝ)*(P:ℝ)/(R:ℝ))+640000*(H:ℝ)^2*(L:ℝ)*((P:ℝ)^2/(R:ℝ)^3):=by
  dsimp only [M_rhs];ring
 have h6:6*((Y:ℝ)/(L:ℝ)^4)=6*(Y:ℝ)/(L:ℝ)^4:=by ring
 linarith only [hstep1,hstep2,hexp,hT0,hQne1,hQne2,hQne3,hQne4,hQne5,h6]
lemma r2_bd :
  ∃ Y0:ℕ,∀ Y ≥ Y0,∀ H:ℕ,Y < H^22->H^41<=Y^10->(H:ℝ)^2*(Mstar Y H:ℝ)<=(2^70:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by
 refine ⟨2^100000,fun Y hY H hH_lb hH_ub => ?_⟩
 have hY600:2^600<=Y:=ltr (npr (by omega) (by omega)) hY
 have hY1:1<=Y:=ltr (o1p 600 2 (by omega)) hY600
 have hL5000:(Nat.log 2 (40*Y^2)+2)^5000<=Y:=lp5k Y hY
 set L:=Nat.log 2 (40*Y^2)+2 with hL_def
 have hlogY_ge:100000<=Nat.log 2 Y:=llp (by omega) hY
 have hlogY_le_L:Nat.log 2 Y<=L:=by
  have h1:Y<=40*Y^2:=by
   calc Y=1*Y:=(omul Y).symm
    _<=40*(Y*Y):=nmm (by omega) (Nat.le_mul_of_pos_left Y hY1)
    _=40*Y^2:=by ring
  have h2:Nat.log 2 Y<=Nat.log 2 (40*Y^2):=lmr h1
  omega
 have hL_ge:100000<=L:=ltr hlogY_ge hlogY_le_L
 have hL_le_3logY:L<=3*Nat.log 2 Y:=by
  have h40:40*Y^2 < 2^(2*Nat.log 2 Y+8):=by
   have hlt:Y < 2^(Nat.log 2 Y+1):=lsl (by omega) Y
   have hY2':Y^2 < (2^(Nat.log 2 Y+1))^2:=Nat.pow_lt_pow_left hlt (by omega)
   have h64:40*Y^2 < 64*(2^(Nat.log 2 Y+1))^2:=by nlinarith only [hY2']
   have heq:64*(2^(Nat.log 2 Y+1))^2=2^(2*Nat.log 2 Y+8):=by
    have h6:(64:ℕ)=2^6:=by norm_num
    rw [h6,← pmul,← padd];congr 1;ring
   linarith only [h64,heq]
  have hlt2:Nat.log 2 (40*Y^2) < 2*Nat.log 2 Y+8:=Nat.log_lt_of_lt_pow (by positivity) h40
  omega
 have hlogH_ge:Nat.log 2 Y/22<=Nat.log 2 H:=by
  have h1:2^(Nat.log 2 Y/22)<=H:=by
   by_contra hlt;push Not at hlt
   have h2:H^22 < (2^(Nat.log 2 Y/22))^22:=Nat.pow_lt_pow_left hlt (by omega)
   have h3:(2^(Nat.log 2 Y/22))^22=2^(22*(Nat.log 2 Y/22)):=by
    rw [← pmul,mcom]
   have h4:2^(22*(Nat.log 2 Y/22))<=2^Nat.log 2 Y:=npr (by omega) (Nat.mul_div_le _ _)
   have h5:2^Nat.log 2 Y<=Y:=pls 2 (by omega)
   exact lt_irrefl Y (lt_of_lt_of_le (lt_trans hH_lb h2) (ltr (le_of_eq h3) (ltr h4 h5)))
  exact llp (by omega) h1
 have hlogH_4545:4545<=Nat.log 2 H:=by omega
 have hH_ge_20:2^20<=H:=ltr (npr (by omega) (by omega:20<=4545))
   (ltr (npr (by omega) hlogH_4545) (pls 2 (by
    by_contra h0;simp only [h0,zero_pow (by omega:22≠0)] at hH_lb;omega)))
 have hH_pos:1<=H:=ltr (by norm_num:1<=2^20) hH_ge_20
 have hH3:H^3 < 10^9*Y:=by
  have h2:(H^3)^41<=Y^30:=by
   calc (H^3)^41=(H^41)^3:=by ring
    _<=(Y^10)^3:=npl hH_ub 3
    _=Y^30:=by ring
  have h3:Y^30 < Y^41:=Nat.pow_lt_pow_right (by
   have:2<=2^600:=ltr (by norm_num:2<=2^1) (npr (by omega) (by omega))
   exact lt_of_lt_of_le (by omega) hY600) (by omega)
  have h4:H^3 < Y:=by
   by_contra hge;push Not at hge
   exact lt_irrefl _ (lt_of_le_of_lt (ltr (npl hge 41) h2) h3)
  omega
 set Z1:=H*Nat.log 2 H/1000
 set Z2:=10^5*(Nat.sqrt (Y/H)+1)
 have hH_le_Z1:H<=Z1:=by
  refine (ldim (by omega:0 < 1000)).mpr ?_
  exact nml H (by omega:1000<=Nat.log 2 H)
 have hZ1_16:16<=Z1:=ltr (by norm_num:16<=2^20) (ltr hH_ge_20 hH_le_Z1)
 have hZ2_le_Y:Z2<=Y:=by
  have hsq:Nat.sqrt (Y/H)^2<=Y/H:=Nat.sqrt_le' (Y/H)
  have hZ2_sq:Z2^2<=4*10^10*(Y/H+1):=by
   have h1:(Nat.sqrt (Y/H)+1)^2<=4*(Y/H+1):=by
    have:=Nat.sqrt_le_self (Y/H);nlinarith only [hsq,this]
   have h2:Z2^2=10^10*(Nat.sqrt (Y/H)+1)^2:=by dsimp [Z2];ring
   nlinarith only [h1,h2]
  have hdiv:Y/H+1<=Y:=by
   have:Y/H<=Y/2:=ddll (by omega:2<=H) (by omega)
   have hY4:4<=Y:=ltr (by norm_num:4<=2^2) (ltr (npr (by omega) (by omega)) hY600)
   omega
  have h4e10:4*10^10 < Y:=by
   have:4*10^10 < 2^40:=by norm_num
   exact lt_of_lt_of_le this (ltr (npr (by omega) (by omega)) hY600)
  by_contra hgt;push Not at hgt
  have:Y^2 < Z2^2:=Nat.pow_lt_pow_left hgt (by omega)
  have:4*10^10*(Y/H+1)<=4*10^10*Y:=nml _ hdiv
  nlinarith only [hZ2_sq,‹Y^2 < Z2^2›,‹4*10^10*(Y/H+1)<=4*10^10*Y›,h4e10]
 set P_of:ℕ->ℕ:=fun i => Z1*2^i
 set I:=(range L).filter (fun i => P_of i<=Z2)
 set R:=H/(8*L)
 have hL_pow_H:L^200<=H:=by
  by_contra hlt;push Not at hlt
  have h1:H^22 < (L^200)^22:=Nat.pow_lt_pow_left hlt (by omega)
  have h2:(L^200)^22=L^4400:=by rw [← pmul]
  have h3:L^4400<=L^5000:=npr (by omega) (by omega)
  exact lt_irrefl Y (lt_of_lt_of_le (lt_trans hH_lb h1) (ltr (le_of_eq h2) (ltr h3 hL5000)))
 have hR4:4<=R:=by
  have h1:32*L<=H:=ltr (by nlinarith only [hL_ge]:32*L<=L^2)
   (ltr (npr (by omega) (by omega)) hL_pow_H)
  exact (ldim (by omega:0 < 8*L)).mpr (by linarith only [h1])
 set E:=(Ioc (Y/2) Y).filter (noSqf H)
 set E_shell:ℕ->Finset ℕ:=fun i => E.filter (fun m => R<=((Ioc (P_of i) (2*P_of i)).filter
  (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card)
 have hE_cover:E⊆I.biUnion E_shell:=by
  intro m hm
  have hm_loc:m∈Ioc (Y/2) Y:=(mf.mp hm).1
  have hm_nosqf:noSqf H m:=(mf.mp hm).2
  have hdet:=det_pw Y H m hH_ge_20 hH3 hm_loc hm_nosqf
  set S_all:=(Ioc Z1 Z2).filter (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)
  have hS_sub:S_all⊆I.biUnion (fun i => (Ioc (P_of i) (2*P_of i)).filter
    (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)):=by
   intro p hp
   rw [mbu]
   have hp_Ioc:=mioc.mp (mf.mp hp).1
   have hp_pr:=(mf.mp hp).2
   let i:=Nat.log 2 ((p - 1)/Z1)
   have hq_pos:1<=(p - 1)/Z1:=(ldim (by omega)).mpr (by omega)
   have hi_lo:2^i<=(p - 1)/Z1:=pls 2 (by omega)
   have hi_hi:(p - 1)/Z1 < 2^(i+1):=lsl (by omega) _
   have hP_lt:P_of i < p:=by
    have:Z1*2^i<=p - 1:=ltr (nml Z1 hi_lo) (Nat.mul_div_le (p - 1) Z1)
    dsimp [P_of];omega
   have hp_le2P:p<=2*P_of i:=by
    have hdiv:(p - 1)/Z1<=2^(i+1) - 1:=Nat.le_sub_one_of_lt hi_hi
    have h1:p - 1 < Z1*2^(i+1):=by
     by_contra hge;push Not at hge
     have:=(ldim (by omega:0 < Z1)).mpr (by linarith only [hge]:2^(i+1)*Z1<=p - 1)
     omega
    have h2:Z1*2^(i+1)=2*P_of i:=by dsimp [P_of];ring
    omega
   have hi_mem:i∈I:=by
    rw [mf,mrng]
    refine ⟨?_,by omega⟩
    have h2i:2^i<=40*Y^2:=by
     have h1:2^i<=P_of i:=Nat.le_mul_of_pos_left _ (by omega)
     have h2:P_of i<=Y:=by omega
     calc 2^i<=Y:=ltr h1 h2
      _=1*Y:=(omul Y).symm
      _<=40*(Y*Y):=nmm (by omega) (Nat.le_mul_of_pos_left Y hY1)
      _=40*Y^2:=by ring
    have:=llp (by omega) h2i
    omega
   exact ⟨i,hi_mem,mf.mpr ⟨mioc.mpr ⟨hP_lt,hp_le2P⟩,hp_pr⟩⟩
  by_contra hnot
  rw [mbu] at hnot;push Not at hnot
  have hlt_all:∀ i∈I,((Ioc (P_of i) (2*P_of i)).filter
    (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card<=R:=by
   intro i hi
   have hnot_i:=hnot i hi
   rw [mf] at hnot_i
   have hnotR:¬ R<=((Ioc (P_of i) (2*P_of i)).filter
     (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card:=fun h => hnot_i ⟨hm,h⟩
   omega
  have hcard_le:S_all.card<=I.card*R:=by
   calc S_all.card<=(I.biUnion _).card:=clc hS_sub
    _<=∑ i∈I,((Ioc (P_of i) (2*P_of i)).filter
      (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card:=cbi
    _<=∑ _i∈I,R:=sls hlt_all
    _=I.card*R:=by simp
  have hI_le:I.card<=L:=ltr (cfl _ _) (by simp)
  have hLR:L*R<=H/8:=by
   have:8*(L*R)<=H:=by
    have hmul:8*L*R<=H:=Nat.mul_div_le H (8*L)
    linarith only [hmul]
   omega
  have hbad:H/4<=H/8:=ltr hdet (ltr hcard_le (ltr (nmr R hI_le) hLR))
  omega
 have hMstar_le:(Mstar Y H:ℝ)<=∑ i∈I,((E_shell i).card:ℝ):=by
  have hnat:Mstar Y H<=∑ i∈I,(E_shell i).card:=ltr (clc hE_cover) cbi
  exact_mod_cast hnat
 set I_small:=I.filter (fun i => (P_of i)^2*H^2*L^6<=Y)
 set I_large:=I.filter (fun i => Y < (P_of i)^2*H^2*L^6)
 have hI_split:∑ i∈I,((E_shell i).card:ℝ)=(∑ i∈I_small,((E_shell i).card:ℝ))+(∑ i∈I_large,((E_shell i).card:ℝ)):=by
  have:=(sum_filter_add_sum_filter_not I (fun i => (P_of i)^2*H^2*L^6<=Y)
   (fun i => ((E_shell i).card:ℝ))).symm
  convert this using 2
  apply sum_congr _ (fun _ _ => rfl)
  ext i;simp only [I_large,mf,not_le]
 have hLpos:(0:ℝ) < (L:ℝ):=by exact_mod_cast (by omega:0 < L)
 have hlogY_pos:(0:ℝ) < (Nat.log 2 Y:ℝ):=by exact_mod_cast (by omega:0 < Nat.log 2 Y)
 have hYpos:(0:ℝ) < (Y:ℝ):=by exact_mod_cast (by omega:0 < Y)
 have hHpos:(0:ℝ) < (H:ℝ):=by exact_mod_cast hH_pos
 have hLarge:∑ i∈I_large,(H:ℝ)^2*((E_shell i).card:ℝ)<=(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by
  have hterm:∀ i∈I_large,(H:ℝ)^2*((E_shell i).card:ℝ)<=6*(Y:ℝ)/(L:ℝ)^4:=by
   intro i hi
   have hiI:i∈I:=(mf.mp hi).1
   have hP_lb:Y < (P_of i)^2*H^2*L^6:=(mf.mp hi).2
   have hP_ub:P_of i<=Z2:=(mf.mp hiI).2
   have hHP:H<=P_of i:=ltr hH_le_Z1 (Nat.le_mul_of_pos_right Z1 (by positivity))
   exact r2_ls Y H (P_of i) hY600 hL5000 hH_lb hH_ub hHP hP_lb hP_ub
    (E_shell i) (Finset.Subset.trans (fsub _ _) (fsub _ _))
    (fun m hm => (mf.mp hm).2)
  have hsum:=sls hterm
  simp only [sum_const,nsmul_eq_mul] at hsum
  have hcard:(I_large.card:ℝ)<=(L:ℝ):=by
   have:I_large.card<=L:=ltr (cfl _ _) (ltr (cfl _ _) (by simp))
   exact_mod_cast this
  have h1:(I_large.card:ℝ)*(6*(Y:ℝ)/(L:ℝ)^4)<=6*(Y:ℝ)/(L:ℝ)^3:=by
   have hmul:=mr hcard (by positivity:0<=6*(Y:ℝ)/(L:ℝ)^4)
   have heq:(L:ℝ)*(6*(Y:ℝ)/(L:ℝ)^4)=6*(Y:ℝ)/(L:ℝ)^3:=by field_simp
   linarith only [hmul,heq]
  have h2:6*(Y:ℝ)/(L:ℝ)^3<=(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by
   rw [ddi (by positivity) (by positivity)]
   have hL_geR:(Nat.log 2 Y:ℝ)<=(L:ℝ):=by exact_mod_cast hlogY_le_L
   have hL6:(6:ℝ)<=(L:ℝ):=by exact_mod_cast (by omega:6<=L)
   have hA:(Nat.log 2 Y:ℝ)^2<=(L:ℝ)^2:=by gcongr
   have hB:6*(Nat.log 2 Y:ℝ)^2<=(L:ℝ)^3:=by nlinarith only [hL6,hA]
   have:=ml hB (lol hYpos)
   linarith only [this]
  linarith only [hsum,h1,h2]
 have hHR_ub:(H:ℝ)/(R:ℝ)<=16*(L:ℝ):=by
  have hRpos:(0:ℝ) < (R:ℝ):=by exact_mod_cast (by omega:0 < R)
  rw [dli hRpos]
  have h1:H<=16*L*R:=by
   have hdiv:H < 8*L*(R+1):=lmd H (by omega:0 < 8*L)
   nlinarith only [hdiv,hR4]
  have h2:(H:ℝ)<=((16*L*R:ℕ):ℝ):=by exact_mod_cast h1
  push_cast at h2;linarith only [h2]
 have hHZ1:(H:ℝ)/(Z1:ℝ)<=46000/(Nat.log 2 Y:ℝ):=by
  have hZ1pos:(0:ℝ) < (Z1:ℝ):=by exact_mod_cast (by omega:0 < Z1)
  rw [ddi hZ1pos hlogY_pos]
  have hnat:H*Nat.log 2 Y<=46000*Z1:=by
   have h1:Nat.log 2 Y<=23*Nat.log 2 H:=by omega
   have h2:H*Nat.log 2 H<=2000*Z1:=by
    have hdiv:H*Nat.log 2 H < 1000*(Z1+1):=lmd (H*Nat.log 2 H) (by omega:0 < 1000)
    nlinarith only [hdiv,hZ1_16]
   have h3:H*Nat.log 2 Y<=23*(H*Nat.log 2 H):=by
    have:=nml H h1;linarith only [this]
   omega
  have hR:((H*Nat.log 2 Y:ℕ):ℝ)<=((46000*Z1:ℕ):ℝ):=by exact_mod_cast hnat
  push_cast at hR;linarith only [hR]
 have hSmall:∑ i∈I_small,(H:ℝ)^2*((E_shell i).card:ℝ)<=(2^69:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by
  have hterm:∀ i∈I_small,(H:ℝ)^2*((E_shell i).card:ℝ)<=(2^65:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*(1/4:ℝ)^i+1024*(Y:ℝ)/(L:ℝ)^4:=by
   intro i hi
   have hPi_small:(P_of i)^2*H^2*L^6<=Y:=(mf.mp hi).2
   have hPi16:16<=P_of i:=ltr hZ1_16 (Nat.le_mul_of_pos_right Z1 (by positivity))
   have hEs_Icc:E_shell i⊆Icc 1 Y:=by
    intro m hm
    have h1:=mioc.mp (mf.mp (mf.mp hm).1).1
    have hY2:2<=Y:=by omega
    exact micc.mpr ⟨by omega,h1.2⟩
   have ht1:=t1_pb Y H (P_of i) R hPi16 hR4 (E_shell i) hEs_Icc
    (fun m hm => (mf.mp hm).2)
   have hpref:(H:ℝ)^2*(4*(H:ℝ)^2/(R:ℝ)^2)<=1024*(H:ℝ)^2*(L:ℝ)^2:=by
    have h1:((H:ℝ)/(R:ℝ))^2<=(16*(L:ℝ))^2:=by gcongr
    have h2:=ml h1 (by positivity:0<=4*(H:ℝ)^2)
    have hl:4*(H:ℝ)^2*((H:ℝ)/(R:ℝ))^2=(H:ℝ)^2*(4*(H:ℝ)^2/(R:ℝ)^2):=by ring
    have hr:4*(H:ℝ)^2*(16*(L:ℝ))^2=1024*(H:ℝ)^2*(L:ℝ)^2:=by ring
    linarith only [h2,hl,hr]
   have hstep:(H:ℝ)^2*((E_shell i).card:ℝ)<=1024*(H:ℝ)^2*(L:ℝ)^2*((Y:ℝ)*(36/((P_of i:ℝ)*(Nat.log 2 (P_of i):ℝ)))^2+(P_of i:ℝ)^2):=by
    have h1:=ml ht1 (by positivity:0<=(H:ℝ)^2)
    have h2:=mr hpref (by positivity :
     0<=(Y:ℝ)*(36/((P_of i:ℝ)*(Nat.log 2 (P_of i):ℝ)))^2+(P_of i:ℝ)^2)
    linarith only [h1,h2]
   have hTermB:1024*(H:ℝ)^2*(L:ℝ)^2*(P_of i:ℝ)^2<=1024*(Y:ℝ)/(L:ℝ)^4:=by
    rw [ldi (by positivity)]
    have hR:(((P_of i)^2*H^2*L^6:ℕ):ℝ)<=(Y:ℝ):=by exact_mod_cast hPi_small
    push_cast at hR
    nlinarith only [hR]
   have hTermA:1024*(H:ℝ)^2*(L:ℝ)^2*((Y:ℝ)*(36/((P_of i:ℝ)*(Nat.log 2 (P_of i):ℝ)))^2)<=(2^65:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*(1/4:ℝ)^i:=by
    have hHPi:H<=P_of i:=ltr hH_le_Z1 (Nat.le_mul_of_pos_right Z1 (by positivity))
    have hlogP_ge:Nat.log 2 Y<=23*Nat.log 2 (P_of i):=by
     have:Nat.log 2 H<=Nat.log 2 (P_of i):=lmr hHPi
     omega
    have hlogP_pos:(0:ℝ) < (Nat.log 2 (P_of i):ℝ):=by exact_mod_cast (by omega:0 < Nat.log 2 (P_of i))
    have hZ1pos:(0:ℝ) < (Z1:ℝ):=by exact_mod_cast (by omega:0 < Z1)
    have hfrac:(H:ℝ)/((P_of i:ℝ)*(Nat.log 2 (P_of i):ℝ))<=(46000*23:ℝ)/((Nat.log 2 Y:ℝ)^2*(2:ℝ)^i):=by
     have hPeq:(P_of i:ℝ)=(Z1:ℝ)*(2:ℝ)^i:=by dsimp [P_of];push_cast;ring
     have h1:1/(Nat.log 2 (P_of i):ℝ)<=23/(Nat.log 2 Y:ℝ):=by
      rw [ddi hlogP_pos hlogY_pos]
      have hR:(Nat.log 2 Y:ℝ)<=23*(Nat.log 2 (P_of i):ℝ):=by exact_mod_cast hlogP_ge
      linarith only [hR]
     have h2:(H:ℝ)/(Z1:ℝ)*(1/(Nat.log 2 (P_of i):ℝ))<=(46000/(Nat.log 2 Y:ℝ))*(23/(Nat.log 2 Y:ℝ)):=mlm hHZ1 h1 (by positivity) (by positivity)
     have h3:=mr h2 (by positivity:0<=1/(2:ℝ)^i)
     have hl:(H:ℝ)/(Z1:ℝ)*(1/(Nat.log 2 (P_of i):ℝ))*(1/(2:ℝ)^i)=(H:ℝ)/((P_of i:ℝ)*(Nat.log 2 (P_of i):ℝ)):=by rw [hPeq];field_simp
     have hr:(46000/(Nat.log 2 Y:ℝ))*(23/(Nat.log 2 Y:ℝ))*(1/(2:ℝ)^i)=(46000*23:ℝ)/((Nat.log 2 Y:ℝ)^2*(2:ℝ)^i):=by field_simp
     linarith only [h3,hl,hr]
    have hsq:((H:ℝ)/((P_of i:ℝ)*(Nat.log 2 (P_of i):ℝ)))^2<=((46000*23:ℝ)/((Nat.log 2 Y:ℝ)^2*(2:ℝ)^i))^2:=by gcongr
    have hL3:(L:ℝ)^2<=9*(Nat.log 2 Y:ℝ)^2:=by
     have hR:(L:ℝ)<=3*(Nat.log 2 Y:ℝ):=by exact_mod_cast hL_le_3logY
     nlinarith only [hR,hLpos]
    have hl:1024*(H:ℝ)^2*(L:ℝ)^2*((Y:ℝ)*(36/((P_of i:ℝ)*(Nat.log 2 (P_of i):ℝ)))^2)=(1024*36^2:ℝ)*(Y:ℝ)*(L:ℝ)^2*((H:ℝ)/((P_of i:ℝ)*(Nat.log 2 (P_of i):ℝ)))^2:=by ring
    have hmul:=mlm hL3 hsq (by positivity) (by positivity)
    have hmul2:=ml hmul (by positivity:0<=(1024*36^2:ℝ)*(Y:ℝ))
    have hmid:(1024*36^2:ℝ)*(Y:ℝ)*(9*(Nat.log 2 Y:ℝ)^2*((46000*23:ℝ)/((Nat.log 2 Y:ℝ)^2*(2:ℝ)^i))^2)=(1024*36^2*9*(46000*23)^2:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*(1/4:ℝ)^i:=by
     have h4:((2:ℝ)^i)^2=(4:ℝ)^i:=by rw [← pmul,mcom,pmul];norm_num
     rw [dpow,dpow,one_pow,mpow ((Nat.log 2 Y:ℝ)^2),h4]
     field_simp
    have hconst:(1024*36^2*9*(46000*23)^2:ℝ)<=(2^65:ℝ):=by norm_num
    have hfin:=mr hconst
     (by positivity:0<=(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*(1/4:ℝ)^i)
    have hlin:(1024*36^2*9*(46000*23)^2:ℝ)*((Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*(1/4:ℝ)^i)=(1024*36^2*9*(46000*23)^2:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*(1/4:ℝ)^i:=by ring
    have hlin2:(2^65:ℝ)*((Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*(1/4:ℝ)^i)=(2^65:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*(1/4:ℝ)^i:=by ring
    linarith only [hl,hmul2,hmid,hfin,hlin,hlin2]
   have hexp:1024*(H:ℝ)^2*(L:ℝ)^2*((Y:ℝ)*(36/((P_of i:ℝ)*(Nat.log 2 (P_of i):ℝ)))^2+(P_of i:ℝ)^2)=1024*(H:ℝ)^2*(L:ℝ)^2*((Y:ℝ)*(36/((P_of i:ℝ)*(Nat.log 2 (P_of i):ℝ)))^2)+1024*(H:ℝ)^2*(L:ℝ)^2*(P_of i:ℝ)^2:=by ring
   linarith only [hstep,hexp,hTermA,hTermB]
  have hsum:=sls hterm
  rw [sum_add_distrib] at hsum
  have hmul_out:∑ i∈I_small,(2^65:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*(1/4:ℝ)^i=(2^65:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*∑ i∈I_small,(1/4:ℝ)^i:=(mul_sum _ _ _).symm
  have hgeom:∑ i∈I_small,(1/4:ℝ)^i<=2:=by
   have hsub:I_small⊆range L:=Finset.Subset.trans (fsub _ _) (fsub _ _)
   have h1:∑ i∈I_small,(1/4:ℝ)^i<=∑ i∈range L,(1/4:ℝ)^i:=ssub hsub (fun _ _ _ => by positivity)
   have h2:∀ n:ℕ,∑ i∈range n,(1/4:ℝ)^i<=2 - (4/3:ℝ)*(1/4:ℝ)^n:=by
    intro n;induction n with
    | zero => norm_num
    | succ k ih =>
     rw [sum_range_succ,pow_succ]
     linarith only [ih]
   have h3:(0:ℝ)<=(4/3:ℝ)*(1/4:ℝ)^L:=by positivity
   linarith only [h1,h2 L,h3]
  have hA:(2^65:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*∑ i∈I_small,(1/4:ℝ)^i<=(2^66:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by
   have:=ml hgeom (by positivity:0<=(2^65:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2))
   have hr:(2^65:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)*2=(2^66:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by ring
   linarith only [this,hr]
  have hB:∑ _i∈I_small,1024*(Y:ℝ)/(L:ℝ)^4<=(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by
   simp only [sum_const,nsmul_eq_mul]
   have hcard:(I_small.card:ℝ)<=(L:ℝ):=by
    have:I_small.card<=L:=ltr (cfl _ _) (ltr (cfl _ _) (by simp))
    exact_mod_cast this
   have h1:=mr hcard (by positivity:0<=1024*(Y:ℝ)/(L:ℝ)^4)
   have heq:(L:ℝ)*(1024*(Y:ℝ)/(L:ℝ)^4)=1024*(Y:ℝ)/(L:ℝ)^3:=by field_simp
   have h2:1024*(Y:ℝ)/(L:ℝ)^3<=(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by
    rw [ddi (by positivity) (by positivity)]
    have hL_geR:(Nat.log 2 Y:ℝ)<=(L:ℝ):=by exact_mod_cast hlogY_le_L
    have hL1024:(1024:ℝ)<=(L:ℝ):=by exact_mod_cast (by omega:1024<=L)
    have hA':(Nat.log 2 Y:ℝ)^2<=(L:ℝ)^2:=by gcongr
    have hB':1024*(Nat.log 2 Y:ℝ)^2<=(L:ℝ)^3:=by nlinarith only [hL1024,hA']
    have:=ml hB' (lol hYpos)
    linarith only [this]
   linarith only [h1,heq,h2]
  have h66:(2^66:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)+(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)<=(2^69:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by
   have hnn:0<=(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by positivity
   have hl:(2^66:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)+(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)=(2^66+1:ℝ)*((Y:ℝ)/((Nat.log 2 Y:ℝ)^2)):=by ring
   have hr:(2^69:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)=(2^69:ℝ)*((Y:ℝ)/((Nat.log 2 Y:ℝ)^2)):=by ring
   nlinarith only [hnn,hl,hr]
  linarith only [hsum,hmul_out,hA,hB,h66]
 have hcomb:(H:ℝ)^2*(Mstar Y H:ℝ)<=(∑ i∈I_small,(H:ℝ)^2*((E_shell i).card:ℝ))+(∑ i∈I_large,(H:ℝ)^2*((E_shell i).card:ℝ)):=by
  have h1:=ml hMstar_le (by positivity:0<=(H:ℝ)^2)
  rw [hI_split,mul_add,mul_sum,mul_sum] at h1
  exact h1
 have hfin:(2^69:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)+(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)<=(2^70:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by
  have hnn:0<=(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by positivity
  have hl:(2^69:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)+(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)=(2^69+1:ℝ)*((Y:ℝ)/((Nat.log 2 Y:ℝ)^2)):=by ring
  have hr:(2^70:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)=(2^70:ℝ)*((Y:ℝ)/((Nat.log 2 Y:ℝ)^2)):=by ring
  nlinarith only [hnn,hl,hr]
 linarith only [hcomb,hSmall,hLarge,hfin]
lemma gr_sp (r L0:ℕ) (_hL0:1<=L0) :
  ∀ (T:Finset ℕ),(¬ ∃ f:Fin (r+1)->ℕ,(∀ i,f i∈T)/\∀ i:Fin r,f i.castSucc+L0<=f i.succ)->T.card<=r*L0:=by
 induction r with
 | zero =>
  intro T hno
  by_contra hpos;push Not at hpos
  have hne:T.Nonempty:=card_pos.mp (by omega)
  obtain ⟨x,hx⟩:=hne
  exact hno ⟨fun _ => x,fun _ => hx,fun i => i.elim0⟩
 | succ r ih =>
  intro T hno
  by_cases hne:T.Nonempty
  ·
   let x:=T.min' hne
   have hx_mem:x∈T:=min'_mem T hne
   let Tlo:=T.filter (fun y => y < x+L0)
   let Thi:=T.filter (fun y => x+L0<=y)
   have hT_sub:T⊆Tlo∪Thi:=by
    intro y hy;rw [mun,mf,mf]
    by_cases h:y < x+L0
    · exact Or.inl ⟨hy,h⟩
    · exact Or.inr ⟨hy,by omega⟩
   have hTlo:Tlo.card<=L0:=by
    have hsub:Tlo⊆Ico x (x+L0):=by
     intro y hy
     exact mico.mpr ⟨min'_le T y (mf.mp hy).1,(mf.mp hy).2⟩
    calc Tlo.card<=(Ico x (x+L0)).card:=clc hsub
     _=L0:=by simp
   have hThi:Thi.card<=r*L0:=by
    apply ih Thi
    rintro ⟨f,hf_mem,hf_gap⟩
    let g:Fin (r+2)->ℕ:=Fin.cases x f
    apply hno
    refine ⟨g,fun i => ?_,fun i => ?_⟩
    ·
     refine Fin.cases ?_ ?_ i
     · exact hx_mem
     · intro j;exact (mf.mp (hf_mem j)).1
    ·
     refine Fin.cases ?_ ?_ i
     ·
      change x+L0<=f 0
      exact (mf.mp (hf_mem 0)).2
     ·
      intro j
      change f j.castSucc+L0<=f j.succ
      exact hf_gap j
   have hcard:T.card<=Tlo.card+Thi.card:=ltr (clc hT_sub) (cul _ _)
   nlinarith only [hcard,hTlo,hThi]
  · rw [not_nonempty_iff_eq_empty] at hne;simp [hne]
lemma sh_sp (P Lblk r L0:ℕ) (hL0:1<=L0) (S:Finset ℕ)
  (hS_sub:S⊆Ioc P (2*P))
  (hno:∀ a:ℕ,¬ ∃ f:Fin (r+1)->ℕ,(∀ i,f i∈S/\a<=f i/\f i<=a+Lblk)/\∀ i:Fin r,f i.castSucc+L0<=f i.succ) :
  S.card<=(P/(Lblk+1)+1)*(r*L0):=by
 let B:ℕ->Finset ℕ:=fun t =>
  S.filter (fun p => P+1+t*(Lblk+1)<=p/\p<=P+1+t*(Lblk+1)+Lblk)
 have hcov:S⊆(range (P/(Lblk+1)+1)).biUnion B:=by
  intro p hp
  have hpIoc:=mioc.mp (hS_sub hp)
  let t:=(p - (P+1))/(Lblk+1)
  rw [mbu]
  refine ⟨t,mrng.mpr ?_,mf.mpr ⟨hp,?_,?_⟩⟩
  ·
   have:t<=P/(Lblk+1):=ddlr (by omega)
   omega
  ·
   have hmul:t*(Lblk+1)<=p - (P+1):=dls (p - (P+1)) (Lblk+1)
   omega
  ·
   have hlt:p - (P+1) < (t+1)*(Lblk+1):=by
    have h1:p - (P+1) < (Lblk+1)*(t+1):=lmd (p - (P+1)) (by omega:0 < Lblk+1)
    linarith only [h1]
   have hexp:(t+1)*(Lblk+1)=t*(Lblk+1)+Lblk+1:=by ring
   omega
 have hB:∀ t∈range (P/(Lblk+1)+1),(B t).card<=r*L0:=by
  intro t _
  apply gr_sp r L0 hL0 (B t)
  rintro ⟨f,hf_mem,hf_gap⟩
  exact hno (P+1+t*(Lblk+1)) ⟨f,fun i => by
   have h:=mf.mp (hf_mem i);exact ⟨h.1,h.2.1,h.2.2⟩,hf_gap⟩
 calc S.card<=((range (P/(Lblk+1)+1)).biUnion B).card:=clc hcov
  _<=∑ t∈range (P/(Lblk+1)+1),(B t).card:=cbi
  _<=∑ _t∈range (P/(Lblk+1)+1),r*L0:=sls hB
  _=(P/(Lblk+1)+1)*(r*L0):=by simp
lemma divdiff2_inv_sq {p1 p2 p3:ℝ} (h1:p1≠0) (h2:p2≠0) (h3:p3≠0) :
  (p3 - p2)/p1^2 - (p3 - p1)/p2^2+(p2 - p1)/p3^2=(p2 - p1)*(p3 - p2)*(p3 - p1)*(p1*p2+p2*p3+p3*p1) /
    (p1^2*p2^2*p3^2):=by
 field_simp;ring
lemma divdiff3_inv_sq {p1 p2 p3 p4:ℝ} (h1:p1≠0) (h2:p2≠0) (h3:p3≠0) (h4:p4≠0) :
  ((p3 - p2)*(p4 - p2)*(p4 - p3))/p1^2 -
   ((p3 - p1)*(p4 - p1)*(p4 - p3))/p2^2+((p2 - p1)*(p4 - p1)*(p4 - p2))/p3^2 -
   ((p2 - p1)*(p3 - p1)*(p3 - p2))/p4^2=(p2 - p1)*(p3 - p1)*(p4 - p1)*(p3 - p2)*(p4 - p2)*(p4 - p3)*(p1*p2*p3+p1*p2*p4+p1*p3*p4+p2*p3*p4) /
    (p1^2*p2^2*p3^2*p4^2):=by
 field_simp;ring
lemma no_t2 (Y H P m:ℕ) (hY:2<=Y) (hH_pos:1<=H)
  (hH3:H^3 < 3*Y*P^2) (hP_pos:1<=P)
  (hm_lo:Y/2 < m) (hm_hi:m<=Y)
  (p1 p2 p3 a1 a2 a3:ℕ)
  (hp1:P < p1) (hp3:p3<=2*P)
  (hgap1:natRoot 2 (64*H*P^2/Y)+1<=p2 - p1)
  (hgap2:natRoot 2 (64*H*P^2/Y)+1<=p3 - p2)
  (hord1:p1 < p2) (hord2:p2 < p3)
  (hspan:p3 - p1<=natRoot 3 (P^4/(24*Y)))
  (ha1:m+1<=a1*p1^2/\a1*p1^2<=m+H)
  (ha2:m+1<=a2*p2^2/\a2*p2^2<=m+H)
  (ha3:m+1<=a3*p3^2/\a3*p3^2<=m+H):False:=by
 set L0:=natRoot 2 (64*H*P^2/Y)+1
 set L2:=natRoot 3 (P^4/(24*Y))
 let N2:ℤ:=((p3 - p2:ℕ):ℤ)*(a1:ℤ) - ((p3 - p1:ℕ):ℤ)*(a2:ℤ)+((p2 - p1:ℕ):ℤ)*(a3:ℤ)
 have hPpos:(0:ℝ) < (P:ℝ):=by exact_mod_cast hP_pos
 have hYpos:(0:ℝ) < (Y:ℝ):=by exact_mod_cast (by omega:0 < Y)
 have hHpos:(0:ℝ) < (H:ℝ):=by exact_mod_cast hH_pos
 have hp1_pos:(0:ℝ) < (p1:ℝ):=by exact_mod_cast (by omega:0 < p1)
 have hp2_pos:(0:ℝ) < (p2:ℝ):=by exact_mod_cast (by omega:0 < p2)
 have hp3_pos:(0:ℝ) < (p3:ℝ):=by exact_mod_cast (by omega:0 < p3)
 let e1:ℝ:=(a1:ℝ) - (m:ℝ)/(p1:ℝ)^2
 let e2:ℝ:=(a2:ℝ) - (m:ℝ)/(p2:ℝ)^2
 let e3:ℝ:=(a3:ℝ) - (m:ℝ)/(p3:ℝ)^2
 have he_bd:∀ (a p:ℕ),P < p->m+1<=a*p^2->a*p^2<=m+H->0<=(a:ℝ) - (m:ℝ)/(p:ℝ)^2/\(a:ℝ) - (m:ℝ)/(p:ℝ)^2<=(H:ℝ)/(P:ℝ)^2:=by
  intro a p hp hlo hhi
  have hpR:(0:ℝ) < (p:ℝ):=by exact_mod_cast (by omega:0 < p)
  have hloR:(m:ℝ)<=(a:ℝ)*(p:ℝ)^2:=by exact_mod_cast (by omega:m<=a*p^2)
  have hhiR:(a:ℝ)*(p:ℝ)^2<=(m:ℝ)+(H:ℝ):=by exact_mod_cast hhi
  constructor
  · rw [sub_nonneg,dli (by positivity)];exact hloR
  ·
   have h1:(a:ℝ) - (m:ℝ)/(p:ℝ)^2<=(H:ℝ)/(p:ℝ)^2:=by
    rw [sub_le_iff_le_add,← add_div,ldi (by positivity)];linarith only [hhiR]
   have h2:(H:ℝ)/(p:ℝ)^2<=(H:ℝ)/(P:ℝ)^2:=by gcongr
   linarith only [h1,h2]
 have he1:=he_bd a1 p1 hp1 ha1.1 ha1.2
 have he2:=he_bd a2 p2 (by omega) ha2.1 ha2.2
 have he3:=he_bd a3 p3 (by omega) ha3.1 ha3.2
 set M2:ℝ:=(m:ℝ)*(((p2:ℝ) - p1)*((p3:ℝ) - p2)*((p3:ℝ) - p1)*((p1:ℝ)*p2+p2*p3+p3*p1)/((p1:ℝ)^2*(p2:ℝ)^2*(p3:ℝ)^2))
 set E2:ℝ:=((p3:ℝ) - p2)*e1 - ((p3:ℝ) - p1)*e2+((p2:ℝ) - p1)*e3
 have hN2_eq:(N2:ℝ)=M2+E2:=by
  have hcast:(N2:ℝ)=((p3:ℝ) - p2)*(a1:ℝ) - ((p3:ℝ) - p1)*(a2:ℝ)+((p2:ℝ) - p1)*(a3:ℝ):=by
   dsimp only [N2];push_cast
   rw [ncs (by omega),ncs (by omega),ncs (by omega)]
  have hid:=divdiff2_inv_sq hp1_pos.ne' hp2_pos.ne' hp3_pos.ne'
  dsimp only [M2,E2,e1,e2,e3]
  rw [hcast,← hid];ring
 have hd1:(0:ℝ)<=(p2:ℝ) - p1:=by
  have:(p1:ℝ)<=(p2:ℝ):=by exact_mod_cast lol hord1
  linarith only [this]
 have hd2:(0:ℝ)<=(p3:ℝ) - p2:=by
  have:(p2:ℝ)<=(p3:ℝ):=by exact_mod_cast lol hord2
  linarith only [this]
 have hd3:(0:ℝ) < (p3:ℝ) - p1:=by
  have:(p1:ℝ) < (p3:ℝ):=by exact_mod_cast (by omega:p1 < p3)
  linarith only [this]
 have hE2_lo:-(((p3:ℝ) - p1)*((H:ℝ)/(P:ℝ)^2))<=E2:=by
  dsimp only [E2]
  have h1:0<=((p3:ℝ) - p2)*e1:=mul_nonneg hd2 he1.1
  have h2:0<=((p2:ℝ) - p1)*e3:=mul_nonneg hd1 he3.1
  have h3:((p3:ℝ) - p1)*e2<=((p3:ℝ) - p1)*((H:ℝ)/(P:ℝ)^2):=ml he2.2 (lol hd3)
  linarith only [h1,h2,h3]
 have hE2_hi:E2<=((p3:ℝ) - p1)*((H:ℝ)/(P:ℝ)^2):=by
  dsimp only [E2]
  have h1:((p3:ℝ) - p2)*e1<=((p3:ℝ) - p2)*((H:ℝ)/(P:ℝ)^2):=ml he1.2 hd2
  have h2:((p2:ℝ) - p1)*e3<=((p2:ℝ) - p1)*((H:ℝ)/(P:ℝ)^2):=ml he3.2 hd1
  have h3:0<=((p3:ℝ) - p1)*e2:=mul_nonneg (lol hd3) he2.1
  linarith only [h1,h2,h3]
 have hM2_gt:((p3:ℝ) - p1)*((H:ℝ)/(P:ℝ)^2) < M2:=by
  have hL0_sq:64*(H:ℝ)*(P:ℝ)^2/(Y:ℝ) < (L0:ℝ)^2:=by
   have hlt:=lt_succ_natRoot_pow 2 (64*H*P^2/Y) (by omega)
   have hnat:64*H*P^2 < L0^2*Y:=by
    have h1:64*H*P^2/Y+1<=L0^2:=hlt
    have h2:=lmd (64*H*P^2) (by omega:0 < Y)
    have h3:Y*(64*H*P^2/Y+1)<=Y*L0^2:=nml Y h1
    linarith only [h2,h3]
   rw [div_lt_iff₀ hYpos]
   have hR:((64*H*P^2:ℕ):ℝ) < ((L0^2*Y:ℕ):ℝ):=by exact_mod_cast hnat
   push_cast at hR;linarith only [hR]
  have hg1:(L0:ℝ)<=(p2:ℝ) - p1:=by
   have:(L0:ℝ)<=((p2 - p1:ℕ):ℝ):=by exact_mod_cast hgap1
   rw [ncs (by omega)] at this;exact this
  have hg2:(L0:ℝ)<=(p3:ℝ) - p2:=by
   have:(L0:ℝ)<=((p3 - p2:ℕ):ℝ):=by exact_mod_cast hgap2
   rw [ncs (by omega)] at this;exact this
  have hm_ge:(Y:ℝ)/2<=(m:ℝ):=by
   have hnat:Y<=2*m:=by omega
   have hR:(Y:ℝ)<=2*(m:ℝ):=by exact_mod_cast hnat
   linarith only [hR]
  have hp1P:(P:ℝ)<=(p1:ℝ):=by exact_mod_cast lol hp1
  have hp2P:(P:ℝ)<=(p2:ℝ):=by exact_mod_cast (by omega:P<=p2)
  have hp3P:(P:ℝ)<=(p3:ℝ):=by exact_mod_cast (by omega:P<=p3)
  have hp1_2P:(p1:ℝ)<=2*(P:ℝ):=by exact_mod_cast (by omega:p1<=2*P)
  have hp2_2P:(p2:ℝ)<=2*(P:ℝ):=by exact_mod_cast (by omega:p2<=2*P)
  have hp3_2P:(p3:ℝ)<=2*(P:ℝ):=by exact_mod_cast hp3
  have hsum_lo:3*(P:ℝ)^2<=(p1:ℝ)*p2+p2*p3+p3*p1:=by
   nlinarith only [hp1P,hp2P,hp3P,hPpos]
  have hden_hi:(p1:ℝ)^2*(p2:ℝ)^2*(p3:ℝ)^2<=64*(P:ℝ)^6:=by
   have h1:(p1:ℝ)^2<=4*(P:ℝ)^2:=by nlinarith only [hp1_2P,hp1_pos]
   have h2:(p2:ℝ)^2<=4*(P:ℝ)^2:=by nlinarith only [hp2_2P,hp2_pos]
   have h3:(p3:ℝ)^2<=4*(P:ℝ)^2:=by nlinarith only [hp3_2P,hp3_pos]
   have h12:(p1:ℝ)^2*(p2:ℝ)^2<=16*(P:ℝ)^4:=by
    have:=mlm h1 h2 (by positivity) (by positivity);linarith only [this]
   have:=mlm h12 h3 (by positivity) (by positivity);linarith only [this]
  have hnum_lo:(Y:ℝ)/2*((L0:ℝ)^2*((p3:ℝ) - p1)*(3*(P:ℝ)^2))<=(m:ℝ)*(((p2:ℝ) - p1)*((p3:ℝ) - p2)*((p3:ℝ) - p1)*((p1:ℝ)*p2+p2*p3+p3*p1)):=by
   have hL0nn:(0:ℝ)<=(L0:ℝ):=by positivity
   have hprod:(L0:ℝ)^2<=((p2:ℝ) - p1)*((p3:ℝ) - p2):=by
    have:=mlm hg1 hg2 hL0nn hd1;linarith only [this]
   have hprod2:(L0:ℝ)^2*((p3:ℝ) - p1)<=((p2:ℝ) - p1)*((p3:ℝ) - p2)*((p3:ℝ) - p1):=mr hprod (lol hd3)
   have hprod3:(L0:ℝ)^2*((p3:ℝ) - p1)*(3*(P:ℝ)^2)<=((p2:ℝ) - p1)*((p3:ℝ) - p2)*((p3:ℝ) - p1)*((p1:ℝ)*p2+p2*p3+p3*p1):=mlm hprod2 hsum_lo (by positivity) (by positivity)
   exact mlm hm_ge hprod3 (by positivity) (by positivity)
  have hM2_ge:(Y:ℝ)/2*((L0:ℝ)^2*((p3:ℝ) - p1)*(3*(P:ℝ)^2))/(64*(P:ℝ)^6)<=M2:=by
   dsimp only [M2]
   rw [← mul_div_assoc]
   exact div_le_div₀ (by positivity) hnum_lo (by positivity) hden_hi
  have hstrict:((p3:ℝ) - p1)*((H:ℝ)/(P:ℝ)^2) < (Y:ℝ)/2*((L0:ℝ)^2*((p3:ℝ) - p1)*(3*(P:ℝ)^2))/(64*(P:ℝ)^6):=by
   have h1:=mul_lt_mul_of_pos_left hL0_sq (by positivity:(0:ℝ) < 3*(Y:ℝ)*((p3:ℝ) - p1)*(P:ℝ)^2/(128*(P:ℝ)^6))
   have hl:3*(Y:ℝ)*((p3:ℝ) - p1)*(P:ℝ)^2/(128*(P:ℝ)^6)*(64*(H:ℝ)*(P:ℝ)^2/(Y:ℝ))=(3/2:ℝ)*(((p3:ℝ) - p1)*((H:ℝ)/(P:ℝ)^2)):=by field_simp;ring
   have hr:3*(Y:ℝ)*((p3:ℝ) - p1)*(P:ℝ)^2/(128*(P:ℝ)^6)*(L0:ℝ)^2=(Y:ℝ)/2*((L0:ℝ)^2*((p3:ℝ) - p1)*(3*(P:ℝ)^2))/(64*(P:ℝ)^6):=by ring
   have hpos_t:(0:ℝ) < ((p3:ℝ) - p1)*((H:ℝ)/(P:ℝ)^2):=by positivity
   linarith only [h1,hl,hr,hpos_t]
  linarith only [hstrict,hM2_ge]
 have hM2_le:M2<=1/2:=by
  have hL2_cub:(L2:ℝ)^3<=(P:ℝ)^4/(24*(Y:ℝ)):=by
   have h1:=natRoot_pow_le 3 (P^4/(24*Y)) (by omega)
   have h2:L2^3*(24*Y)<=P^4:=ltr (nmr _ h1) (dls _ _)
   rw [ldi (by positivity)]
   have hR:((L2^3*(24*Y):ℕ):ℝ)<=((P^4:ℕ):ℝ):=by exact_mod_cast h2
   push_cast at hR;linarith only [hR]
  have hs3:(p3:ℝ) - p1<=(L2:ℝ):=by
   have hR:((p3 - p1:ℕ):ℝ)<=(L2:ℝ):=by exact_mod_cast hspan
   rw [ncs (by omega)] at hR;exact hR
  have hs1:(p2:ℝ) - p1<=(L2:ℝ):=by linarith only [hs3,hd2]
  have hs2:(p3:ℝ) - p2<=(L2:ℝ):=by linarith only [hs3,hd1]
  have hp1_2P:(p1:ℝ)<=2*(P:ℝ):=by exact_mod_cast (by omega:p1<=2*P)
  have hp2_2P:(p2:ℝ)<=2*(P:ℝ):=by exact_mod_cast (by omega:p2<=2*P)
  have hp3_2P:(p3:ℝ)<=2*(P:ℝ):=by exact_mod_cast hp3
  have hsum_hi:(p1:ℝ)*p2+p2*p3+p3*p1<=12*(P:ℝ)^2:=by
   nlinarith only [hp1_2P,hp2_2P,hp3_2P,hp1_pos,hp2_pos,hp3_pos]
  have hp1P:(P:ℝ)<=(p1:ℝ):=by exact_mod_cast lol hp1
  have hp2P:(P:ℝ)<=(p2:ℝ):=by exact_mod_cast (by omega:P<=p2)
  have hp3P:(P:ℝ)<=(p3:ℝ):=by exact_mod_cast (by omega:P<=p3)
  have hden_lo:(P:ℝ)^6<=(p1:ℝ)^2*(p2:ℝ)^2*(p3:ℝ)^2:=by
   have h1:(P:ℝ)^2<=(p1:ℝ)^2:=by gcongr
   have h2:(P:ℝ)^2<=(p2:ℝ)^2:=by gcongr
   have h3:(P:ℝ)^2<=(p3:ℝ)^2:=by gcongr
   have h12:(P:ℝ)^4<=(p1:ℝ)^2*(p2:ℝ)^2:=by
    have:=mlm h1 h2 (by positivity) (by positivity);linarith only [this]
   have:=mlm h12 h3 (by positivity) (by positivity);linarith only [this]
  have hprod_hi:((p2:ℝ) - p1)*((p3:ℝ) - p2)*((p3:ℝ) - p1)<=(L2:ℝ)^3:=by
   have h12:=mlm hs1 hs2 hd2 (by positivity)
   have h123:=mlm h12 hs3 (lol hd3) (by positivity)
   linarith only [h123]
  have hnum_hi:(m:ℝ)*(((p2:ℝ) - p1)*((p3:ℝ) - p2)*((p3:ℝ) - p1)*((p1:ℝ)*p2+p2*p3+p3*p1))<=(Y:ℝ)*((L2:ℝ)^3*(12*(P:ℝ)^2)):=by
   have hmR:(m:ℝ)<=(Y:ℝ):=by exact_mod_cast hm_hi
   have h1:=mlm hprod_hi hsum_hi (by positivity) (by positivity)
   exact mlm hmR h1 (by positivity) (by positivity)
  have hM2_ub:M2<=(Y:ℝ)*((L2:ℝ)^3*(12*(P:ℝ)^2))/(P:ℝ)^6:=by
   dsimp only [M2];rw [← mul_div_assoc]
   exact div_le_div₀ (by positivity) hnum_hi (by positivity) hden_lo
  have hfin:(Y:ℝ)*((L2:ℝ)^3*(12*(P:ℝ)^2))/(P:ℝ)^6<=1/2:=by
   have h1:=ml hL2_cub (by positivity:(0:ℝ)<=12*(Y:ℝ)*(P:ℝ)^2/(P:ℝ)^6)
   have hl:12*(Y:ℝ)*(P:ℝ)^2/(P:ℝ)^6*(L2:ℝ)^3=(Y:ℝ)*((L2:ℝ)^3*(12*(P:ℝ)^2))/(P:ℝ)^6:=by ring
   have hr:12*(Y:ℝ)*(P:ℝ)^2/(P:ℝ)^6*((P:ℝ)^4/(24*(Y:ℝ)))=1/2:=by
    field_simp;ring
   linarith only [h1,hl,hr]
  linarith only [hM2_ub,hfin]
 have hE2_lt:E2 < 1/2:=by
  have hs3:(p3:ℝ) - p1<=(L2:ℝ):=by
   have hR:((p3 - p1:ℕ):ℝ)<=(L2:ℝ):=by exact_mod_cast hspan
   rw [ncs (by omega)] at hR;exact hR
  have h1:E2<=(L2:ℝ)*((H:ℝ)/(P:ℝ)^2):=ltr hE2_hi (mr hs3 (by positivity))
  have hlt3:((L2:ℝ)*((H:ℝ)/(P:ℝ)^2))^3 < (1/2:ℝ)^3:=by
   have hL2_cub:(L2:ℝ)^3<=(P:ℝ)^4/(24*(Y:ℝ)):=by
    have hA:=natRoot_pow_le 3 (P^4/(24*Y)) (by omega)
    have hB:L2^3*(24*Y)<=P^4:=ltr (nmr _ hA) (dls _ _)
    rw [ldi (by positivity)]
    have hR:((L2^3*(24*Y):ℕ):ℝ)<=((P^4:ℕ):ℝ):=by exact_mod_cast hB
    push_cast at hR;linarith only [hR]
   have hH3R:(H:ℝ)^3 < 3*(Y:ℝ)*(P:ℝ)^2:=by
    have hR:((H^3:ℕ):ℝ) < ((3*Y*P^2:ℕ):ℝ):=by exact_mod_cast hH3
    push_cast at hR;linarith only [hR]
   have hA:((L2:ℝ)*((H:ℝ)/(P:ℝ)^2))^3=(L2:ℝ)^3*((H:ℝ)^3/(P:ℝ)^6):=by ring
   have hB:(L2:ℝ)^3*((H:ℝ)^3/(P:ℝ)^6)<=(P:ℝ)^4/(24*(Y:ℝ))*((H:ℝ)^3/(P:ℝ)^6):=mr hL2_cub (by positivity)
   have hC:(P:ℝ)^4/(24*(Y:ℝ))*((H:ℝ)^3/(P:ℝ)^6) < (P:ℝ)^4/(24*(Y:ℝ))*((3*(Y:ℝ)*(P:ℝ)^2)/(P:ℝ)^6):=by
    gcongr
   have hD:(P:ℝ)^4/(24*(Y:ℝ))*((3*(Y:ℝ)*(P:ℝ)^2)/(P:ℝ)^6)=(1/2:ℝ)^3:=by
    field_simp;ring
   linarith only [hA,hB,hC,hD]
  have hlt1:(L2:ℝ)*((H:ℝ)/(P:ℝ)^2) < 1/2:=by
   by_contra hge;push Not at hge
   have:(1/2:ℝ)^3<=((L2:ℝ)*((H:ℝ)/(P:ℝ)^2))^3:=by gcongr
   linarith only [hlt3,this]
  linarith only [h1,hlt1]
 have hN2_pos:(0:ℝ) < (N2:ℝ):=by linarith only [hN2_eq,hM2_gt,hE2_lo]
 have hN2_lt1:(N2:ℝ) < 1:=by linarith only [hN2_eq,hM2_le,hE2_lt]
 have hZpos:(0:ℤ) < N2:=by exact_mod_cast hN2_pos
 have hZlt1:N2 < (1:ℤ):=by exact_mod_cast hN2_lt1
 omega
lemma dd3_le (Y P m L3 p1 p2 p3 p4:ℕ)
  (hY:2<=Y) (hP_pos:1<=P) (hm_hi:m<=Y)
  (hp1:P < p1) (hord1:p1 < p2) (hord2:p2 < p3) (hord3:p3 < p4) (hp4:p4<=2*P)
  (hspan:p4 - p1<=L3) (hL3_6:(L3:ℝ)^6<=(P:ℝ)^5/(64*(Y:ℝ))) :
  (m:ℝ)*(((p2:ℝ) - p1)*((p3:ℝ) - p1)*((p4:ℝ) - p1)*((p3:ℝ) - p2)*((p4:ℝ) - p2)*((p4:ℝ) - p3)*((p1:ℝ)*p2*p3+p1*p2*p4+p1*p3*p4+p2*p3*p4) /
   ((p1:ℝ)^2*(p2:ℝ)^2*(p3:ℝ)^2*(p4:ℝ)^2))<=1/2:=by
 have hPpos:(0:ℝ) < (P:ℝ):=by exact_mod_cast hP_pos
 have hYpos:(0:ℝ) < (Y:ℝ):=by exact_mod_cast (by omega:0 < Y)
 have hp1_pos:(0:ℝ) < (p1:ℝ):=by exact_mod_cast (by omega:0 < p1)
 have hp2_pos:(0:ℝ) < (p2:ℝ):=by exact_mod_cast (by omega:0 < p2)
 have hp3_pos:(0:ℝ) < (p3:ℝ):=by exact_mod_cast (by omega:0 < p3)
 have hp4_pos:(0:ℝ) < (p4:ℝ):=by exact_mod_cast (by omega:0 < p4)
 set Δ:ℝ:=((p2:ℝ) - p1)*((p3:ℝ) - p1)*((p4:ℝ) - p1)*((p3:ℝ) - p2)*((p4:ℝ) - p2)*((p4:ℝ) - p3)
 have hsub_le:∀ x y:ℕ,p1<=x->x<=y->y<=p4->(y:ℝ) - (x:ℝ)<=(L3:ℝ):=by
  intro x y hx hxy hy
  have hR:((y - x:ℕ):ℝ)<=(L3:ℝ):=by exact_mod_cast (by omega:y - x<=L3)
  rw [ncs hxy] at hR;exact hR
 have hpos:∀ x y:ℕ,x<=y->(0:ℝ)<=(y:ℝ) - (x:ℝ):=by
  intro x y h
  have hxy:(x:ℝ)<=(y:ℝ):=by exact_mod_cast h
  linarith only [hxy]
 have hΔ_hi:Δ<=(L3:ℝ)^6:=by
  have ha:=hsub_le p1 p2 (le_refl _) (lol hord1) (by omega)
  have hb:=hsub_le p1 p3 (le_refl _) (by omega) (lol hord3)
  have hc:=hsub_le p1 p4 (le_refl _) (by omega) (le_refl _)
  have hd:=hsub_le p2 p3 (lol hord1) (lol hord2) (lol hord3)
  have he:=hsub_le p2 p4 (lol hord1) (by omega) (le_refl _)
  have hf:=hsub_le p3 p4 (by omega) (lol hord3) (le_refl _)
  have h12:=mlm ha hb (hpos p1 p3 (by omega)) (by positivity)
  have h123:=mlm h12 hc (hpos p1 p4 (by omega)) (by positivity)
  have h45:=mlm hd he (hpos p2 p4 (by omega)) (by positivity)
  have h456:=mlm h45 hf (hpos p3 p4 (by omega)) (by positivity)
  have h456_nn:(0:ℝ)<=((p3:ℝ) - p2)*((p4:ℝ) - p2)*((p4:ℝ) - p3):=mul_nonneg (mul_nonneg (hpos p2 p3 (lol hord2)) (hpos p2 p4 (by omega))) (hpos p3 p4 (lol hord3))
  have h16:=mlm h123 h456 h456_nn (by positivity)
  have hpow:((L3:ℝ)*L3*L3)*((L3:ℝ)*L3*L3)=(L3:ℝ)^6:=by ring
  have hΔeq:Δ=(((p2:ℝ) - p1)*((p3:ℝ) - p1)*((p4:ℝ) - p1))*(((p3:ℝ) - p2)*((p4:ℝ) - p2)*((p4:ℝ) - p3)):=by dsimp only [Δ];ring
  linarith only [h16,hpow,hΔeq]
 have hp1_2P:(p1:ℝ)<=2*(P:ℝ):=by exact_mod_cast (by omega:p1<=2*P)
 have hp2_2P:(p2:ℝ)<=2*(P:ℝ):=by exact_mod_cast (by omega:p2<=2*P)
 have hp3_2P:(p3:ℝ)<=2*(P:ℝ):=by exact_mod_cast (by omega:p3<=2*P)
 have hp4_2P:(p4:ℝ)<=2*(P:ℝ):=by exact_mod_cast hp4
 have hsum_hi:(p1:ℝ)*p2*p3+p1*p2*p4+p1*p3*p4+p2*p3*p4<=32*(P:ℝ)^3:=by
  have h3:∀ a b c:ℝ,0<=b->0<=c->a<=2*(P:ℝ)->b<=2*(P:ℝ)->c<=2*(P:ℝ)->a*b*c<=8*(P:ℝ)^3:=by
   intro a b c hb hc ha' hb' hc'
   have:=mlm (mlm ha' hb' hb (by positivity)) hc' hc (by positivity)
   linarith only [this]
  have ha:=h3 p1 p2 p3 (lol hp2_pos) (lol hp3_pos) hp1_2P hp2_2P hp3_2P
  have hb:=h3 p1 p2 p4 (lol hp2_pos) (lol hp4_pos) hp1_2P hp2_2P hp4_2P
  have hc:=h3 p1 p3 p4 (lol hp3_pos) (lol hp4_pos) hp1_2P hp3_2P hp4_2P
  have hd:=h3 p2 p3 p4 (lol hp3_pos) (lol hp4_pos) hp2_2P hp3_2P hp4_2P
  linarith only [ha,hb,hc,hd]
 have hp1P:(P:ℝ)<=(p1:ℝ):=by exact_mod_cast lol hp1
 have hp2P:(P:ℝ)<=(p2:ℝ):=by exact_mod_cast (by omega:P<=p2)
 have hp3P:(P:ℝ)<=(p3:ℝ):=by exact_mod_cast (by omega:P<=p3)
 have hp4P:(P:ℝ)<=(p4:ℝ):=by exact_mod_cast (by omega:P<=p4)
 have hden_lo:(P:ℝ)^8<=(p1:ℝ)^2*(p2:ℝ)^2*(p3:ℝ)^2*(p4:ℝ)^2:=by
  have h1:(P:ℝ)^2<=(p1:ℝ)^2:=by gcongr
  have h2:(P:ℝ)^2<=(p2:ℝ)^2:=by gcongr
  have h3:(P:ℝ)^2<=(p3:ℝ)^2:=by gcongr
  have h4:(P:ℝ)^2<=(p4:ℝ)^2:=by gcongr
  have h12:(P:ℝ)^4<=(p1:ℝ)^2*(p2:ℝ)^2:=by
   have:=mlm h1 h2 (by positivity) (by positivity);linarith only [this]
  have h34:(P:ℝ)^4<=(p3:ℝ)^2*(p4:ℝ)^2:=by
   have:=mlm h3 h4 (by positivity) (by positivity);linarith only [this]
  have:=mlm h12 h34 (by positivity) (by positivity);linarith only [this]
 have hnum_hi:(m:ℝ)*(Δ*((p1:ℝ)*p2*p3+p1*p2*p4+p1*p3*p4+p2*p3*p4))<=(Y:ℝ)*((L3:ℝ)^6*(32*(P:ℝ)^3)):=by
  have hmR:(m:ℝ)<=(Y:ℝ):=by exact_mod_cast hm_hi
  have h1:=mlm hΔ_hi hsum_hi (by positivity) (by positivity)
  have hΔnn:(0:ℝ)<=Δ:=by
   dsimp only [Δ]
   exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hpos p1 p2 (lol hord1))
    (hpos p1 p3 (by omega))) (hpos p1 p4 (by omega))) (hpos p2 p3 (lol hord2)))
    (hpos p2 p4 (by omega))) (hpos p3 p4 (lol hord3))
  exact mlm hmR h1 (by positivity) (by positivity)
 have hM3_ub:(m:ℝ)*(Δ*((p1:ℝ)*p2*p3+p1*p2*p4+p1*p3*p4+p2*p3*p4) /
   ((p1:ℝ)^2*(p2:ℝ)^2*(p3:ℝ)^2*(p4:ℝ)^2))<=(Y:ℝ)*((L3:ℝ)^6*(32*(P:ℝ)^3))/(P:ℝ)^8:=by
  rw [← mul_div_assoc]
  exact div_le_div₀ (by positivity) hnum_hi (by positivity) hden_lo
 have hfin:(Y:ℝ)*((L3:ℝ)^6*(32*(P:ℝ)^3))/(P:ℝ)^8<=1/2:=by
  have h1:=ml hL3_6 (by positivity:(0:ℝ)<=32*(Y:ℝ)*(P:ℝ)^3/(P:ℝ)^8)
  have hl:32*(Y:ℝ)*(P:ℝ)^3/(P:ℝ)^8*(L3:ℝ)^6=(Y:ℝ)*((L3:ℝ)^6*(32*(P:ℝ)^3))/(P:ℝ)^8:=by ring
  have hr:32*(Y:ℝ)*(P:ℝ)^3/(P:ℝ)^8*((P:ℝ)^5/(64*(Y:ℝ)))=1/2:=by
   field_simp;ring
  linarith only [h1,hl,hr]
 linarith only [hM3_ub,hfin]
lemma no_q3 (Y H P m:ℕ) (hY:2<=Y) (hH_pos:1<=H)
  (hPH2:P*H^2 < 4*Y) (hP_pos:1<=P)
  (hm_lo:Y/2 < m) (hm_hi:m<=Y)
  (p1 p2 p3 p4 a1 a2 a3 a4:ℕ)
  (hp1:P < p1) (hp4:p4<=2*P)
  (hgap1:natRoot 3 (256*H*P^3/Y)+1<=p2 - p1)
  (hgap2:natRoot 3 (256*H*P^3/Y)+1<=p3 - p2)
  (hgap3:natRoot 3 (256*H*P^3/Y)+1<=p4 - p3)
  (hord1:p1 < p2) (hord2:p2 < p3) (hord3:p3 < p4)
  (hspan:p4 - p1<=natRoot 6 (P^5/(64*Y)))
  (ha1:m+1<=a1*p1^2/\a1*p1^2<=m+H)
  (ha2:m+1<=a2*p2^2/\a2*p2^2<=m+H)
  (ha3:m+1<=a3*p3^2/\a3*p3^2<=m+H)
  (ha4:m+1<=a4*p4^2/\a4*p4^2<=m+H):False:=by
 set L0:=natRoot 3 (256*H*P^3/Y)+1
 set L3:=natRoot 6 (P^5/(64*Y))
 let c1:ℕ:=(p3 - p2)*(p4 - p2)*(p4 - p3)
 let c2:ℕ:=(p3 - p1)*(p4 - p1)*(p4 - p3)
 let c3:ℕ:=(p2 - p1)*(p4 - p1)*(p4 - p2)
 let c4:ℕ:=(p2 - p1)*(p3 - p1)*(p3 - p2)
 let N3:ℤ:=(c1:ℤ)*(a1:ℤ) - (c2:ℤ)*(a2:ℤ)+(c3:ℤ)*(a3:ℤ) - (c4:ℤ)*(a4:ℤ)
 have hPpos:(0:ℝ) < (P:ℝ):=by exact_mod_cast hP_pos
 have hYpos:(0:ℝ) < (Y:ℝ):=by exact_mod_cast (by omega:0 < Y)
 have hHpos:(0:ℝ) < (H:ℝ):=by exact_mod_cast hH_pos
 have hp1_pos:(0:ℝ) < (p1:ℝ):=by exact_mod_cast (by omega:0 < p1)
 have hp2_pos:(0:ℝ) < (p2:ℝ):=by exact_mod_cast (by omega:0 < p2)
 have hp3_pos:(0:ℝ) < (p3:ℝ):=by exact_mod_cast (by omega:0 < p3)
 have hp4_pos:(0:ℝ) < (p4:ℝ):=by exact_mod_cast (by omega:0 < p4)
 let e1:ℝ:=(a1:ℝ) - (m:ℝ)/(p1:ℝ)^2
 let e2:ℝ:=(a2:ℝ) - (m:ℝ)/(p2:ℝ)^2
 let e3:ℝ:=(a3:ℝ) - (m:ℝ)/(p3:ℝ)^2
 let e4:ℝ:=(a4:ℝ) - (m:ℝ)/(p4:ℝ)^2
 have he_bd:∀ (a p:ℕ),P < p->m+1<=a*p^2->a*p^2<=m+H->0<=(a:ℝ) - (m:ℝ)/(p:ℝ)^2/\(a:ℝ) - (m:ℝ)/(p:ℝ)^2<=(H:ℝ)/(P:ℝ)^2:=by
  intro a p hp hlo hhi
  have hpR:(0:ℝ) < (p:ℝ):=by exact_mod_cast (by omega:0 < p)
  have hloR:(m:ℝ)<=(a:ℝ)*(p:ℝ)^2:=by exact_mod_cast (by omega:m<=a*p^2)
  have hhiR:(a:ℝ)*(p:ℝ)^2<=(m:ℝ)+(H:ℝ):=by exact_mod_cast hhi
  constructor
  · rw [sub_nonneg,dli (by positivity)];exact hloR
  ·
   have h1:(a:ℝ) - (m:ℝ)/(p:ℝ)^2<=(H:ℝ)/(p:ℝ)^2:=by
    rw [sub_le_iff_le_add,← add_div,ldi (by positivity)];linarith only [hhiR]
   have h2:(H:ℝ)/(p:ℝ)^2<=(H:ℝ)/(P:ℝ)^2:=by gcongr
   linarith only [h1,h2]
 have he1:=he_bd a1 p1 hp1 ha1.1 ha1.2
 have he2:=he_bd a2 p2 (by omega) ha2.1 ha2.2
 have he3:=he_bd a3 p3 (by omega) ha3.1 ha3.2
 have he4:=he_bd a4 p4 (by omega) ha4.1 ha4.2
 have hc1R:(c1:ℝ)=((p3:ℝ) - p2)*((p4:ℝ) - p2)*((p4:ℝ) - p3):=by
  dsimp only [c1];push_cast
  rw [ncs (by omega),ncs (by omega),ncs (by omega)]
 have hc2R:(c2:ℝ)=((p3:ℝ) - p1)*((p4:ℝ) - p1)*((p4:ℝ) - p3):=by
  dsimp only [c2];push_cast
  rw [ncs (by omega),ncs (by omega),ncs (by omega)]
 have hc3R:(c3:ℝ)=((p2:ℝ) - p1)*((p4:ℝ) - p1)*((p4:ℝ) - p2):=by
  dsimp only [c3];push_cast
  rw [ncs (by omega),ncs (by omega),ncs (by omega)]
 have hc4R:(c4:ℝ)=((p2:ℝ) - p1)*((p3:ℝ) - p1)*((p3:ℝ) - p2):=by
  dsimp only [c4];push_cast
  rw [ncs (by omega),ncs (by omega),ncs (by omega)]
 have hc_bal:(c1:ℝ)+(c3:ℝ)=(c2:ℝ)+(c4:ℝ):=by
  rw [hc1R,hc2R,hc3R,hc4R];ring
 set Δ:ℝ:=((p2:ℝ) - p1)*((p3:ℝ) - p1)*((p4:ℝ) - p1)*((p3:ℝ) - p2)*((p4:ℝ) - p2)*((p4:ℝ) - p3)
 set M3:ℝ:=(m:ℝ)*(Δ*((p1:ℝ)*p2*p3+p1*p2*p4+p1*p3*p4+p2*p3*p4) /
  ((p1:ℝ)^2*(p2:ℝ)^2*(p3:ℝ)^2*(p4:ℝ)^2))
 set E3:ℝ:=(c1:ℝ)*e1 - (c2:ℝ)*e2+(c3:ℝ)*e3 - (c4:ℝ)*e4
 have hN3_eq:(N3:ℝ)=M3+E3:=by
  have hcast:(N3:ℝ)=(c1:ℝ)*a1 - (c2:ℝ)*a2+(c3:ℝ)*a3 - (c4:ℝ)*a4:=by
   dsimp only [N3];push_cast;ring
  have hid:=divdiff3_inv_sq hp1_pos.ne' hp2_pos.ne' hp3_pos.ne' hp4_pos.ne'
  dsimp only [M3,E3,e1,e2,e3,e4,Δ]
  rw [hcast,← hid,← hc1R,← hc2R,← hc3R,← hc4R];ring
 have hE3_lo:-(((c2:ℝ)+(c4:ℝ))*((H:ℝ)/(P:ℝ)^2))<=E3:=by
  dsimp only [E3]
  have h1:0<=(c1:ℝ)*e1:=mul_nonneg (by positivity) he1.1
  have h3:0<=(c3:ℝ)*e3:=mul_nonneg (by positivity) he3.1
  have h2:(c2:ℝ)*e2<=(c2:ℝ)*((H:ℝ)/(P:ℝ)^2):=ml he2.2 (by positivity)
  have h4:(c4:ℝ)*e4<=(c4:ℝ)*((H:ℝ)/(P:ℝ)^2):=ml he4.2 (by positivity)
  linarith only [h1,h2,h3,h4]
 have hE3_hi:E3<=((c2:ℝ)+(c4:ℝ))*((H:ℝ)/(P:ℝ)^2):=by
  dsimp only [E3]
  have h1:(c1:ℝ)*e1<=(c1:ℝ)*((H:ℝ)/(P:ℝ)^2):=ml he1.2 (by positivity)
  have h3:(c3:ℝ)*e3<=(c3:ℝ)*((H:ℝ)/(P:ℝ)^2):=ml he3.2 (by positivity)
  have h2:0<=(c2:ℝ)*e2:=mul_nonneg (by positivity) he2.1
  have h4:0<=(c4:ℝ)*e4:=mul_nonneg (by positivity) he4.1
  have hbal_mul:((c1:ℝ)+(c3:ℝ))*((H:ℝ)/(P:ℝ)^2)=((c2:ℝ)+(c4:ℝ))*((H:ℝ)/(P:ℝ)^2):=by rw [hc_bal]
  linarith only [h1,h2,h3,h4,hbal_mul]
 have hc24_pos:(0:ℝ) < (c2:ℝ)+(c4:ℝ):=by
  have:0 < c2:=by dsimp only [c2];exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hR:(0:ℝ) < (c2:ℝ):=by exact_mod_cast this
  have:(0:ℝ)<=(c4:ℝ):=by positivity
  linarith only [hR,this]
 have hΔ_ge:((c2:ℝ)+(c4:ℝ))*(L0:ℝ)^3<=Δ:=by
  have hg1:(L0:ℝ)<=(p2:ℝ) - p1:=by
   have:(L0:ℝ)<=((p2 - p1:ℕ):ℝ):=by exact_mod_cast hgap1
   rw [ncs (by omega)] at this;exact this
  have hg2:(L0:ℝ)<=(p3:ℝ) - p2:=by
   have:(L0:ℝ)<=((p3 - p2:ℕ):ℝ):=by exact_mod_cast hgap2
   rw [ncs (by omega)] at this;exact this
  have hg3:(L0:ℝ)<=(p4:ℝ) - p3:=by
   have:(L0:ℝ)<=((p4 - p3:ℕ):ℝ):=by exact_mod_cast hgap3
   rw [ncs (by omega)] at this;exact this
  have hL0nn:(0:ℝ)<=(L0:ℝ):=by positivity
  have h42:2*(L0:ℝ)<=(p4:ℝ) - p2:=by linarith only [hg2,hg3]
  have h41:(L0:ℝ)<=(p4:ℝ) - p1:=by linarith only [hg1,hg2,hg3]
  have hA:2*(L0:ℝ)^3<=((p2:ℝ) - p1)*((p3:ℝ) - p2)*((p4:ℝ) - p2):=by
   have h12:=mlm hg1 hg2 hL0nn (by linarith only [hg1,hL0nn])
   have h12_nn:(0:ℝ)<=((p2:ℝ) - p1)*((p3:ℝ) - p2):=mul_nonneg (by linarith only [hg1,hL0nn]) (by linarith only [hg2,hL0nn])
   have h123:=mlm h12 h42 (by positivity) h12_nn
   linarith only [h123]
  have hB:2*(L0:ℝ)^3<=((p4:ℝ) - p1)*((p4:ℝ) - p2)*((p4:ℝ) - p3):=by
   have h12:=mlm h41 h42 (by positivity) (by linarith only [h41,hL0nn])
   have h12_nn:(0:ℝ)<=((p4:ℝ) - p1)*((p4:ℝ) - p2):=mul_nonneg (by linarith only [h41,hL0nn]) (by linarith only [h42,hL0nn])
   have h123:=mlm h12 hg3 hL0nn h12_nn
   linarith only [h123]
  have hA2:(c2:ℝ)*(2*(L0:ℝ)^3)<=Δ:=by
   have:=ml hA (by positivity:(0:ℝ)<=(c2:ℝ))
   have hr:(c2:ℝ)*(((p2:ℝ) - p1)*((p3:ℝ) - p2)*((p4:ℝ) - p2))=Δ:=by
    rw [hc2R];dsimp only [Δ];ring
   linarith only [this,hr]
  have hB2:(c4:ℝ)*(2*(L0:ℝ)^3)<=Δ:=by
   have:=ml hB (by positivity:(0:ℝ)<=(c4:ℝ))
   have hr:(c4:ℝ)*(((p4:ℝ) - p1)*((p4:ℝ) - p2)*((p4:ℝ) - p3))=Δ:=by
    rw [hc4R];dsimp only [Δ];ring
   linarith only [this,hr]
  linarith only [hA2,hB2]
 have hM3_gt:((c2:ℝ)+(c4:ℝ))*((H:ℝ)/(P:ℝ)^2) < M3:=by
  have hL0_cub:256*(H:ℝ)*(P:ℝ)^3/(Y:ℝ) < (L0:ℝ)^3:=by
   have hlt:=lt_succ_natRoot_pow 3 (256*H*P^3/Y) (by omega)
   have hnat:256*H*P^3 < L0^3*Y:=by
    have h2:=lmd (256*H*P^3) (by omega:0 < Y)
    have h3:Y*(256*H*P^3/Y+1)<=Y*L0^3:=nml Y hlt
    linarith only [h2,h3]
   rw [div_lt_iff₀ hYpos]
   have hR:((256*H*P^3:ℕ):ℝ) < ((L0^3*Y:ℕ):ℝ):=by exact_mod_cast hnat
   push_cast at hR;linarith only [hR]
  have hm_ge:(Y:ℝ)/2<=(m:ℝ):=by
   have hR:(Y:ℝ)<=2*(m:ℝ):=by exact_mod_cast (by omega:Y<=2*m)
   linarith only [hR]
  have hp1P:(P:ℝ)<=(p1:ℝ):=by exact_mod_cast lol hp1
  have hp2P:(P:ℝ)<=(p2:ℝ):=by exact_mod_cast (by omega:P<=p2)
  have hp3P:(P:ℝ)<=(p3:ℝ):=by exact_mod_cast (by omega:P<=p3)
  have hp4P:(P:ℝ)<=(p4:ℝ):=by exact_mod_cast (by omega:P<=p4)
  have hp1_2P:(p1:ℝ)<=2*(P:ℝ):=by exact_mod_cast (by omega:p1<=2*P)
  have hp2_2P:(p2:ℝ)<=2*(P:ℝ):=by exact_mod_cast (by omega:p2<=2*P)
  have hp3_2P:(p3:ℝ)<=2*(P:ℝ):=by exact_mod_cast (by omega:p3<=2*P)
  have hp4_2P:(p4:ℝ)<=2*(P:ℝ):=by exact_mod_cast hp4
  have hsum_lo:4*(P:ℝ)^3<=(p1:ℝ)*p2*p3+p1*p2*p4+p1*p3*p4+p2*p3*p4:=by
   have ha:(P:ℝ)^3<=(p1:ℝ)*p2*p3:=by
    have:=mlm (mlm hp1P hp2P (lol hPpos) (lol hp1_pos)) hp3P (lol hPpos) (by positivity)
    linarith only [this]
   have hb:(P:ℝ)^3<=(p1:ℝ)*p2*p4:=by
    have:=mlm (mlm hp1P hp2P (lol hPpos) (lol hp1_pos)) hp4P (lol hPpos) (by positivity)
    linarith only [this]
   have hc:(P:ℝ)^3<=(p1:ℝ)*p3*p4:=by
    have:=mlm (mlm hp1P hp3P (lol hPpos) (lol hp1_pos)) hp4P (lol hPpos) (by positivity)
    linarith only [this]
   have hd:(P:ℝ)^3<=(p2:ℝ)*p3*p4:=by
    have:=mlm (mlm hp2P hp3P (lol hPpos) (lol hp2_pos)) hp4P (lol hPpos) (by positivity)
    linarith only [this]
   linarith only [ha,hb,hc,hd]
  have hden_hi:(p1:ℝ)^2*(p2:ℝ)^2*(p3:ℝ)^2*(p4:ℝ)^2<=256*(P:ℝ)^8:=by
   have h1:(p1:ℝ)^2<=4*(P:ℝ)^2:=by nlinarith only [hp1_2P,hp1_pos]
   have h2:(p2:ℝ)^2<=4*(P:ℝ)^2:=by nlinarith only [hp2_2P,hp2_pos]
   have h3:(p3:ℝ)^2<=4*(P:ℝ)^2:=by nlinarith only [hp3_2P,hp3_pos]
   have h4:(p4:ℝ)^2<=4*(P:ℝ)^2:=by nlinarith only [hp4_2P,hp4_pos]
   have h12:(p1:ℝ)^2*(p2:ℝ)^2<=16*(P:ℝ)^4:=by
    have:=mlm h1 h2 (by positivity) (by positivity);linarith only [this]
   have h34:(p3:ℝ)^2*(p4:ℝ)^2<=16*(P:ℝ)^4:=by
    have:=mlm h3 h4 (by positivity) (by positivity);linarith only [this]
   have:=mlm h12 h34 (by positivity) (by positivity);linarith only [this]
  have hnum_lo:(Y:ℝ)/2*(((c2:ℝ)+(c4:ℝ))*(L0:ℝ)^3*(4*(P:ℝ)^3))<=(m:ℝ)*(Δ*((p1:ℝ)*p2*p3+p1*p2*p4+p1*p3*p4+p2*p3*p4)):=by
   have h1:=mlm hΔ_ge hsum_lo (by positivity) (by
    have:0<=((c2:ℝ)+(c4:ℝ))*(L0:ℝ)^3:=by positivity
    linarith only [this,hΔ_ge])
   exact mlm hm_ge h1 (by positivity) (by positivity)
  have hM3_ge:(Y:ℝ)/2*(((c2:ℝ)+(c4:ℝ))*(L0:ℝ)^3*(4*(P:ℝ)^3))/(256*(P:ℝ)^8)<=M3:=by
   dsimp only [M3];rw [← mul_div_assoc]
   have hΔnn:(0:ℝ)<=Δ:=ltr (by positivity) hΔ_ge
   exact div_le_div₀ (by positivity) hnum_lo (by positivity) hden_hi
  have hstrict:((c2:ℝ)+(c4:ℝ))*((H:ℝ)/(P:ℝ)^2) < (Y:ℝ)/2*(((c2:ℝ)+(c4:ℝ))*(L0:ℝ)^3*(4*(P:ℝ)^3))/(256*(P:ℝ)^8):=by
   have h1:=mul_lt_mul_of_pos_left hL0_cub
    (by positivity:(0:ℝ) < (Y:ℝ)*((c2:ℝ)+(c4:ℝ))*(P:ℝ)^3/(128*(P:ℝ)^8))
   have hl:(Y:ℝ)*((c2:ℝ)+(c4:ℝ))*(P:ℝ)^3/(128*(P:ℝ)^8)*(256*(H:ℝ)*(P:ℝ)^3/(Y:ℝ))=2*(((c2:ℝ)+(c4:ℝ))*((H:ℝ)/(P:ℝ)^2)):=by field_simp;ring
   have hr:(Y:ℝ)*((c2:ℝ)+(c4:ℝ))*(P:ℝ)^3/(128*(P:ℝ)^8)*(L0:ℝ)^3=(Y:ℝ)/2*(((c2:ℝ)+(c4:ℝ))*(L0:ℝ)^3*(4*(P:ℝ)^3))/(256*(P:ℝ)^8):=by ring
   have hpos_t:(0:ℝ) < ((c2:ℝ)+(c4:ℝ))*((H:ℝ)/(P:ℝ)^2):=by positivity
   linarith only [h1,hl,hr,hpos_t]
  linarith only [hstrict,hM3_ge]
 have hL3_6:(L3:ℝ)^6<=(P:ℝ)^5/(64*(Y:ℝ)):=by
  have h1:=natRoot_pow_le 6 (P^5/(64*Y)) (by omega)
  have h2:L3^6*(64*Y)<=P^5:=ltr (nmr _ h1) (dls _ _)
  rw [ldi (by positivity)]
  have hR:((L3^6*(64*Y):ℕ):ℝ)<=((P^5:ℕ):ℝ):=by exact_mod_cast h2
  push_cast at hR;linarith only [hR]
 have hM3_le:M3<=1/2:=dd3_le Y P m L3 p1 p2 p3 p4 hY hP_pos hm_hi hp1 hord1 hord2 hord3 hp4 hspan hL3_6
 have hE3_lt:E3 < 1/2:=by
  have hc2_le:(c2:ℝ)<=(L3:ℝ)^3:=by
   have hnat:c2<=L3^3:=by
    dsimp only [c2]
    have h1:p3 - p1<=L3:=by omega
    have h2:p4 - p1<=L3:=hspan
    have h3:p4 - p3<=L3:=by omega
    have h12:=nmm h1 h2
    have h123:=nmm h12 h3
    have hpow:L3*L3*L3=L3^3:=by ring
    linarith only [h123,hpow]
   exact_mod_cast hnat
  have hc4_le:(c4:ℝ)<=(L3:ℝ)^3:=by
   have hnat:c4<=L3^3:=by
    dsimp only [c4]
    have h1:p2 - p1<=L3:=by omega
    have h2:p3 - p1<=L3:=by omega
    have h3:p3 - p2<=L3:=by omega
    have h12:=nmm h1 h2
    have h123:=nmm h12 h3
    have hpow:L3*L3*L3=L3^3:=by ring
    linarith only [h123,hpow]
   exact_mod_cast hnat
  have h1:E3<=2*(L3:ℝ)^3*((H:ℝ)/(P:ℝ)^2):=by
   have h2:(c2:ℝ)+(c4:ℝ)<=2*(L3:ℝ)^3:=by linarith only [hc2_le,hc4_le]
   exact ltr hE3_hi (mr h2 (by positivity))
  have hsq:(2*(L3:ℝ)^3*((H:ℝ)/(P:ℝ)^2))^2 < (1/2:ℝ)^2:=by
   have hPH2R:(P:ℝ)*(H:ℝ)^2 < 4*(Y:ℝ):=by
    have hR:((P*H^2:ℕ):ℝ) < ((4*Y:ℕ):ℝ):=by exact_mod_cast hPH2
    push_cast at hR;linarith only [hR]
   have hA:(2*(L3:ℝ)^3*((H:ℝ)/(P:ℝ)^2))^2=4*(L3:ℝ)^6*((H:ℝ)^2/(P:ℝ)^4):=by ring
   have hB:4*(L3:ℝ)^6*((H:ℝ)^2/(P:ℝ)^4)<=4*((P:ℝ)^5/(64*(Y:ℝ)))*((H:ℝ)^2/(P:ℝ)^4):=mr (ml hL3_6 (by positivity)) (by positivity)
   have hC:4*((P:ℝ)^5/(64*(Y:ℝ)))*((H:ℝ)^2/(P:ℝ)^4)=((P:ℝ)*(H:ℝ)^2)/(16*(Y:ℝ)):=by field_simp;ring
   have hD:((P:ℝ)*(H:ℝ)^2)/(16*(Y:ℝ)) < (4*(Y:ℝ))/(16*(Y:ℝ)):=by gcongr
   have hE:(4*(Y:ℝ))/(16*(Y:ℝ))=(1/2:ℝ)^2:=by field_simp;ring
   linarith only [hA,hB,hC,hD,hE]
  have hlt:2*(L3:ℝ)^3*((H:ℝ)/(P:ℝ)^2) < 1/2:=by
   by_contra hge;push Not at hge
   have:(1/2:ℝ)^2<=(2*(L3:ℝ)^3*((H:ℝ)/(P:ℝ)^2))^2:=by gcongr
   linarith only [hsq,this]
  linarith only [h1,hlt]
 have hN3_pos:(0:ℝ) < (N3:ℝ):=by linarith only [hN3_eq,hM3_gt,hE3_lo]
 have hN3_lt1:(N3:ℝ) < 1:=by linarith only [hN3_eq,hM3_le,hE3_lt]
 have hZpos:(0:ℤ) < N3:=by exact_mod_cast hN3_pos
 have hZlt1:N3 < (1:ℤ):=by exact_mod_cast hN3_lt1
 omega
lemma r3_3A (Y H P m L:ℕ) (hY:2^100000<=Y) (hH_lb:Y^10 < H^41)
  (hH_ub:H^3 < 10^9*Y) (hL_ge:100000<=L) (hL5000:L^5000<=Y)
  (hL1000_H:L^1000<=H) (hH_ge_20:2^20<=H) (hHP:H<=P)
  (hm_loc:m∈Ioc (Y/2) Y) (hsplit:P^40<=Y^11)
  (S:Finset ℕ) (hS_sub:S⊆Ioc P (2*P))
  (hex_a:∀ p∈S,∃ a:ℕ,m+1<=a*p^2/\a*p^2<=m+H) :
  (S.card:ℝ)*(8*(L:ℝ))<=(H:ℝ):=by
 have hY1:1<=Y:=ltr (o1p 100000 2 (by omega)) hY
 have hPpos:(0:ℝ) < (P:ℝ):=by exact_mod_cast (by omega:0 < P)
 have hYpos:(0:ℝ) < (Y:ℝ):=by exact_mod_cast (by omega:0 < Y)
 have hHpos:(0:ℝ) < (H:ℝ):=by exact_mod_cast (by omega:0 < H)
 have hLR:(100000:ℝ)<=(L:ℝ):=by exact_mod_cast hL_ge
 have h1_le_L:(1:ℝ)<=(L:ℝ):=by linarith only [hLR]
 have hL5000R:(L:ℝ)^5000<=(Y:ℝ):=by exact_mod_cast hL5000
 have hL1000HR:(L:ℝ)^1000<=(H:ℝ):=by exact_mod_cast hL1000_H
 have hY10H41:(Y:ℝ)^10<=(H:ℝ)^41:=by exact_mod_cast lol hH_lb
 have hPH2:P*H^2 < 4*Y:=by
  by_contra hge;push Not at hge
  have h1:(4*Y)^120<=(P*H^2)^120:=npl hge 120
  have h2:(P*H^2)^120=(P^40)^3*(H^3)^80:=by
   rw [mpow,← pmul,← pmul,← pmul]
  have h3:(P^40)^3<=(Y^11)^3:=npl hsplit 3
  have h4:(H^3)^80<=(10^9*Y)^80:=npl (lol hH_ub) 80
  have h5:(P^40)^3*(H^3)^80<=(Y^11)^3*(10^9*Y)^80:=nmm h3 h4
  have h6:(Y^11)^3*(10^9*Y)^80=10^720*Y^113:=by
   rw [mpow,← pmul,← pmul];ring
  have h7:10^720 < Y:=by
   have hA:(10^9:ℕ)^80 < (2^30:ℕ)^80:=Nat.pow_lt_pow_left (by norm_num) (by omega)
   calc 10^720=(10^9)^80:=by rw [← pmul]
    _ < (2^30)^80:=hA
    _=2^2400:=by rw [← pmul]
    _<=Y:=ltr (npr (by omega) (by omega)) hY
  have h8:10^720*Y^113 < Y^120:=by
   have hY114:10^720*Y^113 < Y*Y^113:=Nat.mul_lt_mul_of_pos_right h7 (by positivity)
   have hA:Y*Y^113=Y^114:=by ring
   have hB:Y^114<=Y^120:=npr hY1 (by omega)
   rw [hA] at hY114
   exact lt_of_lt_of_le hY114 hB
  have h9:Y^120<=(4*Y)^120:=npl (by omega) 120
  have hbad:Y^120 < Y^120:=calc
   Y^120<=(4*Y)^120:=h9
   _<=(P*H^2)^120:=h1
   _=(P^40)^3*(H^3)^80:=h2
   _<=(Y^11)^3*(10^9*Y)^80:=h5
   _=10^720*Y^113:=h6
   _ < Y^120:=h8
  exact lt_irrefl _ hbad
 set d3:=natRoot 3 (256*H*P^3/Y)
 set L0:=d3+1
 set L3:=natRoot 6 (P^5/(64*Y))
 have hScard:S.card<=(P/(L3+1)+1)*(3*L0):=by
  apply sh_sp P L3 3 L0 (by omega) S hS_sub
  intro a ⟨f,hf_mem,hf_gap⟩
  obtain ⟨a1,ha1⟩:=hex_a (f 0) (hf_mem 0).1
  obtain ⟨a2,ha2⟩:=hex_a (f 1) (hf_mem 1).1
  obtain ⟨a3,ha3⟩:=hex_a (f 2) (hf_mem 2).1
  obtain ⟨a4,ha4⟩:=hex_a (f 3) (hf_mem 3).1
  have hg0:f 0+L0<=f 1:=hf_gap 0
  have hg1:f 1+L0<=f 2:=hf_gap 1
  have hg2:f 2+L0<=f 3:=hf_gap 2
  have hI0:=mioc.mp (hS_sub (hf_mem 0).1)
  have hI3:=mioc.mp (hS_sub (hf_mem 3).1)
  have hhm:=mioc.mp hm_loc
  exact no_q3 Y H P m (by omega) (by omega) hPH2 (by omega) hhm.1 hhm.2
   (f 0) (f 1) (f 2) (f 3) a1 a2 a3 a4 hI0.1 hI3.2
   (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
   (by have:=(hf_mem 0).2.1;have:=(hf_mem 3).2.2;omega) ha1 ha2 ha3 ha4
 have hScardR:(S.card:ℝ)*(8*(L:ℝ))<=24*(L:ℝ)*(((P:ℝ)/((L3:ℝ)+1)+1)*((d3:ℝ)+1)):=by
  have h1:((S.card*(8*L):ℕ):ℝ)<=(((P/(L3+1)+1)*(3*L0)*(8*L):ℕ):ℝ):=by
   exact_mod_cast nmr (8*L) hScard
  have hdiv:((P/(L3+1):ℕ):ℝ)<=(P:ℝ)/((L3:ℝ)+1):=by
   rw [ldi (by positivity)]
   have hR:(((P/(L3+1))*(L3+1):ℕ):ℝ)<=(P:ℝ):=by
    exact_mod_cast dls P (L3+1)
   push_cast at hR;linarith only [hR]
  dsimp only [L0] at h1;push_cast at h1
  have h2:(((P/(L3+1):ℕ):ℝ)+1)*(3*((d3:ℝ)+1))*(8*(L:ℝ))<=((P:ℝ)/((L3:ℝ)+1)+1)*(3*((d3:ℝ)+1))*(8*(L:ℝ)):=mr (mr (by linarith only [hdiv]) (by positivity)) (by positivity)
  have h3:((P:ℝ)/((L3:ℝ)+1)+1)*(3*((d3:ℝ)+1))*(8*(L:ℝ))=24*(L:ℝ)*(((P:ℝ)/((L3:ℝ)+1)+1)*((d3:ℝ)+1)):=by ring
  linarith only [h1,h2,h3]
 have hd3_cub:(d3:ℝ)^3<=256*(H:ℝ)*(P:ℝ)^3/(Y:ℝ):=by
  have h1:=natRoot_pow_le 3 (256*H*P^3/Y) (by omega)
  have h2:d3^3*Y<=256*H*P^3:=ltr (nmr Y h1) (dls _ _)
  rw [ldi hYpos]
  have hR:((d3^3*Y:ℕ):ℝ)<=((256*H*P^3:ℕ):ℝ):=by exact_mod_cast h2
  push_cast at hR;linarith only [hR]
 have hL3_inv6:((P:ℝ)/((L3:ℝ)+1))^6<=64*(Y:ℝ)*(P:ℝ):=by
  have hlt:=lt_succ_natRoot_pow 6 (P^5/(64*Y)) (by omega)
  have hnat:P^5<=(L3+1)^6*(64*Y):=by
   have h2:=lmd (P^5) (by omega:0 < 64*Y)
   have h3:64*Y*(P^5/(64*Y)+1)<=64*Y*(L3+1)^6:=nml _ hlt
   linarith only [h2,h3]
  have hR:(P:ℝ)^5<=((L3:ℝ)+1)^6*(64*(Y:ℝ)):=by
   have h':((P^5:ℕ):ℝ)<=(((L3+1)^6*(64*Y):ℕ):ℝ):=by exact_mod_cast hnat
   push_cast at h';linarith only [h']
  rw [dpow,dli (by positivity)]
  have hmul:=ml hR (lol hPpos)
  linarith only [hmul]
 have hP40R:(P:ℝ)^40<=(Y:ℝ)^11:=by exact_mod_cast hsplit
 have hA1:96*(L:ℝ)*((P:ℝ)/((L3:ℝ)+1))*(d3:ℝ)<=(H:ℝ):=by
  have h6:(96*(L:ℝ)*((P:ℝ)/((L3:ℝ)+1))*(d3:ℝ))^6<=(H:ℝ)^6:=by
   have hl:(96*(L:ℝ)*((P:ℝ)/((L3:ℝ)+1))*(d3:ℝ))^6=(96:ℝ)^6*(L:ℝ)^6*((P:ℝ)/((L3:ℝ)+1))^6*((d3:ℝ)^3)^2:=by ring
   have hd2:((d3:ℝ)^3)^2<=(256*(H:ℝ)*(P:ℝ)^3/(Y:ℝ))^2:=by gcongr
   have h1:(96:ℝ)^6*(L:ℝ)^6*((P:ℝ)/((L3:ℝ)+1))^6*((d3:ℝ)^3)^2<=(96:ℝ)^6*(L:ℝ)^6*(64*(Y:ℝ)*(P:ℝ))*(256*(H:ℝ)*(P:ℝ)^3/(Y:ℝ))^2:=by
    gcongr
   have h2:(96:ℝ)^6*(L:ℝ)^6*(64*(Y:ℝ)*(P:ℝ))*(256*(H:ℝ)*(P:ℝ)^3/(Y:ℝ))^2=((96:ℝ)^6*64*256^2)*(L:ℝ)^6*(P:ℝ)^7*(H:ℝ)^2/(Y:ℝ):=by
    field_simp
   have hc:((96:ℝ)^6*64*256^2)<=(L:ℝ)^4:=by
    have hA:(100000:ℝ)^4<=(L:ℝ)^4:=by gcongr
    have hB:((96:ℝ)^6*64*256^2)<=(100000:ℝ)^4:=by norm_num
    linarith only [hA,hB]
   have hcore:(L:ℝ)^10*(P:ℝ)^7<=(H:ℝ)^4*(Y:ℝ):=by
    have hpow:((L:ℝ)^10*(P:ℝ)^7)^1640<=((H:ℝ)^4*(Y:ℝ))^1640:=by
     rw [mpow,mpow,← pmul,← pmul,← pmul]
     have hP7:(P:ℝ)^(7*1640)<=(Y:ℝ)^3157:=by
      have heq:7*1640=40*287:=by omega
      rw [heq,pmul]
      calc ((P:ℝ)^40)^287<=((Y:ℝ)^11)^287:=pl0 (by positivity) hP40R 287
       _=(Y:ℝ)^3157:=by rw [← pmul]
     have hL10:(L:ℝ)^(10*1640)<=(Y:ℝ)^83:=by
      calc (L:ℝ)^(10*1640)<=(L:ℝ)^(5000*83):=pr0 h1_le_L (by omega)
       _=((L:ℝ)^5000)^83:=by rw [pmul]
       _<=(Y:ℝ)^83:=pl0 (by positivity) hL5000R 83
     have hH4:(Y:ℝ)^1600<=(H:ℝ)^(4*1640):=by
      have heq:4*1640=41*160:=by omega
      rw [heq,pmul]
      calc (Y:ℝ)^1600=((Y:ℝ)^10)^160:=by rw [← pmul]
       _<=((H:ℝ)^41)^160:=pl0 (by positivity) hY10H41 160
     calc (L:ℝ)^(10*1640)*(P:ℝ)^(7*1640)<=(Y:ℝ)^83*(Y:ℝ)^3157:=mlm hL10 hP7 (by positivity) (by positivity)
      _=(Y:ℝ)^1600*(Y:ℝ)^1640:=by rw [← padd,← padd]
      _<=(H:ℝ)^(4*1640)*(Y:ℝ)^1640:=mr hH4 (by positivity)
    exact lp0 (by omega) (by positivity) hpow
   have h3:((96:ℝ)^6*64*256^2)*(L:ℝ)^6*(P:ℝ)^7*(H:ℝ)^2/(Y:ℝ)<=(H:ℝ)^6:=by
    rw [dli hYpos]
    have hA:((96:ℝ)^6*64*256^2)*(L:ℝ)^6*(P:ℝ)^7<=(L:ℝ)^10*(P:ℝ)^7:=by
     have:=mr hc (by positivity:0<=(L:ℝ)^6*(P:ℝ)^7)
     linarith only [this]
    have hB:=mr (ltr hA hcore) (by positivity:0<=(H:ℝ)^2)
    linarith only [hB]
   linarith only [hl,h1,h2,h3]
  exact lp0 (by omega) (lol hHpos) h6
 have hA2:96*(L:ℝ)*((P:ℝ)/((L3:ℝ)+1))<=(H:ℝ):=by
  have h6:(96*(L:ℝ)*((P:ℝ)/((L3:ℝ)+1)))^6<=(H:ℝ)^6:=by
   have hl:(96*(L:ℝ)*((P:ℝ)/((L3:ℝ)+1)))^6=(96:ℝ)^6*(L:ℝ)^6*((P:ℝ)/((L3:ℝ)+1))^6:=by ring
   have h1:(96:ℝ)^6*(L:ℝ)^6*((P:ℝ)/((L3:ℝ)+1))^6<=((96:ℝ)^6*64)*(L:ℝ)^6*(Y:ℝ)*(P:ℝ):=by
    have:=ml hL3_inv6 (by positivity:0<=(96:ℝ)^6*(L:ℝ)^6)
    linarith only [this]
   have hc:((96:ℝ)^6*64)<=(L:ℝ)^4:=by
    have hA:(100000:ℝ)^4<=(L:ℝ)^4:=by gcongr
    have hB:((96:ℝ)^6*64)<=(100000:ℝ)^4:=by norm_num
    linarith only [hA,hB]
   have h2:((96:ℝ)^6*64)*(L:ℝ)^6*(Y:ℝ)*(P:ℝ)<=(L:ℝ)^10*(Y:ℝ)*(P:ℝ):=by
    have:=mr hc (by positivity:0<=(L:ℝ)^6*(Y:ℝ)*(P:ℝ))
    linarith only [this]
   have h3:(L:ℝ)^10*(Y:ℝ)*(P:ℝ)<=(H:ℝ)^6:=by
    have hpow:((L:ℝ)^10*(Y:ℝ)*(P:ℝ))^1640<=((H:ℝ)^6)^1640:=by
     rw [mpow,mpow,← pmul,← pmul]
     have hP1:(P:ℝ)^1640<=(Y:ℝ)^451:=by
      have heq:1640=40*41:=by omega
      rw [heq,pmul]
      calc ((P:ℝ)^40)^41<=((Y:ℝ)^11)^41:=pl0 (by positivity) hP40R 41
       _=(Y:ℝ)^451:=by rw [← pmul]
     have hL10:(L:ℝ)^(10*1640)<=(Y:ℝ)^309:=by
      calc (L:ℝ)^(10*1640)<=(L:ℝ)^(5000*309):=pr0 h1_le_L (by omega)
       _=((L:ℝ)^5000)^309:=by rw [pmul]
       _<=(Y:ℝ)^309:=pl0 (by positivity) hL5000R 309
     have hH6:(Y:ℝ)^2400<=(H:ℝ)^(6*1640):=by
      have heq:6*1640=41*240:=by omega
      rw [heq,pmul]
      calc (Y:ℝ)^2400=((Y:ℝ)^10)^240:=by rw [← pmul]
       _<=((H:ℝ)^41)^240:=pl0 (by positivity) hY10H41 240
     calc (L:ℝ)^(10*1640)*(Y:ℝ)^1640*(P:ℝ)^1640
       <= (Y:ℝ)^309*(Y:ℝ)^1640*(Y:ℝ)^451:=mlm (mr hL10 (by positivity)) hP1 (by positivity) (by positivity)
      _=(Y:ℝ)^2400:=by rw [← padd,← padd]
      _<=(H:ℝ)^(6*1640):=hH6
    exact lp0 (by omega) (by positivity) hpow
   linarith only [hl,h1,h2,h3]
  exact lp0 (by omega) (lol hHpos) h6
 have hA3:96*(L:ℝ)*(d3:ℝ)<=(H:ℝ):=by
  have h3:(96*(L:ℝ)*(d3:ℝ))^3<=(H:ℝ)^3:=by
   have hl:(96*(L:ℝ)*(d3:ℝ))^3=(96:ℝ)^3*(L:ℝ)^3*(d3:ℝ)^3:=by ring
   have hP3Y:(P:ℝ)^3<=(Y:ℝ):=by
    have hpow:((P:ℝ)^3)^40<=(Y:ℝ)^40:=by
     rw [← pmul,mcom 3 40,pmul]
     have hY1R:(1:ℝ)<=(Y:ℝ):=by exact_mod_cast hY1
     calc ((P:ℝ)^40)^3<=((Y:ℝ)^11)^3:=pl0 (by positivity) hP40R 3
      _=(Y:ℝ)^33:=by rw [← pmul]
      _<=(Y:ℝ)^40:=pr0 hY1R (by omega)
    exact lp0 (by omega) (lol hYpos) hpow
   have h1:(d3:ℝ)^3<=256*(H:ℝ):=by
    have hA:256*(H:ℝ)*(P:ℝ)^3/(Y:ℝ)<=256*(H:ℝ)*(Y:ℝ)/(Y:ℝ):=by gcongr
    have hB:256*(H:ℝ)*(Y:ℝ)/(Y:ℝ)=256*(H:ℝ):=by field_simp
    linarith only [hd3_cub,hA,hB]
   have hc:(96:ℝ)^3*256<=(L:ℝ)^2:=by
    have hA:(100000:ℝ)^2<=(L:ℝ)^2:=by gcongr
    have hB:(96:ℝ)^3*256<=(100000:ℝ)^2:=by norm_num
    linarith only [hA,hB]
   have hL5:(L:ℝ)^5<=(H:ℝ)^2:=by
    have hA:(L:ℝ)^5<=(H:ℝ):=ltr (pr0 h1_le_L (by omega)) hL1000HR
    have hB:(H:ℝ)<=(H:ℝ)^2:=lsp (by exact_mod_cast (by omega:1<=H)) (by omega)
    linarith only [hA,hB]
   have h2:(96:ℝ)^3*(L:ℝ)^3*(d3:ℝ)^3<=((96:ℝ)^3*256)*(L:ℝ)^3*(H:ℝ):=by
    have:=ml h1 (by positivity:0<=(96:ℝ)^3*(L:ℝ)^3)
    linarith only [this]
   have h3':((96:ℝ)^3*256)*(L:ℝ)^3*(H:ℝ)<=(L:ℝ)^5*(H:ℝ):=by
    have:=mr hc (by positivity:0<=(L:ℝ)^3*(H:ℝ))
    linarith only [this]
   have h4':(L:ℝ)^5*(H:ℝ)<=(H:ℝ)^3:=by
    have:=mr hL5 (lol hHpos);linarith only [this]
   linarith only [hl,h2,h3',h4']
  exact lp0 (by omega) (lol hHpos) h3
 have hA4:96*(L:ℝ)<=(H:ℝ):=by
  have h1:96*(L:ℝ)<=(L:ℝ)^2:=by nlinarith only [hLR]
  exact ltr h1 (ltr (pr0 h1_le_L (by omega)) hL1000HR)
 have hexp:24*(L:ℝ)*(((P:ℝ)/((L3:ℝ)+1)+1)*((d3:ℝ)+1))=(96*(L:ℝ)*((P:ℝ)/((L3:ℝ)+1))*(d3:ℝ)+96*(L:ℝ)*((P:ℝ)/((L3:ℝ)+1))+96*(L:ℝ)*(d3:ℝ)+96*(L:ℝ))/4:=by ring
 linarith only [hScardR,hexp,hA1,hA2,hA3,hA4]
lemma r3_3B (Y H P m L:ℕ) (hY:2^100000<=Y) (hH_lb:Y^10 < H^41)
  (hH_ub:H^3 < 10^9*Y) (hL_ge:100000<=L) (hL5000:L^5000<=Y)
  (hL1000_H:L^1000<=H) (hH_ge_20:2^20<=H) (hHP:H<=P)
  (hP2_ubR:(P:ℝ)^2<=8*(10^10:ℝ)*(Y:ℝ)/(H:ℝ))
  (hm_loc:m∈Ioc (Y/2) Y) (hsplit:Y^11 < P^40)
  (S:Finset ℕ) (hS_sub:S⊆Ioc P (2*P))
  (hex_a:∀ p∈S,∃ a:ℕ,m+1<=a*p^2/\a*p^2<=m+H) :
  (S.card:ℝ)*(8*(L:ℝ))<=(H:ℝ):=by
 have hY1:1<=Y:=ltr (o1p 100000 2 (by omega)) hY
 have hPpos:(0:ℝ) < (P:ℝ):=by exact_mod_cast (by omega:0 < P)
 have hYpos:(0:ℝ) < (Y:ℝ):=by exact_mod_cast (by omega:0 < Y)
 have hHpos:(0:ℝ) < (H:ℝ):=by exact_mod_cast (by omega:0 < H)
 have hLR:(100000:ℝ)<=(L:ℝ):=by exact_mod_cast hL_ge
 have h1_le_L:(1:ℝ)<=(L:ℝ):=by linarith only [hLR]
 have hL5000R:(L:ℝ)^5000<=(Y:ℝ):=by exact_mod_cast hL5000
 have hL1000HR:(L:ℝ)^1000<=(H:ℝ):=by exact_mod_cast hL1000_H
 have hY10H41:(Y:ℝ)^10<=(H:ℝ)^41:=by exact_mod_cast lol hH_lb
 have hH3_3YP2:H^3 < 3*Y*P^2:=by
  have h1:10^9 < 3*P^2:=by
   have:2^20<=P:=ltr hH_ge_20 hHP
   nlinarith only [this]
  have h2:10^9*Y<=3*P^2*Y:=nmr Y (lol h1)
  linarith only [hH_ub,h2]
 set d2:=natRoot 2 (64*H*P^2/Y)
 set L0:=d2+1
 set L2:=natRoot 3 (P^4/(24*Y))
 have hScard:S.card<=(P/(L2+1)+1)*(2*L0):=by
  apply sh_sp P L2 2 L0 (by omega) S hS_sub
  intro a ⟨f,hf_mem,hf_gap⟩
  obtain ⟨a1,ha1⟩:=hex_a (f 0) (hf_mem 0).1
  obtain ⟨a2,ha2⟩:=hex_a (f 1) (hf_mem 1).1
  obtain ⟨a3,ha3⟩:=hex_a (f 2) (hf_mem 2).1
  have hg0:f 0+L0<=f 1:=hf_gap 0
  have hg1:f 1+L0<=f 2:=hf_gap 1
  have hI0:=mioc.mp (hS_sub (hf_mem 0).1)
  have hI2:=mioc.mp (hS_sub (hf_mem 2).1)
  have hhm:=mioc.mp hm_loc
  exact no_t2 Y H P m (by omega) (by omega) hH3_3YP2 (by omega) hhm.1 hhm.2
   (f 0) (f 1) (f 2) a1 a2 a3 hI0.1 hI2.2
   (by omega) (by omega) (by omega) (by omega)
   (by have:=(hf_mem 0).2.1;have:=(hf_mem 2).2.2;omega) ha1 ha2 ha3
 have hScardR:(S.card:ℝ)*(8*(L:ℝ))<=16*(L:ℝ)*(((P:ℝ)/((L2:ℝ)+1)+1)*((d2:ℝ)+1)):=by
  have h1:((S.card*(8*L):ℕ):ℝ)<=(((P/(L2+1)+1)*(2*L0)*(8*L):ℕ):ℝ):=by
   exact_mod_cast nmr (8*L) hScard
  have hdiv:((P/(L2+1):ℕ):ℝ)<=(P:ℝ)/((L2:ℝ)+1):=by
   rw [ldi (by positivity)]
   have hR:(((P/(L2+1))*(L2+1):ℕ):ℝ)<=(P:ℝ):=by
    exact_mod_cast dls P (L2+1)
   push_cast at hR;linarith only [hR]
  dsimp only [L0] at h1;push_cast at h1
  have h2:(((P/(L2+1):ℕ):ℝ)+1)*(2*((d2:ℝ)+1))*(8*(L:ℝ))<=((P:ℝ)/((L2:ℝ)+1)+1)*(2*((d2:ℝ)+1))*(8*(L:ℝ)):=mr (mr (by linarith only [hdiv]) (by positivity)) (by positivity)
  have h3:((P:ℝ)/((L2:ℝ)+1)+1)*(2*((d2:ℝ)+1))*(8*(L:ℝ))=16*(L:ℝ)*(((P:ℝ)/((L2:ℝ)+1)+1)*((d2:ℝ)+1)):=by ring
  linarith only [h1,h2,h3]
 have hd2_sq:(d2:ℝ)^2<=64*(H:ℝ)*(P:ℝ)^2/(Y:ℝ):=by
  have h1:=natRoot_pow_le 2 (64*H*P^2/Y) (by omega)
  have h2:d2^2*Y<=64*H*P^2:=ltr (nmr Y h1) (dls _ _)
  rw [ldi hYpos]
  have hR:((d2^2*Y:ℕ):ℝ)<=((64*H*P^2:ℕ):ℝ):=by exact_mod_cast h2
  push_cast at hR;linarith only [hR]
 have hL2_inv3:((P:ℝ)/((L2:ℝ)+1))^3<=24*(Y:ℝ)/(P:ℝ):=by
  have hlt:=lt_succ_natRoot_pow 3 (P^4/(24*Y)) (by omega)
  have hnat:P^4<=(L2+1)^3*(24*Y):=by
   have h2:=lmd (P^4) (by omega:0 < 24*Y)
   have h3:24*Y*(P^4/(24*Y)+1)<=24*Y*(L2+1)^3:=nml _ hlt
   linarith only [h2,h3]
  have hR:(P:ℝ)^4<=((L2:ℝ)+1)^3*(24*(Y:ℝ)):=by
   have h':((P^4:ℕ):ℝ)<=(((L2+1)^3*(24*Y):ℕ):ℝ):=by exact_mod_cast hnat
   push_cast at h';linarith only [h']
  rw [dpow,ddi (by positivity) hPpos]
  linarith only [hR]
 have hY11P40:(Y:ℝ)^11<=(P:ℝ)^40:=by exact_mod_cast lol hsplit
 have hB1:64*(L:ℝ)*((P:ℝ)/((L2:ℝ)+1))*(d2:ℝ)<=(H:ℝ):=by
  have h6:(64*(L:ℝ)*((P:ℝ)/((L2:ℝ)+1))*(d2:ℝ))^6<=(H:ℝ)^6:=by
   have hl:(64*(L:ℝ)*((P:ℝ)/((L2:ℝ)+1))*(d2:ℝ))^6=(64:ℝ)^6*(L:ℝ)^6*(((P:ℝ)/((L2:ℝ)+1))^3)^2*((d2:ℝ)^2)^3:=by ring
   have h1:(64:ℝ)^6*(L:ℝ)^6*(((P:ℝ)/((L2:ℝ)+1))^3)^2*((d2:ℝ)^2)^3<=(64:ℝ)^6*(L:ℝ)^6*(24*(Y:ℝ)/(P:ℝ))^2*(64*(H:ℝ)*(P:ℝ)^2/(Y:ℝ))^3:=by
    gcongr
   have h2:(64:ℝ)^6*(L:ℝ)^6*(24*(Y:ℝ)/(P:ℝ))^2*(64*(H:ℝ)*(P:ℝ)^2/(Y:ℝ))^3=((64:ℝ)^9*24^2)*(L:ℝ)^6*(H:ℝ)^3/(Y:ℝ)*((P:ℝ)^2)^2:=by
    field_simp
   have hP4:((P:ℝ)^2)^2<=(8*(10^10:ℝ)*(Y:ℝ)/(H:ℝ))^2:=by gcongr
   have h3:((64:ℝ)^9*24^2)*(L:ℝ)^6*(H:ℝ)^3/(Y:ℝ)*((P:ℝ)^2)^2<=((64:ℝ)^9*24^2*64*10^20)*(L:ℝ)^6*(H:ℝ)*(Y:ℝ):=by
    have:=ml hP4 (by positivity:0<=((64:ℝ)^9*24^2)*(L:ℝ)^6*(H:ℝ)^3/(Y:ℝ))
    have hr:((64:ℝ)^9*24^2)*(L:ℝ)^6*(H:ℝ)^3/(Y:ℝ)*(8*(10^10:ℝ)*(Y:ℝ)/(H:ℝ))^2=((64:ℝ)^9*24^2*64*10^20)*(L:ℝ)^6*(H:ℝ)*(Y:ℝ):=by field_simp;norm_num
    linarith only [this,hr]
   have hc:((64:ℝ)^9*24^2*64*10^20)<=(L:ℝ)^10:=by
    have hA:(100000:ℝ)^10<=(L:ℝ)^10:=by gcongr
    have hB:((64:ℝ)^9*24^2*64*10^20)<=(100000:ℝ)^10:=by norm_num
    linarith only [hA,hB]
   have h4:((64:ℝ)^9*24^2*64*10^20)*(L:ℝ)^6*(H:ℝ)*(Y:ℝ)<=(L:ℝ)^16*(Y:ℝ)*(H:ℝ):=by
    have:=mr hc (by positivity:0<=(L:ℝ)^6*(H:ℝ)*(Y:ℝ))
    linarith only [this]
   have h5:(L:ℝ)^16*(Y:ℝ)<=(H:ℝ)^5:=by
    have hpow:((L:ℝ)^16*(Y:ℝ))^41<=((H:ℝ)^5)^41:=by
     rw [mpow,← pmul,← pmul]
     have hL16:(L:ℝ)^(16*41)<=(Y:ℝ)^9:=by
      calc (L:ℝ)^(16*41)<=(L:ℝ)^(5000*9):=pr0 h1_le_L (by omega)
       _=((L:ℝ)^5000)^9:=by rw [pmul]
       _<=(Y:ℝ)^9:=pl0 (by positivity) hL5000R 9
     have hH5:(Y:ℝ)^50<=(H:ℝ)^(5*41):=by
      rw [mcom 5 41,pmul]
      calc (Y:ℝ)^50=((Y:ℝ)^10)^5:=by rw [← pmul]
       _<=((H:ℝ)^41)^5:=pl0 (by positivity) hY10H41 5
     calc (L:ℝ)^(16*41)*(Y:ℝ)^41<=(Y:ℝ)^9*(Y:ℝ)^41:=mr hL16 (by positivity)
      _=(Y:ℝ)^50:=by rw [← padd]
      _<=(H:ℝ)^(5*41):=hH5
    exact lp0 (by omega) (by positivity) hpow
   have h6':=mr h5 (lol hHpos)
   linarith only [hl,h1,h2,h3,h4,h6']
  exact lp0 (by omega) (lol hHpos) h6
 have hB2:64*(L:ℝ)*((P:ℝ)/((L2:ℝ)+1))<=(H:ℝ):=by
  have h3:(64*(L:ℝ)*((P:ℝ)/((L2:ℝ)+1)))^3<=(H:ℝ)^3:=by
   have hl:(64*(L:ℝ)*((P:ℝ)/((L2:ℝ)+1)))^3=(64:ℝ)^3*(L:ℝ)^3*((P:ℝ)/((L2:ℝ)+1))^3:=by ring
   have h1:(64:ℝ)^3*(L:ℝ)^3*((P:ℝ)/((L2:ℝ)+1))^3<=((64:ℝ)^3*24)*(L:ℝ)^3*(Y:ℝ)/(P:ℝ):=by
    have:=ml hL2_inv3 (by positivity:0<=(64:ℝ)^3*(L:ℝ)^3)
    have hr:(64:ℝ)^3*(L:ℝ)^3*(24*(Y:ℝ)/(P:ℝ))=((64:ℝ)^3*24)*(L:ℝ)^3*(Y:ℝ)/(P:ℝ):=by ring
    linarith only [this,hr]
   have hc:((64:ℝ)^3*24)<=(L:ℝ)^2:=by
    have hA:(100000:ℝ)^2<=(L:ℝ)^2:=by gcongr
    have hB:((64:ℝ)^3*24)<=(100000:ℝ)^2:=by norm_num
    linarith only [hA,hB]
   have h2:((64:ℝ)^3*24)*(L:ℝ)^3*(Y:ℝ)/(P:ℝ)<=(H:ℝ)^3:=by
    rw [dli hPpos]
    have hA:((64:ℝ)^3*24)*(L:ℝ)^3*(Y:ℝ)<=(L:ℝ)^5*(Y:ℝ):=by
     have:=mr hc (by positivity:0<=(L:ℝ)^3*(Y:ℝ))
     linarith only [this]
    have hB:(L:ℝ)^5*(Y:ℝ)<=(H:ℝ)^3*(P:ℝ):=by
     have hpow:((L:ℝ)^5*(Y:ℝ))^1640<=((H:ℝ)^3*(P:ℝ))^1640:=by
      rw [mpow,mpow,← pmul,← pmul]
      have hL5:(L:ℝ)^(5*1640)<=(Y:ℝ)^11:=by
       calc (L:ℝ)^(5*1640)<=(L:ℝ)^(5000*11):=pr0 h1_le_L (by omega)
        _=((L:ℝ)^5000)^11:=by rw [pmul]
        _<=(Y:ℝ)^11:=pl0 (by positivity) hL5000R 11
      have hH3':(Y:ℝ)^1200<=(H:ℝ)^(3*1640):=by
       have heq:3*1640=41*120:=by omega
       rw [heq,pmul]
       calc (Y:ℝ)^1200=((Y:ℝ)^10)^120:=by rw [← pmul]
        _<=((H:ℝ)^41)^120:=pl0 (by positivity) hY10H41 120
      have hP1':(Y:ℝ)^451<=(P:ℝ)^1640:=by
       have heq:1640=40*41:=by omega
       rw [heq,pmul]
       calc (Y:ℝ)^451=((Y:ℝ)^11)^41:=by rw [← pmul]
        _<=((P:ℝ)^40)^41:=pl0 (by positivity) hY11P40 41
      calc (L:ℝ)^(5*1640)*(Y:ℝ)^1640<=(Y:ℝ)^11*(Y:ℝ)^1640:=mr hL5 (by positivity)
       _=(Y:ℝ)^1200*(Y:ℝ)^451:=by rw [← padd,← padd]
       _<=(H:ℝ)^(3*1640)*(P:ℝ)^1640:=mlm hH3' hP1' (by positivity) (by positivity)
     exact lp0 (by omega) (by positivity) hpow
    linarith only [hA,hB]
   linarith only [hl,h1,h2]
  exact lp0 (by omega) (lol hHpos) h3
 have hB3:64*(L:ℝ)*(d2:ℝ)<=(H:ℝ):=by
  have h2:(64*(L:ℝ)*(d2:ℝ))^2<=(H:ℝ)^2:=by
   have hl:(64*(L:ℝ)*(d2:ℝ))^2=4096*(L:ℝ)^2*(d2:ℝ)^2:=by ring
   have hd2_const:(d2:ℝ)^2<=64*8*(10^10:ℝ):=by
    have hA:64*(H:ℝ)*(P:ℝ)^2/(Y:ℝ)<=64*(H:ℝ)*(8*(10^10:ℝ)*(Y:ℝ)/(H:ℝ))/(Y:ℝ):=by gcongr
    have hB:64*(H:ℝ)*(8*(10^10:ℝ)*(Y:ℝ)/(H:ℝ))/(Y:ℝ)=64*8*(10^10:ℝ):=by
     field_simp
    linarith only [hd2_sq,hA,hB]
   have hc:4096*(64*8*(10^10:ℝ))<=(L:ℝ)^4:=by
    have hA:(100000:ℝ)^4<=(L:ℝ)^4:=by gcongr
    have hB:4096*(64*8*(10^10:ℝ))<=(100000:ℝ)^4:=by norm_num
    linarith only [hA,hB]
   have hL6:(L:ℝ)^6<=(H:ℝ)^2:=by
    have hA:(L:ℝ)^6<=(H:ℝ):=ltr (pr0 h1_le_L (by omega)) hL1000HR
    have hB:(H:ℝ)<=(H:ℝ)^2:=lsp (by exact_mod_cast (by omega:1<=H)) (by omega)
    linarith only [hA,hB]
   have h1:4096*(L:ℝ)^2*(d2:ℝ)^2<=(4096*(64*8*(10^10:ℝ)))*(L:ℝ)^2:=by
    have:=ml hd2_const (by positivity:0<=4096*(L:ℝ)^2)
    linarith only [this]
   have h2':(4096*(64*8*(10^10:ℝ)))*(L:ℝ)^2<=(L:ℝ)^6:=by
    have:=mr hc (by positivity:0<=(L:ℝ)^2)
    linarith only [this]
   linarith only [hl,h1,h2',hL6]
  exact lp0 (by omega) (lol hHpos) h2
 have hB4:64*(L:ℝ)<=(H:ℝ):=by
  have h1:64*(L:ℝ)<=(L:ℝ)^2:=by nlinarith only [hLR]
  exact ltr h1 (ltr (pr0 h1_le_L (by omega)) hL1000HR)
 have hexp:16*(L:ℝ)*(((P:ℝ)/((L2:ℝ)+1)+1)*((d2:ℝ)+1))=(64*(L:ℝ)*((P:ℝ)/((L2:ℝ)+1))*(d2:ℝ)+64*(L:ℝ)*((P:ℝ)/((L2:ℝ)+1))+64*(L:ℝ)*(d2:ℝ)+64*(L:ℝ))/4:=by ring
 linarith only [hScardR,hexp,hB1,hB2,hB3,hB4]
lemma r3_van (Y H:ℕ) (hY:2^100000<=Y) (hH_lb:Y^10 < H^41)
  (hH_ub:H^3 < 10^9*Y):Mstar Y H=0:=by
 have hY600:2^600<=Y:=ltr (npr (by omega) (by omega)) hY
 have hY1:1<=Y:=ltr (o1p 600 2 (by omega)) hY600
 have hL5000:(Nat.log 2 (40*Y^2)+2)^5000<=Y:=lp5k Y hY
 set L:=Nat.log 2 (40*Y^2)+2 with hL_def
 have hlogY_ge:100000<=Nat.log 2 Y:=llp (by omega) hY
 have hL_ge:100000<=L:=by
  have h1:Y<=40*Y^2:=by
   calc Y=1*Y:=(omul Y).symm
    _<=40*(Y*Y):=nmm (by omega) (Nat.le_mul_of_pos_left Y hY1)
    _=40*Y^2:=by ring
  have h2:Nat.log 2 Y<=Nat.log 2 (40*Y^2):=lmr h1
  omega
 have hL1000_H:L^1000<=H:=by
  by_contra hlt;push Not at hlt
  have h1:H^41 < (L^1000)^41:=Nat.pow_lt_pow_left hlt (by omega)
  have h2:(L^1000)^41=L^41000:=by rw [← pmul]
  have h3:L^41000<=L^50000:=npr (by omega) (by omega)
  have h4:L^50000=(L^5000)^10:=by rw [← pmul]
  have h5:(L^5000)^10<=Y^10:=npl hL5000 10
  exact lt_irrefl _ (lt_of_lt_of_le (lt_trans hH_lb h1) (ltr (le_of_eq h2) (ltr h3 (ltr (le_of_eq h4) h5))))
 have hH_ge_20:2^20<=H:=by
  have h1:2^20<=L^2:=by nlinarith only [hL_ge]
  exact ltr h1 (ltr (npr (by omega) (by omega)) hL1000_H)
 have hlogH_ge:1000<=Nat.log 2 H:=by
  have h1:2^1000<=H:=by
   have hL2:2<=L:=by omega
   exact ltr (npl hL2 1000) hL1000_H
  exact llp (by omega) h1
 set Z1:=H*Nat.log 2 H/1000
 set Z2:=10^5*(Nat.sqrt (Y/H)+1)
 have hH_le_Z1:H<=Z1:=(ldim (by omega:0 < 1000)).mpr (nml H hlogH_ge)
 have hZ2_sq:Z2^2<=4*10^10*(Y/H+1):=by
  have hsq:Nat.sqrt (Y/H)^2<=Y/H:=Nat.sqrt_le' (Y/H)
  have h1:(Nat.sqrt (Y/H)+1)^2<=4*(Y/H+1):=by
   have:=Nat.sqrt_le_self (Y/H);nlinarith only [hsq,this]
  have h2:Z2^2=10^10*(Nat.sqrt (Y/H)+1)^2:=by dsimp [Z2];ring
  nlinarith only [h1,h2]
 have hZ2_le_Y:Z2<=Y:=by
  have hdiv:Y/H+1<=Y:=by
   have:Y/H<=Y/2:=ddll (by omega:2<=H) (by omega)
   have hY4:4<=Y:=ltr (by norm_num:4<=2^2) (ltr (npr (by omega) (by omega)) hY600)
   omega
  have h4e10:4*10^10 < Y:=lt_of_lt_of_le (by norm_num:4*10^10 < 2^40)
   (ltr (npr (by omega) (by omega)) hY600)
  by_contra hgt;push Not at hgt
  have:Y^2 < Z2^2:=Nat.pow_lt_pow_left hgt (by omega)
  have:4*10^10*(Y/H+1)<=4*10^10*Y:=nml _ hdiv
  nlinarith only [hZ2_sq,‹Y^2 < Z2^2›,‹4*10^10*(Y/H+1)<=4*10^10*Y›,h4e10]
 by_contra hne0
 have hne:((Ioc (Y/2) Y).filter (noSqf H)).Nonempty:=card_pos.mp (pnz hne0)
 obtain ⟨m,hm⟩:=hne
 have hm_loc:=(mf.mp hm).1
 have hm_no:=(mf.mp hm).2
 have hdet:=det_pw Y H m hH_ge_20 hH_ub hm_loc hm_no
 set P_of:ℕ->ℕ:=fun i => Z1*2^i
 set I:=(range L).filter (fun i => P_of i<=Z2)
 set S_all:=(Ioc Z1 Z2).filter (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)
 have hS_sub:S_all⊆I.biUnion (fun i => (Ioc (P_of i) (2*P_of i)).filter
   (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)):=by
  intro p hp;rw [mbu]
  have hpIoc:=mioc.mp (mf.mp hp).1
  let i:=Nat.log 2 ((p - 1)/Z1)
  have hq_pos:1<=(p - 1)/Z1:=(ldim (by omega)).mpr (by omega)
  have hi_lo:2^i<=(p - 1)/Z1:=pls 2 (by omega)
  have hi_hi:(p - 1)/Z1 < 2^(i+1):=lsl (by omega) _
  have hP_lt:P_of i < p:=by
   have:=ltr (nml Z1 hi_lo) (Nat.mul_div_le (p - 1) Z1)
   dsimp [P_of];omega
  have hp_le2P:p<=2*P_of i:=by
   have h1:p - 1 < Z1*2^(i+1):=by
    by_contra hge;push Not at hge
    have:=(ldim (by omega:0 < Z1)).mpr (by linarith only [hge]:2^(i+1)*Z1<=p - 1)
    omega
   have h2:Z1*2^(i+1)=2*P_of i:=by dsimp [P_of];ring
   omega
  have hi_mem:i∈I:=by
   rw [mf,mrng];refine ⟨?_,by omega⟩
   have h2i:2^i<=40*Y^2:=by
    have h1:2^i<=P_of i:=Nat.le_mul_of_pos_left _ (by omega)
    calc 2^i<=Y:=ltr h1 (by omega)
     _=1*Y:=(omul Y).symm
     _<=40*(Y*Y):=nmm (by omega) (Nat.le_mul_of_pos_left Y hY1)
     _=40*Y^2:=by ring
   have:i<=Nat.log 2 (40*Y^2):=llp (by omega) h2i;omega
  exact ⟨i,hi_mem,mf.mpr ⟨mioc.mpr ⟨hP_lt,hp_le2P⟩,(mf.mp hp).2⟩⟩
 have hshell_le:∀ i∈I,((Ioc (P_of i) (2*P_of i)).filter
   (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card<=H/(8*L):=by
  intro i hi
  set P:=P_of i
  set S:=(Ioc P (2*P)).filter (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)
  have hP_ub:P<=Z2:=(mf.mp hi).2
  have hHP:H<=P:=ltr hH_le_Z1 (Nat.le_mul_of_pos_right Z1 (by positivity))
  have hHpos:(0:ℝ) < (H:ℝ):=by exact_mod_cast (by omega:0 < H)
  have hP2_ubR:(P:ℝ)^2<=8*(10^10:ℝ)*(Y:ℝ)/(H:ℝ):=by
   have h1:P^2<=4*10^10*(Y/H+1):=ltr (npl hP_ub 2) hZ2_sq
   have h2:(P:ℝ)^2<=4*(10^10:ℝ)*(((Y/H:ℕ):ℝ)+1):=by
    have hR:((P^2:ℕ):ℝ)<=((4*10^10*(Y/H+1):ℕ):ℝ):=by exact_mod_cast h1
    push_cast at hR;linarith only [hR]
   have hdiv:((Y/H:ℕ):ℝ)<=(Y:ℝ)/(H:ℝ):=by
    rw [ldi hHpos];exact_mod_cast dls Y H
   have hHleY:H<=Y:=by
    by_contra hgt;push Not at hgt
    have hY3:Y^3 < H^3:=Nat.pow_lt_pow_left hgt (by omega)
    have h109:10^9 < Y:=lt_of_lt_of_le (by norm_num:10^9 < 2^40)
     (ltr (npr (by omega) (by omega)) hY600)
    have hY2:10^9*Y < Y^2:=by nlinarith only [h109,hY1]
    have hY23:Y^2<=Y^3:=npr hY1 (by omega)
    omega
   have h1_le:(1:ℝ)<=(Y:ℝ)/(H:ℝ):=by
    rw [ldi hHpos,omul];exact_mod_cast hHleY
   have hring:4*(10^10:ℝ)*((Y:ℝ)/(H:ℝ)+(Y:ℝ)/(H:ℝ))=8*(10^10:ℝ)*(Y:ℝ)/(H:ℝ):=by ring
   linarith only [h2,hdiv,h1_le,hring]
  have hex_a:∀ p∈S,∃ a:ℕ,m+1<=a*p^2/\a*p^2<=m+H:=by
   intro p hp
   obtain ⟨j,hj,hdvd⟩:=(mf.mp hp).2.2
   obtain ⟨a,ha⟩:=hdvd
   have hjIcc:=micc.mp hj
   exact ⟨a,by rw [mcom,← ha];omega,by rw [mcom,← ha];omega⟩
  suffices hsuff:(S.card:ℝ)*(8*(L:ℝ))<=(H:ℝ) by
   refine (ldim (by omega:0 < 8*L)).mpr ?_
   have hR:((S.card*(8*L):ℕ):ℝ)<=(H:ℝ):=by push_cast;linarith only [hsuff]
   exact_mod_cast hR
  by_cases hsplit:P^40<=Y^11
  ·
   exact r3_3A Y H P m L hY hH_lb hH_ub hL_ge hL5000 hL1000_H hH_ge_20 hHP
    hm_loc hsplit S (fsub _ _) hex_a
  ·
   push Not at hsplit
   exact r3_3B Y H P m L hY hH_lb hH_ub hL_ge hL5000 hL1000_H hH_ge_20 hHP
    hP2_ubR hm_loc hsplit S (fsub _ _) hex_a
 have hcard_le:S_all.card<=I.card*(H/(8*L)):=by
  calc S_all.card<=(I.biUnion _).card:=clc hS_sub
   _<=∑ i∈I,((Ioc (P_of i) (2*P_of i)).filter
     (fun p => p.Prime/\∃ j∈Icc 1 H,p^2∣m+j)).card:=cbi
   _<=∑ _i∈I,(H/(8*L)):=sls hshell_le
   _=I.card*(H/(8*L)):=by simp
 have hI_le:I.card<=L:=ltr (cfl _ _) (by simp)
 have hLR:L*(H/(8*L))<=H/8:=by
  have:8*(L*(H/(8*L)))<=H:=by
   have:=Nat.mul_div_le H (8*L);linarith only [this]
  omega
 have hbad:H/4<=H/8:=ltr hdet (ltr hcard_le (ltr (nmr _ hI_le) hLR))
 omega
lemma dy_Ms :
  ∃ Y0:ℕ,2^100000<=Y0/\∀ (Y:ℕ),Y0<=Y->∀ (K:ℕ),10000<=K->∑ j∈(range (Nat.log 2 Y+2)).filter (fun j => K<=2^j),((2^j:ℕ):ℝ)^2*(Mstar Y (2^j):ℝ)<=((2^34:ℝ)/(K:ℝ)+(2^71:ℝ)/(Nat.log 2 Y:ℝ))*(Y:ℝ):=by
 obtain ⟨Y2,hY2⟩:=r2_bd
 refine ⟨max Y2 (2^100000),lmrt _ _,fun Y hY K hK => ?_⟩
 have hY2':Y2<=Y:=ltr (lml _ _) hY
 have hY100k:2^100000<=Y:=ltr (lmrt _ _) hY
 have hY600:2^600<=Y:=ltr (npr (by omega) (by omega)) hY100k
 have hlogY:100000<=Nat.log 2 Y:=llp (by omega) hY100k
 set J:=(range (Nat.log 2 Y+2)).filter (fun j => K<=2^j)
 have hterm:∀ j∈J,((2^j:ℕ):ℝ)^2*(Mstar Y (2^j):ℝ)<=(2^32:ℝ)*(Y:ℝ)*(1/(2:ℝ)^j)+(2^70:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by
  intro j hj
  have hHj:K<=2^j:=(mf.mp hj).2
  have hH10k:10000<=2^j:=ltr hK hHj
  have h1nn:(0:ℝ)<=(2^32:ℝ)*(Y:ℝ)*(1/(2:ℝ)^j):=by positivity
  have h2nn:(0:ℝ)<=(2^70:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2):=by positivity
  by_cases h1:(2^j)^22<=Y
  ·
   have hb:=r1_bd Y (2^j) hH10k h1
   have heq:(2^32:ℝ)*(Y:ℝ)/((2^j:ℕ):ℝ)=(2^32:ℝ)*(Y:ℝ)*(1/(2:ℝ)^j):=by
    push_cast;ring
   linarith only [hb,heq,h2nn]
  ·
   push Not at h1
   by_cases h2:(2^j)^41<=Y^10
   ·
    have hb:=hY2 Y hY2' (2^j) h1 h2
    linarith only [hb,h1nn]
   ·
    push Not at h2
    by_cases h3:(2^j)^3 < 10^9*Y
    ·
     have h0:=r3_van Y (2^j) hY100k h2 h3
     rw [h0];simp only [Nat.cast_zero,mul_zero];linarith only [h1nn,h2nn]
    ·
     push Not at h3
     have h0:=r4_van Y (2^j) hY600 h3
     rw [h0];simp only [Nat.cast_zero,mul_zero];linarith only [h1nn,h2nn]
 have hsum:=sls hterm
 rw [sum_add_distrib,← mul_sum] at hsum
 have hgeom:∑ j∈J,(1/(2:ℝ)^j)<=4/(K:ℝ):=by
  let j0:=Nat.log 2 K
  have hj0_le:∀ j∈J,j0<=j:=by
   intro j hj
   have hle:2^j0<=2^j:=ltr (pls 2 (by omega)) (mf.mp hj).2
   exact (Nat.pow_le_pow_iff_right (by omega:1 < 2)).mp hle
  have hK_lt:(K:ℝ)<=2*(2:ℝ)^j0:=by
   have hlt:K < 2^(j0+1):=lsl (by omega) K
   have hR:(K:ℝ)<=((2^(j0+1):ℕ):ℝ):=by exact_mod_cast lol hlt
   push_cast at hR;rw [pow_succ] at hR;linarith only [hR]
  have hKpos:(0:ℝ) < (K:ℝ):=by exact_mod_cast (by omega:0 < K)
  have hinv_j0:1/(2:ℝ)^j0<=2/(K:ℝ):=by
   rw [ddi (by positivity) hKpos];linarith only [hK_lt]
  have hshift:∑ j∈J,(1/(2:ℝ)^j)<=(2/(K:ℝ))*∑ j∈J,(1/2:ℝ)^(j - j0):=by
   rw [mul_sum]
   apply sls
   intro j hj
   have hge:=hj0_le j hj
   have hpow:(2:ℝ)^j=(2:ℝ)^j0*(2:ℝ)^(j - j0):=by
    rw [← padd,Nat.add_sub_of_le hge]
   have h1:1/(2:ℝ)^j=(1/(2:ℝ)^j0)*(1/2:ℝ)^(j - j0):=by
    rw [hpow,dpow,one_pow];field_simp
   rw [h1]
   exact mr hinv_j0 (by positivity)
  have hsub_sum:∑ j∈J,(1/2:ℝ)^(j - j0)<=∑ t∈range (Nat.log 2 Y+2),(1/2:ℝ)^t:=by
   have hinj:Set.InjOn (fun j => j - j0) (J:Set ℕ):=by
    intro a ha b hb hab
    have ha':=hj0_le a (mem_coe.mp ha)
    have hb':=hj0_le b (mem_coe.mp hb)
    dsimp only at hab;omega
   have himg:J.image (fun j => j - j0)⊆range (Nat.log 2 Y+2):=by
    intro t ht
    obtain ⟨j,hj,rfl⟩:=mim.mp ht
    have:=mrng.mp (mf.mp hj).1
    exact mrng.mpr (by omega)
   calc ∑ j∈J,(1/2:ℝ)^(j - j0)
     = ∑ t∈J.image (fun j => j - j0),(1/2:ℝ)^t:=(sum_image hinj).symm
    _<=∑ t∈range (Nat.log 2 Y+2),(1/2:ℝ)^t:=ssub himg (fun _ _ _ => by positivity)
  have hhalf:∀ n:ℕ,∑ t∈range n,(1/2:ℝ)^t<=2 - 2*(1/2:ℝ)^n:=by
   intro n;induction n with
   | zero => norm_num
   | succ k ih => rw [sum_range_succ,pow_succ];linarith only [ih]
  have h2:∑ j∈J,(1/2:ℝ)^(j - j0)<=2:=by
   have hnn:(0:ℝ)<=2*(1/2:ℝ)^(Nat.log 2 Y+2):=by positivity
   linarith only [hsub_sum,hhalf (Nat.log 2 Y+2),hnn]
  have hmul:=ml h2 (by positivity:(0:ℝ)<=2/(K:ℝ))
  have hr:2/(K:ℝ)*2=4/(K:ℝ):=by ring
  linarith only [hshift,hmul,hr]
 have hpart1:(2^32:ℝ)*(Y:ℝ)*∑ j∈J,(1/(2:ℝ)^j)<=(2^34:ℝ)/(K:ℝ)*(Y:ℝ):=by
  have:=ml hgeom (by positivity:(0:ℝ)<=(2^32:ℝ)*(Y:ℝ))
  have hr:(2^32:ℝ)*(Y:ℝ)*(4/(K:ℝ))=(2^34:ℝ)/(K:ℝ)*(Y:ℝ):=by ring
  linarith only [this,hr]
 have hpart2:∑ _j∈J,(2^70:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2)<=(2^71:ℝ)/(Nat.log 2 Y:ℝ)*(Y:ℝ):=by
  simp only [sum_const,nsmul_eq_mul]
  have hcard:(J.card:ℝ)<=2*(Nat.log 2 Y:ℝ):=by
   have h1:J.card<=Nat.log 2 Y+2:=ltr (cfl _ _) (by simp)
   have h2:Nat.log 2 Y+2<=2*Nat.log 2 Y:=by omega
   exact_mod_cast ltr h1 h2
  have hlogY_pos:(0:ℝ) < (Nat.log 2 Y:ℝ):=by exact_mod_cast (by omega:0 < Nat.log 2 Y)
  have h1:=mr hcard (by positivity:0<=(2^70:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2))
  have heq:2*(Nat.log 2 Y:ℝ)*((2^70:ℝ)*(Y:ℝ)/((Nat.log 2 Y:ℝ)^2))=(2^71:ℝ)/(Nat.log 2 Y:ℝ)*(Y:ℝ):=by field_simp
  linarith only [h1,heq]
 have hr:((2^34:ℝ)/(K:ℝ)+(2^71:ℝ)/(Nat.log 2 Y:ℝ))*(Y:ℝ)=(2^34:ℝ)/(K:ℝ)*(Y:ℝ)+(2^71:ℝ)/(Nat.log 2 Y:ℝ)*(Y:ℝ):=by ring
 linarith only [hsum,hpart1,hpart2,hr]
lemma noSqf_f (m H:ℕ) (hm:2^600<=m) (hH:10^9*m<=H^3) :
  ¬ noSqf H m:=by
 intro hno
 have h0:=r4_van m H hm hH
 have hmem:m∈(Ioc (m/2) m).filter (noSqf H):=by
  have hm1:1<=m:=ltr (o1p 600 2 (by omega)) hm
  exact mf.mpr ⟨mioc.mpr ⟨by omega,le_refl m⟩,hno⟩
 have hpos:0 < Mstar m H:=card_pos.mpr ⟨m,hmem⟩
 omega
lemma dy_Ioc (Y0:ℕ) (hY0_ge:2^100000<=Y0)
  (hM:∀ (Y:ℕ),Y0<=Y->∀ (K:ℕ),10000<=K->∑ j∈(range (Nat.log 2 Y+2)).filter (fun j => K<=2^j),((2^j:ℕ):ℝ)^2*(Mstar Y (2^j):ℝ)<=((2^34:ℝ)/(K:ℝ)+(2^71:ℝ)/(Nat.log 2 Y:ℝ))*(Y:ℝ))
  (Ycut K:ℕ) (hYcut:Y0<=Ycut) (hK:10000<=K) :
  ∀ X:ℕ,∑ j∈(range (Nat.log 2 X+2)).filter (fun j => K<=2^j),((2^j:ℕ):ℝ)^2*(((Ioc Ycut X).filter (noSqf (2^j))).card:ℝ)<=2*((2^34:ℝ)/(K:ℝ)+(2^71:ℝ)/(Nat.log 2 Ycut:ℝ))*(X:ℝ):=by
 intro X
 induction X using Nat.strong_induction_on with
 | h X ih =>
  set C:ℝ:=(2^34:ℝ)/(K:ℝ)+(2^71:ℝ)/(Nat.log 2 Ycut:ℝ)
  have hCnn:0<=C:=by positivity
  by_cases hle:X<=Ycut
  ·
   have hempty:Ioc Ycut X=∅:=Ioc_eq_empty (by omega)
   simp only [hempty,filter_empty,card_empty,Nat.cast_zero,mul_zero,sum_const_zero]
   positivity
  ·
   push Not at hle
   have hX_pos:0 < X:=by omega
   have hX_ge_Y0:Y0<=X:=ltr hYcut (lol hle)
   set JX:=(range (Nat.log 2 X+2)).filter (fun j => K<=2^j)
   set JX2:=(range (Nat.log 2 (X/2)+2)).filter (fun j => K<=2^j)
   have hsplit_card:∀ j:ℕ,(((Ioc Ycut X).filter (noSqf (2^j))).card:ℝ)<=(((Ioc Ycut (X/2)).filter (noSqf (2^j))).card:ℝ)+(Mstar X (2^j):ℝ):=by
    intro j
    have hsub:(Ioc Ycut X).filter (noSqf (2^j)) ⊆
      (Ioc Ycut (X/2)).filter (noSqf (2^j)) ∪
      (Ioc (X/2) X).filter (noSqf (2^j)):=by
     intro m hm
     rw [mun,mf,mf]
     have hI:=mioc.mp (mf.mp hm).1
     have hno:=(mf.mp hm).2
     by_cases h:m<=X/2
     · exact Or.inl ⟨mioc.mpr ⟨hI.1,h⟩,hno⟩
     · exact Or.inr ⟨mioc.mpr ⟨by omega,hI.2⟩,hno⟩
    have hnat:=ltr (clc hsub) (cul _ _)
    exact_mod_cast hnat
   have hsum_split:∑ j∈JX,((2^j:ℕ):ℝ)^2*(((Ioc Ycut X).filter (noSqf (2^j))).card:ℝ)<=(∑ j∈JX,((2^j:ℕ):ℝ)^2*(((Ioc Ycut (X/2)).filter (noSqf (2^j))).card:ℝ))+(∑ j∈JX,((2^j:ℕ):ℝ)^2*(Mstar X (2^j):ℝ)):=by
    rw [← sum_add_distrib]
    apply sls
    intro j _
    have:=ml (hsplit_card j) (by positivity:0<=((2^j:ℕ):ℝ)^2)
    linarith only [this]
   have htop:∑ j∈JX,((2^j:ℕ):ℝ)^2*(Mstar X (2^j):ℝ)<=C*(X:ℝ):=by
    have h1:=hM X hX_ge_Y0 K hK
    have hlog_mono:Nat.log 2 Ycut<=Nat.log 2 X:=lmr (lol hle)
    have hlogYcut_pos:0 < Nat.log 2 Ycut:=by
     have:2^100000<=Ycut:=ltr hY0_ge hYcut
     have:=llp (by omega) this;omega
    have hC_ge:(2^34:ℝ)/(K:ℝ)+(2^71:ℝ)/(Nat.log 2 X:ℝ)<=C:=by
     dsimp only [C]
     have:(2^71:ℝ)/(Nat.log 2 X:ℝ)<=(2^71:ℝ)/(Nat.log 2 Ycut:ℝ):=by
      gcongr
     linarith only [this]
    have h2:=mr hC_ge (by positivity:(0:ℝ)<=(X:ℝ))
    linarith only [h1,h2]
   have hJX2_sub:JX2⊆JX:=by
    intro j hj
    rw [mf,mrng] at hj ⊢
    have:Nat.log 2 (X/2)<=Nat.log 2 X:=lmr (dvls X 2)
    exact ⟨by omega,hj.2⟩
   have hvanish:∀ j∈JX,j ∉ JX2->((2^j:ℕ):ℝ)^2*(((Ioc Ycut (X/2)).filter (noSqf (2^j))).card:ℝ)=0:=by
    intro j hj hnot
    suffices hempty:(Ioc Ycut (X/2)).filter (noSqf (2^j))=∅ by
     simp [hempty]
    rw [filter_eq_empty_iff]
    intro m hm
    have hmI:=mioc.mp hm
    have hj_ge:Nat.log 2 (X/2)+2<=j:=by
     rw [mf,mrng] at hnot
     have hKj:=(mf.mp hj).2
     by_contra hlt;push Not at hlt;exact hnot ⟨hlt,hKj⟩
    have hX2_lt:X/2 < 2^j:=by
     have hlt:X/2 < 2^(Nat.log 2 (X/2)+1):=lsl (by omega) (X/2)
     exact lt_of_lt_of_le hlt (npr (by omega) (by omega))
    have hm600:2^600<=m:=by
     have h1:2^600<=Y0:=ltr (npr (by omega) (by omega)) hY0_ge
     omega
    have hm_le:m < 2^j:=lt_of_le_of_lt hmI.2 hX2_lt
    have h109:10^9*m<=(2^j)^3:=by
     have h1:10^9<=m:=ltr (by norm_num:10^9<=2^40)
      (ltr (npr (by omega) (by omega)) hm600)
     have h2:10^9*m<=m^2:=by nlinarith only [h1]
     have h3:m^2<=m^3:=npr (by omega) (by omega)
     have h4:m^3<=(2^j)^3:=npl (lol hm_le) 3
     omega
    exact noSqf_f m (2^j) hm600 h109
   have hlow_eq:∑ j∈JX,((2^j:ℕ):ℝ)^2*(((Ioc Ycut (X/2)).filter (noSqf (2^j))).card:ℝ)=∑ j∈JX2,((2^j:ℕ):ℝ)^2*(((Ioc Ycut (X/2)).filter (noSqf (2^j))).card:ℝ):=(sum_subset hJX2_sub hvanish).symm
   have hih:=ih (X/2) (Nat.div_lt_self hX_pos (by omega))
   have hX2R:2*C*((X/2:ℕ):ℝ)<=C*(X:ℝ):=by
    have hnat:2*(X/2)<=X:=by omega
    have hR:2*((X/2:ℕ):ℝ)<=(X:ℝ):=by exact_mod_cast hnat
    have:=ml hR hCnn
    linarith only [this]
   linarith only [hsum_split,htop,hlow_eq,hih,hX2R]
lemma cubic_tail_bound (ε:ℝ) (hε:0 < ε) :
  ∃ K:ℕ,0 < K/\∀ᶠ x:ℝ in atTop,(1/x)*∑ n∈(A x).filter (fun n => K<=s (n+1) - s n),((s (n+1) - s n:ℕ):ℝ)^3<=ε:=by
 obtain ⟨Y0,hY0_ge,hM⟩:=dy_Ms
 let K0:ℕ:=max 10000 (Nat.ceil (256*(2^34:ℝ)*3 / ε)+1)
 have hK0_10k:10000<=K0:=lml _ _
 have hK0_bd:256*((2^34:ℝ)/(K0:ℝ))<=ε / 3:=by
  have hK0_pos:(0:ℝ) < (K0:ℝ):=by exact_mod_cast (by omega:0 < K0)
  have hge:256*(2^34:ℝ)*3 / ε<=(K0:ℝ):=by
   have hnat:Nat.ceil (256*(2^34:ℝ)*3 / ε)<=K0:=ltr (Nat.le_succ _) (lmrt 10000 _)
   exact ltr (Nat.le_ceil _) (Nat.cast_le.mpr hnat)
  rw [mul_div_assoc',ddi hK0_pos (by norm_num:(0:ℝ) < 3)]
  have h2:=(dli hε).mp hge
  linarith only [h2]
 let tcut:ℕ:=max (Nat.log 2 Y0+1) (max 100000 (Nat.ceil (256*(2^71:ℝ)*3 / ε)+1))
 let Ycut:ℕ:=2^tcut
 have hY0_le_Ycut:Y0<=Ycut:=by
  have hlt:Y0 < 2^(Nat.log 2 Y0+1):=lsl (by omega) Y0
  exact ltr (lol hlt) (npr (by omega) (lml _ _))
 have hlogYcut:Nat.log 2 Ycut=tcut:=Nat.log_pow (by omega:1 < 2) tcut
 have htcut_bd:256*((2^71:ℝ)/(Nat.log 2 Ycut:ℝ))<=ε / 3:=by
  rw [hlogYcut]
  have ht_pos:(0:ℝ) < (tcut:ℝ):=by
   have:100000<=tcut:=ltr (lml _ _) (lmrt _ _)
   exact_mod_cast (by omega:0 < tcut)
  have hge:256*(2^71:ℝ)*3 / ε<=(tcut:ℝ):=by
   have hnat:Nat.ceil (256*(2^71:ℝ)*3 / ε)<=tcut:=ltr (Nat.le_succ _) (ltr (lmrt _ _) (lmrt _ _))
   exact ltr (Nat.le_ceil _) (Nat.cast_le.mpr hnat)
  rw [mul_div_assoc',ddi ht_pos (by norm_num:(0:ℝ) < 3)]
  have h2:=(dli hε).mp hge
  linarith only [h2]
 let C0:ℝ:=∑ n∈range (Ycut+1),((s (n+1) - s n:ℕ):ℝ)^3
 have hC0_nn:0<=C0:=sum_nonneg (fun _ _ => by positivity)
 refine ⟨4*K0,by omega,?_⟩
 filter_upwards [eventually_ge_atTop (max 1 (3*(C0+1) / ε))] with x hx
 have hx_pos:0 < x:=lt_of_lt_of_le (by norm_num:(0:ℝ) < 1) (ltr (lml _ _) hx)
 have hx_big:3*(C0+1) / ε<=x:=ltr (lmrt _ _) hx
 set X:=⌊x⌋₊
 have hXR_le:(X:ℝ)<=x:=Nat.floor_le (lol hx_pos)
 set D:=(A x).filter (fun n => 4*K0<=s (n+1) - s n)
 set Dlo:=D.filter (fun n => s n<=Ycut)
 set Dhi:=D.filter (fun n => Ycut < s n)
 have hD_split:∑ n∈D,((s (n+1) - s n:ℕ):ℝ)^3=(∑ n∈Dlo,((s (n+1) - s n:ℕ):ℝ)^3)+(∑ n∈Dhi,((s (n+1) - s n:ℕ):ℝ)^3):=by
  have:=(sum_filter_add_sum_filter_not D (fun n => s n<=Ycut)
   (fun n => ((s (n+1) - s n:ℕ):ℝ)^3)).symm
  convert this using 2
  apply sum_congr _ (fun _ _ => rfl)
  ext n;simp only [Dhi,mf,not_le]
 have hlo_bd:(1/x)*∑ n∈Dlo,((s (n+1) - s n:ℕ):ℝ)^3<=ε / 3:=by
  have hsub:Dlo⊆range (Ycut+1):=by
   intro n hn
   have hsn:s n<=Ycut:=(mf.mp hn).2
   have hmono:StrictMono s:=Nat.nth_strictMono Nat.squarefree_infinite
   have hle:n<=s n:=hmono.id_le n
   exact mrng.mpr (by omega)
  have h1:∑ n∈Dlo,((s (n+1) - s n:ℕ):ℝ)^3<=C0:=ssub hsub (fun _ _ _ => by positivity)
  have h2:(1/x)*C0<=ε / 3:=by
   rw [one_div_mul_eq_div,ddi hx_pos (by norm_num:(0:ℝ) < 3)]
   have:=(dli hε).mp hx_big
   linarith only [this,hC0_nn]
  have h3:=ml h1 (by positivity:0<=1/x)
  linarith only [h2,h3]
 set J2X:=(range (Nat.log 2 (2*X)+2)).filter (fun j => K0<=2^j)
 let j_of:ℕ->ℕ:=fun n => Nat.log 2 ((s (n+1) - s n)/2)
 have hsn_le_X:∀ n∈Dhi,s n<=X:=by
  intro n hn
  have hA:n∈A x:=(mf.mp (mf.mp hn).1).1
  exact (micc.mp (mem_preimage.mp hA)).2
 have hgap_le_sn:∀ n∈Dhi,s (n+1) - s n<=s n:=by
  intro n hn
  have hgt:Ycut < s n:=(mf.mp hn).2
  have h600:2^600<=s n:=by
   have:2^600<=Ycut:=ltr (npr (by omega) (by omega)) (ltr hY0_ge hY0_le_Ycut)
   omega
  have h109:10^9*s n<=(s n)^3:=by
   have h1:10^9<=s n:=ltr (by norm_num:10^9<=2^40)
    (ltr (npr (by omega) (by omega)) h600)
   have h2:10^9*s n<=(s n)^2:=by nlinarith only [h1]
   have h3:(s n)^2<=(s n)^3:=npr (by omega) (by omega)
   omega
  have hnot:=noSqf_f (s n) (s n) h600 h109
  unfold noSqf at hnot;push Not at hnot
  obtain ⟨t,ht,hsqf⟩:=hnot
  have htIcc:=micc.mp ht
  by_contra hbig;push Not at hbig
  have hmono:StrictMono s:=Nat.nth_strictMono Nat.squarefree_infinite
  have hlt_succ:s n+t < s (n+1):=by omega
  have hgt_sn:s n < s n+t:=by omega
  have hcount:=nth_add (n:=n) (k:=s (n+1) - s n)
   (Nat.sub_pos_of_lt (hmono (Nat.lt_succ_self n)))
  have hnosqf:=(hcount.mp rfl).2 t (mem_Ioo.mpr ⟨by omega,by omega⟩)
  exact hnosqf hsqf
 have hmaps:∀ n∈Dhi,j_of n∈J2X:=by
  intro n hn
  have hgap:4*K0<=s (n+1) - s n:=(mf.mp (mf.mp hn).1).2
  have hhalf:2*K0<=(s (n+1) - s n)/2:=by omega
  have hlt:(s (n+1) - s n)/2 < 2^(j_of n+1):=lsl (by omega) _
  have hK0_le:K0<=2^(j_of n):=by
   have:2^(j_of n+1)=2*2^(j_of n):=by ring
   omega
  have hle_X:(s (n+1) - s n)/2<=2*X:=by
   have:=hgap_le_sn n hn;have:=hsn_le_X n hn;omega
  have hlog_le:j_of n<=Nat.log 2 (2*X):=lmr hle_X
  exact mf.mpr ⟨mrng.mpr (by omega),hK0_le⟩
 have hfib_bd:∀ j∈J2X,∑ n∈Dhi.filter (fun n => j_of n=j),((s (n+1) - s n:ℕ):ℝ)^3<=64*((2^j:ℕ):ℝ)^2*(((Ioc Ycut (2*X)).filter (noSqf (2^j))).card:ℝ):=by
  intro j hj
  set F:=Dhi.filter (fun n => j_of n=j)
  have hterm_le:∀ n∈F,((s (n+1) - s n:ℕ):ℝ)^3<=64*((2^j:ℕ):ℝ)^3:=by
   intro n hn
   have hj_eq:j_of n=j:=(mf.mp hn).2
   have hlt:(s (n+1) - s n)/2 < 2^(j+1):=by
    rw [← hj_eq];exact lsl (by omega) _
   have hle4:s (n+1) - s n<=4*2^j:=by
    have:2^(j+1)=2*2^j:=by ring
    omega
   have hR:((s (n+1) - s n:ℕ):ℝ)<=4*((2^j:ℕ):ℝ):=by exact_mod_cast hle4
   have hcub:((s (n+1) - s n:ℕ):ℝ)^3<=(4*((2^j:ℕ):ℝ))^3:=by gcongr
   have h64:(4*((2^j:ℕ):ℝ))^3=64*((2^j:ℕ):ℝ)^3:=by ring
   linarith only [hcub,h64]
  have hcard_nat:F.card*2^j<=((Ioc Ycut (2*X)).filter (noSqf (2^j))).card:=by
   have hdisj:Set.PairwiseDisjoint (F:Set ℕ) (fun n => Ico (s n) (s n+2^j)):=by
    intro n1 hn1 n2 hn2 hne
    have hmono:StrictMono s:=Nat.nth_strictMono Nat.squarefree_infinite
    have hstep:∀ a∈F,s a+2^j<=s (a+1):=by
     intro a ha
     have hj_eq:j_of a=j:=(mf.mp ha).2
     have hgap:4*K0<=s (a+1) - s a:=(mf.mp (mf.mp (mf.mp ha).1).1).2
     have hpow:2^j<=(s (a+1) - s a)/2:=by
      rw [← hj_eq];exact pls 2 (by omega)
     have hlt:=hmono (Nat.lt_succ_self a)
     omega
    change Disjoint _ _
    rw [disjoint_left]
    intro m hm1 hm2
    have h1:=mico.mp hm1;have h2:=mico.mp hm2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    ·
     have:s (n1+1)<=s n2:=hmono.monotone (by omega)
     have:=hstep n1 (mem_coe.mp hn1);omega
    ·
     have:s (n2+1)<=s n1:=hmono.monotone (by omega)
     have:=hstep n2 (mem_coe.mp hn2);omega
   have hsub:F.biUnion (fun n => Ico (s n) (s n+2^j)) ⊆
     (Ioc Ycut (2*X)).filter (noSqf (2^j)):=by
    intro m hm
    obtain ⟨n,hn,hmI⟩:=mbu.mp hm
    have hmIco:=mico.mp hmI
    have hn_Dhi:n∈Dhi:=(mf.mp hn).1
    have hgt:Ycut < s n:=(mf.mp hn_Dhi).2
    have hj_eq:j_of n=j:=(mf.mp hn).2
    have hgap:4*K0<=s (n+1) - s n:=(mf.mp (mf.mp hn_Dhi).1).2
    have hpow:2^j<=(s (n+1) - s n)/2:=by
     rw [← hj_eq];exact pls 2 (by omega)
    have hle_X:s n<=X:=hsn_le_X n hn_Dhi
    have hgap_X:s (n+1) - s n<=X:=ltr (hgap_le_sn n hn_Dhi) hle_X
    rw [mf,mioc]
    refine ⟨⟨by omega,by omega⟩,?_⟩
    intro t ht
    have htIcc:=micc.mp ht
    have hmono:StrictMono s:=Nat.nth_strictMono Nat.squarefree_infinite
    have hlt_sn:=hmono (Nat.lt_succ_self n)
    have hcount:=(nth_add (n:=n) (k:=s (n+1) - s n) (by omega)).mp rfl
    have hd_pos:0 < m+t - s n:=by omega
    have hd_lt:m+t - s n < s (n+1) - s n:=by omega
    have hnosqf:=hcount.2 (m+t - s n) (mem_Ioo.mpr ⟨hd_pos,hd_lt⟩)
    have heq:s n+(m+t - s n)=m+t:=by omega
    rwa [heq] at hnosqf
   calc F.card*2^j
     = ∑ n∈F,(Ico (s n) (s n+2^j)).card:=by simp
    _=(F.biUnion (fun n => Ico (s n) (s n+2^j))).card:=(card_biUnion hdisj).symm
    _<=((Ioc Ycut (2*X)).filter (noSqf (2^j))).card:=clc hsub
  have hsum1:=sls hterm_le
  simp only [sum_const,nsmul_eq_mul] at hsum1
  have hcardR:(F.card:ℝ)*((2^j:ℕ):ℝ)<=(((Ioc Ycut (2*X)).filter (noSqf (2^j))).card:ℝ):=by exact_mod_cast hcard_nat
  have h2:=ml hcardR (by positivity:0<=64*((2^j:ℕ):ℝ)^2)
  have hl:(F.card:ℝ)*(64*((2^j:ℕ):ℝ)^3)=64*((2^j:ℕ):ℝ)^2*((F.card:ℝ)*((2^j:ℕ):ℝ)):=by ring
  linarith only [hsum1,h2,hl]
 have hhi_sum:∑ n∈Dhi,((s (n+1) - s n:ℕ):ℝ)^3<=64*∑ j∈J2X,((2^j:ℕ):ℝ)^2*(((Ioc Ycut (2*X)).filter (noSqf (2^j))).card:ℝ):=by
  rw [← sum_fiberwise_of_maps_to hmaps,mul_sum]
  apply sls
  intro j hj
  have:=hfib_bd j hj
  linarith only [this]
 have hIoc:=dy_Ioc Y0 hY0_ge hM Ycut K0 hY0_le_Ycut hK0_10k (2*X)
 have hhi_bd:(1/x)*∑ n∈Dhi,((s (n+1) - s n:ℕ):ℝ)^3<=2*ε / 3:=by
  have h1:∑ n∈Dhi,((s (n+1) - s n:ℕ):ℝ)^3<=256*((2^34:ℝ)/(K0:ℝ)+(2^71:ℝ)/(Nat.log 2 Ycut:ℝ))*(X:ℝ):=by
   have hA:=ml hIoc (by norm_num:(0:ℝ)<=64)
   have hB:64*(2*((2^34:ℝ)/(K0:ℝ)+(2^71:ℝ)/(Nat.log 2 Ycut:ℝ))*((2*X:ℕ):ℝ))=256*((2^34:ℝ)/(K0:ℝ)+(2^71:ℝ)/(Nat.log 2 Ycut:ℝ))*(X:ℝ):=by
    push_cast;ring
   linarith only [hhi_sum,hA,hB]
  have h2:256*((2^34:ℝ)/(K0:ℝ)+(2^71:ℝ)/(Nat.log 2 Ycut:ℝ))<=2*ε / 3:=by
   linarith only [hK0_bd,htcut_bd]
  have h3:∑ n∈Dhi,((s (n+1) - s n:ℕ):ℝ)^3<=(2*ε / 3)*x:=by
   have hA:=mr h2 (by positivity:(0:ℝ)<=(X:ℝ))
   have hB:=ml hXR_le (by positivity:(0:ℝ)<=2*ε / 3)
   linarith only [h1,hA,hB]
  have h4:=ml h3 (by positivity:(0:ℝ)<=1/x)
  have hr:1/x*((2*ε / 3)*x)=2*ε / 3:=by field_simp
  linarith only [h4,hr]
 rw [hD_split,mul_add]
 linarith only [hlo_bd,hhi_bd]
end Erdos145CubicGap
open scoped Topology in
theorem OMA.solution:OMA.R_Erdos145_erdos_145_variants_le_three_R1.H2:=by
 classical
 open Filter Finset Erdos145 in
 let g (n:ℕ):=s (n+1) - s n
 let f (x:ℝ):=1/x*∑ n∈A x,((g n:ℕ):ℝ)^3
 change ∃ L:ℝ,Tendsto f atTop (𝓝 L)
 choose d hd using Erdos145CubicGap.fixed_gap_density
 let T (K:ℕ) (x:ℝ):=∑ k∈range K,(1/x*(((A x).filter fun n => g n=k).card:ℝ))*(k:ℝ)^3
 have tend (K:ℕ):Tendsto (T K) atTop (𝓝 (∑ k∈range K,d k*(k:ℝ)^3)):=tendsto_finsetSum _ (fun k _ => (hd k).mul_const _)
 have hdiff (K:ℕ) (x:ℝ) :
   f x - T K x=1/x*∑ n∈(A x).filter (fun n => K<=g n),((g n:ℕ):ℝ)^3:=by
  have htrunc:∑ k∈range K,(((A x).filter fun n => g n=k).card:ℝ)*(k:ℝ)^3=∑ n∈(A x).filter (fun n => g n < K),((g n:ℕ):ℝ)^3:=by
   calc ∑ k∈range K,(((A x).filter fun n => g n=k).card:ℝ)*(k:ℝ)^3
    _=∑ k∈range K,∑ n∈(A x).filter (fun n => g n=k),((g n:ℕ):ℝ)^3:=by
       apply sum_congr rfl;intro k _
       rw [← nsmul_eq_mul,← sum_const]
       exact sum_congr rfl (fun n hn => by rw [(mem_filter.mp hn).2])
    _=_:=by
       simpa only [mem_range] using
        sum_fiberwise_eq_sum_filter (A x) (range K) g (fun n => ((g n:ℕ):ℝ)^3)
  have hT:T K x=1/x*∑ n∈(A x).filter (fun n => g n < K),((g n:ℕ):ℝ)^3:=by
   dsimp only [T];rw [← htrunc,mul_sum]
   exact sum_congr rfl (fun k _ => by ring)
  have hsplit:=sum_filter_add_sum_filter_not (A x) (fun n => g n < K)
   (fun n => ((g n:ℕ):ℝ)^3)
  have hnot:(A x).filter (fun n => ¬ g n < K)=(A x).filter (fun n => K<=g n):=by
   ext n;simp only [mem_filter,not_lt]
  dsimp only [f];rw [hT,← hsplit,hnot,mul_add];ring
 apply cauchySeq_tendsto_of_complete
 apply Metric.cauchySeq_iff.mpr
 intro ε hε
 obtain ⟨K,_,htail⟩:=Erdos145CubicGap.cubic_tail_bound (ε / 4) (by linarith)
 have hcauch:=Metric.cauchySeq_iff.mp (tend K).cauchySeq (ε / 4) (by linarith)
 obtain ⟨N,hN⟩:=hcauch
 obtain ⟨M,hM⟩:=eventually_atTop.mp (htail.and (eventually_gt_atTop (0:ℝ)))
 refine ⟨max N M,fun x hx y hy => ?_⟩
 have ht:=hN x (le_trans (le_max_left _ _) hx) y (le_trans (le_max_left _ _) hy)
 have h1:=hM x (le_trans (le_max_right _ _) hx)
 have h2:=hM y (le_trans (le_max_right _ _) hy)
 have hd1:|f x - T K x|<=ε / 4:=by
  rw [hdiff K x,abs_of_nonneg (by have:=h1.2;positivity)]
  exact h1.1
 have hd2:|f y - T K y|<=ε / 4:=by
  rw [hdiff K y,abs_of_nonneg (by have:=h2.2;positivity)]
  exact h2.1
 rw [Real.dist_eq] at ht ⊢
 rw [abs_le] at hd1 hd2
 rw [abs_lt] at ht ⊢
 constructor <;> linarith only [hd1.1,hd1.2,hd2.1,hd2.2,ht.1,ht.2]
