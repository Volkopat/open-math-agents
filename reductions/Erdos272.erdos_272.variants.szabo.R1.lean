import FormalConjectures.ErdosProblems.«272»
import Mathlib

/-! Arithmetic progression packing, the star lower bound, and Szabó’s family decomposition. -/
open Finset Real Erdos272

namespace OMA.R_Erdos272_erdos_272_variants_szabo_R1


namespace SzaboStar

theorem short_ap (s : Finset ℕ) (hne : s.Nonempty) (small : s.card≤2) :
    ∃ l > (0:ℕ∞), (s : Set ℕ).IsAPOfLength l := by
  by_cases h : s.card=1
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨1,by decide,Set.IsAPOfLength.one.mpr ⟨a,by simp⟩⟩
  · have two : s.card=2 := by have := Finset.card_pos.mpr hne; omega
    obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp two
    rcases lt_or_gt_of_ne ab with lt|gt
    · exact ⟨2,by decide, a,b-a,by simpa using Nat.isAPOfLengthWith_pair lt⟩
    · refine ⟨2,by decide,b,a-b,?_⟩
      simpa [Finset.pair_comm a b] using Nat.isAPOfLengthWith_pair gt

theorem star_bound (N : ℕ) (hn : 1≤N) : N.choose 2 + 1 ≤ maxArithInterCard N := by
  classical
  let U := Finset.Icc 1 N
  let P := U.powersetCard 2
  let F := insert {1} (P.image (insert 1))
  have pp {p : Finset ℕ} (hp : p∈P) : p⊆U ∧ p.card=2 := Finset.mem_powersetCard.mp hp
  have erase {p q : Finset ℕ} (hp : p∈P) (hq : q∈P) (eq : insert 1 p=insert 1 q) : p=q := by
    by_cases a : 1∈p <;> by_cases b : 1∈q
    · simpa [a,b] using eq
    · have := congrArg Finset.card eq; simp [a,b,(pp hp).2,(pp hq).2] at this
    · have := congrArg Finset.card eq; simp [a,b,(pp hp).2,(pp hq).2] at this
    · simpa [a,b] using congrArg (fun z : Finset ℕ => z.erase 1) eq
  have fresh : ({1}:Finset ℕ) ∉ P.image (insert 1) := by
    rintro h
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp h
    have card := Finset.card_le_card (Finset.subset_insert 1 p)
    rw [eq,(pp hp).2] at card; simp at card
  have size : F.card=N.choose 2+1 := by
    rw [Finset.card_insert_of_notMem fresh,Finset.card_image_of_injOn (fun _ hp _ hq => erase hp hq),
      Finset.card_powersetCard]; simp [U]
  have properties (s : Finset ℕ) (hs : s∈F) : 1∈s ∧ s⊆U ∧ s.card≤3 := by
    rcases Finset.mem_insert.mp hs with rfl|mem
    · simp [U,hn]
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp mem
      refine ⟨mem_insert_self ..,insert_subset (Finset.mem_Icc.mpr ⟨by decide,hn⟩) (pp hp).1,?_⟩
      have := Finset.card_insert_le 1 p
      have sizep := (pp hp).2
      omega
  have valid : IsArithInterSet N F := by
    refine ⟨fun s hs => Finset.mem_powerset.mpr (properties s hs).2.1,?_⟩
    intro s hs t ht ne
    obtain ⟨one,_,sc⟩ := properties s hs
    obtain ⟨two,_,tc⟩ := properties t ht
    apply short_ap _ ⟨1,mem_inter.mpr ⟨one,two⟩⟩
    by_contra! big
    have a : s∩t = s := Finset.eq_of_subset_of_card_le inter_subset_left (by omega)
    have b : s∩t = t := Finset.eq_of_subset_of_card_le inter_subset_right (by omega)
    exact ne (a.symm.trans b)
  rw [←size]
  apply le_csSup (a := F.card)
  · refine ⟨U.powerset.card,?_⟩
    rintro _ ⟨A,hA,rfl⟩; exact Finset.card_le_card hA.1
  · exact ⟨F,valid,rfl⟩

end SzaboStar


theorem szabo_fixed_step (N d : ℕ) (dp : 0<d) (F : Finset (Finset ℕ))
    (l r : Finset ℕ → ℕ)
    (ends : ∀ s∈F, 1≤l s ∧ l s≤r s ∧ r s≤N ∧ r s ≡ l s [MOD d])
    (description : ∀ s∈F, ∀ x, x∈s ↔ l s≤x ∧ x≤r s ∧ x ≡ l s [MOD d])
    (meet : ∀ s∈F, ∀ t∈F, (s∩t).Nonempty) :
    (F.card:ℝ) ≤ (((N:ℝ)/d+2)/2)^2 := by
  classical
  rcases F.eq_empty_or_nonempty with rfl|nonempty
  · simp [sq_nonneg]
  obtain ⟨m,hm,maximal⟩ := Finset.exists_max_image F l nonempty
  let c := l m
  have mc := ends m hm
  have anchor (s : Finset ℕ) (hs : s∈F) : l s≤c ∧ c≤r s ∧ c ≡ l s [MOD d] := by
    obtain ⟨x,hx⟩ := meet s hs m hm
    obtain ⟨_,xr,xs⟩ := (description s hs x).mp (Finset.mem_inter.mp hx).1
    obtain ⟨cx,_,xm⟩ := (description m hm x).mp (Finset.mem_inter.mp hx).2
    exact ⟨maximal s hs,cx.trans xr,xm.symm.trans xs⟩
  let code (s : Finset ℕ) := ((c-l s)/d,(r s-c)/d)
  have reconstruct (s : Finset ℕ) (hs : s∈F) :
      d*(code s).1=c-l s ∧ d*(code s).2=r s-c := by
    have h := anchor s hs
    have e := ends s hs
    refine ⟨Nat.mul_div_cancel' ?_, Nat.mul_div_cancel' ?_⟩
    · exact (Nat.modEq_iff_dvd' h.1).mp h.2.2.symm
    · exact (Nat.modEq_iff_dvd' h.2.1).mp (h.2.2.trans e.2.2.2.symm)
  have ci : Set.InjOn code F := by
    intro s hs t ht eq
    have eq1 := congrArg Prod.fst eq
    have eq2 := congrArg Prod.snd eq
    obtain ⟨u,v⟩ := reconstruct s hs; obtain ⟨w,z⟩ := reconstruct t ht
    rw [eq1] at u; rw [eq2] at v
    have as := anchor s hs; have at' := anchor t ht
    have left : l s=l t := by omega
    have right : r s=r t := by omega
    ext x; rw [description s hs,description t ht,left,right]
  let a := (c-1)/d
  let b := (N-c)/d
  have sub : F.image code ⊆ (range (a+1)) ×ˢ (range (b+1)) := by
    rintro _ h; obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp h
    have e := ends s hs
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))),
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))⟩
  have count := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn ci, Finset.card_product,Finset.card_range,Finset.card_range] at count
  have hab : d*(a+b) ≤ N := by
    have u : d*a ≤ c-1 := by dsimp [a]; rw [Nat.mul_comm]; exact Nat.div_mul_le_self .. 
    have v : d*b ≤ N-c := by dsimp [b]; rw [Nat.mul_comm]; exact Nat.div_mul_le_self ..
    dsimp [c] at *; rw [Nat.mul_add]; omega
  have rp : (0:ℝ)<d := by exact_mod_cast dp
  have sum : (a:ℝ)+b ≤ (N:ℝ)/d := (le_div_iff₀ rp).mpr (by
    rw [mul_comm]; exact_mod_cast hab)
  have pos : (0:ℝ)≤N/d := by positivity
  have sq := mul_self_le_mul_self (by positivity : 0≤(a:ℝ)+b+2) (by linarith : (a:ℝ)+b+2 ≤ N/d+2)
  have cr : (F.card:ℝ)≤((a:ℝ)+1)*(b+1) := by exact_mod_cast count
  nlinarith [sq_nonneg ((a:ℝ)-b)]



theorem szabo_reciprocal_squares (n : ℕ) :
    (∑ j ∈ range (n+1), (1/((j:ℝ)+1))^2) ≤ 2-1/((n:ℝ)+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have t : (1/((n:ℝ)+1+1))^2 ≤ 1/((n:ℝ)+1) - 1/((n:ℝ)+1+1) := by
      have a : 0<(n:ℝ)+1 := by positivity
      have b : 0<(n:ℝ)+1+1 := by positivity
      field_simp
      nlinarith
    linarith

theorem szabo_endpoint_sum (n : ℕ) :
    (∑ j ∈ range n, (((n:ℝ)/((j:ℝ)+1)+2)/2)^2) ≤
      (n:ℝ)^2/2 + n*sqrt (2*n) + n := by
  let r (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have rr : ∑ i ∈ range n, (r i)^2 ≤ 2 := by
    cases n with
    | zero => simp
    | succ k => have h := szabo_reciprocal_squares k; dsimp [r]; linarith [show 0≤1/((k:ℝ)+1) by positivity]
  have c := sq_sum_le_card_mul_sum_sq (s := range n) (f := r)
  have rs : ∑ j ∈ range n,r j ≤ sqrt (2*n) := by
    apply le_sqrt_of_sq_le
    simp only [Finset.card_range] at c
    nlinarith [mul_le_mul_of_nonneg_left rr (Nat.cast_nonneg (α := ℝ) n)]
  have expand (j : ℕ) : (((n:ℝ)/((j:ℝ)+1)+2)/2)^2 = ((n:ℝ)^2/4)*(r j)^2+n*r j+1 := by dsimp [r]; ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left rr (show 0≤(n:ℝ)^2/4 by positivity),
    mul_le_mul_of_nonneg_left rs (Nat.cast_nonneg (α := ℝ) n)]



theorem szabo_describe (N : ℕ) (s : Finset ℕ) (sub : s ⊆ Icc 1 N)
    (ap : ∃ L > (0:ℕ∞), (s : Set ℕ).IsAPOfLength L) :
    ∃ d a b : ℕ, 0<d ∧ d≤N ∧ 1≤a ∧ a≤b ∧ b≤N ∧ b ≡ a [MOD d] ∧
      ∀ x, x∈s ↔ a≤x ∧ x≤b ∧ x ≡ a [MOD d] := by
  classical
  obtain ⟨L,pos,a,d,rep⟩ := ap
  have len : L=(s.card:ℕ∞) := by rw [←rep.card]; simp
  subst L
  have index (x : ℕ) : x∈s ↔ ∃ k<s.card, x=a+k*d := by
    change x∈(s:Set ℕ) ↔ _
    rw [rep.eq]
    simp only [Set.mem_ofPred_eq, smul_eq_mul, ENat.natCast_lt_natCast]
    aesop
  have pos' : 0<s.card := by exact_mod_cast pos
  have start : a∈s := (index a).mpr ⟨0,pos',by simp⟩
  have ab := Finset.mem_Icc.mp (sub start)
  by_cases small : s.card=1
  · obtain ⟨z,hz⟩ := Finset.card_eq_one.mp small
    have az : a=z := by simpa [hz] using start
    subst z
    refine ⟨1,a,a,by decide,by omega,ab.1,le_rfl,ab.2,Nat.ModEq.refl _,?_⟩
    intro x; simp [hz,Nat.ModEq]; omega
  have dp : 0<d := by
    by_contra! h
    have dz : d=0 := by omega
    have ss : s ⊆ {a} := by
      intro x hx
      obtain ⟨k,_,eq⟩ := (index x).mp hx
      simpa [dz] using eq
    have := Finset.card_le_card ss
    simp only [Finset.card_singleton] at this
    omega
  let t := s.card-1
  have tlt : t<s.card := by dsimp [t]; omega
  have last : a+t*d∈s := (index _).mpr ⟨t,tlt,rfl⟩
  have nxt : a+1*d∈s := (index _).mpr ⟨1,by omega,rfl⟩
  have mx := (Finset.mem_Icc.mp (sub last)).2
  have dn := (Finset.mem_Icc.mp (sub nxt)).2
  simp only [one_mul] at dn
  refine ⟨d,a,a+t*d,dp,by omega,ab.1,Nat.le_add_right ..,mx,?_,?_⟩
  · show (a+t*d)%d = a%d
    simp
  intro x
  rw [index]
  constructor
  · rintro ⟨k,hk,rfl⟩
    refine ⟨Nat.le_add_right ..,Nat.add_le_add_left (Nat.mul_le_mul_right _ (by dsimp [t]; omega)) _,?_⟩
    show (a+k*d)%d=a%d
    simp
  · rintro ⟨ax,xb,xa⟩
    obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' ax).mp xa.symm
    have xk : x=a+k*d := by rw [Nat.mul_comm] at hk; omega
    have kt : k*d≤t*d := by omega
    have := (mul_le_mul_iff_left₀ dp).mp kt
    exact ⟨k,by omega,xk⟩
theorem szabo_ap_family_bound (N : ℕ) (F : Finset (Finset ℕ))
    (valid : IsArithInterSet N F)
    (ap : ∀ s∈F, ∃ L > (0:ℕ∞), (s : Set ℕ).IsAPOfLength L) :
    (F.card:ℝ) ≤ (N:ℝ)^2/2 + N*Real.sqrt (2*N) + N := by
  classical
  have repr (s : Finset ℕ) : ∃ d a b : ℕ, s∈F →
      0<d ∧ d≤N ∧ 1≤a ∧ a≤b ∧ b≤N ∧ b ≡ a [MOD d] ∧
      ∀ x, x∈s ↔ a≤x ∧ x≤b ∧ x ≡ a [MOD d] := by
    by_cases h : s∈F
    · obtain ⟨d,a,b,rep⟩ := szabo_describe N s (mem_powerset.mp (valid.1 h)) (ap s h)
      exact ⟨d,a,b,fun _ => rep⟩
    · exact ⟨1,0,0,fun hs => (h hs).elim⟩
  choose d a b rep using repr
  have maps : (F:Set (Finset ℕ)).MapsTo (fun s => d s-1) (range N) := by
    intro s hs
    rcases rep s hs with ⟨hp,hn,_⟩
    exact mem_range.mpr (show d s-1<N by omega)
  have count := Finset.card_eq_sum_card_fiberwise maps
  have meet (s) (hs : s∈F) (t) (ht : t∈F) : (s∩t).Nonempty := by
    by_cases e : s=t
    · subst t
      rw [Finset.inter_self]
      have u := rep s hs
      exact ⟨a s,(u.2.2.2.2.2.2 _).mpr ⟨le_rfl,u.2.2.2.1,Nat.ModEq.refl _⟩⟩
    · obtain ⟨L,pos,v,h,vrep⟩ := valid.2 hs ht e
      have size := vrep.card
      simp only [ENat.card_coe_set_eq] at size
      apply Finset.card_pos.mp
      rw [←size] at pos
      exact_mod_cast pos
  calc
    (F.card:ℝ) = ∑ j∈range N, ((F.filter (fun s => d s-1=j)).card:ℝ) := by exact_mod_cast count
    _ ≤ ∑ j∈range N, (((N:ℝ)/((j:ℝ)+1)+2)/2)^2 := by
      apply Finset.sum_le_sum
      intro j hj
      let G := F.filter fun s => d s-1=j
      have info (s) (hs : s∈G) : s∈F ∧ d s=j+1 := by
        obtain ⟨mem,eq⟩ := mem_filter.mp hs
        have pos := (rep s mem).1
        exact ⟨mem,by omega⟩
      have packed := szabo_fixed_step N (j+1) (by omega) G a b (by
        intro s hs
        obtain ⟨mem,eq⟩ := info s hs
        obtain ⟨_,_,h1,h2,h3,h4,_⟩ := rep s mem
        exact ⟨h1,h2,h3,eq ▸ h4⟩) (by
        intro s hs
        obtain ⟨mem,eq⟩ := info s hs
        exact eq ▸ (rep s mem).2.2.2.2.2.2) (fun s hs t ht => meet s (info s hs).1 t (info t ht).1)
      simpa only [Nat.cast_add,Nat.cast_one] using packed
    _ ≤ _ := szabo_endpoint_sum N

/-- Szabó, Lemma 2.2, at the error scale needed here. -/
def H1 : Prop := ∃ C : ℝ, 0≤C ∧ ∃ n₀ : ℕ, ∀ N≥n₀, ∀ F : Finset (Finset ℕ),
  IsArithInterSet N F → (∀ s∈F, (¬∃ l>(0:ℕ∞), (s:Set ℕ).IsAPOfLength l) ∧
    (N:ℝ)^((2:ℝ)/3)<s.card) → (F.card:ℝ) ≤ C*((N:ℝ)^((5:ℝ)/3)*(log N)^3)

/-- The small-set, empty-intersection estimate from Simonovits and Sós, Theorem 4. -/
def H2 : Prop := ∃ C : ℝ, 0≤C ∧ ∃ n₀ : ℕ, ∀ N≥n₀, ∀ F : Finset (Finset ℕ),
  IsArithInterSet N F → (∀ s∈F, (¬∃ l>(0:ℕ∞), (s:Set ℕ).IsAPOfLength l) ∧
    (s.card:ℝ)≤(N:ℝ)^((2:ℝ)/3)) → (¬∃ c∈Icc 1 N, ∀ s∈F, c∈s) →
    (F.card:ℝ) ≤ C*((N:ℝ)^((5:ℝ)/3)*(log N)^3)

/-- The common-point case of Szabó, Section 4, restricted to small nonprogressions. -/
def H3 : Prop := ∃ C : ℝ, 0≤C ∧ ∃ n₀ : ℕ, ∀ N≥n₀, ∀ F : Finset (Finset ℕ),
  IsArithInterSet N F → (∃ c∈Icc 1 N, ∀ s∈F, (¬∃ l>(0:ℕ∞), (s:Set ℕ).IsAPOfLength l) →
    c∈s ∧ (s.card:ℝ)≤(N:ℝ)^((2:ℝ)/3)) →
    (F.card:ℝ) ≤ (N:ℝ)^2/2+C*((N:ℝ)^((5:ℝ)/3)*(log N)^3)

theorem error_scale (n : ℝ) (one : 1≤n) (lg : 1≤log n) :
    n ≤ n^((5:ℝ)/3)*(log n)^3 ∧ n*sqrt (2*n) ≤ 2*(n^((5:ℝ)/3)*(log n)^3) := by
  have pos : 0<n := by linarith
  have factor : 1≤(log n)^3 := one_le_pow₀ lg
  have h := le_mul_of_one_le_right (rpow_nonneg pos.le ((5:ℝ)/3)) factor
  have initial := rpow_le_rpow_of_exponent_le one (by norm_num : (1:ℝ)≤5/3)
  rw [rpow_one] at initial
  refine ⟨initial.trans h,?_⟩
  have sh : sqrt (2*n) ≤ 2*sqrt n := by
    rw [sqrt_mul (by norm_num : (0:ℝ)≤2)]
    gcongr
    exact (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
  have r : n*sqrt n ≤ n^((5:ℝ)/3) := calc
    n*sqrt n = n^((1:ℝ)+1/2) := by rw [rpow_add pos,rpow_one,sqrt_eq_rpow]
    _ ≤ _ := rpow_le_rpow_of_exponent_le one (by norm_num)
  linarith [mul_le_mul_of_nonneg_left sh pos.le, r.trans h]

theorem main : H1 → H2 → H3 → type_of% @Erdos272.erdos_272.variants.szabo := by
  classical
  rintro ⟨B,B0,b,big⟩ ⟨S,S0,s₀,small⟩ ⟨M,M0,m,mixed⟩
  obtain ⟨k,hk⟩ := exists_nat_gt (exp 1)
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨B+S+M+3,Filter.eventually_atTop.mpr ⟨max (max (max b s₀) m) (max k 1),?_⟩⟩
  intro N hN
  have bounds : b≤N ∧ s₀≤N ∧ m≤N ∧ k≤N ∧ 1≤N := by simpa [max_le_iff,and_assoc] using hN
  obtain ⟨bn,sn,mn,kn,on⟩ := bounds
  have one : (1:ℝ)≤N := by exact_mod_cast on
  have lg : 1≤log (N:ℝ) := (le_log_iff_exp_le (by positivity : (0:ℝ)<N)).mpr
    (hk.le.trans (by exact_mod_cast kn))
  let E := (N:ℝ)^((5:ℝ)/3)*(log N)^3
  have esc := error_scale N one lg
  change (N:ℝ)≤E ∧ (N:ℝ)*sqrt (2*N)≤2*E at esc
  have ep : 0≤E := by linarith [esc.1]
  have be := mul_nonneg B0 ep
  have se := mul_nonneg S0 ep
  have me := mul_nonneg M0 ep
  have upper (F : Finset (Finset ℕ)) (ok : IsArithInterSet N F) :
      (F.card:ℝ) ≤ (N:ℝ)^2/2+(B+S+M+3)*E := by
    let AP (s : Finset ℕ) := ∃ l>(0:ℕ∞), (s:Set ℕ).IsAPOfLength l
    let large (s : Finset ℕ) := ¬AP s ∧ (N:ℝ)^((2:ℝ)/3)<s.card
    let G := F.filter large
    let A := F.filter (fun s => ¬large s)
    let P := A.filter AP
    let Q := A.filter (fun s => ¬AP s)
    have subok {T : Finset (Finset ℕ)} (h : T⊆F) : IsArithInterSet N T :=
      ⟨h.trans ok.1,fun _ hu _ hv ne => ok.2 (h hu) (h hv) ne⟩
    have ga : G.card+A.card=F.card := Finset.card_filter_add_card_filter_not ..
    have pq : P.card+Q.card=A.card := Finset.card_filter_add_card_filter_not ..
    have bb : (G.card:ℝ)≤B*E := big N bn G (subok (filter_subset ..))
      (fun _ hs => (mem_filter.mp hs).2)
    have ak : IsArithInterSet N A := subok (filter_subset ..)
    have character {u} (hu : u∈A) (hn : ¬AP u) : (u.card:ℝ)≤(N:ℝ)^((2:ℝ)/3) :=
      le_of_not_gt (fun h => (mem_filter.mp hu).2 ⟨hn,h⟩)
    have gr : (G.card:ℝ)+A.card=F.card := by exact_mod_cast ga
    by_cases common : ∃ c∈Icc 1 N, ∀ u∈Q, c∈u
    · obtain ⟨c,hc,all⟩ := common
      have ma : (A.card:ℝ)≤(N:ℝ)^2/2+M*E := mixed N mn A ak
        ⟨c,hc,fun u hu hn => ⟨all u (mem_filter.mpr ⟨hu,hn⟩),character hu hn⟩⟩
      linarith
    · have pp := szabo_ap_family_bound N P (subok ((filter_subset ..).trans (filter_subset ..)))
          (fun u hu => (mem_filter.mp hu).2)
      have qq : (Q.card:ℝ)≤S*E := small N sn Q (subok ((filter_subset ..).trans (filter_subset ..))) (by
        intro u hu
        obtain ⟨hm,hn⟩ := mem_filter.mp hu
        exact ⟨hn,character hm hn⟩) common
      have pr : (P.card:ℝ)+Q.card=A.card := by exact_mod_cast pq
      linarith [esc.1,esc.2]
  have ub : ((maxArithInterCard N):ℝ) ≤ (N:ℝ)^2/2+(B+S+M+3)*E := by
    have exists_max : maxArithInterCard N ∈ {#A | (A : Finset (Finset ℕ)) (_ : IsArithInterSet N A)} := by
      apply Nat.sSup_mem
      · exact ⟨0,∅,⟨by simp,by simp⟩,rfl⟩
      · refine ⟨(Icc 1 N).powerset.card,?_⟩
        rintro _ ⟨F,ok,rfl⟩; exact card_le_card ok.1
    obtain ⟨F,hF,e⟩ := exists_max
    exact e ▸ upper F hF
  have lb := SzaboStar.star_bound N on
  rw [Nat.choose_two_right] at lb
  have ll : N*(N-1)≤2*maxArithInterCard N := by omega
  have lr : (N:ℝ)*((N:ℝ)-1)≤2*(maxArithInterCard N:ℝ) := by
    exact_mod_cast (show N*(N-1)≤2*maxArithInterCard N from ll)
  change ‖(maxArithInterCard N:ℝ)-(N:ℝ)^2/2‖ ≤ (B+S+M+3)*‖E‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ep,abs_le]
  constructor <;> linarith [esc.1]
end OMA.R_Erdos272_erdos_272_variants_szabo_R1
