import OMAReductions.R_Erdos1062_erdos_1062_variants_lebensold_bounds_R1

/-!
A finite certificate for Lebensold’s lower bound. Start with the integers in (n/3,n]. For each of 91 disjoint scale ranges, replace part of this interval in sets of the form r times a 5-smooth integer, with r coprime to 30. The certificate records the additions and deletions; the kernel checks all possible multiples of a new member. On multiples of 30000000000 the resulting density is at least 0.6725070096. Monotonicity absorbs the rounding for arbitrary large n.
-/
namespace L1062
open Finset Erdos1062
structure Pattern where
  lo : ℕ
  hi : ℕ
  inc : Finset ℕ
  del : Finset ℕ
deriving DecidableEq

def options (p : Pattern) (a : ℕ) := (Icc 2 5).filter fun k => k*a<p.hi ∧ k*a∉p.del ∧ (p.lo<3*(k*a) ∨ k*a∈p.inc)
abbrev Valid (p : Pattern) : Prop := 0<p.lo ∧ p.lo<p.hi ∧
    ∀ a∈p.inc, 0<a ∧ 3*a ≤ p.lo ∧ p.hi ≤ 6*a ∧ a∣30^12 ∧ (options p a).card ≤ 1

lemma splitRough {r q a b : ℕ} (hr : r.Coprime b) (hq : q.Coprime a) (e : r*a=q*b) : r=q := by
  exact Nat.dvd_antisymm (hr.dvd_of_dvd_mul_right (e ▸ dvd_mul_right r a))
    (hq.dvd_of_dvd_mul_right (e.symm ▸ dvd_mul_right q b))

lemma trade {ι : Type*} [DecidableEq ι] (J : Finset ι) (r : ι → ℕ) (p : ι → Pattern) (n : ℕ)
    (inj : Set.InjOn r (J:Set ι)) (valid : ∀ i∈J, Valid (p i))
    (rough : ∀ i∈J,(r i).Coprime 30) (rpos : ∀ i∈J,0 < r i)
    (band : ∀ i∈J,(p i).lo * r i  ≤  n ∧ n < (p i).hi * r i) :
    n-n/3 + (∑ i∈J,(p i).inc.card)  ≤  f n + ∑ i∈J,(p i).del.card := by
  classical
  let base := Icc (n/3+1) n
  let lift (i : ι) (S : Finset ℕ) := S.image fun t => r i*t
  let A := J.biUnion fun i => lift i (p i).inc
  let D := J.biUnion fun i => lift i (p i).del
  let V := (base ∪ A) \ D
  have sm {i j : ι} (hi : i∈J) (hj : j∈J) {a : ℕ} (ha : a∈(p j).inc) : (r i).Coprime a :=
    Nat.Coprime.of_dvd_right ((valid j hj).2.2 a ha).2.2.2.1 ((rough i hi).pow_right 12)
  have mulinj {i : ι} (hi : i∈J) : Function.Injective (fun a => r i*a) :=
    fun _ _ eq => Nat.eq_of_mul_eq_mul_left (rpos i hi) eq
  have hdis : (J:Set ι).PairwiseDisjoint fun i => lift i (p i).inc := by
    intro i hi j hj hne
    apply disjoint_left.mpr
    intro v hv hw
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
    obtain ⟨b,hb,eq⟩ := mem_image.mp hw
    exact hne (inj hi hj (splitRough (sm hi hj hb) (sm hj hi ha) eq.symm))
  have hA : A.card=∑ i∈J,(p i).inc.card := by
    rw [show A.card=_ from card_biUnion hdis]
    exact sum_congr rfl fun i hi => card_image_of_injective _ (mulinj hi)
  have hD : D.card ≤ ∑ i∈J,(p i).del.card := card_biUnion_le.trans (sum_le_sum (fun _ _ => card_image_le))
  have added {x : ℕ} (hx : x∈A) : ∃ i∈J, ∃ a∈(p i).inc, r i*a=x := by
    obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
    obtain ⟨a,ha,eq⟩ := mem_image.mp hx
    exact ⟨i,hi,a,ha,eq⟩
  have bounds {x : ℕ} (hx : x∈A) : 0<x ∧ 3*x ≤ n ∧ n<6*x := by
    obtain ⟨i,hi,a,ha,rfl⟩ := added hx
    have v := (valid i hi).2.2 a ha
    have h1 := Nat.mul_le_mul_right (r i) v.2.1
    have h2 := Nat.mul_le_mul_right (r i) v.2.2.1
    obtain ⟨h3,h4⟩ := band i hi
    exact ⟨Nat.mul_pos (rpos i hi) v.1,by nlinarith,by nlinarith⟩
  have hBA : Disjoint base A := disjoint_left.mpr (fun x h1 h2 => by
    have := (mem_Icc.mp h1).1
    have := (bounds h2).2.1
    omega)
  have sub : V ⊆ Icc 1 n := by
    intro x hx
    rcases mem_union.mp (mem_sdiff.mp hx).1 with h|h
    · exact mem_Icc.mpr ⟨by have := (mem_Icc.mp h).1; omega,(mem_Icc.mp h).2⟩
    · obtain ⟨h1,h2,_⟩ := bounds h; exact mem_Icc.mpr ⟨h1,by omega⟩
  have fork : ForkFree (V:Set ℕ) := by
    intro x hx y hy z hz
    obtain ⟨⟨hy,hy'⟩,k,rfl⟩ := hy
    obtain ⟨⟨hz,hz'⟩,l,rfl⟩ := hz
    have hxpos := (mem_Icc.mp (sub hx)).1
    have hyN := (mem_Icc.mp (sub hy)).2
    have hzN := (mem_Icc.mp (sub hz)).2
    have small {s : ℕ} (hs : x*s∈V) (hne : x*s∉({x}:Set ℕ)) : 2 ≤ s := by
      by_contra! h
      interval_cases s
      · have := (mem_Icc.mp (sub hs)).1; simp at this
      · simp at hne
    have hk := small hy hy'
    have hl := small hz hz'
    congr 1
    rcases mem_union.mp (mem_sdiff.mp hx).1 with hb|hadd
    · have H := (mem_Icc.mp hb).1
      have h3 : n<3*x := by omega
      have cap {t : ℕ} (h : x*t  ≤  n) : t<3 := by
        by_contra! ht
        have := Nat.mul_le_mul_left x ht; nlinarith
      have := cap hyN; have := cap hzN; omega
    obtain ⟨i,hi,a,ha,eq⟩ := added hadd
    have hx6 := (bounds hadd).2.2
    have member {t : ℕ} (ht : 2 ≤ t) (hmem : x*t∈V) : t∈options (p i) a := by
      have hN := (mem_Icc.mp (sub hmem)).2
      have hp := rpos i hi
      have h5 : t ≤ 5 := by
        by_contra! H; have := Nat.mul_le_mul_left x (show 6 ≤ t by omega); nlinarith
      have hnum : r i*(t*a)=x*t := by rw [←eq]; ring
      obtain ⟨blo,bhi⟩ := band i hi
      have top : t*a<(p i).hi := by
        apply (Nat.mul_lt_mul_right hp).mp
        rw [Nat.mul_comm (t*a),hnum]
        omega
      have exc : t*a∉(p i).del := by
        intro hd
        exact (mem_sdiff.mp hmem).2 (mem_biUnion.mpr ⟨i,hi,mem_image.mpr ⟨t*a,hd,hnum⟩⟩)
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨ht,h5⟩,top,exc,?_⟩
      rcases mem_union.mp (mem_sdiff.mp hmem).1 with H|H
      · left
        have hb := (mem_Icc.mp H).1
        have h3 : n<3*(x*t) := by omega
        apply (Nat.mul_lt_mul_right hp).mp
        calc (p i).lo*r i  ≤  n := blo
             _ < 3*(x*t) := h3
             _ = (3*(t*a))*r i := by rw [←hnum]; ring
      · right
        obtain ⟨j,hj,b,hb,hjv⟩ := added H
        have htD : t ∣ 30^12 := by interval_cases t <;> decide
        have cop := Nat.Coprime.of_dvd_right htD ((rough j hj).pow_right 12)
        have eqr := splitRough (sm hi hj hb) (cop.mul_right (sm hj hi ha)) (hnum.trans hjv.symm)
        have e := inj hi hj eqr
        subst j
        have E := mulinj hi (hnum.trans hjv.symm)
        exact E ▸ hb
    exact card_le_one.mp ((valid i hi).2.2 a ha).2.2.2.2 k (member hk hy) l (member hl hz)
  have hf : V.card ≤ f n := by
    apply Nat.le_findGreatest
    · simpa using card_le_card sub
    · exact ⟨(V:Set ℕ),fun _ h => mem_Icc.mp (sub h),fork,Set.ncard_coe_finset _⟩
  have hdel := le_card_sdiff D (base ∪ A)
  have hsplit : (base∪A).card=base.card+A.card := card_union_of_disjoint hBA
  have hb : base.card=n-n/3 := by simp [base]
  change (base ∪ A).card - D.card  ≤  V.card at hdel
  omega
end L1062


namespace L1062
open Finset Erdos1062
def grid : ℕ := 1000000000
def residues : Finset ℕ := {1,7,11,13,17,19,23,29}
theorem res_spec : ∀ c ∈ residues, 0<c ∧ c<30 ∧ c.Coprime 30 := by decide
def blockCount (p : Pattern) := 8 * (grid/p.lo - (grid/p.hi+1))
def pool (p : Pattern) (k : ℕ) := ((Ico ((grid/p.hi+1)*k) (grid/p.lo*k)) ×ˢ residues).image
    fun v : ℕ × ℕ => 30*v.1+v.2

lemma pool_card (p : Pattern) (k : ℕ) : (pool p k).card = k*blockCount p := by
  have hinj : Set.InjOn (fun v : ℕ × ℕ => 30*v.1+v.2)
      ((Ico ((grid/p.hi+1)*k) (grid/p.lo*k) ×ˢ residues : Finset (ℕ × ℕ)) : Set _) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    have hb := (res_spec _ (mem_product.mp hab).2).2.1
    have hd := (res_spec _ (mem_product.mp hcd).2).2.1
    change 30*a+b=30*c+d at he
    exact Prod.ext (by omega) (by omega)
  rw [pool,card_image_of_injOn hinj,card_product,Nat.card_Ico,show residues.card=8 by decide,←Nat.sub_mul]
  unfold blockCount
  ring

lemma pool_spec {p : Pattern} (hv : Valid p) {k r : ℕ} (hk : 0<k) (hr : r∈pool p k) :
    0<r ∧ r.Coprime 30 ∧ p.lo*r ≤ 30*grid*k ∧ 30*grid*k < p.hi*r := by
  obtain ⟨⟨j,c⟩,hm,rfl⟩ := mem_image.mp hr
  obtain ⟨hj,hc⟩ := mem_product.mp hm
  obtain ⟨hj1,hj2⟩ := mem_Ico.mp hj
  obtain ⟨h0,hc',hcop⟩ := res_spec c hc
  dsimp only at *
  refine ⟨by omega, by simpa using hcop,?_,?_⟩
  · have upper : 30*j+c ≤ 30*(grid/p.lo*k) := by omega
    have H := Nat.mul_le_mul_left p.lo upper
    have H' := Nat.mul_le_mul_right (30*k) (Nat.div_mul_le_self grid p.lo)
    nlinarith only [H,H']
  · have hhi := hv.1.trans hv.2.1
    have base := Nat.lt_mul_div_succ grid hhi
    have H := Nat.mul_lt_mul_of_pos_right base (Nat.mul_pos (by decide : 0<30) hk)
    have H' := Nat.mul_le_mul_left (30*p.hi) hj1
    nlinarith only [H,H',Nat.zero_le (p.hi*c)]

lemma grid_bound (tab : List Pattern) (valid : ∀ p∈tab, Valid p)
    (hsort : tab.Pairwise (fun p q => p.hi ≤ q.lo)) (k : ℕ) (hk : 0<k) :
    20*grid*k + k*(tab.map (fun p => blockCount p*p.inc.card)).sum ≤
    f (30*grid*k) + k*(tab.map (fun p => blockCount p*p.del.card)).sum := by
  classical
  let p (i : Fin tab.length) := tab.get i
  let J := univ.sigma (fun i => pool (p i) k)
  have hv (i : Fin tab.length) := valid (p i) (List.get_mem ..)
  have hsp {z : (i : Fin tab.length) × ℕ} (hz : z∈J) :=
    pool_spec (hv z.1) hk (mem_sigma.mp hz).2
  have hlt (i j : Fin tab.length) (hij : i<j) : (p i).hi ≤ (p j).lo :=
    (List.pairwise_iff_getElem.mp hsort) _ _ i.isLt j.isLt hij
  have hinj : Set.InjOn (fun z : (i : Fin tab.length) × ℕ => z.2) (J : Set _) := by
    rintro ⟨i,r⟩ hi ⟨j,s⟩ hj eq
    change r=s at eq; subst s
    have ha := (hsp hi).2.2
    have hb := (hsp hj).2.2
    rcases lt_trichotomy i j with h|h|h
    · have H := Nat.mul_le_mul_right r (hlt i j h)
      change (p i).lo*r ≤ _ ∧ _ < (p i).hi*r at ha
      change (p j).lo*r ≤ _ ∧ _ < (p j).hi*r at hb
      omega
    · subst j; rfl
    · have H := Nat.mul_le_mul_right r (hlt j i h)
      change (p i).lo*r ≤ _ ∧ _ < (p i).hi*r at ha
      change (p j).lo*r ≤ _ ∧ _ < (p j).hi*r at hb
      omega
  have H := trade J (fun z => z.2) (fun z => p z.1) (30*grid*k) hinj (fun z _ => hv z.1)
    (fun _ hz => (hsp hz).2.1) (fun _ hz => (hsp hz).1) (fun _ hz => (hsp hz).2.2)
  have mass (size : Pattern → ℕ) : (∑ z∈J,size (p z.1)) = k*(tab.map (fun t => blockCount t*size t)).sum := by
    simp only [J,sum_sigma,sum_const,nsmul_eq_mul,pool_card,Nat.cast_id,mul_assoc,←mul_sum]
    congr 1
    rw [←List.sum_ofFn]
    congr 1
    apply List.ext_getElem <;> simp [p]
  rw [mass (fun t => t.inc.card),mass (fun t => t.del.card)] at H
  change 20000000000*k+_ ≤ _+_
  change 30000000000*k-(30000000000*k)/3+_ ≤ _+_ at H
  omega
end L1062


namespace L1062
open Finset
def table : List Pattern := [⟨27,30,{6,8,9},{18,24}⟩,
  ⟨30,32,{6,8,9,10},{18,24,30}⟩,
  ⟨54,60,{12,15,16,18},{30,36,48}⟩,
  ⟨60,64,{12,16,18,20},{36,48,60}⟩,
  ⟨81,90,{18,24,25,27},{54,72,75}⟩,
  ⟨90,96,{18,24,27,30},{54,72,90}⟩,
  ⟨96,100,{18,24,27,30,32},{54,72,90,96}⟩,
  ⟨100,108,{18,24,27,30,32},{54,72,90,96}⟩,
  ⟨108,120,{24,30,32,36},{60,72,96}⟩,
  ⟨120,125,{24,32,36,40},{72,96,120}⟩,
  ⟨125,128,{24,32,36,40},{72,96,120}⟩,
  ⟨135,144,{30,36,40,45},{72,90,120}⟩,
  ⟨144,150,{30,40,45,48},{90,120,144}⟩,
  ⟨150,160,{30,40,45,48,50},{90,120,144,150}⟩,
  ⟨162,180,{30,36,45,48,50,54},{90,108,120,144,150}⟩,
  ⟨180,192,{36,48,54,60},{108,144,180}⟩,
  ⟨192,200,{36,48,54,60,64},{108,144,180,192}⟩,
  ⟨200,216,{36,48,54,60,64},{108,144,180,192}⟩,
  ⟨216,225,{48,60,64,72},{144,180,192}⟩,
  ⟨225,240,{48,60,64,72,75},{144,150,180,192}⟩,
  ⟨240,243,{48,60,64,72,75,80},{144,150,180,192,240}⟩,
  ⟨243,250,{48,54,60,64,72,75,80,81},{144,150,162,180,192,216,240}⟩,
  ⟨250,256,{48,54,60,64,72,75,80,81},{144,150,162,180,192,216,240}⟩,
  ⟨256,270,{54,60,72,75,80,81},{150,162,180,216,240}⟩,
  ⟨270,288,{60,72,75,80,81,90},{150,162,180,216,240}⟩,
  ⟨288,300,{60,75,80,81,90,96},{150,162,180,240,288}⟩,
  ⟨300,320,{60,80,81,90,96,100},{162,180,240,288,300}⟩,
  ⟨320,324,{54,72,81,90,96,100},{162,216,270,288,300}⟩,
  ⟨324,360,{60,72,90,96,100,108},{180,216,240,288,300}⟩,
  ⟨360,375,{72,96,100,108,120},{216,288,300,360}⟩,
  ⟨375,384,{72,96,100,108,120,125},{216,288,300,360,375}⟩,
  ⟨384,400,{72,96,100,108,120,125,128},{216,288,300,360,375,384}⟩,
  ⟨400,405,{72,96,108,120,125,128},{216,288,360,375,384}⟩,
  ⟨405,432,{72,90,96,108,120,125,128,135},{216,270,288,360,375,384}⟩,
  ⟨432,450,{90,96,120,125,128,135,144},{270,288,360,375,384}⟩,
  ⟨450,480,{90,96,120,128,135,144,150},{270,288,360,384,450}⟩,
  ⟨480,486,{90,96,120,128,135,144,150,160},{270,288,360,384,450,480}⟩,
  ⟨486,500,{90,96,108,120,128,135,144,150,160,162},{270,288,324,360,384,432,450,480}⟩,
  ⟨500,512,{90,96,108,120,128,135,144,150,160,162},{270,288,324,360,384,432,450,480}⟩,
  ⟨512,540,{90,108,120,135,144,150,160,162},{270,324,360,432,450,480}⟩,
  ⟨540,576,{120,144,150,160,162,180},{300,324,360,432,480}⟩,
  ⟨576,600,{120,150,160,162,180,192},{300,324,360,480,576}⟩,
  ⟨600,625,{120,160,162,180,192,200},{324,360,480,576,600}⟩,
  ⟨625,640,{120,160,162,180,192,200},{324,360,480,576,600}⟩,
  ⟨640,648,{108,144,162,180,192,200},{324,432,540,576,600}⟩,
  ⟨648,675,{144,180,192,200,216},{360,432,576,600}⟩,
  ⟨675,720,{144,150,180,192,200,216,225},{360,432,450,576,600}⟩,
  ⟨720,729,{144,150,192,200,216,225,240},{432,450,576,600,720}⟩,
  ⟨729,750,{150,162,192,200,216,225,240,243},{450,486,576,600,648,720}⟩,
  ⟨750,768,{150,162,192,200,216,225,240,243,250},{450,486,576,600,648,720,750}⟩,
  ⟨768,800,{150,162,192,200,216,225,240,243,250,256},{450,486,576,600,648,720,750,768}⟩,
  ⟨800,810,{162,192,216,225,240,243,250,256},{450,486,576,648,720,750,768}⟩,
  ⟨810,864,{144,150,180,192,216,225,240,243,250,256,270},{432,450,486,540,576,600,720,750,768}⟩,
  ⟨864,900,{150,180,192,225,240,243,250,256,270,288},{450,486,540,576,600,720,750,768}⟩,
  ⟨900,960,{180,192,240,243,256,270,288,300},{486,540,576,720,768,900}⟩,
  ⟨960,972,{180,192,240,243,256,270,288,300,320},{486,540,576,720,768,900,960}⟩,
  ⟨972,1000,{180,192,240,256,270,288,300,320,324},{540,576,648,720,768,900,960}⟩,
  ⟨1000,1024,{180,192,240,256,270,288,300,320,324},{540,576,648,720,768,900,960}⟩,
  ⟨1024,1080,{180,216,240,270,288,300,320,324},{540,648,720,864,900,960}⟩,
  ⟨1080,1125,{240,288,300,320,324,360},{648,720,864,900,960}⟩,
  ⟨1125,1152,{240,288,300,320,324,360,375},{648,720,750,864,900,960}⟩,
  ⟨1152,1200,{240,300,320,324,360,375,384},{648,720,750,900,960,1152}⟩,
  ⟨1200,1215,{240,300,320,324,360,375,384,400},{648,720,750,900,960,1152,1200}⟩,
  ⟨1215,1250,{216,240,270,288,300,320,324,360,375,384,400,405},{648,720,750,810,864,900,960,1080,1152,1200}⟩,
  ⟨1250,1280,{216,240,270,288,300,320,324,360,375,384,400,405},{648,720,750,810,864,900,960,1080,1152,1200}⟩,
  ⟨1280,1296,{216,270,288,300,324,360,375,384,400,405},{648,750,810,864,900,1080,1152,1200}⟩,
  ⟨1296,1350,{270,288,300,360,375,384,400,405,432},{750,810,864,900,1080,1152,1200}⟩,
  ⟨1350,1440,{288,300,360,375,384,400,405,432,450},{720,750,810,864,900,1152,1200}⟩,
  ⟨1440,1458,{288,300,375,384,400,405,432,450,480},{750,810,864,900,1152,1200,1440}⟩,
  ⟨1458,1500,{300,324,375,384,400,405,432,450,480,486},{750,810,900,972,1152,1200,1296,1440}⟩,
  ⟨1500,1536,{300,324,384,400,405,432,450,480,486,500},{810,900,972,1152,1200,1296,1440,1500}⟩,
  ⟨1536,1600,{300,324,384,400,405,432,450,480,486,500,512},{810,900,972,1152,1200,1296,1440,1500,1536}⟩,
  ⟨1600,1620,{270,324,360,384,405,432,450,480,486,500,512},{810,972,1080,1152,1296,1350,1440,1500,1536}⟩,
  ⟨1620,1728,{288,300,360,384,432,450,480,486,500,512,540},{864,900,972,1080,1152,1200,1440,1500,1536}⟩,
  ⟨1728,1800,{300,360,384,450,480,486,500,512,540,576},{900,972,1080,1152,1200,1440,1500,1536}⟩,
  ⟨1800,1875,{360,384,480,486,500,512,540,576,600},{972,1080,1152,1440,1500,1536,1800}⟩,
  ⟨1875,1920,{360,384,480,486,500,512,540,576,600,625},{972,1080,1152,1440,1500,1536,1800,1875}⟩,
  ⟨1920,1944,{360,384,480,486,500,512,540,576,600,625,640},{972,1080,1152,1440,1500,1536,1800,1875,1920}⟩,
  ⟨1944,2000,{360,384,480,500,512,540,576,600,625,640,648},{1080,1152,1296,1440,1500,1536,1800,1875,1920}⟩,
  ⟨2000,2025,{360,384,480,512,540,576,600,625,640,648},{1080,1152,1296,1440,1536,1800,1875,1920}⟩,
  ⟨2025,2048,{360,384,450,480,512,540,576,600,625,640,648,675},{1080,1152,1296,1350,1440,1536,1800,1875,1920}⟩,
  ⟨2048,2160,{360,432,450,480,540,576,600,625,640,648,675},{1080,1296,1350,1440,1728,1800,1875,1920}⟩,
  ⟨2160,2187,{450,480,576,600,625,640,648,675,720},{1296,1350,1440,1728,1800,1875,1920}⟩,
  ⟨2187,2250,{450,480,486,576,600,625,640,648,675,720,729},{1350,1440,1458,1728,1800,1875,1920,1944}⟩,
  ⟨2250,2304,{450,480,486,576,600,640,648,675,720,729,750},{1350,1440,1458,1728,1800,1920,1944,2250}⟩,
  ⟨2304,2400,{450,480,486,600,640,648,675,720,729,750,768},{1350,1440,1458,1800,1920,1944,2250,2304}⟩,
  ⟨2400,2430,{450,480,486,600,640,648,675,720,729,750,768,800},{1350,1440,1458,1800,1920,1944,2250,2304,2400}⟩,
  ⟨2430,2500,{432,450,480,540,576,600,640,648,675,720,729,750,768,800,810},{1296,1350,1440,1458,1620,1728,1800,1920,2160,2250,2304,2400}⟩,
  ⟨2500,2560,{432,450,480,540,576,600,640,648,675,720,729,750,768,800,810},{1296,1350,1440,1458,1620,1728,1800,1920,2160,2250,2304,2400}⟩,
  ⟨2560,2592,{432,450,540,576,600,648,675,720,729,750,768,800,810},{1296,1350,1458,1620,1728,1800,2160,2250,2304,2400}⟩,
  ⟨2592,2700,{450,540,576,600,675,720,729,750,768,800,810,864},{1350,1458,1620,1728,1800,2160,2250,2304,2400}⟩]
theorem allvalid : ∀ p∈table, Valid p := by decide +kernel
theorem sorted_table : table.Pairwise (fun p q => p.hi ≤ q.lo) := by decide +kernel
theorem total_table : (table.map (fun p => blockCount p * p.inc.card)).sum ≥ (table.map (fun p => blockCount p * p.del.card)).sum + 175210288 := by decide +kernel
end L1062

namespace L1062
open Filter Finset Erdos1062
lemma mono_f : Monotone f := by
  classical
  intro n m h
  have spec : ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard=f n := by
    apply Nat.findGreatest_spec (P:=fun k => ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard=k) (m:=0) (Nat.zero_le n)
    exact ⟨∅,Set.empty_subset _,by simp [ForkFree],by simp⟩
  obtain ⟨A,hA,hf,hc⟩ := spec
  apply Nat.le_findGreatest ((Nat.findGreatest_le _).trans h)
  exact ⟨A,hA.trans (Set.Icc_subset_Icc_right h),hf,hc⟩

theorem lower : ∀ᶠ n : ℕ in atTop, (0.6725 : ℝ)*n ≤ f n := by
  filter_upwards [eventually_ge_atTop (30000000000*100000 : ℕ)] with n hn
  let k := n/30000000000
  have hk : 100000 ≤ k := by dsimp [k]; omega
  have H := grid_bound table allvalid sorted_table k (by omega)
  have eff := Nat.mul_le_mul_left k total_table
  rw [Nat.mul_add] at eff
  change 20000000000*k+_ ≤ f (30000000000*k)+_ at H
  have H' := mono_f (show 30000000000*k ≤ n by dsimp [k]; omega)
  have Hn : n<30000000000*(k+1) := by dsimp [k]; omega
  have hnat : 6725*n ≤ 10000*f n := by omega
  have hreal : (6725:ℝ)*n ≤ 10000*f n := by exact_mod_cast hnat
  linarith
end L1062


theorem OMA.solution : OMA.R_Erdos1062_erdos_1062_variants_lebensold_bounds_R1.H1 := L1062.lower
