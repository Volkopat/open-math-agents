import OMAStatements.S_oeis_a008793

/-!
# The MacMahon box supercongruence

Group the product by antidiagonals and remove the factors divisible by p.
Pairing the remaining indices gives a product with a quadratic increment.
Its linear term is a harmonic sum. Reflection and multiplication by two
on the invertible residue classes eliminate that term for odd primes.
For the prime two, the missing divisibility comes from the box count at
the previous scale. Legendre's factorial formula proves both integrality
and the required lower bound for that count.
-/

namespace BoxPartition
open Finset
open OMA.S_oeis_a008793

def wt (N x : ℕ) := min x (2*N-x)

lemma fiber_size (N x : ℕ) (hx : x ∈ Ico 1 (2*N)) :
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun ij : ℕ×ℕ => ij.1+ij.2-1=x)).card = wt N x := by
  let a := max 1 (x+1-N)
  let b := min N x
  have card : (((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun ij : ℕ×ℕ => ij.1+ij.2-1=x)).card =
      (Icc a b).card := by
    apply card_bij (fun ij _ => ij.1)
    · intro ij hij
      simp only [mem_filter,mem_product,mem_Icc] at hij
      simp only [mem_Icc,a,b]; omega
    · rintro ⟨i,j⟩ hij ⟨i',j'⟩ hij' h
      simp only [mem_filter,mem_product,mem_Icc] at hij hij'
      simp only [Prod.mk.injEq]
      dsimp at *
      omega
    · intro i hi
      simp only [mem_Icc,a,b] at hi
      refine ⟨(i,x+1-i),?_,rfl⟩
      simp only [mem_filter,mem_product,mem_Icc]
      omega
  rw [card,Nat.card_Icc]
  have := mem_Ico.mp hx
  dsimp [a,b,wt]; omega

def term (N x : ℕ) : ℚ := ((N+x:ℕ):ℚ)/x

lemma box_grouped (N : ℕ) : a N = ∏ x ∈ Ico 1 (2*N), term N x ^ wt N x := by
  let S := (Icc 1 N) ×ˢ (Icc 1 N)
  let f := fun ij : ℕ×ℕ => ij.1+ij.2-1
  have hmap (ij : ℕ×ℕ) (h : ij∈S) : f ij ∈ Ico 1 (2*N) := by
    simp only [S,mem_product,mem_Icc] at h
    simp only [f,mem_Ico]; omega
  unfold a
  rw [← prod_product']
  calc
    _ = ∏ ij ∈ S, term N (f ij) := by
      apply prod_congr rfl
      rintro ⟨i,j⟩ h
      simp only [S,mem_product,mem_Icc] at h
      unfold term f
      congr 2 <;> omega
    _ = ∏ x ∈ Ico 1 (2*N), ∏ ij ∈ S with f ij=x, term N (f ij) :=
      (prod_fiberwise_of_maps_to hmap _).symm
    _ = _ := by
      apply prod_congr rfl
      intro x hx
      calc
        _ = ∏ _ij ∈ S with f _ij=x, term N x := by
          apply prod_congr rfl
          intro ij h
          rw [(mem_filter.mp h).2]
        _ = _ := by rw [prod_const,fiber_size N x hx]

end BoxPartition

/-! Pairing the factors outside the smaller box. -/

namespace BoxPartition
open Finset OMA.S_oeis_a008793

def small (p N : ℕ) := (Ico 1 N).filter (fun x => ¬p∣x)

def inc (N x : ℕ) : ℚ := 3*(N:ℚ)^2/((x:ℚ)*(2*(N:ℚ)-x))

def residual (p N : ℕ) : ℚ := ∏ x ∈ small p N, (1+inc N x)^x

lemma term_pair {N x : ℕ} (hx : x ∈ Ico 1 N) :
    term N x * term N (2*N-x) = 1+inc N x := by
  obtain ⟨xl,xh⟩ := mem_Ico.mp hx
  unfold term inc
  have hl : x ≤ 2*N := by omega
  push_cast [Nat.cast_sub hl]
  have h1 : (x:ℚ) ≠ 0 := by positivity
  have h2 : 2*(N:ℚ)-x ≠ 0 := by
    apply ne_of_gt; apply sub_pos.mpr; exact_mod_cast (show x<2*N by omega)
  have h3 : (N:ℚ)*2-x≠0 := by rwa [mul_comm (N:ℚ) 2]
  field_simp [h1,h2,h3]
  ring

lemma scale_wt {p M x : ℕ} : wt (p*M) (p*x)=p*wt M x := by
  unfold wt
  rw [show 2*(p*M)=p*(2*M) by ring,← Nat.mul_sub]
  by_cases h : x ≤ 2*M-x
  · rw [min_eq_left h,min_eq_left (Nat.mul_le_mul_left _ h)]
  · rw [min_eq_right (le_of_not_ge h),min_eq_right (Nat.mul_le_mul_left _ (le_of_not_ge h))]

lemma main_split {p M : ℕ} (hp : 0 < p) (hm : 0 < M) :
    a (p*M)=a M^p * residual p (p*M) := by
  let N := p*M
  let r := Ico 1 (2*N)
  let mult := r.filter (fun x => p∣x)
  let rest := r.filter (fun x => ¬p∣x)
  let weight := fun x => term N x ^ wt N x
  have pos : 0<N := Nat.mul_pos hp hm
  have part : (∏ x ∈ mult,weight x)*(∏ x ∈ rest,weight x)=a N := by
    rw [box_grouped]
    exact prod_filter_mul_prod_filter_not .. 
  have left : (∏ x ∈ mult,weight x)=a M^p := by
    rw [box_grouped,← Finset.prod_pow]
    symm
    apply prod_bij (fun x _ => p*x)
    · intro x hx
      have h := mem_Ico.mp hx
      simp only [mult,r,mem_filter,mem_Ico,N]
      exact ⟨⟨by nlinarith [Nat.mul_pos hp h.1],by simpa only [mul_left_comm] using Nat.mul_lt_mul_of_pos_left h.2 hp⟩,dvd_mul_right _ _⟩
    · intro x hx y hy h
      exact Nat.eq_of_mul_eq_mul_left hp h
    · intro x hx
      obtain ⟨hr,k,hk⟩ := mem_filter.mp hx
      obtain ⟨lo,hi⟩ := mem_Ico.mp hr
      refine ⟨k,mem_Ico.mpr ⟨?_,?_⟩,hk.symm⟩
      · by_contra! h; have : k=0 := by omega
        simp [this] at hk; omega
      · dsimp [N] at hi
        rw [hk,mul_left_comm] at hi
        exact Nat.lt_of_mul_lt_mul_left hi
    · intro x hx
      dsimp [weight,N]
      rw [scale_wt,← pow_mul, mul_comm p]
      congr 1
      unfold term
      push_cast
      field_simp [show (p:ℚ) ≠ 0 by positivity]
      ring
  let lower := small p N
  let upper := rest.filter (fun x => ¬x<N)
  have decomp : (∏ x ∈ lower,weight x)*(∏ x ∈ upper,weight x) = ∏ x ∈ rest,weight x := by
    have eq : rest.filter (fun x => x<N) = lower := by
      ext x; simp only [rest,r,lower,small,mem_filter,mem_Ico]; omega
    rw [← eq]; exact prod_filter_mul_prod_filter_not ..
  have rev : (∏ x ∈ upper,weight x) = ∏ x ∈ lower,weight (2*N-x) := by
    symm
    apply prod_bij (fun x _ => 2*N-x)
    · intro x hx
      change x ∈ (Ico 1 N).filter (fun k => ¬p∣k) at hx
      obtain ⟨hr,xf⟩ := mem_filter.mp hx
      obtain ⟨xl,xh⟩ := mem_Ico.mp hr
      have multN : p∣2*N := ⟨2*M,by dsimp [N]; ring⟩
      simp only [upper,rest,r,mem_filter,mem_Ico]
      refine ⟨⟨⟨by omega,by omega⟩,?_⟩,by omega⟩
      intro hd
      have hback := Nat.dvd_sub multN hd
      rw [show 2*N-(2*N-x)=x by omega] at hback
      exact xf hback
    · intro x hx y hy eq
      have hx' := mem_Ico.mp (mem_filter.mp hx).1
      have hy' := mem_Ico.mp (mem_filter.mp hy).1
      omega
    · intro x hx
      simp only [upper,rest,r,mem_filter,mem_Ico] at hx
      obtain ⟨⟨hr',hd⟩,high⟩ := hx
      have xn : x≠N := by rintro rfl; exact hd (dvd_mul_right _ _)
      have multN : p∣2*N := ⟨2*M,by dsimp [N]; ring⟩
      refine ⟨2*N-x,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩
      intro hd'
      have hback := Nat.dvd_sub multN hd'
      rw [show 2*N-(2*N-x)=x by omega] at hback
      exact hd hback
    · intros; rfl
  change a N=_
  rw [← part,left,← decomp,rev,← prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro x hx
  have hx' := mem_Ico.mp (mem_filter.mp hx).1
  have lo : wt N x=x := by unfold wt; omega
  have hi : wt N (2*N-x)=x := by unfold wt; omega
  dsimp [weight]; rw [lo,hi,←mul_pow,term_pair (mem_filter.mp hx).1]

end BoxPartition

/-! Rationals with denominator prime to p, and a first-order product expansion. -/

namespace BoxPartition
open Finset

def localRing (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {q | ∃ a : ℤ, ∃ b : ℕ, ¬p∣b ∧ q*b=a}
  zero_mem' := ⟨0,1,(Fact.out : p.Prime).not_dvd_one,by simp⟩
  one_mem' := ⟨1,1,(Fact.out : p.Prime).not_dvd_one,by simp⟩
  add_mem' := by
    rintro x y ⟨a,b,hb,he⟩ ⟨c,d,hd,hf⟩
    refine ⟨a*d+c*b,b*d,fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd,?_⟩
    push_cast
    linear_combination (d:ℚ)*he+(b:ℚ)*hf
  mul_mem' := by
    rintro x y ⟨a,b,hb,he⟩ ⟨c,d,hd,hf⟩
    refine ⟨a*c,b*d,fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd,?_⟩
    push_cast
    linear_combination (y*(d:ℚ))*he+(a:ℚ)*hf
  neg_mem' := by
    rintro x ⟨a,b,hb,h⟩
    exact ⟨-a,b,hb,by push_cast; linarith⟩

lemma linv {p : ℕ} [Fact p.Prime] (x : ℕ) (hx : ¬p∣x) : (x:ℚ)⁻¹ ∈ localRing p := by
  have hn : x≠0 := by rintro rfl; simp at hx
  exact ⟨1,x,hx,by simp [hn]⟩

lemma int_from_local {p : ℕ} [Fact p.Prime] {m : ℤ} {k : ℕ} {u : ℚ}
    (hu : u∈localRing p) (hm : (m:ℚ)=(p:ℚ)^k*u) : (p:ℤ)^k ∣ m := by
  obtain ⟨a,b,hb,he⟩ := hu
  have h : (p:ℤ)^k∣m*(b:ℤ) := by
    refine ⟨a,?_⟩
    exact_mod_cast (show (m:ℚ)*b=(p:ℚ)^k*a by rw [hm,mul_assoc,he])
  have cop : IsCoprime ((p:ℤ)^k) (b:ℤ) := by
    exact (Nat.Coprime.isCoprime ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hb)).pow_left
  exact cop.dvd_of_dvd_mul_right h

lemma first_power {R : Type*} [CommRing R] (z v : R) (k : ℕ) :
    z^2 ∣ (1+z*v)^k-1-z*(k:R)*v := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨u,hu⟩ := ih
    refine ⟨u*(1+z*v)+(k:R)*v^2,?_⟩
    rw [pow_succ]; push_cast
    linear_combination (1+z*v)*hu

lemma first_product {R ι : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (z : R) (v : ι → R) (k : ι → ℕ) :
    z^2 ∣ (∏ x ∈ s, (1+z*v x)^(k x))-1-z*∑ x ∈ s,(k x:R)*v x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨a,ha⟩ := first_power z (v i) (k i)
    obtain ⟨b,hb⟩ := ih
    rw [prod_insert hi,sum_insert hi]
    let w := ∑ x ∈ s,(k x:R)*v x
    let e := ∏ x ∈ s,(1+z*v x)^(k x)
    change e-1-z*w=z^2*b at hb
    change z^2 ∣ (1+z*v i)^(k i)*e-1-z*((k i:R)*v i+w)
    refine ⟨a*e+b+((k i:R)*v i)*(w+z*b),?_⟩
    linear_combination e*ha+(1+z*(k i:R)*v i)*hb

end BoxPartition

/-! Reduction of these rationals modulo a prime power. -/

namespace BoxPartition
variable {p r : ℕ} [Fact p.Prime]

private lemma reduce_exists (hr : 0<r) (x : localRing p) :
    ∃ z : ZMod (p^r), ∀ (a : ℤ) (b : ℕ), ¬p∣b → (x:ℚ)*b=a → z*b=a := by
  obtain ⟨a,b,hb,he⟩ := x.property
  have ub := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hb
  refine ⟨(a:ZMod (p^r))*(b:ZMod (p^r))⁻¹,?_⟩
  intro c d hd hf
  have eq : a*(d:ℤ)=c*(b:ℤ) := by
    exact_mod_cast (show (a:ℚ)*d=(c:ℚ)*b by rw [← he,← hf]; ring)
  have eq' := congrArg (fun t : ℤ => (t : ZMod (p^r))) eq
  push_cast at eq'
  have bi := ZMod.mul_inv_of_unit _ ub
  linear_combination (b:ZMod (p^r))⁻¹*eq'+(c:ZMod (p^r))*bi

noncomputable def red (hr : 0<r) (x : localRing p) := (reduce_exists hr x).choose

lemma red_spec (hr : 0<r) (x : localRing p) (a : ℤ) (b : ℕ) (hb : ¬p∣b)
    (he : (x:ℚ)*b=a) : red hr x*b=a := (reduce_exists hr x).choose_spec a b hb he

noncomputable def reduce (hr : 0<r) : localRing p →+* ZMod (p^r) where
  toFun := red hr
  map_zero' := by simpa using red_spec (p:=p) hr 0 0 1 (Fact.out : p.Prime).not_dvd_one (by simp)
  map_one' := by simpa using red_spec (p:=p) hr 1 1 1 (Fact.out : p.Prime).not_dvd_one (by simp)
  map_add' := by
    intro x y
    obtain ⟨a,b,hb,he⟩ := x.property
    obtain ⟨c,d,hd,hf⟩ := y.property
    have hbd : ¬p∣b*d := fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd
    have hz := red_spec hr (x+y) (a*d+c*b) (b*d) hbd (by push_cast; linear_combination (d:ℚ)*he+(b:ℚ)*hf)
    have hx := red_spec hr x a b hb he
    have hy := red_spec hr y c d hd hf
    apply ((ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hbd).mul_left_inj.mp
    push_cast at hz ⊢
    linear_combination hz-(d:ZMod (p^r))*hx-(b:ZMod (p^r))*hy
  map_mul' := by
    intro x y
    obtain ⟨a,b,hb,he⟩ := x.property
    obtain ⟨c,d,hd,hf⟩ := y.property
    have hbd : ¬p∣b*d := fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd
    have hz := red_spec hr (x*y) (a*c) (b*d) hbd (by push_cast; linear_combination (y.val*(d:ℚ))*he+(a:ℚ)*hf)
    have hx := red_spec hr x a b hb he
    have hy := red_spec hr y c d hd hf
    apply ((ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hbd).mul_left_inj.mp
    push_cast at hz ⊢
    linear_combination hz-(red hr y*(d:ZMod (p^r)))*hx-(a:ZMod (p^r))*hy

lemma ker_reduce (hr : 0<r) (x : localRing p) (h : reduce hr x=0) : (p:localRing p)^r ∣ x := by
  obtain ⟨a,b,hb,he⟩ := x.property
  have hz := red_spec hr x a b hb he
  change red hr x = 0 at h
  rw [h,zero_mul] at hz
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz.symm
  let inv : localRing p := ⟨(b:ℚ)⁻¹,linv b hb⟩
  have bn : b≠0 := by rintro rfl; simp at hb
  refine ⟨(k:localRing p)*inv,Subtype.ext ?_⟩
  change (x:ℚ)=(p:ℚ)^r*((k:ℚ)*(b:ℚ)⁻¹)
  field_simp [bn]
  have hq := congrArg (fun t : ℤ => (t:ℚ)) hk
  push_cast at hq
  linear_combination he+hq

noncomputable def invNat (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : ¬p∣k) : localRing p :=
  ⟨(k:ℚ)⁻¹,linv k hk⟩

lemma red_inv (hr : 0<r) (k : ℕ) (hk : ¬p∣k) : reduce hr (invNat p k hk)=(k:ZMod (p^r))⁻¹ := by
  have hn : k≠0 := by rintro rfl; simp at hk
  have he := red_spec hr (invNat p k hk) 1 k hk (by simp [invNat,hn])
  have un := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hk
  change red hr _ = _
  apply un.mul_left_inj.mp
  simpa only [ZMod.inv_mul_of_unit _ un,Int.cast_one] using he

end BoxPartition

/-! Inverse-square sums over complete blocks of residues. -/

namespace BoxPartition
open Finset
variable {p r : ℕ} [Fact p.Prime]

noncomputable def safe (p : ℕ) [Fact p.Prime] (x : ℕ) : localRing p :=
  if h : ¬p∣x then invNat p x h else 0

lemma safe_inv (x : ℕ) (h : ¬p∣x) : (x:localRing p)*safe p x = 1 := by
  have nz : x≠0 := by rintro rfl; simp at h
  apply Subtype.ext
  simp [safe,h,invNat,nz]

noncomputable def invSq (P : ℕ) (z : ZMod P) : ZMod P := by classical exact if IsUnit z then z⁻¹^2 else 0

lemma three_sum_zero (modulus : ℕ) [NeZero modulus] (htwo : IsUnit (2 : ZMod modulus)) :
    3*(∑ z : ZMod modulus, invSq modulus z)=0 := by
  classical
  let u := htwo.unit
  have ue : (u:ZMod modulus)=2 := htwo.unit_spec
  have perm := Equiv.sum_comp u.mulLeft (invSq modulus)
  have point (z : ZMod modulus) : 4*invSq modulus (u.mulLeft z)=invSq modulus z := by
    change 4*invSq modulus ((u:ZMod modulus)*z)=_
    rw [ue]
    by_cases hz : IsUnit z
    · simp only [invSq,if_pos hz,if_pos (htwo.mul hz)]
      have a := ZMod.mul_inv_of_unit _ (htwo.mul hz)
      have b := ZMod.mul_inv_of_unit _ hz
      have he : 2*((2:ZMod modulus)*z)⁻¹=z⁻¹ := by
        apply hz.mul_left_inj.mp
        linear_combination a-b
      calc
        4*((2:ZMod modulus)*z)⁻¹^2=(2*((2:ZMod modulus)*z)⁻¹)^2 := by ring
        _ = _ := by rw [he]
    · have bad : ¬ IsUnit ((2:ZMod modulus)*z) := fun h => hz (isUnit_of_mul_isUnit_right h)
      simp [invSq,hz,bad]
  have hs : 4*(∑ z : ZMod modulus, invSq modulus z)=(∑ z : ZMod modulus, invSq modulus z) := by
    conv_lhs => rw [← perm,Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => point z
  linear_combination hs

lemma periodic_sum {P : ℕ} [NeZero P] (hP : 0<P) (n : ℕ) (f : ZMod P → ZMod P) :
    (∑ x ∈ range (n*P), f x)=(n:ZMod P)*∑ z : ZMod P, f z := by
  have block : (∑ x ∈ range P, f x)=∑ z : ZMod P, f z := by
    cases P with
    | zero => omega
    | succ P =>
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro i hi
      congr 1
      exact ZMod.natCast_zmod_val (n:=P+1) (show ZMod (P+1) from i)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,sum_range_add,ih]
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_add,block,Nat.cast_succ]
    ring

lemma three_square_local (r N : ℕ) (hr : 0<r) (hN : p^r∣N) (hodd : p≠2) :
    (p:localRing p)^r ∣ 3*(∑ x ∈ range N, (safe p x)^2) := by
  apply ker_reduce hr
  let P := p^r
  have hP : 0<P := pow_pos (Fact.out : p.Prime).pos _
  let _ : NeZero P := ⟨hP.ne'⟩
  have nd2 : ¬p∣2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with bad|bad
    · exact (Fact.out : p.Prime).ne_one bad
    · exact hodd bad
  have hu : IsUnit (2:ZMod P) := by
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr nd2
  have each (x : ℕ) : reduce hr (safe p x)^2=invSq P x := by
    by_cases hx : p∣x
    · have bad := mt (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mp (not_not.mpr hx)
      simp [safe,hx,invSq,P,bad]
    · have good := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hx
      simp [safe,hx,red_inv,invSq,P,good]
  obtain ⟨n,hn⟩ := hN
  simp only [map_mul,map_ofNat,map_sum,map_pow,each]
  have he : N=n*P := by simpa only [P,mul_comm] using hn
  rw [he,periodic_sum hP]
  linear_combination (n:ZMod P)*three_sum_zero P hu

end BoxPartition

/-! Reflection of the harmonic sum. -/

namespace BoxPartition
open Finset
variable {p : ℕ} [Fact p.Prime]

noncomputable def H (p N : ℕ) [Fact p.Prime] : localRing p :=
  ∑ x ∈ small p N, safe p (2*N-x)
noncomputable def T (p N : ℕ) [Fact p.Prime] : localRing p :=
  ∑ x ∈ small p N, safe p (N+x)*safe p (2*N-x)

omit [Fact p.Prime] in
lemma two_units {N x : ℕ} (hN : p∣N) (hx : x∈small p N) :
    ¬p∣N+x ∧ ¬p∣2*N-x := by
  obtain ⟨hr,hd⟩ := mem_filter.mp hx
  obtain ⟨lo,hi⟩ := mem_Ico.mp hr
  have h2 : p∣2*N := dvd_mul_of_dvd_right hN 2
  refine ⟨fun h => hd ((Nat.dvd_add_iff_right hN).mpr h),?_⟩
  intro h
  have he := Nat.dvd_sub h2 h
  rw [show 2*N-(2*N-x)=x by omega] at he; exact hd he

omit [Fact p.Prime] in
lemma reflection {R : Type*} [AddCommMonoid R] {N : ℕ} (hN : p∣N) (f : ℕ → R) :
    (∑ x ∈ small p N,f (N-x))=∑ x ∈ small p N,f x := by
  apply sum_bij (fun x _ => N-x)
  · intro x hx
    obtain ⟨hr,hd⟩ := mem_filter.mp hx
    obtain ⟨lo,hi⟩ := mem_Ico.mp hr
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
    intro h
    have hh := Nat.dvd_sub hN h
    rw [show N-(N-x)=x by omega] at hh; exact hd hh
  · intro x hx y hy he
    have := mem_Ico.mp (mem_filter.mp hx).1
    have := mem_Ico.mp (mem_filter.mp hy).1
    omega
  · intro x hx
    obtain ⟨hr,hd⟩ := mem_filter.mp hx
    obtain ⟨lo,hi⟩ := mem_Ico.mp hr
    refine ⟨N-x,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩
    intro h
    have hh := Nat.dvd_sub hN h
    rw [show N-(N-x)=x by omega] at hh; exact hd hh
  · intros; rfl

lemma harmonic_reflect {N : ℕ} (hN : p∣N) : 2*H p N=3*(N:localRing p)*T p N := by
  have ref := reflection hN (fun x => safe p (N+x))
  have rr : H p N = ∑ x ∈ small p N,safe p (N+x) := by
    rw [← ref]
    apply sum_congr rfl
    intro x hx
    have hh := mem_Ico.mp (mem_filter.mp hx).1
    rw [show N+(N-x)=2*N-x by omega]
  rw [two_mul]
  nth_rw 1 [rr]
  unfold H T
  rw [←sum_add_distrib,mul_sum]
  apply sum_congr rfl
  intro x hx
  obtain ⟨h1,h2⟩ := two_units hN hx
  have hl := mem_Ico.mp (mem_filter.mp hx).1
  have ex : N+x+(2*N-x)=3*N := by omega
  have e : ((N+x:ℕ):localRing p)+((2*N-x:ℕ):localRing p)=3*N := by exact_mod_cast ex
  have a := safe_inv (N+x) h1
  have b := safe_inv (2*N-x) h2
  linear_combination (safe p (N+x)*safe p (2*N-x))*e - safe p (2*N-x)*a - safe p (N+x)*b

lemma square_filter {N : ℕ} : (∑ x ∈ range N,(safe p x)^2)=∑ x ∈ small p N,(safe p x)^2 := by
  symm
  apply sum_subset_zero_on_sdiff
  · intro x hx; exact mem_range.mpr (mem_Ico.mp (mem_filter.mp hx).1).2
  · intro x hx
    obtain ⟨hr,hn⟩ := mem_sdiff.mp hx
    have hh := mem_range.mp hr
    by_cases hd : p∣x
    · simp [safe,hd]
    · have lo : 1≤x := by have hn : x ≠ 0 := fun he => hd (by rw [he]; exact dvd_zero _); omega
      exact (hn (mem_filter.mpr ⟨mem_Ico.mpr ⟨lo,hh⟩,hd⟩)).elim
  · intros; rfl

lemma harmonic_odd {N r : ℕ} (hr : 0<r) (hN : p^r∣N) (hp : p≠2) :
    (p:localRing p)^(2*r) ∣ 3*H p N := by
  have pN : p∣N := (dvd_pow_self p hr.ne').trans hN
  have piN : (p:localRing p)^r ∣ (N:localRing p) := by
    obtain ⟨v,hv⟩ := hN; exact ⟨(v:localRing p),by exact_mod_cast hv⟩
  have PN0 : (N:ZMod (p^r))=0 := (ZMod.natCast_eq_zero_iff ..).mpr hN
  have td : (p:localRing p)^r ∣ T p N+∑ x ∈ small p N,(safe p x)^2 := by
    apply ker_reduce hr
    simp only [T,map_add,map_sum,map_mul,map_pow,← sum_add_distrib]
    apply sum_eq_zero
    intro x hx
    have hw := mem_Ico.mp (mem_filter.mp hx).1
    have hx' := (mem_filter.mp hx).2
    obtain ⟨h1,h2⟩ := two_units pN hx
    simp only [safe,dif_pos h1,dif_pos h2,dif_pos hx',red_inv]
    rw [Nat.cast_add, Nat.cast_sub (show x≤2*N by omega),Nat.cast_mul,PN0,zero_add,mul_zero,zero_sub]
    have u := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hx'
    have negi : (-(x:ZMod (p^r)))⁻¹ = -(x:ZMod (p^r))⁻¹ := by
      apply u.neg.mul_left_inj.mp
      rw [ZMod.inv_mul_of_unit _ u.neg,neg_mul_neg,ZMod.inv_mul_of_unit _ u]
    rw [negi]; ring
  have s := three_square_local r N hr hN hp
  rw [square_filter] at s
  have td' : (p:localRing p)^r ∣ 3*T p N := by
    obtain ⟨a,ha⟩ := td; obtain ⟨b,hb⟩ := s
    exact ⟨3*a-b,by linear_combination 3*ha-hb⟩
  have d : (p:localRing p)^(2*r) ∣ 2*(3*H p N) := by
    obtain ⟨a,ha⟩ := piN
    obtain ⟨b,hb⟩ := td'
    have eq := harmonic_reflect pN
    refine ⟨3*a*b,?_⟩
    rw [show 2*r=r+r by omega,pow_add]
    linear_combination 3*eq +3*(N:localRing p)*hb +3*((p:localRing p)^r*b)*ha
  obtain ⟨q,hq⟩ := d
  have hn2 : ¬p∣2 := fun h => ((Nat.dvd_prime Nat.prime_two).mp h).elim (Fact.out : p.Prime).ne_one hp
  have htwo := safe_inv 2 hn2
  refine ⟨safe p 2*q,?_⟩
  push_cast at htwo
  linear_combination safe p 2*hq - (3*H p N)*htwo

end BoxPartition

/-! The error term in the paired MacMahon product. -/

namespace BoxPartition
open Finset
variable {p : ℕ} [Fact p.Prime]

noncomputable def unitProduct (p N : ℕ) [Fact p.Prime] : localRing p :=
  ∏ x ∈ small p N, (1+(N:localRing p)^2*(3*safe p x*safe p (2*N-x)))^x

lemma residual_coe {N : ℕ} (hN : p∣N) : (unitProduct p N : ℚ)=residual p N := by
  unfold unitProduct residual
  push_cast
  apply prod_congr rfl
  intro x hx
  have h := (mem_filter.mp hx).2
  have h2 := (two_units hN hx).2
  have lo := (mem_Ico.mp (mem_filter.mp hx).1).2
  simp only [safe,dif_pos h,dif_pos h2,invNat,inc,Nat.cast_sub (by omega : x≤2*N),Nat.cast_mul,Nat.cast_ofNat]
  congr 2
  rw [show ((3:localRing p):ℚ)=(3:ℚ) by rfl]
  rw [div_eq_mul_inv,mul_inv_rev]
  ring

lemma expansion {N : ℕ} (_hN : p∣N) :
    ∃ b : localRing p, unitProduct p N-1=(N:localRing p)^2*(3*H p N)+(N:localRing p)^4*b := by
  let v := fun x => (3:localRing p)*safe p x*safe p (2*N-x)
  obtain ⟨b,hb⟩ := first_product (small p N) ((N:localRing p)^2) v id
  have sum : (∑ x ∈ small p N, (x:localRing p)*v x)=3*H p N := by
    unfold H
    rw [mul_sum]; apply sum_congr rfl
    intro x hx
    have a := safe_inv x (mem_filter.mp hx).2
    dsimp [v]
    linear_combination 3*safe p (2*N-x)*a
  change unitProduct p N-1-(N:localRing p)^2*(∑ x ∈ small p N,(x:localRing p)*v x)=_ at hb
  rw [sum] at hb
  exact ⟨b,by linear_combination hb⟩

lemma two_orders {N r : ℕ} (hr : 0<r) (hN : p^r∣N) :
    (p:localRing p)^(2*r) ∣ unitProduct p N-1 := by
  obtain ⟨b,hb⟩ := expansion ((dvd_pow_self p hr.ne').trans hN)
  obtain ⟨k,hk⟩ := hN
  have he : (N:localRing p)=(p:localRing p)^r*k := by exact_mod_cast hk
  refine ⟨(k:localRing p)^2*(3*H p N+(N:localRing p)^2*b),?_⟩
  rw [hb,he,show 2*r=r*2 by omega,pow_mul]
  ring

lemma four_orders {N r : ℕ} (hr : 0<r) (hN : p^r∣N) (hp : p≠2) :
    (p:localRing p)^(4*r) ∣ unitProduct p N-1 := by
  obtain ⟨b,hb⟩ := expansion ((dvd_pow_self p hr.ne').trans hN)
  obtain ⟨c,hc⟩ := harmonic_odd hr hN hp
  obtain ⟨k,hk⟩ := hN
  have he : (N:localRing p)=(p:localRing p)^r*k := by exact_mod_cast hk
  refine ⟨(k:localRing p)^2*c+(k:localRing p)^4*b,?_⟩
  rw [hb,hc,he,show 4*r=r*4 by omega,show 2*r=r*2 by omega]
  simp only [pow_mul]
  ring

end BoxPartition

/-! The contribution of one prime power in Legendre’s formula. -/

namespace BoxPartition
open Finset

def floorSum (D t : ℕ) : ℤ := ∑ i ∈ range t, ((i/D:ℕ):ℤ)
def layer (D N : ℕ) : ℤ := floorSum D (3*N)-3*floorSum D (2*N)+3*floorSum D N

lemma floor_small {D t : ℕ} (h : t≤D) : floorSum D t=0 := by
  apply sum_eq_zero
  intro i hi
  simp [Nat.div_eq_of_lt ((mem_range.mp hi).trans_le h)]

lemma floor_shift {D : ℕ} (hD : 0<D) (n : ℕ) : floorSum D (D+n)=floorSum D n+n := by
  unfold floorSum
  rw [sum_range_add,show (∑ i ∈ range D, ((i/D:ℕ):ℤ))=0 from floor_small le_rfl,zero_add]
  simp only [Nat.add_div_left _ hD,Nat.cast_add,Nat.cast_one,sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one]

lemma floor_shift_many {D : ℕ} (hD : 0<D) (q s : ℕ) :
    2*floorSum D (q*D+s)=2*floorSum D s+(D:ℤ)*q*((q:ℤ)-1)+2*q*s := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q+1)*D+s=D+(q*D+s) by ring,floor_shift hD]
    push_cast
    linear_combination ih

lemma periodic_layer {D : ℕ} (hD : 0<D) (q s : ℕ) : layer D (q*D+s)=layer D s := by
  unfold layer
  have h1 := floor_shift_many hD q s
  have h2 := floor_shift_many hD (2*q) (2*s)
  have h3 := floor_shift_many hD (3*q) (3*s)
  rw [show 2*(q*D+s)=2*q*D+2*s by ring,show 3*(q*D+s)=3*q*D+3*s by ring]
  push_cast at h2 h3
  linarith [show 2*floorSum D (3*q*D+3*s)-6*floorSum D (2*q*D+2*s)+6*floorSum D (q*D+s)=
    2*floorSum D (3*s)-6*floorSum D (2*s)+6*floorSum D s by linear_combination h3-3*h2+3*h1]

lemma floor_three {D t : ℕ} (hD : 0<D) (ht : t≤3*D) :
    floorSum D t=((t-D:ℕ):ℤ)+((t-2*D:ℕ):ℤ) := by
  by_cases h0 : t≤D
  · rw [floor_small h0]; omega
  have e : t=D+(t-D) := by omega
  rw [e,floor_shift hD]
  by_cases h1 : t-D≤D
  · rw [floor_small h1]; omega
  have ee : t-D=D+(t-2*D) := by omega
  rw [ee,floor_shift hD,floor_small (show t-2*D≤D by omega)]
  omega

lemma layer_nonneg {D : ℕ} (hD : 0<D) (N : ℕ) : 0≤layer D N := by
  let s := N%D
  have hs : s < D := Nat.mod_lt _ hD 
  have hN : N=N/D*D+s := by dsimp [s]; exact (Nat.div_add_mod' N D).symm
  rw [hN,periodic_layer hD]
  unfold layer
  rw [floor_three hD (show 3*s≤3*D by omega),floor_three hD (show 2*s≤3*D by omega),floor_small hs.le]
  omega

lemma layer_two_odd {N : ℕ} (h : Odd N) : layer 2 N=1 := by
  obtain ⟨k,hk⟩ := h
  rw [show N=k*2+1 by omega,periodic_layer (by decide)]
  decide

lemma row_floor (D N : ℕ) :
    (∑ i ∈ range N, ((((i+2*N)/D:ℕ):ℤ)+((i/D:ℕ):ℤ)-2*(((i+N)/D:ℕ):ℤ)))=layer D N := by
  have h (t : ℕ) : (∑ i ∈ range N, (((i+t)/D:ℕ):ℤ))=floorSum D (t+N)-floorSum D t := by
    unfold floorSum
    rw [sum_range_add,add_sub_cancel_left]
    apply sum_congr rfl; intro i hi; rw [add_comm i t]
  rw [sum_sub_distrib,sum_add_distrib,←mul_sum,h (2*N),h N]
  change _ + floorSum D N - _ = _
  rw [show 2*N+N=3*N by omega,show N+N=2*N by omega]
  unfold layer; ring

end BoxPartition

/-! MacMahon’s row factorials and their prime valuations. -/

namespace BoxPartition
open Finset OMA.S_oeis_a008793

def facQ (k : ℕ) : ℚ := k.factorial

lemma fac_pos (k : ℕ) : 0<facQ k := by unfold facQ; positivity

lemma rising (m k : ℕ) : (∏ i ∈ range k, ((m+i+1:ℕ):ℚ)) = facQ (m+k)/facQ m := by
  induction k with
  | zero => simp [(fac_pos m).ne']
  | succ k ih =>
    rw [prod_range_succ,ih]
    have hs : facQ (m+(k+1))=((m+k+1:ℕ):ℚ)*facQ (m+k) := by
      rw [show m+(k+1)=(m+k)+1 by omega]
      simp [facQ,Nat.factorial_succ]
    rw [hs]; ring

lemma shift_product (N : ℕ) (f : ℕ → ℚ) :
    (∏ i ∈ Icc 1 N,f i)=∏ i ∈ range N, f (i+1) := by
  rw [← Ico_add_one_right_eq_Icc,prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]; apply prod_congr rfl; intro i hi; rw [add_comm 1 i]

def rowQ (N i : ℕ) := facQ (i+2*N)*facQ i/(facQ (i+N))^2

lemma rows (N : ℕ) : a N=∏ i ∈ range N,rowQ N i := by
  unfold a
  rw [shift_product]
  apply prod_congr rfl
  intro i hi
  rw [shift_product,prod_div_distrib]
  have hnum : (∏ j ∈ range N, ((N+(i+1)+(j+1)-1:ℕ):ℚ))=facQ (i+2*N)/facQ (i+N) := by
    convert rising (i+N) N using 1
    · apply prod_congr rfl; intro j hj; congr 1 <;> omega
    · rw [show i+2*N=i+N+N by omega]
  have hden : (∏ j ∈ range N, (((i+1)+(j+1)-1:ℕ):ℚ))=facQ (i+N)/facQ i := by
    convert rising i N using 1
    apply prod_congr rfl; intro j hj; congr 1 <;> omega
  rw [hnum,hden]; unfold rowQ
  field_simp [(fac_pos i).ne',(fac_pos (i+N)).ne']

lemma row_pos (N i : ℕ) : 0 < rowQ N i := by
  unfold rowQ; exact div_pos (mul_pos (fac_pos _) (fac_pos _)) (sq_pos_of_pos (fac_pos _))

lemma box_pos (N : ℕ) : 0<a N := by
  rw [rows]; exact prod_pos fun i _ => row_pos N i

lemma val_rows {p : ℕ} [Fact p.Prime] (N : ℕ) :
    padicValRat p (a N)= ∑ i ∈ range N,
      ((padicValNat p (i+2*N).factorial:ℤ)+padicValNat p i.factorial-2*padicValNat p (i+N).factorial) := by
  rw [rows]
  have prodVal (s : Finset ℕ) : padicValRat p (∏ i ∈ s,rowQ N i)=∑ i ∈ s,padicValRat p (rowQ N i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [prod_insert hi,sum_insert hi,padicValRat.mul (row_pos _ _).ne' (prod_pos (fun i _ => row_pos N i)).ne',ih]
  rw [prodVal]; apply sum_congr rfl; intro i hi
  unfold rowQ
  rw [padicValRat.div (mul_pos (fac_pos _) (fac_pos _)).ne' (sq_pos_of_pos (fac_pos _)).ne',
    padicValRat.mul (fac_pos _).ne' (fac_pos _).ne',padicValRat.pow]
  simp [facQ,padicValRat.of_nat]

lemma box_val {p : ℕ} [Fact p.Prime] (N : ℕ) :
    padicValRat p (a N)=∑ t ∈ Ico 1 (3*N+1),layer (p^t) N := by
  rw [val_rows]
  have leg (k : ℕ) (hk : k≤3*N) : (padicValNat p k.factorial:ℤ)=
      ∑ t ∈ Ico 1 (3*N+1), ((k/p^t:ℕ):ℤ) := by
    rw [padicValNat_factorial (show Nat.log p k<3*N+1 by have := Nat.log_le_self p k; omega)]
    push_cast; rfl
  calc
    _ = ∑ i ∈ range N, ∑ t ∈ Ico 1 (3*N+1),
      ((((i+2*N)/p^t:ℕ):ℤ)+((i/p^t:ℕ):ℤ)-2*(((i+N)/p^t:ℕ):ℤ)) := by
        apply sum_congr rfl; intro i hi
        have ih := mem_range.mp hi
        rw [leg _ (by omega),leg _ (by omega),leg _ (by omega)]
        rw [sum_sub_distrib,sum_add_distrib,←mul_sum]
    _ = _ := by rw [sum_comm]; simp_rw [row_floor]

end BoxPartition

/-! Integrality and the extra factor of two at the previous scale. -/

namespace BoxPartition
open Finset OMA.S_oeis_a008793

lemma integer_box (N : ℕ) : ∃ z : ℕ, a N=(z:ℚ) := by
  let q := a N
  have nonnegative (p : ℕ) [Fact p.Prime] : 0≤padicValRat p q := by
    rw [show q=a N from rfl,box_val]
    exact sum_nonneg fun t _ => layer_nonneg (pow_pos (Fact.out : p.Prime).pos _) _
  have den : q.den=1 := by
    by_contra hn
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hn
    let _ : Fact p.Prime := ⟨hp⟩
    have hnum : ¬p∣q.num.natAbs := by
      intro hd
      exact hp.not_dvd_one (q.reduced ▸ Nat.dvd_gcd hd hpd)
    have val := nonnegative p
    rw [padicValRat_def,padicValInt,padicValNat.eq_zero_of_not_dvd hnum] at val
    have hpos := one_le_padicValNat_of_dvd q.den_nz hpd
    omega
  have hnum : 0≤q.num := Rat.num_nonneg.mpr (box_pos N).le
  refine ⟨q.num.toNat,?_⟩
  have eq := q.num_div_den
  rw [den,Nat.cast_one,div_one] at eq
  have he := Int.toNat_of_nonneg hnum
  exact eq.symm.trans (by exact_mod_cast he.symm)

lemma layer_mid (z : ℕ) (hz : 0<z) (k : ℕ) : layer (2*z) ((2*k+1)*z)=(z:ℤ) := by
  rw [show (2*k+1)*z=k*(2*z)+z by ring,periodic_layer (by omega)]
  unfold layer
  rw [floor_three (by omega) (show 3*z≤3*(2*z) by omega),
    floor_small (show 2*z≤2*z by omega),floor_small (show z≤2*z by omega)]
  omega

lemma two_div_box (n r m : ℕ) (hn : 0<n) (hr : 0<r) (eq : a (n*2^(r-1))=(m:ℚ)) : 2^r∣m := by
  obtain ⟨e,u,hu,he⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  obtain ⟨k,hk⟩ := hu
  let t := e+(r-1)
  let M := n*2^(r-1)
  have b : M=(2*k+1)*2^t := by dsimp [M,t]; rw [he,hk,pow_add]; ring
  have pos : 0<2^t := by positivity
  have tl : t<2^t := Nat.lt_two_pow_self
  have zm : 2^t≤M := by rw [b]; exact Nat.le_mul_of_pos_left _ (by omega)
  have mem : t+1∈Ico 1 (3*M+1) := mem_Ico.mpr ⟨by omega,by omega⟩
  have low := single_le_sum (fun j (_ : j∈Ico 1 (3*M+1)) => layer_nonneg (show 0<2^j by positivity) M) mem
  rw [← box_val (p:=2) M] at low
  have mid : layer (2^(t+1)) M=(2^t:ℕ) := by
    rw [b,pow_succ,mul_comm (2^t) 2]; exact layer_mid _ pos k
  rw [mid,show a M=(m:ℚ) from eq,padicValRat.of_nat] at low
  have rt : r≤t+1 := by dsimp [t]; omega
  have rm : r≤2^t := rt.trans (Nat.succ_le_of_lt tl)
  have mh : m≠0 := by rintro rfl; have := box_pos (n*2^(r-1)); rw [eq] at this; norm_num at this
  exact (padicValNat_dvd_iff_le mh).mpr (by exact_mod_cast (show (r:ℤ)≤(padicValNat 2 m:ℤ) by omega))

end BoxPartition

open BoxPartition OMA.S_oeis_a008793 in
theorem OMA.solution : type_of% @OMA.S_oeis_a008793.main := by
  intro p n r hp hn hr
  let _ : Fact p.Prime := ⟨hp⟩
  let M := n*p^(r-1)
  let N := n*p^r
  have eqN : N=p*M := by
    dsimp [M,N]
    rw [show r=r-1+1 from by omega] at ⊢
    simp only [Nat.add_sub_cancel,pow_succ]; ring
  have pm : 0<M := Nat.mul_pos hn (pow_pos hp.pos _)
  have hN : p^r∣N := dvd_mul_left _ _
  have pn : p∣N := (dvd_pow_self p hr.ne').trans hN
  obtain ⟨m,em⟩ := integer_box M
  obtain ⟨v,ev⟩ := integer_box N
  have d : (v:localRing p)-(m:localRing p)^p=(m:localRing p)^p*(unitProduct p N-1) := by
    apply Subtype.ext
    change (v:ℚ)-(m:ℚ)^p=(m:ℚ)^p*((unitProduct p N:ℚ)-1)
    rw [residual_coe pn,← ev,← em,eqN,main_split hp.pos pm]; ring
  have dv : (p:localRing p)^(4*r) ∣ (v:localRing p)-(m:localRing p)^p := by
    rw [d]
    by_cases h2 : p=2
    · subst p
      obtain ⟨b,hb⟩ := two_orders hr hN
      obtain ⟨k,hk⟩ := two_div_box n r m hn hr em
      have he : (m:localRing 2)=(2:localRing 2)^r*k := by exact_mod_cast hk
      refine ⟨(k:localRing 2)^2*b,?_⟩
      rw [hb,he,show 4*r=r*4 by omega,show 2*r=r*2 by omega]
      simp only [pow_mul]; ring
    · exact dvd_mul_of_dvd_right (four_orders hr hN h2) _
  obtain ⟨u,hu⟩ := dv
  let delta : ℤ := (v:ℤ)-(m:ℤ)^p
  have eqD : (delta:ℚ)=(p:ℚ)^(4*r)*(u:ℚ) := by
    have hh := congrArg (fun z : localRing p => (z:ℚ)) hu
    dsimp [delta]; push_cast
    exact_mod_cast hh
  obtain ⟨k,hk⟩ := int_from_local u.property eqD
  refine ⟨k,?_⟩
  change a N-a M^p=_
  rw [em,ev]
  dsimp [delta] at hk
  exact_mod_cast hk
