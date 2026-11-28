import OMAStatements.S_oeis_a165141
import Mathlib

/-! An elementary modular count for the ordinary square, pentagonal and
hexagonal sum. All representation variables in the final count are natural. -/

namespace SunRatio

abbrev Triple (R : Type*) := R × R × R

/-- If evaluated on natural indices and cast to a ring, this equals four
times the polygonal sum plus one. -/
def poly {R : Type*} [CommRing R] (v : Triple R) : R :=
  4*v.1^2 + 6*v.2.1^2 - 2*v.2.1 + 8*v.2.2^2 - 4*v.2.2 + 1

abbrev Zeros (R : Type*) [CommRing R] := {v : Triple R // poly v = 0}

section Field
variable {K : Type*} [Field K]

def affine (v : Triple K) : Triple K :=
  (2*v.1+3*v.2.1+2*v.2.2-1, 2*v.1-3*v.2.1+2*v.2.2,
   2*v.1-4*v.2.2+1)

def affineInv (v : Triple K) : Triple K :=
  ((v.1+v.2.1+v.2.2)/6, (v.1-v.2.1+1)/6, (v.1+v.2.1-2*v.2.2+3)/12)

def affineEquiv (h6 : (6 : K) ≠ 0) (h12 : (12 : K) ≠ 0) : Triple K ≃ Triple K where
  toFun := affine
  invFun := affineInv
  left_inv := by
    rintro ⟨x,y,z⟩
    simp only [affine, affineInv, Prod.mk.injEq]
    constructor
    · field_simp [h6,h12]
      ring
    constructor <;> field_simp [h6,h12] <;> ring
  right_inv := by
    rintro ⟨x,y,z⟩
    simp only [affine, affineInv, Prod.mk.injEq]
    constructor
    · field_simp [h6,h12]
      ring
    constructor <;> field_simp [h6,h12] <;> ring

def squareSum (v : Triple K) : K := v.1^2 + v.2.1^2 + v.2.2^2

theorem affine_norm (v : Triple K) : squareSum (affine v) = 3*poly v - 1 := by
  dsimp [squareSum, affine, poly]
  ring

/-- Split the equation of the sphere using a²+b² = -1. -/
def splitMap (a b : K) (v : Triple K) : Triple K :=
  (a*v.1+b*v.2.1, v.2.2-(-b*v.1+a*v.2.1), v.2.2+(-b*v.1+a*v.2.1))

def splitInv (a b : K) (v : Triple K) : Triple K :=
  (-a*v.1+b*((v.2.2-v.2.1)/2), -b*v.1-a*((v.2.2-v.2.1)/2), (v.2.1+v.2.2)/2)

def splitEquiv (a b : K) (h : a^2+b^2 = -1) (h2 : (2:K) ≠ 0) :
    Triple K ≃ Triple K where
  toFun := splitMap a b
  invFun := splitInv a b
  left_inv := by
    rintro ⟨x,y,z⟩
    simp only [splitMap, splitInv, Prod.mk.injEq]
    constructor
    · field_simp
      linear_combination -2*x*h
    constructor
    · field_simp
      linear_combination -2*y*h
    · field_simp
      ring
  right_inv := by
    rintro ⟨r,s,t⟩
    simp only [splitMap, splitInv, Prod.mk.injEq]
    constructor
    · field_simp
      linear_combination -2*r*h
    constructor
    · field_simp
      linear_combination (t-s)*h
    · field_simp
      linear_combination (s-t)*h

def splitNorm (v : Triple K) : K := v.2.1*v.2.2 - v.1^2

theorem split_norm (a b : K) (h : a^2+b^2 = -1) (v : Triple K) :
    splitNorm (splitMap a b v) = squareSum v := by
  dsimp [splitNorm, splitMap, squareSum]
  linear_combination -(v.1^2+v.2.1^2)*h

/-- The first branch has nonzero second coordinate. The other two branches
have second coordinate zero and first coordinate either 1 or -1. -/
def param : (Kˣ ⊕ Bool) × K → Triple K
  | (.inl s,r) => (r,s,(r^2-1)/(s:K))
  | (.inr false,t) => (1,0,t)
  | (.inr true,t) => (-1,0,t)

theorem param_norm (e : (Kˣ ⊕ Bool) × K) : splitNorm (param e) = -1 := by
  rcases e with ⟨s | s, r⟩
  · dsimp [param, splitNorm]
    field_simp
    ring
  · cases s <;> simp [param, splitNorm]

theorem param_injective (h2 : (2:K) ≠ 0) : Function.Injective (param (K:=K)) := by
  have signs : (1:K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  rintro ⟨a | a,x⟩ ⟨b | b,y⟩ h
  · simp only [param, Prod.mk.injEq] at h
    have hab : a = b := Units.ext h.2.1
    subst b
    simp [h.1]
  · cases b <;> simp [param, Units.ne_zero] at h
  · cases a <;> simp only [param, Prod.mk.injEq] at h <;> exact (b.ne_zero h.2.1.symm).elim
  · cases a <;> cases b <;> simp_all [param, Ne.symm signs]

theorem param_onto (v : Triple K) (hv : splitNorm v = -1) :
    ∃ e : (Kˣ ⊕ Bool) × K, param e = v := by
  rcases v with ⟨r,s,t⟩
  change s*t-r^2 = -1 at hv
  by_cases hs : s=0
  · subst s
    have hh : (r-1)*(r+1)=0 := by linear_combination -hv
    rcases mul_eq_zero.mp hh with h | h
    · have hr : r=1 := by linear_combination h
      exact ⟨(.inr false,t), by simp [param,hr]⟩
    · have hr : r = -1 := by linear_combination h
      exact ⟨(.inr true,t), by simp [param,hr]⟩
  · refine ⟨(.inl (Units.mk0 s hs),r), ?_⟩
    simp only [param, Units.val_mk0, Prod.mk.injEq, true_and]
    field_simp
    linear_combination -hv

end Field

theorem prime_count (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.card (Zeros (ZMod p)) = p*(p+1) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have small (j : ℕ) (hj : 0 < j) (hl : j < p) : (j : ZMod p) ≠ 0 :=
    fun h => Nat.not_dvd_of_pos_of_lt hj hl ((ZMod.natCast_eq_zero_iff j p).mp h)
  have h2 : (2 : ZMod p) ≠ 0 := small 2 (by decide) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := small 3 (by decide) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := by
    rw [show (6 : ZMod p) = 2*3 by ring]
    exact mul_ne_zero h2 h3
  have h12 : (12 : ZMod p) ≠ 0 := by
    rw [show (12 : ZMod p) = 2*6 by ring]
    exact mul_ne_zero h2 h6
  obtain ⟨a,b,hab⟩ := ZMod.sq_add_sq p (-1)
  let e := (affineEquiv h6 h12).trans (splitEquiv a b hab h2)
  let E : Zeros (ZMod p) ≃ {v : Triple (ZMod p) // splitNorm v = -1} :=
    e.subtypeEquiv fun v => by
      change poly v = 0 ↔ splitNorm (splitMap a b (affine v)) = -1
      rw [split_norm a b hab, affine_norm]
      constructor
      · intro h
        rw [h]
        ring
      · intro h
        have hh : 3*poly v=0 := by linear_combination h
        exact (mul_eq_zero.mp hh).resolve_left h3
  let g : ((ZMod p)ˣ ⊕ Bool) × ZMod p → {v : Triple (ZMod p) // splitNorm v = -1} :=
    fun v => ⟨param v, param_norm v⟩
  have hg : Function.Bijective g := by
    constructor
    · exact fun _ _ h => param_injective h2 (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨w,hw⟩ := param_onto v hv
      exact ⟨w, Subtype.ext hw⟩
  rw [Nat.card_congr (E.trans (Equiv.ofBijective g hg).symm), Nat.card_prod, Nat.card_sum]
  have hu : Nat.card (ZMod p)ˣ = p-1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hu, Nat.card_zmod, show Nat.card Bool = 2 by simp, show p-1+2=p+1 by omega, Nat.mul_comm]

def mapTriple {R S : Type*} [CommRing R] [CommRing S] (e : R →+* S) (v : Triple R) :
    Triple S := (e v.1,e v.2.1,e v.2.2)

theorem map_poly {R S : Type*} [CommRing R] [CommRing S] (e : R →+* S) (v : Triple R) :
    e (poly v) = poly (mapTriple e v) := by simp [poly, mapTriple, map_ofNat]

def changeRing {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Zeros R ≃ Zeros S where
  toFun v := ⟨mapTriple e.toRingHom v.val, by rw [← map_poly,v.property,map_zero]⟩
  invFun v := ⟨mapTriple e.symm.toRingHom v.val, by rw [← map_poly,v.property,map_zero]⟩
  left_inv := by rintro ⟨⟨x,y,z⟩,h⟩; apply Subtype.ext; simp [mapTriple]
  right_inv := by rintro ⟨⟨x,y,z⟩,h⟩; apply Subtype.ext; simp [mapTriple]

def splitProduct (R S : Type*) [CommRing R] [CommRing S] :
    Zeros (R × S) ≃ Zeros R × Zeros S where
  toFun v :=
    (⟨mapTriple (RingHom.fst R S) v.val, by rw [← map_poly,v.property,map_zero]⟩,
     ⟨mapTriple (RingHom.snd R S) v.val, by rw [← map_poly,v.property,map_zero]⟩)
  invFun v :=
    ⟨((v.1.val.1,v.2.val.1),(v.1.val.2.1,v.2.val.2.1),(v.1.val.2.2,v.2.val.2.2)),
     Prod.ext v.1.property v.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_mul {m n : ℕ} (h : m.Coprime n) :
    Nat.card (Zeros (ZMod (m*n))) = Nat.card (Zeros (ZMod m)) * Nat.card (Zeros (ZMod n)) := by
  rw [Nat.card_congr ((changeRing (ZMod.chineseRemainder h)).trans
    (splitProduct (ZMod m) (ZMod n))), Nat.card_prod]

theorem squarefree_count (S : Finset ℕ) (hs : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) :
    Nat.card (Zeros (ZMod (∏ p ∈ S, p))) = ∏ p ∈ S, (p*(p+1)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact @Nat.card_unique (Zeros (ZMod 1)) ⟨⟨(0,0,0),Subsingleton.elim _ _⟩⟩ inferInstance
  | @insert a s ha ih =>
    have hp := hs a (Finset.mem_insert_self _ _)
    have hsmall : ∀ p ∈ s, p.Prime ∧ 5 ≤ p := fun p h => hs p (Finset.mem_insert_of_mem h)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p h
      exact (Nat.coprime_primes hp.1 (hsmall p h).1).mpr (fun hh => ha (hh ▸ h))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, count_mul hcop, prime_count a hp.1 hp.2, ih hsmall]

/-- Disjoint blocks of primes above five give arbitrarily large reciprocal sums. -/
theorem prime_sum (t : ℕ) : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 5 ≤ p) ∧
    (t:ℝ)/2 ≤ ∑ p ∈ S, (1/(p:ℝ)) := by
  classical
  induction t with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ t ih =>
    obtain ⟨S,hS,hbound⟩ := ih
    let k := S.sup id + 5
    let T := (4 ^ (k.primesBelow.card + 1)).succ.primesBelow \ k.primesBelow
    have block : (1:ℝ)/2 ≤ ∑ p ∈ T, 1/(p:ℝ) := one_half_le_sum_primes_ge_one_div k
    have good (p : ℕ) (h : p ∈ T) : p.Prime ∧ k ≤ p := by
      obtain ⟨hi,ho⟩ := Finset.mem_sdiff.mp h
      have hp := Nat.prime_of_mem_primesBelow hi
      exact ⟨hp, le_of_not_gt fun hl => ho (Nat.mem_primesBelow.mpr ⟨hl,hp⟩)⟩
    have dis : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro p hp ht
      have hle : p ≤ S.sup id := Finset.le_sup (f:=id) hp
      have hk := (good p ht).2
      dsimp [k] at hk
      omega
    refine ⟨S ∪ T, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact hS p h
      · obtain ⟨h1,h2⟩ := good p h
        exact ⟨h1, by dsimp [k] at h2; omega⟩
    · rw [Finset.sum_union dis]
      push_cast
      linarith

theorem prod_lower (S : Finset ℕ) :
    1 + (∑ p ∈ S, 1/(p:ℝ)) ≤ ∏ p ∈ S, (1+1/(p:ℝ)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hsum : 0 ≤ ∑ p ∈ s, 1/(p:ℝ) := Finset.sum_nonneg fun _ _ => by positivity
    have hmul := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1+1/(a:ℝ) by positivity)
    nlinarith [mul_nonneg hsum (show 0 ≤ 1/(a:ℝ) by positivity)]

theorem dense_modulus (L : ℕ) : ∃ M : ℕ, 0 < M ∧ L*M^2 < Nat.card (Zeros (ZMod M)) := by
  obtain ⟨S,hs,hb⟩ := prime_sum (2*L+2)
  let M := ∏ p ∈ S, p
  have hm : 0 < M := Finset.prod_pos fun p h => (hs p h).1.pos
  have hfactor : (Nat.card (Zeros (ZMod M)) : ℝ) =
      (M:ℝ)^2 * ∏ p ∈ S, (1+1/(p:ℝ)) := by
    dsimp [M]
    rw [squarefree_count S hs]
    push_cast
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hn : (p:ℝ) ≠ 0 := by exact_mod_cast (hs p hp).1.ne_zero
    field_simp
  have hP : (L:ℝ) < ∏ p ∈ S, (1+1/(p:ℝ)) := by
    have h := prod_lower S
    push_cast at hb
    linarith
  have hm' : (0:ℝ) < M := by exact_mod_cast hm
  have hlt : (L:ℝ) * (M:ℝ)^2 < (Nat.card (Zeros (ZMod M)) : ℝ) := by
    rw [hfactor, mul_comm (L:ℝ)]
    exact mul_lt_mul_of_pos_left hP (sq_pos_of_pos hm')
  exact ⟨M,hm,by exact_mod_cast hlt⟩

/-- The triangular term j(j-1)/2, defined by its ordinary recurrence. -/
def triangle : ℕ → ℕ
  | 0 => 0
  | j+1 => triangle j+j

theorem twice_triangle (j : ℕ) : 2*triangle j+j=j^2 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [triangle]; nlinarith

theorem triangle_formula (j : ℕ) : triangle j = j*(j-1)/2 := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [Nat.succ_sub_one]
    have h := twice_triangle (j+1)
    have h' : (j+1)*j = 2*triangle (j+1) := by nlinarith
    rw [h']
    omega

def value (t : Triple ℕ) : ℕ :=
  t.1^2 + 3*triangle t.2.1+t.2.1 + 4*triangle t.2.2+t.2.2

theorem clear_value (x y z : ℕ) :
    2*value (x,y,z)+y+2*z = 2*x^2+3*y^2+4*z^2 := by
  dsimp [value]
  nlinarith [twice_triangle y, twice_triangle z]

theorem cast_value (M x y z : ℕ) :
    poly ((x:ZMod M),(y:ZMod M),(z:ZMod M)) =
      ((4*value (x,y,z)+1 : ℕ) : ZMod M) := by
  have hh : (2:ZMod M)*(value (x,y,z):ZMod M)+y+2*z = 2*(x:ZMod M)^2+3*(y:ZMod M)^2+4*(z:ZMod M)^2 := by
    have hc := congrArg (fun j : ℕ => (j : ZMod M)) (clear_value x y z)
    push_cast at hc
    exact hc
  dsimp [poly]
  push_cast
  linear_combination -2*hh

def unbox {M : ℕ} [NeZero M] (v : Zeros (ZMod M)) : Triple ℕ :=
  (v.val.1.val,v.val.2.1.val,v.val.2.2.val)

theorem unbox_injective (M : ℕ) [NeZero M] : Function.Injective (unbox (M:=M)) := by
  intro v w h
  apply Subtype.ext
  have hh := congrArg (fun u : Triple ℕ => ((u.1 : ZMod M),(u.2.1 : ZMod M),(u.2.2 : ZMod M))) h
  simpa [unbox] using hh

theorem box_dvd (M : ℕ) [NeZero M] (v : Zeros (ZMod M)) : M ∣ 4*value (unbox v)+1 := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  change ((4*value (_,_,_)+1 : ℕ) : ZMod M) = 0
  rw [← cast_value]
  simpa [unbox] using v.property

theorem box_bound (M : ℕ) [NeZero M] (v : Zeros (ZMod M)) : value (unbox v) < 5*M^2 := by
  obtain ⟨⟨x,y,z⟩,h⟩ := v
  change value (x.val,y.val,z.val) < 5*M^2
  have xlt := Nat.pow_lt_pow_left x.val_lt (by decide : 2 ≠ 0)
  have ylt := Nat.pow_lt_pow_left y.val_lt (by decide : 2 ≠ 0)
  have zlt := Nat.pow_lt_pow_left z.val_lt (by decide : 2 ≠ 0)
  nlinarith [clear_value x.val y.val z.val]

/-- Finite fibers count ordered triples of ordinary, nonnegative polygonal indices. -/
abbrev Reps (n : ℕ) := { t : Triple ℕ // value t = n }

theorem coord_bound (v : Triple ℕ) : v.1 ≤ value v ∧ v.2.1 ≤ value v ∧ v.2.2 ≤ value v := by
  rcases v with ⟨x,y,z⟩
  have hx : x ≤ x^2 := by cases x <;> nlinarith
  dsimp [value]
  omega

instance repsFinite (n : ℕ) : Finite (Reps n) := by
  let bound (v : Reps n) : v.val.1 ≤ n ∧ v.val.2.1 ≤ n ∧ v.val.2.2 ≤ n := by
    simpa only [← v.property] using coord_bound v.val
  let f : Reps n → Triple (Fin (n+1)) := fun v =>
    (⟨v.val.1, by have := (bound v).1; omega⟩,
     ⟨v.val.2.1, by have := (bound v).2.1; omega⟩,
     ⟨v.val.2.2, by have := (bound v).2.2; omega⟩)
  apply Finite.of_injective f
  intro v w h
  apply Subtype.ext
  exact congrArg (fun u : Triple (Fin (n+1)) => (u.1.val,u.2.1.val,u.2.2.val)) h

noncomputable def count (n : ℕ) : ℕ := Nat.card (Reps n)

theorem count_zero : count 0 = 1 := by
  have heq (v : Reps 0) : v.val = (0,0,0) := by
    have h := coord_bound v.val
    rw [v.property] at h
    exact Prod.ext (Nat.eq_zero_of_le_zero h.1)
      (Prod.ext (Nat.eq_zero_of_le_zero h.2.1) (Nat.eq_zero_of_le_zero h.2.2))
  exact @Nat.card_unique (Reps 0) ⟨⟨(0,0,0), rfl⟩⟩
    ⟨fun v w => Subtype.ext ((heq v).trans (heq w).symm)⟩

/-- For every factor q there is an attained count k > q with q*n < k². -/
theorem abundant (q : ℕ) : ∃ n : ℕ, 0 < n ∧ q < count n ∧ q*n < (count n)^2 := by
  classical
  obtain ⟨M,hM,hR⟩ := dense_modulus (22*(q+5))
  let : NeZero M := ⟨hM.ne'⟩
  let : Fintype (Zeros (ZMod M)) := Fintype.ofFinite _
  let bucket (v : Zeros (ZMod M)) : Fin (22*M) :=
    ⟨(4*value (unbox v)+1)/M, by
      apply (Nat.div_lt_iff_lt_mul hM).mpr
      have hb := box_bound M v
      nlinarith [sq_pos_of_pos hM]⟩
  have hsize : Fintype.card (Fin (22*M)) * ((q+5)*M) < Fintype.card (Zeros (ZMod M)) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    convert hR using 1
    ring
  obtain ⟨j,hj⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card bucket hsize
  let F := {v : Zeros (ZMod M) // bucket v = j}
  have hF : (q+5)*M < Nat.card F := by
    simpa only [F,Nat.card_eq_fintype_card,Fintype.card_subtype] using hj
  have hfpos : 0 < Nat.card F := by omega
  obtain ⟨v⟩ := (Nat.card_pos_iff.mp hfpos).1
  let n := value (unbox v.val)
  have hequal (w : F) : value (unbox w.val) = n := by
    have he := congrArg Fin.val (w.property.trans v.property.symm)
    change (4*value (unbox w.val)+1)/M = (4*n+1)/M at he
    have h1 := Nat.div_mul_cancel (box_dvd M w.val)
    have h2 := Nat.div_mul_cancel (box_dvd M v.val)
    change (4*n+1)/M*M=4*n+1 at h2
    rw [he,h2] at h1
    omega
  let into : F → Reps n := fun w => ⟨unbox w.val, hequal w⟩
  have hinj : Function.Injective into := by
    intro u w hh
    exact Subtype.ext (unbox_injective M (congrArg Subtype.val hh))
  have hbig : (q+5)*M < count n :=
    lt_of_lt_of_le hF (Nat.card_le_card_of_injective into hinj)
  have hnn : n < 5*M^2 := box_bound M v.val
  have hq : q+5 ≤ (q+5)*M := by nlinarith [Nat.mul_le_mul_left (q+5) hM]
  have hk : 0 < n := by
    by_contra! bad
    have hz : n=0 := by omega
    rw [hz,count_zero] at hbig
    omega
  refine ⟨n,hk,by omega,?_⟩
  have ht : q*n ≤ q*(5*M^2) := Nat.mul_le_mul_left q hnn.le
  have hc : ((q+5)*M)^2 < (count n)^2 := Nat.pow_lt_pow_left hbig (by decide)
  calc q*n ≤ q*(5*M^2) := ht
       _ ≤ ((q+5)*M)^2 := by nlinarith [Nat.zero_le (q^2*M^2), Nat.zero_le (q*M^2)]
       _ < (count n)^2 := hc

/-- The first positive occurrence of k. The default value at unattained k
never enters any ratio witness below. -/
noncomputable def first (k : ℕ) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, 0<n ∧ count n=k then Nat.find h else 0

theorem first_le (n : ℕ) (hn : 0<n) : first (count n) ≤ n := by
  classical
  have h : ∃ j : ℕ, 0<j ∧ count j=count n := ⟨n,hn,rfl⟩
  unfold first
  split
  · exact Nat.find_min' _ ⟨hn,rfl⟩
  · rename_i hbad
    exact (hbad h).elim

/-- Integer form of lower limit zero along attained counts. -/
theorem first_ratio_witness (B K : ℕ) : ∃ k n : ℕ,
    K < k ∧ 0<n ∧ count n=k ∧ B*first k < k^2 := by
  obtain ⟨n,hn,hk,hr⟩ := abundant (max B K)
  refine ⟨count n,n,lt_of_le_of_lt (le_max_right _ _) hk,hn,rfl,?_⟩
  exact lt_of_le_of_lt (Nat.mul_le_mul (le_max_left _ _) (first_le n hn)) hr

/-- No positive constant can be the limiting first-occurrence ratio. -/
theorem no_positive_limit (c : ℝ) (hc : 0<c) :
    ¬ Filter.Tendsto (fun k : ℕ => (first k:ℝ)/(k:ℝ)^2) Filter.atTop (nhds c) := by
  intro h
  obtain ⟨B,hB⟩ := exists_nat_gt (2/c)
  have hB0 : (0:ℝ)<B := lt_trans (by positivity : 0 < 2/c) hB
  have hlarge := h.eventually (Ioi_mem_nhds (show c/2 < c by linarith))
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp hlarge
  obtain ⟨k,n,hk,hn,hr,hsmall⟩ := first_ratio_witness B K
  have hit : c/2 < (first k:ℝ)/(k:ℝ)^2 := hK k hk.le
  have hk0 : (0:ℝ)<k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hsq : 0 < (k:ℝ)^2 := sq_pos_of_pos hk0
  have hlo := (lt_div_iff₀ hsq).mp hit
  have hi : (B:ℝ)*(first k:ℝ) < (k:ℝ)^2 := by exact_mod_cast hsmall
  have cB := (div_lt_iff₀ hc).mp hB
  have hmul := mul_lt_mul_of_pos_left hlo hB0
  nlinarith [mul_lt_mul_of_pos_right cB hsq]


/-- Real form of the witness theorem, restricted to counts that actually occur. -/
theorem arbitrarily_small (ε : ℝ) (he : 0 < ε) (K : ℕ) :
    ∃ k n : ℕ, K < k ∧ 0 < n ∧ count n = k ∧ (first k : ℝ)/(k:ℝ)^2 < ε := by
  obtain ⟨B,hB⟩ := exists_nat_gt (1/ε)
  obtain ⟨k,n,hk,hn,hc,hw⟩ := first_ratio_witness B K
  refine ⟨k,n,hk,hn,hc,?_⟩
  have hk' : (0:ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hsq : 0 < (k:ℝ)^2 := sq_pos_of_pos hk'
  apply (div_lt_iff₀ hsq).mpr
  have hh : (B:ℝ)*(first k:ℝ) < (k:ℝ)^2 := by exact_mod_cast hw
  have h1 := (div_lt_iff₀ he).mp hB
  have h2 := mul_lt_mul_of_pos_right hh he
  nlinarith [mul_le_mul_of_nonneg_right h1.le (show (0:ℝ) ≤ first k by positivity)]

theorem no_positive_limit_on_attained (c : ℝ) (hc : 0 < c) :
    ¬ Filter.Tendsto (fun k : ℕ => (first k : ℝ)/(k:ℝ)^2)
      (Filter.atTop ⊓ Filter.principal {k | ∃ n : ℕ, 0 < n ∧ count n = k}) (nhds c) := by
  intro h
  have hev := h.eventually (Ioi_mem_nhds (show c/2 < c by linarith))
  rw [Filter.eventually_inf_principal] at hev
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨k,n,hk,hn,hcnt,hr⟩ := arbitrarily_small (c/2) (by linarith) K
  exact (not_lt_of_ge (hK k hk.le ⟨n,hn,hcnt⟩).le) hr

end SunRatio

theorem SunRatio.value_agrees (v : ℕ × ℕ × ℕ) : SunRatio.value v = OMA.S_oeis_a165141.value v := by
  simp only [SunRatio.value, OMA.S_oeis_a165141.value, SunRatio.triangle_formula]

theorem SunRatio.count_agrees : SunRatio.count = OMA.S_oeis_a165141.count := by
  funext n
  unfold SunRatio.count OMA.S_oeis_a165141.count
  change Nat.card {v : ℕ × ℕ × ℕ // SunRatio.value v = n} = _
  simp_rw [SunRatio.value_agrees]

theorem SunRatio.first_agrees : SunRatio.first = OMA.S_oeis_a165141.first := by
  funext k
  classical
  unfold SunRatio.first OMA.S_oeis_a165141.first
  rw [SunRatio.count_agrees]

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a165141.main) := by
  rintro ⟨_,_,c,hlo,_,ht⟩
  apply SunRatio.no_positive_limit c (by linarith)
  change Filter.Tendsto (fun k : ℕ => (OMA.S_oeis_a165141.first k : ℝ)/(k:ℝ)^2) _ _ at ht
  rw [SunRatio.first_agrees]
  exact ht
