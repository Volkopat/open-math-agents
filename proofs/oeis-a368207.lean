import OMAStatements.S_oeis_a368207

/-!
Proof of OEIS A368207, contributed by @CubeJerry.

The new counting argument classifies all sublattices of Z² of index n.
Each Bacher representation gives a unique standard black basis. A reflected
white family has the same cardinality. Their intersection is counted by axis
bases; lattices outside both families are characterized by diagonal minima
for the maximum-coordinate norm. The resulting divisor identity proves all
registered conjectures, including the prime-power formulas and the limit.

The argument uses the balanced-basis uniqueness lemma from desk note #151612.
The implication from the divisor identity and divisor-count limit to the
registered conjectures is adapted from reduction PR #31996:
https://github.com/lefttosolve2/open-math-agents/pull/31996
Both earlier contributions are credited; the missing all-index counting
identity and a proof of the divisor-count limit are supplied here.

Mathematical context: Roland Bacher, arXiv:2210.07657, and
https://oeis.org/A368207. The conjectures are due to Pontus von Brömssen
and Chai Wah Wu.
-/

/- A368207LatticeDefs -/

namespace A368207Lattice

abbrev V := ℤ × ℤ

def lin (u v : V) (k l : ℤ) : V :=
  (k * u.1 + l * v.1, k * u.2 + l * v.2)

def det (u v : V) : ℤ := u.1 * v.2 - u.2 * v.1

def span (u v : V) : Set V := {w | ∃ k l : ℤ, w = lin u v k l}

def height (w : V) : ℕ := max w.1.natAbs w.2.natAbs

def Minimal (L : Set V) (w : V) : Prop :=
  w ∈ L ∧ w ≠ (0, 0) ∧ ∀ z ∈ L, z ≠ (0, 0) → height w ≤ height z

def Standard (a b c d : ℤ) : Prop :=
  0 ≤ c ∧ 0 ≤ d ∧ c < a ∧ d < a ∧ c < b ∧ d < b

def Black (L : Set V) : Prop :=
  ∃ a b c d : ℤ, Standard a b c d ∧ span (a, c) (-d, b) = L

def White (L : Set V) : Prop :=
  ∃ a b c d : ℤ, Standard a b c d ∧ span (a, -c) (d, b) = L

def Diagonal (w : V) : Prop := w.1.natAbs = w.2.natAbs

def reflect (w : V) : V := (w.1, -w.2)

def rotate (w : V) : V := (w.2, -w.1)

@[simp] theorem lin_one_zero (u v : V) : lin u v 1 0 = u := by
  rcases u with ⟨x,y⟩
  simp [lin]

@[simp] theorem lin_zero_one (u v : V) : lin u v 0 1 = v := by
  rcases v with ⟨x,y⟩
  simp [lin]

theorem left_mem_span (u v : V) : u ∈ span u v := ⟨1, 0, by simp⟩
theorem right_mem_span (u v : V) : v ∈ span u v := ⟨0, 1, by simp⟩

theorem det_lin (u v : V) (a b c d : ℤ) :
    det (lin u v a b) (lin u v c d) = (a * d - b * c) * det u v := by
  simp only [lin, det]
  ring

theorem lin_lin (u v : V) (a b c d k l : ℤ) :
    lin (lin u v a b) (lin u v c d) k l =
      lin u v (k * a + l * c) (k * b + l * d) := by
  apply Prod.ext <;> simp only [lin] <;> ring

theorem span_change (u v : V) (a b c d : ℤ) (h : a * d - b * c = 1) :
    span (lin u v a b) (lin u v c d) = span u v := by
  ext w
  constructor
  · rintro ⟨k,l,rfl⟩
    exact ⟨k*a+l*c,k*b+l*d,lin_lin u v a b c d k l⟩
  · rintro ⟨k,l,rfl⟩
    refine ⟨d*k-c*l,-b*k+a*l,?_⟩
    rw [lin_lin]
    have h₁ : (d*k-c*l)*a+(-b*k+a*l)*c=k := by
      calc
        _ = k*(a*d-b*c) := by ring
        _ = k := by rw [h]; ring
    have h₂ : (d*k-c*l)*b+(-b*k+a*l)*d=l := by
      calc
        _ = l*(a*d-b*c) := by ring
        _ = l := by rw [h]; ring
    rw [h₁,h₂]

end A368207Lattice

/- A368207HNF -/

namespace A368207Lattice

def Lattice (n : ℕ) :=
  {L : Set V // ∃ u v : V, span u v = L ∧ det u v = (n : ℤ)}

lemma det_dvd_of_span_subset {u v U W : V}
    (h : span u v ⊆ span U W) : det U W ∣ det u v := by
  obtain ⟨a,b,hu⟩ := h (left_mem_span u v)
  obtain ⟨c,d,hv⟩ := h (right_mem_span u v)
  refine ⟨a*d-b*c, ?_⟩
  rw [hu,hv,det_lin]
  ring

lemma det_eq_of_span_eq {u v U W : V} (h : span u v = span U W)
    (huv : 0 ≤ det u v) (hUW : 0 ≤ det U W) : det u v = det U W := by
  exact Int.dvd_antisymm huv hUW
    (det_dvd_of_span_subset h.symm.subset) (det_dvd_of_span_subset h.subset)

lemma exists_hnf (u v : V) (hn : 0 < det u v) :
    ∃ h r g : ℤ, 0 < h ∧ 0 < g ∧ 0 ≤ r ∧ r < h ∧
      h * g = det u v ∧ span (h,0) (r,g) = span u v := by
  rcases u with ⟨x,y⟩
  rcases v with ⟨z,w⟩
  let g : ℤ := Int.gcd y w
  have hg : 0 < g := by
    have hgz : Int.gcd y w ≠ 0 := by
      intro h
      obtain ⟨hy,hw⟩ := Int.gcd_eq_zero_iff.mp h
      simp [det,hy,hw] at hn
    dsimp [g]
    exact_mod_cast Nat.pos_of_ne_zero hgz
  obtain ⟨c,hc⟩ := Int.gcd_dvd_left y w
  obtain ⟨d,hd⟩ := Int.gcd_dvd_right y w
  change y = g*c at hc
  change w = g*d at hd
  let A := Int.gcdA y w
  let B := Int.gcdB y w
  have hbez : g = y*A+w*B := Int.gcd_eq_gcd_ab y w
  have hunit : d*B-(-c)*A=1 := by
    apply mul_left_cancel₀ hg.ne'
    calc
      g*(d*B-(-c)*A) = y*A+w*B := by rw [hc,hd]; ring
      _ = g*1 := by rw [←hbez]; ring
  let h : ℤ := d*x-c*z
  let s : ℤ := A*x+B*z
  have hfirst : lin (x,y) (z,w) d (-c) = (h,0) := by
    apply Prod.ext <;> simp only [lin,h]
    · ring
    · rw [hc,hd]; ring
  have hsecond : lin (x,y) (z,w) A B = (s,g) := by
    apply Prod.ext
    · rfl
    · simpa only [lin,mul_comm] using hbez.symm
  have hspan : span (h,0) (s,g) = span (x,y) (z,w) := by
    simpa only [hfirst,hsecond] using span_change (x,y) (z,w) d (-c) A B hunit
  have hdet : h*g=det (x,y) (z,w) := by
    dsimp [h,det]
    rw [hc,hd]
    ring
  have hh : 0 < h := by
    have hprod : 0 < h*g := by rw [hdet]; exact hn
    rcases mul_pos_iff.mp hprod with hp | hp
    · exact hp.1
    · linarith [hp.2]
  let r := s % h
  have hreduced : lin (h,0) (s,g) (-(s/h)) 1 = (r,g) := by
    apply Prod.ext
    · dsimp [lin,r]
      have he := Int.ediv_mul_add_emod s h
      linarith
    · simp [lin]
  refine ⟨h,r,g,hh,hg,Int.emod_nonneg _ hh.ne',Int.emod_lt_of_pos _ hh,hdet,?_⟩
  calc
    span (h,0) (r,g) = span (h,0) (s,g) := by
      simpa only [lin_one_zero,hreduced] using
        span_change (h,0) (s,g) 1 0 (-(s/h)) 1 (by norm_num)
    _ = span (x,y) (z,w) := hspan

lemma hnf_unique {h r g H R G : ℤ}
    (hh : 0 < h) (hg : 0 < g) (hr : 0 ≤ r) (hrh : r < h)
    (hH : 0 < H) (hG : 0 < G) (hR : 0 ≤ R) (hRH : R < H)
    (heq : span (h,0) (r,g) = span (H,0) (R,G)) :
    h = H ∧ r = R ∧ g = G := by
  have horizontal {a b c A B C : ℤ} (hC : C ≠ 0)
      (hs : span (a,0) (b,c) ⊆ span (A,0) (B,C)) : A ∣ a := by
    obtain ⟨k,l,hkl⟩ := hs (left_mem_span (a,0) (b,c))
    have hy := congrArg Prod.snd hkl
    simp only [lin,mul_zero,zero_add] at hy
    have hl : l=0 := (mul_eq_zero.mp hy.symm).resolve_right hC
    refine ⟨k,?_⟩
    have hx := congrArg Prod.fst hkl
    simpa [lin,hl,mul_comm] using hx
  have hheq : h=H := Int.dvd_antisymm hh.le hH.le
    (horizontal hg.ne' heq.symm.subset) (horizontal hG.ne' heq.subset)
  have vertical {a b c A B C : ℤ}
      (hs : span (a,0) (b,c) ⊆ span (A,0) (B,C)) : C ∣ c := by
    obtain ⟨k,l,hkl⟩ := hs (right_mem_span (a,0) (b,c))
    refine ⟨l,?_⟩
    have hy := congrArg Prod.snd hkl
    simpa only [lin,mul_zero,zero_add,mul_comm] using hy
  have hgeq : g=G := Int.dvd_antisymm hg.le hG.le
    (vertical heq.symm.subset) (vertical heq.subset)
  obtain ⟨k,l,hkl⟩ := heq.subset (right_mem_span (h,0) (r,g))
  have hy := congrArg Prod.snd hkl
  simp only [lin,mul_zero,zero_add,←hgeq] at hy
  have hl : l=1 := by nlinarith
  have hx := congrArg Prod.fst hkl
  simp only [lin,hl,one_mul,←hheq] at hx
  have hm := congrArg (fun t : ℤ => t % h) hx
  have hRmod : R % h = R := Int.emod_eq_of_lt hR (hheq ▸ hRH)
  have hrmod : r % h = r := Int.emod_eq_of_lt hr hrh
  simp [Int.add_emod,Int.mul_emod,hrmod,hRmod] at hm
  exact ⟨hheq,hm,hgeq⟩

lemma lattice_hnf {n : ℕ} (hn : 0 < n) (L : Lattice n) :
    ∃ h r g : ℤ, 0 < h ∧ 0 < g ∧ 0 ≤ r ∧ r < h ∧
      h*g=(n:ℤ) ∧ span (h,0) (r,g)=L.val := by
  obtain ⟨u,v,huv,hdet⟩ := L.property
  have hp : 0 < det u v := by rw [hdet]; exact_mod_cast hn
  obtain ⟨h,r,g,hh,hg,hr,hrh,he,hspan⟩ := exists_hnf u v hp
  exact ⟨h,r,g,hh,hg,hr,hrh,he.trans hdet,hspan.trans huv⟩

end A368207Lattice

/- A368207LatticeCard -/

namespace A368207Lattice

open Finset

abbrev HermiteData (n : ℕ) := Σ d : {d : ℕ // d ∈ n.divisors}, Fin d.val

def hermiteMap {n : ℕ} (t : HermiteData n) : Lattice n :=
  ⟨span ((t.1.val : ℤ),0) ((t.2.val : ℤ),(n/t.1.val : ℕ)),
    ((t.1.val : ℤ),0), ((t.2.val : ℤ),(n/t.1.val : ℕ)), rfl, by
      dsimp [det]
      rw [zero_mul,sub_zero]
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp t.1.property).1⟩

lemma divisor_quotient_pos {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors) :
    0 < n/d := by
  have he := Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
  apply Nat.pos_of_ne_zero
  intro hz
  rw [hz,mul_zero] at he
  exact hn.ne' he.symm

lemma hermiteMap_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (@hermiteMap n) := by
  intro x y hxy
  have hxpos := Nat.pos_of_mem_divisors x.1.property
  have hypos := Nat.pos_of_mem_divisors y.1.property
  have hxq := divisor_quotient_pos hn x.1.property
  have hyq := divisor_quotient_pos hn y.1.property
  have hs := congrArg Subtype.val hxy
  change span ((x.1.val : ℤ),0) ((x.2.val : ℤ),(n/x.1.val : ℕ)) =
    span ((y.1.val : ℤ),0) ((y.2.val : ℤ),(n/y.1.val : ℕ)) at hs
  have he := hnf_unique (by exact_mod_cast hxpos) (by exact_mod_cast hxq)
    (by positivity) (by exact_mod_cast x.2.isLt)
    (by exact_mod_cast hypos) (by exact_mod_cast hyq)
    (by positivity) (by exact_mod_cast y.2.isLt) hs
  have hd : x.1=y.1 := Subtype.ext (Int.natCast_inj.mp he.1)
  cases x with
  | mk d r =>
    cases y with
    | mk e s =>
      dsimp at hd
      subst e
      have hrs : r=s := Fin.ext (Int.natCast_inj.mp he.2.1)
      subst s
      rfl

lemma hermiteMap_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (@hermiteMap n) := by
  intro L
  obtain ⟨h,r,g,hh,hg,hr,hrh,he,hspan⟩ := lattice_hnf hn L
  let d := h.toNat
  have hd : (d : ℤ)=h := Int.toNat_of_nonneg hh.le
  have hgg : (g.toNat : ℤ)=g := Int.toNat_of_nonneg hg.le
  have hrr : (r.toNat : ℤ)=r := Int.toNat_of_nonneg hr
  have hdpos : 0 < d := by omega
  have hprod : d*g.toNat=n := by
    exact_mod_cast (show (d:ℤ)*(g.toNat:ℤ)=(n:ℤ) by rw [hd,hgg]; exact he)
  have hdm : d∈n.divisors := Nat.mem_divisors.mpr ⟨⟨g.toNat,hprod.symm⟩,hn.ne'⟩
  have hdiv : n/d=g.toNat := by rw [←hprod,Nat.mul_div_right _ hdpos]
  have hrlt : r.toNat<d := by omega
  refine ⟨⟨⟨d,hdm⟩,⟨r.toNat,hrlt⟩⟩,?_⟩
  apply Subtype.ext
  change span ((d:ℤ),0) ((r.toNat:ℤ),(n/d:ℕ))=L.val
  rw [hd,hrr,hdiv,hgg]
  exact hspan

noncomputable def hermiteEquiv {n : ℕ} (hn : 0 < n) : HermiteData n ≃ Lattice n :=
  Equiv.ofBijective hermiteMap ⟨hermiteMap_injective hn,hermiteMap_surjective hn⟩

lemma lattice_finite {n : ℕ} (hn : 0 < n) : Finite (Lattice n) :=
  Finite.of_equiv (HermiteData n) (hermiteEquiv hn)

lemma lattice_card {n : ℕ} (hn : 0 < n) :
    Nat.card (Lattice n) = ArithmeticFunction.sigma 1 n := by
  rw [←Nat.card_congr (hermiteEquiv hn), Nat.card_eq_fintype_card]
  simp only [HermiteData,Fintype.card_sigma,Fintype.card_fin]
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.sum_coe_sort n.divisors id

end A368207Lattice

/- A368207Minimum -/

namespace A368207Lattice

@[simp] theorem height_zero_iff (w : V) : height w = 0 ↔ w = (0,0) := by
  rcases w with ⟨x,y⟩
  simp [height]

theorem height_scale (g : ℤ) (w : V) :
    height (g*w.1,g*w.2) = g.natAbs * height w := by
  simp only [height, Int.natAbs_mul]
  exact (mul_max _ _ _).symm

theorem height_cast (w : V) : (height w : ℤ) = max |w.1| |w.2| := by
  simp [height, Nat.cast_max]

theorem minimal_norm_le {L : Set V} {w z : V} (hw : Minimal L w)
    (hz : z ∈ L) (hz0 : z ≠ (0,0)) :
    max |w.1| |w.2| ≤ max |z.1| |z.2| := by
  have h := Int.ofNat_le.mpr (hw.2.2 z hz hz0)
  simpa only [height_cast] using h

theorem exists_minimal {L : Set V} {u v : V}
    (hs : span u v = L) (hd : det u v ≠ 0) : ∃ w, Minimal L w := by
  classical
  have hu0 : u ≠ (0,0) := by
    intro h
    apply hd
    simp [h,det]
  have hu : u ∈ L := hs ▸ left_mem_span u v
  have he : ∃ r : ℕ, ∃ w ∈ L, w ≠ (0,0) ∧ height w = r :=
    ⟨height u,u,hu,hu0,rfl⟩
  obtain ⟨w,hw,hw0,hwr⟩ := Nat.find_spec he
  refine ⟨w,hw,hw0,?_⟩
  intro z hz hz0
  rw [hwr]
  exact Nat.find_min' he ⟨z,hz,hz0,rfl⟩

theorem minimal_coeff_gcd {L : Set V} {u v w : V}
    (hs : span u v = L) (hw : Minimal L w)
    (k l : ℤ) (hkl : w = lin u v k l) : Int.gcd k l = 1 := by
  obtain ⟨k',hk⟩ := Int.gcd_dvd_left k l
  obtain ⟨l',hl⟩ := Int.gcd_dvd_right k l
  let z := lin u v k' l'
  have hz : z ∈ L := hs ▸ (show z ∈ span u v from ⟨k',l',rfl⟩)
  have hwz : w = ((Int.gcd k l:ℤ)*z.1,(Int.gcd k l:ℤ)*z.2) := by
    rw [hkl]
    apply Prod.ext
    · have h₁ := congrArg (fun t : ℤ => t*u.1) hk
      have h₂ := congrArg (fun t : ℤ => t*v.1) hl
      dsimp [lin,z]
      nlinarith only [h₁,h₂]
    · have h₁ := congrArg (fun t : ℤ => t*u.2) hk
      have h₂ := congrArg (fun t : ℤ => t*v.2) hl
      dsimp [lin,z]
      nlinarith only [h₁,h₂]
  have hz0 : z ≠ (0,0) := by
    intro h
    apply hw.2.1
    rw [hwz,h]
    simp
  have hheight : height w = Int.gcd k l * height z := by
    rw [hwz,height_scale]
    simp
  have hpz : 0 < height z := Nat.pos_of_ne_zero ((height_zero_iff z).not.mpr hz0)
  have hpw : 0 < height w := Nat.pos_of_ne_zero ((height_zero_iff w).not.mpr hw.2.1)
  have hm := hw.2.2 z hz hz0
  rw [hheight] at hm hpw
  have hg : 0 < Int.gcd k l := by
    by_contra hg
    have h0 : Int.gcd k l = 0 := by omega
    simp only [h0,zero_mul,lt_self_iff_false] at hpw
  nlinarith

theorem extend_minimal {L : Set V} {u v w : V}
    (hs : span u v = L) (hw : Minimal L w) :
    ∃ z, span w z = L ∧ det w z = det u v := by
  obtain ⟨k,l,hkl⟩ := (show w ∈ span u v by simpa only [hs] using hw.1)
  have hg := minimal_coeff_gcd hs hw k l hkl
  let p := -Int.gcdB k l
  let q := Int.gcdA k l
  have hd : k*q-l*p=1 := by
    have h := Int.gcd_eq_gcd_ab k l
    rw [hg] at h
    dsimp [p,q]
    norm_num at h
    nlinarith only [h]
  refine ⟨lin u v p q,?_,?_⟩
  · rw [hkl,span_change u v k l p q hd,hs]
  · rw [hkl,det_lin,hd,one_mul]

end A368207Lattice

/- A368207Symmetry -/

namespace A368207Lattice

def negV (w : V) : V := (-w.1,-w.2)
def swapV (w : V) : V := (w.2,w.1)

@[simp] theorem negV_negV (w : V) : negV (negV w) = w := by
  rcases w with ⟨x,y⟩; simp [negV]
@[simp] theorem reflect_reflect (w : V) : reflect (reflect w) = w := by
  rcases w with ⟨x,y⟩; simp [reflect]
@[simp] theorem swapV_swapV (w : V) : swapV (swapV w) = w := by
  rcases w with ⟨x,y⟩; rfl

@[simp] theorem height_negV (w : V) : height (negV w) = height w := by simp [height,negV]
@[simp] theorem height_reflect (w : V) : height (reflect w) = height w := by simp [height,reflect]
@[simp] theorem height_swapV (w : V) : height (swapV w) = height w := by simp [height,swapV,max_comm]

theorem image_span (f : V → V)
    (hf : ∀ u v k l, f (lin u v k l) = lin (f u) (f v) k l) (u v : V) :
    f '' span u v = span (f u) (f v) := by
  ext w
  constructor
  · rintro ⟨z,⟨k,l,rfl⟩,rfl⟩
    exact ⟨k,l,hf u v k l⟩
  · rintro ⟨k,l,rfl⟩
    exact ⟨lin u v k l,⟨k,l,rfl⟩,hf u v k l⟩

theorem span_swap (u v : V) : span v u = span u v := by
  ext w
  constructor <;> rintro ⟨k,l,rfl⟩ <;> refine ⟨l,k,?_⟩ <;>
    apply Prod.ext <;> simp [lin,add_comm]

theorem span_neg_right (u v : V) : span u (negV v) = span u v := by
  ext w
  constructor <;> rintro ⟨k,l,rfl⟩ <;> refine ⟨k,-l,?_⟩ <;>
    apply Prod.ext <;> simp [lin,negV]

theorem span_neg_left (u v : V) : span (negV u) v = span u v := by
  rw [span_swap,span_neg_right,span_swap]

theorem span_neg_both (u v : V) : span (negV u) (negV v) = span u v := by
  rw [span_neg_left,span_neg_right]

theorem image_negV_span (u v : V) : negV '' span u v = span u v := by
  rw [image_span negV (by intros; apply Prod.ext <;> simp [negV,lin] <;> ring),
    span_neg_both]

theorem image_reflect_span (u v : V) :
    reflect '' span u v = span (reflect u) (reflect v) :=
  image_span reflect (by intros; apply Prod.ext <;> simp [reflect,lin] <;> ring) u v

theorem image_swapV_span (u v : V) :
    swapV '' span u v = span (swapV u) (swapV v) :=
  image_span swapV (by intros; rfl) u v

@[simp] theorem image_reflect_reflect (L : Set V) : reflect '' (reflect '' L) = L := by
  simp [Set.image_image]

@[simp] theorem image_swapV_swapV (L : Set V) : swapV '' (swapV '' L) = L := by
  simp [Set.image_image]

theorem minimal_image {L : Set V} {w : V} (hw : Minimal L w)
    (f : V → V) (hf : Function.Involutive f) (h0 : f (0,0) = (0,0))
    (hh : ∀ z, height (f z) = height z) : Minimal (f '' L) (f w) := by
  refine ⟨⟨w,hw.1,rfl⟩,?_,?_⟩
  · intro h
    exact hw.2.1 (hf.injective (h.trans h0.symm))
  · rintro z ⟨x,hx,rfl⟩ hx0
    have hxn : x ≠ (0,0) := by intro h; apply hx0; simpa only [h] using h0
    simpa only [hh] using hw.2.2 x hx hxn

theorem minimal_negV {L : Set V} {u v w : V}
    (hs : span u v = L) (hw : Minimal L w) : Minimal L (negV w) := by
  have h := minimal_image hw negV negV_negV rfl height_negV
  have he : negV '' L = L := by rw [← hs,image_negV_span]
  simpa only [he] using h

theorem minimal_reflect {L : Set V} {w : V} (hw : Minimal L w) :
    Minimal (reflect '' L) (reflect w) :=
  minimal_image hw reflect reflect_reflect rfl height_reflect

theorem minimal_swapV {L : Set V} {w : V} (hw : Minimal L w) :
    Minimal (swapV '' L) (swapV w) :=
  minimal_image hw swapV swapV_swapV rfl height_swapV

theorem black_reflect {L : Set V} (h : Black L) : White (reflect '' L) := by
  obtain ⟨a,b,c,d,hs,hspan⟩ := h
  refine ⟨a,b,c,d,hs,?_⟩
  rw [← hspan,image_reflect_span]
  change span (a,-c) (d,b) = span (a,-c) (negV (d,b))
  rw [span_neg_right]

theorem white_reflect {L : Set V} (h : White L) : Black (reflect '' L) := by
  obtain ⟨a,b,c,d,hs,hspan⟩ := h
  refine ⟨a,b,c,d,hs,?_⟩
  rw [← hspan,image_reflect_span]
  simp only [reflect,neg_neg]
  simpa only [negV,neg_neg] using (span_neg_right (a,c) (-d,b)).symm

theorem standard_swap {a b c d : ℤ} (h : Standard a b c d) : Standard b a d c :=
  ⟨h.2.1,h.1,h.2.2.2.2.2,h.2.2.2.2.1,h.2.2.2.1,h.2.2.1⟩

theorem black_swapV {L : Set V} (h : Black L) : White (swapV '' L) := by
  obtain ⟨a,b,c,d,hs,hspan⟩ := h
  refine ⟨b,a,d,c,standard_swap hs,?_⟩
  rw [← hspan,image_swapV_span]
  exact span_swap _ _

theorem white_swapV {L : Set V} (h : White L) : Black (swapV '' L) := by
  obtain ⟨a,b,c,d,hs,hspan⟩ := h
  refine ⟨b,a,d,c,standard_swap hs,?_⟩
  rw [← hspan,image_swapV_span]
  exact span_swap _ _

theorem reflect_basis {L : Set V} {u v : V} (hs : span u v = L) :
    span (reflect v) (reflect u) = reflect '' L ∧
      det (reflect v) (reflect u) = det u v := by
  constructor
  · rw [span_swap,← image_reflect_span,hs]
  · simp only [det,reflect]; ring

theorem swapV_basis {L : Set V} {u v : V} (hs : span u v = L) :
    span (swapV v) (swapV u) = swapV '' L ∧
      det (swapV v) (swapV u) = det u v := by
  constructor
  · rw [span_swap,← image_swapV_span,hs]
  · simp only [det,swapV]; ring

end A368207Lattice

/- A368207BalancedUnique -/

-- uses note #151612

/-!
Algebraic uniqueness of a balanced basis of a rank-two integral lattice.
Context: Roland Bacher, arXiv:2210.07657, windmill-basis uniqueness.
This helper does not prove the A368207 counting identity.
-/

namespace BacherResearch

theorem balanced_basis_unique
    {a b c d A B C D α β γ δ : ℤ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbal : max c d < min a b) (hBal : max C D < min A B)
    (hAeq : A = a * α - d * β) (hCeq : C = c * α + b * β)
    (hDeq : D = d * δ - a * γ) (hBeq : B = c * γ + b * δ)
    (hdet : α * δ - β * γ = 1) :
    α = 1 ∧ β = 0 ∧ γ = 0 ∧ δ = 1 := by
  simp only [max_lt_iff, lt_min_iff] at hbal hBal
  obtain ⟨⟨hca, hda⟩, hcb, hdb⟩ := hbal
  obtain ⟨⟨hCA, hDA⟩, hCB, hDB⟩ := hBal
  have ha : 0 < a := lt_of_le_of_lt hc hca
  have hb : 0 < b := lt_of_le_of_lt hc hcb
  have hAA : 0 < A := lt_of_le_of_lt hC hCA
  have hBB : 0 < B := lt_of_le_of_lt hC hCB
  have hn : 0 < a * b + c * d := by positivity
  have haeq : (a * b + c * d) * α = b * A + d * C := by
    rw [hAeq, hCeq]; ring
  have hdeq : (a * b + c * d) * δ = c * D + a * B := by
    rw [hDeq, hBeq]; ring
  have hα : 0 < α := by
    have : 0 < (a * b + c * d) * α := by rw [haeq]; positivity
    exact pos_of_mul_pos_right this hn.le
  have hδ : 0 < δ := by
    have : 0 < (a * b + c * d) * δ := by rw [hdeq]; positivity
    exact pos_of_mul_pos_right this hn.le
  have hcInv : c = δ * C - β * B := by
    rw [hCeq, hBeq]
    linear_combination -c * hdet
  have hdInv : d = γ * A + α * D := by
    rw [hAeq, hDeq]
    linear_combination -d * hdet
  have hprod : β * γ = 0 := by
    have hp : 0 ≤ β * γ := by have := mul_pos hα hδ; omega
    by_contra he
    have hp' : 0 < β * γ := lt_of_le_of_ne hp (Ne.symm he)
    rcases mul_pos_iff.mp hp' with ⟨hβ, hγ⟩ | ⟨hβ, hγ⟩
    · have hcb' : b ≤ C := by
        nlinarith only [hCeq, mul_nonneg hc hα.le,
          mul_nonneg hb.le (show 0 ≤ β - 1 by omega)]
      have had : A ≤ d := by
        nlinarith only [hdInv, mul_nonneg hα.le hD,
          mul_nonneg (show 0 ≤ γ - 1 by omega) hAA.le]
      omega
    · have hac : a ≤ D := by
        nlinarith only [hDeq, mul_nonneg hd hδ.le,
          mul_nonneg ha.le (show 0 ≤ -γ - 1 by omega)]
      have hbc : B ≤ c := by
        nlinarith only [hcInv, mul_nonneg hδ.le hC,
          mul_nonneg (show 0 ≤ -β - 1 by omega) hBB.le]
      omega
  have hα1 : α = 1 := by
    nlinarith only [hdet, hprod, hα, hδ,
      mul_nonneg (show 0 ≤ α - 1 by omega) (show 0 ≤ δ - 1 by omega)]
  have hδ1 : δ = 1 := by rw [hα1, one_mul, hprod, sub_zero] at hdet; exact hdet
  simp only [hα1, hδ1, mul_one] at hAeq hCeq hDeq hBeq
  rcases mul_eq_zero.mp hprod with hβ | hγ
  · have hγ0 : γ = 0 := by
      simp only [hβ, mul_zero, sub_zero, add_zero] at hAeq hCeq
      rcases lt_trichotomy γ 0 with h | h | h
      · nlinarith only [hAeq, hDeq, hDA, hd,
          mul_nonneg ha.le (show 0 ≤ -γ - 1 by omega)]
      · exact h
      · nlinarith only [hDeq, hda, hD,
          mul_nonneg ha.le (show 0 ≤ γ - 1 by omega)]
    exact ⟨hα1, hβ, hγ0, hδ1⟩
  · have hβ0 : β = 0 := by
      simp only [hγ, mul_zero, sub_zero, zero_add] at hDeq hBeq
      rcases lt_trichotomy β 0 with h | h | h
      · nlinarith only [hCeq, hcb, hC,
          mul_nonneg hb.le (show 0 ≤ -β - 1 by omega)]
      · exact h
      · nlinarith only [hCeq, hBeq, hCB, hc,
          mul_nonneg hb.le (show 0 ≤ β - 1 by omega)]
    exact ⟨hα1, hβ0, hγ, hδ1⟩

end BacherResearch

/- A368207Axes -/

namespace A368207Axes

open A368207Lattice

def Horizontal (L : Set V) : Prop :=
  ∃ a b d : ℤ, 0 ≤ d ∧ d < a ∧ d < b ∧
    (d = 0 ∨ a - d < b) ∧ span (a,0) (-d,b) = L

def Vertical (L : Set V) : Prop :=
  ∃ a b c : ℤ, 0 ≤ c ∧ c < a ∧ c < b ∧
    (c = 0 ∨ b - c < a) ∧ span (a,c) (0,b) = L

def Rectangular (L : Set V) : Prop :=
  ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ span (a,0) (0,b) = L

lemma standard_pos {a b c d : ℤ} (h : Standard a b c d) : 0 < a ∧ 0 < b :=
  ⟨lt_of_le_of_lt h.1 h.2.2.1, lt_of_le_of_lt h.1 h.2.2.2.2.1⟩

lemma standard_det_pos {a b c d : ℤ} (h : Standard a b c d) :
    0 < det (a,c) (-d,b) := by
  obtain ⟨ha,hb⟩ := standard_pos h
  have hc := h.1
  have hd := h.2.1
  simp only [det]
  nlinarith only [mul_pos ha hb, mul_nonneg hc hd]

lemma white_det_pos {a b c d : ℤ} (h : Standard a b c d) :
    0 < det (a,-c) (d,b) := by
  simpa only [det,neg_mul,mul_neg,sub_neg_eq_add] using standard_det_pos h

lemma transition_of_span_eq {u v U W : V} (hs : span u v = span U W)
    (huv : 0 < det u v) (hUW : 0 < det U W) :
    ∃ α β γ δ : ℤ, U = lin u v α β ∧ W = lin u v γ δ ∧ α*δ-β*γ=1 := by
  obtain ⟨α,β,hU⟩ := (show U ∈ span u v by rw [hs]; exact left_mem_span U W)
  obtain ⟨γ,δ,hW⟩ := (show W ∈ span u v by rw [hs]; exact right_mem_span U W)
  refine ⟨α,β,γ,δ,hU,hW,?_⟩
  have heq := det_eq_of_span_eq hs huv.le hUW.le
  apply mul_right_cancel₀ huv.ne'
  rw [one_mul,← det_lin,← hU,← hW,heq]

-- Uses the public balanced-basis uniqueness helper from desk note #151612.
lemma standard_basis_unique {a b c d A B C D : ℤ}
    (h : Standard a b c d) (H : Standard A B C D)
    (hs : span (a,c) (-d,b) = span (A,C) (-D,B)) :
    a = A ∧ b = B ∧ c = C ∧ d = D := by
  obtain ⟨α,β,γ,δ,hU,hW,hdet⟩ := transition_of_span_eq hs
    (standard_det_pos h) (standard_det_pos H)
  have hAeq : A = a*α-d*β := by
    have hh := congrArg Prod.fst hU
    dsimp [lin] at hh
    nlinarith only [hh]
  have hCeq : C = c*α+b*β := by
    have hh := congrArg Prod.snd hU
    dsimp [lin] at hh
    nlinarith only [hh]
  have hDeq : D = d*δ-a*γ := by
    have hh := congrArg Prod.fst hW
    dsimp [lin] at hh
    nlinarith only [hh]
  have hBeq : B = c*γ+b*δ := by
    have hh := congrArg Prod.snd hW
    dsimp [lin] at hh
    nlinarith only [hh]
  have hbal : max c d < min a b :=
    lt_min_iff.mpr ⟨max_lt_iff.mpr ⟨h.2.2.1,h.2.2.2.1⟩,
      max_lt_iff.mpr ⟨h.2.2.2.2.1,h.2.2.2.2.2⟩⟩
  have hBal : max C D < min A B :=
    lt_min_iff.mpr ⟨max_lt_iff.mpr ⟨H.2.2.1,H.2.2.2.1⟩,
      max_lt_iff.mpr ⟨H.2.2.2.2.1,H.2.2.2.2.2⟩⟩
  obtain ⟨hα,hβ,hγ,hδ⟩ := BacherResearch.balanced_basis_unique
    h.1 h.2.1 H.1 H.2.1 hbal hBal hAeq hCeq hDeq hBeq hdet
  simp only [hα,hβ,hγ,hδ,mul_one,mul_zero,sub_zero,zero_add,add_zero] at hAeq hCeq hDeq hBeq
  exact ⟨hAeq.symm,hBeq.symm,hCeq.symm,hDeq.symm⟩

lemma opposite_transition {a b c d A B C D α β γ δ : ℤ}
    (h : Standard a b c d) (H : Standard A B C D)
    (hAeq : A = a*α-d*β) (hCeq : -C = c*α+b*β)
    (hDeq : D = a*γ-d*δ) (hBeq : B = c*γ+b*δ)
    (hdet : α*δ-β*γ=1) : α=1 ∧ δ=1 ∧ (β=0 ∨ γ=0) := by
  obtain ⟨ha,hb⟩ := standard_pos h
  obtain ⟨hA,hB⟩ := standard_pos H
  rcases h with ⟨hc,hd,hca,hda,hcb,hdb⟩
  rcases H with ⟨hC,hD,hCA,hDA,hCB,hDB⟩
  have hn : 0 < a*b+c*d := by positivity
  have hαeq : (a*b+c*d)*α=b*A-d*C := by
    linear_combination -b*hAeq-d*hCeq
  have hδeq : (a*b+c*d)*δ=a*B-c*D := by
    linear_combination -a*hBeq+c*hDeq
  have hβeq : (a*b+c*d)*β= -c*A-a*C := by
    linear_combination c*hAeq-a*hCeq
  have hγeq : (a*b+c*d)*γ=b*D+d*B := by
    linear_combination -b*hDeq-d*hBeq
  have hα : 0 < α := by
    apply pos_of_mul_pos_right (a := a*b+c*d) _ hn.le
    rw [hαeq]
    nlinarith only [mul_pos hb (sub_pos.mpr hCA),
      mul_nonneg (sub_nonneg.mpr hdb.le) hC]
  have hδ : 0 < δ := by
    apply pos_of_mul_pos_right (a := a*b+c*d) _ hn.le
    rw [hδeq]
    nlinarith only [mul_pos ha (sub_pos.mpr hDB),
      mul_nonneg (sub_nonneg.mpr hca.le) hD]
  have hβ : β ≤ 0 := by
    apply nonpos_of_mul_nonpos_right (a := a*b+c*d) _ hn
    rw [hβeq]
    nlinarith only [mul_nonneg hc hA.le,mul_nonneg ha.le hC]
  have hγ : 0 ≤ γ := by
    apply nonneg_of_mul_nonneg_right (a := a*b+c*d) _ hn
    rw [hγeq]
    positivity
  have hβγ : β*γ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hβ hγ
  have hα1 : α=1 := by
    nlinarith only [hdet,hβγ,hα,mul_nonneg hα.le (show 0 ≤ δ-1 by omega)]
  have hδ1 : δ=1 := by
    nlinarith only [hdet,hβγ,hδ,mul_nonneg hδ.le (show 0 ≤ α-1 by omega)]
  have hzero : β*γ=0 := by nlinarith only [hdet,hα1,hδ1]
  exact ⟨hα1,hδ1,mul_eq_zero.mp hzero⟩

lemma black_white_axes {L : Set V} (hb : Black L) (hw : White L) :
    Horizontal L ∨ Vertical L := by
  obtain ⟨a,b,c,d,hstd,hspan⟩ := hb
  obtain ⟨A,B,C,D,Hstd,Hspan⟩ := hw
  have hsame := hspan.trans Hspan.symm
  obtain ⟨α,β,γ,δ,hU,hW,hdet⟩ := transition_of_span_eq hsame
    (standard_det_pos hstd) (white_det_pos Hstd)
  have hAeq : A = a*α-d*β := by
    have hh := congrArg Prod.fst hU
    dsimp [lin] at hh
    nlinarith only [hh]
  have hCeq : -C = c*α+b*β := by
    have hh := congrArg Prod.snd hU
    dsimp [lin] at hh
    nlinarith only [hh]
  have hDeq : D = a*γ-d*δ := by
    have hh := congrArg Prod.fst hW
    dsimp [lin] at hh
    nlinarith only [hh]
  have hBeq : B = c*γ+b*δ := by
    have hh := congrArg Prod.snd hW
    dsimp [lin] at hh
    nlinarith only [hh]
  obtain ⟨hα,hδ,hcases⟩ := opposite_transition hstd Hstd hAeq hCeq hDeq hBeq hdet
  obtain ⟨ha,hb⟩ := standard_pos hstd
  rcases hstd with ⟨hc,hd,hca,hda,hcb,hdb⟩
  rcases Hstd with ⟨hC,hD,hCA,hDA,hCB,hDB⟩
  simp only [hα,hδ,mul_one] at hAeq hCeq hDeq hBeq
  rcases hcases with hβ | hγ
  · have hc0 : c=0 := by simp only [hβ,mul_zero,add_zero] at hCeq; omega
    have hB : B=b := by simpa only [hc0,zero_mul,zero_add] using hBeq
    refine Or.inl ⟨a,b,d,hd,hda,hdb,?_,?_⟩
    · by_cases hd0 : d=0
      · exact Or.inl hd0
      · right
        have hdpos : 0 < d := by omega
        have hγpos : 0 < γ := by
          apply pos_of_mul_pos_right (a := a) _ ha.le
          nlinarith only [hDeq,hD,hdpos]
        have hp := mul_nonneg ha.le (show 0 ≤ γ-1 by omega)
        nlinarith only [hDeq,hDB,hB,hp]
    · simpa only [hc0] using hspan
  · have hd0 : d=0 := by simp only [hγ,mul_zero,zero_sub] at hDeq; omega
    have hA : A=a := by simpa only [hd0,zero_mul,sub_zero] using hAeq
    refine Or.inr ⟨a,b,c,hc,hca,hcb,?_,?_⟩
    · by_cases hc0 : c=0
      · exact Or.inl hc0
      · right
        have hcpos : 0 < c := by omega
        have hβneg : β < 0 := by
          by_contra hh
          have hp := mul_nonneg hb.le (show 0 ≤ β by omega)
          nlinarith only [hCeq,hC,hcpos,hp]
        have hp := mul_nonneg hb.le (show 0 ≤ -β-1 by omega)
        nlinarith only [hCeq,hCA,hA,hp]
    · simpa only [hd0,neg_zero] using hspan

lemma horizontal_colored {L : Set V} (h : Horizontal L) : Black L ∧ White L := by
  obtain ⟨a,b,d,hd,hda,hdb,hcond,hspan⟩ := h
  have ha : 0<a := lt_of_le_of_lt hd hda
  have hb : 0<b := lt_of_le_of_lt hd hdb
  have hblack : Black L := ⟨a,b,0,d,⟨le_rfl,hd,ha,hda,hb,hdb⟩,hspan⟩
  refine ⟨hblack,?_⟩
  by_cases hd0 : d=0
  · refine ⟨a,b,0,0,⟨le_rfl,le_rfl,ha,ha,hb,hb⟩,?_⟩
    simpa only [hd0,neg_zero] using hspan
  · have hbound : a-d<b := hcond.resolve_left hd0
    have hstd : Standard a b 0 (a-d) := by
      refine ⟨le_rfl,by omega,ha,by omega,hb,hbound⟩
    refine ⟨a,b,0,a-d,hstd,?_⟩
    have hchange := span_change (a,0) (-d,b) 1 0 1 1 (by ring)
    have hcol : lin (a,0) (-d,b) 1 1 = (a-d,b) := by
      apply Prod.ext <;> simp [lin,sub_eq_add_neg]
    rw [lin_one_zero,hcol] at hchange
    simpa only [neg_zero] using hchange.trans hspan

lemma vertical_colored {L : Set V} (h : Vertical L) : Black L ∧ White L := by
  obtain ⟨a,b,c,hc,hca,hcb,hcond,hspan⟩ := h
  have ha : 0<a := lt_of_le_of_lt hc hca
  have hb : 0<b := lt_of_le_of_lt hc hcb
  have hblack : Black L := by
    refine ⟨a,b,c,0,⟨hc,le_rfl,hca,ha,hcb,hb⟩,?_⟩
    simpa only [neg_zero] using hspan
  refine ⟨hblack,?_⟩
  by_cases hc0 : c=0
  · refine ⟨a,b,0,0,⟨le_rfl,le_rfl,ha,ha,hb,hb⟩,?_⟩
    simpa only [hc0,neg_zero] using hspan
  · have hbound : b-c<a := hcond.resolve_left hc0
    have hstd : Standard a b (b-c) 0 := by
      refine ⟨by omega,le_rfl,hbound,ha,by omega,hb⟩
    refine ⟨a,b,b-c,0,hstd,?_⟩
    have hchange := span_change (a,c) (0,b) 1 (-1) 0 1 (by ring)
    have hcol : lin (a,c) (0,b) 1 (-1) = (a,-(b-c)) := by
      apply Prod.ext <;> simp [lin,sub_eq_add_neg]
    rw [hcol,lin_zero_one] at hchange
    exact hchange.trans hspan

theorem colored_intersection_iff (L : Set V) :
    (Black L ∧ White L) ↔ Horizontal L ∨ Vertical L := by
  constructor
  · rintro ⟨hb,hw⟩
    exact black_white_axes hb hw
  · rintro (hh | hv)
    · exact horizontal_colored hh
    · exact vertical_colored hv

lemma rectangular_axes {L : Set V} (h : Rectangular L) : Horizontal L ∧ Vertical L := by
  obtain ⟨a,b,ha,hb,hspan⟩ := h
  constructor
  · refine ⟨a,b,0,le_rfl,ha,hb,Or.inl rfl,?_⟩
    simpa only [neg_zero] using hspan
  · exact ⟨a,b,0,le_rfl,ha,hb,Or.inl rfl,hspan⟩

theorem axes_intersection_iff (L : Set V) :
    (Horizontal L ∧ Vertical L) ↔ Rectangular L := by
  constructor
  · rintro ⟨hh,hv⟩
    obtain ⟨a,b,d,hd,hda,hdb,_,hspan⟩ := hh
    obtain ⟨A,B,c,hc,hcA,hcB,_,Hspan⟩ := hv
    have ha : 0<a := lt_of_le_of_lt hd hda
    have hb : 0<b := lt_of_le_of_lt hd hdb
    have hA : 0<A := lt_of_le_of_lt hc hcA
    have hB : 0<B := lt_of_le_of_lt hc hcB
    have hstd : Standard a b 0 d := ⟨le_rfl,hd,ha,hda,hb,hdb⟩
    have Hstd : Standard A B c 0 := ⟨hc,le_rfl,hcA,hA,hcB,hB⟩
    have hs : span (a,0) (-d,b) = span (A,c) (-0,B) := by
      simpa only [neg_zero] using hspan.trans Hspan.symm
    have hd0 := (standard_basis_unique hstd Hstd hs).2.2.2
    refine ⟨a,b,ha,hb,?_⟩
    simpa only [hd0,neg_zero] using hspan
  · exact rectangular_axes

def unrotate (w : V) : V := (-w.2,w.1)

@[simp] lemma unrotate_rotate (w : V) : unrotate (rotate w) = w := by
  rcases w with ⟨x,y⟩
  simp [unrotate,rotate]

@[simp] lemma rotate_unrotate (w : V) : rotate (unrotate w) = w := by
  rcases w with ⟨x,y⟩
  simp [unrotate,rotate]

lemma image_rotate_span (u v : V) :
    rotate '' span u v = span (rotate u) (rotate v) :=
  image_span rotate (by
    intros
    apply Prod.ext
    · rfl
    · simp only [rotate,lin]; ring) u v

lemma image_unrotate_span (u v : V) :
    unrotate '' span u v = span (unrotate u) (unrotate v) :=
  image_span unrotate (by
    intros
    apply Prod.ext
    · simp only [unrotate,lin]; ring
    · rfl) u v

@[simp] lemma image_unrotate_rotate (L : Set V) : unrotate '' (rotate '' L) = L := by
  simp [Set.image_image]

@[simp] lemma image_rotate_unrotate (L : Set V) : rotate '' (unrotate '' L) = L := by
  simp [Set.image_image]

lemma horizontal_rotate {L : Set V} (h : Horizontal L) : Vertical (rotate '' L) := by
  obtain ⟨a,b,d,hd,hda,hdb,hcond,hspan⟩ := h
  refine ⟨b,a,d,hd,hdb,hda,hcond,?_⟩
  rw [← hspan,image_rotate_span]
  simp only [rotate,neg_neg]
  exact (span_swap (0,a) (b,d)).trans
    (by simpa only [negV,neg_zero] using (span_neg_left (0,a) (b,d)).symm)

lemma vertical_unrotate {L : Set V} (h : Vertical L) : Horizontal (unrotate '' L) := by
  obtain ⟨a,b,c,hc,hca,hcb,hcond,hspan⟩ := h
  refine ⟨b,a,c,hc,hcb,hca,hcond,?_⟩
  rw [← hspan,image_unrotate_span]
  change span (b,0) (-c,a) = span (-c,a) (negV (b,0))
  rw [span_neg_right,span_swap]

theorem horizontal_rotate_iff (L : Set V) : Horizontal L ↔ Vertical (rotate '' L) := by
  constructor
  · exact horizontal_rotate
  · intro h
    simpa only [image_unrotate_rotate] using vertical_unrotate h

lemma det_rotate (u v : V) : det (rotate u) (rotate v) = det u v := by
  simp only [det,rotate]
  ring

lemma det_unrotate (u v : V) : det (unrotate u) (unrotate v) = det u v := by
  simp only [det,unrotate]
  ring

def rotateMap {n : ℕ} : Lattice n ≃ Lattice n where
  toFun L := ⟨rotate '' L.val,by
    obtain ⟨u,v,hspan,hdet⟩ := L.property
    exact ⟨rotate u,rotate v,by rw [← image_rotate_span,hspan],by rw [det_rotate,hdet]⟩⟩
  invFun L := ⟨unrotate '' L.val,by
    obtain ⟨u,v,hspan,hdet⟩ := L.property
    exact ⟨unrotate u,unrotate v,by rw [← image_unrotate_span,hspan],by rw [det_unrotate,hdet]⟩⟩
  left_inv L := Subtype.ext (image_unrotate_rotate L.val)
  right_inv L := Subtype.ext (image_rotate_unrotate L.val)

@[simp] theorem rotateMap_val {n : ℕ} (L : Lattice n) :
    (rotateMap L).val = rotate '' L.val := rfl

theorem horizontal_rotateMap_iff {n : ℕ} (L : Lattice n) :
    Horizontal L.val ↔ Vertical (rotateMap L).val := horizontal_rotate_iff L.val

end A368207Axes

/- A368207LatticeReflection -/

namespace A368207Lattice

def latticeReflect {n : ℕ} (L : Lattice n) : Lattice n :=
  ⟨reflect '' L.val, by
    obtain ⟨u, v, hs, hd⟩ := L.property
    obtain ⟨hsp, hdet⟩ := reflect_basis hs
    exact ⟨reflect v, reflect u, hsp, hdet.trans hd⟩⟩

@[simp] theorem latticeReflect_val {n : ℕ} (L : Lattice n) :
    (latticeReflect L).val = reflect '' L.val := rfl

@[simp] theorem latticeReflect_latticeReflect {n : ℕ} (L : Lattice n) :
    latticeReflect (latticeReflect L) = L := by
  apply Subtype.ext
  exact image_reflect_reflect L.val

def latticeReflectEquiv (n : ℕ) : Lattice n ≃ Lattice n where
  toFun := latticeReflect
  invFun := latticeReflect
  left_inv := latticeReflect_latticeReflect
  right_inv := latticeReflect_latticeReflect

@[simp] theorem latticeReflectEquiv_apply (n : ℕ) (L : Lattice n) :
    latticeReflectEquiv n L = latticeReflect L := rfl

theorem latticeReflect_injective (n : ℕ) :
    Function.Injective (@latticeReflect n) := (latticeReflectEquiv n).injective

@[simp] theorem black_latticeReflect_iff {n : ℕ} (L : Lattice n) :
    Black (latticeReflect L).val ↔ White L.val := by
  constructor
  · intro h
    simpa only [latticeReflect_val, image_reflect_reflect] using black_reflect h
  · exact white_reflect

@[simp] theorem white_latticeReflect_iff {n : ℕ} (L : Lattice n) :
    White (latticeReflect L).val ↔ Black L.val := by
  constructor
  · intro h
    simpa only [latticeReflect_val, image_reflect_reflect] using white_reflect h
  · exact black_reflect

end A368207Lattice

/- A368207BlackCard -/

namespace A368207Lattice

open Finset A368207Axes

def representations (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1)).filter
    (fun q => q.1 * q.2.1 + q.2.2.1 * q.2.2.2 = n ∧
      max q.1 q.2.1 < min q.2.2.1 q.2.2.2))

abbrev Representation (n : ℕ) := {q // q ∈ representations n}
abbrev BlackLattices (n : ℕ) := {L : Lattice n // Black L.val}
abbrev WhiteLattices (n : ℕ) := {L : Lattice n // White L.val}

lemma mem_representations {n : ℕ} {q : ℕ × ℕ × ℕ × ℕ} :
    q ∈ representations n ↔
    (q.1 ≤ n ∧ q.2.1 ≤ n ∧ q.2.2.1 ≤ n ∧ q.2.2.2 ≤ n) ∧
    q.1*q.2.1+q.2.2.1*q.2.2.2=n ∧ max q.1 q.2.1 < min q.2.2.1 q.2.2.2 := by
  simp [representations]

lemma representation_standard {n : ℕ} (q : Representation n) :
    Standard (q.val.2.2.1 : ℤ) (q.val.2.2.2 : ℤ) (q.val.1 : ℤ) (q.val.2.1 : ℤ) := by
  have h := (mem_representations.mp q.property).2.2
  have hy := max_lt_iff.mp (lt_min_iff.mp h).1
  have hz := max_lt_iff.mp (lt_min_iff.mp h).2
  refine ⟨by positivity,by positivity,?_,?_,?_,?_⟩
  · exact_mod_cast hy.1
  · exact_mod_cast hy.2
  · exact_mod_cast hz.1
  · exact_mod_cast hz.2

def representationLattice {n : ℕ} (q : Representation n) : Lattice n :=
  ⟨span ((q.val.2.2.1 : ℤ),(q.val.1 : ℤ)) (-(q.val.2.1 : ℤ),(q.val.2.2.2 : ℤ)),
    ((q.val.2.2.1 : ℤ),(q.val.1 : ℤ)), (-(q.val.2.1 : ℤ),(q.val.2.2.2 : ℤ)),rfl,by
      have he := (mem_representations.mp q.property).2.1
      simp only [det,mul_neg,sub_neg_eq_add]
      rw [add_comm]
      exact_mod_cast he⟩

def representationBlack {n : ℕ} (q : Representation n) : BlackLattices n :=
  ⟨representationLattice q,q.val.2.2.1,q.val.2.2.2,q.val.1,q.val.2.1,
    representation_standard q,rfl⟩

lemma representationBlack_injective (n : ℕ) :
    Function.Injective (@representationBlack n) := by
  intro x y heq
  have hs := congrArg (fun L : BlackLattices n => L.val.val) heq
  change span ((x.val.2.2.1 : ℤ),(x.val.1 : ℤ)) (-(x.val.2.1 : ℤ),(x.val.2.2.2 : ℤ)) =
    span ((y.val.2.2.1 : ℤ),(y.val.1 : ℤ)) (-(y.val.2.1 : ℤ),(y.val.2.2.2 : ℤ)) at hs
  have h := standard_basis_unique (representation_standard x) (representation_standard y) hs
  apply Subtype.ext
  apply Prod.ext
  · exact Int.natCast_inj.mp h.2.2.1
  · apply Prod.ext
    · exact Int.natCast_inj.mp h.2.2.2
    · exact Prod.ext (Int.natCast_inj.mp h.1) (Int.natCast_inj.mp h.2.1)

lemma representationBlack_surjective {n : ℕ} (_hn : 0 < n) :
    Function.Surjective (@representationBlack n) := by
  intro L
  obtain ⟨a,b,c,d,hstd,hspan⟩ := L.property
  obtain ⟨u,v,huv,hdet⟩ := L.val.property
  obtain ⟨ha,hb⟩ := standard_pos hstd
  have hc := hstd.1
  have hd := hstd.2.1
  have hnz : 0 ≤ det u v := by rw [hdet]; positivity
  have hprod : a*b+c*d=(n:ℤ) := by
    have he := det_eq_of_span_eq (hspan.trans huv.symm) (standard_det_pos hstd).le hnz
    rw [hdet] at he
    simpa only [det,mul_neg,sub_neg_eq_add] using he
  rcases hstd with ⟨hc0,hd0,hca,hda,hcb,hdb⟩
  have haN : (a.toNat : ℤ)=a := Int.toNat_of_nonneg ha.le
  have hbN : (b.toNat : ℤ)=b := Int.toNat_of_nonneg hb.le
  have hcN : (c.toNat : ℤ)=c := Int.toNat_of_nonneg hc
  have hdN : (d.toNat : ℤ)=d := Int.toNat_of_nonneg hd
  have hprodN : c.toNat*d.toNat+a.toNat*b.toNat=n := by
    exact_mod_cast (show (c.toNat:ℤ)*(d.toNat:ℤ)+(a.toNat:ℤ)*(b.toNat:ℤ)=(n:ℤ) by
      rw [haN,hbN,hcN,hdN,add_comm]; exact hprod)
  have ha_bound : a ≤ (n:ℤ) := by
    nlinarith only [hprod,mul_nonneg hc hd,mul_nonneg ha.le (show 0 ≤ b-1 by omega)]
  have hb_bound : b ≤ (n:ℤ) := by
    nlinarith only [hprod,mul_nonneg hc hd,mul_nonneg hb.le (show 0 ≤ a-1 by omega)]
  have hq : (c.toNat,d.toNat,a.toNat,b.toNat) ∈ representations n := by
    apply mem_representations.mpr
    dsimp only
    refine ⟨⟨?_,?_,?_,?_⟩,hprodN,?_⟩
    · omega
    · omega
    · omega
    · omega
    · apply lt_min_iff.mpr
      constructor <;> apply max_lt_iff.mpr <;> constructor <;> omega
  refine ⟨⟨(c.toNat,d.toNat,a.toNat,b.toNat),hq⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change span ((a.toNat:ℤ),(c.toNat:ℤ)) (-(d.toNat:ℤ),(b.toNat:ℤ))=L.val.val
  rw [haN,hbN,hcN,hdN]
  exact hspan

noncomputable def representationBlackEquiv {n : ℕ} (hn : 0 < n) :
    Representation n ≃ BlackLattices n :=
  Equiv.ofBijective representationBlack
    ⟨representationBlack_injective n,representationBlack_surjective hn⟩

lemma black_lattices_card {n : ℕ} (hn : 0 < n) :
    Nat.card (BlackLattices n) = (representations n).card := by
  rw [←Nat.card_congr (representationBlackEquiv hn),Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

noncomputable def blackWhiteEquiv (n : ℕ) : BlackLattices n ≃ WhiteLattices n where
  toFun L := ⟨latticeReflect L.val, (white_latticeReflect_iff L.val).mpr L.property⟩
  invFun L := ⟨latticeReflect L.val, (black_latticeReflect_iff L.val).mpr L.property⟩
  left_inv L := by apply Subtype.ext; simp
  right_inv L := by apply Subtype.ext; simp

lemma white_lattices_card {n : ℕ} (hn : 0 < n) :
    Nat.card (WhiteLattices n) = (representations n).card := by
  rw [←Nat.card_congr (blackWhiteEquiv n)]
  exact black_lattices_card hn

end A368207Lattice

/- A368207CountUnion -/

namespace A368207Lattice

theorem card_two_predicates {α : Type*} [Finite α] (P Q : α → Prop) :
    Nat.card {x // P x} + Nat.card {x // Q x} + Nat.card {x // ¬P x ∧ ¬Q x} =
      Nat.card α + Nat.card {x // P x ∧ Q x} := by
  classical
  let := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  let s := Finset.univ.filter P
  let t := Finset.univ.filter Q
  have hi : s ∩ t = Finset.univ.filter (fun x => P x ∧ Q x) := by
    ext x
    simp [s,t]
  have hc : (s ∪ t)ᶜ = Finset.univ.filter (fun x => ¬P x ∧ ¬Q x) := by
    ext x
    simp [s,t]
  have h₁ := Finset.card_union_add_card_inter s t
  have h₂ := Finset.card_add_card_compl (s ∪ t)
  rw [hi] at h₁
  rw [hc] at h₂
  change s.card+t.card+(Finset.univ.filter (fun x => ¬P x ∧ ¬Q x)).card =
    Fintype.card α+(Finset.univ.filter (fun x => P x ∧ Q x)).card
  omega

theorem two_color_count {n : ℕ} (hn : 0 < n) :
    2*(representations n).card + Nat.card {L : Lattice n // ¬Black L.val ∧ ¬White L.val} =
      ArithmeticFunction.sigma 1 n + Nat.card {L : Lattice n // Black L.val ∧ White L.val} := by
  let := lattice_finite hn
  have h := card_two_predicates (fun L : Lattice n => Black L.val) (fun L => White L.val)
  change Nat.card (BlackLattices n)+Nat.card (WhiteLattices n)+
    Nat.card {L : Lattice n // ¬Black L.val ∧ ¬White L.val} =
    Nat.card (Lattice n)+Nat.card {L : Lattice n // Black L.val ∧ White L.val} at h
  rw [black_lattices_card hn,white_lattices_card hn,lattice_card hn] at h
  omega

end A368207Lattice

/- A368207BoundaryCounts -/

namespace A368207Boundary

open Finset

/-- Number of horizontal-axis parameters admitting both colors. -/
def h (d e : ℕ) : ℕ := max 1 (2 * min d e - d)

/-- Number of missing-color lattices associated with a strict factor pair. -/
def j (d e : ℕ) : ℕ :=
  if d < e then
    if e < 2 * d then 2 * (e - d - 1)
    else if e = 2 * d then 2 * d - 1
    else 2 * d
  else 0

/-- The H1 correction written using both factors rather than their product. -/
def w (d e : ℕ) : ℕ :=
  if e ≤ 2 * d ∧ d < 2 * e then
    if d = e then 2 * d - 1
    else max 1 (2 * (2 * min d e - max d e))
  else 0

def horizontal (n : ℕ) : ℕ := ∑ d ∈ n.divisors, h d (n / d)

def missing (n : ℕ) : ℕ := ∑ d ∈ n.divisors, j d (n / d)

def correction (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors.filter (fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n),
    if d ^ 2 = n then 2 * d - 1
    else max 1 (2 * (2 * min d (n / d) - max d (n / d)))

theorem pair_balance (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    2 * h d e + 2 * h e d =
      2 + j d e + j e d + w d e + w e d := by
  unfold h j w
  split_ifs <;> omega

theorem sum_swap (f : ℕ → ℕ → ℕ) (n : ℕ) :
    (∑ d ∈ n.divisors, f d (n / d)) =
      ∑ d ∈ n.divisors, f (n / d) d := by
  exact (Nat.sum_divisorsAntidiagonal f).symm.trans
    (Nat.sum_divisorsAntidiagonal' f)

theorem weight_on_divisor (n d : ℕ) (hd : d ∈ n.divisors) :
    w d (n / d) =
      if n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n then
        if d ^ 2 = n then 2 * d - 1
        else max 1 (2 * (2 * min d (n / d) - max d (n / d)))
      else 0 := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hmul : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  have h₁ : n / d ≤ 2 * d ↔ n ≤ 2 * d ^ 2 := by
    constructor <;> intro hh <;> nlinarith
  have h₂ : d < 2 * (n / d) ↔ d ^ 2 < 2 * n := by
    constructor <;> intro hh <;> nlinarith
  have h₃ : d = n / d ↔ d ^ 2 = n := by
    constructor
    · intro hh
      rw [← hmul, ← hh]
      simp [pow_two]
    · intro hh
      exact Nat.eq_of_mul_eq_mul_left hdpos (by nlinarith)
  simp only [w, h₁, h₂, h₃]

theorem sum_w_eq_correction (n : ℕ) :
    (∑ d ∈ n.divisors, w d (n / d)) = correction n := by
  rw [correction, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun d hd => weight_on_divisor n d hd)

/-- Scalar boundary-count identity needed after lattice inclusion-exclusion. -/
theorem boundary_identity (n : ℕ) :
    2 * horizontal n = n.divisors.card + missing n + correction n := by
  have hs :
      (∑ d ∈ n.divisors, (2 * h d (n / d) + 2 * h (n / d) d)) =
        ∑ d ∈ n.divisors,
          (2 + j d (n / d) + j (n / d) d + w d (n / d) + w (n / d) d) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact pair_balance d (n / d) (Nat.pos_of_mem_divisors hd)
      (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hs
  rw [← sum_swap h n, ← sum_swap j n, ← sum_swap w n, sum_w_eq_correction] at hs
  change 2 * horizontal n + 2 * horizontal n =
    n.divisors.card * 2 + missing n + missing n + correction n + correction n at hs
  omega

def horizontalResidues (a b : ℕ) : Finset ℕ :=
  (Finset.range (min a b)).filter (fun t => t = 0 ∨ a - t < min a b)

theorem horizontalResidues_card (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (horizontalResidues a b).card = h a b := by
  have hmpos : 0 < min a b := Nat.lt_min.mpr ⟨ha, hb⟩
  have hmle : min a b ≤ a := min_le_left a b
  have heq : horizontalResidues a b = insert 0 (Finset.Ioo (a - min a b) (min a b)) := by
    ext t
    simp only [horizontalResidues, Finset.mem_filter, Finset.mem_range,
      Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [heq, Finset.card_insert_of_notMem (by simp), Nat.card_Ioo]
  unfold h
  omega

def diagonalResidues (d e : ℕ) : Finset ℕ :=
  if d < e then
    if e < 2 * d then Finset.Ioo 0 (e - d) else Finset.range d
  else ∅

theorem diagonalResidues_card (d e : ℕ) (hd : 0 < d) :
    j d e + (if d < e ∧ e = 2 * d then 1 else 0) =
      2 * (diagonalResidues d e).card := by
  unfold j diagonalResidues
  split_ifs <;> simp only [Nat.card_Ioo, Finset.card_range, Finset.card_empty,
    Nat.sub_zero] <;> omega

theorem mem_diagonalResidues_iff (d e t : ℕ) :
    t ∈ diagonalResidues d e ↔
      t < d ∧ d < e ∧ (t = 0 → 2 * d ≤ e) ∧ (0 < t → t < e - d) := by
  unfold diagonalResidues
  split_ifs <;> simp_all <;> omega

def diagonalCount (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, (diagonalResidues d (n / d)).card

def twiceSquareCount (n : ℕ) : ℕ :=
  (n.divisors.filter (fun d => n = 2 * d ^ 2)).card

theorem diagonal_count_identity (n : ℕ) :
    2 * diagonalCount n = missing n + twiceSquareCount n := by
  have hs :
      (∑ d ∈ n.divisors,
        (j d (n / d) + if d < n / d ∧ n / d = 2 * d then 1 else 0)) =
        ∑ d ∈ n.divisors, 2 * (diagonalResidues d (n / d)).card := by
    exact Finset.sum_congr rfl (fun d hd =>
      diagonalResidues_card d (n / d) (Nat.pos_of_mem_divisors hd))
  have hb : (∑ d ∈ n.divisors, if d < n / d ∧ n / d = 2 * d then 1 else 0) =
      twiceSquareCount n := by
    rw [twiceSquareCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    have hp : 0 < d := Nat.pos_of_mem_divisors hd
    have hm : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    have heq : d < n / d ∧ n / d = 2 * d ↔ n = 2 * d ^ 2 := by
      constructor
      · rintro ⟨_, hh⟩
        rw [hh] at hm
        nlinarith
      · intro hh
        have he : n / d = 2 * d :=
          Nat.eq_of_mul_eq_mul_left hp (by nlinarith)
        exact ⟨by omega, he⟩
    simp only [heq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hb] at hs
  exact hs.symm

end A368207Boundary

/- A368207AxisCard -/

namespace A368207AxisCard

open A368207Lattice A368207Axes A368207Boundary

abbrev HorizontalData (n : ℕ) :=
  Σ d : {d : ℕ // d ∈ n.divisors},
    {t : ℕ // t ∈ horizontalResidues d.val (n/d.val)}

def horizontalMap {n : ℕ} (x : HorizontalData n) : Lattice n :=
  ⟨span ((x.1.val:ℤ),0) (-(x.2.val:ℤ),(n/x.1.val:ℕ)),
    ((x.1.val:ℤ),0), (-(x.2.val:ℤ),(n/x.1.val:ℕ)), rfl, by
      simp only [det,zero_mul,sub_zero]
      exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors x.1.property)⟩

theorem horizontalMap_spec {n : ℕ} (x : HorizontalData n) :
    Horizontal (horizontalMap x).val := by
  have hm := x.2.property
  simp only [horizontalResidues,Finset.mem_filter,Finset.mem_range] at hm
  refine ⟨(x.1.val:ℤ),(n/x.1.val:ℕ),(x.2.val:ℤ),by omega,by omega,by omega,?_,rfl⟩
  rcases hm.2 with h0 | h0
  · exact Or.inl (by exact_mod_cast h0)
  · exact Or.inr (by omega)

theorem horizontalMap_standard {n : ℕ} (x : HorizontalData n) :
    Standard (x.1.val:ℤ) (n/x.1.val:ℕ) 0 (x.2.val:ℤ) := by
  have hm := x.2.property
  simp only [horizontalResidues,Finset.mem_filter,Finset.mem_range] at hm
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

theorem horizontalMap_injective {n : ℕ} : Function.Injective (@horizontalMap n) := by
  intro x y hxy
  have hs := congrArg Subtype.val hxy
  have hh := standard_basis_unique (horizontalMap_standard x) (horizontalMap_standard y) hs
  have hd : x.1=y.1 := Subtype.ext (Int.natCast_inj.mp hh.1)
  cases x with
  | mk d t =>
    cases y with
    | mk e s =>
      dsimp at hd
      subst e
      have hts : t=s := Subtype.ext (Int.natCast_inj.mp hh.2.2.2)
      subst s
      rfl

theorem lattice_det_eq {n : ℕ} (L : Lattice n) {u v : V}
    (hs : span u v=L.val) (hp : 0<det u v) : det u v=(n:ℤ) := by
  obtain ⟨U,W,hUW,hdet⟩ := L.property
  have hpos : 0≤det U W := by rw [hdet]; positivity
  exact (det_eq_of_span_eq (hs.trans hUW.symm) hp.le hpos).trans hdet

theorem horizontalMap_surjective {n : ℕ} (hn : 0<n) (L : Lattice n)
    (hL : Horizontal L.val) : ∃ x : HorizontalData n, horizontalMap x=L := by
  obtain ⟨a,b,d,hd,hda,hdb,hcond,hspan⟩ := hL
  have ha : 0<a := lt_of_le_of_lt hd hda
  have hb : 0<b := lt_of_le_of_lt hd hdb
  have hdet : det (a,0) (-d,b)=(n:ℤ) :=
    lattice_det_eq L hspan (by simpa [det] using mul_pos ha hb)
  have hab : a*b=(n:ℤ) := by simpa [det] using hdet
  let A := a.toNat
  let B := b.toNat
  let D := d.toNat
  have hA : (A:ℤ)=a := Int.toNat_of_nonneg ha.le
  have hB : (B:ℤ)=b := Int.toNat_of_nonneg hb.le
  have hD : (D:ℤ)=d := Int.toNat_of_nonneg hd
  have hAp : 0<A := by omega
  have hprod : A*B=n := by
    exact_mod_cast (show (A:ℤ)*(B:ℤ)=(n:ℤ) by rw [hA,hB]; exact hab)
  have hAm : A∈n.divisors := Nat.mem_divisors.mpr ⟨⟨B,hprod.symm⟩,hn.ne'⟩
  have hdiv : n/A=B := by rw [← hprod,Nat.mul_div_right _ hAp]
  have hres : D∈horizontalResidues A (n/A) := by
    rw [hdiv]
    simp only [horizontalResidues,Finset.mem_filter,Finset.mem_range]
    omega
  refine ⟨⟨⟨A,hAm⟩,⟨D,hres⟩⟩,?_⟩
  apply Subtype.ext
  change span ((A:ℤ),0) (-(D:ℤ),(n/A:ℕ))=L.val
  rw [hdiv,hA,hB,hD]
  exact hspan

def horizontalTo {n : ℕ} (x : HorizontalData n) :
    {L : Lattice n // Horizontal L.val} := ⟨horizontalMap x,horizontalMap_spec x⟩

noncomputable def horizontalEquiv {n : ℕ} (hn : 0<n) :
    HorizontalData n ≃ {L : Lattice n // Horizontal L.val} :=
  Equiv.ofBijective horizontalTo ⟨by
    intro x y h
    exact horizontalMap_injective (congrArg Subtype.val h),by
    intro L
    obtain ⟨x,hx⟩ := horizontalMap_surjective hn L.val L.property
    exact ⟨x,Subtype.ext hx⟩⟩

theorem horizontal_card {n : ℕ} (hn : 0<n) :
    Nat.card {L : Lattice n // Horizontal L.val}=horizontal n := by
  classical
  rw [←Nat.card_congr (horizontalEquiv hn),Nat.card_eq_fintype_card]
  simp only [HorizontalData,Fintype.card_sigma,Fintype.card_coe]
  calc
    _ = ∑ d ∈ n.divisors, (horizontalResidues d (n/d)).card :=
      Finset.sum_coe_sort n.divisors (fun d => (horizontalResidues d (n/d)).card)
    _ = horizontal n := by
      unfold horizontal
      apply Finset.sum_congr rfl
      intro d hd
      exact horizontalResidues_card d (n/d) (Nat.pos_of_mem_divisors hd)
        (divisor_quotient_pos hn hd)

def rectangleMap {n : ℕ} (d : {d : ℕ // d∈n.divisors}) : Lattice n :=
  ⟨span ((d.val:ℤ),0) (0,(n/d.val:ℕ)),
    ((d.val:ℤ),0), (0,(n/d.val:ℕ)), rfl, by
      simp only [det,zero_mul,sub_zero]
      exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors d.property)⟩

theorem rectangleMap_spec {n : ℕ} (hn : 0<n) (d : {d : ℕ // d∈n.divisors}) :
    Rectangular (rectangleMap d).val := by
  refine ⟨(d.val:ℤ),(n/d.val:ℕ),?_,?_,rfl⟩
  · exact_mod_cast Nat.pos_of_mem_divisors d.property
  · exact_mod_cast divisor_quotient_pos hn d.property

theorem rectangleMap_injective {n : ℕ} (hn : 0<n) :
    Function.Injective (@rectangleMap n) := by
  intro d e hde
  have hdp : (0:ℤ)<d.val := by exact_mod_cast Nat.pos_of_mem_divisors d.property
  have hep : (0:ℤ)<e.val := by exact_mod_cast Nat.pos_of_mem_divisors e.property
  have hdq : (0:ℤ)<(n/d.val:ℕ) := by exact_mod_cast divisor_quotient_pos hn d.property
  have heq : (0:ℤ)<(n/e.val:ℕ) := by exact_mod_cast divisor_quotient_pos hn e.property
  have hs := congrArg Subtype.val hde
  have hh := hnf_unique hdp hdq (by omega) hdp hep heq (by omega) hep hs
  exact Subtype.ext (Int.natCast_inj.mp hh.1)

theorem rectangleMap_surjective {n : ℕ} (hn : 0<n) (L : Lattice n)
    (hL : Rectangular L.val) : ∃ d, rectangleMap d=L := by
  obtain ⟨a,b,ha,hb,hspan⟩ := hL
  have hdet : det (a,0) (0,b)=(n:ℤ) :=
    lattice_det_eq L hspan (by simpa [det] using mul_pos ha hb)
  have hab : a*b=(n:ℤ) := by simpa [det] using hdet
  let A := a.toNat
  let B := b.toNat
  have hA : (A:ℤ)=a := Int.toNat_of_nonneg ha.le
  have hB : (B:ℤ)=b := Int.toNat_of_nonneg hb.le
  have hAp : 0<A := by omega
  have hprod : A*B=n := by
    exact_mod_cast (show (A:ℤ)*(B:ℤ)=(n:ℤ) by rw [hA,hB]; exact hab)
  have hAm : A∈n.divisors := Nat.mem_divisors.mpr ⟨⟨B,hprod.symm⟩,hn.ne'⟩
  have hdiv : n/A=B := by rw [←hprod,Nat.mul_div_right _ hAp]
  refine ⟨⟨A,hAm⟩,?_⟩
  apply Subtype.ext
  change span ((A:ℤ),0) (0,(n/A:ℕ))=L.val
  rw [hdiv,hA,hB]
  exact hspan

noncomputable def rectangleEquiv {n : ℕ} (hn : 0<n) :
    {d : ℕ // d∈n.divisors} ≃ {L : Lattice n // Rectangular L.val} :=
  Equiv.ofBijective (fun d => ⟨rectangleMap d,rectangleMap_spec hn d⟩) ⟨by
    intro d e h
    exact rectangleMap_injective hn (congrArg Subtype.val h),by
    intro L
    obtain ⟨d,hd⟩ := rectangleMap_surjective hn L.val L.property
    exact ⟨d,Subtype.ext hd⟩⟩

theorem rectangle_card {n : ℕ} (hn : 0<n) :
    Nat.card {L : Lattice n // Rectangular L.val}=n.divisors.card := by
  rw [←Nat.card_congr (rectangleEquiv hn),Nat.card_eq_fintype_card,Fintype.card_coe]

theorem card_predicate_union_inter {α : Type*} [Finite α] (p q : α → Prop) :
    Nat.card {x // p x ∨ q x}+Nat.card {x // p x ∧ q x} =
      Nat.card {x // p x}+Nat.card {x // q x} := by
  classical
  let : Fintype α := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hu : Finset.univ.filter (fun x => p x ∨ q x) =
      Finset.univ.filter p ∪ Finset.univ.filter q := by ext x; simp
  have hi : Finset.univ.filter (fun x => p x ∧ q x) =
      Finset.univ.filter p ∩ Finset.univ.filter q := by ext x; simp
  rw [hu,hi]
  exact Finset.card_union_add_card_inter _ _

noncomputable def horizontalVerticalEquiv {n : ℕ} :
    {L : Lattice n // Horizontal L.val} ≃ {L : Lattice n // Vertical L.val} :=
  Equiv.subtypeEquiv rotateMap (fun L => horizontal_rotateMap_iff L)

theorem vertical_card {n : ℕ} (hn : 0<n) :
    Nat.card {L : Lattice n // Vertical L.val}=horizontal n := by
  rw [← Nat.card_congr (@horizontalVerticalEquiv n),horizontal_card hn]

theorem colored_intersection_card {n : ℕ} (hn : 0<n) :
    Nat.card {L : Lattice n // Black L.val ∧ White L.val}+n.divisors.card =
      2*horizontal n := by
  let : Finite (Lattice n) := lattice_finite hn
  have hc := card_predicate_union_inter
    (fun L : Lattice n => Horizontal L.val) (fun L => Vertical L.val)
  have hu : Nat.card {L : Lattice n // Horizontal L.val ∨ Vertical L.val} =
      Nat.card {L : Lattice n // Black L.val ∧ White L.val} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun L => (colored_intersection_iff L.val).symm))
  have hi : Nat.card {L : Lattice n // Horizontal L.val ∧ Vertical L.val} =
      Nat.card {L : Lattice n // Rectangular L.val} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun L => axes_intersection_iff L.val))
  rw [hu,hi,rectangle_card hn,horizontal_card hn,vertical_card hn] at hc
  omega

end A368207AxisCard

/- A368207Classification -/

namespace A368207Lattice

theorem normalize_minimal_horizontal {L : Set V} {u v : V} {a c : ℤ}
    (hs : span u v = L) (hn : 0 < det u v)
    (hm : Minimal L (a,c)) (hc : 0 ≤ c) (hca : c < a) :
    ∃ b d : ℤ, Standard a b c d ∧ span (a,c) (-d,b) = L ∧
      det (a,c) (-d,b) = det u v := by
  have ha : 0 < a := lt_of_le_of_lt hc hca
  obtain ⟨z,hzs,hzd⟩ := extend_minimal hs hm
  let k := (-z.1) / a
  let d := (-z.1) % a
  let b := k*c+z.2
  have hd : 0 ≤ d := Int.emod_nonneg _ (ne_of_gt ha)
  have hda : d < a := Int.emod_lt_of_pos _ ha
  have hcol : lin (a,c) z k 1 = (-d,b) := by
    have hdiv := Int.ediv_mul_add_emod (-z.1) a
    apply Prod.ext
    · dsimp [lin,k,d]
      nlinarith only [hdiv]
    · simp [lin,b]
  have hspan : span (a,c) (-d,b) = L := by
    have hh := span_change (a,c) z 1 0 k 1 (by ring)
    rw [lin_one_zero,hcol] at hh
    exact hh.trans hzs
  have hdet : det (a,c) (-d,b) = det u v := by
    have hh := det_lin (a,c) z 1 0 k 1
    rw [lin_one_zero,hcol] at hh
    simpa only [one_mul,zero_mul,sub_zero,hzd] using hh
  have hz0 : (-d,b) ≠ ((0,0):V) := by
    intro h
    have hh := hn
    rw [← hdet,h] at hh
    simp [det] at hh
  have hnorm := minimal_norm_le hm (hspan ▸ right_mem_span (a,c) (-d,b)) hz0
  have hab : a ≤ |b| := by
    simp only [abs_of_nonneg ha.le,abs_of_nonneg hc,abs_neg,abs_of_nonneg hd,
      max_eq_left hca.le] at hnorm
    exact (le_max_iff.mp hnorm).resolve_left (not_le.mpr hda)
  have hba : a ≤ b := by
    by_cases hb : 0 ≤ b
    · simpa only [abs_of_nonneg hb] using hab
    · have hb' : b ≤ -a := by rw [abs_of_nonpos (le_of_not_ge hb)] at hab; omega
      have hprod₁ := mul_le_mul_of_nonneg_left hda.le hc
      have hprod₂ := mul_lt_mul_of_pos_right hca ha
      have hprod₃ := mul_le_mul_of_nonneg_left hb' ha.le
      have hpos : 0 < a*b+c*d := by
        have hh : 0 < det (a,c) (-d,b) := by rw [hdet]; exact hn
        simpa [det] using hh
      nlinarith only [hprod₁,hprod₂,hprod₃,hpos]
  exact ⟨b,d,⟨hc,hd,hca,hda,lt_of_lt_of_le hca hba,lt_of_lt_of_le hda hba⟩,
    hspan,hdet⟩

theorem colored_of_minimal_right {L : Set V} {u v : V} {a c : ℤ}
    (hs : span u v = L) (hn : 0 < det u v)
    (hm : Minimal L (a,c)) (hac : |c| < a) : Black L ∨ White L := by
  by_cases hc : 0 ≤ c
  · obtain ⟨b,d,hstd,hsp,_⟩ := normalize_minimal_horizontal hs hn hm hc
      (by simpa only [abs_of_nonneg hc] using hac)
    exact Or.inl ⟨a,b,c,d,hstd,hsp⟩
  · have hm' : Minimal (reflect '' L) (a,-c) := minimal_reflect hm
    have hbs := reflect_basis hs
    have hpos : 0 < det (reflect v) (reflect u) := by rw [hbs.2]; exact hn
    obtain ⟨b,d,hstd,hsp,_⟩ := normalize_minimal_horizontal hbs.1 hpos hm'
      (by omega) (by simpa only [abs_of_neg (lt_of_not_ge hc)] using hac)
    have hb : Black (reflect '' L) := ⟨a,b,-c,d,hstd,hsp⟩
    exact Or.inr (by simpa only [image_reflect_reflect] using black_reflect hb)

theorem colored_of_minimal_horizontal {L : Set V} {u v w : V}
    (hs : span u v = L) (hn : 0 < det u v) (hm : Minimal L w)
    (hh : w.2.natAbs < w.1.natAbs) : Black L ∨ White L := by
  rcases w with ⟨a,c⟩
  have habs : |c| < |a| := by
    have h := Int.ofNat_lt.mpr hh
    simpa only [Int.natCast_natAbs] using h
  by_cases ha : 0 ≤ a
  · exact colored_of_minimal_right hs hn hm
      (by simpa only [abs_of_nonneg ha] using habs)
  · have hm' : Minimal L (-a,-c) := minimal_negV hs hm
    exact colored_of_minimal_right hs hn hm'
      (by simpa only [abs_neg,abs_of_neg (lt_of_not_ge ha)] using habs)

theorem colored_of_minimal_not_diagonal {L : Set V} {u v w : V}
    (hs : span u v = L) (hn : 0 < det u v) (hm : Minimal L w)
    (hd : ¬ Diagonal w) : Black L ∨ White L := by
  by_cases hh : w.2.natAbs < w.1.natAbs
  · exact colored_of_minimal_horizontal hs hn hm hh
  · have hv : w.1.natAbs < w.2.natAbs := by unfold Diagonal at hd; omega
    have hbs := swapV_basis hs
    have hpos : 0 < det (swapV v) (swapV u) := by rw [hbs.2]; exact hn
    have hc := colored_of_minimal_horizontal hbs.1 hpos (minimal_swapV hm)
      (show (swapV w).2.natAbs < (swapV w).1.natAbs from hv)
    rcases hc with hb | hw
    · exact Or.inr (by simpa only [image_swapV_swapV] using black_swapV hb)
    · exact Or.inl (by simpa only [image_swapV_swapV] using white_swapV hw)

end A368207Lattice

/- A368207StandardMinimum -/

namespace A368207Lattice

theorem coefficients_zero_of_rectangle {a b c d k l : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : -a < k*a-l*d ∧ k*a-l*d < a)
    (hy : -b < k*c+l*b ∧ k*c+l*b < b) : k=0 ∧ l=0 := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have hka := mul_le_mul_of_nonneg_right (show k ≤ -1 by omega) ha.le
    rcases lt_trichotomy l 0 with hl | rfl | hl
    · have hlb := mul_le_mul_of_nonneg_right (show l ≤ -1 by omega) hb.le
      have hkc := mul_nonpos_of_nonpos_of_nonneg hk.le hc
      nlinarith only [hy.1,hlb,hkc]
    · simp only [zero_mul,sub_zero] at hx
      nlinarith only [hx.1,hka]
    · have hld := mul_nonneg hl.le hd
      nlinarith only [hx.1,hka,hld]
  · rcases lt_trichotomy l 0 with hl | rfl | hl
    · have hlb := mul_le_mul_of_nonneg_right (show l ≤ -1 by omega) hb.le
      simp only [zero_mul,zero_add] at hy
      nlinarith only [hy.1,hlb]
    · exact ⟨rfl,rfl⟩
    · have hlb := mul_le_mul_of_nonneg_right (show 1 ≤ l by omega) hb.le
      simp only [zero_mul,zero_add] at hy
      nlinarith only [hy.2,hlb]
  · have hka := mul_le_mul_of_nonneg_right (show 1 ≤ k by omega) ha.le
    rcases lt_trichotomy l 0 with hl | rfl | hl
    · have hld := mul_nonpos_of_nonpos_of_nonneg hl.le hd
      nlinarith only [hx.2,hka,hld]
    · simp only [zero_mul,sub_zero] at hx
      nlinarith only [hx.2,hka]
    · have hlb := mul_le_mul_of_nonneg_right (show 1 ≤ l by omega) hb.le
      have hkc := mul_nonneg hk.le hc
      nlinarith only [hy.2,hlb,hkc]

theorem standard_norm_lower {a b c d : ℤ} (h : Standard a b c d)
    {w : V} (hw : w ∈ span (a,c) (-d,b)) (hw0 : w ≠ (0,0)) :
    min a b ≤ max |w.1| |w.2| := by
  by_contra hh
  have hs : max |w.1| |w.2| < min a b := lt_of_not_ge hh
  have hxa : |w.1| < a := lt_of_le_of_lt (le_max_left _ _) (hs.trans_le (min_le_left _ _))
  have hyb : |w.2| < b := lt_of_le_of_lt (le_max_right _ _) (hs.trans_le (min_le_right _ _))
  obtain ⟨k,l,rfl⟩ := hw
  have hc := h.1
  have hd := h.2.1
  have ha : 0<a := lt_of_le_of_lt hc h.2.2.1
  have hb : 0<b := lt_of_le_of_lt hc h.2.2.2.2.1
  have hzero := coefficients_zero_of_rectangle (k:=k) (l:=l) ha hb hc hd
    (by simpa only [lin,mul_neg,sub_eq_add_neg] using abs_lt.mp hxa)
    (by simpa only [lin] using abs_lt.mp hyb)
  apply hw0
  simp [lin,hzero.1,hzero.2]

theorem black_has_nondiagonal_minimal {L : Set V} (h : Black L) :
    ∃ w, Minimal L w ∧ ¬ Diagonal w := by
  obtain ⟨a,b,c,d,hs,hspan⟩ := h
  have hc := hs.1
  have hd := hs.2.1
  have hca := hs.2.2.1
  have hdb := hs.2.2.2.2.2
  have ha : 0<a := lt_of_le_of_lt hc hca
  have hb : 0<b := lt_of_le_of_lt hd hdb
  by_cases hab : a≤b
  · have hu0 : (a,c) ≠ ((0,0):V) := by
      intro he; have := congrArg Prod.fst he; simp only at this; omega
    refine ⟨(a,c),⟨hspan ▸ left_mem_span _ _,hu0,?_⟩,?_⟩
    · intro z hz hz0
      have hn := standard_norm_lower hs (hspan.symm ▸ hz) hz0
      apply Int.ofNat_le.mp
      rw [height_cast,height_cast]
      simpa only [abs_of_nonneg ha.le,abs_of_nonneg hc,max_eq_left hca.le,min_eq_left hab] using hn
    · change a.natAbs ≠ c.natAbs
      intro he
      have := (Int.natAbs_inj_of_nonneg_of_nonneg ha.le hc).mp he
      omega
  · have hba : b≤a := by omega
    have hv0 : (-d,b) ≠ ((0,0):V) := by
      intro he; have := congrArg Prod.snd he; simp only at this; omega
    refine ⟨(-d,b),⟨hspan ▸ right_mem_span _ _,hv0,?_⟩,?_⟩
    · intro z hz hz0
      have hn := standard_norm_lower hs (hspan.symm ▸ hz) hz0
      apply Int.ofNat_le.mp
      rw [height_cast,height_cast]
      simpa only [abs_neg,abs_of_nonneg hb.le,abs_of_nonneg hd,max_eq_right hdb.le,min_eq_right hba] using hn
    · change (-d).natAbs ≠ b.natAbs
      rw [Int.natAbs_neg]
      intro he
      have := (Int.natAbs_inj_of_nonneg_of_nonneg hd hb.le).mp he
      omega

theorem white_has_nondiagonal_minimal {L : Set V} (h : White L) :
    ∃ w, Minimal L w ∧ ¬ Diagonal w := by
  obtain ⟨w,hm,hd⟩ := black_has_nondiagonal_minimal (white_reflect h)
  refine ⟨reflect w,?_,?_⟩
  · simpa only [image_reflect_reflect] using minimal_reflect hm
  · simpa only [Diagonal,reflect,Int.natAbs_neg] using hd

theorem missing_iff_all_minimal_diagonal {L : Set V} {u v : V}
    (hs : span u v = L) (hn : 0 < det u v) :
    (¬ Black L ∧ ¬ White L) ↔ ∀ w, Minimal L w → Diagonal w := by
  constructor
  · intro h w hw
    by_contra hd
    exact (colored_of_minimal_not_diagonal hs hn hw hd).elim h.1 h.2
  · intro h
    constructor
    · intro hb
      obtain ⟨w,hw,hd⟩ := black_has_nondiagonal_minimal hb
      exact hd (h w hw)
    · intro hw
      obtain ⟨w,hm,hd⟩ := white_has_nondiagonal_minimal hw
      exact hd (h w hm)

end A368207Lattice

/- A368207DiagonalSquare -/

namespace A368207Lattice

theorem square_coefficients
    (d e t k l : ℤ) (hd : 0 < d) (hde : d < e)
    (ht0 : 0 ≤ t) (htd : t < d)
    (hzero : t = 0 → 2 * d ≤ e) (hpos : 0 < t → t < e - d)
    (hxlo : -d ≤ k * d - l * t) (hxhi : k * d - l * t ≤ d)
    (hylo : -d ≤ k * d + l * (e - t)) (hyhi : k * d + l * (e - t) ≤ d) :
    (k = 0 ∧ l = 0) ∨ (k = 1 ∧ l = 0) ∨ (k = -1 ∧ l = 0) ∨
      (t = 0 ∧ e = 2 * d ∧ ((k = -1 ∧ l = 1) ∨ (k = 1 ∧ l = -1))) := by
  have he : 0 < e := lt_trans hd hde
  have hl : -1 ≤ l ∧ l ≤ 1 := by
    constructor
    · by_contra hh
      have hp := mul_nonneg (show 0 ≤ -l - 2 by omega) he.le
      nlinarith
    · by_contra hh
      have hp := mul_nonneg (show 0 ≤ l - 2 by omega) he.le
      nlinarith
  obtain ⟨hl₁, hl₂⟩ := hl
  interval_cases l
  · have hk : 0 ≤ k ∧ k ≤ 1 := by
      constructor
      · by_contra hh
        have hp := mul_nonneg (show 0 ≤ -k - 1 by omega) hd.le
        nlinarith
      · by_contra hh
        have hp := mul_nonneg (show 0 ≤ k - 2 by omega) hd.le
        nlinarith
    obtain ⟨hk₁, hk₂⟩ := hk
    interval_cases k
    · have ht : 0 < t := by nlinarith
      have hp := hpos ht
      nlinarith
    · have ht : t = 0 := by nlinarith
      have heq : e = 2 * d := by have hz := hzero ht; nlinarith
      exact Or.inr (Or.inr (Or.inr ⟨ht, heq, Or.inr ⟨rfl, rfl⟩⟩))
  · have hk : -1 ≤ k ∧ k ≤ 1 := by
      constructor
      · by_contra hh
        have hp := mul_nonneg (show 0 ≤ -k - 2 by omega) hd.le
        nlinarith
      · by_contra hh
        have hp := mul_nonneg (show 0 ≤ k - 2 by omega) hd.le
        nlinarith
    obtain ⟨hk₁, hk₂⟩ := hk
    interval_cases k
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · have hk : -1 ≤ k ∧ k ≤ 0 := by
      constructor
      · by_contra hh
        have hp := mul_nonneg (show 0 ≤ -k - 2 by omega) hd.le
        nlinarith
      · by_contra hh
        have hp := mul_nonneg (show 0 ≤ k - 1 by omega) hd.le
        nlinarith
    obtain ⟨hk₁, hk₂⟩ := hk
    interval_cases k
    · have ht : t = 0 := by nlinarith
      have heq : e = 2 * d := by have hz := hzero ht; nlinarith
      exact Or.inr (Or.inr (Or.inr ⟨ht, heq, Or.inl ⟨rfl, rfl⟩⟩))
    · have ht : 0 < t := by nlinarith
      have hp := hpos ht
      nlinarith

theorem height_le_natAbs_iff (v : V) (d : ℤ) (hd : 0 ≤ d) :
    height v ≤ d.natAbs ↔
      -d ≤ v.1 ∧ v.1 ≤ d ∧ -d ≤ v.2 ∧ v.2 ≤ d := by
  simp only [height, max_le_iff]
  have h₁ : v.1.natAbs ≤ d.natAbs ↔ -d ≤ v.1 ∧ v.1 ≤ d := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs,
      abs_of_nonneg hd, abs_le]
  have h₂ : v.2.natAbs ≤ d.natAbs ↔ -d ≤ v.2 ∧ v.2 ≤ d := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs,
      abs_of_nonneg hd, abs_le]
  rw [h₁, h₂]
  tauto

theorem diagonal_square_vectors
    (d e t : ℤ) (hd : 0 < d) (hde : d < e)
    (ht0 : 0 ≤ t) (htd : t < d)
    (hzero : t = 0 → 2 * d ≤ e) (hpos : 0 < t → t < e - d)
    (v : V) (hv : v ∈ span (d, d) (-t, e - t)) (hb : height v ≤ d.natAbs) :
    v = (0, 0) ∨ v = (d, d) ∨ v = (-d, -d) ∨
      (t = 0 ∧ e = 2 * d ∧ (v = (d, -d) ∨ v = (-d, d))) := by
  obtain ⟨k, l, rfl⟩ := hv
  obtain ⟨hxlo, hxhi, hylo, hyhi⟩ := (height_le_natAbs_iff _ d hd.le).mp hb
  simp only [lin] at hxlo hxhi hylo hyhi
  have hxy : k * d + l * -t = k * d - l * t := by ring
  rw [hxy] at hxlo hxhi
  rcases square_coefficients d e t k l hd hde ht0 htd hzero hpos hxlo hxhi hylo hyhi
    with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, hc⟩
  · simp [lin]
  · simp [lin]
  · simp [lin]
  · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, Or.inr ?_⟩))
      apply Prod.ext <;> dsimp [lin] <;> ring
    · refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, Or.inl ?_⟩))
      apply Prod.ext <;> dsimp [lin] <;> ring

theorem minimal_of_height_le_diagonal
    {L : Set V} {d : ℤ} (hm : Minimal L (d, d))
    {v : V} (hv : v ∈ L) (hne : v ≠ (0, 0)) (hle : height v ≤ d.natAbs) :
    Minimal L v := by
  refine ⟨hv, hne, ?_⟩
  intro z hz hzne
  exact hle.trans (by simpa [height] using hm.2.2 z hz hzne)

theorem diagonal_square_criterion (d e t : ℤ)
    (hd : 0 < d) (he : 0 < e) (ht0 : 0 ≤ t) (htd : t < d) :
    (Minimal (span (d, d) (-t, e - t)) (d, d) ∧
      ∀ v, Minimal (span (d, d) (-t, e - t)) v → Diagonal v) ↔
      (d < e ∧ (t = 0 → 2 * d ≤ e) ∧ (0 < t → t < e - d)) := by
  constructor
  · rintro ⟨hm, hall⟩
    have full_coords (v : V) (hv : v ∈ span (d, d) (-t, e - t))
        (hne : v ≠ (0, 0)) (hle : height v ≤ d.natAbs) :
        d.natAbs ≤ v.1.natAbs ∧ d.natAbs ≤ v.2.natAbs := by
      have hvmin := minimal_of_height_le_diagonal hm hv hne hle
      have heq := hall v hvmin
      change v.1.natAbs = v.2.natAbs at heq
      have hb : d.natAbs ≤ height v := by simpa [height] using hm.2.2 v hv hne
      simp only [height, heq, max_self] at hb
      exact ⟨by simpa [heq] using hb, hb⟩
    have hvne : (-t, e - t) ≠ (0, 0) := by
      intro hz
      have hx := congrArg Prod.fst hz
      have hy := congrArg Prod.snd hz
      dsimp at hx hy
      omega
    have htAbs : t.natAbs < d.natAbs :=
      Int.natAbs_lt_natAbs_of_nonneg_of_lt ht0 htd
    have hde : d < e := by
      by_contra hh
      have hb : height (-t, e - t) ≤ d.natAbs :=
        (height_le_natAbs_iff _ d hd.le).mpr (by dsimp; omega)
      have hf := (full_coords (-t, e - t) (right_mem_span _ _) hvne hb).1
      simp only [Int.natAbs_neg] at hf
      omega
    refine ⟨hde, ?_, ?_⟩
    · intro hz
      by_contra hh
      let v : V := (-d, e - d)
      have hv : v ∈ span (d, d) (-t, e - t) := by
        refine ⟨-1, 1, ?_⟩
        apply Prod.ext <;> dsimp [v, lin] <;> rw [hz] <;> ring
      have hne : v ≠ (0, 0) := by
        intro hv0
        have hx := congrArg Prod.fst hv0
        dsimp [v] at hx
        omega
      have hb : height v ≤ d.natAbs :=
        (height_le_natAbs_iff _ d hd.le).mpr (by dsimp [v]; omega)
      have hf := (full_coords v hv hne hb).2
      have hlt : (e - d).natAbs < d.natAbs :=
        Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
      dsimp [v] at hf
      omega
    · intro htpos
      by_contra hh
      have hb : height (-t, e - t) ≤ d.natAbs :=
        (height_le_natAbs_iff _ d hd.le).mpr (by dsimp; omega)
      have hf := (full_coords (-t, e - t) (right_mem_span _ _) hvne hb).1
      simp only [Int.natAbs_neg] at hf
      omega
  · rintro ⟨hde, hz, hp⟩
    have hdne : (d, d) ≠ (0, 0) := by
      intro hh
      have hx := congrArg Prod.fst hh
      dsimp at hx
      omega
    have hm : Minimal (span (d, d) (-t, e - t)) (d, d) := by
      refine ⟨left_mem_span _ _, hdne, ?_⟩
      intro v hv hne
      change max d.natAbs d.natAbs ≤ height v
      rw [max_self]
      by_cases hb : d.natAbs ≤ height v
      · exact hb
      have hsq := diagonal_square_vectors d e t hd hde ht0 htd hz hp v hv
        (by omega : height v ≤ d.natAbs)
      rcases hsq with hv0 | rfl | rfl | ⟨_, _, rfl | rfl⟩
      · exact (hne hv0).elim
      all_goals simp [height]
    refine ⟨hm, ?_⟩
    intro v hv
    have hb : height v ≤ d.natAbs := by
      simpa [height] using hv.2.2 (d, d) (left_mem_span _ _) hdne
    rcases diagonal_square_vectors d e t hd hde ht0 htd hz hp v hv.1 hb
      with rfl | rfl | rfl | ⟨_, _, rfl | rfl⟩ <;> simp [Diagonal]

theorem negative_diagonal_minimum_iff (d e t : ℤ)
    (hd : 0 < d) (he : 0 < e) (ht0 : 0 ≤ t) (htd : t < d)
    (hc : d < e ∧ (t = 0 → 2 * d ≤ e) ∧ (0 < t → t < e - d)) :
    Minimal (span (d, d) (-t, e - t)) (-d, d) ↔ t = 0 ∧ e = 2 * d := by
  have hm := ((diagonal_square_criterion d e t hd he ht0 htd).mpr hc).1
  constructor
  · intro hv
    have hs := diagonal_square_vectors d e t hd hc.1 ht0 htd hc.2.1 hc.2.2
      (-d, d) hv.1 (by simp [height])
    rcases hs with h | h | h | h
    · have hh := congrArg Prod.snd h
      dsimp at hh
      omega
    · have hh := congrArg Prod.fst h
      dsimp at hh
      omega
    · have hh := congrArg Prod.snd h
      dsimp at hh
      omega
    · exact ⟨h.1, h.2.1⟩
  · rintro ⟨rfl, rfl⟩
    apply minimal_of_height_le_diagonal hm
    · refine ⟨-1, 1, ?_⟩
      apply Prod.ext <;> dsimp [lin] <;> ring
    · intro hh
      have hx := congrArg Prod.snd hh
      dsimp at hx
      omega
    · simp [height]

theorem diag_axis_mem_iff (d e t x : ℤ) (he : 0 < e) :
    (x, x) ∈ span (d, d) (-t, e - t) ↔ d ∣ x := by
  constructor
  · rintro ⟨k, l, hxy⟩
    have hx := congrArg Prod.fst hxy
    have hy := congrArg Prod.snd hxy
    dsimp [lin] at hx hy
    have hl : l * e = 0 := by nlinarith
    have hl0 : l = 0 := (mul_eq_zero.mp hl).resolve_right (ne_of_gt he)
    refine ⟨k, ?_⟩
    rw [hl0] at hx
    nlinarith
  · rintro ⟨k, rfl⟩
    refine ⟨k, 0, ?_⟩
    apply Prod.ext <;> dsimp [lin] <;> ring

theorem diag_difference_dvd (d e t : ℤ) (v : V)
    (hv : v ∈ span (d, d) (-t, e - t)) : e ∣ v.2 - v.1 := by
  obtain ⟨k, l, rfl⟩ := hv
  refine ⟨l, ?_⟩
  dsimp [lin]
  ring

/-- Normalized diagonal-basis parameters uniquely determine their span. -/
theorem diag_span_injective (d e t D E T : ℤ)
    (hd : 0 < d) (he : 0 < e) (hD : 0 < D) (hE : 0 < E)
    (ht0 : 0 ≤ t) (htd : t < d) (hT0 : 0 ≤ T) (hTD : T < D)
    (hs : span (d, d) (-t, e - t) = span (D, D) (-T, E - T)) :
    d = D ∧ e = E ∧ t = T := by
  have hdD : d ∣ D := (diag_axis_mem_iff d e t D he).mp (by
    rw [hs]
    exact left_mem_span _ _)
  have hDd : D ∣ d := (diag_axis_mem_iff D E T d hE).mp (by
    rw [← hs]
    exact left_mem_span _ _)
  have heE : e ∣ E := by
    have hv : (-T, E - T) ∈ span (d, d) (-t, e - t) := by
      rw [hs]
      exact right_mem_span _ _
    simpa using diag_difference_dvd d e t (-T, E - T) hv
  have hEe : E ∣ e := by
    have hv : (-t, e - t) ∈ span (D, D) (-T, E - T) := by
      rw [← hs]
      exact right_mem_span _ _
    simpa using diag_difference_dvd D E T (-t, e - t) hv
  have hd_eq := Int.dvd_antisymm hd.le hD.le hdD hDd
  have he_eq := Int.dvd_antisymm he.le hE.le heE hEe
  subst D
  subst E
  have hv : (-T, e - T) ∈ span (d, d) (-t, e - t) := by
    rw [hs]
    exact right_mem_span _ _
  obtain ⟨k, l, hxy⟩ := hv
  have hx := congrArg Prod.fst hxy
  have hy := congrArg Prod.snd hxy
  dsimp [lin] at hx hy
  have hl : l = 1 := mul_right_cancel₀ (ne_of_gt he) (by nlinarith : l * e = 1 * e)
  rw [hl] at hx hy
  have hk : k = 0 := by
    rcases lt_trichotomy k 0 with hk | hk | hk
    · have hp := mul_nonneg (show 0 ≤ -k - 1 by omega) hd.le
      nlinarith
    · exact hk
    · have hp := mul_nonneg (show 0 ≤ k - 1 by omega) hd.le
      nlinarith
  exact ⟨rfl, rfl, by nlinarith⟩

end A368207Lattice

/- A368207DiagonalBasis -/

namespace A368207Lattice

theorem diagonal_basis_of_minimal {L : Set V} {u v : V} {d : ℤ}
    (hs : span u v = L) (hn : 0 < det u v) (hd : 0 < d)
    (hm : Minimal L (d,d)) :
    ∃ e t : ℤ, 0 < e ∧ 0 ≤ t ∧ t < d ∧ d*e = det u v ∧
      span (d,d) (-t,e-t) = L := by
  obtain ⟨z,hzs,hzd⟩ := extend_minimal hs hm
  let k := (-z.1)/d
  let t := (-z.1)%d
  let e := z.2-z.1
  have ht : 0 ≤ t := Int.emod_nonneg _ hd.ne'
  have htd : t < d := Int.emod_lt_of_pos _ hd
  have hde : d*e = det u v := by
    dsimp [e]
    simpa only [det,mul_sub] using hzd
  have he : 0 < e := by nlinarith only [hde,hd,hn]
  have hcol : lin (d,d) z k 1 = (-t,e-t) := by
    have hdiv := Int.ediv_mul_add_emod (-z.1) d
    apply Prod.ext <;> dsimp [lin,k,t,e] <;> nlinarith only [hdiv]
  have hsp : span (d,d) (-t,e-t) = L := by
    have hh := span_change (d,d) z 1 0 k 1 (by ring)
    rw [lin_one_zero,hcol] at hh
    exact hh.trans hzs
  exact ⟨e,t,he,ht,htd,hde,hsp⟩

theorem diagonal_minimal_orientation {L : Set V} {u v w : V}
    (hs : span u v = L) (hm : Minimal L w) (hw : Diagonal w) :
    ∃ d : ℤ, 0 < d ∧ (Minimal L (d,d) ∨ Minimal L (-d,d)) := by
  rcases w with ⟨x,y⟩
  change x.natAbs = y.natAbs at hw
  have hxy : |x| = |y| := by
    have hh := congrArg (fun z : ℕ => (z:ℤ)) hw
    simpa only [Int.natCast_natAbs] using hh
  have hy0 : y ≠ 0 := by
    intro hy
    have hx : x=0 := by simpa only [hy,abs_zero,abs_eq_zero] using hxy
    exact hm.2.1 (by simp [hx,hy])
  have hy : 0 < |y| := abs_pos.mpr hy0
  refine ⟨|y|,hy,?_⟩
  have hm' : Minimal L (negV (x,y)) := minimal_negV hs hm
  by_cases hx : 0≤x
  · by_cases hy' : 0≤y
    · have he : x=y := by simpa only [abs_of_nonneg hx,abs_of_nonneg hy'] using hxy
      left
      simpa only [he,abs_of_nonneg hy'] using hm
    · have he : x = -y := by simpa only [abs_of_nonneg hx,abs_of_neg (lt_of_not_ge hy')] using hxy
      right
      simpa only [negV,he,abs_of_neg (lt_of_not_ge hy'),neg_neg] using hm'
  · by_cases hy' : 0≤y
    · have he : -x = y := by simpa only [abs_of_neg (lt_of_not_ge hx),abs_of_nonneg hy'] using hxy
      right
      have hxe : x = -y := by omega
      simpa only [hxe,abs_of_nonneg hy'] using hm
    · have he : x=y := by simpa only [abs_of_neg (lt_of_not_ge hx),abs_of_neg (lt_of_not_ge hy'),neg_inj] using hxy
      left
      simpa only [negV,he,abs_of_neg (lt_of_not_ge hy')] using hm'

theorem minimal_height_eq {L : Set V} {w z : V}
    (hw : Minimal L w) (hz : Minimal L z) : height w = height z :=
  le_antisymm (hw.2.2 z hz.1 hz.2.1) (hz.2.2 w hw.1 hw.2.1)

theorem diagonal_minimum_radius_unique {L : Set V} {d D : ℤ}
    (hd : 0 < d) (hD : 0 < D)
    (hm : Minimal L (d,d)) (hM : Minimal L (-D,D)) : d=D := by
  have hh := minimal_height_eq hm hM
  have he : d.natAbs=D.natAbs := by simpa [height] using hh
  exact (Int.natAbs_inj_of_nonneg_of_nonneg hd.le hD.le).mp he

theorem missing_reflect {L : Set V} (hm : ¬Black L ∧ ¬White L) :
    ¬Black (reflect '' L) ∧ ¬White (reflect '' L) := by
  constructor
  · intro h
    exact hm.2 (by simpa only [image_reflect_reflect] using black_reflect h)
  · intro h
    exact hm.1 (by simpa only [image_reflect_reflect] using white_reflect h)

theorem missing_positive_parameters {L : Set V} {u v : V} {d : ℤ}
    (hs : span u v = L) (hn : 0 < det u v) (hd : 0 < d)
    (hm : Minimal L (d,d)) (hmiss : ¬Black L ∧ ¬White L) :
    ∃ e t : ℤ, 0 < e ∧ 0 ≤ t ∧ t < d ∧ d*e = det u v ∧
      (d < e ∧ (t=0 → 2*d≤e) ∧ (0<t → t<e-d)) ∧
      span (d,d) (-t,e-t) = L := by
  obtain ⟨e,t,he,ht0,htd,hde,hsp⟩ := diagonal_basis_of_minimal hs hn hd hm
  have hall := (missing_iff_all_minimal_diagonal hs hn).mp hmiss
  have hg := (diagonal_square_criterion d e t hd he ht0 htd).mp
    ⟨by simpa only [hsp] using hm,by simpa only [hsp] using hall⟩
  exact ⟨e,t,he,ht0,htd,hde,hg,hsp⟩

theorem good_diagonal_missing (d e t : ℤ)
    (hd : 0<d) (he : 0<e) (ht0 : 0≤t) (htd : t<d)
    (hg : d<e ∧ (t=0 → 2*d≤e) ∧ (0<t → t<e-d)) :
    ¬Black (span (d,d) (-t,e-t)) ∧ ¬White (span (d,d) (-t,e-t)) := by
  have hp : 0 < det (d,d) (-t,e-t) := by
    have hh := mul_pos hd he
    dsimp [det]
    nlinarith only [hh]
  exact (missing_iff_all_minimal_diagonal rfl hp).mpr
    ((diagonal_square_criterion d e t hd he ht0 htd).mpr hg).2

theorem missing_diagonal_parameters {L : Set V} {u v : V}
    (hs : span u v = L) (hn : 0 < det u v) (hmiss : ¬Black L ∧ ¬White L) :
    ∃ d e t : ℤ, 0<d ∧ 0<e ∧ 0≤t ∧ t<d ∧ d*e=det u v ∧
      (d<e ∧ (t=0 → 2*d≤e) ∧ (0<t → t<e-d)) ∧
      (span (d,d) (-t,e-t)=L ∨ reflect '' span (d,d) (-t,e-t)=L) := by
  obtain ⟨w,hm⟩ := exists_minimal hs hn.ne'
  have hall := (missing_iff_all_minimal_diagonal hs hn).mp hmiss
  obtain ⟨d,hd,hpos | hneg⟩ := diagonal_minimal_orientation hs hm (hall w hm)
  · obtain ⟨e,t,he,ht0,htd,hde,hg,hsp⟩ := missing_positive_parameters hs hn hd hpos hmiss
    exact ⟨d,e,t,hd,he,ht0,htd,hde,hg,Or.inl hsp⟩
  · have hbs := reflect_basis hs
    have hn' : 0<det (reflect v) (reflect u) := by rw [hbs.2]; exact hn
    have hm' : Minimal (reflect '' L) (d,d) := by
      have hh := minimal_reflect (minimal_negV hs hneg)
      simpa only [reflect,negV,neg_neg] using hh
    obtain ⟨e,t,he,ht0,htd,hde,hg,hsp⟩ :=
      missing_positive_parameters hbs.1 hn' hd hm' (missing_reflect hmiss)
    refine ⟨d,e,t,hd,he,ht0,htd,hde.trans hbs.2,hg,Or.inr ?_⟩
    rw [hsp,image_reflect_reflect]

end A368207Lattice

/- A368207MissingCard -/

/-!
Missing lattices are parametrized by a shortest positive or negative diagonal.
For a fixed determinant, a positive diagonal basis is uniquely specified by a
divisor and one of `diagonalResidues`. Reflection gives the negative orientation.
The two orientations coincide precisely for the diamond lattices of determinant
`2 * d ^ 2`; subtracting that overlap gives the scalar function `missing`.
-/

namespace A368207Lattice

open Finset A368207Boundary

abbrev DiagonalData (n : ℕ) :=
  Σ d : {d : ℕ // d ∈ n.divisors},
    {t : ℕ // t ∈ diagonalResidues d.val (n / d.val)}

def diagonalMap {n : ℕ} (x : DiagonalData n) : Lattice n :=
  ⟨span ((x.1.val : ℤ), (x.1.val : ℤ))
      (-(x.2.val : ℤ), (n / x.1.val : ℕ) - (x.2.val : ℤ)),
    ((x.1.val : ℤ), (x.1.val : ℤ)),
    (-(x.2.val : ℤ), (n / x.1.val : ℕ) - (x.2.val : ℤ)), rfl, by
      have hm : (x.1.val : ℤ) * (n / x.1.val : ℕ) = (n : ℤ) := by
        exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors x.1.property)
      simp only [Int.natCast_ediv] at hm
      dsimp [det]
      nlinarith only [hm]⟩

theorem diagonalData_good {n : ℕ} (x : DiagonalData n) :
    0 < (x.1.val : ℤ) ∧ 0 < ((n / x.1.val : ℕ) : ℤ) ∧
      0 ≤ (x.2.val : ℤ) ∧ (x.2.val : ℤ) < (x.1.val : ℤ) ∧
      ((x.1.val : ℤ) < (n / x.1.val : ℕ) ∧
        ((x.2.val : ℤ) = 0 → 2 * (x.1.val : ℤ) ≤ (n / x.1.val : ℕ)) ∧
        (0 < (x.2.val : ℤ) → (x.2.val : ℤ) < (n / x.1.val : ℕ) - (x.1.val : ℤ))) := by
  have hd := Nat.pos_of_mem_divisors x.1.property
  obtain ⟨ht, hde, hz, hp⟩ := (mem_diagonalResidues_iff _ _ _).mp x.2.property
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · intro h
    have hh := hz (by omega)
    omega
  · intro h
    have hh := hp (by omega)
    omega

theorem diagonalMap_injective (n : ℕ) : Function.Injective (@diagonalMap n) := by
  intro x y hxy
  obtain ⟨hxd, hxe, hxt0, hxtd, hxg⟩ := diagonalData_good x
  obtain ⟨hyd, hye, hyt0, hytd, hyg⟩ := diagonalData_good y
  have hs := congrArg Subtype.val hxy
  have hh := diag_span_injective _ _ _ _ _ _ hxd hxe hyd hye hxt0 hxtd hyt0 hytd hs
  have hd : x.1 = y.1 := Subtype.ext (Int.natCast_inj.mp hh.1)
  cases x with
  | mk d t =>
    cases y with
    | mk e s =>
      dsimp at hd
      subst e
      have ht : t = s := Subtype.ext (Int.natCast_inj.mp hh.2.2)
      subst s
      rfl

theorem diagonalData_card (n : ℕ) : Nat.card (DiagonalData n) = diagonalCount n := by
  rw [Nat.card_eq_fintype_card]
  simp only [DiagonalData, Fintype.card_sigma, Fintype.card_coe]
  exact Finset.sum_coe_sort n.divisors (fun d => (diagonalResidues d (n / d)).card)

theorem diagonalData_twice_card (n : ℕ) :
    2 * Nat.card (DiagonalData n) = missing n + twiceSquareCount n := by
  rw [diagonalData_card]
  exact diagonal_count_identity n

theorem diagonalMap_missing {n : ℕ} (x : DiagonalData n) :
    ¬ Black (diagonalMap x).val ∧ ¬ White (diagonalMap x).val := by
  obtain ⟨hd, he, ht0, htd, hg⟩ := diagonalData_good x
  exact good_diagonal_missing _ _ _ hd he ht0 htd hg

theorem diagonalMap_minimum {n : ℕ} (x : DiagonalData n) :
    Minimal (diagonalMap x).val ((x.1.val : ℤ), (x.1.val : ℤ)) := by
  obtain ⟨hd, he, ht0, htd, hg⟩ := diagonalData_good x
  exact ((diagonal_square_criterion _ _ _ hd he ht0 htd).mpr hg).1

theorem diagonal_reflection_forces_boundary
    (d e t D E T : ℤ)
    (hd : 0 < d) (he : 0 < e) (ht0 : 0 ≤ t) (htd : t < d)
    (hD : 0 < D) (hE : 0 < E) (hT0 : 0 ≤ T) (hTD : T < D)
    (hg : d < e ∧ (t = 0 → 2 * d ≤ e) ∧ (0 < t → t < e - d))
    (hG : D < E ∧ (T = 0 → 2 * D ≤ E) ∧ (0 < T → T < E - D))
    (hs : span (d, d) (-t, e - t) = reflect '' span (D, D) (-T, E - T)) :
    t = 0 ∧ e = 2 * d := by
  have hm := ((diagonal_square_criterion d e t hd he ht0 htd).mpr hg).1
  have hM := ((diagonal_square_criterion D E T hD hE hT0 hTD).mpr hG).1
  have hneg : Minimal (span (d, d) (-t, e - t)) (-D, D) := by
    have hh := minimal_reflect hM
    rw [← hs] at hh
    have hh' := minimal_negV rfl hh
    simpa only [reflect, negV, neg_neg] using hh'
  have hrad := diagonal_minimum_radius_unique hd hD hm hneg
  subst D
  exact (negative_diagonal_minimum_iff d e t hd he ht0 htd hg).mp hneg

theorem diamond_reflection (d : ℤ) :
    reflect '' span (d, d) (0, 2 * d) = span (d, d) (0, 2 * d) := by
  have hsp := span_change (d, d) (0, 2 * d) 0 (-1) 1 (-1) (by norm_num)
  have h₁ : lin (d, d) (0, 2 * d) 0 (-1) = (0, -(2 * d)) := by
    apply Prod.ext <;> dsimp [lin] <;> ring
  have h₂ : lin (d, d) (0, 2 * d) 1 (-1) = (d, -d) := by
    apply Prod.ext <;> dsimp [lin] <;> ring
  rw [h₁, h₂] at hsp
  rw [image_reflect_span, span_swap]
  simpa only [reflect, neg_zero] using hsp

theorem diagonalData_of_parameters {n : ℕ} (hn : 0 < n)
    (d e t : ℤ) (hd : 0 < d) (he : 0 < e) (ht0 : 0 ≤ t) (htd : t < d)
    (hprod : d * e = (n : ℤ))
    (hg : d < e ∧ (t = 0 → 2 * d ≤ e) ∧ (0 < t → t < e - d)) :
    ∃ x : DiagonalData n, (diagonalMap x).val = span (d, d) (-t, e - t) := by
  let D := d.toNat
  let E := e.toNat
  let T := t.toNat
  have hD : (D : ℤ) = d := Int.toNat_of_nonneg hd.le
  have hE : (E : ℤ) = e := Int.toNat_of_nonneg he.le
  have hT : (T : ℤ) = t := Int.toNat_of_nonneg ht0
  have hDp : 0 < D := by omega
  have hprodN : D * E = n := by
    exact_mod_cast (show (D : ℤ) * (E : ℤ) = (n : ℤ) by rw [hD, hE]; exact hprod)
  have hDm : D ∈ n.divisors := Nat.mem_divisors.mpr ⟨⟨E, hprodN.symm⟩, hn.ne'⟩
  have hdiv : n / D = E := by rw [← hprodN, Nat.mul_div_right _ hDp]
  have hres : T ∈ diagonalResidues D (n / D) := by
    rw [hdiv, mem_diagonalResidues_iff]
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro h
      have hh := hg.2.1 (by omega)
      omega
    · intro h
      have hh := hg.2.2 (by omega)
      omega
  refine ⟨⟨⟨D, hDm⟩, ⟨T, hres⟩⟩, ?_⟩
  change span ((D : ℤ), (D : ℤ)) (-(T : ℤ), (n / D : ℕ) - (T : ℤ)) = _
  rw [hdiv, hD, hE, hT]

def positiveDiagonals (n : ℕ) : Set (Lattice n) := Set.range (@diagonalMap n)

def negativeDiagonals (n : ℕ) : Set (Lattice n) :=
  Set.range (fun x : DiagonalData n => latticeReflect (diagonalMap x))

def missingLattices (n : ℕ) : Set (Lattice n) :=
  {L | ¬ Black L.val ∧ ¬ White L.val}

theorem missing_eq_diagonal_union {n : ℕ} (hn : 0 < n) :
    missingLattices n = positiveDiagonals n ∪ negativeDiagonals n := by
  ext L
  constructor
  · intro hmiss
    obtain ⟨u, v, hs, hdet⟩ := L.property
    have hp : 0 < det u v := by rw [hdet]; exact_mod_cast hn
    obtain ⟨d, e, t, hd, he, ht0, htd, hde, hg, hspan⟩ :=
      missing_diagonal_parameters hs hp hmiss
    obtain ⟨x, hx⟩ := diagonalData_of_parameters hn d e t hd he ht0 htd (hde.trans hdet) hg
    rcases hspan with hsp | hsp
    · exact Or.inl ⟨x, Subtype.ext (hx.trans hsp)⟩
    · exact Or.inr ⟨x, Subtype.ext (by change reflect '' (diagonalMap x).val = L.val; rw [hx, hsp])⟩
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact diagonalMap_missing x
    · exact missing_reflect (diagonalMap_missing x)

theorem positiveDiagonals_card (n : ℕ) :
    (positiveDiagonals n).ncard = Nat.card (DiagonalData n) :=
  Set.ncard_range_of_injective (diagonalMap_injective n)

theorem negativeDiagonals_card (n : ℕ) :
    (negativeDiagonals n).ncard = Nat.card (DiagonalData n) :=
  Set.ncard_range_of_injective ((latticeReflect_injective n).comp (diagonalMap_injective n))

abbrev DiamondData (n : ℕ) := {d : ℕ // d ∈ n.divisors.filter (fun d => n = 2 * d ^ 2)}

theorem diamondData_divisor {n : ℕ} (x : DiamondData n) : x.val ∈ n.divisors :=
  (Finset.mem_filter.mp x.property).1

theorem diamondData_positive {n : ℕ} (x : DiamondData n) : 0 < x.val :=
  Nat.pos_of_mem_divisors (diamondData_divisor x)

theorem diamondData_quotient {n : ℕ} (x : DiamondData n) : n / x.val = 2 * x.val := by
  have hm := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (diamondData_divisor x))
  have hs := (Finset.mem_filter.mp x.property).2
  apply Nat.eq_of_mul_eq_mul_left (diamondData_positive x)
  nlinarith only [hm, hs]

def diamondToDiagonal {n : ℕ} (x : DiamondData n) : DiagonalData n :=
  ⟨⟨x.val, diamondData_divisor x⟩, ⟨0, by
    change (0 : ℕ) ∈ diagonalResidues x.val (n / x.val)
    rw [mem_diagonalResidues_iff, diamondData_quotient x]
    have hp := diamondData_positive x
    refine ⟨hp, by omega, ?_, ?_⟩
    · intro _
      omega
    · intro h
      omega⟩⟩

def diamondMap {n : ℕ} (x : DiamondData n) : Lattice n := diagonalMap (diamondToDiagonal x)

theorem diamondMap_val {n : ℕ} (x : DiamondData n) :
    (diamondMap x).val = span ((x.val : ℤ), (x.val : ℤ)) (0, 2 * (x.val : ℤ)) := by
  change span ((x.val : ℤ), (x.val : ℤ)) (-(0 : ℤ), (n / x.val : ℕ) - (0 : ℤ)) = _
  rw [diamondData_quotient x]
  simp only [neg_zero, sub_zero, Nat.cast_mul, Nat.cast_ofNat]

theorem diamondMap_injective (n : ℕ) : Function.Injective (@diamondMap n) := by
  intro x y h
  have hd := diagonalMap_injective n h
  exact Subtype.ext (congrArg (fun z : DiagonalData n => z.1.val) hd)

theorem diamondMap_reflect {n : ℕ} (x : DiamondData n) :
    latticeReflect (diamondMap x) = diamondMap x := by
  apply Subtype.ext
  change reflect '' (diamondMap x).val = (diamondMap x).val
  rw [diamondMap_val, diamond_reflection]

theorem diagonal_intersection_eq_diamonds (n : ℕ) :
    positiveDiagonals n ∩ negativeDiagonals n = Set.range (@diamondMap n) := by
  ext L
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨hd, he, ht0, htd, hg⟩ := diagonalData_good x
    obtain ⟨hD, hE, hT0, hTD, hG⟩ := diagonalData_good y
    have hs := congrArg Subtype.val (hx.trans hy.symm)
    have hb := diagonal_reflection_forces_boundary _ _ _ _ _ _ hd he ht0 htd hD hE hT0 hTD hg hG hs
    have ht : x.2.val = 0 := by exact_mod_cast hb.1
    have heq : n / x.1.val = 2 * x.1.val := by exact_mod_cast hb.2
    have hm := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors x.1.property)
    have hn : n = 2 * x.1.val ^ 2 := by rw [heq] at hm; nlinarith only [hm]
    let z : DiamondData n := ⟨x.1.val, Finset.mem_filter.mpr ⟨x.1.property, hn⟩⟩
    refine ⟨z, ?_⟩
    have hz : diamondMap z = diagonalMap x := by
      apply Subtype.ext
      rw [diamondMap_val]
      change span ((x.1.val : ℤ), (x.1.val : ℤ)) (0, 2 * (x.1.val : ℤ)) =
        span ((x.1.val : ℤ), (x.1.val : ℤ)) (-(x.2.val : ℤ), (n / x.1.val : ℕ) - (x.2.val : ℤ))
      rw [ht, heq]
      simp only [Nat.cast_zero, neg_zero, sub_zero, Nat.cast_mul, Nat.cast_ofNat]
    exact hz.trans hx
  · rintro ⟨x, rfl⟩
    exact ⟨⟨diamondToDiagonal x, rfl⟩, ⟨diamondToDiagonal x, diamondMap_reflect x⟩⟩

theorem diagonal_intersection_card (n : ℕ) :
    (positiveDiagonals n ∩ negativeDiagonals n).ncard = twiceSquareCount n := by
  rw [diagonal_intersection_eq_diamonds,
    Set.ncard_range_of_injective (diamondMap_injective n), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

theorem missing_lattice_card {n : ℕ} (hn : 0 < n) :
    Nat.card {L : Lattice n // ¬ Black L.val ∧ ¬ White L.val} = missing n := by
  have hp : (positiveDiagonals n).Finite := Set.finite_range _
  have hm : (negativeDiagonals n).Finite := Set.finite_range _
  have hc := Set.ncard_union_add_ncard_inter (positiveDiagonals n) (negativeDiagonals n) hp hm
  rw [← missing_eq_diagonal_union hn, diagonal_intersection_card,
    positiveDiagonals_card, negativeDiagonals_card] at hc
  have hd := diagonalData_twice_card n
  change (missingLattices n).ncard = missing n
  omega

end A368207Lattice

/- A368207DivisorLimit -/

namespace A368207DivisorLimit

open Finset Filter Topology

lemma cube_le_eight_two_pow (e : ℕ) : (e + 1) ^ 3 ≤ 8 * 2 ^ e := by
  have h (k : ℕ) : (k + 4) ^ 3 ≤ 8 * 2 ^ (k + 3) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hs : (k + 5) ^ 3 ≤ 2 * (k + 4) ^ 3 := by
        calc
          (k + 5) ^ 3 ≤ (k + 5) ^ 3 + (k ^ 3 + 9 * k ^ 2 + 21 * k + 3) :=
            Nat.le_add_right _ _
          _ = 2 * (k + 4) ^ 3 := by ring
      have hm := Nat.mul_le_mul_left 2 ih
      have hp : 8 * 2 ^ (k + 1 + 3) = 2 * (8 * 2 ^ (k + 3)) := by
        rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ]
        ring
      simpa only [Nat.succ_eq_add_one, show k + 1 + 4 = k + 5 by omega, hp]
        using hs.trans hm
  rcases e with _ | _ | _ | k
  · norm_num
  · norm_num
  · norm_num
  · simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using h k

lemma cube_le_prime_pow (p e : ℕ) (hp : 8 ≤ p) : (e + 1) ^ 3 ≤ p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hle : e + 2 ≤ 2 * (e + 1) := by omega
    calc
      (e + 1 + 1) ^ 3 ≤ (2 * (e + 1)) ^ 3 := Nat.pow_le_pow_left hle 3
      _ = 8 * (e + 1) ^ 3 := by ring
      _ ≤ 8 * p ^ e := Nat.mul_le_mul_left 8 ih
      _ ≤ p * p ^ e := Nat.mul_le_mul_right _ hp
      _ = p ^ (e + 1) := (pow_succ' p e).symm

lemma factor_bound (p e : ℕ) (hp : p.Prime) :
    (e + 1) ^ 3 ≤ (if p < 8 then 8 else 1) * p ^ e := by
  split_ifs with h
  · exact (cube_le_eight_two_pow e).trans
      (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hp.two_le e))
  · simpa using cube_le_prime_pow p e (by omega)

lemma divisor_cube_bound (n : ℕ) : n.divisors.card ^ 3 ≤ 8 ^ 8 * n := by
  by_cases hn : n = 0
  · subst n; simp
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 3
        ≤ ∏ p ∈ n.primeFactors,
          (if p < 8 then 8 else 1) * p ^ n.factorization p := by
      exact prod_le_prod' fun p hp => factor_bound p _ (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors, if p < 8 then 8 else 1) * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ 8 ^ 8 * n := by
      apply Nat.mul_le_mul_right
      have hc : (n.primeFactors.filter (fun p => p < 8)).card ≤ 8 := by
        calc
          _ ≤ (Finset.range 8).card := card_le_card (by
            intro p hp
            exact mem_range.mpr (mem_filter.mp hp).2)
          _ = 8 := card_range 8
      have he : (∏ p ∈ n.primeFactors, if p < 8 then 8 else 1) =
          8 ^ (n.primeFactors.filter (fun p => p < 8)).card := by
        simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
      rw [he]
      exact Nat.pow_le_pow_right (by omega) hc

theorem divisor_ratio_tendsto :
    Tendsto (fun n : ℕ => (n.divisors.card : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let C : ℝ := 8 ^ 8
  let M : ℝ := C / ε ^ 3
  obtain ⟨N, hN⟩ := exists_nat_gt (M ^ 2 + 1)
  refine ⟨N, ?_⟩
  intro n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnb : M ^ 2 + 1 < (n : ℝ) := hN.trans_le hnR
  have hnpos : 0 < (n : ℝ) := by nlinarith [sq_nonneg M]
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsq := Real.sq_sqrt hnpos.le
  have hM : M < Real.sqrt n := by nlinarith [sq_nonneg M]
  have he3 : 0 < ε ^ 3 := pow_pos hε _
  have hlarge : C < ε ^ 3 * Real.sqrt n := by
    have hh := (div_lt_iff₀ he3).mp hM
    simpa only [mul_comm] using hh
  have hbound : (n.divisors.card : ℝ) ^ 3 ≤ C * n := by
    dsimp [C]
    exact_mod_cast divisor_cube_bound n
  have hnonneg : 0 ≤ (n.divisors.card : ℝ) / Real.sqrt n := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  by_contra hnot
  have hlow : ε * Real.sqrt n ≤ (n.divisors.card : ℝ) :=
    (le_div_iff₀ hspos).mp (le_of_not_gt hnot)
  have hcube := pow_le_pow_left₀ (show 0 ≤ ε * Real.sqrt n by positivity) hlow 3
  have hmul := mul_lt_mul_of_pos_right hlarge hnpos
  have hident : (ε * Real.sqrt n) ^ 3 = (ε ^ 3 * Real.sqrt n) * n := by
    calc
      _ = (ε ^ 3 * Real.sqrt n) * (Real.sqrt n) ^ 2 := by ring
      _ = _ := by rw [hsq]
  rw [hident] at hcube
  exact (not_lt_of_ge (hbound.trans' hcube)) hmul

end A368207DivisorLimit

/- Consequences from reduction PR #31996. -/

namespace OMA.R_oeis_a368207_R1

open Finset Filter Topology ArithmeticFunction OMA.S_oeis_a368207

def H1 : Prop := ∀ n : ℕ, 0 < n →
  2 * a n = sigma 1 n +
    ∑ d ∈ n.divisors.filter (fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n),
      if d ^ 2 = n then 2 * d - 1
      else max 1 (2 * (2 * min d (n / d) - max d (n / d)))

def H2 : Prop :=
  Tendsto (fun n : ℕ => (n.divisors.card : ℝ) / Real.sqrt n) atTop (𝓝 0)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a368207.main := by
  intro h1 h2
  let middle (n : ℕ) : Finset ℕ :=
    n.divisors.filter fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n

  let weight (n d : ℕ) : ℕ :=
    if d ^ 2 = n then 2 * d - 1
    else max 1 (2 * (2 * min d (n / d) - max d (n / d)))

  let correction (n : ℕ) : ℕ := ∑ d ∈ middle n, weight n d

  have weight_pos {n d : ℕ} (hd : d ∈ n.divisors) : 0 < weight n d := by
    have hp := Nat.pos_of_mem_divisors hd
    unfold weight
    split_ifs <;> omega

  have correction_zero_iff (n : ℕ) : correction n = 0 ↔ ¬ HasMiddleDivisor n := by
    constructor
    · intro hz ⟨d, hd, h1, h2⟩
      have hm : d ∈ middle n := by simp [middle, hd, h1, h2]
      have hle := Finset.single_le_sum (fun i _ => Nat.zero_le (weight n i)) hm
      have hp := weight_pos hd
      change weight n d ≤ correction n at hle
      omega
    · intro hn
      have he : middle n = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro d hd
        simp only [middle, mem_filter] at hd
        exact hn ⟨d, hd.1, hd.2⟩
      simp [correction, he]

  have pow_eq_square (p k : ℕ) : p ^ (2 * k) = (p ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]

  have pow_eq_square_mul (p k : ℕ) : p ^ (2 * k + 1) = (p ^ k) ^ 2 * p := by
    rw [pow_succ, pow_eq_square]

  have pow_gap {p i j : ℕ} (hp : 2 ≤ p) (hij : i < j) :
      2 * p ^ i ≤ p ^ j := by
    calc
      2 * p ^ i ≤ p * p ^ i := Nat.mul_le_mul_right _ hp
      _ = p ^ (i + 1) := by rw [pow_succ, Nat.mul_comm]
      _ ≤ p ^ j := Nat.pow_le_pow_right (by omega) hij

  have middle_even_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
      middle (p ^ (2 * k)) = {p ^ k} := by
    ext d
    simp only [middle, mem_filter, Nat.mem_divisors_prime_pow hp, mem_singleton]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, h1, h2⟩
      have hm : 0 < p ^ k := pow_pos hp.pos _
      have hd : 0 < p ^ j := pow_pos hp.pos _
      rw [pow_eq_square] at h1 h2
      rcases lt_trichotomy j k with h | rfl | h
      · have hgap := pow_gap hp.two_le h
        nlinarith
      · rfl
      · have hgap := pow_gap hp.two_le h
        nlinarith
    · rintro rfl
      have hm : 0 < p ^ k := pow_pos hp.pos _
      refine ⟨⟨k, by omega, rfl⟩, ?_, ?_⟩ <;> rw [pow_eq_square] <;> nlinarith

  have middle_odd_pow {p : ℕ} (hp : p.Prime) (h2 : 2 < p) (k : ℕ) :
      middle (p ^ (2 * k + 1)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    simp only [middle, mem_filter, Nat.mem_divisors_prime_pow hp] at hd
    obtain ⟨⟨j, hj, rfl⟩, h1, h2'⟩ := hd
    rw [pow_eq_square_mul] at h1 h2'
    have hm : 0 < p ^ k := pow_pos hp.pos _
    have hp3 : 3 ≤ p := h2
    by_cases hjk : j ≤ k
    · have hle : p ^ j ≤ p ^ k := Nat.pow_le_pow_right hp.one_lt.le hjk
      have hs := Nat.pow_le_pow_left hle 2
      have hl := Nat.mul_le_mul_left ((p ^ k) ^ 2) hp3
      nlinarith
    · have hjk : k + 1 ≤ j := by omega
      have hle : p ^ k * p ≤ p ^ j := by
        simpa [pow_succ] using Nat.pow_le_pow_right hp.one_lt.le hjk
      have hs := Nat.pow_le_pow_left hle 2
      have hl := Nat.mul_le_mul_left ((p ^ k) ^ 2 * p) hp3
      nlinarith

  have middle_two_odd (k : ℕ) : middle (2 ^ (2 * k + 1)) = {2 ^ k} := by
    ext d
    simp only [middle, mem_filter, Nat.mem_divisors_prime_pow Nat.prime_two, mem_singleton]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, h1, h2⟩
      have hm : 0 < 2 ^ k := Nat.two_pow_pos _
      have hd : 0 < 2 ^ j := Nat.two_pow_pos _
      rw [pow_eq_square_mul] at h1 h2
      rcases lt_trichotomy j k with h | rfl | h
      · have hgap := pow_gap (by omega : 2 ≤ 2) h
        nlinarith
      · rfl
      · have hgap := pow_gap (by omega : 2 ≤ 2) h
        nlinarith
    · rintro rfl
      have hm : 0 < 2 ^ k := Nat.two_pow_pos _
      refine ⟨⟨k, by omega, rfl⟩, ?_, ?_⟩ <;> rw [pow_eq_square_mul] <;> nlinarith

  have correction_even_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
      correction (p ^ (2 * k)) = 2 * p ^ k - 1 := by
    simp only [correction]
    rw [middle_even_pow hp, Finset.sum_singleton]
    simp [weight, pow_eq_square]

  have correction_odd_pow {p : ℕ} (hp : p.Prime) (h2 : 2 < p) (k : ℕ) :
      correction (p ^ (2 * k + 1)) = 0 := by
    simp [correction, middle_odd_pow hp h2]

  have correction_two_odd (k : ℕ) : correction (2 ^ (2 * k + 1)) = 1 := by
    have hp : 0 < 2 ^ k := Nat.two_pow_pos _
    have hn : (2 ^ k) ^ 2 ≠ 2 ^ (2 * k + 1) := by
      rw [pow_eq_square_mul]
      nlinarith
    have hd : 2 ^ (2 * k + 1) / 2 ^ k = 2 * 2 ^ k := by
      rw [pow_eq_square_mul]
      have he : (2 ^ k) ^ 2 * 2 = (2 * 2 ^ k) * 2 ^ k := by ring
      rw [he, Nat.mul_div_left _ hp]
    have hle : 2 ^ k ≤ 2 * 2 ^ k := by omega
    simp [correction, middle_two_odd, weight, hn, hd, min_eq_left hle, max_eq_right hle]

  have weight_le {n d : ℕ} (hd : d ∈ n.divisors) : weight n d ≤ 4 * d := by
    have hp := Nat.pos_of_mem_divisors hd
    have hm := min_le_left d (n / d)
    unfold weight
    split_ifs <;> omega

  have correction_bound (n : ℕ) :
      (correction n : ℝ) ≤ 8 * (n.divisors.card : ℝ) * Real.sqrt n := by
    have each : ∀ d ∈ middle n, (weight n d : ℝ) ≤ 8 * Real.sqrt n := by
      intro d hd
      obtain ⟨hd, hlo, hhi⟩ := Finset.mem_filter.mp hd
      have hw : (weight n d : ℝ) ≤ 4 * (d : ℝ) := by exact_mod_cast weight_le hd
      have hsq : (d : ℝ) ^ 2 < 2 * (n : ℝ) := by exact_mod_cast hhi
      have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
      have hp := Real.sqrt_nonneg (n : ℝ)
      have hd0 : 0 ≤ (d : ℝ) := by positivity
      nlinarith
    have hc : ((middle n).card : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    calc
      (correction n : ℝ) = ∑ d ∈ middle n, (weight n d : ℝ) := by simp [correction]
      _ ≤ ∑ _d ∈ middle n, 8 * Real.sqrt n := Finset.sum_le_sum each
      _ = (middle n).card * (8 * Real.sqrt n) := by simp
      _ ≤ (n.divisors.card : ℝ) * (8 * Real.sqrt n) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 8 * (n.divisors.card : ℝ) * Real.sqrt n := by ring

  have self_le_sigma (n : ℕ) (hn : 0 < n) : n ≤ sigma 1 n := by
    rw [sigma_one_apply]
    exact Finset.single_le_sum (fun d _ => Nat.zero_le d)
      (Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩)

  have correction_ratio_bound {n : ℕ} (hn : 0 < n) :
      (correction n : ℝ) / (sigma 1 n : ℝ) ≤
        8 * ((n.divisors.card : ℝ) / Real.sqrt n) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
    have hsig : (n : ℝ) ≤ (sigma 1 n : ℝ) := by exact_mod_cast self_le_sigma n hn
    calc
      (correction n : ℝ) / (sigma 1 n : ℝ) ≤ (correction n : ℝ) / n :=
        div_le_div_of_nonneg_left (by positivity) hnR hsig
      _ ≤ (8 * (n.divisors.card : ℝ) * Real.sqrt n) / n :=
        div_le_div_of_nonneg_right (correction_bound n) hnR.le
      _ = 8 * ((n.divisors.card : ℝ) / Real.sqrt n) := by
        rw [← mul_div_assoc]
        apply (div_eq_div_iff hnR.ne' hs.ne').mpr
        calc
          (8 * (n.divisors.card : ℝ) * Real.sqrt n) * Real.sqrt n =
              8 * (n.divisors.card : ℝ) * (Real.sqrt n) ^ 2 := by ring
          _ = 8 * (n.divisors.card : ℝ) * n := by rw [Real.sq_sqrt hnR.le]

  have conjecture_one (h : ∀ n : ℕ, 0 < n → 2 * a n = sigma 1 n + correction n) : Conj1 := by
    intro n hn
    have hc := h n (by omega)
    refine ⟨by omega, ?_⟩
    rw [← correction_zero_iff]
    omega

  have conjecture_wu (h : ∀ n : ℕ, 0 < n → 2 * a n = sigma 1 n + correction n) : ConjWu := by
    refine ⟨?_, ?_, ?_⟩
    · intro p m hp hp2 hm
      obtain ⟨k, rfl⟩ := hm
      have hc := h (p ^ (2 * k + 1)) (pow_pos hp.pos _)
      rw [correction_odd_pow hp hp2, Nat.add_zero] at hc
      exact hc
    · intro p m hp hm
      obtain ⟨k, rfl⟩ := hm
      have he : k + k = 2 * k := by omega
      rw [he]
      have hc := h (p ^ (2 * k)) (pow_pos hp.pos _)
      rw [correction_even_pow hp] at hc
      have hs := sigma_pos 1 (p ^ (2 * k)) (pow_ne_zero _ hp.ne_zero)
      have hk : 0 < p ^ k := pow_pos hp.pos _
      have hd : 2 * k / 2 = k := by omega
      rw [hd]
      omega
    · intro m hm
      obtain ⟨k, rfl⟩ := hm
      have hc := h (2 ^ (2 * k + 1)) (Nat.two_pow_pos _)
      rwa [correction_two_odd] at hc

  have correction_limit (h : H2) :
      Tendsto (fun n : ℕ => (correction n : ℝ) / (sigma 1 n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => by positivity))
      (g := fun n : ℕ => 8 * ((n.divisors.card : ℝ) / Real.sqrt n))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact correction_ratio_bound (by omega)
    · simpa using h.const_mul 8

  have conjecture_two (h1 : ∀ n : ℕ, 0 < n → 2 * a n = sigma 1 n + correction n) (h2 : H2) : Conj2 := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hl : Tendsto
        (fun n : ℕ => (1 + (correction n : ℝ) / (sigma 1 n : ℝ)) / 2)
        atTop (𝓝 (1 / 2)) := by
      simpa using (hconst.add (correction_limit h2)).div_const (2 : ℝ)
    apply hl.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : (sigma 1 n : ℝ) ≠ 0 := by
      exact_mod_cast (sigma_pos 1 n (by omega)).ne'
    have hc : 2 * (a n : ℝ) = (sigma 1 n : ℝ) + (correction n : ℝ) := by
      exact_mod_cast h1 n (by omega)
    field_simp
    linarith

  have hid : ∀ n : ℕ, 0 < n → 2 * a n = sigma 1 n + correction n := h1
  exact ⟨conjecture_one hid, conjecture_two hid h2, conjecture_wu hid⟩

end OMA.R_oeis_a368207_R1

namespace A368207Final

theorem divisor_identity : OMA.R_oeis_a368207_R1.H1 := by
  intro n hn
  have hc := A368207Lattice.two_color_count hn
  have hm := A368207Lattice.missing_lattice_card hn
  have hi := A368207AxisCard.colored_intersection_card hn
  have hb := A368207Boundary.boundary_identity n
  rw [hm] at hc
  change 2 * (A368207Lattice.representations n).card =
    ArithmeticFunction.sigma 1 n + A368207Boundary.correction n
  omega

end A368207Final

theorem OMA.solution : type_of% @OMA.S_oeis_a368207.main := by
  exact OMA.R_oeis_a368207_R1.main A368207Final.divisor_identity
    A368207DivisorLimit.divisor_ratio_tendsto
