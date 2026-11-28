import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Order.Ring.Int

-- Credit: @Hennyrick

namespace BealCubicNorm

abbrev Triple := Int × Int × Int

/-- Multiplication in the integral power basis of a root of X³ − 2. -/
def mul (x y : Triple) : Triple :=
  (x.1*y.1 + 2*(x.2.1*y.2.2+x.2.2*y.2.1),
   x.1*y.2.1+x.2.1*y.1+2*x.2.2*y.2.2,
   x.1*y.2.2+x.2.1*y.2.1+x.2.2*y.1)

def norm (x : Triple) : Int :=
  x.1^3 + 2*x.2.1^3 + 4*x.2.2^3 - 6*x.1*x.2.1*x.2.2

/-- Three rows of the matrix of left multiplication. -/
def regular (x : Triple) : Triple × Triple × Triple :=
  ((x.1, 2*x.2.2, 2*x.2.1), (x.2.1, x.1, 2*x.2.2), (x.2.2,x.2.1,x.1))

def dot (r x : Triple) : Int := r.1*x.1+r.2.1*x.2.1+r.2.2*x.2.2

def applyMatrix (M : Triple × Triple × Triple) (x : Triple) : Triple :=
  (dot M.1 x, dot M.2.1 x, dot M.2.2 x)

def det (M : Triple × Triple × Triple) : Int :=
  let (r,s,t) := M
  r.1*(s.2.1*t.2.2 - s.2.2*t.2.1) -
  r.2.1*(s.1*t.2.2 - s.2.2*t.1) +
  r.2.2*(s.1*t.2.1 - s.2.1*t.1)

theorem regular_action (x y : Triple) : applyMatrix (regular x) y = mul x y := by
  dsimp [applyMatrix, regular, dot, mul]
  grind

theorem det_regular (x : Triple) : det (regular x) = BealCubicNorm.norm x := by
  dsimp [det, regular, BealCubicNorm.norm]
  grind

theorem norm_mul (x y : Triple) : BealCubicNorm.norm (mul x y) = BealCubicNorm.norm x * BealCubicNorm.norm y := by
  dsimp [BealCubicNorm.norm, mul]
  grind

theorem mul_assoc (x y z : Triple) : mul (mul x y) z = mul x (mul y z) := by
  dsimp [mul]
  grind

theorem mul_comm (x y : Triple) : mul x y = mul y x := by
  dsimp [mul]
  grind

def one : Triple := (1,0,0)

theorem mul_one (x : Triple) : mul x one = x := by simp [one,mul]
theorem one_mul (x : Triple) : mul one x = x := by rw [mul_comm, mul_one]

def pow (x : Triple) : Nat → Triple
  | 0 => one
  | n+1 => mul (pow x n) x

theorem norm_pow (x : Triple) (n : Nat) : BealCubicNorm.norm (pow x n) = (BealCubicNorm.norm x)^n := by
  induction n with
  | zero => simp [pow, one, BealCubicNorm.norm]
  | succ n ih => rw [pow, BealCubicNorm.norm_mul, ih, Int.pow_succ]

def eps : Triple := (-1,1,0)
def epsInv : Triple := (1,1,1)

theorem eps_mul_inv : mul eps epsInv = one := by decide
theorem inv_mul_eps : mul epsInv eps = one := by decide

theorem eps_norm : BealCubicNorm.norm eps = 1 := by decide
theorem epsInv_norm : BealCubicNorm.norm epsInv = 1 := by decide

def unit (i : Fin 5) : Triple :=
  [(1,0,0), (-1,1,0), (1,-2,1), (1,3,-3), (-7,-2,6)][i.val]'(i.isLt)

theorem unit_powers : ∀ i : Fin 5, unit i = pow eps i.val := by decide
theorem unit_norm (i : Fin 5) : BealCubicNorm.norm (unit i) = 1 := by rw [unit_powers, BealCubicNorm.norm_pow, eps_norm, Int.one_pow]

theorem target_norm {a b q : Nat} (h : a^3 + b^5 = 2^(3*q+2)) :
    BealCubicNorm.norm (-(a:Int),0,2^q) = (b:Int)^5 := by
  have hnat : a^3 + b^5 = (2^q)^3*4 := by
    rw [h, Nat.pow_add, Nat.mul_comm 3 q, Nat.pow_mul]
  have he := congrArg Int.ofNat hnat
  change ((a ^ 3 + b ^ 5 : Nat) : Int) = (((2^q)^3*4 : Nat) : Int) at he
  simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int] at he
  dsimp [BealCubicNorm.norm]
  grind

end BealCubicNorm

namespace BealCubicInterval

structure BoxInterval where
  lo : Int
  hi : Int
deriving DecidableEq

def product (B C : BoxInterval) : BoxInterval :=
  ⟨min (min (B.lo*C.lo) (B.lo*C.hi)) (min (B.hi*C.lo) (B.hi*C.hi)),
   max (max (B.lo*C.lo) (B.lo*C.hi)) (max (B.hi*C.lo) (B.hi*C.hi))⟩

def scale (d : Int) (B : BoxInterval) : BoxInterval := ⟨d*B.lo,d*B.hi⟩

private theorem between (a b x k l u : Int) (hx : a ≤ x ∧ x ≤ b)
    (ha : l ≤ a*k ∧ a*k ≤ u) (hb : l ≤ b*k ∧ b*k ≤ u) :
    l ≤ x*k ∧ x*k ≤ u := by
  by_cases hk : 0 ≤ k
  · exact ⟨Int.le_trans ha.1 (Int.mul_le_mul_of_nonneg_right hx.1 hk),
           Int.le_trans (Int.mul_le_mul_of_nonneg_right hx.2 hk) hb.2⟩
  · have hk' : k ≤ 0 := by omega
    exact ⟨Int.le_trans hb.1 (Int.mul_le_mul_of_nonpos_right hx.2 hk'),
           Int.le_trans (Int.mul_le_mul_of_nonpos_right hx.1 hk') ha.2⟩

theorem product_bounds (B C : BoxInterval) {d e x y : Int} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hx : d*B.lo ≤ x ∧ x ≤ d*B.hi) (hy : e*C.lo ≤ y ∧ y ≤ e*C.hi) :
    (d*e)*(product B C).lo ≤ x*y ∧ x*y ≤ (d*e)*(product B C).hi := by
  let l := (product B C).lo
  let u := (product B C).hi
  have hde := Int.mul_nonneg hd he
  have corner (i j : Int) (h : l ≤ i*j ∧ i*j ≤ u) :
      d*e*l ≤ (d*i)*(e*j) ∧ (d*i)*(e*j) ≤ d*e*u := by
    have hm : (d*i)*(e*j) = d*e*(i*j) := by grind
    rw [hm]
    exact ⟨Int.mul_le_mul_of_nonneg_left h.1 hde, Int.mul_le_mul_of_nonneg_left h.2 hde⟩
  have left := between _ _ _ _ _ _ hx
    (corner B.lo C.lo (by dsimp [l,u,product]; omega))
    (corner B.hi C.lo (by dsimp [l,u,product]; omega))
  have right := between _ _ _ _ _ _ hx
    (corner B.lo C.hi (by dsimp [l,u,product]; omega))
    (corner B.hi C.hi (by dsimp [l,u,product]; omega))
  rw [Int.mul_comm x y]
  apply between _ _ _ _ _ _ hy
  · simpa only [Int.mul_comm (e*C.lo) x] using left
  · simpa only [Int.mul_comm (e*C.hi) x] using right

private theorem cube_mono {a b : Int} (h : a ≤ b) : a^3 ≤ b^3 := by
  have hf : 0 ≤ 2*(a^2 + a*b + b^2) := by
    have ha := Int.sq_nonneg a
    have hb := Int.sq_nonneg b
    have hab := Int.sq_nonneg (a+b)
    grind
  have hp := Int.mul_nonneg (show 0 ≤ b-a by omega) (show 0 ≤ a^2 + a*b + b^2 by omega)
  grind

theorem cube_bounds (B : BoxInterval) {d x : Int} (hx : d*B.lo ≤ x ∧ x ≤ d*B.hi) :
    d^3*B.lo^3 ≤ x^3 ∧ x^3 ≤ d^3*B.hi^3 := by
  simpa only [Int.mul_pow] using And.intro (cube_mono hx.1) (cube_mono hx.2)

end BealCubicInterval

namespace BealCubicCover

open BealCubicNorm BealCubicInterval

/-- Coordinates are scaled by six. A bit specifies which endpoint of the
original unit cube is chosen as the approximating integral coordinate. -/
def cell (i : Fin 6) (s : Fin 2) : BoxInterval :=
  ⟨(i.val:Int) - 6*s.val, (i.val:Int) + 1 - 6*s.val⟩

def normBounds (B C T : BoxInterval) : BoxInterval :=
  let p := product (product B C) T
  ⟨B.lo^3 + 2*C.lo^3 + 4*T.lo^3 - 6*p.hi,
   B.hi^3 + 2*C.hi^3 + 4*T.hi^3 - 6*p.lo⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem finite_cover : ∀ i j k : Fin 6, ∃ s t u : Fin 2,
    -208 ≤ (normBounds (cell i s) (cell j t) (cell k u)).lo ∧
    (normBounds (cell i s) (cell j t) (cell k u)).hi ≤ 208 := by
  decide +kernel

theorem norm_bounds (B C T : BoxInterval) {d x y z : Int} (hd : 0 ≤ d)
    (hx : d*B.lo ≤ x ∧ x ≤ d*B.hi) (hy : d*C.lo ≤ y ∧ y ≤ d*C.hi)
    (hz : d*T.lo ≤ z ∧ z ≤ d*T.hi) :
    d^3*(normBounds B C T).lo ≤ BealCubicNorm.norm (x,y,z) ∧
      BealCubicNorm.norm (x,y,z) ≤ d^3*(normBounds B C T).hi := by
  have hp := product_bounds B C hd hd hx hy
  have hp' := product_bounds (product B C) T (Int.mul_nonneg hd hd) hd hp hz
  have hc1 := cube_bounds B hx
  have hc2 := cube_bounds C hy
  have hc3 := cube_bounds T hz
  let w := product (product B C) T
  change (d*d*d)*w.lo ≤ x*y*z ∧ x*y*z ≤ (d*d*d)*w.hi at hp'
  change d^3*(B.lo^3 + 2*C.lo^3 + 4*T.lo^3 - 6*w.hi) ≤
    x^3 + 2*y^3 + 4*z^3 - 6*x*y*z ∧
    x^3 + 2*y^3 + 4*z^3 - 6*x*y*z ≤ d^3*(B.hi^3 + 2*C.hi^3 + 4*T.hi^3 - 6*w.lo)
  grind

private theorem locate (x d : Int) (hd : 0 < d) (hx : 0 ≤ x ∧ x < d) :
    ∃ i : Fin 6, ∀ s : Fin 2, d*(cell i s).lo ≤ 6*(x-(s.val:Int)*d) ∧
      6*(x-(s.val:Int)*d) ≤ d*(cell i s).hi := by
  let n := 6*x/d
  have hn0 : 0 ≤ n := Int.ediv_nonneg (by omega) (by omega)
  have hn6 : n < 6 := (Int.ediv_lt_iff_lt_mul hd).mpr (by omega)
  let i : Fin 6 := ⟨n.toNat, by omega⟩
  have hi : (i.val:Int) = n := Int.toNat_of_nonneg hn0
  refine ⟨i, fun s => ?_⟩
  have l : n*d ≤ 6*x := Int.ediv_mul_le _ (by omega)
  have h : 6*x < (n+1)*d := Int.lt_ediv_add_one_mul_self _ hd
  dsimp only [cell]
  rw [hi]
  grind

/-- For any rational coefficient triple with common positive denominator d,
there is an integral triple with the absolute norm of the numerator error
strictly less than d³. -/
theorem approximate (x y z d : Int) (hd : 0 < d) :
    ∃ a b c : Int, (BealCubicNorm.norm (x-a*d, y-b*d, z-c*d)).natAbs < (d^3).natAbs := by
  have inside (t : Int) : 0 ≤ t%d ∧ t%d < d :=
    ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hd⟩
  obtain ⟨i, hi⟩ := locate _ _ hd (inside x)
  obtain ⟨j, hj⟩ := locate _ _ hd (inside y)
  obtain ⟨k, hk⟩ := locate _ _ hd (inside z)
  obtain ⟨s,t,u,hl,hh⟩ := finite_cover i j k
  let a := x/d + (s.val:Int)
  let b := y/d + (t.val:Int)
  let c := z/d + (u.val:Int)
  refine ⟨a,b,c,?_⟩
  have trans (v w : Int) : v%d - w*d = v - (v/d+w)*d := by
    have := Int.emod_add_ediv_mul v d
    grind
  have h := norm_bounds _ _ _ (d := d) (by omega) (hi s) (hj t) (hk u)
  rw [trans, trans, trans] at h
  let N := BealCubicNorm.norm (x-a*d, y-b*d, z-c*d)
  let bound := normBounds (cell i s) (cell j t) (cell k u)
  have hhom : BealCubicNorm.norm (6*(x-a*d), 6*(y-b*d), 6*(z-c*d)) = 216*N := by
    dsimp only [BealCubicNorm.norm,N]
    grind
  change d^3*bound.lo ≤ BealCubicNorm.norm (6*(x-a*d), 6*(y-b*d), 6*(z-c*d)) ∧
    BealCubicNorm.norm (6*(x-a*d), 6*(y-b*d), 6*(z-c*d)) ≤ d^3*bound.hi at h
  rw [hhom] at h
  have hd3 : 0 < d^3 := Int.pow_pos hd
  have l := Int.mul_le_mul_of_nonneg_left hl (show 0 ≤ d^3 by omega)
  have u := Int.mul_le_mul_of_nonneg_left hh (show 0 ≤ d^3 by omega)
  change d^3*(-208) ≤ d^3*bound.lo at l
  change d^3*bound.hi ≤ d^3*208 at u
  change N.natAbs < (d^3).natAbs
  have habs := Int.natAbs_eq_iff.mp (rfl : N.natAbs = N.natAbs)
  have hpos := Int.natAbs_of_nonneg (show 0 ≤ d^3 by omega)
  omega

end BealCubicCover

namespace BealCubicNorm

private theorem even_of_cube (a t : Int) (h : a^3 = 2*t) : a = 2*(a/2) := by
  let k := a/2
  by_cases he : a = 2*k
  · exact he
  · have ho : a = 2*k+1 := by dsimp [k] at *; omega
    have hc : a^3 = 2*(4*k^3+6*k^2+3*k)+1 := by rw [ho]; grind
    omega

/-- Successive division of the norm equation by 2 and 4 shows that all
three coordinates of a zero of the norm are even. -/
theorem even_coords_of_norm_zero (a b c : Int) (h : BealCubicNorm.norm (a,b,c) = 0) :
    a = 2*(a/2) ∧ b = 2*(b/2) ∧ c = 2*(c/2) := by
  change a^3 + 2*b^3 + 4*c^3 - 6*a*b*c = 0 at h
  have ha := even_of_cube a (3*a*b*c-b^3-2*c^3) (by grind)
  let i := a/2
  have hi : a = 2*i := ha
  rw [hi] at h
  have hb := even_of_cube b (3*i*b*c-2*i^3-c^3) (by grind)
  let j := b/2
  have hj : b = 2*j := hb
  rw [hj] at h
  exact ⟨ha, hb, even_of_cube c (3*i*j*c-i^3-2*j^3) (by grind)⟩

private theorem zero_coords (a b c : Int) (h : BealCubicNorm.norm (a,b,c) = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨ha,hb,hc⟩ := even_coords_of_norm_zero a b c h
  by_cases hz : a = 0 ∧ b = 0 ∧ c = 0
  · exact hz
  · let i := a/2
    let j := b/2
    let k := c/2
    have hi : a = 2*i := ha
    have hj : b = 2*j := hb
    have hk : c = 2*k := hc
    have habs {x y : Int} (hxy : x = 2*y) : x.natAbs = 2*y.natAbs := by
      rw [hxy, Int.natAbs_mul]
      rfl
    have hsmall : i.natAbs+j.natAbs+k.natAbs < a.natAbs+b.natAbs+c.natAbs := by
      have := habs hi
      have := habs hj
      have := habs hk
      have hpos : 0 < a.natAbs ∨ 0 < b.natAbs ∨ 0 < c.natAbs := by
        by_cases ha0 : a = 0
        · by_cases hb0 : b = 0
          · exact Or.inr (Or.inr (Int.natAbs_pos.mpr (by omega)))
          · exact Or.inr (Or.inl (Int.natAbs_pos.mpr hb0))
        · exact Or.inl (Int.natAbs_pos.mpr ha0)
      omega
    have hnorm : BealCubicNorm.norm (i,j,k) = 0 := by
      rw [hi,hj,hk] at h
      dsimp [BealCubicNorm.norm] at h ⊢
      grind
    obtain ⟨r,s,t⟩ := zero_coords i j k hnorm
    omega
termination_by a.natAbs+b.natAbs+c.natAbs

theorem norm_eq_zero_iff (x : Triple) : BealCubicNorm.norm x = 0 ↔ x = (0,0,0) := by
  obtain ⟨a,b,c⟩ := x
  constructor
  · intro h
    obtain ⟨rfl,rfl,rfl⟩ := zero_coords a b c h
    rfl
  · intro h
    rw [h]
    decide

end BealCubicNorm

namespace BealCubicDivision

open BealCubicNorm

def adj (x : Triple) : Triple :=
  (x.1^2 - 2*x.2.1*x.2.2, 2*x.2.2^2-x.1*x.2.1, x.2.1^2-x.1*x.2.2)

def sub (x y : Triple) : Triple :=
  (x.1-y.1,x.2.1-y.2.1,x.2.2-y.2.2)

def scale (k : Int) (x : Triple) : Triple :=
  (x.1*k,x.2.1*k,x.2.2*k)

theorem mul_adj (x : Triple) : mul x (adj x) = (BealCubicNorm.norm x,0,0) := by
  dsimp [mul, adj, BealCubicNorm.norm]
  grind

private theorem mul_scale (a : Int) (x y : Triple) :
    mul (scale a x) y = scale a (mul x y) := by
  dsimp [mul,scale]
  grind

private theorem mul_sub (x y z : Triple) : mul (sub x y) z = sub (mul x z) (mul y z) := by
  dsimp [mul,sub]
  grind

private theorem norm_scale (d : Int) (x : Triple) : BealCubicNorm.norm (scale d x) = d^3 * BealCubicNorm.norm x := by
  dsimp [BealCubicNorm.norm,scale]
  grind

private theorem error_mul (x y m : Triple) :
    mul (sub (mul x (adj y)) (scale (BealCubicNorm.norm y) m)) y = scale (BealCubicNorm.norm y) (sub x (mul m y)) := by
  rw [mul_sub, BealCubicNorm.mul_assoc, BealCubicNorm.mul_comm (adj y), mul_adj, mul_scale]
  dsimp [sub, scale, mul]
  grind

/-- Approximation of every rational triple by an integral triple within unit absolute norm. -/
def Covers : Prop := ∀ x y z d : Int, 0 < d → ∃ a b c : Int,
    (BealCubicNorm.norm (x-a*d, y-b*d, z-c*d)).natAbs < (d^3).natAbs

private theorem approx_signed (h : Covers) (x : Triple) (d : Int) (hd : d ≠ 0) :
    ∃ m : Triple, (BealCubicNorm.norm (sub x (scale d m))).natAbs < (d^3).natAbs := by
  by_cases hp : 0 < d
  · obtain ⟨a,b,c,hs⟩ := h x.1 x.2.1 x.2.2 d hp
    exact ⟨(a,b,c),hs⟩
  obtain ⟨a,b,c,hs⟩ := h x.1 x.2.1 x.2.2 (-d) (by omega)
  refine ⟨(-a,-b,-c), ?_⟩
  dsimp [sub,scale]
  simpa only [Int.neg_mul, Int.mul_neg, Int.natAbs_pow, Int.natAbs_neg] using hs

/-- A strict approximation in the norm yields Euclidean division for any divisor
of nonzero norm. The remainder is given by x minus the quotient times y. -/
theorem euclidean_division (h : Covers) (x y : Triple) (hy : BealCubicNorm.norm y ≠ 0) :
    ∃ m : Triple, (BealCubicNorm.norm (sub x (mul m y))).natAbs < (BealCubicNorm.norm y).natAbs := by
  obtain ⟨m, hm⟩ := approx_signed h (mul x (adj y)) (BealCubicNorm.norm y) hy
  refine ⟨m, ?_⟩
  have he := congrArg BealCubicNorm.norm (error_mul x y m)
  change BealCubicNorm.norm (mul _ y) = BealCubicNorm.norm (scale _ _) at he
  rw [BealCubicNorm.norm_mul, norm_scale] at he
  have ha := congrArg Int.natAbs he
  simp only [Int.natAbs_mul, Int.natAbs_pow] at ha hm
  have hpos : 0 < (BealCubicNorm.norm y).natAbs := by omega
  have hbound := Nat.mul_lt_mul_of_pos_right hm hpos
  rw [ha] at hbound
  exact Nat.lt_of_mul_lt_mul_left hbound

theorem euclidean_division_nonzero (h : Covers) (x y : Triple) (hy : y ≠ (0,0,0)) :
    ∃ m : Triple, (BealCubicNorm.norm (sub x (mul m y))).natAbs < (BealCubicNorm.norm y).natAbs :=
  euclidean_division h x y (fun hzero => hy ((norm_eq_zero_iff y).mp hzero))

end BealCubicDivision

namespace BealCubicRing

/-- The integral cubic order with power basis 1, α, α² and α³ = 2. -/
structure R where
  coords : BealCubicNorm.Triple
deriving DecidableEq

theorem R.ext {x y : R} (h : x.coords = y.coords) : x = y := by cases x; cases y; cases h; rfl

instance : Zero R := ⟨⟨0,0,0⟩⟩
instance : One R := ⟨⟨BealCubicNorm.one⟩⟩
instance : Add R := ⟨fun x y => ⟨x.coords+y.coords⟩⟩
instance : Neg R := ⟨fun x => ⟨-x.coords⟩⟩
instance : Mul R := ⟨fun x y => ⟨BealCubicNorm.mul x.coords y.coords⟩⟩

theorem coords_zero : (0:R).coords = (0,0,0) := rfl
theorem coords_one : (1:R).coords = (1,0,0) := rfl
theorem coords_add (x y : R) : (x+y).coords = x.coords+y.coords := rfl
theorem coords_neg (x : R) : (-x).coords = -x.coords := rfl
theorem coords_mul (x y : R) : (x*y).coords = BealCubicNorm.mul x.coords y.coords := rfl

instance : CommRing R := CommRing.ofMinimalAxioms
  (fun x y z => R.ext <| add_assoc x.coords y.coords z.coords)
  (fun x => R.ext <| zero_add x.coords)
  (fun x => R.ext <| neg_add_cancel x.coords)
  (fun x y z => R.ext <| BealCubicNorm.mul_assoc x.coords y.coords z.coords)
  (fun x y => R.ext <| BealCubicNorm.mul_comm x.coords y.coords)
  (fun x => R.ext <| BealCubicNorm.one_mul x.coords)
  (fun x y z => by
    apply R.ext
    simp only [coords_add, coords_mul, BealCubicNorm.mul]
    ext <;> dsimp <;> ring)

instance : Nontrivial R := ⟨⟨0,1,by decide⟩⟩

theorem coords_sub (x y : R) : (x-y).coords = BealCubicDivision.sub x.coords y.coords := by
  rw [sub_eq_add_neg, coords_add, coords_neg]
  ext <;> simp [BealCubicDivision.sub,sub_eq_add_neg]

def scalar : Int →+* R where
  toFun z := ⟨(z,0,0)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by apply R.ext; simp [coords_add]
  map_mul' x y := by apply R.ext; simp [coords_mul, BealCubicNorm.mul]

theorem coords_intCast (z : Int) : (z:R).coords = (z,0,0) := by
  rw [← map_intCast scalar z]
  rfl

def alpha : R := ⟨(0,1,0)⟩

theorem alpha_cube : alpha^3 = 2 := by
  apply R.ext
  rw [show (2:R) = ((2:Int):R) by rfl, coords_intCast]
  decide

private noncomputable def normQuotient (x y : R) : R :=
  if h : y = 0 then 0 else
    ⟨Classical.choose (BealCubicDivision.euclidean_division_nonzero
      BealCubicCover.approximate x.coords y.coords (fun h' => h (R.ext h')))⟩

private theorem normQuotient_spec (x y : R) (hy : y ≠ 0) :
    (BealCubicNorm.norm (x-y*normQuotient x y).coords).natAbs <
      (BealCubicNorm.norm y.coords).natAbs := by
  rw [coords_sub, coords_mul, BealCubicNorm.mul_comm y.coords]
  unfold normQuotient
  rw [dif_neg hy]
  exact Classical.choose_spec (BealCubicDivision.euclidean_division_nonzero
    BealCubicCover.approximate x.coords y.coords (fun h => hy (R.ext h)))

noncomputable instance : EuclideanDomain R where
  quotient := normQuotient
  quotient_zero x := by simp [normQuotient]
  remainder x y := x-y*normQuotient x y
  quotient_mul_add_remainder_eq x y := by rw [add_sub_cancel]
  r x y := (BealCubicNorm.norm x.coords).natAbs < (BealCubicNorm.norm y.coords).natAbs
  r_wellFounded := (measure (fun x : R => (BealCubicNorm.norm x.coords).natAbs)).wf
  remainder_lt x _ hy := normQuotient_spec _ _ hy
  mul_left_not_lt x y hy := by
    change ¬ (BealCubicNorm.norm (x*y).coords).natAbs < (BealCubicNorm.norm x.coords).natAbs
    rw [coords_mul, BealCubicNorm.norm_mul, Int.natAbs_mul]
    have hn : BealCubicNorm.norm y.coords ≠ 0 :=
      fun h => hy (R.ext ((BealCubicNorm.norm_eq_zero_iff _).mp h))
    have hp : 0 < (BealCubicNorm.norm y.coords).natAbs := by omega
    have h := Nat.mul_le_mul_left (BealCubicNorm.norm x.coords).natAbs
      (show 1 ≤ (BealCubicNorm.norm y.coords).natAbs by omega)
    omega

section

variable {A : Type*} [CommRing A]

/-- Evaluation in any commutative ring at a root of X³−2. -/
def evalHom (β : A) (hβ : β^3=2) : R →+* A where
  toFun x := (x.coords.1 : A) + β*x.coords.2.1 + β^2*x.coords.2.2
  map_zero' := by simp [coords_zero]
  map_one' := by simp [coords_one]
  map_add' x y := by
    simp only [coords_add, Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring
  map_mul' x y := by
    simp only [coords_mul, BealCubicNorm.mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    have hc : β^4=2*β := by rw [pow_succ, hβ]
    ring_nf
    simp only [hβ,hc]
    ring

@[simp] theorem evalHom_alpha (β : A) (hβ : β^3=2) : evalHom β hβ alpha = β := by
  simp [evalHom, alpha]

end

end BealCubicRing

namespace BealCubicExtraction

private theorem two_pow_branch_mod_nine (q : Nat) :
    2^(3*q+2) % 9 = 4 ∨ 2^(3*q+2) % 9 = 5 := by
  induction q with
  | zero => decide
  | succ q ih =>
    rw [show 3*(q+1)+2 = (3*q+2)+3 by omega, Nat.pow_add, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> decide

theorem three_not_dvd_fifth_base {a b q : Nat} (he : a ^ 3 + b ^ 5 = 2 ^ (3*q+2)) :
    ¬ 3 ∣ b := by
  intro hb
  have hb0 := Nat.mod_eq_zero_of_dvd hb
  have cubes : ∀ i : Fin 9, i.val^3 % 9 = 0 ∨ i.val^3 % 9 = 1 ∨ i.val^3 % 9 = 8 := by decide
  have fifths : ∀ i : Fin 9, i.val%3 = 0 → i.val^5 % 9 = 0 := by decide
  have hc := cubes ⟨a%9,Nat.mod_lt _ (by decide)⟩
  have hf := fifths ⟨b%9,Nat.mod_lt _ (by decide)⟩ (by change b%9%3 = 0; omega)
  change (a%9)^3%9=0 ∨ (a%9)^3%9=1 ∨ (a%9)^3%9=8 at hc
  change (b%9)^5%9=0 at hf
  rw [← Nat.pow_mod] at hf
  simp only [← Nat.pow_mod] at hc
  have h := congrArg (· % 9) he
  change (a^3 + b^5)%9 = 2^(3*q+2)%9 at h
  rw [Nat.add_mod, hf] at h
  have := two_pow_branch_mod_nine q
  omega

/-- Coprimality of the two factors in the difference of cubes, over any
commutative ring in which the equation and integer Bézout identity hold. -/
theorem coprime_factors {R : Type*} [CommRing R] {a b f : R}
    (hb : IsCoprime b (3*a^2))
    (he : f * (3*a^2 + f*(f+3*a)) = b^5) :
    IsCoprime f (3*a^2 + f*(f+3*a)) := by
  have hc : IsCoprime (b^5) (3*a^2) := hb.pow_left
  have hd : f ∣ b^5 := ⟨_, he.symm⟩
  exact (hc.of_isCoprime_of_dvd_left hd).add_mul_left_right _

/-- Over a Bézout domain, the cubic-field factor is a fifth power up to a
unit. Here α³=2 and no primality or factorization of the fifth-power base
is needed. -/
theorem associated_fifth {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] {alpha : R}
    (hα : alpha^3 = 2) {a b q : Nat} (hc : a.Coprime b)
    (he : a^3+b^5 = 2^(3*q+2)) :
    ∃ x : R, Associated (x^5) ((2 : R)^q * alpha^2 - (a : R)) := by
  let f := (2:R)^q * alpha^2 - a
  let g := 3*(a:R)^2 + f*(f+3*a)
  have ht : b.Coprime 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
    (three_not_dvd_fifth_base he)).symm
  have hi : b.Coprime (3*a^2) := ht.mul_right (hc.symm.pow_right 2)
  have hmap := hi.isCoprime.map (Int.castRingHom R)
  have hcop : IsCoprime (b:R) (3*(a:R)^2) := by simpa using hmap
  have hnat : a^3+b^5 = 4*(2^q)^3 := by
    rw [he, Nat.pow_add, Nat.mul_comm 3 q, Nat.pow_mul, Nat.mul_comm]
  have hcast := congrArg (fun n : Nat => (n:R)) hnat
  push_cast at hcast
  have hcalc : f*g = (b:R)^5 := by
    calc
      f*g = (f+a)^3 - (a:R)^3 := by dsimp [g]; ring
      _ = ((2:R)^q * alpha^2)^3 - (a:R)^3 := by rw [show f+(a:R) = (2:R)^q * alpha^2 by dsimp [f]; ring]
      _ = ((2:R)^q)^3 * (alpha^3)^2 - (a:R)^3 := by rw [mul_pow]; ring
      _ = (b:R)^5 := by rw [hα]; grind
  exact exists_associated_pow_of_mul_eq_pow' (coprime_factors hcop hcalc) hcalc

end BealCubicExtraction

namespace BealCubicExtraction

open BealCubicRing

/-- The target element of the cubic descent is a fifth power up to a unit
of the integral cubic order. -/
theorem associated_target {a b q : Nat} (hc : a.Coprime b)
    (he : a^3+b^5 = 2^(3*q+2)) :
    ∃ w : R, Associated (w^5) (R.mk (-(a:Int),0,2^q)) := by
  have h := associated_fifth alpha_cube hc he
  have hr : (2:R)^q * alpha^2 - a = R.mk (-(a:Int),0,2^q) := by
    apply R.ext
    have hq : (2:R)^q = (((2:Int)^q : Int):R) := by push_cast; rfl
    have ha : (a : R) = ((a : Int) : R) := by simp
    rw [coords_sub, coords_mul, hq, coords_intCast, ha, coords_intCast]
    have halpha : (alpha^2).coords = (0,0,1) := by decide
    rw [halpha]
    simp [BealCubicDivision.sub, BealCubicNorm.mul]
  rwa [hr] at h

end BealCubicExtraction

namespace BealCubicUnits
open BealCubicNorm

/-- An integer approximation to the coordinates of the real embedding,
with weights close to 10000 times 1, ∛2 and ∛4. -/
def height (x : Triple) : Int :=
  max |10000*x.1| (max |12599*x.2.1| |15874*x.2.2|)

private theorem forward_contract (a b c M : Int)
    (ha : |10000*a| ≤ M) (hb : |12599*b| ≤ M) (hc : |15874*c| ≤ M)
    (hab : 2*|10000*a-12599*b| < M) (hbc : 2*|12599*b-15874*c| < M)
    (hca : 2*|15874*c-10000*a| < M) :
    height (mul (a,b,c) eps) < M := by
  rw [abs_le] at ha hb hc
  have h₁ := le_abs_self (10000*a-12599*b)
  have h₂ := neg_le_abs (10000*a-12599*b)
  have h₃ := le_abs_self (12599*b-15874*c)
  have h₄ := neg_le_abs (12599*b-15874*c)
  have h₅ := le_abs_self (15874*c-10000*a)
  have h₆ := neg_le_abs (15874*c-10000*a)
  simp only [height, mul, eps, mul_neg_one, mul_one, mul_zero, zero_mul, add_zero,
    zero_add, max_lt_iff, abs_lt]
  constructor
  · constructor <;> linarith
  · constructor <;> constructor <;> linarith

private theorem inverse_contract (a b c M : Int)
    (ha : |10000*a| ≤ M) (hb : |12599*b| ≤ M) (hc : |15874*c| ≤ M)
    (h : 25*|10000*a+12599*b+15874*c| < M) :
    height (mul (a,b,c) epsInv) < M := by
  rw [abs_le] at ha hb hc
  have h₁ := le_abs_self (10000*a+12599*b+15874*c)
  have h₂ := neg_le_abs (10000*a+12599*b+15874*c)
  simp only [height, mul, epsInv, mul_one, max_lt_iff, abs_lt]
  constructor
  · constructor <;> linarith
  · constructor <;> constructor <;> linarith

/-- The quadratic factor in the identity for a sum of three cubes equals
half the sum of the three squared pairwise differences. -/
private theorem twice_square_bound {u v w M : Int}
    (hu : 0 ≤ M) (h : M ≤ 2*|u-v| ∨ M ≤ 2*|v-w| ∨ M ≤ 2*|w-u|) :
    M^2 ≤ 8*(u^2+v^2+w^2-u*v-v*w-w*u) := by
  obtain h | h | h := h
  · have h' := pow_le_pow_left₀ hu h 2
    rw [mul_pow, sq_abs] at h'
    nlinarith [sq_nonneg (v-w),sq_nonneg (w-u)]
  · have h' := pow_le_pow_left₀ hu h 2
    rw [mul_pow, sq_abs] at h'
    nlinarith [sq_nonneg (u-v),sq_nonneg (w-u)]
  · have h' := pow_le_pow_left₀ hu h 2
    rw [mul_pow, sq_abs] at h'
    nlinarith [sq_nonneg (u-v),sq_nonneg (v-w)]

set_option maxHeartbeats 1000000 in
private theorem error_bound (a b c S : Int) (ha : |a| ≤ S) (hb : |b| ≤ S) (hc : |c| ≤ S) :
    |-(100242201*b^3) - 7952376*c^3 + 104220000*a*b*c| ≤ 212414577*S^3 := by
  have hS := (abs_nonneg a).trans ha
  have hB := pow_le_pow_left₀ (abs_nonneg b) hb 3
  have hC := pow_le_pow_left₀ (abs_nonneg c) hc 3
  have hABC := mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hS) hc (abs_nonneg _) (mul_nonneg hS hS)
  calc
    _ ≤ |-(100242201*b^3) - 7952376*c^3| + |104220000*a*b*c| := abs_add_le _ _
    _ ≤ (|-(100242201*b^3)| + |7952376*c^3|) + |104220000*a*b*c| :=
      add_le_add (abs_sub _ _) (le_refl _)
    _ ≤ _ := by
      simp only [abs_mul,abs_neg,abs_pow] 
      norm_num
      linarith

/-- If neither elementary unit shortens the triple, the linear form L and
the quadratic form Q give lower bounds for its height and squared height.
Their product approximates 10¹² times the integral norm. -/
private theorem minimal_small (a b c : Int) (hn : |BealCubicNorm.norm (a,b,c)| = 1)
    (hf : height (a,b,c) ≤ height (mul (a,b,c) eps))
    (hi : height (a,b,c) ≤ height (mul (a,b,c) epsInv)) :
    max |a| (max |b| |c|) ≤ 5 := by
  let S := max |a| (max |b| |c|)
  let M := height (a,b,c)
  let u := 10000*a
  let v := 12599*b
  let w := 15874*c
  let L := u+v+w
  let Q := u^2+v^2+w^2-u*v-v*w-w*u
  have ha : |a| ≤ S := le_max_left _ _
  have hb : |b| ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hc : |c| ≤ S := (le_max_right _ _).trans (le_max_right _ _)
  have hu : |u| ≤ M := le_max_left _ _
  have hv : |v| ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hw : |w| ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hM : 0 ≤ M := (abs_nonneg _).trans hu
  have hS : 0 ≤ S := (abs_nonneg _).trans ha
  have hSM : 10000*S ≤ M := by
    dsimp [u,v,w] at hu hv hw
    simp only [abs_mul, abs_of_nonneg (by decide : (0:Int) ≤ 10000),
      abs_of_nonneg (by decide : (0:Int) ≤ 12599), abs_of_nonneg (by decide : (0:Int) ≤ 15874)] at hu hv hw
    dsimp [S]
    rcases le_total |a| (max |b| |c|) with ha' | ha'
    · rw [max_eq_right ha']
      rcases le_total |b| |c| with h | h
      · rw [max_eq_right h]
        linarith [abs_nonneg c]
      · rw [max_eq_left h]
        linarith [abs_nonneg b]
    · rwa [max_eq_left ha']
  have hL : M ≤ 25*|L| := by
    by_contra! h
    exact (not_lt_of_ge hi) (inverse_contract a b c M hu hv hw h)
  have hD : M ≤ 2*|u-v| ∨ M ≤ 2*|v-w| ∨ M ≤ 2*|w-u| := by
    by_contra! h
    exact (not_lt_of_ge hf) (forward_contract a b c M hu hv hw h.1 h.2.1 h.2.2)
  have hQ : M^2 ≤ 8*Q := twice_square_bound hM hD
  have hQn : 0 ≤ Q := by linarith [sq_nonneg M]
  have hbig := mul_le_mul hL hQ (sq_nonneg M) (mul_nonneg (by decide : (0:Int) ≤ 25) (abs_nonneg L))
  have hprod : L*Q = 1000000000000*BealCubicNorm.norm (a,b,c) +
      (-(100242201*b^3) - 7952376*c^3 + 104220000*a*b*c) := by
    dsimp [L,Q,u,v,w,BealCubicNorm.norm]
    ring
  have hbound : |L| * Q ≤ 1000000000000+212414577*S^3 := by
    calc
      _ = |L*Q| := by rw [abs_mul, abs_of_nonneg hQn]
      _ ≤ _ := by
        rw [hprod]
        apply (abs_add_le _ _).trans
        apply add_le_add _ (error_bound a b c S ha hb hc)
        rw [abs_mul, hn]
        decide
  have hm3 := pow_le_pow_left₀ (mul_nonneg (by decide : (0:Int) ≤ 10000) hS) hSM 3
  change S ≤ 5
  by_contra! h
  have hs6 : (6:Int) ≤ S := by omega
  have hs3 := pow_le_pow_left₀ (by decide : (0:Int) ≤ 6) hs6 3
  nlinarith only [hm3, hbig, hbound, hs3]

private theorem coordinate_enumeration : ∀ i j k : Fin 11,
    let x : Triple := ((i.val:Int)-5,(j.val:Int)-5,(k.val:Int)-5)
    |BealCubicNorm.norm x| = 1 → height x ≤ height (mul x eps) → height x ≤ height (mul x epsInv) →
    x = one ∨ x = (-1,0,0) := by decide +kernel

theorem minimal_unit {x : Triple} (hn : |BealCubicNorm.norm x| = 1)
    (hf : height x ≤ height (mul x eps)) (hi : height x ≤ height (mul x epsInv)) :
    x = one ∨ x = (-1,0,0) := by
  obtain ⟨a,b,c⟩ := x
  have h := minimal_small a b c hn hf hi
  simp only [max_le_iff, abs_le] at h
  let i : Fin 11 := ⟨(a+5).toNat, by omega⟩
  let j : Fin 11 := ⟨(b+5).toNat, by omega⟩
  let k : Fin 11 := ⟨(c+5).toNat, by omega⟩
  have hA : (i.val:Int)-5=a := by dsimp [i]; omega
  have hB : (j.val:Int)-5=b := by dsimp [j]; omega
  have hC : (k.val:Int)-5=c := by dsimp [k]; omega
  have t := coordinate_enumeration i j k
  dsimp only at t
  rw [hA,hB,hC] at t
  exact t hn hf hi

def negOne : Triple := (-1,0,0)

/-- Integer powers of the unit ε = ∛2−1. -/
def zpowEps : Int → Triple
  | .ofNat n => pow eps n
  | .negSucc n => pow epsInv (n+1)

theorem zpow_succ (j : Int) : zpowEps (j+1) = mul (zpowEps j) eps := by
  cases j with
  | ofNat n => rfl
  | negSucc n =>
    cases n with
    | zero => decide
    | succ n =>
      change pow epsInv (n+1) = mul (mul (pow epsInv (n+1)) epsInv) eps
      rw [BealCubicNorm.mul_assoc, inv_mul_eps, BealCubicNorm.mul_one]

theorem zpow_pred (j : Int) : zpowEps (j-1) = mul (zpowEps j) epsInv := by
  have h := zpow_succ (j-1)
  rw [show j-1+1=j by omega] at h
  rw [h, BealCubicNorm.mul_assoc, eps_mul_inv, BealCubicNorm.mul_one]

theorem zpow_add (j k : Int) : zpowEps (j+k) = mul (zpowEps j) (zpowEps k) := by
  cases k with
  | ofNat n =>
    induction n with
    | zero => change zpowEps (j+0) = mul (zpowEps j) one; rw [Int.add_zero, BealCubicNorm.mul_one]
    | succ n ih =>
      change zpowEps (j+((n:Int)+1)) = mul (zpowEps j) (mul (zpowEps (n:Int)) eps)
      change zpowEps (j+(n:Int)) = mul (zpowEps j) (zpowEps (n:Int)) at ih
      rw [← Int.add_assoc, zpow_succ, ih, BealCubicNorm.mul_assoc]
  | negSucc n =>
    induction n with
    | zero => change zpowEps (j-1) = mul (zpowEps j) epsInv; exact zpow_pred j
    | succ n ih =>
      have h : j + Int.negSucc (n+1) = (j + Int.negSucc n)-1 := by omega
      change zpowEps (j+Int.negSucc (n+1)) = mul (zpowEps j) (mul (zpowEps (Int.negSucc n)) epsInv)
      rw [h, zpow_pred, ih, BealCubicNorm.mul_assoc]

theorem zpow_mul_nat (j : Int) (n : Nat) : zpowEps ((n:Int)*j) = pow (zpowEps j) n := by
  induction n with
  | zero => change zpowEps (0*j) = one; rw [Int.zero_mul]; rfl
  | succ n ih =>
    change zpowEps (((n:Int)+1)*j) = mul (pow (zpowEps j) n) (zpowEps j)
    rw [Int.add_mul, Int.one_mul, zpow_add, ih]

theorem pow_product (x y : Triple) (n : Nat) :
    pow (mul x y) n = mul (pow x n) (pow y n) := by
  induction n with
  | zero => exact (BealCubicNorm.mul_one one).symm
  | succ n ih =>
    simp only [pow,ih]
    calc
      mul (mul (pow x n) (pow y n)) (mul x y)
          = mul (pow x n) (mul x (mul (pow y n) y)) := by
              rw [BealCubicNorm.mul_assoc, ← BealCubicNorm.mul_assoc (pow y n) x, BealCubicNorm.mul_comm (pow y n) x, BealCubicNorm.mul_assoc]
      _ = _ := (BealCubicNorm.mul_assoc _ _ _).symm

/-- Every integral triple of norm ±1 is a sign times an integer power of ε. -/
theorem units_generated (x : Triple) (hn : |BealCubicNorm.norm x| = 1) :
    ∃ s : Triple, (s = one ∨ s = negOne) ∧ ∃ j : Int, x = mul s (zpowEps j) := by
  generalize he : (height x).toNat = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    have hpos (t : Triple) : 0 ≤ height t := (abs_nonneg _).trans (le_max_left _ _)
    by_cases hf : height (mul x eps) < height x
    · have hn' : |BealCubicNorm.norm (mul x eps)| = 1 := by rw [BealCubicNorm.norm_mul,eps_norm,Int.mul_one]; exact hn
      have hlt : (height (mul x eps)).toNat < n := by have := hpos (mul x eps); omega
      obtain ⟨s,hs,j,hj⟩ := ih _ hlt _ hn' rfl
      refine ⟨s,hs,j-1,?_⟩
      rw [zpow_pred, ← BealCubicNorm.mul_assoc, ← hj, BealCubicNorm.mul_assoc, eps_mul_inv, BealCubicNorm.mul_one]
    · by_cases hi : height (mul x epsInv) < height x
      · have hn' : |BealCubicNorm.norm (mul x epsInv)| = 1 := by rw [BealCubicNorm.norm_mul,epsInv_norm,Int.mul_one]; exact hn
        have hlt : (height (mul x epsInv)).toNat < n := by have := hpos (mul x epsInv); omega
        obtain ⟨s,hs,j,hj⟩ := ih _ hlt _ hn' rfl
        refine ⟨s,hs,j+1,?_⟩
        rw [zpow_succ, ← BealCubicNorm.mul_assoc, ← hj, BealCubicNorm.mul_assoc, inv_mul_eps, BealCubicNorm.mul_one]
      · obtain hp | hp := minimal_unit hn (le_of_not_gt hf) (le_of_not_gt hi)
        · exact ⟨one, Or.inl rfl, 0, hp.trans (BealCubicNorm.mul_one one).symm⟩
        · exact ⟨negOne, Or.inr rfl, 0, hp.trans (BealCubicNorm.mul_one negOne).symm⟩

/-- The five explicit representatives used by the coefficient sieve suffice for
every integral unit, including those of norm −1. -/
theorem units_mod_fifth (x : Triple) (hn : |BealCubicNorm.norm x| = 1) :
    ∃ i : Fin 5, ∃ y : Triple, x = mul (unit i) (pow y 5) := by
  obtain ⟨s,hs,j,hj⟩ := units_generated x hn
  let i : Fin 5 := ⟨(j%5).toNat, by omega⟩
  have hri : (i.val:Int) = j%5 := by dsimp [i]; omega
  have hsign : pow s 5 = s := by rcases hs with rfl | rfl <;> decide
  refine ⟨i, mul s (zpowEps (j/5)), ?_⟩
  have hi : unit i = zpowEps (i.val:Int) := unit_powers i
  rw [pow_product,hsign,hi,hri, ← zpow_mul_nat, hj]
  have he : j = j%5 + 5*(j/5) := by omega
  calc
    mul s (zpowEps j) = mul s (mul (zpowEps (j%5)) (zpowEps (5*(j/5)))) :=
      congrArg (mul s) ((congrArg zpowEps he).trans (zpow_add _ _))
    _ = _ := by rw [← BealCubicNorm.mul_assoc, BealCubicNorm.mul_comm s, BealCubicNorm.mul_assoc]; rfl

end BealCubicUnits

namespace BealCubicRing

theorem coords_pow (x : R) (n : Nat) :
    (x^n).coords = BealCubicNorm.pow x.coords n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, coords_mul, ih]; rfl

theorem abs_norm_unit (u : Rˣ) : |BealCubicNorm.norm (u:R).coords| = 1 := by
  have h : BealCubicNorm.norm (u:R).coords * BealCubicNorm.norm (↑u⁻¹:R).coords = 1 := by
    rw [← BealCubicNorm.norm_mul, ← coords_mul, u.mul_inv]
    rfl
  have hh := congrArg Int.natAbs h
  rw [Int.natAbs_mul] at hh
  have hone : (BealCubicNorm.norm (u:R).coords).natAbs = 1 := Nat.eq_one_of_mul_eq_one_right hh
  rw [← Int.natCast_natAbs, hone]
  rfl

theorem associated_to_mod_fifth {x : BealCubicNorm.Triple}
    (hf : ∃ w : R, Associated (w^5) (R.mk x)) :
    ∃ i : Fin 5, ∃ t : BealCubicNorm.Triple,
      BealCubicNorm.mul (BealCubicNorm.unit i) (BealCubicNorm.pow t 5) = x := by
  obtain ⟨w, u, hu⟩ := hf
  obtain ⟨i, y, hy⟩ := BealCubicUnits.units_mod_fifth (u:R).coords (abs_norm_unit u)
  have hu' : (u:R) = R.mk (BealCubicNorm.unit i) * (R.mk y)^5 := by
    apply R.ext
    rw [coords_mul, coords_pow]
    exact hy
  refine ⟨i, (w * R.mk y).coords, ?_⟩
  have h : R.mk (BealCubicNorm.unit i) * (w * R.mk y)^5 = R.mk x := by
    calc
      _ = w^5 * (R.mk (BealCubicNorm.unit i) * (R.mk y)^5) := by rw [mul_pow]; ac_rfl
      _ = w^5 * (u:R) := by rw [← hu']
      _ = _ := hu
  have h' := congrArg R.coords h
  rw [coords_mul, coords_pow] at h'
  exact h'

end BealCubicRing

namespace BealCubicDescent

private theorem fifth_power (x : BealCubicNorm.Triple) :
    BealCubicNorm.pow x 5 =
      BealCubicNorm.mul x (BealCubicNorm.mul (BealCubicNorm.mul x x) (BealCubicNorm.mul x x)) := by
  simp [BealCubicNorm.pow, BealCubicNorm.one_mul, BealCubicNorm.mul_assoc]

/-- Cubic descent in the integral cubic order for the branch k ≡ 2 modulo 3. -/
theorem descent : OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1.H4 := by
  intro a b q _ _ hc he
  obtain ⟨i, x, hx⟩ := BealCubicRing.associated_to_mod_fifth
    (BealCubicExtraction.associated_target hc he)
  refine ⟨i, x, ?_⟩
  rw [fifth_power] at hx
  exact hx

end BealCubicDescent

theorem OMA.solution : OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1.H4 := by
  exact BealCubicDescent.descent
