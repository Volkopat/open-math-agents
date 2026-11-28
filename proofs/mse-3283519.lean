import OMAStatements.S_mse_3283519

/- A counterexample to dyadic uniqueness. Two complex exponential series solve the dilation equation. A cross product enforces the conditions at zero and two. Fixed-point enclosures certify the global bound and the discrepancy at three. -/

namespace OMA.FabiusInterval

def scale : ℤ := 4294967296

structure Ball where
  center : ℤ
  radius : ℤ

def Ball.Holds (a : Ball) (x : ℝ) : Prop := |(scale : ℝ)*x - a.center| ≤ a.radius

def Ball.integer (n : ℤ) : Ball := ⟨n*scale,0⟩
def Ball.add (a b : Ball) : Ball := ⟨a.center+b.center, a.radius+b.radius⟩
def Ball.neg (a : Ball) : Ball := ⟨-a.center, a.radius⟩
def Ball.times (a : Ball) (n : ℤ) : Ball := ⟨a.center*n, a.radius*|n|⟩
def Ball.divide (a : Ball) (d : ℤ) : Ball :=
  ⟨a.center / d, a.radius / d + 2⟩

def Ball.mul (a b : Ball) : Ball :=
  (⟨a.center*b.center, |a.center| *b.radius + |b.center| *a.radius + a.radius*b.radius⟩ : Ball).divide scale

lemma scale_pos : 0 < (scale : ℝ) := by norm_num [scale]

lemma Ball.holds_integer (n : ℤ) : (Ball.integer n).Holds (n : ℝ) := by
  simp [Ball.Holds,Ball.integer,mul_comm]

lemma Ball.Holds.add {a b : Ball} {x y : ℝ} (hx : a.Holds x) (hy : b.Holds y) :
    (a.add b).Holds (x+y) := by
  unfold Ball.Holds Ball.add at *
  push_cast
  calc |(scale : ℝ)*(x+y) - ((a.center : ℝ)+b.center)|
      = |((scale : ℝ)*x - a.center) + ((scale : ℝ)*y - b.center)| := by ring_nf
    _ ≤ _ := (abs_add_le ..).trans (add_le_add hx hy)

lemma Ball.Holds.neg {a : Ball} {x : ℝ} (hx : a.Holds x) : a.neg.Holds (-x) := by
  unfold Ball.Holds Ball.neg at *
  push_cast
  rwa [show (scale : ℝ)*(-x) - -(a.center : ℝ) = -((scale : ℝ)*x-a.center) by ring, abs_neg]

lemma Ball.Holds.times {a : Ball} {x : ℝ} (hx : a.Holds x) (n : ℤ) :
    (a.times n).Holds (x*n) := by
  unfold Ball.Holds Ball.times at *
  push_cast
  rw [← mul_assoc, ← sub_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

lemma round_bound (n d : ℤ) (hd : 0 < d) :
    |(n : ℝ)/d - (↑(n/d) : ℝ)| ≤ 1 := by
  have h1 := Int.ediv_mul_le n hd.ne'
  have h2 := Int.lt_ediv_add_one_mul_self n hd
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  have hl : (↑(n/d) : ℝ) * d ≤ n := by exact_mod_cast h1
  have hu : (n : ℝ) < ((↑(n/d) : ℝ)+1) * d := by exact_mod_cast h2
  exact abs_le.mpr ⟨by linarith [(le_div_iff₀ hp).mpr hl], by linarith [(div_lt_iff₀ hp).mpr hu]⟩

lemma Ball.Holds.divide {a : Ball} {x : ℝ} (hx : a.Holds x) {d : ℤ} (hd : 0 < d) :
    (a.divide d).Holds (x/d) := by
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  have hr := (abs_le.mp (round_bound a.radius d hd)).2
  unfold Ball.Holds Ball.divide at *
  push_cast
  calc |(scale : ℝ)*(x/d) - (↑(a.center / d) : ℝ)|
      = |((scale : ℝ)*x-a.center)/d + ((a.center : ℝ)/d - (↑(a.center / d) : ℝ))| := by ring_nf
    _ ≤ |((scale : ℝ)*x-a.center)/d| + |(a.center : ℝ)/d - (↑(a.center / d) : ℝ)| := abs_add_le .. 
    _ ≤ _ := by rw [abs_div,abs_of_pos hp]; linarith [div_le_div_of_nonneg_right hx hp.le,round_bound a.center d hd]

lemma Ball.Holds.mul {a b : Ball} {x y : ℝ} (hx : a.Holds x) (hy : b.Holds y) :
    (a.mul b).Holds (x*y) := by
  have ha : (0 : ℝ) ≤ a.radius := (abs_nonneg _).trans hx
  have hb : (0 : ℝ) ≤ b.radius := (abs_nonneg _).trans hy
  let p : Ball := ⟨a.center*b.center, |a.center| *b.radius + |b.center| *a.radius + a.radius*b.radius⟩
  have h : p.Holds ((scale : ℝ)*(x*y)) := by
    unfold Ball.Holds
    dsimp [p]
    push_cast
    let u := (scale : ℝ)*x - a.center
    let v := (scale : ℝ)*y - b.center
    have e : (scale : ℝ)*(scale*(x*y)) - (a.center : ℝ)*b.center =
        (a.center : ℝ)*v + (b.center : ℝ)*u + u*v := by dsimp [u,v]; ring
    rw [e]
    calc _ ≤ |(a.center : ℝ)*v| + |(b.center : ℝ)*u| + |u*v| :=
            (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
      _ ≤ _ := by
        simp only [abs_mul]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hx (abs_nonneg _))) (mul_le_mul hx hy (abs_nonneg _) ha)
  have res := h.divide (d := scale) (by decide)
  simpa only [Ball.mul,p,mul_div_cancel_left₀ _ scale_pos.ne'] using res

lemma Ball.Holds.widen {a : Ball} {x y : ℝ} (hx : a.Holds x) {r : ℤ}
    (he : |(scale : ℝ)*(y-x)| ≤ r) : (Ball.mk a.center (a.radius+r)).Holds y := by
  unfold Ball.Holds at *
  dsimp
  push_cast
  rw [show (scale : ℝ)*y - a.center = (scale*x-a.center) + scale*(y-x) by ring]
  exact (abs_add_le ..).trans (add_le_add hx he)

def Ball.magnitude (a : Ball) : ℤ := |a.center| + a.radius

lemma Ball.Holds.magnitude {a : Ball} {x : ℝ} (hx : a.Holds x) :
    |(scale : ℝ)*x| ≤ a.magnitude := by
  unfold Ball.magnitude
  push_cast
  calc |(scale : ℝ)*x| = |(a.center : ℝ) + (scale*x-a.center)| := by ring_nf
    _ ≤ _ := (abs_add_le ..).trans (add_le_add le_rfl hx)

def squareN (a : Ball) : ℕ → Ball
  | 0 => a
  | n+1 => let b := squareN a n; b.mul b

lemma squareN_sound {a : Ball} {x : ℝ} (h : a.Holds x) (n : ℕ) :
    (squareN a n).Holds (x ^ (2^n : ℕ)) := by
  induction n with
  | zero => simpa [squareN] using h
  | succ n ih => simpa only [squareN, pow_succ 2 n, pow_mul, pow_two] using ih.mul ih

def smallExp (t : Ball) : Ball :=
  let b := (Ball.integer 1).add t
  ⟨b.center, b.radius + (t.mul t).magnitude⟩

lemma smallExp_sound {a : Ball} {t : ℝ} (h : a.Holds t) (ht : |t| ≤ 1) :
    (smallExp a).Holds (Real.exp t) := by
  apply (((Ball.holds_integer 1).add h)).widen
  have he := Real.abs_exp_sub_one_sub_id_le ht
  have hm := (h.mul h).magnitude
  rw [abs_mul,abs_of_pos scale_pos] at hm ⊢
  rw [abs_of_nonneg (mul_self_nonneg _)] at hm
  norm_num at *
  rw [show Real.exp t - (1+t) = Real.exp t-1-t by ring]
  exact (mul_le_mul_of_nonneg_left he scale_pos.le).trans (by simpa [pow_two] using hm)

def enclosureExp (a : Ball) : Ball := squareN (smallExp (a.divide 16384)) 14

lemma enclosureExp_sound {a : Ball} {x : ℝ} (h : a.Holds x) (hx : |x| ≤ 16384) :
    (enclosureExp a).Holds (Real.exp x) := by
  have hd := h.divide (d := 16384) (by decide)
  have ht : |x / 16384| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have hs := squareN_sound (smallExp_sound hd ht) 14
  norm_num only [Nat.reducePow] at hs
  rw [← Real.exp_nat_mul] at hs
  push_cast at hs
  rw [show (16384 : ℝ) * (x / 16384) = x by ring] at hs
  exact hs

def smallCos (a : Ball) : Ball :=
  let q := a.mul a
  let b := (Ball.integer 1).add (q.divide 2).neg
  let err := ((q.mul q).divide 16).magnitude
  ⟨b.center, b.radius + err⟩

lemma smallCos_sound {a : Ball} {x : ℝ} (h : a.Holds x) (hx : |x| ≤ 1) :
    (smallCos a).Holds (Real.cos x) := by
  have q := h.mul h
  apply ((Ball.holds_integer 1).add (q.divide (d := 2) (by decide)).neg).widen
  have hm := ((q.mul q).divide (d := 16) (by decide)).magnitude
  rw [abs_mul,abs_of_pos scale_pos] at hm ⊢
  norm_num at hm ⊢
  have hp : 0 ≤ x*x*(x*x)/16 := div_nonneg (mul_self_nonneg _) (by norm_num)
  rw [abs_of_nonneg hp] at hm
  refine le_trans (mul_le_mul_of_nonneg_left ?_ scale_pos.le) hm
  have he := Real.cos_bound hx
  rw [show (1 + -(x*x/2)) = 1-x^2/2 by ring]
  rw [show |x|^4 = x^4 by rw [← abs_pow,abs_of_nonneg (by positivity)]] at he
  nlinarith [sq_nonneg (x^2)]

def doubleCos (b : Ball) : Ball := ((b.mul b).times 2).add (Ball.integer (-1))

def doubleCosN (b : Ball) : ℕ → Ball
  | 0 => b
  | n+1 => doubleCos (doubleCosN b n)

lemma doubleCosN_sound {b : Ball} {t : ℝ} (h : b.Holds (Real.cos t)) (n : ℕ) :
    (doubleCosN b n).Holds (Real.cos ((2:ℝ)^n*t)) := by
  induction n with
  | zero => simpa [doubleCosN] using h
  | succ n ih =>
    have hd := ((ih.mul ih).times 2).add (Ball.holds_integer (-1))
    rw [show (2:ℝ)^(n+1)*t = 2*(2^n*t) by ring, Real.cos_two_mul]
    change (doubleCos (doubleCosN b n)).Holds _
    convert hd using 1 <;> first | rfl | push_cast; ring

def piBall : Ball := ⟨13493037705,2⟩
def logBall : Ball := ⟨2977044472,4⟩
def sqrtBall : Ball := ⟨6074001000,2⟩

lemma pi_sound : piBall.Holds Real.pi := by
  unfold Ball.Holds piBall scale
  norm_num
  exact abs_le.mpr ⟨by linarith [Real.pi_gt_d20], by linarith [Real.pi_lt_d20]⟩

lemma log_sound : logBall.Holds (Real.log 2) := by
  unfold Ball.Holds logBall scale
  norm_num
  exact abs_le.mpr ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

lemma sqrt_sound : sqrtBall.Holds (Real.sqrt 2) := by
  unfold Ball.Holds sqrtBall scale
  norm_num
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2:ℝ)
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

def unitBall : Ball := ⟨0,scale⟩

lemma unit_sound {x : ℝ} (h : |x| ≤ 1) : unitBall.Holds x := by
  unfold Ball.Holds unitBall
  simp only [Int.cast_zero, sub_zero, abs_mul, abs_of_pos scale_pos]
  linarith [mul_le_mul_of_nonneg_left h scale_pos.le]

def approxCos (a : Ball) : Ball :=
  let k := (a.center + piBall.center) / (2*piBall.center)
  let reduced := (Ball.mk a.center 0).add (piBall.times (-(2*k)))
  let t := reduced.divide 64
  if t.magnitude ≤ scale then
    let q := doubleCosN (smallCos t) 6
    let r := q.radius + a.radius
    if r < scale then ⟨q.center,r⟩ else unitBall
  else unitBall

lemma approxCos_sound {a : Ball} {x : ℝ} (ha : a.Holds x) : (approxCos a).Holds (Real.cos x) := by
  let k := (a.center + piBall.center) / (2*piBall.center)
  let x0 : ℝ := (a.center : ℝ)/scale
  let z := x0 - (k : ℝ)*(2*Real.pi)
  have hx0 : (Ball.mk a.center 0).Holds x0 := by
    unfold Ball.Holds x0
    simp [mul_div_cancel₀,scale_pos.ne']
  let t := ((Ball.mk a.center 0).add (piBall.times (-(2*k)))).divide 64
  have ht : t.Holds (z/64) := by
    have h := (hx0.add (pi_sound.times (-(2*k)))).divide (d := 64) (by decide)
    change t.Holds _ at h
    convert h using 1
    dsimp [z]; push_cast; ring
  let q := doubleCosN (smallCos t) 6
  change Ball.Holds (if t.magnitude ≤ scale then (if q.radius+a.radius < scale then ⟨q.center,q.radius+a.radius⟩ else unitBall) else unitBall) _
  split_ifs with hsmall hrad
  · have hm := ht.magnitude
    have hmag : (t.magnitude : ℝ) ≤ scale := by exact_mod_cast hsmall
    rw [abs_mul, abs_of_pos scale_pos] at hm
    have harg : |z/64| ≤ 1 := by nlinarith [scale_pos]
    have hq := doubleCosN_sound (smallCos_sound ht harg) 6
    have hz : Real.cos z = Real.cos x0 := by
      dsimp [z]
      simpa [sub_eq_add_neg] using Real.cos_add_int_mul_two_pi x0 (-k)
    rw [show (2:ℝ)^6*(z/64)=z by ring,hz] at hq
    change q.Holds (Real.cos x0) at hq
    refine hq.widen (r := a.radius) ?_
    rw [abs_mul, abs_of_pos scale_pos]
    have H := mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le x x0) scale_pos.le
    apply H.trans
    rw [← abs_of_pos scale_pos, ← abs_mul, mul_sub]
    unfold Ball.Holds at ha
    rwa [show (scale : ℝ)*x0 = a.center by dsimp [x0]; field_simp [scale_pos.ne']]
  all_goals exact unit_sound (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

def approxSin (a : Ball) : Ball := approxCos ((piBall.divide 2).add a.neg)

lemma approxSin_sound {a : Ball} {x : ℝ} (h : a.Holds x) : (approxSin a).Holds (Real.sin x) := by
  have h' := approxCos_sound ((pi_sound.divide (d := 2) (by decide)).add h.neg)
  simpa only [approxSin,Int.cast_ofNat, ←sub_eq_add_neg,Real.cos_pi_div_two_sub] using h'

end OMA.FabiusInterval

namespace OMA.P_mse_3283519
open MeasureTheory Complex Real Set Filter Topology

lemma le_one_of_concave {a b : ℝ} {F F' F'' : ℝ → ℝ}
    (ha : a ≤ 1) (hb : 1 ≤ b)
    (hF1 : F 1 = 1) (hF'1 : F' 1 = 0)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc a b, HasDerivAt F' (F'' x) x)
    (hconc : ∀ x ∈ Icc a b, F'' x ≤ 0) :
    ∀ x ∈ Icc a b, F x ≤ 1 := by
  have hanti : AntitoneOn F' (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · exact fun x hx => (hF' x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hF' x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hF' x (interior_subset hx)).deriv]
      exact hconc x (interior_subset hx)
  intro x hx
  rcases le_total x 1 with hx1 | h1x
  · have hmono : MonotoneOn F (Icc x 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc x 1)
      · exact fun t ht => (hF t ⟨hx.1.trans ht.1, ht.2.trans hb⟩).continuousAt.continuousWithinAt
      · exact fun t ht => (hF t ⟨hx.1.trans (interior_subset ht).1, (interior_subset ht).2.trans hb⟩).differentiableAt.differentiableWithinAt
      · intro t ht
        have htm : t ∈ Icc a b := ⟨hx.1.trans (interior_subset ht).1, (interior_subset ht).2.trans hb⟩
        rw [(hF t htm).deriv, ← hF'1]
        exact hanti htm ⟨ha, hb⟩ (interior_subset ht).2
    have := hmono ⟨le_rfl, hx1⟩ ⟨hx1, le_rfl⟩ hx1
    linarith
  · have hantiF : AntitoneOn F (Icc 1 x) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 1 x)
      · exact fun t ht => (hF t ⟨ha.trans ht.1, ht.2.trans hx.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => (hF t ⟨ha.trans (interior_subset ht).1, (interior_subset ht).2.trans hx.2⟩).differentiableAt.differentiableWithinAt
      · intro t ht
        have htm : t ∈ Icc a b := ⟨ha.trans (interior_subset ht).1, (interior_subset ht).2.trans hx.2⟩
        rw [(hF t htm).deriv, ← hF'1]
        exact hanti ⟨ha, hb⟩ htm (interior_subset ht).1
    have := hantiF ⟨le_rfl, h1x⟩ ⟨h1x, le_rfl⟩ h1x
    linarith

end OMA.P_mse_3283519

namespace OMA.FabiusSeries
open Complex Real Filter Set MeasureTheory Topology

noncomputable def coef (z : ℂ) (k : ℤ) : ℂ :=
  (2:ℂ)^(-(k*(k-1)/2)) * z^(-k)

lemma step (z : ℂ) (hz : z≠0) (k : ℤ) :
    coef z (k+1) * (z * (2:ℂ)^k) = coef z k := by
  have hk : (k+1)*(k+1-1)/2 = k*(k-1)/2+k := by
    rw [show (k+1)*(k+1-1) = k*(k-1)+k*2 by ring, Int.add_mul_ediv_right _ _ (by decide)]
  unfold coef; rw [hk,neg_add,neg_add, zpow_add₀ (by norm_num : (2:ℂ)≠0),zpow_add₀ hz]
  rw [zpow_neg,zpow_neg]
  have h2 : (2:ℂ)^k ≠ 0 := zpow_ne_zero _ (by norm_num)
  field_simp <;> ring

noncomputable def term (z : ℂ) (k : ℤ) (x : ℝ) : ℂ :=
  coef z k * Complex.exp (z * (2:ℂ)^k * (max x 0 : ℝ))

noncomputable def H (z : ℂ) (x : ℝ) : ℂ := ∑' k : ℤ, term z k x

lemma term_bound {z : ℂ} (hz : z.re ≤ 0) (k : ℤ) (x : ℝ) : ‖term z k x‖ ≤ ‖coef z k‖ := by
  unfold term
  rw [norm_mul,Complex.norm_exp]
  apply mul_le_of_le_one_right (norm_nonneg _)
  apply Real.exp_le_one_iff.mpr
  rw [show z*(2:ℂ)^k*(max x 0:ℝ) = z * (((2:ℝ)^k * max x 0:ℝ):ℂ) by push_cast; ring,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg hz (mul_nonneg (by positivity) (le_max_right _ _))

lemma pos_ratio {z : ℂ} (hz : 1 ≤ ‖z‖) (n : ℕ) (hn : 1≤n) :
    ‖coef z ((n:ℤ)+1)‖ ≤ (1/2:ℝ)*‖coef z n‖ := by
  have hnz : z ≠ 0 := by intro h; norm_num [h] at hz
  have he := congrArg norm (step z hnz n)
  simp only [norm_mul, zpow_natCast,norm_pow,Complex.norm_ofNat] at he
  have h2 : (2:ℝ)^1 ≤ 2^n := pow_le_pow_right₀ (by norm_num) hn
  have hpos := norm_nonneg (coef z ((n:ℤ)+1))
  have hprod : 2 ≤ ‖z‖ * (2:ℝ)^n := by nlinarith [mul_nonneg (sub_nonneg.mpr hz) (by positivity : 0 ≤ (2:ℝ)^n)]
  nlinarith [mul_le_mul_of_nonneg_left hprod hpos]

lemma neg_ratio {z : ℂ} (hz : z≠0) (h5 : ‖z‖ ≤ 5) (n : ℕ) (hn : 4≤n) :
    ‖coef z (-((n:ℤ)+1))‖ ≤ (1/2:ℝ)*‖coef z (-(n:ℤ))‖ := by
  have he := congrArg norm (step z hz (-((n:ℤ)+1)))
  rw [show -((n:ℤ)+1)+1 = -(n:ℤ) by ring] at he
  simp only [norm_mul, norm_zpow,Complex.norm_ofNat,zpow_neg,
    ← Nat.cast_succ, zpow_natCast] at he
  change ‖coef z (-(n.succ:ℤ))‖ ≤ _
  simp only [norm_inv, norm_pow, Complex.norm_ofNat] at he
  rw [←he]
  have h2 : (2:ℝ)^5 ≤ 2^(n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hp : 0 < (2:ℝ)^(n+1) := by positivity
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _) |>.trans_eq (mul_comm _ _)
  rw [← div_eq_mul_inv,div_le_iff₀ hp]
  norm_num at h2; linarith

lemma geom_bound (f : ℕ → ℝ) (N : ℕ) (hs : ∀ j, N≤j → f (j+1) ≤ (1/2:ℝ)*f j) (k : ℕ) :
    f (k+N) ≤ f N*(1/2:ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k+1+N = (k+N)+1 by omega, pow_succ]
    linarith [hs (k+N) (by omega)]

lemma summable_coef {z : ℂ} (h1 : 1≤‖z‖) (h5 : ‖z‖≤5) :
    Summable (fun k : ℤ => ‖coef z k‖) := by
  have hz : z≠0 := by intro hh; norm_num [hh] at h1
  have hg : Summable (fun n : ℕ => (1/2:ℝ)^n) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · apply (summable_nat_add_iff 10).mp
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hg.mul_left ‖coef z 10‖)
    exact geom_bound (fun n => ‖coef z n‖) 10 (fun j hj => by simpa using pos_ratio h1 j (by omega))
  · apply (summable_nat_add_iff 10).mp
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hg.mul_left ‖coef z (-10)‖)
    exact geom_bound (fun n => ‖coef z (-(n:ℤ))‖) 10
      (fun j hj => by simpa using neg_ratio hz h5 j (by omega))

lemma continuous_H {z : ℂ} (hr : z.re ≤ 0) (hc : Summable (fun k : ℤ => ‖coef z k‖)) :
    Continuous (H z) :=
  continuous_tsum (fun k => by unfold term; fun_prop) hc (term_bound hr)

lemma deriv_H {z : ℂ} (hz : z≠0) (hr : z.re ≤ 0) (hc : Summable (fun k : ℤ => ‖coef z k‖))
    {x : ℝ} (hx : 0<x) : HasDerivAt (H z) (2*H z (2*x)) x := by
  let g' := fun (k : ℤ) (y : ℝ) => (2:ℂ)*term z (k-1) (2*y)
  have shift : ∀ k : ℤ, coef z k * (z*(2:ℂ)^k) = 2*coef z (k-1) := by
    intro k
    have he := step z hz (k-1)
    rw [sub_add_cancel] at he
    rw [show (2:ℂ)^k = (2:ℂ)^(k-1)*2 by rw [←zpow_add_one₀ (by norm_num : (2:ℂ) ≠ 0),sub_add_cancel]]
    linear_combination 2*he
  have hd (k : ℤ) (y : ℝ) (hy : y ∈ Ioi (0:ℝ)) : HasDerivAt (term z k) (g' k y) y := by
    have hlin := (hasDerivAt_id y).ofReal_comp.const_mul (z*(2:ℂ)^k)
    have h := ((Complex.hasDerivAt_exp _).comp y hlin).const_mul (coef z k)
    have hh : HasDerivAt (fun t : ℝ => coef z k * Complex.exp (z*(2:ℂ)^k*(t:ℂ)))
        (g' k y) y := by
      apply h.congr_deriv
      unfold g' term
      rw [max_eq_left (by have := hy.out; linarith : 0≤2*y)]
      have e : (2:ℂ)^(k-1)*((2*y:ℝ):ℂ)=(2:ℂ)^k*(y:ℂ) := by
        push_cast
        rw [show (2:ℂ)^k = (2:ℂ)^(k-1)*2 by rw [←zpow_add_one₀ (by norm_num : (2:ℂ)≠0),sub_add_cancel]]
        ring
      rw [show z*(2:ℂ)^(k-1)*((2*y:ℝ):ℂ) = z*(2:ℂ)^k*(y:ℂ) by rw [mul_assoc,e,mul_assoc]]
      simp only [id_eq,Complex.ofReal_one,mul_one]
      linear_combination Complex.exp (z*2^k*(y:ℂ)) * shift k
    apply hh.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hy.out] with t ht
    simp [term,max_eq_left ht.le]
  have hbase : Summable (fun k : ℤ => 2*‖coef z (k-1)‖) := by
    have hs := (Equiv.subRight (1:ℤ)).summable_iff.mpr hc
    exact hs.mul_left 2
  have hder := hasDerivAt_tsum_of_isPreconnected (g := term z) (g' := g') hbase
    isOpen_Ioi isPreconnected_Ioi hd
    (fun k t _ => by
      unfold g'; rw [norm_mul,Complex.norm_ofNat]; exact mul_le_mul_of_nonneg_left (term_bound hr _ _) (by norm_num))
    hx (Summable.of_norm_bounded hc (fun k => term_bound hr k x)) hx
  apply hder.congr_deriv
  unfold g' H
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.subRight (1:ℤ)).tsum_eq (fun k => term z k (2*x))

noncomputable def finiteH (z : ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range 11, (term z n x + term z (-(n+1:ℤ)) x)

lemma trunc_H {z : ℂ} (h1 : 1≤‖z‖) (h5 : ‖z‖≤5) (hr : z.re≤0) (x : ℝ) :
    ‖H z x - finiteH z x‖ ≤ 1/1000000 := by
  let f := fun n : ℕ => term z n x + term z (-(n+1:ℤ)) x
  have hz : z≠0 := by intro hh; norm_num [hh] at h1
  have hs := summable_coef h1 h5
  have hh : Summable (fun k : ℤ => term z k x) :=
    Summable.of_norm_bounded hs (fun k => term_bound hr k x)
  have hf : Summable f := hh.hasSum.nat_add_neg_add_one.summable
  have he : (∑' n : ℕ, f n) = H z x := tsum_nat_add_neg_add_one hh
  have he' := hf.sum_add_tsum_nat_add 11
  rw [he] at he'
  have hrew : H z x - finiteH z x = ∑' n : ℕ, f (n+11) := by
    change (∑ n ∈ Finset.range 11, f n) + _ = _ at he'
    change H z x - (∑ n ∈ Finset.range 11, f n) = _
    rw [←he']; abel
  let C := ‖coef z 11‖ + ‖coef z (-12)‖
  have hgeo : ∀ n : ℕ, ‖f (n+11)‖ ≤ C*(1/2:ℝ)^n := by
    intro n
    have hp := geom_bound (fun n => ‖coef z n‖) 11
      (fun j hj => by simpa using pos_ratio h1 j (by omega)) n
    have hm := geom_bound (fun n => ‖coef z (-(n:ℤ))‖) 12
      (fun j hj => by simpa using neg_ratio hz h5 j (by omega)) n
    apply (norm_add_le ..).trans
    dsimp only [C]
    rw [add_mul]
    refine add_le_add ((term_bound hr _ x).trans hp) ((term_bound hr _ x).trans ?_)
    simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc, show (11:ℤ)+1=12 by decide] using hm
  have hg := hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ)<1)
  have hg' := hg.mul_left C
  have hs' := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hgeo hg'.summable
  rw [hrew]
  apply (norm_tsum_le_tsum_norm hs').trans
  apply (hs'.tsum_le_tsum hgeo hg'.summable).trans
  rw [hg'.tsum_eq]
  have hp : ‖coef z 11‖ ≤ (1:ℝ)/2^55 := by
    norm_num [coef,norm_mul,norm_zpow, Complex.norm_ofNat]
    first | positivity | grw [←h1]; norm_num
  have hm : ‖coef z (-12)‖ ≤ (5:ℝ)^12/2^78 := by
    norm_num [coef,norm_mul,norm_zpow,Complex.norm_ofNat]
    first | grw [h5]; norm_num | nlinarith [pow_le_pow_left₀ (norm_nonneg _) h5 12]
  dsimp [C]
  norm_num at hp hm ⊢
  linarith

end OMA.FabiusSeries

namespace OMA.FabiusSeries
open OMA.FabiusInterval Complex Real

def phaseRate (b : ℕ) : ℚ × ℚ := (-1/4, b)

def qmul (a b : ℚ × ℚ) : ℚ × ℚ :=
  (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)

def qpow (z : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1,0)
  | n+1 => qmul (qpow z n) z

noncomputable def embed (a : ℚ × ℚ) : ℂ := (a.1:ℂ)+(a.2:ℂ)*Complex.I

lemma embed_mul (a b : ℚ × ℚ) : embed (qmul a b) = embed a * embed b := by
  unfold embed qmul
  simp only [Rat.cast_sub,Rat.cast_add,Rat.cast_mul]
  linear_combination -(a.2:ℂ)*(b.2:ℂ)*Complex.I_sq

lemma embed_pow (z : ℚ × ℚ) (n : ℕ) : embed (qpow z n) = embed z ^ n := by
  induction n with
  | zero => simp [qpow,embed]
  | succ n ih => simp only [qpow,embed_mul,ih,pow_succ]

def qinv (z : ℚ × ℚ) : ℚ × ℚ :=
  (z.1/(z.1^2+z.2^2),-z.2/(z.1^2+z.2^2))

lemma embed_inv (z : ℚ × ℚ) (hz : z.1^2+z.2^2 ≠ 0) :
    embed (qinv z) = (embed z)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←embed_mul]
  have h : qmul (qinv z) z = (1,0) := by
    ext <;> dsimp [qmul,qinv] <;> field_simp [hz] <;> ring
  rw [h]; simp [embed]

def qc (b : ℕ) (k : ℤ) : ℚ × ℚ :=
  let z := phaseRate b
  let u := match k with
    | .ofNat n => qpow (qinv z) n
    | .negSucc n => qpow z (n+1)
  let w := (2:ℚ)^(-(k*(k-1)/2))
  (w*u.1,w*u.2)

lemma embed_qc (b : ℕ) (k : ℤ) : embed (qc b k) = coef (embed (phaseRate b)) k := by
  have hn : (phaseRate b).1^2+(phaseRate b).2^2≠0 := by
    dsimp [phaseRate]; positivity
  have hs (r : ℚ) (u : ℚ × ℚ) : embed (r*u.1,r*u.2) = (r:ℂ)*embed u := by
    unfold embed; push_cast; ring
  cases k with
  | ofNat n =>
    unfold qc
    rw [hs,embed_pow,embed_inv _ hn]
    unfold coef
    push_cast; simp
  | negSucc n =>
    unfold qc
    rw [hs,embed_pow]
    unfold coef
    push_cast; simp [Int.negSucc_eq]
    left; rw [←Int.natCast_one,←Int.natCast_add,zpow_natCast]

def qball (q : ℚ) : Ball := ⟨⌊q*scale⌋,1⟩

lemma qball_sound (q : ℚ) : (qball q).Holds (q:ℝ) := by
  unfold Ball.Holds qball
  dsimp
  have h1 := Int.floor_le (q*(scale:ℚ))
  have h2 := Int.lt_floor_add_one (q*(scale:ℚ))
  have hh : (⌊q*(scale:ℚ)⌋:ℝ) ≤ (q:ℝ)*scale := by exact_mod_cast h1
  have hh' : (q:ℝ)*scale < (⌊q*(scale:ℚ)⌋:ℝ)+1 := by exact_mod_cast h2
  norm_num only [Int.cast_one]; exact abs_le.mpr ⟨by linarith,by linarith⟩

noncomputable def Z (b : ℕ) := embed (phaseRate b)

lemma Z_re (b : ℕ) : (Z b).re = -1/4 := by simp [Z,embed,phaseRate,Complex.add_re,Complex.mul_re]
lemma Z_im (b : ℕ) : (Z b).im = b := by simp [Z,embed,phaseRate,Complex.add_im,Complex.mul_im]

lemma Z_bounds {b : ℕ} (h3 : 3 ≤ b) (h4 : b ≤ 4) : 1≤‖Z b‖ ∧ ‖Z b‖≤5 := by
  have h := Complex.normSq_apply (Z b)
  have he := Complex.sq_norm (Z b)
  rw [h,Z_re,Z_im] at he
  have hl : (3:ℝ)≤b := by exact_mod_cast h3
  have hu : (b:ℝ)≤4 := by exact_mod_cast h4
  have hp := norm_nonneg (Z b)
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by positivity : 0≤(b:ℝ)+4)]

lemma qc_re (b : ℕ) (k : ℤ) : (coef (Z b) k).re = ((qc b k).1 : ℝ) := by
  unfold Z; rw [←embed_qc]; simp [embed,Complex.add_re,Complex.mul_re]

lemma qc_im (b : ℕ) (k : ℤ) : (coef (Z b) k).im = ((qc b k).2 : ℝ) := by
  unfold Z; rw [←embed_qc]; simp [embed,Complex.add_im,Complex.mul_im]

def termBox (b : ℕ) (k : ℤ) (x : Ball) : Ball × Ball :=
  let a := qball (qc b k).1
  let d := qball (qc b k).2
  let s := (qball ((2:ℚ)^k)).mul x
  let e := enclosureExp (s.neg.divide 4)
  let t := s.times b
  let co := approxCos t
  let si := approxSin t
  ((e.mul ((a.mul co).add (d.mul si).neg)), e.mul ((a.mul si).add (d.mul co)))

lemma termBox_sound {x : ℝ} {X : Ball} (hx : X.Holds x) (hx0 : 0≤x) (hx32 : x≤32)
    (b : ℕ) (k : ℤ) (hk : k ≤ 10) :
    (termBox b k X).1.Holds (term (Z b) k x).re ∧
    (termBox b k X).2.Holds (term (Z b) k x).im := by
  have hp : (2:ℝ)^k ≤ 2^(10:ℤ) := zpow_le_zpow_right₀ (by norm_num) hk
  norm_num at hp
  have hs := (qball_sound ((2:ℚ)^k)).mul hx
  rw [Rat.cast_zpow, Rat.cast_ofNat] at hs
  have he := enclosureExp_sound (hs.neg.divide (d := 4) (by decide))
    (by rw [abs_of_nonpos (by have := mul_nonneg (by positivity : 0≤(2:ℝ)^k) hx0; norm_num; linarith)];
        norm_num; nlinarith [mul_le_mul hp hx32 hx0 (by norm_num)])
  have ht := hs.times (b:ℤ)
  have hc := approxCos_sound ht
  have hi := approxSin_sound ht
  have ha := qball_sound (qc b k).1
  have hd := qball_sound (qc b k).2
  rw [←qc_re] at ha
  rw [←qc_im] at hd
  have hr := he.mul ((ha.mul hc).add (hd.mul hi).neg)
  have hm := he.mul ((ha.mul hi).add (hd.mul hc))
  have e : (Z b)*(2:ℂ)^k*((max x 0:ℝ):ℂ) = (Z b)*(((2:ℝ)^k*x:ℝ):ℂ) := by
    rw [max_eq_left hx0]; push_cast; ring
  have re : ((Z b)*(((2:ℝ)^k*x:ℝ):ℂ)).re = -(2^k*x)/4 := by
    rw [Complex.mul_re,Z_re,Complex.ofReal_re,Complex.ofReal_im]; ring
  have im : ((Z b)*(((2:ℝ)^k*x:ℝ):ℂ)).im = (2^k*x)*(b:ℝ) := by
    rw [Complex.mul_im,Z_im,Complex.ofReal_re,Complex.ofReal_im]; ring
  constructor
  · change (termBox b k X).1.Holds _ at hr
    convert hr using 1
    rw [term,e,Complex.mul_re,Complex.exp_re,Complex.exp_im,re,im]
    push_cast; ring
  · change (termBox b k X).2.Holds _ at hm
    convert hm using 1
    rw [term,e,Complex.mul_im,Complex.exp_re,Complex.exp_im,re,im]
    push_cast; ring

def partialBox (b : ℕ) (X : Ball) : ℕ → Ball × Ball
  | 0 => (Ball.integer 0,Ball.integer 0)
  | j+1 =>
    let p := termBox b (j:ℤ) X
    let m := termBox b (-(j+1:ℤ)) X
    let h := partialBox b X j
    (h.1.add (p.1.add m.1),h.2.add (p.2.add m.2))

def fullBox (b : ℕ) (X : Ball) : Ball × Ball :=
  let v := partialBox b X 11
  let pad := scale/1000000+1
  (⟨v.1.center,v.1.radius+pad⟩,⟨v.2.center,v.2.radius+pad⟩)

lemma fullBox_sound {x : ℝ} {X : Ball} (hx : X.Holds x) (hx0 : 0≤x) (hx32 : x≤32)
    {b : ℕ} (h3 : 3≤b) (h4 : b≤4) :
    (fullBox b X).1.Holds (H (Z b) x).re ∧ (fullBox b X).2.Holds (H (Z b) x).im := by
  let f := fun n : ℕ => term (Z b) n x + term (Z b) (-(n+1:ℤ)) x
  have hs (j : ℕ) (hj : j≤11) :
      (partialBox b X j).1.Holds (∑ k ∈ Finset.range j, f k).re ∧
      (partialBox b X j).2.Holds (∑ k ∈ Finset.range j, f k).im := by
    induction j with
    | zero => simp [partialBox,Ball.integer,Ball.Holds]
    | succ j ih =>
      have prev := ih (by omega)
      have hp := termBox_sound hx hx0 hx32 b (j:ℤ) (by omega)
      have hm := termBox_sound hx hx0 hx32 b (-(j+1:ℤ)) (by omega)
      rw [Finset.sum_range_succ]
      exact ⟨prev.1.add (hp.1.add hm.1),prev.2.add (hp.2.add hm.2)⟩
  have hs' := hs 11 (by decide)
  change (partialBox b X 11).1.Holds (finiteH (Z b) x).re ∧
    (partialBox b X 11).2.Holds (finiteH (Z b) x).im at hs'
  have hz := Z_bounds h3 h4
  have ht := trunc_H hz.1 hz.2 (by rw [Z_re];norm_num) x
  have er := (Complex.abs_re_le_norm _).trans ht
  have ei := (Complex.abs_im_le_norm _).trans ht
  have pad {t : ℝ} (h : |t| ≤ 1/1000000) : |(scale:ℝ)*t| ≤ ((scale/1000000+1:ℤ):ℝ) := by
    rw [abs_mul,abs_of_pos scale_pos]
    apply (mul_le_mul_of_nonneg_left h scale_pos.le).trans
    norm_num [scale]
  exact ⟨hs'.1.widen (pad er),hs'.2.widen (pad ei)⟩

def tailTerm (b : ℕ) (k : ℤ) : Ball :=
  let a := qball (qc b k).1
  let d := qball (qc b k).2
  let s := (qball ((2:ℚ)^k)).mul (Ball.integer 32)
  (Ball.mk (a.magnitude+d.magnitude) 0).mul (enclosureExp (s.neg.divide 4))

def tailSum (b : ℕ) : ℕ → Ball
  | 0 => Ball.integer 0
  | j+1 => (tailSum b j).add ((tailTerm b j).add (tailTerm b (-(j+1:ℤ))))

def tailBox (b : ℕ) : Ball :=
  let h := tailSum b 11
  ⟨h.center,h.radius+(scale/1000000+1)⟩

lemma tail_term_bound (b : ℕ) (k : ℤ) (hk : k≤10) {x : ℝ} (hx : 32≤x) :
    ∃ y, (tailTerm b k).Holds y ∧ ‖term (Z b) k x‖ ≤ y := by
  let a := qball (qc b k).1
  let d := qball (qc b k).2
  let M : ℝ := ((a.magnitude:ℝ)+d.magnitude)/scale
  have hM : (Ball.mk (a.magnitude+d.magnitude) 0).Holds M := by
    dsimp [M,Ball.Holds]; push_cast; field_simp [scale_pos.ne']; simp
  have hp : (2:ℝ)^k ≤ 2^(10:ℤ) := zpow_le_zpow_right₀ (by norm_num) hk
  norm_num at hp
  have hs := (qball_sound ((2:ℚ)^k)).mul (Ball.holds_integer 32)
  simp only [Rat.cast_zpow,Rat.cast_ofNat,Int.cast_ofNat] at hs
  have hE := enclosureExp_sound (hs.neg.divide (d := 4) (by decide))
    (by rw [abs_of_nonpos (by have := (zpow_pos (by norm_num : (0:ℝ)<2) k); norm_num; linarith)]; norm_num; linarith)
  refine ⟨_,hM.mul hE,?_⟩
  have hnorm : ‖coef (Z b) k‖ ≤ M := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    apply (le_div_iff₀ scale_pos).2
    have ha := (qball_sound (qc b k).1).magnitude
    have hd := (qball_sound (qc b k).2).magnitude
    rw [←qc_re,abs_mul,abs_of_pos scale_pos] at ha
    rw [←qc_im,abs_mul,abs_of_pos scale_pos] at hd
    dsimp only [a,d]; linarith
  rw [term,norm_mul,Complex.norm_exp]
  apply mul_le_mul hnorm _ (Real.exp_nonneg _) ((norm_nonneg _).trans hnorm)
  apply Real.exp_le_exp.mpr
  rw [show (Z b)*(2:ℂ)^k*((max x 0:ℝ):ℂ) = (Z b)*(((2:ℝ)^k*x:ℝ):ℂ) by
    rw [max_eq_left (by linarith : 0≤x)]; push_cast; ring,
    Complex.mul_re,Z_re,Complex.ofReal_re,Complex.ofReal_im]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left hx (by positivity : 0≤(2:ℝ)^k)]

lemma tailBox_sound {b : ℕ} (h3 : 3≤b) (h4 : b≤4) {x : ℝ} (hx : 32≤x) :
    ∃ y, (tailBox b).Holds y ∧ ‖H (Z b) x‖ ≤ y := by
  let f := fun n : ℕ => term (Z b) n x + term (Z b) (-(n+1:ℤ)) x
  have hs (j : ℕ) (hj : j≤11) :
      ∃ y, (tailSum b j).Holds y ∧ ‖∑ k ∈ Finset.range j, f k‖ ≤ y := by
    induction j with
    | zero => exact ⟨0, by simpa [tailSum] using Ball.holds_integer 0, by simp⟩
    | succ j ih =>
      obtain ⟨v,hv,hev⟩ := ih (by omega)
      obtain ⟨p,hp,hep⟩ := tail_term_bound b (j:ℤ) (by omega) hx
      obtain ⟨m,hm,hem⟩ := tail_term_bound b (-(j+1:ℤ)) (by omega) hx
      refine ⟨_,hv.add (hp.add hm),?_⟩
      rw [Finset.sum_range_succ]
      exact (norm_add_le ..).trans (add_le_add hev ((norm_add_le ..).trans (add_le_add hep hem)))
  obtain ⟨v,hv,hev⟩ := hs 11 (by decide)
  change ‖finiteH (Z b) x‖ ≤ v at hev
  have hz := Z_bounds h3 h4
  have ht := trunc_H hz.1 hz.2 (by rw [Z_re];norm_num) x
  refine ⟨v+1/1000000,hv.widen ?_,?_⟩
  · norm_num [scale]
  · have h := norm_sub_le (H (Z b) x - finiteH (Z b) x) (-finiteH (Z b) x)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at h
    linarith

end OMA.FabiusSeries

namespace OMA.FabiusSeries
open OMA.FabiusInterval Complex Real Set MeasureTheory

structure Triple (α : Type) where
  a : α
  b : α
  c : α

noncomputable def V (x : ℝ) : Triple ℝ := ⟨(H (Z 3) x).im,(H (Z 4) x).re,(H (Z 4) x).im⟩

noncomputable def cross (v w : Triple ℝ) : Triple ℝ :=
  ⟨v.b*w.c-v.c*w.b,v.c*w.a-v.a*w.c,v.a*w.b-v.b*w.a⟩

noncomputable def dot (v w : Triple ℝ) : ℝ := (v.a*w.a+v.b*w.b)+v.c*w.c

noncomputable def weights := cross (V 0) (V 2)
noncomputable def denominator := dot weights (V 1)
noncomputable def G (x : ℝ) := dot weights (V x)/denominator

lemma continuous_mode {b : ℕ} (h3 : 3≤b) (h4 : b≤4) : Continuous (H (Z b)) := by
  have hz := Z_bounds h3 h4
  exact continuous_H (by rw [Z_re];norm_num) (summable_coef hz.1 hz.2)

lemma mode_deriv {b : ℕ} (h3 : 3≤b) (h4 : b≤4) {x : ℝ} (hx : 0<x) :
    HasDerivAt (H (Z b)) (2*H (Z b) (2*x)) x := by
  have hz := Z_bounds h3 h4
  apply deriv_H _ (by rw [Z_re];norm_num) (summable_coef hz.1 hz.2) hx
  intro h; rw [h,norm_zero] at hz; linarith [hz.1]

lemma G_zero : G 0 = 0 := by
  unfold G weights dot cross; dsimp; ring

lemma G_two : G 2 = 0 := by
  unfold G weights dot cross; dsimp; ring

lemma G_one (h : denominator ≠ 0) : G 1 = 1 := div_self h

lemma G_cont : Continuous G := by
  have h3 := continuous_mode (b := 3) (by decide) (by decide)
  have h4 := continuous_mode (b := 4) (by decide) (by decide)
  unfold G V dot; fun_prop

lemma G_deriv {x : ℝ} (hx : 0<x) : HasDerivAt G (2*G (2*x)) x := by
  have h3 := mode_deriv (b := 3) (by decide) (by decide) hx
  have h4 := mode_deriv (b := 4) (by decide) (by decide) hx
  have h3i := (Complex.imCLM.hasFDerivAt.comp x h3.hasFDerivAt).hasDerivAt
  have h4r := (Complex.reCLM.hasFDerivAt.comp x h4.hasFDerivAt).hasDerivAt
  have h4i := (Complex.imCLM.hasFDerivAt.comp x h4.hasFDerivAt).hasDerivAt
  have hh := ((((h3i.const_mul weights.a).add (h4r.const_mul weights.b)).add
    (h4i.const_mul weights.c)).div_const denominator)
  apply hh.congr_deriv
  simp [G,dot,V]; ring

lemma G_second {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun t => 2*G (2*t)) (8*G (4*x)) x := by
  have h : HasDerivAt (fun t : ℝ => 2*t) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
  apply (((G_deriv (x := 2*x) (by linarith)).comp x h).const_mul 2).congr_deriv
  rw [show 2*(2*x)=4*x by ring]; ring

lemma G_equation : ∀ x : ℝ, (if x≤0 then 0 else G x) =
    ∫ t in (0:ℝ)..(2*x), if t≤0 then 0 else G t := by
  intro x
  by_cases hx : x≤0
  · rw [if_pos hx]
    symm
    calc _ = ∫ t in (0:ℝ)..(2*x), (0:ℝ) := by
              apply intervalIntegral.integral_congr
              intro t ht
              rw [uIcc_of_ge (by linarith)] at ht
              exact if_pos ht.2
         _ = 0 := by simp
  · rw [if_neg hx]
    have hpos : 0 < x := lt_of_not_ge hx
    have he (t : ℝ) (ht : t ∈ uIcc 0 (2*x)) : (if t≤0 then 0 else G t) = G t := by
      rw [uIcc_of_le (by linarith)] at ht
      split_ifs with h
      · have : t=0 := le_antisymm h ht.1; subst t; exact G_zero.symm
      · rfl
    rw [intervalIntegral.integral_congr he]
    have hd (t : ℝ) (ht : t ∈ Ioo 0 (2*x)) : HasDerivAt (fun s : ℝ => G (s/2)) (G t) t := by
      have h : HasDerivAt (fun s : ℝ => s/2) (1/2) t := by simpa using (hasDerivAt_id t).div_const 2
      apply ((G_deriv (x := t/2) (by linarith [ht.1])).comp t h).congr_deriv
      rw [show 2*(t/2)=t by ring]; ring
    have hc : Continuous (fun s : ℝ => G (s/2)) := G_cont.comp (by fun_prop)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hc.continuousOn hd
      (G_cont.intervalIntegrable ..)]
    simp [G_zero]

lemma disproof_of_ranges (hn : 0<denominator)
    (hleft : ∀ x ∈ Icc (0:ℝ) (3/4), |G x| ≤ 1)
    (hright : ∀ x ∈ Icc (5/4:ℝ) 32, |G x| ≤ 1)
    (htail : ∀ x : ℝ, 32≤x → |G x| ≤ 1)
    (hmid : ∀ x ∈ Icc (3/4:ℝ) (5/4), -1≤G x)
    (hconc : ∀ x ∈ Icc (3:ℝ) 5, -1<G x ∧ G x≤0) :
    ¬(type_of% @OMA.S_mse_3283519.main) := by
  have hup := OMA.P_mse_3283519.le_one_of_concave (a := 3/4) (b := 5/4)
    (by norm_num) (by norm_num) (G_one hn.ne')
    (F' := fun t => 2*G (2*t)) (F'' := fun t => 8*G (4*t))
    (by simp [G_two]) (fun t ht => G_deriv (by linarith [ht.1]))
    (fun t ht => G_second (by linarith [ht.1]))
    (fun t ht => mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (hconc (4*t) ⟨by linarith [ht.1],by linarith [ht.2]⟩).2)
  let F := fun x : ℝ => if x≤0 then 0 else G x
  have hb (x : ℝ) : F x ∈ Icc (-1:ℝ) 1 := by
    by_cases hx : x≤0
    · simp [F,hx]
    simp only [F,if_neg hx]
    by_cases h1 : x≤3/4
    · exact abs_le.mp (hleft x ⟨(le_of_not_ge hx),h1⟩)
    by_cases h2 : 5/4≤x
    · rcases le_total x 32 with h | h
      · exact abs_le.mp (hright x ⟨h2,h⟩)
      · exact abs_le.mp (htail x h)
    have hm : x ∈ Icc (3/4:ℝ) (5/4) := ⟨by linarith,by linarith⟩
    exact ⟨hmid x hm,hup x hm⟩
  intro hall
  have h1 : F 1 = 1 := by simpa [F,show ¬ (1:ℝ)≤0 by norm_num] using G_one hn.ne'
  have h := hall F hb G_equation h1 3 0
  rw [show OMA.S_mse_3283519.calF 3 0 = -1 by decide +kernel] at h
  norm_num [F] at h
  linarith [(hconc 3 (by constructor <;> norm_num)).1]

end OMA.FabiusSeries

namespace OMA.FabiusSeries
open OMA.FabiusInterval Set

def VBox (X : Ball) : Triple Ball := ⟨(fullBox 3 X).2,(fullBox 4 X).1,(fullBox 4 X).2⟩
def TH (B : Triple Ball) (v : Triple ℝ) := B.a.Holds v.a ∧ B.b.Holds v.b ∧ B.c.Holds v.c
def CBox (v w : Triple Ball) : Triple Ball :=
  ⟨(v.b.mul w.c).add (v.c.mul w.b).neg,(v.c.mul w.a).add (v.a.mul w.c).neg,
    (v.a.mul w.b).add (v.b.mul w.a).neg⟩
def DBox (v w : Triple Ball) := ((v.a.mul w.a).add (v.b.mul w.b)).add (v.c.mul w.c)
lemma VBox_sound {X : Ball} {x : ℝ} (hx : X.Holds x) (h0 : 0≤x) (h32 : x≤32) :
    TH (VBox X) (V x) := by
  have a := fullBox_sound hx h0 h32 (b := 3) (by decide) (by decide)
  have b := fullBox_sound hx h0 h32 (b := 4) (by decide) (by decide)
  exact ⟨a.2,b⟩
lemma CBox_sound {A B : Triple Ball} {v w : Triple ℝ} (a : TH A v) (b : TH B w) :
    TH (CBox A B) (cross v w) := by
  simpa only [TH,CBox,cross,sub_eq_add_neg] using
    And.intro ((a.2.1.mul b.2.2).add (a.2.2.mul b.2.1).neg)
    (And.intro ((a.2.2.mul b.1).add (a.1.mul b.2.2).neg) ((a.1.mul b.2.1).add (a.2.1.mul b.1).neg))
lemma DBox_sound {A B : Triple Ball} {v w : Triple ℝ} (a : TH A v) (b : TH B w) :
    (DBox A B).Holds (dot v w) := ((a.1.mul b.1).add (a.2.1.mul b.2.1)).add (a.2.2.mul b.2.2)

def wc : Triple Ball := ⟨⟨-1970874852,9896515⟩,⟨-1688334549,7183521⟩,⟨-70875995,8965310⟩⟩
def dc : Ball := ⟨5863064027,59838658⟩
def domainBall (l r : ℤ) : Ball := (Ball.mk (l+r) (r-l)).divide 2

lemma domain_sound {x : ℝ} {l r : ℤ} (hl : (l:ℝ) ≤ scale*x) (hr : (scale:ℝ)*x ≤ r) :
    (domainBall l r).Holds x := by
  have h : (Ball.mk (l+r) (r-l)).Holds (2*x) := by
    unfold Ball.Holds
    dsimp; push_cast
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h' := h.divide (d := 2) (by decide)
  simpa [domainBall] using h'

lemma separated {a b : Ball} {x y : ℝ} (hx : a.Holds x) (hy : b.Holds y)
    (h : a.center+a.radius < b.center-b.radius) : x < y := by
  have e : (a.center:ℝ)+a.radius < (b.center:ℝ)-b.radius := by exact_mod_cast h
  have ex := abs_le.mp hx
  have ey := abs_le.mp hy
  apply lt_of_mul_lt_mul_left (a := (scale:ℝ)) _ scale_pos.le
  linarith

def leaf (lo hi l r : ℤ) : Bool :=
  let y := DBox wc (VBox (domainBall l r))
  let a := dc.times lo
  let b := dc.times hi
  decide (a.center+a.radius < y.center-y.radius ∧ y.center+y.radius < b.center-b.radius)

lemma denominator_gt (h : dc.Holds denominator) : 1 < denominator := by
  have e := abs_le.mp h
  norm_num [dc,scale] at e
  linarith

lemma leaf_sound {lo hi l r : ℤ} {x : ℝ} (hw : TH wc weights) (hd : dc.Holds denominator)
    (h : leaf lo hi l r = true) (h0 : 0≤x) (h32 : x≤32)
    (hl : (l:ℝ) ≤ scale*x) (hr : (scale:ℝ)*x ≤ r) : (lo:ℝ)<G x ∧ G x<hi := by
  let y := DBox wc (VBox (domainBall l r))
  have hy : y.Holds (dot weights (V x)) := DBox_sound hw (VBox_sound (domain_sound hl hr) h0 h32)
  have hh : (dc.times lo).center+(dc.times lo).radius < y.center-y.radius ∧
      y.center+y.radius < (dc.times hi).center-(dc.times hi).radius := of_decide_eq_true h
  have ha := separated (hd.times lo) hy hh.1
  have hb := separated hy (hd.times hi) hh.2
  have hp : 0<denominator := by linarith [denominator_gt hd]
  exact ⟨(lt_div_iff₀ hp).2 (by linarith),(div_lt_iff₀ hp).2 (by linarith)⟩

lemma tail_sound (hw : TH wc weights) (hd : dc.Holds denominator)
    (ha : tailBox 3 = ⟨2007242456,413046⟩) (hb : tailBox 4 = ⟨4270064192,700085⟩)
    (x : ℝ) (hx : 32≤x) : |G x| ≤ 1 := by
  obtain ⟨u,hu,h3⟩ := tailBox_sound (b := 3) (by decide) (by decide) hx
  obtain ⟨v,hv,h4⟩ := tailBox_sound (b := 4) (by decide) (by decide) hx
  rw [ha] at hu
  rw [hb] at hv
  have eu := abs_le.mp hu
  have ev := abs_le.mp hv
  norm_num [scale] at eu ev
  have um : ‖H (Z 3) x‖ ≤ 1 := by linarith
  have vm : ‖H (Z 4) x‖ ≤ 1 := by linarith
  have hu' := (Complex.abs_im_le_norm _).trans um
  have hv' := (Complex.abs_re_le_norm _).trans vm
  have hv'' := (Complex.abs_im_le_norm _).trans vm
  have wa := hw.1.magnitude
  have wb := hw.2.1.magnitude
  have wcc := hw.2.2.magnitude
  norm_num [wc,scale,Ball.magnitude,abs_mul] at wa wb wcc
  have wsum : |weights.a| + |weights.b| + |weights.c| ≤ 1 := by linarith
  have e : |dot weights (V x)| ≤ 1 := by
    apply (abs_add_le ..).trans
    apply (add_le_add (abs_add_le ..) le_rfl).trans
    unfold V; dsimp only
    simp only [abs_mul]
    calc _ ≤ |weights.a| * 1+|weights.b| * 1+|weights.c| * 1 := add_le_add
               (add_le_add (mul_le_mul_of_nonneg_left hu' (abs_nonneg _))
                 (mul_le_mul_of_nonneg_left hv' (abs_nonneg _)))
               (mul_le_mul_of_nonneg_left hv'' (abs_nonneg _))
         _ ≤ 1 := by simpa using wsum
  have hd' := denominator_gt hd
  have hp : 0<denominator := by linarith
  rw [G,abs_div,abs_of_pos hp]
  exact (div_le_iff₀ hp).2 (by linarith)

end OMA.FabiusSeries

namespace OMA.FabiusSeries
open OMA.FabiusInterval
deriving instance DecidableEq for Ball
deriving instance DecidableEq for Triple

def sample0 : Triple Ball := ⟨⟨2640552486,985633⟩,⟨-3192428828,1414548⟩,⟨2619919444,1417557⟩⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma calibration0 : VBox (Ball.integer 0) = sample0 := by decide +kernel

def sample1 : Triple Ball := ⟨⟨-5217742482,739023⟩,⟨-8153703648,1175619⟩,⟨-15971151328,1901853⟩⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma calibration1 : VBox (Ball.integer 1) = sample1 := by decide +kernel

def sample2 : Triple Ball := ⟨⟨-11103553612,959852⟩,⟨13308917263,2504551⟩,⟨-8270645801,1682784⟩⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma calibration2 : VBox (Ball.integer 2) = sample2 := by decide +kernel

lemma calibrated : TH wc weights ∧ dc.Holds denominator := by
  have h0 := VBox_sound (X := Ball.integer 0) (x := 0) (by simpa using Ball.holds_integer 0) (by norm_num) (by norm_num)
  have h1 := VBox_sound (X := Ball.integer 1) (x := 1) (by simpa using Ball.holds_integer 1) (by norm_num) (by norm_num)
  have h2 := VBox_sound (X := Ball.integer 2) (x := 2) (by simpa using Ball.holds_integer 2) (by norm_num) (by norm_num)
  rw [calibration0] at h0
  rw [calibration1] at h1
  rw [calibration2] at h2
  have w := CBox_sound h0 h2
  rw [show CBox sample0 sample2 = wc by decide +kernel] at w
  have d := DBox_sound w h1
  rw [show DBox wc sample1 = dc by decide +kernel] at d
  exact ⟨w,d⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tail3 : tailBox 3 = ⟨2007242456,413046⟩ := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tail4 : tailBox 4 = ⟨4270064192,700085⟩ := by decide +kernel

end OMA.FabiusSeries

namespace OMA.FabiusSeries
open OMA.FabiusInterval Set

def RangeOn (lo hi l r : ℤ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 32 → (l:ℝ) ≤ scale*x → (scale:ℝ)*x ≤ r → (lo:ℝ)<G x ∧ G x<hi

lemma join_ranges {lo hi l m r : ℤ} (a : RangeOn lo hi l m) (b : RangeOn lo hi m r) :
    RangeOn lo hi l r := by
  intro x h0 h32 hl hr
  rcases le_total ((scale:ℝ)*x) (m:ℝ) with h | h
  · exact a x h0 h32 hl h
  · exact b x h0 h32 h hr

lemma range_of_leaf {lo hi l r : ℤ} (hw : TH wc weights) (hd : dc.Holds denominator)
    (h : leaf lo hi l r = true) : RangeOn lo hi l r :=
  fun _ h0 h32 hl hr => leaf_sound hw hd h h0 h32 hl hr


set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile0 : leaf (-1) 1 0 805306368 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile1 : leaf (-1) 1 805306368 1610612736 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile2 : leaf (-1) 1 1610612736 2013265920 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile3 : leaf (-1) 1 2013265920 2415919104 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile4 : leaf (-1) 1 2415919104 2617245696 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile5 : leaf (-1) 1 2617245696 2818572288 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile6 : leaf (-1) 1 2818572288 3019898880 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile7 : leaf (-1) 1 3019898880 3120562176 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile8 : leaf (-1) 1 3120562176 3221225472 = true := by decide +kernel

lemma sector0 (hw : TH wc weights) (hd : dc.Holds denominator) : RangeOn (-1) 1 0 3221225472 :=
  (join_ranges (join_ranges (range_of_leaf hw hd tile0) (range_of_leaf hw hd tile1)) (join_ranges (join_ranges (range_of_leaf hw hd tile2) (range_of_leaf hw hd tile3)) (join_ranges (join_ranges (range_of_leaf hw hd tile4) (range_of_leaf hw hd tile5)) (join_ranges (range_of_leaf hw hd tile6) (join_ranges (range_of_leaf hw hd tile7) (range_of_leaf hw hd tile8))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile9 : leaf (-1) 1 5368709120 5497683968 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile10 : leaf (-1) 1 5497683968 5626658816 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile11 : leaf (-1) 1 5626658816 5884608512 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile12 : leaf (-1) 1 5884608512 6400507904 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile13 : leaf (-1) 1 6400507904 6916407296 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile14 : leaf (-1) 1 6916407296 7432306688 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile15 : leaf (-1) 1 7432306688 8464105472 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile16 : leaf (-1) 1 8464105472 9495904256 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile17 : leaf (-1) 1 9495904256 10527703040 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile18 : leaf (-1) 1 10527703040 11043602432 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile19 : leaf (-1) 1 11043602432 11301552128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile20 : leaf (-1) 1 11301552128 11559501824 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile21 : leaf (-1) 1 11559501824 11817451520 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile22 : leaf (-1) 1 11817451520 12075401216 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile23 : leaf (-1) 1 12075401216 12333350912 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile24 : leaf (-1) 1 12333350912 12591300608 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile25 : leaf (-1) 1 12591300608 12849250304 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile26 : leaf (-1) 1 12849250304 13107200000 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile27 : leaf (-1) 1 13107200000 13623099392 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile28 : leaf (-1) 1 13623099392 14138998784 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile29 : leaf (-1) 1 14138998784 14654898176 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile30 : leaf (-1) 1 14654898176 15686696960 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile31 : leaf (-1) 1 15686696960 16718495744 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile32 : leaf (-1) 1 16718495744 17750294528 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile33 : leaf (-1) 1 17750294528 18782093312 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile34 : leaf (-1) 1 18782093312 19297992704 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile35 : leaf (-1) 1 19297992704 19813892096 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile36 : leaf (-1) 1 19813892096 20329791488 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile37 : leaf (-1) 1 20329791488 20845690880 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile38 : leaf (-1) 1 20845690880 21877489664 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile39 : leaf (-1) 1 21877489664 23941087232 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile40 : leaf (-1) 1 23941087232 26004684800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile41 : leaf (-1) 1 26004684800 28068282368 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile42 : leaf (-1) 1 28068282368 30131879936 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile43 : leaf (-1) 1 30131879936 32195477504 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile44 : leaf (-1) 1 32195477504 34259075072 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile45 : leaf (-1) 1 34259075072 36322672640 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile46 : leaf (-1) 1 36322672640 38386270208 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile47 : leaf (-1) 1 38386270208 42513465344 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile48 : leaf (-1) 1 42513465344 44577062912 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile49 : leaf (-1) 1 44577062912 46640660480 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile50 : leaf (-1) 1 46640660480 50767855616 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile51 : leaf (-1) 1 50767855616 54895050752 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile52 : leaf (-1) 1 54895050752 63149441024 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile53 : leaf (-1) 1 63149441024 67276636160 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile54 : leaf (-1) 1 67276636160 71403831296 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile55 : leaf (-1) 1 71403831296 137438953472 = true := by decide +kernel

lemma sector1 (hw : TH wc weights) (hd : dc.Holds denominator) : RangeOn (-1) 1 5368709120 137438953472 :=
  (join_ranges (join_ranges (join_ranges (join_ranges (join_ranges (join_ranges (join_ranges (join_ranges (join_ranges (join_ranges (range_of_leaf hw hd tile9) (range_of_leaf hw hd tile10)) (range_of_leaf hw hd tile11)) (range_of_leaf hw hd tile12)) (join_ranges (range_of_leaf hw hd tile13) (range_of_leaf hw hd tile14))) (join_ranges (range_of_leaf hw hd tile15) (range_of_leaf hw hd tile16))) (join_ranges (join_ranges (range_of_leaf hw hd tile17) (join_ranges (range_of_leaf hw hd tile18) (join_ranges (range_of_leaf hw hd tile19) (range_of_leaf hw hd tile20)))) (join_ranges (join_ranges (join_ranges (range_of_leaf hw hd tile21) (range_of_leaf hw hd tile22)) (join_ranges (range_of_leaf hw hd tile23) (range_of_leaf hw hd tile24))) (join_ranges (join_ranges (range_of_leaf hw hd tile25) (range_of_leaf hw hd tile26)) (range_of_leaf hw hd tile27))))) (join_ranges (join_ranges (join_ranges (join_ranges (range_of_leaf hw hd tile28) (range_of_leaf hw hd tile29)) (range_of_leaf hw hd tile30)) (join_ranges (range_of_leaf hw hd tile31) (range_of_leaf hw hd tile32))) (join_ranges (join_ranges (range_of_leaf hw hd tile33) (join_ranges (range_of_leaf hw hd tile34) (range_of_leaf hw hd tile35))) (join_ranges (join_ranges (range_of_leaf hw hd tile36) (range_of_leaf hw hd tile37)) (range_of_leaf hw hd tile38))))) (join_ranges (join_ranges (join_ranges (range_of_leaf hw hd tile39) (range_of_leaf hw hd tile40)) (join_ranges (range_of_leaf hw hd tile41) (range_of_leaf hw hd tile42))) (join_ranges (join_ranges (range_of_leaf hw hd tile43) (range_of_leaf hw hd tile44)) (join_ranges (range_of_leaf hw hd tile45) (range_of_leaf hw hd tile46))))) (join_ranges (join_ranges (join_ranges (range_of_leaf hw hd tile47) (join_ranges (range_of_leaf hw hd tile48) (range_of_leaf hw hd tile49))) (join_ranges (range_of_leaf hw hd tile50) (range_of_leaf hw hd tile51))) (join_ranges (range_of_leaf hw hd tile52) (join_ranges (range_of_leaf hw hd tile53) (range_of_leaf hw hd tile54))))) (range_of_leaf hw hd tile55))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile56 : leaf (-1) 4 3221225472 5368709120 = true := by decide +kernel

lemma sector2 (hw : TH wc weights) (hd : dc.Holds denominator) : RangeOn (-1) 4 3221225472 5368709120 :=
  (range_of_leaf hw hd tile56)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile57 : leaf (-1) 0 12884901888 13153337344 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile58 : leaf (-1) 0 13153337344 13421772800 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile59 : leaf (-1) 0 13421772800 13958643712 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile60 : leaf (-1) 0 13958643712 14495514624 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile61 : leaf (-1) 0 14495514624 15032385536 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile62 : leaf (-1) 0 15032385536 15569256448 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile63 : leaf (-1) 0 15569256448 16106127360 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile64 : leaf (-1) 0 16106127360 16642998272 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile65 : leaf (-1) 0 16642998272 17179869184 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile66 : leaf (-1) 0 17179869184 17716740096 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile67 : leaf (-1) 0 17716740096 18253611008 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile68 : leaf (-1) 0 18253611008 18790481920 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile69 : leaf (-1) 0 18790481920 19327352832 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile70 : leaf (-1) 0 19327352832 19864223744 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile71 : leaf (-1) 0 19864223744 20401094656 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile72 : leaf (-1) 0 20401094656 20937965568 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma tile73 : leaf (-1) 0 20937965568 21474836480 = true := by decide +kernel

lemma sector3 (hw : TH wc weights) (hd : dc.Holds denominator) : RangeOn (-1) 0 12884901888 21474836480 :=
  (join_ranges (join_ranges (join_ranges (join_ranges (join_ranges (range_of_leaf hw hd tile57) (range_of_leaf hw hd tile58)) (range_of_leaf hw hd tile59)) (join_ranges (range_of_leaf hw hd tile60) (range_of_leaf hw hd tile61))) (join_ranges (join_ranges (range_of_leaf hw hd tile62) (range_of_leaf hw hd tile63)) (join_ranges (range_of_leaf hw hd tile64) (range_of_leaf hw hd tile65)))) (join_ranges (join_ranges (join_ranges (range_of_leaf hw hd tile66) (range_of_leaf hw hd tile67)) (join_ranges (range_of_leaf hw hd tile68) (range_of_leaf hw hd tile69))) (join_ranges (join_ranges (range_of_leaf hw hd tile70) (range_of_leaf hw hd tile71)) (join_ranges (range_of_leaf hw hd tile72) (range_of_leaf hw hd tile73)))))

end OMA.FabiusSeries

namespace OMA.FabiusSeries
open OMA.FabiusInterval Set
lemma finished : ¬ (type_of% @OMA.S_mse_3283519.main) := by
  obtain ⟨hw,hd⟩ := calibrated
  apply disproof_of_ranges (by linarith [denominator_gt hd])
  · intro x hx
    have h := sector0 hw hd x hx.1 (by linarith [hx.2]) (by norm_num [scale]; linarith [hx.1])
      (by norm_num [scale]; linarith [hx.2])
    exact abs_le.mpr ⟨by norm_num at h; linarith,by norm_num at h; linarith⟩
  · intro x hx
    have h := sector1 hw hd x (by linarith [hx.1]) hx.2 (by norm_num [scale]; linarith [hx.1])
      (by norm_num [scale]; linarith [hx.2])
    exact abs_le.mpr ⟨by norm_num at h; linarith,by norm_num at h; linarith⟩
  · exact tail_sound hw hd tail3 tail4
  · intro x hx
    have h := sector2 hw hd x (by linarith [hx.1]) (by linarith [hx.2])
      (by norm_num [scale]; linarith [hx.1]) (by norm_num [scale]; linarith [hx.2])
    norm_num at h
    linarith [h.1]
  · intro x hx
    have h := sector3 hw hd x (by linarith [hx.1]) (by linarith [hx.2])
      (by norm_num [scale]; linarith [hx.1]) (by norm_num [scale]; linarith [hx.2])
    norm_num at h
    exact ⟨h.1,h.2.le⟩
end OMA.FabiusSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_3283519.main) := OMA.FabiusSeries.finished
