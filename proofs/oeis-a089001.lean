import OMAStatements.S_oeis_a089001

/-!
The norm of 1 + k√(-2) is 2k² + 1. If the norm is composite, this element
factors nontrivially in the norm-Euclidean ring ℤ[√(-2)]. Conjugating one
factor gives a second norm representation x² + 2y² with |x| > 1. It yields
a factorization of the triangular number with index (|x|-1)/2.
-/

namespace TriangularDivisors

private abbrev R := Zsqrtd (-2)

private theorem norm_coords (z : R) : z.norm = z.re ^ 2 + 2 * z.im ^ 2 := by
  unfold Zsqrtd.norm
  ring

private def quotient (x y : R) : R :=
  let s := x * star y
  ⟨s.re.bdiv y.norm.natAbs, s.im.bdiv y.norm.natAbs⟩

private theorem balanced_square (a : ℤ) {D : ℕ} (hD : 0 < D) :
    4 * (a.bmod D) ^ 2 ≤ (D : ℤ) ^ 2 := by
  have := Int.le_bmod (x := a) hD
  have := Int.bmod_le (x := a) hD
  have lo : 0 ≤ (D : ℤ) + 2 * a.bmod D := by omega
  have hi : 0 ≤ (D : ℤ) - 2 * a.bmod D := by omega
  nlinarith only [mul_nonneg lo hi]

private theorem norm_remainder (x y : R) (hy : y ≠ 0) :
    (x - y * quotient x y).norm.natAbs < y.norm.natAbs := by
  let D := y.norm.natAbs
  let s := x * star y
  let t := x - y * quotient x y
  have castD : (D : ℤ) = y.norm := Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by decide) y)
  have hD : 0 < D := Int.natAbs_pos.mpr (fun h => hy ((Zsqrtd.norm_eq_zero_iff (by decide) y).mp h))
  have scaled : t * star y = s - (y.norm : R) * quotient x y := by
    dsimp [t, s]
    rw [Zsqrtd.norm_eq_mul_conj]
    ring
  have hre : (t * star y).re = s.re.bmod D := by
    rw [scaled, Zsqrtd.re_sub, Zsqrtd.re_smul, Int.bmod_eq_self_sub_mul_bdiv, castD]
    rfl
  have him : (t * star y).im = s.im.bmod D := by
    rw [scaled, Zsqrtd.im_sub, Zsqrtd.im_smul, Int.bmod_eq_self_sub_mul_bdiv, castD]
    rfl
  have hn := norm_coords (t * star y)
  rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj, hre, him] at hn
  have reBound := balanced_square s.re hD
  have imBound := balanced_square s.im hD
  rw [castD] at reBound imBound
  have ypos : 0 < y.norm := by omega
  have lt : t.norm < y.norm := by
    by_contra! h
    nlinarith only [hn, reBound, imBound, mul_nonneg (sub_nonneg.mpr h) ypos.le,
      sq_pos_of_pos ypos]
  change t.norm.natAbs < y.norm.natAbs
  exact Int.ofNat_lt.mp (by
    simpa only [Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by decide) t),
      Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by decide) y)] using lt)

local instance : EuclideanDomain R :=
  { Zsqrtd.commRing, Zsqrtd.nontrivial with
    quotient := quotient
    remainder := fun x y => x - y * quotient x y
    quotient_zero := by intro a; simp [quotient]; rfl
    quotient_mul_add_remainder_eq := by intro a b; abel
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := fun a _ hb => norm_remainder a _ hb
    mul_left_not_lt := by
      intro a b hb
      rw [Zsqrtd.norm_mul, Int.natAbs_mul]
      have pos := Int.natAbs_pos.mpr (fun h => hb ((Zsqrtd.norm_eq_zero_iff (by decide) b).mp h))
      exact not_lt_of_ge (Nat.le_mul_of_pos_right _ pos) }

private def z (k : ℕ) : R := ⟨1, k⟩

private theorem norm_z (k : ℕ) : (z k).norm = (2*k^2+1 : ℕ) := by
  rw [norm_coords]
  push_cast
  dsimp [z]
  ring

private theorem norm_dvd_integer {k m : ℕ} (h : z k ∣ (m : R)) :
    2*k^2+1 ∣ m := by
  obtain ⟨w, hw⟩ := h
  have e : (m : R) * star (z k) = ((z k).norm : R) * w := by
    rw [hw, Zsqrtd.norm_eq_mul_conj]
    ring
  have coord := congrArg Zsqrtd.re e
  simp [z, Zsqrtd.norm] at coord
  exact_mod_cast (show ((2*k^2+1 : ℕ) : ℤ) ∣ m from ⟨w.re, by push_cast; nlinarith⟩)

private theorem nontrivial_factors (k : ℕ) (hk : 0 < k) (hc : ¬ (2*k^2+1).Prime) :
    ∃ a b : R, z k = a*b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
  let N := 2*k^2+1
  have hN : 2 ≤ N := by dsimp [N]; nlinarith [Nat.one_le_pow 2 k hk]
  obtain ⟨u, v, hu, hv, prod⟩ := (Nat.not_prime_iff_exists_mul_eq hN).mp hc
  have hnu : ¬ IsUnit (z k) := by
    rw [← Zsqrtd.norm_eq_one_iff' (by decide), norm_z]
    change ¬ ((N : ℕ) : ℤ) = 1
    omega
  have hni : ¬ Irreducible (z k) := by
    intro hi
    have hdiv : z k ∣ (u : R) * (v : R) := by
      rw [← Nat.cast_mul, prod]
      have hn : (N : R) = ((z k).norm : R) := by rw [norm_z]; norm_cast
      rw [hn, Zsqrtd.norm_eq_mul_conj]
      exact dvd_mul_right _ _
    have positive : 0 < u*v := by omega
    have posu := Nat.pos_of_mul_pos_right positive
    have posv := Nat.pos_of_mul_pos_left positive
    rcases hi.prime.dvd_or_dvd hdiv with h | h
    · exact (Nat.not_dvd_of_pos_of_lt posu hu) (norm_dvd_integer h)
    · exact (Nat.not_dvd_of_pos_of_lt posv hv) (norm_dvd_integer h)
  simpa [irreducible_iff, hnu, not_forall, not_or] using hni

private theorem alternative (k : ℕ) (hk : 0 < k) (hc : ¬ (2*k^2+1).Prime) :
    ∃ x y : ℕ, 1 < x ∧ x^2 + 2*y^2 = 2*k^2+1 := by
  obtain ⟨a,b,hab,ha,hb⟩ := nontrivial_factors k hk hc
  have realPart : a.re * b.re - 2 * a.im * b.im = 1 := by
    have := congrArg Zsqrtd.re hab
    simpa [z, sub_eq_add_neg, mul_assoc] using this.symm
  have im_ne (c e : R) (hu : ¬ IsUnit c)
      (h : c.re * e.re - 2 * c.im * e.im = 1) : c.im ≠ 0 := by
    intro hzero
    rw [hzero] at h
    simp only [mul_zero, zero_mul, sub_zero] at h
    apply hu
    rw [← Zsqrtd.norm_eq_one_iff' (by decide), norm_coords, hzero]
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h with h | h <;> norm_num [h.1]
  have nz := mul_ne_zero (im_ne a b ha realPart)
    (im_ne b a hb (by nlinarith only [realPart]))
  let w := a * star b
  have re : w.re = 1 + 4 * (a.im * b.im) := by
    change a.re*b.re + (-2)*a.im*(-b.im) = _
    nlinarith only [realPart]
  have big : 1 < w.re.natAbs := by omega
  have eq : w.norm = (z k).norm := by
    rw [hab]
    simp [w, Zsqrtd.norm_mul, Zsqrtd.norm_conj]
  rw [norm_coords, norm_z] at eq
  push_cast at eq
  refine ⟨w.re.natAbs, w.im.natAbs, big, Int.ofNat_inj.mp ?_⟩
  push_cast
  simpa only [Int.natCast_natAbs, sq_abs] using eq

private theorem triangular_of_norm {k x y : ℕ} (hx : 1 < x)
    (eq : x^2 + 2*y^2 = 2*k^2+1) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ d ∣ n*(n+1)/2 ∧ k = d+(n*(n+1)/2)/d := by
  have classify : ∀ i j l : ZMod 4, i^2+2*j^2=2*l^2+1 →
      i.val%2=1 ∧ j.val%2=l.val%2 := by decide
  have hz : (x : ZMod 4)^2 + 2*(y : ZMod 4)^2 = 2*(k : ZMod 4)^2+1 := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ZMod 4)) eq
  have parity := classify x y k hz
  simp only [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)] at parity
  have ylt : y < k := by
    by_contra! h
    have le := Nat.pow_le_pow_left h 2
    nlinarith [Nat.pow_le_pow_left hx 2]
  let n := (x-1)/2
  let d := (k-y)/2
  let e := d+y
  have xn : x = 2*n+1 := by dsimp [n]; omega
  have kd : k = d+e := by dsimp [e,d]; omega
  have hn : 0 < n := by omega
  have hd : 0 < d := by dsimp [d]; omega
  have product : n*(n+1) = 2*(d*e) := by
    rw [xn, kd] at eq
    dsimp [e] at *
    nlinarith only [eq]
  have half : n*(n+1)/2 = d*e := by rw [product]; omega
  refine ⟨n, d, hn, hd, half ▸ dvd_mul_right _ _, ?_⟩
  simpa [half, Nat.mul_div_cancel_left _ hd] using kd

private theorem excludes_prime {k n d : ℕ} (hp : (2*k^2+1).Prime) (hn : 0 < n) (hd : 0 < d)
    (hdiv : d ∣ n*(n+1)/2) (hk : k = d+(n*(n+1)/2)/d) : False := by
  let u := (n*(n+1)/2)/d
  have hu : (n*(n+1)/2) = d*u := (Nat.mul_div_cancel' hdiv).symm
  have tri : n*(n+1) = 2*(d*u) := by rw [← hu, Nat.mul_div_cancel' (n.two_dvd_mul_add_one)]
  change k = d+u at hk
  let A := 2*d^2+n^2
  let B := 2*d^2+(n+1)^2
  have identity : A*B = (2*k^2+1)*(2*d^2) := by
    dsimp [A,B]
    rw [hk]
    zify at tri ⊢
    linear_combination (4*(d:ℤ)^2 + n*(n+1) + 2*d*u) * tri
  have dAB : 2*k^2+1 ∣ A*B := ⟨_, identity⟩
  have lA : A < 2*k^2+1 := by dsimp [A]; rw [hk]; nlinarith
  have lB : B < 2*k^2+1 := by dsimp [B]; rw [hk]; nlinarith [Nat.pow_pos hn (n := 2)]
  rcases hp.dvd_mul.mp dAB with h | h
  · exact (Nat.not_dvd_of_pos_of_lt (by dsimp [A]; positivity) lA) h
  · exact (Nat.not_dvd_of_pos_of_lt (by dsimp [B]; positivity) lB) h

end TriangularDivisors

open TriangularDivisors

theorem OMA.solution : type_of% @OMA.S_oeis_a089001.main := by
  intro k hk
  constructor
  · rintro hp ⟨n,d,hn,hd,hdiv,hk'⟩
    exact excludes_prime hp hn hd hdiv hk'
  · intro h
    by_contra hc
    obtain ⟨x,y,hx,eq⟩ := alternative k hk hc
    exact h (triangular_of_norm hx eq)
