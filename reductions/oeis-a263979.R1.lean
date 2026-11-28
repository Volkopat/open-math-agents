import OMAStatements.S_oeis_a263979

/-!
Jonathan Sondow's quantitative conjecture, https://oeis.org/A263979.

A Gaussian prime in the sector from π/4 to π/3 and the norm interval (4n²,8n²]
has both coordinate magnitudes above n and prime ordinary norm. The classical
fixed-sector prime number theorem supplies this annulus at all sufficiently large
scales, as stated in (1.1) of Huang–Liu–Rudnick, *Gaussian primes in almost all
narrow sectors*, DOI 10.4064/aa190331-23-7. The second subgoal requires an effective
starting point compatible with the first subgoal's checked finite range.
-/

namespace A263979Sector

private theorem unit_axis (u : GaussianIntˣ) :
    (u : GaussianInt).re = 0 ∨ (u : GaussianInt).im = 0 := by
  have hn := (Zsqrtd.norm_eq_one_iff.mpr u.isUnit)
  rw [GaussianInt.natAbs_norm_eq] at hn
  by_contra! hnz
  have hre : 0 < (u : GaussianInt).re.natAbs := Int.natAbs_pos.mpr hnz.1
  have him : 0 < (u : GaussianInt).im.natAbs := Int.natAbs_pos.mpr hnz.2
  nlinarith

private theorem divides_rational_prime (z : GaussianInt) (hz : Prime z)
    (n : ℕ) (hn : n ≠ 0) (hd : z ∣ (n : GaussianInt)) :
    ∃ p : ℕ, p.Prime ∧ z ∣ (p : GaussianInt) := by
  induction n using Nat.recOnMul with
  | zero => exact (hn rfl).elim
  | one => exact (hz.not_isUnit (isUnit_of_dvd_one (by simpa using hd))).elim
  | prime p hp => exact ⟨p,hp,hd⟩
  | mul a b ha hb =>
    rw [Nat.cast_mul] at hd
    rcases hz.dvd_or_dvd hd with h | h
    · exact ha (left_ne_zero_of_mul hn) h
    · exact hb (right_ne_zero_of_mul hn) h

/-- A Gaussian prime off the two axes has rationally prime norm. -/
theorem prime_norm (z : GaussianInt) (hz : Prime z) (hr : z.re ≠ 0) (hi : z.im ≠ 0) :
    Nat.Prime z.norm.natAbs := by
  have hzN : z.norm.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, ne_eq, GaussianInt.norm_eq_zero]
    exact hz.ne_zero
  have hd : z ∣ (z.norm.natAbs : GaussianInt) := by
    have h : (z.norm.natAbs : GaussianInt) = (z.norm : GaussianInt) := by
      calc
        _ = ((z.norm.natAbs : ℤ) : GaussianInt) := by simp only [Int.cast_natCast]
        _ = _ := congrArg (fun i : ℤ => (i : GaussianInt)) (GaussianInt.abs_natCast_norm z)
    rw [h, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right z _
  obtain ⟨p,hp,w,hw⟩ := divides_rational_prime z hz _ hzN hd
  have hwu : ¬IsUnit w := by
    rintro ⟨u,rfl⟩
    have he : (p : GaussianInt) * ↑u⁻¹ = z := by rw [hw]; simp [mul_assoc]
    rcases unit_axis u⁻¹ with hur | hui
    · apply hr
      rw [← he, Zsqrtd.re_mul, Zsqrtd.im_natCast, hur]
      ring
    · apply hi
      rw [← he, Zsqrtd.im_mul, Zsqrtd.im_natCast, hui]
      ring
  have hn : z.norm.natAbs * w.norm.natAbs = p ^ 2 := by
    rw [← Int.natCast_inj, Int.natCast_pow, sq, ← @Zsqrtd.norm_natCast (-1), hw]
    simp
  have h := (hp.mul_eq_prime_sq_iff (mt Zsqrtd.norm_eq_one_iff.mp hz.not_isUnit)
    (mt Zsqrtd.norm_eq_one_iff.mp hwu)).mp hn
  exact h.1 ▸ hp

/-- The annulus (4n²,8n²] in the closed sector [π/4,π/3]. -/
theorem annular_witness (n : ℕ) (z : GaussianInt) (hz : Prime z)
    (hxy : z.re.natAbs ≤ z.im.natAbs)
    (hs : z.im.natAbs ^ 2 ≤ 3*z.re.natAbs ^ 2)
    (hl : 4*n^2 < z.norm.natAbs) (hu : z.norm.natAbs ≤ 8*n^2) :
    ∃ x y : ℕ, n < x ∧ n < y ∧ Nat.Prime (x^2+y^2) ∧ x^2+y^2 ≤ 2*(2*n+1)^2 := by
  have hn : z.norm.natAbs = z.re.natAbs^2 + z.im.natAbs^2 := by
    simpa only [sq] using GaussianInt.natAbs_norm_eq z
  have hx : n < z.re.natAbs := by
    by_contra! h
    have hsquare := Nat.pow_le_pow_left h 2
    nlinarith only [hn,hl,hs,hsquare]
  have hy := lt_of_lt_of_le hx hxy
  have hr : z.re ≠ 0 := Int.natAbs_ne_zero.mp (by omega)
  have hi : z.im ≠ 0 := Int.natAbs_ne_zero.mp (by omega)
  refine ⟨_, _, hx, hy, hn ▸ prime_norm z hz hr hi, ?_⟩
  nlinarith only [hu, hn, Nat.zero_le n]

end A263979Sector

namespace OMA.R_oeis_a263979_R1

/-- The finite range covered by overlapping intervals of explicit prime witnesses. -/
def H1 : Prop :=
  ∀ n : ℕ, n ≤ 1000000000000000000 →
    ∃ x y : ℕ, n < x ∧ n < y ∧ Nat.Prime (x^2+y^2) ∧ x^2+y^2 ≤ 2*(2*n+1)^2

/-- A Gaussian prime in the annular sector at every remaining scale. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000000000000000000 < n →
    ∃ z : GaussianInt, Prime z ∧ z.re.natAbs ≤ z.im.natAbs ∧
      z.im.natAbs^2 ≤ 3*z.re.natAbs^2 ∧ 4*n^2 < z.norm.natAbs ∧ z.norm.natAbs ≤ 8*n^2

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a263979.main := by
  intro finite sector n
  by_cases h : n ≤ 1000000000000000000
  · exact finite n h
  · obtain ⟨z,hp,hxy,hangle,hl,hu⟩ := sector n (Nat.lt_of_not_ge h)
    exact A263979Sector.annular_witness n z hp hxy hangle hl hu

end OMA.R_oeis_a263979_R1
