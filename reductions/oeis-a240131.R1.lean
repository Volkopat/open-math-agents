import OMAStatements.S_oeis_a240131

-- Reduction oeis-a240131.R1
-- Credit: @Pixelstorm44

namespace OMA.R_oeis_a240131_R1

/-- The real coordinate of a Gaussian integer divides the real coordinate of every odd power. -/
theorem dvd_odd_real (z : GaussianInt) (t : ℕ) : z.re ∣ (z ^ (2*t+1)).re := by
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    rw [show 2*(t+1)+1 = (2*t+1)+2 by omega, pow_add, sq]
    refine ⟨c * (z.re^2-z.im^2) - 2*(z^(2*t+1)).im*z.im, ?_⟩
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, hc]
    ring

/-- At an odd prime exponent r, all nonconstant real terms in the binomial expansion
of (1+bi)^r are multiples of r b². The last term is purely imaginary. -/
theorem exceptional_divisor (b t : ℕ) (hr : (2*t+1).Prime) :
    ((2*t+1 : ℕ) : ℤ) * (b : ℤ)^2 ∣ ((⟨1, b⟩ : GaussianInt)^(2*t+1)).re - 1 := by
  let r := 2*t+1
  let u : GaussianInt := ⟨0, b⟩
  let realPart : GaussianInt →+ ℤ :=
    { toFun := fun z => z.re, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change (r : ℤ) * (b : ℤ)^2 ∣ realPart ((u + 1)^r) - 1
  rw [add_pow, map_sum, Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    show realPart 1 = 1 by rfl, add_sub_cancel_right]
  apply Finset.dvd_sum
  intro i hi
  have hir : i < r := Finset.mem_range.mp hi
  change (r : ℤ) * (b : ℤ)^2 ∣ ((u^(i+1) * ↑(r.choose (i+1))).re)
  simp only [Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast, mul_zero, add_zero]
  by_cases top : i+1 = r
  · have hz := dvd_odd_real u t
    change (0 : ℤ) ∣ (u^r).re at hz
    rw [top, zero_dvd_iff.mp hz, zero_mul]
    exact dvd_zero _
  cases i with
  | zero => simp [u]
  | succ j =>
    obtain ⟨c, hc⟩ := hr.dvd_choose_self (k := j+1+1) (by omega) (by omega : j+1+1 < r)
    change r.choose (j+1+1) = r*c at hc
    rw [hc, show j+1+1 = j+2 by omega, pow_add]
    refine ⟨-(u^j).re * c, ?_⟩
    simp [sq, u, Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring

/-- Relax a prime point on each line to a first or odd-prime power of a Gaussian
integer of prime norm, up to reflection in the imaginary axis. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a b t : ℕ, 0 < b ∧ (a^2+b^2).Prime ∧
    (t = 0 ∨ (2*t+1).Prime) ∧ ((⟨a,b⟩ : GaussianInt)^(2*t+1)).re.natAbs = p

/-- For the exceptional lines generated from 1+bi, find a power with prime base
norm above p+2. Both original search parameters satisfy r b² ≤ p+1. -/
def H2 : Prop :=
  ∀ b t : ℕ, 0 < b → (1+b^2).Prime → (2*t+1).Prime →
    let p := ((⟨1,b⟩ : GaussianInt)^(2*t+1)).re.natAbs
    p.Prime → (2*t+1)*b^2 ≤ p+1 →
      ∃ a k s : ℕ, 0 < k ∧ (a^2+k^2).Prime ∧ p+2 < a^2+k^2 ∧
        (s = 0 ∨ (2*s+1).Prime) ∧ ((⟨a,k⟩ : GaussianInt)^(2*s+1)).re.natAbs = p

theorem exceptional_bound (b t p : ℕ) (hp : p.Prime) (hr : (2*t+1).Prime)
    (he : ((⟨1,b⟩ : GaussianInt)^(2*t+1)).re.natAbs = p) : (2*t+1)*b^2 ≤ p+1 := by
  let x := ((⟨1,b⟩ : GaussianInt)^(2*t+1)).re
  have hx : x.natAbs = p := he
  have hd := Int.natAbs_dvd_natAbs.mpr (exceptional_divisor b t hr)
  have hn : 0 < (x-1).natAbs := by
    have hne : x ≠ 1 := by
      intro h
      simp [h] at hx
      have := hp.two_le
      omega
    exact Nat.pos_of_ne_zero fun h => hne (sub_eq_zero.mp (Int.natAbs_eq_zero.mp h))
  have h := Nat.le_of_dvd hn hd
  calc
    (2*t+1)*b^2 = ((((2*t+1 : ℕ) : ℤ) * (b : ℤ)^2).natAbs) := by
      rw [Int.natAbs_mul, Int.natAbs_pow]
      rfl
    _ ≤ (x-1).natAbs := h
    _ ≤ p+1 := by simpa [hx] using Int.natAbs_sub_le x 1

theorem extract_or_exception (p a b t : ℕ) (hp : p.Prime)
    (ht : t = 0 ∨ (2*t+1).Prime)
    (he : ((⟨a,b⟩ : GaussianInt)^(2*t+1)).re.natAbs = p) :
    a = p ∨ (a = 1 ∧ (2*t+1).Prime ∧ (2*t+1)*b^2 ≤ p+1) := by
  have hd := Int.natAbs_dvd_natAbs.mpr (dvd_odd_real (⟨a,b⟩ : GaussianInt) t)
  rw [he] at hd
  change (a : ℤ).natAbs ∣ p at hd
  rcases (Nat.dvd_prime hp).mp (by simpa using hd) with ha | ha
  · subst a
    rcases ht with rfl | hr
    · simp at he
      have := hp.two_le
      omega
    · exact Or.inr ⟨rfl, hr, exceptional_bound b t p hp hr he⟩
  · exact Or.inl ha

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a240131.main := by
  intro line exceptional p hp
  obtain ⟨a,b,t,hb,hq,ht,he⟩ := line p hp
  rcases extract_or_exception p a b t hp ht he with rfl | ⟨rfl,hr,hbound⟩
  · exact ⟨b,hb,hq⟩
  · have h := exceptional b t hb (by simpa using hq) hr
    dsimp only at h
    simp only [Nat.cast_one] at he
    rw [he] at h
    obtain ⟨a,k,s,hk,hq',hlarge,hs,he'⟩ := h hp hbound
    rcases extract_or_exception p a k s hp hs he' with rfl | ⟨rfl,_,hsmall⟩
    · exact ⟨k,hk,hq'⟩
    · have hkbound : k^2 ≤ (2*s+1)*k^2 := Nat.le_mul_of_pos_left _ (by omega)
      simp only [one_pow] at hlarge
      omega

/-- A prime point itself supplies an exponent-one witness to both steps. -/
theorem necessary (sol : type_of% @OMA.S_oeis_a240131.main) : H1 ∧ H2 := by
  constructor
  · intro p hp
    obtain ⟨k,hk,hq⟩ := sol p hp
    exact ⟨p,k,0,hk,hq,Or.inl rfl,by simp⟩
  · intro b t _ _ _ p hp _
    obtain ⟨k,hk,hq⟩ := sol p hp
    refine ⟨p,k,0,hk,hq,?_,Or.inl rfl,by simp⟩
    nlinarith [hp.two_le, Nat.mul_self_le_mul_self (show 1 ≤ k by omega)]

end OMA.R_oeis_a240131_R1
