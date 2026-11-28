import OMAStatements.S_oeis_a361711
import Mathlib

/-!
Proof of Peter Bala's A361711 supercongruence, https://oeis.org/A361711.

The signed factorial expression for odd terms follows from the alternating
binomial moment and its telescoping recurrence. Splitting the two factorials
into multiples of p and units gives paired factors (a^2 - p^(2*k)).
The inverse-square sum over one representative of each pair of opposite
units vanishes modulo p^k, which gives the congruence modulo p^(3*k).
-/

open Finset

namespace A361711ClosedForm

def signedCube (n j : ℕ) : ℤ := (-1) ^ j * (n.choose j : ℤ) ^ 3

def moment (n : ℕ) : ℤ :=
  ∑ j ∈ range (n + 1), ((n : ℤ) - 2 * j) * signedCube n j

private def certificate (n j : ℤ) : ℤ :=
  -2 * (n + 1)^2 * (n + 2) * (14*n^3 + 82*n^2 + 157*n + 99)
  + j * ((n + 1) * (134*n^4 + 941*n^3 + 2454*n^2 + 2816*n + 1199)
    + j * (-3*(n+2)*(3*n+5)*(27*n^2+73*n+48)
      + j * ((3*n+5)*(73*n^2+227*n+172)
        + j * (-3*(3*n+5)*(11*n+17) + j * (6*(3*n+5))))))

private lemma certificate_identity (n j : ℤ) :
    -(n + 2 - j)^3 * certificate n (j + 1) - j^3 * certificate n j =
      (n + 1)^5 * (n + 2)^3 * (n + 2 - 2*j) +
      3 * (3*n + 1) * (3*n + 5) * ((n + 2 - j)*(n + 1 - j))^3 * (n - 2*j) := by
  unfold certificate
  ring

private lemma choose_shift (n j : ℕ) (hj : j ≤ n + 2) :
    ((n + 2).choose j : ℤ) * (((n : ℤ) + 2 - j) * ((n : ℤ) + 1 - j)) =
      (n.choose j : ℤ) * (((n : ℤ) + 2) * ((n : ℤ) + 1)) := by
  by_cases h : j ≤ n + 1
  · have h1 := congrArg (fun x : ℕ => (x : ℤ)) (Nat.choose_mul_succ_eq n j)
    have h2 := congrArg (fun x : ℕ => (x : ℤ)) (Nat.choose_mul_succ_eq (n + 1) j)
    push_cast [Nat.cast_sub h, Nat.cast_sub hj] at h1 h2
    linear_combination -((n : ℤ) + 2) * h1 - ((n : ℤ) + 1 - j) * h2
  · have he : j = n + 2 := by omega
    subst j
    simp [Nat.choose_eq_zero_of_lt (by omega : n < n + 2)]

private lemma cube_shift (n j : ℕ) (hj : j ≤ n + 2) :
    (((n : ℤ) + 2 - j) * ((n : ℤ) + 1 - j)) ^ 3 * signedCube (n + 2) j =
      (((n : ℤ) + 2) * ((n : ℤ) + 1)) ^ 3 * signedCube n j := by
  have hh := congrArg (fun x : ℤ => x ^ 3) (choose_shift n j hj)
  simp only [signedCube]
  linear_combination ((-1 : ℤ) ^ j) * hh

private lemma cube_succ (n j : ℕ) (hj : j ≤ n) :
    ((j : ℤ) + 1)^3 * signedCube n (j + 1) =
      -((n : ℤ) - j)^3 * signedCube n j := by
  have hh := congrArg (fun x : ℕ => (x : ℤ)) (Nat.choose_succ_right_eq n j)
  push_cast [Nat.cast_sub hj] at hh
  have hh3 := congrArg (fun x : ℤ => x ^ 3) hh
  simp only [signedCube, pow_succ (-1 : ℤ) j]
  linear_combination -((-1 : ℤ) ^ j) * hh3

private lemma moment_extend (n : ℕ) :
    (∑ j ∈ range (n + 3), ((n : ℤ) - 2*j) * signedCube n j) = moment n := by
  have h1 : n.choose (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h2 : n.choose (n + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp only [show n + 3 = (n + 2) + 1 by omega, sum_range_succ, signedCube,
    h1, h2, Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), mul_zero, add_zero, moment]

lemma moment_step (n : ℕ) :
    ((n : ℤ) + 1)^2 * moment (n + 2) =
      -3 * (3*(n : ℤ) + 1) * (3*(n : ℤ) + 5) * moment n := by
  let g : ℕ → ℤ := fun j => (j : ℤ)^3 * certificate n j * signedCube (n + 2) j
  let c : ℤ := 3 * (3*(n : ℤ) + 1) * (3*(n : ℤ) + 5)
  let d : ℤ := (((n : ℤ) + 2) * ((n : ℤ) + 1))^3
  have hg (j : ℕ) (hj : j ∈ range (n + 3)) :
      g (j + 1) - g j =
        d * (((n : ℤ) + 1)^2 * (((n + 2 : ℕ) : ℤ) - 2*j) * signedCube (n + 2) j +
          c * (((n : ℤ) - 2*j) * signedCube n j)) := by
    have hj' : j ≤ n + 2 := by simp only [mem_range] at hj; omega
    have hcert := certificate_identity n j
    have hwidth := cube_shift n j hj'
    have hstep := cube_succ (n + 2) j hj'
    push_cast at hstep
    dsimp [g, d, c]
    linear_combination certificate n ((j : ℤ) + 1) * hstep +
      signedCube (n + 2) j * hcert +
      (3 * (3*(n : ℤ) + 1) * (3*(n : ℤ) + 5) * ((n : ℤ) - 2*j)) * hwidth
  have h0 : g 0 = 0 := by simp [g]
  have hend : g (n + 3) = 0 := by
    simp [g, signedCube]
  have ht (m : ℕ) : (∑ j ∈ range m, (g (j + 1) - g j)) = g m - g 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, ih]; ring
  have hsum := (sum_congr rfl hg).symm
  rw [ht, hend, h0, sub_zero, ← mul_sum, sum_add_distrib] at hsum
  simp only [mul_assoc] at hsum
  rw [← mul_sum, ← mul_sum, moment_extend] at hsum
  have hd : d ≠ 0 := by dsimp [d]; positivity
  have hz := (mul_eq_zero.mp hsum).resolve_left hd
  change ((n : ℤ) + 1)^2 * moment (n + 2) + c * moment n = 0 at hz
  dsimp [c] at hz
  linarith

private lemma neg_reflection (n j : ℕ) (hj : j ≤ n) (hn : Odd n) :
    signedCube n (n-j) = -signedCube n j := by
  rw [signedCube, signedCube, Nat.choose_symm hj]
  have hsign : (-1 : ℤ) ^ (n-j) * (-1)^j = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hj]
    exact (neg_one_pow_eq_neg_one_iff_odd (by decide)).mpr hn
  obtain hp | hp := neg_one_pow_eq_or ℤ j
  · rw [hp, mul_one] at hsign
    rw [hsign, hp]
    ring
  · rw [hp] at hsign ⊢
    have hsign' : (-1 : ℤ) ^ (n-j) = 1 := by linarith
    rw [hsign']
    ring

abbrev a := OMA.S_oeis_a361711.a

private lemma moment_eq_a (n : ℕ) (hn : Odd n) :
    moment n = 2 * (n : ℤ) * a n := by
  by_cases h1 : n = 1
  · subst n
    norm_num [moment, a, OMA.S_oeis_a361711.a, signedCube, sum_range_succ]
  have h2 : 2 ≤ n := by obtain ⟨j, hj⟩ := hn; omega
  let w : ℕ → ℤ := fun j => (((n : ℤ) - j)*((n : ℤ) - 1 - j))*signedCube n j
  have hw :
      (∑ j ∈ range (n + 1), w j) = (n : ℤ) * ((n : ℤ) - 1) * a n := by
    rw [a, OMA.S_oeis_a361711.a, if_neg h1, mul_sum]
    trans ∑ j ∈ range (n + 1),
      (n : ℤ) * ((n : ℤ) - 1) * ((-1 : ℤ)^j * (n.choose j : ℤ)^2 * ((n-2).choose j : ℤ))
    · apply sum_congr rfl
      intro j hj
      have hj' : j ≤ n := by simpa using hj
      have he : n - 2 + 2 = n := Nat.sub_add_cancel h2
      have hchoose := choose_shift (n - 2) j (by simpa only [he] using hj')
      rw [he] at hchoose
      push_cast [Nat.cast_sub h2] at hchoose
      dsimp [w, signedCube]
      linear_combination ((-1 : ℤ)^j * (n.choose j : ℤ)^2) * hchoose
    · symm
      refine sum_subset (range_mono (by omega)) fun j hj hj' => ?_
      have hj'' : n - 2 < j := by simp only [mem_range, not_lt] at hj'; omega
      simp [Nat.choose_eq_zero_of_lt hj'']
  have href (j : ℕ) (hj : j ∈ range (n + 1)) :
      w j + w (n - j) = ((n : ℤ) - 1) * (((n : ℤ) - 2*j)*signedCube n j) := by
    have hj' : j ≤ n := by simpa using hj
    dsimp [w]
    rw [neg_reflection n j hj' hn]
    push_cast [Nat.cast_sub hj']
    ring
  have hs := sum_congr rfl href
  rw [sum_add_distrib, ← mul_sum] at hs
  have hr := sum_range_reflect w (n+1)
  simp only [Nat.add_sub_cancel] at hr
  rw [hr, hw] at hs
  change (n : ℤ) * ((n : ℤ) - 1) * a n + (n : ℤ) * ((n : ℤ) - 1) * a n =
    ((n : ℤ) - 1) * moment n at hs
  have hd : (n : ℤ) - 1 ≠ 0 := by omega
  apply mul_left_cancel₀ hd
  linear_combination -hs

private lemma moment_factorial (m : ℕ) :
    (m.factorial : ℤ)^3 * moment (2*m+1) = 2 * (-1)^m * ((3*m+1).factorial : ℤ) := by
  induction m with
  | zero => norm_num [moment, signedCube, sum_range_succ]
  | succ m ih =>
    have hs := moment_step (2*m+1)
    push_cast at hs
    have hstep : ((m : ℤ)+1)^2 * moment (2*(m+1)+1) =
        -3 * (3*(m : ℤ)+2) * (3*(m : ℤ)+4) * moment (2*m+1) := by
      rw [show 2*(m+1)+1 = (2*m+1)+2 by omega]
      nlinarith only [hs]
    rw [Nat.factorial_succ m, show 3*(m+1)+1 = (3*m+1)+1+1+1 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, pow_succ (-1 : ℤ) m]
    push_cast
    linear_combination (((m : ℤ)+1) * (m.factorial : ℤ)^3) * hstep -
      (3 * ((m : ℤ)+1) * (3*(m : ℤ)+2) * (3*(m : ℤ)+4)) * ih

/-- The signed factorial expression for the odd terms, with denominators cleared. -/
theorem odd_factorial (m : ℕ) :
    (2*(m : ℤ)+1) * (m.factorial : ℤ)^3 * a (2*m+1) =
      (-1)^m * ((3*m+1).factorial : ℤ) := by
  have h := moment_factorial m
  rw [moment_eq_a _ (by exact ⟨m, by omega⟩)] at h
  push_cast at h
  nlinarith only [h]

end A361711ClosedForm

open Finset

namespace A361711UnitProduct

def unitRange (p n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun a => ¬ p ∣ a)

def unitProduct (p n : ℕ) : ℕ := ∏ a ∈ unitRange p n, a

private lemma multiple_range (p n : ℕ) (hp : 0 < p) :
    (Icc 1 n).filter (fun a => p ∣ a) = (Icc 1 (n/p)).image (p * ·) := by
  ext a
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨hpos, hle⟩, b, rfl⟩
    refine ⟨b, ⟨?_, (Nat.le_div_iff_mul_le hp).2 (by simpa [mul_comm] using hle)⟩, rfl⟩
    by_contra! hb
    have : b = 0 := by omega
    simp [this] at hpos
  · rintro ⟨b, ⟨hb, hle⟩, rfl⟩
    exact ⟨⟨Nat.mul_pos hp hb, by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hp).1 hle⟩, dvd_mul_right _ _⟩

lemma factorial_split (p n : ℕ) (hp : 0 < p) :
    n.factorial = p^(n/p) * (n/p).factorial * unitProduct p n := by
  have hmul : (∏ i ∈ (Icc 1 n).filter (fun a => p ∣ a), i) =
      p^(n/p) * (n/p).factorial := by
    rw [multiple_range p n hp, prod_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp h)]
    rw [prod_mul_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel]
    rw [← Ico_add_one_right_eq_Icc, prod_Ico_id_eq_factorial]
  rw [← prod_Ico_id_eq_factorial n, Ico_add_one_right_eq_Icc, ← hmul]
  exact (prod_filter_mul_prod_filter_not (Icc 1 n) (fun a => p ∣ a) id).symm

private lemma units_card (p m : ℕ) (hp : 0 < p) :
    (unitRange p m).card = m - m/p := by
  have h := card_filter_add_card_filter_not (s := Icc 1 m) (fun a => p ∣ a)
  rw [multiple_range p m hp,
    card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h),
    Nat.card_Icc, Nat.card_Icc] at h
  unfold unitRange
  simp only [Nat.add_sub_cancel] at h
  omega

private lemma dvd_sub_from_multiple {p t a : ℕ} (ht : p ∣ t) (ha : a ≤ t) :
    p ∣ t - a ↔ p ∣ a := by
  constructor
  · intro h
    have := Nat.dvd_sub ht h
    simpa only [Nat.sub_sub_self ha] using this
  · exact Nat.dvd_sub ht

private lemma upper_range (p m t : ℕ) (ht : t = 2*m+1) (hpt : p ∣ t) :
    (Ioc m (t+m)).filter (fun a => ¬ p ∣ a) =
      (unitRange p m).image (t - ·) ∪ (unitRange p m).image (t + ·) := by
  ext x
  simp only [mem_filter, mem_Ioc, mem_union, mem_image, unitRange, mem_Icc]
  constructor
  · rintro ⟨⟨hx, hxm⟩, hxp⟩
    by_cases hxt : x < t
    · refine Or.inl ⟨t - x, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      simpa only [dvd_sub_from_multiple hpt hxt.le] using hxp
    · have htne : x ≠ t := fun he => hxp (he ▸ hpt)
      have htx : t < x := by omega
      refine Or.inr ⟨x - t, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      intro hd
      have hsum : t + (x-t) = x := by omega
      exact hxp (hsum ▸ Nat.dvd_add hpt hd)
  · rintro (⟨a, ⟨⟨ha, ham⟩, hap⟩, rfl⟩ | ⟨a, ⟨⟨ha, ham⟩, hap⟩, rfl⟩)
    · exact ⟨⟨by omega, by omega⟩, (dvd_sub_from_multiple hpt (by omega)).not.mpr hap⟩
    · exact ⟨⟨by omega, by omega⟩, (Nat.dvd_add_right hpt).not.mpr hap⟩

lemma paired_differences (p m t : ℕ) (ht : t = 2*m+1) (hpt : p ∣ t)
    (hp : 0 < p) :
    (-1 : ℤ)^(m-m/p) * (unitProduct p (t+m) : ℤ) =
      (unitProduct p m : ℤ) * ∏ a ∈ unitRange p m, ((a : ℤ)^2 - (t : ℤ)^2) := by
  let s := unitRange p m
  have hsplit : unitRange p (t+m) = s ∪ (Ioc m (t+m)).filter (fun a => ¬ p ∣ a) := by
    ext a
    simp only [s, unitRange, mem_filter, mem_Icc, mem_Ioc, mem_union]
    omega
  have hd1 : Disjoint s ((Ioc m (t+m)).filter (fun a => ¬ p ∣ a)) := by
    refine disjoint_left.mpr fun a ha hb => ?_
    simp only [s, unitRange, mem_filter, mem_Icc, mem_Ioc] at ha hb
    omega
  have hd2 : Disjoint (s.image (t - ·)) (s.image (t + ·)) := by
    refine disjoint_left.mpr fun a ha hb => ?_
    simp only [mem_image, s, unitRange, mem_filter, mem_Icc] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, he⟩ := hb
    omega
  have hsub (x : ℕ) (hx : x ∈ s) : x ≤ t := by
    simp only [s, unitRange, mem_filter, mem_Icc] at hx
    omega
  have hinj : ∀ x ∈ s, ∀ y ∈ s, t-x = t-y → x=y := by
    intro x hx y hy he
    have := hsub x hx
    have := hsub y hy
    omega
  unfold unitProduct
  rw [hsplit, prod_union hd1, upper_range p m t ht hpt,
    prod_union hd2, prod_image hinj, prod_image (fun x _ y _ h => Nat.add_left_cancel h)]
  push_cast
  rw [← units_card p m hp]
  change (-1 : ℤ)^s.card *
    ((∏ a ∈ s, (a : ℤ)) * ((∏ a ∈ s, ((t-a : ℕ) : ℤ)) * (∏ a ∈ s, ((t : ℤ) + a)))) = _
  rw [← prod_const (s := s), mul_left_comm, ← prod_mul_distrib, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun a ha => ?_
  rw [Nat.cast_sub (hsub a ha)]
  ring

private lemma product_one_sub_sq_zero {R ι : Type*} [CommRing R] (s : Finset ι)
    (x : R) (f : ι → R) (hx : x ^ 2 = 0) :
    (∏ i ∈ s, (1 - x * f i)) = 1 - x * ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    calc
      (1 - x * f a) * (1 - x * ∑ i ∈ s, f i) =
          1 - x * (f a + ∑ i ∈ s, f i) + x ^ 2 * (f a * ∑ i ∈ s, f i) := by ring
      _ = 1 - x * (f a + ∑ i ∈ s, f i) := by rw [hx]; simp

private lemma sum_units_sq_eq_zero_of_unit_sub_one {R : Type*} [CommRing R]
    [Fintype Rˣ] (v : Rˣ) (hv : IsUnit ((v : R)^2 - 1)) :
    (∑ u : Rˣ, (u : R)^2) = 0 := by
  classical
  have h := Equiv.sum_comp (Equiv.mulLeft v) (fun u : Rˣ => (u : R)^2)
  change (∑ u : Rˣ, ((v * u : Rˣ) : R)^2) = _ at h
  simp only [Units.val_mul, mul_pow, ← Finset.mul_sum] at h
  apply hv.mul_right_eq_zero.mp
  calc
    ((v : R)^2 - 1) * (∑ u : Rˣ, (u : R)^2) =
      (v : R)^2 * (∑ u : Rˣ, (u : R)^2) - (∑ u : Rˣ, (u : R)^2) := by ring
    _ = 0 := sub_eq_zero.mpr h

private lemma sum_units_inv_sq_eq_zero {R : Type*} [CommRing R]
    [Fintype Rˣ] (v : Rˣ) (hv : IsUnit ((v : R)^2 - 1)) :
    (∑ u : Rˣ, ((u⁻¹ : Rˣ) : R)^2) = 0 := by
  have h := Equiv.sum_comp (Equiv.inv Rˣ) (fun u : Rˣ => (u : R)^2)
  change (∑ u : Rˣ, ((u⁻¹ : Rˣ) : R)^2) = _ at h
  rw [h]
  exact sum_units_sq_eq_zero_of_unit_sub_one v hv

private lemma sum_half_units_inv_sq_eq_zero {R : Type*} [CommRing R] [Fintype Rˣ] [DecidableEq Rˣ]
    (v : Rˣ) (hv : IsUnit ((v : R)^2 - 1)) (h2 : IsUnit (2 : R))
    (s : Finset Rˣ) (hd : Disjoint s (s.image fun u => -u))
    (hu : s ∪ (s.image fun u => -u) = Finset.univ) :
    (∑ u ∈ s, ((u⁻¹ : Rˣ) : R)^2) = 0 := by
  classical
  have hi : Function.Injective (fun u : Rˣ => -u) := neg_injective
  have hs : (∑ u ∈ s.image (fun u : Rˣ => -u), ((u⁻¹ : Rˣ) : R)^2) =
      ∑ u ∈ s, ((u⁻¹ : Rˣ) : R)^2 := by
    rw [Finset.sum_image (fun x hx y hy he => hi he)]
    simp
  have hz := sum_units_inv_sq_eq_zero v hv
  rw [← hu, Finset.sum_union hd, hs] at hz
  apply h2.mul_right_eq_zero.mp
  linear_combination hz

private lemma half_inverse_sum (p k m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 0 < k) (ht : p^k = 2*m+1) :
    (∑ a ∈ unitRange p m, (((a : ZMod (p^k))⁻¹)^2)) = 0 := by
  classical
  let t := p^k
  have ht1 : 1 < t := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    dsimp [t]
    rw [pow_succ]
    have := pow_pos hp.pos j
    nlinarith
  let _ : NeZero t := ⟨by omega⟩
  let R := ZMod t
  have hunit (a : ℕ) : IsUnit (a : R) ↔ ¬ p ∣ a :=
    ZMod.isUnit_natCast_iff_not_dvd_pow hp hk
  have htwo : IsUnit (2 : R) := (hunit 2).2 (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have hthree : IsUnit (3 : R) := (hunit 3).2 (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  let v := htwo.unit
  have hv : IsUnit ((v : R)^2 - 1) := by
    rw [show (v : R) = 2 from htwo.unit_spec]
    convert hthree using 1
    norm_num
  let s : Finset Rˣ := univ.filter (fun u => (u : R).val ≤ m)
  have hu_ne (u : Rˣ) : (u : R) ≠ 0 := by
    intro he
    have hu := u.val_inv
    change (u : R) * ((u⁻¹ : Rˣ) : R) = 1 at hu
    rw [he, zero_mul] at hu
    exact ht1.ne' ((ZMod.one_eq_zero_iff).mp hu.symm)
  have hneg (u : Rˣ) : ((-u : Rˣ) : R).val = t - (u : R).val := by
    let _ : NeZero (u : R) := ⟨hu_ne u⟩
    change (-(u : R)).val = _
    exact ZMod.val_neg_of_ne_zero _
  have hd : Disjoint s (s.image fun u => -u) := by
    refine disjoint_left.mpr fun u hu hw => ?_
    simp only [s, mem_filter, mem_univ, true_and, mem_image] at hu hw
    obtain ⟨w, hw, rfl⟩ := hw
    rw [hneg] at hu
    change t = 2*m+1 at ht
    omega
  have hcover : s ∪ (s.image fun u => -u) = univ := by
    ext u
    simp only [s, mem_union, mem_image, mem_filter, mem_univ, true_and, iff_true]
    by_cases h : (u : R).val ≤ m
    · exact Or.inl h
    · refine Or.inr ⟨-u, ?_, neg_neg u⟩
      rw [hneg]
      change t = 2*m+1 at ht
      omega
  have hinj : Function.Injective (fun u : Rˣ => (u : R).val) := by
    intro u w h
    apply Units.ext
    change (u : R).val = (w : R).val at h
    calc
      (u : R) = ((u : R).val : ℕ) := (ZMod.natCast_zmod_val _).symm
      _ = (w : R) := by rw [h, ZMod.natCast_zmod_val]
  have hs : s.image (fun u : Rˣ => (u : R).val) = unitRange p m := by
    ext a
    simp only [s, unitRange, mem_filter, mem_univ, true_and, mem_image, mem_Icc]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨ZMod.val_pos.mpr (hu_ne u), hu⟩, (hunit _).mp ?_⟩
      rw [ZMod.natCast_zmod_val]
      exact u.isUnit
    · rintro ⟨⟨ha, ham⟩, hap⟩
      let u := ((hunit a).mpr hap).unit
      have hc : (u : R) = a := ((hunit a).mpr hap).unit_spec
      have hlt : a < t := by change t = 2*m+1 at ht; omega
      have hv' : (u : R).val = a := by rw [hc, ZMod.val_natCast_of_lt hlt]
      exact ⟨u, hv'.trans_le ham, hv'⟩
  have hz := sum_half_units_inv_sq_eq_zero v hv htwo s hd hcover
  change (∑ a ∈ unitRange p m, (((a : R)⁻¹)^2)) = 0
  rw [← hs, sum_image (fun a _ b _ h => hinj h), ← hz]
  refine sum_congr rfl fun u hu => ?_
  rw [ZMod.natCast_zmod_val, ZMod.inv_eq_of_mul_eq_one t (u : R) ((u⁻¹ : Rˣ) : R) u.val_inv]

private lemma kernel_mul_square (t : ℕ) [NeZero (t^3)] (hdiv : t ∣ t^3)
    (x : ZMod (t^3)) (hx : ZMod.castHom hdiv (ZMod t) x = 0) :
    (t : ZMod (t^3))^2 * x = 0 := by
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [map_natCast, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨c, hc⟩ := hx
  rw [hc, Nat.cast_mul]
  calc
    (t : ZMod (t^3))^2 * ((t : ZMod (t^3)) * c) = (t : ZMod (t^3))^3 * c := by ring
    _ = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]

lemma paired_product_mod (p k m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k)
    (ht : p^k = 2*m+1) :
    (∏ a ∈ unitRange p m, ((a : ZMod ((p^k)^3))^2 - ((p^k : ℕ) : ZMod ((p^k)^3))^2)) =
      ∏ a ∈ unitRange p m, (a : ZMod ((p^k)^3))^2 := by
  let t := p^k
  have ht0 : 0 < t := pow_pos hp.pos k
  let _ : NeZero (t^3) := ⟨pow_ne_zero _ ht0.ne'⟩
  let _ : NeZero t := ⟨ht0.ne'⟩
  let R := ZMod (t^3)
  let hdiv : t ∣ t^3 := dvd_pow_self _ (by decide)
  let red := ZMod.castHom hdiv (ZMod t)
  let f (a : ℕ) : R := ((((a : ZMod t)⁻¹).val : ℕ) : R)^2
  have hf (a : ℕ) : red (f a) = ((a : ZMod t)⁻¹)^2 := by
    change red ((((a : ZMod t)⁻¹).val : R)^2) = _
    rw [map_pow, map_natCast, ZMod.natCast_zmod_val]
  have hcube : (t : R)^3 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hzero : ((t : R)^2)^2 = 0 := by
    calc
      ((t : R)^2)^2 = (t : R)^3 * t := by ring
      _ = 0 := by rw [hcube, zero_mul]
  have hsum : (t : R)^2 * (∑ a ∈ unitRange p m, f a) = 0 := by
    apply kernel_mul_square t hdiv
    change red (∑ a ∈ unitRange p m, f a) = 0
    rw [map_sum]
    simp_rw [hf]
    exact half_inverse_sum p k m hp hp5 hk ht
  change (∏ a ∈ unitRange p m, ((a : R)^2 - (t : R)^2)) = _
  calc
    (∏ a ∈ unitRange p m, ((a : R)^2 - (t : R)^2)) =
        ∏ a ∈ unitRange p m, ((a : R)^2 * (1 - (t : R)^2 * f a)) := by
      refine prod_congr rfl fun a ha => ?_
      have hap : ¬ p ∣ a := (mem_filter.mp ha).2
      have hu : IsUnit (a : ZMod t) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).2 hap
      have hz : red ((a : R)^2 * f a - 1) = 0 := by
        rw [map_sub, map_mul, map_pow, map_natCast, hf, map_one, ← mul_pow,
          ZMod.mul_inv_of_unit _ hu]
        simp
      have h := kernel_mul_square t hdiv _ hz
      linear_combination h
    _ = ∏ a ∈ unitRange p m, (a : R)^2 := by
      rw [prod_mul_distrib, product_one_sub_sq_zero _ _ _ hzero, hsum, sub_zero, mul_one]

end A361711UnitProduct

open A361711ClosedForm A361711UnitProduct Finset

namespace A361711Finish

lemma congruence (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    a (p^k) ≡ a (p^(k-1)) [ZMOD (p : ℤ)^(3*k)] := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp only [Nat.succ_sub_one]
  let t₀ := p^e
  let t := p^(e+1)
  have hts : t = p*t₀ := by dsimp [t, t₀]; rw [pow_succ, mul_comm]
  have ht₀pos : 0 < t₀ := pow_pos hp.pos e
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨m₀, hodd₀⟩ : Odd t₀ := hpo.pow
  obtain ⟨h, hodd⟩ := hpo
  let m := p*m₀+h
  have ht₀ : t₀ = 2*m₀+1 := by omega
  have ht : t = 2*m+1 := by
    rw [hts, ht₀]
    dsimp [m]
    have hh : p = 2*h+1 := by omega
    linear_combination hh
  have hhp : h < p := by omega
  have hdiv (q : ℕ) : (p*q + h)/p = q := by
    rw [add_comm (p*q), Nat.add_mul_div_left h q hp.pos, Nat.div_eq_of_lt hhp, zero_add]
  have hmdiv : m/p = m₀ := hdiv m₀
  have htmdiv : (t+m)/p = t₀ + m₀ := by
    rw [show t+m = p*(t₀+m₀)+h by rw [hts]; dsimp [m]; ring]
    exact hdiv _
  have hmle : m₀ ≤ m := hmdiv ▸ Nat.div_le_self m p
  have hfac := factorial_split p m hp.pos
  have hfacbig := factorial_split p (t+m) hp.pos
  rw [hmdiv] at hfac
  rw [htmdiv] at hfacbig
  have h1 := odd_factorial m
  rw [← ht, show 3*m+1 = t+m by omega, hfac, hfacbig] at h1
  have ht_int : (2*(m : ℤ)+1) = (t : ℤ) := by exact_mod_cast ht.symm
  rw [ht_int] at h1
  push_cast at h1
  have h0 := odd_factorial m₀
  rw [← ht₀, show 3*m₀+1 = t₀+m₀ by omega] at h0
  have ht₀_int : (2*(m₀ : ℤ)+1) = (t₀ : ℤ) := by exact_mod_cast ht₀.symm
  rw [ht₀_int] at h0
  have hpow : (p : ℤ)^(t₀+m₀) = ((p : ℤ)^m₀)^3 * (p : ℤ) := by
    rw [show t₀+m₀ = m₀*3+1 by omega, pow_add, pow_mul, pow_one]
  have hsign : (-1 : ℤ)^m = (-1 : ℤ)^(m-m₀) * (-1 : ℤ)^m₀ := by
    rw [← pow_add, Nat.sub_add_cancel hmle]
  have ht_cast : (t : ℤ) = (p : ℤ) * t₀ := by exact_mod_cast hts
  rw [hpow, hsign, ht_cast] at h1
  have hcancel : ((p : ℤ)^m₀)^3 * (p : ℤ) * t₀ * (m₀.factorial : ℤ)^3 ≠ 0 := by
    have := hp.pos
    have := Nat.factorial_pos m₀
    positivity
  have hunit_eq :
      (unitProduct p m : ℤ)^3 * a t =
        (-1 : ℤ)^(m-m₀) * (unitProduct p (t+m) : ℤ) * a t₀ := by
    apply mul_left_cancel₀ hcancel
    linear_combination h1 -
      (((p : ℤ)^m₀)^3 * p * (-1 : ℤ)^(m-m₀) * (unitProduct p (t+m) : ℤ)) * h0
  have hpt : p ∣ t := ⟨t₀, hts⟩
  have hm_cast : ((p : ℤ)^(3*(e+1))) = ((t^3 : ℕ) : ℤ) := by
    dsimp [t]
    push_cast
    rw [← pow_mul, Nat.mul_comm]
  change a t ≡ a t₀ [ZMOD (p : ℤ)^(3*(e+1))]
  rw [hm_cast, ← ZMod.intCast_eq_intCast_iff]
  let R := ZMod (t^3)
  let castR : ℤ →+* R := Int.castRingHom R
  have hfac_cast :
      (-1 : R)^(m-m₀) * (unitProduct p (t+m) : R) = (unitProduct p m : R)^3 := by
    have hpair := congrArg castR (paired_differences p m t ht hpt hp.pos)
    rw [hmdiv] at hpair
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_prod, map_sub] at hpair
    rw [paired_product_mod p (e+1) m hp hp5 (by omega) ht] at hpair
    have hprod : (∏ a ∈ unitRange p m, (a : R)^2) = (unitProduct p m : R)^2 := by
      rw [unitProduct, Nat.cast_prod, Finset.prod_pow]
    rw [hprod] at hpair
    linear_combination hpair
  have hfinal := congrArg castR hunit_eq
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast] at hfinal
  rw [hfac_cast] at hfinal
  have hu : IsUnit (unitProduct p m : R) := by
    rw [unitProduct, Nat.cast_prod]
    refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one ?_
    intro a ha
    change IsUnit (a : ZMod ((p^(e+1))^3))
    rw [← pow_mul]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).2 (mem_filter.mp ha).2
  exact (IsUnit.mul_right_inj (hu.pow 3)).mp hfinal

end A361711Finish

theorem OMA.solution : type_of% @OMA.S_oeis_a361711.main :=
  A361711Finish.congruence
