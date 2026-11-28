import OMAStatements.S_wp_erdos_mollin_walsh_conjecture

-- Credit: @Pixelstorm44
namespace OMA.R_wp_erdos_mollin_walsh_conjecture_R1

open OMA.S_wp_erdos_mollin_walsh_conjecture

private theorem no_two_mod_four {n : ℕ} (h : Powerful n) : n % 4 ≠ 2 := by
  intro hr
  have hd : 2 ∣ n := by omega
  have h4 := h 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, by omega⟩)
  norm_num at h4
  omega

private theorem powerful_mul {u v : ℕ} (hu : Powerful u) (hv : Powerful v) :
    Powerful (u * v) := by
  intro p hp
  obtain ⟨prime, divides, nz⟩ := Nat.mem_primeFactors.mp hp
  rcases prime.dvd_mul.mp divides with h | h
  · exact dvd_mul_of_dvd_left (hu p (Nat.mem_primeFactors.mpr
      ⟨prime, h, left_ne_zero_of_mul nz⟩)) v
  · exact dvd_mul_of_dvd_right (hv p (Nat.mem_primeFactors.mpr
      ⟨prime, h, right_ne_zero_of_mul nz⟩)) u

/-- The squarefree part of a positive powerful number divides its square coordinate. -/
private theorem kernel_dvd {d y : ℕ} (hd : Squarefree d) (hy : y ≠ 0)
    (h : Powerful (y ^ 2 * d)) : d ∣ y := by
  rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.prod_primeFactors_dvd_iff hy]
  intro p hp
  obtain ⟨prime, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  apply Nat.mem_primeFactors.mpr
  refine ⟨prime, ?_, hy⟩
  by_contra hpy
  have hsq := h p (Nat.mem_primeFactors.mpr
    ⟨prime, dvd_mul_of_dvd_right hpd _, mul_ne_zero (pow_ne_zero _ hy) hd.ne_zero⟩)
  have bad := ((prime.coprime_iff_not_dvd.mpr hpy).pow 2 2).dvd_of_dvd_mul_left hsq
  exact Nat.squarefree_iff_prime_squarefree.mp hd p prime (by simpa [sq] using bad)

private theorem parameter_mod_eight {n y d : ℕ} (hc : 4 ∣ n + 1)
    (he : y ^ 2 * d = n * (n + 2)) : d % 8 = 7 := by
  obtain ⟨k, hk⟩ := hc
  have eqn : (4 * k)^2 = 1 + y^2 * d := by rw [← hk, he]; ring
  have hz := congrArg (fun t : ℕ => (t : ZMod 8)) eqn
  push_cast at hz
  have sieve : ∀ a b c : ZMod 8, (4 * a)^2 = 1 + b^2 * c → c = 7 := by decide
  exact (ZMod.natCast_eq_natCast_iff' d 7 8).mp (sieve _ _ _ hz)

private theorem even_power_x {d : ℤ} (a : Pell.Solution₁ d) (k : ℕ) :
    (a ^ (2*k)).x = 2 * (a^k).x ^ 2 - 1 := by
  rw [two_mul, pow_add, Pell.Solution₁.x_mul]
  nlinarith [(a^k).prop]

/-- Reduction of odd Pell powers modulo the parameter, valid also at composite d. -/
private theorem odd_coordinates (d : ℕ) (a : Pell.Solution₁ (d : ℤ)) (j : ℕ) :
    (((a ^ (2*j+1)).x : ℤ) : ZMod d) = a.x ∧
    (((a ^ (2*j+1)).y : ℤ) : ZMod d) = (2 * (j : ZMod d) + 1) * a.y := by
  have hx := congrArg (fun t : ℤ => (t : ZMod d)) a.prop_x
  push_cast at hx
  simp at hx
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2*(j+1)+1 = (2*j+1)+1+1 by omega, pow_succ, pow_succ]
    simp only [Pell.Solution₁.x_mul, Pell.Solution₁.y_mul, Int.cast_add,
      Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero,
      ih.1, ih.2, Nat.cast_succ]
    constructor
    · linear_combination (a.x : ZMod d) * hx
    · linear_combination ((2 * (j : ZMod d) + 3) * a.y) * hx

private theorem powerful_of_coprime_factor {u v : ℕ} (hv : v ≠ 0)
    (hcop : u.Coprime v) (hh : Powerful (u*v)) : Powerful u := by
  intro p hp
  have hpu := Nat.dvd_of_mem_primeFactors hp
  have hq := hh p (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
    dvd_mul_of_dvd_left hpu _, mul_ne_zero (Nat.mem_primeFactors.mp hp).2.2 hv⟩)
  exact ((hcop.of_dvd_left hpu).pow_left 2).dvd_of_dvd_mul_right hq

/-- Each admissible Pell point with a powerful x-coordinate gives an actual triple. -/
theorem triple_of_point {d : ℕ} (b : Pell.Solution₁ (d : ℤ)) (hx : 0 < b.x)
    (hy : 0 ≤ b.y) (h4 : (4 : ℤ) ∣ b.x) (hdy : (d : ℤ) ∣ b.y)
    (hc : Powerful b.x.toNat) :
    ∃ n : ℕ, Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2) := by
  let n := b.x.toNat - 1
  let y := b.y.toNat
  have nx : b.x = (n : ℤ)+1 := by dsimp [n]; omega
  have yy : b.y = (y : ℤ) := (Int.toNat_of_nonneg hy).symm
  have hn : 0 < n := by omega
  have he : n*(n+2) = y^2*d := by
    have h := b.prop
    rw [nx, yy] at h
    exact_mod_cast (show (n : ℤ)*(n+2) = (y : ℤ)^2*d by linarith only [
      show (n : ℤ)*(n+2)-y^2*d = ((n:ℤ)+1)^2 - d*y^2 - 1 by ring, h])
  have hd : d ∣ y := by rw [yy] at hdy; exact_mod_cast hdy
  have hprod : Powerful (n*(n+2)) := by
    rw [he]
    intro p hp
    obtain ⟨prime, hmul, _⟩ := Nat.mem_primeFactors.mp hp
    have hpy : p ∣ y := (prime.dvd_mul.mp hmul).elim prime.dvd_of_dvd_pow (·.trans hd)
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hpy 2) _
  have hcop : n.Coprime (n+2) := by
    rw [Nat.coprime_add_iff_right (dvd_refl n), Nat.coprime_comm,
      Nat.prime_two.coprime_iff_not_dvd]
    omega
  exact ⟨n, powerful_of_coprime_factor (by omega) hcop hprod,
    (show b.x.toNat = n+1 by omega) ▸ hc,
    powerful_of_coprime_factor hn.ne' hcop.symm (by simpa [mul_comm] using hprod)⟩

/-- The fundamental solution of each eligible Pell equation. -/
def H1 : Prop :=
  ∀ d : ℕ, Squarefree d → d % 8 = 7 →
    ∀ a : Pell.Solution₁ (d : ℤ), Pell.IsFundamental a →
      (d : ℤ) ∣ a.y → (4 : ℤ) ∣ a.x → ¬ Powerful a.x.toNat

/-- Higher odd powers need testing only when the index times the
fundamental y-coordinate is divisible by the discriminant parameter d. -/
def H2 : Prop :=
  ∀ d : ℕ, Squarefree d → d % 8 = 7 →
    ∀ a : Pell.Solution₁ (d : ℤ), Pell.IsFundamental a →
      ∀ j : ℕ, 0 < j → (d : ℤ) ∣ (2 * (j : ℤ) + 1) * a.y →
        (4 : ℤ) ∣ (a ^ (2 * j + 1)).x → ¬ Powerful (a ^ (2 * j + 1)).x.toNat

theorem necessary_conditions
    (h : ¬ ∃ n : ℕ, Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2)) : H1 ∧ H2 := by
  constructor
  · intro d _ _ a ha hd h4 hp
    exact h (triple_of_point a ha.x_pos ha.2.1.le h4 hd hp)
  · intro d _ _ a ha j _ hd h4 hp
    have hy : (d : ℤ) ∣ (a^(2*j+1)).y := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      rw [(odd_coordinates d a j).2]
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    exact h (triple_of_point _ (Pell.Solution₁.x_pow_pos ha.x_pos _)
      (Pell.Solution₁.y_pow_succ_pos ha.x_pos ha.2.1 _).le h4 hy hp)

theorem main : H1 → H2 → type_of% @OMA.S_wp_erdos_mollin_walsh_conjecture.main := by
  rintro hfund hhigher ⟨n, hl, hc, hr⟩
  have hfour : 4 ∣ n+1 := by
    have := no_two_mod_four hl
    have := no_two_mod_four hc
    have := no_two_mod_four hr
    omega
  have hn : 0 < n := by omega
  obtain ⟨d,y,hd,hy,he,hs⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < n*(n+2) by positivity)
  have hdy := kernel_dvd hs hy.ne' (he ▸ powerful_mul hl hr)
  have hm := parameter_mod_eight hfour he
  have eqn : ((n+1 : ℕ) : ℤ)^2 - (d : ℤ)*(y : ℤ)^2 = 1 := by
    have he' : (y : ℤ)^2 * d = n * ((n : ℤ)+2) := by exact_mod_cast he
    push_cast
    linarith only [show ((n : ℤ)+1)^2 - d*y^2 - 1 =
      (n : ℤ)*(n+2) - y^2*d by ring, he']
  let b := Pell.Solution₁.mk (d := (d : ℤ)) (n+1) y (by simpa using eqn)
  have bx : b.x = (n : ℤ)+1 := rfl
  have by' : b.y = (y : ℤ) := rfl
  have hbx : 1 < b.x := by rw [bx]; omega
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare (by exact_mod_cast hd)
    (Pell.Solution₁.d_nonsquare_of_one_lt_x hbx)
  obtain ⟨k, hk⟩ := ha.eq_pow_of_nonneg (by omega : 0 < b.x) (by rw [by']; positivity)
  have kx : (a^k).x = (n : ℤ)+1 := hk ▸ bx
  have ky : (a^k).y = (y : ℤ) := hk ▸ by'
  have hkodd : k % 2 = 1 := by
    by_contra h
    have heven : k = 2*(k/2) := by omega
    rw [heven, even_power_x] at kx
    omega
  let j := k / 2
  have kj : k = 2*j+1 := by dsimp [j]; omega
  rw [kj] at kx ky
  have hdiv : (d : ℤ) ∣ (a^(2*j+1)).y := by rw [ky]; exact_mod_cast hdy
  have hindex : (d : ℤ) ∣ (2*(j : ℤ)+1)*a.y := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [← (odd_coordinates d a j).2]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
  have h4 : (4 : ℤ) ∣ (a^(2*j+1)).x := by rw [kx]; exact_mod_cast hfour
  have hp : Powerful (a^(2*j+1)).x.toNat := by simpa [kx] using hc
  by_cases hj : j = 0
  · simp [hj] at h4 hp hindex
    exact hfund d hs hm a ha hindex h4 hp
  · exact hhigher d hs hm a ha j (Nat.pos_of_ne_zero hj) hindex h4 hp

end OMA.R_wp_erdos_mollin_walsh_conjecture_R1
