import OMAReductions.R_oeis_a236539_R1

/-! Hurlburt and Kettlestrings, Further Nonexistence of Fibonacci Triangles,
Propositions 3.1–3.5, normalize an integral-area triangle to a primitive
Pythagorean triple. Here the distance to the preceding square also bounds
the index of the repeated side. Writing g = gcd(i,j), it gives
j + max(2,g) + 4 ≤ 2i. The two remaining equations correspond to
the two possible legs in Euclid's parametrization. -/

namespace OMA.R_oeis_a236539_R1_H2_R1

/-- Extract the primitive half-base, altitude and hypotenuse from Heron's equation. -/
theorem normalize_heron (b u A : ℕ) (hb : 0 < b) (hbu : b < u)
    (h : 16*A^2 = (b+u+u)*(b+u-u)*(b+u-u)*(u+u-b)) :
    ∃ x y z : ℕ, b = 2 * (b.gcd u) * x ∧ u = (b.gcd u) * z ∧
      x.Coprime y ∧ x^2 + y^2 = z^2 := by
  let d := b.gcd u
  let B := b / d
  let z := u / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left u hb
  have hb' : d * B = b := Nat.mul_div_cancel' (Nat.gcd_dvd_left b u)
  have hu' : d * z = u := Nat.mul_div_cancel' (Nat.gcd_dvd_right b u)
  have hc : B.Coprime z := Nat.coprime_div_gcd_div_gcd hd
  have hB : B < z := by
    apply lt_of_mul_lt_mul_left (a := d)
    · simpa only [hb', hu'] using hbu
    · exact Nat.zero_le _
  let v := 2*z-B
  have hv : v + B = 2*z := Nat.sub_add_cancel (by omega)
  have hs : u+u-b = d*v := by
    dsimp [v]
    rw [Nat.mul_sub, ← hb', ← hu']
    ring_nf
  have he : (4*A)^2 = (b*d)^2 * ((B+2*z)*v) := by
    simp only [Nat.add_sub_cancel] at h
    calc
      (4*A)^2 = 16*A^2 := by ring
      _ = _ := h
      _ = (b*d)^2 * ((B+2*z)*v) := by
        rw [hs, ← hb', ← hu']
        ring
  obtain ⟨w, hw⟩ := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    (show (b*d)^2 ∣ (4*A)^2 from ⟨_,he⟩)
  have hw' : w^2 = (B+2*z)*v := by
    rw [hw, mul_pow] at he
    exact Nat.mul_left_cancel (by positivity) he
  have hright : w^2 + B^2 = 4*z^2 := by
    calc
      w^2 + B^2 = (B+2*z)*v + B^2 := by rw [hw']
      _ = (2*z)^2 := by rw [← hv]; ring
      _ = 4*z^2 := by ring
  have mods (a : ℕ) : a^2 % 4 = a % 2 := by
    have ha := Nat.mod_lt a (by decide : 0 < 4)
    calc
      a^2 % 4 = (a%4)^2 % 4 := Nat.pow_mod ..
      _ = (a%4) % 2 := by interval_cases a % 4 <;> decide
      _ = a % 2 := Nat.mod_mod_of_dvd _ (by decide)
  have even : w % 2 = 0 ∧ B % 2 = 0 := by
    have hr := congrArg (fun t : ℕ => t % 4) hright
    change (w^2+B^2)%4 = (4*z^2)%4 at hr
    rw [Nat.add_mod, mods, mods, Nat.mul_mod_right] at hr
    omega
  let x := B/2
  let y := w/2
  have hx : 2*x = B := by dsimp [x]; omega
  have hy : 2*y = w := by dsimp [y]; omega
  have ht : x^2 + y^2 = z^2 := by rw [← hx, ← hy] at hright; nlinarith
  have hp : PythagoreanTriple (x : ℤ) (y : ℤ) (z : ℤ) := by
    unfold PythagoreanTriple
    exact_mod_cast (show x*x+y*y=z*z by simpa [sq] using ht)
  have hdiv : x.gcd y ∣ z := by
    exact Int.natCast_dvd_natCast.mp (by simpa only [Int.gcd_natCast_natCast] using hp.gcd_dvd)
  have hcop : x.Coprime y :=
    Nat.eq_one_of_dvd_coprimes hc ((Nat.gcd_dvd_left x y).trans ⟨2, by omega⟩) hdiv
  refine ⟨x,y,z,?_,hu'.symm,hcop,ht⟩
  change b = 2*d*x
  calc
    b = d*B := hb'.symm
    _ = 2*d*x := by rw [← hx]; ring

/-- The height is an integer strictly below the hypotenuse. -/
private theorem square_spacing {x y z : ℕ} (hx : 0 < x) (h : x^2 + y^2 = z^2) :
    2*z ≤ x^2 + 1 := by
  have hy : y < z := by nlinarith [sq_pos_of_pos hx]
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show y+1 ≤ z by omega)
  rw [hk] at h ⊢
  nlinarith

/-- Compare the square spacing in the primitive triangle with the Fibonacci addition law. -/
theorem index_bound (i j g x y z : ℕ) (hi : 0 < Nat.fib i)
    (hij : Nat.fib i < Nat.fib j) (hb : Nat.fib i = 2*Nat.fib g*x)
    (hu : Nat.fib j = Nat.fib g*z) (ht : x^2+y^2=z^2) :
    j + max 2 g + 4 ≤ 2*i := by
  have hx : 0 < x := by
    by_contra! hh
    rw [show x = 0 by omega, Nat.mul_zero] at hb
    omega
  have hd : 0 < Nat.fib g := by
    by_contra! hh
    rw [show Nat.fib g = 0 by omega, Nat.mul_zero, Nat.zero_mul] at hb
    omega
  have hz : 2*x < z := by
    apply Nat.lt_of_mul_lt_mul_left (a := Nat.fib g)
    simpa [hb,hu,mul_assoc,mul_left_comm,mul_comm] using hij
  have hgap := square_spacing hx ht
  -- Clearing the common scale will give 5 F_j F_g < F_i².
  have hsmall : 5*z < 4*x^2 := by omega
  have hprod : 5 * (Nat.fib j * Nat.fib g) < Nat.fib i^2 := by
    rw [hu,hb]
    nlinarith only [Nat.mul_lt_mul_of_pos_left hsmall (sq_pos_of_pos hd)]
  have hi3 : 3 ≤ i := by
    by_contra! hl
    have hle := Nat.fib_mono (show i ≤ 2 by omega)
    change Nat.fib i ≤ 1 at hle
    have := Nat.mul_le_mul (show 1 ≤ Nat.fib g by omega) (show 1 ≤ x by omega)
    rw [mul_assoc] at hb
    omega
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hi3
  have hsum : Nat.fib (3+n) = Nat.fib n + 2*Nat.fib (n+1) := by
    rw [show 3+n = (n+1)+2 by omega, Nat.fib_add_two, @Nat.fib_add_two n]
    omega
  -- Cauchy–Schwarz applied to F_n + 2 F_(n+1).
  have hsq : Nat.fib (3+n)^2 ≤ 5*Nat.fib (2*n+1) := by
    rw [hsum, Nat.fib_two_mul_add_one]
    nlinarith [sq_nonneg (2*(Nat.fib n : ℤ) - Nat.fib (n+1))]
  have hlim : Nat.fib j * Nat.fib g < Nat.fib (2*n+1) := by omega
  have hj : 0 < j := Nat.fib_pos.mp (by omega)
  by_cases hg : g ≤ 2
  · rw [max_eq_left hg]
    have hidx : j < 2*n+1 := lt_of_not_ge fun h =>
      (hlim.trans_le (Nat.fib_mono h)).not_ge (Nat.le_mul_of_pos_right _ hd)
    omega
  · rw [max_eq_right (by omega : 2 ≤ g)]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ g by omega)
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hshift : Nat.fib (t+1+k) ≤ Nat.fib (t+1) * Nat.fib (2+k) := by
      rw [show t+1+k=t+k+1 by omega, Nat.fib_add, show 2+k=k+2 by omega,
        Nat.fib_add_two, Nat.mul_add]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ Nat.fib_le_fib_succ) _
    have hidx : t+1+k < 2*n+1 := lt_of_not_ge fun h =>
      (hshift.trans_lt hlim).not_ge (Nat.fib_mono h)
    omega

/-- The normalized half-base is the difference-of-squares leg. -/
def H1 : Prop := ∀ (i j : ℕ) (m n : ℤ), i < j → j + max 2 (i.gcd j) + 4 ≤ 2*i →
  (∀ s : ℕ, 2^(s+2) ∣ j → 2^(s+2) ∣ i) →
  m.gcd n = 1 → m % 2 ≠ n % 2 →
  (Nat.fib j : ℤ) = Nat.fib (i.gcd j) * (m^2+n^2) →
  (Nat.fib i : ℤ) ≠ 2 * Nat.fib (i.gcd j) * (m^2-n^2)

/-- The normalized half-base is the product leg. -/
def H2 : Prop := ∀ (i j : ℕ) (m n : ℤ), i < j → j + max 2 (i.gcd j) + 4 ≤ 2*i →
  (∀ s : ℕ, 2^(s+2) ∣ j → 2^(s+2) ∣ i) →
  m.gcd n = 1 → m % 2 ≠ n % 2 →
  (Nat.fib j : ℤ) = Nat.fib (i.gcd j) * (m^2+n^2) →
  (Nat.fib i : ℤ) ≠ 4 * Nat.fib (i.gcd j) * m * n

theorem main : H1 → H2 → OMA.R_oeis_a236539_R1.H2 := by
  intro h₁ h₂ i j A hi hij _ hdy h
  obtain ⟨x,y,z,hb,hu,hc,ht⟩ := normalize_heron _ _ A hi hij h
  rw [← Nat.fib_gcd] at hb hu
  let d := Nat.fib (i.gcd j)
  change Nat.fib i = 2*d*x at hb
  change Nat.fib j = d*z at hu
  have hbound := index_bound i j (i.gcd j) x y z hi hij hb hu ht
  have hindex : i < j := lt_of_not_ge (fun hj => (Nat.fib_mono hj).not_gt hij)
  have hp : PythagoreanTriple (x : ℤ) (y : ℤ) (z : ℤ) := by
    unfold PythagoreanTriple
    exact_mod_cast (show x*x+y*y=z*z by simpa [sq] using ht)
  obtain ⟨m,n,legs,hz,hm,parity⟩ := PythagoreanTriple.coprime_classification.mp
    ⟨hp, by simpa only [Int.gcd_natCast_natCast] using hc⟩
  have hzpos : 0 < z := by
    by_contra! hn
    have : z = 0 := by omega
    simp [this] at hu
    omega
  have hsum : (z : ℤ) = m^2+n^2 := hz.resolve_right (by
    have : (0 : ℤ) < z := by exact_mod_cast hzpos
    nlinarith [sq_nonneg m, sq_nonneg n])
  have hpar : m%2 ≠ n%2 := by rcases parity with h | h <;> omega
  have hleg : (Nat.fib i : ℤ) = 2*(d : ℤ)*x := by exact_mod_cast hb
  have hhyp : (Nat.fib j : ℤ) = (d : ℤ)*(m^2+n^2) := by
    rw [← hsum]
    exact_mod_cast hu
  rcases legs with leg | leg
  · exact h₁ i j m n hindex hbound hdy hm hpar hhyp (by rwa [leg.1] at hleg)
  · apply h₂ i j m n hindex hbound hdy hm hpar hhyp
    rw [hleg, leg.1]
    ring

end OMA.R_oeis_a236539_R1_H2_R1
