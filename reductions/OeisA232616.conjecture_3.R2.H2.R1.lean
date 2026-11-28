import OMAReductions.R_OeisA232616_conjecture_3_R2

/-! Extract a prime exponent and normalize the resulting bases by their gcd. -/
-- Credit: @PanPapag

namespace OMA.R_OeisA232616_conjecture_3_R2_H2_R1

def H1 : Prop := ∀ d a b t : ℕ, 1 < d → 0 < a → 0 < b → 0 < t →
  a.Coprime b → let n := d^2*t
  n.Coprime 2 → d^(n-2)*a^n+t ≠ b^2

def H2 : Prop := ∀ d a b t p : ℕ, p.Prime → 2 < p → 1 < d → 0 < a → 0 < b → 0 < t →
  a.Coprime b → let n := d^p*t
  n.Coprime p → d^(n-p)*a^n+t ≠ b^p

-- Power gap from desk note 131676.
private theorem gap (u k : ℕ) (hu : 0 < u) :
    u^(k+2) + (k+2)*u ≤ (u+1)^(k+2) := by
  induction k with
  | zero => simp; nlinarith
  | succ k ih =>
    have h := Nat.mul_le_mul_right (u+1) ih
    rw [pow_succ (u+1) (k+2), pow_succ u (k+2)]
    have hpow : u ≤ u^(k+2) := by simpa using Nat.pow_le_pow_right hu (show 1 ≤ k+2 by omega)
    apply le_trans _ h
    calc
      _ ≤ u^(k+2)*u + (k+2)*u + u^(k+2)  := by
        calc
          _ = u^(k+2)*u + (k+2)*u + u := by ring
          _ ≤ _ := by omega
      _ ≤ (u^(k+2)+(k+2)*u)*(u+1) := by
        rw [Nat.mul_add]
        simp only [Nat.mul_one, Nat.add_mul]
        omega

theorem coprime_exponents {x y n m : ℕ} (hx : 1 < x) (hn : 0 < n)
    (eqn : x^n+n=y^m) : n.Coprime m := by
  by_contra hc
  obtain ⟨p,hp,hpn,hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  obtain ⟨l,rfl⟩ := hpn
  obtain ⟨j,rfl⟩ := hpm
  rw [Nat.mul_comm p l, pow_mul, Nat.mul_comm p j, pow_mul] at eqn
  have hu : l < x^l := Nat.lt_pow_self hx
  have hlt : x^l < y^j := by
    by_contra! h
    have := Nat.pow_le_pow_left h p
    rw [Nat.mul_comm] at hn
    omega
  have hbound := Nat.pow_le_pow_left (show x^l+1 ≤ y^j by omega) p
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hp.two_le
  have hg := gap (x^l) k (by positivity)
  rw [show k+2=p by omega] at hg
  have := Nat.mul_lt_mul_of_pos_left hu hp.pos
  nlinarith

theorem main : H1 → H2 → OMA.R_OeisA232616_conjecture_3_R2.H2 := by
  intro squares oddPrimes c u v w m hc hu hv hw hm _
  dsimp only
  intro eqn
  let n := c^m*w
  let x := c*u
  let p := m.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  obtain ⟨k,hk⟩ := Nat.minFac_dvd m
  have hkpos : 0 < k := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hk; omega
  let y := (c*v)^k
  have hx : 1 < x := by dsimp [x]; nlinarith
  have hy : 0 < y := by dsimp [y]; positivity
  have hn : 0 < n := by dsimp [n]; positivity
  have hmn : m ≤ n := (Nat.lt_pow_self hc).le.trans (Nat.le_mul_of_pos_right _ hw)
  change c^(n-m)*u^n+w=v^m at eqn
  have e : x^n+n=y^p := by
    have h := congrArg (fun z : ℕ => c^m*z) eqn
    simp only [Nat.mul_add, ← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le hmn] at h
    change (c*u)^n+n=((c*v)^k)^p
    rw [← pow_mul, Nat.mul_comm k p, ← hk, mul_pow, mul_pow]
    simpa [Nat.add_comm m (n-m), Nat.sub_add_cancel hmn, n] using h
  have hcop := coprime_exponents hx hn e
  -- Normalize the new bases as in desenyon's parent reduction.
  let d := x.gcd y
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
  have hcy : c ∣ y := dvd_trans (dvd_mul_right c v)
    (dvd_pow_self (c*v) hkpos.ne')
  have hd2 : 1 < d := hc.trans_le (Nat.le_of_dvd hd
    (Nat.dvd_gcd (dvd_mul_right c u) hcy))
  have dx : d ∣ x := Nat.gcd_dvd_left ..
  have dy : d ∣ y := Nat.gcd_dvd_right ..
  have pn : p ≤ n := (Nat.le_of_dvd (by omega : 0 < m) (Nat.minFac_dvd m)).trans hmn
  have hsum : d^p ∣ x^n+n := e ▸ pow_dvd_pow_of_dvd_of_le dy le_rfl
  obtain ⟨t,ht⟩ := (Nat.dvd_add_right (pow_dvd_pow_of_dvd_of_le dx pn)).mp hsum
  let a := x / d
  let b := y / d
  have hxa : a * d = x := Nat.div_mul_cancel dx
  have hyb : b * d = y := Nat.div_mul_cancel dy
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hd
  have ha : 0 < a := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hxa; omega
  have hb : 0 < b := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hyb; omega
  have htpos : 0 < t := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at ht; omega
  have no : let N := d^p*t; N.Coprime p → d^(N-p)*a^N+t ≠ b^p := by
    by_cases he : p = 2
    · simpa only [he] using squares d a b t hd2 ha hb htpos hab
    · exact oddPrimes d a b t p hp (by have := hp.two_le; omega) hd2 ha hb htpos hab
  apply no (ht ▸ hcop)
  rw [← ht]
  have hdexp : d ^ (n - p) * d ^ p = d ^ n := by rw [← pow_add, Nat.sub_add_cancel pn]
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hd p)
  calc
    (d ^ (n - p) * a ^ n + t) * d ^ p = a ^ n * (d ^ (n - p) * d ^ p) + d ^ p * t := by ring
    _ = x ^ n + n := by rw [hdexp, ← mul_pow, hxa, ← ht]
    _ = b ^ p * d ^ p := by rw [e, ← mul_pow, hyb]

end OMA.R_OeisA232616_conjecture_3_R2_H2_R1
