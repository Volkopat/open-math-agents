import OMAStatements.S_oeis_a337828

-- Credit: @Pixelstorm44
namespace OMA.R_oeis_a337828_R1

open OMA.S_oeis_a337828

/-- The order of minus a divides both u and its least prime factor minus one. -/
private lemma least_factor {u a : ℕ} (hu : 1 < u) (ho : Odd u)
    (hd : u ∣ a ^ u + 1) : u.minFac ∣ a + 1 := by
  let p := u.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  let : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff _ p).2 ((Nat.minFac_dvd u).trans hd)
  push_cast at hz
  have he : (-(a : ZMod p)) ^ u = 1 := by rw [ho.neg_pow]; linear_combination -hz
  have hn : -(a : ZMod p) ≠ 0 := by
    intro h
    simp [h, zero_pow (by omega : u ≠ 0)] at he
  have hc : u.Coprime (p - 1) :=
    Nat.coprime_of_lt_minFac (by have := hp.two_le; omega) (by change p - 1 < p; have := hp.two_le; omega)
  have hd1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one he) (ZMod.orderOf_dvd_card_sub_one hn)
  rw [hc.gcd_eq_one] at hd1
  have ha := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)
  apply (ZMod.natCast_eq_zero_iff _ p).1
  push_cast
  linear_combination -ha

/-- Apart from 1 and 2, a half-index is twice an odd multiple of five. -/
private lemma half_shape {m : ℕ} (hm : 1 < m) (hd : m ∣ 3 ^ m + 1) :
    ∃ u, m = 2*u ∧ Odd u ∧ (u = 1 ∨ 5 ∣ u) := by
  have he : 2 ∣ m := by
    by_contra hn
    have ho : Odd m := by rw [Nat.odd_iff]; omega
    have h4 := least_factor hm ho hd
    have hp := Nat.minFac_prime (show m ≠ 1 by omega)
    have h2 := hp.two_le
    have hf : m.minFac = 2 := by
      have h := hp.dvd_mul.mp (show m.minFac ∣ 2 * 2 from h4)
      rcases h with h | h <;> have := Nat.le_of_dvd (by decide : 0 < 2) h <;> omega
    exact hn (hf ▸ Nat.minFac_dvd m)
  obtain ⟨u, rfl⟩ := he
  have hz : 3 ^ (2*u) + 1 ≡ 2 [MOD 4] := by
    rw [pow_mul]
    have h := (show 3^2 ≡ 1 [MOD 4] by decide).pow u
    simpa using h.add_right 1
  have ho : Odd u := by
    rw [Nat.odd_iff]
    by_contra h
    have h4 : 4 ∣ 2*u := by omega
    have := h4.trans hd
    change (3 ^ (2*u) + 1) % 4 = 2 % 4 at hz
    omega
  refine ⟨u, rfl, ho, ?_⟩
  by_cases h1 : u = 1
  · exact Or.inl h1
  apply Or.inr
  have hu : u ∣ (3^2)^u + 1 := by rw [← pow_mul]; exact dvd_trans (Nat.dvd_mul_left u 2) hd
  have h10 := least_factor (by omega : 1 < u) ho hu
  have hp := Nat.minFac_prime h1
  have h := hp.dvd_mul.mp (show u.minFac ∣ 2*5 from h10)
  have hmin := Nat.minFac_dvd u
  have hodd := Nat.odd_iff.mp ho
  rcases h with h | h
  · have := Nat.le_of_dvd (by decide : 0 < 2) h
    have hf : u.minFac = 2 := by have := hp.two_le; omega
    rw [hf] at hmin
    omega
  · have hf := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp h
    have := hp.two_le
    rcases hf with hf | hf
    · omega
    · exact hf ▸ hmin

private lemma prime_divides {k : ℕ} (hp : k.Prime) (h4 : k % 4 = 1) (h3 : k % 3 = 2) :
    k ∣ 3 ^ ((k-1)/2) + 1 := by
  let : Fact k.Prime := ⟨hp⟩
  have hc : (k : ZMod 3) = 2 := by rw [← ZMod.natCast_mod, h3]; rfl
  have hl : legendreSym 3 k = -1 := by
    change quadraticChar (ZMod 3) ((k : ℤ) : ZMod 3) = -1
    rw [Int.cast_natCast, hc]
    decide
  have hq := legendreSym.quadratic_reciprocity_one_mod_four (p := k) (q := 3) h4 (by decide)
  have hv := legendreSym.eq_pow k 3
  norm_num only [Nat.cast_ofNat] at hq
  rw [← hq, hl] at hv
  apply (ZMod.natCast_eq_zero_iff _ k).1
  push_cast at hv ⊢
  rw [show (k-1)/2 = k/2 by omega, ← hv]
  simp

private lemma one_mod_four_of_factors {u : ℕ} (hn : u ≠ 0)
    (hall : ∀ p : ℕ, p.Prime → p ∣ u → p % 4 = 1) : u % 4 = 1 := by
  induction u using induction_on_primes with
  | zero => contradiction
  | one => decide
  | prime_mul p n hp ih =>
    have h1 := hall p hp (dvd_mul_right p n)
    have h2 := ih (by rintro rfl; simp at hn)
      (fun q hq hqn => hall q hq (hqn.trans (dvd_mul_left n p)))
    rw [Nat.mul_mod, h1, h2]

private lemma prime_one_mod_four {p u : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (hd : p ∣ 3^(2*u)+1) : p % 4 = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff _ p).2 hd
  push_cast at hz
  rw [mul_comm 2 u, pow_mul] at hz
  have ha : ((3 : ZMod p)^u)^2 = -1 := by linear_combination hz
  have := ZMod.mod_four_ne_three_of_sq_eq_neg_one ha
  have := Nat.odd_iff.mp (hp.odd_of_ne_two hne)
  omega

/-- The order divides twice the exponent but does not divide the exponent. -/
private lemma order_shape {p u : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (hd : p ∣ 3^(2*u)+1) :
    ∃ d, d ∣ u ∧ orderOf (3 : ZMod p) = 4*d := by
  let : Fact p.Prime := ⟨hp⟩
  let r := orderOf (3 : ZMod p)
  have hz := (ZMod.natCast_eq_zero_iff _ p).2 hd
  push_cast at hz
  have ha : (3 : ZMod p)^(2*u) = -1 := by linear_combination hz
  have hr : r ∣ (2*u)*2 := orderOf_dvd_of_pow_eq_one (by rw [pow_mul, ha]; simp)
  have hnot : ¬ r ∣ 2*u := by
    intro h
    have h1 := orderOf_dvd_iff_pow_eq_one.mp h
    rw [ha] at h1
    have hz : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -h1
    exact hne ((Nat.dvd_prime Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff _ _).mp hz) |>.resolve_left hp.ne_one)
  obtain ⟨t, ht⟩ := hr
  have htodd : ¬ 2 ∣ t := by
    rintro ⟨b, rfl⟩
    exact hnot ⟨b, by nlinarith only [ht]⟩
  have hcop : Nat.Coprime 4 t := by
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr htodd).pow_left 2
  have h4 : 4 ∣ r*t := ⟨u, by omega⟩
  obtain ⟨d, hrd⟩ := hcop.dvd_of_dvd_mul_right h4
  exact ⟨d, ⟨t, by rw [hrd] at ht; nlinarith only [ht]⟩, hrd⟩

/-- At a repeated prime, Euler’s theorem and the global congruence force
the base-three Wieferich congruence modulo the prime square. -/
private lemma repeated_prime {p k m : ℕ} (hp : p.Prime) (hpk : p^2 ∣ k)
    (hkm : k = 2*m+1) (h3 : k % 3 = 2) (hd : k ∣ 3^m+1) :
    3^(p-1) ≡ 1 [MOD p^2] := by
  have hpk' : p ∣ k := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hpk
  have hpn : ¬ p ∣ 3 := by
    intro h
    have : p = 3 := ((Nat.prime_three.dvd_iff_eq hp.ne_one).mp h).symm
    rw [this] at hpk'
    omega
  have hf := (ZMod.natCast_eq_natCast_iff _ _ _).2
    (Nat.ModEq.pow_totient (hp.coprime_pow_of_not_dvd (m := 2) hpn))
  rw [Nat.totient_prime_pow_succ hp 1, pow_one, Nat.cast_pow, Nat.cast_one,
    mul_comm, pow_mul] at hf
  let x := (3 : ZMod (p^2)) ^ (p-1)
  have hx : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hf
  have hz := (ZMod.natCast_eq_zero_iff _ _).2 (hpk.trans hd)
  push_cast at hz
  have ha : (3 : ZMod (p^2))^m = -1 := by linear_combination hz
  have hx' : x ^ (2*m) = 1 := by
    dsimp [x]
    rw [← pow_mul, mul_comm (p-1), pow_mul, mul_comm 2, pow_mul, ha]
    simp
  have he := (Nat.dvd_prime hp).mp hx
  rcases he with he | he
  · apply (ZMod.natCast_eq_natCast_iff _ _ _).1
    push_cast
    exact orderOf_eq_one_iff.mp he
  · have hdiv := orderOf_dvd_of_pow_eq_one hx'
    rw [he] at hdiv
    have hone : p ∣ 1 := by
      have h := Nat.dvd_sub hpk' hdiv
      rwa [hkm, Nat.add_sub_cancel_left] at h
    exact (hp.not_dvd_one hone).elim

/-- A squarefree composite in the remaining progression has a prime factor
whose order of three is not four times a divisor of the quarter-index. -/
def H1 : Prop := ∀ k : ℕ, k % 240 = 101 → Squarefree k → ¬ k.Prime →
  HalfCondition k → ∃ p : ℕ, p.Prime ∧ p ∣ k ∧
    ¬ ∃ d, d ∣ (k-1)/4 ∧ orderOf (3 : ZMod p) = 4*d

/-- Exclude candidates containing the square of a base-three Wieferich prime
congruent to one modulo four. -/
def H2 : Prop := ∀ k p : ℕ, k % 240 = 101 → p.Prime → p % 4 = 1 →
  p^2 ∣ k → 3^(p-1) ≡ 1 [MOD p^2] → HalfCondition k → ¬ k ∣ 3^((k-1)/2)+1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a337828.main := by
  intro h1 h2 k
  constructor
  · rintro ⟨hk, ho, hd⟩
    let m := (k-1)/2
    have hodd := Nat.odd_iff.mp ho
    have hkm : k = 2*m+1 := by dsimp [m]; omega
    have hpos : 0 < m := by omega
    have hm : m ∣ 3^m+1 := dvd_trans (Nat.dvd_mul_left m k) hd
    have hkd : k ∣ 3^m+1 := dvd_trans (Nat.dvd_mul_right k m) hd
    have hc : HalfCondition k := ⟨hpos, hm⟩
    have hn : ¬ 3 ∣ 3^m+1 := by
      have h := dvd_pow_self 3 (by omega : m ≠ 0)
      omega
    have h3 : k % 3 = 2 := by
      have hna : ¬ 3 ∣ k := fun h => hn (h.trans hkd)
      have hnb : ¬ 3 ∣ m := fun h => hn (h.trans hm)
      omega
    refine ⟨?_, h3, hc⟩
    by_cases hs : m ≤ 2
    · have : k = 5 := by omega
      rw [this]
      decide
    obtain ⟨u, hu, hou, h5⟩ := half_shape (by omega : 1 < m) hm
    have huodd := Nat.odd_iff.mp hou
    have hu4 : u % 4 = 1 := by
      apply one_mod_four_of_factors (by omega)
      intro p hp hpu
      have hne : p ≠ 2 := by rintro rfl; omega
      apply prime_one_mod_four hp hne (u := u)
      rw [← hu]
      exact hpu.trans ((show u ∣ m by rw [hu]; exact Nat.dvd_mul_left u 2).trans hm)
    have hprog : k % 240 = 101 := by omega
    have hlocal (p : ℕ) (hpk : p ∣ k) : p ∣ 3^(2*u)+1 := by
      rw [← hu]
      exact hpk.trans hkd
    by_contra hnp
    by_cases hsf : Squarefree k
    · obtain ⟨p, hp, hpk, hfail⟩ := h1 k hprog hsf hnp hc
      have hne : p ≠ 2 := by rintro rfl; omega
      apply hfail
      rw [show (k-1)/4 = u by omega]
      exact order_shape hp hne (hlocal p hpk)
    · rw [Nat.squarefree_iff_prime_squarefree] at hsf
      push Not at hsf
      obtain ⟨p, hp, hpp⟩ := hsf
      have hpk := (Nat.dvd_mul_right p p).trans hpp
      have hne : p ≠ 2 := by rintro rfl; omega
      have hp4 := prime_one_mod_four hp hne (hlocal p hpk)
      rw [← pow_two] at hpp
      exact h2 k p hprog hp hp4 hpp (repeated_prime hp hpp hkm h3 hkd) hc hkd
  · rintro ⟨hp, h3, hpos, hm⟩
    let m := (k-1)/2
    have hk := hp.two_le
    have hne : k ≠ 2 := by intro h; rw [h] at hpos; norm_num at hpos
    have ho := hp.odd_of_ne_two hne
    have hodd := Nat.odd_iff.mp ho
    have hkm : k = 2*m+1 := by dsimp [m]; omega
    have hm' : m ∣ 3^m+1 := hm
    have hgt : 1 < m := by omega
    obtain ⟨u, hu, _, _⟩ := half_shape hgt hm'
    have h4 : k % 4 = 1 := by omega
    have hcop : k.Coprime m := by
      rw [show k = 1 + m * 2 by omega, Nat.coprime_add_mul_left_left]
      exact Nat.coprime_one_left m
    exact ⟨by omega, ho, hcop.mul_dvd_of_dvd_of_dvd (prime_divides hp h4 h3) hm⟩

end OMA.R_oeis_a337828_R1
