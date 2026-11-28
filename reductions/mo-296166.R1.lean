import OMAStatements.S_mo_296166
import Mathlib

/-!
# Strong probable-prime pairs with a composite outer number

The question is due to fgrieu (https://mathoverflow.net/q/296166). Fedor Petrov's
argument (https://mathoverflow.net/a/295517) excludes a prime half using the
multiplicative order. Here the order of four supplies a proper exponent d for *both* signs.

Any counterexample decomposes as m = d*u with d,u odd and greater than one.
The outer number 2m+1 divides either 2^d-1 or 2^d+1. Testing strength of m
also rules out complementary factor one in both cases and factor three in the
second case. The two hypotheses concern precisely the remaining signed cases.
-/

namespace OMA.R_mo_296166_R1

/-- For composite n = 2m+1, a base-two Fermat test forces the order of four
to be a nontrivial proper divisor of m. This also excludes every prime m. -/
theorem proper_order {n m : ℕ} (hn : n = 2*m+1) (hm : 1 < m)
    (hc : ¬ n.Prime) (test : (4 : ZMod n)^m = 1) :
    1 < orderOf (4 : ZMod n) ∧ orderOf (4 : ZMod n) ∣ m ∧ orderOf (4 : ZMod n) < m := by
  have hn2 : 2 < n := by omega
  have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.mpr ⟨m, by omega⟩
  have divM := orderOf_dvd_of_pow_eq_one test
  have pos := Nat.pos_of_dvd_of_pos divM (by omega : 0 < m)
  have notOne : orderOf (4 : ZMod n) ≠ 1 := by
    intro h
    have eqn := orderOf_eq_one_iff.mp h
    have eqmod : 4 ≡ 1 [MOD n] := (ZMod.natCast_eq_natCast_iff 4 1 n).mp (by simpa using eqn)
    change 4 % n = 1 % n at eqmod
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at eqmod
    contradiction
  obtain ⟨f,hf⟩ := Nat.totient_even hn2
  have euler := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient hcop)
  push_cast at euler
  have pow4 : (4 : ZMod n)^f = 1 := by
    rw [show (4:ZMod n) = 2^2 by norm_num, ← pow_mul, show 2*f = n.totient by omega]
    exact euler
  have phiPos := Nat.totient_pos.mpr (by omega : 0 < n)
  have ordLe := Nat.le_of_dvd (by omega : 0 < f) (orderOf_dvd_of_pow_eq_one pow4)
  have phiLt := Nat.totient_lt n (by omega)
  have hfLt : f < m := by
    by_contra! hle
    apply hc
    apply (Nat.totient_eq_iff_prime (by omega : 0 < n)).mp
    omega
  exact ⟨by omega, divM, ordLe.trans_lt hfLt⟩


open OMA.S_mo_296166

theorem strong_odd {m : ℕ} (hs : StrongProbablePrime m) (hne : m ≠ 2) : Odd m := by
  rcases hs with he | ⟨hm, d, s, hd, he, h⟩
  · contradiction
  apply Nat.not_even_iff_odd.mp
  intro hEven
  obtain rfl | s := s
  · simp only [pow_zero, Nat.mul_one] at he
    rcases h with h | ⟨r, hr, _⟩
    · have hmod := Nat.ModEq.of_dvd hEven.two_dvd h
      change 2^d % 2 = 1 % 2 at hmod
      have hd0 := hd.pos
      rw [Nat.pow_mod] at hmod
      simp [show d ≠ 0 by omega] at hmod
    · omega
  · have htwo : 2 ∣ m-1 := he ▸ Nat.dvd_mul_left_of_dvd (dvd_pow_self _ (by omega)) d
    obtain ⟨a, ha⟩ := htwo
    obtain ⟨b, hb⟩ := hEven
    omega

theorem strong_sign {n m : ℕ} (hs : StrongProbablePrime n) (hn : n = 2*m+1)
    (hm : Odd m) : (2 : ZMod n)^m = 1 ∨ (2 : ZMod n)^m = -1 := by
  rcases hs with he | ⟨_, d, s, hd, he, h⟩
  · omega
  have hval : 2*m = d*2^s := by omega
  have hs' : s = 1 := by
    cases s with
    | zero => simp only [pow_zero, Nat.mul_one] at hval; obtain ⟨k,hk⟩ := hd; omega
    | succ s =>
      by_contra hbad
      have : 4 ∣ 2*m := hval ▸ Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 (by omega : 2 ≤ s+1)) d
      obtain ⟨a, ha⟩ := this
      obtain ⟨b, hb⟩ := hm
      omega
  subst s
  have hdm : d = m := by simp only [pow_one] at hval; omega
  subst d
  rcases h with h | ⟨r, hr, h⟩
  · left
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  · right
    have hr0 : r = 0 := by omega
    subst r
    simpa using (ZMod.intCast_eq_intCast_iff _ _ _).mpr h

/-- The sign test already holds at the proper divisor given by the order of four. -/
theorem compressed_sign {n m : ℕ} (hn : n = 2*m+1) (hm : 1 < m) (ho : Odd m)
    (hc : ¬ n.Prime) (hs : StrongProbablePrime n) :
    ∃ d, 1 < d ∧ d ∣ m ∧ d < m ∧ ((2 : ZMod n)^d = 1 ∨ (2 : ZMod n)^d = -1) := by
  have hsign := strong_sign hs hn ho
  have square : (4 : ZMod n)^m = 1 := by
    rw [show (4 : ZMod n) = 2^2 by norm_num, ← pow_mul, Nat.mul_comm, pow_mul]
    rcases hsign with e | e <;> rw [e] <;> norm_num
  let d := orderOf (4 : ZMod n)
  obtain ⟨hd, hdiv, hlt⟩ := proper_order hn hm hc square
  refine ⟨d, hd, hdiv, hlt, ?_⟩
  change d ∣ m at hdiv
  obtain ⟨u,hu⟩ := hdiv
  obtain ⟨v,hv⟩ := (Nat.odd_mul.mp (hu ▸ ho)).2
  have orderSquare : ((2 : ZMod n)^d)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, show (2 : ZMod n)^2 = 4 by norm_num]
    exact pow_orderOf_eq_one _
  have eqpow : (2 : ZMod n)^m = (2 : ZMod n)^d := by
    rw [hu, pow_mul, hv, pow_add, pow_mul, orderSquare, one_pow, pow_one, one_mul]
  rwa [eqpow] at hsign

private theorem residue_at_involution {M : Type*} [Monoid M] {a : M} {k : ℕ}
    (hsq : a^(2*k) = 1) (hne : a^k ≠ 1) :
    2*(k % orderOf a) = orderOf a := by
  let t := orderOf a
  have div2 : t ∣ 2*k := orderOf_dvd_of_pow_eq_one hsq
  have hk : k ≠ 0 := by rintro rfl; simp at hne
  have ht := Nat.pos_of_dvd_of_pos div2 (by omega : 0 < 2*k)
  have hlt := Nat.mod_lt k ht
  have hrem : k%t ≠ 0 := fun h => hne (orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_of_mod_eq_zero h))
  have hz := Nat.mod_eq_zero_of_dvd div2
  rw [two_mul, Nat.add_mod] at hz
  change 2*(k%t) = t
  by_cases hsmall : k%t+k%t < t
  · rw [Nat.mod_eq_of_lt hsmall] at hz; omega
  · rw [Nat.mod_eq_sub_mod (by omega : t ≤ k%t+k%t),
        Nat.mod_eq_of_lt (by omega : k%t+k%t-t < t)] at hz
    omega

/-- A base-two strong probable prime admits only the two trivial square roots
of one among the powers of two. -/
private theorem strong_root {m k : ℕ} (hm : 2 < m) (hs : StrongProbablePrime m)
    (hpow : (2 : ZMod m)^(2*k) = 1) : (2 : ZMod m)^k = 1 ∨ (2 : ZMod m)^k = -1 := by
  by_cases hpos : (2 : ZMod m)^k = 1
  · exact Or.inl hpos
  rcases hs with h | ⟨_, d, s, hd, _, h | ⟨r, _, h⟩⟩
  · omega
  · have he : (2 : ZMod m)^d = 1 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    obtain ⟨v,hv⟩ := hd
    have h1 : ((2 : ZMod m)^k)^2 = 1 := by rwa [← pow_mul, Nat.mul_comm k]
    have h2 : ((2 : ZMod m)^k)^d = 1 := by rw [← pow_mul, Nat.mul_comm k, pow_mul, he, one_pow]
    rw [hv, pow_add, pow_mul, h1, one_pow, pow_one, one_mul] at h2
    exact (hpos h2).elim
  · right
    let j := d*2^r
    have hj : (2 : ZMod m)^j = -1 := by simpa [j] using (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
    have hsquare : (2 : ZMod m)^(2*j) = 1 := by rw [Nat.mul_comm 2, pow_mul, hj]; norm_num
    have hn : (2 : ZMod m)^j ≠ 1 := by
      rw [hj]
      intro e
      have hz : (2 : ZMod m) = 0 := by linear_combination -e
      have hdiv : m ∣ 2 := (ZMod.natCast_eq_zero_iff 2 m).mp (by simpa using hz)
      have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
      omega
    have h1 := residue_at_involution hpow hpos
    have h2 := residue_at_involution hsquare hn
    have hrem : k % orderOf (2 : ZMod m) = j % orderOf (2 : ZMod m) := by omega
    rw [← pow_mod_orderOf (2 : ZMod m) k, hrem, pow_mod_orderOf, hj]

private theorem half_power_bound {m k : ℕ} (hm : 2 < m) (hk : 0 < k)
    (hs : StrongProbablePrime m) (hd : m ∣ 2^(2*k)-1) : m ≤ 2^k+1 := by
  have hp : 1 ≤ (2:ℕ)^(2*k) := Nat.one_le_pow _ _ (by decide)
  have eqm : 2^(2*k) ≡ 1 [MOD m] := (Nat.modEq_iff_dvd' hp).mpr hd |>.symm
  have hpow : (2 : ZMod m)^(2*k) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr eqm
  rcases strong_root hm hs hpow with h | h
  · have eq1 : 2^k ≡ 1 [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using h)
    have hgt : 1 < (2:ℕ)^k := Nat.one_lt_two_pow (by omega)
    have hdiv := (Nat.modEq_iff_dvd' hgt.le).mp eq1.symm
    have := Nat.le_of_dvd (by omega : 0 < 2^k-1) hdiv
    omega
  · have hz : (((2^k+1 : ℕ) : ZMod m)) = 0 := by push_cast; rw [h]; simp
    exact Nat.le_of_dvd (by positivity) ((ZMod.natCast_eq_zero_iff _ _).mp hz)


private theorem small_complement_impossible {m k a : ℕ} (hk : 0 < k) (hl : 2*k+1 < m)
    (hs : StrongProbablePrime m) (ha : a = 1 ∨ a = 3)
    (he : (2^k : ℕ)^2 = a*m+1) : False := by
  have hpow : (2 : ℕ)^(2*k) = (2^k)^2 := by rw [Nat.mul_comm 2 k, pow_mul]
  have hd : m ∣ 2^(2*k)-1 := ⟨a, by rw [hpow, he, Nat.mul_comm a]; omega⟩
  have hbound := half_power_bound (by omega : 2 < m) hk hs hd
  have hupper : (2^k : ℕ)^2 ≤ 3*(2^k)+4 := by
    rcases ha with rfl | rfl
    · rw [Nat.one_mul] at he
      omega
    · omega
  have hle : (2:ℕ)^k ≤ 4 := by
    by_contra! h
    have hsq := Nat.mul_le_mul_right (2^k) (by omega : 5 ≤ 2^k)
    nlinarith only [hsq, hupper, h]
  have eq1 : k = 1 := by omega
  subst k
  norm_num at hbound hl
  omega

theorem positive_cofactor {d m : ℕ} (hd : 1 < d) (ho : Odd d) (hl : d < m)
    (hs : StrongProbablePrime m) (div : 2*m+1 ∣ 2^d-1) : 3*(2*m+1) ≤ 2^d-1 := by
  obtain ⟨k, rfl⟩ := ho
  obtain ⟨c, hc⟩ := div
  have hp : (2:ℕ)^(2*k+1) = 2*(2^k)^2 := by rw [pow_succ, Nat.mul_comm 2 k, pow_mul]; ring
  rw [hp] at hc ⊢
  by_contra! bad
  have csmall : c < 3 := by
    by_contra! h
    have hmul := Nat.mul_le_mul_left (2*m+1) h
    omega
  have pp : 0 < (2^k : ℕ)^2 := by positivity
  interval_cases c <;> try simp only [Nat.mul_zero, Nat.mul_one] at hc
  · omega
  · exact small_complement_impossible (by omega) hl hs (Or.inl rfl : 1 = 1 ∨ 1 = 3)
      (by omega)
  · omega

theorem negative_cofactor {d m : ℕ} (hd : 1 < d) (ho : Odd d) (hl : d < m)
    (hs : StrongProbablePrime m) (div : 2*m+1 ∣ 2^d+1) : 5*(2*m+1) ≤ 2^d+1 := by
  obtain ⟨k, rfl⟩ := ho
  obtain ⟨c, hc⟩ := div
  have hk : 0 < k := by omega
  have hp : (2:ℕ)^(2*k+1) = 2*(2^k)^2 := by rw [pow_succ, Nat.mul_comm 2 k, pow_mul]; ring
  rw [hp] at hc ⊢
  by_contra! bad
  have csmall : c < 5 := by
    by_contra! h
    have hmul := Nat.mul_le_mul_left (2*m+1) h
    omega
  interval_cases c <;> try simp only [Nat.mul_zero, Nat.mul_one] at hc
  · omega
  · have hm : m = (2^k)^2 := by omega
    have dv : 2 ∣ m := hm ▸ dvd_pow (dvd_pow_self 2 (by omega : k ≠ 0)) (by decide : 2 ≠ 0)
    exact (strong_odd hs (by omega)).not_two_dvd_nat dv
  · omega
  · exact small_complement_impossible hk hl hs (Or.inr rfl : 3 = 1 ∨ 3 = 3) (by omega)
  · omega


/-- Positive sign. The number 2du+1 is a factor of a Mersenne number,
and its complementary factor is at least three. -/
def H1 : Prop :=
  ∀ d u c : ℕ, 1 < d → Odd d → 3 ≤ u → Odd u → 3 ≤ c →
    2^d - 1 = (2*(d*u)+1)*c →
    OMA.S_mo_296166.StrongProbablePrime (d*u) → (2*(d*u)+1).Prime

/-- Negative sign. The complementary factor of 2^d+1 is at least five. -/
def H2 : Prop :=
  ∀ d u c : ℕ, 1 < d → Odd d → 3 ≤ u → Odd u → 5 ≤ c →
    2^d + 1 = (2*(d*u)+1)*c →
    OMA.S_mo_296166.StrongProbablePrime (d*u) → (2*(d*u)+1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_mo_296166.main := by
  intro positive negative n hn hs hm
  obtain ⟨m, hn⟩ := hn
  have hq : (n-1)/2 = m := by omega
  rw [hq] at hm
  by_cases hsmall : m ≤ 2
  · interval_cases m
    · rcases hm with h | ⟨h,_⟩ <;> omega
    · rw [hn]; decide
    · rw [hn]; decide
  by_contra composite
  have om := strong_odd hm (by omega)
  obtain ⟨d, hd, div, hlt, hsigned⟩ := compressed_sign hn (by omega) om composite hs
  obtain ⟨u, hu⟩ := div
  obtain ⟨od, ou⟩ := Nat.odd_mul.mp (hu ▸ om)
  have hu3 : 3 ≤ u := by
    by_contra! h
    have : u = 1 := by obtain ⟨k,hk⟩ := ou; omega
    simp [this] at hu
    omega
  have hnPos : 0 < 2*m+1 := by omega
  rcases hsigned with plus | minus
  · have congr : 2^d ≡ 1 [MOD n] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using plus)
    have div := (Nat.modEq_iff_dvd' (Nat.one_le_pow d 2 (by decide))).mp congr.symm
    rw [hn] at div
    have bound := positive_cofactor hd od hlt hm div
    obtain ⟨c,hc⟩ := div
    rw [hc, Nat.mul_comm 3] at bound
    have lower := Nat.le_of_mul_le_mul_left bound hnPos
    apply composite
    rw [hn, hu]
    exact positive d u c hd od hu3 ou lower (hu ▸ hc) (hu ▸ hm)
  · have hz : (((2^d + 1 : ℕ) : ZMod n)) = 0 := by push_cast; rw [minus]; simp
    have div := (ZMod.natCast_eq_zero_iff _ _).mp hz
    rw [hn] at div
    have bound := negative_cofactor hd od hlt hm div
    obtain ⟨c,hc⟩ := div
    rw [hc, Nat.mul_comm 5] at bound
    have lower := Nat.le_of_mul_le_mul_left bound hnPos
    apply composite
    rw [hn, hu]
    exact negative d u c hd od hu3 ou lower (hu ▸ hc) (hu ▸ hm)

end OMA.R_mo_296166_R1
