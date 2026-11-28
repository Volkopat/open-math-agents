import OMAStatements.S_oeis_a227877

namespace OMA.S_oeis_a227877

/-! ## The statement -/



/-- The condition counted by `a n`, for the triple `(x, y, z)`. -/
def IsSol (n x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧ IsTriangular (x * y) ∧ IsTriangular (x * z) ∧
    (6 * y - 1).Prime ∧ (6 * z + 1).Prime

theorem a_eq_zero_of {n : ℕ} (h : ∀ x y z, ¬ IsSol n x y z) : a n = 0 := by
  have hset : {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧
      IsTriangular (t.1 * t.2.1) ∧ IsTriangular (t.1 * t.2.2) ∧
      (6 * t.2.1 - 1).Prime ∧ (6 * t.2.2 + 1).Prime} = ∅ := by
    ext ⟨x, y, z⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact h x y z
  rw [a, hset, Set.ncard_empty]

theorem isTriangular_iff (t : ℕ) : IsTriangular t ↔ ∃ r, r * r = 8 * t + 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    have h := Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_succ_self k))
    exact ⟨2 * k + 1, by nlinarith [h]⟩
  · rintro ⟨r, hr⟩
    have hodd : r % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one r with h | h
      · have : r * r % 2 = 0 := by rw [Nat.mul_mod, h]
        omega
      · exact h
    obtain ⟨k, rfl⟩ : ∃ k, r = 2 * k + 1 := ⟨r / 2, by omega⟩
    refine ⟨k, ?_⟩
    have : k * (k + 1) = 2 * t := by nlinarith [hr]
    omega

/-- Every solution puts a lattice point on the circle `s² + r² = 8x(n - x) + 2`. -/
theorem circle {n x y z : ℕ} (h : IsSol n x y z) :
    ∃ s r : ℕ, 8 * x * (n - x) + 2 = s ^ 2 + r ^ 2 := by
  obtain ⟨-, -, -, hsum, hty, htz, -, -⟩ := h
  obtain ⟨s, hs⟩ := (isTriangular_iff _).mp hty
  obtain ⟨r, hr⟩ := (isTriangular_iff _).mp htz
  refine ⟨s, r, ?_⟩
  rw [show n - x = y + z by omega, sq, sq, hs, hr]
  ring

/-! ## Sums of two squares -/

theorem sq_mod_four (x : ℕ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; ring_nf; omega
  · right; ring_nf; omega

/-- A factor `Q ≡ 3 (mod 4)` of `M` coprime to its cofactor rules out `M = x² + y²`. -/
theorem not_sos_of_witness {M Q : ℕ} (hM : 0 < M) (hQ : Q % 4 = 3) (hdvd : Q ∣ M)
    (hcop : Nat.Coprime Q (M / Q)) : ¬ ∃ x y, M = x ^ 2 + y ^ 2 := by
  intro hsos
  have hQnot : ¬ ∃ x y, Q = x ^ 2 + y ^ 2 := by
    rintro ⟨x, y, h⟩
    rcases sq_mod_four x with hx | hx <;> rcases sq_mod_four y with hy | hy <;> omega
  have hex : ¬ ∀ q ∈ Q.primeFactors, q % 4 = 3 → Even (padicValNat q Q) :=
    fun h => hQnot (Nat.eq_sq_add_sq_iff.mpr h)
  push_neg at hex
  obtain ⟨q, hq, hq4, hodd⟩ := hex
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqQ : q ∣ Q := Nat.dvd_of_mem_primeFactors hq
  have hQ0 : 0 < Q := by omega
  have hM' : M = Q * (M / Q) := (Nat.mul_div_cancel' hdvd).symm
  have hc0 : 0 < M / Q := Nat.div_pos (Nat.le_of_dvd hM hdvd) hQ0
  have hndvd : ¬ q ∣ M / Q := by
    intro h
    have h1 : Nat.Coprime q (M / Q) := Nat.Coprime.coprime_dvd_left hqQ hcop
    have h2 : q ∣ Nat.gcd q (M / Q) := Nat.dvd_gcd dvd_rfl h
    rw [h1] at h2
    exact hqp.one_lt.ne' (Nat.eq_one_of_dvd_one h2)
  have hval : padicValNat q M = padicValNat q Q := by
    have := Fact.mk hqp
    rw [hM', padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd hndvd, add_zero]
  have hqM : q ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, dvd_trans hqQ hdvd, by omega⟩
  have := (Nat.eq_sq_add_sq_iff.mp hsos) q hqM hq4
  rw [hval] at this
  exact hodd this

/-- A prime `q ≡ 3 (mod 4)` dividing `M` exactly once rules out `M = x² + y²`. -/
theorem not_sos_of_prime {M q : ℕ} (hM : 0 < M) (hq : q.Prime) (hq4 : q % 4 = 3) (hdvd : q ∣ M)
    (hsq : ¬ q * q ∣ M) : ¬ ∃ x y, M = x ^ 2 + y ^ 2 := by
  apply not_sos_of_witness hM hq4 hdvd
  apply (Nat.Prime.coprime_iff_not_dvd hq).mpr
  intro h
  apply hsq
  obtain ⟨c, hc⟩ := h
  have hM' : M = q * (M / q) := (Nat.mul_div_cancel' hdvd).symm
  exact ⟨c, by rw [hM', hc]; ring⟩

/-! ## Combs of a given length -/

/-- `combL len q fuel c s` doubles a comb `c` whose teeth are `q * t` for `t < s` until
`len ≤ q * s`. -/
def combL (len q : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, c, _ => c
  | fuel + 1, c, s =>
    cond (Nat.ble len (q * s)) c (combL len q fuel (c ||| (c <<< (q * s))) (2 * s))

theorem combL_spec (len q : ℕ) : ∀ fuel c s, len ≤ q * s * 2 ^ fuel →
    (∀ j, c.testBit j = true ↔ ∃ t, t < s ∧ j = q * t) →
    ∃ s', len ≤ q * s' ∧ ∀ j, (combL len q fuel c s).testBit j = true ↔
      ∃ t, t < s' ∧ j = q * t := by
  intro fuel
  induction fuel with
  | zero =>
    intro c s hL hc
    exact ⟨s, by simpa using hL, by simpa [combL] using hc⟩
  | succ fuel ih =>
    intro c s hL hc
    by_cases hs : len ≤ q * s
    · have hb : Nat.ble len (q * s) = true := Nat.ble_eq.mpr hs
      refine ⟨s, hs, ?_⟩
      simp only [combL, hb, cond_true]
      exact hc
    · have hb : Nat.ble len (q * s) = false := by
        cases h : Nat.ble len (q * s)
        · rfl
        · exact absurd (Nat.ble_eq.mp h) hs
      simp only [combL, hb, cond_false]
      apply ih
      · calc len ≤ q * s * 2 ^ (fuel + 1) := hL
          _ = q * (2 * s) * 2 ^ fuel := by ring
      · intro j
        rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_iff, hc, hc]
        constructor
        · rintro (⟨t, ht, rfl⟩ | ⟨hj, t, ht, hjt⟩)
          · exact ⟨t, by omega, rfl⟩
          · refine ⟨s + t, by omega, ?_⟩
            have e : q * (s + t) = q * s + q * t := by ring
            omega
        · rintro ⟨t, ht, rfl⟩
          by_cases hts : t < s
          · exact Or.inl ⟨t, hts, rfl⟩
          · right
            obtain ⟨u, rfl⟩ : ∃ u, t = s + u := ⟨t - s, by omega⟩
            have e : q * (s + u) = q * s + q * u := by ring
            exact ⟨by omega, u, by omega, by omega⟩

/-- The comb of `q` of length `len`: teeth `q * t` for all `t` with `q * t < len`. -/
def combOfL (len q : ℕ) : ℕ := combL len q 24 1 1 &&& (2 ^ len - 1)

theorem combOfL_spec {len q : ℕ} (hq : 0 < q) (hlen : len ≤ 2 ^ 24) (j : ℕ) :
    (combOfL len q).testBit j = true ↔ ∃ t, q * t < len ∧ j = q * t := by
  have h1 : ∀ j, (1 : ℕ).testBit j = true ↔ ∃ t, t < 1 ∧ j = q * t := by
    intro j
    rw [Nat.testBit_one_eq_true_iff_self_eq_zero]
    constructor
    · rintro rfl; exact ⟨0, by omega, by simp⟩
    · rintro ⟨t, ht, rfl⟩
      obtain rfl : t = 0 := by omega
      simp
  have hL : len ≤ q * 1 * 2 ^ 24 := by
    calc len ≤ 2 ^ 24 := hlen
      _ ≤ q * 1 * 2 ^ 24 := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨s', hs', hc⟩ := combL_spec len q 24 1 1 hL h1
  rw [combOfL, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, hc,
    decide_eq_true_iff]
  constructor
  · rintro ⟨⟨t, _, rfl⟩, hlt⟩
    exact ⟨t, hlt, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ?_, rfl⟩, ht⟩
    by_contra hts
    have : q * s' ≤ q * t := Nat.mul_le_mul_left q (by omega)
    omega

/-- The offset of the first `j` with `(x0 + j) % m = r`. -/
def offs (x0 m r : ℕ) : ℕ := (r + m - x0 % m) % m

theorem offs_mod {x0 m r : ℕ} (hm : 0 < m) (hr : r < m) : (x0 + offs x0 m r) % m = r := by
  have hu := Nat.mod_lt x0 hm
  have hd := Nat.mod_add_div x0 m
  unfold offs
  by_cases h : x0 % m ≤ r
  · rw [show r + m - x0 % m = (r - x0 % m) + m * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (show r - x0 % m < m by omega)]
    rw [show x0 + (r - x0 % m) = r + m * (x0 / m) by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hr]
  · rw [Nat.mod_eq_of_lt (show r + m - x0 % m < m by omega)]
    rw [show x0 + (r + m - x0 % m) = r + m * (x0 / m + 1) by rw [Nat.mul_add]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

theorem offs_lt {x0 m r : ℕ} (hm : 0 < m) : offs x0 m r < m := Nat.mod_lt _ hm

/-- The bits `j < len` with `(x0 + j) % m = r` (none when the first such `j` is past `len`, which
also keeps the shift small). -/
def cls (len x0 m r : ℕ) : ℕ :=
  cond (Nat.blt (offs x0 m r) len) ((combOfL len m <<< offs x0 m r) &&& (2 ^ len - 1)) 0

theorem cls_spec {len x0 m r : ℕ} (hm : 0 < m) (hr : r < m) (hlen : len ≤ 2 ^ 24) (j : ℕ) :
    (cls len x0 m r).testBit j = true ↔ j < len ∧ (x0 + j) % m = r := by
  have ho := offs_mod (x0 := x0) hm hr
  have hol := offs_lt (x0 := x0) (r := r) hm
  by_cases hbig : offs x0 m r < len
  swap
  · have hb : Nat.blt (offs x0 m r) len = false := by
      cases h : Nat.blt (offs x0 m r) len
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hbig
    rw [cls, hb, cond_false, Nat.zero_testBit]
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro hj hjr
    have h1 : (x0 + j) % m = (x0 + offs x0 m r) % m := by rw [hjr, ho]
    have h2 : j ≡ offs x0 m r [MOD m] := Nat.ModEq.add_left_cancel' x0 h1
    have h3 : j % m = offs x0 m r := by rw [h2, Nat.mod_eq_of_lt hol]
    have h4 : j % m ≤ j := Nat.mod_le j m
    omega
  rw [cls, show Nat.blt (offs x0 m r) len = true from Nat.blt_eq.mpr hbig, cond_true]
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_iff,
    Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff, combOfL_spec hm hlen]
  constructor
  · rintro ⟨⟨hj, t, ht, hjt⟩, hlen'⟩
    refine ⟨hlen', ?_⟩
    rw [show x0 + j = (x0 + offs x0 m r) + m * t by omega, Nat.add_mul_mod_self_left, ho]
  · rintro ⟨hj, hjr⟩
    have hmod : j % m = offs x0 m r := by
      have h1 : (x0 + j) % m = (x0 + offs x0 m r) % m := by rw [hjr, ho]
      have h2 : j ≡ offs x0 m r [MOD m] := Nat.ModEq.add_left_cancel' x0 h1
      rw [h2, Nat.mod_eq_of_lt hol]
    have hdj := Nat.mod_add_div j m
    refine ⟨⟨by omega, j / m, by
      have : m * (j / m) ≤ j := Nat.mul_div_le j m
      omega, by omega⟩, hj⟩

/-! ## Witness combs

For a prime `q ≡ 3 (mod 4)`, the roots `r` of `F(x) = 8x(n - x) + 2` modulo `q` and their lifts `s`
modulo `q²` give the `x` with `v_q(F(x)) = 1`: `x ≡ r (mod q)` and `x ≢ s (mod q²)`. -/

def wq (len x0 q r1 r2 s1 s2 : ℕ) : ℕ :=
  (cls len x0 q r1 ||| cls len x0 q r2) &&&
    ((2 ^ len - 1) ^^^ (cls len x0 (q * q) s1 ||| cls len x0 (q * q) s2))

theorem wq_spec {len x0 q r1 r2 s1 s2 : ℕ} (hq : 0 < q) (h1 : r1 < q) (h2 : r2 < q)
    (h3 : s1 < q * q) (h4 : s2 < q * q) (hlen : len ≤ 2 ^ 24) (j : ℕ)
    (hw : (wq len x0 q r1 r2 s1 s2).testBit j = true) :
    j < len ∧ ((x0 + j) % q = r1 ∨ (x0 + j) % q = r2) ∧
      (x0 + j) % (q * q) ≠ s1 ∧ (x0 + j) % (q * q) ≠ s2 := by
  have hqq : 0 < q * q := Nat.mul_pos hq hq
  rw [wq, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true] at hw
  obtain ⟨hA, hB⟩ := hw
  rw [cls_spec hq h1 hlen, cls_spec hq h2 hlen] at hA
  have hj : j < len := by rcases hA with h | h <;> exact h.1
  refine ⟨hj, by rcases hA with h | h; exact Or.inl h.2; exact Or.inr h.2, ?_, ?_⟩
  · intro he
    have : (cls len x0 (q * q) s1).testBit j = true := (cls_spec hqq h3 hlen j).mpr ⟨hj, he⟩
    simp [this, hj] at hB
  · intro he
    have : (cls len x0 (q * q) s2).testBit j = true := (cls_spec hqq h4 hlen j).mpr ⟨hj, he⟩
    simp [this, hj] at hB

/-- `t` is a root of `F(x) = 8x(n - x) + 2` modulo `m`, stated without subtraction. -/
def isRoot (n m t : ℕ) : Bool := Nat.beq ((8 * t * n + 2) % m) ((8 * t * t) % m)

theorem F_int {n x : ℕ} (hx : x ≤ n) :
    ((8 * x * (n - x) + 2 : ℕ) : ℤ) = 8 * (x : ℤ) * ((n : ℤ) - x) + 2 := by
  push_cast [Nat.cast_sub hx]
  ring

theorem isRoot_int {n m t : ℕ} (h : isRoot n m t = true) :
    (m : ℤ) ∣ 8 * (t : ℤ) * ((n : ℤ) - t) + 2 := by
  simp only [isRoot, Nat.beq_eq] at h
  have h1 : (8 * t * n + 2 : ℕ) ≡ 8 * t * t [MOD m] := h
  have h2 := (Nat.modEq_iff_dvd.mp h1.symm)
  push_cast at h2
  have : 8 * (t : ℤ) * ((n : ℤ) - t) + 2 = (8 * t * n + 2) - 8 * t * t := by ring
  rw [this]
  exact h2

/-- A checked witness entry: `q` prime, `q ≡ 3 (mod 4)`, roots `r1, r2` and lifts `s1, s2`, and
`n ≢ 2r (mod q)`. -/
def entryOK (n : ℕ) (q r1 r2 s1 s2 : ℕ) (qprime : Bool) : Bool :=
  qprime && Nat.beq (q % 4) 3 && Nat.blt r1 q && Nat.blt r2 q && Nat.blt s1 (q * q) &&
    Nat.blt s2 (q * q) && Nat.beq (s1 % q) r1 && Nat.beq (s2 % q) r2 &&
    isRoot n q r1 && isRoot n q r2 && isRoot n (q * q) s1 && isRoot n (q * q) s2 &&
    !(Nat.beq (n % q) ((2 * r1) % q)) && !(Nat.beq (n % q) ((2 * r2) % q))

theorem int_sq_dvd {q : ℕ} (hq : q.Prime) {u v : ℤ} (h : ((q * q : ℕ) : ℤ) ∣ u * v)
    (hv : ¬ (q : ℤ) ∣ v) : ((q * q : ℕ) : ℤ) ∣ u := by
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hc : IsCoprime (q : ℤ) v := (Prime.coprime_iff_not_dvd hp).mpr hv
  have hcop : IsCoprime ((q * q : ℕ) : ℤ) v := by
    push_cast
    exact IsCoprime.mul_left hc hc
  exact hcop.dvd_of_dvd_mul_right h

/-- A checked entry and a set bit of its comb give `v_q(F(x)) = 1`, so `F(x)` is not a sum of two
squares. -/
theorem entry_witness {n len x0 q r1 r2 s1 s2 : ℕ} (hq : q.Prime)
    (he : entryOK n q r1 r2 s1 s2 true = true) (hlen : len ≤ 2 ^ 24) (j : ℕ)
    (hw : (wq len x0 q r1 r2 s1 s2).testBit j = true) (hx : x0 + j ≤ n) :
    ¬ ∃ s r : ℕ, 8 * (x0 + j) * (n - (x0 + j)) + 2 = s ^ 2 + r ^ 2 := by
  simp only [entryOK, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, Nat.blt_eq,
    Bool.true_and] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hq4, hr1⟩, hr2⟩, hs1⟩, hs2⟩, hs1r⟩, hs2r⟩, hR1⟩, hR2⟩, hS1⟩, hS2⟩, hn1⟩,
    hn2⟩ := he
  have hq0 := hq.pos
  obtain ⟨-, hroot, hne1, hne2⟩ := wq_spec hq0 hr1 hr2 hs1 hs2 hlen j hw
  set x := x0 + j with hxdef
  have hM : 0 < 8 * x * (n - x) + 2 := by omega
  -- the root `r` and its lift `s` for the residue of `x`
  obtain ⟨r, s, hxr, hR, hS, hsr, hnr, hsne, hslt⟩ : ∃ r s, x % q = r ∧ isRoot n q r = true ∧
      isRoot n (q * q) s = true ∧ s % q = r ∧ n % q ≠ (2 * r) % q ∧ x % (q * q) ≠ s ∧
      s < q * q := by
    rcases hroot with h | h
    · exact ⟨r1, s1, h, hR1, hS1, hs1r, Nat.ne_of_beq_eq_false hn1, hne1, hs1⟩
    · exact ⟨r2, s2, h, hR2, hS2, hs2r, Nat.ne_of_beq_eq_false hn2, hne2, hs2⟩
  apply not_sos_of_prime hM hq hq4
  · -- q ∣ F(x)
    have hFr := isRoot_int hR
    have hdiff : (q : ℤ) ∣ (8 * (x : ℤ) * ((n : ℤ) - x) + 2) - (8 * (r : ℤ) * ((n : ℤ) - r) + 2) := by
      have hxr' : (q : ℤ) ∣ (x : ℤ) - r := by
        have : x ≡ r [MOD q] := by
          show x % q = r % q
          rw [hxr, Nat.mod_eq_of_lt (by rw [← hxr]; exact Nat.mod_lt _ hq0)]
        exact (Nat.modEq_iff_dvd.mp this.symm)
      have : (8 * (x : ℤ) * ((n : ℤ) - x) + 2) - (8 * (r : ℤ) * ((n : ℤ) - r) + 2) =
          ((x : ℤ) - r) * (8 * ((n : ℤ) - x - r)) := by ring
      rw [this]
      exact Dvd.dvd.mul_right hxr' _
    have : (q : ℤ) ∣ ((8 * x * (n - x) + 2 : ℕ) : ℤ) := by
      rw [F_int hx]
      have e : 8 * (x : ℤ) * ((n : ℤ) - x) + 2 =
          ((8 * (x : ℤ) * ((n : ℤ) - x) + 2) - (8 * (r : ℤ) * ((n : ℤ) - r) + 2)) +
            (8 * (r : ℤ) * ((n : ℤ) - r) + 2) := by ring
      rw [e]
      exact dvd_add hdiff hFr
    exact_mod_cast this
  · -- ¬ q² ∣ F(x)
    intro hdvd
    have hFs := isRoot_int hS
    have hFx : ((q * q : ℕ) : ℤ) ∣ 8 * (x : ℤ) * ((n : ℤ) - x) + 2 := by
      rw [← F_int hx]
      exact_mod_cast hdvd
    have hdiff : ((q * q : ℕ) : ℤ) ∣ ((x : ℤ) - s) * (8 * ((n : ℤ) - x - s)) := by
      have : ((x : ℤ) - s) * (8 * ((n : ℤ) - x - s)) =
          (8 * (x : ℤ) * ((n : ℤ) - x) + 2) - (8 * (s : ℤ) * ((n : ℤ) - s) + 2) := by ring
      rw [this]
      exact dvd_sub hFx hFs
    have hnot : ¬ (q : ℤ) ∣ 8 * ((n : ℤ) - x - s) := by
      intro h
      have hp := Nat.prime_iff_prime_int.mp hq
      rcases hp.dvd_or_dvd h with h8 | h8
      · have h8' : q ∣ 2 ^ 3 := by
          have : q ∣ 8 := by exact_mod_cast h8
          simpa using this
        have h2 : q ∣ 2 := hq.dvd_of_dvd_pow h8'
        have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
        omega
      · -- n - x - s ≡ n - 2r (mod q)
        apply hnr
        have hx' : (q : ℤ) ∣ (x : ℤ) - r := by
          have : x ≡ r [MOD q] := by
            show x % q = r % q
            rw [hxr, Nat.mod_eq_of_lt (by rw [← hxr]; exact Nat.mod_lt _ hq0)]
          exact (Nat.modEq_iff_dvd.mp this.symm)
        have hs' : (q : ℤ) ∣ (s : ℤ) - r := by
          have : s ≡ r [MOD q] := by
            show s % q = r % q
            rw [hsr, Nat.mod_eq_of_lt (by rw [← hsr]; exact Nat.mod_lt _ hq0)]
          exact (Nat.modEq_iff_dvd.mp this.symm)
        have h3 : (q : ℤ) ∣ (n : ℤ) - (2 * r : ℕ) := by
          have : (n : ℤ) - (2 * r : ℕ) = ((n : ℤ) - x - s) + ((x : ℤ) - r) + ((s : ℤ) - r) := by
            push_cast; ring
          rw [this]
          exact dvd_add (dvd_add h8 hx') hs'
        have h4 : (2 * r : ℕ) ≡ n [MOD q] := (Nat.modEq_iff_dvd.mpr h3)
        exact h4.symm
    have hu := int_sq_dvd hq hdiff hnot
    have h5 : s ≡ x [MOD q * q] := Nat.modEq_iff_dvd.mpr hu
    apply hsne
    have h6 : s % (q * q) = x % (q * q) := h5
    rw [← h6, Nat.mod_eq_of_lt hslt]

/-! ## The witness bitmap of a block -/

/-- One witness entry: `(q, r1, r2, s1, s2)`. -/
def wBlock (len x0 : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | e :: es => wq len x0 e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 ||| wBlock len x0 es

theorem wBlock_spec (len x0 : ℕ) : ∀ (es : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (j : ℕ),
    (wBlock len x0 es).testBit j = true →
      ∃ e ∈ es, (wq len x0 e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2).testBit j = true := by
  intro es
  induction es with
  | nil => intro j h; simp [wBlock] at h
  | cons e es ih =>
    intro j h
    rw [wBlock, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self .., h⟩
    · obtain ⟨e', he', h'⟩ := ih j h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

/-! ## Squares and primes -/

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hc : Nat.beq a b
  · rfl
  · exact absurd (Nat.beq_eq.mp hc) h

theorem blt_false_of_not {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hc : Nat.blt a b
  · rfl
  · exact absurd (Nat.blt_eq.mp hc) h

/-! The hot functions below call `Nat.add`, `Nat.mul`, ... directly: the kernel evaluates these on
literals at once, while `+`, `*`, ... first unfold their instances (about five times slower in a
measured loop). The proofs turn them back into notation with these lemmas. The hot loops are
written with `Nat.rec` and `List.rec`, which the kernel runs about twice as fast as the compiled
form of a recursive definition (measured). -/

theorem nadd (a b : ℕ) : Nat.add a b = a + b := rfl
theorem nmul (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem nsub (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem ndiv (a b : ℕ) : Nat.div a b = a / b := rfl
theorem nmod (a b : ℕ) : Nat.mod a b = a % b := rfl
theorem npow (a b : ℕ) : Nat.pow a b = a ^ b := rfl

def qrCheck (QRM : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, k => Nat.testBit QRM (k * k % 45045) && qrCheck QRM n (k + 1)

theorem qrCheck_spec (QRM : ℕ) : ∀ n k, qrCheck QRM n k = true →
    ∀ j, k ≤ j → j < k + n → Nat.testBit QRM (j * j % 45045) = true := by
  intro n
  induction n with
  | zero => intro k _ j h1 h2; omega
  | succ n ih =>
    intro k h j h1 h2
    simp only [qrCheck, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih (k + 1) h.2 j (by omega) (by omega)

def isqF : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | fuel + 1, v, g => cond (Nat.blt ((g + v / g) / 2) g) (isqF fuel v ((g + v / g) / 2)) g

/-- A square root guess (Newton from `2 ^ 23`); `sqB` checks its result. -/
def isq (v : ℕ) : ℕ := isqF 40 v 8388608

def slowSq (v : ℕ) : Bool := (List.range (v + 1)).any (fun r => Nat.beq (r * r) v)

/-- `v` is a perfect square: a residue filter modulo 45045, then the guess `isq v` checked
exactly. (Two machine-word filters, modulo 64 and 63, measured slower and needed more memory.) -/
def sqB (QRM v : ℕ) : Bool :=
  Nat.testBit QRM (Nat.mod v 45045) &&
    cond (Nat.beq (isq v * isq v) v) true
      (cond (Nat.ble (isq v * isq v) v && Nat.blt v ((isq v + 1) * (isq v + 1))) false (slowSq v))

theorem sqB_iff {QRM : ℕ} (hQ : ∀ k, k < 45045 → Nat.testBit QRM (k * k % 45045) = true) (v : ℕ) :
    sqB QRM v = true ↔ ∃ r, r * r = v := by
  constructor
  · intro h
    simp only [sqB, Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    by_cases h1 : isq v * isq v = v
    · exact ⟨isq v, h1⟩
    · rw [beq_false_of_ne h1, cond_false] at h
      by_cases h2 : (Nat.ble (isq v * isq v) v && Nat.blt v ((isq v + 1) * (isq v + 1))) = true
      · rw [h2, cond_true] at h
        exact absurd h (by simp)
      · rw [Bool.eq_false_iff.mpr h2, cond_false] at h
        simp only [slowSq, List.any_eq_true, List.mem_range, Nat.beq_eq] at h
        obtain ⟨r, -, hr⟩ := h
        exact ⟨r, hr⟩
  · rintro ⟨r, rfl⟩
    simp only [sqB, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [nmod, Nat.mul_mod]
      exact hQ _ (Nat.mod_lt _ (by norm_num))
    · by_cases h1 : isq (r * r) * isq (r * r) = r * r
      · rw [show Nat.beq (isq (r * r) * isq (r * r)) (r * r) = true from Nat.beq_eq.mpr h1, cond_true]
      · rw [beq_false_of_ne h1, cond_false]
        have h2 : (Nat.ble (isq (r * r) * isq (r * r)) (r * r) &&
            Nat.blt (r * r) ((isq (r * r) + 1) * (isq (r * r) + 1))) = false := by
          by_contra hc
          simp only [Bool.not_eq_false, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
          obtain ⟨hlo, hhi⟩ := hc
          have hs : isq (r * r) ≤ r := Nat.mul_self_le_mul_self_iff.mp hlo
          have hr : r < isq (r * r) + 1 := Nat.mul_self_lt_mul_self_iff.mp hhi
          exact h1 (by rw [show isq (r * r) = r by omega])
        rw [h2, cond_false]
        simp only [slowSq, List.any_eq_true, List.mem_range, Nat.beq_eq]
        exact ⟨r, by nlinarith, rfl⟩

def primeLoop (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, d =>
    cond (Nat.blt p (d * d)) true (cond (Nat.beq (p % d) 0) false (primeLoop p fuel (d + 1)))

/-- Trial division up to the square root. -/
def primeB (p : ℕ) : Bool := Nat.ble 2 p && primeLoop p p 2

theorem primeLoop_spec (p : ℕ) : ∀ fuel d, p < (d + fuel) * (d + fuel) →
    (primeLoop p fuel d = true ↔ ∀ e, d ≤ e → e * e ≤ p → p % e ≠ 0) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d hd
    rw [Nat.add_zero] at hd
    simp only [primeLoop]
    refine ⟨fun _ e he hep => ?_, fun _ => trivial⟩
    have : d * d ≤ e * e := Nat.mul_le_mul he he
    omega
  | succ fuel ih =>
    intro d hd
    simp only [primeLoop]
    by_cases h1 : p < d * d
    · rw [show Nat.blt p (d * d) = true from Nat.blt_eq.mpr h1, cond_true]
      refine ⟨fun _ e he hep => ?_, fun _ => rfl⟩
      have : d * d ≤ e * e := Nat.mul_le_mul he he
      omega
    · rw [blt_false_of_not h1, cond_false]
      by_cases h2 : p % d = 0
      · rw [show Nat.beq (p % d) 0 = true from Nat.beq_eq.mpr h2, cond_true]
        refine ⟨fun h => absurd h (by simp), fun h => absurd h2 (h d le_rfl (by omega))⟩
      · rw [beq_false_of_ne h2, cond_false,
          ih (d + 1) (by rw [show d + 1 + fuel = d + (fuel + 1) by ring]; exact hd)]
        constructor
        · intro h e he hep
          rcases Nat.eq_or_lt_of_le he with rfl | hlt
          · exact h2
          · exact h e hlt hep
        · intro h e he hep
          exact h e (by omega) hep

theorem primeB_iff (p : ℕ) : primeB p = true ↔ p.Prime := by
  rw [primeB, Bool.and_eq_true, Nat.ble_eq, primeLoop_spec p p 2 (by nlinarith),
    Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hms hdvd => h m hm (Nat.le_sqrt.mp hms) (Nat.mod_eq_zero_of_dvd hdvd)⟩
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun e he hep hmod => h e he (Nat.le_sqrt.mpr hep) (Nat.dvd_of_mod_eq_zero hmod)⟩

/-! ## The enumeration of `w = min(y, z)` for one `x`

`k` runs over the classes modulo `M = ∏ p^j` that `x ∣ T_k` forces (`p^j ∣ k` or `p^j ∣ k + 1` for
each prime power), and the leaf tests the partner `o = n - x - w` of `w = T_k / x`. -/

def tri (k : ℕ) : ℕ := Nat.div (Nat.mul k (Nat.add k 1)) 2

/-- If `x * o` is triangular for the partner `o = n - x - w`, neither role assignment has both
primes. -/
def leaf (QRM n x w : ℕ) : Bool :=
  cond (sqB QRM (Nat.add (Nat.mul 8 (Nat.mul x (Nat.sub (Nat.sub n x) w))) 1))
    (!(primeB (6 * w - 1) && primeB (6 * (n - x - w) + 1)) &&
      !(primeB (6 * (n - x - w) - 1) && primeB (6 * w + 1)))
    true

theorem leaf_spec {QRM : ℕ} (hQ : ∀ k, k < 45045 → Nat.testBit QRM (k * k % 45045) = true)
    {n x w : ℕ} (h : leaf QRM n x w = true) (ht : IsTriangular (x * (n - x - w))) :
    ¬ ((6 * w - 1).Prime ∧ (6 * (n - x - w) + 1).Prime) ∧
      ¬ ((6 * (n - x - w) - 1).Prime ∧ (6 * w + 1).Prime) := by
  have hs : sqB QRM (Nat.add (Nat.mul 8 (Nat.mul x (Nat.sub (Nat.sub n x) w))) 1) = true :=
    (sqB_iff hQ _).mpr ((isTriangular_iff _).mp ht)
  rw [leaf, hs, cond_true, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · rintro ⟨hp1, hp2⟩
    rw [(primeB_iff _).mpr hp1, (primeB_iff _).mpr hp2] at h1
    exact absurd h1 (by simp)
  · rintro ⟨hp1, hp2⟩
    rw [(primeB_iff _).mpr hp1, (primeB_iff _).mpr hp2] at h2
    exact absurd h2 (by simp)

/-- Visits `k = c, c + M, c + 2M, ...` while `k(k+1) ≤ N`. -/
def stepOK (QRM n x M N fuel : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih k => cond (Nat.blt N (Nat.mul k (Nat.add k 1))) true
      (leaf QRM n x (Nat.div (tri k) x) && ih (Nat.add k M))) fuel

theorem stepOK_spec {QRM n x M N : ℕ} : ∀ f c, stepOK QRM n x M N f c = true →
    ∀ t, (c + M * t) * (c + M * t + 1) ≤ N → leaf QRM n x (tri (c + M * t) / x) = true := by
  intro f
  induction f with
  | zero => intro c h; exact absurd (show false = true from h) (by decide)
  | succ f ih =>
    intro c h0 t hN
    have h : cond (Nat.blt N (c * (c + 1))) true
        (leaf QRM n x (tri c / x) && stepOK QRM n x M N f (c + M)) = true := h0
    by_cases hb : N < c * (c + 1)
    · have : c * (c + 1) ≤ (c + M * t) * (c + M * t + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    rw [blt_false_of_not hb, cond_false, Bool.and_eq_true] at h
    obtain ⟨h0, hrest⟩ := h
    rcases t with _ | t
    · simpa using h0
    · have e : c + M * (t + 1) = (c + M) + M * t := by ring
      rw [e] at hN ⊢
      exact ih (c + M) hrest t hN

/-- `b ^ e % m` by squaring. -/
def powMod (m fuel : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => Nat.mod acc m)
    (fun _ ih b e acc => cond (Nat.beq e 0) (Nat.mod acc m)
      (ih (Nat.mod (Nat.mul b b) m) (Nat.div e 2)
        (cond (Nat.beq (Nat.mod e 2) 1) (Nat.mod (Nat.mul acc b) m) acc))) fuel

/-- The class `≡ c (mod M)` and `≡ a (mod m)`, reduced modulo `M m`. -/
def crt1 (c M a m inv : ℕ) : ℕ :=
  Nat.mod (Nat.add c (Nat.mul M (Nat.mod (Nat.mul (Nat.mod (Nat.sub (Nat.add a m) (Nat.mod c m)) m)
    inv) m))) (Nat.mul M m)

theorem crt1_spec {c M a m inv : ℕ} (hM : 0 < M) (hm : 0 < m) (ha : a < m)
    (hinv : M * inv % m = 1 % m) (hcop : Nat.Coprime M m) {k : ℕ} (hk1 : k % M = c % M)
    (hk2 : k % m = a) : k % (M * m) = crt1 c M a m inv := by
  show k % (M * m) = (c + M * (((a + m - c % m) % m) * inv % m)) % (M * m)
  set t := ((a + m - c % m) % m) * inv % m
  have h1 : c + M * t ≡ c [MOD M] := by
    show (c + M * t) % M = c % M
    rw [Nat.add_mul_mod_self_left]
  have h2 : c + M * t ≡ a [MOD m] := by
    have hcm := Nat.mod_lt c hm
    have e1 : M * t ≡ M * (((a + m - c % m) % m) * inv) [MOD m] :=
      Nat.ModEq.mul_left M (Nat.mod_modEq _ _)
    have e2 : M * (((a + m - c % m) % m) * inv) = ((a + m - c % m) % m) * (M * inv) := by ring
    have e3 : ((a + m - c % m) % m) * (M * inv) ≡ ((a + m - c % m) % m) * 1 [MOD m] :=
      Nat.ModEq.mul_left _ (by show M * inv % m = 1 % m; exact hinv)
    have e4 : ((a + m - c % m) % m) * 1 ≡ a + m - c % m [MOD m] := by
      rw [Nat.mul_one]; exact Nat.mod_modEq _ _
    have e5 : M * t ≡ a + m - c % m [MOD m] := by
      rw [e2] at e1; exact e1.trans (e3.trans e4)
    have e6 : c ≡ c % m [MOD m] := (Nat.mod_modEq _ _).symm
    have e7 : c + M * t ≡ c % m + (a + m - c % m) [MOD m] := Nat.ModEq.add e6 e5
    rw [show c % m + (a + m - c % m) = a + m * 1 by omega] at e7
    exact e7.trans (by show (a + m * 1) % m = a % m; rw [Nat.add_mul_mod_self_left])
  have hk : k ≡ c + M * t [MOD M * m] := by
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    exact ⟨(show k ≡ c [MOD M] from hk1).trans h1.symm,
      (show k ≡ a [MOD m] from by rw [Nat.ModEq, hk2, Nat.mod_eq_of_lt ha]).trans h2.symm⟩
  exact hk

/-- An inverse of `M` modulo `p ^ j` (by Euler's theorem; `1` when `M = 1`). It is only a
candidate: `crtTree` checks `M * inv ≡ 1`. -/
def invOf (M p j : ℕ) : ℕ :=
  cond (Nat.beq M 1) 1
    (powMod (Nat.pow p j) 64 (Nat.mod M (Nat.pow p j))
      (Nat.sub (Nat.mul (Nat.pow p (Nat.sub j 1)) (Nat.sub p 1)) 1) 1)

theorem mod_pred_of_dvd_succ {k m : ℕ} (hm : 0 < m) (hd : m ∣ k + 1) : k % m = m - 1 := by
  have h1 : (k + 1) % m = 0 := Nat.mod_eq_zero_of_dvd hd
  have h2 := Nat.mod_lt k hm
  have hdm := Nat.mod_add_div k m
  have h3 : (k % m + 1 + m * (k / m)) % m = 0 := by
    rw [show k % m + 1 + m * (k / m) = k + 1 by omega]; exact h1
  rw [Nat.add_mul_mod_self_left] at h3
  rcases Nat.lt_or_ge (k % m + 1) m with h4 | h4
  · rw [Nat.mod_eq_of_lt h4] at h3; omega
  · omega

/-- Visits the classes of `k` modulo the prime powers `fl` (`p ^ j ∣ k` or `p ^ j ∣ k + 1`) depth
first, each CRT step checked, and steps every class modulo the full product. -/
def crtTree (QRM n x N : ℕ) (fl : List (ℕ × ℕ)) : ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → ℕ → Bool) (fun c M => stepOK QRM n x M N n c)
    (fun e _ ih c M =>
      Nat.beq (Nat.mod (Nat.mul M (invOf M e.1 e.2)) (Nat.pow e.1 e.2)) 1 &&
        Nat.beq (Nat.gcd M (Nat.pow e.1 e.2)) 1 && Nat.ble 2 (Nat.pow e.1 e.2) &&
        ih (crt1 c M 0 (Nat.pow e.1 e.2) (invOf M e.1 e.2)) (Nat.mul M (Nat.pow e.1 e.2)) &&
        ih (crt1 c M (Nat.sub (Nat.pow e.1 e.2) 1) (Nat.pow e.1 e.2) (invOf M e.1 e.2))
          (Nat.mul M (Nat.pow e.1 e.2))) fl

theorem crtTree_spec {QRM n x N : ℕ} : ∀ (fl : List (ℕ × ℕ)) (c M : ℕ), 0 < M →
    crtTree QRM n x N fl c M = true →
    ∀ k, k % M = c → (∀ e ∈ fl, e.1 ^ e.2 ∣ k ∨ e.1 ^ e.2 ∣ k + 1) → k * (k + 1) ≤ N →
      leaf QRM n x (tri k / x) = true := by
  intro fl
  induction fl with
  | nil =>
    intro c M hM h0 k hk _ hN
    have h : stepOK QRM n x M N n c = true := h0
    have hkd : c + M * (k / M) = k := by rw [← hk]; exact Nat.mod_add_div k M
    have := stepOK_spec _ _ h (k / M) (by rw [hkd]; exact hN)
    rwa [hkd] at this
  | cons e rest ih =>
    intro c M hM h0 k hk hfl hN
    have h : (Nat.beq (M * invOf M e.1 e.2 % e.1 ^ e.2) 1 && Nat.beq (Nat.gcd M (e.1 ^ e.2)) 1 &&
        Nat.ble 2 (e.1 ^ e.2) &&
        crtTree QRM n x N rest (crt1 c M 0 (e.1 ^ e.2) (invOf M e.1 e.2)) (M * e.1 ^ e.2) &&
        crtTree QRM n x N rest (crt1 c M (e.1 ^ e.2 - 1) (e.1 ^ e.2) (invOf M e.1 e.2))
          (M * e.1 ^ e.2)) = true := h0
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨hinv, hg⟩, hm2⟩, h1⟩, h2⟩ := h
    set m := e.1 ^ e.2 with hmdef
    set inv := invOf M e.1 e.2 with hinvdef
    have hm : 0 < m := by omega
    have hcop : Nat.Coprime M m := hg
    have hinv' : M * inv % m = 1 % m := by rw [hinv, Nat.mod_eq_of_lt (by omega)]
    have hkM : k % M = c % M := by rw [← hk, Nat.mod_mod]
    have hfl' : ∀ e' ∈ rest, e'.1 ^ e'.2 ∣ k ∨ e'.1 ^ e'.2 ∣ k + 1 :=
      fun e' he' => hfl e' (List.mem_cons_of_mem _ he')
    rcases hfl e (List.mem_cons_self ..) with hd | hd
    · exact ih _ (M * m) (Nat.mul_pos hM hm) h1 k
        (crt1_spec hM hm hm hinv' hcop hkM (Nat.mod_eq_zero_of_dvd hd)) hfl' hN
    · exact ih _ (M * m) (Nat.mul_pos hM hm) h2 k
        (crt1_spec hM hm (show m - 1 < m by omega) hinv' hcop hkM (mod_pred_of_dvd_succ hm hd))
        hfl' hN

/-! ## Trial division (a heuristic: every prime power it returns is checked) -/

def divOut (d fuel : ℕ) : ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ × ℕ) (fun m => (0, m))
    (fun _ ih m => cond (Nat.beq (Nat.mod m d) 0)
      (Nat.add (ih (Nat.div m d)).1 1, (ih (Nat.div m d)).2) (0, m)) fuel

/-- Divides `m` by the primes of `ps` that divide `g` (for `p = 2` the exponent is one more), and
stops once `g = 1`. -/
def tdivG (ps : List ℕ) : ℕ → ℕ → List (ℕ × ℕ) × ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → List (ℕ × ℕ) × ℕ) (fun m _ => ([], m))
    (fun p _ ih m g => cond (Nat.beq g 1) ([], m)
      (cond (Nat.beq (Nat.mod g p) 0)
        ((p, cond (Nat.beq p 2) (Nat.add (divOut p 30 m).1 1) (divOut p 30 m).1) ::
            (ih (divOut p 30 m).2 (Nat.div g p)).1,
          (ih (divOut p 30 m).2 (Nat.div g p)).2)
        (ih m g))) ps

/-- The primes below 70. -/
def smallP : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]

/-- The primes from 71 to 577. -/
def midP : List ℕ := [
  71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
  173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271,
  277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389,
  397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
  509, 521, 523, 541, 547, 557, 563, 569, 571, 577]

/-- The product of the primes below 71. -/
def P67 : ℕ := 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 * 41 * 43 * 47 * 53 * 59 * 61 * 67

/-- The product of the primes below 584 (`prime_dvd_P577` checks what the proofs use). -/
def P577 : ℕ :=
  151521411679651275011132543953376311964004066972606689153427336881854992567724460294429083492800459737673130059467002646903931073695536639941219637506214383793800345244043516019092325035883377583122456232162242090392205219246548986185390

/-- Bit `p` is set for the primes `p` below 71. -/
def SPM : ℕ := 150465415423185266860

theorem small_dvd_P67 : ∀ q, q < 71 → q.Prime → q ∣ P67 := by decide +kernel

theorem prime_dvd_P577 : ∀ q, q < 584 → primeB q = true → q ∣ P577 := by decide +kernel

theorem spm_prime : ∀ q, q < 71 → Nat.testBit SPM q = true → primeB q = true := by decide +kernel

/-- `m` is prime: `71 ≤ m < 584²` with no prime factor below 584, or `m < 71²` with none below 71. -/
def primeBig (m : ℕ) : Bool :=
  Nat.ble 71 m && Nat.blt m 341056 &&
    (Nat.beq (Nat.gcd m P577) 1 || (Nat.blt m 5041 && Nat.beq (Nat.gcd m P67) 1))

theorem primeBig_spec {m : ℕ} (h : primeBig m = true) : m.Prime := by
  simp only [primeBig, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨h71, hlt⟩, hg⟩ := h
  by_contra hnp
  have hm1 : m ≠ 1 := by omega
  have hq := Nat.minFac_prime hm1
  have hsq := Nat.minFac_sq_le_self (show 0 < m by omega) hnp
  have hdvd := Nat.minFac_dvd m
  have hsq' : m.minFac * m.minFac ≤ m := by rw [← sq]; exact hsq
  rcases hg with hg | ⟨h5041, hg⟩
  · have h584 : m.minFac < 584 := by
      by_contra hc
      have := Nat.mul_le_mul (show 584 ≤ m.minFac by omega) (show 584 ≤ m.minFac by omega)
      omega
    have h1 := prime_dvd_P577 _ h584 ((primeB_iff _).mpr hq)
    have h2 : m.minFac ∣ Nat.gcd m P577 := Nat.dvd_gcd hdvd h1
    rw [hg] at h2
    exact hq.one_lt.ne' (Nat.eq_one_of_dvd_one h2)
  · by_cases hs : m.minFac < 71
    · have h1 := small_dvd_P67 _ hs hq
      have h2 : m.minFac ∣ Nat.gcd m P67 := Nat.dvd_gcd hdvd h1
      rw [hg] at h2
      exact hq.one_lt.ne' (Nat.eq_one_of_dvd_one h2)
    · have := Nat.mul_le_mul (show 71 ≤ m.minFac by omega) (show 71 ≤ m.minFac by omega)
      omega

/-- A primality check for the factors of `x < 341056`. -/
def primeQ (m : ℕ) : Bool := cond (Nat.blt m 71) (Nat.testBit SPM m) (primeBig m)

theorem primeQ_spec {m : ℕ} (h : primeQ m = true) : m.Prime := by
  unfold primeQ at h
  by_cases hs : m < 71
  · rw [show Nat.blt m 71 = true from Nat.blt_eq.mpr hs, cond_true] at h
    exact (primeB_iff _).mp (spm_prime m hs h)
  · rw [blt_false_of_not hs, cond_false] at h
    exact primeBig_spec h

/-- Prime powers for `x` (for `p = 2` the exponent is one more than in `x`), largest prime first. -/
def factorH (x : ℕ) : List (ℕ × ℕ) :=
  let s := tdivG smallP x (Nat.gcd x P67)
  cond (Nat.beq s.2 1) s.1
    (cond (primeQ s.2) ((s.2, 1) :: s.1)
      (let t := tdivG midP s.2 (Nat.gcd s.2 P577)
       t.1 ++ s.1 ++ cond (Nat.beq t.2 1) [] [(t.2, 1)]))

/-- A checked prime power for `x`: `p` prime, `j ≥ 1`, and `p^j ∣ 2x` (`p = 2`) or `p^j ∣ x`. -/
def ppOK (x : ℕ) (e : ℕ × ℕ) : Bool :=
  primeQ e.1 && Nat.ble 1 e.2 && Nat.beq (x % cond (Nat.beq e.1 2) (2 ^ (e.2 - 1)) (e.1 ^ e.2)) 0

theorem tri_two (k : ℕ) : 2 * tri k = k * (k + 1) := by
  unfold tri
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_succ_self k))

theorem prime_pow_dvd_consec {p j k : ℕ} (hp : p.Prime) (h : p ^ j ∣ k * (k + 1)) :
    p ^ j ∣ k ∨ p ^ j ∣ k + 1 := by
  by_cases hk : p ∣ k
  · left
    have hk1 : ¬ p ∣ k + 1 := by
      intro h1
      have : p ∣ 1 := by
        have := Nat.dvd_sub h1 hk
        simpa using this
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)
    have hc : Nat.Coprime (p ^ j) (k + 1) :=
      Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk1)
    exact hc.dvd_of_dvd_mul_right h
  · right
    have hc : Nat.Coprime (p ^ j) k :=
      Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk)
    exact hc.dvd_of_dvd_mul_left h

theorem ppOK_spec {x : ℕ} {e : ℕ × ℕ} (h : ppOK x e = true) {k : ℕ} (hk : x ∣ tri k) :
    e.1 ^ e.2 ∣ k ∨ e.1 ^ e.2 ∣ k + 1 := by
  simp only [ppOK, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨hpr, hj⟩, hdiv⟩ := h
  have hp : e.1.Prime := primeQ_spec hpr
  apply prime_pow_dvd_consec hp
  rw [← tri_two]
  by_cases h2 : e.1 = 2
  · rw [show Nat.beq e.1 2 = true from Nat.beq_eq.mpr h2, cond_true] at hdiv
    have hd : 2 ^ (e.2 - 1) ∣ tri k := dvd_trans (Nat.dvd_of_mod_eq_zero hdiv) hk
    rw [h2, show e.2 = (e.2 - 1) + 1 by omega, pow_succ]
    rw [Nat.mul_comm]
    exact Nat.mul_dvd_mul_left 2 hd
  · rw [beq_false_of_ne h2, cond_false] at hdiv
    have hd : e.1 ^ e.2 ∣ tri k := dvd_trans (Nat.dvd_of_mod_eq_zero hdiv) hk
    exact dvd_trans hd (Dvd.intro_left 2 rfl)

/-- The enumeration of `x`: checked prime powers, then the CRT classes and the stepping. -/
def enumOK (QRM n x : ℕ) : Bool :=
  (factorH x).all (ppOK x) && crtTree QRM n x (Nat.mul x (Nat.sub n x)) (factorH x) 0 1

/-- The core of the enumeration: for `w ≤ o`, `x + w + o = n` with `x * w` triangular, the leaf
at `w` is reached and passes. -/
theorem enumOK_leaf {QRM n x w o : ℕ} (h : enumOK QRM n x = true) (hw : 1 ≤ w) (hx : 1 ≤ x)
    (hwo : w ≤ o) (hsum : x + w + o = n) (htw : IsTriangular (x * w)) : leaf QRM n x w = true := by
  simp only [enumOK, nmul, nsub, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hall, htree⟩ := h
  obtain ⟨k, hk⟩ := htw
  have hk2 : x * w = tri k := hk
  have hxk : x ∣ tri k := ⟨w, by rw [← hk2]⟩
  have hkN : k * (k + 1) ≤ x * (n - x) := by
    rw [← tri_two, ← hk2, show n - x = w + o by omega]
    nlinarith
  have := crtTree_spec (factorH x) 0 1 one_pos htree k (Nat.mod_one k)
    (fun e he => ppOK_spec (hall e he) hxk) hkN
  rw [← hk2, Nat.mul_div_cancel_left w (by omega)] at this
  exact this

theorem enumOK_spec {QRM n x : ℕ}
    (hQ : ∀ k, k < 45045 → Nat.testBit QRM (k * k % 45045) = true)
    (h : enumOK QRM n x = true) : ∀ y z, ¬ IsSol n x y z := by
  intro y z hs
  obtain ⟨hx, hy, hz, hsum, hty, htz, hpy, hpz⟩ := hs
  by_cases hyz : y ≤ z
  · have hl := enumOK_leaf h hy hx hyz (by omega) hty
    have hz' : n - x - y = z := by omega
    have := leaf_spec hQ hl (by rw [hz']; exact htz)
    rw [hz'] at this
    exact this.1 ⟨hpy, hpz⟩
  · have hl := enumOK_leaf h hz hx (show z ≤ y by omega) (by omega) htz
    have hy' : n - x - z = y := by omega
    have := leaf_spec hQ hl (by rw [hy']; exact hty)
    rw [hy'] at this
    exact this.2 ⟨hpy, hpz⟩

/-! ## Explicit witnesses

For an `x` whose `F(x) = 8x(n - x) + 2` has its 3-mod-4 prime above the comb range, the data give
the cofactor `S`: `Q = F(x) / S ≡ 3 (mod 4)` and `gcd(Q, S) = 1`. -/

def witOK (n : ℕ) (e : ℕ × ℕ) : Bool :=
  Nat.ble 1 e.2 && Nat.beq ((8 * e.1 * (n - e.1) + 2) % e.2) 0 &&
    Nat.beq ((8 * e.1 * (n - e.1) + 2) / e.2 % 4) 3 &&
    Nat.beq (Nat.gcd ((8 * e.1 * (n - e.1) + 2) / e.2) e.2) 1

theorem witOK_spec {n : ℕ} {e : ℕ × ℕ} (h : witOK n e = true) :
    ¬ ∃ s r : ℕ, 8 * e.1 * (n - e.1) + 2 = s ^ 2 + r ^ 2 := by
  simp only [witOK, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨hS, hdiv⟩, hQ4⟩, hg⟩ := h
  set M := 8 * e.1 * (n - e.1) + 2 with hMdef
  have hM : 0 < M := by omega
  have hSM : e.2 ∣ M := Nat.dvd_of_mod_eq_zero hdiv
  have hMQ : M = M / e.2 * e.2 := (Nat.div_mul_cancel hSM).symm
  have hQ0 : 0 < M / e.2 := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hQ4; norm_num at hQ4)
  have hQdvd : M / e.2 ∣ M := ⟨e.2, hMQ⟩
  have hQS : M / (M / e.2) = e.2 := by
    rw [Nat.div_div_self hSM (by omega)]
  apply not_sos_of_witness hM hQ4 hQdvd
  rw [hQS]
  exact hg

/-- The bitmap of the listed `x` (at positions `x - x0`). -/
def wlBits (x0 : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | e :: es => (1 <<< (e.1 - x0)) ||| wlBits x0 es

theorem wlBits_spec (x0 : ℕ) : ∀ (es : List (ℕ × ℕ)) (j : ℕ), (wlBits x0 es).testBit j = true →
    ∃ e ∈ es, e.1 - x0 = j := by
  intro es
  induction es with
  | nil => intro j h; simp [wlBits] at h
  | cons e es ih =>
    intro j h
    rw [wlBits, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h
      exact ⟨e, List.mem_cons_self .., by simpa using h⟩
    · obtain ⟨e', he', h'⟩ := ih j h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

/-- The listed witnesses of a block: each in `[x0, x0 + len)` and valid. -/
def wlOK (n x0 len : ℕ) (es : List (ℕ × ℕ)) : Bool :=
  es.all (fun e => Nat.ble x0 e.1 && Nat.blt e.1 (x0 + len) && witOK n e)

/-! ## Blocks of `x` -/

def blockOK (QRM n x0 W V len : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => (Nat.testBit W j || Nat.testBit V j || Nat.beq (Nat.add x0 j) 0 ||
        Nat.blt (Nat.sub n 2) (Nat.add x0 j) || enumOK QRM n (Nat.add x0 j)) && ih) len

theorem blockOK_spec {QRM n len x0 : ℕ} {QL : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {WL : List (ℕ × ℕ)}
    (hQ : ∀ k, k < 45045 → Nat.testBit QRM (k * k % 45045) = true)
    (hQL : ∀ e ∈ QL, entryOK n e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 (primeB e.1) = true)
    (hlen : len ≤ 2 ^ 24)
    (h : (wlOK n x0 len WL && blockOK QRM n x0 (wBlock len x0 QL) (wlBits x0 WL) len) = true) :
    ∀ j < len, ∀ y z, ¬ IsSol n (x0 + j) y z := by
  rw [Bool.and_eq_true] at h
  obtain ⟨hwl, h⟩ := h
  simp only [wlOK, List.all_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hwl
  have key : ∀ m, m ≤ len →
      blockOK QRM n x0 (wBlock len x0 QL) (wlBits x0 WL) m = true →
      ∀ j < m, ∀ y z, ¬ IsSol n (x0 + j) y z := by
    intro m
    induction m with
    | zero => intro _ _ j hj; omega
    | succ m ih =>
      intro hm hb0 j hj y z hs
      have hb : ((Nat.testBit (wBlock len x0 QL) m || Nat.testBit (wlBits x0 WL) m ||
          Nat.beq (x0 + m) 0 || Nat.blt (n - 2) (x0 + m) || enumOK QRM n (x0 + m)) &&
          blockOK QRM n x0 (wBlock len x0 QL) (wlBits x0 WL) m) = true := hb0
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hb
      obtain ⟨hcase, hrest⟩ := hb
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | hjm
      · exact ih (by omega) hrest j hlt y z hs
      · rw [hjm] at hs
        have hs' := hs
        obtain ⟨hx, hy, hz, hsum, -⟩ := hs'
        rcases hcase with (((hbit | hv) | h0) | hbig) | hen
        · obtain ⟨e, he, hwq⟩ := wBlock_spec len x0 QL m hbit
          have hent := hQL e he
          have hpq : primeB e.1 = true := by
            cases hpb : primeB e.1
            · rw [hpb] at hent
              simp [entryOK] at hent
            · rfl
          have hq := (primeB_iff _).mp hpq
          rw [hpq] at hent
          have := entry_witness hq hent hlen m hwq (by omega)
          exact this (circle hs)
        · obtain ⟨e, he, hem⟩ := wlBits_spec x0 WL m hv
          obtain ⟨⟨hlo, -⟩, hw⟩ := hwl e he
          have hex : e.1 = x0 + m := by omega
          have := witOK_spec hw
          rw [hex] at this
          exact this (circle hs)
        · omega
        · omega
        · exact enumOK_spec hQ hen y z hs
  exact key len le_rfl h

/-! ## Covering the range of `x` with blocks of varying length -/

theorem range_of_block {n x0 len : ℕ} (h : ∀ j < len, ∀ y z, ¬ IsSol n (x0 + j) y z) :
    ∀ x, x0 ≤ x → x < x0 + len → ∀ y z, ¬ IsSol n x y z := by
  intro x h1 h2 y z
  have := h (x - x0) (by omega) y z
  rwa [show x0 + (x - x0) = x by omega] at this

theorem range_join {n a b c : ℕ} (h1 : ∀ x, a ≤ x → x < b → ∀ y z, ¬ IsSol n x y z)
    (h2 : ∀ x, b ≤ x → x < c → ∀ y z, ¬ IsSol n x y z) :
    ∀ x, a ≤ x → x < c → ∀ y z, ¬ IsSol n x y z := by
  intro x hx1 hx2
  by_cases hb : x < b
  · exact h1 x hx1 hb
  · exact h2 x (by omega) hx2

theorem no_sol_of_range {n c : ℕ} (hc : n ≤ c + 1)
    (h : ∀ x, 0 ≤ x → x < c → ∀ y z, ¬ IsSol n x y z) : ∀ x y z, ¬ IsSol n x y z := by
  intro x y z hs
  have hs' := hs
  obtain ⟨hx, hy, hz, hsum, -⟩ := hs'
  exact h x (Nat.zero_le _) (by omega) y z hs


/-! ## Certificate data -/

/-- Bit `r` is set for every square residue `r` modulo `45045`. -/
def QRM : ℕ := 0x4000000000000080100000004020000000000000800100000800000000000000004000400100100002000800000020000100000800000000000400000020800110020000000080000000000000000000000100000000000000004000820000800080000020080800004000000010020000010004100000000100000000000000000000004000800000800000810000400020000000000000402100000800000020000000100120000000000000100002000000100000020000000000000804000000004000020000800000000000000820004000000080400000120800004000000000000000010100000800100000900000006000000004000000000800080400020000020000100000000020002000804000020880100000100000000000400000000002000000000000000100000004800000000004100000000010080000000100000004004000000100400100800000000020000000000000000000c000000008000100000040100040008100001000040000200000000001140200000200000008008000000201000000000000020040000040000000040000000200000800020000000200100001001000000000208004000000000008040000001000008020000800000200040000000040000000000060000008000100a4000020000000800000000800000400000000004020080000000000400800004800100100000000000000000004000010804100000000000100000004110000000020000100000880020800000400000000004000020000000800000000000000024000002004000000000000002000000000000080120000000800804000800000000000010080000010100000000004002004000002100020800000004000000000020000100000000000000100000104020000004000000000800080000000100020014000000020020000800804000000000400000100000000000800000000100800000020000004000000000806004000000000800000010000400020100000804000000000000000120800100000000100000000800000000400000000900000004000030004000020000800000000400100800004000080000020000000804084000000020000000000100000820004000900000000000000100000000000000004010000000800000100020080420100000004000020000100080000000980000000104002000000002000000000000000000810000020020080020000000000000000100030000004000080000000000000004000800000000100000000000000004400000000002000000020100000000100084000020000000000080020800100000000000000020820000000100400000000400004000022004000004000000100800000100000000020100000000010000800000000000010880000020100000800000002004800002000000000000000020004000800000000004000020100010000104000000020000000000104000400100000000010000004820000000000000802000000400000020000010024000000100100000100020000020002110000800020000004000800400800080020100000000004000000000004000000000100000000002000000800010000000000000000800004000000000002800000004000800100100000004010000000000000000800100000000000000020004100000000400000100400800020020000000100000080000800000100800000000000000420000020004000004000000080000000100000000100002010800006000000104000000000800084000000000820010000000000000100000800000024080000000020400100000000100000000000100020000000402000000804000020000100020000010080000004000800004000000010000000120000004000800400000100000100000c00004000100010004004010104500800000800000000022000000000010000000000000000800000020000100000000800002000080000000000000000004020000000802000800000000020100010000000020000002000000004004000000120080000000080000820004000100000000000820100000000000010004000000100800800100000010020002020000004020000100000000400800000020100000000000800000000104000020000000004020000000800004010000000000100120000080020000000000010000804000080100000900000004000000004000002004000000020000000000000000004000020000000c000000008000000000000100840208000000000000000000008000001000200008000044000040000020001000000000001020000040040000000000001000008000200000000008020100000000000004008200000000040200040000000001000800000000801000000040200000204000108009060000000000000000000000008000000000000048000000200000000200000000040004000000008001000200000000001000008040200000040020000008000000000061000000048000000000000800208000000040100200000000040000008800000001008000040200000040008000008040048000000008000000000000000220000008040000000000001800200001800000000000020008000020200200000001000000040004200001000000000000000000041000300040000000000000000000000000000000200800000000000008001044021000000000040001000008000000000044000000008200000000200100000020000000000008801000001004001000000000040000020000800000200005000000040000000200240000000000000200000000000200000840000000000001008000000008000040001000000000004001040008000000000000000241000108000000000000020000200001100200001200000008100000008000000001000000000040000040000200000000844000001808000041000200100200020100000000000000000000000000000000200000009000000800008300000000000000000000200020008008000000a0000020100000000004000000000402000000100000080100000000000800000800100000020010800004000000000020804000004000400100100400004020000000000000000800000800000000800000004000000000000000004000000020020080000004100000000000002100800000020080100000000000004000c000000008000000000008100001000000048020040000001000000001000000000000000008040000000000004021000009000200200000000004000000008000001008200100000000300000008200000000040004200001000041000000000000000008000040000001004000000000020048000020008000000000000000000000020000000240000001001008001000000804000000000000000204000000008020008000000200041000000008000000004060000200000000800000200800208040000008000000001100000000000a0004000800000004084000100100800000000000010020000000000100000000020100000004010000800000000100800880000000100000000000000004020000100800000000000400024100020000000020000000100000000000000080120000000800004000800004000100010000000020100000800000002004000000100800800000004000000000020000104000800120000000000002020080000000000000800000400100000020004000004020000000800004000020000000000120000010020800000000000000000000000000000100000006004000004000000000000080420004080000800000000000000000000800100000000020000000000000000c000000000000100000040200000000200008000040004000000000041100a0000000000000004104000000020000000000000000800004000800400800000020100000022000000004030000000000000100000080000000100000004020000100000000000900000000000002000000004000800102000000000810004020000080020800000004000000000030800000020000000000000400904000400000000100000000000000004400000004800000020020000020004000004000020000100004000000800100400110000004020000000000800400000080c00000000020010000000010000100000000000000080002100000800000000000100000000800180020020000000800000000000000000100020000000000000004000822000000000000020000100004004000000020000000000100000420100000000010000004000004400800000802000000000000020000010020000000100000800000020800000000100000802000000104000000000000080420000100000004800000000004000020000000020000002000020404000000000000000100800084000020004000000000000000800100000800000010080000024000000800100000000020000020000100000800420000000c008000208201000001000100800040000000000000000000000004001000000040000200000001800000000800000000000000100008040000001000001000000000040200000000020140000000000000008108000000240800000000004001040008000200000000001040200000000020000008020000201001000200000000040000040000008040000200000000001000000040200000000001004000000208000040000020108040000101004008000000000000200260000000040000000000000801008000000200001200000008000020008000000008000000040000000000000020108000040000001000000001000000800000000008041000000000000800000001000000200040021000008000008000000000200000000000200000008028000000000100200001100040000000001000000000000000000001040000000008040008000004000200000000000000220000008040100040000001001208000800000000000020100001000000000000009004000040000000040000000008000000000001000200040000000004200001008040000008000000801000100000008200000009000000000000000041000000008000044000000008000001000000000201020008040000008001000001008009000000001000000020000000040000005008000000000000200040000200000000800000001000000040040000000204000008000060000200000000000000000808200040008000000000000100000000100000000040000020000000001000208000200000000108000200001000000000008000000001040000000040100000000000800000001000200100200000200000000008004000000004000040000200000008020000040048000000000000040000000000060000008000000800000201000000001000008000204020000000000208801000000000000000048200001000000000000000000040000300040000240000001000004001100000000200800000008000008000044000000008000000201000008200040000040000000000000000000000000000020100000040000801200000004001040000000000000000000840000001001000000040020040200020000008000000000000000000200000800200000000001000001000200000040001000008000000000041008020008000000200200000008040000000004020001000001000000001000800008100000000000004008000000040040000000008200000000004000201000000040000200000000000008001000000001000000000001000000200000009000008000000300000000200000000000004021008000000000800000200001200040040000000000000000001000000a0104000000000004000000104000000000800004010020000820000000000080402100000c000000200000000000000109000000001000000000000020000000000000000048000004200201800200000000000000000000000040000000805000001000000040008200000001020000000008000040000000000020040000041008000001000800000200000000000040008001000020008008000200201000000004000000044000000000200000000040200000008000001000000000201001004000100200000000000000008840000201004000000000020048200060000000040000000200000800000000000240100001000008001000008000200000000000040204001000000020008000000201001000000008020000004040000208001100a4000000080000004000000000000000110000000020000004000800400804080000100000800004000000010024000010004100000000000000000000010000000020000000800800000800000400000000004000800002100000000000000000000100020000000004000000002000000100000000000000000000804000000004000100000880000000000000820004000000000400000820800000004000000000000000100000800100000110000006020080004000000000804080400000000020010000000000020000000804000020080000000120000000000000000000000800100020000000002100000804000000004100000000810080000004100000004000000000000000120800000000000020000000000000000c00000000900010004004010004000800000800004000020000800000110020000020000000804000000000100000000000102000000004000000000000000020000000002000000000030000100000000000020000400100020004004000000100080000000080000020004000000000000000800106000000000010084000020000800800000004000000000020000004020080000000000400800000800100000100000000000000004000000004002000020000100000004110000000020000100000080020800000400010000004000020000000900000000000800004000002014000000000004000800000000000080020100000800004000800000000000010180020000100000000000002004800002100020000000004000004000022000100004000000100100004104020000020000000000800000000000000000010080000020000400800004002000020400000000000000000000000000100800000020000020000010000806000000000000800000000000400100100000004800000000000000020800100004000000000020804010000000000000100000004020020004002000000800000800000100800004000080000020000002804000000000020000000004100000800000000100800000020000100000000000004004810000000800000000000000420100000004000024000000180000000180000000100002010800002000000000000100000800000020000000020000000000000000100830000000000080000000020000004000800020080100000100000000004402000000006000000100100000000000084000020000800000000020010000000000000000020800000000100c0010000040000400000200000000400000050080000080000002002410000000001000000000000002000008000000012000000080000200080000000010000000000002000400080001000000400002010081000010000000002200000000010400000012000000001000000082000000010000080200000010000002000001000442000010080200010002001002010213

theorem QRM_spec : ∀ k, k < 45045 → Nat.testBit QRM (k * k % 45045) = true :=
  fun k hk => qrCheck_spec QRM 45045 0 (by decide +kernel) k (Nat.zero_le _) (by omega)

/-- Witness entries `(q, r1, r2, s1, s2)`: `q ≡ 3 (mod 4)` prime, `r1, r2` the roots of
`8x(335979 - x) + 2` modulo `q`, `s1, s2` their lifts modulo `q²`. -/
def QL : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3, 1, 2, 4, 5), (7, 3, 4, 17, 18), (11, 2, 4, 57, 26), (19, 6, 15, 215, 34),
  (23, 1, 17, 369, 224), (31, 12, 20, 136, 454), (43, 5, 15, 693, 617),
  (59, 6, 27, 3015, 2269), (71, 9, 69, 2565, 708), (79, 2, 69, 4900, 306),
  (83, 8, 70, 4241, 1066), (103, 40, 56, 6426, 674), (139, 59, 96, 1866, 5656),
  (151, 60, 95, 20445, 19121), (163, 74, 125, 26480, 17240), (179, 5, 170, 14146, 1423),
  (199, 108, 158, 1899, 17272), (211, 85, 193, 26038, 42815), (283, 123, 218, 53610, 42102),
  (331, 153, 192, 73966, 42891), (347, 121, 309, 101792, 113778),
  (431, 281, 380, 70534, 79684), (439, 241, 342, 35361, 107897),
  (443, 295, 333, 163762, 172217), (463, 341, 426, 114702, 6908), (467, 42, 164, 95777, 22113),
  (479, 319, 360, 121027, 214952), (487, 133, 303, 203699, 132280),
  (499, 156, 495, 112431, 223548), (607, 432, 483, 215917, 120062),
  (631, 308, 610, 204121, 131858), (643, 447, 529, 411324, 338104),
  (647, 73, 113, 373392, 381196), (659, 174, 374, 359988, 410272),
  (691, 339, 505, 339620, 473840), (719, 101, 105, 81348, 254631),
  (727, 47, 58, 66204, 269775), (743, 323, 563, 202419, 133560),
  (787, 12, 705, 423418, 531930), (823, 59, 136, 589327, 423981),
  (863, 438, 697, 132477, 203502), (883, 32, 407, 674644, 441024),
  (907, 165, 224, 96307, 239672), (911, 337, 394, 276370, 59609),
  (947, 263, 478, 441565, 791223), (1031, 2, 902, 441270, 957670),
  (1039, 608, 813, 708167, 707333), (1063, 540, 594, 794601, 671347),
  (1087, 423, 760, 56947, 279032), (1091, 285, 757, 1079284, 446976),
  (1123, 440, 885, 426057, 1171051), (1151, 75, 963, 79494, 256485),
  (1171, 292, 781, 1076441, 630779), (1223, 262, 615, 963986, 867722),
  (1231, 1160, 1218, 1410655, 440685), (1259, 47, 1038, 637101, 1283959),
  (1279, 936, 1224, 140347, 195632), (1283, 209, 907, 1169022, 813046),
  (1307, 270, 1117, 1414444, 629784), (1327, 547, 1028, 974565, 1122343),
  (1367, 490, 574, 1830903, 373765), (1399, 650, 968, 916995, 1376185),
  (1447, 497, 1225, 985904, 1443884), (1471, 154, 437, 782726, 1717094),
  (1499, 247, 1455, 1773564, 809416), (1511, 29, 508, 1544271, 1074829),
  (1523, 1014, 1428, 930044, 1725464), (1531, 306, 384, 854604, 1825336),
  (1543, 253, 895, 1322604, 1394224), (1559, 264, 530, 637895, 2128565),
  (1567, 805, 1403, 2424954, 366514), (1571, 624, 732, 399658, 2404362),
  (1607, 481, 1242, 349200, 2569228), (1627, 22, 795, 2388458, 594650),
  (1663, 517, 1199, 1109738, 1991810), (1667, 993, 1586, 1629652, 1485216),
  (1699, 208, 1068, 1389990, 1832590), (1723, 270, 1447, 1926584, 1378124),
  (1783, 961, 1597, 1245495, 2269573), (1787, 388, 1422, 863509, 2665839),
  (1811, 450, 494, 1059885, 2555815), (1823, 96, 451, 3272381, 386927),
  (1831, 309, 597, 2087649, 1600891), (1867, 1811, 1842, 1534618, 2287050),
  (1871, 1197, 1744, 1990070, 1846550), (1907, 392, 1862, 2454701, 1517927),
  (1931, 246, 1670, 3713559, 351181), (1987, 773, 1390, 4747, 331232),
  (1999, 173, 1973, 2716814, 1615166), (2039, 515, 1068, 43334, 292645),
  (2111, 953, 1488, 3137899, 1654401), (2131, 504, 908, 3024393, 1852747),
  (2203, 256, 867, 4071400, 1117788), (2207, 1093, 1629, 974380, 4232448),
  (2243, 15, 1757, 4104705, 1262323), (2251, 967, 1864, 127023, 208956),
  (2267, 638, 2092, 363358, 5111910), (2287, 230, 1847, 1425031, 4141317),
  (2347, 1210, 1495, 4711639, 1132749), (2383, 208, 2151, 4492163, 1522505),
  (2399, 727, 1791, 833180, 5258000), (2503, 1420, 1660, 1996311, 4604677),
  (2531, 45, 1842, 6302235, 439705), (2543, 1218, 1628, 3647880, 3154948),
  (2579, 1032, 2256, 4186749, 2800471), (2687, 261, 2530, 6320085, 1235863),
  (2699, 405, 898, 5106913, 2513667), (2731, 842, 1955, 2395929, 5398411),
  (2803, 2589, 2636, 7590310, 602478), (2819, 1415, 1922, 7237788, 1044952),
  (2843, 1141, 2207, 1161085, 7257543), (2851, 509, 1903, 6001864, 2462316),
  (2879, 2253, 2641, 6828362, 1796258), (2887, 503, 584, 618321, 8052427),
  (2927, 274, 2027, 1302789, 7600519), (2971, 440, 2787, 1563186, 7599634),
  (3011, 2048, 2721, 1387108, 8014992), (3019, 75, 795, 2626605, 6823735),
  (3023, 55, 371, 6889472, 2585036), (3079, 1312, 2135, 8179136, 1637084),
  (3167, 1680, 1764, 9106805, 1259063), (3259, 1385, 2176, 1513561, 9443499),
  (3319, 26, 734, 7491009, 3860731), (3323, 1204, 2475, 3995450, 7382858),
  (3331, 894, 1985, 430593, 11000947), (3359, 916, 2522, 9127319, 2491541),
  (3391, 828, 2833, 4927951, 6906909), (3463, 1348, 2183, 10868242, 1460106),
  (3467, 1328, 1819, 3631277, 8724791), (3511, 245, 2189, 3929054, 8734046),
  (3527, 2193, 2248, 3486869, 9288839), (3559, 590, 843, 9844784, 3157676),
  (3571, 1417, 2459, 7846904, 5241116), (3607, 945, 3190, 6363693, 6982735),
  (3623, 2964, 3322, 10527779, 2934329), (3643, 267, 556, 6222511, 7384917),
  (3767, 1391, 3092, 12134898, 2391370), (3803, 1405, 3713, 2180524, 12618264),
  (3847, 167, 1123, 9109863, 6025525), (3851, 2237, 2556, 2647874, 12518306),
  (3863, 253, 3508, 9116933, 6141815), (3907, 1749, 2135, 474496, 15126132),
  (3923, 912, 1612, 15355534, 370374), (3931, 1932, 3843, 10922250, 4866490),
  (3943, 1044, 3723, 14444253, 1438975), (3947, 2158, 2273, 11247161, 4667627),
  (4079, 2297, 3283, 4595251, 12378969), (4091, 178, 339, 3812990, 13259270),
  (4099, 190, 3770, 6460214, 10677566), (4111, 794, 2194, 9591757, 7644543),
  (4139, 1021, 3838, 878489, 16588811), (4219, 1112, 1566, 4287616, 13848324),
  (4231, 438, 1292, 10649865, 7587475), (4259, 1372, 2405, 6462275, 12012785),
  (4271, 2877, 4235, 14156971, 4420449), (4283, 554, 1351, 3041484, 15638584),
  (4327, 3277, 3850, 232608, 103371), (4339, 2501, 3714, 9904099, 9258801),
  (4447, 3088, 3813, 4974834, 15136954), (4483, 150, 4087, 19738799, 694469),
  (4519, 1711, 4381, 10634918, 10122422), (4583, 483, 937, 1783270, 19556598),
  (4603, 549, 4014, 9653040, 11870548), (4639, 2875, 3735, 17413042, 4443258),
  (4643, 751, 932, 5428418, 16465010), (4651, 1511, 4247, 11694125, 10273655),
  (4663, 1810, 3096, 3153998, 18925550), (4703, 2189, 4580, 7682188, 14772000),
  (4723, 1613, 3756, 10203293, 12439415), (4751, 3483, 4677, 16052361, 6855619),
  (4783, 2406, 3546, 16039805, 7173263), (4799, 874, 3974, 16029534, 7336846),
  (4831, 650, 1990, 9073268, 14601272), (4871, 1675, 3076, 6041715, 18020905),
  (4903, 379, 2196, 740732, 23634656), (4919, 1665, 4741, 24129360, 403180),
  (4931, 316, 355, 17387022, 7263718), (4951, 4431, 4782, 22234421, 2613959),
  (4967, 551, 2639, 3695999, 21311069), (4987, 165, 1685, 12926469, 12279679),
  (5023, 4584, 4900, 18850880, 6715628), (5039, 228, 3177, 5039228, 20688272),
  (5087, 711, 4613, 10154363, 16059185), (5119, 1516, 1728, 4562545, 21977595),
  (5147, 1554, 5017, 809633, 26017955), (5179, 677, 3846, 23943194, 3214826),
  (5227, 1504, 5174, 17078113, 10579395), (5231, 2846, 3580, 12886799, 14812541),
  (5279, 1533, 1869, 22880719, 5323101), (5323, 1372, 4581, 21713889, 6956419),
  (5387, 3135, 4237, 10965680, 18390068), (5399, 1361, 5279, 23292647, 6192533),
  (5471, 638, 1610, 26086366, 4181454), (5483, 2281, 4718, 11461751, 18937517),
  (5507, 2568, 2991, 21870865, 8792163), (5519, 131, 4708, 25001201, 5794139),
  (5531, 1018, 3101, 11560808, 19367132), (5591, 904, 5206, 18126926, 13468334),
  (5623, 4344, 5501, 28389248, 3564860), (5651, 3450, 4771, 31389104, 880676),
  (5659, 3406, 4351, 15350614, 17009646), (5711, 5108, 5344, 6698400, 26253100),
  (5743, 1321, 1564, 116181, 219798), (5827, 3866, 5801, 19594240, 14695668),
  (5839, 735, 2421, 29464329, 4965571), (5867, 2704, 4723, 14171509, 20586159),
  (5879, 1779, 4976, 10813260, 24085360), (5939, 4567, 4767, 26694433, 8913267),
  (6007, 2699, 2895, 18288007, 18132021), (6011, 2274, 3100, 24815682, 11652418),
  (6047, 1247, 2147, 4748142, 32154046), (6131, 2178, 2727, 13895024, 24030116),
  (6143, 4266, 6134, 17069520, 21002908), (6163, 664, 2513, 33471917, 4846631),
  (6199, 3265, 4167, 6307648, 32455932), (6203, 2521, 4699, 10256080, 28557108),
  (6211, 2728, 4068, 15971209, 22941291), (6247, 5179, 5956, 5296388, 34064600),
  (6271, 1622, 1994, 31764237, 7897183), (6299, 752, 1380, 29309999, 10703381),
  (6427, 2757, 5445, 18473955, 23168353), (6451, 2088, 4890, 27025327, 14926053),
  (6491, 472, 4466, 11314285, 31154775), (6547, 730, 1352, 24984082, 18215106),
  (6599, 2282, 3747, 33940939, 9941841), (6619, 411, 4618, 1469829, 42677311),
  (6659, 4303, 5385, 24595990, 20082270), (6703, 1865, 5667, 3480722, 41785466),
  (6719, 2196, 4552, 42694722, 2786218), (6779, 1484, 2324, 12007093, 34283727),
  (6823, 3508, 4967, 32747085, 14142223), (6863, 3084, 3471, 22939230, 24497518),
  (6899, 1155, 3672, 40470689, 7461491), (6907, 1158, 3285, 1237511, 46805117),
  (6947, 1214, 1309, 1946374, 46650414), (6959, 2779, 6127, 28311991, 20451669),
  (6967, 2795, 5735, 22011548, 26863520), (7027, 706, 5004, 28164922, 21549786),
  (7043, 5271, 6730, 23535934, 26403894), (7103, 2598, 6643, 44431863, 6356725),
  (7151, 1081, 5952, 19487556, 31985224), (7159, 2034, 4631, 17112044, 34475216),
  (7207, 1098, 3359, 15006072, 37270756), (7211, 5009, 6475, 30521961, 21812539),
  (7219, 73, 3832, 14041028, 38408912), (7307, 3309, 3855, 20894022, 32834206),
  (7331, 2601, 3483, 7443566, 46635974), (7351, 1721, 3463, 20400746, 33972434),
  (7451, 2173, 5962, 2349238, 53504142), (7583, 123, 2204, 42457340, 15380528),
  (7591, 2356, 7210, 1505374, 56453886), (7603, 3831, 5219, 45325314, 12816274),
  (7607, 4329, 4549, 4591350, 53611078), (7639, 954, 6548, 37959145, 20731155),
  (7687, 5976, 7149, 4080086, 55345862), (7699, 5281, 7340, 6534033, 53076547),
  (7703, 1540, 3210, 15761878, 43910310), (7723, 1236, 2654, 15872001, 44108707),
  (7727, 1797, 1921, 7798340, 52244168), (7823, 704, 6709, 57820497, 3714811),
  (7867, 5960, 7472, 47915990, 14309678), (7883, 1394, 3499, 11802245, 50675423),
  (7907, 5703, 6089, 26264850, 36591778), (7919, 1596, 1785, 247085, 88894),
  (7927, 4999, 5973, 26837894, 36335414), (7951, 943, 1094, 49090417, 14463963),
  (7963, 2241, 7255, 11668036, 52077312), (8059, 1986, 3574, 24461051, 40822409),
  (8111, 4032, 7507, 38320396, 27803904), (8147, 4812, 5287, 46010921, 20698667),
  (8167, 1656, 7643, 9916394, 57119474), (8171, 1733, 7406, 45930924, 21170296),
  (8191, 2413, 5926, 36427790, 31000670), (8219, 7297, 8141, 35603786, 32284154),
  (8287, 5327, 7459, 3825634, 65184714), (8363, 3660, 6162, 39945348, 30330400),
  (8387, 2041, 6845, 54450445, 16227303), (8419, 1070, 6568, 64785275, 6430265),
  (8423, 594, 6888, 5517659, 65765249), (8431, 414, 6756, 21971600, 49446140),
  (8599, 4474, 4743, 1156740, 73122040), (8623, 1373, 6932, 2717618, 71974490),
  (8699, 6355, 7761, 32114364, 43894216), (8707, 6877, 6943, 51003776, 25144052),
  (8803, 2040, 8228, 1973912, 75854876), (8819, 4192, 5484, 6768365, 71342375),
  (8887, 2585, 4575, 77843818, 1470930), (8923, 293, 5535, 33461543, 46494365),
  (8951, 5083, 8660, 50497674, 29958706), (8963, 1462, 2886, 70755384, 9915964),
  (8999, 3919, 8096, 57336548, 23981432), (9011, 5531, 6052, 7601804, 73932296),
  (9067, 3754, 5813, 25001473, 57544995), (9199, 1476, 3339, 26319815, 58637765),
  (9227, 46, 3761, 43865204, 41608304), (9239, 382, 2993, 50011089, 35684011),
  (9319, 4768, 5046, 40635608, 46544132), (9323, 2370, 7304, 16159129, 71095179),
  (9371, 2412, 5582, 29230561, 58921059), (9403, 7182, 9095, 22771845, 65980543),
  (9463, 7016, 7221, 62680465, 27203883), (9479, 4459, 9234, 84282248, 5905172),
  (9491, 4743, 8542, 41898017, 48517043), (9539, 2929, 8724, 89888926, 1439574),
  (9551, 2763, 8482, 39658515, 51899065), (9587, 2870, 7151, 86650176, 5596372),
  (9619, 2102, 6831, 4984744, 87876396), (9631, 9073, 9083, 58199575, 34892565),
  (9643, 1081, 7036, 22179981, 71143447), (9767, 4489, 9179, 62786765, 32943503),
  (9787, 3462, 9546, 21544649, 74576699), (9907, 2817, 6231, 70629820, 27854808),
  (9931, 2002, 6254, 56817253, 42143487)]

theorem QL_ok : ∀ e ∈ QL, entryOK 335979 e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 (primeB e.1) = true := by
  decide +kernel

/-! Explicit witnesses `(x, S)` per block of `x`. -/

def WL0 : List (ℕ × ℕ) := [
  (23, 54), (49, 54), (50, 54), (104, 1566), (212, 54), (238, 43254)]

def WL1 : List (ℕ × ℕ) := [
  (265, 54), (373, 54), (401, 486), (427, 54), (428, 54), (492, 38174), (616, 54), (644, 486),
  (670, 54), (698, 54)]

def WL2 : List (ℕ × ℕ) := [
  (778, 54), (810, 54814), (825, 27254), (995, 54), (1076, 54), (1122, 32126), (1156, 54),
  (1183, 54), (1202, 191358), (1237, 54), (1238, 41742), (1265, 54), (1272, 38846),
  (1308, 33806), (1341, 686), (1400, 54), (1426, 54), (1427, 313902)]

def WL3 : List (ℕ × ℕ) := [
  (1589, 368766), (1590, 62102), (1671, 79262), (1723, 54), (1724, 4806), (1769, 221814),
  (1770, 84358), (1804, 54), (1805, 57294), (1831, 2646), (1832, 54), (1912, 10638),
  (1913, 54), (1939, 39366), (1966, 54), (1967, 54), (1976, 238662), (1980, 77566),
  (2031, 75974), (2074, 54), (2075, 2646), (2129, 54), (2211, 36878), (2291, 54),
  (2309, 233406), (2452, 54), (2480, 54)]

def WL4 : List (ℕ × ℕ) := [
  (2588, 486), (2614, 20324574), (2722, 432918), (2805, 57446), (2848, 269046), (2857, 66798),
  (2858, 54), (2885, 50598), (3047, 54), (3108, 28814), (3208, 10422), (3228, 52454),
  (3261, 28606), (3262, 69606), (3263, 54), (3289, 54), (3317, 321246), (3324, 2662),
  (3344, 54), (3424, 54), (3438, 81182), (3452, 91422), (3459, 40574), (3505, 54),
  (3506, 797094), (3516, 103438), (3586, 280206), (3613, 1566), (3640, 486), (3668, 54),
  (3694, 54), (3705, 93014), (3829, 54)]

def WL5 : List (ℕ × ℕ) := [
  (3857, 54), (3937, 616518), (4046, 486), (4101, 57406), (4109, 284814), (4153, 54),
  (4181, 881982), (4230, 54598), (4261, 6534), (4296, 34862), (4297, 269046), (4342, 57726),
  (4377, 90494), (4397, 469422), (4428, 66542), (4478, 10422), (4506, 59198), (4559, 10422),
  (4586, 54), (4612, 486), (4720, 22086), (4748, 54), (4802, 1566), (4828, 54), (4829, 54),
  (4901, 210582), (4909, 54), (4990, 54), (4991, 54), (5018, 58806), (5045, 1112022)]

def WL6 : List (ℕ × ℕ) := [
  (5223, 21782), (5234, 54), (5256, 50294), (5280, 42382), (5346, 64958), (5358, 686),
  (5368, 54), (5369, 790182), (5395, 59238), (5431, 263502), (5457, 686), (5508, 38062),
  (5558, 40878), (5637, 64054), (5661, 23462), (5692, 54), (5701, 179046), (5754, 25342),
  (5773, 384534), (5784, 127214), (5787, 79022), (5800, 129654), (5899, 324774), (6012, 47774),
  (6053, 198486), (6060, 20798), (6070, 486), (6097, 102006), (6125, 70254), (6126, 22478),
  (6138, 38102), (6179, 54), (6259, 10638), (6287, 54), (6341, 54), (6368, 151902),
  (6486, 686), (6610, 54)]

def WL7 : List (ℕ × ℕ) := [
  (6691, 1745334), (6700, 396054), (6777, 90526), (6853, 5238), (6882, 97558), (6935, 239814),
  (6944, 342558), (7015, 1566), (7069, 27486), (7070, 54), (7074, 672182), (7161, 142942),
  (7205, 583686), (7232, 133542), (7233, 130246), (7268, 458478), (7281, 22766), (7313, 54),
  (7420, 4806), (7455, 140878), (7475, 54), (7502, 746766), (7503, 78382), (7510, 213606),
  (7555, 106542), (7582, 54), (7632, 96742), (7664, 54), (7674, 36382), (7709, 326286),
  (7799, 756486), (7887, 25238), (7896, 171982), (7905, 584582), (8042, 389502), (8069, 54),
  (8085, 38854), (8149, 22086), (8150, 54), (8203, 54), (8231, 54), (8283, 27926),
  (8311, 1379646), (8392, 114966), (8393, 235278), (8420, 486), (8437, 183798), (8445, 33614),
  (8446, 2646)]

def WL8 : List (ℕ × ℕ) := [
  (8490, 29278), (8493, 55598), (8528, 1823526), (8544, 184534), (8554, 205038),
  (8555, 1888974), (8608, 360342), (8609, 54), (8636, 54), (8690, 2646), (8709, 155486),
  (8770, 54), (8788, 6174), (8829, 145454), (8887, 6174), (8910, 184222), (8932, 54),
  (8933, 4806), (8960, 4806), (8986, 486), (9014, 563382), (9060, 209086), (9144, 147454),
  (9149, 486), (9175, 54), (9203, 31158), (9213, 58846), (9252, 93374), (9256, 173718),
  (9284, 54), (9337, 12582), (9345, 32374), (9364, 45414), (9410, 469494), (9445, 580662),
  (9472, 47142), (9474, 686), (9491, 184662), (9499, 54), (9513, 26998), (9527, 259254),
  (9540, 54478), (9543, 84142), (9555, 22886), (9581, 54), (9589, 232542), (9689, 10422),
  (9942, 170398), (9954, 126398), (9966, 67006), (10093, 5238), (10094, 35694),
  (10101, 114542), (10129, 645534), (10165, 338454), (10191, 25582), (10200, 49094),
  (10215, 200918), (10255, 54), (10263, 795934), (10296, 148726), (10310, 206334),
  (10319, 457902), (10337, 54), (10417, 1128438), (10431, 21718), (10444, 2066958),
  (10458, 30398), (10471, 54)]

def WL9 : List (ℕ × ℕ) := [
  (10499, 21438), (10503, 247646), (10553, 20641446), (10554, 202414), (10607, 486),
  (10633, 54), (10634, 54), (10642, 232398), (10656, 74726), (10662, 157286), (10687, 4374),
  (10795, 6534), (10796, 54), (10822, 14526), (10823, 54), (10876, 16902), (10956, 76654),
  (10975, 681246), (10984, 13014), (10985, 54), (11038, 54), (11065, 54), (11067, 42974),
  (11094, 21478), (11166, 70054), (11353, 229734), (11361, 134894), (11362, 54), (11551, 54),
  (11579, 486), (11669, 684846), (11740, 1866078), (11767, 19494), (11811, 232894),
  (11875, 89766414), (11876, 2646), (11884, 23958), (11902, 486), (11929, 54), (11930, 54),
  (11974, 179046), (12011, 54), (12119, 1566), (12173, 54), (12199, 54), (12200, 341118),
  (12218, 6174), (12298, 532998), (12317, 6174), (12334, 124038), (12343, 251982),
  (12361, 707022), (12362, 54), (12415, 2807406), (12497, 54), (12523, 14958), (12524, 54),
  (12578, 224478), (12658, 298134), (12659, 637686), (12684, 32278), (12711, 45718),
  (12739, 66798), (12767, 54), (12794, 169614)]

def WL10 : List (ℕ × ℕ) := [
  (12803, 368694), (12804, 75182), (12837, 33134), (12901, 54), (12902, 1566),
  (12906, 1991798), (12921, 47198), (12963, 121886), (13029, 33038), (13090, 469422),
  (13117, 130734), (13145, 54), (13225, 54), (13253, 54), (13260, 145006), (13333, 287982),
  (13362, 90278), (13487, 369918), (13594, 219006), (13658, 54), (13659, 54542),
  (13692, 197878), (13711, 70254), (13792, 2206494), (13845, 43982), (13874, 54), (13901, 54),
  (13972, 23958), (13981, 16902), (13982, 2646), (14036, 54), (14043, 32894), (14062, 189486),
  (14089, 486), (14133, 58622), (14153, 306486), (14197, 54), (14224, 54), (14252, 486),
  (14278, 54), (14279, 54), (14350, 377262), (14387, 259254), (14391, 153662), (14400, 193918),
  (14439, 901958), (14441, 54), (14495, 3256686), (14521, 2646), (14523, 138878),
  (14547, 30934), (14548, 54), (14575, 14094), (14602, 54), (14619, 395822), (14791, 54),
  (14792, 54), (14818, 486), (14820, 44566), (14846, 5238), (14853, 143774), (14901, 273622),
  (14917, 196038), (14925, 38278), (14980, 1916622), (14981, 2720142), (14988, 82702),
  (15007, 630774)]

def WL11 : List (ℕ × ℕ) := [
  (15115, 403974), (15156, 53566), (15161, 202302), (15205, 210582), (15224, 486),
  (15251, 45414), (15276, 25934), (15288, 29782), (15304, 486), (15332, 407646),
  (15412, 23382), (15440, 54), (15477, 80254), (15493, 54), (15513, 54086), (15521, 54),
  (15638, 773622), (15673, 801126), (15682, 54), (15763, 22086), (15828, 44134),
  (15845, 1145718), (15927, 131902), (15939, 66446), (15953, 486), (15980, 54),
  (15988, 448326), (15989, 242982), (16060, 1855926), (16088, 22734), (16114, 1764342),
  (16116, 94558), (16122, 197774), (16142, 4806), (16169, 4806), (16178, 467118),
  (16242, 95054), (16375, 621198), (16389, 38326), (16465, 304614), (16466, 54),
  (16500, 220502), (16569, 30182), (16575, 196094), (16582, 250326), (16609, 341046),
  (16654, 2636118), (16655, 54), (16677, 686), (16695, 161302), (16708, 15174), (16709, 54),
  (16725, 88526), (16772, 489222), (16870, 54), (17005, 486), (17059, 4806), (17114, 1272078),
  (17141, 1210086), (17190, 51206), (17208, 2662), (17211, 26822), (17275, 54), (17292, 53894),
  (17302, 251478), (17337, 72526), (17383, 54), (17394, 226262), (17487, 68294),
  (17499, 93502), (17519, 54), (17564, 257454), (17627, 54)]

def WL12 : List (ℕ × ℕ) := [
  (17694, 20854), (17707, 76734), (17708, 112806), (17838, 101846), (17843, 76086),
  (17870, 54), (17897, 486), (17922, 1828238), (17949, 1851022), (17950, 5238), (18005, 54),
  (18117, 36758), (18135, 54254), (18230, 222822), (18283, 466902), (18291, 125446),
  (18328, 6534), (18356, 644382), (18392, 6174), (18402, 21334), (18410, 54), (18423, 113902),
  (18437, 47574), (18472, 466758), (18480, 35806), (18490, 76734), (18492, 78902), (18571, 54),
  (18598, 54), (18599, 21438), (18618, 24982), (18648, 3941446), (18732, 172222), (18733, 54),
  (18734, 54), (18741, 49886), (18760, 302238), (18846, 252646), (18912, 56102),
  (18948, 32854), (18981, 2112782), (18986, 213534), (19003, 54), (19005, 135358),
  (19066, 791766), (19074, 285598), (19165, 54), (19182, 189206), (19192, 198774),
  (19200, 34582), (19220, 3700134), (19256, 188262), (19283, 388566), (19327, 16902),
  (19328, 54), (19332, 136798), (19377, 23734), (19399, 266958), (19489, 57726),
  (19508, 564822), (19536, 226126), (19572, 1027006), (19579, 343566), (19598, 486),
  (19644, 279142), (19651, 54), (19678, 4566942), (19706, 54), (19732, 54), (19764, 604366),
  (19777, 610614), (19803, 64502), (19814, 2646), (19863, 686), (19867, 2590974), (19894, 54),
  (19895, 112374), (19917, 277798), (19921, 486), (19930, 205182), (20029, 1323918),
  (20048, 946206), (20076, 30766), (20084, 47142), (20111, 2803518), (20120, 320238),
  (20137, 54), (20138, 54), (20217, 181054), (20272, 185382), (20273, 1162134),
  (20300, 670086), (20327, 486), (20362, 951894), (20370, 132214), (20399, 236718),
  (20461, 54702)]

def WL13 : List (ℕ × ℕ) := [
  (20515, 54), (20543, 46278), (20551, 586566), (20623, 265086), (20650, 2825118), (20705, 54),
  (20785, 60966), (20840, 500958), (20866, 54), (20867, 16902), (20921, 54), (21028, 54),
  (21033, 66446), (21051, 1352038), (21110, 14958), (21136, 155207502), (21163, 4514238),
  (21186, 2002238), (21201, 2662), (21271, 54), (21272, 54), (21357, 22766), (21434, 39582),
  (21479, 6174), (21488, 54), (21513, 187366), (21578, 6174), (21595, 6534), (21596, 51894),
  (21642, 154694), (21649, 18846), (21676, 2045358), (21678, 145118), (21693, 38422),
  (21756, 91726), (21758, 54), (21785, 486), (21812, 993654), (21820, 866358), (21822, 135142),
  (21838, 4806), (21909, 143614), (21910, 367974), (21973, 15174), (22000, 54),
  (22001, 2558574), (22135, 54), (22149, 103438), (22248, 37342), (22297, 54), (22377, 231926),
  (22395, 60142), (22440, 191822), (22459, 2646), (22460, 2646), (22470, 2080262),
  (22476, 47942), (22512, 66574), (22514, 486), (22567, 5238), (22622, 611766),
  (22671, 300302), (22674, 243118), (22703, 5238), (22707, 182278), (22765, 634518),
  (22784, 54), (22811, 1147878), (22878, 763222), (22946, 54), (22965, 602678), (22973, 54),
  (22982, 230238), (23000, 620622), (23088, 49102), (23094, 210046), (23161, 1867374),
  (23189, 54), (23289, 236918), (23296, 874422), (23304, 780158), (23315, 637614),
  (23325, 67198), (23337, 139718), (23340, 35942), (23350, 54), (23351, 4806), (23360, 733662),
  (23378, 1350486), (23387, 562878), (23458, 1566), (23459, 650214), (23486, 4374),
  (23512, 54), (23513, 54), (23521, 866934), (23539, 54)]

def WL14 : List (ℕ × ℕ) := [
  (23589, 105998), (23620, 484326), (23637, 105614), (23667, 55054), (23675, 5854734),
  (23697, 107974), (23701, 54), (23772, 141166), (23782, 2646), (23809, 4374), (23836, 40878),
  (23862, 22894), (23864, 2958174), (23904, 182366), (23931, 90382), (23979, 686),
  (24025, 664254), (24102, 31582), (24241, 139374), (24242, 54), (24295, 136566),
  (24304, 498438), (24318, 37006), (24368, 483102), (24372, 47438), (24387, 200918),
  (24403, 54), (24423, 31294), (24431, 2085966), (24484, 54), (24485, 54), (24486, 67006),
  (24566, 178429662), (24584, 230382), (24591, 45742), (24593, 40878), (24701, 47142),
  (24745, 207342), (24835, 359694), (24836, 97254), (24870, 1202398), (24871, 438678),
  (24890, 54), (24909, 686), (24997, 54), (25008, 33614), (25020, 55646), (25023, 26374),
  (25024, 14094), (25052, 47358), (25059, 187934), (25101, 177638), (25149, 320998),
  (25187, 2683206), (25206, 130654), (25241, 54), (25263, 196094), (25321, 54), (25402, 54),
  (25430, 14094), (25446, 76606), (25464, 23854), (25482, 86854), (25506, 173846),
  (25510, 486), (25530, 222694), (25537, 45414), (25538, 54), (25565, 10638), (25619, 243702),
  (25668, 29462), (25699, 54), (25726, 224262), (25734, 106558), (25803, 22342),
  (25818, 48214), (25844, 677934), (25851, 47942), (25888, 54), (25890, 1611806),
  (25908, 221006), (25947, 29102), (25951, 23958), (25970, 54), (26024, 107838),
  (26181, 30278), (26186, 18846), (26187, 27518), (26213, 490158), (26257, 995958),
  (26258, 236718), (26266, 979182), (26293, 54), (26343, 72686), (26348, 150606),
  (26419, 672534), (26429, 1727838), (26478, 1041838), (26509, 54), (26510, 1202958),
  (26532, 1665238), (26586, 109126), (26598, 175502), (26698, 310014), (26752, 54),
  (26753, 54), (26775, 23942), (26780, 620838), (26859, 46406), (26861, 54)]

def WL15 : List (ℕ × ℕ) := [
  (26914, 54), (26922, 112078), (26968, 23814), (26979, 47438), (27057, 34246), (27063, 49934),
  (27076, 54), (27077, 54), (27104, 3657582), (27123, 162038), (27158, 54), (27239, 1918998),
  (27265, 190782), (27266, 54), (27365, 992286), (27400, 44334), (27428, 54), (27446, 469782),
  (27468, 268078), (27510, 35918), (27585, 44078), (27589, 54), (27643, 14526),
  (27644, 572886), (27651, 13718), (27671, 54), (27725, 54), (27752, 199508238), (27805, 5238),
  (27806, 54), (27833, 54), (27846, 75742), (27868, 271926), (27887, 4188294), (27967, 21438),
  (27994, 54), (28048, 54), (28049, 54), (28156, 2976966), (28203, 41918), (28210, 12582),
  (28237, 54), (28251, 307126), (28260, 65222), (28350, 856718), (28453, 54), (28476, 34702),
  (28616, 34614), (28638, 23974), (28716, 52814), (28805, 83646), (28894, 503046),
  (28939, 941166), (28940, 54), (28959, 1458526), (28968, 1090574), (29021, 54),
  (29025, 519302), (29065, 1053198), (29101, 12582), (29124, 5055134), (29155, 486),
  (29157, 62774), (29210, 54), (29223, 306134), (29244, 49694), (29290, 54), (29309, 821862),
  (29337, 25814), (29344, 54), (29345, 4480326), (29371, 54), (29398, 280422), (29496, 113782),
  (29507, 54), (29562, 188662), (29569, 835902), (29587, 54), (29588, 54), (29596, 594414),
  (29637, 96766), (29643, 23486), (29695, 54), (29776, 54), (29777, 54), (29920, 222246),
  (29938, 54), (29939, 5238), (30074, 12582), (30127, 247374), (30136, 1126638), (30182, 54),
  (30204, 2394278)]

def WL16 : List (ℕ × ℕ) := [
  (30253, 249822), (30290, 486), (30297, 235022), (30316, 54), (30317, 2804814),
  (30324, 28814), (30343, 54), (30344, 1878174), (30393, 54958), (30399, 77806), (30424, 5238),
  (30456, 278878), (30478, 54), (30479, 54), (30506, 54), (30533, 93798), (30541, 312966),
  (30546, 143998), (30613, 486), (30651, 48494), (30667, 14958), (30693, 20606), (30740, 6174),
  (30753, 33958), (30829, 887382), (30830, 92934), (30839, 6174), (30840, 226334),
  (30849, 23726), (30856, 486), (30897, 223334), (30910, 54), (30911, 1566), (31009, 299718),
  (31019, 486), (31038, 115894), (31083, 527534), (31208, 54), (31215, 49094), (31218, 197254),
  (31234, 54), (31262, 486), (31269, 20222), (31275, 2662), (31329, 1117102), (31344, 62438),
  (31369, 54), (31397, 54), (31450, 4806), (31478, 54), (31521, 287654), (31554, 321934),
  (31613, 54), (31621, 1124262), (31639, 54), (31647, 84806), (31720, 2646), (31800, 33094),
  (31802, 19494), (31855, 54), (32016, 108734), (32018, 63774), (32055, 40246), (32112, 66542),
  (32180, 13014), (32206, 154494), (32207, 1566), (32261, 903366), (32367, 3030806),
  (32422, 230742), (32450, 20142), (32451, 65678), (32503, 54), (32504, 2646),
  (32530, 2779542), (32557, 4374), (32611, 14526), (32612, 54), (32625, 168998),
  (32640, 384014), (32688, 62534), (32832, 125206), (32835, 295294), (32864, 579654),
  (32877, 114278), (32886, 134782), (32908, 54), (32909, 69606), (32935, 54), (32970, 684806),
  (32989, 54), (33017, 54), (33043, 2309958), (33116, 738918), (33117, 97742), (33152, 41094),
  (33188, 246222), (33304, 361134), (33369, 29686), (33375, 327718), (33395, 54),
  (33405, 1855478), (33440, 184806), (33447, 220046), (33467, 558702), (33476, 54),
  (33495, 32134), (33529, 1203822), (33557, 54), (33583, 236859822), (33637, 1566),
  (33665, 4431942), (33699, 202966), (33711, 350822), (33718, 293814), (33745, 54),
  (33746, 54), (33756, 374086)]

def WL17 : List (ℕ × ℕ) := [
  (33801, 220718), (33907, 54), (33908, 54), (33935, 486), (33944, 841014), (33962, 53838),
  (33969, 3406742), (34008, 83702), (34042, 346734), (34043, 1566), (34105, 532782),
  (34116, 37006), (34123, 54), (34131, 73574), (34155, 52526), (34230, 29662), (34269, 83006),
  (34305, 165806), (34312, 203526), (34347, 30902), (34376, 1107342), (34383, 69358),
  (34421, 529254), (34428, 50342), (34447, 106542), (34449, 772966), (34473, 27926),
  (34510, 123462), (34511, 23958), (34572, 294662), (34609, 28566), (34636, 54), (34691, 54),
  (34791, 29662), (34798, 54), (34812, 357118), (34853, 54), (34866, 54134), (34879, 203094),
  (34965, 29758), (35041, 194022), (35079, 111974), (35106, 265046), (35141, 218934),
  (35176, 47574), (35196, 46622), (35199, 1408358), (35208, 202646), (35258, 54),
  (35337, 146966), (35338, 137646), (35419, 54), (35420, 124686), (35436, 29686), (35527, 54),
  (35547, 87886), (35581, 54), (35595, 25814), (35636, 486), (35762, 494766), (35770, 68958),
  (35778, 161822), (35784, 40102), (35824, 99846), (35905, 54), (35933, 1162134), (35959, 486),
  (35986, 1566), (36013, 54), (36094, 39582), (36176, 126414), (36185, 271926), (36230, 54),
  (36237, 151966), (36266, 1225566), (36310, 54), (36327, 686), (36365, 113238),
  (36402, 119302), (36473, 2646), (36483, 220678), (36553, 20142), (36554, 54), (36576, 37798),
  (36580, 54), (36626, 664758), (36661, 54), (36688, 486), (36699, 21782), (36715, 54),
  (36720, 4430294), (36734, 1217142), (36750, 170894), (36751, 584838), (36762, 26318),
  (36765, 29366), (36814, 978246), (36877, 35262), (36878, 43038), (36897, 101078),
  (36905, 1566), (36958, 1633014), (36959, 54), (36981, 76238), (37011, 49054), (37066, 54),
  (37067, 670734), (37121, 54), (37137, 777838), (37148, 54), (37155, 127342), (37203, 94102),
  (37266, 24214), (37309, 80622), (37310, 54), (37332, 213646), (37364, 3217374)]

def WL18 : List (ℕ × ℕ) := [
  (37386, 132694), (37389, 22894), (37410, 173878), (37449, 188798), (37472, 54), (37526, 54),
  (37533, 27446), (37552, 76734), (37617, 68062), (37634, 185382), (37687, 54),
  (37695, 372838), (37715, 54), (37758, 391478), (37849, 22086), (37850, 54), (37876, 54),
  (37903, 486), (37914, 28102), (38011, 54), (38039, 282582), (38092, 54), (38121, 96742),
  (38138, 254574), (38247, 203446), (38254, 369414), (38255, 4982526), (38264, 656118),
  (38309, 486), (38385, 686), (38417, 5238), (38442, 1114006), (38444, 54), (38498, 67446),
  (38544, 318446), (38583, 73774), (38605, 54), (38610, 113342), (38632, 486), (38660, 54),
  (38767, 54), (38781, 97054), (38830, 698238), (38875, 23814), (38921, 256374), (38929, 54),
  (38943, 28654), (38982, 95398), (38983, 54), (38991, 51886), (39033, 85334), (39038, 486),
  (39045, 91726), (39069, 227518), (39150, 28654), (39172, 54), (39226, 54), (39236, 184662),
  (39249, 21958), (39254, 433782), (39335, 54), (39388, 613062), (39496, 54), (39523, 1636686),
  (39541, 358686), (39551, 530766), (39612, 91174), (39632, 64854), (39636, 121222),
  (39658, 129654), (39740, 338526), (39757, 3710574), (39804, 41614), (39821, 54),
  (39870, 47198), (39874, 14526), (39893, 284238), (39902, 54), (39920, 430398), (39955, 54),
  (39983, 23382), (39996, 44158), (40018, 683766), (40063, 64422), (40100, 6174),
  (40109, 824022), (40118, 4888782), (40144, 54), (40161, 29558), (40199, 4806),
  (40216, 1152126), (40235, 192006), (40299, 80198), (40307, 797094), (40344, 686),
  (40388, 54), (40433, 713214), (40441, 54), (40443, 19894), (40455, 196838), (40469, 2354886),
  (40496, 486), (40522, 54), (40532, 1127502), (40620, 85406), (40677, 54214), (40739, 486),
  (40755, 54022), (40815, 253846), (40851, 116062), (40854, 23462), (40928, 54),
  (40955, 1261062), (41008, 19494), (41090, 1566), (41116, 54), (41162, 280494),
  (41214, 116398), (41223, 190382), (41225, 356238), (41251, 54), (41278, 22086), (41333, 54),
  (41369, 123462), (41376, 437254), (41377, 279486), (41400, 1619302), (41484, 21806),
  (41495, 54), (41503, 298206), (41526, 292846), (41603, 1566), (41607, 277094),
  (41656, 237438), (41706, 5369038)]

def WL19 : List (ℕ × ℕ) := [
  (41764, 4314654), (41823, 155318), (41845, 54), (41847, 120854), (41889, 25294),
  (41981, 789966), (42008, 54702), (42078, 81166), (42169, 14526), (42170, 54), (42177, 36758),
  (42223, 54), (42251, 540486), (42305, 7496118), (42331, 54), (42369, 294062),
  (42378, 419702), (42386, 1566), (42402, 7623518), (42412, 2600478), (42501, 686),
  (42503, 1092942), (42520, 486), (42558, 72902), (42702, 291598), (42720, 267934),
  (42736, 54), (42745, 6174), (42818, 54), (42844, 55566), (42890, 246222), (42903, 313438),
  (42930, 246254), (42945, 60142), (42952, 54), (42961, 329526), (42975, 876206),
  (42980, 41742), (42987, 26998), (42996, 159158), (43008, 21718), (43043, 410526),
  (43051, 1231182), (43115, 16902), (43167, 98734), (43169, 126846), (43191, 163406),
  (43196, 54), (43223, 6534), (43224, 22054), (43254, 2121614), (43293, 198734), (43357, 54),
  (43385, 54), (43434, 314582), (43465, 581526), (43530, 686), (43546, 1566), (43547, 3485214),
  (43587, 321446), (43590, 72614), (43605, 77342), (43627, 8512182), (43680, 103654),
  (43682, 46278), (43707, 2484614), (43726, 9376542), (43735, 696438), (43790, 59238),
  (43797, 73894), (43842, 161726), (43871, 54), (43906, 219798), (43933, 237294),
  (44028, 230446), (44113, 50598), (44142, 153982), (44168, 54), (44214, 226318),
  (44232, 347374), (44239, 485046), (44275, 40878), (44329, 1566), (44339, 662166),
  (44357, 55134), (44358, 2120654), (44415, 42646), (44421, 177638), (44438, 54),
  (44472, 454262), (44491, 54), (44518, 54), (44617, 283806), (44654, 54), (44680, 16902),
  (44700, 137798), (44707, 486), (44718, 306686), (44721, 34838), (44766, 212246),
  (44806, 679446), (44841, 248134), (44842, 133758), (44843, 54), (44850, 21278),
  (44886, 116822), (44914, 367398), (44924, 54), (44949, 97694), (44977, 31158),
  (45004, 32454), (45059, 54), (45087, 91646), (45096, 177614), (45147, 1376998),
  (45159, 960982), (45185, 615078), (45193, 486), (45213, 271702), (45220, 54),
  (45248, 258606), (45382, 1566), (45383, 54), (45432, 2662726), (45464, 110862),
  (45491, 3282822), (45562, 972198), (45563, 668214), (45571, 54), (45572, 54),
  (45732, 153358), (45734, 2646), (45744, 25238), (45774, 252622), (45814, 1160622)]

def WL20 : List (ℕ × ℕ) := [
  (45832, 2451078), (45842, 8888454), (45922, 486), (45941, 422262), (45950, 54),
  (45977, 2160702), (45996, 183422), (46030, 54), (46031, 54), (46067, 297342),
  (46170, 6894046), (46175, 6174), (46192, 54), (46220, 16902), (46274, 312671934),
  (46354, 31158), (46355, 54), (46377, 32902), (46381, 54), (46382, 54), (46516, 10666134),
  (46517, 54), (46542, 2080982), (46544, 2076246), (46548, 383062), (46572, 344846),
  (46597, 219078), (46614, 386734), (46625, 54), (46678, 1566), (46705, 54), (46725, 173158),
  (46751, 271638), (46759, 5238), (46786, 21438), (46795, 879246), (46839, 53726),
  (46867, 7924446), (46894, 486), (46912, 1357038), (46920, 69742), (46922, 6431454),
  (46948, 3258846), (46949, 54), (47046, 201694), (47083, 5297022), (47223, 42694),
  (47273, 54), (47353, 54), (47364, 297494), (47417, 489222), (47424, 83966), (47453, 1079478),
  (47462, 3705102), (47488, 54), (47490, 1582414), (47516, 54), (47543, 4203414), (47547, 686),
  (47550, 389726), (47570, 32454), (47596, 2646), (47646, 686), (47651, 20142),
  (47679, 163406), (47686, 123462), (47731, 189486), (47732, 6482646), (47759, 54),
  (47812, 54702), (47839, 54), (47850, 249358), (47858, 749646), (47893, 54), (47894, 54),
  (47921, 195102), (47928, 34774), (48001, 41526), (48055, 120798), (48056, 702486),
  (48082, 54), (48109, 486), (48126, 47326), (48137, 1566), (48145, 201078), (48189, 278534),
  (48263, 1204614), (48298, 2446254), (48299, 173286), (48300, 32222), (48307, 950526),
  (48326, 54), (48396, 25934), (48405, 57502), (48406, 54), (48460, 6673374), (48487, 34614),
  (48488, 2581038), (48537, 113422), (48561, 348694), (48564, 25582), (48568, 13014),
  (48576, 686), (48603, 41438), (48642, 119942), (48645, 405254), (48650, 1566),
  (48675, 132398), (48735, 20542), (48747, 436382), (48748, 480582), (48774, 23462),
  (48785, 54), (48803, 225702), (48838, 632286), (48852, 272942), (48865, 63774), (48946, 54),
  (48973, 54), (49027, 1566), (49028, 54), (49055, 54), (49146, 20798), (49162, 3395358),
  (49189, 93582), (49190, 5523822), (49224, 44342), (49252, 1177326), (49280, 260046),
  (49281, 1980934), (49386, 304126), (49432, 14526), (49461, 256238), (49495, 184662),
  (49540, 54), (49545, 206134), (49595, 54), (49622, 7664814), (49703, 76734), (49730, 4374),
  (49747, 988326), (49749, 180118), (49758, 310462), (49783, 10638), (49784, 4806),
  (49884, 20326), (49999, 6534), (50016, 43726), (50027, 54), (50062, 417654), (50108, 51894),
  (50161, 10401318), (50169, 23678), (50188, 54), (50189, 22734), (50216, 14094),
  (50243, 2646), (50269, 54), (50324, 54), (50350, 54), (50367, 63926), (50391, 133702)]

def WL21 : List (ℕ × ℕ) := [
  (50484, 97814), (50513, 726678), (50541, 33958), (50566, 54), (50567, 54), (50634, 184534),
  (50661, 146518), (50675, 54), (50706, 44006), (50729, 54), (50733, 686), (50756, 2593998),
  (50784, 87518), (50836, 54), (50918, 23382), (50972, 114966), (51071, 531558),
  (51079, 241974), (51080, 1472958), (51120, 164278), (51161, 1229526), (51214, 54),
  (51241, 23382), (51282, 277918), (51296, 19494), (51322, 54), (51323, 1125846),
  (51333, 135062), (51375, 189542), (51456, 360838), (51457, 54), (51485, 54), (51566, 828198),
  (51597, 68342), (51603, 5263742), (51612, 75982), (51620, 195318), (51630, 58262),
  (51646, 1566), (51674, 210438), (51681, 124078), (51700, 54), (51890, 54), (51939, 30398),
  (52015, 647118), (52017, 33806), (52024, 54), (52025, 219942), (52105, 344985534),
  (52106, 409806), (52116, 64102), (52128, 107398), (52178, 362214), (52206, 120206),
  (52213, 54), (52214, 4806), (52240, 4374), (52267, 89478), (52268, 35262), (52281, 28286),
  (52295, 54), (52312, 469998), (52376, 424062), (52393, 1014894), (52403, 486), (52429, 1566),
  (52456, 54), (52466, 541278), (52473, 326614), (52479, 21542), (52519, 216774),
  (52578, 117886), (52590, 27134), (52591, 54), (52704, 172798), (52726, 486), (52753, 54),
  (52754, 54), (52772, 674694), (52785, 149014), (52834, 4353966), (52872, 151318),
  (52889, 23814), (52915, 54), (52942, 1566), (52996, 5506758), (53023, 54), (53058, 1694006),
  (53104, 1331262), (53159, 13014), (53184, 201406), (53240, 54), (53428, 2646),
  (53482, 9633222), (53509, 54), (53520, 359054), (53590, 54), (53622, 58382),
  (53672, 2172366), (53716, 340182), (53721, 686), (53754, 1037678), (53769, 40966),
  (53790, 214694), (53832, 181198), (53874, 149686), (53914, 54), (53996, 54), (54033, 388966),
  (54077, 54), (54104, 4374), (54112, 341046), (54139, 705438), (54180, 187118), (54347, 486),
  (54391, 1115838), (54392, 7965198), (54447, 63598), (54482, 54), (54483, 77422),
  (54535, 36342), (54544, 224766), (54545, 123462), (54563, 2531358), (54594, 306718),
  (54616, 5238), (54643, 10212102), (54657, 36422), (54675, 118838), (54698, 54),
  (54714, 336166), (54724, 1285254), (54725, 2442582), (54732, 65174), (54752, 2135646),
  (54756, 186766), (54777, 119318)]

def WL22 : List (ℕ × ℕ) := [
  (54805, 50598), (54913, 467046), (54978, 23734), (54985, 747342), (55021, 54),
  (55083, 121718), (55093, 6174), (55183, 54), (55291, 1566), (55292, 54), (55319, 3243078),
  (55327, 205974), (55335, 20998), (55344, 151222), (55413, 77446), (55426, 54), (55427, 54),
  (55463, 282078), (55498, 341622), (55534, 2646), (55553, 192438), (55588, 55134),
  (55616, 54), (55624, 493326), (55777, 54), (55778, 646326), (55797, 158902),
  (55831, 5505678), (55832, 150606), (55854, 66622), (55858, 54), (55859, 54), (55876, 795726),
  (55956, 218222), (55993, 54), (55995, 481526), (56007, 23726), (56019, 474542), (56020, 54),
  (56021, 266598), (56055, 30398), (56074, 76734), (56128, 486), (56133, 323846),
  (56142, 27934), (56155, 54), (56156, 54), (56182, 5819094), (56264, 54), (56299, 1138446),
  (56318, 2646), (56343, 415238), (56349, 159398), (56371, 486), (56435, 198054),
  (56497, 1300878), (56506, 54), (56561, 54), (56565, 236798), (56589, 34862), (56601, 97574),
  (56615, 1636038), (56628, 66422), (56642, 54), (56651, 225846), (56733, 217654),
  (56777, 486), (56796, 196414), (56831, 54), (56853, 113846), (56884, 54), (56992, 54),
  (57065, 493758), (57073, 54), (57100, 918054), (57128, 1229526), (57154, 210006),
  (57155, 818694), (57183, 36878), (57273, 20078), (57297, 364214), (57371, 649998),
  (57397, 732942), (57398, 341766), (57451, 4858758), (57498, 75598), (57532, 10460934),
  (57533, 1566), (57546, 335246), (57559, 54), (57560, 494694), (57624, 90526), (57694, 54),
  (57722, 20142), (57735, 475414), (57812, 916038), (57837, 686), (57848, 180702), (57856, 54),
  (57857, 54), (57924, 377878), (57936, 1268414), (57960, 45622), (57981, 76094),
  (58002, 268486), (58011, 2692526), (58100, 54), (58197, 51862), (58242, 43982), (58262, 54),
  (58275, 54958), (58281, 155054), (58361, 1157094), (58386, 221294), (58443, 26126),
  (58487, 687294), (58504, 108918), (58505, 14958), (58596, 223598), (58613, 54),
  (58617, 85958), (58666, 54), (58693, 1566), (58694, 229014), (58721, 486), (58738, 637614),
  (58739, 1338894), (58746, 239678), (58774, 557982), (58866, 1647086), (58890, 237374),
  (58910, 54), (58914, 172222), (58926, 177286), (58932, 106814), (58941, 196982),
  (58965, 686), (59018, 54), (59064, 177686), (59099, 1661526), (59208, 106478), (59233, 5238),
  (59234, 54), (59241, 67582), (59316, 2703382), (59361, 334318), (59386, 401094), (59395, 54),
  (59396, 4806), (59423, 4806), (59442, 48838), (59450, 486), (59467, 6349086),
  (59521, 625302), (59557, 313902), (59577, 60182), (59583, 1162958), (59584, 54),
  (59585, 41526), (59604, 480574), (59634, 172358), (59639, 108918)]

def WL23 : List (ℕ × ℕ) := [
  (59729, 181854), (59746, 53838), (59961, 29782), (59994, 686), (60012, 193406), (60016, 486),
  (60044, 222966), (60048, 2313838), (60115, 345798), (60124, 21438), (60125, 1055214),
  (60151, 54), (60165, 20998), (60180, 89014), (60233, 460998), (60278, 706086), (60286, 4806),
  (60287, 2646), (60303, 106718), (60313, 4806), (60342, 99566), (60367, 1363662), (60368, 54),
  (60474, 27382), (60475, 54), (60486, 90878), (60489, 209158), (60556, 7259814),
  (60557, 100247814), (60564, 133582), (60657, 271774), (60684, 96542), (60709, 295398),
  (60719, 403758), (60745, 486), (60747, 81878), (60773, 617598), (60786, 20518), (60800, 54),
  (60864, 153982), (60880, 54), (60881, 53838), (60908, 486), (60962, 54), (60963, 126598),
  (61042, 1566), (61047, 514526), (61070, 1728054), (61097, 459702), (61101, 32278),
  (61122, 31342), (61123, 41526), (61124, 54), (61143, 39686), (61188, 22054), (61231, 292086),
  (61242, 180814), (61258, 54), (61259, 54), (61277, 408582), (61286, 54), (61326, 103606),
  (61339, 844614), (61367, 5238), (61420, 67446), (61440, 103022), (61447, 54),
  (61465, 721998), (61474, 10766358), (61501, 731862), (61502, 54), (61539, 429566),
  (61545, 366598), (61592, 1242342), (61619, 454446), (61691, 9767574), (61707, 208366),
  (61709, 179046), (61773, 104726), (61815, 197462), (61852, 5238), (61880, 93798),
  (61906, 54), (61907, 8161614), (61929, 179918), (61953, 686), (61969, 1047582),
  (61983, 152566), (62040, 87422), (62130, 3329678), (62139, 290126), (62160, 42278),
  (62169, 125942), (62203, 486), (62222, 7716726), (62223, 258374), (62230, 15174),
  (62235, 34334), (62247, 1782718), (62274, 196918), (62337, 4021814), (62379, 71206),
  (62419, 270486), (62456, 498438), (62481, 45062), (62501, 34614), (62509, 182934),
  (62518, 698094), (62662, 54), (62688, 1173158), (62689, 2119446), (62743, 54),
  (62789, 774054), (62797, 54), (62798, 4350942), (62816, 740574), (62824, 54), (62852, 4374),
  (62879, 8682174), (62907, 408878), (62923, 369774), (62932, 210438), (62960, 54),
  (62982, 135142), (63015, 93182), (63033, 421342), (63040, 13014), (63041, 54),
  (63081, 288806), (63093, 25238), (63104, 221814), (63121, 1566), (63135, 32638),
  (63147, 8230022), (63148, 2124414), (63149, 70254), (63194, 1558782), (63203, 54),
  (63264, 90982), (63303, 138238), (63310, 54), (63338, 486), (63365, 23382), (63391, 1566),
  (63392, 36342), (63509, 242982), (63544, 781038), (63553, 54), (63555, 97718),
  (63567, 164014), (63630, 5756614), (63657, 26902), (63693, 219158), (63824, 58806),
  (63831, 4638734), (63852, 205294), (63877, 54), (63932, 54), (63959, 10378422),
  (64012, 10777158), (64050, 27422), (64094, 21438), (64147, 486), (64170, 91942),
  (64174, 1566), (64202, 4806), (64282, 7800894), (64336, 1566918), (64427, 870894), (64498, 54)]

def WL24 : List (ℕ × ℕ) := [
  (64525, 54), (64526, 54), (64553, 486), (64569, 55054), (64580, 1566), (64589, 312318),
  (64626, 332518), (64661, 74142), (64741, 54), (64797, 395606), (64822, 54), (64842, 308054),
  (64850, 431622), (64876, 134622), (64911, 362126), (64975, 534078), (65040, 192766),
  (65065, 34614), (65066, 54), (65092, 466182), (65093, 1566), (65139, 686), (65175, 508982),
  (65227, 54), (65228, 54), (65263, 863046), (65282, 486), (65295, 62318), (65336, 54),
  (65424, 246286), (65457, 52526), (65497, 54), (65526, 22798), (65532, 21806),
  (65541, 146518), (65589, 367958), (65605, 486), (65610, 470486), (65631, 196454),
  (65687, 1757214), (65714, 1258038), (65722, 595278), (65739, 52166), (65799, 162038),
  (65921, 650358), (65956, 12582), (65975, 709974), (66029, 225846), (66036, 205046),
  (66038, 54), (66064, 54), (66072, 45134), (66118, 2003022), (66127, 527166), (66168, 686),
  (66171, 21958), (66186, 514918), (66199, 226854), (66227, 22086), (66254, 486), (66281, 54),
  (66317, 244206), (66334, 58806), (66366, 38854), (66424, 254574), (66438, 23726),
  (66443, 54), (66459, 88246), (66551, 54), (66597, 496646), (66603, 118886), (66604, 2614086),
  (66605, 466182), (66654, 65414), (66669, 86582), (66712, 54), (66766, 20142), (66767, 54),
  (66795, 29566), (66866, 391518), (66894, 55078), (66975, 91558), (66991, 510318),
  (67010, 10422), (67041, 395302), (67053, 38414), (67068, 42974), (67090, 5238),
  (67117, 11181294), (67144, 2100654), (67149, 21478), (67153, 1064862), (67172, 54),
  (67173, 116726), (67198, 259254), (67227, 58046), (67279, 54), (67314, 63134),
  (67333, 6618942), (67334, 76086), (67360, 54), (67398, 48742), (67415, 54), (67419, 93454),
  (67442, 76734), (67479, 251318), (67491, 3099446), (67495, 1350486), (67536, 192662),
  (67540, 6174), (67576, 54), (67604, 914598), (67657, 54), (67710, 4191766), (67739, 54),
  (67766, 5383206), (67811, 868302), (67887, 20078), (67900, 54), (67901, 54), (67935, 764614),
  (67981, 2646), (67986, 435038), (68062, 14958), (68080, 5622462), (68089, 377406),
  (68090, 1301886), (68144, 54), (68214, 25598), (68250, 483382), (68252, 93582),
  (68306, 2051838), (68333, 1883358), (68343, 66398), (68391, 2857294), (68441, 486),
  (68454, 20798), (68469, 47758), (68494, 8712414), (68496, 89774), (68508, 468374),
  (68544, 1758734), (68601, 108166), (68629, 63774), (68630, 54), (68647, 352062),
  (68657, 14526), (68724, 69766), (68769, 282622), (68791, 110862), (68819, 210006),
  (68823, 26518), (68854, 612702), (68899, 54), (68927, 486), (68949, 87734), (68973, 99838),
  (68980, 1009854), (69034, 54), (69035, 4806), (69141, 60238), (69196, 54), (69222, 116222),
  (69250, 486), (69322, 372942), (69358, 64854), (69440, 54), (69466, 80406), (69525, 270566),
  (69547, 13014), (69575, 3354534), (69600, 5616686), (69602, 41742), (69628, 54), (69629, 54),
  (69651, 2960246), (69673, 684198), (69683, 54), (69690, 54182), (69719, 266022),
  (69756, 124094), (69763, 54), (69792, 24902)]

def WL25 : List (ℕ × ℕ) := [
  (69924, 324182), (69930, 45502), (69952, 54), (69971, 763326), (70070, 279198),
  (70088, 2646), (70161, 51878), (70169, 12053718), (70185, 349174), (70187, 1227726),
  (70218, 34862), (70222, 486), (70284, 3919118), (70331, 54), (70332, 1368766),
  (70385, 1137726), (70407, 36742), (70411, 6590214), (70412, 54), (70428, 187526),
  (70434, 251078), (70440, 170398), (70455, 70214), (70491, 358702), (70520, 54),
  (70528, 6174), (70573, 54), (70574, 1566), (70601, 3206358), (70626, 1609846),
  (70645, 385326), (70716, 190222), (70735, 54), (70736, 54), (70755, 97222), (70905, 29774),
  (70925, 794718), (70929, 267118), (70978, 22086), (71006, 929286), (71058, 64126),
  (71059, 10638), (71070, 52214), (71114, 486), (71167, 228366), (71168, 54), (71205, 1738286),
  (71214, 686), (71217, 454774), (71302, 54), (71329, 54), (71330, 60966), (71410, 2646),
  (71411, 235494), (71456, 777726), (71492, 54), (71517, 37358), (71520, 59222),
  (71545, 148662), (71553, 10702382), (71654, 10823598), (71673, 304406), (71707, 54),
  (71730, 22894), (71762, 3361014), (71793, 151966), (71896, 20142), (71897, 54),
  (71904, 176158), (71923, 4374), (71951, 810702), (71976, 60638), (72059, 64854),
  (72086, 486), (72105, 391814), (72112, 54), (72113, 54), (72189, 35806), (72193, 54),
  (72194, 1050462), (72220, 54), (72342, 7972006), (72387, 62462), (72518, 54),
  (72598, 3072438), (72618, 195758), (72625, 54), (72672, 4735958), (72680, 13014),
  (72693, 35414), (72732, 195694), (72760, 1473174), (72787, 1566), (72815, 2076678),
  (72841, 54), (72868, 8422326), (72869, 1892862), (72885, 82702), (72948, 34406), (73030, 54),
  (73192, 54), (73247, 54), (73254, 36758), (73299, 452126), (73311, 422542), (73354, 7085502),
  (73400, 795222), (73408, 54), (73409, 59238), (73436, 10638), (73491, 331046),
  (73500, 77134), (73516, 54), (73518, 2490278), (73527, 553838), (73599, 2884862),
  (73615, 6174), (73626, 396182), (73652, 54), (73683, 225086), (73714, 6174), (73719, 307742),
  (73733, 794718), (73787, 4374), (73841, 1965654), (73894, 1577286), (73921, 54),
  (73926, 78742), (73956, 34094), (73959, 3865022), (74002, 54), (74003, 133542),
  (74055, 199646), (74057, 452411838), (74083, 1566), (74093, 291366), (74138, 54),
  (74165, 11346102), (74181, 273958), (74184, 25838), (74299, 54), (74300, 23382),
  (74301, 686), (74326, 54), (74380, 54), (74382, 1610254), (74400, 247646), (74409, 262286),
  (74466, 82358), (74480, 479646), (74489, 1566), (74508, 20534), (74570, 54), (74580, 41486),
  (74596, 5739174), (74633, 1660374), (74678, 1853766), (74712, 41486), (74732, 1276182),
  (74776, 257454), (74781, 258574), (74786, 579582), (74829, 36574), (74867, 102006),
  (74886, 47326), (74893, 154494), (74920, 1683342), (74929, 481158), (74940, 507302),
  (74948, 54), (74975, 1393254), (74976, 128542), (75012, 6221654), (75028, 22734),
  (75042, 133582), (75081, 347678), (75082, 136566), (75109, 54), (75137, 54), (75168, 25526),
  (75199, 1216422), (75271, 54), (75282, 1168454), (75353, 54), (75433, 423414), (75460, 54),
  (75461, 54), (75515, 8202654), (75615, 503246), (75622, 8542206), (75676, 39582),
  (75677, 54), (75747, 110678)]

def WL26 : List (ℕ × ℕ) := [
  (75780, 25598), (75811, 486), (75829, 1035486), (75839, 44334), (75865, 54), (75866, 54),
  (75919, 76734), (76020, 97502), (76027, 35694), (76046, 401094), (76065, 1499302),
  (76074, 73774), (76081, 10422), (76099, 181422), (76104, 98782), (76161, 56822),
  (76162, 10422), (76172, 283158), (76189, 14526), (76217, 43254), (76271, 413046),
  (76305, 2139238), (76326, 30598), (76359, 686), (76362, 27926), (76389, 43198),
  (76406, 7995942), (76449, 29182), (76460, 486), (76505, 896094), (76554, 70166),
  (76567, 7006446), (76594, 54), (76605, 1180214), (76656, 261062), (76665, 20534),
  (76702, 1611414), (76757, 437454), (76767, 21278), (76801, 6174), (76810, 41094),
  (76811, 54), (76935, 12337414), (76986, 172982), (77008, 242982), (77045, 549486),
  (77103, 2662), (77134, 581526), (77161, 54), (77162, 54), (77215, 1674054),
  (77216, 10985166), (77242, 2646), (77253, 1042318), (77292, 240742), (77324, 804438),
  (77337, 34654), (77351, 1626318), (77358, 360574), (77404, 15174), (77406, 53854),
  (77436, 216262), (77485, 45414), (77539, 54), (77567, 54), (77589, 131438), (77670, 78646),
  (77694, 64406), (77701, 627534), (77742, 241078), (77793, 43222), (77863, 54), (77890, 54),
  (77891, 1566), (77898, 29686), (77940, 2336414), (77979, 175022), (77980, 408222),
  (78006, 173702), (78026, 2646), (78106, 54), (78107, 54), (78174, 28894), (78183, 252454),
  (78188, 54), (78213, 22886), (78241, 486), (78296, 54), (78350, 54), (78395, 275166),
  (78426, 34246), (78430, 76086), (78441, 22006), (78458, 16036974), (78538, 9725886),
  (78602, 905166), (78701, 54), (78702, 10237358), (78708, 551438), (78727, 696438),
  (78741, 67846), (78755, 3712662), (78836, 2253366), (78862, 12334734), (78997, 54),
  (79025, 54), (79106, 54), (79143, 155734), (79232, 507798), (79240, 3500118),
  (79267, 611766), (79284, 29662), (79304, 1249686), (79308, 24694), (79322, 35262),
  (79348, 2646), (79402, 9493902), (79429, 12582), (79430, 54), (79437, 28174), (79456, 486),
  (79484, 54), (79546, 698094), (79548, 20542), (79575, 36614), (79591, 747414),
  (79602, 862982), (79610, 907398), (79623, 288758), (79707, 39454), (79789, 6174),
  (79808, 34614), (79830, 25294), (79835, 54), (79888, 477168462), (79953, 458534),
  (80032, 224838), (80067, 28102), (80078, 54), (80079, 288902), (80131, 54),
  (80132, 478169838), (80159, 6534), (80185, 47142), (80193, 146966), (80213, 54), (80320, 54),
  (80428, 486), (80529, 34702), (80536, 219942), (80537, 12495654), (80564, 54),
  (80571, 88174), (80574, 686), (80617, 1566), (80652, 123742), (80715, 76606),
  (80717, 790974), (80761, 524358), (80771, 410598), (80779, 54), (80780, 1084806),
  (80781, 78902), (80787, 24214), (80814, 29366), (80877, 85366), (80914, 486),
  (80943, 247262), (80968, 54), (80969, 54), (81104, 54), (81130, 1566), (81157, 486),
  (81185, 6776838), (81210, 1581622), (81324, 68566), (81346, 1554606), (81438, 454726),
  (81454, 54), (81455, 1780758), (81504, 686), (81508, 4798062), (81509, 54), (81570, 102766),
  (81590, 54), (81606, 387526), (81608, 276894)]

def WL27 : List (ℕ × ℕ) := [
  (81669, 44566), (81670, 54), (81671, 54), (81711, 98678), (81752, 54), (81779, 54),
  (81824, 16197822), (81859, 54), (81878, 1187118), (81909, 52454), (81940, 9597582),
  (81994, 2646), (81995, 2646), (82021, 22086), (82049, 898614), (82089, 60638),
  (82210, 3436182), (82237, 54), (82278, 23054), (82319, 151902), (82398, 162406),
  (82404, 21334), (82431, 24502), (82507, 54), (82508, 54), (82533, 686), (82584, 221846),
  (82588, 4601502), (82615, 486), (82643, 10422), (82669, 1836054), (82671, 65942),
  (82698, 46142), (82769, 1707246), (82805, 20142), (82818, 78238), (82822, 1147374),
  (82831, 54), (82858, 4374), (82885, 54), (82913, 21438), (82930, 1194462), (82993, 94662),
  (83022, 99422), (83075, 54), (83133, 133526), (83155, 55134), (83165, 197622),
  (83172, 84886), (83209, 292518), (83223, 479702), (83237, 54), (83291, 703998),
  (83299, 380502), (83322, 61286), (83344, 4234518), (83398, 1243134), (83452, 14526),
  (83466, 41086), (83561, 54), (83562, 818398), (83601, 25238), (83614, 54), (83643, 294214),
  (83649, 44606), (83661, 686), (83685, 287486), (83722, 150606), (83750, 805302),
  (83754, 8796982), (83776, 711558), (83803, 54), (83804, 1321542), (83830, 486),
  (83831, 2217942), (83841, 49094), (83858, 5429646), (83939, 54), (83966, 54), (83973, 51286),
  (84101, 2646), (84219, 26342), (84225, 116414), (84236, 117126), (84245, 466902),
  (84344, 54), (84370, 3978774), (84498, 29558), (84505, 54), (84576, 35582), (84587, 54),
  (84591, 686), (84659, 1338534), (84694, 2112102), (84695, 54), (84750, 131678),
  (84775, 16593606), (84777, 237142), (84838, 740358), (84901, 1008702), (84937, 54),
  (84938, 151902), (84965, 486), (84992, 54), (85035, 2553622), (85038, 31574), (85072, 54),
  (85091, 713862), (85099, 14320206), (85119, 126598), (85128, 161254), (85176, 57742),
  (85181, 41094), (85191, 48182), (85234, 6325182), (85315, 1566), (85343, 194022),
  (85356, 79102), (85387, 607302), (85424, 9570582), (85434, 140398), (85478, 14526),
  (85504, 88398), (85640, 54), (85689, 217174), (85694, 14172246), (85719, 686), (85721, 1566),
  (85748, 54), (85801, 6038334), (85854, 326518), (85909, 262494), (85926, 218846),
  (85937, 486), (85963, 501274062), (85964, 1346814), (86017, 486), (86043, 365702),
  (86062, 6174), (86064, 29542), (86071, 54), (86094, 238726), (86127, 1583342),
  (86178, 2439118), (86206, 54), (86234, 1566), (86260, 8972046), (86315, 54), (86368, 133542),
  (86395, 22734), (86423, 486), (86430, 29774), (86449, 73494), (86450, 54), (86477, 2611062),
  (86493, 124702), (86557, 40878), (86613, 67294), (86625, 20918), (86666, 4790502),
  (86675, 794358), (86683, 637542), (86745, 404654), (86756, 5831262), (86774, 54),
  (86793, 59222), (86800, 54), (86801, 54), (86808, 1908694), (86809, 1376766), (86855, 19494),
  (86886, 471494), (86900, 392166), (86935, 2045142), (86952, 371134), (86955, 40822),
  (86962, 15219198), (86976, 240566), (87015, 92366), (87043, 227718), (87053, 295686),
  (87061, 383814), (87152, 486), (87177, 2662), (87205, 14556294), (87260, 1108134),
  (87340, 54), (87341, 54), (87367, 229662), (87390, 20078), (87393, 432518), (87395, 486),
  (87450, 98062), (87483, 989702), (87528, 366902), (87530, 35262), (87610, 4541886),
  (87611, 880254), (87645, 69214), (87673, 410526), (87684, 2039222), (87764, 1295694),
  (87772, 3099006), (87777, 686), (87827, 54), (87885, 227446), (87934, 54), (87935, 3887406),
  (87989, 41526), (88016, 54)]

def WL28 : List (ℕ × ℕ) := [
  (88097, 54), (88124, 486), (88150, 54), (88164, 162166), (88258, 54), (88263, 119446),
  (88296, 30214), (88313, 22086), (88326, 21446), (88340, 2903742), (88440, 109958),
  (88474, 54), (88501, 54), (88502, 54), (88545, 475262), (88573, 215766), (88627, 193302),
  (88744, 54), (88825, 54), (88845, 372046), (88879, 54), (88908, 269278), (89041, 195318),
  (89042, 54), (89055, 84758), (89076, 1176646), (89082, 2662), (89122, 14653494),
  (89196, 8054542), (89203, 6534), (89284, 2447766), (89285, 54), (89298, 113654),
  (89340, 33622), (89382, 13718), (89384, 697446), (89392, 54), (89397, 258758),
  (89403, 72262), (89409, 27718), (89419, 4374), (89427, 11404102), (89451, 499558),
  (89474, 50598), (89528, 54), (89550, 6944174), (89592, 88406), (89622, 21542),
  (89634, 38326), (89649, 191606), (89662, 192942), (89679, 37342), (89689, 54), (89690, 54),
  (89725, 733878), (89736, 686), (89802, 131798), (89805, 59518), (89811, 333358), (89851, 54),
  (89879, 54), (89932, 2646), (90041, 8550414), (90068, 486), (90095, 54), (90102, 468646),
  (90175, 54), (90202, 6534), (90203, 54), (90210, 57406), (90364, 54), (90365, 10638),
  (90418, 54), (90419, 5507622), (90420, 215686), (90441, 168382), (90498, 234662),
  (90580, 266598), (90581, 6663438), (90608, 187326), (90634, 486), (90662, 4806),
  (90714, 24022), (90742, 17119566), (90770, 262494), (90823, 112806), (90824, 54),
  (90900, 495182), (90915, 78998), (90932, 1566), (90958, 2136294), (90977, 1420542),
  (90986, 4394142), (91013, 54), (91041, 84278), (91047, 118886), (91131, 33262), (91147, 54),
  (91155, 560926), (91170, 2662), (91188, 80702), (91212, 24334), (91254, 66806),
  (91255, 2646), (91256, 2646), (91257, 54478), (91274, 1534446), (91309, 1566),
  (91336, 112374), (91363, 95742), (91364, 2478438), (91464, 158854), (91498, 54),
  (91526, 486), (91527, 58486), (91575, 23974), (91596, 23726), (91714, 6013494),
  (91715, 1566), (91769, 7356582), (91796, 9108558), (91877, 54), (91893, 933646), (91957, 54),
  (91968, 115118), (92007, 48502), (92031, 227182), (92038, 20142), (92065, 54), (92066, 54),
  (92092, 14094), (92120, 54), (92157, 385598), (92209, 1194174), (92236, 302526),
  (92255, 486), (92286, 199534), (92290, 543798), (92301, 399598), (92363, 54),
  (92367, 154478), (92370, 86974), (92373, 23038), (92398, 1001358), (92443, 54),
  (92463, 242534), (92475, 422494), (92552, 35694), (92579, 55566), (92587, 322398),
  (92601, 2662262), (92605, 54), (92619, 36254), (92625, 312694), (92632, 54),
  (92676, 1748222), (92686, 54), (92687, 54), (92750, 219798), (92751, 7235582), (92794, 54),
  (92848, 3268134), (92850, 55486), (92889, 190054), (92922, 686), (92961, 35918),
  (92988, 26326), (92997, 84046), (93037, 54), (93078, 752086), (93092, 54), (93118, 2646),
  (93126, 79022), (93156, 247966), (93192, 141646), (93199, 6442038), (93204, 45742),
  (93219, 92702), (93254, 73494), (93270, 149654), (93280, 5238), (93375, 380678),
  (93379, 290502), (93399, 93614), (93456, 37958), (93470, 4374), (93522, 2011382),
  (93541, 520686), (93550, 486), (93577, 54), (93613, 289206), (93618, 76598),
  (93641, 1187334), (93648, 93286), (93651, 88766), (93686, 13244526), (93708, 26342),
  (93717, 116726), (93739, 54), (93759, 77398), (93767, 54), (93819, 272134), (93820, 54),
  (93848, 14071374), (93902, 2646), (93983, 15174), (94080, 124918), (94171, 54),
  (94172, 137646), (94207, 1174302), (94253, 231606), (94269, 22054), (94333, 54),
  (94334, 1566), (94352, 267606), (94387, 54), (94389, 47942), (94396, 181854), (94414, 54),
  (94458, 490822), (94495, 54), (94576, 3726054), (94585, 577062), (94631, 54),
  (94680, 203054), (94698, 38366), (94710, 28286)]

def WL29 : List (ℕ × ℕ) := [
  (94739, 54), (94743, 62102), (94792, 14958), (94803, 20782), (94891, 487926), (94900, 54),
  (94927, 2005398), (94955, 54), (94962, 23486), (94981, 54), (94982, 13309326),
  (95019, 6597494), (95061, 76654), (95062, 1933254), (95116, 1033614), (95117, 1566),
  (95144, 54), (95153, 1087974), (95163, 2662), (95171, 486), (95184, 507622), (95226, 526478),
  (95265, 100174), (95278, 80406), (95279, 27486), (95323, 8847342), (95342, 510318),
  (95360, 54), (95397, 111422), (95403, 89294), (95472, 54542), (95522, 54), (95529, 47438),
  (95549, 10733094), (95556, 118814), (95567, 6174), (95657, 1841454), (95683, 54),
  (95710, 54), (95711, 54), (95730, 32902), (95765, 54), (95828, 448326), (95837, 544878),
  (95853, 161198), (95901, 160814), (95907, 354566), (95954, 54), (95971, 525222),
  (95982, 194254), (95997, 602606), (95998, 953118), (96007, 6979662), (96008, 2646),
  (96035, 5238), (96053, 1073718), (96063, 38414), (96115, 173718), (96116, 313254),
  (96251, 12884238), (96278, 11225358), (96321, 440302), (96332, 54), (96357, 480742),
  (96413, 1566), (96466, 4321998), (96468, 46406), (96494, 138896262), (96504, 83038),
  (96521, 54), (96565, 519174), (96600, 272686), (96602, 19494), (96609, 28646),
  (96633, 8667718), (96642, 54086), (96655, 54), (96656, 54), (96741, 1423958),
  (96781, 487638), (96817, 10780398), (96818, 5903334), (96845, 54), (96880, 917478),
  (96885, 27814), (96899, 6905358), (96930, 68078), (96978, 4215398), (96987, 35942),
  (97006, 17269254), (97007, 54), (97025, 350694), (97026, 23854), (97060, 1566),
  (97069, 505566), (97087, 2646), (97113, 65126), (97151, 1162422), (97168, 9315918),
  (97223, 54), (97249, 23382), (97278, 327694), (97293, 124382), (97326, 29782),
  (97331, 17699094), (97344, 283942), (97349, 290502), (97358, 486), (97411, 12582),
  (97412, 71334), (97431, 4692622), (97509, 21718), (97510, 963126), (97536, 30398),
  (97564, 205974), (97573, 1566), (97601, 169614), (97610, 1381878), (97655, 114966),
  (97665, 166406), (97677, 26822), (97690, 744318), (97708, 54), (97735, 54), (97736, 54),
  (97764, 47942), (97771, 801126), (97870, 2646), (97897, 54), (97944, 68974),
  (97988, 8637534), (97995, 92198), (98033, 5238), (98067, 83006), (98070, 263542),
  (98139, 48214), (98148, 51286), (98167, 4374), (98194, 54), (98195, 54), (98222, 54),
  (98229, 338854), (98275, 54), (98328, 254798), (98329, 3609846), (98330, 10103454),
  (98384, 420606), (98456, 355086), (98505, 281174), (98517, 275414), (98537, 345798),
  (98545, 54), (98601, 23942), (98649, 143614), (98653, 496206), (98680, 54), (98681, 523206),
  (98706, 174646), (98708, 13014), (98761, 4806), (98762, 189486), (98763, 24334),
  (98789, 77382), (98950, 54), (98951, 54), (98959, 225702), (98997, 239414), (99031, 54),
  (99049, 193014), (99113, 2096982), (99139, 1367118), (99141, 60854), (99156, 2662),
  (99194, 2646), (99237, 165694), (99247, 54), (99248, 15174), (99275, 12582),
  (99291, 1700398), (99436, 54), (99437, 51894), (99441, 274798), (99490, 19494),
  (99582, 371974), (99652, 13458366), (99723, 22798), (99734, 36342), (99780, 143326),
  (99815, 1768014), (99868, 486), (99896, 54), (99897, 184774), (99923, 54), (99930, 84782),
  (99976, 54), (100084, 54), (100161, 154894), (100165, 15174), (100219, 199638), (100220, 54),
  (100233, 36742), (100246, 54), (100260, 102766), (100301, 54), (100338, 53398),
  (100353, 24646), (100381, 21438), (100382, 54), (100409, 54), (100517, 23814),
  (100536, 114094), (100543, 54), (100560, 695246), (100570, 54), (100571, 54),
  (100624, 13014), (100651, 35694), (100659, 45358), (100679, 2411694), (100728, 202054),
  (100737, 223198), (100813, 54), (100814, 295758), (100815, 179318), (100851, 254102),
  (100884, 94246), (100890, 52222), (100920, 134782), (100921, 2579526), (101003, 95742),
  (101030, 152982), (101052, 366526), (101061, 2662), (101064, 72526), (101137, 466182),
  (101192, 54), (101218, 54), (101220, 191894), (101229, 38102), (101241, 388142),
  (101300, 2646), (101317, 267966), (101353, 28134), (101354, 54), (101376, 611566),
  (101403, 293486), (101436, 98062), (101443, 760302), (101497, 179046), (101547, 27382),
  (101583, 27358), (101597, 2724894)]

def WL30 : List (ℕ × ℕ) := [
  (101641, 597582), (101682, 348182), (101704, 54), (101733, 64982), (101759, 54),
  (101921, 14516118), (101947, 54), (101964, 49934), (101975, 356238), (102002, 51894),
  (102009, 58462), (102066, 58622), (102109, 20142), (102145, 499734), (102191, 54),
  (102244, 54), (102255, 62494), (102285, 56198), (102290, 212526), (102325, 54),
  (102352, 572454), (102353, 54), (102366, 8155174), (102402, 93286), (102411, 235918),
  (102433, 54), (102487, 18846), (102488, 77382), (102594, 148726), (102649, 41526),
  (102669, 397006), (102704, 486), (102730, 54), (102738, 68942), (102783, 64958),
  (102838, 54), (102846, 205822), (102879, 450046), (102892, 54), (102893, 5636574),
  (102921, 364054), (102993, 59966), (102996, 688286), (103026, 156518), (103027, 486),
  (103047, 118838), (103054, 1937142), (103065, 2748998), (103113, 686), (103131, 394414),
  (103136, 881982), (103146, 301934), (103163, 2646), (103194, 77582), (103216, 54),
  (103224, 498878), (103244, 54), (103278, 184438), (103293, 206462), (103297, 3291894),
  (103361, 1019862), (103378, 54), (103392, 48494), (103396, 1232046), (103458, 26438),
  (103476, 33742), (103487, 10422), (103496, 198054), (103515, 137086), (103608, 43822),
  (103621, 54), (103640, 812502), (103648, 54), (103649, 54), (103683, 219638),
  (103702, 616518), (103703, 1360206), (103810, 54), (103851, 55078), (103854, 256294),
  (103865, 4133214), (103923, 3151846), (103959, 82286), (103972, 91422), (103973, 54),
  (103991, 5975334), (104026, 54), (104027, 54), (104055, 349054), (104085, 105766),
  (104142, 933646), (104215, 1057158), (104223, 3018958), (104225, 283086), (104242, 467046),
  (104378, 54), (104431, 54), (104432, 54), (104442, 82886), (104512, 54), (104540, 54702),
  (104584, 6174), (104593, 12582), (104594, 54), (104630, 304686), (104701, 54),
  (104718, 300598), (104728, 5585598), (104783, 697518), (104841, 214454), (104872, 528534),
  (104917, 4071006), (104918, 54), (104945, 54), (104970, 154646), (104998, 57294),
  (105025, 2646), (105124, 227646), (105187, 54), (105188, 54), (105204, 508142),
  (105210, 145006), (105233, 1063494), (105251, 796734), (105259, 1182726), (105378, 23038),
  (105485, 54), (105511, 54), (105565, 54), (105566, 12582), (105618, 71822), (105700, 486),
  (105727, 54), (105737, 858798), (105754, 54), (105790, 588726), (105808, 2646),
  (105809, 76734), (105849, 563366), (105882, 69518), (105889, 54), (105917, 54),
  (105952, 401454), (105961, 843606), (105971, 54), (106052, 54), (106056, 352246),
  (106078, 57726), (106079, 45414), (106106, 486), (106134, 273062), (106151, 11609766),
  (106160, 54), (106230, 24326), (106290, 96238), (106294, 185382), (106295, 6534),
  (106321, 7267374), (106322, 10638), (106359, 379486), (106402, 54), (106448, 519678),
  (106456, 546534), (106457, 12582), (106538, 54), (106617, 24974), (106646, 222966),
  (106699, 187974), (106779, 3123494), (106780, 250398), (106807, 51894), (106835, 136566),
  (106861, 54), (106863, 157958), (106888, 64854), (106969, 1191726), (107050, 20142),
  (107051, 54), (107115, 30182), (107142, 3431318), (107149, 330678), (107211, 58382),
  (107217, 141902), (107229, 1913254), (107339, 258246), (107374, 54), (107401, 317358),
  (107424, 119942), (107437, 562158), (107455, 54), (107550, 188126), (107564, 486),
  (107599, 1801854), (107655, 25526), (107671, 573344622), (107724, 60374), (107743, 1290798),
  (107752, 440046), (107753, 40878), (107808, 54974), (107833, 54), (107834, 54),
  (107862, 98662), (107915, 574029774), (107932, 1219014), (107994, 131966), (107996, 54),
  (108023, 28134), (108051, 1702126), (108081, 56806), (108096, 62518), (108120, 79006),
  (108158, 1566), (108184, 54), (108185, 54), (108204, 34406), (108234, 181942),
  (108267, 52214), (108320, 54), (108428, 1566), (108445, 1054422), (108509, 5238),
  (108526, 1100718), (108527, 490302)]

def WL31 : List (ℕ × ℕ) := [
  (108576, 84646), (108589, 13014), (108687, 43574), (108690, 621542), (108725, 54),
  (108779, 844182), (108797, 10318518), (108806, 5408262), (108831, 158758), (108859, 486),
  (108879, 314414), (108886, 54), (108887, 54), (108969, 2721086), (108995, 54),
  (109017, 74678), (109048, 36342), (109076, 44334), (109130, 5238), (109137, 30166),
  (109219, 267606), (109237, 19494), (109238, 2646), (109282, 433638), (109292, 54),
  (109293, 628814), (109317, 112246), (109345, 486), (109363, 365166), (109368, 216374),
  (109373, 23382), (109453, 154494), (109534, 54), (109615, 5238), (109634, 1101798),
  (109643, 1121742), (109662, 546734), (109670, 3074598), (109680, 1574566), (109697, 54),
  (109710, 354862), (109728, 1115534), (109761, 57158), (109777, 2646), (109778, 955206),
  (109821, 64822), (109858, 54), (109877, 649206), (109886, 4806), (109929, 133046),
  (109984, 303174), (110012, 330822), (110021, 656046), (110047, 54), (110074, 292086),
  (110109, 41222), (110129, 23382), (110133, 59062), (110136, 3446806), (110172, 257366),
  (110182, 126414), (110264, 13014), (110280, 622838), (110292, 141278), (110307, 233158),
  (110316, 1699222), (110317, 23814), (110340, 20134), (110361, 20542), (110364, 63286),
  (110381, 1039158), (110412, 131926), (110426, 54), (110452, 54), (110480, 8738766),
  (110507, 1379646), (110668, 54), (110696, 54), (110727, 106462), (110803, 486),
  (110830, 6323886), (110832, 116542), (110857, 54), (110858, 14958), (110910, 26902),
  (110920, 323262), (111019, 54), (111020, 54), (111046, 486), (111100, 1050462),
  (111101, 582721182), (111144, 29566), (111235, 9437742), (111253, 973638), (111263, 54),
  (111264, 4141318), (111281, 391806), (111285, 27358), (111294, 130478), (111363, 155494),
  (111420, 27758), (111424, 2012958), (111425, 54), (111480, 317854), (111483, 39374),
  (111523, 305334), (111532, 3050622), (111540, 20798), (111559, 2566782), (111587, 3636846),
  (111741, 90358), (111748, 54), (111749, 5238), (111803, 54), (111865, 1075878),
  (111884, 2646), (111902, 514422), (111911, 54), (112065, 555382), (112072, 6534),
  (112113, 50494), (112128, 427318), (112154, 54), (112181, 12208806), (112208, 54),
  (112217, 268038), (112289, 4806), (112316, 32454), (112370, 54), (112397, 92934),
  (112414, 879462), (112478, 32454), (112482, 46262), (112491, 569678), (112504, 130734),
  (112531, 54), (112559, 54), (112621, 744966), (112650, 540598), (112667, 486),
  (112720, 1566), (112734, 2143654), (112803, 472814), (112845, 36878), (112848, 86902),
  (112882, 3198582), (112910, 486), (112936, 18503046), (112937, 501174), (112946, 925758),
  (112995, 65662), (113017, 15174), (113044, 54), (113045, 54), (113098, 7638894),
  (113099, 46278), (113125, 54), (113127, 604246), (113163, 99478), (113169, 279998),
  (113211, 399934), (113233, 7342974), (113256, 2033206), (113261, 2877174), (113295, 169718),
  (113296, 597798), (113297, 708678), (113332, 1061622), (113349, 2043166), (113352, 289342),
  (113388, 12056678), (113403, 83006), (113422, 54), (113433, 58678), (113450, 27486),
  (113504, 54), (113547, 222542), (113556, 40126), (113574, 124598), (113583, 83222),
  (113584, 53838), (113639, 14094), (113674, 771462), (113679, 500102), (113688, 112862),
  (113693, 54), (113738, 274662), (113745, 66574), (113746, 589577022), (113747, 256662),
  (113773, 780246), (113827, 229014), (113846, 1640502), (113881, 3107646), (114016, 1566),
  (114070, 5048622), (114079, 764838), (114098, 108918), (114179, 54), (114188, 6174),
  (114232, 5913702), (114233, 54), (114240, 56878), (114260, 54), (114296, 1308222),
  (114339, 234142), (114366, 275038), (114421, 54), (114432, 461678), (114476, 54),
  (114531, 686), (114637, 54), (114638, 423414), (114651, 70054), (114665, 4806), (114746, 54),
  (114786, 247606), (114799, 421254), (114827, 54), (114854, 11110446), (114907, 54),
  (114961, 54), (114966, 589462), (115043, 93582), (115059, 116302), (115068, 7073086),
  (115069, 76734), (115087, 1641294), (115101, 254726), (115124, 54), (115128, 5731286),
  (115143, 93446), (115186, 1204614), (115204, 54), (115218, 4956886), (115232, 862542),
  (115275, 95198), (115276, 1173222), (115285, 22734), (115338, 3252022), (115353, 102694),
  (115367, 54), (115411, 207342), (115422, 330662), (115428, 30518), (115485, 42814),
  (115520, 1066302), (115521, 114118), (115527, 349886), (115547, 346806), (115555, 4806),
  (115560, 686), (115609, 1727838), (115663, 4374), (115690, 718686)]

def WL32 : List (ℕ × ℕ) := [
  (115717, 54), (115809, 45398), (115842, 113998), (115853, 2646), (115863, 43534),
  (115880, 54), (115935, 100262), (115961, 54), (115989, 168926), (115992, 75974),
  (116095, 54), (116096, 2358774), (116103, 57254), (116123, 54), (116149, 6608142),
  (116247, 70054), (116256, 114382), (116258, 8426646), (116268, 161134), (116276, 123462),
  (116284, 12582), (116303, 852318), (116338, 6534), (116500, 1709478), (116508, 38966),
  (116544, 108182), (116555, 486), (116556, 64502), (116589, 686), (116608, 54),
  (116653, 1093734), (116663, 54), (116689, 2530062), (116697, 137366), (116698, 776718),
  (116753, 1246734), (116775, 24902), (116825, 54), (116852, 54), (116905, 54),
  (116907, 137854), (116982, 41102), (117032, 6601734), (117033, 2662), (117054, 106478),
  (117067, 5168502), (117095, 10289646), (117175, 12582), (117249, 99838), (117256, 54),
  (117257, 54), (117300, 251422), (117311, 54), (117348, 93494), (117391, 1009854),
  (117411, 232478), (117419, 1386342), (117423, 36422), (117468, 421438), (117472, 5238),
  (117519, 686), (117553, 54), (117580, 54), (117588, 420694), (117607, 1174662),
  (117618, 2206862), (117661, 54), (117662, 28566), (117707, 1392462), (117733, 184806),
  (117742, 54), (117774, 289766), (117780, 1797622), (117797, 36342), (117805, 196254),
  (117810, 38846), (117824, 1566), (117833, 1881774), (117852, 421678), (117885, 291022),
  (117985, 4806), (118004, 404046), (118039, 54), (118147, 13138254), (118173, 28606),
  (118201, 1566), (118202, 54), (118203, 289582), (118228, 13092246), (118266, 281326),
  (118336, 257094), (118350, 162094), (118363, 54), (118390, 54), (118391, 22734),
  (118435, 822438), (118445, 54), (118526, 54), (118552, 54), (118572, 406414),
  (118634, 173718), (118687, 54), (118715, 54), (118761, 25822), (118768, 54),
  (118778, 681678), (118840, 1665054), (118876, 54), (118930, 10638), (118931, 54),
  (118977, 21446), (118995, 201046), (119028, 332438), (119038, 2646), (119058, 60542),
  (119075, 1334574), (119085, 392542), (119093, 5889942), (119106, 73558), (119119, 1122606),
  (119120, 302238), (119139, 175438), (119173, 54), (119232, 199942), (119281, 92934),
  (119282, 54), (119391, 97222), (119406, 155174), (119427, 134086), (119498, 1292814),
  (119524, 54), (119547, 57326), (119551, 3143934), (119659, 54), (119685, 24758),
  (119691, 142838), (119695, 23958), (119714, 4374), (119736, 40102), (119740, 54),
  (119741, 47358), (119793, 25342), (119821, 54), (119822, 2646), (119895, 341798),
  (119903, 1566), (119929, 1252638), (119940, 120886), (119952, 31454), (119964, 349982),
  (119967, 299254), (120037, 39366), (120063, 33526), (120064, 17517438), (120065, 54),
  (120263, 6174), (120280, 10894662), (120282, 24326), (120308, 54), (120335, 54),
  (120363, 120278), (120444, 38102), (120450, 2036854), (120497, 5180166), (120546, 209998),
  (120569, 308214), (120596, 398646), (120612, 44566), (120631, 23382), (120632, 20233854),
  (120658, 249534), (120686, 14094), (120735, 49814), (120794, 1226934), (120821, 5775678),
  (120902, 91422), (120919, 764334), (120924, 167686), (120965, 933102), (120972, 601246),
  (121086, 127598), (121108, 246798), (121126, 1212102), (121144, 54), (121170, 626302),
  (121198, 5816502), (121203, 23678), (121252, 486), (121298, 505782), (121360, 43038),
  (121415, 486), (121424, 593478), (121458, 25238), (121459, 212958), (121515, 28894),
  (121522, 47358), (121604, 5238), (121631, 6534), (121635, 4333462), (121658, 486),
  (121668, 161374), (121734, 686), (121764, 102878), (121765, 54), (121783, 1173942),
  (121792, 6196446), (121793, 14526), (121806, 57238), (121927, 54), (121954, 54),
  (121956, 52502), (121973, 829854), (122116, 1566), (122117, 54), (122142, 53758),
  (122144, 486), (122162, 297846), (122197, 2445822), (122199, 131902), (122206, 271638),
  (122220, 28102), (122224, 214326), (122268, 20222), (122274, 500534), (122288, 482094),
  (122332, 54), (122352, 255326), (122359, 54), (122360, 638334), (122387, 1845342),
  (122397, 968542), (122414, 7920126), (122418, 642622), (122424, 29894), (122466, 29758),
  (122576, 54), (122585, 501894), (122628, 71822), (122649, 59342), (122664, 686),
  (122712, 20222), (122738, 54), (122754, 3114542), (122781, 61718), (122782, 499734),
  (122845, 6933222), (122886, 267086), (122900, 54), (122928, 2000014), (122946, 34582),
  (122967, 43118), (123007, 611009838), (123008, 2646), (123018, 29366), (123025, 1467846),
  (123030, 265414), (123062, 54), (123066, 86998), (123089, 20142), (123106, 6174),
  (123108, 219806), (123135, 13718), (123142, 810918), (123153, 30718), (123170, 54),
  (123174, 159934), (123216, 29662), (123223, 54), (123234, 474134), (123269, 574038),
  (123305, 1566), (123318, 62774), (123332, 54), (123341, 367758), (123381, 185254)]

def WL33 : List (ℕ × ℕ) := [
  (123404, 280494), (123475, 602766), (123513, 275894), (123548, 4927446), (123621, 474406),
  (123669, 113686), (123709, 54), (123717, 178606), (123738, 5206766), (123746, 772614),
  (123790, 54), (123792, 13429822), (123804, 9038102), (123817, 54), (123871, 59238),
  (123899, 69606), (123979, 325998), (124034, 4606038), (124042, 519174), (124061, 54702),
  (124097, 346806), (124101, 586358), (124122, 67198), (124158, 198278), (124195, 1566),
  (124196, 2206062), (124215, 3914398), (124276, 231606), (124277, 2503926), (124367, 768006),
  (124374, 128878), (124438, 21438), (124466, 54), (124497, 582718), (124530, 41462),
  (124572, 953926), (124593, 401342), (124600, 2212542), (124647, 38854), (124691, 1564902),
  (124699, 250326), (124762, 54), (124763, 54), (124924, 5228334), (124943, 458478),
  (124952, 779598), (125001, 62438), (125005, 54), (125032, 35262), (125034, 197926),
  (125060, 486), (125076, 78382), (125113, 54), (125148, 197822), (125181, 1176646),
  (125194, 4806), (125249, 54), (125357, 54), (125383, 486), (125411, 54), (125412, 74318),
  (125518, 54), (125519, 9645102), (125571, 21334), (125572, 54), (125599, 54),
  (125607, 26302), (125652, 586294), (125654, 76734), (125671, 1147374), (125680, 54),
  (125751, 686), (125762, 54), (125797, 575334), (125816, 14958), (125847, 97718),
  (125860, 232542), (125887, 1761678), (125897, 6534), (125937, 76654), (125977, 15153102),
  (126093, 6492326), (126121, 1915038), (126139, 3926934), (126162, 91382), (126198, 25934),
  (126288, 99566), (126302, 54), (126309, 336526), (126329, 54), (126342, 4312006),
  (126364, 1921302), (126387, 85846), (126393, 45622), (126462, 313382), (126463, 54),
  (126490, 54), (126518, 486), (126552, 98822), (126567, 78998), (126572, 54),
  (126644, 577062), (126652, 5478894), (126653, 54), (126681, 78502), (126734, 54),
  (126751, 1924326), (126761, 130734), (126807, 255166), (126868, 54), (126891, 376966),
  (126930, 668102), (126950, 1566), (126972, 75814), (126976, 16587774), (126987, 101678),
  (127057, 54), (127062, 463102), (127084, 486), (127111, 54), (127212, 23174),
  (127218, 43174), (127233, 56702), (127273, 54), (127300, 28134), (127308, 20198),
  (127332, 99614), (127335, 142526), (127356, 3286918), (127374, 214366), (127435, 40878),
  (127462, 54), (127463, 5238), (127464, 76598), (127476, 111382), (127489, 2052702),
  (127497, 79342), (127498, 897174), (127517, 6826734), (127597, 139374), (127625, 16902),
  (127643, 1513062), (127650, 27998), (127689, 192958), (127696, 672822), (127713, 705686),
  (127777, 367398), (127779, 374942), (127786, 1308366), (127787, 54), (127804, 261918),
  (127815, 363574), (127840, 54), (127867, 556902), (127908, 1353478), (127962, 53726),
  (128001, 249478), (128002, 54), (128003, 1566), (128043, 141998), (128084, 54),
  (128133, 204142), (128165, 6534), (128191, 2928582), (128211, 14605246), (128245, 54),
  (128247, 567278), (128255, 9556254), (128316, 57238), (128325, 53806), (128344, 1595934),
  (128353, 54), (128354, 11951118), (128407, 6534), (128434, 133542), (128520, 43222),
  (128597, 54), (128606, 1362222), (128632, 8587422), (128651, 54), (128696, 222246),
  (128731, 19494), (128758, 54), (128785, 14491062), (128799, 300406), (128813, 54),
  (128838, 686), (128875, 236862), (128920, 54), (128925, 64822), (128937, 686), (128948, 486),
  (128952, 373894), (128970, 284366), (128974, 224478), (128975, 54), (129002, 14958),
  (129083, 235494), (129136, 54), (129137, 54), (129159, 482606), (129164, 6534),
  (129181, 2673342), (129226, 224118), (129255, 41086), (129271, 486), (129281, 195246),
  (129312, 37798), (129326, 54), (129378, 3135118), (129379, 7099758), (129380, 50598),
  (129407, 54), (129429, 397718), (129460, 54), (129487, 28134), (129501, 213326),
  (129524, 1438542), (129534, 243094), (129541, 150606), (129542, 10422), (129543, 45502),
  (129568, 7031718), (129621, 266782), (129669, 619118), (129677, 486), (129704, 54),
  (129730, 54), (129731, 5805486), (129759, 11185078), (129828, 68942), (129893, 54),
  (129946, 151902), (129954, 162598), (129974, 28566), (129996, 9917854), (130011, 3045086),
  (130027, 54), (130054, 54), (130074, 45062), (130095, 40958), (130136, 54), (130216, 54),
  (130271, 54), (130377, 29542), (130432, 54), (130433, 54), (130459, 1566), (130513, 15174),
  (130536, 13718), (130548, 275542), (130599, 20854), (130620, 119326), (130647, 418598),
  (130676, 54), (130698, 193574), (130752, 21382), (130782, 145342), (130793, 1144998),
  (130828, 362574), (130837, 54), (130865, 1566), (130884, 498398), (130892, 486),
  (130914, 40862), (130919, 54), (130945, 2646), (130991, 452646), (130999, 54), (131000, 54),
  (131027, 54), (131081, 54), (131082, 33094), (131160, 73142), (131161, 54),
  (131171, 1588662), (131189, 142182), (131215, 486), (131252, 396054), (131270, 54),
  (131280, 972022), (131307, 30766), (131349, 137486), (131350, 54), (131382, 497758),
  (131405, 1739502), (131431, 54), (131432, 6534), (131433, 426614), (131440, 19253142),
  (131539, 5331582), (131558, 399078), (131566, 71334), (131567, 20971926), (131583, 1052422)]

def WL34 : List (ℕ × ℕ) := [
  (131593, 54), (131594, 292302), (131621, 113238), (131648, 1566), (131675, 54), (131728, 54),
  (131747, 265878), (131755, 54), (131787, 389798), (131805, 599446), (131823, 342806),
  (131836, 54), (131864, 6510942), (131937, 468134), (131944, 486), (131973, 427694),
  (131997, 316838), (132043, 1092654), (132053, 54), (132099, 463142), (132133, 54),
  (132160, 19494), (132161, 54), (132188, 5336118), (132195, 5638918), (132214, 15435414),
  (132295, 490158), (132377, 141318), (132399, 31574), (132403, 5675886), (132404, 54),
  (132431, 6253038), (132494, 204894), (132539, 54), (132611, 10106838), (132690, 46862),
  (132771, 28814), (132781, 1438182), (132782, 54), (132795, 311398), (132858, 35318),
  (132889, 54), (132897, 46742), (132916, 486), (132944, 54), (132952, 1659222),
  (132998, 3395358), (133005, 2662), (133035, 254974), (133096, 680382), (133106, 54),
  (133191, 93182), (133200, 2634142), (133218, 48086), (133268, 54), (133294, 54),
  (133295, 14958), (133314, 169102), (133330, 6374142), (133349, 971406), (133356, 115054),
  (133404, 434734), (133429, 3099006), (133457, 54), (133474, 489438), (133502, 562446),
  (133510, 2069982), (133551, 144334), (133592, 6194286), (133618, 54), (133645, 515646),
  (133650, 20326), (133672, 54), (133681, 623718), (133812, 203254), (133825, 1432422),
  (133834, 54), (133943, 54), (133959, 31462), (133983, 686), (133996, 54), (134024, 14526),
  (134078, 54), (134100, 257182), (134104, 54), (134131, 23814), (134185, 183006),
  (134266, 9181134), (134295, 191414), (134427, 447422), (134496, 36614), (134500, 277686),
  (134514, 23942), (134563, 54), (134568, 601646), (134580, 41758), (134590, 28566),
  (134637, 528182), (134658, 57502), (134671, 67446), (134672, 54), (134718, 1067318),
  (134833, 54), (134860, 486), (134888, 2668086), (134940, 144542), (134968, 815454),
  (134995, 54), (135012, 19894), (135023, 2891214), (135036, 20134), (135081, 63334),
  (135093, 2662), (135130, 243918), (135158, 54), (135212, 31158), (135239, 54), (135266, 486),
  (135270, 52502), (135284, 721782), (135288, 30574), (135309, 300862), (135319, 7523982),
  (135330, 23486), (135374, 1687446), (135429, 4953206), (135454, 129654), (135483, 370582),
  (135528, 169622), (135536, 14198598), (135562, 54), (135564, 47822), (135570, 203998),
  (135589, 486), (135616, 203094), (135617, 3089934), (135697, 54), (135698, 15688134),
  (135725, 54), (135729, 112478), (135759, 64958), (135778, 15174), (135779, 54),
  (135805, 5238), (135806, 627534), (135850, 617886), (135864, 121358), (135868, 1492254),
  (135886, 512838), (135940, 189486), (135967, 54), (135968, 36342), (135987, 101294),
  (135990, 51862), (136086, 225902), (136130, 54), (136137, 29566), (136158, 196646),
  (136183, 54), (136238, 20408598), (136242, 90982), (136278, 197894), (136284, 93734),
  (136290, 6266006), (136346, 1566), (136372, 124038), (136373, 54), (136422, 56878),
  (136452, 58502), (136507, 54), (136508, 10911942), (136526, 1668294), (136535, 54),
  (136554, 330686), (136638, 261238), (136670, 1283742), (136724, 486), (136773, 64982),
  (136779, 318998), (136858, 699462), (136859, 54), (136911, 610838), (136912, 804438),
  (136953, 131686), (137021, 616518), (137047, 486), (137101, 54), (137151, 88246),
  (137169, 856814), (137192, 300654), (137263, 20142), (137264, 10638), (137318, 6751782),
  (137345, 14668398), (137349, 468086), (137353, 311886), (137398, 7437798), (137445, 183262),
  (137479, 3352374), (137496, 266806), (137506, 1566), (137507, 54), (137514, 50878),
  (137560, 2646), (137606, 419598), (137619, 110254), (137628, 99206), (137641, 16902),
  (137668, 54), (137723, 54), (137760, 354766), (137795, 1250838), (137804, 1680534),
  (137829, 568166), (137831, 54), (137844, 47374), (137885, 919782), (137912, 364878),
  (137913, 65878), (138046, 54), (138073, 54), (138101, 2072142), (138144, 1505158),
  (138154, 2186622), (138189, 181574), (138192, 219502), (138198, 642782), (138199, 1051254),
  (138209, 54), (138236, 10638), (138244, 1227942), (138258, 364862), (138279, 89918),
  (138370, 54), (138397, 3825846), (138425, 486), (138442, 6174), (138460, 299718),
  (138469, 322254), (138532, 54), (138541, 6174), (138595, 246438), (138606, 2475446),
  (138614, 54), (138640, 54), (138650, 480366), (138721, 54), (138739, 764118), (138748, 486),
  (138775, 54), (138785, 6174), (138816, 552974), (138843, 574382), (138847, 279918),
  (138883, 2646), (138964, 54), (138969, 281654), (139008, 117398), (139018, 54), (139046, 54),
  (139127, 21438), (139176, 4822334), (139180, 126414), (139207, 8343918), (139215, 30614),
  (139227, 686), (139245, 23174), (139288, 54), (139343, 341766), (139369, 54),
  (139455, 189806), (139467, 189374), (139470, 88118), (139477, 13991454), (139568, 460854),
  (139578, 5528678), (139711, 517878), (139747, 54), (139775, 17141598)]

def WL35 : List (ℕ × ℕ) := [
  (139819, 893286), (139838, 831582), (139872, 80246), (139883, 486), (139909, 54),
  (139963, 486), (139981, 1910934), (139991, 54), (140106, 47758), (140118, 90494),
  (140157, 132398), (140160, 6107422), (140161, 342558), (140180, 39582), (140206, 4691358),
  (140260, 54), (140261, 1566), (140315, 102654), (140355, 76606), (140394, 541438),
  (140421, 112262), (140422, 5238), (140451, 2199806), (140476, 54), (140477, 11311758),
  (140553, 20206), (140601, 21278), (140665, 22086), (140709, 328886), (140712, 54958),
  (140746, 828198), (140882, 862542), (140908, 1566), (140909, 54), (140940, 112078),
  (140973, 137374), (140994, 4428166), (141034, 441918), (141125, 2023326), (141135, 155998),
  (141177, 65126), (141205, 54), (141241, 297342), (141268, 594414), (141285, 15855518),
  (141304, 444078), (141314, 1566), (141322, 217926), (141345, 379046), (141351, 20326),
  (141367, 28134), (141449, 205038), (141476, 54), (141498, 228686), (141531, 238486),
  (141534, 126254), (141610, 18394182), (141611, 54), (141664, 486), (141780, 3267542),
  (141799, 54), (141826, 1661958), (141853, 20205342), (141854, 54), (141933, 405814),
  (141971, 6174), (142007, 569574), (142016, 54), (142029, 26294), (142043, 4532382),
  (142101, 32126), (142150, 486), (142204, 1566), (142205, 54), (142322, 20532006),
  (142339, 12582), (142340, 44334), (142367, 54), (142422, 46502), (142448, 54), (142501, 54),
  (142583, 10638), (142611, 1988438), (142659, 620462), (142680, 32222), (142737, 17075158),
  (142745, 54), (142746, 283334), (142763, 466974), (142764, 951838), (142836, 150334),
  (142852, 732942), (142879, 387342), (142896, 193598), (142907, 54), (142974, 188926),
  (142987, 1566), (143073, 129758), (143088, 90166), (143096, 54), (143115, 26438),
  (143122, 486), (143149, 54), (143253, 256798), (143289, 24502), (143339, 54),
  (143374, 1189494), (143392, 2646), (143473, 54), (143474, 54), (143501, 4806),
  (143502, 438166), (143505, 218782), (143528, 17690886), (143555, 10638), (143653, 23958),
  (143663, 1566), (143670, 33686), (143716, 54), (143718, 574118), (143824, 10422),
  (143877, 22766), (143879, 54), (143960, 14958), (144023, 1031094), (144041, 54),
  (144076, 329598), (144078, 1223726), (144094, 4798278), (144122, 54), (144144, 258982),
  (144229, 54), (144230, 284742), (144276, 235526), (144283, 354726), (144284, 54),
  (144310, 54), (144328, 900414), (144363, 26902), (144373, 897678), (144391, 4806),
  (144426, 577606), (144447, 40958), (144513, 69214), (144516, 66806), (144527, 16902),
  (144580, 486), (144607, 54), (144616, 6174), (144617, 11599182), (144688, 1591542),
  (144711, 98734), (144715, 645568974), (144716, 18846), (144734, 214686), (144810, 85438),
  (144864, 323662), (144877, 54), (144959, 645832494), (145013, 54), (145040, 57294),
  (145066, 1133838), (145095, 41086), (145102, 740574), (145201, 47358), (145236, 108278),
  (145256, 10422), (145319, 205182), (145363, 54), (145399, 826974), (145404, 65438),
  (145418, 54), (145425, 293638), (145440, 296798), (145445, 54), (145482, 159686),
  (145524, 25838), (145525, 10638), (145530, 66974), (145606, 45414), (145661, 54),
  (145695, 3725078), (145696, 1073934), (145710, 6651854), (145741, 166644486),
  (145767, 63814), (145769, 54), (145773, 33622), (145803, 81118), (145822, 54),
  (145830, 82934), (145857, 47494), (145885, 745974), (145921, 645822), (145931, 4806),
  (145944, 6151766), (145958, 4374), (145980, 58622), (146012, 1566), (146085, 344342),
  (146160, 62302), (146190, 247454), (146193, 35678), (146250, 519814), (146256, 63926),
  (146331, 19894), (146362, 4879278), (146397, 172526), (146417, 93582), (146466, 555718),
  (146470, 40878), (146497, 54), (146498, 54), (146551, 824526), (146552, 54), (146578, 54),
  (146587, 610614), (146651, 702846), (146652, 20158), (146659, 266598), (146677, 1225998),
  (146679, 3412198), (146713, 54), (146740, 54), (146778, 77134), (146795, 1566),
  (146820, 23846), (146822, 2013606), (146871, 1121414), (146883, 3481502), (146956, 7107318),
  (146957, 54), (147029, 614214), (147064, 718038), (147072, 2662), (147119, 54),
  (147145, 14958), (147253, 486), (147307, 54), (147317, 7163406), (147342, 167966),
  (147352, 1201518), (147441, 209422), (147442, 1058886), (147443, 54), (147488, 500382),
  (147524, 54), (147551, 54), (147559, 244206), (147604, 54), (147605, 2646), (147609, 131702),
  (147623, 711054), (147632, 16902), (147659, 486), (147686, 54), (147713, 54),
  (147757, 614646), (147793, 230742), (147802, 6174), (147819, 537686), (147825, 26518),
  (147847, 54), (147848, 54), (147909, 252446), (147929, 394038)]

def WL36 : List (ℕ × ℕ) := [
  (148009, 6534), (148023, 446518), (148028, 266022), (148056, 535046), (148077, 20198),
  (148083, 62102), (148090, 54), (148118, 1347462), (148125, 50494), (148145, 649018494),
  (148171, 54), (148188, 40822), (148198, 107838), (148230, 44134), (148280, 199638),
  (148389, 686), (148442, 54), (148488, 686), (148496, 54), (148518, 44566),
  (148577, 13760982), (148594, 695718), (148611, 120542), (148631, 367902), (148632, 196774),
  (148684, 19942902), (148731, 138854), (148748, 892854), (148829, 857214), (148846, 54),
  (148847, 11760822), (148864, 301734), (148927, 54), (148932, 3079046), (148954, 1843398),
  (148982, 1032534), (149016, 43702), (149025, 489238), (149045, 839574), (149100, 488182),
  (149115, 727262), (149170, 494694), (149189, 892062), (149247, 25078), (149256, 41462),
  (149323, 535662), (149324, 462006), (149332, 280638), (149400, 204046), (149413, 426654),
  (149418, 20704166), (149467, 2646), (149511, 55078), (149548, 54), (149575, 6396462),
  (149576, 116262), (149584, 1215558), (149683, 822798), (149738, 54), (149751, 50822),
  (149826, 20998), (149841, 466462), (149850, 60182), (149872, 15839982), (149900, 54),
  (149953, 54), (149958, 1129646), (149970, 37798), (149980, 968166), (149981, 54),
  (150018, 27518), (150036, 21262), (150061, 501174), (150066, 3757534), (150116, 4310118),
  (150162, 234638), (150243, 12372902), (150278, 41526), (150291, 420566), (150304, 1566),
  (150358, 4301478), (150369, 34054), (150386, 19270278), (150408, 106558), (150439, 54),
  (150520, 54), (150521, 4409046), (150546, 686), (150656, 1636686), (150683, 298134),
  (150701, 5605758), (150710, 139374), (150741, 1009694), (150791, 1526742), (150844, 10638),
  (150871, 35262), (150872, 2493774), (150898, 47142), (150899, 5279094), (150925, 4006854),
  (150954, 177542), (150963, 54182), (150975, 21694), (151006, 54), (151011, 130846),
  (151017, 107014), (151033, 47574), (151034, 633798), (151115, 54), (151146, 21446),
  (151212, 81758), (151250, 54), (151276, 6534), (151277, 54), (151321, 241398),
  (151330, 2646), (151411, 54), (151412, 54702), (151438, 54), (151482, 501454), (151492, 54),
  (151510, 215766), (151520, 54), (151556, 306486), (151574, 2646), (151611, 86446),
  (151627, 43254), (151629, 2141998), (151647, 166486), (151655, 54), (151772, 192438),
  (151821, 29278), (151843, 54), (151888, 1619262), (151979, 54), (152033, 58806),
  (152059, 54), (152073, 1316542), (152087, 54), (152124, 126622), (152140, 154494),
  (152221, 54), (152248, 54), (152249, 54), (152250, 3094886), (152276, 14094),
  (152294, 409518), (152322, 27358), (152340, 163862), (152356, 725598), (152383, 1566),
  (152384, 15243174), (152388, 11982254), (152410, 54), (152411, 28134), (152465, 54),
  (152511, 72614), (152545, 54), (152546, 54), (152609, 302814), (152619, 379718),
  (152626, 54), (152653, 76734), (152654, 54), (152663, 232398), (152712, 7411094),
  (152727, 386494), (152735, 225558), (152762, 486), (152815, 880254), (152826, 53366),
  (152865, 6637238), (152887, 407142), (152897, 2646), (152950, 54), (152970, 1706342),
  (152978, 16902), (152991, 213806), (153049, 729126), (153057, 6467614), (153063, 493022),
  (153076, 502542), (153140, 4806), (153186, 126494), (153194, 120798), (153207, 26438),
  (153258, 484838), (153301, 54), (153302, 20142), (153328, 486), (153356, 54),
  (153357, 159262), (153382, 54), (153390, 18146806), (153435, 33806), (153436, 76734),
  (153437, 2646), (153491, 486), (153517, 5238), (153534, 686), (153544, 54),
  (153581, 6248862), (153589, 301734), (153600, 194206), (153684, 38414), (153699, 41798),
  (153750, 3000598), (153761, 54), (153768, 126206), (153770, 488286), (153788, 54),
  (153805, 219798), (153867, 426134), (153888, 601382), (153895, 2705886), (153900, 2766542),
  (153918, 87518), (153923, 54), (153950, 9132966), (153957, 41918), (153976, 22059702),
  (154065, 3321718), (154084, 99846), (154085, 578286), (154089, 33742), (154104, 46262),
  (154111, 47574), (154166, 4393062), (154220, 653781294), (154251, 57686), (154273, 110862),
  (154275, 325406), (154319, 6174), (154327, 10422), (154328, 54), (154329, 7686038),
  (154336, 572382), (154408, 54), (154440, 24974), (154490, 2051622), (154509, 762526),
  (154517, 54), (154566, 632102), (154597, 22734), (154638, 73894), (154660, 1140606),
  (154680, 34654), (154705, 5084694), (154743, 144502), (154759, 2646), (154760, 2646),
  (154779, 22886), (154785, 5290846), (154786, 486), (154813, 54), (154824, 303878),
  (154841, 54), (154908, 410926), (154911, 53294), (155028, 32374), (155029, 4374),
  (155048, 1271502), (155057, 54), (155084, 19494), (155111, 2697462), (155119, 220734),
  (155120, 1132254), (155148, 3792382), (155164, 16171758), (155259, 275014), (155265, 225662),
  (155272, 486), (155281, 329598), (155318, 1126638), (155325, 592574), (155337, 96374),
  (155373, 171382), (155408, 1566), (155469, 67846), (155569, 54), (155595, 68518),
  (155604, 38782), (155615, 1004814), (155623, 6119766), (155650, 57294), (155651, 5238),
  (155659, 576918), (155660, 6745806), (155664, 57614), (155678, 93798), (155691, 686),
  (155736, 536806), (155763, 86854), (155785, 1566), (155812, 54), (155813, 3500766),
  (155832, 41278), (155835, 325574), (155867, 54), (155937, 24502), (155947, 54), (155974, 54),
  (156001, 455382), (156021, 257126), (156029, 54), (156030, 434542), (156038, 541638),
  (156042, 194606), (156109, 77382), (156137, 23382)]

def WL37 : List (ℕ × ℕ) := [
  (156218, 2179278), (156219, 31574), (156249, 2834518), (156273, 42814), (156288, 359638),
  (156316, 707814), (156379, 7422462), (156389, 23958), (156408, 442654), (156462, 121318),
  (156465, 181822), (156507, 299086), (156515, 54), (156541, 54), (156542, 54),
  (156550, 1002006), (156595, 21438), (156627, 97142), (156648, 96982), (156676, 15556158),
  (156704, 1566), (156720, 18983678), (156758, 12314646), (156819, 128558), (156865, 54),
  (156866, 2646), (156893, 17045478), (157001, 6278742), (157010, 1401606), (157019, 398214),
  (157072, 406206), (157081, 1566), (157108, 54), (157109, 54), (157149, 20782), (157162, 54),
  (157163, 54), (157179, 305702), (157243, 54), (157261, 432774), (157325, 54),
  (157387, 848574), (157432, 2283174), (157464, 48182), (157494, 2504734), (157568, 6534),
  (157572, 21334), (157605, 20198), (157617, 124766), (157648, 16902), (157650, 686),
  (157662, 129782), (157684, 373374), (157752, 4811134), (157757, 1566), (157837, 54),
  (157838, 54), (157856, 588942), (157891, 54), (157892, 54), (157899, 375926),
  (157974, 195214), (158031, 212206), (158046, 204278), (158054, 35262), (158082, 275446),
  (158135, 54), (158144, 658926), (158153, 915102), (158187, 8355742), (158208, 54086),
  (158214, 177622), (158216, 54), (158243, 54), (158286, 340486), (158296, 54),
  (158319, 114214), (158405, 240678), (158431, 486), (158486, 1670598), (158566, 54),
  (158584, 1668726), (158594, 486), (158640, 313342), (158729, 2646), (158782, 148446),
  (158801, 5359374), (158810, 54), (158823, 95054), (158828, 1084662), (158837, 486),
  (158863, 136134), (158873, 947358), (158971, 54), (159080, 4374), (159090, 20158),
  (159133, 54), (159160, 486), (159192, 3387518), (159215, 1613142), (159237, 483926),
  (159243, 246014), (159300, 511486), (159312, 40966), (159377, 46278), (159441, 87182),
  (159512, 521262), (159561, 4101398), (159566, 573966), (159593, 54), (159594, 101782),
  (159619, 54), (159620, 54), (159627, 85574), (159630, 203222), (159657, 157022),
  (159708, 33614), (159747, 143966), (159754, 54), (159781, 948942), (159899, 992934),
  (159908, 896094), (159916, 54), (159962, 433494), (160007, 791334), (160020, 113318),
  (160025, 54), (160078, 54), (160092, 429214), (160105, 74142), (160106, 3615894),
  (160159, 54), (160160, 2509758), (160169, 486198), (160203, 70214), (160267, 54),
  (160295, 723654), (160322, 4806), (160348, 54), (160358, 10358046), (160431, 11225486),
  (160473, 45238), (160482, 41494), (160484, 54), (160596, 80198), (160645, 13014),
  (160665, 54382), (160713, 46286), (160726, 54), (160728, 61286), (160737, 686), (160754, 54),
  (160785, 131038), (160836, 7845782), (160852, 439326), (160887, 333206), (160916, 68958),
  (160988, 462006), (161015, 1903518), (161049, 32638), (161077, 13989294), (161082, 5520958),
  (161100, 35782), (161124, 263182), (161175, 34862), (161205, 30518), (161267, 4374),
  (161271, 143974), (161294, 54), (161302, 495486), (161322, 509942), (161357, 1031166),
  (161401, 19494), (161456, 171774), (161483, 54), (161562, 166918), (161590, 4374),
  (161617, 2087262), (161644, 54), (161688, 6826942), (161699, 54), (161700, 33038),
  (161833, 486), (161860, 54), (161877, 69374), (161887, 54), (161901, 180382),
  (161931, 43574), (161959, 1020798), (161973, 23174), (161978, 938934), (162015, 63134),
  (162022, 41742), (162045, 2516558), (162048, 201182), (162093, 395534), (162184, 54),
  (162238, 5513022), (162239, 6925014), (162311, 901998), (162339, 917734), (162346, 54),
  (162363, 75694), (162372, 63254), (162387, 36622), (162392, 988542), (162482, 486),
  (162500, 1657926), (162580, 237294), (162616, 54), (162624, 70198), (162699, 479078),
  (162752, 4806), (162759, 55382), (162778, 229014), (162792, 176678), (162805, 416502),
  (162825, 21382), (162849, 518918), (162860, 54), (162869, 372726), (162913, 54),
  (162968, 14094), (162994, 5898798), (163021, 330102), (163030, 216774), (163050, 410678),
  (163122, 3116398), (163138, 3957534), (163148, 999846), (163183, 54), (163184, 54),
  (163236, 2298982), (163345, 421254), (163346, 54), (163371, 556774), (163395, 355078),
  (163427, 54), (163480, 4529142), (163481, 657729342), (163535, 1684638), (163562, 18846),
  (163588, 54), (163589, 54), (163598, 528534), (163626, 42646), (163641, 33854),
  (163647, 506878), (163659, 21806), (163683, 25582), (163743, 545134), (163751, 1566),
  (163857, 76094), (163868, 528102), (163884, 292478), (163923, 12389846), (163941, 121438),
  (164020, 23814), (164074, 54), (164110, 1099782), (164130, 67862), (164142, 87158),
  (164208, 380566), (164217, 1631798), (164236, 54), (164264, 5887566), (164268, 69334),
  (164291, 28134), (164316, 118166), (164334, 144934)]

def WL38 : List (ℕ × ℕ) := [
  (164372, 54), (164409, 79318), (164466, 299206), (164471, 1258398), (164478, 2618806),
  (164561, 54), (164583, 135518), (164586, 4402222), (164607, 493222), (164613, 31846),
  (164632, 185454), (164646, 41614), (164709, 479758), (164712, 81542), (164722, 54),
  (164732, 241398), (164775, 1897006), (164803, 54), (164822, 696582), (164838, 653894),
  (164853, 19894), (164857, 2598534), (164884, 54), (164885, 230742), (164939, 54),
  (164949, 2238742), (164961, 376214), (165047, 54), (165060, 2551294), (165075, 74758),
  (165101, 6534), (165110, 922302), (165128, 4806), (165159, 112766), (165171, 51206),
  (165177, 534406), (165181, 1566), (165209, 54), (165237, 13147502), (165263, 54),
  (165339, 324782), (165370, 54), (165381, 33406), (165425, 15959214), (165452, 54),
  (165478, 486), (165492, 175918), (165523, 1292526), (165549, 996614), (165585, 5941342),
  (165613, 54), (165627, 33526), (165668, 54), (165690, 307486), (165703, 7716726),
  (165748, 92934), (165775, 54), (165776, 54), (165802, 5560974), (165804, 670822),
  (165810, 3603598), (165830, 54), (165978, 282214), (165991, 54), (166019, 10422),
  (166041, 211966), (166073, 54), (166083, 157838), (166116, 188894), (166125, 220838),
  (166154, 54), (166207, 486), (166221, 31582), (166262, 54), (166342, 12983382),
  (166343, 34614), (166396, 54), (166424, 54), (166441, 425934), (166460, 263502),
  (166496, 1162638), (166551, 363518), (166559, 167886), (166585, 13295718), (166602, 2138518),
  (166666, 4098654), (166667, 129654), (166686, 47438), (166719, 212486), (166739, 1735974),
  (166747, 1566), (166748, 7128918), (166782, 178918), (166791, 6340822), (166829, 54),
  (166878, 77494), (166910, 54), (166936, 16265934), (166956, 29686), (166963, 54),
  (166964, 141318), (166972, 1806174), (166991, 54), (167010, 686), (167049, 56894),
  (167067, 29366), (167108, 12562326), (167118, 523942), (167152, 13014), (167179, 486),
  (167207, 304614), (167223, 352694), (167287, 133758), (167307, 485494), (167340, 39982),
  (167369, 4972374), (167382, 24526), (167406, 263894), (167421, 388526), (167450, 2646),
  (167476, 20142), (167530, 1566), (167540, 187038), (167547, 567038), (167553, 175046),
  (167580, 49886), (167592, 225118), (167607, 381014), (167656, 236646), (167665, 486),
  (167692, 1421118), (167720, 54), (167755, 257814), (167769, 115718), (167775, 310846),
  (167838, 443614), (167859, 30598), (167881, 7478838), (167889, 400814), (167935, 54),
  (167936, 1566), (167988, 110702), (167991, 110702), (168043, 1566), (168044, 54),
  (168090, 400814), (168098, 7478838), (168120, 30598), (168141, 443614), (168204, 310846),
  (168210, 115718), (168224, 257814), (168259, 54), (168287, 1421118), (168314, 486),
  (168323, 236646), (168372, 381014), (168387, 225118), (168399, 49886), (168426, 175046),
  (168432, 567038), (168439, 187038), (168449, 1566), (168503, 20142), (168529, 2646),
  (168558, 388526), (168573, 263894), (168597, 24526), (168610, 4972374), (168639, 39982),
  (168672, 485494), (168692, 133758), (168756, 352694), (168772, 304614), (168800, 486),
  (168827, 13014), (168861, 523942), (168871, 12562326), (168912, 29366), (168930, 56894),
  (168969, 686), (168988, 54), (169007, 1806174), (169015, 141318), (169016, 54),
  (169023, 29686), (169043, 16265934), (169069, 54), (169101, 77494), (169150, 54),
  (169188, 6340822), (169197, 178918), (169231, 7128918), (169232, 1566), (169240, 1735974),
  (169260, 212486), (169293, 47438), (169312, 129654), (169313, 4098654), (169377, 2138518),
  (169394, 13295718), (169420, 167886), (169428, 363518), (169483, 1162638), (169519, 263502),
  (169538, 425934), (169555, 54), (169583, 54), (169636, 34614), (169637, 12983382),
  (169717, 54), (169758, 31582), (169772, 486), (169825, 54), (169854, 220838),
  (169863, 188894), (169896, 157838), (169906, 54), (169938, 211966), (169960, 10422),
  (169988, 54), (170001, 282214), (170149, 54), (170169, 3603598), (170175, 670822),
  (170177, 5560974), (170203, 54), (170204, 54), (170231, 92934), (170276, 7716726),
  (170289, 307486), (170311, 54), (170352, 33526), (170366, 54), (170394, 5941342),
  (170430, 996614), (170456, 1292526), (170487, 175918), (170501, 486), (170527, 54),
  (170554, 15959214), (170598, 33406), (170609, 54), (170640, 324782), (170716, 54),
  (170742, 13147502), (170770, 54), (170798, 1566), (170802, 534406), (170808, 51206),
  (170820, 112766), (170851, 4806), (170869, 922302), (170878, 6534), (170904, 74758),
  (170919, 2551294), (170932, 54), (171018, 376214), (171030, 2238742), (171040, 54),
  (171094, 230742), (171095, 54), (171122, 2598534), (171126, 19894), (171141, 653894),
  (171157, 696582), (171176, 54), (171204, 1897006), (171247, 241398), (171257, 54),
  (171267, 81542), (171270, 479758), (171333, 41614), (171347, 185454), (171366, 31846),
  (171372, 493222), (171393, 4402222), (171396, 135518), (171418, 54), (171501, 2618806),
  (171508, 1258398), (171513, 299206), (171570, 79318), (171607, 54), (171645, 144934),
  (171663, 118166), (171688, 28134), (171711, 69334), (171715, 5887566), (171743, 54),
  (171762, 1631798), (171771, 380566), (171837, 87158), (171849, 67862), (171869, 1099782),
  (171905, 54), (171959, 23814), (172038, 121438), (172056, 12389846), (172095, 292478),
  (172111, 528102), (172122, 76094), (172228, 1566), (172236, 545134), (172296, 25582),
  (172320, 21806), (172332, 506878), (172338, 33854), (172353, 42646), (172381, 528534),
  (172390, 54), (172391, 54), (172417, 18846), (172444, 1684638), (172498, 657729342),
  (172499, 4529142)]

def WL39 : List (ℕ × ℕ) := [
  (172552, 54), (172584, 355078), (172608, 556774), (172633, 54), (172634, 421254),
  (172743, 2298982), (172795, 54), (172796, 54), (172831, 999846), (172841, 3957534),
  (172857, 3116398), (172929, 410678), (172949, 216774), (172958, 330102), (172985, 5898798),
  (173011, 14094), (173066, 54), (173110, 372726), (173119, 54), (173130, 518918),
  (173154, 21382), (173174, 416502), (173187, 176678), (173201, 229014), (173220, 55382),
  (173227, 4806), (173280, 479078), (173355, 70198), (173363, 54), (173399, 237294),
  (173479, 1657926), (173497, 486), (173587, 988542), (173592, 36622), (173607, 63254),
  (173616, 75694), (173633, 54), (173640, 917734), (173668, 901998), (173740, 6925014),
  (173741, 5513022), (173795, 54), (173886, 395534), (173931, 201182), (173934, 2516558),
  (173957, 41742), (173964, 63134), (174001, 938934), (174006, 23174), (174020, 1020798),
  (174048, 43574), (174078, 180382), (174092, 54), (174102, 69374), (174119, 54),
  (174146, 486), (174279, 33038), (174280, 54), (174291, 6826942), (174335, 54),
  (174362, 2087262), (174389, 4374), (174417, 166918), (174496, 54), (174523, 171774),
  (174578, 19494), (174622, 1031166), (174657, 509942), (174677, 495486), (174685, 54),
  (174708, 143974), (174712, 4374), (174774, 30518), (174804, 34862), (174855, 263182),
  (174879, 35782), (174897, 5520958), (174902, 13989294), (174930, 32638), (174964, 1903518),
  (174991, 462006), (175063, 68958), (175092, 333206), (175127, 439326), (175143, 7845782),
  (175194, 131038), (175225, 54), (175242, 686), (175251, 61286), (175253, 54),
  (175266, 46286), (175314, 54382), (175334, 13014), (175383, 80198), (175495, 54),
  (175497, 41494), (175506, 45238), (175548, 11225486), (175621, 10358046), (175631, 54),
  (175657, 4806), (175684, 723654), (175712, 54), (175776, 70214), (175810, 486198),
  (175819, 2509758), (175820, 54), (175873, 3615894), (175874, 74142), (175887, 429214),
  (175901, 54), (175954, 54), (175959, 113318), (175972, 791334), (176017, 433494),
  (176063, 54), (176071, 896094), (176080, 992934), (176198, 948942), (176225, 54),
  (176232, 143966), (176271, 33614), (176322, 157022), (176349, 203222), (176352, 85574),
  (176359, 54), (176360, 54), (176385, 101782), (176386, 54), (176413, 573966),
  (176418, 4101398), (176467, 521262), (176538, 87182), (176602, 46278), (176667, 40966),
  (176679, 511486), (176736, 246014), (176742, 483926), (176764, 1613142), (176787, 3387518),
  (176819, 486), (176846, 54), (176889, 20158), (176899, 4374), (177008, 54), (177106, 947358),
  (177116, 136134), (177142, 486), (177151, 1084662), (177156, 95054), (177169, 54),
  (177178, 5359374), (177197, 148446), (177250, 2646), (177339, 313342), (177385, 486),
  (177395, 1668726), (177413, 54), (177493, 1670598), (177548, 486), (177574, 240678),
  (177660, 114214), (177683, 54), (177693, 340486), (177736, 54), (177763, 54),
  (177765, 177622), (177771, 54086), (177792, 8355742), (177826, 915102), (177835, 658926),
  (177844, 54), (177897, 275446), (177925, 35262), (177933, 204278), (177948, 212206),
  (178005, 195214), (178080, 375926), (178087, 54), (178088, 54), (178123, 588942),
  (178141, 54), (178142, 54), (178222, 1566), (178227, 4811134), (178295, 373374),
  (178317, 129782), (178329, 686), (178331, 16902), (178362, 124766), (178374, 20198),
  (178407, 21334), (178411, 6534), (178485, 2504734), (178515, 48182), (178547, 2283174),
  (178592, 848574), (178654, 54), (178718, 432774), (178736, 54), (178800, 305702),
  (178816, 54), (178817, 54), (178830, 20782), (178870, 54), (178871, 54), (178898, 1566),
  (178907, 406206), (178960, 398214), (178969, 1401606), (178978, 6278742), (179086, 17045478),
  (179113, 2646), (179114, 54), (179160, 128558), (179221, 12314646), (179259, 18983678),
  (179275, 1566), (179303, 15556158), (179331, 96982), (179352, 97142), (179384, 21438),
  (179429, 1002006), (179437, 54), (179438, 54), (179464, 54), (179472, 299086),
  (179514, 181822), (179517, 121318), (179571, 442654), (179590, 23958), (179600, 7422462),
  (179663, 707814), (179691, 359638), (179706, 42814), (179730, 2834518), (179760, 31574),
  (179761, 2179278), (179842, 23382), (179870, 77382), (179937, 194606), (179941, 541638),
  (179949, 434542), (179950, 54), (179958, 257126), (179978, 455382), (180005, 54),
  (180032, 54), (180042, 24502), (180112, 54), (180144, 325574), (180147, 41278),
  (180166, 3500766), (180167, 54), (180194, 1566), (180216, 86854), (180243, 536806),
  (180288, 686), (180301, 93798), (180315, 57614), (180319, 6745806), (180320, 576918),
  (180328, 5238), (180329, 57294), (180356, 6119766), (180364, 1004814), (180375, 38782),
  (180384, 68518), (180410, 54), (180510, 67846), (180571, 1566), (180606, 171382),
  (180642, 96374), (180654, 592574), (180661, 1126638), (180698, 329598), (180707, 486),
  (180714, 225662), (180720, 275014)]

def WL40 : List (ℕ × ℕ) := [
  (180815, 16171758), (180831, 3792382), (180859, 1132254), (180860, 220734),
  (180868, 2697462), (180895, 19494), (180922, 54), (180931, 1271502), (180950, 4374),
  (180951, 32374), (181068, 53294), (181071, 410926), (181138, 54), (181155, 303878),
  (181166, 54), (181193, 486), (181194, 5290846), (181200, 22886), (181219, 2646),
  (181220, 2646), (181236, 144502), (181274, 5084694), (181299, 34654), (181319, 1140606),
  (181341, 73894), (181382, 22734), (181413, 632102), (181462, 54), (181470, 762526),
  (181489, 2051622), (181539, 24974), (181571, 54), (181643, 572382), (181650, 7686038),
  (181651, 54), (181652, 10422), (181660, 6174), (181704, 325406), (181706, 110862),
  (181728, 57686), (181759, 653781294), (181813, 4393062), (181868, 47574), (181875, 46262),
  (181890, 33742), (181894, 578286), (181895, 99846), (181914, 3321718), (182003, 22059702),
  (182022, 41918), (182029, 9132966), (182056, 54), (182061, 87518), (182079, 2766542),
  (182084, 2705886), (182091, 601382), (182112, 426134), (182174, 219798), (182191, 54),
  (182209, 488286), (182211, 126206), (182218, 54), (182229, 3000598), (182280, 41798),
  (182295, 38414), (182379, 194206), (182390, 301734), (182398, 6248862), (182435, 54),
  (182445, 686), (182462, 5238), (182488, 486), (182542, 2646), (182543, 76734),
  (182544, 33806), (182589, 18146806), (182597, 54), (182622, 159262), (182623, 54),
  (182651, 486), (182677, 20142), (182678, 54), (182721, 484838), (182772, 26438),
  (182785, 120798), (182793, 126494), (182839, 4806), (182903, 502542), (182916, 493022),
  (182922, 6467614), (182930, 729126), (182988, 213806), (183001, 16902), (183009, 1706342),
  (183029, 54), (183082, 2646), (183092, 407142), (183114, 6637238), (183153, 53366),
  (183164, 880254), (183217, 486), (183244, 225558), (183252, 386494), (183267, 7411094),
  (183316, 232398), (183325, 54), (183326, 76734), (183353, 54), (183360, 379718),
  (183370, 302814), (183433, 54), (183434, 54), (183468, 72614), (183514, 54), (183568, 28134),
  (183569, 54), (183591, 11982254), (183595, 15243174), (183596, 1566), (183623, 725598),
  (183639, 163862), (183657, 27358), (183685, 409518), (183703, 14094), (183729, 3094886),
  (183730, 54), (183731, 54), (183758, 54), (183839, 154494), (183855, 126622), (183892, 54),
  (183906, 1316542), (183920, 54), (183946, 58806), (184000, 54), (184091, 1619262),
  (184136, 54), (184158, 29278), (184207, 192438), (184324, 54), (184332, 166486),
  (184350, 2141998), (184352, 43254), (184368, 86446), (184405, 2646), (184423, 306486),
  (184459, 54), (184469, 215766), (184487, 54), (184497, 501454), (184541, 54),
  (184567, 54702), (184568, 54), (184649, 2646), (184658, 241398), (184702, 54),
  (184703, 6534), (184729, 54), (184767, 81758), (184833, 21446), (184864, 54),
  (184945, 633798), (184946, 47574), (184962, 107014), (184968, 130846), (184973, 54),
  (185004, 21694), (185016, 54182), (185025, 177542), (185054, 4006854), (185080, 5279094),
  (185081, 47142), (185107, 2493774), (185108, 35262), (185135, 10638), (185188, 1526742),
  (185238, 1009694), (185269, 139374), (185278, 5605758), (185296, 298134), (185323, 1636686),
  (185433, 686), (185458, 4409046), (185459, 54), (185540, 54), (185571, 106558),
  (185593, 19270278), (185610, 34054), (185621, 4301478), (185675, 1566), (185688, 420566),
  (185701, 41526), (185736, 12372902), (185817, 234638), (185863, 4310118), (185913, 3757534),
  (185918, 501174), (185943, 21262), (185961, 27518), (185998, 54), (185999, 968166),
  (186009, 37798), (186021, 1129646), (186026, 54), (186079, 54), (186107, 15839982),
  (186129, 60182), (186138, 466462), (186153, 20998), (186228, 50822), (186241, 54),
  (186296, 822798), (186395, 1215558), (186403, 116262), (186404, 6396462), (186431, 54),
  (186468, 55078), (186512, 2646), (186561, 20704166), (186566, 426654), (186579, 204046),
  (186647, 280638), (186655, 462006), (186656, 535662), (186723, 41462), (186732, 25078),
  (186790, 892062), (186809, 494694), (186864, 727262), (186879, 488182), (186934, 839574),
  (186954, 489238), (186963, 43702), (186997, 1032534), (187025, 1843398), (187047, 3079046),
  (187052, 54), (187115, 301734), (187132, 11760822), (187133, 54), (187150, 857214),
  (187231, 892854), (187248, 138854), (187295, 19942902), (187347, 196774), (187348, 367902),
  (187368, 120542), (187385, 695718), (187402, 13760982), (187461, 44566), (187483, 54),
  (187491, 686), (187537, 54), (187590, 686), (187699, 199638), (187749, 44134),
  (187781, 107838), (187791, 40822), (187808, 54), (187834, 649018494), (187854, 50494),
  (187861, 1347462), (187889, 54), (187896, 62102), (187902, 20198), (187923, 535046),
  (187951, 266022), (187956, 446518), (187970, 6534), (188050, 394038), (188070, 252446),
  (188131, 54), (188132, 54), (188154, 26518), (188160, 537686), (188177, 6174),
  (188186, 230742), (188222, 614646), (188266, 54), (188293, 54), (188320, 486),
  (188347, 16902), (188356, 711054), (188370, 131702), (188374, 2646), (188375, 54),
  (188420, 244206), (188428, 54), (188455, 54), (188491, 500382), (188536, 54),
  (188537, 1058886), (188538, 209422), (188627, 1201518), (188637, 167966), (188662, 7163406),
  (188672, 54), (188726, 486), (188834, 14958), (188860, 54), (188907, 2662), (188915, 718038)]

def WL41 : List (ℕ × ℕ) := [
  (188950, 614214), (189022, 54), (189023, 7107318), (189096, 3481502), (189108, 1121414),
  (189157, 2013606), (189159, 23846), (189184, 1566), (189201, 77134), (189239, 54),
  (189266, 54), (189300, 3412198), (189302, 1225998), (189320, 266598), (189327, 20158),
  (189328, 702846), (189392, 610614), (189401, 54), (189427, 54), (189428, 824526),
  (189481, 54), (189482, 54), (189509, 40878), (189513, 555718), (189562, 93582),
  (189582, 172526), (189617, 4879278), (189648, 19894), (189723, 63926), (189729, 519814),
  (189786, 35678), (189789, 247454), (189819, 62302), (189894, 344342), (189967, 1566),
  (189999, 58622), (190021, 4374), (190035, 6151766), (190048, 4806), (190058, 645822),
  (190094, 745974), (190122, 47494), (190149, 82934), (190157, 54), (190176, 81118),
  (190206, 33622), (190210, 54), (190212, 63814), (190238, 166644486), (190269, 6651854),
  (190283, 1073934), (190284, 3725078), (190318, 54), (190373, 45414), (190449, 66974),
  (190454, 10638), (190455, 25838), (190497, 159686), (190534, 54), (190539, 296798),
  (190554, 293638), (190561, 54), (190575, 65438), (190580, 826974), (190616, 54),
  (190660, 205182), (190723, 10422), (190743, 108278), (190778, 47358), (190877, 740574),
  (190884, 41086), (190913, 1133838), (190939, 57294), (190966, 54), (191020, 645832494),
  (191102, 54), (191115, 323662), (191169, 85438), (191245, 214686), (191263, 18846),
  (191264, 645568974), (191268, 98734), (191291, 1591542), (191362, 11599182), (191363, 6174),
  (191372, 54), (191399, 486), (191452, 16902), (191463, 66806), (191466, 69214),
  (191532, 40958), (191553, 577606), (191588, 4806), (191606, 897678), (191616, 26902),
  (191651, 900414), (191669, 54), (191695, 54), (191696, 354726), (191703, 235526),
  (191749, 284742), (191750, 54), (191835, 258982), (191857, 54), (191885, 4798278),
  (191901, 1223726), (191903, 329598), (191938, 54), (191956, 1031094), (192019, 14958),
  (192100, 54), (192102, 22766), (192155, 10422), (192261, 574118), (192263, 54),
  (192309, 33686), (192316, 1566), (192326, 23958), (192424, 10638), (192451, 17690886),
  (192474, 218782), (192477, 438166), (192478, 4806), (192505, 54), (192506, 54),
  (192587, 2646), (192605, 1189494), (192640, 54), (192690, 24502), (192726, 256798),
  (192830, 54), (192857, 486), (192864, 26438), (192883, 54), (192891, 90166),
  (192906, 129758), (192992, 1566), (193005, 188926), (193072, 54), (193083, 193598),
  (193100, 387342), (193127, 732942), (193143, 150334), (193215, 951838), (193216, 466974),
  (193233, 283334), (193234, 54), (193242, 17075158), (193299, 32222), (193320, 620462),
  (193368, 1988438), (193396, 10638), (193478, 54), (193531, 54), (193557, 46502),
  (193612, 54), (193639, 44334), (193640, 12582), (193657, 20532006), (193774, 54),
  (193775, 1566), (193829, 486), (193878, 32126), (193936, 4532382), (193950, 26294),
  (193963, 54), (193972, 569574), (194008, 6174), (194046, 405814), (194125, 54),
  (194126, 20205342), (194153, 1661958), (194180, 54), (194199, 3267542), (194315, 486),
  (194368, 54), (194369, 18394182), (194445, 126254), (194448, 238486), (194481, 228686),
  (194503, 54), (194530, 205038), (194612, 28134), (194628, 20326), (194634, 379046),
  (194657, 217926), (194665, 1566), (194675, 444078), (194694, 15855518), (194711, 594414),
  (194738, 297342), (194774, 54), (194802, 65126), (194844, 155998), (194854, 2023326),
  (194945, 441918), (194985, 4428166), (195006, 137374), (195039, 112078), (195070, 54),
  (195071, 1566), (195097, 862542), (195233, 828198), (195267, 54958), (195270, 328886),
  (195314, 22086), (195378, 21278), (195426, 20206), (195502, 11311758), (195503, 54),
  (195528, 2199806), (195557, 5238), (195558, 112262), (195585, 541438), (195624, 76606),
  (195664, 102654), (195718, 1566), (195719, 54), (195773, 4691358), (195799, 39582),
  (195818, 342558), (195819, 6107422), (195822, 132398), (195861, 90494), (195873, 47758),
  (195988, 54), (195998, 1910934), (196016, 486), (196070, 54), (196096, 486), (196107, 80246),
  (196141, 831582), (196160, 893286), (196204, 17141598), (196232, 54), (196268, 517878),
  (196401, 5528678), (196411, 460854), (196502, 13991454), (196509, 88118), (196512, 189374),
  (196524, 189806), (196610, 54), (196636, 341766), (196691, 54), (196734, 23174),
  (196752, 686), (196764, 30614), (196772, 8343918), (196799, 126414), (196803, 4822334),
  (196852, 21438), (196933, 54), (196961, 54), (196971, 117398), (197010, 281654),
  (197015, 54), (197096, 2646)]

def WL42 : List (ℕ × ℕ) := [
  (197132, 279918), (197136, 574382), (197163, 552974), (197194, 6174), (197204, 54),
  (197231, 486), (197240, 764118), (197258, 54), (197329, 480366), (197339, 54), (197365, 54),
  (197373, 2475446), (197384, 246438), (197438, 6174), (197447, 54), (197510, 322254),
  (197519, 299718), (197537, 6174), (197554, 486), (197582, 3825846), (197609, 54),
  (197700, 89918), (197721, 364862), (197735, 1227942), (197743, 10638), (197770, 54),
  (197780, 1051254), (197781, 642782), (197787, 219502), (197790, 181574), (197825, 2186622),
  (197835, 1505158), (197878, 2072142), (197906, 54), (197933, 54), (198066, 65878),
  (198067, 364878), (198094, 919782), (198135, 47374), (198148, 54), (198150, 568166),
  (198175, 1680534), (198184, 1250838), (198219, 354766), (198256, 54), (198311, 54),
  (198338, 16902), (198351, 99206), (198360, 110254), (198373, 419598), (198419, 2646),
  (198465, 50878), (198472, 54), (198473, 1566), (198483, 266806), (198500, 3352374),
  (198534, 183262), (198581, 7437798), (198626, 311886), (198630, 468086), (198634, 14668398),
  (198661, 6751782), (198715, 10638), (198716, 20142), (198787, 300654), (198810, 856814),
  (198828, 88246), (198878, 54), (198932, 486), (198958, 616518), (199026, 131686),
  (199067, 804438), (199068, 610838), (199120, 54), (199121, 699462), (199200, 318998),
  (199206, 64982), (199255, 486), (199309, 1283742), (199341, 261238), (199425, 330686),
  (199444, 54), (199453, 1668294), (199471, 10911942), (199472, 54), (199527, 58502),
  (199557, 56878), (199606, 54), (199607, 124038), (199633, 1566), (199689, 6266006),
  (199695, 93734), (199701, 197894), (199737, 90982), (199741, 20408598), (199796, 54),
  (199821, 196646), (199842, 29566), (199849, 54), (199893, 225902), (199989, 51862),
  (199992, 101294), (200011, 36342), (200012, 54), (200039, 189486), (200093, 512838),
  (200111, 1492254), (200115, 121358), (200129, 617886), (200173, 627534), (200174, 5238),
  (200200, 54), (200201, 15174), (200220, 64958), (200250, 112478), (200254, 54),
  (200281, 15688134), (200282, 54), (200362, 3089934), (200363, 203094), (200390, 486),
  (200409, 203998), (200415, 47822), (200417, 54), (200443, 14198598), (200451, 169622),
  (200496, 370582), (200525, 129654), (200550, 4953206), (200605, 1687446), (200649, 23486),
  (200660, 7523982), (200670, 300862), (200691, 30574), (200695, 721782), (200709, 52502),
  (200713, 486), (200740, 54), (200767, 31158), (200821, 54), (200849, 243918), (200886, 2662),
  (200898, 63334), (200943, 20134), (200956, 2891214), (200967, 19894), (200984, 54),
  (201011, 815454), (201039, 144542), (201091, 2668086), (201119, 486), (201146, 54),
  (201261, 1067318), (201307, 54), (201308, 67446), (201321, 57502), (201342, 528182),
  (201389, 28566), (201399, 41758), (201411, 601646), (201416, 54), (201465, 23942),
  (201479, 277686), (201483, 36614), (201552, 447422), (201684, 191414), (201713, 9181134),
  (201794, 183006), (201848, 23814), (201875, 54), (201879, 257182), (201901, 54),
  (201955, 14526), (201983, 54), (201996, 686), (202020, 31462), (202036, 54), (202145, 54),
  (202154, 1432422), (202167, 203254), (202298, 623718), (202307, 54), (202329, 20326),
  (202334, 515646), (202361, 54), (202387, 6194286), (202428, 144334), (202469, 2069982),
  (202477, 562446), (202505, 489438), (202522, 54), (202550, 3099006), (202575, 434734),
  (202623, 115054), (202630, 971406), (202649, 6374142), (202665, 169102), (202684, 14958),
  (202685, 54), (202711, 54), (202761, 48086), (202779, 2634142), (202788, 93182),
  (202873, 54), (202883, 680382), (202944, 254974), (202974, 2662), (202981, 3395358),
  (203027, 1659222), (203035, 54), (203063, 486), (203082, 46742), (203090, 54),
  (203121, 35318), (203184, 311398), (203197, 54), (203198, 1438182), (203208, 28814),
  (203289, 46862), (203368, 10106838), (203440, 54), (203485, 204894), (203548, 6253038),
  (203575, 54), (203576, 5675886), (203580, 31574), (203602, 141318), (203684, 490158),
  (203765, 15435414), (203784, 5638918), (203791, 5336118), (203818, 54), (203819, 19494),
  (203846, 54), (203880, 463142), (203926, 54), (203936, 1092654), (203982, 316838),
  (204006, 427694), (204035, 486), (204042, 468134), (204115, 6510942), (204143, 54),
  (204156, 342806), (204174, 599446), (204192, 389798), (204224, 54), (204232, 265878),
  (204251, 54), (204304, 54), (204331, 1566), (204358, 113238), (204385, 292302), (204386, 54),
  (204396, 1052422), (204412, 20971926), (204413, 71334), (204421, 399078), (204440, 5331582),
  (204539, 19253142), (204546, 426614), (204547, 6534), (204548, 54), (204574, 1739502),
  (204597, 497758), (204629, 54), (204630, 137486), (204672, 30766), (204699, 972022),
  (204709, 54), (204727, 396054), (204764, 486), (204790, 142182), (204808, 1588662),
  (204818, 54), (204819, 73142), (204897, 33094), (204898, 54), (204952, 54), (204979, 54),
  (204980, 54), (204988, 452646), (205034, 2646), (205060, 54), (205065, 40862), (205087, 486),
  (205095, 498398), (205114, 1566), (205142, 54), (205151, 362574), (205186, 1144998),
  (205197, 145342), (205227, 21382), (205281, 193574), (205303, 54)]

def WL43 : List (ℕ × ℕ) := [
  (205332, 418598), (205359, 119326), (205380, 20854), (205431, 275542), (205443, 13718),
  (205466, 15174), (205520, 1566), (205546, 54), (205547, 54), (205602, 29542), (205708, 54),
  (205763, 54), (205843, 54), (205884, 40958), (205905, 45062), (205925, 54), (205952, 54),
  (205968, 3045086), (205983, 9917854), (206005, 28566), (206025, 162598), (206033, 151902),
  (206086, 54), (206151, 68942), (206220, 11185078), (206248, 5805486), (206249, 54),
  (206275, 54), (206302, 486), (206310, 619118), (206358, 266782), (206411, 7031718),
  (206436, 45502), (206437, 10422), (206438, 150606), (206445, 243094), (206455, 1438542),
  (206478, 213326), (206492, 28134), (206519, 54), (206550, 397718), (206572, 54),
  (206599, 50598), (206600, 7099758), (206601, 3135118), (206653, 54), (206667, 37798),
  (206698, 195246), (206708, 486), (206724, 41086), (206753, 224118), (206798, 2673342),
  (206815, 6534), (206820, 482606), (206842, 54), (206843, 54), (206896, 235494),
  (206977, 14958), (207004, 54), (207005, 224478), (207009, 284366), (207027, 373894),
  (207031, 486), (207042, 686), (207054, 64822), (207059, 54), (207104, 236862), (207141, 686),
  (207166, 54), (207180, 300406), (207194, 14491062), (207221, 54), (207248, 19494),
  (207283, 222246), (207328, 54), (207347, 8587422), (207373, 1362222), (207382, 54),
  (207459, 43222), (207545, 133542), (207572, 6534), (207625, 11951118), (207626, 54),
  (207635, 1595934), (207654, 53806), (207663, 57238), (207724, 9556254), (207732, 567278),
  (207734, 54), (207768, 14605246), (207788, 2928582), (207814, 6534), (207846, 204142),
  (207895, 54), (207936, 141998), (207976, 1566), (207977, 54), (207978, 249478),
  (208017, 53726), (208071, 1353478), (208112, 556902), (208139, 54), (208164, 363574),
  (208175, 261918), (208192, 54), (208193, 1308366), (208200, 374942), (208202, 367398),
  (208266, 705686), (208283, 672822), (208290, 192958), (208329, 27998), (208336, 1513062),
  (208354, 16902), (208382, 139374), (208462, 6826734), (208481, 897174), (208482, 79342),
  (208490, 2052702), (208503, 111382), (208515, 76598), (208516, 5238), (208517, 54),
  (208544, 40878), (208605, 214366), (208623, 3286918), (208644, 142526), (208647, 99614),
  (208671, 20198), (208679, 28134), (208706, 54), (208746, 56702), (208761, 43174),
  (208767, 23174), (208868, 54), (208895, 486), (208917, 463102), (208922, 54),
  (208992, 101678), (209003, 16587774), (209007, 75814), (209029, 1566), (209049, 668102),
  (209088, 376966), (209111, 54), (209172, 255166), (209218, 130734), (209228, 1924326),
  (209245, 54), (209298, 78502), (209326, 54), (209327, 5478894), (209335, 577062),
  (209407, 54), (209412, 78998), (209427, 98822), (209461, 486), (209489, 54), (209516, 54),
  (209517, 313382), (209586, 45622), (209592, 85846), (209615, 1921302), (209637, 4312006),
  (209650, 54), (209670, 336526), (209677, 54), (209691, 99566), (209781, 25934),
  (209817, 91382), (209840, 3926934), (209858, 1915038), (209886, 6492326), (210002, 15153102),
  (210042, 76654), (210082, 6534), (210092, 1761678), (210119, 232542), (210132, 97718),
  (210163, 14958), (210182, 575334), (210217, 54), (210228, 686), (210299, 54),
  (210308, 1147374), (210325, 76734), (210327, 586294), (210372, 26302), (210380, 54),
  (210407, 54), (210408, 21334), (210460, 9645102), (210461, 54), (210567, 74318),
  (210568, 54), (210596, 486), (210622, 54), (210730, 54), (210785, 4806), (210798, 1176646),
  (210831, 197822), (210866, 54), (210903, 78382), (210919, 486), (210945, 197926),
  (210947, 35262), (210974, 54), (210978, 62438), (211027, 779598), (211036, 458478),
  (211055, 5228334), (211216, 54), (211217, 54), (211280, 250326), (211288, 1564902),
  (211332, 38854), (211379, 2212542), (211386, 401342), (211407, 953926), (211449, 41462),
  (211482, 582718), (211513, 54), (211541, 21438), (211605, 128878), (211612, 768006),
  (211702, 2503926), (211703, 231606), (211764, 3914398), (211783, 2206062), (211784, 1566),
  (211821, 198278), (211857, 67198), (211878, 586358), (211882, 346806), (211918, 54702),
  (211937, 519174), (211945, 4606038), (212000, 325998), (212080, 69606), (212108, 59238),
  (212162, 54), (212175, 9038102), (212187, 13429822), (212189, 54), (212233, 772614),
  (212241, 5206766), (212262, 178606), (212270, 54), (212310, 113686), (212358, 474406),
  (212431, 4927446), (212466, 275894), (212504, 602766), (212575, 280494), (212598, 185254),
  (212638, 367758), (212647, 54), (212661, 62774), (212674, 1566), (212710, 574038),
  (212745, 474134), (212756, 54), (212763, 29662), (212805, 159934), (212809, 54),
  (212826, 30718), (212837, 810918), (212844, 13718), (212871, 219806), (212873, 6174),
  (212890, 20142), (212913, 86998), (212917, 54), (212949, 265414), (212954, 1467846),
  (212961, 29366), (212971, 2646), (212972, 611009838), (213012, 43118), (213033, 34582),
  (213051, 2000014), (213079, 54), (213093, 267086), (213134, 6933222), (213197, 499734),
  (213198, 61718), (213225, 3114542), (213241, 54), (213267, 20222), (213315, 686),
  (213330, 59342), (213351, 71822), (213394, 501894), (213403, 54)]

def WL44 : List (ℕ × ℕ) := [
  (213513, 29758), (213555, 29894), (213561, 642622), (213565, 7920126), (213582, 968542),
  (213592, 1845342), (213619, 638334), (213620, 54), (213627, 255326), (213647, 54),
  (213691, 482094), (213705, 500534), (213711, 20222), (213755, 214326), (213759, 28102),
  (213773, 271638), (213780, 131902), (213782, 2445822), (213817, 297846), (213835, 486),
  (213837, 53758), (213862, 54), (213863, 1566), (214006, 829854), (214023, 52502),
  (214025, 54), (214052, 54), (214173, 57238), (214186, 14526), (214187, 6196446),
  (214196, 1173942), (214214, 54), (214215, 102878), (214245, 686), (214311, 161374),
  (214321, 486), (214344, 4333462), (214348, 6534), (214375, 5238), (214457, 47358),
  (214464, 28894), (214520, 212958), (214521, 25238), (214555, 593478), (214564, 486),
  (214619, 43038), (214681, 505782), (214727, 486), (214776, 23678), (214781, 5816502),
  (214809, 626302), (214835, 54), (214853, 1212102), (214871, 246798), (214893, 127598),
  (215007, 601246), (215014, 933102), (215055, 167686), (215060, 764334), (215077, 91422),
  (215158, 5775678), (215185, 1226934), (215244, 49814), (215293, 14094), (215321, 249534),
  (215347, 20233854), (215348, 23382), (215367, 44566), (215383, 398646), (215410, 308214),
  (215433, 209998), (215482, 5180166), (215529, 2036854), (215535, 38102), (215616, 120278),
  (215644, 54), (215671, 54), (215697, 24326), (215699, 10894662), (215716, 6174),
  (215914, 54), (215915, 17517438), (215916, 33526), (215942, 39366), (216012, 299254),
  (216015, 349982), (216027, 31454), (216039, 120886), (216050, 1252638), (216076, 1566),
  (216084, 341798), (216157, 2646), (216158, 54), (216186, 25342), (216238, 47358),
  (216239, 54), (216243, 40102), (216265, 4374), (216284, 23958), (216288, 142838),
  (216294, 24758), (216320, 54), (216428, 3143934), (216432, 57326), (216455, 54),
  (216481, 1292814), (216552, 134086), (216573, 155174), (216588, 97222), (216697, 54),
  (216698, 92934), (216747, 199942), (216806, 54), (216840, 175438), (216859, 302238),
  (216860, 1122606), (216873, 73558), (216886, 5889942), (216894, 392542), (216904, 1334574),
  (216921, 60542), (216941, 2646), (216951, 332438), (216984, 201046), (217002, 21446),
  (217048, 54), (217049, 10638), (217103, 54), (217139, 1665054), (217201, 681678),
  (217211, 54), (217218, 25822), (217264, 54), (217292, 54), (217345, 173718),
  (217407, 406414), (217427, 54), (217453, 54), (217534, 54), (217544, 822438),
  (217588, 22734), (217589, 54), (217616, 54), (217629, 162094), (217643, 257094),
  (217713, 281326), (217751, 13092246), (217776, 289582), (217777, 54), (217778, 1566),
  (217806, 28606), (217832, 13138254), (217940, 54), (217975, 404046), (217994, 4806),
  (218094, 291022), (218127, 421678), (218146, 1881774), (218155, 1566), (218169, 38846),
  (218174, 196254), (218182, 36342), (218199, 1797622), (218205, 289766), (218237, 54),
  (218246, 184806), (218272, 1392462), (218317, 28566), (218318, 54), (218361, 2206862),
  (218372, 1174662), (218391, 420694), (218399, 54), (218426, 54), (218460, 686),
  (218507, 5238), (218511, 421438), (218556, 36422), (218560, 1386342), (218568, 232478),
  (218588, 1009854), (218631, 93494), (218668, 54), (218679, 251422), (218722, 54),
  (218723, 54), (218730, 99838), (218804, 12582), (218884, 10289646), (218912, 5168502),
  (218925, 106478), (218946, 2662), (218947, 6601734), (218997, 41102), (219072, 137854),
  (219074, 54), (219127, 54), (219154, 54), (219204, 24902), (219226, 1246734),
  (219281, 776718), (219282, 137366), (219290, 2530062), (219316, 54), (219326, 1093734),
  (219371, 54), (219390, 686), (219423, 64502), (219424, 486), (219435, 108182),
  (219471, 38966), (219479, 1709478), (219641, 6534), (219676, 852318), (219695, 12582),
  (219703, 123462), (219711, 161134), (219721, 8426646), (219723, 114382), (219732, 70054),
  (219830, 6608142), (219856, 54), (219876, 57254), (219883, 2358774), (219884, 54),
  (219987, 75974), (219990, 168926), (220018, 54), (220044, 100262), (220099, 54),
  (220116, 43534), (220126, 2646), (220137, 113998), (220170, 45398), (220262, 54),
  (220289, 718686), (220316, 4374), (220370, 1727838), (220419, 686), (220424, 4806),
  (220432, 346806), (220452, 349886), (220458, 114118), (220459, 1066302), (220494, 42814),
  (220551, 30518), (220557, 330662), (220568, 207342), (220612, 54), (220626, 102694),
  (220641, 3252022), (220694, 22734), (220703, 1173222), (220704, 95198), (220747, 862542),
  (220761, 4956886), (220775, 54), (220793, 1204614), (220836, 93446), (220851, 5731286),
  (220855, 54), (220878, 254726), (220892, 1641294), (220910, 76734), (220911, 7073086),
  (220920, 116302), (220936, 93582), (221013, 589462), (221018, 54), (221072, 54),
  (221125, 11110446), (221152, 54), (221180, 421254), (221193, 247606), (221233, 54),
  (221314, 4806), (221328, 70054), (221341, 423414), (221342, 54), (221448, 686), (221503, 54),
  (221547, 461678), (221558, 54), (221613, 275038), (221640, 234142), (221683, 1308222)]

def WL45 : List (ℕ × ℕ) := [
  (221719, 54), (221739, 56878), (221746, 54), (221747, 5913702), (221791, 6174), (221800, 54),
  (221881, 108918), (221900, 764838), (221909, 5048622), (221963, 1566), (222098, 3107646),
  (222133, 1640502), (222152, 229014), (222206, 780246), (222232, 256662), (222233, 589577022),
  (222234, 66574), (222241, 274662), (222286, 54), (222291, 112862), (222300, 500102),
  (222305, 771462), (222340, 14094), (222395, 53838), (222396, 83222), (222405, 124598),
  (222423, 40126), (222432, 222542), (222475, 54), (222529, 27486), (222546, 58678),
  (222557, 54), (222576, 83006), (222591, 12056678), (222627, 289342), (222630, 2043166),
  (222647, 1061622), (222682, 708678), (222683, 597798), (222684, 169718), (222718, 2877174),
  (222723, 2033206), (222746, 7342974), (222768, 399934), (222810, 279998), (222816, 99478),
  (222852, 604246), (222854, 54), (222880, 46278), (222881, 7638894), (222934, 54),
  (222935, 54), (222962, 15174), (222984, 65662), (223033, 925758), (223042, 501174),
  (223043, 18503046), (223069, 486), (223097, 3198582), (223131, 86902), (223134, 36878),
  (223176, 472814), (223245, 2143654), (223259, 1566), (223312, 486), (223329, 540598),
  (223358, 744966), (223420, 54), (223448, 54), (223475, 130734), (223488, 569678),
  (223497, 46262), (223501, 32454), (223565, 879462), (223582, 92934), (223609, 54),
  (223663, 32454), (223690, 4806), (223762, 268038), (223771, 54), (223798, 12208806),
  (223825, 54), (223851, 427318), (223866, 50494), (223907, 6534), (223914, 555382),
  (224068, 54), (224077, 514422), (224095, 2646), (224114, 1075878), (224176, 54),
  (224230, 5238), (224231, 54), (224238, 90358), (224392, 3636846), (224420, 2566782),
  (224439, 20798), (224447, 3050622), (224456, 305334), (224496, 39374), (224499, 317854),
  (224554, 54), (224555, 2012958), (224559, 27758), (224616, 155494), (224685, 130478),
  (224694, 27358), (224698, 391806), (224715, 4141318), (224716, 54), (224726, 973638),
  (224744, 9437742), (224835, 29566), (224878, 582721182), (224879, 1050462), (224933, 486),
  (224959, 54), (224960, 54), (225059, 323262), (225069, 26902), (225121, 14958), (225122, 54),
  (225147, 116542), (225149, 6323886), (225176, 486), (225252, 106462), (225283, 54),
  (225311, 54), (225472, 1379646), (225499, 8738766), (225527, 54), (225553, 54),
  (225567, 131926), (225598, 1039158), (225615, 63286), (225618, 20542), (225639, 20134),
  (225662, 23814), (225663, 1699222), (225672, 233158), (225687, 141278), (225699, 622838),
  (225715, 13014), (225797, 126414), (225807, 257366), (225843, 3446806), (225846, 59062),
  (225850, 23382), (225870, 41222), (225905, 292086), (225932, 54), (225958, 656046),
  (225967, 330822), (225995, 303174), (226050, 133046), (226093, 4806), (226102, 649206),
  (226121, 54), (226158, 64822), (226201, 955206), (226202, 2646), (226218, 57158),
  (226251, 1115534), (226269, 354862), (226282, 54), (226299, 1574566), (226309, 3074598),
  (226317, 546734), (226336, 1121742), (226345, 1101798), (226364, 5238), (226445, 54),
  (226526, 154494), (226606, 23382), (226611, 216374), (226616, 365166), (226634, 486),
  (226662, 112246), (226686, 628814), (226687, 54), (226697, 433638), (226741, 2646),
  (226742, 19494), (226760, 267606), (226842, 30166), (226849, 5238), (226903, 44334),
  (226931, 36342), (226962, 74678), (226984, 54), (227010, 2721086), (227092, 54),
  (227093, 54), (227100, 314414), (227120, 486), (227148, 158758), (227173, 5408262),
  (227182, 10318518), (227200, 844182), (227254, 54), (227289, 621542), (227292, 43574),
  (227390, 13014), (227403, 84646), (227452, 490302), (227453, 1100718), (227470, 5238),
  (227534, 1054422), (227551, 1566), (227659, 54), (227712, 52214), (227745, 181942),
  (227775, 34406), (227794, 54), (227795, 54), (227821, 1566), (227859, 79006),
  (227883, 62518), (227898, 56806), (227928, 1702126), (227956, 28134), (227983, 54),
  (227985, 131966), (228047, 1219014), (228064, 574029774), (228117, 98662), (228145, 54),
  (228146, 54), (228171, 54974), (228226, 40878), (228227, 440046), (228236, 1290798),
  (228255, 60374), (228308, 573344622), (228324, 25526), (228380, 1801854), (228415, 486),
  (228429, 188126), (228524, 54), (228542, 562158), (228555, 119942), (228578, 317358),
  (228605, 54), (228640, 258246), (228750, 1913254), (228762, 141902), (228768, 58382),
  (228830, 330678), (228837, 3431318), (228864, 30182), (228928, 54), (228929, 20142),
  (229010, 1191726), (229091, 64854), (229116, 157958), (229118, 54), (229144, 136566),
  (229172, 51894), (229199, 250398), (229200, 3123494), (229280, 187974), (229333, 222966),
  (229362, 24974), (229441, 54), (229522, 12582), (229523, 546534), (229531, 519678),
  (229577, 54), (229620, 379486), (229657, 10638), (229658, 7267374), (229684, 6534),
  (229685, 185382), (229689, 96238), (229749, 24326), (229819, 54), (229828, 11609766),
  (229845, 273062), (229873, 486)]

def WL46 : List (ℕ × ℕ) := [
  (229900, 45414), (229901, 57726), (229923, 352246), (229927, 54), (230008, 54),
  (230018, 843606), (230027, 401454), (230062, 54), (230090, 54), (230097, 69518),
  (230130, 563366), (230170, 76734), (230171, 2646), (230189, 588726), (230225, 54),
  (230242, 858798), (230252, 54), (230279, 486), (230361, 71822), (230413, 12582),
  (230414, 54), (230468, 54), (230494, 54), (230601, 23038), (230720, 1182726),
  (230728, 796734), (230746, 1063494), (230769, 145006), (230775, 508142), (230791, 54),
  (230792, 54), (230855, 227646), (230954, 2646), (230981, 57294), (231009, 154646),
  (231034, 54), (231061, 54), (231062, 4071006), (231107, 528534), (231138, 214454),
  (231196, 697518), (231251, 5585598), (231261, 300598), (231278, 54), (231349, 304686),
  (231385, 54), (231386, 12582), (231395, 6174), (231439, 54702), (231467, 54),
  (231537, 82886), (231547, 54), (231548, 54), (231601, 54), (231737, 467046),
  (231754, 283086), (231756, 3018958), (231764, 1057158), (231837, 933646), (231894, 105766),
  (231924, 349054), (231952, 54), (231953, 54), (231988, 5975334), (232006, 54),
  (232007, 91422), (232020, 82286), (232056, 3151846), (232114, 4133214), (232125, 256294),
  (232128, 55078), (232169, 54), (232276, 1360206), (232277, 616518), (232296, 219638),
  (232330, 54), (232331, 54), (232339, 812502), (232358, 54), (232371, 43822),
  (232464, 137086), (232483, 198054), (232492, 10422), (232503, 33742), (232521, 26438),
  (232583, 1232046), (232587, 48494), (232601, 54), (232618, 1019862), (232682, 3291894),
  (232686, 206462), (232701, 184438), (232735, 54), (232755, 498878), (232763, 54),
  (232785, 77582), (232816, 2646), (232833, 301934), (232843, 881982), (232848, 394414),
  (232866, 686), (232914, 2748998), (232925, 1937142), (232932, 118838), (232952, 486),
  (232953, 156518), (232983, 688286), (232986, 59966), (233058, 364054), (233086, 5636574),
  (233087, 54), (233100, 450046), (233133, 205822), (233141, 54), (233196, 64958),
  (233241, 68942), (233249, 54), (233275, 486), (233310, 397006), (233330, 41526),
  (233385, 148726), (233491, 77382), (233492, 18846), (233546, 54), (233568, 235918),
  (233577, 93286), (233613, 8155174), (233626, 54), (233627, 572454), (233654, 54),
  (233689, 212526), (233694, 56198), (233724, 62494), (233735, 54), (233788, 54),
  (233834, 499734), (233870, 20142), (233913, 58622), (233970, 58462), (233977, 51894),
  (234004, 356238), (234015, 49934), (234032, 54), (234058, 14516118), (234220, 54),
  (234246, 64982), (234275, 54), (234297, 348182), (234338, 597582), (234382, 2724894),
  (234396, 27358), (234432, 27382), (234482, 179046), (234536, 760302), (234543, 98062),
  (234576, 293486), (234603, 611566), (234625, 54), (234626, 28134), (234662, 267966),
  (234679, 2646), (234738, 388142), (234750, 38102), (234759, 191894), (234761, 54),
  (234787, 54), (234842, 466182), (234915, 72526), (234918, 2662), (234927, 366526),
  (234949, 152982), (234976, 95742), (235058, 2579526), (235059, 134782), (235089, 52222),
  (235095, 94246), (235128, 254102), (235164, 179318), (235165, 295758), (235166, 54),
  (235242, 223198), (235251, 202054), (235300, 2411694), (235320, 45358), (235328, 35694),
  (235355, 13014), (235408, 54), (235409, 54), (235419, 695246), (235436, 54),
  (235443, 114094), (235462, 23814), (235570, 54), (235597, 54), (235598, 21438),
  (235626, 24646), (235641, 53398), (235678, 54), (235719, 102766), (235733, 54),
  (235746, 36742), (235759, 54), (235760, 199638), (235814, 15174), (235818, 154894),
  (235895, 54), (236003, 54), (236049, 84782), (236056, 54), (236082, 184774), (236083, 54),
  (236111, 486), (236164, 1768014), (236199, 143326), (236245, 36342), (236256, 22798),
  (236327, 13458366), (236397, 371974), (236489, 19494), (236538, 274798), (236542, 51894),
  (236543, 54), (236688, 1700398), (236704, 12582), (236731, 15174), (236732, 54),
  (236742, 165694), (236785, 2646), (236823, 2662), (236838, 60854), (236840, 1367118),
  (236866, 2096982), (236930, 193014), (236948, 54), (236982, 239414), (237020, 225702),
  (237028, 54), (237029, 54), (237190, 77382), (237216, 24334), (237217, 189486),
  (237218, 4806), (237271, 13014), (237273, 174646), (237298, 523206), (237299, 54),
  (237326, 496206), (237330, 143614), (237378, 23942), (237434, 54), (237442, 345798),
  (237462, 275414), (237474, 281174), (237523, 355086), (237595, 420606), (237649, 10103454),
  (237650, 3609846), (237651, 254798), (237704, 54), (237750, 338854), (237757, 54),
  (237784, 54), (237785, 54), (237812, 4374), (237831, 51286), (237840, 48214),
  (237909, 263542), (237912, 83006), (237946, 5238), (237984, 92198), (237991, 8637534),
  (238035, 68974)]

def WL47 : List (ℕ × ℕ) := [
  (238082, 54), (238109, 2646), (238208, 801126), (238215, 47942), (238243, 54), (238244, 54),
  (238271, 54), (238289, 744318), (238302, 26822), (238314, 166406), (238324, 114966),
  (238369, 1381878), (238378, 169614), (238406, 1566), (238415, 205974), (238443, 30398),
  (238469, 963126), (238470, 21718), (238548, 4692622), (238567, 71334), (238568, 12582),
  (238621, 486), (238630, 290502), (238635, 283942), (238648, 17699094), (238653, 29782),
  (238686, 124382), (238701, 327694), (238730, 23382), (238756, 54), (238811, 9315918),
  (238828, 1162422), (238866, 65126), (238892, 2646), (238910, 505566), (238919, 1566),
  (238953, 23854), (238954, 350694), (238972, 54), (238973, 17269254), (238992, 35942),
  (239001, 4215398), (239049, 68078), (239080, 6905358), (239094, 27814), (239099, 917478),
  (239134, 54), (239161, 5903334), (239162, 10780398), (239198, 487638), (239238, 1423958),
  (239323, 54), (239324, 54), (239337, 54086), (239346, 8667718), (239370, 28646),
  (239377, 19494), (239379, 272686), (239414, 519174), (239458, 54), (239475, 83038),
  (239485, 138896262), (239511, 46406), (239513, 4321998), (239566, 1566), (239622, 480742),
  (239647, 54), (239658, 440302), (239701, 11225358), (239728, 12884238), (239863, 313254),
  (239864, 173718), (239916, 38414), (239926, 1073718), (239944, 5238), (239971, 2646),
  (239972, 6979662), (239981, 953118), (239982, 602606), (239997, 194254), (240008, 525222),
  (240025, 54), (240072, 354566), (240078, 160814), (240126, 161198), (240142, 544878),
  (240151, 448326), (240214, 54), (240249, 32902), (240268, 54), (240269, 54), (240296, 54),
  (240322, 1841454), (240412, 6174), (240423, 118814), (240430, 10733094), (240450, 47438),
  (240457, 54), (240507, 54542), (240576, 89294), (240582, 111422), (240619, 54),
  (240637, 510318), (240656, 8847342), (240700, 27486), (240701, 80406), (240714, 100174),
  (240753, 526478), (240795, 507622), (240808, 486), (240816, 2662), (240826, 1087974),
  (240835, 54), (240862, 1566), (240863, 1033614), (240917, 1933254), (240918, 76654),
  (240960, 6597494), (240997, 13309326), (240998, 54), (241017, 23486), (241024, 54),
  (241052, 2005398), (241079, 54), (241088, 487926), (241176, 20782), (241187, 14958),
  (241236, 62102), (241240, 54), (241269, 28286), (241281, 38366), (241299, 203054),
  (241348, 54), (241394, 577062), (241403, 3726054), (241484, 54), (241521, 490822),
  (241565, 54), (241583, 181854), (241590, 47942), (241592, 54), (241627, 267606),
  (241645, 1566), (241646, 54), (241710, 22054), (241726, 231606), (241772, 1174302),
  (241807, 137646), (241808, 54), (241899, 124918), (241996, 15174), (242077, 2646),
  (242131, 14071374), (242159, 54), (242160, 272134), (242212, 54), (242220, 77398),
  (242240, 54), (242262, 116726), (242271, 26342), (242293, 13244526), (242328, 88766),
  (242331, 93286), (242338, 1187334), (242361, 76598), (242366, 289206), (242402, 54),
  (242429, 486), (242438, 520686), (242457, 2011382), (242509, 4374), (242523, 37958),
  (242580, 93614), (242600, 290502), (242604, 380678), (242699, 5238), (242709, 149654),
  (242725, 73494), (242760, 92702), (242775, 45742), (242780, 6442038), (242787, 141646),
  (242823, 247966), (242853, 79022), (242861, 2646), (242887, 54), (242901, 752086),
  (242942, 54), (242982, 84046), (242991, 26326), (243018, 35918), (243057, 686),
  (243090, 190054), (243129, 55486), (243131, 3268134), (243185, 54), (243228, 7235582),
  (243229, 219798), (243292, 54), (243293, 54), (243303, 1748222), (243347, 54),
  (243354, 312694), (243360, 36254), (243374, 54), (243378, 2662262), (243392, 322398),
  (243400, 55566), (243427, 35694), (243504, 422494), (243516, 242534), (243536, 54),
  (243581, 1001358), (243606, 23038), (243609, 86974), (243612, 154478), (243616, 54),
  (243678, 399598), (243689, 543798), (243693, 199534), (243724, 486), (243743, 302526),
  (243770, 1194174), (243822, 385598), (243859, 54), (243887, 14094), (243913, 54),
  (243914, 54), (243941, 20142), (243948, 227182), (243972, 48502), (244011, 115118),
  (244022, 54), (244086, 933646), (244102, 54), (244183, 9108558), (244210, 7356582),
  (244264, 1566), (244265, 6013494), (244383, 23726), (244404, 23974), (244452, 58486),
  (244453, 486), (244481, 54), (244515, 158854), (244615, 2478438), (244616, 95742),
  (244643, 112374), (244670, 1566), (244705, 1534446), (244722, 54478), (244723, 2646),
  (244724, 2646), (244725, 66806), (244767, 24334), (244791, 80702), (244809, 2662),
  (244824, 560926), (244832, 54), (244848, 33262), (244932, 118886), (244938, 84278),
  (244966, 54), (244993, 4394142), (245002, 1420542), (245021, 2136294), (245047, 1566),
  (245064, 78998), (245079, 495182), (245155, 54), (245156, 112806), (245209, 262494),
  (245237, 17119566), (245265, 24022), (245317, 4806), (245345, 486), (245371, 187326),
  (245398, 6663438), (245399, 266598), (245481, 234662), (245538, 168382), (245559, 215686),
  (245560, 5507622), (245561, 54), (245614, 10638), (245615, 54), (245769, 57406),
  (245776, 54), (245777, 6534), (245804, 54), (245877, 468646), (245884, 54), (245911, 486),
  (245938, 8550414), (246047, 2646), (246100, 54), (246128, 54), (246168, 333358),
  (246174, 59518), (246177, 131798), (246243, 686), (246254, 733878)]

def WL48 : List (ℕ × ℕ) := [
  (246289, 54), (246290, 54), (246300, 37342), (246317, 192942), (246330, 191606),
  (246345, 38326), (246357, 21542), (246387, 88406), (246429, 6944174), (246451, 54),
  (246505, 50598), (246528, 499558), (246552, 11404102), (246560, 4374), (246570, 27718),
  (246576, 72262), (246582, 258758), (246587, 54), (246595, 697446), (246597, 13718),
  (246639, 33622), (246681, 113654), (246694, 54), (246695, 2447766), (246776, 6534),
  (246783, 8054542), (246857, 14653494), (246897, 2662), (246903, 1176646), (246924, 84758),
  (246937, 54), (246938, 195318), (247071, 269278), (247100, 54), (247134, 372046),
  (247154, 54), (247235, 54), (247352, 193302), (247406, 215766), (247434, 475262),
  (247477, 54), (247478, 54), (247505, 54), (247539, 109958), (247639, 2903742),
  (247653, 21446), (247666, 22086), (247683, 30214), (247716, 119446), (247721, 54),
  (247815, 162166), (247829, 54), (247855, 486), (247882, 54), (247963, 54), (247990, 41526),
  (248044, 3887406), (248045, 54), (248094, 227446), (248152, 54), (248202, 686),
  (248207, 3099006), (248215, 1295694), (248295, 2039222), (248306, 410526), (248334, 69214),
  (248368, 880254), (248369, 4541886), (248449, 35262), (248451, 366902), (248496, 989702),
  (248529, 98062), (248584, 486), (248586, 432518), (248589, 20078), (248612, 229662),
  (248638, 54), (248639, 54), (248719, 1108134), (248774, 14556294), (248802, 2662),
  (248827, 486), (248918, 383814), (248926, 295686), (248936, 227718), (248964, 92366),
  (249003, 240566), (249017, 15219198), (249024, 40822), (249027, 371134), (249044, 2045142),
  (249079, 392166), (249093, 471494), (249124, 19494), (249170, 1376766), (249171, 1908694),
  (249178, 54), (249179, 54), (249186, 59222), (249205, 54), (249223, 5831262),
  (249234, 404654), (249296, 637542), (249304, 794358), (249313, 4790502), (249354, 20918),
  (249366, 67294), (249422, 40878), (249486, 124702), (249502, 2611062), (249529, 54),
  (249530, 73494), (249549, 29774), (249556, 486), (249584, 22734), (249611, 133542),
  (249664, 54), (249719, 8972046), (249745, 1566), (249773, 54), (249801, 2439118),
  (249852, 1583342), (249885, 238726), (249908, 54), (249915, 29542), (249917, 6174),
  (249936, 365702), (249962, 486), (250015, 1346814), (250016, 501274062), (250042, 486),
  (250053, 218846), (250070, 262494), (250125, 326518), (250178, 6038334), (250231, 54),
  (250258, 1566), (250260, 686), (250285, 14172246), (250290, 217174), (250339, 54),
  (250475, 88398), (250501, 14526), (250545, 140398), (250555, 9570582), (250592, 607302),
  (250623, 79102), (250636, 194022), (250664, 1566), (250745, 6325182), (250788, 48182),
  (250798, 41094), (250803, 57742), (250851, 161254), (250860, 126598), (250880, 14320206),
  (250888, 713862), (250907, 54), (250941, 31574), (250944, 2553622), (250987, 54),
  (251014, 486), (251041, 151902), (251042, 54), (251078, 1008702), (251141, 740358),
  (251202, 237142), (251204, 16593606), (251229, 131678), (251284, 54), (251285, 2112102),
  (251320, 1338534), (251388, 686), (251392, 54), (251403, 35582), (251474, 54),
  (251481, 29558), (251609, 3978774), (251635, 54), (251734, 466902), (251743, 117126),
  (251754, 116414), (251760, 26342), (251878, 2646), (252006, 51286), (252013, 54),
  (252040, 54), (252121, 5429646), (252138, 49094), (252148, 2217942), (252149, 486),
  (252175, 1321542), (252176, 54), (252203, 711558), (252225, 8796982), (252229, 805302),
  (252257, 150606), (252294, 287486), (252318, 686), (252330, 44606), (252336, 294214),
  (252365, 54), (252378, 25238), (252417, 818398), (252418, 54), (252513, 41086),
  (252527, 14526), (252581, 1243134), (252635, 4234518), (252657, 61286), (252680, 380502),
  (252688, 703998), (252742, 54), (252756, 479702), (252770, 292518), (252807, 84886),
  (252814, 197622), (252824, 55134), (252846, 133526), (252904, 54), (252957, 99422),
  (252986, 94662), (253049, 1194462), (253066, 21438), (253094, 54), (253121, 4374),
  (253148, 54), (253157, 1147374), (253161, 78238), (253174, 20142), (253210, 1707246),
  (253281, 46142), (253308, 65942), (253310, 1836054), (253336, 10422), (253364, 486),
  (253391, 4601502), (253395, 221846), (253446, 686), (253471, 54), (253472, 54),
  (253548, 24502), (253575, 21334), (253581, 162406), (253660, 151902), (253701, 23054),
  (253742, 54), (253769, 3436182), (253890, 60638), (253930, 898614), (253958, 22086),
  (253984, 2646), (253985, 2646), (254039, 9597582), (254070, 52454), (254101, 1187118),
  (254120, 54), (254155, 16197822), (254200, 54), (254227, 54), (254268, 98678), (254308, 54),
  (254309, 54), (254310, 44566), (254371, 276894), (254373, 387526), (254389, 54),
  (254409, 102766)]

def WL49 : List (ℕ × ℕ) := [
  (254470, 54), (254471, 4798062), (254475, 686), (254524, 1780758), (254525, 54),
  (254541, 454726), (254633, 1554606), (254655, 68566), (254769, 1581622), (254794, 6776838),
  (254822, 486), (254849, 1566), (254875, 54), (255010, 54), (255011, 54), (255036, 247262),
  (255065, 486), (255102, 85366), (255165, 29366), (255192, 24214), (255198, 78902),
  (255199, 1084806), (255200, 54), (255208, 410598), (255218, 524358), (255262, 790974),
  (255264, 76606), (255327, 123742), (255362, 1566), (255405, 686), (255408, 88174),
  (255415, 54), (255442, 12495654), (255443, 219942), (255450, 34702), (255551, 486),
  (255659, 54), (255766, 54), (255786, 146966), (255794, 47142), (255820, 6534),
  (255847, 478169838), (255848, 54), (255900, 288902), (255901, 54), (255912, 28102),
  (255947, 224838), (256026, 458534), (256091, 477168462), (256144, 54), (256149, 25294),
  (256171, 34614), (256190, 6174), (256272, 39454), (256356, 288758), (256369, 907398),
  (256377, 862982), (256388, 747414), (256404, 36614), (256431, 20542), (256433, 698094),
  (256495, 54), (256523, 486), (256542, 28174), (256549, 54), (256550, 12582),
  (256577, 9493902), (256631, 2646), (256657, 35262), (256671, 24694), (256675, 1249686),
  (256695, 29662), (256712, 611766), (256739, 3500118), (256747, 507798), (256836, 155734),
  (256873, 54), (256954, 54), (256982, 54), (257117, 12334734), (257143, 2253366),
  (257224, 3712662), (257238, 67846), (257252, 696438), (257271, 551438), (257277, 10237358),
  (257278, 54), (257377, 905166), (257441, 9725886), (257521, 16036974), (257538, 22006),
  (257549, 76086), (257553, 34246), (257584, 275166), (257629, 54), (257683, 54),
  (257738, 486), (257766, 22886), (257791, 54), (257796, 252454), (257805, 28894),
  (257872, 54), (257873, 54), (257953, 2646), (257973, 173702), (257999, 408222),
  (258000, 175022), (258039, 2336414), (258081, 29686), (258088, 1566), (258089, 54),
  (258116, 54), (258186, 43222), (258237, 241078), (258278, 627534), (258285, 64406),
  (258309, 78646), (258390, 131438), (258412, 54), (258440, 54), (258494, 45414),
  (258543, 216262), (258573, 53854), (258575, 15174), (258621, 360574), (258628, 1626318),
  (258642, 34654), (258655, 804438), (258687, 240742), (258726, 1042318), (258737, 2646),
  (258763, 10985166), (258764, 1674054), (258817, 54), (258818, 54), (258845, 581526),
  (258876, 2662), (258934, 549486), (258971, 242982), (258993, 172982), (259044, 12337414),
  (259168, 54), (259169, 41094), (259178, 6174), (259212, 21278), (259222, 437454),
  (259277, 1611414), (259314, 20534), (259323, 261062), (259374, 1180214), (259385, 54),
  (259412, 7006446), (259425, 70166), (259474, 896094), (259519, 486), (259530, 29182),
  (259573, 7995942), (259590, 43198), (259617, 27926), (259620, 686), (259653, 30598),
  (259674, 2139238), (259708, 413046), (259762, 43254), (259790, 14526), (259807, 283158),
  (259817, 10422), (259818, 56822), (259875, 98782), (259880, 181422), (259898, 10422),
  (259905, 73774), (259914, 1499302), (259933, 401094), (259952, 35694), (259959, 97502),
  (260060, 76734), (260113, 54), (260114, 54), (260140, 44334), (260150, 1035486),
  (260168, 486), (260199, 25598), (260232, 110678), (260302, 54), (260303, 39582),
  (260357, 8542206), (260364, 503246), (260464, 8202654), (260518, 54), (260519, 54),
  (260546, 423414), (260626, 54), (260697, 1168454), (260708, 54), (260780, 1216422),
  (260811, 25526), (260842, 54), (260870, 54), (260897, 136566), (260898, 347678),
  (260937, 133582), (260951, 22734), (260967, 6221654), (261003, 128542), (261004, 1393254),
  (261031, 54), (261039, 507302), (261050, 481158), (261059, 1683342), (261086, 154494),
  (261093, 47326), (261112, 102006), (261150, 36574), (261193, 579582), (261198, 258574),
  (261203, 257454), (261247, 1276182), (261267, 41486), (261301, 1853766), (261346, 1660374),
  (261383, 5739174), (261399, 41486), (261409, 54), (261471, 20534), (261490, 1566),
  (261499, 479646), (261513, 82358), (261570, 262286), (261579, 247646), (261597, 1610254),
  (261599, 54), (261653, 54), (261678, 686), (261679, 23382), (261680, 54), (261795, 25838),
  (261798, 273958), (261814, 11346102), (261841, 54), (261886, 291366), (261896, 1566),
  (261922, 452411838), (261924, 199646), (261976, 133542), (261977, 54), (262020, 3865022),
  (262023, 34094), (262053, 78742), (262058, 54), (262085, 1577286), (262138, 1965654),
  (262192, 4374), (262246, 794718), (262260, 307742), (262265, 6174), (262296, 225086),
  (262327, 54), (262353, 396182), (262364, 6174), (262380, 2884862), (262452, 553838),
  (262461, 2490278), (262463, 54), (262479, 77134), (262488, 331046), (262543, 10638),
  (262570, 59238), (262571, 54), (262579, 795222), (262625, 7085502)]

def WL50 : List (ℕ × ℕ) := [
  (262668, 422542), (262680, 452126), (262725, 36758), (262732, 54), (262787, 54),
  (262949, 54), (263031, 34406), (263094, 82702), (263110, 1892862), (263111, 8422326),
  (263138, 54), (263164, 2076678), (263192, 1566), (263219, 1473174), (263247, 195694),
  (263286, 35414), (263299, 13014), (263307, 4735958), (263354, 54), (263361, 195758),
  (263381, 3072438), (263461, 54), (263592, 62462), (263637, 7972006), (263759, 54),
  (263785, 1050462), (263786, 54), (263790, 35806), (263866, 54), (263867, 54),
  (263874, 391814), (263893, 486), (263920, 64854), (264003, 60638), (264028, 810702),
  (264056, 4374), (264075, 176158), (264082, 54), (264083, 20142), (264186, 151966),
  (264217, 3361014), (264249, 22894), (264272, 54), (264306, 304406), (264325, 10823598),
  (264426, 10702382), (264434, 148662), (264459, 59222), (264462, 37358), (264487, 54),
  (264523, 777726), (264568, 235494), (264569, 2646), (264649, 60966), (264650, 54),
  (264677, 54), (264762, 454774), (264765, 686), (264774, 1738286), (264811, 54),
  (264812, 228366), (264865, 486), (264909, 52214), (264920, 10638), (264921, 64126),
  (264973, 929286), (265001, 22086), (265050, 267118), (265054, 794718), (265074, 29774),
  (265224, 97222), (265243, 54), (265244, 54), (265263, 190222), (265334, 385326),
  (265353, 1609846), (265378, 3206358), (265405, 1566), (265406, 54), (265451, 6174),
  (265459, 54), (265488, 358702), (265524, 70214), (265539, 170398), (265545, 251078),
  (265551, 187526), (265567, 54), (265568, 6590214), (265572, 36742), (265594, 1137726),
  (265647, 1368766), (265648, 54), (265695, 3919118), (265757, 486), (265761, 34862),
  (265792, 1227726), (265794, 349174), (265810, 12053718), (265818, 51878), (265891, 2646),
  (265909, 279198), (266008, 763326), (266027, 54), (266049, 45502), (266055, 324182),
  (266187, 24902), (266216, 54), (266223, 124094), (266260, 266022), (266289, 54182),
  (266296, 54), (266306, 684198), (266328, 2960246), (266350, 54), (266351, 54),
  (266377, 41742), (266379, 5616686), (266404, 3354534), (266432, 13014), (266454, 270566),
  (266513, 80406), (266539, 54), (266621, 64854), (266657, 372942), (266729, 486),
  (266757, 116222), (266783, 54), (266838, 60238), (266944, 4806), (266945, 54),
  (266999, 1009854), (267006, 99838), (267030, 87734), (267052, 486), (267080, 54),
  (267125, 612702), (267156, 26518), (267160, 210006), (267188, 110862), (267210, 282622),
  (267255, 69766), (267322, 14526), (267332, 352062), (267349, 54), (267350, 63774),
  (267378, 108166), (267435, 1758734), (267471, 468374), (267483, 89774), (267485, 8712414),
  (267510, 47758), (267525, 20798), (267538, 486), (267588, 2857294), (267636, 66398),
  (267646, 1883358), (267673, 2051838), (267727, 93582), (267729, 483382), (267765, 25598),
  (267835, 54), (267889, 1301886), (267890, 377406), (267899, 5622462), (267917, 14958),
  (267993, 435038), (267998, 2646), (268044, 764614), (268078, 54), (268079, 54),
  (268092, 20078), (268168, 868302), (268213, 5383206), (268240, 54), (268269, 4191766),
  (268322, 54), (268375, 914598), (268403, 54), (268439, 6174), (268443, 192662),
  (268484, 1350486), (268488, 3099446), (268500, 251318), (268537, 76734), (268560, 93454),
  (268564, 54), (268581, 48742), (268619, 54), (268645, 76086), (268646, 6618942),
  (268665, 63134), (268700, 54), (268752, 58046), (268781, 259254), (268806, 116726),
  (268807, 54), (268826, 1064862), (268830, 21478), (268835, 2100654), (268862, 11181294),
  (268889, 5238), (268911, 42974), (268926, 38414), (268938, 395302), (268969, 10422),
  (268988, 510318), (269004, 91558), (269085, 55078), (269113, 391518), (269184, 29566),
  (269212, 54), (269213, 20142), (269267, 54), (269310, 86582), (269325, 65414),
  (269374, 466182), (269375, 2614086), (269376, 118886), (269382, 496646), (269428, 54),
  (269520, 88246), (269536, 54), (269541, 23726), (269555, 254574), (269613, 38854),
  (269645, 58806), (269662, 244206), (269698, 54), (269725, 486), (269752, 22086),
  (269780, 226854), (269793, 514918), (269808, 21958), (269811, 686), (269852, 527166),
  (269861, 2003022), (269907, 45134), (269915, 54), (269941, 54), (269943, 205046),
  (269950, 225846), (270004, 709974), (270023, 12582), (270058, 650358), (270180, 162038),
  (270240, 52166), (270257, 595278), (270265, 1258038), (270292, 1757214), (270348, 196454),
  (270369, 470486), (270374, 486), (270390, 367958), (270438, 146518), (270447, 21806),
  (270453, 22798), (270482, 54), (270522, 52526), (270555, 246286), (270643, 54),
  (270684, 62318), (270697, 486), (270716, 863046), (270751, 54), (270752, 54),
  (270804, 508982), (270840, 686)]

def WL51 : List (ℕ × ℕ) := [
  (270886, 1566), (270887, 466182), (270913, 54), (270914, 34614), (270939, 192766),
  (271004, 534078), (271068, 362126), (271103, 134622), (271129, 431622), (271137, 308054),
  (271157, 54), (271182, 395606), (271238, 54), (271318, 74142), (271353, 332518),
  (271390, 312318), (271399, 1566), (271410, 55054), (271426, 486), (271453, 54), (271454, 54),
  (271481, 54), (271552, 870894), (271643, 1566918), (271697, 7800894), (271777, 4806),
  (271805, 1566), (271809, 91942), (271832, 486), (271885, 21438), (271929, 27422),
  (271967, 10777158), (272020, 10378422), (272047, 54), (272102, 54), (272127, 205294),
  (272148, 4638734), (272155, 58806), (272286, 219158), (272322, 26902), (272349, 5756614),
  (272412, 164014), (272424, 97718), (272426, 54), (272435, 781038), (272470, 242982),
  (272587, 36342), (272588, 1566), (272614, 23382), (272641, 486), (272669, 54),
  (272676, 138238), (272715, 90982), (272776, 54), (272785, 1558782), (272830, 70254),
  (272831, 2124414), (272832, 8230022), (272844, 32638), (272858, 1566), (272875, 221814),
  (272886, 25238), (272898, 288806), (272938, 54), (272939, 13014), (272946, 421342),
  (272964, 93182), (272997, 135142), (273019, 54), (273047, 210438), (273056, 369774),
  (273072, 408878), (273100, 8682174), (273127, 4374), (273155, 54), (273163, 740574),
  (273181, 4350942), (273182, 54), (273190, 774054), (273236, 54), (273290, 2119446),
  (273291, 1173158), (273317, 54), (273461, 698094), (273470, 182934), (273478, 34614),
  (273498, 45062), (273523, 498438), (273560, 270486), (273600, 71206), (273642, 4021814),
  (273705, 196918), (273732, 1782718), (273744, 34334), (273749, 15174), (273756, 258374),
  (273757, 7716726), (273776, 486), (273810, 125942), (273819, 42278), (273840, 290126),
  (273849, 3329678), (273939, 87422), (273996, 152566), (274010, 1047582), (274026, 686),
  (274050, 179918), (274072, 8161614), (274073, 54), (274099, 93798), (274127, 5238),
  (274164, 197462), (274206, 104726), (274270, 179046), (274272, 208366), (274288, 9767574),
  (274360, 454446), (274387, 1242342), (274434, 366598), (274440, 429566), (274477, 54),
  (274478, 731862), (274505, 10766358), (274514, 721998), (274532, 54), (274539, 103022),
  (274559, 67446), (274612, 5238), (274640, 844614), (274653, 103606), (274693, 54),
  (274702, 408582), (274720, 54), (274721, 54), (274737, 180814), (274748, 292086),
  (274791, 22054), (274836, 39686), (274855, 54), (274856, 41526), (274857, 31342),
  (274878, 32278), (274882, 459702), (274909, 1728054), (274932, 514526), (274937, 1566),
  (275016, 126598), (275017, 54), (275071, 486), (275098, 53838), (275099, 54),
  (275115, 153982), (275179, 54), (275193, 20518), (275206, 617598), (275232, 81878),
  (275234, 486), (275260, 403758), (275270, 295398), (275295, 96542), (275322, 271774),
  (275415, 133582), (275422, 100247814), (275423, 7259814), (275490, 209158), (275493, 90878),
  (275504, 54), (275505, 27382), (275611, 54), (275612, 1363662), (275637, 99566),
  (275666, 4806), (275676, 106718), (275692, 2646), (275693, 4806), (275701, 706086),
  (275746, 460998), (275799, 89014), (275814, 20998), (275828, 54), (275854, 1055214),
  (275855, 21438), (275864, 345798), (275931, 2313838), (275935, 222966), (275963, 486),
  (275967, 193406), (275985, 686), (276018, 29782), (276233, 53838), (276250, 181854),
  (276340, 108918), (276345, 172358), (276375, 480574), (276394, 41526), (276395, 54),
  (276396, 1162958), (276402, 60182), (276422, 313902), (276458, 625302), (276512, 6349086),
  (276529, 486), (276537, 48838), (276556, 4806), (276583, 4806), (276584, 54),
  (276593, 401094), (276618, 334318), (276663, 2703382), (276738, 67582), (276745, 54),
  (276746, 5238), (276771, 106478), (276880, 1661526), (276915, 177686), (276961, 54),
  (277014, 686), (277038, 196982), (277047, 106814), (277053, 177286), (277065, 172222),
  (277069, 54), (277089, 237374), (277113, 1647086), (277205, 557982), (277233, 239678),
  (277240, 1338894), (277241, 637614), (277258, 486), (277285, 229014), (277286, 1566),
  (277313, 54), (277362, 85958), (277366, 54), (277383, 223598), (277474, 14958),
  (277475, 108918), (277492, 687294), (277536, 26126), (277593, 221294), (277618, 1157094),
  (277698, 155054), (277704, 54958), (277717, 54), (277737, 43982), (277782, 51862),
  (277879, 54), (277968, 2692526), (277977, 268486), (277998, 76094), (278019, 45622),
  (278043, 1268414), (278055, 377878), (278122, 54), (278123, 54), (278131, 180702),
  (278142, 686), (278167, 916038), (278244, 475414), (278257, 20142), (278285, 54),
  (278355, 90526), (278419, 494694), (278420, 54), (278433, 335246), (278446, 1566),
  (278447, 10460934), (278481, 75598), (278528, 4858758), (278581, 341766), (278582, 732942),
  (278608, 649998), (278682, 364214), (278706, 20078), (278796, 36878), (278824, 818694),
  (278825, 210006), (278851, 1229526), (278879, 918054), (278906, 54), (278914, 493758),
  (278987, 54)]

def WL52 : List (ℕ × ℕ) := [
  (279095, 54), (279126, 113846), (279148, 54), (279183, 196414), (279202, 486),
  (279246, 217654), (279328, 225846), (279337, 54), (279351, 66422), (279364, 1636038),
  (279378, 97574), (279390, 34862), (279414, 236798), (279418, 54), (279473, 54),
  (279482, 1300878), (279544, 198054), (279608, 486), (279630, 159398), (279636, 415238),
  (279661, 2646), (279680, 1138446), (279715, 54), (279797, 5819094), (279823, 54),
  (279824, 54), (279837, 27934), (279846, 323846), (279851, 486), (279905, 76734),
  (279924, 30398), (279958, 266598), (279959, 54), (279960, 474542), (279972, 23726),
  (279984, 481526), (279986, 54), (280023, 218222), (280103, 795726), (280120, 54),
  (280121, 54), (280125, 66622), (280147, 150606), (280148, 5505678), (280182, 158902),
  (280201, 646326), (280202, 54), (280355, 493326), (280363, 54), (280391, 55134),
  (280426, 192438), (280445, 2646), (280481, 341622), (280516, 282078), (280552, 54),
  (280553, 54), (280566, 77446), (280635, 151222), (280644, 20998), (280652, 205974),
  (280660, 3243078), (280687, 54), (280688, 1566), (280796, 54), (280886, 6174),
  (280896, 121718), (280958, 54), (280994, 747342), (281001, 23734), (281066, 467046),
  (281174, 50598), (281202, 119318), (281223, 186766), (281227, 2135646), (281247, 65174),
  (281254, 2442582), (281255, 1285254), (281265, 336166), (281281, 54), (281304, 118838),
  (281322, 36422), (281336, 10212102), (281363, 5238), (281385, 306718), (281416, 2531358),
  (281434, 123462), (281435, 224766), (281444, 36342), (281496, 77422), (281497, 54),
  (281532, 63598), (281587, 7965198), (281588, 1115838), (281632, 486), (281799, 187118),
  (281840, 705438), (281867, 341046), (281875, 4374), (281902, 54), (281946, 388966),
  (281983, 54), (282065, 54), (282105, 149686), (282147, 181198), (282189, 214694),
  (282210, 40966), (282225, 1037678), (282258, 686), (282263, 340182), (282307, 2172366),
  (282357, 58382), (282389, 54), (282459, 359054), (282470, 54), (282497, 9633222),
  (282551, 2646), (282739, 54), (282795, 201406), (282820, 13014), (282875, 1331262),
  (282921, 1694006), (282956, 54), (282983, 5506758), (283037, 1566), (283064, 54),
  (283090, 23814), (283107, 151318), (283145, 4353966), (283194, 149014), (283207, 674694),
  (283225, 54), (283226, 54), (283253, 486), (283275, 172798), (283388, 54), (283389, 27134),
  (283401, 117886), (283460, 216774), (283500, 21542), (283506, 326614), (283513, 541278),
  (283523, 54), (283550, 1566), (283576, 486), (283586, 1014894), (283603, 424062),
  (283667, 469998), (283684, 54), (283698, 28286), (283711, 35262), (283712, 89478),
  (283739, 4374), (283765, 4806), (283766, 54), (283773, 120206), (283801, 362214),
  (283851, 107398), (283863, 64102), (283873, 409806), (283874, 344985534), (283954, 219942),
  (283955, 54), (283962, 33806), (283964, 647118), (284040, 30398), (284089, 54), (284279, 54),
  (284298, 124078), (284305, 210438), (284333, 1566), (284349, 58262), (284359, 195318),
  (284367, 75982), (284376, 5263742), (284382, 68342), (284413, 828198), (284494, 54),
  (284522, 54), (284523, 360838), (284604, 189542), (284646, 135062), (284656, 1125846),
  (284657, 54), (284683, 19494), (284697, 277918), (284738, 23382), (284765, 54),
  (284818, 1229526), (284859, 164278), (284899, 1472958), (284900, 241974), (284908, 531558),
  (285007, 114966), (285061, 23382), (285143, 54), (285195, 87518), (285223, 2593998),
  (285246, 686), (285250, 54), (285273, 44006), (285304, 54), (285318, 146518),
  (285345, 184534), (285412, 54), (285413, 54), (285438, 33958), (285466, 726678),
  (285495, 97814), (285588, 133702), (285612, 63926), (285629, 54), (285655, 54), (285710, 54),
  (285736, 2646), (285763, 14094), (285790, 22734), (285791, 54), (285810, 23678),
  (285818, 10401318), (285871, 51894), (285917, 417654), (285952, 54), (285963, 43726),
  (285980, 6534), (286095, 20326), (286195, 4806), (286196, 10638), (286221, 310462),
  (286230, 180118), (286232, 988326), (286249, 4374), (286276, 76734), (286357, 7664814),
  (286384, 54), (286434, 206134), (286439, 54), (286484, 184662), (286518, 256238),
  (286547, 14526), (286593, 304126), (286698, 1980934), (286699, 260046), (286727, 1177326),
  (286755, 44342), (286789, 5523822), (286790, 93582), (286817, 3395358), (286833, 20798),
  (286924, 54), (286951, 54), (286952, 1566), (287006, 54), (287033, 54), (287114, 63774),
  (287127, 272942), (287141, 632286), (287176, 225702), (287194, 54), (287205, 23462),
  (287231, 480582)]

def WL53 : List (ℕ × ℕ) := [
  (287232, 436382), (287244, 20542), (287304, 132398), (287329, 1566), (287334, 405254),
  (287337, 119942), (287376, 41438), (287403, 686), (287411, 13014), (287415, 25582),
  (287418, 348694), (287442, 113422), (287491, 2581038), (287492, 34614), (287519, 6673374),
  (287573, 54), (287574, 57502), (287583, 25934), (287653, 54), (287672, 950526),
  (287679, 32222), (287680, 173286), (287681, 2446254), (287716, 1204614), (287790, 278534),
  (287834, 201078), (287842, 1566), (287853, 47326), (287870, 486), (287897, 54),
  (287923, 702486), (287924, 120798), (287978, 41526), (288051, 34774), (288058, 195102),
  (288085, 54), (288086, 54), (288121, 749646), (288129, 249358), (288140, 54),
  (288167, 54702), (288220, 54), (288247, 6482646), (288248, 189486), (288293, 123462),
  (288300, 163406), (288328, 20142), (288333, 686), (288383, 2646), (288409, 32454),
  (288429, 389726), (288432, 686), (288436, 4203414), (288463, 54), (288489, 1582414),
  (288491, 54), (288517, 3705102), (288526, 1079478), (288555, 83966), (288562, 489222),
  (288615, 297494), (288626, 54), (288706, 54), (288756, 42694), (288896, 5297022),
  (288933, 201694), (289030, 54), (289031, 3258846), (289057, 6431454), (289059, 69742),
  (289067, 1357038), (289085, 486), (289112, 7924446), (289140, 53726), (289184, 879246),
  (289193, 21438), (289220, 5238), (289228, 271638), (289254, 173158), (289274, 54),
  (289301, 1566), (289354, 54), (289365, 386734), (289382, 219078), (289407, 344846),
  (289431, 383062), (289435, 2076246), (289437, 2080982), (289462, 54), (289463, 10666134),
  (289597, 54), (289598, 54), (289602, 32902), (289624, 54), (289625, 31158),
  (289705, 312671934), (289759, 16902), (289787, 54), (289804, 6174), (289809, 6894046),
  (289912, 297342), (289948, 54), (289949, 54), (289983, 183422), (290002, 2160702),
  (290029, 54), (290038, 422262), (290057, 486), (290137, 8888454), (290147, 2451078),
  (290165, 1160622), (290205, 252622), (290235, 25238), (290245, 2646), (290247, 153358),
  (290407, 54), (290408, 54), (290416, 668214), (290417, 972198), (290488, 3282822),
  (290515, 110862), (290547, 2662726), (290596, 54), (290597, 1566), (290731, 258606),
  (290759, 54), (290766, 271702), (290786, 486), (290794, 615078), (290820, 960982),
  (290832, 1376998), (290883, 177614), (290892, 91646), (290920, 54), (290975, 32454),
  (291002, 31158), (291030, 97694), (291055, 54), (291065, 367398), (291093, 116822),
  (291129, 21278), (291136, 54), (291137, 133758), (291138, 248134), (291173, 679446),
  (291213, 212246), (291258, 34838), (291261, 306686), (291272, 486), (291279, 137798),
  (291299, 16902), (291325, 54), (291362, 283806), (291461, 54), (291488, 54),
  (291507, 454262), (291541, 54), (291558, 177638), (291564, 42646), (291621, 2120654),
  (291622, 55134), (291640, 662166), (291650, 1566), (291704, 40878), (291740, 485046),
  (291747, 347374), (291765, 226318), (291811, 54), (291837, 153982), (291866, 50598),
  (291951, 230446), (292046, 237294), (292073, 219798), (292108, 54), (292137, 161726),
  (292182, 73894), (292189, 59238), (292244, 696438), (292253, 9376542), (292272, 2484614),
  (292297, 46278), (292299, 103654), (292352, 8512182), (292374, 77342), (292389, 72614),
  (292392, 321446), (292432, 3485214), (292433, 1566), (292449, 686), (292514, 581526),
  (292545, 314582), (292594, 54), (292622, 54), (292686, 198734), (292725, 2121614),
  (292755, 22054), (292756, 6534), (292783, 54), (292788, 163406), (292810, 126846),
  (292812, 98734), (292864, 16902), (292928, 1231182), (292936, 410526), (292971, 21718),
  (292983, 159158), (292992, 26998), (292999, 41742), (293004, 876206), (293018, 329526),
  (293027, 54), (293034, 60142), (293049, 246254), (293076, 313438), (293089, 246222),
  (293135, 55566), (293161, 54), (293234, 6174), (293243, 54), (293259, 267934),
  (293277, 291598), (293421, 72902), (293459, 486), (293476, 1092942), (293478, 686),
  (293567, 2600478), (293577, 7623518), (293593, 1566), (293601, 419702), (293610, 294062),
  (293648, 54), (293674, 7496118), (293728, 540486), (293756, 54), (293802, 36758),
  (293809, 54), (293810, 14526), (293901, 81166), (293971, 54702), (293998, 789966),
  (294090, 25294), (294132, 120854), (294134, 54), (294156, 155318), (294215, 4314654),
  (294273, 5369038), (294323, 237438), (294372, 277094), (294376, 1566), (294453, 292846),
  (294476, 298206), (294484, 54), (294495, 21806), (294579, 1619302), (294602, 279486),
  (294603, 437254), (294610, 123462), (294646, 54), (294701, 22086), (294728, 54),
  (294754, 356238), (294756, 190382), (294765, 116398), (294817, 280494), (294863, 54),
  (294889, 1566), (294971, 19494), (295024, 1261062), (295051, 54), (295125, 23462),
  (295128, 116062), (295164, 253846), (295224, 54022), (295240, 486), (295302, 54214),
  (295359, 85406)]

def WL54 : List (ℕ × ℕ) := [
  (295447, 1127502), (295457, 54), (295483, 486), (295510, 2354886), (295524, 196838),
  (295536, 19894), (295538, 54), (295546, 713214), (295591, 54), (295635, 686),
  (295672, 797094), (295680, 80198), (295744, 192006), (295763, 1152126), (295780, 4806),
  (295818, 29558), (295835, 54), (295861, 4888782), (295870, 824022), (295879, 6174),
  (295916, 64422), (295961, 683766), (295983, 44158), (295996, 23382), (296024, 54),
  (296059, 430398), (296077, 54), (296086, 284238), (296105, 14526), (296109, 47198),
  (296158, 54), (296175, 41614), (296222, 3710574), (296239, 338526), (296321, 129654),
  (296343, 121222), (296347, 64854), (296367, 91174), (296428, 530766), (296438, 358686),
  (296456, 1636686), (296483, 54), (296591, 613062), (296644, 54), (296725, 433782),
  (296730, 21958), (296743, 184662), (296753, 54), (296807, 54), (296829, 28654),
  (296910, 227518), (296934, 91726), (296941, 486), (296946, 85334), (296988, 51886),
  (296996, 54), (296997, 95398), (297036, 28654), (297050, 54), (297058, 256374),
  (297104, 23814), (297149, 698238), (297198, 97054), (297212, 54), (297319, 54),
  (297347, 486), (297369, 113342), (297374, 54), (297396, 73774), (297435, 318446),
  (297481, 67446), (297535, 54), (297537, 1114006), (297562, 5238), (297594, 686),
  (297670, 486), (297715, 656118), (297724, 4982526), (297725, 369414), (297732, 203446),
  (297841, 254574), (297858, 96742), (297887, 54), (297940, 282582), (297968, 54),
  (298065, 28102), (298076, 486), (298103, 54), (298129, 54), (298130, 22086),
  (298221, 391478), (298264, 54), (298284, 372838), (298292, 54), (298345, 185382),
  (298362, 68062), (298427, 76734), (298446, 27446), (298453, 54), (298507, 54),
  (298530, 188798), (298569, 173878), (298590, 22894), (298593, 132694), (298615, 3217374),
  (298647, 213646), (298669, 54), (298670, 80622), (298713, 24214), (298776, 94102),
  (298824, 127342), (298831, 54), (298842, 777838), (298858, 54), (298912, 670734),
  (298913, 54), (298968, 49054), (298998, 76238), (299020, 54), (299021, 1633014),
  (299074, 1566), (299082, 101078), (299101, 43038), (299102, 35262), (299165, 978246),
  (299214, 29366), (299217, 26318), (299228, 584838), (299229, 170894), (299245, 1217142),
  (299259, 4430294), (299264, 54), (299280, 21782), (299291, 486), (299318, 54),
  (299353, 664758), (299399, 54), (299403, 37798), (299425, 54), (299426, 20142),
  (299496, 220678), (299506, 2646), (299577, 119302), (299614, 113238), (299652, 686),
  (299669, 54), (299713, 1225566), (299742, 151966), (299749, 54), (299794, 271926),
  (299803, 126414), (299885, 39582), (299966, 54), (299993, 1566), (300020, 486),
  (300046, 1162134), (300074, 54), (300155, 99846), (300195, 40102), (300201, 161822),
  (300209, 68958), (300217, 494766), (300343, 486), (300384, 25814), (300398, 54),
  (300432, 87886), (300452, 54), (300543, 29686), (300559, 124686), (300560, 54),
  (300641, 137646), (300642, 146966), (300721, 54), (300771, 202646), (300780, 1408358),
  (300783, 46622), (300803, 47574), (300838, 218934), (300873, 265046), (300900, 111974),
  (300938, 194022), (301014, 29758), (301100, 203094), (301113, 54134), (301126, 54),
  (301167, 357118), (301181, 54), (301188, 29662), (301288, 54), (301343, 54), (301370, 28566),
  (301407, 294662), (301468, 23958), (301469, 123462), (301506, 27926), (301530, 772966),
  (301532, 106542), (301551, 50342), (301558, 529254), (301596, 69358), (301603, 1107342),
  (301632, 30902), (301667, 203526), (301674, 165806), (301710, 83006), (301749, 29662),
  (301824, 52526), (301848, 73574), (301856, 54), (301863, 37006), (301874, 532782),
  (301936, 1566), (301937, 346734), (301971, 83702), (302010, 3406742), (302017, 53838),
  (302035, 841014), (302044, 486), (302071, 54), (302072, 54), (302178, 220718),
  (302223, 374086), (302233, 54), (302234, 54), (302261, 293814), (302268, 350822),
  (302280, 202966), (302314, 4431942), (302342, 1566), (302396, 236859822), (302422, 54),
  (302450, 1203822), (302484, 32134), (302503, 54), (302512, 558702), (302532, 220046),
  (302539, 184806), (302574, 1855478), (302584, 54), (302604, 327718), (302610, 29686),
  (302675, 361134), (302791, 246222), (302827, 41094), (302862, 97742), (302863, 738918),
  (302936, 2309958), (302962, 54), (302990, 54), (303009, 684806), (303044, 54),
  (303070, 69606), (303071, 54), (303093, 134782), (303102, 114278), (303115, 579654),
  (303144, 295294), (303147, 125206), (303291, 62534), (303339, 384014), (303354, 168998),
  (303367, 54), (303368, 14526), (303422, 4374), (303449, 2779542), (303475, 2646),
  (303476, 54), (303528, 65678), (303529, 20142), (303557, 230742), (303612, 3030806)]

def WL55 : List (ℕ × ℕ) := [
  (303718, 903366), (303772, 1566), (303773, 154494), (303799, 13014), (303867, 66542),
  (303924, 40246), (303961, 63774), (303963, 108734), (304124, 54), (304177, 19494),
  (304179, 33094), (304259, 2646), (304332, 84806), (304340, 54), (304358, 1124262),
  (304366, 54), (304425, 321934), (304458, 287654), (304501, 54), (304529, 4806), (304582, 54),
  (304610, 54), (304635, 62438), (304650, 1117102), (304704, 2662), (304710, 20222),
  (304717, 486), (304745, 54), (304761, 197254), (304764, 49094), (304771, 54),
  (304896, 527534), (304941, 115894), (304960, 486), (304970, 299718), (305068, 1566),
  (305069, 54), (305082, 223334), (305123, 486), (305130, 23726), (305139, 226334),
  (305140, 6174), (305149, 92934), (305150, 887382), (305226, 33958), (305239, 6174),
  (305286, 20606), (305312, 14958), (305328, 48494), (305366, 486), (305433, 143998),
  (305438, 312966), (305446, 93798), (305473, 54), (305500, 54), (305501, 54),
  (305523, 278878), (305555, 5238), (305580, 77806), (305586, 54958), (305635, 1878174),
  (305636, 54), (305655, 28814), (305662, 2804814), (305663, 54), (305682, 235022),
  (305689, 486), (305726, 249822), (305775, 2394278), (305797, 54), (305843, 1126638),
  (305852, 247374), (305905, 12582), (306040, 5238), (306041, 54), (306059, 222246),
  (306202, 54), (306203, 54), (306284, 54), (306336, 23486), (306342, 96766), (306383, 594414),
  (306391, 54), (306392, 54), (306410, 835902), (306417, 188662), (306472, 54),
  (306483, 113782), (306581, 280422), (306608, 54), (306634, 4480326), (306635, 54),
  (306642, 25814), (306670, 821862), (306689, 54), (306735, 49694), (306756, 306134),
  (306769, 54), (306822, 62774), (306824, 486), (306855, 5055134), (306878, 12582),
  (306914, 1053198), (306954, 519302), (306958, 54), (307011, 1090574), (307020, 1458526),
  (307039, 54), (307040, 941166), (307085, 503046), (307174, 83646), (307263, 52814),
  (307341, 23974), (307363, 34614), (307503, 34702), (307526, 54), (307629, 856718),
  (307719, 65222), (307728, 307126), (307742, 54), (307769, 12582), (307776, 41918),
  (307823, 2976966), (307930, 54), (307931, 54), (307985, 54), (308012, 21438),
  (308092, 4188294), (308111, 271926), (308133, 75742), (308146, 54), (308173, 54),
  (308174, 5238), (308227, 199508238), (308254, 54), (308308, 54), (308328, 13718),
  (308335, 572886), (308336, 14526), (308390, 54), (308394, 44078), (308469, 35918),
  (308511, 268078), (308533, 469782), (308551, 54), (308579, 44334), (308614, 992286),
  (308713, 54), (308714, 190782), (308740, 1918998), (308821, 54), (308856, 162038),
  (308875, 3657582), (308902, 54), (308903, 54), (308916, 49934), (308922, 34246),
  (309000, 47438), (309011, 23814), (309057, 112078), (309065, 54), (309118, 54),
  (309120, 46406), (309199, 620838), (309204, 23942), (309226, 54), (309227, 54),
  (309281, 310014), (309381, 175502), (309393, 109126), (309447, 1665238), (309469, 1202958),
  (309470, 54), (309501, 1041838), (309550, 1727838), (309560, 672534), (309631, 150606),
  (309636, 72686), (309686, 54), (309713, 979182), (309721, 236718), (309722, 995958),
  (309766, 490158), (309792, 27518), (309793, 18846), (309798, 30278), (309955, 107838),
  (310009, 54), (310028, 23958), (310032, 29102), (310071, 221006), (310089, 1611806),
  (310091, 54), (310128, 47942), (310135, 677934), (310161, 48214), (310176, 22342),
  (310245, 106558), (310253, 224262), (310280, 54), (310311, 29462), (310360, 243702),
  (310414, 10638), (310441, 54), (310442, 45414), (310449, 222694), (310469, 486),
  (310473, 173846), (310497, 86854), (310515, 23854), (310533, 76606), (310549, 14094),
  (310577, 54), (310658, 54), (310716, 196094), (310738, 54), (310773, 130654),
  (310792, 2683206), (310830, 320998), (310878, 177638), (310920, 187934), (310927, 47358),
  (310955, 14094), (310956, 26374), (310959, 55646), (310971, 33614), (310982, 54),
  (311070, 686), (311089, 54), (311108, 438678), (311109, 1202398), (311143, 97254),
  (311144, 359694), (311234, 207342), (311278, 47142), (311386, 40878), (311388, 45742),
  (311395, 230382), (311413, 178429662), (311493, 67006), (311494, 54), (311495, 54),
  (311548, 2085966), (311556, 31294), (311576, 54), (311592, 200918), (311607, 47438),
  (311611, 483102), (311661, 37006), (311675, 498438), (311684, 136566), (311737, 54),
  (311738, 139374)]

def WL56 : List (ℕ × ℕ) := [
  (311877, 31582), (311954, 664254), (312000, 686), (312048, 90382), (312075, 182366),
  (312115, 2958174), (312117, 22894), (312143, 40878), (312170, 4374), (312197, 2646),
  (312207, 141166), (312278, 54), (312282, 107974), (312304, 5854734), (312312, 55054),
  (312342, 105614), (312359, 484326), (312390, 105998), (312440, 54), (312458, 866934),
  (312466, 54), (312467, 54), (312493, 4374), (312520, 650214), (312521, 1566),
  (312592, 562878), (312601, 1350486), (312619, 733662), (312628, 4806), (312629, 54),
  (312639, 35942), (312642, 139718), (312654, 67198), (312664, 637614), (312675, 780158),
  (312683, 874422), (312690, 236918), (312790, 54), (312818, 1867374), (312885, 210046),
  (312891, 49102), (312979, 620622), (312997, 230238), (313006, 54), (313014, 602678),
  (313033, 54), (313101, 763222), (313168, 1147878), (313195, 54), (313214, 634518),
  (313272, 182278), (313276, 5238), (313305, 243118), (313308, 300302), (313357, 611766),
  (313412, 5238), (313465, 486), (313467, 66574), (313503, 47942), (313509, 2080262),
  (313519, 2646), (313520, 2646), (313539, 191822), (313584, 60142), (313602, 231926),
  (313682, 54), (313731, 37342), (313830, 103438), (313844, 54), (313978, 2558574),
  (313979, 54), (314006, 15174), (314069, 367974), (314070, 143614), (314141, 4806),
  (314157, 135142), (314159, 866358), (314167, 993654), (314194, 486), (314221, 54),
  (314223, 91726), (314286, 38422), (314301, 145118), (314303, 2045358), (314330, 18846),
  (314337, 154694), (314383, 51894), (314384, 6534), (314401, 6174), (314466, 187366),
  (314491, 54), (314500, 6174), (314545, 39582), (314622, 22766), (314707, 54), (314708, 54),
  (314778, 2662), (314793, 2002238), (314816, 4514238), (314843, 155207502), (314869, 14958),
  (314928, 1352038), (314946, 66446), (314951, 54), (315058, 54), (315112, 16902),
  (315113, 54), (315139, 500958), (315194, 60966), (315274, 54), (315329, 2825118),
  (315356, 265086), (315428, 586566), (315436, 46278), (315464, 54), (315518, 54702),
  (315580, 236718), (315609, 132214), (315617, 951894), (315652, 486), (315679, 670086),
  (315706, 1162134), (315707, 185382), (315762, 181054), (315841, 54), (315842, 54),
  (315859, 320238), (315868, 2803518), (315895, 47142), (315903, 30766), (315931, 946206),
  (315950, 1323918), (316049, 205182), (316058, 486), (316062, 277798), (316084, 112374),
  (316085, 54), (316112, 2590974), (316116, 686), (316165, 2646), (316176, 64502),
  (316202, 610614), (316215, 604366), (316247, 54), (316273, 54), (316301, 4566942),
  (316328, 54), (316335, 279142), (316381, 486), (316400, 343566), (316407, 1027006),
  (316443, 226126), (316471, 564822), (316490, 57726), (316580, 266958), (316602, 23734),
  (316647, 136798), (316651, 54), (316652, 16902), (316696, 388566), (316723, 188262),
  (316759, 3700134), (316779, 34582), (316787, 198774), (316797, 189206), (316814, 54),
  (316905, 285598), (316913, 791766), (316974, 135358), (316976, 54), (316993, 213534),
  (316998, 2112782), (317031, 32854), (317067, 56102), (317133, 252646), (317219, 302238),
  (317238, 49886), (317245, 54), (317246, 54), (317247, 172222), (317331, 3941446),
  (317361, 24982), (317380, 21438), (317381, 54), (317408, 54), (317487, 78902),
  (317489, 76734), (317499, 35806), (317507, 466758), (317542, 47574), (317556, 113902),
  (317569, 54), (317577, 21334), (317587, 6174), (317623, 644382), (317651, 6534),
  (317688, 125446), (317696, 466902), (317749, 222822), (317844, 54254), (317862, 36758),
  (317974, 54), (318029, 5238), (318030, 1851022), (318057, 1828238), (318082, 486),
  (318109, 54), (318136, 76086), (318141, 101846), (318271, 112806), (318272, 76734),
  (318285, 20854), (318352, 54), (318415, 257454), (318460, 54), (318480, 93502),
  (318492, 68294), (318585, 226262), (318596, 54), (318642, 72526), (318677, 251478),
  (318687, 53894), (318704, 54), (318768, 26822), (318771, 2662), (318789, 51206),
  (318838, 1210086), (318865, 1272078), (318920, 4806), (318974, 486), (319109, 54),
  (319207, 489222), (319254, 88526), (319270, 54), (319271, 15174), (319284, 161302),
  (319302, 686), (319324, 54), (319325, 2636118), (319370, 341046), (319397, 250326),
  (319404, 196094), (319410, 30182), (319479, 220502), (319513, 54), (319514, 304614),
  (319590, 38326), (319604, 621198), (319737, 95054), (319801, 467118), (319810, 4806),
  (319837, 4806), (319857, 197774), (319863, 94558), (319865, 1764342), (319891, 22734),
  (319919, 1855926), (319990, 242982), (319991, 448326), (319999, 54)]

def WL57 : List (ℕ × ℕ) := [
  (320026, 486), (320040, 66446), (320052, 131902), (320134, 1145718), (320151, 44134),
  (320216, 22086), (320297, 54), (320306, 801126), (320341, 773622), (320458, 54),
  (320466, 54086), (320486, 54), (320502, 80254), (320539, 54), (320567, 23382),
  (320647, 407646), (320675, 486), (320691, 29782), (320703, 25934), (320728, 45414),
  (320755, 486), (320774, 210582), (320818, 202302), (320823, 53566), (320864, 403974),
  (320972, 630774), (320991, 82702), (320998, 2720142), (320999, 1916622), (321054, 38278),
  (321062, 196038), (321078, 273622), (321126, 143774), (321133, 5238), (321159, 44566),
  (321161, 486), (321187, 54), (321188, 54), (321360, 395822), (321377, 54), (321404, 14094),
  (321431, 54), (321432, 30934), (321456, 138878), (321458, 2646), (321484, 3256686),
  (321538, 54), (321540, 901958), (321579, 193918), (321588, 153662), (321592, 259254),
  (321629, 377262), (321700, 54), (321701, 54), (321727, 486), (321755, 54), (321782, 54),
  (321826, 306486), (321846, 58622), (321890, 486), (321917, 189486), (321936, 32894),
  (321943, 54), (321997, 2646), (321998, 16902), (322007, 23958), (322078, 54), (322105, 54),
  (322134, 43982), (322187, 2206494), (322268, 70254), (322287, 197878), (322320, 54542),
  (322321, 54), (322385, 219006), (322492, 369918), (322617, 90278), (322646, 287982),
  (322719, 145006), (322726, 54), (322754, 54), (322834, 54), (322862, 130734),
  (322889, 469422), (322950, 33038), (323016, 121886), (323058, 47198), (323073, 1991798),
  (323077, 1566), (323078, 54), (323142, 33134), (323175, 75182), (323176, 368694),
  (323185, 169614), (323212, 54), (323240, 66798), (323268, 45718), (323295, 32278),
  (323320, 637686), (323321, 298134), (323401, 224478), (323455, 54), (323456, 14958),
  (323482, 54), (323564, 2807406), (323617, 54), (323618, 707022), (323636, 251982),
  (323645, 124038), (323662, 6174), (323681, 532998), (323761, 6174), (323779, 341118),
  (323780, 54), (323806, 54), (323860, 1566), (323968, 54), (324005, 179046), (324049, 54),
  (324050, 54), (324077, 486), (324095, 23958), (324103, 2646), (324104, 89766414),
  (324168, 232894), (324212, 19494), (324239, 1866078), (324310, 684846), (324400, 486),
  (324428, 54), (324617, 54), (324618, 134894), (324626, 229734), (324813, 70054),
  (324885, 21478), (324912, 42974), (324914, 54), (324941, 54), (324994, 54), (324995, 13014),
  (325004, 681246), (325023, 76654), (325103, 16902), (325156, 54), (325157, 14526),
  (325183, 54), (325184, 6534), (325292, 4374), (325317, 157286), (325323, 74726),
  (325337, 232398), (325345, 54), (325346, 54), (325372, 486), (325425, 202414),
  (325426, 20641446), (325476, 247646), (325480, 21438), (325508, 54), (325521, 30398),
  (325535, 2066958), (325548, 21718), (325562, 1128438), (325642, 54), (325660, 457902),
  (325669, 206334), (325683, 148726), (325716, 795934), (325724, 54), (325764, 200918),
  (325779, 49094), (325788, 25582), (325814, 338454), (325850, 645534), (325878, 114542),
  (325885, 35694), (325886, 5238), (326013, 67006), (326025, 126398), (326037, 170398),
  (326290, 10422), (326390, 232542), (326398, 54), (326424, 22886), (326436, 84142),
  (326439, 54478), (326452, 259254), (326466, 26998), (326480, 54), (326488, 184662),
  (326505, 686), (326507, 47142), (326534, 580662), (326569, 469494), (326615, 45414),
  (326634, 32374), (326642, 12582), (326695, 54), (326723, 173718), (326727, 93374),
  (326766, 58846), (326776, 31158), (326804, 54), (326830, 486), (326835, 147454),
  (326919, 209086), (326965, 563382), (326993, 486), (327019, 4806), (327046, 4806),
  (327047, 54), (327069, 184222), (327092, 6174), (327150, 145454), (327191, 6174),
  (327209, 54), (327270, 155486), (327289, 2646), (327343, 54), (327370, 54), (327371, 360342),
  (327424, 1888974), (327425, 205038), (327435, 184534), (327451, 1823526), (327486, 55598),
  (327489, 29278), (327533, 2646), (327534, 33614), (327542, 183798), (327559, 486),
  (327586, 235278), (327587, 114966), (327668, 1379646), (327696, 27926), (327748, 54),
  (327776, 54), (327829, 54), (327830, 22086), (327894, 38854), (327910, 54), (327937, 389502),
  (328074, 584582), (328083, 171982), (328092, 25238), (328180, 756486)]

def WL58 : List (ℕ × ℕ) := [
  (328270, 326286), (328305, 36382), (328315, 54), (328347, 96742), (328397, 54),
  (328424, 106542), (328469, 213606), (328476, 78382), (328477, 746766), (328504, 54),
  (328524, 140878), (328559, 4806), (328666, 54), (328698, 22766), (328711, 458478),
  (328746, 130246), (328747, 133542), (328774, 583686), (328818, 142942), (328905, 672182),
  (328909, 54), (328910, 27486), (328964, 1566), (329035, 342558), (329044, 239814),
  (329097, 97558), (329126, 5238), (329202, 90526), (329279, 396054), (329288, 1745334),
  (329369, 54), (329493, 686), (329611, 151902), (329638, 54), (329692, 54), (329720, 10638),
  (329800, 54), (329841, 38102), (329853, 22478), (329854, 70254), (329882, 102006),
  (329909, 486), (329919, 20798), (329926, 198486), (329967, 47774), (330080, 324774),
  (330179, 129654), (330192, 79022), (330195, 127214), (330206, 384534), (330225, 25342),
  (330278, 179046), (330287, 54), (330318, 23462), (330342, 64054), (330421, 40878),
  (330471, 38062), (330522, 686), (330548, 263502), (330584, 59238), (330610, 790182),
  (330611, 54), (330621, 686), (330633, 64958), (330699, 42382), (330723, 50294), (330745, 54),
  (330756, 21782), (330934, 1112022), (330961, 58806), (330988, 54), (330989, 54),
  (331070, 54), (331078, 210582), (331150, 54), (331151, 54), (331177, 1566), (331231, 54),
  (331259, 22086), (331367, 486), (331393, 54), (331420, 10422), (331473, 59198),
  (331501, 10422), (331551, 66542), (331582, 469422), (331602, 90494), (331637, 57726),
  (331682, 269046), (331683, 34862), (331718, 6534), (331749, 54598), (331798, 881982),
  (331826, 54), (331870, 284814), (331878, 57406), (331933, 486), (332042, 616518),
  (332122, 54), (332150, 54), (332274, 93014), (332285, 54), (332311, 54), (332339, 486),
  (332366, 1566), (332393, 280206), (332463, 103438), (332473, 797094), (332474, 54),
  (332520, 40574), (332527, 91422), (332541, 81182), (332555, 54), (332635, 54),
  (332655, 2662), (332662, 321246), (332690, 54), (332716, 54), (332717, 69606),
  (332718, 28606), (332751, 52454), (332771, 10422), (332871, 28814), (332932, 54),
  (333094, 50598), (333121, 54), (333122, 66798), (333131, 269046), (333174, 57446),
  (333257, 432918), (333365, 20324574), (333391, 486), (333499, 54), (333527, 54),
  (333670, 233406), (333688, 54), (333768, 36878), (333850, 54), (333904, 2646), (333905, 54),
  (333948, 75974), (333999, 77566), (334003, 238662), (334012, 54), (334013, 54),
  (334040, 39366), (334066, 54), (334067, 10638), (334147, 54), (334148, 2646),
  (334174, 57294), (334175, 54), (334209, 84358), (334210, 221814), (334255, 4806),
  (334256, 54), (334308, 79262), (334389, 62102), (334390, 368766), (334552, 313902),
  (334553, 54), (334579, 54), (334638, 686), (334671, 33806), (334707, 38846), (334714, 54),
  (334741, 41742), (334742, 54), (334777, 191358), (334796, 54), (334823, 54), (334857, 32126),
  (334903, 54), (334984, 54), (335154, 27254), (335169, 54814), (335201, 54), (335281, 54),
  (335309, 54), (335335, 486), (335363, 54), (335487, 38174), (335551, 54), (335552, 54),
  (335578, 486), (335606, 54), (335714, 54), (335741, 43254), (335767, 54), (335875, 1566),
  (335929, 54), (335930, 54), (335956, 54)]


set_option maxHeartbeats 0 in
/-- The kernel scan, block by block (each block a separate kernel check); a block holds at most
10000 enumeration steps, since the kernel's memory for one check grows with them. -/
theorem no_sol : ∀ x y z, ¬ IsSol 335979 x y z := by
  have c0 : (wlOK 335979 0 256 WL0 && blockOK QRM 335979 0
      (wBlock 256 0 QL) (wlBits 0 WL0) 256) = true := by
    decide +kernel
  have c1 : (wlOK 335979 256 512 WL1 && blockOK QRM 335979 256
      (wBlock 512 256 QL) (wlBits 256 WL1) 512) = true := by
    decide +kernel
  have c2 : (wlOK 335979 768 768 WL2 && blockOK QRM 335979 768
      (wBlock 768 768 QL) (wlBits 768 WL2) 768) = true := by
    decide +kernel
  have c3 : (wlOK 335979 1536 1024 WL3 && blockOK QRM 335979 1536
      (wBlock 1024 1536 QL) (wlBits 1536 WL3) 1024) = true := by
    decide +kernel
  have c4 : (wlOK 335979 2560 1280 WL4 && blockOK QRM 335979 2560
      (wBlock 1280 2560 QL) (wlBits 2560 WL4) 1280) = true := by
    decide +kernel
  have c5 : (wlOK 335979 3840 1280 WL5 && blockOK QRM 335979 3840
      (wBlock 1280 3840 QL) (wlBits 3840 WL5) 1280) = true := by
    decide +kernel
  have c6 : (wlOK 335979 5120 1536 WL6 && blockOK QRM 335979 5120
      (wBlock 1536 5120 QL) (wlBits 5120 WL6) 1536) = true := by
    decide +kernel
  have c7 : (wlOK 335979 6656 1792 WL7 && blockOK QRM 335979 6656
      (wBlock 1792 6656 QL) (wlBits 6656 WL7) 1792) = true := by
    decide +kernel
  have c8 : (wlOK 335979 8448 2048 WL8 && blockOK QRM 335979 8448
      (wBlock 2048 8448 QL) (wlBits 8448 WL8) 2048) = true := by
    decide +kernel
  have c9 : (wlOK 335979 10496 2304 WL9 && blockOK QRM 335979 10496
      (wBlock 2304 10496 QL) (wlBits 10496 WL9) 2304) = true := by
    decide +kernel
  have c10 : (wlOK 335979 12800 2304 WL10 && blockOK QRM 335979 12800
      (wBlock 2304 12800 QL) (wlBits 12800 WL10) 2304) = true := by
    decide +kernel
  have c11 : (wlOK 335979 15104 2560 WL11 && blockOK QRM 335979 15104
      (wBlock 2560 15104 QL) (wlBits 15104 WL11) 2560) = true := by
    decide +kernel
  have c12 : (wlOK 335979 17664 2816 WL12 && blockOK QRM 335979 17664
      (wBlock 2816 17664 QL) (wlBits 17664 WL12) 2816) = true := by
    decide +kernel
  have c13 : (wlOK 335979 20480 3072 WL13 && blockOK QRM 335979 20480
      (wBlock 3072 20480 QL) (wlBits 20480 WL13) 3072) = true := by
    decide +kernel
  have c14 : (wlOK 335979 23552 3328 WL14 && blockOK QRM 335979 23552
      (wBlock 3328 23552 QL) (wlBits 23552 WL14) 3328) = true := by
    decide +kernel
  have c15 : (wlOK 335979 26880 3328 WL15 && blockOK QRM 335979 26880
      (wBlock 3328 26880 QL) (wlBits 26880 WL15) 3328) = true := by
    decide +kernel
  have c16 : (wlOK 335979 30208 3584 WL16 && blockOK QRM 335979 30208
      (wBlock 3584 30208 QL) (wlBits 30208 WL16) 3584) = true := by
    decide +kernel
  have c17 : (wlOK 335979 33792 3584 WL17 && blockOK QRM 335979 33792
      (wBlock 3584 33792 QL) (wlBits 33792 WL17) 3584) = true := by
    decide +kernel
  have c18 : (wlOK 335979 37376 4352 WL18 && blockOK QRM 335979 37376
      (wBlock 4352 37376 QL) (wlBits 37376 WL18) 4352) = true := by
    decide +kernel
  have c19 : (wlOK 335979 41728 4096 WL19 && blockOK QRM 335979 41728
      (wBlock 4096 41728 QL) (wlBits 41728 WL19) 4096) = true := by
    decide +kernel
  have c20 : (wlOK 335979 45824 4608 WL20 && blockOK QRM 335979 45824
      (wBlock 4608 45824 QL) (wlBits 45824 WL20) 4608) = true := by
    decide +kernel
  have c21 : (wlOK 335979 50432 4352 WL21 && blockOK QRM 335979 50432
      (wBlock 4352 50432 QL) (wlBits 50432 WL21) 4352) = true := by
    decide +kernel
  have c22 : (wlOK 335979 54784 4864 WL22 && blockOK QRM 335979 54784
      (wBlock 4864 54784 QL) (wlBits 54784 WL22) 4864) = true := by
    decide +kernel
  have c23 : (wlOK 335979 59648 4864 WL23 && blockOK QRM 335979 59648
      (wBlock 4864 59648 QL) (wlBits 59648 WL23) 4864) = true := by
    decide +kernel
  have c24 : (wlOK 335979 64512 5376 WL24 && blockOK QRM 335979 64512
      (wBlock 5376 64512 QL) (wlBits 64512 WL24) 5376) = true := by
    decide +kernel
  have c25 : (wlOK 335979 69888 5888 WL25 && blockOK QRM 335979 69888
      (wBlock 5888 69888 QL) (wlBits 69888 WL25) 5888) = true := by
    decide +kernel
  have c26 : (wlOK 335979 75776 5888 WL26 && blockOK QRM 335979 75776
      (wBlock 5888 75776 QL) (wlBits 75776 WL26) 5888) = true := by
    decide +kernel
  have c27 : (wlOK 335979 81664 6400 WL27 && blockOK QRM 335979 81664
      (wBlock 6400 81664 QL) (wlBits 81664 WL27) 6400) = true := by
    decide +kernel
  have c28 : (wlOK 335979 88064 6656 WL28 && blockOK QRM 335979 88064
      (wBlock 6656 88064 QL) (wlBits 88064 WL28) 6656) = true := by
    decide +kernel
  have c29 : (wlOK 335979 94720 6912 WL29 && blockOK QRM 335979 94720
      (wBlock 6912 94720 QL) (wlBits 94720 WL29) 6912) = true := by
    decide +kernel
  have c30 : (wlOK 335979 101632 6912 WL30 && blockOK QRM 335979 101632
      (wBlock 6912 101632 QL) (wlBits 101632 WL30) 6912) = true := by
    decide +kernel
  have c31 : (wlOK 335979 108544 7168 WL31 && blockOK QRM 335979 108544
      (wBlock 7168 108544 QL) (wlBits 108544 WL31) 7168) = true := by
    decide +kernel
  have c32 : (wlOK 335979 115712 7680 WL32 && blockOK QRM 335979 115712
      (wBlock 7680 115712 QL) (wlBits 115712 WL32) 7680) = true := by
    decide +kernel
  have c33 : (wlOK 335979 123392 8192 WL33 && blockOK QRM 335979 123392
      (wBlock 8192 123392 QL) (wlBits 123392 WL33) 8192) = true := by
    decide +kernel
  have c34 : (wlOK 335979 131584 8192 WL34 && blockOK QRM 335979 131584
      (wBlock 8192 131584 QL) (wlBits 131584 WL34) 8192) = true := by
    decide +kernel
  have c35 : (wlOK 335979 139776 8192 WL35 && blockOK QRM 335979 139776
      (wBlock 8192 139776 QL) (wlBits 139776 WL35) 8192) = true := by
    decide +kernel
  have c36 : (wlOK 335979 147968 8192 WL36 && blockOK QRM 335979 147968
      (wBlock 8192 147968 QL) (wlBits 147968 WL36) 8192) = true := by
    decide +kernel
  have c37 : (wlOK 335979 156160 8192 WL37 && blockOK QRM 335979 156160
      (wBlock 8192 156160 QL) (wlBits 156160 WL37) 8192) = true := by
    decide +kernel
  have c38 : (wlOK 335979 164352 8192 WL38 && blockOK QRM 335979 164352
      (wBlock 8192 164352 QL) (wlBits 164352 WL38) 8192) = true := by
    decide +kernel
  have c39 : (wlOK 335979 172544 8192 WL39 && blockOK QRM 335979 172544
      (wBlock 8192 172544 QL) (wlBits 172544 WL39) 8192) = true := by
    decide +kernel
  have c40 : (wlOK 335979 180736 8192 WL40 && blockOK QRM 335979 180736
      (wBlock 8192 180736 QL) (wlBits 180736 WL40) 8192) = true := by
    decide +kernel
  have c41 : (wlOK 335979 188928 8192 WL41 && blockOK QRM 335979 188928
      (wBlock 8192 188928 QL) (wlBits 188928 WL41) 8192) = true := by
    decide +kernel
  have c42 : (wlOK 335979 197120 8192 WL42 && blockOK QRM 335979 197120
      (wBlock 8192 197120 QL) (wlBits 197120 WL42) 8192) = true := by
    decide +kernel
  have c43 : (wlOK 335979 205312 8192 WL43 && blockOK QRM 335979 205312
      (wBlock 8192 205312 QL) (wlBits 205312 WL43) 8192) = true := by
    decide +kernel
  have c44 : (wlOK 335979 213504 8192 WL44 && blockOK QRM 335979 213504
      (wBlock 8192 213504 QL) (wlBits 213504 WL44) 8192) = true := by
    decide +kernel
  have c45 : (wlOK 335979 221696 8192 WL45 && blockOK QRM 335979 221696
      (wBlock 8192 221696 QL) (wlBits 221696 WL45) 8192) = true := by
    decide +kernel
  have c46 : (wlOK 335979 229888 8192 WL46 && blockOK QRM 335979 229888
      (wBlock 8192 229888 QL) (wlBits 229888 WL46) 8192) = true := by
    decide +kernel
  have c47 : (wlOK 335979 238080 8192 WL47 && blockOK QRM 335979 238080
      (wBlock 8192 238080 QL) (wlBits 238080 WL47) 8192) = true := by
    decide +kernel
  have c48 : (wlOK 335979 246272 8192 WL48 && blockOK QRM 335979 246272
      (wBlock 8192 246272 QL) (wlBits 246272 WL48) 8192) = true := by
    decide +kernel
  have c49 : (wlOK 335979 254464 8192 WL49 && blockOK QRM 335979 254464
      (wBlock 8192 254464 QL) (wlBits 254464 WL49) 8192) = true := by
    decide +kernel
  have c50 : (wlOK 335979 262656 8192 WL50 && blockOK QRM 335979 262656
      (wBlock 8192 262656 QL) (wlBits 262656 WL50) 8192) = true := by
    decide +kernel
  have c51 : (wlOK 335979 270848 8192 WL51 && blockOK QRM 335979 270848
      (wBlock 8192 270848 QL) (wlBits 270848 WL51) 8192) = true := by
    decide +kernel
  have c52 : (wlOK 335979 279040 8192 WL52 && blockOK QRM 335979 279040
      (wBlock 8192 279040 QL) (wlBits 279040 WL52) 8192) = true := by
    decide +kernel
  have c53 : (wlOK 335979 287232 8192 WL53 && blockOK QRM 335979 287232
      (wBlock 8192 287232 QL) (wlBits 287232 WL53) 8192) = true := by
    decide +kernel
  have c54 : (wlOK 335979 295424 8192 WL54 && blockOK QRM 335979 295424
      (wBlock 8192 295424 QL) (wlBits 295424 WL54) 8192) = true := by
    decide +kernel
  have c55 : (wlOK 335979 303616 8192 WL55 && blockOK QRM 335979 303616
      (wBlock 8192 303616 QL) (wlBits 303616 WL55) 8192) = true := by
    decide +kernel
  have c56 : (wlOK 335979 311808 8192 WL56 && blockOK QRM 335979 311808
      (wBlock 8192 311808 QL) (wlBits 311808 WL56) 8192) = true := by
    decide +kernel
  have c57 : (wlOK 335979 320000 8192 WL57 && blockOK QRM 335979 320000
      (wBlock 8192 320000 QL) (wlBits 320000 WL57) 8192) = true := by
    decide +kernel
  have c58 : (wlOK 335979 328192 7936 WL58 && blockOK QRM 335979 328192
      (wBlock 7936 328192 QL) (wlBits 328192 WL58) 7936) = true := by
    decide +kernel
  have r0 := range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c0)
  have r1 := range_join r0 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c1))
  have r2 := range_join r1 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c2))
  have r3 := range_join r2 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c3))
  have r4 := range_join r3 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c4))
  have r5 := range_join r4 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c5))
  have r6 := range_join r5 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c6))
  have r7 := range_join r6 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c7))
  have r8 := range_join r7 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c8))
  have r9 := range_join r8 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c9))
  have r10 := range_join r9 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c10))
  have r11 := range_join r10 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c11))
  have r12 := range_join r11 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c12))
  have r13 := range_join r12 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c13))
  have r14 := range_join r13 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c14))
  have r15 := range_join r14 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c15))
  have r16 := range_join r15 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c16))
  have r17 := range_join r16 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c17))
  have r18 := range_join r17 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c18))
  have r19 := range_join r18 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c19))
  have r20 := range_join r19 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c20))
  have r21 := range_join r20 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c21))
  have r22 := range_join r21 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c22))
  have r23 := range_join r22 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c23))
  have r24 := range_join r23 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c24))
  have r25 := range_join r24 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c25))
  have r26 := range_join r25 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c26))
  have r27 := range_join r26 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c27))
  have r28 := range_join r27 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c28))
  have r29 := range_join r28 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c29))
  have r30 := range_join r29 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c30))
  have r31 := range_join r30 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c31))
  have r32 := range_join r31 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c32))
  have r33 := range_join r32 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c33))
  have r34 := range_join r33 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c34))
  have r35 := range_join r34 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c35))
  have r36 := range_join r35 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c36))
  have r37 := range_join r36 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c37))
  have r38 := range_join r37 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c38))
  have r39 := range_join r38 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c39))
  have r40 := range_join r39 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c40))
  have r41 := range_join r40 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c41))
  have r42 := range_join r41 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c42))
  have r43 := range_join r42 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c43))
  have r44 := range_join r43 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c44))
  have r45 := range_join r44 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c45))
  have r46 := range_join r45 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c46))
  have r47 := range_join r46 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c47))
  have r48 := range_join r47 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c48))
  have r49 := range_join r48 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c49))
  have r50 := range_join r49 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c50))
  have r51 := range_join r50 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c51))
  have r52 := range_join r51 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c52))
  have r53 := range_join r52 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c53))
  have r54 := range_join r53 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c54))
  have r55 := range_join r54 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c55))
  have r56 := range_join r55 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c56))
  have r57 := range_join r56 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c57))
  have r58 := range_join r57 (range_of_block (blockOK_spec QRM_spec QL_ok (by norm_num) c58))
  exact no_sol_of_range (by norm_num) r58

theorem a_335979 : a 335979 = 0 := a_eq_zero_of no_sol

/-- Sun's conjecture `a n > 0` for all `n > 4` is false. -/
theorem disproof : ¬ ∀ n : ℕ, 4 < n → 0 < a n := by
  intro h
  have := h 335979 (by norm_num)
  rw [a_335979] at this
  exact lt_irrefl 0 this

/-! ## Controls: the definition reproduces listed terms -/

/-- For small `n`, `a n` is a count over the pairs `(x, y)`, with `z = n - x - y`. -/
theorem a_eq_card_pairs {QRM : ℕ} (hQ : ∀ k, k < 45045 → Nat.testBit QRM (k * k % 45045) = true)
    (n : ℕ) :
    a n = ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p : ℕ × ℕ => p.1 + p.2 < n ∧
      sqB QRM (8 * (p.1 * p.2) + 1) = true ∧ sqB QRM (8 * (p.1 * (n - p.1 - p.2)) + 1) = true ∧
      primeB (6 * p.2 - 1) = true ∧ primeB (6 * (n - p.1 - p.2) + 1) = true)).card := by
  set S := (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p : ℕ × ℕ => p.1 + p.2 < n ∧
      sqB QRM (8 * (p.1 * p.2) + 1) = true ∧ sqB QRM (8 * (p.1 * (n - p.1 - p.2)) + 1) = true ∧
      primeB (6 * p.2 - 1) = true ∧ primeB (6 * (n - p.1 - p.2) + 1) = true) with hS
  have himg : {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧
      IsTriangular (t.1 * t.2.1) ∧ IsTriangular (t.1 * t.2.2) ∧
      (6 * t.2.1 - 1).Prime ∧ (6 * t.2.2 + 1).Prime} =
      ↑(S.image (fun p : ℕ × ℕ => (p.1, p.2, n - p.1 - p.2))) := by
    ext ⟨x, y, z⟩
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, hS,
      Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨hx, hy, hz, hs, ht1, ht2, hp1, hp2⟩
      have hz' : n - x - y = z := by omega
      refine ⟨x, y, ⟨⟨⟨hx, by omega⟩, ⟨hy, by omega⟩⟩, by omega,
        (sqB_iff hQ _).mpr ((isTriangular_iff _).mp ht1), ?_, (primeB_iff _).mpr hp1, ?_⟩,
        rfl, rfl, hz'⟩
      · rw [hz']; exact (sqB_iff hQ _).mpr ((isTriangular_iff _).mp ht2)
      · rw [hz']; exact (primeB_iff _).mpr hp2
    · rintro ⟨x', y', ⟨⟨⟨hx1, -⟩, ⟨hy1, -⟩⟩, hlt, hs1, hs2, hp1, hp2⟩, rfl, rfl, rfl⟩
      exact ⟨hx1, hy1, by omega, by omega, (isTriangular_iff _).mpr ((sqB_iff hQ _).mp hs1),
        (isTriangular_iff _).mpr ((sqB_iff hQ _).mp hs2), (primeB_iff _).mp hp1,
        (primeB_iff _).mp hp2⟩
  rw [a, himg, Set.ncard_coe_finset, Finset.card_image_of_injective]
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2.1

set_option maxHeartbeats 0 in
theorem a_5 : a 5 = 3 := by rw [a_eq_card_pairs QRM_spec]; decide +kernel

set_option maxHeartbeats 0 in
theorem a_6 : a 6 = 2 := by rw [a_eq_card_pairs QRM_spec]; decide +kernel

set_option maxHeartbeats 0 in
theorem a_77 : a 77 = 1 := by rw [a_eq_card_pairs QRM_spec]; decide +kernel

set_option maxHeartbeats 0 in
theorem a_90 : a 90 = 1 := by rw [a_eq_card_pairs QRM_spec]; decide +kernel

/-- All results in one statement, so that one axiom report covers them. -/
theorem summary : a 335979 = 0 ∧ (¬ ∀ n : ℕ, 4 < n → 0 < a n) ∧ a 5 = 3 ∧ a 6 = 2 ∧ a 77 = 1 ∧
    a 90 = 1 :=
  ⟨a_335979, disproof, a_5, a_6, a_77, a_90⟩

end OMA.S_oeis_a227877

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a227877.main) :=
  OMA.S_oeis_a227877.disproof
