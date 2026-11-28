import OMAStatements.S_oeis_a397683

/-!
# Consecutive residues of equal order

For primes in the two remaining residue classes, the proof certifies the
finite range below 260,000 and proves the large range by an exact
multiplicative-character sieve. The sieve separates the principal
Jacobi term from its square-root error and adds each unselected prime
factor in both coordinates.

The prime-power lifting, CRT, exceptional prime powers, and elementary
residue classes reuse arguments from the project's earlier contributions
#23028, #27721, #28047, #30020, #31446, #32057, and #32891.
The adjacent primitive-root method in the large-prime argument follows
the character sieve of S. D. Cohen, Pairs of primitive roots.
-/

section

/-! CRT/order stitching for A397683. The midpoint and even-square ideas are
extracted from accepted upstream reduction oeis-a397683.R1.H2.R1 (Ciphore).
This file has no imported conjecture and introduces no axioms. -/

namespace A397683CRT

def HasPair (m : ℕ) : Prop :=
  ∃ x : ZMod m, IsUnit x ∧ IsUnit (x+1) ∧ orderOf x = orderOf (x+1)

def HasEvenPair (m : ℕ) : Prop :=
  ∃ x : ZMod m, IsUnit x ∧ IsUnit (x+1) ∧
    orderOf x = orderOf (x+1) ∧ 2 ∣ orderOf x

theorem equal_order_of_square {M : Type*} [Monoid M] {x y : M}
    (hx : 2 ∣ orderOf x) (hy : 2 ∣ orderOf y) (h : orderOf (x^2) = orderOf (y^2)) :
    orderOf x = orderOf y := by
  rw [orderOf_pow_of_dvd (by decide) hx, orderOf_pow_of_dvd (by decide) hy] at h
  omega

theorem multiple21 (m : ℕ) (ho : Odd m) (hm : 21 ∣ m) : HasPair m := by
  obtain ⟨k,rfl⟩ := ho
  let m := 2*k+1
  have hmpos : 0 < m := by dsimp [m]; omega
  have h21 : 21 ≤ m := Nat.le_of_dvd hmpos hm
  have hc : k.Coprime m := by simp [m, Nat.mul_comm]
  have hc' : (k+1).Coprime m := by
    apply Nat.Coprime.symm
    change Nat.Coprime (2*k+1) (k+1)
    rw [show 2*k+1 = k+(k+1) by omega]
    simp
  have hs : (k : ZMod m) + (k+1 : ℕ) = 0 := by
    exact_mod_cast (show ((k+(k+1) : ℕ) : ZMod m) = 0 by
      rw [show k+(k+1) = m by dsimp [m]; omega]; simp)
  have h3 : 3 ∣ m := dvd_trans (by decide : 3 ∣ 21) hm
  have h7 : 7 ∣ m := dvd_trans (by decide : 7 ∣ 21) hm
  have e3 : ((k+1 : ℕ) : ZMod 3) = 2 := by
    apply (ZMod.natCast_eq_natCast_iff (k+1) 2 3).2
    change (k+1)%3 = 2%3
    dsimp [m] at h3; omega
  have e7 : (k : ZMod 7) = 3 := by
    apply (ZMod.natCast_eq_natCast_iff k 3 7).2
    change k%7 = 3%7
    dsimp [m] at h7; omega
  have hdiv3 := orderOf_map_dvd (ZMod.castHom h3 (ZMod 3)).toMonoidHom ((k+1 : ℕ) : ZMod m)
  have hdiv7 := orderOf_map_dvd (ZMod.castHom h7 (ZMod 7)).toMonoidHom (k : ZMod m)
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_natCast, e3, e7] at hdiv3 hdiv7
  have o3 : orderOf (2 : ZMod 3) = 2 := by apply orderOf_eq_prime <;> decide
  have o7 : orderOf (3 : ZMod 7) = 6 := by
    apply (orderOf_eq_iff (by decide)).2
    refine ⟨by decide, ?_⟩
    intro i hi hi0
    interval_cases i <;> decide
  rw [o3] at hdiv3
  rw [o7] at hdiv7
  have he := equal_order_of_square ((by decide : 2 ∣ 6).trans hdiv7) hdiv3 (by
    rw [show (k : ZMod m) = -((k+1 : ℕ) : ZMod m) from eq_neg_of_add_eq_zero_left hs, neg_sq])
  exact ⟨(k : ZMod m), (ZMod.isUnit_iff_coprime k m).2 hc,
    by simpa only [Nat.cast_add_one] using (ZMod.isUnit_iff_coprime (k+1) m).2 hc',
    by simpa only [Nat.cast_add_one] using he⟩

theorem extend {a b : ℕ} (ha : 1 < a) (hb : Odd b) (hc : a.Coprime b)
    (v : ZMod a) (hv : IsUnit v) (hw : IsUnit (v+1))
    (he : orderOf v = orderOf (v+1)) (h2 : 2 ∣ orderOf v) :
    HasPair (a*b) := by
  obtain ⟨k,rfl⟩ := hb
  let b := 2*k+1
  have hbpos : 0 < b := by dsimp [b]; omega
  have hm : 1 < a*b := by nlinarith
  let : NeZero (a*b) := ⟨by omega⟩
  let e := ZMod.chineseRemainder hc
  let y : ZMod (a*b) := e.symm (v,(k : ZMod b))
  have ey : e y = (v,(k : ZMod b)) := e.apply_symm_apply _
  have ey' : e (y+1) = (v+1,(k : ZMod b)+1) := by rw [map_add, ey, map_one]; rfl
  have neg : (k : ZMod b) = -((k : ZMod b)+1) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, show k+(k+1)=b by dsimp [b]; omega]
    simp
  have hsq : orderOf (v^2) = orderOf ((v+1)^2) := by
    rw [orderOf_pow_of_dvd (by decide) h2, orderOf_pow_of_dvd (by decide) (he ▸ h2), he]
  have eqord : orderOf y = orderOf (y+1) := by
    rw [← e.toMulEquiv.orderOf_eq y, ← e.toMulEquiv.orderOf_eq (y+1)]
    change orderOf (e y) = orderOf (e (y+1))
    rw [ey, ey']
    apply equal_order_of_square
    · rw [Prod.orderOf_mk]; exact h2.trans (Nat.dvd_lcm_left ..)
    · rw [Prod.orderOf_mk]; exact (he ▸ h2).trans (Nat.dvd_lcm_left ..)
    · simp only [Prod.pow_mk, Prod.orderOf_mk, hsq]
      rw [show (k : ZMod b)^2 = ((k : ZMod b)+1)^2 by conv_lhs => rw [neg, neg_sq]]
  have hku : IsUnit (k : ZMod b) := (ZMod.isUnit_iff_coprime ..).2 (by simp [b,Nat.mul_comm])
  have hku' : IsUnit ((k : ZMod b)+1) := by
    have hu : IsUnit (-((k : ZMod b)+1)) := neg ▸ hku
    simpa only [neg_neg] using hu.neg
  have uy : IsUnit y := by
    have h : IsUnit (e y) := by rw [ey]; exact Prod.isUnit_iff.mpr ⟨hv,hku⟩
    simpa using h.map e.symm.toMonoidHom
  have uy' : IsUnit (y+1) := by
    have h : IsUnit (e (y+1)) := by rw [ey']; exact Prod.isUnit_iff.mpr ⟨hw,hku'⟩
    simpa using h.map e.symm.toMonoidHom
  exact ⟨y, uy, uy', eqord⟩

theorem prime_power_of_one_prime (m : ℕ) (hm : 1 < m)
    (h : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ m ∧ q ∣ m) :
    ∃ p a : ℕ, p.Prime ∧ 1 ≤ a ∧ m = p ^ a := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have ha : 1 ≤ m.factorization p :=
    Nat.succ_le_of_lt (hp.factorization_pos_of_dvd hm0 hpm)
  set a := m.factorization p with ha_def
  have hpa_dvd : p ^ a ∣ m := (hp.pow_dvd_iff_le_factorization hm0).mpr (le_refl a)
  set s := m / p ^ a with hs_def
  have hdecomp : m = p ^ a * s := (Nat.mul_div_cancel' hpa_dvd).symm
  have hs0 : 0 < s := by
    apply Nat.div_pos (Nat.le_of_dvd (by omega) hpa_dvd) (pow_pos hp.pos a)
  by_cases hs1 : s = 1
  · exact ⟨p, a, hp, ha, by rw [hdecomp, hs1, mul_one]⟩
  · exfalso
    have hs2 : 1 < s := by omega
    obtain ⟨q, hq, hqs⟩ := Nat.exists_prime_and_dvd (by omega : s ≠ 1)
    have hqm : q ∣ m := hqs.trans (Nat.div_dvd_of_dvd hpa_dvd)
    by_cases hpq : p = q
    · subst hpq
      have hpdvd : p ^ (a + 1) ∣ m := by
        obtain ⟨t, ht⟩ := hqs
        rw [hdecomp, ht]
        use t
        ring_nf
      have hle : a + 1 ≤ m.factorization p :=
        (hp.pow_dvd_iff_le_factorization hm0).mp hpdvd
      omega
    · exact h ⟨p, q, hp, hq, hpq, hpm, hqm⟩

/-- An exact common-even-order input at each nonexceptional prime power.
No maximal order or primitive-root conclusion is required by global stitching. -/
def PrimePowerInput : Prop :=
  ∀ p a : ℕ, p.Prime → Odd p → p ≠ 3 → p ≠ 7 → 1 ≤ a → HasEvenPair (p^a)

/-- Stitching with an explicitly identified nonexceptional prime divisor. -/
theorem global_of_good_prime (localPairs : PrimePowerInput)
    (m : ℕ) (ho : Odd m) (r : ℕ) (hr : r.Prime) (hrm : r ∣ m)
    (hr3 : r ≠ 3) (hr7 : r ≠ 7) : HasPair m := by
  have hm : m ≠ 0 := by obtain ⟨k,h⟩ := ho; omega
  have hro : Odd r := by
    rcases hr.eq_two_or_odd with h | h
    · subst r; obtain ⟨k,h⟩ := ho; omega
    · exact Nat.odd_iff.mpr h
  let n := m.factorization r
  let b := m / r^n
  have hprod : r^n*b=m := Nat.ordProj_mul_ordCompl_eq_self m r
  have hn : 0 < n := hr.factorization_pos_of_dvd hm hrm
  have hb : Odd b := by
    rw [← hprod, Nat.odd_mul] at ho
    exact ho.2
  obtain ⟨v,hv,hw,he,h2⟩ := localPairs r n hr hro hr3 hr7 hn
  rw [← hprod]
  exact extend (one_lt_pow₀ hr.one_lt hn.ne') hb
    ((Nat.coprime_ordCompl hr hm).pow_left n) v hv hw he h2

/-- Complete global existence from exact prime-power inputs. This covers both
mixed 3/7 moduli (the midpoint lemma) and arbitrary odd coprime balancing. -/
theorem global_exists (localPairs : PrimePowerInput)
    (m : ℕ) (ho : Odd m) (hm : 1 < m)
    (hex : ¬ ∃ k : ℕ, 1 ≤ k ∧ (m = 3^k ∨ m = 7^k)) : HasPair m := by
  by_cases h21 : 21 ∣ m
  · exact multiple21 m ho h21
  have good : ∃ r : ℕ, r.Prime ∧ r ∣ m ∧ r ≠ 3 ∧ r ≠ 7 := by
    by_contra h
    have bad : ∀ p : ℕ, p.Prime → p ∣ m → p = 3 ∨ p = 7 := by
      intro p hp hpm
      by_cases hp3 : p = 3
      · exact Or.inl hp3
      · by_cases hp7 : p = 7
        · exact Or.inr hp7
        · exact (h ⟨p,hp,hpm,hp3,hp7⟩).elim
    have one : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ m ∧ q ∣ m := by
      rintro ⟨p,q,hp,hq,hpq,hpm,hqm⟩
      have h37 : Nat.Coprime 3 7 := by decide
      rcases bad p hp hpm with rfl | rfl <;> rcases bad q hq hqm with rfl | rfl
      · exact hpq rfl
      · exact h21 (h37.mul_dvd_of_dvd_of_dvd hpm hqm)
      · exact h21 (h37.mul_dvd_of_dvd_of_dvd hqm hpm)
      · exact hpq rfl
    obtain ⟨p,a,hp,ha,hma⟩ := prime_power_of_one_prime m hm one
    rcases bad p hp (hma ▸ dvd_pow_self p (by omega)) with h3 | h7
    · exact hex ⟨a,ha,Or.inl (by simpa [h3] using hma)⟩
    · exact hex ⟨a,ha,Or.inr (by simpa [h7] using hma)⟩
  obtain ⟨r,hr,hrm,hr3,hr7⟩ := good
  exact global_of_good_prime localPairs m ho r hr hrm hr3 hr7

/-- Mixed exceptional-prime powers need no prime-power witness hypothesis. -/
theorem mixed_exists (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    HasPair (3^a * 7^b) := by
  apply multiple21
  · have h3 : Odd (3^a) := Odd.pow (by decide : Odd (3 : ℕ))
    have h7 : Odd (7^b) := Odd.pow (by decide : Odd (7 : ℕ))
    exact h3.mul h7
  · exact Nat.mul_dvd_mul (dvd_pow_self 3 (by omega)) (dvd_pow_self 7 (by omega))

end A397683CRT

namespace A397683CRT

/-- Convert a residue-class witness to the exact pinned counting function. -/
theorem f_ne_zero_of_hasPair {m : ℕ} (hm : 1 < m) (hp : HasPair m) :
    OMA.S_oeis_a397683.f m ≠ 0 := by
  obtain ⟨y,uy,uy',eqord⟩ := hp
  let : NeZero m := ⟨by omega⟩
  have hval := ZMod.natCast_zmod_val y
  have c1 := (ZMod.isUnit_iff_coprime y.val m).1 (by rwa [hval])
  have c2 := (ZMod.isUnit_iff_coprime (y.val+1) m).1
    (by rwa [Nat.cast_add_one, hval])
  have hy0 : y.val ≠ 0 := by
    intro h
    simp [h, Nat.Coprime, Nat.ne_of_gt hm] at c1
  rw [OMA.S_oeis_a397683.f, if_neg (by omega)]
  exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨y.val, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ⟨by omega, ZMod.val_lt y⟩, c1, c2,
      by simpa [hval] using eqord⟩⟩)

/-- This is the full existence direction required by the original conjecture. -/
theorem global_f_ne_zero (localPairs : PrimePowerInput)
    (m : ℕ) (ho : Odd m) (hm : 1 < m)
    (hex : ¬ ∃ k : ℕ, 1 ≤ k ∧ (m = 3^k ∨ m = 7^k)) :
    OMA.S_oeis_a397683.f m ≠ 0 :=
  f_ne_zero_of_hasPair hm (global_exists localPairs m ho hm hex)

/-- Final theorem assembly, separating the two accepted obstruction proofs
from the genuinely missing local existence input. -/
theorem characterization_of_primePowerInput (localPairs : PrimePowerInput)
    (obstruction3 : ∀ k : ℕ, 1 ≤ k → OMA.S_oeis_a397683.f (3^k) = 0)
    (obstruction7 : ∀ k : ℕ, 1 ≤ k → OMA.S_oeis_a397683.f (7^k) = 0) :
    ∀ m : ℕ, Odd m → (OMA.S_oeis_a397683.f m = 0 ↔
      ∃ k : ℕ, 1 ≤ k ∧ (m = 3^k ∨ m = 7^k)) := by
  intro m ho
  constructor
  · intro hz
    by_contra hex
    have hm1 : m ≠ 1 := by
      intro hm
      subst m
      exact Nat.one_ne_zero hz
    have hm : 1 < m := by obtain ⟨k,hk⟩ := ho; omega
    exact global_f_ne_zero localPairs m ho hm hex hz
  · rintro ⟨k,hk,h3 | h7⟩
    · rw [h3]; exact obstruction3 k hk
    · rw [h7]; exact obstruction7 k hk

end A397683CRT

end

section

/-! The accepted prime-power obstructions from #32057 and #32891. -/


/-! Following @luciusacarr (#27330), retain the odd/even order obstruction.
Use the general lifting lemma employed by @sntntHb (#28139), and use the
negative-one power parity equivalence for the reduction modulo 3. -/

open OMA.S_oeis_a397683

theorem A397683CRT.obstruction3 : ∀ k : ℕ, 1 ≤ k → f (3 ^ k) = 0 := by
  intro k hk
  have hne : 3 ^ k ≠ 1 := by
    have : 3 ≤ 3 ^ k := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  unfold f
  rw [if_neg hne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨hx, hx1, hord⟩
  have h3dvd : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  have hx3 : ¬ 3 ∣ x := fun h =>
    absurd (Nat.dvd_gcd h h3dvd) (by rw [hx]; norm_num)
  have hx13 : ¬ 3 ∣ x + 1 := fun h =>
    absurd (Nat.dvd_gcd h h3dvd) (by rw [hx1]; norm_num)
  have hxmod : x % 3 = 1 := by omega
  -- order of x is odd
  have hodd : Odd (orderOf (x : ZMod (3 ^ k))) := by
    have hdvd : (3 : ℤ) ^ (k - 1 + 1) ∣ (x : ℤ) ^ (3 ^ (k - 1)) - 1 :=
      by simpa using dvd_sub_pow_of_dvd_sub (show (3 : ℤ) ∣ (x : ℤ) - 1 by omega) (k - 1)
    rw [show k - 1 + 1 = k by omega] at hdvd
    have hpow : (x : ZMod (3 ^ k)) ^ (3 ^ (k - 1)) = 1 := by
      have h0 : (((x : ℤ) ^ (3 ^ (k - 1)) - 1 : ℤ) : ZMod (3 ^ k)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact_mod_cast hdvd
      push_cast at h0
      exact sub_eq_zero.mp h0
    have hd := orderOf_dvd_of_pow_eq_one hpow
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hd
  -- order of x + 1 is even
  have heven : Even (orderOf (((x + 1 : ℕ) : ZMod (3 ^ k)))) := by
    set d := orderOf (((x + 1 : ℕ) : ZMod (3 ^ k)))
    have hp : (((x + 1 : ℕ) : ZMod (3 ^ k))) ^ d = 1 := pow_orderOf_eq_one _
    have hmap := congrArg (ZMod.castHom h3dvd (ZMod 3)) hp
    rw [map_pow, map_natCast, map_one] at hmap
    have h2 : (((x + 1 : ℕ)) : ZMod 3) = 2 := by
      rw [← ZMod.natCast_mod, show (x + 1) % 3 = 2 by omega]
      rfl
    rw [h2] at hmap
    rw [show (2 : ZMod 3) = -1 by decide] at hmap
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hmap
  rw [hord] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) heven


-- Following @luciusacarr (#27449), retain the five residue-order obstructions.
-- Replace the custom seventh-power lifting induction with the general library
-- lemma used in @sntntHb's H3 proof (#28139), and use finite-field power APIs.
-- H4 := ∀ k : ℕ, 1 ≤ k → f (7 ^ k) = 0

/-! Let `x, x + 1` be units modulo `7^k` with common order `d`. Reducing modulo `7`,
`x^d ≡ (x+1)^d ≡ 1`. Lifting the exponent for `7` shows that if `z^o ≡ 1 (mod 7)` then
`z^(o·7^(k-1)) ≡ 1 (mod 7^k)`, so `d ∣ o·7^(k-1)`. For each residue `x mod 7 ∈ {1,…,5}` the
orders modulo `7` of `x` and `x+1` (`1/3, 3/6, 6/3, 3/6, 6/2`) differ in a prime `q ∈ {2,3}`
coprime to `7`, which divides `d` but not `o·7^(k-1)`. -/

open OMA.S_oeis_a397683

namespace OMA.S397683H4

theorem lte7 (a : ℤ) (ha : (7 : ℤ) ∣ a - 1) : ∀ i : ℕ, (7 : ℤ) ^ (i + 1) ∣ a ^ (7 ^ i) - 1 := by
  intro i
  simpa using dvd_sub_pow_of_dvd_sub ha i

theorem up (z o k : ℕ) (hk : 1 ≤ k) (h : (z : ZMod 7) ^ o = 1) :
    (z : ZMod (7 ^ k)) ^ (o * 7 ^ (k - 1)) = 1 := by
  have h7 : (7 : ℤ) ∣ ((z : ℤ) ^ o) - 1 := by
    have h0 : ((((z : ℤ) ^ o - 1 : ℤ)) : ZMod 7) = 0 := by
      push_cast; rw [h]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp h0
  have hd := lte7 _ h7 (k - 1)
  rw [show k - 1 + 1 = k by omega, ← pow_mul] at hd
  have h0 : ((((z : ℤ) ^ (o * 7 ^ (k - 1)) - 1 : ℤ)) : ZMod (7 ^ k)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hd
  push_cast at h0
  exact sub_eq_zero.mp h0

theorem down (z d k : ℕ) (hk : 1 ≤ k) (h : (z : ZMod (7 ^ k)) ^ d = 1) : (z : ZMod 7) ^ d = 1 := by
  have h7 : 7 ∣ 7 ^ k := dvd_pow_self 7 (by omega)
  have hmap := congrArg (ZMod.castHom h7 (ZMod 7)) h
  rwa [map_pow, map_natCast, map_one] at hmap

theorem cast_mod (z : ℕ) : (z : ZMod 7) = ((z % 7 : ℕ) : ZMod 7) := (ZMod.natCast_mod z 7).symm

theorem pow_mod6 (a : ZMod 7) (ha : a ≠ 0) (d : ℕ) : a ^ d = a ^ (d % 6) := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact pow_eq_pow_mod d (ZMod.pow_card_sub_one_eq_one ha)

theorem not_dvd_mul (q o k : ℕ) (hq : q.Prime) (hq7 : q ≠ 7) (hqo : ¬ q ∣ o) :
    ¬ q ∣ o * 7 ^ (k - 1) := by
  intro h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact hqo h
  · have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
    exact hq7 this

end OMA.S397683H4

open OMA.S397683H4 in
theorem A397683CRT.obstruction7 : ∀ k : ℕ, 1 ≤ k → f (7 ^ k) = 0 := by
  intro k hk
  have hne : 7 ^ k ≠ 1 := by
    have : 7 ≤ 7 ^ k := by
      calc 7 = 7 ^ 1 := by norm_num
        _ ≤ 7 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  unfold f
  rw [if_neg hne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨hx, hx1, hord⟩
  have h7dvd : 7 ∣ 7 ^ k := dvd_pow_self 7 (by omega)
  have hx7 : ¬ 7 ∣ x := fun h =>
    absurd (Nat.dvd_gcd h h7dvd) (by rw [hx]; norm_num)
  have hx17 : ¬ 7 ∣ x + 1 := fun h =>
    absurd (Nat.dvd_gcd h h7dvd) (by rw [hx1]; norm_num)
  obtain ⟨d, hd⟩ : ∃ d, d = orderOf (x : ZMod (7 ^ k)) := ⟨_, rfl⟩
  have hpx : (x : ZMod (7 ^ k)) ^ d = 1 := by rw [hd]; exact pow_orderOf_eq_one _
  have hpx1 : (((x + 1 : ℕ) : ZMod (7 ^ k))) ^ d = 1 := by
    rw [hd, hord]; exact pow_orderOf_eq_one _
  have dx := down x d k hk hpx
  have dx1 := down (x + 1) d k hk hpx1
  rw [cast_mod] at dx dx1
  have hdx : ∀ o, ((x % 7 : ℕ) : ZMod 7) ^ o = 1 → d ∣ o * 7 ^ (k - 1) := fun o ho => by
    rw [hd]
    exact orderOf_dvd_of_pow_eq_one (up x o k hk (by rw [cast_mod]; exact ho))
  have hdx1 : ∀ o, (((x + 1) % 7 : ℕ) : ZMod 7) ^ o = 1 → d ∣ o * 7 ^ (k - 1) := fun o ho => by
    rw [hd, hord]
    exact orderOf_dvd_of_pow_eq_one (up (x + 1) o k hk (by rw [cast_mod]; exact ho))
  have hr : x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 := by omega
  have h6 : d % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rcases hr with hr | hr | hr | hr | hr
  · -- x ≡ 1, x+1 ≡ 2 : 3 ∣ d, d ∣ 7^(k-1)
    have hm : (x + 1) % 7 = 2 := by omega
    rw [hm] at dx1
    rw [pow_mod6 _ (by decide)] at dx1
    have h3 : 3 ∣ d := by
      interval_cases h : d % 6 <;> first | omega | (exfalso; revert dx1; decide)
    have := hdx 1 (by rw [hr]; norm_num)
    exact not_dvd_mul 3 1 k (by norm_num) (by norm_num) (by norm_num) (h3.trans this)
  · -- x ≡ 2 (order 3), x+1 ≡ 3 (order 6)
    have hm : (x + 1) % 7 = 3 := by omega
    rw [hm] at dx1
    rw [pow_mod6 _ (by decide)] at dx1
    have h2 : 2 ∣ d := by
      interval_cases h : d % 6 <;> first | omega | (exfalso; revert dx1; decide)
    have := hdx 3 (by rw [hr]; decide)
    exact not_dvd_mul 2 3 k (by norm_num) (by norm_num) (by norm_num) (h2.trans this)
  · -- x ≡ 3 (order 6), x+1 ≡ 4 (order 3)
    have hm : (x + 1) % 7 = 4 := by omega
    rw [hr] at dx
    rw [pow_mod6 _ (by decide)] at dx
    have h2 : 2 ∣ d := by
      interval_cases h : d % 6 <;> first | omega | (exfalso; revert dx; decide)
    have := hdx1 3 (by rw [hm]; decide)
    exact not_dvd_mul 2 3 k (by norm_num) (by norm_num) (by norm_num) (h2.trans this)
  · -- x ≡ 4 (order 3), x+1 ≡ 5 (order 6)
    have hm : (x + 1) % 7 = 5 := by omega
    rw [hm] at dx1
    rw [pow_mod6 _ (by decide)] at dx1
    have h2 : 2 ∣ d := by
      interval_cases h : d % 6 <;> first | omega | (exfalso; revert dx1; decide)
    have := hdx 3 (by rw [hr]; decide)
    exact not_dvd_mul 2 3 k (by norm_num) (by norm_num) (by norm_num) (h2.trans this)
  · -- x ≡ 5 (order 6), x+1 ≡ 6 (order 2)
    have hm : (x + 1) % 7 = 6 := by omega
    rw [hr] at dx
    rw [pow_mod6 _ (by decide)] at dx
    have h3 : 3 ∣ d := by
      interval_cases h : d % 6 <;> first | omega | (exfalso; revert dx; decide)
    have := hdx1 2 (by rw [hm]; decide)
    exact not_dvd_mul 3 2 k (by norm_num) (by norm_num) (by norm_num) (h3.trans this)

end

section

/-! Port of accepted upstream A397683 simultaneous lifting arithmetic,
with the short `primePowerOrderLift` from its accepted reduction. Original
file credits are retained in the local handoff; no placeholder reduction
or target theorem is imported. -/
namespace A397683PrimePowerLift

/-- For `x ^ d - 1 = p s`, the lift `x + k p` has
`(x + k p) ^ d - x ^ d ≡ p (x^(d-1) d k) (mod p²)`. -/
theorem lift_mod (p x k : ℤ) (n : ℕ) :
    p ^ 2 ∣ (x + k * p) ^ n - x ^ n - p * (x ^ (n - 1) * n * k) := by
  have h := sq_dvd_add_pow_sub_sub (k * p) x n
  have h2 : p ^ 2 ∣ (k * p) ^ 2 := ⟨k ^ 2, by ring⟩
  obtain ⟨c, hc⟩ := dvd_trans h2 h
  exact ⟨c, by linear_combination hc⟩

theorem main (p x d : ℕ) (hp : p.Prime) (hodd : Odd p) (hx1 : 1 ≤ x) (hxp : x + 1 < p)
    (hd : d ≠ 0) (ho : orderOf (x : ZMod p) = d) (ho' : orderOf ((x + 1 : ℕ) : ZMod p) = d) :
    ∃ y t u : ℕ, 1 ≤ y ∧ y < p ^ 2 ∧ y ≡ x [MOD p] ∧ y ^ d = 1 + p * t ∧
      (y + 1) ^ d = 1 + p * u ∧ ¬ (p : ℤ) ∣ (t : ℤ) ∧ ¬ (p : ℤ) ∣ (u : ℤ) := by
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by
    rcases hodd with ⟨m, hm⟩
    omega
  have hx0 : (x : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hx0' : ((x + 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hdp : d ∣ p - 1 := ho ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have hdlt : d < p := by
    have := Nat.le_of_dvd (by omega) hdp
    omega
  have hd0 : (d : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hxd : (x : ZMod p) ^ d = 1 := ho ▸ pow_orderOf_eq_one _
  have hxd' : ((x : ZMod p) + 1) ^ d = 1 := by
    have := ho' ▸ pow_orderOf_eq_one ((x + 1 : ℕ) : ZMod p)
    exact_mod_cast this
  have hs : (p : ℤ) ∣ (x : ℤ) ^ d - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hxd, sub_self]
  have hs' : (p : ℤ) ∣ ((x : ℤ) + 1) ^ d - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hxd', sub_self]
  obtain ⟨s, hs⟩ := hs
  obtain ⟨s', hs'⟩ := hs'
  set c : ZMod p := (x : ZMod p) ^ (d - 1) * d with hc
  set c' : ZMod p := ((x : ZMod p) + 1) ^ (d - 1) * d with hc'
  have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hx0) hd0
  have hc0' : c' ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) hd0
    exact_mod_cast hx0'
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  have h02 : (0 : ZMod p) ≠ 2 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h.symm
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have h12 : (1 : ZMod p) ≠ 2 := by
    intro h
    have : ((1 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) - 1 = 0 := by rw [← h]; ring
      exact_mod_cast (by linear_combination this : (1 : ZMod p) = 0)
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have r : ∀ (e f : ZMod p), f ≠ 0 → ∀ a b : ZMod p, e + f * a = 0 → e + f * b = 0 → a = b := by
    intro e f hf a b ha hb
    have : f * (a - b) = 0 := by linear_combination ha - hb
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hf
    · exact sub_eq_zero.mp h
  obtain ⟨k, hk3, hgood, hgood'⟩ : ∃ k : ℕ, k ≤ 2 ∧ (s : ZMod p) + c * k ≠ 0 ∧
      (s' : ZMod p) + c' * k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have e0 := hcon 0 (by omega)
    have e1 := hcon 1 (by omega)
    have e2 := hcon 2 (by omega)
    push_cast at e0 e1 e2
    by_cases a0 : (s : ZMod p) + c * 0 = 0
    · by_cases a1 : (s : ZMod p) + c * 1 = 0
      · exact h01 (r _ _ hc0 _ _ a0 a1)
      · by_cases a2 : (s : ZMod p) + c * 2 = 0
        · exact h02 (r _ _ hc0 _ _ a0 a2)
        · exact h12 (r _ _ hc0' _ _ (e1 a1) (e2 a2))
    · by_cases a1 : (s : ZMod p) + c * 1 = 0
      · by_cases a2 : (s : ZMod p) + c * 2 = 0
        · exact h12 (r _ _ hc0 _ _ a1 a2)
        · exact h02 (r _ _ hc0' _ _ (e0 a0) (e2 a2))
      · exact h01 (r _ _ hc0' _ _ (e0 a0) (e1 a1))
  have hyd : 1 ≤ (x + k * p) ^ d := Nat.one_le_pow _ _ (by omega)
  have hyd' : 1 ≤ (x + k * p + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hdvd : p ∣ (x + k * p) ^ d - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hyd]
    push_cast
    rw [ZMod.natCast_self, mul_zero, add_zero, hxd, sub_self]
  have hdvd' : p ∣ (x + k * p + 1) ^ d - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hyd']
    push_cast
    rw [ZMod.natCast_self, mul_zero, add_zero, hxd', sub_self]
  obtain ⟨t, ht⟩ := hdvd
  obtain ⟨u, hu⟩ := hdvd'
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨x + k * p, t, u, by omega, ?_, ?_, by omega, by omega, ?_, ?_⟩
  · have : k * p ≤ 2 * p := Nat.mul_le_mul_right _ hk3
    have : 3 * p ≤ p * p := Nat.mul_le_mul_right _ hp3
    rw [pow_two]; omega
  · simp [Nat.ModEq, Nat.add_mul_mod_self_right]
  · intro htd
    obtain ⟨m, hm⟩ := htd
    obtain ⟨q, hq⟩ := lift_mod (p : ℤ) (x : ℤ) (k : ℤ) d
    have hyt : (((x + k * p) ^ d : ℕ) : ℤ) = 1 + p * t := by
      have : (x + k * p) ^ d = 1 + p * t := by omega
      exact_mod_cast this
    push_cast at hyt
    have e2 : s + (x : ℤ) ^ (d - 1) * d * k = p * (m - q) := by
      apply mul_left_cancel₀ hp0
      linear_combination hyt - hq - hs + (p : ℤ) * hm
    apply hgood
    have : ((s + (x : ℤ) ^ (d - 1) * d * k : ℤ) : ZMod p) = 0 := by
      rw [e2]; push_cast; simp
    push_cast at this
    rw [hc]; linear_combination this
  · intro hud
    obtain ⟨m, hm⟩ := hud
    obtain ⟨q, hq⟩ := lift_mod (p : ℤ) ((x : ℤ) + 1) (k : ℤ) d
    have hyt : (((x + k * p + 1) ^ d : ℕ) : ℤ) = 1 + p * u := by
      have : (x + k * p + 1) ^ d = 1 + p * u := by omega
      exact_mod_cast this
    push_cast at hyt
    have e2 : s' + ((x : ℤ) + 1) ^ (d - 1) * d * k = p * (m - q) := by
      apply mul_left_cancel₀ hp0
      linear_combination hyt - hq - hs' + (p : ℤ) * hm
    apply hgood'
    have : ((s' + ((x : ℤ) + 1) ^ (d - 1) * d * k : ℤ) : ZMod p) = 0 := by
      rw [e2]; push_cast; simp
    push_cast at this
    rw [hc']; linear_combination this

theorem primePowerOrderLift {p x d t : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hd : d ≠ 0) (hbase : orderOf (x : ZMod p) = d)
    (hpow : x ^ d = 1 + p * t) (ht : ¬ (p : ℤ) ∣ (t : ℤ)) (n : ℕ) :
    orderOf (x : ZMod (p ^ (n+1))) = d * p ^ n := by
  let hmap := ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p)
  have hdiv := orderOf_map_dvd hmap.toMonoidHom (x : ZMod (p^(n+1)))
  have hdiv' : d ∣ orderOf (x : ZMod (p^(n+1))) := by
    simpa [hmap, hbase] using hdiv
  have h := ZMod.orderOf_one_add_mul_prime hp ho (t : ℤ) ht n
  have he : (x : ZMod (p^(n+1)))^d = 1 + (p : ℕ) * (t : ℤ) := by
    exact_mod_cast congrArg (fun z : ℕ => (z : ZMod (p^(n+1)))) hpow
  rw [← he, orderOf_pow_of_dvd hd hdiv'] at h
  rw [← h, Nat.mul_div_cancel' hdiv']


theorem hasEvenPair_prime_power : ∀ p n : ℕ, p.Prime → Odd p → 1 ≤ n →
    A397683CRT.HasEvenPair p → A397683CRT.HasEvenPair (p^n) := by
  intro p n hp hodd hn ⟨v, hv, hv1, hord, h2⟩
  have := Fact.mk hp
  have hp1 : 1 < p := hp.one_lt
  set x := v.val with hx
  have hxv : (x : ZMod p) = v := ZMod.natCast_zmod_val v
  have hxp : x < p := ZMod.val_lt v
  have hx0 : x ≠ 0 := by
    intro h; rw [h, Nat.cast_zero] at hxv; rw [← hxv] at hv; exact not_isUnit_zero hv
  have hx1 : x + 1 ≠ p := by
    intro h
    have : ((x + 1 : ℕ) : ZMod p) = 0 := by rw [h]; exact ZMod.natCast_self p
    push_cast at this; rw [hxv] at this; rw [this] at hv1; exact not_isUnit_zero hv1
  have hxv1 : ((x + 1 : ℕ) : ZMod p) = v + 1 := by push_cast; rw [hxv]
  set d := orderOf v with hdd
  have hd0 : d ≠ 0 := by
    rw [hdd]; exact (orderOf_pos_iff.mpr (hv.isOfFinOrder)).ne'
  have hdx : orderOf (x : ZMod p) = d := by rw [hxv]
  have hdx1 : orderOf ((x + 1 : ℕ) : ZMod p) = d := by rw [hxv1, ← hord]
  obtain ⟨y, t, u, hy1, hyp, hyx, hyt, hyu, ht, hu⟩ :=
    main p x d hp hodd (by omega) (by omega) hd0 hdx hdx1
  have hyxz : (y : ZMod p) = (x : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hyx
  have hy1xz : ((y + 1 : ℕ) : ZMod p) = ((x + 1 : ℕ) : ZMod p) := by push_cast; rw [hyxz]
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k,hk⟩ := hodd; omega
  have oy : orderOf (y : ZMod (p^n)) = d*p^(n-1) := by
    have heq : n = (n-1)+1 := by omega
    conv_lhs => rw [heq]
    exact primePowerOrderLift hp hp2 hd0 (by rw [hyxz, hdx]) hyt ht (n-1)
  have oy1 : orderOf ((y+1 : ℕ) : ZMod (p^n)) = d*p^(n-1) := by
    have heq : n = (n-1)+1 := by omega
    conv_lhs => rw [heq]
    exact primePowerOrderLift hp hp2 hd0 (by rw [hy1xz, hdx1]) hyu hu (n-1)
  have hcop : ∀ z : ℕ, (z : ZMod p) ≠ 0 → IsUnit (z : ZMod (p ^ n)) := by
    intro z hz
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h; exact hz ((ZMod.natCast_eq_zero_iff z p).mpr h)
  refine ⟨(y : ZMod (p ^ n)), hcop y ?_, ?_, ?_, ?_⟩
  · rw [hyxz, hxv]; exact hv.ne_zero
  · have := hcop (y + 1) (by rw [hy1xz, hxv1]; exact hv1.ne_zero)
    push_cast at this; exact this
  · have : ((y : ZMod (p ^ n)) + 1) = ((y + 1 : ℕ) : ZMod (p ^ n)) := by push_cast; rfl
    rw [this, oy, oy1]
  · rw [oy]; exact Dvd.dvd.mul_right h2 _


def PrimeInput : Prop := ∀ p : ℕ,
  p.Prime → Odd p → p ≠ 3 → p ≠ 7 → A397683CRT.HasEvenPair p

/-- The exact local interface consumed by the checked CRT global theorem. -/
theorem primePowerInput_of_primeInput (h : PrimeInput) : A397683CRT.PrimePowerInput := by
  intro p a hp ho hp3 hp7 ha
  exact hasEvenPair_prime_power p a hp ho ha (h p hp ho hp3 hp7)

end A397683PrimePowerLift

end

section

namespace A397683Threshold
open Finset

def primeFloor (i : ℕ) : ℕ :=
  [2,3,7,11,13,17,19,23,29,31,37,41,43,47].getD i 47

def core (w : ℕ) : ℕ := if w ≤ 1 then 1 else if w ≤ 7 then 2 else 3

def bound (w : ℕ) : ℕ :=
  [0,36,324,3944,19098,73741,258542,1093162,3502580,7595456,
    16978785,38442347,96355652,321586627].getD w 0

def delta (w : ℕ) (q : ℕ → ℕ) : ℚ :=
  1 - 2 * ∑ i ∈ range w, if core w ≤ i then (1 : ℚ) / q i else 0

def sieveSquare (w : ℕ) (d : ℚ) : ℚ :=
  ((4 : ℚ) ^ core w * (1 + 2 * (w - core w : ℕ) / d) + 2) ^ 2

/-- Exact finite arithmetic for the thirteen core choices. -/
theorem table : ∀ w : Fin 14, 1 ≤ w.val →
    0 < delta w.val primeFloor ∧
    sieveSquare w.val (delta w.val primeFloor) ≤ bound w.val ∧
    (w.val ≤ 6 → bound w.val < 260000) ∧
    (7 ≤ w.val → bound w.val < ∏ i ∈ range w.val, primeFloor i) := by
  intro ⟨w, hw⟩ hw1
  change 1 ≤ w at hw1
  interval_cases w <;>
    norm_num [delta, sieveSquare, primeFloor, core, bound, sum_range_succ, prod_range_succ] at *

/-- The fourteen smallest admissible distinct factors already exceed
three halves of the unsieved exponential scale. -/
theorem fourteen_product :
    3 * 16 ^ 14 ≤ 2 * ∏ i ∈ range 14, primeFloor i := by
  decide

private theorem floor_pos : ∀ i : Fin 14, 0 < primeFloor i.val := by decide

/-- Coordinatewise larger primes make the sieve delta larger. -/
theorem delta_mono {w : ℕ} (hw : w ≤ 13) (q : ℕ → ℕ)
    (hq : ∀ i < w, primeFloor i ≤ q i) :
    delta w primeFloor ≤ delta w q := by
  unfold delta
  have hs : (∑ i ∈ range w, if core w ≤ i then (1 : ℚ) / q i else 0) ≤
      ∑ i ∈ range w, if core w ≤ i then (1 : ℚ) / primeFloor i else 0 := by
    apply sum_le_sum
    intro i hi
    split_ifs
    · have hiw := mem_range.mp hi
      have hpos : (0 : ℚ) < primeFloor i := by
        exact_mod_cast floor_pos ⟨i, by omega⟩
      apply one_div_le_one_div_of_le hpos
      exact_mod_cast hq i hiw
    · exact le_rfl
  linarith

/-- Explicit checked sieve bound, independent of the character-sum theorem. -/
theorem sieve_bound {w : ℕ} (hw1 : 1 ≤ w) (hw : w ≤ 13) (q : ℕ → ℕ)
    (hq : ∀ i < w, primeFloor i ≤ q i) :
    0 < delta w q ∧ sieveSquare w (delta w q) ≤ bound w := by
  obtain ⟨hd, hb, _, _⟩ := table ⟨w, by omega⟩ hw1
  have hm := delta_mono hw q hq
  have hdq : 0 < delta w q := hd.trans_le hm
  refine ⟨hdq, le_trans ?_ hb⟩
  unfold sieveSquare
  have hdiv : (2 * (w - core w : ℕ) : ℚ) / delta w q ≤
      (2 * (w - core w : ℕ) : ℚ) / delta w primeFloor := by
    exact div_le_div_of_nonneg_left (by positivity) hd hm
  have hnonneg : 0 ≤ (4 : ℚ) ^ core w * (1 + 2 * (w - core w : ℕ) / delta w q) + 2 := by
    positivity
  gcongr

/-- If at most six factors occur, the single finite cutoff suffices. -/
theorem small_eligible {w p : ℕ} (hw1 : 1 ≤ w) (hw : w ≤ 6) (hp : 260000 ≤ p)
    (q : ℕ → ℕ) (hq : ∀ i < w, primeFloor i ≤ q i) :
    0 < delta w q ∧ sieveSquare w (delta w q) < p := by
  obtain ⟨hd, hb⟩ := sieve_bound hw1 (by omega) q hq
  have ht := (table ⟨w, by omega⟩ hw1).2.2.1 hw
  exact ⟨hd, hb.trans_lt (by exact_mod_cast lt_of_lt_of_le ht hp)⟩

/-- With seven through thirteen factors, their product alone gives eligibility. -/
theorem medium_eligible {w p : ℕ} (hw1 : 7 ≤ w) (hw : w ≤ 13)
    (q : ℕ → ℕ) (hq : ∀ i < w, primeFloor i ≤ q i)
    (hp : (∏ i ∈ range w, q i) < p) :
    0 < delta w q ∧ sieveSquare w (delta w q) < p := by
  obtain ⟨hd, hb⟩ := sieve_bound (by omega) hw q hq
  have ht := (table ⟨w, by omega⟩ (show 1 ≤ w by omega)).2.2.2 hw1
  have hprod : (∏ i ∈ range w, primeFloor i) ≤ ∏ i ∈ range w, q i := by
    exact prod_le_prod' (fun i hi => hq i (mem_range.mp hi))
  exact ⟨hd, hb.trans_lt (by exact_mod_cast lt_of_lt_of_le ht hprod |>.trans hp)⟩

private theorem floor_le47 : ∀ i : Fin 14, primeFloor i.val ≤ 47 := by decide

private theorem prime_gap : ∀ i : Fin 13, ∀ n : Fin 48,
    primeFloor i.val < n.val → n.val < primeFloor (i.val + 1) →
      ¬ n.val.Prime ∨ n.val = 5 := by decide

/-- Sorted distinct prime factors excluding five dominate the eligible list. -/
theorem coordinate_lower {w : ℕ} (q : ℕ → ℕ)
    (hp : ∀ i < w, (q i).Prime) (h5 : ∀ i < w, q i ≠ 5)
    (hs : ∀ i j, i < j → j < w → q i < q j) :
    ∀ i, i < w → i < 14 → primeFloor i ≤ q i := by
  intro i
  induction i with
  | zero =>
    intro hi _
    simpa only [primeFloor, List.getD_cons_zero] using (hp 0 hi).two_le
  | succ i ih =>
    intro hi hi14
    have hprev := ih (by omega) (by omega)
    have hlt : primeFloor i < q (i+1) := hprev.trans_lt (hs i (i+1) (by omega) hi)
    by_contra hn
    have hn' : q (i+1) < primeFloor (i+1) := by omega
    have hu := floor_le47 ⟨i+1, hi14⟩
    change primeFloor (i+1) ≤ 47 at hu
    have hg := prime_gap ⟨i, by omega⟩ ⟨q (i+1), by omega⟩ hlt hn'
    exact hg.elim (fun h => h (hp (i+1) hi)) (h5 (i+1) hi)

/-- Elementary exponential comparison used by the unsieved case. -/
theorem unsieved_square {w : ℕ} (hw : 2 ≤ w) :
    2 * (4 ^ w + 2) ^ 2 < 3 * 16 ^ w := by
  have hz : 16 ≤ 4 ^ w := by
    calc 16 = 4 ^ 2 := by norm_num
         _ ≤ 4 ^ w := Nat.pow_le_pow_right (by omega) hw
  have he : 16 ^ w = (4 ^ w) ^ 2 := by
    rw [← pow_mul, mul_comm w 2, pow_mul]
    norm_num
  rw [he]
  nlinarith

/-- Fourteen eligible factors and factors at least sixteen thereafter beat
all remaining unsieved thresholds. -/
theorem large_product {w : ℕ} (hw : 14 ≤ w) (q : ℕ → ℕ)
    (hh : ∀ i < 14, primeFloor i ≤ q i)
    (ht : ∀ i, 14 ≤ i → i < w → 16 ≤ q i) :
    (4 ^ w + 2) ^ 2 < ∏ i ∈ range w, q i := by
  have hhead : (∏ i ∈ range 14, primeFloor i) ≤ ∏ i ∈ range 14, q i :=
    prod_le_prod' (fun i hi => hh i (mem_range.mp hi))
  have htail : 16 ^ (w-14) ≤ ∏ i ∈ range (w-14), q (14+i) := by
    calc
      16 ^ (w-14) = ∏ _i ∈ range (w-14), (16 : ℕ) := by simp
      _ ≤ ∏ i ∈ range (w-14), q (14+i) := by
        apply prod_le_prod'
        intro i hi
        exact ht (14+i) (by omega) (by have := mem_range.mp hi; omega)
  have hp : 3 * 16 ^ w ≤ 2 * ∏ i ∈ range w, q i := by
    rw [← Nat.add_sub_of_le hw, pow_add, prod_range_add]
    have hmul := Nat.mul_le_mul (fourteen_product.trans (Nat.mul_le_mul_left 2 hhead)) htail
    nlinarith
  have hb := unsieved_square (w := w) (by omega)
  omega

/-- The unsieved eligibility conclusion for any sorted factor list. -/
theorem large_eligible {w p : ℕ} (hw : 14 ≤ w) (q : ℕ → ℕ)
    (hp : ∀ i < w, (q i).Prime) (h5 : ∀ i < w, q i ≠ 5)
    (hs : ∀ i j, i < j → j < w → q i < q j)
    (hprod : (∏ i ∈ range w, q i) < p) :
    (4 ^ w + 2) ^ 2 < p := by
  apply lt_trans (large_product hw q ?_ ?_) hprod
  · intro i hi
    exact coordinate_lower q hp h5 hs i (by omega) hi
  · intro i hi hiw
    have h13 := coordinate_lower q hp h5 hs 13 (by omega) (by omega)
    have hstrict := hs 13 i (by omega) hiw
    norm_num [primeFloor] at h13
    omega

/-- The two remaining residue classes exclude the factor five from p-1. -/
theorem five_excluded {p : ℕ} (hp : p % 20 = 3 ∨ p % 20 = 7) : ¬ 5 ∣ p-1 := by
  intro h
  have hmod := Nat.mod_eq_zero_of_dvd h
  have hreduce : (p % 20) % 5 = p % 5 := Nat.mod_mod_of_dvd p (by decide : 5 ∣ 20)
  rcases hp with hp | hp <;> omega

/-- Pure arithmetic eligibility in a form directly consumable by the character
sieve: the chosen core, positive delta, and its strict threshold inequality. -/
theorem eligible {w p : ℕ} (hw : 1 ≤ w) (hp : 260000 ≤ p) (q : ℕ → ℕ)
    (hprime : ∀ i < w, (q i).Prime) (h5 : ∀ i < w, q i ≠ 5)
    (hs : ∀ i j, i < j → j < w → q i < q j)
    (hprod : (∏ i ∈ range w, q i) < p) :
    ∃ k : ℕ, k ≤ w ∧
      let d : ℚ := 1 - 2 * ∑ i ∈ range w, if k ≤ i then (1 : ℚ) / q i else 0
      0 < d ∧ ((4 : ℚ)^k * (1 + 2 * (w-k : ℕ) / d) + 2)^2 < p := by
  by_cases hsmall : w ≤ 13
  · have hq : ∀ i < w, primeFloor i ≤ q i :=
      fun i hi => coordinate_lower q hprime h5 hs i hi (by omega)
    have hbound : 0 < delta w q ∧ sieveSquare w (delta w q) < p := by
      by_cases h6 : w ≤ 6
      · exact small_eligible hw h6 hp q hq
      · exact medium_eligible (by omega) hsmall q hq hprod
    refine ⟨core w, ?_, hbound⟩
    unfold core
    split_ifs <;> omega
  · have hlarge : 14 ≤ w := by omega
    have hbound := large_eligible hlarge q hprime h5 hs hprod
    have hz : (∑ i ∈ range w, if w ≤ i then (1 : ℚ) / q i else 0) = 0 := by
      apply sum_eq_zero
      intro i hi
      rw [if_neg (by have := mem_range.mp hi; omega)]
    refine ⟨w, le_rfl, ?_⟩
    rw [hz]
    simp only [mul_zero, sub_zero, Nat.sub_self, Nat.cast_zero, zero_div,
      add_zero, mul_one]
    exact ⟨by norm_num, by exact_mod_cast hbound⟩

/-- The same interface with exclusion of five derived from the residue class. -/
theorem eligible_of_residue {w p : ℕ} (hw : 1 ≤ w) (hp : 260000 ≤ p)
    (hres : p % 20 = 3 ∨ p % 20 = 7) (q : ℕ → ℕ)
    (hprime : ∀ i < w, (q i).Prime) (hfactor : ∀ i < w, q i ∣ p-1)
    (hs : ∀ i j, i < j → j < w → q i < q j)
    (hprod : (∏ i ∈ range w, q i) < p) :
    ∃ k : ℕ, k ≤ w ∧
      let d : ℚ := 1 - 2 * ∑ i ∈ range w, if k ≤ i then (1 : ℚ) / q i else 0
      0 < d ∧ ((4 : ℚ)^k * (1 + 2 * (w-k : ℕ) / d) + 2)^2 < p := by
  apply eligible hw hp q hprime ?_ hs hprod
  intro i hi heq
  exact five_excluded hres (heq ▸ hfactor i hi)

end A397683Threshold

end

section

namespace A397683Threshold
open Finset

/-- Increasing distinct prime-factor enumeration, extended by zero. -/
noncomputable def sortedFactors (n i : ℕ) : ℕ :=
  if hi : i < n.primeFactors.card then n.primeFactors.orderEmbOfFin rfl ⟨i, hi⟩ else 0

lemma sortedFactors_mem (n i : ℕ) (hi : i < n.primeFactors.card) :
    sortedFactors n i ∈ n.primeFactors := by
  simp only [sortedFactors, dif_pos hi]
  exact orderEmbOfFin_mem _ _ _

lemma sortedFactors_strict (n i j : ℕ) (hij : i < j) (hj : j < n.primeFactors.card) :
    sortedFactors n i < sortedFactors n j := by
  have hi : i < n.primeFactors.card := hij.trans hj
  simp only [sortedFactors, dif_pos hi, dif_pos hj]
  exact (n.primeFactors.orderEmbOfFin rfl).strictMono hij

lemma prod_sortedFactors (n : ℕ) :
    (∏ i ∈ range n.primeFactors.card, sortedFactors n i) = ∏ q ∈ n.primeFactors, q := by
  classical
  apply prod_bij (fun i _ => sortedFactors n i)
  · intro i hi
    exact sortedFactors_mem n i (mem_range.mp hi)
  · intro i hi j hj heq
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    simp only [sortedFactors, dif_pos hi', dif_pos hj'] at heq
    exact congrArg Fin.val ((n.primeFactors.orderEmbOfFin rfl).injective heq)
  · intro q hq
    let i := (n.primeFactors.orderIsoOfFin rfl).symm ⟨q, hq⟩
    refine ⟨i.val, mem_range.mpr i.isLt, ?_⟩
    simp only [sortedFactors, dif_pos i.isLt]
    change ↑(n.primeFactors.orderIsoOfFin rfl i) = q
    simp [i]
  · intro i _
    rfl

/-- Sieve eligibility directly from the actual distinct prime factors of p-1. -/
theorem primeFactors_eligible (p : ℕ) (hp : 260000 ≤ p)
    (hres : p % 20 = 3 ∨ p % 20 = 7) :
    ∃ k : ℕ, k ≤ (p-1).primeFactors.card ∧
      let w := (p-1).primeFactors.card
      let d : ℚ := 1 - 2 * ∑ i ∈ range w,
        if k ≤ i then (1 : ℚ) / sortedFactors (p-1) i else 0
      0 < d ∧ ((4 : ℚ)^k * (1 + 2 * (w-k : ℕ) / d) + 2)^2 < p := by
  have hw : 1 ≤ (p-1).primeFactors.card := by
    exact card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
  apply eligible_of_residue hw hp hres (sortedFactors (p-1))
  · intro i hi
    exact Nat.prime_of_mem_primeFactors (sortedFactors_mem _ _ hi)
  · intro i hi
    exact Nat.dvd_of_mem_primeFactors (sortedFactors_mem _ _ hi)
  · intro i j hij hj
    exact sortedFactors_strict _ _ _ hij hj
  · rw [prod_sortedFactors]
    exact lt_of_le_of_lt (Nat.le_of_dvd (by omega : 0 < p-1) (Nat.prod_primeFactors_dvd _))
      (by omega)

end A397683Threshold

end

section

namespace A397683Threshold
open Finset

noncomputable def factorCore (N k : ℕ) : Finset ℕ :=
  (range k).image (sortedFactors N)

noncomputable def factorTail (N k : ℕ) : Finset ℕ :=
  ((range N.primeFactors.card).filter (fun i => k ≤ i)).image (sortedFactors N)

lemma sortedFactors_inj {N i j : ℕ} (hi : i < N.primeFactors.card)
    (hj : j < N.primeFactors.card) (heq : sortedFactors N i = sortedFactors N j) : i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with hij | hji
  · exact (ne_of_lt (sortedFactors_strict N i j hij hj)) heq
  · exact (ne_of_lt (sortedFactors_strict N j i hji hi)) heq.symm

lemma factorCore_subset (N k : ℕ) (hk : k ≤ N.primeFactors.card) :
    factorCore N k ⊆ N.primeFactors := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
  exact sortedFactors_mem N i ((mem_range.mp hi).trans_le hk)

lemma factorTail_subset (N k : ℕ) : factorTail N k ⊆ N.primeFactors := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
  exact sortedFactors_mem N i (mem_range.mp (mem_filter.mp hi).1)

lemma factorCore_card (N k : ℕ) (hk : k ≤ N.primeFactors.card) :
    (factorCore N k).card = k := by
  unfold factorCore
  rw [card_image_iff.mpr ?_, card_range]
  intro i hi j hj heq
  exact sortedFactors_inj ((mem_range.mp hi).trans_le hk) ((mem_range.mp hj).trans_le hk) heq

lemma factorTail_card (N k : ℕ) : (factorTail N k).card = N.primeFactors.card-k := by
  have hset : (range N.primeFactors.card).filter (fun i => k ≤ i) = Ico k N.primeFactors.card := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  unfold factorTail
  rw [card_image_iff.mpr ?_, hset, Nat.card_Ico]
  intro i hi j hj heq
  exact sortedFactors_inj (mem_range.mp (mem_filter.mp hi).1)
    (mem_range.mp (mem_filter.mp hj).1) heq

lemma factorCore_disjoint_factorTail (N k : ℕ) (hk : k ≤ N.primeFactors.card) :
    Disjoint (factorCore N k) (factorTail N k) := by
  rw [disjoint_left]
  intro q hq ht
  obtain ⟨i,hi,hqi⟩ := mem_image.mp hq
  obtain ⟨j,hj,hqj⟩ := mem_image.mp ht
  have hi' := mem_range.mp hi
  obtain ⟨hj',hjk⟩ := mem_filter.mp hj
  have hji := sortedFactors_inj (hi'.trans_le hk) (mem_range.mp hj') (hqi.trans hqj.symm)
  omega

lemma factorCore_union_factorTail (N k : ℕ) (hk : k ≤ N.primeFactors.card) :
    factorCore N k ∪ factorTail N k = N.primeFactors := by
  apply Subset.antisymm
  · exact union_subset (factorCore_subset N k hk) (factorTail_subset N k)
  · intro q hq
    let i := (N.primeFactors.orderIsoOfFin rfl).symm ⟨q,hq⟩
    have hqi : sortedFactors N i.val = q := by
      simp only [sortedFactors, dif_pos i.isLt]
      change ↑(N.primeFactors.orderIsoOfFin rfl i) = q
      simp [i]
    by_cases hi : i.val < k
    · exact mem_union_left _ (mem_image.mpr ⟨i.val, mem_range.mpr hi, hqi⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨i.val,
        mem_filter.mpr ⟨mem_range.mpr i.isLt, by omega⟩,hqi⟩)

lemma factorCore_prime (N k q : ℕ) (hk : k ≤ N.primeFactors.card)
    (hq : q ∈ factorCore N k) : q.Prime :=
  Nat.prime_of_mem_primeFactors (factorCore_subset N k hk hq)

lemma factorTail_prime (N k q : ℕ) (hq : q ∈ factorTail N k) : q.Prime :=
  Nat.prime_of_mem_primeFactors (factorTail_subset N k hq)

/-- Reindex any tail sum from its actual factors to the sorted coordinates. -/
lemma factorTail_sum {R : Type*} [AddCommMonoid R] (N k : ℕ) (f : ℕ → R) :
    (∑ q ∈ factorTail N k, f q) =
      ∑ i ∈ range N.primeFactors.card, if k ≤ i then f (sortedFactors N i) else 0 := by
  classical
  unfold factorTail
  rw [sum_image]
  · exact sum_filter _ _
  · intro i hi j hj heq
    exact sortedFactors_inj (mem_range.mp (mem_filter.mp hi).1)
      (mem_range.mp (mem_filter.mp hj).1) heq

/-- Exact bridge from the checked rational delta to the real character sieve. -/
lemma factorTail_delta_real (N k : ℕ) :
    ((1 - 2 * ∑ i ∈ range N.primeFactors.card,
      if k ≤ i then (1 : ℚ) / sortedFactors N i else 0 : ℚ) : ℝ) =
      1 - 2 * ∑ q ∈ factorTail N k, (1 : ℝ) / q := by
  rw [factorTail_sum]
  push_cast
  simp only [apply_ite, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_zero]

/-- The exact arithmetic threshold in the real-valued finite-set form used by
the character sieve. -/
theorem primeFactors_real_eligible (p : ℕ) (hp : 260000 ≤ p)
    (hres : p % 20 = 3 ∨ p % 20 = 7) :
    ∃ k : ℕ, k ≤ (p-1).primeFactors.card ∧
      let d : ℝ := 1 - 2 * ∑ q ∈ factorTail (p-1) k, (1 : ℝ) / q
      0 < d ∧
        ((4 : ℝ) ^ (factorCore (p-1) k).card *
          (1 + 2 * ((factorTail (p-1) k).card : ℝ) / d) + 2)^2 < p := by
  obtain ⟨k,hk,hd,hbound⟩ := primeFactors_eligible p hp hres
  refine ⟨k,hk,?_⟩
  dsimp only
  rw [factorCore_card _ _ hk, factorTail_card, ← factorTail_delta_real]
  constructor
  · exact_mod_cast hd
  · exact_mod_cast hbound

end A397683Threshold

end

section

/-! Known prime-pair constructions adapted from OMA PR30020,
credit PanPapag's reciprocal witnesses and finite certificates, Ciphore's
original reduction, and the published Codex reduction author. The reflection
and even-order interfaces below are new integration lemmas. -/
namespace A397683GoodPrimes

namespace QuarterPair

theorem pair {p : ℕ} (hp : p.Prime) (hr : p % 4 = 1) :
    ∃ x : ZMod p, x ≠ 0 ∧ x+1 ≠ 0 ∧ 4 ∣ orderOf x ∧ orderOf x = orderOf (x+1) := by
  let : Fact p.Prime := ⟨hp⟩
  have ht : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (CharP.cast_eq_zero_iff (ZMod p) p 2).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by have := hp.two_le; omega))
  have hm : (-1 : ZMod p) ≠ 1 := by intro h; apply ht; linear_combination -h
  by_cases hd : 4 ∣ orderOf (2 : ZMod p)
  · let v : ZMod p := 2⁻¹
    have hv : -v+1 = v := by dsimp [v]; field_simp; ring
    refine ⟨-v, neg_ne_zero.mpr (inv_ne_zero ht), by rw [hv]; exact inv_ne_zero ht, ?_⟩
    rw [hv]
    have hvd : 4 ∣ orderOf v := by
      let u := Units.mk0 (2 : ZMod p) ht
      change 4 ∣ orderOf (↑u⁻¹ : ZMod p)
      rw [orderOf_units, orderOf_inv, ← orderOf_units]
      exact hd
    have hdiv : orderOf v ∣ 2 * orderOf (-v) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, show v^2 = (-v)^2 by ring, ← pow_mul, Nat.mul_comm, pow_mul,
        pow_orderOf_eq_one, one_pow]
    have h := hvd.trans hdiv
    have e : Even (orderOf (-v)) := ⟨orderOf (-v)/2, by omega⟩
    have e' : Even (orderOf v) := ⟨orderOf v/2, by omega⟩
    have eq : orderOf (-v) = orderOf v := by
      apply Nat.dvd_antisymm
      · apply orderOf_dvd_of_pow_eq_one
        rw [e'.neg_pow, pow_orderOf_eq_one]
      · apply orderOf_dvd_of_pow_eq_one
        simpa only [e.neg_pow] using pow_orderOf_eq_one (-v)
    exact ⟨by rwa [eq], eq⟩
  obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3))
  have hi' : i^2 = -1 := by simpa [pow_two] using hi.symm
  let x := (i-1)/2
  let y := (i+1)/2
  have he : x+1 = y := by dsimp [x,y]; field_simp; ring
  have fourth (z : ZMod p) (hz : z = x ∨ z = y) : z^4*4 = -1 := by
    rcases hz with rfl|rfl
    · dsimp [x]; field_simp; linear_combination (4*i^2-16*i+20)*hi'
    · dsimp [y]; field_simp; linear_combination (4*i^2+16*i+20)*hi'
  let d := orderOf (2 : ZMod p)
  obtain ⟨k,hk,hdk⟩ : ∃ k : ℕ, Odd k ∧ d ∣ 2*k := by
    change ¬4 ∣ d at hd
    by_cases hh : 2 ∣ d
    · exact ⟨d/2, ⟨d/4, by omega⟩, by simpa only [Nat.mul_div_cancel' hh] using (dvd_refl d)⟩
    · exact ⟨d, ⟨d/2, by omega⟩, dvd_mul_left _ _⟩
  have h4 : (4 : ZMod p)^k = 1 := by
    rw [show (4 : ZMod p) = 2^2 by norm_num, ← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp hdk
  have ord (z : ZMod p) (hz : z = x ∨ z = y) : 4 ∣ orderOf z := by
    have hh := congrArg (fun v : ZMod p => v^k) (fourth z hz)
    simp only [mul_pow, h4, mul_one, hk.neg_one_pow] at hh
    rw [← pow_mul, Nat.mul_comm, pow_mul] at hh
    have eight : orderOf (z^k) = 2^(2+1) := by
      apply orderOf_eq_prime_pow (p := 2) (n := 2)
      · change (z^k)^4 ≠ 1; rw [hh]; exact hm
      · change (z^k)^8 = 1
        rw [show 8 = 4*2 by decide, pow_mul, hh]; norm_num
    exact (show 4 ∣ 8 by decide).trans (by rw [← show orderOf (z^k) = 8 from eight]; exact orderOf_pow_dvd k)
  have nx (z : ZMod p) (hz : z = x ∨ z = y) : z ≠ 0 := by
    intro h
    simpa [h] using fourth z hz
  refine ⟨x,nx x (.inl rfl), by rw [he]; exact nx y (.inr rfl), ord x (.inl rfl), ?_⟩
  rw [he]
  have hxy : x^4 = y^4 := by
    apply mul_right_cancel₀ (show (4 : ZMod p) ≠ 0 by convert mul_ne_zero ht ht using 1; norm_num)
    rw [fourth x (.inl rfl), fourth y (.inr rfl)]
  have eq := congrArg orderOf hxy
  rw [orderOf_pow_of_dvd (by decide) (ord x (.inl rfl)), orderOf_pow_of_dvd (by decide) (ord y (.inr rfl))] at eq
  have := ord x (.inl rfl)
  have := ord y (.inr rfl)
  omega
end QuarterPair


namespace SmallPrimePairs
private def witness : ℕ → ℕ × ℕ
  | 5 => (2, 4)
  | 11 => (3, 5)
  | 13 => (6, 12)
  | 17 => (8, 8)
  | 19 => (4, 9)
  | 23 => (2, 11)
  | 29 => (23, 7)
  | 31 => (9, 15)
  | 37 => (33, 9)
  | 41 => (20, 20)
  | 43 => (9, 21)
  | 47 => (2, 23)
  | 53 => (15, 13)
  | 59 => (3, 29)
  | 61 => (15, 15)
  | 67 => (14, 11)
  | 71 => (2, 35)
  | 73 => (13, 72)
  | 79 => (21, 13)
  | 83 => (3, 41)
  | 89 => (9, 44)
  | 97 => (19, 32)
  | 101 => (24, 25)
  | 103 => (8, 17)
  | 107 => (3, 53)
  | 109 => (21, 27)
  | 113 => (56, 28)
  | 127 => (17, 63)
  | 131 => (62, 13)
  | 137 => (59, 17)
  | 139 => (44, 23)
  | 149 => (5, 37)
  | 151 => (123, 25)
  | 157 => (7, 52)
  | 163 => (21, 27)
  | 167 => (2, 83)
  | _ => (0, 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem cert : ∀ i : Fin 170, i.val.Prime → i.val ≠ 2 → i.val ≠ 3 → i.val ≠ 7 →
    let (x,d) := witness i.val
    1 ≤ x ∧ x+1 < i.val ∧ 0 < d ∧
    ((x : ZMod i.val)^d = 1 ∧ ∀ j : Fin d, 0 < j.val → (x : ZMod i.val)^j.val ≠ 1) ∧
    (((x+1 : ℕ) : ZMod i.val)^d = 1 ∧ ∀ j : Fin d, 0 < j.val → ((x+1 : ℕ) : ZMod i.val)^j.val ≠ 1) := by
  decide

theorem small {p : ℕ} (hp : p.Prime) (hb : p < 170) (h2 : p ≠ 2) (h3 : p ≠ 3) (h7 : p ≠ 7) :
    ∃ x d : ℕ, 1 ≤ x ∧ x+1 < p ∧ d ≠ 0 ∧ orderOf (x : ZMod p) = d ∧
      orderOf ((x+1 : ℕ) : ZMod p) = d := by
  have h := cert ⟨p,hb⟩ hp h2 h3 h7
  generalize he : witness p = w
  obtain ⟨x,d⟩ := w
  simp only at h
  rw [he] at h
  obtain ⟨hx,hp',hd,⟨ha,ha'⟩,hb',hb''⟩ := h
  exact ⟨x,d,hx,hp',hd.ne', (orderOf_eq_iff hd).mpr ⟨ha,fun m hm => ha' ⟨m,hm⟩⟩,
    (orderOf_eq_iff hd).mpr ⟨hb',fun m hm => hb'' ⟨m,hm⟩⟩⟩
end SmallPrimePairs


theorem reciprocalRootPrime {p : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hr : p % 5 = 1 ∨ p % 5 = 4) : ∃ x : ZMod p, x*(x+1)=1 := by
  let : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h5 : IsSquare (p : ZMod 5) := by
    rw [← ZMod.natCast_mod p 5]
    rcases hr with h | h <;> rw [h]
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
  obtain ⟨s, hs⟩ := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by decide) ho).mp h5
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (CharP.cast_eq_zero_iff (ZMod p) p 2).not.mpr (fun h => ho ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
  refine ⟨(s-1)/2, ?_⟩
  field_simp
  push_cast at hs
  linear_combination -hs



/-- Negation doubles an odd multiplicative order in an odd prime field. -/
theorem odd_order_neg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x : ZMod p) (ho : Odd (orderOf x)) :
    orderOf (-x) = 2 * orderOf x := by
  let : Fact p.Prime := ⟨hp⟩
  rw [neg_eq_neg_one_mul, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
  · simp [orderOf_neg_one, ringChar.eq (ZMod p) p, hp2]
  · simp [orderOf_neg_one, ringChar.eq (ZMod p) p, hp2, ho]

/-- Reflecting an odd-order adjacent pair makes both orders even. -/
theorem evenize {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x : ZMod p) (hx : x ≠ 0) (hy : x+1 ≠ 0)
    (he : orderOf x = orderOf (x+1)) :
    ∃ y : ZMod p, y ≠ 0 ∧ y+1 ≠ 0 ∧
      orderOf y = orderOf (y+1) ∧ 2 ∣ orderOf y := by
  by_cases hd : Even (orderOf x)
  · exact ⟨x, hx, hy, he, even_iff_two_dvd.mp hd⟩
  have ho : Odd (orderOf x) := Nat.not_even_iff_odd.mp hd
  have ho' : Odd (orderOf (x+1)) := he ▸ ho
  refine ⟨-x-1, ?_, ?_, ?_, ?_⟩
  · simpa only [show -x-1 = -(x+1) by ring, ne_eq, neg_eq_zero] using hy
  · simpa only [sub_add_cancel, ne_eq, neg_eq_zero] using hx
  · rw [show (-x-1)+1 = -x by ring, show -x-1 = -(x+1) by ring]
    rw [odd_order_neg hp hp2 (x+1) ho', odd_order_neg hp hp2 x ho, he]
  · rw [show -x-1 = -(x+1) by ring, odd_order_neg hp hp2 (x+1) ho']
    exact dvd_mul_right 2 _

/-- Reciprocal pairs have equal multiplicative orders. -/
theorem reciprocal_pair {p : ℕ} (hp : p.Prime) (x : ZMod p) (h : x*(x+1)=1) :
    x ≠ 0 ∧ x+1 ≠ 0 ∧ orderOf x = orderOf (x+1) := by
  let : Fact p.Prime := ⟨hp⟩
  let u : (ZMod p)ˣ := ⟨x,x+1,h,by rwa [mul_comm]⟩
  have hx : x ≠ 0 := by intro hz; simp [hz] at h
  have hy : x+1 ≠ 0 := by intro hz; simp [hz] at h
  refine ⟨hx, hy, ?_⟩
  change orderOf (u : ZMod p) = orderOf ((u⁻¹ : (ZMod p)ˣ) : ZMod p)
  rw [orderOf_units, orderOf_units, orderOf_inv]

/-- All nonexceptional odd primes below170 have an even-order adjacent pair. -/
theorem small_even_pair {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hp7 : p ≠ 7) (hb : p < 170) :
    ∃ x : ZMod p, x ≠ 0 ∧ x+1 ≠ 0 ∧
      orderOf x = orderOf (x+1) ∧ 2 ∣ orderOf x := by
  obtain ⟨x,d,hx,hxp,hd,he,he'⟩ := SmallPrimePairs.small hp hb hp2 hp3 hp7
  apply evenize hp hp2 (x : ZMod p)
  · intro h
    have hh := (ZMod.natCast_eq_zero_iff x p).mp h
    exact Nat.not_dvd_of_pos_of_lt hx (by omega) hh
  · intro h
    have hh : p ∣ x+1 := (ZMod.natCast_eq_zero_iff (x+1) p).mp (by simpa using h)
    exact Nat.not_dvd_of_pos_of_lt (by omega) hxp hh
  · simpa only [Nat.cast_add, Nat.cast_one] using he.trans he'.symm

/-- The already elementary residue classes have an even-order adjacent pair. -/
theorem outside_even_pair {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ho : Odd p) (hres : ¬ (p % 20 = 3 ∨ p % 20 = 7)) :
    ∃ x : ZMod p, x ≠ 0 ∧ x+1 ≠ 0 ∧
      orderOf x = orderOf (x+1) ∧ 2 ∣ orderOf x := by
  by_cases h4 : p % 4 = 1
  · obtain ⟨x,hx,hy,hd,he⟩ := QuarterPair.pair hp h4
    exact ⟨x,hx,hy,he,(by decide : 2 ∣ 4).trans hd⟩
  by_cases h5 : p % 5 = 1 ∨ p % 5 = 4
  · obtain ⟨x,hx⟩ := reciprocalRootPrime hp hp2 h5
    obtain ⟨ha,hb,he⟩ := reciprocal_pair hp x hx
    exact evenize hp hp2 x ha hb he
  have h50 : p % 5 ≠ 0 := by
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hp).mp
      (Nat.dvd_of_mod_eq_zero h)
    have : p = 5 := he.symm
    subst p
    norm_num at h4
  have hmod (k : ℕ) (hk : k ∣ 20) : (p % 20) % k = p % k :=
    Nat.mod_mod_of_dvd p hk
  have h₄ := hmod 4 (by decide)
  have h₅ := hmod 5 (by decide)
  have h₂ := hmod 2 (by decide)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ho
  have hb := Nat.mod_lt p (by decide : 0 < 20)
  apply (hres ?_).elim
  generalize p % 20 = r at *
  interval_cases r <;> norm_num at * <;> omega

/-- Unit-valued interface for the lifting and CRT assembly. -/
theorem even_pair_units {p : ℕ} (hp : p.Prime)
    (h : ∃ x : ZMod p, x ≠ 0 ∧ x+1 ≠ 0 ∧
      orderOf x = orderOf (x+1) ∧ 2 ∣ orderOf x) :
    ∃ x : ZMod p, IsUnit x ∧ IsUnit (x+1) ∧
      orderOf x = orderOf (x+1) ∧ 2 ∣ orderOf x := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx,hy,he,hd⟩ := h
  exact ⟨x, isUnit_iff_ne_zero.mpr hx, isUnit_iff_ne_zero.mpr hy, he, hd⟩

/-- Assemble the elementary cases with the two remaining residue classes. -/
theorem assemble_prime_pair
    (remaining : ∀ p : ℕ, p.Prime → Odd p → 170 ≤ p →
      (p % 20 = 3 ∨ p % 20 = 7) →
      ∃ x : ZMod p, x ≠ 0 ∧ x+1 ≠ 0 ∧
        orderOf x = orderOf (x+1) ∧ 2 ∣ orderOf x)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp3 : p ≠ 3) (hp7 : p ≠ 7) :
    ∃ x : ZMod p, IsUnit x ∧ IsUnit (x+1) ∧
      orderOf x = orderOf (x+1) ∧ 2 ∣ orderOf x := by
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨j,hj⟩ := ho; omega
  apply even_pair_units hp
  by_cases hb : p < 170
  · exact small_even_pair hp hp2 hp3 hp7 hb
  · by_cases hres : p % 20 = 3 ∨ p % 20 = 7
    · exact remaining p hp ho (by omega) hres
    · exact outside_even_pair hp hp2 ho hres

end A397683GoodPrimes

end

section

-- Checked component bodies for concatenation after import OMAStatements.S_oeis_a397683.
-- Characters.lean is intentionally omitted. No local imports are required.


section TensorBudgetLegacy

open Finset
noncomputable section
namespace A397683Tensor

/-- Local density of elements free from one prime divisor. -/
def theta (r : ℕ) : ℝ := (r - 1 : ℝ) / r

/-- A principal term, followed by the r-1 nonprincipal terms of the r-projector. -/
def coefficient (r : ℕ) : Option (Fin (r - 1)) → ℝ
  | none => theta r
  | some _ => -(1 / (r : ℝ))

@[simp] theorem coefficient_none (r : ℕ) : coefficient r none = theta r := rfl
@[simp] theorem coefficient_some (r : ℕ) (j : Fin (r - 1)) :
    coefficient r (some j) = -(1 / (r : ℝ)) := rfl

theorem theta_nonneg {r : ℕ} (hr : 1 ≤ r) : 0 ≤ theta r := by
  exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hr)) (Nat.cast_nonneg r)

/-- The crucial normalized local L1 budget: exactly twice the local density. -/
theorem coefficient_l1 (r : ℕ) (hr : 1 ≤ r) :
    (∑ j : Option (Fin (r - 1)), |coefficient r j|) = 2 * theta r := by
  rw [Fintype.sum_option]
  simp only [coefficient_none, coefficient_some, abs_of_nonneg (theta_nonneg hr), abs_neg,
    abs_div, abs_one, abs_of_nonneg (show (0 : ℝ) ≤ r from Nat.cast_nonneg r), sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_sub hr, Nat.cast_one]
  unfold theta
  ring

/-- Tensor weights on choices of the local principal/nonprincipal index. -/
def tensorCoefficient {ι : Type*} [Fintype ι] (r : ι → ℕ)
    (j : ∀ i, Option (Fin (r i - 1))) : ℝ := ∏ i, coefficient (r i) (j i)

/-- The all-principal coefficient is exactly the product of local densities. -/
theorem tensor_principal {ι : Type*} [Fintype ι] (r : ι → ℕ) :
    tensorCoefficient r (fun _ => none) = ∏ i, theta (r i) := by
  simp only [tensorCoefficient, coefficient_none]

/-- The full tensor has the sharp theta(e) W(e) coefficient budget. -/
theorem tensor_l1 {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (hr : ∀ i, 1 ≤ r i) :
    (∑ j : ∀ i, Option (Fin (r i - 1)), |tensorCoefficient r j|) =
      (∏ i, theta (r i)) * 2 ^ Fintype.card ι := by
  classical
  simp only [tensorCoefficient, abs_prod]
  rw [← Fintype.prod_sum (fun i (j : Option (Fin (r i - 1))) => |coefficient (r i) j|)]
  simp_rw [coefficient_l1 _ (hr _)]
  rw [prod_mul_distrib]
  simp only [prod_const, card_univ]
  exact mul_comm _ _

/-- Coprime component orders multiply in a finite product. -/
theorem orderOf_prod_of_pairwise_coprime {ι G : Type*} [CommGroup G]
    (s : Finset ι) (f : ι → G)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (orderOf (f i)) (orderOf (f j))) :
    orderOf (∏ i ∈ s, f i) = ∏ i ∈ s, orderOf (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have htail : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime (orderOf (f a)) (orderOf (f b)) := by
      intro a ha b hb hab
      exact hc a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab
    rw [prod_insert hi, prod_insert hi,
      (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
    · rw [ih htail]
    · rw [ih htail, Nat.coprime_prod_right_iff]
      intro j hj
      exact hc i (mem_insert_self _ _) j (mem_insert_of_mem hj) (ne_of_mem_of_not_mem hj hi).symm

/-- With coprime orders, a trivial product forces every component to be trivial. -/
theorem coprime_product_eq_one_iff {ι G : Type*} [CommGroup G]
    (s : Finset ι) (f : ι → G)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (orderOf (f i)) (orderOf (f j))) :
    (∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1 := by
  classical
  rw [← orderOf_eq_one_iff, orderOf_prod_of_pairwise_coprime s f hc]
  have hall : (∏ i ∈ s, orderOf (f i)) = 1 ↔ ∀ i ∈ s, orderOf (f i) = 1 := by
    constructor
    · intro h i hi
      apply Nat.eq_one_of_dvd_one
      rw [← h]
      exact dvd_prod_of_mem (fun j => orderOf (f j)) hi
    · exact fun h => prod_eq_one h
  rw [hall]
  simp only [orderOf_eq_one_iff]

/-- The character selected by one principal/nonprincipal local index. -/
def localCharacter {M : Type*} [CommMonoid M] (χ : MulChar M ℂ) (r : ℕ) :
    Option (Fin (r - 1)) → MulChar M ℂ
  | none => 1
  | some j => χ ^ (j.val + 1)

/-- Every local character has order dividing its assigned prime. -/
theorem localCharacter_order_dvd {M : Type*} [CommMonoid M]
    (χ : MulChar M ℂ) (r : ℕ) (hχ : orderOf χ = r)
    (j : Option (Fin (r - 1))) : orderOf (localCharacter χ r j) ∣ r := by
  cases j with
  | none => simp only [localCharacter, orderOf_one, one_dvd]
  | some j => simpa only [localCharacter, hχ] using (orderOf_pow_dvd (x := χ) (j.val + 1))

/-- At prime order, every nonprincipal local index is genuinely nontrivial. -/
theorem localCharacter_eq_one_iff {M : Type*} [CommMonoid M]
    (χ : MulChar M ℂ) (r : ℕ) (hr : r.Prime) (hχ : orderOf χ = r)
    (j : Option (Fin (r - 1))) : localCharacter χ r j = 1 ↔ j = none := by
  cases j with
  | none => simp [localCharacter]
  | some j =>
    have hj : j.val + 1 < r := by have := j.isLt; omega
    have hc : (orderOf χ).Coprime (j.val + 1) := by
      rw [hχ]
      exact hr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) hj)
    have ho : orderOf (χ ^ (j.val + 1)) = r := hc.orderOf_pow.trans hχ
    simp only [localCharacter, reduceCtorEq, iff_false]
    intro h
    have he := congrArg orderOf h
    rw [ho, orderOf_one] at he
    exact hr.ne_one he

/-- The all-principal tensor index is the only trivial character product. -/
theorem tensor_character_eq_one_iff {ι M : Type*} [Fintype ι] [CommMonoid M]
    (r : ι → ℕ) (χ : ι → MulChar M ℂ)
    (hr : ∀ i, (r i).Prime) (hχ : ∀ i, orderOf (χ i) = r i)
    (hc : ∀ i j, i ≠ j → Nat.Coprime (r i) (r j))
    (j : ∀ i, Option (Fin (r i - 1))) :
    (∏ i, localCharacter (χ i) (r i) (j i)) = 1 ↔ ∀ i, j i = none := by
  classical
  have hp : ∀ i ∈ (univ : Finset ι), ∀ k ∈ (univ : Finset ι), i ≠ k →
      Nat.Coprime (orderOf (localCharacter (χ i) (r i) (j i)))
        (orderOf (localCharacter (χ k) (r k) (j k))) := by
    intro i _ k _ hik
    exact (hc i k hik).of_dvd
      (localCharacter_order_dvd (χ i) (r i) (hχ i) (j i))
      (localCharacter_order_dvd (χ k) (r k) (hχ k) (j k))
  rw [coprime_product_eq_one_iff _ _ hp]
  simp only [mem_univ, forall_const, localCharacter_eq_one_iff _ _ (hr _) (hχ _)]

/-- The budgeted local coefficient vector is the actual prime-free projector. -/
theorem local_factor_value {M : Type*} [CommMonoid M]
    (χ : MulChar M ℂ) (r : ℕ) (hr : 1 ≤ r) (hχ : χ ^ r = 1) (x : Mˣ) :
    (∑ j : Option (Fin (r - 1)), (coefficient r j : ℂ) *
      localCharacter χ r j (x : M)) = if χ (x : M) = 1 then 0 else 1 := by
  classical
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hr)
  have ht : (theta r : ℂ) = 1 - 1 / (r : ℂ) := by
    simp only [theta, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast,
      Complex.ofReal_one]
    rw [sub_div, div_self hr0]
  have hp : χ (x : M) ^ r = 1 := by
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using
      congrArg (fun ψ : MulChar M ℂ => ψ (x : M)) hχ
  have hk : (∑ j ∈ range r, χ (x : M) ^ j) =
      if χ (x : M) = 1 then (r : ℂ) else 0 := by
    by_cases hx : χ (x : M) = 1
    · simp [hx]
    · rw [if_neg hx]
      have hh := geom_sum_mul (χ (x : M)) r
      rw [hp, sub_self] at hh
      exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hx)
  have hs : (∑ j : Fin (r - 1), χ (x : M) ^ (j.val + 1)) + 1 =
      if χ (x : M) = 1 then (r : ℂ) else 0 := by
    rw [← Finset.sum_range (n := r - 1) (fun j => χ (x : M) ^ (j + 1))]
    have hh := sum_range_succ' (fun j => χ (x : M) ^ j) (r - 1)
    rw [Nat.sub_add_cancel hr, pow_zero, hk] at hh
    exact hh.symm
  rw [Fintype.sum_option]
  simp only [coefficient_none, coefficient_some, localCharacter, MulChar.one_apply_coe,
    MulChar.pow_apply_coe, mul_one, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast]
  rw [ht, ← mul_sum]
  by_cases hx : χ (x : M) = 1
  · rw [if_pos hx] at hs ⊢
    have hd : (1 / (r : ℂ)) * r = 1 := one_div_mul_cancel hr0
    linear_combination -(1 / (r : ℂ)) * hs - hd
  · rw [if_neg hx] at hs ⊢
    linear_combination -(1 / (r : ℂ)) * hs

/-- The tensor weights expand the product of the actual local projectors. -/
theorem tensor_expansion {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (r : ι → ℕ) (χ : ι → MulChar M ℂ) (x : Mˣ) :
    (∏ i, ∑ j : Option (Fin (r i - 1)), (coefficient (r i) j : ℂ) *
      localCharacter (χ i) (r i) j (x : M)) =
    ∑ j : ∀ i, Option (Fin (r i - 1)), (tensorCoefficient r j : ℂ) *
      (∏ i, localCharacter (χ i) (r i) (j i)) (x : M) := by
  classical
  let ev : MulChar M ℂ →* ℂ :=
    { toFun := fun ψ => ψ (x : M)
      map_one' := MulChar.one_apply_coe x
      map_mul' := fun ψ η => MulChar.mul_apply ψ η (x : M) }
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro j _
  have he : (∏ i, localCharacter (χ i) (r i) (j i)) (x : M) =
      ∏ i, localCharacter (χ i) (r i) (j i) (x : M) := by
    exact map_prod ev _ _
  rw [he, tensorCoefficient]
  have hcast : ((∏ i, coefficient (r i) (j i) : ℝ) : ℂ) =
      ∏ i, (coefficient (r i) (j i) : ℂ) := map_prod Complex.ofRealHom _ _
  rw [hcast, prod_mul_distrib]

/-- The expanded tensor is the simultaneous kernel-avoidance indicator on units. -/
theorem tensor_indicator {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (r : ι → ℕ) (χ : ι → MulChar M ℂ) (hr : ∀ i, 1 ≤ r i)
    (hχ : ∀ i, χ i ^ r i = 1) (x : Mˣ) :
    (∑ j : ∀ i, Option (Fin (r i - 1)), (tensorCoefficient r j : ℂ) *
      (∏ i, localCharacter (χ i) (r i) (j i)) (x : M)) =
      if ∀ i, χ i (x : M) ≠ 1 then 1 else 0 := by
  classical
  rw [← tensor_expansion r χ x]
  simp_rw [local_factor_value _ _ (hr _) (hχ _) x]
  by_cases h : ∀ i, χ i (x : M) ≠ 1
  · simp only [if_neg (h _), prod_const_one, if_pos h]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    apply prod_eq_zero (mem_univ i)
    exact if_pos hi

/-- The all-field-element expansion vanishes at zero, even for an empty prime tensor. -/
theorem tensor_at_zero {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (r : ι → ℕ) (χ : ι → MulChar F ℂ) :
    (∑ j : ∀ i, Option (Fin (r i - 1)), (tensorCoefficient r j : ℂ) *
      (∏ i, localCharacter (χ i) (r i) (j i)) (0 : F)) = 0 := by
  have h0 (ψ : MulChar F ℂ) : ψ 0 = 0 := ψ.map_nonunit not_isUnit_zero
  simp only [h0, mul_zero, sum_const_zero]

end A397683Tensor


end -- noncomputable section


end TensorBudgetLegacy


section JacobiBoundsLegacy

open Finset
namespace A397683Characters

/-- Consecutive-argument character correlations are signed Jacobi sums. -/
theorem consecutive_character_sum {F R : Type*} [CommRing F] [Fintype F]
    [CommRing R] (χ ψ : MulChar F R) :
    (∑ x : F, χ x * ψ (x + 1)) = χ (-1) * jacobiSum χ ψ := by
  classical
  calc
    _ = ∑ x : F, χ (-x) * ψ (-x + 1) := (Equiv.sum_comp (Equiv.neg F) _).symm
    _ = χ (-1) * jacobiSum χ ψ := by
      rw [jacobiSum, mul_sum]
      apply sum_congr rfl
      intro x _
      have hn : χ (-x) = χ (-1) * χ x := by rw [← neg_one_mul x, map_mul]
      rw [hn, show -x + 1 = 1 - x by rw [sub_eq_add_neg, add_comm]]
      exact mul_assoc _ _ _

/-- Complex conjugation inverts both multiplicative characters. -/
theorem star_jacobiSum {F : Type*} [CommRing F] [Fintype F]
    (χ ψ : MulChar F ℂ) : star (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
  simp only [jacobiSum, star_sum, star_mul, MulChar.star_apply', mul_comm]

/-- The sharp squared Jacobi norm in the generic, nontrivial case. -/
theorem jacobiSum_normSq {F : Type*} [Field F] [Fintype F]
    (χ ψ : MulChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    Complex.normSq (jacobiSum χ ψ) = (Fintype.card F : ℝ) := by
  have hc : ringChar ℂ ≠ ringChar F := by
    simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm
  have hm := jacobiSum_mul_jacobiSum_inv hc hχ hψ hχψ
  rw [← star_jacobiSum] at hm
  have hm' : (Complex.normSq (jacobiSum χ ψ) : ℂ) = (Fintype.card F : ℂ) := by
    simpa only [Complex.star_def, Complex.mul_conj] using hm
  exact_mod_cast hm'

/-- The generic Jacobi correlation has the exact square-root bound. -/
theorem jacobiSum_norm {F : Type*} [Field F] [Fintype F]
    (χ ψ : MulChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    ‖jacobiSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [Complex.norm_def, jacobiSum_normSq χ ψ hχ hψ hχψ]

/-- Every character has norm one at a unit, including the trivial character. -/
theorem character_norm_at_unit {M : Type*} [CommMonoid M] [Fintype Mˣ]
    (χ : MulChar M ℂ) (x : Mˣ) : ‖χ (x : M)‖ = 1 := by
  have hp : χ (x : M) ^ Fintype.card Mˣ = 1 := by
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using
      congrArg (fun ψ : MulChar M ℂ => ψ (x : M)) χ.pow_card_eq_one
  exact Complex.norm_eq_one_of_pow_eq_one hp Fintype.card_ne_zero

/-- All Jacobi terms other than the double-principal term have norm at most sqrt(q). -/
theorem jacobiSum_norm_le {F : Type*} [Field F] [Fintype F]
    (χ ψ : MulChar F ℂ) (hn : χ ≠ 1 ∨ ψ ≠ 1) :
    ‖jacobiSum χ ψ‖ ≤ Real.sqrt (Fintype.card F : ℝ) := by
  classical
  have hcard : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero : 1 ≤ Fintype.card F)
  have hsq : (1 : ℝ) ≤ Real.sqrt (Fintype.card F : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hcard
  by_cases hχ : χ = 1
  · have hψ : ψ ≠ 1 := hn.resolve_left (not_not.mpr hχ)
    rw [hχ, jacobiSum_one_nontrivial hψ, norm_neg, norm_one]
    exact hsq
  by_cases hψ : ψ = 1
  · rw [hψ, jacobiSum_comm, jacobiSum_one_nontrivial hχ, norm_neg, norm_one]
    exact hsq
  by_cases hp : χ * ψ = 1
  · have hi : ψ = χ⁻¹ := eq_inv_of_mul_eq_one_right hp
    rw [hi, jacobiSum_nontrivial_inv hχ, norm_neg]
    have hnχ : ‖χ (-1)‖ = 1 := by
      simpa only [Units.val_neg, Units.val_one] using character_norm_at_unit χ (-1 : Fˣ)
    rw [hnχ]
    exact hsq
  · rw [jacobiSum_norm χ ψ hχ hψ hp]

/-- The same square-root bound applies to consecutive-argument correlations. -/
theorem consecutive_character_sum_norm_le {F : Type*} [Field F] [Fintype F]
    (χ ψ : MulChar F ℂ) (hn : χ ≠ 1 ∨ ψ ≠ 1) :
    ‖∑ x : F, χ x * ψ (x + 1)‖ ≤ Real.sqrt (Fintype.card F : ℝ) := by
  classical
  rw [consecutive_character_sum, norm_mul]
  have hnχ : ‖χ (-1)‖ = 1 := by
    simpa only [Units.val_neg, Units.val_one] using character_norm_at_unit χ (-1 : Fˣ)
  rw [hnχ, one_mul]
  exact jacobiSum_norm_le χ ψ hn

/-- The double-principal term supplies the exact main term q-2. -/
theorem consecutive_principal_sum {F : Type*} [Field F] [Fintype F] :
    (∑ x : F, (1 : MulChar F ℂ) x * (1 : MulChar F ℂ) (x + 1)) =
      (Fintype.card F : ℂ) - 2 := by
  rw [consecutive_character_sum, jacobiSum_one_one]
  rw [MulChar.one_apply (isUnit_neg_one), one_mul]

/-- Any finite character expansion of a pair count reduces exactly to Jacobi sums. -/
theorem weighted_consecutive_expansion {F ι κ : Type*} [CommRing F] [Fintype F]
    [Fintype ι] [Fintype κ] (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ)
    (a : ι → ℂ) (b : κ → ℂ) :
    (∑ x : F, (∑ i, a i * χ i x) * (∑ j, b j * ψ j (x + 1))) =
      ∑ i, ∑ j, (a i * b j) * (χ i (-1) * jacobiSum (χ i) (ψ j)) := by
  classical
  calc
    _ = ∑ x : F, ∑ i, ∑ j, (a i * b j) * (χ i x * ψ j (x + 1)) := by
      apply sum_congr rfl
      intro x _
      simp only [sum_mul, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ac_rfl
    _ = ∑ i, ∑ j, ∑ x : F, (a i * b j) * (χ i x * ψ j (x + 1)) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = _ := by simp_rw [← mul_sum, consecutive_character_sum]

/-- Triangle bound for any collection of off-principal character pairs. -/
theorem weighted_off_principal_bound {F ι : Type*} [Field F] [Fintype F]
    (s : Finset ι) (χ ψ : ι → MulChar F ℂ) (a : ι → ℂ)
    (hn : ∀ i ∈ s, χ i ≠ 1 ∨ ψ i ≠ 1) :
    ‖∑ i ∈ s, a i * ∑ x : F, χ i x * ψ i (x + 1)‖ ≤
      (∑ i ∈ s, ‖a i‖) * Real.sqrt (Fintype.card F : ℝ) := by
  calc
    _ ≤ ∑ i ∈ s, ‖a i * ∑ x : F, χ i x * ψ i (x + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖a i‖ * Real.sqrt (Fintype.card F : ℝ) := by
      apply sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (consecutive_character_sum_norm_le (χ i) (ψ i) (hn i hi)) (norm_nonneg _)
    _ = _ := (sum_mul _ _ _).symm

end A397683Characters


end JacobiBoundsLegacy


section CountEstimatesLegacy

open Finset A397683Tensor A397683Characters
noncomputable section
namespace A397683Counts

/-- A finite real-weighted multiplicative-character expansion. -/
def series {F ι : Type*} [CommRing F] [Fintype ι]
    (χ : ι → MulChar F ℂ) (a : ι → ℝ) (x : F) : ℂ := ∑ i, (a i : ℂ) * χ i x

def correlation {F ι κ : Type*} [CommRing F] [Fintype F] [Fintype ι] [Fintype κ]
    (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ) (a : ι → ℝ) (b : κ → ℝ) : ℂ :=
  ∑ x : F, series χ a x * series ψ b (x + 1)

/-- Bilinear character expansions, in the x,x+1 rather than Jacobi normalization. -/
theorem correlation_expansion {F ι κ : Type*} [CommRing F] [Fintype F]
    [Fintype ι] [Fintype κ] (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ)
    (a : ι → ℝ) (b : κ → ℝ) :
    correlation χ ψ a b = ∑ z : ι × κ, (a z.1 * b z.2 : ℝ) *
      (∑ x : F, χ z.1 x * ψ z.2 (x + 1)) := by
  unfold correlation series
  rw [weighted_consecutive_expansion]
  simp only [Fintype.sum_prod_type, Complex.ofReal_mul, consecutive_character_sum]

/-- An exact principal coefficient plus a sharp L1 off-principal error bound. -/
theorem correlation_error {F ι κ : Type*} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ] (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ)
    (a : ι → ℝ) (b : κ → ℝ) (i₀ : ι) (j₀ : κ)
    (hχ₀ : χ i₀ = 1) (hψ₀ : ψ j₀ = 1)
    (hχ : ∀ i, i ≠ i₀ → χ i ≠ 1) (hψ : ∀ j, j ≠ j₀ → ψ j ≠ 1) :
    ‖correlation χ ψ a b - (a i₀ * b j₀ : ℝ) * ((Fintype.card F : ℂ) - 2)‖ ≤
      ((∑ i, |a i|) * (∑ j, |b j|) - |a i₀ * b j₀|) *
        Real.sqrt (Fintype.card F : ℝ) := by
  classical
  let s : Finset (ι × κ) := univ.erase (i₀, j₀)
  let term : ι × κ → ℂ := fun z => (a z.1 * b z.2 : ℝ) *
    ∑ x : F, χ z.1 x * ψ z.2 (x + 1)
  have hmain : term (i₀, j₀) =
      (a i₀ * b j₀ : ℝ) * ((Fintype.card F : ℂ) - 2) := by
    dsimp [term]
    rw [hχ₀, hψ₀, consecutive_principal_sum]
  have he : correlation χ ψ a b -
      (a i₀ * b j₀ : ℝ) * ((Fintype.card F : ℂ) - 2) = ∑ z ∈ s, term z := by
    rw [correlation_expansion, ← hmain]
    exact (sum_erase_eq_sub (mem_univ (i₀, j₀))).symm
  have hn : ∀ z ∈ s, χ z.1 ≠ 1 ∨ ψ z.2 ≠ 1 := by
    intro z hz
    by_cases hi : z.1 = i₀
    · right
      apply hψ
      intro hj
      exact (mem_erase.mp hz).1 (Prod.ext hi hj)
    · exact Or.inl (hχ _ hi)
  rw [he]
  have hb := weighted_off_principal_bound s (fun z => χ z.1) (fun z => ψ z.2)
    (fun z => (a z.1 * b z.2 : ℝ)) hn
  change ‖∑ z ∈ s, term z‖ ≤ _ at hb
  have hw : (∑ z ∈ s, ‖(a z.1 * b z.2 : ℝ)‖) =
      (∑ i, |a i|) * (∑ j, |b j|) - |a i₀ * b j₀| := by
    simp only [Real.norm_eq_abs]
    dsimp [s]
    rw [sum_erase_eq_sub (mem_univ _)]
    simp only [Fintype.sum_prod_type, abs_mul, ← mul_sum, ← sum_mul]
  simpa only [Complex.norm_real, hw] using hb

/-- e-free in the character-kernel description, with zero explicitly excluded. -/
def EFree {F ι : Type*} [Field F] (χ : ι → MulChar F ℂ) (x : F) : Prop :=
  x ≠ 0 ∧ ∀ i, χ i x ≠ 1

noncomputable instance eFreeDecidable {F ι : Type*} [Field F]
    (χ : ι → MulChar F ℂ) (x : F) : Decidable (EFree χ x) := Classical.propDecidable _

/-- The exact unnormalized count N(e,f) for two character-kernel systems. -/
def pairCount {F ι κ : Type*} [Field F] [Fintype F]
    (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ) : ℕ := by
  classical
  exact (univ.filter (fun x : F => EFree χ x ∧ EFree ψ (x + 1))).card

/-- The tensor's actual character family. -/
def tensorChars {F ι : Type*} [CommRing F] [Fintype ι]
    (r : ι → ℕ) (χ : ι → MulChar F ℂ) (j : ∀ i, Option (Fin (r i - 1))) : MulChar F ℂ :=
  ∏ i, localCharacter (χ i) (r i) (j i)

/-- The expansion is the exact all-field e-free indicator, including zero. -/
theorem tensor_series_value {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (r : ι → ℕ) (χ : ι → MulChar F ℂ) (hr : ∀ i, 1 ≤ r i)
    (hχ : ∀ i, χ i ^ r i = 1) (x : F) :
    series (tensorChars r χ) (tensorCoefficient r) x = if EFree χ x then 1 else 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    change (∑ j : ∀ i, Option (Fin (r i - 1)), (tensorCoefficient r j : ℂ) *
      (∏ i, localCharacter (χ i) (r i) (j i)) (0 : F)) = _
    rw [tensor_at_zero]
    simp only [EFree, ne_eq, not_true_eq_false, false_and, if_false]
  · let u : Fˣ := Units.mk0 x hx
    have he := tensor_indicator r χ hr hχ u
    change series (tensorChars r χ) (tensorCoefficient r) x = _ at he
    by_cases hf : ∀ i, χ i x ≠ 1
    · rw [if_pos (show EFree χ x from ⟨hx, hf⟩)]
      have hu : ∀ i, χ i (u : F) ≠ 1 := hf
      rw [if_pos hu] at he
      exact he
    · rw [if_neg (show ¬EFree χ x from fun h => hf h.2)]
      have hu : ¬∀ i, χ i (u : F) ≠ 1 := hf
      rw [if_neg hu] at he
      exact he

/-- Tensor correlations are exactly the natural-number e-free pair counts. -/
theorem pairCount_eq_correlation {F ι κ : Type*} [Field F] [Fintype F]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (r : ι → ℕ) (χ : ι → MulChar F ℂ) (hr : ∀ i, 1 ≤ r i)
    (hχ : ∀ i, χ i ^ r i = 1)
    (s : κ → ℕ) (ψ : κ → MulChar F ℂ) (hs : ∀ j, 1 ≤ s j)
    (hψ : ∀ j, ψ j ^ s j = 1) :
    (pairCount χ ψ : ℂ) = correlation (tensorChars r χ) (tensorChars s ψ)
      (tensorCoefficient r) (tensorCoefficient s) := by
  classical
  unfold correlation
  simp_rw [tensor_series_value r χ hr hχ, tensor_series_value s ψ hs hψ]
  simp only [pairCount, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases hx : EFree χ x <;> by_cases hy : EFree ψ (x + 1) <;> simp [hx, hy]

/-- The sharp symmetric tensor count error, before taking its lower bound. -/
theorem pairCount_error {F ι : Type*} [Field F] [Fintype F]
    [Fintype ι] [DecidableEq ι]
    (r : ι → ℕ) (χ : ι → MulChar F ℂ)
    (hr : ∀ i, (r i).Prime) (hχ : ∀ i, orderOf (χ i) = r i)
    (hc : ∀ i j, i ≠ j → Nat.Coprime (r i) (r j)) :
    ‖(pairCount χ χ : ℂ) - ((∏ i, theta (r i)) ^ 2 : ℝ) *
      ((Fintype.card F : ℂ) - 2)‖ ≤
      (∏ i, theta (r i)) ^ 2 * ((2 ^ Fintype.card ι : ℝ) ^ 2 - 1) *
        Real.sqrt (Fintype.card F : ℝ) := by
  classical
  have hpos : ∀ i, 1 ≤ r i := fun i => (hr i).one_lt.le
  have hpow : ∀ i, χ i ^ r i = 1 := fun i => by rw [← hχ i]; exact pow_orderOf_eq_one _
  have hzero : tensorChars r χ (fun _ => none) = 1 := by simp [tensorChars, localCharacter]
  have hnon : ∀ j, j ≠ (fun _ => none) → tensorChars r χ j ≠ 1 := by
    intro j hj he
    exact hj (funext ((tensor_character_eq_one_iff r χ hr hχ hc j).mp he))
  have he := correlation_error (tensorChars r χ) (tensorChars r χ)
    (tensorCoefficient r) (tensorCoefficient r) (fun _ => none) (fun _ => none)
    hzero hzero hnon hnon
  rw [← pairCount_eq_correlation r χ hpos hpow r χ hpos hpow] at he
  simp only [tensor_l1 r hpos, tensor_principal] at he
  have ht : (0 : ℝ) ≤ ∏ i, theta (r i) := prod_nonneg (fun i _ => theta_nonneg (hpos i))
  simp only [abs_mul, abs_of_nonneg ht] at he
  simp only [pow_two] at he ⊢
  convert he using 1 <;> ring

/-- The real-valued lower estimate N(e,e) used by the sieve. -/
theorem pairCount_lower {F ι : Type*} [Field F] [Fintype F]
    [Fintype ι] [DecidableEq ι]
    (r : ι → ℕ) (χ : ι → MulChar F ℂ)
    (hr : ∀ i, (r i).Prime) (hχ : ∀ i, orderOf (χ i) = r i)
    (hc : ∀ i j, i ≠ j → Nat.Coprime (r i) (r j)) :
    (∏ i, theta (r i)) ^ 2 * ((Fintype.card F : ℝ) - 2 -
      ((2 ^ Fintype.card ι : ℝ) ^ 2 - 1) * Real.sqrt (Fintype.card F : ℝ)) ≤
      (pairCount χ χ : ℝ) := by
  have he := pairCount_error r χ hr hχ hc
  have hre := (Complex.abs_re_le_norm ((pairCount χ χ : ℂ) -
    ((∏ i, theta (r i)) ^ 2 : ℝ) * ((Fintype.card F : ℂ) - 2))).trans he
  have hreal : |(pairCount χ χ : ℝ) - (∏ i, theta (r i)) ^ 2 *
      ((Fintype.card F : ℝ) - 2)| ≤
      (∏ i, theta (r i)) ^ 2 * ((2 ^ Fintype.card ι : ℝ) ^ 2 - 1) *
        Real.sqrt (Fintype.card F : ℝ) := by
    have hh : ((pairCount χ χ : ℂ) - ((∏ i, theta (r i)) ^ 2 : ℝ) *
        ((Fintype.card F : ℂ) - 2)) =
        (((pairCount χ χ : ℝ) - (∏ i, theta (r i)) ^ 2 *
          ((Fintype.card F : ℝ) - 2) : ℝ) : ℂ) := by push_cast <;> ring
    rw [hh, Complex.ofReal_re] at hre
    exact hre
  have hl := (abs_le.mp hreal).1
  linarith

/-- A bilinear correlation with no double-principal index is entirely error. -/
theorem correlation_bound {F ι κ : Type*} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ] (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ)
    (a : ι → ℝ) (b : κ → ℝ) (hn : ∀ i j, χ i ≠ 1 ∨ ψ j ≠ 1) :
    ‖correlation χ ψ a b‖ ≤ (∑ i, |a i|) * (∑ j, |b j|) *
      Real.sqrt (Fintype.card F : ℝ) := by
  classical
  rw [correlation_expansion]
  have hb := weighted_off_principal_bound (univ : Finset (ι × κ))
    (fun z => χ z.1) (fun z => ψ z.2) (fun z => (a z.1 * b z.2 : ℝ)) (fun z _ => hn z.1 z.2)
  simpa only [Complex.norm_real, Real.norm_eq_abs, Fintype.sum_prod_type, abs_mul,
    ← mul_sum, ← sum_mul] using hb

/-- Products of weighted series are series of product characters. -/
theorem series_product {F ι κ : Type*} [CommRing F] [Fintype ι] [Fintype κ]
    (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ) (a : ι → ℝ) (b : κ → ℝ) (x : F) :
    series χ a x * series ψ b x =
      series (fun z : ι × κ => χ z.1 * ψ z.2) (fun z => a z.1 * b z.2) x := by
  classical
  simp only [series, Fintype.sum_prod_type, Complex.ofReal_mul, MulChar.mul_apply,
    sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ac_rfl

/-- Multiplication by the principal character fixes any character series. -/
theorem series_mul_principal {F ι : Type*} [CommRing F] [Fintype ι]
    (χ : ι → MulChar F ℂ) (a : ι → ℝ) (x : F) :
    series χ a x * (1 : MulChar F ℂ) x = series χ a x := by
  unfold series
  rw [sum_mul]
  apply sum_congr rfl
  intro i _
  rw [mul_assoc, ← MulChar.mul_apply, mul_one]

end A397683Counts


end -- noncomputable section


end CountEstimatesLegacy


section ExtraCountsLegacy

open Finset A397683Tensor A397683Characters A397683Counts
noncomputable section
namespace A397683Counts

/-- One additional prime's local character projector. -/
def localSeries {F : Type*} [CommRing F] (η : MulChar F ℂ) (r : ℕ) (x : F) : ℂ :=
  series (localCharacter η r) (coefficient r) x

/-- The local expansion consists of its principal term and r-1 equal-weight terms. -/
theorem localSeries_split {F : Type*} [CommRing F]
    (η : MulChar F ℂ) (r : ℕ) (x : F) :
    localSeries η r x = (theta r : ℂ) * (1 : MulChar F ℂ) x +
      series (fun j : Fin (r - 1) => η ^ (j.val + 1)) (fun _ => -(1 / (r : ℝ))) x := by
  unfold localSeries series
  rw [Fintype.sum_option]
  rfl

/-- Local nonprincipal coefficients have total L1 exactly theta(r), not 2 theta(r). -/
theorem local_nonprincipal_l1 (r : ℕ) (hr : 1 ≤ r) :
    (∑ j : Fin (r - 1), |-(1 / (r : ℝ))|) = theta r := by
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg,
    abs_div, abs_one, abs_of_nonneg (show (0 : ℝ) ≤ r from Nat.cast_nonneg r)]
  rw [Nat.cast_sub hr, Nat.cast_one]
  unfold theta
  ring

/-- Adding a local projector on the first member of the consecutive pair. -/
def leftCorrelation {F ι κ : Type*} [CommRing F] [Fintype F] [Fintype ι] [Fintype κ]
    (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ) (a : ι → ℝ) (b : κ → ℝ)
    (η : MulChar F ℂ) (r : ℕ) : ℂ :=
  ∑ x : F, (series χ a x * localSeries η r x) * series ψ b (x + 1)

/-- The new-coordinate error consists solely of the nonprincipal new characters. -/
theorem leftCorrelation_split {F ι κ : Type*} [CommRing F] [Fintype F]
    [Fintype ι] [Fintype κ] (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ)
    (a : ι → ℝ) (b : κ → ℝ) (η : MulChar F ℂ) (r : ℕ) :
    leftCorrelation χ ψ a b η r = (theta r : ℂ) * correlation χ ψ a b +
      correlation (fun z : ι × Fin (r - 1) => χ z.1 * η ^ (z.2.val + 1)) ψ
        (fun z => a z.1 * -(1 / (r : ℝ))) b := by
  unfold leftCorrelation correlation
  have he (x : F) :
      (series χ a x * localSeries η r x) * series ψ b (x + 1) =
      (theta r : ℂ) * (series χ a x * series ψ b (x + 1)) +
        series (fun z : ι × Fin (r - 1) => χ z.1 * η ^ (z.2.val + 1))
          (fun z => a z.1 * -(1 / (r : ℝ))) x * series ψ b (x + 1) := by
    rw [localSeries_split, ← series_product χ
      (fun j : Fin (r - 1) => η ^ (j.val + 1)) a (fun _ => -(1 / (r : ℝ))) x]
    linear_combination (theta r : ℂ) * series ψ b (x + 1) * (series_mul_principal χ a x)
  simp_rw [he]
  rw [sum_add_distrib, ← mul_sum]

/-- Multiplying a prime-order nonprincipal term by a coprime-order character stays nonprincipal. -/
theorem mul_prime_power_ne_one {F : Type*} [CommRing F]
    (χ η : MulChar F ℂ) (r : ℕ) (hr : r.Prime) (hη : orderOf η = r)
    (hc : Nat.Coprime (orderOf χ) r) (j : Fin (r - 1)) :
    χ * η ^ (j.val + 1) ≠ 1 := by
  have hj : j.val + 1 < r := by have := j.isLt; omega
  have hcop : (orderOf η).Coprime (j.val + 1) := by
    rw [hη]
    exact hr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) hj)
  have ho : orderOf (η ^ (j.val + 1)) = r := hcop.orderOf_pow.trans hη
  intro h
  have hi : η ^ (j.val + 1) = χ⁻¹ := eq_inv_of_mul_eq_one_right h
  have he := congrArg orderOf hi
  rw [ho, orderOf_inv] at he
  have hh : Nat.Coprime r r := by simpa only [← he] using hc
  exact hr.ne_one (by simpa only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_self] using hh)

/-- Analytic new-prime-coordinate error, with no triangle loss in the principal term. -/
theorem leftCorrelation_error {F ι κ : Type*} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ] (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ)
    (a : ι → ℝ) (b : κ → ℝ) (η : MulChar F ℂ) (r : ℕ)
    (hr : r.Prime) (hη : orderOf η = r) (hc : ∀ i, Nat.Coprime (orderOf (χ i)) r) :
    ‖leftCorrelation χ ψ a b η r - (theta r : ℂ) * correlation χ ψ a b‖ ≤
      (∑ i, |a i|) * (∑ j, |b j|) * theta r * Real.sqrt (Fintype.card F : ℝ) := by
  rw [leftCorrelation_split, add_sub_cancel_left]
  have he := correlation_bound
    (fun z : ι × Fin (r - 1) => χ z.1 * η ^ (z.2.val + 1)) ψ
    (fun z => a z.1 * -(1 / (r : ℝ))) b
    (fun z _ => Or.inl (mul_prime_power_ne_one (χ z.1) η r hr hη (hc z.1) z.2))
  have hw : (∑ z : ι × Fin (r - 1), |a z.1 * -(1 / (r : ℝ))|) =
      (∑ i, |a i|) * theta r := by
    rw [Fintype.sum_prod_type]
    simp only [abs_mul]
    calc
      _ = ∑ i, |a i| * (∑ j : Fin (r - 1), |-(1 / (r : ℝ))|) := by
        apply sum_congr rfl
        intro i _
        exact (mul_sum _ _ _).symm
      _ = _ := by rw [local_nonprincipal_l1 r hr.one_lt.le, sum_mul]
  rw [hw] at he
  convert he using 1 <;> ring

/-- Adding a local projector on the successor in the consecutive pair. -/
def rightCorrelation {F ι κ : Type*} [CommRing F] [Fintype F] [Fintype ι] [Fintype κ]
    (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ) (a : ι → ℝ) (b : κ → ℝ)
    (η : MulChar F ℂ) (r : ℕ) : ℂ :=
  ∑ x : F, series χ a x * (series ψ b (x + 1) * localSeries η r (x + 1))

theorem rightCorrelation_split {F ι κ : Type*} [CommRing F] [Fintype F]
    [Fintype ι] [Fintype κ] (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ)
    (a : ι → ℝ) (b : κ → ℝ) (η : MulChar F ℂ) (r : ℕ) :
    rightCorrelation χ ψ a b η r = (theta r : ℂ) * correlation χ ψ a b +
      correlation χ (fun z : κ × Fin (r - 1) => ψ z.1 * η ^ (z.2.val + 1))
        a (fun z => b z.1 * -(1 / (r : ℝ))) := by
  unfold rightCorrelation correlation
  have he (x : F) :
      series χ a x * (series ψ b (x + 1) * localSeries η r (x + 1)) =
      (theta r : ℂ) * (series χ a x * series ψ b (x + 1)) +
        series χ a x * series (fun z : κ × Fin (r - 1) => ψ z.1 * η ^ (z.2.val + 1))
          (fun z => b z.1 * -(1 / (r : ℝ))) (x + 1) := by
    rw [localSeries_split, ← series_product ψ
      (fun j : Fin (r - 1) => η ^ (j.val + 1)) b (fun _ => -(1 / (r : ℝ))) (x + 1)]
    linear_combination (theta r : ℂ) * series χ a x * (series_mul_principal ψ b (x + 1))
  simp_rw [he]
  rw [sum_add_distrib, ← mul_sum]

theorem rightCorrelation_error {F ι κ : Type*} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ] (χ : ι → MulChar F ℂ) (ψ : κ → MulChar F ℂ)
    (a : ι → ℝ) (b : κ → ℝ) (η : MulChar F ℂ) (r : ℕ)
    (hr : r.Prime) (hη : orderOf η = r) (hc : ∀ j, Nat.Coprime (orderOf (ψ j)) r) :
    ‖rightCorrelation χ ψ a b η r - (theta r : ℂ) * correlation χ ψ a b‖ ≤
      (∑ i, |a i|) * (∑ j, |b j|) * theta r * Real.sqrt (Fintype.card F : ℝ) := by
  rw [rightCorrelation_split, add_sub_cancel_left]
  have he := correlation_bound χ
    (fun z : κ × Fin (r - 1) => ψ z.1 * η ^ (z.2.val + 1))
    a (fun z => b z.1 * -(1 / (r : ℝ)))
    (fun _ z => Or.inr (mul_prime_power_ne_one (ψ z.1) η r hr hη (hc z.1) z.2))
  have hw : (∑ z : κ × Fin (r - 1), |b z.1 * -(1 / (r : ℝ))|) =
      (∑ j, |b j|) * theta r := by
    rw [Fintype.sum_prod_type]
    simp only [abs_mul]
    calc
      _ = ∑ j, |b j| * (∑ l : Fin (r - 1), |-(1 / (r : ℝ))|) := by
        apply sum_congr rfl
        intro j _
        exact (mul_sum _ _ _).symm
      _ = _ := by rw [local_nonprincipal_l1 r hr.one_lt.le, sum_mul]
  rw [hw] at he
  convert he using 1 <;> ring

/-- Exact local indicator on the whole field, with the trivial character zero at zero. -/
theorem localSeries_value {F : Type*} [Field F]
    (η : MulChar F ℂ) (r : ℕ) (hr : 1 ≤ r) (hη : η ^ r = 1) (x : F) :
    localSeries η r x = if EFree (fun _ : Unit => η) x then 1 else 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    have h0 (ψ : MulChar F ℂ) : ψ 0 = 0 := ψ.map_nonunit not_isUnit_zero
    simp only [localSeries, series, h0, mul_zero, sum_const_zero]
    rw [if_neg (show ¬EFree (fun _ : Unit => η) 0 from fun h => h.1 rfl)]
  · let u : Fˣ := Units.mk0 x hx
    have he := local_factor_value η r hr hη u
    change localSeries η r x = _ at he
    by_cases hy : η x = 1
    · rw [if_neg (show ¬EFree (fun _ : Unit => η) x from fun h => h.2 () hy)]
      have hu : η (u : F) = 1 := hy
      rw [if_pos hu] at he
      exact he
    · rw [if_pos (show EFree (fun _ : Unit => η) x from ⟨hx, fun _ => hy⟩)]
      have hu : η (u : F) ≠ 1 := hy
      rw [if_neg hu] at he
      exact he

/-- N(er,e): add the new prime's kernel exclusion at the first coordinate. -/
def leftPairCount {F ι : Type*} [Field F] [Fintype F]
    (χ : ι → MulChar F ℂ) (η : MulChar F ℂ) : ℕ := by
  classical
  exact (univ.filter (fun x : F => EFree χ x ∧ η x ≠ 1 ∧ EFree χ (x + 1))).card

/-- N(e,er): add the new prime's kernel exclusion at the successor coordinate. -/
def rightPairCount {F ι : Type*} [Field F] [Fintype F]
    (χ : ι → MulChar F ℂ) (η : MulChar F ℂ) : ℕ := by
  classical
  exact (univ.filter (fun x : F => EFree χ x ∧ EFree χ (x + 1) ∧ η (x + 1) ≠ 1)).card

theorem leftPairCount_eq_correlation {F ι : Type*} [Field F] [Fintype F]
    [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (χ : ι → MulChar F ℂ)
    (hr : ∀ i, 1 ≤ r i) (hχ : ∀ i, χ i ^ r i = 1)
    (η : MulChar F ℂ) (t : ℕ) (ht : 1 ≤ t) (hη : η ^ t = 1) :
    (leftPairCount χ η : ℂ) = leftCorrelation (tensorChars r χ) (tensorChars r χ)
      (tensorCoefficient r) (tensorCoefficient r) η t := by
  classical
  unfold leftCorrelation
  simp_rw [tensor_series_value r χ hr hχ, localSeries_value η t ht hη]
  simp only [leftPairCount, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases ha : EFree χ x
  · by_cases hb : EFree χ (x + 1)
    · by_cases he : η x = 1
      · have hex : ¬EFree (fun _ : Unit => η) x := fun h => h.2 () he
        simp [ha, hb, he, hex]
      · have hex : EFree (fun _ : Unit => η) x := ⟨ha.1, fun _ => he⟩
        simp [ha, hb, he, hex]
    · simp [ha, hb]
  · simp [ha]

theorem rightPairCount_eq_correlation {F ι : Type*} [Field F] [Fintype F]
    [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (χ : ι → MulChar F ℂ)
    (hr : ∀ i, 1 ≤ r i) (hχ : ∀ i, χ i ^ r i = 1)
    (η : MulChar F ℂ) (t : ℕ) (ht : 1 ≤ t) (hη : η ^ t = 1) :
    (rightPairCount χ η : ℂ) = rightCorrelation (tensorChars r χ) (tensorChars r χ)
      (tensorCoefficient r) (tensorCoefficient r) η t := by
  classical
  unfold rightCorrelation
  simp_rw [tensor_series_value r χ hr hχ, localSeries_value η t ht hη]
  simp only [rightPairCount, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases ha : EFree χ x
  · by_cases hb : EFree χ (x + 1)
    · by_cases he : η (x + 1) = 1
      · have hex : ¬EFree (fun _ : Unit => η) (x + 1) := fun h => h.2 () he
        simp [ha, hb, he, hex]
      · have hex : EFree (fun _ : Unit => η) (x + 1) := ⟨hb.1, fun _ => he⟩
        simp [ha, hb, he, hex]
    · simp [ha, hb]
  · simp [ha]

/-- Coprimality with a fixed integer is preserved by products of character orders. -/
theorem coprime_order_prod {ι G : Type*} [CommGroup G]
    (s : Finset ι) (f : ι → G) (t : ℕ)
    (hc : ∀ i ∈ s, Nat.Coprime (orderOf (f i)) t) :
    Nat.Coprime (orderOf (∏ i ∈ s, f i)) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi]
    have htail := ih (fun j hj => hc j (mem_insert_of_mem hj))
    have hh := Nat.coprime_mul_iff_left.mpr ⟨hc i (mem_insert_self _ _), htail⟩
    exact hh.of_dvd_left (Commute.all _ _).orderOf_mul_dvd_mul_orderOf

theorem tensor_order_coprime {F ι : Type*} [CommRing F] [Fintype ι]
    (r : ι → ℕ) (χ : ι → MulChar F ℂ) (hχ : ∀ i, orderOf (χ i) = r i)
    (t : ℕ) (hc : ∀ i, Nat.Coprime (r i) t) (j : ∀ i, Option (Fin (r i - 1))) :
    Nat.Coprime (orderOf (tensorChars r χ j)) t := by
  apply coprime_order_prod
  intro i _
  exact (hc i).of_dvd_left (localCharacter_order_dvd (χ i) (r i) (hχ i) (j i))

/-- The actual finite-field sieve correction |N(er,e)-theta(r)N(e,e)|. -/
theorem leftPairCount_error {F ι : Type*} [Field F] [Fintype F]
    [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (χ : ι → MulChar F ℂ)
    (hr : ∀ i, (r i).Prime) (hχ : ∀ i, orderOf (χ i) = r i)
    (η : MulChar F ℂ) (t : ℕ) (ht : t.Prime) (hη : orderOf η = t)
    (hc : ∀ i, Nat.Coprime (r i) t) :
    |(leftPairCount χ η : ℝ) - theta t * (pairCount χ χ : ℝ)| ≤
      (∏ i, theta (r i)) ^ 2 * theta t * (2 ^ Fintype.card ι : ℝ) ^ 2 *
        Real.sqrt (Fintype.card F : ℝ) := by
  classical
  have hpos : ∀ i, 1 ≤ r i := fun i => (hr i).one_lt.le
  have hpow : ∀ i, χ i ^ r i = 1 := fun i => by rw [← hχ i]; exact pow_orderOf_eq_one _
  have hηpow : η ^ t = 1 := by rw [← hη]; exact pow_orderOf_eq_one _
  have he := leftCorrelation_error (tensorChars r χ) (tensorChars r χ)
    (tensorCoefficient r) (tensorCoefficient r) η t ht hη (tensor_order_coprime r χ hχ t hc)
  rw [← leftPairCount_eq_correlation r χ hpos hpow η t ht.one_lt.le hηpow,
    ← pairCount_eq_correlation r χ hpos hpow r χ hpos hpow] at he
  simp only [tensor_l1 r hpos] at he
  have hh : ((leftPairCount χ η : ℂ) - (theta t : ℂ) * (pairCount χ χ : ℂ)) =
      (((leftPairCount χ η : ℝ) - theta t * (pairCount χ χ : ℝ) : ℝ) : ℂ) := by
    push_cast <;> ring
  rw [hh, Complex.norm_real, Real.norm_eq_abs] at he
  convert he using 1 <;> ring

/-- The actual finite-field sieve correction |N(e,er)-theta(r)N(e,e)|. -/
theorem rightPairCount_error {F ι : Type*} [Field F] [Fintype F]
    [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (χ : ι → MulChar F ℂ)
    (hr : ∀ i, (r i).Prime) (hχ : ∀ i, orderOf (χ i) = r i)
    (η : MulChar F ℂ) (t : ℕ) (ht : t.Prime) (hη : orderOf η = t)
    (hc : ∀ i, Nat.Coprime (r i) t) :
    |(rightPairCount χ η : ℝ) - theta t * (pairCount χ χ : ℝ)| ≤
      (∏ i, theta (r i)) ^ 2 * theta t * (2 ^ Fintype.card ι : ℝ) ^ 2 *
        Real.sqrt (Fintype.card F : ℝ) := by
  classical
  have hpos : ∀ i, 1 ≤ r i := fun i => (hr i).one_lt.le
  have hpow : ∀ i, χ i ^ r i = 1 := fun i => by rw [← hχ i]; exact pow_orderOf_eq_one _
  have hηpow : η ^ t = 1 := by rw [← hη]; exact pow_orderOf_eq_one _
  have he := rightCorrelation_error (tensorChars r χ) (tensorChars r χ)
    (tensorCoefficient r) (tensorCoefficient r) η t ht hη (tensor_order_coprime r χ hχ t hc)
  rw [← rightPairCount_eq_correlation r χ hpos hpow η t ht.one_lt.le hηpow,
    ← pairCount_eq_correlation r χ hpos hpow r χ hpos hpow] at he
  simp only [tensor_l1 r hpos] at he
  have hh : ((rightPairCount χ η : ℂ) - (theta t : ℂ) * (pairCount χ χ : ℂ)) =
      (((rightPairCount χ η : ℝ) - theta t * (pairCount χ χ : ℝ) : ℝ) : ℂ) := by
    push_cast <;> ring
  rw [hh, Complex.norm_real, Real.norm_eq_abs] at he
  convert he using 1 <;> ring

end A397683Counts


end -- noncomputable section


end ExtraCountsLegacy

end

section

namespace A397683Sieve
open Finset
variable {α ι : Type*} [DecidableEq α]

/-- The two coordinates are indexed by Bool; tail indices need not be primes
for the purely combinatorial sieve. -/
def badUnion (tail : Finset ι) (bad : ι → Bool → Finset α) : Finset α :=
  tail.biUnion fun r => bad r false ∪ bad r true

def survivors (A : Finset α) (tail : Finset ι) (bad : ι → Bool → Finset α) : Finset α :=
  A \ badUnion tail bad

@[simp] theorem mem_survivors {A : Finset α} {tail : Finset ι}
    {bad : ι → Bool → Finset α} {x : α} :
    x ∈ survivors A tail bad ↔ x ∈ A ∧ ∀ r ∈ tail, ∀ side, x ∉ bad r side := by
  simp only [survivors, mem_sdiff, badUnion, mem_biUnion, mem_union]
  constructor
  · rintro ⟨hx,h⟩
    refine ⟨hx, ?_⟩
    intro r hr side hb
    cases side with
    | false => exact h ⟨r,hr,Or.inl hb⟩
    | true => exact h ⟨r,hr,Or.inr hb⟩
  · rintro ⟨hx,h⟩
    refine ⟨hx, ?_⟩
    rintro ⟨r,hr,hb | hb⟩
    · exact h r hr false hb
    · exact h r hr true hb

/-- The exact two-coordinate union bound, with no disjointness assumptions. -/
theorem card_union_bound (A : Finset α) (tail : Finset ι)
    (bad : ι → Bool → Finset α) :
    A.card ≤ (survivors A tail bad).card +
      ∑ r ∈ tail, ((bad r false).card + (bad r true).card) := by
  have hu : (badUnion tail bad).card ≤
      ∑ r ∈ tail, ((bad r false).card + (bad r true).card) := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro r hr
    exact Finset.card_union_le _ _
  have hc := Finset.card_le_card_sdiff_add_card (s := A) (t := badUnion tail bad)
  change A.card ≤ (survivors A tail bad).card + (badUnion tail bad).card at hc
  omega

theorem real_union_bound (A : Finset α) (tail : Finset ι)
    (bad : ι → Bool → Finset α) :
    (A.card : ℝ) - ∑ r ∈ tail, ((bad r false).card + (bad r true).card : ℝ) ≤
      (survivors A tail bad).card := by
  have hc : (A.card : ℝ) ≤ (survivors A tail bad).card +
      ∑ r ∈ tail, ((bad r false).card + (bad r true).card : ℝ) := by
    exact_mod_cast card_union_bound A tail bad
  linarith

/-- Standard sieve in passing counts: total >= sum of the single-tail passing
counts minus (twice the tail size minus one) times the core passing count. -/
theorem passing_count_bound (A : Finset α) (tail : Finset ι)
    (bad : ι → Bool → Finset α)
    (hsub : ∀ r ∈ tail, ∀ side, bad r side ⊆ A) :
    (∑ r ∈ tail, (((A \ bad r false).card : ℝ) + (A \ bad r true).card)) -
      (2 * (tail.card : ℝ) - 1) * A.card ≤ (survivors A tail bad).card := by
  have hc := real_union_bound A tail bad
  have hs : (∑ r ∈ tail, ((bad r false).card + (bad r true).card : ℝ)) =
      (tail.card : ℝ) * (2 * A.card) -
      ∑ r ∈ tail, (((A \ bad r false).card : ℝ) + (A \ bad r true).card) := by
    calc
      _ = ∑ r ∈ tail, (2 * (A.card : ℝ) -
          (((A \ bad r false).card : ℝ) + (A \ bad r true).card)) := by
        apply Finset.sum_congr rfl
        intro r hr
        have h0 : ((A \ bad r false).card : ℝ) + (bad r false).card = A.card := by
          exact_mod_cast Finset.card_sdiff_add_card_eq_card (hsub r hr false)
        have h1 : ((A \ bad r true).card : ℝ) + (bad r true).card = A.card := by
          exact_mod_cast Finset.card_sdiff_add_card_eq_card (hsub r hr true)
        linarith
      _ = _ := by simp [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hs] at hc
  linarith

/-- δ = 1 - 2 Σ(1-θ_r); with θ_r=1-1/r this is the usual two-coordinate
sieve coefficient 1-2 Σ 1/r. -/
def delta (tail : Finset ι) (θ : ι → ℝ) : ℝ := 1 - 2 * ∑ r ∈ tail, (1 - θ r)

/-- Jacobi correction version: after writing each single-tail passing count
as θ_r times the core count plus J_(r,side), the errors cost only their
absolute values. -/
theorem correction_bound (A : Finset α) (tail : Finset ι)
    (bad : ι → Bool → Finset α) (θ : ι → ℝ) (J : ι → Bool → ℝ)
    (hsub : ∀ r ∈ tail, ∀ side, bad r side ⊆ A)
    (hpass : ∀ r ∈ tail, ∀ side,
      ((A \ bad r side).card : ℝ) = θ r * A.card + J r side) :
    delta tail θ * A.card - ∑ r ∈ tail, (|J r false| + |J r true|) ≤
      (survivors A tail bad).card := by
  have hc := passing_count_bound A tail bad hsub
  have hs : (∑ r ∈ tail, (((A \ bad r false).card : ℝ) + (A \ bad r true).card)) =
      (2 * ∑ r ∈ tail, θ r) * A.card + ∑ r ∈ tail, (J r false + J r true) := by
    calc
      _ = ∑ r ∈ tail, ((2 * θ r) * A.card + (J r false + J r true)) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hpass r hr false, hpass r hr true]
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  have hd : delta tail θ = 1 - 2 * ((tail.card : ℝ) - ∑ r ∈ tail, θ r) := by
    simp [delta, Finset.sum_sub_distrib]
  have he : -(∑ r ∈ tail, (|J r false| + |J r true|)) ≤
      ∑ r ∈ tail, (J r false + J r true) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun r hr => by
      have h0 := neg_abs_le (J r false)
      have h1 := neg_abs_le (J r true)
      linarith
  rw [hs] at hc
  rw [hd]
  nlinarith

/-- Normalize the core by θ(q)^2 and each extension by θ(r). The E terms
are arbitrary exact character/Jacobi corrections; this theorem only performs
finite-set sieving and the triangle inequality. -/

@[simp] theorem delta_one_sub (tail : Finset ι) (u : ι → ℝ) :
    delta tail (fun r => 1-u r) = 1 - 2 * ∑ r ∈ tail, u r := by
  unfold delta
  congr 2
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- A cardinal lower bound that is strictly positive produces an actual
witness passing both coordinates for every tail index. -/
theorem exists_survivor_of_lower_bound (A : Finset α) (tail : Finset ι)
    (bad : ι → Bool → Finset α) (L : ℝ) (hL : 0 < L)
    (hbound : L ≤ (survivors A tail bad).card) :
    ∃ x ∈ A, ∀ r ∈ tail, ∀ side, x ∉ bad r side := by
  have hcard : 0 < (survivors A tail bad).card := by exact_mod_cast lt_of_lt_of_le hL hbound
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hcard
  exact ⟨x,(mem_survivors.mp hx).1,(mem_survivors.mp hx).2⟩

/-- A generic universe of pairs, filtered by both core-prime conditions.
The type α may itself be a product, or may encode a consecutive pair. -/
noncomputable def coreSet (U : Finset α) (core : Finset ι)
    (free : ι → Bool → α → Prop) : Finset α := by
  classical
  exact U.filter fun x => ∀ r ∈ core, ∀ side, free r side x

noncomputable def tailBad (A : Finset α) (free : ι → Bool → α → Prop)
    (r : ι) (side : Bool) : Finset α := by
  classical
  exact A.filter fun x => ¬ free r side x

omit [DecidableEq α] in
theorem tailBad_subset (A : Finset α) (free : ι → Bool → α → Prop)
    (r : ι) (side : Bool) : tailBad A free r side ⊆ A := by
  classical
  exact Finset.filter_subset _ _

/-- Sieving the tail after the core is exactly passing the union of the
core and tail conditions. No algebraic or independence assumption is used. -/
theorem mem_core_survivors_iff [DecidableEq ι]
    (U : Finset α) (core tail : Finset ι) (free : ι → Bool → α → Prop) (x : α) :
    x ∈ survivors (coreSet U core free) tail (tailBad (coreSet U core free) free) ↔
      x ∈ U ∧ ∀ r ∈ core ∪ tail, ∀ side, free r side x := by
  classical
  rw [mem_survivors]
  constructor
  · rintro ⟨hxA,htail⟩
    have hcore := (Finset.mem_filter.mp hxA).2
    refine ⟨(Finset.mem_filter.mp hxA).1, ?_⟩
    intro r hr side
    rcases Finset.mem_union.mp hr with hr | hr
    · exact hcore r hr side
    · by_contra hfree
      exact htail r hr side (Finset.mem_filter.mpr ⟨hxA,hfree⟩)
  · rintro ⟨hx,hpass⟩
    have hxA : x ∈ coreSet U core free := by
      apply Finset.mem_filter.mpr
      exact ⟨hx,fun r hr side => hpass r (Finset.mem_union.mpr (Or.inl hr)) side⟩
    refine ⟨hxA, ?_⟩
    intro r hr side hb
    exact (Finset.mem_filter.mp hb).2 (hpass r (Finset.mem_union.mpr (Or.inr hr)) side)

/-- Final combinatorial witness interface for a universe with core/tail
free predicates. A positive numerical lower bound is the only input. -/
theorem exists_core_tail_of_lower_bound [DecidableEq ι]
    (U : Finset α) (core tail : Finset ι) (free : ι → Bool → α → Prop)
    (L : ℝ) (hL : 0 < L)
    (hbound : L ≤ (survivors (coreSet U core free) tail
      (tailBad (coreSet U core free) free)).card) :
    ∃ x ∈ U, ∀ r ∈ core ∪ tail, ∀ side, free r side x := by
  have hcard : 0 < (survivors (coreSet U core free) tail
      (tailBad (coreSet U core free) free)).card := by
    exact_mod_cast lt_of_lt_of_le hL hbound
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hcard
  exact ⟨x, (mem_core_survivors_iff U core tail free x).mp hx⟩

end A397683Sieve

end

section

namespace A397683Sieve
open Finset

/-- The elementary real inequality behind the two-coordinate sieve threshold.
It is deliberately independent of characters, fields, and prime arithmetic. -/
theorem threshold_scalar (p W s δ : ℝ) (hp : 0 ≤ p) (hW : 0 ≤ W)
    (hs : 0 ≤ s) (hδ : 0 < δ)
    (hlarge : (W * (1 + 2*s/δ) + 2)^2 < p) :
    0 < δ*(p-2) - δ*(W-1)*Real.sqrt p - 2*s*W*Real.sqrt p := by
  let C := W * (1 + 2*s/δ)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hW (by positivity)
  have hsq := Real.sq_sqrt hp
  have ht := Real.sqrt_nonneg p
  have hCt : C + 2 < Real.sqrt p := by
    change (C+2)^2 < p at hlarge
    nlinarith
  have hprod : 0 < Real.sqrt p * (Real.sqrt p - C - 2) := by
    apply mul_pos <;> linarith
  have hinner : 0 < p - 2 - (C-1)*Real.sqrt p := by nlinarith
  have hδC : δ*C = δ*W + 2*s*W := by
    dsimp [C]
    field_simp [ne_of_gt hδ]
  calc
    _ = δ*(p-2) - (δ*C-δ)*Real.sqrt p := by rw [hδC]; ring
    _ = δ * (p-2-(C-1)*Real.sqrt p) := by ring
    _ > 0 := mul_pos hδ hinner

variable {α ι : Type*} [DecidableEq α]

/-- Direct character-sum interface: only a lower bound for the core count
and absolute single-tail passing errors are required. -/
theorem direct_card_pos (A : Finset α) (tail : Finset ι)
    (bad : ι → Bool → Finset α) (θ : ι → ℝ) (θq : ℝ) (p k : ℕ)
    (hsub : ∀ r ∈ tail, ∀ side, bad r side ⊆ A)
    (hθ1 : ∀ r ∈ tail, θ r ≤ 1)
    (hδ : 0 < delta tail θ) (hθq : 0 < θq)
    (hbase : θq^2 * ((p : ℝ)-2-((4 : ℝ)^k-1)*Real.sqrt p) ≤ (A.card : ℝ))
    (hpass : ∀ r ∈ tail, ∀ side,
      |((A \ bad r side).card : ℝ) - θ r*A.card| ≤
        θq^2 * θ r * (4 : ℝ)^k * Real.sqrt p)
    (hlarge : ((4 : ℝ)^k * (1+2*(tail.card : ℝ)/delta tail θ)+2)^2 < p) :
    0 < (survivors A tail bad).card := by
  let W : ℝ := 4^k
  let t : ℝ := Real.sqrt p
  let J : ι → Bool → ℝ := fun r side => ((A \ bad r side).card : ℝ)-θ r*A.card
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have ht : 0 ≤ t := Real.sqrt_nonneg p
  have hId : ∀ r ∈ tail, ∀ side,
      ((A \ bad r side).card : ℝ) = θ r*A.card + J r side := by
    intro r hr side
    dsimp [J]
    ring
  have hc := correction_bound A tail bad θ J hsub hId
  have herror : (∑ r ∈ tail, (|J r false|+|J r true|)) ≤
      θq^2 * (2*(tail.card : ℝ)*W*t) := by
    calc
      _ ≤ ∑ r ∈ tail, (2*θq^2*W*t) := by
        apply Finset.sum_le_sum
        intro r hr
        have h0 := hpass r hr false
        have h1 := hpass r hr true
        change |J r false| ≤ θq^2*θ r*W*t at h0
        change |J r true| ≤ θq^2*θ r*W*t at h1
        have htθ : θq^2*θ r*W*t ≤ θq^2*W*t := by
          have h := mul_le_mul_of_nonneg_right (hθ1 r hr)
            (show 0 ≤ θq^2*W*t by positivity)
          nlinarith
        linarith
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hδbase := mul_le_mul_of_nonneg_left hbase hδ.le
  have hlower : θq^2 * (delta tail θ*((p : ℝ)-2) -
      delta tail θ*(W-1)*t - 2*(tail.card : ℝ)*W*t) ≤
      (survivors A tail bad).card := by
    calc
      _ = delta tail θ * (θq^2*((p : ℝ)-2-(W-1)*t)) -
          θq^2*(2*(tail.card : ℝ)*W*t) := by ring
      _ ≤ delta tail θ*A.card - ∑ r ∈ tail, (|J r false|+|J r true|) := by
        linarith
      _ ≤ _ := hc
  have hscalar := threshold_scalar (p : ℝ) W (tail.card : ℝ) (delta tail θ)
    (Nat.cast_nonneg p) hW (Nat.cast_nonneg tail.card) hδ hlarge
  have hpositive := mul_pos (sq_pos_of_pos hθq) hscalar
  have hreal : (0 : ℝ) < (survivors A tail bad).card := hpositive.trans_le hlower
  exact_mod_cast hreal

/-- Actual core/tail witness from the direct lower-count and Jacobi-error
inequalities used by the tensor-character component. -/
theorem exists_core_tail_of_direct_threshold [DecidableEq ι]
    (U : Finset α) (core tail : Finset ι) (free : ι → Bool → α → Prop)
    (θ : ι → ℝ) (θq : ℝ) (p k : ℕ)
    (hθ1 : ∀ r ∈ tail, θ r ≤ 1)
    (hδ : 0 < delta tail θ) (hθq : 0 < θq)
    (hbase : θq^2*((p : ℝ)-2-((4 : ℝ)^k-1)*Real.sqrt p) ≤
      ((coreSet U core free).card : ℝ))
    (hpass : ∀ r ∈ tail, ∀ side,
      |(((coreSet U core free) \ tailBad (coreSet U core free) free r side).card : ℝ) -
        θ r*(coreSet U core free).card| ≤ θq^2*θ r*(4 : ℝ)^k*Real.sqrt p)
    (hlarge : ((4 : ℝ)^k*(1+2*(tail.card : ℝ)/delta tail θ)+2)^2 < p) :
    ∃ x ∈ U, ∀ r ∈ core ∪ tail, ∀ side, free r side x := by
  have hc := direct_card_pos (coreSet U core free) tail
    (tailBad (coreSet U core free) free) θ θq p k
    (fun r _ side => tailBad_subset _ _ r side) hθ1 hδ hθq hbase hpass hlarge
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hc
  exact ⟨x,(mem_core_survivors_iff U core tail free x).mp hx⟩

end A397683Sieve

end

section

namespace A397683LargePrime

/-- A full-order character exists unconditionally; taking its N/r-th powers
supplies every distinct prime-order projector used by the sieve. -/
theorem exists_full_character (p : ℕ) (hp : p.Prime) :
    ∃ χ : MulChar (ZMod p) ℂ, orderOf χ = p-1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hN : p-1 ≠ 0 := by have := hp.two_le; omega
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/(p-1 : ℕ))
  have hζ : IsPrimitiveRoot ζ (p-1) := Complex.isPrimitiveRoot_exp _ hN
  obtain ⟨χ,hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod p)
    (show p-1 ∣ Fintype.card (ZMod p)-1 by simp) hζ
  exact ⟨χ,hχ⟩

theorem prime_component_order (p : ℕ) (hp : p.Prime)
    (χ : MulChar (ZMod p) ℂ) (hχ : orderOf χ = p-1)
    (r : ℕ) (hr : r ∈ (p-1).primeFactors) :
    orderOf (χ ^ ((p-1)/r)) = r := by
  have hN : p-1 ≠ 0 := by have := hp.two_le; omega
  have hd : r ∣ p-1 := Nat.dvd_of_mem_primeFactors hr
  have horder : orderOf χ ≠ 0 := by rwa [hχ]
  have hd' : r ∣ orderOf χ := by rwa [hχ]
  simpa only [hχ] using orderOf_pow_orderOf_div horder hd'

/-- The common full character makes kernel avoidance imply exact primitive
order, with no choice of a unit generator or discrete logarithms needed. -/
theorem primitive_order_of_free (p : ℕ) (hp : p.Prime)
    (χ : MulChar (ZMod p) ℂ) (x : ZMod p) (hx : x ≠ 0)
    (hfree : ∀ r ∈ (p-1).primeFactors, (χ ^ ((p-1)/r)) x ≠ 1) :
    orderOf x = p-1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hN : 0 < p-1 := by have := hp.two_le; omega
  apply orderOf_eq_of_pow_and_pow_div_prime hN
    (by simpa using ZMod.pow_card_sub_one_eq_one hx)
  intro r hr hd hpow
  apply hfree r (Nat.mem_primeFactors.mpr ⟨hr,hd,hN.ne'⟩)
  let u : (ZMod p)ˣ := Units.mk0 x hx
  have he : (χ ^ ((p-1)/r)) x = χ (x ^ ((p-1)/r)) := by
    change (χ ^ ((p-1)/r)) (u : ZMod p) = χ ((u : ZMod p) ^ ((p-1)/r))
    rw [MulChar.pow_apply_coe, map_pow]
  rw [he,hpow]
  exact χ.map_one

end A397683LargePrime

end

section

namespace A397683LargePrime
open Finset A397683Sieve A397683Counts A397683Tensor A397683Threshold

noncomputable def pairUniverse {F : Type*} [Zero F] [One F] [Add F] [Fintype F] : Finset F := by
  classical
  exact univ.filter fun x => x ≠ 0 ∧ x+1 ≠ 0

def freeCondition {F : Type*} [CommRing F] (χ : ℕ → MulChar F ℂ)
    (r : ℕ) (side : Bool) (x : F) : Prop := χ r (if side then x+1 else x) ≠ 1

theorem core_count_eq_pairCount {F : Type*} [Field F] [Fintype F]
    (core : Finset ℕ) (χ : ℕ → MulChar F ℂ) :
    (coreSet (pairUniverse : Finset F) core (freeCondition χ)).card =
      pairCount (fun r : core => χ r) (fun r : core => χ r) := by
  classical
  unfold pairCount
  congr 1
  ext x
  simp [coreSet, pairUniverse, freeCondition, EFree, Bool.forall_bool]
  simp only [forall_and]
  tauto

theorem theta_pos {r : ℕ} (hr : r.Prime) : 0 < A397683Tensor.theta r := by
  unfold A397683Tensor.theta
  apply div_pos
  · exact sub_pos.mpr (by exact_mod_cast hr.one_lt)
  · exact_mod_cast hr.pos

theorem theta_le_one {r : ℕ} (hr : r.Prime) : A397683Tensor.theta r ≤ 1 := by
  unfold A397683Tensor.theta
  apply (div_le_one (by exact_mod_cast hr.pos : (0 : ℝ) < r)).mpr
  linarith

theorem sieve_delta_eq (tail : Finset ℕ) (hprime : ∀ r ∈ tail, r.Prime) :
    A397683Sieve.delta tail A397683Tensor.theta =
      1 - 2*∑ r ∈ tail, (1 : ℝ)/r := by
  unfold A397683Sieve.delta
  congr 2
  apply Finset.sum_congr rfl
  intro r hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (hprime r hr).ne_zero
  unfold A397683Tensor.theta
  field_simp
  ring

theorem pass_count_eq_left {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (core : Finset ℕ) (χ : ℕ → MulChar F ℂ) (r : ℕ) :
    ((coreSet (pairUniverse : Finset F) core (freeCondition χ)) \
      tailBad (coreSet pairUniverse core (freeCondition χ)) (freeCondition χ) r false).card =
      leftPairCount (fun i : core => χ i) (χ r) := by
  classical
  unfold leftPairCount
  congr 1
  ext x
  simp [coreSet, pairUniverse, tailBad, freeCondition, EFree, Bool.forall_bool, forall_and]
  tauto

theorem pass_count_eq_right {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (core : Finset ℕ) (χ : ℕ → MulChar F ℂ) (r : ℕ) :
    ((coreSet (pairUniverse : Finset F) core (freeCondition χ)) \
      tailBad (coreSet pairUniverse core (freeCondition χ)) (freeCondition χ) r true).card =
      rightPairCount (fun i : core => χ i) (χ r) := by
  classical
  unfold rightPairCount
  congr 1
  ext x
  simp [coreSet, pairUniverse, tailBad, freeCondition, EFree, Bool.forall_bool, forall_and]
  tauto

noncomputable def coreTheta (core : Finset ℕ) : ℝ := ∏ r : core, A397683Tensor.theta (r : ℕ)

theorem coreTheta_pos (core : Finset ℕ) (hprime : ∀ r ∈ core, r.Prime) :
    0 < coreTheta core := by
  unfold coreTheta
  exact Finset.prod_pos fun r _ => theta_pos (hprime r r.property)

/-- Actual core lower count from the checked tensor character estimate. -/
theorem core_lower (p : ℕ) [Fact p.Prime] (hp : p.Prime) (χ : MulChar (ZMod p) ℂ)
    (hχ : orderOf χ = p-1) (core : Finset ℕ)
    (hcore : core ⊆ (p-1).primeFactors) :
    (coreTheta core)^2 * ((p : ℝ)-2-((4 : ℝ)^core.card-1)*Real.sqrt p) ≤
      (coreSet (pairUniverse : Finset (ZMod p)) core
        (freeCondition (fun r => χ^((p-1)/r)))).card := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hprime : ∀ r ∈ core, r.Prime := fun r hr =>
    Nat.prime_of_mem_primeFactors (hcore hr)
  have hcop : ∀ i j : core, i ≠ j → Nat.Coprime (i : ℕ) (j : ℕ) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i i.property) (hprime j j.property)).mpr
      (fun he => hij (Subtype.ext he))
  have hc := pairCount_lower (F := ZMod p) (fun r : core => (r : ℕ))
    (fun r : core => χ^((p-1)/(r : ℕ)))
    (fun r => hprime r r.property)
    (fun r => prime_component_order p hp χ hχ r (hcore r.property)) hcop
  have hpow : ((2 : ℝ)^core.card)^2 = (4 : ℝ)^core.card := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [core_count_eq_pairCount]
  simpa only [ZMod.card, Fintype.card_coe, hpow, coreTheta] using hc

/-- Once the direct character count estimates are instantiated, there are
no remaining primitive-order or witness-extraction obligations. -/
theorem primitive_pair_of_sieve_estimates
    (p : ℕ) [Fact p.Prime] (hp : p.Prime) (χ : MulChar (ZMod p) ℂ)
    (core tail : Finset ℕ) (hcore : core ⊆ (p-1).primeFactors)
    (htail : tail ⊆ (p-1).primeFactors)
    (hunion : core ∪ tail = (p-1).primeFactors)
    (hδ : 0 < A397683Sieve.delta tail A397683Tensor.theta)
    (hbase : (coreTheta core)^2 * ((p : ℝ)-2-((4 : ℝ)^core.card-1)*Real.sqrt p) ≤
      (coreSet (pairUniverse : Finset (ZMod p)) core
        (freeCondition (fun r => χ^((p-1)/r)))).card)
    (hpass : ∀ r ∈ tail, ∀ side,
      |(((coreSet (pairUniverse : Finset (ZMod p)) core
          (freeCondition (fun r => χ^((p-1)/r)))) \
        tailBad (coreSet pairUniverse core (freeCondition (fun r => χ^((p-1)/r))))
          (freeCondition (fun r => χ^((p-1)/r))) r side).card : ℝ) -
        A397683Tensor.theta r *
          (coreSet pairUniverse core (freeCondition (fun r => χ^((p-1)/r)))).card| ≤
      (coreTheta core)^2 * A397683Tensor.theta r * (4 : ℝ)^core.card * Real.sqrt p)
    (hlarge : ((4 : ℝ)^core.card *
      (1+2*(tail.card : ℝ)/A397683Sieve.delta tail A397683Tensor.theta)+2)^2 < p) :
    ∃ x : ZMod p, x ≠ 0 ∧ x+1 ≠ 0 ∧ orderOf x = p-1 ∧ orderOf (x+1) = p-1 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hprime : ∀ r ∈ core, r.Prime := fun r hr => Nat.prime_of_mem_primeFactors (hcore hr)
  obtain ⟨x,hx,hfree⟩ := exists_core_tail_of_direct_threshold
    (pairUniverse : Finset (ZMod p)) core tail
    (freeCondition (fun r => χ^((p-1)/r))) A397683Tensor.theta (coreTheta core) p core.card
    (fun r hr => theta_le_one (Nat.prime_of_mem_primeFactors (htail hr)))
    hδ (coreTheta_pos core hprime) hbase hpass hlarge
  have hx0 : x ≠ 0 ∧ x+1 ≠ 0 := by
    simpa only [pairUniverse, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  refine ⟨x,hx0.1,hx0.2,?_,?_⟩
  · apply primitive_order_of_free p hp χ x hx0.1
    intro r hr
    have hm : r ∈ core ∪ tail := by rwa [hunion]
    simpa only [freeCondition, Bool.false_eq_true, if_false] using hfree r hm false
  · apply primitive_order_of_free p hp χ (x+1) hx0.2
    intro r hr
    have hm : r ∈ core ∪ tail := by rwa [hunion]
    simpa only [freeCondition, if_true] using hfree r hm true

/-- The actual two-coordinate passing errors, specialized to all prime
components of one full-order character. -/
theorem passing_error (p : ℕ) [Fact p.Prime] (hp : p.Prime)
    (χ : MulChar (ZMod p) ℂ) (hχ : orderOf χ = p-1)
    (core tail : Finset ℕ) (hcore : core ⊆ (p-1).primeFactors)
    (htail : tail ⊆ (p-1).primeFactors) (hdisj : Disjoint core tail) :
    ∀ r ∈ tail, ∀ side,
      |(((coreSet (pairUniverse : Finset (ZMod p)) core
          (freeCondition (fun r => χ^((p-1)/r)))) \
        tailBad (coreSet pairUniverse core (freeCondition (fun r => χ^((p-1)/r))))
          (freeCondition (fun r => χ^((p-1)/r))) r side).card : ℝ) -
        A397683Tensor.theta r *
          (coreSet pairUniverse core (freeCondition (fun r => χ^((p-1)/r)))).card| ≤
      (coreTheta core)^2 * A397683Tensor.theta r * (4 : ℝ)^core.card * Real.sqrt p := by
  classical
  have hprime : ∀ r ∈ core, r.Prime := fun r hr => Nat.prime_of_mem_primeFactors (hcore hr)
  have hpow : ((2 : ℝ)^core.card)^2 = (4 : ℝ)^core.card := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  intro r hr side
  have hrprime := Nat.prime_of_mem_primeFactors (htail hr)
  have hcop : ∀ i : core, Nat.Coprime (i : ℕ) r := by
    intro i
    apply (Nat.coprime_primes (hprime i i.property) hrprime).mpr
    intro he
    exact Finset.disjoint_left.mp hdisj (he ▸ i.property) hr
  cases side with
  | false =>
    rw [pass_count_eq_left, core_count_eq_pairCount]
    have he := leftPairCount_error (F := ZMod p) (fun i : core => (i : ℕ))
      (fun i : core => χ^((p-1)/(i : ℕ))) (fun i => hprime i i.property)
      (fun i => prime_component_order p hp χ hχ i (hcore i.property))
      (χ^((p-1)/r)) r hrprime (prime_component_order p hp χ hχ r (htail hr)) hcop
    simpa only [ZMod.card, Fintype.card_coe, hpow, coreTheta] using he
  | true =>
    rw [pass_count_eq_right, core_count_eq_pairCount]
    have he := rightPairCount_error (F := ZMod p) (fun i : core => (i : ℕ))
      (fun i : core => χ^((p-1)/(i : ℕ))) (fun i => hprime i i.property)
      (fun i => prime_component_order p hp χ hχ i (hcore i.property))
      (χ^((p-1)/r)) r hrprime (prime_component_order p hp χ hχ r (htail hr)) hcop
    simpa only [ZMod.card, Fintype.card_coe, hpow, coreTheta] using he

/-- Unconditional consecutive primitive roots in the large residue classes
needed by the A397683 argument. There are no character-sum hypotheses. -/
theorem large_prime (p : ℕ) (hp : p.Prime) (hlarge : 260000 ≤ p)
    (hres : p % 20 = 3 ∨ p % 20 = 7) :
    ∃ x : ZMod p, x ≠ 0 ∧ x+1 ≠ 0 ∧ orderOf x = p-1 ∧ orderOf (x+1) = p-1 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨χ,hχ⟩ := exists_full_character p hp
  obtain ⟨k,hk,hd,hbound⟩ := primeFactors_real_eligible p hlarge hres
  let core := factorCore (p-1) k
  let tail := factorTail (p-1) k
  have hcore : core ⊆ (p-1).primeFactors := factorCore_subset _ _ hk
  have htail : tail ⊆ (p-1).primeFactors := factorTail_subset _ _
  have hprime : ∀ r ∈ tail, r.Prime := fun r hr => Nat.prime_of_mem_primeFactors (htail hr)
  have hδeq := sieve_delta_eq tail hprime
  have hδ : 0 < A397683Sieve.delta tail A397683Tensor.theta := by
    rw [hδeq]
    exact hd
  have hbound' : ((4 : ℝ)^core.card *
      (1+2*(tail.card : ℝ)/A397683Sieve.delta tail A397683Tensor.theta)+2)^2 < p := by
    rw [hδeq]
    exact hbound
  exact primitive_pair_of_sieve_estimates p hp χ core tail hcore htail
    (factorCore_union_factorTail _ _ hk) hδ (core_lower p hp χ hχ core hcore)
    (passing_error p hp χ hχ core tail hcore htail (factorCore_disjoint_factorTail _ _ hk)) hbound'

end A397683LargePrime

end

section

namespace A397683FastFactors

/-- Structurally recursive odd trial division. The fuel256 reaches513. -/
def oddTrial (n d : ℕ) : ℕ → Bool
  | 0 => true
  | fuel+1 => if n < d*d then true else
      if n % d = 0 then false else oddTrial n (d+2) fuel

/-- Bounded primality certificate for the finite range used by A397683. -/
def fastPrime (n : ℕ) : Bool :=
  decide (2 ≤ n ∧ n ≤ 260000) &&
    if n = 2 then true else decide (n % 2 = 1) && oddTrial n 3 256

lemma oddTrial_sound {n d fuel : ℕ} (h : oddTrial n d fuel = true) :
    ∀ j < fuel, (d+2*j)^2 ≤ n → ¬ (d+2*j) ∣ n := by
  induction fuel generalizing d with
  | zero => intro j hj; omega
  | succ fuel ih =>
    intro j hj hsq hdiv
    simp only [oddTrial] at h
    split_ifs at h with hstop hmod
    · have hd : d ≤ d+2*j := by omega
      nlinarith
    · cases j with
      | zero =>
        simp only [Nat.mul_zero, Nat.add_zero] at hdiv
        exact hmod (Nat.mod_eq_zero_of_dvd hdiv)
      | succ j =>
        have heq : d+2*(j+1) = (d+2)+2*j := by omega
        apply ih h j (by omega)
        · simpa only [heq] using hsq
        · simpa only [heq] using hdiv

/-- Soundness is proved once; concrete certificates use ordinary `decide`. -/
theorem fastPrime_sound {n : ℕ} (h : fastPrime n = true) : n.Prime := by
  unfold fastPrime at h
  obtain ⟨hn, ht⟩ := Bool.and_eq_true_iff.mp h
  have hn' : 2 ≤ n ∧ n ≤ 260000 := of_decide_eq_true hn
  split_ifs at ht with heq
  · subst n
    exact Nat.prime_two
  obtain ⟨hodd, htrial⟩ := Bool.and_eq_true_iff.mp ht
  have hodd' : n % 2 = 1 := of_decide_eq_true hodd
  by_contra hnprime
  let m := n.minFac
  have hmprime : m.Prime := Nat.minFac_prime (by omega : n ≠ 1)
  have hmdiv : m ∣ n := Nat.minFac_dvd n
  have hmsq : m^2 ≤ n := Nat.minFac_sq_le_self (by omega) hnprime
  have hm2 : m ≠ 2 := by
    intro hm
    have hh : n % 2 = 0 := Nat.mod_eq_zero_of_dvd (hm ▸ hmdiv)
    omega
  have hmlo : 3 ≤ m := by have := hmprime.two_le; omega
  have hmhi : m ≤ 509 := by nlinarith [hn'.2]
  have hmod : m % 2 = 1 := Nat.odd_iff.mp (hmprime.odd_of_ne_two hm2)
  have he : m = 3+2*((m-3)/2) := by omega
  apply oddTrial_sound htrial ((m-3)/2) (by omega)
  · simpa only [← he] using hmsq
  · simpa only [← he] using hmdiv

/-- Supplied prime factors include multiplicity, so their product is n. -/
def factorCert (n : ℕ) (factors : List ℕ) : Bool :=
  decide (factors.prod = n) && factors.all fastPrime

lemma factorCert_product {n : ℕ} {factors : List ℕ} (h : factorCert n factors = true) :
    factors.prod = n :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

lemma factorCert_prime {n q : ℕ} {factors : List ℕ} (h : factorCert n factors = true)
    (hq : q ∈ factors) : q.Prime := by
  have hall : factors.all fastPrime = true := (Bool.and_eq_true_iff.mp h).2
  exact fastPrime_sound (List.all_eq_true.mp hall q hq)

lemma prime_dvd_product_mem {q : ℕ} (hq : q.Prime) (factors : List ℕ)
    (hp : ∀ r ∈ factors, r.Prime) (hdiv : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil =>
    simp only [List.prod_nil] at hdiv
    exact (hq.not_dvd_one hdiv).elim
  | cons a factors ih =>
    simp only [List.prod_cons] at hdiv
    rcases hq.dvd_mul.mp hdiv with ha | ht
    · exact List.mem_cons.mpr (.inl ((Nat.prime_dvd_prime_iff_eq hq (hp a (by simp))).mp ha))
    · exact List.mem_cons.mpr (.inr (ih (fun r hr => hp r (by simp [hr])) ht))

/-- Every prime divisor is covered, without evaluating primeFactorsList. -/
theorem factorCert_covers {n q : ℕ} {factors : List ℕ}
    (h : factorCert n factors = true) (hq : q.Prime) (hdiv : q ∣ n) : q ∈ factors := by
  apply prime_dvd_product_mem hq factors (fun r hr => factorCert_prime h hr)
  rwa [factorCert_product h]

end A397683FastFactors

end

section

namespace ConsecutiveOrder


/-- Binary modular powering with a structural recursion on the exponent bit bound. -/
def modPow (p x n : ℕ) : ℕ → ℕ
  | 0 => 1 % p
  | f + 1 =>
    let y := modPow p x (n/2) f
    if n%2 = 0 then (y*y)%p else (y*y*x)%p

theorem modPow_lt {p x n f : ℕ} (hp : 0 < p) : modPow p x n f < p := by
  cases f with
  | zero => exact Nat.mod_lt _ hp
  | succ f =>
    rw [modPow]
    split <;> exact Nat.mod_lt _ hp

theorem modPow_cast (p x f n : ℕ) (hn : n < 2^f) :
    (modPow p x n f : ZMod p) = (x : ZMod p)^n := by
  induction f generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    simp [modPow, ZMod.natCast_mod]
  | succ f ih =>
    have hh : n/2 < 2^f := by rw [pow_succ] at hn; omega
    rw [modPow]
    split <;> rename_i h
    · rw [ZMod.natCast_mod, Nat.cast_mul, ih _ hh, ← pow_add,
        show n/2+n/2 = n by omega]
    · rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_mul, ih _ hh, ← pow_add, ← pow_succ,
        show n/2+n/2+1 = n by omega]

theorem modPow_eq_one {p x f n : ℕ} (hp : 1 < p) (hn : n < 2^f) :
    modPow p x n f = 1 ↔ (x : ZMod p)^n = 1 := by
  rw [← modPow_cast p x f n hn]
  constructor
  · intro h
    rw [h, Nat.cast_one]
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (modPow_lt (by omega : 0 < p)),
      ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp] at hv
    exact hv

/-- To certify an exact order, check one proper exponent for each prime divisor. -/
theorem order_eq_of_factor_tests {G : Type*} [Monoid G] {x : G} {n : ℕ} (hn : 0 < n)
    (hpow : x^n = 1) (hfac : ∀ q ∈ n.primeFactors, x^(n/q) ≠ 1) : orderOf x = n := by
  obtain ⟨c,hc⟩ := orderOf_dvd_of_pow_eq_one hpow
  by_contra hne
  have hc₁ : 1 < c := by
    by_contra! h
    have hh : c=1 := by
      by_cases hc₀ : c=0
      · simp [hc₀] at hc
        omega
      omega
    exact hne (by simpa [hh] using hc.symm)
  obtain ⟨q,hq,⟨b,hb⟩⟩ := Nat.exists_prime_and_dvd (by omega : c ≠ 1)
  have hmul : n = (orderOf x*b)*q := by
    rw [hc,hb,mul_comm q b,← mul_assoc]
  have hqn : q ∣ n := ⟨orderOf x*b, hmul.trans (mul_comm _ _)⟩
  have hqmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,hqn,hn.ne'⟩
  apply hfac q hqmem
  rw [hmul,Nat.mul_div_cancel _ hq.pos,pow_mul,pow_orderOf_eq_one,one_pow]

/-- Test a candidate given an independently checked list of all prime factors of p−1. -/
def orderTest (p x : ℕ) (factors : List ℕ) : Bool :=
  (modPow p x (p-1) 19 == 1) &&
  factors.all (fun q => modPow p x ((p-1)/q) 19 != 1)

theorem orderTest_sound {p x : ℕ} {factors : List ℕ} (hp : 1 < p) (hb : p ≤ 260000)
    (hf : A397683FastFactors.factorCert (p-1) factors = true)
    (h : orderTest p x factors = true) : orderOf (x : ZMod p) = p-1 := by
  rw [orderTest,Bool.and_eq_true] at h
  have hpow := (modPow_eq_one hp (by omega : p-1 < 2^19)).mp (beq_iff_eq.mp h.1)
  apply order_eq_of_factor_tests (by omega) hpow
  intro q hq
  obtain ⟨hq',hqd,_⟩ := Nat.mem_primeFactors.mp hq
  have hqmem := A397683FastFactors.factorCert_covers hf hq' hqd
  have hq'' := List.all_eq_true.mp h.2 q hqmem
  have hbound := (Nat.div_le_self (p-1) q).trans_lt (by omega : p-1 < 2^19)
  exact fun he => (bne_iff_ne.mp hq'') ((modPow_eq_one hp hbound).mpr he)

/-- Check one adjacent pair, independently of how the candidate was found. -/
def pairTest (p x : ℕ) (factors : List ℕ) : Bool :=
  decide (1 ≤ x ∧ x+1 < p) && A397683FastFactors.factorCert (p-1) factors &&
    (orderTest p x factors && orderTest p (x+1) factors)

/-- Multiples of 20 with remainders 3 or 7, grouped 100 entries per block. -/
def atResidue (b j : ℕ) : ℕ :=
  b*1000 + 20*(j/2) + if j%2 = 0 then 3 else 7

/-- Values ≥128 are proper divisors plus 128. The remaining values are pair candidates. -/
def checkAt (p : ℕ) (c : ℕ × List ℕ) : Bool :=
  if p < 170 then true else
    if c.1 < 128 then pairTest p c.1 c.2
    else (2 ≤ c.1 - 128 && c.1 - 128 < p && p % (c.1 - 128) == 0)

def checkBlock (b : ℕ) (data : List (ℕ × List ℕ)) : Bool :=
  (data.length == 100) &&
    ((List.range 100).zip data).all (fun jc => checkAt (atResidue b jc.1) jc.2)

theorem checkBlock_sound {b : ℕ} {data : List (ℕ × List ℕ)} {j : ℕ}
    (h : checkBlock b data = true) {p : ℕ} (he : p = atResidue b j)
    (hj : j < 100) (hp : p.Prime) (h170 : 170 ≤ p) (hb : p ≤ 260000) :
    ∃ x : ℕ, 1 ≤ x ∧ x+1 < p ∧ orderOf (x : ZMod p) = p-1 ∧
      orderOf ((x+1 : ℕ) : ZMod p) = p-1 := by
  rw [checkBlock,Bool.and_eq_true] at h
  have hlen : data.length = 100 := beq_iff_eq.mp h.1
  have hj' : j < data.length := hlen ▸ hj
  have hm : (j, data[j]) ∈ (List.range 100).zip data := by
    apply List.mem_iff_getElem.mpr
    have hzip : j < ((List.range 100).zip data).length := by simpa [hlen] using hj
    exact ⟨j, hzip, by simp [List.getElem_zip]⟩
  have hh := List.all_eq_true.mp h.2 (j, data[j]) hm
  change checkAt (atResidue b j) data[j] = true at hh
  rw [← he, checkAt, if_neg (by omega : ¬p < 170)] at hh
  split at hh <;> rename_i hcut
  swap
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
    have hn := (Nat.prime_def_lt.mp hp).2 _ hh.1.2 (Nat.dvd_of_mod_eq_zero hh.2)
    omega
  rw [pairTest, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hh
  have hx := of_decide_eq_true hh.1.1
  exact ⟨_,hx.1,hx.2,orderTest_sound hp.one_lt hb hh.1.2 hh.2.1,
    orderTest_sound hp.one_lt hb hh.1.2 hh.2.2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock0 : ∃ data, checkBlock 0 data = true :=
  ⟨[(0,[]),(0,[]),(0,[]),(0,[]),(0,[]),
    (0,[]),(0,[]),(0,[]),(0,[]),(0,[]),
    (0,[]),(0,[]),(0,[]),(0,[]),(0,[]),
    (0,[]),(0,[]),(0,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(5,[2,3,37]),(5,[2,113]),(131,[]),
    (141,[]),(14,[2,131]),(131,[]),(17,[2,3,47]),(135,[]),
    (131,[]),(13,[2,3,3,17]),(145,[]),(131,[]),(135,[]),
    (5,[2,173]),(131,[]),(10,[2,3,61]),(10,[2,191]),(131,[]),
    (141,[]),(139,[]),(131,[]),(135,[]),(5,[2,13,17]),
    (131,[]),(19,[2,3,7,11]),(5,[2,233]),(131,[]),(10,[2,3,3,3,3,3]),
    (19,[2,251]),(131,[]),(21,[2,3,3,29]),(145,[]),(131,[]),
    (17,[2,3,7,13]),(5,[2,281]),(131,[]),(139,[]),(5,[2,293]),
    (131,[]),(20,[2,3,101]),(135,[]),(131,[]),(13,[2,3,107]),
    (10,[2,17,19]),(131,[]),(151,[]),(5,[2,11,31]),(131,[]),
    (147,[]),(135,[]),(131,[]),(19,[2,3,11,11]),(13,[2,7,53]),
    (131,[]),(135,[]),(141,[]),(131,[]),(12,[2,3,131]),
    (139,[]),(131,[]),(6,[2,3,137]),(6,[2,7,59]),(131,[]),
    (135,[]),(10,[2,431]),(131,[]),(41,[2,3,3,7,7]),(29,[2,443]),
    (131,[]),(2,[2,3,151]),(141,[]),(131,[]),(151,[]),
    (5,[2,11,43]),(131,[]),(5,[2,3,7,23]),(10,[2,491]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock1 : ∃ data, checkBlock 1 data = true :=
  ⟨[(145,[]),(147,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(20,[2,3,3,59]),(139,[]),(131,[]),(12,[2,3,181]),
    (10,[2,19,29]),(131,[]),(2,[2,3,11,17]),(135,[]),(131,[]),
    (159,[]),(5,[2,7,83]),(131,[]),(135,[]),(5,[2,593]),
    (131,[]),(145,[]),(19,[2,13,47]),(131,[]),(139,[]),
    (157,[]),(131,[]),(135,[]),(5,[2,641]),(131,[]),
    (6,[2,3,7,31]),(5,[2,653]),(131,[]),(5,[2,3,13,17]),(145,[]),
    (131,[]),(157,[]),(10,[2,683]),(131,[]),(147,[]),
    (151,[]),(131,[]),(11,[2,3,3,79]),(5,[2,23,31]),(131,[]),
    (20,[2,3,241]),(135,[]),(131,[]),(2,[2,3,13,19]),(19,[2,743]),
    (131,[]),(139,[]),(5,[2,761]),(131,[]),(5,[2,3,257]),
    (135,[]),(131,[]),(5,[2,3,3,3,29]),(14,[2,7,113]),(131,[]),
    (135,[]),(10,[2,11,73]),(131,[]),(17,[2,3,271]),(159,[]),
    (131,[]),(5,[2,3,277]),(5,[2,7,7,17]),(131,[]),(135,[]),
    (141,[]),(131,[]),(17,[2,3,7,41]),(139,[]),(131,[]),
    (2,[2,3,3,97]),(169,[]),(131,[]),(10,[2,3,3,3,3,11]),(7,[2,19,47]),
    (131,[]),(141,[]),(30,[2,911]),(131,[]),(147,[]),
    (19,[2,13,71]),(131,[]),(12,[2,3,311]),(135,[]),(131,[]),
    (139,[]),(5,[2,953]),(131,[]),(169,[]),(157,[]),
    (131,[]),(141,[]),(135,[]),(131,[]),(2,[2,3,331])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock2 : ∃ data, checkBlock 2 data = true :=
  ⟨[(28,[2,7,11,13]),(131,[]),(135,[]),(5,[2,1013]),(131,[]),
    (151,[]),(19,[2,1031]),(131,[]),(2,[2,3,347]),(13,[2,7,149]),
    (131,[]),(135,[]),(139,[]),(131,[]),(5,[2,3,3,7,17]),
    (147,[]),(131,[]),(139,[]),(165,[]),(131,[]),
    (20,[2,3,367]),(14,[2,1103]),(131,[]),(145,[]),(5,[2,19,59]),
    (131,[]),(159,[]),(5,[2,11,103]),(131,[]),(38,[2,3,3,127]),
    (135,[]),(131,[]),(151,[]),(141,[]),(131,[]),
    (11,[2,3,17,23]),(145,[]),(131,[]),(34,[2,3,397]),(135,[]),
    (131,[]),(157,[]),(10,[2,7,173]),(131,[]),(135,[]),
    (10,[2,1223]),(131,[]),(2,[2,3,3,137]),(141,[]),(131,[]),
    (5,[2,3,3,139]),(151,[]),(131,[]),(135,[]),(13,[2,31,41]),
    (131,[]),(139,[]),(145,[]),(131,[]),(141,[]),
    (147,[]),(131,[]),(171,[]),(165,[]),(131,[]),
    (23,[2,3,3,3,7,7]),(10,[2,11,11,11]),(131,[]),(2,[2,3,3,149]),(10,[2,17,79]),
    (131,[]),(2,[2,3,11,41]),(135,[]),(131,[]),(141,[]),
    (169,[]),(131,[]),(5,[2,3,461]),(139,[]),(131,[]),
    (11,[2,3,467]),(135,[]),(131,[]),(139,[]),(5,[2,7,7,29]),
    (131,[]),(135,[]),(175,[]),(131,[]),(5,[2,3,13,37]),
    (29,[2,1451]),(131,[]),(165,[]),(10,[2,7,11,19]),(131,[]),
    (135,[]),(5,[2,1481]),(131,[]),(147,[]),(157,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock3 : ∃ data, checkBlock 3 data = true :=
  ⟨[(131,[]),(159,[]),(10,[2,1511]),(131,[]),(145,[]),
    (139,[]),(131,[]),(38,[2,3,7,73]),(5,[2,23,67]),(131,[]),
    (157,[]),(141,[]),(131,[]),(181,[]),(135,[]),
    (131,[]),(18,[2,3,17,31]),(30,[2,1583]),(131,[]),(12,[2,3,3,3,59]),
    (5,[2,1601]),(131,[]),(139,[]),(135,[]),(131,[]),
    (145,[]),(141,[]),(131,[]),(135,[]),(147,[]),
    (131,[]),(2,[2,3,19,29]),(5,[2,11,151]),(131,[]),(13,[2,3,557]),
    (5,[2,7,239]),(131,[]),(135,[]),(145,[]),(131,[]),
    (169,[]),(30,[2,13,131]),(131,[]),(151,[]),(139,[]),
    (131,[]),(5,[2,3,577]),(5,[2,1733]),(131,[]),(139,[]),
    (159,[]),(131,[]),(141,[]),(29,[2,41,43]),(131,[]),
    (2,[2,3,3,197]),(135,[]),(131,[]),(5,[2,3,3,199]),(145,[]),
    (131,[]),(13,[2,3,601]),(10,[2,1811]),(131,[]),(2,[2,3,607]),
    (135,[]),(131,[]),(147,[]),(157,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(10,[2,3,3,3,3,23]),(147,[]),
    (131,[]),(181,[]),(10,[2,7,269]),(131,[]),(135,[]),
    (5,[2,1901]),(131,[]),(47,[2,3,7,7,13]),(171,[]),(131,[]),
    (5,[2,3,641]),(19,[2,1931]),(131,[]),(139,[]),(141,[]),
    (131,[]),(17,[2,3,3,7,31]),(14,[2,37,53]),(131,[]),(5,[2,3,3,3,73]),
    (5,[2,1973]),(131,[]),(12,[2,3,661]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock4 : ∃ data, checkBlock 4 data = true :=
  ⟨[(2,[2,3,23,29]),(10,[2,2003]),(131,[]),(11,[2,3,11,61]),(141,[]),
    (131,[]),(145,[]),(135,[]),(131,[]),(189,[]),
    (139,[]),(131,[]),(135,[]),(13,[2,2063]),(131,[]),
    (139,[]),(151,[]),(131,[]),(175,[]),(181,[]),
    (131,[]),(135,[]),(169,[]),(131,[]),(2,[2,3,7,101]),
    (159,[]),(131,[]),(145,[]),(5,[2,2141]),(131,[]),
    (141,[]),(187,[]),(131,[]),(6,[2,3,7,103]),(171,[]),
    (131,[]),(2,[2,3,727]),(139,[]),(131,[]),(169,[]),
    (135,[]),(131,[]),(5,[2,3,11,67]),(147,[]),(131,[]),
    (6,[2,3,3,13,19]),(14,[2,23,97]),(131,[]),(17,[2,3,3,3,83]),(135,[]),
    (131,[]),(2,[2,3,751]),(5,[2,7,17,19]),(131,[]),(135,[]),
    (5,[2,2273]),(131,[]),(5,[2,3,761]),(19,[2,29,79]),(131,[]),
    (2,[2,3,13,59]),(145,[]),(131,[]),(135,[]),(5,[2,11,211]),
    (131,[]),(6,[2,3,3,7,37]),(141,[]),(131,[]),(171,[]),
    (34,[2,2351]),(131,[]),(2,[2,3,787]),(157,[]),(131,[]),
    (175,[]),(139,[]),(131,[]),(10,[2,3,797]),(5,[2,2393]),
    (131,[]),(139,[]),(135,[]),(131,[]),(157,[]),
    (165,[]),(131,[]),(159,[]),(147,[]),(131,[]),
    (19,[2,3,19,43]),(135,[]),(131,[]),(141,[]),(10,[2,7,353]),
    (131,[]),(135,[]),(20,[2,13,191]),(131,[]),(2,[2,3,3,277])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock5 : ∃ data, checkBlock 5 data = true :=
  ⟨[(5,[2,41,61]),(131,[]),(19,[2,3,3,3,3,31]),(139,[]),(131,[]),
    (135,[]),(189,[]),(131,[]),(141,[]),(10,[2,2543]),
    (131,[]),(12,[2,3,23,37]),(175,[]),(131,[]),(165,[]),
    (5,[2,31,83]),(131,[]),(12,[2,3,3,7,41]),(199,[]),(131,[]),
    (139,[]),(169,[]),(131,[]),(22,[2,3,13,67]),(135,[]),
    (131,[]),(147,[]),(151,[]),(131,[]),(145,[]),
    (10,[2,11,241]),(131,[]),(33,[2,3,887]),(135,[]),(131,[]),
    (11,[2,3,3,3,3,3,11]),(159,[]),(131,[]),(135,[]),(5,[2,2693]),
    (131,[]),(20,[2,3,17,53]),(139,[]),(131,[]),(2,[2,3,907]),
    (141,[]),(131,[]),(135,[]),(5,[2,2741]),(131,[]),
    (10,[2,3,7,131]),(5,[2,2753]),(131,[]),(5,[2,3,3,307]),(151,[]),
    (131,[]),(2,[2,3,3,3,103]),(147,[]),(131,[]),(165,[]),
    (141,[]),(131,[]),(5,[2,3,937]),(145,[]),(131,[]),
    (5,[2,3,941]),(135,[]),(131,[]),(2,[2,3,947]),(139,[]),
    (131,[]),(141,[]),(187,[]),(131,[]),(10,[2,3,3,11,29]),
    (135,[]),(131,[]),(201,[]),(19,[2,7,7,59]),(131,[]),
    (135,[]),(14,[2,2903]),(131,[]),(2,[2,3,971]),(5,[2,23,127]),
    (131,[]),(139,[]),(5,[2,7,419]),(131,[]),(135,[]),
    (14,[2,13,227]),(131,[]),(2,[2,3,3,7,47]),(10,[2,2963]),(131,[]),
    (147,[]),(195,[]),(131,[]),(159,[]),(5,[2,41,73])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock6 : ∃ data, checkBlock 6 data = true :=
  ⟨[(131,[]),(5,[2,3,7,11,13]),(147,[]),(131,[]),(12,[2,3,19,53]),
    (19,[2,3023]),(131,[]),(18,[2,3,3,337]),(135,[]),(131,[]),
    (145,[]),(159,[]),(131,[]),(139,[]),(10,[2,37,83]),
    (131,[]),(11,[2,3,13,79]),(135,[]),(131,[]),(151,[]),
    (7,[2,7,443]),(131,[]),(135,[]),(141,[]),(131,[]),
    (5,[2,3,3,347]),(10,[2,31,101]),(131,[]),(189,[]),(14,[2,7,449]),
    (131,[]),(135,[]),(5,[2,29,109]),(131,[]),(45,[2,3,7,151]),
    (139,[]),(131,[]),(5,[2,3,1061]),(141,[]),(131,[]),
    (147,[]),(171,[]),(131,[]),(28,[2,3,3,3,7,17]),(145,[]),
    (131,[]),(151,[]),(157,[]),(131,[]),(141,[]),
    (135,[]),(131,[]),(139,[]),(189,[]),(131,[]),
    (2,[2,3,1091]),(20,[2,17,193]),(131,[]),(157,[]),(135,[]),
    (131,[]),(5,[2,3,3,367]),(165,[]),(131,[]),(135,[]),
    (145,[]),(131,[]),(187,[]),(169,[]),(131,[]),
    (5,[2,3,1117]),(147,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(2,[2,3,7,7,23]),(195,[]),(131,[]),(139,[]),
    (5,[2,19,179]),(131,[]),(12,[2,3,3,379]),(5,[2,3413]),(131,[]),
    (169,[]),(29,[2,47,73]),(131,[]),(18,[2,3,31,37]),(199,[]),
    (131,[]),(2,[2,3,1151]),(135,[]),(131,[]),(181,[]),
    (5,[2,23,151]),(131,[]),(10,[2,3,3,3,3,43]),(10,[2,3491]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock7 : ∃ data, checkBlock 7 data = true :=
  ⟨[(175,[]),(135,[]),(131,[]),(11,[2,3,1171]),(5,[2,7,503]),
    (131,[]),(135,[]),(165,[]),(131,[]),(147,[]),
    (19,[2,53,67]),(131,[]),(145,[]),(14,[2,7,509]),(131,[]),
    (135,[]),(141,[]),(131,[]),(139,[]),(5,[2,3593]),
    (131,[]),(6,[2,3,1201]),(159,[]),(131,[]),(2,[2,3,17,71]),
    (10,[2,3623]),(131,[]),(141,[]),(5,[2,11,331]),(131,[]),
    (195,[]),(5,[2,13,281]),(131,[]),(145,[]),(135,[]),
    (131,[]),(165,[]),(181,[]),(131,[]),(211,[]),
    (139,[]),(131,[]),(141,[]),(135,[]),(131,[]),
    (139,[]),(145,[]),(131,[]),(135,[]),(14,[2,19,197]),
    (131,[]),(12,[2,3,3,3,139]),(5,[2,3761]),(131,[]),(147,[]),
    (5,[2,7,7,7,11]),(131,[]),(135,[]),(10,[2,17,223]),(131,[]),
    (2,[2,3,7,181]),(19,[2,3803]),(131,[]),(157,[]),(5,[2,3821]),
    (131,[]),(207,[]),(139,[]),(131,[]),(10,[2,3,3,7,61]),
    (10,[2,3851]),(131,[]),(11,[2,3,3,3,11,13]),(10,[2,3863]),(131,[]),
    (189,[]),(135,[]),(131,[]),(171,[]),(141,[]),
    (131,[]),(165,[]),(14,[2,3911]),(131,[]),(139,[]),
    (135,[]),(131,[]),(13,[2,3,3,19,23]),(7,[2,7,563]),(131,[]),
    (135,[]),(5,[2,59,67]),(131,[]),(5,[2,3,1321]),(141,[]),
    (131,[]),(77,[2,3,1327]),(159,[]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock8 : ∃ data, checkBlock 8 data = true :=
  ⟨[(181,[]),(131,[]),(199,[]),(151,[]),(131,[]),
    (141,[]),(139,[]),(131,[]),(187,[]),(20,[2,13,311]),
    (131,[]),(139,[]),(5,[2,31,131]),(131,[]),(145,[]),
    (5,[2,4073]),(131,[]),(38,[2,3,1361]),(135,[]),(131,[]),
    (141,[]),(157,[]),(131,[]),(147,[]),(5,[2,13,317]),
    (131,[]),(40,[2,3,3,3,3,3,17]),(135,[]),(131,[]),(5,[2,3,1381]),
    (147,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (145,[]),(14,[2,37,113]),(131,[]),(211,[]),(5,[2,7,599]),
    (131,[]),(135,[]),(14,[2,4211]),(131,[]),(2,[2,3,3,7,67]),
    (19,[2,41,103]),(131,[]),(2,[2,3,17,83]),(145,[]),(131,[]),
    (139,[]),(175,[]),(131,[]),(5,[2,3,7,7,29]),(29,[2,4271]),
    (131,[]),(2,[2,3,1427]),(141,[]),(131,[]),(159,[]),
    (135,[]),(131,[]),(5,[2,3,3,479]),(5,[2,19,227]),(131,[]),
    (5,[2,3,11,131]),(13,[2,61,71]),(131,[]),(147,[]),(135,[]),
    (131,[]),(19,[2,3,1451]),(139,[]),(131,[]),(135,[]),
    (5,[2,4373]),(131,[]),(139,[]),(10,[2,4391]),(131,[]),
    (12,[2,3,3,3,163]),(14,[2,7,17,37]),(131,[]),(135,[]),(165,[]),
    (131,[]),(5,[2,3,7,211]),(23,[2,11,13,31]),(131,[]),(12,[2,3,1481]),
    (157,[]),(131,[]),(2,[2,3,1487]),(207,[]),(131,[]),
    (151,[]),(5,[2,4481]),(131,[]),(141,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock9 : ∃ data, checkBlock 9 data = true :=
  ⟨[(131,[]),(12,[2,3,19,79]),(135,[]),(131,[]),(56,[2,3,11,137]),
    (211,[]),(131,[]),(12,[2,3,1511]),(159,[]),(131,[]),
    (20,[2,3,37,41]),(135,[]),(131,[]),(19,[2,3,3,3,13,13]),(169,[]),
    (131,[]),(135,[]),(217,[]),(131,[]),(20,[2,3,1531]),
    (5,[2,43,107]),(131,[]),(151,[]),(5,[2,7,659]),(131,[]),
    (135,[]),(187,[]),(131,[]),(2,[2,3,7,13,17]),(165,[]),
    (131,[]),(169,[]),(5,[2,59,79]),(131,[]),(5,[2,3,3,3,173]),
    (141,[]),(131,[]),(145,[]),(139,[]),(131,[]),
    (11,[2,3,1567]),(151,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(11,[2,3,19,83]),(5,[2,4733]),(131,[]),(181,[]),
    (141,[]),(131,[]),(217,[]),(135,[]),(131,[]),
    (2,[2,3,37,43]),(201,[]),(131,[]),(135,[]),(5,[2,4793]),
    (131,[]),(141,[]),(10,[2,17,283]),(131,[]),(2,[2,3,1607]),
    (139,[]),(131,[]),(135,[]),(151,[]),(131,[]),
    (159,[]),(145,[]),(131,[]),(199,[]),(30,[2,4871]),
    (131,[]),(141,[]),(19,[2,19,257]),(131,[]),(29,[2,3,7,233]),
    (5,[2,13,13,29]),(131,[]),(139,[]),(159,[]),(131,[]),
    (171,[]),(135,[]),(131,[]),(2,[2,3,3,3,3,61]),(10,[2,4943]),
    (131,[]),(2,[2,3,13,127]),(6,[2,11,11,41]),(131,[]),(189,[]),
    (135,[]),(131,[]),(5,[2,3,11,151]),(195,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock10 : ∃ data, checkBlock 10 data = true :=
  ⟨[(135,[]),(14,[2,5003]),(131,[]),(165,[]),(139,[]),
    (131,[]),(157,[]),(5,[2,7,719]),(131,[]),(135,[]),
    (10,[2,5051]),(131,[]),(181,[]),(141,[]),(131,[]),
    (201,[]),(5,[2,5081]),(131,[]),(145,[]),(189,[]),
    (131,[]),(187,[]),(10,[2,19,269]),(131,[]),(37,[2,3,3,569]),
    (19,[2,47,109]),(131,[]),(11,[2,3,29,59]),(135,[]),(131,[]),
    (37,[2,3,17,101]),(139,[]),(131,[]),(151,[]),(10,[2,5171]),
    (131,[]),(171,[]),(135,[]),(131,[]),(141,[]),
    (229,[]),(131,[]),(135,[]),(5,[2,13,401]),(131,[]),
    (159,[]),(30,[2,5231]),(131,[]),(139,[]),(10,[2,7,7,107]),
    (131,[]),(135,[]),(145,[]),(131,[]),(141,[]),
    (181,[]),(131,[]),(6,[2,3,3,587]),(147,[]),(131,[]),
    (151,[]),(10,[2,5303]),(131,[]),(42,[2,3,7,11,23]),(157,[]),
    (131,[]),(5,[2,3,1777]),(5,[2,5333]),(131,[]),(5,[2,3,13,137]),
    (135,[]),(131,[]),(2,[2,3,1787]),(145,[]),(131,[]),
    (139,[]),(175,[]),(131,[]),(169,[]),(135,[]),
    (131,[]),(229,[]),(207,[]),(131,[]),(135,[]),
    (10,[2,11,17,29]),(131,[]),(32,[2,3,1811]),(5,[2,5441]),(131,[]),
    (5,[2,3,23,79]),(141,[]),(131,[]),(135,[]),(159,[]),
    (131,[]),(147,[]),(139,[]),(131,[]),(11,[2,3,1831])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock11 : ∃ data, checkBlock 11 data = true :=
  ⟨[(5,[2,5501]),(131,[]),(201,[]),(5,[2,37,149]),(131,[]),
    (10,[2,3,7,263]),(141,[]),(131,[]),(31,[2,3,1847]),(30,[2,23,241]),
    (131,[]),(157,[]),(135,[]),(131,[]),(139,[]),
    (199,[]),(131,[]),(141,[]),(181,[]),(131,[]),
    (145,[]),(135,[]),(131,[]),(231,[]),(20,[2,7,11,73]),
    (131,[]),(135,[]),(147,[]),(131,[]),(5,[2,3,3,3,11,19]),
    (217,[]),(131,[]),(141,[]),(175,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(5,[2,3,7,271]),(187,[]),
    (131,[]),(139,[]),(10,[2,5711]),(131,[]),(2,[2,3,1907]),
    (13,[2,59,97]),(131,[]),(28,[2,3,3,7,7,13]),(5,[2,5741]),(131,[]),
    (6,[2,3,3,3,3,71]),(165,[]),(131,[]),(5,[2,3,17,113]),(135,[]),
    (131,[]),(159,[]),(171,[]),(131,[]),(2,[2,3,1931]),
    (169,[]),(131,[]),(187,[]),(135,[]),(131,[]),
    (147,[]),(235,[]),(131,[]),(135,[]),(141,[]),
    (131,[]),(151,[]),(147,[]),(131,[]),(6,[2,3,19,103]),
    (145,[]),(131,[]),(135,[]),(13,[2,43,137]),(131,[]),
    (139,[]),(10,[2,5903]),(131,[]),(41,[2,3,3,3,3,73]),(141,[]),
    (131,[]),(5,[2,3,3,659]),(5,[2,17,349]),(131,[]),(28,[2,3,7,283]),
    (10,[2,11,541]),(131,[]),(30,[2,3,1987]),(10,[2,67,89]),(131,[]),
    (141,[]),(135,[]),(131,[]),(151,[]),(5,[2,13,461])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock12 : ∃ data, checkBlock 12 data = true :=
  ⟨[(131,[]),(33,[2,3,3,23,29]),(139,[]),(131,[]),(17,[2,3,3,3,223]),
    (135,[]),(131,[]),(139,[]),(171,[]),(131,[]),
    (135,[]),(5,[2,6053]),(131,[]),(195,[]),(29,[2,13,467]),
    (131,[]),(33,[2,3,2027]),(151,[]),(131,[]),(135,[]),
    (5,[2,6101]),(131,[]),(145,[]),(5,[2,6113]),(131,[]),
    (165,[]),(10,[2,6131]),(131,[]),(199,[]),(139,[]),
    (131,[]),(159,[]),(5,[2,61,101]),(131,[]),(13,[2,3,11,11,17]),
    (5,[2,6173]),(131,[]),(211,[]),(135,[]),(131,[]),
    (207,[]),(147,[]),(131,[]),(145,[]),(151,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(12,[2,3,2081]),
    (14,[2,7,19,47]),(131,[]),(135,[]),(10,[2,6263]),(131,[]),
    (2,[2,3,3,17,41]),(145,[]),(131,[]),(19,[2,3,3,3,233]),(169,[]),
    (131,[]),(135,[]),(141,[]),(131,[]),(175,[]),
    (29,[2,6323]),(131,[]),(181,[]),(139,[]),(131,[]),
    (11,[2,3,29,73]),(225,[]),(131,[]),(139,[]),(10,[2,23,277]),
    (131,[]),(2,[2,3,3,709]),(145,[]),(131,[]),(147,[]),
    (135,[]),(131,[]),(5,[2,3,2137]),(229,[]),(131,[]),
    (157,[]),(147,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(2,[2,3,3,3,239]),(5,[2,7,13,71]),(131,[]),(135,[]),
    (139,[]),(131,[]),(11,[2,3,2161]),(10,[2,6491]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock13 : ∃ data, checkBlock 13 data = true :=
  ⟨[(19,[2,3,11,197]),(10,[2,7,929]),(131,[]),(135,[]),(5,[2,6521]),
    (131,[]),(74,[2,3,7,311]),(201,[]),(131,[]),(151,[]),
    (40,[2,6551]),(131,[]),(139,[]),(10,[2,6563]),(131,[]),
    (2,[2,3,7,313]),(5,[2,6581]),(131,[]),(11,[2,3,13,13,13]),(5,[2,19,347]),
    (131,[]),(175,[]),(135,[]),(131,[]),(145,[]),
    (141,[]),(131,[]),(12,[2,3,3,11,67]),(165,[]),(131,[]),
    (181,[]),(135,[]),(131,[]),(42,[2,3,2221]),(139,[]),
    (131,[]),(135,[]),(14,[2,41,163]),(131,[]),(139,[]),
    (141,[]),(131,[]),(159,[]),(157,[]),(131,[]),
    (135,[]),(13,[2,53,127]),(131,[]),(225,[]),(10,[2,11,613]),
    (131,[]),(141,[]),(5,[2,6761]),(131,[]),(157,[]),
    (147,[]),(131,[]),(11,[2,3,7,17,19]),(145,[]),(131,[]),
    (189,[]),(139,[]),(131,[]),(2,[2,3,3,757]),(135,[]),
    (131,[]),(141,[]),(207,[]),(131,[]),(5,[2,3,2281]),
    (199,[]),(131,[]),(2,[2,3,2287]),(135,[]),(131,[]),
    (187,[]),(6,[2,7,983]),(131,[]),(135,[]),(145,[]),
    (131,[]),(5,[2,3,3,13,59]),(151,[]),(131,[]),(237,[]),
    (189,[]),(131,[]),(135,[]),(5,[2,11,631]),(131,[]),
    (12,[2,3,7,331]),(5,[2,17,409]),(131,[]),(147,[]),(201,[]),
    (131,[]),(17,[2,3,13,179]),(13,[2,6983]),(131,[]),(199,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock14 : ∃ data, checkBlock 14 data = true :=
  ⟨[(139,[]),(131,[]),(165,[]),(141,[]),(131,[]),
    (139,[]),(135,[]),(131,[]),(17,[2,3,2347]),(34,[2,7043]),
    (131,[]),(11,[2,3,2351]),(157,[]),(131,[]),(19,[2,3,2357]),
    (135,[]),(131,[]),(159,[]),(141,[]),(131,[]),
    (135,[]),(13,[2,7103]),(131,[]),(169,[]),(5,[2,7121]),
    (131,[]),(145,[]),(139,[]),(131,[]),(135,[]),
    (10,[2,7151]),(131,[]),(28,[2,3,7,11,31]),(10,[2,13,19,29]),(131,[]),
    (11,[2,3,3,797]),(181,[]),(131,[]),(147,[]),(5,[2,7193]),
    (131,[]),(37,[2,3,7,7,7,7]),(29,[2,7211]),(131,[]),(139,[]),
    (10,[2,31,233]),(131,[]),(145,[]),(135,[]),(131,[]),
    (5,[2,3,2417]),(217,[]),(131,[]),(201,[]),(10,[2,11,661]),
    (131,[]),(18,[2,3,3,809]),(135,[]),(131,[]),(157,[]),
    (145,[]),(131,[]),(135,[]),(5,[2,71,103]),(131,[]),
    (225,[]),(139,[]),(131,[]),(11,[2,3,2447]),(147,[]),
    (131,[]),(135,[]),(5,[2,17,433]),(131,[]),(151,[]),
    (5,[2,73,101]),(131,[]),(5,[2,3,23,107]),(19,[2,19,389]),(131,[]),
    (241,[]),(141,[]),(131,[]),(12,[2,3,7,353]),(5,[2,41,181]),
    (131,[]),(217,[]),(5,[2,7433]),(131,[]),(5,[2,3,3,827]),
    (135,[]),(131,[]),(2,[2,3,3,829]),(139,[]),(131,[]),
    (2,[2,3,47,53]),(141,[]),(131,[]),(5,[2,3,11,227]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock15 : ∃ data, checkBlock 15 data = true :=
  ⟨[(131,[]),(171,[]),(211,[]),(131,[]),(135,[]),
    (169,[]),(131,[]),(141,[]),(5,[2,7541]),(131,[]),
    (139,[]),(5,[2,7,13,83]),(131,[]),(135,[]),(147,[]),
    (131,[]),(187,[]),(157,[]),(131,[]),(18,[2,3,2531]),
    (151,[]),(131,[]),(141,[]),(5,[2,23,331]),(131,[]),
    (207,[]),(19,[2,13,587]),(131,[]),(145,[]),(19,[2,7643]),
    (131,[]),(12,[2,3,2551]),(135,[]),(131,[]),(195,[]),
    (231,[]),(131,[]),(139,[]),(10,[2,7691]),(131,[]),
    (201,[]),(135,[]),(131,[]),(11,[2,3,3,857]),(6,[2,7,1103]),
    (131,[]),(135,[]),(5,[2,11,19,37]),(131,[]),(145,[]),
    (165,[]),(131,[]),(147,[]),(14,[2,7,1109]),(131,[]),
    (135,[]),(207,[]),(131,[]),(23,[2,3,7,7,53]),(139,[]),
    (131,[]),(5,[2,3,3,3,17,17]),(145,[]),(131,[]),(44,[2,3,3,11,79]),
    (10,[2,7823]),(131,[]),(2,[2,3,7,373]),(5,[2,7841]),(131,[]),
    (169,[]),(241,[]),(131,[]),(5,[2,3,2621]),(135,[]),
    (131,[]),(139,[]),(10,[2,7883]),(131,[]),(2,[2,3,3,877]),
    (5,[2,7901]),(131,[]),(20,[2,3,3,3,293]),(135,[]),(131,[]),
    (141,[]),(157,[]),(131,[]),(135,[]),(10,[2,13,13,47]),
    (131,[]),(12,[2,3,11,241]),(5,[2,19,419]),(131,[]),(235,[]),
    (165,[]),(131,[]),(135,[]),(139,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock16 : ∃ data, checkBlock 16 data = true :=
  ⟨[(141,[]),(19,[2,53,151]),(131,[]),(139,[]),(189,[]),
    (131,[]),(5,[2,3,2677]),(5,[2,29,277]),(131,[]),(5,[2,3,7,383]),
    (29,[2,83,97]),(131,[]),(151,[]),(10,[2,11,733]),(131,[]),
    (195,[]),(135,[]),(131,[]),(54,[2,3,3,29,31]),(5,[2,8093]),
    (131,[]),(147,[]),(10,[2,8111]),(131,[]),(165,[]),
    (135,[]),(131,[]),(11,[2,3,2711]),(147,[]),(131,[]),
    (135,[]),(151,[]),(131,[]),(157,[]),(187,[]),
    (131,[]),(2,[2,3,3,3,3,101]),(141,[]),(131,[]),(135,[]),
    (175,[]),(131,[]),(139,[]),(5,[2,43,191]),(131,[]),
    (5,[2,3,2741]),(229,[]),(131,[]),(181,[]),(10,[2,8243]),
    (131,[]),(145,[]),(141,[]),(131,[]),(199,[]),
    (5,[2,8273]),(131,[]),(12,[2,3,11,251]),(135,[]),(131,[]),
    (2,[2,3,2767]),(19,[2,19,19,23]),(131,[]),(141,[]),(139,[]),
    (131,[]),(147,[]),(135,[]),(131,[]),(139,[]),
    (10,[2,7,1193]),(131,[]),(135,[]),(171,[]),(131,[]),
    (11,[2,3,2791]),(5,[2,17,17,29]),(131,[]),(141,[]),(5,[2,7,11,109]),
    (131,[]),(135,[]),(10,[2,13,647]),(131,[]),(2,[2,3,7,401]),
    (145,[]),(131,[]),(229,[]),(5,[2,23,367]),(131,[]),
    (5,[2,3,3,3,313]),(139,[]),(131,[]),(6,[2,3,7,13,31]),(10,[2,43,197]),
    (131,[]),(2,[2,3,11,257]),(147,[]),(131,[]),(11,[2,3,19,149])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock17 : ∃ data, checkBlock 17 data = true :=
  ⟨[(135,[]),(131,[]),(157,[]),(5,[2,8513]),(131,[]),
    (19,[2,3,3,947]),(241,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(17,[2,3,2851]),(6,[2,7,1223]),(131,[]),(135,[]),
    (141,[]),(131,[]),(12,[2,3,2861]),(10,[2,11,11,71]),(131,[]),
    (2,[2,3,47,61]),(10,[2,7,1229]),(131,[]),(135,[]),(171,[]),
    (131,[]),(189,[]),(159,[]),(131,[]),(187,[]),
    (139,[]),(131,[]),(145,[]),(13,[2,8663]),(131,[]),
    (139,[]),(225,[]),(131,[]),(10,[2,3,2897]),(5,[2,8693]),
    (131,[]),(141,[]),(135,[]),(131,[]),(2,[2,3,3,3,17,19]),
    (201,[]),(131,[]),(12,[2,3,41,71]),(5,[2,8741]),(131,[]),
    (151,[]),(135,[]),(131,[]),(145,[]),(181,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(171,[]),
    (157,[]),(131,[]),(5,[2,3,3,11,89]),(6,[2,7,1259]),(131,[]),
    (135,[]),(145,[]),(131,[]),(67,[2,3,7,421]),(151,[]),
    (131,[]),(17,[2,3,13,227]),(165,[]),(131,[]),(139,[]),
    (5,[2,19,467]),(131,[]),(237,[]),(30,[2,17,523]),(131,[]),
    (147,[]),(10,[2,29,307]),(131,[]),(2,[2,3,2971]),(135,[]),
    (131,[]),(47,[2,3,13,229]),(145,[]),(131,[]),(159,[]),
    (13,[2,8951]),(131,[]),(11,[2,3,29,103]),(135,[]),(131,[]),
    (259,[]),(139,[]),(131,[]),(135,[]),(5,[2,17,23,23])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock18 : ∃ data, checkBlock 18 data = true :=
  ⟨[(131,[]),(139,[]),(195,[]),(131,[]),(2,[2,3,31,97]),
    (14,[2,7,1289]),(131,[]),(135,[]),(141,[]),(131,[]),
    (171,[]),(147,[]),(131,[]),(5,[2,3,3,19,53]),(10,[2,47,193]),
    (131,[]),(169,[]),(165,[]),(131,[]),(141,[]),
    (237,[]),(131,[]),(47,[2,3,3037]),(139,[]),(131,[]),
    (199,[]),(135,[]),(131,[]),(175,[]),(10,[2,41,223]),
    (131,[]),(37,[2,3,3,3,3,113]),(201,[]),(131,[]),(141,[]),
    (135,[]),(131,[]),(5,[2,3,3061]),(159,[]),(131,[]),
    (135,[]),(207,[]),(131,[]),(12,[2,3,37,83]),(5,[2,9221]),
    (131,[]),(165,[]),(187,[]),(131,[]),(135,[]),
    (10,[2,11,29,29]),(131,[]),(12,[2,3,3,3,7,7,7]),(225,[]),(131,[]),
    (145,[]),(147,[]),(131,[]),(5,[2,3,19,163]),(5,[2,9293]),
    (131,[]),(151,[]),(139,[]),(131,[]),(231,[]),
    (157,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (187,[]),(141,[]),(131,[]),(189,[]),(14,[2,9371]),
    (131,[]),(157,[]),(135,[]),(131,[]),(2,[2,3,31,101]),
    (5,[2,7,17,79]),(131,[]),(135,[]),(195,[]),(131,[]),
    (175,[]),(141,[]),(131,[]),(151,[]),(139,[]),
    (131,[]),(135,[]),(255,[]),(131,[]),(147,[]),
    (5,[2,9473]),(131,[]),(141,[]),(169,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock19 : ∃ data, checkBlock 19 data = true :=
  ⟨[(159,[]),(211,[]),(131,[]),(181,[]),(265,[]),
    (131,[]),(139,[]),(151,[]),(131,[]),(37,[2,3,3181]),
    (135,[]),(131,[]),(141,[]),(159,[]),(131,[]),
    (169,[]),(18,[2,11,13,67]),(131,[]),(12,[2,3,23,139]),(135,[]),
    (131,[]),(10,[2,3,3,11,97]),(175,[]),(131,[]),(135,[]),
    (147,[]),(131,[]),(19,[2,3,13,13,19]),(139,[]),(131,[]),
    (225,[]),(171,[]),(131,[]),(135,[]),(151,[]),
    (131,[]),(145,[]),(235,[]),(131,[]),(11,[2,3,3,3,359]),
    (13,[2,89,109]),(131,[]),(39,[2,3,3,13,83]),(5,[2,11,883]),(131,[]),
    (5,[2,3,7,463]),(10,[2,37,263]),(131,[]),(2,[2,3,17,191]),(141,[]),
    (131,[]),(2,[2,3,3251]),(135,[]),(131,[]),(23,[2,3,3257]),
    (139,[]),(131,[]),(145,[]),(10,[2,9791]),(131,[]),
    (2,[2,3,3,3,3,11,11]),(135,[]),(131,[]),(147,[]),(141,[]),
    (131,[]),(135,[]),(199,[]),(131,[]),(20,[2,3,17,193]),
    (145,[]),(131,[]),(139,[]),(13,[2,7,1409]),(131,[]),
    (135,[]),(5,[2,41,241]),(131,[]),(201,[]),(175,[]),
    (131,[]),(157,[]),(171,[]),(131,[]),(33,[2,3,3307]),
    (217,[]),(131,[]),(2,[2,3,7,11,43]),(187,[]),(131,[]),
    (141,[]),(145,[]),(131,[]),(12,[2,3,3,3,3,3,41]),(135,[]),
    (131,[]),(2,[2,3,3,1109]),(169,[]),(131,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock20 : ∃ data, checkBlock 20 data = true :=
  ⟨[(211,[]),(131,[]),(19,[2,3,47,71]),(135,[]),(131,[]),
    (44,[2,3,13,257]),(20,[2,7,1433]),(131,[]),(135,[]),(181,[]),
    (131,[]),(18,[2,3,3,1117]),(5,[2,10061]),(131,[]),(45,[2,3,3,3,373]),
    (6,[2,7,1439]),(131,[]),(135,[]),(10,[2,10091]),(131,[]),
    (217,[]),(139,[]),(131,[]),(241,[]),(159,[]),
    (131,[]),(151,[]),(141,[]),(131,[]),(5,[2,3,3,7,7,23]),
    (207,[]),(131,[]),(2,[2,3,3,1129]),(19,[2,10163]),(131,[]),
    (12,[2,3,3391]),(135,[]),(131,[]),(139,[]),(147,[]),
    (131,[]),(39,[2,3,19,179]),(141,[]),(131,[]),(2,[2,3,3407]),
    (135,[]),(131,[]),(225,[]),(5,[2,7,7,11,19]),(131,[]),
    (135,[]),(5,[2,10253]),(131,[]),(141,[]),(19,[2,10271]),
    (131,[]),(11,[2,3,23,149]),(259,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(169,[]),(5,[2,10313]),(131,[]),
    (139,[]),(10,[2,10331]),(131,[]),(141,[]),(265,[]),
    (131,[]),(44,[2,3,7,17,29]),(145,[]),(131,[]),(33,[2,3,3457]),
    (5,[2,11,23,41]),(131,[]),(147,[]),(135,[]),(131,[]),
    (199,[]),(29,[2,101,103]),(131,[]),(187,[]),(147,[]),
    (131,[]),(159,[]),(135,[]),(131,[]),(11,[2,3,59,59]),
    (14,[2,7,1493]),(131,[]),(135,[]),(145,[]),(131,[]),
    (11,[2,3,3491]),(5,[2,47,223]),(131,[]),(5,[2,3,13,269]),(159,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock21 : ∃ data, checkBlock 21 data = true :=
  ⟨[(131,[]),(135,[]),(13,[2,23,457]),(131,[]),(139,[]),
    (141,[]),(131,[]),(12,[2,3,3511]),(157,[]),(131,[]),
    (175,[]),(5,[2,61,173]),(131,[]),(165,[]),(10,[2,11,31,31]),
    (131,[]),(2,[2,3,3527]),(189,[]),(131,[]),(17,[2,3,3,11,107]),
    (135,[]),(131,[]),(147,[]),(5,[2,10613]),(131,[]),
    (12,[2,3,3541]),(139,[]),(131,[]),(34,[2,3,3547]),(135,[]),
    (131,[]),(139,[]),(5,[2,7,1523]),(131,[]),(135,[]),
    (5,[2,13,821]),(131,[]),(151,[]),(29,[2,10691]),(131,[]),
    (145,[]),(10,[2,7,11,139]),(131,[]),(135,[]),(169,[]),
    (131,[]),(141,[]),(5,[2,10733]),(131,[]),(5,[2,3,3581]),
    (10,[2,13,827]),(131,[]),(12,[2,3,17,211]),(139,[]),(131,[]),
    (157,[]),(5,[2,10781]),(131,[]),(241,[]),(5,[2,43,251]),
    (131,[]),(145,[]),(135,[]),(131,[]),(151,[]),
    (19,[2,79,137]),(131,[]),(175,[]),(5,[2,37,293]),(131,[]),
    (139,[]),(135,[]),(131,[]),(5,[2,3,3,17,71]),(145,[]),
    (131,[]),(135,[]),(10,[2,10883]),(131,[]),(37,[2,3,3631]),
    (5,[2,11,991]),(131,[]),(267,[]),(141,[]),(131,[]),
    (135,[]),(14,[2,17,643]),(131,[]),(207,[]),(171,[]),
    (131,[]),(147,[]),(139,[]),(131,[]),(5,[2,3,3,23,53]),
    (145,[]),(131,[]),(139,[]),(141,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock22 : ∃ data, checkBlock 22 data = true :=
  ⟨[(11,[2,3,19,193]),(187,[]),(131,[]),(20,[2,3,3671]),(135,[]),
    (131,[]),(5,[2,3,3677]),(5,[2,11,17,59]),(131,[]),(141,[]),
    (151,[]),(131,[]),(2,[2,3,3,1229]),(135,[]),(131,[]),
    (13,[2,3,3691]),(165,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(181,[]),(199,[]),(131,[]),(141,[]),
    (10,[2,7,7,227]),(131,[]),(135,[]),(5,[2,13,857]),(131,[]),
    (6,[2,3,3,3,7,59]),(5,[2,19,587]),(131,[]),(211,[]),(34,[2,11171]),
    (131,[]),(139,[]),(10,[2,53,211]),(131,[]),(189,[]),
    (171,[]),(131,[]),(145,[]),(169,[]),(131,[]),
    (20,[2,3,3,29,43]),(135,[]),(131,[]),(20,[2,3,3,1249]),(241,[]),
    (131,[]),(199,[]),(229,[]),(131,[]),(19,[2,3,13,17,17]),
    (135,[]),(131,[]),(20,[2,3,3761]),(139,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(139,[]),(5,[2,11321]),
    (131,[]),(259,[]),(147,[]),(131,[]),(135,[]),
    (201,[]),(131,[]),(159,[]),(10,[2,11,1033]),(131,[]),
    (151,[]),(141,[]),(131,[]),(5,[2,3,3797]),(5,[2,11393]),
    (131,[]),(6,[2,3,3,7,181]),(157,[]),(131,[]),(181,[]),
    (139,[]),(131,[]),(141,[]),(135,[]),(131,[]),
    (165,[]),(5,[2,13,881]),(131,[]),(229,[]),(13,[2,11471]),
    (131,[]),(19,[2,3,43,89]),(135,[]),(131,[]),(255,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock23 : ∃ data, checkBlock 23 data = true :=
  ⟨[(5,[2,7,31,53]),(131,[]),(135,[]),(5,[2,29,397]),(131,[]),
    (147,[]),(19,[2,13,887]),(131,[]),(169,[]),(10,[2,7,17,97]),
    (131,[]),(135,[]),(147,[]),(131,[]),(37,[2,3,7,19,29]),
    (207,[]),(131,[]),(38,[2,3,3,3,3,11,13]),(225,[]),(131,[]),
    (11,[2,3,3,1289]),(151,[]),(131,[]),(18,[2,3,7,7,79]),(139,[]),
    (131,[]),(171,[]),(181,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(211,[]),(29,[2,107,109]),(131,[]),
    (165,[]),(189,[]),(131,[]),(195,[]),(135,[]),
    (131,[]),(217,[]),(187,[]),(131,[]),(135,[]),
    (13,[2,19,617]),(131,[]),(159,[]),(151,[]),(131,[]),
    (147,[]),(139,[]),(131,[]),(135,[]),(141,[]),
    (131,[]),(11,[2,3,3,7,11,17]),(10,[2,11783]),(131,[]),(231,[]),
    (5,[2,11801]),(131,[]),(19,[2,3,31,127]),(5,[2,11813]),(131,[]),
    (141,[]),(30,[2,11831]),(131,[]),(139,[]),(10,[2,13,911]),
    (131,[]),(279,[]),(135,[]),(131,[]),(5,[2,3,3,1319]),
    (5,[2,31,383]),(131,[]),(40,[2,3,17,233]),(145,[]),(131,[]),
    (141,[]),(135,[]),(131,[]),(12,[2,3,11,19,19]),(241,[]),
    (131,[]),(135,[]),(157,[]),(131,[]),(5,[2,3,3,1327]),
    (139,[]),(131,[]),(175,[]),(199,[]),(131,[]),
    (135,[]),(159,[]),(131,[]),(157,[]),(145,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock24 : ∃ data, checkBlock 24 data = true :=
  ⟨[(131,[]),(46,[2,3,4001]),(19,[2,12011]),(131,[]),(2,[2,3,4007]),
    (267,[]),(131,[]),(169,[]),(5,[2,12041]),(131,[]),
    (38,[2,3,3,13,103]),(5,[2,17,709]),(131,[]),(151,[]),(135,[]),
    (131,[]),(201,[]),(139,[]),(131,[]),(147,[]),
    (5,[2,12101]),(131,[]),(10,[2,3,11,367]),(135,[]),(131,[]),
    (10,[2,3,3,3,449]),(147,[]),(131,[]),(135,[]),(277,[]),
    (131,[]),(237,[]),(141,[]),(131,[]),(139,[]),
    (225,[]),(131,[]),(135,[]),(165,[]),(131,[]),
    (151,[]),(10,[2,12203]),(131,[]),(141,[]),(5,[2,11,11,101]),
    (131,[]),(145,[]),(171,[]),(131,[]),(175,[]),
    (235,[]),(131,[]),(265,[]),(19,[2,12263]),(131,[]),
    (21,[2,3,4091]),(135,[]),(131,[]),(141,[]),(151,[]),
    (131,[]),(139,[]),(10,[2,13,947]),(131,[]),(147,[]),
    (135,[]),(131,[]),(145,[]),(6,[2,7,41,43]),(131,[]),
    (135,[]),(159,[]),(131,[]),(207,[]),(237,[]),
    (131,[]),(2,[2,3,4127]),(20,[2,7,29,61]),(131,[]),(135,[]),
    (145,[]),(131,[]),(231,[]),(139,[]),(131,[]),
    (10,[2,3,41,101]),(151,[]),(131,[]),(277,[]),(169,[]),
    (131,[]),(18,[2,3,7,593]),(5,[2,17,733]),(131,[]),(5,[2,3,4157]),
    (141,[]),(131,[]),(23,[2,3,3,19,73]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock25 : ∃ data, checkBlock 25 data = true :=
  ⟨[(139,[]),(145,[]),(131,[]),(157,[]),(207,[]),
    (131,[]),(199,[]),(135,[]),(131,[]),(5,[2,3,37,113]),
    (141,[]),(131,[]),(135,[]),(14,[2,17,739]),(131,[]),
    (12,[2,3,3,11,127]),(5,[2,23,547]),(131,[]),(5,[2,3,3,1399]),(217,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(2,[2,3,7,601]),
    (29,[2,13,971]),(131,[]),(139,[]),(259,[]),(131,[]),
    (10,[2,3,4217]),(5,[2,12653]),(131,[]),(147,[]),(19,[2,12671]),
    (131,[]),(141,[]),(10,[2,11,1153]),(131,[]),(181,[]),
    (135,[]),(131,[]),(20,[2,3,19,223]),(175,[]),(131,[]),
    (5,[2,3,4241]),(10,[2,29,439]),(131,[]),(145,[]),(135,[]),
    (131,[]),(151,[]),(7,[2,7,1823]),(131,[]),(135,[]),
    (187,[]),(131,[]),(165,[]),(19,[2,12791]),(131,[]),
    (2,[2,3,17,251]),(157,[]),(131,[]),(135,[]),(5,[2,12821]),
    (131,[]),(139,[]),(5,[2,41,313]),(131,[]),(145,[]),
    (30,[2,71,181]),(131,[]),(157,[]),(141,[]),(131,[]),
    (45,[2,3,7,613]),(5,[2,11,1171]),(131,[]),(147,[]),(235,[]),
    (131,[]),(259,[]),(135,[]),(131,[]),(171,[]),
    (19,[2,12923]),(131,[]),(2,[2,3,3,3,479]),(139,[]),(131,[]),
    (19,[2,3,3,1439]),(135,[]),(131,[]),(139,[]),(13,[2,7,17,109]),
    (131,[]),(135,[]),(151,[]),(131,[]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock26 : ∃ data, checkBlock 26 data = true :=
  ⟨[(5,[2,13001]),(131,[]),(181,[]),(145,[]),(131,[]),
    (135,[]),(195,[]),(131,[]),(22,[2,3,3,3,3,7,23]),(147,[]),
    (131,[]),(2,[2,3,19,229]),(279,[]),(131,[]),(141,[]),
    (139,[]),(131,[]),(265,[]),(19,[2,13,19,53]),(131,[]),
    (11,[2,3,11,397]),(201,[]),(131,[]),(11,[2,3,3,31,47]),(135,[]),
    (131,[]),(5,[2,3,3,1459]),(5,[2,23,571]),(131,[]),(225,[]),
    (157,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (17,[2,3,4391]),(169,[]),(131,[]),(135,[]),(5,[2,79,167]),
    (131,[]),(19,[2,3,3,3,3,163]),(10,[2,11,1201]),(131,[]),(159,[]),
    (181,[]),(131,[]),(135,[]),(199,[]),(131,[]),
    (145,[]),(141,[]),(131,[]),(169,[]),(139,[]),
    (131,[]),(229,[]),(159,[]),(131,[]),(139,[]),
    (165,[]),(131,[]),(207,[]),(5,[2,13313]),(131,[]),
    (11,[2,3,4441]),(135,[]),(131,[]),(2,[2,3,4447]),(10,[2,11,1213]),
    (131,[]),(145,[]),(5,[2,31,431]),(131,[]),(175,[]),
    (135,[]),(131,[]),(141,[]),(10,[2,7,1913]),(131,[]),
    (135,[]),(139,[]),(131,[]),(267,[]),(145,[]),
    (131,[]),(5,[2,3,11,11,37]),(195,[]),(131,[]),(135,[]),
    (13,[2,13451]),(131,[]),(141,[]),(19,[2,13463]),(131,[]),
    (12,[2,3,3,3,499]),(187,[]),(131,[]),(139,[]),(5,[2,103,131])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock27 : ∃ data, checkBlock 27 data = true :=
  ⟨[(131,[]),(241,[]),(189,[]),(131,[]),(41,[2,3,4507]),
    (145,[]),(131,[]),(2,[2,3,13,347]),(135,[]),(131,[]),
    (5,[2,3,4517]),(5,[2,13553]),(131,[]),(5,[2,3,3,11,137]),(14,[2,41,331]),
    (131,[]),(151,[]),(135,[]),(131,[]),(159,[]),
    (139,[]),(131,[]),(135,[]),(147,[]),(131,[]),
    (139,[]),(265,[]),(131,[]),(37,[2,3,4547]),(141,[]),
    (131,[]),(135,[]),(217,[]),(131,[]),(165,[]),
    (151,[]),(131,[]),(5,[2,3,4561]),(267,[]),(131,[]),
    (195,[]),(14,[2,71,193]),(131,[]),(38,[2,3,7,653]),(141,[]),
    (131,[]),(157,[]),(139,[]),(131,[]),(10,[2,3,3,3,509]),
    (135,[]),(131,[]),(145,[]),(10,[2,13763]),(131,[]),
    (141,[]),(171,[]),(131,[]),(5,[2,3,4597]),(135,[]),
    (131,[]),(147,[]),(151,[]),(131,[]),(135,[]),
    (10,[2,23,601]),(131,[]),(201,[]),(147,[]),(131,[]),
    (141,[]),(231,[]),(131,[]),(135,[]),(21,[2,11,13,97]),
    (131,[]),(12,[2,3,7,661]),(10,[2,13883]),(131,[]),(165,[]),
    (5,[2,13901]),(131,[]),(10,[2,3,4637]),(5,[2,13913]),(131,[]),
    (107,[2,3,3,7,13,17]),(139,[]),(131,[]),(28,[2,3,3,1549]),(207,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(5,[2,3,4657]),
    (5,[2,89,157]),(131,[]),(5,[2,3,59,79]),(13,[2,17,823]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock28 : ∃ data, checkBlock 28 data = true :=
  ⟨[(169,[]),(135,[]),(131,[]),(2,[2,3,3,3,3,173]),(157,[]),
    (131,[]),(135,[]),(141,[]),(131,[]),(11,[2,3,31,151]),
    (285,[]),(131,[]),(17,[2,3,43,109]),(139,[]),(131,[]),
    (135,[]),(5,[2,14081]),(131,[]),(10,[2,3,7,11,61]),(199,[]),
    (131,[]),(195,[]),(141,[]),(131,[]),(189,[]),
    (175,[]),(131,[]),(151,[]),(5,[2,79,179]),(131,[]),
    (139,[]),(5,[2,14153]),(131,[]),(141,[]),(135,[]),
    (131,[]),(241,[]),(147,[]),(131,[]),(2,[2,3,3,19,83]),
    (5,[2,11,1291]),(131,[]),(171,[]),(135,[]),(131,[]),
    (11,[2,3,11,431]),(19,[2,7,19,107]),(131,[]),(135,[]),(189,[]),
    (131,[]),(157,[]),(139,[]),(131,[]),(145,[]),
    (5,[2,7,2039]),(131,[]),(135,[]),(229,[]),(131,[]),
    (11,[2,3,3,7,227]),(30,[2,14303]),(131,[]),(11,[2,3,13,367]),(5,[2,14321]),
    (131,[]),(12,[2,3,17,281]),(237,[]),(131,[]),(39,[2,3,7,683]),
    (10,[2,113,127]),(131,[]),(2,[2,3,4787]),(151,[]),(131,[]),
    (145,[]),(135,[]),(131,[]),(235,[]),(139,[]),
    (131,[]),(43,[2,3,4801]),(147,[]),(131,[]),(44,[2,3,11,19,23]),
    (135,[]),(131,[]),(12,[2,3,17,283]),(145,[]),(131,[]),
    (135,[]),(265,[]),(131,[]),(23,[2,3,3,1607]),(231,[]),
    (131,[]),(139,[]),(211,[]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock29 : ∃ data, checkBlock 29 data = true :=
  ⟨[(141,[]),(131,[]),(6,[2,3,7,691]),(23,[2,23,631]),(131,[]),
    (159,[]),(10,[2,11,1321]),(131,[]),(255,[]),(145,[]),
    (131,[]),(141,[]),(5,[2,14561]),(131,[]),(279,[]),
    (5,[2,13,19,59]),(131,[]),(5,[2,3,4861]),(135,[]),(131,[]),
    (147,[]),(19,[2,17,859]),(131,[]),(139,[]),(5,[2,14621]),
    (131,[]),(141,[]),(135,[]),(131,[]),(10,[2,3,3,1627]),
    (19,[2,7,7,13,23]),(131,[]),(135,[]),(10,[2,11,31,43]),(131,[]),
    (12,[2,3,67,73]),(5,[2,53,277]),(131,[]),(19,[2,3,59,83]),(5,[2,7,2099]),
    (131,[]),(135,[]),(10,[2,47,313]),(131,[]),(12,[2,3,7,701]),
    (139,[]),(131,[]),(207,[]),(5,[2,14741]),(131,[]),
    (291,[]),(147,[]),(131,[]),(5,[2,3,7,19,37]),(159,[]),
    (131,[]),(145,[]),(39,[2,14783]),(131,[]),(17,[2,3,4931]),
    (135,[]),(131,[]),(139,[]),(141,[]),(131,[]),
    (151,[]),(14,[2,14831]),(131,[]),(34,[2,3,3,17,97]),(135,[]),
    (131,[]),(189,[]),(5,[2,7,11,193]),(131,[]),(135,[]),
    (279,[]),(131,[]),(145,[]),(141,[]),(131,[]),
    (42,[2,3,4967]),(169,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(40,[2,3,3,3,7,79]),(5,[2,109,137]),(131,[]),(139,[]),
    (145,[]),(131,[]),(151,[]),(20,[2,13,1151]),(131,[]),
    (41,[2,3,7,23,31]),(147,[]),(131,[]),(5,[2,3,19,263]),(285,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock30 : ∃ data, checkBlock 30 data = true :=
  ⟨[(131,[]),(165,[]),(135,[]),(131,[]),(141,[]),
    (29,[2,83,181]),(131,[]),(235,[]),(195,[]),(131,[]),
    (5,[2,3,29,173]),(135,[]),(131,[]),(175,[]),(171,[]),
    (131,[]),(135,[]),(225,[]),(131,[]),(29,[2,3,3,3,13,43]),
    (5,[2,15101]),(131,[]),(12,[2,3,3,23,73]),(295,[]),(131,[]),
    (135,[]),(181,[]),(131,[]),(139,[]),(159,[]),
    (131,[]),(2,[2,3,5051]),(5,[2,15161]),(131,[]),(147,[]),
    (5,[2,15173]),(131,[]),(38,[2,3,3,7,241]),(151,[]),(131,[]),
    (29,[2,3,3,3,563]),(141,[]),(131,[]),(20,[2,3,11,461]),(135,[]),
    (131,[]),(169,[]),(5,[2,15233]),(131,[]),(171,[]),
    (139,[]),(131,[]),(259,[]),(135,[]),(131,[]),
    (139,[]),(141,[]),(131,[]),(135,[]),(201,[]),
    (131,[]),(255,[]),(241,[]),(131,[]),(2,[2,3,5107]),
    (147,[]),(131,[]),(135,[]),(189,[]),(131,[]),
    (5,[2,3,7,17,43]),(5,[2,13,1181]),(131,[]),(11,[2,3,3,3,569]),(199,[]),
    (131,[]),(2,[2,3,3,1709]),(139,[]),(131,[]),(145,[]),
    (5,[2,15401]),(131,[]),(141,[]),(157,[]),(131,[]),
    (237,[]),(135,[]),(131,[]),(217,[]),(195,[]),
    (131,[]),(159,[]),(145,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(301,[]),(14,[2,7,2213]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock31 : ∃ data, checkBlock 31 data = true :=
  ⟨[(135,[]),(229,[]),(131,[]),(147,[]),(165,[]),
    (131,[]),(5,[2,3,31,167]),(175,[]),(131,[]),(135,[]),
    (147,[]),(131,[]),(11,[2,3,3,7,13,19]),(145,[]),(131,[]),
    (18,[2,3,29,179]),(139,[]),(131,[]),(11,[2,3,5197]),(141,[]),
    (131,[]),(139,[]),(10,[2,67,233]),(131,[]),(285,[]),
    (19,[2,17,919]),(131,[]),(2,[2,3,3,3,3,193]),(135,[]),(131,[]),
    (151,[]),(5,[2,11,1423]),(131,[]),(6,[2,3,23,227]),(141,[]),
    (131,[]),(207,[]),(135,[]),(131,[]),(2,[2,3,5231]),
    (159,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (141,[]),(201,[]),(131,[]),(147,[]),(151,[]),
    (131,[]),(135,[]),(157,[]),(131,[]),(5,[2,3,7,751]),
    (5,[2,15773]),(131,[]),(6,[2,3,5261]),(19,[2,15791]),(131,[]),
    (139,[]),(10,[2,15803]),(131,[]),(17,[2,3,3,7,251]),(5,[2,13,1217]),
    (131,[]),(5,[2,3,3,1759]),(5,[2,71,223]),(131,[]),(12,[2,3,5281]),
    (135,[]),(131,[]),(50,[2,3,17,311]),(10,[2,29,547]),(131,[]),
    (181,[]),(151,[]),(131,[]),(165,[]),(135,[]),
    (131,[]),(145,[]),(139,[]),(131,[]),(135,[]),
    (14,[2,15923]),(131,[]),(139,[]),(5,[2,19,839]),(131,[]),
    (189,[]),(6,[2,7,43,53]),(131,[]),(135,[]),(145,[]),
    (131,[]),(2,[2,3,7,761]),(141,[]),(131,[]),(157,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock32 : ∃ data, checkBlock 32 data = true :=
  ⟨[(5,[2,16001]),(131,[]),(159,[]),(5,[2,67,239]),(131,[]),
    (201,[]),(10,[2,17,23,41]),(131,[]),(2,[2,3,5347]),(139,[]),
    (131,[]),(225,[]),(135,[]),(131,[]),(10,[2,3,11,487]),
    (145,[]),(131,[]),(147,[]),(13,[2,16091]),(131,[]),
    (2,[2,3,3,1789]),(135,[]),(131,[]),(141,[]),(147,[]),
    (131,[]),(135,[]),(169,[]),(131,[]),(211,[]),
    (29,[2,31,521]),(131,[]),(2,[2,3,5387]),(14,[2,7,2309]),(131,[]),
    (135,[]),(5,[2,11,1471]),(131,[]),(141,[]),(267,[]),
    (131,[]),(151,[]),(19,[2,13,29,43]),(131,[]),(11,[2,3,5407]),
    (199,[]),(131,[]),(2,[2,3,7,773]),(139,[]),(131,[]),
    (10,[2,3,5417]),(5,[2,16253]),(131,[]),(139,[]),(135,[]),
    (131,[]),(11,[2,3,3,3,3,3,67]),(157,[]),(131,[]),(2,[2,3,5431]),
    (5,[2,16301]),(131,[]),(145,[]),(135,[]),(131,[]),
    (19,[2,3,5441]),(217,[]),(131,[]),(135,[]),(13,[2,59,277]),
    (131,[]),(11,[2,3,3,23,79]),(171,[]),(131,[]),(265,[]),
    (139,[]),(131,[]),(135,[]),(10,[2,37,443]),(131,[]),
    (44,[2,3,7,11,71]),(181,[]),(131,[]),(145,[]),(5,[2,16421]),
    (131,[]),(187,[]),(151,[]),(131,[]),(5,[2,3,3,3,3,7,29]),
    (141,[]),(131,[]),(139,[]),(147,[]),(131,[]),
    (175,[]),(135,[]),(131,[]),(5,[2,3,23,239]),(5,[2,16493])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock33 : ∃ data, checkBlock 33 data = true :=
  ⟨[(131,[]),(141,[]),(10,[2,11,19,79]),(131,[]),(301,[]),
    (135,[]),(131,[]),(171,[]),(7,[2,7,17,139]),(131,[]),
    (135,[]),(5,[2,16553]),(131,[]),(285,[]),(139,[]),
    (131,[]),(141,[]),(145,[]),(131,[]),(135,[]),
    (5,[2,13,1277]),(131,[]),(10,[2,3,7,7,113]),(277,[]),(131,[]),
    (13,[2,3,3,1847]),(157,[]),(131,[]),(211,[]),(10,[2,11,17,89]),
    (131,[]),(147,[]),(175,[]),(131,[]),(5,[2,3,5557]),
    (5,[2,16673]),(131,[]),(189,[]),(135,[]),(131,[]),
    (18,[2,3,19,293]),(139,[]),(131,[]),(11,[2,3,3,3,619]),(181,[]),
    (131,[]),(237,[]),(135,[]),(131,[]),(10,[2,3,5581]),
    (13,[2,7,2393]),(131,[]),(135,[]),(141,[]),(131,[]),
    (2,[2,3,5591]),(5,[2,97,173]),(131,[]),(139,[]),(6,[2,7,2399]),
    (131,[]),(135,[]),(13,[2,16811]),(131,[]),(145,[]),
    (10,[2,16823]),(131,[]),(259,[]),(141,[]),(131,[]),
    (5,[2,3,41,137]),(165,[]),(131,[]),(157,[]),(169,[]),
    (131,[]),(147,[]),(19,[2,16883]),(131,[]),(141,[]),
    (135,[]),(131,[]),(277,[]),(5,[2,13,1301]),(131,[]),
    (139,[]),(10,[2,16931]),(131,[]),(159,[]),(135,[]),
    (131,[]),(169,[]),(5,[2,7,2423]),(131,[]),(135,[]),
    (211,[]),(131,[]),(12,[2,3,3,3,17,37]),(145,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock34 : ∃ data, checkBlock 34 data = true :=
  ⟨[(165,[]),(159,[]),(131,[]),(135,[]),(187,[]),
    (131,[]),(151,[]),(139,[]),(131,[]),(217,[]),
    (195,[]),(131,[]),(2,[2,3,11,11,47]),(10,[2,113,151]),(131,[]),
    (41,[2,3,3,7,271]),(255,[]),(131,[]),(12,[2,3,3,3,3,211]),(145,[]),
    (131,[]),(207,[]),(135,[]),(131,[]),(139,[]),
    (151,[]),(131,[]),(2,[2,3,5711]),(5,[2,61,281]),(131,[]),
    (68,[2,3,5717]),(135,[]),(131,[]),(5,[2,3,3,1907]),(189,[]),
    (131,[]),(135,[]),(10,[2,17183]),(131,[]),(265,[]),
    (5,[2,103,167]),(131,[]),(157,[]),(301,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(12,[2,3,7,821]),(34,[2,43,401]),
    (131,[]),(139,[]),(147,[]),(131,[]),(10,[2,3,3,19,101]),
    (307,[]),(131,[]),(141,[]),(29,[2,17291]),(131,[]),
    (2,[2,3,73,79]),(29,[2,11,11,11,13]),(131,[]),(159,[]),(135,[]),
    (131,[]),(145,[]),(5,[2,17333]),(131,[]),(5,[2,3,3,41,47]),
    (10,[2,17351]),(131,[]),(141,[]),(135,[]),(131,[]),
    (2,[2,3,5791]),(7,[2,7,13,191]),(131,[]),(135,[]),(171,[]),
    (131,[]),(12,[2,3,5801]),(225,[]),(131,[]),(17,[2,3,5807]),
    (13,[2,7,19,131]),(131,[]),(135,[]),(5,[2,107,163]),(131,[]),
    (139,[]),(195,[]),(131,[]),(181,[]),(211,[]),
    (131,[]),(2,[2,3,5827]),(201,[]),(131,[]),(187,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock35 : ∃ data, checkBlock 35 data = true :=
  ⟨[(145,[]),(131,[]),(5,[2,3,13,449]),(5,[2,83,211]),(131,[]),
    (229,[]),(135,[]),(131,[]),(2,[2,3,3,1949]),(141,[]),
    (131,[]),(12,[2,3,5851]),(139,[]),(131,[]),(241,[]),
    (135,[]),(131,[]),(139,[]),(279,[]),(131,[]),
    (135,[]),(145,[]),(131,[]),(2,[2,3,3,19,103]),(141,[]),
    (131,[]),(307,[]),(23,[2,7,11,229]),(131,[]),(135,[]),
    (171,[]),(131,[]),(22,[2,3,7,29,29]),(19,[2,17,1039]),(131,[]),
    (141,[]),(5,[2,17681]),(131,[]),(169,[]),(139,[]),
    (131,[]),(6,[2,3,3,7,281]),(10,[2,89,199]),(131,[]),(151,[]),
    (10,[2,37,479]),(131,[]),(157,[]),(135,[]),(131,[]),
    (141,[]),(5,[2,41,433]),(131,[]),(5,[2,3,31,191]),(14,[2,13,1367]),
    (131,[]),(139,[]),(135,[]),(131,[]),(147,[]),
    (5,[2,7,2543]),(131,[]),(135,[]),(151,[]),(131,[]),
    (171,[]),(147,[]),(131,[]),(145,[]),(255,[]),
    (131,[]),(135,[]),(267,[]),(131,[]),(159,[]),
    (5,[2,61,293]),(131,[]),(175,[]),(139,[]),(131,[]),
    (34,[2,3,3,3,3,13,17]),(189,[]),(131,[]),(139,[]),(201,[]),
    (131,[]),(11,[2,3,43,139]),(141,[]),(131,[]),(145,[]),
    (135,[]),(131,[]),(2,[2,3,5987]),(165,[]),(131,[]),
    (231,[]),(5,[2,17981]),(131,[]),(5,[2,3,3,1999]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock36 : ∃ data, checkBlock 36 data = true :=
  ⟨[(131,[]),(5,[2,3,17,353]),(141,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(13,[2,3,6011]),(5,[2,18041]),(131,[]),
    (207,[]),(5,[2,7,2579]),(131,[]),(135,[]),(175,[]),
    (131,[]),(157,[]),(187,[]),(131,[]),(12,[2,3,37,163]),
    (169,[]),(131,[]),(139,[]),(145,[]),(131,[]),
    (195,[]),(19,[2,18131]),(131,[]),(141,[]),(259,[]),
    (131,[]),(2,[2,3,3,2017]),(135,[]),(131,[]),(33,[2,3,3,3,673]),
    (147,[]),(131,[]),(169,[]),(14,[2,18191]),(131,[]),
    (187,[]),(135,[]),(131,[]),(201,[]),(139,[]),
    (131,[]),(135,[]),(5,[2,18233]),(131,[]),(139,[]),
    (301,[]),(131,[]),(2,[2,3,3,2029]),(14,[2,7,2609]),(131,[]),
    (135,[]),(5,[2,101,181]),(131,[]),(28,[2,3,7,13,67]),(5,[2,11,1663]),
    (131,[]),(33,[2,3,6101]),(181,[]),(131,[]),(20,[2,3,31,197]),
    (141,[]),(131,[]),(165,[]),(5,[2,18341]),(131,[]),
    (145,[]),(139,[]),(131,[]),(147,[]),(135,[]),
    (131,[]),(225,[]),(10,[2,31,593]),(131,[]),(2,[2,3,6131]),
    (141,[]),(131,[]),(151,[]),(135,[]),(131,[]),
    (5,[2,3,3,23,89]),(319,[]),(131,[]),(135,[]),(10,[2,18443]),
    (131,[]),(141,[]),(5,[2,18461]),(131,[]),(11,[2,3,47,131]),
    (7,[2,7,7,13,29]),(131,[]),(135,[]),(159,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock37 : ∃ data, checkBlock 37 data = true :=
  ⟨[(2,[2,3,7,881]),(151,[]),(131,[]),(189,[]),(145,[]),
    (131,[]),(141,[]),(229,[]),(131,[]),(54,[2,3,7,883]),
    (139,[]),(131,[]),(18,[2,3,23,269]),(265,[]),(131,[]),
    (139,[]),(135,[]),(131,[]),(147,[]),(169,[]),
    (131,[]),(157,[]),(14,[2,37,503]),(131,[]),(2,[2,3,3,2069]),
    (135,[]),(131,[]),(211,[]),(151,[]),(131,[]),
    (135,[]),(5,[2,23,811]),(131,[]),(291,[]),(235,[]),
    (131,[]),(28,[2,3,13,479]),(139,[]),(131,[]),(135,[]),
    (241,[]),(131,[]),(11,[2,3,3,3,3,3,7,11]),(141,[]),(131,[]),
    (5,[2,3,79,79]),(34,[2,18731]),(131,[]),(2,[2,3,6247]),(147,[]),
    (131,[]),(73,[2,3,7,19,47]),(285,[]),(131,[]),(139,[]),
    (5,[2,18773]),(131,[]),(19,[2,3,3,2087]),(135,[]),(131,[]),
    (159,[]),(10,[2,18803]),(131,[]),(319,[]),(5,[2,11,29,59]),
    (131,[]),(5,[2,3,6277]),(135,[]),(131,[]),(141,[]),
    (165,[]),(131,[]),(135,[]),(159,[]),(131,[]),
    (17,[2,3,3,3,3,233]),(139,[]),(131,[]),(10,[2,3,3,2099]),(157,[]),
    (131,[]),(135,[]),(237,[]),(131,[]),(141,[]),
    (29,[2,127,149]),(131,[]),(147,[]),(171,[]),(131,[]),
    (157,[]),(5,[2,11,1723]),(131,[]),(145,[]),(147,[]),
    (131,[]),(2,[2,3,3,3,19,37]),(19,[2,41,463]),(131,[]),(11,[2,3,13,487])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock38 : ∃ data, checkBlock 38 data = true :=
  ⟨[(135,[]),(131,[]),(175,[]),(139,[]),(131,[]),
    (6,[2,3,17,373]),(145,[]),(131,[]),(11,[2,3,11,577]),(135,[]),
    (131,[]),(181,[]),(195,[]),(131,[]),(135,[]),
    (165,[]),(131,[]),(20,[2,3,6361]),(29,[2,17,1123]),(131,[]),
    (139,[]),(141,[]),(131,[]),(135,[]),(295,[]),
    (131,[]),(211,[]),(145,[]),(131,[]),(13,[2,3,3,3,709]),
    (10,[2,11,1741]),(131,[]),(147,[]),(10,[2,19163]),(131,[]),
    (159,[]),(141,[]),(131,[]),(259,[]),(151,[]),
    (131,[]),(321,[]),(135,[]),(131,[]),(165,[]),
    (30,[2,47,409]),(131,[]),(139,[]),(157,[]),(131,[]),
    (267,[]),(135,[]),(131,[]),(187,[]),(14,[2,7,2753]),
    (131,[]),(135,[]),(19,[2,11,1753]),(131,[]),(175,[]),
    (5,[2,19301]),(131,[]),(141,[]),(147,[]),(131,[]),
    (135,[]),(151,[]),(131,[]),(229,[]),(139,[]),
    (131,[]),(2,[2,3,6451]),(5,[2,19,1019]),(131,[]),(145,[]),
    (5,[2,19373]),(131,[]),(43,[2,3,7,13,71]),(19,[2,19391]),(131,[]),
    (19,[2,3,29,223]),(279,[]),(131,[]),(169,[]),(135,[]),
    (131,[]),(139,[]),(5,[2,19433]),(131,[]),(165,[]),
    (13,[2,53,367]),(131,[]),(2,[2,3,13,499]),(135,[]),(131,[]),
    (145,[]),(175,[]),(131,[]),(135,[]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock39 : ∃ data, checkBlock 39 data = true :=
  ⟨[(131,[]),(147,[]),(19,[2,109,179]),(131,[]),(2,[2,3,3,3,3,241]),
    (13,[2,7,2789]),(131,[]),(135,[]),(139,[]),(131,[]),
    (5,[2,3,7,7,7,19]),(5,[2,19553]),(131,[]),(139,[]),(141,[]),
    (131,[]),(2,[2,3,61,107]),(181,[]),(131,[]),(277,[]),
    (325,[]),(131,[]),(189,[]),(5,[2,11,1783]),(131,[]),
    (141,[]),(135,[]),(131,[]),(291,[]),(145,[]),
    (131,[]),(151,[]),(5,[2,19661]),(131,[]),(20,[2,3,79,83]),
    (135,[]),(131,[]),(47,[2,3,3,3,3,3,3,3,3,3]),(20,[2,7,29,97]),(131,[]),
    (135,[]),(285,[]),(131,[]),(217,[]),(5,[2,13,37,41]),
    (131,[]),(147,[]),(189,[]),(131,[]),(135,[]),
    (14,[2,19751]),(131,[]),(139,[]),(157,[]),(131,[]),
    (199,[]),(5,[2,131,151]),(131,[]),(151,[]),(159,[]),
    (131,[]),(6,[2,3,7,23,41]),(10,[2,11,1801]),(131,[]),(157,[]),
    (169,[]),(131,[]),(11,[2,3,11,601]),(135,[]),(131,[]),
    (5,[2,3,13,509]),(187,[]),(131,[]),(5,[2,3,3,2207]),(139,[]),
    (131,[]),(145,[]),(135,[]),(131,[]),(139,[]),
    (181,[]),(131,[]),(135,[]),(5,[2,19913]),(131,[]),
    (10,[2,3,29,229]),(19,[2,19,1049]),(131,[]),(28,[2,3,17,17,23]),(14,[2,7,7,11,37]),
    (131,[]),(135,[]),(141,[]),(131,[]),(187,[]),
    (171,[]),(131,[]),(145,[]),(10,[2,19991]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock40 : ∃ data, checkBlock 40 data = true :=
  ⟨[(237,[]),(139,[]),(131,[]),(141,[]),(151,[]),
    (131,[]),(5,[2,3,11,607]),(231,[]),(131,[]),(5,[2,3,3,17,131]),
    (135,[]),(131,[]),(2,[2,3,3,3,743]),(34,[2,20063]),(131,[]),
    (147,[]),(5,[2,43,467]),(131,[]),(139,[]),(135,[]),
    (131,[]),(159,[]),(147,[]),(131,[]),(135,[]),
    (295,[]),(131,[]),(195,[]),(5,[2,11,1831]),(131,[]),
    (169,[]),(145,[]),(131,[]),(135,[]),(14,[2,23,877]),
    (131,[]),(309,[]),(165,[]),(131,[]),(2,[2,3,53,127]),
    (139,[]),(131,[]),(10,[2,3,6737]),(5,[2,17,29,41]),(131,[]),
    (139,[]),(171,[]),(131,[]),(2,[2,3,3,13,173]),(29,[2,31,653]),
    (131,[]),(2,[2,3,43,157]),(135,[]),(131,[]),(19,[2,3,29,233]),
    (141,[]),(131,[]),(241,[]),(10,[2,103,197]),(131,[]),
    (147,[]),(135,[]),(131,[]),(2,[2,3,3,37,61]),(225,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(151,[]),
    (141,[]),(131,[]),(321,[]),(267,[]),(131,[]),
    (135,[]),(5,[2,89,229]),(131,[]),(145,[]),(5,[2,20393]),
    (131,[]),(141,[]),(19,[2,20411]),(131,[]),(139,[]),
    (10,[2,13,1571]),(131,[]),(2,[2,3,7,7,139]),(5,[2,20441]),(131,[]),
    (5,[2,3,17,401]),(147,[]),(131,[]),(5,[2,3,19,359]),(135,[]),
    (131,[]),(141,[]),(199,[]),(131,[]),(145,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock41 : ∃ data, checkBlock 41 data = true :=
  ⟨[(259,[]),(131,[]),(5,[2,3,3,43,53]),(135,[]),(131,[]),
    (19,[2,3,6841]),(139,[]),(131,[]),(135,[]),(309,[]),
    (131,[]),(139,[]),(145,[]),(131,[]),(12,[2,3,6857]),
    (151,[]),(131,[]),(135,[]),(14,[2,59,349]),(131,[]),
    (52,[2,3,3,3,7,109]),(217,[]),(131,[]),(2,[2,3,6871]),(5,[2,17,1213]),
    (131,[]),(40,[2,3,13,23,23]),(157,[]),(131,[]),(147,[]),
    (231,[]),(131,[]),(159,[]),(139,[]),(131,[]),
    (301,[]),(135,[]),(131,[]),(157,[]),(5,[2,20693]),
    (131,[]),(175,[]),(151,[]),(131,[]),(2,[2,3,6907]),
    (135,[]),(131,[]),(34,[2,3,6911]),(141,[]),(131,[]),
    (135,[]),(5,[2,20753]),(131,[]),(259,[]),(19,[2,20771]),
    (131,[]),(217,[]),(325,[]),(131,[]),(135,[]),
    (5,[2,11,31,61]),(131,[]),(235,[]),(5,[2,13,1601]),(131,[]),
    (44,[2,3,11,631]),(189,[]),(131,[]),(201,[]),(14,[2,19,1097]),
    (131,[]),(307,[]),(139,[]),(131,[]),(141,[]),
    (237,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (145,[]),(225,[]),(131,[]),(279,[]),(5,[2,20921]),
    (131,[]),(23,[2,3,6977]),(135,[]),(131,[]),(5,[2,3,3,13,179]),
    (10,[2,7,41,73]),(131,[]),(135,[]),(13,[2,20963]),(131,[]),
    (34,[2,3,6991]),(157,[]),(131,[]),(33,[2,3,6997]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock42 : ∃ data, checkBlock 42 data = true :=
  ⟨[(131,[]),(135,[]),(10,[2,21011]),(131,[]),(11,[2,3,7,7,11,13]),
    (147,[]),(131,[]),(151,[]),(5,[2,53,397]),(131,[]),
    (199,[]),(141,[]),(131,[]),(231,[]),(145,[]),
    (131,[]),(139,[]),(277,[]),(131,[]),(13,[2,3,79,89]),
    (135,[]),(131,[]),(10,[2,3,31,227]),(5,[2,43,491]),(131,[]),
    (211,[]),(141,[]),(131,[]),(2,[2,3,3,3,3,3,3,29]),(135,[]),
    (131,[]),(11,[2,3,11,641]),(5,[2,7,3023]),(131,[]),(135,[]),
    (145,[]),(131,[]),(141,[]),(139,[]),(131,[]),
    (2,[2,3,37,191]),(14,[2,7,13,233]),(131,[]),(135,[]),(5,[2,21221]),
    (131,[]),(5,[2,3,3,7,337]),(5,[2,17,1249]),(131,[]),(5,[2,3,73,97]),
    (147,[]),(131,[]),(141,[]),(151,[]),(131,[]),
    (285,[]),(159,[]),(131,[]),(225,[]),(165,[]),
    (131,[]),(265,[]),(135,[]),(131,[]),(17,[2,3,3,23,103]),
    (139,[]),(131,[]),(28,[2,3,13,547]),(5,[2,21341]),(131,[]),
    (5,[2,3,11,647]),(135,[]),(131,[]),(5,[2,3,7121]),(14,[2,7,43,71]),
    (131,[]),(135,[]),(14,[2,21383]),(131,[]),(20,[2,3,3,2377]),
    (151,[]),(131,[]),(139,[]),(241,[]),(131,[]),
    (135,[]),(13,[2,29,739]),(131,[]),(147,[]),(141,[]),
    (131,[]),(235,[]),(5,[2,11,1951]),(131,[]),(23,[2,3,17,421]),
    (195,[]),(131,[]),(10,[2,3,3,7,11,31]),(181,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock43 : ∃ data, checkBlock 43 data = true :=
  ⟨[(19,[2,3,3,2389]),(157,[]),(131,[]),(145,[]),(135,[]),
    (131,[]),(10,[2,3,7177]),(5,[2,61,353]),(131,[]),(139,[]),
    (10,[2,23,937]),(131,[]),(157,[]),(135,[]),(131,[]),
    (141,[]),(145,[]),(131,[]),(135,[]),(147,[]),
    (131,[]),(5,[2,3,19,379]),(10,[2,21611]),(131,[]),(211,[]),
    (187,[]),(131,[]),(135,[]),(5,[2,17,19,67]),(131,[]),
    (141,[]),(139,[]),(131,[]),(165,[]),(217,[]),
    (131,[]),(231,[]),(145,[]),(131,[]),(171,[]),
    (5,[2,21701]),(131,[]),(301,[]),(5,[2,21713]),(131,[]),
    (151,[]),(135,[]),(131,[]),(139,[]),(10,[2,17,1279]),
    (131,[]),(267,[]),(199,[]),(131,[]),(20,[2,3,3,41,59]),
    (135,[]),(131,[]),(147,[]),(169,[]),(131,[]),
    (135,[]),(10,[2,21803]),(131,[]),(2,[2,3,11,661]),(147,[]),
    (131,[]),(175,[]),(141,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(151,[]),(201,[]),(131,[]),
    (139,[]),(235,[]),(131,[]),(5,[2,3,7297]),(5,[2,21893]),
    (131,[]),(199,[]),(141,[]),(131,[]),(145,[]),
    (291,[]),(131,[]),(17,[2,3,3,2437]),(135,[]),(131,[]),
    (171,[]),(151,[]),(131,[]),(141,[]),(10,[2,127,173]),
    (131,[]),(18,[2,3,17,431]),(135,[]),(131,[]),(2,[2,3,7331])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock44 : ∃ data, checkBlock 44 data = true :=
  ⟨[(207,[]),(131,[]),(135,[]),(5,[2,22013]),(131,[]),
    (145,[]),(267,[]),(131,[]),(141,[]),(14,[2,7,47,67]),
    (131,[]),(135,[]),(7,[2,13,1697]),(131,[]),(139,[]),
    (259,[]),(131,[]),(157,[]),(145,[]),(131,[]),
    (19,[2,3,53,139]),(10,[2,23,31,31]),(131,[]),(175,[]),(279,[]),
    (131,[]),(54,[2,3,3,2459]),(5,[2,22133]),(131,[]),(195,[]),
    (135,[]),(131,[]),(255,[]),(147,[]),(131,[]),
    (189,[]),(139,[]),(131,[]),(10,[2,3,13,569]),(135,[]),
    (131,[]),(139,[]),(159,[]),(131,[]),(135,[]),
    (141,[]),(131,[]),(181,[]),(5,[2,23,967]),(131,[]),
    (319,[]),(5,[2,7,11,17,17]),(131,[]),(135,[]),(10,[2,22271]),
    (131,[]),(17,[2,3,7,1061]),(169,[]),(131,[]),(11,[2,3,3,2477]),
    (141,[]),(131,[]),(40,[2,3,3,37,67]),(139,[]),(131,[]),
    (10,[2,3,7,1063]),(187,[]),(131,[]),(2,[2,3,11,677]),(10,[2,22343]),
    (131,[]),(141,[]),(135,[]),(131,[]),(229,[]),
    (157,[]),(131,[]),(217,[]),(147,[]),(131,[]),
    (139,[]),(135,[]),(131,[]),(151,[]),(5,[2,7,3203]),
    (131,[]),(135,[]),(5,[2,22433]),(131,[]),(5,[2,3,7481]),
    (211,[]),(131,[]),(295,[]),(10,[2,7,3209]),(131,[]),
    (135,[]),(5,[2,22481]),(131,[]),(40,[2,3,3,3,7,7,17]),(5,[2,83,271])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock45 : ∃ data, checkBlock 45 data = true :=
  ⟨[(131,[]),(54,[2,3,13,577]),(139,[]),(131,[]),(159,[]),
    (235,[]),(131,[]),(139,[]),(5,[2,22541]),(131,[]),
    (151,[]),(171,[]),(131,[]),(20,[2,3,3,23,109]),(135,[]),
    (131,[]),(147,[]),(159,[]),(131,[]),(201,[]),
    (145,[]),(131,[]),(169,[]),(135,[]),(131,[]),
    (5,[2,3,7541]),(10,[2,7,53,61]),(131,[]),(135,[]),(139,[]),
    (131,[]),(2,[2,3,3,3,839]),(189,[]),(131,[]),(6,[2,3,3,11,229]),
    (265,[]),(131,[]),(135,[]),(141,[]),(131,[]),
    (12,[2,3,7,23,47]),(145,[]),(131,[]),(12,[2,3,67,113]),(157,[]),
    (131,[]),(139,[]),(147,[]),(131,[]),(141,[]),
    (19,[2,22751]),(131,[]),(11,[2,3,3,3,3,281]),(181,[]),(131,[]),
    (165,[]),(135,[]),(131,[]),(207,[]),(5,[2,23,991]),
    (131,[]),(187,[]),(171,[]),(131,[]),(141,[]),
    (135,[]),(131,[]),(2,[2,3,3,43,59]),(139,[]),(131,[]),
    (135,[]),(5,[2,22853]),(131,[]),(139,[]),(277,[]),
    (131,[]),(43,[2,3,29,263]),(20,[2,7,7,467]),(131,[]),(135,[]),
    (291,[]),(131,[]),(5,[2,3,7,1091]),(5,[2,11,2083]),(131,[]),
    (147,[]),(10,[2,23,997]),(131,[]),(145,[]),(14,[2,22943]),
    (131,[]),(157,[]),(147,[]),(131,[]),(6,[2,3,13,19,31]),
    (139,[]),(131,[]),(171,[]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock46 : ∃ data, checkBlock 46 data = true :=
  ⟨[(307,[]),(141,[]),(131,[]),(2,[2,3,3,2557]),(169,[]),
    (131,[]),(201,[]),(135,[]),(131,[]),(145,[]),
    (13,[2,7,37,89]),(131,[]),(135,[]),(321,[]),(131,[]),
    (2,[2,3,7691]),(141,[]),(131,[]),(5,[2,3,43,179]),(5,[2,7,3299]),
    (131,[]),(135,[]),(145,[]),(131,[]),(259,[]),
    (231,[]),(131,[]),(141,[]),(159,[]),(131,[]),
    (147,[]),(5,[2,13,13,137]),(131,[]),(5,[2,3,7,1103]),(139,[]),
    (131,[]),(199,[]),(327,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(141,[]),(145,[]),(131,[]),
    (11,[2,3,7741]),(225,[]),(131,[]),(151,[]),(135,[]),
    (131,[]),(2,[2,3,23,337]),(5,[2,7,3323]),(131,[]),(135,[]),
    (217,[]),(131,[]),(5,[2,3,3,13,199]),(165,[]),(131,[]),
    (157,[]),(139,[]),(131,[]),(135,[]),(5,[2,23321]),
    (131,[]),(12,[2,3,7,11,101]),(151,[]),(131,[]),(40,[2,3,31,251]),
    (19,[2,19,1229]),(131,[]),(2,[2,3,13,599]),(13,[2,61,383]),(131,[]),
    (2,[2,3,3,7,7,53]),(229,[]),(131,[]),(139,[]),(141,[]),
    (131,[]),(12,[2,3,29,269]),(135,[]),(131,[]),(267,[]),
    (207,[]),(131,[]),(12,[2,3,73,107]),(301,[]),(131,[]),
    (145,[]),(135,[]),(131,[]),(295,[]),(141,[]),
    (131,[]),(135,[]),(195,[]),(131,[]),(147,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock47 : ∃ data, checkBlock 47 data = true :=
  ⟨[(139,[]),(131,[]),(187,[]),(159,[]),(131,[]),
    (135,[]),(147,[]),(131,[]),(325,[]),(34,[2,13,1811]),
    (131,[]),(145,[]),(5,[2,23561]),(131,[]),(12,[2,3,3,3,3,3,97]),
    (6,[2,11,2143]),(131,[]),(229,[]),(157,[]),(131,[]),
    (141,[]),(19,[2,23603]),(131,[]),(211,[]),(135,[]),
    (131,[]),(279,[]),(139,[]),(131,[]),(5,[2,3,3,37,71]),
    (10,[2,67,353]),(131,[]),(165,[]),(135,[]),(131,[]),
    (241,[]),(5,[2,7,17,199]),(131,[]),(135,[]),(5,[2,19,29,43]),
    (131,[]),(5,[2,3,7901]),(175,[]),(131,[]),(139,[]),
    (145,[]),(131,[]),(135,[]),(231,[]),(131,[]),
    (195,[]),(5,[2,23753]),(131,[]),(33,[2,3,89,89]),(10,[2,11,2161]),
    (131,[]),(30,[2,3,7927]),(141,[]),(131,[]),(151,[]),
    (309,[]),(131,[]),(5,[2,3,7937]),(225,[]),(131,[]),
    (157,[]),(135,[]),(131,[]),(169,[]),(171,[]),
    (131,[]),(139,[]),(141,[]),(131,[]),(11,[2,3,73,109]),
    (135,[]),(131,[]),(165,[]),(199,[]),(131,[]),
    (135,[]),(10,[2,11,41,53]),(131,[]),(141,[]),(5,[2,19,1259]),
    (131,[]),(151,[]),(279,[]),(131,[]),(135,[]),
    (10,[2,43,557]),(131,[]),(145,[]),(139,[]),(131,[]),
    (29,[2,3,61,131]),(5,[2,23981]),(131,[]),(141,[]),(175,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock48 : ∃ data, checkBlock 48 data = true :=
  ⟨[(131,[]),(189,[]),(30,[2,13,1847]),(131,[]),(235,[]),
    (151,[]),(131,[]),(199,[]),(135,[]),(131,[]),
    (139,[]),(201,[]),(131,[]),(145,[]),(159,[]),
    (131,[]),(11,[2,3,23,349]),(135,[]),(131,[]),(2,[2,3,3,2677]),
    (147,[]),(131,[]),(135,[]),(157,[]),(131,[]),
    (10,[2,3,11,17,43]),(145,[]),(131,[]),(181,[]),(237,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(157,[]),
    (141,[]),(131,[]),(139,[]),(10,[2,17,1423]),(131,[]),
    (225,[]),(13,[2,24203]),(131,[]),(207,[]),(321,[]),
    (131,[]),(45,[2,3,41,197]),(145,[]),(131,[]),(5,[2,3,8081]),
    (135,[]),(131,[]),(12,[2,3,8087]),(19,[2,19,1277]),(131,[]),
    (171,[]),(5,[2,24281]),(131,[]),(147,[]),(135,[]),
    (131,[]),(141,[]),(10,[2,7,23,151]),(131,[]),(135,[]),
    (10,[2,13,1871]),(131,[]),(169,[]),(217,[]),(131,[]),
    (241,[]),(181,[]),(131,[]),(135,[]),(207,[]),
    (131,[]),(139,[]),(10,[2,37,659]),(131,[]),(2,[2,3,47,173]),
    (165,[]),(131,[]),(5,[2,3,79,103]),(285,[]),(131,[]),
    (5,[2,3,7,1163]),(259,[]),(131,[]),(2,[2,3,8147]),(147,[]),
    (131,[]),(11,[2,3,3,11,13,19]),(135,[]),(131,[]),(145,[]),
    (5,[2,24473]),(131,[]),(151,[]),(139,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock49 : ∃ data, checkBlock 49 data = true :=
  ⟨[(51,[2,3,8167]),(135,[]),(131,[]),(139,[]),(5,[2,7,31,113]),
    (131,[]),(135,[]),(267,[]),(131,[]),(319,[]),
    (19,[2,24551]),(131,[]),(17,[2,3,3,2729]),(141,[]),(131,[]),
    (135,[]),(339,[]),(131,[]),(265,[]),(229,[]),
    (131,[]),(6,[2,3,59,139]),(10,[2,24611]),(131,[]),(151,[]),
    (139,[]),(131,[]),(147,[]),(141,[]),(131,[]),
    (175,[]),(5,[2,89,277]),(131,[]),(235,[]),(135,[]),
    (131,[]),(12,[2,3,19,433]),(19,[2,24683]),(131,[]),(141,[]),
    (255,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (325,[]),(13,[2,7,3533]),(131,[]),(135,[]),(145,[]),
    (131,[]),(159,[]),(5,[2,11,2251]),(131,[]),(141,[]),
    (5,[2,7,3539]),(131,[]),(135,[]),(307,[]),(131,[]),
    (11,[2,3,7,1181]),(241,[]),(131,[]),(12,[2,3,3,3,919]),(139,[]),
    (131,[]),(5,[2,3,3,31,89]),(5,[2,19,1307]),(131,[]),(139,[]),
    (151,[]),(131,[]),(147,[]),(19,[2,23,23,47]),(131,[]),
    (11,[2,3,8291]),(135,[]),(131,[]),(12,[2,3,8297]),(14,[2,11,31,73]),
    (131,[]),(6,[2,3,3,2767]),(10,[2,29,859]),(131,[]),(2,[2,3,3,3,13,71]),
    (135,[]),(131,[]),(175,[]),(211,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(10,[2,3,53,157]),(10,[2,24971]),
    (131,[]),(145,[]),(157,[]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock50 : ∃ data, checkBlock 50 data = true :=
  ⟨[(159,[]),(131,[]),(6,[2,3,3,7,397]),(147,[]),(131,[]),
    (37,[2,3,19,439]),(141,[]),(131,[]),(139,[]),(10,[2,79,317]),
    (131,[]),(217,[]),(5,[2,19,1319]),(131,[]),(169,[]),
    (5,[2,25073]),(131,[]),(141,[]),(135,[]),(131,[]),
    (189,[]),(10,[2,13,1931]),(131,[]),(11,[2,3,11,761]),(175,[]),
    (131,[]),(5,[2,3,8377]),(135,[]),(131,[]),(23,[2,3,17,17,29]),
    (139,[]),(131,[]),(135,[]),(187,[]),(131,[]),
    (139,[]),(5,[2,13,13,149]),(131,[]),(6,[2,3,3,3,3,311]),(5,[2,7,59,61]),
    (131,[]),(135,[]),(14,[2,17,1483]),(131,[]),(201,[]),
    (189,[]),(131,[]),(237,[]),(147,[]),(131,[]),
    (5,[2,3,19,443]),(145,[]),(131,[]),(37,[2,3,3,7,401]),(10,[2,37,683]),
    (131,[]),(187,[]),(139,[]),(131,[]),(61,[2,3,8431]),
    (135,[]),(131,[]),(151,[]),(5,[2,17,1489]),(131,[]),
    (10,[2,3,23,367]),(157,[]),(131,[]),(2,[2,3,8447]),(135,[]),
    (131,[]),(12,[2,3,3,3,3,313]),(17,[2,7,3623]),(131,[]),(135,[]),
    (159,[]),(131,[]),(5,[2,3,8461]),(171,[]),(131,[]),
    (229,[]),(151,[]),(131,[]),(135,[]),(141,[]),
    (131,[]),(147,[]),(5,[2,29,877]),(131,[]),(279,[]),
    (237,[]),(131,[]),(11,[2,3,3,3,23,41]),(255,[]),(131,[]),
    (141,[]),(139,[]),(131,[]),(145,[]),(195,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock51 : ∃ data, checkBlock 51 data = true :=
  ⟨[(131,[]),(139,[]),(135,[]),(131,[]),(12,[2,3,47,181]),
    (59,[2,25523]),(131,[]),(351,[]),(151,[]),(131,[]),
    (141,[]),(135,[]),(131,[]),(157,[]),(327,[]),
    (131,[]),(135,[]),(147,[]),(131,[]),(145,[]),
    (5,[2,25601]),(131,[]),(309,[]),(139,[]),(131,[]),
    (135,[]),(10,[2,19,19,71]),(131,[]),(11,[2,3,3,7,11,37]),(10,[2,25643]),
    (131,[]),(30,[2,3,17,503]),(145,[]),(131,[]),(5,[2,3,43,199]),
    (5,[2,25673]),(131,[]),(159,[]),(19,[2,23,1117]),(131,[]),
    (139,[]),(10,[2,25703]),(131,[]),(20,[2,3,3,2857]),(135,[]),
    (131,[]),(181,[]),(141,[]),(131,[]),(6,[2,3,8581]),
    (10,[2,11,2341]),(131,[]),(195,[]),(135,[]),(131,[]),
    (147,[]),(5,[2,7,29,127]),(131,[]),(135,[]),(207,[]),
    (131,[]),(23,[2,3,3,47,61]),(139,[]),(131,[]),(171,[]),
    (13,[2,7,7,17,31]),(131,[]),(135,[]),(5,[2,25841]),(131,[]),
    (277,[]),(157,[]),(131,[]),(141,[]),(187,[]),
    (131,[]),(165,[]),(19,[2,11,13,181]),(131,[]),(61,[2,3,3,3,7,137]),
    (5,[2,59,439]),(131,[]),(157,[]),(5,[2,25913]),(131,[]),
    (267,[]),(135,[]),(131,[]),(141,[]),(139,[]),
    (131,[]),(94,[2,3,41,211]),(265,[]),(131,[]),(255,[]),
    (135,[]),(131,[]),(285,[]),(355,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock52 : ∃ data, checkBlock 52 data = true :=
  ⟨[(135,[]),(259,[]),(131,[]),(17,[2,3,13,23,29]),(199,[]),
    (131,[]),(139,[]),(5,[2,7,3719]),(131,[]),(135,[]),
    (14,[2,109,239]),(131,[]),(175,[]),(10,[2,67,389]),(131,[]),
    (18,[2,3,3,2897]),(5,[2,11,2371]),(131,[]),(5,[2,3,3,13,223]),(151,[]),
    (131,[]),(145,[]),(19,[2,26111]),(131,[]),(217,[]),
    (141,[]),(131,[]),(2,[2,3,31,281]),(135,[]),(131,[]),
    (321,[]),(147,[]),(131,[]),(139,[]),(145,[]),
    (131,[]),(29,[2,3,3,2909]),(135,[]),(131,[]),(2,[2,3,8731]),
    (141,[]),(131,[]),(135,[]),(231,[]),(131,[]),
    (307,[]),(151,[]),(131,[]),(159,[]),(201,[]),
    (131,[]),(135,[]),(181,[]),(131,[]),(40,[2,3,3,3,7,139]),
    (139,[]),(131,[]),(5,[2,3,8761]),(10,[2,61,431]),(131,[]),
    (169,[]),(159,[]),(131,[]),(17,[2,3,7,7,179]),(189,[]),
    (131,[]),(141,[]),(5,[2,17,1549]),(131,[]),(147,[]),
    (135,[]),(131,[]),(139,[]),(10,[2,41,643]),(131,[]),
    (22,[2,3,59,149]),(147,[]),(131,[]),(5,[2,3,19,463]),(135,[]),
    (131,[]),(19,[2,3,13,677]),(229,[]),(131,[]),(135,[]),
    (171,[]),(131,[]),(157,[]),(5,[2,137,193]),(131,[]),
    (5,[2,3,3,2939]),(319,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(38,[2,3,7,13,97]),(30,[2,71,373]),(131,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock53 : ∃ data, checkBlock 53 data = true :=
  ⟨[(5,[2,26501]),(131,[]),(145,[]),(141,[]),(131,[]),
    (22,[2,3,3,7,421]),(175,[]),(131,[]),(237,[]),(10,[2,11,19,127]),
    (131,[]),(151,[]),(135,[]),(131,[]),(147,[]),
    (5,[2,26573]),(131,[]),(207,[]),(141,[]),(131,[]),
    (211,[]),(135,[]),(131,[]),(145,[]),(165,[]),
    (131,[]),(135,[]),(5,[2,26633]),(131,[]),(141,[]),
    (279,[]),(131,[]),(17,[2,3,8887]),(14,[2,7,13,293]),(131,[]),
    (135,[]),(145,[]),(131,[]),(139,[]),(325,[]),
    (131,[]),(5,[2,3,3,3,23,43]),(169,[]),(131,[]),(141,[]),
    (147,[]),(131,[]),(255,[]),(207,[]),(131,[]),
    (5,[2,3,37,241]),(5,[2,31,863]),(131,[]),(10,[2,3,11,811]),(135,[]),
    (131,[]),(157,[]),(145,[]),(131,[]),(169,[]),
    (139,[]),(131,[]),(10,[2,3,3,3,3,331]),(135,[]),(131,[]),
    (139,[]),(231,[]),(131,[]),(135,[]),(165,[]),
    (131,[]),(171,[]),(159,[]),(131,[]),(351,[]),
    (199,[]),(131,[]),(135,[]),(10,[2,26891]),(131,[]),
    (301,[]),(141,[]),(131,[]),(147,[]),(151,[]),
    (131,[]),(189,[]),(139,[]),(131,[]),(11,[2,3,7,1283]),
    (147,[]),(131,[]),(19,[2,3,11,19,43]),(10,[2,59,457]),(131,[]),
    (201,[]),(135,[]),(131,[]),(165,[]),(5,[2,26993])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock54 : ∃ data, checkBlock 54 data = true :=
  ⟨[(131,[]),(181,[]),(217,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(141,[]),(5,[2,7,3863]),(131,[]),
    (135,[]),(189,[]),(131,[]),(241,[]),(157,[]),
    (131,[]),(37,[2,3,3,3,17,59]),(10,[2,7,53,73]),(131,[]),(135,[]),
    (195,[]),(131,[]),(141,[]),(339,[]),(131,[]),
    (145,[]),(139,[]),(131,[]),(147,[]),(14,[2,27143]),
    (131,[]),(139,[]),(5,[2,157,173]),(131,[]),(159,[]),
    (5,[2,29,937]),(131,[]),(20,[2,3,13,17,41]),(135,[]),(131,[]),
    (2,[2,3,9067]),(169,[]),(131,[]),(165,[]),(5,[2,163,167]),
    (131,[]),(235,[]),(135,[]),(131,[]),(151,[]),
    (10,[2,7,17,229]),(131,[]),(135,[]),(139,[]),(131,[]),
    (11,[2,3,9091]),(5,[2,27281]),(131,[]),(5,[2,3,11,827]),(141,[]),
    (131,[]),(135,[]),(19,[2,31,881]),(131,[]),(181,[]),
    (29,[2,89,307]),(131,[]),(2,[2,3,3,3037]),(277,[]),(131,[]),
    (139,[]),(355,[]),(131,[]),(38,[2,3,7,1303]),(141,[]),
    (131,[]),(151,[]),(10,[2,139,197]),(131,[]),(12,[2,3,23,397]),
    (135,[]),(131,[]),(201,[]),(237,[]),(131,[]),
    (141,[]),(211,[]),(131,[]),(199,[]),(135,[]),
    (131,[]),(2,[2,3,9151]),(139,[]),(131,[]),(135,[]),
    (151,[]),(131,[]),(139,[]),(10,[2,37,743]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock55 : ∃ data, checkBlock 55 data = true :=
  ⟨[(141,[]),(195,[]),(131,[]),(135,[]),(147,[]),
    (131,[]),(145,[]),(181,[]),(131,[]),(159,[]),
    (10,[2,27551]),(131,[]),(327,[]),(13,[2,43,641]),(131,[]),
    (18,[2,3,7,13,101]),(5,[2,27581]),(131,[]),(267,[]),(139,[]),
    (131,[]),(5,[2,3,3,3067]),(135,[]),(131,[]),(2,[2,3,3,3,3,11,31]),
    (229,[]),(131,[]),(145,[]),(187,[]),(131,[]),
    (157,[]),(135,[]),(131,[]),(189,[]),(13,[2,7,59,67]),
    (131,[]),(135,[]),(141,[]),(131,[]),(225,[]),
    (145,[]),(131,[]),(147,[]),(171,[]),(131,[]),
    (135,[]),(165,[]),(131,[]),(241,[]),(10,[2,27743]),
    (131,[]),(175,[]),(141,[]),(131,[]),(195,[]),
    (5,[2,27773]),(131,[]),(309,[]),(139,[]),(131,[]),
    (11,[2,3,3,3089]),(145,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(10,[2,3,9277]),(5,[2,13,2141]),(131,[]),(361,[]),
    (181,[]),(131,[]),(231,[]),(135,[]),(131,[]),
    (235,[]),(5,[2,7,7,569]),(131,[]),(135,[]),(5,[2,27893]),
    (131,[]),(12,[2,3,71,131]),(10,[2,13,19,113]),(131,[]),(12,[2,3,41,227]),
    (139,[]),(131,[]),(135,[]),(157,[]),(131,[]),
    (11,[2,3,7,11,11,11]),(165,[]),(131,[]),(28,[2,3,3,13,239]),(171,[]),
    (131,[]),(319,[]),(13,[2,27983]),(131,[]),(2,[2,3,7,31,43])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock56 : ∃ data, checkBlock 56 data = true :=
  ⟨[(5,[2,28001]),(131,[]),(139,[]),(307,[]),(131,[]),
    (169,[]),(135,[]),(131,[]),(145,[]),(10,[2,29,967]),
    (131,[]),(147,[]),(7,[2,11,2551]),(131,[]),(151,[]),
    (135,[]),(131,[]),(41,[2,3,11,23,37]),(147,[]),(131,[]),
    (135,[]),(13,[2,157,179]),(131,[]),(187,[]),(139,[]),
    (131,[]),(28,[2,3,9377]),(5,[2,7,4019]),(131,[]),(135,[]),
    (141,[]),(131,[]),(279,[]),(151,[]),(131,[]),
    (157,[]),(285,[]),(131,[]),(5,[2,3,9397]),(241,[]),
    (131,[]),(141,[]),(145,[]),(131,[]),(67,[2,3,23,409]),
    (175,[]),(131,[]),(11,[2,3,3,3137]),(135,[]),(131,[]),
    (12,[2,3,3,43,73]),(139,[]),(131,[]),(22,[2,3,9421]),(10,[2,17,1663]),
    (131,[]),(141,[]),(135,[]),(131,[]),(199,[]),
    (151,[]),(131,[]),(135,[]),(145,[]),(131,[]),
    (165,[]),(19,[2,41,691]),(131,[]),(139,[]),(13,[2,7,4049]),
    (131,[]),(135,[]),(259,[]),(131,[]),(307,[]),
    (5,[2,17,1669]),(131,[]),(5,[2,3,9461]),(10,[2,11,29,89]),(131,[]),
    (171,[]),(10,[2,28403]),(131,[]),(2,[2,3,3,7,11,41]),(5,[2,97,293]),
    (131,[]),(229,[]),(147,[]),(131,[]),(291,[]),
    (135,[]),(131,[]),(17,[2,3,53,179]),(141,[]),(131,[]),
    (139,[]),(5,[2,19,1499]),(131,[]),(5,[2,3,9497]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock57 : ∃ data, checkBlock 57 data = true :=
  ⟨[(131,[]),(237,[]),(255,[]),(131,[]),(135,[]),
    (10,[2,11,2593]),(131,[]),(277,[]),(141,[]),(131,[]),
    (145,[]),(7,[2,7,4079]),(131,[]),(135,[]),(10,[2,28571]),
    (131,[]),(2,[2,3,7,1361]),(139,[]),(131,[]),(141,[]),
    (5,[2,37,773]),(131,[]),(41,[2,3,3,11,17,17]),(217,[]),(131,[]),
    (147,[]),(301,[]),(131,[]),(2,[2,3,9547]),(29,[2,28643]),
    (131,[]),(145,[]),(135,[]),(131,[]),(139,[]),
    (5,[2,53,541]),(131,[]),(12,[2,3,3,3187]),(14,[2,13,2207]),(131,[]),
    (265,[]),(135,[]),(131,[]),(2,[2,3,17,563]),(145,[]),
    (131,[]),(135,[]),(5,[2,59,487]),(131,[]),(47,[2,3,11,13,67]),
    (19,[2,28751]),(131,[]),(151,[]),(13,[2,7,7,587]),(131,[]),
    (135,[]),(139,[]),(131,[]),(217,[]),(5,[2,28793]),
    (131,[]),(139,[]),(157,[]),(131,[]),(187,[]),
    (145,[]),(131,[]),(17,[2,3,7,1373]),(165,[]),(131,[]),
    (147,[]),(141,[]),(131,[]),(20,[2,3,3,3,1069]),(135,[]),
    (131,[]),(175,[]),(189,[]),(131,[]),(2,[2,3,9631]),
    (5,[2,28901]),(131,[]),(181,[]),(135,[]),(131,[]),
    (10,[2,3,31,311]),(141,[]),(131,[]),(135,[]),(235,[]),
    (131,[]),(207,[]),(5,[2,28961]),(131,[]),(5,[2,3,3,3,29,37]),
    (5,[2,7,4139]),(131,[]),(135,[]),(151,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock58 : ∃ data, checkBlock 58 data = true :=
  ⟨[(139,[]),(147,[]),(131,[]),(2,[2,3,19,509]),(5,[2,29021]),
    (131,[]),(159,[]),(5,[2,29033]),(131,[]),(157,[]),
    (225,[]),(131,[]),(141,[]),(165,[]),(131,[]),
    (12,[2,3,11,881]),(135,[]),(131,[]),(211,[]),(159,[]),
    (131,[]),(12,[2,3,89,109]),(139,[]),(131,[]),(2,[2,3,17,571]),
    (135,[]),(131,[]),(139,[]),(295,[]),(131,[]),
    (135,[]),(327,[]),(131,[]),(145,[]),(169,[]),
    (131,[]),(2,[2,3,71,137]),(14,[2,7,11,379]),(131,[]),(135,[]),
    (5,[2,29201]),(131,[]),(165,[]),(5,[2,131,223]),(131,[]),
    (339,[]),(145,[]),(131,[]),(361,[]),(139,[]),
    (131,[]),(169,[]),(171,[]),(131,[]),(6,[2,3,11,887]),
    (255,[]),(131,[]),(10,[2,3,43,227]),(135,[]),(131,[]),
    (32,[2,3,9767]),(231,[]),(131,[]),(151,[]),(141,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(12,[2,3,9781]),
    (175,[]),(131,[]),(135,[]),(10,[2,29363]),(131,[]),
    (141,[]),(14,[2,11,2671]),(131,[]),(157,[]),(6,[2,7,13,17,19]),
    (131,[]),(135,[]),(187,[]),(131,[]),(147,[]),
    (211,[]),(131,[]),(165,[]),(139,[]),(131,[]),
    (141,[]),(5,[2,29453]),(131,[]),(139,[]),(10,[2,13,2267]),
    (131,[]),(17,[2,3,31,317]),(29,[2,29483]),(131,[]),(189,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock59 : ∃ data, checkBlock 59 data = true :=
  ⟨[(135,[]),(131,[]),(19,[2,3,3,3,1093]),(195,[]),(131,[]),
    (265,[]),(10,[2,29531]),(131,[]),(12,[2,3,43,229]),(135,[]),
    (131,[]),(18,[2,3,9851]),(5,[2,7,41,103]),(131,[]),(135,[]),
    (139,[]),(131,[]),(10,[2,3,3,19,173]),(10,[2,127,233]),(131,[]),
    (201,[]),(10,[2,7,4229]),(131,[]),(135,[]),(6,[2,19,1559]),
    (131,[]),(54,[2,3,7,17,83]),(141,[]),(131,[]),(229,[]),
    (159,[]),(131,[]),(139,[]),(169,[]),(131,[]),
    (145,[]),(151,[]),(131,[]),(171,[]),(5,[2,23,1291]),
    (131,[]),(5,[2,3,9901]),(135,[]),(131,[]),(17,[2,3,9907]),
    (10,[2,29723]),(131,[]),(2,[2,3,11,17,53]),(145,[]),(131,[]),
    (285,[]),(135,[]),(131,[]),(141,[]),(139,[]),
    (131,[]),(135,[]),(14,[2,13,29,79]),(131,[]),(139,[]),
    (147,[]),(131,[]),(237,[]),(5,[2,7,4259]),(131,[]),
    (135,[]),(13,[2,23,1297]),(131,[]),(141,[]),(145,[]),
    (131,[]),(17,[2,3,3,31,107]),(5,[2,13,2297]),(131,[]),(12,[2,3,3,3319]),
    (5,[2,29873]),(131,[]),(187,[]),(319,[]),(131,[]),
    (207,[]),(139,[]),(131,[]),(157,[]),(135,[]),
    (131,[]),(5,[2,3,11,907]),(259,[]),(131,[]),(5,[2,3,3,3,1109]),
    (165,[]),(131,[]),(159,[]),(135,[]),(131,[]),
    (279,[]),(189,[]),(131,[]),(135,[]),(351,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock60 : ∃ data, checkBlock 60 data = true :=
  ⟨[(131,[]),(151,[]),(321,[]),(131,[]),(225,[]),
    (141,[]),(131,[]),(135,[]),(5,[2,11,2731]),(131,[]),
    (5,[2,3,3,3,3,7,53]),(5,[2,41,733]),(131,[]),(5,[2,3,11,911]),(265,[]),
    (131,[]),(145,[]),(14,[2,67,449]),(131,[]),(267,[]),
    (139,[]),(131,[]),(10,[2,3,10037]),(357,[]),(131,[]),
    (139,[]),(135,[]),(131,[]),(151,[]),(147,[]),
    (131,[]),(141,[]),(307,[]),(131,[]),(5,[2,3,89,113]),
    (135,[]),(131,[]),(145,[]),(10,[2,7,19,227]),(131,[]),
    (135,[]),(157,[]),(131,[]),(11,[2,3,3,3,3,373]),(5,[2,47,643]),
    (131,[]),(141,[]),(139,[]),(131,[]),(135,[]),
    (145,[]),(131,[]),(157,[]),(10,[2,53,571]),(131,[]),
    (319,[]),(199,[]),(131,[]),(175,[]),(171,[]),
    (131,[]),(6,[2,3,3,7,13,37]),(45,[2,17,1783]),(131,[]),(139,[]),
    (10,[2,30323]),(131,[]),(147,[]),(135,[]),(131,[]),
    (11,[2,3,67,151]),(145,[]),(131,[]),(33,[2,3,29,349]),(147,[]),
    (131,[]),(71,[2,3,13,19,41]),(135,[]),(131,[]),(217,[]),
    (169,[]),(131,[]),(135,[]),(141,[]),(131,[]),
    (199,[]),(139,[]),(131,[]),(235,[]),(19,[2,7,4349]),
    (131,[]),(135,[]),(5,[2,83,367]),(131,[]),(5,[2,3,7,1451]),
    (187,[]),(131,[]),(169,[]),(141,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock61 : ∃ data, checkBlock 61 data = true :=
  ⟨[(181,[]),(13,[2,11,47,59]),(131,[]),(2,[2,3,7,1453]),(5,[2,23,1327]),
    (131,[]),(355,[]),(207,[]),(131,[]),(141,[]),
    (135,[]),(131,[]),(147,[]),(139,[]),(131,[]),
    (175,[]),(159,[]),(131,[]),(145,[]),(135,[]),
    (131,[]),(225,[]),(13,[2,7,4373]),(131,[]),(135,[]),
    (201,[]),(131,[]),(325,[]),(5,[2,13,2357]),(131,[]),
    (139,[]),(229,[]),(131,[]),(135,[]),(14,[2,30671]),
    (131,[]),(30,[2,3,3,7,487]),(237,[]),(131,[]),(145,[]),
    (5,[2,11,2791]),(131,[]),(367,[]),(147,[]),(131,[]),
    (171,[]),(19,[2,79,389]),(131,[]),(2,[2,3,10247]),(30,[2,71,433]),
    (131,[]),(2,[2,3,3,3,17,67]),(135,[]),(131,[]),(5,[2,3,3,13,263]),
    (5,[2,30773]),(131,[]),(139,[]),(10,[2,41,751]),(131,[]),
    (2,[2,3,10267]),(135,[]),(131,[]),(11,[2,3,10271]),(7,[2,7,7,17,37]),
    (131,[]),(135,[]),(5,[2,11,2803]),(131,[]),(20,[2,3,3,23,149]),
    (10,[2,30851]),(131,[]),(19,[2,3,3,3,3,3,127]),(145,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(159,[]),(139,[]),
    (131,[]),(147,[]),(339,[]),(131,[]),(12,[2,3,11,937]),
    (151,[]),(131,[]),(141,[]),(147,[]),(131,[]),
    (231,[]),(159,[]),(131,[]),(5,[2,3,10321]),(135,[]),
    (131,[]),(139,[]),(10,[2,30983]),(131,[]),(2,[2,3,10331])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock62 : ∃ data, checkBlock 62 data = true :=
  ⟨[(5,[2,29,1069]),(131,[]),(141,[]),(135,[]),(131,[]),
    (23,[2,3,3,3,3,383]),(181,[]),(131,[]),(135,[]),(175,[]),
    (131,[]),(301,[]),(151,[]),(131,[]),(6,[2,3,10357]),
    (157,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (145,[]),(38,[2,19,1637]),(131,[]),(139,[]),(195,[]),
    (131,[]),(147,[]),(199,[]),(131,[]),(327,[]),
    (29,[2,31151]),(131,[]),(32,[2,3,13,17,47]),(10,[2,11,2833]),(131,[]),
    (20,[2,3,10391]),(135,[]),(131,[]),(19,[2,3,37,281]),(141,[]),
    (131,[]),(145,[]),(10,[2,23,23,59]),(131,[]),(169,[]),
    (135,[]),(131,[]),(11,[2,3,29,359]),(5,[2,7,4463]),(131,[]),
    (135,[]),(5,[2,31253]),(131,[]),(159,[]),(141,[]),
    (131,[]),(12,[2,3,10427]),(147,[]),(131,[]),(135,[]),
    (5,[2,113,277]),(131,[]),(139,[]),(5,[2,173,181]),(131,[]),
    (141,[]),(351,[]),(131,[]),(30,[2,3,31,337]),(10,[2,13,2411]),
    (131,[]),(201,[]),(5,[2,11,2851]),(131,[]),(55,[2,3,10457]),
    (145,[]),(131,[]),(151,[]),(135,[]),(131,[]),
    (141,[]),(309,[]),(131,[]),(12,[2,3,37,283]),(139,[]),
    (131,[]),(165,[]),(135,[]),(131,[]),(139,[]),
    (10,[2,7,4493]),(131,[]),(135,[]),(13,[2,73,431]),(131,[]),
    (147,[]),(207,[]),(131,[]),(19,[2,3,3,3499]),(7,[2,7,11,409])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock63 : ∃ data, checkBlock 63 data = true :=
  ⟨[(131,[]),(135,[]),(147,[]),(131,[]),(151,[]),
    (195,[]),(131,[]),(2,[2,3,23,457]),(327,[]),(131,[]),
    (19,[2,3,13,809]),(139,[]),(131,[]),(5,[2,3,3,3,7,167]),(361,[]),
    (131,[]),(211,[]),(141,[]),(131,[]),(307,[]),
    (135,[]),(131,[]),(145,[]),(151,[]),(131,[]),
    (5,[2,3,83,127]),(169,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(157,[]),(141,[]),(131,[]),(135,[]),
    (5,[2,19,1667]),(131,[]),(12,[2,3,59,179]),(369,[]),(131,[]),
    (147,[]),(291,[]),(131,[]),(135,[]),(5,[2,31721]),
    (131,[]),(5,[2,3,7,1511]),(5,[2,13,2441]),(131,[]),(5,[2,3,3,3527]),
    (139,[]),(131,[]),(267,[]),(14,[2,23,1381]),(131,[]),
    (139,[]),(145,[]),(131,[]),(141,[]),(5,[2,31793]),
    (131,[]),(10,[2,3,10601]),(135,[]),(131,[]),(159,[]),
    (10,[2,11,11,263]),(131,[]),(2,[2,3,3,3,3,3,131]),(171,[]),(131,[]),
    (23,[2,3,3,3539]),(135,[]),(131,[]),(19,[2,3,13,19,43]),(10,[2,7,29,157]),
    (131,[]),(135,[]),(139,[]),(131,[]),(355,[]),
    (5,[2,19,23,73]),(131,[]),(11,[2,3,11,967]),(211,[]),(131,[]),
    (135,[]),(13,[2,37,863]),(131,[]),(321,[]),(157,[]),
    (131,[]),(2,[2,3,10651]),(225,[]),(131,[]),(139,[]),
    (141,[]),(131,[]),(175,[]),(237,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock64 : ∃ data, checkBlock 64 data = true :=
  ⟨[(157,[]),(10,[2,32003]),(131,[]),(171,[]),(135,[]),
    (131,[]),(20,[2,3,3,3559]),(5,[2,103,311]),(131,[]),(147,[]),
    (141,[]),(131,[]),(2,[2,3,10687]),(135,[]),(131,[]),
    (151,[]),(139,[]),(131,[]),(135,[]),(5,[2,67,479]),
    (131,[]),(139,[]),(10,[2,163,197]),(131,[]),(145,[]),
    (169,[]),(131,[]),(135,[]),(5,[2,32141]),(131,[]),
    (6,[2,3,7,1531]),(235,[]),(131,[]),(5,[2,3,71,151]),(165,[]),
    (131,[]),(141,[]),(319,[]),(131,[]),(159,[]),
    (5,[2,13,2477]),(131,[]),(151,[]),(139,[]),(131,[]),
    (145,[]),(135,[]),(131,[]),(2,[2,3,11,977]),(187,[]),
    (131,[]),(379,[]),(241,[]),(131,[]),(147,[]),
    (135,[]),(131,[]),(19,[2,3,3,17,211]),(145,[]),(131,[]),
    (135,[]),(151,[]),(131,[]),(20,[2,3,10771]),(255,[]),
    (131,[]),(6,[2,3,13,829]),(7,[2,7,31,149]),(131,[]),(135,[]),
    (217,[]),(131,[]),(187,[]),(141,[]),(131,[]),
    (30,[2,3,3,3,11,109]),(5,[2,32381]),(131,[]),(40,[2,3,3,59,61]),(145,[]),
    (131,[]),(357,[]),(139,[]),(131,[]),(189,[]),
    (147,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (169,[]),(175,[]),(131,[]),(11,[2,3,3,3607]),(229,[]),
    (131,[]),(295,[]),(135,[]),(131,[]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock65 : ∃ data, checkBlock 65 data = true :=
  ⟨[(19,[2,7,4643]),(131,[]),(135,[]),(5,[2,13,41,61]),(131,[]),
    (157,[]),(10,[2,32531]),(131,[]),(165,[]),(139,[]),
    (131,[]),(135,[]),(5,[2,32561]),(131,[]),(141,[]),
    (5,[2,32573]),(131,[]),(5,[2,3,10861]),(40,[2,13,23,109]),(131,[]),
    (2,[2,3,10867]),(325,[]),(131,[]),(147,[]),(181,[]),
    (131,[]),(139,[]),(5,[2,32633]),(131,[]),(5,[2,3,3,3,3,13,31]),
    (135,[]),(131,[]),(2,[2,3,3,19,191]),(10,[2,89,367]),(131,[]),
    (229,[]),(291,[]),(131,[]),(279,[]),(135,[]),
    (131,[]),(19,[2,3,11,991]),(13,[2,7,4673]),(131,[]),(135,[]),
    (13,[2,43,761]),(131,[]),(145,[]),(139,[]),(131,[]),
    (159,[]),(141,[]),(131,[]),(135,[]),(10,[2,32771]),
    (131,[]),(11,[2,3,7,7,223]),(301,[]),(131,[]),(2,[2,3,17,643]),
    (145,[]),(131,[]),(265,[]),(157,[]),(131,[]),
    (6,[2,3,3,7,521]),(141,[]),(131,[]),(147,[]),(19,[2,32843]),
    (131,[]),(2,[2,3,47,233]),(135,[]),(131,[]),(157,[]),
    (139,[]),(131,[]),(141,[]),(285,[]),(131,[]),
    (151,[]),(135,[]),(131,[]),(11,[2,3,3,3,23,53]),(5,[2,7,4703]),
    (131,[]),(135,[]),(5,[2,32933]),(131,[]),(169,[]),
    (187,[]),(131,[]),(139,[]),(10,[2,7,17,277]),(131,[]),
    (135,[]),(6,[2,13,43,59]),(131,[]),(10,[2,3,7,1571]),(147,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock66 : ∃ data, checkBlock 66 data = true :=
  ⟨[(131,[]),(277,[]),(231,[]),(131,[]),(339,[]),
    (10,[2,33023]),(131,[]),(68,[2,3,7,11,11,13]),(5,[2,19,37,47]),(131,[]),
    (5,[2,3,23,479]),(5,[2,33053]),(131,[]),(217,[]),(135,[]),
    (131,[]),(237,[]),(255,[]),(131,[]),(139,[]),
    (367,[]),(131,[]),(175,[]),(135,[]),(131,[]),
    (159,[]),(151,[]),(131,[]),(135,[]),(141,[]),
    (131,[]),(189,[]),(157,[]),(131,[]),(5,[2,3,11057]),
    (5,[2,7,7,677]),(131,[]),(135,[]),(10,[2,33191]),(131,[]),
    (2,[2,3,3,7,17,31]),(139,[]),(131,[]),(309,[]),(141,[]),
    (131,[]),(12,[2,3,11,19,53]),(5,[2,167,199]),(131,[]),(145,[]),
    (201,[]),(131,[]),(2,[2,3,11087]),(199,[]),(131,[]),
    (141,[]),(135,[]),(131,[]),(139,[]),(5,[2,13,13,197]),
    (131,[]),(171,[]),(145,[]),(131,[]),(17,[2,3,29,383]),
    (135,[]),(131,[]),(291,[]),(5,[2,7,11,433]),(131,[]),
    (135,[]),(169,[]),(131,[]),(181,[]),(159,[]),
    (131,[]),(12,[2,3,3,3709]),(307,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(147,[]),(145,[]),(131,[]),
    (139,[]),(10,[2,101,331]),(131,[]),(44,[2,3,71,157]),(339,[]),
    (131,[]),(151,[]),(5,[2,33461]),(131,[]),(5,[2,3,3,3719]),
    (5,[2,11,17,179]),(131,[]),(295,[]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock67 : ∃ data, checkBlock 67 data = true :=
  ⟨[(2,[2,3,13,859]),(165,[]),(131,[]),(225,[]),(5,[2,33521]),
    (131,[]),(327,[]),(135,[]),(131,[]),(201,[]),
    (10,[2,7,4793]),(131,[]),(135,[]),(147,[]),(131,[]),
    (211,[]),(175,[]),(131,[]),(151,[]),(5,[2,7,4799]),
    (131,[]),(135,[]),(141,[]),(131,[]),(139,[]),
    (10,[2,33623]),(131,[]),(265,[]),(189,[]),(131,[]),
    (145,[]),(5,[2,73,461]),(131,[]),(141,[]),(10,[2,11,3061]),
    (131,[]),(159,[]),(151,[]),(131,[]),(207,[]),
    (135,[]),(131,[]),(319,[]),(5,[2,33713]),(131,[]),
    (19,[2,3,3,3,1249]),(139,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(139,[]),(5,[2,7,7,13,53]),(131,[]),(135,[]),
    (5,[2,33773]),(131,[]),(12,[2,3,11261]),(147,[]),(131,[]),
    (195,[]),(10,[2,7,11,439]),(131,[]),(135,[]),(145,[]),
    (131,[]),(199,[]),(285,[]),(131,[]),(241,[]),
    (207,[]),(131,[]),(19,[2,3,11287]),(139,[]),(131,[]),
    (165,[]),(5,[2,17,1993]),(131,[]),(5,[2,3,11,13,79]),(181,[]),
    (131,[]),(10,[2,3,3,3767]),(135,[]),(131,[]),(21,[2,3,3,3769]),
    (141,[]),(131,[]),(2,[2,3,11311]),(5,[2,33941]),(131,[]),
    (139,[]),(135,[]),(131,[]),(12,[2,3,11321]),(20,[2,7,23,211]),
    (131,[]),(135,[]),(14,[2,17,1999]),(131,[]),(2,[2,3,3,3,1259])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock68 : ∃ data, checkBlock 68 data = true :=
  ⟨[(141,[]),(131,[]),(5,[2,3,3,3779]),(187,[]),(131,[]),
    (135,[]),(157,[]),(131,[]),(231,[]),(39,[2,59,577]),
    (131,[]),(141,[]),(139,[]),(131,[]),(211,[]),
    (5,[2,13,2621]),(131,[]),(139,[]),(169,[]),(131,[]),
    (369,[]),(19,[2,67,509]),(131,[]),(17,[2,3,83,137]),(135,[]),
    (131,[]),(141,[]),(147,[]),(131,[]),(151,[]),
    (295,[]),(131,[]),(145,[]),(135,[]),(131,[]),
    (169,[]),(265,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(195,[]),(181,[]),(131,[]),(29,[2,3,11,17,61]),
    (13,[2,7,4889]),(131,[]),(135,[]),(5,[2,97,353]),(131,[]),
    (189,[]),(5,[2,34253]),(131,[]),(145,[]),(30,[2,43,797]),
    (131,[]),(139,[]),(10,[2,34283]),(131,[]),(235,[]),
    (159,[]),(131,[]),(291,[]),(141,[]),(131,[]),
    (147,[]),(135,[]),(131,[]),(17,[2,3,11447]),(10,[2,61,563]),
    (131,[]),(255,[]),(147,[]),(131,[]),(10,[2,3,3,3,19,67]),
    (135,[]),(131,[]),(19,[2,3,73,157]),(139,[]),(131,[]),
    (135,[]),(211,[]),(131,[]),(139,[]),(171,[]),
    (131,[]),(10,[2,3,23,499]),(145,[]),(131,[]),(135,[]),
    (14,[2,47,733]),(131,[]),(285,[]),(30,[2,11,13,241]),(131,[]),
    (2,[2,3,11491]),(5,[2,29,29,41]),(131,[]),(229,[]),(277,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock69 : ∃ data, checkBlock 69 data = true :=
  ⟨[(131,[]),(279,[]),(151,[]),(131,[]),(141,[]),
    (139,[]),(131,[]),(2,[2,3,3,3,1279]),(135,[]),(131,[]),
    (147,[]),(157,[]),(131,[]),(5,[2,3,41,281]),(14,[2,181,191]),
    (131,[]),(2,[2,3,11527]),(135,[]),(131,[]),(171,[]),
    (5,[2,7,4943]),(131,[]),(135,[]),(165,[]),(131,[]),
    (5,[2,3,3,3847]),(29,[2,34631]),(131,[]),(207,[]),(321,[]),
    (131,[]),(135,[]),(309,[]),(131,[]),(145,[]),
    (159,[]),(131,[]),(199,[]),(29,[2,113,307]),(131,[]),
    (34,[2,3,43,269]),(141,[]),(131,[]),(2,[2,3,3,7,19,29]),(139,[]),
    (131,[]),(6,[2,3,3,17,227]),(5,[2,47,739]),(131,[]),(139,[]),
    (135,[]),(131,[]),(165,[]),(379,[]),(131,[]),
    (145,[]),(141,[]),(131,[]),(277,[]),(135,[]),
    (131,[]),(175,[]),(10,[2,7,4973]),(131,[]),(135,[]),
    (385,[]),(131,[]),(141,[]),(145,[]),(131,[]),
    (171,[]),(139,[]),(131,[]),(135,[]),(225,[]),
    (131,[]),(2,[2,3,7,11,151]),(10,[2,34883]),(131,[]),(147,[]),
    (157,[]),(131,[]),(141,[]),(5,[2,34913]),(131,[]),
    (12,[2,3,7,1663]),(147,[]),(131,[]),(139,[]),(145,[]),
    (131,[]),(181,[]),(135,[]),(131,[]),(151,[]),
    (241,[]),(131,[]),(159,[]),(175,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock70 : ∃ data, checkBlock 70 data = true :=
  ⟨[(2,[2,3,3,3889]),(135,[]),(131,[]),(367,[]),(217,[]),
    (131,[]),(135,[]),(5,[2,53,661]),(131,[]),(237,[]),
    (139,[]),(131,[]),(2,[2,3,13,29,31]),(151,[]),(131,[]),
    (135,[]),(5,[2,35081]),(131,[]),(10,[2,3,3,7,557]),(141,[]),
    (131,[]),(28,[2,3,11701]),(29,[2,35111]),(131,[]),(147,[]),
    (327,[]),(131,[]),(157,[]),(195,[]),(131,[]),
    (357,[]),(295,[]),(131,[]),(21,[2,3,3,3907]),(135,[]),
    (131,[]),(145,[]),(139,[]),(131,[]),(187,[]),
    (151,[]),(131,[]),(10,[2,3,11,11,97]),(135,[]),(131,[]),
    (141,[]),(159,[]),(131,[]),(135,[]),(14,[2,13,2711]),
    (131,[]),(18,[2,3,3,3917]),(237,[]),(131,[]),(139,[]),
    (147,[]),(131,[]),(135,[]),(13,[2,35291]),(131,[]),
    (141,[]),(10,[2,43,821]),(131,[]),(28,[2,3,79,149]),(169,[]),
    (131,[]),(33,[2,3,11777]),(5,[2,89,397]),(131,[]),(19,[2,3,3,3,7,11,17]),
    (145,[]),(131,[]),(325,[]),(235,[]),(131,[]),
    (391,[]),(135,[]),(131,[]),(5,[2,3,47,251]),(199,[]),
    (131,[]),(139,[]),(10,[2,17,2083]),(131,[]),(2,[2,3,11807]),
    (135,[]),(131,[]),(17,[2,3,3,31,127]),(201,[]),(131,[]),
    (135,[]),(145,[]),(131,[]),(147,[]),(189,[]),
    (131,[]),(157,[]),(141,[]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock71 : ∃ data, checkBlock 71 data = true :=
  ⟨[(147,[]),(131,[]),(58,[2,3,7,19,89]),(139,[]),(131,[]),
    (151,[]),(307,[]),(131,[]),(159,[]),(195,[]),
    (131,[]),(339,[]),(141,[]),(131,[]),(6,[2,3,71,167]),
    (5,[2,35573]),(131,[]),(20,[2,3,29,409]),(135,[]),(131,[]),
    (139,[]),(159,[]),(131,[]),(141,[]),(319,[]),
    (131,[]),(5,[2,3,3,37,107]),(135,[]),(131,[]),(20,[2,3,109,109]),
    (241,[]),(131,[]),(135,[]),(10,[2,19,1877]),(131,[]),
    (11,[2,3,11,23,47]),(5,[2,31,1151]),(131,[]),(141,[]),(5,[2,7,5099]),
    (131,[]),(135,[]),(139,[]),(131,[]),(30,[2,3,3,3,3,3,3,7,7]),
    (165,[]),(131,[]),(139,[]),(5,[2,103,347]),(131,[]),
    (5,[2,3,17,701]),(151,[]),(131,[]),(19,[2,3,7,13,131]),(157,[]),
    (131,[]),(2,[2,3,11927]),(187,[]),(131,[]),(145,[]),
    (135,[]),(131,[]),(195,[]),(169,[]),(131,[]),
    (5,[2,3,11941]),(10,[2,35831]),(131,[]),(225,[]),(135,[]),
    (131,[]),(18,[2,3,17,19,37]),(145,[]),(131,[]),(135,[]),
    (141,[]),(131,[]),(171,[]),(151,[]),(131,[]),
    (187,[]),(13,[2,7,23,223]),(131,[]),(135,[]),(5,[2,17,2113]),
    (131,[]),(139,[]),(5,[2,35933]),(131,[]),(23,[2,3,11981]),
    (141,[]),(131,[]),(199,[]),(145,[]),(131,[]),
    (12,[2,3,3,7,571]),(13,[2,11,3271]),(131,[]),(6,[2,3,3,3,31,43]),(5,[2,35993])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock72 : ∃ data, checkBlock 72 data = true :=
  ⟨[(131,[]),(141,[]),(135,[]),(131,[]),(20,[2,3,12007]),
    (29,[2,13,17,163]),(131,[]),(147,[]),(139,[]),(131,[]),
    (10,[2,3,61,197]),(135,[]),(131,[]),(139,[]),(147,[]),
    (131,[]),(135,[]),(14,[2,36083]),(131,[]),(165,[]),
    (231,[]),(131,[]),(5,[2,3,12037]),(7,[2,7,7,11,67]),(131,[]),
    (135,[]),(255,[]),(131,[]),(169,[]),(19,[2,47,769]),
    (131,[]),(11,[2,3,3,3,13,103]),(159,[]),(131,[]),(201,[]),
    (139,[]),(131,[]),(22,[2,3,7,1723]),(10,[2,36191]),(131,[]),
    (145,[]),(189,[]),(131,[]),(151,[]),(135,[]),
    (131,[]),(361,[]),(5,[2,19,1907]),(131,[]),(301,[]),
    (13,[2,36251]),(131,[]),(139,[]),(135,[]),(131,[]),
    (18,[2,3,107,113]),(277,[]),(131,[]),(135,[]),(157,[]),
    (131,[]),(145,[]),(10,[2,11,3301]),(131,[]),(2,[2,3,12107]),
    (14,[2,7,5189]),(131,[]),(135,[]),(141,[]),(131,[]),
    (151,[]),(5,[2,36353]),(131,[]),(13,[2,3,17,23,31]),(139,[]),
    (131,[]),(2,[2,3,67,181]),(13,[2,36383]),(131,[]),(139,[]),
    (175,[]),(131,[]),(11,[2,3,53,229]),(147,[]),(131,[]),
    (225,[]),(135,[]),(131,[]),(20,[2,3,3,4049]),(151,[]),
    (131,[]),(2,[2,3,29,419]),(7,[2,19,19,101]),(131,[]),(141,[]),
    (135,[]),(131,[]),(259,[]),(187,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock73 : ∃ data, checkBlock 73 data = true :=
  ⟨[(135,[]),(139,[]),(131,[]),(231,[]),(5,[2,59,619]),
    (131,[]),(11,[2,3,3,3,3,11,41]),(159,[]),(131,[]),(135,[]),
    (169,[]),(131,[]),(211,[]),(29,[2,36563]),(131,[]),
    (321,[]),(151,[]),(131,[]),(139,[]),(291,[]),
    (131,[]),(147,[]),(165,[]),(131,[]),(19,[2,3,3,13,313]),
    (217,[]),(131,[]),(169,[]),(135,[]),(131,[]),
    (5,[2,3,19,643]),(141,[]),(131,[]),(19,[2,3,11,11,101]),(199,[]),
    (131,[]),(44,[2,3,12227]),(135,[]),(131,[]),(18,[2,3,3,3,3,3,151]),
    (139,[]),(131,[]),(135,[]),(229,[]),(131,[]),
    (139,[]),(141,[]),(131,[]),(2,[2,3,37,331]),(171,[]),
    (131,[]),(135,[]),(5,[2,36761]),(131,[]),(379,[]),
    (5,[2,11,3343]),(131,[]),(141,[]),(10,[2,36791]),(131,[]),
    (217,[]),(14,[2,13,19,149]),(131,[]),(145,[]),(5,[2,36821]),
    (131,[]),(147,[]),(139,[]),(131,[]),(159,[]),
    (135,[]),(131,[]),(141,[]),(10,[2,191,193]),(131,[]),
    (157,[]),(145,[]),(131,[]),(5,[2,3,3,4099]),(135,[]),
    (131,[]),(151,[]),(14,[2,7,5273]),(131,[]),(135,[]),
    (10,[2,36923]),(131,[]),(2,[2,3,13,947]),(5,[2,17,41,53]),(131,[]),
    (391,[]),(5,[2,7,5279]),(131,[]),(135,[]),(10,[2,11,3361]),
    (131,[]),(165,[]),(145,[]),(131,[]),(369,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock74 : ∃ data, checkBlock 74 data = true :=
  ⟨[(171,[]),(131,[]),(207,[]),(5,[2,37013]),(131,[]),
    (19,[2,3,7,41,43]),(139,[]),(131,[]),(151,[]),(141,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(5,[2,3,3,3,1373]),
    (181,[]),(131,[]),(5,[2,3,47,263]),(159,[]),(131,[]),
    (2,[2,3,83,149]),(135,[]),(131,[]),(327,[]),(141,[]),
    (131,[]),(135,[]),(151,[]),(131,[]),(11,[2,3,3,4127]),
    (195,[]),(131,[]),(30,[2,3,3,4129]),(139,[]),(131,[]),
    (135,[]),(5,[2,37181]),(131,[]),(5,[2,3,7,7,11,23]),(201,[]),
    (131,[]),(165,[]),(147,[]),(131,[]),(145,[]),
    (237,[]),(131,[]),(241,[]),(339,[]),(131,[]),
    (139,[]),(5,[2,37253]),(131,[]),(5,[2,3,12421]),(135,[]),
    (131,[]),(301,[]),(10,[2,23,1621]),(131,[]),(2,[2,3,31,401]),
    (189,[]),(131,[]),(20,[2,3,12437]),(135,[]),(131,[]),
    (145,[]),(325,[]),(131,[]),(135,[]),(13,[2,107,349]),
    (131,[]),(2,[2,3,12451]),(139,[]),(131,[]),(169,[]),
    (5,[2,7,19,281]),(131,[]),(135,[]),(145,[]),(131,[]),
    (147,[]),(367,[]),(131,[]),(11,[2,3,3,4157]),(5,[2,23,1627]),
    (131,[]),(171,[]),(141,[]),(131,[]),(5,[2,3,7,1783]),
    (10,[2,17,2203]),(131,[]),(19,[2,3,12487]),(159,[]),(131,[]),
    (277,[]),(135,[]),(131,[]),(295,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock75 : ∃ data, checkBlock 75 data = true :=
  ⟨[(131,[]),(235,[]),(141,[]),(131,[]),(229,[]),
    (135,[]),(131,[]),(399,[]),(5,[2,7,31,173]),(131,[]),
    (135,[]),(147,[]),(131,[]),(141,[]),(291,[]),
    (131,[]),(139,[]),(10,[2,7,7,13,59]),(131,[]),(135,[]),
    (285,[]),(131,[]),(10,[2,3,3,3,7,199]),(5,[2,29,1297]),(131,[]),
    (175,[]),(201,[]),(131,[]),(141,[]),(207,[]),
    (131,[]),(30,[2,3,7,11,163]),(5,[2,13,2897]),(131,[]),(187,[]),
    (5,[2,101,373]),(131,[]),(12,[2,3,3,53,79]),(135,[]),(131,[]),
    (11,[2,3,3,59,71]),(34,[2,37,1019]),(131,[]),(139,[]),(165,[]),
    (131,[]),(145,[]),(135,[]),(131,[]),(147,[]),
    (14,[2,7,5393]),(131,[]),(135,[]),(10,[2,11,3433]),(131,[]),
    (159,[]),(147,[]),(131,[]),(38,[2,3,3,13,17,19]),(259,[]),
    (131,[]),(135,[]),(175,[]),(131,[]),(195,[]),
    (139,[]),(131,[]),(145,[]),(5,[2,79,479]),(131,[]),
    (10,[2,3,11,31,37]),(5,[2,37853]),(131,[]),(169,[]),(19,[2,37871]),
    (131,[]),(367,[]),(29,[2,43,881]),(131,[]),(20,[2,3,17,743]),
    (135,[]),(131,[]),(139,[]),(319,[]),(131,[]),
    (201,[]),(235,[]),(131,[]),(2,[2,3,12647]),(135,[]),
    (131,[]),(141,[]),(151,[]),(131,[]),(135,[]),
    (301,[]),(131,[]),(5,[2,3,11,1151]),(29,[2,37991]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock76 : ∃ data, checkBlock 76 data = true :=
  ⟨[(44,[2,3,53,239]),(145,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(141,[]),(157,[]),(131,[]),(139,[]),
    (10,[2,13,2927]),(131,[]),(11,[2,3,3,4229]),(397,[]),(131,[]),
    (11,[2,3,7,7,7,37]),(5,[2,113,337]),(131,[]),(157,[]),(175,[]),
    (131,[]),(23,[2,3,13,977]),(135,[]),(131,[]),(12,[2,3,97,131]),
    (147,[]),(131,[]),(181,[]),(5,[2,43,887]),(131,[]),
    (12,[2,3,3,3,3,3,157]),(135,[]),(131,[]),(255,[]),(10,[2,7,7,19,41]),
    (131,[]),(135,[]),(10,[2,38183]),(131,[]),(11,[2,3,29,439]),
    (5,[2,38201]),(131,[]),(19,[2,3,47,271]),(141,[]),(131,[]),
    (135,[]),(14,[2,38231]),(131,[]),(139,[]),(10,[2,167,229]),
    (131,[]),(12,[2,3,41,311]),(187,[]),(131,[]),(11,[2,3,12757]),
    (169,[]),(131,[]),(151,[]),(141,[]),(131,[]),
    (2,[2,3,17,751]),(10,[2,38303]),(131,[]),(147,[]),(135,[]),
    (131,[]),(159,[]),(5,[2,38333]),(131,[]),(141,[]),
    (139,[]),(131,[]),(201,[]),(135,[]),(131,[]),
    (139,[]),(157,[]),(131,[]),(135,[]),(159,[]),
    (131,[]),(217,[]),(145,[]),(131,[]),(141,[]),
    (14,[2,7,11,499]),(131,[]),(135,[]),(5,[2,13,2957]),(131,[]),
    (181,[]),(5,[2,38453]),(131,[]),(171,[]),(10,[2,17,31,73]),
    (131,[]),(21,[2,3,101,127]),(139,[]),(131,[]),(295,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock77 : ∃ data, checkBlock 77 data = true :=
  ⟨[(5,[2,38501]),(131,[]),(5,[2,3,3,11,389]),(145,[]),(131,[]),
    (5,[2,3,12841]),(135,[]),(131,[]),(147,[]),(285,[]),
    (131,[]),(211,[]),(361,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(42,[2,3,3,3,1429]),(207,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(157,[]),(5,[2,11,3511]),
    (131,[]),(39,[2,3,79,163]),(5,[2,7,5519]),(131,[]),(135,[]),
    (151,[]),(131,[]),(2,[2,3,7,7,263]),(181,[]),(131,[]),
    (17,[2,3,3,4297]),(139,[]),(131,[]),(12,[2,3,3,3,1433]),(147,[]),
    (131,[]),(139,[]),(267,[]),(131,[]),(171,[]),
    (29,[2,38723]),(131,[]),(141,[]),(135,[]),(131,[]),
    (145,[]),(307,[]),(131,[]),(13,[2,3,3,59,73]),(10,[2,137,283]),
    (131,[]),(12,[2,3,3,31,139]),(135,[]),(131,[]),(2,[2,3,67,193]),
    (199,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (5,[2,3,12941]),(165,[]),(131,[]),(259,[]),(10,[2,7,31,179]),
    (131,[]),(135,[]),(5,[2,38861]),(131,[]),(5,[2,3,3,7,617]),
    (5,[2,38873]),(131,[]),(147,[]),(19,[2,38891]),(131,[]),
    (139,[]),(157,[]),(131,[]),(351,[]),(145,[]),
    (131,[]),(22,[2,3,19,683]),(5,[2,38933]),(131,[]),(199,[]),
    (135,[]),(131,[]),(157,[]),(277,[]),(131,[]),
    (151,[]),(181,[]),(131,[]),(5,[2,3,41,317]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock78 : ∃ data, checkBlock 78 data = true :=
  ⟨[(131,[]),(20,[2,3,13001]),(139,[]),(131,[]),(135,[]),
    (145,[]),(131,[]),(139,[]),(241,[]),(131,[]),
    (211,[]),(165,[]),(131,[]),(135,[]),(141,[]),
    (131,[]),(17,[2,3,7,1861]),(19,[2,11,11,17,19]),(131,[]),(169,[]),
    (13,[2,61,641]),(131,[]),(147,[]),(265,[]),(131,[]),
    (141,[]),(189,[]),(131,[]),(33,[2,3,3,4349]),(139,[]),
    (131,[]),(2,[2,3,31,421]),(135,[]),(131,[]),(285,[]),
    (5,[2,43,911]),(131,[]),(5,[2,3,37,353]),(231,[]),(131,[]),
    (141,[]),(135,[]),(131,[]),(12,[2,3,3,4357]),(175,[]),
    (131,[]),(135,[]),(5,[2,39233]),(131,[]),(12,[2,3,103,127]),
    (157,[]),(131,[]),(145,[]),(147,[]),(131,[]),
    (135,[]),(379,[]),(131,[]),(6,[2,3,7,1871]),(217,[]),
    (131,[]),(5,[2,3,3,11,397]),(30,[2,19,2069]),(131,[]),(77,[2,3,3,17,257]),
    (159,[]),(131,[]),(225,[]),(139,[]),(131,[]),
    (339,[]),(13,[2,23,29,59]),(131,[]),(139,[]),(135,[]),
    (131,[]),(207,[]),(141,[]),(131,[]),(2,[2,3,3,3,1459]),
    (5,[2,31,31,41]),(131,[]),(23,[2,3,3,29,151]),(135,[]),(131,[]),
    (165,[]),(145,[]),(131,[]),(135,[]),(14,[2,39443]),
    (131,[]),(147,[]),(141,[]),(131,[]),(217,[]),
    (139,[]),(131,[]),(135,[]),(147,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock79 : ∃ data, checkBlock 79 data = true :=
  ⟨[(327,[]),(169,[]),(131,[]),(141,[]),(5,[2,39521]),
    (131,[]),(20,[2,3,13177]),(145,[]),(131,[]),(12,[2,3,7,7,269]),
    (19,[2,39551]),(131,[]),(139,[]),(195,[]),(131,[]),
    (17,[2,3,3,4397]),(135,[]),(131,[]),(141,[]),(5,[2,17,17,137]),
    (131,[]),(231,[]),(355,[]),(131,[]),(237,[]),
    (135,[]),(131,[]),(159,[]),(7,[2,7,7,809]),(131,[]),
    (135,[]),(199,[]),(131,[]),(151,[]),(139,[]),
    (131,[]),(147,[]),(13,[2,7,5669]),(131,[]),(135,[]),
    (399,[]),(131,[]),(5,[2,3,7,31,61]),(5,[2,151,263]),(131,[]),
    (181,[]),(357,[]),(131,[]),(189,[]),(229,[]),
    (131,[]),(171,[]),(409,[]),(131,[]),(145,[]),
    (141,[]),(131,[]),(379,[]),(135,[]),(131,[]),
    (151,[]),(139,[]),(131,[]),(11,[2,3,23,577]),(201,[]),
    (131,[]),(157,[]),(135,[]),(131,[]),(5,[2,3,3,19,233]),
    (141,[]),(131,[]),(135,[]),(189,[]),(131,[]),
    (145,[]),(159,[]),(131,[]),(139,[]),(151,[]),
    (131,[]),(135,[]),(14,[2,107,373]),(131,[]),(11,[2,3,7,1901]),
    (10,[2,13,37,83]),(131,[]),(12,[2,3,3,3,3,17,29]),(145,[]),(131,[]),
    (20,[2,3,3,23,193]),(5,[2,39953]),(131,[]),(385,[]),(29,[2,39971]),
    (131,[]),(141,[]),(29,[2,39983]),(131,[]),(2,[2,3,13331])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock80 : ∃ data, checkBlock 80 data = true :=
  ⟨[(135,[]),(131,[]),(171,[]),(207,[]),(131,[]),
    (139,[]),(151,[]),(131,[]),(181,[]),(135,[]),
    (131,[]),(11,[2,3,13,13,79]),(147,[]),(131,[]),(135,[]),
    (5,[2,11,3643]),(131,[]),(20,[2,3,31,431]),(309,[]),(131,[]),
    (267,[]),(14,[2,7,17,337]),(131,[]),(135,[]),(157,[]),
    (131,[]),(5,[2,3,3,7,7,7,13]),(139,[]),(131,[]),(5,[2,3,13381]),
    (259,[]),(131,[]),(175,[]),(141,[]),(131,[]),
    (2,[2,3,7,1913]),(5,[2,23,1747]),(131,[]),(159,[]),(5,[2,40193]),
    (131,[]),(5,[2,3,3,3,1489]),(135,[]),(131,[]),(139,[]),
    (10,[2,19,29,73]),(131,[]),(195,[]),(141,[]),(131,[]),
    (147,[]),(135,[]),(131,[]),(12,[2,3,13421]),(367,[]),
    (131,[]),(135,[]),(10,[2,40283]),(131,[]),(141,[]),
    (5,[2,191,211]),(131,[]),(165,[]),(5,[2,7,13,443]),(131,[]),
    (135,[]),(139,[]),(131,[]),(12,[2,3,7,17,113]),(30,[2,40343]),
    (131,[]),(139,[]),(217,[]),(131,[]),(141,[]),
    (5,[2,47,859]),(131,[]),(145,[]),(29,[2,13,13,239]),(131,[]),
    (2,[2,3,3,67,67]),(147,[]),(131,[]),(259,[]),(135,[]),
    (131,[]),(40,[2,3,13477]),(321,[]),(131,[]),(175,[]),
    (145,[]),(131,[]),(2,[2,3,13487]),(135,[]),(131,[]),
    (189,[]),(5,[2,7,5783]),(131,[]),(135,[]),(237,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock81 : ∃ data, checkBlock 81 data = true :=
  ⟨[(131,[]),(187,[]),(19,[2,17,2383]),(131,[]),(28,[2,3,13,1039]),
    (20,[2,7,7,827]),(131,[]),(135,[]),(5,[2,71,571]),(131,[]),
    (139,[]),(141,[]),(131,[]),(159,[]),(181,[]),
    (131,[]),(30,[2,3,3,3,3,3,167]),(151,[]),(131,[]),(147,[]),
    (5,[2,11,3691]),(131,[]),(5,[2,3,13537]),(171,[]),(131,[]),
    (241,[]),(135,[]),(131,[]),(2,[2,3,19,23,31]),(157,[]),
    (131,[]),(2,[2,3,3,4517]),(139,[]),(131,[]),(12,[2,3,3,4519]),
    (135,[]),(131,[]),(139,[]),(225,[]),(131,[]),
    (135,[]),(255,[]),(131,[]),(235,[]),(151,[]),
    (131,[]),(13,[2,3,13577]),(169,[]),(131,[]),(135,[]),
    (277,[]),(131,[]),(141,[]),(19,[2,40763]),(131,[]),
    (11,[2,3,13591]),(5,[2,13,3137]),(131,[]),(145,[]),(139,[]),
    (131,[]),(207,[]),(159,[]),(131,[]),(147,[]),
    (10,[2,40823]),(131,[]),(29,[2,3,3,13,349]),(135,[]),(131,[]),
    (53,[2,3,3,3,17,89]),(5,[2,40853]),(131,[]),(23,[2,3,53,257]),(171,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(145,[]),
    (307,[]),(131,[]),(135,[]),(175,[]),(131,[]),
    (5,[2,3,3,4547]),(199,[]),(131,[]),(17,[2,3,3,4549]),(141,[]),
    (131,[]),(135,[]),(145,[]),(131,[]),(5,[2,3,7,1951]),
    (147,[]),(131,[]),(5,[2,3,19,719]),(139,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock82 : ∃ data, checkBlock 82 data = true :=
  ⟨[(2,[2,3,79,173]),(14,[2,131,313]),(131,[]),(139,[]),(141,[]),
    (131,[]),(265,[]),(5,[2,37,1109]),(131,[]),(151,[]),
    (135,[]),(131,[]),(169,[]),(145,[]),(131,[]),
    (141,[]),(5,[2,41081]),(131,[]),(41,[2,3,13697]),(135,[]),
    (131,[]),(5,[2,3,3,4567]),(10,[2,7,7,839]),(131,[]),(135,[]),
    (139,[]),(131,[]),(2,[2,3,13711]),(235,[]),(131,[]),
    (141,[]),(5,[2,7,5879]),(131,[]),(135,[]),(195,[]),
    (131,[]),(151,[]),(159,[]),(131,[]),(2,[2,3,3,23,199]),
    (147,[]),(131,[]),(139,[]),(267,[]),(131,[]),
    (157,[]),(40,[2,41231]),(131,[]),(11,[2,3,59,233]),(10,[2,41243]),
    (131,[]),(18,[2,3,13751]),(135,[]),(131,[]),(325,[]),
    (151,[]),(131,[]),(5,[2,3,3,3,11,139]),(397,[]),(131,[]),
    (145,[]),(135,[]),(131,[]),(181,[]),(139,[]),
    (131,[]),(135,[]),(141,[]),(131,[]),(139,[]),
    (319,[]),(131,[]),(18,[2,3,17,811]),(20,[2,7,19,311]),(131,[]),
    (135,[]),(5,[2,41381]),(131,[]),(147,[]),(5,[2,11,53,71]),
    (131,[]),(145,[]),(141,[]),(131,[]),(165,[]),
    (13,[2,23,1801]),(131,[]),(301,[]),(5,[2,29,1429]),(131,[]),
    (19,[2,3,41,337]),(139,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(11,[2,3,3,11,419]),(291,[]),(131,[]),(159,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock83 : ∃ data, checkBlock 83 data = true :=
  ⟨[(5,[2,47,883]),(131,[]),(5,[2,3,101,137]),(135,[]),(131,[]),
    (5,[2,3,13841]),(20,[2,7,17,349]),(131,[]),(135,[]),(147,[]),
    (131,[]),(169,[]),(229,[]),(131,[]),(157,[]),
    (145,[]),(131,[]),(135,[]),(321,[]),(131,[]),
    (17,[2,3,7,7,283]),(10,[2,41603]),(131,[]),(41,[2,3,11,13,97]),(5,[2,41621]),
    (131,[]),(181,[]),(5,[2,17,31,79]),(131,[]),(165,[]),
    (139,[]),(131,[]),(225,[]),(231,[]),(131,[]),
    (139,[]),(135,[]),(131,[]),(5,[2,3,13,1069]),(189,[]),
    (131,[]),(5,[2,3,13901]),(13,[2,53,787]),(131,[]),(2,[2,3,13907]),
    (135,[]),(131,[]),(147,[]),(159,[]),(131,[]),
    (135,[]),(241,[]),(131,[]),(229,[]),(147,[]),
    (131,[]),(2,[2,3,19,733]),(139,[]),(131,[]),(135,[]),
    (141,[]),(131,[]),(145,[]),(369,[]),(131,[]),
    (361,[]),(19,[2,59,709]),(131,[]),(195,[]),(181,[]),
    (131,[]),(141,[]),(157,[]),(131,[]),(139,[]),
    (211,[]),(131,[]),(339,[]),(135,[]),(131,[]),
    (309,[]),(171,[]),(131,[]),(145,[]),(6,[2,11,37,103]),
    (131,[]),(141,[]),(135,[]),(131,[]),(277,[]),
    (14,[2,7,13,461]),(131,[]),(135,[]),(151,[]),(131,[]),
    (255,[]),(139,[]),(131,[]),(40,[2,3,13997]),(7,[2,7,7,857])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock84 : ∃ data, checkBlock 84 data = true :=
  ⟨[(131,[]),(135,[]),(201,[]),(131,[]),(357,[]),
    (39,[2,42023]),(131,[]),(2,[2,3,14011]),(175,[]),(131,[]),
    (159,[]),(279,[]),(131,[]),(6,[2,3,7,2003]),(10,[2,42071]),
    (131,[]),(22,[2,3,13,13,83]),(145,[]),(131,[]),(157,[]),
    (135,[]),(131,[]),(20,[2,3,3,4679]),(139,[]),(131,[]),
    (5,[2,3,19,739]),(10,[2,42131]),(131,[]),(217,[]),(135,[]),
    (131,[]),(11,[2,3,14051]),(165,[]),(131,[]),(135,[]),
    (5,[2,181,233]),(131,[]),(367,[]),(141,[]),(131,[]),
    (139,[]),(10,[2,7,6029]),(131,[]),(135,[]),(5,[2,42221]),
    (131,[]),(5,[2,3,7,2011]),(5,[2,157,269]),(131,[]),(141,[]),
    (22,[2,11,23,167]),(131,[]),(18,[2,3,14087]),(309,[]),(131,[]),
    (187,[]),(231,[]),(131,[]),(169,[]),(379,[]),
    (131,[]),(147,[]),(135,[]),(131,[]),(141,[]),
    (175,[]),(131,[]),(139,[]),(147,[]),(131,[]),
    (199,[]),(135,[]),(131,[]),(321,[]),(211,[]),
    (131,[]),(135,[]),(157,[]),(131,[]),(18,[2,3,13,1087]),
    (265,[]),(131,[]),(399,[]),(5,[2,7,73,83]),(131,[]),
    (135,[]),(241,[]),(131,[]),(157,[]),(139,[]),
    (131,[]),(325,[]),(291,[]),(131,[]),(301,[]),
    (5,[2,42473]),(131,[]),(28,[2,3,7,7,17,17]),(145,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock85 : ∃ data, checkBlock 85 data = true :=
  ⟨[(295,[]),(141,[]),(131,[]),(2,[2,3,37,383]),(135,[]),
    (131,[]),(139,[]),(385,[]),(131,[]),(5,[2,3,3,29,163]),
    (13,[2,17,2503]),(131,[]),(151,[]),(135,[]),(131,[]),
    (21,[2,3,23,617]),(141,[]),(131,[]),(135,[]),(145,[]),
    (131,[]),(267,[]),(29,[2,42611]),(131,[]),(11,[2,3,14207]),
    (13,[2,7,6089]),(131,[]),(135,[]),(139,[]),(131,[]),
    (28,[2,3,3,7,677]),(151,[]),(131,[]),(139,[]),(159,[]),
    (131,[]),(12,[2,3,41,347]),(147,[]),(131,[]),(231,[]),
    (169,[]),(131,[]),(141,[]),(5,[2,11,11,353]),(131,[]),
    (5,[2,3,3,47,101]),(135,[]),(131,[]),(201,[]),(19,[2,42743]),
    (131,[]),(165,[]),(5,[2,61,701]),(131,[]),(259,[]),
    (135,[]),(131,[]),(169,[]),(151,[]),(131,[]),
    (135,[]),(10,[2,23,1861]),(131,[]),(2,[2,3,3,67,71]),(5,[2,42821]),
    (131,[]),(145,[]),(5,[2,7,29,211]),(131,[]),(135,[]),
    (13,[2,73,587]),(131,[]),(139,[]),(187,[]),(131,[]),
    (147,[]),(267,[]),(131,[]),(237,[]),(141,[]),
    (131,[]),(181,[]),(147,[]),(131,[]),(17,[2,3,3,19,251]),
    (10,[2,42923]),(131,[]),(145,[]),(135,[]),(131,[]),
    (21,[2,3,103,139]),(399,[]),(131,[]),(157,[]),(139,[]),
    (131,[]),(159,[]),(135,[]),(131,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock86 : ∃ data, checkBlock 86 data = true :=
  ⟨[(145,[]),(131,[]),(135,[]),(5,[2,43013]),(131,[]),
    (141,[]),(217,[]),(131,[]),(28,[2,3,14347]),(159,[]),
    (131,[]),(135,[]),(199,[]),(131,[]),(5,[2,3,7,7,293]),
    (405,[]),(131,[]),(327,[]),(10,[2,41,1051]),(131,[]),
    (141,[]),(139,[]),(131,[]),(151,[]),(5,[2,13,31,107]),
    (131,[]),(11,[2,3,11,1307]),(409,[]),(131,[]),(21,[2,3,73,197]),
    (135,[]),(131,[]),(2,[2,3,14387]),(301,[]),(131,[]),
    (207,[]),(195,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(199,[]),(14,[2,7,6173]),(131,[]),(135,[]),
    (265,[]),(131,[]),(2,[2,3,14411]),(325,[]),(131,[]),
    (151,[]),(147,[]),(131,[]),(135,[]),(165,[]),
    (131,[]),(235,[]),(141,[]),(131,[]),(17,[2,3,14431]),
    (139,[]),(131,[]),(157,[]),(5,[2,43313]),(131,[]),
    (139,[]),(207,[]),(131,[]),(145,[]),(151,[]),
    (131,[]),(159,[]),(135,[]),(131,[]),(5,[2,3,3,61,79]),
    (351,[]),(131,[]),(6,[2,3,14461]),(10,[2,43391]),(131,[]),
    (189,[]),(135,[]),(131,[]),(141,[]),(5,[2,7,6203]),
    (131,[]),(135,[]),(139,[]),(131,[]),(145,[]),
    (171,[]),(131,[]),(2,[2,3,3,11,439]),(10,[2,7,7,887]),(131,[]),
    (135,[]),(147,[]),(131,[]),(141,[]),(165,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock87 : ∃ data, checkBlock 87 data = true :=
  ⟨[(131,[]),(295,[]),(145,[]),(131,[]),(139,[]),
    (189,[]),(131,[]),(211,[]),(5,[2,43541]),(131,[]),
    (5,[2,3,3,3,1613]),(5,[2,97,449]),(131,[]),(279,[]),(135,[]),
    (131,[]),(229,[]),(195,[]),(131,[]),(11,[2,3,11,1321]),
    (157,[]),(131,[]),(5,[2,3,14537]),(135,[]),(131,[]),
    (171,[]),(139,[]),(131,[]),(135,[]),(319,[]),
    (131,[]),(139,[]),(5,[2,43661]),(131,[]),(147,[]),
    (141,[]),(131,[]),(135,[]),(14,[2,43691]),(131,[]),
    (2,[2,3,7,2081]),(10,[2,11,29,137]),(131,[]),(2,[2,3,3,3,1619]),(5,[2,43721]),
    (131,[]),(277,[]),(175,[]),(131,[]),(217,[]),
    (141,[]),(131,[]),(2,[2,3,29,503]),(139,[]),(131,[]),
    (2,[2,3,14591]),(135,[]),(131,[]),(11,[2,3,11,1327]),(5,[2,43793]),
    (131,[]),(141,[]),(14,[2,193,227]),(131,[]),(20,[2,3,3,3,3,541]),
    (135,[]),(131,[]),(157,[]),(5,[2,7,6263]),(131,[]),
    (135,[]),(357,[]),(131,[]),(165,[]),(19,[2,19,2309]),
    (131,[]),(141,[]),(14,[2,7,6269]),(131,[]),(135,[]),
    (5,[2,11,13,307]),(131,[]),(159,[]),(199,[]),(131,[]),
    (235,[]),(169,[]),(131,[]),(151,[]),(13,[2,43943]),
    (131,[]),(145,[]),(139,[]),(131,[]),(6,[2,3,14657]),
    (159,[]),(131,[]),(139,[]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock88 : ∃ data, checkBlock 88 data = true :=
  ⟨[(2,[2,3,3,4889]),(29,[2,79,557]),(131,[]),(147,[]),(145,[]),
    (131,[]),(211,[]),(135,[]),(131,[]),(187,[]),
    (147,[]),(131,[]),(135,[]),(141,[]),(131,[]),
    (309,[]),(259,[]),(131,[]),(291,[]),(139,[]),
    (131,[]),(135,[]),(10,[2,44111]),(131,[]),(207,[]),
    (145,[]),(131,[]),(189,[]),(141,[]),(131,[]),
    (355,[]),(361,[]),(131,[]),(13,[2,3,3,7,701]),(151,[]),
    (131,[]),(139,[]),(225,[]),(131,[]),(141,[]),
    (135,[]),(131,[]),(10,[2,3,14737]),(5,[2,13,19,179]),(131,[]),
    (369,[]),(13,[2,11,4021]),(131,[]),(147,[]),(135,[]),
    (131,[]),(195,[]),(20,[2,7,6323]),(131,[]),(135,[]),
    (5,[2,44273]),(131,[]),(159,[]),(139,[]),(131,[]),
    (379,[]),(20,[2,7,6329]),(131,[]),(135,[]),(5,[2,23,41,47]),
    (131,[]),(6,[2,3,7,2111]),(5,[2,43,1031]),(131,[]),(259,[]),
    (235,[]),(131,[]),(145,[]),(211,[]),(131,[]),
    (22,[2,3,7,2113]),(165,[]),(131,[]),(175,[]),(147,[]),
    (131,[]),(5,[2,3,19,19,41]),(135,[]),(131,[]),(2,[2,3,13,17,67]),
    (139,[]),(131,[]),(11,[2,3,3,4937]),(6,[2,19,2339]),(131,[]),
    (10,[2,3,3,11,449]),(135,[]),(131,[]),(145,[]),(157,[]),
    (131,[]),(135,[]),(171,[]),(131,[]),(151,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock89 : ∃ data, checkBlock 89 data = true :=
  ⟨[(5,[2,44501]),(131,[]),(139,[]),(255,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(31,[2,3,3,7,7,101]),(10,[2,44543]),
    (131,[]),(2,[2,3,14851]),(5,[2,11,4051]),(131,[]),(225,[]),
    (367,[]),(131,[]),(141,[]),(229,[]),(131,[]),
    (2,[2,3,14867]),(165,[]),(131,[]),(12,[2,3,3,4957]),(135,[]),
    (131,[]),(151,[]),(145,[]),(131,[]),(139,[]),
    (10,[2,44651]),(131,[]),(141,[]),(135,[]),(131,[]),
    (175,[]),(17,[2,7,13,491]),(131,[]),(135,[]),(5,[2,11,17,239]),
    (131,[]),(157,[]),(351,[]),(131,[]),(32,[2,3,3,4969]),
    (151,[]),(131,[]),(135,[]),(171,[]),(131,[]),
    (165,[]),(139,[]),(131,[]),(44,[2,3,43,347]),(279,[]),
    (131,[]),(2,[2,3,11,23,59]),(10,[2,19,2357]),(131,[]),(229,[]),
    (13,[2,71,631]),(131,[]),(147,[]),(5,[2,41,1093]),(131,[]),
    (285,[]),(135,[]),(131,[]),(139,[]),(141,[]),
    (131,[]),(237,[]),(151,[]),(131,[]),(145,[]),
    (135,[]),(131,[]),(5,[2,3,3,4987]),(10,[2,7,11,11,53]),(131,[]),
    (135,[]),(159,[]),(131,[]),(171,[]),(141,[]),
    (131,[]),(201,[]),(5,[2,7,7,7,131]),(131,[]),(135,[]),
    (139,[]),(131,[]),(37,[2,3,7,2141]),(147,[]),(131,[]),
    (139,[]),(14,[2,31,1451]),(131,[]),(10,[2,3,3,4999]),(157,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock90 : ∃ data, checkBlock 90 data = true :=
  ⟨[(131,[]),(6,[2,3,7,2143]),(37,[2,19,23,103]),(131,[]),(255,[]),
    (181,[]),(131,[]),(2,[2,3,17,883]),(135,[]),(131,[]),
    (141,[]),(5,[2,45053]),(131,[]),(5,[2,3,3,3,1669]),(237,[]),
    (131,[]),(2,[2,3,3,5009]),(135,[]),(131,[]),(12,[2,3,15031]),
    (5,[2,7,17,379]),(131,[]),(135,[]),(5,[2,197,229]),(131,[]),
    (5,[2,3,13,13,89]),(29,[2,45131]),(131,[]),(265,[]),(145,[]),
    (131,[]),(135,[]),(169,[]),(131,[]),(139,[]),
    (295,[]),(131,[]),(151,[]),(147,[]),(131,[]),
    (11,[2,3,13,19,61]),(13,[2,17,2659]),(131,[]),(159,[]),(277,[]),
    (131,[]),(189,[]),(141,[]),(131,[]),(169,[]),
    (135,[]),(131,[]),(2,[2,3,3,47,107]),(19,[2,45263]),(131,[]),
    (17,[2,3,15091]),(139,[]),(131,[]),(5,[2,3,31,487]),(135,[]),
    (131,[]),(139,[]),(141,[]),(131,[]),(135,[]),
    (13,[2,61,743]),(131,[]),(199,[]),(157,[]),(131,[]),
    (12,[2,3,3,5039]),(189,[]),(131,[]),(135,[]),(231,[]),
    (131,[]),(145,[]),(267,[]),(131,[]),(11,[2,3,15131]),
    (5,[2,83,547]),(131,[]),(51,[2,3,15137]),(139,[]),(131,[]),
    (5,[2,3,3,7,7,103]),(10,[2,181,251]),(131,[]),(141,[]),(10,[2,29,1567]),
    (131,[]),(13,[2,3,109,139]),(135,[]),(131,[]),(327,[]),
    (5,[2,37,1229]),(131,[]),(145,[]),(165,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock91 : ∃ data, checkBlock 91 data = true :=
  ⟨[(139,[]),(135,[]),(131,[]),(355,[]),(309,[]),
    (131,[]),(135,[]),(147,[]),(131,[]),(207,[]),
    (145,[]),(131,[]),(421,[]),(10,[2,7,23,283]),(131,[]),
    (135,[]),(5,[2,19,2399]),(131,[]),(5,[2,3,7,13,167]),(195,[]),
    (131,[]),(351,[]),(139,[]),(131,[]),(19,[2,3,3,37,137]),
    (141,[]),(131,[]),(139,[]),(5,[2,45641]),(131,[]),
    (5,[2,3,15217]),(145,[]),(131,[]),(399,[]),(135,[]),
    (131,[]),(339,[]),(29,[2,11,4153]),(131,[]),(2,[2,3,3,5077]),
    (141,[]),(131,[]),(12,[2,3,3,3,1693]),(135,[]),(131,[]),
    (147,[]),(13,[2,7,47,139]),(131,[]),(135,[]),(139,[]),
    (131,[]),(141,[]),(147,[]),(131,[]),(159,[]),
    (171,[]),(131,[]),(135,[]),(13,[2,29,1579]),(131,[]),
    (175,[]),(229,[]),(131,[]),(187,[]),(241,[]),
    (131,[]),(139,[]),(159,[]),(131,[]),(405,[]),
    (30,[2,13,3527]),(131,[]),(165,[]),(157,[]),(131,[]),
    (151,[]),(135,[]),(131,[]),(145,[]),(391,[]),
    (131,[]),(11,[2,3,11,13,107]),(14,[2,31,1481]),(131,[]),(157,[]),
    (135,[]),(131,[]),(2,[2,3,61,251]),(139,[]),(131,[]),
    (135,[]),(201,[]),(131,[]),(139,[]),(10,[2,45971]),
    (131,[]),(169,[]),(13,[2,7,6569]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock92 : ∃ data, checkBlock 92 data = true :=
  ⟨[(5,[2,157,293]),(131,[]),(151,[]),(141,[]),(131,[]),
    (211,[]),(171,[]),(131,[]),(2,[2,3,103,149]),(199,[]),
    (131,[]),(2,[2,3,3,7,17,43]),(145,[]),(131,[]),(33,[2,3,3,5119]),
    (139,[]),(131,[]),(165,[]),(135,[]),(131,[]),
    (2,[2,3,11,11,127]),(147,[]),(131,[]),(11,[2,3,19,809]),(5,[2,17,2713]),
    (131,[]),(385,[]),(135,[]),(131,[]),(141,[]),
    (369,[]),(131,[]),(135,[]),(145,[]),(131,[]),
    (13,[2,3,15391]),(5,[2,46181]),(131,[]),(5,[2,3,89,173]),(5,[2,7,6599]),
    (131,[]),(135,[]),(157,[]),(131,[]),(141,[]),
    (321,[]),(131,[]),(11,[2,3,3,11,467]),(151,[]),(131,[]),
    (5,[2,3,3,3,3,571]),(5,[2,23,2011]),(131,[]),(195,[]),(139,[]),
    (131,[]),(279,[]),(39,[2,31,1493]),(131,[]),(139,[]),
    (135,[]),(131,[]),(43,[2,3,43,359]),(5,[2,29,1597]),(131,[]),
    (6,[2,3,3,5147]),(147,[]),(131,[]),(12,[2,3,3,19,271]),(135,[]),
    (131,[]),(18,[2,3,15451]),(5,[2,7,37,179]),(131,[]),(135,[]),
    (291,[]),(131,[]),(5,[2,3,15461]),(159,[]),(131,[]),
    (145,[]),(139,[]),(131,[]),(135,[]),(355,[]),
    (131,[]),(6,[2,3,3,7,11,67]),(5,[2,59,787]),(131,[]),(157,[]),
    (189,[]),(131,[]),(171,[]),(14,[2,97,479]),(131,[]),
    (169,[]),(141,[]),(131,[]),(139,[]),(5,[2,19,2447])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock93 : ∃ data, checkBlock 93 data = true :=
  ⟨[(131,[]),(145,[]),(135,[]),(131,[]),(147,[]),
    (10,[2,46523]),(131,[]),(141,[]),(5,[2,11,4231]),(131,[]),
    (5,[2,3,59,263]),(135,[]),(131,[]),(151,[]),(145,[]),
    (131,[]),(135,[]),(279,[]),(131,[]),(18,[2,3,3,31,167]),
    (139,[]),(131,[]),(141,[]),(181,[]),(131,[]),
    (135,[]),(10,[2,13,17,211]),(131,[]),(2,[2,3,7,2221]),(19,[2,46643]),
    (131,[]),(2,[2,3,15551]),(5,[2,29,1609]),(131,[]),(397,[]),
    (145,[]),(131,[]),(201,[]),(10,[2,46691]),(131,[]),
    (151,[]),(29,[2,46703]),(131,[]),(11,[2,3,23,677]),(135,[]),
    (131,[]),(5,[2,3,37,421]),(139,[]),(131,[]),(6,[2,3,15581]),
    (10,[2,46751]),(131,[]),(20,[2,3,11,13,109]),(135,[]),(131,[]),
    (267,[]),(5,[2,7,41,163]),(131,[]),(135,[]),(141,[]),
    (131,[]),(5,[2,3,15601]),(379,[]),(131,[]),(139,[]),
    (165,[]),(131,[]),(135,[]),(5,[2,31,1511]),(131,[]),
    (45,[2,3,7,23,97]),(211,[]),(131,[]),(147,[]),(141,[]),
    (131,[]),(2,[2,3,3,5209]),(169,[]),(131,[]),(12,[2,3,7,7,11,29]),
    (147,[]),(131,[]),(145,[]),(5,[2,43,1091]),(131,[]),
    (141,[]),(135,[]),(131,[]),(351,[]),(29,[2,13,23,157]),
    (131,[]),(139,[]),(5,[2,151,311]),(131,[]),(165,[]),
    (135,[]),(131,[]),(21,[2,3,15661]),(13,[2,7,7,7,137]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock94 : ∃ data, checkBlock 94 data = true :=
  ⟨[(135,[]),(10,[2,11,4273]),(131,[]),(145,[]),(285,[]),
    (131,[]),(23,[2,3,61,257]),(237,[]),(131,[]),(135,[]),
    (267,[]),(131,[]),(189,[]),(139,[]),(131,[]),
    (159,[]),(145,[]),(131,[]),(147,[]),(225,[]),
    (131,[]),(10,[2,3,7,2243]),(187,[]),(131,[]),(201,[]),
    (207,[]),(131,[]),(235,[]),(135,[]),(131,[]),
    (139,[]),(5,[2,61,773]),(131,[]),(5,[2,3,79,199]),(13,[2,43,1097]),
    (131,[]),(325,[]),(135,[]),(131,[]),(165,[]),
    (195,[]),(131,[]),(135,[]),(5,[2,31,1523]),(131,[]),
    (10,[2,3,3,3,3,11,53]),(29,[2,73,647]),(131,[]),(17,[2,3,3,29,181]),(147,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(5,[2,3,7,2251]),
    (5,[2,41,1153]),(131,[]),(139,[]),(10,[2,19,19,131]),(131,[]),
    (13,[2,3,15767]),(217,[]),(131,[]),(141,[]),(159,[]),
    (131,[]),(309,[]),(265,[]),(131,[]),(5,[2,3,43,367]),
    (135,[]),(131,[]),(20,[2,3,15787]),(34,[2,47363]),(131,[]),
    (2,[2,3,15791]),(321,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(241,[]),(10,[2,7,13,521]),(131,[]),(135,[]),
    (10,[2,47,1009]),(131,[]),(147,[]),(367,[]),(131,[]),
    (19,[2,3,15817]),(5,[2,7,6779]),(131,[]),(135,[]),(147,[]),
    (131,[]),(139,[]),(151,[]),(131,[]),(171,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock95 : ∃ data, checkBlock 95 data = true :=
  ⟨[(5,[2,47501]),(131,[]),(295,[]),(5,[2,47513]),(131,[]),
    (145,[]),(10,[2,11,29,149]),(131,[]),(2,[2,3,13,23,53]),(10,[2,47543]),
    (131,[]),(37,[2,3,11,11,131]),(135,[]),(131,[]),(5,[2,3,101,157]),
    (141,[]),(131,[]),(187,[]),(139,[]),(131,[]),
    (2,[2,3,3,3,41,43]),(135,[]),(131,[]),(139,[]),(151,[]),
    (131,[]),(135,[]),(7,[2,19,23,109]),(131,[]),(5,[2,3,15881]),
    (141,[]),(131,[]),(147,[]),(10,[2,7,11,619]),(131,[]),
    (135,[]),(175,[]),(131,[]),(23,[2,3,3,7,757]),(145,[]),
    (131,[]),(141,[]),(165,[]),(131,[]),(17,[2,3,15907]),
    (139,[]),(131,[]),(30,[2,3,7,2273]),(5,[2,47741]),(131,[]),
    (171,[]),(5,[2,17,53,53]),(131,[]),(5,[2,3,3,3,29,61]),(135,[]),
    (131,[]),(141,[]),(355,[]),(131,[]),(189,[]),
    (5,[2,13,3677]),(131,[]),(139,[]),(135,[]),(131,[]),
    (229,[]),(399,[]),(131,[]),(135,[]),(231,[]),
    (131,[]),(17,[2,3,3,13,409]),(5,[2,11,19,229]),(131,[]),(195,[]),
    (5,[2,7,7,977]),(131,[]),(135,[]),(14,[2,83,577]),(131,[]),
    (12,[2,3,7,2281]),(277,[]),(131,[]),(207,[]),(139,[]),
    (131,[]),(145,[]),(165,[]),(131,[]),(139,[]),
    (157,[]),(131,[]),(41,[2,3,3,73,73]),(141,[]),(131,[]),
    (2,[2,3,15991]),(135,[]),(131,[]),(181,[]),(13,[2,11,4363])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock96 : ∃ data, checkBlock 96 data = true :=
  ⟨[(131,[]),(147,[]),(259,[]),(131,[]),(17,[2,3,16007]),
    (135,[]),(131,[]),(145,[]),(141,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(225,[]),(207,[]),
    (131,[]),(151,[]),(10,[2,7,6869]),(131,[]),(135,[]),
    (145,[]),(131,[]),(5,[2,3,7,29,79]),(169,[]),(131,[]),
    (237,[]),(19,[2,48131]),(131,[]),(139,[]),(201,[]),
    (131,[]),(321,[]),(5,[2,17,2833]),(131,[]),(141,[]),
    (151,[]),(131,[]),(157,[]),(135,[]),(131,[]),
    (277,[]),(145,[]),(131,[]),(339,[]),(5,[2,48221]),
    (131,[]),(147,[]),(135,[]),(131,[]),(23,[2,3,13,1237]),
    (139,[]),(131,[]),(135,[]),(13,[2,17,17,167]),(131,[]),
    (139,[]),(189,[]),(131,[]),(187,[]),(5,[2,7,6899]),
    (131,[]),(135,[]),(151,[]),(131,[]),(2,[2,3,3,7,13,59]),
    (255,[]),(131,[]),(2,[2,3,16111]),(237,[]),(131,[]),
    (5,[2,3,71,227]),(141,[]),(131,[]),(325,[]),(217,[]),
    (131,[]),(22,[2,3,16127]),(139,[]),(131,[]),(2,[2,3,3,19,283]),
    (135,[]),(131,[]),(11,[2,3,3,3,11,163]),(5,[2,48413]),(131,[]),
    (11,[2,3,16141]),(141,[]),(131,[]),(145,[]),(135,[]),
    (131,[]),(12,[2,3,31,521]),(231,[]),(131,[]),(135,[]),
    (157,[]),(131,[]),(141,[]),(421,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock97 : ∃ data, checkBlock 97 data = true :=
  ⟨[(28,[2,3,3,17,317]),(14,[2,7,13,13,41]),(131,[]),(135,[]),(181,[]),
    (131,[]),(157,[]),(241,[]),(131,[]),(145,[]),
    (29,[2,47,1033]),(131,[]),(141,[]),(14,[2,48563]),(131,[]),
    (147,[]),(139,[]),(131,[]),(285,[]),(5,[2,48593]),
    (131,[]),(139,[]),(135,[]),(131,[]),(175,[]),
    (159,[]),(131,[]),(151,[]),(5,[2,127,383]),(131,[]),
    (5,[2,3,16217]),(135,[]),(131,[]),(39,[2,3,3,5407]),(439,[]),
    (131,[]),(135,[]),(14,[2,89,547]),(131,[]),(11,[2,3,16231]),
    (385,[]),(131,[]),(23,[2,3,13,1249]),(139,[]),(131,[]),
    (135,[]),(10,[2,48731]),(131,[]),(199,[]),(141,[]),
    (131,[]),(409,[]),(5,[2,48761]),(131,[]),(151,[]),
    (5,[2,17,19,151]),(131,[]),(171,[]),(29,[2,97,503]),(131,[]),
    (139,[]),(10,[2,37,1319]),(131,[]),(361,[]),(135,[]),
    (131,[]),(255,[]),(229,[]),(131,[]),(5,[2,3,3,3,3,3,3,67]),
    (169,[]),(131,[]),(207,[]),(135,[]),(131,[]),
    (141,[]),(187,[]),(131,[]),(135,[]),(7,[2,13,3761]),
    (131,[]),(175,[]),(139,[]),(131,[]),(2,[2,3,23,709]),
    (14,[2,7,29,241]),(131,[]),(135,[]),(5,[2,109,449]),(131,[]),
    (141,[]),(147,[]),(131,[]),(22,[2,3,19,859]),(19,[2,13,3767]),
    (131,[]),(291,[]),(10,[2,11,61,73]),(131,[]),(32,[2,3,7,2333])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock98 : ∃ data, checkBlock 98 data = true :=
  ⟨[(151,[]),(131,[]),(211,[]),(189,[]),(131,[]),
    (20,[2,3,3,13,419]),(135,[]),(131,[]),(171,[]),(139,[]),
    (131,[]),(145,[]),(5,[2,71,691]),(131,[]),(42,[2,3,11,1487]),
    (135,[]),(131,[]),(217,[]),(175,[]),(131,[]),
    (135,[]),(13,[2,49103]),(131,[]),(30,[2,3,3,3,17,107]),(145,[]),
    (131,[]),(139,[]),(141,[]),(131,[]),(135,[]),
    (325,[]),(131,[]),(17,[2,3,7,2341]),(10,[2,211,233]),(131,[]),
    (28,[2,3,37,443]),(147,[]),(131,[]),(165,[]),(5,[2,49193]),
    (131,[]),(6,[2,3,3,7,11,71]),(141,[]),(131,[]),(11,[2,3,3,3,1823]),
    (145,[]),(131,[]),(12,[2,3,16411]),(135,[]),(131,[]),
    (265,[]),(5,[2,49253]),(131,[]),(139,[]),(10,[2,29,1699]),
    (131,[]),(11,[2,3,16427]),(135,[]),(131,[]),(439,[]),
    (279,[]),(131,[]),(135,[]),(5,[2,11,4483]),(131,[]),
    (151,[]),(10,[2,49331]),(131,[]),(141,[]),(157,[]),
    (131,[]),(135,[]),(397,[]),(131,[]),(147,[]),
    (139,[]),(131,[]),(411,[]),(301,[]),(131,[]),
    (157,[]),(10,[2,127,389]),(131,[]),(165,[]),(225,[]),
    (131,[]),(237,[]),(5,[2,49433]),(131,[]),(74,[2,3,16481]),
    (135,[]),(131,[]),(139,[]),(10,[2,49463]),(131,[]),
    (87,[2,3,3,23,239]),(5,[2,49481]),(131,[]),(159,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock99 : ∃ data, checkBlock 99 data = true :=
  ⟨[(131,[]),(309,[]),(10,[2,7,11,643]),(131,[]),(135,[]),
    (141,[]),(131,[]),(285,[]),(5,[2,107,463]),(131,[]),
    (43,[2,3,83,199]),(151,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(181,[]),(259,[]),(131,[]),(139,[]),
    (141,[]),(131,[]),(11,[2,3,23,719]),(195,[]),(131,[]),
    (189,[]),(145,[]),(131,[]),(229,[]),(171,[]),
    (131,[]),(141,[]),(135,[]),(131,[]),(169,[]),
    (5,[2,13,3821]),(131,[]),(6,[2,3,16561]),(151,[]),(131,[]),
    (235,[]),(135,[]),(131,[]),(147,[]),(405,[]),
    (131,[]),(135,[]),(145,[]),(131,[]),(5,[2,3,3,5527]),
    (147,[]),(131,[]),(19,[2,3,3,3,19,97]),(14,[2,7,7109]),(131,[]),
    (135,[]),(5,[2,67,743]),(131,[]),(139,[]),(181,[]),
    (131,[]),(6,[2,3,13,1277]),(19,[2,49811]),(131,[]),(11,[2,3,16607]),
    (379,[]),(131,[]),(2,[2,3,3,7,7,113]),(211,[]),(131,[]),
    (307,[]),(5,[2,49853]),(131,[]),(159,[]),(135,[]),
    (131,[]),(195,[]),(19,[2,83,601]),(131,[]),(2,[2,3,16631]),
    (139,[]),(131,[]),(41,[2,3,127,131]),(135,[]),(131,[]),
    (139,[]),(165,[]),(131,[]),(135,[]),(187,[]),
    (131,[]),(2,[2,3,16651]),(5,[2,47,1063]),(131,[]),(145,[]),
    (217,[]),(131,[]),(135,[]),(141,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock100 : ∃ data, checkBlock 100 data = true :=
  ⟨[(2,[2,3,7,2381]),(225,[]),(131,[]),(151,[]),(5,[2,50021]),
    (131,[]),(175,[]),(139,[]),(131,[]),(141,[]),
    (10,[2,50051]),(131,[]),(187,[]),(351,[]),(131,[]),
    (145,[]),(135,[]),(131,[]),(23,[2,3,59,283]),(147,[]),
    (131,[]),(19,[2,3,3,19,293]),(159,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(29,[2,3,17,983]),(145,[]),(131,[]),
    (135,[]),(165,[]),(131,[]),(169,[]),(10,[2,11,4561]),
    (131,[]),(2,[2,3,43,389]),(295,[]),(131,[]),(135,[]),
    (6,[2,17,2953]),(131,[]),(361,[]),(157,[]),(131,[]),
    (5,[2,3,16741]),(139,[]),(131,[]),(11,[2,3,16747]),(145,[]),
    (131,[]),(139,[]),(5,[2,50261]),(131,[]),(157,[]),
    (5,[2,50273]),(131,[]),(147,[]),(135,[]),(131,[]),
    (165,[]),(141,[]),(131,[]),(175,[]),(147,[]),
    (131,[]),(171,[]),(135,[]),(131,[]),(235,[]),
    (10,[2,7,7193]),(131,[]),(135,[]),(139,[]),(131,[]),
    (2,[2,3,3,29,193]),(141,[]),(131,[]),(225,[]),(6,[2,7,23,313]),
    (131,[]),(135,[]),(13,[2,50411]),(131,[]),(159,[]),
    (29,[2,50423]),(131,[]),(141,[]),(207,[]),(131,[]),
    (139,[]),(5,[2,13,3881]),(131,[]),(51,[2,3,3,3,3,7,89]),(30,[2,41,1231]),
    (131,[]),(145,[]),(159,[]),(131,[]),(2,[2,3,16831])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock101 : ∃ data, checkBlock 101 data = true :=
  ⟨[(135,[]),(131,[]),(141,[]),(5,[2,50513]),(131,[]),
    (165,[]),(20,[2,13,13,13,23]),(131,[]),(399,[]),(135,[]),
    (131,[]),(12,[2,3,3,41,137]),(139,[]),(131,[]),(135,[]),
    (169,[]),(131,[]),(139,[]),(10,[2,50591]),(131,[]),
    (19,[2,3,101,167]),(13,[2,7,7229]),(131,[]),(135,[]),(265,[]),
    (131,[]),(259,[]),(5,[2,11,4603]),(131,[]),(5,[2,3,3,17,331]),
    (145,[]),(131,[]),(2,[2,3,3,13,433]),(147,[]),(131,[]),
    (11,[2,3,7,19,127]),(5,[2,59,859]),(131,[]),(5,[2,3,61,277]),(139,[]),
    (131,[]),(151,[]),(135,[]),(131,[]),(189,[]),
    (357,[]),(131,[]),(2,[2,3,3,3,1879]),(5,[2,50741]),(131,[]),
    (5,[2,3,3,5639]),(135,[]),(131,[]),(5,[2,3,16921]),(141,[]),
    (131,[]),(135,[]),(175,[]),(131,[]),(157,[]),
    (13,[2,37,1373]),(131,[]),(279,[]),(5,[2,7,7,17,61]),(131,[]),
    (135,[]),(10,[2,11,4621]),(131,[]),(151,[]),(189,[]),
    (131,[]),(147,[]),(13,[2,181,281]),(131,[]),(199,[]),
    (5,[2,50873]),(131,[]),(277,[]),(139,[]),(131,[]),
    (141,[]),(19,[2,109,467]),(131,[]),(139,[]),(135,[]),
    (131,[]),(5,[2,3,3,5659]),(151,[]),(131,[]),(267,[]),
    (309,[]),(131,[]),(355,[]),(135,[]),(131,[]),
    (225,[]),(5,[2,7,7283]),(131,[]),(135,[]),(5,[2,50993])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock102 : ∃ data, checkBlock 102 data = true :=
  ⟨[(131,[]),(211,[]),(10,[2,29,1759]),(131,[]),(28,[2,3,3,5669]),
    (139,[]),(131,[]),(135,[]),(159,[]),(131,[]),
    (11,[2,3,7,11,13,17]),(5,[2,19,2687]),(131,[]),(201,[]),(151,[]),
    (131,[]),(147,[]),(141,[]),(131,[]),(145,[]),
    (5,[2,137,373]),(131,[]),(139,[]),(279,[]),(131,[]),
    (187,[]),(135,[]),(131,[]),(157,[]),(361,[]),
    (131,[]),(391,[]),(141,[]),(131,[]),(181,[]),
    (135,[]),(131,[]),(12,[2,3,3,11,11,47]),(171,[]),(131,[]),
    (135,[]),(13,[2,51203]),(131,[]),(141,[]),(139,[]),
    (131,[]),(207,[]),(147,[]),(131,[]),(135,[]),
    (10,[2,53,967]),(131,[]),(47,[2,3,7,2441]),(145,[]),(131,[]),
    (2,[2,3,3,3,3,3,211]),(5,[2,19,2699]),(131,[]),(141,[]),(5,[2,11,4663]),
    (131,[]),(45,[2,3,7,7,349]),(169,[]),(131,[]),(28,[2,3,17107]),
    (19,[2,17,3019]),(131,[]),(20,[2,3,71,241]),(135,[]),(131,[]),
    (159,[]),(139,[]),(131,[]),(171,[]),(255,[]),
    (131,[]),(2,[2,3,3,3,11,173]),(135,[]),(131,[]),(151,[]),
    (351,[]),(131,[]),(135,[]),(159,[]),(131,[]),
    (147,[]),(157,[]),(131,[]),(139,[]),(265,[]),
    (131,[]),(135,[]),(147,[]),(131,[]),(241,[]),
    (141,[]),(131,[]),(6,[2,3,131,131]),(10,[2,11,31,151]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock103 : ∃ data, checkBlock 103 data = true :=
  ⟨[(145,[]),(10,[2,51503]),(131,[]),(397,[]),(5,[2,51521]),
    (131,[]),(151,[]),(5,[2,29,1777]),(131,[]),(5,[2,3,3,3,23,83]),
    (135,[]),(131,[]),(12,[2,3,3,17,337]),(409,[]),(131,[]),
    (139,[]),(199,[]),(131,[]),(11,[2,3,29,593]),(135,[]),
    (131,[]),(141,[]),(237,[]),(131,[]),(135,[]),
    (151,[]),(131,[]),(165,[]),(307,[]),(131,[]),
    (147,[]),(5,[2,7,47,157]),(131,[]),(135,[]),(145,[]),
    (131,[]),(141,[]),(139,[]),(131,[]),(28,[2,3,17231]),
    (181,[]),(131,[]),(5,[2,3,11,1567]),(187,[]),(131,[]),
    (159,[]),(285,[]),(131,[]),(2,[2,3,3,5749]),(367,[]),
    (131,[]),(217,[]),(135,[]),(131,[]),(139,[]),
    (145,[]),(131,[]),(28,[2,3,41,421]),(14,[2,67,773]),(131,[]),
    (441,[]),(135,[]),(131,[]),(301,[]),(5,[2,7,11,673]),
    (131,[]),(135,[]),(211,[]),(131,[]),(10,[2,3,11,1571]),
    (19,[2,19,2729]),(131,[]),(11,[2,3,59,293]),(141,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(195,[]),(5,[2,51893]),
    (131,[]),(139,[]),(175,[]),(131,[]),(11,[2,3,3,3,3,641]),
    (241,[]),(131,[]),(2,[2,3,7,2473]),(141,[]),(131,[]),
    (6,[2,3,17317]),(157,[]),(131,[]),(231,[]),(135,[]),
    (131,[]),(22,[2,3,17327]),(29,[2,227,229]),(131,[]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock104 : ∃ data, checkBlock 104 data = true :=
  ⟨[(5,[2,149,349]),(131,[]),(145,[]),(135,[]),(131,[]),
    (5,[2,3,17341]),(147,[]),(131,[]),(135,[]),(10,[2,71,733]),
    (131,[]),(20,[2,3,17351]),(5,[2,79,659]),(131,[]),(141,[]),
    (5,[2,7,43,173]),(131,[]),(135,[]),(14,[2,13,4007]),(131,[]),
    (139,[]),(10,[2,52103]),(131,[]),(145,[]),(5,[2,52121]),
    (131,[]),(169,[]),(255,[]),(131,[]),(5,[2,3,7,13,191]),
    (165,[]),(131,[]),(29,[2,3,17387]),(10,[2,52163]),(131,[]),
    (11,[2,3,3,11,17,31]),(135,[]),(131,[]),(5,[2,3,3,3,1933]),(175,[]),
    (131,[]),(259,[]),(139,[]),(131,[]),(147,[]),
    (135,[]),(131,[]),(139,[]),(291,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(5,[2,3,3,5807]),(19,[2,167,313]),
    (131,[]),(159,[]),(145,[]),(131,[]),(135,[]),
    (157,[]),(131,[]),(33,[2,3,7,47,53]),(151,[]),(131,[]),
    (355,[]),(141,[]),(131,[]),(12,[2,3,73,239]),(139,[]),
    (131,[]),(2,[2,3,3,3,7,277]),(5,[2,52361]),(131,[]),(6,[2,3,3,11,23,23]),
    (147,[]),(131,[]),(141,[]),(135,[]),(131,[]),
    (33,[2,3,17467]),(439,[]),(131,[]),(12,[2,3,17471]),(187,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(181,[]),
    (151,[]),(131,[]),(135,[]),(445,[]),(131,[]),
    (13,[2,3,17491]),(171,[]),(131,[]),(405,[]),(5,[2,7,7499])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock105 : ∃ data, checkBlock 105 data = true :=
  ⟨[(131,[]),(135,[]),(14,[2,52511]),(131,[]),(145,[]),
    (201,[]),(131,[]),(157,[]),(139,[]),(131,[]),
    (189,[]),(5,[2,52553]),(131,[]),(139,[]),(10,[2,52571]),
    (131,[]),(231,[]),(34,[2,52583]),(131,[]),(421,[]),
    (135,[]),(131,[]),(267,[]),(5,[2,11,4783]),(131,[]),
    (145,[]),(10,[2,52631]),(131,[]),(255,[]),(135,[]),
    (131,[]),(159,[]),(5,[2,7,7523]),(131,[]),(135,[]),
    (139,[]),(131,[]),(11,[2,3,17,1033]),(145,[]),(131,[]),
    (237,[]),(10,[2,7,7529]),(131,[]),(135,[]),(141,[]),
    (131,[]),(391,[]),(5,[2,52733]),(131,[]),(165,[]),
    (39,[2,17,29,107]),(131,[]),(139,[]),(10,[2,19,2777]),(131,[]),
    (141,[]),(5,[2,47,1123]),(131,[]),(147,[]),(145,[]),
    (131,[]),(5,[2,3,3,5867]),(135,[]),(131,[]),(217,[]),
    (157,[]),(131,[]),(30,[2,3,11,1601]),(5,[2,53,997]),(131,[]),
    (141,[]),(135,[]),(131,[]),(12,[2,3,67,263]),(139,[]),
    (131,[]),(135,[]),(14,[2,52883]),(131,[]),(139,[]),
    (159,[]),(131,[]),(151,[]),(225,[]),(131,[]),
    (135,[]),(14,[2,41,1291]),(131,[]),(2,[2,3,7,2521]),(147,[]),
    (131,[]),(19,[2,3,19,929]),(201,[]),(131,[]),(5,[2,3,17657]),
    (181,[]),(131,[]),(22,[2,3,3,7,29,29]),(10,[2,19,2789]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock106 : ∃ data, checkBlock 106 data = true :=
  ⟨[(199,[]),(139,[]),(131,[]),(357,[]),(135,[]),
    (131,[]),(145,[]),(141,[]),(131,[]),(6,[2,3,17681]),
    (14,[2,53051]),(131,[]),(20,[2,3,23,769]),(135,[]),(131,[]),
    (307,[]),(5,[2,7,7583]),(131,[]),(135,[]),(5,[2,53093]),
    (131,[]),(19,[2,3,31,571]),(141,[]),(131,[]),(11,[2,3,17707]),
    (309,[]),(131,[]),(135,[]),(151,[]),(131,[]),
    (5,[2,3,7,2531]),(5,[2,23,2311]),(131,[]),(141,[]),(147,[]),
    (131,[]),(11,[2,3,3,19,311]),(19,[2,13,4091]),(131,[]),(319,[]),
    (139,[]),(131,[]),(159,[]),(5,[2,127,419]),(131,[]),
    (139,[]),(135,[]),(131,[]),(141,[]),(19,[2,37,1439]),
    (131,[]),(201,[]),(165,[]),(131,[]),(5,[2,3,3,3,1973]),
    (135,[]),(131,[]),(189,[]),(181,[]),(131,[]),
    (135,[]),(145,[]),(131,[]),(2,[2,3,13,1367]),(175,[]),
    (131,[]),(5,[2,3,29,613]),(139,[]),(131,[]),(135,[]),
    (14,[2,31,1721]),(131,[]),(147,[]),(10,[2,17,43,73]),(131,[]),
    (2,[2,3,17791]),(369,[]),(131,[]),(42,[2,3,13,37,37]),(5,[2,107,499]),
    (131,[]),(157,[]),(19,[2,53411]),(131,[]),(139,[]),
    (141,[]),(131,[]),(12,[2,3,3,3,1979]),(135,[]),(131,[]),
    (5,[2,3,3,5939]),(5,[2,53453]),(131,[]),(151,[]),(357,[]),
    (131,[]),(21,[2,3,17827]),(135,[]),(131,[]),(211,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock107 : ∃ data, checkBlock 107 data = true :=
  ⟨[(141,[]),(131,[]),(135,[]),(147,[]),(131,[]),
    (295,[]),(139,[]),(131,[]),(145,[]),(301,[]),
    (131,[]),(135,[]),(5,[2,19,2819]),(131,[]),(435,[]),
    (237,[]),(131,[]),(159,[]),(19,[2,53591]),(131,[]),
    (151,[]),(175,[]),(131,[]),(22,[2,3,3,7,23,37]),(5,[2,29,43,43]),
    (131,[]),(141,[]),(195,[]),(131,[]),(145,[]),
    (135,[]),(131,[]),(51,[2,3,31,577]),(139,[]),(131,[]),
    (11,[2,3,17891]),(229,[]),(131,[]),(201,[]),(135,[]),
    (131,[]),(147,[]),(145,[]),(131,[]),(135,[]),
    (267,[]),(131,[]),(2,[2,3,17911]),(147,[]),(131,[]),
    (139,[]),(5,[2,7,7,1097]),(131,[]),(135,[]),(169,[]),
    (131,[]),(65,[2,3,7,13,197]),(391,[]),(131,[]),(399,[]),
    (5,[2,11,67,73]),(131,[]),(409,[]),(141,[]),(131,[]),
    (68,[2,3,7,11,233]),(151,[]),(131,[]),(385,[]),(39,[2,23,2341]),
    (131,[]),(165,[]),(135,[]),(131,[]),(291,[]),
    (5,[2,17,3169]),(131,[]),(139,[]),(141,[]),(131,[]),
    (195,[]),(135,[]),(131,[]),(20,[2,3,17971]),(5,[2,7,7703]),
    (131,[]),(135,[]),(18,[2,11,4903]),(131,[]),(141,[]),
    (10,[2,53951]),(131,[]),(17,[2,3,17987]),(30,[2,7,13,593]),(131,[]),
    (135,[]),(235,[]),(131,[]),(211,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock108 : ∃ data, checkBlock 108 data = true :=
  ⟨[(131,[]),(68,[2,3,47,383]),(10,[2,54011]),(131,[]),(141,[]),
    (231,[]),(131,[]),(181,[]),(157,[]),(131,[]),
    (145,[]),(5,[2,191,283]),(131,[]),(12,[2,3,3,6007]),(135,[]),
    (131,[]),(139,[]),(147,[]),(131,[]),(19,[2,3,13,19,73]),
    (5,[2,54101]),(131,[]),(11,[2,3,17,1061]),(135,[]),(131,[]),
    (5,[2,3,18041]),(10,[2,7,11,19,37]),(131,[]),(135,[]),(10,[2,29,1867]),
    (131,[]),(145,[]),(277,[]),(131,[]),(5,[2,3,3,13,463]),
    (5,[2,7,71,109]),(131,[]),(135,[]),(139,[]),(131,[]),
    (171,[]),(141,[]),(131,[]),(139,[]),(145,[]),
    (131,[]),(10,[2,3,18077]),(207,[]),(131,[]),(285,[]),
    (29,[2,54251]),(131,[]),(175,[]),(169,[]),(131,[]),
    (147,[]),(135,[]),(131,[]),(151,[]),(5,[2,54293]),
    (131,[]),(195,[]),(147,[]),(131,[]),(19,[2,3,19,953]),
    (135,[]),(131,[]),(141,[]),(379,[]),(131,[]),
    (135,[]),(5,[2,13,37,113]),(131,[]),(5,[2,3,18121]),(165,[]),
    (131,[]),(189,[]),(151,[]),(131,[]),(135,[]),
    (5,[2,54401]),(131,[]),(139,[]),(5,[2,54413]),(131,[]),
    (217,[]),(29,[2,13,53,79]),(131,[]),(2,[2,3,3,23,263]),(10,[2,54443]),
    (131,[]),(12,[2,3,7,2593]),(5,[2,11,4951]),(131,[]),(19,[2,3,67,271]),
    (5,[2,19,47,61]),(131,[]),(5,[2,3,11,13,127]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock109 : ∃ data, checkBlock 109 data = true :=
  ⟨[(147,[]),(189,[]),(131,[]),(159,[]),(139,[]),
    (131,[]),(12,[2,3,3,73,83]),(135,[]),(131,[]),(139,[]),
    (13,[2,7,7793]),(131,[]),(135,[]),(157,[]),(131,[]),
    (17,[2,3,18191]),(301,[]),(131,[]),(169,[]),(141,[]),
    (131,[]),(135,[]),(367,[]),(131,[]),(157,[]),
    (235,[]),(131,[]),(2,[2,3,18211]),(231,[]),(131,[]),
    (5,[2,3,18217]),(139,[]),(131,[]),(145,[]),(141,[]),
    (131,[]),(42,[2,3,11,1657]),(10,[2,149,367]),(131,[]),(2,[2,3,3,59,103]),
    (135,[]),(131,[]),(5,[2,3,3,6079]),(201,[]),(131,[]),
    (141,[]),(145,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(2,[2,3,18251]),(159,[]),(131,[]),(135,[]),
    (5,[2,54773]),(131,[]),(5,[2,3,3,3,2029]),(10,[2,11,17,293]),(131,[]),
    (141,[]),(171,[]),(131,[]),(135,[]),(211,[]),
    (131,[]),(43,[2,3,7,7,373]),(145,[]),(131,[]),(147,[]),
    (139,[]),(131,[]),(241,[]),(307,[]),(131,[]),
    (139,[]),(147,[]),(131,[]),(439,[]),(229,[]),
    (131,[]),(5,[2,3,18301]),(135,[]),(131,[]),(17,[2,3,18307]),
    (10,[2,11,4993]),(131,[]),(309,[]),(5,[2,54941]),(131,[]),
    (5,[2,3,13,1409]),(135,[]),(131,[]),(165,[]),(10,[2,7,7853]),
    (131,[]),(135,[]),(139,[]),(131,[]),(11,[2,3,23,797])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock110 : ∃ data, checkBlock 110 data = true :=
  ⟨[(169,[]),(131,[]),(10,[2,3,11,1667]),(175,[]),(131,[]),
    (135,[]),(13,[2,113,487]),(131,[]),(2,[2,3,7,2621]),(411,[]),
    (131,[]),(231,[]),(141,[]),(131,[]),(139,[]),
    (151,[]),(131,[]),(169,[]),(29,[2,89,619]),(131,[]),
    (321,[]),(319,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(199,[]),(159,[]),(131,[]),(157,[]),
    (201,[]),(131,[]),(11,[2,3,3,3,3,3,227]),(135,[]),(131,[]),
    (145,[]),(139,[]),(131,[]),(135,[]),(295,[]),
    (131,[]),(139,[]),(151,[]),(131,[]),(307,[]),
    (147,[]),(131,[]),(135,[]),(145,[]),(131,[]),
    (33,[2,3,3,7,877]),(187,[]),(131,[]),(33,[2,3,13,13,109]),(10,[2,19,2909]),
    (131,[]),(2,[2,3,18427]),(13,[2,59,937]),(131,[]),(2,[2,3,7,2633]),
    (5,[2,17,3253]),(131,[]),(5,[2,3,103,179]),(139,[]),(131,[]),
    (10,[2,3,3,3,3,683]),(135,[]),(131,[]),(279,[]),(145,[]),
    (131,[]),(277,[]),(391,[]),(131,[]),(187,[]),
    (135,[]),(131,[]),(385,[]),(267,[]),(131,[]),
    (135,[]),(10,[2,17,3259]),(131,[]),(147,[]),(327,[]),
    (131,[]),(5,[2,3,3,3,2053]),(157,[]),(131,[]),(135,[]),
    (141,[]),(131,[]),(33,[2,3,7,19,139]),(10,[2,37,1499]),(131,[]),
    (18,[2,3,11,41,41]),(165,[]),(131,[]),(157,[]),(169,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock111 : ∃ data, checkBlock 111 data = true :=
  ⟨[(131,[]),(141,[]),(139,[]),(131,[]),(2,[2,3,3,31,199]),
    (421,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (10,[2,3,18517]),(265,[]),(131,[]),(6,[2,3,18521]),(20,[2,61,911]),
    (131,[]),(141,[]),(135,[]),(131,[]),(12,[2,3,3,3,29,71]),
    (189,[]),(131,[]),(135,[]),(5,[2,19,2927]),(131,[]),
    (181,[]),(10,[2,55631]),(131,[]),(147,[]),(139,[]),
    (131,[]),(135,[]),(5,[2,55661]),(131,[]),(151,[]),
    (5,[2,55673]),(131,[]),(145,[]),(159,[]),(131,[]),
    (229,[]),(165,[]),(131,[]),(18,[2,3,7,7,379]),(5,[2,55721]),
    (131,[]),(139,[]),(5,[2,55733]),(131,[]),(5,[2,3,17,1093]),
    (135,[]),(131,[]),(357,[]),(141,[]),(131,[]),
    (459,[]),(157,[]),(131,[]),(369,[]),(135,[]),
    (131,[]),(361,[]),(13,[2,7,7,17,67]),(131,[]),(135,[]),
    (225,[]),(131,[]),(2,[2,3,37,503]),(139,[]),(131,[]),
    (165,[]),(145,[]),(131,[]),(135,[]),(259,[]),
    (131,[]),(201,[]),(19,[2,29,41,47]),(131,[]),(141,[]),
    (151,[]),(131,[]),(195,[]),(23,[2,11,13,17,23]),(131,[]),
    (55,[2,3,7,2663]),(10,[2,55931]),(131,[]),(181,[]),(255,[]),
    (131,[]),(175,[]),(135,[]),(131,[]),(141,[]),
    (139,[]),(131,[]),(147,[]),(241,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock112 : ∃ data, checkBlock 112 data = true :=
  ⟨[(159,[]),(135,[]),(131,[]),(157,[]),(147,[]),
    (131,[]),(135,[]),(5,[2,137,409]),(131,[]),(5,[2,3,3,13,479]),
    (29,[2,23,2437]),(131,[]),(139,[]),(159,[]),(131,[]),
    (135,[]),(5,[2,56081]),(131,[]),(145,[]),(171,[]),
    (131,[]),(5,[2,3,18701]),(10,[2,11,5101]),(131,[]),(235,[]),
    (10,[2,56123]),(131,[]),(259,[]),(175,[]),(131,[]),
    (10,[2,3,3,17,367]),(141,[]),(131,[]),(5,[2,3,97,193]),(135,[]),
    (131,[]),(2,[2,3,61,307]),(441,[]),(131,[]),(139,[]),
    (20,[2,43,1307]),(131,[]),(147,[]),(135,[]),(131,[]),
    (151,[]),(141,[]),(131,[]),(135,[]),(325,[]),
    (131,[]),(2,[2,3,17,1103]),(145,[]),(131,[]),(6,[2,3,18757]),
    (369,[]),(131,[]),(135,[]),(10,[2,181,311]),(131,[]),
    (2,[2,3,7,7,383]),(139,[]),(131,[]),(169,[]),(5,[2,17,3313]),
    (131,[]),(10,[2,3,3,11,569]),(189,[]),(131,[]),(10,[2,3,7,2683]),
    (171,[]),(131,[]),(141,[]),(145,[]),(131,[]),
    (159,[]),(135,[]),(131,[]),(139,[]),(5,[2,56393]),
    (131,[]),(28,[2,3,3,3,2089]),(385,[]),(131,[]),(11,[2,3,3,6269]),
    (135,[]),(131,[]),(187,[]),(285,[]),(131,[]),
    (135,[]),(151,[]),(131,[]),(39,[2,3,11,29,59]),(181,[]),
    (131,[]),(211,[]),(20,[2,7,8069]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock113 : ∃ data, checkBlock 113 data = true :=
  ⟨[(139,[]),(131,[]),(5,[2,3,3,3,7,13,23]),(5,[2,31,1823]),(131,[]),
    (139,[]),(10,[2,56531]),(131,[]),(20,[2,3,47,401]),(141,[]),
    (131,[]),(147,[]),(5,[2,163,347]),(131,[]),(19,[2,3,109,173]),
    (5,[2,11,37,139]),(131,[]),(5,[2,3,3,6287]),(135,[]),(131,[]),
    (145,[]),(207,[]),(131,[]),(18,[2,3,113,167]),(141,[]),
    (131,[]),(319,[]),(135,[]),(131,[]),(10,[2,3,79,239]),
    (157,[]),(131,[]),(135,[]),(10,[2,56663]),(131,[]),
    (141,[]),(5,[2,56681]),(131,[]),(6,[2,3,3,6299]),(199,[]),
    (131,[]),(135,[]),(229,[]),(131,[]),(139,[]),
    (169,[]),(131,[]),(30,[2,3,18911]),(411,[]),(131,[]),
    (141,[]),(351,[]),(131,[]),(235,[]),(145,[]),
    (131,[]),(147,[]),(10,[2,56783]),(131,[]),(225,[]),
    (135,[]),(131,[]),(10,[2,3,29,653]),(165,[]),(131,[]),
    (5,[2,3,13,31,47]),(139,[]),(131,[]),(2,[2,3,18947]),(135,[]),
    (131,[]),(139,[]),(5,[2,7,8123]),(131,[]),(135,[]),
    (145,[]),(131,[]),(157,[]),(19,[2,56891]),(131,[]),
    (445,[]),(201,[]),(131,[]),(135,[]),(5,[2,56921]),
    (131,[]),(159,[]),(141,[]),(131,[]),(189,[]),
    (10,[2,56951]),(131,[]),(165,[]),(139,[]),(131,[]),
    (2,[2,3,7,2713]),(5,[2,19,2999]),(131,[]),(5,[2,3,11,11,157]),(159,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock114 : ∃ data, checkBlock 114 data = true :=
  ⟨[(131,[]),(301,[]),(135,[]),(131,[]),(12,[2,3,83,229]),
    (187,[]),(131,[]),(2,[2,3,3,6337]),(5,[2,57041]),(131,[]),
    (139,[]),(135,[]),(131,[]),(141,[]),(14,[2,7,31,263]),
    (131,[]),(135,[]),(10,[2,13,4391]),(131,[]),(217,[]),
    (5,[2,11,29,179]),(131,[]),(145,[]),(231,[]),(131,[]),
    (135,[]),(291,[]),(131,[]),(141,[]),(151,[]),
    (131,[]),(279,[]),(139,[]),(131,[]),(5,[2,3,17,19,59]),
    (157,[]),(131,[]),(139,[]),(235,[]),(131,[]),
    (361,[]),(29,[2,57203]),(131,[]),(145,[]),(135,[]),
    (131,[]),(157,[]),(5,[2,11,11,11,43]),(131,[]),(45,[2,3,19081]),
    (195,[]),(131,[]),(199,[]),(135,[]),(131,[]),
    (29,[2,3,17,1123]),(145,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(159,[]),(211,[]),(131,[]),(11,[2,3,3,3,11,193]),
    (141,[]),(131,[]),(135,[]),(201,[]),(131,[]),
    (147,[]),(379,[]),(131,[]),(175,[]),(29,[2,103,557]),
    (131,[]),(139,[]),(145,[]),(131,[]),(207,[]),
    (141,[]),(131,[]),(327,[]),(5,[2,57413]),(131,[]),
    (12,[2,3,19141]),(135,[]),(131,[]),(2,[2,3,41,467]),(259,[]),
    (131,[]),(141,[]),(169,[]),(131,[]),(265,[]),
    (135,[]),(131,[]),(23,[2,3,3,3,2129]),(139,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock115 : ∃ data, checkBlock 115 data = true :=
  ⟨[(135,[]),(147,[]),(131,[]),(139,[]),(157,[]),
    (131,[]),(141,[]),(5,[2,7,8219]),(131,[]),(135,[]),
    (159,[]),(131,[]),(12,[2,3,7,2741]),(10,[2,11,5233]),(131,[]),
    (241,[]),(5,[2,71,811]),(131,[]),(5,[2,3,3,3,3,3,3,79]),(357,[]),
    (131,[]),(151,[]),(10,[2,53,1087]),(131,[]),(145,[]),
    (139,[]),(131,[]),(201,[]),(135,[]),(131,[]),
    (5,[2,3,11,1747]),(195,[]),(131,[]),(5,[2,3,3,43,149]),(13,[2,101,571]),
    (131,[]),(57,[2,3,3,13,17,29]),(135,[]),(131,[]),(147,[]),
    (165,[]),(131,[]),(135,[]),(141,[]),(131,[]),
    (145,[]),(147,[]),(131,[]),(151,[]),(181,[]),
    (131,[]),(135,[]),(7,[2,11,59,89]),(131,[]),(355,[]),
    (5,[2,57773]),(131,[]),(291,[]),(141,[]),(131,[]),
    (2,[2,3,19267]),(321,[]),(131,[]),(171,[]),(139,[]),
    (131,[]),(6,[2,3,37,521]),(151,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(159,[]),(19,[2,13,4451]),(131,[]),
    (411,[]),(5,[2,57881]),(131,[]),(116,[2,3,23,839]),(135,[]),
    (131,[]),(5,[2,3,19301]),(10,[2,7,8273]),(131,[]),(135,[]),
    (159,[]),(131,[]),(237,[]),(5,[2,13,4457]),(131,[]),
    (5,[2,3,3,47,137]),(139,[]),(131,[]),(135,[]),(151,[]),
    (131,[]),(11,[2,3,7,11,251]),(217,[]),(131,[]),(31,[2,3,13,1487])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock116 : ∃ data, checkBlock 116 data = true :=
  ⟨[(439,[]),(131,[]),(285,[]),(5,[2,58013]),(131,[]),
    (5,[2,3,3,3,7,307]),(405,[]),(131,[]),(139,[]),(157,[]),
    (131,[]),(2,[2,3,37,523]),(135,[]),(131,[]),(165,[]),
    (147,[]),(131,[]),(5,[2,3,19,1019]),(351,[]),(131,[]),
    (157,[]),(135,[]),(131,[]),(199,[]),(6,[2,7,19,19,23]),
    (131,[]),(135,[]),(361,[]),(131,[]),(231,[]),
    (139,[]),(131,[]),(217,[]),(189,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(309,[]),(5,[2,58193]),
    (131,[]),(187,[]),(29,[2,58211]),(131,[]),(2,[2,3,3,6469]),
    (10,[2,11,67,79]),(131,[]),(141,[]),(5,[2,139,419]),(131,[]),
    (241,[]),(5,[2,13,4481]),(131,[]),(147,[]),(135,[]),
    (131,[]),(169,[]),(139,[]),(131,[]),(151,[]),
    (145,[]),(131,[]),(141,[]),(135,[]),(131,[]),
    (195,[]),(14,[2,7,13,641]),(131,[]),(135,[]),(14,[2,41,1423]),
    (131,[]),(2,[2,3,53,367]),(279,[]),(131,[]),(139,[]),
    (31,[2,7,31,269]),(131,[]),(135,[]),(157,[]),(131,[]),
    (11,[2,3,3,3,3,7,103]),(145,[]),(131,[]),(2,[2,3,19471]),(459,[]),
    (131,[]),(151,[]),(5,[2,71,823]),(131,[]),(307,[]),
    (30,[2,58451]),(131,[]),(11,[2,3,13,1499]),(19,[2,17,19,181]),(131,[]),
    (211,[]),(135,[]),(131,[]),(147,[]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock117 : ∃ data, checkBlock 117 data = true :=
  ⟨[(131,[]),(139,[]),(10,[2,58511]),(131,[]),(2,[2,3,19507]),
    (135,[]),(131,[]),(295,[]),(319,[]),(131,[]),
    (135,[]),(309,[]),(131,[]),(19,[2,3,3,3,3,3,241]),(141,[]),
    (131,[]),(52,[2,3,3,23,283]),(13,[2,7,8369]),(131,[]),(135,[]),
    (5,[2,58601]),(131,[]),(6,[2,3,7,2791]),(139,[]),(131,[]),
    (141,[]),(277,[]),(131,[]),(145,[]),(147,[]),
    (131,[]),(44,[2,3,3,7,7,7,19]),(151,[]),(131,[]),(399,[]),
    (171,[]),(131,[]),(369,[]),(135,[]),(131,[]),
    (139,[]),(241,[]),(131,[]),(2,[2,3,19571]),(5,[2,13,4517]),
    (131,[]),(229,[]),(135,[]),(131,[]),(145,[]),
    (14,[2,7,7,11,109]),(131,[]),(135,[]),(339,[]),(131,[]),
    (169,[]),(5,[2,43,1367]),(131,[]),(159,[]),(187,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(11,[2,3,7,2801]),
    (199,[]),(131,[]),(139,[]),(265,[]),(131,[]),
    (5,[2,3,3,13,503]),(159,[]),(131,[]),(11,[2,3,7,2803]),(147,[]),
    (131,[]),(2,[2,3,19,1033]),(141,[]),(131,[]),(13,[2,3,67,293]),
    (135,[]),(131,[]),(187,[]),(145,[]),(131,[]),
    (319,[]),(171,[]),(131,[]),(2,[2,3,3,3,37,59]),(135,[]),
    (131,[]),(285,[]),(141,[]),(131,[]),(135,[]),
    (207,[]),(131,[]),(151,[]),(255,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock118 : ∃ data, checkBlock 118 data = true :=
  ⟨[(325,[]),(327,[]),(131,[]),(135,[]),(5,[2,59021]),
    (131,[]),(139,[]),(165,[]),(131,[]),(391,[]),
    (217,[]),(131,[]),(147,[]),(10,[2,59063]),(131,[]),
    (2,[2,3,7,29,97]),(5,[2,11,41,131]),(131,[]),(141,[]),(201,[]),
    (131,[]),(171,[]),(135,[]),(131,[]),(151,[]),
    (29,[2,59123]),(131,[]),(355,[]),(139,[]),(131,[]),
    (145,[]),(135,[]),(131,[]),(139,[]),(10,[2,7,79,107]),
    (131,[]),(135,[]),(169,[]),(131,[]),(2,[2,3,3,6577]),
    (295,[]),(131,[]),(5,[2,3,3,3,3,17,43]),(147,[]),(131,[]),
    (135,[]),(10,[2,61,971]),(131,[]),(237,[]),(175,[]),
    (131,[]),(145,[]),(157,[]),(131,[]),(20,[2,3,23,859]),
    (139,[]),(131,[]),(267,[]),(10,[2,211,281]),(131,[]),
    (2,[2,3,3,11,599]),(211,[]),(131,[]),(441,[]),(135,[]),
    (131,[]),(235,[]),(181,[]),(131,[]),(5,[2,3,131,151]),
    (141,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (2,[2,3,3,3,3,733]),(241,[]),(131,[]),(135,[]),(5,[2,59393]),
    (131,[]),(141,[]),(159,[]),(131,[]),(2,[2,3,29,683]),
    (145,[]),(131,[]),(135,[]),(147,[]),(131,[]),
    (5,[2,3,7,19,149]),(5,[2,59453]),(131,[]),(5,[2,3,3,6607]),(139,[]),
    (131,[]),(141,[]),(14,[2,17,3499]),(131,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock119 : ∃ data, checkBlock 119 data = true :=
  ⟨[(187,[]),(131,[]),(169,[]),(5,[2,59513]),(131,[]),
    (5,[2,3,19841]),(135,[]),(131,[]),(2,[2,3,89,223]),(10,[2,11,5413]),
    (131,[]),(17,[2,3,3,13,509]),(267,[]),(131,[]),(411,[]),
    (135,[]),(131,[]),(397,[]),(14,[2,7,8513]),(131,[]),
    (135,[]),(139,[]),(131,[]),(11,[2,3,31,641]),(5,[2,59621]),
    (131,[]),(147,[]),(6,[2,7,7,1217]),(131,[]),(135,[]),
    (181,[]),(131,[]),(145,[]),(141,[]),(131,[]),
    (151,[]),(5,[2,37,1613]),(131,[]),(139,[]),(405,[]),
    (131,[]),(225,[]),(435,[]),(131,[]),(159,[]),
    (10,[2,59723]),(131,[]),(321,[]),(135,[]),(131,[]),
    (5,[2,3,3,3,2213]),(255,[]),(131,[]),(145,[]),(301,[]),
    (131,[]),(2,[2,3,19927]),(135,[]),(131,[]),(141,[]),
    (139,[]),(131,[]),(135,[]),(7,[2,13,43,107]),(131,[]),
    (139,[]),(145,[]),(131,[]),(157,[]),(19,[2,7,83,103]),
    (131,[]),(135,[]),(5,[2,31,1931]),(131,[]),(141,[]),
    (5,[2,11,5443]),(131,[]),(357,[]),(10,[2,13,17,271]),(131,[]),
    (175,[]),(151,[]),(131,[]),(44,[2,3,3,3,7,317]),(165,[]),
    (131,[]),(195,[]),(139,[]),(131,[]),(229,[]),
    (135,[]),(131,[]),(71,[2,3,11,23,79]),(171,[]),(131,[]),
    (147,[]),(5,[2,59981]),(131,[]),(12,[2,3,19997]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock120 : ∃ data, checkBlock 120 data = true :=
  ⟨[(131,[]),(169,[]),(147,[]),(131,[]),(135,[]),
    (10,[2,193,311]),(131,[]),(21,[2,3,20011]),(151,[]),(131,[]),
    (5,[2,3,37,541]),(141,[]),(131,[]),(135,[]),(445,[]),
    (131,[]),(30,[2,3,7,2861]),(10,[2,60083]),(131,[]),(159,[]),
    (199,[]),(131,[]),(22,[2,3,3,6679]),(237,[]),(131,[]),
    (23,[2,3,7,7,409]),(139,[]),(131,[]),(11,[2,3,20047]),(165,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(145,[]),
    (279,[]),(131,[]),(141,[]),(14,[2,23,2617]),(131,[]),
    (147,[]),(135,[]),(131,[]),(2,[2,3,20071]),(171,[]),
    (131,[]),(135,[]),(307,[]),(131,[]),(199,[]),
    (10,[2,60251]),(131,[]),(141,[]),(139,[]),(131,[]),
    (135,[]),(5,[2,13,4637]),(131,[]),(165,[]),(5,[2,60293]),
    (131,[]),(13,[2,3,20101]),(19,[2,41,1471]),(131,[]),(351,[]),
    (13,[2,179,337]),(131,[]),(195,[]),(145,[]),(131,[]),
    (139,[]),(147,[]),(131,[]),(151,[]),(135,[]),
    (131,[]),(2,[2,3,3,6709]),(10,[2,60383]),(131,[]),(171,[]),
    (235,[]),(131,[]),(42,[2,3,13,1549]),(135,[]),(131,[]),
    (44,[2,3,11,1831]),(13,[2,7,89,97]),(131,[]),(135,[]),(141,[]),
    (131,[]),(2,[2,3,3,3,2239]),(139,[]),(131,[]),(5,[2,3,3,6719]),
    (5,[2,7,53,163]),(131,[]),(135,[]),(465,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock121 : ∃ data, checkBlock 121 data = true :=
  ⟨[(151,[]),(29,[2,17,3559]),(131,[]),(165,[]),(141,[]),
    (131,[]),(12,[2,3,20177]),(6,[2,11,5503]),(131,[]),(147,[]),
    (475,[]),(131,[]),(2,[2,3,3,3,2243]),(187,[]),(131,[]),
    (141,[]),(135,[]),(131,[]),(307,[]),(139,[]),
    (131,[]),(189,[]),(369,[]),(131,[]),(391,[]),
    (135,[]),(131,[]),(11,[2,3,3,6737]),(5,[2,7,8663]),(131,[]),
    (135,[]),(157,[]),(131,[]),(12,[2,3,73,277]),(19,[2,13,13,359]),
    (131,[]),(139,[]),(10,[2,7,8669]),(131,[]),(135,[]),
    (5,[2,101,601]),(131,[]),(157,[]),(159,[]),(131,[]),
    (5,[2,3,3,3,13,173]),(151,[]),(131,[]),(169,[]),(10,[2,19,23,139]),
    (131,[]),(2,[2,3,7,11,263]),(5,[2,60761]),(131,[]),(147,[]),
    (5,[2,60773]),(131,[]),(145,[]),(135,[]),(131,[]),
    (405,[]),(19,[2,41,1483]),(131,[]),(139,[]),(231,[]),
    (131,[]),(217,[]),(135,[]),(131,[]),(19,[2,3,17,1193]),
    (145,[]),(131,[]),(135,[]),(13,[2,11,11,503]),(131,[]),
    (339,[]),(5,[2,23,2647]),(131,[]),(321,[]),(5,[2,7,8699]),
    (131,[]),(135,[]),(141,[]),(131,[]),(2,[2,3,3,7,967]),
    (139,[]),(131,[]),(11,[2,3,19,1069]),(5,[2,149,409]),(131,[]),
    (267,[]),(145,[]),(131,[]),(141,[]),(325,[]),
    (131,[]),(17,[2,3,20327]),(19,[2,13,4691]),(131,[]),(327,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock122 : ∃ data, checkBlock 122 data = true :=
  ⟨[(135,[]),(131,[]),(139,[]),(5,[2,17,37,97]),(131,[]),
    (159,[]),(165,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(151,[]),(225,[]),(131,[]),(135,[]),
    (5,[2,157,389]),(131,[]),(19,[2,3,3,11,617]),(189,[]),(131,[]),
    (2,[2,3,3,3,31,73]),(13,[2,7,7,29,43]),(131,[]),(135,[]),(139,[]),
    (131,[]),(23,[2,3,7,41,71]),(5,[2,113,541]),(131,[]),(139,[]),
    (147,[]),(131,[]),(11,[2,3,19,29,37]),(14,[2,31,1973]),(131,[]),
    (11,[2,3,3,7,971]),(5,[2,193,317]),(131,[]),(145,[]),(5,[2,11,5563]),
    (131,[]),(237,[]),(135,[]),(131,[]),(2,[2,3,20407]),
    (141,[]),(131,[]),(157,[]),(181,[]),(131,[]),
    (5,[2,3,17,1201]),(135,[]),(131,[]),(11,[2,3,3,3,2269]),(159,[]),
    (131,[]),(135,[]),(151,[]),(131,[]),(145,[]),
    (141,[]),(131,[]),(175,[]),(277,[]),(131,[]),
    (135,[]),(13,[2,61331]),(131,[]),(139,[]),(207,[]),
    (131,[]),(141,[]),(145,[]),(131,[]),(43,[2,3,3,3,2273]),
    (259,[]),(131,[]),(421,[]),(327,[]),(131,[]),
    (165,[]),(355,[]),(131,[]),(19,[2,3,11,1861]),(135,[]),
    (131,[]),(141,[]),(5,[2,23,2671]),(131,[]),(6,[2,3,3,6827]),
    (139,[]),(131,[]),(211,[]),(135,[]),(131,[]),
    (139,[]),(5,[2,7,8783]),(131,[]),(135,[]),(147,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock123 : ∃ data, checkBlock 123 data = true :=
  ⟨[(131,[]),(39,[2,3,13,19,83]),(171,[]),(131,[]),(199,[]),
    (157,[]),(131,[]),(135,[]),(5,[2,19,41,79]),(131,[]),
    (385,[]),(435,[]),(131,[]),(38,[2,3,20521]),(19,[2,23,2677]),
    (131,[]),(157,[]),(139,[]),(131,[]),(175,[]),
    (5,[2,229,269]),(131,[]),(277,[]),(141,[]),(131,[]),
    (165,[]),(135,[]),(131,[]),(241,[]),(159,[]),
    (131,[]),(2,[2,3,20551]),(5,[2,197,313]),(131,[]),(139,[]),
    (135,[]),(131,[]),(147,[]),(141,[]),(131,[]),
    (135,[]),(10,[2,61703]),(131,[]),(2,[2,3,3,6857]),(147,[]),
    (131,[]),(459,[]),(439,[]),(131,[]),(135,[]),
    (14,[2,61751]),(131,[]),(229,[]),(34,[2,13,4751]),(131,[]),
    (19,[2,3,59,349]),(139,[]),(131,[]),(5,[2,3,43,479]),(211,[]),
    (131,[]),(139,[]),(309,[]),(131,[]),(141,[]),
    (189,[]),(131,[]),(2,[2,3,20611]),(135,[]),(131,[]),
    (231,[]),(5,[2,11,5623]),(131,[]),(12,[2,3,17,1213]),(145,[]),
    (131,[]),(151,[]),(135,[]),(131,[]),(11,[2,3,3,13,23,23]),
    (43,[2,7,37,239]),(131,[]),(135,[]),(139,[]),(131,[]),
    (399,[]),(10,[2,17,3643]),(131,[]),(171,[]),(10,[2,7,8849]),
    (131,[]),(135,[]),(5,[2,61961]),(131,[]),(169,[]),
    (145,[]),(131,[]),(181,[]),(29,[2,61991]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock124 : ∃ data, checkBlock 124 data = true :=
  ⟨[(139,[]),(141,[]),(131,[]),(201,[]),(291,[]),
    (131,[]),(225,[]),(13,[2,17,41,89]),(131,[]),(12,[2,3,20681]),
    (135,[]),(131,[]),(17,[2,3,137,151]),(147,[]),(131,[]),
    (42,[2,3,3,3,11,11,19]),(141,[]),(131,[]),(5,[2,3,3,6899]),(135,[]),
    (131,[]),(157,[]),(139,[]),(131,[]),(135,[]),
    (13,[2,23,37,73]),(131,[]),(139,[]),(165,[]),(131,[]),
    (10,[2,3,20717]),(325,[]),(131,[]),(135,[]),(13,[2,62171]),
    (131,[]),(92,[2,3,3,3,7,7,47]),(10,[2,11,5653]),(131,[]),(301,[]),
    (159,[]),(131,[]),(141,[]),(5,[2,62213]),(131,[]),
    (10,[2,3,7,2963]),(199,[]),(131,[]),(409,[]),(139,[]),
    (131,[]),(147,[]),(135,[]),(131,[]),(5,[2,3,3,11,17,37]),
    (397,[]),(131,[]),(5,[2,3,13,1597]),(147,[]),(131,[]),
    (181,[]),(135,[]),(131,[]),(145,[]),(5,[2,7,29,307]),
    (131,[]),(135,[]),(187,[]),(131,[]),(195,[]),
    (19,[2,62351]),(131,[]),(319,[]),(165,[]),(131,[]),
    (135,[]),(145,[]),(131,[]),(6,[2,3,7,2971]),(141,[]),
    (131,[]),(265,[]),(40,[2,139,449]),(131,[]),(259,[]),
    (13,[2,62423]),(131,[]),(151,[]),(139,[]),(131,[]),
    (157,[]),(5,[2,19,19,173]),(131,[]),(139,[]),(135,[]),
    (131,[]),(147,[]),(145,[]),(131,[]),(11,[2,3,37,563])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock125 : ∃ data, checkBlock 125 data = true :=
  ⟨[(5,[2,62501]),(131,[]),(159,[]),(135,[]),(131,[]),
    (141,[]),(10,[2,7,8933]),(131,[]),(135,[]),(171,[]),
    (131,[]),(11,[2,3,29,719]),(339,[]),(131,[]),(151,[]),
    (139,[]),(131,[]),(135,[]),(10,[2,62591]),(131,[]),
    (141,[]),(10,[2,62603]),(131,[]),(225,[]),(5,[2,13,4817]),
    (131,[]),(357,[]),(147,[]),(131,[]),(12,[2,3,7,19,157]),
    (19,[2,31,43,47]),(131,[]),(139,[]),(151,[]),(131,[]),
    (291,[]),(135,[]),(131,[]),(11,[2,3,20897]),(5,[2,71,883]),
    (131,[]),(28,[2,3,3,6967]),(10,[2,11,5701]),(131,[]),(145,[]),
    (135,[]),(131,[]),(165,[]),(157,[]),(131,[]),
    (135,[]),(5,[2,62753]),(131,[]),(5,[2,3,20921]),(139,[]),
    (131,[]),(435,[]),(141,[]),(131,[]),(135,[]),
    (151,[]),(131,[]),(397,[]),(5,[2,23,2731]),(131,[]),
    (145,[]),(181,[]),(131,[]),(18,[2,3,20947]),(10,[2,11,29,197]),
    (131,[]),(29,[2,3,7,41,73]),(141,[]),(131,[]),(12,[2,3,19,1103]),
    (169,[]),(131,[]),(159,[]),(135,[]),(131,[]),
    (12,[2,3,3,29,241]),(139,[]),(131,[]),(141,[]),(189,[]),
    (131,[]),(10,[2,3,11,1907]),(135,[]),(131,[]),(5,[2,3,20981]),
    (265,[]),(131,[]),(135,[]),(14,[2,79,797]),(131,[]),
    (157,[]),(5,[2,62981]),(131,[]),(139,[]),(145,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock126 : ∃ data, checkBlock 126 data = true :=
  ⟨[(131,[]),(135,[]),(20,[2,13,37,131]),(131,[]),(369,[]),
    (19,[2,19,31,107]),(131,[]),(17,[2,3,21011]),(187,[]),(131,[]),
    (147,[]),(5,[2,17,3709]),(131,[]),(19,[2,3,3,7,7,11,13]),(30,[2,59,1069]),
    (131,[]),(207,[]),(199,[]),(131,[]),(385,[]),
    (135,[]),(131,[]),(10,[2,3,109,193]),(5,[2,63113]),(131,[]),
    (139,[]),(159,[]),(131,[]),(421,[]),(135,[]),
    (131,[]),(2,[2,3,3,3,2339]),(7,[2,7,7,1289]),(131,[]),(135,[]),
    (141,[]),(131,[]),(235,[]),(175,[]),(131,[]),
    (169,[]),(147,[]),(131,[]),(135,[]),(5,[2,191,331]),
    (131,[]),(145,[]),(139,[]),(131,[]),(28,[2,3,3,7027]),
    (141,[]),(131,[]),(151,[]),(157,[]),(131,[]),
    (2,[2,3,7,23,131]),(195,[]),(131,[]),(5,[2,3,17,17,73]),(231,[]),
    (131,[]),(141,[]),(135,[]),(131,[]),(139,[]),
    (217,[]),(131,[]),(145,[]),(5,[2,97,653]),(131,[]),
    (11,[2,3,3,7039]),(135,[]),(131,[]),(481,[]),(20,[2,7,11,823]),
    (131,[]),(135,[]),(237,[]),(131,[]),(147,[]),
    (145,[]),(131,[]),(5,[2,3,23,919]),(5,[2,7,9059]),(131,[]),
    (135,[]),(139,[]),(131,[]),(159,[]),(351,[]),
    (131,[]),(139,[]),(5,[2,17,3733]),(131,[]),(10,[2,3,21157]),
    (165,[]),(131,[]),(5,[2,3,7,3023]),(151,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock127 : ∃ data, checkBlock 127 data = true :=
  ⟨[(217,[]),(145,[]),(131,[]),(187,[]),(135,[]),
    (131,[]),(189,[]),(411,[]),(131,[]),(295,[]),
    (10,[2,103,617]),(131,[]),(2,[2,3,21187]),(135,[]),(131,[]),
    (181,[]),(7,[2,7,31,293]),(131,[]),(135,[]),(321,[]),
    (131,[]),(5,[2,3,3,37,191]),(157,[]),(131,[]),(147,[]),
    (14,[2,7,61,149]),(131,[]),(135,[]),(141,[]),(131,[]),
    (139,[]),(189,[]),(131,[]),(285,[]),(19,[2,63671]),
    (131,[]),(11,[2,3,21227]),(195,[]),(131,[]),(141,[]),
    (5,[2,11,5791]),(131,[]),(28,[2,3,3,7079]),(207,[]),(131,[]),
    (22,[2,3,11,1931]),(135,[]),(131,[]),(145,[]),(19,[2,63743]),
    (131,[]),(22,[2,3,79,269]),(139,[]),(131,[]),(141,[]),
    (135,[]),(131,[]),(139,[]),(10,[2,7,13,701]),(131,[]),
    (135,[]),(14,[2,63803]),(131,[]),(151,[]),(5,[2,19,3359]),
    (131,[]),(23,[2,3,21277]),(171,[]),(131,[]),(135,[]),
    (10,[2,67,953]),(131,[]),(465,[]),(19,[2,63863]),(131,[]),
    (2,[2,3,3,47,151]),(5,[2,127,503]),(131,[]),(181,[]),(139,[]),
    (131,[]),(43,[2,3,7,17,179]),(145,[]),(131,[]),(11,[2,3,11,13,149]),
    (301,[]),(131,[]),(17,[2,3,101,211]),(135,[]),(131,[]),
    (151,[]),(141,[]),(131,[]),(147,[]),(225,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(259,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock128 : ∃ data, checkBlock 128 data = true :=
  ⟨[(147,[]),(131,[]),(135,[]),(145,[]),(131,[]),
    (5,[2,3,21341]),(141,[]),(131,[]),(477,[]),(151,[]),
    (131,[]),(135,[]),(159,[]),(131,[]),(255,[]),
    (5,[2,17,3769]),(131,[]),(141,[]),(139,[]),(131,[]),
    (11,[2,3,23,929]),(169,[]),(131,[]),(139,[]),(385,[]),
    (131,[]),(175,[]),(157,[]),(131,[]),(5,[2,3,3,7127]),
    (135,[]),(131,[]),(141,[]),(10,[2,11,19,307]),(131,[]),
    (17,[2,3,21391]),(151,[]),(131,[]),(147,[]),(135,[]),
    (131,[]),(201,[]),(295,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(29,[2,3,3,3,3,13,61]),(5,[2,227,283]),(131,[]),
    (145,[]),(235,[]),(131,[]),(135,[]),(319,[]),
    (131,[]),(19,[2,3,7,3061]),(211,[]),(131,[]),(277,[]),
    (5,[2,64301]),(131,[]),(139,[]),(421,[]),(131,[]),
    (231,[]),(29,[2,23,2797]),(131,[]),(44,[2,3,3,3,2383]),(141,[]),
    (131,[]),(145,[]),(135,[]),(131,[]),(159,[]),
    (5,[2,64373]),(131,[]),(12,[2,3,11,1951]),(217,[]),(131,[]),
    (279,[]),(135,[]),(131,[]),(175,[]),(139,[]),
    (131,[]),(135,[]),(159,[]),(131,[]),(139,[]),
    (10,[2,64451]),(131,[]),(28,[2,3,21487]),(357,[]),(131,[]),
    (135,[]),(157,[]),(131,[]),(5,[2,3,7,37,83]),(5,[2,11,11,13,41])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock129 : ∃ data, checkBlock 129 data = true :=
  ⟨[(131,[]),(151,[]),(22,[2,31,2081]),(131,[]),(171,[]),
    (145,[]),(131,[]),(147,[]),(5,[2,233,277]),(131,[]),
    (141,[]),(139,[]),(131,[]),(5,[2,3,21521]),(135,[]),
    (131,[]),(355,[]),(165,[]),(131,[]),(11,[2,3,3,7177]),
    (175,[]),(131,[]),(19,[2,3,3,3,2393]),(135,[]),(131,[]),
    (435,[]),(20,[2,7,7,1319]),(131,[]),(135,[]),(10,[2,127,509]),
    (131,[]),(319,[]),(207,[]),(131,[]),(339,[]),
    (5,[2,7,9239]),(131,[]),(135,[]),(237,[]),(131,[]),
    (32,[2,3,3,7,13,79]),(279,[]),(131,[]),(157,[]),(5,[2,61,1061]),
    (131,[]),(165,[]),(141,[]),(131,[]),(159,[]),
    (139,[]),(131,[]),(145,[]),(19,[2,64763]),(131,[]),
    (139,[]),(135,[]),(131,[]),(229,[]),(5,[2,64793]),
    (131,[]),(5,[2,3,21601]),(141,[]),(131,[]),(2,[2,3,17,31,41]),
    (135,[]),(131,[]),(255,[]),(169,[]),(131,[]),
    (135,[]),(5,[2,64853]),(131,[]),(141,[]),(151,[]),
    (131,[]),(28,[2,3,3,3,3,3,3,89]),(139,[]),(131,[]),(135,[]),
    (5,[2,64901]),(131,[]),(325,[]),(147,[]),(131,[]),
    (169,[]),(145,[]),(131,[]),(141,[]),(14,[2,101,643]),
    (131,[]),(165,[]),(301,[]),(131,[]),(139,[]),
    (327,[]),(131,[]),(12,[2,3,21661]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock130 : ∃ data, checkBlock 130 data = true :=
  ⟨[(20,[2,3,47,461]),(157,[]),(131,[]),(2,[2,3,13,1667]),(5,[2,11,23,257]),
    (131,[]),(241,[]),(135,[]),(131,[]),(11,[2,3,3,3,3,11,73]),
    (409,[]),(131,[]),(135,[]),(14,[2,65063]),(131,[]),
    (21,[2,3,109,199]),(139,[]),(131,[]),(10,[2,3,13,1669]),(339,[]),
    (131,[]),(135,[]),(10,[2,65111]),(131,[]),(267,[]),
    (141,[]),(131,[]),(30,[2,3,3,7237]),(147,[]),(131,[]),
    (23,[2,3,3,3,19,127]),(5,[2,11,5923]),(131,[]),(181,[]),(10,[2,65171]),
    (131,[]),(18,[2,3,21727]),(29,[2,65183]),(131,[]),(151,[]),
    (135,[]),(131,[]),(12,[2,3,21737]),(139,[]),(131,[]),
    (5,[2,3,3,7247]),(411,[]),(131,[]),(13,[2,3,3,11,659]),(135,[]),
    (131,[]),(141,[]),(5,[2,7,9323]),(131,[]),(135,[]),
    (5,[2,13,5021]),(131,[]),(187,[]),(195,[]),(131,[]),
    (139,[]),(259,[]),(131,[]),(135,[]),(5,[2,83,787]),
    (131,[]),(141,[]),(169,[]),(131,[]),(5,[2,3,23,947]),
    (157,[]),(131,[]),(189,[]),(159,[]),(131,[]),
    (145,[]),(171,[]),(131,[]),(19,[2,3,71,307]),(5,[2,65393]),
    (131,[]),(5,[2,3,3,13,13,43]),(135,[]),(131,[]),(2,[2,3,3,3,2423]),
    (151,[]),(131,[]),(139,[]),(145,[]),(131,[]),
    (207,[]),(135,[]),(131,[]),(5,[2,3,21821]),(165,[]),
    (131,[]),(135,[]),(147,[]),(131,[]),(33,[2,3,3,19,383])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock131 : ∃ data, checkBlock 131 data = true :=
  ⟨[(397,[]),(131,[]),(6,[2,3,3,29,251]),(141,[]),(131,[]),
    (135,[]),(10,[2,19,3449]),(131,[]),(175,[]),(139,[]),
    (131,[]),(171,[]),(151,[]),(131,[]),(5,[2,3,11,1987]),
    (441,[]),(131,[]),(157,[]),(141,[]),(131,[]),
    (12,[2,3,3,37,197]),(307,[]),(131,[]),(409,[]),(135,[]),
    (131,[]),(139,[]),(5,[2,65633]),(131,[]),(141,[]),
    (14,[2,65651]),(131,[]),(169,[]),(135,[]),(131,[]),
    (147,[]),(5,[2,7,11,853]),(131,[]),(135,[]),(165,[]),
    (131,[]),(459,[]),(147,[]),(131,[]),(141,[]),
    (14,[2,7,41,229]),(131,[]),(135,[]),(139,[]),(131,[]),
    (235,[]),(5,[2,47,1399]),(131,[]),(139,[]),(10,[2,89,739]),
    (131,[]),(145,[]),(277,[]),(131,[]),(309,[]),
    (229,[]),(131,[]),(171,[]),(5,[2,11,31,193]),(131,[]),
    (175,[]),(135,[]),(131,[]),(165,[]),(19,[2,65843]),
    (131,[]),(28,[2,3,3,3,3,3,271]),(285,[]),(131,[]),(5,[2,3,3,13,563]),
    (135,[]),(131,[]),(145,[]),(10,[2,7,9413]),(131,[]),
    (135,[]),(141,[]),(131,[]),(369,[]),(159,[]),
    (131,[]),(157,[]),(291,[]),(131,[]),(135,[]),
    (145,[]),(131,[]),(139,[]),(10,[2,65963]),(131,[]),
    (2,[2,3,21991]),(141,[]),(131,[]),(187,[]),(217,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock132 : ∃ data, checkBlock 132 data = true :=
  ⟨[(131,[]),(229,[]),(175,[]),(131,[]),(151,[]),
    (10,[2,103,641]),(131,[]),(141,[]),(135,[]),(131,[]),
    (10,[2,3,3,41,179]),(145,[]),(131,[]),(165,[]),(139,[]),
    (131,[]),(277,[]),(135,[]),(131,[]),(139,[]),
    (201,[]),(131,[]),(135,[]),(151,[]),(131,[]),
    (11,[2,3,3,3,31,79]),(19,[2,13,5087]),(131,[]),(2,[2,3,3,7349]),(19,[2,7,11,859]),
    (131,[]),(135,[]),(241,[]),(131,[]),(217,[]),
    (5,[2,66173]),(131,[]),(5,[2,3,13,1697]),(10,[2,66191]),(131,[]),
    (12,[2,3,22067]),(139,[]),(131,[]),(279,[]),(157,[]),
    (131,[]),(159,[]),(267,[]),(131,[]),(147,[]),
    (135,[]),(131,[]),(21,[2,3,13,1699]),(29,[2,23,43,67]),(131,[]),
    (2,[2,3,22091]),(147,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(5,[2,3,3,53,139]),(14,[2,7,9473]),(131,[]),(135,[]),
    (10,[2,29,2287]),(131,[]),(13,[2,3,22111]),(405,[]),(131,[]),
    (259,[]),(6,[2,7,9479]),(131,[]),(135,[]),(141,[]),
    (131,[]),(57,[2,3,7,29,109]),(231,[]),(131,[]),(145,[]),
    (139,[]),(131,[]),(445,[]),(171,[]),(131,[]),
    (139,[]),(10,[2,66431]),(131,[]),(211,[]),(19,[2,13,19,269]),
    (131,[]),(157,[]),(135,[]),(131,[]),(147,[]),
    (5,[2,11,6043]),(131,[]),(23,[2,3,3,83,89]),(199,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock133 : ∃ data, checkBlock 133 data = true :=
  ⟨[(141,[]),(135,[]),(131,[]),(265,[]),(361,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(34,[2,3,41,541]),
    (10,[2,61,1091]),(131,[]),(367,[]),(145,[]),(131,[]),
    (135,[]),(165,[]),(131,[]),(5,[2,3,3,7,7,151]),(5,[2,66593]),
    (131,[]),(159,[]),(255,[]),(131,[]),(139,[]),
    (147,[]),(131,[]),(199,[]),(5,[2,103,647]),(131,[]),
    (6,[2,3,13,1709]),(237,[]),(131,[]),(5,[2,3,3,3,3,823]),(135,[]),
    (131,[]),(321,[]),(141,[]),(131,[]),(2,[2,3,11,43,47]),
    (5,[2,66701]),(131,[]),(151,[]),(135,[]),(131,[]),
    (33,[2,3,23,967]),(139,[]),(131,[]),(135,[]),(157,[]),
    (131,[]),(139,[]),(141,[]),(131,[]),(11,[2,3,3,3,2473]),
    (211,[]),(131,[]),(135,[]),(13,[2,66791]),(131,[]),
    (145,[]),(151,[]),(131,[]),(141,[]),(235,[]),
    (131,[]),(201,[]),(477,[]),(131,[]),(171,[]),
    (147,[]),(131,[]),(12,[2,3,3,17,19,23]),(139,[]),(131,[]),
    (207,[]),(135,[]),(131,[]),(141,[]),(481,[]),
    (131,[]),(145,[]),(291,[]),(131,[]),(2,[2,3,22307]),
    (135,[]),(131,[]),(391,[]),(151,[]),(131,[]),
    (135,[]),(487,[]),(131,[]),(327,[]),(145,[]),
    (131,[]),(2,[2,3,83,269]),(10,[2,7,7,1367]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock134 : ∃ data, checkBlock 134 data = true :=
  ⟨[(231,[]),(131,[]),(351,[]),(229,[]),(131,[]),
    (10,[2,3,3,11,677]),(207,[]),(131,[]),(147,[]),(13,[2,67043]),
    (131,[]),(187,[]),(139,[]),(131,[]),(181,[]),
    (141,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (171,[]),(30,[2,67103]),(131,[]),(18,[2,3,3,7457]),(5,[2,67121]),
    (131,[]),(5,[2,3,3,7459]),(135,[]),(131,[]),(5,[2,3,22381]),
    (141,[]),(131,[]),(135,[]),(13,[2,47,1429]),(131,[]),
    (165,[]),(5,[2,67181]),(131,[]),(189,[]),(139,[]),
    (131,[]),(135,[]),(357,[]),(131,[]),(57,[2,3,3,7,11,97]),
    (159,[]),(131,[]),(175,[]),(309,[]),(131,[]),
    (12,[2,3,29,773]),(5,[2,109,617]),(131,[]),(151,[]),(211,[]),
    (131,[]),(139,[]),(181,[]),(131,[]),(21,[2,3,3,7477]),
    (135,[]),(131,[]),(145,[]),(189,[]),(131,[]),
    (157,[]),(439,[]),(131,[]),(19,[2,3,22447]),(135,[]),
    (131,[]),(29,[2,3,11,13,157]),(327,[]),(131,[]),(135,[]),
    (255,[]),(131,[]),(147,[]),(139,[]),(131,[]),
    (151,[]),(14,[2,7,9629]),(131,[]),(135,[]),(147,[]),
    (131,[]),(285,[]),(5,[2,67433]),(131,[]),(5,[2,3,22481]),
    (441,[]),(131,[]),(18,[2,3,113,199]),(141,[]),(131,[]),
    (33,[2,3,3,3,3,7,7,17]),(145,[]),(131,[]),(475,[]),(151,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock135 : ∃ data, checkBlock 135 data = true :=
  ⟨[(131,[]),(10,[2,3,22501]),(135,[]),(131,[]),(17,[2,3,71,317]),
    (139,[]),(131,[]),(159,[]),(141,[]),(131,[]),
    (295,[]),(135,[]),(131,[]),(291,[]),(277,[]),
    (131,[]),(135,[]),(145,[]),(131,[]),(141,[]),
    (181,[]),(131,[]),(139,[]),(157,[]),(131,[]),
    (135,[]),(151,[]),(131,[]),(28,[2,3,7,3221]),(187,[]),
    (131,[]),(397,[]),(259,[]),(131,[]),(141,[]),
    (5,[2,31,37,59]),(131,[]),(6,[2,3,7,11,293]),(165,[]),(131,[]),
    (2,[2,3,22567]),(171,[]),(131,[]),(12,[2,3,22571]),(135,[]),
    (131,[]),(10,[2,3,107,211]),(5,[2,67733]),(131,[]),(139,[]),
    (307,[]),(131,[]),(187,[]),(135,[]),(131,[]),
    (217,[]),(159,[]),(131,[]),(135,[]),(169,[]),
    (131,[]),(20,[2,3,97,233]),(10,[2,19,43,83]),(131,[]),(145,[]),
    (13,[2,7,9689]),(131,[]),(135,[]),(369,[]),(131,[]),
    (225,[]),(139,[]),(131,[]),(5,[2,3,22621]),(10,[2,67,1013]),
    (131,[]),(255,[]),(265,[]),(131,[]),(2,[2,3,7,53,61]),
    (267,[]),(131,[]),(199,[]),(165,[]),(131,[]),
    (145,[]),(135,[]),(131,[]),(139,[]),(10,[2,67943]),
    (131,[]),(147,[]),(157,[]),(131,[]),(195,[]),
    (135,[]),(131,[]),(141,[]),(145,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock136 : ∃ data, checkBlock 136 data = true :=
  ⟨[(135,[]),(405,[]),(131,[]),(2,[2,3,3,3,11,229]),(5,[2,251,271]),
    (131,[]),(231,[]),(6,[2,7,9719]),(131,[]),(135,[]),
    (139,[]),(131,[]),(141,[]),(325,[]),(131,[]),
    (139,[]),(14,[2,13,5237]),(131,[]),(151,[]),(145,[]),
    (131,[]),(6,[2,3,3,7,23,47]),(29,[2,68111]),(131,[]),(169,[]),
    (10,[2,11,11,563]),(131,[]),(171,[]),(135,[]),(131,[]),
    (5,[2,3,22717]),(159,[]),(131,[]),(6,[2,3,22721]),(10,[2,68171]),
    (131,[]),(147,[]),(135,[]),(131,[]),(157,[]),
    (7,[2,7,9743]),(131,[]),(135,[]),(355,[]),(131,[]),
    (5,[2,3,22741]),(19,[2,31,31,71]),(131,[]),(22,[2,3,23,23,43]),(141,[]),
    (131,[]),(135,[]),(5,[2,68261]),(131,[]),(139,[]),
    (5,[2,67,1019]),(131,[]),(165,[]),(201,[]),(131,[]),
    (2,[2,3,3,7589]),(10,[2,167,409]),(131,[]),(445,[]),(141,[]),
    (131,[]),(145,[]),(147,[]),(131,[]),(181,[]),
    (135,[]),(131,[]),(175,[]),(29,[2,137,499]),(131,[]),
    (141,[]),(139,[]),(131,[]),(171,[]),(135,[]),
    (131,[]),(139,[]),(189,[]),(131,[]),(135,[]),
    (409,[]),(131,[]),(145,[]),(5,[2,89,769]),(131,[]),
    (141,[]),(207,[]),(131,[]),(135,[]),(10,[2,13,23,229]),
    (131,[]),(17,[2,3,3,7,1087]),(157,[]),(131,[]),(19,[2,3,17,17,79])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock137 : ∃ data, checkBlock 137 data = true :=
  ⟨[(145,[]),(131,[]),(391,[]),(139,[]),(131,[]),
    (147,[]),(169,[]),(131,[]),(157,[]),(10,[2,68543]),
    (131,[]),(295,[]),(135,[]),(131,[]),(42,[2,3,3,19,401]),
    (5,[2,47,1459]),(131,[]),(201,[]),(13,[2,113,607]),(131,[]),
    (139,[]),(135,[]),(131,[]),(169,[]),(199,[]),
    (131,[]),(135,[]),(141,[]),(131,[]),(151,[]),
    (10,[2,11,79,79]),(131,[]),(181,[]),(217,[]),(131,[]),
    (135,[]),(5,[2,173,397]),(131,[]),(10,[2,3,7,3271]),(5,[2,73,941]),
    (131,[]),(441,[]),(139,[]),(131,[]),(2,[2,3,22907]),
    (13,[2,19,3617]),(131,[]),(139,[]),(5,[2,53,1297]),(131,[]),
    (147,[]),(5,[2,197,349]),(131,[]),(141,[]),(135,[]),
    (131,[]),(151,[]),(10,[2,11,13,13,37]),(131,[]),(47,[2,3,23,997]),
    (165,[]),(131,[]),(5,[2,3,22937]),(135,[]),(131,[]),
    (187,[]),(157,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(11,[2,3,59,389]),(14,[2,13,5297]),(131,[]),(40,[2,3,11,2087]),
    (151,[]),(131,[]),(135,[]),(339,[]),(131,[]),
    (42,[2,3,7,17,193]),(147,[]),(131,[]),(97,[2,3,3,13,19,31]),(435,[]),
    (131,[]),(139,[]),(5,[2,29,2377]),(131,[]),(145,[]),
    (367,[]),(131,[]),(235,[]),(10,[2,68963]),(131,[]),
    (2,[2,3,83,277]),(135,[]),(131,[]),(5,[2,3,13,29,61]),(171,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock138 : ∃ data, checkBlock 138 data = true :=
  ⟨[(131,[]),(6,[2,3,3,11,17,41]),(145,[]),(131,[]),(159,[]),
    (135,[]),(131,[]),(229,[]),(139,[]),(131,[]),
    (135,[]),(5,[2,199,347]),(131,[]),(139,[]),(10,[2,17,17,239]),
    (131,[]),(2,[2,3,23027]),(159,[]),(131,[]),(135,[]),
    (141,[]),(131,[]),(405,[]),(145,[]),(131,[]),
    (6,[2,3,23041]),(147,[]),(131,[]),(2,[2,3,19,1213]),(189,[]),
    (131,[]),(141,[]),(5,[2,23,31,97]),(131,[]),(165,[]),
    (139,[]),(131,[]),(307,[]),(135,[]),(131,[]),
    (2,[2,3,3,3,11,233]),(10,[2,69203]),(131,[]),(2,[2,3,23071]),(295,[]),
    (131,[]),(141,[]),(135,[]),(131,[]),(207,[]),
    (171,[]),(131,[]),(135,[]),(211,[]),(131,[]),
    (37,[2,3,3,43,179]),(5,[2,29,2389]),(131,[]),(267,[]),(5,[2,7,19,521]),
    (131,[]),(135,[]),(195,[]),(131,[]),(147,[]),
    (10,[2,181,383]),(131,[]),(151,[]),(5,[2,69341]),(131,[]),
    (145,[]),(157,[]),(131,[]),(6,[2,3,3,3,7,367]),(139,[]),
    (131,[]),(2,[2,3,3,13,593]),(321,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(157,[]),(141,[]),(131,[]),
    (171,[]),(14,[2,69431]),(131,[]),(17,[2,3,79,293]),(135,[]),
    (131,[]),(145,[]),(5,[2,7,9923]),(131,[]),(135,[]),
    (147,[]),(131,[]),(10,[2,3,19,23,53]),(141,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock139 : ∃ data, checkBlock 139 data = true :=
  ⟨[(357,[]),(139,[]),(131,[]),(135,[]),(145,[]),
    (131,[]),(187,[]),(5,[2,31,2243]),(131,[]),(141,[]),
    (241,[]),(131,[]),(2,[2,3,3,59,131]),(151,[]),(131,[]),
    (475,[]),(445,[]),(131,[]),(139,[]),(5,[2,69593]),
    (131,[]),(235,[]),(135,[]),(131,[]),(141,[]),
    (145,[]),(131,[]),(2,[2,3,3,3,2579]),(159,[]),(131,[]),
    (20,[2,3,3,71,109]),(135,[]),(131,[]),(147,[]),(28,[2,7,37,269]),
    (131,[]),(135,[]),(13,[2,17,4099]),(131,[]),(34,[2,3,13,1787]),
    (139,[]),(131,[]),(5,[2,3,19,1223]),(195,[]),(131,[]),
    (135,[]),(217,[]),(131,[]),(12,[2,3,3,3,3,3,7,41]),(29,[2,97,719]),
    (131,[]),(189,[]),(169,[]),(131,[]),(175,[]),
    (5,[2,11,6343]),(131,[]),(361,[]),(225,[]),(131,[]),
    (265,[]),(141,[]),(131,[]),(20,[2,3,3,7757]),(135,[]),
    (131,[]),(20,[2,3,3,7759]),(139,[]),(131,[]),(169,[]),
    (10,[2,23,3037]),(131,[]),(145,[]),(135,[]),(131,[]),
    (11,[2,3,23291]),(141,[]),(131,[]),(135,[]),(5,[2,37,1889]),
    (131,[]),(379,[]),(165,[]),(131,[]),(139,[]),
    (237,[]),(131,[]),(135,[]),(5,[2,69941]),(131,[]),
    (159,[]),(5,[2,13,5381]),(131,[]),(145,[]),(10,[2,11,6361]),
    (131,[]),(195,[]),(10,[2,47,1489]),(131,[]),(11,[2,3,3,7,11,101])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock140 : ∃ data, checkBlock 140 data = true :=
  ⟨[(319,[]),(131,[]),(141,[]),(159,[]),(131,[]),
    (151,[]),(135,[]),(131,[]),(199,[]),(147,[]),
    (131,[]),(139,[]),(5,[2,70061]),(131,[]),(5,[2,3,23357]),
    (135,[]),(131,[]),(75,[2,3,3,13,599]),(231,[]),(131,[]),
    (135,[]),(10,[2,11,6373]),(131,[]),(17,[2,3,23371]),(187,[]),
    (131,[]),(12,[2,3,97,241]),(145,[]),(131,[]),(135,[]),
    (301,[]),(131,[]),(151,[]),(139,[]),(131,[]),
    (421,[]),(5,[2,70181]),(131,[]),(207,[]),(141,[]),
    (131,[]),(5,[2,3,7,3343]),(34,[2,61,1151]),(131,[]),(2,[2,3,89,263]),
    (157,[]),(131,[]),(147,[]),(135,[]),(131,[]),
    (139,[]),(151,[]),(131,[]),(5,[2,3,3,37,211]),(141,[]),
    (131,[]),(157,[]),(135,[]),(131,[]),(2,[2,3,23431]),
    (7,[2,7,11,11,83]),(131,[]),(135,[]),(5,[2,70313]),(131,[]),
    (141,[]),(30,[2,53,1327]),(131,[]),(2,[2,3,23447]),(397,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(145,[]),
    (225,[]),(131,[]),(139,[]),(151,[]),(131,[]),
    (141,[]),(267,[]),(131,[]),(2,[2,3,7,7,479]),(255,[]),
    (131,[]),(5,[2,3,17,1381]),(5,[2,11,19,337]),(131,[]),(217,[]),
    (135,[]),(131,[]),(147,[]),(181,[]),(131,[]),
    (145,[]),(201,[]),(131,[]),(52,[2,3,23497]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock141 : ∃ data, checkBlock 141 data = true :=
  ⟨[(131,[]),(165,[]),(10,[2,7,7,1439]),(131,[]),(135,[]),
    (175,[]),(131,[]),(2,[2,3,3,17,461]),(145,[]),(131,[]),
    (277,[]),(5,[2,7,10079]),(131,[]),(135,[]),(157,[]),
    (131,[]),(139,[]),(141,[]),(131,[]),(187,[]),
    (465,[]),(131,[]),(5,[2,3,23537]),(147,[]),(131,[]),
    (265,[]),(10,[2,11,6421]),(131,[]),(2,[2,3,3,47,167]),(145,[]),
    (131,[]),(47,[2,3,11,2141]),(135,[]),(131,[]),(409,[]),
    (235,[]),(131,[]),(501,[]),(139,[]),(131,[]),
    (11,[2,3,23567]),(135,[]),(131,[]),(139,[]),(17,[2,7,10103]),
    (131,[]),(135,[]),(369,[]),(131,[]),(279,[]),
    (199,[]),(131,[]),(225,[]),(435,[]),(131,[]),
    (135,[]),(181,[]),(131,[]),(141,[]),(5,[2,70793]),
    (131,[]),(147,[]),(10,[2,13,13,419]),(131,[]),(325,[]),
    (139,[]),(131,[]),(2,[2,3,7,3373]),(147,[]),(131,[]),
    (151,[]),(5,[2,70853]),(131,[]),(367,[]),(135,[]),
    (131,[]),(145,[]),(29,[2,73,971]),(131,[]),(199,[]),
    (5,[2,70901]),(131,[]),(139,[]),(135,[]),(131,[]),
    (211,[]),(13,[2,7,10133]),(131,[]),(135,[]),(151,[]),
    (131,[]),(20,[2,3,67,353]),(475,[]),(131,[]),(171,[]),
    (141,[]),(131,[]),(135,[]),(169,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock142 : ∃ data, checkBlock 142 data = true :=
  ⟨[(339,[]),(19,[2,19,37,101]),(131,[]),(237,[]),(139,[]),
    (131,[]),(147,[]),(5,[2,251,283]),(131,[]),(139,[]),
    (141,[]),(131,[]),(2,[2,3,23687]),(439,[]),(131,[]),
    (169,[]),(135,[]),(131,[]),(37,[2,3,3,3,2633]),(157,[]),
    (131,[]),(141,[]),(10,[2,17,47,89]),(131,[]),(231,[]),
    (135,[]),(131,[]),(241,[]),(391,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(10,[2,3,3,7907]),(265,[]),
    (131,[]),(141,[]),(147,[]),(131,[]),(135,[]),
    (5,[2,13,5477]),(131,[]),(201,[]),(5,[2,17,59,71]),(131,[]),
    (309,[]),(237,[]),(131,[]),(139,[]),(165,[]),
    (131,[]),(159,[]),(487,[]),(131,[]),(10,[2,3,3,7919]),
    (5,[2,263,271]),(131,[]),(20,[2,3,23761]),(135,[]),(131,[]),
    (187,[]),(10,[2,113,631]),(131,[]),(321,[]),(195,[]),
    (131,[]),(307,[]),(135,[]),(131,[]),(225,[]),
    (139,[]),(131,[]),(135,[]),(141,[]),(131,[]),
    (139,[]),(495,[]),(131,[]),(145,[]),(5,[2,7,7,31,47]),
    (131,[]),(135,[]),(147,[]),(131,[]),(211,[]),
    (339,[]),(131,[]),(2,[2,3,3,7937]),(141,[]),(131,[]),
    (5,[2,3,3,17,467]),(5,[2,71453]),(131,[]),(175,[]),(351,[]),
    (131,[]),(2,[2,3,23827]),(139,[]),(131,[]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock143 : ∃ data, checkBlock 143 data = true :=
  ⟨[(135,[]),(131,[]),(217,[]),(285,[]),(131,[]),
    (181,[]),(13,[2,233,307]),(131,[]),(151,[]),(135,[]),
    (131,[]),(22,[2,3,17,23,61]),(145,[]),(131,[]),(135,[]),
    (171,[]),(131,[]),(189,[]),(259,[]),(131,[]),
    (147,[]),(199,[]),(131,[]),(135,[]),(5,[2,11,17,383]),
    (131,[]),(77,[2,3,3,3,7,379]),(151,[]),(131,[]),(43,[2,3,11,13,167]),
    (175,[]),(131,[]),(459,[]),(145,[]),(131,[]),
    (157,[]),(139,[]),(131,[]),(255,[]),(5,[2,71693]),
    (131,[]),(139,[]),(135,[]),(131,[]),(11,[2,3,3,13,613]),
    (195,[]),(131,[]),(62,[2,3,23911]),(5,[2,71741]),(131,[]),
    (5,[2,3,23917]),(135,[]),(131,[]),(5,[2,3,19,1259]),(151,[]),
    (131,[]),(135,[]),(13,[2,23,3121]),(131,[]),(267,[]),
    (291,[]),(131,[]),(159,[]),(139,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(181,[]),(10,[2,71843]),
    (131,[]),(259,[]),(229,[]),(131,[]),(12,[2,3,23957]),
    (159,[]),(131,[]),(141,[]),(187,[]),(131,[]),
    (139,[]),(10,[2,13,5531]),(131,[]),(12,[2,3,23971]),(135,[]),
    (131,[]),(421,[]),(175,[]),(131,[]),(147,[]),
    (279,[]),(131,[]),(141,[]),(135,[]),(131,[]),
    (30,[2,3,3,11,727]),(147,[]),(131,[]),(135,[]),(265,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock144 : ∃ data, checkBlock 144 data = true :=
  ⟨[(131,[]),(145,[]),(139,[]),(131,[]),(157,[]),
    (411,[]),(131,[]),(135,[]),(277,[]),(131,[]),
    (19,[2,3,7,47,73]),(181,[]),(131,[]),(229,[]),(145,[]),
    (131,[]),(12,[2,3,3,8009]),(14,[2,11,6553]),(131,[]),(151,[]),
    (5,[2,72101]),(131,[]),(45,[2,3,13,43,43]),(361,[]),(131,[]),
    (10,[2,3,29,829]),(135,[]),(131,[]),(285,[]),(139,[]),
    (131,[]),(11,[2,3,3,8017]),(5,[2,72161]),(131,[]),(147,[]),
    (135,[]),(131,[]),(159,[]),(20,[2,7,10313]),(131,[]),
    (135,[]),(14,[2,103,701]),(131,[]),(17,[2,3,24071]),(141,[]),
    (131,[]),(139,[]),(201,[]),(131,[]),(135,[]),
    (211,[]),(131,[]),(171,[]),(241,[]),(131,[]),
    (141,[]),(5,[2,11,6571]),(131,[]),(20,[2,3,24097]),(319,[]),
    (131,[]),(169,[]),(157,[]),(131,[]),(237,[]),
    (147,[]),(131,[]),(20,[2,3,3,3,3,19,47]),(135,[]),(131,[]),
    (141,[]),(165,[]),(131,[]),(139,[]),(181,[]),
    (131,[]),(11,[2,3,23,1049]),(135,[]),(131,[]),(195,[]),
    (217,[]),(131,[]),(135,[]),(379,[]),(131,[]),
    (33,[2,3,3,13,619]),(159,[]),(131,[]),(2,[2,3,3,3,2683]),(13,[2,7,79,131]),
    (131,[]),(135,[]),(151,[]),(131,[]),(321,[]),
    (139,[]),(131,[]),(5,[2,3,37,653]),(10,[2,71,1021]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock145 : ∃ data, checkBlock 145 data = true :=
  ⟨[(165,[]),(10,[2,72503]),(131,[]),(145,[]),(5,[2,47,1543]),
    (131,[]),(5,[2,3,3,8059]),(141,[]),(131,[]),(157,[]),
    (135,[]),(131,[]),(139,[]),(231,[]),(131,[]),
    (301,[]),(145,[]),(131,[]),(175,[]),(135,[]),
    (131,[]),(23,[2,3,3,3,2689]),(141,[]),(131,[]),(135,[]),
    (465,[]),(131,[]),(2,[2,3,11,31,71]),(5,[2,17,4273]),(131,[]),
    (10,[2,3,61,397]),(5,[2,7,97,107]),(131,[]),(135,[]),(139,[]),
    (131,[]),(189,[]),(145,[]),(131,[]),(139,[]),
    (225,[]),(131,[]),(10,[2,3,3,3,2693]),(169,[]),(131,[]),
    (165,[]),(34,[2,257,283]),(131,[]),(141,[]),(10,[2,11,17,389]),
    (131,[]),(355,[]),(135,[]),(131,[]),(5,[2,3,127,191]),
    (5,[2,61,1193]),(131,[]),(151,[]),(325,[]),(131,[]),
    (18,[2,3,3,8089]),(135,[]),(131,[]),(235,[]),(6,[2,7,101,103]),
    (131,[]),(135,[]),(157,[]),(131,[]),(20,[2,3,24281]),
    (19,[2,263,277]),(131,[]),(12,[2,3,149,163]),(171,[]),(131,[]),
    (135,[]),(199,[]),(131,[]),(139,[]),(147,[]),
    (131,[]),(38,[2,3,19,1279]),(19,[2,72911]),(131,[]),(145,[]),
    (141,[]),(131,[]),(327,[]),(241,[]),(131,[]),
    (5,[2,3,24317]),(187,[]),(131,[]),(201,[]),(135,[]),
    (131,[]),(18,[2,3,3,3,3,17,53]),(19,[2,59,1237]),(131,[]),(2,[2,3,29,839])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock146 : ∃ data, checkBlock 146 data = true :=
  ⟨[(139,[]),(131,[]),(11,[2,3,24337]),(135,[]),(131,[]),
    (139,[]),(10,[2,7,10433]),(131,[]),(135,[]),(475,[]),
    (131,[]),(141,[]),(175,[]),(131,[]),(187,[]),
    (229,[]),(131,[]),(135,[]),(145,[]),(131,[]),
    (32,[2,3,7,59,59]),(421,[]),(131,[]),(159,[]),(147,[]),
    (131,[]),(141,[]),(139,[]),(131,[]),(369,[]),
    (151,[]),(131,[]),(11,[2,3,3,11,739]),(259,[]),(131,[]),
    (2,[2,3,24391]),(135,[]),(131,[]),(38,[2,3,31,787]),(145,[]),
    (131,[]),(5,[2,3,13,1877]),(14,[2,179,409]),(131,[]),(139,[]),
    (135,[]),(131,[]),(277,[]),(165,[]),(131,[]),
    (135,[]),(367,[]),(131,[]),(20,[2,3,24421]),(33,[2,11,6661]),
    (131,[]),(17,[2,3,13,1879]),(225,[]),(131,[]),(135,[]),
    (6,[2,23,3187]),(131,[]),(147,[]),(141,[]),(131,[]),
    (6,[2,3,3,8147]),(139,[]),(131,[]),(2,[2,3,3,29,281]),(175,[]),
    (131,[]),(139,[]),(159,[]),(131,[]),(10,[2,3,37,661]),
    (385,[]),(131,[]),(20,[2,3,61,401]),(135,[]),(131,[]),
    (201,[]),(10,[2,11,6673]),(131,[]),(157,[]),(5,[2,73421]),
    (131,[]),(145,[]),(135,[]),(131,[]),(141,[]),
    (169,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (151,[]),(409,[]),(131,[]),(10,[2,3,11,17,131]),(6,[2,7,10499])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock147 : ∃ data, checkBlock 147 data = true :=
  ⟨[(131,[]),(135,[]),(361,[]),(131,[]),(141,[]),
    (19,[2,73523]),(131,[]),(145,[]),(5,[2,13,5657]),(131,[]),
    (139,[]),(5,[2,73553]),(131,[]),(295,[]),(397,[]),
    (131,[]),(37,[2,3,24527]),(495,[]),(131,[]),(231,[]),
    (135,[]),(131,[]),(151,[]),(5,[2,73613]),(131,[]),
    (357,[]),(14,[2,29,2539]),(131,[]),(2,[2,3,24547]),(135,[]),
    (131,[]),(147,[]),(139,[]),(131,[]),(135,[]),
    (5,[2,73673]),(131,[]),(139,[]),(147,[]),(131,[]),
    (351,[]),(141,[]),(131,[]),(135,[]),(411,[]),
    (131,[]),(367,[]),(159,[]),(131,[]),(12,[2,3,47,523]),
    (10,[2,73751]),(131,[]),(157,[]),(279,[]),(131,[]),
    (30,[2,3,3,7,1171]),(141,[]),(131,[]),(5,[2,3,3,3,3,911]),(139,[]),
    (131,[]),(10,[2,3,73,337]),(135,[]),(131,[]),(319,[]),
    (10,[2,73823]),(131,[]),(141,[]),(151,[]),(131,[]),
    (5,[2,3,103,239]),(135,[]),(131,[]),(5,[2,3,3,29,283]),(20,[2,7,61,173]),
    (131,[]),(135,[]),(235,[]),(131,[]),(17,[2,3,24631]),
    (189,[]),(131,[]),(141,[]),(5,[2,7,10559]),(131,[]),
    (135,[]),(10,[2,11,11,13,47]),(131,[]),(145,[]),(169,[]),
    (131,[]),(481,[]),(181,[]),(131,[]),(465,[]),
    (325,[]),(131,[]),(207,[]),(139,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock148 : ∃ data, checkBlock 148 data = true :=
  ⟨[(175,[]),(217,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(5,[2,3,24677]),(147,[]),(131,[]),(145,[]),
    (157,[]),(131,[]),(22,[2,3,3,3,13,211]),(135,[]),(131,[]),
    (33,[2,3,24691]),(357,[]),(131,[]),(135,[]),(141,[]),
    (131,[]),(23,[2,3,17,1453]),(145,[]),(131,[]),(18,[2,3,31,797]),
    (139,[]),(131,[]),(135,[]),(207,[]),(131,[]),
    (5,[2,3,3,7,11,107]),(171,[]),(131,[]),(151,[]),(141,[]),
    (131,[]),(217,[]),(20,[2,31,2393]),(131,[]),(12,[2,3,7,3533]),
    (5,[2,74201]),(131,[]),(139,[]),(145,[]),(131,[]),
    (141,[]),(135,[]),(131,[]),(2,[2,3,3,73,113]),(211,[]),
    (131,[]),(225,[]),(147,[]),(131,[]),(169,[]),
    (135,[]),(131,[]),(157,[]),(159,[]),(131,[]),
    (135,[]),(301,[]),(131,[]),(61,[2,3,3,23,359]),(139,[]),
    (131,[]),(6,[2,3,3,3,2753]),(5,[2,7,7,37,41]),(131,[]),(135,[]),
    (165,[]),(131,[]),(11,[2,3,7,3541]),(29,[2,74363]),(131,[]),
    (17,[2,3,13,1907]),(5,[2,74381]),(131,[]),(41,[2,3,137,181]),(151,[]),
    (131,[]),(195,[]),(171,[]),(131,[]),(379,[]),
    (201,[]),(131,[]),(29,[2,3,43,577]),(135,[]),(131,[]),
    (145,[]),(139,[]),(131,[]),(11,[2,3,24821]),(175,[]),
    (131,[]),(309,[]),(135,[]),(131,[]),(511,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock149 : ∃ data, checkBlock 149 data = true :=
  ⟨[(237,[]),(131,[]),(135,[]),(5,[2,269,277]),(131,[]),
    (241,[]),(151,[]),(131,[]),(139,[]),(14,[2,7,23,463]),
    (131,[]),(135,[]),(141,[]),(131,[]),(6,[2,3,7,53,67]),
    (157,[]),(131,[]),(171,[]),(10,[2,11,6781]),(131,[]),
    (159,[]),(147,[]),(131,[]),(141,[]),(145,[]),
    (131,[]),(157,[]),(189,[]),(131,[]),(5,[2,3,139,179]),
    (135,[]),(131,[]),(2,[2,3,41,607]),(159,[]),(131,[]),
    (139,[]),(169,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(181,[]),(19,[2,7,13,821]),(131,[]),(135,[]),
    (145,[]),(131,[]),(265,[]),(211,[]),(131,[]),
    (23,[2,3,24917]),(175,[]),(131,[]),(135,[]),(10,[2,74771]),
    (131,[]),(12,[2,3,3,7,1187]),(139,[]),(131,[]),(147,[]),
    (5,[2,131,571]),(131,[]),(5,[2,3,11,2267]),(5,[2,79,947]),(131,[]),
    (391,[]),(147,[]),(131,[]),(171,[]),(309,[]),
    (131,[]),(151,[]),(135,[]),(131,[]),(139,[]),
    (141,[]),(131,[]),(12,[2,3,109,229]),(229,[]),(131,[]),
    (2,[2,3,24967]),(135,[]),(131,[]),(20,[2,3,24971]),(157,[]),
    (131,[]),(135,[]),(5,[2,74933]),(131,[]),(165,[]),
    (141,[]),(131,[]),(145,[]),(441,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(151,[]),(255,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock150 : ∃ data, checkBlock 150 data = true :=
  ⟨[(131,[]),(139,[]),(199,[]),(131,[]),(147,[]),
    (355,[]),(131,[]),(2,[2,3,3,3,7,397]),(5,[2,75041]),(131,[]),
    (495,[]),(5,[2,11,6823]),(131,[]),(145,[]),(135,[]),
    (131,[]),(141,[]),(151,[]),(131,[]),(229,[]),
    (5,[2,13,53,109]),(131,[]),(34,[2,3,25037]),(135,[]),(131,[]),
    (10,[2,3,3,17,491]),(145,[]),(131,[]),(135,[]),(10,[2,163,461]),
    (131,[]),(157,[]),(5,[2,75161]),(131,[]),(5,[2,3,25057]),
    (147,[]),(131,[]),(135,[]),(14,[2,17,4423]),(131,[]),
    (139,[]),(10,[2,157,479]),(131,[]),(45,[2,3,3,61,137]),(151,[]),
    (131,[]),(507,[]),(145,[]),(131,[]),(189,[]),
    (10,[2,11,6841]),(131,[]),(2,[2,3,25087]),(141,[]),(131,[]),
    (279,[]),(135,[]),(131,[]),(20,[2,3,25097]),(5,[2,17,43,103]),
    (131,[]),(5,[2,3,3,3,2789]),(139,[]),(131,[]),(327,[]),
    (135,[]),(131,[]),(139,[]),(141,[]),(131,[]),
    (135,[]),(5,[2,75353]),(131,[]),(147,[]),(37,[2,23,29,113]),
    (131,[]),(235,[]),(10,[2,7,11,11,89]),(131,[]),(135,[]),
    (147,[]),(131,[]),(175,[]),(5,[2,13,5801]),(131,[]),
    (5,[2,3,31,811]),(187,[]),(131,[]),(13,[2,3,25147]),(139,[]),
    (131,[]),(2,[2,3,7,3593]),(165,[]),(131,[]),(141,[]),
    (399,[]),(131,[]),(5,[2,3,3,8387]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock151 : ∃ data, checkBlock 151 data = true :=
  ⟨[(157,[]),(45,[2,75503]),(131,[]),(12,[2,3,25171]),(259,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(151,[]),
    (181,[]),(131,[]),(135,[]),(207,[]),(131,[]),
    (145,[]),(5,[2,11,6871]),(131,[]),(147,[]),(159,[]),
    (131,[]),(135,[]),(225,[]),(131,[]),(2,[2,3,7,13,277]),
    (19,[2,47,1609]),(131,[]),(459,[]),(139,[]),(131,[]),
    (19,[2,3,151,167]),(141,[]),(131,[]),(139,[]),(10,[2,31,2441]),
    (131,[]),(151,[]),(165,[]),(131,[]),(175,[]),
    (135,[]),(131,[]),(5,[2,3,25237]),(291,[]),(131,[]),
    (397,[]),(141,[]),(131,[]),(33,[2,3,25247]),(135,[]),
    (131,[]),(11,[2,3,3,19,443]),(5,[2,7,79,137]),(131,[]),(135,[]),
    (139,[]),(131,[]),(141,[]),(157,[]),(131,[]),
    (2,[2,3,11,2297]),(14,[2,7,7,7,13,17]),(131,[]),(135,[]),(5,[2,75821]),
    (131,[]),(165,[]),(5,[2,75833]),(131,[]),(28,[2,3,3,3,53,53]),
    (19,[2,101,751]),(131,[]),(139,[]),(199,[]),(131,[]),
    (171,[]),(175,[]),(131,[]),(45,[2,3,41,617]),(5,[2,29,2617]),
    (131,[]),(159,[]),(135,[]),(131,[]),(445,[]),
    (22,[2,23,3301]),(131,[]),(147,[]),(5,[2,75941]),(131,[]),
    (37,[2,3,3,3,29,97]),(135,[]),(131,[]),(267,[]),(139,[]),
    (131,[]),(135,[]),(14,[2,75983]),(131,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock152 : ∃ data, checkBlock 152 data = true :=
  ⟨[(5,[2,76001]),(131,[]),(195,[]),(5,[2,7,10859]),(131,[]),
    (135,[]),(13,[2,76031]),(131,[]),(79,[2,3,3,7,17,71]),(141,[]),
    (131,[]),(165,[]),(5,[2,23,3307]),(131,[]),(481,[]),
    (5,[2,127,599]),(131,[]),(145,[]),(10,[2,76091]),(131,[]),
    (28,[2,3,25367]),(139,[]),(131,[]),(319,[]),(135,[]),
    (131,[]),(171,[]),(5,[2,19,4007]),(131,[]),(6,[2,3,17,1493]),
    (145,[]),(131,[]),(147,[]),(135,[]),(131,[]),
    (141,[]),(5,[2,7,10883]),(131,[]),(135,[]),(225,[]),
    (131,[]),(12,[2,3,3,8467]),(19,[2,17,4483]),(131,[]),(11,[2,3,3,3,3,941]),
    (285,[]),(131,[]),(135,[]),(267,[]),(131,[]),
    (141,[]),(145,[]),(131,[]),(255,[]),(231,[]),
    (131,[]),(11,[2,3,47,541]),(14,[2,76283]),(131,[]),(181,[]),
    (139,[]),(131,[]),(10,[2,3,3,61,139]),(147,[]),(131,[]),
    (139,[]),(135,[]),(131,[]),(189,[]),(307,[]),
    (131,[]),(207,[]),(5,[2,19,4019]),(131,[]),(151,[]),
    (135,[]),(131,[]),(5,[2,3,3,3,3,23,41]),(10,[2,7,7,1559]),(131,[]),
    (135,[]),(169,[]),(131,[]),(195,[]),(5,[2,76421]),
    (131,[]),(199,[]),(139,[]),(131,[]),(135,[]),
    (235,[]),(131,[]),(159,[]),(151,[]),(131,[]),
    (2,[2,3,3,29,293]),(279,[]),(131,[]),(145,[]),(187,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock153 : ∃ data, checkBlock 153 data = true :=
  ⟨[(131,[]),(147,[]),(141,[]),(131,[]),(139,[]),
    (159,[]),(131,[]),(2,[2,3,97,263]),(135,[]),(131,[]),
    (411,[]),(5,[2,37,2069]),(131,[]),(141,[]),(165,[]),
    (131,[]),(225,[]),(135,[]),(131,[]),(145,[]),
    (151,[]),(131,[]),(135,[]),(201,[]),(131,[]),
    (39,[2,3,25541]),(139,[]),(131,[]),(141,[]),(14,[2,7,10949]),
    (131,[]),(135,[]),(145,[]),(131,[]),(5,[2,3,3,7,1217]),
    (217,[]),(131,[]),(231,[]),(291,[]),(131,[]),
    (307,[]),(10,[2,11,19,367]),(131,[]),(2,[2,3,7,13,281]),(5,[2,17,4513]),
    (131,[]),(147,[]),(171,[]),(131,[]),(5,[2,3,3,8527]),
    (135,[]),(131,[]),(12,[2,3,3,3,2843]),(139,[]),(131,[]),
    (361,[]),(5,[2,76781]),(131,[]),(511,[]),(135,[]),
    (131,[]),(5,[2,3,25601]),(13,[2,7,10973]),(131,[]),(135,[]),
    (141,[]),(131,[]),(159,[]),(441,[]),(131,[]),
    (139,[]),(409,[]),(131,[]),(135,[]),(13,[2,76871]),
    (131,[]),(2,[2,3,7,7,523]),(147,[]),(131,[]),(157,[]),
    (141,[]),(131,[]),(229,[]),(327,[]),(131,[]),
    (151,[]),(379,[]),(131,[]),(165,[]),(19,[2,76943]),
    (131,[]),(141,[]),(135,[]),(131,[]),(385,[]),
    (5,[2,13,31,191]),(131,[]),(139,[]),(171,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock154 : ∃ data, checkBlock 154 data = true :=
  ⟨[(145,[]),(135,[]),(131,[]),(2,[2,3,3,43,199]),(5,[2,7,11003]),
    (131,[]),(135,[]),(5,[2,11,47,149]),(131,[]),(5,[2,3,61,421]),
    (201,[]),(131,[]),(151,[]),(14,[2,7,101,109]),(131,[]),
    (135,[]),(159,[]),(131,[]),(28,[2,3,7,3671]),(139,[]),
    (131,[]),(145,[]),(147,[]),(131,[]),(11,[2,3,3,11,19,41]),
    (10,[2,233,331]),(131,[]),(50,[2,3,7,3673]),(169,[]),(131,[]),
    (5,[2,3,25717]),(151,[]),(131,[]),(165,[]),(135,[]),
    (131,[]),(139,[]),(157,[]),(131,[]),(2,[2,3,3,3,3,953]),
    (187,[]),(131,[]),(5,[2,3,3,23,373]),(135,[]),(131,[]),
    (169,[]),(211,[]),(131,[]),(135,[]),(10,[2,77243]),
    (131,[]),(495,[]),(5,[2,77261]),(131,[]),(5,[2,3,43,599]),
    (145,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (147,[]),(477,[]),(131,[]),(139,[]),(5,[2,167,463]),
    (131,[]),(339,[]),(5,[2,17,4549]),(131,[]),(141,[]),
    (195,[]),(131,[]),(17,[2,3,107,241]),(22,[2,11,13,541]),(131,[]),
    (2,[2,3,3,8597]),(135,[]),(131,[]),(159,[]),(5,[2,193,401]),
    (131,[]),(10,[2,3,25801]),(10,[2,199,389]),(131,[]),(141,[]),
    (135,[]),(131,[]),(379,[]),(5,[2,7,13,23,37]),(131,[]),
    (135,[]),(147,[]),(131,[]),(5,[2,3,3,3,19,151]),(19,[2,77471]),
    (131,[]),(369,[]),(481,[]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock155 : ∃ data, checkBlock 155 data = true :=
  ⟨[(6,[2,19,4079]),(131,[]),(139,[]),(5,[2,77513]),(131,[]),
    (5,[2,3,25841]),(157,[]),(131,[]),(2,[2,3,25847]),(10,[2,77543]),
    (131,[]),(237,[]),(189,[]),(131,[]),(295,[]),
    (175,[]),(131,[]),(10,[2,3,11,2351]),(135,[]),(131,[]),
    (11,[2,3,25867]),(141,[]),(131,[]),(145,[]),(139,[]),
    (131,[]),(267,[]),(135,[]),(131,[]),(139,[]),
    (13,[2,7,11093]),(131,[]),(135,[]),(14,[2,37,2099]),(131,[]),
    (187,[]),(141,[]),(131,[]),(6,[2,3,19,29,47]),(5,[2,7,11,1009]),
    (131,[]),(135,[]),(10,[2,77711]),(131,[]),(19,[2,3,7,3701]),
    (487,[]),(131,[]),(141,[]),(217,[]),(131,[]),
    (151,[]),(139,[]),(131,[]),(157,[]),(237,[]),
    (131,[]),(201,[]),(145,[]),(131,[]),(285,[]),
    (135,[]),(131,[]),(141,[]),(5,[2,77813]),(131,[]),
    (445,[]),(14,[2,13,5987]),(131,[]),(139,[]),(135,[]),
    (131,[]),(12,[2,3,25951]),(5,[2,7,7,7,227]),(131,[]),(135,[]),
    (5,[2,43,1811]),(131,[]),(181,[]),(10,[2,11,73,97]),(131,[]),
    (475,[]),(165,[]),(131,[]),(135,[]),(229,[]),
    (131,[]),(6,[2,3,3,7,1237]),(207,[]),(131,[]),(33,[2,3,25981]),
    (139,[]),(131,[]),(169,[]),(369,[]),(131,[]),
    (139,[]),(151,[]),(131,[]),(279,[]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock156 : ∃ data, checkBlock 156 data = true :=
  ⟨[(131,[]),(10,[2,3,3,3,3,3,3,107]),(135,[]),(131,[]),(145,[]),
    (147,[]),(131,[]),(367,[]),(255,[]),(131,[]),
    (165,[]),(135,[]),(131,[]),(10,[2,3,26021]),(141,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(441,[]),
    (309,[]),(131,[]),(157,[]),(5,[2,7,11159]),(131,[]),
    (135,[]),(435,[]),(131,[]),(259,[]),(501,[]),
    (131,[]),(33,[2,3,109,239]),(351,[]),(131,[]),(139,[]),
    (5,[2,78173]),(131,[]),(399,[]),(145,[]),(131,[]),
    (141,[]),(357,[]),(131,[]),(147,[]),(135,[]),
    (131,[]),(175,[]),(5,[2,78233]),(131,[]),(6,[2,3,11,2371]),
    (147,[]),(131,[]),(321,[]),(135,[]),(131,[]),
    (165,[]),(139,[]),(131,[]),(135,[]),(145,[]),
    (131,[]),(139,[]),(10,[2,78311]),(131,[]),(159,[]),
    (511,[]),(131,[]),(135,[]),(5,[2,78341]),(131,[]),
    (73,[2,3,7,7,13,41]),(5,[2,11,17,419]),(131,[]),(54,[2,3,3,8707]),(169,[]),
    (131,[]),(187,[]),(141,[]),(131,[]),(211,[]),
    (157,[]),(131,[]),(6,[2,3,59,443]),(139,[]),(131,[]),
    (195,[]),(135,[]),(131,[]),(147,[]),(10,[2,47,1669]),
    (131,[]),(169,[]),(141,[]),(131,[]),(5,[2,3,3,8719]),
    (135,[]),(131,[]),(5,[2,3,26161]),(307,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock157 : ∃ data, checkBlock 157 data = true :=
  ⟨[(135,[]),(10,[2,29,2707]),(131,[]),(141,[]),(225,[]),
    (131,[]),(145,[]),(151,[]),(131,[]),(135,[]),
    (10,[2,11,37,193]),(131,[]),(199,[]),(10,[2,251,313]),(131,[]),
    (295,[]),(5,[2,179,439]),(131,[]),(141,[]),(147,[]),
    (131,[]),(5,[2,3,7,19,197]),(139,[]),(131,[]),(11,[2,3,73,359]),
    (34,[2,78623]),(131,[]),(139,[]),(135,[]),(131,[]),
    (11,[2,3,3,3,3,971]),(5,[2,78653]),(131,[]),(19,[2,3,13,2017]),(151,[]),
    (131,[]),(2,[2,3,26227]),(135,[]),(131,[]),(159,[]),
    (145,[]),(131,[]),(135,[]),(5,[2,78713]),(131,[]),
    (207,[]),(181,[]),(131,[]),(32,[2,3,3,13,673]),(139,[]),
    (131,[]),(135,[]),(7,[2,17,41,113]),(131,[]),(10,[2,3,7,11,11,31]),
    (141,[]),(131,[]),(147,[]),(165,[]),(131,[]),
    (301,[]),(145,[]),(131,[]),(2,[2,3,3,3,3,7,139]),(147,[]),
    (131,[]),(139,[]),(5,[2,31,2543]),(131,[]),(265,[]),
    (135,[]),(131,[]),(237,[]),(169,[]),(131,[]),
    (2,[2,3,61,431]),(207,[]),(131,[]),(211,[]),(135,[]),
    (131,[]),(141,[]),(14,[2,7,11273]),(131,[]),(135,[]),
    (157,[]),(131,[]),(2,[2,3,83,317]),(139,[]),(131,[]),
    (397,[]),(5,[2,7,11279]),(131,[]),(135,[]),(187,[]),
    (131,[]),(141,[]),(175,[]),(131,[]),(151,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock158 : ∃ data, checkBlock 158 data = true :=
  ⟨[(5,[2,13,59,103]),(131,[]),(147,[]),(165,[]),(131,[]),
    (5,[2,3,7,53,71]),(391,[]),(131,[]),(145,[]),(241,[]),
    (131,[]),(351,[]),(135,[]),(131,[]),(5,[2,3,26357]),
    (139,[]),(131,[]),(405,[]),(445,[]),(131,[]),
    (409,[]),(135,[]),(131,[]),(11,[2,3,26371]),(6,[2,7,89,127]),
    (131,[]),(135,[]),(229,[]),(131,[]),(145,[]),
    (29,[2,79151]),(131,[]),(139,[]),(141,[]),(131,[]),
    (135,[]),(5,[2,79181]),(131,[]),(169,[]),(277,[]),
    (131,[]),(12,[2,3,17,1553]),(145,[]),(131,[]),(20,[2,3,26407]),
    (151,[]),(131,[]),(235,[]),(141,[]),(131,[]),
    (159,[]),(13,[2,41,1933]),(131,[]),(20,[2,3,3,8807]),(135,[]),
    (131,[]),(11,[2,3,3,23,383]),(30,[2,79283]),(131,[]),(139,[]),
    (327,[]),(131,[]),(255,[]),(135,[]),(131,[]),
    (10,[2,3,137,193]),(13,[2,7,7,1619]),(131,[]),(135,[]),(217,[]),
    (131,[]),(147,[]),(151,[]),(131,[]),(141,[]),
    (5,[2,7,17,23,29]),(131,[]),(135,[]),(147,[]),(131,[]),
    (2,[2,3,7,19,199]),(139,[]),(131,[]),(199,[]),(5,[2,43,1847]),
    (131,[]),(37,[2,3,11,29,83]),(5,[2,79433]),(131,[]),(187,[]),
    (259,[]),(131,[]),(12,[2,3,3,3,3,3,3,109]),(19,[2,229,347]),(131,[]),
    (181,[]),(135,[]),(131,[]),(139,[]),(301,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock159 : ∃ data, checkBlock 159 data = true :=
  ⟨[(131,[]),(157,[]),(13,[2,23,3457]),(131,[]),(217,[]),
    (135,[]),(131,[]),(201,[]),(385,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(355,[]),(171,[]),
    (131,[]),(147,[]),(19,[2,7,11369]),(131,[]),(135,[]),
    (139,[]),(131,[]),(5,[2,3,7,17,223]),(5,[2,79613]),(131,[]),
    (139,[]),(141,[]),(131,[]),(175,[]),(13,[2,73,1091]),
    (131,[]),(145,[]),(235,[]),(131,[]),(207,[]),
    (5,[2,11,7243]),(131,[]),(141,[]),(135,[]),(131,[]),
    (20,[2,3,31,857]),(59,[2,13,6131]),(131,[]),(259,[]),(145,[]),
    (131,[]),(12,[2,3,3,3,2953]),(135,[]),(131,[]),(171,[]),
    (10,[2,7,11393]),(131,[]),(135,[]),(195,[]),(131,[]),
    (231,[]),(5,[2,13,17,19,19]),(131,[]),(181,[]),(157,[]),
    (131,[]),(135,[]),(14,[2,79811]),(131,[]),(139,[]),
    (145,[]),(131,[]),(32,[2,3,13,23,89]),(5,[2,79841]),(131,[]),
    (157,[]),(5,[2,47,1699]),(131,[]),(339,[]),(159,[]),
    (131,[]),(12,[2,3,26627]),(325,[]),(131,[]),(2,[2,3,3,3,11,269]),
    (135,[]),(131,[]),(309,[]),(151,[]),(131,[]),
    (147,[]),(139,[]),(131,[]),(229,[]),(135,[]),
    (131,[]),(139,[]),(147,[]),(131,[]),(135,[]),
    (435,[]),(131,[]),(475,[]),(285,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock160 : ∃ data, checkBlock 160 data = true :=
  ⟨[(171,[]),(181,[]),(131,[]),(135,[]),(141,[]),
    (131,[]),(195,[]),(187,[]),(131,[]),(5,[2,3,26681]),
    (151,[]),(131,[]),(145,[]),(139,[]),(131,[]),
    (141,[]),(5,[2,73,1097]),(131,[]),(47,[2,3,3,11,809]),(169,[]),
    (131,[]),(5,[2,3,26701]),(135,[]),(131,[]),(21,[2,3,17,1571]),
    (165,[]),(131,[]),(267,[]),(157,[]),(131,[]),
    (139,[]),(135,[]),(131,[]),(145,[]),(14,[2,7,13,881]),
    (131,[]),(135,[]),(10,[2,181,443]),(131,[]),(2,[2,3,26731]),
    (5,[2,11,23,317]),(131,[]),(6,[2,3,26737]),(265,[]),(131,[]),
    (135,[]),(145,[]),(131,[]),(12,[2,3,7,3821]),(159,[]),
    (131,[]),(17,[2,3,3,37,241]),(139,[]),(131,[]),(165,[]),
    (309,[]),(131,[]),(139,[]),(10,[2,17,4723]),(131,[]),
    (66,[2,3,13,29,71]),(147,[]),(131,[]),(2,[2,3,19,1409]),(135,[]),
    (131,[]),(5,[2,3,26777]),(141,[]),(131,[]),(6,[2,3,3,79,113]),
    (399,[]),(131,[]),(2,[2,3,3,8929]),(135,[]),(131,[]),
    (151,[]),(501,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(11,[2,3,26801]),(141,[]),(131,[]),(169,[]),
    (367,[]),(131,[]),(135,[]),(5,[2,257,313]),(131,[]),
    (40,[2,3,3,7,1277]),(5,[2,43,1871]),(131,[]),(141,[]),(355,[]),
    (131,[]),(139,[]),(10,[2,13,41,151]),(131,[]),(147,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock161 : ∃ data, checkBlock 161 data = true :=
  ⟨[(361,[]),(131,[]),(151,[]),(411,[]),(131,[]),
    (5,[2,3,3,23,389]),(135,[]),(131,[]),(141,[]),(10,[2,239,337]),
    (131,[]),(159,[]),(7,[2,13,6197]),(131,[]),(145,[]),
    (135,[]),(131,[]),(12,[2,3,26861]),(139,[]),(131,[]),
    (135,[]),(151,[]),(131,[]),(139,[]),(511,[]),
    (131,[]),(5,[2,3,3,17,17,31]),(5,[2,7,11519]),(131,[]),(135,[]),
    (14,[2,80651]),(131,[]),(12,[2,3,7,23,167]),(157,[]),(131,[]),
    (145,[]),(5,[2,80681]),(131,[]),(199,[]),(5,[2,19,31,137]),
    (131,[]),(6,[2,3,3,3,7,7,61]),(465,[]),(131,[]),(147,[]),
    (139,[]),(131,[]),(189,[]),(135,[]),(131,[]),
    (10,[2,3,11,2447]),(13,[2,23,3511]),(131,[]),(5,[2,3,26921]),(13,[2,37,37,59]),
    (131,[]),(2,[2,3,26927]),(135,[]),(131,[]),(477,[]),
    (141,[]),(131,[]),(135,[]),(5,[2,211,383]),(131,[]),
    (237,[]),(169,[]),(131,[]),(29,[2,3,26947]),(145,[]),
    (131,[]),(135,[]),(171,[]),(131,[]),(5,[2,3,7,3851]),
    (147,[]),(131,[]),(211,[]),(19,[2,23,3517]),(131,[]),
    (367,[]),(14,[2,17,4759]),(131,[]),(169,[]),(139,[]),
    (131,[]),(141,[]),(285,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(2,[2,3,26987]),(321,[]),(131,[]),
    (28,[2,3,3,3,2999]),(277,[]),(131,[]),(39,[2,3,3,8999]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock162 : ∃ data, checkBlock 162 data = true :=
  ⟨[(131,[]),(5,[2,3,13,31,67]),(157,[]),(131,[]),(135,[]),
    (259,[]),(131,[]),(171,[]),(237,[]),(131,[]),
    (175,[]),(139,[]),(131,[]),(135,[]),(10,[2,81071]),
    (131,[]),(145,[]),(385,[]),(131,[]),(207,[]),
    (147,[]),(131,[]),(159,[]),(141,[]),(131,[]),
    (217,[]),(29,[2,81131]),(131,[]),(139,[]),(10,[2,53,1531]),
    (131,[]),(229,[]),(135,[]),(131,[]),(19,[2,3,3,29,311]),
    (159,[]),(131,[]),(145,[]),(141,[]),(131,[]),
    (151,[]),(135,[]),(131,[]),(187,[]),(189,[]),
    (131,[]),(135,[]),(165,[]),(131,[]),(141,[]),
    (139,[]),(131,[]),(2,[2,3,3,9029]),(28,[2,7,13,19,47]),(131,[]),
    (135,[]),(5,[2,81281]),(131,[]),(147,[]),(151,[]),
    (131,[]),(241,[]),(30,[2,17,4783]),(131,[]),(141,[]),
    (169,[]),(131,[]),(175,[]),(5,[2,13,6257]),(131,[]),
    (6,[2,3,3,3,23,131]),(145,[]),(131,[]),(5,[2,3,37,733]),(135,[]),
    (131,[]),(165,[]),(139,[]),(131,[]),(17,[2,3,13,2087]),
    (199,[]),(131,[]),(12,[2,3,11,2467]),(135,[]),(131,[]),
    (11,[2,3,3,83,109]),(151,[]),(131,[]),(135,[]),(147,[]),
    (131,[]),(2,[2,3,19,1429]),(319,[]),(131,[]),(139,[]),
    (7,[2,7,103,113]),(131,[]),(135,[]),(477,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock163 : ∃ data, checkBlock 163 data = true :=
  ⟨[(11,[2,3,7,3881]),(141,[]),(131,[]),(2,[2,3,3,3,3019]),(175,[]),
    (131,[]),(5,[2,3,3,9059]),(157,[]),(131,[]),(199,[]),
    (339,[]),(131,[]),(285,[]),(29,[2,81563]),(131,[]),
    (2,[2,3,27191]),(135,[]),(131,[]),(145,[]),(181,[]),
    (131,[]),(139,[]),(10,[2,81611]),(131,[]),(11,[2,3,3,3,3023]),
    (135,[]),(131,[]),(141,[]),(397,[]),(131,[]),
    (135,[]),(5,[2,11,13,571]),(131,[]),(5,[2,3,163,167]),(147,[]),
    (131,[]),(2,[2,3,19,1433]),(14,[2,7,7,1667]),(131,[]),(135,[]),
    (5,[2,81701]),(131,[]),(141,[]),(139,[]),(131,[]),
    (201,[]),(159,[]),(131,[]),(11,[2,3,11,2477]),(10,[2,43,1901]),
    (131,[]),(151,[]),(145,[]),(131,[]),(6,[2,3,97,281]),
    (195,[]),(131,[]),(68,[2,3,3,3,13,233]),(135,[]),(131,[]),
    (139,[]),(175,[]),(131,[]),(2,[2,3,27271]),(5,[2,17,4813]),
    (131,[]),(189,[]),(135,[]),(131,[]),(319,[]),
    (255,[]),(131,[]),(135,[]),(145,[]),(131,[]),
    (501,[]),(157,[]),(131,[]),(151,[]),(141,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(187,[]),
    (29,[2,17,61,79]),(131,[]),(139,[]),(5,[2,67,1223]),(131,[]),
    (379,[]),(189,[]),(131,[]),(5,[2,3,3,7,1301]),(141,[]),
    (131,[]),(241,[]),(151,[]),(131,[]),(2,[2,3,151,181])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock164 : ∃ data, checkBlock 164 data = true :=
  ⟨[(135,[]),(131,[]),(20,[2,3,27337]),(147,[]),(131,[]),
    (141,[]),(487,[]),(131,[]),(159,[]),(135,[]),
    (131,[]),(507,[]),(169,[]),(131,[]),(135,[]),
    (5,[2,82073]),(131,[]),(309,[]),(19,[2,103,797]),(131,[]),
    (141,[]),(159,[]),(131,[]),(135,[]),(151,[]),
    (131,[]),(139,[]),(5,[2,23,3571]),(131,[]),(169,[]),
    (171,[]),(131,[]),(201,[]),(229,[]),(131,[]),
    (277,[]),(14,[2,11,31,241]),(131,[]),(217,[]),(5,[2,82193]),
    (131,[]),(145,[]),(135,[]),(131,[]),(2,[2,3,27407]),
    (29,[2,82223]),(131,[]),(291,[]),(139,[]),(131,[]),
    (11,[2,3,3,13,19,37]),(135,[]),(131,[]),(139,[]),(145,[]),
    (131,[]),(135,[]),(141,[]),(131,[]),(2,[2,3,27431]),
    (369,[]),(131,[]),(5,[2,3,27437]),(5,[2,7,11,1069]),(131,[]),
    (135,[]),(10,[2,17,29,167]),(131,[]),(29,[2,3,3,7,1307]),(165,[]),
    (131,[]),(30,[2,3,97,283]),(141,[]),(131,[]),(5,[2,3,27457]),
    (139,[]),(131,[]),(12,[2,3,7,3923]),(495,[]),(131,[]),
    (225,[]),(157,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(147,[]),(241,[]),(131,[]),(151,[]),
    (231,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (409,[]),(5,[2,7,11783]),(131,[]),(135,[]),(5,[2,82493])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock165 : ∃ data, checkBlock 165 data = true :=
  ⟨[(131,[]),(285,[]),(187,[]),(131,[]),(279,[]),
    (10,[2,7,11789]),(131,[]),(135,[]),(5,[2,59,1399]),(131,[]),
    (5,[2,3,7,3931]),(169,[]),(131,[]),(189,[]),(139,[]),
    (131,[]),(151,[]),(147,[]),(131,[]),(139,[]),
    (5,[2,82601]),(131,[]),(145,[]),(255,[]),(131,[]),
    (5,[2,3,27541]),(135,[]),(131,[]),(325,[]),(10,[2,11,11,683]),
    (131,[]),(181,[]),(159,[]),(131,[]),(19,[2,3,17,1621]),
    (135,[]),(131,[]),(5,[2,3,3,9187]),(10,[2,7,11813]),(131,[]),
    (135,[]),(139,[]),(131,[]),(145,[]),(5,[2,82721]),
    (131,[]),(22,[2,3,11,23,109]),(465,[]),(131,[]),(135,[]),
    (141,[]),(131,[]),(12,[2,3,7,7,563]),(30,[2,82763]),(131,[]),
    (147,[]),(145,[]),(131,[]),(139,[]),(5,[2,82793]),
    (131,[]),(141,[]),(147,[]),(131,[]),(199,[]),
    (279,[]),(131,[]),(12,[2,3,27611]),(135,[]),(131,[]),
    (12,[2,3,27617]),(5,[2,29,2857]),(131,[]),(231,[]),(235,[]),
    (131,[]),(141,[]),(135,[]),(131,[]),(321,[]),
    (139,[]),(131,[]),(135,[]),(267,[]),(131,[]),
    (139,[]),(175,[]),(131,[]),(11,[2,3,27647]),(13,[2,7,17,17,41]),
    (131,[]),(135,[]),(405,[]),(131,[]),(159,[]),
    (13,[2,11,19,397]),(131,[]),(157,[]),(10,[2,37,2243]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock166 : ∃ data, checkBlock 166 data = true :=
  ⟨[(147,[]),(237,[]),(131,[]),(2,[2,3,7,59,67]),(5,[2,61,1361]),
    (131,[]),(23,[2,3,13,2129]),(139,[]),(131,[]),(435,[]),
    (135,[]),(131,[]),(399,[]),(141,[]),(131,[]),
    (11,[2,3,27691]),(217,[]),(131,[]),(19,[2,3,27697]),(135,[]),
    (131,[]),(5,[2,3,27701]),(241,[]),(131,[]),(135,[]),
    (10,[2,101,823]),(131,[]),(151,[]),(141,[]),(131,[]),
    (28,[2,3,3,9239]),(147,[]),(131,[]),(135,[]),(525,[]),
    (131,[]),(22,[2,3,7,17,233]),(171,[]),(131,[]),(141,[]),
    (14,[2,19,29,151]),(131,[]),(291,[]),(175,[]),(131,[]),
    (145,[]),(139,[]),(131,[]),(357,[]),(19,[2,83243]),
    (131,[]),(139,[]),(135,[]),(131,[]),(141,[]),
    (157,[]),(131,[]),(6,[2,3,17,23,71]),(145,[]),(131,[]),
    (17,[2,3,27767]),(135,[]),(131,[]),(2,[2,3,3,9257]),(7,[2,7,11903]),
    (131,[]),(135,[]),(5,[2,167,499]),(131,[]),(147,[]),
    (10,[2,17,4903]),(131,[]),(2,[2,3,37,751]),(139,[]),(131,[]),
    (135,[]),(147,[]),(131,[]),(10,[2,3,7,11,19,19]),(145,[]),
    (131,[]),(5,[2,3,3,3,3089]),(29,[2,239,349]),(131,[]),(2,[2,3,3,13,23,31]),
    (13,[2,83423]),(131,[]),(2,[2,3,7,29,137]),(171,[]),(131,[]),
    (139,[]),(141,[]),(131,[]),(207,[]),(135,[]),
    (131,[]),(231,[]),(10,[2,31,2693]),(131,[]),(12,[2,3,3,9277])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock167 : ∃ data, checkBlock 167 data = true :=
  ⟨[(151,[]),(131,[]),(39,[2,3,3,3,3,1031]),(135,[]),(131,[]),
    (5,[2,3,11,2531]),(141,[]),(131,[]),(135,[]),(13,[2,19,4397]),
    (131,[]),(56,[2,3,27851]),(139,[]),(131,[]),(147,[]),
    (187,[]),(131,[]),(135,[]),(159,[]),(131,[]),
    (165,[]),(399,[]),(131,[]),(171,[]),(157,[]),
    (131,[]),(145,[]),(5,[2,11,7603]),(131,[]),(259,[]),
    (421,[]),(131,[]),(141,[]),(277,[]),(131,[]),
    (199,[]),(135,[]),(131,[]),(187,[]),(139,[]),
    (131,[]),(5,[2,3,27901]),(10,[2,97,863]),(131,[]),(2,[2,3,11,43,59]),
    (135,[]),(131,[]),(145,[]),(5,[2,7,7,1709]),(131,[]),
    (135,[]),(319,[]),(131,[]),(361,[]),(19,[2,19,4409]),
    (131,[]),(139,[]),(169,[]),(131,[]),(135,[]),
    (145,[]),(131,[]),(10,[2,3,7,13,307]),(5,[2,83813]),(131,[]),
    (151,[]),(10,[2,11,7621]),(131,[]),(2,[2,3,27947]),(141,[]),
    (131,[]),(157,[]),(307,[]),(131,[]),(171,[]),
    (5,[2,83873]),(131,[]),(255,[]),(135,[]),(131,[]),
    (159,[]),(145,[]),(131,[]),(139,[]),(141,[]),
    (131,[]),(5,[2,3,101,277]),(135,[]),(131,[]),(11,[2,3,3,3,3109]),
    (147,[]),(131,[]),(135,[]),(159,[]),(131,[]),
    (141,[]),(229,[]),(131,[]),(301,[]),(5,[2,7,13,13,71])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock168 : ∃ data, checkBlock 168 data = true :=
  ⟨[(131,[]),(135,[]),(10,[2,84011]),(131,[]),(2,[2,3,7,4001]),
    (139,[]),(131,[]),(11,[2,3,3,9337]),(5,[2,31,2711]),(131,[]),
    (141,[]),(151,[]),(131,[]),(6,[2,3,7,4003]),(46,[2,13,29,223]),
    (131,[]),(465,[]),(339,[]),(131,[]),(237,[]),
    (135,[]),(131,[]),(139,[]),(5,[2,19,19,233]),(131,[]),
    (40,[2,3,3,13,719]),(14,[2,84131]),(131,[]),(145,[]),(135,[]),
    (131,[]),(175,[]),(5,[2,7,11,1093]),(131,[]),(135,[]),
    (5,[2,41,2053]),(131,[]),(229,[]),(151,[]),(131,[]),
    (157,[]),(211,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(11,[2,3,3,7,7,191]),(141,[]),(131,[]),(139,[]),
    (295,[]),(131,[]),(11,[2,3,28087]),(13,[2,84263]),(131,[]),
    (159,[]),(187,[]),(131,[]),(391,[]),(147,[]),
    (131,[]),(267,[]),(135,[]),(131,[]),(2,[2,3,3,3,3,3,347]),
    (265,[]),(131,[]),(279,[]),(165,[]),(131,[]),
    (201,[]),(135,[]),(131,[]),(141,[]),(10,[2,7,17,709]),
    (131,[]),(135,[]),(199,[]),(131,[]),(189,[]),
    (5,[2,84401]),(131,[]),(207,[]),(145,[]),(131,[]),
    (135,[]),(13,[2,84431]),(131,[]),(139,[]),(10,[2,84443]),
    (131,[]),(195,[]),(379,[]),(131,[]),(5,[2,3,37,761]),
    (171,[]),(131,[]),(147,[]),(157,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock169 : ∃ data, checkBlock 169 data = true :=
  ⟨[(17,[2,3,3,41,229]),(10,[2,84503]),(131,[]),(151,[]),(135,[]),
    (131,[]),(5,[2,3,19,1483]),(5,[2,84533]),(131,[]),(481,[]),
    (139,[]),(131,[]),(181,[]),(135,[]),(131,[]),
    (139,[]),(267,[]),(131,[]),(135,[]),(495,[]),
    (131,[]),(169,[]),(325,[]),(131,[]),(2,[2,3,67,421]),
    (141,[]),(131,[]),(135,[]),(5,[2,53,1597]),(131,[]),
    (145,[]),(5,[2,84653]),(131,[]),(22,[2,3,3,23,409]),(10,[2,227,373]),
    (131,[]),(385,[]),(139,[]),(131,[]),(241,[]),
    (141,[]),(131,[]),(147,[]),(5,[2,84713]),(131,[]),
    (157,[]),(135,[]),(131,[]),(12,[2,3,47,601]),(151,[]),
    (131,[]),(141,[]),(5,[2,84761]),(131,[]),(139,[]),
    (135,[]),(131,[]),(12,[2,3,59,479]),(13,[2,7,12113]),(131,[]),
    (135,[]),(10,[2,137,619]),(131,[]),(2,[2,3,17,1663]),(145,[]),
    (131,[]),(141,[]),(7,[2,7,12119]),(131,[]),(135,[]),
    (351,[]),(131,[]),(217,[]),(147,[]),(131,[]),
    (327,[]),(139,[]),(131,[]),(5,[2,3,28297]),(159,[]),
    (131,[]),(139,[]),(10,[2,19,41,109]),(131,[]),(2,[2,3,28307]),
    (145,[]),(131,[]),(165,[]),(135,[]),(131,[]),
    (199,[]),(259,[]),(131,[]),(379,[]),(13,[2,31,2741]),
    (131,[]),(477,[]),(135,[]),(131,[]),(20,[2,3,41,691])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock170 : ∃ data, checkBlock 170 data = true :=
  ⟨[(5,[2,7,12143]),(131,[]),(135,[]),(139,[]),(131,[]),
    (5,[2,3,3,3,47,67]),(22,[2,23,3697]),(131,[]),(411,[]),(207,[]),
    (131,[]),(135,[]),(5,[2,85061]),(131,[]),(157,[]),
    (357,[]),(131,[]),(5,[2,3,79,359]),(141,[]),(131,[]),
    (139,[]),(10,[2,85103]),(131,[]),(19,[2,3,3,7,7,193]),(5,[2,85121]),
    (131,[]),(10,[2,3,3,3,3,1051]),(5,[2,85133]),(131,[]),(141,[]),
    (135,[]),(131,[]),(145,[]),(19,[2,13,6551]),(131,[]),
    (11,[2,3,11,29,89]),(5,[2,103,827]),(131,[]),(20,[2,3,73,389]),(135,[]),
    (131,[]),(151,[]),(139,[]),(131,[]),(135,[]),
    (14,[2,85223]),(131,[]),(139,[]),(5,[2,13,79,83]),(131,[]),
    (5,[2,3,157,181]),(295,[]),(131,[]),(135,[]),(327,[]),
    (131,[]),(147,[]),(409,[]),(131,[]),(307,[]),
    (5,[2,197,433]),(131,[]),(225,[]),(5,[2,85313]),(131,[]),
    (6,[2,3,7,17,239]),(145,[]),(131,[]),(151,[]),(139,[]),
    (131,[]),(17,[2,3,23,1237]),(135,[]),(131,[]),(241,[]),
    (201,[]),(131,[]),(6,[2,3,3,53,179]),(195,[]),(131,[]),
    (237,[]),(135,[]),(131,[]),(2,[2,3,71,401]),(5,[2,7,12203]),
    (131,[]),(135,[]),(145,[]),(131,[]),(5,[2,3,19,1499]),
    (159,[]),(131,[]),(187,[]),(10,[2,7,29,421]),(131,[]),
    (135,[]),(141,[]),(131,[]),(189,[]),(291,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock171 : ∃ data, checkBlock 171 data = true :=
  ⟨[(131,[]),(6,[2,3,11,2591]),(19,[2,233,367]),(131,[]),(11,[2,3,29,983]),
    (13,[2,85523]),(131,[]),(141,[]),(139,[]),(131,[]),
    (5,[2,3,28517]),(525,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(2,[2,3,3,37,257]),(30,[2,23,61,61]),(131,[]),(157,[]),
    (5,[2,85601]),(131,[]),(141,[]),(135,[]),(131,[]),
    (147,[]),(14,[2,7,13,941]),(131,[]),(135,[]),(285,[]),
    (131,[]),(235,[]),(147,[]),(131,[]),(145,[]),
    (139,[]),(131,[]),(135,[]),(10,[2,85691]),(131,[]),
    (51,[2,3,7,7,11,53]),(309,[]),(131,[]),(2,[2,3,28571]),(301,[]),
    (131,[]),(405,[]),(5,[2,85733]),(131,[]),(351,[]),
    (169,[]),(131,[]),(139,[]),(171,[]),(131,[]),
    (145,[]),(135,[]),(131,[]),(5,[2,3,28597]),(141,[]),
    (131,[]),(199,[]),(201,[]),(131,[]),(165,[]),
    (135,[]),(131,[]),(169,[]),(145,[]),(131,[]),
    (135,[]),(5,[2,85853]),(131,[]),(211,[]),(139,[]),
    (131,[]),(2,[2,3,28627]),(157,[]),(131,[]),(135,[]),
    (5,[2,17,31,163]),(131,[]),(13,[2,3,7,4091]),(5,[2,53,1621]),(131,[]),
    (141,[]),(34,[2,85931]),(131,[]),(157,[]),(145,[]),
    (131,[]),(231,[]),(5,[2,67,1283]),(131,[]),(267,[]),
    (5,[2,149,577]),(131,[]),(511,[]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock172 : ∃ data, checkBlock 172 data = true :=
  ⟨[(141,[]),(139,[]),(131,[]),(11,[2,3,3,19,503]),(171,[]),
    (131,[]),(151,[]),(135,[]),(131,[]),(165,[]),
    (187,[]),(131,[]),(135,[]),(13,[2,89,967]),(131,[]),
    (2,[2,3,13,2207]),(235,[]),(131,[]),(139,[]),(361,[]),
    (131,[]),(135,[]),(14,[2,86111]),(131,[]),(2,[2,3,3,7,1367]),
    (151,[]),(131,[]),(159,[]),(5,[2,11,41,191]),(131,[]),
    (181,[]),(5,[2,101,853]),(131,[]),(517,[]),(30,[2,86171]),
    (131,[]),(145,[]),(141,[]),(131,[]),(147,[]),
    (135,[]),(131,[]),(11,[2,3,3,3,31,103]),(5,[2,73,1181]),(131,[]),
    (139,[]),(147,[]),(131,[]),(265,[]),(135,[]),
    (131,[]),(2,[2,3,28751]),(141,[]),(131,[]),(135,[]),
    (237,[]),(131,[]),(145,[]),(10,[2,86291]),(131,[]),
    (18,[2,3,3,43,223]),(13,[2,7,12329]),(131,[]),(135,[]),(5,[2,37,2333]),
    (131,[]),(6,[2,3,7,4111]),(139,[]),(131,[]),(5,[2,3,17,1693]),
    (145,[]),(131,[]),(211,[]),(181,[]),(131,[]),
    (355,[]),(159,[]),(131,[]),(141,[]),(5,[2,19,4547]),
    (131,[]),(45,[2,3,83,347]),(135,[]),(131,[]),(139,[]),
    (255,[]),(131,[]),(12,[2,3,47,613]),(5,[2,86441]),(131,[]),
    (171,[]),(135,[]),(131,[]),(157,[]),(291,[]),
    (131,[]),(135,[]),(397,[]),(131,[]),(20,[2,3,11,2621])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock173 : ∃ data, checkBlock 173 data = true :=
  ⟨[(241,[]),(131,[]),(5,[2,3,28837]),(199,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(201,[]),(19,[2,37,2339]),
    (131,[]),(139,[]),(165,[]),(131,[]),(169,[]),
    (141,[]),(131,[]),(151,[]),(19,[2,131,661]),(131,[]),
    (507,[]),(10,[2,11,7873]),(131,[]),(439,[]),(135,[]),
    (131,[]),(5,[2,3,67,431]),(5,[2,41,2113]),(131,[]),(277,[]),
    (141,[]),(131,[]),(481,[]),(135,[]),(131,[]),
    (29,[2,3,167,173]),(181,[]),(131,[]),(135,[]),(211,[]),
    (131,[]),(141,[]),(189,[]),(131,[]),(151,[]),
    (235,[]),(131,[]),(135,[]),(5,[2,127,683]),(131,[]),
    (139,[]),(157,[]),(131,[]),(147,[]),(19,[2,86771]),
    (131,[]),(141,[]),(165,[]),(131,[]),(145,[]),
    (147,[]),(131,[]),(157,[]),(151,[]),(131,[]),
    (11,[2,3,3,11,877]),(135,[]),(131,[]),(2,[2,3,3,9649]),(30,[2,86843]),
    (131,[]),(2,[2,3,13,17,131]),(139,[]),(131,[]),(5,[2,3,23,1259]),
    (135,[]),(131,[]),(139,[]),(10,[2,7,12413]),(131,[]),
    (135,[]),(14,[2,43,43,47]),(131,[]),(30,[2,3,3,3,3,29,37]),(391,[]),
    (131,[]),(165,[]),(5,[2,7,11,1129]),(131,[]),(135,[]),
    (151,[]),(131,[]),(2,[2,3,7,41,101]),(141,[]),(131,[]),
    (175,[]),(169,[]),(131,[]),(147,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock174 : ∃ data, checkBlock 174 data = true :=
  ⟨[(131,[]),(5,[2,3,3,7,1381]),(229,[]),(131,[]),(397,[]),
    (10,[2,17,5119]),(131,[]),(2,[2,3,67,433]),(135,[]),(131,[]),
    (279,[]),(171,[]),(131,[]),(159,[]),(13,[2,87071]),
    (131,[]),(139,[]),(135,[]),(131,[]),(141,[]),
    (157,[]),(131,[]),(135,[]),(187,[]),(131,[]),
    (291,[]),(10,[2,11,89,89]),(131,[]),(525,[]),(147,[]),
    (131,[]),(135,[]),(175,[]),(131,[]),(141,[]),
    (5,[2,179,487]),(131,[]),(6,[2,3,3,3,3229]),(139,[]),(131,[]),
    (145,[]),(20,[2,29,31,97]),(131,[]),(139,[]),(5,[2,87221]),
    (131,[]),(187,[]),(5,[2,83,1051]),(131,[]),(20,[2,3,13,2237]),
    (135,[]),(131,[]),(327,[]),(10,[2,11,7933]),(131,[]),
    (151,[]),(355,[]),(131,[]),(5,[2,3,3,3,53,61]),(135,[]),
    (131,[]),(145,[]),(159,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(147,[]),(435,[]),(131,[]),
    (22,[2,3,11,2647]),(141,[]),(131,[]),(135,[]),(145,[]),
    (131,[]),(22,[2,3,3,7,19,73]),(19,[2,87383]),(131,[]),(405,[]),
    (195,[]),(131,[]),(139,[]),(207,[]),(131,[]),
    (181,[]),(141,[]),(131,[]),(307,[]),(175,[]),
    (131,[]),(12,[2,3,3,3,41,79]),(135,[]),(131,[]),(5,[2,3,3,9719]),
    (145,[]),(131,[]),(141,[]),(361,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock175 : ∃ data, checkBlock 175 data = true :=
  ⟨[(11,[2,3,29167]),(135,[]),(131,[]),(309,[]),(139,[]),
    (131,[]),(135,[]),(5,[2,17,19,271]),(131,[]),(139,[]),
    (10,[2,29,3019]),(131,[]),(141,[]),(201,[]),(131,[]),
    (135,[]),(237,[]),(131,[]),(295,[]),(367,[]),
    (131,[]),(369,[]),(265,[]),(131,[]),(159,[]),
    (157,[]),(131,[]),(2,[2,3,3,7,13,107]),(151,[]),(131,[]),
    (5,[2,3,3,9739]),(139,[]),(131,[]),(20,[2,3,29221]),(135,[]),
    (131,[]),(157,[]),(159,[]),(131,[]),(255,[]),
    (5,[2,87701]),(131,[]),(145,[]),(135,[]),(131,[]),
    (20,[2,3,3,3,3,3,19,19]),(13,[2,7,83,151]),(131,[]),(135,[]),(141,[]),
    (131,[]),(421,[]),(5,[2,19,31,149]),(131,[]),(5,[2,3,17,1721]),
    (477,[]),(131,[]),(135,[]),(199,[]),(131,[]),
    (169,[]),(195,[]),(131,[]),(145,[]),(141,[]),
    (131,[]),(10,[2,3,3,3,3253]),(225,[]),(131,[]),(6,[2,3,7,47,89]),
    (139,[]),(131,[]),(2,[2,3,29287]),(30,[2,41,2143]),(131,[]),
    (139,[]),(135,[]),(131,[]),(5,[2,3,29297]),(165,[]),
    (131,[]),(147,[]),(321,[]),(131,[]),(2,[2,3,3,9769]),
    (135,[]),(131,[]),(199,[]),(147,[]),(131,[]),
    (135,[]),(181,[]),(131,[]),(151,[]),(157,[]),
    (131,[]),(18,[2,3,29327]),(139,[]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock176 : ∃ data, checkBlock 176 data = true :=
  ⟨[(201,[]),(131,[]),(10,[2,3,3,7,11,127]),(231,[]),(131,[]),
    (5,[2,3,13,37,61]),(19,[2,47,1873]),(131,[]),(165,[]),(13,[2,17,5179]),
    (131,[]),(189,[]),(5,[2,107,823]),(131,[]),(139,[]),
    (481,[]),(131,[]),(241,[]),(135,[]),(131,[]),
    (151,[]),(10,[2,19,4637]),(131,[]),(2,[2,3,23,1277]),(5,[2,11,8011]),
    (131,[]),(147,[]),(135,[]),(131,[]),(301,[]),
    (29,[2,7,7,7,257]),(131,[]),(135,[]),(13,[2,131,673]),(131,[]),
    (12,[2,3,3,97,101]),(139,[]),(131,[]),(5,[2,3,3,41,239]),(151,[]),
    (131,[]),(135,[]),(141,[]),(131,[]),(145,[]),
    (229,[]),(131,[]),(12,[2,3,29411]),(159,[]),(131,[]),
    (20,[2,3,23,1279]),(5,[2,11,71,113]),(131,[]),(141,[]),(181,[]),
    (131,[]),(511,[]),(147,[]),(131,[]),(169,[]),
    (135,[]),(131,[]),(475,[]),(139,[]),(131,[]),
    (145,[]),(151,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(211,[]),(207,[]),(131,[]),(135,[]),
    (5,[2,67,1319]),(131,[]),(175,[]),(145,[]),(131,[]),
    (139,[]),(10,[2,7,73,173]),(131,[]),(135,[]),(217,[]),
    (131,[]),(277,[]),(265,[]),(131,[]),(38,[2,3,3,31,317]),
    (29,[2,11,11,17,43]),(131,[]),(12,[2,3,3,9829]),(10,[2,88463]),(131,[]),
    (147,[]),(399,[]),(131,[]),(47,[2,3,13,2269]),(145,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock177 : ∃ data, checkBlock 177 data = true :=
  ⟨[(131,[]),(5,[2,3,29501]),(135,[]),(131,[]),(2,[2,3,19,1553]),
    (141,[]),(131,[]),(139,[]),(189,[]),(131,[]),
    (157,[]),(135,[]),(131,[]),(5,[2,3,53,557]),(175,[]),
    (131,[]),(135,[]),(10,[2,11,8053]),(131,[]),(295,[]),
    (141,[]),(131,[]),(13,[2,3,29537]),(159,[]),(131,[]),
    (135,[]),(231,[]),(131,[]),(12,[2,3,3,3,7,7,67]),(139,[]),
    (131,[]),(141,[]),(5,[2,88661]),(131,[]),(237,[]),
    (7,[2,13,19,359]),(131,[]),(321,[]),(34,[2,31,2861]),(131,[]),
    (147,[]),(169,[]),(131,[]),(2,[2,3,3,9857]),(135,[]),
    (131,[]),(139,[]),(5,[2,89,997]),(131,[]),(5,[2,3,29581]),
    (267,[]),(131,[]),(241,[]),(135,[]),(131,[]),
    (171,[]),(165,[]),(131,[]),(135,[]),(385,[]),
    (131,[]),(225,[]),(19,[2,88811]),(131,[]),(529,[]),
    (13,[2,7,12689]),(131,[]),(135,[]),(139,[]),(131,[]),
    (211,[]),(147,[]),(131,[]),(139,[]),(10,[2,181,491]),
    (131,[]),(11,[2,3,13,43,53]),(151,[]),(131,[]),(65,[2,3,3,7,17,83]),
    (145,[]),(131,[]),(33,[2,3,3,3,37,89]),(141,[]),(131,[]),
    (159,[]),(135,[]),(131,[]),(18,[2,3,23,1289]),(19,[2,29,3067]),
    (131,[]),(2,[2,3,149,199]),(309,[]),(131,[]),(5,[2,3,47,631]),
    (135,[]),(131,[]),(21,[2,3,3,9887]),(141,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock178 : ∃ data, checkBlock 178 data = true :=
  ⟨[(135,[]),(145,[]),(131,[]),(181,[]),(151,[]),
    (131,[]),(169,[]),(22,[2,7,7,23,79]),(131,[]),(135,[]),
    (14,[2,89051]),(131,[]),(139,[]),(10,[2,13,13,17,31]),(131,[]),
    (157,[]),(147,[]),(131,[]),(5,[2,3,3,19,521]),(5,[2,41,41,53]),
    (131,[]),(23,[2,3,7,4243]),(10,[2,11,8101]),(131,[]),(141,[]),
    (10,[2,89123]),(131,[]),(217,[]),(135,[]),(131,[]),
    (165,[]),(5,[2,89153]),(131,[]),(13,[2,3,3,9907]),(139,[]),
    (131,[]),(301,[]),(135,[]),(131,[]),(139,[]),
    (5,[2,7,12743]),(131,[]),(135,[]),(241,[]),(131,[]),
    (10,[2,3,29741]),(307,[]),(131,[]),(145,[]),(19,[2,7,11,19,61]),
    (131,[]),(135,[]),(295,[]),(131,[]),(147,[]),
    (189,[]),(131,[]),(6,[2,3,29761]),(235,[]),(131,[]),
    (29,[2,3,17,17,103]),(139,[]),(131,[]),(47,[2,3,7,4253]),(5,[2,179,499]),
    (131,[]),(181,[]),(501,[]),(131,[]),(145,[]),
    (135,[]),(131,[]),(441,[]),(157,[]),(131,[]),
    (165,[]),(141,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(5,[2,3,17,1753]),(145,[]),(131,[]),(135,[]),
    (147,[]),(131,[]),(141,[]),(169,[]),(131,[]),
    (5,[2,3,3,3,3313]),(5,[2,7,13,983]),(131,[]),(135,[]),(255,[]),
    (131,[]),(151,[]),(319,[]),(131,[]),(22,[2,3,23,1297])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock179 : ∃ data, checkBlock 179 data = true :=
  ⟨[(139,[]),(131,[]),(141,[]),(145,[]),(131,[]),
    (139,[]),(369,[]),(131,[]),(28,[2,3,3,9949]),(159,[]),
    (131,[]),(2,[2,3,29851]),(135,[]),(131,[]),(20,[2,3,73,409]),
    (151,[]),(131,[]),(53,[2,3,13,2297]),(187,[]),(131,[]),
    (17,[2,3,29867]),(135,[]),(131,[]),(147,[]),(5,[2,7,7,31,59]),
    (131,[]),(135,[]),(139,[]),(131,[]),(5,[2,3,29881]),
    (147,[]),(131,[]),(231,[]),(13,[2,7,12809]),(131,[]),
    (135,[]),(211,[]),(131,[]),(5,[2,3,7,4271]),(141,[]),
    (131,[]),(5,[2,3,3,9967]),(151,[]),(131,[]),(139,[]),
    (439,[]),(131,[]),(325,[]),(5,[2,43,2087]),(131,[]),
    (145,[]),(201,[]),(131,[]),(5,[2,3,29921]),(135,[]),
    (131,[]),(32,[2,3,29927]),(207,[]),(131,[]),(175,[]),
    (5,[2,89,1009]),(131,[]),(20,[2,3,3,17,587]),(135,[]),(131,[]),
    (141,[]),(139,[]),(131,[]),(135,[]),(14,[2,13,6911]),
    (131,[]),(139,[]),(181,[]),(131,[]),(5,[2,3,29,1033]),
    (301,[]),(131,[]),(135,[]),(165,[]),(131,[]),
    (141,[]),(10,[2,11,11,743]),(131,[]),(2,[2,3,17,41,43]),(145,[]),
    (131,[]),(259,[]),(169,[]),(131,[]),(157,[]),
    (10,[2,293,307]),(131,[]),(2,[2,3,157,191]),(139,[]),(131,[]),
    (19,[2,3,3,13,769]),(135,[]),(131,[]),(339,[]),(147,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock180 : ∃ data, checkBlock 180 data = true :=
  ⟨[(131,[]),(37,[2,3,19,1579]),(14,[2,90011]),(131,[]),(2,[2,3,37,811]),
    (135,[]),(131,[]),(151,[]),(229,[]),(131,[]),
    (135,[]),(517,[]),(131,[]),(171,[]),(279,[]),
    (131,[]),(195,[]),(141,[]),(131,[]),(135,[]),
    (159,[]),(131,[]),(357,[]),(165,[]),(131,[]),
    (5,[2,3,11,2731]),(34,[2,193,467]),(131,[]),(267,[]),(14,[2,109,827]),
    (131,[]),(2,[2,3,3,3,3,3,7,53]),(139,[]),(131,[]),(151,[]),
    (5,[2,90173]),(131,[]),(139,[]),(135,[]),(131,[]),
    (217,[]),(351,[]),(131,[]),(141,[]),(147,[]),
    (131,[]),(19,[2,3,19,1583]),(135,[]),(131,[]),(229,[]),
    (13,[2,7,12893]),(131,[]),(135,[]),(151,[]),(131,[]),
    (11,[2,3,30091]),(5,[2,90281]),(131,[]),(141,[]),(139,[]),
    (131,[]),(135,[]),(10,[2,13,6947]),(131,[]),(171,[]),
    (10,[2,41,2203]),(131,[]),(2,[2,3,3,10037]),(409,[]),(131,[]),
    (265,[]),(285,[]),(131,[]),(145,[]),(189,[]),
    (131,[]),(139,[]),(291,[]),(131,[]),(475,[]),
    (135,[]),(131,[]),(147,[]),(339,[]),(131,[]),
    (19,[2,3,3,3,17,197]),(145,[]),(131,[]),(2,[2,3,3,13,773]),(135,[]),
    (131,[]),(98,[2,3,11,2741]),(367,[]),(131,[]),(135,[]),
    (141,[]),(131,[]),(165,[]),(139,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock181 : ∃ data, checkBlock 181 data = true :=
  ⟨[(2,[2,3,97,311]),(445,[]),(131,[]),(135,[]),(325,[]),
    (131,[]),(5,[2,3,3,3,7,479]),(145,[]),(131,[]),(6,[2,3,30181]),
    (141,[]),(131,[]),(12,[2,3,30187]),(147,[]),(131,[]),
    (207,[]),(157,[]),(131,[]),(5,[2,3,30197]),(537,[]),
    (131,[]),(141,[]),(135,[]),(131,[]),(20,[2,3,3,10069]),
    (139,[]),(131,[]),(237,[]),(5,[2,90641]),(131,[]),
    (19,[2,3,11,41,67]),(135,[]),(131,[]),(307,[]),(169,[]),
    (131,[]),(135,[]),(421,[]),(131,[]),(2,[2,3,3,3,3359]),
    (411,[]),(131,[]),(139,[]),(547,[]),(131,[]),
    (135,[]),(207,[]),(131,[]),(255,[]),(225,[]),
    (131,[]),(147,[]),(14,[2,11,37,223]),(131,[]),(145,[]),
    (199,[]),(131,[]),(159,[]),(147,[]),(131,[]),
    (11,[2,3,3,3,3,19,59]),(19,[2,90803]),(131,[]),(157,[]),(135,[]),
    (131,[]),(517,[]),(5,[2,90833]),(131,[]),(139,[]),
    (237,[]),(131,[]),(151,[]),(135,[]),(131,[]),
    (145,[]),(5,[2,7,12983]),(131,[]),(135,[]),(20,[2,11,8263]),
    (131,[]),(409,[]),(301,[]),(131,[]),(175,[]),
    (171,[]),(131,[]),(135,[]),(141,[]),(131,[]),
    (5,[2,3,7,61,71]),(139,[]),(131,[]),(6,[2,3,3,3,3,1123]),(10,[2,90971]),
    (131,[]),(147,[]),(10,[2,37,2459]),(131,[]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock182 : ∃ data, checkBlock 182 data = true :=
  ⟨[(165,[]),(131,[]),(319,[]),(5,[2,13,7001]),(131,[]),
    (82,[2,3,30341]),(135,[]),(131,[]),(139,[]),(145,[]),
    (131,[]),(2,[2,3,3,67,151]),(5,[2,41,2221]),(131,[]),(141,[]),
    (135,[]),(131,[]),(12,[2,3,97,313]),(151,[]),(131,[]),
    (135,[]),(157,[]),(131,[]),(277,[]),(5,[2,91121]),
    (131,[]),(225,[]),(147,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(157,[]),(169,[]),(131,[]),
    (139,[]),(171,[]),(131,[]),(399,[]),(5,[2,91193]),
    (131,[]),(175,[]),(19,[2,197,463]),(131,[]),(19,[2,3,13,2339]),
    (165,[]),(131,[]),(2,[2,3,3,3,31,109]),(135,[]),(131,[]),
    (5,[2,3,3,10139]),(141,[]),(131,[]),(477,[]),(405,[]),
    (131,[]),(145,[]),(135,[]),(131,[]),(30,[2,3,30431]),
    (5,[2,7,13043]),(131,[]),(135,[]),(5,[2,127,719]),(131,[]),
    (147,[]),(141,[]),(131,[]),(159,[]),(13,[2,7,13049]),
    (131,[]),(135,[]),(147,[]),(131,[]),(139,[]),
    (5,[2,91373]),(131,[]),(141,[]),(175,[]),(131,[]),
    (11,[2,3,30467]),(159,[]),(131,[]),(151,[]),(195,[]),
    (131,[]),(235,[]),(5,[2,91433]),(131,[]),(5,[2,3,11,17,163]),
    (135,[]),(131,[]),(141,[]),(34,[2,91463]),(131,[]),
    (241,[]),(139,[]),(131,[]),(169,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock183 : ∃ data, checkBlock 183 data = true :=
  ⟨[(131,[]),(139,[]),(10,[2,7,17,769]),(131,[]),(135,[]),
    (13,[2,19,4817]),(131,[]),(45,[2,3,13,2347]),(351,[]),(131,[]),
    (147,[]),(145,[]),(131,[]),(135,[]),(501,[]),
    (131,[]),(279,[]),(19,[2,91583]),(131,[]),(165,[]),
    (5,[2,139,659]),(131,[]),(171,[]),(139,[]),(131,[]),
    (19,[2,3,7,4363]),(10,[2,91631]),(131,[]),(2,[2,3,11,2777]),(141,[]),
    (131,[]),(2,[2,3,137,223]),(135,[]),(131,[]),(5,[2,3,30557]),
    (175,[]),(131,[]),(157,[]),(13,[2,91691]),(131,[]),
    (139,[]),(135,[]),(131,[]),(159,[]),(141,[]),
    (131,[]),(135,[]),(399,[]),(131,[]),(5,[2,3,53,577]),
    (10,[2,11,19,439]),(131,[]),(2,[2,3,73,419]),(10,[2,7,13109]),(131,[]),
    (135,[]),(151,[]),(131,[]),(145,[]),(14,[2,13,23,307]),
    (131,[]),(217,[]),(139,[]),(131,[]),(355,[]),
    (195,[]),(131,[]),(139,[]),(5,[2,91841]),(131,[]),
    (141,[]),(5,[2,31,2963]),(131,[]),(397,[]),(135,[]),
    (131,[]),(2,[2,3,3,3,41,83]),(279,[]),(131,[]),(145,[]),
    (169,[]),(131,[]),(65,[2,3,30637]),(135,[]),(131,[]),
    (285,[]),(147,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(18,[2,3,3,17,601]),(145,[]),(131,[]),(11,[2,3,3,11,929]),
    (157,[]),(131,[]),(135,[]),(379,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock184 : ∃ data, checkBlock 184 data = true :=
  ⟨[(31,[2,3,7,13,337]),(19,[2,92003]),(131,[]),(291,[]),(5,[2,17,5413]),
    (131,[]),(139,[]),(141,[]),(131,[]),(5,[2,3,3,3,7,487]),
    (199,[]),(131,[]),(229,[]),(145,[]),(131,[]),
    (235,[]),(135,[]),(131,[]),(195,[]),(5,[2,19,37,131]),
    (131,[]),(151,[]),(141,[]),(131,[]),(147,[]),
    (135,[]),(131,[]),(231,[]),(139,[]),(131,[]),
    (135,[]),(207,[]),(131,[]),(139,[]),(211,[]),
    (131,[]),(391,[]),(459,[]),(131,[]),(135,[]),
    (189,[]),(131,[]),(439,[]),(171,[]),(131,[]),
    (39,[2,3,3,10247]),(10,[2,149,619]),(131,[]),(141,[]),(14,[2,92243]),
    (131,[]),(435,[]),(5,[2,13,47,151]),(131,[]),(159,[]),
    (139,[]),(131,[]),(11,[2,3,19,1619]),(135,[]),(131,[]),
    (145,[]),(10,[2,241,383]),(131,[]),(17,[2,3,3,3,13,263]),(157,[]),
    (131,[]),(175,[]),(135,[]),(131,[]),(5,[2,3,30781]),
    (19,[2,7,79,167]),(131,[]),(135,[]),(10,[2,92363]),(131,[]),
    (367,[]),(201,[]),(131,[]),(385,[]),(169,[]),
    (131,[]),(135,[]),(10,[2,11,31,271]),(131,[]),(19,[2,3,3,3,3,7,163]),
    (141,[]),(131,[]),(351,[]),(421,[]),(131,[]),
    (20,[2,3,30817]),(307,[]),(131,[]),(147,[]),(139,[]),
    (131,[]),(165,[]),(34,[2,23,4021]),(131,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock185 : ∃ data, checkBlock 185 data = true :=
  ⟨[(135,[]),(131,[]),(181,[]),(5,[2,71,1303]),(131,[]),
    (339,[]),(13,[2,17,5443]),(131,[]),(187,[]),(135,[]),
    (131,[]),(141,[]),(5,[2,7,7,1889]),(131,[]),(135,[]),
    (145,[]),(131,[]),(5,[2,3,3,3,3,3,3,127]),(10,[2,53,1747]),(131,[]),
    (295,[]),(139,[]),(131,[]),(135,[]),(6,[2,23,4027]),
    (131,[]),(141,[]),(5,[2,17,5449]),(131,[]),(159,[]),
    (30,[2,13,7127]),(131,[]),(2,[2,3,67,461]),(19,[2,19,4877]),(131,[]),
    (201,[]),(5,[2,92681]),(131,[]),(139,[]),(217,[]),
    (131,[]),(165,[]),(135,[]),(131,[]),(169,[]),
    (181,[]),(131,[]),(22,[2,3,30911]),(7,[2,11,8431]),(131,[]),
    (231,[]),(135,[]),(131,[]),(5,[2,3,3,11,937]),(20,[2,7,29,457]),
    (131,[]),(135,[]),(13,[2,31,41,73]),(131,[]),(151,[]),
    (139,[]),(131,[]),(145,[]),(141,[]),(131,[]),
    (135,[]),(529,[]),(131,[]),(37,[2,3,7,4421]),(147,[]),
    (131,[]),(11,[2,3,3,3,19,181]),(5,[2,92861]),(131,[]),(217,[]),
    (5,[2,11,8443]),(131,[]),(19,[2,3,7,4423]),(141,[]),(131,[]),
    (157,[]),(199,[]),(131,[]),(145,[]),(135,[]),
    (131,[]),(151,[]),(139,[]),(131,[]),(141,[]),
    (10,[2,92951]),(131,[]),(11,[2,3,3,3,11,313]),(135,[]),(131,[]),
    (11,[2,3,17,1823]),(145,[]),(131,[]),(135,[]),(5,[2,92993])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock186 : ∃ data, checkBlock 186 data = true :=
  ⟨[(131,[]),(5,[2,3,29,1069]),(29,[2,281,331]),(131,[]),(139,[]),
    (151,[]),(131,[]),(135,[]),(181,[]),(131,[]),
    (6,[2,3,3,7,7,211]),(5,[2,93053]),(131,[]),(501,[]),(147,[]),
    (131,[]),(2,[2,3,19,23,71]),(145,[]),(131,[]),(17,[2,3,7,11,13,31]),
    (207,[]),(131,[]),(201,[]),(5,[2,93113]),(131,[]),
    (5,[2,3,3,3,3449]),(135,[]),(131,[]),(11,[2,3,3,79,131]),(235,[]),
    (131,[]),(139,[]),(151,[]),(131,[]),(5,[2,3,13,2389]),
    (135,[]),(131,[]),(355,[]),(157,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(169,[]),(165,[]),
    (131,[]),(327,[]),(391,[]),(131,[]),(135,[]),
    (549,[]),(131,[]),(147,[]),(139,[]),(131,[]),
    (229,[]),(141,[]),(131,[]),(10,[2,3,11,11,257]),(5,[2,29,3217]),
    (131,[]),(319,[]),(559,[]),(131,[]),(145,[]),
    (29,[2,93323]),(131,[]),(141,[]),(135,[]),(131,[]),
    (139,[]),(5,[2,13,43,167]),(131,[]),(5,[2,3,31121]),(13,[2,93371]),
    (131,[]),(11,[2,3,17,1831]),(135,[]),(131,[]),(279,[]),
    (495,[]),(131,[]),(135,[]),(147,[]),(131,[]),
    (145,[]),(195,[]),(131,[]),(44,[2,3,31147]),(165,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(199,[]),
    (5,[2,211,443]),(131,[]),(139,[]),(145,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock187 : ∃ data, checkBlock 187 data = true :=
  ⟨[(11,[2,3,3,3,3463]),(171,[]),(131,[]),(17,[2,3,7,61,73]),(5,[2,41,2281]),
    (131,[]),(411,[]),(5,[2,11,11,773]),(131,[]),(189,[]),
    (135,[]),(131,[]),(2,[2,3,13,2399]),(29,[2,93563]),(131,[]),
    (159,[]),(5,[2,93581]),(131,[]),(165,[]),(135,[]),
    (131,[]),(147,[]),(10,[2,7,43,311]),(131,[]),(135,[]),
    (169,[]),(131,[]),(529,[]),(147,[]),(131,[]),
    (19,[2,3,19,31,53]),(225,[]),(131,[]),(135,[]),(141,[]),
    (131,[]),(139,[]),(10,[2,93683]),(131,[]),(2,[2,3,31231]),
    (321,[]),(131,[]),(5,[2,3,31237]),(151,[]),(131,[]),
    (141,[]),(10,[2,11,8521]),(131,[]),(175,[]),(441,[]),
    (131,[]),(11,[2,3,3,11,947]),(135,[]),(131,[]),(157,[]),
    (5,[2,79,1187]),(131,[]),(181,[]),(139,[]),(131,[]),
    (141,[]),(135,[]),(131,[]),(139,[]),(159,[]),
    (131,[]),(135,[]),(195,[]),(131,[]),(10,[2,3,3,10427]),
    (151,[]),(131,[]),(259,[]),(475,[]),(131,[]),
    (135,[]),(5,[2,269,349]),(131,[]),(207,[]),(5,[2,93893]),
    (131,[]),(237,[]),(10,[2,93911]),(131,[]),(2,[2,3,31307]),
    (139,[]),(131,[]),(145,[]),(5,[2,93941]),(131,[]),
    (169,[]),(5,[2,47,1999]),(131,[]),(5,[2,3,31321]),(135,[]),
    (131,[]),(20,[2,3,31327]),(141,[]),(131,[]),(22,[2,3,17,19,97])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock188 : ∃ data, checkBlock 188 data = true :=
  ⟨[(145,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (175,[]),(189,[]),(131,[]),(135,[]),(255,[]),
    (131,[]),(18,[2,3,107,293]),(141,[]),(131,[]),(5,[2,3,31357]),
    (5,[2,7,89,151]),(131,[]),(135,[]),(355,[]),(131,[]),
    (181,[]),(145,[]),(131,[]),(141,[]),(139,[]),
    (131,[]),(159,[]),(201,[]),(131,[]),(139,[]),
    (10,[2,94151]),(131,[]),(2,[2,3,31387]),(211,[]),(131,[]),
    (147,[]),(135,[]),(131,[]),(141,[]),(159,[]),
    (131,[]),(12,[2,3,3,3,3,1163]),(147,[]),(131,[]),(2,[2,3,3,19,19,29]),
    (135,[]),(131,[]),(357,[]),(5,[2,7,13463]),(131,[]),
    (135,[]),(139,[]),(131,[]),(21,[2,3,13,2417]),(295,[]),
    (131,[]),(19,[2,3,11,2857]),(229,[]),(131,[]),(135,[]),
    (5,[2,181,521]),(131,[]),(151,[]),(181,[]),(131,[]),
    (199,[]),(165,[]),(131,[]),(139,[]),(10,[2,94343]),
    (131,[]),(38,[2,3,7,4493]),(169,[]),(131,[]),(301,[]),
    (141,[]),(131,[]),(12,[2,3,3,10487]),(135,[]),(131,[]),
    (147,[]),(151,[]),(131,[]),(11,[2,3,11,2861]),(5,[2,94421]),
    (131,[]),(10,[2,3,31477]),(135,[]),(131,[]),(145,[]),
    (139,[]),(131,[]),(135,[]),(13,[2,94463]),(131,[]),
    (139,[]),(361,[]),(131,[]),(37,[2,3,3,10499]),(175,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock189 : ∃ data, checkBlock 189 data = true :=
  ⟨[(131,[]),(135,[]),(145,[]),(131,[]),(2,[2,3,7,7,643]),
    (207,[]),(131,[]),(12,[2,3,31511]),(151,[]),(131,[]),
    (255,[]),(147,[]),(131,[]),(40,[2,3,3,7,19,79]),(201,[]),
    (131,[]),(141,[]),(139,[]),(131,[]),(11,[2,3,31531]),
    (135,[]),(131,[]),(10,[2,3,11,47,61]),(145,[]),(131,[]),
    (225,[]),(181,[]),(131,[]),(157,[]),(135,[]),
    (131,[]),(2,[2,3,3,13,809]),(211,[]),(131,[]),(135,[]),
    (5,[2,17,5569]),(131,[]),(537,[]),(357,[]),(131,[]),
    (165,[]),(14,[2,7,83,163]),(131,[]),(135,[]),(517,[]),
    (131,[]),(6,[2,3,7,13,347]),(5,[2,61,1553]),(131,[]),(147,[]),
    (159,[]),(131,[]),(11,[2,3,3,10529]),(141,[]),(131,[]),
    (67,[2,3,7,4513]),(139,[]),(131,[]),(10,[2,3,19,1663]),(171,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(2,[2,3,31607]),
    (327,[]),(131,[]),(369,[]),(141,[]),(131,[]),
    (145,[]),(135,[]),(131,[]),(151,[]),(13,[2,7,13553]),
    (131,[]),(135,[]),(13,[2,239,397]),(131,[]),(141,[]),
    (187,[]),(131,[]),(5,[2,3,17,1861]),(139,[]),(131,[]),
    (135,[]),(157,[]),(131,[]),(445,[]),(10,[2,19,19,263]),
    (131,[]),(145,[]),(385,[]),(131,[]),(141,[]),
    (5,[2,73,1301]),(131,[]),(5,[2,3,7,4523]),(40,[2,13,7307]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock190 : ∃ data, checkBlock 190 data = true :=
  ⟨[(139,[]),(379,[]),(131,[]),(2,[2,3,3,3,3,3,17,23]),(135,[]),
    (131,[]),(10,[2,3,3,10559]),(199,[]),(131,[]),(561,[]),
    (171,[]),(131,[]),(159,[]),(135,[]),(131,[]),
    (11,[2,3,11,43,67]),(525,[]),(131,[]),(135,[]),(151,[]),
    (131,[]),(5,[2,3,3,10567]),(139,[]),(131,[]),(2,[2,3,3,3,13,271]),
    (145,[]),(131,[]),(135,[]),(5,[2,89,1069]),(131,[]),
    (175,[]),(141,[]),(131,[]),(157,[]),(259,[]),
    (131,[]),(169,[]),(14,[2,11,17,509]),(131,[]),(12,[2,3,3,7,1511]),
    (5,[2,31,37,83]),(131,[]),(237,[]),(319,[]),(131,[]),
    (171,[]),(135,[]),(131,[]),(367,[]),(139,[]),
    (131,[]),(2,[2,3,31751]),(5,[2,95261]),(131,[]),(10,[2,3,11,2887]),
    (135,[]),(131,[]),(141,[]),(14,[2,7,13613]),(131,[]),
    (135,[]),(14,[2,13,7331]),(131,[]),(147,[]),(439,[]),
    (131,[]),(139,[]),(7,[2,7,13619]),(131,[]),(135,[]),
    (147,[]),(131,[]),(141,[]),(217,[]),(131,[]),
    (181,[]),(14,[2,11,13,23,29]),(131,[]),(5,[2,3,3,3,3533]),(5,[2,95393]),
    (131,[]),(11,[2,3,7,7,11,59]),(19,[2,73,1307]),(131,[]),(2,[2,3,17,1871]),
    (267,[]),(131,[]),(159,[]),(135,[]),(131,[]),
    (477,[]),(157,[]),(131,[]),(139,[]),(207,[]),
    (131,[]),(171,[]),(135,[]),(131,[]),(459,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock191 : ∃ data, checkBlock 191 data = true :=
  ⟨[(537,[]),(131,[]),(135,[]),(5,[2,11,19,457]),(131,[]),
    (41,[2,3,17,1873]),(145,[]),(131,[]),(147,[]),(141,[]),
    (131,[]),(135,[]),(5,[2,95561]),(131,[]),(23,[2,3,3,7,37,41]),
    (139,[]),(131,[]),(277,[]),(169,[]),(131,[]),
    (199,[]),(495,[]),(131,[]),(2,[2,3,7,29,157]),(141,[]),
    (131,[]),(321,[]),(145,[]),(131,[]),(325,[]),
    (135,[]),(131,[]),(139,[]),(165,[]),(131,[]),
    (141,[]),(159,[]),(131,[]),(151,[]),(135,[]),
    (131,[]),(405,[]),(235,[]),(131,[]),(135,[]),
    (10,[2,95723]),(131,[]),(11,[2,3,3,11,967]),(547,[]),(131,[]),
    (141,[]),(5,[2,7,13679]),(131,[]),(135,[]),(139,[]),
    (131,[]),(11,[2,3,7,4561]),(151,[]),(131,[]),(139,[]),
    (157,[]),(131,[]),(165,[]),(5,[2,95813]),(131,[]),
    (211,[]),(265,[]),(131,[]),(231,[]),(195,[]),
    (131,[]),(2,[2,3,89,359]),(135,[]),(131,[]),(145,[]),
    (5,[2,95873]),(131,[]),(147,[]),(10,[2,95891]),(131,[]),
    (18,[2,3,13,2459]),(135,[]),(131,[]),(20,[2,3,3,10657]),(147,[]),
    (131,[]),(135,[]),(141,[]),(131,[]),(439,[]),
    (29,[2,229,419]),(131,[]),(409,[]),(187,[]),(131,[]),
    (135,[]),(225,[]),(131,[]),(139,[]),(241,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock192 : ∃ data, checkBlock 192 data = true :=
  ⟨[(131,[]),(5,[2,3,3,10667]),(141,[]),(131,[]),(13,[2,3,3,47,227]),
    (10,[2,131,733]),(131,[]),(157,[]),(145,[]),(131,[]),
    (5,[2,3,101,317]),(159,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(187,[]),(169,[]),(131,[]),(2,[2,3,3,3,3559]),
    (139,[]),(131,[]),(147,[]),(135,[]),(131,[]),
    (139,[]),(10,[2,7,31,443]),(131,[]),(135,[]),(145,[]),
    (131,[]),(2,[2,3,32051]),(14,[2,13,13,569]),(131,[]),(5,[2,3,32057]),
    (6,[2,7,11,1249]),(131,[]),(135,[]),(10,[2,43,2237]),(131,[]),
    (309,[]),(29,[2,17,5659]),(131,[]),(465,[]),(181,[]),
    (131,[]),(12,[2,3,32077]),(139,[]),(131,[]),(151,[]),
    (291,[]),(131,[]),(207,[]),(147,[]),(131,[]),
    (2,[2,3,3,19,563]),(135,[]),(131,[]),(23,[2,3,3,13,823]),(5,[2,96293]),
    (131,[]),(229,[]),(199,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(2,[2,3,163,197]),(171,[]),(131,[]),
    (135,[]),(235,[]),(131,[]),(159,[]),(10,[2,11,8761]),
    (131,[]),(145,[]),(10,[2,7,7,7,281]),(131,[]),(135,[]),
    (141,[]),(131,[]),(169,[]),(279,[]),(131,[]),
    (12,[2,3,32141]),(139,[]),(131,[]),(12,[2,3,17,31,61]),(13,[2,96443]),
    (131,[]),(139,[]),(5,[2,96461]),(131,[]),(189,[]),
    (151,[]),(131,[]),(145,[]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock193 : ∃ data, checkBlock 193 data = true :=
  ⟨[(12,[2,3,19,1693]),(385,[]),(131,[]),(171,[]),(5,[2,263,367]),
    (131,[]),(141,[]),(135,[]),(131,[]),(421,[]),
    (145,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (2,[2,3,32191]),(5,[2,96581]),(131,[]),(10,[2,3,11,2927]),(189,[]),
    (131,[]),(135,[]),(151,[]),(131,[]),(2,[2,3,7,43,107]),
    (19,[2,23,4201]),(131,[]),(285,[]),(5,[2,241,401]),(131,[]),
    (139,[]),(145,[]),(131,[]),(40,[2,3,7,4603]),(157,[]),
    (131,[]),(147,[]),(10,[2,109,887]),(131,[]),(2,[2,3,167,193]),
    (135,[]),(131,[]),(20,[2,3,32237]),(141,[]),(131,[]),
    (11,[2,3,3,11,977]),(14,[2,96731]),(131,[]),(319,[]),(135,[]),
    (131,[]),(2,[2,3,32251]),(139,[]),(131,[]),(135,[]),
    (165,[]),(131,[]),(139,[]),(141,[]),(131,[]),
    (11,[2,3,41,787]),(13,[2,7,13829]),(131,[]),(135,[]),(169,[]),
    (131,[]),(5,[2,3,3,7,29,53]),(147,[]),(131,[]),(141,[]),
    (10,[2,96851]),(131,[]),(29,[2,3,83,389]),(14,[2,13,7451]),(131,[]),
    (441,[]),(5,[2,19,5099]),(131,[]),(145,[]),(139,[]),
    (131,[]),(157,[]),(135,[]),(131,[]),(141,[]),
    (10,[2,103,941]),(131,[]),(151,[]),(5,[2,13,7457]),(131,[]),
    (225,[]),(135,[]),(131,[]),(181,[]),(20,[2,7,7,1979]),
    (131,[]),(135,[]),(159,[]),(131,[]),(145,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock194 : ∃ data, checkBlock 194 data = true :=
  ⟨[(5,[2,97001]),(131,[]),(379,[]),(5,[2,7,13859]),(131,[]),
    (135,[]),(175,[]),(131,[]),(19,[2,3,7,4621]),(10,[2,53,1831]),
    (131,[]),(201,[]),(145,[]),(131,[]),(151,[]),
    (277,[]),(131,[]),(6,[2,3,3,7,23,67]),(139,[]),(131,[]),
    (2,[2,3,3,10789]),(141,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(5,[2,3,32377]),(5,[2,137,709]),(131,[]),(165,[]),
    (211,[]),(131,[]),(21,[2,3,139,233]),(135,[]),(131,[]),
    (237,[]),(141,[]),(131,[]),(135,[]),(157,[]),
    (131,[]),(189,[]),(327,[]),(131,[]),(12,[2,3,23,1409]),
    (139,[]),(131,[]),(135,[]),(5,[2,97241]),(131,[]),
    (147,[]),(5,[2,13,7481]),(131,[]),(5,[2,3,3,101,107]),(29,[2,211,461]),
    (131,[]),(181,[]),(231,[]),(131,[]),(159,[]),
    (151,[]),(131,[]),(139,[]),(169,[]),(131,[]),
    (12,[2,3,32441]),(135,[]),(131,[]),(11,[2,3,71,457]),(10,[2,311,313]),
    (131,[]),(2,[2,3,3,29,373]),(5,[2,11,53,167]),(131,[]),(277,[]),
    (135,[]),(131,[]),(10,[2,3,11,13,227]),(237,[]),(131,[]),
    (135,[]),(147,[]),(131,[]),(17,[2,3,19,1709]),(139,[]),
    (131,[]),(13,[2,3,47,691]),(5,[2,7,31,449]),(131,[]),(135,[]),
    (195,[]),(131,[]),(549,[]),(525,[]),(131,[]),
    (511,[]),(5,[2,43,2267]),(131,[]),(201,[]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock195 : ∃ data, checkBlock 195 data = true :=
  ⟨[(131,[]),(145,[]),(10,[2,97511]),(131,[]),(2,[2,3,32507]),
    (34,[2,97523]),(131,[]),(225,[]),(135,[]),(131,[]),
    (19,[2,3,3,3,3613]),(139,[]),(131,[]),(5,[2,3,17,1913]),(141,[]),
    (131,[]),(2,[2,3,11,2957]),(135,[]),(131,[]),(147,[]),
    (5,[2,7,73,191]),(131,[]),(135,[]),(325,[]),(131,[]),
    (141,[]),(147,[]),(131,[]),(139,[]),(529,[]),
    (131,[]),(135,[]),(165,[]),(131,[]),(19,[2,3,7,4651]),
    (145,[]),(131,[]),(207,[]),(189,[]),(131,[]),
    (141,[]),(10,[2,41,2383]),(131,[]),(12,[2,3,3,3,7,11,47]),(5,[2,13,7517]),
    (131,[]),(199,[]),(187,[]),(131,[]),(361,[]),
    (135,[]),(131,[]),(151,[]),(19,[2,59,1657]),(131,[]),
    (139,[]),(397,[]),(131,[]),(259,[]),(135,[]),
    (131,[]),(171,[]),(181,[]),(131,[]),(135,[]),
    (307,[]),(131,[]),(517,[]),(207,[]),(131,[]),
    (159,[]),(151,[]),(131,[]),(135,[]),(10,[2,97871]),
    (131,[]),(291,[]),(139,[]),(131,[]),(28,[2,3,3,73,149]),
    (231,[]),(131,[]),(145,[]),(159,[]),(131,[]),
    (279,[]),(19,[2,97931]),(131,[]),(2,[2,3,32647]),(19,[2,97943]),
    (131,[]),(2,[2,3,103,317]),(135,[]),(131,[]),(139,[]),
    (147,[]),(131,[]),(19,[2,3,3,3,19,191]),(151,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock196 : ∃ data, checkBlock 196 data = true :=
  ⟨[(11,[2,3,3,10889]),(135,[]),(131,[]),(141,[]),(18,[2,7,11,19,67]),
    (131,[]),(135,[]),(217,[]),(131,[]),(5,[2,3,11,2971]),
    (169,[]),(131,[]),(171,[]),(157,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(141,[]),(5,[2,233,421]),
    (131,[]),(139,[]),(445,[]),(131,[]),(157,[]),
    (14,[2,98123]),(131,[]),(169,[]),(459,[]),(131,[]),
    (28,[2,3,32717]),(5,[2,11,8923]),(131,[]),(147,[]),(135,[]),
    (131,[]),(307,[]),(145,[]),(131,[]),(11,[2,3,71,461]),
    (147,[]),(131,[]),(217,[]),(135,[]),(131,[]),
    (159,[]),(351,[]),(131,[]),(135,[]),(477,[]),
    (131,[]),(165,[]),(5,[2,97,1013]),(131,[]),(6,[2,3,3,61,179]),
    (141,[]),(131,[]),(135,[]),(14,[2,227,433]),(131,[]),
    (139,[]),(549,[]),(131,[]),(151,[]),(5,[2,98321]),
    (131,[]),(23,[2,3,73,449]),(321,[]),(131,[]),(5,[2,3,3,7,7,223]),
    (141,[]),(131,[]),(255,[]),(10,[2,19,31,167]),(131,[]),
    (309,[]),(135,[]),(131,[]),(147,[]),(435,[]),
    (131,[]),(141,[]),(139,[]),(131,[]),(145,[]),
    (135,[]),(131,[]),(139,[]),(175,[]),(131,[]),
    (135,[]),(5,[2,98453]),(131,[]),(11,[2,3,23,1427]),(159,[]),
    (131,[]),(141,[]),(559,[]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock197 : ∃ data, checkBlock 197 data = true :=
  ⟨[(5,[2,13,7577]),(131,[]),(13,[2,3,7,4691]),(201,[]),(131,[]),
    (145,[]),(10,[2,37,2663]),(131,[]),(2,[2,3,3,10949]),(139,[]),
    (131,[]),(181,[]),(5,[2,98561]),(131,[]),(265,[]),
    (5,[2,98573]),(131,[]),(199,[]),(135,[]),(131,[]),
    (12,[2,3,23,1429]),(19,[2,151,653]),(131,[]),(295,[]),(5,[2,98621]),
    (131,[]),(139,[]),(135,[]),(131,[]),(157,[]),
    (319,[]),(131,[]),(135,[]),(141,[]),(131,[]),
    (2,[2,3,31,1061]),(151,[]),(131,[]),(6,[2,3,67,491]),(145,[]),
    (131,[]),(135,[]),(13,[2,98711]),(131,[]),(475,[]),
    (175,[]),(131,[]),(147,[]),(139,[]),(131,[]),
    (441,[]),(5,[2,17,37,157]),(131,[]),(139,[]),(147,[]),
    (131,[]),(159,[]),(19,[2,173,571]),(131,[]),(141,[]),
    (135,[]),(131,[]),(211,[]),(357,[]),(131,[]),
    (5,[2,3,32941]),(285,[]),(131,[]),(12,[2,3,47,701]),(135,[]),
    (131,[]),(339,[]),(277,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(10,[2,3,3,10987]),(225,[]),(131,[]),
    (2,[2,3,3,3,3,3,11,37]),(10,[2,7,71,199]),(131,[]),(135,[]),(171,[]),
    (131,[]),(145,[]),(157,[]),(131,[]),(6,[2,3,13,43,59]),
    (201,[]),(131,[]),(139,[]),(10,[2,98963]),(131,[]),
    (22,[2,3,3,7,1571]),(5,[2,98981]),(131,[]),(157,[]),(165,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock198 : ∃ data, checkBlock 198 data = true :=
  ⟨[(131,[]),(151,[]),(135,[]),(131,[]),(2,[2,3,13,2539]),
    (10,[2,99023]),(131,[]),(145,[]),(5,[2,99041]),(131,[]),
    (525,[]),(135,[]),(131,[]),(5,[2,3,3,3,3,1223]),(139,[]),
    (131,[]),(135,[]),(181,[]),(131,[]),(139,[]),
    (145,[]),(131,[]),(10,[2,3,33037]),(147,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(151,[]),(211,[]),
    (131,[]),(159,[]),(5,[2,17,19,307]),(131,[]),(369,[]),
    (5,[2,99173]),(131,[]),(141,[]),(411,[]),(131,[]),
    (327,[]),(139,[]),(131,[]),(11,[2,3,33071]),(135,[]),
    (131,[]),(10,[2,3,11,31,97]),(151,[]),(131,[]),(201,[]),
    (13,[2,99251]),(131,[]),(141,[]),(135,[]),(131,[]),
    (495,[]),(157,[]),(131,[]),(135,[]),(199,[]),
    (131,[]),(147,[]),(19,[2,47,2113]),(131,[]),(399,[]),
    (10,[2,7,7,2027]),(131,[]),(135,[]),(147,[]),(131,[]),
    (171,[]),(237,[]),(131,[]),(165,[]),(151,[]),
    (131,[]),(175,[]),(241,[]),(131,[]),(265,[]),
    (139,[]),(131,[]),(39,[2,3,13,2549]),(5,[2,89,1117]),(131,[]),
    (139,[]),(135,[]),(131,[]),(145,[]),(141,[]),
    (131,[]),(571,[]),(195,[]),(131,[]),(5,[2,3,71,467]),
    (135,[]),(131,[]),(5,[2,3,33161]),(321,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock199 : ∃ data, checkBlock 199 data = true :=
  ⟨[(135,[]),(187,[]),(131,[]),(157,[]),(141,[]),
    (131,[]),(147,[]),(139,[]),(131,[]),(135,[]),
    (10,[2,99551]),(131,[]),(301,[]),(235,[]),(131,[]),
    (141,[]),(405,[]),(131,[]),(537,[]),(267,[]),
    (131,[]),(12,[2,3,3,3,7,17,31]),(145,[]),(131,[]),(139,[]),
    (10,[2,99623]),(131,[]),(2,[2,3,33211]),(135,[]),(131,[]),
    (141,[]),(369,[]),(131,[]),(175,[]),(10,[2,11,13,17,41]),
    (131,[]),(201,[]),(135,[]),(131,[]),(151,[]),
    (5,[2,7,14243]),(131,[]),(135,[]),(145,[]),(131,[]),
    (33,[2,3,13,2557]),(139,[]),(131,[]),(12,[2,3,33247]),(13,[2,7,14249]),
    (131,[]),(135,[]),(5,[2,99761]),(131,[]),(511,[]),
    (159,[]),(131,[]),(5,[2,3,3,11087]),(19,[2,73,1367]),(131,[]),
    (21,[2,3,3,13,853]),(157,[]),(131,[]),(217,[]),(309,[]),
    (131,[]),(151,[]),(141,[]),(131,[]),(10,[2,3,23,1447]),
    (135,[]),(131,[]),(157,[]),(139,[]),(131,[]),
    (147,[]),(165,[]),(131,[]),(5,[2,3,3,11,1009]),(135,[]),
    (131,[]),(10,[2,3,33301]),(141,[]),(131,[]),(135,[]),
    (151,[]),(131,[]),(397,[]),(265,[]),(131,[]),
    (139,[]),(171,[]),(131,[]),(135,[]),(307,[]),
    (131,[]),(487,[]),(10,[2,13,7691]),(131,[]),(355,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock200 : ∃ data, checkBlock 200 data = true :=
  ⟨[(5,[2,11,9091]),(131,[]),(12,[2,3,17,37,53]),(445,[]),(131,[]),
    (379,[]),(29,[2,67,1493]),(131,[]),(141,[]),(19,[2,100043]),
    (131,[]),(145,[]),(135,[]),(131,[]),(391,[]),
    (361,[]),(131,[]),(139,[]),(10,[2,101,991]),(131,[]),
    (147,[]),(135,[]),(131,[]),(19,[2,3,13,17,151]),(145,[]),
    (131,[]),(135,[]),(175,[]),(131,[]),(181,[]),
    (157,[]),(131,[]),(17,[2,3,3,31,359]),(291,[]),(131,[]),
    (135,[]),(5,[2,17,71,83]),(131,[]),(5,[2,3,7,13,367]),(139,[]),
    (131,[]),(39,[2,3,127,263]),(171,[]),(131,[]),(2,[2,3,11,3037]),
    (141,[]),(131,[]),(11,[2,3,3,7,37,43]),(5,[2,59,1699]),(131,[]),
    (165,[]),(147,[]),(131,[]),(321,[]),(135,[]),
    (131,[]),(139,[]),(295,[]),(131,[]),(2,[2,3,101,331]),
    (141,[]),(131,[]),(567,[]),(135,[]),(131,[]),
    (411,[]),(159,[]),(131,[]),(135,[]),(229,[]),
    (131,[]),(141,[]),(5,[2,100361]),(131,[]),(325,[]),
    (231,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (285,[]),(29,[2,100403]),(131,[]),(139,[]),(5,[2,137,733]),
    (131,[]),(141,[]),(5,[2,67,1499]),(131,[]),(147,[]),
    (19,[2,13,7727]),(131,[]),(145,[]),(29,[2,11,9133]),(131,[]),
    (165,[]),(135,[]),(131,[]),(23,[2,3,19,41,43]),(5,[2,100493])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock201 : ∃ data, checkBlock 201 data = true :=
  ⟨[(131,[]),(11,[2,3,3,13,859]),(169,[]),(131,[]),(151,[]),
    (135,[]),(131,[]),(195,[]),(339,[]),(131,[]),
    (135,[]),(5,[2,193,521]),(131,[]),(145,[]),(199,[]),
    (131,[]),(2,[2,3,13,2579]),(20,[2,7,14369]),(131,[]),(135,[]),
    (5,[2,29,3469]),(131,[]),(139,[]),(141,[]),(131,[]),
    (6,[2,3,17,1973]),(145,[]),(131,[]),(159,[]),(10,[2,19,5297]),
    (131,[]),(2,[2,3,7,4793]),(237,[]),(131,[]),(147,[]),
    (157,[]),(131,[]),(187,[]),(135,[]),(131,[]),
    (13,[2,3,3,67,167]),(159,[]),(131,[]),(199,[]),(139,[]),
    (131,[]),(157,[]),(135,[]),(131,[]),(139,[]),
    (151,[]),(131,[]),(135,[]),(265,[]),(131,[]),
    (2,[2,3,3,11197]),(481,[]),(131,[]),(175,[]),(327,[]),
    (131,[]),(135,[]),(10,[2,100811]),(131,[]),(141,[]),
    (147,[]),(131,[]),(11,[2,3,19,29,61]),(14,[2,13,7757]),(131,[]),
    (529,[]),(139,[]),(131,[]),(189,[]),(10,[2,19,5309]),
    (131,[]),(217,[]),(10,[2,79,1277]),(131,[]),(2,[2,3,13,13,199]),
    (135,[]),(131,[]),(5,[2,3,33637]),(5,[2,100913]),(131,[]),
    (5,[2,3,33641]),(465,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(2,[2,3,3,3,3739]),(7,[2,7,14423]),(131,[]),(135,[]),
    (5,[2,37,2729]),(131,[]),(267,[]),(165,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock202 : ∃ data, checkBlock 202 data = true :=
  ⟨[(207,[]),(141,[]),(131,[]),(135,[]),(157,[]),
    (131,[]),(10,[2,3,7,17,283]),(5,[2,71,1423]),(131,[]),(12,[2,3,3,103,109]),
    (139,[]),(131,[]),(235,[]),(14,[2,101063]),(131,[]),
    (139,[]),(141,[]),(131,[]),(5,[2,3,31,1087]),(5,[2,43,2351]),
    (131,[]),(357,[]),(135,[]),(131,[]),(2,[2,3,37,911]),
    (391,[]),(131,[]),(141,[]),(145,[]),(131,[]),
    (229,[]),(135,[]),(131,[]),(10,[2,3,33721]),(20,[2,7,97,149]),
    (131,[]),(135,[]),(139,[]),(131,[]),(20,[2,3,89,379]),
    (5,[2,17,5953]),(131,[]),(141,[]),(165,[]),(131,[]),
    (135,[]),(421,[]),(131,[]),(147,[]),(145,[]),
    (131,[]),(157,[]),(159,[]),(131,[]),(139,[]),
    (187,[]),(131,[]),(33,[2,3,7,7,13,53]),(301,[]),(131,[]),
    (211,[]),(151,[]),(131,[]),(20,[2,3,3,11257]),(135,[]),
    (131,[]),(169,[]),(5,[2,101333]),(131,[]),(285,[]),
    (189,[]),(131,[]),(165,[]),(135,[]),(131,[]),
    (83,[2,3,33791]),(139,[]),(131,[]),(135,[]),(141,[]),
    (131,[]),(139,[]),(10,[2,101411]),(131,[]),(321,[]),
    (199,[]),(131,[]),(135,[]),(151,[]),(131,[]),
    (459,[]),(5,[2,11,23,401]),(131,[]),(435,[]),(141,[]),
    (131,[]),(145,[]),(13,[2,101483]),(131,[]),(2,[2,3,3,3,3,7,179])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock203 : ∃ data, checkBlock 203 data = true :=
  ⟨[(171,[]),(131,[]),(13,[2,3,3,11279]),(139,[]),(131,[]),
    (141,[]),(135,[]),(131,[]),(439,[]),(157,[]),
    (131,[]),(325,[]),(357,[]),(131,[]),(159,[]),
    (135,[]),(131,[]),(145,[]),(13,[2,7,23,631]),(131,[]),
    (135,[]),(10,[2,101603]),(131,[]),(21,[2,3,33871]),(147,[]),
    (131,[]),(309,[]),(159,[]),(131,[]),(135,[]),
    (145,[]),(131,[]),(22,[2,3,7,47,103]),(255,[]),(131,[]),
    (171,[]),(5,[2,101681]),(131,[]),(10,[2,3,3,11299]),(5,[2,101693]),
    (131,[]),(235,[]),(139,[]),(131,[]),(259,[]),
    (517,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (237,[]),(145,[]),(131,[]),(151,[]),(217,[]),
    (131,[]),(17,[2,3,3,43,263]),(135,[]),(131,[]),(291,[]),
    (225,[]),(131,[]),(135,[]),(7,[2,17,53,113]),(131,[]),
    (169,[]),(10,[2,79,1289]),(131,[]),(277,[]),(139,[]),
    (131,[]),(135,[]),(141,[]),(131,[]),(201,[]),
    (195,[]),(131,[]),(12,[2,3,33961]),(157,[]),(131,[]),
    (151,[]),(13,[2,181,563]),(131,[]),(141,[]),(5,[2,101921]),
    (131,[]),(139,[]),(367,[]),(131,[]),(159,[]),
    (135,[]),(131,[]),(189,[]),(147,[]),(131,[]),
    (18,[2,3,19,1789]),(187,[]),(131,[]),(141,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock204 : ∃ data, checkBlock 204 data = true :=
  ⟨[(131,[]),(10,[2,3,11,11,281]),(14,[2,7,13,19,59]),(131,[]),(135,[]),
    (14,[2,102023]),(131,[]),(2,[2,3,3,3,3779]),(139,[]),(131,[]),
    (181,[]),(5,[2,7,61,239]),(131,[]),(135,[]),(10,[2,102071]),
    (131,[]),(2,[2,3,7,4861]),(189,[]),(131,[]),(145,[]),
    (165,[]),(131,[]),(571,[]),(459,[]),(131,[]),
    (157,[]),(151,[]),(131,[]),(195,[]),(409,[]),
    (131,[]),(147,[]),(135,[]),(131,[]),(255,[]),
    (139,[]),(131,[]),(10,[2,3,34061]),(147,[]),(131,[]),
    (175,[]),(135,[]),(131,[]),(13,[2,3,3,41,277]),(5,[2,7,17,859]),
    (131,[]),(135,[]),(169,[]),(131,[]),(34,[2,3,173,197]),
    (141,[]),(131,[]),(139,[]),(145,[]),(131,[]),
    (135,[]),(5,[2,23,4447]),(131,[]),(56,[2,3,7,4871]),(5,[2,102293]),
    (131,[]),(141,[]),(33,[2,11,71,131]),(131,[]),(241,[]),
    (165,[]),(131,[]),(11,[2,3,7,11,443]),(325,[]),(131,[]),
    (405,[]),(5,[2,19,5387]),(131,[]),(229,[]),(135,[]),
    (131,[]),(141,[]),(225,[]),(131,[]),(139,[]),
    (5,[2,13,7877]),(131,[]),(367,[]),(135,[]),(131,[]),
    (207,[]),(477,[]),(131,[]),(135,[]),(10,[2,11,67,139]),
    (131,[]),(151,[]),(5,[2,102461]),(131,[]),(157,[]),
    (7,[2,7,14639]),(131,[]),(135,[]),(10,[2,113,907]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock205 : ∃ data, checkBlock 205 data = true :=
  ⟨[(145,[]),(139,[]),(131,[]),(549,[]),(5,[2,157,653]),
    (131,[]),(23,[2,3,11,13,239]),(147,[]),(131,[]),(195,[]),
    (19,[2,102551]),(131,[]),(169,[]),(141,[]),(131,[]),
    (399,[]),(135,[]),(131,[]),(139,[]),(5,[2,102593]),
    (131,[]),(145,[]),(13,[2,102611]),(131,[]),(295,[]),
    (135,[]),(131,[]),(20,[2,3,34211]),(141,[]),(131,[]),
    (135,[]),(5,[2,102653]),(131,[]),(10,[2,3,3,11,17,61]),(145,[]),
    (131,[]),(265,[]),(151,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(6,[2,3,7,67,73]),(5,[2,13,7901]),(131,[]),
    (139,[]),(10,[2,17,6043]),(131,[]),(11,[2,3,23,1489]),(14,[2,127,809]),
    (131,[]),(38,[2,3,3,7,7,233]),(147,[]),(131,[]),(141,[]),
    (145,[]),(131,[]),(327,[]),(135,[]),(131,[]),
    (12,[2,3,34267]),(29,[2,223,461]),(131,[]),(11,[2,3,43,797]),(151,[]),
    (131,[]),(19,[2,3,151,227]),(135,[]),(131,[]),(199,[]),
    (10,[2,7,7,2099]),(131,[]),(135,[]),(537,[]),(131,[]),
    (159,[]),(5,[2,102881]),(131,[]),(12,[2,3,34297]),(201,[]),
    (131,[]),(135,[]),(13,[2,102911]),(131,[]),(139,[]),
    (10,[2,19,5417]),(131,[]),(255,[]),(5,[2,311,331]),(131,[]),
    (147,[]),(141,[]),(131,[]),(171,[]),(169,[]),
    (131,[]),(38,[2,3,34327]),(10,[2,102983]),(131,[]),(157,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock206 : ∃ data, checkBlock 206 data = true :=
  ⟨[(135,[]),(131,[]),(145,[]),(5,[2,31,3323]),(131,[]),
    (28,[2,3,3,11447]),(139,[]),(131,[]),(2,[2,3,3,107,107]),(135,[]),
    (131,[]),(139,[]),(5,[2,7,14723]),(131,[]),(135,[]),
    (339,[]),(131,[]),(141,[]),(30,[2,103091]),(131,[]),
    (17,[2,3,34367]),(147,[]),(131,[]),(135,[]),(159,[]),
    (131,[]),(56,[2,3,3,7,1637]),(441,[]),(131,[]),(151,[]),
    (10,[2,19,61,89]),(131,[]),(141,[]),(139,[]),(131,[]),
    (29,[2,3,7,17,17,17]),(145,[]),(131,[]),(6,[2,3,11,53,59]),(307,[]),
    (131,[]),(5,[2,3,3,11467]),(135,[]),(131,[]),(171,[]),
    (30,[2,109,947]),(131,[]),(58,[2,3,13,2647]),(5,[2,17,6073]),(131,[]),
    (139,[]),(135,[]),(131,[]),(19,[2,3,34421]),(20,[2,7,14753]),
    (131,[]),(135,[]),(145,[]),(131,[]),(147,[]),
    (5,[2,11,9391]),(131,[]),(5,[2,3,3,13,883]),(5,[2,7,14759]),(131,[]),
    (135,[]),(147,[]),(131,[]),(157,[]),(141,[]),
    (131,[]),(225,[]),(139,[]),(131,[]),(207,[]),
    (151,[]),(131,[]),(139,[]),(10,[2,103391]),(131,[]),
    (2,[2,3,3,11489]),(19,[2,53,1951]),(131,[]),(17,[2,3,34471]),(135,[]),
    (131,[]),(159,[]),(165,[]),(131,[]),(6,[2,3,29,29,41]),
    (241,[]),(131,[]),(20,[2,3,34487]),(135,[]),(131,[]),
    (141,[]),(195,[]),(131,[]),(135,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock207 : ∃ data, checkBlock 207 data = true :=
  ⟨[(131,[]),(265,[]),(151,[]),(131,[]),(145,[]),
    (325,[]),(131,[]),(135,[]),(285,[]),(131,[]),
    (141,[]),(199,[]),(131,[]),(13,[2,3,3,37,311]),(487,[]),
    (131,[]),(139,[]),(351,[]),(131,[]),(2,[2,3,7,4933]),
    (511,[]),(131,[]),(175,[]),(5,[2,103613]),(131,[]),
    (145,[]),(135,[]),(131,[]),(181,[]),(10,[2,103643]),
    (131,[]),(2,[2,3,3,3,11,349]),(279,[]),(131,[]),(34,[2,3,3,11519]),
    (135,[]),(131,[]),(5,[2,3,17,19,107]),(139,[]),(131,[]),
    (135,[]),(561,[]),(131,[]),(139,[]),(5,[2,19,53,103]),
    (131,[]),(22,[2,3,71,487]),(141,[]),(131,[]),(135,[]),
    (187,[]),(131,[]),(2,[2,3,3,3,3,3,7,61]),(267,[]),(131,[]),
    (2,[2,3,34591]),(5,[2,59,1759]),(131,[]),(169,[]),(145,[]),
    (131,[]),(159,[]),(141,[]),(131,[]),(2,[2,3,34607]),
    (139,[]),(131,[]),(151,[]),(135,[]),(131,[]),
    (357,[]),(181,[]),(131,[]),(141,[]),(14,[2,241,431]),
    (131,[]),(17,[2,3,31,1117]),(135,[]),(131,[]),(175,[]),
    (147,[]),(131,[]),(135,[]),(189,[]),(131,[]),
    (5,[2,3,3,3,3,1283]),(237,[]),(131,[]),(141,[]),(577,[]),
    (131,[]),(135,[]),(23,[2,11,13,727]),(131,[]),(151,[]),
    (5,[2,173,601]),(131,[]),(5,[2,3,11,23,137]),(369,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock208 : ∃ data, checkBlock 208 data = true :=
  ⟨[(2,[2,3,34667]),(207,[]),(131,[]),(405,[]),(139,[]),
    (131,[]),(145,[]),(5,[2,104033]),(131,[]),(139,[]),
    (135,[]),(131,[]),(201,[]),(151,[]),(131,[]),
    (2,[2,3,113,307]),(171,[]),(131,[]),(147,[]),(135,[]),
    (131,[]),(20,[2,3,3,43,269]),(10,[2,7,107,139]),(131,[]),(135,[]),
    (141,[]),(131,[]),(145,[]),(5,[2,223,467]),(131,[]),
    (195,[]),(139,[]),(131,[]),(135,[]),(181,[]),
    (131,[]),(229,[]),(10,[2,104183]),(131,[]),(2,[2,3,3,3,17,227]),
    (141,[]),(131,[]),(157,[]),(385,[]),(131,[]),
    (187,[]),(29,[2,104231]),(131,[]),(139,[]),(147,[]),
    (131,[]),(141,[]),(135,[]),(131,[]),(235,[]),
    (475,[]),(131,[]),(169,[]),(295,[]),(131,[]),
    (465,[]),(135,[]),(131,[]),(31,[2,3,11,29,109]),(165,[]),
    (131,[]),(135,[]),(6,[2,101,1033]),(131,[]),(23,[2,3,34781]),
    (139,[]),(131,[]),(159,[]),(175,[]),(131,[]),
    (135,[]),(319,[]),(131,[]),(409,[]),(5,[2,104393]),
    (131,[]),(10,[2,3,13,2677]),(495,[]),(131,[]),(2,[2,3,34807]),
    (159,[]),(131,[]),(147,[]),(217,[]),(131,[]),
    (445,[]),(5,[2,67,1559]),(131,[]),(5,[2,3,3,3,53,73]),(135,[]),
    (131,[]),(29,[2,3,3,13,19,47]),(139,[]),(131,[]),(231,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock209 : ∃ data, checkBlock 209 data = true :=
  ⟨[(157,[]),(131,[]),(171,[]),(135,[]),(131,[]),
    (151,[]),(14,[2,7,109,137]),(131,[]),(135,[]),(165,[]),
    (131,[]),(195,[]),(5,[2,104561]),(131,[]),(139,[]),
    (5,[2,7,14939]),(131,[]),(135,[]),(141,[]),(131,[]),
    (28,[2,3,7,17,293]),(259,[]),(131,[]),(29,[2,3,34871]),(211,[]),
    (131,[]),(52,[2,3,34877]),(5,[2,19,5507]),(131,[]),(141,[]),
    (439,[]),(131,[]),(147,[]),(67,[2,13,83,97]),(131,[]),
    (2,[2,3,23,37,41]),(135,[]),(131,[]),(165,[]),(169,[]),
    (131,[]),(139,[]),(145,[]),(131,[]),(141,[]),
    (135,[]),(131,[]),(157,[]),(399,[]),(131,[]),
    (135,[]),(151,[]),(131,[]),(319,[]),(10,[2,17,6163]),
    (131,[]),(61,[2,3,53,659]),(30,[2,7,14969]),(131,[]),(135,[]),
    (367,[]),(131,[]),(6,[2,3,7,7,23,31]),(139,[]),(131,[]),
    (10,[2,3,3,19,613]),(199,[]),(131,[]),(577,[]),(10,[2,59,1777]),
    (131,[]),(11,[2,3,7,4993]),(529,[]),(131,[]),(23,[2,3,13,2689]),
    (265,[]),(131,[]),(19,[2,3,34961]),(135,[]),(131,[]),
    (139,[]),(141,[]),(131,[]),(165,[]),(351,[]),
    (131,[]),(187,[]),(135,[]),(131,[]),(5,[2,3,34981]),
    (207,[]),(131,[]),(135,[]),(10,[2,43,2441]),(131,[]),
    (199,[]),(141,[]),(131,[]),(6,[2,3,79,443]),(5,[2,7,53,283])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock210 : ∃ data, checkBlock 210 data = true :=
  ⟨[(131,[]),(135,[]),(139,[]),(131,[]),(169,[]),
    (157,[]),(131,[]),(139,[]),(147,[]),(131,[]),
    (145,[]),(291,[]),(131,[]),(5,[2,3,7,5003]),(30,[2,105071]),
    (131,[]),(157,[]),(201,[]),(131,[]),(20,[2,3,3,11677]),
    (135,[]),(131,[]),(141,[]),(171,[]),(131,[]),
    (5,[2,3,67,523]),(10,[2,13,8087]),(131,[]),(12,[2,3,101,347]),(135,[]),
    (131,[]),(145,[]),(5,[2,7,83,181]),(131,[]),(135,[]),
    (5,[2,105173]),(131,[]),(339,[]),(229,[]),(131,[]),
    (12,[2,3,3,11689]),(13,[2,7,7,19,113]),(131,[]),(135,[]),(145,[]),
    (131,[]),(139,[]),(5,[2,47,2239]),(131,[]),(5,[2,3,35081]),
    (309,[]),(131,[]),(20,[2,3,13,2699]),(10,[2,105263]),(131,[]),
    (439,[]),(321,[]),(131,[]),(159,[]),(141,[]),
    (131,[]),(175,[]),(135,[]),(131,[]),(11,[2,3,35107]),
    (145,[]),(131,[]),(421,[]),(139,[]),(131,[]),
    (151,[]),(135,[]),(131,[]),(139,[]),(141,[]),
    (131,[]),(135,[]),(147,[]),(131,[]),(229,[]),
    (5,[2,105401]),(131,[]),(33,[2,3,41,857]),(6,[2,7,11,37,37]),(131,[]),
    (135,[]),(165,[]),(131,[]),(355,[]),(151,[]),
    (131,[]),(2,[2,3,3,11717]),(5,[2,163,647]),(131,[]),(5,[2,3,3,11719]),
    (139,[]),(131,[]),(5,[2,3,7,5023]),(175,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock211 : ∃ data, checkBlock 211 data = true :=
  ⟨[(141,[]),(10,[2,105503]),(131,[]),(169,[]),(135,[]),
    (131,[]),(5,[2,3,29,1213]),(5,[2,105533]),(131,[]),(171,[]),
    (507,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (147,[]),(151,[]),(131,[]),(135,[]),(5,[2,23,4591]),
    (131,[]),(157,[]),(147,[]),(131,[]),(189,[]),
    (10,[2,7,79,191]),(131,[]),(135,[]),(5,[2,149,709]),(131,[]),
    (259,[]),(165,[]),(131,[]),(145,[]),(139,[]),
    (131,[]),(225,[]),(141,[]),(131,[]),(139,[]),
    (5,[2,105701]),(131,[]),(241,[]),(5,[2,61,1733]),(131,[]),
    (481,[]),(135,[]),(131,[]),(207,[]),(189,[]),
    (131,[]),(2,[2,3,35251]),(141,[]),(131,[]),(5,[2,3,35257]),
    (135,[]),(131,[]),(211,[]),(10,[2,7,7,17,127]),(131,[]),
    (135,[]),(139,[]),(131,[]),(141,[]),(5,[2,29,41,89]),
    (131,[]),(28,[2,3,3,11,1069]),(145,[]),(131,[]),(135,[]),
    (397,[]),(131,[]),(12,[2,3,7,71,71]),(29,[2,105863]),(131,[]),
    (2,[2,3,35291]),(549,[]),(131,[]),(139,[]),(157,[]),
    (131,[]),(151,[]),(159,[]),(131,[]),(477,[]),
    (169,[]),(131,[]),(12,[2,3,35311]),(135,[]),(131,[]),
    (157,[]),(147,[]),(131,[]),(38,[2,3,11,13,13,19]),(14,[2,105971]),
    (131,[]),(255,[]),(135,[]),(131,[]),(187,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock212 : ∃ data, checkBlock 212 data = true :=
  ⟨[(139,[]),(131,[]),(135,[]),(277,[]),(131,[]),
    (139,[]),(291,[]),(131,[]),(151,[]),(217,[]),
    (131,[]),(135,[]),(5,[2,67,1583]),(131,[]),(145,[]),
    (141,[]),(131,[]),(12,[2,3,3,3,3929]),(10,[2,277,383]),(131,[]),
    (2,[2,3,3,11789]),(13,[2,106103]),(131,[]),(12,[2,3,7,31,163]),(5,[2,106121]),
    (131,[]),(361,[]),(139,[]),(131,[]),(147,[]),
    (135,[]),(131,[]),(195,[]),(241,[]),(131,[]),
    (145,[]),(147,[]),(131,[]),(41,[2,3,3,3,3,3,19,23]),(135,[]),
    (131,[]),(141,[]),(14,[2,7,15173]),(131,[]),(135,[]),
    (10,[2,13,8171]),(131,[]),(12,[2,3,17,2083]),(145,[]),(131,[]),
    (169,[]),(6,[2,7,43,353]),(131,[]),(135,[]),(151,[]),
    (131,[]),(141,[]),(159,[]),(131,[]),(28,[2,3,11,3221]),
    (561,[]),(131,[]),(277,[]),(5,[2,41,2593]),(131,[]),
    (465,[]),(139,[]),(131,[]),(28,[2,3,35447]),(145,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(147,[]),
    (207,[]),(131,[]),(391,[]),(517,[]),(131,[]),
    (369,[]),(135,[]),(131,[]),(20,[2,3,79,449]),(7,[2,7,23,661]),
    (131,[]),(135,[]),(5,[2,106433]),(131,[]),(487,[]),
    (10,[2,106451]),(131,[]),(18,[2,3,3,3,3943]),(139,[]),(131,[]),
    (135,[]),(301,[]),(131,[]),(501,[]),(5,[2,109,977])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock213 : ∃ data, checkBlock 213 data = true :=
  ⟨[(131,[]),(181,[]),(29,[2,43,2477]),(131,[]),(21,[2,3,35507]),
    (147,[]),(131,[]),(2,[2,3,3,7,19,89]),(141,[]),(131,[]),
    (139,[]),(231,[]),(131,[]),(195,[]),(135,[]),
    (131,[]),(145,[]),(187,[]),(131,[]),(141,[]),
    (6,[2,11,11,881]),(131,[]),(5,[2,3,35537]),(135,[]),(131,[]),
    (21,[2,3,3,3,11,359]),(13,[2,7,15233]),(131,[]),(135,[]),(14,[2,47,2269]),
    (131,[]),(20,[2,3,73,487]),(139,[]),(131,[]),(141,[]),
    (319,[]),(131,[]),(135,[]),(10,[2,13,29,283]),(131,[]),
    (187,[]),(34,[2,106703]),(131,[]),(147,[]),(589,[]),
    (131,[]),(151,[]),(5,[2,11,31,313]),(131,[]),(169,[]),
    (145,[]),(131,[]),(2,[2,3,19,1873]),(157,[]),(131,[]),
    (307,[]),(135,[]),(131,[]),(265,[]),(139,[]),
    (131,[]),(355,[]),(14,[2,17,61,103]),(131,[]),(157,[]),
    (135,[]),(131,[]),(171,[]),(159,[]),(131,[]),
    (135,[]),(141,[]),(131,[]),(12,[2,3,179,199]),(339,[]),
    (131,[]),(139,[]),(369,[]),(131,[]),(135,[]),
    (175,[]),(131,[]),(165,[]),(5,[2,17,19,331]),(131,[]),
    (53,[2,3,29,1229]),(141,[]),(131,[]),(147,[]),(10,[2,229,467]),
    (131,[]),(537,[]),(151,[]),(131,[]),(5,[2,3,181,197]),
    (5,[2,23,4651]),(131,[]),(141,[]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock214 : ∃ data, checkBlock 214 data = true :=
  ⟨[(11,[2,3,3,3,3,1321]),(30,[2,13,8231]),(131,[]),(139,[]),(5,[2,107021]),
    (131,[]),(5,[2,3,35677]),(135,[]),(131,[]),(5,[2,3,31,1151]),
    (379,[]),(131,[]),(135,[]),(361,[]),(131,[]),
    (12,[2,3,3,11897]),(5,[2,13,8237]),(131,[]),(145,[]),(147,[]),
    (131,[]),(135,[]),(157,[]),(131,[]),(31,[2,3,7,5101]),
    (139,[]),(131,[]),(165,[]),(5,[2,19,5639]),(131,[]),
    (159,[]),(169,[]),(131,[]),(207,[]),(231,[]),
    (131,[]),(22,[2,3,3,11909]),(175,[]),(131,[]),(145,[]),
    (135,[]),(131,[]),(139,[]),(159,[]),(131,[]),
    (259,[]),(13,[2,157,683]),(131,[]),(2,[2,3,35747]),(135,[]),
    (131,[]),(18,[2,3,3,17,701]),(145,[]),(131,[]),(135,[]),
    (201,[]),(131,[]),(147,[]),(187,[]),(131,[]),
    (2,[2,3,47,761]),(14,[2,7,15329]),(131,[]),(135,[]),(139,[]),
    (131,[]),(5,[2,3,7,19,269]),(5,[2,181,593]),(131,[]),(139,[]),
    (181,[]),(131,[]),(2,[2,3,3,79,151]),(145,[]),(131,[]),
    (141,[]),(5,[2,167,643]),(131,[]),(33,[2,3,35797]),(14,[2,11,13,751]),
    (131,[]),(34,[2,3,35801]),(135,[]),(131,[]),(151,[]),
    (309,[]),(131,[]),(62,[2,3,3,3,23,173]),(5,[2,107441]),(131,[]),
    (141,[]),(135,[]),(131,[]),(325,[]),(14,[2,7,13,1181]),
    (131,[]),(135,[]),(14,[2,19,5657]),(131,[]),(11,[2,3,35831])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock215 : ∃ data, checkBlock 215 data = true :=
  ⟨[(195,[]),(131,[]),(147,[]),(151,[]),(131,[]),
    (135,[]),(14,[2,293,367]),(131,[]),(139,[]),(10,[2,41,43,61]),
    (131,[]),(379,[]),(5,[2,29,3709]),(131,[]),(5,[2,3,23,1559]),
    (189,[]),(131,[]),(231,[]),(10,[2,11,9781]),(131,[]),
    (145,[]),(435,[]),(131,[]),(265,[]),(135,[]),
    (131,[]),(295,[]),(141,[]),(131,[]),(589,[]),
    (139,[]),(131,[]),(291,[]),(135,[]),(131,[]),
    (139,[]),(411,[]),(131,[]),(135,[]),(171,[]),
    (131,[]),(145,[]),(141,[]),(131,[]),(2,[2,3,3,11969]),
    (10,[2,7,11,1399]),(131,[]),(135,[]),(5,[2,107741]),(131,[]),
    (5,[2,3,7,7,733]),(5,[2,277,389]),(131,[]),(141,[]),(145,[]),
    (131,[]),(38,[2,3,37,971]),(139,[]),(131,[]),(11,[2,3,3,7,29,59]),
    (277,[]),(131,[]),(385,[]),(199,[]),(131,[]),
    (217,[]),(135,[]),(131,[]),(141,[]),(29,[2,107843]),
    (131,[]),(147,[]),(5,[2,13,8297]),(131,[]),(139,[]),
    (135,[]),(131,[]),(5,[2,3,3,11987]),(147,[]),(131,[]),
    (135,[]),(195,[]),(131,[]),(2,[2,3,13,2767]),(5,[2,11,9811]),
    (131,[]),(5,[2,3,35977]),(267,[]),(131,[]),(135,[]),
    (171,[]),(131,[]),(391,[]),(19,[2,107,1009]),(131,[]),
    (151,[]),(139,[]),(131,[]),(5,[2,3,3,13,13,71]),(399,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock216 : ∃ data, checkBlock 216 data = true :=
  ⟨[(131,[]),(139,[]),(10,[2,108011]),(131,[]),(165,[]),
    (141,[]),(131,[]),(561,[]),(135,[]),(131,[]),
    (19,[2,3,36017]),(13,[2,11,11,19,47]),(131,[]),(12,[2,3,3,12007]),(459,[]),
    (131,[]),(147,[]),(135,[]),(131,[]),(181,[]),
    (141,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (171,[]),(10,[2,108131]),(131,[]),(441,[]),(159,[]),
    (131,[]),(135,[]),(265,[]),(131,[]),(195,[]),
    (5,[2,13,53,157]),(131,[]),(189,[]),(279,[]),(131,[]),
    (139,[]),(151,[]),(131,[]),(145,[]),(229,[]),
    (131,[]),(141,[]),(147,[]),(131,[]),(165,[]),
    (135,[]),(131,[]),(2,[2,3,3,23,523]),(421,[]),(131,[]),
    (211,[]),(145,[]),(131,[]),(237,[]),(135,[]),
    (131,[]),(5,[2,3,13,2777]),(139,[]),(131,[]),(135,[]),
    (13,[2,149,727]),(131,[]),(139,[]),(151,[]),(131,[]),
    (5,[2,3,3,3,4013]),(187,[]),(131,[]),(135,[]),(13,[2,307,353]),
    (131,[]),(171,[]),(145,[]),(131,[]),(2,[2,3,36131]),
    (5,[2,108401]),(131,[]),(181,[]),(141,[]),(131,[]),
    (147,[]),(357,[]),(131,[]),(201,[]),(139,[]),
    (131,[]),(159,[]),(135,[]),(131,[]),(187,[]),
    (5,[2,67,1619]),(131,[]),(10,[2,3,36161]),(141,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock217 : ∃ data, checkBlock 217 data = true :=
  ⟨[(12,[2,3,59,613]),(135,[]),(131,[]),(2,[2,3,3,3,4019]),(255,[]),
    (131,[]),(135,[]),(259,[]),(131,[]),(141,[]),
    (235,[]),(131,[]),(157,[]),(307,[]),(131,[]),
    (135,[]),(5,[2,11,9871]),(131,[]),(225,[]),(175,[]),
    (131,[]),(10,[2,3,3,11,1097]),(34,[2,313,347]),(131,[]),(141,[]),
    (181,[]),(131,[]),(295,[]),(139,[]),(131,[]),
    (147,[]),(5,[2,179,607]),(131,[]),(139,[]),(135,[]),
    (131,[]),(11,[2,3,17,2131]),(19,[2,251,433]),(131,[]),(29,[2,3,3,13,929]),
    (159,[]),(131,[]),(169,[]),(135,[]),(131,[]),
    (145,[]),(14,[2,7,7,7,317]),(131,[]),(135,[]),(207,[]),
    (131,[]),(327,[]),(165,[]),(131,[]),(211,[]),
    (139,[]),(131,[]),(135,[]),(145,[]),(131,[]),
    (151,[]),(141,[]),(131,[]),(411,[]),(5,[2,108821]),
    (131,[]),(435,[]),(5,[2,43,2531]),(131,[]),(5,[2,3,7,71,73]),
    (157,[]),(131,[]),(139,[]),(10,[2,108863]),(131,[]),
    (17,[2,3,3,12097]),(135,[]),(131,[]),(217,[]),(145,[]),
    (131,[]),(301,[]),(10,[2,11,9901]),(131,[]),(307,[]),
    (135,[]),(131,[]),(141,[]),(181,[]),(131,[]),
    (135,[]),(6,[2,13,17,17,29]),(131,[]),(511,[]),(139,[]),
    (131,[]),(339,[]),(165,[]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock218 : ∃ data, checkBlock 218 data = true :=
  ⟨[(5,[2,109001]),(131,[]),(141,[]),(391,[]),(131,[]),
    (5,[2,3,36341]),(147,[]),(131,[]),(2,[2,3,19,1913]),(10,[2,11,23,431]),
    (131,[]),(2,[2,3,3,3,7,577]),(187,[]),(131,[]),(19,[2,3,3,12119]),
    (159,[]),(131,[]),(157,[]),(135,[]),(131,[]),
    (241,[]),(139,[]),(131,[]),(2,[2,3,37,983]),(169,[]),
    (131,[]),(145,[]),(135,[]),(131,[]),(10,[2,3,3,67,181]),
    (327,[]),(131,[]),(135,[]),(237,[]),(131,[]),
    (225,[]),(5,[2,23,47,101]),(131,[]),(139,[]),(141,[]),
    (131,[]),(135,[]),(14,[2,109211]),(131,[]),(147,[]),
    (10,[2,239,457]),(131,[]),(145,[]),(171,[]),(131,[]),
    (175,[]),(481,[]),(131,[]),(22,[2,3,7,11,11,43]),(141,[]),
    (131,[]),(189,[]),(255,[]),(131,[]),(369,[]),
    (135,[]),(131,[]),(5,[2,3,83,439]),(5,[2,109313]),(131,[]),
    (139,[]),(577,[]),(131,[]),(507,[]),(135,[]),
    (131,[]),(151,[]),(5,[2,7,17,919]),(131,[]),(135,[]),
    (147,[]),(131,[]),(159,[]),(10,[2,109391]),(131,[]),
    (141,[]),(145,[]),(131,[]),(135,[]),(5,[2,13,19,443]),
    (131,[]),(157,[]),(139,[]),(131,[]),(13,[2,3,191,191]),
    (585,[]),(131,[]),(2,[2,3,11,31,107]),(201,[]),(131,[]),
    (2,[2,3,7,13,401]),(5,[2,109481]),(131,[]),(151,[]),(5,[2,223,491])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock219 : ∃ data, checkBlock 219 data = true :=
  ⟨[(131,[]),(517,[]),(135,[]),(131,[]),(139,[]),
    (445,[]),(131,[]),(175,[]),(5,[2,109541]),(131,[]),
    (20,[2,3,13,53,53]),(135,[]),(131,[]),(147,[]),(13,[2,7,11,1423]),
    (131,[]),(135,[]),(141,[]),(131,[]),(11,[2,3,3,3,3,3,11,41]),
    (147,[]),(131,[]),(10,[2,3,3,19,641]),(169,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(145,[]),(231,[]),
    (131,[]),(139,[]),(141,[]),(131,[]),(171,[]),
    (529,[]),(131,[]),(181,[]),(207,[]),(131,[]),
    (279,[]),(10,[2,11,9973]),(131,[]),(141,[]),(135,[]),
    (131,[]),(5,[2,3,79,463]),(5,[2,13,23,367]),(131,[]),(145,[]),
    (10,[2,109751]),(131,[]),(2,[2,3,36587]),(135,[]),(131,[]),
    (29,[2,3,3,12197]),(217,[]),(131,[]),(135,[]),(5,[2,109793]),
    (131,[]),(11,[2,3,17,2153]),(145,[]),(131,[]),(285,[]),
    (37,[2,7,29,541]),(131,[]),(135,[]),(5,[2,109841]),(131,[]),
    (139,[]),(5,[2,37,2969]),(131,[]),(5,[2,3,3,3,13,313]),(165,[]),
    (131,[]),(11,[2,3,3,29,421]),(10,[2,109883]),(131,[]),(2,[2,3,7,5233]),
    (201,[]),(131,[]),(5,[2,3,36637]),(145,[]),(131,[]),
    (10,[2,3,11,3331]),(135,[]),(131,[]),(159,[]),(147,[]),
    (131,[]),(157,[]),(139,[]),(131,[]),(10,[2,3,3,3,4073]),
    (135,[]),(131,[]),(139,[]),(10,[2,7,19,827]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock220 : ∃ data, checkBlock 220 data = true :=
  ⟨[(135,[]),(159,[]),(131,[]),(189,[]),(421,[]),
    (131,[]),(5,[2,3,36677]),(487,[]),(131,[]),(135,[]),
    (141,[]),(131,[]),(12,[2,3,3,7,1747]),(379,[]),(131,[]),
    (11,[2,3,36691]),(5,[2,31,53,67]),(131,[]),(549,[]),(139,[]),
    (131,[]),(141,[]),(319,[]),(131,[]),(11,[2,3,11,47,71]),
    (187,[]),(131,[]),(147,[]),(135,[]),(131,[]),
    (145,[]),(5,[2,59,1867]),(131,[]),(28,[2,3,36721]),(147,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(201,[]),
    (5,[2,7,7,13,173]),(131,[]),(135,[]),(181,[]),(131,[]),
    (5,[2,3,3,37,331]),(241,[]),(131,[]),(165,[]),(157,[]),
    (131,[]),(135,[]),(231,[]),(131,[]),(11,[2,3,7,59,89]),
    (151,[]),(131,[]),(495,[]),(139,[]),(131,[]),
    (157,[]),(295,[]),(131,[]),(139,[]),(145,[]),
    (131,[]),(5,[2,3,3,13,23,41]),(14,[2,19,5807]),(131,[]),(20,[2,3,36781]),
    (135,[]),(131,[]),(147,[]),(141,[]),(131,[]),
    (50,[2,3,36791]),(385,[]),(131,[]),(5,[2,3,31,1187]),(135,[]),
    (131,[]),(10,[2,3,3,3,3,29,47]),(151,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(169,[]),(141,[]),(131,[]),
    (19,[2,3,11,3347]),(5,[2,7,31,509]),(131,[]),(135,[]),(237,[]),
    (131,[]),(207,[]),(277,[]),(131,[]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock221 : ∃ data, checkBlock 221 data = true :=
  ⟨[(189,[]),(131,[]),(139,[]),(147,[]),(131,[]),
    (12,[2,3,7,19,277]),(171,[]),(131,[]),(2,[2,3,36847]),(10,[2,110543]),
    (131,[]),(255,[]),(135,[]),(131,[]),(141,[]),
    (409,[]),(131,[]),(195,[]),(157,[]),(131,[]),
    (2,[2,3,3,12289]),(135,[]),(131,[]),(2,[2,3,36871]),(139,[]),
    (131,[]),(135,[]),(301,[]),(131,[]),(139,[]),
    (10,[2,110651]),(131,[]),(145,[]),(13,[2,7,15809]),(131,[]),
    (135,[]),(309,[]),(131,[]),(235,[]),(397,[]),
    (131,[]),(147,[]),(307,[]),(131,[]),(357,[]),
    (13,[2,263,421]),(131,[]),(151,[]),(147,[]),(131,[]),
    (487,[]),(139,[]),(131,[]),(145,[]),(135,[]),
    (131,[]),(277,[]),(10,[2,139,797]),(131,[]),(18,[2,3,36931]),
    (5,[2,179,619]),(131,[]),(5,[2,3,43,859]),(135,[]),(131,[]),
    (157,[]),(141,[]),(131,[]),(135,[]),(169,[]),
    (131,[]),(2,[2,3,3,109,113]),(5,[2,59,1879]),(131,[]),(151,[]),
    (5,[2,7,47,337]),(131,[]),(135,[]),(259,[]),(131,[]),
    (265,[]),(19,[2,13,19,449]),(131,[]),(2,[2,3,11,3361]),(291,[]),
    (131,[]),(147,[]),(145,[]),(131,[]),(175,[]),
    (139,[]),(131,[]),(141,[]),(151,[]),(131,[]),
    (139,[]),(135,[]),(131,[]),(267,[]),(14,[2,17,6529])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock222 : ∃ data, checkBlock 222 data = true :=
  ⟨[(131,[]),(10,[2,3,163,227]),(14,[2,31,3581]),(131,[]),(2,[2,3,23,1609]),
    (135,[]),(131,[]),(22,[2,3,3,13,13,73]),(465,[]),(131,[]),
    (135,[]),(5,[2,111053]),(131,[]),(19,[2,3,37021]),(321,[]),
    (131,[]),(2,[2,3,61,607]),(139,[]),(131,[]),(135,[]),
    (151,[]),(131,[]),(189,[]),(157,[]),(131,[]),
    (10,[2,3,3,12347]),(175,[]),(131,[]),(327,[]),(141,[]),
    (131,[]),(259,[]),(5,[2,89,1249]),(131,[]),(139,[]),
    (5,[2,107,1039]),(131,[]),(12,[2,3,37061]),(135,[]),(131,[]),
    (11,[2,3,101,367]),(165,[]),(131,[]),(475,[]),(141,[]),
    (131,[]),(397,[]),(135,[]),(131,[]),(159,[]),
    (229,[]),(131,[]),(135,[]),(13,[2,111263]),(131,[]),
    (141,[]),(139,[]),(131,[]),(231,[]),(5,[2,7,13,1223]),
    (131,[]),(135,[]),(147,[]),(131,[]),(2,[2,3,3,3,7,19,31]),
    (19,[2,111323]),(131,[]),(235,[]),(145,[]),(131,[]),
    (141,[]),(5,[2,11,53,191]),(131,[]),(199,[]),(481,[]),
    (131,[]),(459,[]),(217,[]),(131,[]),(2,[2,3,3,12377]),
    (135,[]),(131,[]),(5,[2,3,3,12379]),(139,[]),(131,[]),
    (151,[]),(10,[2,111431]),(131,[]),(11,[2,3,11,11,307]),(135,[]),
    (131,[]),(229,[]),(157,[]),(131,[]),(135,[]),
    (5,[2,19,5867]),(131,[]),(33,[2,3,3,3,4129]),(159,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock223 : ∃ data, checkBlock 223 data = true :=
  ⟨[(139,[]),(13,[2,7,17,937]),(131,[]),(135,[]),(195,[]),
    (131,[]),(11,[2,3,7,47,113]),(141,[]),(131,[]),(13,[2,3,37181]),
    (10,[2,11,10141]),(131,[]),(151,[]),(171,[]),(131,[]),
    (165,[]),(169,[]),(131,[]),(181,[]),(211,[]),
    (131,[]),(5,[2,3,37201]),(135,[]),(131,[]),(11,[2,3,29,1283]),
    (19,[2,111623]),(131,[]),(139,[]),(5,[2,111641]),(131,[]),
    (12,[2,3,37217]),(135,[]),(131,[]),(141,[]),(301,[]),
    (131,[]),(135,[]),(10,[2,11,11,13,71]),(131,[]),(157,[]),
    (5,[2,19,5879]),(131,[]),(5,[2,3,23,1619]),(501,[]),(131,[]),
    (135,[]),(10,[2,111731]),(131,[]),(141,[]),(139,[]),
    (131,[]),(43,[2,3,3,3,4139]),(235,[]),(131,[]),(57,[2,3,3,11,1129]),
    (5,[2,111773]),(131,[]),(145,[]),(151,[]),(131,[]),
    (159,[]),(181,[]),(131,[]),(241,[]),(135,[]),
    (131,[]),(139,[]),(5,[2,111833]),(131,[]),(147,[]),
    (145,[]),(131,[]),(537,[]),(135,[]),(131,[]),
    (2,[2,3,89,419]),(147,[]),(131,[]),(135,[]),(187,[]),
    (131,[]),(207,[]),(39,[2,17,29,227]),(131,[]),(11,[2,3,37307]),
    (141,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (6,[2,3,3,7,1777]),(145,[]),(131,[]),(139,[]),(367,[]),
    (131,[]),(38,[2,3,163,229]),(157,[]),(131,[]),(171,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock224 : ∃ data, checkBlock 224 data = true :=
  ⟨[(141,[]),(131,[]),(187,[]),(5,[2,11,17,599]),(131,[]),
    (5,[2,3,3,3,3,3,461]),(135,[]),(131,[]),(157,[]),(459,[]),
    (131,[]),(141,[]),(207,[]),(131,[]),(147,[]),
    (135,[]),(131,[]),(225,[]),(165,[]),(131,[]),
    (135,[]),(267,[]),(131,[]),(151,[]),(181,[]),
    (131,[]),(141,[]),(5,[2,7,83,193]),(131,[]),(135,[]),
    (14,[2,13,8627]),(131,[]),(139,[]),(10,[2,112163]),(131,[]),
    (159,[]),(5,[2,112181]),(131,[]),(145,[]),(585,[]),
    (131,[]),(477,[]),(10,[2,11,101,101]),(131,[]),(2,[2,3,3,37,337]),
    (147,[]),(131,[]),(2,[2,3,11,19,179]),(135,[]),(131,[]),
    (151,[]),(589,[]),(131,[]),(19,[2,3,23,1627]),(139,[]),
    (131,[]),(11,[2,3,13,2879]),(135,[]),(131,[]),(139,[]),
    (7,[2,7,61,263]),(131,[]),(135,[]),(141,[]),(131,[]),
    (405,[]),(157,[]),(131,[]),(37,[2,3,37447]),(151,[]),
    (131,[]),(135,[]),(145,[]),(131,[]),(19,[2,3,7,5351]),
    (507,[]),(131,[]),(201,[]),(141,[]),(131,[]),
    (169,[]),(139,[]),(131,[]),(147,[]),(159,[]),
    (131,[]),(5,[2,3,11,3407]),(237,[]),(131,[]),(141,[]),
    (135,[]),(131,[]),(165,[]),(145,[]),(131,[]),
    (2,[2,3,3,12497]),(151,[]),(131,[]),(139,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock225 : ∃ data, checkBlock 225 data = true :=
  ⟨[(131,[]),(351,[]),(13,[2,7,16073]),(131,[]),(135,[]),
    (441,[]),(131,[]),(2,[2,3,37511]),(175,[]),(131,[]),
    (291,[]),(357,[]),(131,[]),(135,[]),(14,[2,112571]),
    (131,[]),(11,[2,3,3,7,1787]),(19,[2,112583]),(131,[]),(195,[]),
    (139,[]),(131,[]),(11,[2,3,37537]),(5,[2,19,5927]),(131,[]),
    (139,[]),(10,[2,23,59,83]),(131,[]),(147,[]),(19,[2,112643]),
    (131,[]),(2,[2,3,3,12517]),(135,[]),(131,[]),(23,[2,3,3,3,3,13,107]),
    (5,[2,11,10243]),(131,[]),(165,[]),(10,[2,112691]),(131,[]),
    (145,[]),(135,[]),(131,[]),(2,[2,3,37571]),(279,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(571,[]),
    (10,[2,137,823]),(131,[]),(37,[2,3,3,11,17,67]),(14,[2,7,89,181]),(131,[]),
    (135,[]),(141,[]),(131,[]),(28,[2,3,7,41,131]),(147,[]),
    (131,[]),(145,[]),(169,[]),(131,[]),(139,[]),
    (175,[]),(131,[]),(141,[]),(5,[2,19,5939]),(131,[]),
    (207,[]),(157,[]),(131,[]),(181,[]),(135,[]),
    (131,[]),(529,[]),(10,[2,157,719]),(131,[]),(169,[]),
    (477,[]),(131,[]),(141,[]),(135,[]),(131,[]),
    (577,[]),(139,[]),(131,[]),(135,[]),(241,[]),
    (131,[]),(139,[]),(285,[]),(131,[]),(5,[2,3,37657]),
    (145,[]),(131,[]),(135,[]),(14,[2,103,1097]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock226 : ∃ data, checkBlock 226 data = true :=
  ⟨[(321,[]),(22,[2,11,10273]),(131,[]),(32,[2,3,3,29,433]),(147,[]),
    (131,[]),(5,[2,3,3,19,661]),(151,[]),(131,[]),(11,[2,3,7,7,769]),
    (10,[2,113051]),(131,[]),(30,[2,3,13,13,223]),(139,[]),(131,[]),
    (187,[]),(135,[]),(131,[]),(5,[2,3,11,23,149]),(141,[]),
    (131,[]),(159,[]),(171,[]),(131,[]),(361,[]),
    (135,[]),(131,[]),(13,[2,3,43,877]),(5,[2,7,7,2309]),(131,[]),
    (135,[]),(5,[2,113153]),(131,[]),(217,[]),(141,[]),
    (131,[]),(181,[]),(10,[2,7,19,23,37]),(131,[]),(135,[]),
    (157,[]),(131,[]),(145,[]),(5,[2,113213]),(131,[]),
    (141,[]),(29,[2,199,569]),(131,[]),(11,[2,3,37747]),(14,[2,13,31,281]),
    (131,[]),(211,[]),(139,[]),(131,[]),(229,[]),
    (5,[2,227,499]),(131,[]),(139,[]),(135,[]),(131,[]),
    (141,[]),(169,[]),(131,[]),(145,[]),(6,[2,13,23,379]),
    (131,[]),(5,[2,3,37,1021]),(135,[]),(131,[]),(525,[]),
    (159,[]),(131,[]),(135,[]),(147,[]),(131,[]),
    (325,[]),(145,[]),(131,[]),(23,[2,3,3,43,293]),(139,[]),
    (131,[]),(135,[]),(14,[2,19,47,127]),(131,[]),(12,[2,3,7,11,491]),
    (165,[]),(131,[]),(157,[]),(225,[]),(131,[]),
    (5,[2,3,13,2909]),(5,[2,113453]),(131,[]),(277,[]),(19,[2,233,487]),
    (131,[]),(139,[]),(141,[]),(131,[]),(151,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock227 : ∃ data, checkBlock 227 data = true :=
  ⟨[(135,[]),(131,[]),(259,[]),(5,[2,113513]),(131,[]),
    (237,[]),(195,[]),(131,[]),(171,[]),(135,[]),
    (131,[]),(147,[]),(141,[]),(131,[]),(135,[]),
    (5,[2,137,829]),(131,[]),(12,[2,3,37861]),(139,[]),(131,[]),
    (255,[]),(13,[2,7,16229]),(131,[]),(135,[]),(241,[]),
    (131,[]),(151,[]),(5,[2,13,8741]),(131,[]),(295,[]),
    (19,[2,29,3919]),(131,[]),(159,[]),(187,[]),(131,[]),
    (189,[]),(5,[2,79,1439]),(131,[]),(141,[]),(5,[2,41,47,59]),
    (131,[]),(5,[2,3,151,251]),(135,[]),(131,[]),(145,[]),
    (139,[]),(131,[]),(30,[2,3,3,12637]),(237,[]),(131,[]),
    (211,[]),(135,[]),(131,[]),(175,[]),(267,[]),
    (131,[]),(135,[]),(13,[2,113783]),(131,[]),(165,[]),
    (5,[2,31,3671]),(131,[]),(139,[]),(5,[2,7,71,229]),(131,[]),
    (135,[]),(13,[2,89,1279]),(131,[]),(351,[]),(201,[]),
    (131,[]),(2,[2,3,37951]),(151,[]),(131,[]),(42,[2,3,37957]),
    (141,[]),(131,[]),(367,[]),(145,[]),(131,[]),
    (235,[]),(285,[]),(131,[]),(29,[2,3,3,3,4219]),(135,[]),
    (131,[]),(319,[]),(147,[]),(131,[]),(139,[]),
    (141,[]),(131,[]),(445,[]),(135,[]),(131,[]),
    (11,[2,3,37991]),(439,[]),(131,[]),(135,[]),(145,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock228 : ∃ data, checkBlock 228 data = true :=
  ⟨[(131,[]),(141,[]),(10,[2,23,4957]),(131,[]),(585,[]),
    (225,[]),(131,[]),(135,[]),(169,[]),(131,[]),
    (5,[2,3,7,5431]),(139,[]),(131,[]),(5,[2,3,193,197]),(157,[]),
    (131,[]),(141,[]),(211,[]),(131,[]),(301,[]),
    (14,[2,13,67,131]),(131,[]),(13,[2,3,3,31,409]),(369,[]),(131,[]),
    (147,[]),(135,[]),(131,[]),(139,[]),(171,[]),
    (131,[]),(17,[2,3,13,2927]),(147,[]),(131,[]),(517,[]),
    (135,[]),(131,[]),(151,[]),(10,[2,7,11,1483]),(131,[]),
    (135,[]),(199,[]),(131,[]),(2,[2,3,11,3461]),(5,[2,114221]),
    (131,[]),(145,[]),(175,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(28,[2,3,7,5441]),(141,[]),(131,[]),
    (139,[]),(159,[]),(131,[]),(307,[]),(5,[2,37,3089]),
    (131,[]),(157,[]),(165,[]),(131,[]),(151,[]),
    (10,[2,11,19,547]),(131,[]),(145,[]),(135,[]),(131,[]),
    (147,[]),(5,[2,173,661]),(131,[]),(255,[]),(187,[]),
    (131,[]),(231,[]),(135,[]),(131,[]),(141,[]),
    (145,[]),(131,[]),(135,[]),(151,[]),(131,[]),
    (10,[2,3,43,887]),(207,[]),(131,[]),(12,[2,3,37,1031]),(14,[2,7,16349]),
    (131,[]),(135,[]),(5,[2,17,6733]),(131,[]),(139,[]),
    (411,[]),(131,[]),(229,[]),(34,[2,13,8807]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock229 : ∃ data, checkBlock 229 data = true :=
  ⟨[(2,[2,3,38167]),(145,[]),(131,[]),(32,[2,3,7,7,19,41]),(355,[]),
    (131,[]),(285,[]),(165,[]),(131,[]),(235,[]),
    (135,[]),(131,[]),(11,[2,3,3,3,4243]),(19,[2,17,23,293]),(131,[]),
    (171,[]),(139,[]),(131,[]),(159,[]),(135,[]),
    (131,[]),(139,[]),(10,[2,7,7,2339]),(131,[]),(135,[]),
    (13,[2,83,1381]),(131,[]),(11,[2,3,3,47,271]),(5,[2,114641]),(131,[]),
    (157,[]),(141,[]),(131,[]),(135,[]),(10,[2,114671]),
    (131,[]),(165,[]),(475,[]),(131,[]),(147,[]),
    (5,[2,23,4987]),(131,[]),(40,[2,3,38237]),(139,[]),(131,[]),
    (327,[]),(141,[]),(131,[]),(145,[]),(10,[2,114743]),
    (131,[]),(20,[2,3,29,1319]),(135,[]),(131,[]),(181,[]),
    (5,[2,114773]),(131,[]),(141,[]),(19,[2,191,601]),(131,[]),
    (139,[]),(135,[]),(131,[]),(2,[2,3,3,12757]),(259,[]),
    (131,[]),(135,[]),(291,[]),(131,[]),(145,[]),
    (22,[2,11,53,197]),(131,[]),(141,[]),(10,[2,7,61,269]),(131,[]),
    (135,[]),(5,[2,13,8837]),(131,[]),(175,[]),(189,[]),
    (131,[]),(165,[]),(139,[]),(131,[]),(147,[]),
    (13,[2,41,2803]),(131,[]),(139,[]),(157,[]),(131,[]),
    (6,[2,3,38317]),(277,[]),(131,[]),(159,[]),(135,[]),
    (131,[]),(21,[2,3,38327]),(181,[]),(131,[]),(225,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock230 : ∃ data, checkBlock 230 data = true :=
  ⟨[(5,[2,115001]),(131,[]),(151,[]),(135,[]),(131,[]),
    (21,[2,3,23,1667]),(10,[2,7,16433]),(131,[]),(135,[]),(139,[]),
    (131,[]),(19,[2,3,38351]),(5,[2,115061]),(131,[]),(5,[2,3,11,11,317]),
    (147,[]),(131,[]),(135,[]),(511,[]),(131,[]),
    (17,[2,3,3,3,3,7,7,29]),(151,[]),(131,[]),(58,[2,3,38371]),(141,[]),
    (131,[]),(139,[]),(537,[]),(131,[]),(549,[]),
    (19,[2,115151]),(131,[]),(267,[]),(10,[2,115163]),(131,[]),
    (141,[]),(135,[]),(131,[]),(53,[2,3,3,12799]),(5,[2,13,8861]),
    (131,[]),(241,[]),(159,[]),(131,[]),(207,[]),
    (135,[]),(131,[]),(18,[2,3,71,541]),(139,[]),(131,[]),
    (135,[]),(5,[2,23,5011]),(131,[]),(139,[]),(169,[]),
    (131,[]),(30,[2,3,3,12809]),(14,[2,7,43,383]),(131,[]),(135,[]),
    (147,[]),(131,[]),(339,[]),(295,[]),(131,[]),
    (23,[2,3,13,2957]),(10,[2,115331]),(131,[]),(12,[2,3,38447]),(325,[]),
    (131,[]),(145,[]),(175,[]),(131,[]),(5,[2,3,3,3,4273]),
    (139,[]),(131,[]),(11,[2,3,38461]),(135,[]),(131,[]),
    (571,[]),(22,[2,37,3119]),(131,[]),(58,[2,3,17,31,73]),(145,[]),
    (131,[]),(20,[2,3,109,353]),(135,[]),(131,[]),(501,[]),
    (361,[]),(131,[]),(135,[]),(157,[]),(131,[]),
    (285,[]),(199,[]),(131,[]),(147,[]),(229,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock231 : ∃ data, checkBlock 231 data = true :=
  ⟨[(131,[]),(135,[]),(141,[]),(131,[]),(157,[]),
    (145,[]),(131,[]),(37,[2,3,3,3,11,389]),(195,[]),(131,[]),
    (187,[]),(5,[2,115553]),(131,[]),(141,[]),(139,[]),
    (131,[]),(399,[]),(159,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(10,[2,3,89,433]),(235,[]),(131,[]),
    (199,[]),(409,[]),(131,[]),(141,[]),(135,[]),
    (131,[]),(441,[]),(18,[2,7,13,31,41]),(131,[]),(135,[]),
    (5,[2,131,883]),(131,[]),(10,[2,3,38561]),(171,[]),(131,[]),
    (151,[]),(139,[]),(131,[]),(135,[]),(5,[2,97,1193]),
    (131,[]),(6,[2,3,3,7,11,167]),(339,[]),(131,[]),(211,[]),
    (19,[2,115751]),(131,[]),(145,[]),(169,[]),(131,[]),
    (17,[2,3,7,37,149]),(5,[2,115781]),(131,[]),(139,[]),(151,[]),
    (131,[]),(38,[2,3,3,3,4289]),(135,[]),(131,[]),(11,[2,3,3,17,757]),
    (141,[]),(131,[]),(147,[]),(319,[]),(131,[]),
    (391,[]),(135,[]),(131,[]),(145,[]),(147,[]),
    (131,[]),(135,[]),(355,[]),(131,[]),(159,[]),
    (139,[]),(131,[]),(10,[2,3,3,3,3,3,3,3,53]),(6,[2,7,29,571]),(131,[]),
    (135,[]),(145,[]),(131,[]),(589,[]),(195,[]),
    (131,[]),(141,[]),(5,[2,61,1901]),(131,[]),(5,[2,3,29,31,43]),
    (7,[2,11,13,811]),(131,[]),(40,[2,3,3,7,7,263]),(189,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock232 : ∃ data, checkBlock 232 data = true :=
  ⟨[(12,[2,3,3,12889]),(19,[2,311,373]),(131,[]),(165,[]),(135,[]),
    (131,[]),(141,[]),(139,[]),(131,[]),(157,[]),
    (10,[2,13,79,113]),(131,[]),(147,[]),(135,[]),(131,[]),
    (397,[]),(307,[]),(131,[]),(135,[]),(5,[2,17,6829]),
    (131,[]),(65,[2,3,13,13,229]),(309,[]),(131,[]),(139,[]),
    (399,[]),(131,[]),(135,[]),(159,[]),(131,[]),
    (13,[2,3,7,5531]),(5,[2,41,2833]),(131,[]),(507,[]),(411,[]),
    (131,[]),(20,[2,3,3,3,13,331]),(10,[2,223,521]),(131,[]),(409,[]),
    (405,[]),(131,[]),(195,[]),(141,[]),(131,[]),
    (319,[]),(135,[]),(131,[]),(211,[]),(30,[2,116243]),
    (131,[]),(139,[]),(6,[2,19,29,211]),(131,[]),(145,[]),
    (135,[]),(131,[]),(10,[2,3,83,467]),(141,[]),(131,[]),
    (135,[]),(10,[2,11,97,109]),(131,[]),(481,[]),(5,[2,293,397]),
    (131,[]),(12,[2,3,17,2281]),(157,[]),(131,[]),(135,[]),
    (225,[]),(131,[]),(181,[]),(139,[]),(131,[]),
    (145,[]),(265,[]),(131,[]),(151,[]),(259,[]),
    (131,[]),(147,[]),(19,[2,116411]),(131,[]),(141,[]),
    (45,[2,116423]),(131,[]),(465,[]),(135,[]),(131,[]),
    (139,[]),(5,[2,101,1153]),(131,[]),(291,[]),(201,[]),
    (131,[]),(11,[2,3,41,947]),(135,[]),(131,[]),(2,[2,3,13,29,103])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock233 : ∃ data, checkBlock 233 data = true :=
  ⟨[(169,[]),(131,[]),(135,[]),(159,[]),(131,[]),
    (369,[]),(165,[]),(131,[]),(11,[2,3,3,23,563]),(145,[]),
    (131,[]),(135,[]),(139,[]),(131,[]),(44,[2,3,7,7,13,61]),
    (181,[]),(131,[]),(139,[]),(10,[2,31,3761]),(131,[]),
    (189,[]),(141,[]),(131,[]),(187,[]),(151,[]),
    (131,[]),(147,[]),(13,[2,11,23,461]),(131,[]),(207,[]),
    (135,[]),(131,[]),(20,[2,3,37,1051]),(19,[2,116663]),(131,[]),
    (2,[2,3,38891]),(141,[]),(131,[]),(547,[]),(135,[]),
    (131,[]),(10,[2,3,3,12967]),(10,[2,7,16673]),(131,[]),(135,[]),
    (171,[]),(131,[]),(141,[]),(277,[]),(131,[]),
    (367,[]),(165,[]),(131,[]),(135,[]),(175,[]),
    (131,[]),(139,[]),(147,[]),(131,[]),(237,[]),
    (207,[]),(131,[]),(141,[]),(435,[]),(131,[]),
    (159,[]),(10,[2,11,13,19,43]),(131,[]),(2,[2,3,17,29,79]),(10,[2,331,353]),
    (131,[]),(231,[]),(135,[]),(131,[]),(5,[2,3,163,239]),
    (5,[2,73,1601]),(131,[]),(145,[]),(139,[]),(131,[]),
    (165,[]),(135,[]),(131,[]),(139,[]),(507,[]),
    (131,[]),(135,[]),(225,[]),(131,[]),(151,[]),
    (145,[]),(131,[]),(67,[2,3,13,2999]),(351,[]),(131,[]),
    (135,[]),(171,[]),(131,[]),(5,[2,3,3,3,7,619]),(141,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock234 : ∃ data, checkBlock 234 data = true :=
  ⟨[(131,[]),(51,[2,3,43,907]),(147,[]),(131,[]),(50,[2,3,19,2053]),
    (139,[]),(131,[]),(18,[2,3,7,5573]),(5,[2,117041]),(131,[]),
    (10,[2,3,11,3547]),(145,[]),(131,[]),(385,[]),(135,[]),
    (131,[]),(151,[]),(19,[2,191,613]),(131,[]),(12,[2,3,23,1697]),
    (5,[2,117101]),(131,[]),(139,[]),(135,[]),(131,[]),
    (141,[]),(445,[]),(131,[]),(135,[]),(10,[2,13,9011]),
    (131,[]),(171,[]),(13,[2,11,10651]),(131,[]),(12,[2,3,3,47,277]),
    (151,[]),(131,[]),(135,[]),(13,[2,117191]),(131,[]),
    (141,[]),(157,[]),(131,[]),(487,[]),(139,[]),
    (131,[]),(5,[2,3,23,1699]),(5,[2,59,1987]),(131,[]),(139,[]),
    (279,[]),(131,[]),(157,[]),(34,[2,149,787]),(131,[]),
    (43,[2,3,13,31,97]),(135,[]),(131,[]),(145,[]),(5,[2,11,10663]),
    (131,[]),(411,[]),(151,[]),(131,[]),(169,[]),
    (135,[]),(131,[]),(189,[]),(5,[2,7,16763]),(131,[]),
    (135,[]),(139,[]),(131,[]),(10,[2,3,19,29,71]),(10,[2,117371]),
    (131,[]),(159,[]),(141,[]),(131,[]),(135,[]),
    (6,[2,19,37,167]),(131,[]),(171,[]),(577,[]),(131,[]),
    (12,[2,3,3,3,4349]),(19,[2,117431]),(131,[]),(139,[]),(159,[]),
    (131,[]),(33,[2,3,7,7,17,47]),(141,[]),(131,[]),(231,[]),
    (5,[2,79,1487]),(131,[]),(20,[2,3,39161]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock235 : ∃ data, checkBlock 235 data = true :=
  ⟨[(18,[2,3,53,739]),(10,[2,117503]),(131,[]),(141,[]),(5,[2,17,31,223]),
    (131,[]),(441,[]),(135,[]),(131,[]),(147,[]),
    (139,[]),(131,[]),(135,[]),(145,[]),(131,[]),
    (139,[]),(147,[]),(131,[]),(141,[]),(379,[]),
    (131,[]),(135,[]),(199,[]),(131,[]),(2,[2,3,3,7,1867]),
    (495,[]),(131,[]),(151,[]),(165,[]),(131,[]),
    (295,[]),(7,[2,29,4057]),(131,[]),(267,[]),(285,[]),
    (131,[]),(501,[]),(139,[]),(131,[]),(529,[]),
    (135,[]),(131,[]),(175,[]),(439,[]),(131,[]),
    (5,[2,3,39241]),(169,[]),(131,[]),(18,[2,3,13,3019]),(135,[]),
    (131,[]),(159,[]),(5,[2,7,16823]),(131,[]),(135,[]),
    (141,[]),(131,[]),(157,[]),(217,[]),(131,[]),
    (145,[]),(10,[2,7,16829]),(131,[]),(135,[]),(189,[]),
    (131,[]),(5,[2,3,7,31,181]),(591,[]),(131,[]),(339,[]),
    (141,[]),(131,[]),(2,[2,3,17,2311]),(151,[]),(131,[]),
    (45,[2,3,3,7,1871]),(139,[]),(131,[]),(10,[2,3,3,13099]),(5,[2,31,3803]),
    (131,[]),(139,[]),(135,[]),(131,[]),(309,[]),
    (147,[]),(131,[]),(277,[]),(267,[]),(131,[]),
    (181,[]),(135,[]),(131,[]),(5,[2,3,3,3,17,257]),(145,[]),
    (131,[]),(135,[]),(14,[2,127,929]),(131,[]),(175,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock236 : ∃ data, checkBlock 236 data = true :=
  ⟨[(151,[]),(131,[]),(165,[]),(139,[]),(131,[]),
    (135,[]),(19,[2,17,53,131]),(131,[]),(435,[]),(10,[2,118043]),
    (131,[]),(11,[2,3,3,13,1009]),(517,[]),(131,[]),(19,[2,3,3,3,4373]),
    (145,[]),(131,[]),(40,[2,3,7,5623]),(385,[]),(131,[]),
    (139,[]),(10,[2,89,1327]),(131,[]),(147,[]),(135,[]),
    (131,[]),(157,[]),(319,[]),(131,[]),(5,[2,3,3,13127]),
    (147,[]),(131,[]),(20,[2,3,3,19,691]),(135,[]),(131,[]),
    (255,[]),(175,[]),(131,[]),(135,[]),(5,[2,181,653]),
    (131,[]),(5,[2,3,31,31,41]),(139,[]),(131,[]),(195,[]),
    (169,[]),(131,[]),(135,[]),(141,[]),(131,[]),
    (12,[2,3,3,7,1877]),(5,[2,118253]),(131,[]),(12,[2,3,79,499]),(171,[]),
    (131,[]),(2,[2,3,89,443]),(309,[]),(131,[]),(141,[]),
    (351,[]),(131,[]),(145,[]),(5,[2,13,19,479]),(131,[]),
    (151,[]),(135,[]),(131,[]),(147,[]),(139,[]),
    (131,[]),(2,[2,3,39451]),(5,[2,118361]),(131,[]),(141,[]),
    (135,[]),(131,[]),(187,[]),(19,[2,7,13,1301]),(131,[]),
    (135,[]),(14,[2,167,709]),(131,[]),(145,[]),(157,[]),
    (131,[]),(139,[]),(5,[2,7,7,2417]),(131,[]),(135,[]),
    (369,[]),(131,[]),(151,[]),(175,[]),(131,[]),
    (28,[2,3,17,23,101]),(145,[]),(131,[]),(5,[2,3,127,311]),(147,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock237 : ∃ data, checkBlock 237 data = true :=
  ⟨[(131,[]),(217,[]),(549,[]),(131,[]),(11,[2,3,3,13,1013]),
    (229,[]),(131,[]),(18,[2,3,39511]),(135,[]),(131,[]),
    (169,[]),(141,[]),(131,[]),(139,[]),(10,[2,118571]),
    (131,[]),(2,[2,3,29,29,47]),(135,[]),(131,[]),(241,[]),
    (5,[2,7,16943]),(131,[]),(135,[]),(285,[]),(131,[]),
    (195,[]),(141,[]),(131,[]),(12,[2,3,71,557]),(13,[2,7,17,997]),
    (131,[]),(135,[]),(201,[]),(131,[]),(13,[2,3,7,5651]),
    (139,[]),(131,[]),(141,[]),(151,[]),(131,[]),
    (171,[]),(327,[]),(131,[]),(361,[]),(147,[]),
    (131,[]),(211,[]),(5,[2,37,3209]),(131,[]),(19,[2,3,39581]),
    (135,[]),(131,[]),(139,[]),(397,[]),(131,[]),
    (17,[2,3,3,3,53,83]),(5,[2,13,9137]),(131,[]),(321,[]),(135,[]),
    (131,[]),(12,[2,3,199,199]),(421,[]),(131,[]),(135,[]),
    (235,[]),(131,[]),(399,[]),(5,[2,23,5167]),(131,[]),
    (595,[]),(7,[2,7,16979]),(131,[]),(135,[]),(139,[]),
    (131,[]),(19,[2,3,3,3,7,17,37]),(19,[2,19,6257]),(131,[]),(139,[]),
    (525,[]),(131,[]),(147,[]),(231,[]),(131,[]),
    (145,[]),(159,[]),(131,[]),(33,[2,3,41,967]),(141,[]),
    (131,[]),(201,[]),(135,[]),(131,[]),(405,[]),
    (165,[]),(131,[]),(5,[2,3,17,2333]),(145,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock238 : ∃ data, checkBlock 238 data = true :=
  ⟨[(157,[]),(135,[]),(131,[]),(151,[]),(141,[]),
    (131,[]),(135,[]),(445,[]),(131,[]),(169,[]),
    (39,[2,17,47,149]),(131,[]),(355,[]),(147,[]),(131,[]),
    (135,[]),(5,[2,193,617]),(131,[]),(139,[]),(145,[]),
    (131,[]),(40,[2,3,29,37,37]),(19,[2,19,6269]),(131,[]),(165,[]),
    (10,[2,139,857]),(131,[]),(69,[2,3,3,7,31,61]),(367,[]),(131,[]),
    (141,[]),(14,[2,17,43,163]),(131,[]),(189,[]),(135,[]),
    (131,[]),(2,[2,3,39727]),(477,[]),(131,[]),(351,[]),
    (139,[]),(131,[]),(43,[2,3,79,503]),(135,[]),(131,[]),
    (139,[]),(14,[2,7,17033]),(131,[]),(135,[]),(151,[]),
    (131,[]),(147,[]),(225,[]),(131,[]),(241,[]),
    (5,[2,7,11,1549]),(131,[]),(135,[]),(147,[]),(131,[]),
    (397,[]),(159,[]),(131,[]),(2,[2,3,3,3,3,3,491]),(295,[]),
    (131,[]),(145,[]),(139,[]),(131,[]),(165,[]),
    (10,[2,41,41,71]),(131,[]),(2,[2,3,11,3617]),(10,[2,119363]),(131,[]),
    (12,[2,3,39791]),(135,[]),(131,[]),(201,[]),(217,[]),
    (131,[]),(175,[]),(141,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(145,[]),(5,[2,7,113,151]),(131,[]),
    (135,[]),(169,[]),(131,[]),(141,[]),(10,[2,11,10861]),
    (131,[]),(147,[]),(10,[2,7,13,13,101]),(131,[]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock239 : ∃ data, checkBlock 239 data = true :=
  ⟨[(145,[]),(131,[]),(10,[2,3,3,7,7,271]),(5,[2,119513]),(131,[]),
    (157,[]),(139,[]),(131,[]),(141,[]),(14,[2,173,691]),
    (131,[]),(139,[]),(171,[]),(131,[]),(217,[]),
    (5,[2,109,1097]),(131,[]),(20,[2,3,3,3,43,103]),(135,[]),(131,[]),
    (379,[]),(145,[]),(131,[]),(159,[]),(5,[2,37,53,61]),
    (131,[]),(5,[2,3,39877]),(135,[]),(131,[]),(10,[2,3,19,2099]),
    (189,[]),(131,[]),(135,[]),(139,[]),(131,[]),
    (2,[2,3,3,13297]),(187,[]),(131,[]),(68,[2,3,3,3,11,13,31]),(5,[2,7,17099]),
    (131,[]),(135,[]),(13,[2,59,2029]),(131,[]),(277,[]),
    (141,[]),(131,[]),(171,[]),(199,[]),(131,[]),
    (139,[]),(181,[]),(131,[]),(12,[2,3,3,7,1901]),(29,[2,119771]),
    (131,[]),(169,[]),(10,[2,119783]),(131,[]),(17,[2,3,73,547]),
    (135,[]),(131,[]),(5,[2,3,39937]),(157,[]),(131,[]),
    (147,[]),(571,[]),(131,[]),(145,[]),(135,[]),
    (131,[]),(141,[]),(139,[]),(131,[]),(135,[]),
    (175,[]),(131,[]),(139,[]),(10,[2,119891]),(131,[]),
    (11,[2,3,17,2351]),(14,[2,7,7,2447]),(131,[]),(135,[]),(5,[2,119921]),
    (131,[]),(141,[]),(151,[]),(131,[]),(145,[]),
    (255,[]),(131,[]),(207,[]),(195,[]),(131,[]),
    (2,[2,3,7,29,197]),(5,[2,119981]),(131,[]),(171,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock240 : ∃ data, checkBlock 240 data = true :=
  ⟨[(131,[]),(10,[2,3,13,17,181]),(135,[]),(131,[]),(12,[2,3,11,3637]),
    (10,[2,19,6317]),(131,[]),(559,[]),(537,[]),(131,[]),
    (147,[]),(135,[]),(131,[]),(237,[]),(151,[]),
    (131,[]),(135,[]),(165,[]),(131,[]),(309,[]),
    (5,[2,83,1447]),(131,[]),(361,[]),(141,[]),(131,[]),
    (135,[]),(10,[2,11,67,163]),(131,[]),(17,[2,3,3,7,1907]),(10,[2,317,379]),
    (131,[]),(187,[]),(157,[]),(131,[]),(159,[]),
    (5,[2,17,7069]),(131,[]),(285,[]),(139,[]),(131,[]),
    (439,[]),(147,[]),(131,[]),(139,[]),(135,[]),
    (131,[]),(165,[]),(159,[]),(131,[]),(141,[]),
    (14,[2,19,6329]),(131,[]),(189,[]),(135,[]),(131,[]),
    (169,[]),(237,[]),(131,[]),(135,[]),(5,[2,120293]),
    (131,[]),(5,[2,3,3,13367]),(10,[2,31,3881]),(131,[]),(141,[]),
    (139,[]),(131,[]),(135,[]),(229,[]),(131,[]),
    (145,[]),(5,[2,61,1973]),(131,[]),(6,[2,3,53,757]),(29,[2,120371]),
    (131,[]),(34,[2,3,40127]),(189,[]),(131,[]),(147,[]),
    (241,[]),(131,[]),(139,[]),(201,[]),(131,[]),
    (355,[]),(135,[]),(131,[]),(11,[2,3,19,2113]),(267,[]),
    (131,[]),(145,[]),(217,[]),(131,[]),(23,[2,3,13,3089]),
    (135,[]),(131,[]),(5,[2,3,3,11,1217]),(265,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock241 : ∃ data, checkBlock 241 data = true :=
  ⟨[(135,[]),(141,[]),(131,[]),(2,[2,3,17,17,139]),(139,[]),
    (131,[]),(151,[]),(5,[2,7,67,257]),(131,[]),(135,[]),
    (589,[]),(131,[]),(231,[]),(19,[2,120563]),(131,[]),
    (279,[]),(141,[]),(131,[]),(5,[2,3,3,13399]),(171,[]),
    (131,[]),(5,[2,3,7,5743]),(591,[]),(131,[]),(147,[]),
    (145,[]),(131,[]),(141,[]),(135,[]),(131,[]),
    (5,[2,3,131,307]),(139,[]),(131,[]),(5,[2,3,3,3,41,109]),(10,[2,120671]),
    (131,[]),(2,[2,3,3,11,23,53]),(135,[]),(131,[]),(327,[]),
    (291,[]),(131,[]),(135,[]),(255,[]),(131,[]),
    (211,[]),(19,[2,13,37,251]),(131,[]),(139,[]),(187,[]),
    (131,[]),(135,[]),(151,[]),(131,[]),(5,[2,3,3,3,3,3,7,71]),
    (147,[]),(131,[]),(19,[2,3,13,19,163]),(159,[]),(131,[]),
    (12,[2,3,67,601]),(487,[]),(131,[]),(175,[]),(5,[2,19,6359]),
    (131,[]),(10,[2,3,40277]),(5,[2,120833]),(131,[]),(5,[2,3,3,29,463]),
    (135,[]),(131,[]),(145,[]),(19,[2,120863]),(131,[]),
    (139,[]),(547,[]),(131,[]),(5,[2,3,59,683]),(135,[]),
    (131,[]),(5,[2,3,191,211]),(20,[2,7,23,751]),(131,[]),(135,[]),
    (10,[2,11,10993]),(131,[]),(12,[2,3,3,3,3,1493]),(5,[2,120941]),(131,[]),
    (5,[2,3,3,89,151]),(7,[2,7,37,467]),(131,[]),(135,[]),(141,[]),
    (131,[]),(76,[2,3,7,7,823]),(139,[]),(131,[]),(189,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock242 : ∃ data, checkBlock 242 data = true :=
  ⟨[(147,[]),(131,[]),(169,[]),(301,[]),(131,[]),
    (141,[]),(145,[]),(131,[]),(18,[2,3,3,3,4483]),(361,[]),
    (131,[]),(367,[]),(135,[]),(131,[]),(139,[]),
    (5,[2,41,2953]),(131,[]),(151,[]),(327,[]),(131,[]),
    (141,[]),(135,[]),(131,[]),(2,[2,3,3,13457]),(5,[2,7,11,11,11,13]),
    (131,[]),(135,[]),(145,[]),(131,[]),(201,[]),
    (465,[]),(131,[]),(199,[]),(159,[]),(131,[]),
    (135,[]),(139,[]),(131,[]),(147,[]),(165,[]),
    (131,[]),(139,[]),(277,[]),(131,[]),(151,[]),
    (14,[2,241,503]),(131,[]),(29,[2,3,7,23,251]),(5,[2,31,3911]),(131,[]),
    (409,[]),(325,[]),(131,[]),(157,[]),(135,[]),
    (131,[]),(171,[]),(141,[]),(131,[]),(495,[]),
    (5,[2,101,1201]),(131,[]),(459,[]),(135,[]),(131,[]),
    (5,[2,3,37,1093]),(355,[]),(131,[]),(135,[]),(147,[]),
    (131,[]),(291,[]),(141,[]),(131,[]),(145,[]),
    (5,[2,7,7,2477]),(131,[]),(135,[]),(235,[]),(131,[]),
    (139,[]),(10,[2,121403]),(131,[]),(141,[]),(169,[]),
    (131,[]),(5,[2,3,17,2381]),(6,[2,13,9341]),(131,[]),(28,[2,3,7,5783]),
    (151,[]),(131,[]),(28,[2,3,40487]),(10,[2,23,5281]),(131,[]),
    (145,[]),(135,[]),(131,[]),(141,[]),(321,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock243 : ∃ data, checkBlock 243 data = true :=
  ⟨[(131,[]),(169,[]),(139,[]),(131,[]),(487,[]),
    (135,[]),(131,[]),(139,[]),(145,[]),(131,[]),
    (135,[]),(157,[]),(131,[]),(165,[]),(147,[]),
    (131,[]),(201,[]),(10,[2,7,11,1579]),(131,[]),(135,[]),
    (5,[2,17,23,311]),(131,[]),(157,[]),(5,[2,31,3923]),(131,[]),
    (475,[]),(10,[2,121631]),(131,[]),(339,[]),(139,[]),
    (131,[]),(595,[]),(181,[]),(131,[]),(5,[2,3,3,11,1229]),
    (141,[]),(131,[]),(12,[2,3,47,863]),(135,[]),(131,[]),
    (2,[2,3,113,359]),(529,[]),(131,[]),(357,[]),(159,[]),
    (131,[]),(139,[]),(135,[]),(131,[]),(39,[2,3,3,3,3,3,3,167]),
    (141,[]),(131,[]),(135,[]),(10,[2,121763]),(131,[]),
    (151,[]),(279,[]),(131,[]),(5,[2,3,40597]),(5,[2,7,127,137]),
    (131,[]),(135,[]),(14,[2,41,2971]),(131,[]),(19,[2,3,7,5801]),
    (29,[2,13,9371]),(131,[]),(267,[]),(139,[]),(131,[]),
    (11,[2,3,3,3,4513]),(5,[2,121853]),(131,[]),(139,[]),(199,[]),
    (131,[]),(141,[]),(171,[]),(131,[]),(2,[2,3,41,991]),
    (135,[]),(131,[]),(151,[]),(147,[]),(131,[]),
    (187,[]),(10,[2,121931]),(131,[]),(175,[]),(135,[]),
    (131,[]),(319,[]),(481,[]),(131,[]),(135,[]),
    (139,[]),(131,[]),(145,[]),(397,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock244 : ∃ data, checkBlock 244 data = true :=
  ⟨[(12,[2,3,11,3697]),(151,[]),(131,[]),(135,[]),(5,[2,122021]),
    (131,[]),(159,[]),(235,[]),(131,[]),(5,[2,3,17,2393]),
    (145,[]),(131,[]),(139,[]),(141,[]),(131,[]),
    (42,[2,3,7,5813]),(165,[]),(131,[]),(189,[]),(159,[]),
    (131,[]),(147,[]),(135,[]),(131,[]),(21,[2,3,3,3,4523]),
    (10,[2,97,1259]),(131,[]),(157,[]),(141,[]),(131,[]),
    (5,[2,3,19,2143]),(135,[]),(131,[]),(391,[]),(139,[]),
    (131,[]),(135,[]),(13,[2,61,2003]),(131,[]),(139,[]),
    (5,[2,122201]),(131,[]),(10,[2,3,3,37,367]),(189,[]),(131,[]),
    (135,[]),(13,[2,122231]),(131,[]),(169,[]),(237,[]),
    (131,[]),(2,[2,3,40751]),(567,[]),(131,[]),(141,[]),
    (5,[2,122273]),(131,[]),(5,[2,3,3,3,7,647]),(10,[2,13,23,409]),(131,[]),
    (12,[2,3,3,107,127]),(139,[]),(131,[]),(171,[]),(135,[]),
    (131,[]),(147,[]),(5,[2,71,1723]),(131,[]),(28,[2,3,13,3137]),
    (14,[2,29,4219]),(131,[]),(229,[]),(135,[]),(131,[]),
    (21,[2,3,3,13597]),(285,[]),(131,[]),(135,[]),(5,[2,122393]),
    (131,[]),(159,[]),(175,[]),(131,[]),(18,[2,3,13,43,73]),
    (157,[]),(131,[]),(135,[]),(361,[]),(131,[]),
    (165,[]),(141,[]),(131,[]),(151,[]),(34,[2,122471]),
    (131,[]),(157,[]),(147,[]),(131,[]),(145,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock245 : ∃ data, checkBlock 245 data = true :=
  ⟨[(139,[]),(131,[]),(10,[2,3,97,421]),(187,[]),(131,[]),
    (139,[]),(135,[]),(131,[]),(2,[2,3,40847]),(19,[2,31,59,67]),
    (131,[]),(12,[2,3,3,3,3,17,89]),(145,[]),(131,[]),(171,[]),
    (135,[]),(131,[]),(141,[]),(10,[2,7,83,211]),(131,[]),
    (135,[]),(201,[]),(131,[]),(379,[]),(231,[]),
    (131,[]),(187,[]),(139,[]),(131,[]),(135,[]),
    (159,[]),(131,[]),(141,[]),(145,[]),(131,[]),
    (147,[]),(259,[]),(131,[]),(5,[2,3,40897]),(151,[]),
    (131,[]),(12,[2,3,7,5843]),(147,[]),(131,[]),(139,[]),
    (199,[]),(131,[]),(169,[]),(135,[]),(131,[]),
    (511,[]),(225,[]),(131,[]),(5,[2,3,151,271]),(157,[]),
    (131,[]),(12,[2,3,40927]),(135,[]),(131,[]),(11,[2,3,11,61,61]),
    (577,[]),(131,[]),(135,[]),(5,[2,191,643]),(131,[]),
    (189,[]),(139,[]),(131,[]),(2,[2,3,3,13649]),(141,[]),
    (131,[]),(135,[]),(5,[2,122861]),(131,[]),(525,[]),
    (5,[2,19,29,223]),(131,[]),(307,[]),(29,[2,122891]),(131,[]),
    (145,[]),(501,[]),(131,[]),(421,[]),(141,[]),
    (131,[]),(5,[2,3,3,3,29,157]),(181,[]),(131,[]),(259,[]),
    (135,[]),(131,[]),(159,[]),(139,[]),(131,[]),
    (141,[]),(5,[2,23,5347]),(131,[]),(19,[2,3,11,3727]),(135,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock246 : ∃ data, checkBlock 246 data = true :=
  ⟨[(131,[]),(145,[]),(475,[]),(131,[]),(135,[]),
    (159,[]),(131,[]),(231,[]),(201,[]),(131,[]),
    (139,[]),(147,[]),(131,[]),(135,[]),(145,[]),
    (131,[]),(327,[]),(10,[2,123083]),(131,[]),(12,[2,3,3,3,47,97]),
    (5,[2,11,19,19,31]),(131,[]),(20,[2,3,3,13679]),(241,[]),(131,[]),
    (11,[2,3,7,11,13,41]),(217,[]),(131,[]),(225,[]),(169,[]),
    (131,[]),(151,[]),(135,[]),(131,[]),(5,[2,3,41057]),
    (145,[]),(131,[]),(139,[]),(165,[]),(131,[]),
    (2,[2,3,3,3,3,3,3,13,13]),(135,[]),(131,[]),(211,[]),(187,[]),
    (131,[]),(135,[]),(141,[]),(131,[]),(147,[]),
    (181,[]),(131,[]),(2,[2,3,181,227]),(13,[2,7,17609]),(131,[]),
    (135,[]),(147,[]),(131,[]),(151,[]),(139,[]),
    (131,[]),(5,[2,3,23,1787]),(141,[]),(131,[]),(11,[2,3,11,37,101]),
    (285,[]),(131,[]),(159,[]),(5,[2,123341]),(131,[]),
    (157,[]),(5,[2,293,421]),(131,[]),(141,[]),(135,[]),
    (131,[]),(139,[]),(151,[]),(131,[]),(12,[2,3,41131]),
    (5,[2,123401]),(131,[]),(145,[]),(135,[]),(131,[]),
    (321,[]),(171,[]),(131,[]),(135,[]),(367,[]),
    (131,[]),(11,[2,3,3,11,29,43]),(5,[2,13,9497]),(131,[]),(147,[]),
    (18,[2,7,31,569]),(131,[]),(135,[]),(139,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock247 : ∃ data, checkBlock 247 data = true :=
  ⟨[(267,[]),(19,[2,123503]),(131,[]),(139,[]),(151,[]),
    (131,[]),(235,[]),(5,[2,23,41,131]),(131,[]),(19,[2,3,3,7,37,53]),
    (237,[]),(131,[]),(165,[]),(549,[]),(131,[]),
    (229,[]),(135,[]),(131,[]),(20,[2,3,13,3169]),(279,[]),
    (131,[]),(171,[]),(10,[2,71,1741]),(131,[]),(561,[]),
    (135,[]),(131,[]),(175,[]),(157,[]),(131,[]),
    (135,[]),(351,[]),(131,[]),(295,[]),(29,[2,19,23,283]),
    (131,[]),(2,[2,3,41227]),(145,[]),(131,[]),(135,[]),
    (141,[]),(131,[]),(139,[]),(309,[]),(131,[]),
    (225,[]),(19,[2,123731]),(131,[]),(391,[]),(507,[]),
    (131,[]),(141,[]),(255,[]),(131,[]),(201,[]),
    (5,[2,13,9521]),(131,[]),(165,[]),(135,[]),(131,[]),
    (2,[2,3,29,1423]),(30,[2,123803]),(131,[]),(147,[]),(139,[]),
    (131,[]),(141,[]),(135,[]),(131,[]),(139,[]),
    (147,[]),(131,[]),(135,[]),(319,[]),(131,[]),
    (157,[]),(169,[]),(131,[]),(159,[]),(277,[]),
    (131,[]),(135,[]),(207,[]),(131,[]),(145,[]),
    (19,[2,123923]),(131,[]),(439,[]),(615,[]),(131,[]),
    (285,[]),(139,[]),(131,[]),(169,[]),(10,[2,151,821]),
    (131,[]),(151,[]),(195,[]),(131,[]),(181,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock248 : ∃ data, checkBlock 248 data = true :=
  ⟨[(135,[]),(131,[]),(325,[]),(141,[]),(131,[]),
    (145,[]),(14,[2,31,4001]),(131,[]),(139,[]),(135,[]),
    (131,[]),(265,[]),(409,[]),(131,[]),(135,[]),
    (151,[]),(131,[]),(20,[2,3,3,17,811]),(141,[]),(131,[]),
    (19,[2,3,3,13789]),(175,[]),(131,[]),(135,[]),(5,[2,124121]),
    (131,[]),(537,[]),(5,[2,124133]),(131,[]),(141,[]),
    (139,[]),(131,[]),(2,[2,3,41387]),(157,[]),(131,[]),
    (139,[]),(435,[]),(131,[]),(277,[]),(145,[]),
    (131,[]),(10,[2,3,19,2179]),(135,[]),(131,[]),(141,[]),
    (10,[2,11,23,491]),(131,[]),(547,[]),(5,[2,13,19,503]),(131,[]),
    (195,[]),(135,[]),(131,[]),(159,[]),(10,[2,7,41,433]),
    (131,[]),(135,[]),(139,[]),(131,[]),(2,[2,3,13,3187]),
    (165,[]),(131,[]),(181,[]),(5,[2,7,7,43,59]),(131,[]),
    (135,[]),(295,[]),(131,[]),(2,[2,3,7,31,191]),(559,[]),
    (131,[]),(2,[2,3,3,41,337]),(5,[2,23,5407]),(131,[]),(139,[]),
    (169,[]),(131,[]),(147,[]),(19,[2,53,2347]),(131,[]),
    (187,[]),(141,[]),(131,[]),(12,[2,3,113,367]),(135,[]),
    (131,[]),(145,[]),(5,[2,124433]),(131,[]),(5,[2,3,3,3,11,419]),
    (13,[2,97,1283]),(131,[]),(357,[]),(135,[]),(131,[]),
    (301,[]),(139,[]),(131,[]),(135,[]),(5,[2,124493])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock249 : ∃ data, checkBlock 249 data = true :=
  ⟨[(131,[]),(139,[]),(157,[]),(131,[]),(465,[]),
    (165,[]),(131,[]),(135,[]),(211,[]),(131,[]),
    (45,[2,3,3,3,7,659]),(14,[2,11,13,13,67]),(131,[]),(5,[2,3,41521]),(10,[2,43,2897]),
    (131,[]),(321,[]),(229,[]),(131,[]),(30,[2,3,7,17,349]),
    (145,[]),(131,[]),(141,[]),(139,[]),(131,[]),
    (409,[]),(135,[]),(131,[]),(237,[]),(10,[2,124643]),
    (131,[]),(189,[]),(411,[]),(131,[]),(151,[]),
    (135,[]),(131,[]),(5,[2,3,13,23,139]),(14,[2,7,47,379]),(131,[]),
    (135,[]),(145,[]),(131,[]),(2,[2,3,3,3,31,149]),(171,[]),
    (131,[]),(5,[2,3,3,13859]),(217,[]),(131,[]),(135,[]),
    (10,[2,11,11,1031]),(131,[]),(175,[]),(147,[]),(131,[]),
    (385,[]),(5,[2,124781]),(131,[]),(10,[2,3,41597]),(141,[]),
    (131,[]),(47,[2,3,3,7,7,283]),(139,[]),(131,[]),(159,[]),
    (19,[2,124823]),(131,[]),(139,[]),(135,[]),(131,[]),
    (10,[2,3,41617]),(199,[]),(131,[]),(11,[2,3,41621]),(141,[]),
    (131,[]),(2,[2,3,41627]),(135,[]),(131,[]),(165,[]),
    (151,[]),(131,[]),(135,[]),(5,[2,23,5431]),(131,[]),
    (141,[]),(10,[2,271,461]),(131,[]),(145,[]),(139,[]),
    (131,[]),(135,[]),(5,[2,29,31,139]),(131,[]),(10,[2,3,7,11,541]),
    (5,[2,47,2659]),(131,[]),(6,[2,3,3,3,3,1543]),(147,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock250 : ∃ data, checkBlock 250 data = true :=
  ⟨[(141,[]),(14,[2,125003]),(131,[]),(18,[2,3,7,5953]),(5,[2,13,59,163]),
    (131,[]),(139,[]),(157,[]),(131,[]),(145,[]),
    (135,[]),(131,[]),(11,[2,3,41687]),(517,[]),(131,[]),
    (2,[2,3,3,13,1069]),(225,[]),(131,[]),(157,[]),(135,[]),
    (131,[]),(279,[]),(145,[]),(131,[]),(135,[]),
    (379,[]),(131,[]),(2,[2,3,53,787]),(139,[]),(131,[]),
    (171,[]),(5,[2,7,19,941]),(131,[]),(135,[]),(10,[2,17,37,199]),
    (131,[]),(147,[]),(141,[]),(131,[]),(159,[]),
    (5,[2,125201]),(131,[]),(57,[2,3,41737]),(145,[]),(131,[]),
    (151,[]),(175,[]),(131,[]),(591,[]),(235,[]),
    (131,[]),(525,[]),(135,[]),(131,[]),(5,[2,3,3,31,449]),
    (139,[]),(131,[]),(459,[]),(10,[2,349,359]),(131,[]),
    (259,[]),(135,[]),(131,[]),(141,[]),(7,[2,7,17903]),
    (131,[]),(135,[]),(147,[]),(131,[]),(12,[2,3,3,19,733]),
    (19,[2,103,1217]),(131,[]),(139,[]),(10,[2,7,17909]),(131,[]),
    (135,[]),(157,[]),(131,[]),(141,[]),(5,[2,37,3389]),
    (131,[]),(33,[2,3,41801]),(165,[]),(131,[]),(199,[]),
    (265,[]),(131,[]),(2,[2,3,3,7,11,181]),(159,[]),(131,[]),
    (145,[]),(151,[]),(131,[]),(187,[]),(135,[]),
    (131,[]),(2,[2,3,151,277]),(39,[2,29,4327]),(131,[]),(139,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock251 : ∃ data, checkBlock 251 data = true :=
  ⟨[(5,[2,41,3061]),(131,[]),(301,[]),(135,[]),(131,[]),
    (147,[]),(19,[2,7,79,227]),(131,[]),(135,[]),(13,[2,11,101,113]),
    (131,[]),(145,[]),(147,[]),(131,[]),(5,[2,3,19,2203]),
    (141,[]),(131,[]),(135,[]),(151,[]),(131,[]),
    (18,[2,3,7,5981]),(139,[]),(131,[]),(157,[]),(145,[]),
    (131,[]),(38,[2,3,3,3,3,3,11,47]),(165,[]),(131,[]),(5,[2,3,7,31,193]),
    (141,[]),(131,[]),(17,[2,3,41887]),(225,[]),(131,[]),
    (12,[2,3,163,257]),(135,[]),(131,[]),(139,[]),(5,[2,125693]),
    (131,[]),(141,[]),(231,[]),(131,[]),(2,[2,3,3,61,229]),
    (135,[]),(131,[]),(12,[2,3,41911]),(7,[2,7,11,23,71]),(131,[]),
    (135,[]),(171,[]),(131,[]),(10,[2,3,11,37,103]),(29,[2,173,727]),
    (131,[]),(141,[]),(14,[2,7,7,17,151]),(131,[]),(135,[]),
    (139,[]),(131,[]),(10,[2,3,3,7,1997]),(159,[]),(131,[]),
    (139,[]),(10,[2,29,4339]),(131,[]),(517,[]),(421,[]),
    (131,[]),(74,[2,3,7,13,461]),(339,[]),(131,[]),(355,[]),
    (189,[]),(131,[]),(351,[]),(135,[]),(131,[]),
    (181,[]),(147,[]),(131,[]),(151,[]),(5,[2,125921]),
    (131,[]),(169,[]),(135,[]),(131,[]),(10,[2,3,41981]),
    (13,[2,7,19,947]),(131,[]),(135,[]),(141,[]),(131,[]),
    (2,[2,3,3,13997]),(325,[]),(131,[]),(23,[2,3,3,13999]),(195,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock252 : ∃ data, checkBlock 252 data = true :=
  ⟨[(131,[]),(135,[]),(171,[]),(131,[]),(139,[]),
    (435,[]),(131,[]),(571,[]),(141,[]),(131,[]),
    (151,[]),(187,[]),(131,[]),(145,[]),(10,[2,11,73,157]),
    (131,[]),(2,[2,3,3,14009]),(589,[]),(131,[]),(141,[]),
    (135,[]),(131,[]),(10,[2,3,127,331]),(181,[]),(131,[]),
    (159,[]),(139,[]),(131,[]),(11,[2,3,19,2213]),(135,[]),
    (131,[]),(139,[]),(20,[2,7,67,269]),(131,[]),(135,[]),
    (405,[]),(131,[]),(171,[]),(19,[2,13,17,571]),(131,[]),
    (211,[]),(301,[]),(131,[]),(135,[]),(5,[2,113,1117]),
    (131,[]),(5,[2,3,7,6011]),(145,[]),(131,[]),(291,[]),
    (157,[]),(131,[]),(195,[]),(139,[]),(131,[]),
    (199,[]),(151,[]),(131,[]),(12,[2,3,11,43,89]),(357,[]),
    (131,[]),(11,[2,3,42101]),(135,[]),(131,[]),(147,[]),
    (595,[]),(131,[]),(28,[2,3,3,3,4679]),(169,[]),(131,[]),
    (139,[]),(135,[]),(131,[]),(5,[2,3,73,577]),(159,[]),
    (131,[]),(135,[]),(10,[2,47,2689]),(131,[]),(577,[]),
    (229,[]),(131,[]),(6,[2,3,29,1453]),(5,[2,7,18059]),(131,[]),
    (135,[]),(141,[]),(131,[]),(171,[]),(19,[2,126443]),
    (131,[]),(175,[]),(139,[]),(131,[]),(145,[]),
    (147,[]),(131,[]),(139,[]),(10,[2,126491]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock253 : ∃ data, checkBlock 253 data = true :=
  ⟨[(2,[2,3,149,283]),(241,[]),(131,[]),(217,[]),(135,[]),
    (131,[]),(5,[2,3,3,17,827]),(211,[]),(131,[]),(465,[]),
    (10,[2,126551]),(131,[]),(141,[]),(135,[]),(131,[]),
    (145,[]),(511,[]),(131,[]),(135,[]),(139,[]),
    (131,[]),(151,[]),(259,[]),(131,[]),(65,[2,3,3,11,1279]),
    (10,[2,7,18089]),(131,[]),(135,[]),(145,[]),(131,[]),
    (567,[]),(5,[2,126653]),(131,[]),(147,[]),(19,[2,197,643]),
    (131,[]),(139,[]),(10,[2,126683]),(131,[]),(38,[2,3,3,7,2011]),
    (147,[]),(131,[]),(5,[2,3,3,3,13,19,19]),(5,[2,126713]),(131,[]),
    (33,[2,3,53,797]),(135,[]),(131,[]),(151,[]),(141,[]),
    (131,[]),(12,[2,3,11,23,167]),(187,[]),(131,[]),(5,[2,3,42257]),
    (135,[]),(131,[]),(5,[2,3,3,14087]),(139,[]),(131,[]),
    (135,[]),(14,[2,17,7459]),(131,[]),(139,[]),(141,[]),
    (131,[]),(157,[]),(151,[]),(131,[]),(135,[]),
    (13,[2,126851]),(131,[]),(477,[]),(615,[]),(131,[]),
    (141,[]),(5,[2,181,701]),(131,[]),(147,[]),(6,[2,13,43,227]),
    (131,[]),(481,[]),(10,[2,179,709]),(131,[]),(441,[]),
    (139,[]),(131,[]),(11,[2,3,29,1459]),(135,[]),(131,[]),
    (141,[]),(5,[2,79,1607]),(131,[]),(399,[]),(151,[]),
    (131,[]),(145,[]),(135,[]),(131,[]),(12,[2,3,42331])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock254 : ∃ data, checkBlock 254 data = true :=
  ⟨[(5,[2,7,18143]),(131,[]),(135,[]),(5,[2,157,809]),(131,[]),
    (5,[2,3,13,3257]),(211,[]),(131,[]),(2,[2,3,17,47,53]),(147,[]),
    (131,[]),(135,[]),(327,[]),(131,[]),(207,[]),
    (5,[2,83,1531]),(131,[]),(145,[]),(285,[]),(131,[]),
    (361,[]),(13,[2,127103]),(131,[]),(165,[]),(139,[]),
    (131,[]),(379,[]),(141,[]),(131,[]),(139,[]),
    (135,[]),(131,[]),(169,[]),(325,[]),(131,[]),
    (181,[]),(241,[]),(131,[]),(37,[2,3,42397]),(135,[]),
    (131,[]),(19,[2,3,109,389]),(141,[]),(131,[]),(135,[]),
    (13,[2,29,41,107]),(131,[]),(147,[]),(301,[]),(131,[]),
    (435,[]),(139,[]),(131,[]),(135,[]),(147,[]),
    (131,[]),(405,[]),(321,[]),(131,[]),(151,[]),
    (159,[]),(131,[]),(5,[2,3,42437]),(6,[2,17,7489]),(131,[]),
    (5,[2,3,3,7,43,47]),(19,[2,127331]),(131,[]),(139,[]),(385,[]),
    (131,[]),(157,[]),(135,[]),(131,[]),(397,[]),
    (5,[2,127373]),(131,[]),(235,[]),(10,[2,11,37,313]),(131,[]),
    (2,[2,3,42467]),(135,[]),(131,[]),(11,[2,3,3,3,3,11,11,13]),(201,[]),
    (131,[]),(135,[]),(409,[]),(131,[]),(23,[2,3,23,1847]),
    (139,[]),(131,[]),(147,[]),(14,[2,7,131,139]),(131,[]),
    (135,[]),(5,[2,127481]),(131,[]),(145,[]),(5,[2,127493])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock255 : ∃ data, checkBlock 255 data = true :=
  ⟨[(131,[]),(5,[2,3,3,31,457]),(19,[2,47,2713]),(131,[]),(18,[2,3,3,3,4723]),
    (141,[]),(131,[]),(507,[]),(5,[2,127541]),(131,[]),
    (199,[]),(5,[2,229,557]),(131,[]),(21,[2,3,101,421]),(135,[]),
    (131,[]),(175,[]),(139,[]),(131,[]),(145,[]),
    (141,[]),(131,[]),(159,[]),(135,[]),(131,[]),
    (12,[2,3,19,2239]),(165,[]),(131,[]),(135,[]),(157,[]),
    (131,[]),(141,[]),(145,[]),(131,[]),(139,[]),
    (159,[]),(131,[]),(135,[]),(13,[2,127691]),(131,[]),
    (157,[]),(181,[]),(131,[]),(201,[]),(5,[2,11,17,683]),
    (131,[]),(141,[]),(5,[2,127733]),(131,[]),(6,[2,3,7,7,11,79]),
    (34,[2,13,31,317]),(131,[]),(2,[2,3,37,1151]),(145,[]),(131,[]),
    (549,[]),(135,[]),(131,[]),(559,[]),(5,[2,47,2719]),
    (131,[]),(139,[]),(235,[]),(131,[]),(279,[]),
    (135,[]),(131,[]),(11,[2,3,42611]),(147,[]),(131,[]),
    (135,[]),(165,[]),(131,[]),(175,[]),(10,[2,71,1801]),
    (131,[]),(28,[2,3,3,13,1093]),(20,[2,7,18269]),(131,[]),(135,[]),
    (5,[2,79,1619]),(131,[]),(237,[]),(139,[]),(131,[]),
    (6,[2,3,42641]),(459,[]),(131,[]),(187,[]),(10,[2,97,1319]),
    (131,[]),(11,[2,3,3,3,7,677]),(5,[2,41,3121]),(131,[]),(339,[]),
    (5,[2,127973]),(131,[]),(151,[]),(135,[]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock256 : ∃ data, checkBlock 256 data = true :=
  ⟨[(139,[]),(195,[]),(131,[]),(631,[]),(181,[]),
    (131,[]),(147,[]),(135,[]),(131,[]),(141,[]),
    (175,[]),(131,[]),(135,[]),(169,[]),(131,[]),
    (2,[2,3,11,3881]),(5,[2,263,487]),(131,[]),(369,[]),(5,[2,7,29,631]),
    (131,[]),(135,[]),(139,[]),(131,[]),(141,[]),
    (279,[]),(131,[]),(139,[]),(355,[]),(131,[]),
    (201,[]),(5,[2,128153]),(131,[]),(265,[]),(145,[]),
    (131,[]),(45,[2,3,42727]),(147,[]),(131,[]),(211,[]),
    (135,[]),(131,[]),(5,[2,3,42737]),(151,[]),(131,[]),
    (157,[]),(159,[]),(131,[]),(2,[2,3,3,14249]),(135,[]),
    (131,[]),(307,[]),(199,[]),(131,[]),(135,[]),
    (145,[]),(131,[]),(5,[2,3,61,701]),(507,[]),(131,[]),
    (28,[2,3,42767]),(141,[]),(131,[]),(135,[]),(5,[2,128321]),
    (131,[]),(139,[]),(171,[]),(131,[]),(19,[2,3,179,239]),
    (151,[]),(131,[]),(2,[2,3,42787]),(277,[]),(131,[]),
    (147,[]),(141,[]),(131,[]),(169,[]),(339,[]),
    (131,[]),(199,[]),(135,[]),(131,[]),(229,[]),
    (547,[]),(131,[]),(141,[]),(139,[]),(131,[]),
    (10,[2,3,47,911]),(135,[]),(131,[]),(139,[]),(217,[]),
    (131,[]),(135,[]),(14,[2,128483]),(131,[]),(207,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock257 : ∃ data, checkBlock 257 data = true :=
  ⟨[(5,[2,23,37,151]),(131,[]),(141,[]),(157,[]),(131,[]),
    (135,[]),(187,[]),(131,[]),(159,[]),(445,[]),
    (131,[]),(11,[2,3,73,587]),(5,[2,59,2179]),(131,[]),(157,[]),
    (139,[]),(131,[]),(357,[]),(171,[]),(131,[]),
    (147,[]),(159,[]),(131,[]),(145,[]),(135,[]),
    (131,[]),(41,[2,3,53,809]),(495,[]),(131,[]),(5,[2,3,137,313]),
    (207,[]),(131,[]),(139,[]),(135,[]),(131,[]),
    (151,[]),(145,[]),(131,[]),(135,[]),(141,[]),
    (131,[]),(5,[2,3,42901]),(265,[]),(131,[]),(29,[2,3,107,401]),
    (10,[2,7,7,37,71]),(131,[]),(135,[]),(165,[]),(131,[]),
    (39,[2,3,7,6131]),(147,[]),(131,[]),(171,[]),(139,[]),
    (131,[]),(309,[]),(145,[]),(131,[]),(139,[]),
    (169,[]),(131,[]),(151,[]),(5,[2,128813]),(131,[]),
    (141,[]),(135,[]),(131,[]),(255,[]),(10,[2,11,13,17,53]),
    (131,[]),(30,[2,3,3,103,139]),(157,[]),(131,[]),(501,[]),
    (135,[]),(131,[]),(169,[]),(10,[2,7,18413]),(131,[]),
    (135,[]),(139,[]),(131,[]),(159,[]),(529,[]),
    (131,[]),(6,[2,3,11,3907]),(6,[2,7,113,163]),(131,[]),(135,[]),
    (14,[2,128951]),(131,[]),(225,[]),(165,[]),(131,[]),
    (2,[2,3,13,3307]),(147,[]),(131,[]),(139,[]),(5,[2,128993])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock258 : ∃ data, checkBlock 258 data = true :=
  ⟨[(131,[]),(187,[]),(29,[2,129011]),(131,[]),(145,[]),
    (211,[]),(131,[]),(2,[2,3,3,3,3,3,3,3,59]),(135,[]),(131,[]),
    (327,[]),(5,[2,23,31,181]),(131,[]),(5,[2,3,11,3911]),(13,[2,337,383]),
    (131,[]),(181,[]),(135,[]),(131,[]),(157,[]),
    (139,[]),(131,[]),(135,[]),(199,[]),(131,[]),
    (139,[]),(399,[]),(131,[]),(2,[2,3,3,3,4783]),(309,[]),
    (131,[]),(135,[]),(141,[]),(131,[]),(147,[]),
    (201,[]),(131,[]),(217,[]),(145,[]),(131,[]),
    (2,[2,3,43067]),(13,[2,47,2749]),(131,[]),(141,[]),(5,[2,129221]),
    (131,[]),(259,[]),(139,[]),(131,[]),(10,[2,3,67,643]),
    (135,[]),(131,[]),(547,[]),(10,[2,129263]),(131,[]),
    (175,[]),(5,[2,129281]),(131,[]),(141,[]),(135,[]),
    (131,[]),(12,[2,3,3,3,4789]),(14,[2,7,7,7,13,29]),(131,[]),(135,[]),
    (147,[]),(131,[]),(165,[]),(295,[]),(131,[]),
    (6,[2,3,43117]),(5,[2,7,17,1087]),(131,[]),(135,[]),(14,[2,11,19,619]),
    (131,[]),(2,[2,3,7,61,101]),(157,[]),(131,[]),(44,[2,3,3,11,1307]),
    (5,[2,129401]),(131,[]),(189,[]),(5,[2,127,1019]),(131,[]),
    (5,[2,3,7,6163]),(139,[]),(131,[]),(157,[]),(34,[2,129443]),
    (131,[]),(139,[]),(135,[]),(131,[]),(159,[]),
    (141,[]),(131,[]),(5,[2,3,3,14387]),(14,[2,129491]),(131,[])], by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkedBlock259 : ∃ data, checkBlock 259 data = true :=
  ⟨[(151,[]),(135,[]),(131,[]),(147,[]),(211,[]),
    (131,[]),(135,[]),(159,[]),(131,[]),(225,[]),
    (141,[]),(131,[]),(28,[2,3,19,2273]),(139,[]),(131,[]),
    (135,[]),(5,[2,129581]),(131,[]),(10,[2,3,3,7,11,11,17]),(151,[]),
    (131,[]),(141,[]),(181,[]),(131,[]),(169,[]),
    (171,[]),(131,[]),(145,[]),(379,[]),(131,[]),
    (139,[]),(477,[]),(131,[]),(301,[]),(135,[]),
    (131,[]),(141,[]),(561,[]),(131,[]),(12,[2,3,17,2543]),
    (145,[]),(131,[]),(187,[]),(135,[]),(131,[]),
    (529,[]),(151,[]),(131,[]),(135,[]),(175,[]),
    (131,[]),(18,[2,3,3,13,1109]),(139,[]),(131,[]),(589,[]),
    (5,[2,7,18539]),(131,[]),(135,[]),(10,[2,107,1213]),(131,[]),
    (2,[2,3,7,7,883]),(145,[]),(131,[]),(11,[2,3,43271]),(5,[2,131,991]),
    (131,[]),(231,[]),(6,[2,11,11,29,37]),(131,[]),(159,[]),
    (165,[]),(131,[]),(17,[2,3,3,47,307]),(141,[]),(131,[]),
    (237,[]),(135,[]),(131,[]),(33,[2,3,29,1493]),(139,[]),
    (131,[]),(201,[]),(10,[2,163,797]),(131,[]),(325,[]),
    (135,[]),(131,[]),(11,[2,3,3,14437]),(141,[]),(131,[]),
    (135,[]),(5,[2,129953]),(131,[]),(157,[]),(19,[2,129971]),
    (131,[]),(139,[]),(21,[2,7,31,599]),(131,[]),(135,[])], by decide⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem finite_primitive_pair {p : ℕ} (hp : p.Prime) (h170 : 170 ≤ p)
    (hr : p%20 = 3 ∨ p%20 = 7) (hbound : p < 260000) :
    ∃ x : ℕ, 1 ≤ x ∧ x+1 < p ∧ orderOf (x : ZMod p) = p-1 ∧
      orderOf ((x+1 : ℕ) : ZMod p) = p-1 := by
  let b := p/1000
  let i := p%1000
  let j := 2*(i/20) + if i%20 = 3 then 0 else 1
  have hj : j < 100 := by dsimp [j,i]; split <;> omega
  have he : p = atResidue b j := by
    have ham : i % 20 = p%20 := Nat.mod_mod_of_dvd _ (by decide)
    rcases hr with hr | hr <;> simp [j, i, b, atResidue, ham, hr] <;> omega
  suffices h : ∃ data, checkBlock b data = true by
    obtain ⟨data, hh⟩ := h
    exact checkBlock_sound hh he hj hp h170 hbound.le
  have hl : b < 260 := by dsimp [b]; omega
  interval_cases eq : b
  · exact checkedBlock0
  · exact checkedBlock1
  · exact checkedBlock2
  · exact checkedBlock3
  · exact checkedBlock4
  · exact checkedBlock5
  · exact checkedBlock6
  · exact checkedBlock7
  · exact checkedBlock8
  · exact checkedBlock9
  · exact checkedBlock10
  · exact checkedBlock11
  · exact checkedBlock12
  · exact checkedBlock13
  · exact checkedBlock14
  · exact checkedBlock15
  · exact checkedBlock16
  · exact checkedBlock17
  · exact checkedBlock18
  · exact checkedBlock19
  · exact checkedBlock20
  · exact checkedBlock21
  · exact checkedBlock22
  · exact checkedBlock23
  · exact checkedBlock24
  · exact checkedBlock25
  · exact checkedBlock26
  · exact checkedBlock27
  · exact checkedBlock28
  · exact checkedBlock29
  · exact checkedBlock30
  · exact checkedBlock31
  · exact checkedBlock32
  · exact checkedBlock33
  · exact checkedBlock34
  · exact checkedBlock35
  · exact checkedBlock36
  · exact checkedBlock37
  · exact checkedBlock38
  · exact checkedBlock39
  · exact checkedBlock40
  · exact checkedBlock41
  · exact checkedBlock42
  · exact checkedBlock43
  · exact checkedBlock44
  · exact checkedBlock45
  · exact checkedBlock46
  · exact checkedBlock47
  · exact checkedBlock48
  · exact checkedBlock49
  · exact checkedBlock50
  · exact checkedBlock51
  · exact checkedBlock52
  · exact checkedBlock53
  · exact checkedBlock54
  · exact checkedBlock55
  · exact checkedBlock56
  · exact checkedBlock57
  · exact checkedBlock58
  · exact checkedBlock59
  · exact checkedBlock60
  · exact checkedBlock61
  · exact checkedBlock62
  · exact checkedBlock63
  · exact checkedBlock64
  · exact checkedBlock65
  · exact checkedBlock66
  · exact checkedBlock67
  · exact checkedBlock68
  · exact checkedBlock69
  · exact checkedBlock70
  · exact checkedBlock71
  · exact checkedBlock72
  · exact checkedBlock73
  · exact checkedBlock74
  · exact checkedBlock75
  · exact checkedBlock76
  · exact checkedBlock77
  · exact checkedBlock78
  · exact checkedBlock79
  · exact checkedBlock80
  · exact checkedBlock81
  · exact checkedBlock82
  · exact checkedBlock83
  · exact checkedBlock84
  · exact checkedBlock85
  · exact checkedBlock86
  · exact checkedBlock87
  · exact checkedBlock88
  · exact checkedBlock89
  · exact checkedBlock90
  · exact checkedBlock91
  · exact checkedBlock92
  · exact checkedBlock93
  · exact checkedBlock94
  · exact checkedBlock95
  · exact checkedBlock96
  · exact checkedBlock97
  · exact checkedBlock98
  · exact checkedBlock99
  · exact checkedBlock100
  · exact checkedBlock101
  · exact checkedBlock102
  · exact checkedBlock103
  · exact checkedBlock104
  · exact checkedBlock105
  · exact checkedBlock106
  · exact checkedBlock107
  · exact checkedBlock108
  · exact checkedBlock109
  · exact checkedBlock110
  · exact checkedBlock111
  · exact checkedBlock112
  · exact checkedBlock113
  · exact checkedBlock114
  · exact checkedBlock115
  · exact checkedBlock116
  · exact checkedBlock117
  · exact checkedBlock118
  · exact checkedBlock119
  · exact checkedBlock120
  · exact checkedBlock121
  · exact checkedBlock122
  · exact checkedBlock123
  · exact checkedBlock124
  · exact checkedBlock125
  · exact checkedBlock126
  · exact checkedBlock127
  · exact checkedBlock128
  · exact checkedBlock129
  · exact checkedBlock130
  · exact checkedBlock131
  · exact checkedBlock132
  · exact checkedBlock133
  · exact checkedBlock134
  · exact checkedBlock135
  · exact checkedBlock136
  · exact checkedBlock137
  · exact checkedBlock138
  · exact checkedBlock139
  · exact checkedBlock140
  · exact checkedBlock141
  · exact checkedBlock142
  · exact checkedBlock143
  · exact checkedBlock144
  · exact checkedBlock145
  · exact checkedBlock146
  · exact checkedBlock147
  · exact checkedBlock148
  · exact checkedBlock149
  · exact checkedBlock150
  · exact checkedBlock151
  · exact checkedBlock152
  · exact checkedBlock153
  · exact checkedBlock154
  · exact checkedBlock155
  · exact checkedBlock156
  · exact checkedBlock157
  · exact checkedBlock158
  · exact checkedBlock159
  · exact checkedBlock160
  · exact checkedBlock161
  · exact checkedBlock162
  · exact checkedBlock163
  · exact checkedBlock164
  · exact checkedBlock165
  · exact checkedBlock166
  · exact checkedBlock167
  · exact checkedBlock168
  · exact checkedBlock169
  · exact checkedBlock170
  · exact checkedBlock171
  · exact checkedBlock172
  · exact checkedBlock173
  · exact checkedBlock174
  · exact checkedBlock175
  · exact checkedBlock176
  · exact checkedBlock177
  · exact checkedBlock178
  · exact checkedBlock179
  · exact checkedBlock180
  · exact checkedBlock181
  · exact checkedBlock182
  · exact checkedBlock183
  · exact checkedBlock184
  · exact checkedBlock185
  · exact checkedBlock186
  · exact checkedBlock187
  · exact checkedBlock188
  · exact checkedBlock189
  · exact checkedBlock190
  · exact checkedBlock191
  · exact checkedBlock192
  · exact checkedBlock193
  · exact checkedBlock194
  · exact checkedBlock195
  · exact checkedBlock196
  · exact checkedBlock197
  · exact checkedBlock198
  · exact checkedBlock199
  · exact checkedBlock200
  · exact checkedBlock201
  · exact checkedBlock202
  · exact checkedBlock203
  · exact checkedBlock204
  · exact checkedBlock205
  · exact checkedBlock206
  · exact checkedBlock207
  · exact checkedBlock208
  · exact checkedBlock209
  · exact checkedBlock210
  · exact checkedBlock211
  · exact checkedBlock212
  · exact checkedBlock213
  · exact checkedBlock214
  · exact checkedBlock215
  · exact checkedBlock216
  · exact checkedBlock217
  · exact checkedBlock218
  · exact checkedBlock219
  · exact checkedBlock220
  · exact checkedBlock221
  · exact checkedBlock222
  · exact checkedBlock223
  · exact checkedBlock224
  · exact checkedBlock225
  · exact checkedBlock226
  · exact checkedBlock227
  · exact checkedBlock228
  · exact checkedBlock229
  · exact checkedBlock230
  · exact checkedBlock231
  · exact checkedBlock232
  · exact checkedBlock233
  · exact checkedBlock234
  · exact checkedBlock235
  · exact checkedBlock236
  · exact checkedBlock237
  · exact checkedBlock238
  · exact checkedBlock239
  · exact checkedBlock240
  · exact checkedBlock241
  · exact checkedBlock242
  · exact checkedBlock243
  · exact checkedBlock244
  · exact checkedBlock245
  · exact checkedBlock246
  · exact checkedBlock247
  · exact checkedBlock248
  · exact checkedBlock249
  · exact checkedBlock250
  · exact checkedBlock251
  · exact checkedBlock252
  · exact checkedBlock253
  · exact checkedBlock254
  · exact checkedBlock255
  · exact checkedBlock256
  · exact checkedBlock257
  · exact checkedBlock258
  · exact checkedBlock259

end ConsecutiveOrder

end

section

namespace A397683Finish

def BoundedPrimitivePairs : Prop :=
  ∀ {p : ℕ}, p.Prime → 170 ≤ p → (p%20 = 3 ∨ p%20 = 7) → p < 260000 →
    ∃ x : ℕ, 1 ≤ x ∧ x+1 < p ∧ orderOf (x : ZMod p) = p-1 ∧
      orderOf ((x+1 : ℕ) : ZMod p) = p-1

def LargePrimitivePairs : Prop :=
  ∀ {p : ℕ}, p.Prime → 260000 ≤ p → (p%20 = 3 ∨ p%20 = 7) →
    ∃ x : ZMod p, x ≠ 0 ∧ x+1 ≠ 0 ∧ orderOf x = p-1 ∧
      orderOf (x+1) = p-1

theorem primeInput (small : BoundedPrimitivePairs) (large : LargePrimitivePairs) :
    A397683PrimePowerLift.PrimeInput := by
  intro p hp ho h3 h7
  apply A397683GoodPrimes.assemble_prime_pair _ hp ho h3 h7
  intro p hp ho h170 hres
  have hprim : ∃ x : ZMod p, x ≠ 0 ∧ x+1 ≠ 0 ∧ orderOf x = p-1 ∧
      orderOf (x+1) = p-1 := by
    by_cases hbound : p < 260000
    · obtain ⟨x, hx, hxp, hd, hd'⟩ := small hp h170 hres hbound
      refine ⟨(x : ZMod p), ?_, ?_, hd, by simpa only [Nat.cast_add, Nat.cast_one] using hd'⟩
      · rw [ne_eq, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt hx (by omega)
      · rw [← Nat.cast_one, ← Nat.cast_add, ne_eq, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt (by omega) hxp
    · exact large hp (Nat.le_of_not_gt hbound) hres
  obtain ⟨x, hx, hx', hd, hd'⟩ := hprim
  have heven : 2 ∣ p - 1 := by
    obtain ⟨k, hk⟩ := ho
    exact ⟨k, by omega⟩
  exact ⟨x, hx, hx', hd.trans hd'.symm, by rw [hd]; exact heven⟩

end A397683Finish

end

theorem OMA.solution : type_of% @OMA.S_oeis_a397683.main := by
  exact A397683CRT.characterization_of_primePowerInput
    (A397683PrimePowerLift.primePowerInput_of_primeInput
      (A397683Finish.primeInput ConsecutiveOrder.finite_primitive_pair
        (fun {p} => A397683LargePrime.large_prime p)))
    A397683CRT.obstruction3 A397683CRT.obstruction7
