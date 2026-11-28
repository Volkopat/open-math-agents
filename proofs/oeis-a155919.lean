import OMAStatements.S_oeis_a155919
import Mathlib

-- Problem: OEIS A155919, conjecture of Andrew Howroyd: the number a(n) of values of
-- x^2 + y^2 + z^2 in Z/nZ satisfies a(2^k) = A171231(k-1) = (10 * 2^(k-1) + 3 - (-1)^(k-1))/6
-- for k > 0, and a(p^k) = p^k for each odd prime p.
-- Statement: statements/oeis-a155919.lean (declaration OMA.S_oeis_a155919.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof, odd p. There are a, b with a^2 + b^2 == -1 (mod p) and p not a divisor of a. A lift
-- a -> a + t p^j gives a^2 + b^2 + 1 == 0 (mod p^k) for each k. Then for t = (r - 1)/2 the
-- triple (t a, t b, t + 1) has the sum of squares t^2 (a^2 + b^2 + 1) + 2 t + 1 = r. So the
-- map is surjective.
-- Proof, p = 2. Let S(k) be the set of r < 2^k that are sums of three squares modulo 2^k.
-- (1) Each u == 1 (mod 8) is a square modulo 2^j (lift s -> s + 2^(j-1)). Thus each r that is
-- 1, 2, 3, 5 or 6 modulo 8 is in S(k) (r = s^2 + e with e = 0, 1, 2, 4, 5).
-- (2) For k >= 3, no r == 7 (mod 8) is in S(k), because squares are 0, 1, 4 modulo 8.
-- (3) 4 r is in S(k+2) if and only if r is in S(k), because a sum of three squares that is
-- divisible by 4 has three even terms.
-- So |S(k+3)| = |S(k+1)| + 5 * 2^k, with |S(1)| = 2 and |S(2)| = 4, and the formula follows by
-- induction.

namespace OMA.A155919

open Finset OMA.S_oeis_a155919


lemma lift_step (p j : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hj : 1 ≤ j) (a b : ℤ)
    (hpa : ¬ (p : ℤ) ∣ a) (h : (p : ℤ) ^ j ∣ a ^ 2 + b ^ 2 + 1) :
    ∃ a' : ℤ, ¬ (p : ℤ) ∣ a' ∧ (p : ℤ) ^ (j + 1) ∣ a' ^ 2 + b ^ 2 + 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, hc⟩ := h
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have ha0 : ((a : ℤ) : ZMod p) ≠ 0 := fun h0 => hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 h0)
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (p : ℤ) ∣ c + 2 * a * t := by
    refine ⟨(((-(c : ZMod p)) * (2 * (a : ZMod p))⁻¹).val : ℤ), ?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    push_cast
    rw [ZMod.natCast_zmod_val]
    field_simp
    ring
  obtain ⟨d, hd⟩ := ht
  refine ⟨a + t * (p : ℤ) ^ j, ?_, ?_⟩
  · intro hdv
    apply hpa
    have h1 : (p : ℤ) ∣ t * (p : ℤ) ^ j := Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    exact (dvd_add_left h1).1 hdv
  · refine ⟨d + t ^ 2 * (p : ℤ) ^ (j - 1), ?_⟩
    have e : (p : ℤ) ^ j = (p : ℤ) ^ (j - 1) * p := by rw [← pow_succ]; congr 1; omega
    have e1 : (p : ℤ) ^ (j + 1) = (p : ℤ) ^ j * p := pow_succ _ _
    rw [e1]
    generalize (p : ℤ) ^ j = P at hc e ⊢
    generalize (p : ℤ) ^ (j - 1) = q at e ⊢
    linear_combination hc + P * hd + t ^ 2 * P * e

lemma exists_iso (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ k : ℕ, 1 ≤ k → ∃ a b : ℤ, ¬ (p : ℤ) ∣ a ∧ (p : ℤ) ^ k ∣ a ^ 2 + b ^ 2 + 1 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    obtain ⟨A, B, hAB⟩ := ZMod.sq_add_sq p (-1)
    have key : ∀ X Y : ZMod p, X ^ 2 + Y ^ 2 = -1 → X ≠ 0 →
        ∃ a b : ℤ, ¬ (p : ℤ) ∣ a ∧ (p : ℤ) ^ 1 ∣ a ^ 2 + b ^ 2 + 1 := by
      intro X Y hXY hX
      refine ⟨(X.val : ℤ), (Y.val : ℤ), ?_, ?_⟩
      · intro hd
        apply hX
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
        simpa using this
      · rw [pow_one]
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hXY]; ring
    by_cases hA : A = 0
    · have hB : B ≠ 0 := by
        intro hB
        rw [hA, hB] at hAB
        have : (1 : ZMod p) = 0 := by linear_combination hAB
        exact one_ne_zero this
      exact key B A (by rw [add_comm]; exact hAB) hB
    · exact key A B hAB hA
  | succ j hj ih =>
    obtain ⟨a, b, hpa, hab⟩ := ih
    obtain ⟨a', ha', hab'⟩ := lift_step p j hp2 hj a b hpa hab
    exact ⟨a', b, ha', hab'⟩

lemma odd_surj (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hk : 1 ≤ k) (r : ZMod (p ^ k)) :
    ∃ x y z : ZMod (p ^ k), x ^ 2 + y ^ 2 + z ^ 2 = r := by
  have hp : p.Prime := Fact.out
  obtain ⟨a, b, _, hab⟩ := exists_iso p hp2 k hk
  have hAB : ((a : ℤ) : ZMod (p ^ k)) ^ 2 + ((b : ℤ) : ZMod (p ^ k)) ^ 2 + 1 = 0 := by
    have hd : (((p ^ k : ℕ) : ℤ)) ∣ a ^ 2 + b ^ 2 + 1 := by push_cast; exact hab
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ k)).2 hd
    push_cast at this
    exact this
  have hodd : Odd (p ^ k) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2u : (2 : ZMod (p ^ k)) * (((p ^ k + 1) / 2 : ℕ) : ZMod (p ^ k)) = 1 := by
    have h1 : 2 * ((p ^ k + 1) / 2) = p ^ k + 1 := by
      obtain ⟨m, hm⟩ := hodd
      omega
    have h3 := congrArg (fun x : ℕ => (x : ZMod (p ^ k))) h1
    simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add,
      Nat.cast_ofNat] at h3
    exact h3
  generalize (((p ^ k + 1) / 2 : ℕ) : ZMod (p ^ k)) = u at h2u
  generalize ((a : ℤ) : ZMod (p ^ k)) = A at hAB
  generalize ((b : ℤ) : ZMod (p ^ k)) = B at hAB
  obtain ⟨t, ht⟩ : ∃ t, t = (r - 1) * u := ⟨_, rfl⟩
  refine ⟨t * A, t * B, t + 1, ?_⟩
  linear_combination t ^ 2 * hAB + (r - 1) * h2u + 2 * ht

theorem odd_case (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) : a (p ^ k) = p ^ k := by
  have hfact : Fact p.Prime := ⟨hp⟩
  unfold a
  have hsurj : Set.range (fun v : ZMod (p ^ k) × ZMod (p ^ k) × ZMod (p ^ k) =>
      v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) = Set.univ := by
    rw [Set.range_eq_univ]
    intro r
    obtain ⟨x, y, z, h⟩ := odd_surj p k hp2 hk r
    exact ⟨(x, y, z), h⟩
  rw [hsurj, Set.ncard_univ, Nat.card_zmod]


/-- r is a sum of three squares modulo 2^k. -/
def Rep (k r : ℕ) : Prop :=
  ∃ x y z : ℕ, (2 : ℤ) ^ k ∣ (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 - (r : ℤ)

/-- The residues modulo 2^k that are sums of three squares. -/
def S (k : ℕ) : Set ℕ := {r | r < 2 ^ k ∧ Rep k r}

lemma sq_mod8 (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h : x ^ 2 % 8 = ((x % 8) ^ 2) % 8 := by simp [Nat.pow_mod]
  have hlt : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [h]
  interval_cases (x % 8) <;> simp

lemma sq_mod4 (x : ℕ) : (x ^ 2 % 4 = 0 ∧ x % 2 = 0) ∨ (x ^ 2 % 4 = 1 ∧ x % 2 = 1) := by
  rcases Nat.even_or_odd' x with ⟨q, rfl | rfl⟩
  · left
    have h : (2 * q) ^ 2 = 4 * q ^ 2 := by ring
    rw [h]; omega
  · right
    have h : (2 * q + 1) ^ 2 = 4 * (q ^ 2 + q) + 1 := by ring
    rw [h]; omega

lemma a_eq (k : ℕ) : a (2 ^ k) = (S k).ncard := by
  have hne : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  unfold a
  rw [← Set.ncard_image_of_injective _ (ZMod.val_injective (2 ^ k))]
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨⟨X, Y, Z⟩, rfl⟩, rfl⟩
    refine ⟨ZMod.val_lt _, X.val, Y.val, Z.val, ?_⟩
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((X.val : ℤ) ^ 2 + (Y.val : ℤ) ^ 2 + (Z.val : ℤ) ^ 2
        - (((X ^ 2 + Y ^ 2 + Z ^ 2 : ZMod (2 ^ k)).val : ℕ) : ℤ)) (2 ^ k)).1
      (by push_cast; simp only [ZMod.natCast_zmod_val]; ring)
    have e : (((2 ^ k : ℕ) : ℤ)) = (2 : ℤ) ^ k := by push_cast; rfl
    rw [e] at hd
    exact hd
  · rintro ⟨hr, x, y, z, hd⟩
    refine ⟨_, ⟨((x : ZMod (2 ^ k)), (y : ZMod (2 ^ k)), (z : ZMod (2 ^ k))), rfl⟩, ?_⟩
    have e : (((2 ^ k : ℕ) : ℤ)) = (2 : ℤ) ^ k := by push_cast; rfl
    rw [← e] at hd
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ k)).2 hd
    push_cast at h0
    have h1 : (x : ZMod (2 ^ k)) ^ 2 + (y : ZMod (2 ^ k)) ^ 2 + (z : ZMod (2 ^ k)) ^ 2
        = (r : ZMod (2 ^ k)) := by linear_combination h0
    show ZMod.val ((x : ZMod (2 ^ k)) ^ 2 + (y : ZMod (2 ^ k)) ^ 2 + (z : ZMod (2 ^ k)) ^ 2) = r
    rw [h1, ZMod.val_natCast_of_lt hr]

/-- Each u ≡ 1 (mod 8) is a square modulo 2^j. -/
lemma sq_lift : ∀ j : ℕ, ∀ u : ℕ, u % 8 = 1 →
    ∃ s : ℕ, s % 2 = 1 ∧ (2 : ℤ) ^ j ∣ (s : ℤ) ^ 2 - u := by
  intro j
  induction j with
  | zero => intro u _; exact ⟨1, rfl, by simp⟩
  | succ j ih =>
    intro u hu
    by_cases hj : j < 3
    · refine ⟨1, rfl, ?_⟩
      have h8 : (8 : ℤ) ∣ ((1 : ℕ) : ℤ) ^ 2 - (u : ℤ) := by
        have : (8 : ℤ) ∣ 1 - (u : ℤ) := by omega
        simpa using this
      have h2 : (2 : ℤ) ^ (j + 1) ∣ 2 ^ 3 := pow_dvd_pow 2 (by omega)
      have e : (2 : ℤ) ^ 3 = 8 := by norm_num
      rw [e] at h2
      exact Dvd.dvd.trans h2 h8
    · obtain ⟨s, hs, c, hc⟩ := ih u hu
      rcases Int.even_or_odd' c with ⟨m, hm | hm⟩
      · exact ⟨s, hs, m, by rw [hc, hm, pow_succ]; ring⟩
      · refine ⟨s + 2 ^ (j - 1), ?_, ?_⟩
        · have e : 2 ^ (j - 1) = 2 * 2 ^ (j - 2) := by rw [← pow_succ']; congr 1; omega
          omega
        · obtain ⟨q, hq⟩ : ∃ q : ℤ, (s : ℤ) = 2 * q + 1 := ⟨((s / 2 : ℕ) : ℤ), by omega⟩
          refine ⟨m + q + 1 + 2 ^ (j - 3), ?_⟩
          have e1 : (2 : ℤ) ^ j = 2 ^ (j - 1) * 2 := by rw [← pow_succ]; congr 1; omega
          have e3 : (2 : ℤ) ^ (j - 1) = 2 ^ (j - 3) * 4 := by
            have : (4 : ℤ) = 2 ^ 2 := by norm_num
            rw [this, ← pow_add]; congr 1; omega
          have e0 : (2 : ℤ) ^ (j + 1) = 2 ^ j * 2 := pow_succ _ _
          rw [e0]
          push_cast
          generalize (2 : ℤ) ^ j = P at hc e1 ⊢
          generalize (2 : ℤ) ^ (j - 1) = P1 at e1 e3 ⊢
          generalize (2 : ℤ) ^ (j - 3) = P3 at e3 ⊢
          linear_combination hc + P * hm + (-1 - 2 * q - 2 * P3) * e1 + 2 * P1 * hq + P1 * e3

lemma rep_of_good (K r : ℕ) (h4 : r % 4 ≠ 0) (h8 : r % 8 ≠ 7) : Rep K r := by
  have key : ∀ e x y : ℕ, e ≤ r → (r - e) % 8 = 1 → x ^ 2 + y ^ 2 = e → Rep K r := by
    intro e x y he hu hxy
    obtain ⟨s, _, hs⟩ := sq_lift K (r - e) hu
    refine ⟨s, x, y, ?_⟩
    have h : (s : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 - r = (s : ℤ) ^ 2 - ((r - e : ℕ) : ℤ) := by
      rw [Nat.cast_sub he, ← hxy]; push_cast; ring
    rw [h]; exact hs
  have hr : r % 8 = 1 ∨ r % 8 = 2 ∨ r % 8 = 3 ∨ r % 8 = 5 ∨ r % 8 = 6 := by omega
  rcases hr with h | h | h | h | h
  · exact key 0 0 0 (by omega) (by omega) rfl
  · exact key 1 1 0 (by omega) (by omega) rfl
  · exact key 2 1 1 (by omega) (by omega) rfl
  · exact key 4 2 0 (by omega) (by omega) rfl
  · exact key 5 2 1 (by omega) (by omega) rfl

lemma good_of_rep (K r : ℕ) (hK : 3 ≤ K) (h : Rep K r) : r % 8 ≠ 7 := by
  obtain ⟨x, y, z, hd⟩ := h
  have h2 : (2 : ℤ) ^ 3 ∣ 2 ^ K := pow_dvd_pow 2 hK
  have e : (2 : ℤ) ^ 3 = 8 := by norm_num
  rw [e] at h2
  have h8 : (8 : ℤ) ∣ ((x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ℤ) - (r : ℤ) := by
    push_cast; exact Dvd.dvd.trans h2 hd
  have hx := sq_mod8 x
  have hy := sq_mod8 y
  have hz := sq_mod8 z
  omega

lemma rep_four (K r : ℕ) : Rep (K + 2) (4 * r) ↔ Rep K r := by
  have e2 : (2 : ℤ) ^ (K + 2) = 4 * 2 ^ K := by rw [pow_add]; ring
  constructor
  · rintro ⟨x, y, z, hd⟩
    rw [e2] at hd
    have h4 : (4 : ℤ) ∣ ((x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ℤ) - ((4 * r : ℕ) : ℤ) := by
      push_cast; exact Dvd.dvd.trans (Dvd.intro _ rfl) hd
    have hev : x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 := by
      rcases sq_mod4 x with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases sq_mod4 y with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
        rcases sq_mod4 z with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> omega
    obtain ⟨x', rfl⟩ : ∃ x', x = 2 * x' := ⟨x / 2, by omega⟩
    obtain ⟨y', rfl⟩ : ∃ y', y = 2 * y' := ⟨y / 2, by omega⟩
    obtain ⟨z', rfl⟩ : ∃ z', z = 2 * z' := ⟨z / 2, by omega⟩
    refine ⟨x', y', z', ?_⟩
    have e : ((2 * x' : ℕ) : ℤ) ^ 2 + ((2 * y' : ℕ) : ℤ) ^ 2 + ((2 * z' : ℕ) : ℤ) ^ 2
        - ((4 * r : ℕ) : ℤ) = 4 * ((x' : ℤ) ^ 2 + (y' : ℤ) ^ 2 + (z' : ℤ) ^ 2 - (r : ℤ)) := by
      push_cast; ring
    rw [e] at hd
    exact (mul_dvd_mul_iff_left (by norm_num)).1 hd
  · rintro ⟨x, y, z, c, hc⟩
    refine ⟨2 * x, 2 * y, 2 * z, c, ?_⟩
    rw [e2]; push_cast
    linear_combination 4 * hc

lemma rep_small (k r : ℕ) (hr : r ≤ 3) : Rep k r := by
  interval_cases r
  · exact ⟨0, 0, 0, by simp⟩
  · exact ⟨1, 0, 0, by simp⟩
  · exact ⟨1, 1, 0, by norm_num⟩
  · exact ⟨1, 1, 1, by norm_num⟩

lemma cnt5 (m : ℕ) : ({r | r < 8 * m ∧ r % 4 ≠ 0 ∧ r % 8 ≠ 7} : Set ℕ).ncard = 5 * m := by
  have h : ({r | r < 8 * m ∧ r % 4 ≠ 0 ∧ r % 8 ≠ 7} : Set ℕ)
      = ↑((range (8 * m)).filter (fun r => r % 4 ≠ 0 ∧ r % 8 ≠ 7)) := by
    ext r; simp
  rw [h, Set.ncard_coe_finset]
  clear h
  induction m with
  | zero => simp
  | succ m ih =>
    rw [card_filter] at ih ⊢
    rw [show 8 * (m + 1) = 8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
    simp only [sum_range_succ]
    rw [ih]
    have c0 : ¬ ((8 * m) % 4 ≠ 0 ∧ (8 * m) % 8 ≠ 7) := by omega
    have c1 : (8 * m + 1) % 4 ≠ 0 ∧ (8 * m + 1) % 8 ≠ 7 := by omega
    have c2 : (8 * m + 1 + 1) % 4 ≠ 0 ∧ (8 * m + 1 + 1) % 8 ≠ 7 := by omega
    have c3 : (8 * m + 1 + 1 + 1) % 4 ≠ 0 ∧ (8 * m + 1 + 1 + 1) % 8 ≠ 7 := by omega
    have c4 : ¬ ((8 * m + 1 + 1 + 1 + 1) % 4 ≠ 0 ∧ (8 * m + 1 + 1 + 1 + 1) % 8 ≠ 7) := by omega
    have c5 : (8 * m + 1 + 1 + 1 + 1 + 1) % 4 ≠ 0 ∧ (8 * m + 1 + 1 + 1 + 1 + 1) % 8 ≠ 7 := by
      omega
    have c6 : (8 * m + 1 + 1 + 1 + 1 + 1 + 1) % 4 ≠ 0
        ∧ (8 * m + 1 + 1 + 1 + 1 + 1 + 1) % 8 ≠ 7 := by omega
    have c7 : ¬ ((8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1) % 4 ≠ 0
        ∧ (8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1) % 8 ≠ 7) := by omega
    rw [if_neg c0, if_pos c1, if_pos c2, if_pos c3, if_neg c4, if_pos c5, if_pos c6, if_neg c7]
    ring

lemma S_finite (k : ℕ) : (S k).Finite :=
  (Set.finite_lt_nat (2 ^ k)).subset (fun r hr => hr.1)

lemma S_rec (K : ℕ) : (S (K + 3)).ncard = (S (K + 1)).ncard + 5 * 2 ^ K := by
  have e8 : 2 ^ (K + 3) = 8 * 2 ^ K := by ring
  have e4 : 2 ^ (K + 3) = 4 * 2 ^ (K + 1) := by ring
  have hsplit : S (K + 3) = ((fun r => 4 * r) '' S (K + 1))
      ∪ {r | r < 8 * 2 ^ K ∧ r % 4 ≠ 0 ∧ r % 8 ≠ 7} := by
    ext r
    constructor
    · rintro ⟨hr, hrep⟩
      by_cases h4 : r % 4 = 0
      · left
        refine ⟨r / 4, ⟨by omega, ?_⟩, by show 4 * (r / 4) = r; omega⟩
        have h : r = 4 * (r / 4) := by omega
        rw [h] at hrep
        exact (rep_four (K + 1) _).1 hrep
      · right
        exact ⟨by omega, h4, good_of_rep (K + 3) r (by omega) hrep⟩
    · rintro (⟨r', ⟨hr', hrep⟩, rfl⟩ | ⟨hr, h4, h8⟩)
      · show 4 * r' < 2 ^ (K + 3) ∧ Rep (K + 3) (4 * r')
        exact ⟨by omega, (rep_four (K + 1) r').2 hrep⟩
      · exact ⟨by omega, rep_of_good _ r h4 h8⟩
  have hdisj : Disjoint ((fun r => 4 * r) '' S (K + 1))
      {r | r < 8 * 2 ^ K ∧ r % 4 ≠ 0 ∧ r % 8 ≠ 7} := by
    rw [Set.disjoint_left]
    rintro _ ⟨r', _, rfl⟩ ⟨_, h4, _⟩
    have h4' : (4 * r') % 4 ≠ 0 := h4
    omega
  have hf1 : ((fun r => 4 * r) '' S (K + 1)).Finite := (S_finite _).image _
  have hf2 : ({r | r < 8 * 2 ^ K ∧ r % 4 ≠ 0 ∧ r % 8 ≠ 7} : Set ℕ).Finite :=
    (Set.finite_lt_nat (8 * 2 ^ K)).subset (fun r hr => hr.1)
  rw [hsplit, Set.ncard_union_eq hdisj hf1 hf2,
    Set.ncard_image_of_injective _ (mul_right_injective₀ (by norm_num)), cnt5]

lemma S_small (k : ℕ) (hk : k ≤ 2) : (S k).ncard = 2 ^ k := by
  have h : S k = ↑(range (2 ^ k)) := by
    ext r
    constructor
    · rintro ⟨hr, _⟩; simpa using hr
    · intro hr
      have hr' : r < 2 ^ k := by simpa using hr
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk
      exact ⟨hr', rep_small k r (by omega)⟩
  rw [h, Set.ncard_coe_finset, card_range]

lemma S_formula : ∀ k : ℕ, 6 * ((S (k + 1)).ncard : ℤ) = 10 * 2 ^ k + 3 - (-1) ^ k ∧
    6 * ((S (k + 2)).ncard : ℤ) = 10 * 2 ^ (k + 1) + 3 - (-1) ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    rw [S_small 1 (by norm_num), S_small 2 (by norm_num)]
    constructor <;> norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h := S_rec k
    have e : k + 1 + 2 = k + 3 := by ring
    rw [e, h]
    push_cast
    have e2 : (2 : ℤ) ^ (k + 1 + 1) = 2 ^ k * 4 := by ring
    have e3 : (-1 : ℤ) ^ (k + 1 + 1) = (-1) ^ k := by ring
    rw [e2, e3]
    linear_combination ih.1

theorem two_case (k : ℕ) (hk : 0 < k) :
    6 * (a (2 ^ k) : ℤ) = 10 * 2 ^ (k - 1) + 3 - (-1) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [a_eq, Nat.add_sub_cancel]
  exact (S_formula j).1

end OMA.A155919

theorem OMA.solution : type_of% @OMA.S_oeis_a155919.main :=
  ⟨fun k hk => OMA.A155919.two_case k hk,
    fun p k hp hp2 hk => OMA.A155919.odd_case p k hp hp2 hk⟩
