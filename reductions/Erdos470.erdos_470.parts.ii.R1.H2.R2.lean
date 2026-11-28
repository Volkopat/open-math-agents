import OMAReductions.R_Erdos470_erdos_470_parts_ii_R1

/-!
# Almost-equal prime-power representations for the dyadic prime-pair step

For `s = 2^j` and `X = 16s²`, count representations of `2X - 4` as
`(X - 2 - t) + (X - 2 + t)`, for `3 ≤ t ≤ s`, by two prime powers.
A nonprime summand spoils at most one offset, and the whole interval contains
at most one higher power for each exponent. Thus a count exceeding `2j + 5`
already gives two primes at the offsets required in Melfi's construction.

H1 is an open estimate for these particular Goldbach representations. H2,
the bound on higher prime powers in a short interval, is proved below.
At every scale `j = 4y` with `y ≥ 3`, the required count is attained
when primality testing is replaced by trial division through `y`
(`dyadicRough`). This leaves factors larger than the sieve cutoff uncontrolled.
-/

-- Reduction Erdos470.erdos_470.parts.ii.R1.H2.R2 of step Erdos470.erdos_470.parts.ii.R1.H2
-- Credit: @yiklin21

namespace OMA.R_Erdos470_erdos_470_parts_ii_R1_H2_R2

open Finset

def H1 : Prop :=
  ∀ B : ℕ, ∃ j ≥ B,
    let C := 2 ^ (2 * j + 4) - 2
    2 * j + 5 < ((Icc 3 (2 ^ j)).filter fun t =>
      IsPrimePow (C - t) ∧ IsPrimePow (C + t)).card

def H2 : Prop :=
  ∀ x h E : ℕ, h * h < x → x + h < 2 ^ E →
    ((Icc x (x + h)).filter fun n => IsPrimePow n ∧ ¬ n.Prime).card ≤ E

lemma power_separation {r u e h : ℕ} (hr : 2 ≤ r) (hru : r < u)
    (he : 2 ≤ e) (hh : h * h < r ^ e) : r ^ e + h < u ^ e := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 2 := ⟨e - 2, by omega⟩
  have sq : r ^ (d + 2) ≤ r ^ (d + 1) * r ^ (d + 1) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have step : h < r ^ (d + 1) := by
    by_contra! hn
    exact hh.not_ge (sq.trans (Nat.mul_le_mul hn hn))
  calc
    r ^ (d + 2) + h < r ^ (d + 2) + r ^ (d + 1) := by omega
    _ = r ^ (d + 1) * (r + 1) := by rw [pow_succ r (d + 1)]; ring
    _ ≤ u ^ (d + 1) * u := Nat.mul_le_mul (Nat.pow_le_pow_left hru.le _) hru
    _ = u ^ (d + 2) := (pow_succ u (d + 1)).symm

/-- In an interval shorter than the square root of its left endpoint, each
exponent at least two can account for at most one nonprime prime power. -/
theorem higherPowerBound : H2 := by
  classical
  intro x h E small cap
  let I := Icc x (x + h)
  let powers (e : ℕ) := I.filter fun n => 2 ≤ e ∧ ∃ r ≥ 2, r ^ e = n
  have one_per_exponent (e : ℕ) : (powers e).card ≤ 1 := by
    apply card_le_one.mpr
    intro m hm n hn
    obtain ⟨hmI, he, r, hr, rfl⟩ := mem_filter.mp hm
    obtain ⟨hnI, _, u, hu, rfl⟩ := mem_filter.mp hn
    obtain ⟨hm₁, hm₂⟩ := mem_Icc.mp hmI
    obtain ⟨hn₁, hn₂⟩ := mem_Icc.mp hnI
    rcases lt_trichotomy r u with hru | rfl | hur
    · have sep := power_separation hr hru he (small.trans_le hm₁)
      omega
    · rfl
    · have sep := power_separation hu hur he (small.trans_le hn₁)
      omega
  have covers : I.filter (fun n => IsPrimePow n ∧ ¬ n.Prime) ⊆ (range E).biUnion powers := by
    intro n hn
    obtain ⟨hnI, hpow, composite⟩ := mem_filter.mp hn
    obtain ⟨r, e, hr, he, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
    have he₂ : 2 ≤ e := by
      by_contra! he₁
      have : e = 1 := by omega
      exact composite (by simpa [this] using hr)
    have smallExp : 2 ^ e < 2 ^ E :=
      (Nat.pow_le_pow_left hr.two_le e).trans_lt ((mem_Icc.mp hnI).2.trans_lt cap)
    exact mem_biUnion.mpr ⟨e, mem_range.mpr ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp smallExp),
      mem_filter.mpr ⟨hnI, he₂, r, hr.two_le, rfl⟩⟩
  calc
    _ ≤ ((range E).biUnion powers).card := card_le_card covers
    _ ≤ ∑ e ∈ range E, (powers e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ range E, 1 := sum_le_sum fun e _ => one_per_exponent e
    _ = E := by simp

private lemma extract_prime_pair {C s E : ℕ} (hs : s ≤ C)
    (many : E < ((Icc 3 s).filter fun t => IsPrimePow (C - t) ∧ IsPrimePow (C + t)).card)
    (few : ((Icc (C - s) (C + s)).filter fun n => IsPrimePow n ∧ ¬ n.Prime).card ≤ E) :
    ∃ t ∈ Icc 3 s, (C - t).Prime ∧ (C + t).Prime := by
  classical
  by_contra none
  let offsets := (Icc 3 s).filter fun t => IsPrimePow (C - t) ∧ IsPrimePow (C + t)
  let bad := (Icc (C - s) (C + s)).filter fun n => IsPrimePow n ∧ ¬ n.Prime
  let f (t : ℕ) := if (C - t).Prime then C + t else C - t
  have maps : Set.MapsTo f offsets bad := by
    intro t ht
    obtain ⟨hI, hl, hr⟩ := mem_filter.mp ht
    obtain ⟨ht₁, ht₂⟩ := mem_Icc.mp hI
    apply mem_filter.mpr
    by_cases h : (C - t).Prime
    · simpa only [f, if_pos h] using
        And.intro (mem_Icc.mpr (show C - s ≤ C + t ∧ C + t ≤ C + s by omega))
          (And.intro hr (fun h' => none ⟨t, hI, h, h'⟩))
    · simp only [f, if_neg h]
      exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hl, h⟩
  have inj : (↑offsets : Set ℕ).InjOn f := by
    intro t ht u hu heq
    obtain ⟨ht₁, ht₂⟩ := mem_Icc.mp (mem_filter.mp ht).1
    obtain ⟨hu₁, hu₂⟩ := mem_Icc.mp (mem_filter.mp hu).1
    dsimp [f] at heq
    split at heq <;> split at heq <;> omega
  exact many.not_ge ((card_le_card_of_injOn f maps inj).trans few)

theorem main : H1 → H2 → OMA.R_Erdos470_erdos_470_parts_ii_R1.H2 := by
  intro reps discard N
  obtain ⟨j, hj, many⟩ := reps (max N 2)
  let s := 2 ^ j
  let X := 2 ^ (2 * j + 4)
  let C := X - 2
  have hs : 4 ≤ s := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ j by omega)
  have hx : X = 16 * s * s := by
    dsimp [X, s]
    rw [show 2 * j + 4 = j + j + 4 by omega, pow_add, pow_add]
    ring
  have sq : s ≤ s * s := by nlinarith
  have margin : (2 * s) * (2 * s) + s + 2 < X := by rw [hx]; nlinarith
  have center : C + 2 = X := by change X - 2 + 2 = X; omega
  have hsc : s ≤ C := by omega
  have small : (2 * s) * (2 * s) < C - s := by omega
  have hi : C - s + 2 * s = C + s := by omega
  have cap : C - s + 2 * s < 2 ^ (2 * j + 5) := by
    rw [hi, pow_succ 2 (2 * j + 4)]
    change C + s < X * 2
    omega
  have few := discard (C - s) (2 * s) (2 * j + 5) small cap
  rw [hi] at few
  obtain ⟨t, ht, hp, hq⟩ := extract_prime_pair (C := C) (s := s) hsc many few
  obtain ⟨ht₁, ht₂⟩ := mem_Icc.mp ht
  refine ⟨2 * j + 2, t + 2, t - 2, by omega, by omega, ?_, ?_, ?_⟩
  · change (t + 2) * (t + 2 + (t - 2)) < X
    rw [show t + 2 + (t - 2) = 2 * t by omega, hx]
    have bound := Nat.mul_le_mul (Nat.add_le_add_right ht₂ 2) (Nat.mul_le_mul_left 2 ht₂)
    nlinarith
  · change (X - (t + 2)).Prime
    rwa [show X - (t + 2) = C - t by dsimp [C]; omega]
  · change (X + (t - 2)).Prime
    rwa [show X + (t - 2) = C + t by dsimp [C]; omega]

/-- The only outstanding assumption in this route concerns the count of representations. -/
theorem ofPrimePowerRepresentations (h : H1) : OMA.R_Erdos470_erdos_470_parts_ii_R1.H2 :=
  main h higherPowerBound

open scoped Classical in
/-- An explicit residue class modulo the primorial supplies simultaneous rough pairs. -/
theorem roughPairs {C y : ℕ} (room : (4 ^ y) ^ 2 ≤ C) :
    4 ^ y - 2 ≤ ((Icc 3 ((4 ^ y) ^ 2)).filter fun t =>
      ∀ p ∈ Nat.primesLE y, ¬ p ∣ C - t ∧ ¬ p ∣ C + t).card := by
  classical
  let W := 4 ^ y
  let P := primorial y
  let S := (Nat.primesLE y).filter fun p => ¬ p ∣ C
  let r := ∏ p ∈ S, p
  let t (i : ℕ) := r + i * P
  have Ppos : 0 < P := primorial_pos y
  have PW : P ≤ W := primorial_le_four_pow y
  have rpos : 0 < r :=
    prod_pos fun p hp => (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).pos
  have rP : r ≤ P := Nat.le_of_dvd Ppos (by
    change (∏ p ∈ S, p) ∣ primorial y
    rw [primorial_eq_prod_primesLE]
    exact prod_dvd_prod_of_subset _ _ _ (filter_subset _ _))
  have maps : Set.MapsTo t (Ico 2 W) ((Icc 3 (W ^ 2)).filter fun b =>
      ∀ p ∈ Nat.primesLE y, ¬ p ∣ C-b ∧ ¬ p ∣ C+b) := by
    intro i hi
    obtain ⟨hi₂, hiW⟩ := mem_Ico.mp hi
    have low : 3 ≤ t i := by
      have h := Nat.mul_le_mul hi₂ (show 1 ≤ P from Ppos)
      dsimp [t]
      omega
    have high : t i ≤ W ^ 2 := calc
      r + i * P ≤ P + i * P := Nat.add_le_add_right rP _
      _ = (i+1)*P := by ring
      _ ≤ W*W := Nat.mul_le_mul hiW PW
      _ = W^2 := (sq W).symm
    have htC : t i ≤ C := high.trans room
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨low, high⟩, ?_⟩
    intro p hp
    have prime := Nat.prime_of_mem_primesLE hp
    have hP : p ∣ P := dvd_prod_of_mem id hp
    have hmul : p ∣ i*P := dvd_mul_of_dvd_right hP i
    have ht : p ∣ t i ↔ ¬ p ∣ C := by
      change p ∣ r+i*P ↔ ¬p ∣ C
      rw [Nat.dvd_add_left hmul]
      constructor
      · intro hd
        obtain ⟨q, hq, hpq⟩ := (prime.prime.dvd_finsetProd_iff id).mp hd
        have eq := (Nat.prime_dvd_prime_iff_eq prime (Nat.prime_of_mem_primesLE (mem_filter.mp hq).1)).mp hpq
        exact eq ▸ (mem_filter.mp hq).2
      · intro h
        exact dvd_prod_of_mem id (mem_filter.mpr ⟨hp,h⟩)
    by_cases divides : p ∣ C
    · have avoids : ¬p ∣ t i := fun hd => ht.mp hd divides
      refine ⟨fun h => avoids ((Nat.dvd_add_right h).mp ?_), fun h => avoids ((Nat.dvd_add_right divides).mp h)⟩
      simpa only [Nat.sub_add_cancel htC] using divides
    · have d := ht.mpr divides
      refine ⟨fun h => divides ?_, fun h => divides ((Nat.dvd_add_left d).mp h)⟩
      simpa only [Nat.sub_add_cancel htC] using Nat.dvd_add h d
  have inj : Function.Injective t := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_right Ppos (Nat.add_left_cancel hab)
  simpa [Nat.card_Ico, W] using card_le_card_of_injOn t maps inj.injOn

open scoped Classical in
/-- At every j=4y, y≥3, enough pairs survive trial division by every prime
up to y to exceed the count required in the prime-power reduction. -/
theorem dyadicRough (y : ℕ) (hy : 3 ≤ y) :
    let j := 4*y
    let C := 2^(2*j+4)-2
    2*j+5 < ((Icc 3 (2^j)).filter fun t =>
      ∀ p ∈ Nat.primesLE y, ¬ p ∣ C-t ∧ ¬ p ∣ C+t).card := by
  have threshold : 8*y+7 < 4^y := by
    induction y, hy using Nat.le_induction with
    | base => decide
    | succ n hn ih => rw [pow_succ]; omega
  let j := 4*y
  have hs : 2^j = (4^y)^2 := by
    change 2^(4*y) = (4^y)^2
    rw [← pow_mul, Nat.mul_comm y 2, pow_mul 4 2 y, pow_mul 2 4 y]
    rfl
  have room : (4^y)^2 ≤ 2^(2*j+4)-2 := by
    rw [← hs]
    have hj : j+2 ≤ 2*j+4 := by omega
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hj
    rw [pow_add] at h
    have pos : 0 < (2:ℕ)^j := by positivity
    omega
  have count := roughPairs room
  change 2*j+5 < ((Icc 3 (2^j)).filter _).card
  rw [hs]
  exact lt_of_lt_of_le (by dsimp [j]; omega) count

lemma intersect_majorities {L : ℕ} (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hp : L < 2 * ((Ico L (2 * L)).filter P).card)
    (hq : L < 2 * ((Ico L (2 * L)).filter Q).card) :
    ∃ j, L ≤ j ∧ P j ∧ Q j := by
  let I := Ico L (2 * L)
  let U := I.filter P
  let V := I.filter Q
  change L < 2 * U.card at hp
  change L < 2 * V.card at hq
  have hsub : U ∪ V ⊆ I := union_subset (filter_subset _ _) (filter_subset _ _)
  have hbound := card_le_card hsub
  have hlen : I.card = L := by simp [I, Nat.card_Ico]; omega
  have hsum := card_union_add_card_inter U V
  have hpos : 0 < (U ∩ V).card := by omega
  obtain ⟨j, hj⟩ := card_pos.mp hpos
  obtain ⟨hu, hv⟩ := mem_inter.mp hj
  exact ⟨j, (mem_Ico.mp (mem_filter.mp hu).1).1, (mem_filter.mp hu).2, (mem_filter.mp hv).2⟩

open scoped Classical in
/-- The separate one-sided counts in the original draft also give the prime-pair step.
See @KoaOkano's PR #16840 for an earlier block argument with different windows. -/
theorem ofOneSidedMajorities
    (upper : ∀ B : ℕ, ∃ L ≥ B, L < 2 * ((Ico L (2 * L)).filter fun j =>
      ∃ b : ℕ, 4 * b ≤ 2 ^ j ∧ (2 ^ (2 * j + 2) + b).Prime).card)
    (lower : ∃ L₀ : ℕ, ∀ L ≥ L₀, L < 2 * ((Ico L (2 * L)).filter fun j =>
      ∃ a : ℕ, 2 ^ j ≤ 2 * a ∧ a ≤ 2 ^ j ∧ (2 ^ (2 * j + 2) - a).Prime).card) :
    OMA.R_Erdos470_erdos_470_parts_ii_R1.H2 := by
  classical
  intro N
  obtain ⟨L₀, lower⟩ := lower
  obtain ⟨L, hL, hu⟩ := upper (max (max N L₀) 4)
  obtain ⟨j, hj, ⟨b, hb, hq⟩, ⟨a, ha, ha', hp⟩⟩ :=
    intersect_majorities _ _ hu (lower L (by omega))
  have hj4 : 4 ≤ j := by omega
  have hs : 16 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide : 0 < 2) hj4
  refine ⟨2 * j, a, b, by omega, by omega, ?_, hp, hq⟩
  have hx : 2 ^ (2 * j + 2) = 4 * 2 ^ j * 2 ^ j := by
    rw [show 2 * j + 2 = j + j + 2 by omega, pow_add, pow_add]
    ring
  have hprod : a * (a + b) ≤ 2 ^ j * (2 ^ j + 2 ^ j) :=
    Nat.mul_le_mul ha' (Nat.add_le_add ha' (by omega))
  rw [hx]
  nlinarith [show 0 < (2 ^ j) * (2 ^ j) by positivity]

end OMA.R_Erdos470_erdos_470_parts_ii_R1_H2_R2
