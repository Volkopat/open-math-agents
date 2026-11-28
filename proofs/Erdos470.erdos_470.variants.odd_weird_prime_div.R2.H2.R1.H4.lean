import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

/-!
# Proof of Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1.H4

Proves that every odd primitive abundant multiple of 45 with 4 or 5 distinct prime
factors, coprime to 7, 11, and 13, and divisible by some prime r in
[17, 19, 23, 29, 31, 37, 41, 43], is pseudoperfect.

Architecture:
1. Final-prime interval translation lemmas (`FinalPrime`): given a deficient cofactor `B`
   whose proper-divisor subset sums cover `[L, P(B) - L]` with directed gap `g = 2`,
   any primitive abundant coprime prime-power extension `B * q^(j+1)` with excess `E >= L`
   (and `2 <= B - P(B)` when `j = 0`) is pseudoperfect.
2. Core subset-sum certification and inductive prime-power lifting (`CoreLift`):
   certifies 17 base numbers (`45*17*19` plus 16 three-prime bases `3^a0 * 5^b0 * r`),
   lifts along `r`, `5`, `3` via `HasRelGap`, and lifts along the coprime 4th prime `p`
   via `middle_next`, preserving `[L, P - L]` and gap `2`.
3. Pure-Nat branch-and-bound verifiers (`SmallExcess`): proves that whenever `3` does not
   divide `sigma 1 n` (forcing even `v_5(n) >= 2` and restricted exponents), the excess
   satisfies `E >= L`, and every deficient even-exponent 4-prime base satisfies `2 <= 2*B - sigma 1 B`.
4. Main classification and assembly (`OMA.solution`).
-/

namespace Erdos470R2H2R1H4

open Finset ArithmeticFunction
open OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

/- ## Section 1: Final-prime interval translation -/

section FinalPrime

private lemma final_prime_alternatives {P D q L g E : ℤ}
    (hg : 1 ≤ g) (hL : 1 ≤ L) (hD : 2 ≤ D) (hq : 3 ≤ q)
    (big : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ P)
    (excess : E = 2 * P - D * (q - 1)) (low : L ≤ E) :
    (g * q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q * P) ∨
    (q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q ∧ E ≤ 2 * P + D + q - L) ∨
    (L ≤ E ∧ E ≤ P - L) := by
  have gL : 0 ≤ g * L := mul_nonneg (by omega) (by omega)
  have gg : 0 ≤ g * g := mul_self_nonneg g
  have g1L : 0 ≤ (g - 1) * L := mul_nonneg (by omega) (by omega)
  have pbound : 5 * L ≤ P := by nlinarith only [big, hg, hL, gg, g1L]
  have dpos : 0 ≤ D := by omega
  have dlt : D < P := by nlinarith only [excess, low, hL, mul_nonneg (show 0 ≤ q - 3 by omega) dpos]
  by_cases small : g * q ≤ P - 2 * L + 1
  · left
    refine ⟨small, ?_⟩
    have t := mul_le_mul_of_nonneg_right hq (show 0 ≤ P by omega)
    nlinarith only [t, dlt, pbound, hL]
  · have dcap : D < 8 * g := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ q - 1 by omega)
      have w := mul_nonneg (show 0 ≤ g by omega) (show 0 ≤ q - 2 by omega)
      nlinarith only [small, k, w, excess, low, pbound, hL]
    have bigq : 2 * L + 8 * g + 8 < q := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ g by omega)
      nlinarith only [k, small, big, gg, gL, hg]
    by_cases overlap : q ≤ P - 2 * L + 1
    · right; left
      have h := mul_nonneg dpos (show 0 ≤ q - 1 by omega)
      exact ⟨overlap, by omega, by linarith only [excess, h, hD, bigq, hg, hL]⟩
    · right; right
      have k := mul_le_mul_of_nonneg_left hD (show 0 ≤ q - 1 by omega)
      exact ⟨low, by nlinarith only [k, excess, overlap, pbound]⟩

private lemma four_interval_join {P D q L A : ℤ} (w : q ≤ P - 2 * L + 1) (v : D + 2 * L - 1 ≤ q)
    (lo : L ≤ A) (hi : A ≤ 2 * P + D + q - L) :
    (L ≤ A ∧ A ≤ P - L) ∨ (L ≤ A - q ∧ A - q ≤ P - L) ∨
    (L ≤ A - (P + D) ∧ A - (P + D) ≤ P - L) ∨
    (L ≤ A - (P + D + q) ∧ A - (P + D + q) ≤ P - L) := by omega

private lemma nondivisor {P D q : ℤ} (hD : 0 < D)
    (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1)) : ¬ D ∣ 2 * P := by
  rintro ⟨x, h⟩
  rw [h] at low high
  have a := (mul_lt_mul_iff_right₀ hD).mp low
  have b := (mul_lt_mul_iff_right₀ hD).mp high
  omega

private lemma repeated_bounds {P D q L : ℤ} (hD : 0 < D) (hq : 3 ≤ q)
    (large : 6 * L ≤ P) (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1))
    (divone : ¬ D ∣ 2 * P) :
    3 ≤ D ∧ q ≤ P - 2 * L + 1 := by
  have three : 3 ≤ D := by
    by_contra! bad
    interval_cases D <;> simp at divone
  refine ⟨three, ?_⟩
  have a := mul_le_mul_of_nonneg_right three (show 0 ≤ q - 2 by omega)
  omega

private lemma repeated_alternatives {P D q L g E : ℤ} (hg : 1 ≤ g) (hL : 1 ≤ L)
    (hD : 0 < D) (hq : 3 ≤ q) (big : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ P)
    (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1)) (excess : E ≤ 2 * P + D - q) :
    (g * q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q * P ∧ E ≤ 2 * P + D + q * P - L) ∨
    (q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q ∧ E ≤ 2 * P + D + q - L) := by
  have gL := mul_nonneg (show 0 ≤ g - 1 by omega) (show 0 ≤ L by omega)
  have gg := mul_self_nonneg g
  have pl : 6 * L ≤ P := by nlinarith only [big, hg, gL, gg]
  have pd : D < 2 * P := by nlinarith only [low, mul_nonneg (show 0 ≤ D by omega) (show 0 ≤ q - 3 by omega)]
  obtain ⟨_, qw⟩ := repeated_bounds hD hq pl low high (nondivisor hD low high)
  by_cases small : g * q ≤ P - 2 * L + 1
  · left
    have covers := mul_le_mul_of_nonneg_right hq (show 0 ≤ P by omega)
    exact ⟨small, by omega, by omega⟩
  · right
    have largeQ : 2 * L + 8 * g + 8 < q := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ g by omega)
      nlinarith only [k, small, big, gg, gL, hg, hL]
    have dcap : D < 8 * g := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_right h (show 0 ≤ q - 2 by omega)
      have w := mul_nonneg (show 0 ≤ g by omega) (show 0 ≤ q - 4 by omega)
      nlinarith only [k, low, small, pl, hL, w]
    exact ⟨qw, by omega, by omega⟩

private lemma repeat_from_excess {P D q : ℤ} (hq : 0 < q - 1) (hs : 0 < 2 * P + D)
    (E : ℕ → ℤ) (base : E 0 = -D)
    (next : ∀ j, E (j + 1) = q * E j + (2 * P + D))
    (j : ℕ) (firstDef : E 1 < 0) (previousDef : E j < 0) (abundant : 0 < E (j + 1)) :
    D * (q - 2) < 2 * P ∧ 2 * P < D * (q - 1) ∧ E (j + 1) ≤ 2 * P + D - q := by
  have closed (t : ℕ) : (q - 1) * E t = q ^ t * (2 * P - D * (q - 2)) - (2 * P + D) := by
    induction t with
    | zero => rw [base, pow_zero]; ring
    | succ t ih =>
      rw [next, pow_succ]
      calc _ = q * ((q - 1) * E t) + (q - 1) * (2 * P + D) := by ring
        _ = _ := by rw [ih]; ring
  have c := closed (j + 1)
  have prodPos := mul_pos hq abundant
  have pos : 0 < 2 * P - D * (q - 2) := by
    by_contra! h
    have x := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (show 0 ≤ q by omega) (j + 1)) h
    omega
  have one := next 0
  rw [base] at one
  have qNonneg : 0 ≤ q := by omega
  have neg := mul_le_mul_of_nonneg_left (show E j ≤ -1 by omega) qNonneg
  refine ⟨by omega, ?_, ?_⟩
  · nlinarith only [firstDef, one]
  · rw [next]; linarith only [neg]

private lemma index_for_translate {A : Set ℤ} {T L H g r x : ℤ}
    (hr : 0 < r) (wide : r * g ≤ H - L + 1) (last : T ∈ A)
    (gap : ∀ k : ℤ, 0 ≤ k → k < T → ∃ i ∈ A, k - g < i ∧ i ≤ k)
    (lo : L ≤ x) (hi : x ≤ H + r * T) :
    ∃ i ∈ A, L ≤ x - r * i ∧ x - r * i ≤ H := by
  by_cases finished : L + r * T ≤ x
  · exact ⟨T, last, by omega, by omega⟩
  let k := (x - L) / r
  have kp : k < T := Int.ediv_lt_of_lt_mul hr (by rw [mul_comm T r]; omega)
  obtain ⟨i, mem, lower, upper⟩ := gap k (Int.ediv_nonneg (by omega) (by omega)) kp
  have decomp := Int.emod_add_mul_ediv (x - L) r
  change (x - L) % r + r * k = x - L at decomp
  have remLo := Int.emod_nonneg (x - L) (by omega : r ≠ 0)
  have remHi := Int.emod_lt_of_pos (x - L) hr
  have left := mul_le_mul_of_nonneg_left upper (le_of_lt hr)
  have right := mul_le_mul_of_nonneg_left (show k - g + 1 ≤ i by omega) (le_of_lt hr)
  rw [mul_add, mul_sub, mul_one] at right
  exact ⟨i, mem, by omega, by omega⟩

private lemma middle_next {A B C : Set ℤ} {T P b L g r : ℤ}
    (hr : 0 < r) (wide : r * g ≤ P - 2 * L + 1) (overlap : b + 2 * L ≤ P + r * T + 1)
    (endA : T ∈ A) (gap : ∀ k : ℤ, 0 ≤ k → k < T → ∃ i ∈ A, k - g < i ∧ i ≤ k)
    (central : ∀ y : ℤ, L ≤ y → y ≤ P - L → y ∈ B)
    (layers : ∀ i ∈ A, ∀ y ∈ B, y + r * i ∈ C ∧ b + y + r * i ∈ C) :
    ∀ x : ℤ, L ≤ x → x ≤ b + P + r * T - L → x ∈ C := by
  intro x low high
  by_cases first : x ≤ P - L + r * T
  · obtain ⟨i, hi, h, k⟩ := index_for_translate hr (show r * g ≤ (P - L) - L + 1 by omega) endA gap low first
    have represented := (layers i hi _ (central _ h k)).1
    convert represented using 1
    ring
  · obtain ⟨i, hi, h, k⟩ := index_for_translate (x := x - b) hr (show r * g ≤ (P - L) - L + 1 by omega) endA gap
      (show L ≤ x - b by omega) (show x - b ≤ (P - L) + r * T by omega)
    have represented := (layers i hi _ (central _ h k)).2
    convert represented using 1
    ring

private lemma pseudoperfect_of_excess {m : ℕ} (pos : 0 < m) {s : Finset ℕ}
    (subset : s ⊆ m.properDivisors)
    (sum : (∑ d ∈ s, (d : ℤ)) = (sigma 1 m : ℤ) - 2 * (m : ℤ)) : m.Pseudoperfect := by
  classical
  have total : (sigma 1 m : ℤ) = (∑ d ∈ m.properDivisors, (d : ℤ)) + m := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp
  have rest := sum_sdiff subset (f := fun x : ℕ => (x : ℤ))
  refine ⟨pos, m.properDivisors \ s, sdiff_subset, Int.ofNat_inj.mp ?_⟩
  push_cast
  linarith only [sum, total, rest]

private def repNat (S : Finset ℕ) (x : ℕ) : Prop :=
  ∃ s ⊆ S, ∑ d ∈ s, d = x

private def properDivsSum (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d

private lemma properDivsSum_eq_sigma_sub {n : ℕ} :
    properDivsSum n + n = sigma 1 n := by
  unfold properDivsSum
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]

private lemma layers_nat {b m q : ℕ} (hm : 0 < m) (bm : b ∣ m) (hn : ¬ q ∣ b)
    (hq : 1 < q) {i y : ℕ} (hi : repNat m.properDivisors i) (hy : repNat b.properDivisors y) :
    repNat (q * m).properDivisors (y + q * i) ∧ repNat (q * m).properDivisors (b + y + q * i) := by
  classical
  obtain ⟨s, hs, rfl⟩ := hy
  obtain ⟨t, ht, rfl⟩ := hi
  have hb : b ≠ 0 := by intro z; subst b; exact hm.ne' (by simpa using bm)
  have combine : ∀ {s' : Finset ℕ}, s' ⊆ b.divisors →
      repNat (q * m).properDivisors ((∑ d ∈ s', d) + q * ∑ d ∈ t, d) := by
    intro s' hs'
    let f (x : ℕ) := q * x
    have qpos : 0 < q := by omega
    have inj : Function.Injective f := fun x y eq => Nat.eq_of_mul_eq_mul_left qpos eq
    have subset : s' ⊆ (q * m).properDivisors := by
      intro x hx
      have d := Nat.dvd_of_mem_divisors (hs' hx)
      have dm := d.trans bm
      refine Nat.mem_properDivisors.mpr ⟨dm.trans (dvd_mul_left _ _), ?_⟩
      exact lt_of_le_of_lt (Nat.le_of_dvd hm dm) (by simpa using Nat.mul_lt_mul_of_pos_right hq hm)
    have scaled : t.image f ⊆ (q * m).properDivisors := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      obtain ⟨div, lt⟩ := Nat.mem_properDivisors.mp (ht hz)
      exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_left q div, Nat.mul_lt_mul_of_pos_left lt qpos⟩
    have separate : Disjoint s' (t.image f) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨z, _, rfl⟩ := mem_image.mp hx'
      exact hn ((dvd_mul_right q z).trans (Nat.dvd_of_mem_divisors (hs' hx)))
    refine ⟨s' ∪ t.image f, Finset.union_subset subset scaled, ?_⟩
    rw [sum_union separate, sum_image (fun _ _ _ _ eq => inj eq), Finset.mul_sum]
  constructor
  · exact combine (hs.trans Nat.properDivisors_subset_divisors)
  · have full : insert b s ⊆ b.divisors := by
      rw [← Nat.insert_self_properDivisors hb]
      exact Finset.insert_subset_insert _ hs
    have nb : b ∉ s := fun h => Nat.self_notMem_properDivisors (hs h)
    simpa [sum_insert nb, add_assoc] using combine full

private lemma certified_prime_power_gen {b q j L g : ℕ} (bpos : 1 < b) (hq : q.Prime)
    (coprime : b.Coprime q) (q3 : 3 ≤ q) (hg : 1 ≤ g) (hL : 1 ≤ L)
    (primitive : ∀ d ∈ (b * q ^ (j + 1)).properDivisors, d.Deficient)
    (high : (L : ℤ) ≤ (sigma 1 (b * q ^ (j + 1)) : ℤ) - 2 * (b * q ^ (j + 1) : ℤ))
    (large : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ properDivsSum b)
    (simple : j = 0 → 2 ≤ b - properDivsSum b)
    (middle : ∀ y : ℕ, L ≤ y → y ≤ properDivsSum b - L → repNat b.properDivisors y)
    (gap : ∀ k : ℕ, k < properDivsSum b → ∃ i : ℕ, repNat b.properDivisors i ∧ k < i + g ∧ i ≤ k) :
    (b * q ^ (j + 1)).Pseudoperfect := by
  classical
  let represented (n : ℕ) (x : ℤ) : Prop :=
    ∃ s : Finset ℕ, s ⊆ n.properDivisors ∧ (∑ d ∈ s, (d : ℤ)) = x
  have rep_of_nat : ∀ {n y : ℕ}, repNat n.properDivisors y → represented n (y : ℤ) := by
    rintro n y ⟨s, hs, rfl⟩
    exact ⟨s, hs, by simp⟩
  let properTotal (n : ℕ) : ℤ := (properDivsSum n : ℤ)
  let excess (n : ℕ) : ℤ := (sigma 1 n : ℤ) - 2 * (n : ℤ)
  have sigma_split (n : ℕ) : (sigma 1 n : ℤ) = properTotal n + (n : ℤ) := by
    have h := properDivsSum_eq_sigma_sub (n := n)
    dsimp [properTotal]; omega
  have excess_step (t : ℕ) : excess (b * q ^ (t + 1)) = (q : ℤ) * excess (b * q ^ t) + (sigma 1 b : ℤ) := by
    have recurEq : sigma 1 (b * q ^ (t + 1)) = q * sigma 1 (b * q ^ t) + sigma 1 b := by
      rw [isMultiplicative_sigma.map_mul_of_coprime (coprime.pow_right (t + 1)),
          isMultiplicative_sigma.map_mul_of_coprime (coprime.pow_right t),
          sigma_one_apply_prime_pow hq, sigma_one_apply_prime_pow hq, geom_sum_succ]
      ring
    dsimp [excess]; rw [recurEq]; push_cast; ring
  have mpos : 0 < b * q ^ (j + 1) := by have := hq.pos; positivity
  let P : ℤ := properTotal b
  let D : ℤ := (b : ℤ) - P
  have bpos0 : 0 < b := by omega
  have hqZ : (3 : ℤ) ≤ q := by exact_mod_cast q3
  have hgZ : (1 : ℤ) ≤ g := by exact_mod_cast hg
  have hLZ : (1 : ℤ) ≤ L := by exact_mod_cast hL
  have largeZ : (2 * (g : ℤ) + 1) * (2 * (L : ℤ) + 8 * (g : ℤ) + 8) ≤ P := by
    dsimp [P, properTotal]; exact_mod_cast large
  have middleZ : ∀ y : ℤ, (L : ℤ) ≤ y → y ≤ P - (L : ℤ) → represented b y := by
    intro y hy1 hy2
    lift y to ℕ using (by omega)
    exact rep_of_nat (middle y (by omega) (by dsimp [P, properTotal] at hy2; omega))
  have gapZ : ∀ k : ℤ, 0 ≤ k → k < P → ∃ i : ℤ, represented b i ∧ k - (g : ℤ) < i ∧ i ≤ k := by
    intro k hk1 hk2
    lift k to ℕ using hk1
    obtain ⟨i, hi, h1, h2⟩ := gap k (by dsimp [P, properTotal] at hk2; omega)
    exact ⟨(i : ℤ), rep_of_nat hi, by omega, by omega⟩
  have total : represented b P := rep_of_nat ⟨b.properDivisors, subset_rfl, rfl⟩
  have zero : represented b 0 := rep_of_nat ⟨∅, by simp, by simp⟩
  have unit : represented b 1 := rep_of_nat ⟨{1}, by simpa using Nat.one_mem_properDivisors_iff_one_lt.mpr bpos, by simp⟩
  have layersZ : ∀ {m' : ℕ}, 0 < m' → b ∣ m' → ∀ i y : ℤ,
      represented m' i → represented b y →
      represented (q * m') (y + (q : ℤ) * i) ∧ represented (q * m') ((b : ℤ) + y + (q : ℤ) * i) := by
    intro m' hm' bm' i y ⟨t, ht, hti⟩ ⟨s, hs, hsy⟩
    have hiN : repNat m'.properDivisors (∑ d ∈ t, d) := ⟨t, ht, rfl⟩
    have hyN : repNat b.properDivisors (∑ d ∈ s, d) := ⟨s, hs, rfl⟩
    have h := layers_nat hm' bm' (hq.coprime_iff_not_dvd.mp coprime.symm) hq.one_lt hiN hyN
    have h1 := rep_of_nat h.1
    have h2 := rep_of_nat h.2
    rw [← hti, ← hsy]
    constructor
    · convert h1 using 1; push_cast; ring
    · convert h2 using 1; push_cast; ring
  have highE : (L : ℤ) ≤ excess (b * q ^ (j + 1)) := by
    dsimp [excess]; exact high
  have repE : represented (b * q ^ (j + 1)) (excess (b * q ^ (j + 1))) := by
    by_cases hj : j = 0
    · subst j
      simp only [zero_add, pow_one] at highE primitive ⊢
      have hPb_le_b : properDivsSum b < b := by
        have hmem : b ∈ (b * q).properDivisors := Nat.mem_properDivisors.mpr
          ⟨dvd_mul_right b q, by nlinarith [hq.one_lt]⟩
        exact primitive b hmem
      have hD : 2 ≤ D := by
        have := simple rfl
        dsimp [D, P, properTotal]; omega
      have formula : excess (b * q) = 2 * P - D * ((q : ℤ) - 1) := by
        have first := excess_step 0
        simp only [pow_zero, pow_one, mul_one, zero_add] at first
        rw [first, sigma_split b]; dsimp [excess, P, D]; rw [sigma_split b]; ring
      have cases' := final_prime_alternatives hgZ hLZ hD hqZ largeZ formula highE
      have translate (i y : ℤ) (hi : represented b i) (hy : represented b y) :
          represented (b * q) (y + (q : ℤ) * i) ∧ represented (b * q) ((b : ℤ) + y + (q : ℤ) * i) := by
        simpa only [mul_comm q b] using layersZ bpos0 (dvd_refl b) i y hi hy
      rcases cases' with ⟨wide, join⟩ | ⟨wide, join, cap⟩ | basic
      · have gb := mul_nonneg (show 0 ≤ (g : ℤ) - 1 by omega) (show 0 ≤ (L : ℤ) by omega)
        have gg := mul_self_nonneg (g : ℤ)
        have pL : (L : ℤ) ≤ P := by nlinarith only [largeZ, hgZ, hLZ, gb, gg]
        have qP := mul_le_mul_of_nonneg_right hqZ (show 0 ≤ P by omega)
        have prod := mul_nonneg (show 0 ≤ D by omega) (show 0 ≤ (q : ℤ) - 1 by omega)
        exact middle_next (A := fun i => represented b i) (B := fun y => represented b y)
          (C := fun z => represented (b * q) z) (P := P) (T := P) (b := (b : ℤ))
          (by omega : (0 : ℤ) < q) (by simpa only [mul_comm (q : ℤ) (g : ℤ)] using wide)
          (by change (b : ℤ) - P + 2 * (L : ℤ) - 1 ≤ (q : ℤ) * P at join; omega)
          total gapZ middleZ (fun i hi y hy => translate i y hi hy)
          _ highE (by dsimp only [D] at formula prod; omega)
      · have eq : P + D = (b : ℤ) := by dsimp [D]; ring
        rcases four_interval_join wide join highE cap with h | h | h | h
        · simpa using (translate 0 _ zero (middleZ _ h.1 h.2)).1
        · simpa using (translate 1 _ unit (middleZ _ h.1 h.2)).1
        · rw [eq] at h; simpa using (translate 0 _ zero (middleZ _ h.1 h.2)).2
        · rw [eq] at h; convert (translate 1 _ unit (middleZ _ h.1 h.2)).2 using 1; ring
      · simpa using (translate 0 _ zero (middleZ _ basic.1 basic.2)).1
    · have earlier (k : ℕ) (hk : k < j + 1) : properTotal (b * q ^ k) < (b * q ^ k : ℤ) := by
        have mem : b * q ^ k ∈ (b * q ^ (j + 1)).properDivisors := Nat.mem_properDivisors.mpr
          ⟨Nat.mul_dvd_mul_left b (pow_dvd_pow q hk.le),
           Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hq.one_lt hk) bpos0⟩
        have defic : properDivsSum (b * q ^ k) < b * q ^ k := primitive _ mem
        dsimp [properTotal]; exact_mod_cast defic
      have earlierEx (k : ℕ) (hk : k < j + 1) : excess (b * q ^ k) < 0 := by
        dsimp [excess]; rw [sigma_split]; push_cast; linarith only [earlier k hk]
      have defBase : properTotal b < (b : ℤ) := by simpa using earlier 0 (by omega)
      have firstDef : excess (b * q) < 0 := by simpa using earlierEx 1 (by omega)
      have prevDef : excess (b * q ^ j) < 0 := earlierEx j (by omega)
      have sig : (sigma 1 b : ℤ) = 2 * P + D := by rw [sigma_split]; dsimp [P, D]; ring
      have sPos : 0 < 2 * P + D := by rw [← sig]; exact_mod_cast (sigma_pos_iff.mpr bpos0 : 0 < sigma 1 b)
      have dPos : 0 < D := by dsimp [D, P]; omega
      let E (t : ℕ) := excess (b * q ^ t)
      have recurEq (t : ℕ) : E (t + 1) = (q : ℤ) * E t + (2 * P + D) := by rw [← sig]; exact excess_step t
      have e0 : E 0 = -D := by simp only [E, pow_zero, mul_one, excess, sig]; dsimp [D]; ring
      have one : E 1 < 0 := by simpa [E] using firstDef
      obtain ⟨l, h, e⟩ := repeat_from_excess (q := (q : ℤ)) (by omega) sPos E e0 recurEq j one prevDef
        (lt_of_lt_of_le (by omega : (0 : ℤ) < L) highE)
      have alt := repeated_alternatives (P := P) (D := D) (E := E (j + 1)) hgZ hLZ dPos hqZ largeZ l h e
      have translate (i y : ℤ) (hi : represented b i) (hy : represented b y) :
          represented (b * q ^ (j + 1)) (y + (q : ℤ) * i) ∧
          represented (b * q ^ (j + 1)) ((b : ℤ) + y + (q : ℤ) * i) := by
        have divis : b ∣ b * q ^ j := dvd_mul_right _ _
        have pos : 0 < b * q ^ j := by have := hq.pos; positivity
        obtain ⟨t, sub, ht⟩ := hi
        have inclusion : represented (b * q ^ j) i := by
          refine ⟨t, fun d hd => ?_, ht⟩
          obtain ⟨dvd, lt⟩ := Nat.mem_properDivisors.mp (sub hd)
          exact Nat.mem_properDivisors.mpr ⟨dvd.trans divis, lt_of_lt_of_le lt (Nat.le_of_dvd pos divis)⟩
        have holds := layersZ pos divis i y inclusion hy
        convert holds using 2 <;> ring
      rcases alt with ⟨wide, join, cap⟩ | ⟨wide, join, cap⟩
      · exact middle_next (A := fun i => represented b i) (B := fun y => represented b y)
          (C := fun z => represented (b * q ^ (j + 1)) z) (P := P) (T := P) (b := (b : ℤ))
          (by omega : (0 : ℤ) < q) (by simpa only [mul_comm (q : ℤ) (g : ℤ)] using wide)
          (by change (b : ℤ) - P + 2 * (L : ℤ) - 1 ≤ (q : ℤ) * P at join; omega)
          total gapZ middleZ (fun i hi y hy => translate i y hi hy)
          _ highE (by change excess (b * q ^ (j + 1)) ≤ 2 * P + ((b : ℤ) - P) + (q : ℤ) * P - (L : ℤ) at cap; omega)
      · have bEq : P + D = (b : ℤ) := by dsimp [D]; ring
        rcases four_interval_join wide join highE cap with h | h | h | h
        · simpa using (translate 0 _ zero (middleZ _ h.1 h.2)).1
        · simpa using (translate 1 _ unit (middleZ _ h.1 h.2)).1
        · rw [bEq] at h; simpa using (translate 0 _ zero (middleZ _ h.1 h.2)).2
        · rw [bEq] at h; convert (translate 1 _ unit (middleZ _ h.1 h.2)).2 using 1; ring
  obtain ⟨s, hs, hsum⟩ := repE
  exact pseudoperfect_of_excess mpos hs hsum

end FinalPrime

/- ## Section 2: Core subset-sum certification and prime-power lifting -/

section CoreLift

private def inIvs (ivs : List (ℕ × ℕ)) (x : ℕ) : Prop :=
  ∃ ab ∈ ivs, ab.1 ≤ x ∧ x ≤ ab.2

private def insertIv (p : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [p]
  | q :: qs => if Nat.ble p.1 q.1 then p :: q :: qs else q :: insertIv p qs

private def sortIvs : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | p :: ps => insertIv p (sortIvs ps)

private def coalesceAcc (cur : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [cur]
  | q :: rest =>
    if Nat.ble q.1 (cur.2 + 1) then
      coalesceAcc (cur.1, if Nat.ble cur.2 q.2 then q.2 else cur.2) rest
    else cur :: coalesceAcc q rest

private def coalesceIvs : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | p :: rest => coalesceAcc p rest

private def dupShift (d : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (a, b) :: rest => (a, b) :: (a + d, b + d) :: dupShift d rest

private def stepIvs (ivs : List (ℕ × ℕ)) (d : ℕ) : List (ℕ × ℕ) :=
  coalesceIvs (sortIvs (dupShift d ivs))

private def ivsOfList (ds : List ℕ) : List (ℕ × ℕ) :=
  ds.foldl stepIvs [(0, 0)]

private lemma mem_insertIv {p q : ℕ × ℕ} {l : List (ℕ × ℕ)} :
    q ∈ insertIv p l ↔ q = p ∨ q ∈ l := by
  induction l with
  | nil => simp [insertIv]
  | cons a t ih =>
    dsimp [insertIv]; split_ifs
    · simp
    · simp [ih]; tauto

private lemma mem_sortIvs {q : ℕ × ℕ} {l : List (ℕ × ℕ)} :
    q ∈ sortIvs l ↔ q ∈ l := by
  induction l with
  | nil => simp [sortIvs]
  | cons a t ih => simp [sortIvs, mem_insertIv, ih]

private lemma inIvs_coalesceAcc :
    ∀ (cur : ℕ × ℕ) (l : List (ℕ × ℕ)) (x : ℕ),
      inIvs (coalesceAcc cur l) x → inIvs (cur :: l) x
  | cur, [], x, h => h
  | cur, q :: rest, x, h => by
    simp only [coalesceAcc] at h
    split_ifs at h with hle hmax
    · have hle' : q.1 ≤ cur.2 + 1 := (Iff.of_eq Nat.ble_eq).mp hle
      have hmax' : cur.2 ≤ q.2 := (Iff.of_eq Nat.ble_eq).mp hmax
      obtain ⟨ab, hab, h1, h2⟩ := inIvs_coalesceAcc _ rest x h
      rcases List.mem_cons.mp hab with rfl | hab'
      · by_cases hx : x ≤ cur.2
        · exact ⟨cur, List.mem_cons_self, h1, hx⟩
        · exact ⟨q, List.mem_cons_of_mem cur List.mem_cons_self, by omega, by omega⟩
      · exact ⟨ab, List.mem_cons_of_mem cur (List.mem_cons_of_mem q hab'), h1, h2⟩
    · obtain ⟨ab, hab, h1, h2⟩ := inIvs_coalesceAcc _ rest x h
      rcases List.mem_cons.mp hab with rfl | hab'
      · exact ⟨cur, List.mem_cons_self, h1, h2⟩
      · exact ⟨ab, List.mem_cons_of_mem cur (List.mem_cons_of_mem q hab'), h1, h2⟩
    · obtain ⟨ab, hab, h1, h2⟩ := h
      rcases List.mem_cons.mp hab with rfl | hab'
      · exact ⟨ab, List.mem_cons_self, h1, h2⟩
      · obtain ⟨cd, hcd, c1, c2⟩ := inIvs_coalesceAcc q rest x ⟨ab, hab', h1, h2⟩
        exact ⟨cd, List.mem_cons_of_mem cur hcd, c1, c2⟩

private lemma inIvs_coalesceIvs {l : List (ℕ × ℕ)} {x : ℕ}
    (h : inIvs (coalesceIvs l) x) : inIvs l x := by
  cases l with
  | nil => exact h
  | cons p rest => exact inIvs_coalesceAcc p rest x h

private lemma mem_dupShift {d : ℕ} {ab : ℕ × ℕ} {l : List (ℕ × ℕ)} :
    ab ∈ dupShift d l → ab ∈ l ∨ ∃ cd ∈ l, (cd.1 + d, cd.2 + d) = ab := by
  induction l with
  | nil => intro h; cases h
  | cons p rest ih =>
    intro h
    simp only [dupShift, List.mem_cons] at h
    rcases h with rfl | rfl | hrest
    · exact Or.inl List.mem_cons_self
    · exact Or.inr ⟨p, List.mem_cons_self, rfl⟩
    · rcases ih hrest with h1 | ⟨cd, hcd, rfl⟩
      · exact Or.inl (List.mem_cons_of_mem p h1)
      · exact Or.inr ⟨cd, List.mem_cons_of_mem p hcd, rfl⟩

private lemma repNat_of_inIvs_fold {S : Finset ℕ} {ds : List ℕ} {ivs : List (ℕ × ℕ)}
    (hnd : ds.Nodup) (hdisj : ∀ d ∈ ds, d ∉ S)
    (hbase : ∀ x, inIvs ivs x → repNat S x) :
    ∀ x, inIvs (ds.foldl stepIvs ivs) x → repNat (S ∪ ds.toFinset) x := by
  classical
  induction ds generalizing S ivs with
  | nil =>
    intro x hx
    simpa using hbase x hx
  | cons d rest ih =>
    rw [List.nodup_cons] at hnd
    have hdS : d ∉ S := hdisj d List.mem_cons_self
    have hstep : ∀ x, inIvs (stepIvs ivs d) x → repNat (insert d S) x := by
      intro x hx
      obtain ⟨ab, hab, h1a, h2a⟩ := inIvs_coalesceIvs hx
      rw [mem_sortIvs] at hab
      rcases mem_dupShift hab with hab' | ⟨cd, hcd, rfl⟩
      · obtain ⟨s, hs, hsum⟩ := hbase x ⟨ab, hab', h1a, h2a⟩
        exact ⟨s, hs.trans (Finset.subset_insert d S), hsum⟩
      · obtain ⟨s, hs, hsum⟩ := hbase (x - d) ⟨cd, hcd, by omega, by omega⟩
        have hds : d ∉ s := fun h => hdS (hs h)
        refine ⟨insert d s, Finset.insert_subset_insert d hs, ?_⟩
        rw [Finset.sum_insert hds, hsum]; omega
    have hdisj' : ∀ z ∈ rest, z ∉ insert d S := by
      intro z hz hmem
      rcases Finset.mem_insert.mp hmem with rfl | hzS
      · exact hnd.1 hz
      · exact hdisj z (List.mem_cons_of_mem d hz) hzS
    intro x hx
    have hres := ih hnd.2 hdisj' hstep x hx
    have hEq : insert d S ∪ rest.toFinset = S ∪ (d :: rest).toFinset := by
      ext z; simp
    rwa [← hEq]

private lemma repNat_of_inIvs {ds : List ℕ} (hnd : ds.Nodup) :
    ∀ x, inIvs (ivsOfList ds) x → repNat ds.toFinset x := by
  intro x hx
  have hbase : ∀ y, inIvs [(0, 0)] y → repNat (∅ : Finset ℕ) y := by
    rintro y ⟨ab, hab, h1, h2⟩
    simp only [List.mem_singleton] at hab
    subst hab
    exact ⟨∅, subset_rfl, by simp; omega⟩
  simpa using repNat_of_inIvs_fold hnd (fun _ _ => Finset.notMem_empty _) hbase x hx

private def checkCovB (ivs : List (ℕ × ℕ)) (lo hi : ℕ) : Bool :=
  ivs.any fun ab => Nat.ble ab.1 lo && Nat.ble hi ab.2

private lemma inIvs_of_checkCovB {ivs : List (ℕ × ℕ)} {lo hi : ℕ}
    (h : checkCovB ivs lo hi = true) : ∀ y, lo ≤ y → y ≤ hi → inIvs ivs y := by
  simp only [checkCovB, List.any_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨ab, hab, h1, h2⟩ := h
  intro y hy1 hy2
  exact ⟨ab, hab, le_trans h1 hy1, le_trans hy2 h2⟩

private def checkGapIvsB (g : ℕ) : List (ℕ × ℕ) → ℕ → Bool
  | [], _ => true
  | (a, b) :: rest, prevEnd =>
    Nat.ble a (prevEnd + g) && checkGapIvsB g rest b

private lemma gap_of_checkGapIvsB {g : ℕ} (hg : 1 ≤ g) :
    ∀ (ivs : List (ℕ × ℕ)) (prevEnd : ℕ),
      checkGapIvsB g ivs prevEnd = true →
      ∀ (S : Finset ℕ),
        (∀ x, inIvs ivs x → repNat S x) →
        repNat S prevEnd →
        ∀ k : ℕ, prevEnd ≤ k →
          (∀ ab ∈ ivs, ab.1 ≤ ab.2) →
          (∃ ab ∈ ivs, k ≤ ab.2) →
          ∃ i, repNat S i ∧ k < i + g ∧ i ≤ k
  | [], prevEnd, _, S, _, _, k, _, _, ⟨ab, hab, _⟩ => by cases hab
  | (a, b) :: rest, prevEnd, hchk, S, hrep, hprev, k, hk_lo, hwf, hbound => by
    simp only [checkGapIvsB, Bool.and_eq_true, Nat.ble_eq] at hchk
    obtain ⟨hgap, hrest⟩ := hchk
    by_cases h1 : k < a
    · exact ⟨prevEnd, hprev, by omega, hk_lo⟩
    · by_cases h2 : k ≤ b
      · exact ⟨k, hrep k ⟨(a, b), List.mem_cons_self, by omega, h2⟩, by omega, le_rfl⟩
      · have hb_rep : repNat S b :=
          hrep b ⟨(a, b), List.mem_cons_self, (hwf (a, b) List.mem_cons_self), le_rfl⟩
        have hbound' : ∃ ab ∈ rest, k ≤ ab.2 := by
          obtain ⟨ab, hab, hkab⟩ := hbound
          rcases List.mem_cons.mp hab with rfl | hab'
          · omega
          · exact ⟨ab, hab', hkab⟩
        exact gap_of_checkGapIvsB hg rest b hrest S
          (fun x ⟨ab, hab, x1, x2⟩ => hrep x ⟨ab, List.mem_cons_of_mem _ hab, x1, x2⟩)
          hb_rep k (by omega)
          (fun ab hab => hwf ab (List.mem_cons_of_mem _ hab)) hbound'

private def inIvsB (ivs : List (ℕ × ℕ)) (x : ℕ) : Bool :=
  ivs.any fun ab => Nat.ble ab.1 x && Nat.ble x ab.2

private lemma inIvs_of_inIvsB {ivs : List (ℕ × ℕ)} {x : ℕ} (h : inIvsB ivs x = true) :
    inIvs ivs x := by
  simp only [inIvsB, List.any_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨ab, hab, h1, h2⟩ := h
  exact ⟨ab, hab, h1, h2⟩

private def checkModB (ivs : List (ℕ × ℕ)) (step : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 =>
    (if Nat.beq ((k + 1) % step) 0 then inIvsB ivs (k + 1) else true) && checkModB ivs step k

private lemma mod_of_checkModB {ivs : List (ℕ × ℕ)} {step : ℕ} :
    ∀ lim : ℕ, checkModB ivs step lim = true →
      ∀ x : ℕ, 0 < x → x ≤ lim → x % step = 0 → inIvs ivs x
  | 0, _, x, hx, hle, _ => by omega
  | lim + 1, h, x, hx, hle, hmod => by
    simp only [checkModB, Bool.and_eq_true] at h
    by_cases heq : x = lim + 1
    · subst heq
      have hbeq : Nat.beq ((lim + 1) % step) 0 = true := (Iff.of_eq Nat.beq_eq).mpr hmod
      rw [hbeq] at h
      exact inIvs_of_inIvsB h.1
    · exact mod_of_checkModB lim h.2 x hx (by omega) hmod

private lemma repNat_insert_interval {S : Finset ℕ} {L H x : ℕ}
    (hx : x ∉ S) (hcov : ∀ y, L ≤ y → y ≤ H → repNat S y) (hstep : L + x ≤ H + 1) :
    ∀ y, L ≤ y → y ≤ H + x → repNat (insert x S) y := by
  intro y hy1 hy2
  by_cases h1 : y ≤ H
  · obtain ⟨s, hs, hsum⟩ := hcov y hy1 h1
    exact ⟨s, hs.trans (Finset.subset_insert x S), hsum⟩
  · obtain ⟨s, hs, hsum⟩ := hcov (y - x) (by omega) (by omega)
    have hxs : x ∉ s := fun h => hx (hs h)
    refine ⟨insert x s, Finset.insert_subset_insert x hs, ?_⟩
    rw [Finset.sum_insert hxs, hsum]; omega

private lemma repNat_insert_list {S : Finset ℕ} {L H : ℕ} {l : List ℕ}
    (hnd : l.Nodup) (hdisj : ∀ z ∈ l, z ∉ S)
    (hcov : ∀ y, L ≤ y → y ≤ H → repNat S y)
    (hsteps : ∀ (pre : List ℕ) (z : ℕ) (suf : List ℕ),
      l = pre ++ z :: suf → L + z ≤ H + pre.sum + 1) :
    ∀ y, L ≤ y → y ≤ H + l.sum → repNat (S ∪ l.toFinset) y := by
  classical
  induction l generalizing S H with
  | nil =>
    intro y hy1 hy2
    simpa using hcov y hy1 (by simpa using hy2)
  | cons x rest ih =>
    rw [List.nodup_cons] at hnd
    have hxS : x ∉ S := hdisj x List.mem_cons_self
    have hstep0 : L + x ≤ H + 1 := by
      have := hsteps [] x rest rfl
      simpa using this
    have hcov1 := repNat_insert_interval hxS hcov hstep0
    have hdisj' : ∀ z ∈ rest, z ∉ insert x S := by
      intro z hz hmem
      rcases Finset.mem_insert.mp hmem with rfl | hzS
      · exact hnd.1 hz
      · exact hdisj z (List.mem_cons_of_mem x hz) hzS
    have hsteps' : ∀ (pre : List ℕ) (z : ℕ) (suf : List ℕ),
        rest = pre ++ z :: suf → L + z ≤ (H + x) + pre.sum + 1 := by
      intro pre z suf heq
      have := hsteps (x :: pre) z suf (by simp [heq])
      simp only [List.sum_cons] at this
      omega
    have hres := ih hnd.2 hdisj' hcov1 hsteps'
    intro y hy1 hy2
    have hEq : S ∪ (x :: rest).toFinset = insert x S ∪ rest.toFinset := by
      ext z; simp
    rw [hEq]
    exact hres y hy1 (by simp only [List.sum_cons] at hy2; omega)

private lemma repNat_union_gap {S T : Finset ℕ} {L g : ℕ} (hg : 1 ≤ g) (hST : S ⊆ T)
    (hLS : L ≤ ∑ d ∈ S, d)
    (hcovT : ∀ y, L ≤ y → y ≤ (∑ d ∈ T, d) - L → repNat T y)
    (hgapS : ∀ k, k < ∑ d ∈ S, d → ∃ i, repNat S i ∧ k < i + g ∧ i ≤ k) :
    ∀ k, k < ∑ d ∈ T, d → ∃ i, repNat T i ∧ k < i + g ∧ i ≤ k := by
  classical
  have hsumT : ∑ d ∈ T, d = (∑ d ∈ S, d) + ∑ d ∈ T \ S, d := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hST]
  intro k hk
  by_cases h1 : k < L
  · obtain ⟨i, ⟨s, hs, hsum⟩, hi1, hi2⟩ := hgapS k (lt_of_lt_of_le h1 hLS)
    exact ⟨i, ⟨s, hs.trans hST, hsum⟩, hi1, hi2⟩
  · by_cases h2 : k ≤ (∑ d ∈ T, d) - L
    · exact ⟨k, hcovT k (by omega) h2, by omega, le_rfl⟩
    · let Δ := ∑ d ∈ T \ S, d
      have hkS : k - Δ < ∑ d ∈ S, d := by omega
      obtain ⟨j, ⟨s, hs, hsum⟩, hj1, hj2⟩ := hgapS (k - Δ) hkS
      have hdisj : Disjoint s (T \ S) :=
        Finset.disjoint_of_subset_left hs Finset.disjoint_sdiff
      refine ⟨j + Δ, ⟨s ∪ (T \ S), Finset.union_subset (hs.trans hST) Finset.sdiff_subset, ?_⟩, ?_, ?_⟩
      · rw [Finset.sum_union hdisj, hsum]
      · omega
      · omega

private def HasRelGap (u a_num a_den : ℕ) : Prop :=
  ∀ d ∈ u.properDivisors,
    a_den * d ≤ a_num * u + a_den * ∑ e ∈ u.properDivisors.filter (· < d), e

private lemma HasRelGap.mul_prime {u p a_num a_den : ℕ} (hp : p.Prime) (hu : 0 < u)
    (hrel : HasRelGap u a_num a_den)
    (hdef : a_den * u ≤ a_num * (p * u) + a_den * ∑ e ∈ u.properDivisors, e) :
    HasRelGap (p * u) a_num a_den := by
  intro d hd
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
  by_cases hdu : d ∣ u
  · by_cases heq : d = u
    · subst d
      have hsub : u.properDivisors ⊆ (p * u).properDivisors.filter (· < u) := by
        intro e he
        obtain ⟨hed, hel⟩ := Nat.mem_properDivisors.mp he
        exact Finset.mem_filter.mpr ⟨Nat.mem_properDivisors.mpr
          ⟨hed.trans (dvd_mul_left u p), lt_trans hel (by nlinarith [hp.one_lt])⟩, hel⟩
      have hle := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
      calc a_den * u ≤ a_num * (p * u) + a_den * ∑ e ∈ u.properDivisors, e := hdef
        _ ≤ a_num * (p * u) + a_den * ∑ e ∈ (p * u).properDivisors.filter (· < u), e := by gcongr
    · have hdmem : d ∈ u.properDivisors :=
        Nat.mem_properDivisors.mpr ⟨hdu, lt_of_le_of_ne (Nat.le_of_dvd hu hdu) heq⟩
      have h1 := hrel d hdmem
      have hsub : u.properDivisors.filter (· < d) ⊆ (p * u).properDivisors.filter (· < d) := by
        intro e he
        rw [Finset.mem_filter] at he ⊢
        obtain ⟨hed, hel⟩ := Nat.mem_properDivisors.mp he.1
        exact ⟨Nat.mem_properDivisors.mpr
          ⟨hed.trans (dvd_mul_left u p), lt_trans hel (by nlinarith [hp.one_lt])⟩, he.2⟩
      have hle := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
      have hup : a_num * u ≤ a_num * (p * u) := Nat.mul_le_mul_left a_num (Nat.le_mul_of_pos_left u hp.pos)
      calc a_den * d ≤ a_num * u + a_den * ∑ e ∈ u.properDivisors.filter (· < d), e := h1
        _ ≤ a_num * (p * u) + a_den * ∑ e ∈ (p * u).properDivisors.filter (· < d), e :=
            Nat.add_le_add hup (Nat.mul_le_mul_left a_den hle)
  · have hpd : p ∣ d := by
      by_contra hnp
      exact hdu ((hp.coprime_iff_not_dvd.mpr hnp).symm.dvd_of_dvd_mul_left hdvd)
    obtain ⟨d', rfl⟩ := hpd
    have hd'dvd : d' ∣ u := (Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd
    have hd'lt : d' < u := lt_of_mul_lt_mul_left hlt (Nat.zero_le p)
    have hd'mem : d' ∈ u.properDivisors := Nat.mem_properDivisors.mpr ⟨hd'dvd, hd'lt⟩
    have h1 := hrel d' hd'mem
    have hmul : a_den * (p * d') ≤ a_num * (p * u) +
        a_den * (p * ∑ e ∈ u.properDivisors.filter (· < d'), e) := by
      calc a_den * (p * d') = p * (a_den * d') := by ring
        _ ≤ p * (a_num * u + a_den * ∑ e ∈ u.properDivisors.filter (· < d'), e) := Nat.mul_le_mul_left p h1
        _ = a_num * (p * u) + a_den * (p * ∑ e ∈ u.properDivisors.filter (· < d'), e) := by ring
    have hsub : (u.properDivisors.filter (· < d')).image (p * ·) ⊆
        (p * u).properDivisors.filter (· < p * d') := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter] at he ⊢
      obtain ⟨hed, helt⟩ := Nat.mem_properDivisors.mp he.1
      exact ⟨Nat.mem_properDivisors.mpr
        ⟨Nat.mul_dvd_mul_left p hed, Nat.mul_lt_mul_of_pos_left helt hp.pos⟩,
        Nat.mul_lt_mul_of_pos_left he.2 hp.pos⟩
    have hsum_im : ∑ x ∈ (u.properDivisors.filter (· < d')).image (p * ·), x =
        p * ∑ e ∈ u.properDivisors.filter (· < d'), e := by
      rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h), Finset.mul_sum]
    have hle := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
    rw [hsum_im] at hle
    exact le_trans hmul (Nat.add_le_add_left (Nat.mul_le_mul_left a_den hle) _)

private lemma properDivsSum_ratio_mono {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) :
    properDivsSum a * b ≤ properDivsSum b * a := by
  have hle : a.abundancyIndex ≤ b.abundancyIndex := Nat.abundancyIndex_le_of_dvd hb.ne' hab
  rw [Nat.abundancyIndex, Nat.abundancyIndex,
      div_le_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hb)] at hle
  have h1 : (∑ d ∈ a.divisors, d) * b ≤ (∑ d ∈ b.divisors, d) * a := by exact_mod_cast hle
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, Nat.sum_divisors_eq_sum_properDivisors_add_self] at h1
  change (properDivsSum a + a) * b ≤ (properDivsSum b + b) * a at h1
  nlinarith

private lemma sub_mul_le_sub_mul_of_mul_le {P0 P1 B0 B1 M : ℕ}
    (h1 : M ≤ P0) (h2 : M ≤ P1) (hB : B0 ≤ B1) (hm : P0 * B1 ≤ P1 * B0) :
    (P0 - M) * B1 ≤ (P1 - M) * B0 := by
  zify [h1, h2] at hm ⊢
  nlinarith

private lemma toFinset_eq_properDivisors_of_sum {u : ℕ} {ds : List ℕ} (hu : 0 < u)
    (hnd : ds.Nodup) (hsub : ∀ d ∈ ds, d ∣ u ∧ d < u)
    (hsum : ds.sum = properDivsSum u) :
    ds.toFinset = u.properDivisors := by
  have hss : ds.toFinset ⊆ u.properDivisors := fun d hd =>
    Nat.mem_properDivisors.mpr (hsub d (List.mem_toFinset.mp hd))
  by_contra hne
  have hps : ds.toFinset ⊂ u.properDivisors := Finset.ssubset_iff_subset_ne.mpr ⟨hss, hne⟩
  obtain ⟨x, hx1, hx2⟩ := Finset.exists_of_ssubset hps
  have hxpos : 0 < x := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hx1).1 hu
  have hsum_eq : ∑ d ∈ ds.toFinset, d = ds.sum := by
    calc ∑ d ∈ ds.toFinset, d = (ds.map id).sum := List.sum_toFinset id hnd
      _ = ds.sum := by simp
  have hlt : ∑ d ∈ ds.toFinset, d < ∑ d ∈ u.properDivisors, d := by
    have hsplit := Finset.sum_sdiff hss (f := id)
    have hge : x ≤ ∑ d ∈ u.properDivisors \ ds.toFinset, d :=
      Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Finset.mem_sdiff.mpr ⟨hx1, hx2⟩)
    change (∑ d ∈ u.properDivisors \ ds.toFinset, d) + ∑ d ∈ ds.toFinset, d = properDivsSum u at hsplit
    omega
  change ∑ d ∈ ds.toFinset, d < properDivsSum u at hlt
  omega

private def checkSortedRelGapB (u a_num a_den : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | d :: rest, acc =>
    Nat.ble (a_den * d) (a_num * u + a_den * acc) &&
    (match rest with
     | [] => true
     | d' :: _ => Nat.ble (d + 1) d') &&
    checkSortedRelGapB u a_num a_den rest (acc + d)

private lemma checkSortedRelGapB_strict :
    ∀ (u a_num a_den : ℕ) (ds : List ℕ) (acc : ℕ),
      checkSortedRelGapB u a_num a_den ds acc = true → ds.Pairwise (· < ·)
  | _, _, _, [], _, _ => List.Pairwise.nil
  | u, a_num, a_den, d :: rest, acc, h => by
    simp only [checkSortedRelGapB, Bool.and_eq_true] at h
    have htail := checkSortedRelGapB_strict u a_num a_den rest (acc + d) h.2
    refine List.Pairwise.cons ?_ htail
    cases rest with
    | nil => intro _ hm; cases hm
    | cons d' rest' =>
      have hdd' : d < d' := by
        have := (Iff.of_eq Nat.ble_eq).mp h.1.2
        omega
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hdd'
      · exact lt_trans hdd' ((List.pairwise_cons.mp htail).1 y hy')

private lemma checkSortedRelGapB_bound :
    ∀ (u a_num a_den : ℕ) (ds : List ℕ) (pre : List ℕ) (d : ℕ) (suf : List ℕ),
      ds = pre ++ d :: suf →
      checkSortedRelGapB u a_num a_den ds 0 = true →
      a_den * d ≤ a_num * u + a_den * pre.sum := by
  have aux : ∀ (u a_num a_den : ℕ) (ds : List ℕ) (acc : ℕ) (pre : List ℕ) (d : ℕ) (suf : List ℕ),
      ds = pre ++ d :: suf →
      checkSortedRelGapB u a_num a_den ds acc = true →
      a_den * d ≤ a_num * u + a_den * (acc + pre.sum) := by
    intro u a_num a_den ds
    induction ds with
    | nil =>
      intro acc pre d suf heq
      cases pre <;> simp at heq
    | cons x xs ih =>
      intro acc pre d suf heq hchk
      simp only [checkSortedRelGapB, Bool.and_eq_true] at hchk
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        simpa using (Iff.of_eq Nat.ble_eq).mp hchk.1.1
      | cons y ys =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        have := ih (acc + x) ys d suf rfl hchk.2
        simpa [List.sum_cons, add_assoc] using this
  intro u a_num a_den ds pre d suf heq hchk
  simpa using aux u a_num a_den ds 0 pre d suf heq hchk

private lemma hasRelGap_of_sorted_list {u a_num a_den : ℕ} {ds : List ℕ}
    (heq : ds.toFinset = u.properDivisors)
    (hchk : checkSortedRelGapB u a_num a_den ds 0 = true) :
    HasRelGap u a_num a_den := by
  have hpw : ds.Pairwise (· < ·) := checkSortedRelGapB_strict u a_num a_den ds 0 hchk
  intro d hd
  have hmem : d ∈ ds := List.mem_toFinset.mp (heq ▸ hd)
  obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hmem
  have hbd := checkSortedRelGapB_bound u a_num a_den (pre ++ d :: suf) pre d suf rfl hchk
  have hpw_split := List.pairwise_append.mp hpw
  have hpre_nd : pre.Nodup := hpw_split.1.imp (fun h => ne_of_lt h)
  have hpre_lt : ∀ x ∈ pre, x < d := fun x hx => hpw_split.2.2 x hx d List.mem_cons_self
  have hsub : pre.toFinset ⊆ u.properDivisors.filter (· < d) := by
    intro x hx
    have hxpre := List.mem_toFinset.mp hx
    refine Finset.mem_filter.mpr ⟨?_, hpre_lt x hxpre⟩
    rw [← heq]
    exact List.mem_toFinset.mpr (List.mem_append_left _ hxpre)
  have hsum_pre : ∑ e ∈ pre.toFinset, e = pre.sum := by
    calc ∑ e ∈ pre.toFinset, e = (pre.map id).sum := List.sum_toFinset id hpre_nd
      _ = pre.sum := by simp
  have hle := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
  rw [hsum_pre] at hle
  exact le_trans hbd (Nat.add_le_add_left (Nat.mul_le_mul_left a_den hle) _)

private lemma lift_dividing_prime_step {B0 P0 B u s k L g : ℕ}
    (hs : s.Prime) (hu : 0 < u) (hcop : ¬ s ∣ u) (hk : 1 ≤ k) (hB : B = s ^ k * u)
    (hB0 : 0 < B0) (hg : 1 ≤ g) (h2L_B : 2 * L ≤ properDivsSum B)
    (hcovB : ∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y)
    (hgapB : ∀ j, j < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ j < i + g ∧ i ≤ j)
    (hPratio : (P0 - 2 * L) * B ≤ (properDivsSum B - 2 * L) * B0)
    (hrel : HasRelGap u (P0 - 2 * L) (s * B0))
    (hfin : B0 * u ≤ (P0 - 2 * L) * u + s * B0 * properDivsSum u) :
    (∀ y, L ≤ y → y ≤ properDivsSum (s * B) - L → repNat (s * B).properDivisors y) ∧
    (∀ j, j < properDivsSum (s * B) → ∃ i, repNat (s * B).properDivisors i ∧ j < i + g ∧ i ≤ j) := by
  classical
  have hBpos : 0 < B := by rw [hB]; have := hs.pos; positivity
  have hsk_pos : 0 < s ^ (k + 1) := pow_pos hs.pos _
  have hsB_eq : s * B = s ^ (k + 1) * u := by rw [hB, pow_succ']; ring
  -- Fresh proper divisors of s*B outside B.properDivisors are {B} ∪ (s^(k+1) * u.properDivisors)
  let freshP := (u.properDivisors.sort (· ≤ ·)).map (fun d => s ^ (k + 1) * d)
  let fresh := freshP ++ [B]
  have hsort_nd : (u.properDivisors.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have hsort_mem : ∀ d, d ∈ u.properDivisors.sort (· ≤ ·) ↔ d ∈ u.properDivisors :=
    fun d => Finset.mem_sort (· ≤ ·)
  have hmul_inj : Function.Injective (fun d : ℕ => s ^ (k + 1) * d) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hsk_pos h
  have hfreshP_nd : freshP.Nodup := hsort_nd.map hmul_inj
  have hB_not_freshP : B ∉ freshP := by
    intro hm
    obtain ⟨d, hd, hEq⟩ := List.mem_map.mp hm
    have hdlt : d < u := (Nat.mem_properDivisors.mp ((hsort_mem d).mp hd)).2
    have h1 : s ^ (k + 1) * d = s ^ k * u := hEq.trans hB
    have h2 : s ∣ u := by
      have : s ^ k * (s * d) = s ^ k * u := by rw [← h1, pow_succ]; ring
      exact ⟨d, (Nat.eq_of_mul_eq_mul_left (pow_pos hs.pos k) this).symm⟩
    exact hcop h2
  have hfresh_nd : fresh.Nodup := by
    rw [List.nodup_append]
    refine ⟨hfreshP_nd, List.nodup_singleton B, ?_⟩
    intro x hx y hy heq
    rw [List.mem_singleton] at hy; subst hy; subst heq
    exact hB_not_freshP hx
  have hfresh_disj : ∀ z ∈ fresh, z ∉ B.properDivisors := by
    intro z hz hmem
    rcases List.mem_append.mp hz with hz1 | hz2
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hz1
      have hdvd : s ^ (k + 1) ∣ s ^ k * u := (dvd_mul_right _ d).trans (hB ▸ (Nat.mem_properDivisors.mp hmem).1)
      have hsd : s ∣ u := by
        rw [pow_succ] at hdvd
        exact (Nat.mul_dvd_mul_iff_left (pow_pos hs.pos k)).mp hdvd
      exact hcop hsd
    · rw [List.mem_singleton] at hz2; subst hz2
      exact Nat.self_notMem_properDivisors hmem
  have hunion_eq : B.properDivisors ∪ fresh.toFinset = (s * B).properDivisors := by
    ext z
    simp only [Finset.mem_union, List.mem_toFinset, fresh, List.mem_append, List.mem_singleton,
      freshP, List.mem_map, hsort_mem]
    constructor
    · rintro (hz | ⟨d, hd, rfl⟩ | hEq)
      · obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp hz
        exact Nat.mem_properDivisors.mpr ⟨hd1.trans (dvd_mul_left B s),
          lt_trans hd2 (by nlinarith [hs.one_lt])⟩
      · obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp hd
        rw [hsB_eq]
        exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_left _ hd1,
          Nat.mul_lt_mul_of_pos_left hd2 hsk_pos⟩
      · rw [hEq]
        exact Nat.mem_properDivisors.mpr ⟨dvd_mul_left B s, by nlinarith [hs.one_lt]⟩
    · intro hz
      obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp hz
      by_cases hzB : z ∣ B
      · by_cases heq : z = B
        · exact Or.inr (Or.inr heq)
        · exact Or.inl (Nat.mem_properDivisors.mpr ⟨hzB, lt_of_le_of_ne (Nat.le_of_dvd hBpos hzB) heq⟩)
      · right; left
        have hcop_sk : Nat.Coprime (s ^ (k + 1)) u := (hs.coprime_iff_not_dvd.mpr hcop).pow_left _
        have hz_ne : z ≠ 0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hd1 (mul_pos hs.pos hBpos))
        rw [hsB_eq] at hd1 hd2
        have hsk_z : s ^ (k + 1) ∣ z := by
          have hvs : k + 1 ≤ z.factorization s := by
            by_contra hlt
            have hle : z.factorization s ≤ k := by omega
            have hzdvd_B : z ∣ s ^ k * u := by
              rw [← Nat.factorization_le_iff_dvd hz_ne (mul_ne_zero (pow_ne_zero k hs.ne_zero) hu.ne')]
              intro q
              by_cases hqs : q = s
              · subst q
                rw [Nat.factorization_mul (pow_ne_zero k hs.ne_zero) hu.ne', Finsupp.add_apply,
                    hs.factorization_pow, Finsupp.single_eq_same]
                omega
              · have hle_all := (Nat.factorization_le_iff_dvd hz_ne (mul_ne_zero (pow_ne_zero (k + 1) hs.ne_zero) hu.ne')).mpr hd1 q
                rw [Nat.factorization_mul (pow_ne_zero (k + 1) hs.ne_zero) hu.ne', Finsupp.add_apply,
                    hs.factorization_pow, Finsupp.single_eq_of_ne hqs, zero_add] at hle_all
                rw [Nat.factorization_mul (pow_ne_zero k hs.ne_zero) hu.ne', Finsupp.add_apply,
                    hs.factorization_pow, Finsupp.single_eq_of_ne hqs, zero_add]
                exact hle_all
            exact hzB (hB.symm ▸ hzdvd_B)
          exact (hs.pow_dvd_iff_le_factorization hz_ne).mpr hvs
        obtain ⟨d, rfl⟩ := hsk_z
        refine ⟨d, Nat.mem_properDivisors.mpr ⟨(Nat.mul_dvd_mul_iff_left hsk_pos).mp hd1,
          lt_of_mul_lt_mul_left hd2 (Nat.zero_le _)⟩, rfl⟩
  have hfreshP_sum : freshP.sum = s ^ (k + 1) * properDivsSum u := by
    dsimp [freshP]
    rw [List.sum_map_mul_left]
    congr 1
    simp only [List.map_id']
    have h1 := List.sum_toFinset (f := id) hsort_nd
    simp only [List.map_id, id_eq] at h1
    rw [← h1]
    congr 1; ext d; simp
  have hsteps : ∀ (pre : List ℕ) (z : ℕ) (suf : List ℕ),
      fresh = pre ++ z :: suf → L + z ≤ (properDivsSum B - L) + pre.sum + 1 := by
    intro pre z suf heq
    have h1 : freshP.length ≤ pre.length ∨ pre.length < freshP.length := le_or_gt _ _
    rcases h1 with hge | hlt
    · -- z must be B, pre = freshP!
      have hlen_eq : fresh.length = freshP.length + 1 := by simp [fresh]
      have hpre_eq : pre.length = freshP.length := by
        have := congrArg List.length heq
        simp only [List.length_append, List.length_cons, hlen_eq] at this
        omega
      have hpre_eq' : pre = freshP ∧ [B] = z :: suf := by
        have := List.append_inj heq hpre_eq.symm
        exact ⟨this.1.symm, this.2⟩
      have hzB : z = B := by injection hpre_eq'.2 with h; exact h.symm
      rw [hzB, hpre_eq'.1, hfreshP_sum]
      -- Need B <= (properDivsSum B - 2*L) + s^(k+1) * properDivsSum u + 1
      have hmul : B0 * B ≤ (properDivsSum B - 2 * L) * B0 + B0 * (s ^ (k + 1) * properDivsSum u) := by
        calc B0 * B = s ^ k * (B0 * u) := by rw [hB]; ring
          _ ≤ s ^ k * ((P0 - 2 * L) * u + s * B0 * properDivsSum u) := Nat.mul_le_mul_left _ hfin
          _ = (P0 - 2 * L) * B + B0 * (s ^ (k + 1) * properDivsSum u) := by rw [hB, pow_succ]; ring
          _ ≤ (properDivsSum B - 2 * L) * B0 + B0 * (s ^ (k + 1) * properDivsSum u) :=
              Nat.add_le_add_right hPratio _
      have hB_le : B ≤ (properDivsSum B - 2 * L) + s ^ (k + 1) * properDivsSum u := by
        apply Nat.le_of_mul_le_mul_left _ hB0
        linarith
      omega
    · -- z is in freshP!
      have hpre_take : pre = freshP.take pre.length := by
        have h2 := congrArg (List.take pre.length) heq
        rw [List.take_append_of_le_length hlt.le, List.take_left] at h2
        exact h2.symm
      have hz_get : z = freshP[pre.length] := by
        have h2 := congrArg (fun l => l[pre.length]?) heq
        rw [List.getElem?_append_left hlt, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero] at h2
        rw [List.getElem?_eq_getElem hlt] at h2
        exact (Option.some.inj h2).symm
      let sd := u.properDivisors.sort (· ≤ ·)
      have hlt_sd : pre.length < sd.length := by simpa [freshP, sd] using hlt
      let d := sd[pre.length]
      have hz_eq : z = s ^ (k + 1) * d := by
        rw [hz_get]; simp [freshP, sd, d]
      have hd_mem : d ∈ u.properDivisors := (hsort_mem d).mp (List.getElem_mem hlt_sd)
      have hpre_sum : pre.sum = s ^ (k + 1) * (sd.take pre.length).sum := by
        calc pre.sum = (freshP.take pre.length).sum := congrArg List.sum hpre_take
          _ = ((sd.take pre.length).map (fun d => s ^ (k + 1) * d)).sum := by
              simp only [freshP, sd, List.map_take]
          _ = s ^ (k + 1) * (sd.take pre.length).sum := by
              rw [List.sum_map_mul_left]; simp only [List.map_id']
      have hfilt_eq : (sd.take pre.length).sum = ∑ e ∈ u.properDivisors.filter (· < d), e := by
        -- Cleanly prove (sd.take m).toFinset = u.properDivisors.filter (< d)!
        have hpw_lt : sd.Pairwise (· < ·) :=
          ((Finset.pairwise_sort u.properDivisors (· ≤ ·)).and hsort_nd).imp
            (fun h => lt_of_le_of_ne h.1 h.2)
        have hsplit_sd : sd = sd.take pre.length ++ d :: sd.drop (pre.length + 1) := by
          have h1 := (List.take_append_drop pre.length sd).symm
          have h2 : sd.drop pre.length = d :: sd.drop (pre.length + 1) :=
            List.drop_eq_getElem_cons hlt_sd
          rw [h2] at h1; exact h1
        have htake_nd : (sd.take pre.length).Nodup := hsort_nd.take
        have htofin : (sd.take pre.length).toFinset = u.properDivisors.filter (· < d) := by
          ext e
          simp only [List.mem_toFinset, Finset.mem_filter, ← hsort_mem]
          constructor
          · intro he
            have h1 : e ∈ sd := List.mem_of_mem_take he
            have h2 : e < d := by
              rw [hsplit_sd, List.pairwise_append] at hpw_lt
              exact hpw_lt.2.2 e he d List.mem_cons_self
            exact ⟨h1, h2⟩
          · rintro ⟨he, helt⟩
            change e ∈ sd at he
            rw [hsplit_sd, List.mem_append, List.mem_cons] at he
            rcases he with h | rfl | h
            · exact h
            · omega
            · rw [hsplit_sd, List.pairwise_append] at hpw_lt
              have hd_lt_e := (List.pairwise_cons.mp hpw_lt.2.1).1 e h
              omega
        rw [← htofin]
        calc (sd.take pre.length).sum = ((sd.take pre.length).map id).sum := by simp
          _ = ∑ e ∈ (sd.take pre.length).toFinset, e := (List.sum_toFinset id htake_nd).symm
      rw [hz_eq, hpre_sum, hfilt_eq]
      have hrel_d := hrel d hd_mem
      -- s*B0 * d <= (P0 - 2*L)*u + s*B0 * sum_(e < d) e
      -- Multiply by s^k: B0 * (s^(k+1) * d) <= (P0 - 2*L)*B + B0 * (s^(k+1) * sum_(e < d) e)
      have hmul : B0 * (s ^ (k + 1) * d) ≤ (properDivsSum B - 2 * L) * B0 +
          B0 * (s ^ (k + 1) * ∑ e ∈ u.properDivisors.filter (· < d), e) := by
        calc B0 * (s ^ (k + 1) * d) = s ^ k * (s * B0 * d) := by rw [pow_succ]; ring
          _ ≤ s ^ k * ((P0 - 2 * L) * u + s * B0 * ∑ e ∈ u.properDivisors.filter (· < d), e) :=
              Nat.mul_le_mul_left _ hrel_d
          _ = (P0 - 2 * L) * B + B0 * (s ^ (k + 1) * ∑ e ∈ u.properDivisors.filter (· < d), e) := by
              rw [hB, pow_succ]; ring
          _ ≤ (properDivsSum B - 2 * L) * B0 +
              B0 * (s ^ (k + 1) * ∑ e ∈ u.properDivisors.filter (· < d), e) :=
              Nat.add_le_add_right hPratio _
      have hle : s ^ (k + 1) * d ≤ (properDivsSum B - 2 * L) +
          s ^ (k + 1) * ∑ e ∈ u.properDivisors.filter (· < d), e := by
        apply Nat.le_of_mul_le_mul_left _ hB0
        linarith
      omega
  have hcov_new : ∀ y, L ≤ y → y ≤ properDivsSum (s * B) - L → repNat (s * B).properDivisors y := by
    have hsum_all : (properDivsSum B) + fresh.sum = properDivsSum (s * B) := by
      have hdisj_fin : Disjoint B.properDivisors fresh.toFinset := by
        rw [Finset.disjoint_right]
        intro z hz; exact hfresh_disj z (List.mem_toFinset.mp hz)
      have h1 := Finset.sum_union hdisj_fin (f := id)
      rw [hunion_eq] at h1
      have h2 : ∑ d ∈ fresh.toFinset, d = fresh.sum := by
        calc ∑ d ∈ fresh.toFinset, d = (fresh.map id).sum := List.sum_toFinset id hfresh_nd
          _ = fresh.sum := by simp
      change properDivsSum (s * B) = properDivsSum B + ∑ d ∈ fresh.toFinset, d at h1
      omega
    have hcov_u := repNat_insert_list hfresh_nd hfresh_disj hcovB hsteps
    rw [hunion_eq] at hcov_u
    intro y hy1 hy2
    exact hcov_u y hy1 (by omega)
  have hsub_divs : B.properDivisors ⊆ (s * B).properDivisors := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp hd
    exact Nat.mem_properDivisors.mpr ⟨hd1.trans (dvd_mul_left B s),
      lt_trans hd2 (by nlinarith [hs.one_lt])⟩
  have hgap_new := repNat_union_gap hg hsub_divs (by change L ≤ properDivsSum B; omega) hcov_new hgapB
  exact ⟨hcov_new, hgap_new⟩

private lemma lift_coprime_prime_pow {B p L g : ℕ}
    (hBpos : 0 < B) (hp : p.Prime) (hcop : B.Coprime p) (hg : 1 ≤ g)
    (hL_le : 2 * L ≤ properDivsSum B)
    (hwide : p * g ≤ properDivsSum B - 2 * L + 1)
    (hoverlap : B + 2 * L ≤ properDivsSum B + p * properDivsSum B + 1)
    (hcovB : ∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y)
    (hgapB : ∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + g ∧ i ≤ k) :
    ∀ d : ℕ, 1 ≤ d →
      (∀ y, L ≤ y → y ≤ properDivsSum (B * p ^ d) - L → repNat (B * p ^ d).properDivisors y) ∧
      (∀ k, k < properDivsSum (B * p ^ d) → ∃ i, repNat (B * p ^ d).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
  have step : ∀ t : ℕ,
      (∀ y, L ≤ y → y ≤ properDivsSum (B * p ^ t) - L → repNat (B * p ^ t).properDivisors y) ∧
      (∀ k, k < properDivsSum (B * p ^ t) → ∃ i, repNat (B * p ^ t).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
    intro t
    induction t with
    | zero => simpa using ⟨hcovB, hgapB⟩
    | succ t ih =>
      obtain ⟨hcov_t, hgap_t⟩ := ih
      let m := B * p ^ t
      have hmpos : 0 < m := by have := hp.pos; positivity
      have hP_ge : properDivsSum B ≤ properDivsSum m := by
        apply Finset.sum_le_sum_of_subset
        intro d hd
        obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp hd
        have hle : B ≤ m := Nat.le_mul_of_pos_right B (pow_pos hp.pos t)
        exact Nat.mem_properDivisors.mpr ⟨hd1.trans (dvd_mul_right B _), lt_of_lt_of_le hd2 hle⟩
      have hP_next : properDivsSum (B * p ^ (t + 1)) = B + properDivsSum B + p * properDivsSum m := by
        have h1 : sigma 1 (B * p ^ (t + 1)) = p * sigma 1 m + sigma 1 B := by
          dsimp [m]
          rw [isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right (t + 1)),
              isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right t),
              sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, geom_sum_succ]
          ring
        have h2 := properDivsSum_eq_sigma_sub (n := B * p ^ (t + 1))
        have h3 := properDivsSum_eq_sigma_sub (n := m)
        have h4 := properDivsSum_eq_sigma_sub (n := B)
        have h5 : B * p ^ (t + 1) = p * m := by dsimp [m]; rw [pow_succ]; ring
        have h3p : p * properDivsSum m + p * m = p * sigma 1 m := by
          calc p * properDivsSum m + p * m = p * (properDivsSum m + m) := by ring
            _ = p * sigma 1 m := by rw [h3]
        omega
      let repZ (n : ℕ) (x : ℤ) : Prop := ∃ y : ℕ, repNat n.properDivisors y ∧ (y : ℤ) = x
      have hcov_next : ∀ y, L ≤ y → y ≤ properDivsSum (B * p ^ (t + 1)) - L →
          repNat (B * p ^ (t + 1)).properDivisors y := by
        intro y hy1 hy2
        have hres : repZ (B * p ^ (t + 1)) (y : ℤ) := by
          apply middle_next (A := repZ m) (B := repZ B) (C := repZ (B * p ^ (t + 1)))
            (P := (properDivsSum B : ℤ)) (T := (properDivsSum m : ℤ))
            (b := (B : ℤ)) (L := (L : ℤ)) (g := (g : ℤ)) (r := (p : ℤ))
          · exact_mod_cast hp.pos
          · omega
          · have : (p : ℤ) * (properDivsSum B : ℤ) ≤ (p : ℤ) * (properDivsSum m : ℤ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hP_ge) (by exact_mod_cast hp.pos.le)
            omega
          · exact ⟨properDivsSum m, ⟨m.properDivisors, subset_rfl, rfl⟩, rfl⟩
          · intro k hk1 hk2
            lift k to ℕ using hk1
            obtain ⟨i, hi, h1, h2⟩ := hgap_t k (by change k < properDivsSum m; omega)
            exact ⟨(i : ℤ), ⟨i, hi, rfl⟩, by omega, by omega⟩
          · intro z hz1 hz2
            lift z to ℕ using (by omega)
            exact ⟨z, hcovB z (by omega) (by omega), rfl⟩
          · rintro i ⟨iN, hiN, rfl⟩ z ⟨zN, hzN, rfl⟩
            have hlay := layers_nat hmpos (dvd_mul_right B (p ^ t))
              (hp.coprime_iff_not_dvd.mp hcop.symm) hp.one_lt hiN hzN
            have hEq : p * m = B * p ^ (t + 1) := by dsimp [m]; rw [pow_succ]; ring
            rw [hEq] at hlay
            exact ⟨⟨zN + p * iN, hlay.1, by push_cast; ring⟩,
                   ⟨B + zN + p * iN, hlay.2, by push_cast; ring⟩⟩
          · exact_mod_cast hy1
          · omega
        obtain ⟨y', hy', hyEq⟩ := hres
        have : y' = y := by exact_mod_cast hyEq
        rwa [← this]
      have hsub : m.properDivisors ⊆ (B * p ^ (t + 1)).properDivisors := by
        intro d hd
        obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp hd
        have hEq : B * p ^ (t + 1) = p * m := by dsimp [m]; rw [pow_succ]; ring
        rw [hEq]
        exact Nat.mem_properDivisors.mpr ⟨hd1.trans (dvd_mul_left m p),
          lt_trans hd2 (by nlinarith [hp.one_lt])⟩
      have hgap_next := repNat_union_gap hg hsub (by change L ≤ properDivsSum m; omega) hcov_next hgap_t
      exact ⟨hcov_next, hgap_next⟩
  intro d _
  exact step d

private structure Base3Data where
  a0 : ℕ
  b0 : ℕ
  r : ℕ
  maxP : ℕ
  L : ℕ
  P0 : ℕ
  modStep : ℕ
  dsB0 : List ℕ
  dsUr : List ℕ
  dsU5 : List ℕ
  dsU3 : List ℕ


private def isStrictInc : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => Nat.ble (a + 1) b && isStrictInc (b :: rest)

private lemma isStrictInc_nodup : ∀ l : List ℕ, isStrictInc l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_singleton _
  | a :: b :: rest, h => by
    simp only [isStrictInc, Bool.and_eq_true, Nat.ble_eq] at h
    have htail := isStrictInc_nodup (b :: rest) h.2
    have hpw : (a :: b :: rest).Pairwise (· < ·) := by
      have aux : ∀ l : List ℕ, isStrictInc l = true → l.Pairwise (· < ·) := by
        intro l
        induction l with
        | nil => intro _; exact List.Pairwise.nil
        | cons x xs ih =>
          cases xs with
          | nil => intro _; exact List.pairwise_singleton _ _
          | cons y ys =>
            intro h'
            simp only [isStrictInc, Bool.and_eq_true, Nat.ble_eq] at h'
            have ht := ih h'.2
            refine List.Pairwise.cons ?_ ht
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz'
            · omega
            · exact lt_trans (by omega : x < y) ((List.pairwise_cons.mp ht).1 z hz')
      exact aux (a :: b :: rest) (by simp [isStrictInc, Nat.ble_eq]; exact h)
    exact hpw.imp (fun hlt => ne_of_lt hlt)

private def checkProperDivsB (n P : ℕ) (ds : List ℕ) : Bool :=
  isStrictInc ds &&
  Nat.beq ds.sum P &&
  ds.all (fun d => Nat.beq (n % d) 0 && Nat.ble (d + 1) n)

private lemma properDivs_of_checkB {n P : ℕ} {ds : List ℕ} (hn : 0 < n)
    (hP : P = properDivsSum n) (h : checkProperDivsB n P ds = true) :
    ds.toFinset = n.properDivisors := by
  simp only [checkProperDivsB, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hinc, hsum⟩, hall⟩ := h
  exact toFinset_eq_properDivisors_of_sum hn (isStrictInc_nodup ds hinc)
    (fun d hd => ⟨Nat.dvd_of_mod_eq_zero (hall d hd).1, by have := (hall d hd).2; omega⟩)
    (hsum.trans hP)

private def checkBase3B (b : Base3Data) : Bool :=
  let B0 := 3 ^ b.a0 * 5 ^ b.b0 * b.r
  let ur := 3 ^ b.a0 * 5 ^ b.b0
  let u5 := 3 ^ b.a0 * b.r
  let u3 := 5 ^ b.b0 * b.r
  let num := b.P0 - 2 * b.L
  let ivs := ivsOfList b.dsB0
  let Pur := b.dsUr.sum
  let Pu5 := b.dsU5.sum
  let Pu3 := b.dsU3.sum
  Nat.ble 2 b.a0 &&
  Nat.ble 1 b.b0 &&
  Nat.ble (5 * (2 * b.L + 24)) b.P0 &&
  Nat.ble (2 * b.L) b.P0 &&
  Nat.ble (b.maxP * 2) (num + 1) &&
  Nat.ble (B0 + 2 * b.L) (20 * b.P0) &&
  checkProperDivsB B0 b.P0 b.dsB0 &&
  checkProperDivsB ur Pur b.dsUr &&
  checkProperDivsB u5 Pu5 b.dsU5 &&
  checkProperDivsB u3 Pu3 b.dsU3 &&
  checkCovB ivs b.L (b.P0 - b.L) &&
  checkGapIvsB 2 ivs 0 &&
  ivs.all (fun ab => Nat.ble ab.1 ab.2) &&
  inIvsB ivs b.P0 &&
  checkModB ivs b.modStep (b.L - 1) &&
  checkSortedRelGapB ur num (b.r * B0) b.dsUr 0 &&
  checkSortedRelGapB u5 num (5 * B0) b.dsU5 0 &&
  Nat.ble (5 * B0 * u5) (num * (b.r * u5) + 5 * B0 * Pu5) &&
  checkSortedRelGapB u3 num (3 * B0) b.dsU3 0 &&
  Nat.ble (3 * B0 * u3) (num * (5 * u3) + 3 * B0 * Pu3) &&
  Nat.ble (3 * B0 * u3) (num * (b.r * u3) + 3 * B0 * Pu3) &&
  Nat.ble (B0 * ur) (num * ur + b.r * B0 * Pur) &&
  Nat.ble (B0 * u5) (num * u5 + 5 * B0 * Pu5) &&
  Nat.ble (B0 * u3) (num * u3 + 3 * B0 * Pu3)

private def bases3List : List Base3Data := [
  ⟨3, 1, 17, 31, 12, 2025, 6, [1, 3, 5, 9, 15, 17, 27, 45, 51, 85, 135, 153, 255, 459, 765], [1, 3, 5, 9, 15, 27, 45], [1, 3, 9, 17, 27, 51, 153], [1, 5, 17]⟩,
  ⟨3, 1, 19, 29, 27, 2235, 6, [1, 3, 5, 9, 15, 19, 27, 45, 57, 95, 135, 171, 285, 513, 855], [1, 3, 5, 9, 15, 27, 45], [1, 3, 9, 19, 27, 57, 171], [1, 5, 19]⟩,
  ⟨4, 1, 17, 509, 12, 6183, 6, [1, 3, 5, 9, 15, 17, 27, 45, 51, 81, 85, 135, 153, 255, 405, 459, 765, 1377, 2295], [1, 3, 5, 9, 15, 27, 45, 81, 135], [1, 3, 9, 17, 27, 51, 81, 153, 459], [1, 5, 17]⟩,
  ⟨4, 1, 19, 191, 27, 6825, 6, [1, 3, 5, 9, 15, 19, 27, 45, 57, 81, 95, 135, 171, 285, 405, 513, 855, 1539, 2565], [1, 3, 5, 9, 15, 27, 45, 81, 135], [1, 3, 9, 19, 27, 57, 81, 171, 513], [1, 5, 19]⟩,
  ⟨4, 1, 23, 97, 35, 8109, 6, [1, 3, 5, 9, 15, 23, 27, 45, 69, 81, 115, 135, 207, 345, 405, 621, 1035, 1863, 3105], [1, 3, 5, 9, 15, 27, 45, 81, 135], [1, 3, 9, 23, 27, 69, 81, 207, 621], [1, 5, 23]⟩,
  ⟨4, 1, 29, 67, 68, 10035, 6, [1, 3, 5, 9, 15, 27, 29, 45, 81, 87, 135, 145, 261, 405, 435, 783, 1305, 2349, 3915], [1, 3, 5, 9, 15, 27, 45, 81, 135], [1, 3, 9, 27, 29, 81, 87, 261, 783], [1, 5, 29]⟩,
  ⟨4, 1, 31, 61, 39, 10677, 6, [1, 3, 5, 9, 15, 27, 31, 45, 81, 93, 135, 155, 279, 405, 465, 837, 1395, 2511, 4185], [1, 3, 5, 9, 15, 27, 45, 81, 135], [1, 3, 9, 27, 31, 81, 93, 279, 837], [1, 5, 31]⟩,
  ⟨4, 1, 37, 53, 72, 12603, 6, [1, 3, 5, 9, 15, 27, 37, 45, 81, 111, 135, 185, 333, 405, 555, 999, 1665, 2997, 4995], [1, 3, 5, 9, 15, 27, 45, 81, 135], [1, 3, 9, 27, 37, 81, 111, 333, 999], [1, 5, 37]⟩,
  ⟨4, 1, 41, 47, 80, 13887, 6, [1, 3, 5, 9, 15, 27, 41, 45, 81, 123, 135, 205, 369, 405, 615, 1107, 1845, 3321, 5535], [1, 3, 5, 9, 15, 27, 45, 81, 135], [1, 3, 9, 27, 41, 81, 123, 369, 1107], [1, 5, 41]⟩,
  ⟨2, 2, 17, 509, 12, 3429, 3, [1, 3, 5, 9, 15, 17, 25, 45, 51, 75, 85, 153, 225, 255, 425, 765, 1275], [1, 3, 5, 9, 15, 25, 45, 75], [1, 3, 9, 17, 51], [1, 5, 17, 25, 85]⟩,
  ⟨2, 2, 19, 191, 12, 3785, 3, [1, 3, 5, 9, 15, 19, 25, 45, 57, 75, 95, 171, 225, 285, 475, 855, 1425], [1, 3, 5, 9, 15, 25, 45, 75], [1, 3, 9, 19, 57], [1, 5, 19, 25, 95]⟩,
  ⟨2, 2, 23, 97, 23, 4497, 3, [1, 3, 5, 9, 15, 23, 25, 45, 69, 75, 115, 207, 225, 345, 575, 1035, 1725], [1, 3, 5, 9, 15, 25, 45, 75], [1, 3, 9, 23, 69], [1, 5, 23, 25, 115]⟩,
  ⟨3, 2, 29, 67, 23, 17625, 3, [1, 3, 5, 9, 15, 25, 27, 29, 45, 75, 87, 135, 145, 225, 261, 435, 675, 725, 783, 1305, 2175, 3915, 6525], [1, 3, 5, 9, 15, 25, 27, 45, 75, 135, 225], [1, 3, 9, 27, 29, 87, 261], [1, 5, 25, 29, 145]⟩,
  ⟨3, 2, 31, 61, 23, 18755, 3, [1, 3, 5, 9, 15, 25, 27, 31, 45, 75, 93, 135, 155, 225, 279, 465, 675, 775, 837, 1395, 2325, 4185, 6975], [1, 3, 5, 9, 15, 25, 27, 45, 75, 135, 225], [1, 3, 9, 27, 31, 93, 279], [1, 5, 25, 31, 155]⟩,
  ⟨3, 2, 37, 53, 23, 22145, 3, [1, 3, 5, 9, 15, 25, 27, 37, 45, 75, 111, 135, 185, 225, 333, 555, 675, 925, 999, 1665, 2775, 4995, 8325], [1, 3, 5, 9, 15, 25, 27, 45, 75, 135, 225], [1, 3, 9, 27, 37, 111, 333], [1, 5, 25, 37, 185]⟩,
  ⟨3, 2, 41, 47, 23, 24405, 3, [1, 3, 5, 9, 15, 25, 27, 41, 45, 75, 123, 135, 205, 225, 369, 615, 675, 1025, 1107, 1845, 3075, 5535, 9225], [1, 3, 5, 9, 15, 25, 27, 45, 75, 135, 225], [1, 3, 9, 27, 41, 123, 369], [1, 5, 25, 41, 205]⟩
]

private lemma bases3List_ok : bases3List.all checkBase3B = true := by decide +kernel

private def ds45_17_19 : List ℕ := [1, 3, 5, 9, 15, 17, 19, 45, 51, 57, 85, 95, 153, 171, 255, 285, 323, 765, 855, 969, 1615, 2907, 4845]
private def ds45_19 : List ℕ := [1, 3, 5, 9, 15, 19, 45, 57, 95, 171, 285]
private def ds45_17 : List ℕ := [1, 3, 5, 9, 15, 17, 45, 51, 85, 153, 255]

private def checkBase45_17_19 : Bool :=
  let B0 := 14535
  let P0 := 13545
  let L := 12
  let num := P0 - 2 * L
  let ivs := ivsOfList ds45_17_19
  let P19 := ds45_19.sum
  let P17 := ds45_17.sum
  checkProperDivsB B0 P0 ds45_17_19 &&
  checkProperDivsB 855 P19 ds45_19 &&
  checkProperDivsB 765 P17 ds45_17 &&
  checkCovB ivs L (P0 - L) &&
  checkGapIvsB 2 ivs 0 &&
  ivs.all (fun ab => Nat.ble ab.1 ab.2) &&
  inIvsB ivs P0 &&
  checkModB ivs 6 (L - 1) &&
  checkSortedRelGapB 855 num (17 * B0) ds45_19 0 &&
  checkSortedRelGapB 765 num (19 * B0) ds45_17 0 &&
  Nat.ble (19 * B0 * 765) (num * (17 * 765) + 19 * B0 * P17) &&
  Nat.ble (B0 * 855) (num * 855 + 17 * B0 * P19) &&
  Nat.ble (B0 * 765) (num * 765 + 19 * B0 * P17)

private lemma base45_17_19_ok : checkBase45_17_19 = true := by decide +kernel

/- ### Exact sigma / ppSum helpers -/

private def ppSum (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => ppSum p e + p ^ (e + 1)

private lemma ppSum_eq_sigma (p e : ℕ) (hp : p.Prime) :
    ppSum p e = sigma 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp]
  induction e with
  | zero => simp [ppSum]
  | succ e ih => simp [ppSum, ih, Finset.sum_range_succ]

private lemma ppSum_pos (p e : ℕ) : 0 < ppSum p e := by
  induction e with
  | zero => simp [ppSum]
  | succ e ih => simp [ppSum]; omega

private lemma ppSum_lt_lim {p e : ℕ} (hp : 2 ≤ p) :
    ppSum p e * (p - 1) < p * p ^ e := by
  have h : ppSum p e * (p - 1) + 1 = p ^ (e + 1) := by
    induction e with
    | zero => simp [ppSum]; omega
    | succ e ih =>
      rw [ppSum, add_mul]
      have h1 : p ^ (e + 1) * (p - 1) + p ^ (e + 1) = p ^ (e + 1) * p := by
        rw [show p ^ (e + 1) * (p - 1) + p ^ (e + 1) = p ^ (e + 1) * ((p - 1) + 1) by ring]
        rw [Nat.sub_add_cancel (by omega)]
      have h2 : p ^ (e + 1 + 1) = p ^ (e + 1) * p := pow_succ p (e + 1)
      linarith [ih, h1, h2]
  rw [pow_succ'] at h
  omega

private lemma ppSum_mono_exp {p a b : ℕ} (hp : 2 ≤ p) (hab : a ≤ b) :
    ppSum p a * p ^ b ≤ ppSum p b * p ^ a := by
  induction hab with
  | refl => exact le_rfl
  | @step m hm ih =>
    rw [ppSum, add_mul, pow_succ]
    calc ppSum p a * (p ^ m * p) = (ppSum p a * p ^ m) * p := by ring
      _ ≤ (ppSum p m * p ^ a) * p := Nat.mul_le_mul_right p ih
      _ ≤ ppSum p m * p ^ a + p ^ (m + 1) * p ^ a := by
          have h1 : ppSum p m * (p - 1) ≤ p ^ (m + 1) := by
            have := ppSum_lt_lim (p := p) (e := m) hp; rw [pow_succ'] ; omega
          have h2 : ppSum p m * p = ppSum p m + ppSum p m * (p - 1) := by
            zify [show 1 ≤ p by omega]; ring
          have h3 : ppSum p m * p ≤ ppSum p m + p ^ (m + 1) := by omega
          calc (ppSum p m * p ^ a) * p = (ppSum p m * p) * p ^ a := by ring
            _ ≤ (ppSum p m + p ^ (m + 1)) * p ^ a := Nat.mul_le_mul_right _ h3
            _ = ppSum p m * p ^ a + p ^ (m + 1) * p ^ a := by ring

private lemma ppSum_anti_prime {p q e : ℕ} (_hp : 1 ≤ p) (hpq : p ≤ q) :
    ppSum q e * p ^ e ≤ ppSum p e * q ^ e := by
  induction e with
  | zero => simp [ppSum]
  | succ e ih =>
    rw [ppSum, ppSum, add_mul, add_mul, pow_succ, pow_succ]
    have h1 : ppSum q e * (p ^ e * p) ≤ ppSum p e * (q ^ e * q) := by
      calc ppSum q e * (p ^ e * p) = (ppSum q e * p ^ e) * p := by ring
        _ ≤ (ppSum p e * q ^ e) * q := Nat.mul_le_mul ih hpq
        _ = ppSum p e * (q ^ e * q) := by ring
    have h2 : q ^ e * q * (p ^ e * p) = p ^ e * p * (q ^ e * q) := by ring
    omega

private lemma sigma_three_primes {r a b c : ℕ} (hr : r.Prime) (h5r : 5 < r) :
    sigma 1 (3 ^ a * 5 ^ b * r ^ c) = ppSum 3 a * ppSum 5 b * ppSum r c := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have h35 : (3 ^ a).Coprime (5 ^ b) :=
    ((Nat.coprime_primes h3p h5p).mpr (by decide)).pow _ _
  have h3r : (3 ^ a).Coprime (r ^ c) :=
    ((Nat.coprime_primes h3p hr).mpr (by omega)).pow _ _
  have h5r' : (5 ^ b).Coprime (r ^ c) :=
    ((Nat.coprime_primes h5p hr).mpr (by omega)).pow _ _
  rw [isMultiplicative_sigma.map_mul_of_coprime (h3r.mul_left h5r'),
      isMultiplicative_sigma.map_mul_of_coprime h35,
      ppSum_eq_sigma 3 a h3p, ppSum_eq_sigma 5 b h5p, ppSum_eq_sigma r c hr]

private lemma sigma_four_primes {r p a b c d : ℕ} (hr : r.Prime) (hp : p.Prime)
    (h5r : 5 < r) (hrp : r < p) :
    sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d) = ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have hc3 : (3 ^ a).Coprime (p ^ d) := ((Nat.coprime_primes h3p hp).mpr (by omega)).pow _ _
  have hc5 : (5 ^ b).Coprime (p ^ d) := ((Nat.coprime_primes h5p hp).mpr (by omega)).pow _ _
  have hcr : (r ^ c).Coprime (p ^ d) := ((Nat.coprime_primes hr hp).mpr (by omega)).pow _ _
  rw [isMultiplicative_sigma.map_mul_of_coprime ((hc3.mul_left hc5).mul_left hcr),
      sigma_three_primes hr h5r, ppSum_eq_sigma p d hp]

private lemma sigma_five_primes {r p q a b c d e : ℕ} (hr : r.Prime) (hp : p.Prime) (hq : q.Prime)
    (h5r : 5 < r) (hrp : r < p) (hpq : p < q) :
    sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e) =
      ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * ppSum q e := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have hc3 : (3 ^ a).Coprime (q ^ e) := ((Nat.coprime_primes h3p hq).mpr (by omega)).pow _ _
  have hc5 : (5 ^ b).Coprime (q ^ e) := ((Nat.coprime_primes h5p hq).mpr (by omega)).pow _ _
  have hcr : (r ^ c).Coprime (q ^ e) := ((Nat.coprime_primes hr hq).mpr (by omega)).pow _ _
  have hcp : (p ^ d).Coprime (q ^ e) := ((Nat.coprime_primes hp hq).mpr (by omega)).pow _ _
  rw [isMultiplicative_sigma.map_mul_of_coprime (((hc3.mul_left hc5).mul_left hcr).mul_left hcp),
      sigma_four_primes hr hp h5r hrp, ppSum_eq_sigma q e hq]

private lemma properDivsSum_35r {r a b c : ℕ} (hr : r.Prime) (h5r : 5 < r) :
    properDivsSum (3 ^ a * 5 ^ b * r ^ c) =
      ppSum 3 a * ppSum 5 b * ppSum r c - 3 ^ a * 5 ^ b * r ^ c := by
  have h1 := properDivsSum_eq_sigma_sub (n := 3 ^ a * 5 ^ b * r ^ c)
  rw [sigma_three_primes hr h5r] at h1
  omega

private lemma properDivsSum_35rp {r p a b c d : ℕ} (hr : r.Prime) (hp : p.Prime)
    (h5r : 5 < r) (hrp : r < p) :
    properDivsSum (3 ^ a * 5 ^ b * r ^ c * p ^ d) =
      ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d - 3 ^ a * 5 ^ b * r ^ c * p ^ d := by
  have h1 := properDivsSum_eq_sigma_sub (n := 3 ^ a * 5 ^ b * r ^ c * p ^ d)
  rw [sigma_four_primes hr hp h5r hrp] at h1
  omega

private lemma lift_base3_core (bd : Base3Data) (hmem : bd ∈ bases3List)
    (hr : bd.r.Prime) (h5r : 5 < bd.r)
    (hP0_eq : bd.P0 = properDivsSum (3 ^ bd.a0 * 5 ^ bd.b0 * bd.r))
    (hPur_eq : bd.dsUr.sum = properDivsSum (3 ^ bd.a0 * 5 ^ bd.b0))
    (hPu5_eq : bd.dsU5.sum = properDivsSum (3 ^ bd.a0 * bd.r))
    (hPu3_eq : bd.dsU3.sum = properDivsSum (5 ^ bd.b0 * bd.r))
    {a b c : ℕ} (ha : bd.a0 ≤ a) (hb : bd.b0 ≤ b) (hc : 1 ≤ c) :
    let B := 3 ^ a * 5 ^ b * bd.r ^ c
    (∀ y, bd.L ≤ y → y ≤ properDivsSum B - bd.L → repNat B.properDivisors y) ∧
    (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
    (∀ x, 0 < x → x < bd.L → x % bd.modStep = 0 → repNat B.properDivisors x) ∧
    (5 * (2 * bd.L + 24) ≤ properDivsSum B) ∧
    (2 * bd.L ≤ properDivsSum B) ∧
    (bd.maxP * 2 ≤ properDivsSum B - 2 * bd.L + 1) ∧
    (B + 2 * bd.L ≤ properDivsSum B + 19 * properDivsSum B + 1) := by
  have hchk : checkBase3B bd = true := List.all_eq_true.mp bases3List_ok bd hmem
  dsimp only [checkBase3B] at hchk
  repeat rw [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha0ge2, hb0ge1⟩, hbig⟩, h2L⟩, hmp⟩, hov⟩, hdsB0⟩, hdsUr⟩, hdsU5⟩, hdsU3⟩,
    hcovB⟩, hgapB⟩, hwfB⟩, hP0in⟩, hmodB⟩, hrelUr⟩, hrelU5⟩, hmu5r⟩, hrelU3⟩, hmu35⟩, hmu3r⟩,
    hfinr⟩, hfin5⟩, hfin3⟩
  have ha0_2 : 2 ≤ bd.a0 := (Iff.of_eq Nat.ble_eq).mp ha0ge2
  have hb0_1 : 1 ≤ bd.b0 := (Iff.of_eq Nat.ble_eq).mp hb0ge1
  have hbig' : 5 * (2 * bd.L + 24) ≤ bd.P0 := (Iff.of_eq Nat.ble_eq).mp hbig
  have h2L' : 2 * bd.L ≤ bd.P0 := (Iff.of_eq Nat.ble_eq).mp h2L
  have hmp' : bd.maxP * 2 ≤ bd.P0 - 2 * bd.L + 1 := (Iff.of_eq Nat.ble_eq).mp hmp
  have hov' : 3 ^ bd.a0 * 5 ^ bd.b0 * bd.r + 2 * bd.L ≤ 20 * bd.P0 := (Iff.of_eq Nat.ble_eq).mp hov
  let B0 := 3 ^ bd.a0 * 5 ^ bd.b0 * bd.r
  let ur := 3 ^ bd.a0 * 5 ^ bd.b0
  let u5 := 3 ^ bd.a0 * bd.r
  let u3 := 5 ^ bd.b0 * bd.r
  change bd.P0 = properDivsSum B0 at hP0_eq
  change B0 + 2 * bd.L ≤ 20 * bd.P0 at hov'
  have hB0pos : 0 < B0 := by have := hr.pos; positivity
  have hurpos : 0 < ur := by positivity
  have hu5pos : 0 < u5 := by have := hr.pos; positivity
  have hu3pos : 0 < u3 := by have := hr.pos; positivity
  have htoB0 : bd.dsB0.toFinset = B0.properDivisors := properDivs_of_checkB hB0pos hP0_eq hdsB0
  have htoUr : bd.dsUr.toFinset = ur.properDivisors := properDivs_of_checkB hurpos hPur_eq hdsUr
  have htoU5 : bd.dsU5.toFinset = u5.properDivisors := properDivs_of_checkB hu5pos hPu5_eq hdsU5
  have htoU3 : bd.dsU3.toFinset = u3.properDivisors := properDivs_of_checkB hu3pos hPu3_eq hdsU3
  have hndB0 : bd.dsB0.Nodup := by
    simp only [checkProperDivsB, Bool.and_eq_true] at hdsB0
    exact isStrictInc_nodup _ hdsB0.1.1
  have hrep0 : ∀ x, inIvs (ivsOfList bd.dsB0) x → repNat B0.properDivisors x := by
    intro x hx; rw [← htoB0]; exact repNat_of_inIvs hndB0 x hx
  have hcov0 : ∀ y, bd.L ≤ y → y ≤ properDivsSum B0 - bd.L → repNat B0.properDivisors y := by
    intro y hy1 hy2
    exact hrep0 y (inIvs_of_checkCovB hcovB y hy1 (by omega))
  have hgap0 : ∀ k, k < properDivsSum B0 → ∃ i, repNat B0.properDivisors i ∧ k < i + 2 ∧ i ≤ k := by
    intro k hk
    have hwf : ∀ ab ∈ ivsOfList bd.dsB0, ab.1 ≤ ab.2 := fun ab hab =>
      (Iff.of_eq Nat.ble_eq).mp (List.all_eq_true.mp hwfB ab hab)
    obtain ⟨ab0, hab0, _, hP0ab⟩ := inIvs_of_inIvsB hP0in
    exact gap_of_checkGapIvsB (by decide) (ivsOfList bd.dsB0) 0 hgapB B0.properDivisors hrep0
      ⟨∅, by simp, by simp⟩ k (Nat.zero_le k) hwf ⟨ab0, hab0, by omega⟩
  have hmod0 : ∀ x, 0 < x → x < bd.L → x % bd.modStep = 0 → repNat B0.properDivisors x := by
    intro x hx1 hx2 hx3
    exact hrep0 x (mod_of_checkModB (bd.L - 1) hmodB x hx1 (by omega) hx3)
  -- Helper: ratio bound from B0 to any multiple M
  have hratio : ∀ M : ℕ, B0 ∣ M → 0 < M →
      (bd.P0 - 2 * bd.L) * M ≤ (properDivsSum M - 2 * bd.L) * B0 ∧ bd.P0 ≤ properDivsSum M := by
    intro M hM hMpos
    have hmo := properDivsSum_ratio_mono hB0pos hMpos hM
    rw [← hP0_eq] at hmo
    have hB0le : B0 ≤ M := Nat.le_of_dvd hMpos hM
    have hPge : bd.P0 ≤ properDivsSum M := by nlinarith
    exact ⟨sub_mul_le_sub_mul_of_mul_le h2L' (le_trans h2L' hPge) hB0le hmo, hPge⟩
  have hrelUr' : HasRelGap ur (bd.P0 - 2 * bd.L) (bd.r * B0) :=
    hasRelGap_of_sorted_list htoUr hrelUr
  have hrelU5_0 : HasRelGap u5 (bd.P0 - 2 * bd.L) (5 * B0) :=
    hasRelGap_of_sorted_list htoU5 hrelU5
  have hrelU3_0 : HasRelGap u3 (bd.P0 - 2 * bd.L) (3 * B0) :=
    hasRelGap_of_sorted_list htoU3 hrelU3
  -- Step 1: lift r from 1 to c (ur fixed!)
  have hstep1 : ∀ c', 1 ≤ c' →
      (∀ y, bd.L ≤ y → y ≤ properDivsSum (3 ^ bd.a0 * 5 ^ bd.b0 * bd.r ^ c') - bd.L →
        repNat (3 ^ bd.a0 * 5 ^ bd.b0 * bd.r ^ c').properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ bd.a0 * 5 ^ bd.b0 * bd.r ^ c') →
        ∃ i, repNat (3 ^ bd.a0 * 5 ^ bd.b0 * bd.r ^ c').properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    intro c' hc'
    induction c' with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero => simpa [B0] using ⟨hcov0, hgap0⟩
      | succ m' =>
        obtain ⟨hc1, hg1⟩ := ih (by omega)
        let Bcur := 3 ^ bd.a0 * 5 ^ bd.b0 * bd.r ^ (m' + 1)
        have hdvd : B0 ∣ Bcur := by
          dsimp [B0, Bcur]
          exact Nat.mul_dvd_mul_left _ (dvd_pow_self bd.r (by omega))
        have hpos : 0 < Bcur := by have := hr.pos; positivity
        have hrat := hratio Bcur hdvd hpos
        have hcop_r : ¬ bd.r ∣ ur := by
          intro h; dsimp [ur] at h
          rcases hr.dvd_mul.mp h with h3 | h5
          · exact absurd (hr.dvd_of_dvd_pow h3) (by intro hd; have := Nat.le_of_dvd (by decide) hd; omega)
          · exact absurd (hr.dvd_of_dvd_pow h5) (by intro hd; have := Nat.le_of_dvd (by decide) hd; omega)
        have hres := lift_dividing_prime_step hr hurpos hcop_r (show 1 ≤ m' + 1 by omega)
          (show Bcur = bd.r ^ (m' + 1) * ur by dsimp [Bcur, ur]; ring) hB0pos (by decide)
          (le_trans h2L' hrat.2) hc1 hg1 hrat.1 hrelUr'
          (by rw [← hPur_eq]; exact (Iff.of_eq Nat.ble_eq).mp hfinr)
        have hEq : bd.r * Bcur = 3 ^ bd.a0 * 5 ^ bd.b0 * bd.r ^ (m' + 2) := by
          dsimp [Bcur]; rw [pow_succ]; ring
        rwa [hEq] at hres
  -- Helper: lift HasRelGap for u5 * r^t
  have hrelU5_all : ∀ t : ℕ, HasRelGap (3 ^ bd.a0 * bd.r ^ (t + 1)) (bd.P0 - 2 * bd.L) (5 * B0) := by
    intro t
    induction t with
    | zero => simpa [u5] using hrelU5_0
    | succ t ih =>
      have hpos : 0 < 3 ^ bd.a0 * bd.r ^ (t + 1) := by have := hr.pos; positivity
      have hdvd : u5 ∣ 3 ^ bd.a0 * bd.r ^ (t + 1) := by
        dsimp [u5]; exact Nat.mul_dvd_mul_left _ (dvd_pow_self bd.r (by omega))
      have hmo := properDivsSum_ratio_mono hu5pos hpos hdvd
      have hfin5' : 5 * B0 * u5 ≤ (bd.P0 - 2 * bd.L) * (bd.r * u5) + 5 * B0 * properDivsSum u5 := by
        rw [← hPu5_eq]; exact (Iff.of_eq Nat.ble_eq).mp hmu5r
      have hdef : 5 * B0 * (3 ^ bd.a0 * bd.r ^ (t + 1)) ≤
          (bd.P0 - 2 * bd.L) * (bd.r * (3 ^ bd.a0 * bd.r ^ (t + 1))) +
          5 * B0 * properDivsSum (3 ^ bd.a0 * bd.r ^ (t + 1)) := by
        have h1 := Nat.mul_le_mul_right (3 ^ bd.a0 * bd.r ^ (t + 1)) hfin5'
        have h2 := Nat.mul_le_mul_left (5 * B0) hmo
        apply Nat.le_of_mul_le_mul_right _ hu5pos
        linarith
      have h := ih.mul_prime hr hpos hdef
      have hEq : bd.r * (3 ^ bd.a0 * bd.r ^ (t + 1)) = 3 ^ bd.a0 * bd.r ^ (t + 2) := by rw [pow_succ]; ring
      rwa [hEq] at h
  -- Step 2: lift 5 from b0 to b
  have hstep2 : ∀ b', bd.b0 ≤ b' →
      (∀ y, bd.L ≤ y → y ≤ properDivsSum (3 ^ bd.a0 * 5 ^ b' * bd.r ^ c) - bd.L →
        repNat (3 ^ bd.a0 * 5 ^ b' * bd.r ^ c).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ bd.a0 * 5 ^ b' * bd.r ^ c) →
        ∃ i, repNat (3 ^ bd.a0 * 5 ^ b' * bd.r ^ c).properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    intro b' hb'
    induction b' with
    | zero => omega
    | succ m ih =>
      by_cases heq : m + 1 = bd.b0
      · rw [heq]; exact hstep1 c hc
      · obtain ⟨hc2, hg2⟩ := ih (by omega)
        have hm1 : 1 ≤ m := by omega
        let Bcur := 3 ^ bd.a0 * 5 ^ m * bd.r ^ c
        let u5c := 3 ^ bd.a0 * bd.r ^ c
        have hu5c_pos : 0 < u5c := by have := hr.pos; positivity
        have hBcur_pos : 0 < Bcur := by have := hr.pos; positivity
        have hdvdB0 : B0 ∣ Bcur := by
          dsimp [B0, Bcur]
          exact Nat.mul_dvd_mul (Nat.mul_dvd_mul_left _ (pow_dvd_pow 5 (by omega)))
            (by simpa using pow_dvd_pow bd.r hc)
        have hrat := hratio Bcur hdvdB0 hBcur_pos
        have h5p : Nat.Prime 5 := by decide
        have hcop5 : ¬ 5 ∣ u5c := by
          intro h; dsimp [u5c] at h
          rcases h5p.dvd_mul.mp h with h3 | hr'
          · exact absurd (h5p.dvd_of_dvd_pow h3) (by decide)
          · exact absurd (h5p.dvd_of_dvd_pow hr') (by intro hd; rcases hr.eq_one_or_self_of_dvd 5 hd with h1 | h2 <;> omega)
        have hrel5c : HasRelGap u5c (bd.P0 - 2 * bd.L) (5 * B0) := by
          have := hrelU5_all (c - 1)
          rwa [show c - 1 + 1 = c by omega] at this
        have hfin5c : B0 * u5c ≤ (bd.P0 - 2 * bd.L) * u5c + 5 * B0 * properDivsSum u5c := by
          have hdvd_u5 : u5 ∣ u5c := by
            dsimp [u5, u5c]; exact Nat.mul_dvd_mul_left _ (by simpa using pow_dvd_pow bd.r hc)
          have hmo := properDivsSum_ratio_mono hu5pos hu5c_pos hdvd_u5
          have hfin5_0 : B0 * u5 ≤ (bd.P0 - 2 * bd.L) * u5 + 5 * B0 * properDivsSum u5 := by
            rw [← hPu5_eq]; exact (Iff.of_eq Nat.ble_eq).mp hfin5
          have h1 := Nat.mul_le_mul_right u5c hfin5_0
          have h2 := Nat.mul_le_mul_left (5 * B0) hmo
          apply Nat.le_of_mul_le_mul_right _ hu5pos
          linarith
        have hres := lift_dividing_prime_step h5p hu5c_pos hcop5 hm1
          (show Bcur = 5 ^ m * u5c by dsimp [Bcur, u5c]; ring) hB0pos (by decide)
          (le_trans h2L' hrat.2) hc2 hg2 hrat.1 hrel5c hfin5c
        have hEq : 5 * Bcur = 3 ^ bd.a0 * 5 ^ (m + 1) * bd.r ^ c := by
          dsimp [Bcur]; rw [pow_succ]; ring
        rwa [hEq] at hres
  -- Helper: lift HasRelGap for 5^b * r^c
  have hrelU3_r : ∀ t : ℕ, HasRelGap (5 ^ bd.b0 * bd.r ^ (t + 1)) (bd.P0 - 2 * bd.L) (3 * B0) := by
    intro t
    induction t with
    | zero => simpa [u3] using hrelU3_0
    | succ t ih =>
      have hpos : 0 < 5 ^ bd.b0 * bd.r ^ (t + 1) := by have := hr.pos; positivity
      have hdvd : u3 ∣ 5 ^ bd.b0 * bd.r ^ (t + 1) := by
        dsimp [u3]; exact Nat.mul_dvd_mul_left _ (dvd_pow_self bd.r (by omega))
      have hmo := properDivsSum_ratio_mono hu3pos hpos hdvd
      have hmu : 3 * B0 * u3 ≤ (bd.P0 - 2 * bd.L) * (bd.r * u3) + 3 * B0 * properDivsSum u3 := by
        rw [← hPu3_eq]; exact (Iff.of_eq Nat.ble_eq).mp hmu3r
      have hdef : 3 * B0 * (5 ^ bd.b0 * bd.r ^ (t + 1)) ≤
          (bd.P0 - 2 * bd.L) * (bd.r * (5 ^ bd.b0 * bd.r ^ (t + 1))) +
          3 * B0 * properDivsSum (5 ^ bd.b0 * bd.r ^ (t + 1)) := by
        have h1 := Nat.mul_le_mul_right (5 ^ bd.b0 * bd.r ^ (t + 1)) hmu
        have h2 := Nat.mul_le_mul_left (3 * B0) hmo
        apply Nat.le_of_mul_le_mul_right _ hu3pos
        linarith
      have h := ih.mul_prime hr hpos hdef
      have hEq : bd.r * (5 ^ bd.b0 * bd.r ^ (t + 1)) = 5 ^ bd.b0 * bd.r ^ (t + 2) := by rw [pow_succ]; ring
      rwa [hEq] at h
  have hrelU3_all : ∀ b', bd.b0 ≤ b' → HasRelGap (5 ^ b' * bd.r ^ c) (bd.P0 - 2 * bd.L) (3 * B0) := by
    intro b' hb'
    induction b' with
    | zero => omega
    | succ m ih =>
      by_cases heq : m + 1 = bd.b0
      · rw [heq]; have := hrelU3_r (c - 1); rwa [show c - 1 + 1 = c by omega] at this
      · have ih' := ih (by omega)
        have hpos : 0 < 5 ^ m * bd.r ^ c := by have := hr.pos; positivity
        have hdvd : u3 ∣ 5 ^ m * bd.r ^ c := by
          dsimp [u3]
          exact Nat.mul_dvd_mul (pow_dvd_pow 5 (by omega)) (by simpa using pow_dvd_pow bd.r hc)
        have hmo := properDivsSum_ratio_mono hu3pos hpos hdvd
        have hmu : 3 * B0 * u3 ≤ (bd.P0 - 2 * bd.L) * (5 * u3) + 3 * B0 * properDivsSum u3 := by
          rw [← hPu3_eq]; exact (Iff.of_eq Nat.ble_eq).mp hmu35
        have hdef : 3 * B0 * (5 ^ m * bd.r ^ c) ≤
            (bd.P0 - 2 * bd.L) * (5 * (5 ^ m * bd.r ^ c)) + 3 * B0 * properDivsSum (5 ^ m * bd.r ^ c) := by
          have h1 := Nat.mul_le_mul_right (5 ^ m * bd.r ^ c) hmu
          have h2 := Nat.mul_le_mul_left (3 * B0) hmo
          apply Nat.le_of_mul_le_mul_right _ hu3pos
          linarith
        have h := ih'.mul_prime (by decide) hpos hdef
        have hEq : 5 * (5 ^ m * bd.r ^ c) = 5 ^ (m + 1) * bd.r ^ c := by rw [pow_succ]; ring
        rwa [hEq] at h
  -- Step 3: lift 3 from a0 to a
  have hstep3 : ∀ a', bd.a0 ≤ a' →
      (∀ y, bd.L ≤ y → y ≤ properDivsSum (3 ^ a' * 5 ^ b * bd.r ^ c) - bd.L →
        repNat (3 ^ a' * 5 ^ b * bd.r ^ c).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ a' * 5 ^ b * bd.r ^ c) →
        ∃ i, repNat (3 ^ a' * 5 ^ b * bd.r ^ c).properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    intro a' ha'
    induction a' with
    | zero => omega
    | succ m ih =>
      by_cases heq : m + 1 = bd.a0
      · rw [heq]; exact hstep2 b hb
      · obtain ⟨hc3, hg3⟩ := ih (by omega)
        have hm1 : 1 ≤ m := by omega
        let Bcur := 3 ^ m * 5 ^ b * bd.r ^ c
        let u3bc := 5 ^ b * bd.r ^ c
        have hu3bc_pos : 0 < u3bc := by have := hr.pos; positivity
        have hBcur_pos : 0 < Bcur := by have := hr.pos; positivity
        have hdvdB0 : B0 ∣ Bcur := by
          dsimp [B0, Bcur]
          exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 (by omega)) (pow_dvd_pow 5 hb))
            (by simpa using pow_dvd_pow bd.r hc)
        have hrat := hratio Bcur hdvdB0 hBcur_pos
        have h3p : Nat.Prime 3 := by decide
        have hcop3 : ¬ 3 ∣ u3bc := by
          intro h; dsimp [u3bc] at h
          rcases h3p.dvd_mul.mp h with h5 | hr'
          · exact absurd (h3p.dvd_of_dvd_pow h5) (by decide)
          · exact absurd (h3p.dvd_of_dvd_pow hr') (by intro hd; rcases hr.eq_one_or_self_of_dvd 3 hd with h1 | h2 <;> omega)
        have hfin3bc : B0 * u3bc ≤ (bd.P0 - 2 * bd.L) * u3bc + 3 * B0 * properDivsSum u3bc := by
          have hdvd_u3 : u3 ∣ u3bc := by
            dsimp [u3, u3bc]
            exact Nat.mul_dvd_mul (pow_dvd_pow 5 hb) (by simpa using pow_dvd_pow bd.r hc)
          have hmo := properDivsSum_ratio_mono hu3pos hu3bc_pos hdvd_u3
          have hfin3_0 : B0 * u3 ≤ (bd.P0 - 2 * bd.L) * u3 + 3 * B0 * properDivsSum u3 := by
            rw [← hPu3_eq]; exact (Iff.of_eq Nat.ble_eq).mp hfin3
          have h1 := Nat.mul_le_mul_right u3bc hfin3_0
          have h2 := Nat.mul_le_mul_left (3 * B0) hmo
          apply Nat.le_of_mul_le_mul_right _ hu3pos
          linarith
        have hres := lift_dividing_prime_step h3p hu3bc_pos hcop3 hm1
          (show Bcur = 3 ^ m * u3bc by dsimp [Bcur, u3bc]; ring) hB0pos (by decide)
          (le_trans h2L' hrat.2) hc3 hg3 hrat.1 (hrelU3_all b hb) hfin3bc
        have hEq : 3 * Bcur = 3 ^ (m + 1) * 5 ^ b * bd.r ^ c := by
          dsimp [Bcur]; rw [pow_succ]; ring
        rwa [hEq] at hres
  -- Combine all conclusions
  let B := 3 ^ a * 5 ^ b * bd.r ^ c
  have hBpos : 0 < B := by have := hr.pos; positivity
  have hdvdB0 : B0 ∣ B := by
    dsimp [B0, B]
    exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow 5 hb))
      (by simpa using pow_dvd_pow bd.r hc)
  have hrat := hratio B hdvdB0 hBpos
  have hsubB0 : B0.properDivisors ⊆ B.properDivisors := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp hd
    exact Nat.mem_properDivisors.mpr ⟨hd1.trans hdvdB0, lt_of_lt_of_le hd2 (Nat.le_of_dvd hBpos hdvdB0)⟩
  obtain ⟨hcovB, hgapB⟩ := hstep3 a ha
  have hP0_le : bd.P0 ≤ properDivsSum B := hrat.2
  refine ⟨hcovB, hgapB, ?_, le_trans hbig' hP0_le, le_trans h2L' hP0_le, ?_, ?_⟩
  · intro x hx1 hx2 hx3
    obtain ⟨s, hs, hsum⟩ := hmod0 x hx1 hx2 hx3
    exact ⟨s, hs.trans hsubB0, hsum⟩
  · change bd.maxP * 2 ≤ properDivsSum B - 2 * bd.L + 1; omega
  · have hmo := properDivsSum_ratio_mono hB0pos hBpos hdvdB0
    rw [← hP0_eq] at hmo
    have hB0le : B0 ≤ B := Nat.le_of_dvd hBpos hdvdB0
    have h20 : 20 * bd.P0 * B ≤ 20 * properDivsSum B * B0 := by
      have := Nat.mul_le_mul_left 20 hmo; linarith only [this]
    have h2 : B0 * B + 2 * bd.L * B ≤ 20 * bd.P0 * B := by
      have := Nat.mul_le_mul_right B hov'; linarith only [this]
    have h2L : 2 * bd.L * B0 ≤ 2 * bd.L * B := Nat.mul_le_mul_left (2 * bd.L) hB0le
    have h1 : B0 * (B + 2 * bd.L) ≤ B0 * (20 * properDivsSum B) := by
      linarith only [h20, h2, h2L]
    have h3 : B + 2 * bd.L ≤ 20 * properDivsSum B := Nat.le_of_mul_le_mul_left h1 hB0pos
    change B + 2 * bd.L ≤ properDivsSum B + 19 * properDivsSum B + 1; omega

private lemma lift_base_45_17_19 {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) :
    let B := 3 ^ 2 * 5 ^ 1 * 17 ^ c * 19 ^ d
    (∀ y, 12 ≤ y → y ≤ properDivsSum B - 12 → repNat B.properDivisors y) ∧
    (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
    (∀ x, 0 < x → x < 12 → x % 6 = 0 → repNat B.properDivisors x) ∧
    (5 * (2 * 12 + 24) ≤ properDivsSum B) := by
  have hchk := base45_17_19_ok
  dsimp only [checkBase45_17_19] at hchk
  repeat rw [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdsB0, hds19⟩, hds17⟩, hcovB⟩, hgapB⟩, hwfB⟩, hP0in⟩, hmodB⟩,
    hrel19⟩, hrel17⟩, hmu17⟩, hfin19⟩, hfin17⟩
  have hB0_eq : 3 ^ 2 * 5 ^ 1 * 17 ^ 1 * 19 ^ 1 = 14535 := by decide
  have hP0_eq : 13545 = properDivsSum 14535 := by
    rw [← hB0_eq, properDivsSum_35rp (by decide) (by decide) (by decide) (by decide)]
    decide
  have hP19_eq : ds45_19.sum = properDivsSum 855 := by
    have : 855 = 3 ^ 2 * 5 ^ 1 * 19 ^ 1 := by decide
    rw [this, properDivsSum_35r (by decide) (by decide)]; decide
  have hP17_eq : ds45_17.sum = properDivsSum 765 := by
    have : 765 = 3 ^ 2 * 5 ^ 1 * 17 ^ 1 := by decide
    rw [this, properDivsSum_35r (by decide) (by decide)]; decide
  have htoB0 : ds45_17_19.toFinset = (14535 : ℕ).properDivisors :=
    properDivs_of_checkB (by decide) hP0_eq hdsB0
  have hto19 : ds45_19.toFinset = (855 : ℕ).properDivisors :=
    properDivs_of_checkB (by decide) hP19_eq hds19
  have hto17 : ds45_17.toFinset = (765 : ℕ).properDivisors :=
    properDivs_of_checkB (by decide) hP17_eq hds17
  have hndB0 : ds45_17_19.Nodup := by
    simp only [checkProperDivsB, Bool.and_eq_true] at hdsB0
    exact isStrictInc_nodup _ hdsB0.1.1
  have hrep0 : ∀ x, inIvs (ivsOfList ds45_17_19) x → repNat (14535 : ℕ).properDivisors x := by
    intro x hx; rw [← htoB0]; exact repNat_of_inIvs hndB0 x hx
  have hcov0 : ∀ y, 12 ≤ y → y ≤ properDivsSum 14535 - 12 → repNat (14535 : ℕ).properDivisors y := by
    intro y hy1 hy2; exact hrep0 y (inIvs_of_checkCovB hcovB y hy1 (by omega))
  have hgap0 : ∀ k, k < properDivsSum 14535 → ∃ i, repNat (14535 : ℕ).properDivisors i ∧ k < i + 2 ∧ i ≤ k := by
    intro k hk
    have hwf : ∀ ab ∈ ivsOfList ds45_17_19, ab.1 ≤ ab.2 := fun ab hab =>
      (Iff.of_eq Nat.ble_eq).mp (List.all_eq_true.mp hwfB ab hab)
    obtain ⟨ab0, hab0, _, hP0ab⟩ := inIvs_of_inIvsB hP0in
    exact gap_of_checkGapIvsB (by decide) (ivsOfList ds45_17_19) 0 hgapB (14535 : ℕ).properDivisors hrep0
      ⟨∅, by simp, by simp⟩ k (Nat.zero_le k) hwf ⟨ab0, hab0, by omega⟩
  have hmod0 : ∀ x, 0 < x → x < 12 → x % 6 = 0 → repNat (14535 : ℕ).properDivisors x := by
    intro x hx1 hx2 hx3; exact hrep0 x (mod_of_checkModB 11 hmodB x hx1 (by omega) hx3)
  have hratio : ∀ M : ℕ, 14535 ∣ M → 0 < M →
      (13545 - 2 * 12) * M ≤ (properDivsSum M - 2 * 12) * 14535 ∧ 13545 ≤ properDivsSum M := by
    intro M hM hMpos
    have hmo := properDivsSum_ratio_mono (by decide) hMpos hM
    rw [← hP0_eq] at hmo
    have hle : 14535 ≤ M := Nat.le_of_dvd hMpos hM
    have hPge : 13545 ≤ properDivsSum M := by nlinarith
    exact ⟨sub_mul_le_sub_mul_of_mul_le (by decide) (by omega) hle hmo, hPge⟩
  have hrel19' : HasRelGap 855 (13545 - 2 * 12) (17 * 14535) :=
    hasRelGap_of_sorted_list hto19 hrel19
  have hrel17_0 : HasRelGap 765 (13545 - 2 * 12) (19 * 14535) :=
    hasRelGap_of_sorted_list hto17 hrel17
  -- Step 1: lift 17 from 1 to c
  have hstep1 : ∀ c', 1 ≤ c' →
      (∀ y, 12 ≤ y → y ≤ properDivsSum (3 ^ 2 * 5 ^ 1 * 17 ^ c' * 19 ^ 1) - 12 →
        repNat (3 ^ 2 * 5 ^ 1 * 17 ^ c' * 19 ^ 1).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ 2 * 5 ^ 1 * 17 ^ c' * 19 ^ 1) →
        ∃ i, repNat (3 ^ 2 * 5 ^ 1 * 17 ^ c' * 19 ^ 1).properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    intro c' hc'
    induction c' with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero => rw [hB0_eq]; exact ⟨hcov0, hgap0⟩
      | succ m' =>
        obtain ⟨hc1, hg1⟩ := ih (by omega)
        let Bcur := 3 ^ 2 * 5 ^ 1 * 17 ^ (m' + 1) * 19 ^ 1
        have hpos : 0 < Bcur := by positivity
        have hdvd : 14535 ∣ Bcur := by
          rw [← hB0_eq]; dsimp [Bcur]
          exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_left _ (by simpa using pow_dvd_pow 17 (show 1 ≤ m' + 1 by omega))) _
        have hrat := hratio Bcur hdvd hpos
        have hres := lift_dividing_prime_step (by decide : Nat.Prime 17) (by decide : 0 < 855)
          (by decide : ¬ 17 ∣ 855) (show 1 ≤ m' + 1 by omega)
          (show Bcur = 17 ^ (m' + 1) * 855 by dsimp [Bcur]; ring) (by decide) (by decide)
          (by omega) hc1 hg1 hrat.1 hrel19'
          (by rw [← hP19_eq]; exact (Iff.of_eq Nat.ble_eq).mp hfin19)
        have hEq : 17 * Bcur = 3 ^ 2 * 5 ^ 1 * 17 ^ (m' + 2) * 19 ^ 1 := by
          dsimp [Bcur]; rw [pow_succ]; ring
        rwa [hEq] at hres
  have hrel17_all : ∀ t : ℕ, HasRelGap (3 ^ 2 * 5 ^ 1 * 17 ^ (t + 1)) (13545 - 2 * 12) (19 * 14535) := by
    intro t
    induction t with
    | zero => simpa [show 3 ^ 2 * 5 ^ 1 * 17 ^ 1 = 765 by decide] using hrel17_0
    | succ t ih =>
      have hpos : 0 < 3 ^ 2 * 5 ^ 1 * 17 ^ (t + 1) := by positivity
      have hdvd : 765 ∣ 3 ^ 2 * 5 ^ 1 * 17 ^ (t + 1) := by
        rw [show (765 : ℕ) = 3 ^ 2 * 5 ^ 1 * 17 ^ 1 by decide]
        exact Nat.mul_dvd_mul_left _ (pow_dvd_pow 17 (show 1 ≤ t + 1 by omega))
      have hmo := properDivsSum_ratio_mono (by decide) hpos hdvd
      have hmu : 19 * 14535 * 765 ≤ (13545 - 2 * 12) * (17 * 765) + 19 * 14535 * properDivsSum 765 := by
        rw [← hP17_eq]; exact (Iff.of_eq Nat.ble_eq).mp hmu17
      have hdef : 19 * 14535 * (3 ^ 2 * 5 ^ 1 * 17 ^ (t + 1)) ≤
          (13545 - 2 * 12) * (17 * (3 ^ 2 * 5 ^ 1 * 17 ^ (t + 1))) +
          19 * 14535 * properDivsSum (3 ^ 2 * 5 ^ 1 * 17 ^ (t + 1)) := by
        have h1 := Nat.mul_le_mul_right (3 ^ 2 * 5 ^ 1 * 17 ^ (t + 1)) hmu
        have h2 := Nat.mul_le_mul_left (19 * 14535) hmo
        apply Nat.le_of_mul_le_mul_right _ (by decide : 0 < 765)
        linarith
      have h := ih.mul_prime (by decide : Nat.Prime 17) hpos hdef
      have hEq : 17 * (3 ^ 2 * 5 ^ 1 * 17 ^ (t + 1)) = 3 ^ 2 * 5 ^ 1 * 17 ^ (t + 2) := by rw [pow_succ]; ring
      rwa [hEq] at h
  -- Step 2: lift 19 from 1 to d
  have hstep2 : ∀ d', 1 ≤ d' →
      (∀ y, 12 ≤ y → y ≤ properDivsSum (3 ^ 2 * 5 ^ 1 * 17 ^ c * 19 ^ d') - 12 →
        repNat (3 ^ 2 * 5 ^ 1 * 17 ^ c * 19 ^ d').properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ 2 * 5 ^ 1 * 17 ^ c * 19 ^ d') →
        ∃ i, repNat (3 ^ 2 * 5 ^ 1 * 17 ^ c * 19 ^ d').properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    intro d' hd'
    induction d' with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero => exact hstep1 c hc
      | succ m' =>
        obtain ⟨hc2, hg2⟩ := ih (by omega)
        let Bcur := 3 ^ 2 * 5 ^ 1 * 17 ^ c * 19 ^ (m' + 1)
        let u17 := 3 ^ 2 * 5 ^ 1 * 17 ^ c
        have hu_pos : 0 < u17 := by positivity
        have hpos : 0 < Bcur := by positivity
        have hdvd : 14535 ∣ Bcur := by
          rw [← hB0_eq]; dsimp [Bcur]
          exact Nat.mul_dvd_mul (Nat.mul_dvd_mul_left _ (by simpa using pow_dvd_pow 17 hc))
            (by simpa using pow_dvd_pow 19 (show 1 ≤ m' + 1 by omega))
        have hrat := hratio Bcur hdvd hpos
        have h19p : Nat.Prime 19 := by decide
        have hcop19 : ¬ 19 ∣ u17 := by
          intro h; dsimp [u17] at h
          rcases h19p.dvd_mul.mp h with h45 | h17
          · exact absurd h45 (by decide)
          · exact absurd (h19p.dvd_of_dvd_pow h17) (by decide)
        have hrelc : HasRelGap u17 (13545 - 2 * 12) (19 * 14535) := by
          have := hrel17_all (c - 1)
          rwa [show c - 1 + 1 = c by omega] at this
        have hfin17c : 14535 * u17 ≤ (13545 - 2 * 12) * u17 + 19 * 14535 * properDivsSum u17 := by
          have hdvd_u : 765 ∣ u17 := by
            rw [show (765 : ℕ) = 3 ^ 2 * 5 ^ 1 * 17 ^ 1 by decide]
            exact Nat.mul_dvd_mul_left _ (pow_dvd_pow 17 hc)
          have hmo := properDivsSum_ratio_mono (by decide) hu_pos hdvd_u
          have hf0 : 14535 * 765 ≤ (13545 - 2 * 12) * 765 + 19 * 14535 * properDivsSum 765 := by
            rw [← hP17_eq]; exact (Iff.of_eq Nat.ble_eq).mp hfin17
          have h1 := Nat.mul_le_mul_right u17 hf0
          have h2 := Nat.mul_le_mul_left (19 * 14535) hmo
          apply Nat.le_of_mul_le_mul_right _ (by decide : 0 < 765)
          linarith
        have hres := lift_dividing_prime_step h19p hu_pos hcop19 (show 1 ≤ m' + 1 by omega)
          (show Bcur = 19 ^ (m' + 1) * u17 by dsimp [Bcur, u17]; ring) (by decide) (by decide)
          (by omega) hc2 hg2 hrat.1 hrelc hfin17c
        have hEq : 19 * Bcur = 3 ^ 2 * 5 ^ 1 * 17 ^ c * 19 ^ (m' + 2) := by
          dsimp [Bcur]; rw [pow_succ]; ring
        rwa [hEq] at hres
  let B := 3 ^ 2 * 5 ^ 1 * 17 ^ c * 19 ^ d
  have hBpos : 0 < B := by positivity
  have hdvd : 14535 ∣ B := by
    rw [← hB0_eq]; dsimp [B]
    exact Nat.mul_dvd_mul (Nat.mul_dvd_mul_left _ (by simpa using pow_dvd_pow 17 hc))
      (by simpa using pow_dvd_pow 19 hd)
  have hrat := hratio B hdvd hBpos
  have hsub : (14535 : ℕ).properDivisors ⊆ B.properDivisors := by
    intro x hx
    obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp hx
    exact Nat.mem_properDivisors.mpr ⟨h1.trans hdvd, lt_of_lt_of_le h2 (Nat.le_of_dvd hBpos hdvd)⟩
  have hP0_le : 13545 ≤ properDivsSum B := hrat.2
  obtain ⟨hcovB, hgapB⟩ := hstep2 d hd
  refine ⟨hcovB, hgapB, ?_, by change 5 * (2 * 12 + 24) ≤ properDivsSum B; omega⟩
  intro x hx1 hx2 hx3
  obtain ⟨s, hs, hsum⟩ := hmod0 x hx1 hx2 hx3
  exact ⟨s, hs.trans hsub, hsum⟩

end CoreLift

/- ## Section 3: Pure-Nat branch-and-bound verifiers for small excess and D >= 2 -/

section SmallExcess

private def leOpt (x : ℕ) : Option ℕ → Prop
  | none => True
  | some y => x ≤ y

private def minOpt : Option ℕ → ℕ → Option ℕ
  | none, y => some y
  | some x, y => some (min x y)

private lemma leOpt_minOpt {x y : ℕ} {o : Option ℕ} (ho : leOpt x o) (hy : x ≤ y) :
    leOpt x (minOpt o y) := by
  cases o with
  | none => exact hy
  | some z => exact le_min ho hy

private lemma ite_true_or {c X : Bool} (h : (if c = true then true else X) = true) :
    c = true ∨ X = true := by
  revert h; cases c <;> cases X <;> decide

private lemma ite_not_false {b X : Bool} (h : (if (!b) = true then false else X) = true) :
    b = true ∧ X = true := by
  revert h; cases b <;> cases X <;> decide

private lemma optBle_false {q x : ℕ} {o : Option ℕ}
    (h : (match o with | some v => Nat.ble (v + 1) x | none => false) = true)
    (ho : leOpt q o) (hx : x ≤ q) : False := by
  cases o with
  | none => simp at h
  | some v =>
    have h1 : v + 1 ≤ x := by
      first
        | exact (Iff.of_eq Nat.ble_eq).mp h
        | simpa using h
    have h2 : q ≤ v := ho
    omega

private def hiNum (p : ℕ) : Option ℕ → ℕ
  | none => p
  | some hi => ppSum p hi

private def hiDen (p : ℕ) : Option ℕ → ℕ
  | none => p - 1
  | some hi => p ^ hi

private lemma hiDen_pos {p : ℕ} (hp : 2 ≤ p) (o : Option ℕ) : 0 < hiDen p o := by
  cases o with
  | none => simp [hiDen]; omega
  | some hi => simp [hiDen]; exact pow_pos (by omega) hi

private lemma ppSum_le_hi {p a : ℕ} (hp : 2 ≤ p) {o : Option ℕ} (ho : leOpt a o) :
    ppSum p a * hiDen p o ≤ hiNum p o * p ^ a := by
  cases o with
  | none => exact (ppSum_lt_lim hp).le
  | some hi => exact ppSum_mono_exp hp ho

private lemma ppSum_le_hi_prime {q0 q e : ℕ} (hq0 : 2 ≤ q0) (hq0q : q0 ≤ q)
    {o : Option ℕ} (ho : leOpt e o) :
    ppSum q e * hiDen q0 o ≤ hiNum q0 o * q ^ e := by
  cases o with
  | none =>
    simp only [hiNum, hiDen]
    have h1 := (ppSum_lt_lim (p := q) (e := e) (by omega)).le
    have h2 : q * (q0 - 1) ≤ q0 * (q - 1) := by
      zify [show 1 ≤ q0 by omega, show 1 ≤ q by omega]; nlinarith
    apply Nat.le_of_mul_le_mul_right _ (show 0 < q - 1 by omega)
    calc ppSum q e * (q0 - 1) * (q - 1) = (ppSum q e * (q - 1)) * (q0 - 1) := by ring
      _ ≤ (q * q ^ e) * (q0 - 1) := Nat.mul_le_mul_right _ h1
      _ = (q * (q0 - 1)) * q ^ e := by ring
      _ ≤ (q0 * (q - 1)) * q ^ e := Nat.mul_le_mul_right _ h2
      _ = q0 * q ^ e * (q - 1) := by ring
  | some e1 =>
    simp only [hiNum, hiDen]
    have h1 := ppSum_mono_exp (p := q) (a := e) (b := e1) (by omega) ho
    have h2 := ppSum_anti_prime (p := q0) (q := q) (e := e1) (by omega) hq0q
    apply Nat.le_of_mul_le_mul_right _ (pow_pos (show 0 < q by omega) e1)
    calc ppSum q e * q0 ^ e1 * q ^ e1 = (ppSum q e * q ^ e1) * q0 ^ e1 := by ring
      _ ≤ (ppSum q e1 * q ^ e) * q0 ^ e1 := Nat.mul_le_mul_right _ h1
      _ = (ppSum q e1 * q0 ^ e1) * q ^ e := by ring
      _ ≤ (ppSum q0 e1 * q ^ e1) * q ^ e := Nat.mul_le_mul_right _ h2
      _ = ppSum q0 e1 * q ^ e * q ^ e1 := by ring

private def smallPs : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

private def isCompSmall (x : ℕ) : Bool :=
  smallPs.any (fun sp => Nat.ble (sp + 1) x && Nat.beq (x % sp) 0)

private lemma not_prime_of_isCompSmall {x : ℕ} (h : isCompSmall x = true) : ¬ x.Prime := by
  simp only [isCompSmall, List.any_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨sp, hsp, hgt, hmod⟩ := h
  have hsp2 : 2 ≤ sp := by
    simp only [smallPs, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro hp
  have hdvd : sp ∣ x := Nat.dvd_of_mod_eq_zero hmod
  rcases hp.eq_one_or_self_of_dvd sp hdvd with h1 | h2 <;> omega

private def skipUp : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x => if isCompSmall x then skipUp fuel (x + 1) else x

private lemma skipUp_le {q : ℕ} (hq : q.Prime) : ∀ (fuel x : ℕ), x ≤ q → skipUp fuel x ≤ q
  | 0, _, h => h
  | fuel + 1, x, h => by
    simp only [skipUp]
    cases hc : isCompSmall x
    · exact h
    · have hne : x ≠ q := fun heq => not_prime_of_isCompSmall hc (heq ▸ hq)
      exact skipUp_le hq fuel (x + 1) (by omega)

private lemma le_skipUp : ∀ (fuel x : ℕ), x ≤ skipUp fuel x
  | 0, _ => le_rfl
  | fuel + 1, x => by
    simp only [skipUp]; split_ifs
    · exact le_trans (Nat.le_succ x) (le_skipUp fuel (x + 1))
    · exact le_rfl

private def skipDn : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x => if Nat.ble 2 x && isCompSmall x then skipDn fuel (x - 1) else x

private lemma le_skipDn {q : ℕ} (hq : q.Prime) : ∀ (fuel x : ℕ), q ≤ x → q ≤ skipDn fuel x
  | 0, _, h => h
  | fuel + 1, x, h => by
    simp only [skipDn]
    cases h2 : Nat.ble 2 x
    · simpa [h2] using h
    · cases hc : isCompSmall x
      · simpa [h2, hc] using h
      · simp only [Bool.and_self, ↓reduceIte]
        have hne : x ≠ q := fun heq => not_prime_of_isCompSmall hc (heq ▸ hq)
        exact le_skipDn hq fuel (x - 1) (by omega)

private def gapRatioGt (p1 lo1 : ℕ) (hi1 : Option ℕ) (p2 lo2 : ℕ) (hi2 : Option ℕ) : Bool :=
  let n1 := hiNum p1 hi1 * p1 ^ lo1
  let d1 := hiDen p1 hi1 * ppSum p1 lo1
  let n2 := hiNum p2 hi2 * p2 ^ lo2
  let d2 := hiDen p2 hi2 * ppSum p2 lo2
  Nat.ble (n2 * d1 + 1) (n1 * d2)

private def canSplit (lo : ℕ) : Option ℕ → Bool
  | none => true
  | some hi => Nat.ble (lo + 1) hi

private def pickDim4 (r p a0 : ℕ) (a1 : Option ℕ) (b0 : ℕ) (b1 : Option ℕ)
    (c0 : ℕ) (c1 : Option ℕ) (d0 : ℕ) (d1 : Option ℕ) : ℕ :=
  let cands : List (ℕ × ℕ × ℕ × Option ℕ) :=
    (if canSplit a0 a1 then [(0, 3, a0, a1)] else []) ++
    (if canSplit b0 b1 then [(1, 5, b0, b1)] else []) ++
    (if canSplit c0 c1 then [(2, r, c0, c1)] else []) ++
    (if canSplit d0 d1 then [(3, p, d0, d1)] else [])
  match cands with
  | [] => 0
  | h :: t =>
    let best := t.foldl (fun acc cur =>
      if gapRatioGt cur.2.1 cur.2.2.1 cur.2.2.2 acc.2.1 acc.2.2.1 acc.2.2.2 then cur else acc) h
    best.1

private def pickDim3 (r a0 : ℕ) (a1 : Option ℕ) (b0 : ℕ) (b1 : Option ℕ)
    (c0 : ℕ) (c1 : Option ℕ) : ℕ :=
  let cands : List (ℕ × ℕ × ℕ × Option ℕ) :=
    (if canSplit a0 a1 then [(0, 3, a0, a1)] else []) ++
    (if canSplit b0 b1 then [(1, 5, b0, b1)] else []) ++
    (if canSplit c0 c1 then [(2, r, c0, c1)] else [])
  match cands with
  | [] => 0
  | h :: t =>
    let best := t.foldl (fun acc cur =>
      if gapRatioGt cur.2.1 cur.2.2.1 cur.2.2.2 acc.2.1 acc.2.2.1 acc.2.2.2 then cur else acc) h
    best.1

private lemma ppSum_mod3_of_prime_mod3 {p e : ℕ} :
    (p % 3 = 2 → e % 2 = 1 → ppSum p e % 3 = 0) ∧
    (p % 3 = 1 → e % 3 = 2 → ppSum p e % 3 = 0) := by
  constructor
  · intro hp he
    have h : ∀ k : ℕ, ppSum p (2 * k + 1) % 3 = 0 := by
      intro k
      induction k with
      | zero => simp [ppSum]; omega
      | succ k ih =>
        have h1 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
        rw [h1, ppSum, ppSum]
        have hpow : p ^ (2 * k + 1 + 1 + 1) = p ^ (2 * k + 1 + 1) * p := pow_succ _ _
        rw [hpow]
        have hmod : (p ^ (2 * k + 1 + 1) + p ^ (2 * k + 1 + 1) * p) % 3 = 0 := by
          have : p ^ (2 * k + 1 + 1) + p ^ (2 * k + 1 + 1) * p = p ^ (2 * k + 1 + 1) * (p + 1) := by ring
          rw [this, Nat.mul_mod]
          have : (p + 1) % 3 = 0 := by omega
          simp [this]
        omega
    obtain ⟨k, hk⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
    rw [hk]; exact h k
  · intro hp he
    have hpow : ∀ k : ℕ, p ^ k % 3 = 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, Nat.mul_mod, ih, hp]
    have hsum : ∀ k : ℕ, ppSum p k % 3 = (k + 1) % 3 := by
      intro k
      induction k with
      | zero => simp [ppSum]
      | succ k ih =>
        rw [ppSum, Nat.add_mod, ih, hpow (k + 1)]
        omega
    rw [hsum e]; omega

-- Fix the e0 % 2 = 0 condition cleanly by making it an explicit hypothesis!
private lemma exp_step_of_not_dvd3' {p e e0 : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hno3 : ppSum p e % 3 ≠ 0) (he_lo : e0 ≤ e) (hne : e ≠ e0)
    (he0_even : p % 3 = 2 → e0 % 2 = 0) :
    (if Nat.beq (p % 3) 2 then e0 + 2
     else if Nat.beq (e0 % 3) 1 then e0 + 2 else e0 + 1) ≤ e := by
  have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have hnd : ¬ 3 ∣ p := fun h => by
      rcases hp.eq_one_or_self_of_dvd 3 h with h1 | h2 <;> omega
    omega
  split_ifs with h1 h2
  · have hp2 : p % 3 = 2 := (Iff.of_eq Nat.beq_eq).mp h1
    have he_even : e % 2 = 0 := by
      by_contra hodd
      exact hno3 (ppSum_mod3_of_prime_mod3.1 hp2 (by omega))
    have := he0_even hp2
    omega
  · have hp1 : p % 3 = 1 := by
      have hne2 : p % 3 ≠ 2 := fun h => h1 ((Iff.of_eq Nat.beq_eq).mpr h)
      omega
    have he01 : e0 % 3 = 1 := (Iff.of_eq Nat.beq_eq).mp h2
    have hne2 : e % 3 ≠ 2 := fun h => hno3 (ppSum_mod3_of_prime_mod3.2 hp1 h)
    omega
  · omega

private lemma abund_iff_nat {m : ℕ} (hm : 0 < m) : m.Abundant ↔ 2 * m < sigma 1 m := by
  rw [Nat.abundant_iff_two_lt_abundancyIndex, Nat.abundancyIndex,
      lt_div_iff₀ (by exact_mod_cast hm), ← ArithmeticFunction.sigma_one_apply]
  exact_mod_cast Iff.rfl

private lemma defic_iff_nat {m : ℕ} (_hm : 0 < m) : m.Deficient ↔ sigma 1 m < 2 * m := by
  have h := properDivsSum_eq_sigma_sub (n := m)
  change properDivsSum m < m ↔ sigma 1 m < 2 * m
  omega

/- ### 3a. Pure-Nat verifier `checkD2` for `2 <= 2*B - sigma 1 B` on even-exponent 4-prime bases -/

private def checkD2 (fuel r p a0 : ℕ) (a1 : Option ℕ) (b0 : ℕ) (b1 : Option ℕ)
    (c0 : ℕ) (c1 : Option ℕ) (d0 : ℕ) (d1 : Option ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    let lN := ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * ppSum p d0
    let lD := 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0
    if Nat.ble (2 * lD + 1) lN then true
    else
      let hN := hiNum 3 a1 * hiNum 5 b1 * hiNum r c1 * hiNum p d1
      let hD := hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1
      if Nat.ble (hN + 1) (2 * hD) && Nat.ble (2 * hD) (lD * (2 * hD - hN)) then true
      else if (a1 == some a0) && (b1 == some b0) && (c1 == some c0) && (d1 == some d0) then
        Nat.ble (2 * lD) lN || Nat.ble (lN + 2) (2 * lD)
      else
        match pickDim4 r p a0 a1 b0 b1 c0 c1 d0 d1 with
        | 0 => checkD2 fuel r p a0 (some a0) b0 b1 c0 c1 d0 d1 &&
               checkD2 fuel r p (a0 + 2) a1 b0 b1 c0 c1 d0 d1
        | 1 => checkD2 fuel r p a0 a1 b0 (some b0) c0 c1 d0 d1 &&
               checkD2 fuel r p a0 a1 (b0 + 2) b1 c0 c1 d0 d1
        | 2 => checkD2 fuel r p a0 a1 b0 b1 c0 (some c0) d0 d1 &&
               checkD2 fuel r p a0 a1 b0 b1 (c0 + 2) c1 d0 d1
        | _ => checkD2 fuel r p a0 a1 b0 b1 c0 c1 d0 (some d0) &&
               checkD2 fuel r p a0 a1 b0 b1 c0 c1 (d0 + 2) d1

private lemma checkD2_sound :
    ∀ (fuel r p a0 : ℕ) (a1 : Option ℕ) (b0 : ℕ) (b1 : Option ℕ)
      (c0 : ℕ) (c1 : Option ℕ) (d0 : ℕ) (d1 : Option ℕ) (a b c d : ℕ),
      r.Prime → p.Prime → 5 < r → r < p →
      a0 ≤ a → leOpt a a1 → a % 2 = 0 → a0 % 2 = 0 →
      b0 ≤ b → leOpt b b1 → b % 2 = 0 → b0 % 2 = 0 →
      c0 ≤ c → leOpt c c1 → c % 2 = 0 → c0 % 2 = 0 →
      d0 ≤ d → leOpt d d1 → d % 2 = 0 → d0 % 2 = 0 →
      sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d) < 2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d) →
      checkD2 fuel r p a0 a1 b0 b1 c0 c1 d0 d1 = true →
      2 ≤ 2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d) - sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hok => by
      simp [checkD2] at hok
  | fuel + 1, r, p, a0, a1, b0, b1, c0, c1, d0, d1, a, b, c, d,
    hr, hp, h5r, hrp, ha0, ha1, hae, ha0e, hb0, hb1, hbe, hb0e, hc0, hc1, hce, hc0e, hd0, hd1, hde, hd0e, hdef, hok => by
    have hsig := sigma_four_primes hr hp h5r hrp (a := a) (b := b) (c := c) (d := d)
    set B := 3 ^ a * 5 ^ b * r ^ c * p ^ d
    set sB := ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d
    rw [hsig] at hdef ⊢
    change sB < 2 * B at hdef
    change 2 ≤ 2 * B - sB
    have hBpos : 0 < B := by have := hr.pos; have := hp.pos; positivity
    let lN := ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * ppSum p d0
    let lD := 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0
    have hlDpos : 0 < lD := by have := hr.pos; have := hp.pos; positivity
    have hlo_ratio : lN * B ≤ sB * lD := by
      have m3 := ppSum_mono_exp (p := 3) (by decide) ha0
      have m5 := ppSum_mono_exp (p := 5) (by decide) hb0
      have mr := ppSum_mono_exp (p := r) hr.two_le hc0
      have mp := ppSum_mono_exp (p := p) hp.two_le hd0
      have m12 := Nat.mul_le_mul m3 m5
      have m34 := Nat.mul_le_mul mr mp
      have m1234 := Nat.mul_le_mul m12 m34
      dsimp only [lN, lD, B, sB]
      linarith [m1234]
    have hlD_le_B : lD ≤ B := by
      dsimp [lD, B]
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) ha0)
        (pow_le_pow_right₀ (by decide) hb0)) (pow_le_pow_right₀ hr.one_lt.le hc0))
        (pow_le_pow_right₀ hp.one_lt.le hd0)
    simp only [checkD2] at hok
    by_cases h1 : Nat.ble (2 * lD + 1) lN = true
    · have hgt : 2 * lD < lN := by have := (Iff.of_eq Nat.ble_eq).mp h1; omega
      have : 2 * lD * B < lN * B := Nat.mul_lt_mul_of_pos_right hgt hBpos
      have : sB * lD < 2 * B * lD := Nat.mul_lt_mul_of_pos_right hdef hlDpos
      linarith
    · rw [Bool.eq_false_iff.mpr h1] at hok
      simp only [Bool.false_eq_true, ↓reduceIte] at hok
      let hN := hiNum 3 a1 * hiNum 5 b1 * hiNum r c1 * hiNum p d1
      let hD := hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1
      have hhDpos : 0 < hD := by
        have := hiDen_pos (p := 3) (by decide) a1
        have := hiDen_pos (p := 5) (by decide) b1
        have := hiDen_pos (p := r) hr.two_le c1
        have := hiDen_pos (p := p) hp.two_le d1
        positivity
      have hhi_ratio : sB * hD ≤ hN * B := by
        have u3 := ppSum_le_hi (p := 3) (by decide) ha1
        have u5 := ppSum_le_hi (p := 5) (by decide) hb1
        have ur := ppSum_le_hi (p := r) hr.two_le hc1
        have up := ppSum_le_hi (p := p) hp.two_le hd1
        have u12 := Nat.mul_le_mul u3 u5
        have u34 := Nat.mul_le_mul ur up
        have u1234 := Nat.mul_le_mul u12 u34
        dsimp only [hN, hD, B, sB]
        linarith [u1234]
      by_cases h2 : (Nat.ble (hN + 1) (2 * hD) && Nat.ble (2 * hD) (lD * (2 * hD - hN))) = true
      · rw [Bool.and_eq_true] at h2
        have hlt : hN < 2 * hD := by have := (Iff.of_eq Nat.ble_eq).mp h2.1; omega
        have hgap : 2 * hD ≤ lD * (2 * hD - hN) := (Iff.of_eq Nat.ble_eq).mp h2.2
        have hmul : 2 * hD ≤ B * (2 * hD - hN) :=
          le_trans hgap (Nat.mul_le_mul_right _ hlD_le_B)
        have hdiff : (2 * B - sB) * hD ≥ 2 * hD := by
          zify [hdef.le, hlt.le] at hhi_ratio hmul ⊢
          nlinarith
        exact Nat.le_of_mul_le_mul_right hdiff hhDpos
      · rw [Bool.eq_false_iff.mpr h2] at hok
        simp only [Bool.false_eq_true, ↓reduceIte] at hok
        by_cases h3 : ((a1 == some a0) && (b1 == some b0) && (c1 == some c0) && (d1 == some d0)) = true
        · rw [h3] at hok; simp only [↓reduceIte] at hok
          repeat rw [Bool.and_eq_true] at h3
          rcases h3 with ⟨⟨⟨ea, eb⟩, ec⟩, ed⟩
          have ea' : a1 = some a0 := by simpa using ea
          have eb' : b1 = some b0 := by simpa using eb
          have ec' : c1 = some c0 := by simpa using ec
          have ed' : d1 = some d0 := by simpa using ed
          rw [ea'] at ha1; rw [eb'] at hb1; rw [ec'] at hc1; rw [ed'] at hd1
          have ha_eq : a = a0 := le_antisymm ha1 ha0
          have hb_eq : b = b0 := le_antisymm hb1 hb0
          have hc_eq : c = c0 := le_antisymm hc1 hc0
          have hd_eq : d = d0 := le_antisymm hd1 hd0
          subst ha_eq; subst hb_eq; subst hc_eq; subst hd_eq
          rw [Bool.or_eq_true] at hok
          rcases hok with hge | hok2
          · have := (Iff.of_eq Nat.ble_eq).mp hge; omega
          · have := (Iff.of_eq Nat.ble_eq).mp hok2; omega
        · rw [Bool.eq_false_iff.mpr h3] at hok
          simp only [Bool.false_eq_true, ↓reduceIte] at hok
          have hdef' : sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d) < 2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d) := by
            rwa [hsig]
          suffices H : 2 ≤ 2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d) - sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d) by
            rw [hsig] at H; exact H
          split at hok
          · rw [Bool.and_eq_true] at hok
            by_cases heq : a = a0
            · exact checkD2_sound fuel r p a0 (some a0) b0 b1 c0 c1 d0 d1 a b c d
                hr hp h5r hrp ha0 (show a ≤ a0 by omega) hae ha0e hb0 hb1 hbe hb0e hc0 hc1 hce hc0e hd0 hd1 hde hd0e
                hdef' hok.1
            · exact checkD2_sound fuel r p (a0 + 2) a1 b0 b1 c0 c1 d0 d1 a b c d
                hr hp h5r hrp (by omega) ha1 hae (by omega) hb0 hb1 hbe hb0e hc0 hc1 hce hc0e hd0 hd1 hde hd0e
                hdef' hok.2
          · rw [Bool.and_eq_true] at hok
            by_cases heq : b = b0
            · exact checkD2_sound fuel r p a0 a1 b0 (some b0) c0 c1 d0 d1 a b c d
                hr hp h5r hrp ha0 ha1 hae ha0e hb0 (show b ≤ b0 by omega) hbe hb0e hc0 hc1 hce hc0e hd0 hd1 hde hd0e
                hdef' hok.1
            · exact checkD2_sound fuel r p a0 a1 (b0 + 2) b1 c0 c1 d0 d1 a b c d
                hr hp h5r hrp ha0 ha1 hae ha0e (by omega) hb1 hbe (by omega) hc0 hc1 hce hc0e hd0 hd1 hde hd0e
                hdef' hok.2
          · rw [Bool.and_eq_true] at hok
            by_cases heq : c = c0
            · exact checkD2_sound fuel r p a0 a1 b0 b1 c0 (some c0) d0 d1 a b c d
                hr hp h5r hrp ha0 ha1 hae ha0e hb0 hb1 hbe hb0e hc0 (show c ≤ c0 by omega) hce hc0e hd0 hd1 hde hd0e
                hdef' hok.1
            · exact checkD2_sound fuel r p a0 a1 b0 b1 (c0 + 2) c1 d0 d1 a b c d
                hr hp h5r hrp ha0 ha1 hae ha0e hb0 hb1 hbe hb0e (by omega) hc1 hce (by omega) hd0 hd1 hde hd0e
                hdef' hok.2
          · rw [Bool.and_eq_true] at hok
            by_cases heq : d = d0
            · exact checkD2_sound fuel r p a0 a1 b0 b1 c0 c1 d0 (some d0) a b c d
                hr hp h5r hrp ha0 ha1 hae ha0e hb0 hb1 hbe hb0e hc0 hc1 hce hc0e hd0 (show d ≤ d0 by omega) hde hd0e
                hdef' hok.1
            · exact checkD2_sound fuel r p a0 a1 b0 b1 c0 c1 (d0 + 2) d1 a b c d
                hr hp h5r hrp ha0 ha1 hae ha0e hb0 hb1 hbe hb0e hc0 hc1 hce hc0e (by omega) hd1 hde (by omega)
                hdef' hok.2

/- ### 3b. Pure-Nat verifier `checkBox4` for omega = 4 small excess -/

private def findMinExp : ℕ → ℕ → ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _, _, _ => none
  | fuel + 1, sB, B, p, d =>
    if Nat.ble (2 * B * p ^ d + 1) (sB * ppSum p d) then some d
    else findMinExp fuel sB B p (d + 1)

private lemma findMinExp_sound :
    ∀ (fuel sB B p d0 d : ℕ),
      findMinExp fuel sB B p d0 = some d →
      d0 ≤ d ∧ 2 * B * p ^ d < sB * ppSum p d ∧
      ∀ k, d0 ≤ k → k < d → sB * ppSum p k ≤ 2 * B * p ^ k
  | 0, _, _, _, _, _, h => by simp [findMinExp] at h
  | fuel + 1, sB, B, p, d0, d, h => by
    simp only [findMinExp] at h
    cases hle : Nat.ble (2 * B * p ^ d0 + 1) (sB * ppSum p d0)
    · rw [hle] at h
      obtain ⟨h1, h2, h3⟩ := findMinExp_sound fuel sB B p (d0 + 1) d h
      refine ⟨by omega, h2, ?_⟩
      intro k hk1 hk2
      by_cases heq : k = d0
      · subst heq
        by_contra hgt
        have : Nat.ble (2 * B * p ^ k + 1) (sB * ppSum p k) = true := (Iff.of_eq Nat.ble_eq).mpr (by omega)
        rw [hle] at this; exact Bool.noConfusion this
      · exact h3 k (by omega) hk2
    · rw [hle] at h
      have heq : d0 = d := Option.some.inj h
      subst heq
      have hgt := (Iff.of_eq Nat.ble_eq).mp hle
      exact ⟨le_rfl, by omega, fun k hk1 hk2 => by omega⟩

private def checkFixedB3 (r p a0 b0 c0 d0 : ℕ) (d1 : Option ℕ) (Lcut : ℕ) : Bool :=
  let B := 3 ^ a0 * 5 ^ b0 * r ^ c0
  let sB := ppSum 3 a0 * ppSum 5 b0 * ppSum r c0
  if Nat.ble (2 * B) sB then true
  else if Nat.ble (2 * B * (p - 1)) (sB * p) then
    match findMinExp 50 sB B p d0 with
    | none => false
    | some d =>
      match d1 with
      | some d1v =>
        if Nat.ble (d1v + 1) d then true
        else
          Nat.ble (2 * B * p ^ d + Lcut) (sB * ppSum p d) ||
          Nat.beq ((sB * ppSum p d) % 3) 0
      | none =>
        Nat.ble (2 * B * p ^ d + Lcut) (sB * ppSum p d) ||
        Nat.beq ((sB * ppSum p d) % 3) 0
  else true

private lemma checkFixedB3_sound {r p a0 b0 c0 d0 d Lcut : ℕ} {d1 : Option ℕ}
    (hr : r.Prime) (hp : p.Prime) (h5r : 5 < r) (hrp : r < p)
    (hd_pos : 1 ≤ d) (hd0 : d0 ≤ d) (hd1 : leOpt d d1)
    (hno3 : (ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * ppSum p d) % 3 ≠ 0)
    (hab : (3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d).Abundant)
    (hprim : ∀ x ∈ (3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d).properDivisors, x.Deficient)
    (hok : checkFixedB3 r p a0 b0 c0 d0 d1 Lcut = true) :
    Lcut ≤ sigma 1 (3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d) - 2 * (3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d) := by
  let B := 3 ^ a0 * 5 ^ b0 * r ^ c0
  let sB := ppSum 3 a0 * ppSum 5 b0 * ppSum r c0
  have hBpos : 0 < B := by have := hr.pos; positivity
  have hmpos : 0 < B * p ^ d := by have := hp.pos; positivity
  have hsig := sigma_four_primes hr hp h5r hrp (a := a0) (b := b0) (c := c0) (d := d)
  have hmab : 2 * B * p ^ d < sB * ppSum p d := by
    have h1 := (abund_iff_nat hmpos).mp hab
    rw [hsig] at h1; dsimp [B, sB] at h1 ⊢; linarith
  have hBdef : sB < 2 * B := by
    have hmem : B ∈ (B * p ^ d).properDivisors := Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right B _, lt_mul_of_one_lt_right hBpos (one_lt_pow₀ hp.one_lt (by omega))⟩
    have h1 := (defic_iff_nat hBpos).mp (hprim B hmem)
    rw [sigma_three_primes hr h5r] at h1; exact h1
  have hlim : 2 * B * (p - 1) < sB * p := by
    have h1 := ppSum_lt_lim (p := p) (e := d) hp.two_le
    have h2 : 2 * B * p ^ d * (p - 1) < sB * ppSum p d * (p - 1) :=
      Nat.mul_lt_mul_of_pos_right hmab (by have := hp.two_le; omega)
    have h3 : sB * ppSum p d * (p - 1) ≤ sB * (p * p ^ d) := by
      calc sB * ppSum p d * (p - 1) = sB * (ppSum p d * (p - 1)) := by ring
        _ ≤ sB * (p * p ^ d) := Nat.mul_le_mul_left sB h1.le
    have h4 : 2 * B * (p - 1) * p ^ d < sB * p * p ^ d := by linarith
    exact Nat.lt_of_mul_lt_mul_right h4
  dsimp only [checkFixedB3] at hok
  have hble1 : Nat.ble (2 * B) sB = false := by
    cases h : Nat.ble (2 * B) sB
    · rfl
    · have := (Iff.of_eq Nat.ble_eq).mp h; omega
  have hble2 : Nat.ble (2 * B * (p - 1)) (sB * p) = true := (Iff.of_eq Nat.ble_eq).mpr hlim.le
  rw [hble1, hble2] at hok
  simp only [Bool.false_eq_true, ↓reduceIte] at hok
  cases hfind : findMinExp 50 sB B p d0 with
  | none => rw [hfind] at hok; exact Bool.noConfusion hok
  | some d_min =>
    rw [hfind] at hok
    obtain ⟨hdmin_lo, hdmin_ab, hdmin_lt⟩ := findMinExp_sound 50 sB B p d0 d_min hfind
    have hd_ge : d_min ≤ d := by
      by_contra hlt
      have := hdmin_lt d hd0 (by omega)
      omega
    have hd_eq : d = d_min := by
      by_contra hne
      have hgt : d_min < d := by omega
      have hmem : B * p ^ d_min ∈ (B * p ^ d).properDivisors := Nat.mem_properDivisors.mpr
        ⟨Nat.mul_dvd_mul_left B (pow_dvd_pow p hgt.le),
         Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hp.one_lt hgt) hBpos⟩
      have hdef := (defic_iff_nat (mul_pos hBpos (pow_pos hp.pos _))).mp (hprim _ hmem)
      rw [sigma_four_primes hr hp h5r hrp] at hdef
      change sB * ppSum p d_min < 2 * (B * p ^ d_min) at hdef
      linarith
    subst hd_eq
    have hok' : (Nat.ble (2 * B * p ^ d + Lcut) (sB * ppSum p d) || Nat.beq ((sB * ppSum p d) % 3) 0) = true := by
      cases d1 with
      | none => exact hok
      | some d1v =>
        dsimp only at hok
        have hnotgt : Nat.ble (d1v + 1) d = false := by
          cases h : Nat.ble (d1v + 1) d
          · rfl
          · have := (Iff.of_eq Nat.ble_eq).mp h; change d ≤ d1v at hd1; omega
        rw [hnotgt] at hok; simpa using hok
    rw [Bool.or_eq_true] at hok'
    rcases hok' with hE | h3
    · have := (Iff.of_eq Nat.ble_eq).mp hE
      rw [hsig]; change Lcut ≤ sB * ppSum p d - 2 * (B * p ^ d)
      have : 2 * (B * p ^ d) = 2 * B * p ^ d := by ring
      omega
    · exfalso; exact hno3 ((Iff.of_eq Nat.beq_eq).mp h3)

private def checkBox4 (fuel r p a0 : ℕ) (a1 : Option ℕ) (b0 : ℕ) (b1 : Option ℕ)
    (c0 : ℕ) (c1 : Option ℕ) (d0 : ℕ) (d1 : Option ℕ) (Lcut : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    let hN := hiNum 3 a1 * hiNum 5 b1 * hiNum r c1 * hiNum p d1
    let hD := hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1
    if Nat.ble hN (2 * hD) then true
    else
      let lN3 := ppSum 3 a0 * ppSum 5 b0 * ppSum r c0
      let lD3 := 3 ^ a0 * 5 ^ b0 * r ^ c0
      if Nat.ble (2 * lD3 * p ^ d0 + 1) (lN3 * ppSum p d0) then
        checkFixedB3 r p a0 b0 c0 d0 (some d0) Lcut
      else if (a1 == some a0) && (b1 == some b0) && (c1 == some c0) then
        checkFixedB3 r p a0 b0 c0 d0 d1 Lcut
      else
        let (okCut, d1') :=
          if Nat.ble (2 * lD3 * hiDen p d1 + 1) (lN3 * hiNum p d1) then
            match findMinExp 50 lN3 lD3 p d0 with
            | none => (false, d1)
            | some dhit =>
              (checkFixedB3 r p a0 b0 c0 dhit (some dhit) Lcut, minOpt d1 (dhit - 1))
          else (true, d1)
        if !okCut then false
        else
          let hN' := hiNum 3 a1 * hiNum 5 b1 * hiNum r c1 * hiNum p d1'
          let hD' := hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1'
          if (match d1' with | some dv => Nat.ble (dv + 1) d0 | none => false) || Nat.ble hN' (2 * hD') then true
          else
            match pickDim3 r a0 a1 b0 b1 c0 c1 with
            | 0 => checkBox4 fuel r p a0 (some a0) b0 b1 c0 c1 d0 d1' Lcut &&
                   checkBox4 fuel r p (a0 + 1) a1 b0 b1 c0 c1 d0 d1' Lcut
            | 1 => checkBox4 fuel r p a0 a1 b0 (some b0) c0 c1 d0 d1' Lcut &&
                   checkBox4 fuel r p a0 a1 (b0 + 2) b1 c0 c1 d0 d1' Lcut
            | _ =>
              let step := if Nat.beq (r % 3) 2 then 2 else if Nat.beq (c0 % 3) 1 then 2 else 1
              checkBox4 fuel r p a0 a1 b0 b1 c0 (some c0) d0 d1' Lcut &&
              checkBox4 fuel r p a0 a1 b0 b1 (c0 + step) c1 d0 d1' Lcut

private lemma checkBox4_sound :
    ∀ (fuel r p a0 : ℕ) (a1 : Option ℕ) (b0 : ℕ) (b1 : Option ℕ)
      (c0 : ℕ) (c1 : Option ℕ) (d0 : ℕ) (d1 : Option ℕ) (Lcut a b c d : ℕ),
      r.Prime → p.Prime → 5 < r → r < p →
      a0 ≤ a → leOpt a a1 →
      b0 ≤ b → leOpt b b1 → b % 2 = 0 → b0 % 2 = 0 →
      c0 ≤ c → leOpt c c1 → (r % 3 = 2 → c0 % 2 = 0) →
      1 ≤ d → d0 ≤ d → leOpt d d1 →
      (ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d) % 3 ≠ 0 →
      (3 ^ a * 5 ^ b * r ^ c * p ^ d).Abundant →
      (∀ x ∈ (3 ^ a * 5 ^ b * r ^ c * p ^ d).properDivisors, x.Deficient) →
      checkBox4 fuel r p a0 a1 b0 b1 c0 c1 d0 d1 Lcut = true →
      Lcut ≤ sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d) - 2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hok => by
      simp [checkBox4] at hok
  | fuel + 1, r, p, a0, a1, b0, b1, c0, c1, d0, d1, Lcut, a, b, c, d,
    hr, hp, h5r, hrp, ha0, ha1, hb0, hb1, hbe, hb0e, hc0, hc1, hc0e, hd_pos, hd0, hd1, hno3, hab, hprim, hok => by
    have hsig := sigma_four_primes hr hp h5r hrp (a := a) (b := b) (c := c) (d := d)
    set M := 3 ^ a * 5 ^ b * r ^ c * p ^ d
    set sM := ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d
    have hMpos : 0 < M := by have := hr.pos; have := hp.pos; positivity
    have hMab : 2 * M < sM := by
      have h1 := (abund_iff_nat hMpos).mp hab; rwa [hsig] at h1
    have hup : ∀ {d1' : Option ℕ}, leOpt d d1' →
        sM * (hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1') ≤
        (hiNum 3 a1 * hiNum 5 b1 * hiNum r c1 * hiNum p d1') * M := by
      intro d1' hd1'
      have u3 := ppSum_le_hi (p := 3) (by decide) ha1
      have u5 := ppSum_le_hi (p := 5) (by decide) hb1
      have ur := ppSum_le_hi (p := r) hr.two_le hc1
      have up := ppSum_le_hi (p := p) hp.two_le hd1'
      have u12 := Nat.mul_le_mul u3 u5
      have u34 := Nat.mul_le_mul ur up
      have u1234 := Nat.mul_le_mul u12 u34
      dsimp only [M, sM]
      linarith [u1234]
    have hup_kill : ∀ {d1' : Option ℕ}, leOpt d d1' →
        hiNum 3 a1 * hiNum 5 b1 * hiNum r c1 * hiNum p d1' ≤
        2 * (hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1') → False := by
      intro d1' hd1' hle
      have hDpos : 0 < hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1' := by
        have := hiDen_pos (p := 3) (by decide) a1
        have := hiDen_pos (p := 5) (by decide) b1
        have := hiDen_pos (p := r) hr.two_le c1
        have := hiDen_pos (p := p) hp.two_le d1'
        positivity
      have h1 := hup hd1'
      have h2 := Nat.mul_lt_mul_of_pos_right hMab hDpos
      have h3 := Nat.mul_le_mul_right M hle
      linarith
    have hdom_eq : ∀ d_t : ℕ, d_t ≤ d →
        2 * (3 ^ a0 * 5 ^ b0 * r ^ c0) * p ^ d_t < ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * ppSum p d_t →
        a = a0 ∧ b = b0 ∧ c = c0 ∧ d = d_t := by
      intro d_t hdt hgt
      let M0 := 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d_t
      have hM0pos : 0 < M0 := by have := hr.pos; have := hp.pos; positivity
      have hM0dvd : M0 ∣ M := by
        dsimp [M0, M]
        exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 ha0) (pow_dvd_pow 5 hb0))
          (pow_dvd_pow r hc0)) (pow_dvd_pow p hdt)
      have hM0eq : M0 = M := by
        by_contra hne
        have hmem : M0 ∈ M.properDivisors := Nat.mem_properDivisors.mpr
          ⟨hM0dvd, lt_of_le_of_ne (Nat.le_of_dvd hMpos hM0dvd) hne⟩
        have hdef := (defic_iff_nat hM0pos).mp (hprim M0 hmem)
        rw [sigma_four_primes hr hp h5r hrp] at hdef
        dsimp [M0] at hdef; linarith
      have ha_eq : a = a0 := by
        by_contra hne
        have hlt : 3 ^ a0 < 3 ^ a := Nat.pow_lt_pow_right (by decide) (by omega)
        have hle1 : 5 ^ b0 * r ^ c0 * p ^ d_t ≤ 5 ^ b * r ^ c * p ^ d :=
          Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) hb0) (pow_le_pow_right₀ hr.one_lt.le hc0))
            (pow_le_pow_right₀ hp.one_lt.le hdt)
        have hltM : M0 < M := by
          dsimp [M0, M]
          calc 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d_t = 3 ^ a0 * (5 ^ b0 * r ^ c0 * p ^ d_t) := by ring
            _ < 3 ^ a * (5 ^ b * r ^ c * p ^ d) :=
                lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (by have := hr.pos; have := hp.pos; positivity))
                  (Nat.mul_le_mul_left _ hle1)
            _ = 3 ^ a * 5 ^ b * r ^ c * p ^ d := by ring
        omega
      have hb_eq : b = b0 := by
        by_contra hne
        have hlt : 5 ^ b0 < 5 ^ b := Nat.pow_lt_pow_right (by decide) (by omega)
        have hle1 : 3 ^ a0 * r ^ c0 * p ^ d_t ≤ 3 ^ a * r ^ c * p ^ d :=
          Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) ha0) (pow_le_pow_right₀ hr.one_lt.le hc0))
            (pow_le_pow_right₀ hp.one_lt.le hdt)
        have hltM : M0 < M := by
          dsimp [M0, M]
          calc 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d_t = 5 ^ b0 * (3 ^ a0 * r ^ c0 * p ^ d_t) := by ring
            _ < 5 ^ b * (3 ^ a * r ^ c * p ^ d) :=
                lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (by have := hr.pos; have := hp.pos; positivity))
                  (Nat.mul_le_mul_left _ hle1)
            _ = 3 ^ a * 5 ^ b * r ^ c * p ^ d := by ring
        omega
      have hc_eq : c = c0 := by
        by_contra hne
        have hlt : r ^ c0 < r ^ c := Nat.pow_lt_pow_right hr.one_lt (by omega)
        have hle1 : 3 ^ a0 * 5 ^ b0 * p ^ d_t ≤ 3 ^ a * 5 ^ b * p ^ d :=
          Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) ha0) (pow_le_pow_right₀ (by decide) hb0))
            (pow_le_pow_right₀ hp.one_lt.le hdt)
        have hltM : M0 < M := by
          dsimp [M0, M]
          calc 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d_t = r ^ c0 * (3 ^ a0 * 5 ^ b0 * p ^ d_t) := by ring
            _ < r ^ c * (3 ^ a * 5 ^ b * p ^ d) :=
                lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (by have := hp.pos; positivity))
                  (Nat.mul_le_mul_left _ hle1)
            _ = 3 ^ a * 5 ^ b * r ^ c * p ^ d := by ring
        omega
      have hd_eq : d = d_t := by
        by_contra hne
        have hlt : p ^ d_t < p ^ d := Nat.pow_lt_pow_right hp.one_lt (by omega)
        have hle1 : 3 ^ a0 * 5 ^ b0 * r ^ c0 ≤ 3 ^ a * 5 ^ b * r ^ c :=
          Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) ha0) (pow_le_pow_right₀ (by decide) hb0))
            (pow_le_pow_right₀ hr.one_lt.le hc0)
        have hltM : M0 < M := by
          dsimp [M0, M]
          calc 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d_t = p ^ d_t * (3 ^ a0 * 5 ^ b0 * r ^ c0) := by ring
            _ < p ^ d * (3 ^ a * 5 ^ b * r ^ c) :=
                lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (by have := hr.pos; positivity))
                  (Nat.mul_le_mul_left _ hle1)
            _ = 3 ^ a * 5 ^ b * r ^ c * p ^ d := by ring
        omega
      exact ⟨ha_eq, hb_eq, hc_eq, hd_eq⟩
    simp only [checkBox4] at hok
    by_cases h1 : Nat.ble (hiNum 3 a1 * hiNum 5 b1 * hiNum r c1 * hiNum p d1)
        (2 * (hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1)) = true
    · exact (hup_kill hd1 ((Iff.of_eq Nat.ble_eq).mp h1)).elim
    · rw [Bool.eq_false_iff.mpr h1] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
      let lN3 := ppSum 3 a0 * ppSum 5 b0 * ppSum r c0
      let lD3 := 3 ^ a0 * 5 ^ b0 * r ^ c0
      by_cases h2 : Nat.ble (2 * lD3 * p ^ d0 + 1) (lN3 * ppSum p d0) = true
      · rw [h2] at hok; simp only [↓reduceIte] at hok
        have hgt : 2 * lD3 * p ^ d0 < lN3 * ppSum p d0 := by have := (Iff.of_eq Nat.ble_eq).mp h2; omega
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hdom_eq d0 hd0 hgt
        exact checkFixedB3_sound hr hp h5r hrp hd_pos le_rfl le_rfl hno3 hab hprim hok
      · rw [Bool.eq_false_iff.mpr h2] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
        by_cases h3 : ((a1 == some a0) && (b1 == some b0) && (c1 == some c0)) = true
        · rw [h3] at hok; simp only [↓reduceIte] at hok
          repeat rw [Bool.and_eq_true] at h3
          rcases h3 with ⟨⟨ea, eb⟩, ec⟩
          have ea' : a1 = some a0 := by simpa using ea
          have eb' : b1 = some b0 := by simpa using eb
          have ec' : c1 = some c0 := by simpa using ec
          rw [ea'] at ha1; rw [eb'] at hb1; rw [ec'] at hc1
          have ha_eq : a = a0 := le_antisymm ha1 ha0
          have hb_eq : b = b0 := le_antisymm hb1 hb0
          have hc_eq : c = c0 := le_antisymm hc1 hc0
          subst ha_eq; subst hb_eq; subst hc_eq
          exact checkFixedB3_sound hr hp h5r hrp hd_pos hd0 hd1 hno3 hab hprim hok
        · rw [Bool.eq_false_iff.mpr h3] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
          -- Handle the d1' tightening step cleanly
          have hstep_d1 : ∀ (d1' : Option ℕ), leOpt d d1' →
              (if (match d1' with | some dv => Nat.ble (dv + 1) d0 | none => false) ||
                  Nat.ble (hiNum 3 a1 * hiNum 5 b1 * hiNum r c1 * hiNum p d1')
                    (2 * (hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1')) then true
               else
                match pickDim3 r a0 a1 b0 b1 c0 c1 with
                | 0 => checkBox4 fuel r p a0 (some a0) b0 b1 c0 c1 d0 d1' Lcut &&
                       checkBox4 fuel r p (a0 + 1) a1 b0 b1 c0 c1 d0 d1' Lcut
                | 1 => checkBox4 fuel r p a0 a1 b0 (some b0) c0 c1 d0 d1' Lcut &&
                       checkBox4 fuel r p a0 a1 (b0 + 2) b1 c0 c1 d0 d1' Lcut
                | _ =>
                  let step := if Nat.beq (r % 3) 2 then 2 else if Nat.beq (c0 % 3) 1 then 2 else 1
                  checkBox4 fuel r p a0 a1 b0 b1 c0 (some c0) d0 d1' Lcut &&
                  checkBox4 fuel r p a0 a1 b0 b1 (c0 + step) c1 d0 d1' Lcut) = true →
              Lcut ≤ sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d) - 2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d) := by
            intro d1' hd1' hrem
            rcases ite_true_or hrem with hkill | hrem
            · rw [Bool.or_eq_true] at hkill
              rcases hkill with hemp | hlim
              · exact (optBle_false hemp hd1' hd0).elim
              · exact (hup_kill hd1' ((Iff.of_eq Nat.ble_eq).mp hlim)).elim
            · split at hrem
              · rw [Bool.and_eq_true] at hrem
                by_cases heq : a = a0
                · exact checkBox4_sound fuel r p a0 (some a0) b0 b1 c0 c1 d0 d1' Lcut a b c d
                    hr hp h5r hrp ha0 (show a ≤ a0 by omega) hb0 hb1 hbe hb0e hc0 hc1 hc0e hd_pos hd0 hd1' hno3 hab hprim hrem.1
                · exact checkBox4_sound fuel r p (a0 + 1) a1 b0 b1 c0 c1 d0 d1' Lcut a b c d
                    hr hp h5r hrp (by omega) ha1 hb0 hb1 hbe hb0e hc0 hc1 hc0e hd_pos hd0 hd1' hno3 hab hprim hrem.2
              · rw [Bool.and_eq_true] at hrem
                by_cases heq : b = b0
                · exact checkBox4_sound fuel r p a0 a1 b0 (some b0) c0 c1 d0 d1' Lcut a b c d
                    hr hp h5r hrp ha0 ha1 hb0 (show b ≤ b0 by omega) hbe hb0e hc0 hc1 hc0e hd_pos hd0 hd1' hno3 hab hprim hrem.1
                · exact checkBox4_sound fuel r p a0 a1 (b0 + 2) b1 c0 c1 d0 d1' Lcut a b c d
                    hr hp h5r hrp ha0 ha1 (by omega) hb1 hbe (by omega) hc0 hc1 hc0e hd_pos hd0 hd1' hno3 hab hprim hrem.2
              · rw [Bool.and_eq_true] at hrem
                by_cases heq : c = c0
                · exact checkBox4_sound fuel r p a0 a1 b0 b1 c0 (some c0) d0 d1' Lcut a b c d
                    hr hp h5r hrp ha0 ha1 hb0 hb1 hbe hb0e hc0 (show c ≤ c0 by omega) hc0e hd_pos hd0 hd1' hno3 hab hprim hrem.1
                · have hno3_r : ppSum r c % 3 ≠ 0 := by
                    intro h3; apply hno3
                    have : 3 ∣ ppSum r c := Nat.dvd_of_mod_eq_zero h3
                    exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this _) _)
                  have hstep_c := exp_step_of_not_dvd3' hr h5r hno3_r hc0 heq hc0e
                  have hstep_c' : c0 + (if Nat.beq (r % 3) 2 then 2 else if Nat.beq (c0 % 3) 1 then 2 else 1) ≤ c := by
                    split_ifs at hstep_c ⊢ <;> omega
                  have hstep_even : r % 3 = 2 →
                      (c0 + if Nat.beq (r % 3) 2 then 2 else if Nat.beq (c0 % 3) 1 then 2 else 1) % 2 = 0 := by
                    intro hr2
                    rw [(Iff.of_eq Nat.beq_eq).mpr hr2]; simp; have := hc0e hr2; omega
                  exact checkBox4_sound fuel r p a0 a1 b0 b1
                    (c0 + if Nat.beq (r % 3) 2 then 2 else if Nat.beq (c0 % 3) 1 then 2 else 1)
                    c1 d0 d1' Lcut a b c d
                    hr hp h5r hrp ha0 ha1 hb0 hb1 hbe hb0e hstep_c' hc1 hstep_even hd_pos hd0 hd1' hno3 hab hprim hrem.2
          by_cases hcut : Nat.ble (2 * (3 ^ a0 * 5 ^ b0 * r ^ c0) * hiDen p d1 + 1)
              (ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * hiNum p d1) = true
          · simp only [hcut, ↓reduceIte] at hok
            cases hfind : findMinExp 50 (ppSum 3 a0 * ppSum 5 b0 * ppSum r c0) (3 ^ a0 * 5 ^ b0 * r ^ c0) p d0 with
            | none => rw [hfind] at hok; simp at hok
            | some dhit =>
              rw [hfind] at hok; dsimp only at hok
              obtain ⟨hdhit_lo, hdhit_ab, _⟩ := findMinExp_sound 50 _ _ p d0 dhit hfind
              obtain ⟨hfix, hok⟩ := ite_not_false hok
              by_cases hge : dhit ≤ d
              · obtain ⟨rfl, rfl, rfl, rfl⟩ := hdom_eq dhit hge hdhit_ab
                exact checkFixedB3_sound hr hp h5r hrp hd_pos le_rfl le_rfl hno3 hab hprim hfix
              · exact hstep_d1 (minOpt d1 (dhit - 1)) (leOpt_minOpt hd1 (by omega)) hok
          · simp only [Bool.eq_false_iff.mpr hcut, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hok
            exact hstep_d1 d1 hd1 hok

/- ### 3c. Pure-Nat verifier `checkBox5` for omega = 5 small excess -/

private def checkFixedB5Loop (sB B Lcut : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | rem + 1, qc =>
    let ok_this :=
      if Nat.ble (2 * B * qc + 1) (sB * (qc + 1)) then
        Nat.ble (2 * B * qc + Lcut) (sB * (qc + 1)) ||
        Nat.beq ((sB * (qc + 1)) % 3) 0 ||
        isCompSmall qc
      else if Nat.ble 2 qc && Nat.ble (2 * B * (qc - 1) + 1) (sB * qc) then
        match findMinExp 50 sB B qc 2 with
        | none => false
        | some e =>
          Nat.ble (2 * B * qc ^ e + Lcut) (sB * ppSum qc e) ||
          Nat.beq ((sB * ppSum qc e) % 3) 0 ||
          isCompSmall qc
      else true
    ok_this && checkFixedB5Loop sB B Lcut rem (qc + 1)

private lemma checkFixedB5Loop_mem (sB B Lcut : ℕ) :
    ∀ (rem start q : ℕ),
      start ≤ q → q < start + rem →
      checkFixedB5Loop sB B Lcut rem start = true →
      (if Nat.ble (2 * B * q + 1) (sB * (q + 1)) then
        Nat.ble (2 * B * q + Lcut) (sB * (q + 1)) ||
        Nat.beq ((sB * (q + 1)) % 3) 0 ||
        isCompSmall q
      else if Nat.ble 2 q && Nat.ble (2 * B * (q - 1) + 1) (sB * q) then
        match findMinExp 50 sB B q 2 with
        | none => false
        | some e =>
          Nat.ble (2 * B * q ^ e + Lcut) (sB * ppSum q e) ||
          Nat.beq ((sB * ppSum q e) % 3) 0 ||
          isCompSmall q
      else true) = true
  | 0, start, q, h1, h2, _ => by omega
  | rem + 1, start, q, h1, h2, hok => by
    dsimp only [checkFixedB5Loop] at hok
    rw [Bool.and_eq_true] at hok
    by_cases heq : q = start
    · subst heq; exact hok.1
    · exact checkFixedB5Loop_mem sB B Lcut rem (start + 1) q (by omega) (by omega) hok.2

private def checkFixedB5 (r p a0 b0 c0 d0 q0 : ℕ) (q1 : Option ℕ) (Lcut : ℕ) : Bool :=
  let B := 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0
  let sB := ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * ppSum p d0
  if Nat.ble (2 * B) sB then true
  else
    let D := 2 * B - sB
    let q_lo := max q0 ((sB - Lcut) / D)
    let q_hi_raw := sB / D + 1
    let q_hi := match q1 with | none => q_hi_raw | some v => min v q_hi_raw
    if Nat.ble (q_hi + 1) q_lo then true
    else checkFixedB5Loop sB B Lcut (q_hi - q_lo + 1) q_lo

private lemma checkFixedB5_sound {r p q a0 b0 c0 d0 q0 e Lcut : ℕ} {q1 : Option ℕ}
    (hr : r.Prime) (hp : p.Prime) (hq : q.Prime) (h5r : 5 < r) (hrp : r < p) (hpq : p < q)
    (hq0 : q0 ≤ q) (hq1 : leOpt q q1) (he : 1 ≤ e)
    (hno3 : (ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * ppSum p d0 * ppSum q e) % 3 ≠ 0)
    (hab : (3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e).properDivisors, x.Deficient)
    (hok : checkFixedB5 r p a0 b0 c0 d0 q0 q1 Lcut = true) :
    Lcut ≤ sigma 1 (3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e) -
      2 * (3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e) := by
  let B := 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0
  let sB := ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * ppSum p d0
  have hBpos : 0 < B := by have := hr.pos; have := hp.pos; positivity
  have hmpos : 0 < B * q ^ e := by have := hq.pos; positivity
  have hsig := sigma_five_primes hr hp hq h5r hrp hpq (a := a0) (b := b0) (c := c0) (d := d0) (e := e)
  have hmab : 2 * B * q ^ e < sB * ppSum q e := by
    have h1 := (abund_iff_nat hmpos).mp hab
    rw [hsig] at h1; dsimp [B, sB] at h1 ⊢; linarith
  have hBdef : sB < 2 * B := by
    have hmem : B ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right B _, lt_mul_of_one_lt_right hBpos (one_lt_pow₀ hq.one_lt (by omega))⟩
    have h1 := (defic_iff_nat hBpos).mp (hprim B hmem)
    rw [sigma_four_primes hr hp h5r hrp] at h1; exact h1
  let D := 2 * B - sB
  have hDpos : 0 < D := by omega
  have hlim : 2 * B * (q - 1) < sB * q := by
    have h1 := ppSum_lt_lim (p := q) (e := e) hq.two_le
    have h2 : 2 * B * q ^ e * (q - 1) < sB * ppSum q e * (q - 1) :=
      Nat.mul_lt_mul_of_pos_right hmab (by have := hq.two_le; omega)
    have h3 : sB * ppSum q e * (q - 1) ≤ sB * (q * q ^ e) := by
      calc sB * ppSum q e * (q - 1) = sB * (ppSum q e * (q - 1)) := by ring
        _ ≤ sB * (q * q ^ e) := Nat.mul_le_mul_left sB h1.le
    have h4 : 2 * B * (q - 1) * q ^ e < sB * q * q ^ e := by linarith
    exact Nat.lt_of_mul_lt_mul_right h4
  have hq_le_raw : q ≤ sB / D + 1 := by
    have hqD : q * D < sB + D := by
      have hBD : 2 * B = sB + D := by omega
      zify [show 1 ≤ q by omega] at hlim hBD ⊢; nlinarith
    have hdiv := Nat.div_add_mod sB D
    have hmod := Nat.mod_lt sB hDpos
    nlinarith
  by_contra hlt_L
  push Not at hlt_L
  rw [hsig] at hlt_L
  change sB * ppSum q e - 2 * (B * q ^ e) < Lcut at hlt_L
  have hq_ge_div : (sB - Lcut) / D ≤ q := by
    by_cases he1 : e = 1
    · subst he1
      simp only [pow_one, ppSum, zero_add] at hmab hlt_L
      have hsub : sB - Lcut ≤ q * D := by
        have h1 : 2 * B * q < sB * (1 + q) := hmab
        have h2 : sB * (1 + q) - 2 * (B * q) < Lcut := hlt_L
        have h3 : sB * (1 + q) < 2 * (B * q) + Lcut := by omega
        have hBD : 2 * B = sB + D := by omega
        have h4 : sB * (1 + q) = sB + sB * q := by ring
        have h5 : 2 * (B * q) = (sB + D) * q := by rw [← hBD]; ring
        have h6 : (sB + D) * q = sB * q + q * D := by ring
        omega
      exact Nat.div_le_of_le_mul (by rwa [mul_comm])
    · have hmem : B * q ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
        ⟨Nat.mul_dvd_mul_left B (dvd_pow_self q (by omega)),
         Nat.mul_lt_mul_of_pos_left (by simpa using Nat.pow_lt_pow_right hq.one_lt (show 1 < e by omega)) hBpos⟩
      have hdef1 := (defic_iff_nat (mul_pos hBpos hq.pos)).mp (hprim _ hmem)
      have hsig1 := sigma_five_primes hr hp hq h5r hrp hpq (a := a0) (b := b0) (c := c0) (d := d0) (e := 1)
      simp only [pow_one, ppSum, zero_add] at hsig1
      rw [hsig1] at hdef1
      have hsub : sB < q * D := by
        change sB * (1 + q) < 2 * (B * q) at hdef1
        have hBD : 2 * B = sB + D := by omega
        have h4 : sB * (1 + q) = sB + sB * q := by ring
        have h5 : 2 * (B * q) = (sB + D) * q := by rw [← hBD]; ring
        have h6 : (sB + D) * q = sB * q + q * D := by ring
        omega
      exact Nat.div_le_of_le_mul (by rw [mul_comm]; omega)
  dsimp only [checkFixedB5] at hok
  have hble1 : Nat.ble (2 * B) sB = false := by
    cases h : Nat.ble (2 * B) sB
    · rfl
    · have := (Iff.of_eq Nat.ble_eq).mp h; omega
  rw [hble1] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
  let q_lo := max q0 ((sB - Lcut) / D)
  let q_hi := match q1 with | none => sB / D + 1 | some v => min v (sB / D + 1)
  have hq_lo : q_lo ≤ q := max_le hq0 hq_ge_div
  have hq_hi : q ≤ q_hi := by
    cases q1 with
    | none => exact hq_le_raw
    | some v => exact le_min hq1 hq_le_raw
  have hnot_empty : Nat.ble (q_hi + 1) q_lo = false := by
    cases h : Nat.ble (q_hi + 1) q_lo
    · rfl
    · have := (Iff.of_eq Nat.ble_eq).mp h; omega
  rw [hnot_empty] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
  have hq_ok := checkFixedB5Loop_mem sB B Lcut (q_hi - q_lo + 1) q_lo q hq_lo (by omega) hok
  by_cases he1 : e = 1
  · subst he1
    simp only [pow_one, ppSum, zero_add] at hmab hlt_L hno3
    have hqcomm : 1 + q = q + 1 := by ring
    have hBmul : 2 * (B * q) = 2 * B * q := by ring
    have hble_e1 : Nat.ble (2 * B * q + 1) (sB * (q + 1)) = true :=
      (Iff.of_eq Nat.ble_eq).mpr (by rw [← hqcomm]; omega)
    rw [hble_e1] at hq_ok; simp only [↓reduceIte, Bool.or_eq_true] at hq_ok
    rcases hq_ok with (hE | h3) | hcomp
    · have := (Iff.of_eq Nat.ble_eq).mp hE; rw [← hqcomm] at this; omega
    · rw [← hqcomm] at h3; exact hno3 ((Iff.of_eq Nat.beq_eq).mp h3)
    · exact not_prime_of_isCompSmall hcomp hq
  · have hmem : B * q ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_left B (dvd_pow_self q (by omega)),
       Nat.mul_lt_mul_of_pos_left (by simpa using Nat.pow_lt_pow_right hq.one_lt (show 1 < e by omega)) hBpos⟩
    have hdef1 := (defic_iff_nat (mul_pos hBpos hq.pos)).mp (hprim _ hmem)
    have hsig1 := sigma_five_primes hr hp hq h5r hrp hpq (a := a0) (b := b0) (c := c0) (d := d0) (e := 1)
    simp only [pow_one, ppSum, zero_add] at hsig1
    rw [hsig1] at hdef1
    have hnot_e1 : Nat.ble (2 * B * q + 1) (sB * (q + 1)) = false := by
      cases h : Nat.ble (2 * B * q + 1) (sB * (q + 1))
      · rfl
      · have := (Iff.of_eq Nat.ble_eq).mp h
        change sB * (1 + q) < 2 * (B * q) at hdef1
        have : sB * (q + 1) = sB * (1 + q) := by ring
        have : 2 * B * q = 2 * (B * q) := by ring
        omega
    have hcond2 : (Nat.ble 2 q && Nat.ble (2 * B * (q - 1) + 1) (sB * q)) = true := by
      rw [Bool.and_eq_true]
      exact ⟨(Iff.of_eq Nat.ble_eq).mpr hq.two_le, (Iff.of_eq Nat.ble_eq).mpr (by omega)⟩
    rw [hnot_e1, hcond2] at hq_ok; simp only [Bool.false_eq_true, ↓reduceIte] at hq_ok
    cases hfind : findMinExp 50 sB B q 2 with
    | none => rw [hfind] at hq_ok; exact Bool.noConfusion hq_ok
    | some e_min =>
      rw [hfind] at hq_ok
      obtain ⟨hemin_lo, hemin_ab, hemin_lt⟩ := findMinExp_sound 50 sB B q 2 e_min hfind
      have he_ge : e_min ≤ e := by
        by_contra hlt
        have := hemin_lt e (by omega) (by omega)
        omega
      have he_eq : e = e_min := by
        by_contra hne
        have hgt : e_min < e := by omega
        have hmem' : B * q ^ e_min ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
          ⟨Nat.mul_dvd_mul_left B (pow_dvd_pow q hgt.le),
           Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hq.one_lt hgt) hBpos⟩
        have hdef' := (defic_iff_nat (mul_pos hBpos (pow_pos hq.pos _))).mp (hprim _ hmem')
        rw [sigma_five_primes hr hp hq h5r hrp hpq] at hdef'
        change sB * ppSum q e_min < 2 * (B * q ^ e_min) at hdef'
        linarith
      subst he_eq
      simp only [Bool.or_eq_true] at hq_ok
      rcases hq_ok with (hE | h3) | hcomp
      · have := (Iff.of_eq Nat.ble_eq).mp hE
        have : 2 * (B * q ^ e) = 2 * B * q ^ e := by ring
        omega
      · exact hno3 ((Iff.of_eq Nat.beq_eq).mp h3)
      · exact not_prime_of_isCompSmall hcomp hq

private def checkBox5 (fuel r p a0 : ℕ) (a1 : Option ℕ) (b0 : ℕ) (b1 : Option ℕ)
    (c0 : ℕ) (c1 : Option ℕ) (d0 : ℕ) (d1 : Option ℕ)
    (q0 : ℕ) (q1 e1 : Option ℕ) (Lcut : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    let q0' := skipUp 50 q0
    if Nat.ble q0' 1 then false
    else
      let hN := hiNum 3 a1 * hiNum 5 b1 * hiNum r c1 * hiNum p d1
      let hD := hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1
      let q1' :=
        if Nat.ble (hN + 1) (2 * hD) then minOpt q1 ((2 * hD - 1) / (2 * hD - hN))
        else q1
      let q1'' := match q1' with | none => none | some v => some (skipDn 50 v)
      if (match q1'' with | some v => Nat.ble (v + 1) q0' | none => false) then true
      else if Nat.ble (hN * hiNum q0' e1) (2 * hD * hiDen q0' e1) then true
      else
        let lN := ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * ppSum p d0
        let lD := 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0
        if Nat.ble (2 * lD + 1) lN then true
        else if (a1 == some a0) && (b1 == some b0) && (c1 == some c0) && (d1 == some d0) then
          checkFixedB5 r p a0 b0 c0 d0 q0' q1'' Lcut
        else
          let (okCut, q0'') :=
            if Nat.ble (lN + 1) (2 * lD) then
              let q_cut := (lN - 1) / (2 * lD - lN)
              if Nat.ble q0' q_cut then
                (checkFixedB5 r p a0 b0 c0 d0 q0' (minOpt q1'' q_cut) Lcut, skipUp 50 (q_cut + 1))
              else (true, q0')
            else (true, q0')
          if !okCut then false
          else if (match q1'' with | some v => Nat.ble (v + 1) q0'' | none => false) then true
          else if Nat.ble (hN * hiNum q0'' e1) (2 * hD * hiDen q0'' e1) then true
          else
            let (okEq, e1') :=
              match q1'' with
              | some qv =>
                if Nat.beq q0'' qv && Nat.ble (2 * lD * hiDen qv e1 + 1) (lN * hiNum qv e1) then
                  match findMinExp 50 lN lD qv 2 with
                  | none => (false, e1)
                  | some e0 =>
                    (checkFixedB5 r p a0 b0 c0 d0 qv (some qv) Lcut, minOpt e1 (e0 - 1))
                else (true, e1)
              | none => (true, e1)
            if !okEq then false
            else if Nat.ble (hN * hiNum q0'' e1') (2 * hD * hiDen q0'' e1') then true
            else
              match pickDim4 r p a0 a1 b0 b1 c0 c1 d0 d1 with
              | 0 => checkBox5 fuel r p a0 (some a0) b0 b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut &&
                     checkBox5 fuel r p (a0 + 1) a1 b0 b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut
              | 1 => checkBox5 fuel r p a0 a1 b0 (some b0) c0 c1 d0 d1 q0'' q1'' e1' Lcut &&
                     checkBox5 fuel r p a0 a1 (b0 + 2) b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut
              | 2 =>
                let step := if Nat.beq (r % 3) 2 then 2 else if Nat.beq (c0 % 3) 1 then 2 else 1
                checkBox5 fuel r p a0 a1 b0 b1 c0 (some c0) d0 d1 q0'' q1'' e1' Lcut &&
                checkBox5 fuel r p a0 a1 b0 b1 (c0 + step) c1 d0 d1 q0'' q1'' e1' Lcut
              | _ =>
                let step := if Nat.beq (p % 3) 2 then 2 else if Nat.beq (d0 % 3) 1 then 2 else 1
                checkBox5 fuel r p a0 a1 b0 b1 c0 c1 d0 (some d0) q0'' q1'' e1' Lcut &&
                checkBox5 fuel r p a0 a1 b0 b1 c0 c1 (d0 + step) d1 q0'' q1'' e1' Lcut

set_option maxHeartbeats 800000 in
private lemma checkBox5_sound :
    ∀ (fuel r p a0 : ℕ) (a1 : Option ℕ) (b0 : ℕ) (b1 : Option ℕ)
      (c0 : ℕ) (c1 : Option ℕ) (d0 : ℕ) (d1 : Option ℕ)
      (q0 : ℕ) (q1 e1 : Option ℕ) (Lcut a b c d q e : ℕ),
      r.Prime → p.Prime → q.Prime → 5 < r → r < p → p < q →
      a0 ≤ a → leOpt a a1 →
      b0 ≤ b → leOpt b b1 → b % 2 = 0 → b0 % 2 = 0 →
      c0 ≤ c → leOpt c c1 → (r % 3 = 2 → c0 % 2 = 0) →
      d0 ≤ d → leOpt d d1 → (p % 3 = 2 → d0 % 2 = 0) →
      q0 ≤ q → leOpt q q1 → 1 ≤ e → leOpt e e1 →
      (ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * ppSum q e) % 3 ≠ 0 →
      (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e).Abundant →
      (∀ x ∈ (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e).properDivisors, x.Deficient) →
      checkBox5 fuel r p a0 a1 b0 b1 c0 c1 d0 d1 q0 q1 e1 Lcut = true →
      Lcut ≤ sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e) -
        2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hok => by
      simp [checkBox5] at hok
  | fuel + 1, r, p, a0, a1, b0, b1, c0, c1, d0, d1, q0, q1, e1, Lcut, a, b, c, d, q, e,
    hr, hp, hq, h5r, hrp, hpq, ha0, ha1, hb0, hb1, hbe, hb0e, hc0, hc1, hc0e, hd0, hd1, hd0e,
    hq0, hq1, he_lo, he1, hno3, hab, hprim, hok => by
    have hsig := sigma_five_primes hr hp hq h5r hrp hpq (a := a) (b := b) (c := c) (d := d) (e := e)
    set B := 3 ^ a * 5 ^ b * r ^ c * p ^ d
    set sB := ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d
    have hBpos : 0 < B := by have := hr.pos; have := hp.pos; positivity
    have hMpos : 0 < B * q ^ e := by have := hq.pos; positivity
    have hMab : 2 * (B * q ^ e) < sB * ppSum q e := by
      have h1 := (abund_iff_nat hMpos).mp hab; rwa [hsig] at h1
    let hN := hiNum 3 a1 * hiNum 5 b1 * hiNum r c1 * hiNum p d1
    let hD := hiDen 3 a1 * hiDen 5 b1 * hiDen r c1 * hiDen p d1
    have hhDpos : 0 < hD := by
      have := hiDen_pos (p := 3) (by decide) a1
      have := hiDen_pos (p := 5) (by decide) b1
      have := hiDen_pos (p := r) hr.two_le c1
      have := hiDen_pos (p := p) hp.two_le d1
      positivity
    have hhiB : sB * hD ≤ hN * B := by
      have u3 := ppSum_le_hi (p := 3) (by decide) ha1
      have u5 := ppSum_le_hi (p := 5) (by decide) hb1
      have ur := ppSum_le_hi (p := r) hr.two_le hc1
      have up := ppSum_le_hi (p := p) hp.two_le hd1
      have u12 := Nat.mul_le_mul u3 u5
      have u34 := Nat.mul_le_mul ur up
      have u1234 := Nat.mul_le_mul u12 u34
      calc sB * hD
          = (ppSum 3 a * hiDen 3 a1 * (ppSum 5 b * hiDen 5 b1)) *
            (ppSum r c * hiDen r c1 * (ppSum p d * hiDen p d1)) := by dsimp [sB, hD]; ring
        _ ≤ (hiNum 3 a1 * 3 ^ a * (hiNum 5 b1 * 5 ^ b)) *
            (hiNum r c1 * r ^ c * (hiNum p d1 * p ^ d)) := u1234
        _ = hN * B := by dsimp [hN, B]; ring
    have hup_kill : ∀ {qb : ℕ} {eb : Option ℕ}, 2 ≤ qb → qb ≤ q → leOpt e eb →
        hN * hiNum qb eb ≤ 2 * hD * hiDen qb eb → False := by
      intro qb eb hqb2 hqbq heb hle
      have hqhi := ppSum_le_hi_prime hqb2 hqbq heb
      have hden_pos : 0 < hD * hiDen qb eb := Nat.mul_pos hhDpos (hiDen_pos hqb2 eb)
      have hmul : sB * ppSum q e * (hD * hiDen qb eb) ≤ hN * hiNum qb eb * (B * q ^ e) := by
        have := Nat.mul_le_mul hhiB hqhi; linarith
      have h1 : 2 * (B * q ^ e) * (hD * hiDen qb eb) < sB * ppSum q e * (hD * hiDen qb eb) :=
        Nat.mul_lt_mul_of_pos_right hMab hden_pos
      have h2 : hN * hiNum qb eb * (B * q ^ e) ≤ 2 * hD * hiDen qb eb * (B * q ^ e) :=
        Nat.mul_le_mul_right _ hle
      linarith
    have hdom_eq : ∀ e_t : ℕ, 1 ≤ e_t → e_t ≤ e →
        2 * (3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0) * q ^ e_t <
          ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * ppSum p d0 * ppSum q e_t →
        a = a0 ∧ b = b0 ∧ c = c0 ∧ d = d0 ∧ e = e_t := by
      intro e_t het1 het hgt
      let M0 := 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e_t
      have hM0pos : 0 < M0 := by have := hr.pos; have := hp.pos; have := hq.pos; positivity
      have hM0dvd : M0 ∣ B * q ^ e := by
        dsimp [M0, B]
        exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 ha0)
          (pow_dvd_pow 5 hb0)) (pow_dvd_pow r hc0)) (pow_dvd_pow p hd0)) (pow_dvd_pow q het)
      have hM0eq : M0 = B * q ^ e := by
        by_contra hne
        have hmem : M0 ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
          ⟨hM0dvd, lt_of_le_of_ne (Nat.le_of_dvd hMpos hM0dvd) hne⟩
        have hdef := (defic_iff_nat hM0pos).mp (hprim M0 hmem)
        rw [sigma_five_primes hr hp hq h5r hrp hpq] at hdef
        dsimp [M0] at hdef; linarith
      have ha_eq : a = a0 := by
        by_contra hne
        have hlt : 3 ^ a0 < 3 ^ a := Nat.pow_lt_pow_right (by decide) (by omega)
        have hle1 : 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e_t ≤ 5 ^ b * r ^ c * p ^ d * q ^ e :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) hb0)
            (pow_le_pow_right₀ hr.one_lt.le hc0)) (pow_le_pow_right₀ hp.one_lt.le hd0)) (pow_le_pow_right₀ hq.one_lt.le het)
        have hltM : M0 < B * q ^ e := by
          dsimp [M0, B]
          calc 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e_t = 3 ^ a0 * (5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e_t) := by ring
            _ < 3 ^ a * (5 ^ b * r ^ c * p ^ d * q ^ e) :=
                lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (by have := hr.pos; have := hp.pos; have := hq.pos; positivity))
                  (Nat.mul_le_mul_left _ hle1)
            _ = 3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e := by ring
        omega
      have hb_eq : b = b0 := by
        by_contra hne
        have hlt : 5 ^ b0 < 5 ^ b := Nat.pow_lt_pow_right (by decide) (by omega)
        have hle1 : 3 ^ a0 * r ^ c0 * p ^ d0 * q ^ e_t ≤ 3 ^ a * r ^ c * p ^ d * q ^ e :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) ha0)
            (pow_le_pow_right₀ hr.one_lt.le hc0)) (pow_le_pow_right₀ hp.one_lt.le hd0)) (pow_le_pow_right₀ hq.one_lt.le het)
        have hltM : M0 < B * q ^ e := by
          dsimp [M0, B]
          calc 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e_t = 5 ^ b0 * (3 ^ a0 * r ^ c0 * p ^ d0 * q ^ e_t) := by ring
            _ < 5 ^ b * (3 ^ a * r ^ c * p ^ d * q ^ e) :=
                lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (by have := hr.pos; have := hp.pos; have := hq.pos; positivity))
                  (Nat.mul_le_mul_left _ hle1)
            _ = 3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e := by ring
        omega
      have hc_eq : c = c0 := by
        by_contra hne
        have hlt : r ^ c0 < r ^ c := Nat.pow_lt_pow_right hr.one_lt (by omega)
        have hle1 : 3 ^ a0 * 5 ^ b0 * p ^ d0 * q ^ e_t ≤ 3 ^ a * 5 ^ b * p ^ d * q ^ e :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) ha0)
            (pow_le_pow_right₀ (by decide) hb0)) (pow_le_pow_right₀ hp.one_lt.le hd0)) (pow_le_pow_right₀ hq.one_lt.le het)
        have hltM : M0 < B * q ^ e := by
          dsimp [M0, B]
          calc 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e_t = r ^ c0 * (3 ^ a0 * 5 ^ b0 * p ^ d0 * q ^ e_t) := by ring
            _ < r ^ c * (3 ^ a * 5 ^ b * p ^ d * q ^ e) :=
                lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (by have := hp.pos; have := hq.pos; positivity))
                  (Nat.mul_le_mul_left _ hle1)
            _ = 3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e := by ring
        omega
      have hd_eq : d = d0 := by
        by_contra hne
        have hlt : p ^ d0 < p ^ d := Nat.pow_lt_pow_right hp.one_lt (by omega)
        have hle1 : 3 ^ a0 * 5 ^ b0 * r ^ c0 * q ^ e_t ≤ 3 ^ a * 5 ^ b * r ^ c * q ^ e :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) ha0)
            (pow_le_pow_right₀ (by decide) hb0)) (pow_le_pow_right₀ hr.one_lt.le hc0)) (pow_le_pow_right₀ hq.one_lt.le het)
        have hltM : M0 < B * q ^ e := by
          dsimp [M0, B]
          calc 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e_t = p ^ d0 * (3 ^ a0 * 5 ^ b0 * r ^ c0 * q ^ e_t) := by ring
            _ < p ^ d * (3 ^ a * 5 ^ b * r ^ c * q ^ e) :=
                lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (by have := hr.pos; have := hq.pos; positivity))
                  (Nat.mul_le_mul_left _ hle1)
            _ = 3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e := by ring
        omega
      have he_eq : e = e_t := by
        by_contra hne
        have hlt : q ^ e_t < q ^ e := Nat.pow_lt_pow_right hq.one_lt (by omega)
        have hle1 : 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 ≤ 3 ^ a * 5 ^ b * r ^ c * p ^ d :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) ha0)
            (pow_le_pow_right₀ (by decide) hb0)) (pow_le_pow_right₀ hr.one_lt.le hc0)) (pow_le_pow_right₀ hp.one_lt.le hd0)
        have hltM : M0 < B * q ^ e := by
          dsimp [M0, B]
          calc 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0 * q ^ e_t = q ^ e_t * (3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0) := by ring
            _ < q ^ e * (3 ^ a * 5 ^ b * r ^ c * p ^ d) :=
                lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (by have := hr.pos; have := hp.pos; positivity))
                  (Nat.mul_le_mul_left _ hle1)
            _ = 3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e := by ring
        omega
      exact ⟨ha_eq, hb_eq, hc_eq, hd_eq, he_eq⟩
    simp only [checkBox5] at hok
    let q0' := skipUp 50 q0
    have hq0'_le : q0' ≤ q := skipUp_le hq 50 q0 hq0
    by_cases hq0_bad : Nat.ble q0' 1 = true
    · rw [hq0_bad] at hok; simp at hok
    · rw [Bool.eq_false_iff.mpr hq0_bad] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
      have hq0'_ge2 : 2 ≤ q0' := by
        by_contra hlt
        exact hq0_bad ((Iff.of_eq Nat.ble_eq).mpr (by omega))
      let q1' := if Nat.ble (hN + 1) (2 * hD) then minOpt q1 ((2 * hD - 1) / (2 * hD - hN)) else q1
      have hq1'_le : leOpt q q1' := by
        dsimp only [q1']
        split_ifs with hlt
        · have hlt' : hN < 2 * hD := by have := (Iff.of_eq Nat.ble_eq).mp hlt; omega
          have hq_bound : q ≤ (2 * hD - 1) / (2 * hD - hN) := by
            have hqlim := ppSum_lt_lim (p := q) (e := e) hq.two_le
            have h1 : 2 * (B * q ^ e) * (hD * (q - 1)) < sB * ppSum q e * (hD * (q - 1)) :=
              Nat.mul_lt_mul_of_pos_right hMab (Nat.mul_pos hhDpos (by have := hq.two_le; omega))
            have h2 : sB * ppSum q e * (hD * (q - 1)) ≤ hN * q * (B * q ^ e) := by
              have := Nat.mul_le_mul hhiB hqlim.le; linarith
            have h3 : 2 * hD * (q - 1) < hN * q := Nat.lt_of_mul_lt_mul_right (show 2 * hD * (q - 1) * (B * q ^ e) < hN * q * (B * q ^ e) by linarith)
            have h4 : (2 * hD - hN) * q ≤ 2 * hD - 1 := by
              zify [hlt'.le, show 1 ≤ q by omega, show 1 ≤ 2 * hD by omega] at h3 ⊢; nlinarith
            exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rwa [mul_comm])
          exact leOpt_minOpt hq1 hq_bound
        · exact hq1
      let q1'' := match q1' with | none => none | some v => some (skipDn 50 v)
      have hq1''_le : leOpt q q1'' := by
        dsimp only [q1'']
        generalize hq1'_eq : q1' = o at hq1'_le ⊢
        cases o with
        | none => trivial
        | some v => exact le_skipDn hq 50 v hq1'_le
      by_cases hemp1 : (match (generalizing := false) q1'' with | some v => Nat.ble (v + 1) q0' | none => false) = true
      · exfalso
        have hle := hq1''_le
        generalize hq1''_eq : q1'' = o at hemp1 hle
        cases o with
        | none => exact Bool.noConfusion hemp1
        | some v =>
          have := (Iff.of_eq Nat.ble_eq).mp hemp1
          change q ≤ v at hle; omega
      · rw [Bool.eq_false_iff.mpr hemp1] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
        by_cases hlim1 : Nat.ble (hN * hiNum q0' e1) (2 * hD * hiDen q0' e1) = true
        · exact (hup_kill hq0'_ge2 hq0'_le he1 ((Iff.of_eq Nat.ble_eq).mp hlim1)).elim
        · rw [Bool.eq_false_iff.mpr hlim1] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
          let lN := ppSum 3 a0 * ppSum 5 b0 * ppSum r c0 * ppSum p d0
          let lD := 3 ^ a0 * 5 ^ b0 * r ^ c0 * p ^ d0
          by_cases hlo_ab : Nat.ble (2 * lD + 1) lN = true
          · have hgt : 2 * lD < lN := by have := (Iff.of_eq Nat.ble_eq).mp hlo_ab; omega
            have hlDpos : 0 < lD := by have := hr.pos; have := hp.pos; positivity
            have hdvd : lD ∣ B * q ^ e := by
              dsimp [lD, B]
              exact dvd_mul_of_dvd_left (Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul
                (pow_dvd_pow 3 ha0) (pow_dvd_pow 5 hb0)) (pow_dvd_pow r hc0)) (pow_dvd_pow p hd0)) _
            have hlt : lD < B * q ^ e := by
              have hle : lD ≤ B := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) ha0)
                (pow_le_pow_right₀ (by decide) hb0)) (pow_le_pow_right₀ hr.one_lt.le hc0)) (pow_le_pow_right₀ hp.one_lt.le hd0)
              exact lt_of_le_of_lt hle (lt_mul_of_one_lt_right hBpos (one_lt_pow₀ hq.one_lt (by omega)))
            have hdef := (defic_iff_nat hlDpos).mp (hprim lD (Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩))
            rw [sigma_four_primes hr hp h5r hrp] at hdef
            change lN < 2 * lD at hdef; omega
          · rw [Bool.eq_false_iff.mpr hlo_ab] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
            by_cases hfixed : ((a1 == some a0) && (b1 == some b0) && (c1 == some c0) && (d1 == some d0)) = true
            · rw [hfixed] at hok; simp only [↓reduceIte] at hok
              repeat rw [Bool.and_eq_true] at hfixed
              rcases hfixed with ⟨⟨⟨ea, eb⟩, ec⟩, ed⟩
              have ea' : a1 = some a0 := by simpa using ea
              have eb' : b1 = some b0 := by simpa using eb
              have ec' : c1 = some c0 := by simpa using ec
              have ed' : d1 = some d0 := by simpa using ed
              rw [ea'] at ha1; rw [eb'] at hb1; rw [ec'] at hc1; rw [ed'] at hd1
              have ha_eq : a = a0 := le_antisymm ha1 ha0
              have hb_eq : b = b0 := le_antisymm hb1 hb0
              have hc_eq : c = c0 := le_antisymm hc1 hc0
              have hd_eq : d = d0 := le_antisymm hd1 hd0
              subst ha_eq; subst hb_eq; subst hc_eq; subst hd_eq
              exact checkFixedB5_sound hr hp hq h5r hrp hpq hq0'_le hq1''_le he_lo hno3 hab hprim hok
            · rw [Bool.eq_false_iff.mpr hfixed] at hok; simp only [Bool.false_eq_true, ↓reduceIte] at hok
              -- Continue after q_cut step
              have hafter_cut : ∀ (q0'' : ℕ), 2 ≤ q0'' → q0'' ≤ q →
                  (if (match (generalizing := false) q1'' with | some v => Nat.ble (v + 1) q0'' | none => false) then true
                   else if Nat.ble (hN * hiNum q0'' e1) (2 * hD * hiDen q0'' e1) then true
                   else
                     let (okEq, e1') :=
                       match (generalizing := false) q1'' with
                       | some qv =>
                         if Nat.beq q0'' qv && Nat.ble (2 * lD * hiDen qv e1 + 1) (lN * hiNum qv e1) then
                           match findMinExp 50 lN lD qv 2 with
                           | none => (false, e1)
                           | some e0 =>
                             (checkFixedB5 r p a0 b0 c0 d0 qv (some qv) Lcut, minOpt e1 (e0 - 1))
                         else (true, e1)
                       | none => (true, e1)
                     if !okEq then false
                     else if Nat.ble (hN * hiNum q0'' e1') (2 * hD * hiDen q0'' e1') then true
                     else
                       match pickDim4 r p a0 a1 b0 b1 c0 c1 d0 d1 with
                       | 0 => checkBox5 fuel r p a0 (some a0) b0 b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut &&
                              checkBox5 fuel r p (a0 + 1) a1 b0 b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut
                       | 1 => checkBox5 fuel r p a0 a1 b0 (some b0) c0 c1 d0 d1 q0'' q1'' e1' Lcut &&
                              checkBox5 fuel r p a0 a1 (b0 + 2) b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut
                       | 2 =>
                         let step := if Nat.beq (r % 3) 2 then 2 else if Nat.beq (c0 % 3) 1 then 2 else 1
                         checkBox5 fuel r p a0 a1 b0 b1 c0 (some c0) d0 d1 q0'' q1'' e1' Lcut &&
                         checkBox5 fuel r p a0 a1 b0 b1 (c0 + step) c1 d0 d1 q0'' q1'' e1' Lcut
                       | _ =>
                         let step := if Nat.beq (p % 3) 2 then 2 else if Nat.beq (d0 % 3) 1 then 2 else 1
                         checkBox5 fuel r p a0 a1 b0 b1 c0 c1 d0 (some d0) q0'' q1'' e1' Lcut &&
                         checkBox5 fuel r p a0 a1 b0 b1 c0 c1 (d0 + step) d1 q0'' q1'' e1' Lcut) = true →
                  Lcut ≤ sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e) -
                    2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e) := by
                intro q0'' hq0''_2 hq0''_le hrem
                by_cases hemp2 : (match (generalizing := false) q1'' with | some v => Nat.ble (v + 1) q0'' | none => false) = true
                · exfalso
                  have hle := hq1''_le
                  generalize hq1''_eq : q1'' = o at hemp2 hle
                  cases o with
                  | none => exact Bool.noConfusion hemp2
                  | some v =>
                    have := (Iff.of_eq Nat.ble_eq).mp hemp2
                    change q ≤ v at hle; omega
                · rw [Bool.eq_false_iff.mpr hemp2] at hrem; simp only [Bool.false_eq_true, ↓reduceIte] at hrem
                  by_cases hlim2 : Nat.ble (hN * hiNum q0'' e1) (2 * hD * hiDen q0'' e1) = true
                  · exact (hup_kill hq0''_2 hq0''_le he1 ((Iff.of_eq Nat.ble_eq).mp hlim2)).elim
                  · rw [Bool.eq_false_iff.mpr hlim2] at hrem; simp only [Bool.false_eq_true, ↓reduceIte] at hrem
                    have hafter_e1 : ∀ (e1' : Option ℕ), leOpt e e1' →
                        (if Nat.ble (hN * hiNum q0'' e1') (2 * hD * hiDen q0'' e1') then true
                         else
                           match pickDim4 r p a0 a1 b0 b1 c0 c1 d0 d1 with
                           | 0 => checkBox5 fuel r p a0 (some a0) b0 b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut &&
                                  checkBox5 fuel r p (a0 + 1) a1 b0 b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut
                           | 1 => checkBox5 fuel r p a0 a1 b0 (some b0) c0 c1 d0 d1 q0'' q1'' e1' Lcut &&
                                  checkBox5 fuel r p a0 a1 (b0 + 2) b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut
                           | 2 =>
                             let step := if Nat.beq (r % 3) 2 then 2 else if Nat.beq (c0 % 3) 1 then 2 else 1
                             checkBox5 fuel r p a0 a1 b0 b1 c0 (some c0) d0 d1 q0'' q1'' e1' Lcut &&
                             checkBox5 fuel r p a0 a1 b0 b1 (c0 + step) c1 d0 d1 q0'' q1'' e1' Lcut
                           | _ =>
                             let step := if Nat.beq (p % 3) 2 then 2 else if Nat.beq (d0 % 3) 1 then 2 else 1
                             checkBox5 fuel r p a0 a1 b0 b1 c0 c1 d0 (some d0) q0'' q1'' e1' Lcut &&
                             checkBox5 fuel r p a0 a1 b0 b1 c0 c1 (d0 + step) d1 q0'' q1'' e1' Lcut) = true →
                        Lcut ≤ sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e) -
                          2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e) := by
                      intro e1' he1' hrem2
                      by_cases hlim3 : Nat.ble (hN * hiNum q0'' e1') (2 * hD * hiDen q0'' e1') = true
                      · exact (hup_kill hq0''_2 hq0''_le he1' ((Iff.of_eq Nat.ble_eq).mp hlim3)).elim
                      · rw [Bool.eq_false_iff.mpr hlim3] at hrem2; simp only [Bool.false_eq_true, ↓reduceIte] at hrem2
                        split at hrem2
                        · rw [Bool.and_eq_true] at hrem2
                          by_cases heq : a = a0
                          · exact checkBox5_sound fuel r p a0 (some a0) b0 b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut a b c d q e
                              hr hp hq h5r hrp hpq ha0 (by simp [leOpt, heq]) hb0 hb1 hbe hb0e hc0 hc1 hc0e hd0 hd1 hd0e
                              hq0''_le hq1''_le he_lo he1' hno3 hab hprim hrem2.1
                          · exact checkBox5_sound fuel r p (a0 + 1) a1 b0 b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut a b c d q e
                              hr hp hq h5r hrp hpq (by omega) ha1 hb0 hb1 hbe hb0e hc0 hc1 hc0e hd0 hd1 hd0e
                              hq0''_le hq1''_le he_lo he1' hno3 hab hprim hrem2.2
                        · rw [Bool.and_eq_true] at hrem2
                          by_cases heq : b = b0
                          · exact checkBox5_sound fuel r p a0 a1 b0 (some b0) c0 c1 d0 d1 q0'' q1'' e1' Lcut a b c d q e
                              hr hp hq h5r hrp hpq ha0 ha1 hb0 (by simp [leOpt, heq]) hbe hb0e hc0 hc1 hc0e hd0 hd1 hd0e
                              hq0''_le hq1''_le he_lo he1' hno3 hab hprim hrem2.1
                          · exact checkBox5_sound fuel r p a0 a1 (b0 + 2) b1 c0 c1 d0 d1 q0'' q1'' e1' Lcut a b c d q e
                              hr hp hq h5r hrp hpq ha0 ha1 (by omega) hb1 hbe (by omega) hc0 hc1 hc0e hd0 hd1 hd0e
                              hq0''_le hq1''_le he_lo he1' hno3 hab hprim hrem2.2
                        · rw [Bool.and_eq_true] at hrem2
                          by_cases heq : c = c0
                          · exact checkBox5_sound fuel r p a0 a1 b0 b1 c0 (some c0) d0 d1 q0'' q1'' e1' Lcut a b c d q e
                              hr hp hq h5r hrp hpq ha0 ha1 hb0 hb1 hbe hb0e hc0 (by simp [leOpt, heq]) hc0e hd0 hd1 hd0e
                              hq0''_le hq1''_le he_lo he1' hno3 hab hprim hrem2.1
                          · have hno3_r : ppSum r c % 3 ≠ 0 := by
                              intro h3; apply hno3
                              have : 3 ∣ ppSum r c := Nat.dvd_of_mod_eq_zero h3
                              exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this _) _) _)
                            have hstep_c := exp_step_of_not_dvd3' hr h5r hno3_r hc0 heq hc0e
                            have hstep_even : r % 3 = 2 →
                                (c0 + if Nat.beq (r % 3) 2 then 2 else if Nat.beq (c0 % 3) 1 then 2 else 1) % 2 = 0 := by
                              intro hr2; rw [(Iff.of_eq Nat.beq_eq).mpr hr2]; simp; have := hc0e hr2; omega
                            exact checkBox5_sound fuel r p a0 a1 b0 b1
                              (c0 + if Nat.beq (r % 3) 2 then 2 else if Nat.beq (c0 % 3) 1 then 2 else 1)
                              c1 d0 d1 q0'' q1'' e1' Lcut a b c d q e
                              hr hp hq h5r hrp hpq ha0 ha1 hb0 hb1 hbe hb0e (by split_ifs at hstep_c ⊢ <;> omega) hc1 hstep_even hd0 hd1 hd0e
                              hq0''_le hq1''_le he_lo he1' hno3 hab hprim hrem2.2
                        · rw [Bool.and_eq_true] at hrem2
                          by_cases heq : d = d0
                          · exact checkBox5_sound fuel r p a0 a1 b0 b1 c0 c1 d0 (some d0) q0'' q1'' e1' Lcut a b c d q e
                              hr hp hq h5r hrp hpq ha0 ha1 hb0 hb1 hbe hb0e hc0 hc1 hc0e hd0 (by simp [leOpt, heq]) hd0e
                              hq0''_le hq1''_le he_lo he1' hno3 hab hprim hrem2.1
                          · have hno3_p : ppSum p d % 3 ≠ 0 := by
                              intro h3; apply hno3
                              have : 3 ∣ ppSum p d := Nat.dvd_of_mod_eq_zero h3
                              exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this _) _)
                            have hstep_d := exp_step_of_not_dvd3' hp (by omega) hno3_p hd0 heq hd0e
                            have hstep_even : p % 3 = 2 →
                                (d0 + if Nat.beq (p % 3) 2 then 2 else if Nat.beq (d0 % 3) 1 then 2 else 1) % 2 = 0 := by
                              intro hp2; rw [(Iff.of_eq Nat.beq_eq).mpr hp2]; simp; have := hd0e hp2; omega
                            exact checkBox5_sound fuel r p a0 a1 b0 b1 c0 c1
                              (d0 + if Nat.beq (p % 3) 2 then 2 else if Nat.beq (d0 % 3) 1 then 2 else 1)
                              d1 q0'' q1'' e1' Lcut a b c d q e
                              hr hp hq h5r hrp hpq ha0 ha1 hb0 hb1 hbe hb0e hc0 hc1 hc0e (by split_ifs at hstep_d ⊢ <;> omega) hd1 hstep_even
                              hq0''_le hq1''_le he_lo he1' hno3 hab hprim hrem2.2
                    have hle_q := hq1''_le
                    cases hq1'' : q1'' with
                    | none =>
                      have hred : (match (generalizing := false) q1'' with
                        | some qv =>
                          if Nat.beq q0'' qv && Nat.ble (2 * lD * hiDen qv e1 + 1) (lN * hiNum qv e1) then
                            match findMinExp 50 lN lD qv 2 with
                            | none => (false, e1)
                            | some e0 =>
                              (checkFixedB5 r p a0 b0 c0 d0 qv (some qv) Lcut, minOpt e1 (e0 - 1))
                          else (true, e1)
                        | none => (true, e1)) = (true, e1) := by rw [hq1'']
                      rw [hred] at hrem; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrem
                      exact hafter_e1 e1 he1 hrem
                    | some qv =>
                      rw [hq1''] at hle_q
                      have hred : (match (generalizing := false) q1'' with
                        | some qv =>
                          if Nat.beq q0'' qv && Nat.ble (2 * lD * hiDen qv e1 + 1) (lN * hiNum qv e1) then
                            match findMinExp 50 lN lD qv 2 with
                            | none => (false, e1)
                            | some e0 =>
                              (checkFixedB5 r p a0 b0 c0 d0 qv (some qv) Lcut, minOpt e1 (e0 - 1))
                          else (true, e1)
                        | none => (true, e1)) =
                        (if Nat.beq q0'' qv && Nat.ble (2 * lD * hiDen qv e1 + 1) (lN * hiNum qv e1) then
                          match findMinExp 50 lN lD qv 2 with
                          | none => (false, e1)
                          | some e0 =>
                            (checkFixedB5 r p a0 b0 c0 d0 qv (some qv) Lcut, minOpt e1 (e0 - 1))
                        else (true, e1)) := by rw [hq1'']
                      rw [hred] at hrem
                      by_cases hcond : (Nat.beq q0'' qv && Nat.ble (2 * lD * hiDen qv e1 + 1) (lN * hiNum qv e1)) = true
                      · simp only [hcond, ↓reduceIte] at hrem
                        rw [Bool.and_eq_true] at hcond
                        have hqv_eq : q0'' = qv := (Iff.of_eq Nat.beq_eq).mp hcond.1
                        have hq_eq : q = qv := le_antisymm hle_q (hqv_eq ▸ hq0''_le)
                        cases hfind : findMinExp 50 lN lD qv 2 with
                        | none => rw [hfind] at hrem; simp at hrem
                        | some e0 =>
                          rw [hfind] at hrem
                          obtain ⟨he0_2, he0_ab, _⟩ := findMinExp_sound 50 lN lD qv 2 e0 hfind
                          cases hfix : checkFixedB5 r p a0 b0 c0 d0 qv (some qv) Lcut
                          · rw [hfix] at hrem; simp at hrem
                          · rw [hfix] at hrem; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrem
                            by_cases hge : e0 ≤ e
                            · rw [← hq_eq] at he0_ab
                              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hdom_eq e0 (by omega) hge he0_ab
                              exact checkFixedB5_sound hr hp hq h5r hrp hpq (by omega) (by omega) he_lo hno3 hab hprim hfix
                            · exact hafter_e1 (minOpt e1 (e0 - 1)) (leOpt_minOpt he1 (by omega)) hrem
                      · simp only [Bool.eq_false_iff.mpr hcond, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hrem
                        exact hafter_e1 e1 he1 hrem
              -- Now dispatch the q_cut step into hafter_cut!
              by_cases hlt : Nat.ble (lN + 1) (2 * lD) = true
              · rw [hlt] at hok; simp only [↓reduceIte] at hok
                have hlt' : lN < 2 * lD := by have := (Iff.of_eq Nat.ble_eq).mp hlt; omega
                let q_cut := (lN - 1) / (2 * lD - lN)
                by_cases hle_cut : Nat.ble q0' q_cut = true
                · rw [hle_cut] at hok; simp only [↓reduceIte] at hok
                  cases hfix : checkFixedB5 r p a0 b0 c0 d0 q0' (minOpt q1'' q_cut) Lcut
                  · rw [hfix] at hok; simp at hok
                  · rw [hfix] at hok; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
                    by_cases hq_le_cut : q ≤ q_cut
                    · have hqD_lt : (2 * lD - lN) * q < lN := by
                        have hmul : q * (2 * lD - lN) ≤ lN - 1 :=
                          (Nat.le_div_iff_mul_le (by omega)).mp hq_le_cut
                        have hlN_pos : 0 < lN := by
                          dsimp [lN]; have := ppSum_pos 3 a0; have := ppSum_pos 5 b0
                          have := ppSum_pos r c0; have := ppSum_pos p d0; positivity
                        rw [mul_comm] at hmul; omega
                      have hq1_ab : 2 * lD * q ^ 1 < lN * ppSum q 1 := by
                        simp only [ppSum, zero_add, pow_one]
                        zify [hlt'.le] at hqD_lt ⊢; nlinarith
                      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hdom_eq 1 le_rfl he_lo hq1_ab
                      exact checkFixedB5_sound hr hp hq h5r hrp hpq hq0'_le (leOpt_minOpt hq1''_le hq_le_cut)
                        he_lo hno3 hab hprim hfix
                    · have hq0''_le : skipUp 50 (q_cut + 1) ≤ q := skipUp_le hq 50 (q_cut + 1) (by omega)
                      have hq0''_2 : 2 ≤ skipUp 50 (q_cut + 1) := by
                        have h1 : q0' ≤ q_cut := (Iff.of_eq Nat.ble_eq).mp hle_cut
                        have h2 := le_skipUp 50 (q_cut + 1)
                        omega
                      exact hafter_cut (skipUp 50 (q_cut + 1)) hq0''_2 hq0''_le hok
                · rw [Bool.eq_false_iff.mpr hle_cut] at hok; simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hok
                  exact hafter_cut q0' hq0'_ge2 hq0'_le hok
              · rw [Bool.eq_false_iff.mpr hlt] at hok; simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hok
                exact hafter_cut q0' hq0'_ge2 hq0'_le hok

/- ### 3d. Chunked `decide +kernel` certificates -/

private def pairs4List : List (ℕ × ℕ) := [
  (17, 19), (17, 23), (17, 29), (17, 31), (17, 37), (17, 41), (17, 43), (17, 47),
  (17, 53), (17, 59), (17, 61), (17, 67), (17, 71), (17, 73), (17, 79), (17, 83),
  (17, 89), (17, 97), (17, 101), (17, 103), (17, 107), (17, 109), (17, 113), (17, 127),
  (17, 131), (17, 137), (17, 139), (17, 149), (17, 151), (17, 157), (17, 163), (17, 167),
  (17, 173), (17, 179), (17, 181), (17, 191), (17, 193), (17, 197), (17, 199), (17, 211),
  (17, 223), (17, 227), (17, 229), (17, 233), (17, 239), (17, 241), (17, 251), (19, 23),
  (19, 29), (19, 31), (19, 37), (19, 41), (19, 43), (19, 47), (19, 53), (19, 59),
  (19, 61), (19, 67), (19, 71), (19, 73), (19, 79), (19, 83), (19, 89), (23, 29),
  (23, 31), (23, 37), (23, 41), (23, 43), (23, 47), (29, 31)
]

private def LcutOf (r : ℕ) : ℕ :=
  if Nat.beq r 17 || Nat.beq r 19 then 12 else 23

private def checkD2Pair (rp : ℕ × ℕ) : Bool :=
  checkD2 40 rp.1 rp.2 2 none 2 none 2 none 2 none

private lemma all_D2_ok : pairs4List.all checkD2Pair = true := by decide +kernel

private def checkBox4Pair (rp : ℕ × ℕ) : Bool :=
  let r := rp.1; let p := rp.2
  let c0 := if Nat.beq (r % 3) 2 then 2 else 1
  let d0 := if Nat.beq (p % 3) 2 then 2 else 1
  checkBox4 40 r p 2 none 2 none c0 none d0 none (LcutOf r)

private lemma all_box4_ok : pairs4List.all checkBox4Pair = true := by decide +kernel

private def checkBox5Pair (rp : ℕ × ℕ) : Bool :=
  let r := rp.1; let p := rp.2
  let c0 := if Nat.beq (r % 3) 2 then 2 else 1
  let d0 := if Nat.beq (p % 3) 2 then 2 else 1
  checkBox5 60 r p 2 none 2 none c0 none d0 none (p + 2) none none (LcutOf r)

private def pairs5_17a : List (ℕ × ℕ) := [
  (17, 19), (17, 23), (17, 29), (17, 31), (17, 37), (17, 41), (17, 43), (17, 47),
  (17, 53), (17, 59), (17, 61), (17, 67), (17, 71), (17, 73), (17, 79), (17, 83),
  (17, 89), (17, 97), (17, 101), (17, 103), (17, 107), (17, 109), (17, 113)
]
private lemma pairs5_17a_ok : pairs5_17a.all checkBox5Pair = true := by decide +kernel

private def pairs5_17b : List (ℕ × ℕ) := [
  (17, 127), (17, 131), (17, 137), (17, 139), (17, 149), (17, 151), (17, 157), (17, 163),
  (17, 167), (17, 173), (17, 179), (17, 181), (17, 191), (17, 193), (17, 197), (17, 199),
  (17, 211), (17, 223), (17, 227), (17, 229), (17, 233), (17, 239), (17, 241)
]
private lemma pairs5_17b_ok : pairs5_17b.all checkBox5Pair = true := by decide +kernel

private def pairs5_17c : List (ℕ × ℕ) := [
  (17, 251), (17, 257), (17, 263), (17, 269), (17, 271), (17, 277), (17, 281), (17, 283),
  (17, 293), (17, 307), (17, 311), (17, 313), (17, 317), (17, 331), (17, 337), (17, 347),
  (17, 349), (17, 353), (17, 359), (17, 367), (17, 373), (17, 379)
]
private lemma pairs5_17c_ok : pairs5_17c.all checkBox5Pair = true := by decide +kernel

private def pairs5_17d : List (ℕ × ℕ) := [
  (17, 383), (17, 389), (17, 397), (17, 401), (17, 409), (17, 419), (17, 421), (17, 431),
  (17, 433), (17, 439), (17, 443), (17, 449), (17, 457), (17, 461), (17, 463), (17, 467),
  (17, 479), (17, 487), (17, 491), (17, 499), (17, 503), (17, 509)
]
private lemma pairs5_17d_ok : pairs5_17d.all checkBox5Pair = true := by decide +kernel

private def pairs5_19a : List (ℕ × ℕ) := [
  (19, 23), (19, 29), (19, 31), (19, 37), (19, 41), (19, 43), (19, 47), (19, 53),
  (19, 59), (19, 61), (19, 67), (19, 71), (19, 73), (19, 79), (19, 83), (19, 89),
  (19, 97), (19, 101)
]
private lemma pairs5_19a_ok : pairs5_19a.all checkBox5Pair = true := by decide +kernel

private def pairs5_19b : List (ℕ × ℕ) := [
  (19, 103), (19, 107), (19, 109), (19, 113), (19, 127), (19, 131), (19, 137), (19, 139),
  (19, 149), (19, 151), (19, 157), (19, 163), (19, 167), (19, 173), (19, 179), (19, 181),
  (19, 191)
]
private lemma pairs5_19b_ok : pairs5_19b.all checkBox5Pair = true := by decide +kernel

private def pairs5_23 : List (ℕ × ℕ) := [
  (23, 29), (23, 31), (23, 37), (23, 41), (23, 43), (23, 47), (23, 53), (23, 59),
  (23, 61), (23, 67), (23, 71), (23, 73), (23, 79), (23, 83), (23, 89), (23, 97)
]
private lemma pairs5_23_ok : pairs5_23.all checkBox5Pair = true := by decide +kernel

private def pairs5_hi : List (ℕ × ℕ) := [
  (29, 31), (29, 37), (29, 41), (29, 43), (29, 47), (29, 53), (29, 59), (29, 61),
  (29, 67), (31, 37), (31, 41), (31, 43), (31, 47), (31, 53), (31, 59), (31, 61),
  (37, 41), (37, 43), (37, 47), (37, 53), (41, 43), (41, 47)
]
private lemma pairs5_hi_ok : pairs5_hi.all checkBox5Pair = true := by decide +kernel

private def pairs5List : List (ℕ × ℕ) :=
  pairs5_17a ++ pairs5_17b ++ pairs5_17c ++ pairs5_17d ++
  pairs5_19a ++ pairs5_19b ++ pairs5_23 ++ pairs5_hi

private lemma all_box5_ok : pairs5List.all checkBox5Pair = true := by
  simp only [pairs5List, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨pairs5_17a_ok, pairs5_17b_ok⟩, pairs5_17c_ok⟩, pairs5_17d_ok⟩,
    pairs5_19a_ok⟩, pairs5_19b_ok⟩, pairs5_23_ok⟩, pairs5_hi_ok⟩

end SmallExcess

/- ## Section 4: Classification and main assembly -/

section MainProof

private lemma not_div3_of_dvd_sigma_five_odd {b : ℕ} (hb : b % 2 = 1) : 6 ∣ ppSum 5 b := by
  have h : ∀ k : ℕ, 6 ∣ ppSum 5 (2 * k + 1) := by
    intro k
    induction k with
    | zero => simp [ppSum]
    | succ k ih =>
      have h1 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      rw [h1, ppSum, ppSum]
      have h2 : 5 ^ (2 * k + 1 + 1) + 5 ^ (2 * k + 1 + 1 + 1) = 6 * 5 ^ (2 * k + 1 + 1) := by
        rw [pow_succ]; ring
      rw [add_assoc, h2]
      exact dvd_add ih (dvd_mul_right 6 _)
  obtain ⟨k, hk⟩ : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
  rw [hk]; exact h k

private lemma sigma_even_of_odd_exp {p e : ℕ} (hp : Odd p) (he : e % 2 = 1) :
    2 ∣ ppSum p e := by
  have h : ∀ k : ℕ, 2 ∣ ppSum p (2 * k + 1) := by
    intro k
    induction k with
    | zero =>
      simp [ppSum]; obtain ⟨m, hm⟩ := hp; exact ⟨m + 1, by omega⟩
    | succ k ih =>
      have h1 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      rw [h1, ppSum, ppSum]
      have h2 : p ^ (2 * k + 1 + 1) + p ^ (2 * k + 1 + 1 + 1) = (p + 1) * p ^ (2 * k + 1 + 1) := by
        rw [pow_succ]; ring
      rw [add_assoc, h2]
      obtain ⟨m, hm⟩ := hp
      exact dvd_add ih (dvd_mul_of_dvd_left ⟨m + 1, by omega⟩ _)
  obtain ⟨k, hk⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
  rw [hk]; exact h k

private lemma d_ge_two_of_odd_exp {n : ℕ} (hn : Odd n) (hdef : sigma 1 n < 2 * n)
    (heven : 2 ∣ sigma 1 n) : 2 ≤ n - properDivsSum n := by
  have h := properDivsSum_eq_sigma_sub (n := n)
  obtain ⟨k, hk⟩ := heven
  omega

private lemma d_ge_two_three_primes {r a b c : ℕ} (hr : r.Prime) (h17 : 17 ≤ r)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    2 ≤ 3 ^ a * 5 ^ b * r ^ c - properDivsSum (3 ^ a * 5 ^ b * r ^ c) := by
  let B := 3 ^ a * 5 ^ b * r ^ c
  have hsig := sigma_three_primes hr (by omega) (a := a) (b := b) (c := c)
  have h3 := ppSum_lt_lim (p := 3) (e := a) (by decide)
  have h5 := ppSum_lt_lim (p := 5) (e := b) (by decide)
  have hr' := ppSum_lt_lim (p := r) (e := c) hr.two_le
  have hrr : r * 16 ≤ 17 * (r - 1) := by omega
  have h1 : ppSum r c * 16 ≤ 17 * r ^ c := by
    apply Nat.le_of_mul_le_mul_right _ (show 0 < r - 1 by omega)
    calc ppSum r c * 16 * (r - 1) = (ppSum r c * (r - 1)) * 16 := by ring
      _ ≤ (r * r ^ c) * 16 := Nat.mul_le_mul_right 16 hr'.le
      _ = (r * 16) * r ^ c := by ring
      _ ≤ (17 * (r - 1)) * r ^ c := Nat.mul_le_mul_right _ hrr
      _ = 17 * r ^ c * (r - 1) := by ring
  have hprod : ppSum 3 a * ppSum 5 b * ppSum r c * 128 ≤ 255 * B := by
    have h12 := Nat.mul_le_mul h3.le h5.le
    have h123 := Nat.mul_le_mul h12 h1
    dsimp [B]; linarith
  have hBge : 256 ≤ B := by
    dsimp [B]
    have h1' : 9 ≤ 3 ^ a := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 3) ha
    have h2' : 5 ≤ 5 ^ b := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 5) hb
    have h3' : 17 ≤ r ^ c := le_trans h17 (by simpa using pow_le_pow_right₀ hr.one_lt.le hc)
    nlinarith [Nat.mul_le_mul (Nat.mul_le_mul h1' h2') h3']
  have hP := properDivsSum_eq_sigma_sub (n := B)
  rw [hsig] at hP
  change 2 ≤ B - properDivsSum B
  omega

private lemma d_ge_two_four_primes {r p a b c d : ℕ} (hr : r.Prime) (hp : p.Prime)
    (h17 : 17 ≤ r) (hrp : r < p) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hmem : (r, p) ∈ pairs5List)
    (hdef : sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d) < 2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d)) :
    2 ≤ 3 ^ a * 5 ^ b * r ^ c * p ^ d - properDivsSum (3 ^ a * 5 ^ b * r ^ c * p ^ d) := by
  let B := 3 ^ a * 5 ^ b * r ^ c * p ^ d
  have hBodd : Odd B := by
    have hro : Odd r := hr.odd_of_ne_two (by omega)
    have hpo : Odd p := hp.odd_of_ne_two (by omega)
    exact ((Odd.pow (by decide : Odd 3) |>.mul (Odd.pow (by decide : Odd 5))).mul
      (Odd.pow hro)).mul (Odd.pow hpo)
  have hsig := sigma_four_primes hr hp (by omega) hrp (a := a) (b := b) (c := c) (d := d)
  by_cases hae : a % 2 = 1
  · exact d_ge_two_of_odd_exp hBodd hdef (by rw [hsig]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (sigma_even_of_odd_exp (by decide) hae) _) _) _)
  by_cases hbe : b % 2 = 1
  · exact d_ge_two_of_odd_exp hBodd hdef (by rw [hsig]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (sigma_even_of_odd_exp (by decide) hbe) _) _) _)
  by_cases hce : c % 2 = 1
  · exact d_ge_two_of_odd_exp hBodd hdef (by rw [hsig]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (sigma_even_of_odd_exp (hr.odd_of_ne_two (by omega)) hce) _) _)
  by_cases hde : d % 2 = 1
  · exact d_ge_two_of_odd_exp hBodd hdef (by rw [hsig]; exact dvd_mul_of_dvd_right (sigma_even_of_odd_exp (hp.odd_of_ne_two (by omega)) hde) _)
  -- All 4 exponents are even!
  have hb2 : 2 ≤ b := by omega
  have hc2 : 2 ≤ c := by omega
  have hd2 : 2 ≤ d := by omega
  by_cases hlim4 : 16 * (r - 1) * (p - 1) < 15 * r * p
  · have hmem4 : (r, p) ∈ pairs4List := by
      have htest : pairs5List.all (fun x =>
          if Nat.ble (16 * (x.1 - 1) * (x.2 - 1) + 1) (15 * x.1 * x.2) then pairs4List.contains x else true) = true := by
        decide +kernel
      have h1 := List.all_eq_true.mp htest (r, p) hmem
      have h2 : Nat.ble (16 * (r - 1) * (p - 1) + 1) (15 * r * p) = true := (Iff.of_eq Nat.ble_eq).mpr (by omega)
      rw [h2] at h1
      exact List.contains_iff_mem.mp (by simpa using h1)
    have hok := List.all_eq_true.mp all_D2_ok (r, p) hmem4
    have hres := checkD2_sound 40 r p 2 none 2 none 2 none 2 none a b c d
      hr hp (by omega) hrp ha trivial (by omega) (by decide)
      hb2 trivial (by omega) (by decide) hc2 trivial (by omega) (by decide)
      hd2 trivial (by omega) (by decide) hdef hok
    have hP := properDivsSum_eq_sigma_sub (n := 3 ^ a * 5 ^ b * r ^ c * p ^ d)
    show 2 ≤ 3 ^ a * 5 ^ b * r ^ c * p ^ d - properDivsSum (3 ^ a * 5 ^ b * r ^ c * p ^ d)
    omega
  · -- lim4 <= 2 (in fact < 2 since no prime pair gives equality!)
    have hlt4 : 15 * r * p < 16 * (r - 1) * (p - 1) := by
      have hneq : pairs5List.all (fun x => !(Nat.beq (15 * x.1 * x.2) (16 * (x.1 - 1) * (x.2 - 1)))) = true := by
        decide +kernel
      have h1 := List.all_eq_true.mp hneq (r, p) hmem
      simp only [Bool.not_eq_true'] at h1
      have hne : 15 * r * p ≠ 16 * (r - 1) * (p - 1) := fun heq => by
        have := (Iff.of_eq Nat.beq_eq).mpr heq; rw [this] at h1; exact Bool.noConfusion h1
      omega
    have h3 := ppSum_lt_lim (p := 3) (e := a) (by decide)
    have h5 := ppSum_lt_lim (p := 5) (e := b) (by decide)
    have hr' := ppSum_lt_lim (p := r) (e := c) hr.two_le
    have hp' := ppSum_lt_lim (p := p) (e := d) hp.two_le
    have hprod : ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * (8 * (r - 1) * (p - 1)) ≤ 15 * r * p * B := by
      have h12 := Nat.mul_le_mul h3.le h5.le
      have h34 := Nat.mul_le_mul hr'.le hp'.le
      have h1234 := Nat.mul_le_mul h12 h34
      dsimp [B]; linarith
    have hBge : 16 * (r - 1) * (p - 1) ≤ B := by
      dsimp [B]
      have h1' : 9 ≤ 3 ^ a := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 3) ha
      have h2' : 5 ≤ 5 ^ b := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 5) hb
      have h3' : r ≤ r ^ c := by simpa using pow_le_pow_right₀ hr.one_lt.le hc
      have h4' : p ≤ p ^ d := by simpa using pow_le_pow_right₀ hp.one_lt.le hd
      have h45 : 45 * r * p ≤ B := by
        have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1' h2') h3') h4'
        dsimp [B]; linarith
      have : (r - 1) * (p - 1) ≤ r * p := Nat.mul_le_mul (Nat.sub_le r 1) (Nat.sub_le p 1)
      have h16 : 16 * (r - 1) * (p - 1) ≤ 45 * r * p := by
        calc 16 * (r - 1) * (p - 1) = 16 * ((r - 1) * (p - 1)) := by ring
          _ ≤ 16 * (r * p) := Nat.mul_le_mul_left _ this
          _ ≤ 45 * (r * p) := Nat.mul_le_mul_right _ (by decide)
          _ = 45 * r * p := by ring
      exact le_trans h16 h45
    have hP := properDivsSum_eq_sigma_sub (n := B)
    rw [hsig] at hP
    have hgap : (2 * B - ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d) * (8 * (r - 1) * (p - 1)) ≥
        2 * (8 * (r - 1) * (p - 1)) := by
      have h1 : 1 ≤ 16 * (r - 1) * (p - 1) - 15 * r * p := by omega
      have h2 : 16 * (r - 1) * (p - 1) ≤ B * (16 * (r - 1) * (p - 1) - 15 * r * p) :=
        le_trans hBge (Nat.le_mul_of_pos_right B h1)
      have hdef' : ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d < 2 * B := by
        rw [hsig] at hdef; exact hdef
      have hr1 : 1 ≤ r := by omega
      have hp1 : 1 ≤ p := by omega
      zify [hdef'.le, hlt4.le, hr1, hp1] at hprod h2 ⊢
      nlinarith
    have hden_pos : 0 < 8 * (r - 1) * (p - 1) := by
      have : 1 ≤ r - 1 := by omega
      have : 1 ≤ p - 1 := by omega
      positivity
    have hge2 : 2 ≤ 2 * B - ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d :=
      Nat.le_of_mul_le_mul_right hgap hden_pos
    change 2 ≤ B - properDivsSum B
    omega

private lemma lift_base3_core' (bd : Base3Data) (hmem : bd ∈ bases3List)
    (hr : bd.r.Prime) (h5r : 5 < bd.r)
    (e1 : bd.P0 = ppSum 3 bd.a0 * ppSum 5 bd.b0 * ppSum bd.r 1 - 3 ^ bd.a0 * 5 ^ bd.b0 * bd.r)
    (e2 : bd.dsUr.sum = ppSum 3 bd.a0 * ppSum 5 bd.b0 * ppSum bd.r 0 - 3 ^ bd.a0 * 5 ^ bd.b0)
    (e3 : bd.dsU5.sum = ppSum 3 bd.a0 * ppSum 5 0 * ppSum bd.r 1 - 3 ^ bd.a0 * bd.r)
    (e4 : bd.dsU3.sum = ppSum 3 0 * ppSum 5 bd.b0 * ppSum bd.r 1 - 5 ^ bd.b0 * bd.r)
    {a b c : ℕ} (ha : bd.a0 ≤ a) (hb : bd.b0 ≤ b) (hc : 1 ≤ c) :
    let B := 3 ^ a * 5 ^ b * bd.r ^ c
    (∀ y, bd.L ≤ y → y ≤ properDivsSum B - bd.L → repNat B.properDivisors y) ∧
    (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
    (∀ x, 0 < x → x < bd.L → x % bd.modStep = 0 → repNat B.properDivisors x) ∧
    (5 * (2 * bd.L + 24) ≤ properDivsSum B) ∧
    (2 * bd.L ≤ properDivsSum B) ∧
    (bd.maxP * 2 ≤ properDivsSum B - 2 * bd.L + 1) ∧
    (B + 2 * bd.L ≤ properDivsSum B + 19 * properDivsSum B + 1) := by
  have h1 := properDivsSum_35r hr h5r (a := bd.a0) (b := bd.b0) (c := 1)
  have h2 := properDivsSum_35r hr h5r (a := bd.a0) (b := bd.b0) (c := 0)
  have h3 := properDivsSum_35r hr h5r (a := bd.a0) (b := 0) (c := 1)
  have h4 := properDivsSum_35r hr h5r (a := 0) (b := bd.b0) (c := 1)
  rw [pow_one] at h1
  rw [pow_zero, mul_one] at h2
  rw [pow_zero, pow_one, mul_one] at h3
  rw [pow_zero, pow_one, one_mul] at h4
  exact lift_base3_core bd hmem hr h5r (e1.trans h1.symm) (e2.trans h2.symm)
    (e3.trans h3.symm) (e4.trans h4.symm) ha hb hc

-- Helper: look up a Base3Data in bases3List and apply lift_base3_core!
private lemma base3_for_odd {r a b c : ℕ} (hr : r.Prime) (h5r : 5 < r)
    (ha : 4 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hr_mem : r ∈ ([17, 19, 23, 29, 31, 37, 41] : List ℕ)) :
    ∃ L maxP : ℕ,
      (r = 17 → maxP = 509) ∧ (r = 19 → maxP = 191) ∧ (r = 23 → maxP = 97) ∧
      (r = 29 → maxP = 67) ∧ (r = 31 → maxP = 61) ∧ (r = 37 → maxP = 53) ∧ (r = 41 → maxP = 47) ∧
      1 ≤ L ∧
      let B := 3 ^ a * 5 ^ b * r ^ c
      (∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y) ∧
      (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
      (∀ x, 0 < x → x < L → x % 6 = 0 → repNat B.properDivisors x) ∧
      (5 * (2 * L + 24) ≤ properDivsSum B) ∧
      (2 * L ≤ properDivsSum B) ∧
      (maxP * 2 ≤ properDivsSum B - 2 * L + 1) ∧
      (B + 2 * L ≤ properDivsSum B + 19 * properDivsSum B + 1) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
  have hP35r : ∀ (a0 b0 r0 : ℕ), r0.Prime → 5 < r0 →
      properDivsSum (3 ^ a0 * 5 ^ b0 * r0) = ppSum 3 a0 * ppSum 5 b0 * ppSum r0 1 - 3 ^ a0 * 5 ^ b0 * r0 := by
    intro a0 b0 r0 hr0 h5
    simpa using properDivsSum_35r hr0 h5 (a := a0) (b := b0) (c := 1)
  have hP35 : ∀ (a0 b0 : ℕ),
      properDivsSum (3 ^ a0 * 5 ^ b0) = ppSum 3 a0 * ppSum 5 b0 - 3 ^ a0 * 5 ^ b0 := by
    intro a0 b0
    have h := properDivsSum_35r (by decide : Nat.Prime 7) (by decide) (a := a0) (b := b0) (c := 0)
    simpa [ppSum] using h
  have hP3r : ∀ (a0 r0 : ℕ), r0.Prime → 5 < r0 →
      properDivsSum (3 ^ a0 * r0) = ppSum 3 a0 * ppSum r0 1 - 3 ^ a0 * r0 := by
    intro a0 r0 hr0 h5
    have h := properDivsSum_35r hr0 h5 (a := a0) (b := 0) (c := 1)
    simpa [ppSum] using h
  have hP5r : ∀ (b0 r0 : ℕ), r0.Prime → 5 < r0 →
      properDivsSum (5 ^ b0 * r0) = ppSum 5 b0 * ppSum r0 1 - 5 ^ b0 * r0 := by
    intro b0 r0 hr0 h5
    have h := properDivsSum_35r hr0 h5 (a := 0) (b := b0) (c := 1)
    simpa [ppSum] using h
  rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := lift_base3_core' (bases3List[2]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨12, 509, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by decide, h⟩
  · have h := lift_base3_core' (bases3List[3]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨27, 191, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by decide, h⟩
  · have h := lift_base3_core' (bases3List[4]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨35, 97, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by decide, h⟩
  · have h := lift_base3_core' (bases3List[5]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨68, 67, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by decide, h⟩
  · have h := lift_base3_core' (bases3List[6]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨39, 61, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by decide, h⟩
  · have h := lift_base3_core' (bases3List[7]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨72, 53, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by decide, h⟩
  · have h := lift_base3_core' (bases3List[8]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨80, 47, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by decide, h⟩

private lemma base3_for_a3_odd {r a b c : ℕ} (hr : r.Prime) (h5r : 5 < r)
    (ha : 3 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hr_mem : r = 17 ∨ r = 19) :
    ∃ L maxP : ℕ,
      (r = 17 → maxP = 31) ∧ (r = 19 → maxP = 29) ∧ 1 ≤ L ∧
      let B := 3 ^ a * 5 ^ b * r ^ c
      (∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y) ∧
      (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
      (∀ x, 0 < x → x < L → x % 6 = 0 → repNat B.properDivisors x) ∧
      (5 * (2 * L + 24) ≤ properDivsSum B) ∧
      (2 * L ≤ properDivsSum B) ∧
      (maxP * 2 ≤ properDivsSum B - 2 * L + 1) ∧
      (B + 2 * L ≤ properDivsSum B + 19 * properDivsSum B + 1) := by
  have hP35r : ∀ (a0 b0 r0 : ℕ), r0.Prime → 5 < r0 →
      properDivsSum (3 ^ a0 * 5 ^ b0 * r0) = ppSum 3 a0 * ppSum 5 b0 * ppSum r0 1 - 3 ^ a0 * 5 ^ b0 * r0 := by
    intro a0 b0 r0 hr0 h5; simpa using properDivsSum_35r hr0 h5 (a := a0) (b := b0) (c := 1)
  have hP35 : ∀ (a0 b0 : ℕ),
      properDivsSum (3 ^ a0 * 5 ^ b0) = ppSum 3 a0 * ppSum 5 b0 - 3 ^ a0 * 5 ^ b0 := by
    intro a0 b0; simpa [ppSum] using properDivsSum_35r (by decide : Nat.Prime 7) (by decide) (a := a0) (b := b0) (c := 0)
  have hP3r : ∀ (a0 r0 : ℕ), r0.Prime → 5 < r0 →
      properDivsSum (3 ^ a0 * r0) = ppSum 3 a0 * ppSum r0 1 - 3 ^ a0 * r0 := by
    intro a0 r0 hr0 h5; simpa [ppSum] using properDivsSum_35r hr0 h5 (a := a0) (b := 0) (c := 1)
  have hP5r : ∀ (b0 r0 : ℕ), r0.Prime → 5 < r0 →
      properDivsSum (5 ^ b0 * r0) = ppSum 5 b0 * ppSum r0 1 - 5 ^ b0 * r0 := by
    intro b0 r0 hr0 h5; simpa [ppSum] using properDivsSum_35r hr0 h5 (a := 0) (b := b0) (c := 1)
  rcases hr_mem with rfl | rfl
  · have h := lift_base3_core' (bases3List[0]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨12, 31, by omega, by omega, by decide, h⟩
  · have h := lift_base3_core' (bases3List[1]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨27, 29, by omega, by omega, by decide, h⟩

private lemma base3_for_b2 {r a b c : ℕ} (hr : r.Prime) (h5r : 5 < r)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 1 ≤ c)
    (ha_hi : 29 ≤ r → 3 ≤ a)
    (hr_mem : r ∈ ([17, 19, 23, 29, 31, 37, 41] : List ℕ)) :
    ∃ maxP : ℕ,
      (r = 17 → maxP = 509) ∧ (r = 19 → maxP = 191) ∧ (r = 23 → maxP = 97) ∧
      (r = 29 → maxP = 67) ∧ (r = 31 → maxP = 61) ∧ (r = 37 → maxP = 53) ∧ (r = 41 → maxP = 47) ∧
      let L := LcutOf r
      let B := 3 ^ a * 5 ^ b * r ^ c
      (∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y) ∧
      (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
      (∀ x, 0 < x → x < L → x % 3 = 0 → repNat B.properDivisors x) ∧
      (5 * (2 * L + 24) ≤ properDivsSum B) ∧
      (2 * L ≤ properDivsSum B) ∧
      (maxP * 2 ≤ properDivsSum B - 2 * L + 1) ∧
      (B + 2 * L ≤ properDivsSum B + 19 * properDivsSum B + 1) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
  have hP35r : ∀ (a0 b0 r0 : ℕ), r0.Prime → 5 < r0 →
      properDivsSum (3 ^ a0 * 5 ^ b0 * r0) = ppSum 3 a0 * ppSum 5 b0 * ppSum r0 1 - 3 ^ a0 * 5 ^ b0 * r0 := by
    intro a0 b0 r0 hr0 h5; simpa using properDivsSum_35r hr0 h5 (a := a0) (b := b0) (c := 1)
  have hP35 : ∀ (a0 b0 : ℕ),
      properDivsSum (3 ^ a0 * 5 ^ b0) = ppSum 3 a0 * ppSum 5 b0 - 3 ^ a0 * 5 ^ b0 := by
    intro a0 b0; simpa [ppSum] using properDivsSum_35r (by decide : Nat.Prime 7) (by decide) (a := a0) (b := b0) (c := 0)
  have hP3r : ∀ (a0 r0 : ℕ), r0.Prime → 5 < r0 →
      properDivsSum (3 ^ a0 * r0) = ppSum 3 a0 * ppSum r0 1 - 3 ^ a0 * r0 := by
    intro a0 r0 hr0 h5; simpa [ppSum] using properDivsSum_35r hr0 h5 (a := a0) (b := 0) (c := 1)
  have hP5r : ∀ (b0 r0 : ℕ), r0.Prime → 5 < r0 →
      properDivsSum (5 ^ b0 * r0) = ppSum 5 b0 * ppSum r0 1 - 5 ^ b0 * r0 := by
    intro b0 r0 hr0 h5; simpa [ppSum] using properDivsSum_35r hr0 h5 (a := 0) (b := b0) (c := 1)
  rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := lift_base3_core' (bases3List[9]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨509, by omega, by omega, by omega, by omega, by omega, by omega, by omega, h⟩
  · have h := lift_base3_core' (bases3List[10]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨191, by omega, by omega, by omega, by omega, by omega, by omega, by omega, h⟩
  · have h := lift_base3_core' (bases3List[11]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha hb hc
    exact ⟨97, by omega, by omega, by omega, by omega, by omega, by omega, by omega, h⟩
  · have ha3 := ha_hi (by decide)
    have h := lift_base3_core' (bases3List[12]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha3 hb hc
    exact ⟨67, by omega, by omega, by omega, by omega, by omega, by omega, by omega, h⟩
  · have ha3 := ha_hi (by decide)
    have h := lift_base3_core' (bases3List[13]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha3 hb hc
    exact ⟨61, by omega, by omega, by omega, by omega, by omega, by omega, by omega, h⟩
  · have ha3 := ha_hi (by decide)
    have h := lift_base3_core' (bases3List[14]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha3 hb hc
    exact ⟨53, by omega, by omega, by omega, by omega, by omega, by omega, by omega, h⟩
  · have ha3 := ha_hi (by decide)
    have h := lift_base3_core' (bases3List[15]'(by decide)) (List.getElem_mem _) hr h5r
      (by decide) (by decide) (by decide) (by decide) ha3 hb hc
    exact ⟨47, by omega, by omega, by omega, by omega, by omega, by omega, by omega, h⟩

private lemma finish_from_core {B q e L : ℕ} (hB1 : 1 < B) (hq : q.Prime) (hcop : B.Coprime q)
    (hq3 : 3 ≤ q) (hL1 : 1 ≤ L) (he : 1 ≤ e)
    (hab : (B * q ^ e).Abundant)
    (hprim : ∀ x ∈ (B * q ^ e).properDivisors, x.Deficient)
    (hbig : 5 * (2 * L + 24) ≤ properDivsSum B)
    (hcov : ∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y)
    (hgap : ∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + 2 ∧ i ≤ k)
    (hD2 : e = 1 → 2 ≤ B - properDivsSum B)
    (hsmall : sigma 1 (B * q ^ e) - 2 * (B * q ^ e) < L →
      repNat B.properDivisors (sigma 1 (B * q ^ e) - 2 * (B * q ^ e))) :
    (B * q ^ e).Pseudoperfect := by
  have hmpos : 0 < B * q ^ e := by have := hq.pos; positivity
  have hmab : 2 * (B * q ^ e) < sigma 1 (B * q ^ e) := (abund_iff_nat hmpos).mp hab
  by_cases hE_lt : sigma 1 (B * q ^ e) - 2 * (B * q ^ e) < L
  · obtain ⟨s, hs, hsum⟩ := hsmall hE_lt
    have hsub : s ⊆ (B * q ^ e).properDivisors := by
      intro x hx
      obtain ⟨hd1, hd2⟩ := Nat.mem_properDivisors.mp (hs hx)
      exact Nat.mem_properDivisors.mpr ⟨hd1.trans (dvd_mul_right B _),
        lt_of_lt_of_le hd2 (Nat.le_mul_of_pos_right B (pow_pos hq.pos e))⟩
    exact pseudoperfect_of_excess hmpos hsub (by
      have : (∑ d ∈ s, (d : ℤ)) = ((∑ d ∈ s, d : ℕ) : ℤ) := by simp
      rw [this, hsum]; omega)
  · obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
    exact certified_prime_power_gen hB1 hq hcop hq3 (by decide) hL1 hprim
      (by
        have hle : 2 * (B * q ^ (j + 1)) ≤ sigma 1 (B * q ^ (j + 1)) := hmab.le
        have hL : L ≤ sigma 1 (B * q ^ (j + 1)) - 2 * (B * q ^ (j + 1)) := by omega
        zify [hle] at hL ⊢; push_cast at hL ⊢; exact hL)
      hbig (fun hj => hD2 (by omega)) hcov hgap

set_option maxHeartbeats 1600000 in
private lemma solve_omega4 {r p a b c d : ℕ}
    (hr : r.Prime) (hp : p.Prime) (h17 : 17 ≤ r) (hrp : r < p)
    (hr_mem : r ∈ ([17, 19, 23, 29, 31, 37, 41, 43] : List ℕ))
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hab : (3 ^ a * 5 ^ b * r ^ c * p ^ d).Abundant)
    (hprim : ∀ x ∈ (3 ^ a * 5 ^ b * r ^ c * p ^ d).properDivisors, x.Deficient) :
    (3 ^ a * 5 ^ b * r ^ c * p ^ d).Pseudoperfect := by
  set M := 3 ^ a * 5 ^ b * r ^ c * p ^ d
  have hMpos : 0 < M := by have := hr.pos; have := hp.pos; positivity
  have hsig := sigma_four_primes hr hp (by omega) hrp (a := a) (b := b) (c := c) (d := d)
  have hMab : 2 * M < ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d := by
    have h1 := (abund_iff_nat hMpos).mp hab; rwa [hsig] at h1
  -- Ratio bound: 16 * (r - 1) * (p - 1) < 15 * r * p
  have hlim4 : 16 * (r - 1) * (p - 1) < 15 * r * p := by
    have h3 := ppSum_lt_lim (p := 3) (e := a) (by decide)
    have h5 := ppSum_lt_lim (p := 5) (e := b) (by decide)
    have hr' := ppSum_lt_lim (p := r) (e := c) hr.two_le
    have hp' := ppSum_lt_lim (p := p) (e := d) hp.two_le
    have hprod : ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * (8 * (r - 1) * (p - 1)) ≤ 15 * r * p * M := by
      have := Nat.mul_le_mul (Nat.mul_le_mul h3.le h5.le) (Nat.mul_le_mul hr'.le hp'.le)
      dsimp [M]; linarith
    have hden_pos : 0 < 8 * (r - 1) * (p - 1) := by
      have : 1 ≤ r - 1 := by omega
      have : 1 ≤ p - 1 := by omega
      positivity
    have h1 := Nat.mul_lt_mul_of_pos_right hMab hden_pos
    exact Nat.lt_of_mul_lt_mul_right (show 16 * (r - 1) * (p - 1) * M < 15 * r * p * M by linarith)
  have hr_le29 : r ∈ ([17, 19, 23, 29] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem ⊢
    rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    all_goals omega
  have hr_mem7 : r ∈ ([17, 19, 23, 29, 31, 37, 41] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_le29 ⊢
    rcases hr_le29 with rfl | rfl | rfl | rfl <;> tauto
  have hmem4 : (r, p) ∈ pairs4List := by
    have hp_lt : p < 256 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_le29
      rcases hr_le29 with rfl | rfl | rfl | rfl <;> omega
    have hchk : ∀ i : Fin 256, i.val.Prime →
        ∀ r0 ∈ ([17, 19, 23, 29] : List ℕ), r0 < i.val →
        16 * (r0 - 1) * (i.val - 1) < 15 * r0 * i.val →
        (r0, i.val) ∈ pairs4List := by decide +kernel
    exact hchk ⟨p, hp_lt⟩ hp r hr_le29 hrp hlim4
  let B := 3 ^ a * 5 ^ b * r ^ c
  have hB1 : 1 < B := by
    dsimp [B]
    have h1 : 9 ≤ 3 ^ a := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 3) ha
    have h2 : 1 ≤ 5 ^ b := Nat.one_le_pow _ _ (by decide)
    have h3 : 1 ≤ r ^ c := Nat.one_le_pow _ _ hr.pos
    have h23 : 1 ≤ 5 ^ b * r ^ c := Nat.mul_pos h2 h3
    nlinarith
  have hcop : B.Coprime p := by
    dsimp [B]
    have h3p : Nat.Coprime (3 ^ a) p := ((Nat.coprime_primes (by decide) hp).mpr (by omega)).pow_left a
    have h5p : Nat.Coprime (5 ^ b) p := ((Nat.coprime_primes (by decide) hp).mpr (by omega)).pow_left b
    have hrp' : Nat.Coprime (r ^ c) p := ((Nat.coprime_primes hr hp).mpr (by omega)).pow_left c
    exact (h3p.mul_left h5p).mul_left hrp'
  have hD2 : d = 1 → 2 ≤ B - properDivsSum B := fun _ => d_ge_two_three_primes hr h17 ha hb hc
  by_cases hb1 : b = 1
  · -- b = 1: must have a >= 4 (since a <= 3 gives max ratio (16/9)*(17/16)*(19/18) = 323/162 < 2)!
    have ha4 : 4 ≤ a := by
      by_contra hlt
      have ha3 : a ≤ 3 := by omega
      have h3 := ppSum_mono_exp (p := 3) (by decide) ha3
      have h5 : ppSum 5 b = 6 := by rw [hb1]; decide
      have hr' := ppSum_lt_lim (p := r) (e := c) hr.two_le
      have hp' := ppSum_lt_lim (p := p) (e := d) hp.two_le
      have hp19 : 19 ≤ p := by
        obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega); omega
      have hrr : r * 16 ≤ 17 * (r - 1) := by omega
      have hpp : p * 18 ≤ 19 * (p - 1) := by omega
      have h1r : ppSum r c * 16 ≤ 17 * r ^ c := by
        apply Nat.le_of_mul_le_mul_right _ (show 0 < r - 1 by omega)
        calc ppSum r c * 16 * (r - 1) = (ppSum r c * (r - 1)) * 16 := by ring
          _ ≤ (r * r ^ c) * 16 := Nat.mul_le_mul_right 16 hr'.le
          _ = (r * 16) * r ^ c := by ring
          _ ≤ (17 * (r - 1)) * r ^ c := Nat.mul_le_mul_right _ hrr
          _ = 17 * r ^ c * (r - 1) := by ring
      have h1p : ppSum p d * 18 ≤ 19 * p ^ d := by
        apply Nat.le_of_mul_le_mul_right _ (show 0 < p - 1 by omega)
        calc ppSum p d * 18 * (p - 1) = (ppSum p d * (p - 1)) * 18 := by ring
          _ ≤ (p * p ^ d) * 18 := Nat.mul_le_mul_right 18 hp'.le
          _ = (p * 18) * p ^ d := by ring
          _ ≤ (19 * (p - 1)) * p ^ d := Nat.mul_le_mul_right _ hpp
          _ = 19 * p ^ d * (p - 1) := by ring
      have h3v : ppSum 3 3 = 40 := by decide
      rw [h3v] at h3
      have h35 : ppSum 3 a * ppSum 5 b * 135 ≤ 240 * (3 ^ a * 5 ^ b) := by
        rw [h5, hb1]; linarith
      have hprod : ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * (135 * 16 * 18) ≤
          240 * 17 * 19 * M := by
        have := Nat.mul_le_mul h35 (Nat.mul_le_mul h1r h1p); dsimp [M]; linarith
      have hlt2 := Nat.mul_lt_mul_of_pos_right hMab (by decide : 0 < 135 * 16 * 18)
      linarith
    obtain ⟨L, _, _, _, _, _, _, _, _, hL1, hcov, hgap, hmod6, hbig, _, _, _⟩ :=
      base3_for_odd hr (by omega) ha4 hb hc hr_mem7
    apply finish_from_core hB1 hp hcop (by omega) hL1 hd hab hprim hbig hcov hgap hD2
    intro hElt
    have h6sig : 6 ∣ sigma 1 M := by
      rw [hsig]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
        (not_div3_of_dvd_sigma_five_odd (by omega)) _) _) _
    have h6M : 6 ∣ 2 * M := by
      have h3M : 3 ∣ M := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_pow_self 3 (by omega)) _) _) _
      obtain ⟨k, hk⟩ := h3M; exact ⟨k, by omega⟩
    have h6E : 6 ∣ sigma 1 M - 2 * M := Nat.dvd_sub h6sig h6M
    exact hmod6 (sigma 1 M - 2 * M) (by rw [hsig]; omega) hElt (Nat.mod_eq_zero_of_dvd h6E)
  · -- b >= 2!
    have hb2 : 2 ≤ b := by omega
    have ha_hi : 29 ≤ r → 3 ≤ a := by
      intro hr29
      by_contra hlt
      have ha2 : a = 2 := by omega
      have h3 : ppSum 3 a = 13 := by rw [ha2]; decide
      have h5 := ppSum_lt_lim (p := 5) (e := b) (by decide)
      have hr' := ppSum_lt_lim (p := r) (e := c) hr.two_le
      have hp' := ppSum_lt_lim (p := p) (e := d) hp.two_le
      have hp31 : 31 ≤ p := by
        obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega); omega
      have hrr : r * 28 ≤ 29 * (r - 1) := by omega
      have hpp : p * 30 ≤ 31 * (p - 1) := by omega
      have h1r : ppSum r c * 28 ≤ 29 * r ^ c := by
        apply Nat.le_of_mul_le_mul_right _ (show 0 < r - 1 by omega)
        calc ppSum r c * 28 * (r - 1) = (ppSum r c * (r - 1)) * 28 := by ring
          _ ≤ (r * r ^ c) * 28 := Nat.mul_le_mul_right 28 hr'.le
          _ = (r * 28) * r ^ c := by ring
          _ ≤ (29 * (r - 1)) * r ^ c := Nat.mul_le_mul_right _ hrr
          _ = 29 * r ^ c * (r - 1) := by ring
      have h1p : ppSum p d * 30 ≤ 31 * p ^ d := by
        apply Nat.le_of_mul_le_mul_right _ (show 0 < p - 1 by omega)
        calc ppSum p d * 30 * (p - 1) = (ppSum p d * (p - 1)) * 30 := by ring
          _ ≤ (p * p ^ d) * 30 := Nat.mul_le_mul_right 30 hp'.le
          _ = (p * 30) * p ^ d := by ring
          _ ≤ (31 * (p - 1)) * p ^ d := Nat.mul_le_mul_right _ hpp
          _ = 31 * p ^ d * (p - 1) := by ring
      have h35 : ppSum 3 a * ppSum 5 b * 36 ≤ 65 * (3 ^ a * 5 ^ b) := by
        rw [h3, ha2]; linarith
      have hprod : ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * (36 * 28 * 30) ≤
          65 * 29 * 31 * M := by
        have := Nat.mul_le_mul h35 (Nat.mul_le_mul h1r h1p); dsimp [M]; linarith
      have hlt2 := Nat.mul_lt_mul_of_pos_right hMab (by decide : 0 < 36 * 28 * 30)
      linarith
    obtain ⟨_, _, _, _, _, _, _, _, hcov, hgap, hmod3, hbig, _, _, _⟩ :=
      base3_for_b2 hr (by omega) ha hb2 hc ha_hi hr_mem7
    have hL1 : 1 ≤ LcutOf r := by dsimp [LcutOf]; split_ifs <;> decide
    apply finish_from_core hB1 hp hcop (by omega) hL1 hd hab hprim hbig hcov hgap hD2
    intro hElt
    change sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d) - 2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d) < LcutOf r at hElt
    by_cases h3sig : (ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d) % 3 = 0
    · have h3s : 3 ∣ sigma 1 M := by rw [hsig]; exact Nat.dvd_of_mod_eq_zero h3sig
      have h3M : 3 ∣ 2 * M := dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _) _) _) 2
      have h3E : 3 ∣ sigma 1 M - 2 * M := Nat.dvd_sub h3s h3M
      exact hmod3 (sigma 1 M - 2 * M) (by rw [hsig]; omega) hElt (Nat.mod_eq_zero_of_dvd h3E)
    · exfalso
      have hbe : b % 2 = 0 := by
        by_contra hodd
        apply h3sig
        exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
          (dvd_trans (by decide : 3 ∣ 6) (not_div3_of_dvd_sigma_five_odd (by omega))) _) _) _)
      have hc0_le : (if Nat.beq (r % 3) 2 then 2 else 1) ≤ c := by
        split_ifs with hr2
        · have hr2' : r % 3 = 2 := (Iff.of_eq Nat.beq_eq).mp hr2
          have hce : c % 2 = 0 := by
            by_contra hodd; apply h3sig
            have h3r : 3 ∣ ppSum r c := Nat.dvd_of_mod_eq_zero (ppSum_mod3_of_prime_mod3.1 hr2' (by omega))
            exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h3r _) _)
          omega
        · exact hc
      have hd0_le : (if Nat.beq (p % 3) 2 then 2 else 1) ≤ d := by
        split_ifs with hp2
        · have hp2' : p % 3 = 2 := (Iff.of_eq Nat.beq_eq).mp hp2
          have hde : d % 2 = 0 := by
            by_contra hodd; apply h3sig
            have h3p : 3 ∣ ppSum p d := Nat.dvd_of_mod_eq_zero (ppSum_mod3_of_prime_mod3.1 hp2' (by omega))
            exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right h3p _)
          omega
        · exact hd
      have hc0_even : r % 3 = 2 → (if Nat.beq (r % 3) 2 then 2 else 1) % 2 = 0 := by
        intro hr2; rw [(Iff.of_eq Nat.beq_eq).mpr hr2]; decide
      have hok := List.all_eq_true.mp all_box4_ok (r, p) hmem4
      have hge := checkBox4_sound 40 r p 2 none 2 none (if Nat.beq (r % 3) 2 then 2 else 1) none
        (if Nat.beq (p % 3) 2 then 2 else 1) none (LcutOf r) a b c d
        hr hp (by omega) hrp ha trivial hb2 trivial hbe (by decide) hc0_le trivial hc0_even
        hd hd0_le trivial h3sig hab hprim hok
      omega

set_option maxHeartbeats 4000000 in
private lemma solve_omega5 {r p q a b c d e : ℕ}
    (hr : r.Prime) (hp : p.Prime) (hq : q.Prime)
    (h17 : 17 ≤ r) (hrp : r < p) (hpq : p < q)
    (hr_mem : r ∈ ([17, 19, 23, 29, 31, 37, 41, 43] : List ℕ))
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hab : (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e).properDivisors, x.Deficient) :
    (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e).Pseudoperfect := by
  set M := 3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e
  have hMpos : 0 < M := by have := hr.pos; have := hp.pos; have := hq.pos; positivity
  have hsig := sigma_five_primes hr hp hq (by omega) hrp hpq (a := a) (b := b) (c := c) (d := d) (e := e)
  have hMab : 2 * M < ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * ppSum q e := by
    have h1 := (abund_iff_nat hMpos).mp hab; rwa [hsig] at h1
  -- Ratio bound: 16 * (r - 1) * (p - 1) * (q - 1) < 15 * r * p * q
  have hlim5 : 16 * (r - 1) * (p - 1) * (q - 1) < 15 * r * p * q := by
    have h3 := ppSum_lt_lim (p := 3) (e := a) (by decide)
    have h5 := ppSum_lt_lim (p := 5) (e := b) (by decide)
    have hr' := ppSum_lt_lim (p := r) (e := c) hr.two_le
    have hp' := ppSum_lt_lim (p := p) (e := d) hp.two_le
    have hq' := ppSum_lt_lim (p := q) (e := e) hq.two_le
    have hprod : ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * ppSum q e *
        (8 * (r - 1) * (p - 1) * (q - 1)) ≤ 15 * r * p * q * M := by
      have h1 := Nat.mul_le_mul (Nat.mul_le_mul h3.le h5.le) (Nat.mul_le_mul hr'.le hp'.le)
      have h2 := Nat.mul_le_mul h1 hq'.le
      dsimp [M]; linarith
    have hden_pos : 0 < 8 * (r - 1) * (p - 1) * (q - 1) := by
      have : 1 ≤ r - 1 := by omega
      have : 1 ≤ p - 1 := by omega
      have : 1 ≤ q - 1 := by omega
      positivity
    have h1 := Nat.mul_lt_mul_of_pos_right hMab hden_pos
    exact Nat.lt_of_mul_lt_mul_right (show 16 * (r - 1) * (p - 1) * (q - 1) * M < 15 * r * p * q * M by linarith)
  have hq_ge : p + 2 ≤ q := by
    have hp_odd := hp.odd_of_ne_two (by omega)
    have hq_odd := hq.odd_of_ne_two (by omega)
    obtain ⟨m1, hm1⟩ := hp_odd; obtain ⟨m2, hm2⟩ := hq_odd; omega
  have hlim5_sq : 16 * (r - 1) * (p - 1) * (p - 1) < 15 * r * p * p := by
    have hqp : q * (p - 1) ≤ p * (q - 1) := by
      zify [show 1 ≤ p by omega, show 1 ≤ q by omega]; nlinarith
    have h1 : 16 * (r - 1) * (p - 1) * (q - 1) * (p - 1) < 15 * r * p * q * (p - 1) :=
      Nat.mul_lt_mul_of_pos_right hlim5 (by omega)
    have h2 : 15 * r * p * q * (p - 1) ≤ 15 * r * p * p * (q - 1) := by
      calc 15 * r * p * q * (p - 1) = 15 * r * p * (q * (p - 1)) := by ring
        _ ≤ 15 * r * p * (p * (q - 1)) := Nat.mul_le_mul_left _ hqp
        _ = 15 * r * p * p * (q - 1) := by ring
    exact Nat.lt_of_mul_lt_mul_right (show 16 * (r - 1) * (p - 1) * (p - 1) * (q - 1) <
      15 * r * p * p * (q - 1) by linarith)
  have hr_mem7 : r ∈ ([17, 19, 23, 29, 31, 37, 41] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem ⊢
    rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    · -- r = 43 impossible: p >= 47, q >= 53!
      have hp47 : 47 ≤ p := by
        have hchk : ∀ i : Fin 47, i.val.Prime → 43 < i.val → False := by decide
        by_contra hlt; exact hchk ⟨p, by omega⟩ hp hrp
      have hq53 : 53 ≤ q := by
        have hchk : ∀ i : Fin 53, i.val.Prime → 47 < i.val → False := by decide
        by_contra hlt; exact hchk ⟨q, by omega⟩ hq (show 47 < q by omega)
      have hp47' : p * 46 ≤ 47 * (p - 1) := by omega
      have hq53' : q * 52 ≤ 53 * (q - 1) := by omega
      have h1 : 15 * 43 * p * q * 46 * 52 ≤ 15 * 43 * 47 * 53 * (p - 1) * (q - 1) := by
        have := Nat.mul_le_mul hp47' hq53'; linarith
      have h2 := Nat.mul_lt_mul_of_pos_right hlim5 (by decide : 0 < 46 * 52)
      nlinarith
  have hmem5 : (r, p) ∈ pairs5List := by
    have hp_lt : p < 512 := by
      by_contra hge
      push_neg at hge
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem7
      obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hlim5_sq
      have hk := Nat.mul_le_mul_right k hge
      rcases hr_mem7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> nlinarith
    have hchk : ∀ i : Fin 512, i.val.Prime →
        ∀ r0 ∈ ([17, 19, 23, 29, 31, 37, 41] : List ℕ), r0 < i.val →
        16 * (r0 - 1) * (i.val - 1) * (i.val - 1) < 15 * r0 * i.val * i.val →
        (r0, i.val) ∈ pairs5List := by decide +kernel
    exact hchk ⟨p, hp_lt⟩ hp r hr_mem7 hrp hlim5_sq
  have hp_le_maxP : ∀ maxP : ℕ,
      (r = 17 → maxP = 509) → (r = 19 → maxP = 191) → (r = 23 → maxP = 97) →
      (r = 29 → maxP = 67) → (r = 31 → maxP = 61) → (r = 37 → maxP = 53) → (r = 41 → maxP = 47) →
      p ≤ maxP := by
    intro maxP h17' h19' h23' h29' h31' h37' h41'
    have hchk : pairs5List.all (fun x =>
      Nat.ble x.2 (if Nat.beq x.1 17 then 509 else if Nat.beq x.1 19 then 191
        else if Nat.beq x.1 23 then 97 else if Nat.beq x.1 29 then 67
        else if Nat.beq x.1 31 then 61 else if Nat.beq x.1 37 then 53 else 47)) = true := by
      decide +kernel
    have h1 := (Iff.of_eq Nat.ble_eq).mp (List.all_eq_true.mp hchk (r, p) hmem5)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem7
    rcases hr_mem7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  let B := 3 ^ a * 5 ^ b * r ^ c * p ^ d
  let B3 := 3 ^ a * 5 ^ b * r ^ c
  have hB3pos : 0 < B3 := by have := hr.pos; positivity
  have hB1 : 1 < B := by
    dsimp [B]
    have h1 : 9 ≤ 3 ^ a := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 3) ha
    have h2 : 1 ≤ 5 ^ b := Nat.one_le_pow _ _ (by decide)
    have h3 : 1 ≤ r ^ c := Nat.one_le_pow _ _ hr.pos
    have h4 : 1 ≤ p ^ d := Nat.one_le_pow _ _ hp.pos
    have h234 : 1 ≤ 5 ^ b * r ^ c * p ^ d := Nat.mul_pos (Nat.mul_pos h2 h3) h4
    nlinarith
  have hB3cop_p : B3.Coprime p := by
    dsimp [B3]
    exact (((Nat.coprime_primes (by decide) hp).mpr (by omega)).pow_left a |>.mul_left
      (((Nat.coprime_primes (by decide) hp).mpr (by omega)).pow_left b)).mul_left
      (((Nat.coprime_primes hr hp).mpr (by omega)).pow_left c)
  have hBcop_q : B.Coprime q := by
    dsimp [B]
    exact ((((Nat.coprime_primes (by decide) hq).mpr (by omega)).pow_left a |>.mul_left
      (((Nat.coprime_primes (by decide) hq).mpr (by omega)).pow_left b)).mul_left
      (((Nat.coprime_primes hr hq).mpr (by omega)).pow_left c)).mul_left
      (((Nat.coprime_primes hp hq).mpr (by omega)).pow_left d)
  have hBdef : sigma 1 B < 2 * B := by
    have hmem : B ∈ M.properDivisors := Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right B _, lt_mul_of_one_lt_right (by have := hr.pos; have := hp.pos; positivity)
        (one_lt_pow₀ hq.one_lt (by omega))⟩
    exact (defic_iff_nat (by omega)).mp (hprim B hmem)
  have hD2 : e = 1 → 2 ≤ B - properDivsSum B := fun _ =>
    d_ge_two_four_primes hr hp h17 hrp ha hb hc hd hmem5 hBdef
  -- Helper: lift core from B3 to B = B3 * p^d and finish!
  have hfrom_B3 : ∀ (L maxP : ℕ), 1 ≤ L → p ≤ maxP →
      (∀ y, L ≤ y → y ≤ properDivsSum B3 - L → repNat B3.properDivisors y) →
      (∀ k, k < properDivsSum B3 → ∃ i, repNat B3.properDivisors i ∧ k < i + 2 ∧ i ≤ k) →
      (5 * (2 * L + 24) ≤ properDivsSum B3) →
      (2 * L ≤ properDivsSum B3) →
      (maxP * 2 ≤ properDivsSum B3 - 2 * L + 1) →
      (B3 + 2 * L ≤ properDivsSum B3 + 19 * properDivsSum B3 + 1) →
      (sigma 1 M - 2 * M < L → repNat B3.properDivisors (sigma 1 M - 2 * M)) →
      M.Pseudoperfect := by
    intro L maxP hL1 hple hcov3 hgap3 hbig3 h2L3 hwide3 hov3 hsmall3
    have hwide_p : p * 2 ≤ properDivsSum B3 - 2 * L + 1 := by omega
    have hov_p : B3 + 2 * L ≤ properDivsSum B3 + p * properDivsSum B3 + 1 := by
      have hp19 : 19 ≤ p := by
        obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega); omega
      have : 19 * properDivsSum B3 ≤ p * properDivsSum B3 := Nat.mul_le_mul_right _ hp19
      omega
    obtain ⟨hcovB, hgapB⟩ := lift_coprime_prime_pow hB3pos hp hB3cop_p (by decide)
      h2L3 hwide_p hov_p hcov3 hgap3 d hd
    have hsub3 : B3.properDivisors ⊆ B.properDivisors := by
      intro x hx
      obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp hx
      exact Nat.mem_properDivisors.mpr ⟨h1.trans (dvd_mul_right B3 _),
        lt_of_lt_of_le h2 (Nat.le_mul_of_pos_right B3 (pow_pos hp.pos d))⟩
    have hP3_le_PB : properDivsSum B3 ≤ properDivsSum B := Finset.sum_le_sum_of_subset hsub3
    apply finish_from_core hB1 hq hBcop_q (by omega) hL1 he hab hprim (le_trans hbig3 hP3_le_PB) hcovB hgapB hD2
    intro hElt
    obtain ⟨s, hs, hsum⟩ := hsmall3 hElt
    exact ⟨s, hs.trans hsub3, hsum⟩
  by_cases hb1 : b = 1
  · -- b = 1: 6 | E! Split by a = 2, a = 3, a >= 4!
    have h6E : 6 ∣ sigma 1 M - 2 * M := by
      have h6s : 6 ∣ sigma 1 M := by
        rw [hsig]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
          (not_div3_of_dvd_sigma_five_odd (by omega)) _) _) _) _
      have h6M : 6 ∣ 2 * M := by
        have h3M : 3 ∣ M := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
          (dvd_pow_self 3 (by omega)) _) _) _) _
        obtain ⟨k, hk⟩ := h3M; exact ⟨k, by omega⟩
      exact Nat.dvd_sub h6s h6M
    by_cases ha2 : a = 2
    · -- a = 2, b = 1: only (r, p) = (17, 19) survives!
      have hrp_17_19 : r = 17 ∧ p = 19 := by
        have h35 : ppSum 3 a * ppSum 5 b = 78 := by rw [ha2, hb1]; decide
        have hB35 : 3 ^ a * 5 ^ b = 45 := by rw [ha2, hb1]; decide
        have hr' := ppSum_lt_lim (p := r) (e := c) hr.two_le
        have hp' := ppSum_lt_lim (p := p) (e := d) hp.two_le
        have hq' := ppSum_lt_lim (p := q) (e := e) hq.two_le
        have hlim_21 : 15 * (r - 1) * (p - 1) * (q - 1) < 13 * r * p * q := by
          have hprod : ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * ppSum q e *
              ((r - 1) * (p - 1) * (q - 1)) ≤ 78 * r * p * q * (r ^ c * p ^ d * q ^ e) := by
            have := Nat.mul_le_mul (Nat.mul_le_mul hr'.le hp'.le) hq'.le
            rw [h35]; linarith
          have hden_pos : 0 < (r - 1) * (p - 1) * (q - 1) := by
            have : 1 ≤ r - 1 := by omega
            have : 1 ≤ p - 1 := by omega
            have : 1 ≤ q - 1 := by omega
            positivity
          have h1 := Nat.mul_lt_mul_of_pos_right hMab hden_pos
          have hM_eq : M = 45 * (r ^ c * p ^ d * q ^ e) := by dsimp [M]; rw [hB35]; ring
          rw [hM_eq] at h1
          have h2 : 90 * (r - 1) * (p - 1) * (q - 1) * (r ^ c * p ^ d * q ^ e) <
              78 * r * p * q * (r ^ c * p ^ d * q ^ e) := by linarith
          have h3 := Nat.lt_of_mul_lt_mul_right h2
          have e1 : 90 * (r - 1) * (p - 1) * (q - 1) = 6 * (15 * (r - 1) * (p - 1) * (q - 1)) := by ring
          have e2 : 78 * r * p * q = 6 * (13 * r * p * q) := by ring
          rw [e1, e2] at h3
          omega
        have hr17 : r = 17 := by
          by_contra hne
          have hr19 : 19 ≤ r := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem7
            rcases hr_mem7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          have hp23 : 23 ≤ p := by
            have hchk : ∀ i : Fin 23, i.val.Prime → 19 < i.val → False := by decide
            by_contra hlt; exact hchk ⟨p, by omega⟩ hp (show _ < p by omega)
          have hq29 : 29 ≤ q := by
            have hchk : ∀ i : Fin 29, i.val.Prime → 23 < i.val → False := by decide
            by_contra hlt; exact hchk ⟨q, by omega⟩ hq (show _ < q by omega)
          have h1 : r * 18 ≤ 19 * (r - 1) := by omega
          have h2 : p * 22 ≤ 23 * (p - 1) := by omega
          have h3 : q * 28 ≤ 29 * (q - 1) := by omega
          have h123 : r * p * q * (18 * 22 * 28) ≤ 19 * 23 * 29 * ((r - 1) * (p - 1) * (q - 1)) := by
            have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3; linarith
          have hlt2 := Nat.mul_lt_mul_of_pos_right hlim_21 (by decide : 0 < 18 * 22 * 28)
          nlinarith
        subst hr17
        have hp19 : p = 19 := by
          by_contra hne
          have hp23 : 23 ≤ p := by
            have hchk : ∀ i : Fin 23, i.val.Prime → 17 < i.val → i.val ≠ 19 → False := by decide
            by_contra hlt; exact hchk ⟨p, by omega⟩ hp hrp hne
          have hq29 : 29 ≤ q := by
            have hchk : ∀ i : Fin 29, i.val.Prime → 23 < i.val → False := by decide
            by_contra hlt; exact hchk ⟨q, by omega⟩ hq (show _ < q by omega)
          have h2 : p * 22 ≤ 23 * (p - 1) := by omega
          have h3 : q * 28 ≤ 29 * (q - 1) := by omega
          have h23 : p * q * (22 * 28) ≤ 23 * 29 * ((p - 1) * (q - 1)) := by
            have := Nat.mul_le_mul h2 h3; linarith
          have hlt2 := Nat.mul_lt_mul_of_pos_right hlim_21 (by decide : 0 < 22 * 28)
          nlinarith
        exact ⟨rfl, hp19⟩
      obtain ⟨rfl, rfl⟩ := hrp_17_19
      subst ha2; subst hb1
      obtain ⟨hcovB, hgapB, hmod6, hbigB⟩ := lift_base_45_17_19 hc hd
      apply finish_from_core hB1 hq hBcop_q (by omega) (by decide) he hab hprim hbigB hcovB hgapB hD2
      intro hElt
      exact hmod6 (sigma 1 M - 2 * M) (by rw [hsig]; omega) hElt (Nat.mod_eq_zero_of_dvd h6E)
    · by_cases ha3 : a = 3
      · -- a = 3, b = 1: r in {17, 19} and p <= 31 (if r=17) or p <= 29 (if r=19)!
        have h35 : ppSum 3 a * ppSum 5 b = 240 := by rw [ha3, hb1]; decide
        have hB35 : 3 ^ a * 5 ^ b = 135 := by rw [ha3, hb1]; decide
        have hlim_31 : 9 * (r - 1) * (p - 1) * (q - 1) < 8 * r * p * q := by
          have hr' := ppSum_lt_lim (p := r) (e := c) hr.two_le
          have hp' := ppSum_lt_lim (p := p) (e := d) hp.two_le
          have hq' := ppSum_lt_lim (p := q) (e := e) hq.two_le
          have hprod : ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * ppSum q e *
              ((r - 1) * (p - 1) * (q - 1)) ≤ 240 * r * p * q * (r ^ c * p ^ d * q ^ e) := by
            have := Nat.mul_le_mul (Nat.mul_le_mul hr'.le hp'.le) hq'.le
            rw [h35]; linarith
          have hden_pos : 0 < (r - 1) * (p - 1) * (q - 1) := by
            have : 1 ≤ r - 1 := by omega
            have : 1 ≤ p - 1 := by omega
            have : 1 ≤ q - 1 := by omega
            positivity
          have h1 := Nat.mul_lt_mul_of_pos_right hMab hden_pos
          have hM_eq : M = 135 * (r ^ c * p ^ d * q ^ e) := by dsimp [M]; rw [hB35]; ring
          rw [hM_eq] at h1
          have h2 : 270 * (r - 1) * (p - 1) * (q - 1) * (r ^ c * p ^ d * q ^ e) <
              240 * r * p * q * (r ^ c * p ^ d * q ^ e) := by linarith
          have h3 := Nat.lt_of_mul_lt_mul_right h2
          have e1 : 270 * (r - 1) * (p - 1) * (q - 1) = 30 * (9 * (r - 1) * (p - 1) * (q - 1)) := by ring
          have e2 : 240 * r * p * q = 30 * (8 * r * p * q) := by ring
          rw [e1, e2] at h3
          omega
        have hr_17_19 : r = 17 ∨ r = 19 := by
          by_contra hne; push Not at hne
          have hr23 : 23 ≤ r := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem7
            rcases hr_mem7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          have hp29 : 29 ≤ p := by
            have hchk : ∀ i : Fin 29, i.val.Prime → 23 < i.val → False := by decide
            by_contra hlt; exact hchk ⟨p, by omega⟩ hp (show _ < p by omega)
          have hq31 : 31 ≤ q := by omega
          have h1 : r * 22 ≤ 23 * (r - 1) := by omega
          have h2 : p * 28 ≤ 29 * (p - 1) := by omega
          have h3 : q * 30 ≤ 31 * (q - 1) := by omega
          have h123 : r * p * q * (22 * 28 * 30) ≤ 23 * 29 * 31 * ((r - 1) * (p - 1) * (q - 1)) := by
            have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3; linarith
          have hlt2 := Nat.mul_lt_mul_of_pos_right hlim_31 (by decide : 0 < 22 * 28 * 30)
          nlinarith
        have hp_le_31 : (r = 17 → p ≤ 31) ∧ (r = 19 → p ≤ 29) := by
          constructor
          · rintro rfl
            by_contra hgt
            have hp37 : 37 ≤ p := by
              have hchk : ∀ i : Fin 37, i.val.Prime → 31 < i.val → False := by decide
              by_contra hlt; exact hchk ⟨p, by omega⟩ hp (show _ < p by omega)
            have hq41 : 41 ≤ q := by
              have hchk : ∀ i : Fin 41, i.val.Prime → 37 < i.val → False := by decide
              by_contra hlt; exact hchk ⟨q, by omega⟩ hq (show _ < q by omega)
            have h2 : p * 36 ≤ 37 * (p - 1) := by omega
            have h3 : q * 40 ≤ 41 * (q - 1) := by omega
            have h23 : p * q * (36 * 40) ≤ 37 * 41 * ((p - 1) * (q - 1)) := by
              have := Nat.mul_le_mul h2 h3; linarith
            have hlt2 := Nat.mul_lt_mul_of_pos_right hlim_31 (by decide : 0 < 36 * 40)
            nlinarith
          · rintro rfl
            by_contra hgt
            have hp31 : 31 ≤ p := by
              obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega); omega
            have hq37 : 37 ≤ q := by
              have hchk : ∀ i : Fin 37, i.val.Prime → 31 < i.val → False := by decide
              by_contra hlt; exact hchk ⟨q, by omega⟩ hq (show _ < q by omega)
            have h2 : p * 30 ≤ 31 * (p - 1) := by omega
            have h3 : q * 36 ≤ 37 * (q - 1) := by omega
            have h23 : p * q * (30 * 36) ≤ 31 * 37 * ((p - 1) * (q - 1)) := by
              have := Nat.mul_le_mul h2 h3; linarith
            have hlt2 := Nat.mul_lt_mul_of_pos_right hlim_31 (by decide : 0 < 30 * 36)
            nlinarith
        obtain ⟨L, maxP, hm17, hm19, hL1, hcov3, hgap3, hmod6, hbig3, h2L3, hwide3, hov3⟩ :=
          base3_for_a3_odd (a := a) hr (by omega) (by omega) hb hc hr_17_19
        have hple : p ≤ maxP := by rcases hr_17_19 with rfl | rfl <;> [rw [hm17 rfl]; rw [hm19 rfl]] <;> [exact hp_le_31.1 rfl; exact hp_le_31.2 rfl]
        exact hfrom_B3 L maxP hL1 hple hcov3 hgap3 hbig3 h2L3 hwide3 hov3
          (fun hElt => hmod6 (sigma 1 M - 2 * M) (by rw [hsig]; omega) hElt (Nat.mod_eq_zero_of_dvd h6E))
      · -- a >= 4, b = 1!
        have ha4 : 4 ≤ a := by omega
        obtain ⟨L, maxP, h17', h19', h23', h29', h31', h37', h41', hL1,
          hcov3, hgap3, hmod6, hbig3, h2L3, hwide3, hov3⟩ :=
          base3_for_odd hr (by omega) ha4 hb hc hr_mem7
        exact hfrom_B3 L maxP hL1 (hp_le_maxP maxP h17' h19' h23' h29' h31' h37' h41')
          hcov3 hgap3 hbig3 h2L3 hwide3 hov3
          (fun hElt => hmod6 (sigma 1 M - 2 * M) (by rw [hsig]; omega) hElt (Nat.mod_eq_zero_of_dvd h6E))
  · -- b >= 2!
    have hb2 : 2 ≤ b := by omega
    have ha_hi : 29 ≤ r → 3 ≤ a := by
      intro hr29
      by_contra hlt
      have ha2 : a = 2 := by omega
      have h3 : ppSum 3 a = 13 := by rw [ha2]; decide
      have h5 := ppSum_lt_lim (p := 5) (e := b) (by decide)
      have hr' := ppSum_lt_lim (p := r) (e := c) hr.two_le
      have hp' := ppSum_lt_lim (p := p) (e := d) hp.two_le
      have hq' := ppSum_lt_lim (p := q) (e := e) hq.two_le
      have hp31 : 31 ≤ p := by
        obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega); omega
      have hq37 : 37 ≤ q := by
        have hchk : ∀ i : Fin 37, i.val.Prime → 31 < i.val → False := by decide
        by_contra hlt'; exact hchk ⟨q, by omega⟩ hq (show _ < q by omega)
      have h1r : ppSum r c * 28 ≤ 29 * r ^ c := by
        have hrr : r * 28 ≤ 29 * (r - 1) := by omega
        apply Nat.le_of_mul_le_mul_right _ (show 0 < r - 1 by omega)
        calc ppSum r c * 28 * (r - 1) = (ppSum r c * (r - 1)) * 28 := by ring
          _ ≤ (r * r ^ c) * 28 := Nat.mul_le_mul_right 28 hr'.le
          _ = (r * 28) * r ^ c := by ring
          _ ≤ (29 * (r - 1)) * r ^ c := Nat.mul_le_mul_right _ hrr
          _ = 29 * r ^ c * (r - 1) := by ring
      have h1p : ppSum p d * 30 ≤ 31 * p ^ d := by
        have hpp : p * 30 ≤ 31 * (p - 1) := by omega
        apply Nat.le_of_mul_le_mul_right _ (show 0 < p - 1 by omega)
        calc ppSum p d * 30 * (p - 1) = (ppSum p d * (p - 1)) * 30 := by ring
          _ ≤ (p * p ^ d) * 30 := Nat.mul_le_mul_right 30 hp'.le
          _ = (p * 30) * p ^ d := by ring
          _ ≤ (31 * (p - 1)) * p ^ d := Nat.mul_le_mul_right _ hpp
          _ = 31 * p ^ d * (p - 1) := by ring
      have h1q : ppSum q e * 36 ≤ 37 * q ^ e := by
        have hqq : q * 36 ≤ 37 * (q - 1) := by omega
        apply Nat.le_of_mul_le_mul_right _ (show 0 < q - 1 by omega)
        calc ppSum q e * 36 * (q - 1) = (ppSum q e * (q - 1)) * 36 := by ring
          _ ≤ (q * q ^ e) * 36 := Nat.mul_le_mul_right 36 hq'.le
          _ = (q * 36) * q ^ e := by ring
          _ ≤ (37 * (q - 1)) * q ^ e := Nat.mul_le_mul_right _ hqq
          _ = 37 * q ^ e * (q - 1) := by ring
      have h35 : ppSum 3 a * ppSum 5 b * 36 ≤ 65 * (3 ^ a * 5 ^ b) := by
        rw [h3, ha2]; linarith
      have hprod : ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * ppSum q e * (36 * 28 * 30 * 36) ≤
          65 * 29 * 31 * 37 * M := by
        have := Nat.mul_le_mul (Nat.mul_le_mul h35 (Nat.mul_le_mul h1r h1p)) h1q
        dsimp [M]; linarith
      have hlt2 := Nat.mul_lt_mul_of_pos_right hMab (by decide : 0 < 36 * 28 * 30 * 36)
      linarith
    obtain ⟨maxP, h17', h19', h23', h29', h31', h37', h41',
      hcov3, hgap3, hmod3, hbig3, h2L3, hwide3, hov3⟩ :=
      base3_for_b2 hr (by omega) ha hb2 hc ha_hi hr_mem7
    have hL1 : 1 ≤ LcutOf r := by dsimp [LcutOf]; split_ifs <;> decide
    apply hfrom_B3 (LcutOf r) maxP hL1 (hp_le_maxP maxP h17' h19' h23' h29' h31' h37' h41')
      hcov3 hgap3 hbig3 h2L3 hwide3 hov3
    intro hElt
    by_cases h3sig : (ppSum 3 a * ppSum 5 b * ppSum r c * ppSum p d * ppSum q e) % 3 = 0
    · have h3s : 3 ∣ sigma 1 M := by rw [hsig]; exact Nat.dvd_of_mod_eq_zero h3sig
      have h3M : 3 ∣ 2 * M := dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _) _) _) _) 2
      have h3E : 3 ∣ sigma 1 M - 2 * M := Nat.dvd_sub h3s h3M
      exact hmod3 (sigma 1 M - 2 * M) (by rw [hsig]; omega) hElt (Nat.mod_eq_zero_of_dvd h3E)
    · exfalso
      have hbe : b % 2 = 0 := by
        by_contra hodd; apply h3sig
        exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right (dvd_trans (by decide : 3 ∣ 6) (not_div3_of_dvd_sigma_five_odd (by omega))) _) _) _) _)
      have hc0_le : (if Nat.beq (r % 3) 2 then 2 else 1) ≤ c := by
        split_ifs with hr2
        · have hr2' : r % 3 = 2 := (Iff.of_eq Nat.beq_eq).mp hr2
          have hce : c % 2 = 0 := by
            by_contra hodd; apply h3sig
            have h3r : 3 ∣ ppSum r c := Nat.dvd_of_mod_eq_zero (ppSum_mod3_of_prime_mod3.1 hr2' (by omega))
            exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h3r _) _) _)
          omega
        · exact hc
      have hd0_le : (if Nat.beq (p % 3) 2 then 2 else 1) ≤ d := by
        split_ifs with hp2
        · have hp2' : p % 3 = 2 := (Iff.of_eq Nat.beq_eq).mp hp2
          have hde : d % 2 = 0 := by
            by_contra hodd; apply h3sig
            have h3p : 3 ∣ ppSum p d := Nat.dvd_of_mod_eq_zero (ppSum_mod3_of_prime_mod3.1 hp2' (by omega))
            exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h3p _) _)
          omega
        · exact hd
      have hc0_even : r % 3 = 2 → (if Nat.beq (r % 3) 2 then 2 else 1) % 2 = 0 := by
        intro hr2; rw [(Iff.of_eq Nat.beq_eq).mpr hr2]; decide
      have hd0_even : p % 3 = 2 → (if Nat.beq (p % 3) 2 then 2 else 1) % 2 = 0 := by
        intro hp2; rw [(Iff.of_eq Nat.beq_eq).mpr hp2]; decide
      have hok := List.all_eq_true.mp all_box5_ok (r, p) hmem5
      have hge := checkBox5_sound 60 r p 2 none 2 none (if Nat.beq (r % 3) 2 then 2 else 1) none
        (if Nat.beq (p % 3) 2 then 2 else 1) none (p + 2) none none (LcutOf r) a b c d q e
        hr hp hq (by omega) hrp hpq ha trivial hb2 trivial hbe (by decide) hc0_le trivial hc0_even
        hd0_le trivial hd0_even hq_ge trivial he trivial h3sig hab hprim hok
      have hEq : sigma 1 M - 2 * M = sigma 1 (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e) -
          2 * (3 ^ a * 5 ^ b * r ^ c * p ^ d * q ^ e) := rfl
      omega

end MainProof

end Erdos470R2H2R1H4

set_option maxHeartbeats 1600000 in
theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.H4 := by
  intro n hodd hab hcard4 hcard5 hprim h45 h7 h11 h13 ⟨r0, hr0_mem, hr0_dvd⟩
  have hn_pos : 0 < n := hodd.pos
  have hn_ne : n ≠ 0 := hn_pos.ne'
  have hd9 : 9 ∣ n := dvd_trans (by decide : 9 ∣ 45) h45
  have hd3 : 3 ∣ n := dvd_trans (by decide : 3 ∣ 9) hd9
  have hd5 : 5 ∣ n := dvd_trans (by decide : 5 ∣ 45) h45
  have hm3 : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, hd3, hn_ne⟩
  have hm5 : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, hd5, hn_ne⟩
  have ha2 : 2 ≤ n.factorization 3 :=
    ((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization hn_ne (k := 2)).mp (by simpa using hd9)
  have hb1 : 1 ≤ n.factorization 5 :=
    ((by decide : Nat.Prime 5).pow_dvd_iff_le_factorization hn_ne (k := 1)).mp (by simpa using hd5)
  let S := n.primeFactors \ {3, 5}
  have hsub35 : ({3, 5} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hS_card : S.card = n.primeFactors.card - 2 := by
    rw [Finset.card_sdiff_of_subset hsub35, Finset.card_pair (by decide)]
  have hS_ge17 : ∀ s ∈ S, s.Prime ∧ 17 ≤ s := by
    intro s hs
    obtain ⟨hsm, hs35⟩ := Finset.mem_sdiff.mp hs
    have hsp := Nat.prime_of_mem_primeFactors hsm
    have hsd := Nat.dvd_of_mem_primeFactors hsm
    refine ⟨hsp, ?_⟩
    by_contra hlt
    have hchk : ∀ i : Fin 17, i.val.Prime → i.val ∈ ([2, 3, 5, 7, 11, 13] : List ℕ) := by
      decide
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs35
    have hmem : s ∈ ([2, 3, 5, 7, 11, 13] : List ℕ) := hchk ⟨s, by omega⟩ hsp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hodd.not_two_dvd_nat hsd
    · exact hs35.1 rfl
    · exact hs35.2 rfl
    · exact h7 hsd
    · exact h11 hsd
    · exact h13 hsd
  have hr0_prime : r0.Prime := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr0_mem
    rcases hr0_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr0_le43 : r0 ≤ 43 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr0_mem
    rcases hr0_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr0_in_S : r0 ∈ S := by
    refine Finset.mem_sdiff.mpr ⟨Nat.mem_primeFactors.mpr ⟨hr0_prime, hr0_dvd, hn_ne⟩, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    have : 17 ≤ r0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr0_mem
      rcases hr0_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    omega
  have hr_list_of_le43 : ∀ r : ℕ, r.Prime → 17 ≤ r → r ≤ 43 →
      r ∈ ([17, 19, 23, 29, 31, 37, 41, 43] : List ℕ) := by
    intro r hrp h17 h43
    have hchk : ∀ i : Fin 44, i.val.Prime → 17 ≤ i.val →
        i.val ∈ ([17, 19, 23, 29, 31, 37, 41, 43] : List ℕ) := by decide
    exact hchk ⟨r, by omega⟩ hrp h17
  by_cases hc4 : n.primeFactors.card = 4
  · have hSc2 : S.card = 2 := by omega
    obtain ⟨x, y, hxy_ne, hS_eq⟩ := Finset.card_eq_two.mp hSc2
    obtain ⟨r, p, hrp_lt, hS_rp⟩ : ∃ r p, r < p ∧ S = {r, p} := by
      rcases lt_or_gt_of_ne hxy_ne with h | h
      · exact ⟨x, y, h, hS_eq⟩
      · exact ⟨y, x, h, by rw [hS_eq, Finset.pair_comm]⟩
    have hr_in : r ∈ S := by rw [hS_rp]; simp
    have hp_in : p ∈ S := by rw [hS_rp]; simp
    obtain ⟨hr_pr, hr17⟩ := hS_ge17 r hr_in
    obtain ⟨hp_pr, _⟩ := hS_ge17 p hp_in
    have hr_le : r ≤ r0 := by
      rw [hS_rp] at hr0_in_S; simp only [Finset.mem_insert, Finset.mem_singleton] at hr0_in_S
      rcases hr0_in_S with rfl | rfl <;> omega
    have hr_mem : r ∈ ([17, 19, 23, 29, 31, 37, 41, 43] : List ℕ) :=
      hr_list_of_le43 r hr_pr hr17 (le_trans hr_le hr0_le43)
    have hpf_eq : n.primeFactors = {3, 5, r, p} := by
      have hu := Finset.sdiff_union_of_subset hsub35
      change S ∪ {3, 5} = n.primeFactors at hu
      rw [← hu, hS_rp]; ext z; simp; tauto
    have hn_eq : n = 3 ^ n.factorization 3 * 5 ^ n.factorization 5 * r ^ n.factorization r * p ^ n.factorization p := by
      have hprod := (Nat.prod_primeFactors_pow_factorization hn_ne).symm
      rw [hpf_eq] at hprod
      rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
          Finset.prod_insert (by simp; omega), Finset.prod_singleton] at hprod
      linarith [hprod]
    have hc1 : 1 ≤ n.factorization r :=
      OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.at_least_one (Finset.mem_sdiff.mp hr_in).1
    have hd1 : 1 ≤ n.factorization p :=
      OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.at_least_one (Finset.mem_sdiff.mp hp_in).1
    rw [hn_eq] at hab hprim ⊢
    exact Erdos470R2H2R1H4.solve_omega4 hr_pr hp_pr hr17 hrp_lt hr_mem ha2 hb1 hc1 hd1 hab hprim
  · have hSc3 : S.card = 3 := by omega
    obtain ⟨x, y, z, hxy, hxz, hyz, hS_eq⟩ := Finset.card_eq_three.mp hSc3
    -- Sort {x, y, z} into r < p < q
    obtain ⟨r, p, q, hrp_lt, hpq_lt, hS_rpq⟩ : ∃ r p q, r < p ∧ p < q ∧ S = {r, p, q} := by
      have sort3 : ∀ a b c : ℕ, a ≠ b → a ≠ c → b ≠ c →
          ∃ u v w, u < v ∧ v < w ∧ ({a, b, c} : Finset ℕ) = {u, v, w} := by
        intro a b c hab' hac' hbc'
        rcases lt_or_gt_of_ne hab' with h1 | h1 <;>
        rcases lt_or_gt_of_ne hac' with h2 | h2 <;>
        rcases lt_or_gt_of_ne hbc' with h3 | h3
        · exact ⟨a, b, c, h1, h3, rfl⟩
        · exact ⟨a, c, b, h2, h3, by ext t; simp; tauto⟩
        · omega
        · exact ⟨c, a, b, h2, h1, by ext t; simp; tauto⟩
        · exact ⟨b, a, c, h1, h2, by ext t; simp; tauto⟩
        · omega
        · exact ⟨b, c, a, h3, h2, by ext t; simp; tauto⟩
        · exact ⟨c, b, a, h3, h1, by ext t; simp; tauto⟩
      obtain ⟨r, p, q, h1, h2, h3⟩ := sort3 x y z hxy hxz hyz
      exact ⟨r, p, q, h1, h2, hS_eq.trans h3⟩
    have hr_in : r ∈ S := by rw [hS_rpq]; simp
    have hp_in : p ∈ S := by rw [hS_rpq]; simp
    have hq_in : q ∈ S := by rw [hS_rpq]; simp
    obtain ⟨hr_pr, hr17⟩ := hS_ge17 r hr_in
    obtain ⟨hp_pr, _⟩ := hS_ge17 p hp_in
    obtain ⟨hq_pr, _⟩ := hS_ge17 q hq_in
    have hr_le : r ≤ r0 := by
      rw [hS_rpq] at hr0_in_S; simp only [Finset.mem_insert, Finset.mem_singleton] at hr0_in_S
      rcases hr0_in_S with rfl | rfl | rfl <;> omega
    have hr_mem : r ∈ ([17, 19, 23, 29, 31, 37, 41, 43] : List ℕ) :=
      hr_list_of_le43 r hr_pr hr17 (le_trans hr_le hr0_le43)
    have hpf_eq : n.primeFactors = {3, 5, r, p, q} := by
      have hu := Finset.sdiff_union_of_subset hsub35
      change S ∪ {3, 5} = n.primeFactors at hu
      rw [← hu, hS_rpq]; ext t; simp; tauto
    have hn_eq : n = 3 ^ n.factorization 3 * 5 ^ n.factorization 5 *
        r ^ n.factorization r * p ^ n.factorization p * q ^ n.factorization q := by
      have hprod := (Nat.prod_primeFactors_pow_factorization hn_ne).symm
      rw [hpf_eq] at hprod
      rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
          Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
          Finset.prod_singleton] at hprod
      linarith [hprod]
    have hc1 : 1 ≤ n.factorization r :=
      OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.at_least_one (Finset.mem_sdiff.mp hr_in).1
    have hd1 : 1 ≤ n.factorization p :=
      OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.at_least_one (Finset.mem_sdiff.mp hp_in).1
    have he1 : 1 ≤ n.factorization q :=
      OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.at_least_one (Finset.mem_sdiff.mp hq_in).1
    rw [hn_eq] at hab hprim ⊢
    exact Erdos470R2H2R1H4.solve_omega5 hr_pr hp_pr hq_pr hr17 hrp_lt hpq_lt hr_mem
      ha2 hb1 hc1 hd1 he1 hab hprim
