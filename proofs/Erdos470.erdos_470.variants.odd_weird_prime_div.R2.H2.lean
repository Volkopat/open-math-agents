import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2
import Mathlib

/-!
Proof of Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2:
Every odd primitive abundant multiple of 9 with at most five distinct prime factors
is pseudoperfect.

Structure:
1. FinalPrime: final-prime interval translation lemmas (central interval [L, P - L] and gap g).
2. CoreLift: interval-list subset-sum checker, coprime prime lift, prime-power lift,
   HasAbsGap and HasRelGap with extra-divisor preservation.
3. DGe2: proof that no odd deficient B with omega(B) <= 4 and 9 | B satisfies 2*B - sigma(B) = 1.
4. CheckBox: pure-Nat recursive branch-and-bound verifier ruling out small-excess exceptions
   across all 4-prime and 5-prime families without external certificate trees.
5. SmallCases: exact classification and explicit excess witnesses for omega = 3 (8 numbers)
   and omega = 4 with 5 not dividing m (39 numbers).
6. MainProof and assembly of OMA.solution.
-/

namespace R2H2

open Finset ArithmeticFunction

section FinalPrime

lemma final_prime_alternatives {P D q L g E : ℤ}
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

lemma four_interval_join {P D q L A : ℤ} (w : q ≤ P - 2 * L + 1) (v : D + 2 * L - 1 ≤ q)
    (lo : L ≤ A) (hi : A ≤ 2 * P + D + q - L) :
    (L ≤ A ∧ A ≤ P - L) ∨ (L ≤ A - q ∧ A - q ≤ P - L) ∨
    (L ≤ A - (P + D) ∧ A - (P + D) ≤ P - L) ∨
    (L ≤ A - (P + D + q) ∧ A - (P + D + q) ≤ P - L) := by omega

lemma nondivisor {P D q : ℤ} (hD : 0 < D)
    (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1)) : ¬ D ∣ 2 * P := by
  rintro ⟨x, h⟩
  rw [h] at low high
  have a := (mul_lt_mul_iff_right₀ hD).mp low
  have b := (mul_lt_mul_iff_right₀ hD).mp high
  omega

lemma repeated_bounds {P D q L : ℤ} (hD : 0 < D) (hq : 3 ≤ q)
    (large : 6 * L ≤ P) (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1))
    (divone : ¬ D ∣ 2 * P) :
    3 ≤ D ∧ q ≤ P - 2 * L + 1 := by
  have three : 3 ≤ D := by
    by_contra! bad
    interval_cases D <;> simp at divone
  refine ⟨three, ?_⟩
  have a := mul_le_mul_of_nonneg_right three (show 0 ≤ q - 2 by omega)
  omega

lemma repeated_alternatives {P D q L g E : ℤ} (hg : 1 ≤ g) (hL : 1 ≤ L)
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

lemma repeat_from_excess {P D q : ℤ} (hq : 0 < q - 1) (hs : 0 < 2 * P + D)
    (E : ℕ → ℤ) (base : E 0 = -D)
    (next : ∀ j, E (j + 1) = q * E j + (2 * P + D))
    (j : ℕ) (firstDef : E 1 < 0) (previousDef : E j < 0) (abundant : 0 < E (j + 1)) :
    D * (q - 2) < 2 * P ∧ 2 * P < D * (q - 1) ∧ E (j + 1) ≤ 2 * P + D - q := by
  have closed (t : ℕ) : (q - 1) * E t = q ^ t * (2 * P - D * (q - 2)) - (2 * P + D) := by
    induction t with
    | zero => rw [base, pow_zero]; ring
    | succ t ih =>
      rw [next, pow_succ]
      calc
        _ = q * ((q - 1) * E t) + (q - 1) * (2 * P + D) := by ring
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

lemma index_for_translate {A : Set ℤ} {T L H g r x : ℤ}
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

lemma middle_next {A B C : Set ℤ} {T P b L g r : ℤ}
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

def repNat (S : Finset ℕ) (x : ℕ) : Prop :=
  ∃ s ⊆ S, ∑ d ∈ s, d = x

def represented (n : ℕ) (x : ℤ) : Prop :=
  ∃ s : Finset ℕ, s ⊆ n.properDivisors ∧ (∑ d ∈ s, (d : ℤ)) = x

def properTotal (n : ℕ) : ℤ :=
  ∑ d ∈ n.properDivisors, (d : ℤ)

def excess (n : ℕ) : ℤ :=
  (sigma 1 n : ℤ) - 2 * (n : ℤ)

lemma repNat_to_represented {n x : ℕ} (h : repNat n.properDivisors x) :
    represented n (x : ℤ) := by
  obtain ⟨s, hs, hsum⟩ := h
  exact ⟨s, hs, by rw [← Nat.cast_sum]; exact_mod_cast hsum⟩

lemma pseudoperfect_of_excess {m : ℕ} (pos : 0 < m) {s : Finset ℕ}
    (subset : s ⊆ m.properDivisors)
    (sum : (∑ d ∈ s, (d : ℤ)) = excess m) : m.Pseudoperfect := by
  classical
  have total : (sigma 1 m : ℤ) = (∑ d ∈ m.properDivisors, (d : ℤ)) + m := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp
  have rest := sum_sdiff subset (f := fun x : ℕ => (x : ℤ))
  refine ⟨pos, m.properDivisors \ s, sdiff_subset, Int.ofNat_inj.mp ?_⟩
  push_cast
  dsimp [excess] at sum
  linarith only [sum, total, rest]

lemma sigma_split (n : ℕ) : (sigma 1 n : ℤ) = properTotal n + n := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  simp [properTotal]

lemma excess_step {b q : ℕ} (prime : q.Prime) (cop : b.Coprime q) (j : ℕ) :
    excess (b * q ^ (j + 1)) = q * excess (b * q ^ j) + (sigma 1 b : ℤ) := by
  have recurEq : sigma 1 (b * q ^ (j + 1)) = q * sigma 1 (b * q ^ j) + sigma 1 b := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right (j + 1)),
        isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right j),
        sigma_one_apply_prime_pow prime, sigma_one_apply_prime_pow prime, geom_sum_succ]
    ring
  dsimp [excess]
  have h1 : (sigma 1 (b * q ^ (j + 1)) : ℤ) = q * (sigma 1 (b * q ^ j) : ℤ) + (sigma 1 b : ℤ) := by
    exact_mod_cast recurEq
  rw [h1]
  ring

set_option maxHeartbeats 1600000 in
lemma certified_prime_power_gen {b q j : ℕ} (bpos : 1 < b) (hq : q.Prime)
    (coprime : b.Coprime q) (q3 : 3 ≤ q)
    (primitive : ∀ d ∈ (b * q ^ (j + 1)).properDivisors, d.Deficient)
    (L g : ℤ) (hL : 1 ≤ L) (hg : 1 ≤ g)
    (high : L ≤ excess (b * q ^ (j + 1)))
    (large : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ properTotal b)
    (simple : j = 0 → 2 ≤ (b : ℤ) - properTotal b)
    (middle : ∀ y : ℤ, L ≤ y → y ≤ properTotal b - L → represented b y)
    (gap : ∀ k : ℤ, 0 ≤ k → k < properTotal b → ∃ i : ℤ, represented b i ∧ k - g < i ∧ i ≤ k) :
    (b * q ^ (j + 1)).Pseudoperfect := by
  classical
  have combine {b' m' q' : ℕ} (hm : 0 < m') (bm : b' ∣ m') (hn : ¬ q' ∣ b')
      (hq' : 1 < q') {s t : Finset ℕ} (hs : s ⊆ b'.divisors) (ht : t ⊆ m'.properDivisors) :
      represented (q' * m') ((∑ d ∈ s, (d : ℤ)) + q' * ∑ d ∈ t, (d : ℤ)) := by
    let f (x : ℕ) := q' * x
    have positive : 0 < q' := by omega
    have inj : Function.Injective f := fun x y eq => Nat.eq_of_mul_eq_mul_left positive eq
    have subset : s ⊆ (q' * m').properDivisors := by
      intro x hx
      have d := Nat.dvd_of_mem_divisors (hs hx)
      have dm := d.trans bm
      refine Nat.mem_properDivisors.mpr ⟨dm.trans (dvd_mul_left _ _), ?_⟩
      exact lt_of_le_of_lt (Nat.le_of_dvd hm dm) (by simpa using Nat.mul_lt_mul_of_pos_right hq' hm)
    have scaled : t.image f ⊆ (q' * m').properDivisors := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      obtain ⟨div, lt⟩ := Nat.mem_properDivisors.mp (ht hz)
      exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_left q' div, Nat.mul_lt_mul_of_pos_left lt positive⟩
    have separate : Disjoint s (t.image f) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx'
      exact hn ((dvd_mul_right q' z).trans (Nat.dvd_of_mem_divisors (hs hx)))
    refine ⟨s ∪ t.image f, Finset.union_subset subset scaled, ?_⟩
    rw [sum_union separate, sum_image (fun x _ y _ eq => inj eq), Finset.mul_sum]
    simp [f]
  have layers {b' m' q' : ℕ} (hm : 0 < m') (bm : b' ∣ m') (hn : ¬ q' ∣ b')
      (hq' : 1 < q') {i y : ℤ} (hi : represented m' i) (hy : represented b' y) :
      represented (q' * m') (y + q' * i) ∧ represented (q' * m') (b' + y + q' * i) := by
    obtain ⟨s, hs, rfl⟩ := hy
    obtain ⟨t, ht, rfl⟩ := hi
    have hb : b' ≠ 0 := by
      intro z; subst b'; exact hm.ne' (by simpa using bm)
    have full : insert b' s ⊆ b'.divisors := by
      rw [← Nat.insert_self_properDivisors hb]
      exact Finset.insert_subset_insert _ hs
    constructor
    · exact combine hm bm hn hq' (hs.trans Nat.properDivisors_subset_divisors) ht
    · have nb : b' ∉ s := fun h => Nat.self_notMem_properDivisors (hs h)
      simpa [sum_insert nb] using combine hm bm hn hq' full ht
  have mpos : 0 < b * q ^ (j + 1) := by have := hq.pos; positivity
  let P := properTotal b
  let D : ℤ := b - P
  have bpos0 : 0 < b := by omega
  have hqZ : (3 : ℤ) ≤ q := by exact_mod_cast q3
  have total : represented b P := ⟨b.properDivisors, subset_rfl, rfl⟩
  have zero : represented b 0 := ⟨∅, by simp, by simp⟩
  have unit : represented b 1 := ⟨{1}, by simpa using Nat.one_mem_properDivisors_iff_one_lt.mpr bpos, by simp⟩
  have repE : represented (b * q ^ (j + 1)) (excess (b * q ^ (j + 1))) := by
    by_cases hj : j = 0
    · subst j
      simp only [zero_add, pow_one] at high ⊢
      have hD : 2 ≤ D := simple rfl
      have formula : excess (b * q) = 2 * P - D * (q - 1) := by
        have first := excess_step hq coprime 0
        simp only [pow_zero, pow_one, mul_one, zero_add] at first
        rw [first, sigma_split b]; dsimp [excess, P, D]; rw [sigma_split b]; ring
      have cases' := final_prime_alternatives hg hL hD hqZ large formula high
      have translate (i y : ℤ) (hi : represented b i) (hy : represented b y) :
          represented (b * q) (y + q * i) ∧ represented (b * q) (b + y + q * i) := by
        simpa only [mul_comm q b] using layers bpos0 (dvd_refl _) (hq.coprime_iff_not_dvd.mp coprime.symm) hq.one_lt hi hy
      rcases cases' with ⟨wide, join⟩ | ⟨wide, join, cap⟩ | basic
      · have gb := mul_nonneg (show 0 ≤ g - 1 by omega) (show 0 ≤ L by omega)
        have gg := mul_self_nonneg g
        have pL : L ≤ P := by change _ ≤ P at large; nlinarith only [large, hg, hL, gb, gg]
        have qP := mul_le_mul_of_nonneg_right hqZ (show 0 ≤ P by omega)
        have prod := mul_nonneg (show 0 ≤ D by omega) (show 0 ≤ (q : ℤ) - 1 by omega)
        exact middle_next (A := fun i => represented b i) (B := fun y => represented b y)
          (C := fun z => represented (b * q) z) (P := P) (T := P) (b := (b : ℤ))
          (by omega : (0 : ℤ) < q)
          (by simpa only [mul_comm (q : ℤ) g] using wide)
          (by change (b : ℤ) - P + 2 * L - 1 ≤ q * P at join; omega)
          total gap middle (fun i hi y hy => translate i y hi hy)
          _ high (by dsimp only [D] at formula prod; omega)
      · have eq : P + D = (b : ℤ) := by dsimp [D]; ring
        rcases four_interval_join wide join high cap with h | h | h | h
        · simpa using (translate 0 _ zero (middle _ h.1 h.2)).1
        · simpa using (translate 1 _ unit (middle _ h.1 h.2)).1
        · rw [eq] at h; simpa using (translate 0 _ zero (middle _ h.1 h.2)).2
        · rw [eq] at h; convert (translate 1 _ unit (middle _ h.1 h.2)).2 using 1; ring
      · simpa using (translate 0 _ zero (middle _ basic.1 basic.2)).1
    · have earlier (k : ℕ) (hk : k < j + 1) : properTotal (b * q ^ k) < (b * q ^ k : ℕ) := by
        have mem : b * q ^ k ∈ (b * q ^ (j + 1)).properDivisors := Nat.mem_properDivisors.mpr
          ⟨Nat.mul_dvd_mul_left b (pow_dvd_pow q hk.le),
           Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hq.one_lt hk) bpos0⟩
        have defic := primitive _ mem
        change ∑ d ∈ (b * q ^ k).properDivisors, d < b * q ^ k at defic
        dsimp only [properTotal]
        rw [← Nat.cast_sum]
        exact_mod_cast defic
      have earlierEx (k : ℕ) (hk : k < j + 1) : excess (b * q ^ k) < 0 := by
        dsimp only [excess]; rw [sigma_split]; linarith only [earlier k hk]
      have defBase : properTotal b < b := by simpa using earlier 0 (by omega)
      have firstDef : excess (b * q) < 0 := by simpa using earlierEx 1 (by omega)
      have prevDef : excess (b * q ^ j) < 0 := earlierEx j (by omega)
      have sig : (sigma 1 b : ℤ) = 2 * P + D := by rw [sigma_split]; dsimp [P, D]; ring
      have sPos : 0 < 2 * P + D := by rw [← sig]; exact_mod_cast (sigma_pos_iff.mpr bpos0 : 0 < sigma 1 b)
      have dPos : 0 < D := by dsimp [D, P]; omega
      let E (t : ℕ) := excess (b * q ^ t)
      have recurEq (t : ℕ) : E (t + 1) = (q : ℤ) * E t + (2 * P + D) := by rw [← sig]; exact excess_step hq coprime t
      have e0 : E 0 = -D := by simp only [E, pow_zero, mul_one, excess, sig]; dsimp [D]; ring
      have one : E 1 < 0 := by simpa [E] using firstDef
      obtain ⟨l, h, e⟩ := repeat_from_excess (q := (q : ℤ)) (by omega) sPos E e0 recurEq j one prevDef
        (lt_of_lt_of_le (by omega : 0 < L) high)
      have alt := repeated_alternatives (P := P) (D := D) (E := E (j + 1)) hg hL dPos hqZ large l h e
      have translate (i y : ℤ) (hi : represented b i) (hy : represented b y) :
          represented (b * q ^ (j + 1)) (y + q * i) ∧ represented (b * q ^ (j + 1)) (b + y + q * i) := by
        have divis : b ∣ b * q ^ j := dvd_mul_right _ _
        have pos : 0 < b * q ^ j := by have := hq.pos; positivity
        obtain ⟨t, sub, ht⟩ := hi
        have inclusion : represented (b * q ^ j) i := by
          refine ⟨t, fun d hd => ?_, ht⟩
          obtain ⟨dvd, lt⟩ := Nat.mem_properDivisors.mp (sub hd)
          exact Nat.mem_properDivisors.mpr ⟨dvd.trans divis, lt_of_lt_of_le lt (Nat.le_of_dvd pos divis)⟩
        have holds := layers pos divis (hq.coprime_iff_not_dvd.mp coprime.symm) hq.one_lt inclusion hy
        convert holds using 2 <;> ring
      rcases alt with ⟨wide, join, cap⟩ | ⟨wide, join, cap⟩
      · exact middle_next (A := fun i => represented b i) (B := fun y => represented b y)
          (C := fun z => represented (b * q ^ (j + 1)) z) (P := P) (T := P) (b := (b : ℤ))
          (by omega : (0 : ℤ) < q) (by simpa only [mul_comm (q : ℤ) g] using wide)
          (by change (b : ℤ) - P + 2 * L - 1 ≤ q * P at join; omega)
          total gap middle (fun i hi y hy => translate i y hi hy)
          _ high (by change excess (b * q ^ (j + 1)) ≤ 2 * P + ((b : ℤ) - P) + q * P - L at cap; omega)
      · have bEq : P + D = (b : ℤ) := by dsimp [D]; ring
        rcases four_interval_join wide join high cap with h | h | h | h
        · simpa using (translate 0 _ zero (middle _ h.1 h.2)).1
        · simpa using (translate 1 _ unit (middle _ h.1 h.2)).1
        · rw [bEq] at h; simpa using (translate 0 _ zero (middle _ h.1 h.2)).2
        · rw [bEq] at h; convert (translate 1 _ unit (middle _ h.1 h.2)).2 using 1; ring
  obtain ⟨s, hs, hsum⟩ := repE
  exact pseudoperfect_of_excess mpos hs hsum

end FinalPrime

section CoreLift

def inIvs (ivs : List (ℕ × ℕ)) (x : ℕ) : Prop :=
  ∃ ab ∈ ivs, ab.1 ≤ x ∧ x ≤ ab.2

def inIvsB (ivs : List (ℕ × ℕ)) (x : ℕ) : Bool :=
  ivs.any fun ab => decide (ab.1 ≤ x ∧ x ≤ ab.2)

lemma inIvs_of_inIvsB {ivs : List (ℕ × ℕ)} {x : ℕ} (h : inIvsB ivs x = true) :
    inIvs ivs x := by
  unfold inIvsB at h
  rw [List.any_eq_true] at h
  obtain ⟨ab, hab, hcond⟩ := h
  exact ⟨ab, hab, of_decide_eq_true hcond⟩

def insertIv (p : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [p]
  | q :: qs => if p.1 ≤ q.1 then p :: q :: qs else q :: insertIv p qs

def sortIvs : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | p :: ps => insertIv p (sortIvs ps)

def coalesceIvsGo : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, l => l
  | _, [] => []
  | _, [p] => [p]
  | fuel + 1, p :: q :: rest =>
    if q.1 ≤ p.2 + 1 then coalesceIvsGo fuel ((p.1, max p.2 q.2) :: rest)
    else p :: coalesceIvsGo fuel (q :: rest)

def coalesceIvs (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  coalesceIvsGo l.length l

def stepIvs (ivs : List (ℕ × ℕ)) (d : ℕ) : List (ℕ × ℕ) :=
  coalesceIvs (sortIvs (ivs ++ ivs.map (fun p => (p.1 + d, p.2 + d))))

def ivsOfList (ds : List ℕ) : List (ℕ × ℕ) :=
  ds.foldl stepIvs [(0, 0)]

lemma mem_insertIv {p q : ℕ × ℕ} {l : List (ℕ × ℕ)} :
    q ∈ insertIv p l ↔ q = p ∨ q ∈ l := by
  induction l with
  | nil => simp [insertIv]
  | cons a t ih =>
    dsimp [insertIv]
    split_ifs <;> simp [ih] <;> tauto

lemma mem_sortIvs {q : ℕ × ℕ} {l : List (ℕ × ℕ)} :
    q ∈ sortIvs l ↔ q ∈ l := by
  induction l with
  | nil => simp [sortIvs]
  | cons a t ih => simp [sortIvs, mem_insertIv, ih]

lemma inIvs_sortIvs {l : List (ℕ × ℕ)} {x : ℕ} :
    inIvs (sortIvs l) x ↔ inIvs l x := by
  simp [inIvs, mem_sortIvs]

lemma inIvs_coalesceIvsGo_imp {fuel : ℕ} {l : List (ℕ × ℕ)} {x : ℕ}
    (h : inIvs (coalesceIvsGo fuel l) x) : inIvs l x := by
  induction fuel generalizing l with
  | zero => exact h
  | succ f ih =>
    cases l with
    | nil => exact h
    | cons p rest =>
      cases rest with
      | nil => exact h
      | cons q tail =>
        dsimp only [coalesceIvsGo] at h
        split_ifs at h with hle
        · obtain ⟨ab, hab, h1, h2⟩ := ih h
          rcases List.mem_cons.mp hab with rfl | hmem
          · by_cases hx : x ≤ p.2
            · exact ⟨p, List.mem_cons_self, h1, hx⟩
            · exact ⟨q, List.mem_cons_of_mem _ List.mem_cons_self, by omega, by omega⟩
          · exact ⟨ab, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem), h1, h2⟩
        · obtain ⟨ab, hab, h1, h2⟩ := h
          rcases List.mem_cons.mp hab with hEq | hmem
          · rw [hEq] at h1 h2; exact ⟨p, List.mem_cons_self, h1, h2⟩
          · obtain ⟨cd, hcd, c1, c2⟩ := ih ⟨ab, hmem, h1, h2⟩
            exact ⟨cd, List.mem_cons_of_mem _ hcd, c1, c2⟩

lemma inIvs_coalesceIvs_imp {l : List (ℕ × ℕ)} {x : ℕ}
    (h : inIvs (coalesceIvs l) x) : inIvs l x :=
  inIvs_coalesceIvsGo_imp h

lemma stepIvs_sound {S : Finset ℕ} {ivs : List (ℕ × ℕ)} {d : ℕ}
    (hd : d ∉ S) (hsound : ∀ x, inIvs ivs x → repNat S x) :
    ∀ x, inIvs (stepIvs ivs d) x → repNat (insert d S) x := by
  intro x hx
  have h1 := inIvs_sortIvs.mp (inIvs_coalesceIvs_imp hx)
  obtain ⟨ab, hab, hlo, hhi⟩ := h1
  rcases List.mem_append.mp hab with hmem | hmap
  · obtain ⟨s, hs, hsum⟩ := hsound x ⟨ab, hmem, hlo, hhi⟩
    exact ⟨s, hs.trans (Finset.subset_insert d S), hsum⟩
  · obtain ⟨pq, hpq, rfl⟩ := List.mem_map.mp hmap
    obtain ⟨s, hs, hsum⟩ := hsound (x - d) ⟨pq, hpq, by omega, by omega⟩
    refine ⟨insert d s, Finset.insert_subset_insert d hs, ?_⟩
    rw [Finset.sum_insert (fun h => hd (hs h))]
    omega

lemma ivsOfList_sound_aux {ds : List ℕ} {S : Finset ℕ} {ivs : List (ℕ × ℕ)}
    (hnd : ds.Nodup) (hdisj : ∀ d ∈ ds, d ∉ S)
    (hsound : ∀ x, inIvs ivs x → repNat S x) :
    ∀ x, inIvs (ds.foldl stepIvs ivs) x → repNat (S ∪ ds.toFinset) x := by
  induction ds generalizing S ivs with
  | nil =>
    intro x hx
    simpa using hsound x hx
  | cons d rest ih =>
    rw [List.nodup_cons] at hnd
    have hdS : d ∉ S := hdisj d List.mem_cons_self
    have hstep := stepIvs_sound hdS hsound
    have hdisj' : ∀ e ∈ rest, e ∉ insert d S := by
      intro e he hmem
      rcases Finset.mem_insert.mp hmem with rfl | heS
      · exact hnd.1 he
      · exact hdisj e (List.mem_cons_of_mem _ he) heS
    have hres := ih hnd.2 hdisj' hstep
    intro x hx
    have hEq : S ∪ (d :: rest).toFinset = insert d S ∪ rest.toFinset := by
      ext y; simp [or_left_comm, or_comm, or_assoc]
    rw [hEq]
    exact hres x hx

lemma ivsOfList_sound {ds : List ℕ} {T : Finset ℕ}
    (hnd : ds.Nodup) (hsub : ∀ d ∈ ds, d ∈ T) :
    ∀ x, inIvs (ivsOfList ds) x → repNat T x := by
  have h0 : ∀ x, inIvs [(0, 0)] x → repNat ∅ x := by
    intro x ⟨ab, hab, h1, h2⟩
    simp only [List.mem_singleton] at hab
    subst hab
    have hx : x = 0 := by omega
    subst hx
    exact ⟨∅, subset_rfl, by simp⟩
  have h1 := ivsOfList_sound_aux hnd (S := ∅) (by simp) h0
  intro x hx
  obtain ⟨s, hs, hsum⟩ := h1 x hx
  refine ⟨s, fun y hy => ?_, hsum⟩
  have := hs hy
  simp only [Finset.empty_union, List.mem_toFinset] at this
  exact hsub y this

def checkGapsB : List (ℕ × ℕ) → ℕ → Bool
  | [], _ => true
  | [_], _ => true
  | p :: q :: rest, g => decide (p.1 ≤ p.2 ∧ p.2 < q.1 ∧ q.1 - p.2 ≤ g) && checkGapsB (q :: rest) g

lemma gap_of_checkGapsB {ivs : List (ℕ × ℕ)} {g : ℕ} (hg : 1 ≤ g)
    (hchk : checkGapsB ivs g = true) (hnonempty : ivs ≠ [])
    (hhead : ∀ p, ivs.head? = some p → p.1 = 0 ∧ p.1 ≤ p.2)
    (hlast : ∀ q, ivs.getLast? = some q → q.1 ≤ q.2) :
    ∀ k : ℕ, (∀ q, ivs.getLast? = some q → k ≤ q.2) →
      ∃ i : ℕ, inIvs ivs i ∧ k < i + g ∧ i ≤ k := by
  induction ivs with
  | nil => exact absurd rfl hnonempty
  | cons p rest ih =>
    cases rest with
    | nil =>
      intro k hk
      have hp := hhead p rfl
      have hkl : k ≤ p.2 := hk p rfl
      exact ⟨k, ⟨p, List.mem_cons_self, by omega, hkl⟩, by omega, le_rfl⟩
    | cons q tail =>
      simp only [checkGapsB, Bool.and_eq_true, decide_eq_true_eq] at hchk
      intro k hk
      have hp := hhead p rfl
      by_cases h1 : k ≤ p.2
      · exact ⟨k, ⟨p, List.mem_cons_self, by omega, h1⟩, by omega, le_rfl⟩
      · by_cases h2 : k < q.1
        · exact ⟨p.2, ⟨p, List.mem_cons_self, hp.2, le_rfl⟩, by omega, by omega⟩
        · -- recurse on q :: tail by shifting? No, direct induction on arbitrary head!
          have hsub : ∀ l : List (ℕ × ℕ), ∀ a : ℕ × ℕ,
              checkGapsB (a :: l) g = true → a.1 ≤ a.2 →
              (∀ z, (a :: l).getLast? = some z → z.1 ≤ z.2) →
              ∀ m : ℕ, a.1 ≤ m → (∀ z, (a :: l).getLast? = some z → m ≤ z.2) →
              ∃ i : ℕ, inIvs (a :: l) i ∧ m < i + g ∧ i ≤ m := by
            intro l
            induction l with
            | nil =>
              intro a _ ha _ m hm1 hm2
              exact ⟨m, ⟨a, List.mem_cons_self, hm1, hm2 a rfl⟩, by omega, le_rfl⟩
            | cons b tl ihl =>
              intro a hc ha hlt m hm1 hm2
              simp only [checkGapsB, Bool.and_eq_true, decide_eq_true_eq] at hc
              by_cases hma : m ≤ a.2
              · exact ⟨m, ⟨a, List.mem_cons_self, hm1, hma⟩, by omega, le_rfl⟩
              · by_cases hmb : m < b.1
                · exact ⟨a.2, ⟨a, List.mem_cons_self, ha, le_rfl⟩, by omega, by omega⟩
                · have hb : b.1 ≤ b.2 := by
                    cases tl with
                    | nil => exact hlt b rfl
                    | cons c tl' =>
                      have := hc.2
                      simp only [checkGapsB, Bool.and_eq_true, decide_eq_true_eq] at this
                      exact this.1.1
                  have hlt' : ∀ z, (b :: tl).getLast? = some z → z.1 ≤ z.2 := by
                    intro z hz; exact hlt z (by simpa using hz)
                  have hm2' : ∀ z, (b :: tl).getLast? = some z → m ≤ z.2 := by
                    intro z hz; exact hm2 z (by simpa using hz)
                  obtain ⟨i, hi, hi1, hi2⟩ := ihl b hc.2 hb hlt' m (by omega) hm2'
                  obtain ⟨ab, hab, ab1, ab2⟩ := hi
                  exact ⟨i, ⟨ab, List.mem_cons_of_mem _ hab, ab1, ab2⟩, hi1, hi2⟩
          have hqle : q.1 ≤ q.2 := by
            cases tail with
            | nil => exact hlast q rfl
            | cons r tr =>
              have := hchk.2
              simp only [checkGapsB, Bool.and_eq_true, decide_eq_true_eq] at this
              exact this.1.1
          obtain ⟨i, hi, hi1, hi2⟩ := hsub tail q hchk.2 hqle
            (fun z hz => hlast z (by simpa using hz)) k (by omega)
            (fun z hz => hk z (by simpa using hz))
          obtain ⟨ab, hab, ab1, ab2⟩ := hi
          exact ⟨i, ⟨ab, List.mem_cons_of_mem _ hab, ab1, ab2⟩, hi1, hi2⟩

/-- Adding one fresh element extends a covered interval [L, H] to [L, H + d]. -/
lemma repNat_insert_interval {S : Finset ℕ} {d L H : ℕ} (hd : d ∉ S)
    (hcov : ∀ y, L ≤ y → y ≤ H → repNat S y) (hstep : L + d ≤ H + 1) :
    ∀ y, L ≤ y → y ≤ H + d → repNat (insert d S) y := by
  intro y hLy hyH
  by_cases h1 : y ≤ H
  · obtain ⟨s, hs, hsum⟩ := hcov y hLy h1
    exact ⟨s, hs.trans (Finset.subset_insert d S), hsum⟩
  · obtain ⟨s, hs, hsum⟩ := hcov (y - d) (by omega) (by omega)
    refine ⟨insert d s, Finset.insert_subset_insert d hs, ?_⟩
    rw [Finset.sum_insert (fun h => hd (hs h))]
    omega

/-- Adding a list of distinct fresh elements extends [L, H] to [L, H + xs.sum]. -/
lemma repNat_append_list_interval {S : Finset ℕ} {L H : ℕ}
    (xs : List ℕ) (hnd : xs.Nodup) (hdisj : ∀ x ∈ xs, x ∉ S)
    (hcov : ∀ y, L ≤ y → y ≤ H → repNat S y)
    (hsteps : ∀ (pre : List ℕ) (x : ℕ) (suf : List ℕ),
      xs = pre ++ x :: suf → L + x ≤ H + pre.sum + 1) :
    ∀ y, L ≤ y → y ≤ H + xs.sum → repNat (S ∪ xs.toFinset) y := by
  induction xs generalizing S H with
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
      · exact hdisj z (List.mem_cons_of_mem _ hz) hzS
    have hsteps' : ∀ (pre : List ℕ) (z : ℕ) (suf : List ℕ),
        rest = pre ++ z :: suf → L + z ≤ (H + x) + pre.sum + 1 := by
      intro pre z suf heq
      have := hsteps (x :: pre) z suf (by simp [heq])
      simp only [List.sum_cons] at this
      omega
    have hres := ih hnd.2 hdisj' hcov1 hsteps'
    intro y hy1 hy2
    have hEq : S ∪ (x :: rest).toFinset = insert x S ∪ rest.toFinset := by
      ext z; simp [or_left_comm, or_comm, or_assoc]
    rw [hEq]
    exact hres y hy1 (by simp only [List.sum_cons] at hy2; omega)

/-- Adding fresh elements preserves directed gap g once the new central interval is covered. -/
lemma repNat_union_gap {S T : Finset ℕ} {L g : ℕ} (hg : 1 ≤ g) (hST : S ⊆ T)
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

def HasRelGap (u a_num a_den : ℕ) : Prop :=
  ∀ d ∈ u.properDivisors,
    a_den * d ≤ a_num * u + a_den * ∑ e ∈ u.properDivisors.filter (· < d), e

def HasAbsGap (u C : ℕ) : Prop :=
  ∀ d ∈ u.properDivisors,
    d ≤ C + ∑ e ∈ u.properDivisors.filter (· < d), e

lemma HasRelGap.mul_prime {u p a_num a_den : ℕ} (hp : p.Prime) (hu : 0 < u)
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
        _ ≤ a_num * (p * u) + a_den * ∑ e ∈ (p * u).properDivisors.filter (· < u), e := by
            gcongr
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
      have hup : a_num * u ≤ a_num * (p * u) :=
        Nat.mul_le_mul_left a_num (Nat.le_mul_of_pos_left u hp.pos)
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
        _ ≤ p * (a_num * u + a_den * ∑ e ∈ u.properDivisors.filter (· < d'), e) :=
            Nat.mul_le_mul_left p h1
        _ = a_num * (p * u) + a_den * (p * ∑ e ∈ u.properDivisors.filter (· < d'), e) := by ring
    have hinj : Function.Injective (fun e => p * e) := fun x y h => Nat.eq_of_mul_eq_mul_left hp.pos h
    have himg : (u.properDivisors.filter (· < d')).image (fun e => p * e) ⊆
        (p * u).properDivisors.filter (· < p * d') := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter] at he ⊢
      obtain ⟨hed, hel⟩ := Nat.mem_properDivisors.mp he.1
      exact ⟨Nat.mem_properDivisors.mpr
        ⟨Nat.mul_dvd_mul_left p hed, Nat.mul_lt_mul_of_pos_left hel hp.pos⟩,
        Nat.mul_lt_mul_of_pos_left he.2 hp.pos⟩
    have hsum_img : p * ∑ e ∈ u.properDivisors.filter (· < d'), e =
        ∑ x ∈ (u.properDivisors.filter (· < d')).image (fun e => p * e), x := by
      rw [Finset.sum_image (fun x _ y _ h => hinj h), Finset.mul_sum]
    have hle := Finset.sum_le_sum_of_subset (f := fun x => x) himg
    rw [← hsum_img] at hle
    exact le_trans hmul (Nat.add_le_add_left (Nat.mul_le_mul_left a_den hle) _)

lemma HasAbsGap.mul_prime {u p C : ℕ} (hp : p.Prime) (hu : 0 < u) (hpu : p ∣ u)
    (habs : HasAbsGap u C)
    (h_u : u ≤ C + ∑ x ∈ (p * u).properDivisors.filter (· < u), x)
    (h_small : ∀ d' ∈ u.properDivisors, p ∣ d' →
      C * p ≤ C + ∑ x ∈ (p * u).properDivisors.filter (fun x => x < p * d' ∧ ¬ p ∣ x), x) :
    HasAbsGap (p * u) C := by
  intro d hd
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
  by_cases hdu : d ∣ u
  · by_cases heq : d = u
    · subst d; exact h_u
    · have hdmem : d ∈ u.properDivisors :=
        Nat.mem_properDivisors.mpr ⟨hdu, lt_of_le_of_ne (Nat.le_of_dvd hu hdu) heq⟩
      have h1 := habs d hdmem
      have hsub : u.properDivisors.filter (· < d) ⊆ (p * u).properDivisors.filter (· < d) := by
        intro e he
        rw [Finset.mem_filter] at he ⊢
        obtain ⟨hed, hel⟩ := Nat.mem_properDivisors.mp he.1
        exact ⟨Nat.mem_properDivisors.mpr
          ⟨hed.trans (dvd_mul_left u p), lt_trans hel (by nlinarith [hp.one_lt])⟩, he.2⟩
      exact le_trans h1 (Nat.add_le_add_left (Finset.sum_le_sum_of_subset (f := fun x => x) hsub) C)
  · have hpd : p ∣ d := by
      by_contra hnp
      exact hdu ((hp.coprime_iff_not_dvd.mpr hnp).symm.dvd_of_dvd_mul_left hdvd)
    obtain ⟨d', rfl⟩ := hpd
    have hd'dvd : d' ∣ u := (Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd
    have hd'lt : d' < u := lt_of_mul_lt_mul_left hlt (Nat.zero_le p)
    have hd'mem : d' ∈ u.properDivisors := Nat.mem_properDivisors.mpr ⟨hd'dvd, hd'lt⟩
    have hpd' : p ∣ d' := by
      by_contra hnp
      obtain ⟨w, rfl⟩ := hpu
      have hcop : Nat.Coprime p d' := hp.coprime_iff_not_dvd.mpr hnp
      have hd'w : d' ∣ w := hcop.symm.dvd_of_dvd_mul_left hd'dvd
      exact hdu (Nat.mul_dvd_mul_left p hd'w)
    have h1 := habs d' hd'mem
    have hmul : p * d' ≤ C * p + p * ∑ e ∈ u.properDivisors.filter (· < d'), e := by
      calc p * d' ≤ p * (C + ∑ e ∈ u.properDivisors.filter (· < d'), e) := Nat.mul_le_mul_left p h1
        _ = C * p + p * ∑ e ∈ u.properDivisors.filter (· < d'), e := by ring
    let S1 := (u.properDivisors.filter (· < d')).image (fun e => p * e)
    let S2 := (p * u).properDivisors.filter (fun x => x < p * d' ∧ ¬ p ∣ x)
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx1
      exact (Finset.mem_filter.mp hx2).2.2 (dvd_mul_right p e)
    have hsub1 : S1 ⊆ (p * u).properDivisors.filter (· < p * d') := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter] at he ⊢
      obtain ⟨hed, hel⟩ := Nat.mem_properDivisors.mp he.1
      exact ⟨Nat.mem_properDivisors.mpr
        ⟨Nat.mul_dvd_mul_left p hed, Nat.mul_lt_mul_of_pos_left hel hp.pos⟩,
        Nat.mul_lt_mul_of_pos_left he.2 hp.pos⟩
    have hsub2 : S2 ⊆ (p * u).properDivisors.filter (· < p * d') := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
    have hinj : Function.Injective (fun e => p * e) := fun x y h => Nat.eq_of_mul_eq_mul_left hp.pos h
    have hsum1 : p * ∑ e ∈ u.properDivisors.filter (· < d'), e = ∑ x ∈ S1, x := by
      rw [Finset.sum_image (fun x _ y _ h => hinj h), Finset.mul_sum]
    have hsumU : ∑ x ∈ S1, x + ∑ x ∈ S2, x ≤ ∑ x ∈ (p * u).properDivisors.filter (· < p * d'), x := by
      rw [← Finset.sum_union hdisj]
      exact Finset.sum_le_sum_of_subset (f := fun x => x) (Finset.union_subset hsub1 hsub2)
    have hsm := h_small d' hd'mem hpd'
    dsimp only [S1, S2] at hsum1 hsumU
    linarith [hmul, hsum1, hsumU, hsm]

/-- Lift a solid-core interval [L, P(n) - L] and gap g from n = r^a * u to r * n,
    assuming every fresh divisor x = r^(a+1) * d (d in u.properDivisors) fits in the running width,
    followed by n itself at the end. -/
lemma lift_prime_step_no_interleave {u r a L g : ℕ} (hr : r.Prime) (hu : 0 < u) (ha : 1 ≤ a)
    (hcop : ¬ r ∣ u) (hg : 1 ≤ g)
    (hL : L ≤ ∑ d ∈ (r ^ a * u).properDivisors, d)
    (hcov : ∀ y, L ≤ y → y ≤ (∑ d ∈ (r ^ a * u).properDivisors, d) - L →
      repNat (r ^ a * u).properDivisors y)
    (hgap : ∀ k, k < ∑ d ∈ (r ^ a * u).properDivisors, d →
      ∃ i, repNat (r ^ a * u).properDivisors i ∧ k < i + g ∧ i ≤ k)
    (hstep_d : ∀ d ∈ u.properDivisors,
      2 * L + r ^ (a + 1) * d ≤
        (∑ e ∈ (r ^ a * u).properDivisors, e) +
        r ^ (a + 1) * (∑ e ∈ u.properDivisors.filter (· < d), e) + 1)
    (hstep_n : 2 * L + r ^ a * u ≤
      (∑ e ∈ (r ^ a * u).properDivisors, e) +
      r ^ (a + 1) * (∑ e ∈ u.properDivisors, e) + 1) :
    (∀ y, L ≤ y → y ≤ (∑ d ∈ (r ^ (a + 1) * u).properDivisors, d) - L →
      repNat (r ^ (a + 1) * u).properDivisors y) ∧
    (∀ k, k < ∑ d ∈ (r ^ (a + 1) * u).properDivisors, d →
      ∃ i, repNat (r ^ (a + 1) * u).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
  classical
  let n := r ^ a * u
  let n' := r ^ (a + 1) * u
  have hn_pos : 0 < n := by have := hr.pos; positivity
  let ds := u.properDivisors.sort (· ≤ ·)
  let xs := ds.map (fun d => r ^ (a + 1) * d) ++ [n]
  have hds_nd : ds.Nodup := Finset.sort_nodup _ _
  have hds_sorted : ds.Pairwise (· < ·) :=
    ((Finset.pairwise_sort u.properDivisors (· ≤ ·)).and (List.nodup_iff_pairwise_ne.mp hds_nd)).imp
      (fun h => lt_of_le_of_ne h.1 h.2)
  have hmap_mul : ∀ l : List ℕ, (l.map (fun d => r ^ (a + 1) * d)).sum = r ^ (a + 1) * l.sum := by
    intro l; induction l with
    | nil => simp
    | cons hd tl ih => simp [ih, mul_add]
  have hinj_r : Function.Injective (fun d => r ^ (a + 1) * d) :=
    fun x y h => Nat.eq_of_mul_eq_mul_left (pow_pos hr.pos _) h
  have hxs_nd : xs.Nodup := by
    rw [List.nodup_append]
    refine ⟨hds_nd.map hinj_r, List.nodup_singleton n, ?_⟩
    intro x hx y hy heq
    simp only [List.mem_singleton] at hy
    subst hy; subst heq
    obtain ⟨d, _, hEq⟩ := List.mem_map.mp hx
    have hmul : r ^ (a + 1) ∣ r ^ a * u := ⟨d, hEq.symm⟩
    rw [pow_succ] at hmul
    exact hcop ((Nat.mul_dvd_mul_iff_left (pow_pos hr.pos a)).mp hmul)
  have hdisj : ∀ x ∈ xs, x ∉ n.properDivisors := by
    intro x hx hmem
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hmem
    rcases List.mem_append.mp hx with hmap | hsing
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hmap
      have hmul : r ^ (a + 1) ∣ r ^ a * u := (dvd_mul_right _ d).trans hdvd
      rw [pow_succ] at hmul
      exact hcop ((Nat.mul_dvd_mul_iff_left (pow_pos hr.pos a)).mp hmul)
    · simp only [List.mem_singleton] at hsing
      omega
  have hUnion : n.properDivisors ∪ xs.toFinset = n'.properDivisors := by
    ext x
    simp only [Finset.mem_union, List.mem_toFinset, xs, List.mem_append, List.mem_map,
      List.mem_singleton, ds, Finset.mem_sort, Nat.mem_properDivisors]
    constructor
    · rintro (⟨h1, h2⟩ | (⟨d, ⟨hd1, hd2⟩, rfl⟩ | rfl))
      · refine ⟨h1.trans ?_, lt_of_lt_of_le h2 ?_⟩
        · exact Nat.mul_dvd_mul_right (pow_dvd_pow r (Nat.le_succ a)) u
        · exact Nat.mul_le_mul_right u (pow_le_pow_right₀ hr.one_lt.le (Nat.le_succ a))
      · exact ⟨Nat.mul_dvd_mul_left _ hd1, Nat.mul_lt_mul_of_pos_left hd2 (pow_pos hr.pos _)⟩
      · exact ⟨Nat.mul_dvd_mul_right (pow_dvd_pow r (Nat.le_succ a)) u,
          Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hr.one_lt (Nat.lt_succ_self a)) hu⟩
    · rintro ⟨hx1, hx2⟩
      by_cases hdiv : r ^ (a + 1) ∣ x
      · obtain ⟨d, rfl⟩ := hdiv
        right; left
        refine ⟨d, ⟨(Nat.mul_dvd_mul_iff_left (pow_pos hr.pos _)).mp hx1,
          lt_of_mul_lt_mul_left hx2 (Nat.zero_le _)⟩, rfl⟩
      · have hx_dvd_n : x ∣ n := by
          have hx0 : x ≠ 0 := fun h => by
            subst h; exact hdiv (dvd_zero _)
          have hfx : x.factorization r ≤ a := by
            by_contra! hgt
            exact hdiv ((hr.pow_dvd_iff_le_factorization hx0).mpr hgt)
          have h1 : r ^ x.factorization r ∣ r ^ a := pow_dvd_pow r hfx
          have h2 : x / r ^ x.factorization r ∣ u := by
            have hd' : x / r ^ x.factorization r ∣ r ^ (a + 1) * u :=
              (Nat.ordCompl_dvd x r).trans hx1
            exact ((hr.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hr hx0)).pow_left _).symm.dvd_of_dvd_mul_left hd'
          rw [← Nat.ordProj_mul_ordCompl_eq_self x r]
          exact Nat.mul_dvd_mul h1 h2
        by_cases hxn : x = n
        · right; right; exact hxn
        · left; exact ⟨hx_dvd_n, lt_of_le_of_ne (Nat.le_of_dvd hn_pos hx_dvd_n) hxn⟩
  have hds_sum : ds.sum = ∑ d ∈ u.properDivisors, d := by
    rw [← Finset.sum_toList]
    exact (Finset.sort_perm_toList u.properDivisors (· ≤ ·)).sum_eq
  have hxs_sum : xs.sum = r ^ (a + 1) * (∑ d ∈ u.properDivisors, d) + n := by
    simp only [xs, List.sum_append, List.sum_singleton, hmap_mul, hds_sum]
  have hP_eq : ∑ d ∈ n'.properDivisors, d = (∑ d ∈ n.properDivisors, d) + xs.sum := by
    rw [← hUnion, Finset.sum_union (by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact hdisj x (List.mem_toFinset.mp hx2) hx1)]
    congr 1
    simpa using List.sum_toFinset id hxs_nd
  have hsteps : ∀ (pre : List ℕ) (x : ℕ) (suf : List ℕ),
      xs = pre ++ x :: suf → L + x ≤ ((∑ e ∈ n.properDivisors, e) - L) + pre.sum + 1 := by
    intro pre x suf heq
    have hsplit : pre.length < ds.length ∨ pre.length = ds.length := by
      have hlen : xs.length = ds.length + 1 := by simp [xs]
      have hlen2 : xs.length = pre.length + 1 + suf.length := by rw [heq]; simp; omega
      omega
    rcases hsplit with hlt_len | heq_len
    · -- x is inside ds.map ...
      have htake : pre ++ x :: suf = ds.map (fun d => r ^ (a + 1) * d) ++ [n] := heq.symm
      let pre_d := ds.take pre.length
      have hpre_eq : pre = pre_d.map (fun d => r ^ (a + 1) * d) := by
        have := congrArg (List.take pre.length) htake
        simp only [List.take_left, List.take_append_of_le_length (by simp; omega : pre.length ≤ (ds.map (fun d => r ^ (a + 1) * d)).length)] at this
        simpa [pre_d, List.map_take] using this
      have hx_eq : x = r ^ (a + 1) * ds[pre.length] := by
        have hget := congrArg (fun l => l[pre.length]?) htake
        simp only [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero] at hget
        rw [List.getElem?_append_left (by simp; omega)] at hget
        simp only [List.getElem?_map, List.getElem?_eq_getElem hlt_len, Option.map_some, Option.some.injEq] at hget
        exact hget
      let d := ds[pre.length]
      have hd_mem : d ∈ u.properDivisors := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hlt_len)
      have hpre_sub : u.properDivisors.filter (· < d) ⊆ pre_d.toFinset := by
        intro e he
        rw [Finset.mem_filter] at he
        have he_ds : e ∈ ds := (Finset.mem_sort (· ≤ ·)).mpr he.1
        obtain ⟨idx, hidx, hget_e⟩ := List.getElem_of_mem he_ds
        have hidx_lt : idx < pre.length := by
          by_contra! hge
          rcases eq_or_lt_of_le hge with rfl | hgt
          · omega
          · have := List.pairwise_iff_getElem.mp hds_sorted pre.length idx hlt_len hidx hgt
            omega
        rw [List.mem_toFinset]
        have : ds[idx] ∈ ds.take pre.length := by
          rw [List.mem_iff_getElem]
          exact ⟨idx, by simp; omega, by simp [List.getElem_take]⟩
        simpa [pre_d, hget_e] using this
      have hpre_sum_ge : r ^ (a + 1) * (∑ e ∈ u.properDivisors.filter (· < d), e) ≤ pre.sum := by
        rw [hpre_eq, hmap_mul]
        apply Nat.mul_le_mul_left
        have htf : ∑ e ∈ pre_d.toFinset, e = pre_d.sum := by simpa using List.sum_toFinset id hds_nd.take
        rw [← htf]
        exact Finset.sum_le_sum_of_subset (f := fun e => e) hpre_sub
      have hs := hstep_d d hd_mem
      have hx_eq' : x = r ^ (a + 1) * d := hx_eq
      rw [hx_eq']
      have hL' : L ≤ ∑ e ∈ n.properDivisors, e := hL
      have hs' : 2 * L + r ^ (a + 1) * d ≤
          (∑ e ∈ n.properDivisors, e) + r ^ (a + 1) * ∑ e ∈ u.properDivisors.filter (· < d), e + 1 := hs
      omega
    · -- x = n at the end
      have hpre_eq : pre = ds.map (fun d => r ^ (a + 1) * d) := by
        have := congrArg (List.take pre.length) heq.symm
        simp only [List.take_left] at this
        have hlen_m : (ds.map (fun d => r ^ (a + 1) * d)).length = pre.length := by simp [heq_len]
        rw [List.take_append_of_le_length hlen_m.ge, ← hlen_m, List.take_length] at this
        exact this
      have hx_eq : x = n := by
        have hget := congrArg (fun l => l[pre.length]?) heq.symm
        simp only [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero] at hget
        have hlen_m : (ds.map (fun d => r ^ (a + 1) * d)).length = pre.length := by simp [heq_len]
        rw [List.getElem?_append_right hlen_m.le, hlen_m, Nat.sub_self, List.getElem?_cons_zero] at hget
        exact Option.some.inj hget
      have hpre_sum : pre.sum = r ^ (a + 1) * (∑ d ∈ u.properDivisors, d) := by
        rw [hpre_eq, hmap_mul, hds_sum]
      rw [hx_eq, hpre_sum]
      have hL' : L ≤ ∑ e ∈ n.properDivisors, e := hL
      have hsn' : 2 * L + n ≤ (∑ e ∈ n.properDivisors, e) + r ^ (a + 1) * ∑ e ∈ u.properDivisors, e + 1 := hstep_n
      omega
  have hcov' := repNat_append_list_interval xs hxs_nd hdisj hcov hsteps
  rw [hUnion] at hcov'
  have hcov_final : ∀ y, L ≤ y → y ≤ (∑ d ∈ n'.properDivisors, d) - L → repNat n'.properDivisors y := by
    intro y hy1 hy2
    have hL' : L ≤ ∑ d ∈ n.properDivisors, d := hL
    have hy2' : y ≤ ((∑ d ∈ n.properDivisors, d) - L) + xs.sum := by omega
    exact hcov' y hy1 hy2'
  have hsub_n : n.properDivisors ⊆ n'.properDivisors := by
    rw [← hUnion]; exact Finset.subset_union_left
  exact ⟨hcov_final, repNat_union_gap hg hsub_n hL hcov_final hgap⟩

end CoreLift

section Arithmetic

def ppSum (p a : ℕ) : ℕ :=
  (p ^ (a + 1) - 1) / (p - 1)

lemma geom_sum_mul_sub {p a : ℕ} (hp : 2 ≤ p) :
    (∑ i ∈ range (a + 1), p ^ i) * (p - 1) = p ^ (a + 1) - 1 := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have h1 : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ p ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2, (show 1 ≤ p by omega)]
    ring

lemma ppSum_eq_sigma {p a : ℕ} (hp : p.Prime) :
    ppSum p a = sigma 1 (p ^ a) := by
  rw [sigma_one_apply_prime_pow hp, ppSum]
  have h1 := geom_sum_mul_sub (a := a) hp.two_le
  rw [← h1, Nat.mul_div_cancel _ (by have := hp.two_le; omega)]

lemma ppSum_mul_sub {p a : ℕ} (hp : 2 ≤ p) :
    ppSum p a * (p - 1) = p ^ (a + 1) - 1 := by
  have hdiv : (p - 1) ∣ (p ^ (a + 1) - 1) :=
    ⟨∑ i ∈ range (a + 1), p ^ i, by rw [mul_comm, geom_sum_mul_sub hp]⟩
  exact Nat.div_mul_cancel hdiv

lemma ppSum_mono_exp {p a b : ℕ} (hp : 2 ≤ p) (hab : a ≤ b) :
    ppSum p a * p ^ b ≤ ppSum p b * p ^ a := by
  have hpos : 0 < p - 1 := by omega
  apply Nat.le_of_mul_le_mul_right _ hpos
  have ha := ppSum_mul_sub (a := a) hp
  have hb := ppSum_mul_sub (a := b) hp
  have h1 : ppSum p a * p ^ b * (p - 1) = (p ^ (a + 1) - 1) * p ^ b := by
    calc ppSum p a * p ^ b * (p - 1) = (ppSum p a * (p - 1)) * p ^ b := by ring
      _ = (p ^ (a + 1) - 1) * p ^ b := by rw [ha]
  have h2 : ppSum p b * p ^ a * (p - 1) = (p ^ (b + 1) - 1) * p ^ a := by
    calc ppSum p b * p ^ a * (p - 1) = (ppSum p b * (p - 1)) * p ^ a := by ring
      _ = (p ^ (b + 1) - 1) * p ^ a := by rw [hb]
  rw [h1, h2]
  have hpa : p ^ a ≤ p ^ b := pow_le_pow_right₀ (by omega) hab
  have hpow1 : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  have hpow2 : 1 ≤ p ^ (b + 1) := Nat.one_le_pow _ _ (by omega)
  zify [hpow1, hpow2]
  have heq : ((p : ℤ) ^ (a + 1) - 1) * (p : ℤ) ^ b = (p : ℤ) ^ (a + b + 1) - (p : ℤ) ^ b := by
    ring
  have heq2 : ((p : ℤ) ^ (b + 1) - 1) * (p : ℤ) ^ a = (p : ℤ) ^ (a + b + 1) - (p : ℤ) ^ a := by
    ring
  rw [heq, heq2]
  have : (p : ℤ) ^ a ≤ (p : ℤ) ^ b := by exact_mod_cast hpa
  linarith

lemma ppSum_lt_lim {p a : ℕ} (hp : 2 ≤ p) :
    ppSum p a * (p - 1) < p * p ^ a := by
  rw [ppSum_mul_sub hp, ← pow_succ']
  have : 1 ≤ p ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
  omega

lemma ppSum_anti_base {p q a : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    ppSum q a * p ^ a ≤ ppSum p a * q ^ a := by
  induction a with
  | zero =>
    simp only [ppSum, zero_add, pow_one, pow_zero, mul_one]
    rw [Nat.div_self (by omega), Nat.div_self (by omega)]
  | succ k ih =>
    have hq : 2 ≤ q := by omega
    have hsp : ppSum p (k + 1) = ppSum p k * p + 1 := by
      have hp1 : 0 < p - 1 := by omega
      apply Nat.eq_of_mul_eq_mul_right hp1
      rw [ppSum_mul_sub hp, add_mul, one_mul]
      have h1 : ppSum p k * p * (p - 1) = (p ^ (k + 1) - 1) * p := by
        calc ppSum p k * p * (p - 1) = (ppSum p k * (p - 1)) * p := by ring
          _ = (p ^ (k + 1) - 1) * p := by rw [ppSum_mul_sub hp]
      rw [h1]
      have hge : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
      have hge2 : 1 ≤ p ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
      zify [hge, hge2, (show 1 ≤ p by omega)]
      ring
    have hsq : ppSum q (k + 1) = ppSum q k * q + 1 := by
      have hq1 : 0 < q - 1 := by omega
      apply Nat.eq_of_mul_eq_mul_right hq1
      rw [ppSum_mul_sub hq, add_mul, one_mul]
      have h1 : ppSum q k * q * (q - 1) = (q ^ (k + 1) - 1) * q := by
        calc ppSum q k * q * (q - 1) = (ppSum q k * (q - 1)) * q := by ring
          _ = (q ^ (k + 1) - 1) * q := by rw [ppSum_mul_sub hq]
      rw [h1]
      have hge : 1 ≤ q ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
      have hge2 : 1 ≤ q ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
      zify [hge, hge2, (show 1 ≤ q by omega)]
      ring
    rw [hsp, hsq, pow_succ, pow_succ]
    have hpk : p ^ k * p ≤ q ^ k * q := Nat.mul_le_mul (pow_le_pow_left₀ (by omega) hpq k) hpq
    have hmul := Nat.mul_le_mul_right (p * q) ih
    calc (ppSum q k * q + 1) * (p ^ k * p)
        = (ppSum q k * p ^ k) * (p * q) + p ^ k * p := by ring
      _ ≤ (ppSum p k * q ^ k) * (p * q) + q ^ k * q := Nat.add_le_add hmul hpk
      _ = (ppSum p k * p + 1) * (q ^ k * q) := by ring

def hiNum (p : ℕ) : Option ℕ → ℕ
  | some a => ppSum p a
  | none => p

def hiDen (p : ℕ) : Option ℕ → ℕ
  | some a => p ^ a
  | none => p - 1

def leOpt (a : ℕ) : Option ℕ → Prop
  | some hi => a ≤ hi
  | none => True

lemma ppSum_le_hi {p a : ℕ} {o : Option ℕ} (hp : 2 ≤ p) (ho : leOpt a o) :
    ppSum p a * hiDen p o ≤ hiNum p o * p ^ a := by
  cases o with
  | none =>
    simp only [hiNum, hiDen]
    exact (ppSum_lt_lim hp).le
  | some h =>
    simp only [hiNum, hiDen]
    exact ppSum_mono_exp hp ho

end Arithmetic

section CoreLiftExtra

def properDivsSum (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

lemma properDivsSum_eq_sigma_sub (n : ℕ) :
    properDivsSum n = sigma 1 n - n := by
  rw [properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

lemma abund_iff_nat {n : ℕ} (hn : 0 < n) : n.Abundant ↔ 2 * n < sigma 1 n := by
  rw [Nat.Abundant, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

lemma defic_iff_nat {n : ℕ} (hn : 0 < n) : n.Deficient ↔ sigma 1 n < 2 * n := by
  rw [Nat.Deficient, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

lemma ppSum_succ {p k : ℕ} (hp : 2 ≤ p) :
    ppSum p (k + 1) = ppSum p k * p + 1 := by
  have hp1 : 0 < p - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hp1
  rw [ppSum_mul_sub hp, add_mul, one_mul]
  have h1 : ppSum p k * p * (p - 1) = (p ^ (k + 1) - 1) * p := by
    calc ppSum p k * p * (p - 1) = (ppSum p k * (p - 1)) * p := by ring
      _ = (p ^ (k + 1) - 1) * p := by rw [ppSum_mul_sub hp]
  rw [h1]
  have hge1 : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have hge2 : 1 ≤ p ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
  zify [hge1, hge2, (show 1 ≤ p by omega)]
  ring

lemma ppSum_add_two {p k : ℕ} (hp : 2 ≤ p) :
    ppSum p (k + 2) = ppSum p k * (p * p) + p + 1 := by
  rw [ppSum_succ hp, ppSum_succ hp]; ring

lemma ppSum_zero {p : ℕ} (hp : 2 ≤ p) : ppSum p 0 = 1 := by
  simp only [ppSum, zero_add, pow_one]
  exact Nat.div_self (by omega)

lemma ppSum_one {p : ℕ} (hp : 2 ≤ p) : ppSum p 1 = p + 1 := by
  rw [ppSum_succ hp, ppSum_zero hp]; ring

lemma ppSum_pos {p k : ℕ} (hp : 2 ≤ p) : 0 < ppSum p k := by
  induction k with
  | zero => rw [ppSum_zero hp]; omega
  | succ n _ => rw [ppSum_succ hp]; omega

lemma three_dvd_ppSum_odd {p a : ℕ} (hp : 2 ≤ p) (hp3 : p % 3 = 2) (ha : a % 2 = 1) :
    3 ∣ ppSum p a := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  have hpow : p ^ (2 * k + 2) % 3 = 1 := by
    have h2 : (p * p) % 3 = 1 := by
      have := Nat.mul_mod p p 3; rw [hp3] at this; omega
    have heq : p ^ (2 * k + 2) = (p * p) ^ (k + 1) := by ring
    rw [heq, Nat.pow_mod, h2]; simp
  have hdiv : 3 ∣ p ^ (2 * k + 2) - 1 := by
    have h1 : 1 ≤ p ^ (2 * k + 2) := Nat.one_le_pow _ _ (by omega)
    omega
  have hmul := ppSum_mul_sub (p := p) (a := 2 * k + 1) hp
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at hmul
  rw [← hmul] at hdiv
  have hcop : Nat.Coprime 3 (p - 1) := by
    have hmod : (p - 1) % 3 = 1 := by omega
    rw [Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)]
    intro h; have := Nat.mod_eq_zero_of_dvd h; omega
  exact hcop.dvd_of_dvd_mul_right hdiv

lemma two_dvd_ppSum_odd {p a : ℕ} (hp : p.Prime) (hodd : Odd p) (ha : a % 2 = 1) :
    2 ∣ ppSum p a := by
  rw [ppSum_eq_sigma hp, sigma_one_apply_prime_pow hp]
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  clear ha
  induction k with
  | zero =>
    simp only [mul_zero, zero_add, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    obtain ⟨t, ht⟩ := hodd; exact ⟨t + 1, by omega⟩
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 + 1 = (2 * m + 1 + 1) + 2 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
    obtain ⟨t, ht⟩ := ih
    have h1 : Odd (p ^ (2 * m + 1 + 1)) := hodd.pow
    have h2 : Odd (p ^ (2 * m + 1 + 1 + 1)) := hodd.pow
    obtain ⟨u, hu⟩ := h1
    obtain ⟨v, hv⟩ := h2
    exact ⟨t + u + v + 1, by rw [ht, hu, hv]; ring⟩

lemma frac_anti {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : b * (a - 1) ≤ a * (b - 1) := by
  zify [(show 1 ≤ a by omega), (show 1 ≤ b by omega)]; nlinarith

lemma sigma_mul_coprime_three {p1 p2 p3 a b c : ℕ}
    (h1 : p1.Prime) (h2 : p2.Prime) (h3 : p3.Prime)
    (h12 : p1 < p2) (h23 : p2 < p3) :
    sigma 1 (p1 ^ a * p2 ^ b * p3 ^ c) = ppSum p1 a * ppSum p2 b * ppSum p3 c := by
  have c12 : Nat.Coprime (p1 ^ a) (p2 ^ b) :=
    ((Nat.coprime_primes h1 h2).mpr (by omega)).pow a b
  have c123 : Nat.Coprime (p1 ^ a * p2 ^ b) (p3 ^ c) :=
    (Nat.Coprime.mul_left (((Nat.coprime_primes h1 h3).mpr (by omega)).pow_left a)
      (((Nat.coprime_primes h2 h3).mpr (by omega)).pow_left b)).pow_right c
  rw [isMultiplicative_sigma.map_mul_of_coprime c123,
      isMultiplicative_sigma.map_mul_of_coprime c12,
      ← ppSum_eq_sigma h1, ← ppSum_eq_sigma h2, ← ppSum_eq_sigma h3]

lemma sigma_mul_coprime_four {p1 p2 p3 p4 a b c d : ℕ}
    (h1 : p1.Prime) (h2 : p2.Prime) (h3 : p3.Prime) (h4 : p4.Prime)
    (h12 : p1 < p2) (h23 : p2 < p3) (h34 : p3 < p4) :
    sigma 1 (p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) =
      ppSum p1 a * ppSum p2 b * ppSum p3 c * ppSum p4 d := by
  have c1234 : Nat.Coprime (p1 ^ a * p2 ^ b * p3 ^ c) (p4 ^ d) :=
    (Nat.Coprime.mul_left
      (Nat.Coprime.mul_left (((Nat.coprime_primes h1 h4).mpr (by omega)).pow_left a)
        (((Nat.coprime_primes h2 h4).mpr (by omega)).pow_left b))
      (((Nat.coprime_primes h3 h4).mpr (by omega)).pow_left c)).pow_right d
  rw [isMultiplicative_sigma.map_mul_of_coprime c1234,
      sigma_mul_coprime_three h1 h2 h3 h12 h23, ← ppSum_eq_sigma h4]

lemma sigma_mul_coprime_five {p1 p2 p3 p4 q a b c d e : ℕ}
    (h1 : p1.Prime) (h2 : p2.Prime) (h3 : p3.Prime) (h4 : p4.Prime) (hq : q.Prime)
    (h12 : p1 < p2) (h23 : p2 < p3) (h34 : p3 < p4) (h4q : p4 < q) :
    sigma 1 (p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d * q ^ e) =
      ppSum p1 a * ppSum p2 b * ppSum p3 c * ppSum p4 d * ppSum q e := by
  have c5 : Nat.Coprime (p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) (q ^ e) :=
    (Nat.Coprime.mul_left
      (Nat.Coprime.mul_left
        (Nat.Coprime.mul_left (((Nat.coprime_primes h1 hq).mpr (by omega)).pow_left a)
          (((Nat.coprime_primes h2 hq).mpr (by omega)).pow_left b))
        (((Nat.coprime_primes h3 hq).mpr (by omega)).pow_left c))
      (((Nat.coprime_primes h4 hq).mpr (by omega)).pow_left d)).pow_right e
  rw [isMultiplicative_sigma.map_mul_of_coprime c5,
      sigma_mul_coprime_four h1 h2 h3 h4 h12 h23 h34, ← ppSum_eq_sigma hq]

lemma properDivsSum_mono_of_sigma_ratio {n0 n : ℕ}
    (hmul : sigma 1 n0 * n ≤ sigma 1 n * n0) :
    properDivsSum n0 * n ≤ properDivsSum n * n0 := by
  have hge0 : n0 ≤ sigma 1 n0 := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
  have hge1 : n ≤ sigma 1 n := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
  rw [properDivsSum_eq_sigma_sub, properDivsSum_eq_sigma_sub]
  zify [hge0, hge1]
  have hmulZ : (sigma 1 n0 : ℤ) * (n : ℤ) ≤ (sigma 1 n : ℤ) * (n0 : ℤ) := by exact_mod_cast hmul
  linarith

lemma properDivsSum_ratio_mono_3p {p1 p2 p3 a0 b0 c0 a b c : ℕ}
    (h1 : p1.Prime) (h2 : p2.Prime) (h3 : p3.Prime) (h12 : p1 < p2) (h23 : p2 < p3)
    (ha : a0 ≤ a) (hb : b0 ≤ b) (hc : c0 ≤ c) :
    properDivsSum (p1 ^ a0 * p2 ^ b0 * p3 ^ c0) * (p1 ^ a * p2 ^ b * p3 ^ c) ≤
    properDivsSum (p1 ^ a * p2 ^ b * p3 ^ c) * (p1 ^ a0 * p2 ^ b0 * p3 ^ c0) := by
  apply properDivsSum_mono_of_sigma_ratio
  rw [sigma_mul_coprime_three h1 h2 h3 h12 h23, sigma_mul_coprime_three h1 h2 h3 h12 h23]
  have m1 := ppSum_mono_exp h1.two_le ha
  have m2 := ppSum_mono_exp h2.two_le hb
  have m3 := ppSum_mono_exp h3.two_le hc
  have m123 := Nat.mul_le_mul (Nat.mul_le_mul m1 m2) m3
  linarith

lemma properDivsSum_ratio_mono_4p {p1 p2 p3 p4 a0 b0 c0 d0 a b c d : ℕ}
    (h1 : p1.Prime) (h2 : p2.Prime) (h3 : p3.Prime) (h4 : p4.Prime)
    (h12 : p1 < p2) (h23 : p2 < p3) (h34 : p3 < p4)
    (ha : a0 ≤ a) (hb : b0 ≤ b) (hc : c0 ≤ c) (hd : d0 ≤ d) :
    properDivsSum (p1 ^ a0 * p2 ^ b0 * p3 ^ c0 * p4 ^ d0) * (p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) ≤
    properDivsSum (p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) * (p1 ^ a0 * p2 ^ b0 * p3 ^ c0 * p4 ^ d0) := by
  apply properDivsSum_mono_of_sigma_ratio
  rw [sigma_mul_coprime_four h1 h2 h3 h4 h12 h23 h34, sigma_mul_coprime_four h1 h2 h3 h4 h12 h23 h34]
  have m1 := ppSum_mono_exp h1.two_le ha
  have m2 := ppSum_mono_exp h2.two_le hb
  have m3 := ppSum_mono_exp h3.two_le hc
  have m4 := ppSum_mono_exp h4.two_le hd
  have m1234 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul m1 m2) m3) m4
  linarith

lemma properDivsSum_mono_dvd {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) :
    properDivsSum a ≤ properDivsSum b := by
  apply Finset.sum_le_sum_of_subset (f := fun x => x)
  intro x hx
  obtain ⟨hd, hlt⟩ := Nat.mem_properDivisors.mp hx
  exact Nat.mem_properDivisors.mpr ⟨hd.trans hab, lt_of_lt_of_le hlt (Nat.le_of_dvd hb hab)⟩

lemma toFinset_eq_properDivisors_of_sum {u : ℕ} {ds : List ℕ} (hu : 0 < u)
    (hnd : ds.Nodup) (hsub : ∀ d ∈ ds, d ∣ u ∧ d < u)
    (hsum : ds.sum = properDivsSum u) :
    ds.toFinset = u.properDivisors := by
  have hsubF : ds.toFinset ⊆ u.properDivisors := fun d hd =>
    Nat.mem_properDivisors.mpr (hsub d (List.mem_toFinset.mp hd))
  have hsumF : ∑ d ∈ ds.toFinset, d = ∑ d ∈ u.properDivisors, d := by
    have h1 : ∑ d ∈ ds.toFinset, d = ds.sum := by
      generalize ds = l at hnd ⊢
      simpa only [List.map_id'] using List.sum_toFinset (fun x => x) hnd
    rw [h1, hsum]; rfl
  by_contra hne
  have hss : ds.toFinset ⊂ u.properDivisors := lt_of_le_of_ne hsubF hne
  obtain ⟨x, hxU, hxN⟩ := Finset.exists_of_ssubset hss
  have hxpos : 0 < x := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hxU).1 hu
  have hdisj : Disjoint ds.toFinset (u.properDivisors \ ds.toFinset) := Finset.disjoint_sdiff
  have htot : ∑ d ∈ u.properDivisors, d =
      (∑ d ∈ ds.toFinset, d) + ∑ d ∈ u.properDivisors \ ds.toFinset, d := by
    rw [← Finset.sum_union hdisj, Finset.union_sdiff_of_subset hsubF]
  have hge : x ≤ ∑ d ∈ u.properDivisors \ ds.toFinset, d :=
    Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) (Finset.mem_sdiff.mpr ⟨hxU, hxN⟩)
  omega

def checkCoreBadB (B0 L g P0 : ℕ) (bad ds : List ℕ) : Bool :=
  let ivs := ivsOfList ds
  decide (ds.Nodup) &&
  ds.all (fun d => decide (d ∣ B0 ∧ d < B0)) &&
  decide (ds.sum = P0) &&
  ivs.any (fun ab => decide (ab.1 ≤ L ∧ P0 - L ≤ ab.2)) &&
  checkGapsB ivs g &&
  (match ivs.head?, ivs.getLast? with
   | some p, some q => decide (p.1 = 0 ∧ p.1 ≤ p.2 ∧ q.1 ≤ q.2 ∧ q.2 = P0)
   | _, _ => false) &&
  (List.range L).all (fun x => bad.any (fun b => decide (b == x)) || inIvsB ivs x)

lemma core_of_checkCoreBadB {B0 L g P0 : ℕ} {bad ds : List ℕ}
    (hg : 1 ≤ g) (hP : P0 = properDivsSum B0)
    (hchk : checkCoreBadB B0 L g P0 bad ds = true) :
    (∀ y : ℕ, L ≤ y → y ≤ P0 - L → repNat B0.properDivisors y) ∧
    (∀ k : ℕ, k < P0 → ∃ i : ℕ, repNat B0.properDivisors i ∧ k < i + g ∧ i ≤ k) ∧
    (∀ x : ℕ, x < L → x ∉ bad → repNat B0.properDivisors x) := by
  unfold checkCoreBadB at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hnd, hsub⟩, _⟩, ⟨ab, hab, habL, habR⟩⟩, hgaps⟩, hhl⟩, hbad⟩ := hchk
  have hmemT : ∀ d ∈ ds, d ∈ B0.properDivisors := fun d hd =>
    Nat.mem_properDivisors.mpr (hsub d hd)
  have hsound := ivsOfList_sound hnd hmemT
  refine ⟨?_, ?_, ?_⟩
  · intro y hy1 hy2
    exact hsound y ⟨ab, hab, le_trans habL hy1, le_trans hy2 habR⟩
  · intro k hk
    cases hh : (ivsOfList ds).head? with
    | none => simp [hh] at hhl
    | some p =>
      cases hl : (ivsOfList ds).getLast? with
      | none => simp [hh, hl] at hhl
      | some q =>
        simp only [hh, hl, decide_eq_true_eq] at hhl
        have hne : ivsOfList ds ≠ [] := by intro he; simp [he] at hh
        obtain ⟨i, hi, hi1, hi2⟩ := gap_of_checkGapsB hg hgaps hne
          (fun p' hp' => by rw [hh] at hp'; cases hp'; exact ⟨hhl.1, hhl.2.1⟩)
          (fun q' hq' => by rw [hl] at hq'; cases hq'; exact hhl.2.2.1)
          k (fun q' hq' => by rw [hl] at hq'; cases hq'; omega)
        exact ⟨i, hsound i hi, hi1, hi2⟩
  · intro x hx hnot
    rcases hbad x (List.mem_range.mpr hx) with ⟨b, hb, rfl⟩ | hin
    · exact absurd hb hnot
    · exact hsound x (inIvs_of_inIvsB hin)

def checkAbsGapListB (u C P_u : ℕ) (ds : List ℕ) : Bool :=
  decide (ds.Nodup) &&
  ds.all (fun d => decide (d ∣ u ∧ d < u)) &&
  decide (ds.sum = P_u) &&
  ds.all (fun d => decide (d ≤ C + (ds.filter (· < d)).sum))

lemma hasAbsGap_of_list {u C P_u : ℕ} {ds : List ℕ} (hu : 0 < u)
    (hP : P_u = properDivsSum u) (h : checkAbsGapListB u C P_u ds = true) : HasAbsGap u C := by
  unfold checkAbsGapListB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hnd, hsub⟩, hsum⟩, hgap⟩ := h
  have heq : ds.toFinset = u.properDivisors :=
    toFinset_eq_properDivisors_of_sum hu hnd hsub (hsum.trans hP)
  intro d hd
  have hdmem : d ∈ ds := List.mem_toFinset.mp (heq.symm ▸ hd)
  have h1 := hgap d hdmem
  have hfeq : (ds.filter (· < d)).toFinset = u.properDivisors.filter (· < d) := by
    rw [← heq]; ext e; simp
  have hsf : ∑ e ∈ u.properDivisors.filter (· < d), e = (ds.filter (· < d)).sum := by
    rw [← hfeq]
    have hndf := hnd.filter (fun x => decide (x < d))
    generalize ds.filter (fun x => decide (x < d)) = lf at hndf ⊢
    simpa only [List.map_id'] using List.sum_toFinset (fun x => x) hndf
  rw [hsf]
  exact h1

def checkRelGapListB (u a_num a_den P_u : ℕ) (ds : List ℕ) : Bool :=
  decide (ds.Nodup) &&
  ds.all (fun d => decide (d ∣ u ∧ d < u)) &&
  decide (ds.sum = P_u) &&
  ds.all (fun d => decide (a_den * d ≤ a_num * u + a_den * (ds.filter (· < d)).sum))

lemma hasRelGap_of_list {u a_num a_den P_u : ℕ} {ds : List ℕ} (hu : 0 < u)
    (hP : P_u = properDivsSum u) (h : checkRelGapListB u a_num a_den P_u ds = true) :
    HasRelGap u a_num a_den := by
  unfold checkRelGapListB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hnd, hsub⟩, hsum⟩, hgap⟩ := h
  have heq : ds.toFinset = u.properDivisors :=
    toFinset_eq_properDivisors_of_sum hu hnd hsub (hsum.trans hP)
  intro d hd
  have hdmem : d ∈ ds := List.mem_toFinset.mp (heq.symm ▸ hd)
  have h1 := hgap d hdmem
  have hfeq : (ds.filter (· < d)).toFinset = u.properDivisors.filter (· < d) := by
    rw [← heq]; ext e; simp
  have hsf : ∑ e ∈ u.properDivisors.filter (· < d), e = (ds.filter (· < d)).sum := by
    rw [← hfeq]
    have hndf := hnd.filter (fun x => decide (x < d))
    generalize ds.filter (fun x => decide (x < d)) = lf at hndf ⊢
    simpa only [List.map_id'] using List.sum_toFinset (fun x => x) hndf
  rw [hsf]
  exact h1

/-- HasRelGap preservation with one extra divisor ex < u not dividing u. -/
lemma HasRelGap.mul_prime_extra {u p a_num a_den ex : ℕ} (hp : p.Prime) (hu : 0 < u)
    (hrel : HasRelGap u a_num a_den)
    (hex_dvd : ex ∣ p * u) (hex_lt : ex < u) (hex_not : ¬ ex ∣ u)
    (hdef : a_den * u ≤ a_num * (p * u) + a_den * (ex + properDivsSum u)) :
    HasRelGap (p * u) a_num a_den := by
  intro d hd
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
  by_cases hdu : d ∣ u
  · by_cases heq : d = u
    · subst d
      have hsub : insert ex u.properDivisors ⊆ (p * u).properDivisors.filter (· < u) := by
        intro e he
        rw [Finset.mem_filter]
        rcases Finset.mem_insert.mp he with rfl | heu
        · exact ⟨Nat.mem_properDivisors.mpr ⟨hex_dvd, lt_trans hex_lt (by nlinarith [hp.one_lt])⟩, hex_lt⟩
        · obtain ⟨hed, hel⟩ := Nat.mem_properDivisors.mp heu
          exact ⟨Nat.mem_properDivisors.mpr ⟨hed.trans (dvd_mul_left u p), lt_trans hel (by nlinarith [hp.one_lt])⟩, hel⟩
      have hex_notin : ex ∉ u.properDivisors := fun h => hex_not (Nat.mem_properDivisors.mp h).1
      have hle := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
      rw [Finset.sum_insert hex_notin] at hle
      exact le_trans hdef (Nat.add_le_add_left (Nat.mul_le_mul_left a_den hle) _)
    · have hdmem : d ∈ u.properDivisors :=
        Nat.mem_properDivisors.mpr ⟨hdu, lt_of_le_of_ne (Nat.le_of_dvd hu hdu) heq⟩
      have h1 := hrel d hdmem
      have hsub : u.properDivisors.filter (· < d) ⊆ (p * u).properDivisors.filter (· < d) := by
        intro e he
        rw [Finset.mem_filter] at he ⊢
        obtain ⟨hed, hel⟩ := Nat.mem_properDivisors.mp he.1
        exact ⟨Nat.mem_properDivisors.mpr ⟨hed.trans (dvd_mul_left u p), lt_trans hel (by nlinarith [hp.one_lt])⟩, he.2⟩
      have hle := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
      have hup : a_num * u ≤ a_num * (p * u) :=
        Nat.mul_le_mul_left a_num (Nat.le_mul_of_pos_left u hp.pos)
      calc a_den * d ≤ a_num * u + a_den * ∑ e ∈ u.properDivisors.filter (· < d), e := h1
        _ ≤ a_num * (p * u) + a_den * ∑ e ∈ (p * u).properDivisors.filter (· < d), e :=
            Nat.add_le_add hup (Nat.mul_le_mul_left a_den hle)
  · have hpd : p ∣ d := by
      by_contra hnp
      exact hdu ((hp.coprime_iff_not_dvd.mpr hnp).symm.dvd_of_dvd_mul_left hdvd)
    obtain ⟨d', rfl⟩ := hpd
    have hd'dvd : d' ∣ u := (Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd
    have hd'lt : d' < u := lt_of_mul_lt_mul_left hlt (Nat.zero_le p)
    have h1 := hrel d' (Nat.mem_properDivisors.mpr ⟨hd'dvd, hd'lt⟩)
    have hmul : a_den * (p * d') ≤ a_num * (p * u) +
        a_den * (p * ∑ e ∈ u.properDivisors.filter (· < d'), e) := by
      calc a_den * (p * d') = p * (a_den * d') := by ring
        _ ≤ p * (a_num * u + a_den * ∑ e ∈ u.properDivisors.filter (· < d'), e) := Nat.mul_le_mul_left p h1
        _ = a_num * (p * u) + a_den * (p * ∑ e ∈ u.properDivisors.filter (· < d'), e) := by ring
    have hinj : Function.Injective (fun e => p * e) := fun x y h => Nat.eq_of_mul_eq_mul_left hp.pos h
    have himg : (u.properDivisors.filter (· < d')).image (fun e => p * e) ⊆
        (p * u).properDivisors.filter (· < p * d') := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter] at he ⊢
      obtain ⟨hed, hel⟩ := Nat.mem_properDivisors.mp he.1
      exact ⟨Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_left p hed, Nat.mul_lt_mul_of_pos_left hel hp.pos⟩,
        Nat.mul_lt_mul_of_pos_left he.2 hp.pos⟩
    have hsum_img : p * ∑ e ∈ u.properDivisors.filter (· < d'), e =
        ∑ x ∈ (u.properDivisors.filter (· < d')).image (fun e => p * e), x := by
      rw [Finset.sum_image (fun x _ y _ h => hinj h), Finset.mul_sum]
    have hle := Finset.sum_le_sum_of_subset (f := fun x => x) himg
    rw [← hsum_img] at hle
    exact le_trans hmul (Nat.add_le_add_left (Nat.mul_le_mul_left a_den hle) _)

/-- Lift a solid core [L, P(b) - L] and gap g to b * q for a coprime prime q. -/
lemma lift_coprime_prime {b q L g : ℕ} (hb : 0 < b) (hq : q.Prime) (hcop : b.Coprime q)
    (hg : 1 ≤ g) (hL : L ≤ properDivsSum b)
    (hwide : q * g + 2 * L ≤ properDivsSum b + 1)
    (hover : b + 2 * L ≤ properDivsSum b + q * properDivsSum b + 1)
    (hcov : ∀ y, L ≤ y → y ≤ properDivsSum b - L → repNat b.properDivisors y)
    (hgap : ∀ k, k < properDivsSum b → ∃ i, repNat b.properDivisors i ∧ k < i + g ∧ i ≤ k) :
    (∀ y, L ≤ y → y ≤ properDivsSum (b * q) - L → repNat (b * q).properDivisors y) ∧
    (∀ k, k < properDivsSum (b * q) → ∃ i, repNat (b * q).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
  classical
  have hP_bq : properDivsSum (b * q) = b + properDivsSum b + q * properDivsSum b := by
    have hs : sigma 1 (b * q) = sigma 1 b * sigma 1 q := isMultiplicative_sigma.map_mul_of_coprime hcop
    have hsq : sigma 1 q = q + 1 := by simpa [pow_one, ppSum_one hq.two_le] using (ppSum_eq_sigma (a := 1) hq).symm
    have hsb : sigma 1 b = properDivsSum b + b := by
      rw [properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    have hsbq : sigma 1 (b * q) = properDivsSum (b * q) + b * q := by
      rw [properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    rw [hsq, hsb] at hs
    nlinarith
  have hnq : ¬ q ∣ b := hq.coprime_iff_not_dvd.mp hcop.symm
  have hlayers : ∀ i : ℤ, represented b i → ∀ y : ℤ, represented b y →
      represented (b * q) (y + (q : ℤ) * i) ∧ represented (b * q) ((b : ℤ) + y + (q : ℤ) * i) := by
    intro i hi y hy
    obtain ⟨t, ht, rfl⟩ := hi
    obtain ⟨s, hs, rfl⟩ := hy
    have combine {s' : Finset ℕ} (hs' : s' ⊆ b.divisors) :
        represented (b * q) ((∑ d ∈ s', (d : ℤ)) + (q : ℤ) * ∑ d ∈ t, (d : ℤ)) := by
      let f (x : ℕ) := q * x
      have hinj : Function.Injective f := fun x y h => Nat.eq_of_mul_eq_mul_left hq.pos h
      have hsub1 : s' ⊆ (b * q).properDivisors := by
        intro x hx
        have hxd := Nat.dvd_of_mem_divisors (hs' hx)
        exact Nat.mem_properDivisors.mpr ⟨hxd.trans (dvd_mul_right b q),
          lt_of_le_of_lt (Nat.le_of_dvd hb hxd) (by nlinarith [hq.one_lt])⟩
      have hsub2 : t.image f ⊆ (b * q).properDivisors := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨hzd, hzlt⟩ := Nat.mem_properDivisors.mp (ht hz)
        exact Nat.mem_properDivisors.mpr ⟨by rw [mul_comm b q]; exact Nat.mul_dvd_mul_left q hzd,
          by rw [mul_comm b q]; exact Nat.mul_lt_mul_of_pos_left hzlt hq.pos⟩
      have hdisj : Disjoint s' (t.image f) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx2
        exact hnq ((dvd_mul_right q z).trans (Nat.dvd_of_mem_divisors (hs' hx1)))
      refine ⟨s' ∪ t.image f, Finset.union_subset hsub1 hsub2, ?_⟩
      rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ h => hinj h), Finset.mul_sum]
      simp [f]
    have hbne : b ≠ 0 := hb.ne'
    have hfull : insert b s ⊆ b.divisors := by
      rw [← Nat.insert_self_properDivisors hbne]
      exact Finset.insert_subset_insert b hs
    have hnb : b ∉ s := fun h => Nat.self_notMem_properDivisors (hs h)
    refine ⟨combine (hs.trans Nat.properDivisors_subset_divisors), ?_⟩
    simpa [Finset.sum_insert hnb, add_assoc] using combine hfull
  have hcov_res : ∀ y, L ≤ y → y ≤ properDivsSum (b * q) - L → repNat (b * q).properDivisors y := by
    intro y hy1 hy2
    have hP_cast : properTotal b = (properDivsSum b : ℤ) := by simp [properTotal, properDivsSum]
    have hmid := middle_next (A := fun i => represented b i) (B := fun z => represented b z)
      (C := fun z => represented (b * q) z) (T := (properDivsSum b : ℤ))
      (P := (properDivsSum b : ℤ)) (b := (b : ℤ)) (L := (L : ℤ)) (g := (g : ℤ)) (r := (q : ℤ))
      (by exact_mod_cast hq.pos)
      (by have h : (q : ℤ) * (g : ℤ) + 2 * (L : ℤ) ≤ (properDivsSum b : ℤ) + 1 := (by exact_mod_cast hwide); omega)
      (by have h : (b : ℤ) + 2 * (L : ℤ) ≤ (properDivsSum b : ℤ) + (q : ℤ) * (properDivsSum b : ℤ) + 1 := (by exact_mod_cast hover); omega)
      ⟨b.properDivisors, subset_rfl, by simp [properDivsSum]⟩
      (fun k hk0 hkt => by
        lift k to ℕ using hk0
        obtain ⟨i, hi, hi1, hi2⟩ := hgap k (by exact_mod_cast hkt)
        exact ⟨(i : ℤ), repNat_to_represented hi, by omega, by omega⟩)
      (fun z hz1 hz2 => by
        lift z to ℕ using (by omega)
        exact repNat_to_represented (hcov z (by exact_mod_cast hz1) (by omega)))
      hlayers (y : ℤ) (by exact_mod_cast hy1) (by rw [hP_bq] at hy2; omega)
    obtain ⟨s, hs, hsum⟩ := hmid
    refine ⟨s, hs, ?_⟩
    rw [← Nat.cast_sum] at hsum
    exact_mod_cast hsum
  have hsub_b : b.properDivisors ⊆ (b * q).properDivisors := by
    intro x hx
    obtain ⟨hd, hlt⟩ := Nat.mem_properDivisors.mp hx
    exact Nat.mem_properDivisors.mpr ⟨hd.trans (dvd_mul_right b q), lt_of_lt_of_le hlt (Nat.le_mul_of_pos_right b hq.pos)⟩
  exact ⟨hcov_res, repNat_union_gap hg hsub_b hL hcov_res hgap⟩

/-- Variant of lift_prime_step placing n immediately after r^(a+1)*1 (for 315 * p4^d). -/
lemma lift_prime_step_n_second {u r a L g : ℕ} (hr : r.Prime) (hu : 1 < u) (ha : 1 ≤ a)
    (hcop : ¬ r ∣ u) (hg : 1 ≤ g)
    (hL : L ≤ properDivsSum (r ^ a * u))
    (hcov : ∀ y, L ≤ y → y ≤ properDivsSum (r ^ a * u) - L → repNat (r ^ a * u).properDivisors y)
    (hgap : ∀ k, k < properDivsSum (r ^ a * u) → ∃ i, repNat (r ^ a * u).properDivisors i ∧ k < i + g ∧ i ≤ k)
    (hstep_1 : 2 * L + r ^ (a + 1) ≤ properDivsSum (r ^ a * u) + 1)
    (hstep_n : 2 * L + r ^ a * u ≤ properDivsSum (r ^ a * u) + r ^ (a + 1) + 1)
    (hstep_d : ∀ d ∈ u.properDivisors, 1 < d →
      2 * L + r ^ (a + 1) * d ≤
        properDivsSum (r ^ a * u) + r ^ a * u +
        r ^ (a + 1) * (∑ e ∈ u.properDivisors.filter (· < d), e) + 1) :
    (∀ y, L ≤ y → y ≤ properDivsSum (r ^ (a + 1) * u) - L → repNat (r ^ (a + 1) * u).properDivisors y) ∧
    (∀ k, k < properDivsSum (r ^ (a + 1) * u) → ∃ i, repNat (r ^ (a + 1) * u).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
  classical
  let n := r ^ a * u
  let n' := r ^ (a + 1) * u
  have hu0 : 0 < u := by omega
  have hn_pos : 0 < n := by have := hr.pos; positivity
  let rest_u := u.properDivisors.erase 1
  let ds := rest_u.sort (· ≤ ·)
  let xs := r ^ (a + 1) :: n :: ds.map (fun d => r ^ (a + 1) * d)
  have h1mem : 1 ∈ u.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hu
  have hds_nd : ds.Nodup := Finset.sort_nodup _ _
  have hds_sorted : ds.Pairwise (· < ·) :=
    ((Finset.pairwise_sort rest_u (· ≤ ·)).and (List.nodup_iff_pairwise_ne.mp hds_nd)).imp
      (fun h => lt_of_le_of_ne h.1 h.2)
  have hmap_mul : ∀ l : List ℕ, (l.map (fun d => r ^ (a + 1) * d)).sum = r ^ (a + 1) * l.sum := by
    intro l; induction l with
    | nil => simp
    | cons hd tl ih => simp [ih, mul_add]
  have hinj_r : Function.Injective (fun d => r ^ (a + 1) * d) :=
    fun x y h => Nat.eq_of_mul_eq_mul_left (pow_pos hr.pos _) h
  have hnot_ra1_n : ¬ r ^ (a + 1) ∣ n := by
    intro h
    rw [pow_succ] at h
    exact hcop ((Nat.mul_dvd_mul_iff_left (pow_pos hr.pos a)).mp h)
  have hxs_nd : xs.Nodup := by
    rw [List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, hds_nd.map hinj_r⟩
    · intro h
      rcases List.mem_cons.mp h with hEq | hmap
      · exact hnot_ra1_n (by rw [← hEq])
      · obtain ⟨d, hd, hEq⟩ := List.mem_map.mp hmap
        have hd1 : d ≠ 1 := (Finset.mem_erase.mp ((Finset.mem_sort (· ≤ ·)).mp hd)).1
        have : d = 1 := hinj_r (by simpa using hEq)
        exact hd1 this
    · intro hmap
      obtain ⟨d, _, hEq⟩ := List.mem_map.mp hmap
      exact hnot_ra1_n ⟨d, hEq.symm⟩
  have hdisj : ∀ x ∈ xs, x ∉ n.properDivisors := by
    intro x hx hmem
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hmem
    rcases List.mem_cons.mp hx with rfl | h2
    · exact hnot_ra1_n hdvd
    · rcases List.mem_cons.mp h2 with rfl | hmap
      · omega
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hmap
        exact hnot_ra1_n ((dvd_mul_right _ d).trans hdvd)
  have hUnion : n.properDivisors ∪ xs.toFinset = n'.properDivisors := by
    ext x
    simp only [Finset.mem_union, List.mem_toFinset, xs, List.mem_cons, List.mem_map,
      ds, Finset.mem_sort, rest_u, Finset.mem_erase, Nat.mem_properDivisors]
    constructor
    · rintro (⟨h1, h2⟩ | rfl | rfl | ⟨d, ⟨_, hd1, hd2⟩, rfl⟩)
      · exact ⟨h1.trans (Nat.mul_dvd_mul_right (pow_dvd_pow r (Nat.le_succ a)) u),
          lt_of_lt_of_le h2 (Nat.mul_le_mul_right u (pow_le_pow_right₀ hr.one_lt.le (Nat.le_succ a)))⟩
      · exact ⟨dvd_mul_right _ u, by simpa using Nat.mul_lt_mul_of_pos_left hu (pow_pos hr.pos (a + 1))⟩
      · exact ⟨Nat.mul_dvd_mul_right (pow_dvd_pow r (Nat.le_succ a)) u,
          Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hr.one_lt (Nat.lt_succ_self a)) hu0⟩
      · exact ⟨Nat.mul_dvd_mul_left _ hd1, Nat.mul_lt_mul_of_pos_left hd2 (pow_pos hr.pos _)⟩
    · rintro ⟨hx1, hx2⟩
      by_cases hdiv : r ^ (a + 1) ∣ x
      · obtain ⟨d, rfl⟩ := hdiv
        have hd1 : d ∣ u := (Nat.mul_dvd_mul_iff_left (pow_pos hr.pos _)).mp hx1
        have hd2 : d < u := lt_of_mul_lt_mul_left hx2 (Nat.zero_le _)
        by_cases hdeq : d = 1
        · right; left; simp [hdeq]
        · right; right; right; exact ⟨d, ⟨hdeq, hd1, hd2⟩, rfl⟩
      · have hx_dvd_n : x ∣ n := by
          have hx0 : x ≠ 0 := fun h => by subst h; exact hdiv (dvd_zero _)
          have hfx : x.factorization r ≤ a := by
            by_contra! hgt; exact hdiv ((hr.pow_dvd_iff_le_factorization hx0).mpr hgt)
          have h1 : r ^ x.factorization r ∣ r ^ a := pow_dvd_pow r hfx
          have h2 : x / r ^ x.factorization r ∣ u := by
            have hd' : x / r ^ x.factorization r ∣ r ^ (a + 1) * u := (Nat.ordCompl_dvd x r).trans hx1
            exact ((hr.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hr hx0)).pow_left _).symm.dvd_of_dvd_mul_left hd'
          rw [← Nat.ordProj_mul_ordCompl_eq_self x r]
          exact Nat.mul_dvd_mul h1 h2
        by_cases hxn : x = n
        · right; right; left; exact hxn
        · left; exact ⟨hx_dvd_n, lt_of_le_of_ne (Nat.le_of_dvd hn_pos hx_dvd_n) hxn⟩
  have hP_eq : properDivsSum n' = properDivsSum n + xs.sum := by
    rw [properDivsSum, ← hUnion, Finset.sum_union (by
      rw [Finset.disjoint_left]; intro x hx1 hx2; exact hdisj x (List.mem_toFinset.mp hx2) hx1)]
    congr 1
    generalize xs = l at hxs_nd ⊢
    simpa only [List.map_id'] using List.sum_toFinset (fun x => x) hxs_nd
  have hsteps : ∀ (pre : List ℕ) (x : ℕ) (suf : List ℕ),
      xs = pre ++ x :: suf → L + x ≤ (properDivsSum n - L) + pre.sum + 1 := by
    intro pre x suf heq
    cases pre with
    | nil =>
      simp only [xs, List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, _⟩ := heq
      simp only [List.sum_nil, add_zero]
      dsimp only [n]; omega
    | cons a1 pre1 =>
      simp only [xs, List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq1⟩ := heq
      cases pre1 with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq1
        obtain ⟨rfl, _⟩ := heq1
        simp only [List.sum_cons, List.sum_nil, add_zero]
        dsimp only [n]; omega
      | cons a2 pre2 =>
        simp only [List.cons_append, List.cons.injEq] at heq1
        obtain ⟨rfl, heq2⟩ := heq1
        have hlen : pre2.length < ds.length := by
          have := congrArg List.length heq2
          simp only [List.length_map, List.length_append, List.length_cons] at this
          omega
        let pre_d := ds.take pre2.length
        have hpre2_eq : pre2 = pre_d.map (fun d => r ^ (a + 1) * d) := by
          have := congrArg (List.take pre2.length) heq2.symm
          simpa [pre_d, List.map_take] using this
        have hx_eq : x = r ^ (a + 1) * ds[pre2.length] := by
          have hget := congrArg (fun l => l[pre2.length]?) heq2.symm
          simp only [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero,
            List.getElem?_map, List.getElem?_eq_getElem hlen, Option.map_some, Option.some.injEq] at hget
          exact hget
        let d := ds[pre2.length]
        have hd_rest : d ∈ rest_u := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hlen)
        have hd_ne1 : d ≠ 1 := (Finset.mem_erase.mp hd_rest).1
        have hd_mem : d ∈ u.properDivisors := (Finset.mem_erase.mp hd_rest).2
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hd_mem).1 hu0
        have hd_gt1 : 1 < d := by omega
        have hpre_sub : (u.properDivisors.filter (· < d)).erase 1 ⊆ pre_d.toFinset := by
          intro e he
          rw [Finset.mem_erase, Finset.mem_filter] at he
          have he_rest : e ∈ rest_u := Finset.mem_erase.mpr ⟨he.1, he.2.1⟩
          have he_ds : e ∈ ds := (Finset.mem_sort (· ≤ ·)).mpr he_rest
          obtain ⟨idx, hidx, hget_e⟩ := List.getElem_of_mem he_ds
          have hidx_lt : idx < pre2.length := by
            by_contra! hge
            rcases eq_or_lt_of_le hge with rfl | hgt
            · omega
            · have := List.pairwise_iff_getElem.mp hds_sorted pre2.length idx hlen hidx hgt
              omega
          rw [List.mem_toFinset]
          have : ds[idx] ∈ ds.take pre2.length := by
            rw [List.mem_iff_getElem]
            exact ⟨idx, by simp; omega, by simp [List.getElem_take]⟩
          simpa [pre_d, hget_e] using this
        have h1_in_filt : 1 ∈ u.properDivisors.filter (· < d) :=
          Finset.mem_filter.mpr ⟨h1mem, hd_gt1⟩
        have hfilt_sum : ∑ e ∈ u.properDivisors.filter (· < d), e =
            1 + ∑ e ∈ (u.properDivisors.filter (· < d)).erase 1, e := by
          rw [← Finset.add_sum_erase _ _ h1_in_filt]
        have hpre_d_sum : ∑ e ∈ (u.properDivisors.filter (· < d)).erase 1, e ≤ pre_d.sum := by
          have htf : ∑ e ∈ pre_d.toFinset, e = pre_d.sum := by
            have hnd_t : pre_d.Nodup := hds_nd.sublist (List.take_sublist pre2.length ds)
            generalize pre_d = lp at hnd_t ⊢
            simpa only [List.map_id'] using List.sum_toFinset (fun x => x) hnd_t
          rw [← htf]
          exact Finset.sum_le_sum_of_subset (f := fun x => x) hpre_sub
        have hsum_pre : (r ^ (a + 1) :: n :: pre2).sum =
            r ^ (a + 1) + n + r ^ (a + 1) * pre_d.sum := by
          simp only [List.sum_cons, hpre2_eq, hmap_mul]; ring
        have hs := hstep_d d hd_mem hd_gt1
        have hmul_le : r ^ (a + 1) * (∑ e ∈ u.properDivisors.filter (· < d), e) ≤
            r ^ (a + 1) + r ^ (a + 1) * pre_d.sum := by
          rw [hfilt_sum, mul_add, mul_one]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hpre_d_sum) _
        rw [hx_eq, hsum_pre]
        change L + r ^ (a + 1) * d ≤ properDivsSum n - L + (r ^ (a + 1) + n + r ^ (a + 1) * pre_d.sum) + 1
        dsimp only [n] at *; omega
  have hcov' := repNat_append_list_interval xs hxs_nd hdisj hcov hsteps
  rw [hUnion] at hcov'
  have hcov_final : ∀ y, L ≤ y → y ≤ properDivsSum n' - L → repNat n'.properDivisors y := by
    intro y hy1 hy2
    exact hcov' y hy1 (by dsimp only [n, n'] at *; omega)
  have hsub_n : n.properDivisors ⊆ n'.properDivisors := by
    rw [← hUnion]; exact Finset.subset_union_left
  exact ⟨hcov_final, repNat_union_gap hg hsub_n hL hcov_final hgap⟩

end CoreLiftExtra

section VStateEngine

structure VState where
  p : ℕ
  l : ℕ
  pl : ℕ
  sl : ℕ
  h : Option ℕ
  un : ℕ
  ud : ℕ
  st : ℕ

def mkV (p l : ℕ) (h : Option ℕ) (st : ℕ) : VState :=
  ⟨p, l, p ^ l, ppSum p l, h, hiNum p h, hiDen p h, st⟩

def mkV1 : VState := ⟨1, 0, 1, 1, some 0, 1, 1, 1⟩

def fixV (v : VState) : VState :=
  { v with h := some v.l, un := v.sl, ud := v.pl }

def stepV (v : VState) : VState :=
  if v.st == 2 then
    let p2 := v.p * v.p
    { v with l := v.l + 2, pl := v.pl * p2, sl := v.sl * p2 + v.p + 1 }
  else
    { v with l := v.l + 1, pl := v.pl * v.p, sl := v.sl * v.p + 1 }

def canSplit (v : VState) : Bool :=
  match v.h with | none => true | some k => decide (v.l < k)

def pickV (v1 v2 v3 v4 : VState) : Nat :=
  let k1 := if canSplit v1 then v1.pl * v1.p else 10^30
  let k2 := if canSplit v2 then v2.pl * v2.p else 10^30
  let k3 := if canSplit v3 then v3.pl * v3.p else 10^30
  let k4 := if canSplit v4 then v4.pl * v4.p else 10^30
  if k1 ≤ k2 && k1 ≤ k3 && k1 ≤ k4 then 0
  else if k2 ≤ k3 && k2 ≤ k4 then 1
  else if k3 ≤ k4 then 2
  else 3

def VValid (v : VState) (e : ℕ) : Prop :=
  (v.p = 1 ∧ v.l = 0 ∧ v.pl = 1 ∧ v.sl = 1 ∧ v.h = some 0 ∧ v.un = 1 ∧ v.ud = 1 ∧ e = 0) ∨
  (v.p.Prime ∧ v.l ≤ e ∧ leOpt e v.h ∧ v.pl = v.p ^ v.l ∧ v.sl = ppSum v.p v.l ∧
    v.un = hiNum v.p v.h ∧ v.ud = hiDen v.p v.h ∧
    (v.st = 1 ∨ (v.st = 2 ∧ v.l % 2 = 0 ∧ e % 2 = 0)))

def vSigma (v : VState) (e : ℕ) : ℕ :=
  if v.p = 1 then 1 else ppSum v.p e

lemma VValid.mk {p l e : ℕ} {h : Option ℕ} {st : ℕ}
    (hp : p.Prime) (hle : l ≤ e) (ho : leOpt e h)
    (hst : st = 1 ∨ (st = 2 ∧ l % 2 = 0 ∧ e % 2 = 0)) :
    VValid (mkV p l h st) e :=
  Or.inr ⟨hp, hle, ho, rfl, rfl, rfl, rfl, hst⟩

lemma VValid.mk1 : VValid mkV1 0 :=
  Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma VValid.pl_le_pow {v : VState} {e : ℕ} (hv : VValid v e) : v.pl ≤ v.p ^ e := by
  rcases hv with ⟨hp, _, hpl, _, _, _, _, he⟩ | ⟨hp, hle, _, hpl, _, _, _, _⟩
  · simp [hp, hpl, he]
  · rw [hpl]; exact pow_le_pow_right₀ hp.one_lt.le hle

lemma VValid.pl_dvd_pow {v : VState} {e : ℕ} (hv : VValid v e) : v.pl ∣ v.p ^ e := by
  rcases hv with ⟨hp, _, hpl, _, _, _, _, he⟩ | ⟨hp, hle, _, hpl, _, _, _, _⟩
  · simp [hp, hpl, he]
  · rw [hpl]; exact pow_dvd_pow v.p hle

lemma VValid.pl_pos {v : VState} {e : ℕ} (hv : VValid v e) : 0 < v.pl := by
  rcases hv with ⟨_, _, hpl, _, _, _, _, _⟩ | ⟨hp, _, _, hpl, _, _, _, _⟩
  · omega
  · rw [hpl]; exact pow_pos hp.pos _

lemma VValid.pow_pos {v : VState} {e : ℕ} (hv : VValid v e) : 0 < v.p ^ e := by
  rcases hv with ⟨hp, _, _, _, _, _, _, he⟩ | ⟨hp, _, _, _, _, _, _, _⟩
  · simp [hp, he]
  · exact Nat.pow_pos hp.pos

lemma VValid.ud_pos {v : VState} {e : ℕ} (hv : VValid v e) : 0 < v.ud := by
  rcases hv with ⟨_, _, _, _, _, _, hud, _⟩ | ⟨hp, _, _, _, _, _, hud, _⟩
  · omega
  · rw [hud]; cases v.h with
    | none => dsimp [hiDen]; have := hp.two_le; omega
    | some k => dsimp [hiDen]; exact Nat.pow_pos hp.pos

lemma VValid.lo_ratio {v : VState} {e : ℕ} (hv : VValid v e) :
    v.sl * v.p ^ e ≤ vSigma v e * v.pl := by
  rcases hv with ⟨hp, _, hpl, hsl, _, _, _, he⟩ | ⟨hp, hle, _, hpl, hsl, _, _, _⟩
  · simp [vSigma, hp, hpl, hsl, he]
  · have hne : v.p ≠ 1 := hp.ne_one
    simp only [vSigma, hne, ↓reduceIte, hpl, hsl]
    exact ppSum_mono_exp hp.two_le hle

lemma VValid.hi_ratio {v : VState} {e : ℕ} (hv : VValid v e) :
    vSigma v e * v.ud ≤ v.un * v.p ^ e := by
  rcases hv with ⟨hp, _, _, _, _, hun, hud, he⟩ | ⟨hp, _, ho, _, _, hun, hud, _⟩
  · simp [vSigma, hp, hun, hud, he]
  · have hne : v.p ≠ 1 := hp.ne_one
    simp only [vSigma, hne, ↓reduceIte, hun, hud]
    exact ppSum_le_hi hp.two_le ho

lemma VValid.hi_ratio_strict {v : VState} {e : ℕ} (hv : VValid v e) (hnone : v.h = none) :
    vSigma v e * v.ud < v.un * v.p ^ e := by
  rcases hv with ⟨_, _, _, _, hh, _, _, _⟩ | ⟨hp, _, _, _, _, hun, hud, _⟩
  · rw [hnone] at hh; cases hh
  · have hne : v.p ≠ 1 := hp.ne_one
    simp only [vSigma, hne, ↓reduceIte, hun, hud, hnone, hiNum, hiDen]
    exact ppSum_lt_lim hp.two_le

lemma VValid.eq_of_not_canSplit {v : VState} {e : ℕ} (hv : VValid v e) (hc : canSplit v = false) :
    e = v.l ∧ v.p ^ e = v.pl ∧ vSigma v e = v.sl := by
  rcases hv with ⟨hp, hl, hpl, hsl, _, _, _, he⟩ | ⟨hp, hle, ho, hpl, hsl, _, _, _⟩
  · simp [vSigma, hp, hl, hpl, hsl, he]
  · unfold canSplit at hc
    cases hh : v.h with
    | none => simp [hh] at hc
    | some k =>
      simp only [hh, decide_eq_false_iff_not, not_lt] at hc
      rw [hh] at ho
      have heq : e = v.l := by change e ≤ k at ho; omega
      have hne : v.p ≠ 1 := hp.ne_one
      exact ⟨heq, by rw [heq, hpl], by simp [vSigma, hne, heq, hsl]⟩

lemma VValid.split {v : VState} {e : ℕ} (hv : VValid v e) :
    VValid (fixV v) e ∨ VValid (stepV v) e := by
  rcases hv with ⟨hp, hl, hpl, hsl, hh, hun, hud, he⟩ | ⟨hp, hle, ho, hpl, hsl, hun, hud, hst⟩
  · left; exact Or.inl ⟨hp, hl, hpl, hsl, by simp [fixV, hl], by simp [fixV, hsl], by simp [fixV, hpl], he⟩
  · by_cases heq : e = v.l
    · left; unfold VValid; right; dsimp only [fixV]
      exact ⟨hp, by omega, by simp [leOpt, heq], hpl, hsl, by simp [hiNum, hsl], by simp [hiDen, hpl], hst⟩
    · right; unfold VValid; right
      rcases hst with h1 | ⟨h2, hl2, he2⟩
      · have hne2 : (v.st == 2) = false := by simp [h1]
        dsimp only [stepV]; simp only [hne2, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hp, by omega, ho, by rw [hpl, pow_succ], by rw [hsl, ppSum_succ hp.two_le], hun, hud, Or.inl h1⟩
      · have heq2 : (v.st == 2) = true := by simp [h2]
        dsimp only [stepV]; simp only [heq2, ↓reduceIte]
        exact ⟨hp, by omega, ho, by rw [hpl]; ring, by rw [hsl, ppSum_add_two hp.two_le], hun, hud, Or.inr ⟨h2, by omega, he2⟩⟩

lemma fixV_p (v : VState) : (fixV v).p = v.p := rfl
lemma stepV_p (v : VState) : (stepV v).p = v.p := by unfold stepV; split_ifs <;> rfl
lemma vSigma_fixV (v : VState) (e : ℕ) : vSigma (fixV v) e = vSigma v e := rfl
lemma vSigma_stepV (v : VState) (e : ℕ) : vSigma (stepV v) e = vSigma v e := by simp [vSigma, stepV_p]

end VStateEngine

section DGe2

lemma two_le_deficiency_of_even_sigma {B : ℕ} (hdef : sigma 1 B < 2 * B) (heven : 2 ∣ sigma 1 B) :
    2 ≤ 2 * B - sigma 1 B := by
  obtain ⟨k, hk⟩ := heven; omega

lemma two_le_deficiency_of_inf_lt_two {p1 p2 p3 p4 a b c d : ℕ}
    (h1 : p1.Prime) (h2 : p2.Prime) (h3 : p3.Prime) (h4 : p4.Prime)
    (h12 : p1 < p2) (h23 : p2 < p3) (h34 : p3 < p4)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hinf : p1 * p2 * p3 * p4 < 2 * ((p1 - 1) * (p2 - 1) * (p3 - 1) * (p4 - 1))) :
    2 ≤ 2 * (p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) - sigma 1 (p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) := by
  let B := p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d
  let ud := (p1 - 1) * (p2 - 1) * (p3 - 1) * (p4 - 1)
  have hsB : sigma 1 B = ppSum p1 a * ppSum p2 b * ppSum p3 c * ppSum p4 d :=
    sigma_mul_coprime_four h1 h2 h3 h4 h12 h23 h34
  have l1 := ppSum_lt_lim (a := a) h1.two_le
  have l2 := ppSum_lt_lim (a := b) h2.two_le
  have l3 := ppSum_lt_lim (a := c) h3.two_le
  have l4 := ppSum_lt_lim (a := d) h4.two_le
  have hmul : sigma 1 B * ud < (p1 * p2 * p3 * p4) * B := by
    rw [hsB]
    have m12 := Nat.mul_lt_mul_of_lt_of_lt l1 l2
    have m34 := Nat.mul_lt_mul_of_lt_of_lt l3 l4
    have m1234 := Nat.mul_lt_mul_of_lt_of_lt m12 m34
    dsimp only [B, ud]; linarith
  have hB_gt : ud < B := by
    have h1' : p1 - 1 < p1 ^ a := lt_of_lt_of_le (by have := h1.two_le; omega) (Nat.le_self_pow (by omega) p1)
    have h2' : p2 - 1 < p2 ^ b := lt_of_lt_of_le (by have := h2.two_le; omega) (Nat.le_self_pow (by omega) p2)
    have h3' : p3 - 1 < p3 ^ c := lt_of_lt_of_le (by have := h3.two_le; omega) (Nat.le_self_pow (by omega) p3)
    have h4' : p4 - 1 < p4 ^ d := lt_of_lt_of_le (by have := h4.two_le; omega) (Nat.le_self_pow (by omega) p4)
    have m12 := Nat.mul_lt_mul_of_lt_of_lt h1' h2'
    have m34 := Nat.mul_lt_mul_of_lt_of_lt h3' h4'
    have m1234 := Nat.mul_lt_mul_of_lt_of_lt m12 m34
    dsimp only [B, ud]; linarith
  have hud_pos : 0 < ud := by
    have hp1 : 0 < p1 - 1 := by have := h1.two_le; omega
    have hp2 : 0 < p2 - 1 := by have := h2.two_le; omega
    have hp3 : 0 < p3 - 1 := by have := h3.two_le; omega
    have hp4 : 0 < p4 - 1 := by have := h4.two_le; omega
    dsimp only [ud]; positivity
  change p1 * p2 * p3 * p4 < 2 * ud at hinf
  have hdiff : ud < (2 * B - sigma 1 B) * ud := by
    have h2B : sigma 1 B < 2 * B := by
      have h1' : (p1 * p2 * p3 * p4) * B ≤ (2 * ud) * B := Nat.mul_le_mul_right B hinf.le
      have : sigma 1 B * ud < 2 * B * ud := by linarith
      exact Nat.lt_of_mul_lt_mul_right this
    have : (2 * B - sigma 1 B) * ud = 2 * B * ud - sigma 1 B * ud := Nat.sub_mul _ _ _
    rw [this]
    have hgap : 1 ≤ 2 * ud - p1 * p2 * p3 * p4 := by omega
    have hmulB : (2 * ud - p1 * p2 * p3 * p4) * B = 2 * B * ud - (p1 * p2 * p3 * p4) * B := by
      rw [Nat.sub_mul]; ring_nf
    have hB_le : B ≤ 2 * B * ud - (p1 * p2 * p3 * p4) * B := by
      rw [← hmulB]; exact le_trans (by omega) (Nat.mul_le_mul_right B hgap)
    omega
  by_contra! hlt
  have : (2 * B - sigma 1 B) * ud ≤ ud := by nlinarith
  omega

def checkDge2 : ℕ → VState → VState → VState → VState → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, v1, v2, v3, v4 =>
    let ln := v1.sl * v2.sl * v3.sl * v4.sl
    let ld := v1.pl * v2.pl * v3.pl * v4.pl
    if 2 * ld ≤ ln then true
    else
      let un := v1.un * v2.un * v3.un * v4.un
      let ud := v1.ud * v2.ud * v3.ud * v4.ud
      let hasInf := v1.h.isNone || v2.h.isNone || v3.h.isNone || v4.h.isNone
      if un < 2 * ud && ((hasInf && ud ≤ ld * (2 * ud - un)) || 2 * ud ≤ ld * (2 * ud - un)) then
        true
      else if !(canSplit v1 || canSplit v2 || canSplit v3 || canSplit v4) then
        false
      else
        match pickV v1 v2 v3 v4 with
        | 0 => checkDge2 fuel (fixV v1) v2 v3 v4 && checkDge2 fuel (stepV v1) v2 v3 v4
        | 1 => checkDge2 fuel v1 (fixV v2) v3 v4 && checkDge2 fuel v1 (stepV v2) v3 v4
        | 2 => checkDge2 fuel v1 v2 (fixV v3) v4 && checkDge2 fuel v1 v2 (stepV v3) v4
        | _ => checkDge2 fuel v1 v2 v3 (fixV v4) && checkDge2 fuel v1 v2 v3 (stepV v4)

lemma checkDge2_sound {fuel : ℕ} {v1 v2 v3 v4 : VState} {a b c d : ℕ}
    (h1 : VValid v1 a) (h2 : VValid v2 b) (h3 : VValid v3 c) (h4 : VValid v4 d)
    (hdef : vSigma v1 a * vSigma v2 b * vSigma v3 c * vSigma v4 d <
      2 * (v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d))
    (hchk : checkDge2 fuel v1 v2 v3 v4 = true) :
    2 ≤ 2 * (v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d) -
      vSigma v1 a * vSigma v2 b * vSigma v3 c * vSigma v4 d := by
  induction fuel generalizing v1 v2 v3 v4 with
  | zero => simp [checkDge2] at hchk
  | succ f ih =>
    unfold checkDge2 at hchk
    dsimp only at hchk
    let B := v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d
    let sB := vSigma v1 a * vSigma v2 b * vSigma v3 c * vSigma v4 d
    let ln := v1.sl * v2.sl * v3.sl * v4.sl
    let ld := v1.pl * v2.pl * v3.pl * v4.pl
    let un := v1.un * v2.un * v3.un * v4.un
    let ud := v1.ud * v2.ud * v3.ud * v4.ud
    have hlo : ln * B ≤ sB * ld := by
      have m := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1.lo_ratio h2.lo_ratio) h3.lo_ratio) h4.lo_ratio
      dsimp only [ln, ld, B, sB]; linarith
    have hld_le_B : ld ≤ B := by
      have m := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1.pl_le_pow h2.pl_le_pow) h3.pl_le_pow) h4.pl_le_pow
      dsimp only [ld, B]; exact m
    have hld_pos : 0 < ld := by
      have := h1.pl_pos; have := h2.pl_pos; have := h3.pl_pos; have := h4.pl_pos
      dsimp only [ld]; positivity
    have hud_pos : 0 < ud := by
      have := h1.ud_pos; have := h2.ud_pos; have := h3.ud_pos; have := h4.ud_pos
      dsimp only [ud]; positivity
    have hhi : sB * ud ≤ un * B := by
      have m := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1.hi_ratio h2.hi_ratio) h3.hi_ratio) h4.hi_ratio
      dsimp only [un, ud, B, sB]; linarith
    by_cases hln : 2 * ld ≤ ln
    · exfalso
      have : 2 * ld * B ≤ ln * B := Nat.mul_le_mul_right B hln
      have : 2 * B ≤ sB := Nat.le_of_mul_le_mul_right (by linarith) hld_pos
      change sB < 2 * B at hdef; omega
    · change (if 2 * ld ≤ ln then true else _) = true at hchk
      rw [if_neg hln] at hchk
      by_cases hok : (decide (un < 2 * ud) && (((v1.h.isNone || v2.h.isNone || v3.h.isNone || v4.h.isNone) && decide (ud ≤ ld * (2 * ud - un))) || decide (2 * ud ≤ ld * (2 * ud - un)))) = true
      · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
        obtain ⟨hlt_un, hcond⟩ := hok
        have hsub_eq : (2 * B - sB) * ud = 2 * B * ud - sB * ud := Nat.sub_mul _ _ _
        rcases hcond with ⟨hinf, hge1⟩ | hge2
        · have hhi_lt : sB * ud < un * B := by
            have p1 := h1.hi_ratio; have p2 := h2.hi_ratio; have p3 := h3.hi_ratio; have p4 := h4.hi_ratio
            have hsig_pos : ∀ v e, VValid v e → 0 < vSigma v e * v.ud := by
              intro v e hv
              have hu := hv.ud_pos
              rcases hv with ⟨hp, _, _, _, _, _, _, _⟩ | ⟨hp, _, _, _, _, _, _, _⟩
              · simp [vSigma, hp]; exact hu
              · have : 0 < vSigma v e := by simp [vSigma, hp.ne_one, ppSum_pos hp.two_le]
                positivity
            simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at hinf
            rcases hinf with ((h1n | h2n) | h3n) | h4n
            · have s1 := h1.hi_ratio_strict h1n
              have m2 := Nat.mul_le_mul (Nat.mul_le_mul p2 p3) p4
              have mp : 0 < vSigma v2 b * v2.ud * (vSigma v3 c * v3.ud) * (vSigma v4 d * v4.ud) := by
                have := hsig_pos v2 b h2; have := hsig_pos v3 c h3; have := hsig_pos v4 d h4; positivity
              have m := Nat.mul_lt_mul_of_lt_of_le' s1 m2 mp
              have hL : (vSigma v1 a * v1.ud) * ((vSigma v2 b * v2.ud) * (vSigma v3 c * v3.ud) * (vSigma v4 d * v4.ud)) = sB * ud := by dsimp [sB, ud]; ring
              have hR : (v1.un * v1.p ^ a) * ((v2.un * v2.p ^ b) * (v3.un * v3.p ^ c) * (v4.un * v4.p ^ d)) = un * B := by dsimp [un, B]; ring
              linarith
            · have s2 := h2.hi_ratio_strict h2n
              have m2 := Nat.mul_le_mul (Nat.mul_le_mul p1 p3) p4
              have mp : 0 < vSigma v1 a * v1.ud * (vSigma v3 c * v3.ud) * (vSigma v4 d * v4.ud) := by
                have := hsig_pos v1 a h1; have := hsig_pos v3 c h3; have := hsig_pos v4 d h4; positivity
              have m := Nat.mul_lt_mul_of_lt_of_le' s2 m2 mp
              have hL : (vSigma v2 b * v2.ud) * ((vSigma v1 a * v1.ud) * (vSigma v3 c * v3.ud) * (vSigma v4 d * v4.ud)) = sB * ud := by dsimp [sB, ud]; ring
              have hR : (v2.un * v2.p ^ b) * ((v1.un * v1.p ^ a) * (v3.un * v3.p ^ c) * (v4.un * v4.p ^ d)) = un * B := by dsimp [un, B]; ring
              linarith
            · have s3 := h3.hi_ratio_strict h3n
              have m2 := Nat.mul_le_mul (Nat.mul_le_mul p1 p2) p4
              have mp : 0 < vSigma v1 a * v1.ud * (vSigma v2 b * v2.ud) * (vSigma v4 d * v4.ud) := by
                have := hsig_pos v1 a h1; have := hsig_pos v2 b h2; have := hsig_pos v4 d h4; positivity
              have m := Nat.mul_lt_mul_of_lt_of_le' s3 m2 mp
              have hL : (vSigma v3 c * v3.ud) * ((vSigma v1 a * v1.ud) * (vSigma v2 b * v2.ud) * (vSigma v4 d * v4.ud)) = sB * ud := by dsimp [sB, ud]; ring
              have hR : (v3.un * v3.p ^ c) * ((v1.un * v1.p ^ a) * (v2.un * v2.p ^ b) * (v4.un * v4.p ^ d)) = un * B := by dsimp [un, B]; ring
              linarith
            · have s4 := h4.hi_ratio_strict h4n
              have m2 := Nat.mul_le_mul (Nat.mul_le_mul p1 p2) p3
              have mp : 0 < vSigma v1 a * v1.ud * (vSigma v2 b * v2.ud) * (vSigma v3 c * v3.ud) := by
                have := hsig_pos v1 a h1; have := hsig_pos v2 b h2; have := hsig_pos v3 c h3; positivity
              have m := Nat.mul_lt_mul_of_lt_of_le' s4 m2 mp
              have hL : (vSigma v4 d * v4.ud) * ((vSigma v1 a * v1.ud) * (vSigma v2 b * v2.ud) * (vSigma v3 c * v3.ud)) = sB * ud := by dsimp [sB, ud]; ring
              have hR : (v4.un * v4.p ^ d) * ((v1.un * v1.p ^ a) * (v2.un * v2.p ^ b) * (v3.un * v3.p ^ c)) = un * B := by dsimp [un, B]; ring
              linarith
          have hgt : ud < (2 * B - sB) * ud := by
            rw [hsub_eq]
            have : ud ≤ B * (2 * ud - un) := le_trans hge1 (Nat.mul_le_mul_right _ hld_le_B)
            have : B * (2 * ud - un) = 2 * B * ud - un * B := by rw [Nat.mul_sub]; ring_nf
            omega
          by_contra! hbad
          have : (2 * B - sB) * ud ≤ 1 * ud := Nat.mul_le_mul_right ud (by omega)
          omega
        · have hge : 2 * ud ≤ (2 * B - sB) * ud := by
            rw [hsub_eq]
            have : 2 * ud ≤ B * (2 * ud - un) := le_trans hge2 (Nat.mul_le_mul_right _ hld_le_B)
            have : B * (2 * ud - un) = 2 * B * ud - un * B := by rw [Nat.mul_sub]; ring_nf
            omega
          exact Nat.le_of_mul_le_mul_right hge hud_pos
      · change (if (decide (un < 2 * ud) && (((v1.h.isNone || v2.h.isNone || v3.h.isNone || v4.h.isNone) && decide (ud ≤ ld * (2 * ud - un))) || decide (2 * ud ≤ ld * (2 * ud - un)))) = true then true else _) = true at hchk
        rw [if_neg hok] at hchk
        by_cases hns : (!(canSplit v1 || canSplit v2 || canSplit v3 || canSplit v4)) = true
        · rw [if_pos hns] at hchk; cases hchk
        · rw [if_neg hns] at hchk
          split at hchk
          · simp only [Bool.and_eq_true] at hchk
            rcases h1.split with h1a | h1b
            · simpa only [fixV_p, vSigma_fixV] using ih h1a h2 h3 h4 (by simpa only [fixV_p, vSigma_fixV] using hdef) hchk.1
            · simpa only [stepV_p, vSigma_stepV] using ih h1b h2 h3 h4 (by simpa only [stepV_p, vSigma_stepV] using hdef) hchk.2
          · simp only [Bool.and_eq_true] at hchk
            rcases h2.split with h2a | h2b
            · simpa only [fixV_p, vSigma_fixV] using ih h1 h2a h3 h4 (by simpa only [fixV_p, vSigma_fixV] using hdef) hchk.1
            · simpa only [stepV_p, vSigma_stepV] using ih h1 h2b h3 h4 (by simpa only [stepV_p, vSigma_stepV] using hdef) hchk.2
          · simp only [Bool.and_eq_true] at hchk
            rcases h3.split with h3a | h3b
            · simpa only [fixV_p, vSigma_fixV] using ih h1 h2 h3a h4 (by simpa only [fixV_p, vSigma_fixV] using hdef) hchk.1
            · simpa only [stepV_p, vSigma_stepV] using ih h1 h2 h3b h4 (by simpa only [stepV_p, vSigma_stepV] using hdef) hchk.2
          · simp only [Bool.and_eq_true] at hchk
            rcases h4.split with h4a | h4b
            · simpa only [fixV_p, vSigma_fixV] using ih h1 h2 h3 h4a (by simpa only [fixV_p, vSigma_fixV] using hdef) hchk.1
            · simpa only [stepV_p, vSigma_stepV] using ih h1 h2 h3 h4b (by simpa only [stepV_p, vSigma_stepV] using hdef) hchk.2

end DGe2

section CheckBox

def isSmallComp (n : ℕ) : Bool :=
  n > 31 && (n % 2 == 0 || n % 3 == 0 || n % 5 == 0 || n % 7 == 0 ||
    n % 11 == 0 || n % 13 == 0 || n % 17 == 0 || n % 19 == 0 ||
    n % 23 == 0 || n % 29 == 0 || n % 31 == 0)

lemma not_prime_of_isSmallComp {n : ℕ} (h : isSmallComp n = true) : ¬ n.Prime := by
  unfold isSmallComp at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  intro hp
  have hgt := h.1
  have hdiv : ∀ d : ℕ, 1 < d → d < n → n % d = 0 → False := fun d hd1 hd2 hmod => by
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with rfl | rfl <;> omega
  rcases h.2 with (((((((((hm | hm) | hm) | hm) | hm) | hm) | hm) | hm) | hm) | hm) | hm
  · exact hdiv 2 (by decide) (by omega) hm
  · exact hdiv 3 (by decide) (by omega) hm
  · exact hdiv 5 (by decide) (by omega) hm
  · exact hdiv 7 (by decide) (by omega) hm
  · exact hdiv 11 (by decide) (by omega) hm
  · exact hdiv 13 (by decide) (by omega) hm
  · exact hdiv 17 (by decide) (by omega) hm
  · exact hdiv 19 (by decide) (by omega) hm
  · exact hdiv 23 (by decide) (by omega) hm
  · exact hdiv 29 (by decide) (by omega) hm
  · exact hdiv 31 (by decide) (by omega) hm

def hasDivGo : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, n, d =>
    if d * d > n then false
    else if n % d == 0 then true
    else hasDivGo fuel n (d + 2)

lemma not_prime_of_hasDivGo {fuel n d : ℕ} (hd : 1 < d) (h : hasDivGo fuel n d = true) : ¬ n.Prime := by
  induction fuel generalizing d with
  | zero => simp [hasDivGo] at h
  | succ f ih =>
    unfold hasDivGo at h
    by_cases hsq : d * d > n
    · rw [if_pos hsq] at h; cases h
    · rw [if_neg hsq] at h
      by_cases hmod : (n % d == 0) = true
      · intro hp
        have hdn : d ∣ n := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hmod)
        have hlt : d < n := by nlinarith
        rcases hp.eq_one_or_self_of_dvd d hdn with rfl | rfl <;> omega
      · rw [if_neg hmod] at h; exact ih (by omega) h

def isComp (n : ℕ) : Bool :=
  if n < 4 then false
  else if n % 2 == 0 then true
  else if n % 3 == 0 then n > 3
  else hasDivGo 500 n 5

lemma not_prime_of_isComp {n : ℕ} (h : isComp n = true) : ¬ n.Prime := by
  unfold isComp at h
  by_cases h4 : n < 4
  · rw [if_pos h4] at h; cases h
  · rw [if_neg h4] at h
    by_cases h2 : (n % 2 == 0) = true
    · intro hp
      rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h2)) with h1 | h2' <;> omega
    · rw [if_neg h2] at h
      by_cases h3 : (n % 3 == 0) = true
      · intro hp
        rcases hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h3)) with h1 | h2' <;> omega
      · rw [if_neg h3] at h; exact not_prime_of_hasDivGo (by decide) h

def peelTop : ℕ → ℕ → ℕ → ℕ
  | 0, _, q1 => q1
  | fuel + 1, q0, q1 =>
    if q1 < q0 then q1
    else if isSmallComp q1 then peelTop fuel q0 (q1 - 1)
    else q1

lemma peelTop_sound {fuel q0 q1 q : ℕ} (hq : q.Prime) (hqle : q ≤ q1) :
    q ≤ peelTop fuel q0 q1 := by
  induction fuel generalizing q1 with
  | zero => exact hqle
  | succ f ih =>
    unfold peelTop
    split_ifs with h1 h2
    · exact hqle
    · have hne : q ≠ q1 := fun heq => not_prime_of_isSmallComp h2 (heq ▸ hq)
      exact ih (by omega)
    · exact hqle

def isBad (bad : List ℕ) (x : ℕ) : Bool := bad.any (fun b => decide (b == x))

lemma not_mem_of_isBad_false {bad : List ℕ} {x : ℕ} (h : isBad bad x = false) : x ∉ bad := by
  intro hm
  have ht : isBad bad x = true := by
    unfold isBad; rw [List.any_eq_true]; exact ⟨x, hm, by simp⟩
  rw [ht] at h; cases h

def findEmin : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ × ℕ)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, bn, bd, q, qpow, sQ, e =>
    if bn * sQ > 2 * bd * qpow then some (e, qpow, sQ)
    else findEmin fuel bn bd q (qpow * q) (sQ + qpow * q) (e + 1)

lemma findEmin_sound {fuel bn bd q qpow sQ e e0 qpow0 sQ0 : ℕ}
    (hq : 2 ≤ q) (hqpow : qpow = q ^ e) (hsQ : sQ = ppSum q e)
    (h : findEmin fuel bn bd q qpow sQ e = some (e0, qpow0, sQ0)) :
    e ≤ e0 ∧ qpow0 = q ^ e0 ∧ sQ0 = ppSum q e0 ∧
    bn * ppSum q e0 > 2 * bd * q ^ e0 ∧
    ∀ k, e ≤ k → k < e0 → bn * ppSum q k ≤ 2 * bd * q ^ k := by
  induction fuel generalizing qpow sQ e with
  | zero => simp [findEmin] at h
  | succ f ih =>
    unfold findEmin at h
    split_ifs at h with hgt
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨le_rfl, hqpow, hsQ, ?_, fun k hk1 hk2 => by omega⟩
      rw [← hqpow, ← hsQ]; exact hgt
    · have hnext_p : qpow * q = q ^ (e + 1) := by rw [hqpow, pow_succ]
      have hnext_s : sQ + qpow * q = ppSum q (e + 1) := by
        rw [hsQ, hqpow]
        have hp1 : 0 < q - 1 := by omega
        apply Nat.eq_of_mul_eq_mul_right hp1
        rw [ppSum_mul_sub hq, add_mul, ppSum_mul_sub hq]
        have h1 : 1 ≤ q ^ (e + 1) := Nat.one_le_pow _ _ (by omega)
        have h2 : 1 ≤ q ^ (e + 2) := Nat.one_le_pow _ _ (by omega)
        zify [h1, h2, (show 1 ≤ q by omega)]
        ring
      obtain ⟨hle, hp0, hs0, hgt0, hprev⟩ := ih hnext_p hnext_s h
      refine ⟨by omega, hp0, hs0, hgt0, fun k hk1 hk2 => ?_⟩
      by_cases hke : k = e
      · subst k; rw [← hqpow, ← hsQ]; omega
      · exact hprev k (by omega) hk2

def checkRangeE1 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Bool → Bool
  | 0, _, _, _, _, _, _, _ => true
  | fuel + 1, sB, D, L, qhi, cur, bad, kill3 =>
    if cur > qhi then true
    else
      let E := sB - D * cur
      let ok := decide (E == 0 ∨ L ≤ E) || (kill3 && decide (E % 3 == 0 ∨ cur % 3 == 2)) || !(isBad bad E) || isComp cur
      ok && checkRangeE1 fuel sB D L qhi (cur + 1) bad kill3

lemma checkRangeE1_sound {fuel sB D L qhi cur q : ℕ} {bad : List ℕ} {kill3 : Bool}
    (hfuel : qhi + 1 ≤ cur + fuel) (hq : q.Prime) (hlo : cur ≤ q) (hhi : q ≤ qhi)
    (hEpos : 0 < sB - D * q)
    (hchk : checkRangeE1 fuel sB D L qhi cur bad kill3 = true) :
    L ≤ sB - D * q ∨ (kill3 = true ∧ ((sB - D * q) % 3 = 0 ∨ q % 3 = 2)) ∨ (sB - D * q) ∉ bad := by
  induction fuel generalizing cur with
  | zero => omega
  | succ f ih =>
    unfold checkRangeE1 at hchk
    split_ifs at hchk with hgt
    · omega
    · simp only [Bool.and_eq_true] at hchk
      by_cases hqcur : q = cur
      · subst q
        have h1 := hchk.1
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
          Bool.not_eq_true'] at h1
        rcases h1 with (((hE0 | hEL) | ⟨hk3, hmod⟩) | hnb) | hcomp
        · omega
        · left; exact hEL
        · right; left; exact ⟨hk3, hmod⟩
        · right; right; exact not_mem_of_isBad_false hnb
        · exact absurd hq (not_prime_of_isComp hcomp)
      · exact ih (by omega) (by omega) hchk.2

def isOutOpt (x : ℕ) : Option ℕ → Bool
  | some k => decide (k < x)
  | none => false

lemma isOutOpt_false_of_leOpt {x y : ℕ} {o : Option ℕ} (hxy : x ≤ y) (ho : leOpt y o) : isOutOpt x o = false := by
  cases o with
  | none => rfl
  | some k => simp only [isOutOpt, decide_eq_false_iff_not]; change y ≤ k at ho; omega

def isLtOpt (x : ℕ) : Option ℕ → Bool
  | some k => decide (k < x)
  | none => false

def checkLeafB (B sB q0 : ℕ) (q1 : Option ℕ) (L : ℕ) (bad : List ℕ) (kill3 onlyE1 : Bool) : Bool :=
  if 2 * B ≤ sB then true
  else
    let D := 2 * B - sB
    let rem := sB % D
    let ok1 :=
      if decide (L ≤ rem) || decide (rem == 0 ∧ L ≤ D) then true
      else
        let qhi := match q1 with | some k => min k ((sB - 1) / D) | none => (sB - 1) / D
        let qlo := max q0 (if sB > L then (sB - L) / D + 1 else 0)
        if qlo > qhi then true
        else checkRangeE1 (qhi - qlo + 1) sB D L qhi qlo bad kill3
    if !ok1 then false
    else if onlyE1 then true
    else if rem == 0 then true
    else
      let q2 := sB / D + 1
      let q2Out := decide (q2 < q0) || isOutOpt q2 q1
      if q2Out then true
      else
        match findEmin 25 sB B q2 (q2 * q2) (1 + q2 + q2 * q2) 2 with
        | none => isComp q2
        | some (e, qpow, sQ) =>
          let E := sB * sQ - 2 * B * qpow
          decide (L ≤ E) || (kill3 && decide (E % 3 == 0 ∨ (q2 % 3 == 2 ∧ e % 2 == 1))) || !(isBad bad E) || isComp q2

lemma checkLeafB_sound {B sB q0 L q e : ℕ} {q1 : Option ℕ} {bad : List ℕ} {kill3 onlyE1 : Bool}
    (hBpos : 0 < B) (hq : q.Prime) (hq0 : q0 ≤ q) (hq1 : leOpt q q1) (he : 1 ≤ e)
    (hBdef : sB < 2 * B)
    (hab : 2 * (B * q ^ e) < sB * ppSum q e)
    (hprev : ∀ k, k < e → sB * ppSum q k < 2 * (B * q ^ k))
    (honly : onlyE1 = true → e = 1)
    (hchk : checkLeafB B sB q0 q1 L bad kill3 onlyE1 = true) :
    let E := sB * ppSum q e - 2 * (B * q ^ e)
    L ≤ E ∨ (kill3 = true ∧ (E % 3 = 0 ∨ (q % 3 = 2 ∧ e % 2 = 1))) ∨ E ∉ bad := by
  intro E
  unfold checkLeafB at hchk
  have hnotle : ¬ (2 * B ≤ sB) := by omega
  simp only [hnotle, ↓reduceIte] at hchk
  let D := 2 * B - sB
  have hDpos : 0 < D := by dsimp [D]; omega
  let qhi := match q1 with | some k => min k ((sB - 1) / D) | none => (sB - 1) / D
  let qlo := max q0 (if sB > L then (sB - L) / D + 1 else 0)
  let ok1b :=
    if decide (L ≤ sB % D) || decide ((sB % D == 0) ∧ L ≤ D) then true
    else if qlo > qhi then true
    else checkRangeE1 (qhi - qlo + 1) sB D L qhi qlo bad kill3
  have hok1_t : ok1b = true := by
    by_contra hf
    have hf' : ok1b = false := by cases h : ok1b <;> [rfl; exact absurd h hf]
    change (if !ok1b then false else _) = true at hchk
    simp [hf'] at hchk
  by_cases he1 : e = 1
  · subst he1
    have hE_eq : E = sB - D * q := by
      dsimp only [E, D]; rw [pow_one, ppSum_one hq.two_le]
      have h1 : sB * (q + 1) = sB * q + sB := by ring
      have h2 : 2 * (B * q) = sB * q + (2 * B - sB) * q := by
        have hmul : 2 * (B * q) = 2 * B * q := by ring
        rw [hmul, Nat.sub_mul]; have : sB * q ≤ 2 * B * q := Nat.mul_le_mul_right q (by omega); omega
      omega
    have hEpos : 0 < sB - D * q := by rw [← hE_eq]; dsimp only [E]; omega
    have hqle_div1 : q ≤ (sB - 1) / D := by
      have : D * q ≤ sB - 1 := by omega
      exact (Nat.le_div_iff_mul_le hDpos).mpr (by rw [mul_comm]; exact this)
    have hqle_hi : q ≤ qhi := by
      dsimp only [qhi]; cases q1 with
      | none => exact hqle_div1
      | some k => exact le_min hq1 hqle_div1
    dsimp only [ok1b] at hok1_t
    split_ifs at hok1_t with hrem hqempty
    · simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hrem
      left; rw [hE_eq]
      have hdiv := Nat.div_add_mod sB D
      have hqle_div : q ≤ sB / D := by
        by_contra! hgt
        have : D * (sB / D + 1) ≤ D * q := Nat.mul_le_mul_left D hgt
        have : sB < D * (sB / D + 1) := by have := Nat.mod_lt sB hDpos; nlinarith
        omega
      rcases hrem with h1 | ⟨h0, hD⟩
      · have : D * q ≤ D * (sB / D) := Nat.mul_le_mul_left D hqle_div
        omega
      · have hlt_div : q < sB / D := by
          by_contra! hge
          have heq : q = sB / D := by omega
          rw [h0, add_zero] at hdiv; rw [heq] at hEpos; omega
        have : D * q + D ≤ D * (sB / D) := by have : q + 1 ≤ sB / D := (by omega); nlinarith
        omega
    · by_cases hEL : L ≤ E
      · left; exact hEL
      · exfalso
        have hqge_lo : qlo ≤ q := by
          dsimp only [qlo]; apply max_le hq0
          split_ifs with hsL
          · by_contra! hlt
            have hle : q ≤ (sB - L) / D := by omega
            have : D * q ≤ sB - L := by
              have := Nat.mul_le_mul_left D hle
              have := Nat.div_mul_le_self (sB - L) D
              linarith
            omega
          · omega
        omega
    · by_cases hEL : L ≤ E
      · left; exact hEL
      · have hqge_lo : qlo ≤ q := by
          dsimp only [qlo]; apply max_le hq0
          split_ifs with hsL
          · by_contra! hlt
            have hle : q ≤ (sB - L) / D := by omega
            have : D * q ≤ sB - L := by
              have := Nat.mul_le_mul_left D hle
              have := Nat.div_mul_le_self (sB - L) D
              linarith
            omega
          · omega
        have hres := checkRangeE1_sound (by omega) hq hqge_lo hqle_hi hEpos hok1_t
        rw [hE_eq]
        rcases hres with h1 | ⟨hk, h2 | h3⟩ | h4
        · left; exact h1
        · right; left; exact ⟨hk, Or.inl h2⟩
        · right; left; exact ⟨hk, Or.inr ⟨h3, rfl⟩⟩
        · right; right; exact h4
  · -- e >= 2
    have he2 : 2 ≤ e := by omega
    have honly_f : onlyE1 = false := by
      cases ho : onlyE1
      · rfl
      · exact absurd (honly ho) he1
    have h1def : sB * (q + 1) < 2 * (B * q) := by
      simpa [pow_one, ppSum_one hq.two_le] using hprev 1 (by omega)
    have hinf_ab : 2 * B * (q - 1) < sB * q := by
      have hlim := ppSum_lt_lim (a := e) hq.two_le
      have h1 : 2 * (B * q ^ e) * (q - 1) < sB * ppSum q e * (q - 1) :=
        Nat.mul_lt_mul_of_pos_right hab (by have := hq.two_le; omega)
      have h2 : sB * ppSum q e * (q - 1) ≤ sB * (q * q ^ e) := by
        have := Nat.mul_le_mul_left sB hlim.le; linarith
      have h3 : (2 * B * (q - 1)) * q ^ e < (sB * q) * q ^ e := by linarith
      exact Nat.lt_of_mul_lt_mul_right h3
    have hDq_gt : sB < D * q := by
      have : sB * q + sB < 2 * B * q := by linarith
      have : 2 * B * q = sB * q + D * q := by dsimp [D]; rw [Nat.sub_mul]; omega
      omega
    have hDq1_lt : D * (q - 1) < sB := by
      have : 2 * B * (q - 1) = sB * (q - 1) + D * (q - 1) := by
        dsimp [D]; rw [Nat.sub_mul]
        have : sB * (q - 1) ≤ 2 * B * (q - 1) := Nat.mul_le_mul_right _ (by omega); omega
      have hq1_pos : 1 ≤ q := hq.pos
      have : sB * q = sB * (q - 1) + sB := by zify [hq1_pos]; ring
      omega
    have hdiv_eq : sB / D = q - 1 := by
      have hdiv := Nat.div_add_mod sB D
      have hlt := Nat.mod_lt sB hDpos
      have hle1 : q - 1 ≤ sB / D := by
        by_contra! h; have : sB / D + 1 ≤ q - 1 := by omega
        have : D * (sB / D + 1) ≤ D * (q - 1) := Nat.mul_le_mul_left D this
        nlinarith
      have hle2 : sB / D < q := by
        by_contra! h; have : D * q ≤ D * (sB / D) := Nat.mul_le_mul_left D h
        omega
      omega
    have hrem_ne : sB % D ≠ 0 := by
      intro h0
      have hdiv := Nat.div_add_mod sB D
      rw [hdiv_eq, h0, add_zero] at hdiv
      omega
    have hq2_eq : sB / D + 1 = q := by rw [hdiv_eq]; have := hq.pos; omega
    have hrem_b : (sB % D == 0) = false := beq_false_of_ne hrem_ne
    have hnot_out : (decide (sB / D + 1 < q0) || isOutOpt (sB / D + 1) q1) = false := by
      rw [hq2_eq, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨by omega, isOutOpt_false_of_leOpt le_rfl hq1⟩
    change (if !ok1b then false
      else if onlyE1 then true
      else if (sB % D == 0) then true
      else if (decide (sB / D + 1 < q0) || isOutOpt (sB / D + 1) q1) then true
      else
        match findEmin 25 sB B (sB / D + 1) ((sB / D + 1) * (sB / D + 1)) (1 + (sB / D + 1) + (sB / D + 1) * (sB / D + 1)) 2 with
        | none => isComp (sB / D + 1)
        | some (e, qpow, sQ) =>
          let E := sB * sQ - 2 * B * qpow
          decide (L ≤ E) || (kill3 && decide (E % 3 == 0 ∨ ((sB / D + 1) % 3 == 2 ∧ e % 2 == 1))) || !(isBad bad E) || isComp (sB / D + 1)) = true at hchk
    simp only [hok1_t, Bool.not_true, Bool.false_eq_true, ↓reduceIte, honly_f, hrem_b, hnot_out] at hchk
    rw [hq2_eq] at hchk
    cases hf : findEmin 25 sB B q (q * q) (1 + q + q * q) 2 with
    | none =>
      rw [hf] at hchk
      exact absurd hq (not_prime_of_isComp hchk)
    | some triple =>
      rcases triple with ⟨e0, qpow0, sQ0⟩
      rw [hf] at hchk
      have hq2p : q * q = q ^ 2 := by ring
      have hsQ2 : 1 + q + q * q = ppSum q 2 := by
        rw [ppSum_add_two hq.two_le, ppSum_zero hq.two_le]; ring
      obtain ⟨he0_ge2, rfl, rfl, hgt0, hprev0⟩ := findEmin_sound hq.two_le hq2p hsQ2 hf
      have he_eq : e = e0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := hprev0 e he2 hlt; linarith
        · have := hprev e0 hgt; linarith
      subst he_eq
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        Bool.not_eq_true'] at hchk
      have hE_eq' : sB * ppSum q e - 2 * B * q ^ e = E := by dsimp [E]; ring_nf
      rw [hE_eq'] at hchk
      rcases hchk with ((h1 | ⟨hk, h2⟩) | h3) | hcomp
      · left; exact h1
      · right; left; exact ⟨hk, h2⟩
      · right; right; exact not_mem_of_isBad_false h3
      · exact absurd hq (not_prime_of_isComp hcomp)

def clampOpt (un ud : ℕ) (q1 : Option ℕ) : Option ℕ :=
  if un < 2 * ud then
    let bnd := (2 * ud - 1) / (2 * ud - un)
    match q1 with | some k => some (min k bnd) | none => some bnd
  else q1

def peelOpt (q0 : ℕ) : Option ℕ → Option ℕ
  | some k => some (peelTop 60 q0 k)
  | none => none

lemma peelOpt_leOpt {q q0 : ℕ} {o : Option ℕ} (hq : q.Prime) (ho : leOpt q o) : leOpt q (peelOpt q0 o) := by
  cases o with
  | none => trivial
  | some k => exact peelTop_sound hq ho

def checkBox : ℕ → VState → VState → VState → VState → ℕ → Option ℕ → ℕ → List ℕ → Bool → Bool
  | 0, _, _, _, _, _, _, _, _, _ => false
  | fuel + 1, v1, v2, v3, v4, q0, q1, L, bad, kill3 =>
    if isOutOpt q0 q1 then true
    else
      let un := v1.un * v2.un * v3.un * v4.un
      let ud := v1.ud * v2.ud * v3.ud * v4.ud
      if 2 ≤ q0 && decide (un * q0 ≤ 2 * ud * (q0 - 1)) then true
      else
        let ln := v1.sl * v2.sl * v3.sl * v4.sl
        let ld := v1.pl * v2.pl * v3.pl * v4.pl
        if ln ≥ 2 * ld then true
        else
          let q1'' := peelOpt q0 (clampOpt un ud q1)
          if isOutOpt q0 q1'' then true
          else if !(canSplit v1 || canSplit v2 || canSplit v3 || canSplit v4) then
            checkLeafB ld ln q0 q1'' L bad kill3 false
          else
            match q1'' with
            | none =>
              match pickV v1 v2 v3 v4 with
              | 0 => checkBox fuel (fixV v1) v2 v3 v4 q0 none L bad kill3 && checkBox fuel (stepV v1) v2 v3 v4 q0 none L bad kill3
              | 1 => checkBox fuel v1 (fixV v2) v3 v4 q0 none L bad kill3 && checkBox fuel v1 (stepV v2) v3 v4 q0 none L bad kill3
              | 2 => checkBox fuel v1 v2 (fixV v3) v4 q0 none L bad kill3 && checkBox fuel v1 v2 (stepV v3) v4 q0 none L bad kill3
              | _ => checkBox fuel v1 v2 v3 (fixV v4) q0 none L bad kill3 && checkBox fuel v1 v2 v3 (stepV v4) q0 none L bad kill3
            | some k =>
              if ln * (k + 1) > 2 * ld * k then
                checkLeafB ld ln q0 (some k) L bad kill3 true
              else if q0 == k then
                match findEmin 25 un ud q0 q0 (1 + q0) 1 with
                | none => false
                | some (e, qpow, sQ) =>
                  if ln * sQ > 2 * ld * qpow then
                    let E := ln * sQ - 2 * ld * qpow
                    decide (L ≤ E) || (kill3 && decide (E % 3 == 0 ∨ (q0 % 3 == 2 ∧ e % 2 == 1))) || !(isBad bad E)
                  else
                    match pickV v1 v2 v3 v4 with
                    | 0 => checkBox fuel (fixV v1) v2 v3 v4 q0 (some k) L bad kill3 && checkBox fuel (stepV v1) v2 v3 v4 q0 (some k) L bad kill3
                    | 1 => checkBox fuel v1 (fixV v2) v3 v4 q0 (some k) L bad kill3 && checkBox fuel v1 (stepV v2) v3 v4 q0 (some k) L bad kill3
                    | 2 => checkBox fuel v1 v2 (fixV v3) v4 q0 (some k) L bad kill3 && checkBox fuel v1 v2 (stepV v3) v4 q0 (some k) L bad kill3
                    | _ => checkBox fuel v1 v2 v3 (fixV v4) q0 (some k) L bad kill3 && checkBox fuel v1 v2 v3 (stepV v4) q0 (some k) L bad kill3
              else if q0 < k && decide (un * (k + 1) ≤ 2 * ud * k) then
                checkBox fuel v1 v2 v3 v4 q0 (some (k - 1)) L bad kill3 &&
                (isComp k || checkBox fuel v1 v2 v3 v4 k (some k) L bad kill3)
              else
                match pickV v1 v2 v3 v4 with
                | 0 => checkBox fuel (fixV v1) v2 v3 v4 q0 (some k) L bad kill3 && checkBox fuel (stepV v1) v2 v3 v4 q0 (some k) L bad kill3
                | 1 => checkBox fuel v1 (fixV v2) v3 v4 q0 (some k) L bad kill3 && checkBox fuel v1 (stepV v2) v3 v4 q0 (some k) L bad kill3
                | 2 => checkBox fuel v1 v2 (fixV v3) v4 q0 (some k) L bad kill3 && checkBox fuel v1 v2 (stepV v3) v4 q0 (some k) L bad kill3
                | _ => checkBox fuel v1 v2 v3 (fixV v4) q0 (some k) L bad kill3 && checkBox fuel v1 v2 v3 (stepV v4) q0 (some k) L bad kill3

set_option maxHeartbeats 1600000 in
lemma checkBox_sound {fuel : ℕ} {v1 v2 v3 v4 : VState} {a b c d q0 L q e : ℕ}
    {q1 : Option ℕ} {bad : List ℕ} {kill3 : Bool}
    (h1 : VValid v1 a) (h2 : VValid v2 b) (h3 : VValid v3 c) (h4 : VValid v4 d)
    (hq : q.Prime) (hq0 : q0 ≤ q) (hq1 : leOpt q q1) (he : 1 ≤ e)
    (hB_sig : sigma 1 (v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d) =
      vSigma v1 a * vSigma v2 b * vSigma v3 c * vSigma v4 d)
    (hBlo_sig : ∀ u1 u2 u3 u4 : VState, VValid u1 a → VValid u2 b → VValid u3 c → VValid u4 d →
      u1.p = v1.p → u2.p = v2.p → u3.p = v3.p → u4.p = v4.p →
      sigma 1 (u1.pl * u2.pl * u3.pl * u4.pl) = u1.sl * u2.sl * u3.sl * u4.sl)
    (hcop : (v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d).Coprime q)
    (hab : (v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d * q ^ e).properDivisors, x.Deficient)
    (hchk : checkBox fuel v1 v2 v3 v4 q0 q1 L bad kill3 = true) :
    let m := v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d * q ^ e
    let E := sigma 1 m - 2 * m
    L ≤ E ∨ (kill3 = true ∧ (E % 3 = 0 ∨ (q % 3 = 2 ∧ e % 2 = 1))) ∨ E ∉ bad := by
  induction fuel generalizing v1 v2 v3 v4 q0 q1 with
  | zero => simp [checkBox] at hchk
  | succ f ih =>
    intro m E
    let B := v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d
    let sB := vSigma v1 a * vSigma v2 b * vSigma v3 c * vSigma v4 d
    have hBpos : 0 < B := by
      have := h1.pow_pos; have := h2.pow_pos; have := h3.pow_pos; have := h4.pow_pos
      dsimp only [B]; positivity
    have hmpos : 0 < m := by have := hq.pos; dsimp only [m]; positivity
    have hsm : sigma 1 m = sB * ppSum q e := by
      dsimp only [m]
      rw [isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right e), hB_sig, ← ppSum_eq_sigma hq]
    have hab_nat : 2 * (B * q ^ e) < sB * ppSum q e := by
      rw [← hsm]; exact (abund_iff_nat hmpos).mp hab
    have hBdef : sB < 2 * B := by
      have hmem : B ∈ m.properDivisors := Nat.mem_properDivisors.mpr
        ⟨dvd_mul_right B (q ^ e), by
          dsimp only [m, B]
          simpa using Nat.mul_lt_mul_of_pos_left (one_lt_pow₀ hq.one_lt (by omega)) hBpos⟩
      dsimp only [sB, B]; rw [← hB_sig]; exact (defic_iff_nat hBpos).mp (hprim B hmem)
    have hprev_q : ∀ k, k < e → sB * ppSum q k < 2 * (B * q ^ k) := by
      intro k hk
      have hmem : B * q ^ k ∈ m.properDivisors := Nat.mem_properDivisors.mpr
        ⟨Nat.mul_dvd_mul_left B (pow_dvd_pow q hk.le),
         Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hq.one_lt hk) hBpos⟩
      have hd := (defic_iff_nat (by have := hq.pos; positivity)).mp (hprim _ hmem)
      rw [isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right k), hB_sig, ← ppSum_eq_sigma hq] at hd
      exact hd
    let un := v1.un * v2.un * v3.un * v4.un
    let ud := v1.ud * v2.ud * v3.ud * v4.ud
    let ln := v1.sl * v2.sl * v3.sl * v4.sl
    let ld := v1.pl * v2.pl * v3.pl * v4.pl
    have hhi : sB * ud ≤ un * B := by
      have m1 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1.hi_ratio h2.hi_ratio) h3.hi_ratio) h4.hi_ratio
      dsimp only [sB, ud, un, B]; linarith
    have hlo : ln * B ≤ sB * ld := by
      have m1 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1.lo_ratio h2.lo_ratio) h3.lo_ratio) h4.lo_ratio
      dsimp only [ln, ld, sB, B]; linarith
    have hld_pos : 0 < ld := by
      have := h1.pl_pos; have := h2.pl_pos; have := h3.pl_pos; have := h4.pl_pos
      dsimp only [ld]; positivity
    have hud_pos : 0 < ud := by
      have := h1.ud_pos; have := h2.ud_pos; have := h3.ud_pos; have := h4.ud_pos
      dsimp only [ud]; positivity
    have hld_dvd_B : ld ∣ B :=
      Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul h1.pl_dvd_pow h2.pl_dvd_pow) h3.pl_dvd_pow) h4.pl_dvd_pow
    have hld_sig : sigma 1 ld = ln := hBlo_sig v1 v2 v3 v4 h1 h2 h3 h4 rfl rfl rfl rfl
    have hcop_ld : ld.Coprime q := hcop.coprime_dvd_left hld_dvd_B
    have hab_lim : 2 * ud * (q - 1) < un * q := by
      have hqlim := ppSum_lt_lim (a := e) hq.two_le
      have hq1p : 0 < q - 1 := by have := hq.two_le; omega
      have hstep1 : 2 * (B * q ^ e) * (ud * (q - 1)) < sB * ppSum q e * (ud * (q - 1)) :=
        Nat.mul_lt_mul_of_pos_right hab_nat (by positivity)
      have hstep2 : sB * ppSum q e * (ud * (q - 1)) ≤ (un * B) * (q * q ^ e) := by
        have := Nat.mul_le_mul hhi hqlim.le; linarith
      have hstep3 : (2 * ud * (q - 1)) * (B * q ^ e) < (un * q) * (B * q ^ e) := by linarith
      exact Nat.lt_of_mul_lt_mul_right hstep3
    unfold checkBox at hchk
    dsimp only at hchk
    rw [isOutOpt_false_of_leOpt hq0 hq1] at hchk
    simp only [Bool.false_eq_true, ↓reduceIte] at hchk
    have hdef_q0_f : ¬ (decide (2 ≤ q0) && decide (un * q0 ≤ 2 * ud * (q0 - 1))) = true := by
      intro hdef_q0
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hdef_q0
      obtain ⟨hq0_ge2, hdef_q0⟩ := hdef_q0
      have hanti := frac_anti hq0_ge2 hq0
      have h1 : 2 * ud * (q - 1) * q0 < un * q * q0 := Nat.mul_lt_mul_of_pos_right hab_lim (by omega)
      have h2 : un * q0 * (q - 1) ≤ 2 * ud * (q0 - 1) * (q - 1) := Nat.mul_le_mul_right _ hdef_q0
      have h4 : un * q * (q0 - 1) ≤ un * q0 * (q - 1) := by
        have := Nat.mul_le_mul_left un hanti; linarith
      have hq0_sub : 0 < q0 - 1 := by omega
      nlinarith
    change (if (decide (2 ≤ q0) && decide (un * q0 ≤ 2 * ud * (q0 - 1))) = true then true else _) = true at hchk
    rw [if_neg hdef_q0_f] at hchk
    have hlo_ab_f : ¬ (ln ≥ 2 * ld) := by
      intro hlo_ab
      have : 2 * ld * B ≤ ln * B := Nat.mul_le_mul_right B hlo_ab
      have : 2 * B ≤ sB := Nat.le_of_mul_le_mul_right (by linarith) hld_pos
      omega
    change (if ln ≥ 2 * ld then true else _) = true at hchk
    rw [if_neg hlo_ab_f] at hchk
    let q1' : Option ℕ := clampOpt un ud q1
    have hq_le_q1' : leOpt q q1' := by
      dsimp only [q1', clampOpt]
      by_cases hlt : un < 2 * ud
      · rw [if_pos hlt]
        have hgap : 0 < 2 * ud - un := by omega
        have hmul : (2 * ud - un) * q ≤ 2 * ud - 1 := by
          have : (2 * ud - un) * q = 2 * ud * q - un * q := Nat.sub_mul _ _ _
          have : 2 * ud * (q - 1) = 2 * ud * q - 2 * ud := by rw [Nat.mul_sub, mul_one]
          omega
        have hbnd : q ≤ (2 * ud - 1) / (2 * ud - un) := (Nat.le_div_iff_mul_le hgap).mpr (by rw [mul_comm]; exact hmul)
        cases q1 with
        | none => exact hbnd
        | some k => exact le_min hq1 hbnd
      · rw [if_neg hlt]; exact hq1
    let q1'' : Option ℕ := peelOpt q0 q1'
    have hq_le_q1'' : leOpt q q1'' := peelOpt_leOpt hq hq_le_q1'
    have do_split (qo : Option ℕ) (hqo : leOpt q qo) :
        (match pickV v1 v2 v3 v4 with
        | 0 => checkBox f (fixV v1) v2 v3 v4 q0 qo L bad kill3 && checkBox f (stepV v1) v2 v3 v4 q0 qo L bad kill3
        | 1 => checkBox f v1 (fixV v2) v3 v4 q0 qo L bad kill3 && checkBox f v1 (stepV v2) v3 v4 q0 qo L bad kill3
        | 2 => checkBox f v1 v2 (fixV v3) v4 q0 qo L bad kill3 && checkBox f v1 v2 (stepV v3) v4 q0 qo L bad kill3
        | _ => checkBox f v1 v2 v3 (fixV v4) q0 qo L bad kill3 && checkBox f v1 v2 v3 (stepV v4) q0 qo L bad kill3) = true →
        L ≤ E ∨ (kill3 = true ∧ (E % 3 = 0 ∨ (q % 3 = 2 ∧ e % 2 = 1))) ∨ E ∉ bad := by
      intro hs
      split at hs
      · simp only [Bool.and_eq_true] at hs
        rcases h1.split with h1a | h1b
        · simpa only [fixV_p] using ih h1a h2 h3 h4 hq0 hqo (by simpa only [fixV_p, vSigma_fixV] using hB_sig) (by simpa only [fixV_p] using hBlo_sig) (by simpa only [fixV_p] using hcop) (by simpa only [fixV_p] using hab) (by simpa only [fixV_p] using hprim) hs.1
        · simpa only [stepV_p] using ih h1b h2 h3 h4 hq0 hqo (by simpa only [stepV_p, vSigma_stepV] using hB_sig) (by simpa only [stepV_p] using hBlo_sig) (by simpa only [stepV_p] using hcop) (by simpa only [stepV_p] using hab) (by simpa only [stepV_p] using hprim) hs.2
      · simp only [Bool.and_eq_true] at hs
        rcases h2.split with h2a | h2b
        · simpa only [fixV_p] using ih h1 h2a h3 h4 hq0 hqo (by simpa only [fixV_p, vSigma_fixV] using hB_sig) (by simpa only [fixV_p] using hBlo_sig) (by simpa only [fixV_p] using hcop) (by simpa only [fixV_p] using hab) (by simpa only [fixV_p] using hprim) hs.1
        · simpa only [stepV_p] using ih h1 h2b h3 h4 hq0 hqo (by simpa only [stepV_p, vSigma_stepV] using hB_sig) (by simpa only [stepV_p] using hBlo_sig) (by simpa only [stepV_p] using hcop) (by simpa only [stepV_p] using hab) (by simpa only [stepV_p] using hprim) hs.2
      · simp only [Bool.and_eq_true] at hs
        rcases h3.split with h3a | h3b
        · simpa only [fixV_p] using ih h1 h2 h3a h4 hq0 hqo (by simpa only [fixV_p, vSigma_fixV] using hB_sig) (by simpa only [fixV_p] using hBlo_sig) (by simpa only [fixV_p] using hcop) (by simpa only [fixV_p] using hab) (by simpa only [fixV_p] using hprim) hs.1
        · simpa only [stepV_p] using ih h1 h2 h3b h4 hq0 hqo (by simpa only [stepV_p, vSigma_stepV] using hB_sig) (by simpa only [stepV_p] using hBlo_sig) (by simpa only [stepV_p] using hcop) (by simpa only [stepV_p] using hab) (by simpa only [stepV_p] using hprim) hs.2
      · simp only [Bool.and_eq_true] at hs
        rcases h4.split with h4a | h4b
        · simpa only [fixV_p] using ih h1 h2 h3 h4a hq0 hqo (by simpa only [fixV_p, vSigma_fixV] using hB_sig) (by simpa only [fixV_p] using hBlo_sig) (by simpa only [fixV_p] using hcop) (by simpa only [fixV_p] using hab) (by simpa only [fixV_p] using hprim) hs.1
        · simpa only [stepV_p] using ih h1 h2 h3 h4b hq0 hqo (by simpa only [stepV_p, vSigma_stepV] using hB_sig) (by simpa only [stepV_p] using hBlo_sig) (by simpa only [stepV_p] using hcop) (by simpa only [stepV_p] using hab) (by simpa only [stepV_p] using hprim) hs.2
    change (if isOutOpt q0 q1'' then true else if !(canSplit v1 || canSplit v2 || canSplit v3 || canSplit v4) then checkLeafB ld ln q0 q1'' L bad kill3 false else _) = true at hchk
    rw [isOutOpt_false_of_leOpt hq0 hq_le_q1''] at hchk
    simp only [Bool.false_eq_true, ↓reduceIte] at hchk
    by_cases hfixed : (!(canSplit v1 || canSplit v2 || canSplit v3 || canSplit v4)) = true
    · rw [if_pos hfixed] at hchk
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hfixed
      obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hfixed
      have e1 := h1.eq_of_not_canSplit c1
      have e2 := h2.eq_of_not_canSplit c2
      have e3 := h3.eq_of_not_canSplit c3
      have e4 := h4.eq_of_not_canSplit c4
      have hBeq : B = ld := by dsimp [B, ld]; rw [e1.2.1, e2.2.1, e3.2.1, e4.2.1]
      have hsBeq : sB = ln := by dsimp [sB, ln]; rw [e1.2.2, e2.2.2, e3.2.2, e4.2.2]
      have hres := checkLeafB_sound hld_pos hq hq0 hq_le_q1'' he (hsBeq ▸ hBeq ▸ hBdef)
        (hsBeq ▸ hBeq ▸ hab_nat) (fun k hk => hsBeq ▸ hBeq ▸ hprev_q k hk) (fun h => by cases h) hchk
      have hEeq : ln * ppSum q e - 2 * (ld * q ^ e) = E := by
        dsimp [E]; rw [hsm, ← hBeq, ← hsBeq]
      rwa [hEeq] at hres
    · rw [if_neg hfixed] at hchk
      have hq1''_eq1 : peelOpt q0 (clampOpt (v1.un * v2.un * v3.un * v4.un) (v1.ud * v2.ud * v3.ud * v4.ud) q1) = q1'' := rfl
      have hq1''_eq2 : peelOpt q0 (clampOpt un ud q1) = q1'' := rfl
      try rw [hq1''_eq1] at hchk
      try rw [hq1''_eq2] at hchk
      obtain ⟨q1v, hq1''_val⟩ : ∃ q1v, q1'' = q1v := ⟨q1'', rfl⟩
      rw [hq1''_val] at hchk hq_le_q1''
      cases q1v with
      | none =>
        dsimp only at hchk
        exact do_split none trivial hchk
      | some k =>
        dsimp only at hchk
        change q ≤ k at hq_le_q1''
        by_cases hpin1 : ln * (k + 1) > 2 * ld * k
        · rw [if_pos hpin1] at hchk
          have hab_lo_q : 2 * (ld * q) < ln * (q + 1) := by
            have h1' : (k + 1) * q ≤ (q + 1) * k := by nlinarith
            have h2' : 2 * ld * k * q < ln * (k + 1) * q := Nat.mul_lt_mul_of_pos_right hpin1 hq.pos
            have h3' : ln * (k + 1) * q ≤ ln * (q + 1) * k := by
              have := Nat.mul_le_mul_left ln h1'; linarith
            have h4' : (2 * (ld * q)) * k < (ln * (q + 1)) * k := by linarith
            exact Nat.lt_of_mul_lt_mul_right h4'
          have hdvd_m : ld * q ∣ m := Nat.mul_dvd_mul hld_dvd_B (dvd_pow_self q (by omega))
          have hsig_lo_q : sigma 1 (ld * q) = ln * (q + 1) := by
            rw [isMultiplicative_sigma.map_mul_of_coprime hcop_ld, hld_sig, ← ppSum_one hq.two_le, ppSum_eq_sigma hq, pow_one]
          have heq_m : ld * q = m := by
            by_contra hne
            have hmem : ld * q ∈ m.properDivisors := Nat.mem_properDivisors.mpr
              ⟨hdvd_m, lt_of_le_of_ne (Nat.le_of_dvd hmpos hdvd_m) hne⟩
            have hd := (defic_iff_nat (by have := hq.pos; positivity)).mp (hprim _ hmem)
            rw [hsig_lo_q] at hd; omega
          have he1 : e = 1 := by
            by_contra hne
            have h2 : ld * q < B * q ^ e := by
              have h1' : ld ≤ B := Nat.le_of_dvd hBpos hld_dvd_B
              have h2' : q < q ^ e := by simpa using Nat.pow_lt_pow_right hq.one_lt (show 1 < e by omega)
              exact Nat.mul_lt_mul_of_le_of_lt h1' h2' hBpos
            exact absurd heq_m (ne_of_lt h2)
          have hBeq : ld = B := by
            dsimp [m] at heq_m; rw [he1, pow_one] at heq_m
            exact Nat.eq_of_mul_eq_mul_right hq.pos heq_m
          have hsBeq : ln = sB := by rw [← hld_sig, hBeq, hB_sig]
          change checkLeafB ld ln q0 (some k) L bad kill3 true = true at hchk
          have hres := checkLeafB_sound (q1 := some k) hld_pos hq hq0 hq_le_q1'' he
            (by rw [hBeq, hsBeq]; exact hBdef)
            (by rw [hBeq, hsBeq]; exact hab_nat)
            (fun j hj => by rw [hBeq, hsBeq]; exact hprev_q j hj) (fun _ => he1) hchk
          have hEeq : ln * ppSum q e - 2 * (ld * q ^ e) = E := by
            dsimp [E]; rw [hsm, hBeq, hsBeq]
          rwa [hEeq] at hres
        · rw [if_neg hpin1] at hchk
          by_cases hqeq : (q0 == k) = true
          · rw [if_pos hqeq] at hchk
            have hqq0 : q = q0 := by have : q0 = k := beq_iff_eq.mp hqeq; omega
            subst hqq0
            cases hf : findEmin 25 un ud q q (1 + q) 1 with
            | none => rw [hf] at hchk; simp at hchk
            | some triple =>
              rcases triple with ⟨e0, qpow0, sQ0⟩
              rw [hf] at hchk
              dsimp only at hchk
              by_cases hpin_e : ln * sQ0 > 2 * ld * qpow0
              · rw [if_pos hpin_e] at hchk
                obtain ⟨he0_ge1, rfl, rfl, _, hprev0⟩ :=
                  findEmin_sound hq.two_le (pow_one q).symm (by rw [ppSum_one hq.two_le]; ring) hf
                have he0_le_e : e0 ≤ e := by
                  by_contra! hlt
                  have hle_e := hprev0 e he hlt
                  have h1' : sB * ppSum q e * ud ≤ un * B * ppSum q e := by
                    have := Nat.mul_le_mul_right (ppSum q e) hhi; linarith
                  have h2' : un * ppSum q e * B ≤ 2 * ud * q ^ e * B := Nat.mul_le_mul_right B hle_e
                  have h3' : sB * ppSum q e * ud ≤ 2 * (B * q ^ e) * ud := by
                    have : un * B * ppSum q e = un * ppSum q e * B := by ring
                    have : 2 * ud * q ^ e * B = 2 * (B * q ^ e) * ud := by ring
                    linarith
                  have := Nat.le_of_mul_le_mul_right h3' hud_pos
                  omega
                have hdvd_m : ld * q ^ e0 ∣ m := Nat.mul_dvd_mul hld_dvd_B (pow_dvd_pow q he0_le_e)
                have hsig_lo_e : sigma 1 (ld * q ^ e0) = ln * ppSum q e0 := by
                  rw [isMultiplicative_sigma.map_mul_of_coprime (hcop_ld.pow_right e0), hld_sig, ← ppSum_eq_sigma hq]
                have heq_m : ld * q ^ e0 = m := by
                  by_contra hne
                  have hmem : ld * q ^ e0 ∈ m.properDivisors := Nat.mem_properDivisors.mpr
                    ⟨hdvd_m, lt_of_le_of_ne (Nat.le_of_dvd hmpos hdvd_m) hne⟩
                  have hd := (defic_iff_nat (by have := hq.pos; positivity)).mp (hprim _ hmem)
                  rw [hsig_lo_e] at hd; rw [mul_assoc 2 ld (q ^ e0)] at hpin_e; omega
                have he_eq : e = e0 := by
                  by_contra hne
                  have hlt : e0 < e := by omega
                  have h1' : ld ≤ B := Nat.le_of_dvd hBpos hld_dvd_B
                  have h2' : q ^ e0 < q ^ e := Nat.pow_lt_pow_right hq.one_lt hlt
                  have : ld * q ^ e0 < m := Nat.mul_lt_mul_of_le_of_lt h1' h2' hBpos
                  exact absurd heq_m (ne_of_lt this)
                subst he_eq
                have hE_eq : ln * ppSum q e - 2 * ld * q ^ e = E := by
                  dsimp only [E]; rw [← heq_m, hsig_lo_e]; ring_nf
                dsimp only [ln, ld] at hE_eq
                rw [hE_eq] at hchk
                simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
                  Bool.not_eq_true'] at hchk
                rcases hchk with (h1 | ⟨hk, h2⟩) | h3
                · left; exact h1
                · right; left; exact ⟨hk, h2⟩
                · right; right; exact not_mem_of_isBad_false h3
              · rw [if_neg hpin_e] at hchk
                exact do_split (some k) hq_le_q1'' hchk
          · rw [if_neg hqeq] at hchk
            by_cases hpeel : (decide (q0 < k) && decide (un * (k + 1) ≤ 2 * ud * k)) = true
            · rw [if_pos hpeel] at hchk
              simp only [Bool.and_eq_true, Bool.or_eq_true] at hchk
              by_cases hq_top : q = k
              · subst hq_top
                rcases hchk.2 with hcomp | htop
                · exact absurd hq (not_prime_of_isComp hcomp)
                · exact ih h1 h2 h3 h4 le_rfl le_rfl hB_sig hBlo_sig hcop hab hprim htop
              · exact ih (q1 := some (k - 1)) h1 h2 h3 h4 hq0 (show q ≤ k - 1 by omega) hB_sig hBlo_sig hcop hab hprim hchk.1
            · rw [if_neg hpeel] at hchk
              exact do_split (some k) hq_le_q1'' hchk
def runP4s (p3 l1 l2 l3 : ℕ) (h1 : Option ℕ) (L : ℕ) (bad : List ℕ) (p4s : List (ℕ × ℕ)) : Bool :=
  p4s.all fun (p4, q0) =>
    let l4 := if p4 % 3 == 2 then 2 else 1
    let s3 := if p3 % 3 == 2 then 2 else 1
    let s4 := if p4 % 3 == 2 then 2 else 1
    checkBox 45 (mkV 3 l1 h1 1) (mkV 5 l2 none 2) (mkV p3 l3 none s3) (mkV p4 l4 none s4) q0 none L bad true

end CheckBox

section SmallCases

def checkMinCover : ℕ → VState → VState → VState → VState → List (ℕ × ℕ × ℕ × ℕ) → Bool
  | 0, _, _, _, _, _ => false
  | fuel + 1, v1, v2, v3, v4, mins =>
    if mins.any (fun m => decide (m.1 ≤ v1.l ∧ m.2.1 ≤ v2.l ∧ m.2.2.1 ≤ v3.l ∧ m.2.2.2 ≤ v4.l)) then
      true
    else
      let un := v1.un * v2.un * v3.un * v4.un
      let ud := v1.ud * v2.ud * v3.ud * v4.ud
      if un ≤ 2 * ud then true
      else if !(canSplit v1 || canSplit v2 || canSplit v3 || canSplit v4) then false
      else
        match pickV v1 v2 v3 v4 with
        | 0 => checkMinCover fuel (fixV v1) v2 v3 v4 mins && checkMinCover fuel (stepV v1) v2 v3 v4 mins
        | 1 => checkMinCover fuel v1 (fixV v2) v3 v4 mins && checkMinCover fuel v1 (stepV v2) v3 v4 mins
        | 2 => checkMinCover fuel v1 v2 (fixV v3) v4 mins && checkMinCover fuel v1 v2 (stepV v3) v4 mins
        | _ => checkMinCover fuel v1 v2 v3 (fixV v4) mins && checkMinCover fuel v1 v2 v3 (stepV v4) mins

lemma checkMinCover_sound {fuel : ℕ} {v1 v2 v3 v4 : VState} {a b c d : ℕ}
    {mins : List (ℕ × ℕ × ℕ × ℕ)}
    (h1 : VValid v1 a) (h2 : VValid v2 b) (h3 : VValid v3 c) (h4 : VValid v4 d)
    (hab : 2 * (v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d) <
      vSigma v1 a * vSigma v2 b * vSigma v3 c * vSigma v4 d)
    (hchk : checkMinCover fuel v1 v2 v3 v4 mins = true) :
    ∃ m ∈ mins, m.1 ≤ a ∧ m.2.1 ≤ b ∧ m.2.2.1 ≤ c ∧ m.2.2.2 ≤ d := by
  induction fuel generalizing v1 v2 v3 v4 with
  | zero => simp [checkMinCover] at hchk
  | succ f ih =>
    unfold checkMinCover at hchk
    dsimp only at hchk
    by_cases hmin : mins.any (fun m => decide (m.1 ≤ v1.l ∧ m.2.1 ≤ v2.l ∧ m.2.2.1 ≤ v3.l ∧ m.2.2.2 ≤ v4.l)) = true
    · rw [List.any_eq_true] at hmin
      obtain ⟨m, hm, hc⟩ := hmin
      simp only [decide_eq_true_eq] at hc
      have ha : v1.l ≤ a := by rcases h1 with ⟨_, hl, _, _, _, _, _, he⟩ | ⟨_, hl, _⟩ <;> omega
      have hb : v2.l ≤ b := by rcases h2 with ⟨_, hl, _, _, _, _, _, he⟩ | ⟨_, hl, _⟩ <;> omega
      have hc' : v3.l ≤ c := by rcases h3 with ⟨_, hl, _, _, _, _, _, he⟩ | ⟨_, hl, _⟩ <;> omega
      have hd : v4.l ≤ d := by rcases h4 with ⟨_, hl, _, _, _, _, _, he⟩ | ⟨_, hl, _⟩ <;> omega
      exact ⟨m, hm, by omega, by omega, by omega, by omega⟩
    · rw [if_neg hmin] at hchk
      let B := v1.p ^ a * v2.p ^ b * v3.p ^ c * v4.p ^ d
      let sB := vSigma v1 a * vSigma v2 b * vSigma v3 c * vSigma v4 d
      let un := v1.un * v2.un * v3.un * v4.un
      let ud := v1.ud * v2.ud * v3.ud * v4.ud
      by_cases hle : un ≤ 2 * ud
      · exfalso
        have hud_pos : 0 < ud := by
          have := h1.ud_pos; have := h2.ud_pos; have := h3.ud_pos; have := h4.ud_pos
          dsimp only [ud]; positivity
        have hhi : sB * ud ≤ un * B := by
          have m1 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1.hi_ratio h2.hi_ratio) h3.hi_ratio) h4.hi_ratio
          dsimp only [sB, ud, un, B]; linarith
        have : sB * ud ≤ 2 * B * ud := by
          have := Nat.mul_le_mul_right B hle; linarith
        have : sB ≤ 2 * B := Nat.le_of_mul_le_mul_right this hud_pos
        change 2 * B < sB at hab; omega
      · change (if un ≤ 2 * ud then true else _) = true at hchk
        rw [if_neg hle] at hchk
        by_cases hns : (!(canSplit v1 || canSplit v2 || canSplit v3 || canSplit v4)) = true
        · rw [if_pos hns] at hchk; cases hchk
        · rw [if_neg hns] at hchk
          split at hchk
          · simp only [Bool.and_eq_true] at hchk
            rcases h1.split with h1a | h1b
            · exact ih h1a h2 h3 h4 hab hchk.1
            · exact ih h1b h2 h3 h4 (by simpa only [stepV_p, vSigma_stepV] using hab) hchk.2
          · simp only [Bool.and_eq_true] at hchk
            rcases h2.split with h2a | h2b
            · exact ih h1 h2a h3 h4 hab hchk.1
            · exact ih h1 h2b h3 h4 (by simpa only [stepV_p, vSigma_stepV] using hab) hchk.2
          · simp only [Bool.and_eq_true] at hchk
            rcases h3.split with h3a | h3b
            · exact ih h1 h2 h3a h4 hab hchk.1
            · exact ih h1 h2 h3b h4 (by simpa only [stepV_p, vSigma_stepV] using hab) hchk.2
          · simp only [Bool.and_eq_true] at hchk
            rcases h4.split with h4a | h4b
            · exact ih h1 h2 h3 h4a hab hchk.1
            · exact ih h1 h2 h3 h4b (by simpa only [stepV_p, vSigma_stepV] using hab) hchk.2
    
    def checkWitness (n sN : ℕ) (wit : List ℕ) : Bool :=
      decide (wit.Nodup) &&
      wit.all (fun d => decide (d ∣ n ∧ d < n)) &&
      decide (wit.sum + 2 * n = sN)
    
    lemma pseudoperfect_of_checkWitness {n sN : ℕ} {wit : List ℕ}
        (hn : 0 < n) (hs : sN = sigma 1 n) (hchk : checkWitness n sN wit = true) :
        n.Pseudoperfect := by
      unfold checkWitness at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
      obtain ⟨⟨hnd, hsub⟩, hsum⟩ := hchk
      have hsubF : wit.toFinset ⊆ n.properDivisors := fun d hd =>
        Nat.mem_properDivisors.mpr (hsub d (List.mem_toFinset.mp hd))
      have hsumF : ∑ d ∈ wit.toFinset, d = wit.sum := by
        generalize wit = l at hnd ⊢
        simpa only [List.map_id'] using List.sum_toFinset (fun x => x) hnd
      apply pseudoperfect_of_excess hn hsubF
      rw [← Nat.cast_sum, hsumF]
      dsimp only [excess]
      omega
end SmallCases

section DataAndDecide

def w3Witnesses : List (ℕ × ℕ × ℕ × ℕ × List ℕ) := [
  (7, 2, 1, 2, [5, 7, 9, 15]),
  (7, 2, 2, 1, [1, 5, 7, 15, 21, 25]),
  (7, 3, 1, 1, [3, 5, 7, 15]),
  (11, 3, 2, 1, [1, 5, 9, 15]),
  (13, 3, 3, 2, [3, 5, 9, 13, 15, 25, 27, 39, 45, 65, 75, 125, 135, 169, 195, 225]),
  (13, 4, 2, 2, [5, 9, 15, 25, 27, 39, 45, 65, 75, 81, 117, 135, 169, 195, 225, 351, 405]),
  (13, 4, 3, 1, [3, 9, 13, 15, 25, 27, 39, 65, 75, 81, 117, 125, 195, 225]),
  (13, 5, 2, 1, [1, 3, 9, 13]),
]

def w4No5Witnesses : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ) := [
  (7, 11, 13, 2, 2, 2, 3, [1, 3, 7, 11, 13, 33, 39, 49, 63, 77, 91, 99, 117, 121, 143, 147, 169, 231, 273, 363, 429, 441, 507, 539, 637, 819, 847, 1001, 1089, 1183, 1287, 77077]),
  (7, 11, 13, 2, 2, 3, 2, [3, 7, 9, 11, 33, 39, 49, 63, 77, 91, 99, 117, 121, 143, 147, 169, 231, 273, 363, 429, 441, 507, 539, 693, 819, 121121]),
  (7, 11, 13, 2, 3, 2, 2, [1, 3, 7, 9, 11, 21, 33, 39, 49, 63, 77, 91, 99, 117, 121, 143, 147, 169, 231, 273, 363, 429, 441, 507, 33957, 273273]),
  (7, 11, 13, 3, 1, 1, 2, [7, 11]),
  (7, 11, 13, 3, 1, 2, 1, [3, 7, 11, 13, 21, 27, 33, 63, 77, 91, 99, 117, 121, 143, 189, 231]),
  (7, 11, 13, 3, 2, 1, 1, [7, 9, 11, 21, 27, 33, 39, 49, 63, 77, 91, 99, 117, 143, 147, 189, 231, 273, 297, 429, 441, 539, 637, 693]),
  (7, 11, 13, 4, 1, 1, 1, [3, 7, 9, 11, 21, 27, 33, 39, 63, 77, 81, 91]),
  (7, 11, 17, 3, 2, 2, 1, [3, 7, 9, 17, 21, 33, 49, 51, 63, 77, 99, 119, 121, 147, 153, 187, 189, 231, 297, 357, 363, 441, 459, 539, 561, 693, 833, 847, 1071, 1089, 1309, 1323, 1683, 2057]),
  (7, 11, 17, 3, 3, 1, 2, [1, 7, 9, 11, 17, 21, 33, 49, 51, 63, 77, 99, 119, 147, 153, 187, 189, 289, 297, 343, 357, 441, 459, 539, 561, 693, 833, 867, 1029, 54621]),
  (7, 11, 17, 4, 2, 1, 1, [1, 7, 9, 11, 17, 27, 33, 49, 51, 63, 77, 81, 99, 147, 153, 187, 189, 231, 297, 357, 441, 459, 539, 561, 567, 693]),
  (7, 11, 17, 5, 1, 3, 2, [1, 3, 7, 9, 11, 17, 21, 27, 33, 51, 63, 81, 99, 119, 121, 153, 187, 189, 231, 243, 289, 297, 357, 363, 459, 561, 567, 693, 847, 867, 891, 1071, 1089, 1309, 1331, 1683, 1701, 166617]),
  (7, 11, 17, 6, 1, 2, 2, [1, 3, 7, 11, 17, 21, 27, 33, 51, 63, 81, 99, 119, 121, 153, 187, 189, 231, 243, 289, 297, 357, 459, 129591]),
  (7, 11, 19, 3, 2, 3, 2, [3, 11, 19, 21, 27, 33, 49, 57, 63, 77, 99, 121, 133, 147, 171, 189, 209, 231, 297, 361, 363, 399, 441, 539, 627, 693, 847, 931, 1083, 1089, 1197, 1323, 1331, 1463, 1617, 1881, 2079, 2299, 2527, 2541, 2793, 337953]),
  (7, 11, 19, 3, 3, 2, 2, [1, 3, 7, 11, 19, 21, 27, 33, 49, 57, 63, 77, 99, 121, 133, 147, 171, 189, 209, 231, 297, 343, 361, 363, 399, 441, 513, 627, 693, 847, 931, 1029, 337953, 1362053]),
  (7, 11, 19, 3, 3, 3, 1, [1, 3, 7, 9, 11, 19, 21, 27, 33, 49, 57, 63, 77, 99, 121, 133, 147, 189, 209, 75867]),
  (7, 11, 19, 4, 2, 1, 2, [7, 9, 11, 19, 21, 27, 33, 49, 57, 63, 77, 81, 99, 133, 147, 171, 189, 231, 297, 361, 399, 441, 513, 539, 567, 627, 693, 891, 931, 1083, 1197, 1323]),
  (7, 11, 19, 4, 2, 2, 1, [1, 7, 9, 19, 21, 27, 49, 57, 63, 77, 81, 99, 121, 133, 147, 171, 189, 209, 231, 297, 363, 399, 513, 539, 567, 92169]),
  (7, 11, 19, 4, 3, 1, 1, [3, 7, 9, 19, 21, 27, 33, 49, 57, 63, 77, 81, 99, 133, 147, 171, 189, 209, 231, 297, 343, 441]),
  (7, 11, 19, 5, 2, 1, 1, [1, 3, 7, 9, 19, 21, 27, 33, 49, 57, 63, 77, 81, 99, 133, 147, 189, 209, 231, 243, 297, 399]),
  (7, 11, 23, 4, 3, 2, 2, [1, 3, 7, 11, 21, 23, 27, 33, 49, 63, 69, 77, 81, 99, 121, 147, 189, 207, 231, 253, 297, 343, 181447, 2863707]),
  (7, 11, 23, 4, 4, 3, 1, [1, 3, 7, 9, 11, 21, 27, 33, 49, 63, 69, 77, 81, 99, 121, 147, 161, 189, 231, 253, 297, 343, 363, 441, 483, 539, 567, 621, 693, 759, 847, 891, 1029, 1089, 1127, 1323, 1331, 1449, 1617, 1771, 1863, 2079, 2277, 2401, 2541, 1004157]),
  (7, 11, 23, 5, 2, 2, 2, [1, 3, 7, 9, 11, 23, 27, 33, 49, 63, 69, 77, 81, 99, 121, 147, 161, 189, 207, 231, 243, 297, 363, 441, 483, 529, 539, 567, 621, 693, 99981, 1577961]),
  (7, 11, 23, 5, 2, 4, 1, [1, 3, 7, 9, 11, 21, 23, 33, 49, 63, 69, 77, 81, 99, 121, 147, 161, 189, 207, 231, 243, 253, 297, 363, 483, 539, 567, 621, 693, 759, 847, 891, 1089, 1127, 1323, 307461]),
  (7, 11, 23, 5, 3, 2, 1, [3, 7, 9, 11, 23, 27, 33, 49, 63, 69, 53361, 781011]),
  (7, 11, 23, 6, 2, 2, 1, [7, 11, 21, 23, 27, 33, 49, 63, 69, 77, 81, 99, 121, 147, 161, 207, 231, 243, 253, 297, 363, 39123]),
  (7, 13, 17, 4, 2, 3, 3, [1, 3, 9, 13, 17, 21, 27, 39, 49, 51, 63, 81, 91, 117, 119, 147, 153, 169, 189, 221, 273, 289, 97461, 3800979]),
  (7, 13, 17, 4, 3, 2, 2, [1, 3, 7, 9, 13, 17, 21, 27, 39, 49, 51, 63, 81, 91, 117, 119, 153, 169, 189, 221, 273, 52479, 236691, 4970511]),
  (7, 13, 17, 5, 2, 2, 2, [1, 3, 7, 9, 13, 21, 27, 39, 49, 63, 81, 91, 117, 119, 147, 153, 169, 189, 221, 243, 273, 289, 351, 441, 459, 507, 146523, 2393209]),
  (7, 13, 17, 5, 3, 2, 1, [1, 3, 7, 13, 17, 21, 39, 49, 51, 63, 81, 91, 117, 119, 147, 682227]),
  (7, 13, 17, 6, 2, 3, 1, [3, 9, 13, 17, 21, 27, 39, 51, 63, 81, 91, 117, 119, 147, 153, 169, 189, 221, 243, 273, 351, 357, 441, 459, 507, 567, 637, 729, 819, 833, 1053, 1071, 1183, 1323, 1377, 1521, 1547, 670761]),
  (7, 13, 17, 6, 3, 1, 2, [1, 3, 9, 13, 17, 21, 27, 39, 51, 63, 81, 91, 117, 119, 147, 153, 189, 221, 243, 273, 343, 351, 357, 441, 459, 567, 637, 227409]),
  (7, 13, 17, 7, 2, 2, 1, [1, 3, 7, 9, 13, 17, 21, 27, 39, 49, 51, 63, 81, 91, 119, 147, 153, 86751]),
  (7, 13, 19, 6, 4, 3, 3, [7, 9, 13, 19, 21, 27, 39, 49, 57, 63, 81, 91, 144039, 2069613, 50557689, 949361049]),
  (7, 13, 19, 7, 3, 4, 4, [1, 3, 9, 13, 21, 27, 39, 49, 57, 63, 81, 91, 117, 133, 147, 169, 292201, 9074457, 2408702751, 33498882729]),
  (7, 13, 19, 7, 3, 5, 3, [9, 13, 19, 21, 27, 39, 49, 57, 63, 81, 91, 117, 133, 147, 169, 171, 189, 243, 247, 273, 343, 351, 361, 441, 68229, 1008273, 382060497, 5915249613]),
  (7, 13, 19, 7, 4, 3, 2, [3, 9, 13, 19, 21, 27, 39, 49, 57, 63, 81, 91, 117, 133, 147, 169, 189, 243, 247, 273, 343, 351, 361, 399, 46683, 614061, 55879551, 1491101703]),
  (7, 13, 19, 8, 3, 3, 3, [1, 7, 13, 19, 21, 27, 49, 57, 63, 81, 91, 117, 133, 108927, 42758037, 4600749699]),
  (7, 13, 19, 8, 4, 2, 3, [9, 13, 19, 21, 27, 39, 49, 63, 81, 91, 117, 133, 147, 169, 171, 189, 243, 247, 343, 351, 361, 399, 441, 68229, 2407509, 190563597]),
  (7, 13, 19, 10, 3, 4, 2, [1, 3, 9, 13, 19, 21, 27, 39, 57, 63, 81, 91, 117, 133, 147, 169, 171, 243, 247, 273, 343, 351, 361, 399, 441, 507, 513, 567, 637, 729, 741, 819, 931, 1029, 1053, 1083, 1183, 1197, 1323, 1521, 1539, 1701, 1729, 2187, 2197, 2223, 2457, 793117, 114700131, 3147881373]),
]

-- (a0, b0, p3, L, g, P0, bad, ds, bestDivForP3, ds3p3, relNum5)
def bases3Data : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × ℕ × List ℕ × ℕ) := [
  (2, 1, 7, 3, 2, 309, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105], 9, [1, 3, 7, 9, 21], 0),
  (2, 1, 11, 23, 2, 441, [2, 7, 22], [1, 3, 5, 9, 11, 15, 33, 45, 55, 99, 165], 15, [1, 3, 9, 11, 33], 0),
  (2, 1, 13, 36, 2, 507, [2, 7, 11, 35], [1, 3, 5, 9, 13, 15, 39, 45, 65, 117, 195], 15, [1, 3, 9, 13, 39], 0),
  (3, 1, 11, 23, 2, 1395, [2, 7, 22], [1, 3, 5, 9, 11, 15, 27, 33, 45, 55, 99, 135, 165, 297, 495], 15, [1, 3, 9, 11, 27, 33, 99], 0),
  (3, 1, 13, 12, 2, 1605, [2, 7, 11], [1, 3, 5, 9, 13, 15, 27, 39, 45, 65, 117, 135, 195, 351, 585], 15, [1, 3, 9, 13, 27, 39, 117], 0),
  (3, 1, 17, 12, 2, 2025, [2, 7, 11], [1, 3, 5, 9, 15, 17, 27, 45, 51, 85, 135, 153, 255, 459, 765], 27, [1, 3, 9, 17, 27, 51, 153], 0),
  (3, 1, 19, 27, 2, 2235, [2, 7, 11, 26], [1, 3, 5, 9, 15, 19, 27, 45, 57, 95, 135, 171, 285, 513, 855], 27, [1, 3, 9, 19, 27, 57, 171], 0),
  (3, 1, 23, 35, 2, 2655, [2, 7, 11, 22, 34], [1, 3, 5, 9, 15, 23, 27, 45, 69, 115, 135, 207, 345, 621, 1035], 27, [1, 3, 9, 23, 27, 69, 207], 0),
  (2, 2, 11, 23, 2, 2361, [2, 7, 22], [1, 3, 5, 9, 11, 15, 25, 33, 45, 55, 75, 99, 165, 225, 275, 495, 825], 15, [1, 3, 9, 11, 33], 142),
  (2, 2, 13, 12, 2, 2717, [2, 7, 11], [1, 3, 5, 9, 13, 15, 25, 39, 45, 65, 75, 117, 195, 225, 325, 585, 975], 15, [1, 3, 9, 13, 39], 149),
  (2, 2, 17, 12, 2, 3429, [2, 7, 11], [1, 3, 5, 9, 15, 17, 25, 45, 51, 75, 85, 153, 225, 255, 425, 765, 1275], 25, [1, 3, 9, 17, 51], 157),
  (2, 2, 19, 12, 2, 3785, [2, 7, 11], [1, 3, 5, 9, 15, 19, 25, 45, 57, 75, 95, 171, 225, 285, 475, 855, 1425], 25, [1, 3, 9, 19, 57], 160),
  (2, 2, 23, 23, 2, 4497, [2, 7, 11, 22], [1, 3, 5, 9, 15, 23, 25, 45, 69, 75, 115, 207, 225, 345, 575, 1035, 1725], 25, [1, 3, 9, 23, 69], 165),
  (3, 2, 29, 23, 2, 17625, [2, 7, 11, 22], [1, 3, 5, 9, 15, 25, 27, 29, 45, 75, 87, 135, 145, 225, 261, 435, 675, 725, 783, 1305, 2175, 3915, 6525], 45, [1, 3, 9, 27, 29, 87, 261], 156),
  (3, 2, 31, 23, 2, 18755, [2, 7, 11, 22], [1, 3, 5, 9, 15, 25, 27, 31, 45, 75, 93, 135, 155, 225, 279, 465, 675, 775, 837, 1395, 2325, 4185, 6975], 45, [1, 3, 9, 27, 31, 93, 279], 157),
  (3, 2, 37, 23, 2, 22145, [2, 7, 11, 22], [1, 3, 5, 9, 15, 25, 27, 37, 45, 75, 111, 135, 185, 225, 333, 555, 675, 925, 999, 1665, 2775, 4995, 8325], 45, [1, 3, 9, 27, 37, 111, 333], 160),
  (3, 2, 41, 23, 2, 24405, [2, 7, 11, 22], [1, 3, 5, 9, 15, 25, 27, 41, 45, 75, 123, 135, 205, 225, 369, 615, 675, 1025, 1107, 1845, 3075, 5535, 9225], 45, [1, 3, 9, 27, 41, 123, 369], 161),
]

def bases315Data : List (ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ) := [
  (157, 3, 2, 49137, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 157, 315, 471, 785, 1099, 1413, 2355, 3297, 5495, 7065, 9891, 16485]),
  (163, 3, 2, 50991, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 163, 315, 489, 815, 1141, 1467, 2445, 3423, 5705, 7335, 10269, 17115]),
  (167, 3, 2, 52227, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 167, 315, 501, 835, 1169, 1503, 2505, 3507, 5845, 7515, 10521, 17535]),
  (173, 3, 2, 54081, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 173, 315, 519, 865, 1211, 1557, 2595, 3633, 6055, 7785, 10899, 18165]),
  (179, 3, 2, 55935, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 179, 315, 537, 895, 1253, 1611, 2685, 3759, 6265, 8055, 11277, 18795]),
  (181, 3, 2, 56553, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 181, 315, 543, 905, 1267, 1629, 2715, 3801, 6335, 8145, 11403, 19005]),
  (191, 3, 2, 59643, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 191, 315, 573, 955, 1337, 1719, 2865, 4011, 6685, 8595, 12033, 20055]),
  (193, 3, 2, 60261, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 193, 315, 579, 965, 1351, 1737, 2895, 4053, 6755, 8685, 12159, 20265]),
  (197, 3, 2, 61497, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 197, 315, 591, 985, 1379, 1773, 2955, 4137, 6895, 8865, 12411, 20685]),
  (199, 3, 2, 62115, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 199, 315, 597, 995, 1393, 1791, 2985, 4179, 6965, 8955, 12537, 20895]),
]

def ds_45_17_19 : List ℕ := [1, 3, 5, 9, 15, 17, 19, 45, 51, 57, 85, 95, 153, 171, 255, 285, 323, 765, 855, 969, 1615, 2907, 4845]
def ds_45_19 : List ℕ := [1, 3, 5, 9, 15, 19, 45, 57, 95, 171, 285]
def ds_45_17 : List ℕ := [1, 3, 5, 9, 15, 17, 45, 51, 85, 153, 255]
-- 45*17*19: L=12, g=2, P=13545, bad=[2, 7, 11]

-- (p2, p3, p4, q0, L, g, P0, bad, ds, a2, a3, a4, ds_u2, ds_u3, ds_u4)
def basesNo5Data : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (7, 11, 13, 17, 7, 3, 8463, [2, 5, 6], [1, 3, 7, 9, 11, 13, 21, 33, 39, 63, 77, 91, 99, 117, 143, 231, 273, 429, 693, 819, 1001, 1287, 3003], 11, 4, 5, [1, 3, 9, 11, 13, 33, 39, 99, 117, 143, 429], [1, 3, 7, 9, 13, 21, 39, 63, 91, 117, 273], [1, 3, 7, 9, 11, 21, 33, 63, 77, 99, 231]),
  (7, 11, 17, 19, 7, 3, 10683, [2, 5, 6], [1, 3, 7, 9, 11, 17, 21, 33, 51, 63, 77, 99, 119, 153, 187, 231, 357, 561, 693, 1071, 1309, 1683, 3927], 20, 3, 5, [1, 3, 9, 11, 17, 33, 51, 99, 153, 187, 561], [1, 3, 7, 9, 17, 21, 51, 63, 119, 153, 357], [1, 3, 7, 9, 11, 21, 33, 63, 77, 99, 231]),
  (7, 11, 19, 23, 7, 3, 11793, [2, 5, 6], [1, 3, 7, 9, 11, 19, 21, 33, 57, 63, 77, 99, 133, 171, 209, 231, 399, 627, 693, 1197, 1463, 1881, 4389], 23, 3, 5, [1, 3, 9, 11, 19, 33, 57, 99, 171, 209, 627], [1, 3, 7, 9, 19, 21, 57, 63, 133, 171, 399], [1, 3, 7, 9, 11, 21, 33, 63, 77, 99, 231]),
  (7, 11, 23, 29, 7, 3, 14013, [2, 5, 6], [1, 3, 7, 9, 11, 21, 23, 33, 63, 69, 77, 99, 161, 207, 231, 253, 483, 693, 759, 1449, 1771, 2277, 5313], 28, 3, 5, [1, 3, 9, 11, 23, 33, 69, 99, 207, 253, 759], [1, 3, 7, 9, 21, 23, 63, 69, 161, 207, 483], [1, 3, 7, 9, 11, 21, 33, 63, 77, 99, 231]),
  (7, 11, 29, 31, 27, 3, 17343, [2, 5, 6, 26], [1, 3, 7, 9, 11, 21, 29, 33, 63, 77, 87, 99, 203, 231, 261, 319, 609, 693, 957, 1827, 2233, 2871, 6699], 37, 2, 5, [1, 3, 9, 11, 29, 33, 87, 99, 261, 319, 957], [1, 3, 7, 9, 21, 29, 63, 87, 203, 261, 609], [1, 3, 7, 9, 11, 21, 33, 63, 77, 99, 231]),
  (7, 11, 31, 37, 27, 3, 18453, [2, 5, 6, 26], [1, 3, 7, 9, 11, 21, 31, 33, 63, 77, 93, 99, 217, 231, 279, 341, 651, 693, 1023, 1953, 2387, 3069, 7161], 41, 2, 5, [1, 3, 9, 11, 31, 33, 93, 99, 279, 341, 1023], [1, 3, 7, 9, 21, 31, 63, 93, 217, 279, 651], [1, 3, 7, 9, 11, 21, 33, 63, 77, 99, 231]),
  (7, 11, 37, 41, 27, 3, 21783, [2, 5, 6, 26], [1, 3, 7, 9, 11, 21, 33, 37, 63, 77, 99, 111, 231, 259, 333, 407, 693, 777, 1221, 2331, 2849, 3663, 8547], 49, 4, 5, [1, 3, 9, 11, 33, 37, 99, 111, 333, 407, 1221], [1, 3, 7, 9, 21, 37, 63, 111, 259, 333, 777], [1, 3, 7, 9, 11, 21, 33, 63, 77, 99, 231]),
  (7, 11, 41, 43, 27, 3, 24003, [2, 5, 6, 26], [1, 3, 7, 9, 11, 21, 33, 41, 63, 77, 99, 123, 231, 287, 369, 451, 693, 861, 1353, 2583, 3157, 4059, 9471], 53, 8, 5, [1, 3, 9, 11, 33, 41, 99, 123, 369, 451, 1353], [1, 3, 7, 9, 21, 41, 63, 123, 287, 369, 861], [1, 3, 7, 9, 11, 21, 33, 63, 77, 99, 231]),
  (7, 11, 43, 47, 27, 3, 25113, [2, 5, 6, 26], [1, 3, 7, 9, 11, 21, 33, 43, 63, 77, 99, 129, 231, 301, 387, 473, 693, 903, 1419, 2709, 3311, 4257, 9933], 55, 10, 5, [1, 3, 9, 11, 33, 43, 99, 129, 387, 473, 1419], [1, 3, 7, 9, 21, 43, 63, 129, 301, 387, 903], [1, 3, 7, 9, 11, 21, 33, 63, 77, 99, 231]),
  (7, 11, 47, 53, 27, 3, 27333, [2, 5, 6, 26], [1, 3, 7, 9, 11, 21, 33, 47, 63, 77, 99, 141, 231, 329, 423, 517, 693, 987, 1551, 2961, 3619, 4653, 10857], 58, 13, 5, [1, 3, 9, 11, 33, 47, 99, 141, 423, 517, 1551], [1, 3, 7, 9, 21, 47, 63, 141, 329, 423, 987], [1, 3, 7, 9, 11, 21, 33, 63, 77, 99, 231]),
  (7, 13, 17, 19, 16, 3, 12285, [2, 5, 6, 15], [1, 3, 7, 9, 13, 17, 21, 39, 51, 63, 91, 117, 119, 153, 221, 273, 357, 663, 819, 1071, 1547, 1989, 4641], 41, 3, 4, [1, 3, 9, 13, 17, 39, 51, 117, 153, 221, 663], [1, 3, 7, 9, 17, 21, 51, 63, 119, 153, 357], [1, 3, 7, 9, 13, 21, 39, 63, 91, 117, 273]),
  (7, 13, 19, 23, 19, 3, 13559, [2, 5, 6, 15, 18], [1, 3, 7, 9, 13, 19, 21, 39, 57, 63, 91, 117, 133, 171, 247, 273, 399, 741, 819, 1197, 1729, 2223, 5187], 44, 3, 4, [1, 3, 9, 13, 19, 39, 57, 117, 171, 247, 741], [1, 3, 7, 9, 19, 21, 57, 63, 133, 171, 399], [1, 3, 7, 9, 13, 21, 39, 63, 91, 117, 273]),
  (7, 13, 23, 29, 19, 3, 16107, [2, 5, 6, 15, 18], [1, 3, 7, 9, 13, 21, 23, 39, 63, 69, 91, 117, 161, 207, 273, 299, 483, 819, 897, 1449, 2093, 2691, 6279], 49, 3, 4, [1, 3, 9, 13, 23, 39, 69, 117, 207, 299, 897], [1, 3, 7, 9, 21, 23, 63, 69, 161, 207, 483], [1, 3, 7, 9, 13, 21, 39, 63, 91, 117, 273]),
  (7, 13, 29, 31, 28, 3, 19929, [2, 5, 6, 15, 18, 27], [1, 3, 7, 9, 13, 21, 29, 39, 63, 87, 91, 117, 203, 261, 273, 377, 609, 819, 1131, 1827, 2639, 3393, 7917], 58, 2, 4, [1, 3, 9, 13, 29, 39, 87, 117, 261, 377, 1131], [1, 3, 7, 9, 21, 29, 63, 87, 203, 261, 609], [1, 3, 7, 9, 13, 21, 39, 63, 91, 117, 273]),
  (7, 13, 31, 37, 37, 3, 21203, [2, 5, 6, 15, 18, 27, 36], [1, 3, 7, 9, 13, 21, 31, 39, 63, 91, 93, 117, 217, 273, 279, 403, 651, 819, 1209, 1953, 2821, 3627, 8463], 61, 2, 4, [1, 3, 9, 13, 31, 39, 93, 117, 279, 403, 1209], [1, 3, 7, 9, 21, 31, 63, 93, 217, 279, 651], [1, 3, 7, 9, 13, 21, 39, 63, 91, 117, 273]),
  (7, 17, 19, 23, 16, 3, 17091, [2, 5, 6, 14, 15], [1, 3, 7, 9, 17, 19, 21, 51, 57, 63, 119, 133, 153, 171, 323, 357, 399, 969, 1071, 1197, 2261, 2907, 6783], 72, 3, 3, [1, 3, 9, 17, 19, 51, 57, 153, 171, 323, 969], [1, 3, 7, 9, 19, 21, 57, 63, 133, 171, 399], [1, 3, 7, 9, 17, 21, 51, 63, 119, 153, 357]),
  (7, 17, 23, 29, 16, 3, 20295, [2, 5, 6, 14, 15], [1, 3, 7, 9, 17, 21, 23, 51, 63, 69, 119, 153, 161, 207, 357, 391, 483, 1071, 1173, 1449, 2737, 3519, 8211], 76, 3, 3, [1, 3, 9, 17, 23, 51, 69, 153, 207, 391, 1173], [1, 3, 7, 9, 21, 23, 63, 69, 161, 207, 483], [1, 3, 7, 9, 17, 21, 51, 63, 119, 153, 357]),
  (7, 19, 23, 29, 19, 3, 22389, [2, 5, 6, 14, 15, 18], [1, 3, 7, 9, 19, 21, 23, 57, 63, 69, 133, 161, 171, 207, 399, 437, 483, 1197, 1311, 1449, 3059, 3933, 9177], 86, 3, 3, [1, 3, 9, 19, 23, 57, 69, 171, 207, 437, 1311], [1, 3, 7, 9, 21, 23, 63, 69, 161, 207, 483], [1, 3, 7, 9, 19, 21, 57, 63, 133, 171, 399]),
  (11, 13, 17, 19, 36, 5, 17433, [2, 5, 6, 7, 8, 19, 35], [1, 3, 9, 11, 13, 17, 33, 39, 51, 99, 117, 143, 153, 187, 221, 429, 561, 663, 1287, 1683, 1989, 2431, 7293], 41, 20, 11, [1, 3, 9, 13, 17, 39, 51, 117, 153, 221, 663], [1, 3, 9, 11, 17, 33, 51, 99, 153, 187, 561], [1, 3, 9, 11, 13, 33, 39, 99, 117, 143, 429]),
]

def dge2Pairs5 : List (ℕ × ℕ × ℕ) := [
  (11,13,2), (11,17,2), (11,19,2), (11,23,2), (11,29,2), (11,31,2), (11,37,2), (11,41,2), (11,43,2), (11,47,2),
  (11,53,2), (11,59,2), (11,61,2), (11,67,2), (11,71,2), (11,73,2), (11,79,2), (11,83,2), (11,89,2), (11,97,2),
  (11,101,2), (11,103,2), (11,107,2), (11,109,2), (11,113,2), (11,127,2), (11,131,2), (11,137,2), (11,139,2), (13,17,2),
  (13,19,2), (13,23,2), (13,29,2), (13,31,2), (13,37,2), (13,41,2), (13,43,2), (17,19,0), (17,23,0), (17,29,0),
  (17,31,0), (17,37,0), (17,41,0), (17,43,0), (17,47,0), (17,53,0), (17,59,0), (17,61,0), (17,67,0), (17,71,0),
  (17,73,0), (17,79,0), (17,83,0), (17,89,0), (17,97,0), (17,101,0), (17,103,0), (17,107,0), (17,109,0), (17,113,0),
  (17,127,0), (17,131,0), (17,137,0), (17,139,0), (17,149,0), (17,151,0), (17,157,0), (17,163,0), (17,167,0), (17,173,0),
  (17,179,0), (17,181,0), (17,191,0), (17,193,0), (17,197,0), (17,199,0), (17,211,0), (17,223,0), (17,227,0), (17,229,0),
  (17,233,0), (17,239,0), (17,241,0), (17,251,0), (19,23,0), (19,29,0), (19,31,0), (19,37,0), (19,41,0), (19,43,0),
  (19,47,0), (19,53,0), (19,59,0), (19,61,0), (19,67,0), (19,71,0), (19,73,0), (19,79,0), (19,83,0), (19,89,0),
  (23,29,0), (23,31,0), (23,37,0), (23,41,0), (23,43,0), (23,47,0), (29,31,0)
]

def cb5_11_0_pairs : List (ℕ × ℕ) := [(13,17),(17,19),(19,23),(23,29),(29,31),(31,37),(37,41),(41,43),(43,47),(47,53),(53,59),(59,61),(61,67),(67,71),(71,73),(73,79),(79,83),(83,89),(89,97),(97,101),(101,103),(103,107),(107,109),(109,113),(113,127)]
def cb5_11_1_pairs : List (ℕ × ℕ) := [(127,131),(131,137),(137,139),(139,149),(149,151),(151,157),(157,163),(163,167),(167,173),(173,179),(179,181),(181,191),(191,193),(193,197),(197,199),(199,211),(211,223),(223,227),(227,229),(229,233),(233,239),(239,241),(241,251),(251,257),(257,263)]
def cb5_11_2_pairs : List (ℕ × ℕ) := [(263,269),(269,271),(271,277),(277,281),(281,283)]
def cb5_13_0_pairs : List (ℕ × ℕ) := [(17,19),(19,23),(23,29),(29,31),(31,37),(37,41),(41,43),(43,47),(47,53),(53,59),(59,61),(61,67),(67,71),(71,73),(73,79),(79,83),(83,89),(89,97),(97,101),(101,103),(103,107),(107,109),(109,113),(113,127),(127,131)]
def cb5_13_1_pairs : List (ℕ × ℕ) := [(131,137),(137,139),(139,149),(149,151),(151,157),(157,163),(163,167),(167,173),(173,179),(179,181),(181,191),(191,193),(193,197),(197,199),(199,211),(211,223),(223,227),(227,229),(229,233),(233,239),(239,241),(241,251),(251,257),(257,263),(263,269)]
def cb5_13_2_pairs : List (ℕ × ℕ) := [(269,271),(271,277),(277,281),(281,283),(283,293),(293,307),(307,311),(311,313),(313,317),(317,331),(331,337),(337,347),(347,349),(349,353),(353,359),(359,367),(367,373),(373,379),(379,383),(383,389),(389,397),(397,401),(401,409),(409,419),(419,421)]
def cb5_13_3_pairs : List (ℕ × ℕ) := [(421,431),(431,433),(433,439),(439,443),(443,449),(449,457),(457,461),(461,463),(463,467),(467,479),(479,487),(487,491),(491,499),(499,503),(503,509),(509,521),(521,523),(523,541),(541,547),(547,557),(557,563),(563,569),(569,571),(571,577),(577,587)]
def cb5_13_4_pairs : List (ℕ × ℕ) := [(587,593),(593,599),(599,601),(601,607),(607,613),(613,617),(617,619),(619,631),(631,641),(641,643),(643,647),(647,653),(653,659),(659,661),(661,673),(673,677),(677,683),(683,691),(691,701),(701,709),(709,719),(719,727),(727,733),(733,739),(739,743)]
def cb5_13_5_pairs : List (ℕ × ℕ) := [(743,751),(751,757),(757,761),(761,769),(769,773)]
def cb5_17_0_pairs : List (ℕ × ℕ) := [(19,23),(23,29),(29,31),(31,37),(37,41),(41,43),(43,47),(47,53),(53,59),(59,61),(61,67),(67,71),(71,73),(73,79),(79,83),(83,89),(89,97),(97,101),(101,103),(103,107),(107,109),(109,113),(113,127),(127,131),(131,137)]
def cb5_17_1_pairs : List (ℕ × ℕ) := [(137,139),(139,149),(149,151),(151,157),(157,163),(163,167),(167,173),(173,179),(179,181),(181,191),(191,193),(193,197),(197,199),(199,211),(211,223),(223,227),(227,229),(229,233),(233,239),(239,241),(241,251),(251,257),(257,263),(263,269),(269,271)]
def cb5_17_2_pairs : List (ℕ × ℕ) := [(271,277),(277,281),(281,283),(283,293),(293,307),(307,311),(311,313),(313,317),(317,331),(331,337),(337,347),(347,349),(349,353),(353,359),(359,367),(367,373),(373,379),(379,383),(383,389),(389,397),(397,401),(401,409),(409,419),(419,421),(421,431)]
def cb5_17_3_pairs : List (ℕ × ℕ) := [(431,433),(433,439),(439,443),(443,449),(449,457),(457,461),(461,463),(463,467),(467,479),(479,487),(487,491),(491,499),(499,503),(503,509)]
def cb5_19_0_pairs : List (ℕ × ℕ) := [(23,29),(29,31),(31,37),(37,41),(41,43),(43,47),(47,53),(53,59),(59,61),(61,67),(67,71),(71,73),(73,79),(79,83),(83,89),(89,97),(97,101),(101,103),(103,107),(107,109),(109,113),(113,127),(127,131),(131,137),(137,139)]
def cb5_19_1_pairs : List (ℕ × ℕ) := [(139,149),(149,151),(151,157),(157,163),(163,167),(167,173),(173,179),(179,181),(181,191)]
def cb5_23_0_pairs : List (ℕ × ℕ) := [(29,31),(31,37),(37,41),(41,43),(43,47),(47,53),(53,59),(59,61),(61,67),(67,71),(71,73),(73,79),(79,83),(83,89),(89,97),(97,101)]
def cb5_29_0_pairs : List (ℕ × ℕ) := [(31,37),(37,41),(41,43),(43,47),(47,53),(53,59),(59,61),(61,67)]
def cb5_31_0_pairs : List (ℕ × ℕ) := [(37,41),(41,43),(43,47),(47,53),(53,59),(59,61)]
def cb5_37_0_pairs : List (ℕ × ℕ) := [(41,43),(43,47),(47,53)]
def cb5_41_0_pairs : List (ℕ × ℕ) := [(43,47),(47,53)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_11_0_ok : runP4s 11 2 2 2 (some 2) 23 [2, 7, 22] cb5_11_0_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_11_1_ok : runP4s 11 2 2 2 (some 2) 23 [2, 7, 22] cb5_11_1_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_11_2_ok : runP4s 11 2 2 2 (some 2) 23 [2, 7, 22] cb5_11_2_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_13_0_ok : runP4s 13 2 2 1 (some 4) 12 [2, 7, 11] cb5_13_0_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_13_1_ok : runP4s 13 2 2 1 (some 4) 12 [2, 7, 11] cb5_13_1_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_13_2_ok : runP4s 13 2 2 1 (some 4) 12 [2, 7, 11] cb5_13_2_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_13_3_ok : runP4s 13 2 2 1 (some 4) 12 [2, 7, 11] cb5_13_3_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_13_4_ok : runP4s 13 2 2 1 (some 4) 12 [2, 7, 11] cb5_13_4_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_13_5_ok : runP4s 13 2 2 1 (some 4) 12 [2, 7, 11] cb5_13_5_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_17_0_ok : runP4s 17 2 2 2 none 12 [2, 7, 11] cb5_17_0_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_17_1_ok : runP4s 17 2 2 2 none 12 [2, 7, 11] cb5_17_1_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_17_2_ok : runP4s 17 2 2 2 none 12 [2, 7, 11] cb5_17_2_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_17_3_ok : runP4s 17 2 2 2 none 12 [2, 7, 11] cb5_17_3_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_19_0_ok : runP4s 19 2 2 1 none 12 [2, 7, 11] cb5_19_0_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_19_1_ok : runP4s 19 2 2 1 none 12 [2, 7, 11] cb5_19_1_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_23_0_ok : runP4s 23 2 2 2 none 23 [2, 7, 11, 22] cb5_23_0_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_29_0_ok : runP4s 29 3 2 2 none 23 [2, 7, 11, 22] cb5_29_0_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_31_0_ok : runP4s 31 3 2 1 none 23 [2, 7, 11, 22] cb5_31_0_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_37_0_ok : runP4s 37 3 2 1 none 23 [2, 7, 11, 22] cb5_37_0_pairs = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cb5_41_0_ok : runP4s 41 3 2 2 none 23 [2, 7, 11, 22] cb5_41_0_pairs = true := by decide


def cb5_11_all : List (ℕ × ℕ) := cb5_11_0_pairs ++ cb5_11_1_pairs ++ cb5_11_2_pairs
lemma cb5_11_all_ok : runP4s 11 2 2 2 (some 2) 23 [2, 7, 22] cb5_11_all = true := by
  dsimp only [cb5_11_all, runP4s]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨cb5_11_0_ok, cb5_11_1_ok⟩, cb5_11_2_ok⟩
def cb5_13_all : List (ℕ × ℕ) := cb5_13_0_pairs ++ cb5_13_1_pairs ++ cb5_13_2_pairs ++ cb5_13_3_pairs ++ cb5_13_4_pairs ++ cb5_13_5_pairs
lemma cb5_13_all_ok : runP4s 13 2 2 1 (some 4) 12 [2, 7, 11] cb5_13_all = true := by
  dsimp only [cb5_13_all, runP4s]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨cb5_13_0_ok, cb5_13_1_ok⟩, cb5_13_2_ok⟩, cb5_13_3_ok⟩, cb5_13_4_ok⟩, cb5_13_5_ok⟩
def cb5_17_all : List (ℕ × ℕ) := cb5_17_0_pairs ++ cb5_17_1_pairs ++ cb5_17_2_pairs ++ cb5_17_3_pairs
lemma cb5_17_all_ok : runP4s 17 2 2 2 none 12 [2, 7, 11] cb5_17_all = true := by
  dsimp only [cb5_17_all, runP4s]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨cb5_17_0_ok, cb5_17_1_ok⟩, cb5_17_2_ok⟩, cb5_17_3_ok⟩
def cb5_19_all : List (ℕ × ℕ) := cb5_19_0_pairs ++ cb5_19_1_pairs
lemma cb5_19_all_ok : runP4s 19 2 2 1 none 12 [2, 7, 11] cb5_19_all = true := by
  dsimp only [cb5_19_all, runP4s]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨cb5_19_0_ok, cb5_19_1_ok⟩
def cb5_23_all : List (ℕ × ℕ) := cb5_23_0_pairs
lemma cb5_23_all_ok : runP4s 23 2 2 2 none 23 [2, 7, 11, 22] cb5_23_all = true := by
  dsimp only [cb5_23_all, runP4s]
  exact cb5_23_0_ok
def cb5_29_all : List (ℕ × ℕ) := cb5_29_0_pairs
lemma cb5_29_all_ok : runP4s 29 3 2 2 none 23 [2, 7, 11, 22] cb5_29_all = true := by
  dsimp only [cb5_29_all, runP4s]
  exact cb5_29_0_ok
def cb5_31_all : List (ℕ × ℕ) := cb5_31_0_pairs
lemma cb5_31_all_ok : runP4s 31 3 2 1 none 23 [2, 7, 11, 22] cb5_31_all = true := by
  dsimp only [cb5_31_all, runP4s]
  exact cb5_31_0_ok
def cb5_37_all : List (ℕ × ℕ) := cb5_37_0_pairs
lemma cb5_37_all_ok : runP4s 37 3 2 1 none 23 [2, 7, 11, 22] cb5_37_all = true := by
  dsimp only [cb5_37_all, runP4s]
  exact cb5_37_0_ok
def cb5_41_all : List (ℕ × ℕ) := cb5_41_0_pairs
lemma cb5_41_all_ok : runP4s 41 3 2 2 none 23 [2, 7, 11, 22] cb5_41_all = true := by
  dsimp only [cb5_41_all, runP4s]
  exact cb5_41_0_ok

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_11_13_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 11 1 none 1) (mkV 13 1 none 1) 17 none 7 [2, 5, 6] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_11_17_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 11 1 none 1) (mkV 17 1 none 1) 19 none 7 [2, 5, 6] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_11_19_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 11 1 none 1) (mkV 19 1 none 1) 23 none 7 [2, 5, 6] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_11_23_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 11 1 none 1) (mkV 23 1 none 1) 29 none 7 [2, 5, 6] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_11_29_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 11 1 none 1) (mkV 29 1 none 1) 31 none 27 [2, 5, 6, 26] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_11_31_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 11 1 none 1) (mkV 31 1 none 1) 37 none 27 [2, 5, 6, 26] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_11_37_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 11 1 none 1) (mkV 37 1 none 1) 41 none 27 [2, 5, 6, 26] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_11_41_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 11 1 none 1) (mkV 41 1 none 1) 43 none 27 [2, 5, 6, 26] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_11_43_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 11 1 none 1) (mkV 43 1 none 1) 47 none 27 [2, 5, 6, 26] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_11_47_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 11 1 none 1) (mkV 47 1 none 1) 53 none 27 [2, 5, 6, 26] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_13_17_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 13 1 none 1) (mkV 17 1 none 1) 19 none 16 [2, 5, 6, 15] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_13_19_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 13 1 none 1) (mkV 19 1 none 1) 23 none 19 [2, 5, 6, 15, 18] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_13_23_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 13 1 none 1) (mkV 23 1 none 1) 29 none 19 [2, 5, 6, 15, 18] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_13_29_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 13 1 none 1) (mkV 29 1 none 1) 31 none 28 [2, 5, 6, 15, 18, 27] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_13_31_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 13 1 none 1) (mkV 31 1 none 1) 37 none 37 [2, 5, 6, 15, 18, 27, 36] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_17_19_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 17 1 none 1) (mkV 19 1 none 1) 23 none 16 [2, 5, 6, 14, 15] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_17_23_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 17 1 none 1) (mkV 23 1 none 1) 29 none 16 [2, 5, 6, 14, 15] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_7_19_23_ok : checkBox 45 (mkV 3 2 none 1) (mkV 7 1 none 1) (mkV 19 1 none 1) (mkV 23 1 none 1) 29 none 19 [2, 5, 6, 14, 15, 18] false = true := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma cbNo5_11_13_17_ok : checkBox 45 (mkV 3 2 none 1) (mkV 11 1 none 1) (mkV 13 1 none 1) (mkV 17 1 none 1) 19 none 36 [2, 5, 6, 7, 8, 19, 35] false = true := by decide

-- Verify w3 witnesses & minimal covers
lemma w3Witnesses_ok :
    w3Witnesses.all (fun x =>
      let n := 3 ^ x.2.1 * 5 ^ x.2.2.1 * x.1 ^ x.2.2.2.1
      let sN := ppSum 3 x.2.1 * ppSum 5 x.2.2.1 * ppSum x.1 x.2.2.2.1
      checkWitness n sN x.2.2.2.2) = true := by decide

lemma w3Cover_7_ok :
    checkMinCover 20 (mkV 3 2 none 1) (mkV 5 1 none 1) (mkV 7 1 none 1) mkV1
      [(2,1,2,0), (2,2,1,0), (3,1,1,0)] = true := by decide

lemma w3Cover_11_ok :
    checkMinCover 20 (mkV 3 2 none 1) (mkV 5 1 none 1) (mkV 11 1 none 1) mkV1
      [(3,2,1,0)] = true := by decide

lemma w3Cover_13_ok :
    checkMinCover 25 (mkV 3 2 none 1) (mkV 5 1 none 1) (mkV 13 1 none 1) mkV1
      [(3,3,2,0), (4,2,2,0), (4,3,1,0), (5,2,1,0)] = true := by decide

-- Verify w4_no5 witnesses & minimal covers
set_option maxHeartbeats 2000000 in
lemma w4No5Witnesses_ok :
    w4No5Witnesses.all (fun x =>
      let (p2, p3, p4, a, b, c, d, wit) := x
      let n := 3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d
      let sN := ppSum 3 a * ppSum p2 b * ppSum p3 c * ppSum p4 d
      checkWitness n sN wit) = true := by decide

def w4No5Mins (p2 p3 p4 : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (w4No5Witnesses.filter (fun x => x.1 == p2 && x.2.1 == p3 && x.2.2.1 == p4)).map
    (fun x => (x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1))

set_option maxRecDepth 2048 in
lemma w4No5Covers_ok :
    [(7,11,13),(7,11,17),(7,11,19),(7,11,23),(7,13,17),(7,13,19)].all (fun t =>
      checkMinCover 30 (mkV 3 2 none 1) (mkV t.1 1 none 1) (mkV t.2.1 1 none 1) (mkV t.2.2 1 none 1)
        (w4No5Mins t.1 t.2.1 t.2.2)) = true := by decide

-- Verify all 17 bases3Data: checkCoreBadB, checkAbsGapListB(C=2), P0, large, no mod3 in bad, bestDiv, relGap5
set_option maxHeartbeats 4000000 in
lemma bases3Data_ok :
    bases3Data.all (fun x =>
      let (a0, b0, p3, L, g, P0, bad, ds, bestD, ds3p3, relN) := x
      let B0 := 3 ^ a0 * 5 ^ b0 * p3
      let sB0 := ppSum 3 a0 * ppSum 5 b0 * ppSum p3 1
      let u3p3 := 3 ^ a0 * p3
      let Pu3 := ppSum 3 a0 * ppSum p3 1 - u3p3
      decide (1 ≤ L ∧ g = 2 ∧ P0 + B0 = sB0 ∧ (2 * g + 1) * (2 * L + 8 * g + 8) ≤ P0 ∧
              B0 ≤ 2 * P0 ∧ p3 < bestD ∧ bestD ∣ (3 ^ a0 * 5 ^ b0) ∧
              2 * B0 * bestD ≤ sB0 * bestD + p3 * B0) &&
      bad.all (fun b => decide (b % 3 ≠ 0)) &&
      checkCoreBadB B0 L g P0 bad ds &&
      checkAbsGapListB B0 2 P0 ds &&
      (if b0 == 2 then
        checkRelGapListB u3p3 relN 1000 Pu3 ds3p3 &&
        decide (1000 * (2 * u3p3 - (Pu3 + u3p3)) ≤ 3 * relN * u3p3 ∧
                1000 * (2 * L + 1) + 125 * relN * u3p3 ≤ 1000 * (31 * (Pu3 + u3p3) - 25 * u3p3 + 1) ∧
                2 * L + 25 * u3p3 ≤ (31 * (Pu3 + u3p3) - 25 * u3p3) + 125 * Pu3 + 1)
       else true)) = true := by decide

-- Verify 10 bases315Data (315 * p4 for p4 in 157..199)
set_option maxHeartbeats 4000000 in
lemma bases315Data_ok :
    bases315Data.all (fun x =>
      let (p4, L, g, P0, bad, ds) := x
      let B0 := 315 * p4
      let sB0 := 624 * (p4 + 1)
      decide (L = 3 ∧ g = 2 ∧ P0 + B0 = sB0 ∧ (2 * g + 1) * (2 * L + 8 * g + 8) ≤ P0 ∧ bad = [2]) &&
      checkCoreBadB B0 L g P0 bad ds) = true := by decide

-- Verify 45 * 17 * 19
set_option maxHeartbeats 2000000 in
lemma base45_17_19_ok :
    (checkCoreBadB (45 * 17 * 19) 12 2 13545 [2, 7, 11] ds_45_17_19 &&
     checkAbsGapListB (45 * 19) 2 (78 * 20 - 45 * 19) ds_45_19 &&
     checkAbsGapListB (45 * 17) 2 (78 * 18 - 45 * 17) ds_45_17) = true := by decide

-- Verify all 19 basesNo5Data
set_option maxHeartbeats 4000000 in
lemma basesNo5Data_ok :
    basesNo5Data.all (fun x =>
      let (p2, p3, p4, q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4) := x
      let B0 := 9 * p2 * p3 * p4
      let sB0 := 13 * (p2 + 1) * (p3 + 1) * (p4 + 1)
      let u2 := 9 * p3 * p4; let s2 := 13 * (p3 + 1) * (p4 + 1); let P2 := s2 - u2
      let u3 := 9 * p2 * p4; let s3 := 13 * (p2 + 1) * (p4 + 1); let P3 := s3 - u3
      let u4 := 9 * p2 * p3; let s4 := 13 * (p2 + 1) * (p3 + 1); let P4 := s4 - u4
      let dp2_3 := if p2 == 7 then 9 else p4
      let dp2_4 := if p2 == 7 then 9 else p3
      decide (1 ≤ L ∧ 1 ≤ g ∧ P0 + B0 = sB0 ∧ (2 * g + 1) * (2 * L + 8 * g + 8) ≤ P0 ∧
              -- Step 1 (lift 3): p2 * d <= u => check 2L + 27 * (u/p2) <= P(9*u) + 1
              p2 * (2 * L) + 27 * (p2 * p3 * p4) ≤ p2 * (P0 + 1) ∧
              2 * L + B0 ≤ P0 + 27 * ((p2 + 1) * (p3 + 1) * (p4 + 1) - p2 * p3 * p4) + 1 ∧
              -- Step 2 (lift p2): a2/1000 budget + grow 3 (extra d1=p3)
              1000 * (2 * L) + p2 * p2 * a2 * u2 ≤ 1000 * (P0 + 1) ∧
              2 * L + B0 ≤ P0 + p2 * p2 * P2 + 1 ∧
              1000 * (2 * u2 * p3) ≤ 1000 * (s2 * p3 + 3 * u2) + 3 * a2 * u2 * p3 ∧
              -- Step 3 (lift p3): a3/1000 budget + grow 3 (d1=p2) + grow p2 (d1=dp2_3)
              1000 * (2 * L) + p3 * p3 * a3 * u3 ≤ 1000 * (P0 + 1) ∧
              2 * L + B0 ≤ P0 + p3 * p3 * P3 + 1 ∧
              1000 * (2 * u3 * p2) ≤ 1000 * (s3 * p2 + 3 * u3) + 3 * a3 * u3 * p2 ∧
              1000 * (2 * u3 * dp2_3) ≤ 1000 * (s3 * dp2_3 + p2 * u3) + p2 * a3 * u3 * dp2_3 ∧
              -- Step 4 (lift p4): a4/1000 budget + grow 3 (d1=p2) + grow p2 (d1=dp2_4) + grow p3 (d1=3*p2)
              1000 * (2 * L) + p4 * p4 * a4 * u4 ≤ 1000 * (P0 + 1) ∧
              2 * L + B0 ≤ P0 + p4 * p4 * P4 + 1 ∧
              1000 * (2 * u4 * p2) ≤ 1000 * (s4 * p2 + 3 * u4) + 3 * a4 * u4 * p2 ∧
              1000 * (2 * u4 * dp2_4) ≤ 1000 * (s4 * dp2_4 + p2 * u4) + p2 * a4 * u4 * dp2_4 ∧
              1000 * (2 * u4 * (3 * p2)) ≤ 1000 * (s4 * (3 * p2) + p3 * u4) + p3 * a4 * u4 * (3 * p2)) &&
      checkCoreBadB B0 L g P0 bad ds &&
      checkRelGapListB u2 a2 1000 P2 ds2 &&
      checkRelGapListB u3 a3 1000 P3 ds3 &&
      checkRelGapListB u4 a4 1000 P4 ds4) = true := by decide

-- Verify D >= 2 for all odd squares (omega=3, omega=4 5 nmid B, omega=4 5 | B)
set_option maxRecDepth 2048 in
lemma dge2_no5_ok :
    [(7,11,13),(7,11,17),(7,11,19),(7,11,23),(7,13,17),(7,13,19)].all (fun t =>
      checkDge2 30 (mkV 3 2 none 2) (mkV t.1 2 none 2) (mkV t.2.1 2 none 2) (mkV t.2.2 2 none 2)) = true := by
  decide

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
lemma dge2_5_ok :
    dge2Pairs5.all (fun t =>
      let h1 := if t.2.2 == 0 then none else some t.2.2
      checkDge2 30 (mkV 3 2 h1 2) (mkV 5 2 none 2) (mkV t.1 2 none 2) (mkV t.2.1 2 none 2)) = true := by
  decide

-- Verify CheckBox for omega = 4, 5 | m, b even (6 primes p3 in (11, 13, 17, 19, 23, 29))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma cb4_5_ok :
    [(11, 13, 2, some 2, 2, 2, 23, [2, 7, 22]),
     (13, 17, 2, some 4, 1, 1, 12, [2, 7, 11]),
     (17, 19, 2, none,   2, 2, 12, [2, 7, 11]),
     (19, 23, 2, none,   1, 1, 12, [2, 7, 11]),
     (23, 29, 2, none,   2, 2, 23, [2, 7, 11, 22]),
     (29, 31, 3, none,   2, 2, 23, [2, 7, 11, 22])].all (fun t =>
      let (p3, q0, l1, h1, l3, s3, L, bad) := t
      checkBox 45 (mkV 3 l1 h1 1) (mkV 5 2 none 2) (mkV p3 l3 none s3) mkV1 q0 none L bad true) = true := by
  decide

-- Verify HasAbsGap 45 2 and HasAbsGap 315 2
lemma hasAbsGap_45 : HasAbsGap 45 2 :=
  hasAbsGap_of_list (by decide) (by decide) (by decide : checkAbsGapListB 45 2 33 [1, 3, 5, 9, 15] = true)

lemma hasAbsGap_315 : HasAbsGap 315 2 :=
  hasAbsGap_of_list (by decide) (by decide)
    (by decide : checkAbsGapListB 315 2 309 [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105] = true)

end DataAndDecide

section LiftsAndDGe2

lemma apply_final_prime_or_bad {B q e L g : ℕ} {bad : List ℕ}
    (hBgt1 : 1 < B) (hq : q.Prime) (hcop : B.Coprime q) (hq3 : 3 ≤ q) (he : 1 ≤ e)
    (hL : 1 ≤ L) (hg : 1 ≤ g)
    (hab : (B * q ^ e).Abundant)
    (hprim : ∀ d ∈ (B * q ^ e).properDivisors, d.Deficient)
    (hD2 : 2 ≤ 2 * B - sigma 1 B)
    (hbig : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ properDivsSum B)
    (hcov : ∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y)
    (hgap : ∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + g ∧ i ≤ k)
    (hbad : ∀ x, x < L → x ∉ bad → repNat B.properDivisors x)
    (hEok : L ≤ sigma 1 (B * q ^ e) - 2 * (B * q ^ e) ∨
            (sigma 1 (B * q ^ e) - 2 * (B * q ^ e)) ∉ bad) :
    (B * q ^ e).Pseudoperfect := by
  let m := B * q ^ e
  have hBpos : 0 < B := by omega
  have hmpos : 0 < m := by have := hq.pos; dsimp [m]; positivity
  let En := sigma 1 m - 2 * m
  have hab_nat : 2 * m < sigma 1 m := (abund_iff_nat hmpos).mp hab
  have hEn_eq : (En : ℤ) = excess m := by dsimp [En, excess]; omega
  by_cases hEL : L ≤ En
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    have hP_cast : properTotal B = (properDivsSum B : ℤ) := by simp [properTotal, properDivsSum]
    have hsimpleD : 2 ≤ (B : ℤ) - properTotal B := by
      have : (B : ℤ) - properTotal B = 2 * (B : ℤ) - (sigma 1 B : ℤ) := by rw [sigma_split B]; ring
      have hBdef : sigma 1 B < 2 * B := by
        have hmem : B ∈ (B * q ^ (j + 1)).properDivisors := Nat.mem_properDivisors.mpr
          ⟨dvd_mul_right B _, by simpa using Nat.mul_lt_mul_of_pos_left (one_lt_pow₀ hq.one_lt (by omega)) hBpos⟩
        exact (defic_iff_nat hBpos).mp (hprim B hmem)
      omega
    exact certified_prime_power_gen hBgt1 hq hcop hq3 hprim (L : ℤ) (g : ℤ)
      (by exact_mod_cast hL) (by exact_mod_cast hg)
      (by rw [← hEn_eq]; exact_mod_cast hEL)
      (by rw [hP_cast]; exact_mod_cast hbig)
      (fun _ => hsimpleD)
      (fun y hy1 hy2 => by
        lift y to ℕ using (by omega)
        rw [hP_cast] at hy2
        exact repNat_to_represented (hcov y (by exact_mod_cast hy1) (by omega)))
      (fun k hk1 hk2 => by
        lift k to ℕ using hk1
        rw [hP_cast] at hk2
        obtain ⟨i, hi, hi1, hi2⟩ := hgap k (by exact_mod_cast hk2)
        exact ⟨(i : ℤ), repNat_to_represented hi, by omega, by omega⟩)
  · have hnot : En ∉ bad := hEok.resolve_left hEL
    obtain ⟨s, hs, hsum⟩ := hbad En (by omega) hnot
    have hs_m : s ⊆ m.properDivisors := by
      intro x hx
      obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp (hs hx)
      exact Nat.mem_properDivisors.mpr ⟨h1.trans (dvd_mul_right B (q ^ e)),
        lt_of_lt_of_le h2 (Nat.le_of_dvd hmpos (dvd_mul_right B (q ^ e)))⟩
    exact pseudoperfect_of_excess hmpos hs_m (by rw [← hEn_eq, ← hsum]; simp)

lemma extra_div_sum_ge {u p ex : ℕ} (hp : p.Prime)
    (hex_dvd : ex ∣ p * u) (hex_lt : ex < u) (hex_not : ¬ ex ∣ u) :
    ex + properDivsSum u ≤ ∑ x ∈ (p * u).properDivisors.filter (· < u), x := by
  have hsub : insert ex u.properDivisors ⊆ (p * u).properDivisors.filter (· < u) := by
    intro x hx
    rw [Finset.mem_filter]
    rcases Finset.mem_insert.mp hx with rfl | hxu
    · exact ⟨Nat.mem_properDivisors.mpr ⟨hex_dvd, lt_trans hex_lt (by nlinarith [hp.one_lt])⟩, hex_lt⟩
    · obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp hxu
      exact ⟨Nat.mem_properDivisors.mpr ⟨h1.trans (dvd_mul_left u p), lt_trans h2 (by nlinarith [hp.one_lt])⟩, h2⟩
  have hex_notin : ex ∉ u.properDivisors := fun h => hex_not (Nat.mem_properDivisors.mp h).1
  have := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
  rw [Finset.sum_insert hex_notin] at this
  exact this

lemma small_sum_ge_coprime {u p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hu : 0 < u)
    (hd' : ℕ) (hd'_mem : hd' ∈ u.properDivisors) (hpd' : p ∣ hd')
    (hS : ∀ x ∈ S, x ∣ u ∧ x < p * p ∧ ¬ p ∣ x) :
    ∑ x ∈ S, x ≤ ∑ x ∈ (p * u).properDivisors.filter (fun x => x < p * hd' ∧ ¬ p ∣ x), x := by
  have hpd'_ge : p * p ≤ p * hd' := by
    obtain ⟨t, rfl⟩ := hpd'
    have hpos := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hd'_mem).1 hu
    have ht : 1 ≤ t := by by_contra! h0; have : t = 0 := (by omega); subst this; simp at hpos
    nlinarith
  have hpu_gt : p * hd' < p * u := Nat.mul_lt_mul_of_pos_left (Nat.mem_properDivisors.mp hd'_mem).2 hp.pos
  apply Finset.sum_le_sum_of_subset (f := fun x => x)
  intro x hx
  obtain ⟨hxu, hxlt, hxnp⟩ := hS x hx
  rw [Finset.mem_filter, Nat.mem_properDivisors]
  exact ⟨⟨hxu.trans (dvd_mul_left u p), by omega⟩, by omega, hxnp⟩

lemma hasAbsGap_3_5 {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b) : HasAbsGap (3 ^ a * 5 ^ b) 2 := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have hbase_b : ∀ b', 1 ≤ b' → HasAbsGap (3 ^ 2 * 5 ^ b') 2 := by
    intro b' hb'
    induction b' with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hasAbsGap_45
      | succ k' =>
        have hprev := ih (by omega)
        let u := 3 ^ 2 * 5 ^ (k' + 1)
        have hu_pos : 0 < u := by positivity
        have h5u : 5 ∣ u := dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) _
        rw [show 3 ^ 2 * 5 ^ (k' + 2) = 5 * u by dsimp [u]; ring]
        apply HasAbsGap.mul_prime h5p hu_pos h5u hprev
        · let ex := 5 ^ (k' + 2)
          have hex_dvd : ex ∣ 5 * u := ⟨9, by dsimp [ex, u]; ring⟩
          have hex_lt : ex < u := by dsimp [ex, u]; rw [pow_succ]; have : 0 < 5 ^ (k' + 1) := (by positivity); nlinarith
          have hex_not : ¬ ex ∣ u := by
            intro h
            have h1 : 5 ^ (k' + 2) ∣ 9 * 5 ^ (k' + 1) := by simpa [u] using h
            rw [show 5 ^ (k' + 2) = 5 * 5 ^ (k' + 1) by ring] at h1
            have : 5 ∣ 9 := (Nat.mul_dvd_mul_iff_right (by positivity : 0 < 5 ^ (k' + 1))).mp h1
            omega
          have hsum := extra_div_sum_ge h5p hex_dvd hex_lt hex_not
          have hsig : sigma 1 u = 13 * ppSum 5 (k' + 1) := by
            have h := sigma_mul_coprime_three h3p h5p (by decide : Nat.Prime 7) (by decide) (by decide)
              (a := 2) (b := k' + 1) (c := 0)
            simp only [pow_zero, mul_one, ppSum_zero (by decide : 2 ≤ 7)] at h
            rw [h]; rfl
          have hP : properDivsSum u = 13 * ppSum 5 (k' + 1) - u := by rw [properDivsSum_eq_sigma_sub, hsig]
          have h5m := ppSum_mono_exp (p := 5) (by decide) (show 1 ≤ k' + 1 by omega)
          have h5_1 : ppSum 5 1 = 6 := by decide
          rw [h5_1, pow_one] at h5m
          have hP_ge : 33 * 5 ^ k' ≤ properDivsSum u := by dsimp [u] at hP ⊢; omega
          have : ex = 25 * 5 ^ k' := by dsimp [ex]; ring
          have : u = 45 * 5 ^ k' := by dsimp [u]; ring
          omega
        · intro d' hd' h5d'
          have hle := small_sum_ge_coprime h5p hu_pos d' hd' h5d' (S := {1, 3, 9}) (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact ⟨one_dvd _, by decide, by decide⟩
            · exact ⟨(by decide : 3 ∣ 9).trans (dvd_mul_right _ _), by decide, by decide⟩
            · exact ⟨dvd_mul_right _ _, by decide, by decide⟩)
          have hs : ∑ x ∈ ({1, 3, 9} : Finset ℕ), x = 13 := by decide
          omega
  induction a with
  | zero => omega
  | succ k ih =>
    by_cases hk : k < 2
    · have : k + 1 = 2 := by omega
      rw [this]; exact hbase_b b hb
    · have hprev := ih (by omega)
      let u := 3 ^ k * 5 ^ b
      have hu_pos : 0 < u := by positivity
      have h3u : 3 ∣ u := dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _
      rw [show 3 ^ (k + 1) * 5 ^ b = 3 * u by dsimp [u]; ring]
      apply HasAbsGap.mul_prime h3p hu_pos h3u hprev
      · let ex := 3 ^ (k + 1) * 5 ^ (b - 1)
        have h5b : 5 ^ b = 5 * 5 ^ (b - 1) := by rw [← pow_succ', Nat.sub_add_cancel hb]
        have hex_dvd : ex ∣ 3 * u := ⟨5, by dsimp [ex, u]; rw [h5b]; ring⟩
        have hex_lt : ex < u := by
          dsimp [ex, u]; rw [h5b, pow_succ]
          have : 0 < 3 ^ k * 5 ^ (b - 1) := (by positivity); nlinarith
        have hex_not : ¬ ex ∣ u := by
          intro h
          have h1 : 3 ^ (k + 1) ∣ 3 ^ k * 5 ^ b := (dvd_mul_right _ _).trans h
          rw [pow_succ'] at h1
          have : 3 ∣ 5 ^ b := by
            have h2 := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 3 ^ k)).mp
              (by simpa [mul_comm (3 ^ k), mul_assoc] using h1)
            exact h2
          exact (by decide : Nat.Coprime 3 5).pow_right b |>.symm |> fun hc =>
            h3p.not_dvd_one (hc.symm.dvd_of_dvd_mul_right (by simpa using this))
        have hsum := extra_div_sum_ge h3p hex_dvd hex_lt hex_not
        have hsig : sigma 1 u = ppSum 3 k * ppSum 5 b := by
          have h := sigma_mul_coprime_three h3p h5p (by decide : Nat.Prime 7) (by decide) (by decide)
            (a := k) (b := b) (c := 0)
          simp only [pow_zero, mul_one, ppSum_zero (by decide : 2 ≤ 7)] at h
          exact h
        have h3m := ppSum_mono_exp (p := 3) (by decide) (show 2 ≤ k by omega)
        have h5m := ppSum_mono_exp (p := 5) (by decide) hb
        have h3_2 : ppSum 3 2 = 13 := by decide
        have h5_1 : ppSum 5 1 = 6 := by decide
        rw [h3_2] at h3m; rw [h5_1, pow_one] at h5m
        have hm := Nat.mul_le_mul h3m h5m
        have hP : properDivsSum u = ppSum 3 k * ppSum 5 b - u := by rw [properDivsSum_eq_sigma_sub, hsig]
        have : 5 * ex = 3 * u := by dsimp [ex, u]; rw [h5b]; ring
        have hu_le : u ≤ ppSum 3 k * ppSum 5 b := by
          rw [← hsig, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
        have : 45 * (ex + properDivsSum u) ≥ 45 * u := by
          have h78 : 45 * (ppSum 3 k * ppSum 5 b) ≥ 78 * u := by dsimp [u]; linarith
          rw [hP, mul_add, Nat.mul_sub]; omega
        omega
      · intro d' hd' h3d'
        have hle := small_sum_ge_coprime h3p hu_pos d' hd' h3d' (S := {1, 5}) (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨one_dvd _, by decide, by decide⟩
          · exact ⟨dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) _, by decide, by decide⟩)
        have hs : ∑ x ∈ ({1, 5} : Finset ℕ), x = 6 := by decide
        omega

-- Lift HasAbsGap C=2 from a bases3Data entry to 3^a * 5^b * p3^c.
set_option maxHeartbeats 1600000 in
lemma hasAbsGap_base3 {a0 b0 p3 L g P0 bestD relN a b c : ℕ} {bad ds ds3p3 : List ℕ}
    (hmem : (a0, b0, p3, L, g, P0, bad, ds, bestD, ds3p3, relN) ∈ bases3Data)
    (hp3 : p3.Prime) (hp3_gt5 : 5 < p3) (ha0 : 2 ≤ a0) (hb0 : 1 ≤ b0)
    (ha : a0 ≤ a) (hb : b0 ≤ b) (hc : 1 ≤ c) :
    HasAbsGap (3 ^ a * 5 ^ b * p3 ^ c) 2 := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have hok := List.all_eq_true.mp bases3Data_ok _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hmeta, _⟩, _⟩, habs0⟩, _⟩ := hok
  obtain ⟨_, _, hP0_eq, _, _, hbd_gt, hbd_dvd, hbd_ineq⟩ := hmeta
  let B0 := 3 ^ a0 * 5 ^ b0 * p3
  have hB0_pos : 0 < B0 := by have := hp3.pos; dsimp [B0]; positivity
  have hsB0 : sigma 1 B0 = ppSum 3 a0 * ppSum 5 b0 * ppSum p3 1 := by
    simpa [B0, pow_one] using sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a0) (b := b0) (c := 1)
  have hP0_eq' : P0 = properDivsSum B0 := by
    rw [properDivsSum_eq_sigma_sub, hsB0]; omega
  have hbase : HasAbsGap B0 2 := hasAbsGap_of_list hB0_pos hP0_eq' habs0
  -- First lift a: 3^a * 5^b0 * p3
  have hlift_a : ∀ a', a0 ≤ a' → HasAbsGap (3 ^ a' * 5 ^ b0 * p3) 2 := by
    intro a' ha'
    induction a' with
    | zero => omega
    | succ k ih =>
      by_cases hk : k < a0
      · have : k + 1 = a0 := by omega
        rw [this]; exact hbase
      · have hprev := ih (by omega)
        let u := 3 ^ k * 5 ^ b0 * p3
        have hu_pos : 0 < u := by have := hp3.pos; dsimp [u]; positivity
        have h3u : 3 ∣ u := (dvd_pow_self 3 (by omega)).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
        rw [show 3 ^ (k + 1) * 5 ^ b0 * p3 = 3 * u by dsimp [u]; ring]
        apply HasAbsGap.mul_prime h3p hu_pos h3u hprev
        · let ex := 3 ^ (k + 1) * 5 ^ (b0 - 1) * p3
          have h5b : 5 ^ b0 = 5 * 5 ^ (b0 - 1) := by rw [← pow_succ', Nat.sub_add_cancel hb0]
          have hex_dvd : ex ∣ 3 * u := ⟨5, by dsimp [ex, u]; rw [h5b]; ring⟩
          have hex_lt : ex < u := by
            dsimp [ex, u]; rw [h5b, pow_succ]
            have : 0 < 3 ^ k * 5 ^ (b0 - 1) * p3 := by have := hp3.pos; positivity
            nlinarith
          have hex_not : ¬ ex ∣ u := by
            intro h
            have h1 : 3 ^ (k + 1) ∣ 3 ^ k * (5 ^ b0 * p3) := by
              have := (dvd_mul_right (3 ^ (k + 1)) (5 ^ (b0 - 1))).trans ((dvd_mul_right _ p3).trans h)
              simpa [u, mul_assoc] using this
            rw [pow_succ] at h1
            have h2 : 3 ∣ 5 ^ b0 * p3 := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 3 ^ k)).mp
              (by simpa [mul_assoc] using h1)
            have hcop : Nat.Coprime 3 (5 ^ b0 * p3) :=
              Nat.Coprime.mul_right ((by decide : Nat.Coprime 3 5).pow_right b0)
                ((Nat.coprime_primes h3p hp3).mpr (by omega))
            exact h3p.not_dvd_one (hcop.dvd_of_dvd_mul_right (by simpa using h2))
          have hsum := extra_div_sum_ge h3p hex_dvd hex_lt hex_not
          have hratio := properDivsSum_ratio_mono_3p h3p h5p hp3 (by decide) hp3_gt5 (b0 := b0) (c0 := 1) (show a0 ≤ k by omega) le_rfl le_rfl
          simp only [pow_one] at hratio
          have hB0_le : 45 * properDivsSum B0 ≥ 33 * B0 := by
            have h3m := ppSum_mono_exp (p := 3) (by decide) ha0
            have h5m := ppSum_mono_exp (p := 5) (by decide) hb0
            have hp3m : p3 ≤ ppSum p3 1 := by rw [ppSum_one hp3.two_le]; omega
            have h32 : ppSum 3 2 = 13 := by decide
            have h51 : ppSum 5 1 = 6 := by decide
            rw [h32] at h3m; rw [h51, pow_one] at h5m
            have h12 := Nat.mul_le_mul h3m h5m
            have h123 := Nat.mul_le_mul h12 hp3m
            have : 45 * sigma 1 B0 ≥ 78 * B0 := by rw [hsB0]; dsimp [B0]; linarith
            rw [properDivsSum_eq_sigma_sub]; omega
          have hu_P : 45 * properDivsSum u ≥ 33 * u := by
            have : 45 * properDivsSum u * B0 ≥ 33 * u * B0 := by
              have h1 : 33 * B0 * u ≤ 45 * properDivsSum B0 * u := Nat.mul_le_mul_right u hB0_le
              have h2 : 45 * (properDivsSum B0 * u) ≤ 45 * (properDivsSum u * B0) := Nat.mul_le_mul_left 45 hratio
              linarith
            exact Nat.le_of_mul_le_mul_right this hB0_pos
          have : 5 * ex = 3 * u := by dsimp [ex, u]; rw [h5b]; ring
          omega
        · intro d' hd' h3d'
          have hle := small_sum_ge_coprime h3p hu_pos d' hd' h3d' (S := {1, 5}) (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact ⟨one_dvd _, by decide, by decide⟩
            · exact ⟨(dvd_pow_self 5 (by omega)).trans ((dvd_mul_left _ _).trans (dvd_mul_right _ _)), by decide, by decide⟩)
          have hs : ∑ x ∈ ({1, 5} : Finset ℕ), x = 6 := by decide
          omega
  -- Second lift b: 3^a * 5^b * p3
  have hlift_b : ∀ b', b0 ≤ b' → HasAbsGap (3 ^ a * 5 ^ b' * p3) 2 := by
    intro b' hb'
    induction b' with
    | zero => omega
    | succ k ih =>
      by_cases hk : k < b0
      · have : k + 1 = b0 := by omega
        rw [this]; exact hlift_a a ha
      · have hprev := ih (by omega)
        let u := 3 ^ a * 5 ^ k * p3
        have hu_pos : 0 < u := by have := hp3.pos; dsimp [u]; positivity
        have h5u : 5 ∣ u := (dvd_pow_self 5 (by omega)).trans ((dvd_mul_left _ _).trans (dvd_mul_right _ _))
        rw [show 3 ^ a * 5 ^ (k + 1) * p3 = 5 * u by dsimp [u]; ring]
        apply HasAbsGap.mul_prime h5p hu_pos h5u hprev
        · let ex := 3 ^ (a - 2) * 5 ^ (k + 1) * p3
          have h3a : 3 ^ a = 9 * 3 ^ (a - 2) := by
            have : 2 ≤ a := by omega
            calc 3 ^ a = 3 ^ (2 + (a - 2)) := by congr 1; omega
              _ = 9 * 3 ^ (a - 2) := by rw [pow_add]; norm_num
          have hex_dvd : ex ∣ 5 * u := ⟨9, by dsimp [ex, u]; rw [h3a]; ring⟩
          have hex_lt : ex < u := by
            dsimp [ex, u]; rw [h3a, pow_succ]
            have : 0 < 3 ^ (a - 2) * 5 ^ k * p3 := by have := hp3.pos; positivity
            nlinarith
          have hex_not : ¬ ex ∣ u := by
            intro h
            have h1 : 5 ^ (k + 1) ∣ 5 ^ k * (3 ^ a * p3) := by
              have := (dvd_mul_left (5 ^ (k + 1)) (3 ^ (a - 2))).trans ((dvd_mul_right _ p3).trans h)
              simpa [u, mul_comm, mul_left_comm, mul_assoc] using this
            rw [pow_succ] at h1
            have h2 : 5 ∣ 3 ^ a * p3 := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 5 ^ k)).mp
              (by simpa [mul_assoc] using h1)
            have hcop : Nat.Coprime 5 (3 ^ a * p3) :=
              Nat.Coprime.mul_right ((by decide : Nat.Coprime 5 3).pow_right a)
                ((Nat.coprime_primes h5p hp3).mpr (by omega))
            exact h5p.not_dvd_one (hcop.dvd_of_dvd_mul_right (by simpa using h2))
          have hsum := extra_div_sum_ge h5p hex_dvd hex_lt hex_not
          have hratio := properDivsSum_ratio_mono_3p h3p h5p hp3 (by decide) hp3_gt5 (c0 := 1) ha (show b0 ≤ k by omega) le_rfl
          simp only [pow_one] at hratio
          have hu_P : 45 * properDivsSum u ≥ 33 * u := by
            have h3m := ppSum_mono_exp (p := 3) (by decide) (show 2 ≤ a by omega)
            have h5m := ppSum_mono_exp (p := 5) (by decide) (show 1 ≤ k by omega)
            have hp3m : p3 ≤ ppSum p3 1 := by rw [ppSum_one hp3.two_le]; omega
            have h32 : ppSum 3 2 = 13 := by decide
            have h51 : ppSum 5 1 = 6 := by decide
            rw [h32] at h3m; rw [h51, pow_one] at h5m
            have h123 := Nat.mul_le_mul (Nat.mul_le_mul h3m h5m) hp3m
            have hsig : sigma 1 u = ppSum 3 a * ppSum 5 k * ppSum p3 1 := by
              simpa [u, pow_one] using sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a) (b := k) (c := 1)
            have h78 : 45 * (ppSum 3 a * ppSum 5 k * ppSum p3 1) ≥ 78 * u := by dsimp [u]; linarith
            rw [properDivsSum_eq_sigma_sub, hsig]; omega
          have : 9 * ex = 5 * u := by dsimp [ex, u]; rw [h3a]; ring
          omega
        · intro d' hd' h5d'
          have h9 : 9 ∣ 3 ^ a := by have := pow_dvd_pow 3 (show 2 ≤ a by omega); norm_num at this; exact this
          have h9u : 9 ∣ u := h9.trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
          have hle := small_sum_ge_coprime h5p hu_pos d' hd' h5d' (S := {1, 3, 9}) (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact ⟨one_dvd _, by decide, by decide⟩
            · exact ⟨(by decide : 3 ∣ 9).trans h9u, by decide, by decide⟩
            · exact ⟨h9u, by decide, by decide⟩)
          have hs : ∑ x ∈ ({1, 3, 9} : Finset ℕ), x = 13 := by decide
          omega
  -- Third lift c: 3^a * 5^b * p3^c
  induction c with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simpa using hlift_b b hb
    | succ k' =>
      have hprev := ih (by omega)
      let u := 3 ^ a * 5 ^ b * p3 ^ (k' + 1)
      have hu_pos : 0 < u := by have := hp3.pos; dsimp [u]; positivity
      have hpu : p3 ∣ u := dvd_mul_of_dvd_right (dvd_pow_self p3 (by omega)) _
      rw [show 3 ^ a * 5 ^ b * p3 ^ (k' + 2) = p3 * u by dsimp [u]; ring]
      apply HasAbsGap.mul_prime hp3 hu_pos hpu hprev
      · obtain ⟨q0, hq0⟩ := hbd_dvd
        have hbd_pos : 0 < bestD := by omega
        have h35_dvd : 3 ^ a0 * 5 ^ b0 ∣ 3 ^ a * 5 ^ b :=
          Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow 5 hb)
        obtain ⟨q1, hq1⟩ := h35_dvd
        let ex := (q0 * q1) * p3 ^ (k' + 2)
        have hmul_ex : bestD * ex = p3 * u := by
          dsimp only [ex, u]
          have : 3 ^ a * 5 ^ b = bestD * (q0 * q1) := by rw [hq1, hq0]; ring
          rw [this]; ring
        have hex_dvd : ex ∣ p3 * u := ⟨bestD, by rw [mul_comm ex bestD, hmul_ex]⟩
        have hex_lt : ex < u := by nlinarith
        have hex_not : ¬ ex ∣ u := by
          intro h
          have h1 : p3 ^ (k' + 2) ∣ (3 ^ a * 5 ^ b) * p3 ^ (k' + 1) := (dvd_mul_left _ _).trans h
          rw [show p3 ^ (k' + 2) = p3 * p3 ^ (k' + 1) by ring] at h1
          have h2 : p3 ∣ 3 ^ a * 5 ^ b := (Nat.mul_dvd_mul_iff_right (pow_pos hp3.pos _)).mp h1
          have hcop : Nat.Coprime p3 (3 ^ a * 5 ^ b) :=
            Nat.Coprime.mul_right (((Nat.coprime_primes hp3 h3p).mpr (by omega)).pow_right a)
              (((Nat.coprime_primes hp3 h5p).mpr (by omega)).pow_right b)
          exact hp3.not_dvd_one (hcop.dvd_of_dvd_mul_right (by simpa using h2))
        have hsum := extra_div_sum_ge hp3 hex_dvd hex_lt hex_not
        have hratio := properDivsSum_ratio_mono_3p h3p h5p hp3 (by decide) hp3_gt5 ha hb (show 1 ≤ k' + 1 by omega)
        simp only [pow_one] at hratio
        have hB0_ineq : u * bestD ≤ properDivsSum u * bestD + p3 * u := by
          have h1 : B0 * bestD ≤ properDivsSum B0 * bestD + p3 * B0 := by
            rw [properDivsSum_eq_sigma_sub, hsB0]
            have hleB0 : B0 ≤ ppSum 3 a0 * ppSum 5 b0 * ppSum p3 1 := by
              rw [← hsB0, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
            have : B0 * bestD ≤ ppSum 3 a0 * ppSum 5 b0 * ppSum p3 1 * bestD := Nat.mul_le_mul_right bestD hleB0
            have h2mul : 2 * (3 ^ a0 * 5 ^ b0 * p3) * bestD = 2 * ((3 ^ a0 * 5 ^ b0 * p3) * bestD) := by ring
            rw [Nat.sub_mul]; dsimp only [B0] at hbd_ineq ⊢; rw [h2mul] at hbd_ineq; omega
          have h2 : B0 * bestD * u ≤ properDivsSum B0 * bestD * u + p3 * B0 * u := by
            have := Nat.mul_le_mul_right u h1; linarith
          have h3 : properDivsSum B0 * u * bestD ≤ properDivsSum u * B0 * bestD :=
            Nat.mul_le_mul_right bestD hratio
          have h4 : (u * bestD) * B0 ≤ (properDivsSum u * bestD + p3 * u) * B0 := by linarith
          exact Nat.le_of_mul_le_mul_right h4 hB0_pos
        have : bestD * (ex + properDivsSum u) = p3 * u + properDivsSum u * bestD := by
          rw [mul_add, hmul_ex, mul_comm bestD]
        have : u ≤ ex + properDivsSum u := Nat.le_of_mul_le_mul_left (by linarith) hbd_pos
        omega
      · intro d' hd' hpd'
        -- 45 | 3^a * 5^b | u (and for p3 >= 29, 675 | u!). Just check 2 * p3 <= 2 + sum_{x in S} x!
        -- Wait: 45 has {1, 3, 5, 9, 15, 45} summing to 78 >= 2*37 + 2 = 76!
        -- For p3 = 7: {1, 3, 5, 9, 15, 45} all < 49, sum = 78 >= 14!
        -- For p3 = 41: a0 = 3, b0 = 2 so 675 | u, {1, 3, 5, 9, 15, 25, 45} all < 49 <= p3^2, sum = 103 >= 82!
        have h45_u : 45 ∣ u := by
          have h9 : 9 ∣ 3 ^ a := by have := pow_dvd_pow 3 (show 2 ≤ a by omega); norm_num at this; exact this
          have h5 : 5 ∣ 5 ^ b := dvd_pow_self 5 (by omega)
          exact (Nat.mul_dvd_mul h9 h5).trans (dvd_mul_right _ _)
        have hnp3 : ¬ p3 ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
        have hnp5 : ¬ p3 ∣ 5 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
        have hnp45 : ¬ p3 ∣ 45 := fun h => by
          rcases hp3.dvd_mul.mp (show p3 ∣ 9 * 5 from h) with h1 | h2
          · rcases hp3.dvd_mul.mp (show p3 ∣ 3 * 3 from h1) with h3 | h4 <;> exact hnp3 ‹_›
          · exact hnp5 h2
        have hp3_ge7 : 7 ≤ p3 := by
          by_contra! h; have : p3 = 6 := (by omega); subst this; exact absurd hp3 (by decide)
        by_cases hp3_41 : p3 ≤ 37
        · have hle := small_sum_ge_coprime hp3 hu_pos d' hd' hpd' (S := {1, 3, 5, 9, 15, 45}) (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
            · exact ⟨one_dvd _, by nlinarith, fun h => hnp45 (h.trans (by decide : 1 ∣ 45))⟩
            · exact ⟨(by decide : 3 ∣ 45).trans h45_u, by nlinarith, fun h => hnp45 (h.trans (by decide : 3 ∣ 45))⟩
            · exact ⟨(by decide : 5 ∣ 45).trans h45_u, by nlinarith, fun h => hnp45 (h.trans (by decide : 5 ∣ 45))⟩
            · exact ⟨(by decide : 9 ∣ 45).trans h45_u, by nlinarith, fun h => hnp45 (h.trans (by decide : 9 ∣ 45))⟩
            · exact ⟨(by decide : 15 ∣ 45).trans h45_u, by nlinarith, fun h => hnp45 (h.trans (by decide : 15 ∣ 45))⟩
            · exact ⟨h45_u, by nlinarith, hnp45⟩)
          have hs : ∑ x ∈ ({1, 3, 5, 9, 15, 45} : Finset ℕ), x = 78 := by decide
          omega
        · -- p3 = 41 (so b0 = 2 => 225 | u)
          have hb02 : b0 = 2 ∧ p3 = 41 := by
            have h1 : ∀ x ∈ bases3Data, 37 < x.2.2.1 → x.2.1 = 2 ∧ x.2.2.1 = 41 := by decide
            exact h1 (a0, b0, p3, L, g, P0, bad, ds, bestD, ds3p3, relN) hmem (by dsimp; omega)
          have h225_u : 225 ∣ u := by
            have h9 : 9 ∣ 3 ^ a := by have := pow_dvd_pow 3 (show 2 ≤ a by omega); norm_num at this; exact this
            have h25 : 25 ∣ 5 ^ b := by have := pow_dvd_pow 5 (show 2 ≤ b by omega); norm_num at this; exact this
            exact (Nat.mul_dvd_mul h9 h25).trans (dvd_mul_right _ _)
          have hnp225 : ¬ p3 ∣ 225 := fun h => by
            rcases hp3.dvd_mul.mp (show p3 ∣ 45 * 5 from h) with h1 | h2
            · exact hnp45 h1
            · exact hnp5 h2
          have hle := small_sum_ge_coprime hp3 hu_pos d' hd' hpd' (S := {1, 3, 5, 9, 15, 25, 45}) (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact ⟨one_dvd _, by nlinarith, fun h => hnp225 (h.trans (by decide : 1 ∣ 225))⟩
            · exact ⟨(by decide : 3 ∣ 225).trans h225_u, by nlinarith, fun h => hnp225 (h.trans (by decide : 3 ∣ 225))⟩
            · exact ⟨(by decide : 5 ∣ 225).trans h225_u, by nlinarith, fun h => hnp225 (h.trans (by decide : 5 ∣ 225))⟩
            · exact ⟨(by decide : 9 ∣ 225).trans h225_u, by nlinarith, fun h => hnp225 (h.trans (by decide : 9 ∣ 225))⟩
            · exact ⟨(by decide : 15 ∣ 225).trans h225_u, by nlinarith, fun h => hnp225 (h.trans (by decide : 15 ∣ 225))⟩
            · exact ⟨(by decide : 25 ∣ 225).trans h225_u, by nlinarith, fun h => hnp225 (h.trans (by decide : 25 ∣ 225))⟩
            · exact ⟨(by decide : 45 ∣ 225).trans h225_u, by nlinarith, fun h => hnp225 (h.trans (by decide : 45 ∣ 225))⟩)
          have hs : ∑ x ∈ ({1, 3, 5, 9, 15, 25, 45} : Finset ℕ), x = 103 := by decide
          omega

-- Lift solid core [L, P - L] and gap 2 from a bases3Data entry to 3^a * 5^b * p3^c.
set_option maxHeartbeats 1600000 in
lemma lift_base3 {a0 b0 p3 L g P0 bestD relN a b c : ℕ} {bad ds ds3p3 : List ℕ}
    (hmem : (a0, b0, p3, L, g, P0, bad, ds, bestD, ds3p3, relN) ∈ bases3Data)
    (hp3 : p3.Prime) (hp3_gt5 : 5 < p3)
    (ha : a0 ≤ a) (hb : b0 ≤ b) (hc : 1 ≤ c)
    (ha_fix : (a0 = 2 ∧ b0 = 1) → a = 2) (hb_fix : b0 = 1 → b = 1) :
    let B3 := 3 ^ a * 5 ^ b * p3 ^ c
    (∀ y, L ≤ y → y ≤ properDivsSum B3 - L → repNat B3.properDivisors y) ∧
    (∀ k, k < properDivsSum B3 → ∃ i, repNat B3.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
    (∀ x, x < L → x ∉ bad → repNat B3.properDivisors x) ∧
    P0 ≤ properDivsSum B3 := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have ha0_ge2 : 2 ≤ a0 := by
    have : ∀ x ∈ bases3Data, 2 ≤ x.1 := by decide
    exact this _ hmem
  have hb0_ge1 : 1 ≤ b0 := by
    have : ∀ x ∈ bases3Data, 1 ≤ x.2.1 := by decide
    exact this _ hmem
  have hp3_le41 : p3 ≤ 41 := by
    have : ∀ x ∈ bases3Data, x.2.2.1 ≤ 41 := by decide
    exact this _ hmem
  have hok := List.all_eq_true.mp bases3Data_ok _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hmeta, _⟩, hcore0⟩, _⟩, hrel5⟩ := hok
  obtain ⟨hL1, rfl, hP0_eq, hbig0, hB0_2P, _, _, _⟩ := hmeta
  let B0 := 3 ^ a0 * 5 ^ b0 * p3
  have hB0_pos : 0 < B0 := by have := hp3.pos; dsimp [B0]; positivity
  have hsB0 : sigma 1 B0 = ppSum 3 a0 * ppSum 5 b0 * ppSum p3 1 := by
    simpa [B0, pow_one] using sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a0) (b := b0) (c := 1)
  have hP0_eq' : P0 = properDivsSum B0 := by rw [properDivsSum_eq_sigma_sub, hsB0]; omega
  obtain ⟨hcov0, hgap0, hbad0⟩ := core_of_checkCoreBadB (by decide : 1 ≤ 2) hP0_eq' hcore0
  have hL_le_P0 : L ≤ P0 := by omega
  -- Step 1: lift 3 from a0 to a (when a0 = 3 or b0 = 2; for a0 = 2 ∧ b0 = 1, a = 2!)
  have hstep1 : (∀ y, L ≤ y → y ≤ properDivsSum (3 ^ a * 5 ^ b0 * p3) - L →
        repNat (3 ^ a * 5 ^ b0 * p3).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ a * 5 ^ b0 * p3) →
        ∃ i, repNat (3 ^ a * 5 ^ b0 * p3).properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    by_cases hfix : a0 = 2 ∧ b0 = 1
    · rw [ha_fix hfix]; dsimp only [B0] at hcov0 hgap0 hP0_eq'; rw [hfix.1] at hcov0 hgap0 hP0_eq'; rw [← hP0_eq']; exact ⟨hcov0, hgap0⟩
    · clear ha_fix
      have hB0_big : 1485 ≤ B0 := by
        have : ∀ x ∈ bases3Data, ¬ (x.1 = 2 ∧ x.2.1 = 1) → 1485 ≤ 3 ^ x.1 * 5 ^ x.2.1 * x.2.2.1 := by decide
        exact this _ hmem hfix
      have hL_le68 : L ≤ 68 := by
        have : ∀ x ∈ bases3Data, x.2.2.2.1 ≤ 68 := by decide
        exact this _ hmem
      induction a with
      | zero => omega
      | succ k ih =>
        by_cases hk : k < a0
        · have : k + 1 = a0 := by omega
          rw [this]; dsimp only [B0] at hcov0 hgap0 hP0_eq'; rw [← hP0_eq']; exact ⟨hcov0, hgap0⟩
        · obtain ⟨hc_k, hg_k⟩ := ih (by omega)
          let u := 5 ^ b0 * p3
          have hu_pos : 0 < u := by have := hp3.pos; dsimp [u]; positivity
          have hcop : ¬ 3 ∣ u := by
            have hc : Nat.Coprime 3 u := Nat.Coprime.mul_right ((by decide : Nat.Coprime 3 5).pow_right b0)
              ((Nat.coprime_primes h3p hp3).mpr (by omega))
            exact h3p.coprime_iff_not_dvd.mp hc
          have hPk_ge : P0 ≤ properDivsSum (3 ^ k * u) := by
            rw [hP0_eq']
            have hB0_eq : B0 = 3 ^ a0 * u := by dsimp [B0, u]; ring
            rw [hB0_eq]
            exact properDivsSum_mono_dvd (by positivity)
              (Nat.mul_dvd_mul_right (pow_dvd_pow 3 (show a0 ≤ k by omega)) u)
          have hsig_k : sigma 1 (3 ^ k * u) = ppSum 3 k * ppSum 5 b0 * ppSum p3 1 := by
            simpa [u, pow_one, mul_assoc] using
              sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := k) (b := b0) (c := 1)
          have hP_ge_11 : 15 * properDivsSum (3 ^ k * u) ≥ 11 * (3 ^ k * u) := by
            have h3m := ppSum_mono_exp (p := 3) (by decide) (show 2 ≤ k by omega)
            have h5m := ppSum_mono_exp (p := 5) (by decide) hb0_ge1
            have hp3m : p3 ≤ ppSum p3 1 := by rw [ppSum_one hp3.two_le]; omega
            have h32 : ppSum 3 2 = 13 := by decide
            have h51 : ppSum 5 1 = 6 := by decide
            rw [h32] at h3m; rw [h51, pow_one] at h5m
            have h123 := Nat.mul_le_mul (Nat.mul_le_mul h3m h5m) hp3m
            have h78 : 45 * (ppSum 3 k * ppSum 5 b0 * ppSum p3 1) ≥ 78 * (3 ^ k * u) := by dsimp [u]; linarith
            rw [properDivsSum_eq_sigma_sub, hsig_k]; omega
          have hku_ge : 1485 ≤ 3 ^ k * u :=
            le_trans (show 1485 ≤ 3 ^ a0 * u by simpa [B0, u, mul_assoc] using hB0_big)
              (Nat.mul_le_mul_right u (pow_le_pow_right₀ (by decide : 1 ≤ 3) (show a0 ≤ k by omega)))
          have heq_k : 3 ^ k * u = 3 ^ k * 5 ^ b0 * p3 := by dsimp [u]; ring
          have heq_k1 : 3 ^ (k + 1) * u = 3 ^ (k + 1) * 5 ^ b0 * p3 := by dsimp [u]; ring
          have hstep := lift_prime_step_no_interleave (u := u) (r := 3) (a := k) (L := L) (g := 2)
            h3p hu_pos (show 1 ≤ k by omega) hcop (by decide) (le_trans hL_le_P0 hPk_ge)
            (by rw [heq_k]; exact hc_k) (by rw [heq_k]; exact hg_k)
            (by
              intro d hd
              have hd5 : 5 * d ≤ u := by
                obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
                obtain ⟨t, ht⟩ := hdvd
                have ht1 : 1 < t := by
                  by_contra! h1; have : t = 0 ∨ t = 1 := by omega
                  rcases this with rfl | rfl <;> simp_all
                have ht5 : 5 ≤ t := by
                  by_contra! htlt
                  have hp_min := Nat.minFac_prime (by omega : t ≠ 1)
                  have hdvd_u : t.minFac ∣ u := (Nat.minFac_dvd t).trans ⟨d, by rw [mul_comm]; exact ht⟩
                  have hle4 : t.minFac ≤ 4 := le_trans (Nat.minFac_le (by omega)) (by omega)
                  have h5_or_p : t.minFac ∣ 5 ^ b0 ∨ t.minFac ∣ p3 := hp_min.dvd_mul.mp hdvd_u
                  rcases h5_or_p with h5d | hpd
                  · have := hp_min.dvd_of_dvd_pow h5d
                    rcases (by decide : Nat.Prime 5).eq_one_or_self_of_dvd _ this with h1 | h2
                    · exact hp_min.ne_one h1
                    · omega
                  · rcases hp3.eq_one_or_self_of_dvd _ hpd with h1 | h2
                    · exact hp_min.ne_one h1
                    · omega
                nlinarith
              have h1 : 15 * (2 * L + 3 ^ (k + 1) * d) ≤ 30 * L + 9 * (3 ^ k * u) := by
                rw [pow_succ]; nlinarith
              have h2 : 30 * L + 9 * (3 ^ k * u) ≤ 15 * properDivsSum (3 ^ k * u) := by omega
              change 2 * L + 3 ^ (k + 1) * d ≤ properDivsSum (3 ^ k * u) + _ + 1
              omega)
            (by
              change 2 * L + 3 ^ k * u ≤ properDivsSum (3 ^ k * u) + 3 ^ (k + 1) * properDivsSum u + 1
              have hPu : 5 * properDivsSum u ≥ u := by
                have hsu : sigma 1 u = ppSum 5 b0 * ppSum p3 1 := by
                  have h := sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := 0) (b := b0) (c := 1)
                  simp only [pow_zero, one_mul, pow_one, ppSum_zero (by decide : 2 ≤ 3)] at h
                  exact h
                have h5m := ppSum_mono_exp (p := 5) (by decide) hb0_ge1
                have h51 : ppSum 5 1 = 6 := by decide
                rw [h51, pow_one] at h5m
                have hp3m : p3 ≤ ppSum p3 1 := by rw [ppSum_one hp3.two_le]; omega
                have := Nat.mul_le_mul h5m hp3m
                have h6 : 5 * (ppSum 5 b0 * ppSum p3 1) ≥ 6 * u := by dsimp [u]; linarith
                rw [properDivsSum_eq_sigma_sub, hsu]; omega
              have h3Pu := Nat.mul_le_mul_left (3 ^ k) hPu
              have h1 : 3 ^ k * (5 * properDivsSum u) = 5 * (3 ^ k * properDivsSum u) := by ring
              have h2 : 3 ^ (k + 1) * properDivsSum u = 3 * (3 ^ k * properDivsSum u) := by ring
              omega)
          rw [heq_k1] at hstep; exact hstep
  -- Step 2: lift 5 from b0 to b (only needed when b0 = 2; if b0 = 1, b = 1!)
  have hstep2 : (∀ y, L ≤ y → y ≤ properDivsSum (3 ^ a * 5 ^ b * p3) - L →
        repNat (3 ^ a * 5 ^ b * p3).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ a * 5 ^ b * p3) →
        ∃ i, repNat (3 ^ a * 5 ^ b * p3).properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    by_cases hb1 : b0 = 1
    · rw [hb_fix hb1, ← hb1]; exact hstep1
    · clear hb_fix
      have hb0_eq2 : b0 = 2 := by
        have : ∀ x ∈ bases3Data, x.2.1 = 1 ∨ x.2.1 = 2 := by decide
        exact (this _ hmem).resolve_left hb1
      subst hb0_eq2
      simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hrel5
      obtain ⟨hrel5_chk, hmul5, hbud5, hstepn5⟩ := hrel5
      let u0 := 3 ^ a0 * p3
      have hu0_pos : 0 < u0 := by have := hp3.pos; dsimp [u0]; positivity
      have hsu0 : sigma 1 u0 = ppSum 3 a0 * ppSum p3 1 := by
        have h := sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a0) (b := 0) (c := 1)
        simp only [pow_zero, mul_one, pow_one, ppSum_zero (by decide : 2 ≤ 5)] at h
        exact h
      have hPu0_eq : ppSum 3 a0 * ppSum p3 1 - u0 = properDivsSum u0 := by
        rw [properDivsSum_eq_sigma_sub, hsu0]
      have hrel_u0 : HasRelGap u0 relN 1000 := hasRelGap_of_list hu0_pos hPu0_eq hrel5_chk
      have hrel_ua : ∀ a', a0 ≤ a' → HasRelGap (3 ^ a' * p3) relN 1000 := by
        intro a' ha'
        induction a' with
        | zero => omega
        | succ k ih =>
          by_cases hk : k < a0
          · have : k + 1 = a0 := (by omega); rw [this]; exact hrel_u0
          · have hprev := ih (by omega)
            let uk := 3 ^ k * p3
            have huk_pos : 0 < uk := by have := hp3.pos; dsimp [uk]; positivity
            rw [show 3 ^ (k + 1) * p3 = 3 * uk by dsimp [uk]; ring]
            apply HasRelGap.mul_prime h3p huk_pos hprev
            have hratio : properDivsSum u0 * uk ≤ properDivsSum uk * u0 := by
              have h := properDivsSum_ratio_mono_3p h3p h5p hp3 (by decide) hp3_gt5 (show a0 ≤ k by omega) le_rfl le_rfl (b0 := 0) (c0 := 1)
              simpa [u0, uk] using h
            have h1 : 1000 * u0 ≤ relN * (3 * u0) + 1000 * properDivsSum u0 := by
              have hsu_add : properDivsSum u0 + u0 = ppSum 3 a0 * ppSum p3 1 := by
                rw [← hsu0, properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
              dsimp only [u0] at hmul5 hsu_add hPu0_eq ⊢
              rw [hPu0_eq, hsu_add] at hmul5
              have : 3 * relN * (3 ^ a0 * p3) = relN * (3 * (3 ^ a0 * p3)) := by ring
              omega
            have h2 : (1000 * uk) * u0 ≤ (relN * (3 * uk) + 1000 * properDivsSum uk) * u0 := by
              have hm1 := Nat.mul_le_mul_right uk h1
              have hm2 := Nat.mul_le_mul_left 1000 hratio
              linarith
            exact Nat.le_of_mul_le_mul_right h2 hu0_pos
      let u := 3 ^ a * p3
      have hu_pos : 0 < u := by have := hp3.pos; dsimp [u]; positivity
      have hrel_u : HasRelGap u relN 1000 := hrel_ua a ha
      have hcop5 : ¬ 5 ∣ u := by
        have hc : Nat.Coprime 5 u := Nat.Coprime.mul_right ((by decide : Nat.Coprime 5 3).pow_right a)
          ((Nat.coprime_primes h5p hp3).mpr (by omega))
        exact h5p.coprime_iff_not_dvd.mp hc
      induction b with
      | zero => omega
      | succ k ih =>
        by_cases hk : k < 2
        · have : k + 1 = 2 := (by omega); rw [this]; exact hstep1
        · obtain ⟨hc_k, hg_k⟩ := ih (by omega)
          have hP_ge : P0 ≤ properDivsSum (5 ^ k * u) := by
            rw [hP0_eq']
            exact properDivsSum_mono_dvd (by positivity)
              (by
                have h1 : 3 ^ a0 * 5 ^ 2 * p3 ∣ 3 ^ a * 5 ^ k * p3 :=
                  Nat.mul_dvd_mul_right (Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow 5 (by omega))) p3
                simpa [B0, u, mul_comm, mul_left_comm, mul_assoc] using h1)
          have hratio_B : properDivsSum (25 * u0) * (5 ^ k * u) ≤ properDivsSum (5 ^ k * u) * (25 * u0) := by
            have h := properDivsSum_ratio_mono_3p h3p h5p hp3 (by decide) hp3_gt5 ha (show 2 ≤ k by omega) le_rfl (c0 := 1)
            simpa [u0, u, mul_comm, mul_left_comm, mul_assoc] using h
          have h25u0_P : properDivsSum (25 * u0) = 31 * (ppSum 3 a0 * ppSum p3 1) - 25 * u0 := by
            rw [properDivsSum_eq_sigma_sub]
            have h := sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a0) (b := 2) (c := 1)
            have h52 : ppSum 5 2 = 31 := by decide
            simp only [pow_one, h52] at h
            have : 25 * u0 = 3 ^ a0 * 5 ^ 2 * p3 := by dsimp [u0]; ring
            rw [this, h]; ring_nf
          have h5k_ge25 : 25 * u0 ≤ 5 ^ k * u := by
            have h1 : 25 ≤ 5 ^ k := by have := pow_le_pow_right₀ (by decide : 1 ≤ 5) (show 2 ≤ k by omega); norm_num at this; exact this
            have h2 : u0 ≤ u := Nat.mul_le_mul_right p3 (pow_le_pow_right₀ (by decide) ha)
            exact Nat.mul_le_mul h1 h2
          have heq_k : 5 ^ k * u = 3 ^ a * 5 ^ k * p3 := by dsimp [u]; ring
          have heq_k1 : 5 ^ (k + 1) * u = 3 ^ a * 5 ^ (k + 1) * p3 := by dsimp [u]; ring
          have hstep := lift_prime_step_no_interleave (u := u) (r := 5) (a := k) (L := L) (g := 2)
            h5p hu_pos (show 1 ≤ k by omega) hcop5 (by decide) (le_trans hL_le_P0 hP_ge)
            (by rw [heq_k]; exact hc_k)
            (by rw [heq_k]; exact hg_k)
            (by
              intro d hd
              have hrg := hrel_u d hd
              have hP_u0_add : ppSum 3 a0 * ppSum p3 1 - u0 + u0 = ppSum 3 a0 * ppSum p3 1 := by
                rw [← hsu0, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
              rw [hP_u0_add] at hbud5
              -- Scale hbud5 by (5^k * u) / (25 * u0)
              have hbud_scaled : (1000 * (2 * L) + 5 ^ (k + 1) * relN * u) * (25 * u0) ≤
                  (1000 * properDivsSum (5 ^ k * u)) * (25 * u0) := by
                have h1 : 125 * relN * u0 + 1000 * (2 * L) ≤ 1000 * properDivsSum (25 * u0) := by
                  rw [h25u0_P]; dsimp only [u0] at hbud5 ⊢
                  have : 1000 * (2 * L + 1) = 1000 * (2 * L) + 1000 := by ring
                  have : 1000 * (31 * (ppSum 3 a0 * ppSum p3 1) - 25 * (3 ^ a0 * p3) + 1) = 1000 * (31 * (ppSum 3 a0 * ppSum p3 1) - 25 * (3 ^ a0 * p3)) + 1000 := by ring
                  omega
                have h2 : (125 * relN * u0 + 1000 * (2 * L)) * (5 ^ k * u) ≤
                    1000 * properDivsSum (25 * u0) * (5 ^ k * u) := Nat.mul_le_mul_right _ h1
                have h3 : 1000 * (properDivsSum (25 * u0) * (5 ^ k * u)) ≤
                    1000 * (properDivsSum (5 ^ k * u) * (25 * u0)) := Nat.mul_le_mul_left 1000 hratio_B
                have h4 : 5 ^ (k + 1) * relN * u * (25 * u0) = 125 * relN * u0 * (5 ^ k * u) := by ring
                have h5 : 1000 * (2 * L) * (25 * u0) ≤ 1000 * (2 * L) * (5 ^ k * u) :=
                  Nat.mul_le_mul_left _ h5k_ge25
                linarith
              have hbud_k : 1000 * (2 * L) + 5 ^ (k + 1) * relN * u ≤ 1000 * properDivsSum (5 ^ k * u) :=
                Nat.le_of_mul_le_mul_right hbud_scaled (by positivity)
              have hm := Nat.mul_le_mul_left (5 ^ (k + 1)) hrg
              change 2 * L + 5 ^ (k + 1) * d ≤ properDivsSum (5 ^ k * u) + 5 ^ (k + 1) * _ + 1
              linarith)
            (by
              have hratio_u : properDivsSum u0 * u ≤ properDivsSum u * u0 := by
                have h := properDivsSum_ratio_mono_3p h3p h5p hp3 (by decide) hp3_gt5 ha le_rfl le_rfl (b0 := 0) (c0 := 1)
                simpa [u0, u] using h
              have hP_u0_add : ppSum 3 a0 * ppSum p3 1 - u0 + u0 = ppSum 3 a0 * ppSum p3 1 := by
                rw [← hsu0, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
              rw [hP_u0_add, hPu0_eq, ← h25u0_P] at hstepn5
              change 2 * L + 25 * u0 ≤ properDivsSum (25 * u0) + 125 * properDivsSum u0 + 1 at hstepn5
              have h1 : (2 * L + 5 ^ k * u) * (25 * u0) ≤
                  (properDivsSum (5 ^ k * u) + 5 ^ (k + 1) * properDivsSum u + 1) * (25 * u0) := by
                have hm1 := Nat.mul_le_mul_right (5 ^ k * u) hstepn5
                have hm2 : 5 ^ (k + 1) * 25 * (properDivsSum u0 * u) = 125 * properDivsSum u0 * (5 ^ k * u) := by ring
                have hm3 : 5 ^ (k + 1) * 25 * (properDivsSum u0 * u) ≤ 5 ^ (k + 1) * 25 * (properDivsSum u * u0) :=
                  Nat.mul_le_mul_left _ hratio_u
                have h2L : 2 * L * (25 * u0) ≤ 2 * L * (5 ^ k * u) := Nat.mul_le_mul_left _ h5k_ge25
                have h1mul : 1 * (25 * u0) ≤ 1 * (5 ^ k * u) := Nat.mul_le_mul_left 1 h5k_ge25
                have h4 : 5 ^ (k + 1) * 25 * (properDivsSum u * u0) = 5 ^ (k + 1) * properDivsSum u * (25 * u0) := by ring
                have h5 : (25 * u0) * (5 ^ k * u) = 5 ^ k * u * (25 * u0) := by ring
                have h6 : (2 * L - 1) * (25 * u0) + (5 ^ k * u) ≤ 2 * L * (5 ^ k * u) := by
                  have hL1' : 1 ≤ L := by have : ∀ x ∈ bases3Data, 1 ≤ x.2.2.2.1 := (by decide); exact this _ hmem
                  have ha1 := Nat.mul_le_mul_left (2 * L - 1) h5k_ge25
                  have ha2 : ((2 * L - 1) + 1) * (5 ^ k * u) = 2 * L * (5 ^ k * u) := by congr 1; omega
                  linarith
                have h7 : 2 * L * (25 * u0) = (2 * L - 1) * (25 * u0) + 25 * u0 := by
                  have hL1' : 1 ≤ L := by have : ∀ x ∈ bases3Data, 1 ≤ x.2.2.2.1 := (by decide); exact this _ hmem
                  have : ((2 * L - 1) + 1) * (25 * u0) = 2 * L * (25 * u0) := by congr 1; omega
                  linarith
                linarith
              change 2 * L + 5 ^ k * u ≤ properDivsSum (5 ^ k * u) + 5 ^ (k + 1) * properDivsSum u + 1
              exact Nat.le_of_mul_le_mul_right h1 (by positivity))
          rw [heq_k1] at hstep; exact hstep
  -- Step 3: lift p3 from 1 to c using HasAbsGap (3^a * 5^b) 2!
  have hstep3 : (∀ y, L ≤ y → y ≤ properDivsSum (3 ^ a * 5 ^ b * p3 ^ c) - L →
        repNat (3 ^ a * 5 ^ b * p3 ^ c).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ a * 5 ^ b * p3 ^ c) →
        ∃ i, repNat (3 ^ a * 5 ^ b * p3 ^ c).properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    let u := 3 ^ a * 5 ^ b
    have hu_pos : 0 < u := by positivity
    have habs_u : HasAbsGap u 2 := hasAbsGap_3_5 (by omega) (by omega)
    have hcop_p : ¬ p3 ∣ u := by
      have hc : Nat.Coprime p3 u := Nat.Coprime.mul_right (((Nat.coprime_primes hp3 h3p).mpr (by omega)).pow_right a)
        (((Nat.coprime_primes hp3 h5p).mpr (by omega)).pow_right b)
      exact hp3.coprime_iff_not_dvd.mp hc
    induction c with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hstep2
      | succ k' =>
        obtain ⟨hc_k, hg_k⟩ := ih (by omega)
        have hPk_ge : P0 ≤ properDivsSum (p3 ^ (k' + 1) * u) := by
          rw [hP0_eq']
          exact properDivsSum_mono_dvd (by positivity)
            (by
              have h1 : 3 ^ a0 * 5 ^ b0 * p3 ∣ 3 ^ a * 5 ^ b * p3 ^ (k' + 1) :=
                Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow 5 hb)) (dvd_pow_self p3 (by omega))
              simpa [B0, u, mul_comm, mul_left_comm, mul_assoc] using h1)
        have hP_lb : 2 * L + 2 * p3 ^ (k' + 2) ≤ properDivsSum (p3 ^ (k' + 1) * u) + 1 := by
          have hsig_k : sigma 1 (p3 ^ (k' + 1) * u) = ppSum 3 a * ppSum 5 b * ppSum p3 (k' + 1) := by
            have h := sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a) (b := b) (c := k' + 1)
            simpa [u, mul_comm, mul_left_comm, mul_assoc] using h
          have h35_sig : sigma 1 u = ppSum 3 a * ppSum 5 b := by
            have h := sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a) (b := b) (c := 0)
            simp only [pow_zero, mul_one, ppSum_zero hp3.two_le] at h; exact h
          have hP_expand : properDivsSum (p3 ^ (k' + 1) * u) ≥ p3 ^ (k' + 1) * properDivsSum u + sigma 1 u := by
            have hpp_ge : p3 ^ (k' + 1) + 1 ≤ ppSum p3 (k' + 1) := by
              have h1 := ppSum_succ (p := p3) (k := k') hp3.two_le
              have h2 : p3 ^ k' ≤ ppSum p3 k' := by
                rw [ppSum_eq_sigma hp3, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
              rw [h1, pow_succ]; nlinarith
            have hsu_ge : u ≤ sigma 1 u := by
              rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
            rw [properDivsSum_eq_sigma_sub, hsig_k, ← h35_sig, properDivsSum_eq_sigma_sub]
            have h1 : sigma 1 u * (p3 ^ (k' + 1) + 1) ≤ sigma 1 u * ppSum p3 (k' + 1) :=
              Nat.mul_le_mul_left _ hpp_ge
            have h2 : p3 ^ (k' + 1) * (sigma 1 u - u) = p3 ^ (k' + 1) * sigma 1 u - p3 ^ (k' + 1) * u :=
              Nat.mul_sub _ _ _
            have h3 : sigma 1 u * (p3 ^ (k' + 1) + 1) = p3 ^ (k' + 1) * sigma 1 u + sigma 1 u := by ring
            have h4 : p3 ^ (k' + 1) * u ≤ p3 ^ (k' + 1) * sigma 1 u := Nat.mul_le_mul_left _ hsu_ge
            have h5 : sigma 1 u * ppSum p3 (k' + 1) = ppSum 3 a * ppSum 5 b * ppSum p3 (k' + 1) := by rw [h35_sig]
            omega
          have h45_P : properDivsSum u ≥ properDivsSum (3 ^ a0 * 5 ^ b0) :=
            properDivsSum_mono_dvd hu_pos (Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow 5 hb))
          have h45_sig : sigma 1 u ≥ 78 := by
            have ha_ge2 : 2 ≤ a := le_trans ha0_ge2 ha
            have hb_pos : 1 ≤ b := le_trans hb0_ge1 hb
            have : 45 ∣ u := Nat.mul_dvd_mul (by have := pow_dvd_pow 3 ha_ge2; norm_num at this; exact this) (dvd_pow_self 5 (show b ≠ 0 by omega))
            have : properDivsSum 45 ≤ properDivsSum u := properDivsSum_mono_dvd hu_pos this
            have : 45 ≤ u := Nat.le_of_dvd hu_pos ‹45 ∣ u›
            have hP45 : properDivsSum 45 = 33 := by decide
            have hPu_sub := properDivsSum_eq_sigma_sub u
            omega
          have hPu_gt : 2 * p3 + 2 * L ≤ p3 * properDivsSum (3 ^ a0 * 5 ^ b0) + 78 ∧
              2 * p3 ≤ properDivsSum (3 ^ a0 * 5 ^ b0) := by
            have hchk : ∀ x ∈ bases3Data,
                2 * x.2.2.1 + 2 * x.2.2.2.1 ≤ x.2.2.1 * (ppSum 3 x.1 * ppSum 5 x.2.1 - 3 ^ x.1 * 5 ^ x.2.1) + 78 ∧
                2 * x.2.2.1 ≤ ppSum 3 x.1 * ppSum 5 x.2.1 - 3 ^ x.1 * 5 ^ x.2.1 := by decide
            have hs0 : sigma 1 (3 ^ a0 * 5 ^ b0) = ppSum 3 a0 * ppSum 5 b0 := by
              have h := sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a0) (b := b0) (c := 0)
              simp only [pow_zero, mul_one, ppSum_zero hp3.two_le] at h; exact h
            rw [properDivsSum_eq_sigma_sub, hs0]
            exact hchk _ hmem
          have hp_pow : p3 ≤ p3 ^ (k' + 1) := Nat.le_self_pow (by omega) p3
          have h1 : 2 * p3 ^ (k' + 2) + 2 * L = p3 ^ (k' + 1) * (2 * p3) + 2 * L := by ring
          have h2 : p3 ^ (k' + 1) * (2 * p3) + 2 * L ≤ p3 ^ (k' + 1) * properDivsSum u + 78 := by
            have hd : 2 * p3 ≤ properDivsSum u := le_trans hPu_gt.2 h45_P
            have hmul := Nat.mul_le_mul_right (properDivsSum u - 2 * p3) hp_pow
            have hsub1 : p3 * (properDivsSum u - 2 * p3) = p3 * properDivsSum u - p3 * (2 * p3) := Nat.mul_sub _ _ _
            have hsub2 : p3 ^ (k' + 1) * (properDivsSum u - 2 * p3) =
                p3 ^ (k' + 1) * properDivsSum u - p3 ^ (k' + 1) * (2 * p3) := Nat.mul_sub _ _ _
            have hle_p : 2 * L ≤ p3 * properDivsSum u - p3 * (2 * p3) + 78 := by
              have : p3 * (2 * p3) ≤ p3 * properDivsSum u := Nat.mul_le_mul_left p3 hd
              have : 2 * p3 ≤ p3 * (2 * p3) := by nlinarith [hp3.two_le]
              -- Actually even simpler: we have 2*L <= 2*68 = 136, and p3*(Pu - 2*p3) >= p3*(Pu0 - 2*p3):
              have hchk2 : ∀ x ∈ bases3Data,
                  2 * x.2.2.2.1 ≤ x.2.2.1 * (ppSum 3 x.1 * ppSum 5 x.2.1 - 3 ^ x.1 * 5 ^ x.2.1 - 2 * x.2.2.1) + 78 := by decide
              have hs0 : sigma 1 (3 ^ a0 * 5 ^ b0) = ppSum 3 a0 * ppSum 5 b0 := by
                have h := sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a0) (b := b0) (c := 0)
                simp only [pow_zero, mul_one, ppSum_zero hp3.two_le] at h; exact h
              have hPu_sub : ppSum 3 a0 * ppSum 5 b0 - 3 ^ a0 * 5 ^ b0 - 2 * p3 ≤ properDivsSum u - 2 * p3 := by
                rw [properDivsSum_eq_sigma_sub (3 ^ a0 * 5 ^ b0), hs0] at h45_P; omega
              have hmul_sub := Nat.mul_le_mul_left p3 hPu_sub
              have h2L_le := hchk2 _ hmem
              dsimp only at h2L_le
              rw [← hsub1]; omega
            have : p3 ^ (k' + 1) * (2 * p3) ≤ p3 ^ (k' + 1) * properDivsSum u := Nat.mul_le_mul_left _ hd
            have : p3 * (2 * p3) ≤ p3 * properDivsSum u := Nat.mul_le_mul_left _ hd
            omega
          omega
        have heq_k : p3 ^ (k' + 1) * u = 3 ^ a * 5 ^ b * p3 ^ (k' + 1) := by dsimp [u]; ring
        have heq_k2 : p3 ^ (k' + 2) * u = 3 ^ a * 5 ^ b * p3 ^ (k' + 2) := by dsimp [u]; ring
        have hstep := lift_prime_step_no_interleave (u := u) (r := p3) (a := k' + 1) (L := L) (g := 2)
          hp3 hu_pos (by omega) hcop_p (by decide) (le_trans hL_le_P0 hPk_ge)
          (by rw [heq_k]; exact hc_k)
          (by rw [heq_k]; exact hg_k)
          (by
            intro d hd
            have h1 := habs_u d hd
            have hm := Nat.mul_le_mul_left (p3 ^ (k' + 2)) h1
            change 2 * L + p3 ^ (k' + 2) * d ≤ properDivsSum (p3 ^ (k' + 1) * u) + p3 ^ (k' + 2) * _ + 1
            linarith)
          (by
            change 2 * L + p3 ^ (k' + 1) * u ≤ properDivsSum (p3 ^ (k' + 1) * u) + p3 ^ (k' + 2) * properDivsSum u + 1
            have hu_le_2Pu : u ≤ 2 * properDivsSum u := by
              have h3m := ppSum_mono_exp (p := 3) (by decide) (show 2 ≤ a by omega)
              have h5m := ppSum_mono_exp (p := 5) (by decide) (show 1 ≤ b by omega)
              have h32 : ppSum 3 2 = 13 := by decide
              have h51 : ppSum 5 1 = 6 := by decide
              rw [h32] at h3m; rw [h51, pow_one] at h5m
              have h12 := Nat.mul_le_mul h3m h5m
              have hs : sigma 1 u = ppSum 3 a * ppSum 5 b := by
                have h := sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a) (b := b) (c := 0)
                simp only [pow_zero, mul_one, ppSum_zero hp3.two_le] at h; exact h
              have h78 : 45 * (ppSum 3 a * ppSum 5 b) ≥ 78 * u := by dsimp [u]; linarith
              rw [properDivsSum_eq_sigma_sub, hs]; omega
            have : p3 ^ (k' + 1) * u ≤ p3 ^ (k' + 2) * properDivsSum u := by
              have h1 := Nat.mul_le_mul_left (p3 ^ (k' + 1)) hu_le_2Pu
              have h2 := Nat.mul_le_mul_left (p3 ^ (k' + 1)) (Nat.mul_le_mul_right (properDivsSum u) hp3.two_le)
              have h3 : p3 ^ (k' + 1) * (p3 * properDivsSum u) = p3 ^ (k' + 2) * properDivsSum u := by ring
              linarith
            omega)
        rw [heq_k2] at hstep; exact hstep
  have hB0_dvd_B3 : B0 ∣ 3 ^ a * 5 ^ b * p3 ^ c :=
    Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow 5 hb)) (dvd_pow_self p3 (by omega))
  refine ⟨hstep3.1, hstep3.2, ?_, ?_⟩
  · intro x hx hnot
    obtain ⟨s, hs, hsum⟩ := hbad0 x hx hnot
    refine ⟨s, fun d hd => ?_, hsum⟩
    obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp (hs hd)
    exact Nat.mem_properDivisors.mpr ⟨h1.trans hB0_dvd_B3,
      lt_of_lt_of_le h2 (Nat.le_of_dvd (by have := hp3.pos; positivity) hB0_dvd_B3)⟩
  · rw [hP0_eq']; exact properDivsSum_mono_dvd (by have := hp3.pos; positivity) hB0_dvd_B3

-- Extend lift_base3 by a 4th prime p4^d (for p4 <= (P0 - 2*L + 1) / 2).
set_option maxHeartbeats 1600000 in
lemma lift_base3_p4 {a0 b0 p3 L g P0 bestD relN a b c p4 d : ℕ} {bad ds ds3p3 : List ℕ}
    (hmem : (a0, b0, p3, L, g, P0, bad, ds, bestD, ds3p3, relN) ∈ bases3Data)
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hp3_gt5 : 5 < p3) (hp34 : p3 < p4)
    (ha : a0 ≤ a) (hb : b0 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (ha_fix : (a0 = 2 ∧ b0 = 1) → a = 2) (hb_fix : b0 = 1 → b = 1)
    (hp4_bound : 2 * p4 + 2 * L ≤ P0 + 1) :
    let B4 := 3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d
    (∀ y, L ≤ y → y ≤ properDivsSum B4 - L → repNat B4.properDivisors y) ∧
    (∀ k, k < properDivsSum B4 → ∃ i, repNat B4.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
    (∀ x, x < L → x ∉ bad → repNat B4.properDivisors x) ∧
    P0 ≤ properDivsSum B4 := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have ha0_ge2 : 2 ≤ a0 := by have : ∀ x ∈ bases3Data, 2 ≤ x.1 := (by decide); exact this _ hmem
  have hb0_ge1 : 1 ≤ b0 := by have : ∀ x ∈ bases3Data, 1 ≤ x.2.1 := (by decide); exact this _ hmem
  obtain ⟨hcov3, hgap3, hbad3, hP3_ge⟩ := lift_base3 hmem hp3 hp3_gt5 ha hb hc ha_fix hb_fix
  have habs3 : HasAbsGap (3 ^ a * 5 ^ b * p3 ^ c) 2 := hasAbsGap_base3 hmem hp3 hp3_gt5 ha0_ge2 hb0_ge1 ha hb hc
  let B3 := 3 ^ a * 5 ^ b * p3 ^ c
  have hB3_pos : 0 < B3 := by have := hp3.pos; dsimp [B3]; positivity
  have hcop34 : B3.Coprime p4 :=
    Nat.Coprime.mul_left
      (Nat.Coprime.mul_left (((Nat.coprime_primes h3p hp4).mpr (by omega)).pow_left a)
        (((Nat.coprime_primes h5p hp4).mpr (by omega)).pow_left b))
      (((Nat.coprime_primes hp3 hp4).mpr (by omega)).pow_left c)
  have hB3_le_2P : B3 ≤ 2 * properDivsSum B3 := by
    have h3m := ppSum_mono_exp (p := 3) (by decide) (show 2 ≤ a by omega)
    have h5m := ppSum_mono_exp (p := 5) (by decide) (show 1 ≤ b by omega)
    have hp3m : p3 ^ c ≤ ppSum p3 c := by
      rw [ppSum_eq_sigma hp3, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
    have h32 : ppSum 3 2 = 13 := by decide
    have h51 : ppSum 5 1 = 6 := by decide
    rw [h32] at h3m; rw [h51, pow_one] at h5m
    have h123 := Nat.mul_le_mul (Nat.mul_le_mul h3m h5m) hp3m
    have hs : sigma 1 B3 = ppSum 3 a * ppSum 5 b * ppSum p3 c :=
      sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5
    have h78 : 45 * (ppSum 3 a * ppSum 5 b * ppSum p3 c) ≥ 78 * B3 := by dsimp [B3]; linarith
    rw [properDivsSum_eq_sigma_sub, hs]; omega
  change P0 ≤ properDivsSum B3 at hP3_ge
  have hp4_2 : 2 ≤ p4 := hp4.two_le
  have hL_le_P3 : L ≤ properDivsSum B3 := by omega
  have hover : B3 + 2 * L ≤ properDivsSum B3 + p4 * properDivsSum B3 + 1 := by
    have : 2 * properDivsSum B3 ≤ p4 * properDivsSum B3 := Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨hcov31, hgap31⟩ := lift_coprime_prime hB3_pos hp4 hcop34 (by decide : 1 ≤ 2) hL_le_P3
    (by omega) hover hcov3 hgap3
  have hnot_p4_B3 : ¬ p4 ∣ B3 := hp4.coprime_iff_not_dvd.mp hcop34.symm
  have hstep_d : (∀ y, L ≤ y → y ≤ properDivsSum (B3 * p4 ^ d) - L → repNat (B3 * p4 ^ d).properDivisors y) ∧
      (∀ k, k < properDivsSum (B3 * p4 ^ d) → ∃ i, repNat (B3 * p4 ^ d).properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    induction d with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using ⟨hcov31, hgap31⟩
      | succ k' =>
        obtain ⟨hc_k, hg_k⟩ := ih (by omega)
        have hP_lb : properDivsSum (p4 ^ (k' + 1) * B3) ≥ p4 ^ (k' + 1) * properDivsSum B3 := by
          have hs : sigma 1 (p4 ^ (k' + 1) * B3) = ppSum p4 (k' + 1) * sigma 1 B3 := by
            rw [isMultiplicative_sigma.map_mul_of_coprime (hcop34.symm.pow_left _), ← ppSum_eq_sigma hp4]
          have hpp : p4 ^ (k' + 1) ≤ ppSum p4 (k' + 1) := by
            rw [ppSum_eq_sigma hp4, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
          have hsigB : B3 ≤ sigma 1 B3 := by
            rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
          rw [properDivsSum_eq_sigma_sub, hs, properDivsSum_eq_sigma_sub]
          have : p4 ^ (k' + 1) * (sigma 1 B3 - B3) = p4 ^ (k' + 1) * sigma 1 B3 - p4 ^ (k' + 1) * B3 := Nat.mul_sub _ _ _
          have : p4 ^ (k' + 1) * sigma 1 B3 ≤ ppSum p4 (k' + 1) * sigma 1 B3 := Nat.mul_le_mul_right _ hpp
          omega
        have hPk_ge_P0 : P0 ≤ properDivsSum (p4 ^ (k' + 1) * B3) :=
          le_trans hP3_ge (properDivsSum_mono_dvd (by have := hp4.pos; positivity) (dvd_mul_left B3 _))
        have hstep := lift_prime_step_no_interleave (u := B3) (r := p4) (a := k' + 1) (L := L) (g := 2)
          hp4 hB3_pos (by omega) hnot_p4_B3 (by decide) (le_trans (by omega : L ≤ P0) hPk_ge_P0)
          (by rw [mul_comm]; exact hc_k) (by rw [mul_comm]; exact hg_k)
          (by
            intro x hx
            have h1 := habs3 x hx
            have hm := Nat.mul_le_mul_left (p4 ^ (k' + 2)) h1
            have hp4_ge2 : 2 ≤ p4 ^ (k' + 1) := le_trans hp4.two_le (Nat.le_self_pow (by omega) p4)
            have h2L : 2 * L + p4 ^ (k' + 1) * (2 * p4) ≤ p4 ^ (k' + 1) * properDivsSum B3 + 1 := by
              have h1' : 2 * p4 + 2 * L ≤ properDivsSum B3 + 1 := by omega
              have hL1 : 1 ≤ L := by have : ∀ x ∈ bases3Data, 1 ≤ x.2.2.2.1 := (by decide); exact this _ hmem
              have h3' : 2 * p4 + (2 * L - 1) ≤ properDivsSum B3 := by omega
              have h4' := Nat.mul_le_mul_left (p4 ^ (k' + 1)) h3'
              have h5' : 2 * L ≤ p4 ^ (k' + 1) * (2 * L - 1) := by
                have := Nat.mul_le_mul_right (2 * L - 1) hp4_ge2; omega
              linarith
            change 2 * L + p4 ^ (k' + 2) * x ≤ properDivsSum (p4 ^ (k' + 1) * B3) + p4 ^ (k' + 2) * _ + 1
            have : p4 ^ (k' + 2) * 2 = p4 ^ (k' + 1) * (2 * p4) := by ring
            linarith)
          (by
            change 2 * L + p4 ^ (k' + 1) * B3 ≤ properDivsSum (p4 ^ (k' + 1) * B3) + p4 ^ (k' + 2) * properDivsSum B3 + 1
            have : p4 ^ (k' + 1) * B3 ≤ p4 ^ (k' + 2) * properDivsSum B3 := by
              have h1 := Nat.mul_le_mul_left (p4 ^ (k' + 1)) hB3_le_2P
              have h2 := Nat.mul_le_mul_left (p4 ^ (k' + 1)) (Nat.mul_le_mul_right (properDivsSum B3) hp4.two_le)
              have h3 : p4 ^ (k' + 1) * (p4 * properDivsSum B3) = p4 ^ (k' + 2) * properDivsSum B3 := by ring
              linarith
            omega)
        rw [mul_comm] at hstep; exact hstep
  refine ⟨hstep_d.1, hstep_d.2, ?_, ?_⟩
  · intro x hx hnot
    obtain ⟨s, hs, hsum⟩ := hbad3 x hx hnot
    refine ⟨s, fun z hz => ?_, hsum⟩
    obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp (hs hz)
    exact Nat.mem_properDivisors.mpr ⟨h1.trans (dvd_mul_right B3 _),
      lt_of_lt_of_le h2 (Nat.le_of_dvd (by have := hp4.pos; positivity) (dvd_mul_right B3 _))⟩
  · exact le_trans hP3_ge (properDivsSum_mono_dvd (by have := hp4.pos; positivity) (dvd_mul_right B3 _))

/-- Lift 315 * p4^d for p4 in {157..199} using lift_prime_step_n_second. -/
lemma lift_315_p4 {p4 L g P0 d : ℕ} {bad ds : List ℕ}
    (hmem : (p4, L, g, P0, bad, ds) ∈ bases315Data)
    (hp4 : p4.Prime) (hd : 1 ≤ d) :
    let B4 := 315 * p4 ^ d
    (∀ y, 3 ≤ y → y ≤ properDivsSum B4 - 3 → repNat B4.properDivisors y) ∧
    (∀ k, k < properDivsSum B4 → ∃ i, repNat B4.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
    (∀ x, x < 3 → x ∉ [2] → repNat B4.properDivisors x) ∧
    P0 ≤ properDivsSum B4 := by
  have hok := List.all_eq_true.mp bases315Data_ok _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨rfl, rfl, hP0_eq, _, rfl⟩, hcore0⟩ := hok
  have hp4_bd : 157 ≤ p4 ∧ p4 ≤ 199 := by
    have : ∀ x ∈ bases315Data, 157 ≤ x.1 ∧ x.1 ≤ 199 := by decide
    exact this _ hmem
  have hcop : Nat.Coprime 315 p4 := by
    rw [show (315 : ℕ) = 3 ^ 2 * 5 * 7 by norm_num]
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (((Nat.coprime_primes (by decide) hp4).mpr (by omega)).pow_left 2)
      ((Nat.coprime_primes (by decide) hp4).mpr (by omega)))
      ((Nat.coprime_primes (by decide) hp4).mpr (by omega))
  have hs315 : sigma 1 315 = 624 := by decide
  have hP0_eq' : P0 = properDivsSum (315 * p4) := by
    rw [properDivsSum_eq_sigma_sub, isMultiplicative_sigma.map_mul_of_coprime hcop, hs315]
    have hsp4 : sigma 1 p4 = p4 + 1 := by simpa [pow_one, ppSum_one hp4.two_le] using (ppSum_eq_sigma (a := 1) hp4).symm
    rw [hsp4]; have : 624 * (p4 + 1) = 624 * p4 + 624 := (by ring); omega
  obtain ⟨hcov0, hgap0, hbad0⟩ := core_of_checkCoreBadB (by decide : 1 ≤ 2) hP0_eq' hcore0
  have hnot_p4 : ¬ p4 ∣ 315 := hp4.coprime_iff_not_dvd.mp hcop.symm
  have hstep : (∀ y, 3 ≤ y → y ≤ properDivsSum (315 * p4 ^ d) - 3 → repNat (315 * p4 ^ d).properDivisors y) ∧
      (∀ k, k < properDivsSum (315 * p4 ^ d) → ∃ i, repNat (315 * p4 ^ d).properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    induction d with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simp only [zero_add, pow_one]; rw [← hP0_eq']; exact ⟨hcov0, hgap0⟩
      | succ k' =>
        obtain ⟨hc_k, hg_k⟩ := ih (by omega)
        have hsig_k : sigma 1 (p4 ^ (k' + 1) * 315) = ppSum p4 (k' + 1) * 624 := by
          rw [isMultiplicative_sigma.map_mul_of_coprime (hcop.symm.pow_left _), hs315, ← ppSum_eq_sigma hp4]
        have hpp_ge : p4 ^ (k' + 1) ≤ ppSum p4 (k' + 1) := by
          rw [ppSum_eq_sigma hp4, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
        have hP_ge : 309 * p4 ^ (k' + 1) ≤ properDivsSum (p4 ^ (k' + 1) * 315) := by
          rw [properDivsSum_eq_sigma_sub, hsig_k]
          have : 624 * p4 ^ (k' + 1) ≤ ppSum p4 (k' + 1) * 624 := by linarith [Nat.mul_le_mul_right 624 hpp_ge]
          omega
        have hpow_ge : 157 ≤ p4 ^ (k' + 1) := le_trans hp4_bd.1 (Nat.le_self_pow (by omega) p4)
        have hres := lift_prime_step_n_second (u := 315) (r := p4) (a := k' + 1) (L := 3) (g := 2)
          hp4 (by decide) (by omega) hnot_p4 (by decide) (by omega)
          (by rw [mul_comm]; exact hc_k) (by rw [mul_comm]; exact hg_k)
          (by have : p4 ^ (k' + 1) * p4 ≤ 199 * p4 ^ (k' + 1) := (by nlinarith); rw [pow_succ]; omega)
          (by have h1 : 157 * p4 ^ (k' + 1) ≤ p4 ^ (k' + 1) * p4 := by nlinarith
              have h2 : p4 ^ (k' + 1 + 1) = p4 ^ (k' + 1) * p4 := pow_succ p4 (k' + 1)
              rw [h2]; nlinarith [hP_ge, hpow_ge])
          (by
            intro x hx _
            have h1 := hasAbsGap_315 x hx
            have hm := Nat.mul_le_mul_left (p4 ^ (k' + 2)) h1
            have : 6 + 2 * p4 ^ (k' + 2) ≤ properDivsSum (p4 ^ (k' + 1) * 315) + p4 ^ (k' + 1) * 315 + 1 := by
              rw [pow_succ]; nlinarith
            linarith)
        rw [mul_comm] at hres; exact hres
  refine ⟨hstep.1, hstep.2, ?_, ?_⟩
  · intro x hx hnot
    obtain ⟨s, hs, hsum⟩ := hbad0 x hx hnot
    refine ⟨s, fun z hz => ?_, hsum⟩
    obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp (hs hz)
    have hdvd : 315 * p4 ∣ 315 * p4 ^ d := Nat.mul_dvd_mul_left 315 (dvd_pow_self p4 (by omega))
    exact Nat.mem_properDivisors.mpr ⟨h1.trans hdvd,
      lt_of_lt_of_le h2 (Nat.le_of_dvd (by have := hp4.pos; positivity) hdvd)⟩
  · rw [hP0_eq']
    exact properDivsSum_mono_dvd (by have := hp4.pos; positivity) (Nat.mul_dvd_mul_left 315 (dvd_pow_self p4 (by omega)))

/-- Lift 45 * 17^c * 19^d (only needed for a=2, b=1, p3=17, p4=19). -/
lemma lift_45_17_19 {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) :
    let B4 := 45 * 17 ^ c * 19 ^ d
    (∀ y, 12 ≤ y → y ≤ properDivsSum B4 - 12 → repNat B4.properDivisors y) ∧
    (∀ k, k < properDivsSum B4 → ∃ i, repNat B4.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
    (∀ x, x < 12 → x ∉ [2, 7, 11] → repNat B4.properDivisors x) ∧
    13545 ≤ properDivsSum B4 := by
  have hok := base45_17_19_ok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hcore0, habs19_b⟩, habs17_b⟩ := hok
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have h17p : Nat.Prime 17 := by decide
  have h19p : Nat.Prime 19 := by decide
  have hs45 : sigma 1 45 = 78 := by decide
  have hs17 : sigma 1 17 = 18 := by simpa [pow_one, ppSum_one h17p.two_le] using (ppSum_eq_sigma (a := 1) h17p).symm
  have hs19 : sigma 1 19 = 20 := by simpa [pow_one, ppSum_one h19p.two_le] using (ppSum_eq_sigma (a := 1) h19p).symm
  have hs45_19 : sigma 1 (45 * 19) = 1560 := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime 45 19), hs45, hs19]
    rfl
  have hs45_17 : sigma 1 (45 * 17) = 1404 := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime 45 17), hs45, hs17]
    rfl
  have hs45_17_19 : sigma 1 (45 * 17 * 19) = 28080 := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime (45 * 17) 19), hs45_17, hs19]
    rfl
  have hP0_eq : (13545 : ℕ) = properDivsSum (45 * 17 * 19) := by
    rw [properDivsSum_eq_sigma_sub, hs45_17_19]
  have hP45_19 : 78 * 20 - 45 * 19 = properDivsSum (45 * 19) := by
    rw [properDivsSum_eq_sigma_sub, hs45_19]
  have hP45_17 : 78 * 18 - 45 * 17 = properDivsSum (45 * 17) := by
    rw [properDivsSum_eq_sigma_sub, hs45_17]
  obtain ⟨hcov0, hgap0, hbad0⟩ := core_of_checkCoreBadB (by decide : 1 ≤ 2) hP0_eq hcore0
  have habs19 : HasAbsGap (45 * 19) 2 := hasAbsGap_of_list (by decide) hP45_19 habs19_b
  have habs17 : HasAbsGap (45 * 17) 2 := hasAbsGap_of_list (by decide) hP45_17 habs17_b
  have hstep1 : (∀ y, 12 ≤ y → y ≤ properDivsSum (45 * 17 ^ c * 19) - 12 → repNat (45 * 17 ^ c * 19).properDivisors y) ∧
      (∀ k, k < properDivsSum (45 * 17 ^ c * 19) → ∃ i, repNat (45 * 17 ^ c * 19).properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    induction c with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simp only [zero_add, pow_one]; rw [← hP0_eq]; exact ⟨hcov0, hgap0⟩
      | succ k' =>
        obtain ⟨hc_k, hg_k⟩ := ih (by omega)
        have hP_ge : 705 * 17 ^ (k' + 1) ≤ properDivsSum (17 ^ (k' + 1) * (45 * 19)) := by
          have hcop : Nat.Coprime (17 ^ (k' + 1)) (45 * 19) := (by decide : Nat.Coprime 17 (45 * 19)).pow_left _
          have hs : sigma 1 (17 ^ (k' + 1) * (45 * 19)) = ppSum 17 (k' + 1) * 1560 := by
            rw [isMultiplicative_sigma.map_mul_of_coprime hcop, ← ppSum_eq_sigma h17p, hs45_19]
          have hpp : 17 ^ (k' + 1) ≤ ppSum 17 (k' + 1) := by
            rw [ppSum_eq_sigma h17p, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
          have h1560 : 1560 * 17 ^ (k' + 1) ≤ ppSum 17 (k' + 1) * 1560 := by nlinarith
          rw [properDivsSum_eq_sigma_sub, hs]; omega
        have hpow : 17 ≤ 17 ^ (k' + 1) := Nat.le_self_pow (by omega) 17
        have heq_k : 17 ^ (k' + 1) * (45 * 19) = 45 * 17 ^ (k' + 1) * 19 := by ring
        have heq_k2 : 17 ^ (k' + 2) * (45 * 19) = 45 * 17 ^ (k' + 2) * 19 := by ring
        have h12le : 12 ≤ properDivsSum (17 ^ (k' + 1) * (45 * 19)) := by
          have := Nat.mul_le_mul_left 705 hpow; omega
        have hres := lift_prime_step_no_interleave (u := 45 * 19) (r := 17) (a := k' + 1) (L := 12) (g := 2)
          h17p (by decide) (by omega) (by decide) (by decide) h12le
          (by rw [heq_k]; exact hc_k) (by rw [heq_k]; exact hg_k)
          (by
            intro x hx
            have hm := Nat.mul_le_mul_left (17 ^ (k' + 2)) (habs19 x hx)
            change 24 + 17 ^ (k' + 2) * x ≤ properDivsSum (17 ^ (k' + 1) * (45 * 19)) + 17 ^ (k' + 2) * _ + 1
            have : 17 ^ (k' + 2) * 2 = 34 * 17 ^ (k' + 1) := by ring
            linarith)
          (by
            have hP4519 : properDivsSum (45 * 19) = 705 := by omega
            change 24 + 17 ^ (k' + 1) * (45 * 19) ≤ properDivsSum (17 ^ (k' + 1) * (45 * 19)) + 17 ^ (k' + 2) * properDivsSum (45 * 19) + 1
            rw [hP4519]; have : 17 ^ (k' + 2) * 705 = 11985 * 17 ^ (k' + 1) := by ring
            omega)
        rw [heq_k2] at hres; exact hres
  have habs_45_17c : HasAbsGap (45 * 17 ^ c) 2 := by
    clear hstep1
    induction c with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using habs17
      | succ k' =>
        have hprev := ih (by omega)
        let u := 45 * 17 ^ (k' + 1)
        have hu_pos : 0 < u := by positivity
        rw [show 45 * 17 ^ (k' + 2) = 17 * u by dsimp [u]; ring]
        apply HasAbsGap.mul_prime h17p hu_pos (dvd_mul_of_dvd_right (dvd_pow_self 17 (by omega)) 45) hprev
        · let ex := 17 ^ (k' + 2)
          have hex_dvd : ex ∣ 17 * u := ⟨45, by dsimp [ex, u]; ring⟩
          have hex_lt : ex < u := by dsimp [ex, u]; rw [pow_succ]; nlinarith [pow_pos h17p.pos (k' + 1)]
          have hex_not : ¬ ex ∣ u := by
            intro h; dsimp only [ex, u] at h
            rw [show 17 ^ (k' + 2) = 17 * 17 ^ (k' + 1) by ring] at h
            have : 17 ∣ 45 := (Nat.mul_dvd_mul_iff_right (pow_pos h17p.pos _)).mp h
            omega
          have hsum := extra_div_sum_ge h17p hex_dvd hex_lt hex_not
          have hs : sigma 1 u = 78 * ppSum 17 (k' + 1) := by
            rw [isMultiplicative_sigma.map_mul_of_coprime ((by decide : Nat.Coprime 45 17).pow_right _),
                hs45, ← ppSum_eq_sigma h17p]
          have hpp : 17 ^ (k' + 1) ≤ ppSum 17 (k' + 1) := by
            rw [ppSum_eq_sigma h17p, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
          have hP : properDivsSum u ≥ 33 * 17 ^ (k' + 1) := by
            have h78 : 78 * 17 ^ (k' + 1) ≤ 78 * ppSum 17 (k' + 1) := Nat.mul_le_mul_left 78 hpp
            rw [properDivsSum_eq_sigma_sub, hs]; dsimp [u]; omega
          have : ex = 17 * 17 ^ (k' + 1) := by dsimp [ex]; ring
          dsimp [u] at *; omega
        · intro d' hd' h17d'
          have hle := small_sum_ge_coprime h17p hu_pos d' hd' h17d' (S := {1, 3, 5, 9, 15, 45}) (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
            · exact ⟨one_dvd _, by decide, by decide⟩
            · exact ⟨(by decide : 3 ∣ 45).trans (dvd_mul_right _ _), by decide, by decide⟩
            · exact ⟨(by decide : 5 ∣ 45).trans (dvd_mul_right _ _), by decide, by decide⟩
            · exact ⟨(by decide : 9 ∣ 45).trans (dvd_mul_right _ _), by decide, by decide⟩
            · exact ⟨(by decide : 15 ∣ 45).trans (dvd_mul_right _ _), by decide, by decide⟩
            · exact ⟨dvd_mul_right _ _, by decide, by decide⟩)
          have hs : ∑ x ∈ ({1, 3, 5, 9, 15, 45} : Finset ℕ), x = 78 := by decide
          omega
  have hstep2 : (∀ y, 12 ≤ y → y ≤ properDivsSum (45 * 17 ^ c * 19 ^ d) - 12 → repNat (45 * 17 ^ c * 19 ^ d).properDivisors y) ∧
      (∀ k, k < properDivsSum (45 * 17 ^ c * 19 ^ d) → ∃ i, repNat (45 * 17 ^ c * 19 ^ d).properDivisors i ∧ k < i + 2 ∧ i ≤ k) := by
    let u := 45 * 17 ^ c
    have hu_pos : 0 < u := by positivity
    have hcop19 : Nat.Coprime 19 u := Nat.Coprime.mul_right (by decide) ((by decide : Nat.Coprime 19 17).pow_right c)
    induction d with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hstep1
      | succ k' =>
        obtain ⟨hc_k, hg_k⟩ := ih (by omega)
        have hPu_ge : 639 ≤ properDivsSum u := by
          have : 45 * 17 ∣ u := Nat.mul_dvd_mul_left 45 (dvd_pow_self 17 (by omega))
          have h1 : properDivsSum (45 * 17) = 639 := by omega
          rw [← h1]; exact properDivsSum_mono_dvd hu_pos this
        have hP_ge : 639 * 19 ^ (k' + 1) ≤ properDivsSum (19 ^ (k' + 1) * u) := by
          have hs : sigma 1 (19 ^ (k' + 1) * u) = ppSum 19 (k' + 1) * sigma 1 u := by
            rw [isMultiplicative_sigma.map_mul_of_coprime (hcop19.pow_left _), ← ppSum_eq_sigma h19p]
          have hpp : 19 ^ (k' + 1) ≤ ppSum 19 (k' + 1) := by
            rw [ppSum_eq_sigma h19p, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
          have hsu : u ≤ sigma 1 u := by
            rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
          rw [properDivsSum_eq_sigma_sub, hs]
          have hsub : 19 ^ (k' + 1) * (sigma 1 u - u) = 19 ^ (k' + 1) * sigma 1 u - 19 ^ (k' + 1) * u := Nat.mul_sub _ _ _
          have hle1 : 19 ^ (k' + 1) * sigma 1 u ≤ ppSum 19 (k' + 1) * sigma 1 u := Nat.mul_le_mul_right _ hpp
          have hle2 : 639 * 19 ^ (k' + 1) ≤ 19 ^ (k' + 1) * (sigma 1 u - u) := by
            rw [properDivsSum_eq_sigma_sub] at hPu_ge
            have := Nat.mul_le_mul_left (19 ^ (k' + 1)) hPu_ge; linarith
          have hle3 : 19 ^ (k' + 1) * u ≤ 19 ^ (k' + 1) * sigma 1 u := Nat.mul_le_mul_left _ hsu
          omega
        have hu_le_2Pu : u ≤ 2 * properDivsSum u := by
          have hs : sigma 1 u = 78 * ppSum 17 c := by
            rw [isMultiplicative_sigma.map_mul_of_coprime ((by decide : Nat.Coprime 45 17).pow_right c),
                hs45, ← ppSum_eq_sigma h17p]
          have hpp : 17 ^ c ≤ ppSum 17 c := by
            rw [ppSum_eq_sigma h17p, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
          have h78 : 78 * 17 ^ c ≤ 78 * ppSum 17 c := Nat.mul_le_mul_left 78 hpp
          rw [properDivsSum_eq_sigma_sub, hs]; dsimp [u]; omega
        have hpow : 19 ≤ 19 ^ (k' + 1) := Nat.le_self_pow (by omega) 19
        have heq_k : 19 ^ (k' + 1) * u = 45 * 17 ^ c * 19 ^ (k' + 1) := by dsimp [u]; ring
        have heq_k2 : 19 ^ (k' + 2) * u = 45 * 17 ^ c * 19 ^ (k' + 2) := by dsimp [u]; ring
        have h12le : 12 ≤ properDivsSum (19 ^ (k' + 1) * u) := by
          have := Nat.mul_le_mul_left 639 hpow; omega
        have hres := lift_prime_step_no_interleave (u := u) (r := 19) (a := k' + 1) (L := 12) (g := 2)
          h19p hu_pos (by omega) (h19p.coprime_iff_not_dvd.mp hcop19) (by decide) h12le
          (by rw [heq_k]; exact hc_k) (by rw [heq_k]; exact hg_k)
          (by
            intro x hx
            have hm := Nat.mul_le_mul_left (19 ^ (k' + 2)) (habs_45_17c x hx)
            change 24 + 19 ^ (k' + 2) * x ≤ properDivsSum (19 ^ (k' + 1) * u) + 19 ^ (k' + 2) * _ + 1
            have : 19 ^ (k' + 2) * 2 = 38 * 19 ^ (k' + 1) := by ring
            linarith)
          (by
            change 24 + 19 ^ (k' + 1) * u ≤ properDivsSum (19 ^ (k' + 1) * u) + 19 ^ (k' + 2) * properDivsSum u + 1
            have h1 := Nat.mul_le_mul_left (19 ^ (k' + 1)) hu_le_2Pu
            have h2 : 19 ^ (k' + 1) * (2 * properDivsSum u) ≤ 19 ^ (k' + 2) * properDivsSum u := by
              have : 19 ^ (k' + 2) * properDivsSum u = 19 ^ (k' + 1) * (19 * properDivsSum u) := by ring
              have := Nat.mul_le_mul_left (19 ^ (k' + 1)) (Nat.mul_le_mul_right (properDivsSum u) (by decide : 2 ≤ 19))
              linarith
            omega)
        rw [heq_k2] at hres; exact hres
  refine ⟨hstep2.1, hstep2.2, ?_, ?_⟩
  · intro x hx hnot
    obtain ⟨s, hs, hsum⟩ := hbad0 x hx hnot
    refine ⟨s, fun z hz => ?_, hsum⟩
    obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp (hs hz)
    have hdvd : 45 * 17 * 19 ∣ 45 * 17 ^ c * 19 ^ d :=
      Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 45 (dvd_pow_self 17 (by omega))) (dvd_pow_self 19 (by omega))
    exact Nat.mem_properDivisors.mpr ⟨h1.trans hdvd, lt_of_lt_of_le h2 (Nat.le_of_dvd (by positivity) hdvd)⟩
  · have hdvd : 45 * 17 * 19 ∣ 45 * 17 ^ c * 19 ^ d :=
      Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 45 (dvd_pow_self 17 (by omega))) (dvd_pow_self 19 (by omega))
    rw [hP0_eq]; exact properDivsSum_mono_dvd (by positivity) hdvd

-- Generic extra-divisor HasRelGap lift for multiplying by a prime power r^k (r | u0). -/
lemma hasRelGap_lift_one_prime {u0 r q d1 a_num a_den k : ℕ}
    (hr : r.Prime) (hu0 : 0 < u0) (hd1_gt : r < d1) (hd1_dvd : d1 ∣ u0) (hd1_cop : ¬ r ∣ d1)
    (hr_dvd : r ∣ u0)
    (hrel0 : HasRelGap u0 a_num a_den)
    (hmono : ∀ j, properDivsSum u0 * (r ^ j * u0) ≤ properDivsSum (r ^ j * u0) * u0)
    (hreq : a_den * (2 * u0 * d1) ≤ a_den * (sigma 1 u0 * d1 + r * u0) + r * a_num * u0 * d1) :
    HasRelGap (r ^ k * u0) a_num a_den := by
  induction k with
  | zero => simpa using hrel0
  | succ j ih =>
    let u := r ^ j * u0
    have hu_pos : 0 < u := by have := hr.pos; positivity
    rw [show r ^ (j + 1) * u0 = r * u by dsimp [u]; ring]
    obtain ⟨w, hw⟩ := hd1_dvd
    have hd1_pos : 0 < d1 := by omega
    let ex := r * (r ^ j * w)
    have hmul_ex : d1 * ex = r * u := by dsimp [ex, u]; rw [hw]; ring
    have hex_dvd : ex ∣ r * u := ⟨d1, by rw [mul_comm ex d1, hmul_ex]⟩
    have hex_lt : ex < u := by nlinarith
    have hex_not : ¬ ex ∣ u := by
      intro h
      -- v_r(r * r^j * w) > v_r(r^j * u0) since r nmid d1 and d1 * w = u0 => v_r(w) = v_r(u0)!
      have hu0_ne : u0 ≠ 0 := hu0.ne'
      have hw_ne : w ≠ 0 := fun h0 => by rw [h0, mul_zero] at hw; exact hu0_ne hw
      have hd1_ne : d1 ≠ 0 := by omega
      have hfu : u.factorization r = j + u0.factorization r := by
        dsimp [u]; rw [Nat.factorization_mul (pow_pos hr.pos j).ne' hu0_ne, Finsupp.add_apply,
          hr.factorization_pow, Finsupp.single_eq_same]
      have hfw : w.factorization r = u0.factorization r := by
        have h1 := congrArg (fun n => n.factorization r) hw
        rw [Nat.factorization_mul hd1_ne hw_ne, Finsupp.add_apply] at h1
        have h0 : d1.factorization r = 0 := Nat.factorization_eq_zero_of_not_dvd hd1_cop
        omega
      have hfex : ex.factorization r = j + 1 + u0.factorization r := by
        dsimp [ex]
        have hex0 : r ^ j * w ≠ 0 := mul_ne_zero (pow_pos hr.pos j).ne' hw_ne
        rw [Nat.factorization_mul hr.ne_zero hex0, Finsupp.add_apply, hr.factorization_self,
            Nat.factorization_mul (pow_pos hr.pos j).ne' hw_ne, Finsupp.add_apply,
            hr.factorization_pow, Finsupp.single_eq_same, hfw]; omega
      have hex_ne : ex ≠ 0 := mul_ne_zero hr.ne_zero (mul_ne_zero (pow_pos hr.pos j).ne' hw_ne)
      have hle := (Nat.factorization_le_iff_dvd hex_ne hu_pos.ne').mpr h r
      omega
    apply HasRelGap.mul_prime_extra hr hu_pos ih hex_dvd hex_lt hex_not
    have hPu0 : sigma 1 u0 = properDivsSum u0 + u0 := by
      rw [properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    have h1 : a_den * u0 * d1 ≤ a_num * (r * u0) * d1 + a_den * (r * u0 + properDivsSum u0 * d1) := by
      rw [hPu0] at hreq; linarith
    have hm1 := Nat.mul_le_mul_right u h1
    have hm2 : a_den * d1 * (properDivsSum u0 * u) ≤ a_den * d1 * (properDivsSum u * u0) :=
      Nat.mul_le_mul_left (a_den * d1) (hmono j)
    have hstep : (a_den * u) * (u0 * d1) ≤ (a_num * (r * u) + a_den * (ex + properDivsSum u)) * (u0 * d1) := by
      have hA : a_den * ex * (u0 * d1) = a_den * (r * u) * u0 := by
        calc a_den * ex * (u0 * d1) = a_den * (d1 * ex) * u0 := by ring
          _ = a_den * (r * u) * u0 := by rw [hmul_ex]
      have hB : a_num * (r * u0) * d1 * u = a_num * (r * u) * (u0 * d1) := by ring
      have hC : a_den * u0 * d1 * u = (a_den * u) * (u0 * d1) := by ring
      have hD : a_den * (r * u0 + properDivsSum u0 * d1) * u = a_den * (r * u) * u0 + a_den * d1 * (properDivsSum u0 * u) := by ring
      have hE : a_den * d1 * (properDivsSum u * u0) = a_den * properDivsSum u * (u0 * d1) := by ring
      have hF : (a_num * (r * u) + a_den * (ex + properDivsSum u)) * (u0 * d1) =
          a_num * (r * u) * (u0 * d1) + a_den * ex * (u0 * d1) + a_den * properDivsSum u * (u0 * d1) := by ring
      have hG : (a_num * (r * u0) * d1 + a_den * (r * u0 + properDivsSum u0 * d1)) * u =
          a_num * (r * u0) * d1 * u + a_den * (r * u0 + properDivsSum u0 * d1) * u := by ring
      linarith
    exact Nat.le_of_mul_le_mul_right hstep (by positivity)

-- Lift solid core [L, P - L] and gap g for all 19 triples of 5 nmid m.
set_option maxHeartbeats 2400000 in
lemma lift_no5_full {p2 p3 p4 q0 L g P0 a2 a3 a4 a b c d : ℕ} {bad ds ds2 ds3 ds4 : List ℕ}
    (hmem : (p2, p3, p4, q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4) ∈ basesNo5Data)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    let B := 3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d
    (∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y) ∧
    (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + g ∧ i ≤ k) ∧
    (∀ x, x < L → x ∉ bad → repNat B.properDivisors x) ∧
    P0 ≤ properDivsSum B ∧ (2 * g + 1) * (2 * L + 8 * g + 8) ≤ properDivsSum B ∧
    1 ≤ L ∧ 1 ≤ g := by
  have h3p : Nat.Prime 3 := by decide
  have hprimes : p2.Prime ∧ p3.Prime ∧ p4.Prime ∧ 7 ≤ p2 ∧ p2 < p3 ∧ p3 < p4 := by
    have : ∀ x ∈ basesNo5Data, x.1.Prime ∧ x.2.1.Prime ∧ x.2.2.1.Prime ∧ 7 ≤ x.1 ∧ x.1 < x.2.1 ∧ x.2.1 < x.2.2.1 := by decide
    exact this _ hmem
  obtain ⟨hp2, hp3, hp4, h7p2, hp23, hp34⟩ := hprimes
  have hok := List.all_eq_true.mp basesNo5Data_ok _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hmeta, hcore0⟩, hrg2_b⟩, hrg3_b⟩, hrg4_b⟩ := hok
  obtain ⟨hL1, hg1, hP0_eq, hbig0,
    hst1_d, hst1_n,
    hst2_d, hst2_n, hst2_g3,
    hst3_d, hst3_n, hst3_g3, hst3_gp2,
    hst4_d, hst4_n, hst4_g3, hst4_gp2, hst4_gp3⟩ := hmeta
  let B0 := 9 * p2 * p3 * p4
  have hB0_pos : 0 < B0 := by have := hp2.pos; have := hp3.pos; have := hp4.pos; dsimp [B0]; positivity
  have hsB0 : sigma 1 B0 = 13 * (p2 + 1) * (p3 + 1) * (p4 + 1) := by
    have h := sigma_mul_coprime_four h3p hp2 hp3 hp4 (by omega) hp23 hp34 (a := 2) (b := 1) (c := 1) (d := 1)
    rw [ppSum_one hp2.two_le, ppSum_one hp3.two_le, ppSum_one hp4.two_le, (by decide : ppSum 3 2 = 13)] at h
    simpa [B0] using h
  have hP0_eq' : P0 = properDivsSum B0 := by rw [properDivsSum_eq_sigma_sub, hsB0]; omega
  obtain ⟨hcov0, hgap0, hbad0⟩ := core_of_checkCoreBadB hg1 hP0_eq' hcore0
  have hL_le_P0 : L ≤ P0 := by omega
  -- Helper: scaling step from base B0 to any n >= B0 with ratio mono
  -- Step 1: lift 3 from 2 to a (u = p2 * p3 * p4 constant)
  have hstep1 : (∀ y, L ≤ y → y ≤ properDivsSum (3 ^ a * p2 * p3 * p4) - L → repNat (3 ^ a * p2 * p3 * p4).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ a * p2 * p3 * p4) → ∃ i, repNat (3 ^ a * p2 * p3 * p4).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
    let u := p2 * p3 * p4
    have hu_pos : 0 < u := by have := hp2.pos; have := hp3.pos; have := hp4.pos; dsimp [u]; positivity
    have hcop : ¬ 3 ∣ u := by
      have hc : Nat.Coprime 3 u := Nat.Coprime.mul_right (Nat.Coprime.mul_right
        ((Nat.coprime_primes h3p hp2).mpr (by omega)) ((Nat.coprime_primes h3p hp3).mpr (by omega)))
        ((Nat.coprime_primes h3p hp4).mpr (by omega))
      exact h3p.coprime_iff_not_dvd.mp hc
    have hPu_eq : properDivsSum u = (p2 + 1) * (p3 + 1) * (p4 + 1) - u := by
      have hs : sigma 1 u = (p2 + 1) * (p3 + 1) * (p4 + 1) := by
        simpa [u, pow_one, ppSum_one hp2.two_le, ppSum_one hp3.two_le, ppSum_one hp4.two_le] using
          sigma_mul_coprime_three hp2 hp3 hp4 hp23 hp34 (a := 1) (b := 1) (c := 1)
      rw [properDivsSum_eq_sigma_sub, hs]
    induction a with
    | zero => omega
    | succ k ih =>
      by_cases hk : k < 2
      · have : k + 1 = 2 := (by omega); rw [this]; have h32 : (3 ^ 2 : ℕ) = 9 := rfl; rw [h32]
        dsimp only [B0] at hcov0 hgap0 hP0_eq'; rw [← hP0_eq']; exact ⟨hcov0, hgap0⟩
      · obtain ⟨hc_k, hg_k⟩ := ih (by omega)
        have hratio := properDivsSum_ratio_mono_4p h3p hp2 hp3 hp4 (by omega) hp23 hp34 (show 2 ≤ k by omega) le_rfl le_rfl le_rfl (b0 := 1) (c0 := 1) (d0 := 1)
        have h9le : 9 ≤ 3 ^ k := by have := pow_le_pow_right₀ (by decide : 1 ≤ 3) (show 2 ≤ k by omega); norm_num at this; exact this
        have hPk_ge : P0 * 3 ^ k ≤ properDivsSum (3 ^ k * u) * 9 := by
          have : properDivsSum B0 * (3 ^ k * u) ≤ properDivsSum (3 ^ k * u) * B0 := by
            simpa [B0, u, mul_assoc] using hratio
          have : P0 * (3 ^ k * u) ≤ properDivsSum (3 ^ k * u) * (9 * u) := by rw [hP0_eq']; simpa [B0, u, mul_assoc] using this
          exact Nat.le_of_mul_le_mul_right (by linarith) hu_pos
        have hPk_ge_P0 : P0 ≤ properDivsSum (3 ^ k * u) := by nlinarith
        have heq_k : 3 ^ k * u = 3 ^ k * p2 * p3 * p4 := by dsimp [u]; ring
        have heq_k1 : 3 ^ (k + 1) * u = 3 ^ (k + 1) * p2 * p3 * p4 := by dsimp [u]; ring
        have hres := lift_prime_step_no_interleave (u := u) (r := 3) (a := k) (L := L) (g := g)
          h3p hu_pos (by omega) hcop hg1 (le_trans hL_le_P0 hPk_ge_P0)
          (by rw [heq_k]; exact hc_k) (by rw [heq_k]; exact hg_k)
          (by
            intro x hx
            have hx_le : p2 * x ≤ u := by
              obtain ⟨⟨t, ht⟩, hlt⟩ := Nat.mem_properDivisors.mp hx
              have ht1 : 1 < t := by by_contra! h; have : t = 0 ∨ t = 1 := (by omega); rcases this with rfl | rfl <;> simp_all
              have htp2 : p2 ≤ t := by
                by_contra! htl
                have hm := Nat.minFac_prime (by omega : t ≠ 1)
                have hdvd : t.minFac ∣ p2 * p3 * p4 := (Nat.minFac_dvd t).trans ⟨x, by dsimp [u] at ht; linarith⟩
                have hlt_mf : t.minFac < p2 := lt_of_le_of_lt (Nat.minFac_le (by omega)) htl
                rcases hm.dvd_mul.mp hdvd with h12 | h4
                · rcases hm.dvd_mul.mp h12 with h2' | h3'
                  · rcases hp2.eq_one_or_self_of_dvd _ h2' with h1 | h2
                    · exact hm.ne_one h1
                    · rw [h2] at hlt_mf; omega
                  · rcases hp3.eq_one_or_self_of_dvd _ h3' with h1 | h2
                    · exact hm.ne_one h1
                    · rw [h2] at hlt_mf; omega
                · rcases hp4.eq_one_or_self_of_dvd _ h4 with h1 | h2
                  · exact hm.ne_one h1
                  · rw [h2] at hlt_mf; omega
              calc p2 * x ≤ t * x := Nat.mul_le_mul_right x htp2
                _ = u := by rw [ht, mul_comm]
            have h1 : p2 * (2 * L) + 27 * u ≤ p2 * (P0 + 1) := hst1_d
            have hm1 := Nat.mul_le_mul_right (3 ^ k) h1
            have ha1 : 3 ^ (k + 1) * u * 9 = 27 * u * 3 ^ k := by ring
            have h3 : (p2 * (2 * L + 3 ^ (k + 1) * x)) * 9 ≤ (p2 * (properDivsSum (3 ^ k * u) + 1)) * 9 := by
              have hx1 : p2 * (3 ^ (k + 1) * x) ≤ 3 ^ (k + 1) * u := by
                calc p2 * (3 ^ (k + 1) * x) = 3 ^ (k + 1) * (p2 * x) := by ring
                  _ ≤ 3 ^ (k + 1) * u := Nat.mul_le_mul_left _ hx_le
              have hx2 := Nat.mul_le_mul_right 9 hx1
              have hP1 := Nat.mul_le_mul_left p2 hPk_ge
              have hL1' : p2 * (2 * L - 1) * 9 + p2 * 3 ^ k ≤ p2 * (2 * L) * 3 ^ k := by
                have : p2 * (2 * L - 1) * 9 ≤ p2 * (2 * L - 1) * 3 ^ k := Nat.mul_le_mul_left _ h9le
                have : p2 * (2 * L - 1) + p2 = p2 * (2 * L) := by
                  have : (2 * L - 1) + 1 = 2 * L := by omega
                  calc p2 * (2 * L - 1) + p2 = p2 * ((2 * L - 1) + 1) := by ring
                    _ = p2 * (2 * L) := by rw [this]
                have : (p2 * (2 * L - 1) + p2) * 3 ^ k = p2 * (2 * L) * 3 ^ k := by rw [this]
                linarith
              have hL2' : p2 * (2 * L) * 9 = p2 * (2 * L - 1) * 9 + p2 * 9 := by
                have : (2 * L - 1) + 1 = 2 * L := by omega
                calc p2 * (2 * L) * 9 = p2 * ((2 * L - 1) + 1) * 9 := by rw [this]
                  _ = p2 * (2 * L - 1) * 9 + p2 * 9 := by ring
              have hP2 : p2 * (P0 + 1) * 3 ^ k = p2 * (P0 * 3 ^ k) + p2 * 3 ^ k := by ring
              have hP3 : p2 * (properDivsSum (3 ^ k * u) * 9) = p2 * properDivsSum (3 ^ k * u) * 9 := by ring
              have hM1 : (p2 * (2 * L) + 27 * u) * 3 ^ k = p2 * (2 * L) * 3 ^ k + 27 * u * 3 ^ k := by ring
              have hM2 : (p2 * (2 * L + 3 ^ (k + 1) * x)) * 9 = p2 * (2 * L) * 9 + p2 * (3 ^ (k + 1) * x) * 9 := by ring
              have hM3 : (p2 * (properDivsSum (3 ^ k * u) + 1)) * 9 = p2 * properDivsSum (3 ^ k * u) * 9 + p2 * 9 := by ring
              linarith
            have h4 : 2 * L + 3 ^ (k + 1) * x ≤ properDivsSum (3 ^ k * u) + 1 := by
              have := Nat.le_of_mul_le_mul_right h3 (by decide : 0 < 9)
              exact Nat.le_of_mul_le_mul_left this hp2.pos
            change 2 * L + 3 ^ (k + 1) * x ≤ properDivsSum (3 ^ k * u) + _ + 1
            omega)
          (by
            have h1 : 2 * L + 9 * u ≤ P0 + 27 * properDivsSum u + 1 := by
              rw [hPu_eq]; simpa [B0, u, mul_assoc] using hst1_n
            have hm1 := Nat.mul_le_mul_right (3 ^ k) h1
            have h2 : (2 * L + 3 ^ k * u) * 9 ≤ (properDivsSum (3 ^ k * u) + 3 ^ (k + 1) * properDivsSum u + 1) * 9 := by
              have ha1 : 3 ^ (k + 1) * properDivsSum u * 9 = 27 * properDivsSum u * 3 ^ k := by ring
              have ha2 : 3 ^ k * u * 9 = 9 * u * 3 ^ k := by ring
              have hL1' : (2 * L - 1) * 9 + 3 ^ k ≤ 2 * L * 3 ^ k := by
                have := Nat.mul_le_mul_left (2 * L - 1) h9le
                have : ((2 * L - 1) + 1) * 3 ^ k = 2 * L * 3 ^ k := by congr 1; omega
                linarith
              have hL2' : 2 * L * 9 = (2 * L - 1) * 9 + 9 := by
                have : ((2 * L - 1) + 1) * 9 = 2 * L * 9 := by congr 1; omega
                linarith
              linarith
            change 2 * L + 3 ^ k * u ≤ properDivsSum (3 ^ k * u) + 3 ^ (k + 1) * properDivsSum u + 1
            exact Nat.le_of_mul_le_mul_right h2 (by decide : 0 < 9))
        rw [heq_k1] at hres; exact hres
  -- Step 2: lift p2 from 1 to b (u2_a = 3^a * p3 * p4, HasRelGap a2 1000 via growing 3 with d1=p3)
  let u2_0 := 9 * p3 * p4
  have hs_u2_0 : sigma 1 u2_0 = 13 * (p3 + 1) * (p4 + 1) := by
    have h := sigma_mul_coprime_three h3p hp3 hp4 (by omega) hp34 (a := 2) (b := 1) (c := 1)
    rw [(by decide : ppSum 3 2 = 13), ppSum_one hp3.two_le, ppSum_one hp4.two_le] at h
    simpa [u2_0] using h
  have hrel_u2_0 : HasRelGap u2_0 a2 1000 := hasRelGap_of_list (by have := hp3.pos; have := hp4.pos; dsimp [u2_0]; positivity)
    (by rw [properDivsSum_eq_sigma_sub, hs_u2_0]) hrg2_b
  have hrel_u2 : HasRelGap (3 ^ a * p3 * p4) a2 1000 := by
    have h := hasRelGap_lift_one_prime (u0 := u2_0) (r := 3) (q := 0) (d1 := p3) (a_num := a2) (a_den := 1000) (k := a - 2)
      h3p (by have := hp3.pos; have := hp4.pos; dsimp [u2_0]; positivity) (by omega)
      (dvd_mul_of_dvd_left (dvd_mul_left p3 9) p4) (h3p.coprime_iff_not_dvd.mp ((Nat.coprime_primes h3p hp3).mpr (by omega)))
      ((by decide : 3 ∣ 9).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))) hrel_u2_0
      (fun j => by
        have hm := properDivsSum_ratio_mono_3p h3p hp3 hp4 (by omega) hp34 (show 2 ≤ j + 2 by omega) le_rfl le_rfl (b0 := 1) (c0 := 1)
        have : 3 ^ (j + 2) * p3 ^ 1 * p4 ^ 1 = 3 ^ j * u2_0 := by dsimp [u2_0]; rw [pow_add]; ring
        rw [this] at hm; simpa [u2_0] using hm)
      (by rw [hs_u2_0]; exact hst2_g3)
    have : 3 ^ (a - 2) * u2_0 = 3 ^ a * p3 * p4 := by
      dsimp [u2_0]; rw [show 3 ^ a = 3 ^ (a - 2) * 3 ^ 2 by rw [← pow_add]; congr 1; omega]; ring
    rwa [this] at h
  have hstep2 : (∀ y, L ≤ y → y ≤ properDivsSum (3 ^ a * p2 ^ b * p3 * p4) - L → repNat (3 ^ a * p2 ^ b * p3 * p4).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ a * p2 ^ b * p3 * p4) → ∃ i, repNat (3 ^ a * p2 ^ b * p3 * p4).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
    let u := 3 ^ a * p3 * p4
    have hu_pos : 0 < u := by have := hp3.pos; have := hp4.pos; dsimp [u]; positivity
    have hcop : ¬ p2 ∣ u := by
      have hc : Nat.Coprime p2 u := Nat.Coprime.mul_right (Nat.Coprime.mul_right
        (((Nat.coprime_primes hp2 h3p).mpr (by omega)).pow_right a) ((Nat.coprime_primes hp2 hp3).mpr (by omega)))
        ((Nat.coprime_primes hp2 hp4).mpr (by omega))
      exact hp2.coprime_iff_not_dvd.mp hc
    induction b with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hstep1
      | succ k' =>
        obtain ⟨hc_k, hg_k⟩ := ih (by omega)
        have hratio_B : properDivsSum B0 * (p2 ^ (k' + 1) * u) ≤ properDivsSum (p2 ^ (k' + 1) * u) * B0 := by
          have h := properDivsSum_ratio_mono_4p h3p hp2 hp3 hp4 (by omega) hp23 hp34 ha (show 1 ≤ k' + 1 by omega) le_rfl le_rfl (c0 := 1) (d0 := 1)
          simpa [B0, u, mul_comm, mul_left_comm, mul_assoc] using h
        have hratio_u : properDivsSum u2_0 * u ≤ properDivsSum u * u2_0 := by
          have h := properDivsSum_ratio_mono_3p h3p hp3 hp4 (by omega) hp34 ha le_rfl le_rfl (b0 := 1) (c0 := 1)
          simpa [u2_0, u] using h
        have hB0_le : B0 ≤ p2 ^ (k' + 1) * u := by
          have : B0 ∣ p2 ^ (k' + 1) * u := by
            have h1 : 3 ^ 2 * p2 ^ 1 * p3 * p4 ∣ 3 ^ a * p2 ^ (k' + 1) * p3 * p4 :=
              Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right (Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow p2 (by omega))) p3) p4
            simpa [B0, u, mul_comm, mul_left_comm, mul_assoc] using h1
          exact Nat.le_of_dvd (by have := hp2.pos; positivity) this
        have hPk_ge : P0 ≤ properDivsSum (p2 ^ (k' + 1) * u) := by
          rw [hP0_eq']
          have : B0 ∣ p2 ^ (k' + 1) * u := by
            have h1 : 3 ^ 2 * p2 ^ 1 * p3 * p4 ∣ 3 ^ a * p2 ^ (k' + 1) * p3 * p4 :=
              Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right (Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow p2 (by omega))) p3) p4
            simpa [B0, u, mul_comm, mul_left_comm, mul_assoc] using h1
          exact properDivsSum_mono_dvd (by have := hp2.pos; positivity) this
        have heq_k : p2 ^ (k' + 1) * u = 3 ^ a * p2 ^ (k' + 1) * p3 * p4 := by dsimp [u]; ring
        have heq_k2 : p2 ^ (k' + 2) * u = 3 ^ a * p2 ^ (k' + 2) * p3 * p4 := by dsimp [u]; ring
        have hres := lift_prime_step_no_interleave (u := u) (r := p2) (a := k' + 1) (L := L) (g := g)
          hp2 hu_pos (by omega) hcop hg1 (le_trans hL_le_P0 hPk_ge)
          (by rw [heq_k]; exact hc_k)
          (by rw [heq_k]; exact hg_k)
          (by
            intro x hx
            have hrg := hrel_u2 x hx
            have hscale : (1000 * (2 * L) + p2 ^ (k' + 2) * a2 * u) * B0 ≤ (1000 * (properDivsSum (p2 ^ (k' + 1) * u) + 1)) * B0 := by
              change 1000 * (2 * L) + p2 * p2 * a2 * u2_0 ≤ 1000 * (P0 + 1) at hst2_d
              have h1 := Nat.mul_le_mul_right (p2 ^ (k' + 1) * u) hst2_d
              have h2 : p2 ^ (k' + 2) * a2 * u * B0 = p2 * p2 * a2 * u2_0 * (p2 ^ (k' + 1) * u) := by dsimp [B0, u2_0]; ring
              have h3 : 1000 * (2 * L) * B0 ≤ 1000 * (2 * L) * (p2 ^ (k' + 1) * u) := Nat.mul_le_mul_left _ hB0_le
              have h4 : 1000 * (P0 * (p2 ^ (k' + 1) * u)) ≤ 1000 * (properDivsSum (p2 ^ (k' + 1) * u) * B0) := by
                rw [hP0_eq']; exact Nat.mul_le_mul_left 1000 hratio_B
              -- Wait: hst2_d has P0 + 1 on RHS, and 1000 * (P0 + 1) * (p2^(k'+1)*u) might exceed 1000*(P+1)*B0 by 1000*(n - B0)!
              -- Check! Actually hst2_d holds with P0 (without +1) because budget had >0 margin! Wait: let's check P0 vs P0+1!
              -- Even simpler: (1000 * (2*L)) + p2^2 * a2 * u2_0 <= 1000 * P0 + 1000; if we prove 1000*(2*L) <= 1000*(2*L)*(n/B0) and 1000 <= 1000*n/B0:
              -- No! 1000 * 1 * (n / B0) = 1000 * (n / B0) > 1000! Wait: 2*L >= 2 => 1000 * (2*L - 1) >= 1000!!
              have hL2 : 2000 ≤ 1000 * (2 * L) := by omega
              have hL1' : (1000 * (2 * L - 1)) * B0 + 1000 * (p2 ^ (k' + 1) * u) ≤ 1000 * (2 * L) * (p2 ^ (k' + 1) * u) := by
                have ha1 := Nat.mul_le_mul_left (1000 * (2 * L - 1)) hB0_le
                have ha2 : (1000 * (2 * L - 1) + 1000) * (p2 ^ (k' + 1) * u) = 1000 * (2 * L) * (p2 ^ (k' + 1) * u) := by congr 1; omega
                linarith
              have hL2' : 1000 * (2 * L) * B0 = 1000 * (2 * L - 1) * B0 + 1000 * B0 := by
                have : (1000 * (2 * L - 1) + 1000) * B0 = 1000 * (2 * L) * B0 := by congr 1; omega
                linarith
              have hX1 : (1000 * (2 * L) + p2 * p2 * a2 * u2_0) * (p2 ^ (k' + 1) * u) = 1000 * (2 * L) * (p2 ^ (k' + 1) * u) + p2 * p2 * a2 * u2_0 * (p2 ^ (k' + 1) * u) := by ring
              have hX2 : 1000 * (P0 + 1) * (p2 ^ (k' + 1) * u) = 1000 * (P0 * (p2 ^ (k' + 1) * u)) + 1000 * (p2 ^ (k' + 1) * u) := by ring
              have hX3 : (1000 * (2 * L) + p2 ^ (k' + 2) * a2 * u) * B0 = 1000 * (2 * L) * B0 + p2 ^ (k' + 2) * a2 * u * B0 := by ring
              have hX4 : 1000 * (properDivsSum (p2 ^ (k' + 1) * u) + 1) * B0 = 1000 * (properDivsSum (p2 ^ (k' + 1) * u) * B0) + 1000 * B0 := by ring
              have hX5 : (1000 * (2 * L - 1)) * B0 = 1000 * (2 * L - 1) * B0 := by ring
              linarith
            have hbud := Nat.le_of_mul_le_mul_right hscale hB0_pos
            change 1000 * (2 * L) + p2 ^ (k' + 2) * a2 * u ≤ 1000 * (properDivsSum (p2 ^ (k' + 1) * u) + 1) at hbud
            let S := ∑ e ∈ u.properDivisors.filter (· < x), e
            change 1000 * x ≤ a2 * u + 1000 * S at hrg
            have hm := Nat.mul_le_mul_left (p2 ^ (k' + 2)) hrg
            have hM1 : p2 ^ (k' + 2) * (1000 * x) = 1000 * (p2 ^ (k' + 2) * x) := by ring
            have hM2 : p2 ^ (k' + 2) * (a2 * u + 1000 * S) = p2 ^ (k' + 2) * a2 * u + 1000 * (p2 ^ (k' + 2) * S) := by ring
            have hM3 : 1000 * (properDivsSum (p2 ^ (k' + 1) * u) + 1) = 1000 * properDivsSum (p2 ^ (k' + 1) * u) + 1000 := by ring
            change 2 * L + p2 ^ (k' + 2) * x ≤ properDivsSum (p2 ^ (k' + 1) * u) + p2 ^ (k' + 2) * S + 1
            linarith)
          (by
            have hPu2 : 13 * (p3 + 1) * (p4 + 1) - u2_0 = properDivsSum u2_0 := by rw [properDivsSum_eq_sigma_sub, hs_u2_0]
            rw [hPu2] at hst2_n
            have hscale : (2 * L + p2 ^ (k' + 1) * u) * B0 ≤
                (properDivsSum (p2 ^ (k' + 1) * u) + p2 ^ (k' + 2) * properDivsSum u + 1) * B0 := by
              change 2 * L + B0 ≤ P0 + p2 * p2 * properDivsSum u2_0 + 1 at hst2_n
              have h1 := Nat.mul_le_mul_right (p2 ^ (k' + 1) * u) hst2_n
              have h2 : p2 ^ (k' + 2) * properDivsSum u2_0 * u * p2 = p2 * p2 * properDivsSum u2_0 * (p2 ^ (k' + 1) * u) := by ring
              have h3 : p2 ^ (k' + 2) * p2 * (properDivsSum u2_0 * u) ≤ p2 ^ (k' + 2) * p2 * (properDivsSum u * u2_0) :=
                Nat.mul_le_mul_left _ hratio_u
              have h4 : p2 ^ (k' + 2) * p2 * (properDivsSum u * u2_0) = p2 ^ (k' + 2) * properDivsSum u * B0 := by
                dsimp [B0, u2_0]; ring
              have h5 : (2 * L - 1) * B0 + (p2 ^ (k' + 1) * u) ≤ 2 * L * (p2 ^ (k' + 1) * u) := by
                have ha1 := Nat.mul_le_mul_left (2 * L - 1) hB0_le
                have ha2 : ((2 * L - 1) + 1) * (p2 ^ (k' + 1) * u) = 2 * L * (p2 ^ (k' + 1) * u) := by congr 1; omega
                linarith
              have h6 : 2 * L * B0 = (2 * L - 1) * B0 + B0 := by
                have : ((2 * L - 1) + 1) * B0 = 2 * L * B0 := by congr 1; omega
                linarith
              have h7 : p2 ^ (k' + 2) * p2 * (properDivsSum u2_0 * u) = p2 * p2 * properDivsSum u2_0 * (p2 ^ (k' + 1) * u) := by ring
              have h8 : (2 * L + B0) * (p2 ^ (k' + 1) * u) = 2 * L * (p2 ^ (k' + 1) * u) + (p2 ^ (k' + 1) * u) * B0 := by ring
              have h9 : (P0 + p2 * p2 * properDivsSum u2_0 + 1) * (p2 ^ (k' + 1) * u) = P0 * (p2 ^ (k' + 1) * u) + p2 * p2 * properDivsSum u2_0 * (p2 ^ (k' + 1) * u) + (p2 ^ (k' + 1) * u) := by ring
              have hP0_mul : P0 * (p2 ^ (k' + 1) * u) = properDivsSum B0 * (p2 ^ (k' + 1) * u) := by rw [hP0_eq']
              have h10 : (2 * L + p2 ^ (k' + 1) * u) * B0 = 2 * L * B0 + (p2 ^ (k' + 1) * u) * B0 := by ring
              have h11 : (properDivsSum (p2 ^ (k' + 1) * u) + p2 ^ (k' + 2) * properDivsSum u + 1) * B0 = properDivsSum (p2 ^ (k' + 1) * u) * B0 + p2 ^ (k' + 2) * properDivsSum u * B0 + B0 := by ring
              linarith
            change 2 * L + p2 ^ (k' + 1) * u ≤ properDivsSum (p2 ^ (k' + 1) * u) + p2 ^ (k' + 2) * properDivsSum u + 1
            exact Nat.le_of_mul_le_mul_right hscale hB0_pos)
        rw [heq_k2] at hres; exact hres
  -- Step 3: lift p3 from 1 to c (u3 = 3^a * p2^b * p4, HasRelGap a3 1000 via growing 3 (d1=p2) and p2 (d1=dp2_3))
  let u3_0 := 9 * p2 * p4
  have hs_u3_0 : sigma 1 u3_0 = 13 * (p2 + 1) * (p4 + 1) := by
    have h := sigma_mul_coprime_three h3p hp2 hp4 (by omega) (lt_trans hp23 hp34) (a := 2) (b := 1) (c := 1)
    rw [(by decide : ppSum 3 2 = 13), ppSum_one hp2.two_le, ppSum_one hp4.two_le] at h
    simpa [u3_0] using h
  have hrel_u3_0 : HasRelGap u3_0 a3 1000 := hasRelGap_of_list (by have := hp2.pos; have := hp4.pos; dsimp [u3_0]; positivity)
    (by rw [properDivsSum_eq_sigma_sub, hs_u3_0]) hrg3_b
  have hrel_u3_a : HasRelGap (3 ^ a * p2 * p4) a3 1000 := by
    have h := hasRelGap_lift_one_prime (u0 := u3_0) (r := 3) (q := 0) (d1 := p2) (a_num := a3) (a_den := 1000) (k := a - 2)
      h3p (by have := hp2.pos; have := hp4.pos; dsimp [u3_0]; positivity) (by omega)
      (dvd_mul_of_dvd_left (dvd_mul_left p2 9) p4) (h3p.coprime_iff_not_dvd.mp ((Nat.coprime_primes h3p hp2).mpr (by omega)))
      ((by decide : 3 ∣ 9).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))) hrel_u3_0
      (fun j => by
        have hm := properDivsSum_ratio_mono_3p h3p hp2 hp4 (by omega) (lt_trans hp23 hp34) (show 2 ≤ j + 2 by omega) le_rfl le_rfl (b0 := 1) (c0 := 1)
        have : 3 ^ (j + 2) * p2 ^ 1 * p4 ^ 1 = 3 ^ j * u3_0 := by dsimp [u3_0]; rw [pow_add]; ring
        rw [this] at hm; simpa [u3_0] using hm)
      (by rw [hs_u3_0]; exact hst3_g3)
    have : 3 ^ (a - 2) * u3_0 = 3 ^ a * p2 * p4 := by
      dsimp [u3_0]; rw [show 3 ^ a = 3 ^ (a - 2) * 3 ^ 2 by rw [← pow_add]; congr 1; omega]; ring
    rwa [this] at h
  have hrel_u3 : HasRelGap (3 ^ a * p2 ^ b * p4) a3 1000 := by
    let dp2_3 := if p2 == 7 then 9 else p4
    have hdp_props : p2 < dp2_3 ∧ dp2_3 ∣ 3 ^ a * p2 * p4 ∧ ¬ p2 ∣ dp2_3 := by
      have hp2_cases : p2 = 7 ∨ p2 = 11 := by
        have : ∀ x ∈ basesNo5Data, x.1 = 7 ∨ x.1 = 11 := by decide
        exact this _ hmem
      rcases hp2_cases with rfl | rfl
      · refine ⟨by simp [dp2_3], ?_, by simp [dp2_3]⟩
        have h9 : 9 ∣ 3 ^ a := by have := pow_dvd_pow 3 ha; norm_num at this; exact this
        simp only [dp2_3, beq_self_eq_true, ↓reduceIte]
        exact h9.trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
      · refine ⟨by simp [dp2_3]; omega, ?_, ?_⟩
        · simp only [dp2_3, show (11 == 7) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact dvd_mul_left p4 _
        · simp only [dp2_3, show (11 == 7) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact hp2.coprime_iff_not_dvd.mp ((Nat.coprime_primes hp2 hp4).mpr (by omega))
    have h := hasRelGap_lift_one_prime (u0 := 3 ^ a * p2 * p4) (r := p2) (q := 0) (d1 := dp2_3) (a_num := a3) (a_den := 1000) (k := b - 1)
      hp2 (by have := hp2.pos; have := hp4.pos; positivity) hdp_props.1 hdp_props.2.1 hdp_props.2.2
      (dvd_mul_of_dvd_left (dvd_mul_left p2 _) p4) hrel_u3_a
      (fun j => by
        have hm := properDivsSum_ratio_mono_3p h3p hp2 hp4 (by omega) (lt_trans hp23 hp34) le_rfl (show 1 ≤ j + 1 by omega) le_rfl (a0 := a) (c0 := 1)
        have : 3 ^ a * p2 ^ (j + 1) * p4 ^ 1 = p2 ^ j * (3 ^ a * p2 * p4) := by rw [pow_add]; ring
        rw [this] at hm; simpa using hm)
      (by
        have hsig_m : sigma 1 u3_0 * (3 ^ a * p2 * p4) ≤ sigma 1 (3 ^ a * p2 * p4) * u3_0 := by
          have hm := properDivsSum_ratio_mono_3p h3p hp2 hp4 (by omega) (lt_trans hp23 hp34) ha le_rfl le_rfl (b0 := 1) (c0 := 1)
          have h1 : sigma 1 u3_0 = properDivsSum u3_0 + u3_0 := by
            rw [properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
          have h2 : sigma 1 (3 ^ a * p2 * p4) = properDivsSum (3 ^ a * p2 * p4) + 3 ^ a * p2 * p4 := by
            rw [properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
          rw [h1, h2]; simp only [pow_one] at hm; change properDivsSum u3_0 * (3 ^ a * p2 * p4) ≤ properDivsSum (3 ^ a * p2 * p4) * u3_0 at hm
          have hL : (properDivsSum u3_0 + u3_0) * (3 ^ a * p2 * p4) = properDivsSum u3_0 * (3 ^ a * p2 * p4) + u3_0 * (3 ^ a * p2 * p4) := by ring
          have hR : (properDivsSum (3 ^ a * p2 * p4) + 3 ^ a * p2 * p4) * u3_0 = properDivsSum (3 ^ a * p2 * p4) * u3_0 + u3_0 * (3 ^ a * p2 * p4) := by ring
          linarith
        have hu3_pos : 0 < u3_0 := by have := hp2.pos; have := hp4.pos; dsimp [u3_0]; positivity
        have h1 : 1000 * (2 * u3_0 * dp2_3) ≤ 1000 * (sigma 1 u3_0 * dp2_3 + p2 * u3_0) + p2 * a3 * u3_0 * dp2_3 := by
          rw [hs_u3_0]; exact hst3_gp2
        have hm1 := Nat.mul_le_mul_right (3 ^ a * p2 * p4) h1
        have hm2 := Nat.mul_le_mul_left (1000 * dp2_3) hsig_m
        exact Nat.le_of_mul_le_mul_right (by linarith) hu3_pos)
    have : p2 ^ (b - 1) * (3 ^ a * p2 * p4) = 3 ^ a * p2 ^ b * p4 := by
      rw [show p2 ^ b = p2 ^ (b - 1) * p2 by rw [← pow_succ, Nat.sub_add_cancel hb]]; ring
    rwa [this] at h
  have hstep3 : (∀ y, L ≤ y → y ≤ properDivsSum (3 ^ a * p2 ^ b * p3 ^ c * p4) - L → repNat (3 ^ a * p2 ^ b * p3 ^ c * p4).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ a * p2 ^ b * p3 ^ c * p4) → ∃ i, repNat (3 ^ a * p2 ^ b * p3 ^ c * p4).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
    let u := 3 ^ a * p2 ^ b * p4
    have hu_pos : 0 < u := by have := hp2.pos; have := hp4.pos; dsimp [u]; positivity
    have hcop : ¬ p3 ∣ u := by
      have hc : Nat.Coprime p3 u := Nat.Coprime.mul_right (Nat.Coprime.mul_right
        (((Nat.coprime_primes hp3 h3p).mpr (by omega)).pow_right a)
        (((Nat.coprime_primes hp3 hp2).mpr (by omega)).pow_right b))
        ((Nat.coprime_primes hp3 hp4).mpr (by omega))
      exact hp3.coprime_iff_not_dvd.mp hc
    induction c with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hstep2
      | succ k' =>
        obtain ⟨hc_k, hg_k⟩ := ih (by omega)
        have hratio_B : properDivsSum B0 * (p3 ^ (k' + 1) * u) ≤ properDivsSum (p3 ^ (k' + 1) * u) * B0 := by
          have h := properDivsSum_ratio_mono_4p h3p hp2 hp3 hp4 (by omega) hp23 hp34 ha hb (show 1 ≤ k' + 1 by omega) le_rfl (d0 := 1)
          simpa [B0, u, mul_comm, mul_left_comm, mul_assoc] using h
        have hratio_u : properDivsSum u3_0 * u ≤ properDivsSum u * u3_0 := by
          have h := properDivsSum_ratio_mono_3p h3p hp2 hp4 (by omega) (lt_trans hp23 hp34) ha hb le_rfl (c0 := 1)
          simpa [u3_0, u] using h
        have hB0_dvd : B0 ∣ p3 ^ (k' + 1) * u := by
          have h1 : 3 ^ 2 * p2 ^ 1 * p3 ^ 1 * p4 ∣ 3 ^ a * p2 ^ b * p3 ^ (k' + 1) * p4 :=
            Nat.mul_dvd_mul_right (Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow p2 hb)) (pow_dvd_pow p3 (by omega))) p4
          simpa [B0, u, mul_comm, mul_left_comm, mul_assoc] using h1
        have hB0_le : B0 ≤ p3 ^ (k' + 1) * u := Nat.le_of_dvd (by have := hp3.pos; positivity) hB0_dvd
        have hPk_ge : P0 ≤ properDivsSum (p3 ^ (k' + 1) * u) := by
          rw [hP0_eq']; exact properDivsSum_mono_dvd (by have := hp3.pos; positivity) hB0_dvd
        have heq_k : p3 ^ (k' + 1) * u = 3 ^ a * p2 ^ b * p3 ^ (k' + 1) * p4 := by dsimp [u]; ring
        have heq_k2 : p3 ^ (k' + 2) * u = 3 ^ a * p2 ^ b * p3 ^ (k' + 2) * p4 := by dsimp [u]; ring
        have hres := lift_prime_step_no_interleave (u := u) (r := p3) (a := k' + 1) (L := L) (g := g)
          hp3 hu_pos (by omega) hcop hg1 (le_trans hL_le_P0 hPk_ge)
          (by rw [heq_k]; exact hc_k)
          (by rw [heq_k]; exact hg_k)
          (by
            intro x hx
            have hrg := hrel_u3 x hx
            have hscale : (1000 * (2 * L) + p3 ^ (k' + 2) * a3 * u) * B0 ≤ (1000 * (properDivsSum (p3 ^ (k' + 1) * u) + 1)) * B0 := by
              change 1000 * (2 * L) + p3 * p3 * a3 * u3_0 ≤ 1000 * (P0 + 1) at hst3_d
              have h1 := Nat.mul_le_mul_right (p3 ^ (k' + 1) * u) hst3_d
              have h2 : p3 ^ (k' + 2) * a3 * u * B0 = p3 * p3 * a3 * u3_0 * (p3 ^ (k' + 1) * u) := by dsimp [B0, u3_0]; ring
              have h4 : 1000 * (P0 * (p3 ^ (k' + 1) * u)) ≤ 1000 * (properDivsSum (p3 ^ (k' + 1) * u) * B0) := by
                rw [hP0_eq']; exact Nat.mul_le_mul_left 1000 hratio_B
              have hL1' : (1000 * (2 * L - 1)) * B0 + 1000 * (p3 ^ (k' + 1) * u) ≤ 1000 * (2 * L) * (p3 ^ (k' + 1) * u) := by
                have ha1 := Nat.mul_le_mul_left (1000 * (2 * L - 1)) hB0_le
                have ha2 : (1000 * (2 * L - 1) + 1000) * (p3 ^ (k' + 1) * u) = 1000 * (2 * L) * (p3 ^ (k' + 1) * u) := by congr 1; omega
                linarith
              have hL2' : 1000 * (2 * L) * B0 = 1000 * (2 * L - 1) * B0 + 1000 * B0 := by
                have : (1000 * (2 * L - 1) + 1000) * B0 = 1000 * (2 * L) * B0 := by congr 1; omega
                linarith
              have hX1 : (1000 * (2 * L) + p3 * p3 * a3 * u3_0) * (p3 ^ (k' + 1) * u) = 1000 * (2 * L) * (p3 ^ (k' + 1) * u) + p3 * p3 * a3 * u3_0 * (p3 ^ (k' + 1) * u) := by ring
              have hX2 : 1000 * (P0 + 1) * (p3 ^ (k' + 1) * u) = 1000 * (P0 * (p3 ^ (k' + 1) * u)) + 1000 * (p3 ^ (k' + 1) * u) := by ring
              have hX3 : (1000 * (2 * L) + p3 ^ (k' + 2) * a3 * u) * B0 = 1000 * (2 * L) * B0 + p3 ^ (k' + 2) * a3 * u * B0 := by ring
              have hX4 : 1000 * (properDivsSum (p3 ^ (k' + 1) * u) + 1) * B0 = 1000 * (properDivsSum (p3 ^ (k' + 1) * u) * B0) + 1000 * B0 := by ring
              have hX5 : (1000 * (2 * L - 1)) * B0 = 1000 * (2 * L - 1) * B0 := by ring
              linarith
            have hbud := Nat.le_of_mul_le_mul_right hscale hB0_pos
            change 1000 * (2 * L) + p3 ^ (k' + 2) * a3 * u ≤ 1000 * (properDivsSum (p3 ^ (k' + 1) * u) + 1) at hbud
            let S := ∑ e ∈ u.properDivisors.filter (· < x), e
            change 1000 * x ≤ a3 * u + 1000 * S at hrg
            have hm := Nat.mul_le_mul_left (p3 ^ (k' + 2)) hrg
            have hM1 : p3 ^ (k' + 2) * (1000 * x) = 1000 * (p3 ^ (k' + 2) * x) := by ring
            have hM2 : p3 ^ (k' + 2) * (a3 * u + 1000 * S) = p3 ^ (k' + 2) * a3 * u + 1000 * (p3 ^ (k' + 2) * S) := by ring
            have hM3 : 1000 * (properDivsSum (p3 ^ (k' + 1) * u) + 1) = 1000 * properDivsSum (p3 ^ (k' + 1) * u) + 1000 := by ring
            change 2 * L + p3 ^ (k' + 2) * x ≤ properDivsSum (p3 ^ (k' + 1) * u) + p3 ^ (k' + 2) * S + 1
            linarith)
          (by
            have hPu3 : 13 * (p2 + 1) * (p4 + 1) - u3_0 = properDivsSum u3_0 := by rw [properDivsSum_eq_sigma_sub, hs_u3_0]
            rw [hPu3] at hst3_n
            have hscale : (2 * L + p3 ^ (k' + 1) * u) * B0 ≤
                (properDivsSum (p3 ^ (k' + 1) * u) + p3 ^ (k' + 2) * properDivsSum u + 1) * B0 := by
              change 2 * L + B0 ≤ P0 + p3 * p3 * properDivsSum u3_0 + 1 at hst3_n
              have h1 := Nat.mul_le_mul_right (p3 ^ (k' + 1) * u) hst3_n
              have h2 : p3 ^ (k' + 2) * properDivsSum u3_0 * u * p3 = p3 * p3 * properDivsSum u3_0 * (p3 ^ (k' + 1) * u) := by ring
              have h3 : p3 ^ (k' + 2) * p3 * (properDivsSum u3_0 * u) ≤ p3 ^ (k' + 2) * p3 * (properDivsSum u * u3_0) :=
                Nat.mul_le_mul_left _ hratio_u
              have h4 : p3 ^ (k' + 2) * p3 * (properDivsSum u * u3_0) = p3 ^ (k' + 2) * properDivsSum u * B0 := by
                dsimp [B0, u3_0]; ring
              have h5 : (2 * L - 1) * B0 + (p3 ^ (k' + 1) * u) ≤ 2 * L * (p3 ^ (k' + 1) * u) := by
                have ha1 := Nat.mul_le_mul_left (2 * L - 1) hB0_le
                have ha2 : ((2 * L - 1) + 1) * (p3 ^ (k' + 1) * u) = 2 * L * (p3 ^ (k' + 1) * u) := by congr 1; omega
                linarith
              have h6 : 2 * L * B0 = (2 * L - 1) * B0 + B0 := by
                have : ((2 * L - 1) + 1) * B0 = 2 * L * B0 := by congr 1; omega
                linarith
              have h7 : p3 ^ (k' + 2) * p3 * (properDivsSum u3_0 * u) = p3 * p3 * properDivsSum u3_0 * (p3 ^ (k' + 1) * u) := by ring
              have h8 : (2 * L + B0) * (p3 ^ (k' + 1) * u) = 2 * L * (p3 ^ (k' + 1) * u) + (p3 ^ (k' + 1) * u) * B0 := by ring
              have h9 : (P0 + p3 * p3 * properDivsSum u3_0 + 1) * (p3 ^ (k' + 1) * u) = P0 * (p3 ^ (k' + 1) * u) + p3 * p3 * properDivsSum u3_0 * (p3 ^ (k' + 1) * u) + (p3 ^ (k' + 1) * u) := by ring
              have hP0_mul : P0 * (p3 ^ (k' + 1) * u) = properDivsSum B0 * (p3 ^ (k' + 1) * u) := by rw [hP0_eq']
              have h10 : (2 * L + p3 ^ (k' + 1) * u) * B0 = 2 * L * B0 + (p3 ^ (k' + 1) * u) * B0 := by ring
              have h11 : (properDivsSum (p3 ^ (k' + 1) * u) + p3 ^ (k' + 2) * properDivsSum u + 1) * B0 = properDivsSum (p3 ^ (k' + 1) * u) * B0 + p3 ^ (k' + 2) * properDivsSum u * B0 + B0 := by ring
              linarith
            change 2 * L + p3 ^ (k' + 1) * u ≤ properDivsSum (p3 ^ (k' + 1) * u) + p3 ^ (k' + 2) * properDivsSum u + 1
            exact Nat.le_of_mul_le_mul_right hscale hB0_pos)
        rw [heq_k2] at hres; exact hres
  -- Step 4: lift p4 from 1 to d (u4 = 3^a * p2^b * p3^c, HasRelGap a4 1000)
  let u4_0 := 9 * p2 * p3
  have hs_u4_0 : sigma 1 u4_0 = 13 * (p2 + 1) * (p3 + 1) := by
    have h := sigma_mul_coprime_three h3p hp2 hp3 (by omega) hp23 (a := 2) (b := 1) (c := 1)
    rw [(by decide : ppSum 3 2 = 13), ppSum_one hp2.two_le, ppSum_one hp3.two_le] at h
    simpa [u4_0] using h
  have hrel_u4_0 : HasRelGap u4_0 a4 1000 := hasRelGap_of_list (by have := hp2.pos; have := hp3.pos; dsimp [u4_0]; positivity)
    (by rw [properDivsSum_eq_sigma_sub, hs_u4_0]) hrg4_b
  have hrel_u4_a : HasRelGap (3 ^ a * p2 * p3) a4 1000 := by
    have h := hasRelGap_lift_one_prime (u0 := u4_0) (r := 3) (q := 0) (d1 := p2) (a_num := a4) (a_den := 1000) (k := a - 2)
      h3p (by have := hp2.pos; have := hp3.pos; dsimp [u4_0]; positivity) (by omega)
      (dvd_mul_of_dvd_left (dvd_mul_left p2 9) p3) (h3p.coprime_iff_not_dvd.mp ((Nat.coprime_primes h3p hp2).mpr (by omega)))
      ((by decide : 3 ∣ 9).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))) hrel_u4_0
      (fun j => by
        have hm := properDivsSum_ratio_mono_3p h3p hp2 hp3 (by omega) hp23 (show 2 ≤ j + 2 by omega) le_rfl le_rfl (b0 := 1) (c0 := 1)
        have : 3 ^ (j + 2) * p2 ^ 1 * p3 ^ 1 = 3 ^ j * u4_0 := by dsimp [u4_0]; rw [pow_add]; ring
        rw [this] at hm; simpa [u4_0] using hm)
      (by rw [hs_u4_0]; exact hst4_g3)
    have : 3 ^ (a - 2) * u4_0 = 3 ^ a * p2 * p3 := by
      dsimp [u4_0]; rw [show 3 ^ a = 3 ^ (a - 2) * 3 ^ 2 by rw [← pow_add]; congr 1; omega]; ring
    rwa [this] at h
  have hrel_u4_ab : HasRelGap (3 ^ a * p2 ^ b * p3) a4 1000 := by
    let dp2_4 := if p2 == 7 then 9 else p3
    have hdp_props : p2 < dp2_4 ∧ dp2_4 ∣ 3 ^ a * p2 * p3 ∧ ¬ p2 ∣ dp2_4 := by
      have hp2_cases : p2 = 7 ∨ p2 = 11 := by
        have : ∀ x ∈ basesNo5Data, x.1 = 7 ∨ x.1 = 11 := by decide
        exact this _ hmem
      rcases hp2_cases with rfl | rfl
      · refine ⟨by simp [dp2_4], ?_, by simp [dp2_4]⟩
        have h9 : 9 ∣ 3 ^ a := by have := pow_dvd_pow 3 ha; norm_num at this; exact this
        simp only [dp2_4, beq_self_eq_true, ↓reduceIte]
        exact h9.trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
      · refine ⟨by simp [dp2_4]; omega, ?_, ?_⟩
        · simp only [dp2_4, show (11 == 7) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact dvd_mul_left p3 _
        · simp only [dp2_4, show (11 == 7) = false by decide, Bool.false_eq_true, ↓reduceIte]
          exact hp2.coprime_iff_not_dvd.mp ((Nat.coprime_primes hp2 hp3).mpr (by omega))
    have h := hasRelGap_lift_one_prime (u0 := 3 ^ a * p2 * p3) (r := p2) (q := 0) (d1 := dp2_4) (a_num := a4) (a_den := 1000) (k := b - 1)
      hp2 (by have := hp2.pos; have := hp3.pos; positivity) hdp_props.1 hdp_props.2.1 hdp_props.2.2
      (dvd_mul_of_dvd_left (dvd_mul_left p2 _) p3) hrel_u4_a
      (fun j => by
        have hm := properDivsSum_ratio_mono_3p h3p hp2 hp3 (by omega) hp23 le_rfl (show 1 ≤ j + 1 by omega) le_rfl (a0 := a) (c0 := 1)
        have : 3 ^ a * p2 ^ (j + 1) * p3 ^ 1 = p2 ^ j * (3 ^ a * p2 * p3) := by rw [pow_add]; ring
        rw [this] at hm; simpa using hm)
      (by
        have hsig_m : sigma 1 u4_0 * (3 ^ a * p2 * p3) ≤ sigma 1 (3 ^ a * p2 * p3) * u4_0 := by
          have hm := properDivsSum_ratio_mono_3p h3p hp2 hp3 (by omega) hp23 ha le_rfl le_rfl (b0 := 1) (c0 := 1)
          have h1 : sigma 1 u4_0 = properDivsSum u4_0 + u4_0 := by
            rw [properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
          have h2 : sigma 1 (3 ^ a * p2 * p3) = properDivsSum (3 ^ a * p2 * p3) + 3 ^ a * p2 * p3 := by
            rw [properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
          rw [h1, h2]; simp only [pow_one] at hm; change properDivsSum u4_0 * (3 ^ a * p2 * p3) ≤ properDivsSum (3 ^ a * p2 * p3) * u4_0 at hm
          have hL : (properDivsSum u4_0 + u4_0) * (3 ^ a * p2 * p3) = properDivsSum u4_0 * (3 ^ a * p2 * p3) + u4_0 * (3 ^ a * p2 * p3) := by ring
          have hR : (properDivsSum (3 ^ a * p2 * p3) + 3 ^ a * p2 * p3) * u4_0 = properDivsSum (3 ^ a * p2 * p3) * u4_0 + u4_0 * (3 ^ a * p2 * p3) := by ring
          linarith
        have hu4_pos : 0 < u4_0 := by have := hp2.pos; have := hp3.pos; dsimp [u4_0]; positivity
        have h1 : 1000 * (2 * u4_0 * dp2_4) ≤ 1000 * (sigma 1 u4_0 * dp2_4 + p2 * u4_0) + p2 * a4 * u4_0 * dp2_4 := by
          rw [hs_u4_0]; exact hst4_gp2
        have hm1 := Nat.mul_le_mul_right (3 ^ a * p2 * p3) h1
        have hm2 := Nat.mul_le_mul_left (1000 * dp2_4) hsig_m
        exact Nat.le_of_mul_le_mul_right (by linarith) hu4_pos)
    have : p2 ^ (b - 1) * (3 ^ a * p2 * p3) = 3 ^ a * p2 ^ b * p3 := by
      rw [show p2 ^ b = p2 ^ (b - 1) * p2 by rw [← pow_succ, Nat.sub_add_cancel hb]]; ring
    rwa [this] at h
  have hrel_u4 : HasRelGap (3 ^ a * p2 ^ b * p3 ^ c) a4 1000 := by
    have hlt3p2 : p3 < 3 * p2 := by
      have : ∀ x ∈ basesNo5Data, x.2.1 < 3 * x.1 := by decide
      exact this _ hmem
    have h3p2_dvd : 3 * p2 ∣ 3 ^ a * p2 ^ b * p3 :=
      (Nat.mul_dvd_mul (dvd_pow_self 3 (by omega)) (dvd_pow_self p2 (by omega))).trans (dvd_mul_right _ _)
    have hnp3_3p2 : ¬ p3 ∣ 3 * p2 := by
      intro h; rcases hp3.dvd_mul.mp h with h1 | h2
      · have := Nat.le_of_dvd (by decide) h1; omega
      · have := Nat.le_of_dvd hp2.pos h2; omega
    have h := hasRelGap_lift_one_prime (u0 := 3 ^ a * p2 ^ b * p3) (r := p3) (q := 0) (d1 := 3 * p2) (a_num := a4) (a_den := 1000) (k := c - 1)
      hp3 (by have := hp2.pos; have := hp3.pos; positivity) hlt3p2 h3p2_dvd hnp3_3p2
      (dvd_mul_left p3 _) hrel_u4_ab
      (fun j => by
        have hm := properDivsSum_ratio_mono_3p h3p hp2 hp3 (by omega) hp23 le_rfl le_rfl (show 1 ≤ j + 1 by omega) (a0 := a) (b0 := b)
        have : 3 ^ a * p2 ^ b * p3 ^ (j + 1) = p3 ^ j * (3 ^ a * p2 ^ b * p3) := by rw [pow_add]; ring
        rw [this] at hm; simpa using hm)
      (by
        have hsig_m : sigma 1 u4_0 * (3 ^ a * p2 ^ b * p3) ≤ sigma 1 (3 ^ a * p2 ^ b * p3) * u4_0 := by
          have hm := properDivsSum_ratio_mono_3p h3p hp2 hp3 (by omega) hp23 ha hb le_rfl (c0 := 1)
          have h1 : sigma 1 u4_0 = properDivsSum u4_0 + u4_0 := by
            rw [properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
          have h2 : sigma 1 (3 ^ a * p2 ^ b * p3) = properDivsSum (3 ^ a * p2 ^ b * p3) + 3 ^ a * p2 ^ b * p3 := by
            rw [properDivsSum, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
          rw [h1, h2]; simp only [pow_one] at hm; change properDivsSum u4_0 * (3 ^ a * p2 ^ b * p3) ≤ properDivsSum (3 ^ a * p2 ^ b * p3) * u4_0 at hm
          have hL : (properDivsSum u4_0 + u4_0) * (3 ^ a * p2 ^ b * p3) = properDivsSum u4_0 * (3 ^ a * p2 ^ b * p3) + u4_0 * (3 ^ a * p2 ^ b * p3) := by ring
          have hR : (properDivsSum (3 ^ a * p2 ^ b * p3) + 3 ^ a * p2 ^ b * p3) * u4_0 = properDivsSum (3 ^ a * p2 ^ b * p3) * u4_0 + u4_0 * (3 ^ a * p2 ^ b * p3) := by ring
          linarith
        have hu4_pos : 0 < u4_0 := by have := hp2.pos; have := hp3.pos; dsimp [u4_0]; positivity
        have h1 : 1000 * (2 * u4_0 * (3 * p2)) ≤ 1000 * (sigma 1 u4_0 * (3 * p2) + p3 * u4_0) + p3 * a4 * u4_0 * (3 * p2) := by
          rw [hs_u4_0]; exact hst4_gp3
        have hm1 := Nat.mul_le_mul_right (3 ^ a * p2 ^ b * p3) h1
        have hm2 := Nat.mul_le_mul_left (1000 * (3 * p2)) hsig_m
        exact Nat.le_of_mul_le_mul_right (by linarith) hu4_pos)
    have : p3 ^ (c - 1) * (3 ^ a * p2 ^ b * p3) = 3 ^ a * p2 ^ b * p3 ^ c := by
      rw [show p3 ^ c = p3 ^ (c - 1) * p3 by rw [← pow_succ, Nat.sub_add_cancel hc]]; ring
    rwa [this] at h
  have hstep4 : (∀ y, L ≤ y → y ≤ properDivsSum (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) - L → repNat (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) → ∃ i, repNat (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
    let u := 3 ^ a * p2 ^ b * p3 ^ c
    have hu_pos : 0 < u := by have := hp2.pos; have := hp3.pos; dsimp [u]; positivity
    have hcop : ¬ p4 ∣ u := by
      have hc : Nat.Coprime p4 u := Nat.Coprime.mul_right (Nat.Coprime.mul_right
        (((Nat.coprime_primes hp4 h3p).mpr (by omega)).pow_right a)
        (((Nat.coprime_primes hp4 hp2).mpr (by omega)).pow_right b))
        (((Nat.coprime_primes hp4 hp3).mpr (by omega)).pow_right c)
      exact hp4.coprime_iff_not_dvd.mp hc
    induction d with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hstep3
      | succ k' =>
        obtain ⟨hc_k, hg_k⟩ := ih (by omega)
        have hratio_B : properDivsSum B0 * (p4 ^ (k' + 1) * u) ≤ properDivsSum (p4 ^ (k' + 1) * u) * B0 := by
          have h := properDivsSum_ratio_mono_4p h3p hp2 hp3 hp4 (by omega) hp23 hp34 ha hb hc (show 1 ≤ k' + 1 by omega)
          simpa [B0, u, mul_comm, mul_left_comm, mul_assoc] using h
        have hratio_u : properDivsSum u4_0 * u ≤ properDivsSum u * u4_0 := by
          have h := properDivsSum_ratio_mono_3p h3p hp2 hp3 (by omega) hp23 ha hb hc
          simpa [u4_0, u] using h
        have hB0_dvd : B0 ∣ p4 ^ (k' + 1) * u := by
          have h1 : 3 ^ 2 * p2 ^ 1 * p3 ^ 1 * p4 ^ 1 ∣ 3 ^ a * p2 ^ b * p3 ^ c * p4 ^ (k' + 1) :=
            Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow p2 hb)) (pow_dvd_pow p3 hc)) (pow_dvd_pow p4 (by omega))
          simpa [B0, u, mul_comm, mul_left_comm, mul_assoc] using h1
        have hB0_le : B0 ≤ p4 ^ (k' + 1) * u := Nat.le_of_dvd (by have := hp4.pos; positivity) hB0_dvd
        have hPk_ge : P0 ≤ properDivsSum (p4 ^ (k' + 1) * u) := by
          rw [hP0_eq']; exact properDivsSum_mono_dvd (by have := hp4.pos; positivity) hB0_dvd
        have heq_k : p4 ^ (k' + 1) * u = 3 ^ a * p2 ^ b * p3 ^ c * p4 ^ (k' + 1) := by dsimp [u]; ring
        have heq_k2 : p4 ^ (k' + 2) * u = 3 ^ a * p2 ^ b * p3 ^ c * p4 ^ (k' + 2) := by dsimp [u]; ring
        have hres := lift_prime_step_no_interleave (u := u) (r := p4) (a := k' + 1) (L := L) (g := g)
          hp4 hu_pos (by omega) hcop hg1 (le_trans hL_le_P0 hPk_ge)
          (by rw [heq_k]; exact hc_k)
          (by rw [heq_k]; exact hg_k)
          (by
            intro x hx
            have hrg := hrel_u4 x hx
            have hscale : (1000 * (2 * L) + p4 ^ (k' + 2) * a4 * u) * B0 ≤ (1000 * (properDivsSum (p4 ^ (k' + 1) * u) + 1)) * B0 := by
              change 1000 * (2 * L) + p4 * p4 * a4 * u4_0 ≤ 1000 * (P0 + 1) at hst4_d
              have h1 := Nat.mul_le_mul_right (p4 ^ (k' + 1) * u) hst4_d
              have h2 : p4 ^ (k' + 2) * a4 * u * B0 = p4 * p4 * a4 * u4_0 * (p4 ^ (k' + 1) * u) := by dsimp [B0, u4_0]; ring
              have h4 : 1000 * (P0 * (p4 ^ (k' + 1) * u)) ≤ 1000 * (properDivsSum (p4 ^ (k' + 1) * u) * B0) := by
                rw [hP0_eq']; exact Nat.mul_le_mul_left 1000 hratio_B
              have hL1' : (1000 * (2 * L - 1)) * B0 + 1000 * (p4 ^ (k' + 1) * u) ≤ 1000 * (2 * L) * (p4 ^ (k' + 1) * u) := by
                have ha1 := Nat.mul_le_mul_left (1000 * (2 * L - 1)) hB0_le
                have ha2 : (1000 * (2 * L - 1) + 1000) * (p4 ^ (k' + 1) * u) = 1000 * (2 * L) * (p4 ^ (k' + 1) * u) := by congr 1; omega
                linarith
              have hL2' : 1000 * (2 * L) * B0 = 1000 * (2 * L - 1) * B0 + 1000 * B0 := by
                have : (1000 * (2 * L - 1) + 1000) * B0 = 1000 * (2 * L) * B0 := by congr 1; omega
                linarith
              have hX1 : (1000 * (2 * L) + p4 * p4 * a4 * u4_0) * (p4 ^ (k' + 1) * u) = 1000 * (2 * L) * (p4 ^ (k' + 1) * u) + p4 * p4 * a4 * u4_0 * (p4 ^ (k' + 1) * u) := by ring
              have hX2 : 1000 * (P0 + 1) * (p4 ^ (k' + 1) * u) = 1000 * (P0 * (p4 ^ (k' + 1) * u)) + 1000 * (p4 ^ (k' + 1) * u) := by ring
              have hX3 : (1000 * (2 * L) + p4 ^ (k' + 2) * a4 * u) * B0 = 1000 * (2 * L) * B0 + p4 ^ (k' + 2) * a4 * u * B0 := by ring
              have hX4 : 1000 * (properDivsSum (p4 ^ (k' + 1) * u) + 1) * B0 = 1000 * (properDivsSum (p4 ^ (k' + 1) * u) * B0) + 1000 * B0 := by ring
              have hX5 : (1000 * (2 * L - 1)) * B0 = 1000 * (2 * L - 1) * B0 := by ring
              linarith
            have hbud := Nat.le_of_mul_le_mul_right hscale hB0_pos
            change 1000 * (2 * L) + p4 ^ (k' + 2) * a4 * u ≤ 1000 * (properDivsSum (p4 ^ (k' + 1) * u) + 1) at hbud
            let S := ∑ e ∈ u.properDivisors.filter (· < x), e
            change 1000 * x ≤ a4 * u + 1000 * S at hrg
            have hm := Nat.mul_le_mul_left (p4 ^ (k' + 2)) hrg
            have hM1 : p4 ^ (k' + 2) * (1000 * x) = 1000 * (p4 ^ (k' + 2) * x) := by ring
            have hM2 : p4 ^ (k' + 2) * (a4 * u + 1000 * S) = p4 ^ (k' + 2) * a4 * u + 1000 * (p4 ^ (k' + 2) * S) := by ring
            have hM3 : 1000 * (properDivsSum (p4 ^ (k' + 1) * u) + 1) = 1000 * properDivsSum (p4 ^ (k' + 1) * u) + 1000 := by ring
            change 2 * L + p4 ^ (k' + 2) * x ≤ properDivsSum (p4 ^ (k' + 1) * u) + p4 ^ (k' + 2) * S + 1
            linarith)
          (by
            have hPu4 : 13 * (p2 + 1) * (p3 + 1) - u4_0 = properDivsSum u4_0 := by rw [properDivsSum_eq_sigma_sub, hs_u4_0]
            rw [hPu4] at hst4_n
            have hscale : (2 * L + p4 ^ (k' + 1) * u) * B0 ≤
                (properDivsSum (p4 ^ (k' + 1) * u) + p4 ^ (k' + 2) * properDivsSum u + 1) * B0 := by
              change 2 * L + B0 ≤ P0 + p4 * p4 * properDivsSum u4_0 + 1 at hst4_n
              have h1 := Nat.mul_le_mul_right (p4 ^ (k' + 1) * u) hst4_n
              have h2 : p4 ^ (k' + 2) * properDivsSum u4_0 * u * p4 = p4 * p4 * properDivsSum u4_0 * (p4 ^ (k' + 1) * u) := by ring
              have h3 : p4 ^ (k' + 2) * p4 * (properDivsSum u4_0 * u) ≤ p4 ^ (k' + 2) * p4 * (properDivsSum u * u4_0) :=
                Nat.mul_le_mul_left _ hratio_u
              have h4 : p4 ^ (k' + 2) * p4 * (properDivsSum u * u4_0) = p4 ^ (k' + 2) * properDivsSum u * B0 := by
                dsimp [B0, u4_0]; ring
              have h5 : (2 * L - 1) * B0 + (p4 ^ (k' + 1) * u) ≤ 2 * L * (p4 ^ (k' + 1) * u) := by
                have ha1 := Nat.mul_le_mul_left (2 * L - 1) hB0_le
                have ha2 : ((2 * L - 1) + 1) * (p4 ^ (k' + 1) * u) = 2 * L * (p4 ^ (k' + 1) * u) := by congr 1; omega
                linarith
              have h6 : 2 * L * B0 = (2 * L - 1) * B0 + B0 := by
                have : ((2 * L - 1) + 1) * B0 = 2 * L * B0 := by congr 1; omega
                linarith
              have h7 : p4 ^ (k' + 2) * p4 * (properDivsSum u4_0 * u) = p4 * p4 * properDivsSum u4_0 * (p4 ^ (k' + 1) * u) := by ring
              have h8 : (2 * L + B0) * (p4 ^ (k' + 1) * u) = 2 * L * (p4 ^ (k' + 1) * u) + (p4 ^ (k' + 1) * u) * B0 := by ring
              have h9 : (P0 + p4 * p4 * properDivsSum u4_0 + 1) * (p4 ^ (k' + 1) * u) = P0 * (p4 ^ (k' + 1) * u) + p4 * p4 * properDivsSum u4_0 * (p4 ^ (k' + 1) * u) + (p4 ^ (k' + 1) * u) := by ring
              have hP0_mul : P0 * (p4 ^ (k' + 1) * u) = properDivsSum B0 * (p4 ^ (k' + 1) * u) := by rw [hP0_eq']
              have h10 : (2 * L + p4 ^ (k' + 1) * u) * B0 = 2 * L * B0 + (p4 ^ (k' + 1) * u) * B0 := by ring
              have h11 : (properDivsSum (p4 ^ (k' + 1) * u) + p4 ^ (k' + 2) * properDivsSum u + 1) * B0 = properDivsSum (p4 ^ (k' + 1) * u) * B0 + p4 ^ (k' + 2) * properDivsSum u * B0 + B0 := by ring
              linarith
            change 2 * L + p4 ^ (k' + 1) * u ≤ properDivsSum (p4 ^ (k' + 1) * u) + p4 ^ (k' + 2) * properDivsSum u + 1
            exact Nat.le_of_mul_le_mul_right hscale hB0_pos)
        rw [heq_k2] at hres; exact hres
  have hB0_dvd : B0 ∣ 3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d := by
    have h9 : 9 ∣ 3 ^ a := by have := pow_dvd_pow 3 ha; norm_num at this; exact this
    exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul h9 (dvd_pow_self p2 (by omega))) (dvd_pow_self p3 (by omega))) (dvd_pow_self p4 (by omega))
  have hP_ge : P0 ≤ properDivsSum (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) := by
    rw [hP0_eq']; exact properDivsSum_mono_dvd (by have := hp2.pos; have := hp3.pos; have := hp4.pos; positivity) hB0_dvd
  refine ⟨hstep4.1, hstep4.2, ?_, hP_ge, le_trans hbig0 hP_ge, hL1, hg1⟩
  intro x hx hnot
  obtain ⟨s, hs, hsum⟩ := hbad0 x hx hnot
  refine ⟨s, fun z hz => ?_, hsum⟩
  obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp (hs hz)
  exact Nat.mem_properDivisors.mpr ⟨h1.trans hB0_dvd,
    lt_of_lt_of_le h2 (Nat.le_of_dvd (by have := hp2.pos; have := hp3.pos; have := hp4.pos; positivity) hB0_dvd)⟩

/-- D >= 2 for any odd deficient 3-prime B = 3^a * 5^b * p3^c (a>=2, b>=1, c>=1). -/
lemma dge2_3p_5 {p3 a b c : ℕ} (hp3 : p3.Prime) (hp3_gt5 : 5 < p3)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hdef : sigma 1 (3 ^ a * 5 ^ b * p3 ^ c) < 2 * (3 ^ a * 5 ^ b * p3 ^ c)) :
    2 ≤ 2 * (3 ^ a * 5 ^ b * p3 ^ c) - sigma 1 (3 ^ a * 5 ^ b * p3 ^ c) := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have hs := sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5 (a := a) (b := b) (c := c)
  by_cases hodd : a % 2 = 1 ∨ b % 2 = 1 ∨ c % 2 = 1
  · apply two_le_deficiency_of_even_sigma hdef
    rw [hs]
    rcases hodd with h1 | h2 | h3
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (two_dvd_ppSum_odd h3p (by decide) h1) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (two_dvd_ppSum_odd h5p (by decide) h2) _) _
    · exact dvd_mul_of_dvd_right (two_dvd_ppSum_odd hp3 (hp3.odd_of_ne_two (by omega)) h3) _
  · -- a, b, c all even => a >= 2, b >= 2, c >= 2
    have hb2 : 2 ≤ b := by omega
    have hc2 : 2 ≤ c := by omega
    have h7 : p3 ≠ 7 := by
      rintro rfl
      have h1 := ppSum_mono_exp (p := 3) (by decide) ha
      have h2 := ppSum_mono_exp (p := 5) (by decide) hb2
      have h3 := ppSum_mono_exp (p := 7) (by decide) hc2
      have : 2 * (3 ^ a * 5 ^ b * 7 ^ c) < ppSum 3 a * ppSum 5 b * ppSum 7 c := by
        have m := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
        have hval : ppSum 3 2 = 13 ∧ ppSum 5 2 = 31 ∧ ppSum 7 2 = 57 := by decide
        rw [hval.1, hval.2.1, hval.2.2] at m
        have : 0 < 3 ^ a * 5 ^ b * 7 ^ c := by positivity
        nlinarith
      rw [hs] at hdef; omega
    have hp3_ge11 : 11 ≤ p3 := by
      by_contra! hlt
      exact (by decide : ∀ t < 11, 5 < t → t ≠ 7 → ¬ t.Prime) p3 hlt hp3_gt5 h7 hp3
    -- If p3 in {11, 13}, a must be 2 (since 3^4 * 5^2 * 13^2 is abundant!)
    by_cases hp13 : p3 ≤ 13
    · have ha2 : a = 2 := by
        by_contra hne
        have ha4 : 4 ≤ a := by omega
        have h1 := ppSum_mono_exp (p := 3) (by decide) ha4
        have h2 := ppSum_mono_exp (p := 5) (by decide) hb2
        have h3 := ppSum_mono_exp (p := p3) hp3.two_le hc2
        have h3a := ppSum_anti_base (p := p3) (q := 13) hp3.two_le hp13 (a := 2)
        have h4 : ppSum 3 4 = 121 ∧ ppSum 5 2 = 31 ∧ ppSum 13 2 = 183 := by decide
        have m1 := Nat.mul_le_mul h1 h2
        have m2 := Nat.mul_le_mul m1 h3
        have m3 : ppSum 13 2 * p3 ^ c ≤ ppSum p3 c * 13 ^ 2 := by
          have : ppSum 13 2 * p3 ^ 2 * p3 ^ c ≤ ppSum p3 2 * 13 ^ 2 * p3 ^ c := Nat.mul_le_mul_right _ h3a
          have : ppSum p3 2 * p3 ^ c * 13 ^ 2 ≤ ppSum p3 c * p3 ^ 2 * 13 ^ 2 := Nat.mul_le_mul_right _ h3
          exact Nat.le_of_mul_le_mul_right (by linarith) (pow_pos hp3.pos 2)
        have m4 := Nat.mul_le_mul m1 m3
        rw [h4.1, h4.2.1, h4.2.2] at m4
        have hpos : 0 < 3 ^ a * 5 ^ b * p3 ^ c := by have := hp3.pos; positivity
        rw [hs] at hdef; nlinarith
      subst ha2
      -- I < (13/9)*(5/4)*(11/10) = 143/72 = 2 - 1/72; B >= 9*25*121 = 27225 > 72!
      have l5 := ppSum_lt_lim (p := 5) (a := b) (by decide)
      have lp := ppSum_lt_lim (p := p3) (a := c) hp3.two_le
      have hf := frac_anti (by decide : 2 ≤ 11) hp3_ge11
      have h32 : ppSum 3 2 = 13 := by decide
      have hm := Nat.mul_lt_mul_of_lt_of_lt l5 lp
      have hB : 27225 ≤ 3 ^ 2 * 5 ^ b * p3 ^ c := by
        have : 25 ≤ 5 ^ b := by have := pow_le_pow_right₀ (by decide : 1 ≤ 5) hb2; norm_num at this; exact this
        have : 121 ≤ p3 ^ c := le_trans (by nlinarith : 121 ≤ p3 ^ 2) (pow_le_pow_right₀ hp3.one_lt.le hc2)
        nlinarith
      rw [hs, h32] at hdef ⊢
      have h1 : 13 * ppSum 5 b * ppSum p3 c * (4 * (p3 - 1)) < 13 * 5 * p3 * (5 ^ b * p3 ^ c) := by nlinarith
      have h2 : 13 * 5 * p3 * 10 ≤ 13 * 5 * 11 * (p3 - 1) := by nlinarith
      have h3 : (2 * (3 ^ 2 * 5 ^ b * p3 ^ c) - 13 * ppSum 5 b * ppSum p3 c) * (72 * (p3 - 1)) >
          72 * (p3 - 1) := by
        have hsub : (2 * (3 ^ 2 * 5 ^ b * p3 ^ c) - 13 * ppSum 5 b * ppSum p3 c) * (72 * (p3 - 1)) =
            2 * (3 ^ 2 * 5 ^ b * p3 ^ c) * (72 * (p3 - 1)) - 13 * ppSum 5 b * ppSum p3 c * (72 * (p3 - 1)) := Nat.sub_mul _ _ _
        rw [hsub]
        have h4a : 13 * ppSum 5 b * ppSum p3 c * (72 * (p3 - 1)) * 10 = (13 * ppSum 5 b * ppSum p3 c * (4 * (p3 - 1))) * 180 := by ring
        have h4b : 13 * 5 * p3 * (5 ^ b * p3 ^ c) * 180 = (13 * 5 * p3 * 10) * (18 * (5 ^ b * p3 ^ c)) := by ring
        have h4 : 13 * ppSum 5 b * ppSum p3 c * (72 * (p3 - 1)) * 10 < 13 * 5 * 11 * 18 * (5 ^ b * p3 ^ c) * (p3 - 1) := by
          have ha1 := Nat.mul_lt_mul_of_pos_right h1 (by decide : 0 < 180)
          have ha2 := Nat.mul_le_mul_right (18 * (5 ^ b * p3 ^ c)) h2
          linarith
        have h5 : 13 * ppSum 5 b * ppSum p3 c * (72 * (p3 - 1)) < 143 * (3 ^ 2 * 5 ^ b * p3 ^ c) * (p3 - 1) := by
          have : 143 * (3 ^ 2 * 5 ^ b * p3 ^ c) * (p3 - 1) * 10 = 13 * 5 * 11 * 18 * (5 ^ b * p3 ^ c) * (p3 - 1) := by ring
          omega
        have h6 : 2 * (3 ^ 2 * 5 ^ b * p3 ^ c) * (72 * (p3 - 1)) = 143 * (3 ^ 2 * 5 ^ b * p3 ^ c) * (p3 - 1) + (3 ^ 2 * 5 ^ b * p3 ^ c) * (p3 - 1) := by ring
        have h7 : 72 * (p3 - 1) < (3 ^ 2 * 5 ^ b * p3 ^ c) * (p3 - 1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        omega
      by_contra! hbad
      have : (2 * (3 ^ 2 * 5 ^ b * p3 ^ c) - 13 * ppSum 5 b * ppSum p3 c) * (72 * (p3 - 1)) ≤ 72 * (p3 - 1) := by nlinarith
      omega
    · -- p3 >= 17 => I < (3/2)*(5/4)*(17/16) = 255/128 = 2 - 1/128; B >= 9*25*289 > 128!
      have hp17 : 17 ≤ p3 := by
        by_contra! hlt
        exact (by decide : ∀ t < 17, 13 < t → ¬ t.Prime) p3 hlt (by omega) hp3
      have l3 := ppSum_lt_lim (p := 3) (a := a) (by decide)
      have l5 := ppSum_lt_lim (p := 5) (a := b) (by decide)
      have lp := ppSum_lt_lim (p := p3) (a := c) hp3.two_le
      have hf := frac_anti (by decide : 2 ≤ 17) hp17
      have hm := Nat.mul_lt_mul_of_lt_of_lt (Nat.mul_lt_mul_of_lt_of_lt l3 l5) lp
      have hB : 225 * 289 ≤ 3 ^ a * 5 ^ b * p3 ^ c := by
        have h9 : 9 ≤ 3 ^ a := by have := pow_le_pow_right₀ (by decide : 1 ≤ 3) ha; norm_num at this; exact this
        have h25 : 25 ≤ 5 ^ b := by have := pow_le_pow_right₀ (by decide : 1 ≤ 5) hb2; norm_num at this; exact this
        have hp2' : 289 ≤ p3 ^ c := le_trans (by nlinarith : 289 ≤ p3 ^ 2) (pow_le_pow_right₀ hp3.one_lt.le hc2)
        exact Nat.mul_le_mul (Nat.mul_le_mul h9 h25) hp2'
      rw [hs] at hdef ⊢
      have hsub : (2 * (3 ^ a * 5 ^ b * p3 ^ c) - ppSum 3 a * ppSum 5 b * ppSum p3 c) * (128 * (p3 - 1)) =
          2 * (3 ^ a * 5 ^ b * p3 ^ c) * (128 * (p3 - 1)) - ppSum 3 a * ppSum 5 b * ppSum p3 c * (128 * (p3 - 1)) := Nat.sub_mul _ _ _
      have hlt : 128 * (p3 - 1) < (2 * (3 ^ a * 5 ^ b * p3 ^ c) - ppSum 3 a * ppSum 5 b * ppSum p3 c) * (128 * (p3 - 1)) := by
        rw [hsub]
        have h1 : ppSum 3 a * ppSum 5 b * ppSum p3 c * (8 * (p3 - 1)) < 15 * p3 * (3 ^ a * 5 ^ b * p3 ^ c) := by linarith
        have h2 : 15 * p3 * 16 ≤ 15 * 17 * (p3 - 1) := by linarith
        have h3 := Nat.mul_lt_mul_of_pos_right h1 (by decide : 0 < 16)
        have h4 := Nat.mul_le_mul_right (3 ^ a * 5 ^ b * p3 ^ c) h2
        have h5 : ppSum 3 a * ppSum 5 b * ppSum p3 c * (128 * (p3 - 1)) < 255 * (3 ^ a * 5 ^ b * p3 ^ c) * (p3 - 1) := by linarith
        have h6 : 2 * (3 ^ a * 5 ^ b * p3 ^ c) * (128 * (p3 - 1)) = 255 * (3 ^ a * 5 ^ b * p3 ^ c) * (p3 - 1) + (3 ^ a * 5 ^ b * p3 ^ c) * (p3 - 1) := by ring
        have h7 : 128 * (p3 - 1) < (3 ^ a * 5 ^ b * p3 ^ c) * (p3 - 1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        omega
      by_contra! hbad
      have : (2 * (3 ^ a * 5 ^ b * p3 ^ c) - ppSum 3 a * ppSum 5 b * ppSum p3 c) * (128 * (p3 - 1)) ≤ 1 * (128 * (p3 - 1)) := Nat.mul_le_mul_right _ (by omega)
      omega

/-- D >= 2 for any odd deficient 4-prime B = 3^a * p2^b * p3^c * p4^d (5 nmid B). -/
lemma dge2_4p_no5 {p2 p3 p4 a b c d : ℕ}
    (hp2 : p2.Prime) (hp3 : p3.Prime) (hp4 : p4.Prime)
    (h7p2 : 7 ≤ p2) (hp23 : p2 < p3) (hp34 : p3 < p4)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hdef : sigma 1 (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) < 2 * (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d)) :
    2 ≤ 2 * (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) - sigma 1 (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) := by
  have h3p : Nat.Prime 3 := by decide
  have hs := sigma_mul_coprime_four h3p hp2 hp3 hp4 (by omega) hp23 hp34 (a := a) (b := b) (c := c) (d := d)
  by_cases hodd : a % 2 = 1 ∨ b % 2 = 1 ∨ c % 2 = 1 ∨ d % 2 = 1
  · apply two_le_deficiency_of_even_sigma hdef
    rw [hs]
    rcases hodd with h1 | h2 | h3 | h4
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (two_dvd_ppSum_odd h3p (by decide) h1) _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (two_dvd_ppSum_odd hp2 (hp2.odd_of_ne_two (by omega)) h2) _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (two_dvd_ppSum_odd hp3 (hp3.odd_of_ne_two (by omega)) h3) _) _
    · exact dvd_mul_of_dvd_right (two_dvd_ppSum_odd hp4 (hp4.odd_of_ne_two (by omega)) h4) _
  · have hb2 : 2 ≤ b := by omega
    have hc2 : 2 ≤ c := by omega
    have hd2 : 2 ≤ d := by omega
    by_cases hinf : 3 * p2 * p3 * p4 < 2 * (2 * (p2 - 1) * (p3 - 1) * (p4 - 1))
    · exact two_le_deficiency_of_inf_lt_two h3p hp2 hp3 hp4 (by omega) hp23 hp34 ha hb2 hc2 hd2 hinf
    · -- 3 * p2 * p3 * p4 >= 4 * (p2-1)*(p3-1)*(p4-1) => must be one of the 6 triples!
      have hmem6 : (p2, p3, p4) ∈ [(7,11,13),(7,11,17),(7,11,19),(7,11,23),(7,13,17),(7,13,19)] := by
        have hp2_7 : p2 = 7 := by
          by_contra hne
          have h11 : 11 ≤ p2 := by
            by_contra! hlt; exact (by decide : ∀ t < 11, 7 ≤ t → t ≠ 7 → ¬ t.Prime) p2 hlt h7p2 hne hp2
          have h13 : 13 ≤ p3 := by
            by_contra! hlt; exact (by decide : ∀ t < 13, 11 < t → ¬ t.Prime) p3 hlt (by omega) hp3
          have h17 : 17 ≤ p4 := by
            by_contra! hlt; exact (by decide : ∀ t < 17, 13 < t → ¬ t.Prime) p4 hlt (by omega) hp4
          have f1 := frac_anti (by decide : 2 ≤ 11) h11
          have f2 := frac_anti (by decide : 2 ≤ 13) h13
          have f3 := frac_anti (by decide : 2 ≤ 17) h17
          have hm := Nat.mul_le_mul (Nat.mul_le_mul f1 f2) f3
          have hL : p2 * (11 - 1) * (p3 * (13 - 1)) * (p4 * (17 - 1)) = 1920 * (p2 * p3 * p4) := by ring
          have hR : 11 * (p2 - 1) * (13 * (p3 - 1)) * (17 * (p4 - 1)) = 2431 * ((p2 - 1) * (p3 - 1) * (p4 - 1)) := by ring
          rw [hL, hR] at hm
          have hpos : 0 < (p2 - 1) * (p3 - 1) * (p4 - 1) := by
            have : 0 < p2 - 1 := (by omega); have : 0 < p3 - 1 := (by omega); have : 0 < p4 - 1 := (by omega); positivity
          have hinf1 : 3 * p2 * p3 * p4 = 3 * (p2 * p3 * p4) := by ring
          have hinf2 : 2 * (2 * (p2 - 1) * (p3 - 1) * (p4 - 1)) = 4 * ((p2 - 1) * (p3 - 1) * (p4 - 1)) := by ring
          rw [hinf1, hinf2] at hinf; omega
        subst hp2_7
        have hp3_13 : p3 ≤ 13 := by
          by_contra! hgt
          have h17 : 17 ≤ p3 := by
            by_contra! hlt; exact (by decide : ∀ t < 17, 13 < t → ¬ t.Prime) p3 hlt hgt hp3
          have h19 : 19 ≤ p4 := by
            by_contra! hlt; exact (by decide : ∀ t < 19, 17 < t → ¬ t.Prime) p4 hlt (by omega) hp4
          have f2 := frac_anti (by decide : 2 ≤ 17) h17
          have f3 := frac_anti (by decide : 2 ≤ 19) h19
          have hm := Nat.mul_le_mul f2 f3
          nlinarith
        have hp3_c : p3 = 11 ∨ p3 = 13 :=
          (by decide : ∀ t ≤ 13, 7 < t → t.Prime → t = 11 ∨ t = 13) p3 hp3_13 hp23 hp3
        rcases hp3_c with rfl | rfl
        · have hp4_lt29 : p4 < 29 := by
            by_contra! h29
            have f3 := frac_anti (by decide : 2 ≤ 29) h29
            nlinarith
          have hc4 : p4 = 13 ∨ p4 = 17 ∨ p4 = 19 ∨ p4 = 23 :=
            (by decide : ∀ t < 29, 11 < t → t.Prime → t = 13 ∨ t = 17 ∨ t = 19 ∨ t = 23) p4 hp4_lt29 hp34 hp4
          rcases hc4 with rfl | rfl | rfl | rfl <;> simp
        · have hp4_lt23 : p4 < 23 := by
            by_contra! h23
            have f3 := frac_anti (by decide : 2 ≤ 23) h23
            nlinarith
          have hc4 : p4 = 17 ∨ p4 = 19 :=
            (by decide : ∀ t < 23, 13 < t → t.Prime → t = 17 ∨ t = 19) p4 hp4_lt23 hp34 hp4
          rcases hc4 with rfl | rfl <;> simp
      have hchk := List.all_eq_true.mp dge2_no5_ok _ hmem6
      have hres := checkDge2_sound (a := a) (b := b) (c := c) (d := d)
        (VValid.mk (h := none) h3p ha trivial (Or.inr ⟨rfl, rfl, by omega⟩))
        (VValid.mk (h := none) hp2 hb2 trivial (Or.inr ⟨rfl, rfl, by omega⟩))
        (VValid.mk (h := none) hp3 hc2 trivial (Or.inr ⟨rfl, rfl, by omega⟩))
        (VValid.mk (h := none) hp4 hd2 trivial (Or.inr ⟨rfl, rfl, by omega⟩))
        (by
          have : vSigma (mkV 3 2 none 2) a * vSigma (mkV p2 2 none 2) b * vSigma (mkV p3 2 none 2) c * vSigma (mkV p4 2 none 2) d =
              sigma 1 (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) := by
            rw [hs]; simp [vSigma, mkV, h3p.ne_one, hp2.ne_one, hp3.ne_one, hp4.ne_one]
          rw [this]; exact hdef)
        hchk
      have : vSigma (mkV 3 2 none 2) a * vSigma (mkV p2 2 none 2) b * vSigma (mkV p3 2 none 2) c * vSigma (mkV p4 2 none 2) d =
          sigma 1 (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d) := by
        rw [hs]; simp [vSigma, mkV, h3p.ne_one, hp2.ne_one, hp3.ne_one, hp4.ne_one]
      rw [this] at hres; exact hres

/-- D >= 2 for any odd deficient 4-prime B = 3^a * 5^b * p3^c * p4^d (a>=2, b>=1, c>=1, d>=1). -/
lemma find_dge2Pairs5' (p3 tag hi lo t A B : ℕ) (hlt : t < hi) (hlo : lo < t) (hp : t.Prime)
    (hcond : A * (t - 1) ≤ B * t)
    (h : (List.range (hi - lo - 1)).all (fun i => let s := lo + 1 + i;
      isComp s || !(decide (A * (s - 1) ≤ B * s)) ||
      dge2Pairs5.any (fun x => decide (x.1 = p3 ∧ x.2.1 = s ∧ x.2.2 = tag))) = true) :
    (p3, t, tag) ∈ dge2Pairs5 := by
  have h1 := List.all_eq_true.mp h (t - lo - 1) (List.mem_range.mpr (by omega))
  dsimp only at h1
  rw [show lo + 1 + (t - lo - 1) = t by omega] at h1
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, decide_eq_true_eq] at h1
  rcases h1 with (hcomp | hnot) | ⟨⟨p3', t', tag'⟩, hm, rfl, rfl, rfl⟩
  · exact absurd hp (not_prime_of_isComp hcomp)
  · exact absurd hcond hnot
  · exact hm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
lemma dge2_4p_5 {p3 p4 a b c d : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hp3_gt5 : 5 < p3) (hp34 : p3 < p4)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hdef : sigma 1 (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d) < 2 * (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d)) :
    2 ≤ 2 * (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d) - sigma 1 (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d) := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have hs := sigma_mul_coprime_four h3p h5p hp3 hp4 (by decide) hp3_gt5 hp34 (a := a) (b := b) (c := c) (d := d)
  by_cases hodd : a % 2 = 1 ∨ b % 2 = 1 ∨ c % 2 = 1 ∨ d % 2 = 1
  · apply two_le_deficiency_of_even_sigma hdef
    rw [hs]
    rcases hodd with h1 | h2 | h3 | h4
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (two_dvd_ppSum_odd h3p (by decide) h1) _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (two_dvd_ppSum_odd h5p (by decide) h2) _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (two_dvd_ppSum_odd hp3 (hp3.odd_of_ne_two (by omega)) h3) _) _
    · exact dvd_mul_of_dvd_right (two_dvd_ppSum_odd hp4 (hp4.odd_of_ne_two (by omega)) h4) _
  · have hb2 : 2 ≤ b := by omega
    have hc2 : 2 ≤ c := by omega
    have hd2 : 2 ≤ d := by omega
    -- First rule out p3 = 7 (3^2 * 5^2 * 7^2 is already abundant!)
    have hne7 : p3 ≠ 7 := by
      rintro rfl
      have h1 := ppSum_mono_exp (p := 3) (by decide) ha
      have h2 := ppSum_mono_exp (p := 5) (by decide) hb2
      have h3 := ppSum_mono_exp (p := 7) (by decide) hc2
      have h4 : p4 ^ d ≤ ppSum p4 d := by
        rw [ppSum_eq_sigma hp4, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
      have m := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4
      have hval : ppSum 3 2 = 13 ∧ ppSum 5 2 = 31 ∧ ppSum 7 2 = 57 := by decide
      rw [hval.1, hval.2.1, hval.2.2] at m
      have : 0 < 3 ^ a * 5 ^ b * 7 ^ c * p4 ^ d := by have := hp4.pos; positivity
      rw [hs] at hdef; nlinarith
    have hp3_11 : 11 ≤ p3 := by
      by_contra! hlt; exact (by decide : ∀ t < 11, 5 < t → t ≠ 7 → ¬ t.Prime) p3 hlt hp3_gt5 hne7 hp3
    -- Case A: p3 in {11, 13} => a MUST be 2!
    by_cases hp13 : p3 ≤ 13
    · have ha2 : a = 2 := by
        by_contra hne
        have ha4 : 4 ≤ a := by omega
        have h1 := ppSum_mono_exp (p := 3) (by decide) ha4
        have h2 := ppSum_mono_exp (p := 5) (by decide) hb2
        have h3 := ppSum_mono_exp (p := p3) hp3.two_le hc2
        have h3a := ppSum_anti_base (p := p3) (q := 13) hp3.two_le hp13 (a := 2)
        have h4 : p4 ^ d ≤ ppSum p4 d := by
          rw [ppSum_eq_sigma hp4, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
        have hval : ppSum 3 4 = 121 ∧ ppSum 5 2 = 31 ∧ ppSum 13 2 = 183 := by decide
        have m3 : ppSum 13 2 * p3 ^ c ≤ ppSum p3 c * 13 ^ 2 := by
          have : ppSum 13 2 * p3 ^ 2 * p3 ^ c ≤ ppSum p3 2 * 13 ^ 2 * p3 ^ c := Nat.mul_le_mul_right _ h3a
          have : ppSum p3 2 * p3 ^ c * 13 ^ 2 ≤ ppSum p3 c * p3 ^ 2 * 13 ^ 2 := Nat.mul_le_mul_right _ h3
          exact Nat.le_of_mul_le_mul_right (by linarith) (pow_pos hp3.pos 2)
        have m4 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) m3) h4
        rw [hval.1, hval.2.1, hval.2.2] at m4
        have : 0 < 3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d := by have := hp3.pos; have := hp4.pos; positivity
        rw [hs] at hdef; nlinarith
      subst ha2
      -- Check if (13/9)*(5/4)*(p3/(p3-1))*(p4/(p4-1)) < 2
      by_cases hinf2 : 13 * 5 * p3 * p4 < 2 * (9 * 4 * (p3 - 1) * (p4 - 1))
      · have l5 := ppSum_lt_lim (p := 5) (a := b) (by decide)
        have l3 := ppSum_lt_lim (p := p3) (a := c) hp3.two_le
        have l4 := ppSum_lt_lim (p := p4) (a := d) hp4.two_le
        have h32 : ppSum 3 2 = 13 := by decide
        have hm := Nat.mul_lt_mul_of_lt_of_lt (Nat.mul_lt_mul_of_lt_of_lt l5 l3) l4
        let ud := 9 * 4 * (p3 - 1) * (p4 - 1)
        let B := 3 ^ 2 * 5 ^ b * p3 ^ c * p4 ^ d
        have hud_lt_B : ud < B := by
          have h25 : 4 < 5 ^ b := lt_of_lt_of_le (by decide : 4 < 25) (by have := pow_le_pow_right₀ (by decide : 1 ≤ 5) hb2; norm_num at this; exact this)
          have hp3' : p3 - 1 < p3 ^ c := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p3)
          have hp4' : p4 - 1 < p4 ^ d := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p4)
          have m12 := Nat.mul_lt_mul_of_lt_of_lt (Nat.mul_lt_mul_of_lt_of_lt h25 hp3') hp4'
          have m3 := Nat.mul_lt_mul_of_pos_left m12 (by decide : 0 < 9)
          dsimp only [ud, B]; linarith
        have hsig_lt : sigma 1 B * ud < (13 * 5 * p3 * p4) * B := by
          rw [hs, h32]
          have hm2 := Nat.mul_lt_mul_of_pos_left hm (by decide : 0 < 13 * 9)
          have hL : 13 * 9 * (ppSum 5 b * (5 - 1) * (ppSum p3 c * (p3 - 1)) * (ppSum p4 d * (p4 - 1))) = 13 * ppSum 5 b * ppSum p3 c * ppSum p4 d * ud := by dsimp [ud]; ring
          have hR : 13 * 9 * (5 * 5 ^ b * (p3 * p3 ^ c) * (p4 * p4 ^ d)) = (13 * 5 * p3 * p4) * B := by dsimp [B]; ring
          linarith
        have hsub : (2 * B - sigma 1 B) * ud = 2 * B * ud - sigma 1 B * ud := Nat.sub_mul _ _ _
        have hgt : ud < (2 * B - sigma 1 B) * ud := by
          rw [hsub]
          have hgap : 1 ≤ 2 * ud - 13 * 5 * p3 * p4 := Nat.sub_pos_of_lt hinf2
          have hmul : (2 * ud - 13 * 5 * p3 * p4) * B = 2 * B * ud - (13 * 5 * p3 * p4) * B := by rw [Nat.sub_mul]; ring_nf
          have hBle : B ≤ 2 * B * ud - (13 * 5 * p3 * p4) * B := by rw [← hmul]; exact le_trans (by omega) (Nat.mul_le_mul_right B hgap)
          omega
        by_contra! hbad
        change 2 * B - sigma 1 B < 2 at hbad
        have : (2 * B - sigma 1 B) * ud ≤ 1 * ud := Nat.mul_le_mul_right ud (by omega)
        omega
      · -- (p3, p4, 2) ∈ dge2Pairs5!
        have hp4_le : p4 < 150 := by
          by_contra! hge
          have hp3_c : p3 = 11 ∨ p3 = 13 := (by decide : ∀ t ≤ 13, 11 ≤ t → t.Prime → t = 11 ∨ t = 13) p3 hp13 hp3_11 hp3
          have hf := frac_anti (by decide : 2 ≤ 150) hge
          rcases hp3_c with rfl | rfl <;> nlinarith
        have hmem : (p3, p4, 2) ∈ dge2Pairs5 := by
          have hp3_c : p3 = 11 ∨ p3 = 13 := (by decide : ∀ t ≤ 13, 11 ≤ t → t.Prime → t = 11 ∨ t = 13) p3 hp13 hp3_11 hp3
          rcases hp3_c with rfl | rfl
          · exact find_dge2Pairs5' 11 2 150 11 p4 (2 * (9 * 4 * 10)) (13 * 5 * 11) hp4_le hp34 hp4 (by omega) (by decide)
          · exact find_dge2Pairs5' 13 2 150 13 p4 (2 * (9 * 4 * 12)) (13 * 5 * 13) hp4_le hp34 hp4 (by omega) (by decide)
        have hchk := List.all_eq_true.mp dge2_5_ok _ hmem
        simp only [show (2 == 0) = false by decide, Bool.false_eq_true, ↓reduceIte] at hchk
        have hres := checkDge2_sound (a := 2) (b := b) (c := c) (d := d)
          (VValid.mk (h := some 2) h3p le_rfl le_rfl (Or.inr ⟨rfl, rfl, rfl⟩))
          (VValid.mk (h := none) h5p hb2 trivial (Or.inr ⟨rfl, rfl, by omega⟩))
          (VValid.mk (h := none) hp3 hc2 trivial (Or.inr ⟨rfl, rfl, by omega⟩))
          (VValid.mk (h := none) hp4 hd2 trivial (Or.inr ⟨rfl, rfl, by omega⟩))
          (by
            have : vSigma (mkV 3 2 (some 2) 2) 2 * vSigma (mkV 5 2 none 2) b * vSigma (mkV p3 2 none 2) c * vSigma (mkV p4 2 none 2) d =
                sigma 1 (3 ^ 2 * 5 ^ b * p3 ^ c * p4 ^ d) := by
              rw [hs]; simp [vSigma, mkV, h3p.ne_one, h5p.ne_one, hp3.ne_one, hp4.ne_one]
            rw [this]; exact hdef)
          hchk
        have : vSigma (mkV 3 2 (some 2) 2) 2 * vSigma (mkV 5 2 none 2) b * vSigma (mkV p3 2 none 2) c * vSigma (mkV p4 2 none 2) d =
            sigma 1 (3 ^ 2 * 5 ^ b * p3 ^ c * p4 ^ d) := by
          rw [hs]; simp [vSigma, mkV, h3p.ne_one, h5p.ne_one, hp3.ne_one, hp4.ne_one]
        rw [this] at hres; exact hres
    · -- Case B: p3 >= 17
      by_cases hinf : 3 * 5 * p3 * p4 < 2 * (2 * 4 * (p3 - 1) * (p4 - 1))
      · exact two_le_deficiency_of_inf_lt_two h3p h5p hp3 hp4 (by decide) hp3_gt5 hp34 ha hb2 hc2 hd2 hinf
      · have hp3_le29 : p3 ≤ 29 := by
          by_contra! hgt
          have h31 : 31 ≤ p3 := by by_contra! hlt; exact (by decide : ∀ t < 31, 29 < t → ¬ t.Prime) p3 hlt hgt hp3
          have h37 : 37 ≤ p4 := by by_contra! hlt; exact (by decide : ∀ t < 37, 31 < t → ¬ t.Prime) p4 hlt (by omega) hp4
          have f1 := frac_anti (by decide : 2 ≤ 31) h31
          have f2 := frac_anti (by decide : 2 ≤ 37) h37
          have := Nat.mul_le_mul f1 f2; nlinarith
        have hp4_lt260 : p4 < 260 := by
          by_contra! hge
          have h17 : 17 ≤ p3 := by by_contra! hlt; exact (by decide : ∀ t < 17, 13 < t → ¬ t.Prime) p3 hlt (by omega) hp3
          have f1 := frac_anti (by decide : 2 ≤ 17) h17
          have f2 := frac_anti (by decide : 2 ≤ 260) hge
          have := Nat.mul_le_mul f1 f2; nlinarith
        have hmem : (p3, p4, 0) ∈ dge2Pairs5 := by
          have hp3_c : p3 = 17 ∨ p3 = 19 ∨ p3 = 23 ∨ p3 = 29 :=
            (by decide : ∀ t ≤ 29, 13 < t → t.Prime → t = 17 ∨ t = 19 ∨ t = 23 ∨ t = 29) p3 hp3_le29 (by omega) hp3
          rcases hp3_c with rfl | rfl | rfl | rfl
          · exact find_dge2Pairs5' 17 0 260 17 p4 (2 * (8 * 16)) (15 * 17) hp4_lt260 hp34 hp4 (by omega) (by decide)
          · exact find_dge2Pairs5' 19 0 260 19 p4 (2 * (8 * 18)) (15 * 19) hp4_lt260 hp34 hp4 (by omega) (by decide)
          · exact find_dge2Pairs5' 23 0 260 23 p4 (2 * (8 * 22)) (15 * 23) hp4_lt260 hp34 hp4 (by omega) (by decide)
          · exact find_dge2Pairs5' 29 0 260 29 p4 (2 * (8 * 28)) (15 * 29) hp4_lt260 hp34 hp4 (by omega) (by decide)
        have hchk := List.all_eq_true.mp dge2_5_ok _ hmem
        simp only [beq_self_eq_true, ↓reduceIte] at hchk
        have hres := checkDge2_sound (a := a) (b := b) (c := c) (d := d)
          (VValid.mk (h := none) h3p ha trivial (Or.inr ⟨rfl, rfl, by omega⟩))
          (VValid.mk (h := none) h5p hb2 trivial (Or.inr ⟨rfl, rfl, by omega⟩))
          (VValid.mk (h := none) hp3 hc2 trivial (Or.inr ⟨rfl, rfl, by omega⟩))
          (VValid.mk (h := none) hp4 hd2 trivial (Or.inr ⟨rfl, rfl, by omega⟩))
          (by
            have : vSigma (mkV 3 2 none 2) a * vSigma (mkV 5 2 none 2) b * vSigma (mkV p3 2 none 2) c * vSigma (mkV p4 2 none 2) d =
                sigma 1 (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d) := by
              rw [hs]; simp [vSigma, mkV, h3p.ne_one, h5p.ne_one, hp3.ne_one, hp4.ne_one]
            rw [this]; exact hdef)
          hchk
        have : vSigma (mkV 3 2 none 2) a * vSigma (mkV 5 2 none 2) b * vSigma (mkV p3 2 none 2) c * vSigma (mkV p4 2 none 2) d =
            sigma 1 (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d) := by
          rw [hs]; simp [vSigma, mkV, h3p.ne_one, h5p.ne_one, hp3.ne_one, hp4.ne_one]
        rw [this] at hres; exact hres

end LiftsAndDGe2


lemma find_bases3 (a0 b0 p3 L g P0 : ℕ) (bad : List ℕ)
    (h : bases3Data.any (fun x => decide (x.1 = a0 ∧ x.2.1 = b0 ∧ x.2.2.1 = p3 ∧
      x.2.2.2.1 = L ∧ x.2.2.2.2.1 = g ∧ x.2.2.2.2.2.1 = P0 ∧ x.2.2.2.2.2.2.1 = bad)) = true) :
    ∃ ds bestD ds3 relN, (a0, b0, p3, L, g, P0, bad, ds, bestD, ds3, relN) ∈ bases3Data := by
  obtain ⟨⟨a0', b0', p3', L', g', P0', bad', ds, bestD, ds3, relN⟩, hmem, hcond⟩ := List.any_eq_true.mp h
  simp only [decide_eq_true_eq] at hcond
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hcond
  exact ⟨ds, bestD, ds3, relN, hmem⟩

lemma no_prime_between (lo hi t : ℕ) (hlt : t < hi) (hlo : lo < t)
    (h : (List.range (hi - lo - 1)).all (fun i => isComp (lo + 1 + i)) = true) : ¬ t.Prime := by
  have h1 := List.all_eq_true.mp h (t - lo - 1) (List.mem_range.mpr (by omega))
  rw [show lo + 1 + (t - lo - 1) = t by omega] at h1
  exact not_prime_of_isComp h1

lemma find_cb5 (l : List (ℕ × ℕ)) (hi lo t : ℕ) (hlt : t < hi) (hlo : lo < t) (hp : t.Prime)
    (h : (List.range (hi - lo - 1)).all (fun i => let s := lo + 1 + i;
      isComp s ||
      l.any (fun x => decide (x.1 = s) && (List.range (x.2 - s - 1)).all (fun j => isComp (s + 1 + j)))) = true) :
    ∃ q0, (t, q0) ∈ l ∧ ∀ s < q0, t < s → ¬ s.Prime := by
  have h1 := List.all_eq_true.mp h (t - lo - 1) (List.mem_range.mpr (by omega))
  dsimp only at h1; rw [show lo + 1 + (t - lo - 1) = t by omega] at h1
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h1
  rcases h1 with hcomp | ⟨⟨t', q0⟩, hm, rfl, hall⟩
  · exact absurd hp (not_prime_of_isComp hcomp)
  · refine ⟨q0, hm, fun s hsq hts => ?_⟩
    have h2 := List.all_eq_true.mp hall (s - t' - 1) (List.mem_range.mpr (by omega))
    rw [show t' + 1 + (s - t' - 1) = s by omega] at h2
    exact not_prime_of_isComp h2

lemma find_bases315 (hi lo t : ℕ) (hlt : t < hi) (hlo : lo < t) (hp : t.Prime)
    (h : (List.range (hi - lo - 1)).all (fun i => let s := lo + 1 + i;
      isComp s || bases315Data.any (fun x => decide (x.1 = s))) = true) :
    ∃ L g P0 bad ds, (t, L, g, P0, bad, ds) ∈ bases315Data := by
  have h1 := List.all_eq_true.mp h (t - lo - 1) (List.mem_range.mpr (by omega))
  dsimp only at h1; rw [show lo + 1 + (t - lo - 1) = t by omega] at h1
  simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h1
  rcases h1 with hcomp | ⟨⟨t', L, g, P0, bad, ds⟩, hm, rfl⟩
  · exact absurd hp (not_prime_of_isComp hcomp)
  · exact ⟨L, g, P0, bad, ds, hm⟩

lemma find_basesNo5 (p2 p3 hi lo t : ℕ) (hlt : t < hi) (hlo : lo < t) (hp : t.Prime)
    (h : (List.range (hi - lo - 1)).all (fun i => let s := lo + 1 + i;
      isComp s || basesNo5Data.any (fun x => decide (x.1 = p2 ∧ x.2.1 = p3 ∧ x.2.2.1 = s))) = true) :
    ∃ q0 L g P0 bad ds a2 a3 a4 ds2 ds3 ds4, (p2, p3, t, q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4) ∈ basesNo5Data := by
  have h1 := List.all_eq_true.mp h (t - lo - 1) (List.mem_range.mpr (by omega))
  dsimp only at h1; rw [show lo + 1 + (t - lo - 1) = t by omega] at h1
  simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h1
  rcases h1 with hcomp | ⟨⟨p2', p3', t', q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4⟩, hm, rfl, rfl, rfl⟩
  · exact absurd hp (not_prime_of_isComp hcomp)
  · exact ⟨q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4, hm⟩

lemma find_basesNo5_one (p2 p3 p4 : ℕ)
    (h : basesNo5Data.any (fun x => decide (x.1 = p2 ∧ x.2.1 = p3 ∧ x.2.2.1 = p4)) = true) :
    ∃ q0 L g P0 bad ds a2 a3 a4 ds2 ds3 ds4, (p2, p3, p4, q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4) ∈ basesNo5Data := by
  obtain ⟨⟨p2', p3', p4', q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4⟩, hm, hc⟩ := List.any_eq_true.mp h
  simp only [decide_eq_true_eq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  exact ⟨q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4, hm⟩

lemma find_dge2Pairs5 (p3 tag hi lo t A B : ℕ) (hlt : t < hi) (hlo : lo < t) (hp : t.Prime)
    (hcond : A * (t - 1) ≤ B * t)
    (h : (List.range hi).all (fun s => !(decide (lo < s ∧ s.Prime ∧ A * (s - 1) ≤ B * s)) ||
      dge2Pairs5.any (fun x => decide (x.1 = p3 ∧ x.2.1 = s ∧ x.2.2 = tag))) = true) :
    (p3, t, tag) ∈ dge2Pairs5 := by
  have h1 := List.all_eq_true.mp h t (List.mem_range.mpr hlt)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_and, List.any_eq_true, decide_eq_true_eq] at h1
  rcases h1 with hnot | ⟨⟨p3', t', tag'⟩, hm, rfl, rfl, rfl⟩
  · exact absurd hcond (hnot hlo hp)
  · exact hm

section MainProof

lemma three_dvd_excess_of_mod3 {m : ℕ} (h3m : 3 ∣ m) (h3sig : 3 ∣ sigma 1 m) (hab : 2 * m < sigma 1 m) :
    (sigma 1 m - 2 * m) % 3 = 0 := by
  obtain ⟨x, hx⟩ := h3sig
  obtain ⟨y, hy⟩ := h3m
  omega

lemma rank3_pseudoperfect {p3 a b c : ℕ}
    (hp3 : p3 = 7 ∨ p3 = 11 ∨ p3 = 13) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hab : (3 ^ a * 5 ^ b * p3 ^ c).Abundant)
    (hprim : ∀ d ∈ (3 ^ a * 5 ^ b * p3 ^ c).properDivisors, d.Deficient) :
    (3 ^ a * 5 ^ b * p3 ^ c).Pseudoperfect := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have hp3p : p3.Prime := by rcases hp3 with rfl | rfl | rfl <;> decide
  have hp3_gt5 : 5 < p3 := by rcases hp3 with rfl | rfl | rfl <;> omega
  let m := 3 ^ a * 5 ^ b * p3 ^ c
  have hmpos : 0 < m := by have := hp3p.pos; dsimp [m]; positivity
  have hab_nat : 2 * m < ppSum 3 a * ppSum 5 b * ppSum p3 c := by
    rw [← sigma_mul_coprime_three h3p h5p hp3p (by decide) hp3_gt5]
    exact (abund_iff_nat hmpos).mp hab
  have hcov : ∃ t ∈ w3Witnesses, t.1 = p3 ∧ t.2.1 ≤ a ∧ t.2.2.1 ≤ b ∧ t.2.2.2.1 ≤ c := by
    rcases hp3 with rfl | rfl | rfl
    · obtain ⟨t, ht, h1, h2, h3, _⟩ := checkMinCover_sound (a := a) (b := b) (c := c) (d := 0)
        (VValid.mk (h := none) h3p ha trivial (Or.inl rfl)) (VValid.mk (h := none) h5p hb trivial (Or.inl rfl))
        (VValid.mk (h := none) hp3p hc trivial (Or.inl rfl)) VValid.mk1
        (by simpa [vSigma, mkV, mkV1] using hab_nat) w3Cover_7_ok
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact ⟨(7, 2, 1, 2, [5, 7, 9, 15]), by simp [w3Witnesses], rfl, h1, h2, h3⟩
      · exact ⟨(7, 2, 2, 1, [1, 5, 7, 15, 21, 25]), by simp [w3Witnesses], rfl, h1, h2, h3⟩
      · exact ⟨(7, 3, 1, 1, [3, 5, 7, 15]), by simp [w3Witnesses], rfl, h1, h2, h3⟩
    · obtain ⟨t, ht, h1, h2, h3, _⟩ := checkMinCover_sound (a := a) (b := b) (c := c) (d := 0)
        (VValid.mk (h := none) h3p ha trivial (Or.inl rfl)) (VValid.mk (h := none) h5p hb trivial (Or.inl rfl))
        (VValid.mk (h := none) hp3p hc trivial (Or.inl rfl)) VValid.mk1
        (by simpa [vSigma, mkV, mkV1] using hab_nat) w3Cover_11_ok
      simp only [List.mem_singleton] at ht; subst ht
      exact ⟨(11, 3, 2, 1, [1, 5, 9, 15]), by simp [w3Witnesses], rfl, h1, h2, h3⟩
    · obtain ⟨t, ht, h1, h2, h3, _⟩ := checkMinCover_sound (a := a) (b := b) (c := c) (d := 0)
        (VValid.mk (h := none) h3p ha trivial (Or.inl rfl)) (VValid.mk (h := none) h5p hb trivial (Or.inl rfl))
        (VValid.mk (h := none) hp3p hc trivial (Or.inl rfl)) VValid.mk1
        (by simpa [vSigma, mkV, mkV1] using hab_nat) w3Cover_13_ok
      have hmem_fn : ∀ u ∈ [(3,3,2,0),(4,2,2,0),(4,3,1,0),(5,2,1,0)],
          ∃ w ∈ w3Witnesses, w.1 = 13 ∧ w.2.1 = u.1 ∧ w.2.2.1 = u.2.1 ∧ w.2.2.2.1 = u.2.2.1 := by decide
      obtain ⟨w, hw, hw1, hwa, hwb, hwc⟩ := hmem_fn t ht
      exact ⟨w, hw, hw1, by omega, by omega, by omega⟩
  obtain ⟨⟨p3', a0, b0, c0, wit⟩, hmem, hp3eq, ha0, hb0, hc0⟩ := hcov
  dsimp only at hp3eq ha0 hb0 hc0; subst p3'
  have hchk := List.all_eq_true.mp w3Witnesses_ok _ hmem
  let n0 := 3 ^ a0 * 5 ^ b0 * p3 ^ c0
  have hn0_pos : 0 < n0 := by have := hp3p.pos; dsimp [n0]; positivity
  have hn0_sig : ppSum 3 a0 * ppSum 5 b0 * ppSum p3 c0 = sigma 1 n0 :=
    (sigma_mul_coprime_three h3p h5p hp3p (by decide) hp3_gt5).symm
  have hn0_dvd : n0 ∣ m :=
    Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 ha0) (pow_dvd_pow 5 hb0)) (pow_dvd_pow p3 hc0)
  have hn0_ab : 2 * n0 < sigma 1 n0 := by
    have h1 : ∀ x ∈ w3Witnesses,
        2 * (3 ^ x.2.1 * 5 ^ x.2.2.1 * x.1 ^ x.2.2.2.1) < ppSum 3 x.2.1 * ppSum 5 x.2.2.1 * ppSum x.1 x.2.2.2.1 := by decide
    rw [← hn0_sig]; exact h1 _ hmem
  have heq : n0 = m := by
    by_contra hne
    have hmem' : n0 ∈ m.properDivisors := Nat.mem_properDivisors.mpr ⟨hn0_dvd, lt_of_le_of_ne (Nat.le_of_dvd hmpos hn0_dvd) hne⟩
    have := (defic_iff_nat hn0_pos).mp (hprim n0 hmem')
    omega
  change m.Pseudoperfect; rw [← heq]
  exact pseudoperfect_of_checkWitness hn0_pos hn0_sig hchk

lemma rank4_no5_pseudoperfect {p2 p3 p4 a b c d : ℕ}
    (hmem6 : (p2, p3, p4) ∈ [(7,11,13),(7,11,17),(7,11,19),(7,11,23),(7,13,17),(7,13,19)])
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hab : (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d).Abundant)
    (hprim : ∀ x ∈ (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d).properDivisors, x.Deficient) :
    (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d).Pseudoperfect := by
  have h3p : Nat.Prime 3 := by decide
  have hprimes : p2.Prime ∧ p3.Prime ∧ p4.Prime ∧ 7 ≤ p2 ∧ p2 < p3 ∧ p3 < p4 := by
    have : ∀ t ∈ [(7,11,13),(7,11,17),(7,11,19),(7,11,23),(7,13,17),(7,13,19)],
        t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ 7 ≤ t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 := by decide
    exact this _ hmem6
  obtain ⟨hp2, hp3, hp4, h7p2, hp23, hp34⟩ := hprimes
  let m := 3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d
  have hmpos : 0 < m := by have := hp2.pos; have := hp3.pos; have := hp4.pos; dsimp [m]; positivity
  have hab_nat : 2 * m < ppSum 3 a * ppSum p2 b * ppSum p3 c * ppSum p4 d := by
    rw [← sigma_mul_coprime_four h3p hp2 hp3 hp4 (by omega) hp23 hp34]
    exact (abund_iff_nat hmpos).mp hab
  have hcov_chk := List.all_eq_true.mp w4No5Covers_ok _ hmem6
  obtain ⟨u, hu, hu1, hu2, hu3, hu4⟩ := checkMinCover_sound (a := a) (b := b) (c := c) (d := d)
    (VValid.mk (h := none) h3p ha trivial (Or.inl rfl)) (VValid.mk (h := none) hp2 hb trivial (Or.inl rfl))
    (VValid.mk (h := none) hp3 hc trivial (Or.inl rfl)) (VValid.mk (h := none) hp4 hd trivial (Or.inl rfl))
    (by
      have : vSigma (mkV 3 2 none 1) a * vSigma (mkV p2 1 none 1) b * vSigma (mkV p3 1 none 1) c * vSigma (mkV p4 1 none 1) d =
          ppSum 3 a * ppSum p2 b * ppSum p3 c * ppSum p4 d := by
        simp [vSigma, mkV, h3p.ne_one, hp2.ne_one, hp3.ne_one, hp4.ne_one]
      rw [this]; exact hab_nat)
    hcov_chk
  unfold w4No5Mins at hu
  obtain ⟨w, hw_filt, hw_eq⟩ := List.mem_map.mp hu
  rw [List.mem_filter] at hw_filt
  obtain ⟨hw_mem, hw_cond⟩ := hw_filt
  simp only [Bool.and_eq_true, beq_iff_eq] at hw_cond
  rcases w with ⟨q2, q3, q4, a0, b0, c0, d0, wit⟩
  simp only at hw_cond hw_eq
  obtain ⟨⟨hq2, hq3⟩, hq4⟩ := hw_cond
  subst q2; subst q3; subst q4
  rw [← hw_eq] at hu1 hu2 hu3 hu4
  have hchk := List.all_eq_true.mp w4No5Witnesses_ok _ hw_mem
  let n0 := 3 ^ a0 * p2 ^ b0 * p3 ^ c0 * p4 ^ d0
  have hn0_pos : 0 < n0 := by have := hp2.pos; have := hp3.pos; have := hp4.pos; dsimp [n0]; positivity
  have hn0_sig : ppSum 3 a0 * ppSum p2 b0 * ppSum p3 c0 * ppSum p4 d0 = sigma 1 n0 :=
    (sigma_mul_coprime_four h3p hp2 hp3 hp4 (by omega) hp23 hp34).symm
  have hn0_dvd : n0 ∣ m :=
    Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 hu1) (pow_dvd_pow p2 hu2)) (pow_dvd_pow p3 hu3)) (pow_dvd_pow p4 hu4)
  have hn0_ab : 2 * n0 < sigma 1 n0 := by
    have h1 : ∀ x ∈ w4No5Witnesses,
        let (r2, r3, r4, x1, x2, x3, x4, _) := x
        2 * (3 ^ x1 * r2 ^ x2 * r3 ^ x3 * r4 ^ x4) < ppSum 3 x1 * ppSum r2 x2 * ppSum r3 x3 * ppSum r4 x4 := by decide
    rw [← hn0_sig]; exact h1 _ hw_mem
  have heq : n0 = m := by
    by_contra hne
    have hmem' : n0 ∈ m.properDivisors := Nat.mem_properDivisors.mpr ⟨hn0_dvd, lt_of_le_of_ne (Nat.le_of_dvd hmpos hn0_dvd) hne⟩
    have := (defic_iff_nat hn0_pos).mp (hprim n0 hmem')
    omega
  change m.Pseudoperfect; rw [← heq]
  exact pseudoperfect_of_checkWitness hn0_pos hn0_sig hchk

/-- Helper: apply a bases3Data entry to omega = 4, 5 | m (B = 3^a * 5^b * p3^c, m = B * q^e). -/
lemma rank4_5_from_base3 {a0 b0 p3 L g P0 bestD relN a b c q e : ℕ} {bad ds ds3p3 : List ℕ}
    (hmem : (a0, b0, p3, L, g, P0, bad, ds, bestD, ds3p3, relN) ∈ bases3Data)
    (hp3 : p3.Prime) (hq : q.Prime) (hp3_gt5 : 5 < p3) (hp3q : p3 < q)
    (ha : a0 ≤ a) (hb : b0 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e)
    (ha_fix : (a0 = 2 ∧ b0 = 1) → a = 2) (hb_fix : b0 = 1 → b = 1)
    (hab : (3 ^ a * 5 ^ b * p3 ^ c * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 ^ a * 5 ^ b * p3 ^ c * q ^ e).properDivisors, x.Deficient)
    (hEok : L ≤ sigma 1 (3 ^ a * 5 ^ b * p3 ^ c * q ^ e) - 2 * (3 ^ a * 5 ^ b * p3 ^ c * q ^ e) ∨
            (sigma 1 (3 ^ a * 5 ^ b * p3 ^ c * q ^ e) - 2 * (3 ^ a * 5 ^ b * p3 ^ c * q ^ e)) ∉ bad) :
    (3 ^ a * 5 ^ b * p3 ^ c * q ^ e).Pseudoperfect := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have ha0_ge2 : 2 ≤ a0 := by have : ∀ x ∈ bases3Data, 2 ≤ x.1 := (by decide); exact this _ hmem
  have hb0_ge1 : 1 ≤ b0 := by have : ∀ x ∈ bases3Data, 1 ≤ x.2.1 := (by decide); exact this _ hmem
  have hok := List.all_eq_true.mp bases3Data_ok _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hmeta, _⟩, _⟩, _⟩, _⟩ := hok
  obtain ⟨hL1, rfl, _, hbig0, _, _, _, _⟩ := hmeta
  obtain ⟨hcov, hgap, hbad, hP_ge⟩ := lift_base3 hmem hp3 hp3_gt5 ha hb hc ha_fix hb_fix
  let B := 3 ^ a * 5 ^ b * p3 ^ c
  have hBpos : 0 < B := by have := hp3.pos; dsimp [B]; positivity
  have hBgt1 : 1 < B := by
    have : 9 ≤ 3 ^ a := by have := pow_le_pow_right₀ (by decide : 1 ≤ 3) (show 2 ≤ a by omega); norm_num at this; exact this
    have : 0 < 5 ^ b * p3 ^ c := by have := hp3.pos; positivity
    dsimp [B]; nlinarith
  have hcop : B.Coprime q :=
    Nat.Coprime.mul_left (Nat.Coprime.mul_left (((Nat.coprime_primes h3p hq).mpr (by omega)).pow_left a)
      (((Nat.coprime_primes h5p hq).mpr (by omega)).pow_left b))
      (((Nat.coprime_primes hp3 hq).mpr (by omega)).pow_left c)
  have hBdef : sigma 1 B < 2 * B := by
    have hmemB : B ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right B _, by simpa using Nat.mul_lt_mul_of_pos_left (one_lt_pow₀ hq.one_lt (by omega)) hBpos⟩
    exact (defic_iff_nat hBpos).mp (hprim B hmemB)
  have hD2 : 2 ≤ 2 * B - sigma 1 B := dge2_3p_5 hp3 hp3_gt5 (by omega) (by omega) hc hBdef
  exact apply_final_prime_or_bad hBgt1 hq hcop (by omega) he hL1 (by decide) hab hprim hD2
    (le_trans hbig0 hP_ge) hcov hgap hbad hEok

/-- Helper: when b is odd (or 3 | E), E ∉ bad for any entry in bases3Data. -/
lemma not_mem_bad_of_three_dvd {a0 b0 p3 L g P0 bestD relN E : ℕ} {bad ds ds3p3 : List ℕ}
    (hmem : (a0, b0, p3, L, g, P0, bad, ds, bestD, ds3p3, relN) ∈ bases3Data)
    (h3E : E % 3 = 0) : E ∉ bad := by
  have hok := List.all_eq_true.mp bases3Data_ok _ hmem
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  intro hm
  exact hok.1.1.1.2 E hm h3E

lemma three_dvd_E_of_five_odd {m b : ℕ} (h3m : 3 ∣ m) (hsig5 : ppSum 5 b ∣ sigma 1 m)
    (hbodd : b % 2 = 1) (hab : 2 * m < sigma 1 m) : (sigma 1 m - 2 * m) % 3 = 0 :=
  three_dvd_excess_of_mod3 h3m ((three_dvd_ppSum_odd (by decide) (by decide) hbodd).trans hsig5) hab

set_option maxHeartbeats 1600000 in
lemma rank4_5_pseudoperfect {p3 q a b c e : ℕ}
    (hp3_mem : p3 ∈ ({7, 11, 13, 17, 19, 23, 29} : Finset ℕ))
    (hq : q.Prime) (hp3q : p3 < q) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hab : (3 ^ a * 5 ^ b * p3 ^ c * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 ^ a * 5 ^ b * p3 ^ c * q ^ e).properDivisors, x.Deficient) :
    (3 ^ a * 5 ^ b * p3 ^ c * q ^ e).Pseudoperfect := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have hp3 : p3.Prime := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp3_mem
    rcases hp3_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hp3_gt5 : 5 < p3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp3_mem
    rcases hp3_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  let m := 3 ^ a * 5 ^ b * p3 ^ c * q ^ e
  have hmpos : 0 < m := by have := hp3.pos; have := hq.pos; dsimp [m]; positivity
  have hab_nat : 2 * m < sigma 1 m := (abund_iff_nat hmpos).mp hab
  have hsm : sigma 1 m = ppSum 3 a * ppSum 5 b * ppSum p3 c * ppSum q e :=
    sigma_mul_coprime_four h3p h5p hp3 hq (by decide) hp3_gt5 hp3q
  have h3m : 3 ∣ m := (dvd_pow_self 3 (by omega)).trans ((dvd_mul_right _ _).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _)))
  have h5sig : ppSum 5 b ∣ sigma 1 m := by rw [hsm]; exact ⟨ppSum 3 a * ppSum p3 c * ppSum q e, by ring⟩
  have hBdef : sigma 1 (3 ^ a * 5 ^ b * p3 ^ c) < 2 * (3 ^ a * 5 ^ b * p3 ^ c) := by
    have hmemB : 3 ^ a * 5 ^ b * p3 ^ c ∈ m.properDivisors := Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right _ _, by simpa [m] using Nat.mul_lt_mul_of_pos_left (one_lt_pow₀ hq.one_lt (by omega)) (by have := hp3.pos; positivity)⟩
    exact (defic_iff_nat (by have := hp3.pos; positivity)).mp (hprim _ hmemB)
  -- Helper: checkBox4 for b even
  have run_cb4 (l1 l3 s3 L : ℕ) (h1 : Option ℕ) (bad : List ℕ) (q0 : ℕ)
      (hmem_cb : (p3, q0, l1, h1, l3, s3, L, bad) ∈
        [(11, 13, 2, some 2, 2, 2, 23, [2, 7, 22]),
         (13, 17, 2, some 4, 1, 1, 12, [2, 7, 11]),
         (17, 19, 2, none,   2, 2, 12, [2, 7, 11]),
         (19, 23, 2, none,   1, 1, 12, [2, 7, 11]),
         (23, 29, 2, none,   2, 2, 23, [2, 7, 11, 22]),
         (29, 31, 3, none,   2, 2, 23, [2, 7, 11, 22])])
      (hq0 : q0 ≤ q) (hl1 : l1 ≤ a) (hh1 : leOpt a h1)
      (hb2 : 2 ≤ b) (hbeven : b % 2 = 0)
      (hl3 : l3 ≤ c) (hs3 : s3 = 1 ∨ (s3 = 2 ∧ l3 % 2 = 0 ∧ c % 2 = 0))
      (hbad3 : ∀ x ∈ bad, x % 3 ≠ 0) :
      L ≤ sigma 1 m - 2 * m ∨ (sigma 1 m - 2 * m) ∉ bad := by
    have hchk := List.all_eq_true.mp cb4_5_ok _ hmem_cb
    have hres := checkBox_sound (a := a) (b := b) (c := c) (d := 0) (q := q) (e := e) (q1 := none)
      (VValid.mk h3p hl1 hh1 (Or.inl rfl))
      (VValid.mk (h := none) h5p hb2 trivial (Or.inr ⟨rfl, rfl, hbeven⟩))
      (VValid.mk (h := none) hp3 hl3 trivial hs3) VValid.mk1
      hq hq0 trivial he
      (by
        simp only [mkV, mkV1, pow_zero, mul_one, vSigma, h3p.ne_one, h5p.ne_one, hp3.ne_one, ↓reduceIte]
        exact sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5)
      (fun u1 u2 u3 u4 hu1 hu2 hu3 hu4 hp1' hp2' hp3' hp4' => by
        rcases hu4 with ⟨_, _, hpl4, hsl4, _, _, _, _⟩ | ⟨hp4p, _⟩
        · simp only [hpl4, hsl4, mul_one]
          rcases hu1 with ⟨hp1_1, _⟩ | ⟨_, _, _, hpl1, hsl1, _⟩
          · rw [hp1'] at hp1_1; simp [mkV] at hp1_1
          rcases hu2 with ⟨hp2_1, _⟩ | ⟨_, _, _, hpl2, hsl2, _⟩
          · rw [hp2'] at hp2_1; simp [mkV] at hp2_1
          rcases hu3 with ⟨hp3_1, _⟩ | ⟨_, _, _, hpl3, hsl3, _⟩
          · rw [hp3'] at hp3_1; simp only [mkV] at hp3_1; exact absurd hp3_1 hp3.ne_one
          rw [hpl1, hpl2, hpl3, hsl1, hsl2, hsl3, hp1', hp2', hp3']
          simp only [mkV]
          exact sigma_mul_coprime_three h3p h5p hp3 (by decide) hp3_gt5
        · rw [hp4'] at hp4p; simp [mkV1] at hp4p)
      (by
        simp only [mkV, mkV1, pow_zero, mul_one]
        exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (((Nat.coprime_primes h3p hq).mpr (by omega)).pow_left a)
          (((Nat.coprime_primes h5p hq).mpr (by omega)).pow_left b))
          (((Nat.coprime_primes hp3 hq).mpr (by omega)).pow_left c))
      (by simpa [mkV, mkV1] using hab)
      (by simpa [mkV, mkV1] using hprim) hchk
    simp only [mkV, mkV1, pow_zero, mul_one] at hres
    rcases hres with h1 | ⟨_, h3E | ⟨hq3, heodd⟩⟩ | hnb
    · left; exact h1
    · right; intro hm; exact hbad3 _ hm h3E
    · right; intro hm
      have hqsig : ppSum q e ∣ sigma 1 m := by rw [hsm]; exact dvd_mul_left _ _
      exact hbad3 _ hm (three_dvd_excess_of_mod3 h3m ((three_dvd_ppSum_odd hq.two_le hq3 heodd).trans hqsig) hab_nat)
    · right; exact hnb
  -- Note: for b even, if 3 | E then E ∉ bad automatically! So we may assume 3 ∤ E => c even if p3%3=2!
  -- Now dispatch by p3!
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp3_mem
  rcases hp3_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- p3 = 7: (a,b,c) MUST be (2,1,1)!
    have h211 : a = 2 ∧ b = 1 ∧ c = 1 := by
      have ha2 : a = 2 := by
        by_contra hne; have ha3 : 3 ≤ a := by omega
        have hm := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_mono_exp (p := 3) (by decide) ha3)
          (ppSum_mono_exp (p := 5) (by decide) hb)) (ppSum_mono_exp (p := 7) (by decide) hc)
        have hval : ppSum 3 3 = 40 ∧ ppSum 5 1 = 6 ∧ ppSum 7 1 = 8 := by decide
        rw [hval.1, hval.2.1, hval.2.2] at hm
        rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide)] at hBdef
        have : 0 < 3 ^ a * 5 ^ b * 7 ^ c := (by positivity); nlinarith
      have hb1 : b = 1 := by
        by_contra hne; have hb2 : 2 ≤ b := by omega
        have hm := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_mono_exp (p := 3) (by decide) ha)
          (ppSum_mono_exp (p := 5) (by decide) hb2)) (ppSum_mono_exp (p := 7) (by decide) hc)
        have hval : ppSum 3 2 = 13 ∧ ppSum 5 2 = 31 ∧ ppSum 7 1 = 8 := by decide
        rw [hval.1, hval.2.1, hval.2.2] at hm
        rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide)] at hBdef
        have : 0 < 3 ^ a * 5 ^ b * 7 ^ c := (by positivity); nlinarith
      have hc1 : c = 1 := by
        by_contra hne; have hc2 : 2 ≤ c := by omega
        have hm := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_mono_exp (p := 3) (by decide) ha)
          (ppSum_mono_exp (p := 5) (by decide) hb)) (ppSum_mono_exp (p := 7) (by decide) hc2)
        have hval : ppSum 3 2 = 13 ∧ ppSum 5 1 = 6 ∧ ppSum 7 2 = 57 := by decide
        rw [hval.1, hval.2.1, hval.2.2] at hm
        rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide)] at hBdef
        have : 0 < 3 ^ a * 5 ^ b * 7 ^ c := (by positivity); nlinarith
      exact ⟨ha2, hb1, hc1⟩
    obtain ⟨rfl, rfl, rfl⟩ := h211
    have hmem0 : (2, 1, 7, 3, 2, 309, [2], [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105], 9, [1, 3, 7, 9, 21], 0) ∈ bases3Data := by simp [bases3Data]
    exact rank4_5_from_base3 hmem0 (by decide) hq (by decide) hp3q le_rfl le_rfl le_rfl he (fun _ => rfl) (fun _ => rfl) hab hprim
      (Or.inr (not_mem_bad_of_three_dvd hmem0 (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
  · -- p3 = 11
    by_cases hb1 : b = 1
    · subst hb1
      by_cases ha2 : a = 2
      · subst ha2
        have hmem0 := find_bases3 2 1 11 23 2 441 [2, 7, 22] (by decide)
        obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
        exact rank4_5_from_base3 hm (by decide) hq (by decide) hp3q le_rfl le_rfl hc he (fun _ => rfl) (fun _ => rfl) hab hprim
          (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
      · have hmem0 := find_bases3 3 1 11 23 2 1395 [2, 7, 22] (by decide)
        obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
        exact rank4_5_from_base3 hm (by decide) hq (by decide) hp3q (by omega) le_rfl hc he (by omega) (fun _ => rfl) hab hprim
          (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
    · have hb2 : 2 ≤ b := by omega
      have hmem0 := find_bases3 2 2 11 23 2 2361 [2, 7, 22] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      apply rank4_5_from_base3 hm (by decide) hq (by decide) hp3q ha hb2 hc he (by omega) (by omega) hab hprim
      by_cases hbodd : b % 2 = 1
      · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
      · by_cases hcodd : c % 2 = 1
        · have hcsig : ppSum 11 c ∣ sigma 1 m := by rw [hsm]; exact ⟨ppSum 3 a * ppSum 5 b * ppSum q e, by ring⟩
          exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_excess_of_mod3 h3m ((three_dvd_ppSum_odd (by decide) (by decide) hcodd).trans hcsig) hab_nat))
        · have ha2 : a = 2 := by
            by_contra hne; have ha3 : 3 ≤ a := by omega
            have hm1 := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_mono_exp (p := 3) (by decide) ha3)
              (ppSum_mono_exp (p := 5) (by decide) hb2)) (ppSum_mono_exp (p := 11) (by decide) hc)
            have hval : ppSum 3 3 = 40 ∧ ppSum 5 2 = 31 ∧ ppSum 11 1 = 12 := by decide
            rw [hval.1, hval.2.1, hval.2.2] at hm1
            rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide)] at hBdef
            have : 0 < 3 ^ a * 5 ^ b * 11 ^ c := (by positivity); nlinarith
          have hq13 : 13 ≤ q := by by_contra! hlt; exact (by decide : ∀ t < 13, 11 < t → ¬ t.Prime) q hlt hp3q hq
          exact run_cb4 2 2 2 23 (some 2) [2, 7, 22] 13 (by decide) hq13 ha (by simp [leOpt, ha2])
            hb2 (by omega) (by omega) (Or.inr ⟨rfl, rfl, by omega⟩) (by decide)
  · -- p3 = 13
    by_cases hb1 : b = 1
    · subst hb1
      by_cases ha2 : a = 2
      · subst ha2
        have hmem0 := find_bases3 2 1 13 36 2 507 [2, 7, 11, 35] (by decide)
        obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
        exact rank4_5_from_base3 hm (by decide) hq (by decide) hp3q le_rfl le_rfl hc he (fun _ => rfl) (fun _ => rfl) hab hprim
          (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
      · have hmem0 := find_bases3 3 1 13 12 2 1605 [2, 7, 11] (by decide)
        obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
        exact rank4_5_from_base3 hm (by decide) hq (by decide) hp3q (by omega) le_rfl hc he (by omega) (fun _ => rfl) hab hprim
          (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
    · have hb2 : 2 ≤ b := by omega
      have hmem0 := find_bases3 2 2 13 12 2 2717 [2, 7, 11] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      apply rank4_5_from_base3 hm (by decide) hq (by decide) hp3q ha hb2 hc he (by omega) (by omega) hab hprim
      by_cases hbodd : b % 2 = 1
      · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
      · have ha4 : a ≤ 4 := by
          by_contra! h5
          have hm1 := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_mono_exp (p := 3) (by decide) h5)
            (ppSum_mono_exp (p := 5) (by decide) hb2)) (ppSum_mono_exp (p := 13) (by decide) hc)
          have hval : ppSum 3 5 = 364 ∧ ppSum 5 2 = 31 ∧ ppSum 13 1 = 14 := by decide
          rw [hval.1, hval.2.1, hval.2.2] at hm1
          rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide)] at hBdef
          have : 0 < 3 ^ a * 5 ^ b * 13 ^ c := (by positivity); nlinarith
        have hq17 : 17 ≤ q := by by_contra! hlt; exact (by decide : ∀ t < 17, 13 < t → ¬ t.Prime) q hlt hp3q hq
        exact run_cb4 2 1 1 12 (some 4) [2, 7, 11] 17 (by decide) hq17 ha ha4
          hb2 (by omega) hc (Or.inl rfl) (by decide)
  · -- p3 = 17: a=2 ∧ b=1 impossible!
    have hnot21 : ¬ (a = 2 ∧ b = 1) := by
      rintro ⟨rfl, rfl⟩
      have hq19 : 19 ≤ q := by by_contra! hlt; exact (by decide : ∀ t < 19, 17 < t → ¬ t.Prime) q hlt hp3q hq
      have l17 := (ppSum_lt_lim (p := 17) (a := c) (by decide)).le
      have lq := (ppSum_lt_lim (p := q) (a := e) hq.two_le).le
      have hf := frac_anti (by decide : 2 ≤ 19) hq19
      have hval : ppSum 3 2 = 13 ∧ ppSum 5 1 = 6 := by decide
      rw [hsm, hval.1, hval.2] at hab_nat
      have h1 : 13 * 6 * ppSum 17 c * ppSum q e * (16 * (q - 1)) ≤ 13 * 6 * 17 * q * (17 ^ c * q ^ e) := by
        have hm := Nat.mul_le_mul_left (13 * 6) (Nat.mul_le_mul l17 lq); linarith
      have h2 := Nat.mul_le_mul_right (17 ^ c * q ^ e) (Nat.mul_le_mul_left (13 * 6 * 17) hf)
      have h3 := Nat.mul_le_mul_right 18 h1
      have h4 := Nat.mul_lt_mul_of_pos_right hab_nat (by have : 0 < q - 1 := (by omega); positivity : 0 < 16 * (q - 1) * 18)
      have h5 : 13 * 6 * 17 * 19 * (q - 1) * (17 ^ c * q ^ e) < 2 * (3 ^ 2 * 5 ^ 1 * 17 ^ c * q ^ e) * (16 * (q - 1) * 18) := by
        have hpos : 0 < (q - 1) * (17 ^ c * q ^ e) := by have : 0 < q - 1 := (by omega); have := hq.pos; positivity
        nlinarith
      dsimp [m] at h4; linarith
    by_cases hb1 : b = 1
    · subst hb1
      have hmem0 := find_bases3 3 1 17 12 2 2025 [2, 7, 11] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      exact rank4_5_from_base3 hm (by decide) hq (by decide) hp3q (by omega) le_rfl hc he (by omega) (fun _ => rfl) hab hprim
        (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
    · have hb2 : 2 ≤ b := by omega
      have hmem0 := find_bases3 2 2 17 12 2 3429 [2, 7, 11] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      apply rank4_5_from_base3 hm (by decide) hq (by decide) hp3q ha hb2 hc he (by omega) (by omega) hab hprim
      by_cases hbodd : b % 2 = 1
      · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
      · by_cases hcodd : c % 2 = 1
        · have hcsig : ppSum 17 c ∣ sigma 1 m := by rw [hsm]; exact ⟨ppSum 3 a * ppSum 5 b * ppSum q e, by ring⟩
          exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_excess_of_mod3 h3m ((three_dvd_ppSum_odd (by decide) (by decide) hcodd).trans hcsig) hab_nat))
        · have hq19 : 19 ≤ q := by by_contra! hlt; exact (by decide : ∀ t < 19, 17 < t → ¬ t.Prime) q hlt hp3q hq
          exact run_cb4 2 2 2 12 none [2, 7, 11] 19 (by decide) hq19 ha trivial
            hb2 (by omega) (by omega) (Or.inr ⟨rfl, rfl, by omega⟩) (by decide)
  · -- p3 = 19: a=2 ∧ b=1 impossible!
    have hnot21 : ¬ (a = 2 ∧ b = 1) := by
      rintro ⟨rfl, rfl⟩
      have hq23 : 23 ≤ q := by by_contra! hlt; exact (by decide : ∀ t < 23, 19 < t → ¬ t.Prime) q hlt hp3q hq
      have l19 := (ppSum_lt_lim (p := 19) (a := c) (by decide)).le
      have lq := (ppSum_lt_lim (p := q) (a := e) hq.two_le).le
      have hf := frac_anti (by decide : 2 ≤ 23) hq23
      have hval : ppSum 3 2 = 13 ∧ ppSum 5 1 = 6 := by decide
      rw [hsm, hval.1, hval.2] at hab_nat
      have h1 : 13 * 6 * ppSum 19 c * ppSum q e * (18 * (q - 1)) ≤ 13 * 6 * 19 * q * (19 ^ c * q ^ e) := by
        have hm := Nat.mul_le_mul_left (13 * 6) (Nat.mul_le_mul l19 lq); linarith
      have h2 := Nat.mul_le_mul_right (19 ^ c * q ^ e) (Nat.mul_le_mul_left (13 * 6 * 19) hf)
      have h3 := Nat.mul_le_mul_right 22 h1
      have h4 := Nat.mul_lt_mul_of_pos_right hab_nat (by have : 0 < q - 1 := (by omega); positivity : 0 < 18 * (q - 1) * 22)
      have h5 : 13 * 6 * 19 * 23 * (q - 1) * (19 ^ c * q ^ e) < 2 * (3 ^ 2 * 5 ^ 1 * 19 ^ c * q ^ e) * (18 * (q - 1) * 22) := by
        have hpos : 0 < (q - 1) * (19 ^ c * q ^ e) := by have : 0 < q - 1 := (by omega); have := hq.pos; positivity
        nlinarith
      dsimp [m] at h4; linarith
    by_cases hb1 : b = 1
    · subst hb1
      have hmem0 := find_bases3 3 1 19 27 2 2235 [2, 7, 11, 26] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      exact rank4_5_from_base3 hm (by decide) hq (by decide) hp3q (by omega) le_rfl hc he (by omega) (fun _ => rfl) hab hprim
        (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
    · have hb2 : 2 ≤ b := by omega
      have hmem0 := find_bases3 2 2 19 12 2 3785 [2, 7, 11] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      apply rank4_5_from_base3 hm (by decide) hq (by decide) hp3q ha hb2 hc he (by omega) (by omega) hab hprim
      by_cases hbodd : b % 2 = 1
      · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
      · have hq23 : 23 ≤ q := by by_contra! hlt; exact (by decide : ∀ t < 23, 19 < t → ¬ t.Prime) q hlt hp3q hq
        exact run_cb4 2 1 1 12 none [2, 7, 11] 23 (by decide) hq23 ha trivial
          hb2 (by omega) hc (Or.inl rfl) (by decide)
  · -- p3 = 23: b=1 impossible! (3/2)*(6/5)*(23/22)*(29/28) = 1.948 < 2!
    have hb2 : 2 ≤ b := by
      by_contra! hlt; have hb1 : b = 1 := (by omega); subst hb1
      have hq29 : 29 ≤ q := by by_contra! hl; exact (by decide : ∀ t < 29, 23 < t → ¬ t.Prime) q hl hp3q hq
      have l3 := (ppSum_lt_lim (p := 3) (a := a) (by decide)).le
      have l23 := (ppSum_lt_lim (p := 23) (a := c) (by decide)).le
      have lq := (ppSum_lt_lim (p := q) (a := e) hq.two_le).le
      have hf := frac_anti (by decide : 2 ≤ 29) hq29
      have hval : ppSum 5 1 = 6 := by decide
      rw [hsm, hval] at hab_nat
      have h1 : ppSum 3 a * 6 * ppSum 23 c * ppSum q e * (2 * 22 * (q - 1)) ≤ 3 * 6 * 23 * q * (3 ^ a * 23 ^ c * q ^ e) := by
        have hm := Nat.mul_le_mul_left 6 (Nat.mul_le_mul (Nat.mul_le_mul l3 l23) lq); linarith
      have h2 := Nat.mul_le_mul_right (3 ^ a * 23 ^ c * q ^ e) (Nat.mul_le_mul_left (3 * 6 * 23) hf)
      have h3 := Nat.mul_le_mul_right 28 h1
      have h4 := Nat.mul_lt_mul_of_pos_right hab_nat (by have : 0 < q - 1 := (by omega); positivity : 0 < 2 * 22 * (q - 1) * 28)
      have h5 : 3 * 6 * 23 * 29 * (q - 1) * (3 ^ a * 23 ^ c * q ^ e) < 2 * (3 ^ a * 5 ^ 1 * 23 ^ c * q ^ e) * (2 * 22 * (q - 1) * 28) := by
        have hpos : 0 < (q - 1) * (3 ^ a * 23 ^ c * q ^ e) := by have : 0 < q - 1 := (by omega); have := hq.pos; positivity
        nlinarith
      dsimp [m] at h4; linarith
    have hmem0 := find_bases3 2 2 23 23 2 4497 [2, 7, 11, 22] (by decide)
    obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
    apply rank4_5_from_base3 hm (by decide) hq (by decide) hp3q ha hb2 hc he (by omega) (by omega) hab hprim
    by_cases hbodd : b % 2 = 1
    · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
    · by_cases hcodd : c % 2 = 1
      · have hcsig : ppSum 23 c ∣ sigma 1 m := by rw [hsm]; exact ⟨ppSum 3 a * ppSum 5 b * ppSum q e, by ring⟩
        exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_excess_of_mod3 h3m ((three_dvd_ppSum_odd (by decide) (by decide) hcodd).trans hcsig) hab_nat))
      · have hq29 : 29 ≤ q := by by_contra! hlt; exact (by decide : ∀ t < 29, 23 < t → ¬ t.Prime) q hlt hp3q hq
        exact run_cb4 2 2 2 23 none [2, 7, 11, 22] 29 (by decide) hq29 ha trivial
          hb2 (by omega) (by omega) (Or.inr ⟨rfl, rfl, by omega⟩) (by decide)
  · -- p3 = 29: a >= 3 AND b >= 2!
    have hq31 : 31 ≤ q := by by_contra! hl; exact (by decide : ∀ t < 31, 29 < t → ¬ t.Prime) q hl hp3q hq
    have ha3 : 3 ≤ a := by
      by_contra! hlt; have ha2 : a = 2 := (by omega); subst ha2
      have l5 := (ppSum_lt_lim (p := 5) (a := b) (by decide)).le
      have l29 := (ppSum_lt_lim (p := 29) (a := c) (by decide)).le
      have lq := (ppSum_lt_lim (p := q) (a := e) hq.two_le).le
      have hf := frac_anti (by decide : 2 ≤ 31) hq31
      have hval : ppSum 3 2 = 13 := by decide
      rw [hsm, hval] at hab_nat
      have h1 : 13 * ppSum 5 b * ppSum 29 c * ppSum q e * (4 * 28 * (q - 1)) ≤ 13 * 5 * 29 * q * (5 ^ b * 29 ^ c * q ^ e) := by
        have hm := Nat.mul_le_mul_left 13 (Nat.mul_le_mul (Nat.mul_le_mul l5 l29) lq); linarith
      have h2 := Nat.mul_le_mul_right (5 ^ b * 29 ^ c * q ^ e) (Nat.mul_le_mul_left (13 * 5 * 29) hf)
      have h3 := Nat.mul_le_mul_right 30 h1
      have h4 := Nat.mul_lt_mul_of_pos_right hab_nat (by have : 0 < q - 1 := (by omega); positivity : 0 < 4 * 28 * (q - 1) * 30)
      have h5 : 13 * 5 * 29 * 31 * (q - 1) * (5 ^ b * 29 ^ c * q ^ e) < 2 * (3 ^ 2 * 5 ^ b * 29 ^ c * q ^ e) * (4 * 28 * (q - 1) * 30) := by
        have hpos : 0 < (q - 1) * (5 ^ b * 29 ^ c * q ^ e) := by have : 0 < q - 1 := (by omega); have := hq.pos; positivity
        nlinarith
      dsimp [m] at h4; linarith
    have hb2 : 2 ≤ b := by
      by_contra! hlt; have hb1 : b = 1 := (by omega); subst hb1
      have l3 := (ppSum_lt_lim (p := 3) (a := a) (by decide)).le
      have l29 := (ppSum_lt_lim (p := 29) (a := c) (by decide)).le
      have lq := (ppSum_lt_lim (p := q) (a := e) hq.two_le).le
      have hf := frac_anti (by decide : 2 ≤ 31) hq31
      have hval : ppSum 5 1 = 6 := by decide
      rw [hsm, hval] at hab_nat
      have h1 : ppSum 3 a * 6 * ppSum 29 c * ppSum q e * (2 * 28 * (q - 1)) ≤ 3 * 6 * 29 * q * (3 ^ a * 29 ^ c * q ^ e) := by
        have hm := Nat.mul_le_mul_left 6 (Nat.mul_le_mul (Nat.mul_le_mul l3 l29) lq); linarith
      have h2 := Nat.mul_le_mul_right (3 ^ a * 29 ^ c * q ^ e) (Nat.mul_le_mul_left (3 * 6 * 29) hf)
      have h3 := Nat.mul_le_mul_right 30 h1
      have h4 := Nat.mul_lt_mul_of_pos_right hab_nat (by have : 0 < q - 1 := (by omega); positivity : 0 < 2 * 28 * (q - 1) * 30)
      have h5 : 3 * 6 * 29 * 31 * (q - 1) * (3 ^ a * 29 ^ c * q ^ e) < 2 * (3 ^ a * 5 ^ 1 * 29 ^ c * q ^ e) * (2 * 28 * (q - 1) * 30) := by
        have hpos : 0 < (q - 1) * (3 ^ a * 29 ^ c * q ^ e) := by have : 0 < q - 1 := (by omega); have := hq.pos; positivity
        nlinarith
      dsimp [m] at h4; linarith
    have hmem0 := find_bases3 3 2 29 23 2 17625 [2, 7, 11, 22] (by decide)
    obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
    apply rank4_5_from_base3 hm (by decide) hq (by decide) hp3q ha3 hb2 hc he (by omega) (by omega) hab hprim
    by_cases hbodd : b % 2 = 1
    · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
    · by_cases hcodd : c % 2 = 1
      · have hcsig : ppSum 29 c ∣ sigma 1 m := by rw [hsm]; exact ⟨ppSum 3 a * ppSum 5 b * ppSum q e, by ring⟩
        exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_excess_of_mod3 h3m ((three_dvd_ppSum_odd (by decide) (by decide) hcodd).trans hcsig) hab_nat))
      · exact run_cb4 3 2 2 23 none [2, 7, 11, 22] 31 (by decide) hq31 ha3 trivial
          hb2 (by omega) (by omega) (Or.inr ⟨rfl, rfl, by omega⟩) (by decide)

end MainProof

section MainProofRank5

/-- Helper: checkBox for 4-prime B (omega = 5). -/
lemma run_cb_four {p1 p2 p3 p4 a b c d q e l1 l2 l3 l4 s1 s2 s3 s4 q0 L : ℕ}
    {h1 h2 h3 h4 : Option ℕ} {bad : List ℕ} {kill3 : Bool}
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hp3 : p3.Prime) (hp4 : p4.Prime) (hq : q.Prime)
    (h12 : p1 < p2) (h23 : p2 < p3) (h34 : p3 < p4) (h4q : p4 < q)
    (hl1 : l1 ≤ a) (hh1 : leOpt a h1) (hs1 : s1 = 1 ∨ (s1 = 2 ∧ l1 % 2 = 0 ∧ a % 2 = 0))
    (hl2 : l2 ≤ b) (hh2 : leOpt b h2) (hs2 : s2 = 1 ∨ (s2 = 2 ∧ l2 % 2 = 0 ∧ b % 2 = 0))
    (hl3 : l3 ≤ c) (hh3 : leOpt c h3) (hs3 : s3 = 1 ∨ (s3 = 2 ∧ l3 % 2 = 0 ∧ c % 2 = 0))
    (hl4 : l4 ≤ d) (hh4 : leOpt d h4) (hs4 : s4 = 1 ∨ (s4 = 2 ∧ l4 % 2 = 0 ∧ d % 2 = 0))
    (hq0 : q0 ≤ q) (he : 1 ≤ e)
    (hab : (p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d * q ^ e).properDivisors, x.Deficient)
    (hchk : checkBox 45 (mkV p1 l1 h1 s1) (mkV p2 l2 h2 s2) (mkV p3 l3 h3 s3) (mkV p4 l4 h4 s4) q0 none L bad kill3 = true) :
    let m := p1 ^ a * p2 ^ b * p3 ^ c * p4 ^ d * q ^ e
    let E := sigma 1 m - 2 * m
    L ≤ E ∨ (kill3 = true ∧ (E % 3 = 0 ∨ (q % 3 = 2 ∧ e % 2 = 1))) ∨ E ∉ bad := by
  have hres := checkBox_sound (a := a) (b := b) (c := c) (d := d) (q := q) (e := e) (q1 := none)
    (VValid.mk hp1 hl1 hh1 hs1) (VValid.mk hp2 hl2 hh2 hs2)
    (VValid.mk hp3 hl3 hh3 hs3) (VValid.mk hp4 hl4 hh4 hs4)
    hq hq0 trivial he
    (by
      simp only [mkV, vSigma, hp1.ne_one, hp2.ne_one, hp3.ne_one, hp4.ne_one, ↓reduceIte]
      exact sigma_mul_coprime_four hp1 hp2 hp3 hp4 h12 h23 h34)
    (fun u1 u2 u3 u4 hu1 hu2 hu3 hu4 hp1' hp2' hp3' hp4' => by
      rcases hu1 with ⟨h, _⟩ | ⟨_, _, _, hpl1, hsl1, _⟩; · rw [hp1'] at h; exact absurd h hp1.ne_one
      rcases hu2 with ⟨h, _⟩ | ⟨_, _, _, hpl2, hsl2, _⟩; · rw [hp2'] at h; exact absurd h hp2.ne_one
      rcases hu3 with ⟨h, _⟩ | ⟨_, _, _, hpl3, hsl3, _⟩; · rw [hp3'] at h; exact absurd h hp3.ne_one
      rcases hu4 with ⟨h, _⟩ | ⟨_, _, _, hpl4, hsl4, _⟩; · rw [hp4'] at h; exact absurd h hp4.ne_one
      rw [hpl1, hpl2, hpl3, hpl4, hsl1, hsl2, hsl3, hsl4, hp1', hp2', hp3', hp4']
      exact sigma_mul_coprime_four hp1 hp2 hp3 hp4 h12 h23 h34)
    (by
      simp only [mkV]
      exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left
        (((Nat.coprime_primes hp1 hq).mpr (by omega)).pow_left a)
        (((Nat.coprime_primes hp2 hq).mpr (by omega)).pow_left b))
        (((Nat.coprime_primes hp3 hq).mpr (by omega)).pow_left c))
        (((Nat.coprime_primes hp4 hq).mpr (by omega)).pow_left d))
    (by simpa [mkV] using hab) (by simpa [mkV] using hprim) hchk
  simpa [mkV] using hres

lemma rank5_no5_pseudoperfect {p2 p3 p4 q a b c d e : ℕ}
    (hmem19 : ∃ q0 L g P0 bad ds a2 a3 a4 ds2 ds3 ds4,
      (p2, p3, p4, q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4) ∈ basesNo5Data)
    (hq : q.Prime) (hp4q : p4 < q)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hab : (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d * q ^ e).properDivisors, x.Deficient) :
    (3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d * q ^ e).Pseudoperfect := by
  obtain ⟨q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4, hmem⟩ := hmem19
  have h3p : Nat.Prime 3 := by decide
  have hprimes : p2.Prime ∧ p3.Prime ∧ p4.Prime ∧ 7 ≤ p2 ∧ p2 < p3 ∧ p3 < p4 := by
    have : ∀ x ∈ basesNo5Data, x.1.Prime ∧ x.2.1.Prime ∧ x.2.2.1.Prime ∧ 7 ≤ x.1 ∧ x.1 < x.2.1 ∧ x.2.1 < x.2.2.1 := by decide
    exact this _ hmem
  obtain ⟨hp2, hp3, hp4, h7p2, hp23, hp34⟩ := hprimes
  obtain ⟨hcov, hgap, hbad, _, hbig, hL1, hg1⟩ := lift_no5_full hmem ha hb hc hd
  let B := 3 ^ a * p2 ^ b * p3 ^ c * p4 ^ d
  have hBpos : 0 < B := by have := hp2.pos; have := hp3.pos; have := hp4.pos; dsimp [B]; positivity
  have hBgt1 : 1 < B := by
    have : 9 ≤ 3 ^ a := by have := pow_le_pow_right₀ (by decide : 1 ≤ 3) ha; norm_num at this; exact this
    have : 0 < p2 ^ b * p3 ^ c * p4 ^ d := by have := hp2.pos; have := hp3.pos; have := hp4.pos; positivity
    dsimp [B]; nlinarith
  have hcop : B.Coprime q :=
    Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left
      (((Nat.coprime_primes h3p hq).mpr (by omega)).pow_left a)
      (((Nat.coprime_primes hp2 hq).mpr (by omega)).pow_left b))
      (((Nat.coprime_primes hp3 hq).mpr (by omega)).pow_left c))
      (((Nat.coprime_primes hp4 hq).mpr (by omega)).pow_left d)
  have hBdef : sigma 1 B < 2 * B := by
    have hmemB : B ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right B _, by simpa [B] using Nat.mul_lt_mul_of_pos_left (one_lt_pow₀ hq.one_lt (by omega)) hBpos⟩
    exact (defic_iff_nat hBpos).mp (hprim B hmemB)
  have hD2 : 2 ≤ 2 * B - sigma 1 B := dge2_4p_no5 hp2 hp3 hp4 h7p2 hp23 hp34 ha hb hc hd hBdef
  have hq0_le : q0 ≤ q := by
    have hnext : ∀ x ∈ basesNo5Data, ∀ t < x.2.2.2.1, x.2.2.1 < t → ¬ t.Prime := by decide
    by_contra! hlt
    exact hnext _ hmem q hlt hp4q hq
  have hcb_ok : checkBox 45 (mkV 3 2 none 1) (mkV p2 1 none 1) (mkV p3 1 none 1) (mkV p4 1 none 1) q0 none L bad false = true := by
    simp only [basesNo5Data, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact cbNo5_7_11_13_ok
    · exact cbNo5_7_11_17_ok
    · exact cbNo5_7_11_19_ok
    · exact cbNo5_7_11_23_ok
    · exact cbNo5_7_11_29_ok
    · exact cbNo5_7_11_31_ok
    · exact cbNo5_7_11_37_ok
    · exact cbNo5_7_11_41_ok
    · exact cbNo5_7_11_43_ok
    · exact cbNo5_7_11_47_ok
    · exact cbNo5_7_13_17_ok
    · exact cbNo5_7_13_19_ok
    · exact cbNo5_7_13_23_ok
    · exact cbNo5_7_13_29_ok
    · exact cbNo5_7_13_31_ok
    · exact cbNo5_7_17_19_ok
    · exact cbNo5_7_17_23_ok
    · exact cbNo5_7_19_23_ok
    · exact cbNo5_11_13_17_ok
  have hres := run_cb_four (h1 := none) (h2 := none) (h3 := none) (h4 := none) h3p hp2 hp3 hp4 hq (by omega) hp23 hp34 hp4q
    ha trivial (Or.inl rfl) hb trivial (Or.inl rfl) hc trivial (Or.inl rfl) hd trivial (Or.inl rfl)
    hq0_le he hab hprim hcb_ok
  have hEok : L ≤ sigma 1 (B * q ^ e) - 2 * (B * q ^ e) ∨ (sigma 1 (B * q ^ e) - 2 * (B * q ^ e)) ∉ bad := by
    rcases hres with h1 | ⟨hfalse, _⟩ | hnb
    · left; exact h1
    · cases hfalse
    · right; exact hnb
  exact apply_final_prime_or_bad hBgt1 hq hcop (by omega) he hL1 hg1 hab hprim hD2 hbig hcov hgap hbad hEok

/-- Helper: apply a bases3Data entry + p4 to omega = 5, 5 | m. -/
lemma rank5_5_from_base3 {a0 b0 p3 L g P0 bestD relN a b c p4 d q e : ℕ} {bad ds ds3p3 : List ℕ}
    (hmem : (a0, b0, p3, L, g, P0, bad, ds, bestD, ds3p3, relN) ∈ bases3Data)
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hq : q.Prime) (hp3_gt5 : 5 < p3) (hp34 : p3 < p4) (hp4q : p4 < q)
    (ha : a0 ≤ a) (hb : b0 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e)
    (ha_fix : (a0 = 2 ∧ b0 = 1) → a = 2) (hb_fix : b0 = 1 → b = 1)
    (hp4_bound : 2 * p4 + 2 * L ≤ P0 + 1)
    (hab : (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).properDivisors, x.Deficient)
    (hEok : L ≤ sigma 1 (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) - 2 * (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) ∨
            (sigma 1 (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) - 2 * (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e)) ∉ bad) :
    (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Pseudoperfect := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have ha0_ge2 : 2 ≤ a0 := by have : ∀ x ∈ bases3Data, 2 ≤ x.1 := (by decide); exact this _ hmem
  have hb0_ge1 : 1 ≤ b0 := by have : ∀ x ∈ bases3Data, 1 ≤ x.2.1 := (by decide); exact this _ hmem
  have hok := List.all_eq_true.mp bases3Data_ok _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hmeta, _⟩, _⟩, _⟩, _⟩ := hok
  obtain ⟨hL1, rfl, _, hbig0, _, _, _, _⟩ := hmeta
  obtain ⟨hcov, hgap, hbad, hP_ge⟩ := lift_base3_p4 hmem hp3 hp4 hp3_gt5 hp34 ha hb hc hd ha_fix hb_fix hp4_bound
  let B := 3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d
  have hBpos : 0 < B := by have := hp3.pos; have := hp4.pos; dsimp [B]; positivity
  have hBgt1 : 1 < B := by
    have : 9 ≤ 3 ^ a := by have := pow_le_pow_right₀ (by decide : 1 ≤ 3) (show 2 ≤ a by omega); norm_num at this; exact this
    have : 0 < 5 ^ b * p3 ^ c * p4 ^ d := by have := hp3.pos; have := hp4.pos; positivity
    dsimp [B]; nlinarith
  have hcop : B.Coprime q :=
    Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left
      (((Nat.coprime_primes h3p hq).mpr (by omega)).pow_left a)
      (((Nat.coprime_primes h5p hq).mpr (by omega)).pow_left b))
      (((Nat.coprime_primes hp3 hq).mpr (by omega)).pow_left c))
      (((Nat.coprime_primes hp4 hq).mpr (by omega)).pow_left d)
  have hBdef : sigma 1 B < 2 * B := by
    have hmemB : B ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right B _, by simpa [B] using Nat.mul_lt_mul_of_pos_left (one_lt_pow₀ hq.one_lt (by omega)) hBpos⟩
    exact (defic_iff_nat hBpos).mp (hprim B hmemB)
  have hD2 : 2 ≤ 2 * B - sigma 1 B := dge2_4p_5 hp3 hp4 hp3_gt5 hp34 (by omega) (by omega) hc hd hBdef
  exact apply_final_prime_or_bad hBgt1 hq hcop (by omega) he hL1 (by decide) hab hprim hD2
    (le_trans hbig0 hP_ge) hcov hgap hbad hEok

/-- Helper: discharge b even small-excess via runP4s for a given p3. -/
lemma run_cb5_p4 {p3 p4 q a b c d e l1 l3 L : ℕ} {h1 : Option ℕ} {bad : List ℕ} {p4s : List (ℕ × ℕ)}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hq : q.Prime) (hp3_gt5 : 5 < p3) (hp34 : p3 < p4) (hp4q : p4 < q)
    (ha1 : 1 ≤ a) (hl1 : l1 ≤ a) (hh1 : leOpt a h1) (hl2 : 2 ≤ b) (hb_even : b % 2 = 0)
    (hl3_1 : 1 ≤ c) (hl3_2 : p3 % 3 = 2 → 2 ≤ l3 ∧ l3 = 2) (hl3_1' : p3 % 3 ≠ 2 → l3 = 1)
    (hd : 1 ≤ d) (he : 1 ≤ e)
    (hab : (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).properDivisors, x.Deficient)
    (hbad3 : ∀ x ∈ bad, x % 3 ≠ 0)
    (hrun : runP4s p3 l1 2 l3 h1 L bad p4s = true)
    (hmem_p4 : ∃ q0, (p4, q0) ∈ p4s ∧ q0 ≤ q) :
    let m := 3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e
    L ≤ sigma 1 m - 2 * m ∨ (sigma 1 m - 2 * m) ∉ bad := by
  intro m
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have hmpos : 0 < m := by have := hp3.pos; have := hp4.pos; have := hq.pos; dsimp [m]; positivity
  have hab_nat : 2 * m < sigma 1 m := (abund_iff_nat hmpos).mp hab
  have hsm : sigma 1 m = ppSum 3 a * ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e :=
    sigma_mul_coprime_five h3p h5p hp3 hp4 hq (by decide) hp3_gt5 hp34 hp4q
  have h3m : 3 ∣ m := (dvd_pow_self 3 (by omega)).trans
    ((dvd_mul_right _ _).trans ((dvd_mul_right _ _).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))))
  by_cases h3c : p3 % 3 = 2 ∧ c % 2 = 1
  · right; intro hm
    have hcsig : ppSum p3 c ∣ sigma 1 m := by rw [hsm]; exact ⟨ppSum 3 a * ppSum 5 b * ppSum p4 d * ppSum q e, by ring⟩
    exact hbad3 _ hm (three_dvd_excess_of_mod3 h3m ((three_dvd_ppSum_odd hp3.two_le h3c.1 h3c.2).trans hcsig) hab_nat)
  by_cases h3d : p4 % 3 = 2 ∧ d % 2 = 1
  · right; intro hm
    have hdsig : ppSum p4 d ∣ sigma 1 m := by rw [hsm]; exact ⟨ppSum 3 a * ppSum 5 b * ppSum p3 c * ppSum q e, by ring⟩
    exact hbad3 _ hm (three_dvd_excess_of_mod3 h3m ((three_dvd_ppSum_odd hp4.two_le h3d.1 h3d.2).trans hdsig) hab_nat)
  obtain ⟨q0, hmp4, hq0⟩ := hmem_p4
  have hchk := List.all_eq_true.mp hrun (p4, q0) hmp4
  dsimp only at hchk
  have hs3_ok : (if p3 % 3 == 2 then 2 else 1) = 1 ∨
      ((if p3 % 3 == 2 then 2 else 1) = 2 ∧ l3 % 2 = 0 ∧ c % 2 = 0) := by
    by_cases h : p3 % 3 = 2
    · right; have h2 := hl3_2 h; simp [h, h2.2]; omega
    · left; simp [h]
  have hl3_ok : l3 ≤ c := by
    by_cases h : p3 % 3 = 2
    · have h2 := hl3_2 h; omega
    · rw [hl3_1' h]; exact hl3_1
  have hs4_ok : (if p4 % 3 == 2 then 2 else 1) = 1 ∨
      ((if p4 % 3 == 2 then 2 else 1) = 2 ∧ (if p4 % 3 == 2 then 2 else 1) % 2 = 0 ∧ d % 2 = 0) := by
    by_cases h : p4 % 3 = 2
    · right; simp [h]; omega
    · left; simp [h]
  have hl4_ok : (if p4 % 3 == 2 then 2 else 1) ≤ d := by
    by_cases h : p4 % 3 = 2
    · simp [h]; omega
    · simp [h]; exact hd
  have hres := run_cb_four (h2 := none) (h3 := none) (h4 := none) h3p h5p hp3 hp4 hq (by decide) hp3_gt5 hp34 hp4q
    hl1 hh1 (Or.inl rfl) hl2 trivial (Or.inr ⟨rfl, rfl, hb_even⟩)
    hl3_ok trivial hs3_ok hl4_ok trivial hs4_ok hq0 he hab hprim hchk
  rcases hres with h1' | ⟨_, h3E | ⟨hq3, heodd⟩⟩ | hnb
  · left; exact h1'
  · right; intro hm; exact hbad3 _ hm h3E
  · right; intro hm
    have hqsig : ppSum q e ∣ sigma 1 m := by rw [hsm]; exact dvd_mul_left _ _
    exact hbad3 _ hm (three_dvd_excess_of_mod3 h3m ((three_dvd_ppSum_odd hq.two_le hq3 heodd).trans hqsig) hab_nat)
  · right; exact hnb

/-- Upper bound on p4 for 5 | m when sigma(B3) / B3 <= N / D < 2. -/
lemma p4_lt_of_I3_bound {p3 p4 q a b c d e N D B_p4 : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hq : q.Prime) (hp3_gt5 : 5 < p3) (hp34 : p3 < p4) (hp4q : p4 < q)
    (hB_p4 : 2 ≤ B_p4) (hD : 0 < D)
    (hI3 : ppSum 3 a * ppSum 5 b * ppSum p3 c * D ≤ N * (3 ^ a * 5 ^ b * p3 ^ c))
    (hbound : N * B_p4 * (B_p4 + 2) ≤ 2 * D * (B_p4 - 1) * (B_p4 + 1))
    (hab : (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant) :
    p4 < B_p4 := by
  by_contra! hge
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  let m := 3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e
  have hmpos : 0 < m := by have := hp3.pos; have := hp4.pos; have := hq.pos; dsimp [m]; positivity
  have hab_nat := (abund_iff_nat hmpos).mp hab
  rw [sigma_mul_coprime_five h3p h5p hp3 hp4 hq (by decide) hp3_gt5 hp34 hp4q] at hab_nat
  have hq_ge : B_p4 + 2 ≤ q := by
    have hp4_odd : p4 % 2 = 1 := hp4.odd_of_ne_two (by omega) |> fun ⟨k, hk⟩ => by omega
    have hq_odd : q % 2 = 1 := hq.odd_of_ne_two (by omega) |> fun ⟨k, hk⟩ => by omega
    omega
  have lp4 := (ppSum_lt_lim (p := p4) (a := d) hp4.two_le).le
  have lq := (ppSum_lt_lim (p := q) (a := e) hq.two_le).le
  have f1 := frac_anti hB_p4 hge
  have f2 := frac_anti (show 2 ≤ B_p4 + 2 by omega) hq_ge
  have hmul : ppSum 3 a * ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e * (D * (p4 - 1) * (q - 1)) ≤
      N * p4 * q * m := by
    have m1 := Nat.mul_le_mul (Nat.mul_le_mul hI3 lp4) lq
    dsimp [m]; linarith
  have hf12 : p4 * q * ((B_p4 - 1) * (B_p4 + 1)) ≤ B_p4 * (B_p4 + 2) * ((p4 - 1) * (q - 1)) := by
    have hm := Nat.mul_le_mul f1 f2; have heq : B_p4 + 2 - 1 = B_p4 + 1 := (by omega); rw [heq] at hm; linarith
  have hpos_den : 0 < (B_p4 - 1) * (B_p4 + 1) := by have : 0 < B_p4 - 1 := (by omega); positivity
  have h1 : 2 * m * (D * (p4 - 1) * (q - 1)) * ((B_p4 - 1) * (B_p4 + 1)) <
      N * p4 * q * m * ((B_p4 - 1) * (B_p4 + 1)) := by
    have hlt := Nat.mul_lt_mul_of_pos_right hab_nat (by have : 0 < p4 - 1 := (by have := hp4.two_le; omega); have : 0 < q - 1 := (by have := hq.two_le; omega); positivity : 0 < D * (p4 - 1) * (q - 1))
    exact Nat.mul_lt_mul_of_pos_right (lt_of_lt_of_le hlt hmul) hpos_den
  have h2 : N * p4 * q * ((B_p4 - 1) * (B_p4 + 1)) ≤ N * B_p4 * (B_p4 + 2) * ((p4 - 1) * (q - 1)) := by
    have := Nat.mul_le_mul_left N hf12; linarith
  have h3 : N * B_p4 * (B_p4 + 2) * ((p4 - 1) * (q - 1)) ≤ 2 * D * (B_p4 - 1) * (B_p4 + 1) * ((p4 - 1) * (q - 1)) :=
    Nat.mul_le_mul_right _ hbound
  have h4 := Nat.mul_le_mul_right m (le_trans h2 h3)
  linarith


lemma p4_lt_of_I3_bound_gap {p3 p4 q a b c d e N D B_p4 B_q : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hq : q.Prime) (hp3_gt5 : 5 < p3) (hp34 : p3 < p4) (hp4q : p4 < q)
    (hB_p4 : 2 ≤ B_p4) (hB_q : B_p4 < B_q) (hD : 0 < D)
    (hno : (List.range (B_q - B_p4 - 1)).all (fun i => isComp (B_p4 + 1 + i)) = true)
    (hI3 : ppSum 3 a * ppSum 5 b * ppSum p3 c * D ≤ N * (3 ^ a * 5 ^ b * p3 ^ c))
    (hbound : N * B_p4 * B_q ≤ 2 * D * (B_p4 - 1) * (B_q - 1))
    (hab : (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant) :
    p4 < B_p4 := by
  by_contra! hge
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  let m := 3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e
  have hmpos : 0 < m := by have := hp3.pos; have := hp4.pos; have := hq.pos; dsimp [m]; positivity
  have hab_nat : 2 * m < ppSum 3 a * ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e := by
    rw [← sigma_mul_coprime_five h3p h5p hp3 hp4 hq (by decide) hp3_gt5 hp34 hp4q]
    exact (abund_iff_nat hmpos).mp hab
  have hq_ge : B_q ≤ q := by
    by_contra! hqlt
    exact no_prime_between B_p4 B_q q hqlt (by omega) hno hq
  have lp4 := (ppSum_lt_lim (p := p4) (a := d) hp4.two_le).le
  have lq := (ppSum_lt_lim (p := q) (a := e) hq.two_le).le
  have f1 := frac_anti hB_p4 hge
  have f2 := frac_anti (show 2 ≤ B_q by omega) hq_ge
  have hmul : ppSum 3 a * ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e * (D * (p4 - 1) * (q - 1)) ≤
      N * p4 * q * m := by
    have m1 := Nat.mul_le_mul (Nat.mul_le_mul hI3 lp4) lq
    dsimp [m]; linarith
  have hf12 : p4 * q * ((B_p4 - 1) * (B_q - 1)) ≤ B_p4 * B_q * ((p4 - 1) * (q - 1)) := by
    have hm := Nat.mul_le_mul f1 f2; linarith
  have hpos_den : 0 < (B_p4 - 1) * (B_q - 1) := by
    have : 0 < B_p4 - 1 := (by omega); have : 0 < B_q - 1 := (by omega); positivity
  have h1 : 2 * m * (D * (p4 - 1) * (q - 1)) * ((B_p4 - 1) * (B_q - 1)) <
      N * p4 * q * m * ((B_p4 - 1) * (B_q - 1)) := by
    have hlt := Nat.mul_lt_mul_of_pos_right hab_nat (by have : 0 < p4 - 1 := (by have := hp4.two_le; omega); have : 0 < q - 1 := (by have := hq.two_le; omega); positivity : 0 < D * (p4 - 1) * (q - 1))
    exact Nat.mul_lt_mul_of_pos_right (lt_of_lt_of_le hlt hmul) hpos_den
  have h2 : N * p4 * q * ((B_p4 - 1) * (B_q - 1)) ≤ N * B_p4 * B_q * ((p4 - 1) * (q - 1)) := by
    have := Nat.mul_le_mul_left N hf12; linarith
  have h3 : N * B_p4 * B_q * ((p4 - 1) * (q - 1)) ≤ 2 * D * (B_p4 - 1) * (B_q - 1) * ((p4 - 1) * (q - 1)) :=
    Nat.mul_le_mul_right _ hbound
  have h4 := Nat.mul_le_mul_right m (le_trans h2 h3)
  linarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3200000 in
lemma rank5_5_pseudoperfect {p3 p4 q a b c d e : ℕ}
    (hp3_mem : p3 ∈ ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41} : Finset ℕ))
    (hp4 : p4.Prime) (hq : q.Prime) (hp34 : p3 < p4) (hp4q : p4 < q)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hab : (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).properDivisors, x.Deficient) :
    (3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Pseudoperfect := by
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have hp3 : p3.Prime := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp3_mem
    rcases hp3_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hp3_gt5 : 5 < p3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp3_mem
    rcases hp3_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  let m := 3 ^ a * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e
  have hmpos : 0 < m := by have := hp3.pos; have := hp4.pos; have := hq.pos; dsimp [m]; positivity
  have hab_nat : 2 * m < sigma 1 m := (abund_iff_nat hmpos).mp hab
  have hsm : sigma 1 m = ppSum 3 a * ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e :=
    sigma_mul_coprime_five h3p h5p hp3 hp4 hq (by decide) hp3_gt5 hp34 hp4q
  have h3m : 3 ∣ m := (dvd_pow_self 3 (by omega)).trans
    ((dvd_mul_right _ _).trans ((dvd_mul_right _ _).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))))
  have h5sig : ppSum 5 b ∣ sigma 1 m := by rw [hsm]; exact ⟨ppSum 3 a * ppSum p3 c * ppSum p4 d * ppSum q e, by ring⟩
  have hB3def : sigma 1 (3 ^ a * 5 ^ b * p3 ^ c) < 2 * (3 ^ a * 5 ^ b * p3 ^ c) := by
    have hmemB3 : 3 ^ a * 5 ^ b * p3 ^ c ∈ m.properDivisors := Nat.mem_properDivisors.mpr
      ⟨(dvd_mul_right _ _).trans (dvd_mul_right _ _), by
        dsimp [m]
        have h1 : 1 < p4 ^ d * q ^ e := by
          have : 1 < p4 ^ d := one_lt_pow₀ hp4.one_lt (by omega)
          have : 1 ≤ q ^ e := Nat.one_le_pow _ _ hq.pos
          nlinarith
        have h2 : 0 < 3 ^ a * 5 ^ b * p3 ^ c := by have := hp3.pos; positivity
        have : 3 ^ a * 5 ^ b * p3 ^ c * 1 < 3 ^ a * 5 ^ b * p3 ^ c * (p4 ^ d * q ^ e) := Nat.mul_lt_mul_of_pos_left h1 h2
        linarith⟩
    exact (defic_iff_nat (by have := hp3.pos; positivity)).mp (hprim _ hmemB3)
  -- Dispatch by p3!
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp3_mem
  rcases hp3_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- p3 = 7: (a, b, c) MUST be (2, 1, 1), and p4 <= 199!
    have h211 : a = 2 ∧ b = 1 ∧ c = 1 := by
      have ha2 : a = 2 := by
        by_contra hne; have ha3 : 3 ≤ a := by omega
        have hm := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_mono_exp (p := 3) (by decide) ha3)
          (ppSum_mono_exp (p := 5) (by decide) hb)) (ppSum_mono_exp (p := 7) (by decide) hc)
        have hval : ppSum 3 3 = 40 ∧ ppSum 5 1 = 6 ∧ ppSum 7 1 = 8 := by decide
        rw [hval.1, hval.2.1, hval.2.2] at hm
        rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide)] at hB3def
        have : 0 < 3 ^ a * 5 ^ b * 7 ^ c := (by positivity); nlinarith
      have hb1 : b = 1 := by
        by_contra hne; have hb2 : 2 ≤ b := by omega
        have hm := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_mono_exp (p := 3) (by decide) ha)
          (ppSum_mono_exp (p := 5) (by decide) hb2)) (ppSum_mono_exp (p := 7) (by decide) hc)
        have hval : ppSum 3 2 = 13 ∧ ppSum 5 2 = 31 ∧ ppSum 7 1 = 8 := by decide
        rw [hval.1, hval.2.1, hval.2.2] at hm
        rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide)] at hB3def
        have : 0 < 3 ^ a * 5 ^ b * 7 ^ c := (by positivity); nlinarith
      have hc1 : c = 1 := by
        by_contra hne; have hc2 : 2 ≤ c := by omega
        have hm := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_mono_exp (p := 3) (by decide) ha)
          (ppSum_mono_exp (p := 5) (by decide) hb)) (ppSum_mono_exp (p := 7) (by decide) hc2)
        have hval : ppSum 3 2 = 13 ∧ ppSum 5 1 = 6 ∧ ppSum 7 2 = 57 := by decide
        rw [hval.1, hval.2.1, hval.2.2] at hm
        rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide)] at hB3def
        have : 0 < 3 ^ a * 5 ^ b * 7 ^ c := (by positivity); nlinarith
      exact ⟨ha2, hb1, hc1⟩
    obtain ⟨rfl, rfl, rfl⟩ := h211
    have hp4_lt211 : p4 < 211 := by
      -- Note: 211 is followed by 223, wait (208/105)*(211/210)*(213/212) > 2, so use 211 -> q >= 223!
      by_contra! hge
      by_cases h211eq : p4 = 211
      · subst h211eq
        have hq223 : 223 ≤ q := by by_contra! hlt; exact no_prime_between 211 223 q hlt hp4q (by decide) hq
        have lp4 := (ppSum_lt_lim (p := 211) (a := d) (by decide)).le
        have lq := (ppSum_lt_lim (p := q) (a := e) hq.two_le).le
        have hf := frac_anti (by decide : 2 ≤ 223) hq223
        have h624 : ppSum 3 2 * ppSum 5 1 * ppSum 7 1 = 624 := by decide
        rw [hsm, h624] at hab_nat
        have h1 : 624 * ppSum 211 d * ppSum q e * (210 * (q - 1)) ≤ 624 * 211 * q * (211 ^ d * q ^ e) := by
          have hm := Nat.mul_le_mul_left 624 (Nat.mul_le_mul lp4 lq); linarith
        have h2 := Nat.mul_le_mul_right (211 ^ d * q ^ e) (Nat.mul_le_mul_left (624 * 211) hf)
        have h3 := Nat.mul_le_mul_right 222 h1
        have h4 := Nat.mul_lt_mul_of_pos_right hab_nat (by have : 0 < q - 1 := (by omega); positivity : 0 < 210 * (q - 1) * 222)
        have h5 : 624 * 211 * 223 * (q - 1) * (211 ^ d * q ^ e) < 2 * (3 ^ 2 * 5 ^ 1 * 7 ^ 1 * 211 ^ d * q ^ e) * (210 * (q - 1) * 222) := by
          have hpos : 0 < (q - 1) * (211 ^ d * q ^ e) := by have : 0 < q - 1 := (by omega); have := hq.pos; positivity
          nlinarith
        dsimp [m] at h4; linarith
      · have h212 : 213 ≤ p4 := by
          have : p4 % 2 = 1 := hp4.odd_of_ne_two (by omega) |> fun ⟨k, hk⟩ => by omega
          omega
        exact absurd (p4_lt_of_I3_bound (N := 624) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 213) (by decide : 0 < 315)
          (by decide) (by decide) hab) (by omega)
    by_cases hp4_152 : p4 ≤ 152
    · have hmem0 := find_bases3 2 1 7 3 2 309 [2] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      exact rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q le_rfl le_rfl le_rfl hd he (fun _ => rfl) (fun _ => rfl)
        (by omega) hab hprim (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
    · have hmem315 : ∃ L g P0 bad ds, (p4, L, g, P0, bad, ds) ∈ bases315Data :=
        find_bases315 211 152 p4 hp4_lt211 (by omega) hp4 (by decide)
      obtain ⟨L, g, P0, bad, ds, hm315⟩ := hmem315
      obtain ⟨hcov, hgap, hbad, hP_ge⟩ := lift_315_p4 hm315 hp4 hd
      have hok315 := List.all_eq_true.mp bases315Data_ok _ hm315
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok315
      obtain ⟨⟨rfl, rfl, _, hbig0, rfl⟩, _⟩ := hok315
      let B := 3 ^ 2 * 5 ^ 1 * 7 ^ 1 * p4 ^ d
      have hBeq : B = 315 * p4 ^ d := rfl
      have hBpos : 0 < B := by have := hp4.pos; dsimp [B]; positivity
      have hBdef : sigma 1 B < 2 * B := by
        have hmemB : B ∈ m.properDivisors := Nat.mem_properDivisors.mpr
          ⟨dvd_mul_right B _, by simpa [m, B] using Nat.mul_lt_mul_of_pos_left (one_lt_pow₀ hq.one_lt (by omega)) hBpos⟩
        exact (defic_iff_nat hBpos).mp (hprim B hmemB)
      have hD2 : 2 ≤ 2 * B - sigma 1 B := dge2_4p_5 (by decide) hp4 (by decide) hp34 le_rfl le_rfl le_rfl hd hBdef
      have hcop : B.Coprime q :=
        Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left
          (((Nat.coprime_primes h3p hq).mpr (by omega)).pow_left 2)
          (((Nat.coprime_primes h5p hq).mpr (by omega)).pow_left 1))
          (((Nat.coprime_primes (by decide) hq).mpr (by omega)).pow_left 1))
          (((Nat.coprime_primes hp4 hq).mpr (by omega)).pow_left d)
      apply apply_final_prime_or_bad (B := B) (L := 3) (g := 2) (bad := [2])
        (by dsimp [B]; have := hp4.pos; nlinarith [pow_pos hp4.pos d]) hq hcop (by omega) he (by decide) (by decide)
        hab hprim hD2 (by rw [hBeq]; exact le_trans hbig0 hP_ge)
        (by rw [hBeq]; exact hcov) (by rw [hBeq]; exact hgap) (by rw [hBeq]; exact hbad)
      right
      have h3E := three_dvd_E_of_five_odd h3m h5sig rfl hab_nat
      intro hmem2; simp only [List.mem_singleton] at hmem2; dsimp only [B, m] at hmem2 h3E; rw [hmem2] at h3E; omega
  · -- p3 = 11
    by_cases hb1 : b = 1
    · subst hb1
      by_cases ha2 : a = 2
      · subst ha2
        have hp4_lt43 : p4 < 43 := p4_lt_of_I3_bound (N := 13 * 6 * 11) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 43) (by decide : 0 < 9 * 5 * 10)
          (by rw [(by decide : ppSum 3 2 = 13), (by decide : ppSum 5 1 = 6)]
              have := (ppSum_lt_lim (p := 11) (a := c) (by decide)).le; linarith)
          (by decide) hab
        have hmem0 := find_bases3 2 1 11 23 2 441 [2, 7, 22] (by decide)
        obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
        exact rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q le_rfl le_rfl hc hd he (fun _ => rfl) (fun _ => rfl)
          (by omega) hab hprim (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
      · have hp4_lt200 : p4 < 200 := p4_lt_of_I3_bound (N := 3 * 6 * 11) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 200) (by decide : 0 < 2 * 5 * 10)
          (by rw [(by decide : ppSum 5 1 = 6)]
              have := Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le (ppSum_lt_lim (p := 11) (a := c) (by decide)).le; linarith)
          (by decide) hab
        have hmem0 := find_bases3 3 1 11 23 2 1395 [2, 7, 22] (by decide)
        obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
        exact rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q (by omega) le_rfl hc hd he (by omega) (fun _ => rfl)
          (by omega) hab hprim (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
    · have hb2 : 2 ≤ b := by omega
      have ha2 : a = 2 := by
        by_contra hne; have ha3 : 3 ≤ a := by omega
        have hm1 := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_mono_exp (p := 3) (by decide) ha3)
          (ppSum_mono_exp (p := 5) (by decide) hb2)) (ppSum_mono_exp (p := 11) (by decide) hc)
        have hval : ppSum 3 3 = 40 ∧ ppSum 5 2 = 31 ∧ ppSum 11 1 = 12 := by decide
        rw [hval.1, hval.2.1, hval.2.2] at hm1
        rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide)] at hB3def
        have : 0 < 3 ^ a * 5 ^ b * 11 ^ c := (by positivity); nlinarith
      have hp4_lt283 : p4 < 283 := p4_lt_of_I3_bound_gap (N := 13 * 5 * 11) (B_q := 293) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 283) (by decide) (by decide : 0 < 9 * 4 * 10) (by decide)
        (by rw [ha2, (by decide : ppSum 3 2 = 13)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 5) (a := b) (by decide)).le (ppSum_lt_lim (p := 11) (a := c) (by decide)).le; linarith)
        (by decide) hab
      have hmem0 := find_bases3 2 2 11 23 2 2361 [2, 7, 22] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      apply rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha hb2 hc hd he (by omega) (by omega) (by omega) hab hprim
      by_cases hbodd : b % 2 = 1
      · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
      · have hmp4 : ∃ q0, (p4, q0) ∈ cb5_11_all ∧ q0 ≤ q := by
          obtain ⟨q0, hq0m, hq0n⟩ := find_cb5 cb5_11_all 283 11 p4 hp4_lt283 hp34 hp4 (by decide)
          exact ⟨q0, hq0m, by by_contra! hlt; exact hq0n q hlt hp4q hq⟩
        exact run_cb5_p4 (by decide) hp4 hq (by decide) hp34 hp4q (by omega) ha (by simp [leOpt, ha2]) hb2 (by omega)
          hc (fun _ => ⟨le_rfl, rfl⟩) (by decide) hd he hab hprim (by decide) cb5_11_all_ok hmp4
  · -- p3 = 13
    by_cases hb1 : b = 1
    · subst hb1
      by_cases ha2 : a = 2
      · subst ha2
        have hp4_lt31 : p4 < 31 := p4_lt_of_I3_bound_gap (N := 13 * 6 * 13) (B_q := 37) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 31) (by decide) (by decide : 0 < 9 * 5 * 12) (by decide)
          (by rw [(by decide : ppSum 3 2 = 13), (by decide : ppSum 5 1 = 6)]
              have := (ppSum_lt_lim (p := 13) (a := c) (by decide)).le; linarith)
          (by decide) hab
        have hmem0 := find_bases3 2 1 13 36 2 507 [2, 7, 11, 35] (by decide)
        obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
        exact rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q le_rfl le_rfl hc hd he (fun _ => rfl) (fun _ => rfl)
          (by omega) hab hprim (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
      · have hp4_lt79 : p4 < 79 := p4_lt_of_I3_bound (N := 3 * 6 * 13) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 79) (by decide : 0 < 2 * 5 * 12)
          (by rw [(by decide : ppSum 5 1 = 6)]
              have := Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le (ppSum_lt_lim (p := 13) (a := c) (by decide)).le; linarith)
          (by decide) hab
        have hmem0 := find_bases3 3 1 13 12 2 1605 [2, 7, 11] (by decide)
        obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
        exact rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q (by omega) le_rfl hc hd he (by omega) (fun _ => rfl)
          (by omega) hab hprim (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
    · have hb2 : 2 ≤ b := by omega
      have ha4 : a ≤ 4 := by
        by_contra! h5
        have hm1 := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_mono_exp (p := 3) (by decide) h5)
          (ppSum_mono_exp (p := 5) (by decide) hb2)) (ppSum_mono_exp (p := 13) (by decide) hc)
        have hval : ppSum 3 5 = 364 ∧ ppSum 5 2 = 31 ∧ ppSum 13 1 = 14 := by decide
        rw [hval.1, hval.2.1, hval.2.2] at hm1
        rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide)] at hB3def
        have : 0 < 3 ^ a * 5 ^ b * 13 ^ c := (by positivity); nlinarith
      -- I3 <= 52514 / 26325 => p4 <= 769 (< 773)
      have hI3_13 : ppSum 3 a * ppSum 5 b * ppSum 13 c * 26325 ≤ 52514 * (3 ^ a * 5 ^ b * 13 ^ c) := by
        have : a = 2 ∨ a = 3 ∨ a = 4 := by omega
        rcases this with rfl | rfl | rfl
        · rw [(by decide : ppSum 3 2 = 13)]
          have hm := Nat.mul_le_mul (ppSum_lt_lim (p := 5) (a := b) (by decide)).le (ppSum_lt_lim (p := 13) (a := c) (by decide)).le
          linarith
        · by_cases hb2eq : b = 2
          · subst hb2eq
            rw [(by decide : ppSum 3 3 = 40), (by decide : ppSum 5 2 = 31)]
            have hm := (ppSum_lt_lim (p := 13) (a := c) (by decide)).le; linarith
          · have hb3 : 3 ≤ b := by omega
            have hc1 : c = 1 := by
              by_contra hne; have hc2 : 2 ≤ c := by omega
              have hm := Nat.mul_le_mul (ppSum_mono_exp (p := 5) (by decide) hb3) (ppSum_mono_exp (p := 13) (by decide) hc2)
              have hval : ppSum 3 3 = 40 ∧ ppSum 5 3 = 156 ∧ ppSum 13 2 = 183 := by decide
              rw [hval.2.1, hval.2.2] at hm
              rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide), hval.1] at hB3def
              have : 0 < 3 ^ 3 * 5 ^ b * 13 ^ c := (by positivity); nlinarith
            subst hc1
            rw [(by decide : ppSum 3 3 = 40), (by decide : ppSum 13 1 = 14)]
            have hm := (ppSum_lt_lim (p := 5) (a := b) (by decide)).le; linarith
        · have hb2eq : b = 2 := by
            by_contra hne; have hb3 : 3 ≤ b := by omega
            have hm := Nat.mul_le_mul (ppSum_mono_exp (p := 5) (by decide) hb3) (ppSum_mono_exp (p := 13) (by decide) hc)
            have hval : ppSum 3 4 = 121 ∧ ppSum 5 3 = 156 ∧ ppSum 13 1 = 14 := by decide
            rw [hval.2.1, hval.2.2] at hm
            rw [sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide), hval.1] at hB3def
            have : 0 < 3 ^ 4 * 5 ^ b * 13 ^ c := (by positivity); nlinarith
          have hc1 : c = 1 := by
            by_contra hne; have hc2 : 2 ≤ c := by omega
            have hm := ppSum_mono_exp (p := 13) (by decide) hc2
            have hval : ppSum 3 4 = 121 ∧ ppSum 5 2 = 31 ∧ ppSum 13 2 = 183 := by decide
            rw [hval.2.2] at hm
            rw [hb2eq, sigma_mul_coprime_three h3p h5p (by decide) (by decide) (by decide), hval.1, hval.2.1] at hB3def
            have : 0 < 3 ^ 4 * 5 ^ 2 * 13 ^ c := (by positivity); nlinarith
          subst hb2eq; subst hc1; decide
      have hp4_lt773 : p4 < 773 := p4_lt_of_I3_bound (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 773) (by decide : 0 < 26325)
        hI3_13 (by decide) hab
      have hmem0 := find_bases3 2 2 13 12 2 2717 [2, 7, 11] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      apply rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha hb2 hc hd he (by omega) (by omega) (by omega) hab hprim
      by_cases hbodd : b % 2 = 1
      · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
      · have hmp4 : ∃ q0, (p4, q0) ∈ cb5_13_all ∧ q0 ≤ q := by
          obtain ⟨q0, hq0m, hq0n⟩ := find_cb5 cb5_13_all 773 13 p4 hp4_lt773 hp34 hp4 (by decide)
          exact ⟨q0, hq0m, by by_contra! hlt; exact hq0n q hlt hp4q hq⟩
        exact run_cb5_p4 (h1 := some 4) (by decide) hp4 hq (by decide) hp34 hp4q (by omega) ha ha4 hb2 (by omega)
          hc (by decide) (fun _ => rfl) hd he hab hprim (by decide) cb5_13_all_ok hmp4
  · -- p3 = 17
    by_cases hb1 : b = 1
    · subst hb1
      by_cases ha2 : a = 2
      · subst ha2
        have hp4_19 : p4 = 19 := by
          have hlt23 : p4 < 23 := p4_lt_of_I3_bound_gap (N := 13 * 6 * 17) (B_q := 29) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 23) (by decide) (by decide : 0 < 9 * 5 * 16) (by decide)
            (by rw [(by decide : ppSum 3 2 = 13), (by decide : ppSum 5 1 = 6)]
                have := (ppSum_lt_lim (p := 17) (a := c) (by decide)).le; linarith)
            (by decide) hab
          exact (by decide : ∀ t < 23, 17 < t → t.Prime → t = 19) p4 hlt23 hp34 hp4
        subst hp4_19
        obtain ⟨hcov, hgap, hbad, hP_ge⟩ := lift_45_17_19 hc hd
        let B := 3 ^ 2 * 5 ^ 1 * 17 ^ c * 19 ^ d
        have hBeq : B = 45 * 17 ^ c * 19 ^ d := rfl
        have hBpos : 0 < B := by dsimp [B]; positivity
        have hBdef : sigma 1 B < 2 * B := by
          have hmemB : B ∈ m.properDivisors := Nat.mem_properDivisors.mpr
            ⟨dvd_mul_right B _, by simpa [m, B] using Nat.mul_lt_mul_of_pos_left (one_lt_pow₀ hq.one_lt (by omega)) hBpos⟩
          exact (defic_iff_nat hBpos).mp (hprim B hmemB)
        have hD2 : 2 ≤ 2 * B - sigma 1 B := dge2_4p_5 (by decide) (by decide) (by decide) (by decide) le_rfl le_rfl hc hd hBdef
        have hcop : B.Coprime q :=
          Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left
            (((Nat.coprime_primes h3p hq).mpr (by omega)).pow_left 2)
            (((Nat.coprime_primes h5p hq).mpr (by omega)).pow_left 1))
            (((Nat.coprime_primes (by decide) hq).mpr (by omega)).pow_left c))
            (((Nat.coprime_primes (by decide) hq).mpr (by omega)).pow_left d)
        apply apply_final_prime_or_bad (B := B) (L := 12) (g := 2) (bad := [2, 7, 11])
          (by dsimp [B]; nlinarith [pow_pos (by decide : 0 < 17) c, pow_pos (by decide : 0 < 19) d])
          hq hcop (by omega) he (by decide) (by decide) hab hprim hD2
          (by rw [hBeq]; omega) (by rw [hBeq]; exact hcov) (by rw [hBeq]; exact hgap) (by rw [hBeq]; exact hbad)
        right
        have h3E := three_dvd_E_of_five_odd h3m h5sig rfl hab_nat
        intro hmem'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
        dsimp only [B, m] at hmem' h3E
        rcases hmem' with h | h | h <;> (rw [h] at h3E; omega)
      · have hp4_lt47 : p4 < 47 := p4_lt_of_I3_bound (N := 3 * 6 * 17) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 47) (by decide : 0 < 2 * 5 * 16)
          (by rw [(by decide : ppSum 5 1 = 6)]
              have := Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le (ppSum_lt_lim (p := 17) (a := c) (by decide)).le; linarith)
          (by decide) hab
        have hmem0 := find_bases3 3 1 17 12 2 2025 [2, 7, 11] (by decide)
        obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
        exact rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q (by omega) le_rfl hc hd he (by omega) (fun _ => rfl)
          (by omega) hab hprim (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
    · have hb2 : 2 ≤ b := by omega
      have hp4_lt509 : p4 < 509 := p4_lt_of_I3_bound_gap (N := 3 * 5 * 17) (B_q := 521) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 509) (by decide) (by decide : 0 < 2 * 4 * 16) (by decide)
        (by have := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le
              (ppSum_lt_lim (p := 5) (a := b) (by decide)).le) (ppSum_lt_lim (p := 17) (a := c) (by decide)).le; linarith)
        (by decide) hab
      have hmem0 := find_bases3 2 2 17 12 2 3429 [2, 7, 11] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      apply rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha hb2 hc hd he (by omega) (by omega) (by omega) hab hprim
      by_cases hbodd : b % 2 = 1
      · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
      · have hmp4 : ∃ q0, (p4, q0) ∈ cb5_17_all ∧ q0 ≤ q := by
          obtain ⟨q0, hq0m, hq0n⟩ := find_cb5 cb5_17_all 509 17 p4 hp4_lt509 hp34 hp4 (by decide)
          exact ⟨q0, hq0m, by by_contra! hlt; exact hq0n q hlt hp4q hq⟩
        exact run_cb5_p4 (h1 := none) (by decide) hp4 hq (by decide) hp34 hp4q (by omega) ha trivial hb2 (by omega)
          hc (fun _ => ⟨le_rfl, rfl⟩) (by decide) hd he hab hprim (by decide) cb5_17_all_ok hmp4
  · -- p3 = 19
    by_cases hb1 : b = 1
    · subst hb1
      have ha3 : 3 ≤ a := by
        by_contra! hlt; have ha2 : a = 2 := (by omega); subst ha2
        have h23 : 23 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 23, 19 < t → ¬ t.Prime) p4 h hp34 hp4
        exact absurd (p4_lt_of_I3_bound (N := 13 * 6 * 19) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 23) (by decide : 0 < 9 * 5 * 18)
          (by rw [(by decide : ppSum 3 2 = 13), (by decide : ppSum 5 1 = 6)]
              have := (ppSum_lt_lim (p := 19) (a := c) (by decide)).le; linarith)
          (by decide) hab) (by omega)
      have hp4_lt41 : p4 < 41 := p4_lt_of_I3_bound (N := 3 * 6 * 19) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 41) (by decide : 0 < 2 * 5 * 18)
        (by rw [(by decide : ppSum 5 1 = 6)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le (ppSum_lt_lim (p := 19) (a := c) (by decide)).le; linarith)
        (by decide) hab
      have hmem0 := find_bases3 3 1 19 27 2 2235 [2, 7, 11, 26] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      exact rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha3 le_rfl hc hd he (by omega) (fun _ => rfl)
        (by omega) hab hprim (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
    · have hb2 : 2 ≤ b := by omega
      have hp4_lt191 : p4 < 191 := p4_lt_of_I3_bound (N := 3 * 5 * 19) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 191) (by decide : 0 < 2 * 4 * 18)
        (by have := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le
              (ppSum_lt_lim (p := 5) (a := b) (by decide)).le) (ppSum_lt_lim (p := 19) (a := c) (by decide)).le; linarith)
        (by decide) hab
      have hmem0 := find_bases3 2 2 19 12 2 3785 [2, 7, 11] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      apply rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha hb2 hc hd he (by omega) (by omega) (by omega) hab hprim
      by_cases hbodd : b % 2 = 1
      · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
      · have hmp4 : ∃ q0, (p4, q0) ∈ cb5_19_all ∧ q0 ≤ q := by
          obtain ⟨q0, hq0m, hq0n⟩ := find_cb5 cb5_19_all 191 19 p4 hp4_lt191 hp34 hp4 (by decide)
          exact ⟨q0, hq0m, by by_contra! hlt; exact hq0n q hlt hp4q hq⟩
        exact run_cb5_p4 (h1 := none) (by decide) hp4 hq (by decide) hp34 hp4q (by omega) ha trivial hb2 (by omega)
          hc (by decide) (fun _ => rfl) hd he hab hprim (by decide) cb5_19_all_ok hmp4
  · -- p3 = 23
    by_cases hb1 : b = 1
    · subst hb1
      have ha3 : 3 ≤ a := by
        by_contra! hlt; have ha2 : a = 2 := (by omega); subst ha2
        have h29 : 29 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 29, 23 < t → ¬ t.Prime) p4 h hp34 hp4
        exact absurd (p4_lt_of_I3_bound (N := 13 * 6 * 23) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 29) (by decide : 0 < 9 * 5 * 22)
          (by rw [(by decide : ppSum 3 2 = 13), (by decide : ppSum 5 1 = 6)]
              have := (ppSum_lt_lim (p := 23) (a := c) (by decide)).le; linarith)
          (by decide) hab) (by omega)
      have hp4_lt31 : p4 < 31 := p4_lt_of_I3_bound_gap (N := 3 * 6 * 23) (B_q := 37) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 31) (by decide) (by decide : 0 < 2 * 5 * 22) (by decide)
        (by rw [(by decide : ppSum 5 1 = 6)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le (ppSum_lt_lim (p := 23) (a := c) (by decide)).le; linarith)
        (by decide) hab
      have hmem0 := find_bases3 3 1 23 35 2 2655 [2, 7, 11, 22, 34] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      exact rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha3 le_rfl hc hd he (by omega) (fun _ => rfl)
        (by omega) hab hprim (Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig rfl hab_nat)))
    · have hb2 : 2 ≤ b := by omega
      have hp4_lt101 : p4 < 101 := p4_lt_of_I3_bound (N := 3 * 5 * 23) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 101) (by decide : 0 < 2 * 4 * 22)
        (by have := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le
              (ppSum_lt_lim (p := 5) (a := b) (by decide)).le) (ppSum_lt_lim (p := 23) (a := c) (by decide)).le; linarith)
        (by decide) hab
      have hmem0 := find_bases3 2 2 23 23 2 4497 [2, 7, 11, 22] (by decide)
      obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
      apply rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha hb2 hc hd he (by omega) (by omega) (by omega) hab hprim
      by_cases hbodd : b % 2 = 1
      · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
      · have hmp4 : ∃ q0, (p4, q0) ∈ cb5_23_all ∧ q0 ≤ q := by
          obtain ⟨q0, hq0m, hq0n⟩ := find_cb5 cb5_23_all 101 23 p4 hp4_lt101 hp34 hp4 (by decide)
          exact ⟨q0, hq0m, by by_contra! hlt; exact hq0n q hlt hp4q hq⟩
        exact run_cb5_p4 (h1 := none) (by decide) hp4 hq (by decide) hp34 hp4q (by omega) ha trivial hb2 (by omega)
          hc (fun _ => ⟨le_rfl, rfl⟩) (by decide) hd he hab hprim (by decide) cb5_23_all_ok hmp4
  · -- p3 = 29: a >= 3 AND b >= 2, p4 <= 61 (< 67)
    have h31 : 31 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 31, 29 < t → ¬ t.Prime) p4 h hp34 hp4
    have ha3 : 3 ≤ a := by
      by_contra! hlt; have ha2 : a = 2 := (by omega); subst ha2
      exact absurd (p4_lt_of_I3_bound (N := 13 * 5 * 29) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 31) (by decide : 0 < 9 * 4 * 28)
        (by rw [(by decide : ppSum 3 2 = 13)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 5) (a := b) (by decide)).le (ppSum_lt_lim (p := 29) (a := c) (by decide)).le; linarith)
        (by decide) hab) (by omega)
    have hb2 : 2 ≤ b := by
      by_contra! hlt; have hb1 : b = 1 := (by omega); subst hb1
      exact absurd (p4_lt_of_I3_bound (N := 3 * 6 * 29) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 31) (by decide : 0 < 2 * 5 * 28)
        (by rw [(by decide : ppSum 5 1 = 6)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le (ppSum_lt_lim (p := 29) (a := c) (by decide)).le; linarith)
        (by decide) hab) (by omega)
    have hp4_lt67 : p4 < 67 := p4_lt_of_I3_bound_gap (N := 3 * 5 * 29) (B_q := 71) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 67) (by decide) (by decide : 0 < 2 * 4 * 28) (by decide)
      (by have := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le
            (ppSum_lt_lim (p := 5) (a := b) (by decide)).le) (ppSum_lt_lim (p := 29) (a := c) (by decide)).le; linarith)
      (by decide) hab
    have hmem0 := find_bases3 3 2 29 23 2 17625 [2, 7, 11, 22] (by decide)
    obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
    apply rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha3 hb2 hc hd he (by omega) (by omega) (by omega) hab hprim
    by_cases hbodd : b % 2 = 1
    · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
    · have hmp4 : ∃ q0, (p4, q0) ∈ cb5_29_all ∧ q0 ≤ q := by
        obtain ⟨q0, hq0m, hq0n⟩ := find_cb5 cb5_29_all 67 29 p4 hp4_lt67 hp34 hp4 (by decide)
        exact ⟨q0, hq0m, by by_contra! hlt; exact hq0n q hlt hp4q hq⟩
      exact run_cb5_p4 (h1 := none) (by decide) hp4 hq (by decide) hp34 hp4q (by omega) ha3 trivial hb2 (by omega)
        hc (fun _ => ⟨le_rfl, rfl⟩) (by decide) hd he hab hprim (by decide) cb5_29_all_ok hmp4
  · -- p3 = 31: a >= 3 AND b >= 2, p4 <= 59 (< 61)
    have h37 : 37 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 37, 31 < t → ¬ t.Prime) p4 h hp34 hp4
    have ha3 : 3 ≤ a := by
      by_contra! hlt; have ha2 : a = 2 := (by omega); subst ha2
      exact absurd (p4_lt_of_I3_bound (N := 13 * 5 * 31) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 37) (by decide : 0 < 9 * 4 * 30)
        (by rw [(by decide : ppSum 3 2 = 13)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 5) (a := b) (by decide)).le (ppSum_lt_lim (p := 31) (a := c) (by decide)).le; linarith)
        (by decide) hab) (by omega)
    have hb2 : 2 ≤ b := by
      by_contra! hlt; have hb1 : b = 1 := (by omega); subst hb1
      exact absurd (p4_lt_of_I3_bound (N := 3 * 6 * 31) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 37) (by decide : 0 < 2 * 5 * 30)
        (by rw [(by decide : ppSum 5 1 = 6)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le (ppSum_lt_lim (p := 31) (a := c) (by decide)).le; linarith)
        (by decide) hab) (by omega)
    have hp4_lt61 : p4 < 61 := p4_lt_of_I3_bound_gap (N := 3 * 5 * 31) (B_q := 67) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 61) (by decide) (by decide : 0 < 2 * 4 * 30) (by decide)
      (by have := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le
            (ppSum_lt_lim (p := 5) (a := b) (by decide)).le) (ppSum_lt_lim (p := 31) (a := c) (by decide)).le; linarith)
      (by decide) hab
    have hmem0 := find_bases3 3 2 31 23 2 18755 [2, 7, 11, 22] (by decide)
    obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
    apply rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha3 hb2 hc hd he (by omega) (by omega) (by omega) hab hprim
    by_cases hbodd : b % 2 = 1
    · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
    · have hmp4 : ∃ q0, (p4, q0) ∈ cb5_31_all ∧ q0 ≤ q := by
        obtain ⟨q0, hq0m, hq0n⟩ := find_cb5 cb5_31_all 61 31 p4 hp4_lt61 hp34 hp4 (by decide)
        exact ⟨q0, hq0m, by by_contra! hlt; exact hq0n q hlt hp4q hq⟩
      exact run_cb5_p4 (h1 := none) (by decide) hp4 hq (by decide) hp34 hp4q (by omega) ha3 trivial hb2 (by omega)
        hc (by decide) (fun _ => rfl) hd he hab hprim (by decide) cb5_31_all_ok hmp4
  · -- p3 = 37: a >= 3 AND b >= 2, p4 <= 47 (< 53)
    have h41 : 41 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 41, 37 < t → ¬ t.Prime) p4 h hp34 hp4
    have ha3 : 3 ≤ a := by
      by_contra! hlt; have ha2 : a = 2 := (by omega); subst ha2
      exact absurd (p4_lt_of_I3_bound (N := 13 * 5 * 37) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 41) (by decide : 0 < 9 * 4 * 36)
        (by rw [(by decide : ppSum 3 2 = 13)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 5) (a := b) (by decide)).le (ppSum_lt_lim (p := 37) (a := c) (by decide)).le; linarith)
        (by decide) hab) (by omega)
    have hb2 : 2 ≤ b := by
      by_contra! hlt; have hb1 : b = 1 := (by omega); subst hb1
      exact absurd (p4_lt_of_I3_bound (N := 3 * 6 * 37) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 41) (by decide : 0 < 2 * 5 * 36)
        (by rw [(by decide : ppSum 5 1 = 6)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le (ppSum_lt_lim (p := 37) (a := c) (by decide)).le; linarith)
        (by decide) hab) (by omega)
    have hp4_lt53 : p4 < 53 := p4_lt_of_I3_bound_gap (N := 3 * 5 * 37) (B_q := 59) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 53) (by decide) (by decide : 0 < 2 * 4 * 36) (by decide)
      (by have := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le
            (ppSum_lt_lim (p := 5) (a := b) (by decide)).le) (ppSum_lt_lim (p := 37) (a := c) (by decide)).le; linarith)
      (by decide) hab
    have hmem0 := find_bases3 3 2 37 23 2 22145 [2, 7, 11, 22] (by decide)
    obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
    apply rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha3 hb2 hc hd he (by omega) (by omega) (by omega) hab hprim
    by_cases hbodd : b % 2 = 1
    · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
    · have hmp4 : ∃ q0, (p4, q0) ∈ cb5_37_all ∧ q0 ≤ q := by
        obtain ⟨q0, hq0m, hq0n⟩ := find_cb5 cb5_37_all 53 37 p4 hp4_lt53 hp34 hp4 (by decide)
        exact ⟨q0, hq0m, by by_contra! hlt; exact hq0n q hlt hp4q hq⟩
      exact run_cb5_p4 (h1 := none) (by decide) hp4 hq (by decide) hp34 hp4q (by omega) ha3 trivial hb2 (by omega)
        hc (by decide) (fun _ => rfl) hd he hab hprim (by decide) cb5_37_all_ok hmp4
  · -- p3 = 41: a >= 3 AND b >= 2, p4 <= 47 (< 53)
    have h43 : 43 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 43, 41 < t → ¬ t.Prime) p4 h hp34 hp4
    have ha3 : 3 ≤ a := by
      by_contra! hlt; have ha2 : a = 2 := (by omega); subst ha2
      exact absurd (p4_lt_of_I3_bound (N := 13 * 5 * 41) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 43) (by decide : 0 < 9 * 4 * 40)
        (by rw [(by decide : ppSum 3 2 = 13)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 5) (a := b) (by decide)).le (ppSum_lt_lim (p := 41) (a := c) (by decide)).le; linarith)
        (by decide) hab) (by omega)
    have hb2 : 2 ≤ b := by
      by_contra! hlt; have hb1 : b = 1 := (by omega); subst hb1
      exact absurd (p4_lt_of_I3_bound (N := 3 * 6 * 41) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 43) (by decide : 0 < 2 * 5 * 40)
        (by rw [(by decide : ppSum 5 1 = 6)]
            have := Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le (ppSum_lt_lim (p := 41) (a := c) (by decide)).le; linarith)
        (by decide) hab) (by omega)
    have hp4_lt53 : p4 < 53 := p4_lt_of_I3_bound (N := 3 * 5 * 41) (by decide) hp4 hq (by decide) hp34 hp4q (by decide : 2 ≤ 53) (by decide : 0 < 2 * 4 * 40)
      (by have := Nat.mul_le_mul (Nat.mul_le_mul (ppSum_lt_lim (p := 3) (a := a) (by decide)).le
            (ppSum_lt_lim (p := 5) (a := b) (by decide)).le) (ppSum_lt_lim (p := 41) (a := c) (by decide)).le; linarith)
      (by decide) hab
    have hmem0 := find_bases3 3 2 41 23 2 24405 [2, 7, 11, 22] (by decide)
    obtain ⟨ds, bestD, ds3, relN, hm⟩ := hmem0
    apply rank5_5_from_base3 hm (by decide) hp4 hq (by decide) hp34 hp4q ha3 hb2 hc hd he (by omega) (by omega) (by omega) hab hprim
    by_cases hbodd : b % 2 = 1
    · exact Or.inr (not_mem_bad_of_three_dvd hm (three_dvd_E_of_five_odd h3m h5sig hbodd hab_nat))
    · have hmp4 : ∃ q0, (p4, q0) ∈ cb5_41_all ∧ q0 ≤ q := by
        obtain ⟨q0, hq0m, hq0n⟩ := find_cb5 cb5_41_all 53 41 p4 hp4_lt53 hp34 hp4 (by decide)
        exact ⟨q0, hq0m, by by_contra! hlt; exact hq0n q hlt hp4q hq⟩
      exact run_cb5_p4 (h1 := none) (by decide) hp4 hq (by decide) hp34 hp4q (by omega) ha3 trivial hb2 (by omega)
        hc (fun _ => ⟨le_rfl, rfl⟩) (by decide) hd he hab hprim (by decide) cb5_41_all_ok hmp4

/-- Upper bound on abundancy index for m with 3 | m (arbitrary exponent of 3). -/
lemma prod_le_two_of_prime_bounds_gen {m : ℕ} (hm0 : m ≠ 0) (h3 : 3 ∈ m.primeFactors)
    (ps : List ℕ) (heq : (m.primeFactors.erase 3).toList.Perm ps)
    (hprod : 3 * (ps.map id).prod ≤ 4 * (ps.map (fun p => p - 1)).prod) : ¬ m.Abundant := by
  intro hab
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hsig_prod : sigma 1 m = ppSum 3 (m.factorization 3) * ∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p) := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors hm0, ← Finset.mul_prod_erase _ _ h3]
    rw [ppSum_eq_sigma (by decide : Nat.Prime 3), sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
    congr 1; apply Finset.prod_congr rfl; intro p hp
    have hpp := (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hp)).1
    rw [ppSum_eq_sigma hpp, sigma_one_apply_prime_pow hpp]
  have hm_prod : m = 3 ^ m.factorization 3 * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p := by
    have hfac := Nat.prod_primeFactors_pow_factorization hm0
    rw [← Finset.mul_prod_erase _ _ h3] at hfac; exact hfac
  have h3lim : ppSum 3 (m.factorization 3) * 2 ≤ 3 * 3 ^ m.factorization 3 := (ppSum_lt_lim (p := 3) (by decide)).le
  have h1 : (∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p)) *
      (∏ p ∈ m.primeFactors.erase 3, (p - 1)) ≤
      (∏ p ∈ m.primeFactors.erase 3, p) * (∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'; intro p hp
    exact (ppSum_lt_lim (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hp)).1.two_le).le
  have hperm_num : ∏ p ∈ m.primeFactors.erase 3, p = (ps.map id).prod := by
    rw [← Finset.prod_toList]; simpa using heq.prod_eq
  have hperm_den : ∏ p ∈ m.primeFactors.erase 3, (p - 1) = (ps.map (fun p => p - 1)).prod := by
    rw [← Finset.prod_map_toList]; exact (heq.map (fun p => p - 1)).prod_eq
  have hden_pos : 0 < ∏ p ∈ m.primeFactors.erase 3, (p - 1) := by
    apply Finset.prod_pos; intro p hp
    have := (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hp)).1.two_le; omega
  have hab_nat : 2 * (3 ^ m.factorization 3 * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) <
      ppSum 3 (m.factorization 3) * ∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p) := by
    have h := (abund_iff_nat hmpos).mp hab
    calc 2 * (3 ^ m.factorization 3 * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p)
        = 2 * m := by rw [← hm_prod]
      _ < sigma 1 m := h
      _ = ppSum 3 (m.factorization 3) * ∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p) := hsig_prod
  have hmul := Nat.mul_le_mul h3lim h1
  rw [hperm_num, hperm_den] at hmul
  have hlt := Nat.mul_lt_mul_of_pos_right hab_nat (by rw [← hperm_den]; positivity : 0 < 2 * (ps.map (fun p => p - 1)).prod)
  have hle2 := Nat.mul_le_mul_right (3 ^ m.factorization 3 * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) hprod
  have heq1 : (ppSum 3 (m.factorization 3) * ∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p)) * (2 * (ps.map (fun p => p - 1)).prod) =
      (ppSum 3 (m.factorization 3) * 2) * ((∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p)) * (ps.map (fun p => p - 1)).prod) := by ring
  have heq2 : (3 * 3 ^ m.factorization 3) * ((ps.map id).prod * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) =
      3 * (ps.map id).prod * (3 ^ m.factorization 3 * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) := by ring
  have heq3 : 4 * (ps.map (fun p => p - 1)).prod * (3 ^ m.factorization 3 * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) =
      2 * (3 ^ m.factorization 3 * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) * (2 * (ps.map (fun p => p - 1)).prod) := by ring
  linarith

end MainProofRank5

end R2H2

set_option maxHeartbeats 1600000 in
open Finset R2H2 in
theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2.H2 := by
  intro m hm_odd hm_ab hm_card hm_prim h9
  have hm_pos : 0 < m := hm_odd.pos
  have hm0 : m ≠ 0 := hm_pos.ne'
  have h3p : Nat.Prime 3 := by decide
  have h3dvd : 3 ∣ m := (by decide : 3 ∣ 9).trans h9
  have h3mem : 3 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨h3p, h3dvd, hm0⟩
  have hf3 : 2 ≤ m.factorization 3 := (h3p.pow_dvd_iff_le_factorization hm0).mp (by simpa using h9)
  let rest := m.primeFactors.erase 3
  have hrest_card : rest.card ≤ 4 := by
    have h1 : rest.card = m.primeFactors.card - 1 := Finset.card_erase_of_mem h3mem
    omega
  let ls := rest.sort (· ≤ ·)
  have hls_len : ls.length ≤ 4 := by simpa [ls] using hrest_card
  have hls_nd : ls.Nodup := Finset.sort_nodup _ _
  have hls_sorted : ls.Pairwise (· < ·) :=
    ((Finset.pairwise_sort rest (· ≤ ·)).and (List.nodup_iff_pairwise_ne.mp hls_nd)).imp
      (fun h => lt_of_le_of_ne h.1 h.2)
  have hls_prop : ∀ p ∈ ls, p.Prime ∧ 5 ≤ p ∧ 1 ≤ m.factorization p := by
    intro p hp
    have hmem_r : p ∈ rest := (Finset.mem_sort (· ≤ ·)).mp hp
    have hne3 : p ≠ 3 := (Finset.mem_erase.mp hmem_r).1
    have hmem_m := Nat.mem_primeFactors.mp (Finset.mem_erase.mp hmem_r).2
    have hne2 : p ≠ 2 := by rintro rfl; exact hm_odd.not_two_dvd_nat hmem_m.2.1
    have hge5 : 5 ≤ p := by
      by_contra! hlt
      exact (by decide : ∀ t < 5, t ≠ 2 → t ≠ 3 → ¬ t.Prime) p hlt hne2 hne3 hmem_m.1
    have hf : 1 ≤ m.factorization p :=
      (hmem_m.1.pow_dvd_iff_le_factorization hm0 (k := 1)).mp (by simpa using hmem_m.2.1)
    exact ⟨hmem_m.1, hge5, hf⟩
  have hperm_er3 : (m.primeFactors.erase 3).toList.Perm ls := (Finset.sort_perm_toList rest (· ≤ ·)).symm
  have hm_eq_list : m = 3 ^ m.factorization 3 * (ls.map (fun p => p ^ m.factorization p)).prod := by
    have hfac := Nat.prod_primeFactors_pow_factorization hm0
    rw [← Finset.mul_prod_erase _ _ h3mem] at hfac
    calc m = 3 ^ m.factorization 3 * ∏ p ∈ rest, p ^ m.factorization p := hfac
      _ = 3 ^ m.factorization 3 * (ls.map (fun p => p ^ m.factorization p)).prod := by
        congr 1; rw [← Finset.prod_map_toList]
        exact (hperm_er3.map (fun p => p ^ m.factorization p)).prod_eq
  rcases hls_cases : ls with _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨q, _ | _⟩⟩⟩⟩
  · -- card = 1: {3}
    exfalso; exact prod_le_two_of_prime_bounds_gen hm0 h3mem [] (by simpa [hls_cases] using hperm_er3) (by decide) hm_ab
  · -- card = 2: {3, p2}
    exfalso
    obtain ⟨_, h5p2, _⟩ := hls_prop p2 (by simp [hls_cases])
    have hbd : 3 * ([p2].map id).prod ≤ 4 * ([p2].map (fun p => p - 1)).prod := by
      simp; have := frac_anti (by decide : 2 ≤ 5) h5p2; omega
    exact prod_le_two_of_prime_bounds_gen hm0 h3mem [p2] (by simpa [hls_cases] using hperm_er3) hbd hm_ab
  · -- card = 3: {3, p2, p3}
    obtain ⟨hp2, h5p2, hfb⟩ := hls_prop p2 (by simp [hls_cases])
    obtain ⟨hp3, h5p3, hfc⟩ := hls_prop p3 (by simp [hls_cases])
    have hp23 : p2 < p3 := by
      rw [hls_cases] at hls_sorted; simpa using (List.pairwise_cons.mp hls_sorted).1 p3 List.mem_cons_self
    have hm_eq : m = 3 ^ m.factorization 3 * p2 ^ m.factorization p2 * p3 ^ m.factorization p3 := by
      conv_lhs => rw [hm_eq_list, hls_cases]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    have hp2_5 : p2 = 5 := by
      by_contra hne
      have h7 : 7 ≤ p2 := by by_contra! h; exact (by decide : ∀ t < 7, 5 ≤ t → t ≠ 5 → ¬ t.Prime) p2 h h5p2 hne hp2
      have h11 : 11 ≤ p3 := by by_contra! h; exact (by decide : ∀ t < 11, 7 < t → ¬ t.Prime) p3 h (by omega) hp3
      have hbd : 3 * ([p2, p3].map id).prod ≤ 4 * ([p2, p3].map (fun p => p - 1)).prod := by
        simp; have f1 := frac_anti (by decide : 2 ≤ 7) h7; have f2 := frac_anti (by decide : 2 ≤ 11) h11
        have := Nat.mul_le_mul f1 f2; nlinarith
      exact prod_le_two_of_prime_bounds_gen hm0 h3mem [p2, p3] (by simpa [hls_cases] using hperm_er3) hbd hm_ab
    subst hp2_5
    have hp3_lt17 : p3 < 17 := by
      by_contra! h17
      have hbd : 3 * ([5, p3].map id).prod ≤ 4 * ([5, p3].map (fun p => p - 1)).prod := by
        simp; have f2 := frac_anti (by decide : 2 ≤ 17) h17; nlinarith
      exact prod_le_two_of_prime_bounds_gen hm0 h3mem [5, p3] (by simpa [hls_cases] using hperm_er3) hbd hm_ab
    have hp3_c : p3 = 7 ∨ p3 = 11 ∨ p3 = 13 :=
      (by decide : ∀ t < 17, 5 < t → t.Prime → t = 7 ∨ t = 11 ∨ t = 13) p3 hp3_lt17 hp23 hp3
    rw [hm_eq] at hm_ab hm_prim ⊢
    exact rank3_pseudoperfect hp3_c hf3 hfb hfc hm_ab hm_prim
  · -- card = 4: {3, p2, p3, p4}
    obtain ⟨hp2, h5p2, hfb⟩ := hls_prop p2 (by simp [hls_cases])
    obtain ⟨hp3, h5p3, hfc⟩ := hls_prop p3 (by simp [hls_cases])
    obtain ⟨hp4, h5p4, hfd⟩ := hls_prop p4 (by simp [hls_cases])
    have hord : p2 < p3 ∧ p3 < p4 := by
      rw [hls_cases] at hls_sorted
      have h1 := List.pairwise_cons.mp hls_sorted
      have h2 := List.pairwise_cons.mp h1.2
      exact ⟨h1.1 p3 List.mem_cons_self, h2.1 p4 List.mem_cons_self⟩
    have hm_eq : m = 3 ^ m.factorization 3 * p2 ^ m.factorization p2 * p3 ^ m.factorization p3 * p4 ^ m.factorization p4 := by
      conv_lhs => rw [hm_eq_list, hls_cases]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    have hnot4 (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (h1 : a ≤ p2) (h2 : b ≤ p3) (h3 : c ≤ p4)
        (hcheck : 3 * (a * b * c) ≤ 4 * ((a - 1) * (b - 1) * (c - 1))) : False := by
      have hbd : 3 * ([p2, p3, p4].map id).prod ≤ 4 * ([p2, p3, p4].map (fun p => p - 1)).prod := by
        simp only [List.map_cons, List.map_nil, id_eq, List.prod_cons, List.prod_nil, mul_one]
        have f1 := frac_anti ha h1; have f2 := frac_anti hb h2; have f3 := frac_anti hc h3
        have hmul := Nat.mul_le_mul (Nat.mul_le_mul f1 f2) f3
        have hden : 0 < (a - 1) * (b - 1) * (c - 1) := by
          have : 0 < a - 1 := (by omega); have : 0 < b - 1 := (by omega); have : 0 < c - 1 := (by omega); positivity
        apply Nat.le_of_mul_le_mul_right _ hden
        have hL : 3 * (p2 * (p3 * p4)) * ((a - 1) * (b - 1) * (c - 1)) ≤ 3 * (a * b * c) * ((p2 - 1) * (p3 - 1) * (p4 - 1)) := by
          have := Nat.mul_le_mul_left 3 hmul; linarith
        have hR := Nat.mul_le_mul_right ((p2 - 1) * (p3 - 1) * (p4 - 1)) hcheck
        linarith
      exact prod_le_two_of_prime_bounds_gen hm0 h3mem [p2, p3, p4] (by simpa [hls_cases] using hperm_er3) hbd hm_ab
    by_cases hp2_5 : p2 = 5
    · subst hp2_5
      have hp3_lt31 : p3 < 31 := by
        by_contra! h31
        have h37 : 37 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 37, 31 < t → ¬ t.Prime) p4 h (by omega) hp4
        exact hnot4 5 31 37 (by decide) (by decide) (by decide) le_rfl h31 h37 (by decide)
      have hp3_mem : p3 ∈ ({7, 11, 13, 17, 19, 23, 29} : Finset ℕ) :=
        (by decide : ∀ t < 31, 5 < t → t.Prime → t ∈ ({7, 11, 13, 17, 19, 23, 29} : Finset ℕ)) p3 hp3_lt31 hord.1 hp3
      rw [hm_eq] at hm_ab hm_prim ⊢
      exact rank4_5_pseudoperfect hp3_mem hp4 hord.2 hf3 hfb hfc hfd hm_ab hm_prim
    · have hp2_7 : p2 = 7 := by
        by_contra hne
        have h11 : 11 ≤ p2 := by by_contra! h; exact (by decide : ∀ t < 11, 5 ≤ t → t ≠ 5 → t ≠ 7 → ¬ t.Prime) p2 h h5p2 hp2_5 hne hp2
        have h13 : 13 ≤ p3 := by by_contra! h; exact (by decide : ∀ t < 13, 11 < t → ¬ t.Prime) p3 h (by omega) hp3
        have h17 : 17 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 17, 13 < t → ¬ t.Prime) p4 h (by omega) hp4
        exact hnot4 11 13 17 (by decide) (by decide) (by decide) h11 h13 h17 (by decide)
      subst hp2_7
      have hp3_lt17 : p3 < 17 := by
        by_contra! h17
        have h19 : 19 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 19, 17 < t → ¬ t.Prime) p4 h (by omega) hp4
        exact hnot4 7 17 19 (by decide) (by decide) (by decide) le_rfl h17 h19 (by decide)
      have hp3_c : p3 = 11 ∨ p3 = 13 := (by decide : ∀ t < 17, 7 < t → t.Prime → t = 11 ∨ t = 13) p3 hp3_lt17 hord.1 hp3
      have hmem6 : (7, p3, p4) ∈ [(7,11,13),(7,11,17),(7,11,19),(7,11,23),(7,13,17),(7,13,19)] := by
        rcases hp3_c with rfl | rfl
        · have hlt29 : p4 < 29 := by by_contra! h29; exact hnot4 7 11 29 (by decide) (by decide) (by decide) le_rfl le_rfl h29 (by decide)
          have hc4 := (by decide : ∀ t < 29, 11 < t → t.Prime → t = 13 ∨ t = 17 ∨ t = 19 ∨ t = 23) p4 hlt29 hord.2 hp4
          rcases hc4 with rfl | rfl | rfl | rfl <;> simp
        · have hlt23 : p4 < 23 := by by_contra! h23; exact hnot4 7 13 23 (by decide) (by decide) (by decide) le_rfl le_rfl h23 (by decide)
          have hc4 := (by decide : ∀ t < 23, 13 < t → t.Prime → t = 17 ∨ t = 19) p4 hlt23 hord.2 hp4
          rcases hc4 with rfl | rfl <;> simp
      rw [hm_eq] at hm_ab hm_prim ⊢
      exact rank4_no5_pseudoperfect hmem6 hf3 hfb hfc hfd hm_ab hm_prim
  · -- card = 5: {3, p2, p3, p4, q}
    obtain ⟨hp2, h5p2, hfb⟩ := hls_prop p2 (by simp [hls_cases])
    obtain ⟨hp3, h5p3, hfc⟩ := hls_prop p3 (by simp [hls_cases])
    obtain ⟨hp4, h5p4, hfd⟩ := hls_prop p4 (by simp [hls_cases])
    obtain ⟨hq, h5q, hfe⟩ := hls_prop q (by simp [hls_cases])
    have hord : p2 < p3 ∧ p3 < p4 ∧ p4 < q := by
      rw [hls_cases] at hls_sorted
      have h1 := List.pairwise_cons.mp hls_sorted
      have h2 := List.pairwise_cons.mp h1.2
      have h3 := List.pairwise_cons.mp h2.2
      exact ⟨h1.1 p3 List.mem_cons_self, h2.1 p4 List.mem_cons_self, h3.1 q List.mem_cons_self⟩
    have hm_eq : m = 3 ^ m.factorization 3 * p2 ^ m.factorization p2 * p3 ^ m.factorization p3 *
        p4 ^ m.factorization p4 * q ^ m.factorization q := by
      conv_lhs => rw [hm_eq_list, hls_cases]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    have hnot5 (a b c d : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
        (h1 : a ≤ p2) (h2 : b ≤ p3) (h3 : c ≤ p4) (h4 : d ≤ q)
        (hcheck : 3 * (a * b * c * d) ≤ 4 * ((a - 1) * (b - 1) * (c - 1) * (d - 1))) : False := by
      have hbd : 3 * ([p2, p3, p4, q].map id).prod ≤ 4 * ([p2, p3, p4, q].map (fun p => p - 1)).prod := by
        simp only [List.map_cons, List.map_nil, id_eq, List.prod_cons, List.prod_nil, mul_one]
        have f1 := frac_anti ha h1; have f2 := frac_anti hb h2; have f3 := frac_anti hc h3; have f4 := frac_anti hd h4
        have hmul := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul f1 f2) f3) f4
        have hden : 0 < (a - 1) * (b - 1) * (c - 1) * (d - 1) := by
          have : 0 < a - 1 := (by omega); have : 0 < b - 1 := (by omega); have : 0 < c - 1 := (by omega); have : 0 < d - 1 := (by omega); positivity
        apply Nat.le_of_mul_le_mul_right _ hden
        have hL : 3 * (p2 * (p3 * (p4 * q))) * ((a - 1) * (b - 1) * (c - 1) * (d - 1)) ≤
            3 * (a * b * c * d) * ((p2 - 1) * (p3 - 1) * (p4 - 1) * (q - 1)) := by
          have := Nat.mul_le_mul_left 3 hmul; linarith
        have hR := Nat.mul_le_mul_right ((p2 - 1) * (p3 - 1) * (p4 - 1) * (q - 1)) hcheck
        linarith
      exact prod_le_two_of_prime_bounds_gen hm0 h3mem [p2, p3, p4, q] (by simpa [hls_cases] using hperm_er3) hbd hm_ab
    by_cases hp2_5 : p2 = 5
    · subst hp2_5
      have hp3_lt43 : p3 < 43 := by
        by_contra! h43
        have h47 : 47 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 47, 43 < t → ¬ t.Prime) p4 h (by omega) hp4
        have h53 : 53 ≤ q := by by_contra! h; exact (by decide : ∀ t < 53, 47 < t → ¬ t.Prime) q h (by omega) hq
        exact hnot5 5 43 47 53 (by decide) (by decide) (by decide) (by decide) le_rfl h43 h47 h53 (by decide)
      have hp3_mem : p3 ∈ ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41} : Finset ℕ) :=
        (by decide : ∀ t < 43, 5 < t → t.Prime → t ∈ ({7, 11, 13, 17, 19, 23, 29, 31, 37, 41} : Finset ℕ)) p3 hp3_lt43 hord.1 hp3
      rw [hm_eq] at hm_ab hm_prim ⊢
      exact rank5_5_pseudoperfect hp3_mem hp4 hq hord.2.1 hord.2.2 hf3 hfb hfc hfd hfe hm_ab hm_prim
    · -- 5 nmid m => p2 in {7, 11}, (p2, p3, p4) in basesNo5Data!
      have hp2_lt13 : p2 < 13 := by
        by_contra! h13
        have h17 : 17 ≤ p3 := by by_contra! h; exact (by decide : ∀ t < 17, 13 < t → ¬ t.Prime) p3 h (by omega) hp3
        have h19 : 19 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 19, 17 < t → ¬ t.Prime) p4 h (by omega) hp4
        have h23 : 23 ≤ q := by by_contra! h; exact (by decide : ∀ t < 23, 19 < t → ¬ t.Prime) q h (by omega) hq
        exact hnot5 13 17 19 23 (by decide) (by decide) (by decide) (by decide) h13 h17 h19 h23 (by decide)
      have hp2_c : p2 = 7 ∨ p2 = 11 :=
        (by decide : ∀ t < 13, 5 ≤ t → t ≠ 5 → t.Prime → t = 7 ∨ t = 11) p2 hp2_lt13 h5p2 hp2_5 hp2
      have hmem19 : ∃ q0 L g P0 bad ds a2 a3 a4 ds2 ds3 ds4,
          (p2, p3, p4, q0, L, g, P0, bad, ds, a2, a3, a4, ds2, ds3, ds4) ∈ basesNo5Data := by
        rcases hp2_c with rfl | rfl
        · have hp3_lt23 : p3 < 23 := by
            by_contra! h23
            have h29 : 29 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 29, 23 < t → ¬ t.Prime) p4 h (by omega) hp4
            have h31 : 31 ≤ q := by by_contra! h; exact (by decide : ∀ t < 31, 29 < t → ¬ t.Prime) q h (by omega) hq
            exact hnot5 7 23 29 31 (by decide) (by decide) (by decide) (by decide) le_rfl h23 h29 h31 (by decide)
          have hp3_c : p3 = 11 ∨ p3 = 13 ∨ p3 = 17 ∨ p3 = 19 :=
            (by decide : ∀ t < 23, 7 < t → t.Prime → t = 11 ∨ t = 13 ∨ t = 17 ∨ t = 19) p3 hp3_lt23 hord.1 hp3
          rcases hp3_c with rfl | rfl | rfl | rfl
          · have hlt53 : p4 < 53 := by
              by_contra! h53
              have h59 : 59 ≤ q := by by_contra! h; exact (by decide : ∀ t < 59, 53 < t → ¬ t.Prime) q h (by omega) hq
              exact hnot5 7 11 53 59 (by decide) (by decide) (by decide) (by decide) le_rfl le_rfl h53 h59 (by decide)
            exact R2H2.find_basesNo5 7 11 53 11 p4 hlt53 hord.2.1 hp4 (by decide)
          · have hlt37 : p4 < 37 := by
              by_contra! h37
              have h41 : 41 ≤ q := by by_contra! h; exact (by decide : ∀ t < 41, 37 < t → ¬ t.Prime) q h (by omega) hq
              exact hnot5 7 13 37 41 (by decide) (by decide) (by decide) (by decide) le_rfl le_rfl h37 h41 (by decide)
            exact R2H2.find_basesNo5 7 13 37 13 p4 hlt37 hord.2.1 hp4 (by decide)
          · have hlt29 : p4 < 29 := by
              by_contra! h29
              have h31 : 31 ≤ q := by by_contra! h; exact (by decide : ∀ t < 31, 29 < t → ¬ t.Prime) q h (by omega) hq
              exact hnot5 7 17 29 31 (by decide) (by decide) (by decide) (by decide) le_rfl le_rfl h29 h31 (by decide)
            exact R2H2.find_basesNo5 7 17 29 17 p4 hlt29 hord.2.1 hp4 (by decide)
          · have hlt29 : p4 < 29 := by
              by_contra! h29
              have h31 : 31 ≤ q := by by_contra! h; exact (by decide : ∀ t < 31, 29 < t → ¬ t.Prime) q h (by omega) hq
              exact hnot5 7 19 29 31 (by decide) (by decide) (by decide) (by decide) le_rfl le_rfl h29 h31 (by decide)
            exact R2H2.find_basesNo5 7 19 29 19 p4 hlt29 hord.2.1 hp4 (by decide)
        · have hp3_13 : p3 = 13 := by
            by_contra hne
            have h17 : 17 ≤ p3 := by by_contra! h; exact (by decide : ∀ t < 17, 11 < t → t ≠ 13 → ¬ t.Prime) p3 h hord.1 hne hp3
            have h19 : 19 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 19, 17 < t → ¬ t.Prime) p4 h (by omega) hp4
            have h23 : 23 ≤ q := by by_contra! h; exact (by decide : ∀ t < 23, 19 < t → ¬ t.Prime) q h (by omega) hq
            exact hnot5 11 17 19 23 (by decide) (by decide) (by decide) (by decide) le_rfl h17 h19 h23 (by decide)
          subst hp3_13
          have hp4_17 : p4 = 17 := by
            by_contra hne
            have h19 : 19 ≤ p4 := by by_contra! h; exact (by decide : ∀ t < 19, 13 < t → t ≠ 17 → ¬ t.Prime) p4 h hord.2.1 hne hp4
            have h23 : 23 ≤ q := by by_contra! h; exact (by decide : ∀ t < 23, 19 < t → ¬ t.Prime) q h (by omega) hq
            exact hnot5 11 13 19 23 (by decide) (by decide) (by decide) (by decide) le_rfl le_rfl h19 h23 (by decide)
          subst hp4_17
          exact R2H2.find_basesNo5_one 11 13 17 (by decide)
      rw [hm_eq] at hm_ab hm_prim ⊢
      exact rank5_no5_pseudoperfect hmem19 hq hord.2.2 hf3 hfb hfc hfd hfe hm_ab hm_prim
  · simp [hls_cases] at hls_len; omega
