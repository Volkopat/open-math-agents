import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2
import Mathlib

/-!
Proof of Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H1:
Every odd primitive abundant multiple of 15 with at most five distinct prime factors
and not divisible by 9 is pseudoperfect.

Structure:
1. Final-prime interval translation lemmas (generalizing central interval [L, P - L] and gap g).
2. Interval-list subset-sum checker for the 19 squarefree 4-prime bases B0 = 3 * 5 * p3 * p4
   and for 525, plus inductive prime-power lifting preserving [L, P - L] and gap g.
3. Exact rank-4 classification (13 minimal abundant numbers with explicit excess witnesses).
4. Pure-Nat 3D branch-and-bound certificate engine proving that when b is even and 3 does not
   divide E, every odd primitive abundant 5-prime candidate has E >= 30.
5. Main classification and assembly of OMA.solution.
-/

namespace R2H1

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

def checkCoreB (B0 L g P0 : ℕ) (ds : List ℕ) : Bool :=
  let ivs := ivsOfList ds
  decide (ds.Nodup) &&
  ds.all (fun d => decide (d ∣ B0 ∧ d < B0)) &&
  decide (ds.sum = P0) &&
  ivs.any (fun ab => decide (ab.1 ≤ L ∧ P0 - L ≤ ab.2)) &&
  checkGapsB ivs g &&
  (match ivs.head?, ivs.getLast? with
   | some p, some q => decide (p.1 = 0 ∧ p.1 ≤ p.2 ∧ q.1 ≤ q.2 ∧ q.2 = P0)
   | _, _ => false) &&
  (List.range L).all (fun x => decide (x % 12 ≠ 6) || inIvsB ivs x)

lemma core_of_checkCoreB {B0 L g P0 : ℕ} {ds : List ℕ}
    (hg : 1 ≤ g) (hP : P0 = ∑ d ∈ B0.properDivisors, d)
    (hchk : checkCoreB B0 L g P0 ds = true) :
    (∀ y : ℕ, L ≤ y → y ≤ P0 - L → repNat B0.properDivisors y) ∧
    (∀ k : ℕ, k < P0 → ∃ i : ℕ, repNat B0.properDivisors i ∧ k < i + g ∧ i ≤ k) ∧
    (∀ x : ℕ, x < L → x % 12 = 6 → repNat B0.properDivisors x) := by
  unfold checkCoreB at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hnd, hsub⟩, _⟩, ⟨ab, hab, habL, habR⟩⟩, hgaps⟩, hhl⟩, hmod12⟩ := hchk
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
  · intro x hx hx12
    have hxm := hmod12 x (List.mem_range.mpr hx)
    rcases hxm with hne | hin
    · exact absurd hx12 hne
    · exact hsound x (inIvs_of_inIvsB hin)

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

section Cert3D

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

inductive Cert where
  | pd : Cert
  | pb : Cert
  | tq (q1' : ℕ) (sub : Cert) : Cert
  | pcs (fs : List ℕ) (sub : Cert) : Cert
  | pt (subLo subHi : Cert) : Cert
  | sp (axis : Nat) (subEq subGt : Cert) : Cert
  | ld (eMin : ℕ) (f2 : Option (ℕ × ℕ)) : Cert

def checkPcs (q1 : ℕ) : List ℕ → Option ℕ
  | [] => some q1
  | f :: rest =>
    if 1 < f ∧ f < q1 ∧ q1 % f = 0 then checkPcs (q1 - 1) rest else none

lemma checkPcs_sound {q1 q' q : ℕ} {fs : List ℕ} (hq : q.Prime) (hqle : q ≤ q1)
    (h : checkPcs q1 fs = some q') : q ≤ q' := by
  induction fs generalizing q1 with
  | nil =>
    simp only [checkPcs, Option.some.injEq] at h
    omega
  | cons f rest ih =>
    simp only [checkPcs] at h
    split_ifs at h with hc
    have hne : q ≠ q1 := by
      rintro rfl
      have hdvd : f ∣ q := Nat.dvd_of_mod_eq_zero hc.2.2
      rcases hq.eq_one_or_self_of_dvd f hdvd with h1 | h2 <;> omega
    exact ih (by omega) h

def checkFixedB (p3 p4 b c d : ℕ) (f2 : Option (ℕ × ℕ)) : Bool :=
  if b % 2 = 1 then true
  else
    let B := 3 * 5 ^ b * p3 ^ c * p4 ^ d
    let sB := 4 * ppSum 5 b * ppSum p3 c * ppSum p4 d
    if 2 * B ≤ sB then true
    else
      let D := 2 * B - sB
      let rem := sB % D
      let ok1 := decide ((rem = 0 ∧ 30 ≤ D) ∨ 30 ≤ rem)
      let ok2 :=
        if rem = 0 then true
        else
          let q := sB / D + 1
          if q ≤ p4 then true
          else
            match f2 with
            | none => false
            | some (0, f) => decide (1 < f ∧ f < q ∧ q % f = 0)
            | some (e0, 0) =>
              decide (2 ≤ e0 ∧
                sB * ppSum q (e0 - 1) < 2 * B * q ^ (e0 - 1) ∧
                2 * B * q ^ e0 < sB * ppSum q e0 ∧
                (30 ≤ sB * ppSum q e0 - 2 * B * q ^ e0 ∨
                  (sB * ppSum q e0 - 2 * B * q ^ e0) % 3 = 0))
            | some _ => false
      ok1 && ok2

def Cert.ok (p3 p4 : ℕ) (b0 : ℕ) (b1 : Option ℕ) (c0 : ℕ) (c1 : Option ℕ)
    (d0 : ℕ) (d1 : Option ℕ) (q0 q1 : ℕ) : Cert → Bool
  | .pd =>
    decide (q1 < q0 ∨ (2 ≤ q0 ∧
      2 * (hiNum 5 b1 * hiNum p3 c1 * hiNum p4 d1 * q0) ≤
      3 * (hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * (q0 - 1))))
  | .pb =>
    decide (3 * (5 ^ b0 * p3 ^ c0 * p4 ^ d0) ≤ 2 * (ppSum 5 b0 * ppSum p3 c0 * ppSum p4 d0))
  | .tq q1' sub =>
    decide (q1' < q1 ∧ 1 ≤ q1' ∧
      2 * (hiNum 5 b1 * hiNum p3 c1 * hiNum p4 d1 * (q1' + 1)) ≤
      3 * (hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * q1')) &&
    Cert.ok p3 p4 b0 b1 c0 c1 d0 d1 q0 q1' sub
  | .pcs fs sub =>
    match checkPcs q1 fs with
    | none => false
    | some q1' => Cert.ok p3 p4 b0 b1 c0 c1 d0 d1 q0 q1' sub
  | .pt subLo subHi =>
    decide (q0 < q1) &&
    Cert.ok p3 p4 b0 b1 c0 c1 d0 d1 q0 (q1 - 1) subLo &&
    Cert.ok p3 p4 b0 b1 c0 c1 d0 d1 q1 q1 subHi
  | .sp axis subEq subGt =>
    if axis = 0 then
      Cert.ok p3 p4 b0 (some b0) c0 c1 d0 d1 q0 q1 subEq &&
      Cert.ok p3 p4 (b0 + 1) b1 c0 c1 d0 d1 q0 q1 subGt
    else if axis = 1 then
      Cert.ok p3 p4 b0 b1 c0 (some c0) d0 d1 q0 q1 subEq &&
      Cert.ok p3 p4 b0 b1 (c0 + 1) c1 d0 d1 q0 q1 subGt
    else
      Cert.ok p3 p4 b0 b1 c0 c1 d0 (some d0) q0 q1 subEq &&
      Cert.ok p3 p4 b0 b1 c0 c1 (d0 + 1) d1 q0 q1 subGt
  | .ld eMin f2 =>
    let domOk :=
      if eMin = 1 then
        decide (1 ≤ q1 ∧
          3 * (5 ^ b0 * p3 ^ c0 * p4 ^ d0 * q1) <
          2 * (ppSum 5 b0 * ppSum p3 c0 * ppSum p4 d0 * (q1 + 1)))
      else
        decide (2 ≤ eMin ∧ q0 = q1 ∧ 2 ≤ q1 ∧
          2 * (hiNum 5 b1 * hiNum p3 c1 * hiNum p4 d1 * ppSum q1 (eMin - 1)) ≤
          3 * (hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * q1 ^ (eMin - 1)) ∧
          3 * (5 ^ b0 * p3 ^ c0 * p4 ^ d0 * q1 ^ eMin) <
          2 * (ppSum 5 b0 * ppSum p3 c0 * ppSum p4 d0 * ppSum q1 eMin))
    domOk && checkFixedB p3 p4 b0 c0 d0 f2

/-- Algebraic sigma formula for 3 * 5^b * p3^c * p4^d * q^e when primes are distinct. -/
lemma sigma_five_primes {p3 p4 q b c d e : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hq : q.Prime)
    (h3 : 5 < p3) (h4 : p3 < p4) (h5 : p4 < q) :
    sigma 1 (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) =
      4 * ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e := by
  have h5p : Nat.Prime 5 := by decide
  have h3p : Nat.Prime 3 := by decide
  have hc35 : Nat.Coprime 3 (5 ^ b) :=
    ((Nat.coprime_primes h3p h5p).mpr (by decide)).pow_right b
  have hc_p3 : Nat.Coprime (3 * 5 ^ b) (p3 ^ c) :=
    (Nat.Coprime.mul_left ((Nat.coprime_primes h3p hp3).mpr (by omega))
      (((Nat.coprime_primes h5p hp3).mpr (by omega)).pow_left b)).pow_right c
  have hc_p4 : Nat.Coprime (3 * 5 ^ b * p3 ^ c) (p4 ^ d) :=
    (Nat.Coprime.mul_left
      (Nat.Coprime.mul_left ((Nat.coprime_primes h3p hp4).mpr (by omega))
        (((Nat.coprime_primes h5p hp4).mpr (by omega)).pow_left b))
      (((Nat.coprime_primes hp3 hp4).mpr (by omega)).pow_left c)).pow_right d
  have hc_q : Nat.Coprime (3 * 5 ^ b * p3 ^ c * p4 ^ d) (q ^ e) :=
    (Nat.Coprime.mul_left
      (Nat.Coprime.mul_left
        (Nat.Coprime.mul_left ((Nat.coprime_primes h3p hq).mpr (by omega))
          (((Nat.coprime_primes h5p hq).mpr (by omega)).pow_left b))
        (((Nat.coprime_primes hp3 hq).mpr (by omega)).pow_left c))
      (((Nat.coprime_primes hp4 hq).mpr (by omega)).pow_left d)).pow_right e
  rw [isMultiplicative_sigma.map_mul_of_coprime hc_q,
      isMultiplicative_sigma.map_mul_of_coprime hc_p4,
      isMultiplicative_sigma.map_mul_of_coprime hc_p3,
      isMultiplicative_sigma.map_mul_of_coprime hc35]
  rw [← ppSum_eq_sigma h5p, ← ppSum_eq_sigma hp3, ← ppSum_eq_sigma hp4, ← ppSum_eq_sigma hq]
  have hs3 : sigma 1 3 = 4 := by decide
  rw [hs3]

lemma sigma_four_primes {p3 p4 b c d : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (h3 : 5 < p3) (h4 : p3 < p4) :
    sigma 1 (3 * 5 ^ b * p3 ^ c * p4 ^ d) =
      4 * ppSum 5 b * ppSum p3 c * ppSum p4 d := by
  have h5p : Nat.Prime 5 := by decide
  have h3p : Nat.Prime 3 := by decide
  have hc35 : Nat.Coprime 3 (5 ^ b) :=
    ((Nat.coprime_primes h3p h5p).mpr (by decide)).pow_right b
  have hc_p3 : Nat.Coprime (3 * 5 ^ b) (p3 ^ c) :=
    (Nat.Coprime.mul_left ((Nat.coprime_primes h3p hp3).mpr (by omega))
      (((Nat.coprime_primes h5p hp3).mpr (by omega)).pow_left b)).pow_right c
  have hc_p4 : Nat.Coprime (3 * 5 ^ b * p3 ^ c) (p4 ^ d) :=
    (Nat.Coprime.mul_left
      (Nat.Coprime.mul_left ((Nat.coprime_primes h3p hp4).mpr (by omega))
        (((Nat.coprime_primes h5p hp4).mpr (by omega)).pow_left b))
      (((Nat.coprime_primes hp3 hp4).mpr (by omega)).pow_left c)).pow_right d
  rw [isMultiplicative_sigma.map_mul_of_coprime hc_p4,
      isMultiplicative_sigma.map_mul_of_coprime hc_p3,
      isMultiplicative_sigma.map_mul_of_coprime hc35]
  rw [← ppSum_eq_sigma h5p, ← ppSum_eq_sigma hp3, ← ppSum_eq_sigma hp4]
  have hs3 : sigma 1 3 = 4 := by decide
  rw [hs3]

lemma abund_iff_nat {n : ℕ} (hn : 0 < n) : n.Abundant ↔ 2 * n < sigma 1 n := by
  change n < ∑ d ∈ n.properDivisors, d ↔ 2 * n < sigma 1 n
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

lemma defic_iff_nat {n : ℕ} (hn : 0 < n) : n.Deficient ↔ sigma 1 n < 2 * n := by
  change ∑ d ∈ n.properDivisors, d < n ↔ sigma 1 n < 2 * n
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

lemma checkFixedB_sound {p3 p4 q b c d e : ℕ} {f2 : Option (ℕ × ℕ)}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hq : q.Prime)
    (h3 : 5 < p3) (h4 : p3 < p4) (h5 : p4 < q) (he : 1 ≤ e)
    (hb_even : b % 2 = 0)
    (hab : (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).properDivisors, x.Deficient)
    (hchk : checkFixedB p3 p4 b c d f2 = true) :
    30 ≤ sigma 1 (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) -
      2 * (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) ∨
    (sigma 1 (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) -
      2 * (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e)) % 3 = 0 := by
  let B := 3 * 5 ^ b * p3 ^ c * p4 ^ d
  let sB := 4 * ppSum 5 b * ppSum p3 c * ppSum p4 d
  have hBpos : 0 < B := by have := hp3.pos; have := hp4.pos; positivity
  have hsigB : sigma 1 B = sB := sigma_four_primes hp3 hp4 h3 h4
  have hBmem : B ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
    ⟨dvd_mul_right B (q ^ e),
     by simpa using Nat.mul_lt_mul_of_pos_left (one_lt_pow₀ hq.one_lt (by omega)) hBpos⟩
  have hBdef : sB < 2 * B := by
    rw [← hsigB]; exact (defic_iff_nat hBpos).mp (hprim B hBmem)
  have hmpos : 0 < B * q ^ e := by have := hq.pos; positivity
  have hsigm : sigma 1 (B * q ^ e) = sB * ppSum q e := sigma_five_primes hp3 hp4 hq h3 h4 h5
  have hmab : 2 * (B * q ^ e) < sB * ppSum q e := by
    rw [← hsigm]; exact (abund_iff_nat hmpos).mp hab
  unfold checkFixedB at hchk
  have hnotle : ¬ (2 * (3 * 5 ^ b * p3 ^ c * p4 ^ d) ≤ 4 * ppSum 5 b * ppSum p3 c * ppSum p4 d) := by
    dsimp only [B, sB] at hBdef; omega
  simp only [hb_even, Nat.zero_ne_one, ↓reduceIte, hnotle,
    Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hok1, hok2⟩ := hchk
  let D := 2 * B - sB
  have hDpos : 0 < D := by omega
  have hq_lt : D * q < 2 * B := by
    have hlim : ppSum q e * (q - 1) < q * q ^ e := ppSum_lt_lim hq.two_le
    have h1 : 2 * B * q ^ e * (q - 1) < sB * (q * q ^ e) := by
      calc 2 * B * q ^ e * (q - 1) < (sB * ppSum q e) * (q - 1) :=
            Nat.mul_lt_mul_of_pos_right (by simpa [mul_assoc] using hmab) (by have := hq.two_le; omega)
        _ = sB * (ppSum q e * (q - 1)) := by ring
        _ < sB * (q * q ^ e) := Nat.mul_lt_mul_of_pos_left hlim (by
            have : 0 < sigma 1 B := sigma_pos_iff.mpr hBpos; omega)
    have h2 : 2 * B * (q - 1) < sB * q := by
      have hqe : 0 < q ^ e := pow_pos hq.pos e
      nlinarith
    have hq1 : 1 ≤ q := hq.pos
    dsimp only [D]
    zify [hq1, (show sB ≤ 2 * B by omega)] at h2 ⊢
    nlinarith
  by_cases he1 : e = 1
  · subst he1
    have hpp1 : ppSum q 1 = q + 1 := by
      rw [ppSum_eq_sigma hq, sigma_one_apply_prime_pow hq]
      simp [Finset.sum_range_succ, add_comm]
    rw [hsigm]
    rw [hpp1, pow_one] at hmab ⊢
    have hDq_lt : D * q < sB := by
      dsimp only [D]
      zify [(show sB ≤ 2 * B by omega)] at hmab ⊢; linarith
    have hE : sB * (q + 1) - 2 * (B * q) = sB - D * q := by
      have hDq_le : D * q ≤ sB := hDq_lt.le
      dsimp only [D] at hDq_le ⊢
      zify [hDq_le, (show sB ≤ 2 * B by omega), (show 2 * (B * q) ≤ sB * (q + 1) by omega)]
      ring
    have hdiv_mod := Nat.div_add_mod sB D
    have hrem_lt : sB % D < D := Nat.mod_lt sB hDpos
    have hq_le_div : q ≤ sB / D := by
      by_contra! hgt
      have : D * (sB / D + 1) ≤ D * q := Nat.mul_le_mul_left D hgt
      have : D * (sB / D + 1) = D * (sB / D) + D := by ring
      omega
    have hE_ge : (if sB % D = 0 then D else sB % D) ≤ sB - D * q := by
      split_ifs with h0
      · have hlt : q < sB / D := by
          by_contra! hge
          have hqe : q = sB / D := by omega
          rw [hqe] at hDq_lt; omega
        have : D * (q + 1) ≤ D * (sB / D) := Nat.mul_le_mul_left D hlt
        have : D * (q + 1) = D * q + D := by ring
        omega
      · have : D * q ≤ D * (sB / D) := Nat.mul_le_mul_left D hq_le_div
        omega
    left
    rw [hE]
    rcases hok1 with ⟨h0, h30⟩ | h30
    · change sB % D = 0 at h0
      change 30 ≤ D at h30
      simp only [h0, ↓reduceIte] at hE_ge; omega
    · change 30 ≤ sB % D at h30
      by_cases h0 : sB % D = 0
      · omega
      · simp only [h0, ↓reduceIte] at hE_ge; omega
  · have he2 : 2 ≤ e := by omega
    have hBq_mem : B * q ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_left B (dvd_pow_self q (by omega)),
       Nat.mul_lt_mul_of_pos_left (by simpa using Nat.pow_lt_pow_right hq.one_lt (by omega : 1 < e)) hBpos⟩
    have hBq_def : sigma 1 (B * q) < 2 * (B * q) :=
      (defic_iff_nat (mul_pos hBpos hq.pos)).mp (hprim (B * q) hBq_mem)
    have hsigBq : sigma 1 (B * q) = sB * (q + 1) := by
      have := sigma_five_primes hp3 hp4 hq h3 h4 h5 (b := b) (c := c) (d := d) (e := 1)
      have hpp1 : ppSum q 1 = q + 1 := by
        rw [ppSum_eq_sigma hq, sigma_one_apply_prime_pow hq]
        simp [Finset.sum_range_succ, add_comm]
      simpa [B, sB, hpp1] using this
    rw [hsigBq] at hBq_def
    have hsB_lt_Dq : sB < D * q := by
      dsimp only [D]
      zify [(show sB ≤ 2 * B by omega)] at hBq_def ⊢; linarith
    have hrem_ne : sB % D ≠ 0 := by
      intro h0
      have hdiv_mod := Nat.div_add_mod sB D
      have hq_gt : sB / D < q := by
        by_contra! hle
        have : D * q ≤ D * (sB / D) := Nat.mul_le_mul_left D hle
        omega
      have : D * (sB / D + 1) ≤ D * q := Nat.mul_le_mul_left D hq_gt
      have : D * (sB / D + 1) = D * (sB / D) + D := by ring
      omega
    have hq_eq : q = sB / D + 1 := by
      have hdiv_mod := Nat.div_add_mod sB D
      have hrem_lt : sB % D < D := Nat.mod_lt sB hDpos
      have hq_gt : sB / D < q := by
        by_contra! hle
        have : D * q ≤ D * (sB / D) := Nat.mul_le_mul_left D hle
        omega
      have hq_lt2 : q < sB / D + 2 := by
        by_contra! hge
        have : D * (sB / D + 2) ≤ D * q := Nat.mul_le_mul_left D hge
        have : D * (sB / D + 2) = D * (sB / D) + 2 * D := by ring
        omega
      omega
    have hrem_ne' : (4 * ppSum 5 b * ppSum p3 c * ppSum p4 d) %
        (2 * (3 * 5 ^ b * p3 ^ c * p4 ^ d) - 4 * ppSum 5 b * ppSum p3 c * ppSum p4 d) ≠ 0 := hrem_ne
    have hq_eq' : q = (4 * ppSum 5 b * ppSum p3 c * ppSum p4 d) /
        (2 * (3 * 5 ^ b * p3 ^ c * p4 ^ d) - 4 * ppSum 5 b * ppSum p3 c * ppSum p4 d) + 1 := hq_eq
    simp only [hrem_ne', ↓reduceIte, ← hq_eq', show ¬ (q ≤ p4) by omega] at hok2
    cases hf2 : f2 with
    | none => simp [hf2] at hok2
    | some pair =>
      rcases pair with ⟨e0, f⟩
      simp only [hf2] at hok2
      cases e0 with
      | zero =>
        simp only [decide_eq_true_eq] at hok2
        rcases hq.eq_one_or_self_of_dvd f (Nat.dvd_of_mod_eq_zero hok2.2.2) with h1 | h2 <;> omega
      | succ e0' =>
        cases f with
        | succ f' => simp at hok2
        | zero =>
          simp only [decide_eq_true_eq] at hok2
          obtain ⟨he0_ge, hdef_prev, hab_e0, hE_ok⟩ := hok2
          have he_ge : e0' + 1 ≤ e := by
            by_contra! hlt
            have hle : e ≤ e0' := by omega
            have hmono := ppSum_mono_exp hq.two_le hle
            have h1 : sB * ppSum q e * q ^ e0' ≤ sB * ppSum q e0' * q ^ e := by
              calc sB * ppSum q e * q ^ e0' = sB * (ppSum q e * q ^ e0') := by ring
                _ ≤ sB * (ppSum q e0' * q ^ e) := Nat.mul_le_mul_left sB hmono
                _ = sB * ppSum q e0' * q ^ e := by ring
            have h2 : sB * ppSum q e0' * q ^ e < 2 * B * q ^ e0' * q ^ e :=
              Nat.mul_lt_mul_of_pos_right hdef_prev (pow_pos hq.pos e)
            have h3 : 2 * (B * q ^ e) * q ^ e0' = 2 * B * q ^ e0' * q ^ e := by ring
            have h4 : 2 * (B * q ^ e) * q ^ e0' < sB * ppSum q e * q ^ e0' :=
              Nat.mul_lt_mul_of_pos_right hmab (pow_pos hq.pos e0')
            omega
          have he_eq : e = e0' + 1 := by
            by_contra hne
            have hgt : e0' + 1 < e := by omega
            have hmem : B * q ^ (e0' + 1) ∈ (B * q ^ e).properDivisors := Nat.mem_properDivisors.mpr
              ⟨Nat.mul_dvd_mul_left B (pow_dvd_pow q hgt.le),
               Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hq.one_lt hgt) hBpos⟩
            have hdef := (defic_iff_nat (mul_pos hBpos (pow_pos hq.pos _))).mp (hprim _ hmem)
            have hsig := sigma_five_primes hp3 hp4 hq h3 h4 h5 (b := b) (c := c) (d := d) (e := e0' + 1)
            change sigma 1 (B * q ^ (e0' + 1)) < 2 * (B * q ^ (e0' + 1)) at hdef
            rw [hsig] at hdef
            change sB * ppSum q (e0' + 1) < 2 * (B * q ^ (e0' + 1)) at hdef
            dsimp only [B, sB] at hdef
            linarith [hab_e0]
          subst he_eq
          rw [hsigm]
          simpa [B, sB, mul_assoc] using hE_ok

set_option maxHeartbeats 800000 in
lemma Cert.sound {p3 p4 b0 c0 d0 q0 q1 b c d q e : ℕ}
    {b1 c1 d1 : Option ℕ} {cert : Cert}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hq : q.Prime)
    (h3 : 5 < p3) (h4 : p3 < p4) (h5 : p4 < q)
    (hb_lo : b0 ≤ b) (hb_hi : leOpt b b1)
    (hc_lo : c0 ≤ c) (hc_hi : leOpt c c1)
    (hd_lo : d0 ≤ d) (hd_hi : leOpt d d1)
    (hq_lo : q0 ≤ q) (hq_hi : q ≤ q1) (he : 1 ≤ e)
    (hb_even : b % 2 = 0)
    (hab : (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).properDivisors, x.Deficient)
    (hok : Cert.ok p3 p4 b0 b1 c0 c1 d0 d1 q0 q1 cert = true) :
    30 ≤ sigma 1 (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) -
      2 * (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) ∨
    (sigma 1 (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) -
      2 * (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e)) % 3 = 0 := by
  have hmpos : 0 < 3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e := by
    have := hp3.pos; have := hp4.pos; have := hq.pos; positivity
  have hsigm := sigma_five_primes hp3 hp4 hq h3 h4 h5 (b := b) (c := c) (d := d) (e := e)
  have hmab : 3 * (5 ^ b * p3 ^ c * p4 ^ d * q ^ e) <
      2 * (ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e) := by
    have h1 := (abund_iff_nat hmpos).mp hab
    rw [hsigm] at h1
    linarith
  have hup_mul : ∀ {b1' c1' d1' : Option ℕ}, leOpt b b1' → leOpt c c1' → leOpt d d1' →
      ∀ (q_bd : ℕ), 2 ≤ q_bd → q_bd ≤ q →
      ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e *
        (hiDen 5 b1' * hiDen p3 c1' * hiDen p4 d1' * (q_bd - 1)) ≤
      hiNum 5 b1' * hiNum p3 c1' * hiNum p4 d1' * q_bd *
        (5 ^ b * p3 ^ c * p4 ^ d * q ^ e) := by
    intro b1' c1' d1' hb_hi' hc_hi' hd_hi' q_bd hqbd2 hqbd_le
    have h5u := ppSum_le_hi (p := 5) (a := b) (by decide) hb_hi'
    have h3u := ppSum_le_hi (p := p3) (a := c) hp3.two_le hc_hi'
    have h4u := ppSum_le_hi (p := p4) (a := d) hp4.two_le hd_hi'
    have hqu : ppSum q e * (q_bd - 1) ≤ q_bd * q ^ e := by
      have hqlim := (ppSum_lt_lim (p := q) (a := e) hq.two_le).le
      have hq1 : q * (q_bd - 1) ≤ q_bd * (q - 1) := by
        zify [(show 1 ≤ q_bd by omega), (show 1 ≤ q by omega)]; nlinarith
      have hpos : 0 < q - 1 := by have := hq.two_le; omega
      apply Nat.le_of_mul_le_mul_right _ hpos
      calc ppSum q e * (q_bd - 1) * (q - 1) = (ppSum q e * (q - 1)) * (q_bd - 1) := by ring
        _ ≤ (q * q ^ e) * (q_bd - 1) := Nat.mul_le_mul_right _ hqlim
        _ = (q * (q_bd - 1)) * q ^ e := by ring
        _ ≤ (q_bd * (q - 1)) * q ^ e := Nat.mul_le_mul_right _ hq1
        _ = q_bd * q ^ e * (q - 1) := by ring
    have h12 := Nat.mul_le_mul h5u h3u
    have h34 := Nat.mul_le_mul h4u hqu
    have h1234 := Nat.mul_le_mul h12 h34
    linarith [h1234]
  induction cert generalizing b0 b1 c0 c1 d0 d1 q0 q1 with
  | pd =>
    simp only [Cert.ok, decide_eq_true_eq] at hok
    rcases hok with hlt | ⟨hq0_2, hle⟩
    · omega
    · have hu := hup_mul hb_hi hc_hi hd_hi q0 hq0_2 hq_lo
      have hden_pos : 0 < hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * (q0 - 1) := by
        have h1 : 0 < hiDen 5 b1 := by cases b1 <;> simp [hiDen] <;> positivity
        have h2 : 0 < hiDen p3 c1 := by
          cases c1 <;> simp [hiDen]
          · have := hp3.two_le; omega
          · exact pow_pos hp3.pos _
        have h3' : 0 < hiDen p4 d1 := by
          cases d1 <;> simp [hiDen]
          · have := hp4.two_le; omega
          · exact pow_pos hp4.pos _
        have h4' : 0 < q0 - 1 := by omega
        positivity
      have hcontra1 : 3 * (5 ^ b * p3 ^ c * p4 ^ d * q ^ e) *
          (hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * (q0 - 1)) <
          2 * (ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e) *
          (hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * (q0 - 1)) :=
        Nat.mul_lt_mul_of_pos_right hmab hden_pos
      have hcontra2 : 2 * (ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e) *
          (hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * (q0 - 1)) ≤
          3 * (5 ^ b * p3 ^ c * p4 ^ d * q ^ e) *
          (hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * (q0 - 1)) := by
        have h2u := Nat.mul_le_mul_left 2 hu
        have h2l := Nat.mul_le_mul_right (5 ^ b * p3 ^ c * p4 ^ d * q ^ e) hle
        linarith
      omega
  | pb =>
    simp only [Cert.ok, decide_eq_true_eq] at hok
    let B0 := 3 * 5 ^ b0 * p3 ^ c0 * p4 ^ d0
    have hB0pos : 0 < B0 := by have := hp3.pos; have := hp4.pos; positivity
    have hB0dvd : B0 ∣ 3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e := by
      have h1 : B0 ∣ 3 * 5 ^ b * p3 ^ c * p4 ^ d := by
        exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 3 (pow_dvd_pow 5 hb_lo))
          (pow_dvd_pow p3 hc_lo)) (pow_dvd_pow p4 hd_lo)
      exact h1.trans (dvd_mul_right _ _)
    have hB0lt : B0 < 3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e := by
      have hle : B0 ≤ 3 * 5 ^ b * p3 ^ c * p4 ^ d :=
        Nat.le_of_dvd (by have := hp3.pos; have := hp4.pos; positivity)
          (Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 3 (pow_dvd_pow 5 hb_lo))
            (pow_dvd_pow p3 hc_lo)) (pow_dvd_pow p4 hd_lo))
      have hqgt : 1 < q ^ e := one_lt_pow₀ hq.one_lt (by omega)
      nlinarith
    have hdef := (defic_iff_nat hB0pos).mp (hprim B0 (Nat.mem_properDivisors.mpr ⟨hB0dvd, hB0lt⟩))
    rw [sigma_four_primes hp3 hp4 h3 h4] at hdef
    dsimp only [B0] at hdef
    linarith
  | tq q1' sub ih =>
    simp only [Cert.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, hq1'_1, hle⟩, hsub⟩ := hok
    have hq_le' : q ≤ q1' := by
      by_contra! hgt
      have hq_ge : q1' + 1 ≤ q := hgt
      have hu := hup_mul hb_hi hc_hi hd_hi (q1' + 1) (by omega) hq_ge
      simp only [Nat.add_sub_cancel] at hu
      have hden_pos : 0 < hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * q1' := by
        have h1 : 0 < hiDen 5 b1 := by cases b1 <;> simp [hiDen] <;> positivity
        have h2 : 0 < hiDen p3 c1 := by
          cases c1 <;> simp [hiDen]
          · have := hp3.two_le; omega
          · exact pow_pos hp3.pos _
        have h3' : 0 < hiDen p4 d1 := by
          cases d1 <;> simp [hiDen]
          · have := hp4.two_le; omega
          · exact pow_pos hp4.pos _
        positivity
      have hcontra1 := Nat.mul_lt_mul_of_pos_right hmab hden_pos
      have h2u := Nat.mul_le_mul_left 2 hu
      have h2l := Nat.mul_le_mul_right (5 ^ b * p3 ^ c * p4 ^ d * q ^ e) hle
      linarith
    exact ih hb_lo hb_hi hc_lo hc_hi hd_lo hd_hi hq_lo hq_le' hsub
  | pcs fs sub ih =>
    simp only [Cert.ok] at hok
    cases hcp : checkPcs q1 fs with
    | none => simp [hcp] at hok
    | some q1' =>
      simp only [hcp] at hok
      exact ih hb_lo hb_hi hc_lo hc_hi hd_lo hd_hi hq_lo (checkPcs_sound hq hq_hi hcp) hok
  | pt subLo subHi ihLo ihHi =>
    simp only [Cert.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, hlo⟩, hhi⟩ := hok
    by_cases hqe : q = q1
    · exact ihHi hb_lo hb_hi hc_lo hc_hi hd_lo hd_hi (by omega) hq_hi hhi
    · exact ihLo hb_lo hb_hi hc_lo hc_hi hd_lo hd_hi hq_lo (by omega) hlo
  | sp axis subEq subGt ihEq ihGt =>
    simp only [Cert.ok] at hok
    split_ifs at hok with hax0 hax1
    · simp only [Bool.and_eq_true] at hok
      by_cases hbe : b = b0
      · exact ihEq hb_lo (by simp [leOpt, hbe]) hc_lo hc_hi hd_lo hd_hi hq_lo hq_hi hok.1
      · exact ihGt (by omega) hb_hi hc_lo hc_hi hd_lo hd_hi hq_lo hq_hi hok.2
    · simp only [Bool.and_eq_true] at hok
      by_cases hce : c = c0
      · exact ihEq hb_lo hb_hi hc_lo (by simp [leOpt, hce]) hd_lo hd_hi hq_lo hq_hi hok.1
      · exact ihGt hb_lo hb_hi (by omega) hc_hi hd_lo hd_hi hq_lo hq_hi hok.2
    · simp only [Bool.and_eq_true] at hok
      by_cases hde : d = d0
      · exact ihEq hb_lo hb_hi hc_lo hc_hi hd_lo (by simp [leOpt, hde]) hq_lo hq_hi hok.1
      · exact ihGt hb_lo hb_hi hc_lo hc_hi (by omega) hd_hi hq_lo hq_hi hok.2
  | ld eMin f2 =>
    simp only [Cert.ok, Bool.and_eq_true] at hok
    obtain ⟨hdom, hfix⟩ := hok
    have he_ge_eMin : eMin ≤ e ∧
        3 * (5 ^ b0 * p3 ^ c0 * p4 ^ d0 * q ^ eMin) <
        2 * (ppSum 5 b0 * ppSum p3 c0 * ppSum p4 d0 * ppSum q eMin) := by
      split_ifs at hdom with he1
      · subst he1
        simp only [decide_eq_true_eq] at hdom
        have hpp1 : ppSum q 1 = q + 1 := by
          rw [ppSum_eq_sigma hq, sigma_one_apply_prime_pow hq]
          simp [Finset.sum_range_succ, add_comm]
        refine ⟨he, ?_⟩
        rw [pow_one, hpp1]
        have hq_anti : (q1 + 1) * q ≤ (q + 1) * q1 := by nlinarith
        have hpos : 0 < q1 := hdom.1
        apply Nat.lt_of_mul_lt_mul_right (a := q1)
        calc 3 * (5 ^ b0 * p3 ^ c0 * p4 ^ d0 * q) * q1
            = 3 * (5 ^ b0 * p3 ^ c0 * p4 ^ d0 * q1) * q := by ring
          _ < 2 * (ppSum 5 b0 * ppSum p3 c0 * ppSum p4 d0 * (q1 + 1)) * q :=
              Nat.mul_lt_mul_of_pos_right hdom.2 hq.pos
          _ = 2 * (ppSum 5 b0 * ppSum p3 c0 * ppSum p4 d0) * ((q1 + 1) * q) := by ring
          _ ≤ 2 * (ppSum 5 b0 * ppSum p3 c0 * ppSum p4 d0) * ((q + 1) * q1) :=
              Nat.mul_le_mul_left _ hq_anti
          _ = 2 * (ppSum 5 b0 * ppSum p3 c0 * ppSum p4 d0 * (q + 1)) * q1 := by ring
      · simp only [decide_eq_true_eq] at hdom
        obtain ⟨he2, hq01, hq1_2, hup_e, hlo_e⟩ := hdom
        have hqq1 : q = q1 := by omega
        subst hqq1
        have he_ge : eMin ≤ e := by
          by_contra! hlt
          have hle : e ≤ eMin - 1 := by omega
          have h5u := ppSum_le_hi (p := 5) (a := b) (by decide) hb_hi
          have h3u := ppSum_le_hi (p := p3) (a := c) hp3.two_le hc_hi
          have h4u := ppSum_le_hi (p := p4) (a := d) hp4.two_le hd_hi
          have hqu := ppSum_mono_exp (p := q) hq.two_le hle
          have h1234 := Nat.mul_le_mul (Nat.mul_le_mul h5u h3u) (Nat.mul_le_mul h4u hqu)
          have hden_pos : 0 < hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * q ^ (eMin - 1) := by
            have h1 : 0 < hiDen 5 b1 := by cases b1 <;> simp [hiDen] <;> positivity
            have h2 : 0 < hiDen p3 c1 := by
              cases c1 <;> simp [hiDen]
              · have := hp3.two_le; omega
              · exact pow_pos hp3.pos _
            have h3' : 0 < hiDen p4 d1 := by
              cases d1 <;> simp [hiDen]
              · have := hp4.two_le; omega
              · exact pow_pos hp4.pos _
            have h4' : 0 < q ^ (eMin - 1) := pow_pos hq.pos _
            positivity
          have hc1 := Nat.mul_lt_mul_of_pos_right hmab hden_pos
          have hc2 := Nat.mul_le_mul_left 2 h1234
          have hc3 := Nat.mul_le_mul_right (5 ^ b * p3 ^ c * p4 ^ d * q ^ e) hup_e
          linarith
        exact ⟨he_ge, hlo_e⟩
    have hbcd_eq : b = b0 ∧ c = c0 ∧ d = d0 := by
      by_contra hne
      have hstrict : b0 < b ∨ c0 < c ∨ d0 < d := by omega
      let m0 := 3 * 5 ^ b0 * p3 ^ c0 * p4 ^ d0 * q ^ eMin
      have hm0pos : 0 < m0 := by have := hp3.pos; have := hp4.pos; have := hq.pos; positivity
      have hm0dvd : m0 ∣ 3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e :=
        Nat.mul_dvd_mul
          (Nat.mul_dvd_mul
            (Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 3 (pow_dvd_pow 5 hb_lo)) (pow_dvd_pow p3 hc_lo))
            (pow_dvd_pow p4 hd_lo))
          (pow_dvd_pow q he_ge_eMin.1)
      have hm0lt : m0 < 3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e := by
        have h1le : 3 * 5 ^ b0 ≤ 3 * 5 ^ b := Nat.mul_le_mul_left 3 (pow_le_pow_right₀ (by decide) hb_lo)
        have h2le : p3 ^ c0 ≤ p3 ^ c := pow_le_pow_right₀ hp3.one_lt.le hc_lo
        have h3le : p4 ^ d0 ≤ p4 ^ d := pow_le_pow_right₀ hp4.one_lt.le hd_lo
        have h4le : q ^ eMin ≤ q ^ e := pow_le_pow_right₀ hq.one_lt.le he_ge_eMin.1
        have hp3_pos : 0 < p3 ^ c0 := pow_pos hp3.pos _
        have hp4_pos : 0 < p4 ^ d0 := pow_pos hp4.pos _
        have hq_pos : 0 < q ^ eMin := pow_pos hq.pos _
        rcases hstrict with hsb | hsc | hsd
        · have h1lt : 3 * 5 ^ b0 < 3 * 5 ^ b :=
            Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by decide) hsb) (by decide)
          have ha := Nat.mul_lt_mul_of_lt_of_le' h1lt h2le hp3_pos
          have hb' := Nat.mul_lt_mul_of_lt_of_le' ha h3le hp4_pos
          exact Nat.mul_lt_mul_of_lt_of_le' hb' h4le hq_pos
        · have h2lt : p3 ^ c0 < p3 ^ c := Nat.pow_lt_pow_right hp3.one_lt hsc
          have ha := Nat.mul_lt_mul_of_le_of_lt h1le h2lt (by positivity)
          have hb' := Nat.mul_lt_mul_of_lt_of_le' ha h3le hp4_pos
          exact Nat.mul_lt_mul_of_lt_of_le' hb' h4le hq_pos
        · have h3lt : p4 ^ d0 < p4 ^ d := Nat.pow_lt_pow_right hp4.one_lt hsd
          have ha := Nat.mul_le_mul h1le h2le
          have hb' := Nat.mul_lt_mul_of_le_of_lt ha h3lt (by positivity)
          exact Nat.mul_lt_mul_of_lt_of_le' hb' h4le hq_pos
      have hdef := (defic_iff_nat hm0pos).mp (hprim m0 (Nat.mem_properDivisors.mpr ⟨hm0dvd, hm0lt⟩))
      rw [sigma_five_primes hp3 hp4 hq h3 h4 h5] at hdef
      dsimp only [m0] at hdef
      linarith [he_ge_eMin.2]
    rcases hbcd_eq with ⟨rfl, rfl, rfl⟩
    exact checkFixedB_sound hp3 hp4 hq h3 h4 h5 he hb_even hab hprim hfix

end Cert3D

section Rank4

/-- Fast algebraic witness checker for pseudoperfectness of 3 * 5^b * 7^c * p4^d. -/
def checkWitness4 (p4 b c d : ℕ) (ws : List ℕ) : Bool :=
  let n := 3 * 5 ^ b * 7 ^ c * p4 ^ d
  let s := 4 * ppSum 5 b * ppSum 7 c * ppSum p4 d
  decide (ws.Nodup) &&
  ws.all (fun x => decide (x ∣ n ∧ x < n)) &&
  decide (ws.sum + 2 * n = s)

lemma pseudoperfect_of_witness4 {p4 b c d : ℕ} {ws : List ℕ}
    (hp4 : p4.Prime) (h7 : 7 < p4)
    (hchk : checkWitness4 p4 b c d ws = true) :
    (3 * 5 ^ b * 7 ^ c * p4 ^ d).Pseudoperfect := by
  unfold checkWitness4 at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨hnd, hsub⟩, hsum⟩ := hchk
  let n := 3 * 5 ^ b * 7 ^ c * p4 ^ d
  have hnpos : 0 < n := by have := hp4.pos; positivity
  have hsig : sigma 1 n = 4 * ppSum 5 b * ppSum 7 c * ppSum p4 d :=
    sigma_four_primes (by decide) hp4 (by decide) h7
  have hsubF : ws.toFinset ⊆ n.properDivisors := by
    intro x hx
    exact Nat.mem_properDivisors.mpr (hsub x (List.mem_toFinset.mp hx))
  apply pseudoperfect_of_excess hnpos hsubF
  have hsumF : ∑ x ∈ ws.toFinset, x = ws.sum := by simpa using List.sum_toFinset id hnd
  dsimp [excess]
  rw [← Nat.cast_sum, hsumF, hsig]
  omega

/-- Helper: if n = 3 * 5^b * 7^c * p4^d is primitive abundant and (b0,c0,d0) is already
    abundant and coordinatewise <= (b,c,d), then (b,c,d) = (b0,c0,d0). -/
lemma eq_of_dom4 {p4 b c d b0 c0 d0 : ℕ} (hp4 : p4.Prime) (h7 : 7 < p4)
    (hb : b0 ≤ b) (hc : c0 ≤ c) (hd : d0 ≤ d)
    (hprim : ∀ x ∈ (3 * 5 ^ b * 7 ^ c * p4 ^ d).properDivisors, x.Deficient)
    (hab0 : 3 * (5 ^ b0 * 7 ^ c0 * p4 ^ d0) < 2 * (ppSum 5 b0 * ppSum 7 c0 * ppSum p4 d0)) :
    b = b0 ∧ c = c0 ∧ d = d0 := by
  by_contra hne
  have hstrict : b0 < b ∨ c0 < c ∨ d0 < d := by omega
  let m0 := 3 * 5 ^ b0 * 7 ^ c0 * p4 ^ d0
  have hm0pos : 0 < m0 := by have := hp4.pos; positivity
  have hm0dvd : m0 ∣ 3 * 5 ^ b * 7 ^ c * p4 ^ d :=
    Nat.mul_dvd_mul
      (Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 3 (pow_dvd_pow 5 hb)) (pow_dvd_pow 7 hc))
      (pow_dvd_pow p4 hd)
  have hm0lt : m0 < 3 * 5 ^ b * 7 ^ c * p4 ^ d := by
    have h1le : 3 * 5 ^ b0 ≤ 3 * 5 ^ b := Nat.mul_le_mul_left 3 (pow_le_pow_right₀ (by decide) hb)
    have h2le : 7 ^ c0 ≤ 7 ^ c := pow_le_pow_right₀ (by decide) hc
    have h3le : p4 ^ d0 ≤ p4 ^ d := pow_le_pow_right₀ hp4.one_lt.le hd
    have h7_pos : 0 < 7 ^ c0 := pow_pos (by decide) _
    have hp4_pos : 0 < p4 ^ d0 := pow_pos hp4.pos _
    rcases hstrict with hsb | hsc | hsd
    · have h1lt : 3 * 5 ^ b0 < 3 * 5 ^ b :=
        Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by decide) hsb) (by decide)
      exact Nat.mul_lt_mul_of_lt_of_le' (Nat.mul_lt_mul_of_lt_of_le' h1lt h2le h7_pos) h3le hp4_pos
    · have h2lt : 7 ^ c0 < 7 ^ c := Nat.pow_lt_pow_right (by decide) hsc
      exact Nat.mul_lt_mul_of_lt_of_le' (Nat.mul_lt_mul_of_le_of_lt h1le h2lt (by positivity)) h3le hp4_pos
    · have h3lt : p4 ^ d0 < p4 ^ d := Nat.pow_lt_pow_right hp4.one_lt hsd
      exact Nat.mul_lt_mul_of_le_of_lt (Nat.mul_le_mul h1le h2le) h3lt (by positivity)
  have hdef := (defic_iff_nat hm0pos).mp (hprim m0 (Nat.mem_properDivisors.mpr ⟨hm0dvd, hm0lt⟩))
  rw [sigma_four_primes (by decide) hp4 (by decide) h7] at hdef
  dsimp only [m0] at hdef
  linarith

lemma not_ab4_of_box {p4 b c d : ℕ} {b1 c1 d1 : Option ℕ} (hp4 : p4.Prime) (h7 : 7 < p4)
    (hb : leOpt b b1) (hc : leOpt c c1) (hd : leOpt d d1)
    (hlim : 2 * (hiNum 5 b1 * hiNum 7 c1 * hiNum p4 d1) ≤
            3 * (hiDen 5 b1 * hiDen 7 c1 * hiDen p4 d1)) :
    ¬ (3 * 5 ^ b * 7 ^ c * p4 ^ d).Abundant := by
  intro hab
  have hnpos : 0 < 3 * 5 ^ b * 7 ^ c * p4 ^ d := by have := hp4.pos; positivity
  have h1 := (abund_iff_nat hnpos).mp hab
  rw [sigma_four_primes (by decide) hp4 (by decide) h7] at h1
  have hu5 := ppSum_le_hi (p := 5) (a := b) (by decide) hb
  have hu7 := ppSum_le_hi (p := 7) (a := c) (by decide) hc
  have hu4 := ppSum_le_hi (p := p4) (a := d) hp4.two_le hd
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul hu5 hu7) hu4
  have hden_pos : 0 < hiDen 5 b1 * hiDen 7 c1 * hiDen p4 d1 := by
    have h1' : 0 < hiDen 5 b1 := by cases b1 <;> simp [hiDen] <;> positivity
    have h2' : 0 < hiDen 7 c1 := by cases c1 <;> simp [hiDen] <;> positivity
    have h3' : 0 < hiDen p4 d1 := by
      cases d1 <;> simp [hiDen]
      · have := hp4.two_le; omega
      · exact pow_pos hp4.pos _
    positivity
  have hlt : 3 * (5 ^ b * 7 ^ c * p4 ^ d) * (hiDen 5 b1 * hiDen 7 c1 * hiDen p4 d1) <
      2 * (ppSum 5 b * ppSum 7 c * ppSum p4 d) * (hiDen 5 b1 * hiDen 7 c1 * hiDen p4 d1) :=
    Nat.mul_lt_mul_of_pos_right (by linarith) hden_pos
  have hle1 : 2 * (ppSum 5 b * ppSum 7 c * ppSum p4 d) * (hiDen 5 b1 * hiDen 7 c1 * hiDen p4 d1) ≤
      2 * (hiNum 5 b1 * hiNum 7 c1 * hiNum p4 d1) * (5 ^ b * 7 ^ c * p4 ^ d) := by
    linarith [Nat.mul_le_mul_left 2 hprod]
  have hle2 := Nat.mul_le_mul_right (5 ^ b * 7 ^ c * p4 ^ d) hlim
  linarith

lemma rank4_pseudoperfect {p4 b c d : ℕ}
    (hp4_mem : p4 ∈ ({11, 13, 17, 19, 23, 29, 31} : Finset ℕ))
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hab : (3 * 5 ^ b * 7 ^ c * p4 ^ d).Abundant)
    (hprim : ∀ x ∈ (3 * 5 ^ b * 7 ^ c * p4 ^ d).properDivisors, x.Deficient) :
    (3 * 5 ^ b * 7 ^ c * p4 ^ d).Pseudoperfect := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp4_mem
  rcases hp4_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- p4 = 11: minimal abundant (2,1,1), (1,2,1), (1,1,2)
    have hp4 : Nat.Prime 11 := by decide
    by_cases hb2 : 2 ≤ b
    · obtain ⟨rfl, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) hb2 hc hd hprim (by decide)
      exact pseudoperfect_of_witness4 hp4 (by decide) (ws := [7,11,15,21,25,33,35,55,75,77]) (by decide)
    · have hb1 : b = 1 := by omega
      subst hb1
      by_cases hc2 : 2 ≤ c
      · obtain ⟨_, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) le_rfl hc2 hd hprim (by decide)
        exact pseudoperfect_of_witness4 hp4 (by decide) (ws := [1,3,5,7,15,21,33,35,49,77]) (by decide)
      · have hc1 : c = 1 := by omega
        subst hc1
        by_cases hd2 : 2 ≤ d
        · obtain ⟨_, _, rfl⟩ := eq_of_dom4 hp4 (by decide) le_rfl le_rfl hd2 hprim (by decide)
          exact pseudoperfect_of_witness4 hp4 (by decide) (ws := [1,3,7,11,15,21,33,35]) (by decide)
        · have hd1 : d = 1 := by omega
          subst hd1
          exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := some 1) (c1 := some 1) (d1 := some 1)
            le_rfl le_rfl le_rfl (by decide))
  · -- p4 = 13: minimal abundant (2,1,1), (1,2,1)
    have hp4 : Nat.Prime 13 := by decide
    by_cases hb2 : 2 ≤ b
    · obtain ⟨rfl, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) hb2 hc hd hprim (by decide)
      exact pseudoperfect_of_witness4 hp4 (by decide) (ws := [3,5,7,13,15,21,25,35,39,75]) (by decide)
    · have hb1 : b = 1 := by omega
      subst hb1
      by_cases hc2 : 2 ≤ c
      · obtain ⟨_, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) le_rfl hc2 hd hprim (by decide)
        exact pseudoperfect_of_witness4 hp4 (by decide) (ws := [3,5,13,21]) (by decide)
      · have hc1 : c = 1 := by omega
        subst hc1
        exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := some 1) (c1 := some 1) (d1 := none)
          le_rfl le_rfl trivial (by decide))
  · -- p4 = 17: minimal abundant (2,1,1)
    have hp4 : Nat.Prime 17 := by decide
    by_cases hb2 : 2 ≤ b
    · obtain ⟨rfl, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) hb2 hc hd hprim (by decide)
      exact pseudoperfect_of_witness4 hp4 (by decide) (ws := [1,5]) (by decide)
    · have hb1 : b = 1 := by omega
      subst hb1
      exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := some 1) (c1 := none) (d1 := none)
        le_rfl trivial trivial (by decide))
  · -- p4 = 19: minimal abundant (3,1,1), (2,2,1)
    have hp4 : Nat.Prime 19 := by decide
    by_cases hb3 : 3 ≤ b
    · obtain ⟨rfl, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) hb3 hc hd hprim (by decide)
      exact pseudoperfect_of_witness4 hp4 (by decide) (ws := [3,7,15,19,21,25]) (by decide)
    · by_cases hb2 : b = 2
      · subst hb2
        by_cases hc2 : 2 ≤ c
        · obtain ⟨_, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) le_rfl hc2 hd hprim (by decide)
          exact pseudoperfect_of_witness4 hp4 (by decide)
            (ws := [5,15,19,21,25,35,49,57,75,95,105,133,147,245,285,399]) (by decide)
        · have hc1 : c = 1 := by omega
          subst hc1
          exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := some 2) (c1 := some 1) (d1 := none)
            le_rfl le_rfl trivial (by decide))
      · have hb1 : b = 1 := by omega
        subst hb1
        exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := some 1) (c1 := none) (d1 := none)
          le_rfl trivial trivial (by decide))
  · -- p4 = 23: minimal abundant (2,2,1)
    have hp4 : Nat.Prime 23 := by decide
    by_cases hbc : 2 ≤ b ∧ 2 ≤ c
    · obtain ⟨rfl, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) hbc.1 hbc.2 hd hprim (by decide)
      exact pseudoperfect_of_witness4 hp4 (by decide)
        (ws := [3,5,15,21,23,25,35,49,69,75,115,147]) (by decide)
    · by_cases hb1 : b = 1
      · subst hb1
        exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := some 1) (c1 := none) (d1 := none)
          le_rfl trivial trivial (by decide))
      · have hc1 : c = 1 := by omega
        subst hc1
        exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := none) (c1 := some 1) (d1 := none)
          trivial le_rfl trivial (by decide))
  · -- p4 = 29: minimal abundant (3,2,1)
    have hp4 : Nat.Prime 29 := by decide
    by_cases hbc : 3 ≤ b ∧ 2 ≤ c
    · obtain ⟨rfl, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) hbc.1 hbc.2 hd hprim (by decide)
      exact pseudoperfect_of_witness4 hp4 (by decide)
        (ws := [5,7,15,21,25,29,35,49,75,87,105,125,145,147,175,245]) (by decide)
    · by_cases hb2 : b ≤ 2
      · exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := some 2) (c1 := none) (d1 := none)
          hb2 trivial trivial (by decide))
      · have hc1 : c = 1 := by omega
        subst hc1
        exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := none) (c1 := some 1) (d1 := none)
          trivial le_rfl trivial (by decide))
  · -- p4 = 31: minimal abundant (4,2,1), (3,3,1), (3,2,2)
    have hp4 : Nat.Prime 31 := by decide
    by_cases hb2 : b ≤ 2
    · exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := some 2) (c1 := none) (d1 := none)
        hb2 trivial trivial (by decide))
    · by_cases hc1 : c = 1
      · subst hc1
        exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := none) (c1 := some 1) (d1 := none)
          trivial le_rfl trivial (by decide))
      · by_cases hb4 : 4 ≤ b
        · obtain ⟨rfl, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) hb4 (show 2 ≤ c by omega) hd hprim (by decide)
          exact pseudoperfect_of_witness4 hp4 (by decide)
            (ws := [5,7,21,25,31,35,75,93,105,125,147,155,175,217,245,465]) (by decide)
        · have hb3 : b = 3 := by omega
          subst hb3
          by_cases hc3 : 3 ≤ c
          · obtain ⟨_, rfl, rfl⟩ := eq_of_dom4 hp4 (by decide) le_rfl hc3 hd hprim (by decide)
            exact pseudoperfect_of_witness4 hp4 (by decide)
              (ws := [1,3,5,7,15,25,31,35,49,75,93,105,125,147,155,175,217,245,343,465,525,651,735,775,875,1029,1085,1225,1519,1715]) (by decide)
          · have hc2 : c = 2 := by omega
            subst hc2
            by_cases hd2 : 2 ≤ d
            · obtain ⟨_, _, rfl⟩ := eq_of_dom4 hp4 (by decide) le_rfl le_rfl hd2 hprim (by decide)
              exact pseudoperfect_of_witness4 hp4 (by decide)
                (ws := [1,3,7,21,25,31,35,49,93,105,125,147,155,175,217,245,375,465]) (by decide)
            · have hd1 : d = 1 := by omega
              subst hd1
              exact absurd hab (not_ab4_of_box hp4 (by decide) (b1 := some 3) (c1 := some 2) (d1 := some 1)
                le_rfl le_rfl le_rfl (by decide))

end Rank4

section CoreAll19

def properDivsSum (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d

lemma properDivsSum_eq_sigma_sub {n : ℕ} :
    properDivsSum n = sigma 1 n - n := by
  have h : sigma 1 n = properDivsSum n + n := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    rfl
  omega

lemma properDivsSum_ratio_mono_4 {p3 p4 b0 c0 d0 b c d : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (h3 : 5 < p3) (h4 : p3 < p4)
    (hb : b0 ≤ b) (hc : c0 ≤ c) (hd : d0 ≤ d) :
    properDivsSum (3 * 5 ^ b0 * p3 ^ c0 * p4 ^ d0) * (3 * 5 ^ b * p3 ^ c * p4 ^ d) ≤
    properDivsSum (3 * 5 ^ b * p3 ^ c * p4 ^ d) * (3 * 5 ^ b0 * p3 ^ c0 * p4 ^ d0) := by
  let n0 := 3 * 5 ^ b0 * p3 ^ c0 * p4 ^ d0
  let n := 3 * 5 ^ b * p3 ^ c * p4 ^ d
  have hs0 : sigma 1 n0 = 4 * ppSum 5 b0 * ppSum p3 c0 * ppSum p4 d0 := sigma_four_primes hp3 hp4 h3 h4
  have hs1 : sigma 1 n = 4 * ppSum 5 b * ppSum p3 c * ppSum p4 d := sigma_four_primes hp3 hp4 h3 h4
  have h5 := ppSum_mono_exp (p := 5) (by decide) hb
  have h3' := ppSum_mono_exp (p := p3) hp3.two_le hc
  have h4' := ppSum_mono_exp (p := p4) hp4.two_le hd
  have hmul : sigma 1 n0 * n ≤ sigma 1 n * n0 := by
    rw [hs0, hs1]
    have h12 := Nat.mul_le_mul h5 h3'
    have h123 := Nat.mul_le_mul h12 h4'
    have h123' := Nat.mul_le_mul_left 12 h123
    dsimp only [n0, n]
    linarith
  have hge0 : n0 ≤ sigma 1 n0 := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
  have hge1 : n ≤ sigma 1 n := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
  rw [properDivsSum_eq_sigma_sub, properDivsSum_eq_sigma_sub]
  change (sigma 1 n0 - n0) * n ≤ (sigma 1 n - n) * n0
  zify [hge0, hge1]
  have hmulZ : (sigma 1 n0 : ℤ) * (n : ℤ) ≤ (sigma 1 n : ℤ) * (n0 : ℤ) := by exact_mod_cast hmul
  have heq1 : ((sigma 1 n0 : ℤ) - (n0 : ℤ)) * (n : ℤ) = (sigma 1 n0 : ℤ) * (n : ℤ) - (n0 : ℤ) * (n : ℤ) := by ring
  have heq2 : ((sigma 1 n : ℤ) - (n : ℤ)) * (n0 : ℤ) = (sigma 1 n : ℤ) * (n0 : ℤ) - (n0 : ℤ) * (n : ℤ) := by ring
  linarith

lemma properDivsSum_ratio_mono_3 {p q a0 b0 a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (h3p : 3 < p) (hpq : p < q)
    (ha : a0 ≤ a) (hb : b0 ≤ b) :
    properDivsSum (3 * p ^ a0 * q ^ b0) * (3 * p ^ a * q ^ b) ≤
    properDivsSum (3 * p ^ a * q ^ b) * (3 * p ^ a0 * q ^ b0) := by
  have h3 : Nat.Prime 3 := by decide
  have sig3 (x y : ℕ) : sigma 1 (3 * p ^ x * q ^ y) = 4 * ppSum p x * ppSum q y := by
    have hc3p : Nat.Coprime 3 (p ^ x) := ((Nat.coprime_primes h3 hp).mpr (by omega)).pow_right x
    have hcq : Nat.Coprime (3 * p ^ x) (q ^ y) :=
      (Nat.Coprime.mul_left ((Nat.coprime_primes h3 hq).mpr (by omega))
        (((Nat.coprime_primes hp hq).mpr (by omega)).pow_left x)).pow_right y
    rw [isMultiplicative_sigma.map_mul_of_coprime hcq,
        isMultiplicative_sigma.map_mul_of_coprime hc3p,
        ← ppSum_eq_sigma hp, ← ppSum_eq_sigma hq]
    have : sigma 1 3 = 4 := by decide
    rw [this]
  let n0 := 3 * p ^ a0 * q ^ b0
  let n := 3 * p ^ a * q ^ b
  have h1 := Nat.mul_le_mul (ppSum_mono_exp hp.two_le ha) (ppSum_mono_exp hq.two_le hb)
  have hmul : sigma 1 n0 * n ≤ sigma 1 n * n0 := by
    rw [sig3, sig3]
    have := Nat.mul_le_mul_left 12 h1
    dsimp only [n0, n]; linarith
  have hge0 : n0 ≤ sigma 1 n0 := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
  have hge1 : n ≤ sigma 1 n := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
  rw [properDivsSum_eq_sigma_sub, properDivsSum_eq_sigma_sub]
  change (sigma 1 n0 - n0) * n ≤ (sigma 1 n - n) * n0
  zify [hge0, hge1]
  have hmulZ : (sigma 1 n0 : ℤ) * (n : ℤ) ≤ (sigma 1 n : ℤ) * (n0 : ℤ) := by exact_mod_cast hmul
  have heq1 : ((sigma 1 n0 : ℤ) - (n0 : ℤ)) * (n : ℤ) = (sigma 1 n0 : ℤ) * (n : ℤ) - (n0 : ℤ) * (n : ℤ) := by ring
  have heq2 : ((sigma 1 n : ℤ) - (n : ℤ)) * (n0 : ℤ) = (sigma 1 n : ℤ) * (n0 : ℤ) - (n0 : ℤ) * (n : ℤ) := by ring
  linarith

/-- Coverage of [18, 449] by proper divisors of 525 = 3 * 5^2 * 7. -/
def ds525 : List ℕ := [1, 3, 5, 7, 15, 21, 25, 35, 75, 105, 175]

lemma check525_ok :
    (decide (ds525.Nodup) &&
     ds525.all (fun d => decide (d ∣ 525 ∧ d < 525)) &&
     (ivsOfList ds525).any (fun ab => decide (ab.1 ≤ 18 ∧ 449 ≤ ab.2))) = true := by
  decide

lemma rep_525 {y : ℕ} (h1 : 18 ≤ y) (h2 : y ≤ 449) :
    repNat (525 : ℕ).properDivisors y := by
  have h := check525_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨hnd, hsub⟩, ⟨ab, hab, h1', h2'⟩⟩ := h
  exact ivsOfList_sound hnd (fun d hd => Nat.mem_properDivisors.mpr (hsub d hd)) y
    ⟨ab, hab, le_trans h1' h1, le_trans h2 h2'⟩

/-- If a duplicate-free list of proper divisors has the full proper-divisor sum, it equals properDivisors. -/
lemma toFinset_eq_properDivisors_of_sum {u : ℕ} {ds : List ℕ} (hu : 0 < u)
    (hnd : ds.Nodup) (hsub : ∀ d ∈ ds, d ∣ u ∧ d < u)
    (hsum : ds.sum = properDivsSum u) :
    ds.toFinset = u.properDivisors := by
  have hsubF : ds.toFinset ⊆ u.properDivisors := fun d hd =>
    Nat.mem_properDivisors.mpr (hsub d (List.mem_toFinset.mp hd))
  have hsumF : ∑ d ∈ ds.toFinset, d = ∑ d ∈ u.properDivisors, d := by
    have h1 : ∑ d ∈ ds.toFinset, d = ds.sum := by simpa using List.sum_toFinset id hnd
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

/-- Fast explicit-list checker for HasAbsGap u C (avoids List.range u in kernel). -/
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
    rw [← hfeq]; simpa using List.sum_toFinset id (hnd.filter (fun x => decide (x < d)))
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
    rw [← hfeq]; simpa using List.sum_toFinset id (hnd.filter (fun x => decide (x < d)))
  rw [hsf]
  exact h1

def sqfree3ProperDivs (p q : ℕ) : List ℕ :=
  [1, 3, p, 3 * p, q, 3 * q, p * q]

lemma properDivsSum_sqfree3 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h3p : 3 < p) (hpq : p < q) :
    properDivsSum (3 * p * q) = 4 * (p + 1) * (q + 1) - 3 * p * q := by
  rw [properDivsSum_eq_sigma_sub]
  have h3p' : Nat.Prime 3 := by decide
  have hc3p : Nat.Coprime 3 p := (Nat.coprime_primes h3p' hp).mpr (by omega)
  have hcq : Nat.Coprime (3 * p) q :=
    Nat.Coprime.mul_left ((Nat.coprime_primes h3p' hq).mpr (by omega))
      ((Nat.coprime_primes hp hq).mpr (by omega))
  rw [isMultiplicative_sigma.map_mul_of_coprime hcq,
      isMultiplicative_sigma.map_mul_of_coprime hc3p]
  have hs3 : sigma 1 3 = 4 := by decide
  have hsp : sigma 1 p = p + 1 := by
    rw [← pow_one p, sigma_one_apply_prime_pow hp]; simp [Finset.sum_range_succ, add_comm]
  have hsq : sigma 1 q = q + 1 := by
    rw [← pow_one q, sigma_one_apply_prime_pow hq]; simp [Finset.sum_range_succ, add_comm]
  rw [hs3, hsp, hsq]

set_option maxHeartbeats 800000 in
/-- Universal single-extra-divisor trick for HasAbsGap on 3 * 5^b * q^c (q in {7, 11}, C = 2; or q = 13, b >= 2, C = 4). -/
lemma hasAbsGap_3_5_q {q C b0 b c : ℕ} (hq : q.Prime) (h5q : 5 < q) (hq15 : q < 15)
    (hb0 : 1 ≤ b0) (hb : b0 ≤ b) (hc : 1 ≤ c) (hb0_q : b0 = 1 ∨ 9 ≤ q)
    (hbase : HasAbsGap (3 * 5 ^ b0 * q) C)
    (hratio5 : 3 * 5 ^ b0 * q ≤ properDivsSum (3 * 5 ^ b0 * q) + 3 * 5 ^ (b0 + 1))
    (hratioq : 3 * 5 ^ b0 * q ≤ properDivsSum (3 * 5 ^ b0 * q) + 5 ^ (b0 - 1) * q ^ 2)
    (hsmall5 : C * 5 ≤ C + (1 + 3 + q))
    (hsmallq : C * q ≤ C + (if b0 = 1 then 1 + 3 + 5 + 15 else 1 + 3 + 5 + 15 + 25 + 75)) :
    HasAbsGap (3 * 5 ^ b * q ^ c) C := by
  have h5p : Nat.Prime 5 := by decide
  have h3p : Nat.Prime 3 := by decide
  have hbase_c : ∀ c', 1 ≤ c' → HasAbsGap (3 * 5 ^ b0 * q ^ c') C := by
    intro c' hc'
    induction c' with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hbase
      | succ k' =>
        have hprev := ih (by omega)
        let u := 3 * 5 ^ b0 * q ^ (k' + 1)
        have hu_pos : 0 < u := by have := hq.pos; positivity
        have hqu : q ∣ u := dvd_mul_of_dvd_right (dvd_pow_self q (by omega)) _
        have hmul_eq : q * u = 3 * 5 ^ b0 * q ^ (k' + 2) := by dsimp [u]; ring
        rw [← hmul_eq]
        apply HasAbsGap.mul_prime hq hu_pos hqu hprev
        · -- h_u: u <= C + sum of divisors of q*u strictly less than u
          let ex := 5 ^ (b0 - 1) * q ^ (k' + 2)
          have hex_lt : ex < u := by
            dsimp only [ex, u]
            have h5b : 5 ^ b0 = 5 * 5 ^ (b0 - 1) := by
              rw [← pow_succ', Nat.sub_add_cancel hb0]
            rw [h5b, show q ^ (k' + 2) = q * q ^ (k' + 1) by ring]
            have hpos : 0 < 5 ^ (b0 - 1) * q ^ (k' + 1) := by have := hq.pos; positivity
            nlinarith
          have hex_dvd : ex ∣ q * u := by
            rw [hmul_eq]; dsimp only [ex]
            have h1 : 5 ^ (b0 - 1) ∣ 3 * 5 ^ b0 :=
              (pow_dvd_pow 5 (Nat.sub_le b0 1)).trans (dvd_mul_left _ 3)
            exact Nat.mul_dvd_mul h1 dvd_rfl
          have hex_not_u : ¬ ex ∣ u := by
            intro h
            have hq2 : q ^ (k' + 2) ∣ 3 * 5 ^ b0 * q ^ (k' + 1) :=
              (dvd_mul_left _ _).trans h
            have hq2' : q * q ^ (k' + 1) ∣ (3 * 5 ^ b0) * q ^ (k' + 1) := by
              simpa [show q ^ (k' + 2) = q * q ^ (k' + 1) by ring] using hq2
            have hq_dvd : q ∣ 3 * 5 ^ b0 :=
              (Nat.mul_dvd_mul_iff_right (pow_pos hq.pos (k' + 1))).mp hq2'
            have hcop : Nat.Coprime q (3 * 5 ^ b0) :=
              Nat.Coprime.mul_right ((Nat.coprime_primes hq h3p).mpr (by omega))
                (((Nat.coprime_primes hq h5p).mpr (by omega)).pow_right b0)
            exact hq.not_dvd_one (hcop.dvd_of_dvd_mul_right (by simpa using hq_dvd))
          have hsub : insert ex u.properDivisors ⊆ (q * u).properDivisors.filter (· < u) := by
            intro x hx
            rw [Finset.mem_filter]
            rcases Finset.mem_insert.mp hx with rfl | hxu
            · exact ⟨Nat.mem_properDivisors.mpr ⟨hex_dvd, lt_trans hex_lt (by nlinarith [hq.one_lt])⟩, hex_lt⟩
            · obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp hxu
              exact ⟨Nat.mem_properDivisors.mpr ⟨h1.trans (dvd_mul_left u q), lt_trans h2 (by nlinarith [hq.one_lt])⟩, h2⟩
          have hex_notin : ex ∉ u.properDivisors := fun h => hex_not_u (Nat.mem_properDivisors.mp h).1
          have hsum_ge : ex + properDivsSum u ≤ ∑ x ∈ (q * u).properDivisors.filter (· < u), x := by
            have := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
            rw [Finset.sum_insert hex_notin] at this
            exact this
          have hmono := properDivsSum_ratio_mono_3 (a0 := b0) (a := b0) (b0 := 1) (b := k' + 1)
            h5p hq (by decide) h5q le_rfl (by omega)
          have hu_eq : u = (3 * 5 ^ b0 * q) * q ^ k' := by dsimp [u]; ring
          have hex_eq : ex = (5 ^ (b0 - 1) * q ^ 2) * q ^ k' := by dsimp [ex]; ring
          have hP_ge : properDivsSum (3 * 5 ^ b0 * q) * q ^ k' ≤ properDivsSum u := by
            have hpos : 0 < 3 * 5 ^ b0 * q := by have := hq.pos; positivity
            have h1 : properDivsSum (3 * 5 ^ b0 * q) * ((3 * 5 ^ b0 * q) * q ^ k') ≤
                properDivsSum u * (3 * 5 ^ b0 * q) := by simpa [← hu_eq] using hmono
            nlinarith
          have hmul_r := Nat.mul_le_mul_right (q ^ k') hratioq
          rw [← hu_eq, add_mul, ← hex_eq] at hmul_r
          omega
        · -- h_small: q | d' => q^2 <= q * d', so {1, 3, 5, 15, ...} < q * d'
          intro d' hd' hqd'
          have hqd'_ge : q ^ 2 ≤ q * d' := by
            obtain ⟨t, rfl⟩ := hqd'
            have hpos := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hd').1 hu_pos
            have ht : 1 ≤ t := by
              by_contra! h0
              have ht0 : t = 0 := by omega
              subst ht0; simp at hpos
            nlinarith
          have hqu_gt_qd' : q * d' < q * u := Nat.mul_lt_mul_of_pos_left (Nat.mem_properDivisors.mp hd').2 hq.pos
          by_cases hb1 : b0 = 1
          · simp only [hb1, ↓reduceIte] at hsmallq
            let S : Finset ℕ := {1, 3, 5, 15}
            have h15_lt : 15 < q ^ 2 := by nlinarith
            have h15_u : 15 ∣ u := by
              dsimp [u]; rw [hb1, pow_one]; exact dvd_mul_right 15 _
            have hsub : S ⊆ (q * u).properDivisors.filter (fun x => x < q * d' ∧ ¬ q ∣ x) := by
              intro x hx
              simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
              rw [Finset.mem_filter, Nat.mem_properDivisors]
              rcases hx with rfl | rfl | rfl | rfl
              · exact ⟨⟨(by decide : 1 ∣ 15).trans (h15_u.trans (dvd_mul_left u q)), by omega⟩,
                  by omega, fun h => by have := Nat.le_of_dvd (by decide) h; omega⟩
              · exact ⟨⟨(by decide : 3 ∣ 15).trans (h15_u.trans (dvd_mul_left u q)), by omega⟩,
                  by omega, fun h => by have := Nat.le_of_dvd (by decide) h; omega⟩
              · exact ⟨⟨(by decide : 5 ∣ 15).trans (h15_u.trans (dvd_mul_left u q)), by omega⟩,
                  by omega, fun h => by have := Nat.le_of_dvd (by decide) h; omega⟩
              · exact ⟨⟨(dvd_refl 15).trans (h15_u.trans (dvd_mul_left u q)), by omega⟩,
                  by omega, fun h => by
                    rcases hq.dvd_mul.mp (show q ∣ 3 * 5 from h) with h1 | h2
                    · have := Nat.le_of_dvd (by decide) h1; omega
                    · have := Nat.le_of_dvd (by decide) h2; omega⟩
            have hsumS : ∑ x ∈ S, x = 1 + 3 + 5 + 15 := by decide
            have hle := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
            rw [hsumS] at hle; omega
          · simp only [hb1, ↓reduceIte] at hsmallq
            have hb02 : 2 ≤ b0 := by omega
            have hq9 : 9 ≤ q := hb0_q.resolve_left hb1
            have hq2_ge : 75 < q ^ 2 := by nlinarith
            let S : Finset ℕ := {1, 3, 5, 15, 25, 75}
            have h75_u : 75 ∣ u := by
              dsimp [u]
              have h25 : 25 ∣ 5 ^ b0 := by
                have := pow_dvd_pow 5 hb02
                norm_num at this; exact this
              exact (Nat.mul_dvd_mul_left 3 h25).trans (dvd_mul_right _ _)
            have hnq3 : ¬ q ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
            have hnq5 : ¬ q ∣ 5 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
            have hnq75 : ¬ q ∣ 75 := by
              intro h
              rcases hq.dvd_mul.mp (show q ∣ 3 * (5 * 5) from h) with h1 | h2
              · exact hnq3 h1
              · rcases hq.dvd_mul.mp h2 with h3 | h4 <;> exact hnq5 ‹_›
            have hsub : S ⊆ (q * u).properDivisors.filter (fun x => x < q * d' ∧ ¬ q ∣ x) := by
              intro x hx
              simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
              rw [Finset.mem_filter, Nat.mem_properDivisors]
              rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
              · exact ⟨⟨(by decide : 1 ∣ 75).trans (h75_u.trans (dvd_mul_left u q)), by omega⟩,
                  by omega, fun h => hnq75 (h.trans (by decide : 1 ∣ 75))⟩
              · exact ⟨⟨(by decide : 3 ∣ 75).trans (h75_u.trans (dvd_mul_left u q)), by omega⟩,
                  by omega, fun h => hnq75 (h.trans (by decide : 3 ∣ 75))⟩
              · exact ⟨⟨(by decide : 5 ∣ 75).trans (h75_u.trans (dvd_mul_left u q)), by omega⟩,
                  by omega, fun h => hnq75 (h.trans (by decide : 5 ∣ 75))⟩
              · exact ⟨⟨(by decide : 15 ∣ 75).trans (h75_u.trans (dvd_mul_left u q)), by omega⟩,
                  by omega, fun h => hnq75 (h.trans (by decide : 15 ∣ 75))⟩
              · exact ⟨⟨(by decide : 25 ∣ 75).trans (h75_u.trans (dvd_mul_left u q)), by omega⟩,
                  by omega, fun h => hnq75 (h.trans (by decide : 25 ∣ 75))⟩
              · exact ⟨⟨(dvd_refl 75).trans (h75_u.trans (dvd_mul_left u q)), by omega⟩,
                  by omega, hnq75⟩
            have hsumS : ∑ x ∈ S, x = 1 + 3 + 5 + 15 + 25 + 75 := by decide
            have hle := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
            rw [hsumS] at hle; omega
  -- Now lift b from b0 to b
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
  induction k with
  | zero => simpa using hbase_c c hc
  | succ m ih =>
    have hprev := ih (by omega)
    let u := 3 * 5 ^ (b0 + m) * q ^ c
    have hu_pos : 0 < u := by have := hq.pos; positivity
    have h5u : 5 ∣ u := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) 3) _
    have hmul_eq : 5 * u = 3 * 5 ^ (b0 + (m + 1)) * q ^ c := by dsimp [u]; ring
    rw [← hmul_eq]
    apply HasAbsGap.mul_prime h5p hu_pos h5u hprev
    · -- h_u: add single fresh divisor ex = 3 * 5^(b0+m+1) * q^(c-1) < u
      let ex := 3 * 5 ^ (b0 + m + 1) * q ^ (c - 1)
      have hqc : q ^ c = q * q ^ (c - 1) := by rw [← pow_succ', Nat.sub_add_cancel hc]
      have hex_lt : ex < u := by
        dsimp only [ex, u]
        rw [hqc, show 5 ^ (b0 + m + 1) = 5 * 5 ^ (b0 + m) by ring]
        have hpos : 0 < 3 * 5 ^ (b0 + m) * q ^ (c - 1) := by have := hq.pos; positivity
        nlinarith
      have hex_dvd : ex ∣ 5 * u := by
        rw [hmul_eq]; dsimp only [ex]
        exact Nat.mul_dvd_mul_left _ (pow_dvd_pow q (Nat.sub_le c 1))
      have hex_not_u : ¬ ex ∣ u := by
        intro h
        have h52 : 5 ^ (b0 + m + 1) ∣ 3 * 5 ^ (b0 + m) * q ^ c :=
          ((dvd_mul_left _ 3).trans (dvd_mul_right _ _)).trans h
        have h52' : 5 ^ (b0 + m) * 5 ∣ 5 ^ (b0 + m) * (3 * q ^ c) := by
          have : 3 * 5 ^ (b0 + m) * q ^ c = 5 ^ (b0 + m) * (3 * q ^ c) := by ring
          rw [← this, show 5 ^ (b0 + m) * 5 = 5 ^ (b0 + m + 1) by ring]; exact h52
        have h5dvd : 5 ∣ 3 * q ^ c :=
          (Nat.mul_dvd_mul_iff_left (pow_pos h5p.pos (b0 + m))).mp h52'
        have hcop : Nat.Coprime 5 (3 * q ^ c) :=
          Nat.Coprime.mul_right (by decide) (((Nat.coprime_primes h5p hq).mpr (by omega)).pow_right c)
        exact h5p.not_dvd_one (hcop.dvd_of_dvd_mul_right (by simpa using h5dvd))
      have hsub : insert ex u.properDivisors ⊆ (5 * u).properDivisors.filter (· < u) := by
        intro x hx
        rw [Finset.mem_filter]
        rcases Finset.mem_insert.mp hx with rfl | hxu
        · exact ⟨Nat.mem_properDivisors.mpr ⟨hex_dvd, lt_trans hex_lt (by nlinarith)⟩, hex_lt⟩
        · obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp hxu
          exact ⟨Nat.mem_properDivisors.mpr ⟨h1.trans (dvd_mul_left u 5), lt_trans h2 (by nlinarith)⟩, h2⟩
      have hex_notin : ex ∉ u.properDivisors := fun h => hex_not_u (Nat.mem_properDivisors.mp h).1
      have hsum_ge : ex + properDivsSum u ≤ ∑ x ∈ (5 * u).properDivisors.filter (· < u), x := by
        have := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
        rw [Finset.sum_insert hex_notin] at this
        exact this
      have hmono := properDivsSum_ratio_mono_3 h5p hq (by decide) h5q (by omega : b0 ≤ b0 + m) hc
      let sc := 5 ^ m * q ^ (c - 1)
      have hu_eq : u = (3 * 5 ^ b0 * q) * sc := by dsimp [u, sc]; rw [hqc]; ring
      have hex_eq : ex = (3 * 5 ^ (b0 + 1)) * sc := by dsimp [ex, sc]; ring
      have hP_ge : properDivsSum (3 * 5 ^ b0 * q) * sc ≤ properDivsSum u := by
        have hpos : 0 < 3 * 5 ^ b0 * q := by have := hq.pos; positivity
        have h1 : properDivsSum (3 * 5 ^ b0 * q) * ((3 * 5 ^ b0 * q) * sc) ≤
            properDivsSum u * (3 * 5 ^ b0 * q) := by simpa [← hu_eq] using hmono
        nlinarith
      have hmul_r := Nat.mul_le_mul_right sc hratio5
      rw [← hu_eq, add_mul, ← hex_eq] at hmul_r
      omega
    · -- h_small: 5 | d' => 25 <= 5 * d', so {1, 3, q} < 5 * d'
      intro d' hd' h5d'
      have h5d'_ge : 25 ≤ 5 * d' := by
        obtain ⟨t, rfl⟩ := h5d'
        have hpos := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hd').1 hu_pos
        have ht : 1 ≤ t := by
          by_contra! h0
          have ht0 : t = 0 := by omega
          subst ht0; simp at hpos
        nlinarith
      have h5u_gt : 5 * d' < 5 * u := Nat.mul_lt_mul_of_pos_left (Nat.mem_properDivisors.mp hd').2 (by decide)
      let S : Finset ℕ := {1, 3, q}
      have hq3_dvd : 3 * q ∣ u := by
        dsimp [u]
        have : q ∣ q ^ c := dvd_pow_self q (by omega)
        have h1 : 3 * q ∣ 3 * q ^ c := Nat.mul_dvd_mul_left 3 this
        have h2 : 3 * q ^ c ∣ 3 * 5 ^ (b0 + m) * q ^ c := ⟨5 ^ (b0 + m), by ring⟩
        exact h1.trans h2
      have hsub : S ⊆ (5 * u).properDivisors.filter (fun x => x < 5 * d' ∧ ¬ 5 ∣ x) := by
        intro x hx
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_filter, Nat.mem_properDivisors]
        rcases hx with hx | hx | hx
        · rw [hx]; exact ⟨⟨one_dvd _, by omega⟩, by omega, by decide⟩
        · rw [hx]; exact ⟨⟨(dvd_mul_right 3 q).trans (hq3_dvd.trans (dvd_mul_left u 5)), by omega⟩,
            by omega, by decide⟩
        · rw [hx]; exact ⟨⟨(dvd_mul_left q 3).trans (hq3_dvd.trans (dvd_mul_left u 5)), by omega⟩,
            by omega, fun h => by rcases hq.eq_one_or_self_of_dvd 5 h with h1 | h2 <;> omega⟩
      have hsumS : ∑ x ∈ S, x = 1 + 3 + q := by
        rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega), Finset.sum_singleton]
        ring
      have hle := Finset.sum_le_sum_of_subset (f := fun x => x) hsub
      rw [hsumS] at hle; omega

lemma hasAbsGap_3_5_7 {b c : ℕ} (hb : 1 ≤ b) (hc : 1 ≤ c) :
    HasAbsGap (3 * 5 ^ b * 7 ^ c) 2 := by
  have hP105 : properDivsSum (3 * 5 * 7) = 87 := by
    rw [properDivsSum_sqfree3 (by decide) (by decide) (by decide) (by decide)]
  have hbase : HasAbsGap (3 * 5 ^ 1 * 7) 2 :=
    hasAbsGap_of_list (u := 3 * 5 * 7) (C := 2) (P_u := 87) (ds := sqfree3ProperDivs 5 7)
      (by decide) hP105.symm (by decide)
  exact hasAbsGap_3_5_q (q := 7) (C := 2) (b0 := 1) (by decide) (by decide) (by decide)
    le_rfl hb hc (Or.inl rfl) hbase (by rw [pow_one, hP105]; decide) (by rw [pow_one, hP105]; decide)
    (by decide) (by decide)

lemma hasAbsGap_3_5_11 {b c : ℕ} (hb : 1 ≤ b) (hc : 1 ≤ c) :
    HasAbsGap (3 * 5 ^ b * 11 ^ c) 2 := by
  have hP165 : properDivsSum (3 * 5 * 11) = 123 := by
    rw [properDivsSum_sqfree3 (by decide) (by decide) (by decide) (by decide)]
  have hbase : HasAbsGap (3 * 5 ^ 1 * 11) 2 :=
    hasAbsGap_of_list (u := 3 * 5 * 11) (C := 2) (P_u := 123) (ds := sqfree3ProperDivs 5 11)
      (by decide) hP165.symm (by decide)
  exact hasAbsGap_3_5_q (q := 11) (C := 2) (b0 := 1) (by decide) (by decide) (by decide)
    le_rfl hb hc (Or.inl rfl) hbase (by rw [pow_one, hP165]; decide) (by rw [pow_one, hP165]; decide)
    (by decide) (by decide)

lemma hasAbsGap_3_25_13 {b c : ℕ} (hb : 2 ≤ b) (hc : 1 ≤ c) :
    HasAbsGap (3 * 5 ^ b * 13 ^ c) 4 := by
  have hP975 : properDivsSum (3 * 5 ^ 2 * 13) = 761 := by
    rw [properDivsSum_eq_sigma_sub]
    have h1 : sigma 1 (3 * 5 ^ 2 * 13) = 4 * ppSum 5 2 * ppSum 13 1 := by
      have hc35 : Nat.Coprime 3 (5 ^ 2) := by decide
      have hc13 : Nat.Coprime (3 * 5 ^ 2) 13 := by decide
      rw [isMultiplicative_sigma.map_mul_of_coprime hc13,
          isMultiplicative_sigma.map_mul_of_coprime hc35,
          ← ppSum_eq_sigma (by decide : Nat.Prime 5)]
      have : sigma 1 3 = 4 := by decide
      have h13 : sigma 1 13 = ppSum 13 1 := by
        simpa [pow_one] using (ppSum_eq_sigma (p := 13) (a := 1) (by decide)).symm
      rw [this, h13]
    rw [h1]; decide
  have hbase : HasAbsGap (3 * 5 ^ 2 * 13) 4 :=
    hasAbsGap_of_list (u := 3 * 5 ^ 2 * 13) (C := 4) (P_u := 761)
      (ds := [1, 3, 5, 13, 15, 25, 39, 65, 75, 195, 325]) (by decide) hP975.symm (by decide)
  exact hasAbsGap_3_5_q (q := 13) (C := 4) (b0 := 2) (by decide) (by decide) (by decide)
    (by decide) hb hc (Or.inr (by decide)) hbase (by rw [hP975]; decide) (by rw [hP975]; decide)
    (by decide) (by decide)

lemma hasRelGap_3_5_13 {c : ℕ} (hc : 1 ≤ c) :
    HasRelGap (3 * 5 * 13 ^ c) 1 40 := by
  have hP195 : properDivsSum (3 * 5 * 13) = 141 := by
    rw [properDivsSum_sqfree3 (by decide) (by decide) (by decide) (by decide)]
  induction c with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      exact hasRelGap_of_list (u := 3 * 5 * 13) (a_num := 1) (a_den := 40) (P_u := 141)
        (ds := sqfree3ProperDivs 5 13) (by decide) hP195.symm (by decide)
    | succ k' =>
      have hprev := ih (by omega)
      have heq : 13 * (3 * 5 * 13 ^ (k' + 1)) = 3 * 5 * 13 ^ (k' + 2) := by ring
      rw [← heq]
      apply HasRelGap.mul_prime (by decide) (by positivity) hprev
      have hmono := properDivsSum_ratio_mono_3 (p := 5) (q := 13) (a0 := 1) (a := 1) (b0 := 1) (b := k' + 1)
        (by decide) (by decide) (by decide) (by decide) le_rfl (by omega)
      have hP195' : properDivsSum (3 * 5 ^ 1 * 13 ^ 1) = 141 := by simpa using hP195
      rw [hP195'] at hmono
      have hu_eq : 3 * 5 * 13 ^ (k' + 1) = 3 * 5 ^ 1 * 13 ^ (k' + 1) := by ring
      rw [hu_eq]
      change 40 * (3 * 5 ^ 1 * 13 ^ (k' + 1)) ≤
        1 * (13 * (3 * 5 ^ 1 * 13 ^ (k' + 1))) + 40 * properDivsSum (3 * 5 ^ 1 * 13 ^ (k' + 1))
      have hbase_n : 3 * 5 ^ 1 * 13 ^ 1 = 195 := by decide
      rw [hbase_n] at hmono
      nlinarith

set_option maxHeartbeats 800000 in
/-- Explicit 8-element lift for u = 105 (b = 1, c = 1, p3 = 7, p4 <= 67). -/
lemma lift_prime_step_105 {r a L g : ℕ} (hr : r.Prime) (hrlo : 47 ≤ r) (hrhi : r ≤ 67)
    (ha : 1 ≤ a) (hg : 1 ≤ g) (hL_le : 2 * L ≤ 3 * r ^ a)
    (hP_ratio : 89 * r ^ a ≤ properDivsSum (r ^ a * 105))
    (hcov : ∀ y, L ≤ y → y ≤ properDivsSum (r ^ a * 105) - L →
      repNat (r ^ a * 105).properDivisors y)
    (hgap : ∀ k, k < properDivsSum (r ^ a * 105) →
      ∃ i, repNat (r ^ a * 105).properDivisors i ∧ k < i + g ∧ i ≤ k) :
    (∀ y, L ≤ y → y ≤ properDivsSum (r ^ (a + 1) * 105) - L →
      repNat (r ^ (a + 1) * 105).properDivisors y) ∧
    (∀ k, k < properDivsSum (r ^ (a + 1) * 105) →
      ∃ i, repNat (r ^ (a + 1) * 105).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
  classical
  let n := r ^ a * 105
  let n' := r ^ (a + 1) * 105
  let R := r ^ (a + 1)
  have hR_eq : R = r * r ^ a := by dsimp [R]; ring
  have hcop : ¬ r ∣ 105 := by
    intro h
    have h1 : r ∣ 3 * (5 * 7) := h
    rcases hr.dvd_mul.mp h1 with h2 | h3
    · have := Nat.le_of_dvd (by decide) h2; omega
    · rcases hr.dvd_mul.mp h3 with h4 | h5
      · have := Nat.le_of_dvd (by decide) h4; omega
      · have := Nat.le_of_dvd (by decide) h5; omega
  let xs : List ℕ := [R, n, 3 * R, 5 * R, 7 * R, 15 * R, 21 * R, 35 * R]
  have hra_pos : 0 < r ^ a := pow_pos hr.pos a
  have hR_pos : 0 < R := pow_pos hr.pos (a + 1)
  have hxs_nd : xs.Nodup := by
    simp only [xs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    have hne : ∀ k : ℕ, k * R ≠ n := by
      intro k h
      have : r ^ (a + 1) ∣ r ^ a * 105 := ⟨k, by dsimp [R, n] at h; linarith⟩
      rw [pow_succ] at this
      exact hcop ((Nat.mul_dvd_mul_iff_left hra_pos).mp this)
    have hmul_ne : ∀ c1 c2 : ℕ, c1 ≠ c2 → c1 * R ≠ c2 * R :=
      fun c1 c2 hc h => hc (Nat.eq_of_mul_eq_mul_right hR_pos h)
    refine ⟨⟨fun h => hne 1 (by simpa using h),
        fun h => hmul_ne 1 3 (by decide) (by simpa using h),
        fun h => hmul_ne 1 5 (by decide) (by simpa using h),
        fun h => hmul_ne 1 7 (by decide) (by simpa using h),
        fun h => hmul_ne 1 15 (by decide) (by simpa using h),
        fun h => hmul_ne 1 21 (by decide) (by simpa using h),
        fun h => hmul_ne 1 35 (by decide) (by simpa using h)⟩,
      ⟨fun h => hne 3 h.symm, fun h => hne 5 h.symm, fun h => hne 7 h.symm,
       fun h => hne 15 h.symm, fun h => hne 21 h.symm, fun h => hne 35 h.symm⟩,
      ⟨hmul_ne 3 5 (by decide), hmul_ne 3 7 (by decide), hmul_ne 3 15 (by decide),
       hmul_ne 3 21 (by decide), hmul_ne 3 35 (by decide)⟩,
      ⟨hmul_ne 5 7 (by decide), hmul_ne 5 15 (by decide), hmul_ne 5 21 (by decide), hmul_ne 5 35 (by decide)⟩,
      ⟨hmul_ne 7 15 (by decide), hmul_ne 7 21 (by decide), hmul_ne 7 35 (by decide)⟩,
      ⟨hmul_ne 15 21 (by decide), hmul_ne 15 35 (by decide)⟩,
      ⟨hmul_ne 21 35 (by decide), not_false⟩⟩
  have hdisj : ∀ x ∈ xs, x ∉ n.properDivisors := by
    intro x hx hmem
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hmem
    have hnoR : ¬ R ∣ n := by
      intro h
      have : r ^ (a + 1) ∣ r ^ a * 105 := h
      rw [pow_succ] at this
      exact hcop ((Nat.mul_dvd_mul_iff_left hra_pos).mp this)
    simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hnoR hdvd
    · omega
    · exact hnoR ((dvd_mul_left R 3).trans hdvd)
    · exact hnoR ((dvd_mul_left R 5).trans hdvd)
    · exact hnoR ((dvd_mul_left R 7).trans hdvd)
    · exact hnoR ((dvd_mul_left R 15).trans hdvd)
    · exact hnoR ((dvd_mul_left R 21).trans hdvd)
    · exact hnoR ((dvd_mul_left R 35).trans hdvd)
  have h105_pdivs : (105 : ℕ).properDivisors = {1, 3, 5, 7, 15, 21, 35} := by decide
  have hUnion : n.properDivisors ∪ xs.toFinset = n'.properDivisors := by
    ext x
    simp only [Finset.mem_union, List.mem_toFinset, xs, List.mem_cons, List.not_mem_nil, or_false,
      Nat.mem_properDivisors]
    constructor
    · rintro (⟨h1, h2⟩ | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))
      · exact ⟨h1.trans (Nat.mul_dvd_mul_right (pow_dvd_pow r (Nat.le_succ a)) 105),
          lt_of_lt_of_le h2 (Nat.mul_le_mul_right 105 (pow_le_pow_right₀ hr.one_lt.le (Nat.le_succ a)))⟩
      · exact ⟨dvd_mul_right R 105, by change R < R * 105; omega⟩
      · exact ⟨Nat.mul_dvd_mul_right (pow_dvd_pow r (Nat.le_succ a)) 105,
          Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hr.one_lt (Nat.lt_succ_self a)) (by decide)⟩
      · exact ⟨⟨35, by dsimp [n', R]; ring⟩, by change 3 * R < R * 105; omega⟩
      · exact ⟨⟨21, by dsimp [n', R]; ring⟩, by change 5 * R < R * 105; omega⟩
      · exact ⟨⟨15, by dsimp [n', R]; ring⟩, by change 7 * R < R * 105; omega⟩
      · exact ⟨⟨7, by dsimp [n', R]; ring⟩, by change 15 * R < R * 105; omega⟩
      · exact ⟨⟨5, by dsimp [n', R]; ring⟩, by change 21 * R < R * 105; omega⟩
      · exact ⟨⟨3, by dsimp [n', R]; ring⟩, by change 35 * R < R * 105; omega⟩
    · rintro ⟨hx1, hx2⟩
      by_cases hdiv : R ∣ x
      · obtain ⟨d, rfl⟩ := hdiv
        have hd : d ∈ (105 : ℕ).properDivisors := Nat.mem_properDivisors.mpr
          ⟨(Nat.mul_dvd_mul_iff_left hR_pos).mp hx1, lt_of_mul_lt_mul_left hx2 (Nat.zero_le R)⟩
        rw [h105_pdivs] at hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        right
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · left; ring
        · right; right; left; ring
        · right; right; right; left; ring
        · right; right; right; right; left; ring
        · right; right; right; right; right; left; ring
        · right; right; right; right; right; right; left; ring
        · right; right; right; right; right; right; right; ring
      · have hx0 : x ≠ 0 := fun h => by subst h; exact hdiv (dvd_zero R)
        have hfx : x.factorization r ≤ a := by
          by_contra! hgt
          exact hdiv ((hr.pow_dvd_iff_le_factorization hx0).mpr hgt)
        have hxdvd : x ∣ n := by
          have h1 : r ^ x.factorization r ∣ r ^ a := pow_dvd_pow r hfx
          have h2 : x / r ^ x.factorization r ∣ 105 := by
            have hd' : x / r ^ x.factorization r ∣ r ^ (a + 1) * 105 :=
              (Nat.ordCompl_dvd x r).trans hx1
            exact ((hr.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hr hx0)).pow_left _).symm.dvd_of_dvd_mul_left hd'
          rw [← Nat.ordProj_mul_ordCompl_eq_self x r]
          exact Nat.mul_dvd_mul h1 h2
        by_cases hxn : x = n
        · right; right; left; exact hxn
        · left; exact ⟨hxdvd, lt_of_le_of_ne (Nat.le_of_dvd (by positivity) hxdvd) hxn⟩
  have hsum_xs : ∑ x ∈ xs.toFinset, x = xs.sum := by
    generalize xs = l at hxs_nd ⊢
    simpa only [List.map_id'] using List.sum_toFinset (fun x => x) hxs_nd
  have hP_eq : properDivsSum n' = properDivsSum n + xs.sum := by
    dsimp only [properDivsSum]
    rw [← hUnion, Finset.sum_union (by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact hdisj x (List.mem_toFinset.mp hx2) hx1), hsum_xs]
  have hP_ratio' : 89 * r ^ a ≤ properDivsSum n := hP_ratio
  have hL_le_Pn : L ≤ properDivsSum n := by omega
  have hsteps : ∀ (pre : List ℕ) (x : ℕ) (suf : List ℕ),
      xs = pre ++ x :: suf → L + x ≤ (properDivsSum n - L) + pre.sum + 1 := by
    intro pre x suf heq
    have hlen : pre.length < 8 := by
      have h1 := congrArg List.length heq
      simp only [xs, List.length_cons, List.length_nil, List.length_append] at h1
      omega
    have hW : 86 * r ^ a ≤ properDivsSum n - 2 * L := by omega
    have hR_le : R ≤ 67 * r ^ a := by rw [hR_eq]; exact Nat.mul_le_mul_right _ hrhi
    have hR_ge : 47 * r ^ a ≤ R := by rw [hR_eq]; exact Nat.mul_le_mul_right _ hrlo
    interval_cases hpl : pre.length
    · cases pre with
      | nil =>
        simp only [List.nil_append, xs, List.cons.injEq] at heq
        rcases heq with ⟨rfl, _⟩
        simp only [List.sum_nil]; omega
      | cons _ _ => simp at hpl
    · rcases pre with _ | ⟨a0, _ | _⟩ <;> simp only [List.length_cons, List.length_nil] at hpl <;> try omega
      simp only [List.cons_append, List.nil_append, xs, List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl, _⟩
      simp only [List.sum_cons, List.sum_nil]; dsimp [n]; omega
    · rcases pre with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hpl <;> try omega
      simp only [List.cons_append, List.nil_append, xs, List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl, _⟩
      simp only [List.sum_cons, List.sum_nil]; dsimp [n]; omega
    · rcases pre with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hpl <;> try omega
      simp only [List.cons_append, List.nil_append, xs, List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl, rfl, _⟩
      simp only [List.sum_cons, List.sum_nil]; dsimp [n]; omega
    · rcases pre with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | _⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hpl <;> try omega
      simp only [List.cons_append, List.nil_append, xs, List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, _⟩
      simp only [List.sum_cons, List.sum_nil]; dsimp [n]; omega
    · rcases pre with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | _⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hpl <;> try omega
      simp only [List.cons_append, List.nil_append, xs, List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, _⟩
      simp only [List.sum_cons, List.sum_nil]; dsimp [n]; omega
    · rcases pre with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | _⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hpl <;> try omega
      simp only [List.cons_append, List.nil_append, xs, List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, _⟩
      simp only [List.sum_cons, List.sum_nil]; dsimp [n]; omega
    · rcases pre with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | _⟩⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hpl <;> try omega
      simp only [List.cons_append, List.nil_append, xs, List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, _⟩
      simp only [List.sum_cons, List.sum_nil]; dsimp [n]; omega
  have hcov' := repNat_append_list_interval xs hxs_nd hdisj hcov hsteps
  rw [hUnion] at hcov'
  have hcov_final : ∀ y, L ≤ y → y ≤ properDivsSum n' - L → repNat n'.properDivisors y := by
    intro y hy1 hy2
    have hy2' : y ≤ (properDivsSum n - L) + xs.sum := by omega
    exact hcov' y hy1 hy2'
  have hsub_n : n.properDivisors ⊆ n'.properDivisors := by
    rw [← hUnion]; exact Finset.subset_union_left
  exact ⟨hcov_final, repNat_union_gap hg hsub_n hL_le_Pn hcov_final hgap⟩

def sqfreeProperDivs (p3 p4 : ℕ) : List ℕ :=
  [1, 3, 5, p3, 15, 3 * p3, 5 * p3, p4, 3 * p4, 5 * p4,
   15 * p3, p3 * p4, 15 * p4, 3 * p3 * p4, 5 * p3 * p4]

lemma properDivsSum_sqfree {p3 p4 : ℕ} (hp3 : p3.Prime) (hp4 : p4.Prime)
    (h3 : 5 < p3) (h4 : p3 < p4) :
    properDivsSum (3 * 5 * p3 * p4) = 4 * 6 * (p3 + 1) * (p4 + 1) - 3 * 5 * p3 * p4 := by
  rw [properDivsSum_eq_sigma_sub]
  have h1 := sigma_four_primes hp3 hp4 h3 h4 (b := 1) (c := 1) (d := 1)
  simp only [pow_one] at h1
  have hp5 : ppSum 5 1 = 6 := by decide
  have hp3' : ppSum p3 1 = p3 + 1 := by
    rw [ppSum_eq_sigma hp3, sigma_one_apply_prime_pow hp3]; simp [Finset.sum_range_succ, add_comm]
  have hp4' : ppSum p4 1 = p4 + 1 := by
    rw [ppSum_eq_sigma hp4, sigma_one_apply_prime_pow hp4]; simp [Finset.sum_range_succ, add_comm]
  rw [h1, hp5, hp3', hp4']

lemma sub_mul_le_sub_mul_of_mul_le {P0 P1 B0 B1 M : ℕ}
    (h1 : M ≤ P0) (h2 : M ≤ P1) (hB : B0 ≤ B1) (hm : P0 * B1 ≤ P1 * B0) :
    (P0 - M) * B1 ≤ (P1 - M) * B0 := by
  zify [h1, h2] at hm ⊢
  nlinarith

/-- Generic 3-prime-power core lift for a pair (p3, p4) with base B0 = 3 * 5 * p3 * p4. -/
lemma lift_4prime_core {p3 p4 L g b c d : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (h3 : 5 < p3) (h4 : p3 < p4) (hg : 1 ≤ g)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hL_bound : 2 * L ≤ properDivsSum (3 * 5 * p3 * p4))
    (hbig0 : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ properDivsSum (3 * 5 * p3 * p4))
    (hcov0 : ∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 * p3 * p4) - L →
      repNat (3 * 5 * p3 * p4).properDivisors y)
    (hgap0 : ∀ k, k < properDivsSum (3 * 5 * p3 * p4) →
      ∃ i, repNat (3 * 5 * p3 * p4).properDivisors i ∧ k < i + g ∧ i ≤ k)
    (hmod0 : ∀ x, x < L → x % 12 = 6 → repNat (3 * 5 * p3 * p4).properDivisors x)
    (hrel5 : HasRelGap (3 * p3 * p4) (properDivsSum (3 * 5 * p3 * p4) - 2 * L) (5 * (3 * 5 * p3 * p4)))
    (hrel3_base : HasRelGap (3 * 5 * p4) (properDivsSum (3 * 5 * p3 * p4) - 2 * L) (p3 * (3 * 5 * p3 * p4)))
    (hrel3_step : p3 * (3 * 5 * p3 * p4) * (3 * 5 * p4) ≤
      (properDivsSum (3 * 5 * p3 * p4) - 2 * L) * (5 * (3 * 5 * p4)) +
      p3 * (3 * 5 * p3 * p4) * properDivsSum (3 * 5 * p4))
    (hstep4 : ∀ b' c' d', 1 ≤ b' → 1 ≤ c' → 1 ≤ d' →
      (∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - L →
        repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ d').properDivisors y) →
      (∀ k, k < properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') →
        ∃ i, repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ d').properDivisors i ∧ k < i + g ∧ i ≤ k) →
      (∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)) - L →
        repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)) →
        ∃ i, repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)).properDivisors i ∧ k < i + g ∧ i ≤ k)) :
    let B := 3 * 5 ^ b * p3 ^ c * p4 ^ d
    (∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y) ∧
    (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + g ∧ i ≤ k) ∧
    (∀ x, x < L → x % 12 = 6 → repNat B.properDivisors x) ∧
    (2 * g + 1) * (2 * L + 8 * g + 8) ≤ properDivsSum B := by
  have h5p : Nat.Prime 5 := by decide
  have h3p : Nat.Prime 3 := by decide
  let B0 := 3 * 5 * p3 * p4
  let P0 := properDivsSum B0
  have hB0pos : 0 < B0 := by have := hp3.pos; have := hp4.pos; positivity
  -- Helper: (P0 - 2L) * n <= (P(n) - 2L) * B0 for any n = 3 * 5^b' * p3^c' * p4^d'
  have hP_lb : ∀ b' c' d', 1 ≤ b' → 1 ≤ c' → 1 ≤ d' →
      (P0 - 2 * L) * (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') ≤
      (properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - 2 * L) * B0 ∧
      P0 ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') := by
    intro b' c' d' hb' hc' hd'
    have hmono := properDivsSum_ratio_mono_4 hp3 hp4 h3 h4 hb' hc' hd'
    have hB0_eq : 3 * 5 ^ 1 * p3 ^ 1 * p4 ^ 1 = B0 := by dsimp [B0]; ring
    rw [hB0_eq] at hmono
    have hB0_le : B0 ≤ 3 * 5 ^ b' * p3 ^ c' * p4 ^ d' := by
      dsimp [B0]
      have h1 : 5 ≤ 5 ^ b' := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 5) hb'
      have h2 : p3 ≤ p3 ^ c' := by simpa using pow_le_pow_right₀ hp3.one_lt.le hc'
      have h3' : p4 ≤ p4 ^ d' := by simpa using pow_le_pow_right₀ hp4.one_lt.le hd'
      have : 3 * 5 * p3 ≤ 3 * 5 ^ b' * p3 ^ c' := Nat.mul_le_mul (Nat.mul_le_mul_left 3 h1) h2
      exact Nat.mul_le_mul this h3'
    have hP_ge : P0 ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') := by
      nlinarith
    refine ⟨?_, hP_ge⟩
    have h2L : 2 * L ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') := le_trans hL_bound hP_ge
    exact sub_mul_le_sub_mul_of_mul_le hL_bound h2L hB0_le hmono
  have hL_le_P0 : L ≤ P0 := by
    have : 2 * L ≤ P0 := hL_bound
    omega
  -- Step 1: lift 5 from 1 to b (u = 3 * p3 * p4 fixed!)
  have hstep1 : ∀ b', 1 ≤ b' →
      (∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 ^ b' * p3 * p4) - L →
        repNat (3 * 5 ^ b' * p3 * p4).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 * 5 ^ b' * p3 * p4) →
        ∃ i, repNat (3 * 5 ^ b' * p3 * p4).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
    intro b' hb'
    induction b' with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa [B0] using ⟨hcov0, hgap0⟩
      | succ k' =>
        obtain ⟨hc_prev, hg_prev⟩ := ih (by omega)
        let u := 3 * p3 * p4
        have hu_pos : 0 < u := by have := hp3.pos; have := hp4.pos; positivity
        have hcop5 : ¬ 5 ∣ u := by
          intro h
          have : 5 ∣ 3 * (p3 * p4) := by simpa [u, mul_assoc] using h
          rcases h5p.dvd_mul.mp this with h1 | h2
          · exact absurd h1 (by decide)
          · rcases h5p.dvd_mul.mp h2 with h1' | h2'
            · rcases hp3.eq_one_or_self_of_dvd 5 h1' with e1 | e2 <;> omega
            · rcases hp4.eq_one_or_self_of_dvd 5 h2' with e1 | e2 <;> omega
        have heq1 : 5 ^ (k' + 1) * u = 3 * 5 ^ (k' + 1) * p3 * p4 := by dsimp [u]; ring
        have heq2 : 5 ^ (k' + 2) * u = 3 * 5 ^ (k' + 2) * p3 * p4 := by dsimp [u]; ring
        have hPlb := hP_lb (k' + 1) 1 1 (by omega) le_rfl le_rfl
        simp only [pow_one] at hPlb
        have hres := lift_prime_step_no_interleave (L := L) (g := g) h5p hu_pos (by omega : 1 ≤ k' + 1) hcop5 hg
          (by rw [heq1]; exact le_trans hL_le_P0 hPlb.2)
          (by rw [heq1]; exact hc_prev) (by rw [heq1]; exact hg_prev)
          (by
            intro d hd
            have hr := hrel5 d hd
            have hmul := Nat.mul_le_mul_left (5 ^ (k' + 1)) hr
            rw [heq1]
            let S := ∑ e ∈ u.properDivisors.filter (· < d), e
            have h5' : B0 * (5 ^ (k' + 2) * d) ≤
                B0 * (properDivsSum (3 * 5 ^ (k' + 1) * p3 * p4) - 2 * L + 5 ^ (k' + 2) * S) := by
              calc B0 * (5 ^ (k' + 2) * d)
                  = 5 ^ (k' + 1) * (5 * B0 * d) := by ring
                _ ≤ 5 ^ (k' + 1) * ((P0 - 2 * L) * u + 5 * B0 * S) := hmul
                _ = (P0 - 2 * L) * (3 * 5 ^ (k' + 1) * p3 * p4) + B0 * (5 ^ (k' + 2) * S) := by dsimp [u]; ring
                _ ≤ (properDivsSum (3 * 5 ^ (k' + 1) * p3 * p4) - 2 * L) * B0 + B0 * (5 ^ (k' + 2) * S) :=
                    Nat.add_le_add_right hPlb.1 _
                _ = B0 * (properDivsSum (3 * 5 ^ (k' + 1) * p3 * p4) - 2 * L + 5 ^ (k' + 2) * S) := by ring
            have h6' := Nat.le_of_mul_le_mul_left h5' hB0pos
            have h2L' : 2 * L ≤ properDivsSum (3 * 5 ^ (k' + 1) * p3 * p4) := le_trans hL_bound hPlb.2
            change 2 * L + 5 ^ (k' + 2) * d ≤
              properDivsSum (3 * 5 ^ (k' + 1) * p3 * p4) + 5 ^ (k' + 2) * S + 1
            omega)
          (by
            have hPu : u ≤ 5 * properDivsSum u := by
              have hmem : p3 * p4 ∈ u.properDivisors := Nat.mem_properDivisors.mpr
                ⟨⟨3, by dsimp [u]; ring⟩, by dsimp [u]; have := hp3.pos; have := hp4.pos; nlinarith⟩
              have hle : p3 * p4 ≤ properDivsSum u :=
                Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hmem
              have hu3 : u = 3 * (p3 * p4) := by dsimp [u]; ring
              omega
            have h2L' : 2 * L ≤ properDivsSum (3 * 5 ^ (k' + 1) * p3 * p4) := le_trans hL_bound hPlb.2
            have hmul5 : 5 ^ (k' + 1) * u ≤ 5 ^ (k' + 2) * properDivsSum u := by
              rw [show 5 ^ (k' + 2) * properDivsSum u = 5 ^ (k' + 1) * (5 * properDivsSum u) by ring]
              exact Nat.mul_le_mul_left _ hPu
            change 2 * L + 5 ^ (k' + 1) * u ≤
              properDivsSum (5 ^ (k' + 1) * u) + 5 ^ (k' + 2) * properDivsSum u + 1
            rw [heq1]
            omega)
        simpa [heq2, properDivsSum] using hres
  -- Step 2: HasRelGap (3 * 5^b * p4) (P0 - 2L) (p3 * B0) by induction on b, then lift p3 from 1 to c!
  have hrel3 : HasRelGap (3 * 5 ^ b * p4) (P0 - 2 * L) (p3 * B0) := by
    induction b with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hrel3_base
      | succ k' =>
        have hprev := ih (by omega)
        have heq : 5 * (3 * 5 ^ (k' + 1) * p4) = 3 * 5 ^ (k' + 2) * p4 := by ring
        rw [← heq]
        apply HasRelGap.mul_prime h5p (by have := hp4.pos; positivity) hprev
        have hmono := properDivsSum_ratio_mono_3 (a0 := 1) (a := k' + 1) (b0 := 1) (b := 1)
          h5p hp4 (by decide) (by omega) (by omega) le_rfl
        simp only [pow_one] at hmono
        have hpos : 0 < 3 * 5 * p4 := by have := hp4.pos; positivity
        have hP_ge : properDivsSum (3 * 5 * p4) * 5 ^ k' ≤ properDivsSum (3 * 5 ^ (k' + 1) * p4) := by
          apply Nat.le_of_mul_le_mul_right _ hpos
          calc properDivsSum (3 * 5 * p4) * 5 ^ k' * (3 * 5 * p4)
              = properDivsSum (3 * 5 * p4) * (3 * 5 ^ (k' + 1) * p4) := by ring
            _ ≤ properDivsSum (3 * 5 ^ (k' + 1) * p4) * (3 * 5 * p4) := hmono
        have hmul := Nat.mul_le_mul_right (5 ^ k') hrel3_step
        have h1 : 3 * 5 ^ (k' + 1) * p4 = (3 * 5 * p4) * 5 ^ k' := by ring
        change p3 * B0 * (3 * 5 ^ (k' + 1) * p4) ≤
          (P0 - 2 * L) * (5 * (3 * 5 ^ (k' + 1) * p4)) + p3 * B0 * properDivsSum (3 * 5 ^ (k' + 1) * p4)
        calc p3 * B0 * (3 * 5 ^ (k' + 1) * p4)
            = p3 * B0 * (3 * 5 * p4) * 5 ^ k' := by rw [h1]; ring
          _ ≤ ((P0 - 2 * L) * (5 * (3 * 5 * p4)) + p3 * B0 * properDivsSum (3 * 5 * p4)) * 5 ^ k' := hmul
          _ = (P0 - 2 * L) * (5 * (3 * 5 ^ (k' + 1) * p4)) + p3 * B0 * (properDivsSum (3 * 5 * p4) * 5 ^ k') := by rw [h1]; ring
          _ ≤ (P0 - 2 * L) * (5 * (3 * 5 ^ (k' + 1) * p4)) + p3 * B0 * properDivsSum (3 * 5 ^ (k' + 1) * p4) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left _ hP_ge) _
  have hstep2 : ∀ c', 1 ≤ c' →
      (∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 ^ b * p3 ^ c' * p4) - L →
        repNat (3 * 5 ^ b * p3 ^ c' * p4).properDivisors y) ∧
      (∀ k, k < properDivsSum (3 * 5 ^ b * p3 ^ c' * p4) →
        ∃ i, repNat (3 * 5 ^ b * p3 ^ c' * p4).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
    intro c' hc'
    induction c' with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hstep1 b hb
      | succ k' =>
        obtain ⟨hc_prev, hg_prev⟩ := ih (by omega)
        let u := 3 * 5 ^ b * p4
        have hu_pos : 0 < u := by have := hp4.pos; positivity
        have hcop3 : ¬ p3 ∣ u := by
          intro h
          have : p3 ∣ 3 * (5 ^ b * p4) := by simpa [u, mul_assoc] using h
          rcases hp3.dvd_mul.mp this with h1 | h2
          · have := Nat.le_of_dvd (by decide) h1; omega
          · rcases hp3.dvd_mul.mp h2 with h1' | h2'
            · have := hp3.dvd_of_dvd_pow h1'; have := Nat.le_of_dvd (by decide) this; omega
            · rcases hp4.eq_one_or_self_of_dvd p3 h2' with e1 | e2 <;> omega
        have heq1 : p3 ^ (k' + 1) * u = 3 * 5 ^ b * p3 ^ (k' + 1) * p4 := by dsimp [u]; ring
        have heq2 : p3 ^ (k' + 2) * u = 3 * 5 ^ b * p3 ^ (k' + 2) * p4 := by dsimp [u]; ring
        have hPlb := hP_lb b (k' + 1) 1 hb (by omega) le_rfl
        simp only [pow_one] at hPlb
        have hres := lift_prime_step_no_interleave (L := L) (g := g) hp3 hu_pos (by omega : 1 ≤ k' + 1) hcop3 hg
          (by rw [heq1]; exact le_trans hL_le_P0 hPlb.2)
          (by rw [heq1]; exact hc_prev) (by rw [heq1]; exact hg_prev)
          (by
            intro d hd
            have hr := hrel3 d hd
            have hmul := Nat.mul_le_mul_left (p3 ^ (k' + 1)) hr
            rw [heq1]
            let S := ∑ e ∈ u.properDivisors.filter (· < d), e
            have h5' : B0 * (p3 ^ (k' + 2) * d) ≤
                B0 * (properDivsSum (3 * 5 ^ b * p3 ^ (k' + 1) * p4) - 2 * L + p3 ^ (k' + 2) * S) := by
              calc B0 * (p3 ^ (k' + 2) * d)
                  = p3 ^ (k' + 1) * (p3 * B0 * d) := by ring
                _ ≤ p3 ^ (k' + 1) * ((P0 - 2 * L) * u + p3 * B0 * S) := hmul
                _ = (P0 - 2 * L) * (3 * 5 ^ b * p3 ^ (k' + 1) * p4) + B0 * (p3 ^ (k' + 2) * S) := by dsimp [u]; ring
                _ ≤ (properDivsSum (3 * 5 ^ b * p3 ^ (k' + 1) * p4) - 2 * L) * B0 + B0 * (p3 ^ (k' + 2) * S) :=
                    Nat.add_le_add_right hPlb.1 _
                _ = B0 * (properDivsSum (3 * 5 ^ b * p3 ^ (k' + 1) * p4) - 2 * L + p3 ^ (k' + 2) * S) := by ring
            have h6' := Nat.le_of_mul_le_mul_left h5' hB0pos
            have h2L' : 2 * L ≤ properDivsSum (3 * 5 ^ b * p3 ^ (k' + 1) * p4) := le_trans hL_bound hPlb.2
            change 2 * L + p3 ^ (k' + 2) * d ≤
              properDivsSum (3 * 5 ^ b * p3 ^ (k' + 1) * p4) + p3 ^ (k' + 2) * S + 1
            omega)
          (by
            have hPu : u ≤ p3 * properDivsSum u := by
              have hpos5 : 0 < 5 ^ b * p4 := by have := hp4.pos; positivity
              have hu3 : u = 3 * (5 ^ b * p4) := by dsimp [u]; ring
              have hmem : 5 ^ b * p4 ∈ u.properDivisors := Nat.mem_properDivisors.mpr
                ⟨⟨3, by rw [hu3]; ring⟩, by omega⟩
              have hle : 5 ^ b * p4 ≤ properDivsSum u :=
                Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hmem
              nlinarith
            have h2L' : 2 * L ≤ properDivsSum (3 * 5 ^ b * p3 ^ (k' + 1) * p4) := le_trans hL_bound hPlb.2
            have hmulp : p3 ^ (k' + 1) * u ≤ p3 ^ (k' + 2) * properDivsSum u := by
              rw [show p3 ^ (k' + 2) * properDivsSum u = p3 ^ (k' + 1) * (p3 * properDivsSum u) by ring]
              exact Nat.mul_le_mul_left _ hPu
            change 2 * L + p3 ^ (k' + 1) * u ≤
              properDivsSum (p3 ^ (k' + 1) * u) + p3 ^ (k' + 2) * properDivsSum u + 1
            rw [heq1]
            omega)
        simpa [heq2, properDivsSum] using hres
  -- Step 3: lift p4 from 1 to d via hstep4!
  have hstep3 : ∀ d', 1 ≤ d' →
      (∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 ^ b * p3 ^ c * p4 ^ d') - L →
        repNat (3 * 5 ^ b * p3 ^ c * p4 ^ d').properDivisors y) ∧
      (∀ k, k < properDivsSum (3 * 5 ^ b * p3 ^ c * p4 ^ d') →
        ∃ i, repNat (3 * 5 ^ b * p3 ^ c * p4 ^ d').properDivisors i ∧ k < i + g ∧ i ≤ k) := by
    intro d' hd'
    induction d' with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero => simpa using hstep2 c hc
      | succ k' =>
        obtain ⟨hc_prev, hg_prev⟩ := ih (by omega)
        exact hstep4 b c (k' + 1) hb hc (by omega) hc_prev hg_prev
  obtain ⟨hcovF, hgapF⟩ := hstep3 d hd
  have hB0_dvd_B : B0 ∣ 3 * 5 ^ b * p3 ^ c * p4 ^ d := by
    dsimp [B0]
    exact Nat.mul_dvd_mul
      (Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 3 (dvd_pow_self 5 (by omega))) (dvd_pow_self p3 (by omega)))
      (dvd_pow_self p4 (by omega))
  have hmodF : ∀ x, x < L → x % 12 = 6 → repNat (3 * 5 ^ b * p3 ^ c * p4 ^ d).properDivisors x := by
    intro x hx hx12
    obtain ⟨s, hs, hsum⟩ := hmod0 x hx hx12
    refine ⟨s, fun y hy => ?_, hsum⟩
    obtain ⟨hy1, hy2⟩ := Nat.mem_properDivisors.mp (hs hy)
    exact Nat.mem_properDivisors.mpr ⟨hy1.trans hB0_dvd_B,
      lt_of_lt_of_le hy2 (Nat.le_of_dvd (by have := hp3.pos; have := hp4.pos; positivity) hB0_dvd_B)⟩
  exact ⟨hcovF, hgapF, hmodF, le_trans hbig0 (hP_lb b c d hb hc hd).2⟩

/-- Helper turning HasAbsGap (3 * 5^b' * p3^c') C into the hstep4 obligation of lift_4prime_core
    whenever C * p4 * B0 <= (P0 - 2*L) * (3 * 5^b' * p3^c'). -/
lemma hstep4_of_abs {p3 p4 L g C b' c' d' : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (h3 : 5 < p3) (h4 : p3 < p4) (hg : 1 ≤ g)
    (hb' : 1 ≤ b') (hc' : 1 ≤ c') (hd' : 1 ≤ d')
    (hL_bound : 2 * L ≤ properDivsSum (3 * 5 * p3 * p4))
    (habs : HasAbsGap (3 * 5 ^ b' * p3 ^ c') C)
    (hmargin : C * p4 * (3 * 5 * p3 * p4) ≤
      (properDivsSum (3 * 5 * p3 * p4) - 2 * L) * (3 * 5 ^ b' * p3 ^ c'))
    (hcov : ∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - L →
      repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ d').properDivisors y)
    (hgap : ∀ k, k < properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') →
      ∃ i, repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ d').properDivisors i ∧ k < i + g ∧ i ≤ k) :
    (∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)) - L →
      repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)).properDivisors y) ∧
    (∀ k, k < properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)) →
      ∃ i, repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
  let u := 3 * 5 ^ b' * p3 ^ c'
  let B0 := 3 * 5 * p3 * p4
  let P0 := properDivsSum B0
  have hu_pos : 0 < u := by have := hp3.pos; positivity
  have hB0pos : 0 < B0 := by have := hp3.pos; have := hp4.pos; positivity
  have hcop4 : ¬ p4 ∣ u := by
    intro h
    have : p4 ∣ 3 * (5 ^ b' * p3 ^ c') := by simpa [u, mul_assoc] using h
    rcases hp4.dvd_mul.mp this with h1 | h2
    · have := Nat.le_of_dvd (by decide) h1; omega
    · rcases hp4.dvd_mul.mp h2 with h1' | h2'
      · have := hp4.dvd_of_dvd_pow h1'; have := Nat.le_of_dvd (by decide) this; omega
      · have := hp4.dvd_of_dvd_pow h2'; rcases hp3.eq_one_or_self_of_dvd p4 this with e1 | e2 <;> omega
  have heq1 : p4 ^ d' * u = 3 * 5 ^ b' * p3 ^ c' * p4 ^ d' := by dsimp [u]; ring
  have heq2 : p4 ^ (d' + 1) * u = 3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1) := by dsimp [u]; ring
  have hmono := properDivsSum_ratio_mono_4 hp3 hp4 h3 h4 hb' hc' hd'
  have hB0_eq : 3 * 5 ^ 1 * p3 ^ 1 * p4 ^ 1 = B0 := by dsimp [B0]; ring
  rw [hB0_eq] at hmono
  have hB0_le : B0 ≤ 3 * 5 ^ b' * p3 ^ c' * p4 ^ d' := by
    dsimp [B0]
    have h1 : 5 ≤ 5 ^ b' := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 5) hb'
    have h2 : p3 ≤ p3 ^ c' := by simpa using pow_le_pow_right₀ hp3.one_lt.le hc'
    have h3' : p4 ≤ p4 ^ d' := by simpa using pow_le_pow_right₀ hp4.one_lt.le hd'
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 3 h1) h2) h3'
  have hP_ge : P0 ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') := by nlinarith
  have h2L' : 2 * L ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') := le_trans hL_bound hP_ge
  have hPlb : (P0 - 2 * L) * (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') ≤
      (properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - 2 * L) * B0 :=
    sub_mul_le_sub_mul_of_mul_le hL_bound h2L' hB0_le hmono
  have hres := lift_prime_step_no_interleave (L := L) (g := g) hp4 hu_pos hd' hcop4 hg
    (by rw [heq1]; change L ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d'); omega)
    (by rw [heq1]; exact hcov) (by rw [heq1]; exact hgap)
    (by
      intro d hd
      have ha := habs d hd
      rw [heq1]
      have hC_bd : C * p4 ^ (d' + 1) ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - 2 * L := by
        apply Nat.le_of_mul_le_mul_right _ hB0pos
        have hm := Nat.mul_le_mul_right (p4 ^ d') hmargin
        have h1 : C * p4 * B0 * p4 ^ d' = C * p4 ^ (d' + 1) * B0 := by ring
        have h2 : (P0 - 2 * L) * u * p4 ^ d' = (P0 - 2 * L) * (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') := by dsimp [u]; ring
        rw [h1, h2] at hm
        exact le_trans hm hPlb
      have hmul := Nat.mul_le_mul_left (p4 ^ (d' + 1)) ha
      let S := ∑ e ∈ u.properDivisors.filter (· < d), e
      have hmul' : p4 ^ (d' + 1) * d ≤ C * p4 ^ (d' + 1) + p4 ^ (d' + 1) * S := by
        rw [mul_add, mul_comm (p4 ^ (d' + 1)) C] at hmul
        exact hmul
      change 2 * L + p4 ^ (d' + 1) * d ≤
        properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') + p4 ^ (d' + 1) * S + 1
      omega)
    (by
      have hPu : u ≤ p4 * properDivsSum u := by
        have hpos5 : 0 < 5 ^ b' * p3 ^ c' := by have := hp3.pos; positivity
        have hu3 : u = 3 * (5 ^ b' * p3 ^ c') := by dsimp [u]; ring
        have hmem : 5 ^ b' * p3 ^ c' ∈ u.properDivisors := Nat.mem_properDivisors.mpr
          ⟨⟨3, by rw [hu3]; ring⟩, by omega⟩
        have hle : 5 ^ b' * p3 ^ c' ≤ properDivsSum u :=
          Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hmem
        nlinarith
      have hmulp : p4 ^ d' * u ≤ p4 ^ (d' + 1) * properDivsSum u := by
        rw [show p4 ^ (d' + 1) * properDivsSum u = p4 ^ d' * (p4 * properDivsSum u) by ring]
        exact Nat.mul_le_mul_left _ hPu
      change 2 * L + p4 ^ d' * u ≤
        properDivsSum (p4 ^ d' * u) + p4 ^ (d' + 1) * properDivsSum u + 1
      rw [heq1]
      omega)
  simpa [heq2, properDivsSum] using hres

lemma hstep4_of_rel {p3 p4 L g a_num a_den b' c' d' : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (h3 : 5 < p3) (h4 : p3 < p4) (hg : 1 ≤ g)
    (hb' : 1 ≤ b') (hc' : 1 ≤ c') (hd' : 1 ≤ d')
    (hL_bound : 2 * L ≤ properDivsSum (3 * 5 * p3 * p4))
    (hrel : HasRelGap (3 * 5 ^ b' * p3 ^ c') a_num a_den)
    (hmargin : a_num * p4 * (3 * 5 * p3 * p4) ≤ a_den * (properDivsSum (3 * 5 * p3 * p4) - 2 * L))
    (hden_pos : 0 < a_den)
    (hcov : ∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - L →
      repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ d').properDivisors y)
    (hgap : ∀ k, k < properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') →
      ∃ i, repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ d').properDivisors i ∧ k < i + g ∧ i ≤ k) :
    (∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)) - L →
      repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)).properDivisors y) ∧
    (∀ k, k < properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)) →
      ∃ i, repNat (3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1)).properDivisors i ∧ k < i + g ∧ i ≤ k) := by
  let u := 3 * 5 ^ b' * p3 ^ c'
  let B0 := 3 * 5 * p3 * p4
  let P0 := properDivsSum B0
  have hu_pos : 0 < u := by have := hp3.pos; positivity
  have hB0pos : 0 < B0 := by have := hp3.pos; have := hp4.pos; positivity
  have hcop4 : ¬ p4 ∣ u := by
    intro h
    have : p4 ∣ 3 * (5 ^ b' * p3 ^ c') := by simpa [u, mul_assoc] using h
    rcases hp4.dvd_mul.mp this with h1 | h2
    · have := Nat.le_of_dvd (by decide) h1; omega
    · rcases hp4.dvd_mul.mp h2 with h1' | h2'
      · have := hp4.dvd_of_dvd_pow h1'; have := Nat.le_of_dvd (by decide) this; omega
      · have := hp4.dvd_of_dvd_pow h2'; rcases hp3.eq_one_or_self_of_dvd p4 this with e1 | e2 <;> omega
  have heq1 : p4 ^ d' * u = 3 * 5 ^ b' * p3 ^ c' * p4 ^ d' := by dsimp [u]; ring
  have heq2 : p4 ^ (d' + 1) * u = 3 * 5 ^ b' * p3 ^ c' * p4 ^ (d' + 1) := by dsimp [u]; ring
  have hmono := properDivsSum_ratio_mono_4 hp3 hp4 h3 h4 hb' hc' hd'
  have hB0_eq : 3 * 5 ^ 1 * p3 ^ 1 * p4 ^ 1 = B0 := by dsimp [B0]; ring
  rw [hB0_eq] at hmono
  have hB0_le : B0 ≤ 3 * 5 ^ b' * p3 ^ c' * p4 ^ d' := by
    dsimp [B0]
    have h1 : 5 ≤ 5 ^ b' := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 5) hb'
    have h2 : p3 ≤ p3 ^ c' := by simpa using pow_le_pow_right₀ hp3.one_lt.le hc'
    have h3' : p4 ≤ p4 ^ d' := by simpa using pow_le_pow_right₀ hp4.one_lt.le hd'
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 3 h1) h2) h3'
  have hP_ge : P0 ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') := by nlinarith
  have h2L' : 2 * L ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') := le_trans hL_bound hP_ge
  have hPlb : (P0 - 2 * L) * (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') ≤
      (properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - 2 * L) * B0 :=
    sub_mul_le_sub_mul_of_mul_le hL_bound h2L' hB0_le hmono
  have hres := lift_prime_step_no_interleave (L := L) (g := g) hp4 hu_pos hd' hcop4 hg
    (by rw [heq1]; change L ≤ properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d'); omega)
    (by rw [heq1]; exact hcov) (by rw [heq1]; exact hgap)
    (by
      intro d hd
      have hr := hrel d hd
      rw [heq1]
      have hterm : a_num * (p4 ^ (d' + 1) * u) ≤ a_den * (properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - 2 * L) := by
        apply Nat.le_of_mul_le_mul_right _ hB0pos
        have hm := Nat.mul_le_mul_right (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') hmargin
        calc a_num * (p4 ^ (d' + 1) * u) * B0
            = a_num * p4 * B0 * (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') := by dsimp [u]; ring
          _ ≤ a_den * (P0 - 2 * L) * (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') := hm
          _ = a_den * ((P0 - 2 * L) * (3 * 5 ^ b' * p3 ^ c' * p4 ^ d')) := by ring
          _ ≤ a_den * ((properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - 2 * L) * B0) :=
              Nat.mul_le_mul_left a_den hPlb
          _ = a_den * (properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - 2 * L) * B0 := by ring
      have hmul := Nat.mul_le_mul_left (p4 ^ (d' + 1)) hr
      let S := ∑ e ∈ u.properDivisors.filter (· < d), e
      have hle_den : a_den * (p4 ^ (d' + 1) * d) ≤
          a_den * (properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - 2 * L + p4 ^ (d' + 1) * S) := by
        calc a_den * (p4 ^ (d' + 1) * d)
            = p4 ^ (d' + 1) * (a_den * d) := by ring
          _ ≤ p4 ^ (d' + 1) * (a_num * u + a_den * S) := hmul
          _ = a_num * (p4 ^ (d' + 1) * u) + a_den * (p4 ^ (d' + 1) * S) := by ring
          _ ≤ a_den * (properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - 2 * L) + a_den * (p4 ^ (d' + 1) * S) :=
              Nat.add_le_add_right hterm _
          _ = a_den * (properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') - 2 * L + p4 ^ (d' + 1) * S) := by ring
      have hle := Nat.le_of_mul_le_mul_left hle_den hden_pos
      change 2 * L + p4 ^ (d' + 1) * d ≤
        properDivsSum (3 * 5 ^ b' * p3 ^ c' * p4 ^ d') + p4 ^ (d' + 1) * S + 1
      omega)
    (by
      have hPu : u ≤ p4 * properDivsSum u := by
        have hpos5 : 0 < 5 ^ b' * p3 ^ c' := by have := hp3.pos; positivity
        have hu3 : u = 3 * (5 ^ b' * p3 ^ c') := by dsimp [u]; ring
        have hmem : 5 ^ b' * p3 ^ c' ∈ u.properDivisors := Nat.mem_properDivisors.mpr
          ⟨⟨3, by rw [hu3]; ring⟩, by omega⟩
        have hle : 5 ^ b' * p3 ^ c' ≤ properDivsSum u :=
          Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hmem
        nlinarith
      have hmulp : p4 ^ d' * u ≤ p4 ^ (d' + 1) * properDivsSum u := by
        rw [show p4 ^ (d' + 1) * properDivsSum u = p4 ^ d' * (p4 * properDivsSum u) by ring]
        exact Nat.mul_le_mul_left _ hPu
      change 2 * L + p4 ^ d' * u ≤
        properDivsSum (p4 ^ d' * u) + p4 ^ (d' + 1) * properDivsSum u + 1
      rw [heq1]
      omega)
  simpa [heq2, properDivsSum] using hres

end CoreAll19

section Core19Table

lemma core_of_pair {p3 p4 L g P0 : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (h3 : 5 < p3) (h4 : p3 < p4) (hg : 1 ≤ g)
    (hP0 : P0 = 4 * 6 * (p3 + 1) * (p4 + 1) - 3 * 5 * p3 * p4)
    (hchk : checkCoreB (3 * 5 * p3 * p4) L g P0 (sqfreeProperDivs p3 p4) = true) :
    (∀ y, L ≤ y → y ≤ properDivsSum (3 * 5 * p3 * p4) - L →
      repNat (3 * 5 * p3 * p4).properDivisors y) ∧
    (∀ k, k < properDivsSum (3 * 5 * p3 * p4) →
      ∃ i, repNat (3 * 5 * p3 * p4).properDivisors i ∧ k < i + g ∧ i ≤ k) ∧
    (∀ x, x < L → x % 12 = 6 → repNat (3 * 5 * p3 * p4).properDivisors x) := by
  have hPeq : P0 = ∑ d ∈ (3 * 5 * p3 * p4).properDivisors, d := by
    rw [hP0, ← properDivsSum_sqfree hp3 hp4 h3 h4]; rfl
  simpa [properDivsSum, ← hPeq] using core_of_checkCoreB hg hPeq hchk

lemma core_pair_abs {p3 p4 L g P0 C : ℕ} {b c d : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (h3 : 5 < p3) (h4 : p3 < p4) (hg : 1 ≤ g)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hP0 : P0 = 4 * 6 * (p3 + 1) * (p4 + 1) - 3 * 5 * p3 * p4)
    (hL_bound : 2 * L ≤ P0)
    (hbig0 : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ P0)
    (hchk : checkCoreB (3 * 5 * p3 * p4) L g P0 (sqfreeProperDivs p3 p4) = true)
    (hrel5 : checkRelGapListB (3 * p3 * p4) (P0 - 2 * L) (5 * (3 * 5 * p3 * p4))
      (4 * (p3 + 1) * (p4 + 1) - 3 * p3 * p4) (sqfree3ProperDivs p3 p4) = true)
    (hrel3_base : checkRelGapListB (3 * 5 * p4) (P0 - 2 * L) (p3 * (3 * 5 * p3 * p4))
      (4 * 6 * (p4 + 1) - 3 * 5 * p4) (sqfree3ProperDivs 5 p4) = true)
    (hrel3_step : p3 * (3 * 5 * p3 * p4) * (3 * 5 * p4) ≤
      (P0 - 2 * L) * (5 * (3 * 5 * p4)) +
      p3 * (3 * 5 * p3 * p4) * (4 * 6 * (p4 + 1) - 3 * 5 * p4))
    (habs_all : ∀ b' c', 1 ≤ b' → 1 ≤ c' → HasAbsGap (3 * 5 ^ b' * p3 ^ c') C)
    (hmargin : C * p4 * (3 * 5 * p3 * p4) ≤ (P0 - 2 * L) * (3 * 5 * p3)) :
    let B := 3 * 5 ^ b * p3 ^ c * p4 ^ d
    (∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y) ∧
    (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + g ∧ i ≤ k) ∧
    (∀ x, x < L → x % 12 = 6 → repNat B.properDivisors x) ∧
    (2 * g + 1) * (2 * L + 8 * g + 8) ≤ properDivsSum B := by
  have hPeq : properDivsSum (3 * 5 * p3 * p4) = P0 := by
    rw [properDivsSum_sqfree hp3 hp4 h3 h4, hP0]
  have hP5 : properDivsSum (3 * p3 * p4) = 4 * (p3 + 1) * (p4 + 1) - 3 * p3 * p4 :=
    properDivsSum_sqfree3 hp3 hp4 (by omega) h4
  have hP3 : properDivsSum (3 * 5 * p4) = 4 * 6 * (p4 + 1) - 3 * 5 * p4 :=
    properDivsSum_sqfree3 (by decide) hp4 (by decide) (by omega)
  obtain ⟨hcov0, hgap0, hmod0⟩ := core_of_pair hp3 hp4 h3 h4 hg hP0 hchk
  apply lift_4prime_core hp3 hp4 h3 h4 hg hb hc hd
    (by rw [hPeq]; exact hL_bound) (by rw [hPeq]; exact hbig0)
    hcov0 hgap0 hmod0
    (by rw [hPeq]; exact hasRelGap_of_list (by have := hp3.pos; have := hp4.pos; positivity) hP5.symm hrel5)
    (by rw [hPeq]; exact hasRelGap_of_list (by have := hp4.pos; positivity) hP3.symm hrel3_base)
    (by rw [hPeq, hP3]; exact hrel3_step)
  intro b' c' d' hb' hc' hd' hcov hgap
  apply hstep4_of_abs hp3 hp4 h3 h4 hg hb' hc' hd'
    (by rw [hPeq]; exact hL_bound) (habs_all b' c' hb' hc')
  · rw [hPeq]
    have h1 : 3 * 5 * p3 ≤ 3 * 5 ^ b' * p3 ^ c' := by
      have ha1 : 5 ≤ 5 ^ b' := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 5) hb'
      have ha2 : p3 ≤ p3 ^ c' := by simpa using pow_le_pow_right₀ hp3.one_lt.le hc'
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 3 ha1) ha2
    exact le_trans hmargin (Nat.mul_le_mul_left _ h1)
  · exact hcov
  · exact hgap

lemma core_pair_7_large {p4 L P0 : ℕ} {b c d : ℕ}
    (hp4 : p4.Prime) (hrlo : 47 ≤ p4) (hrhi : p4 ≤ 67)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hP0 : P0 = 4 * 6 * 8 * (p4 + 1) - 3 * 5 * 7 * p4)
    (hL_bound : 2 * L ≤ P0) (hL_small : 2 * L ≤ 3 * p4)
    (hbig0 : 5 * (2 * L + 24) ≤ P0)
    (hP_ratio0 : 89 * p4 ≤ P0)
    (hchk : checkCoreB (3 * 5 * 7 * p4) L 2 P0 (sqfreeProperDivs 7 p4) = true)
    (hrel5 : checkRelGapListB (3 * 7 * p4) (P0 - 2 * L) (5 * (3 * 5 * 7 * p4))
      (4 * 8 * (p4 + 1) - 3 * 7 * p4) (sqfree3ProperDivs 7 p4) = true)
    (hrel3_base : checkRelGapListB (3 * 5 * p4) (P0 - 2 * L) (7 * (3 * 5 * 7 * p4))
      (4 * 6 * (p4 + 1) - 3 * 5 * p4) (sqfree3ProperDivs 5 p4) = true)
    (hrel3_step : 7 * (3 * 5 * 7 * p4) * (3 * 5 * p4) ≤
      (P0 - 2 * L) * (5 * (3 * 5 * p4)) +
      7 * (3 * 5 * 7 * p4) * (4 * 6 * (p4 + 1) - 3 * 5 * p4))
    (hmargin525 : 2 * p4 * (3 * 5 * 7 * p4) ≤ (P0 - 2 * L) * 525) :
    let B := 3 * 5 ^ b * 7 ^ c * p4 ^ d
    (∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y) ∧
    (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + 2 ∧ i ≤ k) ∧
    (∀ x, x < L → x % 12 = 6 → repNat B.properDivisors x) ∧
    5 * (2 * L + 24) ≤ properDivsSum B := by
  have hp7 : Nat.Prime 7 := by decide
  have hPeq : properDivsSum (3 * 5 * 7 * p4) = P0 := by
    rw [properDivsSum_sqfree hp7 hp4 (by decide) (by omega), hP0]
  have hP5 : properDivsSum (3 * 7 * p4) = 4 * 8 * (p4 + 1) - 3 * 7 * p4 :=
    properDivsSum_sqfree3 hp7 hp4 (by decide) (by omega)
  have hP3 : properDivsSum (3 * 5 * p4) = 4 * 6 * (p4 + 1) - 3 * 5 * p4 :=
    properDivsSum_sqfree3 (by decide) hp4 (by decide) (by omega)
  obtain ⟨hcov0, hgap0, hmod0⟩ := core_of_pair hp7 hp4 (by decide) (by omega) (by decide) hP0 hchk
  apply lift_4prime_core hp7 hp4 (by decide) (by omega) (by decide) hb hc hd
    (by rw [hPeq]; exact hL_bound) (by rw [hPeq]; exact hbig0)
    hcov0 hgap0 hmod0
    (by rw [hPeq]; exact hasRelGap_of_list (by have := hp4.pos; positivity) hP5.symm hrel5)
    (by rw [hPeq]; exact hasRelGap_of_list (by have := hp4.pos; positivity) hP3.symm hrel3_base)
    (by rw [hPeq, hP3]; exact hrel3_step)
  intro b' c' d' hb' hc' hd' hcov hgap
  by_cases h11 : b' = 1 ∧ c' = 1
  · rcases h11 with ⟨rfl, rfl⟩
    have heq1 : p4 ^ d' * 105 = 3 * 5 ^ 1 * 7 ^ 1 * p4 ^ d' := by ring
    have heq2 : p4 ^ (d' + 1) * 105 = 3 * 5 ^ 1 * 7 ^ 1 * p4 ^ (d' + 1) := by ring
    have hL_le : 2 * L ≤ 3 * p4 ^ d' := by
      have : p4 ≤ p4 ^ d' := by simpa using pow_le_pow_right₀ hp4.one_lt.le hd'
      omega
    have hP_rat : 89 * p4 ^ d' ≤ properDivsSum (p4 ^ d' * 105) := by
      have hmono := properDivsSum_ratio_mono_4 (b0 := 1) (c0 := 1) (d0 := 1) (b := 1) (c := 1) (d := d')
        hp7 hp4 (by decide) (by omega) le_rfl le_rfl hd'
      have hB0_eq : 3 * 5 ^ 1 * 7 ^ 1 * p4 ^ 1 = 3 * 5 * 7 * p4 := by ring
      rw [hB0_eq, hPeq, ← heq1] at hmono
      have h1 : 3 * 5 * 7 * p4 = p4 * 105 := by ring
      rw [h1] at hmono
      have hpos : 0 < p4 := hp4.pos
      have h2 : p4 * (89 * p4 ^ d') ≤ p4 * properDivsSum (p4 ^ d' * 105) := by
        have h3 : P0 * (p4 ^ d' * 105) = 105 * (P0 * p4 ^ d') := by ring
        have h4 : properDivsSum (p4 ^ d' * 105) * (p4 * 105) = 105 * (p4 * properDivsSum (p4 ^ d' * 105)) := by ring
        have h5 : P0 * p4 ^ d' ≤ p4 * properDivsSum (p4 ^ d' * 105) := by linarith
        nlinarith
      exact Nat.le_of_mul_le_mul_left h2 hpos
    have hres := lift_prime_step_105 (L := L) (g := 2) hp4 hrlo hrhi hd' (by decide) hL_le hP_rat
      (by rw [heq1]; exact hcov) (by rw [heq1]; exact hgap)
    simpa [heq2] using hres
  · have h525 : 525 ≤ 3 * 5 ^ b' * 7 ^ c' := by
      have hge : 2 ≤ b' ∨ 2 ≤ c' := by omega
      rcases hge with hb2 | hc2
      · have h1 : 25 ≤ 5 ^ b' := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 5) hb2
        have h2 : 7 ≤ 7 ^ c' := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 7) hc'
        nlinarith
      · have h1 : 5 ≤ 5 ^ b' := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 5) hb'
        have h2 : 49 ≤ 7 ^ c' := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 7) hc2
        nlinarith
    apply hstep4_of_abs hp7 hp4 (by decide) (by omega) (by decide) hb' hc' hd'
      (by rw [hPeq]; exact hL_bound) (hasAbsGap_3_5_7 hb' hc')
    · rw [hPeq]; exact le_trans hmargin525 (Nat.mul_le_mul_left _ h525)
    · exact hcov
    · exact hgap

def pairL (p3 p4 : ℕ) : ℕ :=
  if p3 = 7 then
    if p4 = 11 ∨ p4 = 13 then 3
    else if p4 = 17 then 15
    else if p4 = 37 then 108
    else if p4 = 53 then 71
    else if p4 = 59 then 74
    else 18
  else if p3 = 11 then
    if p4 = 13 then 11 else 14
  else 28

def pairG (p3 : ℕ) : ℕ :=
  if p3 = 13 then 4 else 2

def validPairs19 : Finset (ℕ × ℕ) :=
  {(7,11),(7,13),(7,17),(7,19),(7,23),(7,29),(7,31),
   (7,37),(7,41),(7,43),(7,47),(7,53),(7,59),(7,61),(7,67),
   (11,13),(11,17),(11,19),(13,17)}

set_option maxHeartbeats 1600000 in
lemma core_19_pairs {p3 p4 b c d : ℕ}
    (hmem : (p3, p4) ∈ validPairs19) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    let L := pairL p3 p4
    let g := pairG p3
    let B := 3 * 5 ^ b * p3 ^ c * p4 ^ d
    (∀ y, L ≤ y → y ≤ properDivsSum B - L → repNat B.properDivisors y) ∧
    (∀ k, k < properDivsSum B → ∃ i, repNat B.properDivisors i ∧ k < i + g ∧ i ≤ k) ∧
    (∀ x, x < L → x % 12 = 6 → repNat B.properDivisors x) ∧
    (2 * g + 1) * (2 * L + 8 * g + 8) ≤ properDivsSum B := by
  simp only [validPairs19, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact core_pair_abs (P0 := 1149) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_7 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 1323) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_7 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 1671) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_7 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 1845) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_7 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 2193) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_7 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 2715) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_7 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 2889) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_7 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 3411) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_7 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 3759) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_7 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 3933) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_7 hb' hc') (by decide)
  · exact core_pair_7_large (P0 := 4281) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact core_pair_7_large (P0 := 4803) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact core_pair_7_large (P0 := 5325) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact core_pair_7_large (P0 := 5499) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact core_pair_7_large (P0 := 6021) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact core_pair_abs (P0 := 1887) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_11 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 2379) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_11 hb' hc') (by decide)
  · exact core_pair_abs (P0 := 2625) (C := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      hb hc hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun b' c' hb' hc' => hasAbsGap_3_5_11 hb' hc') (by decide)
  · -- (13, 17): L = 28, g = 4, P0 = 2733
    have hp13 : Nat.Prime 13 := by decide
    have hp17 : Nat.Prime 17 := by decide
    have hPeq : properDivsSum (3 * 5 * 13 * 17) = 2733 := by
      rw [properDivsSum_sqfree hp13 hp17 (by decide) (by decide)]
    have hP5 : properDivsSum (3 * 13 * 17) = 345 := by
      rw [properDivsSum_sqfree3 hp13 hp17 (by decide) (by decide)]
    have hP3 : properDivsSum (3 * 5 * 17) = 177 := by
      rw [properDivsSum_sqfree3 (by decide) hp17 (by decide) (by decide)]
    obtain ⟨hcov0, hgap0, hmod0⟩ := core_of_pair (p3 := 13) (p4 := 17) (L := 28) (g := 4) (P0 := 2733)
      hp13 hp17 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hrel5_13 : HasRelGap (3 * 13 * 17) (properDivsSum (3 * 5 * 13 * 17) - 2 * 28) (5 * (3 * 5 * 13 * 17)) := by
      rw [hPeq]
      exact hasRelGap_of_list (u := 3 * 13 * 17) (P_u := 345) (ds := sqfree3ProperDivs 13 17)
        (by decide) hP5.symm (by decide)
    have hrel3_13 : HasRelGap (3 * 5 * 17) (properDivsSum (3 * 5 * 13 * 17) - 2 * 28) (13 * (3 * 5 * 13 * 17)) := by
      rw [hPeq]
      exact hasRelGap_of_list (u := 3 * 5 * 17) (P_u := 177) (ds := sqfree3ProperDivs 5 17)
        (by decide) hP3.symm (by decide)
    apply lift_4prime_core (L := 28) (g := 4) hp13 hp17 (by decide) (by decide) (by decide) hb hc hd
      (by rw [hPeq]; decide) (by rw [hPeq]; decide) hcov0 hgap0 hmod0
      hrel5_13 hrel3_13 (by rw [hPeq, hP3]; decide)
    intro b' c' d' hb' hc' hd' hcov hgap
    by_cases hb1 : b' = 1
    · subst hb1
      apply hstep4_of_rel (a_num := 1) (a_den := 40) hp13 hp17 (by decide) (by decide) (by decide)
        le_rfl hc' hd' (by rw [hPeq]; decide)
        (by simpa using hasRelGap_3_5_13 hc') (by rw [hPeq]; decide) (by decide) hcov hgap
    · have hb2 : 2 ≤ b' := by omega
      apply hstep4_of_abs (C := 4) hp13 hp17 (by decide) (by decide) (by decide)
        hb' hc' hd' (by rw [hPeq]; decide) (hasAbsGap_3_25_13 hb2 hc')
      · rw [hPeq]
        have h1 : 25 ≤ 5 ^ b' := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 5) hb2
        have h2 : 13 ≤ 13 ^ c' := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 13) hc'
        have h975 : 975 ≤ 3 * 5 ^ b' * 13 ^ c' := by nlinarith
        nlinarith
      · exact hcov
      · exact hgap

end Core19Table

section CertData

def cert_7_37 : Cert := (.tq 1295 (.pcs [5,2,3,2] (.sp 1 (.tq 47 (.pt (.pcs [2,3,2] (.sp 0 .pd (.sp 0 (.pt (.pcs [2] (.ld 1 none)) (.sp 2 .pd (.ld 2 none))) (.ld 1 (some (0,3)))))) (.sp 0 .pd (.sp 0 .pd (.sp 2 .pd (.sp 0 .pd (.ld 2 none))))))) (.sp 0 (.tq 114 (.pcs [2] (.sp 1 (.tq 85 (.pcs [5,2] (.sp 2 (.tq 80 (.pcs [2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,5)))))) (.sp 2 (.tq 105 (.pcs [3,2] (.sp 1 (.tq 100 (.pcs [2,3,2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2)))))) (.sp 1 (.tq 108 (.pcs [2] (.ld 1 (some (0,2))))) (.sp 1 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.sp 2 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.sp 1 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2))))))))))) (.sp 1 (.tq 271 (.pt (.pcs [2] (.sp 0 (.tq 189 (.pcs [3,2,11,2,5,2,3,2] (.sp 2 (.tq 166 (.pcs [2,3,2] (.ld 1 none))) (.ld 1 none)))) (.sp 2 (.tq 226 (.pcs [2,3,2] (.sp 0 (.tq 211 (.pt (.pcs [2,11,2,3,2,5,2,7,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0))))) (.sp 0 (.pt (.pcs [2,13,2,3,2,7,2,5,2,3,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 (some (0,3))))))) (.sp 0 (.tq 249 (.pcs [3,2,13,2,5,2,3,2] (.ld 1 (some (0,2))))) (.sp 0 (.tq 266 (.pcs [2,5,2] (.ld 1 none))) (.sp 2 (.pt (.pcs [2,3,2,5,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2))))))))) (.sp 0 .pd (.sp 2 .pd (.sp 0 .pd (.sp 0 .pd (.sp 2 .pd (.sp 0 .pd (.ld 2 none))))))))) (.sp 0 (.tq 421 (.pt (.pcs [2] (.sp 2 (.tq 322 (.pcs [2,3,2,11,2] (.sp 1 (.tq 284 (.pcs [2] (.ld 1 none))) (.sp 1 (.tq 316 (.pcs [2,3,2] (.ld 1 none))) (.ld 1 none))))) (.sp 1 (.tq 358 (.pcs [2,3,2,5,2] (.ld 1 none))) (.sp 1 (.tq 411 (.pcs [3,2] (.sp 2 (.tq 408 (.pcs [2,11,2,3,2,13,2] (.ld 1 none))) (.ld 1 none)))) (.sp 2 (.tq 418 (.pcs [2,3,2,5,2,7,2,3,2] (.ld 1 none))) (.ld 1 none)))))) (.sp 2 .pd (.sp 1 .pd (.sp 1 .pd (.sp 2 .pd (.sp 1 .pd (.ld 2 none)))))))) (.sp 2 (.tq 665 (.pcs [5,2,3,2] (.sp 1 (.tq 521 (.pt (.pcs [2,3,2,11,2,5,2,3,2,7,2] (.sp 0 (.tq 447 (.pcs [3,2,5,2] (.ld 1 (some (0,3))))) (.sp 0 (.tq 504 (.pcs [2] (.ld 1 none))) (.ld 1 (some (0,2)))))) (.sp 0 .pd (.sp 0 .pd (.sp 0 .pd (.sp 0 .pd (.ld 2 (some (2,0))))))))) (.sp 0 (.tq 549 (.pcs [3,2] (.sp 1 (.tq 531 (.pcs [3,2,23,2,17,2,3,2] (.ld 1 (some (0,3))))) (.sp 1 (.tq 546 (.pcs [2,5,2,3,2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2))))))) (.sp 0 (.tq 638 (.pcs [2,7,2,5,2,3,2] (.sp 1 (.tq 615 (.pcs [3,2] (.ld 1 none))) (.ld 1 none)))) (.sp 1 (.tq 640 (.pcs [2,3,2,7,2,5,2,3,2] (.ld 1 (some (0,5))))) (.sp 0 (.tq 660 (.pcs [2] (.sp 1 (.tq 656 (.pcs [2,5,2] (.ld 1 (some (0,2))))) (.sp 1 (.pt (.pcs [2,3,2,5,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2))))))) (.sp 1 (.sp 0 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none)) (.ld 1 (some (0,2)))) (.ld 1 none))))))))) (.sp 1 (.tq 841 (.pcs [29,2] (.sp 0 (.tq 663 (.pcs [3,2] (.sp 2 (.tq 654 (.pcs [2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,3)))))) (.sp 0 (.tq 798 (.pcs [2] (.sp 2 (.tq 786 (.pcs [2,5,2,3,2,11,2,19,2,3,2,5,2] (.ld 1 none))) (.ld 1 none)))) (.sp 2 (.tq 828 (.pcs [2] (.sp 0 (.tq 819 (.pcs [3,2,19,2,5,2,3,2] (.ld 1 (some (0,3))))) (.sp 0 (.tq 826 (.pcs [2,3,2] (.ld 1 none))) (.sp 0 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none)))))) (.sp 0 (.tq 832 (.pcs [2,3,2] (.ld 1 (some (0,2))))) (.sp 0 (.sp 2 (.pt (.pcs [2,3,2,5,2,7,2,3,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none)) (.ld 1 (some (0,29)))))))))) (.sp 0 (.tq 916 (.pcs [2,3,2,11,2] (.sp 1 (.tq 868 (.pcs [2,3,2,5,2] (.sp 2 (.tq 854 (.pcs [2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2)))))) (.sp 2 (.tq 900 (.pcs [2,29,2,3,2,5,2,19,2,3,2,7,2] (.ld 1 (some (0,19))))) (.sp 1 (.tq 909 (.pcs [3,2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2)))))))) (.sp 0 (.tq 1196 (.pcs [2,5,2] (.sp 1 (.tq 1117 (.pt (.pcs [2,5,2,3,2,11,2] (.sp 2 (.tq 1093 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none))) (.ld 1 none))) (.sp 2 .pd (.sp 2 .pd (.ld 2 none))))) (.sp 2 (.tq 1169 (.pcs [7,2,3,2,5,2] (.sp 1 (.tq 1157 (.pcs [13,2,3,2] (.ld 1 none))) (.ld 1 none)))) (.sp 1 (.tq 1184 (.pcs [2,7,2] (.ld 1 none))) (.ld 1 none)))))) (.sp 1 (.tq 1203 (.pcs [3,2] (.sp 2 (.tq 1175 (.pcs [5,2,3,2] (.sp 0 (.tq 1157 (.pcs [13,2,3,2] (.ld 1 (some (0,13))))) (.sp 0 (.pt (.pcs [2,7,2,3,2,5,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 (some (0,2))))))) (.sp 0 (.tq 1185 (.pcs [3,2,7,2] (.ld 1 (some (0,2))))) (.sp 0 (.tq 1199 (.pcs [11,2,3,2,5,2] (.ld 1 none))) (.sp 2 (.sp 0 (.pt (.pcs [2,11,2,3,2,5,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none)) (.ld 1 (some (0,2))))))))) (.sp 2 (.tq 1263 (.pcs [3,2,13,2] (.sp 0 (.tq 1243 (.pcs [11,2,17,2,3,2] (.sp 1 (.tq 1230 (.pcs [2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,17)))))) (.sp 1 (.tq 1250 (.pcs [2] (.sp 0 (.tq 1246 (.pcs [2,3,2,11,2,17,2,3,2] (.ld 1 none))) (.sp 0 (.pt (.pcs [2,29,2,3,2,11,2,17,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none))))) (.sp 0 (.pt (.pcs [2,3,2,5,2,7,2,3,2] (.ld 1 none)) (.sp 1 .pd (.ld 2 none))) (.ld 1 (some (0,2)))))))) (.sp 0 (.tq 1274 (.pcs [2,19,2,31,2,3,2,7,2,5,2,3,2,13,2] (.ld 1 (some (0,2))))) (.sp 1 (.tq 1281 (.pcs [3,2] (.sp 0 (.tq 1277 (.pt (.pcs [2,3,2,19,2,31,2,3,2,7,2,5,2,3,2,13,2] (.ld 1 none)) (.sp 2 .pd (.ld 2 none)))) (.ld 1 (some (0,2)))))) (.sp 0 (.pt (.pcs [2] (.sp 1 (.pt (.pcs [2,3,2,5,2] (.ld 1 none)) (.sp 2 .pd (.ld 2 none))) (.ld 1 none))) (.sp 1 .pd (.sp 2 .pd (.ld 2 none)))) (.ld 1 (some (0,2))))))))))))))))))
def cert_7_41 : Cert := (.tq 287 (.pcs [7,2,3,2] (.sp 1 .pd (.sp 0 (.tq 87 (.pcs [3,2,5,2] (.sp 1 (.tq 69 (.pcs [3,2] (.sp 2 (.pt (.pcs [2,5,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,3)))))) (.sp 2 (.pt (.pcs [2,3,2] (.ld 1 (some (0,2)))) (.sp 1 .pd (.sp 1 .pd (.ld 2 (some (2,0)))))) (.ld 1 (some (0,2))))))) (.sp 1 (.tq 156 (.pcs [2,5,2,3,2] (.sp 0 (.tq 125 (.pcs [5,2,3,2,11,2,7,2,3,2,5,2] (.ld 1 none))) (.sp 2 (.tq 143 (.pcs [11,2,3,2] (.sp 0 (.tq 137 (.pt (.pcs [2,3,2,7,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0))))) (.ld 1 none)))) (.sp 0 (.tq 149 (.pt (.pcs [2,3,2,5,2,11,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0))))) (.ld 1 none)))))) (.sp 0 (.tq 197 (.pt (.pcs [2,3,2] (.sp 2 (.tq 176 (.pcs [2,5,2] (.sp 1 (.tq 164 (.pcs [2] (.ld 1 none))) (.ld 1 none)))) (.sp 1 (.tq 182 (.pcs [2] (.sp 2 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none)))) (.ld 1 none)))) (.sp 2 .pd (.sp 1 .pd (.sp 1 .pd (.sp 2 .pd (.ld 2 none))))))) (.sp 2 (.tq 245 (.pcs [5,2,3,2] (.sp 1 (.tq 223 (.pt (.pcs [2,13,2,3,2,7,2,5,2,3,2] (.sp 0 (.tq 208 (.pcs [2,3,2,5,2,7,2,3,2] (.ld 1 (some (0,2))))) (.ld 1 none))) (.sp 0 .pd (.sp 0 .pd (.sp 0 .pd (.ld 2 none)))))) (.sp 0 (.tq 228 (.pcs [2] (.sp 1 (.tq 225 (.pcs [3,2] (.ld 1 (some (0,3))))) (.sp 1 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2))))))) (.sp 0 (.sp 1 (.tq 238 (.pcs [2,3,2,5,2] (.ld 1 none))) (.sp 1 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none))) (.sp 1 (.sp 0 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none)) (.ld 1 (some (0,2))))))))) (.sp 1 (.tq 257 (.pt (.pcs [2,3,2,11,2] (.sp 0 (.tq 237 (.pcs [3,2,5,2] (.ld 1 (some (0,2))))) (.ld 1 none))) (.sp 0 .pd (.sp 0 .pd (.sp 2 .pd (.sp 0 .pd (.ld 2 none))))))) (.sp 0 (.tq 263 (.pt (.pcs [2,3,2,7,2] (.ld 1 (some (0,2)))) (.sp 1 .pd (.sp 2 .pd (.ld 2 (some (2,0))))))) (.sp 0 (.tq 282 (.pcs [2] (.sp 1 (.tq 278 (.pcs [2] (.sp 2 (.pt (.pcs [2,5,2,3,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none)))) (.sp 2 (.pt (.pcs [2,3,2] (.ld 1 none)) (.sp 1 .pd (.ld 2 none))) (.ld 1 none))))) (.sp 1 (.pt (.pcs [2] (.sp 2 (.sp 0 (.tq 280 (.pcs [2,3,2] (.ld 1 (some (0,2))))) (.sp 0 (.pt (.pcs [2,3,2] (.ld 1 none)) (.ld 2 none)) (.sp 0 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none)))) (.ld 1 (some (0,2))))) (.sp 2 .pd (.sp 0 .pd (.sp 0 .pd (.ld 2 (some (2,0))))))) (.ld 1 (some (0,3))))))))))))))
def cert_7_43 : Cert := (.tq 215 (.pcs [5,2,3,2] (.sp 1 .pd (.sp 0 (.tq 79 (.pt (.pcs [2,7,2,3,2] (.sp 1 (.tq 64 (.pcs [2,3,2] (.ld 1 (some (0,2))))) (.sp 2 (.sp 1 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,3)))) (.ld 1 (some (0,2)))))) (.sp 1 .pd (.sp 2 .pd (.sp 1 .pd (.sp 1 (.sp 2 .pd (.ld 2 (some (2,0)))) (.ld 2 (some (2,0))))))))) (.sp 1 (.tq 132 (.pcs [2] (.sp 0 (.tq 109 (.pt (.pcs [2] (.sp 2 (.tq 103 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none))) (.ld 1 none))) (.sp 2 .pd (.ld 2 none)))) (.sp 2 (.tq 123 (.pcs [3,2,11,2,7,2,3,2,5,2] (.ld 1 (some (0,7))))) (.sp 0 (.tq 127 (.pt (.pcs [2,5,2,3,2,11,2,7,2,3,2,5,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0))))) (.sp 0 (.pt (.pcs [2,3,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 (some (0,2))))))))) (.sp 0 (.tq 160 (.pcs [2,3,2] (.sp 2 (.tq 147 (.pcs [3,2,5,2,11,2,3,2] (.sp 1 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none)))) (.sp 1 (.tq 150 (.pcs [2] (.ld 1 none))) (.ld 1 none))))) (.sp 2 (.tq 193 (.pt (.pcs [2] (.sp 1 (.tq 179 (.pt (.pcs [2,3,2,5,2] (.sp 0 (.tq 169 (.pcs [13,2] (.ld 1 (some (0,13))))) (.ld 1 none))) (.sp 0 .pd (.sp 0 .pd (.sp 0 .pd (.ld 2 none)))))) (.sp 0 (.tq 182 (.pcs [2] (.sp 1 (.tq 180 (.pcs [2] (.ld 1 (some (0,2))))) (.sp 1 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2))))))) (.sp 0 (.pt (.pcs [2,3,2,11,2,5,2,3,2] (.ld 1 none)) (.sp 1 .pd (.sp 1 .pd (.ld 2 none)))) (.sp 1 (.pt (.pcs [2,3,2,11,2,5,2,3,2] (.ld 1 (some (0,2)))) (.sp 0 .pd (.ld 2 none))) (.ld 1 (some (0,2)))))))) (.sp 1 .pd (.sp 0 .pd (.sp 0 .pd (.sp 1 .pd (.sp 0 (.sp 1 .pd (.sp 1 .pd (.ld 2 (some (2,0))))) (.ld 2 none)))))))) (.sp 1 (.tq 198 (.pcs [2] (.sp 0 (.tq 186 (.pcs [2,5,2,3,2] (.ld 1 (some (0,2))))) (.sp 0 (.tq 195 (.pcs [3,2] (.ld 1 none))) (.sp 0 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.sp 2 (.pt (.pcs [2,3,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none))))))) (.sp 0 (.tq 202 (.pcs [2,3,2] (.sp 1 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,3)))))) (.sp 0 (.sp 1 (.tq 210 (.pcs [2,11,2,3,2,5,2,7,2,3,2] (.ld 1 none))) (.ld 1 none)) (.ld 1 (some (0,2)))))))))))))
def cert_7_47 : Cert := (.pcs [2] (.sp 1 .pd (.sp 0 (.tq 68 (.pcs [2] (.sp 1 (.tq 57 (.pcs [3,2,5,2] (.ld 1 (some (0,5))))) (.sp 2 (.tq 66 (.pcs [2,5,2,3,2] (.ld 1 (some (0,2))))) (.sp 1 (.tq 66 (.pcs [2,5,2,3,2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2)))))))) (.sp 1 (.tq 104 (.pcs [2] (.sp 0 (.tq 89 (.pt (.pcs [2,3,2,5,2] (.ld 1 none)) (.sp 2 .pd (.ld 2 none)))) (.sp 2 (.tq 100 (.pcs [2,3,2] (.sp 0 (.pt (.pcs [2,5,2,3,2,7,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none)))) (.sp 0 (.tq 101 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0))))) (.ld 1 none)))))) (.sp 0 (.tq 121 (.pcs [11,2,7,2,3,2,5,2] (.sp 2 (.sp 1 (.tq 109 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none))) (.ld 1 none)) (.ld 1 none)))) (.sp 2 (.tq 140 (.pcs [2] (.sp 1 (.tq 133 (.pcs [7,2] (.sp 0 (.tq 127 (.pt (.pcs [2,5,2,3,2,11,2,7,2,3,2,5,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0))))) (.ld 1 none)))) (.sp 0 (.tq 134 (.pcs [2,7,2] (.ld 1 (some (0,7))))) (.sp 0 (.pt (.pcs [2] (.ld 1 none)) (.sp 1 .pd (.ld 2 none))) (.sp 1 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2))))))))) (.sp 1 (.tq 141 (.pcs [3,2] (.sp 0 (.tq 135 (.pcs [3,2,7,2] (.ld 1 (some (0,3))))) (.ld 1 none)))) (.sp 0 (.tq 143 (.pcs [11,2,3,2] (.ld 1 (some (0,2))))) (.sp 0 (.pt (.pcs [2,3,2,5,2,11,2,3,2] (.ld 1 none)) (.sp 1 .pd (.sp 2 .pd (.sp 1 .pd (.ld 2 none))))) (.sp 1 (.pt (.pcs [2,3,2,5,2,11,2,3,2] (.ld 1 (some (0,2)))) (.sp 0 .pd (.sp 2 (.sp 0 .pd (.sp 0 .pd (.ld 3 none))) (.ld 2 none)))) (.sp 0 (.sp 2 (.sp 1 (.pt (.pcs [2,3,2,5,2,11,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2)))) (.ld 1 (some (0,2)))) (.ld 1 none))))))))))))
def cert_7_53 : Cert := (.pcs [2] (.sp 1 .pd (.sp 0 .pd (.sp 1 (.tq 83 (.pt (.pcs [2,3,2] (.sp 0 (.tq 73 (.pt (.pcs [2] (.sp 2 (.pt (.pcs [2,3,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none))) (.sp 2 .pd (.ld 2 none)))) (.sp 2 (.sp 0 (.pt (.pcs [2,7,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none)) (.ld 1 (some (0,3)))))) (.sp 0 .pd (.sp 2 .pd (.sp 0 .pd (.ld 2 none)))))) (.sp 0 (.tq 93 (.pcs [3,2,7,2] (.sp 1 (.sp 2 (.tq 87 (.pcs [3,2,5,2] (.ld 1 none))) (.ld 1 none)) (.ld 1 none)))) (.sp 1 (.tq 105 (.pcs [3,2] (.sp 2 (.tq 101 (.pt (.pcs [2,3,2] (.ld 1 (some (0,2)))) (.sp 0 .pd (.sp 0 .pd (.ld 2 (some (2,0))))))) (.sp 0 (.tq 101 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0))))) (.ld 1 none))))) (.sp 2 (.tq 105 (.pcs [3,2] (.sp 0 (.tq 102 (.pcs [2] (.sp 1 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2)))))) (.ld 1 none)))) (.sp 0 (.tq 106 (.pcs [2,3,2] (.ld 1 (some (0,3))))) (.sp 0 (.pt (.pcs [2] (.ld 1 none)) (.sp 1 .pd (.ld 2 none))) (.sp 1 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.sp 0 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.sp 1 (.sp 2 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none)) (.sp 0 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none)) (.ld 1 (some (0,2))))) (.sp 2 (.sp 0 (.sp 1 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none)) (.ld 1 (some (0,2)))) (.ld 1 none))))))))))))))
def cert_7_59 : Cert := (.pcs [2] (.sp 1 .pd (.sp 0 .pd (.sp 1 (.tq 71 (.pt (.pcs [2,3,2] (.sp 0 (.tq 64 (.pcs [2,3,2] (.ld 1 none))) (.ld 1 (some (0,2))))) (.sp 0 .pd (.sp 0 .pd (.sp 2 .pd (.ld 2 none)))))) (.sp 0 (.tq 79 (.pt (.pcs [2,7,2,3,2] (.ld 1 none)) (.sp 1 .pd (.sp 2 .pd (.sp 1 (.sp 2 .pd (.ld 3 none)) (.ld 2 none)))))) (.sp 1 (.tq 87 (.pcs [3,2,5,2] (.sp 0 (.sp 2 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,5)))) (.ld 1 none)))) (.sp 0 (.tq 88 (.pcs [2,3,2,5,2] (.ld 1 (some (0,5))))) (.sp 2 (.tq 88 (.pcs [2,3,2,5,2] (.ld 1 none))) (.sp 0 (.sp 1 (.pt (.pcs [2,3,2,5,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none)) (.ld 1 (some (0,2))))))))))))
def cert_7_61 : Cert := (.pcs [2,5,2] (.sp 1 .pd (.sp 0 .pd (.sp 1 (.tq 69 (.pcs [3,2] (.sp 0 .pd (.sp 0 (.sp 2 .pd (.ld 2 (some (2,0)))) (.sp 2 (.ld 2 none) (.ld 1 none)))))) (.sp 0 (.tq 76 (.pcs [2,3,2] (.sp 1 (.pt (.pcs [2] (.ld 1 none)) (.sp 2 .pd (.ld 2 none))) (.ld 1 none)))) (.sp 1 (.pt (.pcs [2,3,2] (.sp 0 (.sp 2 (.pt (.pcs [2,7,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,3)))) (.ld 1 none))) (.sp 0 .pd (.sp 2 .pd (.sp 0 .pd (.ld 2 (some (2,0))))))) (.sp 0 (.sp 2 (.tq 82 (.pcs [2,3,2] (.ld 1 (some (0,3))))) (.sp 1 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2))))) (.sp 2 (.sp 0 (.sp 1 (.pt (.pcs [2,3,2] (.ld 1 none)) (.ld 2 none)) (.sp 1 (.pt (.pcs [2,3,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none))) (.sp 1 (.sp 0 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none)) (.ld 1 (some (0,2))))) (.ld 1 none)))))))))
def cert_7_67 : Cert := (.pcs [2,3,2] (.sp 1 .pd (.sp 0 .pd (.sp 1 .pd (.sp 0 .pd (.sp 1 (.sp 0 (.tq 72 (.pcs [2] (.sp 2 (.ld 2 (some (2,0))) (.ld 1 (some (0,2)))))) (.sp 2 (.pt (.pcs [2] (.ld 1 none)) (.sp 0 .pd (.ld 2 (some (2,0))))) (.sp 0 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none)) (.ld 1 (some (0,2)))))) (.sp 0 (.sp 2 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2)))) (.ld 1 none))))))))
def cert_11_13 : Cert := (.tq 143 (.pcs [11,2,3,2] (.sp 1 (.tq 65 (.pcs [5,2,3,2] (.sp 0 (.tq 43 (.pt (.pcs [2] (.sp 2 (.tq 34 (.pcs [2,3,2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2))))) (.sp 2 .pd (.sp 2 .pd (.ld 2 (some (2,0))))))) (.sp 2 (.tq 47 (.pt (.pcs [2,3,2] (.ld 1 none)) (.sp 0 .pd (.sp 0 .pd (.ld 2 none))))) (.sp 0 (.tq 59 (.pt (.pcs [2,3,2,5,2] (.ld 1 none)) (.sp 2 .pd (.ld 2 none)))) (.ld 1 (some (0,2)))))))) (.sp 0 (.tq 67 (.pt (.pcs [2,5,2,3,2] (.sp 2 (.tq 48 (.pcs [2] (.sp 1 (.tq 46 (.pcs [2,3,2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2)))))) (.ld 1 (some (0,2))))) (.sp 2 .pd (.sp 1 .pd (.sp 2 .pd (.sp 1 .pd (.sp 2 (.sp 1 .pd (.ld 3 (some (3,0)))) (.ld 2 (some (2,0)))))))))) (.sp 2 (.tq 77 (.pcs [7,2,3,2] (.sp 0 (.tq 69 (.pcs [3,2] (.sp 1 (.tq 66 (.pcs [2,5,2,3,2] (.ld 1 none))) (.ld 1 none)))) (.sp 1 (.pt (.pcs [2] (.ld 1 (some (0,2)))) (.sp 0 .pd (.ld 2 none))) (.ld 1 (some (0,3))))))) (.sp 0 (.tq 117 (.pcs [3,2,5,2] (.sp 1 (.tq 107 (.pt (.pcs [2,3,2] (.sp 2 (.tq 102 (.pcs [2] (.ld 1 none))) (.ld 1 none))) (.sp 2 .pd (.ld 2 none)))) (.sp 2 (.tq 111 (.pcs [3,2] (.ld 1 none))) (.ld 1 none))))) (.sp 1 (.tq 130 (.pcs [2,3,2] (.sp 2 (.tq 122 (.pcs [2,11,2,7,2,3,2,5,2] (.ld 1 (some (0,2))))) (.sp 0 (.tq 124 (.pcs [2,3,2,11,2,7,2,3,2,5,2] (.ld 1 (some (0,2))))) (.ld 1 none))))) (.sp 2 (.tq 135 (.pcs [3,2,7,2] (.sp 0 (.tq 129 (.pcs [3,2] (.ld 1 (some (0,2))))) (.ld 1 none)))) (.sp 0 (.tq 137 (.pt (.pcs [2,3,2,7,2] (.ld 1 (some (0,3)))) (.sp 1 .pd (.sp 2 (.sp 1 .pd (.ld 2 (some (2,0)))) (.ld 2 (some (2,0))))))) (.ld 1 none))))))))))
def cert_11_17 : Cert := (.pcs [2] (.sp 1 (.tq 29 (.pt (.pcs [2,3,2,5,2] (.sp 0 (.pt (.pcs [2,3,2] (.ld 1 (some (0,2)))) (.sp 2 .pd (.ld 2 (some (2,0))))) (.ld 1 none))) (.sp 0 .pd (.sp 2 .pd (.sp 0 .pd (.sp 0 (.sp 2 .pd (.ld 2 (some (2,0)))) (.ld 2 none))))))) (.sp 0 (.tq 29 (.pt (.pcs [2,3,2,5,2] (.ld 1 (some (0,2)))) (.sp 2 .pd (.sp 1 .pd (.ld 2 (some (2,0))))))) (.sp 2 (.tq 33 (.pcs [3,2] (.sp 0 (.sp 1 (.pt (.pcs [2] (.ld 1 none)) (.ld 2 none)) (.ld 1 none)) (.ld 1 (some (0,2)))))) (.sp 0 (.tq 36 (.pcs [2,5,2,3,2] (.ld 1 none))) (.sp 1 (.pt (.pcs [2,5,2,3,2] (.ld 1 (some (0,2)))) (.sp 0 .pd (.sp 2 (.sp 0 .pd (.ld 2 (some (2,0)))) (.ld 2 none)))) (.sp 0 (.pt (.pcs [2,5,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.sp 2 (.sp 1 (.sp 0 (.pt (.pcs [2,5,2,3,2] (.ld 1 none)) (.ld 2 none)) (.sp 0 (.pt (.pcs [2,5,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none))) (.ld 1 none)) (.ld 1 none)))))))))
def cert_11_19 : Cert := (.pcs [2] (.sp 1 (.tq 24 (.pcs [2] (.sp 0 .pd (.sp 2 (.sp 0 .pd (.ld 2 (some (2,0)))) (.sp 0 (.ld 2 none) (.ld 1 (some (0,2)))))))) (.sp 0 (.tq 24 (.pcs [2] (.sp 2 (.sp 1 .pd (.ld 2 (some (2,0)))) (.ld 1 (some (0,2)))))) (.sp 2 (.tq 28 (.pcs [2,3,2,5,2] (.ld 1 none))) (.sp 0 (.pt (.pcs [2,3,2,5,2] (.ld 1 none)) (.sp 1 .pd (.ld 2 none))) (.sp 1 (.sp 0 (.pt (.pcs [2,3,2,5,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.sp 2 (.sp 0 (.pt (.pcs [2,3,2,5,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 (some (0,2)))) (.ld 1 none))) (.ld 1 (some (0,2)))))))))
def cert_13_17 : Cert := (.pcs [2] (.sp 0 (.tq 20 (.pcs [2] (.sp 1 .pd (.sp 2 (.ld 2 (some (2,0))) (.ld 1 (some (0,2))))))) (.sp 1 (.tq 21 (.pcs [3,2] (.sp 2 (.sp 0 (.ld 2 none) (.sp 0 (.ld 2 (some (2,0))) (.ld 1 none))) (.ld 1 none)))) (.sp 2 (.tq 22 (.pcs [2,3,2] (.ld 1 none))) (.sp 0 (.pt (.pcs [2,3,2] (.ld 1 none)) (.ld 2 none)) (.sp 1 (.sp 0 (.sp 2 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2)))) (.ld 1 none)) (.ld 1 (some (0,2)))))))))
def cert_7_19 : Cert := (.pcs [3,2,19,2] (.sp 2 (.tq 181 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0))))) (.sp 2 (.tq 345 (.pcs [3,2,7,2,11,2,3,2] (.ld 1 (some (0,3))))) (.ld 1 (some (0,2))))))
def cert_7_23 : Cert := (.tq 230 (.pcs [2] (.sp 0 (.tq 81 (.pcs [3,2] (.sp 2 (.tq 70 (.pcs [2,3,2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2)))))) (.sp 2 (.tq 160 (.pcs [2,3,2] (.sp 0 (.tq 128 (.pcs [2] (.ld 1 none))) (.sp 0 (.tq 153 (.pcs [3,2] (.ld 1 (some (0,3))))) (.ld 1 none))))) (.sp 0 (.tq 168 (.pcs [2] (.sp 2 (.tq 166 (.pcs [2,3,2] (.ld 1 none))) (.ld 1 none)))) (.sp 0 (.tq 215 (.pcs [5,2,3,2] (.sp 2 (.pt (.pcs [2,11,2,3,2,5,2,7,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2)))))) (.sp 2 (.tq 226 (.pcs [2,3,2] (.sp 0 (.pt (.pcs [2,13,2,3,2,7,2,5,2,3,2] (.ld 1 none)) (.ld 2 none)) (.ld 1 (some (0,2)))))) (.sp 0 (.tq 227 (.pt (.pcs [2,3,2] (.ld 1 none)) (.ld 2 none))) (.ld 1 (some (0,2)))))))))))
def cert_7_29_b2 : Cert := (.tq 899 (.pcs [29,2,3,2,5,2,19,2,3,2,7,2] (.sp 1 (.tq 46 (.pcs [2,3,2] (.ld 1 (some (0,2))))) (.sp 1 (.tq 248 (.pcs [2,13,2,5,2,3,2] (.sp 2 (.tq 192 (.pcs [2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2)))))) (.sp 2 (.tq 434 (.pcs [2] (.sp 1 (.tq 368 (.pcs [2] (.ld 1 (some (0,2))))) (.sp 1 (.tq 424 (.pcs [2,3,2] (.ld 1 (some (0,2))))) (.sp 1 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2)))))))) (.sp 1 (.tq 654 (.pcs [2] (.sp 2 (.tq 637 (.pcs [7,2,5,2,3,2] (.ld 1 (some (0,7))))) (.ld 1 (some (0,2)))))) (.sp 1 (.tq 854 (.pcs [2] (.sp 2 (.tq 825 (.pcs [3,2] (.ld 1 (some (0,3))))) (.sp 2 (.pt (.pcs [2,23,2,3,2,7,2,5,2,3,2,29,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2))))))) (.sp 2 (.tq 868 (.pcs [2,3,2,5,2] (.sp 1 (.tq 861 (.pcs [3,2] (.ld 1 (some (0,3))))) (.ld 1 (some (0,3)))))) (.ld 1 (some (0,2)))))))))))
def cert_7_29_c1 : Cert := (.pt (.pcs [2] (.sp 2 (.tq 67 (.pt (.pcs [2,5,2,3,2] (.ld 1 (some (0,2)))) (.sp 0 .pd (.ld 2 none)))) (.sp 0 (.pt (.pcs [2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none)))) (.sp 2 .pd (.sp 0 .pd (.sp 0 (.sp 2 .pd (.ld 2 none)) (.ld 2 (some (2,0)))))))
def cert_7_31_b2 : Cert := (.pt (.pcs [2,3,2,17,2,7,2,3,2] (.sp 1 (.tq 42 (.pcs [2] (.sp 2 (.tq 40 (.pcs [2,3,2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2)))))) (.sp 1 (.tq 158 (.pcs [2] (.sp 2 (.tq 136 (.pcs [2,3,2,7,2] (.ld 1 (some (0,2))))) (.sp 2 (.pt (.pcs [2,5,2,3,2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 (some (0,2))))))) (.sp 2 (.tq 224 (.pcs [2] (.sp 1 (.tq 205 (.pcs [5,2,7,2,3,2] (.ld 1 (some (0,5))))) (.sp 1 (.tq 222 (.pcs [2,13,2,3,2,7,2,5,2,3,2] (.ld 1 (some (0,2))))) (.ld 1 (some (0,2))))))) (.sp 1 (.tq 261 (.pcs [3,2,7,2] (.ld 1 (some (0,7))))) (.ld 1 (some (0,3)))))))) (.sp 1 .pd (.sp 1 .pd (.sp 2 .pd (.sp 1 .pd (.sp 1 .pd (.sp 2 .pd (.sp 1 .pd (.ld 2 (some (2,0)))))))))))
def cert_7_31_c1 : Cert := (.tq 62 (.pcs [2] (.sp 2 (.tq 59 (.pt (.pcs [2,3,2,5,2] (.ld 1 (some (0,2)))) (.sp 0 .pd (.sp 0 .pd (.ld 2 (some (2,0))))))) (.sp 0 (.pt (.pcs [2] (.ld 1 (some (2,0)))) (.ld 2 (some (2,0)))) (.ld 1 none)))))

lemma q_le_of_lim4 {p3 p4 q b c d e qmax : ℕ} {b1 c1 d1 : Option ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hq : q.Prime)
    (h3 : 5 < p3) (h4 : p3 < p4) (h5 : p4 < q)
    (hb : leOpt b b1) (hc : leOpt c c1) (hd : leOpt d d1)
    (hab : (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant)
    (hlim : 2 * (hiNum 5 b1 * hiNum p3 c1 * hiNum p4 d1 * (qmax + 1)) ≤
            3 * (hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * qmax)) :
    q ≤ qmax := by
  by_contra! hgt
  have hmpos : 0 < 3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e := by
    have := hp3.pos; have := hp4.pos; have := hq.pos; positivity
  have hmab : 3 * (5 ^ b * p3 ^ c * p4 ^ d * q ^ e) <
      2 * (ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e) := by
    have h1 := (abund_iff_nat hmpos).mp hab
    rw [sigma_five_primes hp3 hp4 hq h3 h4 h5] at h1
    linarith
  have h5u := ppSum_le_hi (p := 5) (a := b) (by decide) hb
  have h3u := ppSum_le_hi (p := p3) (a := c) hp3.two_le hc
  have h4u := ppSum_le_hi (p := p4) (a := d) hp4.two_le hd
  have hqmax_pos : 0 < qmax := by
    by_contra! h0
    have hq0 : qmax = 0 := by omega
    subst hq0
    simp only [zero_add, mul_one, mul_zero, Nat.le_zero] at hlim
    have h1 : 0 < hiNum 5 b1 := by
      cases b1 with
      | none => decide
      | some k =>
        have := ppSum_mul_sub (p := 5) (a := k) (by decide)
        have : 1 < 5 ^ (k + 1) := one_lt_pow₀ (by decide) (by omega)
        dsimp [hiNum]; omega
    have h2 : 0 < hiNum p3 c1 := by
      cases c1 with
      | none => exact hp3.pos
      | some k =>
        have hsub := ppSum_mul_sub (p := p3) (a := k) hp3.two_le
        have hlt : 1 < p3 ^ (k + 1) := one_lt_pow₀ hp3.one_lt (by omega)
        dsimp [hiNum]
        by_contra! h0
        have h0' : ppSum p3 k = 0 := by omega
        rw [h0', zero_mul] at hsub; omega
    have h3' : 0 < hiNum p4 d1 := by
      cases d1 with
      | none => exact hp4.pos
      | some k =>
        have hsub := ppSum_mul_sub (p := p4) (a := k) hp4.two_le
        have hlt : 1 < p4 ^ (k + 1) := one_lt_pow₀ hp4.one_lt (by omega)
        dsimp [hiNum]
        by_contra! h0
        have h0' : ppSum p4 k = 0 := by omega
        rw [h0', zero_mul] at hsub; omega
    have : 0 < 2 * (hiNum 5 b1 * hiNum p3 c1 * hiNum p4 d1) := by positivity
    omega
  have hqu : ppSum q e * qmax ≤ (qmax + 1) * q ^ e := by
    have hqlim := (ppSum_lt_lim (p := q) (a := e) hq.two_le).le
    have hq1 : q * qmax ≤ (qmax + 1) * (q - 1) := by
      zify [(show 1 ≤ q by have := hq.two_le; omega)]; nlinarith
    apply Nat.le_of_mul_le_mul_right _ (show 0 < q - 1 by have := hq.two_le; omega)
    calc ppSum q e * qmax * (q - 1) = (ppSum q e * (q - 1)) * qmax := by ring
      _ ≤ (q * q ^ e) * qmax := Nat.mul_le_mul_right _ hqlim
      _ = (q * qmax) * q ^ e := by ring
      _ ≤ ((qmax + 1) * (q - 1)) * q ^ e := Nat.mul_le_mul_right _ hq1
      _ = (qmax + 1) * q ^ e * (q - 1) := by ring
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul h5u h3u) (Nat.mul_le_mul h4u hqu)
  have hden_pos : 0 < hiDen 5 b1 * hiDen p3 c1 * hiDen p4 d1 * qmax := by
    have h1 : 0 < hiDen 5 b1 := by cases b1 <;> simp [hiDen] <;> positivity
    have h2 : 0 < hiDen p3 c1 := by
      cases c1 <;> simp [hiDen]
      · have := hp3.two_le; omega
      · exact pow_pos hp3.pos _
    have h3' : 0 < hiDen p4 d1 := by
      cases d1 <;> simp [hiDen]
      · have := hp4.two_le; omega
      · exact pow_pos hp4.pos _
    positivity
  have hc1 := Nat.mul_lt_mul_of_pos_right hmab hden_pos
  have hc2 := Nat.mul_le_mul_left 2 hprod
  have hc3 := Nat.mul_le_mul_right (5 ^ b * p3 ^ c * p4 ^ d * q ^ e) hlim
  linarith

lemma not_prim_of_ab4_div {p3 p4 q b c d e b0 c0 d0 : ℕ}
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hq : q.Prime)
    (h3 : 5 < p3) (h4 : p3 < p4) (he : 1 ≤ e)
    (hb : b0 ≤ b) (hc : c0 ≤ c) (hd : d0 ≤ d)
    (hprim : ∀ x ∈ (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).properDivisors, x.Deficient)
    (hab0 : 3 * (5 ^ b0 * p3 ^ c0 * p4 ^ d0) < 2 * (ppSum 5 b0 * ppSum p3 c0 * ppSum p4 d0)) :
    False := by
  let B0 := 3 * 5 ^ b0 * p3 ^ c0 * p4 ^ d0
  have hB0pos : 0 < B0 := by have := hp3.pos; have := hp4.pos; positivity
  have hB0dvd : B0 ∣ 3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e :=
    (Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 3 (pow_dvd_pow 5 hb))
      (pow_dvd_pow p3 hc)) (pow_dvd_pow p4 hd)).trans (dvd_mul_right _ _)
  have hB0lt : B0 < 3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e := by
    have hle : B0 ≤ 3 * 5 ^ b * p3 ^ c * p4 ^ d :=
      Nat.le_of_dvd (by have := hp3.pos; have := hp4.pos; positivity)
        (Nat.mul_dvd_mul (Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 3 (pow_dvd_pow 5 hb))
          (pow_dvd_pow p3 hc)) (pow_dvd_pow p4 hd))
    have hqgt : 1 < q ^ e := one_lt_pow₀ hq.one_lt (by omega)
    nlinarith
  have hdef := (defic_iff_nat hB0pos).mp (hprim B0 (Nat.mem_properDivisors.mpr ⟨hB0dvd, hB0lt⟩))
  rw [sigma_four_primes hp3 hp4 h3 h4] at hdef
  dsimp only [B0] at hdef
  linarith

lemma next_prime_ge {p4 q : ℕ} (hq : q.Prime) (hgt : p4 < q) {q0 : ℕ}
    (hcomp : ∀ t, p4 < t → t < q0 → ¬ t.Prime) : q0 ≤ q := by
  by_contra! hlt
  exact hcomp q hgt hlt hq

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 20000 in
lemma cert_19_pairs_beven {p3 p4 q b c d e : ℕ}
    (hmem : (p3, p4) ∈ validPairs19) (hq : q.Prime) (h5 : p4 < q)
    (hb : 2 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) (hbeven : b % 2 = 0)
    (hab : (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).properDivisors, x.Deficient) :
    30 ≤ sigma 1 (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) -
      2 * (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) ∨
    (sigma 1 (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e) -
      2 * (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e)) % 3 = 0 := by
  simp only [validPairs19, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd (not_prim_of_ab4_div (b0 := 2) (c0 := 1) (d0 := 1) (by decide) (by decide) hq
      (by decide) (by decide) he hb hc hd hprim (by decide)) id
  · exact absurd (not_prim_of_ab4_div (b0 := 2) (c0 := 1) (d0 := 1) (by decide) (by decide) hq
      (by decide) (by decide) he hb hc hd hprim (by decide)) id
  · exact absurd (not_prim_of_ab4_div (b0 := 2) (c0 := 1) (d0 := 1) (by decide) (by decide) hq
      (by decide) (by decide) he hb hc hd hprim (by decide)) id
  · -- (7, 19): b >= 3 or c >= 2 abundant -> b = 2, c = 1
    have hb2 : b = 2 := by
      by_contra hne
      exact not_prim_of_ab4_div (b0 := 3) (c0 := 1) (d0 := 1) (by decide) (by decide) hq
        (by decide) (by decide) he (by omega) hc hd hprim (by decide)
    have hc1 : c = 1 := by
      by_contra hne
      exact not_prim_of_ab4_div (b0 := 2) (c0 := 2) (d0 := 1) (by decide) (by decide) hq
        (by decide) (by decide) he hb (by omega) hd hprim (by decide)
    have hq0 : 23 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 363 := q_le_of_lim4 (b1 := some 2) (c1 := some 1) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 (by simp [leOpt, hb2])
      (by simp [leOpt, hc1]) trivial hab (by decide)
    exact Cert.sound (b1 := some 2) (c1 := some 1) (d1 := none) (cert := cert_7_19)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb (by simp [leOpt, hb2]) hc (by simp [leOpt, hc1]) hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 23): c >= 2 abundant -> c = 1
    have hc1 : c = 1 := by
      by_contra hne
      exact not_prim_of_ab4_div (b0 := 2) (c0 := 2) (d0 := 1) (by decide) (by decide) hq
        (by decide) (by decide) he hb (by omega) hd hprim (by decide)
    have hq0 : 29 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 231 := q_le_of_lim4 (b1 := none) (c1 := some 1) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial
      (by simp [leOpt, hc1]) trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := some 1) (d1 := none) (cert := cert_7_23)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc (by simp [leOpt, hc1]) hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 29): b = 2 OR (b >= 4 and c = 1)
    have hq0 : 31 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    by_cases hb2 : b = 2
    · have hq1 : q ≤ 900 := q_le_of_lim4 (b1 := some 2) (c1 := none) (d1 := none)
        (by decide) (by decide) hq (by decide) (by decide) h5 (by simp [leOpt, hb2])
        trivial trivial hab (by decide)
      exact Cert.sound (b1 := some 2) (c1 := none) (d1 := none) (cert := cert_7_29_b2)
        (by decide) (by decide) hq (by decide) (by decide) h5
        hb (by simp [leOpt, hb2]) hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
    · have hb4 : 4 ≤ b := by omega
      have hc1 : c = 1 := by
        by_contra hne
        exact not_prim_of_ab4_div (b0 := 3) (c0 := 2) (d0 := 1) (by decide) (by decide) hq
          (by decide) (by decide) he (by omega) (by omega) hd hprim (by decide)
      have hq1 : q ≤ 73 := q_le_of_lim4 (b1 := none) (c1 := some 1) (d1 := none)
        (by decide) (by decide) hq (by decide) (by decide) h5 trivial
        (by simp [leOpt, hc1]) trivial hab (by decide)
      exact Cert.sound (b1 := none) (c1 := some 1) (d1 := none) (cert := cert_7_29_c1)
        (by decide) (by decide) hq (by decide) (by decide) h5
        hb4 trivial hc (by simp [leOpt, hc1]) hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 31): b = 2 OR (b >= 4 and c = 1)
    have hq0 : 37 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    by_cases hb2 : b = 2
    · have hq1 : q ≤ 293 := q_le_of_lim4 (b1 := some 2) (c1 := none) (d1 := none)
        (by decide) (by decide) hq (by decide) (by decide) h5 (by simp [leOpt, hb2])
        trivial trivial hab (by decide)
      exact Cert.sound (b1 := some 2) (c1 := none) (d1 := none) (cert := cert_7_31_b2)
        (by decide) (by decide) hq (by decide) (by decide) h5
        hb (by simp [leOpt, hb2]) hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
    · have hb4 : 4 ≤ b := by omega
      have hc1 : c = 1 := by
        by_contra hne
        exact not_prim_of_ab4_div (b0 := 4) (c0 := 2) (d0 := 1) (by decide) (by decide) hq
          (by decide) (by decide) he hb4 (by omega) hd hprim (by decide)
      have hq1 : q ≤ 63 := q_le_of_lim4 (b1 := none) (c1 := some 1) (d1 := none)
        (by decide) (by decide) hq (by decide) (by decide) h5 trivial
        (by simp [leOpt, hc1]) trivial hab (by decide)
      exact Cert.sound (b1 := none) (c1 := some 1) (d1 := none) (cert := cert_7_31_c1)
        (by decide) (by decide) hq (by decide) (by decide) h5
        hb4 trivial hc (by simp [leOpt, hc1]) hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 37)
    have hq0 : 41 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 1296 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_7_37)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 41)
    have hq0 : 43 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 288 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_7_41)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 43)
    have hq0 : 47 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 216 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_7_43)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 47)
    have hq0 : 53 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 150 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_7_47)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 53)
    have hq0 : 59 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 110 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_7_53)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 59)
    have hq0 : 61 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 90 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_7_59)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 61)
    have hq0 : 67 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 86 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_7_61)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (7, 67)
    have hq0 : 71 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 76 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_7_67)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (11, 13)
    have hq0 : 17 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 144 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_11_13)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (11, 17)
    have hq0 : 19 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 38 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_11_17)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (11, 19)
    have hq0 : 23 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 30 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_11_19)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)
  · -- (13, 17)
    have hq0 : 19 ≤ q := next_prime_ge hq h5 (by intro t h1 h2; interval_cases t <;> decide)
    have hq1 : q ≤ 24 := q_le_of_lim4 (b1 := none) (c1 := none) (d1 := none)
      (by decide) (by decide) hq (by decide) (by decide) h5 trivial trivial trivial hab (by decide)
    exact Cert.sound (b1 := none) (c1 := none) (d1 := none) (cert := cert_13_17)
      (by decide) (by decide) hq (by decide) (by decide) h5
      hb trivial hc trivial hd trivial hq0 hq1 he hbeven hab hprim (by decide)

end CertData

section MainProof

lemma three_dvd_ppSum_five_odd {b : ℕ} (hb : b % 2 = 1) : 3 ∣ ppSum 5 b := by
  have h5p : Nat.Prime 5 := by decide
  rw [ppSum_eq_sigma h5p, sigma_one_apply_prime_pow h5p]
  obtain ⟨k, rfl⟩ := Nat.odd_iff.mpr hb
  clear hb
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 + 1 = (2 * k + 1 + 1) + 2 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
    have hpair : 3 ∣ 5 ^ (2 * k + 2) + 5 ^ (2 * k + 3) := by
      have : 5 ^ (2 * k + 2) + 5 ^ (2 * k + 3) = 5 ^ (2 * k + 2) * 6 := by ring
      rw [this]; exact dvd_mul_of_dvd_right (by decide) _
    rw [add_assoc]
    exact dvd_add ih hpair

lemma rank5_pseudoperfect {p3 p4 q b c d e : ℕ}
    (hmem : (p3, p4) ∈ validPairs19) (hq : q.Prime) (h5 : p4 < q)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hab : (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Abundant)
    (hprim : ∀ x ∈ (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).properDivisors, x.Deficient) :
    (3 * 5 ^ b * p3 ^ c * p4 ^ d * q ^ e).Pseudoperfect := by
  have hp3_p4 : p3.Prime ∧ p4.Prime ∧ 5 < p3 ∧ p3 < p4 ∧ (p3 = 7 ∨ p3 = 11 ∨ p3 = 13) := by
    simp only [validPairs19, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨hp3, hp4, h3gt, h4gt, hp3_cases⟩ := hp3_p4
  let B := 3 * 5 ^ b * p3 ^ c * p4 ^ d
  let m := B * q ^ e
  have hBpos : 0 < B := by have := hp3.pos; have := hp4.pos; positivity
  have hmpos : 0 < m := by have := hq.pos; positivity
  have hBgt1 : 1 < B := by
    have h1 : 5 ≤ 5 ^ b := by simpa using pow_le_pow_right₀ (by decide : 1 ≤ 5) hb
    have h2 : 1 ≤ p3 ^ c := Nat.one_le_pow _ _ hp3.pos
    have h3' : 1 ≤ p4 ^ d := Nat.one_le_pow _ _ hp4.pos
    have h4' : 3 * 5 ≤ 3 * 5 ^ b := Nat.mul_le_mul_left 3 h1
    have h5' : 3 * 5 * 1 * 1 ≤ B := Nat.mul_le_mul (Nat.mul_le_mul h4' h2) h3'
    omega
  have hcopBq : B.Coprime q := by
    have h3p : Nat.Prime 3 := by decide
    have h5p : Nat.Prime 5 := by decide
    exact Nat.Coprime.mul_left
      (Nat.Coprime.mul_left
        (Nat.Coprime.mul_left ((Nat.coprime_primes h3p hq).mpr (by omega))
          (((Nat.coprime_primes h5p hq).mpr (by omega)).pow_left b))
        (((Nat.coprime_primes hp3 hq).mpr (by omega)).pow_left c))
      (((Nat.coprime_primes hp4 hq).mpr (by omega)).pow_left d)
  let L := pairL p3 p4
  let g := pairG p3
  obtain ⟨hcovB, hgapB, hmodB, hbigB⟩ := core_19_pairs hmem hb hc hd
  have hL_pos : 1 ≤ (L : ℤ) := by
    dsimp [L, pairL]; split_ifs <;> omega
  have hg_pos : 1 ≤ (g : ℤ) := by
    dsimp [g, pairG]; split_ifs <;> omega
  have hE_pos : 0 < excess m := by
    have := (abund_iff_nat hmpos).mp hab
    dsimp [excess]; omega
  -- 4 | sigma 1 B and B odd => 2 <= B - properTotal B
  have hB_odd : Odd B := by
    have hp3_odd : Odd p3 := hp3.odd_of_ne_two (by omega)
    have hp4_odd : Odd p4 := hp4.odd_of_ne_two (by omega)
    exact (((by decide : Odd 3).mul ((by decide : Odd 5).pow)).mul hp3_odd.pow).mul hp4_odd.pow
  have hsigB_4 : 4 ∣ sigma 1 B := by
    rw [sigma_four_primes hp3 hp4 h3gt h4gt]
    exact ⟨ppSum 5 b * ppSum p3 c * ppSum p4 d, by ring⟩
  have hB_def : sigma 1 B < 2 * B := by
    have hBmem : B ∈ m.properDivisors := Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right B (q ^ e),
       by simpa using Nat.mul_lt_mul_of_pos_left (one_lt_pow₀ hq.one_lt (by omega)) hBpos⟩
    exact (defic_iff_nat hBpos).mp (hprim B hBmem)
  have hsimpleD : 2 ≤ (B : ℤ) - properTotal B := by
    have h1 : (B : ℤ) - properTotal B = 2 * (B : ℤ) - (sigma 1 B : ℤ) := by
      rw [sigma_split B]; ring
    rw [h1]
    obtain ⟨k, hk⟩ := hB_odd
    obtain ⟨t, ht⟩ := hsigB_4
    omega
  by_cases hhigh : (L : ℤ) ≤ excess m
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    have hP_cast : properTotal B = (properDivsSum B : ℤ) := by
      simp [properTotal, properDivsSum]
    exact certified_prime_power_gen hBgt1 hq hcopBq (by omega) hprim (L : ℤ) (g : ℤ)
      hL_pos hg_pos hhigh
      (by rw [hP_cast]; exact_mod_cast hbigB)
      (fun _ => hsimpleD)
      (fun y hy1 hy2 => by
        lift y to ℕ using (by omega)
        rw [hP_cast] at hy2
        have hLy : L ≤ y := by exact_mod_cast hy1
        have hyP : y ≤ properDivsSum B - L := by omega
        exact repNat_to_represented (hcovB y hLy hyP))
      (fun k hk1 hk2 => by
        lift k to ℕ using hk1
        rw [hP_cast] at hk2
        obtain ⟨i, hi, hi1, hi2⟩ := hgapB k (by exact_mod_cast hk2)
        exact ⟨(i : ℤ), repNat_to_represented hi, by omega, by omega⟩)
  · -- Small excess: E < L!
    let En : ℕ := sigma 1 m - 2 * m
    have hEn_eq : (En : ℤ) = excess m := by
      have hgt := (abund_iff_nat hmpos).mp hab
      dsimp [En, excess]; omega
    have hEn_lt : En < L := by omega
    have hm_odd : Odd m := hB_odd.mul (hq.odd_of_ne_two (by omega)).pow
    have hsigm_4 : 4 ∣ sigma 1 m := by
      rw [sigma_five_primes hp3 hp4 hq h3gt h4gt h5]
      exact ⟨ppSum 5 b * ppSum p3 c * ppSum p4 d * ppSum q e, by ring⟩
    have hEn_mod4 : En % 4 = 2 := by
      obtain ⟨k, hk⟩ := hm_odd
      obtain ⟨t, ht⟩ := hsigm_4
      have hgt := (abund_iff_nat hmpos).mp hab
      dsimp [En]; omega
    by_cases h3E : En % 3 = 0
    · have hEn_mod12 : En % 12 = 6 := by omega
      obtain ⟨s, hs, hsum⟩ := hmodB En hEn_lt hEn_mod12
      have hs_m : s ⊆ m.properDivisors := by
        intro x hx
        obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp (hs hx)
        exact Nat.mem_properDivisors.mpr ⟨h1.trans (dvd_mul_right B (q ^ e)),
          lt_of_lt_of_le h2 (Nat.le_of_dvd hmpos (dvd_mul_right B (q ^ e)))⟩
      exact pseudoperfect_of_excess hmpos hs_m (by rw [← hEn_eq, ← hsum]; simp)
    · -- 3 does not divide En => b MUST be even (b >= 2)!
      have hbeven : b % 2 = 0 := by
        by_contra hodd
        have hbmod : b % 2 = 1 := by omega
        have h3sig : 3 ∣ sigma 1 m := by
          rw [sigma_five_primes hp3 hp4 hq h3gt h4gt h5]
          obtain ⟨t, ht⟩ := three_dvd_ppSum_five_odd hbmod
          exact ⟨4 * t * ppSum p3 c * ppSum p4 d * ppSum q e, by rw [ht]; ring⟩
        have h3m : 3 ∣ m := ⟨5 ^ b * p3 ^ c * p4 ^ d * q ^ e, by dsimp [m, B]; ring⟩
        have h3sub : 3 ∣ En := by
          obtain ⟨a1, ha1⟩ := h3sig
          obtain ⟨a2, ha2⟩ := h3m
          have hgt := (abund_iff_nat hmpos).mp hab
          dsimp [En]; omega
        exact h3E (Nat.mod_eq_zero_of_dvd h3sub)
      have hb2 : 2 ≤ b := by omega
      by_cases h525 : p3 = 7 ∧ 18 ≤ En
      · have hL_le449 : En ≤ 449 := by
          have : L ≤ 108 := by dsimp [L, pairL]; split_ifs <;> omega
          omega
        obtain ⟨s, hs, hsum⟩ := rep_525 h525.2 hL_le449
        have h525_dvd : 525 ∣ m := by
          have h25 : 25 ∣ 5 ^ b := by
            have := pow_dvd_pow 5 hb2; norm_num at this; exact this
          have h7 : 7 ∣ p3 ^ c := by rw [h525.1]; exact dvd_pow_self 7 (by omega)
          have h1 : 3 * 25 * 7 ∣ 3 * 5 ^ b * p3 ^ c :=
            Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 3 h25) h7
          exact h1.trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
        have hs_m : s ⊆ m.properDivisors := by
          intro x hx
          obtain ⟨h1, h2⟩ := Nat.mem_properDivisors.mp (hs hx)
          exact Nat.mem_properDivisors.mpr ⟨h1.trans h525_dvd,
            lt_of_lt_of_le h2 (Nat.le_of_dvd hmpos h525_dvd)⟩
        exact pseudoperfect_of_excess hmpos hs_m (by rw [← hEn_eq, ← hsum]; simp)
      · have hEn_lt30 : En < 30 := by
          rcases hp3_cases with rfl | rfl | rfl
          · omega
          · have : L ≤ 14 := by dsimp [L, pairL]; split_ifs <;> omega
            omega
          · have : L ≤ 28 := by dsimp [L, pairL]; omega
            omega
        have hcert := cert_19_pairs_beven hmem hq h5 hb2 hc hd he hbeven hab hprim
        change 30 ≤ En ∨ En % 3 = 0 at hcert
        omega

/-- Upper bound on abundancy index for a finite set of primes with v_3(m) = 1. -/
lemma prod_le_two_of_prime_bounds {m : ℕ} (hm0 : m ≠ 0) (hf3 : m.factorization 3 = 1)
    (h3 : 3 ∈ m.primeFactors)
    (ps : List ℕ) (hnd : ps.Nodup) (heq : (m.primeFactors.erase 3).toList.Perm ps)
    (hprod : 2 * (ps.map id).prod ≤ 3 * (ps.map (fun p => p - 1)).prod)
    (hge2 : ∀ p ∈ ps, 2 ≤ p) : ¬ m.Abundant := by
  intro hab
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hsig_prod : sigma 1 m = 4 * ∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p) := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors hm0]
    rw [← Finset.mul_prod_erase _ _ h3, hf3]
    have h3sum : ∑ j ∈ range (1 + 1), 3 ^ j = 4 := by decide
    rw [h3sum]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hp)).1
    rw [ppSum_eq_sigma hpp, sigma_one_apply_prime_pow hpp]
  have hm_prod : m = 3 * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p := by
    have hfac := Nat.prod_primeFactors_pow_factorization hm0
    rw [← Finset.mul_prod_erase _ _ h3, hf3, pow_one] at hfac
    exact hfac
  have h1 : (∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p)) *
      (∏ p ∈ m.primeFactors.erase 3, (p - 1)) ≤
      (∏ p ∈ m.primeFactors.erase 3, p) *
      (∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hp)).1
    exact (ppSum_lt_lim hpp.two_le).le
  have hperm_num : ∏ p ∈ m.primeFactors.erase 3, p = (ps.map id).prod := by
    rw [← Finset.prod_toList]; simpa using heq.prod_eq
  have hperm_den : ∏ p ∈ m.primeFactors.erase 3, (p - 1) = (ps.map (fun p => p - 1)).prod := by
    rw [← Finset.prod_map_toList]
    exact (heq.map (fun p => p - 1)).prod_eq
  have hden_pos : 0 < ∏ p ∈ m.primeFactors.erase 3, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hp)).1
    have := hpp.two_le; omega
  have hab_nat : 2 * (3 * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) <
      4 * ∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p) := by
    rw [← hm_prod, ← hsig_prod]
    exact (abund_iff_nat hmpos).mp hab
  have hlt : 3 * (∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) *
      (∏ p ∈ m.primeFactors.erase 3, (p - 1)) <
      2 * (∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p)) *
      (∏ p ∈ m.primeFactors.erase 3, (p - 1)) := by
    have hlt0 : 3 * ∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p <
        2 * ∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p) := by
      omega
    exact Nat.mul_lt_mul_of_pos_right hlt0 hden_pos
  rw [hperm_num, hperm_den] at h1
  have hle1 : 2 * (∏ p ∈ m.primeFactors.erase 3, ppSum p (m.factorization p)) *
      (ps.map (fun p => p - 1)).prod ≤
      2 * (ps.map id).prod * (∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) := by
    linarith [Nat.mul_le_mul_left 2 h1]
  have hle2 := Nat.mul_le_mul_right (∏ p ∈ m.primeFactors.erase 3, p ^ m.factorization p) hprod
  rw [hperm_den] at hlt
  linarith

lemma frac_anti {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : b * (a - 1) ≤ a * (b - 1) := by
  zify [(show 1 ≤ a by omega), (show 1 ≤ b by omega)]; nlinarith

end MainProof

end R2H1

set_option maxHeartbeats 800000 in
open Finset R2H1 in
theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2.H1 := by
  intro m hm_odd hm_ab hm_card hm_prim h15 h9
  have hm_pos : 0 < m := hm_odd.pos
  have hm0 : m ≠ 0 := hm_pos.ne'
  have h3p : Nat.Prime 3 := by decide
  have h5p : Nat.Prime 5 := by decide
  have h3dvd : 3 ∣ m := (by decide : 3 ∣ 15).trans h15
  have h5dvd : 5 ∣ m := (by decide : 5 ∣ 15).trans h15
  have h3mem : 3 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨h3p, h3dvd, hm0⟩
  have h5mem : 5 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨h5p, h5dvd, hm0⟩
  have hf3 : m.factorization 3 = 1 := by
    have hge := (h3p.pow_dvd_iff_le_factorization hm0 (k := 1)).mp (by simpa using h3dvd)
    have hlt : ¬ 2 ≤ m.factorization 3 := fun h => h9 ((h3p.pow_dvd_iff_le_factorization hm0).mpr h)
    omega
  have hf5 : 1 ≤ m.factorization 5 :=
    (h5p.pow_dvd_iff_le_factorization hm0 (k := 1)).mp (by simpa using h5dvd)
  have h5er : 5 ∈ m.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨by decide, h5mem⟩
  let rest := (m.primeFactors.erase 3).erase 5
  have hrest_card : rest.card ≤ 3 := by
    have h1 : (m.primeFactors.erase 3).card = m.primeFactors.card - 1 := Finset.card_erase_of_mem h3mem
    have h2 : rest.card = (m.primeFactors.erase 3).card - 1 := Finset.card_erase_of_mem h5er
    omega
  let ls := rest.sort (· ≤ ·)
  have hls_len : ls.length ≤ 3 := by simpa [ls] using hrest_card
  have hls_nd : ls.Nodup := Finset.sort_nodup _ _
  have hls_sorted : ls.Pairwise (· < ·) :=
    ((Finset.pairwise_sort rest (· ≤ ·)).and (List.nodup_iff_pairwise_ne.mp hls_nd)).imp
      (fun h => lt_of_le_of_ne h.1 h.2)
  have hls_prop : ∀ p ∈ ls, p.Prime ∧ 7 ≤ p ∧ 1 ≤ m.factorization p := by
    intro p hp
    have hmem_r : p ∈ rest := (Finset.mem_sort (· ≤ ·)).mp hp
    have hne5 : p ≠ 5 := (Finset.mem_erase.mp hmem_r).1
    have hmem_3 : p ∈ m.primeFactors.erase 3 := (Finset.mem_erase.mp hmem_r).2
    have hne3 : p ≠ 3 := (Finset.mem_erase.mp hmem_3).1
    have hmem_m := Nat.mem_primeFactors.mp (Finset.mem_erase.mp hmem_3).2
    have hne2 : p ≠ 2 := by rintro rfl; exact hm_odd.not_two_dvd_nat hmem_m.2.1
    have hge7 : 7 ≤ p := by
      by_contra! hlt
      exact (by decide : ∀ t < 7, t ≠ 2 → t ≠ 3 → t ≠ 5 → ¬ t.Prime) p hlt hne2 hne3 hne5 hmem_m.1
    have hf : 1 ≤ m.factorization p :=
      (hmem_m.1.pow_dvd_iff_le_factorization hm0 (k := 1)).mp (by simpa using hmem_m.2.1)
    exact ⟨hmem_m.1, hge7, hf⟩
  have hperm_er3 : (m.primeFactors.erase 3).toList.Perm (5 :: ls) := by
    have h1 : m.primeFactors.erase 3 = insert 5 rest := (Finset.insert_erase h5er).symm
    have h5nr : 5 ∉ rest := Finset.notMem_erase 5 _
    have h2 : (insert 5 rest).toList.Perm (5 :: rest.toList) := Finset.toList_insert h5nr
    have h3 : rest.toList.Perm ls := (Finset.sort_perm_toList rest (· ≤ ·)).symm
    rw [h1]
    exact h2.trans (h3.cons 5)
  have hnd_5ls : (5 :: ls).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun h => by have := (hls_prop 5 h).2.1; omega, hls_nd⟩
  -- Helper: reconstruct m = 3 * 5^b * prod_{p in ls} p^(fact p)
  have hm_eq_list : m = 3 * 5 ^ m.factorization 5 * (ls.map (fun p => p ^ m.factorization p)).prod := by
    have hfac := Nat.prod_primeFactors_pow_factorization hm0
    rw [← Finset.mul_prod_erase _ _ h3mem, hf3, pow_one,
        ← Finset.mul_prod_erase _ _ h5er, ← mul_assoc] at hfac
    calc m = 3 * 5 ^ m.factorization 5 * ∏ p ∈ rest, p ^ m.factorization p := hfac
      _ = 3 * 5 ^ m.factorization 5 * (ls.map (fun p => p ^ m.factorization p)).prod := by
        congr 1
        rw [← Finset.prod_map_toList]
        have hperm : rest.toList.Perm ls := (Finset.sort_perm_toList rest (· ≤ ·)).symm
        exact (hperm.map (fun p => p ^ m.factorization p)).prod_eq
  rcases hls_cases : ls with _ | ⟨p3, _ | ⟨p4, _ | ⟨q, _ | _⟩⟩⟩
  · -- card = 2: {3, 5}
    exfalso
    exact prod_le_two_of_prime_bounds hm0 hf3 h3mem [5]
      (by simpa [hls_cases] using hnd_5ls) (by simpa [hls_cases] using hperm_er3)
      (by decide) (by intro p hp; simp at hp; omega) hm_ab
  · -- card = 3: {3, 5, p3}
    exfalso
    obtain ⟨hp3, h7p3, _⟩ := hls_prop p3 (by simp [hls_cases])
    have hbd : 2 * ([5, p3].map id).prod ≤ 3 * ([5, p3].map (fun p => p - 1)).prod := by
      simp only [List.map_cons, List.map_nil, id_eq, List.prod_cons, List.prod_nil, mul_one]
      have := frac_anti (by decide : 2 ≤ 7) h7p3
      nlinarith
    exact prod_le_two_of_prime_bounds hm0 hf3 h3mem [5, p3]
      (by simpa [hls_cases] using hnd_5ls) (by simpa [hls_cases] using hperm_er3)
      hbd (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> omega) hm_ab
  · -- card = 4: {3, 5, p3, p4}
    obtain ⟨hp3, h7p3, hfc⟩ := hls_prop p3 (by simp [hls_cases])
    obtain ⟨hp4, h7p4, hfd⟩ := hls_prop p4 (by simp [hls_cases])
    have hp34 : p3 < p4 := by
      rw [hls_cases] at hls_sorted
      simpa using (List.pairwise_cons.mp hls_sorted).1 p4 List.mem_cons_self
    have hm_eq : m = 3 * 5 ^ m.factorization 5 * p3 ^ m.factorization p3 * p4 ^ m.factorization p4 := by
      conv_lhs => rw [hm_eq_list, hls_cases]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    have hp3_eq7 : p3 = 7 := by
      by_contra hne
      have h11 : 11 ≤ p3 := by
        by_contra! hlt
        exact (by decide : ∀ t < 11, 7 ≤ t → t ≠ 7 → ¬ t.Prime) p3 hlt h7p3 hne hp3
      have h13 : 13 ≤ p4 := by
        by_contra! hlt
        exact (by decide : ∀ t < 13, 11 < t → ¬ t.Prime) p4 hlt (by omega) hp4
      have hbd : 2 * ([5, p3, p4].map id).prod ≤ 3 * ([5, p3, p4].map (fun p => p - 1)).prod := by
        simp only [List.map_cons, List.map_nil, id_eq, List.prod_cons, List.prod_nil, mul_one]
        have f1 := frac_anti (by decide : 2 ≤ 11) h11
        have f2 := frac_anti (by decide : 2 ≤ 13) h13
        have : p3 * p4 * (10 * 12) ≤ 11 * 13 * ((p3 - 1) * (p4 - 1)) := by
          have := Nat.mul_le_mul f1 f2; linarith
        nlinarith
      exact prod_le_two_of_prime_bounds hm0 hf3 h3mem [5, p3, p4]
        (by simpa [hls_cases] using hnd_5ls) (by simpa [hls_cases] using hperm_er3)
        hbd (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> omega) hm_ab
    subst hp3_eq7
    have hp4_lt37 : p4 < 37 := by
      by_contra! h37
      have hbd : 2 * ([5, 7, p4].map id).prod ≤ 3 * ([5, 7, p4].map (fun p => p - 1)).prod := by
        simp only [List.map_cons, List.map_nil, id_eq, List.prod_cons, List.prod_nil, mul_one]
        have f2 := frac_anti (by decide : 2 ≤ 37) h37
        nlinarith
      exact prod_le_two_of_prime_bounds hm0 hf3 h3mem [5, 7, p4]
        (by simpa [hls_cases] using hnd_5ls) (by simpa [hls_cases] using hperm_er3)
        hbd (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> omega) hm_ab
    have hp4_mem : p4 ∈ ({11, 13, 17, 19, 23, 29, 31} : Finset ℕ) :=
      (by decide : ∀ t < 37, 7 < t → t.Prime → t ∈ ({11, 13, 17, 19, 23, 29, 31} : Finset ℕ))
        p4 hp4_lt37 hp34 hp4
    rw [hm_eq] at hm_ab hm_prim ⊢
    exact rank4_pseudoperfect hp4_mem hf5 hfc hfd hm_ab hm_prim
  · -- card = 5: {3, 5, p3, p4, q}
    obtain ⟨hp3, h7p3, hfc⟩ := hls_prop p3 (by simp [hls_cases])
    obtain ⟨hp4, h7p4, hfd⟩ := hls_prop p4 (by simp [hls_cases])
    obtain ⟨hq, h7q, hfe⟩ := hls_prop q (by simp [hls_cases])
    have hord : p3 < p4 ∧ p4 < q := by
      rw [hls_cases] at hls_sorted
      have h1 := List.pairwise_cons.mp hls_sorted
      have h2 := List.pairwise_cons.mp h1.2
      exact ⟨h1.1 p4 List.mem_cons_self, h2.1 q List.mem_cons_self⟩
    have hm_eq : m = 3 * 5 ^ m.factorization 5 * p3 ^ m.factorization p3 *
        p4 ^ m.factorization p4 * q ^ m.factorization q := by
      conv_lhs => rw [hm_eq_list, hls_cases]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    have hnot5 (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
        (h1 : a ≤ p3) (h2 : b ≤ p4) (h3 : c ≤ q)
        (hcheck : 2 * (5 * a * b * c) ≤ 3 * (4 * (a - 1) * (b - 1) * (c - 1))) : False := by
      have hbd : 2 * ([5, p3, p4, q].map id).prod ≤ 3 * ([5, p3, p4, q].map (fun p => p - 1)).prod := by
        simp only [List.map_cons, List.map_nil, id_eq, List.prod_cons, List.prod_nil, mul_one]
        have f1 := frac_anti ha h1
        have f2 := frac_anti hb h2
        have f3 := frac_anti hc h3
        have hmul := Nat.mul_le_mul (Nat.mul_le_mul f1 f2) f3
        have hden : 0 < (a - 1) * (b - 1) * (c - 1) := by
          have : 0 < a - 1 := by omega
          have : 0 < b - 1 := by omega
          have : 0 < c - 1 := by omega
          positivity
        apply Nat.le_of_mul_le_mul_right _ hden
        have hL : 2 * (5 * (p3 * (p4 * q))) * ((a - 1) * (b - 1) * (c - 1)) ≤
            2 * (5 * a * b * c) * ((p3 - 1) * (p4 - 1) * (q - 1)) := by
          have := Nat.mul_le_mul_left 10 hmul
          linarith
        have hR := Nat.mul_le_mul_right ((p3 - 1) * (p4 - 1) * (q - 1)) hcheck
        linarith
      exact prod_le_two_of_prime_bounds hm0 hf3 h3mem [5, p3, p4, q]
        (by simpa [hls_cases] using hnd_5ls) (by simpa [hls_cases] using hperm_er3)
        hbd (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl | rfl <;> omega) hm_ab
    have hp3_lt17 : p3 < 17 := by
      by_contra! h17
      have h19 : 19 ≤ p4 := by
        by_contra! h; exact (by decide : ∀ t < 19, 17 < t → ¬ t.Prime) p4 h (by omega) hp4
      have h23 : 23 ≤ q := by
        by_contra! h; exact (by decide : ∀ t < 23, 19 < t → ¬ t.Prime) q h (by omega) hq
      exact hnot5 17 19 23 (by decide) (by decide) (by decide) h17 h19 h23 (by decide)
    have hmem19 : (p3, p4) ∈ validPairs19 := by
      have hp3_cases : p3 = 7 ∨ p3 = 11 ∨ p3 = 13 :=
        (by decide : ∀ t < 17, 7 ≤ t → t.Prime → t = 7 ∨ t = 11 ∨ t = 13) p3 hp3_lt17 h7p3 hp3
      rcases hp3_cases with rfl | rfl | rfl
      · have hp4_lt71 : p4 < 71 := by
          by_contra! h71
          have h73 : 73 ≤ q := by
            by_contra! h; exact (by decide : ∀ t < 73, 71 < t → ¬ t.Prime) q h (by omega) hq
          exact hnot5 7 71 73 (by decide) (by decide) (by decide) le_rfl h71 h73 (by decide)
        exact (by decide : ∀ t < 71, 7 < t → t.Prime → (7, t) ∈ validPairs19) p4 hp4_lt71 hord.1 hp4
      · have hp4_lt23 : p4 < 23 := by
          by_contra! h23
          have h29 : 29 ≤ q := by
            by_contra! h; exact (by decide : ∀ t < 29, 23 < t → ¬ t.Prime) q h (by omega) hq
          exact hnot5 11 23 29 (by decide) (by decide) (by decide) le_rfl h23 h29 (by decide)
        exact (by decide : ∀ t < 23, 11 < t → t.Prime → (11, t) ∈ validPairs19) p4 hp4_lt23 hord.1 hp4
      · have hp4_lt19 : p4 < 19 := by
          by_contra! h19
          have h23 : 23 ≤ q := by
            by_contra! h; exact (by decide : ∀ t < 23, 19 < t → ¬ t.Prime) q h (by omega) hq
          exact hnot5 13 19 23 (by decide) (by decide) (by decide) le_rfl h19 h23 (by decide)
        exact (by decide : ∀ t < 19, 13 < t → t.Prime → (13, t) ∈ validPairs19) p4 hp4_lt19 hord.1 hp4
    rw [hm_eq] at hm_ab hm_prim ⊢
    exact rank5_pseudoperfect hmem19 hq hord.2 hf5 hfc hfd hfe hm_ab hm_prim
  · simp [hls_cases] at hls_len; omega
