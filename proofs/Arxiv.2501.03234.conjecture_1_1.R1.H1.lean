import OMAReductions.R_Arxiv_2501_03234_conjecture_1_1_R1
import Mathlib.Tactic

/-!
# Positivity of the finite theta sums

The floor-sum identity is from the merged reduction by @sebastianbachmaier
(#5611). The proof below adapts the cyclic-correlation and bounded-limb
validation lemmas of @MattGaiser (#18042, commit 3127026a), whose certificate
treats the stronger bound above 3119. That work credits @steveDOTdigital
(#7053), @ahmeterdempmk (#12097), and @Ehdunhackme for related work.

Here a doubling algorithm generates a full multiplicative orbit in parallel.
Each stage multiplies the packed residues by one scalar and uses a reciprocal
with 34 fractional bits for modular reduction. The generator is untrusted:
the validator checks every residue and its successor and certifies the order.
The intervals below independently cover all odd primes from 3 to 99999.
-/

namespace ThetaFiniteRange
open Finset

def floorSign (a b : ℕ) : ℤ :=
  ∑ j ∈ Ico 1 b, (-1 : ℤ) ^ (a * j / b)

lemma prime_quotient_reflection (p a j : ℕ) (hp : p.Prime)
    (ha : a ∈ Ico 1 p) (hj : j ∈ Ico 1 p) :
    (p - a) * j / p + a * j / p + 1 = j := by
  simp only [mem_Ico] at ha hj
  exact OMA.R_Arxiv_2501_03234_conjecture_1_1_R1.refl_aux p a j hp (by omega) ha.2 (by omega) hj.2

lemma sum_reflection (p : ℕ) (f : ℕ → ℤ) :
    (∑ a ∈ Ico 1 p, f (p - a)) = ∑ a ∈ Ico 1 p, f a := by
  simpa using (Finset.sum_Ico_reflect f 1 (m := p) (n := p) (by omega))

/-- The floor-sign matrix expression, proved directly from the upstream definition. -/
lemma S_eq_floorSign (p : ℕ) (hp : p.Prime) :
    Arxiv.«2501.03234».S p = ∑ a ∈ Ico 1 p, floorSign a p :=
  OMA.R_Arxiv_2501_03234_conjecture_1_1_R1.S_eq p hp

lemma floorSign_even (a p : ℕ) (hp : p.Prime) (ha : a ∈ Ico 1 p) (he : Even a) :
    floorSign a p = 0 := by
  have hpair : (∑ j ∈ Ico 1 p, (-1 : ℤ) ^ (a * (p - j) / p)) =
      - ∑ j ∈ Ico 1 p, (-1 : ℤ) ^ (a * j / p) := by
    rw [← Finset.sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    have hq := prime_quotient_reflection p j a hp hj ha
    rw [mul_comm (p - j) a, mul_comm j a] at hq
    have hpar : Even (a * (p - j) / p + a * j / p + 1) := by rw [hq]; exact he
    have hzero : (a * (p - j) / p + a * j / p) % 2 = 1 := by
      rw [Nat.even_iff] at hpar
      omega
    by_cases h0 : (a * j / p) % 2 = 0
    · have h1 : (a * (p - j) / p) % 2 = 1 := by omega
      simp [neg_one_pow_eq_pow_mod_two, h0, h1]
    · have h1 : (a * j / p) % 2 = 1 := by omega
      have hv : (a * (p - j) / p) % 2 = 0 := by omega
      simp [neg_one_pow_eq_pow_mod_two, h1, hv]
  have hs : floorSign a p = -floorSign a p := by
    calc
      _ = ∑ j ∈ Ico 1 p, (-1 : ℤ) ^ (a * (p - j) / p) :=
        (sum_reflection p (fun j => (-1 : ℤ) ^ (a * j / p))).symm
      _ = _ := hpair
  omega

lemma filter_even_sum_reflection (p : ℕ) (hp : Odd p) (f : ℕ → ℤ) :
    (∑ j ∈ (Ico 1 p).filter Even, f j) =
      ∑ j ∈ (Ico 1 p).filter Odd, f (p - j) := by
  apply Finset.sum_bij (fun j _ => p - j)
  · intro j hj
    simp only [mem_filter, mem_Ico] at hj ⊢
    have hpmod := Nat.odd_iff.mp hp
    have hjmod := Nat.even_iff.mp hj.2
    refine ⟨⟨by omega, by omega⟩, Nat.odd_iff.mpr (by omega)⟩
  · intro j hj k hk he
    simp only [mem_filter, mem_Ico] at hj hk
    omega
  · intro j hj
    simp only [mem_filter, mem_Ico] at hj
    refine ⟨p - j, ?_, by omega⟩
    simp only [mem_filter, mem_Ico]
    have hpmod := Nat.odd_iff.mp hp
    have hjmod := Nat.odd_iff.mp hj.2
    exact ⟨⟨by omega, by omega⟩, Nat.even_iff.mpr (by omega)⟩
  · intro j hj
    simp only [mem_filter, mem_Ico] at hj
    congr 1
    omega

lemma floorSign_odd_reflection (a p j : ℕ) (hp : p.Prime)
    (ha : a ∈ Ico 1 p) (hj : j ∈ Ico 1 p) (hoa : Odd a) :
    (-1 : ℤ) ^ (a * (p - j) / p) = (-1 : ℤ) ^ (a * j / p) := by
  have hq := prime_quotient_reflection p j a hp hj ha
  rw [mul_comm (p - j) a, mul_comm j a] at hq
  have hm := Nat.odd_iff.mp hoa
  have he : (a * (p - j) / p) % 2 = (a * j / p) % 2 := by omega
  conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
  conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
  rw [he]

lemma floorSign_odd (a p : ℕ) (hp : p.Prime) (hop : Odd p)
    (ha : a ∈ Ico 1 p) (hoa : Odd a) :
    floorSign a p = 2 * ∑ j ∈ (Ico 1 p).filter Odd, (-1 : ℤ) ^ (a * j / p) := by
  have he : (∑ j ∈ (Ico 1 p).filter Even, (-1 : ℤ) ^ (a * j / p)) =
      ∑ j ∈ (Ico 1 p).filter Odd, (-1 : ℤ) ^ (a * j / p) := by
    rw [filter_even_sum_reflection p hop]
    apply sum_congr rfl
    intro j hj
    exact floorSign_odd_reflection a p j hp ha (mem_filter.mp hj).1 hoa
  have hs := Finset.sum_filter_add_sum_filter_not (Ico 1 p) Odd
    (fun j => (-1 : ℤ) ^ (a * j / p))
  simp only [Nat.not_odd_iff_even] at hs
  unfold floorSign
  linarith

lemma S_eq_twice_odd_square (p : ℕ) (hp : p.Prime) (hop : Odd p) :
    Arxiv.«2501.03234».S p =
      2 * ∑ a ∈ (Ico 1 p).filter Odd, ∑ j ∈ (Ico 1 p).filter Odd,
        (-1 : ℤ) ^ (a * j / p) := by
  rw [S_eq_floorSign p hp]
  have hf : (∑ a ∈ (Ico 1 p).filter (fun a => ¬ Odd a), floorSign a p) = 0 := by
    apply sum_eq_zero
    intro a ha
    exact floorSign_even a p hp (mem_filter.mp ha).1
      (Nat.not_odd_iff_even.mp (mem_filter.mp ha).2)
  have hs := Finset.sum_filter_add_sum_filter_not (Ico 1 p) Odd (fun a => floorSign a p)
  rw [hf, add_zero] at hs
  rw [← hs]
  rw [mul_sum]
  apply sum_congr rfl
  intro a ha
  exact floorSign_odd a p hp hop (mem_filter.mp ha).1 (mem_filter.mp ha).2

lemma odd_interval_card (m : ℕ) : ((Ico 1 (2 * m + 1)).filter Odd).card = m := by
  have hs : (Ico 1 (2 * m + 1)).filter Odd = (range m).image (fun j => 2 * j + 1) := by
    ext j
    simp only [mem_filter, mem_Ico, mem_image, mem_range]
    constructor
    · rintro ⟨⟨hj1, hj2⟩, ⟨r, hr⟩⟩
      exact ⟨r, by omega, by omega⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨by omega, by omega⟩, Nat.odd_iff.mpr (by omega)⟩
  rw [hs, card_image_of_injective _ (fun j k h => by omega), card_range]

lemma odd_product_floor_sign (a b p : ℕ) (ha : Odd a) (hb : Odd b) (hp : Odd p) :
    (-1 : ℤ) ^ (a * b / p) = if Odd (a * b % p) then 1 else -1 := by
  have hab := Nat.odd_iff.mp (ha.mul hb)
  have hpm := Nat.odd_iff.mp hp
  have hprod : (p * (a * b / p)) % 2 = (a * b / p) % 2 := by
    rw [Nat.mul_mod, hpm]
    simp
  have hsum : (a * b % p + p * (a * b / p)) % 2 = 1 := by
    rw [Nat.mod_add_div]
    exact hab
  rw [Nat.add_mod, hprod] at hsum
  by_cases hq : (a * b / p) % 2 = 0
  · have hr : Odd (a * b % p) := Nat.odd_iff.mpr (by omega)
    simp [neg_one_pow_eq_pow_mod_two, hq, hr]
  · have hq1 : (a * b / p) % 2 = 1 := by omega
    have hr : ¬ Odd (a * b % p) := by
      rw [Nat.odd_iff]
      omega
    simp [neg_one_pow_eq_pow_mod_two, hq1, hr]

lemma sum_sign_indicator {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (∑ x ∈ s, if P x then (1 : ℤ) else -1) = 2 * ((s.filter P).card : ℤ) - s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    by_cases hP : P a <;> simp [Finset.filter_insert, Finset.mem_filter, ha, hP, ih] <;> ring

def oddPairs (p : ℕ) : Finset (ℕ × ℕ) :=
  ((Ico 1 p).filter Odd) ×ˢ ((Ico 1 p).filter Odd)

def goodOddPairs (p : ℕ) : Finset (ℕ × ℕ) :=
  (oddPairs p).filter (fun z => Odd (z.1 * z.2 % p))

lemma S_eq_goodOddPairs (p : ℕ) (hp : p.Prime) (hop : Odd p) :
    Arxiv.«2501.03234».S p =
      4 * ((goodOddPairs p).card : ℤ) - 2 * (((Ico 1 p).filter Odd).card : ℤ) ^ 2 := by
  have hprod : (∑ z ∈ oddPairs p, (-1 : ℤ) ^ (z.1 * z.2 / p)) =
      ∑ a ∈ (Ico 1 p).filter Odd, ∑ b ∈ (Ico 1 p).filter Odd,
        (-1 : ℤ) ^ (a * b / p) := by
    unfold oddPairs
    rw [Finset.sum_product]
  rw [S_eq_twice_odd_square p hp hop, ← hprod]
  have he : (∑ z ∈ oddPairs p, (-1 : ℤ) ^ (z.1 * z.2 / p)) =
      2 * ((goodOddPairs p).card : ℤ) - (oddPairs p).card := by
    calc
      _ = ∑ z ∈ oddPairs p, if Odd (z.1 * z.2 % p) then (1 : ℤ) else -1 := by
        apply sum_congr rfl
        intro z hz
        have hz' := mem_product.mp hz
        exact odd_product_floor_sign z.1 z.2 p (mem_filter.mp hz'.1).2
          (mem_filter.mp hz'.2).2 hop
      _ = _ := sum_sign_indicator _ _
  change 2 * (∑ z ∈ oddPairs p, (-1 : ℤ) ^ (z.1 * z.2 / p)) = _
  rw [he]
  simp only [oddPairs, Finset.card_product, Nat.cast_mul]
  ring

open Finset

namespace Packed

def repunit (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + B * repunit B n

def constPack (B n c : ℕ) : ℕ := c * repunit B n

def digit (L X i : ℕ) : ℕ := X / (2 ^ L) ^ i % 2 ^ L

lemma constPack_succ (B n c : ℕ) :
    constPack B (n + 1) c = c + B * constPack B n c := by
  simp only [constPack, repunit]
  ring

lemma repunit_identity (B n : ℕ) (hB : 1 < B) :
    (B - 1) * repunit B n + 1 = B ^ n := by
  have hsub : B - 1 + 1 = B := by omega
  induction n with
  | zero => simp [repunit]
  | succ n ih =>
    rw [repunit, pow_succ]
    nlinarith

lemma repunit_eq_div (B n : ℕ) (hB : 1 < B) :
    repunit B n = (B ^ n - 1) / (B - 1) := by
  rw [← repunit_identity B n hB, Nat.add_sub_cancel]
  rw [Nat.mul_div_cancel_left _ (by omega : 0 < B - 1)]

lemma constPack_mod (B n c : ℕ) (_hB : 0 < B) (hc : c < B) :
    constPack B (n + 1) c % B = c := by
  rw [constPack_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

lemma constPack_div (B n c : ℕ) (hB : 0 < B) (hc : c < B) :
    constPack B (n + 1) c / B = constPack B n c := by
  rw [constPack_succ, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hc, zero_add]

lemma digit_zero (L X : ℕ) : digit L X 0 = X % 2 ^ L := by simp [digit]

lemma digit_succ (L X i : ℕ) :
    digit L X (i + 1) = digit L (X / 2 ^ L) i := by
  simp only [digit, pow_succ', Nat.div_div_eq_div_mul]

lemma digit_constPack (L n c i : ℕ) (hc : c < 2 ^ L) (hi : i < n) :
    digit L (constPack (2 ^ L) n c) i = c := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rw [digit_zero, constPack_mod _ _ _ (by positivity) hc]
    | succ i =>
      rw [digit_succ, constPack_div _ _ _ (by positivity) hc]
      exact ih i (by omega)

lemma digit_and (L X Y i : ℕ) :
    digit L (X &&& Y) i = digit L X i &&& digit L Y i := by
  simp only [digit, ← pow_mul, Nat.and_div_two_pow, Nat.and_mod_two_pow]

lemma clean_digit_le (L n c X i : ℕ) (hc : c < 2 ^ L) (hi : i < n)
    (h : X &&& constPack (2 ^ L) n c = X) : digit L X i ≤ c := by
  have hd := congrArg (fun z => digit L z i) h
  rw [digit_and, digit_constPack L n c i hc hi] at hd
  calc
    _ = digit L X i &&& c := hd.symm
    _ ≤ c := Nat.and_le_right

lemma constPack_lt (B n c : ℕ) (_hB : 0 < B) (hc : c < B) :
    constPack B n c < B ^ n := by
  induction n with
  | zero => simp [constPack, repunit]
  | succ n ih =>
    rw [constPack_succ, pow_succ']
    have hm := Nat.mul_le_mul_left B (Nat.succ_le_of_lt ih)
    nlinarith

lemma clean_lt (L n c X : ℕ) (hc : c < 2 ^ L)
    (h : X &&& constPack (2 ^ L) n c = X) : X < (2 ^ L) ^ n := by
  calc
    _ = X &&& constPack (2 ^ L) n c := h.symm
    _ ≤ constPack (2 ^ L) n c := Nat.and_le_right
    _ < _ := constPack_lt _ _ _ (by positivity) hc



lemma mod_add_noCarry (L X Y : ℕ) (h : X % 2 ^ L + Y % 2 ^ L < 2 ^ L) :
    (X + Y) % 2 ^ L = X % 2 ^ L + Y % 2 ^ L := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt h]

lemma div_add_noCarry (L X Y : ℕ) (h : X % 2 ^ L + Y % 2 ^ L < 2 ^ L) :
    (X + Y) / 2 ^ L = X / 2 ^ L + Y / 2 ^ L := by
  rw [Nat.add_div (by positivity : 0 < 2 ^ L), if_neg (Nat.not_le.mpr h), add_zero]

lemma digit_add (L X Y i : ℕ)
    (h : ∀ j ≤ i, digit L X j + digit L Y j < 2 ^ L) :
    digit L (X + Y) i = digit L X i + digit L Y i := by
  induction i generalizing X Y with
  | zero =>
    simpa only [digit_zero] using mod_add_noCarry L X Y (by simpa only [digit_zero] using h 0 (by omega))
  | succ i ih =>
    have h0 : X % 2 ^ L + Y % 2 ^ L < 2 ^ L := by
      simpa only [digit_zero] using h 0 (by omega)
    calc
      _ = digit L ((X + Y) / 2 ^ L) i := digit_succ L (X + Y) i
      _ = digit L (X / 2 ^ L + Y / 2 ^ L) i := by rw [div_add_noCarry L X Y h0]
      _ = digit L (X / 2 ^ L) i + digit L (Y / 2 ^ L) i := ih _ _ (by
        intro j hj
        simpa only [← digit_succ] using h (j + 1) (by omega))
      _ = _ := by rw [← digit_succ, ← digit_succ]

lemma scalar_decomposition (L X k : ℕ) :
    k * X = k * (X % 2 ^ L) + 2 ^ L * (k * (X / 2 ^ L)) := by
  calc
    _ = k * (X % 2 ^ L + 2 ^ L * (X / 2 ^ L)) := by rw [Nat.mod_add_div]
    _ = _ := by ring

lemma mod_mul_noCarry (L X k : ℕ) (h : k * (X % 2 ^ L) < 2 ^ L) :
    (k * X) % 2 ^ L = k * (X % 2 ^ L) := by
  rw [scalar_decomposition L X k, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

lemma div_mul_noCarry (L X k : ℕ) (h : k * (X % 2 ^ L) < 2 ^ L) :
    (k * X) / 2 ^ L = k * (X / 2 ^ L) := by
  rw [scalar_decomposition L X k, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt h, zero_add]

lemma digit_mul (L X k i : ℕ) (h : ∀ j ≤ i, k * digit L X j < 2 ^ L) :
    digit L (k * X) i = k * digit L X i := by
  induction i generalizing X with
  | zero =>
    simpa only [digit_zero] using mod_mul_noCarry L X k (by simpa only [digit_zero] using h 0 (by omega))
  | succ i ih =>
    have h0 : k * (X % 2 ^ L) < 2 ^ L := by simpa only [digit_zero] using h 0 (by omega)
    calc
      _ = digit L ((k * X) / 2 ^ L) i := digit_succ L (k * X) i
      _ = digit L (k * (X / 2 ^ L)) i := by rw [div_mul_noCarry L X k h0]
      _ = k * digit L (X / 2 ^ L) i := ih _ (by
        intro j hj
        simpa only [← digit_succ] using h (j + 1) (by omega))
      _ = _ := by rw [← digit_succ]

lemma clean_complement_digit_le (L n c t X Y i : ℕ) (hc : c < 2 ^ L)
    (hcc : 2 * c < 2 ^ L) (ht : t < 2 ^ L) (hi : i < n)
    (hX : X &&& constPack (2 ^ L) n c = X)
    (hY : Y &&& constPack (2 ^ L) n c = Y)
    (hs : X + Y = constPack (2 ^ L) n t) : digit L X i ≤ t := by
  have hadd : ∀ j ≤ i, digit L X j + digit L Y j < 2 ^ L := by
    intro j hj
    have hx := clean_digit_le L n c X j hc (by omega) hX
    have hy := clean_digit_le L n c Y j hc (by omega) hY
    omega
  have hd := congrArg (fun z => digit L z i) hs
  rw [digit_add L X Y i hadd, digit_constPack L n t i ht hi] at hd
  omega



def pack (L n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ range n, f i * (2 ^ L) ^ i

lemma pack_zero (L : ℕ) (f : ℕ → ℕ) : pack L 0 f = 0 := by simp [pack]

lemma pack_succ (L n : ℕ) (f : ℕ → ℕ) :
    pack L (n + 1) f = pack L n f + f n * (2 ^ L) ^ n := by
  exact sum_range_succ _ _

lemma pack_low (L n : ℕ) (f : ℕ → ℕ) :
    pack L (n + 1) f = f 0 + 2 ^ L * pack L n (fun j => f (j + 1)) := by
  unfold pack
  rw [sum_range_succ']
  have he : (∑ i ∈ range n, f (i + 1) * (2 ^ L) ^ (i + 1)) =
      ∑ i ∈ range n, 2 ^ L * (f (i + 1) * (2 ^ L) ^ i) := by
    apply sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  rw [he, ← mul_sum]
  simp
  omega

lemma pack_lt (L n : ℕ) (f : ℕ → ℕ) (hf : ∀ i < n, f i < 2 ^ L) :
    pack L n f < (2 ^ L) ^ n := by
  induction n with
  | zero => simp [pack_zero]
  | succ n ih =>
    have hprev := ih (fun i hi => hf i (by omega))
    have hlast := hf n (by omega)
    have hm := Nat.mul_le_mul_right ((2 ^ L) ^ n) (Nat.succ_le_of_lt hlast)
    rw [pack_succ, pow_succ']
    nlinarith

lemma pack_div (L n : ℕ) (f : ℕ → ℕ) (hf : f 0 < 2 ^ L) :
    pack L (n + 1) f / 2 ^ L = pack L n (fun j => f (j + 1)) := by
  rw [pack_low, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hf, zero_add]

lemma digit_pack (L n : ℕ) (f : ℕ → ℕ) (hf : ∀ j < n, f j < 2 ^ L)
    (i : ℕ) (hi : i < n) : digit L (pack L n f) i = f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      rw [digit_zero, pack_low, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (hf 0 (by omega))]
    | succ i =>
      rw [digit_succ, pack_div L n f (hf 0 (by omega))]
      exact ih _ (fun j hj => hf (j + 1) (by omega)) i (by omega)

lemma pack_digits (L n X : ℕ) (hX : X < (2 ^ L) ^ n) :
    pack L n (fun i => digit L X i) = X := by
  induction n generalizing X with
  | zero =>
    have hz : X = 0 := by simpa using hX
    subst X
    simp [pack_zero]
  | succ n ih =>
    have ht : X / 2 ^ L < (2 ^ L) ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      simpa only [pow_succ] using hX
    have he : pack L n (fun i => digit L X (i + 1)) = X / 2 ^ L := by
      simpa only [digit_succ] using ih (X / 2 ^ L) ht
    rw [pack_low, digit_zero, he]
    exact Nat.mod_add_div X (2 ^ L)

lemma digit_lt (L X i : ℕ) : digit L X i < 2 ^ L := Nat.mod_lt _ (by positivity)

lemma digit_high_zero (L n X i : ℕ) (hX : X < (2 ^ L) ^ n) (hi : n ≤ i) :
    digit L X i = 0 := by
  have hp : (2 ^ L) ^ n ≤ (2 ^ L) ^ i := Nat.pow_le_pow_right (by positivity) hi
  unfold digit
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hX hp)]
  simp

lemma pack_single (L k : ℕ) :
    pack L (k + 1) (fun i => if i = k then 1 else 0) = (2 ^ L) ^ k := by
  simp [pack, ite_mul]

lemma digit_pow_below (L k i : ℕ) (hL : 0 < L) (hi : i < k) :
    digit L ((2 ^ L) ^ k) i = 0 := by
  have hb : 1 < 2 ^ L := Nat.one_lt_two_pow (by omega)
  rw [← pack_single L k, digit_pack L (k + 1) _ (by
    intro j hj
    split_ifs <;> omega) i (by omega)]
  rw [if_neg (by omega : i ≠ k)]

lemma digit_add_high (L X k i : ℕ) (hL : 0 < L) (hi : i < k) :
    digit L (X + (2 ^ L) ^ k) i = digit L X i := by
  have hz : ∀ j ≤ i, digit L ((2 ^ L) ^ k) j = 0 := by
    intro j hj
    exact digit_pow_below L k j hL (by omega)
  rw [digit_add L X ((2 ^ L) ^ k) i (by
    intro j hj
    rw [hz j hj, add_zero]
    exact digit_lt L X j), hz i (by omega), add_zero]



structure LimbOrbit (p g L n X Q : ℕ) : Prop where
  width_pos : 0 < L
  modulus_gt_one : 1 < p
  multiplier_pos : 0 < g
  length_pos : 0 < n
  word_bound : p * g < 2 ^ L
  size_bound : X < (2 ^ L) ^ n
  x_bound : ∀ i < n, digit L X i < p
  q_bound : ∀ i < n, digit L Q i < g
  first : X % 2 ^ L = 1
  recurrence : g * X = X / 2 ^ L + (2 ^ L) ^ (n - 1) + p * Q

lemma LimbOrbit.of_masks (p g L n c X Q : ℕ) (hp : 1 < p) (hg : 0 < g) (hn : 0 < n)
    (hword : p * g < 2 ^ L) (hcc : 2 * c < 2 ^ L)
    (hX : X &&& constPack (2 ^ L) n c = X)
    (hXC : (constPack (2 ^ L) n (p - 1) - X) &&& constPack (2 ^ L) n c =
      constPack (2 ^ L) n (p - 1) - X)
    (hXB : X ≤ constPack (2 ^ L) n (p - 1))
    (hQ : Q &&& constPack (2 ^ L) n c = Q)
    (hQC : (constPack (2 ^ L) n (g - 1) - Q) &&& constPack (2 ^ L) n c =
      constPack (2 ^ L) n (g - 1) - Q)
    (hQB : Q ≤ constPack (2 ^ L) n (g - 1))
    (hfirst : X % 2 ^ L = 1)
    (hrec : g * X = X / 2 ^ L + (2 ^ L) ^ (n - 1) + p * Q) :
    LimbOrbit p g L n X Q := by
  have hpg : p ≤ p * g := Nat.le_mul_of_pos_right p hg
  have hgp : g ≤ p * g := Nat.le_mul_of_pos_left g (by omega)
  have hc : c < 2 ^ L := by omega
  have htP : p - 1 < 2 ^ L := by omega
  have htG : g - 1 < 2 ^ L := by omega
  have hL : 0 < L := by
    by_contra! hz
    have hzero : L = 0 := by omega
    rw [hzero, pow_zero] at hword
    omega
  refine ⟨hL, hp, hg, hn, hword, clean_lt L n c X hc hX, ?_, ?_, hfirst, hrec⟩
  · intro i hi
    have hs : X + (constPack (2 ^ L) n (p - 1) - X) = constPack (2 ^ L) n (p - 1) := by omega
    have hb := clean_complement_digit_le L n c (p - 1) X _ i hc hcc htP hi hX hXC hs
    omega
  · intro i hi
    have hs : Q + (constPack (2 ^ L) n (g - 1) - Q) = constPack (2 ^ L) n (g - 1) := by omega
    have hb := clean_complement_digit_le L n c (g - 1) Q _ i hc hcc htG hi hQ hQC hs
    omega

lemma LimbOrbit.step {p g L n X Q : ℕ} (H : LimbOrbit p g L n X Q)
    (i : ℕ) (hi : i + 1 < n) :
    g * digit L X i = digit L X (i + 1) + p * digit L Q i := by
  let Y := X / 2 ^ L + (2 ^ L) ^ (n - 1)
  have hy (j : ℕ) (hj : j + 1 < n) : digit L Y j = digit L X (j + 1) := by
    dsimp [Y]
    rw [digit_add_high L (X / 2 ^ L) (n - 1) j H.width_pos (by omega)]
    exact (digit_succ L X j).symm
  have hxmul : digit L (g * X) i = g * digit L X i := by
    apply digit_mul
    intro j hj
    have hm := Nat.mul_le_mul_left g (H.x_bound j (by omega)).le
    exact lt_of_le_of_lt hm (by simpa only [mul_comm] using H.word_bound)
  have hqmul (j : ℕ) (hj : j < n) : digit L (p * Q) j = p * digit L Q j := by
    apply digit_mul
    intro k hk
    have hm := Nat.mul_le_mul_left p (H.q_bound k (by omega)).le
    exact lt_of_le_of_lt hm H.word_bound
  have hcarry : ∀ j ≤ i, digit L Y j + digit L (p * Q) j < 2 ^ L := by
    intro j hj
    rw [hy j (by omega), hqmul j (by omega)]
    calc
      _ < p + p * digit L Q j := Nat.add_lt_add_right (H.x_bound (j + 1) (by omega)) _
      _ = p * (digit L Q j + 1) := by ring
      _ ≤ p * g := Nat.mul_le_mul_left p (Nat.succ_le_of_lt (H.q_bound j (by omega)))
      _ < _ := H.word_bound
  have hd := congrArg (fun z => digit L z i) H.recurrence
  change digit L (g * X) i = digit L (Y + p * Q) i at hd
  rw [hxmul, digit_add L Y (p * Q) i hcarry, hy i hi, hqmul i (by omega)] at hd
  exact hd

lemma LimbOrbit.next_mod {p g L n X Q : ℕ} (H : LimbOrbit p g L n X Q)
    (i : ℕ) (hi : i + 1 < n) :
    digit L X (i + 1) = (g * digit L X i) % p := by
  rw [H.step i hi, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (H.x_bound (i + 1) hi)]

lemma LimbOrbit.orbit_eq {p g L n X Q : ℕ} (H : LimbOrbit p g L n X Q)
    (i : ℕ) (hi : i < n) : digit L X i = g ^ i % p := by
  induction i with
  | zero =>
    simpa only [digit_zero, pow_zero, Nat.mod_eq_of_lt H.modulus_gt_one] using H.first
  | succ i ih =>
    rw [H.next_mod i hi, ih (by omega)]
    simp only [pow_succ, Nat.mul_mod, Nat.mod_mod, mul_comm]



def runPow : ℕ → ℕ → ℕ → ℕ → Option ℕ
  | 0, p, _, n => if n = 0 then some (1 % p) else none
  | fuel + 1, p, a, n =>
      if n = 0 then some (1 % p) else
      (runPow fuel p (a * a % p) (n / 2)).map
        (fun w => if n % 2 = 0 then w else (w * a) % p)

lemma runPow_cast_sound {fuel p a n v : ℕ} (h : runPow fuel p a n = some v) :
    (v : ZMod p) = (a : ZMod p) ^ n := by
  induction fuel generalizing p a n v with
  | zero =>
    by_cases hn : n = 0
    · subst n
      simp only [runPow, if_true, Option.some.injEq] at h
      subst v
      simp
    · simp [runPow, hn] at h
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst n
      simp only [runPow, if_true, Option.some.injEq] at h
      subst v
      simp
    · simp only [runPow, if_neg hn] at h
      rcases Option.map_eq_some_iff.mp h with ⟨w, hw, hv⟩
      have hwc := ih hw
      simp only [ZMod.natCast_mod, Nat.cast_mul] at hwc
      have he : n = 2 * (n / 2) + n % 2 := by omega
      have hpow : (a : ZMod p) ^ n =
          ((a : ZMod p) * a) ^ (n / 2) * (a : ZMod p) ^ (n % 2) := by
        calc
          _ = (a : ZMod p) ^ (2 * (n / 2) + n % 2) := congrArg _ he
          _ = _ := by rw [pow_add, pow_mul, pow_two]
      by_cases hm : n % 2 = 0
      · simp only [if_pos hm] at hv
        subst v
        rw [hpow, hm, pow_zero, mul_one]
        exact hwc
      · have hm1 : n % 2 = 1 := by omega
        simp only [if_neg hm] at hv
        subst v
        rw [hpow, hm1, pow_one]
        simp only [ZMod.natCast_mod, Nat.cast_mul, hwc]

lemma runPow_lt {fuel p a n v : ℕ} (hp : 0 < p) (h : runPow fuel p a n = some v) :
    v < p := by
  induction fuel generalizing p a n v with
  | zero =>
    by_cases hn : n = 0
    · simp only [runPow, if_pos hn, Option.some.injEq] at h
      subst v
      exact Nat.mod_lt _ hp
    · simp [runPow, hn] at h
  | succ fuel ih =>
    by_cases hn : n = 0
    · simp only [runPow, if_pos hn, Option.some.injEq] at h
      subst v
      exact Nat.mod_lt _ hp
    · simp only [runPow, if_neg hn] at h
      rcases Option.map_eq_some_iff.mp h with ⟨w, hw, hv⟩
      by_cases hm : n % 2 = 0
      · simp only [if_pos hm] at hv
        subst v
        exact ih hp hw
      · simp only [if_neg hm] at hv
        subst v
        exact Nat.mod_lt _ hp

lemma runPow_nat_sound {fuel p a n v : ℕ} (hp : 0 < p)
    (h : runPow fuel p a n = some v) : v = a ^ n % p := by
  have hc := runPow_cast_sound h
  rw [← Nat.cast_pow] at hc
  have hv := runPow_lt hp h
  have he := congrArg (fun z : ZMod p => z.val) hc
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hv] using he

def rootCheck (p g n : ℕ) : Bool :=
  match runPow 32 p g n with
  | none => false
  | some v => decide (v = 1 % p) && n.primeFactorsList.all (fun q =>
      match runPow 32 p g (n / q) with
      | none => false
      | some w => decide (w ≠ 1 % p))

lemma rootCheck_sound (p g n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (h : rootCheck p g n = true) : IsPrimitiveRoot (g : ZMod p) n := by
  cases hv : runPow 32 p g n with
  | none => simp [rootCheck, hv] at h
  | some v =>
    simp only [rootCheck, hv, Bool.and_eq_true, decide_eq_true_eq] at h
    have hpow : (g : ZMod p) ^ n = 1 := by
      have hc := runPow_cast_sound hv
      rw [h.1] at hc
      simpa using hc.symm
    apply IsPrimitiveRoot.iff_orderOf.mpr
    apply orderOf_eq_of_pow_and_pow_div_prime hn hpow
    intro q hq hd heq
    have hmem : q ∈ n.primeFactorsList := (Nat.mem_primeFactorsList (by omega)).mpr ⟨hq, hd⟩
    have hc := List.all_eq_true.mp h.2 q hmem
    cases hw : runPow 32 p g (n / q) with
    | none => simp [hw] at hc
    | some w =>
      have hwne : w ≠ 1 % p := by simpa only [hw, decide_eq_true_eq] using hc
      have hnat := runPow_nat_sound hp hw
      rw [← Nat.cast_pow] at heq
      have hmod := congrArg (fun z : ZMod p => z.val) heq
      have hmod' : g ^ (n / q) % p = 1 % p := by simpa only [ZMod.val_natCast, ZMod.val_one_eq_one_mod] using hmod
      exact hwne (hnat.trans hmod')

def orbitValue (p g i : ℕ) : ℕ := ((g : ZMod p) ^ i).val

lemma orbitValue_eq_mod (p g i : ℕ) : orbitValue p g i = g ^ i % p := by
  unfold orbitValue
  rw [← Nat.cast_pow, ZMod.val_natCast]

lemma orbitValue_mem (p g n i : ℕ) (hp : p.Prime) (hn : 0 < n)
    (hr : IsPrimitiveRoot (g : ZMod p) n) : orbitValue p g i ∈ Ico 1 p := by
  let : Fact p.Prime := ⟨hp⟩
  have hz : (g : ZMod p) ^ i ≠ 0 := pow_ne_zero i (hr.ne_zero (by omega))
  exact mem_Ico.mpr ⟨(ZMod.val_pos.mpr hz), ZMod.val_lt _⟩

lemma orbitValue_injOn (p g n : ℕ) (hp : 0 < p)
    (hr : IsPrimitiveRoot (g : ZMod p) n) :
    Set.InjOn (orbitValue p g) (range n) := by
  let : NeZero p := ⟨by omega⟩
  intro i hi j hj he
  apply hr.pow_inj (mem_range.mp hi) (mem_range.mp hj)
  exact ZMod.val_injective p he

lemma orbitValue_image (p g : ℕ) (hp : p.Prime)
    (hr : IsPrimitiveRoot (g : ZMod p) (p - 1)) :
    (range (p - 1)).image (orbitValue p g) = Ico 1 p := by
  have hn : 0 < p - 1 := by have := hp.two_le; omega
  apply eq_of_subset_of_card_le
  · intro a ha
    rcases mem_image.mp ha with ⟨i, hi, rfl⟩
    exact orbitValue_mem p g (p - 1) i hp hn hr
  · rw [card_image_of_injOn (orbitValue_injOn p g (p - 1) hp.pos hr), card_range,
      Nat.card_Ico]

lemma sum_orbitValue (p g : ℕ) (hp : p.Prime)
    (hr : IsPrimitiveRoot (g : ZMod p) (p - 1)) (f : ℕ → ℕ) :
    (∑ i ∈ range (p - 1), f (orbitValue p g i)) = ∑ a ∈ Ico 1 p, f a := by
  rw [← orbitValue_image p g hp hr, sum_image (orbitValue_injOn p g (p - 1) hp.pos hr)]

lemma orbitValue_mul (p g n i j : ℕ) (hr : IsPrimitiveRoot (g : ZMod p) n) :
    orbitValue p g ((i + j) % n) = orbitValue p g i * orbitValue p g j % p := by
  unfold orbitValue
  rw [← pow_eq_pow_mod (i + j) hr.pow_eq_one, pow_add, ZMod.val_mul]

def cyclicCount (n : ℕ) (u : ℕ → ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range n, u i * u j * u ((i + j) % n)

lemma parity_product_indicator (a b p : ℕ) :
    (a % 2) * (b % 2) * ((a * b % p) % 2) =
      if Odd a ∧ Odd b ∧ Odd (a * b % p) then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one (a * b % p) with hc | hc <;>
    simp [Nat.odd_iff, ha, hb, hc]

lemma goodOddPairs_card_full (p : ℕ) :
    (goodOddPairs p).card = ∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 p,
      (a % 2) * (b % 2) * ((a * b % p) % 2) := by
  have he : goodOddPairs p = ((Ico 1 p) ×ˢ (Ico 1 p)).filter
      (fun z => Odd z.1 ∧ Odd z.2 ∧ Odd (z.1 * z.2 % p)) := by
    ext z
    simp only [goodOddPairs, oddPairs, mem_filter, mem_product]
    tauto
  rw [he, card_eq_sum_ones, sum_filter, sum_product]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  exact (parity_product_indicator a b p).symm

lemma cyclicCount_eq_goodOddPairs (p g : ℕ) (hp : p.Prime)
    (hr : IsPrimitiveRoot (g : ZMod p) (p - 1)) :
    cyclicCount (p - 1) (fun i => orbitValue p g i % 2) = (goodOddPairs p).card := by
  unfold cyclicCount
  rw [goodOddPairs_card_full]
  calc
    _ = ∑ i ∈ range (p - 1), ∑ j ∈ range (p - 1),
        (orbitValue p g i % 2) * (orbitValue p g j % 2) *
          ((orbitValue p g i * orbitValue p g j % p) % 2) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      dsimp only
      rw [orbitValue_mul p g (p - 1) i j hr]
    _ = ∑ i ∈ range (p - 1), ∑ b ∈ Ico 1 p,
        (orbitValue p g i % 2) * (b % 2) * ((orbitValue p g i * b % p) % 2) := by
      apply sum_congr rfl
      intro i hi
      exact sum_orbitValue p g hp hr (fun b =>
        (orbitValue p g i % 2) * (b % 2) * ((orbitValue p g i * b % p) % 2))
    _ = _ := sum_orbitValue p g hp hr (fun a => ∑ b ∈ Ico 1 p,
      (a % 2) * (b % 2) * ((a * b % p) % 2))

lemma two_mul_S_eq_cyclicCount (p g : ℕ) (hp : p.Prime) (hop : Odd p)
    (hr : IsPrimitiveRoot (g : ZMod p) (p - 1)) :
    2 * Arxiv.«2501.03234».S p =
      8 * (cyclicCount (p - 1) (fun i => orbitValue p g i % 2) : ℤ) - (p - 1 : ℕ) ^ 2 := by
  rw [S_eq_goodOddPairs p hp hop, cyclicCount_eq_goodOddPairs p g hp hr]
  obtain ⟨m, hm⟩ := hop
  have hpform : p = 2 * m + 1 := by omega
  have hc : ((Ico 1 p).filter Odd).card = m := by rw [hpform]; exact odd_interval_card m
  rw [hc, show p - 1 = 2 * m by omega]
  push_cast
  ring


def cyclicCoeff (n : ℕ) (u : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range n, if (i + j) % n = k then u i * u j else 0

lemma sum_weight_cyclicCoeff (n : ℕ) (hn : 0 < n) (u w : ℕ → ℕ) :
    (∑ k ∈ range n, w k * cyclicCoeff n u k) =
      ∑ i ∈ range n, ∑ j ∈ range n, u i * u j * w ((i + j) % n) := by
  simp only [cyclicCoeff, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  calc
    _ = ∑ k ∈ range n, if (i + j) % n = k then u i * u j * w k else 0 := by
      apply sum_congr rfl
      intro k hk
      split_ifs <;> simp_all [mul_comm]
    _ = _ := sum_ite_eq_of_mem (range n) ((i + j) % n) (fun k => u i * u j * w k)
      (mem_range.mpr (Nat.mod_lt _ hn))

lemma cyclicCoeff_le (n k : ℕ) (u : ℕ → ℕ) (hu : ∀ i < n, u i ≤ 1) :
    cyclicCoeff n u k ≤ n ^ 2 := by
  unfold cyclicCoeff
  calc
    _ ≤ ∑ i ∈ range n, ∑ j ∈ range n, 1 := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      split_ifs
      · simpa using Nat.mul_le_mul (hu i (mem_range.mp hi)) (hu j (mem_range.mp hj))
      · omega
    _ = _ := by simp [pow_two]

lemma cyclicCount_le (n : ℕ) (hn : 0 < n) (u : ℕ → ℕ)
    (hu : ∀ i < n, u i ≤ 1) : cyclicCount n u ≤ n ^ 2 := by
  unfold cyclicCount
  calc
    _ ≤ ∑ i ∈ range n, ∑ j ∈ range n, 1 := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have h1 := Nat.mul_le_mul (hu i (mem_range.mp hi)) (hu j (mem_range.mp hj))
      have h2 := Nat.mul_le_mul h1 (hu ((i + j) % n) (Nat.mod_lt _ hn))
      simpa using h2
    _ = _ := by simp [pow_two]

lemma pack_square (L n : ℕ) (u : ℕ → ℕ) :
    (pack L n u) ^ 2 =
      ∑ i ∈ range n, ∑ j ∈ range n, u i * u j * (2 ^ L) ^ (i + j) := by
  simp only [pow_two, pack, sum_mul, mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

lemma pack_cyclicCoeff (L n : ℕ) (hn : 0 < n) (u : ℕ → ℕ) :
    pack L n (cyclicCoeff n u) =
      ∑ i ∈ range n, ∑ j ∈ range n, u i * u j * (2 ^ L) ^ ((i + j) % n) := by
  unfold pack
  simpa only [mul_comm] using sum_weight_cyclicCoeff n hn u (fun k => (2 ^ L) ^ k)

lemma natCast_pred_mod (a : ℕ) (ha : 0 < a) : (a : ZMod (a - 1)) = 1 := by
  have he : a = (a - 1) + 1 := by omega
  calc
    _ = ((a - 1 : ℕ) : ZMod (a - 1)) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun k : ℕ => (k : ZMod (a - 1))) he
    _ = _ := by rw [ZMod.natCast_self, zero_add]

lemma square_mod_cyclic (L n : ℕ) (hn : 0 < n) (u : ℕ → ℕ) :
    (pack L n u) ^ 2 % ((2 ^ L) ^ n - 1) =
      pack L n (cyclicCoeff n u) % ((2 ^ L) ^ n - 1) := by
  have hp : ((2 ^ L : ℕ) : ZMod ((2 ^ L) ^ n - 1)) ^ n = 1 := by
    rw [← Nat.cast_pow]
    exact natCast_pred_mod ((2 ^ L) ^ n) (by positivity)
  push_cast at hp
  have he : ((pack L n u) ^ 2 : ZMod ((2 ^ L) ^ n - 1)) =
      (pack L n (cyclicCoeff n u) : ℕ) := by
    rw [← Nat.cast_pow, pack_square, pack_cyclicCoeff L n hn u]
    push_cast
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [pow_eq_pow_mod (i + j) hp]
  have hv := congrArg (fun z : ZMod ((2 ^ L) ^ n - 1) => z.val) he
  simpa only [← Nat.cast_pow, ZMod.val_natCast] using hv

lemma repunit_succ_high (B n : ℕ) :
    repunit B (n + 1) = repunit B n + B ^ n := by
  induction n with
  | zero => simp [repunit]
  | succ n ih =>
    calc
      _ = 1 + B * repunit B (n + 1) := rfl
      _ = 1 + B * (repunit B n + B ^ n) := by rw [ih]
      _ = _ := by rw [repunit, pow_succ']; ring

lemma pack_le_constPack (L n c : ℕ) (f : ℕ → ℕ) (hf : ∀ i < n, f i ≤ c) :
    pack L n f ≤ constPack (2 ^ L) n c := by
  induction n with
  | zero => simp [pack_zero, constPack, repunit]
  | succ n ih =>
    have hs : constPack (2 ^ L) (n + 1) c =
        constPack (2 ^ L) n c + c * (2 ^ L) ^ n := by
      unfold constPack
      rw [repunit_succ_high]
      ring
    rw [pack_succ, hs]
    exact Nat.add_le_add (ih (fun i hi => hf i (by omega)))
      (Nat.mul_le_mul_right ((2 ^ L) ^ n) (hf n (by omega)))

lemma repunit_pos (B n : ℕ) (hn : 0 < n) : 0 < repunit B n := by
  cases n with
  | zero => omega
  | succ n => simp only [repunit]; omega

lemma pack_lt_pred (L n c : ℕ) (hn : 0 < n) (hL : 0 < L)
    (f : ℕ → ℕ) (hf : ∀ i < n, f i ≤ c) (hc : c < 2 ^ L - 1) :
    pack L n f < (2 ^ L) ^ n - 1 := by
  have hB : 1 < 2 ^ L := Nat.one_lt_two_pow (by omega)
  have hr := repunit_identity (2 ^ L) n hB
  calc
    _ ≤ constPack (2 ^ L) n c := pack_le_constPack L n c f hf
    _ < constPack (2 ^ L) n (2 ^ L - 1) :=
      Nat.mul_lt_mul_of_pos_right hc (repunit_pos _ _ hn)
    _ = _ := by unfold constPack; omega

lemma cyclicFold_mod (P A : ℕ) (hA : 0 < A) :
    (P % A + P / A) % (A - 1) = P % (A - 1) := by
  have ha : A = A - 1 + 1 := by omega
  have he : P = (P % A + P / A) + (A - 1) * (P / A) := by
    have ht := Nat.mod_add_div P A
    have hm := congrArg (fun k : ℕ => k * (P / A)) ha
    nlinarith only [ht, hm]
  conv_rhs => rw [he]
  exact (Nat.add_mul_mod_self_left _ _ _).symm

def cyclicFold (L n P : ℕ) : ℕ :=
  (P &&& (2 ^ (L * n) - 1)) + (P >>> (L * n))

lemma cyclicFold_eq (L n P : ℕ) :
    cyclicFold L n P = P % (2 ^ L) ^ n + P / (2 ^ L) ^ n := by
  unfold cyclicFold
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]

lemma cyclicFold_square_eq_pack (L n : ℕ) (hn : 0 < n) (hL : 0 < L)
    (u : ℕ → ℕ) (hu : ∀ i < n, u i ≤ 1) (hB : n ^ 2 < 2 ^ L - 1)
    (hfold : cyclicFold L n ((pack L n u) ^ 2) < (2 ^ L) ^ n - 1) :
    cyclicFold L n ((pack L n u) ^ 2) = pack L n (cyclicCoeff n u) := by
  have he : cyclicFold L n ((pack L n u) ^ 2) % ((2 ^ L) ^ n - 1) =
      pack L n (cyclicCoeff n u) % ((2 ^ L) ^ n - 1) := by
    rw [cyclicFold_eq, cyclicFold_mod _ _ (by positivity), square_mod_cyclic L n hn u]
  rw [Nat.mod_eq_of_lt hfold,
    Nat.mod_eq_of_lt (pack_lt_pred L n (n ^ 2) hn hL _
      (fun i _ => cyclicCoeff_le n i u hu) hB)] at he
  exact he

lemma pack_mod_pred (L n : ℕ) (_hL : 0 < L) (f : ℕ → ℕ) :
    pack L n f % (2 ^ L - 1) = (∑ i ∈ range n, f i) % (2 ^ L - 1) := by
  have hbase := natCast_pred_mod (2 ^ L) (by positivity)
  push_cast at hbase
  have he : (pack L n f : ZMod (2 ^ L - 1)) =
      (∑ i ∈ range n, f i : ℕ) := by
    unfold pack
    push_cast
    simp only [hbase, one_pow, mul_one]
  have hv := congrArg (fun z : ZMod (2 ^ L - 1) => z.val) he
  simpa only [ZMod.val_natCast] using hv

lemma parityWord_digits (L n X i : ℕ) (hL : 0 < L) (hi : i < n) :
    digit L (X &&& repunit (2 ^ L) n) i = digit L X i % 2 := by
  rw [digit_and]
  have hr : digit L (repunit (2 ^ L) n) i = 1 := by
    simpa only [constPack, one_mul] using digit_constPack L n 1 i
      (Nat.one_lt_two_pow (by omega)) hi
  rw [hr, Nat.and_one_is_mod]

lemma maskedPack_eq (L n : ℕ) (hL : 0 < L) (u c : ℕ → ℕ)
    (hu : ∀ i < n, u i ≤ 1) (hc : ∀ i < n, c i < 2 ^ L) :
    pack L n c &&& ((2 ^ L - 1) * pack L n u) =
      pack L n (fun i => u i * c i) := by
  have hB : 1 < 2 ^ L := Nat.one_lt_two_pow (by omega)
  have huB : ∀ i < n, u i < 2 ^ L := fun i hi => lt_of_le_of_lt (hu i hi) hB
  have hbound : pack L n c &&& ((2 ^ L - 1) * pack L n u) < (2 ^ L) ^ n :=
    lt_of_le_of_lt Nat.and_le_left (pack_lt L n c hc)
  rw [← pack_digits L n _ hbound]
  change (∑ i ∈ range n, digit L (pack L n c &&& ((2 ^ L - 1) * pack L n u)) i *
    (2 ^ L) ^ i) = ∑ i ∈ range n, (u i * c i) * (2 ^ L) ^ i
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  have hscalar : ∀ j ≤ i, (2 ^ L - 1) * digit L (pack L n u) j < 2 ^ L := by
    intro j hj
    rw [digit_pack L n u huB j (by omega)]
    have hm := Nat.mul_le_mul_left (2 ^ L - 1) (hu j (by omega))
    omega
  rw [digit_and, digit_pack L n c hc i hi', digit_mul L _ _ i hscalar,
    digit_pack L n u huB i hi']
  have hui := hu i hi'
  rcases (show u i = 0 ∨ u i = 1 by omega) with hui' | hui' <;>
    simp [hui', Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hc i hi')]

lemma pack_congr (L n : ℕ) (f g : ℕ → ℕ) (h : ∀ i < n, f i = g i) :
    pack L n f = pack L n g := by
  unfold pack
  apply sum_congr rfl
  intro i hi
  rw [h i (mem_range.mp hi)]

lemma cyclicCount_congr (n : ℕ) (hn : 0 < n) (f g : ℕ → ℕ)
    (h : ∀ i < n, f i = g i) : cyclicCount n f = cyclicCount n g := by
  unfold cyclicCount
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [h i (mem_range.mp hi), h j (mem_range.mp hj), h _ (Nat.mod_lt _ hn)]

def packedParityCount (L n X : ℕ) : ℕ :=
  let U := X &&& repunit (2 ^ L) n
  (cyclicFold L n (U ^ 2) &&& ((2 ^ L - 1) * U)) % (2 ^ L - 1)

lemma packedParityCount_eq (L n X : ℕ) (hn : 0 < n) (hL : 0 < L)
    (hX : X < (2 ^ L) ^ n) (hB : n ^ 2 < 2 ^ L - 1)
    (hfold : cyclicFold L n ((X &&& repunit (2 ^ L) n) ^ 2) < (2 ^ L) ^ n - 1) :
    packedParityCount L n X = cyclicCount n (fun i => digit L X i % 2) := by
  let u := fun i => digit L X i % 2
  have hu : ∀ i < n, u i ≤ 1 := by intro i _; dsimp [u]; omega
  have hUsize : X &&& repunit (2 ^ L) n < (2 ^ L) ^ n :=
    lt_of_le_of_lt Nat.and_le_left hX
  have hU : X &&& repunit (2 ^ L) n = pack L n u := by
    rw [← pack_digits L n _ hUsize]
    exact pack_congr L n _ _ (fun i hi => parityWord_digits L n X i hL hi)
  unfold packedParityCount
  dsimp only
  rw [hU]
  rw [hU] at hfold
  rw [cyclicFold_square_eq_pack L n hn hL u hu hB hfold,
    maskedPack_eq L n hL u (cyclicCoeff n u) hu (by
      intro i hi
      have hc := cyclicCoeff_le n i u hu
      omega), pack_mod_pred L n hL]
  rw [sum_weight_cyclicCoeff n hn u u]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (cyclicCount_le n hn u hu) hB)

lemma two_mul_S_eq_packedParityCount (p g L X Q : ℕ) (hp : p.Prime) (hop : Odd p)
    (H : LimbOrbit p g L (p - 1) X Q)
    (hr : IsPrimitiveRoot (g : ZMod p) (p - 1))
    (hB : (p - 1) ^ 2 < 2 ^ L - 1)
    (hfold : cyclicFold L (p - 1) ((X &&& repunit (2 ^ L) (p - 1)) ^ 2) <
      (2 ^ L) ^ (p - 1) - 1) :
    2 * Arxiv.«2501.03234».S p =
      8 * (packedParityCount L (p - 1) X : ℤ) - (p - 1 : ℕ) ^ 2 := by
  rw [packedParityCount_eq L (p - 1) X H.length_pos H.width_pos H.size_bound hB hfold,
    two_mul_S_eq_cyclicCount p g hp hop hr]
  have hc : cyclicCount (p - 1) (fun i => orbitValue p g i % 2) =
      cyclicCount (p - 1) (fun i => digit L X i % 2) := by
    apply cyclicCount_congr (p - 1) H.length_pos
    intro i hi
    rw [H.orbit_eq i hi, orbitValue_eq_mod]
  rw [hc]


def powTwo (n : ℕ) : ℕ := (1 : ℕ) <<< n

lemma powTwo_eq (n : ℕ) : powTwo n = 2 ^ n := by
  simp [powTwo, Nat.shiftLeft_eq]

lemma pow_div_base (B n : ℕ) (hB : 0 < B) (hn : 0 < n) :
    B ^ n / B = B ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ n => simp [pow_succ, hB]

def validatePacked (p g L h X : ℕ) : Bool :=
  let n := p - 1
  let B := powTwo L
  let BN := powTwo (L * n)
  let R := (BN - 1) / (B - 1)
  let c := powTwo h - 1
  let M := c * R
  let Y := X / B + BN / B
  let Q := (g * X - Y) / p
  let U := X &&& R
  let square := U * U
  let V := (square &&& (BN - 1)) + (square >>> (L * n))
  let C := (V &&& ((B - 1) * U)) % (B - 1)
  decide (1 < p) && decide (0 < g) && decide (p * g < B) && decide (2 * c < B) &&
  decide (n ^ 2 < B - 1) && rootCheck p g n &&
  decide (X ≤ (p - 1) * R) && decide ((X &&& M) = X) &&
  decide ((((p - 1) * R - X) &&& M) = (p - 1) * R - X) &&
  decide (X % B = 1) && decide (g * X = Y + p * Q) &&
  decide (Q ≤ (g - 1) * R) && decide ((Q &&& M) = Q) &&
  decide ((((g - 1) * R - Q) &&& M) = (g - 1) * R - Q) &&
  decide (V < BN - 1) && decide (n ^ 2 < 8 * C)

lemma validatePacked_sound (p g L h X : ℕ) (hp : p.Prime) (hop : Odd p)
    (hc : validatePacked p g L h X = true) :
    0 < Arxiv.«2501.03234».S p := by
  unfold validatePacked at hc
  dsimp only at hc
  simp only [powTwo_eq, pow_mul, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hc
  rcases hc with ⟨hnum, hg, hword, hclean, hB, hr, hXB, hX, hXC, hfirst, hrec,
    hQB, hQ, hQC, hfold, hcount⟩
  have hpg : p ≤ p * g := Nat.le_mul_of_pos_right p hg
  have hbase : 1 < 2 ^ L := by omega
  have hR := (repunit_eq_div (2 ^ L) (p - 1) hbase).symm
  simp only [hR] at hXB hX hXC hQB hQ hQC hfold hcount
  have hprev := pow_div_base (2 ^ L) (p - 1) (by positivity) (by omega)
  simp only [hprev] at hrec hQB hQ hQC
  have H := LimbOrbit.of_masks p g L (p - 1) (2 ^ h - 1) X
    ((g * X - (X / 2 ^ L + (2 ^ L) ^ (p - 1 - 1))) / p)
    hnum hg (by omega) hword hclean hX hXC hXB hQ hQC hQB hfirst hrec
  have hr' := rootCheck_sound p g (p - 1) (by omega) (by omega) hr
  have hfold' : cyclicFold L (p - 1) ((X &&& repunit (2 ^ L) (p - 1)) ^ 2) <
      (2 ^ L) ^ (p - 1) - 1 := by
    simpa only [cyclicFold, pow_mul, pow_two] using hfold
  have hcount' : (p - 1) ^ 2 < 8 * packedParityCount L (p - 1) X := by
    simpa only [packedParityCount, cyclicFold, pow_mul, pow_two] using hcount
  have hs := two_mul_S_eq_packedParityCount p g L X _ hp hop H hr' hB hfold'
  have hi : ((p - 1) ^ 2 : ℕ) < 8 * packedParityCount L (p - 1) X := hcount'
  have hi' : (((p - 1) ^ 2 : ℕ) : ℤ) <
      8 * (packedParityCount L (p - 1) X : ℤ) := by exact_mod_cast hi
  push_cast at hi'
  nlinarith


structure Packet where
  count : Nat
  ones : Nat
  values : Nat
  nextPower : Nat

def double (p : Nat) (a : Packet) : Packet := Id.run do
  let product := a.values * a.nextPower
  let quot := ((product * ((1 <<< 34)/p)) >>> 34) &&& (131071*a.ones)
  let rest := product - quot*p
  let large := ((rest + (262144-p)*a.ones) >>> 18) &&& a.ones
  let high := rest-large*p
  let length := 64*a.count
  return ⟨2*a.count, a.ones ||| (a.ones <<< length), a.values ||| (high <<< length),
    a.nextPower*a.nextPower % p⟩

def powers (p g : Nat) : Nat → Packet
  | 0 => ⟨1,1,1,g⟩
  | t+1 => double p (powers p g t)

def orbitWord (p g : ℕ) : ℕ :=
  (powers p g (Nat.log2 (p-1) + 1)).values % powTwo (64 * (p-1))

def GoodRange (lo hi : ℕ) : Prop :=
  ∀ p : ℕ, lo ≤ p → p < hi → p.Prime → 0 < Arxiv.«2501.03234».S p

lemma GoodRange.join {lo mid hi : ℕ} (ha : GoodRange lo mid) (hb : GoodRange mid hi) :
    GoodRange lo hi := by
  intro p hlo hhi hp
  by_cases hm : p < mid
  · exact ha p hlo hm hp
  · exact hb p (by omega) hhi hp


def properFactorCheck (p d : ℕ) : Bool :=
  decide (1 < d) && decide (d < p) && decide (p % d = 0)

lemma prime_rejects_properFactor (p d : ℕ) (hp : p.Prime)
    (hc : properFactorCheck p d = true) : False := by
  simp only [properFactorCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hd := Nat.dvd_of_mod_eq_zero hc.2
  have he := (Nat.dvd_prime hp).mp hd
  omega

def recordP (record : ℕ) : ℕ := record &&& (powTwo 17 - 1)

def recordCheck (record : ℕ) : Bool :=
  let p := recordP record
  let g := record >>> 17
  decide (2 < p) && validatePacked p g 64 17 (orbitWord p g)

lemma recordCheck_sound (record : ℕ) (hp : (recordP record).Prime)
    (hc : recordCheck record = true) : 0 < Arxiv.«2501.03234».S (recordP record) := by
  unfold recordCheck at hc
  dsimp only at hc
  rw [Bool.and_eq_true, decide_eq_true_eq] at hc
  have hop : Odd (recordP record) := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))
  exact validatePacked_sound _ _ _ _ _ hp hop hc.2

def covered (records : List ℕ) (p : ℕ) : Bool :=
  records.any (fun record => decide (p = recordP record))

lemma covered_sound (records : List ℕ) (p : ℕ) (hc : covered records p = true) :
    ∃ record ∈ records, p = recordP record := by
  rcases List.any_eq_true.mp hc with ⟨record, hr, he⟩
  exact ⟨record, hr, of_decide_eq_true he⟩

def coverageCheck (records : List ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | len + 1, lo =>
      (covered records lo || properFactorCheck lo lo.minFac) &&
        coverageCheck records len (lo + 1)

lemma coverageCheck_sound (records : List ℕ) (len lo : ℕ)
    (hc : coverageCheck records len lo = true) :
    ∀ p : ℕ, lo ≤ p → p < lo + len → p.Prime → covered records p = true := by
  induction len generalizing lo with
  | zero => intro p hlo hhi; omega
  | succ len ih =>
    simp only [coverageCheck, Bool.and_eq_true, Bool.or_eq_true] at hc
    intro p hlo hhi hp
    by_cases he : p = lo
    · subst p
      rcases hc.1 with hcovered | hfactor
      · exact hcovered
      · exact (prime_rejects_properFactor lo lo.minFac hp hfactor).elim
    · exact ih (lo + 1) hc.2 p (by omega) (by omega) hp

def blockCheck (records : List ℕ) (lo hi : ℕ) : Bool :=
  records.all recordCheck && coverageCheck records (hi - lo) lo

lemma blockCheck_sound (records : List ℕ) {lo hi : ℕ}
    (hc : blockCheck records lo hi = true) : GoodRange lo hi := by
  rw [blockCheck, Bool.and_eq_true] at hc
  intro p hlo hhi hp
  have hcovered := coverageCheck_sound records (hi - lo) lo hc.2 p hlo (by omega) hp
  rcases covered_sound records p hcovered with ⟨record, hr, he⟩
  have hrecord := List.all_eq_true.mp hc.1 record hr
  subst p
  exact recordCheck_sound record hp hrecord


end Packed
end ThetaFiniteRange

/-! Exact finite certificates. Candidate data are untrusted; each interval
checks every integer, and each prime must pass the proved validator. The
certificates use PLift data definitions so their proofs are checked serially,
avoiding accumulation of asynchronous large-integer elaboration tasks. -/
namespace ThetaFiniteRange.Packed

abbrev G := GoodRange

lemma bs (records : List ℕ) {lo hi : ℕ}
    (hc : blockCheck records lo hi = true) : G lo hi := blockCheck_sound records hc

lemma j {lo mid hi : ℕ} (ha : G lo mid) (hb : G mid hi) : G lo hi :=
  GoodRange.join ha hb

set_option maxRecDepth 100000 in
def block0 : PLift (G 3 19) := ⟨bs [0x40003,0x40005,0x60007,0x4000b,0x4000d,0x60011] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1 : PLift (G 19 43) := ⟨bs [0x40013,0xa0017,0x4001d,0x6001f,0x40025,0xc0029] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block2 : PLift (G 43 71) := ⟨bs [0x6002b,0xa002f,0x40035,0x4003b,0x4003d,0x40043] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block3 : PLift (G 71 101) := ⟨bs [0xe0047,0xa0049,0x6004f,0x40053,0x60059,0xa0061] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block4 : PLift (G 101 131) := ⟨bs [0x40065,0xa0067,0x4006b,0xc006d,0x60071,0x6007f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block5 : PLift (G 131 163) := ⟨bs [0x40083,0x60089,0x4008b,0x40095,0xc0097,0xa009d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block6 : PLift (G 163 193) := ⟨bs [0x400a3,0xa00a7,0x400ad,0x400b3,0x400b5,0x2600bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block7 : PLift (G 193 229) := ⟨bs [0xa00c1,0x400c5,0x600c7,0x400d3,0x600df,0x400e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block8 : PLift (G 229 263) := ⟨bs [0xc00e5,0x600e9,0xe00ef,0xe00f1,0xc00fb,0x60101] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block9 : PLift (G 263 293) := ⟨bs [0xa0107,0x4010d,0xc010f,0xa0115,0x60119,0x6011b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block10 : PLift (G 293 337) := ⟨bs [0x40125,0xa0133,0x220137,0x140139,0x4013d,0x6014b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block11 : PLift (G 337 373) := ⟨bs [0x140151,0x4015b,0x4015d,0x60161,0xe0167,0xc016f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block12 : PLift (G 373 409) := ⟨bs [0x40175,0x4017b,0xa017f,0x40185,0xa018d,0x60191] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block13 : PLift (G 409 443) := ⟨bs [0x2a0199,0x401a3,0x401a5,0xe01af,0xa01b1,0x1e01b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block14 : PLift (G 443 479) := ⟨bs [0x401bb,0x601c1,0x1a01c9,0x401cd,0x601cf,0x401d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block15 : PLift (G 479 521) := ⟨bs [0x1a01df,0x601e7,0x401eb,0xe01f3,0xa01f7,0x401fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block16 : PLift (G 521 569) := ⟨bs [0x60209,0x4020b,0x4021d,0x40223,0x4022d,0x40233] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block17 : PLift (G 569 601) := ⟨bs [0x60239,0x6023b,0xa0241,0x4024b,0x60251,0xe0257] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block18 : PLift (G 601 641) := ⟨bs [0xe0259,0x6025f,0x40265,0x60269,0x4026b,0x60277] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block19 : PLift (G 641 673) := ⟨bs [0x60281,0x160283,0xa0287,0x4028d,0x40293,0x40295] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block20 : PLift (G 673 719) := ⟨bs [0xa02a1,0x402a5,0xa02ab,0x602b3,0x402bd,0x402c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block21 : PLift (G 719 757) := ⟨bs [0x1602cf,0xa02d7,0xc02dd,0x602e3,0xa02e7,0x602ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block22 : PLift (G 757 809) := ⟨bs [0x402f5,0xc02f9,0x160301,0x40305,0x40313,0x4031d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block23 : PLift (G 809 839) := ⟨bs [0x60329,0x6032b,0x40335,0x60337,0x4033b,0x4033d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block24 : PLift (G 839 881) := ⟨bs [0x160347,0x40355,0x60359,0x4035b,0xa035f,0x4036d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block25 : PLift (G 881 929) := ⟨bs [0x60371,0x40373,0xa0377,0x4038b,0x22038f,0xe0397] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block26 : PLift (G 929 971) := ⟨bs [0x603a1,0xa03a9,0x403ad,0x403b3,0x603b9,0xa03c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block27 : PLift (G 971 1013) := ⟨bs [0xc03cb,0x603d1,0xa03d7,0xc03df,0xe03e5,0x1603f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block28 : PLift (G 1013 1049) := ⟨bs [0x603f5,0x403fb,0x1403fd,0x1c0407,0xa0409,0x6040f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block29 : PLift (G 1049 1091) := ⟨bs [0x60419,0xe041b,0x40425,0x60427,0xc042d,0x6043f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block30 : PLift (G 1091 1123) := ⟨bs [0x40443,0xa0445,0x60449,0xa044f,0x40455,0x4045d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block31 : PLift (G 1123 1181) := ⟨bs [0x40463,0x160469,0x22047f,0xa0481,0xa048b,0x40493] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block32 : PLift (G 1181 1223) := ⟨bs [0xe049d,0x404a3,0x604a9,0x1604b1,0x404bd,0x604c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block33 : PLift (G 1223 1277) := ⟨bs [0xa04c7,0x404cd,0x604cf,0x404d5,0xe04e1,0x404eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block34 : PLift (G 1277 1301) := ⟨bs [0x404fd,0x604ff,0x40503,0xc0509,0x4050b,0x140511] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block35 : PLift (G 1301 1361) := ⟨bs [0x40515,0xc0517,0x4051b,0x1a0527,0x1a0529,0x6052f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block36 : PLift (G 1361 1423) := ⟨bs [0x60551,0xa0557,0x4055d,0x40565,0x1a0577,0x60581] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block37 : PLift (G 1423 1451) := ⟨bs [0x6058f,0x40593,0xc0595,0x60599,0xe059f,0x605a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block38 : PLift (G 1451 1487) := ⟨bs [0x405ab,0x405ad,0x605b3,0xc05bf,0x605c9,0x405cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block39 : PLift (G 1487 1531) := ⟨bs [0xa05cf,0x1c05d1,0x405d5,0x405db,0x1605e7,0x405f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block40 : PLift (G 1531 1571) := ⟨bs [0x405fb,0xa0607,0x4060d,0x60611,0x260617,0x6061f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block41 : PLift (G 1571 1609) := ⟨bs [0x40623,0x6062b,0xa062f,0x16063d,0x60641,0xa0647] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block42 : PLift (G 1609 1657) := ⟨bs [0xe0649,0x6064d,0x40653,0x40655,0x6065b,0x40665] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block43 : PLift (G 1657 1699) := ⟨bs [0x160679,0x6067f,0x40683,0x40685,0x4069d,0x606a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block44 : PLift (G 1699 1747) := ⟨bs [0x606a3,0x606ad,0x606b9,0x606bb,0x406c5,0x406cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block45 : PLift (G 1747 1789) := ⟨bs [0x406d3,0xe06d9,0xc06df,0xa06f1,0x1406f7,0x406fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block46 : PLift (G 1789 1861) := ⟨bs [0xc06fd,0x160709,0xc0713,0xa071f,0x60727,0xa0737] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block47 : PLift (G 1861 1889) := ⟨bs [0x40745,0x4074b,0x1c074f,0x140751,0x40755,0xc0757] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block48 : PLift (G 1889 1949) := ⟨bs [0x60761,0x4076d,0x40773,0x60779,0x4078b,0xa078d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block49 : PLift (G 1949 1997) := ⟨bs [0x4079d,0x6079f,0x407b5,0x407bb,0x407c3,0xa07c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block50 : PLift (G 1997 2029) := ⟨bs [0x407cd,0x607cf,0xa07d3,0x607db,0xa07e1,0x407eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block51 : PLift (G 2029 2083) := ⟨bs [0x407ed,0xe07f7,0x40805,0xa080f,0x40815,0x60821] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block52 : PLift (G 2083 2129) := ⟨bs [0x40823,0xa0827,0xe0829,0x40833,0xe083f,0xa0841] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block53 : PLift (G 2129 2161) := ⟨bs [0x60851,0x40853,0x140859,0x4085d,0x6085f,0x60869] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block54 : PLift (G 2161 2237) := ⟨bs [0x2e0871,0xe0883,0xa089b,0xa089f,0x408a5,0x408ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block55 : PLift (G 2237 2273) := ⟨bs [0x408bd,0x608bf,0x408c3,0xe08cb,0x408db,0x408dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block56 : PLift (G 2273 2311) := ⟨bs [0x608e1,0xe08e9,0x2608ef,0x408f5,0xa08f9,0x40905] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block57 : PLift (G 2311 2357) := ⟨bs [0x60907,0x4091d,0x40923,0xe0925,0x6092b,0x1a092f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block58 : PLift (G 2357 2393) := ⟨bs [0x40935,0x40943,0xa0949,0x6094d,0xa094f,0x40955] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block59 : PLift (G 2393 2441) := ⟨bs [0x60959,0x16095f,0xc096b,0x60971,0xa0977,0x40985] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block60 : PLift (G 2441 2503) := ⟨bs [0xc0989,0xa098f,0x4099b,0x409a3,0xa09a9,0x409ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block61 : PLift (G 2503 2551) := ⟨bs [0x609c7,0x2209d9,0x409e3,0x409eb,0xa09ef,0x409f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block62 : PLift (G 2551 2617) := ⟨bs [0xc09f7,0x409fd,0x40a13,0xe0a1f,0xe0a21,0x60a31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block63 : PLift (G 2617 2663) := ⟨bs [0xa0a39,0x40a3d,0x60a49,0x60a57,0x60a61,0x40a63] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block64 : PLift (G 2663 2693) := ⟨bs [0xa0a67,0xe0a6f,0x40a75,0x40a7b,0xa0a7f,0x260a81] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block65 : PLift (G 2693 2729) := ⟨bs [0x40a85,0x40a8b,0x40a93,0xe0a97,0xa0a99,0x60a9f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block66 : PLift (G 2729 2777) := ⟨bs [0x60aa9,0x60aab,0x40ab5,0xc0abd,0x60ac1,0x60acf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block67 : PLift (G 2777 2819) := ⟨bs [0x60ad9,0x40ae5,0xc0ae7,0x40aed,0x60af1,0x40af3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block68 : PLift (G 2819 2861) := ⟨bs [0x40b03,0xa0b11,0x40b15,0x40b1b,0x40b23,0x160b29] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block69 : PLift (G 2861 2917) := ⟨bs [0x40b2d,0xe0b3f,0xa0b47,0x60b51,0xa0b57,0x40b5d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block70 : PLift (G 2917 2969) := ⟨bs [0xa0b65,0xa0b6f,0x40b7b,0x1a0b89,0x40b8d,0x40b93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block71 : PLift (G 2969 3023) := ⟨bs [0x60b99,0x140b9b,0x220bb7,0x1c0bb9,0x40bc3,0x40bcb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block72 : PLift (G 3023 3079) := ⟨bs [0xa0bcf,0x40bdd,0x60be1,0x160be9,0xc0bf5,0x40bfb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block73 : PLift (G 3079 3137) := ⟨bs [0xc0c07,0x40c0b,0x60c11,0xc0c25,0xe0c2f,0xe0c31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block74 : PLift (G 3137 3191) := ⟨bs [0x60c41,0x60c5b,0xa0c5f,0xe0c61,0xe0c6d,0x40c73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block75 : PLift (G 3191 3251) := ⟨bs [0x160c77,0x40c83,0x60c89,0xa0c91,0x140c95,0xc0c9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block76 : PLift (G 3251 3301) := ⟨bs [0xc0cb3,0x40cb5,0x60cb9,0x60cbb,0x60cc7,0x40ce3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block77 : PLift (G 3301 3331) := ⟨bs [0xc0ce5,0x40ceb,0x140cf1,0xc0cf7,0x40cfb,0x60d01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block78 : PLift (G 3331 3373) := ⟨bs [0x60d03,0xa0d0f,0x40d13,0x160d1f,0x2c0d21,0x40d2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block79 : PLift (G 3373 3449) := ⟨bs [0xa0d2d,0x60d3d,0x60d3f,0xa0d4f,0x40d55,0xa0d69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block80 : PLift (G 3449 3491) := ⟨bs [0x60d79,0xe0d81,0x40d85,0x60d87,0x40d8b,0x40d8d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block81 : PLift (G 3491 3533) := ⟨bs [0x40da3,0x40dab,0xe0db7,0x40dbd,0xa0dc7,0x220dc9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block82 : PLift (G 3533 3571) := ⟨bs [0x40dcd,0x40dd3,0xe0dd5,0x40ddb,0x40de5,0x60de7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block83 : PLift (G 3571 3617) := ⟨bs [0x40df3,0x40dfd,0x60dff,0x60e09,0xa0e17,0x40e1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block84 : PLift (G 3617 3671) := ⟨bs [0x60e21,0xa0e27,0x1e0e2f,0x40e35,0x40e3b,0x40e4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block85 : PLift (G 3671 3709) := ⟨bs [0x1a0e57,0xa0e59,0x40e5d,0x40e6b,0xa0e71,0x40e75] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block86 : PLift (G 3709 3767) := ⟨bs [0x40e7d,0xe0e87,0x60e8f,0x40e95,0xe0e9b,0x60eb1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block87 : PLift (G 3767 3821) := ⟨bs [0xa0eb7,0xe0eb9,0x40ec3,0xa0ed1,0x40ed5,0x40edb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block88 : PLift (G 3821 3863) := ⟨bs [0x60eed,0x60eef,0x60ef9,0xa0f07,0x40f0b,0x40f0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block89 : PLift (G 3863 3917) := ⟨bs [0xa0f17,0x40f25,0x1a0f29,0x160f31,0x40f43,0x1a0f47] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block90 : PLift (G 3917 3947) := ⟨bs [0x40f4d,0x60f4f,0x40f53,0x60f59,0x40f5b,0x60f67] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block91 : PLift (G 3947 4013) := ⟨bs [0x40f6b,0xc0f7f,0x40f95,0x60fa1,0x40fa3,0xa0fa7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block92 : PLift (G 4013 4057) := ⟨bs [0x40fad,0x40fb3,0x40fb5,0x60fbb,0x60fd1,0x140fd3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block93 : PLift (G 4057 4111) := ⟨bs [0xa0fd9,0x60fe9,0x160fef,0x40ffb,0x40ffd,0x41003] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block94 : PLift (G 4111 4157) := ⟨bs [0x18100f,0xa101f,0x1a1021,0x41025,0x4102b,0xa1039] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block95 : PLift (G 4157 4219) := ⟨bs [0x4103d,0x6103f,0xa1051,0x161069,0xc1073,0x61079] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block96 : PLift (G 4219 4259) := ⟨bs [0x4107b,0x41085,0x61087,0x61091,0x41093,0x4109d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block97 : PLift (G 4259 4297) := ⟨bs [0x410a3,0x410a5,0xe10af,0xa10b1,0x410bb,0x610c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block98 : PLift (G 4297 4363) := ⟨bs [0xa10c9,0x610e7,0x610f1,0x1410f3,0x410fd,0x41105] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block99 : PLift (G 4363 4423) := ⟨bs [0x4110b,0x41115,0x1c1127,0x4112d,0x61139,0x61145] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block100 : PLift (G 4423 4481) := ⟨bs [0x61147,0x2a1159,0x6115f,0x41163,0x61169,0xa116f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block101 : PLift (G 4481 4519) := ⟨bs [0x61181,0x41183,0x4118d,0x4119b,0xe11a1,0x411a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block102 : PLift (G 4519 4583) := ⟨bs [0x611a7,0xa11ab,0x411c3,0xc11c5,0x1611d1,0x611d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block103 : PLift (G 4583 4639) := ⟨bs [0xa11e7,0x1611ef,0xa11f5,0x411fb,0x4120d,0x4121d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block104 : PLift (G 4639 4673) := ⟨bs [0x6121f,0xa1223,0x61229,0x6122b,0x1e1231,0x61237] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block105 : PLift (G 4673 4729) := ⟨bs [0x61241,0x161247,0x41253,0xa125f,0xc1271,0x41273] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block106 : PLift (G 4729 4789) := ⟨bs [0x221279,0xa127d,0x26128f,0x61297,0xc12af,0x412b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block107 : PLift (G 4789 4831) := ⟨bs [0x412b5,0x612b9,0xe12bf,0xe12c1,0x412cd,0x612d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block108 : PLift (G 4831 4909) := ⟨bs [0x612df,0x1612fd,0x161307,0x4130d,0x61319,0x61327] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block109 : PLift (G 4909 4951) := ⟨bs [0xc132d,0x1a1337,0xc1343,0x41345,0x61349,0xe134f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block110 : PLift (G 4951 4993) := ⟨bs [0xc1357,0x4135d,0xa1367,0x161369,0x4136d,0x4137b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block111 : PLift (G 4993 5023) := ⟨bs [0xa1381,0x61387,0x4138b,0x61391,0x41393,0x6139d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block112 : PLift (G 5023 5087) := ⟨bs [0x6139f,0x1613af,0x413bb,0x413c3,0x413d5,0x613d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block113 : PLift (G 5087 5147) := ⟨bs [0xa13df,0x413eb,0xc13ed,0x413f3,0x2613f9,0x613ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block114 : PLift (G 5147 5197) := ⟨bs [0x4141b,0xa1421,0xc142f,0x41433,0x4143b,0x41445] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block115 : PLift (G 5197 5261) := ⟨bs [0xe144d,0x221459,0x4146b,0xe146f,0x141471,0x61475] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block116 : PLift (G 5261 5309) := ⟨bs [0x4148d,0x61499,0xe149f,0xe14a1,0x614b1,0xa14b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block117 : PLift (G 5309 5387) := ⟨bs [0x414bd,0xa14cb,0x414d5,0x614e3,0x1614e7,0x61505] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block118 : PLift (G 5387 5419) := ⟨bs [0x4150b,0x61511,0xe1517,0x6151f,0xa1525,0x61529] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block119 : PLift (G 5419 5471) := ⟨bs [0x6152b,0x61537,0xa153d,0x61541,0x41543,0xe1549] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block120 : PLift (G 5471 5507) := ⟨bs [0xe155f,0x41565,0x61567,0x4156b,0x4157d,0x6157f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block121 : PLift (G 5507 5563) := ⟨bs [0x41583,0x1a158f,0x161591,0xa1597,0x14159b,0x415b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block122 : PLift (G 5563 5639) := ⟨bs [0x415bb,0x1a15c1,0x415c5,0xc15cd,0x1615d7,0xa15f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block123 : PLift (G 5639 5659) := ⟨bs [0xe1607,0x1c1609,0x6160f,0x41613,0xa1615,0x61619] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block124 : PLift (G 5659 5711) := ⟨bs [0x4161b,0x61625,0x41633,0x161639,0x4163d,0x41645] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block125 : PLift (G 5711 5779) := ⟨bs [0x26164f,0x41655,0xa1669,0x4166d,0x14166f,0x41675] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block126 : PLift (G 5779 5821) := ⟨bs [0x41693,0xe1697,0xc169f,0x616a9,0xa16af,0x416b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block127 : PLift (G 5821 5857) := ⟨bs [0xc16bd,0x416c3,0xc16cf,0x416d3,0x616d9,0x416db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block128 : PLift (G 5857 5897) := ⟨bs [0xe16e1,0x616e5,0xa16eb,0x416ed,0x1616f7,0x3e16f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block129 : PLift (G 5897 5981) := ⟨bs [0x61709,0xa170f,0x41723,0xa1727,0x41733,0xe1741] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block130 : PLift (G 5981 6043) := ⟨bs [0x6175d,0x41763,0x61777,0x4177b,0x4178d,0xa1795] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block131 : PLift (G 6043 6089) := ⟨bs [0xa179b,0xa179f,0x417a5,0x417b3,0x1417b9,0x2217bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block132 : PLift (G 6089 6133) := ⟨bs [0x617c9,0xe17cb,0x417d5,0x617e1,0xe17e9,0x417f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block133 : PLift (G 6133 6199) := ⟨bs [0xa17f5,0xa17ff,0x61807,0x61813,0x4181d,0x41835] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block134 : PLift (G 6199 6247) := ⟨bs [0x61837,0x4183b,0x41843,0xa1849,0x6184d,0x41855] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block135 : PLift (G 6247 6287) := ⟨bs [0xa1867,0x61871,0xa1877,0x4187d,0x16187f,0x41885] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block136 : PLift (G 6287 6329) := ⟨bs [0xe188f,0x4189b,0x14189d,0xe18a7,0x418ad,0x418b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block137 : PLift (G 6329 6367) := ⟨bs [0x618b9,0x1418c1,0x618c7,0x618d1,0x1a18d7,0x2618d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block138 : PLift (G 6367 6427) := ⟨bs [0x618df,0x418e5,0x418eb,0x418f5,0x418fd,0xc1915] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block139 : PLift (G 6427 6491) := ⟨bs [0x6191b,0x61931,0x61933,0x41945,0x61949,0xe1951] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block140 : PLift (G 6491 6563) := ⟨bs [0x4195b,0xc1979,0xe1981,0x41993,0x221997,0x141999] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block141 : PLift (G 6563 6607) := ⟨bs [0xa19a3,0x619a9,0x619ab,0xa19b1,0x1c19b5,0x1a19c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block142 : PLift (G 6607 6673) := ⟨bs [0x619cf,0x419db,0x419ed,0x419fd,0x41a03,0xc1a05] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block143 : PLift (G 6673 6709) := ⟨bs [0xa1a11,0xe1a17,0x61a21,0x41a23,0x41a2d,0xa1a2f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block144 : PLift (G 6709 6779) := ⟨bs [0x41a35,0x161a3f,0x41a4d,0x61a51,0x61a69,0x41a6b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block145 : PLift (G 6779 6827) := ⟨bs [0x41a7b,0x41a7d,0xe1a87,0x141a89,0x41a93,0x61aa7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block146 : PLift (G 6827 6869) := ⟨bs [0x41aab,0x41aad,0x61ab1,0x2c1ab9,0x61ac9,0xa1acf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block147 : PLift (G 6869 6917) := ⟨bs [0x41ad5,0x61ad7,0x41ae3,0x41af3,0x41afb,0xe1aff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block148 : PLift (G 6917 6971) := ⟨bs [0x41b05,0x41b23,0x41b25,0xe1b2f,0x1a1b31,0xa1b37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block149 : PLift (G 6971 7013) := ⟨bs [0x41b3b,0x61b41,0xa1b47,0xc1b4f,0xa1b55,0x61b59] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block150 : PLift (G 7013 7069) := ⟨bs [0x41b65,0x41b6b,0x41b73,0x61b7f,0x41b83,0xa1b91] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block151 : PLift (G 7069 7129) := ⟨bs [0x41b9d,0xe1ba7,0xa1bbf,0x41bc5,0x61bd1,0xa1bd7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block152 : PLift (G 7129 7207) := ⟨bs [0xe1bd9,0xe1bef,0x61bf7,0x141c09,0x41c13,0x61c19] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block153 : PLift (G 7207 7243) := ⟨bs [0x61c27,0x41c2b,0xa1c2d,0x41c33,0x41c3d,0x41c45] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block154 : PLift (G 7243 7309) := ⟨bs [0x41c4b,0xa1c4f,0x41c55,0x41c73,0xa1c81,0x41c8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block155 : PLift (G 7309 7369) := ⟨bs [0xc1c8d,0xe1c99,0x41ca3,0xc1ca5,0x41cb5,0xc1cb7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block156 : PLift (G 7369 7457) := ⟨bs [0xe1cc9,0xa1ce1,0x41cf3,0xa1cf9,0x61d09,0x41d1b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block157 : PLift (G 7457 7499) := ⟨bs [0x61d21,0x41d23,0x41d35,0xc1d39,0xa1d3f,0xe1d41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block158 : PLift (G 7499 7541) := ⟨bs [0x41d4b,0x41d53,0x41d5d,0x41d63,0x61d69,0xe1d71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block159 : PLift (G 7541 7577) := ⟨bs [0x41d75,0x41d7b,0x41d7d,0x1a1d87,0x1a1d89,0x41d95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block160 : PLift (G 7577 7621) := ⟨bs [0x61d99,0xa1d9f,0x41da5,0xc1da7,0x41db3,0xa1db7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block161 : PLift (G 7621 7681) := ⟨bs [0x41dc5,0xe1dd7,0x41ddb,0x61de1,0x41df5,0x61df9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block162 : PLift (G 7681 7723) := ⟨bs [0x221e01,0xc1e07,0x41e0b,0x61e13,0xa1e17,0x41e25] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block163 : PLift (G 7723 7789) := ⟨bs [0x61e2b,0xa1e2f,0xe1e3d,0x141e49,0x41e4d,0x61e4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block164 : PLift (G 7789 7853) := ⟨bs [0x41e6d,0x61e71,0x61e89,0xa1e8f,0x41e95,0x181ea1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block165 : PLift (G 7853 7901) := ⟨bs [0x41ead,0x61ebb,0xa1ec1,0x41ec5,0x61ec7,0x41ecb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block166 : PLift (G 7901 7949) := ⟨bs [0x41edd,0x41ee3,0xe1eef,0x61ef7,0x41efd,0x61f01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block167 : PLift (G 7949 8017) := ⟨bs [0x41f0d,0xc1f0f,0xa1f1b,0xa1f39,0x61f49,0x1c1f4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block168 : PLift (G 8017 8087) := ⟨bs [0xa1f51,0x161f67,0x41f75,0x61f7b,0x41f85,0x61f91] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block169 : PLift (G 8087 8123) := ⟨bs [0xa1f97,0x221f99,0x41f9d,0xc1fa5,0x161faf,0x41fb5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block170 : PLift (G 8123 8191) := ⟨bs [0x41fbb,0x41fd3,0xe1fe1,0x61fe7,0x41feb,0x41ff3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block171 : PLift (G 8191 8237) := ⟨bs [0x221fff,0xe2011,0x4201b,0x4201d,0x162027,0x142029] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block172 : PLift (G 8237 8291) := ⟨bs [0x4202d,0x42033,0x62047,0x4204d,0x62051,0x6205f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block173 : PLift (G 8291 8353) := ⟨bs [0x42063,0x42065,0x62069,0x62077,0xc207d,0xe2089] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block174 : PLift (G 8353 8419) := ⟨bs [0xa20a1,0x420ab,0x620b1,0xa20b9,0x420c3,0xc20c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block175 : PLift (G 8419 8461) := ⟨bs [0x620e3,0xa20e7,0x420ed,0x620ef,0x420fb,0xa20ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block176 : PLift (G 8461 8537) := ⟨bs [0xc210d,0x42113,0xe2135,0xa2141,0x1a2149,0xa214f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block177 : PLift (G 8537 8597) := ⟨bs [0x62159,0x4215b,0xa215f,0x42173,0x4217d,0xc2185] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block178 : PLift (G 8597 8641) := ⟨bs [0x42195,0x62197,0x621a1,0x621af,0x421b3,0xc21b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block179 : PLift (G 8641 8689) := ⟨bs [0x2221c1,0x621c7,0xa21d7,0x421dd,0x421e5,0x1e21e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block180 : PLift (G 8689 8731) := ⟨bs [0x1a21f1,0x421f5,0x421fb,0xa2203,0xa2209,0x6220f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block181 : PLift (G 8731 8779) := ⟨bs [0x4221b,0xa2221,0x42225,0x4222b,0x62231,0x2e2239] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block182 : PLift (G 8779 8831) := ⟨bs [0x16224b,0xa224f,0x42263,0xa2267,0x42273,0x42275] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block183 : PLift (G 8831 8867) := ⟨bs [0xe227f,0x42285,0x62287,0x62291,0x4229d,0x6229f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block184 : PLift (G 8867 8941) := ⟨bs [0x422a3,0x622b7,0xa22bd,0x422db,0x1622e1,0x422e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block185 : PLift (G 8941 9001) := ⟨bs [0xc22ed,0x1a22f7,0x42303,0x62309,0x4230b,0xe2327] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block186 : PLift (G 9001 9043) := ⟨bs [0xe2329,0x6232f,0x42333,0xa2335,0x42345,0x62351] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block187 : PLift (G 9043 9109) := ⟨bs [0x62353,0xe2359,0x42363,0x6236b,0x62383,0xc238f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block188 : PLift (G 9109 9161) := ⟨bs [0x142395,0x623a7,0xc23ad,0x623b1,0x623bf,0xc23c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block189 : PLift (G 9161 9209) := ⟨bs [0x623c9,0x423d5,0x423dd,0x623e3,0x623ef,0x423f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block190 : PLift (G 9209 9277) := ⟨bs [0x623f9,0x42405,0x4240b,0x262417,0x1a2419,0x62429] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block191 : PLift (G 9277 9323) := ⟨bs [0xa243d,0x62441,0x42443,0x4244d,0xe245f,0x62467] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block192 : PLift (G 9323 9377) := ⟨bs [0x4246b,0xa2479,0x4247d,0xa247f,0x42485,0x4249b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block193 : PLift (G 9377 9421) := ⟨bs [0x624a1,0x624af,0x424b5,0x624bb,0x624c5,0x424cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block194 : PLift (G 9421 9463) := ⟨bs [0x424cd,0xe24d7,0xa24d9,0x424dd,0x2c24df,0x624f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block195 : PLift (G 9463 9511) := ⟨bs [0x624f7,0x424fb,0x62501,0xe2507,0x42513,0x62519] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block196 : PLift (G 9511 9587) := ⟨bs [0x62527,0x62531,0x4253d,0x42543,0x4254b,0x16254f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block197 : PLift (G 9587 9631) := ⟨bs [0x42573,0x1a2581,0x4258d,0x42593,0xa2597,0x4259d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block198 : PLift (G 9631 9689) := ⟨bs [0x6259f,0x425ab,0xe25b1,0x425bd,0x425cd,0x625cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block199 : PLift (G 9689 9743) := ⟨bs [0x625d9,0x1425e1,0x2225f7,0xe25f9,0x42605,0x6260b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block200 : PLift (G 9743 9791) := ⟨bs [0xa260f,0x42615,0xa2627,0x1a2629,0xc2635,0x6263b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block201 : PLift (G 9791 9839) := ⟨bs [0x16263f,0x4264b,0x62653,0xa2659,0x142665,0x62669] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block202 : PLift (G 9839 9887) := ⟨bs [0xe266f,0x4267b,0xa2681,0x42683,0x6268f,0x4269b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block203 : PLift (G 9887 9941) := ⟨bs [0xa269f,0x426ad,0x426b3,0x426c3,0x626c9,0x1426cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block204 : PLift (G 9941 10037) := ⟨bs [0x426d5,0x426dd,0x626ef,0x1626f5,0xa2717,0x162719] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block205 : PLift (G 10037 10091) := ⟨bs [0x42735,0x62737,0x6274d,0x42753,0x42755,0x16275f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block206 : PLift (G 10091 10139) := ⟨bs [0x4276b,0x4276d,0x42773,0xa2777,0x18277f,0x42795] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block207 : PLift (G 10139 10177) := ⟨bs [0x4279b,0x4279d,0xe27a7,0x627af,0x427b3,0x627b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block208 : PLift (G 10177 10247) := ⟨bs [0xe27c1,0x427c5,0x627d1,0xc27e3,0xa27ef,0xe2803] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block209 : PLift (G 10247 10289) := ⟨bs [0xa2807,0x4280d,0x42813,0x4281b,0xe281f,0x142821] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block210 : PLift (G 10289 10333) := ⟨bs [0x62831,0x4283d,0x6283f,0x62849,0xe2851,0x4285b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block211 : PLift (G 10333 10399) := ⟨bs [0xa285d,0x62861,0xa2867,0x42875,0x1a2881,0x262897] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block212 : PLift (G 10399 10459) := ⟨bs [0xc289f,0x428bb,0xe28bd,0x628c1,0xa28d5,0x628d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block213 : PLift (G 10459 10513) := ⟨bs [0x428db,0xa28df,0x428ed,0xa28f7,0x42903,0x42905] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block214 : PLift (G 10513 10597) := ⟨bs [0xe2911,0x62921,0x62923,0x2e293f,0xc2947,0x4295d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block215 : PLift (G 10597 10639) := ⟨bs [0xa2965,0x62969,0xa296f,0x42975,0xa2983,0x162987] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block216 : PLift (G 10639 10691) := ⟨bs [0xc298f,0xe299b,0xe29a1,0x629a7,0x429ab,0xa29bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block217 : PLift (G 10691 10739) := ⟨bs [0x429c3,0x429d5,0x629d7,0x429e3,0xe29e9,0x429ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block218 : PLift (G 10739 10831) := ⟨bs [0xc29f3,0x162a01,0x62a13,0x142a1d,0x42a25,0x262a2f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block219 : PLift (G 10831 10867) := ⟨bs [0xe2a4f,0x42a55,0xa2a5f,0x42a65,0x42a6b,0x42a6d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block220 : PLift (G 10867 10937) := ⟨bs [0x42a73,0x42a83,0x62a89,0x42a8b,0x62a97,0x42a9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block221 : PLift (G 10937 10987) := ⟨bs [0x62ab9,0x62abb,0x42ac5,0xa2acd,0x42add,0x42ae3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block222 : PLift (G 10987 11059) := ⟨bs [0x42aeb,0xe2af1,0x42afb,0x42b13,0x62b27,0x62b31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block223 : PLift (G 11059 11113) := ⟨bs [0x142b33,0x42b3d,0x62b3f,0x42b4b,0xa2b4f,0x42b55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block224 : PLift (G 11113 11161) := ⟨bs [0x1a2b69,0x62b6d,0x62b6f,0x42b7b,0x142b8d,0xe2b97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block225 : PLift (G 11161 11239) := ⟨bs [0xe2b99,0x42ba3,0xa2ba5,0x62ba9,0x42bbd,0x42bcd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block226 : PLift (G 11239 11279) := ⟨bs [0x62be7,0xa2beb,0x1a2bf3,0x142bf9,0x42bfd,0x62c09] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block227 : PLift (G 11279 11329) := ⟨bs [0xe2c0f,0x62c17,0x62c23,0x62c2f,0x42c35,0x62c39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block228 : PLift (G 11329 11399) := ⟨bs [0xe2c41,0xe2c57,0xe2c59,0x62c69,0xa2c77,0x62c81] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block229 : PLift (G 11399 11467) := ⟨bs [0x162c87,0xe2c93,0xa2c9f,0x42cad,0x42cb3,0xa2cb7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block230 : PLift (G 11467 11503) := ⟨bs [0xa2ccb,0x162ccf,0x42cdb,0x62ce1,0x62ce3,0xe2ce9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block231 : PLift (G 11503 11587) := ⟨bs [0x62cef,0xe2cff,0xa2d07,0x42d1d,0xe2d1f,0x42d3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block232 : PLift (G 11587 11657) := ⟨bs [0x42d43,0xa2d49,0x62d4d,0x142d61,0x42d65,0x62d71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block233 : PLift (G 11657 11717) := ⟨bs [0x62d89,0x42d9d,0x62da1,0xe2da9,0x42db3,0xc2db5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block234 : PLift (G 11717 11783) := ⟨bs [0x42dc5,0xc2dc7,0x62dd3,0x62ddf,0x62e01,0x42e03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block235 : PLift (G 11783 11827) := ⟨bs [0xa2e07,0x42e0d,0x62e19,0xa2e1f,0x42e25,0x42e2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block236 : PLift (G 11827 11887) := ⟨bs [0x42e33,0xe2e37,0xa2e39,0x62e3f,0x62e57,0x42e5b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block237 : PLift (G 11887 11933) := ⟨bs [0x62e6f,0x62e79,0xa2e7f,0x42e85,0xa2e93,0xa2e97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block238 : PLift (G 11933 11971) := ⟨bs [0x42e9d,0x42ea3,0x142ea5,0xa2eb1,0x62eb7,0x62ec1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block239 : PLift (G 11971 12041) := ⟨bs [0x142ec3,0x42ecd,0x42ed3,0x1a2ee7,0x42eeb,0xa2f05] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block240 : PLift (G 12041 12101) := ⟨bs [0x62f09,0x42f0b,0x1a2f11,0x162f27,0xe2f29,0xa2f41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block241 : PLift (G 12101 12149) := ⟨bs [0x62f45,0x42f4b,0xc2f4d,0x62f51,0xe2f57,0x142f6f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block242 : PLift (G 12149 12211) := ⟨bs [0x42f75,0x42f7d,0x62f81,0xa2f83,0x42fa5,0x42fab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block243 : PLift (G 12211 12263) := ⟨bs [0x42fb3,0x42fc3,0x1a2fcf,0xe2fd1,0x42fdb,0x42fdd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block244 : PLift (G 12263 12323) := ⟨bs [0xa2fe7,0x42fed,0x42ff5,0x62ff9,0x163001,0x4300d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block245 : PLift (G 12323 12379) := ⟨bs [0x43023,0x63029,0xe3037,0x4303b,0x43055,0xc3059] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block246 : PLift (G 12379 12433) := ⟨bs [0x4305b,0x343067,0x63071,0xe3079,0x4307d,0xe3085] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block247 : PLift (G 12433 12487) := ⟨bs [0x1a3091,0x43095,0x630a3,0x1430a9,0x630b9,0x2e30bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block248 : PLift (G 12487 12527) := ⟨bs [0x630c7,0x430cb,0x630d1,0xa30d7,0x630df,0xc30e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block249 : PLift (G 12527 12577) := ⟨bs [0xa30ef,0x430fb,0x1c30fd,0x43103,0xa3109,0x63119] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block250 : PLift (G 12577 12619) := ⟨bs [0x143121,0xa3127,0x4312d,0x163139,0x43143,0x43145] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block251 : PLift (G 12619 12671) := ⟨bs [0x4314b,0x4315d,0x63161,0xa3167,0x4316d,0x43173] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block252 : PLift (G 12671 12739) := ⟨bs [0x1c317f,0x63191,0xe3199,0x6319f,0x631a9,0x1a31b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block253 : PLift (G 12739 12799) := ⟨bs [0x431c3,0xa31c7,0x431d5,0x431db,0x431ed,0xe31f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block254 : PLift (G 12799 12853) := ⟨bs [0x1a31ff,0x63209,0x43215,0x63217,0x4321d,0x2a3229] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block255 : PLift (G 12853 12917) := ⟨bs [0xa3235,0x1a3259,0x6325d,0x43263,0x4326b,0x2e326f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block256 : PLift (G 12917 12967) := ⟨bs [0x43275,0xc3277,0x4327b,0x4328d,0x63299,0xe329f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block257 : PLift (G 12967 13007) := ⟨bs [0x632a7,0x1c32ad,0x432b3,0xa32b7,0x632c9,0xa32cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block258 : PLift (G 13007 13063) := ⟨bs [0xa32cf,0xe32d1,0xa32e9,0x432ed,0x432f3,0x632f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block259 : PLift (G 13063 13127) := ⟨bs [0xa3307,0xc3325,0x6332b,0xa332f,0x43335,0xe3341] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block260 : PLift (G 13127 13177) := ⟨bs [0xa3347,0x4335b,0x1a335f,0x63367,0x4336b,0x163373] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block261 : PLift (G 13177 13241) := ⟨bs [0xa3379,0x6337f,0x43383,0x633a1,0x633a3,0x433ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block262 : PLift (G 13241 13309) := ⟨bs [0x633b9,0xe33c1,0xc33cb,0x633d3,0x433eb,0xa33f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block263 : PLift (G 13309 13367) := ⟨bs [0xc33fd,0x63401,0x6340f,0x43413,0x63419,0x4341b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block264 : PLift (G 13367 13421) := ⟨bs [0xa3437,0x143445,0x43455,0x63457,0x43463,0xa3469] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block265 : PLift (G 13421 13477) := ⟨bs [0x14346d,0x163481,0x4348b,0x63491,0xa3497,0x4349d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block266 : PLift (G 13477 13553) := ⟨bs [0x434a5,0xa34af,0xc34bb,0xa34c9,0x434d3,0xe34e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block267 : PLift (G 13553 13619) := ⟨bs [0x634f1,0x634ff,0x63509,0x63517,0xa351d,0x4352d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block268 : PLift (G 13619 13681) := ⟨bs [0x43533,0x4353b,0xa3541,0x63551,0xc3565,0xe356f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block269 : PLift (G 13681 13711) := ⟨bs [0x2c3571,0x63577,0x4357b,0xc357d,0x63581,0x4358d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block270 : PLift (G 13711 13759) := ⟨bs [0xc358f,0x63599,0x4359b,0x2e35a1,0x1635b7,0x435bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block271 : PLift (G 13759 13829) := ⟨bs [0xc35bf,0x435c3,0xe35d5,0xe35dd,0xe35e7,0xa35ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block272 : PLift (G 13829 13879) := ⟨bs [0x43605,0xc3607,0xc3611,0x43623,0xa3631,0x43635] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block273 : PLift (G 13879 13921) := ⟨bs [0xc3637,0x4363b,0x4364d,0x6364f,0x43653,0x63659] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block274 : PLift (G 13921 13999) := ⟨bs [0xe3661,0x4366b,0x4366d,0x6368b,0xa368f,0x436ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block275 : PLift (G 13999 14057) := ⟨bs [0x636af,0x636b9,0x436bb,0xc36cd,0x636d1,0x436e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block276 : PLift (G 14057 14143) := ⟨bs [0x636e9,0xe36f7,0x63701,0x63703,0xa3707,0x4371b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block277 : PLift (G 14143 14197) := ⟨bs [0x6373f,0xc3745,0x63749,0x1a374f,0x4375d,0x63761] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block278 : PLift (G 14197 14281) := ⟨bs [0x163775,0xa377f,0x4378d,0x437a3,0x637a9,0x637ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block279 : PLift (G 14281 14341) := ⟨bs [0x2637c9,0xc37d5,0xa37df,0x637f1,0xa37f3,0xa37f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block280 : PLift (G 14341 14407) := ⟨bs [0x43805,0x6380b,0x63821,0x43833,0x43835,0x163841] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block281 : PLift (G 14407 14447) := ⟨bs [0x263847,0x4384b,0x43853,0xa3857,0x6385f,0xa3865] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block282 : PLift (G 14447 14519) := ⟨bs [0xa386f,0x2c3871,0x4387d,0x6388f,0x63899,0x638a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block283 : PLift (G 14519 14557) := ⟨bs [0x1a38b7,0x438c5,0x638c9,0xa38cf,0x438d5,0x638d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block284 : PLift (G 14557 14627) := ⟨bs [0x438dd,0xc38e1,0x638e3,0x1638ff,0xa3901,0x4391d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block285 : PLift (G 14627 14669) := ⟨bs [0x43923,0x43925,0x63929,0x16392f,0x4393d,0x63941] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block286 : PLift (G 14669 14731) := ⟨bs [0x4394d,0x6395b,0x4396b,0xa3979,0x4397d,0x43983] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block287 : PLift (G 14731 14767) := ⟨bs [0x14398b,0x143991,0x43995,0x4399b,0x639a1,0x2239a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block288 : PLift (G 14767 14821) := ⟨bs [0x639af,0x439b3,0x639bb,0xa39bf,0x439cd,0x439dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block289 : PLift (G 14821 14869) := ⟨bs [0x439e5,0x439eb,0x1639ef,0x439fb,0x43a03,0x43a13] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block290 : PLift (G 14869 14929) := ⟨bs [0x43a15,0xe3a1f,0x63a27,0x43a2b,0x63a31,0x43a4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block291 : PLift (G 14929 14983) := ⟨bs [0xe3a51,0x43a5b,0x43a63,0x263a67,0x43a6d,0x63a79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block292 : PLift (G 14983 15073) := ⟨bs [0x63a87,0x43aa5,0x63aa9,0x63ab7,0x43acd,0x43ad5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block293 : PLift (G 15073 15121) := ⟨bs [0xa3ae1,0x43ae5,0x43aeb,0x43af3,0x43afd,0x43b03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block294 : PLift (G 15121 15173) := ⟨bs [0x163b11,0x43b1b,0x63b21,0x43b23,0x43b2d,0x63b39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block295 : PLift (G 15173 15233) := ⟨bs [0x43b45,0x43b53,0xa3b59,0xc3b5f,0x143b71,0x43b7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block296 : PLift (G 15233 15277) := ⟨bs [0x63b81,0x163b89,0x43b9b,0xa3b9f,0x43ba5,0x163ba7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block297 : PLift (G 15277 15319) := ⟨bs [0xc3bad,0xa3bb7,0x163bb9,0x43bc3,0x63bcb,0xa3bd1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block298 : PLift (G 15319 15373) := ⟨bs [0x63bd7,0x63be1,0x43be3,0x43bf5,0x163bff,0xe3c01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block299 : PLift (G 15373 15427) := ⟨bs [0x43c0d,0x63c11,0xa3c17,0x183c1f,0xc3c29,0x43c35] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block300 : PLift (G 15427 15473) := ⟨bs [0x43c43,0x63c4f,0x43c53,0x63c5b,0x43c65,0xa3c6b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block301 : PLift (G 15473 15551) := ⟨bs [0x63c71,0xa3c85,0x63c89,0x63c97,0xa3ca7,0xc3cb5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block302 : PLift (G 15551 15607) := ⟨bs [0xe3cbf,0x63cc7,0x63cd1,0x43cdd,0xa3cdf,0x2e3cf1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block303 : PLift (G 15607 15649) := ⟨bs [0x63cf7,0xe3d03,0x43d0d,0x63d19,0xa3d1b,0xa3d1f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block304 : PLift (G 15649 15727) := ⟨bs [0x163d21,0x43d2d,0x43d33,0x1a3d37,0x163d3f,0x43d43] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block305 : PLift (G 15727 15761) := ⟨bs [0x63d6f,0x43d73,0xc3d75,0x63d79,0x43d7b,0x43d85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block306 : PLift (G 15761 15803) := ⟨bs [0x63d91,0xa3d97,0x43d9d,0x43dab,0x3a3daf,0x43db5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block307 : PLift (G 15803 15881) := ⟨bs [0x43dbb,0x63dc1,0xa3dc9,0x63dcf,0x43df3,0xa3e05] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block308 : PLift (G 15881 15919) := ⟨bs [0x63e09,0xa3e0f,0x2a3e11,0x143e1d,0x43e23,0xa3e29] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block309 : PLift (G 15919 15991) := ⟨bs [0xc3e2f,0x43e33,0xe3e41,0x163e57,0x43e63,0xe3e65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block310 : PLift (G 15991 16063) := ⟨bs [0x183e77,0x63e81,0xa3e87,0xa3ea1,0xe3eb9,0x183ebd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block311 : PLift (G 16063 16097) := ⟨bs [0xa3ebf,0x43ec3,0x43ec5,0x63ec9,0xa3ed7,0xc3edb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block312 : PLift (G 16097 16183) := ⟨bs [0x63ee1,0xa3ee7,0xe3eef,0xa3eff,0x43f0b,0xc3f0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block313 : PLift (G 16183 16229) := ⟨bs [0x63f37,0x43f3b,0x43f3d,0xa3f41,0x63f59,0xa3f5f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block314 : PLift (G 16229 16301) := ⟨bs [0x43f65,0x63f67,0x223f79,0x43f7d,0x63f8b,0xe3f91] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block315 : PLift (G 16301 16363) := ⟨bs [0x43fad,0xe3fbf,0x43fcd,0x43fd3,0x43fdd,0x63fe9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block316 : PLift (G 16363 16427) := ⟨bs [0x43feb,0xe3ff1,0x43ffd,0x6401b,0x144021,0x44025] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block317 : PLift (G 16427 16481) := ⟨bs [0x4402b,0x64031,0x6403f,0xe4043,0x44045,0x4405d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block318 : PLift (G 16481 16553) := ⟨bs [0xc4061,0xa4067,0x4406d,0x64087,0x64091,0x440a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block319 : PLift (G 16553 16619) := ⟨bs [0x640a9,0xe40b1,0x640b7,0x440bd,0x440db,0xa40df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block320 : PLift (G 16619 16661) := ⟨bs [0x440eb,0x2640f7,0x1e40f9,0x64109,0x4410b,0xa4111] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block321 : PLift (G 16661 16729) := ⟨bs [0x144115,0x64121,0xc4133,0x44135,0x6413b,0xa413f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block322 : PLift (G 16729 16811) := ⟨bs [0x1a4159,0xc4165,0x4416b,0x64177,0x4417b,0x44193] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block323 : PLift (G 16811 16879) := ⟨bs [0xe41ab,0xa41b7,0x441bd,0xc41bf,0x441cb,0x2241e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block324 : PLift (G 16879 16927) := ⟨bs [0x641ef,0x441f3,0x641f9,0x44205,0x64207,0x224219] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block325 : PLift (G 16927 16981) := ⟨bs [0xc421f,0x44223,0x64229,0xa422f,0x44243,0x44253] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block326 : PLift (G 16981 17029) := ⟨bs [0x44255,0x6425b,0x144261,0x44273,0x4427d,0x44283] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block327 : PLift (G 17029 17093) := ⟨bs [0x144285,0x64289,0xe4291,0x64297,0x4429d,0x442b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block328 : PLift (G 17093 17159) := ⟨bs [0x442c5,0x442cb,0x642d3,0x642dd,0x442e3,0xa42f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block329 : PLift (G 17159 17207) := ⟨bs [0xe4307,0x6430f,0xa431f,0x44325,0x64327,0x44333] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block330 : PLift (G 17207 17293) := ⟨bs [0xa4337,0x1c4339,0x1a434f,0xc4357,0xa4369,0xc438b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block331 : PLift (G 17293 17341) := ⟨bs [0xe438d,0x44393,0x443a5,0x643a9,0xa43af,0x443b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block332 : PLift (G 17341 17389) := ⟨bs [0xc43bd,0x1643c7,0x643cf,0xe43e1,0xa43e7,0x443eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block333 : PLift (G 17389 17443) := ⟨bs [0x443ed,0x643f1,0x1643f9,0x64409,0x6440b,0x64417] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block334 : PLift (G 17443 17489) := ⟨bs [0x44423,0x1c4429,0x6443b,0x16443f,0x44445,0x4444b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block335 : PLift (G 17489 17551) := ⟨bs [0x64451,0x64453,0xa4459,0x44465,0x1a446f,0x64483] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block336 : PLift (G 17551 17599) := ⟨bs [0x6448f,0x1644a1,0x444a5,0x444ab,0x1444ad,0x444bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block337 : PLift (G 17599 17669) := ⟨bs [0xc44bf,0x644c9,0x644d7,0x444db,0x644f9,0x644fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block338 : PLift (G 17669 17737) := ⟨bs [0x44505,0x64511,0xa4513,0x6452b,0xe4531,0x64541] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block339 : PLift (G 17737 17791) := ⟨bs [0xe4549,0x44553,0x44555,0x264561,0xa4577,0x4457d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block340 : PLift (G 17791 17863) := ⟨bs [0x6457f,0xa458f,0x445a3,0x445ad,0xc45af,0x445bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block341 : PLift (G 17863 17921) := ⟨bs [0xc45c7,0xe45d9,0x445e3,0xa45ef,0x445f5,0x645f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block342 : PLift (G 17921 17971) := ⟨bs [0x64601,0x44603,0x164609,0x44613,0x44625,0xc4627] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block343 : PLift (G 17971 18041) := ⟨bs [0x64633,0xa4639,0x4463d,0xa4643,0x44645,0x4465d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block344 : PLift (G 18041 18077) := ⟨bs [0x64679,0x4467b,0xa467f,0x1a4681,0x4468b,0xc468d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block345 : PLift (G 18077 18131) := ⟨bs [0x4469d,0x646a9,0xa46b1,0x2246c7,0x2e46c9,0x646cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block346 : PLift (G 18131 18191) := ⟨bs [0xe46d3,0xa46d5,0xa46df,0x446e5,0x1646f9,0x44705] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block347 : PLift (G 18191 18233) := ⟨bs [0x3a470f,0x164717,0xe4723,0xe4729,0x6472f,0x44735] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block348 : PLift (G 18233 18289) := ⟨bs [0x64739,0x4474b,0xa474d,0xa4751,0x4475d,0xa476f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block349 : PLift (G 18289 18341) := ⟨bs [0x1a4771,0xc477d,0x164783,0x1a4787,0x144789,0x64799] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block350 : PLift (G 18341 18401) := ⟨bs [0x647a5,0x647b1,0x647bf,0x1647c3,0x647cb,0xc47dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block351 : PLift (G 18401 18451) := ⟨bs [0x647e1,0x447ed,0x447fb,0xa4801,0x64807,0x4480b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block352 : PLift (G 18451 18517) := ⟨bs [0x64813,0xa4819,0x4481d,0x1a4831,0x4483d,0xa4847] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block353 : PLift (G 18517 18583) := ⟨bs [0xc4855,0x64859,0x6485b,0xc486b,0xc486d,0xa4879] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block354 : PLift (G 18583 18671) := ⟨bs [0x64897,0x4489b,0x648a1,0x648b9,0x448cd,0x1448e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block355 : PLift (G 18671 18731) := ⟨bs [0xe48ef,0xc48f7,0x64903,0x4490d,0x64919,0xe491f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block356 : PLift (G 18731 18793) := ⟨bs [0x4492b,0xa4937,0x4493d,0x44945,0x44955,0x44963] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block357 : PLift (G 18793 18899) := ⟨bs [0xa4969,0x6496d,0xa4973,0xe4997,0x449ab,0x449b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block358 : PLift (G 18899 18959) := ⟨bs [0x449d3,0x1c49df,0xe49e1,0x449e5,0x649e7,0x44a03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block359 : PLift (G 18959 19031) := ⟨bs [0x1a4a0f,0x44a1d,0x44a23,0x64a39,0x2e4a41,0x44a45] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block360 : PLift (G 19031 19081) := ⟨bs [0x164a57,0x44a5d,0x44a6b,0x44a7d,0x64a81,0xe4a87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block361 : PLift (G 19081 19163) := ⟨bs [0x224a89,0x264a8f,0xc4ab1,0x44ac3,0x44ac5,0x44ad5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block362 : PLift (G 19163 19219) := ⟨bs [0x44adb,0x44aed,0x64aef,0xa4b07,0xc4b0b,0xa4b0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block363 : PLift (G 19219 19273) := ⟨bs [0x44b13,0xc4b1f,0x44b25,0xe4b31,0x44b3b,0x64b43] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block364 : PLift (G 19273 19373) := ⟨bs [0xa4b49,0x64b59,0x44b65,0xc4b6d,0x164b77,0x44b85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block365 : PLift (G 19373 19417) := ⟨bs [0x44bad,0x44bb3,0xe4bb5,0x44bbb,0x164bbf,0x44bcb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block366 : PLift (G 19417 19441) := ⟨bs [0xa4bd9,0x64bdd,0x64bdf,0x44be3,0xc4be5,0x64be9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block367 : PLift (G 19441 19477) := ⟨bs [0x1a4bf1,0x64bf7,0x64c01,0xa4c07,0x44c0d,0x164c0f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block368 : PLift (G 19477 19541) := ⟨bs [0xc4c15,0x44c1b,0x264c21,0x44c2d,0x44c33,0x1a4c4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block369 : PLift (G 19541 19583) := ⟨bs [0x44c55,0x64c57,0x64c61,0x1a4c67,0x44c73,0x64c79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block370 : PLift (G 19583 19687) := ⟨bs [0xa4c7f,0x44c8d,0x44c93,0x1a4c99,0x44ccd,0x164ce1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block371 : PLift (G 19687 19739) := ⟨bs [0xa4ce7,0x64cf1,0xe4cf3,0x44cfd,0x44d05,0xa4d0f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block372 : PLift (G 19739 19793) := ⟨bs [0x44d1b,0xe4d27,0xa4d29,0x64d2f,0x44d33,0x164d41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block373 : PLift (G 19793 19853) := ⟨bs [0x64d51,0x1a4d59,0x44d65,0x64d6b,0x64d81,0x264d83] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block374 : PLift (G 19853 19919) := ⟨bs [0x44d8d,0x164d95,0x44d9b,0x64db1,0x44db3,0x64dc9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block375 : PLift (G 19919 19973) := ⟨bs [0xe4dcf,0xc4dd7,0x64de1,0x44ded,0xc4df9,0x44dfb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block376 : PLift (G 19973 20021) := ⟨bs [0x44e05,0x44e0b,0x164e17,0x144e19,0x44e1d,0x184e2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block377 : PLift (G 20021 20071) := ⟨bs [0x64e35,0x64e37,0x44e3d,0x64e4f,0x44e53,0xa4e5f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block378 : PLift (G 20071 20123) := ⟨bs [0x64e67,0xe4e79,0xc4e85,0x44e8b,0x144e91,0x44e95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block379 : PLift (G 20123 20173) := ⟨bs [0x44e9b,0x64ea1,0xa4eaf,0xc4eb3,0x44eb5,0x1a4ec1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block380 : PLift (G 20173 20233) := ⟨bs [0x44ecd,0x64ed1,0xa4ed7,0xc4ee9,0x44efb,0x3a4f07] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block381 : PLift (G 20233 20323) := ⟨bs [0xa4f09,0x64f19,0x44f25,0x44f2d,0xa4f3f,0x64f49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block382 : PLift (G 20323 20357) := ⟨bs [0x44f63,0xa4f67,0x64f6d,0x44f75,0x64f7b,0xa4f81] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block383 : PLift (G 20357 20407) := ⟨bs [0x44f85,0x164f87,0x64f91,0xc4fa5,0x64fa9,0xe4faf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block384 : PLift (G 20407 20479) := ⟨bs [0xa4fb7,0xc4fbb,0x64fcf,0x64fd9,0x44fdb,0x44ffd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block385 : PLift (G 20479 20543) := ⟨bs [0x64fff,0xa5003,0x4501b,0x4501d,0x165029,0x45035] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block386 : PLift (G 20543 20611) := ⟨bs [0xa503f,0x45045,0x65047,0x65053,0xa5071,0x65077] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block387 : PLift (G 20611 20693) := ⟨bs [0x45083,0x45093,0x16509f,0xe50a1,0xa50b7,0x650c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block388 : PLift (G 20693 20747) := ⟨bs [0x450d5,0xa50e3,0x450ed,0x650ef,0x450fb,0xa5107] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block389 : PLift (G 20747 20789) := ⟨bs [0xa510b,0x4510d,0x65111,0xe5117,0x45123,0x45125] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block390 : PLift (G 20789 20879) := ⟨bs [0x45135,0xa5147,0xe5149,0x65171,0x145179,0x65189] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block391 : PLift (G 20879 20929) := ⟨bs [0x16518f,0x65197,0x651a1,0x451a3,0xa51a7,0x651b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block392 : PLift (G 20929 20983) := ⟨bs [0xe51c1,0x451cb,0x651d3,0xe51df,0x451e3,0x451f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block393 : PLift (G 20983 21023) := ⟨bs [0x651f7,0x165209,0x45213,0x45215,0x65219,0x4521b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block394 : PLift (G 21023 21101) := ⟨bs [0xa521f,0x185227,0x45243,0xe5245,0x4524b,0x65261] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block395 : PLift (G 21101 21157) := ⟨bs [0x4526d,0x45273,0x265281,0x45293,0x145297,0x6529d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block396 : PLift (G 21157 21193) := ⟨bs [0x452a5,0x452ab,0x1a52b1,0x452bb,0x452c3,0xe52c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block397 : PLift (G 21193 21277) := ⟨bs [0x1652c9,0x452db,0x452e5,0x452eb,0x652ff,0x45315] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block398 : PLift (G 21277 21341) := ⟨bs [0xc531d,0x165323,0xa5341,0x45345,0x1c5347,0xa534b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block399 : PLift (G 21341 21397) := ⟨bs [0x4535d,0x45363,0x65381,0x45383,0xa5387,0xc538f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block400 : PLift (G 21397 21481) := ⟨bs [0x45395,0x65399,0xa539f,0x453ab,0xa53b9,0x453db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block401 : PLift (G 21481 21517) := ⟨bs [0x1a53e9,0x653ef,0x453f3,0x453f5,0x653fb,0xa53ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block402 : PLift (G 21517 21563) := ⟨bs [0xa540d,0x65411,0x45413,0x165419,0x45435,0x1e5437] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block403 : PLift (G 21563 21601) := ⟨bs [0x4543b,0x65441,0xa5449,0x45453,0x45455,0xe545f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block404 : PLift (G 21601 21661) := ⟨bs [0xe5461,0x4546b,0x4546d,0x65471,0xa548f,0x1c5491] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block405 : PLift (G 21661 21737) := ⟨bs [0x4549d,0x1454a9,0x454b3,0x454c5,0x654d1,0x654df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block406 : PLift (G 21737 21787) := ⟨bs [0xc54e9,0x454eb,0x654f7,0xa54fd,0xa5507,0x4550d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block407 : PLift (G 21787 21841) := ⟨bs [0x2e551b,0xe5527,0x4552b,0xe5539,0x4553d,0x16554f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block408 : PLift (G 21841 21893) := ⟨bs [0x165551,0xc555b,0x45563,0xa5567,0xc556f,0x65579] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block409 : PLift (G 21893 21977) := ⟨bs [0x45585,0x1a5597,0x655a9,0xe55b1,0xa55b7,0x2255c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block410 : PLift (G 21977 22031) := ⟨bs [0x655d9,0x655e7,0xe55ed,0x455f3,0x455fd,0x6560b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block411 : PLift (G 22031 22073) := ⟨bs [0xe560f,0x45615,0xc5617,0x65623,0xa562f,0x45633] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block412 : PLift (G 22073 22123) := ⟨bs [0x65639,0xe563f,0x4564b,0xc564d,0x4565d,0xc565f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block413 : PLift (G 22123 22159) := ⟨bs [0x4566b,0x265671,0x45675,0xa5683,0xa5689,0x4568d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block414 : PLift (G 22159 22259) := ⟨bs [0xc568f,0x4569b,0x456ad,0x656b1,0x456d5,0xa56e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block415 : PLift (G 22259 22291) := ⟨bs [0x456f3,0xe56ff,0xa5701,0x45705,0x65707,0x4570b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block416 : PLift (G 22291 22369) := ⟨bs [0x65713,0xc571f,0x45723,0xa5747,0x4574d,0xa575f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block417 : PLift (G 22369 22441) := ⟨bs [0x165761,0x14576d,0x1a5777,0x4577d,0x65789,0x657a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block418 : PLift (G 22441 22501) := ⟨bs [0x1c57a9,0x657af,0xa57b5,0x457c5,0x657d1,0x457d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block419 : PLift (G 22501 22567) := ⟨bs [0x457e5,0x1657ef,0x45803,0x6580d,0x6580f,0x45815] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block420 : PLift (G 22567 22637) := ⟨bs [0x65827,0xc582b,0xc582d,0x45855,0x4585b,0x4585d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block421 : PLift (G 22637 22691) := ⟨bs [0x4586d,0xc586f,0x45873,0x6587b,0x4588d,0x1a5897] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block422 : PLift (G 22691 22727) := ⟨bs [0x458a3,0x658a9,0x1858ab,0x458b5,0x458bd,0x658c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block423 : PLift (G 22727 22783) := ⟨bs [0xa58c7,0x458d3,0xe58d5,0x2a58df,0x658f1,0xe58f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block424 : PLift (G 22783 22859) := ⟨bs [0x658ff,0x45903,0x65917,0xc591b,0x65921,0x45945] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block425 : PLift (G 22859 22921) := ⟨bs [0x4594b,0x4594d,0xe5957,0x4595d,0x45975,0xa597b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block426 : PLift (G 22921 22993) := ⟨bs [0xe5989,0x65999,0xa599f,0xc59b1,0x659b3,0x459bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block427 : PLift (G 22993 23029) := ⟨bs [0xa59d1,0x459db,0xe59e3,0xa59e9,0x459ed,0x459f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block428 : PLift (G 23029 23063) := ⟨bs [0x459f5,0xe59ff,0x165a01,0x45a0d,0xa5a11,0x65a13] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block429 : PLift (G 23063 23131) := ⟨bs [0xa5a17,0x65a1f,0x65a29,0xa5a2f,0x45a3b,0x45a4d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block430 : PLift (G 23131 23197) := ⟨bs [0x65a5b,0xa5a67,0x165a77,0x65a7f,0xa5a85,0x45a95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block431 : PLift (G 23197 23269) := ⟨bs [0x45a9d,0x65aa1,0x65aa3,0x3e5aa9,0x65abb,0x45ad3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block432 : PLift (G 23269 23321) := ⟨bs [0xc5ae5,0xe5aef,0xc5afb,0xa5afd,0x65b01,0x65b0f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block433 : PLift (G 23321 23371) := ⟨bs [0x65b19,0xa5b1f,0x45b25,0x45b2b,0x45b3d,0x65b49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block434 : PLift (G 23371 23473) := ⟨bs [0x45b4b,0x225b67,0x65b79,0x65b87,0xa5b97,0x45ba3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block435 : PLift (G 23473 23549) := ⟨bs [0xa5bb1,0xa5bc9,0x45bd5,0x45beb,0x65bf1,0x45bf3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block436 : PLift (G 23549 23593) := ⟨bs [0x45bfd,0xa5c05,0x65c09,0x45c0b,0xa5c0f,0xc5c1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block437 : PLift (G 23593 23629) := ⟨bs [0xa5c29,0x65c2f,0x45c33,0xc5c39,0xc5c47,0x45c4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block438 : PLift (G 23629 23687) := ⟨bs [0x45c4d,0xa5c51,0xa5c6f,0x45c75,0x65c77,0xa5c7d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block439 : PLift (G 23687 23753) := ⟨bs [0xa5c87,0x165c89,0xc5ca7,0x45cbd,0x65cbf,0x45cc3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block440 : PLift (G 23753 23813) := ⟨bs [0x65cc9,0xe5cd1,0x65cd7,0xa5cdd,0x45ced,0x65cf9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block441 : PLift (G 23813 23869) := ⟨bs [0x45d05,0x45d0b,0x45d13,0x165d17,0xa5d19,0xa5d31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block442 : PLift (G 23869 23909) := ⟨bs [0x45d3d,0x65d41,0xe5d47,0x65d4f,0xa5d55,0x45d5b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block443 : PLift (G 23909 23977) := ⟨bs [0x45d65,0xc5d67,0x45d6d,0xe5d79,0x45d95,0x145da3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block444 : PLift (G 23977 24023) := ⟨bs [0xa5da9,0x65dad,0x65db9,0x1c5dc1,0x225dc7,0x45dd3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block445 : PLift (G 24023 24077) := ⟨bs [0xa5dd7,0x45ddd,0x45deb,0x265df1,0x145dfd,0x165e07] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block446 : PLift (G 24077 24109) := ⟨bs [0x45e0d,0x45e13,0xe5e1b,0xa5e21,0xa5e27,0x45e2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block447 : PLift (G 24109 24169) := ⟨bs [0x45e2d,0x65e31,0x1a5e39,0xc5e45,0x65e49,0xc5e57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block448 : PLift (G 24169 24229) := ⟨bs [0x165e69,0x45e73,0x225e75,0x45e85,0x45e8b,0x65e9f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block449 : PLift (G 24229 24329) := ⟨bs [0x45ea5,0x1a5eaf,0x65eb7,0xc5ebb,0x65ed9,0x45efd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block450 : PLift (G 24329 24391) := ⟨bs [0x65f09,0xa5f11,0x165f27,0x45f33,0xe5f35,0x45f3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block451 : PLift (G 24391 24443) := ⟨bs [0x65f47,0xa5f57,0x45f5d,0x45f63,0xe5f65,0xc5f77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block452 : PLift (G 24443 24517) := ⟨bs [0x45f7b,0x1c5f95,0x65f99,0x165fa1,0x45fb3,0x45fbd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block453 : PLift (G 24517 24593) := ⟨bs [0xa5fc5,0xa5fcf,0x45fd5,0x45fe3,0xe5fe7,0xe5ffb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block454 : PLift (G 24593 24677) := ⟨bs [0x66011,0x1a6023,0xa602f,0x66037,0x46053,0x16605f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block455 : PLift (G 24677 24749) := ⟨bs [0x46065,0x4606b,0x46073,0xa6079,0x46085,0x4609d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block456 : PLift (G 24749 24809) := ⟨bs [0x460ad,0x460bb,0xa60bf,0x460cd,0xa60d9,0xc60df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block457 : PLift (G 24809 24877) := ⟨bs [0xc60e9,0x460f5,0x1c6109,0x6610f,0x46113,0x4611b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block458 : PLift (G 24877 24943) := ⟨bs [0xa612d,0x166139,0x4614b,0x46155,0x66157,0x4615b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block459 : PLift (G 24943 24989) := ⟨bs [0xa616f,0x66179,0x66187,0x4618b,0x66191,0x46193] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block460 : PLift (G 24989 25073) := ⟨bs [0x4619d,0x461b5,0x1a61c7,0xa61c9,0x461cd,0xa61e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block461 : PLift (G 25073 25127) := ⟨bs [0x661f1,0x661ff,0x66209,0x66217,0xa621d,0x66221] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block462 : PLift (G 25127 25183) := ⟨bs [0xa6227,0x4623b,0x146241,0x4624b,0x66251,0x66253] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block463 : PLift (G 25183 25247) := ⟨bs [0xa625f,0x46265,0x46283,0x4628d,0x46295,0x4629b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block464 : PLift (G 25247 25309) := ⟨bs [0xa629f,0x462a5,0xe62ad,0x662d5,0x662d7,0x462db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block465 : PLift (G 25309 25367) := ⟨bs [0x1a62dd,0x2662e9,0x662fb,0xa62ff,0x46305,0x4630d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block466 : PLift (G 25367 25439) := ⟨bs [0xa6317,0x4631d,0xe632f,0x66341,0xe6343,0x6634f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block467 : PLift (G 25439 25471) := ⟨bs [0xe635f,0x66367,0x4636d,0x66371,0xa6377,0x4637d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block468 : PLift (G 25471 25579) := ⟨bs [0xc637f,0x463b3,0x1463c1,0x463c5,0x1663d9,0x663e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block469 : PLift (G 25579 25621) := ⟨bs [0x463eb,0xa63ef,0x463f5,0x66401,0x46403,0xe6409] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block470 : PLift (G 25621 25673) := ⟨bs [0x146415,0xa6421,0x66427,0x4642b,0xa6439,0x46443] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block471 : PLift (G 25673 25741) := ⟨bs [0x66449,0x16644f,0x4645d,0xa6467,0x46475,0x46485] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block472 : PLift (G 25741 25799) := ⟨bs [0xc648d,0x46493,0x6649f,0xa64a3,0x464ab,0x664c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block473 : PLift (G 25799 25867) := ⟨bs [0xe64c7,0xe64c9,0x664db,0x664f1,0xa64f7,0xe64f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block474 : PLift (G 25867 25931) := ⟨bs [0x4650b,0x146511,0x66521,0xa652f,0x66539,0x16653f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block475 : PLift (G 25931 25981) := ⟨bs [0x4654b,0x4654d,0x66553,0xa6557,0x6655f,0xe6571] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block476 : PLift (G 25981 26029) := ⟨bs [0x16657d,0x4658d,0xe658f,0x46593,0xa65a1,0x465a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block477 : PLift (G 26029 26111) := ⟨bs [0xc65ad,0x1a65b9,0x465c5,0xe65e3,0x465f3,0x465fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block478 : PLift (G 26111 26171) := ⟨bs [0xe65ff,0xe6601,0x66607,0x4661d,0x66629,0x1a6631] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block479 : PLift (G 26171 26227) := ⟨bs [0x4663b,0x66641,0xa6647,0x4664d,0x6665b,0x166661] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block480 : PLift (G 26227 26267) := ⟨bs [0x66673,0x4667d,0x66689,0x4668b,0x46695,0x66697] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block481 : PLift (G 26267 26339) := ⟨bs [0x4669b,0xc66b5,0x666b9,0x466c5,0xc66cd,0x666d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block482 : PLift (G 26339 26399) := ⟨bs [0x466e3,0x666eb,0x466f5,0x66703,0x46713,0x66719] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block483 : PLift (G 26399 26449) := ⟨bs [0xe671f,0xa6727,0x66731,0xa6737,0x6673f,0xa6745] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block484 : PLift (G 26449 26513) := ⟨bs [0xe6751,0x4675b,0x6676f,0x66779,0xa6781,0x46785] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block485 : PLift (G 26513 26597) := ⟨bs [0x66791,0x467ab,0x467bd,0x667c1,0x467cd,0x2c67df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block486 : PLift (G 26597 26681) := ⟨bs [0x467e5,0x46803,0x66809,0xe6811,0x66817,0x4682d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block487 : PLift (G 26681 26711) := ⟨bs [0xc6839,0x4683b,0xa683f,0x46845,0x4684b,0x2c684d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block488 : PLift (G 26711 26737) := ⟨bs [0x166857,0x146859,0x4685d,0x46863,0x66869,0x6686b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block489 : PLift (G 26737 26821) := ⟨bs [0x146871,0x1a6887,0x66899,0xa689f,0x668b1,0x468bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block490 : PLift (G 26821 26879) := ⟨bs [0x468c5,0xa68d1,0x668d7,0x668e1,0x468ed,0xa68ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block491 : PLift (G 26879 26927) := ⟨bs [0x1a68ff,0x166901,0xc690b,0xa690d,0xa6917,0x1a6929] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block492 : PLift (G 26927 26987) := ⟨bs [0xa692f,0x46943,0xe6947,0xe6949,0xc694f,0x66965] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block493 : PLift (G 26987 27059) := ⟨bs [0x4696b,0x66971,0x46983,0xa6989,0xc6997,0x469a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block494 : PLift (G 27059 27103) := ⟨bs [0x469b3,0x469b5,0x469bb,0xa69c1,0x469c5,0x469d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block495 : PLift (G 27103 27191) := ⟨bs [0x669df,0x469e3,0xe69e5,0x669f7,0xa6a07,0x46a2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block496 : PLift (G 27191 27259) := ⟨bs [0x346a37,0x46a3d,0x146a4b,0xe6a67,0x226a69,0x46a75] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block497 : PLift (G 27259 27329) := ⟨bs [0x46a7b,0xc6a87,0xc6a8d,0xc6a91,0xa6a93,0x46aa3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block498 : PLift (G 27329 27409) := ⟨bs [0x66ac1,0xa6ac9,0xe6ae1,0x66ae7,0x46b05,0xa6b0f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block499 : PLift (G 27409 27479) := ⟨bs [0x1a6b11,0xa6b23,0x226b27,0x46b2d,0x66b39,0xe6b41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block500 : PLift (G 27479 27539) := ⟨bs [0xe6b57,0xe6b59,0x66b5f,0x46b75,0xa6b87,0xe6b89] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block501 : PLift (G 27539 27617) := ⟨bs [0x46b93,0x266b95,0x226b9f,0x46bbd,0x66bbf,0x46bdb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block502 : PLift (G 27617 27691) := ⟨bs [0x66be1,0xc6bef,0xa6bff,0x46c05,0x166c19,0x66c29] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block503 : PLift (G 27691 27743) := ⟨bs [0x66c2b,0xa6c31,0x46c35,0x46c55,0x66c59,0x66c5b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block504 : PLift (G 27743 27779) := ⟨bs [0xa6c5f,0x66c65,0x66c67,0x66c73,0xa6c77,0x46c7d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block505 : PLift (G 27779 27817) := ⟨bs [0x46c83,0xe6c8f,0xa6c91,0xe6c97,0x46c9b,0x66ca1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block506 : PLift (G 27817 27893) := ⟨bs [0xa6ca9,0xc6caf,0x46cb3,0xc6cc7,0x46ccb,0x66ceb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block507 : PLift (G 27893 27947) := ⟨bs [0x46cf5,0x46cfd,0x46d0d,0x66d0f,0x46d25,0xa6d27] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block508 : PLift (G 27947 28001) := ⟨bs [0x46d2b,0x66d31,0x1a6d39,0x66d3f,0xa6d4f,0xa6d5d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block509 : PLift (G 28001 28069) := ⟨bs [0x66d61,0x46d73,0x46d7b,0x266d7f,0x46d93,0xa6d99] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block510 : PLift (G 28069 28111) := ⟨bs [0xe6da5,0x266db1,0x66db7,0x66dc1,0x46dc3,0x46dcd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block511 : PLift (G 28111 28201) := ⟨bs [0x66dcf,0x46ddb,0xe6df7,0x46e03,0x46e15,0x66e17] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block512 : PLift (G 28201 28283) := ⟨bs [0x166e29,0x46e33,0x66e3b,0x46e45,0x46e75,0x66e77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block513 : PLift (G 28283 28349) := ⟨bs [0x46e7b,0xc6e81,0xa6e89,0x46e93,0x46e95,0xe6e9f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block514 : PLift (G 28349 28411) := ⟨bs [0x46ebd,0xc6ebf,0x46ee3,0x1e6ee9,0xa6ef3,0x66ef9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block515 : PLift (G 28411 28477) := ⟨bs [0x46efb,0x46f0d,0x66f11,0x166f17,0x66f1f,0xa6f2f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block516 : PLift (G 28477 28541) := ⟨bs [0x46f3d,0x46f4d,0x46f53,0xa6f61,0x46f65,0xa6f79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block517 : PLift (G 28541 28579) := ⟨bs [0x46f7d,0x46f83,0x46f85,0x166f8f,0x46f9b,0x46f9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block518 : PLift (G 28579 28621) := ⟨bs [0x46fa3,0x66faf,0x46fb5,0x46fbb,0xa6fbf,0x46fcb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block519 : PLift (G 28621 28661) := ⟨bs [0x1a6fcd,0xa6fd3,0x166fd7,0x46fe3,0x66fe9,0xa6ff1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block520 : PLift (G 28661 28711) := ⟨bs [0x46ff5,0x66ff7,0xc6ffd,0xc700f,0x67019,0xa701f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block521 : PLift (G 28711 28771) := ⟨bs [0x67027,0x47033,0x2c7039,0x1c704f,0x147051,0x67057] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block522 : PLift (G 28771 28837) := ⟨bs [0x47063,0xe7075,0x67079,0x167087,0x4708d,0x67091] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block523 : PLift (G 28837 28901) := ⟨bs [0x470a5,0x470ab,0x470bb,0x670c3,0x1a70c7,0x670cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block524 : PLift (G 28901 28961) := ⟨bs [0x670e5,0x470ed,0x1670f9,0x670ff,0x47105,0x47115] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block525 : PLift (G 28961 29027) := ⟨bs [0x67121,0x47133,0x67151,0xa7159,0x4715d,0x6715f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block526 : PLift (G 29027 29123) := ⟨bs [0x47163,0x67169,0x47183,0x147187,0x47195,0x471ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block527 : PLift (G 29123 29167) := ⟨bs [0x471c3,0x671c9,0x471cb,0xa71d1,0x471db,0x671e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block528 : PLift (G 29167 29209) := ⟨bs [0x671ef,0x471f5,0x1a71fb,0xe7207,0x67211,0xa7217] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block529 : PLift (G 29209 29287) := ⟨bs [0xe7219,0x47225,0x1a722f,0x4723b,0x47243,0xc7255] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block530 : PLift (G 29287 29339) := ⟨bs [0xa7267,0x67271,0xe7277,0x6727f,0xa728f,0x47295] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block531 : PLift (G 29339 29399) := ⟨bs [0x4729b,0x672a3,0x472b3,0xc72c7,0x472cb,0x472cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block532 : PLift (G 29399 29443) := ⟨bs [0x1a72d7,0x1a72d9,0x472e3,0xa72ef,0x472f5,0x472fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block533 : PLift (G 29443 29531) := ⟨bs [0x47303,0x4730d,0xa7321,0x4732b,0x4733d,0x67357] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block534 : PLift (G 29531 29587) := ⟨bs [0x4735b,0x67361,0xa737f,0x227381,0x47385,0x14738d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block535 : PLift (G 29587 29663) := ⟨bs [0x47393,0x1a739f,0x673ab,0xe73bd,0x673c1,0xe73c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block536 : PLift (G 29663 29741) := ⟨bs [0xa73df,0x473e5,0xc73e7,0x1673f3,0x47415,0x4741b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block537 : PLift (G 29741 29819) := ⟨bs [0x4742d,0x67439,0xe743f,0x227441,0x4745d,0xe746b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block538 : PLift (G 29819 29873) := ⟨bs [0xc747b,0xa7489,0x4748d,0x4749b,0x1474a7,0x474ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block539 : PLift (G 29873 29947) := ⟨bs [0x674b1,0x1674b7,0xe74b9,0x474dd,0x674e1,0xa74e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block540 : PLift (G 29947 30029) := ⟨bs [0x674fb,0xc7507,0xa751f,0x47525,0x4753b,0x4753d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block541 : PLift (G 30029 30097) := ⟨bs [0x4754d,0xa755f,0x4756b,0x1a7577,0x67589,0x2a758b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block542 : PLift (G 30097 30137) := ⟨bs [0x147591,0x67597,0x4759d,0x675a1,0x1675a7,0xa75b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block543 : PLift (G 30137 30197) := ⟨bs [0x675b9,0x475bb,0x675d1,0xe75d9,0x475e5,0xa75eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block544 : PLift (G 30197 30259) := ⟨bs [0x475f5,0x475fb,0x47603,0x6760f,0x167621,0x4762d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block545 : PLift (G 30259 30319) := ⟨bs [0x67633,0x6763d,0x6763f,0x47655,0x47663,0xa7669] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block546 : PLift (G 30319 30391) := ⟨bs [0x6766f,0x47673,0x47685,0x4768b,0xa769f,0x476b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block547 : PLift (G 30391 30469) := ⟨bs [0x676b7,0xa76c3,0xa76db,0x1676df,0x676f1,0x47703] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block548 : PLift (G 30469 30529) := ⟨bs [0x47705,0x4771b,0xc771d,0x67721,0x4772d,0x47735] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block549 : PLift (G 30529 30593) := ⟨bs [0x1a7741,0x4774b,0xa7759,0x4775d,0xe775f,0xa7771] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block550 : PLift (G 30593 30671) := ⟨bs [0x67781,0x677a7,0x477ad,0x477b3,0xe77b9,0x477c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block551 : PLift (G 30671 30713) := ⟨bs [0x1677cf,0x477d5,0x677e1,0x1477e9,0x677ef,0x477f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block552 : PLift (G 30713 30803) := ⟨bs [0x677f9,0x67807,0xa7825,0x4782b,0x67835,0x4783d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block553 : PLift (G 30803 30851) := ⟨bs [0x47853,0x67859,0xa7861,0x4786d,0xe7877,0xe7879] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block554 : PLift (G 30851 30893) := ⟨bs [0x47883,0x47885,0x4788b,0x47895,0x67897,0x678a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block555 : PLift (G 30893 30971) := ⟨bs [0x478ad,0x2278bf,0x478d3,0x1e78d9,0x478dd,0x1478e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block556 : PLift (G 30971 31039) := ⟨bs [0x478fb,0x67901,0xa7907,0x47925,0x4792b,0x147939] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block557 : PLift (G 31039 31091) := ⟨bs [0xe793f,0x16794b,0x67957,0x4795d,0x167967,0x1a7969] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block558 : PLift (G 31091 31153) := ⟨bs [0x47973,0x67991,0x67993,0x479a3,0x479ab,0xe79af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block559 : PLift (G 31153 31193) := ⟨bs [0x1479b1,0x679b7,0xe79c9,0x479cd,0x679cf,0x1a79d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block560 : PLift (G 31193 31249) := ⟨bs [0xa79d9,0x1479f3,0xa79f7,0xc79ff,0xc7a05,0xa7a0f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block561 : PLift (G 31249 31307) := ⟨bs [0x2e7a11,0x47a15,0x47a1b,0x47a23,0xe7a27,0x47a2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block562 : PLift (G 31307 31357) := ⟨bs [0x47a4b,0xe7a57,0xe7a59,0xc7a5f,0xa7a65,0x67a69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block563 : PLift (G 31357 31469) := ⟨bs [0x47a7d,0x47a93,0x47a9b,0x3e7a9f,0xa7aa1,0x47aa5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block564 : PLift (G 31469 31517) := ⟨bs [0x47aed,0xc7af5,0xc7af9,0xe7b01,0xe7b17,0xe7b19] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block565 : PLift (G 31517 31573) := ⟨bs [0x47b1d,0x47b2b,0x67b35,0x67b37,0x47b3b,0xc7b4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block566 : PLift (G 31573 31649) := ⟨bs [0xa7b55,0xa7b5f,0x67b71,0xa7b77,0x67b8b,0x47b9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block567 : PLift (G 31649 31721) := ⟨bs [0x67ba1,0xa7ba9,0x67baf,0x47bb3,0x67bc7,0x47bd3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block568 : PLift (G 31721 31769) := ⟨bs [0x167be9,0x67beb,0xa7bef,0xe7bf1,0xc7bfd,0x167c07] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block569 : PLift (G 31769 31849) := ⟨bs [0xc7c19,0x147c1b,0x67c31,0x167c37,0x67c49,0xa7c67] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block570 : PLift (G 31849 31957) := ⟨bs [0x1c7c69,0x47c73,0x167c81,0x47c8b,0x47c93,0x47ca3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block571 : PLift (G 31957 32009) := ⟨bs [0x47cd5,0x47cdb,0x47ce5,0xc7ced,0xe7cf7,0x47d03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block572 : PLift (G 32009 32063) := ⟨bs [0x67d09,0x47d1b,0x47d1d,0x147d33,0x67d39,0x47d3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block573 : PLift (G 32063 32117) := ⟨bs [0xa7d3f,0x47d45,0x47d4d,0x47d53,0x1a7d59,0x47d63] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block574 : PLift (G 32117 32183) := ⟨bs [0x47d75,0x67d77,0x47d8d,0xc7d8f,0xe7d9f,0xa7dad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block575 : PLift (G 32183 32237) := ⟨bs [0xa7db7,0x47dbd,0xc7dbf,0x47dcb,0x47dd5,0xa7de9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block576 : PLift (G 32237 32303) := ⟨bs [0x47ded,0x67dfb,0x1e7e01,0x47e05,0x67e29,0x187e2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block577 : PLift (G 32303 32353) := ⟨bs [0xa7e2f,0x47e35,0xc7e41,0x47e43,0xa7e47,0x47e55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block578 : PLift (G 32353 32381) := ⟨bs [0x1e7e61,0x67e67,0x47e6b,0xc7e71,0x47e73,0xa7e79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block579 : PLift (G 32381 32441) := ⟨bs [0x47e7d,0xe7e91,0x47e9b,0xa7e9d,0xa7ea7,0x67ead] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block580 : PLift (G 32441 32503) := ⟨bs [0x67eb9,0x47ebb,0x47ed3,0xc7edf,0x47eeb,0xe7ef1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block581 : PLift (G 32503 32563) := ⟨bs [0x67ef7,0x47efb,0x47f13,0x47f15,0x67f19,0xc7f31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block582 : PLift (G 32563 32609) := ⟨bs [0x47f33,0xe7f39,0x47f3d,0xc7f43,0x47f4b,0x47f5b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block583 : PLift (G 32609 32687) := ⟨bs [0x67f61,0x67f63,0x67f6d,0x67f79,0x67f87,0x47f8d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block584 : PLift (G 32687 32749) := ⟨bs [0xa7faf,0x47fb5,0x67fc3,0xa7fc9,0x47fcd,0x67fcf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block585 : PLift (G 32749 32801) := ⟨bs [0x47fed,0x48003,0x6800b,0xe800f,0x48015,0x4801d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block586 : PLift (G 32801 32869) := ⟨bs [0x68021,0xa8023,0x1a803f,0xa8041,0xc8047,0x4804b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block587 : PLift (G 32869 32939) := ⟨bs [0xc8065,0x68077,0x4808d,0x6808f,0x48095,0x480a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block588 : PLift (G 32939 32987) := ⟨bs [0x480ab,0x480ad,0x1880bd,0x680c9,0x1680cb,0x680d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block589 : PLift (G 32987 33037) := ⟨bs [0x480db,0x680e1,0xe80e7,0xa80f5,0xa80ff,0x48105] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block590 : PLift (G 33037 33091) := ⟨bs [0x4810d,0x3a8119,0x4811d,0x16812f,0xa8131,0x4813b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block591 : PLift (G 33091 33161) := ⟨bs [0x68143,0x48153,0x68159,0xe815f,0x4817d,0x6817f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block592 : PLift (G 33161 33211) := ⟨bs [0x68189,0x4819b,0xc819d,0xe81a7,0x681af,0x481b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block593 : PLift (G 33211 33311) := ⟨bs [0x481bb,0x1481c7,0xa81df,0xa8207,0x3a8209,0x48215] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block594 : PLift (G 33311 33349) := ⟨bs [0x16821f,0x48225,0x68231,0x68233,0x6823f,0x48243] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block595 : PLift (G 33349 33409) := ⟨bs [0x48245,0x68249,0xe824f,0xa8261,0xc826f,0x6827b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block596 : PLift (G 33409 33479) := ⟨bs [0xe8281,0x48285,0x48293,0x1482b1,0x682b5,0x482bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block597 : PLift (G 33479 33533) := ⟨bs [0x2282c7,0xc82cf,0x482d5,0xa82df,0xc82f1,0xe82f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block598 : PLift (G 33533 33587) := ⟨bs [0x482fd,0x4830b,0x4831b,0x68321,0xa8329,0x4832d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block599 : PLift (G 33587 33619) := ⟨bs [0xc8333,0x48335,0x16833f,0x3a8341,0xa834d,0x68351] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block600 : PLift (G 33619 33679) := ⟨bs [0x48353,0xa8357,0x4835d,0x48365,0x68369,0xa836f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block601 : PLift (G 33679 33751) := ⟨bs [0x6838f,0xa83a7,0x683b1,0x1683b9,0x483cb,0x483d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block602 : PLift (G 33751 33797) := ⟨bs [0xc83d7,0x483dd,0xa83e7,0x1683e9,0x483ed,0xe83ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block603 : PLift (G 33797 33857) := ⟨bs [0x68405,0x68411,0x1e8413,0x48423,0x48425,0x4843b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block604 : PLift (G 33857 33923) := ⟨bs [0x68441,0xa8447,0x1e844f,0x1a8461,0x48465,0x168477] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block605 : PLift (G 33923 33997) := ⟨bs [0x48483,0x4848b,0xa8491,0x48495,0x1a84a9,0x684af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block606 : PLift (G 33997 34061) := ⟨bs [0x484cd,0x484e3,0xe84ef,0xe84f1,0x684f7,0xa8509] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block607 : PLift (G 34061 34157) := ⟨bs [0x4850d,0x4854b,0xa854f,0x168551,0x4855d,0x68563] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block608 : PLift (G 34157 34217) := ⟨bs [0x4856d,0x6856f,0x4857b,0x68587,0x485a3,0x485a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block609 : PLift (G 34217 34273) := ⟨bs [0x685a9,0xc85b7,0x485cd,0x485d3,0x485d5,0x485db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block610 : PLift (G 34273 34319) := ⟨bs [0xa85e1,0x485eb,0xa85f9,0x685fd,0x2285ff,0x68609] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block611 : PLift (G 34319 34369) := ⟨bs [0x26860f,0xa8617,0x68621,0x6862f,0x68639,0xa863f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block612 : PLift (G 34369 34457) := ⟨bs [0xe8641,0xc864d,0x48663,0x48675,0x4867d,0x168687] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block613 : PLift (G 34457 34501) := ⟨bs [0x68699,0x1486a5,0xc86a7,0x486b3,0xa86b7,0x486c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block614 : PLift (G 34501 34549) := ⟨bs [0xe86c5,0xe86cf,0x1686d1,0x686d7,0xa86e9,0xc86ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block615 : PLift (G 34549 34613) := ⟨bs [0x486f5,0xa8717,0x4871d,0x6871f,0x4872b,0x14872f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block616 : PLift (G 34613 34679) := ⟨bs [0x48735,0xe8747,0x68759,0x4875b,0x4876b,0x68771] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block617 : PLift (G 34679 34739) := ⟨bs [0xe8777,0xa877f,0xc8785,0xa878f,0x687a1,0x1a87a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block618 : PLift (G 34739 34807) := ⟨bs [0xc87b3,0x487bb,0x487c5,0xc87c7,0x487cb,0x487dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block619 : PLift (G 34807 34871) := ⟨bs [0x687f7,0x48803,0x68819,0x4881b,0xe881f,0xe8821] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block620 : PLift (G 34871 34939) := ⟨bs [0xe8837,0x4883d,0x48843,0xa8851,0x68861,0x268867] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block621 : PLift (G 34939 35027) := ⟨bs [0x4887b,0x48885,0x68891,0x48893,0x488a5,0xa88cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block622 : PLift (G 35027 35083) := ⟨bs [0x488d3,0x488eb,0x488ed,0x1488f3,0x488fd,0x68909] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block623 : PLift (G 35083 35129) := ⟨bs [0x4890b,0x168911,0x4891b,0x48923,0x1a8927,0x4892d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block624 : PLift (G 35129 35201) := ⟨bs [0x68939,0x48945,0x4894d,0x68951,0x168957,0x48963] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block625 : PLift (G 35201 35279) := ⟨bs [0x68981,0xc8995,0x4899b,0x689b3,0xe89b9,0x489c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block626 : PLift (G 35279 35327) := ⟨bs [0x3a89cf,0x2e89d1,0x489db,0x1689ef,0xa89f5,0x689fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block627 : PLift (G 35327 35401) := ⟨bs [0xa89ff,0x48a0b,0xa8a19,0x48a23,0x68a35,0x68a41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block628 : PLift (G 35401 35449) := ⟨bs [0x1a8a49,0xc8a4f,0x48a5b,0xa8a5f,0xc8a6d,0xa8a77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block629 : PLift (G 35449 35527) := ⟨bs [0x1a8a79,0xc8a85,0xe8aa3,0x48ab3,0x48ab5,0xe8ac1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block630 : PLift (G 35527 35573) := ⟨bs [0x68ac7,0xc8acb,0x48acd,0x68ad1,0xa8ad7,0x168af1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block631 : PLift (G 35573 35671) := ⟨bs [0x48af5,0x228b07,0xa8b09,0x48b0d,0x48b13,0x168b21] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block632 : PLift (G 35671 35759) := ⟨bs [0x68b57,0x48b5d,0x68b91,0x48b93,0x48ba3,0x68ba9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block633 : PLift (G 35759 35831) := ⟨bs [0x168baf,0xc8bbb,0x48bd5,0x68bd9,0x1c8bdb,0x1a8be1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block634 : PLift (G 35831 35879) := ⟨bs [0x168bf7,0x48bfd,0xc8bff,0x48c0b,0x68c17,0x148c1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block635 : PLift (G 35879 35951) := ⟨bs [0xe8c27,0x68c39,0x48c3b,0x188c47,0x48c53,0x48c5d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block636 : PLift (G 35951 35999) := ⟨bs [0x168c6f,0x48c7b,0x68c81,0x148c89,0x68c8f,0x68c99] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block637 : PLift (G 35999 36061) := ⟨bs [0x1a8c9f,0x68ca7,0x48cab,0x48cad,0x68cb1,0x48cc5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block638 : PLift (G 36061 36109) := ⟨bs [0x48cdd,0xa8ce3,0xa8ce9,0x48cf3,0xa8d01,0x48d0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block639 : PLift (G 36109 36191) := ⟨bs [0x48d0d,0x48d23,0x68d29,0x68d37,0x68d41,0x68d5b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block640 : PLift (G 36191 36263) := ⟨bs [0xe8d5f,0x68d71,0x268d79,0x48d85,0x268d91,0x48d9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block641 : PLift (G 36263 36313) := ⟨bs [0xa8da7,0x48dad,0x48db5,0x48dc5,0x48dcb,0x48dd3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block642 : PLift (G 36313 36383) := ⟨bs [0xa8dd9,0xc8ddf,0x48df5,0x1a8df7,0x68e01,0x48e15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block643 : PLift (G 36383 36469) := ⟨bs [0xa8e1f,0x68e25,0xa8e51,0xe8e63,0xa8e69,0x48e73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block644 : PLift (G 36469 36527) := ⟨bs [0x48e75,0x68e79,0xe8e7f,0x48e8d,0x68e91,0x48eab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block645 : PLift (G 36527 36571) := ⟨bs [0xa8eaf,0xe8eb1,0x148ebd,0xe8ec7,0xc8ecf,0x48ed3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block646 : PLift (G 36571 36637) := ⟨bs [0x48edb,0xe8ee7,0x48eeb,0x268ef7,0x68eff,0x48f15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block647 : PLift (G 36637 36691) := ⟨bs [0xa8f1d,0x68f23,0x48f2d,0x1a8f3f,0x48f45,0x48f4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block648 : PLift (G 36691 36749) := ⟨bs [0x48f53,0xa8f59,0x48f65,0x68f69,0x4a8f71,0x48f83] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block649 : PLift (G 36749 36791) := ⟨bs [0x48f8d,0xc8f99,0xa8f9f,0x48fab,0x48fad,0x48fb3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block650 : PLift (G 36791 36857) := ⟨bs [0x228fb7,0x1e8fb9,0x68fc9,0x48fd5,0x68fe1,0x68fef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block651 : PLift (G 36857 36913) := ⟨bs [0x68ff9,0x1e9007,0x4900d,0xa9017,0x49023,0x49025] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block652 : PLift (G 36913 36947) := ⟨bs [0xa9031,0x69037,0x4903b,0x69041,0x49043,0x6904f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block653 : PLift (G 36947 37019) := ⟨bs [0x49053,0x4906d,0x69073,0x49085,0x4908b,0x49095] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block654 : PLift (G 37019 37087) := ⟨bs [0x4909b,0xc909d,0x690af,0xc90b9,0xa90c1,0x490c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block655 : PLift (G 37087 37171) := ⟨bs [0x690df,0x690e9,0x490fd,0x69103,0x49113,0x69127] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block656 : PLift (G 37171 37223) := ⟨bs [0x69133,0x4913d,0x49145,0xe914f,0xe9151,0x69161] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block657 : PLift (G 37223 37309) := ⟨bs [0xa9167,0x4917b,0x49185,0xa9199,0x4919d,0x491bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block658 : PLift (G 37309 37361) := ⟨bs [0xe91bd,0x691c1,0x2e91c9,0x691d9,0x691db,0xc91ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block659 : PLift (G 37361 37423) := ⟨bs [0x691f1,0x691f3,0xe91f9,0x49203,0x49215,0x69221] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block660 : PLift (G 37423 37493) := ⟨bs [0xc922f,0x229241,0x69247,0xa9257,0x4926b,0x269271] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block661 : PLift (G 37493 37537) := ⟨bs [0x49275,0x4927d,0x229283,0x169287,0x4928d,0x69299] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block662 : PLift (G 37537 37573) := ⟨bs [0x1a92a1,0x492ab,0x492ad,0x1692b9,0x692bf,0x492c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block663 : PLift (G 37573 37633) := ⟨bs [0xa92c5,0x492cb,0x492d5,0xc92d7,0xa92e7,0x492f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block664 : PLift (G 37633 37693) := ⟨bs [0xa9301,0x4930b,0x69311,0xa9319,0x6931f,0xc933b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block665 : PLift (G 37693 37799) := ⟨bs [0x4933d,0x69343,0xa9355,0x69373,0x49395,0x69397] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block666 : PLift (G 37799 37861) := ⟨bs [0x1693a7,0xc93b3,0x493b5,0x693c7,0xa93d7,0x493dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block667 : PLift (G 37861 37951) := ⟨bs [0x493e5,0xe93ef,0xe93f7,0x69401,0xa9409,0x49413] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block668 : PLift (G 37951 37993) := ⟨bs [0x6943f,0x49445,0x4944b,0xa944f,0xa9463,0xe9467] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block669 : PLift (G 37993 38069) := ⟨bs [0x149469,0x4946d,0x4947b,0xe9497,0x6949f,0xa94a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block670 : PLift (G 38069 38167) := ⟨bs [0x494b5,0x694c3,0xe94e1,0x694e7,0xc9505,0x69509] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block671 : PLift (G 38167 38219) := ⟨bs [0x69517,0x69521,0xa9527,0x4952d,0x49535,0x69539] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block672 : PLift (G 38219 38281) := ⟨bs [0x4954b,0x1a9557,0x4955d,0x1a955f,0x49575,0x69581] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block673 : PLift (G 38281 38327) := ⟨bs [0x1c9589,0xe958f,0x4959b,0xa959f,0x495ad,0x695b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block674 : PLift (G 38327 38393) := ⟨bs [0xa95b7,0x1a95b9,0x495bd,0x1695cf,0x1495e3,0xa95e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block675 : PLift (G 38393 38461) := ⟨bs [0x695f9,0xc961f,0xa962f,0x1a9631,0x49635,0x4963b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block676 : PLift (G 38461 38569) := ⟨bs [0x1a963d,0x49665,0xa968f,0x4969d,0x696a1,0xa96a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block677 : PLift (G 38569 38639) := ⟨bs [0x1c96a9,0xa96c1,0x496cb,0x696d1,0x696d3,0x496e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block678 : PLift (G 38639 38693) := ⟨bs [0x3a96ef,0x496fb,0x496fd,0x4970d,0xc970f,0xa9715] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block679 : PLift (G 38693 38729) := ⟨bs [0x49725,0x4972b,0x49733,0xe9737,0xa9739,0x49743] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block680 : PLift (G 38729 38791) := ⟨bs [0x69749,0xa9751,0x4975b,0x4975d,0xa976f,0xa977f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block681 : PLift (G 38791 38861) := ⟨bs [0xc9787,0xa9793,0x497a5,0xa97b1,0xc97b7,0x697c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block682 : PLift (G 38861 38921) := ⟨bs [0x1c97cd,0x497d3,0x697d9,0x497eb,0xa97f7,0xa9805] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block683 : PLift (G 38921 38977) := ⟨bs [0xc9809,0x4980b,0x49815,0xa9829,0x6982f,0x4983b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block684 : PLift (G 38977 39047) := ⟨bs [0xa9841,0x69851,0x4986b,0xa986f,0x69881,0x49883] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block685 : PLift (G 39047 39113) := ⟨bs [0xa9887,0x698a7,0x698b1,0xa98b9,0xa98bf,0x498c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block686 : PLift (G 39113 39163) := ⟨bs [0x698c9,0x1698cf,0xa98dd,0xe98e3,0xc98f5,0x698f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block687 : PLift (G 39163 39227) := ⟨bs [0x498fb,0xc990d,0x169917,0x22991f,0x69929,0xe9931] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block688 : PLift (G 39227 39293) := ⟨bs [0x4993b,0x4993d,0x69941,0xe9947,0xe9949,0x49953] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block689 : PLift (G 39293 39343) := ⟨bs [0x4997d,0xe9985,0x149991,0x49995,0x4999b,0x499ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block690 : PLift (G 39343 39397) := ⟨bs [0x699af,0x1699bf,0x699c7,0x499cb,0x2c99cd,0xa99d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block691 : PLift (G 39397 39461) := ⟨bs [0x499e5,0xe99f1,0x499fb,0x69a0f,0x49a13,0x49a1b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block692 : PLift (G 39461 39541) := ⟨bs [0x49a25,0x49a4b,0xa9a4f,0x69a55,0x69a57,0x69a61] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block693 : PLift (G 39541 39619) := ⟨bs [0x49a75,0xe9a7f,0x49a8b,0x69a91,0x49a9d,0x69ab7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block694 : PLift (G 39619 39679) := ⟨bs [0x49ac3,0xa9ac7,0x69acf,0x49aeb,0x69af3,0xe9af7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block695 : PLift (G 39679 39749) := ⟨bs [0xc9aff,0xa9b17,0xc9b1d,0xe9b27,0x69b2f,0x49b35] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block696 : PLift (G 39749 39821) := ⟨bs [0x49b45,0x69b51,0x1a9b59,0x49b63,0x169b6f,0x69b77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block697 : PLift (G 39821 39857) := ⟨bs [0x49b8d,0x49b93,0xc9b95,0xe9b9f,0x3e9ba1,0xa9ba7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block698 : PLift (G 39857 39901) := ⟨bs [0x69bb1,0xa9bb7,0x49bbd,0x49bc5,0x69bcb,0xe9bcf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block699 : PLift (G 39901 39983) := ⟨bs [0x49bdd,0x69bf9,0xa9c01,0x69c11,0x49c23,0x69c2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block700 : PLift (G 39983 40039) := ⟨bs [0xa9c2f,0x49c35,0x169c49,0x49c4d,0x269c5f,0x49c65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block701 : PLift (G 40039 40123) := ⟨bs [0xc9c67,0x69c7f,0x69c97,0x49c9d,0x69ca3,0x69caf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block702 : PLift (G 40123 40169) := ⟨bs [0x49cbb,0xa9cbf,0xe9cc1,0x169cd7,0xa9cd9,0x49ce3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block703 : PLift (G 40169 40237) := ⟨bs [0x69ce9,0x149cf1,0x49cfd,0x69d01,0xc9d15,0x69d27] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block704 : PLift (G 40237 40343) := ⟨bs [0xc9d2d,0x69d31,0x49d3d,0x49d55,0x49d5b,0x69d61] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block705 : PLift (G 40343 40427) := ⟨bs [0xa9d97,0x69d9f,0xa9da5,0x69da9,0x49dc3,0x69de7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block706 : PLift (G 40427 40487) := ⟨bs [0x49deb,0x1c9ded,0xa9df1,0x49e0b,0x69e17,0x49e23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block707 : PLift (G 40487 40531) := ⟨bs [0xa9e27,0x49e2d,0x49e33,0x49e3b,0xc9e47,0x69e51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block708 : PLift (G 40531 40597) := ⟨bs [0x49e53,0x69e5f,0xe9e6f,0x69e81,0xa9e87,0x1a9e8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block709 : PLift (G 40597 40697) := ⟨bs [0x49e95,0x2c9ea1,0x49eb3,0x49ebd,0xe9ebf,0x49ef5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block710 : PLift (G 40697 40763) := ⟨bs [0x69ef9,0x49efb,0x49f05,0x49f23,0x1c9f2f,0x69f37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block711 : PLift (G 40763 40823) := ⟨bs [0x49f3b,0x149f43,0x49f53,0x1a9f61,0x49f6d,0x69f73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block712 : PLift (G 40823 40867) := ⟨bs [0xa9f77,0x49f7d,0x69f89,0xa9f8f,0x169f91,0x49f95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block713 : PLift (G 40867 40933) := ⟨bs [0x49fa3,0xc9faf,0x49fb3,0xa9fc1,0x69fc7,0x69fdf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block714 : PLift (G 40933 41011) := ⟨bs [0x49fe5,0x49feb,0x49ff5,0x6a001,0x4a00d,0xaa021] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block715 : PLift (G 41011 41057) := ⟨bs [0x4a033,0xaa039,0xaa03f,0x16a04f,0xaa057,0x4a05b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block716 : PLift (G 41057 41141) := ⟨bs [0x6a061,0x4a075,0x6a079,0xaa099,0x4a09d,0x14a0ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block717 : PLift (G 41141 41183) := ⟨bs [0x4a0b5,0x6a0b7,0x4a0bd,0x2ca0c9,0x6a0d9,0x6a0db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block718 : PLift (G 41183 41227) := ⟨bs [0xaa0df,0x4a0e5,0x6a0f1,0x6a0f3,0x4a0fd,0x4a105] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block719 : PLift (G 41227 41269) := ⟨bs [0x4a10b,0xea10f,0xaa111,0x4a11b,0xaa129,0xaa12f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block720 : PLift (G 41269 41357) := ⟨bs [0x4a135,0x22a141,0x4a153,0x4a175,0x4a17d,0xea187] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block721 : PLift (G 41357 41413) := ⟨bs [0x4a18d,0x6a1a5,0x4a1ab,0xca1ad,0xea1b7,0x4a1c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block722 : PLift (G 41413 41507) := ⟨bs [0xca1c5,0x4a1e3,0x4a1ed,0x1ca1fb,0x6a207,0x1aa213] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block723 : PLift (G 41507 41549) := ⟨bs [0x4a223,0x6a229,0xea22f,0x2ca231,0x6a243,0xaa247] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block724 : PLift (G 41549 41611) := ⟨bs [0x6a24d,0x4a26b,0xaa279,0x4a27d,0x4a283,0x6a289] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block725 : PLift (G 41611 41651) := ⟨bs [0x4a28b,0xaa291,0x6a295,0x4a29b,0x1aa2a9,0x6a2af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block726 : PLift (G 41651 41729) := ⟨bs [0x4a2b3,0x6a2bb,0x4a2c5,0x6a2d1,0xaa2d7,0xca2f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block727 : PLift (G 41729 41801) := ⟨bs [0x6a301,0xaa309,0xea31f,0x26a321,0x4a32b,0x6a331] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block728 : PLift (G 41801 41863) := ⟨bs [0x6a349,0x2aa351,0x4a355,0x4a373,0x6a379,0x1ea37b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block729 : PLift (G 41863 41911) := ⟨bs [0x6a387,0x1aa397,0x6a39f,0x4a3a5,0x6a3a9,0xaa3af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block730 : PLift (G 41911 41959) := ⟨bs [0x6a3b7,0xaa3c7,0x4a3d5,0xaa3db,0xaa3e1,0x4a3e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block731 : PLift (G 41959 42017) := ⟨bs [0xca3e7,0x6a3f1,0x4a3fd,0xca3ff,0x16a40f,0xca41d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block732 : PLift (G 42017 42073) := ⟨bs [0x6a421,0x4a423,0xaa427,0xaa43b,0xca44d,0xea457] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block733 : PLift (G 42073 42157) := ⟨bs [0xaa459,0x4a463,0x6a469,0x4a475,0x4a493,0x4a49b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block734 : PLift (G 42157 42197) := ⟨bs [0x4a4ad,0x16a4b9,0x4a4c3,0x14a4c5,0x1aa4cb,0x1ea4d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block735 : PLift (G 42197 42257) := ⟨bs [0x4a4d5,0x6a4e1,0x4a4ed,0xaa4ef,0x4a4f3,0xea4ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block736 : PLift (G 42257 42323) := ⟨bs [0x6a511,0x16a529,0x4a52b,0x4a535,0x4a53b,0x6a543] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block737 : PLift (G 42323 42379) := ⟨bs [0x4a553,0x6a55b,0xaa561,0x4a56d,0xea577,0xaa585] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block738 : PLift (G 42379 42433) := ⟨bs [0x4a58b,0xca597,0x4a59d,0x4a5a3,0xaa5a7,0x1ca5a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block739 : PLift (G 42433 42463) := ⟨bs [0x14a5c1,0x4a5c5,0x4a5cb,0x6a5d3,0x16a5d9,0x4a5dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block740 : PLift (G 42463 42509) := ⟨bs [0x6a5df,0xaa5e3,0x6a5e9,0xaa5f7,0x4a5fb,0x4a603] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block741 : PLift (G 42509 42589) := ⟨bs [0x4a60d,0x4a625,0x4a63d,0x6a649,0x4a64b,0xea651] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block742 : PLift (G 42589 42677) := ⟨bs [0x4a65d,0x4a673,0x6a691,0x4a693,0x16a699,0xea6ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block743 : PLift (G 42677 42709) := ⟨bs [0x4a6b5,0x4a6bb,0x6a6c1,0xaa6c9,0x6a6cd,0xaa6cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block744 : PLift (G 42709 42767) := ⟨bs [0xca6d5,0x26a6df,0x6a6e7,0x6a6f1,0xea6f7,0xca6ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block745 : PLift (G 42767 42829) := ⟨bs [0xaa70f,0x6a715,0xaa723,0xaa729,0x4a72d,0x4a745] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block746 : PLift (G 42829 42899) := ⟨bs [0x4a74d,0x16a757,0x2ea759,0x4a765,0x14a76b,0xaa76f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block747 : PLift (G 42899 42953) := ⟨bs [0x4a793,0xca795,0x4a7ab,0x6a7b1,0xaa7b9,0x6a7bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block748 : PLift (G 42953 43013) := ⟨bs [0x6a7c9,0x16a7d1,0x6a7d7,0x6a7e3,0x4a7ed,0xaa7fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block749 : PLift (G 43013 43067) := ⟨bs [0x4a805,0x4a80b,0x4a81d,0x6a829,0x4a82b,0x6a837] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block750 : PLift (G 43067 43159) := ⟨bs [0x4a83b,0xaa855,0xaa85f,0x4a86d,0x4a87d,0x16a88f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block751 : PLift (G 43159 43237) := ⟨bs [0x6a897,0xaa8a9,0x4a8b5,0x2ea8c1,0x6a8c7,0xaa8d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block752 : PLift (G 43237 43319) := ⟨bs [0x4a8e5,0x4a8fd,0x1aa907,0x4a913,0x6a91b,0x6a931] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block753 : PLift (G 43319 43403) := ⟨bs [0x16a937,0x1aa939,0x4a943,0x22a97f,0x4a985,0x1aa987] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block754 : PLift (G 43403 43481) := ⟨bs [0x4a98b,0x6a993,0x4a9a3,0x16a9b1,0x4a9bb,0x6a9c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block755 : PLift (G 43481 43573) := ⟨bs [0xca9d9,0xaa9df,0x4a9eb,0x4a9fd,0x4aa15,0x6aa17] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block756 : PLift (G 43573 43609) := ⟨bs [0x4aa35,0x6aa39,0x4aa3b,0x16aa47,0x4aa4d,0xaaa57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block757 : PLift (G 43609 43661) := ⟨bs [0x1caa59,0x4aa5d,0x4aa6b,0xaaa71,0x6aa81,0x4aa83] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block758 : PLift (G 43661 43753) := ⟨bs [0x4aa8d,0x4aa95,0xcaaab,0x1aaabf,0xaaac5,0x6aac9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block759 : PLift (G 43753 43789) := ⟨bs [0xeaae9,0x6aaef,0xaab01,0x4ab05,0x6ab07,0x4ab0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block760 : PLift (G 43789 43891) := ⟨bs [0xcab0d,0x6ab11,0x3eab19,0x4ab4d,0x6ab5b,0x6ab71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block761 : PLift (G 43891 43963) := ⟨bs [0x6ab73,0x6ab89,0x4ab9d,0xaaba7,0xcabaf,0xcabb9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block762 : PLift (G 43963 44017) := ⟨bs [0x18abbb,0x16abc1,0x4abc5,0x4abd3,0x22abd7,0x4abdd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block763 : PLift (G 44017 44059) := ⟨bs [0x16abf1,0x4abf5,0x4abfb,0xcabfd,0x16ac09,0x4ac15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block764 : PLift (G 44059 44119) := ⟨bs [0x4ac1b,0x6ac27,0xaac37,0x1aac39,0xcac45,0xeac4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block765 : PLift (G 44119 44179) := ⟨bs [0xcac57,0x4ac5b,0x6ac61,0x4ac63,0x16ac7f,0x4ac8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block766 : PLift (G 44179 44249) := ⟨bs [0x4ac93,0x4ac9d,0xcaca9,0xaacab,0xaacaf,0x4acbd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block767 : PLift (G 44249 44279) := ⟨bs [0x6acd9,0xaace1,0x6ace7,0x4aceb,0x4aced,0x6acf1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block768 : PLift (G 44279 44381) := ⟨bs [0xeacf7,0xeacf9,0x4ad05,0x26ad3f,0x4ad45,0x4ad53] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block769 : PLift (G 44381 44483) := ⟨bs [0x4ad5d,0x6ad5f,0x4ad65,0x6ad81,0x1aada1,0x4ada5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block770 : PLift (G 44483 44531) := ⟨bs [0x4adc3,0x1aadcb,0xaadd1,0x4add5,0x4addb,0x1aade7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block771 : PLift (G 44531 44579) := ⟨bs [0x4adf3,0x4adf5,0x6adf9,0xaadff,0x4ae05,0x6ae13] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block772 : PLift (G 44579 44641) := ⟨bs [0x4ae23,0x6ae2b,0xaae49,0x4ae4d,0xaae4f,0x6ae59] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block773 : PLift (G 44641 44699) := ⟨bs [0x26ae61,0xaae67,0x4ae6b,0x6ae71,0x4ae8b,0xaae8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block774 : PLift (G 44699 44771) := ⟨bs [0x4ae9b,0x4ae9d,0xeaea7,0x6aeb9,0x4aec5,0x6aed1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block775 : PLift (G 44771 44819) := ⟨bs [0xcaee3,0xaaee5,0x6aee9,0x4aef5,0x4aefd,0x16af09] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block776 : PLift (G 44819 44887) := ⟨bs [0x4af13,0xcaf27,0xaaf2b,0x14af33,0x4af43,0xeaf4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block777 : PLift (G 44887 44953) := ⟨bs [0xaaf57,0xaaf5d,0x4af6d,0xaaf75,0xeaf7f,0x4af8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block778 : PLift (G 44953 45007) := ⟨bs [0xaaf99,0x6af9f,0x4afa3,0x6afab,0x6afb7,0x4afbb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block779 : PLift (G 45007 45119) := ⟨bs [0x6afcf,0x4afd5,0x4affd,0x4b005,0x4b015,0x4b01b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block780 : PLift (G 45119 45161) := ⟨bs [0xeb03f,0xeb041,0x18b047,0x4b04b,0x6b051,0x4b053] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block781 : PLift (G 45161 45247) := ⟨bs [0x6b069,0xcb07b,0x4b07d,0x16b087,0x4b08d,0x6b0b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block782 : PLift (G 45247 45307) := ⟨bs [0xab0bf,0x6b0cb,0xab0cf,0x6b0e1,0x1cb0e9,0x4b0ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block783 : PLift (G 45307 45343) := ⟨bs [0x4b0fb,0x4b105,0x6b107,0x6b111,0xab119,0x4b11d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block784 : PLift (G 45343 45427) := ⟨bs [0xcb11f,0x16b131,0x6b141,0x4b14d,0x6b15b,0x4b165] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block785 : PLift (G 45427 45503) := ⟨bs [0x6b173,0xeb179,0x6b17f,0x1ab1a9,0x4b1b3,0x6b1b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block786 : PLift (G 45503 45569) := ⟨bs [0xab1bf,0x4b1d3,0x4b1dd,0x14b1e5,0xab1f1,0x6b1f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block787 : PLift (G 45569 45641) := ⟨bs [0x6b201,0x4b213,0x4b215,0xeb21f,0x4b22d,0x18b23f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block788 : PLift (G 45641 45697) := ⟨bs [0x16b249,0x4b25b,0x4b263,0xab269,0x4b26d,0xeb27b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block789 : PLift (G 45697 45767) := ⟨bs [0x14b281,0x4b28b,0x6b2a9,0x6b2b7,0x4b2bd,0xab2c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block790 : PLift (G 45767 45833) := ⟨bs [0xab2c7,0x4b2d3,0xab2f9,0x4b2fd,0x6b2ff,0x4b303] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block791 : PLift (G 45833 45893) := ⟨bs [0xab309,0xeb311,0xab31d,0x14b327,0x4b32d,0xab33f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block792 : PLift (G 45893 45979) := ⟨bs [0x4b345,0xcb377,0x4b37d,0x6b381,0xeb387,0x4b393] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block793 : PLift (G 45979 46061) := ⟨bs [0x4b39b,0x4b3a5,0x4b3c5,0x4b3cb,0x6b3e1,0x6b3e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block794 : PLift (G 46061 46133) := ⟨bs [0x4b3ed,0xab3f9,0x4b40b,0x4b40d,0x4b413,0x14b417] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block795 : PLift (G 46133 46183) := ⟨bs [0x4b435,0x14b43d,0x4b443,0xab449,0x6b45b,0x4b465] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block796 : PLift (G 46183 46261) := ⟨bs [0x6b467,0x4b46b,0x22b477,0x6b48b,0x4b495,0x4b49d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block797 : PLift (G 46261 46309) := ⟨bs [0x4b4b5,0xeb4bf,0xab4c1,0x6b4c7,0x4b4dd,0x4b4e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block798 : PLift (G 46309 46399) := ⟨bs [0x4b4e5,0x6b4f7,0x6b501,0x4b50d,0x6b50f,0xeb52d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block799 : PLift (G 46399 46457) := ⟨bs [0x6b53f,0x6b54b,0xeb567,0xeb569,0x6b56f,0xcb573] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block800 : PLift (G 46457 46511) := ⟨bs [0x6b579,0x6b587,0x4b58d,0x3ab599,0x4b5a3,0x4b5ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block801 : PLift (G 46511 46589) := ⟨bs [0x16b5af,0xab5bb,0x4b5d5,0xeb5df,0x6b5e7,0x4b5ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block802 : PLift (G 46589 46643) := ⟨bs [0x4b5fd,0xcb5ff,0x6b609,0xcb61b,0xab629,0xcb62f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block803 : PLift (G 46643 46691) := ⟨bs [0x4b633,0x1eb639,0xab647,0x22b657,0x16b659,0x6b65f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block804 : PLift (G 46691 46757) := ⟨bs [0x4b663,0xab66f,0x4b683,0xab687,0x4b69b,0x16b69f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block805 : PLift (G 46757 46819) := ⟨bs [0x4b6a5,0x6b6b1,0x4b6b3,0x6b6d7,0x4b6db,0x6b6e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block806 : PLift (G 46819 46877) := ⟨bs [0x4b6e3,0x4b6ed,0x6b6ef,0x4b705,0xcb70d,0x4b713] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block807 : PLift (G 46877 46993) := ⟨bs [0x4b71d,0x6b729,0x16b735,0x16b747,0x4b755,0xab76d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block808 : PLift (G 46993 47059) := ⟨bs [0xab791,0x4b795,0xeb7a9,0x3ab7c1,0x4b7cb,0x6b7d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block809 : PLift (G 47059 47129) := ⟨bs [0x4b7d3,0xab7ef,0x4b7f5,0xeb807,0x6b80f,0x4b813] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block810 : PLift (G 47129 47189) := ⟨bs [0x6b819,0xab821,0xcb827,0x4b82b,0x4b82d,0x22b839] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block811 : PLift (G 47189 47279) := ⟨bs [0x4b855,0xab867,0xcb875,0x4b885,0x14b893,0xcb8a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block812 : PLift (G 47279 47317) := ⟨bs [0xeb8af,0xab8b7,0xcb8bd,0x6b8c1,0xab8c7,0x4b8cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block813 : PLift (G 47317 47387) := ⟨bs [0xcb8d5,0x4b8eb,0x1ab8f7,0xab8f9,0x4b903,0x4b915] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block814 : PLift (G 47387 47441) := ⟨bs [0x4b91b,0x4b91d,0x6b92f,0x6b939,0x4b93b,0x18b947] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block815 : PLift (G 47441 47513) := ⟨bs [0x6b951,0x4b963,0x4b983,0xab989,0x6b98d,0x4b993] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block816 : PLift (G 47513 47569) := ⟨bs [0x6b999,0x22b9a1,0x6b9a7,0x4b9ad,0xab9b7,0x4b9cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block817 : PLift (G 47569 47629) := ⟨bs [0x22b9d1,0x4b9dd,0x16b9e7,0x6b9ef,0xcb9f9,0x6ba07] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block818 : PLift (G 47629 47699) := ⟨bs [0x14ba0d,0xeba17,0x1aba25,0x6ba29,0x4ba2b,0x6ba41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block819 : PLift (G 47699 47741) := ⟨bs [0x4ba53,0x4ba55,0x16ba5f,0x14ba61,0x4ba65,0xaba79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block820 : PLift (G 47741 47807) := ⟨bs [0x6ba7d,0x6ba7f,0x6baa1,0x6baa3,0xebaaf,0xabab5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block821 : PLift (G 47807 47869) := ⟨bs [0xababf,0xebac1,0x4bacb,0x4badd,0x4bae3,0xebaf1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block822 : PLift (G 47869 47939) := ⟨bs [0x4bafd,0x3abb09,0xebb1f,0x6bb27,0xabb2d,0x4bb3d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block823 : PLift (G 47939 47981) := ⟨bs [0x4bb43,0x4bb4b,0xebb4f,0x4bb5b,0x6bb61,0xebb69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block824 : PLift (G 47981 48079) := ⟨bs [0x4bb6d,0x6bb91,0xabb97,0x4bb9d,0x22bbb1,0xabbc9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block825 : PLift (G 48079 48157) := ⟨bs [0xcbbcf,0xebbdb,0x4bbed,0xebbf7,0x1abbf9,0xcbc03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block826 : PLift (G 48157 48221) := ⟨bs [0xabc1d,0x6bc23,0xcbc33,0x4bc3b,0xebc41,0x4bc45] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block827 : PLift (G 48221 48299) := ⟨bs [0x4bc5d,0xebc6f,0x6bc77,0x4bc83,0xcbc8f,0x6bc99] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block828 : PLift (G 48299 48371) := ⟨bs [0x4bcab,0xebcb7,0xabcb9,0x14bcd1,0x6bcd5,0x6bce1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block829 : PLift (G 48371 48437) := ⟨bs [0x4bcf3,0xabcff,0xabd0d,0xabd17,0x22bd19,0x4bd1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block830 : PLift (G 48437 48487) := ⟨bs [0x4bd35,0x6bd41,0xabd4f,0x6bd59,0xebd5f,0x22bd61] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block831 : PLift (G 48487 48539) := ⟨bs [0xabd67,0x4bd6b,0x6bd71,0x6bd8b,0xabd8f,0x4bd95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block832 : PLift (G 48539 48611) := ⟨bs [0x4bd9b,0x4bd9d,0x4bdb3,0x4bdbb,0x14bdcd,0x6bdd1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block833 : PLift (G 48611 48673) := ⟨bs [0x4bde3,0x4bdeb,0xabdef,0xabe07,0xebe09,0x4be15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block834 : PLift (G 48673 48757) := ⟨bs [0x1ebe21,0x4be25,0x6be27,0xcbe5b,0x4be5d,0x6be6f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block835 : PLift (G 48757 48799) := ⟨bs [0x4be75,0x6be79,0xabe7f,0x4be8b,0xcbe8d,0x4be93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block836 : PLift (G 48799 48857) := ⟨bs [0x6be9f,0x6bea9,0xabeb1,0x4beb5,0xabeb7,0x6becf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block837 : PLift (G 48857 48907) := ⟨bs [0x6bed9,0x4bedb,0x4bee5,0x6bee7,0x4bef3,0x44bef9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block838 : PLift (G 48907 49003) := ⟨bs [0x4bf0b,0x4bf33,0x6bf39,0xabf4d,0x4bf5d,0xcbf5f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block839 : PLift (G 49003 49043) := ⟨bs [0x1abf6b,0x26bf71,0x4bf7b,0x1abf87,0x14bf89,0x4bf8d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block840 : PLift (G 49043 49117) := ⟨bs [0x4bf93,0xabfa1,0x4bfad,0x16bfb9,0xabfcf,0x4bfd5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block841 : PLift (G 49117 49171) := ⟨bs [0x4bfdd,0x6bfe1,0x4bfe3,0x4bff3,0x4c005,0x6c011] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block842 : PLift (G 49171 49211) := ⟨bs [0x4c013,0xac019,0x6c029,0x1ac02f,0xec031,0x6c037] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block843 : PLift (G 49211 49297) := ⟨bs [0x4c03b,0xac047,0x4c065,0x4c06d,0x4c07d,0x6c07f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block844 : PLift (G 49297 49367) := ⟨bs [0xac091,0x4c09b,0x4c0b3,0x4c0b5,0x16c0bb,0x4c0d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block845 : PLift (G 49367 49417) := ⟨bs [0xac0d7,0x1ac0d9,0x16c0ef,0xac0f1,0x6c101,0x4c103] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block846 : PLift (G 49417 49477) := ⟨bs [0xac109,0x4c115,0x6c119,0x14c12b,0x6c133,0xac137] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block847 : PLift (G 49477 49537) := ⟨bs [0x16c145,0x6c149,0x4c15b,0x4c173,0x6c179,0x14c17b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block848 : PLift (G 49537 49613) := ⟨bs [0x14c181,0x4c18b,0xcc18d,0x16c197,0xac1bd,0x6c1c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block849 : PLift (G 49613 49669) := ⟨bs [0x4c1cd,0x6c1db,0xac1e1,0x6c1e7,0x6c1ff,0x4c203] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block850 : PLift (G 49669 49741) := ⟨bs [0x4c205,0x22c211,0x6c221,0xec22f,0xac23f,0x4c24b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block851 : PLift (G 49741 49801) := ⟨bs [0x4c24d,0x6c253,0x4c25d,0x6c277,0x4c27b,0xcc27d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block852 : PLift (G 49801 49853) := ⟨bs [0x1ac289,0x6c28f,0xcc293,0xac29f,0x18c2a7,0x4c2b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block853 : PLift (G 49853 49927) := ⟨bs [0x4c2bd,0x22c2cf,0x4c2d5,0x4c2e3,0xec2ff,0x2ec301] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block854 : PLift (G 49927 49993) := ⟨bs [0x6c307,0x6c311,0xec313,0xac317,0xac325,0xec347] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block855 : PLift (G 49993 50051) := ⟨bs [0xac349,0x6c34f,0x4c365,0x6c367,0xac371,0xcc37f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block856 : PLift (G 50051 50101) := ⟨bs [0x4c383,0x4c385,0x4c395,0x4c39d,0xac3a7,0x4c3ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block857 : PLift (G 50101 50147) := ⟨bs [0x4c3b5,0x22c3bf,0x6c3c7,0x4c3cb,0x6c3d1,0x4c3d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block858 : PLift (G 50147 50227) := ⟨bs [0x4c3e3,0x6c3e9,0xec3ef,0x6c401,0xac41f,0x1ac42d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block859 : PLift (G 50227 50291) := ⟨bs [0x4c433,0x16c437,0x6c455,0x6c457,0x6c461,0x6c46f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block860 : PLift (G 50291 50359) := ⟨bs [0x4c473,0x6c487,0xcc491,0xec499,0x4c49d,0x4c4a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block861 : PLift (G 50359 50417) := ⟨bs [0x6c4b7,0x4c4bb,0xac4c9,0x6c4cf,0x4c4d3,0x4c4eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block862 : PLift (G 50417 50503) := ⟨bs [0x6c4f1,0xac4f7,0xcc509,0x4c51b,0xec51d,0xac541] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block863 : PLift (G 50503 50551) := ⟨bs [0xac547,0x6c551,0x6c55f,0x4c56b,0xac56f,0x4c575] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block864 : PLift (G 50551 50627) := ⟨bs [0x6c577,0x4c595,0x1cc59b,0xec59f,0xac5a1,0x6c5a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block865 : PLift (G 50627 50723) := ⟨bs [0x4c5c3,0x6c5d7,0x4c5db,0x16c5ef,0x4c5fb,0x6c613] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block866 : PLift (G 50723 50789) := ⟨bs [0x4c623,0x4c635,0x6c641,0xac64f,0x16c655,0x6c659] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block867 : PLift (G 50789 50867) := ⟨bs [0x4c665,0x4c685,0xec691,0x6c697,0x6c6a1,0x26c6a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block868 : PLift (G 50867 50929) := ⟨bs [0x4c6b3,0x6c6b9,0x4c6cb,0x4c6cd,0x4c6dd,0x4c6eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block869 : PLift (G 50929 50993) := ⟨bs [0x16c6f1,0x2ec707,0x4c70d,0x6c719,0x4c71b,0x4c72d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block870 : PLift (G 50993 51061) := ⟨bs [0x6c731,0xec739,0x6c757,0x4c763,0xac767,0x4c773] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block871 : PLift (G 51061 51151) := ⟨bs [0x4c775,0x16c77f,0x14c7a5,0xcc7bb,0x4c7bd,0x6c7c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block872 : PLift (G 51151 51203) := ⟨bs [0x6c7cf,0xac7d5,0x1cc7e1,0xac7f9,0x4c7fd,0x18c7ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block873 : PLift (G 51203 51263) := ⟨bs [0x4c803,0xac811,0x4c81d,0x2ec827,0x22c829,0x6c839] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block874 : PLift (G 51263 51343) := ⟨bs [0xac83f,0x4c853,0xac857,0xac86b,0x6c881,0x4c88d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block875 : PLift (G 51343 51413) := ⟨bs [0xac88f,0x4c893,0x14c895,0x4ac8a1,0xac8b7,0xac8cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block876 : PLift (G 51413 51439) := ⟨bs [0x4c8d5,0x4c8db,0x4c8dd,0x4c8e3,0xec8e7,0x4c8ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block877 : PLift (G 51439 51487) := ⟨bs [0x6c8ef,0x6c8f9,0x4c905,0x6c911,0xec917,0x22c919] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block878 : PLift (G 51487 51551) := ⟨bs [0x6c91f,0xac92f,0xcc937,0xcc93d,0x6c941,0x4c953] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block879 : PLift (G 51551 51607) := ⟨bs [0x16c95f,0x4c96b,0x14c979,0x4c97d,0x6c989,0xec98f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block880 : PLift (G 51607 51673) := ⟨bs [0x6c997,0x4c99d,0x1ec9af,0xac9b5,0xec9bf,0x4c9cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block881 : PLift (G 51673 51721) := ⟨bs [0xec9d9,0xcc9df,0x4c9e3,0x14c9eb,0x6ca01,0x1aca07] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block882 : PLift (G 51721 51803) := ⟨bs [0xeca09,0x4ca25,0xaca37,0x26ca39,0x6ca4b,0x6ca55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block883 : PLift (G 51803 51859) := ⟨bs [0x4ca5b,0x14ca69,0x4ca73,0x4ca75,0xeca7f,0x16ca8d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block884 : PLift (G 51859 51913) := ⟨bs [0x6ca93,0x4ca9d,0xeca9f,0x4cab5,0x4cabb,0x16cac3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block885 : PLift (G 51913 51977) := ⟨bs [0x14cac9,0x6cad9,0x6cae5,0x4caed,0x4cb03,0x4cb05] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block886 : PLift (G 51977 52057) := ⟨bs [0x6cb09,0xecb17,0x22cb29,0x4cb35,0x4cb3b,0x4cb53] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block887 : PLift (G 52057 52127) := ⟨bs [0xecb59,0x4cb63,0x4cb65,0x22cb71,0xacb87,0x6cb99] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block888 : PLift (G 52127 52183) := ⟨bs [0xacb9f,0x4cbb3,0xacbb9,0x4cbc3,0xacbd1,0x6cbd5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block889 : PLift (G 52183 52253) := ⟨bs [0x6cbd7,0x1acbdd,0x22cbe9,0xacbff,0xccc0d,0x1acc19] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block890 : PLift (G 52253 52313) := ⟨bs [0x4cc1d,0x4cc23,0x4cc2b,0x6cc41,0xecc43,0x4cc4d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block891 : PLift (G 52313 52387) := ⟨bs [0x6cc59,0x22cc61,0xccc89,0xacc8b,0x1acc91,0x4cc9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block892 : PLift (G 52387 52501) := ⟨bs [0x4cca3,0x16cca7,0x6ccd1,0x4cce5,0x6cce9,0xecd09] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block893 : PLift (G 52501 52553) := ⟨bs [0x14cd15,0xecd1f,0x4cd25,0x6cd31,0x4cd3d,0x6cd3f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block894 : PLift (G 52553 52609) := ⟨bs [0x6cd49,0xecd51,0x6cd57,0x4cd5b,0x4cd63,0xacd67] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block895 : PLift (G 52609 52691) := ⟨bs [0x16cd81,0x6cd93,0x1acd97,0x6cd9f,0x4cdbb,0x6cdc1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block896 : PLift (G 52691 52733) := ⟨bs [0x4cdd3,0x6cdd9,0x4cde5,0x2ecde7,0x6cdf1,0xacdf7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block897 : PLift (G 52733 52813) := ⟨bs [0x4cdfd,0x6ce0b,0x4ce15,0x6ce21,0xace2f,0xace47] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block898 : PLift (G 52813 52883) := ⟨bs [0x4ce4d,0x6ce51,0x4ce65,0xcce7b,0x16ce7d,0x6ce8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block899 : PLift (G 52883 52951) := ⟨bs [0x4ce93,0x6ce99,0x6cea5,0x6cea7,0x16ceb7,0xacec9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block900 : PLift (G 52951 52999) := ⟨bs [0x6ced7,0xacedd,0x6cee3,0xacee7,0x4ceed,0x4cef5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block901 : PLift (G 52999 53077) := ⟨bs [0x6cf07,0x4cf0b,0xacf19,0x6cf37,0xccf3b,0x4cf4d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block902 : PLift (G 53077 53117) := ⟨bs [0x4cf55,0xacf5f,0x3ecf61,0x4cf65,0x4cf6d,0xacf79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block903 : PLift (G 53117 53173) := ⟨bs [0x4cf7d,0x6cf89,0x4cf9b,0xccf9d,0x1ccfa9,0x4cfb3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block904 : PLift (G 53173 53239) := ⟨bs [0x24cfb5,0x4cfc5,0x4cfcd,0x6cfd1,0x2ecfef,0xacff1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block905 : PLift (G 53239 53309) := ⟨bs [0x6cff7,0x4d013,0xed015,0xed01f,0x16d021,0x4d033] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block906 : PLift (G 53309 53381) := ⟨bs [0x4d03d,0x4d04b,0xad04f,0xed069,0x6d06f,0xad081] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block907 : PLift (G 53381 53441) := ⟨bs [0x4d085,0xed099,0xad09f,0x4d0a3,0x4d0ab,0x4d0bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block908 : PLift (G 53441 53549) := ⟨bs [0x6d0c1,0x4d0cd,0x6d0e7,0x6d0ff,0x4d103,0x6d117] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block909 : PLift (G 53549 53609) := ⟨bs [0x4d12d,0x6d12f,0x26d141,0x1ad157,0xad159,0x4d15d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block910 : PLift (G 53609 53639) := ⟨bs [0x6d169,0x14d16b,0xad171,0x6d177,0xcd17d,0x6d181] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block911 : PLift (G 53639 53717) := ⟨bs [0x16d187,0x4d195,0x6d199,0x6d1b1,0x4d1bd,0x4d1c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block912 : PLift (G 53717 53783) := ⟨bs [0x4d1d5,0xcd1d7,0x18d1e3,0x22d1ff,0x4d20d,0x6d211] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block913 : PLift (G 53783 53857) := ⟨bs [0xad217,0xcd21f,0x4d235,0x4d23b,0xed247,0x6d259] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block914 : PLift (G 53857 53899) := ⟨bs [0xad261,0x4d265,0x3ed279,0x6d27f,0x4d283,0x6d289] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block915 : PLift (G 53899 53959) := ⟨bs [0x4d28b,0x4d29d,0xad2a3,0xad2a7,0x4d2b3,0xed2bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block916 : PLift (G 53959 54037) := ⟨bs [0x6d2c7,0x4d2e3,0x6d2e9,0x16d2f1,0x4d2fb,0xad2fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block917 : PLift (G 54037 54121) := ⟨bs [0x4d315,0x16d321,0x4d32b,0x4d343,0x6d34b,0x6d355] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block918 : PLift (G 54121 54181) := ⟨bs [0x1ad369,0xad375,0x4d37b,0xcd387,0x4d393,0xad397] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block919 : PLift (G 54181 54287) := ⟨bs [0x4d3a5,0x14d3b1,0xad3c9,0x4d3eb,0x4d3fd,0xad405] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block920 : PLift (G 54287 54347) := ⟨bs [0xad40f,0x4d415,0x16d427,0x6d42f,0x4d433,0x4d43b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block921 : PLift (G 54347 54403) := ⟨bs [0x4d44b,0xed459,0xad45f,0xcd463,0xad469,0x6d481] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block922 : PLift (G 54403 54443) := ⟨bs [0x4d483,0xed489,0x4d48d,0x4d493,0x4d495,0x4d4a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block923 : PLift (G 54443 54503) := ⟨bs [0x4d4ab,0x6d4b1,0x4d4c5,0x4d4dd,0x6d4e1,0x6d4e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block924 : PLift (G 54503 54559) := ⟨bs [0xed4e7,0xad4f5,0x6d4f9,0x4d50b,0x4d50d,0x6d513] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block925 : PLift (G 54559 54617) := ⟨bs [0x6d51f,0x4d523,0xad531,0x14d535,0xad537,0x2cd549] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block926 : PLift (G 54617 54673) := ⟨bs [0x6d559,0xad55f,0x6d565,0xcd567,0xad577,0x4d58b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block927 : PLift (G 54673 54751) := ⟨bs [0xad591,0xed597,0x4d5b5,0xad5b9,0x16d5c1,0x6d5c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block928 : PLift (G 54751 54829) := ⟨bs [0xcd5df,0xad5ef,0x4d5f5,0x4d5fb,0x4d603,0x6d60f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block929 : PLift (G 54829 54907) := ⟨bs [0x4d62d,0x6d631,0xcd643,0x4d655,0x4d65d,0x6d661] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block930 : PLift (G 54907 54973) := ⟨bs [0x4d67b,0x4d685,0x6d687,0x4d69d,0x4d6a5,0xed6af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block931 : PLift (G 54973 55049) := ⟨bs [0x1cd6bd,0x6d6c3,0xad6c7,0x6d6d9,0xed6e1,0xcd6ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block932 : PLift (G 55049 55103) := ⟨bs [0xcd709,0x4d70b,0x14d711,0x4d715,0x6d721,0x1ad727] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block933 : PLift (G 55103 55171) := ⟨bs [0xad73f,0x4d745,0xad74d,0xad757,0xad76b,0x4d77b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block934 : PLift (G 55171 55229) := ⟨bs [0x14d783,0xed7a1,0xad7a7,0x4d7ad,0x6d7b1,0x4d7b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block935 : PLift (G 55229 55331) := ⟨bs [0x4d7bd,0x4d7cb,0x16d7d1,0xcd7db,0x16d7fb,0x6d811] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block936 : PLift (G 55331 55373) := ⟨bs [0x4d823,0xcd825,0x6d829,0x4d82b,0xed82f,0xed837] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block937 : PLift (G 55373 55457) := ⟨bs [0x4d84d,0xcd855,0xcd867,0x4d873,0x1ad88f,0x4cd891] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block938 : PLift (G 55457 55541) := ⟨bs [0x6d8a1,0x4d8ad,0xad8bf,0xcd8cd,0x16d8d7,0x6d8e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block939 : PLift (G 55541 55619) := ⟨bs [0x4d8f5,0x4d8fb,0x4d91b,0x4d925,0x4d933,0x1ad939] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block940 : PLift (G 55619 55663) := ⟨bs [0x4d943,0x4d945,0xed94f,0xad951,0x6d957,0x4d96d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block941 : PLift (G 55663 55711) := ⟨bs [0x6d96f,0x4d973,0x6d979,0x16d981,0x4d98b,0x6d991] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block942 : PLift (G 55711 55793) := ⟨bs [0x6d99f,0x4d9a5,0x6d9a9,0x4d9b5,0x4d9d3,0x4d9eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block943 : PLift (G 55793 55823) := ⟨bs [0x6d9f1,0xed9f7,0x6d9ff,0x4da05,0x6da09,0x4da0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block944 : PLift (G 55823 55889) := ⟨bs [0xada0f,0x4da15,0xada1d,0x4da23,0x1cda29,0xeda3f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block945 : PLift (G 55889 55931) := ⟨bs [0x6da51,0xada59,0x4da5d,0x16da5f,0x2ada71,0x6da77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block946 : PLift (G 55931 56003) := ⟨bs [0xcda7b,0x4da7d,0x4da8d,0xada9f,0x4dab3,0x4dabd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block947 : PLift (G 56003 56087) := ⟨bs [0x4dac3,0x6dac9,0xedae7,0xedae9,0x4daf5,0x6db11] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block948 : PLift (G 56087 56131) := ⟨bs [0xadb17,0x4db1d,0x4db23,0xedb25,0xadb31,0x4db3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block949 : PLift (G 56131 56207) := ⟨bs [0x4db43,0xcdb55,0x6db67,0x4db6b,0x6db73,0x1adb85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block950 : PLift (G 56207 56267) := ⟨bs [0xadb8f,0xedb91,0x4dbad,0x6dbaf,0x6dbb9,0x6dbc7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block951 : PLift (G 56267 56369) := ⟨bs [0x4dbcb,0x4dbcd,0x14dbeb,0xcdbf7,0x4dc0d,0x6dc27] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block952 : PLift (G 56369 56431) := ⟨bs [0x6dc31,0xadc39,0x6dc3f,0x6dc49,0x1adc51,0x6dc61] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block953 : PLift (G 56431 56477) := ⟨bs [0x6dc6f,0x4dc75,0xadc7b,0x4dc85,0x4dc93,0xadc99] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block954 : PLift (G 56477 56519) := ⟨bs [0x4dc9d,0xcdc9f,0x6dca9,0x6dcb5,0x6dcb7,0x4dcbd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block955 : PLift (G 56519 56591) := ⟨bs [0x1adcc7,0x6dccf,0x4dcd3,0xadcd5,0xadcdf,0x16dcf9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block956 : PLift (G 56591 56659) := ⟨bs [0x26dd0f,0x4dd15,0x6dd17,0x34dd23,0x4dd35,0x6dd39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block957 : PLift (G 56659 56711) := ⟨bs [0x4dd53,0xadd57,0x6dd5f,0x6dd69,0xadd6f,0x4dd7d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block958 : PLift (G 56711 56773) := ⟨bs [0xedd87,0xadd89,0x4dd9b,0x14dda1,0x4ddab,0x6ddbf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block959 : PLift (G 56773 56821) := ⟨bs [0x4ddc5,0x4ddcb,0xaddcf,0xadde7,0x22dde9,0x6dded] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block960 : PLift (G 56821 56893) := ⟨bs [0xcddf5,0x4ddfb,0x4de0b,0xede19,0x6de29,0x4de3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block961 : PLift (G 56893 56929) := ⟨bs [0x4de3d,0xade41,0x4de4d,0x6de4f,0x6de59,0x6de5b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block962 : PLift (G 56929 56989) := ⟨bs [0x1cde61,0x4de6d,0x1ade77,0x4de7d,0x4de83,0x6de97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block963 : PLift (G 56989 57059) := ⟨bs [0xcde9d,0x6dea1,0x1adea7,0xadecd,0x16ded1,0xeded7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block964 : PLift (G 57059 57119) := ⟨bs [0x4dee3,0xadef1,0x4def5,0x6df01,0xedf09,0x4df13] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block965 : PLift (G 57119 57173) := ⟨bs [0x26df1f,0x4df2b,0x4df33,0xadf37,0x4df3d,0x4df4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block966 : PLift (G 57173 57223) := ⟨bs [0x4df55,0x4df5b,0xedf67,0xadf69,0x4df73,0x4df85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block967 : PLift (G 57223 57283) := ⟨bs [0x6df87,0x16df99,0x4dfa3,0x4dfab,0x4dfb5,0x6dfb7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block968 : PLift (G 57283 57349) := ⟨bs [0x4dfc3,0xadfc7,0xcdfd5,0x6dff1,0x4dff3,0x4e003] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block969 : PLift (G 57349 57413) := ⟨bs [0x4e005,0x6e017,0x4e01d,0xae027,0x4e02d,0x4e035] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block970 : PLift (G 57413 57503) := ⟨bs [0x4e045,0x4e053,0xae071,0x4e07b,0xce08f,0xae095] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block971 : PLift (G 57503 57587) := ⟨bs [0xae09f,0xae0b7,0xee0b9,0x4e0d5,0xce0d7,0x1ae0e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block972 : PLift (G 57587 57653) := ⟨bs [0x4e0f3,0x6e0f9,0xee101,0x4e125,0x6e129,0x1ae131] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block973 : PLift (G 57653 57713) := ⟨bs [0x4e135,0x6e143,0x6e14f,0x6e159,0xae161,0x4e16d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block974 : PLift (G 57713 57773) := ⟨bs [0x6e171,0xee177,0x6e17f,0x4e183,0x6e189,0xce197] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block975 : PLift (G 57773 57809) := ⟨bs [0x6e1ad,0xce1b5,0x4e1bb,0x34e1bf,0xae1c1,0x4e1cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block976 : PLift (G 57809 57881) := ⟨bs [0x6e1d1,0x14e1e5,0x16e1ef,0x6e1f7,0xae1fd,0x4e203] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block977 : PLift (G 57881 57947) := ⟨bs [0x6e219,0x4e22b,0x4e22d,0x4e23d,0x4e243,0xae257] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block978 : PLift (G 57947 58031) := ⟨bs [0xae25b,0xae275,0x6e279,0xce287,0x4e29d,0x4e2ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block979 : PLift (G 58031 58073) := ⟨bs [0xee2af,0x4e2bb,0x6e2c1,0xee2c9,0x6e2cd,0x4e2d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block980 : PLift (G 58073 58151) := ⟨bs [0xae2d9,0x14e2f3,0x4e2fd,0x18e2ff,0x1ae311,0x6e323] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block981 : PLift (G 58151 58199) := ⟨bs [0xee327,0x14e329,0xce339,0x4e33b,0xce34d,0x6e351] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block982 : PLift (G 58199 58237) := ⟨bs [0xee357,0xae35f,0x4e363,0x6e369,0x4e375,0xce377] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block983 : PLift (G 58237 58337) := ⟨bs [0x1ee37d,0x4e383,0x16e39f,0xce3c5,0x6e3c9,0x16e3d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block984 : PLift (G 58337 58393) := ⟨bs [0x6e3e1,0x4e3fb,0xee3ff,0xee401,0x4e40b,0x16e417] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block985 : PLift (G 58393 58441) := ⟨bs [0xae419,0x4e423,0x4e42b,0xae431,0x4e43b,0x22e447] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block986 : PLift (G 58441 58537) := ⟨bs [0x1ae449,0x14e453,0x4e455,0xae46d,0xce471,0x1ae48f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block987 : PLift (G 58537 58601) := ⟨bs [0xee4a9,0xce4af,0x4e4b5,0xce4c7,0x4e4cd,0x4e4d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block988 : PLift (G 58601 58679) := ⟨bs [0x6e4e9,0x4e4eb,0x4e4f5,0x26e507,0xae521,0x4e525] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block989 : PLift (G 58679 58733) := ⟨bs [0x16e537,0xce53f,0x4e545,0x4e54b,0xce557,0xae567] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block990 : PLift (G 58733 58789) := ⟨bs [0x4e56d,0x4e575,0x4e585,0x4e58b,0x16e593,0x4e5a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block991 : PLift (G 58789 58909) := ⟨bs [0x4e5a5,0x16e5cf,0x6e609,0xae611,0x4e615,0x4e61b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block992 : PLift (G 58909 58967) := ⟨bs [0x4e61d,0x6e621,0x1ae629,0x6e639,0xae63f,0x6e653] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block993 : PLift (G 58967 59021) := ⟨bs [0xae657,0x4e663,0xee66f,0x6e675,0x6e681,0x4e683] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block994 : PLift (G 59021 59069) := ⟨bs [0x4e68d,0xae68f,0x4e695,0x14e6ab,0x1ee6ad,0xae6b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block995 : PLift (G 59069 59119) := ⟨bs [0x4e6bd,0xae6c5,0x4e6cb,0x6e6d5,0x4e6e3,0xee6e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block996 : PLift (G 59119 59183) := ⟨bs [0x6e6ef,0x4e6f3,0x6e705,0x4e70d,0xee717,0x6e71f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block997 : PLift (G 59183 59233) := ⟨bs [0xae72f,0x4e73d,0xae747,0x16e749,0x4e753,0x4e755] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block998 : PLift (G 59233 59333) := ⟨bs [0xae761,0x6e767,0x4e76b,0x6e77f,0x6e789,0xee791] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block999 : PLift (G 59333 59377) := ⟨bs [0x4e7c5,0x1ce7cd,0x1ae7d7,0x4e7dd,0xce7df,0x6e7e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1000 : PLift (G 59377 59419) := ⟨bs [0xae7f1,0x4e7fb,0xae801,0xee807,0x6e80f,0x6e819] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1001 : PLift (G 59419 59471) := ⟨bs [0x4e81b,0x6e831,0x4e833,0xae837,0x4e83d,0x4e84b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1002 : PLift (G 59471 59557) := ⟨bs [0x16e84f,0x14e851,0x1ee869,0x14e875,0x6e879,0x4e893] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1003 : PLift (G 59557 59621) := ⟨bs [0x4e8a5,0x6e8a9,0xae8af,0xce8bd,0x4e8db,0xee8e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1004 : PLift (G 59621 59669) := ⟨bs [0x6e8e5,0x4e8eb,0x4e8ed,0x4e903,0x6e90b,0xae90f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1005 : PLift (G 59669 59729) := ⟨bs [0x4e915,0x18e917,0x4e92d,0x4e933,0x6e93b,0x4e94b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1006 : PLift (G 59729 59791) := ⟨bs [0x6e951,0x6e95f,0x4e963,0xae969,0x4e97b,0x14e983] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1007 : PLift (G 59791 59887) := ⟨bs [0x6e98f,0x4e995,0x22e9a1,0xae9b9,0xae9d7,0x1ce9e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1008 : PLift (G 59887 59981) := ⟨bs [0x6e9ef,0x6ea11,0x26ea19,0x16ea2f,0x4ea35,0x6ea43] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1009 : PLift (G 59981 60041) := ⟨bs [0x4ea4d,0xeea5f,0xcea6d,0x6ea71,0x4ea7d,0x4ea85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1010 : PLift (G 60041 60103) := ⟨bs [0x6ea89,0x4eaad,0x4eab3,0x6eab9,0x4eabb,0x6eac5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1011 : PLift (G 60103 60161) := ⟨bs [0xaeac7,0x4eacb,0x6eadf,0xceae5,0x6eaeb,0x4eaf5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1012 : PLift (G 60161 60251) := ⟨bs [0x6eb01,0xaeb07,0x16eb09,0x6eb31,0xaeb39,0x6eb3f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1013 : PLift (G 60251 60317) := ⟨bs [0xceb5b,0x6eb61,0x6eb63,0x6eb6f,0xeeb81,0x4eb85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1014 : PLift (G 60317 60383) := ⟨bs [0x4eb9d,0x18ebab,0xaebb1,0x6ebb7,0x6ebc1,0x4ebd5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1015 : PLift (G 60383 60457) := ⟨bs [0xaebdf,0xaebed,0x4ebfd,0x6ec0b,0x4ec1b,0x6ec21] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1016 : PLift (G 60457 60539) := ⟨bs [0x1aec29,0x4ec4d,0x6ec51,0x4ec5d,0x6ec69,0xaec6f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1017 : PLift (G 60539 60623) := ⟨bs [0x4ec7b,0x4ecad,0x16ecb9,0x6ecbf,0x14ecc3,0x6ecc9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1018 : PLift (G 60623 60661) := ⟨bs [0xaeccf,0xcecd7,0x4ecdd,0xaece7,0x16ece9,0x4ecf3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1019 : PLift (G 60661 60733) := ⟨bs [0x4ecf5,0x6ed07,0x6ed11,0x6ed1f,0xeed2f,0xaed37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1020 : PLift (G 60733 60779) := ⟨bs [0x4ed3d,0x6ed41,0x4ed55,0xced59,0x6ed5b,0x4ed65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1021 : PLift (G 60779 60887) := ⟨bs [0x4ed6b,0xaed79,0x4ed8b,0x4ed95,0x6edbb,0x4edc5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1022 : PLift (G 60887 60919) := ⟨bs [0xeedd7,0x2aedd9,0x4ede3,0x4ede5,0xaedf1,0x4edf5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1023 : PLift (G 60919 61001) := ⟨bs [0x6edf7,0x4edfb,0x14ee09,0xaee0f,0x6ee19,0xeee21] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1024 : PLift (G 61001 61057) := ⟨bs [0x6ee49,0xaee4f,0x4ee63,0x2cee67,0x4ee73,0x6ee7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1025 : PLift (G 61057 61151) := ⟨bs [0xaee81,0x4eea3,0x4eeab,0x6eec1,0xeeec9,0xceed5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1026 : PLift (G 61151 61253) := ⟨bs [0x3eeedf,0x14eee1,0x6eef1,0x4ef1b,0xaef27,0xeef2f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1027 : PLift (G 61253 61333) := ⟨bs [0x4ef45,0x4ef4d,0x4ef63,0x6ef6b,0xeef71,0x4ef93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1028 : PLift (G 61333 61381) := ⟨bs [0x4ef95,0x4ef9b,0xaef9f,0xcefad,0x6efb3,0x4efc3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1029 : PLift (G 61381 61469) := ⟨bs [0xcefc5,0x4efdb,0x6efe1,0xaefe9,0x22f001,0xaf017] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1030 : PLift (G 61469 61511) := ⟨bs [0x4f01d,0x6f01f,0x4f02b,0xaf02f,0x4f035,0x4f043] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1031 : PLift (G 61511 61561) := ⟨bs [0xef047,0x6f04f,0x6f067,0x4f06b,0x6f071,0xef077] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1032 : PLift (G 61561 61631) := ⟨bs [0xef079,0xaf08f,0x4f0a3,0x1af0a9,0x4f0ad,0x6f0bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1033 : PLift (G 61631 61673) := ⟨bs [0x16f0bf,0x4f0c5,0x4f0cb,0x4f0d3,0xaf0d9,0x4f0e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1034 : PLift (G 61673 61729) := ⟨bs [0xaf0e9,0x3af0f1,0xcf0f7,0xaf107,0x4f115,0xaf11b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1035 : PLift (G 61729 61837) := ⟨bs [0xef121,0xef137,0x4f13d,0x4f155,0x4f175,0x6f17b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1036 : PLift (G 61837 61927) := ⟨bs [0xcf18d,0x4f193,0x4f1a5,0x26f1af,0x6f1b7,0xcf1d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1037 : PLift (G 61927 61981) := ⟨bs [0x6f1e7,0xaf1ed,0x4f1fd,0x6f209,0xaf20f,0x4f21b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1038 : PLift (G 61981 62039) := ⟨bs [0xef21d,0x4f223,0x1af227,0x4f233,0x4f23b,0x14f241] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1039 : PLift (G 62039 62099) := ⟨bs [0x22f257,0x6f25f,0x4f265,0x6f269,0xef277,0xcf281] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1040 : PLift (G 62099 62143) := ⟨bs [0x4f293,0xef2a7,0x6f2b1,0x4f2b3,0xef2b9,0x4f2bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1041 : PLift (G 62143 62213) := ⟨bs [0x6f2bf,0x4f2db,0x4f2ed,0x6f2ef,0x6f2f9,0xaf2ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1042 : PLift (G 62213 62303) := ⟨bs [0x4f305,0x4f30b,0xef319,0x6f341,0x6f359,0x4f35b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1043 : PLift (G 62303 62383) := ⟨bs [0xaf35f,0xcf367,0x4f373,0xaf377,0x6f38b,0xef38f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1044 : PLift (G 62383 62473) := ⟨bs [0xaf3af,0x22f3c1,0x6f3d1,0xaf3d7,0xcf3fb,0x6f403] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1045 : PLift (G 62473 62533) := ⟨bs [0xaf409,0x4f40d,0x4f413,0x14f421,0x4f425,0x4f42b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1046 : PLift (G 62533 62597) := ⟨bs [0x4f445,0x4f44b,0x4f455,0x6f463,0x4f475,0xef47f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1047 : PLift (G 62597 62653) := ⟨bs [0x4f485,0x4f48b,0xaf499,0x4f4a3,0x6f4a9,0x16f4af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1048 : PLift (G 62653 62731) := ⟨bs [0x4f4bd,0x6f4c3,0x6f4db,0xaf4df,0x4f4ed,0x4f503] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1049 : PLift (G 62731 62801) := ⟨bs [0x14f50b,0xef517,0x6f521,0xef529,0xaf535,0x6f547] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1050 : PLift (G 62801 62873) := ⟨bs [0x6f551,0x4f563,0x6f56b,0x4f583,0x6f58d,0x4f595] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1051 : PLift (G 62873 62939) := ⟨bs [0x6f599,0x6f5b1,0xaf5b7,0x1cf5c9,0xaf5cf,0x1cf5d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1052 : PLift (G 62939 62989) := ⟨bs [0x4f5db,0x6f5f9,0x14f5fb,0x4f605,0xaf607,0x4f60b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1053 : PLift (G 62989 63079) := ⟨bs [0x4f60d,0x4f635,0x6f637,0x4f653,0x4f65b,0xaf661] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1054 : PLift (G 63079 63149) := ⟨bs [0x6f667,0xaf679,0x6f67f,0x6f689,0x6f697,0x4f69b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1055 : PLift (G 63149 63247) := ⟨bs [0x4f6ad,0x4f6cb,0x4f6dd,0x6f6df,0xef6eb,0xef709] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1056 : PLift (G 63247 63317) := ⟨bs [0xaf70f,0x4f72d,0xcf731,0x4f743,0x22f74f,0xaf751] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1057 : PLift (G 63317 63367) := ⟨bs [0x4f755,0x4f763,0xaf769,0x4f773,0x6f779,0x4af781] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1058 : PLift (G 63367 63419) := ⟨bs [0x6f787,0x6f791,0x4f79d,0x6f79f,0x4f7a5,0xef7b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1059 : PLift (G 63419 63473) := ⟨bs [0x4f7bb,0x4f7bd,0x6f7cf,0x4f7d3,0xaf7e7,0x4f7eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1060 : PLift (G 63473 63533) := ⟨bs [0x6f7f1,0x6f7ff,0x4f805,0x6f80b,0x6f821,0xaf827] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1061 : PLift (G 63533 63599) := ⟨bs [0x6f82d,0x4f835,0x6f847,0xaf859,0x4f863,0x4f865] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1062 : PLift (G 63599 63647) := ⟨bs [0xef86f,0xef871,0x6f877,0x4f87b,0x6f881,0x4f88d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1063 : PLift (G 63647 63691) := ⟨bs [0xaf89f,0xef8a1,0x4f8ab,0x4f8b3,0x16f8b7,0x6f8c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1064 : PLift (G 63691 63737) := ⟨bs [0x1ef8cb,0xaf8d1,0x6f8d7,0xcf8dd,0x1af8e7,0xcf8ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1065 : PLift (G 63737 63799) := ⟨bs [0x6f8f9,0xaf8ff,0x6f911,0x4f91d,0x4f925,0xaf931] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1066 : PLift (G 63799 63853) := ⟨bs [0xcf937,0x4f93b,0x6f941,0x6f94f,0x3af95f,0x22f961] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1067 : PLift (G 63853 63929) := ⟨bs [0x4f96d,0x6f971,0xaf977,0xef99d,0x4f9a3,0x1af9a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1068 : PLift (G 63929 64019) := ⟨bs [0x6f9b9,0x4f9cd,0x6f9e9,0x4f9fd,0xafa07,0x4fa0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1069 : PLift (G 64019 64091) := ⟨bs [0x4fa13,0xafa21,0x4fa25,0x6fa3f,0xafa43,0x16fa51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1070 : PLift (G 64091 64171) := ⟨bs [0x4fa5b,0x4fa6d,0x4fa7b,0x22fa97,0xafa99,0x4fa9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1071 : PLift (G 64171 64237) := ⟨bs [0xefaab,0x4fabb,0x4fabd,0x6fad9,0xafadf,0x18fae7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1072 : PLift (G 64237 64319) := ⟨bs [0x4faed,0xefb0f,0x3afb17,0x4fb1b,0x4fb2d,0xcfb2f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1073 : PLift (G 64319 64403) := ⟨bs [0x1afb3f,0x6fb47,0x4fb4d,0x4fb75,0x4fb7d,0x6fb8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1074 : PLift (G 64403 64489) := ⟨bs [0xafb93,0x6fbb1,0xefbb7,0x4fbc3,0x4fbc5,0x4fbe3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1075 : PLift (G 64489 64579) := ⟨bs [0xefbe9,0x4fbf3,0xafc01,0x6fc29,0x6fc37,0x6fc41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1076 : PLift (G 64579 64627) := ⟨bs [0x4fc43,0x6fc4f,0x6fc59,0x46fc61,0x4fc65,0xcfc6d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1077 : PLift (G 64627 64693) := ⟨bs [0xafc73,0xafc79,0x4fc95,0xcfc97,0x4fc9b,0x22fca7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1078 : PLift (G 64693 64783) := ⟨bs [0x4fcb5,0x6fcc5,0x4fccd,0xafceb,0x4fcfb,0x4fd0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1079 : PLift (G 64783 64871) := ⟨bs [0xafd0f,0x6fd19,0x4fd2b,0x6fd31,0x1afd51,0x4fd55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1080 : PLift (G 64871 64921) := ⟨bs [0xefd67,0x6fd6d,0xcfd6f,0x14fd7b,0x4fd85,0xefd97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1081 : PLift (G 64921 65003) := ⟨bs [0xefd99,0x6fd9f,0x6fda9,0x6fdb7,0x1afdc9,0x4fde5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1082 : PLift (G 65003 65063) := ⟨bs [0xafdeb,0x4fdf3,0x4fe03,0x4fe05,0x6fe09,0xafe1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1083 : PLift (G 65063 65119) := ⟨bs [0xafe27,0x6fe2f,0xefe41,0x4fe4b,0x4fe4d,0xefe57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1084 : PLift (G 65119 65171) := ⟨bs [0x6fe5f,0x4fe63,0x6fe69,0x4fe75,0x4fe7b,0xafe8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1085 : PLift (G 65171 65239) := ⟨bs [0x4fe93,0x4fe95,0x4fe9b,0xafe9f,0x4feb3,0x4febd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1086 : PLift (G 65239 65309) := ⟨bs [0x6fed7,0xafee9,0x4fef3,0x4fef5,0x6ff07,0x4ff0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1087 : PLift (G 65309 65381) := ⟨bs [0x4ff1d,0x4ff2b,0xaff2f,0xaff49,0x4ff4d,0x4ff5b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1088 : PLift (G 65381 65437) := ⟨bs [0x6ff65,0x6ff71,0x6ff7f,0xaff85,0x6ff8b,0xaff8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1089 : PLift (G 65437 65521) := ⟨bs [0xcff9d,0xaffa7,0x16ffa9,0xeffc7,0xeffd9,0x16ffef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1090 : PLift (G 65521 65563) := ⟨bs [0x22fff1,0x70001,0x50003,0xb0007,0xd000f,0xb0015] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1091 : PLift (G 65563 65617) := ⟨bs [0x7001b,0x5002b,0x5002d,0x50033,0x7003f,0x70049] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1092 : PLift (G 65617 65677) := ⟨bs [0x1b0051,0x5005d,0x70061,0x7006f,0x50073,0x70079] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1093 : PLift (G 65677 65717) := ⟨bs [0x5008d,0xb0097,0x500a3,0xd00a5,0x500ab,0x1500b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1094 : PLift (G 65717 65789) := ⟨bs [0x500b5,0x700b7,0x700c1,0x1500c3,0xf00e1,0x700f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1095 : PLift (G 65789 65843) := ⟨bs [0x500fd,0x170111,0x50123,0x3f0127,0x5012d,0x7012f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1096 : PLift (G 65843 65927) := ⟨bs [0x50133,0x7013b,0x5014b,0x170159,0x7016b,0x70181] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1097 : PLift (G 65927 65983) := ⟨bs [0xb0187,0xf0189,0x1b019f,0x501a5,0x501ab,0x501bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1098 : PLift (G 65983 66067) := ⟨bs [0x701bf,0x701c9,0x501ed,0x501f5,0x701f9,0xb01ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1099 : PLift (G 66067 66109) := ⟨bs [0x70213,0x2d0217,0x50223,0x70229,0x70237,0x5023b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1100 : PLift (G 66109 66191) := ⟨bs [0x5023d,0x70259,0x70271,0x1d0279,0x5027d,0x50283] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1101 : PLift (G 66191 66337) := ⟨bs [0x17028f,0x502ad,0x2302bf,0x702df,0x502f5,0x2d02fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1102 : PLift (G 66337 66377) := ⟨bs [0xb0321,0xb0327,0x5032b,0x1b0337,0x230339,0x50345] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1103 : PLift (G 66377 66457) := ⟨bs [0x70349,0xb034f,0x50363,0x5036d,0xf037f,0x70391] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1104 : PLift (G 66457 66523) := ⟨bs [0xb0399,0x15039f,0x503a3,0x503bb,0x503c3,0x503cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1105 : PLift (G 66523 66571) := ⟨bs [0x503db,0x2703e1,0x503e5,0xd03ed,0x1503f9,0x70409] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1106 : PLift (G 66571 66643) := ⟨bs [0xf040b,0x5041b,0x70421,0xf0429,0x70439,0x50445] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1107 : PLift (G 66643 66721) := ⟨bs [0x50453,0x5045d,0xb047b,0xb0489,0x7048d,0x70499] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1108 : PLift (G 66721 66791) := ⟨bs [0x1b04a1,0x504ad,0x504b3,0x704bd,0x704bf,0x704cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1109 : PLift (G 66791 66853) := ⟨bs [0xf04e7,0x504ed,0xd04f9,0x50505,0xf0519,0x50523] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1110 : PLift (G 66853 66923) := ⟨bs [0x50525,0xb052f,0xb053d,0x50543,0x230549,0xd0567] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1111 : PLift (G 66923 66973) := ⟨bs [0x5056b,0x70573,0x7057f,0x50583,0x150585,0xf058f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1112 : PLift (G 66973 67049) := ⟨bs [0x5059d,0xb05a1,0x505bb,0xf05cd,0xb05d9,0x505e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1113 : PLift (G 67049 67121) := ⟨bs [0x705e9,0xb05f1,0x505f5,0x70601,0x170607,0xb061f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1114 : PLift (G 67121 67169) := ⟨bs [0xd0631,0xf0639,0x50643,0x50645,0xb0651,0x50655] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1115 : PLift (G 67169 67217) := ⟨bs [0x70661,0x5066d,0x50673,0xd0675,0x5068b,0x5068d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1116 : PLift (G 67217 67273) := ⟨bs [0x70691,0x170693,0x7069f,0xb06af,0x506bd,0x1d06c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1117 : PLift (G 67273 67369) := ⟨bs [0xf06c9,0x706d9,0x506eb,0x7070b,0xb070f,0x50715] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1118 : PLift (G 67369 67427) := ⟨bs [0x270729,0xf073f,0x70747,0x70751,0x50753,0x5075d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1119 : PLift (G 67427 67481) := ⟨bs [0x50763,0x50765,0x70769,0x70777,0x5077d,0x50795] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1120 : PLift (G 67481 67531) := ⟨bs [0x70799,0x2f07a1,0x507a5,0x507ab,0x1707b7,0x507c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1121 : PLift (G 67531 67579) := ⟨bs [0x1507cb,0xb07d1,0x507db,0xf07e7,0x707ef,0x707f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1122 : PLift (G 67579 67651) := ⟨bs [0xf07fb,0x50805,0x70811,0xb0817,0x50823,0xf082f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1123 : PLift (G 67651 67741) := ⟨bs [0x170843,0x27085f,0x50873,0x5087d,0xb088b,0x50895] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1124 : PLift (G 67741 67783) := ⟨bs [0xd089d,0x1b08a7,0x708ad,0xd08af,0x508b3,0xb08c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1125 : PLift (G 67783 67843) := ⟨bs [0x708c7,0xd08cd,0x1708d9,0x708df,0x1508eb,0x508f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1126 : PLift (G 67843 67927) := ⟨bs [0x1d0903,0x5090d,0x5091b,0x5092b,0x70933,0x7093d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1127 : PLift (G 67927 67961) := ⟨bs [0x70957,0xd095b,0x5095d,0x70963,0xb0967,0x50975] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1128 : PLift (G 67961 68041) := ⟨bs [0x70979,0xb097f,0x5098b,0x50993,0xb0999,0x709b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1129 : PLift (G 68041 68111) := ⟨bs [0x2d09c9,0xb09d5,0x509db,0xd09e7,0xb09f7,0x50a03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1130 : PLift (G 68111 68207) := ⟨bs [0xf0a0f,0xb0a11,0x70a2d,0x50a33,0x1b0a41,0x50a4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1131 : PLift (G 68207 68261) := ⟨bs [0xb0a6f,0x1b0a71,0x50a75,0x50a7b,0x50a83,0x70a8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1132 : PLift (G 68261 68371) := ⟨bs [0x50aa5,0xf0ab7,0xf0ab9,0xd0ad7,0x170ae9,0x230aff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1133 : PLift (G 68371 68449) := ⟨bs [0xf0b13,0x50b25,0xf0b2f,0x50b55,0xb0b5b,0xb0b5f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1134 : PLift (G 68449 68501) := ⟨bs [0xf0b61,0x150b79,0x50b7d,0x50b83,0x70b89,0x150b8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1135 : PLift (G 68501 68567) := ⟨bs [0x70b95,0x50b9b,0xf0ba9,0xd0bb3,0x50bbb,0xb0bbf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1136 : PLift (G 68567 68659) := ⟨bs [0xb0bd7,0xd0be5,0x50bf5,0x50c03,0x70c19,0xf0c1f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1137 : PLift (G 68659 68713) := ⟨bs [0x50c33,0x50c3d,0x50c4b,0xb0c4f,0x50c5b,0x170c67] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1138 : PLift (G 68713 68771) := ⟨bs [0xb0c69,0x70c79,0xb0c81,0x70c87,0xd0c8d,0x70c9f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1139 : PLift (G 68771 68863) := ⟨bs [0x150ca3,0x70ca9,0x70cb7,0x50ccd,0x50cd3,0x1d0cd5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1140 : PLift (G 68863 68903) := ⟨bs [0x70cff,0x1b0d0f,0x2d0d11,0x50d1b,0x70d21,0x50d23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1141 : PLift (G 68903 68993) := ⟨bs [0xb0d27,0x50d2d,0xb0d35,0xb0d3f,0x50d53,0x50d63] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1142 : PLift (G 68993 69061) := ⟨bs [0x70d81,0x270d89,0xd0d93,0x50d9b,0x50da5,0x70da7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1143 : PLift (G 69061 69143) := ⟨bs [0x50dc5,0x50dcb,0x150dd1,0x50df5,0x1b0dff,0xb0e07] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1144 : PLift (G 69143 69197) := ⟨bs [0xb0e17,0x50e1d,0x170e1f,0x50e2b,0x170e47,0x150e49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1145 : PLift (G 69197 69257) := ⟨bs [0x50e4d,0x50e53,0x50e65,0x70e71,0xf0e77,0x70e7f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1146 : PLift (G 69257 69341) := ⟨bs [0x70e89,0x50e8b,0xb0e8f,0x150ec1,0x70ec5,0xb0ed9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1147 : PLift (G 69341 69403) := ⟨bs [0x70edd,0x50efb,0x50f03,0xb0f07,0x50f0d,0xd0f19] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1148 : PLift (G 69403 69467) := ⟨bs [0x1d0f1b,0x50f33,0x1b0f37,0x70f3f,0xb0f51,0xd0f57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1149 : PLift (G 69467 69499) := ⟨bs [0x50f5b,0x70f61,0xf0f69,0x50f73,0x50f75,0x70f79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1150 : PLift (G 69499 69661) := ⟨bs [0x70f7b,0x50fa3,0x50fb5,0x70fd9,0xb0ff7,0x51015] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1151 : PLift (G 69661 69739) := ⟨bs [0xd101d,0x5102d,0x5103b,0xb1041,0x17104d,0x71069] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1152 : PLift (G 69739 69821) := ⟨bs [0x5106b,0x71081,0x51083,0xb1087,0x51093,0x710b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1153 : PLift (G 69821 69859) := ⟨bs [0xf10bd,0x510c3,0x1510c5,0xb10c9,0x1510d7,0x710e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1154 : PLift (G 69859 69941) := ⟨bs [0x1510e3,0x510f5,0x5110b,0xf1117,0x71129,0x7112b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1155 : PLift (G 69941 70009) := ⟨bs [0x51135,0xf1147,0x71167,0x5116d,0x71171,0x51173] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1156 : PLift (G 70009 70079) := ⟨bs [0x271179,0xd1183,0x71197,0xf11a3,0x511ad,0x511b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1157 : PLift (G 70079 70139) := ⟨bs [0xf11bf,0x711d3,0xd11df,0x511e5,0xd11e9,0x511eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1158 : PLift (G 70139 70183) := ⟨bs [0x511fb,0x1511fd,0x5120d,0x51213,0xb1221,0xf1225] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1159 : PLift (G 70183 70237) := ⟨bs [0x71227,0x231237,0x1d1239,0xb123f,0xb124f,0x51255] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1160 : PLift (G 70237 70309) := ⟨bs [0x5125d,0xd1261,0x2f1269,0x17127f,0x71291,0xb1299] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1161 : PLift (G 70309 70379) := ⟨bs [0xd12a5,0x712a9,0xf12b1,0x1712b7,0xd12cf,0x512e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1162 : PLift (G 70379 70451) := ⟨bs [0xd12eb,0x1512ed,0xb12f9,0xb1317,0x15131d,0x1b1327] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1163 : PLift (G 70451 70501) := ⟨bs [0xd1333,0x71339,0x7133b,0x71351,0xb1357,0x231359] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1164 : PLift (G 70501 70573) := ⟨bs [0x51365,0x5136b,0x71381,0xb1389,0x51395,0x513ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1165 : PLift (G 70573 70627) := ⟨bs [0x513ad,0xb13b7,0x513bd,0xb13cf,0x513db,0xd13dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1166 : PLift (G 70627 70709) := ⟨bs [0xf13e3,0x713ef,0xf1401,0x71407,0x5140b,0xb141f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1167 : PLift (G 70709 70793) := ⟨bs [0x51435,0x5143d,0x2d1449,0xb1461,0x71471,0x7147f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1168 : PLift (G 70793 70867) := ⟨bs [0x71489,0xb14a7,0x714b9,0x514bb,0x2314c1,0x514c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1169 : PLift (G 70867 70919) := ⟨bs [0x714d3,0x514dd,0x714df,0x714eb,0x514f5,0x71501] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1170 : PLift (G 70919 70969) := ⟨bs [0xf1507,0x1b1509,0x71519,0x51525,0xd1527,0x5152d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1171 : PLift (G 70969 71011) := ⟨bs [0x171539,0x51543,0xd1545,0xf154f,0x51555,0x171557] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1172 : PLift (G 71011 71089) := ⟨bs [0x1f1563,0xd156f,0x17157f,0xf1593,0x5159d,0x715a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1173 : PLift (G 71089 71161) := ⟨bs [0x1715b1,0x715cf,0x715d9,0xd15e7,0x515eb,0x715f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1174 : PLift (G 71161 71237) := ⟨bs [0x1715f9,0x715ff,0x51603,0x71617,0xf1629,0x171641] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1175 : PLift (G 71237 71293) := ⟨bs [0x51645,0x71651,0xb1659,0x7165d,0xb165f,0x71677] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1176 : PLift (G 71293 71341) := ⟨bs [0xb167d,0x51695,0xb169f,0xf16a1,0x516a5,0x516ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1177 : PLift (G 71341 71389) := ⟨bs [0xd16ad,0x516b3,0xb16b9,0xd16bf,0x516c3,0x516db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1178 : PLift (G 71389 71437) := ⟨bs [0x1716dd,0x1716e7,0x516f3,0x516f5,0x516fb,0x51705] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1179 : PLift (G 71437 71483) := ⟨bs [0x5170d,0x171713,0x5171d,0xf172f,0xb1731,0xd1737] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1180 : PLift (G 71483 71563) := ⟨bs [0x5173b,0x7174f,0x71767,0x71771,0x5177d,0xd177f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1181 : PLift (G 71563 71663) := ⟨bs [0x5178b,0x271791,0xb17a9,0x517ad,0x717d1,0x717df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1182 : PLift (G 71663 71713) := ⟨bs [0xb17ef,0x1f17f7,0x5180d,0x51813,0x5181b,0x23181f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1183 : PLift (G 71713 71807) := ⟨bs [0xb1821,0x71827,0x5183d,0x591851,0x71861,0x5186d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1184 : PLift (G 71807 71861) := ⟨bs [0xb187f,0xf1881,0x5188d,0x5189d,0x518a3,0x718a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1185 : PLift (G 71861 71909) := ⟨bs [0xf18b5,0x518bb,0x1718c7,0xf18c9,0x718cf,0x518db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1186 : PLift (G 71909 71971) := ⟨bs [0x518e5,0x518ed,0x518fd,0x51905,0x5190b,0x5191b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1187 : PLift (G 71971 72031) := ⟨bs [0x51923,0x7192f,0x51933,0x71939,0xf193f,0x51953] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1188 : PLift (G 72031 72089) := ⟨bs [0x7195f,0xb196b,0xb196f,0x51975,0xb1989,0x5198d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1189 : PLift (G 72089 72161) := ⟨bs [0x71999,0x5199b,0x519a5,0xd19a7,0x519ad,0x519cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1190 : PLift (G 72161 72223) := ⟨bs [0xd19e1,0xb19e7,0xf19e9,0x519ed,0x51a13,0x51a1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1191 : PLift (G 72223 72271) := ⟨bs [0x71a1f,0x51a23,0x51a25,0xf1a3b,0x51a3d,0x71a4d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1192 : PLift (G 72271 72341) := ⟨bs [0x71a4f,0xb1a55,0xb1a5f,0x71a73,0xb1a79,0xf1a91] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1193 : PLift (G 72341 72431) := ⟨bs [0x51a95,0x71aa1,0x71aaf,0x51abb,0xb1abf,0xd1ae5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1194 : PLift (G 72431 72497) := ⟨bs [0x1b1aef,0x51b0d,0x51b13,0xd1b15,0x171b21,0x51b2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1195 : PLift (G 72497 72577) := ⟨bs [0xb1b31,0xb1b37,0x51b55,0x51b63,0x1b1b67,0x71b6f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1196 : PLift (G 72577 72649) := ⟨bs [0xb1b81,0x51ba5,0x71ba9,0xb1baf,0x51bc3,0xb1bc7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1197 : PLift (G 72649 72701) := ⟨bs [0xf1bc9,0x171bd5,0xf1bdf,0xb1be1,0xd1be7,0x71bf1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1198 : PLift (G 72701 72763) := ⟨bs [0x51bfd,0x51c03,0x171c0f,0xf1c17,0x51c1d,0x51c23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1199 : PLift (G 72763 72869) := ⟨bs [0x51c3b,0xb1c3f,0x51c5d,0xb1c71,0xb1c77,0x51c9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1200 : PLift (G 72869 72907) := ⟨bs [0x51ca5,0xd1ca7,0x71cb3,0xf1cb9,0x51cbd,0x51cc5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1201 : PLift (G 72907 72953) := ⟨bs [0x51ccb,0x171ccf,0x51cdb,0x151ce3,0xb1ce9,0x51cf5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1202 : PLift (G 72953 73013) := ⟨bs [0x71cf9,0x231cff,0x51d0d,0x71d11,0x51d25,0xf1d31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1203 : PLift (G 73013 73063) := ⟨bs [0x51d35,0x51d3b,0x51d4d,0x71d4f,0x51d53,0x51d65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1204 : PLift (G 73063 73141) := ⟨bs [0x71d67,0x1b1d77,0x51d83,0x71da1,0xb1da7,0x51dad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1205 : PLift (G 73141 73277) := ⟨bs [0xf1db5,0x51ddd,0x51de5,0xd1e15,0x71e1b,0x51e2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1206 : PLift (G 73277 73351) := ⟨bs [0x71e3d,0x71e4b,0xb1e57,0x51e5d,0x71e6f,0x51e73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1207 : PLift (G 73351 73417) := ⟨bs [0x71e87,0x171e91,0xb1e93,0x171e99,0x51ea3,0x51eab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1208 : PLift (G 73417 73477) := ⟨bs [0x151ec9,0x51ecd,0x71ed9,0x51eed,0x51ef3,0x71eff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1209 : PLift (G 73477 73553) := ⟨bs [0xd1f05,0x51f0b,0x51f2d,0x51f33,0x71f39,0x51f4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1210 : PLift (G 73553 73607) := ⟨bs [0x71f51,0x1b1f59,0x51f63,0xb1f6f,0x51f75,0x51f7d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1211 : PLift (G 73607 73673) := ⟨bs [0xb1f87,0x271f89,0x51f8d,0x51fa5,0x51fab,0x51fb3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1212 : PLift (G 73673 73721) := ⟨bs [0x71fc9,0x1d1fcf,0x1d1fd1,0x51fdd,0x51fe3,0x51fed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1213 : PLift (G 73721 73819) := ⟨bs [0xd1ff9,0xb1fff,0x1b2017,0x5201d,0x5202b,0x72037] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1214 : PLift (G 73819 73877) := ⟨bs [0x7205b,0xb205f,0xb2077,0xf2079,0x52083,0x5208b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1215 : PLift (G 73877 73951) := ⟨bs [0x52095,0x5209b,0xb20a9,0x520b3,0x520d3,0xb20d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1216 : PLift (G 73951 74027) := ⟨bs [0x720df,0x720e9,0x520f5,0xd210f,0xf2121,0x52125] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1217 : PLift (G 74027 74099) := ⟨bs [0x5212b,0x7213f,0xd2143,0x1d2157,0xb215d,0x5216d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1218 : PLift (G 74099 74161) := ⟨bs [0x52173,0x52175,0x52193,0xb219f,0x521a5,0x1b21af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1219 : PLift (G 74161 74203) := ⟨bs [0xf21b1,0xb21b7,0x721c1,0x521cd,0xb21d5,0xd21d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1220 : PLift (G 74203 74287) := ⟨bs [0x521db,0x2721e1,0x521eb,0x1721f7,0xb2211,0xf2227] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1221 : PLift (G 74287 74353) := ⟨bs [0x7222f,0xb2235,0x72239,0x192247,0x5224d,0xb2253] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1222 : PLift (G 74353 74411) := ⟨bs [0xb2271,0x52275,0x5227b,0xb2289,0x5228d,0xb228f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1223 : PLift (G 74411 74471) := ⟨bs [0x522ab,0xb22ad,0x522b3,0x722c9,0x1b22d1,0x522d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1224 : PLift (G 74471 74531) := ⟨bs [0x1722e7,0x722f9,0x5230b,0x5230d,0x1b2319,0x7231f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1225 : PLift (G 74531 74597) := ⟨bs [0x52323,0x172337,0x72341,0xb2347,0x5234d,0x5235b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1226 : PLift (G 74597 74699) := ⟨bs [0x52365,0x72371,0x52373,0x7237f,0x5239d,0xb23bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1227 : PLift (G 74699 74731) := ⟨bs [0x523cb,0x523d3,0x1523d9,0x523dd,0xf23df,0x723e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1228 : PLift (G 74731 74797) := ⟨bs [0x523eb,0x523fb,0x172407,0x272409,0x52413,0x5241b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1229 : PLift (G 74797 74861) := ⟨bs [0xb242d,0xd2445,0x7244b,0xf244f,0x5245b,0xb2469] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1230 : PLift (G 74861 74903) := ⟨bs [0x5246d,0x52475,0x72479,0x72487,0x5248b,0x72491] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1231 : PLift (G 74903 75011) := ⟨bs [0xb2497,0xb24ab,0x2324b1,0x524b5,0xd24bd,0x724cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1232 : PLift (G 75011 75079) := ⟨bs [0xd2503,0x52505,0x72509,0x52515,0x5251d,0x72521] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1233 : PLift (G 75079 75167) := ⟨bs [0x72547,0x5254b,0x52565,0x5257d,0x5258d,0x72599] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1234 : PLift (G 75167 75217) := ⟨bs [0xb259f,0xf25a1,0x525ad,0xf25b9,0x725c9,0x525cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1235 : PLift (G 75217 75277) := ⟨bs [0xb25d1,0x725d7,0x525db,0x1b25e7,0x525f5,0x52605] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1236 : PLift (G 75277 75347) := ⟨bs [0x5260d,0x1b2619,0x7262b,0x5263b,0x72641,0xb2649] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1237 : PLift (G 75347 75401) := ⟨bs [0x52653,0x72659,0x72667,0x72671,0x5267d,0x7267f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1238 : PLift (G 75401 75503) := ⟨bs [0x72689,0x7268b,0xb268f,0x2726a7,0x526ad,0x2726d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1239 : PLift (G 75503 75541) := ⟨bs [0xb26ef,0x726f7,0x72701,0xb2707,0x5270d,0x52713] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1240 : PLift (G 75541 75611) := ⟨bs [0x52715,0xb2721,0x52725,0x52733,0x232739,0xb273f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1241 : PLift (G 75611 75659) := ⟨bs [0x5275b,0x72761,0x52763,0x5276d,0x72779,0x52785] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1242 : PLift (G 75659 75709) := ⟨bs [0x5278b,0xd279f,0x527a3,0x727a9,0xb27b7,0x527bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1243 : PLift (G 75709 75781) := ⟨bs [0x527bd,0x1727c9,0x527d3,0xb27df,0xb27f7,0x527fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1244 : PLift (G 75781 75853) := ⟨bs [0xd2805,0xb280b,0x152811,0x52815,0x5282d,0x72839] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1245 : PLift (G 75853 75941) := ⟨bs [0xb284d,0x5285d,0x5286b,0xb2889,0x7289b,0x1528a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1246 : PLift (G 75941 75997) := ⟨bs [0x528a5,0x728bf,0x528cb,0xb28cf,0x528d5,0x1728d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1247 : PLift (G 75997 76081) := ⟨bs [0x528dd,0x728e1,0xb28e3,0xf28ff,0x192907,0x17292f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1248 : PLift (G 76081 76147) := ⟨bs [0xf2931,0x5293b,0xf2943,0xb2947,0x7295b,0x232961] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1249 : PLift (G 76147 76231) := ⟨bs [0x52973,0x5297d,0x7297f,0x52983,0x729af,0xb29b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1250 : PLift (G 76231 76283) := ⟨bs [0xd29c7,0x729d3,0xf29d9,0x529dd,0x529e3,0x529e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1251 : PLift (G 76283 76369) := ⟨bs [0x529fb,0x72a01,0x72a0f,0xb2a2d,0xb2a37,0xb2a4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1252 : PLift (G 76369 76441) := ⟨bs [0x172a51,0x52a5b,0x72a63,0x52a73,0x72a85,0xb2a87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1253 : PLift (G 76441 76507) := ⟨bs [0x172a99,0xb2aaf,0xd2ab7,0x72ac1,0xb2ac7,0x52acd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1254 : PLift (G 76507 76561) := ⟨bs [0x52adb,0xf2adf,0x72ae7,0xb2af9,0x52afd,0x72aff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1255 : PLift (G 76561 76649) := ⟨bs [0x232b11,0x1d2b23,0xf2b35,0x52b3b,0xb2b3f,0xf2b57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1256 : PLift (G 76649 76717) := ⟨bs [0xd2b69,0x72b6b,0x52b7b,0x72b81,0xf2b87,0x72b99] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1257 : PLift (G 76717 76781) := ⟨bs [0x52bad,0x52bbd,0xb2bd1,0x52bd5,0x52be3,0xb2be9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1258 : PLift (G 76781 76847) := ⟨bs [0x52bed,0x232c01,0xf2c13,0x52c1d,0x3b2c1f,0xb2c25] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1259 : PLift (G 76847 76919) := ⟨bs [0xb2c2f,0xf2c47,0x152c49,0x52c53,0x52c6b,0x72c71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1260 : PLift (G 76919 77003) := ⟨bs [0x1b2c77,0x152c8f,0x52c95,0x72ca1,0x72ca3,0x1b2cbf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1261 : PLift (G 77003 77069) := ⟨bs [0x52ccb,0xf2cd9,0x72cdf,0x52ce5,0xf2cf1,0x72cf7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1262 : PLift (G 77069 77153) := ⟨bs [0x52d0d,0x72d19,0x52d25,0xf2d2d,0x1b2d51,0x72d55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1263 : PLift (G 77153 77237) := ⟨bs [0x72d61,0x2b2d6f,0x52d73,0xd2d87,0x72d91,0x52d9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1264 : PLift (G 77237 77267) := ⟨bs [0x52db5,0x72db7,0x52dbb,0x72dc1,0x52dcd,0xb2dcf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1265 : PLift (G 77267 77339) := ⟨bs [0x52dd3,0x52dd5,0x172ddf,0x52deb,0x52e05,0x52e0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1266 : PLift (G 77339 77383) := ⟨bs [0x52e1b,0x72e23,0x1d2e27,0x72e2f,0x72e39,0xb2e41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1267 : PLift (G 77383 77477) := ⟨bs [0x72e47,0x72e69,0x52e6b,0x72e77,0xb2e87,0xf2e9f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1268 : PLift (G 77477 77521) := ⟨bs [0x52ea5,0xd2ea7,0x72eb1,0x72eb3,0x52ec5,0x72ec9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1269 : PLift (G 77521 77563) := ⟨bs [0xf2ed1,0xb2ed7,0xb2ee7,0x52eed,0xd2eef,0xb2ef5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1270 : PLift (G 77563 77617) := ⟨bs [0x52efb,0x1b2f01,0x52f05,0x52f13,0x1b2f17,0x52f2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1271 : PLift (G 77617 77687) := ⟨bs [0x152f31,0x52f35,0x1b2f49,0x72f4f,0x52f5b,0x72f71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1272 : PLift (G 77687 77723) := ⟨bs [0xb2f77,0x1d2f79,0x52f83,0x1d2f8f,0xf2f91,0xd2f97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1273 : PLift (G 77723 77783) := ⟨bs [0x52f9b,0x52fa3,0x72faf,0x52fb3,0x172fc1,0x52fcd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1274 : PLift (G 77783 77863) := ⟨bs [0xb2fd7,0xb2fe5,0xf2fe9,0x52ff5,0x7300f,0x73019] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1275 : PLift (G 77863 77951) := ⟨bs [0xb3027,0x5302b,0x53045,0x1d304b,0x1d3069,0x5306d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1276 : PLift (G 77951 78017) := ⟨bs [0x17307f,0x73091,0xb3099,0x7309f,0x1730af,0x730b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1277 : PLift (G 78017 78101) := ⟨bs [0x730c1,0xf30cf,0x730d9,0xf30e1,0x530eb,0x1930ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1278 : PLift (G 78101 78167) := ⟨bs [0x53115,0x173129,0x73139,0x7313b,0xd314d,0x73153] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1279 : PLift (G 78167 78229) := ⟨bs [0xb3157,0x5315d,0x53163,0x17316f,0xb3171,0x5317b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1280 : PLift (G 78229 78301) := ⟨bs [0x53195,0x73199,0x2731a1,0x531b3,0xd31c5,0x731cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1281 : PLift (G 78301 78367) := ⟨bs [0xd31dd,0x531e3,0x1d31e7,0x531ed,0x53205,0x5320b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1282 : PLift (G 78367 78479) := ⟨bs [0xb321f,0x1b3241,0x7325b,0x53265,0xd3267,0x53283] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1283 : PLift (G 78479 78539) := ⟨bs [0xf328f,0x73297,0x732a1,0x732ad,0x732af,0x532b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1284 : PLift (G 78539 78583) := ⟨bs [0x532cb,0x532cd,0xb32d9,0x732e9,0x532eb,0xb32f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1285 : PLift (G 78583 78653) := ⟨bs [0x732f7,0x73301,0x7330f,0xb331f,0x173333,0x173339] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1286 : PLift (G 78653 78737) := ⟨bs [0x7333d,0xf3363,0xb3369,0x53373,0x73379,0xf3381] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1287 : PLift (G 78737 78803) := ⟨bs [0x73391,0x533bb,0x1533bd,0x533c3,0x1733c7,0x533cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1288 : PLift (G 78803 78877) := ⟨bs [0x533d3,0x733d9,0x733e7,0x1b33f7,0xb3405,0x73409] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1289 : PLift (G 78877 78929) := ⟨bs [0x5341d,0xb3427,0x173429,0x5342d,0x153435,0x73447] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1290 : PLift (G 78929 79039) := ⟨bs [0x73451,0x5345d,0x73481,0x73483,0x5348d,0xf34b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1291 : PLift (G 79039 79133) := ⟨bs [0xd34bf,0x534c3,0xb34d7,0x734ef,0xb34ff,0xd3507] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1292 : PLift (G 79133 79181) := ⟨bs [0x5351d,0x53523,0x5352b,0x1b352f,0x153531,0x73537] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1293 : PLift (G 79181 79241) := ⟨bs [0x5354d,0xb3553,0x73559,0x1b3561,0x5357d,0x7357f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1294 : PLift (G 79241 79309) := ⟨bs [0x73589,0x5359b,0xb35a9,0x735af,0x535b3,0x535c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1295 : PLift (G 79309 79367) := ⟨bs [0x535cd,0xf35d7,0xb35e5,0x735e9,0x535f5,0xf35fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1296 : PLift (G 79367 79423) := ⟨bs [0xb3607,0x53613,0xb3621,0x53625,0x73627,0x53633] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1297 : PLift (G 79423 79531) := ⟨bs [0x7363f,0x53643,0x73649,0xd365b,0xd3679,0xb3685] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1298 : PLift (G 79531 79589) := ⟨bs [0x536ab,0xf36b1,0x536bd,0xf36c7,0xf36c9,0x1536db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1299 : PLift (G 79589 79631) := ⟨bs [0x536e5,0x736f1,0x1d36f9,0x536fd,0x53705,0x7370b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1300 : PLift (G 79631 79693) := ⟨bs [0x1b370f,0x1b3711,0xb3729,0x153735,0x73747,0x15374b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1301 : PLift (G 79693 79801) := ⟨bs [0xb374d,0x73751,0x53753,0x5378d,0x73799,0xb37a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1302 : PLift (G 79801 79841) := ⟨bs [0x2f37b9,0x537c3,0x537c5,0x737c9,0xb37cf,0x537d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1303 : PLift (G 79841 79889) := ⟨bs [0x737e1,0x537e3,0xb37e7,0x537f5,0x537fb,0xf3801] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1304 : PLift (G 79889 79967) := ⟨bs [0x73811,0x5381d,0x7381f,0x53823,0x73843,0xb3847] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1305 : PLift (G 79967 80021) := ⟨bs [0xb385f,0x53865,0x5386b,0x53873,0x5387d,0x7387f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1306 : PLift (G 80021 80111) := ⟨bs [0x53895,0x1738a7,0x538b3,0x738c7,0x538cd,0x538eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1307 : PLift (G 80111 80173) := ⟨bs [0x1738ef,0x5390d,0x53913,0xd3915,0x73919,0x73927] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1308 : PLift (G 80173 80231) := ⟨bs [0xd392d,0x73931,0x17393f,0xb394f,0x1d3951,0x5395d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1309 : PLift (G 80231 80279) := ⟨bs [0xf3967,0xf3969,0x7396f,0x5397b,0x73987,0x73991] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1310 : PLift (G 80279 80347) := ⟨bs [0x173997,0x7399f,0x539b5,0x539bd,0x1739c9,0x539d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1311 : PLift (G 80347 80447) := ⟨bs [0x539db,0x539eb,0x739f1,0x53a03,0x73a17,0x53a2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1312 : PLift (G 80447 80513) := ⟨bs [0xb3a3f,0xf3a41,0x233a57,0xb3a59,0x73a69,0x53a6b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1313 : PLift (G 80513 80603) := ⟨bs [0x73a81,0x73a8f,0x73a99,0x53aad,0xb3ab7,0x73ad7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1314 : PLift (G 80603 80657) := ⟨bs [0x53adb,0x53ae3,0x53aed,0x53af3,0x53af5,0x53b0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1315 : PLift (G 80657 80687) := ⟨bs [0x73b11,0x53b1d,0x73b1f,0x53b25,0x73b29,0x73b2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1316 : PLift (G 80687 80761) := ⟨bs [0xb3b2f,0x53b3d,0xb3b49,0xf3b61,0x53b6b,0x53b6d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1317 : PLift (G 80761 80809) := ⟨bs [0x173b79,0x73b89,0x53b8b,0xb3b8f,0x53b95,0x53ba3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1318 : PLift (G 80809 80897) := ⟨bs [0x273ba9,0x53bb3,0xf3bbf,0xb3bc1,0x73bd1,0x73bdf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1319 : PLift (G 80897 80933) := ⟨bs [0x73c01,0x53c0d,0x73c0f,0xd3c15,0x53c1b,0x273c21] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1320 : PLift (G 80933 81017) := ⟨bs [0x53c25,0xf3c39,0xb3c43,0x53c5d,0x173c69,0xd3c75] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1321 : PLift (G 81017 81047) := ⟨bs [0x73c79,0x53c7b,0xb3c7f,0xd3c87,0xd3c91,0xb3c93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1322 : PLift (G 81047 81101) := ⟨bs [0xb3c97,0xf3c99,0xf3caf,0x53cb5,0x53cbb,0xb3cc9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1323 : PLift (G 81101 81181) := ⟨bs [0x53ccd,0x173cdf,0x53ceb,0xd3d05,0x53d0b,0x53d15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1324 : PLift (G 81181 81239) := ⟨bs [0xd3d1d,0x53d2d,0xd3d2f,0x53d33,0xb3d47,0x73d51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1325 : PLift (G 81239 81331) := ⟨bs [0xf3d57,0x73d81,0x53d83,0x53d8d,0x53d93,0x53d9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1326 : PLift (G 81331 81373) := ⟨bs [0x193db3,0xd3dbf,0x53dc5,0x73dc9,0x173dcf,0x53ddb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1327 : PLift (G 81373 81463) := ⟨bs [0x53ddd,0x73df9,0xf3e01,0x173e0d,0x73e1f,0xb3e31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1328 : PLift (G 81463 81551) := ⟨bs [0xb3e37,0x53e65,0x53e6d,0xb3e77,0x73e7d,0x73e8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1329 : PLift (G 81551 81619) := ⟨bs [0xf3e8f,0xb3e91,0xd3e97,0x53e9b,0x73ea1,0x53ecb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1330 : PLift (G 81619 81671) := ⟨bs [0x73ed3,0x53edd,0x53ee5,0xb3eef,0x173ef1,0x73f03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1331 : PLift (G 81671 81727) := ⟨bs [0xf3f07,0x73f0d,0x73f19,0x53f25,0x73f27,0x53f2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1332 : PLift (G 81727 81799) := ⟨bs [0x73f3f,0x73f49,0x53f55,0x193f61,0x173f69,0x53f6d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1333 : PLift (G 81799 81883) := ⟨bs [0x73f87,0xb3f99,0xf3faf,0x73fb7,0x173fbd,0x53fcd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1334 : PLift (G 81883 81937) := ⟨bs [0x73fdb,0x53feb,0x53fed,0x73fff,0x74009,0x7400b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1335 : PLift (G 81937 82003) := ⟨bs [0xb4011,0xb4017,0x74021,0xb402f,0x54033,0x54035] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1336 : PLift (G 82003 82037) := ⟨bs [0x54053,0xb4057,0x1b4059,0x17405d,0x2d4065,0x17406f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1337 : PLift (G 82037 82139) := ⟨bs [0x54075,0x1f4077,0x54083,0x54093,0x74099,0x1b40d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1338 : PLift (G 82139 82189) := ⟨bs [0xd40db,0xd40dd,0xb40e9,0x540f3,0x540fb,0x2b4107] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1339 : PLift (G 82189 82231) := ⟨bs [0x15410d,0xb4111,0x7411f,0x74129,0x5412b,0xb412f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1340 : PLift (G 82231 82301) := ⟨bs [0xf4137,0xb413d,0x74141,0xd4155,0x5415b,0xd4167] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1341 : PLift (G 82301 82373) := ⟨bs [0x5417d,0x54183,0x541a3,0x741ad,0x741af,0x741b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1342 : PLift (G 82373 82469) := ⟨bs [0x541c5,0x541d3,0xb41d9,0x541f5,0x74219,0xb421f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1343 : PLift (G 82469 82507) := ⟨bs [0x54225,0x74227,0x54233,0xb4237,0x5423d,0xd4243] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1344 : PLift (G 82507 82567) := ⟨bs [0x5424b,0x74261,0x74263,0x54275,0xf427f,0xf4281] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1345 : PLift (G 82567 82619) := ⟨bs [0x74287,0xd428b,0xd429f,0x742a9,0x1742b1,0x542b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1346 : PLift (G 82619 82723) := ⟨bs [0x542bb,0xb42c9,0x542db,0x1542e1,0x7430b,0xd4321] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1347 : PLift (G 82723 82781) := ⟨bs [0x54323,0xb4327,0xf4329,0x54345,0x74347,0x5434b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1348 : PLift (G 82781 82837) := ⟨bs [0x5435d,0x54363,0x74369,0x1b436f,0x5437b,0x5437d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1349 : PLift (G 82837 82913) := ⟨bs [0x54395,0xb439f,0x543c3,0x743c9,0x543cb,0x743d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1350 : PLift (G 82913 83009) := ⟨bs [0x743e1,0x543fb,0x74413,0x54425,0x54435,0x5443b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1351 : PLift (G 83009 83077) := ⟨bs [0x74441,0x7444f,0x74467,0x54473,0xb4477,0x1d447f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1352 : PLift (G 83077 83177) := ⟨bs [0x1d4485,0xf4491,0x54495,0x5449d,0x544ad,0xb44c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1353 : PLift (G 83177 83231) := ⟨bs [0x744e9,0x54503,0xb4507,0x54513,0xf4515,0xb451b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1354 : PLift (G 83231 83273) := ⟨bs [0xf451f,0xf4521,0x5452b,0xb4539,0x54543,0x54545] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1355 : PLift (G 83273 83383) := ⟨bs [0x74549,0x54563,0x19456f,0x5458b,0x15458d,0x5459d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1356 : PLift (G 83383 83423) := ⟨bs [0x745b7,0x545bd,0xf45c7,0xf45c9,0xb45cf,0x745d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1357 : PLift (G 83423 83471) := ⟨bs [0xb45df,0x1945e7,0x545ed,0x545f3,0x1b45f9,0x54603] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1358 : PLift (G 83471 83563) := ⟨bs [0x17460f,0x54615,0x154629,0x74651,0x54665,0x74669] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1359 : PLift (G 83563 83621) := ⟨bs [0x5466b,0x5467b,0xf4687,0x5468d,0x74699,0xb46a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1360 : PLift (G 83621 83701) := ⟨bs [0x546a5,0x2746b7,0xf46b9,0xb46c5,0xb46cf,0x1b46e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1361 : PLift (G 83701 83777) := ⟨bs [0xd46f5,0x54705,0xd4707,0xb4719,0x174731,0xb473d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1362 : PLift (G 83777 83869) := ⟨bs [0x74741,0x7474f,0x54765,0xb4779,0x54783,0xb4791] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1363 : PLift (G 83869 83933) := ⟨bs [0xd479d,0x747a1,0x547b3,0xb47bf,0x747c7,0x747d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1364 : PLift (G 83933 84017) := ⟨bs [0x547dd,0x547e3,0x74801,0xb480f,0x54813,0xd482b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1365 : PLift (G 84017 84089) := ⟨bs [0x74831,0xb484f,0x54855,0x5485b,0xf485d,0x54863] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1366 : PLift (G 84089 84163) := ⟨bs [0x74879,0x1b4899,0x7489f,0x548a3,0x748a9,0xb48af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1367 : PLift (G 84163 84221) := ⟨bs [0x548c3,0x548d3,0x548d5,0xf48df,0x1748e7,0x748f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1368 : PLift (G 84221 84299) := ⟨bs [0x548fd,0xd48ff,0x54905,0x17490f,0xb4917,0xb4927] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1369 : PLift (G 84299 84349) := ⟨bs [0x5494b,0x74953,0xb4959,0x5495d,0xd495f,0x5497b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1370 : PLift (G 84349 84421) := ⟨bs [0x5497d,0x74999,0x549a5,0x749a7,0x749b1,0xb49b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1371 : PLift (G 84421 84463) := ⟨bs [0x549c5,0xf49cf,0x549d5,0x549db,0x749e1,0xb49e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1372 : PLift (G 84463 84521) := ⟨bs [0xb49ef,0x549f3,0xf4a01,0x54a13,0x1f4a17,0x54a1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1373 : PLift (G 84521 84629) := ⟨bs [0x74a29,0x54a2b,0x54a35,0x274a47,0x74a4f,0x54a6d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1374 : PLift (G 84629 84691) := ⟨bs [0x54a95,0xd4a97,0x1b4aa9,0x54aad,0x54ab3,0x154ac1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1375 : PLift (G 84691 84737) := ⟨bs [0x54ad3,0x174ad9,0x54add,0x74ae9,0x1b4aef,0x54afb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1376 : PLift (G 84737 84811) := ⟨bs [0x74b01,0xd4b0f,0xf4b19,0x54b33,0xb4b39,0x74b49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1377 : PLift (G 84811 84913) := ⟨bs [0x74b4b,0x54b5b,0x74b79,0x54b7b,0x74b85,0x74b87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1378 : PLift (G 84913 84979) := ⟨bs [0xb4bb1,0x74bb7,0x54bd3,0x174be1,0x74be7,0x74bf1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1379 : PLift (G 84979 85049) := ⟨bs [0x54bf3,0x74bff,0x1b4c11,0xf4c1d,0x54c23,0x54c2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1380 : PLift (G 85049 85103) := ⟨bs [0x74c39,0x54c45,0xf4c59,0x74c5f,0xd4c63,0x54c65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1381 : PLift (G 85103 85193) := ⟨bs [0xb4c6f,0x54c75,0xd4c81,0x54c8d,0x54c9b,0x74ca7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1382 : PLift (G 85193 85237) := ⟨bs [0x74cc9,0xf4ccf,0x2d4cd1,0xd4cdd,0xb4ce7,0x74ced] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1383 : PLift (G 85237 85313) := ⟨bs [0x54cf5,0x74cfb,0xb4cff,0x54d0b,0x1f4d31,0xb4d37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1384 : PLift (G 85313 85381) := ⟨bs [0x74d41,0x54d53,0xb4d55,0x74d71,0x74d73,0x234d79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1385 : PLift (G 85381 85451) := ⟨bs [0xd4d85,0x54da3,0x54db3,0xd4db5,0xf4dbf,0x74dc7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1386 : PLift (G 85451 85523) := ⟨bs [0x54dcb,0x54dcd,0x74ddd,0xb4def,0xb4e09,0x54e0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1387 : PLift (G 85523 85601) := ⟨bs [0x54e13,0x1d4e1b,0x54e2d,0x54e43,0x74e49,0x54e5d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1388 : PLift (G 85601 85643) := ⟨bs [0x74e61,0xb4e67,0xd4e73,0x154e75,0x54e7b,0x74e87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1389 : PLift (G 85643 85711) := ⟨bs [0x54e8b,0x54e9d,0xb4ea3,0x54ea5,0x54ebb,0xb4ec7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1390 : PLift (G 85711 85817) := ⟨bs [0xd4ecf,0x54ed5,0x54ee5,0x1d4ef7,0x54f15,0x74f21] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1391 : PLift (G 85817 85847) := ⟨bs [0x74f39,0x54f3b,0x54f45,0x74f47,0x54f4d,0x74f53] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1392 : PLift (G 85847 85933) := ⟨bs [0xb4f57,0x54f5d,0x74f81,0x74f8f,0x54f95,0x54fab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1393 : PLift (G 85933 86029) := ⟨bs [0xb4fad,0x174fe7,0x74fef,0xf4ffb,0xb5001,0x5500b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1394 : PLift (G 86029 86117) := ⟨bs [0x5500d,0x55035,0xb503d,0x55043,0x17505f,0xb5061] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1395 : PLift (G 86117 86179) := ⟨bs [0x55065,0x55073,0xb5079,0x7507f,0x1d5091,0xf509b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1396 : PLift (G 86179 86243) := ⟨bs [0x550a3,0xb50a7,0x550b5,0x750b9,0x1750c1,0x750df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1397 : PLift (G 86243 86291) := ⟨bs [0x550e3,0x750e9,0xb50f1,0x750f7,0xd50fd,0x17510f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1398 : PLift (G 86291 86351) := ⟨bs [0x55113,0x55115,0x75119,0x75127,0x55133,0x55145] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1399 : PLift (G 86351 86389) := ⟨bs [0x1b514f,0x155151,0x55155,0x75161,0x75163,0x7516d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1400 : PLift (G 86389 86461) := ⟨bs [0x55175,0x17517f,0x5518d,0xb5197,0x751a9,0x551b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1401 : PLift (G 86461 86531) := ⟨bs [0x551bd,0x551c3,0x551cd,0x551db,0x551e5,0xd51ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1402 : PLift (G 86531 86587) := ⟨bs [0x55203,0x55205,0x7520b,0x75221,0x5522d,0x55233] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1403 : PLift (G 86587 86693) := ⟨bs [0x7523b,0x75247,0x55263,0x55265,0x55295,0x1b52a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1404 : PLift (G 86693 86767) := ⟨bs [0x552a5,0xf52b7,0xd52bf,0x752c9,0x752d7,0x752e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1405 : PLift (G 86767 86851) := ⟨bs [0x752ef,0xd52f3,0xb52ff,0x5531d,0x55335,0x5533b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1406 : PLift (G 86851 86929) := ⟨bs [0x55343,0x155349,0x5534d,0x55355,0x5538b,0xb538f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1407 : PLift (G 86929 86993) := ⟨bs [0x1d5391,0x5539b,0xf53a7,0x753af,0x753b9,0x553c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1408 : PLift (G 86993 87071) := ⟨bs [0x753d1,0x553e3,0xb53e5,0x553fd,0x75401,0x275409] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1409 : PLift (G 87071 87133) := ⟨bs [0x23541f,0x5542b,0x7543f,0x55443,0xf544f,0xf5451] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1410 : PLift (G 87133 87211) := ⟨bs [0xd545d,0x5546d,0x7546f,0x5548b,0x5548d,0x75493] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1411 : PLift (G 87211 87277) := ⟨bs [0x1b54ab,0x1554b5,0x754b7,0x554d3,0x554d5,0x754d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1412 : PLift (G 87277 87323) := ⟨bs [0xb54ed,0x754f1,0x554fd,0x55503,0xb5511,0x55515] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1413 : PLift (G 87323 87421) := ⟨bs [0x5551b,0xb5529,0x27553f,0xb5557,0x5556b,0xb556f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1414 : PLift (G 87421 87491) := ⟨bs [0xd557d,0x55583,0xb5589,0x55593,0xb55b1,0x3b55b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1415 : PLift (G 87491 87541) := ⟨bs [0x555c3,0x555d5,0x755d7,0x555dd,0x555e3,0x555f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1416 : PLift (G 87541 87587) := ⟨bs [0x2555f5,0x555fb,0xb5601,0x75605,0x75607,0x7561f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1417 : PLift (G 87587 87641) := ⟨bs [0x55623,0x55625,0x5563d,0xb5647,0x5564d,0xd564f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1418 : PLift (G 87641 87691) := ⟨bs [0x75659,0x7565b,0x235661,0x175677,0x7567f,0x55683] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1419 : PLift (G 87691 87743) := ⟨bs [0xf568b,0x235691,0x55695,0xf56a7,0x1756a9,0xf56bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1420 : PLift (G 87743 87811) := ⟨bs [0xb56bf,0x756c7,0xb56d7,0xb56f1,0x556f5,0xb56fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1421 : PLift (G 87811 87887) := ⟨bs [0x55703,0x75719,0x5572d,0x5573d,0x55745,0x75749] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1422 : PLift (G 87887 87961) := ⟨bs [0xb574f,0x3b5767,0x5576d,0x15577b,0x75787,0xf5797] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1423 : PLift (G 87961 88007) := ⟨bs [0x1d5799,0x557a5,0x757a9,0xd57b7,0xd57c1,0x557c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1424 : PLift (G 88007 88117) := ⟨bs [0xb57c7,0x557d3,0x557e5,0x55805,0x3f580f,0x5581d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1425 : PLift (G 88117 88237) := ⟨bs [0xb5835,0x175841,0x75869,0xb5871,0x55893,0xb589f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1426 : PLift (G 88237 88321) := ⟨bs [0x558ad,0x758b1,0x558c3,0x558c5,0x758e1,0x558ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1427 : PLift (G 88321 88411) := ⟨bs [0x455901,0xb5907,0x75911,0x75913,0x5593b,0x5594d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1428 : PLift (G 88411 88493) := ⟨bs [0x5595b,0xd5967,0x5596b,0xb598f,0x55995,0x175997] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1429 : PLift (G 88493 88591) := ⟨bs [0x559ad,0x559b3,0x1559c1,0x559cb,0x559e3,0x55a0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1430 : PLift (G 88591 88661) := ⟨bs [0x1f5a0f,0xb5a1f,0x235a21,0x55a43,0x75a4b,0xb5a51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1431 : PLift (G 88661 88741) := ⟨bs [0x55a55,0x75a57,0x55a5b,0xf5a69,0x75a91,0x235a99] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1432 : PLift (G 88741 88801) := ⟨bs [0x55aa5,0xf5aab,0x175ac3,0x55ad5,0x75ad9,0xf5adf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1433 : PLift (G 88801 88843) := ⟨bs [0xf5ae1,0xb5ae7,0x55aeb,0xb5aed,0x75af1,0x55af3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1434 : PLift (G 88843 88897) := ⟨bs [0x55b0b,0x55b15,0x55b1d,0x55b23,0x1f5b29,0x55b33] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1435 : PLift (G 88897 88993) := ⟨bs [0x175b41,0x75b47,0x2f5b57,0x75b69,0x75b77,0xf5b89] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1436 : PLift (G 88993 89041) := ⟨bs [0xb5ba1,0x55ba5,0x55bab,0x75bb1,0xb5bb9,0x55bbd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1437 : PLift (G 89041 89087) := ⟨bs [0x3b5bd1,0x55bdb,0x75be1,0x55bed,0xd5bef,0x55bfb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1438 : PLift (G 89087 89137) := ⟨bs [0xb5bff,0x55c0d,0x55c13,0xf5c19,0xd5c1f,0xb5c23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1439 : PLift (G 89137 89227) := ⟨bs [0xb5c31,0x75c41,0x55c65,0x55c73,0x2d5c79,0x55c7d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1440 : PLift (G 89227 89293) := ⟨bs [0x75c8b,0x1d5c8f,0x55c95,0x55cad,0x55cb5,0x75cb9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1441 : PLift (G 89293 89381) := ⟨bs [0xb5ccd,0xb5cd7,0x55ce5,0x1b5cf1,0xb5d13,0x55d1b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1442 : PLift (G 89381 89431) := ⟨bs [0x55d25,0x55d2b,0x75d31,0xf5d37,0x55d45,0x75d49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1443 : PLift (G 89431 89501) := ⟨bs [0x175d57,0x55d63,0x175d69,0x55d73,0x55d85,0x55d93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1444 : PLift (G 89501 89561) := ⟨bs [0x55d9d,0x75da9,0x175daf,0x1d5db1,0x75db7,0x55dbd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1445 : PLift (G 89561 89603) := ⟨bs [0x75dd9,0x55ddb,0xb5ddf,0x1b5df7,0x55dfd,0x75dff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1446 : PLift (G 89603 89659) := ⟨bs [0x55e03,0x55e0b,0x55e1b,0x75e21,0x235e35,0x75e39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1447 : PLift (G 89659 89759) := ⟨bs [0x155e3b,0x55e45,0xd5e47,0x75e51,0xf5e59,0x75e99] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1448 : PLift (G 89759 89819) := ⟨bs [0x1b5e9f,0x75ea7,0x55eb3,0xb5eb7,0xb5ec5,0xf5ed1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1449 : PLift (G 89819 89891) := ⟨bs [0x55edb,0x55edd,0xb5ee9,0xf5eef,0x75ef9,0x55f0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1450 : PLift (G 89891 89939) := ⟨bs [0xf5f23,0x75f29,0x55f2b,0x55f35,0x55f3d,0x75f43] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1451 : PLift (G 89939 90001) := ⟨bs [0x55f53,0x75f67,0x55f6b,0xb5f79,0x75f7f,0x55f85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1452 : PLift (G 90001 90031) := ⟨bs [0x1b5f91,0xd5f97,0x55f9b,0x75fa1,0x1d5fa3,0xb5fa7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1453 : PLift (G 90031 90089) := ⟨bs [0x75faf,0x55fc5,0x55fcb,0x55fd3,0xf5fd7,0x155fd9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1454 : PLift (G 90089 90173) := ⟨bs [0x75fe9,0x55ffb,0x2f6009,0x7600f,0x56025,0x56033] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1455 : PLift (G 90173 90217) := ⟨bs [0x5603d,0x5604b,0x23604f,0x56055,0x76057,0x5605b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1456 : PLift (G 90217 90281) := ⟨bs [0x2d6069,0x56073,0xf607f,0xb6087,0xb6097,0x7609f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1457 : PLift (G 90281 90373) := ⟨bs [0x760a9,0x2f60b1,0xb60c9,0x760f1,0x1760f7,0x56103] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1458 : PLift (G 90373 90437) := ⟨bs [0xb6105,0x5610b,0x5611d,0xd6121,0x76123,0xb6127] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1459 : PLift (G 90437 90511) := ⟨bs [0x56145,0x1b6147,0x56165,0x76169,0x1d6171,0x56183] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1460 : PLift (G 90511 90583) := ⟨bs [0x7618f,0x5619b,0xb619f,0xf61a1,0x561a5,0x561b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1461 : PLift (G 90583 90647) := ⟨bs [0xb61d7,0x1761e7,0x761f9,0x761fb,0x76207,0x76211] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1462 : PLift (G 90647 90709) := ⟨bs [0xb6217,0x56223,0x56235,0x76237,0xb6249,0x7624f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1463 : PLift (G 90709 90821) := ⟨bs [0xd6255,0x5626b,0x5627d,0x762a3,0xb62a9,0x562b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1464 : PLift (G 90821 90887) := ⟨bs [0x762c5,0xd62c7,0x762d1,0x2362d9,0xb62df,0xb62ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1465 : PLift (G 90887 90947) := ⟨bs [0xb6307,0x56315,0xb631b,0xf631f,0x56325,0x176333] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1466 : PLift (G 90947 91019) := ⟨bs [0x56343,0x5635b,0x76361,0x5636d,0xb6375,0x176381] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1467 : PLift (G 91019 91121) := ⟨bs [0x5638b,0xb6399,0xf63c7,0x2363c9,0x763d9,0x563db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1468 : PLift (G 91121 91153) := ⟨bs [0xd63f1,0xb63f7,0xf63f9,0x56403,0xd6405,0xf640f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1469 : PLift (G 91153 91229) := ⟨bs [0xf6411,0xd6417,0x5641b,0x7642f,0x76439,0x17643f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1470 : PLift (G 91229 91291) := ⟨bs [0x5645d,0xd6465,0xb646b,0x236471,0x56475,0x56493] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1471 : PLift (G 91291 91369) := ⟨bs [0x5649b,0xb64a1,0x764a7,0x1564ad,0x564c3,0x1764e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1472 : PLift (G 91369 91411) := ⟨bs [0xf64e9,0x764ed,0x2364f5,0x564fb,0x2f6501,0x56505] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1473 : PLift (G 91411 91463) := ⟨bs [0x56513,0x7651f,0x76529,0xd653d,0x76541,0x56543] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1474 : PLift (G 91463 91571) := ⟨bs [0xb6547,0x56565,0x5656b,0x156579,0x76589,0x56595] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1475 : PLift (G 91571 91631) := ⟨bs [0x565b3,0xb65b5,0x765b9,0xb65bf,0x765c7,0x565e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1476 : PLift (G 91631 91733) := ⟨bs [0xf65ef,0x765f7,0x76619,0x5662b,0xb6637,0x17663f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1477 : PLift (G 91733 91807) := ⟨bs [0x56655,0x156669,0x5666d,0x5667b,0x56685,0x1b6699] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1478 : PLift (G 91807 91867) := ⟨bs [0x7669f,0x566a3,0x566a5,0xb66af,0x566bd,0x766c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1479 : PLift (G 91867 91951) := ⟨bs [0x566db,0xb66e1,0x56705,0x1b6711,0x56723,0xb6727] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1480 : PLift (G 91951 92003) := ⟨bs [0x7672f,0xf6735,0x1f6739,0xb673f,0x1b6741,0x5675d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1481 : PLift (G 92003 92083) := ⟨bs [0x56763,0x76769,0x76781,0xf6789,0xd6793,0x567ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1482 : PLift (G 92083 92173) := ⟨bs [0x567b3,0x567cb,0x1b67cf,0x767d7,0xb67ef,0x767f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1483 : PLift (G 92173 92221) := ⟨bs [0x5680d,0xd6811,0x76813,0x5681d,0x5682b,0x5683b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1484 : PLift (G 92221 92269) := ⟨bs [0xd683d,0x76843,0xb6849,0x5684d,0x56853,0x5685b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1485 : PLift (G 92269 92353) := ⟨bs [0x15686d,0x76889,0xf6897,0xd689d,0x568ad,0xb68bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1486 : PLift (G 92353 92383) := ⟨bs [0xb68c1,0x768c5,0x568cb,0x768d1,0xf68d9,0x568dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1487 : PLift (G 92383 92431) := ⟨bs [0x768df,0x568e3,0x1b68ef,0x4568f1,0x568fd,0x56903] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1488 : PLift (G 92431 92503) := ⟨bs [0xd690f,0x5692b,0x5692d,0x56933,0xd693f,0x76949] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1489 : PLift (G 92503 92581) := ⟨bs [0xb6957,0x5695b,0xf6987,0x5698d,0xb6997,0x3f6999] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1490 : PLift (G 92581 92647) := ⟨bs [0xd69a5,0xb69b1,0x1769cf,0x569d3,0xf69df,0x1769e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1491 : PLift (G 92647 92693) := ⟨bs [0x769e7,0x769f1,0x569fd,0x769ff,0x76a09,0x76a0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1492 : PLift (G 92693 92753) := ⟨bs [0x56a15,0x56a1b,0x56a23,0x56a2d,0x56a33,0xb6a41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1493 : PLift (G 92753 92801) := ⟨bs [0x76a51,0x356a59,0x76a5f,0x56a6b,0x56a75,0xd6a77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1494 : PLift (G 92801 92861) := ⟨bs [0x76a81,0x1d6a89,0xd6a95,0xf6a9f,0x76ab1,0xb6ab9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1495 : PLift (G 92861 92927) := ⟨bs [0x56abd,0xd6abf,0x56ac3,0xb6add,0xf6ae3,0x76af9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1496 : PLift (G 92927 92993) := ⟨bs [0xb6aff,0x56b0d,0x176b17,0x56b1d,0xd6b1f,0x56b3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1497 : PLift (G 92993 93083) := ⟨bs [0x76b41,0x1d6b49,0xb6b77,0x56b7d,0x56b83,0x56b95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1498 : PLift (G 93083 93133) := ⟨bs [0x56b9b,0x76ba1,0x156ba9,0xb6baf,0x76bb9,0xd6bcb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1499 : PLift (G 93133 93199) := ⟨bs [0xd6bcd,0x56bd3,0x76bdf,0x176bf1,0x56bfb,0x76c03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1500 : PLift (G 93199 93257) := ⟨bs [0xf6c0f,0xd6c2d,0x176c37,0x1b6c39,0x56c43,0x56c45] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1501 : PLift (G 93257 93319) := ⟨bs [0x76c49,0xb6c4f,0x76c61,0x56c63,0xb6c67,0x56c7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1502 : PLift (G 93319 93383) := ⟨bs [0x76c87,0x56c8b,0x76c91,0xb6c99,0x56cbb,0x76cc1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1503 : PLift (G 93383 93481) := ⟨bs [0xb6cc7,0xb6cdf,0x56ceb,0x56cf3,0x76d17,0xf6d27] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1504 : PLift (G 93481 93523) := ⟨bs [0x476d29,0xd6d2f,0x56d33,0x56d35,0x76d39,0xb6d3f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1505 : PLift (G 93523 93581) := ⟨bs [0x56d53,0x176d59,0xb6d71,0x56d75,0x76d77,0xb6d7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1506 : PLift (G 93581 93701) := ⟨bs [0x76d8d,0x2d6da1,0x76da7,0x56dbd,0xb6dc5,0x56df3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1507 : PLift (G 93701 93787) := ⟨bs [0x56e05,0xb6e07,0x1b6e17,0x76e2b,0xd6e41,0x56e43] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1508 : PLift (G 93787 93887) := ⟨bs [0xf6e5b,0x76e71,0x56e73,0x56e83,0x56e9b,0x76eaf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1509 : PLift (G 93887 93923) := ⟨bs [0xb6ebf,0x1d6ec1,0x56ec5,0x56ecd,0x176ed7,0xb6ed9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1510 : PLift (G 93923 93979) := ⟨bs [0x56ee3,0x1f6ef1,0x56ef5,0x56efd,0x176f0f,0x56f13] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1511 : PLift (G 93979 94049) := ⟨bs [0x76f1b,0xb6f1f,0x176f2d,0xb6f37,0x1b6f39,0x1f6f51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1512 : PLift (G 94049 94111) := ⟨bs [0x76f61,0xf6f69,0x76f6f,0x1b6f7f,0x56f93,0x56f9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1513 : PLift (G 94111 94201) := ⟨bs [0x76f9f,0x56fa5,0x76fa9,0xf6fc7,0xb6fc9,0x76fd9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1514 : PLift (G 94201 94273) := ⟨bs [0x176ff9,0xd6fff,0x7700b,0x57015,0x5702d,0xd7035] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1515 : PLift (G 94273 94331) := ⟨bs [0xb7041,0x57053,0x57063,0xd7065,0xf7071,0x77077] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1516 : PLift (G 94331 94399) := ⟨bs [0x5707b,0xb7087,0x5708d,0x7708f,0x570ab,0x570bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1517 : PLift (G 94399 94447) := ⟨bs [0x770bf,0x570d5,0x570db,0xb70e1,0xf70e7,0x1770e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1518 : PLift (G 94447 94531) := ⟨bs [0xb70ef,0xb70ff,0x5710d,0x57113,0xb7131,0x77141] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1519 : PLift (G 94531 94573) := ⟨bs [0x157143,0x5714d,0x7714f,0x57153,0x17715f,0x1d7161] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1520 : PLift (G 94573 94649) := ⟨bs [0x5716d,0xb7177,0xb7185,0xb718b,0x77195,0x5719d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1521 : PLift (G 94649 94727) := ⟨bs [0x771b9,0x571bb,0xb71df,0xb71e5,0x571f5,0x57203] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1522 : PLift (G 94727 94793) := ⟨bs [0xb7207,0x5721b,0x157233,0x157239,0x5723d,0x57245] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1523 : PLift (G 94793 94847) := ⟨bs [0x77249,0x5725b,0x57263,0xb7267,0x57275,0x77279] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1524 : PLift (G 94847 94933) := ⟨bs [0xb727f,0xf7281,0xb7299,0x772a9,0x772b7,0x572bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1525 : PLift (G 94933 95003) := ⟨bs [0x572d5,0x572e5,0xd72e7,0x772f1,0x157311,0x77317] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1526 : PLift (G 95003 95083) := ⟨bs [0x5731b,0x77321,0x5732d,0x57333,0xb7357,0x7735f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1527 : PLift (G 95083 95111) := ⟨bs [0x5736b,0xb736f,0x1b7371,0x57375,0x5737d,0xb7383] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1528 : PLift (G 95111 95191) := ⟨bs [0x177387,0xf739b,0x773a7,0x773b1,0x773c9,0x573d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1529 : PLift (G 95191 95239) := ⟨bs [0x1b73d7,0x573e3,0x773ed,0x573f3,0x1773ff,0xb7401] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1530 : PLift (G 95239 95287) := ⟨bs [0xf7407,0xb7419,0x5741d,0x57423,0x77429,0xf742f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1531 : PLift (G 95287 95383) := ⟨bs [0x77437,0x7744f,0xb7455,0xb745f,0x5746b,0x77489] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1532 : PLift (G 95383 95441) := ⟨bs [0x77497,0x774a1,0xf74a9,0x574b5,0x774bb,0x574c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1533 : PLift (G 95441 95483) := ⟨bs [0x774d1,0x774d3,0x574e5,0xb74eb,0x5774ef,0x2374f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1534 : PLift (G 95483 95561) := ⟨bs [0x574fb,0x57513,0x77527,0x5752b,0x77533,0x5753d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1535 : PLift (G 95561 95621) := ⟨bs [0x77549,0x1d7551,0x5755d,0x5756d,0xb7573,0xb7581] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1536 : PLift (G 95621 95713) := ⟨bs [0x77585,0x5758d,0x77591,0x575a3,0x575d5,0x575db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1537 : PLift (G 95713 95773) := ⟨bs [0xb75e1,0x575e5,0x575eb,0x575f3,0xb75f9,0xb7603] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1538 : PLift (G 95773 95813) := ⟨bs [0xf761d,0xb7627,0x5762d,0x7762f,0x77639,0x7763b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1539 : PLift (G 95813 95891) := ⟨bs [0x57645,0x5764b,0x157671,0xd767d,0x77681,0x1b7689] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1540 : PLift (G 95891 95957) := ⟨bs [0x57693,0x776a7,0x576ad,0x776b3,0x3576b9,0x576cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1541 : PLift (G 95957 96013) := ⟨bs [0x576d5,0x776d7,0x776e3,0x576f3,0xd76f5,0xf7701] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1542 : PLift (G 96013 96097) := ⟨bs [0x5770d,0x77711,0x5772b,0x57735,0x5773b,0x7774f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1543 : PLift (G 96097 96181) := ⟨bs [0xb7761,0x77789,0x57795,0xb779d,0xb77a7,0x577b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1544 : PLift (G 96181 96259) := ⟨bs [0xd77b5,0x777c7,0x577d3,0x577dd,0xb77df,0x777e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1545 : PLift (G 96259 96323) := ⟨bs [0x57803,0xb7807,0x5780d,0x77819,0x177821,0x57825] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1546 : PLift (G 96323 96401) := ⟨bs [0x57843,0x77849,0x15784b,0xb7851,0x77861,0x77879] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1547 : PLift (G 96401 96461) := ⟨bs [0x77891,0xd78a3,0x1778af,0x578bb,0x578c3,0xb78c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1548 : PLift (G 96461 96517) := ⟨bs [0x578cd,0x1578d5,0x1778df,0x778e7,0xb78ed,0x778f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1549 : PLift (G 96517 96589) := ⟨bs [0x57905,0xb790f,0xb7929,0x5792d,0x57945,0x5794b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1550 : PLift (G 96589 96697) := ⟨bs [0xd794d,0x177959,0x57983,0xf7995,0x5799b,0xf799f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1551 : PLift (G 96697 96757) := ⟨bs [0xf79b9,0x779bf,0x579db,0x779e1,0x579e3,0x579ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1552 : PLift (G 96757 96799) := ⟨bs [0xb79f5,0xb79fb,0x2d7a01,0x57a0b,0x57a13,0x57a1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1553 : PLift (G 96799 96857) := ⟨bs [0xd7a1f,0x57a35,0xb7a37,0x57a3b,0x77a4f,0x57a53] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1554 : PLift (G 96857 96959) := ⟨bs [0x77a59,0x57a7d,0x57a8b,0x177a8f,0x57aa3,0x77ab9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1555 : PLift (G 96959 97003) := ⟨bs [0xf7abf,0x57acd,0x77ad3,0x57add,0x57ae5,0x77ae9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1556 : PLift (G 97003 97103) := ⟨bs [0xf7aeb,0xb7aef,0x57afd,0x77b0f,0x77b31,0xf7b39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1557 : PLift (G 97103 97169) := ⟨bs [0xb7b4f,0x57b5d,0xb7b67,0x1b7b7f,0x57b85,0x77b87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1558 : PLift (G 97169 97241) := ⟨bs [0x77b91,0x157b93,0xb7b99,0x57ba3,0xb7bbd,0xd7bcf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1559 : PLift (G 97241 97367) := ⟨bs [0x77bd9,0xd7beb,0x57c03,0x57c15,0x77c17,0xb7c2f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1560 : PLift (G 97367 97397) := ⟨bs [0xb7c57,0xf7c59,0x57c5d,0x57c63,0x57c65,0x57c6b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1561 : PLift (G 97397 97463) := ⟨bs [0x57c75,0x77c8f,0xd7c95,0x4b7ca1,0x57cad,0x57cb3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1562 : PLift (G 97463 97549) := ⟨bs [0xb7cb7,0x57cdb,0xf7cdd,0xf7ce7,0x57cf3,0x57d0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1563 : PLift (G 97549 97583) := ⟨bs [0x57d0d,0x77d11,0x177d19,0x57d23,0x77d29,0x57d2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1564 : PLift (G 97583 97673) := ⟨bs [0xb7d2f,0xb7d47,0x237d49,0x57d4d,0x77d71,0x57d73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1565 : PLift (G 97673 97787) := ⟨bs [0x77d89,0xb7d97,0x177daf,0x1b7dc1,0x77deb,0x237df1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1566 : PLift (G 97787 97847) := ⟨bs [0x57dfb,0x57dfd,0x57e15,0x57e25,0xd7e31,0x57e33] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1567 : PLift (G 97847 97883) := ⟨bs [0xb7e37,0x1b7e39,0x57e43,0x57e45,0xf7e4f,0xd7e57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1568 : PLift (G 97883 97967) := ⟨bs [0x57e5b,0x2f7e7f,0x77e87,0x57e8b,0xb7e97,0x77ea9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1569 : PLift (G 97967 98041) := ⟨bs [0xb7eaf,0x57eb5,0x57ec3,0x77ed9,0x157edb,0xf7ee1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1570 : PLift (G 98041 98129) := ⟨bs [0x1b7ef9,0xb7eff,0x77f09,0xd7f21,0x57f35,0x57f4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1571 : PLift (G 98129 98227) := ⟨bs [0x77f51,0xb7f5f,0x57f83,0xb7f9f,0x57fa5,0x57fad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1572 : PLift (G 98227 98317) := ⟨bs [0x77fb3,0x57fcb,0x157fd1,0x57fdd,0x77ff9,0x57ffb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1573 : PLift (G 98317 98377) := ⟨bs [0xd800d,0x78011,0x78013,0xb8017,0x5802b,0x78041] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1574 : PLift (G 98377 98429) := ⟨bs [0xb8049,0x58053,0x58055,0xd8067,0x5806b,0x58073] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1575 : PLift (G 98429 98479) := ⟨bs [0x5807d,0x5808b,0x58095,0x5809b,0x780a3,0x1580a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1576 : PLift (G 98479 98561) := ⟨bs [0x780af,0xf80bb,0x580cb,0xf80d7,0x580e5,0xb80ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1577 : PLift (G 98561 98639) := ⟨bs [0x78101,0x58103,0x5810d,0x58125,0xf813d,0x58143] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1578 : PLift (G 98639 98713) := ⟨bs [0xf814f,0x238151,0xb8167,0x5816d,0xf8181,0x1b8197] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1579 : PLift (G 98713 98779) := ⟨bs [0xb8199,0x5819d,0x781a9,0x581ab,0xb81b1,0x581d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1580 : PLift (G 98779 98867) := ⟨bs [0x581db,0x781f1,0xb81f7,0x2381f9,0x58215,0x78221] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1581 : PLift (G 98867 98899) := ⟨bs [0x58233,0x58235,0x78239,0x78247,0x5824d,0x78251] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1582 : PLift (G 98899 98947) := ⟨bs [0x58253,0x5825d,0x19825f,0xb826f,0x178271,0x5827b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1583 : PLift (G 98947 99013) := ⟨bs [0x78283,0x158289,0x58293,0x782a5,0x782b1,0x2782b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1584 : PLift (G 99013 99083) := ⟨bs [0xd82c5,0x782c9,0xb82cf,0xd82e1,0x582ed,0x78307] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1585 : PLift (G 99083 99133) := ⟨bs [0x5830b,0x78311,0x7831f,0xd8325,0x17832f,0xd833b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1586 : PLift (G 99133 99191) := ⟨bs [0x5833d,0x78341,0x58343,0x5834d,0x58365,0xf836d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1587 : PLift (G 99191 99259) := ⟨bs [0x178377,0x78397,0x783a1,0x1783a9,0x1583b3,0x783b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1588 : PLift (G 99259 99367) := ⟨bs [0x583bb,0x583cd,0x3583d9,0x583f5,0x58413,0x178415] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1589 : PLift (G 99367 99409) := ⟨bs [0x78427,0x5842b,0x78431,0xd843f,0x58445,0x78449] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1590 : PLift (G 99409 99523) := ⟨bs [0x178451,0x1b8467,0x7846f,0x5848d,0x7849f,0x784a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1591 : PLift (G 99523 99571) := ⟨bs [0xb84c3,0xb84c7,0xf84c9,0xf84df,0x784e7,0x584eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1592 : PLift (G 99571 99643) := ⟨bs [0x584f3,0xb84f9,0x584fd,0x78517,0x5851b,0xb8527] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1593 : PLift (G 99643 99709) := ⟨bs [0x7853b,0x5854d,0x58553,0xd855f,0x78569,0x5857b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1594 : PLift (G 99709 99767) := ⟨bs [0x15857d,0x78581,0xf8587,0x178589,0x58595,0x785b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1595 : PLift (G 99767 99829) := ⟨bs [0xb85b7,0x585cb,0xb85d1,0x785e1,0xb85e9,0x2b85ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1596 : PLift (G 99829 99881) := ⟨bs [0x585f5,0x785f9,0x1785ff,0x58613,0x7861f,0x58625] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1597 : PLift (G 99881 99971) := ⟨bs [0xd8629,0x5863d,0x58643,0x58653,0x78659,0x3f8679] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def block1598 : PLift (G 99971 100000) := ⟨bs [0x58683,0x58695,0xd8697] (by decide +kernel)⟩

set_option maxHeartbeats 0 in
theorem finite_range : G 3 100000 :=
  (j (j (j (j (j (j (j (j (j (j block0.down (j block1.down block2.down)) (j block3.down (j block4.down block5.down))) (j (j block6.down (j block7.down block8.down)) (j block9.down (j block10.down block11.down)))) (j (j (j block12.down (j block13.down block14.down)) (j block15.down (j block16.down block17.down))) (j (j block18.down (j block19.down block20.down)) (j block21.down (j block22.down block23.down))))) (j (j (j (j block24.down (j block25.down block26.down)) (j block27.down (j block28.down block29.down))) (j (j block30.down (j block31.down block32.down)) (j block33.down (j block34.down block35.down)))) (j (j (j block36.down (j block37.down block38.down)) (j block39.down (j block40.down block41.down))) (j (j block42.down (j block43.down block44.down)) (j (j block45.down block46.down) (j block47.down block48.down)))))) (j (j (j (j (j block49.down (j block50.down block51.down)) (j block52.down (j block53.down block54.down))) (j (j block55.down (j block56.down block57.down)) (j block58.down (j block59.down block60.down)))) (j (j (j block61.down (j block62.down block63.down)) (j block64.down (j block65.down block66.down))) (j (j block67.down (j block68.down block69.down)) (j (j block70.down block71.down) (j block72.down block73.down))))) (j (j (j (j block74.down (j block75.down block76.down)) (j block77.down (j block78.down block79.down))) (j (j block80.down (j block81.down block82.down)) (j block83.down (j block84.down block85.down)))) (j (j (j block86.down (j block87.down block88.down)) (j block89.down (j block90.down block91.down))) (j (j block92.down (j block93.down block94.down)) (j (j block95.down block96.down) (j block97.down block98.down))))))) (j (j (j (j (j (j block99.down (j block100.down block101.down)) (j block102.down (j block103.down block104.down))) (j (j block105.down (j block106.down block107.down)) (j block108.down (j block109.down block110.down)))) (j (j (j block111.down (j block112.down block113.down)) (j block114.down (j block115.down block116.down))) (j (j block117.down (j block118.down block119.down)) (j (j block120.down block121.down) (j block122.down block123.down))))) (j (j (j (j block124.down (j block125.down block126.down)) (j block127.down (j block128.down block129.down))) (j (j block130.down (j block131.down block132.down)) (j block133.down (j block134.down block135.down)))) (j (j (j block136.down (j block137.down block138.down)) (j block139.down (j block140.down block141.down))) (j (j block142.down (j block143.down block144.down)) (j (j block145.down block146.down) (j block147.down block148.down)))))) (j (j (j (j (j block149.down (j block150.down block151.down)) (j block152.down (j block153.down block154.down))) (j (j block155.down (j block156.down block157.down)) (j block158.down (j block159.down block160.down)))) (j (j (j block161.down (j block162.down block163.down)) (j block164.down (j block165.down block166.down))) (j (j block167.down (j block168.down block169.down)) (j (j block170.down block171.down) (j block172.down block173.down))))) (j (j (j (j block174.down (j block175.down block176.down)) (j block177.down (j block178.down block179.down))) (j (j block180.down (j block181.down block182.down)) (j block183.down (j block184.down block185.down)))) (j (j (j block186.down (j block187.down block188.down)) (j block189.down (j block190.down block191.down))) (j (j block192.down (j block193.down block194.down)) (j (j block195.down block196.down) (j block197.down block198.down)))))))) (j (j (j (j (j (j (j block199.down (j block200.down block201.down)) (j block202.down (j block203.down block204.down))) (j (j block205.down (j block206.down block207.down)) (j block208.down (j block209.down block210.down)))) (j (j (j block211.down (j block212.down block213.down)) (j block214.down (j block215.down block216.down))) (j (j block217.down (j block218.down block219.down)) (j (j block220.down block221.down) (j block222.down block223.down))))) (j (j (j (j block224.down (j block225.down block226.down)) (j block227.down (j block228.down block229.down))) (j (j block230.down (j block231.down block232.down)) (j block233.down (j block234.down block235.down)))) (j (j (j block236.down (j block237.down block238.down)) (j block239.down (j block240.down block241.down))) (j (j block242.down (j block243.down block244.down)) (j (j block245.down block246.down) (j block247.down block248.down)))))) (j (j (j (j (j block249.down (j block250.down block251.down)) (j block252.down (j block253.down block254.down))) (j (j block255.down (j block256.down block257.down)) (j block258.down (j block259.down block260.down)))) (j (j (j block261.down (j block262.down block263.down)) (j block264.down (j block265.down block266.down))) (j (j block267.down (j block268.down block269.down)) (j (j block270.down block271.down) (j block272.down block273.down))))) (j (j (j (j block274.down (j block275.down block276.down)) (j block277.down (j block278.down block279.down))) (j (j block280.down (j block281.down block282.down)) (j block283.down (j block284.down block285.down)))) (j (j (j block286.down (j block287.down block288.down)) (j block289.down (j block290.down block291.down))) (j (j block292.down (j block293.down block294.down)) (j (j block295.down block296.down) (j block297.down block298.down))))))) (j (j (j (j (j (j block299.down (j block300.down block301.down)) (j block302.down (j block303.down block304.down))) (j (j block305.down (j block306.down block307.down)) (j block308.down (j block309.down block310.down)))) (j (j (j block311.down (j block312.down block313.down)) (j block314.down (j block315.down block316.down))) (j (j block317.down (j block318.down block319.down)) (j (j block320.down block321.down) (j block322.down block323.down))))) (j (j (j (j block324.down (j block325.down block326.down)) (j block327.down (j block328.down block329.down))) (j (j block330.down (j block331.down block332.down)) (j block333.down (j block334.down block335.down)))) (j (j (j block336.down (j block337.down block338.down)) (j block339.down (j block340.down block341.down))) (j (j block342.down (j block343.down block344.down)) (j (j block345.down block346.down) (j block347.down block348.down)))))) (j (j (j (j (j block349.down (j block350.down block351.down)) (j block352.down (j block353.down block354.down))) (j (j block355.down (j block356.down block357.down)) (j block358.down (j block359.down block360.down)))) (j (j (j block361.down (j block362.down block363.down)) (j block364.down (j block365.down block366.down))) (j (j block367.down (j block368.down block369.down)) (j (j block370.down block371.down) (j block372.down block373.down))))) (j (j (j (j block374.down (j block375.down block376.down)) (j block377.down (j block378.down block379.down))) (j (j block380.down (j block381.down block382.down)) (j block383.down (j block384.down block385.down)))) (j (j (j block386.down (j block387.down block388.down)) (j block389.down (j block390.down block391.down))) (j (j block392.down (j block393.down block394.down)) (j (j block395.down block396.down) (j block397.down block398.down))))))))) (j (j (j (j (j (j (j (j block399.down (j block400.down block401.down)) (j block402.down (j block403.down block404.down))) (j (j block405.down (j block406.down block407.down)) (j block408.down (j block409.down block410.down)))) (j (j (j block411.down (j block412.down block413.down)) (j block414.down (j block415.down block416.down))) (j (j block417.down (j block418.down block419.down)) (j (j block420.down block421.down) (j block422.down block423.down))))) (j (j (j (j block424.down (j block425.down block426.down)) (j block427.down (j block428.down block429.down))) (j (j block430.down (j block431.down block432.down)) (j block433.down (j block434.down block435.down)))) (j (j (j block436.down (j block437.down block438.down)) (j block439.down (j block440.down block441.down))) (j (j block442.down (j block443.down block444.down)) (j (j block445.down block446.down) (j block447.down block448.down)))))) (j (j (j (j (j block449.down (j block450.down block451.down)) (j block452.down (j block453.down block454.down))) (j (j block455.down (j block456.down block457.down)) (j block458.down (j block459.down block460.down)))) (j (j (j block461.down (j block462.down block463.down)) (j block464.down (j block465.down block466.down))) (j (j block467.down (j block468.down block469.down)) (j (j block470.down block471.down) (j block472.down block473.down))))) (j (j (j (j block474.down (j block475.down block476.down)) (j block477.down (j block478.down block479.down))) (j (j block480.down (j block481.down block482.down)) (j block483.down (j block484.down block485.down)))) (j (j (j block486.down (j block487.down block488.down)) (j block489.down (j block490.down block491.down))) (j (j block492.down (j block493.down block494.down)) (j (j block495.down block496.down) (j block497.down block498.down))))))) (j (j (j (j (j (j block499.down (j block500.down block501.down)) (j block502.down (j block503.down block504.down))) (j (j block505.down (j block506.down block507.down)) (j block508.down (j block509.down block510.down)))) (j (j (j block511.down (j block512.down block513.down)) (j block514.down (j block515.down block516.down))) (j (j block517.down (j block518.down block519.down)) (j (j block520.down block521.down) (j block522.down block523.down))))) (j (j (j (j block524.down (j block525.down block526.down)) (j block527.down (j block528.down block529.down))) (j (j block530.down (j block531.down block532.down)) (j block533.down (j block534.down block535.down)))) (j (j (j block536.down (j block537.down block538.down)) (j block539.down (j block540.down block541.down))) (j (j block542.down (j block543.down block544.down)) (j (j block545.down block546.down) (j block547.down block548.down)))))) (j (j (j (j (j block549.down (j block550.down block551.down)) (j block552.down (j block553.down block554.down))) (j (j block555.down (j block556.down block557.down)) (j block558.down (j block559.down block560.down)))) (j (j (j block561.down (j block562.down block563.down)) (j block564.down (j block565.down block566.down))) (j (j block567.down (j block568.down block569.down)) (j (j block570.down block571.down) (j block572.down block573.down))))) (j (j (j (j block574.down (j block575.down block576.down)) (j block577.down (j block578.down block579.down))) (j (j block580.down (j block581.down block582.down)) (j block583.down (j block584.down block585.down)))) (j (j (j block586.down (j block587.down block588.down)) (j block589.down (j block590.down block591.down))) (j (j block592.down (j block593.down block594.down)) (j (j block595.down block596.down) (j block597.down block598.down)))))))) (j (j (j (j (j (j (j block599.down (j block600.down block601.down)) (j block602.down (j block603.down block604.down))) (j (j block605.down (j block606.down block607.down)) (j block608.down (j block609.down block610.down)))) (j (j (j block611.down (j block612.down block613.down)) (j block614.down (j block615.down block616.down))) (j (j block617.down (j block618.down block619.down)) (j (j block620.down block621.down) (j block622.down block623.down))))) (j (j (j (j block624.down (j block625.down block626.down)) (j block627.down (j block628.down block629.down))) (j (j block630.down (j block631.down block632.down)) (j block633.down (j block634.down block635.down)))) (j (j (j block636.down (j block637.down block638.down)) (j block639.down (j block640.down block641.down))) (j (j block642.down (j block643.down block644.down)) (j (j block645.down block646.down) (j block647.down block648.down)))))) (j (j (j (j (j block649.down (j block650.down block651.down)) (j block652.down (j block653.down block654.down))) (j (j block655.down (j block656.down block657.down)) (j block658.down (j block659.down block660.down)))) (j (j (j block661.down (j block662.down block663.down)) (j block664.down (j block665.down block666.down))) (j (j block667.down (j block668.down block669.down)) (j (j block670.down block671.down) (j block672.down block673.down))))) (j (j (j (j block674.down (j block675.down block676.down)) (j block677.down (j block678.down block679.down))) (j (j block680.down (j block681.down block682.down)) (j block683.down (j block684.down block685.down)))) (j (j (j block686.down (j block687.down block688.down)) (j block689.down (j block690.down block691.down))) (j (j block692.down (j block693.down block694.down)) (j (j block695.down block696.down) (j block697.down block698.down))))))) (j (j (j (j (j (j block699.down (j block700.down block701.down)) (j block702.down (j block703.down block704.down))) (j (j block705.down (j block706.down block707.down)) (j block708.down (j block709.down block710.down)))) (j (j (j block711.down (j block712.down block713.down)) (j block714.down (j block715.down block716.down))) (j (j block717.down (j block718.down block719.down)) (j (j block720.down block721.down) (j block722.down block723.down))))) (j (j (j (j block724.down (j block725.down block726.down)) (j block727.down (j block728.down block729.down))) (j (j block730.down (j block731.down block732.down)) (j block733.down (j block734.down block735.down)))) (j (j (j block736.down (j block737.down block738.down)) (j block739.down (j block740.down block741.down))) (j (j block742.down (j block743.down block744.down)) (j (j block745.down block746.down) (j block747.down block748.down)))))) (j (j (j (j (j block749.down (j block750.down block751.down)) (j block752.down (j block753.down block754.down))) (j (j block755.down (j block756.down block757.down)) (j block758.down (j block759.down block760.down)))) (j (j (j block761.down (j block762.down block763.down)) (j block764.down (j block765.down block766.down))) (j (j block767.down (j block768.down block769.down)) (j (j block770.down block771.down) (j block772.down block773.down))))) (j (j (j (j block774.down (j block775.down block776.down)) (j block777.down (j block778.down block779.down))) (j (j block780.down (j block781.down block782.down)) (j block783.down (j block784.down block785.down)))) (j (j (j block786.down (j block787.down block788.down)) (j block789.down (j block790.down block791.down))) (j (j block792.down (j block793.down block794.down)) (j (j block795.down block796.down) (j block797.down block798.down)))))))))) (j (j (j (j (j (j (j (j (j block799.down (j block800.down block801.down)) (j block802.down (j block803.down block804.down))) (j (j block805.down (j block806.down block807.down)) (j block808.down (j block809.down block810.down)))) (j (j (j block811.down (j block812.down block813.down)) (j block814.down (j block815.down block816.down))) (j (j block817.down (j block818.down block819.down)) (j (j block820.down block821.down) (j block822.down block823.down))))) (j (j (j (j block824.down (j block825.down block826.down)) (j block827.down (j block828.down block829.down))) (j (j block830.down (j block831.down block832.down)) (j block833.down (j block834.down block835.down)))) (j (j (j block836.down (j block837.down block838.down)) (j block839.down (j block840.down block841.down))) (j (j block842.down (j block843.down block844.down)) (j (j block845.down block846.down) (j block847.down block848.down)))))) (j (j (j (j (j block849.down (j block850.down block851.down)) (j block852.down (j block853.down block854.down))) (j (j block855.down (j block856.down block857.down)) (j block858.down (j block859.down block860.down)))) (j (j (j block861.down (j block862.down block863.down)) (j block864.down (j block865.down block866.down))) (j (j block867.down (j block868.down block869.down)) (j (j block870.down block871.down) (j block872.down block873.down))))) (j (j (j (j block874.down (j block875.down block876.down)) (j block877.down (j block878.down block879.down))) (j (j block880.down (j block881.down block882.down)) (j block883.down (j block884.down block885.down)))) (j (j (j block886.down (j block887.down block888.down)) (j block889.down (j block890.down block891.down))) (j (j block892.down (j block893.down block894.down)) (j (j block895.down block896.down) (j block897.down block898.down))))))) (j (j (j (j (j (j block899.down (j block900.down block901.down)) (j block902.down (j block903.down block904.down))) (j (j block905.down (j block906.down block907.down)) (j block908.down (j block909.down block910.down)))) (j (j (j block911.down (j block912.down block913.down)) (j block914.down (j block915.down block916.down))) (j (j block917.down (j block918.down block919.down)) (j (j block920.down block921.down) (j block922.down block923.down))))) (j (j (j (j block924.down (j block925.down block926.down)) (j block927.down (j block928.down block929.down))) (j (j block930.down (j block931.down block932.down)) (j block933.down (j block934.down block935.down)))) (j (j (j block936.down (j block937.down block938.down)) (j block939.down (j block940.down block941.down))) (j (j block942.down (j block943.down block944.down)) (j (j block945.down block946.down) (j block947.down block948.down)))))) (j (j (j (j (j block949.down (j block950.down block951.down)) (j block952.down (j block953.down block954.down))) (j (j block955.down (j block956.down block957.down)) (j block958.down (j block959.down block960.down)))) (j (j (j block961.down (j block962.down block963.down)) (j block964.down (j block965.down block966.down))) (j (j block967.down (j block968.down block969.down)) (j (j block970.down block971.down) (j block972.down block973.down))))) (j (j (j (j block974.down (j block975.down block976.down)) (j block977.down (j block978.down block979.down))) (j (j block980.down (j block981.down block982.down)) (j block983.down (j block984.down block985.down)))) (j (j (j block986.down (j block987.down block988.down)) (j block989.down (j block990.down block991.down))) (j (j block992.down (j block993.down block994.down)) (j (j block995.down block996.down) (j block997.down block998.down)))))))) (j (j (j (j (j (j (j block999.down (j block1000.down block1001.down)) (j block1002.down (j block1003.down block1004.down))) (j (j block1005.down (j block1006.down block1007.down)) (j block1008.down (j block1009.down block1010.down)))) (j (j (j block1011.down (j block1012.down block1013.down)) (j block1014.down (j block1015.down block1016.down))) (j (j block1017.down (j block1018.down block1019.down)) (j (j block1020.down block1021.down) (j block1022.down block1023.down))))) (j (j (j (j block1024.down (j block1025.down block1026.down)) (j block1027.down (j block1028.down block1029.down))) (j (j block1030.down (j block1031.down block1032.down)) (j block1033.down (j block1034.down block1035.down)))) (j (j (j block1036.down (j block1037.down block1038.down)) (j block1039.down (j block1040.down block1041.down))) (j (j block1042.down (j block1043.down block1044.down)) (j (j block1045.down block1046.down) (j block1047.down block1048.down)))))) (j (j (j (j (j block1049.down (j block1050.down block1051.down)) (j block1052.down (j block1053.down block1054.down))) (j (j block1055.down (j block1056.down block1057.down)) (j block1058.down (j block1059.down block1060.down)))) (j (j (j block1061.down (j block1062.down block1063.down)) (j block1064.down (j block1065.down block1066.down))) (j (j block1067.down (j block1068.down block1069.down)) (j (j block1070.down block1071.down) (j block1072.down block1073.down))))) (j (j (j (j block1074.down (j block1075.down block1076.down)) (j block1077.down (j block1078.down block1079.down))) (j (j block1080.down (j block1081.down block1082.down)) (j block1083.down (j block1084.down block1085.down)))) (j (j (j block1086.down (j block1087.down block1088.down)) (j block1089.down (j block1090.down block1091.down))) (j (j block1092.down (j block1093.down block1094.down)) (j (j block1095.down block1096.down) (j block1097.down block1098.down))))))) (j (j (j (j (j (j block1099.down (j block1100.down block1101.down)) (j block1102.down (j block1103.down block1104.down))) (j (j block1105.down (j block1106.down block1107.down)) (j block1108.down (j block1109.down block1110.down)))) (j (j (j block1111.down (j block1112.down block1113.down)) (j block1114.down (j block1115.down block1116.down))) (j (j block1117.down (j block1118.down block1119.down)) (j (j block1120.down block1121.down) (j block1122.down block1123.down))))) (j (j (j (j block1124.down (j block1125.down block1126.down)) (j block1127.down (j block1128.down block1129.down))) (j (j block1130.down (j block1131.down block1132.down)) (j block1133.down (j block1134.down block1135.down)))) (j (j (j block1136.down (j block1137.down block1138.down)) (j block1139.down (j block1140.down block1141.down))) (j (j block1142.down (j block1143.down block1144.down)) (j (j block1145.down block1146.down) (j block1147.down block1148.down)))))) (j (j (j (j (j block1149.down (j block1150.down block1151.down)) (j block1152.down (j block1153.down block1154.down))) (j (j block1155.down (j block1156.down block1157.down)) (j block1158.down (j block1159.down block1160.down)))) (j (j (j block1161.down (j block1162.down block1163.down)) (j block1164.down (j block1165.down block1166.down))) (j (j block1167.down (j block1168.down block1169.down)) (j (j block1170.down block1171.down) (j block1172.down block1173.down))))) (j (j (j (j block1174.down (j block1175.down block1176.down)) (j block1177.down (j block1178.down block1179.down))) (j (j block1180.down (j block1181.down block1182.down)) (j block1183.down (j block1184.down block1185.down)))) (j (j (j block1186.down (j block1187.down block1188.down)) (j block1189.down (j block1190.down block1191.down))) (j (j block1192.down (j block1193.down block1194.down)) (j (j block1195.down block1196.down) (j block1197.down block1198.down))))))))) (j (j (j (j (j (j (j (j block1199.down (j block1200.down block1201.down)) (j block1202.down (j block1203.down block1204.down))) (j (j block1205.down (j block1206.down block1207.down)) (j block1208.down (j block1209.down block1210.down)))) (j (j (j block1211.down (j block1212.down block1213.down)) (j block1214.down (j block1215.down block1216.down))) (j (j block1217.down (j block1218.down block1219.down)) (j (j block1220.down block1221.down) (j block1222.down block1223.down))))) (j (j (j (j block1224.down (j block1225.down block1226.down)) (j block1227.down (j block1228.down block1229.down))) (j (j block1230.down (j block1231.down block1232.down)) (j block1233.down (j block1234.down block1235.down)))) (j (j (j block1236.down (j block1237.down block1238.down)) (j block1239.down (j block1240.down block1241.down))) (j (j block1242.down (j block1243.down block1244.down)) (j (j block1245.down block1246.down) (j block1247.down block1248.down)))))) (j (j (j (j (j block1249.down (j block1250.down block1251.down)) (j block1252.down (j block1253.down block1254.down))) (j (j block1255.down (j block1256.down block1257.down)) (j block1258.down (j block1259.down block1260.down)))) (j (j (j block1261.down (j block1262.down block1263.down)) (j block1264.down (j block1265.down block1266.down))) (j (j block1267.down (j block1268.down block1269.down)) (j (j block1270.down block1271.down) (j block1272.down block1273.down))))) (j (j (j (j block1274.down (j block1275.down block1276.down)) (j block1277.down (j block1278.down block1279.down))) (j (j block1280.down (j block1281.down block1282.down)) (j block1283.down (j block1284.down block1285.down)))) (j (j (j block1286.down (j block1287.down block1288.down)) (j block1289.down (j block1290.down block1291.down))) (j (j block1292.down (j block1293.down block1294.down)) (j (j block1295.down block1296.down) (j block1297.down block1298.down))))))) (j (j (j (j (j (j block1299.down (j block1300.down block1301.down)) (j block1302.down (j block1303.down block1304.down))) (j (j block1305.down (j block1306.down block1307.down)) (j block1308.down (j block1309.down block1310.down)))) (j (j (j block1311.down (j block1312.down block1313.down)) (j block1314.down (j block1315.down block1316.down))) (j (j block1317.down (j block1318.down block1319.down)) (j (j block1320.down block1321.down) (j block1322.down block1323.down))))) (j (j (j (j block1324.down (j block1325.down block1326.down)) (j block1327.down (j block1328.down block1329.down))) (j (j block1330.down (j block1331.down block1332.down)) (j block1333.down (j block1334.down block1335.down)))) (j (j (j block1336.down (j block1337.down block1338.down)) (j block1339.down (j block1340.down block1341.down))) (j (j block1342.down (j block1343.down block1344.down)) (j (j block1345.down block1346.down) (j block1347.down block1348.down)))))) (j (j (j (j (j block1349.down (j block1350.down block1351.down)) (j block1352.down (j block1353.down block1354.down))) (j (j block1355.down (j block1356.down block1357.down)) (j block1358.down (j block1359.down block1360.down)))) (j (j (j block1361.down (j block1362.down block1363.down)) (j block1364.down (j block1365.down block1366.down))) (j (j block1367.down (j block1368.down block1369.down)) (j (j block1370.down block1371.down) (j block1372.down block1373.down))))) (j (j (j (j block1374.down (j block1375.down block1376.down)) (j block1377.down (j block1378.down block1379.down))) (j (j block1380.down (j block1381.down block1382.down)) (j block1383.down (j block1384.down block1385.down)))) (j (j (j block1386.down (j block1387.down block1388.down)) (j block1389.down (j block1390.down block1391.down))) (j (j block1392.down (j block1393.down block1394.down)) (j (j block1395.down block1396.down) (j block1397.down block1398.down)))))))) (j (j (j (j (j (j (j block1399.down (j block1400.down block1401.down)) (j block1402.down (j block1403.down block1404.down))) (j (j block1405.down (j block1406.down block1407.down)) (j block1408.down (j block1409.down block1410.down)))) (j (j (j block1411.down (j block1412.down block1413.down)) (j block1414.down (j block1415.down block1416.down))) (j (j block1417.down (j block1418.down block1419.down)) (j (j block1420.down block1421.down) (j block1422.down block1423.down))))) (j (j (j (j block1424.down (j block1425.down block1426.down)) (j block1427.down (j block1428.down block1429.down))) (j (j block1430.down (j block1431.down block1432.down)) (j block1433.down (j block1434.down block1435.down)))) (j (j (j block1436.down (j block1437.down block1438.down)) (j block1439.down (j block1440.down block1441.down))) (j (j block1442.down (j block1443.down block1444.down)) (j (j block1445.down block1446.down) (j block1447.down block1448.down)))))) (j (j (j (j (j block1449.down (j block1450.down block1451.down)) (j block1452.down (j block1453.down block1454.down))) (j (j block1455.down (j block1456.down block1457.down)) (j block1458.down (j block1459.down block1460.down)))) (j (j (j block1461.down (j block1462.down block1463.down)) (j block1464.down (j block1465.down block1466.down))) (j (j block1467.down (j block1468.down block1469.down)) (j (j block1470.down block1471.down) (j block1472.down block1473.down))))) (j (j (j (j block1474.down (j block1475.down block1476.down)) (j block1477.down (j block1478.down block1479.down))) (j (j block1480.down (j block1481.down block1482.down)) (j block1483.down (j block1484.down block1485.down)))) (j (j (j block1486.down (j block1487.down block1488.down)) (j block1489.down (j block1490.down block1491.down))) (j (j block1492.down (j block1493.down block1494.down)) (j (j block1495.down block1496.down) (j block1497.down block1498.down))))))) (j (j (j (j (j (j block1499.down (j block1500.down block1501.down)) (j block1502.down (j block1503.down block1504.down))) (j (j block1505.down (j block1506.down block1507.down)) (j block1508.down (j block1509.down block1510.down)))) (j (j (j block1511.down (j block1512.down block1513.down)) (j block1514.down (j block1515.down block1516.down))) (j (j block1517.down (j block1518.down block1519.down)) (j (j block1520.down block1521.down) (j block1522.down block1523.down))))) (j (j (j (j block1524.down (j block1525.down block1526.down)) (j block1527.down (j block1528.down block1529.down))) (j (j block1530.down (j block1531.down block1532.down)) (j block1533.down (j block1534.down block1535.down)))) (j (j (j block1536.down (j block1537.down block1538.down)) (j block1539.down (j block1540.down block1541.down))) (j (j block1542.down (j block1543.down block1544.down)) (j (j block1545.down block1546.down) (j block1547.down block1548.down)))))) (j (j (j (j (j block1549.down (j block1550.down block1551.down)) (j block1552.down (j block1553.down block1554.down))) (j (j block1555.down (j block1556.down block1557.down)) (j block1558.down (j block1559.down block1560.down)))) (j (j (j block1561.down (j block1562.down block1563.down)) (j block1564.down (j block1565.down block1566.down))) (j (j block1567.down (j block1568.down block1569.down)) (j (j block1570.down block1571.down) (j block1572.down block1573.down))))) (j (j (j (j block1574.down (j block1575.down block1576.down)) (j block1577.down (j block1578.down block1579.down))) (j (j block1580.down (j block1581.down block1582.down)) (j block1583.down (j block1584.down block1585.down)))) (j (j (j block1586.down (j block1587.down block1588.down)) (j block1589.down (j block1590.down block1591.down))) (j (j block1592.down (j block1593.down block1594.down)) (j (j block1595.down block1596.down) (j block1597.down block1598.down)))))))))))

end ThetaFiniteRange.Packed

theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_1_1_R1.H1 := by
  intro p hp hlow hhigh
  have ho : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))
  rw [← OMA.R_Arxiv_2501_03234_conjecture_1_1_R1.S_eq_T p hp ho]
  exact ThetaFiniteRange.Packed.finite_range p (by omega) hhigh hp
