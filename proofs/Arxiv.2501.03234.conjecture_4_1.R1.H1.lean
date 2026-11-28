import OMAReductions.R_Arxiv_2501_03234_conjecture_4_1_R1
import Mathlib.Tactic

/-
Exact finite companion step of @rickmanelius parent PR#21155.
The target is nonempty and substantive, but most certificate work reuses
our own merged PR#18042. The new small range covers all prime candidates
7..3119 with piecewise thresholds. No infinite lower bound is proved.
All proof code is independently authored in this workspace; no external
proof implementation is copied. See the source's retained references and
the PR body for the precise contextual credits.
-/


/-!
Independently authored packed theta-sum certificates. No external proof code is
ported. Classical source: Berndt, Bhat, Meyer, Xie, Zaharescu, An Arithmetic Sum
Associated with the Classical Theta Function, Results Math 81:25 (2026),
DOI 10.1007/s00025-025-02584-2 (refereed).

Related agent work credited: @sebastianbachmaier PRs #5611/#6138 for sign and
recurrence context; @steveDOTdigital PR #7053 for the existing cyclic-parity
formulation and a different word/reversal packing; @ahmeterdempmk PR #12097 for
that packing's extraction step; @Ehdunhackme notes #60862/#61371/#61717 for an
independent native replay and those references. Our code, candidate parameters
and arithmetic validator are independently written. No novelty is claimed for
cyclic correlation or generic coefficient extraction. The exact finite target
comes from @LordMike's merged reduction PR #12031.
-/

namespace ThetaLongHaul
open Finset

def floorSign (a b : ℕ) : ℤ :=
  ∑ j ∈ Ico 1 b, (-1 : ℤ) ^ (a * j / b)

lemma complementary_quotients (b h j : ℕ) (hb : 0 < b) (hh : h ≤ b)
    (hnd : ¬ b ∣ h * j) :
    (b - h) * j / b + h * j / b + 1 = j := by
  have hsum : (b - h) * j + h * j = b * j := by
    rw [← add_mul, Nat.sub_add_cancel hh]
  have hpos : 0 < h * j % b := Nat.pos_of_ne_zero (fun hz => hnd (Nat.dvd_of_mod_eq_zero hz))
  have hx := Nat.div_add_mod ((b - h) * j) b
  have hy := Nat.div_add_mod (h * j) b
  have hq := Nat.add_div (a := (b - h) * j) (b := h * j) hb
  rw [hsum, Nat.mul_div_cancel_left _ hb] at hq
  by_cases hc : b ≤ (b - h) * j % b + h * j % b
  · simpa only [if_pos hc] using hq.symm
  · simp only [if_neg hc, add_zero] at hq
    have hz : (b - h) * j % b + h * j % b = 0 := by
      nlinarith [hsum]
    omega

lemma prime_quotient_reflection (p a j : ℕ) (hp : p.Prime)
    (ha : a ∈ Ico 1 p) (hj : j ∈ Ico 1 p) :
    (p - a) * j / p + a * j / p + 1 = j := by
  simp only [mem_Ico] at ha hj
  apply complementary_quotients p a j hp.pos ha.2.le
  intro hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact (not_le_of_gt ha.2) (Nat.le_of_dvd ha.1 hd)
  · exact (not_le_of_gt hj.2) (Nat.le_of_dvd hj.1 hd)

lemma floor_nat_ratio (a j p : ℕ) : ⌊(a * j : ℚ) / p⌋₊ = a * j / p := by
  rw [← Nat.cast_mul, Nat.floor_div_eq_div]

lemma sum_reflection (p : ℕ) (f : ℕ → ℤ) :
    (∑ a ∈ Ico 1 p, f (p - a)) = ∑ a ∈ Ico 1 p, f a := by
  simpa using (Finset.sum_Ico_reflect f 1 (m := p) (n := p) (by omega))

/-- The floor-sign matrix expression, proved directly from the upstream definition. -/
lemma S_eq_floorSign (p : ℕ) (hp : p.Prime) :
    Arxiv.«2501.03234».S p = ∑ a ∈ Ico 1 p, floorSign a p := by
  unfold Arxiv.«2501.03234».S
  rw [← sum_reflection p (fun a => Arxiv.«2501.03234».S' a p)]
  apply sum_congr rfl
  intro a ha
  unfold Arxiv.«2501.03234».S' floorSign
  apply sum_congr rfl
  intro j hj
  rw [floor_nat_ratio]
  have hq := prime_quotient_reflection p a j hp ha hj
  have he : j + 1 + (p - a) * j / p = a * j / p + 2 * ((p - a) * j / p + 1) := by omega
  rw [he, pow_add, pow_mul]
  simp

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
  decide (V < BN - 1) && decide (n ^ 2 + 6 * p < 8 * C)

lemma validatePacked_sound (p g L h X : ℕ) (hp : p.Prime) (hop : Odd p)
    (hc : validatePacked p g L h X = true) :
    3 * (p : ℤ) < Arxiv.«2501.03234».S p := by
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
  have hcount' : (p - 1) ^ 2 + 6 * p < 8 * packedParityCount L (p - 1) X := by
    simpa only [packedParityCount, cyclicFold, pow_mul, pow_two] using hcount
  have hs := two_mul_S_eq_packedParityCount p g L X _ hp hop H hr' hB hfold'
  have hi : ((p - 1) ^ 2 + 6 * p : ℕ) < 8 * packedParityCount L (p - 1) X := hcount'
  have hi' : (((p - 1) ^ 2 + 6 * p : ℕ) : ℤ) <
      8 * (packedParityCount L (p - 1) X : ℤ) := by exact_mod_cast hi
  push_cast at hi'
  nlinarith


def repeatBits (step : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, count =>
      if count ≤ 1 then 1 else
      let v := repeatBits step fuel (count / 2)
      v ||| (v <<< (step * (count / 2)))

def spreadLoop (stride pad : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | fuel + 1, m, x =>
      if m = 0 then x else
      let repeats := repeatBits (2 * stride * m) 32 (pad / (2 * m))
      let mask := (powTwo m - 1) * (1 + powTwo (stride * m)) * repeats
      spreadLoop stride pad fuel (m / 2) ((x ||| (x <<< ((stride - 1) * m))) &&& mask)

def orbitLoop (p g d index L pad BN D period full : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, c, r, acc =>
      let bits := period * r / p
      let Uc := spreadLoop (L * index) pad 32 (pad / 2) bits
      let numerator := 2 * r * (BN - 1) - p * D * Uc
      let Rc := numerator / (D - 2)
      orbitLoop p g d index L pad BN D period full fuel (c + 1) (r * g % p)
        (acc + (Rc <<< (L * c)))

def seedLoop (p g L : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, c, r, acc =>
      seedLoop p g L fuel (c + 1) (r * g % p) (acc + (r <<< (L * c)))

def layerTree (p stride laneMask : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, layer => (layer, 0)
  | fuel + 1, count, layer =>
      if count = 0 then (layer, 0)
      else if count = 1 then ((layer + p * (layer &&& laneMask)) / 2, layer)
      else
        let half := count / 2
        let left := layerTree p stride laneMask fuel half layer
        let right := layerTree p stride laneMask fuel (count - half) left.1
        (right.1, left.2 + (right.2 <<< (stride * half)))

def packedOrbit (p g d index L pad : ℕ) : ℕ :=
  let BN := powTwo (L * (p - 1))
  let D := powTwo (L * index)
  let period := powTwo d - 1
  let full := powTwo (L * index * pad) - 1
  if index > 16 then
    (layerTree p (L * index) ((D - 1) / (powTwo L - 1)) 32 d
      (seedLoop p g L index 0 1 0)).2
  else orbitLoop p g d index L pad BN D period full index 0 1 0


def certificateCheck (p g d index L h pad : ℕ) : Bool :=
  validatePacked p g L h (packedOrbit p g d index L pad)

lemma certificateCheck_sound (p g d index L h pad : ℕ) (hp : p.Prime) (hop : Odd p)
    (hc : certificateCheck p g d index L h pad = true) :
    3 * (p : ℤ) < Arxiv.«2501.03234».S p :=
  validatePacked_sound p g L h _ hp hop hc

def GoodRange (lo hi : ℕ) : Prop :=
  ∀ p : ℕ, lo ≤ p → p < hi → p.Prime → 3 * (p : ℤ) < Arxiv.«2501.03234».S p

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
  let g := (record >>> 17) &&& (powTwo 17 - 1)
  let d := record >>> 34
  let h := p.log2 + 1
  let L := 2 * h
  let index := (p - 1) / d
  let pad := powTwo ((d - 1).log2 + 1)
  decide (3119 < p) && certificateCheck p g d index L h pad

lemma recordCheck_sound (record : ℕ) (hp : (recordP record).Prime)
    (hc : recordCheck record = true) :
    3 * (recordP record : ℤ) < Arxiv.«2501.03234».S (recordP record) := by
  unfold recordCheck at hc
  dsimp only at hc
  rw [Bool.and_eq_true, decide_eq_true_eq] at hc
  have hop : Odd (recordP record) := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))
  exact certificateCheck_sound (recordP record) _ _ _ _ _ _ hp hop hc.2

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
end ThetaLongHaul

/-! Exact finite certificates. Candidate data are untrusted; each interval
checks every integer, and each prime must pass the proved validator. The
certificates use PLift data definitions so their proofs are checked serially,
avoiding accumulation of asynchronous large-integer elaboration tasks. -/
namespace ThetaLongHaul.Packed

abbrev G := GoodRange

lemma bs (records : List ℕ) {lo hi : ℕ}
    (hc : blockCheck records lo hi = true) : G lo hi := blockCheck_sound records hc

lemma j {lo mid hi : ℕ} (ha : G lo mid) (hb : G mid hi) : G lo hi :=
  GoodRange.join ha hb

set_option maxRecDepth 100000 in
def q0 : PLift (G 3120 3182) := ⟨bs [0x27018400c31,0xc40067e0c41,0x1078089c0c5b,0x18bc0f9c0c5f,0x18c014700c61,0x10900f6a0c6d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1 : PLift (G 3182 3222) := ⟨bs [0x31c80c740c73,0xdc07360c77,0x32080c840c83,0x191008a20c89,0xc9006c40c91,0xa100b1a0c95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2 : PLift (G 3222 3272) := ⟨bs [0x10d00ad80c9d,0xa28076a0cb3,0x32d00cb60cb5,0x65c111a0cb9,0x10f805e60cbb,0x884192c0cc7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q3 : PLift (G 3272 3324) := ⟨bs [0x33880ce40ce3,0xa5011e40ce5,0x33a80cec0ceb,0xcf007540cf1,0x19ec0a1c0cf7,0x33e80cfc0cfb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q4 : PLift (G 3324 3362) := ⟨bs [0x1a000fc60d01,0x37803f20d03,0x8b413740d0f,0x34480d140d13,0x1a3c04100d1f,0x2a0017e0d21] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q5 : PLift (G 3362 3414) := ⟨bs [0x34a80d2c0d2b,0x11900e0e0d2d,0x79006c40d3d,0x1c416300d3f,0x1a9c13540d4f,0x35500d560d55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q6 : PLift (G 3414 3468) := ⟨bs [0x1ad00c500d69,0x6bc13300d79,0x900046e0d81,0x36100d860d85,0x9040f900d87,0x36280d8c0d8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q7 : PLift (G 3468 3528) := ⟨bs [0x36300d8e0d8d,0x36880da40da3,0x36a80dac0dab,0x1b6c0b880db7,0x36f00dbe0dbd,0x1b8c1b3a0dc7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q8 : PLift (G 3528 3558) := ⟨bs [0xdc819c00dc9,0x37300dce0dcd,0x37480dd40dd3,0x3b015560dd5,0x37680ddc0ddb,0x37900de60de5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q9 : PLift (G 3558 3608) := ⟨bs [0x1bcc07c00de7,0x37c80df40df3,0x37f00dfe0dfd,0x1bfc09dc0dff,0x1c1013540e09,0x9640bb00e17] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q10 : PLift (G 3608 3644) := ⟨bs [0x38700e1e0e1d,0x1c4016040e21,0x1c4c06080e27,0x97419340e2f,0x38d00e360e35,0x38e80e3c0e3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q11 : PLift (G 3644 3698) := ⟨bs [0x39280e4c0e4b,0x1cac19dc0e57,0xe5809060e59,0x39700e5e0e5d,0x39a80e6c0e6b,0x1ce000560e71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q12 : PLift (G 3698 3740) := ⟨bs [0x39d00e760e75,0x39f00e7e0e7d,0x1d0c0ec40e87,0x1d1c13e00e8f,0x3a500e960e95,0x8580d440e9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q13 : PLift (G 3740 3798) := ⟨bs [0x2f00fae0eb1,0x1d6c10400eb7,0x1d70132a0eb9,0x3b080ec40ec3,0x1da018e80ed1,0x3b500ed60ed5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q14 : PLift (G 3798 3852) := ⟨bs [0x3b680edc0edb,0xbf016e80eed,0x9f414c40eef,0xef816220ef9,0x1e0c121a0f07,0x3c280f0c0f0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q15 : PLift (G 3852 3908) := ⟨bs [0x3c300f0e0f0d,0x1e2c09f20f17,0x3c900f260f25,0x6101dd00f29,0xa20150e0f31,0x3d080f440f43] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q16 : PLift (G 3908 3932) := ⟨bs [0x1e8c00ea0f47,0x3d300f4e0f4d,0x1e9c15620f4f,0x3d480f540f53,0x1eb00dfc0f59,0x3d680f5c0f5b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q17 : PLift (G 3932 4004) := ⟨bs [0x36c043e0f67,0x3da80f6c0f6b,0x1efc0f400f7f,0x3e500f960f95,0xfa01c800fa1,0x3e880fa40fa3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q18 : PLift (G 4004 4050) := ⟨bs [0x1f4c0ea20fa7,0x3eb00fae0fad,0x3ec80fb40fb3,0x3ed00fb60fb5,0x14f80e280fbb,0x7e813000fd1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q19 : PLift (G 4050 4094) := ⟨bs [0xc813040fd3,0x2a410c20fd9,0x1fd016680fe9,0x1fdc17920fef,0x3fe80ffc0ffb,0x3ff00ffe0ffd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q20 : PLift (G 4094 4140) := ⟨bs [0x400810041003,0x201c08ba100f,0x203c06f2101f,0xac016e41021,0x409010261025,0x40a8102c102b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q21 : PLift (G 4140 4212) := ⟨bs [0x5680b681039,0x40f0103e103d,0x207c166c103f,0x15c0ca81051,0x8341e421069,0xd28166c1073] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q22 : PLift (G 4212 4244) := ⟨bs [0x107820461079,0x41e8107c107b,0x421010861085,0x210c20b21087,0x212019aa1091,0x424810941093] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q23 : PLift (G 4244 4284) := ⟨bs [0x4270109e109d,0x428810a410a3,0x429010a610a5,0x4c4213810af,0x8581fa210b1,0x42e810bc10bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q24 : PLift (G 4284 4350) := ⟨bs [0x10c007f210c1,0x864166a10c9,0x21cc14b010e7,0x21e0079210f1,0x16981aac10f3,0x43f010fe10fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q25 : PLift (G 4350 4410) := ⟨bs [0x441011061105,0x4428110c110b,0x445011161115,0x224c16041127,0x44b0112e112d,0x89c1be41139] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q26 : PLift (G 4410 4458) := ⟨bs [0x55020ba1145,0xb8419321147,0x22b017b81159,0x22bc0fb4115f,0x458811641163,0x11680f661169] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q27 : PLift (G 4458 4514) := ⟨bs [0x22dc1792116f,0x8c005561181,0x460811841183,0x4630118e118d,0x4668119c119b,0xbc0bae11a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q28 : PLift (G 4514 4562) := ⟨bs [0x469011a611a5,0xbc4223411a7,0x42818e011ab,0x470811c411c3,0x17b014ce11c5,0x23a0100211d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q29 : PLift (G 4562 4622) := ⟨bs [0xbe4150611d7,0x23cc1cb811e7,0x23dc16bc11ef,0x17f0019211f5,0x47e811fc11fb,0x4830120e120d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q30 : PLift (G 4622 4658) := ⟨bs [0x4870121e121d,0x243c079c121f,0x6981ccc1223,0x245010e21229,0x183811a4122b,0x6101ab41231] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q31 : PLift (G 4658 4722) := ⟨bs [0xc2405981237,0x24800b181241,0x248c1b101247,0x494812541253,0x24bc0f86125f,0x49c1c6e1271] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q32 : PLift (G 4722 4784) := ⟨bs [0x49c812741273,0xc5021f01279,0x5b01fc6127d,0x76c215e128f,0xc6406d01297,0x255c1c6212af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q33 : PLift (G 4784 4814) := ⟨bs [0x4ac812b412b3,0x4ad012b612b5,0x257018d612b9,0x257c162e12bf,0x12c0000e12c1,0x4b3012ce12cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q34 : PLift (G 4814 4890) := ⟨bs [0x12d00b1c12d1,0x25bc1d1012df,0xf3016ba12fd,0x79c054c1307,0x4c30130e130d,0x263012601319] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q35 : PLift (G 4890 4938) := ⟨bs [0x264c25481327,0x1990003c132d,0x266c043a1337,0xf680b6e1343,0x4d1013461345,0x134811ca1349] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q36 : PLift (G 4938 4974) := ⟨bs [0x269c23e6134f,0x26ac10a21357,0x4d70135e135d,0x26cc01de1367,0x26d003481369,0x4db0136e136d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q37 : PLift (G 4974 5012) := ⟨bs [0x4de8137c137b,0x9c007a41381,0x5940e001387,0x4e28138c138b,0x272004f61391,0x4e4813941393] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q38 : PLift (G 5012 5078) := ⟨bs [0xfb00512139d,0x273c06a2139f,0x275c136813af,0x4ee813bc13bb,0x4f0813c413c3,0x4f5013d613d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q39 : PLift (G 5078 5114) := ⟨bs [0x9ec09d813d9,0x27bc057213df,0x4fa813ec13eb,0x1a90169213ed,0x4fc813f413f3,0x6a81dce13f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q40 : PLift (G 5114 5180) := ⟨bs [0x27fc152613ff,0x5068141c141b,0x1c01bbc1421,0xd742428142f,0x50c814341433,0x50e8143c143b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q41 : PLift (G 5180 5234) := ⟨bs [0x511014461445,0x1b101324144d,0x3640e8e1459,0x51a8146c146b,0x28dc1a50146f,0x14700a741471] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q42 : PLift (G 5234 5298) := ⟨bs [0xbb0243c1475,0x5230148e148d,0x293024801499,0x5e4132e149f,0x2940080a14a1,0xa5818d614b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q43 : PLift (G 5298 5352) := ⟨bs [0x296c120814b7,0x52f014be14bd,0x1bb80bcc14cb,0x535014d614d5,0x3180e4814e3,0x29cc127614e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q44 : PLift (G 5352 5414) := ⟨bs [0x10d020461505,0x5428150c150b,0x151010301511,0x2a2c1bfc1517,0x2a3c29d6151f,0x1c30260c1525] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q45 : PLift (G 5414 5444) := ⟨bs [0x2a5006981529,0xa808e2152b,0x2a6c20341537,0x1c501290153d,0x88001c61541,0x550815441543] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q46 : PLift (G 5444 5502) := ⟨bs [0xe300a3c1549,0x88c1252155f,0x559015661565,0x2acc20cc1567,0x55a8156c156b,0x55f0157e157d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q47 : PLift (G 5502 5532) := ⟨bs [0xe54053e157f,0x560815841583,0x2b1c1c62158f,0x2b201a461591,0x2b2c09361597,0xc580f64159b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q48 : PLift (G 5532 5592) := ⟨bs [0x56d015b615b5,0x56e815bc15bb,0x74010e415c1,0x571015c615c5,0x1f021d415cd,0x2bac01b415d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q49 : PLift (G 5592 5654) := ⟨bs [0x2bec164215f7,0x2c0c02a81607,0x8d00dae1609,0x2c1c2892160f,0x584816141613,0x1d7005581615] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q50 : PLift (G 5654 5694) := ⟨bs [0x2c3015521619,0x5868161c161b,0x6d009be1625,0x58c816341633,0xb1c26d41639,0x58f0163e163d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q51 : PLift (G 5694 5744) := ⟨bs [0x591016461645,0x8ec0818164f,0x595016561655,0x3bc129e1669,0x59b0166e166d,0x2cdc0fa0166f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q52 : PLift (G 5744 5808) := ⟨bs [0x59d016761675,0x5a4816941693,0x2d2c0cf81697,0x2d3c109c169f,0x2d501f3216a9,0x2d5c1b4e16af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q53 : PLift (G 5808 5850) := ⟨bs [0x5ad016b616b5,0x61018fc16bd,0x5b0816c416c3,0x2d9c120616cf,0x5b4816d416d3,0x2db01bc416d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q54 : PLift (G 5850 5880) := ⟨bs [0x5b6816dc16db,0x2dc0130416e1,0x12501c9816e5,0xd180c3816eb,0x5bb016ee16ed,0x2dec203616f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q55 : PLift (G 5880 5940) := ⟨bs [0x16f8181416f9,0x2e101cb81709,0x2e1c01c0170f,0x5c8817241723,0x2e4c17741727,0x5cc817341733] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q56 : PLift (G 5940 6030) := ⟨bs [0xf801d261741,0x730009e175d,0x5d8817641763,0xfa420fe1777,0x5de8177c177b,0x5e30178e178d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q57 : PLift (G 6030 6074) := ⟨bs [0x1f7002ec1795,0x4f814c0179b,0x2f3c0654179f,0x5e9017a617a5,0x5ec817b417b3,0x2f700cd617b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q58 : PLift (G 6074 6122) := ⟨bs [0xfd4106e17bf,0xbe4143a17c9,0x1fb804a017cb,0x5f5017d617d5,0x2fc02cbc17e1,0x17e82bee17e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q59 : PLift (G 6122 6174) := ⟨bs [0x5fc817f417f3,0x1ff0136817f5,0x2ffc0a5417ff,0x10042cf41807,0x20181ee81813,0x6070181e181d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q60 : PLift (G 6174 6222) := ⟨bs [0x60d018361835,0x306c2e581837,0x60e8183c183b,0x610818441843,0x103009321849,0x13701af8184d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q61 : PLift (G 6222 6272) := ⟨bs [0x615018561855,0x30cc139c1867,0x30e020341871,0x30ec102a1877,0x61f0187e187d,0x10541496187f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q62 : PLift (G 6272 6318) := ⟨bs [0x621018861885,0x311c2c76188f,0x6268189c189b,0x20d00c16189d,0x314c0d1218a7,0x62b018ae18ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q63 : PLift (G 6318 6360) := ⟨bs [0x62c818b418b3,0x31700f2e18b9,0x4802a3418c1,0x318c306418c7,0x6341ab818d1,0x31ac0c0218d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q64 : PLift (G 6360 6398) := ⟨bs [0xd42ef618d9,0x31bc1a2818df,0x639018e618e5,0x63a818ec18eb,0x63d018f618f5,0x63f018fe18fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q65 : PLift (G 6398 6474) := ⟨bs [0x21701d1a1915,0x21782500191b,0xc980ee61931,0x219812461933,0x651019461945,0x3290285e1949] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q66 : PLift (G 6474 6552) := ⟨bs [0xca822fa1951,0x6568195c195b,0x1978049c1979,0x19807ca1981,0x664819941993,0x332c09de1997] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q67 : PLift (G 6552 6582) := ⟨bs [0x1d41eba1999,0x608134219a3,0x19a80e7819a9,0x1488190e19ab,0x33600fb819b1,0x14900dac19b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q68 : PLift (G 6582 6660) := ⟨bs [0x338c063c19c7,0x339c095819cf,0x676819dc19db,0x67b019ee19ed,0x67f019fe19fd,0x68081a041a03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q69 : PLift (G 6660 6702) := ⟨bs [0x22b020c81a05,0x116030a01a11,0x27c2f661a17,0xd102eb41a21,0x68881a241a23,0x68b01a2e1a2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q70 : PLift (G 6702 6762) := ⟨bs [0x345c29fc1a2f,0x68d01a361a35,0x347c22d81a3f,0x69301a4e1a4d,0x34a01c1a1a51,0x1a680fe21a69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q71 : PLift (G 6762 6804) := ⟨bs [0x69a81a6c1a6b,0x69e81a7c1a7b,0x69f01a7e1a7d,0xa9c30981a87,0x1a880f9a1a89,0x6a481a941a93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q72 : PLift (G 6804 6858) := ⟨bs [0x354c12be1aa7,0x6aa81aac1aab,0x6ab01aae1aad,0x356033801ab1,0x1ab81bd21ab9,0xd64188c1ac9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q73 : PLift (G 6858 6908) := ⟨bs [0x359c24261acf,0x6b501ad61ad5,0xabc1cfe1ad7,0x6b881ae41ae3,0x6bc81af41af3,0x6be81afc1afb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q74 : PLift (G 6908 6962) := ⟨bs [0x35fc03261aff,0x6c101b061b05,0x6c881b241b23,0x6c901b261b25,0x7c40baa1b2f,0x122032c01b31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q75 : PLift (G 6962 6998) := ⟨bs [0x122401381b37,0x6ce81b3c1b3b,0x36801a641b41,0x368c11541b47,0x369c0e701b4f,0x247009061b55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q76 : PLift (G 6998 7044) := ⟨bs [0x7d00dda1b59,0x6d901b661b65,0x6da81b6c1b6b,0x6dc81b741b73,0x36fc163e1b7f,0x6e081b841b83] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q77 : PLift (G 7044 7122) := ⟨bs [0x62022d41b91,0x6e701b9e1b9d,0x374c323c1ba7,0x377c0d701bbf,0x6f101bc61bc5,0xde826c81bd1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q78 : PLift (G 7122 7188) := ⟨bs [0x37ac03ee1bd7,0x1bd824fc1bd9,0x514264a1bef,0x37ec0c2e1bf7,0x381026061c09,0x70481c141c13] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q79 : PLift (G 7188 7230) := ⟨bs [0x3830230a1c19,0x384c09461c27,0x70a81c2c1c2b,0x259018aa1c2d,0x70c81c341c33,0x70f01c3e1c3d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q80 : PLift (G 7230 7298) := ⟨bs [0x71101c461c45,0x71281c4c1c4b,0x389c1dae1c4f,0x71501c561c55,0x71c81c741c73,0x3900242a1c81] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q81 : PLift (G 7298 7350) := ⟨bs [0x72281c8c1c8b,0x1050100a1c8d,0x13100d301c99,0x72881ca41ca3,0x263030301ca5,0x72d01cb61cb5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q82 : PLift (G 7350 7434) := ⟨bs [0x83400f41cb7,0x133034581cc9,0x42023621ce1,0x73c81cf41cf3,0x39f022ac1cf9,0x3a10268e1d09] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q83 : PLift (G 7434 7488) := ⟨bs [0x74681d1c1d1b,0x3a4022581d21,0x74881d241d23,0x74d01d361d35,0x1d3818301d39,0x314201a1d3f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q84 : PLift (G 7488 7530) := ⟨bs [0x750193e1d41,0x75281d4c1d4b,0x75481d541d53,0x75701d5e1d5d,0x75881d641d63,0xeb41bf21d69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q85 : PLift (G 7530 7562) := ⟨bs [0x13a02c5a1d71,0x75d01d761d75,0x75e81d7c1d7b,0x75f01d7e1d7d,0x3b0c33441d87,0x3b102c221d89] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q86 : PLift (G 7562 7604) := ⟨bs [0x76501d961d95,0x1d9804701d99,0x3b3c2b441d9f,0x76901da61da5,0x3b4c01461da7,0x76c81db41db3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q87 : PLift (G 7604 7670) := ⟨bs [0x3b6c1a5c1db7,0x77101dc61dc5,0x13e4366a1dd7,0x77681ddc1ddb,0x3bc0118c1de1,0x77d01df61df5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q88 : PLift (G 7670 7704) := ⟨bs [0x3bf01a801df9,0x3c002fc01e01,0x3c0c3b921e07,0x78281e0c1e0b,0x28182baa1e13,0x3c2c36e41e17] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q89 : PLift (G 7704 7758) := ⟨bs [0x78901e261e25,0x283829861e2b,0x3c5c031c1e2f,0x285037261e3d,0x50c30e61e49,0x79301e4e1e4d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q90 : PLift (G 7758 7830) := ⟨bs [0x3c9c39361e4f,0x79b01e6e1e6d,0x1e70133e1e71,0x1e8830a41e89,0x3d1c30121e8f,0x7a501e961e95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q91 : PLift (G 7830 7880) := ⟨bs [0x1ea001a81ea1,0x7ab01eae1ead,0xda810681ebb,0x1480139c1ec1,0x7b101ec61ec5,0x3d8c38941ec7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q92 : PLift (G 7880 7934) := ⟨bs [0x7b281ecc1ecb,0x7b701ede1edd,0x7b881ee41ee3,0x3ddc1e961eef,0x14a433d61ef7,0x7bf01efe1efd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q93 : PLift (G 7934 8010) := ⟨bs [0x3e00007e1f01,0x7c301f0e1f0d,0x3e1c05c41f0f,0x29782b921f1b,0xf9c22a21f39,0x3e900eec1f49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q94 : PLift (G 8010 8070) := ⟨bs [0x29b809aa1f4b,0x3ea006141f51,0x3ecc2aca1f67,0x7dd01f761f75,0x29f815cc1f7b,0x7e101f861f85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q95 : PLift (G 8070 8112) := ⟨bs [0xfc8264c1f91,0x3f2c2d781f97,0x3f3013ee1f99,0x7e701f9e1f9d,0x190356a1fa5,0x3f5c23261faf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q96 : PLift (G 8112 8172) := ⟨bs [0x7ed01fb61fb5,0x7ee81fbc1fbb,0x7f481fd41fd3,0x660000e1fe1,0x154423d81fe7,0x7fa81fec1feb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q97 : PLift (G 8172 8232) := ⟨bs [0x7fc81ff41ff3,0x3423a61fff,0x20103b002011,0x8068201c201b,0x8070201e201d,0x404c39f22027] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q98 : PLift (G 8232 8274) := ⟨bs [0x2028310c2029,0x80b0202e202d,0x80c820342033,0x408c0aa42047,0x8130204e204d,0x20501f722051] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q99 : PLift (G 8274 8318) := ⟨bs [0x15941464205f,0x818820642063,0x819020662065,0x40d01f782069,0x40ec2f7a2077,0x4d02aae207d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q100 : PLift (G 8318 8388) := ⟨bs [0x41101d882089,0x7400d6020a1,0x82a820ac20ab,0x20b0095e20b1,0x15d02af020b9,0x830820c420c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q101 : PLift (G 8388 8444) := ⟨bs [0x2bb01b2020c5,0x2bd81bae20e3,0x41cc0f7420e7,0x83b020ee20ed,0x41dc18f020ef,0x83e820fc20fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q102 : PLift (G 8444 8522) := ⟨bs [0x41fc384420ff,0x1a7001e8210d,0x844821142113,0x1a9002442135,0x4280021a2141,0x429014c22149] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q103 : PLift (G 8522 8574) := ⟨bs [0x429c149a214f,0x215800722159,0x8568215c215b,0x42bc1ed8215f,0x85c821742173,0x85f0217e217d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q104 : PLift (G 8574 8628) := ⟨bs [0xa503fc02185,0x865021962195,0x432c143a2197,0x10d042c421a1,0x435c2b1821af,0x86c821b421b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q105 : PLift (G 8628 8678) := ⟨bs [0x2cf011f221b5,0x438010b221c1,0x438c222421c7,0x43ac09be21d7,0x877021de21dd,0x879021e621e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q106 : PLift (G 8678 8714) := ⟨bs [0x1f03b4421e9,0x43e023f821f1,0x87d021f621f5,0x87e821fc21fb,0x2d5806082203,0x5ac12062209] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q107 : PLift (G 8714 8754) := ⟨bs [0x16b43988220f,0x8868221c221b,0x444041622221,0x889022262225,0x88a8222c222b,0x446004982231] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q108 : PLift (G 8754 8820) := ⟨bs [0x5b424a02239,0x2db815be224b,0x449c0964224f,0x898822642263,0x44cc06942267,0x89c822742273] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q109 : PLift (G 8820 8862) := ⟨bs [0x89d022762275,0xdcc02ca227f,0x8a1022862285,0x450c409e2287,0x45202e8c2291,0x8a70229e229d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q110 : PLift (G 8862 8930) := ⟨bs [0x17143a92229f,0x8a8822a422a3,0x456c2f7a22b7,0x2e5021de22bd,0x8b6822dc22db,0x7c0168422e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q111 : PLift (G 8930 8972) := ⟨bs [0x8b9022e622e5,0x2e902b8422ed,0x45ec448c22f7,0x8c0823042303,0x11840a062309,0x8c28230c230b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q112 : PLift (G 8972 9030) := ⟨bs [0x464c35382327,0x23281e502329,0x465c0bda232f,0x8cc823342333,0x2ef03bce2335,0x8d1023462345] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q113 : PLift (G 9030 9092) := ⟨bs [0xe20071c2351,0x2f1810542353,0x46b02ab22359,0x8d8823642363,0x2f383cc8236b,0x1c6812382383] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q114 : PLift (G 9092 9152) := ⟨bs [0x471c3838238f,0x2f7002f62395,0x474c136623a7,0x2f9031d223ad,0x11d836de23b1,0x477c0e9423bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q115 : PLift (G 9152 9200) := ⟨bs [0x1470217c23c5,0x4790388823c9,0x8f5023d623d5,0x8f7023de23dd,0x2fd8172023e3,0x47dc149c23ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q116 : PLift (G 9200 9242) := ⟨bs [0x8fc823f423f3,0x23f808a023f9,0x901024062405,0x9028240c240b,0x482c17e22417,0x2418297e2419] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q117 : PLift (G 9242 9312) := ⟨bs [0x485046ea2429,0x30501b9c243d,0x1220158c2441,0x910824442443,0x9130244e244d,0x48bc0540245f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q118 : PLift (G 9312 9350) := ⟨bs [0x48cc40282467,0x91a8246c246b,0x24781d242479,0x91f0247e247d,0x48fc1a6a247f,0x921024862485] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q119 : PLift (G 9350 9414) := ⟨bs [0x9268249c249b,0x24a0022824a1,0x495c3d4424af,0x92d024b624b5,0x30f842e624bb,0xb502b7c24c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q120 : PLift (G 9414 9440) := ⟨bs [0x932824cc24cb,0x933024ce24cd,0xebc284424d7,0x49b00c9e24d9,0x937024de24dd,0x18941ef224df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q121 : PLift (G 9440 9492) := ⟨bs [0x1d90013624f5,0x18a437ac24f7,0x93e824fc24fb,0x250046d22501,0x4a0c44302507,0x944825142513] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q122 : PLift (G 9492 9548) := ⟨bs [0x4a301d922519,0x4f401802527,0x7701dee2531,0x94f0253e253d,0x950825442543,0x9528254c254b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q123 : PLift (G 9548 9624) := ⟨bs [0x4a9c2892254f,0x95c825742573,0x258004442581,0x9630258e258d,0x964825942593,0x46c0ed82597] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q124 : PLift (G 9624 9678) := ⟨bs [0x9670259e259d,0x19142630259f,0x96a825ac25ab,0x648299225b1,0x96f025be25bd,0x973025ce25cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q125 : PLift (G 9678 9734) := ⟨bs [0x4b9c301225cf,0x4bb01eba25d9,0x25e01a3625e1,0xac266225f7,0xca8087a25f9,0x981026062605] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q126 : PLift (G 9734 9782) := ⟨bs [0x32b822bc260b,0x4c1c0c28260f,0x985026162615,0x4c4c111e2627,0x131429002629,0xa302f3a2635] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q127 : PLift (G 9782 9830) := ⟨bs [0x32f84b30263b,0x4c7c32d0263f,0x9928264c264b,0x33183c4c2653,0x199043fe2659,0x15f037522665] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q128 : PLift (G 9830 9872) := ⟨bs [0x4cd0206c2669,0x4cdc3f86266f,0x99e8267c267b,0x4d0042b42681,0x9a0826842683,0x4d1c1ff6268f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q129 : PLift (G 9872 9930) := ⟨bs [0x9a68269c269b,0x4d3c0e40269f,0x9ab026ae26ad,0x9ac826b426b3,0x9b0826c426c3,0x4904c7826c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q130 : PLift (G 9930 10008) := ⟨bs [0x33b82a8c26cb,0x9b5026d626d5,0x9b7026de26dd,0x4ddc0bde26ef,0x33f0078a26f5,0x4e2c1cc62717] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q131 : PLift (G 10008 10070) := ⟨bs [0x1a1035902719,0x9cd027362735,0x1a2436e42737,0x1f701c36274d,0x9d4827542753,0x9d5027562755] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q132 : PLift (G 10070 10112) := ⟨bs [0x4ebc4572275f,0x9da8276c276b,0x9db0276e276d,0x9dc827742773,0x4eec1c222777,0x4efc33c6277f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q133 : PLift (G 10112 10164) := ⟨bs [0x9e5027962795,0x9e68279c279b,0x9e70279e279d,0x4f4c477427a7,0x1a74289827af,0x9ec827b427b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q134 : PLift (G 10164 10224) := ⟨bs [0x290048827b9,0x9f00e4e27c1,0x9f1027c627c5,0x4fa03bec27d1,0x1fe8141e27e3,0x4fdc49ee27ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q135 : PLift (G 10224 10272) := ⟨bs [0x11c83fea2803,0x500c073a2807,0xa030280e280d,0xa04828142813,0xa068281c281b,0x503c4d20281f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q136 : PLift (G 10272 10322) := ⟨bs [0x504012cc2821,0x50600f8a2831,0xa0f0283e283d,0x1ad4280e283f,0x50901b5a2849,0x50a039262851] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q137 : PLift (G 10322 10370) := ⟨bs [0xa168285c285b,0x11f0166a285d,0x143045d42861,0x50cc10462867,0xa1d028762875,0x14402c622881] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q138 : PLift (G 10370 10454) := ⟨bs [0x512c4bde2897,0x513c385c289f,0xa2e828bc28bb,0x36502d2c28bd,0x14602bb028c1,0xc9030c828d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q139 : PLift (G 10454 10500) := ⟨bs [0x28d846b628d9,0xa36828dc28db,0x51bc0c5e28df,0xa3b028ee28ed,0x51ec09fa28f7,0xa40829042903] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q140 : PLift (G 10500 10568) := ⟨bs [0xa41029062905,0x2910480a2911,0x524021342921,0x36d82fbe2923,0x527c39aa293f,0x528c3cf42947] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q141 : PLift (G 10568 10628) := ⟨bs [0xa570295e295d,0x37304d722965,0x52d03dea2969,0x52dc2908296f,0xa5d029762975,0x17b82d622983] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q142 : PLift (G 10628 10668) := ⟨bs [0x530c124a2987,0x531c20f2298f,0x37781b24299b,0x53439ec29a1,0x1bc41dc029a7,0xa6a829ac29ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q143 : PLift (G 10668 10730) := ⟨bs [0x537c032e29bf,0xa70829c429c3,0xa75029d629d5,0x10bc25a229d7,0xa78829e429e3,0x53d0133a29e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q144 : PLift (G 10730 10790) := ⟨bs [0xa7b029ee29ed,0x17f823aa29f3,0x1c003e462a01,0x38184f6a2a13,0x21b0519c2a1d,0xa8902a262a25] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q145 : PLift (G 10790 10860) := ⟨bs [0x545c34762a2f,0x549c452e2a4f,0xa9502a562a55,0x54bc17402a5f,0xa9902a662a65,0xa9a82a6c2a6b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q146 : PLift (G 10860 10904) := ⟨bs [0xa9b02a6e2a6d,0xa9c82a742a73,0xaa082a842a83,0x2a883fa62a89,0xaa282a8c2a8b,0x1c64244a2a97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q147 : PLift (G 10904 10974) := ⟨bs [0xaa702a9e2a9d,0x155c1e902ab9,0x38f820282abb,0xab102ac62ac5,0x3910144a2acd,0xab702ade2add] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q148 : PLift (G 10974 11048) := ⟨bs [0xab882ae42ae3,0xaba82aec2aeb,0x2af030d02af1,0xabe82afc2afb,0xac482b142b13,0x564c2dc82b27] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q149 : PLift (G 11048 11088) := ⟨bs [0x2b304d662b31,0x39982f802b33,0xacf02b3e2b3d,0x567c46e82b3f,0xad282b4c2b4b,0x569c1c5c2b4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q150 : PLift (G 11088 11150) := ⟨bs [0xad502b562b55,0x73c084a2b69,0x18d048b22b6d,0xcc128e2b6f,0xade82b7c2b7b,0x3a1006642b8d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q151 : PLift (G 11150 11198) := ⟨bs [0x572c22642b97,0x4d809322b99,0xae882ba42ba3,0x3a303fc22ba5,0x15d405ea2ba9,0xaef02bbe2bbd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q152 : PLift (G 11198 11262) := ⟨bs [0xaf302bce2bcd,0x57cc03c02be7,0x191819902beb,0x232827ce2bf3,0x15fc06462bf9,0xaff02bfe2bfd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q153 : PLift (G 11262 11318) := ⟨bs [0x58103d6e2c09,0x581c418a2c0f,0x9cc51aa2c17,0x193841d62c23,0x585c46622c2f,0xb0d02c362c35] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q154 : PLift (G 11318 11384) := ⟨bs [0x2c380e4c2c39,0x76029502c41,0x58ac459e2c57,0x58b02a5a2c59,0x58d00dda2c69,0x58ec44742c77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q155 : PLift (G 11384 11444) := ⟨bs [0x590025be2c81,0x590c3e6c2c87,0x197821582c93,0x593c3d7e2c9f,0xb2b02cae2cad,0xb2c82cb42cb3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q156 : PLift (G 11444 11492) := ⟨bs [0x18421422cb7,0x199826022ccb,0x26c3cf82ccf,0xb3682cdc2cdb,0x59c03cf02ce1,0x3bd81c222ce3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q157 : PLift (G 11492 11552) := ⟨bs [0x59d02f3e2ce9,0x59dc33702cef,0x59fc30942cff,0x5a0c24242d07,0xb4702d1e2d1d,0x1e1428282d1f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q158 : PLift (G 11552 11622) := ⟨bs [0xb4e82d3c2d3b,0xb5082d442d43,0x5a90298c2d49,0xdf02f802d4d,0x16b026f62d61,0xb5902d662d65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q159 : PLift (G 11622 11700) := ⟨bs [0x16b849c22d71,0x16c458762d89,0xb6702d9e2d9d,0x5b4029062da1,0x5b5031382da9,0xb6c82db42db3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q160 : PLift (G 11700 11778) := ⟨bs [0x249045702db5,0xb7102dc62dc5,0x5b8c56842dc7,0x3d184f042dd3,0x5bbc333e2ddf,0x2e000eb02e01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q161 : PLift (G 11778 11814) := ⟨bs [0xb8082e042e03,0x5c0c3b1e2e07,0xb8302e0e2e0d,0x170c57822e19,0x5c3c183e2e1f,0xb8902e262e25] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q162 : PLift (G 11814 11864) := ⟨bs [0xb8b02e2e2e2d,0xb8c82e342e33,0x5c6c09542e37,0x5c7049d62e39,0x5c7c11ec2e3f,0x1ee423f02e57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q163 : PLift (G 11864 11924) := ⟨bs [0xb9682e5c2e5b,0x5cdc401a2e6f,0x5cf0153a2e79,0x5cfc4f282e7f,0xba102e862e85,0x3e1835b02e93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q164 : PLift (G 11924 11960) := ⟨bs [0x5d2c51402e97,0xba702e9e2e9d,0xba882ea42ea3,0x25503f5e2ea5,0xa60451e2eb1,0x1f24397e2eb7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q165 : PLift (G 11960 12012) := ⟨bs [0x2ec04e1c2ec1,0x3e5830e02ec3,0xbb302ece2ecd,0xbb482ed42ed3,0xa6c2a222ee7,0xbba82eec2eeb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q166 : PLift (G 12012 12074) := ⟨bs [0xb1048ae2f05,0x178401062f09,0xbc282f0c2f0b,0xbc446162f11,0x5e4c2d622f27,0x17941a3e2f29] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q167 : PLift (G 12074 12120) := ⟨bs [0x5e802e1e2f41,0x11303dce2f45,0xbd282f4c2f4b,0x3f1015522f4d,0x5ea0544c2f51,0x5eac28aa2f57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q168 : PLift (G 12120 12198) := ⟨bs [0x5edc4c042f6f,0xbdd02f762f75,0xbdf02f7e2f7d,0x2f803bf22f81,0x3f583a642f83,0xbe902fa62fa5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q169 : PLift (G 12198 12252) := ⟨bs [0xbea82fac2fab,0xbec82fb42fb3,0xbf082fc42fc3,0x5f9c26922fcf,0x7f82afc2fd1,0xbf682fdc2fdb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q170 : PLift (G 12252 12290) := ⟨bs [0xbf702fde2fdd,0x5fcc47482fe7,0xbfb02fee2fed,0xbfd02ff62ff5,0x5ff038442ff9,0x600053e63001] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q171 : PLift (G 12290 12374) := ⟨bs [0xc030300e300d,0xc08830243023,0x302805e03029,0x202419183037,0xc0e8303c303b,0xc15030563055] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q172 : PLift (G 12374 12414) := ⟨bs [0x305847a43059,0xc168305c305b,0x204410f43067,0x60e04b6c3071,0x183c15763079,0xc1f0307e307d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q173 : PLift (G 12414 12474) := ⟨bs [0x40b0328c3085,0x61201baa3091,0xc25030963095,0x40d85f7c30a3,0x185434f430a9,0x30b82db630b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q174 : PLift (G 12474 12512) := ⟨bs [0x5bc0a7630bf,0x618c4b8c30c7,0xc32830cc30cb,0x30d029e030d1,0x524389830d7,0x61bc1cb630df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q175 : PLift (G 12512 12554) := ⟨bs [0x413039cc30e5,0x61dc1f2e30ef,0xc3e830fc30fb,0x2730161030fd,0xc40831043103,0x31082f023109] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q176 : PLift (G 12554 12612) := ⟨bs [0x311807563119,0x1890326a3121,0x20c440d43127,0xc4b0312e312d,0x627032623139,0xc50831443143] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q177 : PLift (G 12612 12654) := ⟨bs [0xc51031463145,0xc528314c314b,0xc570315e315d,0x62c139e3161,0x62cc25ce3167,0xc5b0316e316d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q178 : PLift (G 12654 12714) := ⟨bs [0xc5c831743173,0x62fc5bfc317f,0x632002fc3191,0x31985e963199,0x21144926319f,0x31a85ccc31a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q179 : PLift (G 12714 12782) := ⟨bs [0x13e00a4631b1,0xc70831c431c3,0x638c409831c7,0xc75031d631d5,0xc76831dc31db,0xc7b031ee31ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q180 : PLift (G 12782 12830) := ⟨bs [0x63ec211a31f7,0x2154560631ff,0x64100d743209,0xc85032163215,0x642c240a3217,0xc870321e321d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q181 : PLift (G 12830 12908) := ⟨bs [0x85c4f1c3229,0x16502ab03235,0x64b020b43259,0x12500cc8325d,0xc98832643263,0xc9a8326c326b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q182 : PLift (G 12908 12954) := ⟨bs [0x64dc3a7c326f,0xc9d032763275,0x64ec41da3277,0xc9e8327c327b,0xca30328e328d,0x653055943299] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q183 : PLift (G 12954 13002) := ⟨bs [0x653c3d14329f,0x654c22a232a7,0x43904d6232ad,0xcac832b432b3,0x656c297432b7,0x6590409432c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q184 : PLift (G 13002 13044) := ⟨bs [0x43b841aa32cb,0xe840b7832cf,0x21e0121c32d1,0x65d04af032e9,0xcbb032ee32ed,0xcbc832f432f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q185 : PLift (G 13044 13110) := ⟨bs [0x197c0d7632f9,0x2204015c3307,0x443016e83325,0x5881034332b,0x665c25da332f,0xccd033363335] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q186 : PLift (G 13110 13164) := ⟨bs [0x5205bca3341,0x668c24903347,0xcd68335c335b,0x66bc3efe335f,0x66cc54a03367,0xcda8336c336b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q187 : PLift (G 13164 13220) := ⟨bs [0x29282fb03373,0x22503c0a3379,0x66fc3754337f,0xce0833843383,0x33a03ee233a1,0x44d8125433a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q188 : PLift (G 13220 13292) := ⟨bs [0xceb033ae33ad,0x6770041233b9,0x67803efa33c1,0x1d98298a33cb,0x45184bb633d3,0xcfa833ec33eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q189 : PLift (G 13292 13338) := ⟨bs [0x22a0398e33f1,0x455027d433fd,0x680038943401,0x681c5e98340f,0xd04834143413,0x1a0c5d3a3419] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q190 : PLift (G 13338 13412) := ⟨bs [0xd068341c341b,0xa4551e3437,0x29d04f4a3445,0xd15034563455,0x22e4176c3457,0xd18834643463] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q191 : PLift (G 13412 13464) := ⟨bs [0x1a343c323469,0x29f03bfe346d,0x1a404d583481,0xd228348c348b,0x69205edc3491,0x692c4f7c3497] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q192 : PLift (G 13464 13524) := ⟨bs [0xd270349e349d,0xd29034a634a5,0x695c1d7a34af,0xc68085c34bb,0x6990262634c9,0xd34834d434d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q193 : PLift (G 13524 13598) := ⟨bs [0x69c050c634e1,0x9a0209a34f1,0x69fc45a234ff,0x6a1022ca3509,0x23640cd63517,0x46d01060351d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q194 : PLift (G 13598 13670) := ⟨bs [0xd4b0352e352d,0xd4c835343533,0xd4e8353c353b,0x1aa000723541,0x6aa0174c3551,0x330335a3565] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q195 : PLift (G 13670 13698) := ⟨bs [0x6adc293c356f,0x6ae01a7e3571,0x6aec35ec3577,0xd5e8357c357b,0x47503eaa357d,0x6b0053283581] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q196 : PLift (G 13698 13752) := ⟨bs [0xd630358e358d,0x6b1c039a358f,0x6b3027ba3599,0xd668359c359b,0x6b402de035a1,0x157c3ab635b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q197 : PLift (G 13752 13800) := ⟨bs [0xd6f035be35bd,0x6b7c3ff635bf,0xd70835c435c3,0x2b106a5a35d5,0x17f043dc35dd,0x6bcc069635e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q198 : PLift (G 13800 13874) := ⟨bs [0x6bdc3f2035ef,0xd81036063605,0x6c0c45bc3607,0x36100fde3611,0xd88836243623,0x6c60048e3631] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q199 : PLift (G 13874 13908) := ⟨bs [0xd8d036363635,0x6c6c1c363637,0xd8e8363c363b,0xd930364e364d,0x6c9c335c364f,0xd94836543653] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q200 : PLift (G 13908 13968) := ⟨bs [0x365800283659,0x366063423661,0xd9a8366c366b,0xd9b0366e366d,0x10c8182e368b,0x6d1c678a368f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q201 : PLift (G 13968 14034) := ⟨bs [0xdab036ae36ad,0x6d5c1e5436af,0x6d70394c36b9,0xdae836bc36bb,0x4910637636cd,0x6da03dba36d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q202 : PLift (G 14034 14088) := ⟨bs [0xdb8836e436e3,0x6dd0197a36e9,0x15fc507e36f7,0x6e006c463701,0x495838903703,0x6e0c422a3707] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q203 : PLift (G 14088 14174) := ⟨bs [0xdc68371c371b,0x6e7c1292373f,0x189006303745,0x6e901be03749,0x6e9c36d8374f,0xdd70375e375d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q204 : PLift (G 14174 14250) := ⟨bs [0x6ec02e783761,0x49f045ac3775,0x6efc496a377f,0xde30378e378d,0xde8837a437a3,0x37a85c9a37a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q205 : PLift (G 14250 14324) := ⟨bs [0x2c886ec437ab,0x2530584837c9,0x18d05b7a37d5,0x6fbc62d037df,0x1bf83e4637f1,0x738421837f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q206 : PLift (G 14324 14390) := ⟨bs [0x89c55d237f7,0xe01038063805,0x4ab851b0380b,0x382014263821,0xe0c838343833,0xe0d038363835] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q207 : PLift (G 14390 14432) := ⟨bs [0x38405cda3841,0x25840c5c3847,0xe128384c384b,0xe14838543853,0x70ac5ce63857,0x168c5f70385f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q208 : PLift (G 14432 14490) := ⟨bs [0x4b3028903865,0x70dc47fc386f,0x1501caa3871,0xe1f0387e387d,0x25b4253e388f,0x713004423899] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q209 : PLift (G 14490 14550) := ⟨bs [0x25c45d0638a7,0x716c31c838b7,0xe31038c638c5,0x1c645d7838c9,0x719c186a38cf,0xe35038d638d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q210 : PLift (G 14550 14594) := ⟨bs [0x71ac463e38d7,0xe37038de38dd,0x71c01e7438e1,0x1948655c38e3,0x16cc6ea838ff,0x1300552a3901] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q211 : PLift (G 14594 14654) := ⟨bs [0xe470391e391d,0xe48839243923,0xe49039263925,0x1c944bca3929,0x725c38b6392f,0xe4f0393e393d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q212 : PLift (G 14654 14718) := ⟨bs [0x7280410a3941,0xe530394e394d,0x4c784256395b,0xe5a8396c396b,0x39781c2a3979,0xe5f0397e397d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q213 : PLift (G 14718 14754) := ⟨bs [0xe60839843983,0x4cb8136e398b,0x39903a303991,0xe65039963995,0xe668399c399b,0x1cd0650e39a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q214 : PLift (G 14754 14798) := ⟨bs [0x734c088439a7,0x26745dc239af,0xe6c839b439b3,0x4cf859a239bb,0x737c264639bf,0xe73039ce39cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q215 : PLift (G 14798 14852) := ⟨bs [0xe77039de39dd,0xe79039e639e5,0xe7a839ec39eb,0x73dc2efe39ef,0xe7e839fc39fb,0xe8083a043a03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q216 : PLift (G 14852 14898) := ⟨bs [0xe8483a143a13,0xe8503a163a15,0x743c1e343a1f,0x744c59d43a27,0xe8a83a2c3a2b,0xe8c71963a31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q217 : PLift (G 14898 14958) := ⟨bs [0xe9283a4c3a4b,0x3a5062c43a51,0xe9683a5c3a5b,0xe9883a643a63,0x1cc3e663a67,0xe9b03a6e3a6d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q218 : PLift (G 14958 15054) := ⟨bs [0x1d3c467e3a79,0x750c01ca3a87,0xea903aa63aa5,0x1d540e4e3aa9,0x756c4b6c3ab7,0xeb303ace3acd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q219 : PLift (G 15054 15102) := ⟨bs [0xeb503ad63ad5,0x4e82cb63ae1,0xeb903ae63ae5,0xeba83aec3aeb,0xebc83af43af3,0xebf03afe3afd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q220 : PLift (G 15102 15150) := ⟨bs [0xec083b043b03,0x43839323b11,0xec683b1c3b1b,0x764075943b21,0xec883b243b23,0xecb03b2e3b2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q221 : PLift (G 15150 15218) := ⟨bs [0x76705e323b39,0xed103b463b45,0xed483b543b53,0x34c3f803b59,0x279451763b5f,0x3b70494e3b71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q222 : PLift (G 15218 15270) := ⟨bs [0xede83b7c3b7b,0x110056d23b81,0x5f447623b89,0xee683b9c3b9b,0x773c1fd83b9f,0xee903ba63ba5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q223 : PLift (G 15270 15308) := ⟨bs [0x27c4364a3ba7,0x4f901b803bad,0x776c60803bb7,0x9f45b883bb9,0xef083bc43bc3,0x4fb868163bcb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q224 : PLift (G 15308 15360) := ⟨bs [0x3bd0478e3bd1,0x77ac65523bd7,0x77c032ec3be1,0xef883be43be3,0xefd03bf63bf5,0x77fc63543bff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q225 : PLift (G 15360 15402) := ⟨bs [0x3c002e2c3c01,0xf0303c0e3c0d,0x78204f7c3c11,0x782c10583c17,0x783c2dac3c1f,0x78506cd43c29] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q226 : PLift (G 15402 15462) := ⟨bs [0xf0d03c363c35,0xf1083c443c43,0x283443a63c4f,0xf1483c543c53,0x9a801bc3c5b,0xf1903c663c65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q227 : PLift (G 15462 15528) := ⟨bs [0xcb801ac3c6b,0x78e0074e3c71,0x50b016c03c85,0x7910534c3c89,0x792c775c3c97,0x794c70923ca7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q228 : PLift (G 15528 15584) := ⟨bs [0x30905e283cb5,0x184c6be63cbf,0x288417b03cc7,0x1e686f5e3cd1,0xf3703cde3cdd,0x116455623cdf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q229 : PLift (G 15584 15644) := ⟨bs [0x28a01fa03cf1,0x79ec65723cf7,0x4483b983d03,0xf4303d0e3d0d,0x7a3061643d19,0x1b2822c43d1b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q230 : PLift (G 15644 15680) := ⟨bs [0x7a3c4c143d1f,0x7a4066503d21,0xf4b03d2e3d2d,0xf4c83d343d33,0x7a6c1ff83d37,0xd9c328e3d3f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q231 : PLift (G 15680 15740) := ⟨bs [0xf5083d443d43,0x28f438f03d6f,0xf5c83d743d73,0x51f064663d75,0x7af0391e3d79,0xf5e83d7c3d7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q232 : PLift (G 15740 15792) := ⟨bs [0xf6103d863d85,0x3d905cb03d91,0x7b2c0de43d97,0xf6703d9e3d9d,0xf6a83dac3dab,0x7b5c50a03daf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q233 : PLift (G 15792 15860) := ⟨bs [0xf6d03db63db5,0xf6e83dbc3dbb,0x3dc0fb23dc1,0x7b904a483dc9,0x7b9c649a3dcf,0xf7c83df43df3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q234 : PLift (G 15860 15908) := ⟨bs [0x52b03b943e05,0x3e084fbc3e09,0x7c1c32d23e0f,0x296062923e11,0x52d04b7e3e1d,0xf8883e243e23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q235 : PLift (G 15908 15972) := ⟨bs [0x29703fc43e29,0x7c5c10643e2f,0xf8c83e343e33,0x2980267c3e41,0x7cac22fc3e57,0xf9883e643e63] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q236 : PLift (G 15972 16058) := ⟨bs [0x53300c423e65,0x7cec248c3e77,0x7d0075223e81,0x7d0c24ac3e87,0x7d403be03ea1,0x29d00bda3eb9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q237 : PLift (G 16058 16088) := ⟨bs [0x16d06df23ebd,0x7d7c6b023ebf,0xfb083ec43ec3,0xfb103ec63ec5,0x11f0392e3ec9,0x7dac70b43ed7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q238 : PLift (G 16088 16140) := ⟨bs [0x324876dc3edb,0x7dc06dea3ee1,0x7dcc23883ee7,0x8643c303eef,0x7dfc3e803eff,0xfc283f0c3f0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q239 : PLift (G 16140 16218) := ⟨bs [0x32706a883f0d,0x45c20d83f37,0xfce83f3c3f3b,0xfcf03f3e3f3d,0x3f403c3a3f41,0x7eb00c683f59] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q240 : PLift (G 16218 16268) := ⟨bs [0x7ebc5e663f5f,0xfd903f663f65,0x7ecc1e823f67,0x1fbc54703f79,0xfdf03f7e3f7d,0x54b859f63f8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q241 : PLift (G 16268 16350) := ⟨bs [0x7f2034643f91,0xfeb03fae3fad,0x7f7c559e3fbf,0xff303fce3fcd,0xff483fd43fd3,0xff703fde3fdd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q242 : PLift (G 16350 16418) := ⟨bs [0x1ff46ce43fe9,0xffa83fec3feb,0x2aa06bda3ff1,0xfff03ffe3ffd,0x5578642a401b,0x201066b84021] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q243 : PLift (G 16418 16454) := ⟨bs [0x1009040264025,0x100a8402c402b,0x201872b24031,0x807c631a403f,0x336820524043,0x1011040464045] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q244 : PLift (G 16454 16530) := ⟨bs [0x10170405e405d,0x80c0394e4061,0x80cc684e4067,0x101b0406e406d,0x810c275c4087,0x812066a04091] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q245 : PLift (G 16530 16604) := ⟨bs [0x1028840a440a3,0x40a848fc40a9,0x2b204d5e40b1,0x816c146640b7,0x102f040be40bd,0x1036840dc40db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q246 : PLift (G 16604 16652) := ⟨bs [0x81bc305240df,0x103a840ec40eb,0x19fc76d840f7,0x207c573440f9,0x4108311c4109,0x10428410c410b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q247 : PLift (G 16652 16700) := ⟨bs [0x2b602dea4111,0x3410364c4115,0x20900b9a4121,0x3428817a4133,0x104d041364135,0x56f87388413b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q248 : PLift (G 16700 16764) := ⟨bs [0x827c5fbe413f,0xae412444159,0x573028b44165,0x105a8416c416b,0x82ec3c7c4177,0x105e8417c417b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q249 : PLift (G 16764 16844) := ⟨bs [0x1064841944193,0x3488220641ab,0x836c7e6a41b7,0x106f041be41bd,0xbf434fa41bf,0x1072841cc41cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q250 : PLift (G 16844 16904) := ⟨bs [0x1a5c42a441e7,0x2bf40ea641ef,0x107c841f441f3,0x83f07a0641f9,0x1081042064205,0x840c1a8e4207] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q251 : PLift (G 16904 16964) := ⟨bs [0x2c1057104219,0x2c1406a6421f,0x1088842244223,0x845061764229,0x845c7f70422f,0x1090842444243] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q252 : PLift (G 16964 17022) := ⟨bs [0x1094842544253,0x1095042564255,0x587869f6425b,0x84c00c3e4261,0x109c842744273,0x109f0427e427d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q253 : PLift (G 17022 17054) := ⟨bs [0x10a0842844283,0x81048124285,0x428824c84289,0x2c6051904291,0x852c0aa04297,0x10a70429e429d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q254 : PLift (G 17054 17124) := ⟨bs [0x10ad042b642b5,0x10b1042c642c5,0x10b2842cc42cb,0x5918833442d3,0x18500ff042dd,0x10b8842e442e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q255 : PLift (G 17124 17192) := ⟨bs [0x21786a5a42f1,0x860c438a4307,0x861c5a68430f,0x863c29c8431f,0x10c9043264325,0xeec2a2c4327] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q256 : PLift (G 17192 17258) := ⟨bs [0x10cc843344333,0x866c7eba4337,0x219c0aac4339,0x1aec2d16434f,0x86ac1f644357,0x86d058e24369] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q257 : PLift (G 17258 17328) := ⟨bs [0x36081f30438b,0x5a101058438d,0x10e4843944393,0x10e9043a643a5,0x43a82caa43a9,0x875c504a43af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q258 : PLift (G 17328 17384) := ⟨bs [0x10ed043b643b5,0x5a5069c843bd,0x878c58ac43c7,0x2d3442c243cf,0x43e0538243e1,0x2d44137043e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q259 : PLift (G 17384 17420) := ⟨bs [0x10fa843ec43eb,0x10fb043ee43ed,0x87e0287e43f1,0x910027443f9,0x44085bc04409,0x5ab819f2440b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q260 : PLift (G 17420 17478) := ⟨bs [0x882c01ee4417,0x1108844244423,0x885079904429,0x6a84b6e443b,0x887c160a443f,0x1111044464445] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q261 : PLift (G 17478 17520) := ⟨bs [0x11128444c444b,0x88a074164451,0x12380c3e4453,0x44586e2a4459,0x1119044664465,0x88dc3ef0446f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q262 : PLift (G 17520 17582) := ⟨bs [0x3787b8a4483,0x2db44d88448f,0x894052be44a1,0x1129044a644a5,0x112a844ac44ab,0x36f01cde44ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q263 : PLift (G 17582 17658) := ⟨bs [0x112f044be44bd,0x897c67ce44bf,0x44c819f044c9,0x89ac13c644d7,0x1136844dc44db,0x89f033dc44f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q264 : PLift (G 17658 17714) := ⟨bs [0x1ea844ba44fb,0x1141045064505,0x1ba038ac4511,0x5c1819964513,0x5c38080e452b,0x8a6026f44531] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q265 : PLift (G 17714 17784) := ⟨bs [0x4540825e4541,0x22a454504549,0x1154845544553,0x1155045564555,0x2e4016024561,0x8aec4e524577] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q266 : PLift (G 17784 17840) := ⟨bs [0x115f0457e457d,0x1bcc7098457f,0x8b1c10aa458f,0x1168845a445a3,0x116b045ae45ad,0x8b5c25b045af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q267 : PLift (G 17840 17910) := ⟨bs [0x116e845bc45bb,0x8b8c121245c7,0x22ec16cc45d9,0x1178845e445e3,0x8bdc79a845ef,0x117d045f645f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q268 : PLift (G 17910 17958) := ⟨bs [0x8bec597a45f7,0x8c0014824601,0x1180846044603,0x460806964609,0x1184846144613,0x1189046264625] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q269 : PLift (G 17958 17990) := ⟨bs [0x8c4c18e04627,0x3828028a4633,0x8c704d764639,0x118f0463e463d,0x10884d7c4643,0x1191046464645] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q270 : PLift (G 17990 18060) := ⟨bs [0x11970465e465d,0x70c003e4679,0x119e8467c467b,0x8cfc7a78467f,0x2f005fcc4681,0x11a28468c468b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q271 : PLift (G 18060 18122) := ⟨bs [0x12d04ff6468d,0x11a70469e469d,0x8d5053c646a9,0x8d603dca46b1,0x8d8c449c46c7,0x25c67f046c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q272 : PLift (G 18122 18170) := ⟨bs [0x2f34102846cf,0x38a82f2a46d3,0x5e705b9846d5,0x8dbc3a5246df,0x11b9046e646e5,0x46f812f046f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q273 : PLift (G 18170 18224) := ⟨bs [0x11c1047064705,0x8e1c0426470f,0x544120a4717,0x5ed808f24723,0xcf048ea4729,0x2f746f46472f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q274 : PLift (G 18224 18270) := ⟨bs [0x11cd047364735,0x4738441c4739,0x11d28474c474b,0x5f1009b8474d,0x23a80e504751,0x11d70475e475d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q275 : PLift (G 18270 18314) := ⟨bs [0x37c6d20476f,0x477081424771,0x5f50852a477d,0x5f5809ae4783,0x8f0c74fa4787,0x8f104a124789] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q276 : PLift (G 18314 18380) := ⟨bs [0x8f3015244799,0x39502d4047a5,0x47b00a8247b1,0x8f7c7bba47bf,0x3968763047c3,0x1fe816e247cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q277 : PLift (G 18380 18440) := ⟨bs [0x5fd01c1847dd,0x1cc023ae47e1,0x11fb047ee47ed,0x11fe847fc47fb,0x240043104801,0x14943fa44807] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q278 : PLift (G 18440 18494) := ⟨bs [0x12028480c480b,0xb88732c4813,0x90306a4a4819,0x12070481e481d,0x24180fbc4831,0x120f0483e483d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q279 : PLift (G 18494 18542) := ⟨bs [0x4fc61824847,0x607069e84855,0x242c7c324859,0x60784c28485b,0xc987618486b,0x2030608c486d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q280 : PLift (G 18542 18638) := ⟨bs [0x90f06f384879,0x30647b6a4897,0x12268489c489b,0x1228094648a1,0x245c743448b9,0x1233048ce48cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q281 : PLift (G 18638 18714) := ⟨bs [0x6130186048e5,0x91dc342c48ef,0xd4439de48f7,0x3a682cf64903,0x12430490e490d,0x4918616c4919] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q282 : PLift (G 18714 18774) := ⟨bs [0x923c2bc4491f,0x124a8492c492b,0x926c2f684937,0x124f0493e493d,0x1251049464945,0x1255049564955] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q283 : PLift (G 18774 18860) := ⟨bs [0x1258849644963,0x30f048324969,0x7f091b8496d,0x29f8599a4973,0x932c13c24997,0x126a849ac49ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q284 : PLift (G 18860 18920) := ⟨bs [0x126d049b649b5,0x1274849d449d3,0x93bc4c1649df,0x93c010c449e1,0x1279049e649e5,0x93cc115849e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q285 : PLift (G 18920 19010) := ⟨bs [0x128084a044a03,0x941c86524a0f,0x128704a1e4a1d,0x128884a244a23,0x947035cc4a39,0x948029184a41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q286 : PLift (G 19010 19074) := ⟨bs [0x129104a464a45,0x1dbc5cba4a57,0x129704a5e4a5d,0x129a84a6c4a6b,0x129f04a7e4a7d,0x9500205c4a81] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q287 : PLift (G 19074 19142) := ⟨bs [0x950c80ae4a87,0x31b058744a89,0x31b45bca4a8f,0x4ab0508a4ab1,0x12b084ac44ac3,0x12b104ac64ac5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q288 : PLift (G 19142 19212) := ⟨bs [0x12b504ad64ad5,0x12b684adc4adb,0x12bb04aee4aed,0x31f45b164aef,0x960c954a4b07,0x11a829124b0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q289 : PLift (G 19212 19260) := ⟨bs [0x6410727a4b0d,0x12c484b144b13,0x963c89f64b1f,0x12c904b264b25,0x12cc09f64b31,0x12ce84b3c4b3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q290 : PLift (G 19260 19320) := ⟨bs [0x1728126e4b43,0x32307f6c4b49,0x25ac901c4b59,0x12d904b664b65,0x64906eec4b6d,0x96ec4c024b77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q291 : PLift (G 19320 19392) := ⟨bs [0x12e104b864b85,0x12eb04bae4bad,0x12ec84bb44bb3,0x3c907c944bb5,0x12ee84bbc4bbb,0x977c1daa4bbf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q292 : PLift (G 19392 19430) := ⟨bs [0x12f284bcc4bcb,0x1948170e4bd9,0x3cb070544bdd,0x97bc169e4bdf,0x12f884be44be3,0x65306e084be5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q293 : PLift (G 19430 19470) := ⟨bs [0x4be83d2e4be9,0x4bf0752e4bf1,0x32a465224bf7,0x4c0075e64c01,0x980c96044c07,0x130304c0e4c0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q294 : PLift (G 19470 19508) := ⟨bs [0x1e6c2d364c0f,0x65708a964c15,0x130684c1c4c1b,0x984092dc4c21,0x130b04c2e4c2d,0x130c84c344c33] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q295 : PLift (G 19508 19572) := ⟨bs [0x65b824644c4b,0x131504c564c55,0x98ac29264c57,0x98c041944c61,0x98cc8a4a4c67,0x131c84c744c73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q296 : PLift (G 19572 19662) := ⟨bs [0x4c78216a4c79,0x98fc7ebe4c7f,0x132304c8e4c8d,0x132484c944c93,0x99303db04c99,0x133304cce4ccd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q297 : PLift (G 19662 19718) := ⟨bs [0x334086584ce1,0x334438024ce7,0x99e07e3e4cf1,0x669842fe4cf3,0x133f04cfe4cfd,0x134104d064d05] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q298 : PLift (G 19718 19764) := ⟨bs [0x9a1c44fa4d0f,0x134684d1c4d1b,0x9a4c55f44d27,0x3370662e4d29,0x33740b9e4d2f,0x134c84d344d33] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q299 : PLift (G 19764 19842) := ⟨bs [0x19c0256c4d41,0x26a866ce4d51,0x9ab004544d59,0x135904d664d65,0xb786ac64d6b,0x4d80562a4d81] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q300 : PLift (G 19842 19892) := ⟨bs [0x675843984d83,0x136304d8e4d8d,0x67707f5e4d95,0x136684d9c4d9b,0x9b606b6a4db1,0x136c84db44db3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q301 : PLift (G 19892 19962) := ⟨bs [0x9b9099824dc9,0x9b9c565e4dcf,0x9bac73704dd7,0x9bc052c84de1,0x137b04dee4ded,0x9bf03b724df9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q302 : PLift (G 19962 19998) := ⟨bs [0x137e84dfc4dfb,0x138104e064e05,0x138284e0c4e0b,0x9c2c67dc4e17,0x4e186a0e4e19,0x138704e1e4e1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q303 : PLift (G 19998 20052) := ⟨bs [0x683869364e2b,0x3e902e124e35,0x9c6c497e4e37,0x138f04e3e4e3d,0x9c9c7ff44e4f,0x139484e544e53] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q304 : PLift (G 20052 20114) := ⟨bs [0x166404424e5f,0x9ccc93304e67,0x4e7899b84e79,0x68b06e304e85,0x13a284e8c4e8b,0x274856e44e91] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q305 : PLift (G 20114 20150) := ⟨bs [0x13a504e964e95,0x13a684e9c4e9b,0x9d408a2c4ea1,0x117c2a204eaf,0x2cf831144eb3,0x13ad04eb64eb5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q306 : PLift (G 20150 20220) := ⟨bs [0x9d8096e64ec1,0x13b304ece4ecd,0x4ed034b64ed1,0x9dac77ce4ed7,0x9dd03e604ee9,0x13be84efc4efb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q307 : PLift (G 20220 20288) := ⟨bs [0x1dc72824f07,0x9e1018424f09,0x9e3066e24f19,0x13c904f264f25,0x13cb04f2e4f2d,0x9e7c95a04f3f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q308 : PLift (G 20288 20348) := ⟨bs [0x27a4981a4f49,0x13d884f644f63,0x9ecc09384f67,0x12b040f24f6d,0x13dd04f764f75,0x69f822bc4f7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q309 : PLift (G 20348 20394) := ⟨bs [0x27c04b864f81,0x13e104f864f85,0x35047e0c4f87,0x4f9007544f91,0x6a3097564fa5,0x9f506a7a4fa9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q310 : PLift (G 20394 20444) := ⟨bs [0x16c44d584faf,0x3524770e4fb7,0x3fc804504fbb,0x9f9c1aca4fcf,0x16d0362c4fd9,0x13f684fdc4fdb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q311 : PLift (G 20444 20522) := ⟨bs [0x13ff04ffe4ffd,0x9ffc49744fff,0x2db85b9a5003,0x14068501c501b,0x14070501e501d,0x281472645029] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q312 : PLift (G 20522 20594) := ⟨bs [0x140d050365035,0xa07c309c503f,0x1411050465045,0xa08c8f145047,0x6b181f385053,0x35a00f245071] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q313 : PLift (G 20594 20664) := ⟨bs [0xa0ec540e5077,0x1420850845083,0x1424850945093,0xa13c7c18509f,0x50a03cfc50a1,0xa16c8fba50b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q314 : PLift (G 20664 20732) := ⟨bs [0xa190947e50c9,0x1435050d650d5,0x6bd8711a50e3,0x143b050ee50ed,0x35f4921650ef,0x143e850fc50fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q315 : PLift (G 20732 20772) := ⟨bs [0x360420225107,0xe18137c510b,0x14430510e510d,0xa2203f5a5111,0xa22c8b205117,0x1448851245123] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q316 : PLift (G 20772 20858) := ⟨bs [0x1449051265125,0x144d051365135,0xa28ca1c25147,0x28a424e45149,0xa2e073e05171,0x10881785179] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q317 : PLift (G 20858 20904) := ⟨bs [0x518848265189,0xa31c66a0518f,0xa32c40625197,0x51a0a22a51a1,0x1468851a451a3,0xa34c3c7451a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q318 : PLift (G 20904 20964) := ⟨bs [0x28dc292851b9,0xa3804cfe51c1,0x1472851cc51cb,0x6d180a7e51d3,0x7cc766851df,0x1478851e451e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q319 : PLift (G 20964 21018) := ⟨bs [0x147d051f651f5,0x36a43dc251f7,0x36b020f45209,0x1484852145213,0x1485052165215,0x290c41c85219] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q320 : PLift (G 21018 21068) := ⟨bs [0x14868521c521b,0xa43c518e521f,0xa44c0e885227,0x1490852445243,0x75016445245,0x14928524c524b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q321 : PLift (G 21068 21144) := ⟨bs [0x5260811c5261,0x149b0526e526d,0x149c852745273,0xa50077d05281,0x14a4852945293,0xa52c4b625297] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q322 : PLift (G 21144 21188) := ⟨bs [0x13700916529d,0x14a9052a652a5,0x14aa852ac52ab,0x7e0750652b1,0x14ae852bc52bb,0x14b0852c452c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q323 : PLift (G 21188 21248) := ⟨bs [0xa58c56c252c7,0x1b98472452c9,0x14b6852dc52db,0x14b9052e652e5,0x14ba852ec52eb,0xa5fc555852ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q324 : PLift (G 21248 21320) := ⟨bs [0x14c5053165315,0x24f081ba531d,0x6ed82a385323,0x5340067c5341,0x14d1053465345,0xa68c7af65347] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q325 : PLift (G 21320 21384) := ⟨bs [0x2f984c7e534b,0x14d70535e535d,0x14d8853645363,0xa70008965381,0x14e0853845383,0xa70c83985387] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q326 : PLift (G 21384 21434) := ⟨bs [0xa71c6812538f,0x14e5053965395,0x2170749c5399,0xa73c5940539f,0x14ea853ac53ab,0x29dc9c0453b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q327 : PLift (G 21434 21500) := ⟨bs [0x14f6853dc53db,0xdfc40b053e9,0x37f47cd053ef,0x14fc853f453f3,0x14fd053f653f5,0x6ff80f7653fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q328 : PLift (G 21500 21558) := ⟨bs [0xa7fc0c8653ff,0x70103ac6540d,0x54107c845411,0x1504854145413,0x1c0805d05419,0x150d054365435] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q329 : PLift (G 21558 21590) := ⟨bs [0x38244faa5437,0x150e8543c543b,0xa8859485441,0x1c1809e65449,0x1514854545453,0x1515054565455] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q330 : PLift (G 21590 21648) := ⟨bs [0xa8bc34ec545f,0x10e05c585461,0x151a8546c546b,0x151b0546e546d,0xa8e055f65471,0xa91c3dda548f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q331 : PLift (G 21648 21714) := ⟨bs [0xa920907e5491,0x15270549e549d,0x2a54004e54a9,0x152c854b454b3,0x1531054c654c5,0x15343f9a54d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q332 : PLift (G 21714 21768) := ⟨bs [0x3894684054df,0xa9d0311454e9,0x153a854ec54eb,0xa9eca43a54f7,0x3090a55254fd,0xaa0c05385507] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q333 : PLift (G 21768 21822) := ⟨bs [0x15430550e550d,0x71789092551b,0x38c449ea5527,0x154a8552c552b,0xaa702f845539,0x154f0553e553d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q334 : PLift (G 21822 21872) := ⟨bs [0xaa9c29e4554f,0x27095405551,0x11f80aa2555b,0x1558855645563,0xaacc62965567,0xaadc86c8556f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q335 : PLift (G 21872 21944) := ⟨bs [0xaaf05bfc5579,0x1561055865585,0xab2c5edc5597,0xab509bd255a9,0xab60374255b1,0xab6c431e55b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q336 : PLift (G 21944 22014) := ⟨bs [0x55c858ce55c9,0x2aec0a2a55d9,0x39445bb255e7,0x2630a34c55ed,0x157c855f455f3,0x157f055fe55fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q337 : PLift (G 22014 22064) := ⟨bs [0x72b89fe4560b,0xac1c5200560f,0x1585056165615,0xac2c43065617,0xdc811805623,0xac5c8082562f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q338 : PLift (G 22064 22110) := ⟨bs [0x158c856345633,0xac708c0a5639,0xac7c0492563f,0x15928564c564b,0x7310625c564d,0x15970565e565d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q339 : PLift (G 22110 22154) := ⟨bs [0x3243334565f,0x159a8566c566b,0x39a023c85671,0x159d056765675,0x735824085683,0xad1095005689] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q340 : PLift (G 22154 22230) := ⟨bs [0x15a30568e568d,0xad1c3ad6568f,0x15a68569c569b,0x15ab056ae56ad,0xad602b0e56b1,0x15b5056d656d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q341 : PLift (G 22230 22280) := ⟨bs [0xadcc512a56e7,0x15bc856f456f3,0xadfc77d056ff,0xae006f665701,0x15c1057065705,0xae0c48445707] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q342 : PLift (G 22280 22350) := ⟨bs [0x15c28570c570b,0x173893ec5713,0x18e4aa94571f,0x15c8857245723,0xae8ca58c5747,0x15d30574e574d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q343 : PLift (G 22350 22410) := ⟨bs [0xaebc05aa575f,0xaec062d05761,0x45f06b4e576d,0xaeec26c85777,0x15df0577e577d,0xaf108fc45789] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q344 : PLift (G 22410 22482) := ⟨bs [0xaf406c2857a1,0x1d38276e57a9,0xaf5c465057af,0x74f08c0c57b5,0x15f1057c657c5,0xafa037be57d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q345 : PLift (G 22482 22544) := ⟨bs [0x15f4857d457d3,0x15f9057e657e5,0xafdc419057ef,0x1600858045803,0x46708478580d,0xb01c403e580f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q346 : PLift (G 22544 22620) := ⟨bs [0x1605058165815,0xb04c4b125827,0x468835de582b,0x12909c78582d,0x1615058565855,0x16168585c585b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q347 : PLift (G 22620 22670) := ⟨bs [0x16170585e585d,0x161b0586e586d,0x3af475a6586f,0x161c858745873,0x75f8ad5a587b,0x16230588e588d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q348 : PLift (G 22670 22718) := ⟨bs [0xb12c3fa05897,0x1628858a458a3,0x2c54224c58a9,0x1b483c9258ab,0x162d058b658b5,0x162f058be58bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q349 : PLift (G 22718 22770) := ⟨bs [0x58c04ee258c1,0xb18c869458c7,0x1634858d458d3,0x767077c658d5,0xb1bc11a858df,0xb1e0166258f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q350 : PLift (G 22770 22818) := ⟨bs [0xed47f6058f9,0xb1fc948658ff,0x1640859045903,0x3b64124e5917,0x47480ba6591b,0xb2404f225921] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q351 : PLift (G 22818 22902) := ⟨bs [0x1651059465945,0x16528594c594b,0x16530594e594d,0xb2ac27765957,0x16570595e595d,0x165d059765975] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q352 : PLift (G 22902 22964) := ⟨bs [0x1b885f2a597b,0xb310a6c05989,0xb33018945999,0xb33c74aa599f,0xb360348659b1,0x7798454a59b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q353 : PLift (G 22964 23022) := ⟨bs [0x166f059be59bd,0xb3a0389c59d1,0x1676859dc59db,0x47e81bf059e3,0xefca45459e9,0x167b059ee59ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q354 : PLift (G 23022 23058) := ⟨bs [0x167c859f459f3,0x167d059f659f5,0xb3fc69d459ff,0x780a6905a01,0x168305a0e5a0d,0x2d0822545a11] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q355 : PLift (G 23058 23100) := ⟨bs [0x28083c165a13,0xb42c04065a17,0xb43c75ce5a1f,0xb450a43e5a29,0xb45c31ae5a2f,0x168e85a3c5a3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q356 : PLift (G 23100 23174) := ⟨bs [0x169305a4e5a4d,0x787805385a5b,0x3c44a4cc5a67,0xb4ec6f685a77,0xb4fc08485a7f,0x78b03fc65a85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q357 : PLift (G 23174 23228) := ⟨bs [0x16a505a965a95,0x16a705a9e5a9d,0xb5405c345aa1,0x28482d685aa3,0xf1c6f585aa9,0x78f834565abb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q358 : PLift (G 23228 23298) := ⟨bs [0x16b485ad45ad3,0x793037f85ae5,0x1c43cc65aef,0x48c83e4c5afb,0x795042a25afd,0xb600b2885b01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q359 : PLift (G 23298 23358) := ⟨bs [0xb43f605b0f,0xb63070d45b19,0xb63cb5665b1f,0x16c905b265b25,0x16ca85b2c5b2b,0x16cf05b3e5b3d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q360 : PLift (G 23358 23448) := ⟨bs [0x2da450a85b49,0x16d285b4c5b4b,0xb6cc199e5b67,0x5b7836bc5b79,0x3d0473785b87,0xb72c86ba5b97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q361 : PLift (G 23448 23538) := ⟨bs [0x16e885ba45ba3,0x1e900c625bb1,0xb7908d7a5bc9,0x16f505bd65bd5,0x16fa85bec5beb,0x5bf073085bf1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q362 : PLift (G 23538 23568) := ⟨bs [0x16fc85bf45bf3,0x16ff05bfe5bfd,0x1c50918a5c05,0x5c0837365c09,0x170285c0c5c0b,0xb81c12e85c0f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q363 : PLift (G 23568 23624) := ⟨bs [0x7ad056105c1d,0xb8507fac5c29,0x147c6fce5c2f,0x170c85c345c33,0x5c380e785c39,0xb88c82985c47] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q364 : PLift (G 23624 23672) := ⟨bs [0x171285c4c5c4b,0x171305c4e5c4d,0x5c5083785c51,0xb8dc8b725c6f,0x171d05c765c75,0x41c2bea5c77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q365 : PLift (G 23672 23744) := ⟨bs [0x7b50a1625c7d,0xb90c072a5c87,0xb91011325c89,0xb94c5a2c5ca7,0x172f05cbe5cbd,0x3dd46ec05cbf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q366 : PLift (G 23744 23790) := ⟨bs [0x173085cc45cc3,0xb9903e245cc9,0x948781a5cd1,0xb9ac65b65cd7,0x7bd001e05cdd,0x173b05cee5ced] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q367 : PLift (G 23790 23834) := ⟨bs [0x2e7c240e5cf9,0x174105d065d05,0x174285d0c5d0b,0x174485d145d13,0xba2cad9e5d17,0xf8441085d19] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q368 : PLift (G 23834 23894) := ⟨bs [0x2e9869ee5d31,0x174f05d3e5d3d,0x5d405b425d41,0xba8c0bdc5d47,0x3e3480745d4f,0x21f074ca5d55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q369 : PLift (G 23894 23958) := ⟨bs [0x175685d5c5d5b,0x175905d665d65,0xbaccafc45d67,0x175b05d6e5d6d,0x3e508e905d79,0x176505d965d95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q370 : PLift (G 23958 24008) := ⟨bs [0x4ae826e65da3,0x1f3846f25da9,0x4af013cc5dad,0x5db8a0de5db9,0xbb8039545dc1,0x3e846c8e5dc7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q371 : PLift (G 24008 24062) := ⟨bs [0x177485dd45dd3,0xbbac5e725dd7,0x177705dde5ddd,0x177a85dec5deb,0xbbe08a0e5df1,0x7d503fc85dfd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q372 : PLift (G 24062 24104) := ⟨bs [0xbc0c74305e07,0x178305e0e5e0d,0x178485e145e13,0x7d784c685e1b,0xbc40b38e5e21,0xbc4c9fe65e27] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q373 : PLift (G 24104 24138) := ⟨bs [0x178a85e2c5e2b,0x178b05e2e5e2d,0xbc60a3c65e31,0x2f1c78505e39,0x7db030b85e45,0xbc907bb65e49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q374 : PLift (G 24138 24204) := ⟨bs [0x3ee477825e57,0xbcd08ede5e69,0x179c85e745e73,0x7df02a305e75,0x17a105e865e85,0x17a285e8c5e8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q375 : PLift (G 24204 24282) := ⟨bs [0xbd3c90045e9f,0x17a905ea65ea5,0xbd5c9ff65eaf,0xbd6c47e25eb7,0x4bc861445ebb,0x5ed832f45ed9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q376 : PLift (G 24282 24374) := ⟨bs [0x17bf05efe5efd,0x2f8410ae5f09,0x3f6053c45f11,0xbe4c77ca5f27,0x17cc85f345f33,0x7ef0483a5f35] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q377 : PLift (G 24374 24422) := ⟨bs [0x17ce85f3c5f3b,0xcb497125f47,0xbeac81f45f57,0x17d705f5e5f5d,0x17d885f645f63,0x19700c145f65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q378 : PLift (G 24422 24500) := ⟨bs [0xbeec63605f77,0x17de85f7c5f7b,0x7f70a7825f95,0x2fcc9f405f99,0xbf4004d05fa1,0x17ec85fb45fb3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q379 : PLift (G 24500 24552) := ⟨bs [0x17ef05fbe5fbd,0x7fb0a5ec5fc5,0xbf9c80825fcf,0x17f505fd65fd5,0x17f885fe45fe3,0xbfcc446a5fe7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q380 : PLift (G 24552 24660) := ⟨bs [0x7ff881be5ffb,0xc0206dea6011,0x4ce826e46023,0xc05c1f38602f,0x4024b5406037,0x1814860546053] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q381 : PLift (G 24660 24710) := ⟨bs [0xc0bc9e06605f,0x1819060666065,0x181a8606c606b,0x181c860746073,0xc0f0214c6079,0x1821060866085] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q382 : PLift (G 24710 24794) := ⟨bs [0x18270609e609d,0x182b060ae60ad,0x182e860bc60bb,0xc17c0b0860bf,0x1833060ce60cd,0xc1b08dac60d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q383 : PLift (G 24794 24852) := ⟨bs [0xc1bc445460df,0xc1d0397660e9,0x183d060f660f5,0x610857346109,0xc21c1170610f,0x1844861146113] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q384 : PLift (G 24852 24920) := ⟨bs [0x18468611c611b,0x81904158612d,0x40d07dc26139,0x18528614c614b,0x1855061566155,0xc2ac3bf86157] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q385 : PLift (G 24920 24978) := ⟨bs [0x18568615c615b,0xc2dc4368616f,0x30bc82466179,0xc30c351e6187,0x18628618c618b,0x619056ea6191] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q386 : PLift (G 24978 25038) := ⟨bs [0x1864861946193,0x18670619e619d,0x186d061b661b5,0xc38c585861c7,0x61c87b7c61c9,0x1873061ce61cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q387 : PLift (G 25038 25118) := ⟨bs [0x61e05c7e61e1,0xc3e0897261f1,0xc3fcc31e61ff,0xc410254e6209,0x273c6c346217,0x1e307eba621d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q388 : PLift (G 25118 25170) := ⟨bs [0x18885a566221,0xc44ca2446227,0x188e8623c623b,0xc4800c5c6241,0x18928624c624b,0x31288dee6251] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q389 : PLift (G 25170 25238) := ⟨bs [0x83180e906253,0xc4bc9aac625f,0x1899062666265,0x18a0862846283,0x18a30628e628d,0x18a5062966295] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q390 : PLift (G 25238 25304) := ⟨bs [0x18a68629c629b,0xc53c1eec629f,0x18a9062a662a5,0x8390675e62ad,0xfd01cf062d5,0xc5acbc1862d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q391 : PLift (G 25304 25350) := ⟨bs [0x18b6862dc62db,0xab0992662dd,0xc5d00a4a62e9,0x83f89bc262fb,0xc5fc575062ff,0x18c1063066305] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q392 : PLift (G 25350 25412) := ⟨bs [0x18c30630e630d,0xc62c86ba6317,0x18c70631e631d,0x27ac2742632f,0x18d002166341,0x84583bc06343] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q393 : PLift (G 25412 25464) := ⟨bs [0xc69cb900634f,0xc6bca1da635f,0xc6cc9a286367,0x18db0636e636d,0x63707c426371,0xc6ec67d46377] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q394 : PLift (G 25464 25562) := ⟨bs [0x18df0637e637d,0xc6fc7e12637f,0x18ec863b463b3,0x18f0880063c1,0x18f1063c663c5,0x27f069fa63d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q395 : PLift (G 25562 25604) := ⟨bs [0xc7d0204e63e9,0x18fa863ec63eb,0xc7dca16263ef,0x18fd063f663f5,0x640996e6401,0x1900864046403] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q396 : PLift (G 25604 25658) := ⟨bs [0x918c6fe6409,0x85709b0c6415,0x6420302e6421,0x42c4896e6427,0x190a8642c642b,0x42d027826439] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q397 : PLift (G 25658 25718) := ⟨bs [0x1910864446443,0x644825f26449,0xc89c1b6a644f,0x19170645e645d,0xc8cc3b026467,0x191d064766475] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q398 : PLift (G 25718 25772) := ⟨bs [0x1921064866485,0x8f0ae4c648d,0x1924864946493,0x165c688c649f,0x2498509c64a3,0x192a864ac64ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q399 : PLift (G 25772 25848) := ⟨bs [0x1930b73a64c1,0xc98c199c64c7,0xc990222664c9,0x1f081bf864db,0xc9e0488864f1,0xc9ec252a64f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q400 : PLift (G 25848 25914) := ⟨bs [0x327c143664f9,0x19428650c650b,0xca2070b46511,0x32904fee6521,0x437460f0652f,0x329c318c6539] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q401 : PLift (G 25914 25952) := ⟨bs [0xca7c649e653f,0x19528654c654b,0x19530654e654d,0x24d8c4e06553,0xcaac90e66557,0x4394b7f0655f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q402 : PLift (G 25952 26018) := ⟨bs [0x65706d986571,0x87501be8657d,0x19630658e658d,0xcb1cc1a6658f,0x1964865946593,0xcb40240265a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q403 : PLift (G 26018 26100) := ⟨bs [0x1969065a665a5,0x8790b54865ad,0xe884ace65b9,0x1971065c665c5,0x87d8854c65e3,0x197c865f465f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q404 : PLift (G 26100 26154) := ⟨bs [0x197e865fc65fb,0x1d24921a65ff,0xcc0086946601,0xcc0c2f926607,0x19870661e661d,0xcc506ee46629] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q405 : PLift (G 26154 26204) := ⟨bs [0x442076f66631,0x198e8663c663b,0x33201f0c6641,0xcc8ca6a46647,0x19930664e664d,0x88783dca665b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q406 : PLift (G 26204 26262) := ⟨bs [0x2220899e6661,0x8b8c53a6673,0x199f0667e667d,0x334433e26689,0x19a28668c668b,0x19a5066966695] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q407 : PLift (G 26262 26318) := ⟨bs [0xcd2c1e9c6697,0x19a68669c669b,0x88f0c73a66b5,0x66b80ad666b9,0x19b1066c666c5,0x1104dd866cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q408 : PLift (G 26318 26388) := ⟨bs [0xcda003b266d1,0x19b8866e466e3,0x8938313466eb,0x19bd066f666f5,0x9286f1e6703,0x19c4867146713] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q409 : PLift (G 26388 26432) := ⟨bs [0xce30724a6719,0xce3ca422671f,0x16ec7fce6727,0x7f028946731,0xce6c57a66737,0xdc42ca0673f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q410 : PLift (G 26432 26498) := ⟨bs [0x89b0742a6745,0xcea0cdbc6751,0x19d68675c675b,0x44f48aea676f,0xcef0b6f06779,0x228029226781] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q411 : PLift (G 26498 26574) := ⟨bs [0x19e1067866785,0x679078f26791,0x19ea867ac67ab,0x19ef067be67bd,0x33e046ac67c1,0x19f3067ce67cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q412 : PLift (G 26574 26648) := ⟨bs [0xcfbc7bc867df,0x19f9067e667e5,0x1a00868046803,0x34047aec6809,0xd020b6c66811,0x4564b4506817] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q413 : PLift (G 26648 26700) := ⟨bs [0x1a0b0682e682d,0xd070105e6839,0x1a0e8683c683b,0xd07c1bdc683f,0x1a11068466845,0x1a128684c684b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q414 : PLift (G 26700 26730) := ⟨bs [0x8b10cd12684d,0xd0ac3acc6857,0xd0b054be6859,0x1a170685e685d,0x1a18868646863,0xd0d070426869] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q415 : PLift (G 26730 26802) := ⟨bs [0x2e685b7c686b,0xd0e06cd26871,0xd10c7eac6887,0x344c8f566899,0xd13c3528689f,0xd16035aa68b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q416 : PLift (G 26802 26862) := ⟨bs [0x1a2f068be68bd,0x1a31068c668c5,0xd1a0435668d1,0xd1ac6cf068d7,0xd1c30c668e1,0x1a3b068ee68ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q417 : PLift (G 26862 26904) := ⟨bs [0xd1dcb40468ef,0xd1fc534068ff,0xf005c5a6901,0x540800c4690b,0x8c1081fa690d,0xd22c45c26917] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q418 : PLift (G 26904 26960) := ⟨bs [0x2a1047c66929,0xd25c8b72692f,0x1a50869446943,0xd28c97c66947,0x694889bc6949,0xd29cbec4694f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q419 : PLift (G 26960 27032) := ⟨bs [0x545051546965,0x1a5a8696c696b,0x34b820ce6971,0x1a60869846983,0xd31021606989,0x2a3c60706997] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q420 : PLift (G 27032 27078) := ⟨bs [0x1a68869a469a3,0x1a6c869b469b3,0x1a6d069b669b5,0x1a6e869bc69bb,0x69c0a62069c1,0x1a71069c669c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q421 : PLift (G 27078 27144) := ⟨bs [0x1a74869d469d3,0x469482c669df,0x1a78869e469e3,0x8d30b8e269e5,0xd3ec882669f7,0xd40c820c6a07] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q422 : PLift (G 27144 27242) := ⟨bs [0x1a8a86a2c6a2b,0xd46ccbd66a37,0x1a8f06a3e6a3d,0x5508732e6a4b,0xd4cca2e06a67,0xd4d093d46a69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q423 : PLift (G 27242 27284) := ⟨bs [0x1a9d06a766a75,0x1a9e86a7c6a7b,0xd50c120a6a87,0x8e10c6706a8d,0x354830026a91,0x8e1869346a93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q424 : PLift (G 27284 27398) := ⟨bs [0x1aa886aa46aa3,0x6ac076606ac1,0xd590c6c26ac9,0x4c0aa9c6ae1,0xd5ccd16c6ae7,0x1ac106b066b05] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q425 : PLift (G 27398 27450) := ⟨bs [0xd61c28d46b0f,0x8ec88126b11,0x8ed814026b23,0xd64c0b9c6b27,0x1acb06b2e6b2d,0x6b3819c86b39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q426 : PLift (G 27450 27528) := ⟨bs [0x6b4063766b41,0xd6ac341e6b57,0x6b58bfb46b59,0xd6bc87946b5f,0x1add06b766b75,0xd70c1a746b87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q427 : PLift (G 27528 27584) := ⟨bs [0xd71023466b89,0x1ae486b946b93,0x1cb0a6806b95,0x89c09386b9f,0x1aef06bbe6bbd,0x47d481ec6bbf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q428 : PLift (G 27584 27674) := ⟨bs [0x1af686bdc6bdb,0xd7c0b4d66be1,0x2b2ca58a6bef,0xd7fc31266bff,0x1b0106c066c05,0x240865466c19] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q429 : PLift (G 27674 27738) := ⟨bs [0xd850b7f06c29,0x903840c46c2b,0x482083c66c31,0x1b0d06c366c35,0x1b1506c566c55,0xd8b05e1c6c59] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q430 : PLift (G 27738 27768) := ⟨bs [0x302857aa6c5b,0xd8bc7d406c5f,0x3df0d3846c65,0x8ac55f26c67,0x3df859526c73,0xd8ec786a6c77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q431 : PLift (G 27768 27804) := ⟨bs [0x1b1f06c7e6c7d,0x1b2086c846c83,0xd91c0f9a6c8f,0xd9201c486c91,0x48643f306c97,0x1b2686c9c6c9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q432 : PLift (G 27804 27852) := ⟨bs [0x1b28d7066ca1,0x487056a06ca9,0xd95cae146caf,0x1b2c86cb46cb3,0xd98cd8a26cc7,0x1b3286ccc6ccb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q433 : PLift (G 27852 27942) := ⟨bs [0x913874dc6ceb,0x1b3d06cf66cf5,0x1b3f06cfe6cfd,0x1b4306d0e6d0d,0xda1c0f326d0f,0x1b4906d266d25] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q434 : PLift (G 27942 27984) := ⟨bs [0xda4c66fe6d27,0x1b4a86d2c6d2b,0x6d305aa06d31,0x748422c6d39,0x48d49ad46d3f,0xda9cd4266d4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q435 : PLift (G 27984 28052) := ⟨bs [0x91d05df26d5d,0x7d0225c6d61,0x1b5c86d746d73,0x1b5e86d7c6d7b,0xdafc88706d7f,0x1b6486d946d93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q436 : PLift (G 28052 28100) := ⟨bs [0x49107ffc6d99,0x9230c4206da5,0xdb6034c06db1,0xdb6c6b046db7,0xdb8066606dc1,0x1b7086dc46dc3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q437 : PLift (G 28100 28182) := ⟨bs [0x1b7306dce6dcd,0xea479b26dcf,0x1b7686ddc6ddb,0xdbec7d0a6df7,0x1b8086e046e03,0x1b8506e166e15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q438 : PLift (G 28182 28278) := ⟨bs [0x49646b726e17,0x6e28acb26e29,0x1b8c86e346e33,0x92f863aa6e3b,0x1b9106e466e45,0x1b9d06e766e75] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q439 : PLift (G 28278 28310) := ⟨bs [0x49a489006e77,0x1b9e86e7c6e7b,0xdd006cc46e81,0x126c7c206e89,0x1ba486e946e93,0x1ba506e966e95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q440 : PLift (G 28310 28404) := ⟨bs [0xdd3cbf226e9f,0x1baf06ebe6ebd,0x2c4c91d46ebf,0x1bb886ee46ee3,0x127c21ee6ee9,0x285811e26ef3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q441 : PLift (G 28404 28448) := ⟨bs [0x6ef81da26ef9,0x1bbe86efc6efb,0x1bc306f0e6f0d,0x6f10a6a06f11,0xde2c5d806f17,0x4a1404366f1f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q442 : PLift (G 28448 28518) := ⟨bs [0xde5cce946f2f,0x1bcf06f3e6f3d,0x1bd306f4e6f4d,0x1bd486f546f53,0x6f608a306f61,0x1bd906f666f65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q443 : PLift (G 28518 28572) := ⟨bs [0x25288bd46f79,0x1bdf06f7e6f7d,0x1be086f846f83,0x1be106f866f85,0xdf1c6ee66f8f,0x1be686f9c6f9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q444 : PLift (G 28572 28608) := ⟨bs [0x1be706f9e6f9d,0x1be886fa46fa3,0xdf5c45686faf,0x1bed06fb66fb5,0x1bee86fbc6fbb,0xdf7c6b846fbf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q445 : PLift (G 28608 28650) := ⟨bs [0x1bf286fcc6fcb,0x1dd038be6fcd,0x22680ada6fd3,0xdfac227c6fd7,0x1bf886fe46fe3,0xdfd0b3f46fe9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q446 : PLift (G 28650 28698) := ⟨bs [0x1bfc72e46ff1,0x1bfd06ff66ff5,0xdfecd9626ff7,0x95509c786ffd,0xe01c224a700f,0x380c23307019] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q447 : PLift (G 28698 28754) := ⟨bs [0xe03c3d82701f,0xe04cddd47027,0x1c0c870347033,0x381c63667039,0xe09c6066704f,0x705003ba7051] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q448 : PLift (G 28754 28814) := ⟨bs [0xe0ac09827057,0x1c18870647063,0x95f06eb07075,0xe0f09dd07079,0x4b041a1c7087,0x1c230708e708d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q449 : PLift (G 28814 28872) := ⟨bs [0x1c24679e7091,0x1c29070a670a5,0x1c2a870ac70ab,0x1c2e870bc70bb,0x9658a97270c3,0xe18c7a8e70c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q450 : PLift (G 28872 28934) := ⟨bs [0x4b347dd270cf,0x5a508ee270e5,0x1c3b070ee70ed,0xe1f02f9e70f9,0x191c299470ff,0x1c41071067105] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q451 : PLift (G 28934 29022) := ⟨bs [0x1c45071167115,0xe24095187121,0x1c4c871347133,0xe2a0b6ea7151,0x25c88dc87159,0x1c570715e715d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q452 : PLift (G 29022 29078) := ⟨bs [0xe2bc5f9a715f,0x1c58871647163,0x38b4bb547169,0x1c60871847183,0xe30cb0e07187,0x1c65071967195] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q453 : PLift (G 29078 29148) := ⟨bs [0x1c6b071ae71ad,0x1c70871c471c3,0xe390111a71c9,0x1c72871cc71cb,0x71d027dc71d1,0x1c76871dc71db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q454 : PLift (G 29148 29202) := ⟨bs [0x38f0821c71e1,0x4bf462be71ef,0x1c7d071f671f5,0x32a8131671fb,0x1a476a67207,0x390880fe7211] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q455 : PLift (G 29202 29252) := ⟨bs [0xe42cae1a7217,0x390c70ba7219,0x1c89072267225,0xe45c926a722f,0x1c8e8723c723b,0x1c90872447243] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q456 : PLift (G 29252 29328) := ⟨bs [0x98702a667255,0x4c44a82c7267,0xe4e0762a7271,0xe4ec5fec7277,0x4c5427b2727f,0x14d4492c728f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q457 : PLift (G 29328 29388) := ⟨bs [0x1ca5072967295,0x1ca68729c729b,0x98d8443272a3,0x1cac872b472b3,0xe58ca78a72c7,0x1cb2872cc72cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q458 : PLift (G 29388 29430) := ⟨bs [0x1cb3072ce72cd,0xe5ac947872d7,0xe5b0557272d9,0x1cb8872e472e3,0xe5dcd0be72ef,0x1cbd072f672f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q459 : PLift (G 29430 29502) := ⟨bs [0x1cbf072fe72fd,0x1cc0873047303,0x1cc30730e730d,0xe64051947321,0x1cca8732c732b,0x1ccf0733e733d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q460 : PLift (G 29502 29574) := ⟨bs [0x4ce4d0887357,0x1cd68735c735b,0xe6c08c0e7361,0xe6fccdea737f,0x1340dcca7381,0x1ce1073867385] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q461 : PLift (G 29574 29634) := ⟨bs [0x5704962738d,0x1ce4873947393,0x4d14823a739f,0x1608ca1273ab,0x9a5085e873bd,0xe780378673c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q462 : PLift (G 29634 29718) := ⟨bs [0xe790303073c9,0xe7bc0e0473df,0x1cf9073e673e5,0xe7cc522c73e7,0x338835a873f3,0x1d05074167415] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q463 : PLift (G 29718 29790) := ⟨bs [0x1d068741c741b,0x1d0b0742e742d,0xe87022147439,0xe87c4d2e743f,0xba0832c7441,0x1d170745e745d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q464 : PLift (G 29790 29864) := ⟨bs [0x9b38307a746b,0x1b689e9a747b,0x3a44bdca7489,0x1d230748e748d,0x1d268749c749b,0x19eccab074a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q465 : PLift (G 29864 29922) := ⟨bs [0x1d2a874ac74ab,0xe960a8ea74b1,0xe96c462a74b7,0xe970d03c74b9,0x1d37074de74dd,0xe9c03a1a74e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q466 : PLift (G 29922 30012) := ⟨bs [0xe9cc759474e7,0x42d81a5274fb,0xea0c1a847507,0xea3c9e34751f,0x1d49075267525,0x1d4e8753c753b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q467 : PLift (G 30012 30090) := ⟨bs [0x1d4f0753e753d,0x1d530754e754d,0xeabc304a755f,0x1d5a8756c756b,0xeaec28167577,0x75882a467589] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q468 : PLift (G 30090 30120) := ⟨bs [0x5e0885e2758b,0xeb2073c67591,0x4e649f347597,0x1d670759e759d,0xeb407d0675a1,0xeb4cc92075a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q469 : PLift (G 30120 30182) := ⟨bs [0x9cf0d6ec75b5,0x3adcd0e675b9,0x1d6e875bc75bb,0x75d040a475d1,0xebb0791a75d9,0x1d79075e675e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q470 : PLift (G 30182 30242) := ⟨bs [0x9d389dca75eb,0x1d7d075f675f5,0x1d7e875fc75fb,0x1d80876047603,0x4eb4e262760f,0x8704bfe7621] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q471 : PLift (G 30242 30308) := ⟨bs [0x1d8b0762e762d,0x9d9827fe7633,0x1707354763d,0xec7ca9b0763f,0x1d95076567655,0x1d98876647663] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q472 : PLift (G 30308 30368) := ⟨bs [0xecd019107669,0xecdc8074766f,0x1d9c876747673,0x1da1076867685,0x1da28768c768b,0xed3c2b8e769f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q473 : PLift (G 30368 30450) := ⟨bs [0x1dad076b676b5,0xed6c0c7276b7,0x9e58c41076c3,0x9e789d7276db,0xedbc291476df,0xede0e35e76f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q474 : PLift (G 30450 30510) := ⟨bs [0x1dc0877047703,0x1dc1077067705,0x1dc68771c771b,0x2b508b3e771d,0xee400efa7721,0x1dcb0772e772d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q475 : PLift (G 30510 30560) := ⟨bs [0x1dcd077367735,0x774055727741,0x1dd28774c774b,0xeeb063927759,0x1dd70775e775d,0x4f94b3d4775f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q476 : PLift (G 30560 30650) := ⟨bs [0x4fa04d4c7771,0xef00d0f67781,0xef4c2b6c77a7,0x1deb077ae77ad,0x1dec877b477b3,0xef701cd677b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q477 : PLift (G 30650 30704) := ⟨bs [0x1df1077c677c5,0xef9c352477cf,0x1df5077d677d5,0x77e09e0a77e1,0x3bf42eda77e9,0xefdc44ac77ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q478 : PLift (G 30704 30774) := ⟨bs [0x1dfc877f477f3,0xeff0833e77f9,0xf00c903a7807,0xe9090147825,0x1e0a8782c782b,0x44b004287835] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q479 : PLift (G 30774 30840) := ⟨bs [0x1e0f0783e783d,0x1e14878547853,0xf0b07e207859,0x786007927861,0x1e1b0786e786d,0xf0ec8fc27877] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q480 : PLift (G 30840 30872) := ⟨bs [0x3c3c1f787879,0x1e20878847883,0x1e21078867885,0x1e228788c788b,0x1e25078967895,0xf12c87e47897] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q481 : PLift (G 30872 30942) := ⟨bs [0x1e28a67c78a1,0x1e2b078ae78ad,0xf17c6c4a78bf,0x1e34878d478d3,0x2848204678d9,0x1e37078de78dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q482 : PLift (G 30942 31020) := ⟨bs [0xa13008a678e5,0x1e3e878fc78fb,0x1e40d0aa7901,0xf20c2f547907,0x1e49079267925,0x1e4a8792c792b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q483 : PLift (G 31020 31080) := ⟨bs [0x3c9c0b867939,0x50d40ca2793f,0x13682668794b,0x50e4d02e7957,0x1e570795e795d,0xf2cc8a2c7967] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q484 : PLift (G 31080 31148) := ⟨bs [0x22b0e6767969,0x1e5c879747973,0xf320d1d07991,0x45788c2c7993,0x1e68879a479a3,0x1e6a879ac79ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q485 : PLift (G 31148 31184) := ⟨bs [0xf35c5bb879af,0xb103eea79b1,0xf36c6e2879b7,0x1b10724a79c9,0x1e73079ce79cd,0x5134867079cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q486 : PLift (G 31184 31238) := ⟨bs [0xa270adb879d5,0xf3b0388c79d9,0xa298c38a79f3,0xf3ec0aa679f7,0xf3fc346279ff,0xa2b02aae7a05] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q487 : PLift (G 31238 31272) := ⟨bs [0xf41c8ffe7a0f,0xd90ebbe7a11,0x1e8507a167a15,0x1e8687a1c7a1b,0x1e8887a247a23,0xf44c41527a27] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q488 : PLift (G 31272 31334) := ⟨bs [0x1e8b07a2e7a2d,0x1e9287a4c7a4b,0xf4acc7927a57,0x7a5861c07a59,0xf4bc79ae7a5f,0xa330891c7a65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q489 : PLift (G 31334 31394) := ⟨bs [0x7a6827967a69,0x1e9f07a7e7a7d,0x1ea487a947a93,0x1ea687a9c7a9b,0x310cbb1a7a9f,0x7aa0a8a67aa1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q490 : PLift (G 31394 31512) := ⟨bs [0x1ea907aa67aa5,0x1ebb07aee7aed,0xa3f03ae27af5,0xf5f0dae87af9,0xf60062ec7b01,0xf62c8ed07b17] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q491 : PLift (G 31512 31548) := ⟨bs [0x7b18499e7b19,0x1ec707b1e7b1d,0x1eca87b2c7b2b,0x6290f60a7b35,0x5224bb567b37,0x1ece87b3c7b3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q492 : PLift (G 31548 31628) := ⟨bs [0xf69c538e7b4f,0xa470d3f47b55,0xf6bc5efa7b5f,0x3db8a6f07b71,0xf6ecabaa7b77,0x4698d3fe7b8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q493 : PLift (G 31628 31688) := ⟨bs [0x1ee687b9c7b9b,0xf74e5227ba1,0x5270be767ba9,0xf75cd2147baf,0x1eec87bb47bb3,0xf78cd9127bc7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q494 : PLift (G 31688 31742) := ⟨bs [0x1ef487bd47bd3,0xc64964a7be9,0xa538f4fa7beb,0xf7dc63587bef,0xf7e0ed267bf1,0xa550b2927bfd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q495 : PLift (G 31742 31818) := ⟨bs [0xf80cf7127c07,0x3e0cdd147c19,0x3728d2027c1b,0xf86032c67c31,0x131cc4f47c37,0x30800367c49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q496 : PLift (G 31818 31892) := ⟨bs [0xf8cc06507c67,0xf8d04c5c7c69,0x1f1c87c747c73,0x530076a47c81,0x1f2287c8c7c8b,0x1f2487c947c93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q497 : PLift (G 31892 31992) := ⟨bs [0x1f2887ca47ca3,0x1f3507cd67cd5,0x1f3687cdc7cdb,0x1f3907ce67ce5,0x63f0ca247ced,0xf9ec19227cf7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q498 : PLift (G 31992 32058) := ⟨bs [0x1f4087d047d03,0x7d08cf647d09,0x1f4687d1c7d1b,0x1f4707d1e7d1d,0x1408c8307d33,0xfa7039467d39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q499 : PLift (G 32058 32090) := ⟨bs [0x1f4e87d3c7d3b,0xfa7c52a07d3f,0x1f5107d467d45,0x1f5307d4e7d4d,0x1f5487d547d53,0x3eacdbd27d59] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q500 : PLift (G 32090 32160) := ⟨bs [0x1f5887d647d63,0x1f5d07d767d75,0x53a4dd107d77,0x1f6307d8e7d8d,0xfb1cd2e67d8f,0xfb3cd41a7d9f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q501 : PLift (G 32160 32214) := ⟨bs [0xa7905f107dad,0xfb6c163a7db7,0x1f6f07dbe7dbd,0xfb7c88127dbf,0x1f7287dcc7dcb,0x1f7507dd67dd5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q502 : PLift (G 32214 32298) := ⟨bs [0x7de82aa47de9,0x1f7b07dee7ded,0x21982b9a7dfb,0xfc00fb047e01,0x1f8107e067e05,0x7e284d347e29] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q503 : PLift (G 32298 32328) := ⟨bs [0xa83811de7e2b,0xfc5c04187e2f,0x1f8d07e367e35,0x1f90bc147e41,0x1f9087e447e43,0xfc8c3c2e7e47] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q504 : PLift (G 32328 32372) := ⟨bs [0x1f9507e567e55,0x1510754a7e61,0x5444c8f27e67,0x1f9a87e6c7e6b,0xfce0755c7e71,0x1f9c87e747e73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q505 : PLift (G 32372 32424) := ⟨bs [0xe40b1c7e79,0x1f9f07e7e7e7d,0x32a086dc7e91,0x1fa687e9c7e9b,0xa8d00f4e7e9d,0xfd4c09cc7ea7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q506 : PLift (G 32424 32492) := ⟨bs [0x2e102f687ead,0xfd70576e7eb9,0x1fae87ebc7ebb,0x1fb487ed47ed3,0xfdbc0ede7edf,0x1fba87eec7eeb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q507 : PLift (G 32492 32538) := ⟨bs [0x3f78a0847ef1,0xfdec406a7ef7,0x1fbe87efc7efb,0x1fc487f147f13,0x1fc507f167f15,0xfe30bc647f19] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q508 : PLift (G 32538 32588) := ⟨bs [0xfe60f1bc7f31,0x1fcc87f347f33,0xfe7004c87f39,0x1fcf07f3e7f3d,0x2728356c7f43,0x1fd287f4c7f4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q509 : PLift (G 32588 32648) := ⟨bs [0x1fd687f5c7f5b,0xfec076b67f61,0x65e89b7c7f63,0x65f038467f6d,0xfef0cf0e7f79,0xff0c5ca87f87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q510 : PLift (G 32648 32718) := ⟨bs [0x1fe307f8e7f8d,0xff5cc6827faf,0x1fed07fb67fb5,0xaa58fea07fc3,0x154cfd6c7fc9,0x1ff307fce7fcd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q511 : PLift (G 32718 32790) := ⟨bs [0xff9cb6ba7fcf,0x1ffb07fee7fed,0x2000880048003,0xaab87662800b,0x1001c1ad2800f,0x2005080168015] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q512 : PLift (G 32790 32840) := ⟨bs [0x20070801e801d,0x33401e948021,0x4938dd3c8023,0x1007cccaa803f,0x1c801cfc8041,0x1008c95008047] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q513 : PLift (G 32840 32918) := ⟨bs [0x20128804c804b,0xab307a328065,0x100ec25648077,0x20230808e808d,0x336cbc9c808f,0x2025080968095] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q514 : PLift (G 32918 32972) := ⟨bs [0x2029080a680a5,0x202a880ac80ab,0x202b080ae80ad,0x2ed0b4d480bd,0x80c8b60280c9,0xabb8462c80cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q515 : PLift (G 32972 33024) := ⟨bs [0x101ac1f5c80d7,0x2036880dc80db,0x4070cd3c80e1,0x101ccd7d080e7,0x18907a5480f5,0x101fc5a1c80ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q516 : PLift (G 33024 33074) := ⟨bs [0x2041081068105,0x20430810e810d,0x56101ae48119,0x20470811e811d,0x1025c4c84812f,0x813043248131] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q517 : PLift (G 33074 33150) := ⟨bs [0x204e8813c813b,0xac58d4ec8143,0x2054881548153,0x102b077528159,0x102bcf942815f,0x205f0817e817d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q518 : PLift (G 33150 33200) := ⟨bs [0x5654b394817f,0x10310d3e08189,0x20668819c819b,0xacd017b8819d,0x33dc6bf081a7,0x1035c142881af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q519 : PLift (G 33200 33290) := ⟨bs [0x206c881b481b3,0x206e881bc81bb,0x568471d281c7,0x1cdcb28a81df,0x1040cdbba8207,0x10410a91e8209] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q520 : PLift (G 33290 33344) := ⟨bs [0x2085082168215,0x1043c1464821f,0x2089082268225,0x1046014f08231,0xad9806828233,0x56d461d8823f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q521 : PLift (G 33344 33378) := ⟨bs [0x2090882448243,0x2091082468245,0x10490c4e68249,0x1049ca162824f,0x4130f43e8261] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q522 : PLift (G 33378 33458) := ⟨bs [0x254421cc826f,0x9281b52827b,0x1050022868281,0x20a1082868285,0x20a4882948293,0x1056020da82b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q523 : PLift (G 33458 33504) := ⟨bs [0x4ab0194082b5,0x20af082be82bd,0x1058c9b8c82c7,0x1059c821882cf,0x20b5082d682d5,0x2564c8f882df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q524 : PLift (G 33504 33570) := ⟨bs [0x41785f8682f1,0x105f0617e82f9,0x20bf082fe82fd,0x20c28830c830b,0x20c68831c831b,0x106426088321] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q525 : PLift (G 33570 33602) := ⟨bs [0x2bb868868329,0x20cb0832e832d,0x4af83c948333,0x20cd083368335,0x1067ca488833f,0x5780c0ce8341] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q526 : PLift (G 33602 33638) := ⟨bs [0xaf108ad6834d,0x8350b4728351,0x20d4883548353,0x106acb4188357,0x20d70835e835d,0x20d9083668365] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q527 : PLift (G 33638 33714) := ⟨bs [0x41b475b68369,0x106dcc13e836f,0x1071cbf44838f,0x1074ccf4e83a7,0x83b0b24683b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q528 : PLift (G 33714 33768) := ⟨bs [0x41dc161283b9,0x20f2883cc83cb,0x20f5083d683d5,0x1d4cbea083d7,0x20f7083de83dd,0x107cc068083e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q529 : PLift (G 33768 33812) := ⟨bs [0x57f0f21883e9,0x20fb083ee83ed,0x107fcafa883ff,0x1f10e8548405,0x1082057268411,0xb01850c48413] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q530 : PLift (G 33812 33872) := ⟨bs [0x2108884248423,0x2109084268425,0x210e8843c843b,0x8440c07e8441,0x1088cf8428447,0x11a4c2b0844f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q531 : PLift (G 33872 33938) := ⟨bs [0x584022068461,0x2119084668465,0x108ecb2828477,0x2120884848483,0x21228848c848b,0x2c30d9588491] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q532 : PLift (G 33938 34032) := ⟨bs [0x2125084968495,0x84a8634084a9,0x1095cb28a84af,0x2133084ce84cd,0x2138884e484e3,0x352c2d5c84ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q533 : PLift (G 34032 34128) := ⟨bs [0x109e0bbbe84f1,0x45cbcdc84f7,0x10a10caf48509,0x21430850e850d,0x21528854c854b,0x10a9cab80854f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q534 : PLift (G 34128 34172) := ⟨bs [0x85509a868551,0x21570855e855d,0x3b488d0c8563,0x215b0856e856d,0x10adc43ac856f,0x215e8857c857b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q535 : PLift (G 34172 34254) := ⟨bs [0x10b0c4b9a8587,0x2168885a485a3,0x2169085a685a5,0x42d42f7c85a9,0x59240e7685b7,0x2173085ce85cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q536 : PLift (G 34254 34298) := ⟨bs [0x2174885d485d3,0x2175085d685d5,0x2176885dc85db,0xfc0c31285e1,0x217a885ec85eb,0x42fc462a85f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q537 : PLift (G 34298 34338) := ⟨bs [0x6b30289a85fd,0x595465c885ff,0x4304553a8609,0x10c1c175c860f,0x10c2c2ec28617,0x10c40a2448621] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q538 : PLift (G 34338 34404) := ⟨bs [0x10c5c46c4862f,0x431c496e8639,0x10c7cb014863f,0x10c80d3ae8641,0xb3109612864d,0x2198886648663] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q539 : PLift (G 34404 34472) := ⟨bs [0x219d086768675,0x219f0867e867d,0x10d0c424e8687,0x8698d4a68699,0x4cf051e486a5,0x10d4cdcdc86a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q540 : PLift (G 34472 34514) := ⟨bs [0x21ac886b486b3,0x10d6c7f9286b7,0x21b0886c486c3,0xb3b0297286c5,0x94c9dd686cf,0x167883da86d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q541 : PLift (G 34514 34590) := ⟨bs [0x59e45f3086d7,0x59f0b70886e9,0x10ddc1d3486ef,0x21bd086f686f5,0x10e2cd6d48717,0x21c70871e871d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q542 : PLift (G 34590 34650) := ⟨bs [0x10e3c6e48871f,0x21ca8872c872b,0x10e5c8e0a872f,0x21cd087368735,0x10e8c34168747,0x10eb0c87a8759] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q543 : PLift (G 34650 34694) := ⟨bs [0x21d68875c875b,0x21da8876c876b,0x10ee049148771,0x10eec3e9a8777,0x10efcf7bc877f,0xb4b094588785] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q544 : PLift (G 34694 34758) := ⟨bs [0x10f1c3298878f,0x43d0efb887a1,0x10f501eb287a9,0x31582cda87b3,0x21ee887bc87bb,0x21f1087c687c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q545 : PLift (G 34758 34842) := ⟨bs [0x10f8c6fa887c7,0x21f2887cc87cb,0x21f7087de87dd,0x5aa4e87287f7,0x2200888048803,0x440cb3208819] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q546 : PLift (G 34842 34884) := ⟨bs [0x22068881c881b,0x26e41830881f,0x8820bc908821,0x18c4a2608837,0x220f0883e883d,0x2210888448843] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q547 : PLift (G 34884 34950) := ⟨bs [0x22147dfe8851,0x110c0bdee8861,0x110ccbf1c8867,0x221e8887c887b,0x2221088868885] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q548 : PLift (G 34950 35052) := ⟨bs [0x22249fb48891,0x2224888948893,0x2229088a688a5,0x1119c41e688cf,0x2234888d488d3,0x223a888ec88eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q549 : PLift (G 35052 35090) := ⟨bs [0x223b088ee88ed,0xb698265c88f3,0x223f088fe88fd,0xdb41b248909,0x22428890c890b,0x891037748911] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q550 : PLift (G 35090 35142) := ⟨bs [0x22468891c891b,0x2248889248923,0x36dc54a88927,0x224b0892e892d,0x112700fce8939,0x2251089468945] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q551 : PLift (G 35142 35202) := ⟨bs [0x22530894e894d,0x44a8bb948951,0x112acf2348957,0x2258889648963,0x113042da8981] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q552 : PLift (G 35202 35280) := ⟨bs [0x24b089e88995,0x22668899c899b,0xb7990b0e89b3,0x113707d4c89b9,0x2270889c489c3,0x1139c7cd489cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q553 : PLift (G 35280 35328) := ⟨bs [0x1ea1085489d1,0x2276889dc89db,0x5bf41b7a89ef,0xb7f0bf8e89f5,0x4ed8ac7889fb,0x113fcebf489ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q554 : PLift (G 35328 35402) := ⟨bs [0x228288a0c8a0b,0x5c1028f88a19,0x228888a248a23,0x6e9011548a35,0x11480edb88a41,0x2e18863a8a49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q555 : PLift (G 35402 35450) := ⟨bs [0x1149cc9c88a4f,0x229688a5c8a5b,0x114bc4e3e8a5f,0xb8901bb68a6d,0x114ed04108a77,0x1714f88c8a79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q556 : PLift (G 35450 35528) := ⟨bs [0x3d9017e28a85,0x2aa8d05a8aa3,0x22ac88ab48ab3,0x22ad08ab68ab5,0x5c8065de8ac1,0x1158c0c308ac7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q557 : PLift (G 35528 35574) := ⟨bs [0x6f08d8ea8acb,0x22b308ace8acd,0x8ad0ef7c8ad1,0x115ac61628ad7,0x5ca0a4c28af1,0x22bd08af68af5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q558 : PLift (G 35574 35672) := ⟨bs [0x1160c9ac88b07,0x1161056ce8b09,0x22c308b0e8b0d,0x22c488b148b13,0x5cc01e568b21,0x116ac1c048b57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q559 : PLift (G 35672 35760) := ⟨bs [0x22d708b5e8b5d,0x1172048f08b91,0x22e488b948b93,0x22e888ba48ba3,0x1175093288ba9,0x1175d100e8baf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q560 : PLift (G 35760 35804) := ⟨bs [0x4fd8a4da8bbb,0x22f508bd68bd5,0x8bd8554e8bd9,0x3e28d4428bdb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q561 : PLift (G 35804 35864) := ⟨bs [0x2ea108448be1,0x117ec7c4c8bf7,0x22ff08bfe8bfd,0x117fc57be8bff,0x230288c0c8c0b,0x1182c783a8c17] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q562 : PLift (G 35864 35924) := ⟨bs [0xbad056068c1d,0x1184c2fbc8c27,0xa04a6bc8c39,0x230e88c3c8c3b,0x1188d17828c47,0x231488c548c53] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q563 : PLift (G 35924 35984) := ⟨bs [0x231708c5e8c5d,0x118dca7848c6f,0x231e88c7c8c7b,0x11901102e8c81,0x8c88eff88c89,0x1191cc2688c8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q564 : PLift (G 35984 36018) := ⟨bs [0x8c985ad48c99,0x1193c27588c9f,0x1194d16888ca7,0x232a88cac8cab,0x232b08cae8cad,0x465835648cb1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q565 : PLift (G 36018 36098) := ⟨bs [0x233108cc68cc5,0x233708cde8cdd,0xbbd8c3328ce3,0x119d03fba8ce9,0x233c88cf48cf3,0x8d0068568d01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q566 : PLift (G 36098 36162) := ⟨bs [0x234288d0c8d0b,0x234308d0e8d0d,0x234888d248d23,0x8d2839988d29,0x387ceb268d37,0x11a8095a08d41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q567 : PLift (G 36162 36218) := ⟨bs [0xbc7828aa8d5b,0x11abc1ec48d5f,0x235c92228d71,0x5e51177e8d79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q568 : PLift (G 36218 36278) := ⟨bs [0x236108d868d85,0x11b2011508d91,0x236688d9c8d9b,0x11b4c92dc8da7,0x236b08dae8dad,0x236d08db68db5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q569 : PLift (G 36278 36342) := ⟨bs [0x237108dc68dc5,0x237288dcc8dcb,0x237488dd48dd3,0x11bb0eb088dd9,0x11bbc4ebc8ddf,0x237d08df68df5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q570 : PLift (G 36342 36434) := ⟨bs [0x5ea4a1e08df7,0x11c010a2a8e01,0x238508e168e15,0x11c3c3d048e1f,0x33b047f88e25,0x11ca0d3f08e51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q571 : PLift (G 36434 36480) := ⟨bs [0x71e8b17c8e63,0x473489968e69,0x239c88e748e73,0x239d08e768e75,0x11cf0479c8e79,0x11cfc8dc08e7f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q572 : PLift (G 36480 36528) := ⟨bs [0x23a308e8e8e8d,0x11d20a38e8e91,0x23aa88eac8eab,0x28c40e6a8eaf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q573 : PLift (G 36528 36560) := ⟨bs [0x23ac7a5e8eb1,0x3f702fd88ebd,0x11d8c0da68ec7,0x11d9c6a368ecf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q574 : PLift (G 36560 36608) := ⟨bs [0x23b488ed48ed3,0x23b688edc8edb,0x5f44b19a8ee7,0x23ba88eec8eeb,0x11ded12b28ef7,0x11dfc960c8eff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q575 : PLift (G 36608 36678) := ⟨bs [0x23c508f168f15,0xbed0b3948f1d,0xbed8e3d68f23,0x23cb08f2e8f2d,0x11e7c193c8f3f,0x23d108f468f45] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q576 : PLift (G 36678 36722) := ⟨bs [0x23d288f4c8f4b,0x23d488f548f53,0x5f90e5328f59,0x23d908f668f65,0x11ed04f468f69,0x2fd0ba448f71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q577 : PLift (G 36722 36782) := ⟨bs [0x23e088f848f83,0x23e308f8e8f8d,0x11f30e4e28f99,0x11f3c861e8f9f,0x23ea88fac8fab,0x23eb08fae8fad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q578 : PLift (G 36782 36834) := ⟨bs [0x23ec88fb48fb3,0x11f6cd2f88fb7,0x17f4d8488fb9,0x11f90d50e8fc9,0x23f508fd68fd5,0x47f016628fe1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q579 : PLift (G 36834 36900) := ⟨bs [0x11fdc4e0c8fef,0x8ff895928ff9,0x1334867a9007,0x24030900e900d,0x1202c4efe9017,0x2408890249023] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q580 : PLift (G 36900 36932) := ⟨bs [0x2409090269025,0x1808234a9031,0x602455069037,0x240e8903c903b,0x12080e4fe9041,0x2410890449043] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q581 : PLift (G 36932 37004) := ⟨bs [0x1209c2962904f,0x2414890549053,0x241b0906e906d,0xc0982de89073,0x2421090869085,0x24228908c908b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q582 : PLift (G 37004 37058) := ⟨bs [0x2425090969095,0x24268909c909b,0xc0d0b0ac909d,0x60750c3090af,0x90b8057490b9,0x3040f27e90c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q583 : PLift (G 37058 37140) := ⟨bs [0x2431090c690c5,0x121bc709890df,0x121d1141290e9,0x243f090fe90fd,0xc1590cea9103,0x2444891149113] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q584 : PLift (G 37140 37200) := ⟨bs [0x60c51dde9127,0x1d921029133,0x244f0913e913d,0x2451091469145,0x298514a4914f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q585 : PLift (G 37200 37274) := ⟨bs [0x9b0ddae9151,0x48b11b989161,0x122cd022e9167,0x245e8917c917b,0x2461091869185,0x9198fda49199] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q586 : PLift (G 37274 37338) := ⟨bs [0x24670919e919d,0x246e891bc91bb,0xc250732091bd,0x91c0cada91c1,0xe94837891c9,0x48ec80c291d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q587 : PLift (G 37338 37380) := ⟨bs [0x5358304e91db,0xc290a70c91ed,0x91f0ab8891f1,0xc29901e291f3,0x6150c18491f9,0x2480892049203] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q588 : PLift (G 37380 37424) := ⟨bs [0x2485092169215,0x2488d55a9221,0x617451d0922f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q589 : PLift (G 37424 37494) := ⟨bs [0x168121ca9241,0x6184451e9247,0x124ac0baa9257,0x249a8926c926b,0x49383de49271,0x249d092769275] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q590 : PLift (G 37494 37538) := ⟨bs [0x249f0927e927d,0xc35821949283,0x1250c552c9287,0x24a30928e928d,0x1253061609299,0x61c113492a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q591 : PLift (G 37538 37574) := ⟨bs [0x24aa892ac92ab,0x24ab092ae92ad,0x125700d2892b9,0x1257c0ee092bf,0x24b0892c492c3,0xc3b0c13e92c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q592 : PLift (G 37574 37634) := ⟨bs [0x24b2892cc92cb,0x24b5092d692d5,0x61e4fe4c92d7,0x125cd036892e7,0x24bc892f492f3,0x9300cdec9301] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q593 : PLift (G 37634 37694) := ⟨bs [0x24c28930c930b,0x1262120fe9311,0x12630747c9319,0x62140a60931f,0x75c8168c933b,0x24cf0933e933d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q594 : PLift (G 37694 37800) := ⟨bs [0xc45884ca9343,0xc4704b1e9355,0x4188401a9373,0x24e5093969395,0x1272c5dda9397,0x1274ce1c293a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q595 : PLift (G 37800 37862) := ⟨bs [0x76287f8893b3,0x24ed093b693b5,0x1278c37f293c7,0x127ac4bbe93d7,0x24f7093de93dd,0x24f9093e693e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q596 : PLift (G 37862 37952) := ⟨bs [0x3b2ca9bc93ef,0x62a4517e93f7,0x1280096049401,0x9408223c9409,0x2504894149413,0x1287ca536943f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q597 : PLift (G 37952 37994) := ⟨bs [0x2511094469445,0x25128944c944b,0x1289c1ade944f,0xc5d913fe9463,0x128ccd3449467,0x946842909469] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q598 : PLift (G 37994 38070) := ⟨bs [0x251b0946e946d,0x251e8947c947b,0x1b04b03a9497,0x63143bf6949f,0xc630f30494a5,0x252d094b694b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q599 : PLift (G 38070 38168) := ⟨bs [0xc658d18494c3,0x6340d47694e1,0x6344b9b694e7,0x363085909505,0x12a111fe49509,0x12a2c13189517] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q600 : PLift (G 38168 38220) := ⟨bs [0x12a410cd69521,0x12a4cdeb89527,0x254b0952e952d,0x254d095369535,0x9538dc049539,0x25528954c954b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q601 : PLift (G 38220 38274) := ⟨bs [0x12aac2bf89557,0x25570955e955d,0x6394ddaa955f,0x255d095769575,0x256061d49581] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q602 : PLift (G 38274 38322) := ⟨bs [0x958843c49589,0x213c7ede958f,0x25668959c959b,0x12b3c6a6c959f,0x256b095ae95ad,0xef8111895b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q603 : PLift (G 38322 38378) := ⟨bs [0x12b6cfe2695b7,0x63d005b895b9,0x256f095be95bd,0xbfc9b3895cf,0x77e8f7c095e3,0x4af4609895e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q604 : PLift (G 38378 38460) := ⟨bs [0x12bf040e295f9,0x894798a961f,0x12c5ccf8c962f,0x12c602bc69631,0x258d096369635,0x258e8963c963b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q605 : PLift (G 38460 38568) := ⟨bs [0xc850b7f0963d,0x2599096669665,0x12d1c13ac968f,0x25a70969e969d,0x12d40219896a1,0x12d4d1f8a96a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q606 : PLift (G 38568 38630) := ⟨bs [0x12d50f00496a9,0x12d80ac7296c1,0x25b2896cc96cb,0x12da069a696d1,0xc918de1e96d3,0x25b9096e696e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q607 : PLift (G 38630 38678) := ⟨bs [0x12ddc06f496ef,0x25be896fc96fb,0x25bf096fe96fd,0x25c30970e970d,0x3c6c680a970f,0xc97113a89715] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q608 : PLift (G 38678 38724) := ⟨bs [0x25c9097269725,0x25ca8972c972b,0x25cc897349733,0x2b346c309737,0x3268c5129739,0x25d0897449743] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q609 : PLift (G 38724 38784) := ⟨bs [0x4ba42bec9749,0x1207f7a9751,0x25d68975c975b,0x25d70975e975d,0x12edd154a976f,0x12efc3424977f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q610 : PLift (G 38784 38852) := ⟨bs [0x12f0cfc4a9787,0xca18483a9793,0x25e9097a697a5,0x97b0512097b1,0x12f6cef7e97b7,0xca585b3a97c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q611 : PLift (G 38852 38918) := ⟨bs [0x7970cac497cd,0x25f4897d497d3,0x4becd28297d9,0x25fa897ec97eb,0x12fec02e297f7,0xcab0989a9805] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q612 : PLift (G 38918 38972) := ⟨bs [0x3cd0e1209809,0x26028980c980b,0x2605098169815,0x6570cf009829,0x6574095c982f,0x260e8983c983b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q613 : PLift (G 38972 39044) := ⟨bs [0x6580f5829841,0x130a062709851,0x261a8986c986b,0x130dcf20e986f,0x13101079a9881,0x2620898849883] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q614 : PLift (G 39044 39108) := ⟨bs [0x1310c89129887,0x65c4ed4698a7,0x13160db7298b1,0x65d1229a98b9,0x1317c4e8698bf,0x2630898c498c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q615 : PLift (G 39108 39162) := ⟨bs [0x98c81c5698c9,0x1319c21d698cf,0xcbd12a8a98dd,0x3798062c98e3,0xcbf094de98f5,0x1e981f1a98f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q616 : PLift (G 39162 39218) := ⟨bs [0x263e898fc98fb,0xcc106360990d,0x1322c65b29917,0x6614f7f0991f,0x1325062849929,0x6620f5449931] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q617 : PLift (G 39218 39252) := ⟨bs [0x264e8993c993b,0x264f0993e993d,0x994009649941,0x1328c2e6a9947,0x66300b0e9949,0x2654899549953] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q618 : PLift (G 39252 39342) := ⟨bs [0x265f0997e997d,0x1891163e9985,0x13320d99e9991,0x2665099969995,0x26668999c999b,0x266b099ae99ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q619 : PLift (G 39342 39384) := ⟨bs [0x1335cb47299af,0x1bf5264299bf,0x222cac6899c7,0x2672899cc99cb,0xcd10886499cd,0x133ad087a99d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q620 : PLift (G 39384 39452) := ⟨bs [0x2679099e699e5,0x99f0a97499f1,0x267e899fc99fb,0x1341c11089a0f,0x268489a149a13,0x268689a1c9a1b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q621 : PLift (G 39452 39522) := ⟨bs [0x268909a269a25,0x269289a4c9a4b,0x1349cc6829a4f,0x2450e5ee9a55,0x134ad07949a57,0x9a6120fc9a61] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q622 : PLift (G 39522 39608) := ⟨bs [0x269d09a769a75,0x2bc5cfa9a7f,0x26a289a8c9a8b,0x135210e4c9a91,0x26a709a9e9a9d,0xebd27fa9ab7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q623 : PLift (G 39608 39672) := ⟨bs [0x26b089ac49ac3,0x1358ced8a9ac7,0x1359ccaf49acf,0x26ba89aec9aeb,0xce98ad309af3,0x135ed0fb49af7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q624 : PLift (G 39672 39734) := ⟨bs [0x135fcfcee9aff,0x1362cada89b17,0xced0bbde9b1d,0x1364c292e9b27,0x1365c5f469b2f,0x26cd09b369b35] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q625 : PLift (G 39734 39792) := ⟨bs [0x26d109b469b45,0x26d528de9b51,0x9b59281c9b59,0x26d889b649b63,0x136dc078e9b6f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q626 : PLift (G 39792 39842) := ⟨bs [0x228c6fbe9b77,0x26e309b8e9b8d,0x26e489b949b93,0xcf70dd429b95,0x1373c316c9b9f,0x4dd0b69c9ba1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q627 : PLift (G 39842 39884) := ⟨bs [0x67c43c089ba7,0x4dd8cbc09bb1,0x1376c84769bb7,0x26ef09bbe9bbd,0x26f109bc69bc5,0xcfb9087e9bcb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q628 : PLift (G 39884 39972) := ⟨bs [0x1379d19fe9bcf,0x26f709bde9bdd,0x137f03c269bf9,0x680022ea9c01,0x1382045b09c11,0x270889c249c23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q629 : PLift (G 39972 40014) := ⟨bs [0x456837689c2b,0x1385d1ef69c2f,0x270d09c369c35,0x4e24560c9c49,0x271309c4e9c4d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q630 : PLift (G 40014 40094) := ⟨bs [0x138bcf5449c5f,0x271909c669c65,0x138ccb7f09c67,0x138fc845c9c7f,0x1392cae949c97,0x272709c9e9c9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q631 : PLift (G 40094 40152) := ⟨bs [0xd0d896e89ca3,0x1395d242c9caf,0x272e89cbc9cbb,0x1397ce7269cbf,0x13980d35e9cc1,0x1c851a709cd7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q632 : PLift (G 40152 40194) := ⟨bs [0xb34c1769cd9,0x273889ce49ce3,0x4e74e6449ce9,0x9cf06f429cf1,0x273f09cfe9cfd,0x13a0094769d01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q633 : PLift (G 40194 40238) := ⟨bs [0x45d09dec9d15,0x13a4c99ec9d27,0xd1901cc89d2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q634 : PLift (G 40238 40290) := ⟨bs [0x274c990e9d31,0x274f09d3e9d3d,0x275509d569d55,0x275689d5c9d5b,0x9d6136aa9d61] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q635 : PLift (G 40290 40424) := ⟨bs [0x13b2ce9b29d97,0x3f0c212c9d9f,0xd230cdd29da5,0x4ed47d1e9da9,0x277089dc49dc3,0x13bcc5e189de7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q636 : PLift (G 40424 40430) := ⟨bs [0x277a89dec9deb,0x4630fdd49ded] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q637 : PLift (G 40430 40488) := ⟨bs [0x277cb0d29df1,0x278289e0c9e0b,0x1514f9cc9e17,0x278889e249e23,0x13c4c18ee9e27] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q638 : PLift (G 40488 40532) := ⟨bs [0x278b09e2e9e2d,0x278c89e349e33,0x278e89e3c9e3b,0x13c8cd7609e47,0x9e512a1e9e51,0x279489e549e53] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q639 : PLift (G 40532 40598) := ⟨bs [0x13cbc91009e5f,0x13cdc90849e6f,0x4f405f409e81,0x13d0c504e9e87,0x15241dae9e8f,0x27a509e969e95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q640 : PLift (G 40598 40698) := ⟨bs [0x13d40700a9ea1,0x27ac89eb49eb3,0x27af09ebe9ebd,0x69d471169ebf,0x27bd09ef69ef5,0x4f7d0a469ef9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q641 : PLift (G 40698 40764) := ⟨bs [0x27be89efc9efb,0x27c109f069f05,0x27c889f249f23,0x13e5c07249f2f,0x13e6cb4649f37,0x27ce89f3c9f3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q642 : PLift (G 40764 40824) := ⟨bs [0x7f68adda9f43,0x27d489f549f53,0x13ec0ea109f61,0x27db09f6e9f6d,0xd4982c309f73,0x13eed161e9f77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q643 : PLift (G 40824 40868) := ⟨bs [0x27df09f7e9f7d,0xff514069f89,0x13f1c197c9f8f,0x13f2111629f91,0x27e509f969f95,0x27e889fa49fa3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q644 : PLift (G 40868 40934) := ⟨bs [0x13f5d251a9faf,0x27ec89fb49fb3,0x13f80011e9fc1,0x6a84ced89fc7,0x6a94d8aa9fdf,0x27f909fe69fe5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q645 : PLift (G 40934 41012) := ⟨bs [0x27fa89fec9feb,0x27fd09ff69ff5,0xa0008096a001,0x28030a00ea00d,0xa021323ea021,0x280c8a034a033] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q646 : PLift (G 41012 41058) := ⟨bs [0x14070466aa039,0x1407c7446a03f,0x1409c6bdca04f,0x6ae481c6a057,0x28168a05ca05b,0x140c12adaa061] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q647 : PLift (G 41058 41118) := ⟨bs [0x281d0a076a075,0x503c30b0a079,0xa099137aa099,0x28270a09ea09d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q648 : PLift (G 41118 41178) := ⟨bs [0x4768b43ca0ab,0x282d0a0b6a0b5,0x1416c8224a0b7,0x282f0a0bea0bd,0xb7c4814a0c9,0xa0d8451ca0d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q649 : PLift (G 41178 41214) := ⟨bs [0xd6780d12a0db,0x141bd2ec0a0df,0x28390a0e6a0e5,0x6700b44a0f1,0xd698fe34a0f3,0x283f0a0fea0fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q650 : PLift (G 41214 41258) := ⟨bs [0x28410a106a105,0x28428a10ca10b,0x1421c04a0a10f,0x35b07d0aa111,0x28468a11ca11b,0xa1291d72a129] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q651 : PLift (G 41258 41342) := ⟨bs [0x6b74b490a12f,0x284d0a136a135,0x14280be14a141,0x28548a154a153,0x285d0a176a175,0x285f0a17ea17d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q652 : PLift (G 41342 41400) := ⟨bs [0x1430cb01ca187,0x28630a18ea18d,0x8150c2c2a1a5,0x286a8a1aca1ab,0xd790dc02a1ad,0x1436cb6f0a1b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q653 : PLift (G 41400 41480) := ⟨bs [0x28708a1c4a1c3,0xd7b11a56a1c5,0x28788a1e4a1e3,0x287b0a1eea1ed,0xd7f8238ca1fb,0x6c0409b4a207] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q654 : PLift (G 41480 41540) := ⟨bs [0x4808e706a213,0x28888a224a223,0x1445032a0a229,0x1445c41f4a22f,0x2070b100a231,0xd8582ebaa243] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q655 : PLift (G 41540 41604) := ⟨bs [0x1448c7fd2a247,0x31f10ea6a24d,0x289a8a26ca26b,0x144f03112a279,0x289f0a27ea27d,0x28a08a284a283] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q656 : PLift (G 41604 41642) := ⟨bs [0x145104d58a289,0x28a28a28ca28b,0x24203536a291,0x82109100a295,0x28a68a29ca29b,0x6c70f534a2a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q657 : PLift (G 41642 41688) := ⟨bs [0x1455c80b4a2af,0x28ac8a2b4a2b3,0xd8f8f09ca2bb,0x28b10a2c6a2c5,0xa2d0d3b8a2d1,0x145ac70cca2d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q658 : PLift (G 41688 41760) := ⟨bs [0x145ed06aca2f7,0x28c0dec0a301,0x14610b08ea309,0x1463cb832a31f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q659 : PLift (G 41760 41814) := ⟨bs [0x519108eaa321,0x28ca8a32ca32b,0xa330e8bca331,0x14690cceea349,0x6ce0dc88a351,0x28d50a356a355] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q660 : PLift (G 41814 41888) := ⟨bs [0x28dc8a374a373,0x51bd1d56a379,0xd9f8dadaa37b,0x6d0409c2a387,0x1472c987ca397,0x1473c96cea39f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q661 : PLift (G 41888 41942) := ⟨bs [0x28e90a3a6a3a5,0x14750e122a3a9,0x1475cc1f4a3af,0x6d24a2fea3b7,0x1478d0140a3c7,0x28f50a3d6a3d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q662 : PLift (G 41942 41982) := ⟨bs [0xda783bb8a3db,0x147c12c94a3e1,0x28f90a3e6a3e5,0x147cc8192a3e7,0xa3f13b06a3f1,0x28ff0a3fea3fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q663 : PLift (G 41982 42024) := ⟨bs [0x147fcab8ca3ff,0x1481c1c42a40f,0xdad11708a41d,0x14840f698a421,0x29088a424a423,0x1484ca4f4a427] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q664 : PLift (G 42024 42084) := ⟨bs [0x3bb91842a43b,0x8370cc40a44d,0x148ac04aca457,0x148b0bd78a459,0x29188a464a463] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q665 : PLift (G 42084 42170) := ⟨bs [0x5234f860a469,0x291d0a476a475,0x29248a494a493,0x29268a49ca49b,0x292b0a4aea4ad,0x149713d12a4b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q666 : PLift (G 42170 42210) := ⟨bs [0x29308a4c4a4c3,0xdbb06d02a4c5,0xdbb82842a4cb,0x1b79432aa4d1,0x29350a4d6a4d5,0xa4e10db6a4e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q667 : PLift (G 42210 42282) := ⟨bs [0x293b0a4eea4ed,0x6df47e4ea4ef,0x293c8a4f4a4f3,0x149fc787ea4ff,0x14a2134cca511,0xa5280ed0a529] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q668 : PLift (G 42282 42332) := ⟨bs [0x294a8a52ca52b,0x294d0a536a535,0x294e8a53ca53b,0xdc5946d6a543,0x29548a554a553,0x2c182beca55b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q669 : PLift (G 42332 42392) := ⟨bs [0x14ac0afc4a561,0x295b0a56ea56d,0x14aed02aca577,0x630cc66a585,0x29628a58ca58b,0x14b2d3d34a597] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q670 : PLift (G 42392 42438) := ⟨bs [0x29670a59ea59d,0x29688a5a4a5a3,0x14b4c2c40a5a7,0x14b505bcca5a9,0xa5c0b5baa5c1,0x29710a5c6a5c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q671 : PLift (G 42438 42468) := ⟨bs [0x29728a5cca5cb,0x84a8347ca5d3,0x6e909c6ea5d9,0x29770a5dea5dd,0x6e942ab6a5df,0x27083a50a5e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q672 : PLift (G 42468 42534) := ⟨bs [0xa5e90054a5e9,0x14bec0576a5f7,0x297e8a5fca5fb,0x29808a604a603,0x29830a60ea60d,0x29890a626a625] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q673 : PLift (G 42534 42612) := ⟨bs [0x298f0a63ea63d,0x13910d7ea649,0x29928a64ca64b,0x14ca14084a651,0x29970a65ea65d,0x299c8a674a673] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q674 : PLift (G 42612 42684) := ⟨bs [0x820d7dea691,0x29a48a694a693,0x14d3031e6a699,0xde38a832a6ab,0x29ad0a6b6a6b5,0x29ae8a6bca6bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q675 : PLift (G 42684 42720) := ⟨bs [0x14d80cb0ea6c1,0x6f30535ea6c9,0x131114e4a6cd,0x14d9c9916a6cf,0xde70c602a6d5,0x14dbd4398a6df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q676 : PLift (G 42720 42768) := ⟨bs [0x14dcd043ca6e7,0xa6f0155ca6f1,0x2fb489baa6f7,0x14dfc7766a6ff,0x14e1d34a6a70f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q677 : PLift (G 42768 42830) := ⟨bs [0x2750662ca715,0xded92a60a723,0xa7284cd8a729,0x29cb0a72ea72d,0x29d10a746a745,0x29d30a74ea74d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q678 : PLift (G 42830 42900) := ⟨bs [0x14ead0f3ca757,0x771311ea759,0x29d90a766a765,0xdf38d278a76b,0x14edc9714a76f,0x29e48a794a793] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q679 : PLift (G 42900 42954) := ⟨bs [0xdf70b062a795,0x29ea8a7aca7ab,0x14f60c55aa7b1,0x37e90b58a7b9,0x14f7d3670a7bf,0x17f877fca7c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q680 : PLift (G 42954 43014) := ⟨bs [0xa7d0b290a7d1,0x14fad15d8a7d7,0xdfd9451ea7e3,0x29fb0a7eea7ed,0xdff83ae8a7fb,0x2a010a806a805] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q681 : PLift (G 43014 43068) := ⟨bs [0x2a028a80ca80b,0x2a070a81ea81d,0xa8286734a829,0x2a0a8a82ca82b,0x1506d0bdea837,0x2a0e8a83ca83b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q682 : PLift (G 43068 43160) := ⟨bs [0xe07116d4a855,0x150bc4548a85f,0x2a1b0a86ea86d,0x2a1f0a87ea87d,0x1511d4940a88f,0x1512c3a82a897] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q683 : PLift (G 43160 43238) := ⟨bs [0x15150133ea8a9,0x2a2d0a8b6a8b5,0x70813a2ca8c1,0x1518cda18a8c7,0x151ac95bea8d7,0x2a390a8e6a8e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q684 : PLift (G 43238 43320) := ⟨bs [0x2a3f0a8fea8fd,0x1520c3ce2a907,0x2a448a914a913,0xe17836c6a91b,0x5498283ca931,0x1526c9ccea937] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q685 : PLift (G 43320 43404) := ⟨bs [0x70d104c2a939,0x2a508a944a943,0x152fc52cca97f,0x2a610a986a985,0x71050f94a987,0x2a628a98ca98b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q686 : PLift (G 43404 43482) := ⟨bs [0x87a8bcbea993,0x2a688a9a4a9a3,0x2d436d0a9b1,0x2a6e8a9bca9bb,0x15380030ca9c1,0x54ed0154a9d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q687 : PLift (G 43482 43574) := ⟨bs [0x153bc6064a9df,0x2a7a8a9eca9eb,0x2a7f0a9fea9fd,0x2a850aa16aa15,0x1542d494eaa17,0x2a8d0aa36aa35] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q688 : PLift (G 43574 43610) := ⟨bs [0x551c0bacaa39,0x2a8e8aa3caa3b,0x71851382aa47,0x2a930aa4eaa4d,0x154aca6faaa57,0xaa585c48aa59] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q689 : PLift (G 43610 43662) := ⟨bs [0x2a970aa5eaa5d,0x2a9a8aa6caa6b,0x154e004c2aa71,0x2aa13cc0aa81,0x2aa08aa84aa83,0x2aa30aa8eaa8d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q690 : PLift (G 43662 43722) := ⟨bs [0x2aa50aa96aa95,0x88cb98aaab,0x71d4ecdeaabf,0xe3b0adbeaac5,0x11149520aac9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q691 : PLift (G 43722 43782) := ⟨bs [0x38f91cf4aae9,0x71f42f20aaef,0x39004564ab01,0x2ac10ab06ab05] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q692 : PLift (G 43782 43854) := ⟨bs [0x1560d11e0ab07,0x2ac28ab0cab0b,0xe410f03cab0d,0x55887174ab11,0x156301e86ab19,0x2ad30ab4eab4d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q693 : PLift (G 43854 43890) := ⟨bs [0xe47821baab5b,0x2adc4fc6ab71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q694 : PLift (G 43890 43952) := ⟨bs [0x2db8c294ab73,0x1f30aa0cab89,0x2ae70ab9eab9d,0x1574d24deaba7,0x1575d22f8abaf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q695 : PLift (G 43952 43992) := ⟨bs [0x15771059eabb9,0x2868ab3cabbb,0x3940e49aabc1,0x2af10abc6abc5,0x2af48abd4abd3,0x157ac3788abd7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q696 : PLift (G 43992 44042) := ⟨bs [0x2af70abdeabdd,0x72a079f2abf1,0x2afd0abf6abf5,0x2afe8abfcabfb,0x4c70770cabfd,0x72b144a4ac09] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q697 : PLift (G 44042 44102) := ⟨bs [0x2b050ac16ac15,0x2b068ac1cac1b,0x16f41234ac27,0x1586cdf0cac37,0xac382bb2ac39,0x4c91053eac45] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q698 : PLift (G 44102 44160) := ⟨bs [0x1589c5e44ac4f,0x158ac9e96ac57,0x2b168ac5cac5b,0xac6140d6ac61,0x2b188ac64ac63,0x158fd3558ac7f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q699 : PLift (G 44160 44208) := ⟨bs [0x2b228ac8cac8b,0x2b248ac94ac93,0x2b270ac9eac9d,0x228953e4aca9,0xe638ca7aacab,0x1595c5edeacaf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q700 : PLift (G 44208 44270) := ⟨bs [0x2b2f0acbeacbd,0x159b03354acd9,0xace1023eace1,0x159cc2c36ace7,0x2b3a8acecaceb,0x2b3b0aceeaced] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q701 : PLift (G 44270 44358) := ⟨bs [0x56787936acf1,0x159ed0b3cacf7,0x159f01f58acf9,0x2b410ad06ad05,0x15a7d143cad3f,0x2b510ad46ad45] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q702 : PLift (G 44358 44450) := ⟨bs [0x2b548ad54ad53,0x2b570ad5ead5d,0x15abc4b0ead5f,0x2b590ad66ad65,0xad80e19aad81,0xada12adcada1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q703 : PLift (G 44450 44508) := ⟨bs [0x2b690ada6ada5,0x2b708adc4adc3,0xe7b91c3eadcb,0x2b74f93aadd1,0x2b750add6add5,0x2b768addcaddb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q704 : PLift (G 44508 44550) := ⟨bs [0x15bccaebaade7,0x2b7c8adf4adf3,0x2b7d0adf6adf5,0x15bf064d6adf9,0x15bfc65f8adff,0x2b810ae06ae05] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q705 : PLift (G 44550 44624) := ⟨bs [0xe8185410ae13,0x2b888ae24ae23,0x4d6836a8ae2b,0x15c90d542ae49,0x2b930ae4eae4d,0x743540baae4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q706 : PLift (G 44624 44684) := ⟨bs [0xae5831acae59,0x15cc12fb8ae61,0x7444d6d8ae67,0x2b9a8ae6cae6b,0x15ce0c11aae71,0x2ba28ae8cae8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q707 : PLift (G 44684 44742) := ⟨bs [0x15d1c2ccaae8f,0x2ba68ae9cae9b,0x2ba70ae9eae9d,0x15d4d1f98aea7,0x15d702d72aeb9,0x2bb10aec6aec5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q708 : PLift (G 44742 44790) := ⟨bs [0x15da138feaed1,0x3f9873daaee3,0x35d0a966aee5,0xaee936f8aee9,0x2bbd0aef6aef5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q709 : PLift (G 44790 44844) := ⟨bs [0x2bbf0aefeaefd,0x74b07524af09,0x2bc48af14af13,0x15e4cd9caaf27,0x64191fecaf2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q710 : PLift (G 44844 44910) := ⟨bs [0x35e8022eaf33,0x2bd08af44af43,0x15e9c7f64af4f,0x15eacfbeaaf57,0xe9d093ceaf5d,0x2bdb0af6eaf6d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q711 : PLift (G 44910 44964) := ⟨bs [0xe9f0bec8af75,0x15efcf71caf7f,0x2be28af8caf8b,0x751001d6af99,0x15f3d0656af9f,0x2be88afa4afa3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q712 : PLift (G 44964 45054) := ⟨bs [0x2ed93f64afab,0x15f6cbebeafb7,0x2bee8afbcafbb,0x15f9ca286afcf,0x2bf50afd6afd5,0x2bff0affeaffd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q713 : PLift (G 45054 45128) := ⟨bs [0x2c010b006b005,0x2c050b016b015,0x2c068b01cb01b,0x1607ccaeab03f,0x1608071d0b041,0x1608c3000b047] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q714 : PLift (G 45128 45182) := ⟨bs [0x2c128b04cb04b,0x64caa3eb051,0x2c148b054b053,0x58353ea2b069,0x64d91324b07b,0x2c1f0b07eb07d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q715 : PLift (G 45182 45264) := ⟨bs [0x1610c29deb087,0x2c230b08eb08d,0x161611d98b0b1,0x1617d2884b0bf,0xebb8b6acb0cb,0x3284a57eb0cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q716 : PLift (G 45264 45320) := ⟨bs [0xb0e15d34b0e1,0xb0e869e0b0e9,0x2c3b0b0eeb0ed,0x2c3e8b0fcb0fb,0x2c410b106b105,0x3294dfacb107] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q717 : PLift (G 45320 45378) := ⟨bs [0xb1108bcab111,0x76101a70b119,0x2c470b11eb11d,0x1623c8f58b11f,0x162610a34b131,0x16280a584b141] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q718 : PLift (G 45378 45440) := ⟨bs [0x2c530b14eb14d,0xec78adb2b15b,0x2c590b166b165,0xec993ca2b173,0x58bc2ddcb179,0x7654fb2eb17f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q719 : PLift (G 45440 45534) := ⟨bs [0x3b394054b1a9,0x2c6c8b1b4b1b3,0x16370e3eeb1b9,0x1637c1c1cb1bf,0x2c748b1d4b1d3,0x2c770b1deb1dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q720 : PLift (G 45534 45554) := ⟨bs [0x40b0977eb1e5,0x1b6138dab1f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q721 : PLift (G 45554 45614) := ⟨bs [0x65b14d20b1f5,0x1640153a0b201,0x2c848b214b213,0x2c850b216b215,0x1643c850ab21f,0x2c8b0b22eb22d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q722 : PLift (G 45614 45678) := ⟨bs [0x1647d5decb23f,0x32f03996b249,0x2c968b25cb25b,0x2c988b264b263,0x164d092beb269,0x2c9b0b26eb26d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q723 : PLift (G 45678 45738) := ⟨bs [0xedf906d4b27b,0x16508512b281,0x2ca28b28cb28b,0x5954eb66b2a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q724 : PLift (G 45738 45818) := ⟨bs [0x477c6d3eb2b7,0x2caf0b2beb2bd,0xee581c78b2c3,0x1658c221cb2c7,0x2cb48b2d4b2d3,0x775065e0b2f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q725 : PLift (G 45818 45854) := ⟨bs [0x2cbf0b2feb2fd,0x775493ecb2ff,0x2cc08b304b303,0x16610264eb309,0x166202620b311,0xeed00362b31d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q726 : PLift (G 45854 45950) := ⟨bs [0x1664c3cdeb327,0x2ccb0b32eb32d,0x1667ccec2b33f,0x2cd10b346b345,0x166ed63ccb377,0x2cdf0b37eb37d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q727 : PLift (G 45950 46022) := ⟨bs [0x1670033fcb381,0x1670d6160b387,0x2ce48b394b393,0x2ce68b39cb39b,0x2ce90b3a6b3a5,0x2cf10b3c6b3c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q728 : PLift (G 46022 46092) := ⟨bs [0x2cf28b3ccb3cb,0x167d4492b3e1,0x8fe877ceb3e3,0x2cfb0b3eeb3ed,0xb3f859e6b3f9,0x2d028b40cb40b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q729 : PLift (G 46092 46148) := ⟨bs [0x2d030b40eb40d,0x2d048b414b413,0x1682c04e4b417,0x2d0d0b436b435,0xf050d48cb43d,0x2d108b444b443] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q730 : PLift (G 46148 46200) := ⟨bs [0x168914a62b449,0xf0784444b45b,0x2d190b466b465,0x168cc4866b467,0x2d1a8b46cb46b,0x168ec77eab477] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q731 : PLift (G 46200 46274) := ⟨bs [0xf0b8a05ab48b,0x2d250b496b495,0x2d270b49eb49d,0x2d2d0b4b6b4b5,0x1697cdd4cb4bf,0x5a6043e4b4c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q732 : PLift (G 46274 46338) := ⟨bs [0x1698c3822b4c7,0x2d370b4deb4dd,0x2d388b4e4b4e3,0x2d390b4e6b4e5,0x169ecfbeab4f7,0x16a00ce0cb501] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q733 : PLift (G 46338 46440) := ⟨bs [0x2d430b50eb50d,0xe7d6546b50f,0xf190dbb2b52d,0x16a7cda20b53f,0xf1b94182b54b,0xbb5215ab567] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q734 : PLift (G 46440 46478) := ⟨bs [0xa14f64ab569,0x16add14beb56f,0x912922beb573,0x16af0bef6b579,0x79051034b587,0x2d630b58eb58d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q735 : PLift (G 46478 46550) := ⟨bs [0x16b305910b599,0x2d688b5a4b5a3,0x2d6a8b5acb5ab,0x16b5ce062b5af,0x67d89c74b5bb,0x2d750b5d6b5d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q736 : PLift (G 46550 46602) := ⟨bs [0x16bbc7164b5df,0x286cd376b5e7,0x2d7b0b5eeb5ed,0x2d7f0b5feb5fd,0x16bfc6474b5ff,0xb6084ca0b609] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q737 : PLift (G 46602 46644) := ⟨bs [0x3808a3fab61b,0x16c500328b629,0x16c5cce88b62f,0x2d8c8b634b633] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q738 : PLift (G 46644 46692) := ⟨bs [0x341044b4b639,0x16c8ced8ab647,0x16cad2648b657,0x1e64905eb659,0x16cbd4c08b65f,0x2d988b664b663] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q739 : PLift (G 46692 46758) := ⟨bs [0x13351704b66f,0x2da08b684b683,0x16d0d264cb687,0x2da68b69cb69b,0x16d3c2a14b69f,0x2da90b6a6b6a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q740 : PLift (G 46758 46818) := ⟨bs [0x2dac448cb6b1,0x2dac8b6b4b6b3,0x16dad41c0b6d7,0x2db68b6dcb6db,0xb6e1110cb6e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q741 : PLift (G 46818 46868) := ⟨bs [0x2db88b6e4b6e3,0x2dbb0b6eeb6ed,0x79f4c69ab6ef,0x2dc10b706b705,0x42907cd0b70d,0x2dc48b714b713] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q742 : PLift (G 46868 46958) := ⟨bs [0x2dc70b71eb71d,0x5b9406d2b729,0x9290607cb735,0x16e8ce68cb747,0x2dd50b756b755,0x8103abcb76d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q743 : PLift (G 46958 47058) := ⟨bs [0xb7911498b791,0x2de50b796b795,0x5bd44284b7a9,0x16f80fb1ab7c1,0x2df28b7ccb7cb,0xb7d0eed2b7d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q744 : PLift (G 47058 47124) := ⟨bs [0x2df48b7d4b7d3,0x16fdcb716b7ef,0x2dfd0b7f6b7f5,0x1700ca084b807,0x7ab4fe20b80f,0x2e048b814b813] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q745 : PLift (G 47124 47162) := ⟨bs [0x5c0cb472b819,0x170409e88b821,0x1704cc2eab827,0x2e0a8b82cb82b,0x2e0b0b82eb82d,0x5c1d12c2b839] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q746 : PLift (G 47162 47270) := ⟨bs [0x2e150b856b855,0x170cd3fb6b867,0x31303658b875,0x2e210b886b885,0xf61905dcb893,0xf6303706b8a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q747 : PLift (G 47270 47310) := ⟨bs [0x1715ce2ecb8af,0x1716c6c78b8b7,0xf6502ad8b8bd,0xb8c0e1dab8c1,0x1718d2bacb8c7,0x2e330b8ceb8cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q748 : PLift (G 47310 47382) := ⟨bs [0xf67161b2b8d5,0x2e3a8b8ecb8eb,0x171eccd62b8f7,0x171f0c6c2b8f9,0x2e408b904b903,0x2e450b916b915] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q749 : PLift (G 47382 47432) := ⟨bs [0x2e468b91cb91b,0x2e470b91eb91d,0x7b75265eb92f,0x172708838b939,0x2e4e8b93cb93b,0x1728d715ab947] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q750 : PLift (G 47432 47508) := ⟨bs [0x172a0ffb8b951,0x2e588b964b963,0x2e608b984b983,0x5cc54198b989,0x947126c2b98d,0x2e648b994b993] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q751 : PLift (G 47508 47564) := ⟨bs [0xb99879dcb999,0xdc11bd8b9a1,0x1734cdbbab9a7,0x2e6b0b9aeb9ad,0x1736cd136b9b7,0x2e728b9ccb9cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q752 : PLift (G 47564 47624) := ⟨bs [0x3df169dab9d1,0x2e770b9deb9dd,0x173cc8d52b9e7,0x173dc6e78b9ef,0xb9f8929ab9f9,0x1740c643cba07] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q753 : PLift (G 47624 47682) := ⟨bs [0xf8104b12ba0d,0x1742d68ceba17,0x16908262ba25,0x5d1540daba29,0x2e8a8ba2cba2b,0x17480c01aba41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q754 : PLift (G 47682 47738) := ⟨bs [0x2e948ba54ba53,0x2e950ba56ba55,0x174bcb466ba5f,0x174c3d28ba61,0x2e990ba66ba65,0xa5cd5d8ba79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q755 : PLift (G 47738 47792) := ⟨bs [0x95316e00ba7d,0x174fcebbeba7f,0x5d500da2baa1,0xf8d8126abaa3,0x297c9084baaf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q756 : PLift (G 47792 47844) := ⟨bs [0x2390bee6bab5,0x1757c1e26babf,0x175804cc4bac1,0x2eb28baccbacb,0x2eb70badebadd,0x2eb88bae4bae3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q757 : PLift (G 47844 47904) := ⟨bs [0x175e010cabaf1,0x2ebf0bafebafd,0x5d855e5ebb09,0x1763d6df4bb1f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q758 : PLift (G 47904 47952) := ⟨bs [0x4add09f4bb27,0xf990fa96bb2d,0x2ecf0bb3ebb3d,0x2ed08bb44bb43,0x2ed28bb4cbb4b,0x1769d2128bb4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q759 : PLift (G 47952 48024) := ⟨bs [0x2ed68bb5cbb5b,0x176c0536abb61,0x176d127bebb69,0x2edb0bb6ebb6d,0xbb907e08bb91,0x1772c9ba4bb97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q760 : PLift (G 48024 48110) := ⟨bs [0x2ee70bb9ebb9d,0x7d20418cbbb1,0x177916ccebbc9,0x1779cc8e2bbcf,0x321826acbbdb,0x2efb0bbeebbed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q761 : PLift (G 48110 48132) := ⟨bs [0x35b40072bbf7,0x7d50b7c2bbf9,0x96689316bc03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q762 : PLift (G 48132 48198) := ⟨bs [0xfad0f778bc1d,0xfad8d37ebc23,0x39e8c14abc33,0x2f0e8bc3cbc3b,0x178804942bc41,0x2f110bc46bc45] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q763 : PLift (G 48198 48272) := ⟨bs [0x2f170bc5ebc5d,0x178dd3ea4bc6f,0x178ec9c42bc77,0x2f208bc84bc83,0x4b6c3564bc8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q764 : PLift (G 48272 48338) := ⟨bs [0x5e4d274abc99,0x2f2a8bcacbcab,0x1796cee50bcb7,0x14f874bcbcb9,0xbcd04a2cbcd1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q765 : PLift (G 48338 48408) := ⟨bs [0x97105444bcd5,0x179c0889cbce1,0x2f3c8bcf4bcf3,0x179fc42a2bcff,0xfc114c72bd0d,0x17a2d193ebd17] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q766 : PLift (G 48408 48474) := ⟨bs [0x7e102cb8bd19,0x2f470bd1ebd1d,0x2f4d0bd36bd35,0x17a8100e8bd41,0x7e34949abd4f,0x17ab0d3c2bd59] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q767 : PLift (G 48474 48498) := ⟨bs [0x17abd183cbd5f,0x4bc0a196bd61,0x17acc3566bd67,0x2f5a8bd6cbd6b,0xbd71505ebd71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q768 : PLift (G 48498 48564) := ⟨bs [0xfcb93132bd8b,0x17b1caa60bd8f,0x2f650bd96bd95,0x2f668bd9cbd9b,0x2f670bd9ebd9d,0x2f6c8bdb4bdb3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q769 : PLift (G 48564 48620) := ⟨bs [0x2f6e8bdbcbdbb,0xfd1072febdcd,0x5ee97b6abdd1,0x2f788bde4bde3,0x2f7a8bdecbdeb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q770 : PLift (G 48620 48662) := ⟨bs [0x3644850cbdef,0x17c0c9844be07,0x5f044fcabe09,0x2f850be16be15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q771 : PLift (G 48662 48752) := ⟨bs [0x3f6057b0be21,0x2f890be26be25,0x17c4c93febe27,0xdd94a02be5b,0x2f970be5ebe5d,0x7ef44326be6f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q772 : PLift (G 48752 48788) := ⟨bs [0x2f9d0be76be75,0x17cf0fb1ebe79,0x17cfc63f4be7f,0x2fa28be8cbe8b,0x98714f80be8d,0x2fa48be94be93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q773 : PLift (G 48788 48848) := ⟨bs [0x17d3c843ebe9f,0x17d508f36bea9,0x388961cbeb1,0x2fad0beb6beb5,0x17d6d3d92beb7,0x7f35723ebecf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q774 : PLift (G 48848 48890) := ⟨bs [0x17db16b76bed9,0x2fb68bedcbedb,0x2fb90bee6bee5,0x17dcd65a8bee7,0x2fbc8bef4bef3,0xbef895ecbef9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q775 : PLift (G 48890 48990) := ⟨bs [0x2fc28bf0cbf0b,0x2fcc8bf34bf33,0x5f9c2c32bf39,0xff111182bf4d,0x2fd70bf5ebf5d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q776 : PLift (G 48990 49020) := ⟨bs [0x4c8cce34bf5f,0xff38ffaabf6b,0x5fb97caebf71,0x2fde8bf7cbf7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q777 : PLift (G 49020 49044) := ⟨bs [0x4c9c7a3abf87,0x17f105dfcbf89,0x2fe30bf8ebf8d,0x2fe48bf94bf93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q778 : PLift (G 49044 49118) := ⟨bs [0x3fe08154bfa1,0x2feb0bfaebfad,0x17f714a24bfb9,0x17f9c0e54bfcf,0x2ff50bfd6bfd5,0x2ff70bfdebfdd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q779 : PLift (G 49118 49172) := ⟨bs [0xbfe0af66bfe1,0x2ff88bfe4bfe3,0x2ffc8bff4bff3,0x30010c006c005,0x36e0d196c011,0x30048c014c013] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q780 : PLift (G 49172 49212) := ⟨bs [0x180313a74c019,0xc028e24cc029,0x1805c8e50c02f,0x99d6bcec031,0x1806c033ec037,0x300e8c03cc03b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q781 : PLift (G 49212 49298) := ⟨bs [0x1808d2190c047,0x30190c066c065,0x301b0c06ec06d,0x301f0c07ec07d,0x180fd2738c07f,0x3b54cf4c091] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q782 : PLift (G 49298 49368) := ⟨bs [0x30268c09cc09b,0x302c8c0b4c0b3,0x302d0c0b6c0b5,0x55a943ecc0bb,0x30348c0d4c0d3,0x181ace5d6c0d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q783 : PLift (G 49368 49412) := ⟨bs [0x606c0e4ac0d9,0x181dc67d2c0ef,0x6078b9fec0f1,0xc100c238c101,0x30408c104c103] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q784 : PLift (G 49412 49464) := ⟨bs [0x60847396c109,0x30450c116c115,0x18230d6eac119,0x1ee8a812c12b,0x1019971fac133,0x1826d4338c137] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q785 : PLift (G 49464 49532) := ⟨bs [0x1f0fe5cc145,0x60a55d68c149,0x30568c15cc15b,0x305c8c174c173,0x182f08758c179,0x101f96aa6c17b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q786 : PLift (G 49532 49604) := ⟨bs [0x183006bc2c181,0x30628c18cc18b,0x102115d4ec18d,0x1832c61f2c197,0x1025057fec1bd,0x24e8c322c1c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q787 : PLift (G 49604 49668) := ⟨bs [0x30730c1cec1cd,0x10278dc5ec1db,0x2050336ec1e1,0x183cd11acc1e7,0x8154d406c1ff,0x30808c204c203] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q788 : PLift (G 49668 49740) := ⟨bs [0x30810c206c205,0x8717876c211,0x184415382c221,0x81744750c22f,0x1847cc160c23f,0x30928c24cc24b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q789 : PLift (G 49740 49790) := ⟨bs [0x30930c24ec24d,0x103194efcc253,0x30970c25ec25d,0x184ecdfc0c277,0x309e8c27cc27b,0x103516496c27d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q790 : PLift (G 49790 49844) := ⟨bs [0x6144b568c289,0x1851cf782c28f,0x9ba9428cc293,0x1853cb332c29f,0x1854cd278c2a7,0x30ac8c2b4c2b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q791 : PLift (G 49844 49922) := ⟨bs [0x30af0c2bec2bd,0x1859d264ec2cf,0x30b50c2d6c2d5,0x30b88c2e4c2e3,0x185fc8196c2ff,0x1e00ececc301] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q792 : PLift (G 49922 49944) := ⟨bs [0x820480a0c307,0x186206d30c311,0x10418b74ac313,0x1862cfa08c317] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q793 : PLift (G 49944 50024) := ⟨bs [0x104306720c325,0x1868d4928c347,0x186917460c349,0xa049162c34f,0x30d90c366c365,0x6352f2ec367] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q794 : PLift (G 50024 50078) := ⟨bs [0x186e120dcc371,0x186fc9572c37f,0x30e08c384c383,0x30e10c386c385,0x30e50c396c395,0x30e70c39ec39d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q795 : PLift (G 50078 50124) := ⟨bs [0x1874c8fb8c3a7,0x30eb0c3aec3ad,0x30ed0c3b6c3b5,0x1877d10d2c3bf,0x8284bcc4c3c7,0x30f28c3ccc3cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q796 : PLift (G 50124 50178) := ⟨bs [0x187a06d74c3d1,0x30f48c3d4c3d3,0x30f88c3e4c3e3,0xc3e8ca12c3e9,0x187dc8188c3ef,0xc40b446c401] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q797 : PLift (G 50178 50262) := ⟨bs [0x1e2cd49cc41f,0x105909858c42d,0x310c8c434c433,0x1886c31a2c437,0x70313dc0c455] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q798 : PLift (G 50262 50292) := ⟨bs [0x82e4bf8ec457,0x188c0a1ccc461,0x82f50610c46f,0x311c8c474c473] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q799 : PLift (G 50292 50342) := ⟨bs [0x1890ce27cc487,0x624803aac491,0x624c5190c499,0x31270c49ec49d,0x31290c4a6c4a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q800 : PLift (G 50342 50378) := ⟨bs [0x83250c3cc4b7,0x312e8c4bcc4bb,0x62654706c4c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q801 : PLift (G 50378 50442) := ⟨bs [0x833436f4c4cf,0x31348c4d4c4d3,0x313a8c4ecc4eb,0xc4f15b04c4f1,0x189ec141ec4f7,0x13b55e4cc509] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q802 : PLift (G 50442 50528) := ⟨bs [0x31468c51cc51b,0x9db0ce40c51d,0xc54127dac541,0x18a8c8c1cc547,0x18aa070eec551,0x18abd6eacc55f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q803 : PLift (G 50528 50588) := ⟨bs [0x315a8c56cc56b,0x18adc1bb0c56f,0x315d0c576c575,0x83a42534c577,0x31650c596c595,0x1077861b6c59b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q804 : PLift (G 50588 50594) := ⟨bs [0x18b3c8e7ec59f,0x41e0aaecc5a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q805 : PLift (G 50594 50684) := ⟨bs [0x83c4ceeac5a7,0x31708c5c4c5c3,0x18bad5c9ec5d7,0x31768c5dcc5db,0x1a64dde8c5ef,0x317e8c5fcc5fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q806 : PLift (G 50684 50774) := ⟨bs [0x1081976bcc613,0x31888c624c623,0x318d0c636c635,0x18c8f3d2c641,0x18c9cc9f0c64f,0x1087126a0c655] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q807 : PLift (G 50774 50840) := ⟨bs [0x18cb00e92c659,0x31990c666c665,0x31a10c686c685,0x63498096c691,0x18d2c7d5cc697] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q808 : PLift (G 50840 50894) := ⟨bs [0x38c12edec6a1,0xc6a8e3d0c6a9,0x31ac8c6b4c6b3,0x18d704e1ac6b9,0x31b28c6ccc6cb,0x31b30c6cec6cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q809 : PLift (G 50894 50970) := ⟨bs [0x31b70c6dec6dd,0x31ba8c6ecc6eb,0x18de10668c6f1,0x18e0d6afcc707,0x31c30c70ec70d,0x18e30b634c719] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q810 : PLift (G 50970 51044) := ⟨bs [0x31c68c71cc71b,0x31cb0c72ec72d,0xc730ea2cc731,0xff0b1b6c739,0x84e41436c757,0x31d88c764c763] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q811 : PLift (G 51044 51110) := ⟨bs [0x18ecd26a0c767,0x31dc8c774c773,0x31dd0c776c775,0x4fcc8b10c77f,0x10a30bbbec7a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q812 : PLift (G 51110 51138) := ⟨bs [0x9fc93160c7bb,0x31ef0c7bec7bd,0x31f0b4a0c7c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q813 : PLift (G 51138 51198) := ⟨bs [0x4fec54a4c7cf,0x72309242c7d5,0x18fc06bf4c7e1,0x18ff13278c7f9,0x31ff0c7fec7fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q814 : PLift (G 51198 51242) := ⟨bs [0x1164018ec7ff,0x32008c804c803,0xc810c424c811,0x32070c81ec81d,0x1904d7794c827,0x28083dbac829] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q815 : PLift (G 51242 51330) := ⟨bs [0x641cea7ac839,0x1907c2dbcc83f,0x32148c854c853,0x190ad59f6c857,0x10b39412ec86b,0xc880e59cc881] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q816 : PLift (G 51330 51362) := ⟨bs [0x32230c88ec88d,0x1911d6266c88f,0x32248c894c893,0x18510010c895,0x322943e6c8a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q817 : PLift (G 51362 51428) := ⟨bs [0x1916d88aac8b7,0x1919c54dec8cf,0x32350c8d6c8d5,0x32368c8dcc8db,0x32370c8dec8dd,0x32388c8e4c8e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q818 : PLift (G 51428 51474) := ⟨bs [0x191cc8f60c8e7,0x323b0c8eec8ed,0x191dc4754c8ef,0x647c48a4c8f9,0x32410c906c905,0x192202da8c911] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q819 : PLift (G 51474 51518) := ⟨bs [0x1922d19b4c917,0x4118f0ac919,0x1923c375ec91f,0x1925cd0c2c92f,0x1926d4f10c937,0x10c518142c93d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q820 : PLift (G 51518 51582) := ⟨bs [0x64a0f3e6c941,0x32548c954c953,0x192bc92ecc95f,0x325a8c96cc96b,0x192f17cd2c979,0x325f0c97ec97d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q821 : PLift (G 51582 51614) := ⟨bs [0x64c4fce4c989,0x1931c65f4c98f,0x2cccb376c997,0x32670c99ec99d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q822 : PLift (G 51614 51638) := ⟨bs [0x50ac0464c9af,0x10cf0b952c9b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q823 : PLift (G 51638 51680) := ⟨bs [0x39a563acc9bf,0x32728c9ccc9cb,0x86905a44c9d9,0x193bd8cc0c9df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q824 : PLift (G 51680 51750) := ⟨bs [0x32788c9e4c9e3,0xa188e91cc9eb,0x19400dd72ca01,0x1940c0a96ca07,0x1941092d2ca09,0x32890ca26ca25] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q825 : PLift (G 51750 51818) := ⟨bs [0x1946d558cca37,0xca3856d6ca39,0x10db86006ca4b,0x233190aeca55,0x32968ca5cca5b,0x194d0a22eca69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q826 : PLift (G 51818 51870) := ⟨bs [0x329c8ca74ca73,0x329d0ca76ca75,0x194fc1162ca7f,0x10e101c64ca8d,0x10e1895e0ca93,0x32a70ca9eca9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q827 : PLift (G 51870 51930) := ⟨bs [0x871452a4ca9f,0x32ad0cab6cab5,0x32ae8cabccabb,0x10e58902ccac3,0xcac93984cac9,0x195b0f0f0cad9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q828 : PLift (G 51930 51978) := ⟨bs [0x10912c92cae5,0x32bb0caeecaed,0x32c08cb04cb03,0x32c10cb06cb05,0x6584e1eacb09] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q829 : PLift (G 51978 52052) := ⟨bs [0x513c3d74cb17,0xc5065f4cb29,0x32cd0cb36cb35,0x32ce8cb3ccb3b,0x32d48cb54cb53] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q830 : PLift (G 52052 52122) := ⟨bs [0xcb593d02cb59,0x32d88cb64cb63,0x32d90cb66cb65,0xcb710938cb71,0x1970d48d8cb87,0x19730a6f8cb99] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q831 : PLift (G 52122 52182) := ⟨bs [0x1973c155ecb9f,0x32ec8cbb4cbb3,0x87d16b94cbb9,0x32f08cbc4cbc3,0x197a01a42cbd1,0xa310df0ccbd5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q832 : PLift (G 52182 52224) := ⟨bs [0x87e4e8aacbd7,0x10fd0d66ccbdd,0xcbe8d9c2cbe9,0x197fc25a4cbff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q833 : PLift (G 52224 52268) := ⟨bs [0x110112940cc0d,0x660cebe8cc19,0x33070cc1ecc1d,0x33088cc24cc23,0x330a8cc2ccc2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q834 : PLift (G 52268 52314) := ⟨bs [0x6620f48ecc41,0x26e937fecc43,0x33130cc4ecc4d,0x198b04cbecc59] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q835 : PLift (G 52314 52362) := ⟨bs [0x44200460cc61,0x199115dc4cc89] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q836 : PLift (G 52362 52434) := ⟨bs [0x110b8ef64cc8b,0x1992021f2cc91,0x33268cc9ccc9b,0x33288cca4cca3,0x1994c291ccca7,0x199a133acccd1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q837 : PLift (G 52434 52518) := ⟨bs [0x33390cce6cce5,0x199d191b8cce9,0xcd0993b0cd09,0x36b07fd6cd15,0x19a3c1010cd1f,0x33490cd26cd25] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q838 : PLift (G 52518 52568) := ⟨bs [0x19a603260cd31,0x334f0cd3ecd3d,0x19a7c941acd3f,0xcd4932a8cd49,0x1b601192cd51,0x19aad3cc6cd57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q839 : PLift (G 52568 52628) := ⟨bs [0x33568cd5ccd5b,0x33588cd64cd63,0x19acd9774cd67,0x8901537ecd81,0x11218d102cd93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q840 : PLift (G 52628 52674) := ⟨bs [0x523c7d8acd97,0x19b3d0e9acd9f,0x336e8cdbccdbb,0x66e0e872cdc1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q841 : PLift (G 52674 52728) := ⟨bs [0x33748cdd4cdd3,0xcdd87984cdd9,0x33790cde6cde5,0x1b757024cde7,0xcdf10c76cdf1,0x19bed8e72cdf7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q842 : PLift (G 52728 52784) := ⟨bs [0x337f0cdfecdfd,0x112b9539cce0b,0x33850ce16ce15,0xce20678ece21,0x8974d948ce2f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q843 : PLift (G 52784 52860) := ⟨bs [0x89850ae2ce47,0x33930ce4ece4d,0x19ca0b7c4ce51,0x33990ce66ce65,0x3f886ba0ce7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q844 : PLift (G 52860 52904) := ⟨bs [0x11350fceace7d,0x19d1c2c92ce8f,0x33a48ce94ce93,0x19d3186b8ce99,0xa5501d10cea5,0x19d4d10a2cea7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q845 : PLift (G 52904 52968) := ⟨bs [0x19d6c7d2eceb7,0xcec8eefacec9,0x19dace448ced7,0x113d0b536cedd,0x113d94b16cee3,0x19dccfc78cee7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q846 : PLift (G 52968 53048) := ⟨bs [0x33bb0ceeeceed,0x33bd0cef6cef5,0x19e0cfc2ecf07,0x33c28cf0ccf0b,0x678c67f2cf19,0x19e6d017acf37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q847 : PLift (G 53048 53094) := ⟨bs [0xa5c85312cf3b,0x33d30cf4ecf4d,0x33d50cf56cf55,0x19ebd550acf5f,0x19ec12870cf61,0x33d90cf66cf65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q848 : PLift (G 53094 53150) := ⟨bs [0x33db0cf6ecf6d,0x2294362ecf79,0x33df0cf7ecf7d,0x67c5876acf89,0x33e68cf9ccf9b,0x114d02928cf9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q849 : PLift (G 53150 53198) := ⟨bs [0x19f50bafccfa9,0x33ec8cfb4cfb3,0x76b022b4cfb5,0x33f10cfc6cfc5,0x33f30cfcecfcd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q850 : PLift (G 53198 53232) := ⟨bs [0x33f4cf04cfd1,0x19fdc87a6cfef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q851 : PLift (G 53232 53268) := ⟨bs [0x8aa10fcccff1,0x8aa59678cff7,0x34048d014d013] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q852 : PLift (G 53268 53324) := ⟨bs [0x115719e62d015,0x1a03d0312d01f,0x1a041432cd021,0x340c8d034d033,0x340f0d03ed03d,0x34128d04cd04b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q853 : PLift (G 53324 53402) := ⟨bs [0x1a09d03cad04f,0x1a0d068a8d069,0x1a0dccf88d06f,0x1a101435ed081,0x34210d086d085,0x8b10b9a0d099] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q854 : PLift (G 53402 53454) := ⟨bs [0x1a13c6d3cd09f,0x34288d0a4d0a3,0x342a8d0acd0ab,0x342f0d0bed0bd,0x1a18040b4d0c1,0x34330d0ced0cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q855 : PLift (G 53454 53552) := ⟨bs [0x1a1cd8084d0e7,0x8b550df0d0ff,0x34408d104d103,0x1a22cf5cad117,0x344b0d12ed12d,0x1a25cbddcd12f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q856 : PLift (G 53552 53612) := ⟨bs [0x8b811c52d141,0x1a2ad8d3ed157,0x1a2b040d2d159,0x34570d15ed15d,0x1a2d12f54d169,0x11739587cd16b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q857 : PLift (G 53612 53654) := ⟨bs [0x11743124d171,0x1a2ec8100d177,0x117518492d17d,0x1a30e1c0d181,0x203cc2aad187,0x34650d196d195] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q858 : PLift (G 53654 53720) := ⟨bs [0xd1996b82d199,0x53e02792d1b1,0x346f0d1bed1bd,0x34708d1c4d1c3,0x34750d1d6d1d5,0x1a3ac4dead1d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q859 : PLift (G 53720 53792) := ⟨bs [0xa7e84f68d1e3,0x1a3fcb33ed1ff,0x34830d20ed20d,0x690840fad211,0x1a42c8ba2d217,0x1a43da2f6d21f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q860 : PLift (G 53792 53850) := ⟨bs [0x348d0d236d235,0x348e8d23cd23b,0x541ca74ad247,0x692c9128d259] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q861 : PLift (G 53850 53898) := ⟨bs [0x1a4c0cc2ad261,0x34990d266d265,0x693c407ed279,0x1a4fd8ce6d27f,0x34a08d284d283,0xd288f454d289] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q862 : PLift (G 53898 53952) := ⟨bs [0x34a28d28cd28b,0x34a70d29ed29d,0x4c9939e6d2a3,0x1a54d021cd2a7,0x34ac8d2b4d2b3,0x1a57d9536d2bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q863 : PLift (G 53952 54014) := ⟨bs [0x1a58c0d06d2c7,0x34b88d2e4d2e3,0x6357cb4d2e9,0x2d16f3cd2f1,0x34be8d2fcd2fb,0x11950fbd2d2fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q864 : PLift (G 54014 54102) := ⟨bs [0x34c50d316d315,0xd3212ebad321,0x34ca8d32cd32b,0x34d08d344d343,0xa908c976d34b,0xa9119792d355] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q865 : PLift (G 54102 54164) := ⟨bs [0x8cf12974d369,0x119f09f62d375,0x34de8d37cd37b,0x1a70c5f92d387,0x34e48d394d393] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q866 : PLift (G 54164 54270) := ⟨bs [0x3c745eccd397,0x34e90d3a6d3a5,0x1a760a0b6d3b1,0x3ecda9ad3c9,0x34fa8d3ecd3eb,0x34ff0d3fed3fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q867 : PLift (G 54270 54320) := ⟨bs [0x11ab10ee4d405,0x1a81cd326d40f,0x35050d416d415,0x54dd8a0ed427,0x1a85c9706d42f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q868 : PLift (G 54320 54368) := ⟨bs [0x350c8d434d433,0x350e8d43cd43b,0x35128d44cd44b,0x179993acd459,0x8d947e46d45f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q869 : PLift (G 54368 54414) := ⟨bs [0xa9e8d126d463,0x1a8d02a00d469,0x6a405258d481,0x35208d484d483,0xd48871cad489,0x35230d48ed48d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q870 : PLift (G 54414 54470) := ⟨bs [0x35248d494d493,0x35250d496d495,0x35290d4a6d4a5,0x352a8d4acd4ab,0xd4b12a9cd4b1,0x35310d4c6d4c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q871 : PLift (G 54470 54522) := ⟨bs [0x35370d4ded4dd,0xd4e15fead4e1,0x11bd80ed4d4e3,0x1a9cc7b36d4e7,0x11bf029bed4f5,0x1a9f16728d4f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q872 : PLift (G 54522 54578) := ⟨bs [0x35428d50cd50b,0x35430d50ed50d,0x11c18e076d513,0x1aa3cab2ed51f,0x35488d524d523,0xd53067fed531] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q873 : PLift (G 54578 54624) := ⟨bs [0xaa906522d535,0x26c5896ed537,0x1aa914794d549,0x1aab0f216d559,0x1aabc8a92d55f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q874 : PLift (G 54624 54674) := ⟨bs [0x79f15a9ad565,0x1aaccf0a0d567,0x1aaed20dcd577,0x35628d58cd58b,0x8e600912d591] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q875 : PLift (G 54674 54728) := ⟨bs [0x8e644f46d597,0x356d0d5b6d5b5,0xd5b8d672d5b9,0x5f10b98d5c1,0x1ab8c233ad5c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q876 : PLift (G 54728 54800) := ⟨bs [0x1abbd7ea6d5df,0x1abdd77a8d5ef,0x357d0d5f6d5f5,0x357e8d5fcd5fb,0x35808d604d603,0x1ac1c13fed60f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q877 : PLift (G 54800 54882) := ⟨bs [0x358b0d62ed62d,0xd630092ed631,0xab68abd0d643,0x35950d656d655,0x35970d65ed65d,0xd6609236d661] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q878 : PLift (G 54882 54960) := ⟨bs [0x359e8d67cd67b,0x35a10d686d685,0xfe49648d687,0x35a70d69ed69d,0x35a90d6a6d6a5,0x1ad5cde82d6af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q879 : PLift (G 54960 55010) := ⟨bs [0x11e519a86d6bd,0x11e58ff48d6c3,0x1ad8c3a7ed6c7,0x2af81d28d6d9,0x1adc187b2d6e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q880 : PLift (G 55010 55058) := ⟨bs [0x39504fd8d6ed,0x6b84d6b4d709,0x35c28d70cd70b,0x1ae203ae0d711] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q881 : PLift (G 55058 55118) := ⟨bs [0x35c50d716d715,0x1ae414972d721,0x1ae4c8b98d727,0x1ae7d1e90d73f,0x35d10d746d745,0x5fb00244d74d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q882 : PLift (G 55118 55172) := ⟨bs [0x1aead14bcd757,0x11f393f3ad76b,0x35de8d77cd77b,0x3978e590d783] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q883 : PLift (G 55172 55220) := ⟨bs [0x12c00df6d7a1,0x1af4c4794d7a7,0x35eb0d7aed7ad,0x35ed3356d7b1,0x35ec8d7b4d7b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q884 : PLift (G 55220 55314) := ⟨bs [0x35ef0d7bed7bd,0x35f28d7ccd7cb,0x1afa0257ad7d1,0x7b583af6d7db,0x11ff871a8d7fb,0x6c08da3cd811] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q885 : PLift (G 55314 55340) := ⟨bs [0x36088d824d823,0x12030c946d825,0x6c144810d829,0x360a8d82cd82b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q886 : PLift (G 55340 55374) := ⟨bs [0x3dc49342d82f,0x9024c33ed837,0x36130d84ed84d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q887 : PLift (G 55374 55440) := ⟨bs [0xad11494ed855,0x9044dc92d867,0x361c8d874d873,0x1b11cbaa8d88f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q888 : PLift (G 55440 55512) := ⟨bs [0x604c638d891,0x1b140b528d8a1,0x362b0d8aed8ad,0x1b17d5da2d8bf,0x1211095cad8cd,0x1b1ad749ed8d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q889 : PLift (G 55512 55604) := ⟨bs [0xd8e85120d8e9,0x363d0d8f6d8f5,0x363e8d8fcd8fb,0x36468d91cd91b,0x36490d926d925,0x364c8d934d933] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q890 : PLift (G 55604 55640) := ⟨bs [0xf845ffed939,0x36508d944d943,0x36510d946d945,0x1b29c37e8d94f,0x2dd5bb6d951,0x304c5168d957] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q891 : PLift (G 55640 55692) := ⟨bs [0x365b0d96ed96d,0x1b2dc3868d96f,0x365c8d974d973,0x6cbc54bed979,0xd980fe68d981,0x36628d98cd98b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q892 : PLift (G 55692 55764) := ⟨bs [0x1b3203034d991,0x1b33d76a8d99f,0x36690d9a6d9a5,0x1b3508cb2d9a9,0x366d0d9b6d9b5,0x36748d9d4d9d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q893 : PLift (G 55764 55818) := ⟨bs [0x367a8d9ecd9eb,0x1b3e00e3cd9f1,0x1b3ed7cd4d9f7,0x1b3fd62ccd9ff,0x36810da06da05,0x1b4109282da09] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q894 : PLift (G 55818 55850) := ⟨bs [0x36828da0cda0b,0x1b41d1710da0f,0x36850da16da15,0x122d15cdcda1d,0x36888da24da23,0x6d156fb6da29] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q895 : PLift (G 55850 55904) := ⟨bs [0x25d8cacda3f,0xda504b74da51,0x1b4b02578da59,0x36970da5eda5d,0x1b4bd1c84da5f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q896 : PLift (G 55904 55950) := ⟨bs [0x57602ceeda71,0x1b4ed021ada77,0xaec9533eda7b,0x369f0da7eda7d,0x36a30da8eda8d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q897 : PLift (G 55950 56040) := ⟨bs [0x1b53d7498da9f,0x36ac8dab4dab3,0x36af0dabedabd,0x36b08dac4dac3,0x1b5916b2adac9,0x1b5cce9badae7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q898 : PLift (G 56040 56100) := ⟨bs [0x1b5d088b4dae9,0x36bd0daf6daf5,0x1b621ad2adb11,0x1b62c451edb17,0x36c70db1edb1d,0x36c88db24db23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q899 : PLift (G 56100 56150) := ⟨bs [0x231195d8db25,0xdb302356db31,0x36ce8db3cdb3b,0x36d08db44db43,0x124706360db55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q900 : PLift (G 56150 56180) := ⟨bs [0x924586aedb67,0x36da8db6cdb6b,0x61894e8adb73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q901 : PLift (G 56180 56240) := ⟨bs [0x124b1737adb85,0x1b71c7000db8f,0x9261a594db91,0x36eb0dbaedbad,0x1b75d2f54dbaf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q902 : PLift (G 56240 56312) := ⟨bs [0xdbb99582dbb9,0x1b78ca86adbc7,0x36f28dbccdbcb,0x36f30dbcedbcd,0x12539afdedbeb,0x1b7ec29a4dbf7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q903 : PLift (G 56312 56394) := ⟨bs [0x37030dc0edc0d,0x1b84c10a4dc27,0x1b860c8f0dc31,0x1b870a436dc39,0x1b87cb2acdc3f,0x1b8902096dc49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q904 : PLift (G 56394 56438) := ⟨bs [0x1b8a0201cdc51,0x1b8ca8a6dc61,0x582d0e52dc6f,0x371d0dc76dc75] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q905 : PLift (G 56438 56480) := ⟨bs [0x125f83c8adc7b,0x37210dc86dc85,0x37248dc94dc93,0x1b93086c2dc99,0x37270dc9edc9d,0x1b93cef36dc9f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q906 : PLift (G 56480 56528) := ⟨bs [0xdca956dcdca9,0xb0918646dcb5,0x1b96da616dcb7,0x372f0dcbedcbd,0x1b98d49f0dcc7,0x1b99c5ccadccf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q907 : PLift (G 56528 56598) := ⟨bs [0x37348dcd4dcd3,0x7e31727edcd5,0x1b9bc0cf0dcdf,0x1b9f11fdcdcf9,0x1ba1cca44dd0f,0x37450dd16dd15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q908 : PLift (G 56598 56660) := ⟨bs [0x1ba2c6b5cdd17,0x62491c06dd23,0x374d0dd36dd35,0x6e9d00a4dd39,0x37548dd54dd53] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q909 : PLift (G 56660 56682) := ⟨bs [0x1baac056cdd57,0x9394f068dd5f,0x58911bdedd69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q910 : PLift (G 56682 56738) := ⟨bs [0x1badc086cdd6f,0x375f0dd7edd7d,0x1bb0c8638dd87,0x6ec4bee6dd89,0x37668dd9cdd9b,0x1bb4bad2dda1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q911 : PLift (G 56738 56808) := ⟨bs [0x376a8ddacddab,0x1bb7c0906ddbf,0x37710ddc6ddc5,0x37728ddccddcb,0x1bb9d663cddcf,0x1bbccd030dde7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q912 : PLift (G 56808 56858) := ⟨bs [0x1bbd088d4dde9,0x7ed17142dded,0x127f043e8ddf5,0x377e8ddfcddfb,0x37828de0cde0b,0x6f0d68c0de19] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q913 : PLift (G 56858 56912) := ⟨bs [0x1bc513688de29,0x378e8de3cde3b,0x378f0de3ede3d,0x6f214f40de41,0x37930de4ede4d,0x1bc9c9650de4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q914 : PLift (G 56912 56958) := ⟨bs [0x1bcb1a65ede59,0x1287926c8de5b,0x6f308bfcde61,0x379b0de6ede6d,0x1bced1f2ade77,0x379f0de7ede7d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q915 : PLift (G 56958 57038) := ⟨bs [0x37a08de84de83,0x1bd2d9534de97,0x128d1895ede9d,0x1bd41a150dea1,0x1bd4c354cdea7,0x12910be40decd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q916 : PLift (G 57038 57090) := ⟨bs [0xded09494ded1,0x1bdac1a6cded7,0x37b88dee4dee3,0xdef0f9c6def1,0x37bd0def6def5,0x1be018606df01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q917 : PLift (G 57090 57144) := ⟨bs [0x1be10b22adf09,0x37c48df14df13,0x1be3cde30df1f,0x37ca8df2cdf2b,0x37cc8df34df33,0x1be6d3392df37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q918 : PLift (G 57144 57192) := ⟨bs [0x37cf0df3edf3d,0x37d28df4cdf4b,0x37d50df56df55,0x37d68df5cdf5b,0x1becd7e12df67] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q919 : PLift (G 57192 57224) := ⟨bs [0x4a78f37adf69,0x37dc8df74df73,0x37e10df86df85,0x1bf0c1c40df87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q920 : PLift (G 57224 57284) := ⟨bs [0x1bf30e212df99,0x37e88dfa4dfa3,0x37ea8dfacdfab,0x37ed0dfb6dfb5,0x1dd59b20dfb7,0x37f08dfc4dfc3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q921 : PLift (G 57284 57350) := ⟨bs [0x1bf8d1030dfc7,0x3bb02f78dfd5,0xdff0277edff1,0x37fc8dff4dff3,0x38008e004e003,0x38010e006e005] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q922 : PLift (G 57350 57414) := ⟨bs [0x1c02ca24ee017,0x38070e01ee01d,0x1c04c5060e027,0x380b0e02ee02d,0x380d0e036e035,0x38110e046e045] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q923 : PLift (G 57414 57504) := ⟨bs [0x38148e054e053,0x804c7dce071,0x381e8e07ce07b,0x95b49314e08f,0x12b70e9f0e095,0x1c13d2fd8e09f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q924 : PLift (G 57504 57528) := ⟨bs [0x4035230ce0b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q925 : PLift (G 57528 57594) := ⟨bs [0xe0b8e54ae0b9,0x38350e0d6e0d5,0x1c1acd3d2e0d7,0xb3e92810e0e3,0x383c8e0f4e0f3,0xe0f98b80e0f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q926 : PLift (G 57594 57668) := ⟨bs [0x2580dacae101,0x38490e126e125,0xe1290b74e129,0x12c458cce131,0x384d0e136e135,0x12c599420e143] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q927 : PLift (G 57668 57710) := ⟨bs [0x96351e26e14f,0x70ad8c3ae159,0xe160d45ae161,0x385b0e16ee16d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q928 : PLift (G 57710 57752) := ⟨bs [0x1c2e02120e171,0x1c2ecc844e177,0x1c2fd6fb6e17f,0x38608e184e183,0x1c3106cc2e189,0x1c32d4276e197] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q929 : PLift (G 57752 57792) := ⟨bs [0x521158a4e1ad,0x14103946e1b5,0x386e8e1bce1bb,0x1c37c960ee1bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q930 : PLift (G 57792 57810) := ⟨bs [0x4b416beae1c1,0x38728e1cce1cb,0x1c3a081d2e1d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q931 : PLift (G 57810 57882) := ⟨bs [0x12d315e98e1e5,0x1c3dc14a0e1ef,0x1c3ec2ff6e1f7,0x12d513b90e1fd,0x38808e204e203,0x169d21a8e219] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q932 : PLift (G 57882 57948) := ⟨bs [0x388a8e22ce22b,0x388b0e22ee22d,0x388f0e23ee23d,0x38908e244e243,0x1c4ad770ae257,0x8158b2a8e25b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q933 : PLift (G 57948 58028) := ⟨bs [0x12df02014e275,0x1c4f0cd36e279,0x5a9c75a8e287,0x38a70e29ee29d,0x38aa8e2ace2ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q934 : PLift (G 58028 58068) := ⟨bs [0x1c55c2d26e2af,0x38ae8e2bce2bb,0xe2c07e94e2c1,0xe2c99d70e2c9,0xb57197b0e2cd,0x38b48e2d4e2d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q935 : PLift (G 58068 58112) := ⟨bs [0x716d81dee2d9,0x12e99041ce2f3,0x38bf0e2fee2fd,0x1c5fc5a18e2ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q936 : PLift (G 58112 58154) := ⟨bs [0x71881fe4e311,0x1b892970e323,0x1c64c5cb0e327,0x7195b0f6e329] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q937 : PLift (G 58154 58208) := ⟨bs [0x1c67196f2e339,0x38ce8e33ce33b,0x12f109212e34d,0x1c6a0f09ce351,0x1c6ad087ae357,0x1c6bc92bce35f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q938 : PLift (G 58208 58244) := ⟨bs [0x38d88e364e363,0x1c6d01bace369,0x38dd0e376e375,0x1c6ed6600e377,0x12f511c16e37d,0x38e08e384e383] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q939 : PLift (G 58244 58322) := ⟨bs [0x1c73c126ee39f,0x7103b92e3c5,0x71e4893ee3c9,0x1c7a0c008e3d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q940 : PLift (G 58322 58392) := ⟨bs [0x71f03bf2e3e1,0x38fe8e3fce3fb,0x1c7fd48a8e3ff,0xe4004edce401,0x39028e40ce40b,0x1c82c856ee417] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q941 : PLift (G 58392 58440) := ⟨bs [0xe418b988e419,0x39088e424e423,0x390a8e42ce42b,0x982036d2e431,0x390e8e43ce43b,0x1c88d84dee447] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q942 : PLift (G 58440 58442) := ⟨bs [0x4c182492e449] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q943 : PLift (G 58442 58512) := ⟨bs [0xb6a8255ae453,0x39150e456e455,0x1309127b0e46d,0x1c8e00156e471,0x1c91c0fa4e48f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q944 : PLift (G 58512 58580) := ⟨bs [0x7254a434e4a9,0x1c95c4920e4af,0x392d0e4b6e4b5,0x1c98d5b5ee4c7,0x39330e4cee4cd,0x39348e4d4e4d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q945 : PLift (G 58580 58662) := ⟨bs [0x1c9d126f6e4e9,0x393a8e4ece4eb,0x393d0e4f6e4f5,0x5b9db634e507,0xe521860ae521,0x39490e526e525] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q946 : PLift (G 58662 58728) := ⟨bs [0x1ca6cc840e537,0x1ca7c26a0e53f,0x39510e546e545,0x39528e54ce54b,0x1caad95d4e557,0x1cacd1c16e567] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q947 : PLift (G 58728 58788) := ⟨bs [0x395b0e56ee56d,0x395d0e576e575,0x39610e586e585,0x39628e58ce58b,0x66081ffae593,0x39688e5a4e5a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q948 : PLift (G 58788 58908) := ⟨bs [0x39690e5a6e5a5,0x99351c02e5cf,0xe6099042e609,0xe6119088e611,0x39850e616e615,0x39868e61ce61b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q949 : PLift (G 58908 58910) := ⟨bs [0x39870e61ee61d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q950 : PLift (G 58910 58914) := ⟨bs [0x41c09bb8e621] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q951 : PLift (G 58914 58980) := ⟨bs [0x170409dce629,0x1cc71a6bae639,0x1cc7c1ecae63f,0x133199b86e653,0x1ccadae98e657,0x39988e664e663] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q952 : PLift (G 58980 59022) := ⟨bs [0x1ccdd11cce66f,0x83b00f58e675,0x1cd017ea8e681,0x39a08e684e683,0x39a30e68ee68d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q953 : PLift (G 59022 59070) := ⟨bs [0x99b4dd2ee68f,0x39a50e696e695,0x24e99ef8e6ab,0x133906174e6ad,0x1cd6d5b54e6b7,0x39af0e6bee6bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q954 : PLift (G 59070 59120) := ⟨bs [0x133b1579ee6c5,0x39b28e6cce6cb,0x36514cd0e6d5,0x39b88e6e4e6e3,0x267c7e04e6e9,0x1cddd8c14e6ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q955 : PLift (G 59120 59184) := ⟨bs [0x39bc8e6f4e6f3,0xb8d0125ae705,0x39c30e70ee70d,0x1ce2d33ace717,0x1ce3dcce6e71f,0x1ce5d8fece72f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q956 : PLift (G 59184 59234) := ⟨bs [0x39cf0e73ee73d,0x1ce8d039ee747,0x1ce908318e749,0x39d48e754e753,0x39d50e756e755,0x9a4d688e761] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q957 : PLift (G 59234 59274) := ⟨bs [0x9a45b0b4e767,0x39da8e76ce76b,0x1cefc44cce77f,0x73c520f6e789] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q958 : PLift (G 59274 59352) := ⟨bs [0x39e5c162e791,0x39f10e7c6e7c5,0x13511651ce7cd,0x1cfac5ae4e7d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q959 : PLift (G 59352 59394) := ⟨bs [0x39f70e7dee7dd,0x1cfbc489ee7df,0x1cfd06d58e7e9,0x1cfe04060e7f1,0x39fe8e7fce7fb,0x3a0c916e801] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q960 : PLift (G 59394 59444) := ⟨bs [0x1d00d3cc2e807,0x1d01ca1fce80f,0x1d031a3ece819,0x3a068e81ce81b,0x1d0614360e831,0x3a0c8e834e833] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q961 : PLift (G 59444 59498) := ⟨bs [0x1d06d8c30e837,0x3a0f0e83ee83d,0x3a128e84ce84b,0x1d09cb88ee84f,0xe851c88ce851,0x9af0899ee869] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q962 : PLift (G 59498 59562) := ⟨bs [0x135f0a896e875,0x1d0f02ba6e879,0x3a248e894e893,0x3a290e8a6e8a5,0x5d1174d4e8a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q963 : PLift (G 59562 59618) := ⟨bs [0x1d15c560ce8af,0x13651b652e8bd,0x3a368e8dce8db,0x1d1c08ad0e8e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q964 : PLift (G 59618 59660) := ⟨bs [0x54b1ca1ae8e5,0x3a3a8e8ece8eb,0x3a3b0e8eee8ed,0x3a408e904e903,0x136b909e2e90b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q965 : PLift (G 59660 59708) := ⟨bs [0x1d21c899ae90f,0x3a450e916e915,0x1d22dce9ce917,0x3a4b0e92ee92d,0x3a4c8e934e933,0x67a995b6e93b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q966 : PLift (G 59708 59772) := ⟨bs [0x3a528e94ce94b,0x1d2a1c6a2e951,0x9b9404c0e95f,0x3a588e964e963,0xa9cf678e969,0x3a5e8e97ce97b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q967 : PLift (G 59772 59864) := ⟨bs [0x137589264e983,0x1d31d10e8e98f,0x3a650e996e995,0x1379bcd8e9a1,0x1d371763ae9b9,0x1d3ad51e0e9d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q968 : PLift (G 59864 59888) := ⟨bs [0x1d3cd663ee9e7,0x33fcc54ee9ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q969 : PLift (G 59888 59922) := ⟨bs [0x42e0b758ea11] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q970 : PLift (G 59922 60000) := ⟨bs [0x1d43119a2ea19,0x1d45d12f4ea2f,0x3a8d0ea36ea35,0x13859127aea43,0x3a930ea4eea4d,0x1d4bdc7faea5f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q971 : PLift (G 60000 60078) := ⟨bs [0x138913168ea6d,0x1d4e16024ea71,0x3a9f0ea7eea7d,0x3aa10ea86ea85,0x5dd06d5aea89,0x3aab0eaaeeaad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q972 : PLift (G 60078 60108) := ⟨bs [0x3aac8eab4eab3,0x755c3902eab9,0x3aae8eabceabb,0xbbd0e890eac5,0x1d58d26ceeac7,0x3ab28eacceacb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q973 : PLift (G 60108 60134) := ⟨bs [0x9c9479cceadf,0x1393128e0eae5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q974 : PLift (G 60134 60210) := ⟨bs [0x68681f1aeaeb,0x3abd0eaf6eaf5,0x1d6018ed6eb01,0x1d60c3b64eb07,0x1d6104d80eb09,0x1d660c7f6eb31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q975 : PLift (G 60210 60260) := ⟨bs [0x12181330eb39,0x1d67c17fceb3f,0xbc494156eb5b,0xeb610f0eeb61,0x139d853e0eb63] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q976 : PLift (G 60260 60332) := ⟨bs [0x9cf4a894eb6f,0x1d7016cb2eb81,0x3ae10eb86eb85,0x3ae70eb9eeb9d,0xbc885c12ebab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q977 : PLift (G 60332 60344) := ⟨bs [0x3aec6988ebb1,0x9d259ef0ebb7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q978 : PLift (G 60344 60428) := ⟨bs [0xebc05a3cebc1,0x3af50ebd6ebd5,0x1d7bd46b2ebdf,0x13a91d282ebed,0x3aff0ebfeebfd,0xba8d186ec0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q979 : PLift (G 60428 60510) := ⟨bs [0x3b068ec1cec1b,0xec21b94eec21,0x9d719668ec29,0x3b130ec4eec4d,0x1d8a06754ec51,0x3b170ec5eec5d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q980 : PLift (G 60510 60608) := ⟨bs [0x17a59690ec69,0x1d8dd1bfeec6f,0x3b1e8ec7cec7b,0x3b2b0ecaeecad,0x765d0f1eecb9,0x1d97c2348ecbf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q981 : PLift (G 60608 60624) := ⟨bs [0x561955ccecc3,0x1d9911f98ecc9,0x1d99cd6b0eccf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q982 : PLift (G 60624 60662) := ⟨bs [0x9de5a020ecd7,0x3b370ecdeecdd,0x1d9ccca42ece7,0x7675d1caece9,0x3b3c8ecf4ecf3,0x3b3d0ecf6ecf5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q983 : PLift (G 60662 60690) := ⟨bs [0x9e042edced07,0x3b455c6ced11] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q984 : PLift (G 60690 60758) := ⟨bs [0x9e158686ed1f,0x1da5d3d72ed2f,0x1da6cf3f4ed37,0x3b4f0ed3eed3d,0x1da81264ced41,0x3b550ed56ed55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q985 : PLift (G 60758 60812) := ⟨bs [0x1dab01b8aed59,0x13c787048ed5b,0x3b590ed66ed65,0x3b5a8ed6ced6b,0x1daf0b4aaed79,0x3b628ed8ced8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q986 : PLift (G 60812 60888) := ⟨bs [0x3b650ed96ed95,0x13cf9775aedbb,0x3b710edc6edc5,0x1dbadc3a4edd7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q987 : PLift (G 60888 60902) := ⟨bs [0x4f482f24edd9,0x3b788ede4ede3,0x3b790ede6ede5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q988 : PLift (G 60902 60938) := ⟨bs [0x9ea0b44aedf1,0x3b7d0edf6edf5,0x2b45b000edf7,0x3b7e8edfcedfb,0x1dc10c686ee09] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q989 : PLift (G 60938 60944) := ⟨bs [0x4405aae4ee0f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q990 : PLift (G 60944 61028) := ⟨bs [0xee18470cee19,0x1dc41501aee21,0x5f503c0cee49,0x1dc9ced58ee4f,0x3b988ee64ee63] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q991 : PLift (G 61028 61100) := ⟨bs [0x1dccd566aee67,0x3b9c8ee74ee73,0xbec8b956ee7b,0x1dd001152ee81,0x3ba88eea4eea3,0x3baa8eeaceeab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q992 : PLift (G 61100 61130) := ⟨bs [0x5f802646eec1,0x776599e0eec9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q993 : PLift (G 61130 61212) := ⟨bs [0x3fb03ae8eed5,0x1ddbcce6aeedf,0x1ddc0d3b6eee1,0x1dde1a8a2eef1,0x3bc68ef1cef1b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q994 : PLift (G 61212 61224) := ⟨bs [0x44553adcef27] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q995 : PLift (G 61224 61292) := ⟨bs [0x1fe4f992ef2f,0x3bd10ef46ef45,0x3bd30ef4eef4d,0x3bd88ef64ef63,0x6a698418ef6b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q996 : PLift (G 61292 61344) := ⟨bs [0x4fd0e9deef71,0x3be48ef94ef93,0x3be50ef96ef95,0x3be68ef9cef9b,0x1df3d6a20ef9f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q997 : PLift (G 61344 61380) := ⟨bs [0x13f91630cefad,0x88f80bfaefb3,0x3bf08efc4efc3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q998 : PLift (G 61380 61418) := ⟨bs [0xbfd10556efc5,0x3bf68efdcefdb,0x1dfc023acefe1,0x1dfd0f68cefe9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q999 : PLift (G 61418 61472) := ⟨bs [0x5000ab2ef001,0x1e02c28caf017,0x3c070f01ef01d,0x1e03cf942f01f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1000 : PLift (G 61472 61520) := ⟨bs [0x3c0a8f02cf02b,0x1e05cc9eaf02f,0x3c0d0f036f035,0x3c108f044f043,0x1e08d8516f047,0x1e09cc928f04f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1001 : PLift (G 61520 61584) := ⟨bs [0x1e0cc9754f067,0x3c1a8f06cf06b,0xf07076daf071,0x1e0ed8796f077,0xa05020f6f079,0x1e11d9300f08f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1002 : PLift (G 61584 61638) := ⟨bs [0x3c288f0a4f0a3,0x7854ca56f0a9,0x3c2b0f0aef0ad,0x140f8f600f0bb,0x1e17d94aef0bf,0x3c310f0c6f0c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1003 : PLift (G 61638 61682) := ⟨bs [0x3c328f0ccf0cb,0x3c348f0d4f0d3,0xf0d96e64f0d9,0x3c388f0e4f0e3,0x78753594f0e9,0xa0ced0f0f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1004 : PLift (G 61682 61752) := ⟨bs [0x1e1ed0290f0f7,0x1e20da356f107,0x3c450f116f115,0x1417834e2f11b,0xf121302ef121,0x1e26dd8d2f137] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1005 : PLift (G 61752 61844) := ⟨bs [0x3c4f0f13ef13d,0x3c550f156f155,0x3c5d0f176f175,0x141f8fb1af17b,0x14211e206f18d,0x3c648f194f193] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1006 : PLift (G 61844 61928) := ⟨bs [0x3c690f1a6f1a5,0x1e35c358ef1af,0x1e36c3d98f1b7,0x2e11b2aef1d5,0xa145c8d4f1e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1007 : PLift (G 61928 61982) := ⟨bs [0x142918df4f1ed,0x3c7f0f1fef1fd,0x1e4114544f209,0x1e41db692f20f,0x3c868f21cf21b,0x142d16ffcf21d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1008 : PLift (G 61982 62040) := ⟨bs [0x3c888f224f223,0x60dd37fef227,0x3c8c8f234f233,0x3c8e8f23cf23b,0x1e4801b34f241,0x1e4ac77e2f257] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1009 : PLift (G 62040 62072) := ⟨bs [0x35dc1acef25f,0x3c990f266f265,0xf2682a9ef269,0xa1a5d8c2f277] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1010 : PLift (G 62072 62132) := ⟨bs [0x79402f7ef281,0x3ca48f294f293,0xa1c54642f2a7,0xf2b06b44f2b1,0x3cac8f2b4f2b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1011 : PLift (G 62132 62190) := ⟨bs [0x35f1cb50f2b9,0x3caf0f2bef2bd,0xa1d51a3af2bf,0x3cb68f2dcf2db,0x3cbb0f2eef2ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1012 : PLift (G 62190 62214) := ⟨bs [0x612cfbf2f2ef,0x797c4860f2f9,0x1e5fd55dcf2ff,0x3cc10f306f305] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1013 : PLift (G 62214 62304) := ⟨bs [0x3cc28f30cf30b,0x2884e21cf319,0x79a12218f341,0x1e6b119d8f359,0x3cd68f35cf35b,0x1e6bc9e52f35f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1014 : PLift (G 62304 62384) := ⟨bs [0x1e6cde328f367,0x3cdc8f374f373,0x1e6ec5c62f377,0x144b95fdcf38b,0x1e71c05b0f38f,0xa274ffe2f3af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1015 : PLift (G 62384 62474) := ⟨bs [0x1e781351ef3c1,0xf3d127bef3d1,0x1e7acba86f3d7,0x39692d6ef3fb,0x145593620f403,0x28ac9bcef409] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1016 : PLift (G 62474 62534) := ⟨bs [0x3d030f40ef40d,0x3d048f414f413,0x3654698f421,0x3d090f426f425,0x3d0a8f42cf42b,0x3d110f446f445] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1017 : PLift (G 62534 62598) := ⟨bs [0x3d128f44cf44b,0x3d150f456f455,0x145d8982ef463,0x3d1d0f476f475,0x1e8fc1f3ef47f,0x3d210f486f485] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1018 : PLift (G 62598 62654) := ⟨bs [0x3d228f48cf48b,0xa310eb80f499,0x3d288f4a4f4a3,0x1e9506224f4a9,0x1e95cc752f4af,0x3d2f0f4bef4bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1019 : PLift (G 62654 62732) := ⟨bs [0x14659546cf4c3,0x1467824c8f4db,0x1e9bc5990f4df,0x3d3b0f4eef4ed,0x3d408f504f503,0xc409b024f50b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1020 : PLift (G 62732 62774) := ⟨bs [0xa3642dbcf517,0x1ea408f54f521,0xf52983aef529,0x146f1de60f535] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1021 : PLift (G 62774 62792) := ⟨bs [0x46144c2af547] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1022 : PLift (G 62792 62870) := ⟨bs [0xf5509d38f551,0x3d588f564f563,0x8d94ffef56b,0x3d608f584f583,0xc4703056f58d,0x3d650f596f595] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1023 : PLift (G 62870 62904) := ⟨bs [0x7acd0b98f599,0x1eb6064e4f5b1,0x1eb6dc830f5b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1024 : PLift (G 62904 62928) := ⟨bs [0x62515f2ef5c9,0x1eb9c177af5cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1025 : PLift (G 62928 62970) := ⟨bs [0x3d75e254f5d1,0x3d768f5dcf5db,0x7afc17ecf5f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1026 : PLift (G 62970 63030) := ⟨bs [0x147f988eef5fb,0x3d810f606f605,0xa404f360f607,0x3d828f60cf60b,0x3d830f60ef60d,0x3d8d0f636f635] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1027 : PLift (G 63030 63098) := ⟨bs [0x1ec6ce05af637,0x3d948f654f653,0x3d968f65cf65b,0x1ecc1b292f661,0x1eccdcfbcf667,0x7b3c78e2f679] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1028 : PLift (G 63098 63180) := ⟨bs [0x1ecfda576f67f,0x1ed1149f0f689,0x36cc312ef697,0x3da68f69cf69b,0x3dab0f6aef6ad,0x3db28f6ccf6cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1029 : PLift (G 63180 63278) := ⟨bs [0x3db70f6def6dd,0x1edbcbe02f6df,0xc58917ecf6eb,0x292caa34f709,0x1ee1c86a2f70f,0x3dcb0f72ef72d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1030 : PLift (G 63278 63282) := ⟨bs [0x46a1755af731] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1031 : PLift (G 63282 63338) := ⟨bs [0x3dd08f744f743,0x1ee9d6f98f74f,0x3dd42b30f751,0x3dd50f756f755,0x3dd88f764f763,0x1eed18576f769] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1032 : PLift (G 63338 63368) := ⟨bs [0x3ddc8f774f773,0x7bbc6ea4f779,0x630166eef781,0x1ef0dedaaf787] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1033 : PLift (G 63368 63420) := ⟨bs [0x1ef211f48f791,0x3de70f79ef79d,0x1ef3c719af79f,0x3de90f7a6f7a5,0xf7b0ebe4f7b1,0x3dee8f7bcf7bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1034 : PLift (G 63420 63474) := ⟨bs [0x3def0f7bef7bd,0x1ef9d6360f7cf,0x3df48f7d4f7d3,0x1efcd582af7e7,0x3dfa8f7ecf7eb,0x3dfd46b4f7f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1035 : PLift (G 63474 63528) := ⟨bs [0x371c0450f7ff,0x3e010f806f805,0x14ab8a39ef80b,0x7c1150e0f821,0x1f04dd7c0f827] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1036 : PLift (G 63528 63590) := ⟨bs [0x8dd02598f82d,0x3e0d0f836f835,0x1f08c73ccf847,0xdcc82a6f859,0x3e188f864f863,0x3e190f866f865] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1037 : PLift (G 63590 63630) := ⟨bs [0x1f0dddb9af86f,0xf8701d2af871,0x1f0ed91daf877,0x3e1e8f87cf87b,0x1f10011aef881,0x3e230f88ef88d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1038 : PLift (G 63630 63668) := ⟨bs [0x1f13cd678f89f,0xa5c0d6d2f8a1,0x3e2a8f8acf8ab,0x3e2c8f8b4f8b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1039 : PLift (G 63668 63692) := ⟨bs [0x637c4b82f8b7,0x1a318008f8c9,0x14bb8a730f8cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1040 : PLift (G 63692 63738) := ⟨bs [0x1f1a05e78f8d1,0x1f1adc202f8d7,0x14bd18782f8dd,0x1f1cd7e7cf8e7,0x1f1dca192f8ef,0xf8f878f6f8f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1041 : PLift (G 63738 63800) := ⟨bs [0x1f1fc9636f8ff,0x1f2205172f911,0x3e470f91ef91d,0x3e490f926f925,0x1f2601d3cf931,0x1f26c6612f937] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1042 : PLift (G 63800 63854) := ⟨bs [0x3e4e8f93cf93b,0x1f2804ae0f941,0xa63502b4f94f,0x1f2bcd132f95f,0xc7989bef961,0x3e5b0f96ef96d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1043 : PLift (G 63854 63930) := ⟨bs [0x1f2e0e8b8f971,0x1f2ec8f82f977,0x4b06220f99d,0x3e688f9a4f9a3,0x299cc0d6f9a9,0x1f371224af9b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1044 : PLift (G 63930 64020) := ⟨bs [0x3e730f9cef9cd,0x1f3d0bbaef9e9,0x3e7f0f9fef9fd,0x1f40cfb04fa07,0x3e830fa0efa0d,0x3e848fa14fa13] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1045 : PLift (G 64020 64092) := ⟨bs [0xa6c058a4fa21,0x3e890fa26fa25,0x1f47c8db8fa3f,0x9b8e6a2fa43,0x1f4a00166fa51,0x3e968fa5cfa5b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1046 : PLift (G 64092 64158) := ⟨bs [0x3e9b0fa6efa6d,0x3e9e8fa7cfa7b,0x1f52cb07efa97,0xa71117acfa99,0x3ea70fa9efa9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1047 : PLift (G 64158 64232) := ⟨bs [0x6f6992c6faab,0x3eae8fabcfabb,0x3eaf0fabefabd,0x1f5b11564fad9,0x1f5bc7aaefadf,0x1f5cd432cfae7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1048 : PLift (G 64232 64304) := ⟨bs [0x3ebb0faeefaed,0x1f61c418efb0f,0x37cda7e0fb17,0x3ec68fb1cfb1b,0x3ecb0fb2efb2d,0x1f65c5c98fb2f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1049 : PLift (G 64304 64400) := ⟨bs [0x1f67c7c50fb3f,0x1f68da59efb47,0x3ed30fb4efb4d,0x3edd0fb76fb75,0x3edf0fb7efb7d,0xa7b554dafb8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1050 : PLift (G 64400 64404) := ⟨bs [0x4d68a8befb93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1051 : PLift (G 64404 64490) := ⟨bs [0xfbb06e18fbb1,0x4fc6fa2fbb7,0x3ef08fbc4fbc3,0x3ef10fbc6fbc5,0x3ef88fbe4fbe3,0xfbe9a86afbe9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1052 : PLift (G 64490 64580) := ⟨bs [0x3efc8fbf4fbf3,0x1f8000fd0fc01,0x1f851c19efc29,0x1f86c6264fc37,0x1f880af10fc41,0x3f108fc44fc43] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1053 : PLift (G 64580 64614) := ⟨bs [0x1f89ce9a8fc4f,0x7e2c817efc59,0xa840bcccfc61,0x3f190fc66fc65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1054 : PLift (G 64614 64668) := ⟨bs [0xc9f18f80fc6d,0x15098243cfc73,0x1f8f15692fc79,0x3f250fc96fc95,0x1f92d660efc97,0x3f268fc9cfc9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1055 : PLift (G 64668 64764) := ⟨bs [0x1f94d416efca7,0x3f2d0fcb6fcb5,0x907006c8fcc5,0x3f330fccefccd,0x1513964defceb,0x3f3e8fcfcfcfb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1056 : PLift (G 64764 64818) := ⟨bs [0x3f430fd0efd0d,0x383ce4acfd0f,0x1fa305db0fd19,0x3f4a8fd2cfd2b,0x7e99f7f8fd31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1057 : PLift (G 64818 64872) := ⟨bs [0x54712522fd51,0x3f550fd56fd55,0x1facc1078fd67] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1058 : PLift (G 64872 64920) := ⟨bs [0x90d01684fd6d,0x1fadda8b6fd6f,0x151f8c832fd7b,0x3f610fd86fd85,0x1fb2ca226fd97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1059 : PLift (G 64920 64952) := ⟨bs [0xa911b894fd99,0xa9147d6cfd9f,0x1fb51d4befda9,0x1fb6d095efdb7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1060 : PLift (G 64952 65030) := ⟨bs [0x1fb919ceafdc9,0x3f790fde6fde5,0x9118fa8efdeb,0x3f7c8fdf4fdf3,0x3f808fe04fe03,0x3f810fe06fe05] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1061 : PLift (G 65030 65090) := ⟨bs [0xfe08dd72fe09,0x70f1990efe1d,0x1fc4c06c2fe27,0x1fc5c5fa6fe2f,0x1c40630afe41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1062 : PLift (G 65090 65130) := ⟨bs [0x3f928fe4cfe4b,0x3f930fe4efe4d,0x1fcac8b9cfe57,0xa99502f6fe5f,0x3f988fe64fe63,0x7f349530fe69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1063 : PLift (G 65130 65180) := ⟨bs [0x3f9d0fe76fe75,0x3f9e8fe7cfe7b,0x1fd1cce06fe8f,0x3fa48fe94fe93,0x3fa50fe96fe95,0x3fa68fe9cfe9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1064 : PLift (G 65180 65268) := ⟨bs [0x1fd3dd560fe9f,0x3fac8feb4feb3,0x3faf0febefebd,0x1fdaddd3afed7,0xfee8b028fee9,0x3fbc8fef4fef3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1065 : PLift (G 65268 65328) := ⟨bs [0x3fbd0fef6fef5,0x1fe0c41dcff07,0x3fc30ff0eff0d,0x3fc70ff1eff1d,0x3fca8ff2cff2b,0x1fe5ce460ff2f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1066 : PLift (G 65328 65408) := ⟨bs [0x1fe911308ff49,0x3fd30ff4eff4d,0x3fd68ff5cff5b,0xcc514b4aff65,0x1fee177ceff71,0x2e74cd54ff7f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1067 : PLift (G 65408 65450) := ⟨bs [0x154b1976eff85,0x154b9b190ff8b,0x1ff1c8cccff8f,0x30b119b0ff9d,0x1ff4ce65affa7,0xffa8b0d8ffa9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1068 : PLift (G 65450 65520) := ⟨bs [0xaa849128ffc7,0xaa90d708ffd9,0x1ffddd9e6ffef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1069 : PLift (G 65520 65544) := ⟨bs [0x1248e2defff1,0x8001e70001,0x4000900050003,0x2000ce32b0007] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1070 : PLift (G 65544 65558) := ⟨bs [0xaab5312b000f,0x71d0cd150015] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1071 : PLift (G 65558 65600) := ⟨bs [0x155795565001b,0x400a9002d002b,0x400b1002f002d,0x400c900350033,0x2007c77a7003f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1072 : PLift (G 65600 65618) := ⟨bs [0x80259e230049,0x155d18950051] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1073 : PLift (G 65618 65634) := ⟨bs [0x40171005f005d,0x200c130fd0061] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1074 : PLift (G 65634 65648) := ⟨bs [0x4945d077006f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1075 : PLift (G 65648 65700) := ⟨bs [0x401c900750073,0x10078ddd30079,0x40231008f008d,0x2012d3f590097,0x4028900a500a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1076 : PLift (G 65700 65718) := ⟨bs [0x721106fd00a5,0x402a900ad00ab,0x20161e1d100b1,0x402d100b700b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1077 : PLift (G 65718 65732) := ⟨bs [0x2016c860100b7,0x100c11eaf00c1,0x1565869f700c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1078 : PLift (G 65732 65778) := ⟨bs [0x8070b1c300e1,0x201e0876f00f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1079 : PLift (G 65778 65838) := ⟨bs [0x403f100ff00fd,0x20220ea6b0111,0x4048901250123,0x2024c71310127,0x404b1012f012d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1080 : PLift (G 65838 65868) := ⟨bs [0xab75360f012f,0x404c901350133,0x156f9a0c1013b,0x40529014d014b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1081 : PLift (G 65868 65900) := ⟨bs [0x1015817ad0159,0x9318fe37016b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1082 : PLift (G 65900 65930) := ⟨bs [0x10181f2d90181,0x2030c95510187,0x2aec9ef50189] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1083 : PLift (G 65930 65984) := ⟨bs [0x2033d94fb019f,0x4069101a701a5,0x406a901ad01ab,0x406f101bf01bd,0xabd5ce6f01bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1084 : PLift (G 65984 66048) := ⟨bs [0x1c44bbd01c9,0x407b101ef01ed,0x407d101f701f5,0x19ccfd2d01f9,0x203fd00ff01ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1085 : PLift (G 66048 66104) := ⟨bs [0x1f49f99d0213,0x2042c89e70217,0x4088902250223,0x2045017090229,0x2046c03c30237] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1086 : PLift (G 66104 66138) := ⟨bs [0x408e9023d023b,0x408f1023f023d,0x812dbc2f0259] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1087 : PLift (G 66138 66222) := ⟨bs [0xcec88910271,0x204f06a470279,0x409f1027f027d,0x40a0902850283,0x2051cd431028f,0x40ab102af02ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1088 : PLift (G 66222 66302) := ⟨bs [0x2057cac0702bf,0xac94c09102df,0x40bd102f702f5,0x159511ddb02fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1089 : PLift (G 66302 66344) := ⟨bs [0x8190144b0321,0x2064d0a330327] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1090 : PLift (G 66344 66374) := ⟨bs [0x40ca9032d032b,0x2066d704f0337,0x206702ecb0339,0x40d1103470345] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1091 : PLift (G 66374 66414) := ⟨bs [0x10348e3eb0349,0x2069dfcdd034f,0x40d8903650363,0x40db1036f036d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1092 : PLift (G 66414 66432) := ⟨bs [0x4a248aab037f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1093 : PLift (G 66432 66500) := ⟨bs [0x207210eeb0391,0x355b74d0399,0x2073d9763039f,0x40e8903a503a3,0x40ee903bd03bb,0x40f0903c503c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1094 : PLift (G 66500 66554) := ⟨bs [0x40f3103cf03cd,0x40f6903dd03db,0x2f40ecff03e1,0x40f9103e703e5,0x15a91aa3303ed,0x207f01be503f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1095 : PLift (G 66554 66570) := ⟨bs [0x820401710409] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1096 : PLift (G 66570 66594) := ⟨bs [0xd009fa21040b,0x41069041d041b,0x104206c110421] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1097 : PLift (G 66594 66618) := ⟨bs [0x20851cbdb0429,0x821cce8f0439] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1098 : PLift (G 66618 66684) := ⟨bs [0x4111104470445,0x4114904550453,0x41171045f045d,0x94d8a7c1047b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1099 : PLift (G 66684 66698) := ⟨bs [0x56d8c0230489] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1100 : PLift (G 66698 66740) := ⟨bs [0xd0700999048d,0x209300d770499,0x20941e1b104a1,0x412b104af04ad,0x412c904b504b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1101 : PLift (G 66740 66764) := ⟨bs [0x1c308b7904bd,0xadd49a8704bf,0x15bb8705d04cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1102 : PLift (G 66764 66822) := ⟨bs [0x209ccea4104e7,0x413b104ef04ed,0x104f8363f04f9,0x4141105070505] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1103 : PLift (G 66822 66884) := ⟨bs [0x1a1d83930519,0x4148905250523,0x4149105270525,0x20a5c52cb052f,0x15c51c6d7053d,0x4150905450543] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1104 : PLift (G 66884 66932) := ⟨bs [0xae30f58b0549,0x20acc91570567,0x415a9056d056b,0x15c995edf0573] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1105 : PLift (G 66932 66960) := ⟨bs [0xae54c265057f,0x4160905850583,0x15cb160190585,0x20b1c30e1058f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1106 : PLift (G 66960 67004) := ⟨bs [0x41671059f059d,0x20b40016f05a1,0x416e905bd05bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1107 : PLift (G 67004 67022) := ⟨bs [0x45d0c1fd05cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1108 : PLift (G 67022 67044) := ⟨bs [0xe8d038105d9,0x4178905e505e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1109 : PLift (G 67044 67050) := ⟨bs [0x82f49ea905e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1110 : PLift (G 67050 67058) := ⟨bs [0x417c1fe505f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1111 : PLift (G 67058 67062) := ⟨bs [0x417d105f705f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1112 : PLift (G 67062 67074) := ⟨bs [0x4181863b0601] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1113 : PLift (G 67074 67080) := ⟨bs [0x20c0d070b0607] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1114 : PLift (G 67080 67104) := ⟨bs [0x4ae5dff1061f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1115 : PLift (G 67104 67130) := ⟨bs [0x20c6049c70631,0x831dc3610639] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1116 : PLift (G 67130 67182) := ⟨bs [0x4190906450643,0x4191106470645,0x20ca159bd0651,0x4195106570655,0x20cc17b890661,0x419b1066f066d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1117 : PLift (G 67182 67214) := ⟨bs [0x419c906750673,0x15df1d9930675,0x41a29068d068b,0x41a31068f068d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1118 : PLift (G 67214 67220) := ⟨bs [0x83494c1f0691,0x1499e05d0693] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1119 : PLift (G 67220 67274) := ⟨bs [0x20d3d24d3069f,0x20d5d17ab06af,0x41af106bf06bd,0x20d8ddb9306c7,0x20d90946b06c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1120 : PLift (G 67274 67344) := ⟨bs [0x106d87e9d06d9,0x41ba906ed06eb,0x15eb95b4b070b,0x20e1cf4ad070f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1121 : PLift (G 67344 67400) := ⟨bs [0x41c5107170715,0x20e5072130729,0x20e7d4a47073f,0x20e8ccfcd0747] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1122 : PLift (G 67400 67410) := ⟨bs [0x41d5de910751] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1123 : PLift (G 67410 67430) := ⟨bs [0x41d4907550753,0x41d71075f075d,0x41d8907650763,0x41d9107670765] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1124 : PLift (G 67430 67448) := ⟨bs [0x83b4417f0769,0x20eed66af0777] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1125 : PLift (G 67448 67482) := ⟨bs [0x41df1077f077d,0x41e5107970795,0x6970cd0f0799] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1126 : PLift (G 67482 67490) := ⟨bs [0x41e9f69b07a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1127 : PLift (G 67490 67532) := ⟨bs [0x41e9107a707a5,0x41ea907ad07ab,0x20f6cb41107b7,0x41f0907c507c3,0x15fb9743f07cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1128 : PLift (G 67532 67568) := ⟨bs [0xafe0a3bb07d1,0x41f6907dd07db,0x1f0db34307e7,0x20fdce42b07ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1129 : PLift (G 67568 67590) := ⟨bs [0x20ff0093307f9,0x15ff8403707fb,0x4201108070805] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1130 : PLift (G 67590 67602) := ⟨bs [0x69a007410811] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1131 : PLift (G 67602 67608) := ⟨bs [0x4b7568c30817] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1132 : PLift (G 67608 67632) := ⟨bs [0x4208908250823,0x2105dd581082f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1133 : PLift (G 67632 67652) := ⟨bs [0x4678e9fd0843] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1134 : PLift (G 67652 67742) := ⟨bs [0x210bcfc7b085f,0x421c908750873,0x421f1087f087d,0x160b9329f088b,0x4225108970895,0x160d1f8cb089d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1135 : PLift (G 67742 67752) := ⟨bs [0x69dc8a9308a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1136 : PLift (G 67752 67758) := ⟨bs [0x517089d508ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1137 : PLift (G 67758 67778) := ⟨bs [0x2115cd48308af,0x422c908b508b3,0xb080553b08c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1138 : PLift (G 67778 67790) := ⟨bs [0xb085cfd508c7,0x16110ba7108cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1139 : PLift (G 67790 67830) := ⟨bs [0x108d96f0508d9,0x211bde52708df,0x16139db9308eb,0x423d108f708f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1140 : PLift (G 67830 67892) := ⟨bs [0x16158b8f10903,0x42431090f090d,0x42469091d091b,0x424a9092d092b,0xd42a122f0933] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1141 : PLift (G 67892 67934) := ⟨bs [0xd4313061093d,0x212acfc6d0957,0xd448da1f095b,0x42571095f095d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1142 : PLift (G 67934 67958) := ⟨bs [0x161d8b5d30963,0x212cd6f070967,0x425d109770975] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1143 : PLift (G 67958 67988) := ⟨bs [0x6a3152d70979,0x212fc7955097f,0x42629098d098b,0x4264909950993] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1144 : PLift (G 67988 68042) := ⟨bs [0xb111bd810999,0x2136da16909b7,0x2139003d109c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1145 : PLift (G 68042 68100) := ⟨bs [0x16270328b09d5,0x4276909dd09db,0x213cdded509e7,0x213edc07709f7,0x428090a050a03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1146 : PLift (G 68100 68148) := ⟨bs [0x2141dc3310a0f,0x2142084870a11,0xd4f09ce90a2d,0x428c90a350a33] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1147 : PLift (G 68148 68208) := ⟨bs [0x10a407a910a41,0x429290a4d0a4b,0x214dcc8810a6f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1148 : PLift (G 68208 68210) := ⟨bs [0x429d23f90a71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1149 : PLift (G 68210 68280) := ⟨bs [0x429d10a770a75,0x429e90a7d0a7b,0x42a090a850a83,0x2151cb6f50a8f,0x42a910aa70aa5,0x2156db7130ab7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1150 : PLift (G 68280 68330) := ⟨bs [0x6ab0ccc70ab9,0x3b4c619d0ad7,0x215d091b90ae9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1151 : PLift (G 68330 68390) := ⟨bs [0x6acce8b10aff,0xd5a95b090b13,0x42c910b270b25] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1152 : PLift (G 68390 68450) := ⟨bs [0x2165d6dfd0b2f,0x42d510b570b55,0x3ee9f1d90b5b,0x216bcb6ff0b5f,0xb24a70d0b61] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1153 : PLift (G 68450 68484) := ⟨bs [0x85bceba90b79,0x42df10b7f0b7d,0x42e090b850b83] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1154 : PLift (G 68484 68490) := ⟨bs [0x4c704cab0b89] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1155 : PLift (G 68490 68522) := ⟨bs [0x164b8d8e70b8b,0x2ad013850b95,0x42e690b9d0b9b,0x2175155f50ba9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1156 : PLift (G 68522 68544) := ⟨bs [0x98f868310bb3,0x42ee90bbd0bbb,0x2177dd6d50bbf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1157 : PLift (G 68544 68568) := ⟨bs [0x217acab5d0bd7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1158 : PLift (G 68568 68582) := ⟨bs [0x4771ddb30be5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1159 : PLift (G 68582 68670) := ⟨bs [0x42fd10bf70bf5,0x430090c050c03,0x21831806b0c19,0x2183c5d010c1f,0x430c90c350c33,0x430f10c3f0c3d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1160 : PLift (G 68670 68712) := ⟨bs [0x431290c4d0c4b,0x2189ca64d0c4f,0x431690c5d0c5b,0x218cc7de70c67] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1161 : PLift (G 68712 68714) := ⟨bs [0x10c6962270c69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1162 : PLift (G 68714 68738) := ⟨bs [0x863c05d70c79,0x21901d6f10c81] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1163 : PLift (G 68738 68772) := ⟨bs [0x2190d6bb10c87,0x1661040930c8d,0x2193c6d7b0c9f,0xd6e9fc9f0ca3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1164 : PLift (G 68772 68822) := ⟨bs [0x21951b94d0ca9,0x2196e04170cb7,0x433310ccf0ccd,0x433490cd50cd3,0x1667181fd0cd5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1165 : PLift (G 68822 68892) := ⟨bs [0x219fd251b0cff,0x21a1d68070d0f,0xb3603d750d11,0x434690d1d0d1b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1166 : PLift (G 68892 68910) := ⟨bs [0x10d21e48b0d21,0x434890d250d23,0x21a4cfd3d0d27,0x434b10d2f0d2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1167 : PLift (G 68910 68994) := ⟨bs [0x166f10d5f0d35,0x21a7c18930d3f,0x435490d550d53,0x435890d650d63,0x310197e90d81] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1168 : PLift (G 68994 69032) := ⟨bs [0x35e996530d89,0xd7a9525f0d93,0x436690d9d0d9b,0x436910da70da5,0x21b4ce8210da7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1169 : PLift (G 69032 69120) := ⟨bs [0x437110dc70dc5,0x437290dcd0dcb,0x10dd1cf670dd1,0x437d10df70df5,0x21bfd79cb0dff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1170 : PLift (G 69120 69164) := ⟨bs [0x21c0dcb8b0e07,0x21c2dcf390e17,0x438710e1f0e1d,0x21c3c5a630e1f,0x438a90e2d0e2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1171 : PLift (G 69164 69194) := ⟨bs [0x21c8e1b1b0e47,0x8725b3d70e49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1172 : PLift (G 69194 69240) := ⟨bs [0x439310e4f0e4d,0x439490e550e53,0x439910e670e65,0x10e70b3c50e71,0x21cecd1e50e77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1173 : PLift (G 69240 69260) := ⟨bs [0xb455b4c50e7f,0x10e88a3770e89,0x43a290e8d0e8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1174 : PLift (G 69260 69314) := ⟨bs [0x21d1e10b30e8f,0x21d8015b90ec1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1175 : PLift (G 69314 69318) := ⟨bs [0x5351138b0ec5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1176 : PLift (G 69318 69384) := ⟨bs [0x21db20bd30ed9,0xd8b022390edd,0x43be90efd0efb,0x43c090f050f03,0x21e0dfbd70f07] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1177 : PLift (G 69384 69428) := ⟨bs [0x43c310f0f0f0d,0x10f1849a70f19,0x16978c1490f1b,0x43cc90f350f33] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1178 : PLift (G 69428 69458) := ⟨bs [0xd58ddd0f37,0x21e7d46450f3f,0x10f51c29f0f51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1179 : PLift (G 69458 69494) := ⟨bs [0x21eade09f0f57,0x43d690f5d0f5b,0x21ec05cd10f61,0x3649f6a10f69,0x43dc90f750f73,0x43dd10f770f75] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1180 : PLift (G 69494 69498) := ⟨bs [0x26c92a4f0f79] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1181 : PLift (G 69498 69500) := ⟨bs [0x538936150f7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1182 : PLift (G 69500 69654) := ⟨bs [0x43e890fa50fa3,0x43ed10fb70fb5,0x21fb12f7f0fd9,0x21fec50e30ff7,0x4405110171015] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1183 : PLift (G 69654 69698) := ⟨bs [0xd9b01f0b101d,0x440b1102f102d,0x440e9103d103b,0x1104054091041] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1184 : PLift (G 69698 69740) := ⟨bs [0x16b111f4f104d,0x220d1242d1069,0x441a9106d106b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1185 : PLift (G 69740 69764) := ⟨bs [0x8841daab1081,0x4420910851083] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1186 : PLift (G 69764 69828) := ⟨bs [0x2210db6cd1087,0x4424910951093,0x221606e7b10b1,0xda310f1d10bd,0x4430910c510c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1187 : PLift (G 69828 69848) := ⟨bs [0x16bb0184110c5,0x110c962cb10c9,0x221ac12df10d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1188 : PLift (G 69848 69900) := ⟨bs [0x221c1a8a510e1,0x7949309710e3,0x443d110f710f5,0x44429110d110b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1189 : PLift (G 69900 69930) := ⟨bs [0x2222c94391117,0x8895bf231129] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1190 : PLift (G 69930 69998) := ⟨bs [0x1d88bfc9112b,0x444d111371135,0x2228d071b1147,0x222cd973b1167,0x445b1116f116d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1191 : PLift (G 69998 70010) := ⟨bs [0x222e13be51171,0x445c911751173,0xb650cc5b1179] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1192 : PLift (G 70010 70020) := ⟨bs [0x5429c3cd1183] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1193 : PLift (G 70020 70040) := ⟨bs [0x2232e02651197] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1194 : PLift (G 70040 70052) := ⟨bs [0x48f9930911a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1195 : PLift (G 70052 70118) := ⟨bs [0x446b111af11ad,0x446c911b511b3,0x2237c998b11bf,0x16d1980d111d3,0x223bc7a6511df,0x4479111e711e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1196 : PLift (G 70118 70158) := ⟨bs [0x111e8b52b11e9,0x447a911ed11eb,0x447e911fd11fb,0x16d51c64711fd,0x44831120f120d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1197 : PLift (G 70158 70184) := ⟨bs [0x4484912151213,0x22440d5851221,0xdb510d031225,0x2244c6c091227] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1198 : PLift (G 70184 70208) := ⟨bs [0x2246c8a7b1237,0x22471cc8b1239,0xb6d483e9123f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1199 : PLift (G 70208 70242) := ⟨bs [0x2249d1147124f,0x4495112571255,0x44971125f125d,0x224c150251261] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1200 : PLift (G 70242 70272) := ⟨bs [0x8934b9bf1269,0x224fd7b89127f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1201 : PLift (G 70272 70310) := ⟨bs [0x11290f15f1291,0x112989a8f1299,0x3450620712a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1202 : PLift (G 70310 70328) := ⟨bs [0x225502ae312a9,0x36f0bd2912b1,0xb7261ccb12b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1203 : PLift (G 70328 70374) := ⟨bs [0xb734599912cf,0x44b9112e712e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1204 : PLift (G 70374 70394) := ⟨bs [0x9d181c9112eb,0x2fd2129f12ed,0x225f0473112f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1205 : PLift (G 70394 70440) := ⟨bs [0xb765d9d51317,0x16ed16387131d,0x2264c1a991327] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1206 : PLift (G 70440 70482) := ⟨bs [0xdc28446b1333,0x22671c90d1339,0x16efa0a8f133b,0x1b88ef011351] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1207 : PLift (G 70482 70490) := ⟨bs [0x226adaaeb1357,0x5bc943f71359] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1208 : PLift (G 70490 70530) := ⟨bs [0x44d9113671365,0x44da9136d136b,0x11380d8331381] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1209 : PLift (G 70530 70572) := ⟨bs [0x89c48a2b1389,0x44e5113971395,0x44ea913ad13ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1210 : PLift (G 70572 70620) := ⟨bs [0x44eb113af13ad,0x2276d35d713b7,0x44ef113bf13bd,0x2279cf50113cf,0x44f6913dd13db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1211 : PLift (G 70620 70640) := ⟨bs [0xdcb1711913dd,0x16fd8369f13e3,0x227dd3b9113ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1212 : PLift (G 70640 70664) := ⟨bs [0x5c02016f1401,0x2280db9f11407] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1213 : PLift (G 70664 70754) := ⟨bs [0x45029140d140b,0x2283e26c7141f,0x450d114371435,0x450f1143f143d,0x228920ded1449,0x228c05e0f1461] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1214 : PLift (G 70754 70784) := ⟨bs [0x114709b031471,0xb8544dd5147f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1215 : PLift (G 70784 70824) := ⟨bs [0x22911f7bb1489,0x2294caf0d14a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1216 : PLift (G 70824 70844) := ⟨bs [0x8a5c994f14b9,0x452e914bd14bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1217 : PLift (G 70844 70878) := ⟨bs [0x2298082b914c1,0x4531114c714c5,0x1711a006714d3,0x4537114df14dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1218 : PLift (G 70878 70880) := ⟨bs [0xb895d9b714df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1219 : PLift (G 70880 70892) := ⟨bs [0x49d88cb914eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1220 : PLift (G 70892 70922) := ⟨bs [0x453d114f714f5,0x1150014351501,0x22a0c29d91507,0xf6476851509] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1221 : PLift (G 70922 70950) := ⟨bs [0x8a8cf7c51519,0x4549115271525] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1222 : PLift (G 70950 70958) := ⟨bs [0x22a4cea991527,0x454b1152f152d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1223 : PLift (G 70958 70980) := ⟨bs [0x5c69718b1539,0x4550915451543] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1224 : PLift (G 70980 70998) := ⟨bs [0x171b09d651545,0x6eee05ad154f,0x4555115571555] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1225 : PLift (G 70998 71024) := ⟨bs [0xb8e626571557,0x171d8638f1563,0x22adc3945156f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1226 : PLift (G 71024 71090) := ⟨bs [0x22afc9009157f,0x172194bfb1593,0x45671159f159d,0x22b5106f915a9,0x1724001715b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1227 : PLift (G 71090 71148) := ⟨bs [0x1454d3115cf,0x22bb2237f15d9,0x22bcc03e715e7,0x457a915ed15eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1228 : PLift (G 71148 71154) := ⟨bs [0x457e012f15f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1229 : PLift (G 71154 71172) := ⟨bs [0x115f9300b15f9,0x22bfe17a115ff,0x4580916051603] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1230 : PLift (G 71172 71210) := ⟨bs [0x6f3c3bbf1617,0x22c51f26b1629] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1231 : PLift (G 71210 71238) := ⟨bs [0x5cc2100d1641,0x4591116471645] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1232 : PLift (G 71238 71250) := ⟨bs [0x8b288e4f1651] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1233 : PLift (G 71250 71258) := ⟨bs [0x8b2cc8bb1659] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1234 : PLift (G 71258 71288) := ⟨bs [0x9f10054b165d,0x22cbca03f165f,0x22ced17831677] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1235 : PLift (G 71288 71328) := ⟨bs [0x1c90e70d167d,0x45a5116971695,0x22d3c4435169f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1236 : PLift (G 71328 71334) := ⟨bs [0x5ce1185d16a1,0x45a9116a716a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1237 : PLift (G 71334 71340) := ⟨bs [0x45aa916ad16ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1238 : PLift (G 71340 71342) := ⟨bs [0x4a51b5ab16ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1239 : PLift (G 71342 71354) := ⟨bs [0x45ac916b516b3,0x8b5d325316b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1240 : PLift (G 71354 71412) := ⟨bs [0x22d7d6d4f16bf,0x45b0916c516c3,0x45b6916dd16db,0x173d0f52116dd,0x22dcd939b16e7,0x45bc916f516f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1241 : PLift (G 71412 71444) := ⟨bs [0x45bd116f716f5,0x45be916fd16fb,0x45c1117071705,0x45c31170f170d,0x7c0907331713] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1242 : PLift (G 71444 71474) := ⟨bs [0x45c71171f171d,0x6facba05172f,0x1745ac2b1731] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1243 : PLift (G 71474 71538) := ⟨bs [0x22e6dec011737,0x45ce9173d173b,0x22e9d5ffd174f,0x22ecc26551767,0x22ee14d711771] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1244 : PLift (G 71538 71564) := ⟨bs [0x45df1177f177d,0x14b55363177f,0x45e29178d178b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1245 : PLift (G 71564 71570) := ⟨bs [0x4fe18c8f1791] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1246 : PLift (G 71570 71598) := ⟨bs [0x5d3976c117a9,0x45eb117af17ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1247 : PLift (G 71598 71694) := ⟨bs [0x22fa1015317d1,0x22fbdf55317df,0x22fdd267717ef,0x2555718117f7,0x46031180f180d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1248 : PLift (G 71694 71742) := ⟨bs [0x4604918151813,0x46069181d181b,0x2303c6f45181f,0x2304127c11821,0x2304d08bf1827,0x460f1183f183d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1249 : PLift (G 71742 71778) := ⟨bs [0x175d31f91851,0x8c309e2b1861] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1250 : PLift (G 71778 71790) := ⟨bs [0x461b1186f186d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1251 : PLift (G 71790 71808) := ⟨bs [0x5024e25d187f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1252 : PLift (G 71808 71850) := ⟨bs [0xbb017f471881,0x46231188f188d,0x46271189f189d,0x4628918a518a3,0x23151d9af18a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1253 : PLift (G 71850 71880) := ⟨bs [0xe090f9c718b5,0x462e918bd18bb,0x2318cb6cd18c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1254 : PLift (G 71880 71888) := ⟨bs [0x8c64c80b18c9,0x2319c4a4118cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1255 : PLift (G 71888 71948) := ⟨bs [0x4636918dd18db,0x4639118e718e5,0x463b118ef18ed,0x463f118ff18fd,0x4641119071905,0x46429190d190b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1256 : PLift (G 71948 72000) := ⟨bs [0x46469191d191b,0x4648919251923,0x2325e27ff192f,0x464c919351933,0x232701dfb1939,0x2327dce69193f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1257 : PLift (G 72000 72054) := ⟨bs [0x4654919551953,0x232bcad45195f,0x17738f9df196b,0x232dc96fb196f,0x465d119771975] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1258 : PLift (G 72054 72104) := ⟨bs [0x23311bddb1989,0x46631198f198d,0x2333165751999,0x46669199d199b,0x4669119a719a5,0x2334cef4519a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1259 : PLift (G 72104 72168) := ⟨bs [0x466b119af19ad,0x4672919cd19cb,0x233c0fd9719e1,0x233ce2cb119e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1260 : PLift (G 72168 72222) := ⟨bs [0xbbf0a04719e9,0x467b119ef19ed,0x468491a151a13,0x468711a1f1a1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1261 : PLift (G 72222 72254) := ⟨bs [0xbc1422711a1f,0x468891a251a23,0x468911a271a25,0x90a15ed1a3b,0x468f11a3f1a3d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1262 : PLift (G 72254 72288) := ⟨bs [0x26f123211a4d,0x33548bff1a4f,0x178704d1b1a55,0x234bcbaf11a5f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1263 : PLift (G 72288 72342) := ⟨bs [0x17898bfdd1a73,0x11a78d6dd1a79,0x235209e4d1a91,0x46a511a971a95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1264 : PLift (G 72342 72422) := ⟨bs [0x235408ccb1aa1,0x2355c09851aaf,0x46ae91abd1abb,0x2357dc6e71abf,0x17931659b1ae5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1265 : PLift (G 72422 72470) := ⟨bs [0x235dc208b1aef,0x46c311b0f1b0d,0x46c491b151b13,0x225075171b15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1266 : PLift (G 72470 72504) := ⟨bs [0x11b2231ef1b21,0x46cb11b2f1b2d,0x18a047471b31,0x2366e26351b37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1267 : PLift (G 72504 72560) := ⟨bs [0x46d511b571b55,0x46d891b651b63,0x236cd2d4b1b67,0x236dda25b1b6f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1268 : PLift (G 72560 72618) := ⟨bs [0x11b808edf1b81,0x46e911ba71ba5,0x11baa15411ba9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1269 : PLift (G 72618 72650) := ⟨bs [0x2375c8f3d1baf,0x46f091bc51bc3,0x2378c74531bc7,0x237900d3d1bc9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1270 : PLift (G 72650 72672) := ⟨bs [0xa230f1ef1bd5,0x237bd37ad1bdf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1271 : PLift (G 72672 72702) := ⟨bs [0xbd41c6751be1,0x237cde5d11be7,0x144842171bf1,0x46ff11bff1bfd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1272 : PLift (G 72702 72740) := ⟨bs [0x470091c051c03,0x2381ce0511c0f,0xbd6491131c17,0x470711c1f1c1d,0x470891c251c23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1273 : PLift (G 72740 72798) := ⟨bs [0x470e91c3d1c3b,0x2387d4a251c3f,0x471711c5f1c5d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1274 : PLift (G 72798 72824) := ⟨bs [0x5ed230791c71,0x238ee17b31c77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1275 : PLift (G 72824 72872) := ⟨bs [0x472691c9d1c9b,0x472911ca71ca5,0x71de34f31ca7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1276 : PLift (G 72872 72884) := ⟨bs [0x7e89a6d51cb3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1277 : PLift (G 72884 72902) := ⟨bs [0x8e5d8bc91cb9,0x472f11cbf1cbd,0x473111cc71cc5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1278 : PLift (G 72902 72932) := ⟨bs [0x473291ccd1ccb,0x18c5f1a31ccf,0x473691cdd1cdb,0x17bd826251ce3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1279 : PLift (G 72932 72950) := ⟨bs [0x8e750b9f1ce9,0x473d11cf71cf5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1280 : PLift (G 72950 72974) := ⟨bs [0xcf611831cf9,0x239fd75e31cff,0x474311d0f1d0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1281 : PLift (G 72974 72978) := ⟨bs [0x4745a1b91d11] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1282 : PLift (G 72978 73038) := ⟨bs [0x474911d271d25,0xbe20b5671d31,0x474d11d371d35,0x474e91d3d1d3b,0x475311d4f1d4d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1283 : PLift (G 73038 73092) := ⟨bs [0x23a9c4bad1d4f,0x475491d551d53,0x475911d671d65,0x3f6c24051d67,0x23aed02131d77,0x476091d851d83] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1284 : PLift (G 73092 73190) := ⟨bs [0x23b4215711da1,0x23b4e23151da7,0x476b11daf1dad,0x17cf0b5df1db5,0x477711ddf1ddd,0x477911de71de5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1285 : PLift (G 73190 73238) := ⟨bs [0x17d70e5db1e15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1286 : PLift (G 73238 73244) := ⟨bs [0x580835591e1b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1287 : PLift (G 73244 73292) := ⟨bs [0x478a91e2d1e2b,0xa3919d7b1e3d,0x17db936471e4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1288 : PLift (G 73292 73352) := ⟨bs [0x23cad935b1e57,0x479711e5f1e5d,0x23cdd9f791e6f,0x479c91e751e73,0x23d0c87f51e87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1289 : PLift (G 73352 73380) := ⟨bs [0x3951612d1e91,0x17e1924e31e93,0xbf1107391e99,0x47a891ea51ea3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1290 : PLift (G 73380 73460) := ⟨bs [0x47aa91ead1eab,0x63e24051ec9,0x47b311ecf1ecd,0x23db08ff51ed9,0x47bb11eef1eed,0x47bc91ef51ef3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1291 : PLift (G 73460 73524) := ⟨bs [0x26cea051eff,0x17eb15ac91f05,0x47c291f0d1f0b,0x47cb11f2f1f2d,0x47cc91f351f33] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1292 : PLift (G 73524 73530) := ⟨bs [0x5211cd151f39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1293 : PLift (G 73530 73548) := ⟨bs [0x47d291f4d1f4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1294 : PLift (G 73548 73554) := ⟨bs [0x47d46a8f1f51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1295 : PLift (G 73554 73598) := ⟨bs [0x11f5837fb1f59,0x47d891f651f63,0x23edc50a91f6f,0x47dd11f771f75,0x47df11f7f1f7d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1296 : PLift (G 73598 73644) := ⟨bs [0x23f0e0aa51f87,0xbfb089ff1f89,0x47e311f8f1f8d,0x47e911fa71fa5,0x47ea91fad1fab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1297 : PLift (G 73644 73700) := ⟨bs [0x47ec91fb51fb3,0x23f90226d1fc9,0x23f9c52731fcf,0x23fa097471fd1,0x47f711fdf1fdd,0x47f891fe51fe3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1298 : PLift (G 73700 73722) := ⟨bs [0x47fb11fef1fed,0x8ffc30371ff9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1299 : PLift (G 73722 73784) := ⟨bs [0x23ffe3e7f1fff,0x2402d27852017,0x48071201f201d,0x480a9202d202b,0x400c7b2d2037] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1300 : PLift (G 73784 73848) := ⟨bs [0x180789611205b,0x240bcca25205f,0x240ec476b2077] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1301 : PLift (G 73848 73884) := ⟨bs [0xc0505e432079,0x4820920852083,0x48229208d208b,0x4825120972095,0x48269209d209b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1302 : PLift (G 73884 73952) := ⟨bs [0x24150e31f20a9,0x482c920b520b3,0x4834920d520d3,0x241ad34cd20d7,0x241bc10ef20df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1303 : PLift (G 73952 73974) := ⟨bs [0x9074eff120e9,0x483d120f720f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1304 : PLift (G 73974 74028) := ⟨bs [0x2421d6413210f,0x121208feb2121,0x4849121272125,0x484a9212d212b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1305 : PLift (G 74028 74072) := ⟨bs [0x2427cc64d213f,0xe76838512143,0xc0e41f592157] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1306 : PLift (G 74072 74144) := ⟨bs [0x181d1ffe9215d,0x485b1216f216d,0x485c921752173,0x485d121772175,0x4864921952193,0x2433d2f1f219f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1307 : PLift (G 74144 74178) := ⟨bs [0x4869121a721a5,0x2435c58a921af,0x24361361321b1,0x2436c75ff21b7,0x24381ae1721c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1308 : PLift (G 74178 74204) := ⟨bs [0x4873121cf21cd,0x1827226e921d5,0x121d88c3921d9,0x4876921dd21db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1309 : PLift (G 74204 74232) := ⟨bs [0x243da47721e1,0x487a921ed21eb,0x73fcc39721f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1310 : PLift (G 74232 74288) := ⟨bs [0x12211e1392211,0x2444cbea52227,0x407dd285222f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1311 : PLift (G 74288 74324) := ⟨bs [0x182f130332235,0x24471077b2239,0x2448e1f272247,0x48931224f224d,0x18319d95d2253] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1312 : PLift (G 74324 74364) := ⟨bs [0x12270df992271,0x489d122772275,0x489e9227d227b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1313 : PLift (G 74364 74412) := ⟨bs [0xc1b1538d2289,0x48a31228f228d,0x2451e29cb228f,0x48aa922ad22ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1314 : PLift (G 74412 74442) := ⟨bs [0x18391919722ad,0x48ac922b522b3,0x122c8cb2922c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1315 : PLift (G 74442 74490) := ⟨bs [0x122d1319b22d1,0x48b5122d722d5,0x245ce355d22e7,0x245f0c27d22f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1316 : PLift (G 74490 74532) := ⟨bs [0x48c29230d230b,0x48c31230f230d,0x3a38e8032319,0xc21588ed231f,0x48c8923252323] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1317 : PLift (G 74532 74598) := ⟨bs [0x2466c2c292337,0x1d21335b2341,0x2468e39d92347,0x48d31234f234d,0x48d69235d235b,0x48d9123672365] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1318 : PLift (G 74598 74612) := ⟨bs [0x91ba12212371,0x48dc923752373] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1319 : PLift (G 74612 74708) := ⟨bs [0x246fe21d1237f,0x48e71239f239d,0x2477c132923bf,0x48f2923cd23cb,0x48f4923d523d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1320 : PLift (G 74708 74720) := ⟨bs [0x123d816a123d9,0x48f7123df23dd,0x40dda03d23df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1321 : PLift (G 74720 74748) := ⟨bs [0x91f5245923e9,0x48fa923ed23eb,0x48fe923fd23fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1322 : PLift (G 74748 74780) := ⟨bs [0x2480d939b2407,0x1240975cd2409,0x4904924152413,0x49069241d241b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1323 : PLift (G 74780 74844) := ⟨bs [0x1859037a5242d,0x185b071212445,0x185b9b205244b,0x2489c37c1244f,0x49169245d245b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1324 : PLift (G 74844 74874) := ⟨bs [0xc2f05c492469,0x491b1246f246d,0x491d124772475,0x248f2048f2479] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1325 : PLift (G 74874 74904) := ⟨bs [0xc30475772487,0x49229248d248b,0x24921876d2491,0x2492d05bd2497] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1326 : PLift (G 74904 74942) := ⟨bs [0x18638fa4b24ab,0x24961ca9724b1,0x492d124b724b5,0xea3244bd24bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1327 : PLift (G 74942 75038) := ⟨bs [0x2499d523324cf,0x12081acb2503,0x4941125072505,0x24a107e712509,0x4945125172515,0x49471251f251d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1328 : PLift (G 75038 75150) := ⟨bs [0x860d8252521,0x24a8e19352547,0x49529254d254b,0x4959125672565,0x495f1257f257d,0x49631258f258d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1329 : PLift (G 75150 75162) := ⟨bs [0x24b30c7452599] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1330 : PLift (G 75162 75168) := ⟨bs [0x53e49b45259f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1331 : PLift (G 75168 75182) := ⟨bs [0x15c0808325a1,0x496b125af25ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1332 : PLift (G 75182 75194) := ⟨bs [0x92ddef9f25b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1333 : PLift (G 75194 75212) := ⟨bs [0x125ca40b725c9,0x4972925cd25cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1334 : PLift (G 75212 75224) := ⟨bs [0x61f0aef525d1,0x24baca82125d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1335 : PLift (G 75224 75278) := ⟨bs [0x4976925dd25db,0x24bcc2a9f25e7,0x497d125f725f5,0x4981126072605,0x49831260f260d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1336 : PLift (G 75278 75324) := ⟨bs [0x12618ff2f2619,0x188394b81262b,0x498e9263d263b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1337 : PLift (G 75324 75330) := ⟨bs [0x932172032641] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1338 : PLift (G 75330 75354) := ⟨bs [0x12648bd392649,0x4994926552653,0x12659953d2659] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1339 : PLift (G 75354 75402) := ⟨bs [0x24ccd04e32667,0x24ce022052671,0x499f1267f267d,0x24cfc0873267f,0x24d108b5f2689] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1340 : PLift (G 75402 75480) := ⟨bs [0x188b8c36f268b,0xfeda0cb268f,0x24d4d38e526a7,0x49ab126af26ad,0x24dadb46926d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1341 : PLift (G 75480 75512) := ⟨bs [0x24ddc920d26ef,0xc4a4b58726f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1342 : PLift (G 75512 75540) := ⟨bs [0x7601f5a92701,0x24e0dcf772707,0x49c31270f270d,0x49c4927152713] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1343 : PLift (G 75540 75542) := ⟨bs [0x49c5127172715] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1344 : PLift (G 75542 75554) := ⟨bs [0x49c901d12721] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1345 : PLift (G 75554 75612) := ⟨bs [0x49c9127272725,0x49cc927352733,0xc4d246012739,0x24e7c4fb1273f,0x49d69275d275b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1346 : PLift (G 75612 75654) := ⟨bs [0x12760906d2761,0x49d8927652763,0x49db1276f276d,0x24ef060c72779,0x49e1127872785] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1347 : PLift (G 75654 75684) := ⟨bs [0x49e29278d278b,0x24f3c1ebd279f,0x49e8927a527a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1348 : PLift (G 75684 75690) := ⟨bs [0x93d621b927a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1349 : PLift (G 75690 75710) := ⟨bs [0xc524de0f27b7,0x49ee927bd27bb,0x49ef127bf27bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1350 : PLift (G 75710 75732) := ⟨bs [0x93e424f127c9,0x49f4927d527d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1351 : PLift (G 75732 75774) := ⟨bs [0x24fbc8f6927df,0x24fed494d27f7,0x49ff127ff27fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1352 : PLift (G 75774 75782) := ⟨bs [0x83922f8f2805] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1353 : PLift (G 75782 75822) := ⟨bs [0x18ab9d1e5280b,0x2502168cd2811,0x4a05128172815,0x4a0b1282f282d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1354 : PLift (G 75822 75854) := ⟨bs [0x1283850e72839,0xa950d573284d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1355 : PLift (G 75854 75932) := ⟨bs [0x4a171285f285d,0x4a1a9286d286b,0x25110b15b2889,0xed4a26bf289b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1356 : PLift (G 75932 75980) := ⟨bs [0x128a0731b28a1,0x4a29128a728a5,0x2517c9cb328bf,0x4a32928cd28cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1357 : PLift (G 75980 76002) := ⟨bs [0x2519d5c3d28cf,0x4a35128d728d5,0x2794a84f28d7,0x4a37128df28dd,0x1f41617528e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1358 : PLift (G 76002 76040) := ⟨bs [0x18bd9652928e3,0x251fcbc9928ff,0xc604f1e72907] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1359 : PLift (G 76040 76100) := ⟨bs [0x2525c5c8d292f,0xc62015672931,0x4a4e9293d293b,0x18c599f732943] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1360 : PLift (G 76100 76104) := ⟨bs [0x2528c2bfd2947] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1361 : PLift (G 76104 76124) := ⟨bs [0x842a0903295b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1362 : PLift (G 76124 76164) := ⟨bs [0x129611a352961,0x4a5c929752973,0x4a5f1297f297d,0x252fcd765297f,0x4a60929852983] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1363 : PLift (G 76164 76244) := ⟨bs [0x2535c476329af,0x2911027129b5,0x2538df35f29c7,0x18d19351929d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1364 : PLift (G 76244 76284) := ⟨bs [0xc691bf5529d9,0x4a77129df29dd,0x4a78929e529e3,0x4a79129e729e5,0x4a7e929fd29fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1365 : PLift (G 76284 76344) := ⟨bs [0x25400fbf12a01,0x2541e3a452a0f,0x18d923f3d2a2d,0x2546dfe2f2a37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1366 : PLift (G 76344 76404) := ⟨bs [0x2549cc8392a4f,0x18dcac8d2a51,0x4a9692a5d2a5b,0x18dd9b2a92a63,0x4a9c92a752a73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1367 : PLift (G 76404 76442) := ⟨bs [0xeed1c5092a85,0xc705cd3d2a87,0x2553143652a99] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1368 : PLift (G 76442 76482) := ⟨bs [0x2555ddbf12aaf,0x2556cfb792ab7,0x12ac0ec352ac1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1369 : PLift (G 76482 76512) := ⟨bs [0x2558dcda72ac7,0x4ab312acf2acd,0x4ab692add2adb,0x255be4d3d2adf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1370 : PLift (G 76512 76542) := ⟨bs [0xc744a5cb2ae7,0x255f0c1c32af9,0x4abf12aff2afd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1371 : PLift (G 76542 76580) := ⟨bs [0xc75591c12aff,0x31d9e4c32b11,0x18ed8f1a12b23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1372 : PLift (G 76580 76632) := ⟨bs [0x18ef193152b35,0x4ace92b3d2b3b,0x2567d17672b3f,0x256ad80b72b57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1373 : PLift (G 76632 76652) := ⟨bs [0x12b695ddd2b69,0xab1879992b6b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1374 : PLift (G 76652 76734) := ⟨bs [0x4ade92b7d2b7b,0x2570058432b81,0x2570da38f2b87,0x25731763b2b99,0x4aeb12baf2bad,0x4aef12bbf2bbd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1375 : PLift (G 76734 76772) := ⟨bs [0x95ea02952bd1,0x4af512bd72bd5,0x4af892be52be3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1376 : PLift (G 76772 76830) := ⟨bs [0x257d0f8272be9,0x4afb12bef2bed,0x2580061ff2c01,0x19019021d2c13,0x4b0712c1f2c1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1377 : PLift (G 76830 76872) := ⟨bs [0x280524c52c1f,0x19030f70b2c25,0x2585c3cef2c2f,0x2588d08692c47] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1378 : PLift (G 76872 76914) := ⟨bs [0x2589028e72c49,0x4b1492c552c53,0x4b1a92c6d2c6b,0x12c71ac792c71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1379 : PLift (G 76914 76964) := ⟨bs [0x258ecf7352c77,0x2591e221b2c8f,0x4b2512c972c95,0x25940908f2ca1,0x190da22372ca3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1380 : PLift (G 76964 77018) := ⟨bs [0x2597c2db52cbf,0x4b3292ccd2ccb,0xc8922c5d2cd9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1381 : PLift (G 77018 77048) := ⟨bs [0xc895dd392cdf,0x4b3912ce72ce5,0x259e24ac92cf1,0x259ed4bcf2cf7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1382 : PLift (G 77048 77102) := ⟨bs [0x4b4312d0f2d0d,0x25a3180fd2d19,0x4b4912d272d25,0xf0f22ed72d2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1383 : PLift (G 77102 77154) := ⟨bs [0xc8e093ef2d51,0xf112125f2d55,0x25ac138652d61] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1384 : PLift (G 77154 77192) := ⟨bs [0xc8f512bd2d6f,0x4b5c92d752d73,0x25b0ddded2d87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1385 : PLift (G 77192 77202) := ⟨bs [0x4b6646fb2d91] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1386 : PLift (G 77202 77238) := ⟨bs [0x4b6712d9f2d9d,0x4b6d12db72db5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1387 : PLift (G 77238 77240) := ⟨bs [0x563512f72db7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1388 : PLift (G 77240 77262) := ⟨bs [0x4b6e92dbd2dbb,0x12dc01ae32dc1,0x4b7312dcf2dcd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1389 : PLift (G 77262 77292) := ⟨bs [0xc93610972dcf,0x4b7492dd52dd3,0x4b7512dd72dd5,0x25bbdd4632ddf,0x4b7a92ded2deb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1390 : PLift (G 77292 77348) := ⟨bs [0x4b8112e072e05,0x4b8292e0d2e0b,0x4b8692e1d2e1b,0x192d81a612e23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1391 : PLift (G 77348 77370) := ⟨bs [0x78de10912e27,0x25c5e0a972e2f,0x25c71d1732e39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1392 : PLift (G 77370 77384) := ⟨bs [0xc980e9452e41,0x25c8c82312e47] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1393 : PLift (G 77384 77448) := ⟨bs [0x12e696fd32e69,0x4b9a92e6d2e6b,0x25ced3b312e77,0x25d0cafb72e87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1394 : PLift (G 77448 77478) := ⟨bs [0x790d8a2d2e9f,0x4ba912ea72ea5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1395 : PLift (G 77478 77480) := ⟨bs [0xc9c574232ea7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1396 : PLift (G 77480 77490) := ⟨bs [0x9759e7452eb1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1397 : PLift (G 77490 77514) := ⟨bs [0xacf806352eb3,0x4bb112ec72ec5,0x25d90e7b72ec9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1398 : PLift (G 77514 77550) := ⟨bs [0x25da0fb152ed1,0xc9e628792ed7,0x25dce1af32ee7,0x4bbb12eef2eed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1399 : PLift (G 77550 77564) := ⟨bs [0x25ddde5832eef,0x193f02bf12ef5,0x4bbe92efd2efb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1400 : PLift (G 77564 77570) := ⟨bs [0x4bc1ee392f01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1401 : PLift (G 77570 77618) := ⟨bs [0x4bc112f072f05,0x4bc492f152f13,0x25e2e11b12f17,0x4bca92f2d2f2b,0x12f3104cf2f31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1402 : PLift (G 77618 77682) := ⟨bs [0x4bcd12f372f35,0x25e901e712f49,0x25e9e01dd2f4f,0x4bd692f5d2f5b,0x25ee2111f2f71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1403 : PLift (G 77682 77712) := ⟨bs [0x25eed14c72f77,0x12f79448b2f79,0x4be092f852f83,0x25f1cfef32f8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1404 : PLift (G 77712 77732) := ⟨bs [0x25f21097d2f91,0x25f2e11fb2f97,0x4be692f9d2f9b,0x4be892fa52fa3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1405 : PLift (G 77732 77744) := ⟨bs [0x56c4e3252faf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1406 : PLift (G 77744 77798) := ⟨bs [0x4bec92fb52fb3,0x25f8259292fc1,0x4bf312fcf2fcd,0x25fac91c92fd7,0x19531c7fd2fe5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1407 : PLift (G 77798 77840) := ⟨bs [0x7990920b2fe9,0x4bfd12ff72ff5,0x2601d2ef9300f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1408 : PLift (G 77840 77864) := ⟨bs [0x980cdaad3019,0x2604c9bd13027] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1409 : PLift (G 77864 77934) := ⟨bs [0x4c0a9302d302b,0x4c11130473045,0x195b90297304b,0x13068c0713069,0x4c1b1306f306d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1410 : PLift (G 77934 77970) := ⟨bs [0x260fde5ed307f,0x130921dd33091] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1411 : PLift (G 77970 77984) := ⟨bs [0x984e1c8f3099,0x2613d93b3309f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1412 : PLift (G 77984 78032) := ⟨bs [0x2615deec130af,0x2616e2f2130b7,0x2618133a530c1,0x2619ce76130cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1413 : PLift (G 78032 78080) := ⟨bs [0x130d83f4530d9,0x32d0b10330e1,0x4c3a930ed30eb,0x261fda52330ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1414 : PLift (G 78080 78102) := ⟨bs [0x4c45131173115] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1415 : PLift (G 78102 78122) := ⟨bs [0x5730936f3129] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1416 : PLift (G 78122 78140) := ⟨bs [0x26271bc8b3139,0x196f9b4bb313b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1417 : PLift (G 78140 78158) := ⟨bs [0x87b153e5314d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1418 : PLift (G 78158 78174) := ⟨bs [0xae7957213153,0x262ad801b3157,0x4c571315f315d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1419 : PLift (G 78174 78230) := ⟨bs [0x4c58931653163,0x262dc2271316f,0xcba23af73171,0x4c5e9317d317b,0x4c65131973195] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1420 : PLift (G 78230 78278) := ⟨bs [0x269345d3199,0x26341ed0131a1,0x4c6c931b531b3,0x197b2421b31c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1421 : PLift (G 78278 78284) := ⟨bs [0x87e8cc4731cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1422 : PLift (G 78284 78302) := ⟨bs [0x87f1a47931dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1423 : PLift (G 78302 78368) := ⟨bs [0x4c78931e531e3,0x263cdb61131e7,0x4c7b131ef31ed,0x4c81132073205,0x4c829320d320b,0x2643e0467321f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1424 : PLift (G 78368 78468) := ⟨bs [0x3d41b15b3241,0x198793f0b325b,0x4c99132673265,0x264cdca293267,0x4ca0932853283] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1425 : PLift (G 78468 78510) := ⟨bs [0x2651e2647328f,0x2652cdfc33297,0x26541c50132a1,0x40900b8932ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1426 : PLift (G 78510 78554) := ⟨bs [0x28e4881732af,0x4cad132b732b5,0x4cb2932cd32cb,0x4cb3132cf32cd,0xcc91948f32d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1427 : PLift (G 78554 78572) := ⟨bs [0x9974dcad32e9,0x4cba932ed32eb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1428 : PLift (G 78572 78584) := ⟨bs [0x265e13f4932f1,0x265ed224132f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1429 : PLift (G 78584 78594) := ⟨bs [0x998034f73301] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1430 : PLift (G 78594 78644) := ⟨bs [0xccb62735330f,0x2663c760b331f,0x1999a333b3333] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1431 : PLift (G 78644 78654) := ⟨bs [0x266718a413339,0xaf914c5b333d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1432 : PLift (G 78654 78698) := ⟨bs [0x199da125d3363,0x99b5a4f13369] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1433 : PLift (G 78698 78722) := ⟨bs [0x4cdc933753373,0x266f259b53379,0x13380e3ad3381] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1434 : PLift (G 78722 78738) := ⟨bs [0x4ce4fb733391] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1435 : PLift (G 78738 78804) := ⟨bs [0x4cee933bd33bb,0x19a51672d33bd,0x4cf0933c533c3,0x2678e548133c7,0x4cf3133cf33cd,0x4cf4933d533d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1436 : PLift (G 78804 78810) := ⟨bs [0x99ec540733d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1437 : PLift (G 78810 78854) := ⟨bs [0xcd46403333e7,0x267ec250133f7,0x19ab239033405] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1438 : PLift (G 78854 78890) := ⟨bs [0x268103e313409,0x4d071341f341d,0x2684c97733427,0x1342811e33429] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1439 : PLift (G 78890 78930) := ⟨bs [0x4d0b1342f342d,0x19af05ce33435,0x2688c91a93447,0x13450c7353451] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1440 : PLift (G 78930 79032) := ⟨bs [0x4d171345f345d,0x26900522b3481,0x19b58d9e13483,0x4d231348f348d,0x2696dbae534b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1441 : PLift (G 79032 79088) := ⟨bs [0x2697da25b34bf,0x4d30934c534c3,0xcde6516734d7,0x269dcc91334ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1442 : PLift (G 79088 79152) := ⟨bs [0x269fdb88334ff,0x26a0e2da93507,0x4d471351f351d,0x4d48935253523,0x4d4a9352d352b,0x26a5cef0d352f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1443 : PLift (G 79152 79188) := ⟨bs [0x26a6211d33531,0x26a6c6aaf3537,0x4d531354f354d,0x9082abd3553] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1444 : PLift (G 79188 79202) := ⟨bs [0x9aaca8af3559,0x3840d9093561] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1445 : PLift (G 79202 79274) := ⟨bs [0x4d5f1357f357d,0x26afdc019357f,0x161df6cf3589,0x4d669359d359b,0x1136691535a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1446 : PLift (G 79274 79334) := ⟨bs [0x26b5d68d135af,0x4d6c935b535b3,0x4d71135c735c5,0x4d73135cf35cd,0x26bac52e735d7,0x25923a2d35e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1447 : PLift (G 79334 79380) := ⟨bs [0x26bd090fb35e9,0x4d7d135f735f5,0x19d509f7935fd,0x26c0c92cd3607,0x4d84936153613] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1448 : PLift (G 79380 79400) := ⟨bs [0xcec1edf13621,0x4d89136273625,0xcec50ce13627] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1449 : PLift (G 79400 79412) := ⟨bs [0x4d8c936353633] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1450 : PLift (G 79412 79424) := ⟨bs [0x58a4b38b363f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1451 : PLift (G 79424 79452) := ⟨bs [0x4d90936453643,0x26c90fba13649,0xb15a02fb365b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1452 : PLift (G 79452 79532) := ⟨bs [0x26cf049913679,0xb17172133685,0x4daa936ad36ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1453 : PLift (G 79532 79560) := ⟨bs [0x136b181e536b1,0x4daf136bf36bd,0x26d8e500936c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1454 : PLift (G 79560 79562) := ⟨bs [0xcf30c59336c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1455 : PLift (G 79562 79580) := ⟨bs [0x8a28145d36db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1456 : PLift (G 79580 79610) := ⟨bs [0x4db9136e736e5,0x136f1944d36f1,0x136f8567b36f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1457 : PLift (G 79610 79634) := ⟨bs [0x4dbf136ff36fd,0x4dc1137073705,0x19eb875df370b,0x26e1d58a9370f,0x26e2080433711] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1458 : PLift (G 79634 79658) := ⟨bs [0x26e507a493729] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1459 : PLift (G 79658 79670) := ⟨bs [0x8a50614d3735] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1460 : PLift (G 79670 79688) := ⟨bs [0xcf8642e13747] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1461 : PLift (G 79688 79692) := ⟨bs [0x5fc9e88f374b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1462 : PLift (G 79692 79694) := ⟨bs [0x19f1129fb374d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1463 : PLift (G 79694 79698) := ⟨bs [0x4dd4ab493751] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1464 : PLift (G 79698 79770) := ⟨bs [0x4dd4937553753,0x4de31378f378d,0x9bcd3c6b3799] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1465 : PLift (G 79770 79814) := ⟨bs [0x26f4008b137a1,0x137b847eb37b9,0x4df0937c537c3,0x4df1137c737c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1466 : PLift (G 79814 79830) := ⟨bs [0x137c9b4d137c9,0x26f9dba5d37cf,0x4df5137d737d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1467 : PLift (G 79830 79844) := ⟨bs [0x9bf005b737e1,0x4df8937e537e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1468 : PLift (G 79844 79874) := ⟨bs [0x26fccc66337e7,0x4dfd137f737f5,0x4dfe937fd37fb,0x270012bf73801] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1469 : PLift (G 79874 79890) := ⟨bs [0x4e05736d3811] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1470 : PLift (G 79890 79908) := ⟨bs [0x4e071381f381d,0x33e0bd7381f,0x4e08938253823] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1471 : PLift (G 79908 79940) := ⟨bs [0x8ac97a993843] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1472 : PLift (G 79940 79998) := ⟨bs [0x2708d5a853847,0x270bdc70b385f,0x4e19138673865,0x4e1a9386d386b,0x4e1c938753873,0x4e1f1387f387d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1473 : PLift (G 79998 80078) := ⟨bs [0x270fe6f6f387f,0x4e25138973895,0x2714cbbd138a7,0x4e2c938b538b3,0x2718c67e538c7,0x4e33138cf38cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1474 : PLift (G 80078 80148) := ⟨bs [0x4e3a938ed38eb,0x7d2c350538ef,0x4e431390f390d,0x4e44939153913] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1475 : PLift (G 80148 80154) := ⟨bs [0x1a170a9453915,0x9c8c017f3919] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1476 : PLift (G 80154 80174) := ⟨bs [0x2724e2e2f3927,0x49b01523392d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1477 : PLift (G 80174 80178) := ⟨bs [0x4e4cc1673931] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1478 : PLift (G 80178 80232) := ⟨bs [0xb662bb3393f,0x2729de9ef394f,0x272a092a13951,0x4e571395f395d,0x272cc648d3967] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1479 : PLift (G 80232 80252) := ⟨bs [0xd0f1ee393969,0x272dda79b396f,0x4e5e9397d397b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1480 : PLift (G 80252 80264) := ⟨bs [0x59945c953987] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1481 : PLift (G 80264 80310) := ⟨bs [0x13990b8673991,0x2732ce17d3997,0x2733c771f399f,0x4e6d139b739b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1482 : PLift (G 80310 80370) := ⟨bs [0x4e6f139bf39bd,0x27390b93739c9,0x4e75139d739d5,0x4e76939dd39db,0x4e7a939ed39eb,0x273e019c939f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1483 : PLift (G 80370 80448) := ⟨bs [0x4e8093a053a03,0x2742d470f3a17,0x4e8b13a2f3a2d,0x2747d11bd3a3f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1484 : PLift (G 80448 80472) := ⟨bs [0x68c26b033a41,0x305de5dd3a57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1485 : PLift (G 80472 80528) := ⟨bs [0x274b0d4133a59,0x274d1ce333a69,0x4e9a93a6d3a6b,0x9409cc73a81,0x2751e17493a8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1486 : PLift (G 80528 80612) := ⟨bs [0x27531e5ef3a99,0x4eab13aaf3aad,0x2756e277d3ab7,0x1dfd75c33ad7,0x4eb693add3adb,0x4eb893ae53ae3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1487 : PLift (G 80612 80670) := ⟨bs [0x4ebb13aef3aed,0x4ebc93af53af3,0x4ebd13af73af5,0x4ec293b0d3b0b,0x2762240dd3b11,0x4ec713b1f3b1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1488 : PLift (G 80670 80688) := ⟨bs [0x2763deb4f3b1f,0x4ec913b273b25,0x2765072773b29,0x1a4390ca53b2b,0x2765cce773b2f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1489 : PLift (G 80688 80750) := ⟨bs [0x4ecf13b3f3b3d,0x27690d8d53b49,0x276c1dcf53b61,0x4eda93b6d3b6b,0x4edb13b6f3b6d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1490 : PLift (G 80750 80784) := ⟨bs [0x13b79ddc13b79,0x27710fcbf3b89,0x4ee293b8d3b8b,0x2771cb3133b8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1491 : PLift (G 80784 80810) := ⟨bs [0x4ee513b973b95,0x4ee893ba53ba3,0x9dd676bb3ba9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1492 : PLift (G 80810 80850) := ⟨bs [0x4eec93bb53bb3,0x2777e50cd3bbf,0xd28144753bc1,0x277a168033bd1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1493 : PLift (G 80850 80918) := ⟨bs [0x277bd10ab3bdf,0x2780113893c01,0x4f0313c0f3c0d,0x2781cde753c0f,0x1a570a1bd3c15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1494 : PLift (G 80918 80954) := ⟨bs [0x4f0693c1d3c1b,0x4662be53c21,0x4f0913c273c25,0x27870aa813c39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1495 : PLift (G 80954 81002) := ⟨bs [0xb4b91d453c43,0x4f1713c5f3c5d,0x1fa482653c69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1496 : PLift (G 81002 81032) := ⟨bs [0x1a5f129353c75,0x278f1489b3c79,0x4f1e93c7d3c7b,0x278fd28553c7f,0x2790c28fb3c87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1497 : PLift (G 81032 81048) := ⟨bs [0x13c907a033c91,0x1a6181c693c93,0x2792c067d3c97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1498 : PLift (G 81048 81072) := ⟨bs [0x9e4d8e233c99,0x2795d18873caf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1499 : PLift (G 81072 81132) := ⟨bs [0x4f2d13cb73cb5,0x4f2e93cbd3cbb,0x27991b3b93cc9,0x4f3313ccf3ccd,0x279bd237b3cdf,0x4f3a93ced3ceb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1500 : PLift (G 81132 81198) := ⟨bs [0x1a6b0966b3d05,0x4f4293d0d3d0b,0x4f4513d173d15,0xfdb003113d1d,0x4f4b13d2f3d2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1501 : PLift (G 81198 81240) := ⟨bs [0x27a5e23733d2f,0x4f4c93d353d33,0x27a8d3e653d47,0x27aa173653d51,0x27aad92ab3d57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1502 : PLift (G 81240 81332) := ⟨bs [0x27b0174993d81,0x4f6093d853d83,0x4f6313d8f3d8d,0x4f6493d953d93,0x4f6693d9d3d9b,0x1a798d27d3db3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1503 : PLift (G 81332 81374) := ⟨bs [0x27b7d643b3dbf,0x4f7113dc73dc5,0x27b911d0f3dc9,0x27b9c3bc73dcf,0x4f7693ddd3ddb,0x4f7713ddf3ddd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1504 : PLift (G 81374 81410) := ⟨bs [0x27bf14c613df9,0x9f01b5e73e01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1505 : PLift (G 81410 81458) := ⟨bs [0x1a8111a913e0d,0x27c3e4b6d3e1f,0x27c60cd573e31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1506 : PLift (G 81458 81528) := ⟨bs [0xd425b12f3e37,0x4f9913e673e65,0x4f9b13e6f3e6d,0x27cee35fd3e77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1507 : PLift (G 81528 81548) := ⟨bs [0x73d0fd753e7d,0x1a8b93cf33e8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1508 : PLift (G 81548 81552) := ⟨bs [0x27d1d36c13e8f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1509 : PLift (G 81552 81554) := ⟨bs [0x4fa4904f3e91] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1510 : PLift (G 81554 81630) := ⟨bs [0x27d2d6c553e97,0x4fa693e9d3e9b,0x27d410ee53ea1,0x4fb293ecd3ecb,0x1a918b8b33ed3,0x4fb713edf3edd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1511 : PLift (G 81630 81650) := ⟨bs [0x4fb913ee73ee5,0x27ddc97233eef,0x13ef159cb3ef1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1512 : PLift (G 81650 81668) := ⟨bs [0x8dc995fd3f03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1513 : PLift (G 81668 81678) := ⟨bs [0x27e0c86dd3f07,0xb651e68d3f0d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1514 : PLift (G 81678 81702) := ⟨bs [0x9f8e39913f19,0x4fc913f273f25] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1515 : PLift (G 81702 81738) := ⟨bs [0x27e4d845b3f27,0x4fca93f2d3f2b,0xd4d650873f3f,0x27e9242ff3f49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1516 : PLift (G 81738 81774) := ⟨bs [0x4fd513f573f55,0x27ec182773f61,0x13f6873a33f69,0x4fdb13f6f3f6d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1517 : PLift (G 81774 81840) := ⟨bs [0x27f0d315b3f87,0x3545aefd3f99,0x27f5e744f3faf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1518 : PLift (G 81840 81884) := ⟨bs [0xd526113b3fb7,0x1aa526c4f3fbd,0x4ff313fcf3fcd,0x1aa7908213fdb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1519 : PLift (G 81884 81932) := ⟨bs [0x4ffa93fed3feb,0x4ffb13fef3fed,0x27ffc95693fff,0x21b0de554009,0x1aaba1cc5400b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1520 : PLift (G 81932 81938) := ⟨bs [0x355840f74011] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1521 : PLift (G 81938 81944) := ⟨bs [0x5b75ec174017] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1522 : PLift (G 81944 82004) := ⟨bs [0x14020138f4021,0x2805e0609402f,0x500c940354033,0x500d140374035,0x5014940554053] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1523 : PLift (G 82004 82014) := ⟨bs [0x280ae49b94057,0x4730fa594059,0xb7106551405d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1524 : PLift (G 82014 82022) := ⟨bs [0x557177b94065] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1525 : PLift (G 82022 82068) := ⟨bs [0x280dc1891406f,0x501d140774075,0xd5a5bd754077,0x5020940854083,0x5024940954093] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1526 : PLift (G 82068 82130) := ⟨bs [0x1409863f14099,0xae06a6d40d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1527 : PLift (G 82130 82142) := ⟨bs [0xb75a240d40db,0x1abd1d49d40dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1528 : PLift (G 82142 82172) := ⟨bs [0xa0747b1b40e9,0x503c940f540f3,0x503e940fd40fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1529 : PLift (G 82172 82194) := ⟨bs [0xd6062fc14107,0x2f91b7e5410d,0x28222576f4111] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1530 : PLift (G 82194 82224) := ⟨bs [0x2823e5e71411f,0x141294abd4129,0x504a9412d412b,0x2825c0689412f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1531 : PLift (G 82224 82238) := ⟨bs [0x2ad5f1934137,0x1ac508caf413d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1532 : PLift (G 82238 82242) := ⟨bs [0x808148d74141] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1533 : PLift (G 82242 82340) := ⟨bs [0x1ac7110c14155,0x50569415d415b,0x282cc27cf4167,0x505f1417f417d,0x5060941854183,0x5068941a541a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1534 : PLift (G 82340 82362) := ⟨bs [0xb7d22d6141ad,0x477e01d741af,0x28371e20741b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1535 : PLift (G 82362 82458) := ⟨bs [0x5071141c741c5,0x5074941d541d3,0x141d930b541d9,0x507d141f741f5,0x284309bc34219] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1536 : PLift (G 82458 82484) := ⟨bs [0x2843c6217421f,0x5089142274225,0xd6c42abf4227,0x508c942354233] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1537 : PLift (G 82484 82508) := ⟨bs [0x2846e4d734237,0x508f1423f423d,0x43da1df74243,0x50929424d424b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1538 : PLift (G 82508 82560) := ⟨bs [0x142616f734261,0x24da5e6f4263,0x509d142774275,0x284fe51d5427f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1539 : PLift (G 82560 82568) := ⟨bs [0x285010e5b4281,0xd705b1774287] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1540 : PLift (G 82568 82572) := ⟨bs [0x10209ba13428b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1541 : PLift (G 82572 82592) := ⟨bs [0xd7156e2f429f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1542 : PLift (G 82592 82602) := ⟨bs [0x5c30c0d542a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1543 : PLift (G 82602 82620) := ⟨bs [0x28560b48b42b1,0x50ad142b742b5,0x50ae942bd42bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1544 : PLift (G 82620 82652) := ⟨bs [0x6b98294342c9,0x50b6942dd42db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1545 : PLift (G 82652 82728) := ⟨bs [0x35d22f2542e1,0x1aeb8db8f430b,0x815093b4321,0x50c8943254323,0x2864c51894327] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1546 : PLift (G 82728 82782) := ⟨bs [0x28652199d4329,0x50d1143474345,0xd784cccb4347,0x50d29434d434b,0x50d71435f435d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1547 : PLift (G 82782 82838) := ⟨bs [0x50d8943654363,0x286d1bae94369,0x286de31d1436f,0x50de9437d437b,0x50df1437f437d,0x50e5143974395] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1548 : PLift (G 82838 82884) := ⟨bs [0x2873dcc4d439f,0x50f0943c543c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1549 : PLift (G 82884 82892) := ⟨bs [0xa1e5f42d43c9,0x50f2943cd43cb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1550 : PLift (G 82892 82940) := ⟨bs [0x287ad5a9743d7,0x287c0249743e1,0x50fe943fd43fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1551 : PLift (G 82940 82964) := ⟨bs [0x90081bc94413] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1552 : PLift (G 82964 83004) := ⟨bs [0x5109144274425,0x510d144374435,0x510e9443d443b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1553 : PLift (G 83004 83010) := ⟨bs [0x5111d67d4441] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1554 : PLift (G 83010 83060) := ⟨bs [0xd8363c9f444f,0xd8465f674467,0x511c944754473] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1555 : PLift (G 83060 83078) := ⟨bs [0x288ecf9b74477,0x31ec6cd7447f,0x1e32096b4485] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1556 : PLift (G 83078 83090) := ⟨bs [0x51252ed34491] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1557 : PLift (G 83090 83138) := ⟨bs [0x5125144974495,0x51271449f449d,0x512b144af44ad,0x144c2523144c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1558 : PLift (G 83138 83204) := ⟨bs [0xa274196d44e9,0x5140945054503] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1559 : PLift (G 83204 83232) := ⟨bs [0x28a0d865b4507,0x5144945154513,0x1b17136174515,0x1b1799903451b,0x28a3e88a7451f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1560 : PLift (G 83232 83274) := ⟨bs [0x3630c5df4521,0x514a9452d452b,0x28a71847f4539,0x5150945454543,0x5151145474545,0x28a9217854549] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1561 : PLift (G 83274 83384) := ⟨bs [0x5158945654563,0x28addc9bd456f,0x51629458d458b,0x1b211e071458d,0x51671459f459d,0x28b6e5bdf45b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1562 : PLift (G 83384 83400) := ⟨bs [0x516f145bf45bd,0x28b8cfb4945c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1563 : PLift (G 83400 83402) := ⟨bs [0x82525e7145c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1564 : PLift (G 83402 83424) := ⟨bs [0x28b9cdb6745cf,0x145d8c9fd45d9,0x28bbc8bd345df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1565 : PLift (G 83424 83444) := ⟨bs [0x28bcdfc7545e7,0x517b145ef45ed,0x517c945f545f3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1566 : PLift (G 83444 83460) := ⟨bs [0xa2fcace545f9,0x5180946054603] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1567 : PLift (G 83460 83558) := ⟨bs [0x28c1e4aaf460f,0x5185146174615,0x28c514de74629,0x1c6121ff4651,0x5199146674665] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1568 : PLift (G 83558 83562) := ⟨bs [0x8290fdf34669] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1569 : PLift (G 83562 83610) := ⟨bs [0x519a9466d466b,0x519e9467d467b,0x28d0ddea14687,0x51a31468f468d,0x28d324f114699] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1570 : PLift (G 83610 83640) := ⟨bs [0xd9c0c37146a1,0x51a9146a746a5,0x28d6d7e1346b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1571 : PLift (G 83640 83664) := ⟨bs [0xd9d109db46b9,0x1b3b0437146c5,0x28d9e65bd46cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1572 : PLift (G 83664 83720) := ⟨bs [0x28dd19d0746e9,0x1b3f1e44d46f5,0x51c1147074705,0x28e0cf6d94707] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1573 : PLift (G 83720 83738) := ⟨bs [0x1471935dd4719] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1574 : PLift (G 83738 83774) := ⟨bs [0xa3990ac14731,0x1b4517b8d473d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1575 : PLift (G 83774 83814) := ⟨bs [0x147677774741,0x63c1fd3474f,0x51d9147674765] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1576 : PLift (G 83814 83844) := ⟨bs [0x6d29ea294779,0x51e0947854783] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1577 : PLift (G 83844 83892) := ⟨bs [0x147927c494791,0x2d3035a5479d,0x28f41be4747a1,0x51ec947b547b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1578 : PLift (G 83892 83940) := ⟨bs [0x28f7e452547bf,0x28f8dfb9547c7,0x28fa16cb747d1,0x51f7147df47dd,0x51f8947e547e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1579 : PLift (G 83940 83988) := ⟨bs [0x1480257454801,0xdab5bcb3480f,0x5204948154813] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1580 : PLift (G 83988 84018) := ⟨bs [0x10689e033482b,0x29061f0414831] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1581 : PLift (G 84018 84090) := ⟨bs [0x2909e0289484f,0x5215148574855,0x52169485d485b,0x1b5d0992b485d,0x5218948654863,0x290f073554879] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1582 : PLift (G 84090 84138) := ⟨bs [0x29132617b4899,0xdb15d47f489f,0x5228948a548a3,0x29151fe4348a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1583 : PLift (G 84138 84192) := ⟨bs [0x2915c615548af,0x5230948c548c3,0x5234948d548d3,0x5235148d748d5,0x291bc8ab348df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1584 : PLift (G 84192 84224) := ⟨bs [0xdb449d5148e7,0x1b698832b48f3,0x523f148ff48fd,0x291fcba8948ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1585 : PLift (G 84224 84300) := ⟨bs [0x5241149074905,0x3bd63d45490f,0x2922e5d774917,0x2924dae134927,0x52529494d494b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1586 : PLift (G 84300 84350) := ⟨bs [0x1b7190fcd4953,0x24993acf4959,0x52571495f495d,0x292bd7a77495f,0x525e9497d497b,0x525f1497f497d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1587 : PLift (G 84350 84392) := ⟨bs [0x293323c9f4999,0x5269149a749a5,0x2934e3dcd49a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1588 : PLift (G 84392 84402) := ⟨bs [0xa4d92b4149b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1589 : PLift (G 84402 84408) := ⟨bs [0x5e36683f49b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1590 : PLift (G 84408 84450) := ⟨bs [0x5271149c749c5,0x2939cfb5d49cf,0x5275149d749d5,0x5276949dd49db,0x149e0d2e549e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1591 : PLift (G 84450 84482) := ⟨bs [0x49523b3f49e9,0x293dc18d349ef,0x527c949f549f3,0x14a0178b34a01] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1592 : PLift (G 84482 84510) := ⟨bs [0x528494a154a13,0x2942c3ab94a17,0x528714a1f4a1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1593 : PLift (G 84510 84534) := ⟨bs [0xa5161b7b4a29,0x528a94a2d4a2b,0x528d14a374a35] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1594 : PLift (G 84534 84552) := ⟨bs [0x841cd6a14a47] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1595 : PLift (G 84552 84632) := ⟨bs [0x2949ceb454a4f,0x529b14a6f4a6d,0x52a514a974a95,0x2952e534b4a97] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1596 : PLift (G 84632 84692) := ⟨bs [0x14aa9d5e94aa9,0x52ab14aaf4aad,0x52ac94ab54ab3,0x1260ff7b4ac1,0x52b494ad54ad3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1597 : PLift (G 84692 84720) := ⟨bs [0xdc91ccd74ad9,0x52b714adf4add,0x295d278a94ae9,0x295dcbeaf4aef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1598 : PLift (G 84720 84788) := ⟨bs [0x52be94afd4afb,0x296016afd4b01,0x2961e1d974b0f,0x29632553f4b19,0x52cc94b354b33] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1599 : PLift (G 84788 84810) := ⟨bs [0x6e69d94b4b39,0x2969081194b49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1600 : PLift (G 84810 84812) := ⟨bs [0x585908a74b4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1601 : PLift (G 84812 84860) := ⟨bs [0x52d694b5d4b5b,0x14b7a29274b79,0x52de94b7d4b7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1602 : PLift (G 84860 84872) := ⟨bs [0xbd727a274b85,0x2970e95734b87] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1603 : PLift (G 84872 84962) := ⟨bs [0x14bb019a14bb1,0x2976ca45b4bb7,0x52f494bd54bd3,0x762423f4be1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1604 : PLift (G 84962 84992) := ⟨bs [0x297cc0fdd4be7,0x297e1a9574bf1,0x52fc94bf54bf3,0xdd5548d74bff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1605 : PLift (G 84992 85062) := ⟨bs [0x7e9ed974c11,0x1bad279fb4c1d,0x530894c254c23,0x530b14c2f4c2d,0x29872668f4c39,0x531114c474c45] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1606 : PLift (G 85062 85094) := ⟨bs [0x298b118cd4c59,0xdd967e2b4c5f,0x13d8ce714c63,0x531914c674c65] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1607 : PLift (G 85094 85148) := ⟨bs [0x298dd37074c6f,0x531d14c774c75,0x14c813b354c81,0x532314c8f4c8d,0x532694c9d4c9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1608 : PLift (G 85148 85200) := ⟨bs [0x2994c47f94ca7,0x29990799f4cc9,0x2999d45834ccf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1609 : PLift (G 85200 85224) := ⟨bs [0xdde143894cd1,0x1bbd0d90b4cdd,0x299ce4e034ce7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1610 : PLift (G 85224 85244) := ⟨bs [0x7910b3074ced,0x533d14cf74cf5,0x1bbf96a234cfb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1611 : PLift (G 85244 85304) := ⟨bs [0x299fd5dcd4cff,0x534294d0d4d0b,0xde215ea54d31,0x29a6def054d37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1612 : PLift (G 85304 85334) := ⟨bs [0x29a8019df4d41,0x535494d554d53,0x1bc7019014d55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1613 : PLift (G 85334 85364) := ⟨bs [0xa6b84c234d71,0x1bc998aeb4d73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1614 : PLift (G 85364 85382) := ⟨bs [0xa6bd97e34d79,0x1bcb274e54d85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1615 : PLift (G 85382 85440) := ⟨bs [0x536894da54da3,0x536c94db54db3,0x3171c4794db5,0x29b7c65174dbf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1616 : PLift (G 85440 85470) := ⟨bs [0xde855b694dc7,0x537294dcd4dcb,0x537314dcf4dcd,0x3a11452b4ddd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1617 : PLift (G 85470 85524) := ⟨bs [0x29bdce00d4def,0xdeb085554e09,0x538314e0f4e0d,0x538494e154e13] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1618 : PLift (G 85524 85572) := ⟨bs [0x10b48ee254e1b,0x538b14e2f4e2d,0x539094e454e43] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1619 : PLift (G 85572 85598) := ⟨bs [0xa72625474e49,0x539714e5f4e5d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1620 : PLift (G 85598 85608) := ⟨bs [0x29cc296194e61,0x29cce41814e67] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1621 : PLift (G 85608 85620) := ⟨bs [0x66ea2e014e73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1622 : PLift (G 85620 85668) := ⟨bs [0x1bdf1662d4e75,0x539e94e7d4e7b,0x29d0e8f3f4e87,0x53a294e8d4e8b,0x53a714e9f4e9d,0x2e289def4ea3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1623 : PLift (G 85668 85734) := ⟨bs [0x53a914ea74ea5,0x53ae94ebd4ebb,0x29d8ca3794ec7,0x29d9dd0d94ecf,0x53b514ed74ed5,0x53b914ee74ee5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1624 : PLift (G 85734 85752) := ⟨bs [0x5fb661a34ef7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1625 : PLift (G 85752 85832) := ⟨bs [0x53c514f174f15,0x29e42637f4f21,0x29e71a2bf4f39,0x53ce94f3d4f3b,0x53d114f474f45,0x29e8e2e6b4f47] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1626 : PLift (G 85832 85890) := ⟨bs [0x53d314f4f4f4d,0x1bf1a09294f53,0x29ead507d4f57,0x53d714f5f4f5d,0x29f006bad4f81] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1627 : PLift (G 85890 85932) := ⟨bs [0x29f1d273b4f8f,0x53e514f974f95,0x53ea94fad4fab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1628 : PLift (G 85932 85934) := ⟨bs [0xbfd23f9d4fad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1629 : PLift (G 85934 85992) := ⟨bs [0x865e7af14fe7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1630 : PLift (G 85992 86070) := ⟨bs [0x29fdd41674fef,0x1bff977754ffb,0x2a00024a15001,0x54029500d500b,0x54031500f500d,0x540d150375035] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1631 : PLift (G 86070 86078) := ⟨bs [0x95729477503d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1632 : PLift (G 86078 86084) := ⟨bs [0x5410950455043] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1633 : PLift (G 86084 86112) := ⟨bs [0x868e2dc9505f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1634 : PLift (G 86112 86138) := ⟨bs [0x1d633135061,0x5419150675065,0x541c950755073,0x2a0f15a235079] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1635 : PLift (G 86138 86144) := ⟨bs [0xe05491bf507f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1636 : PLift (G 86144 86162) := ⟨bs [0x54257bc35091] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1637 : PLift (G 86162 86202) := ⟨bs [0x118000f509b,0x5428950a550a3,0x2a14c23cb50a7,0x542d150b750b5,0x4359dead50b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1638 : PLift (G 86202 86258) := ⟨bs [0x2a1804cc150c1,0x2a1be526350df,0x5438950e550e3,0x2a1d2150d50e9,0x2571012f50f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1639 : PLift (G 86258 86292) := ⟨bs [0x2a1edd6cf50f7,0x22911e5f50fd,0xe0b59543510f,0x5444951155113] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1640 : PLift (G 86292 86298) := ⟨bs [0x5445151175115,0xa88c37735119] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1641 : PLift (G 86298 86312) := ⟨bs [0x86de4d0f5127] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1642 : PLift (G 86312 86358) := ⟨bs [0x544c951355133,0x5451151475145,0x2a29dd6a1514f,0xe0e286f75151,0x5455151575155] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1643 : PLift (G 86358 86372) := ⟨bs [0x2a2c050b55161,0x10dea133f5163] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1644 : PLift (G 86372 86424) := ⟨bs [0x26910aed516d,0x545d151775175,0x2a2fe2ee3517f,0x54631518f518d,0x2a32d65e95197] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1645 : PLift (G 86424 86462) := ⟨bs [0xa8d52fc551a9,0x546d151b751b5,0x546f151bf51bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1646 : PLift (G 86462 86532) := ⟨bs [0x5470951c551c3,0x5473151cf51cd,0x5476951dd51db,0x5479151e751e5,0x1c292220951ed,0x5480952055203] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1647 : PLift (G 86532 86588) := ⟨bs [0x5481152075205,0x1c2b994ef520b,0x10ea67715221,0x548b1522f522d,0x548c952355233,0x1c2f911bb523b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1648 : PLift (G 86588 86694) := ⟨bs [0x2a48c5dcd5247,0x5498952655263,0x5499152675265,0x54a5152975295,0x2a542335f52a1,0x54a9152a752a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1649 : PLift (G 86694 86744) := ⟨bs [0x2a56c2ce152b7,0x2a57c67e752bf,0x2a590925352c9,0x2a5aea16152d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1650 : PLift (G 86744 86768) := ⟨bs [0xa9710ae952e1,0x2a5ddf31352ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1651 : PLift (G 86768 86814) := ⟨bs [0x10f28f4d552f3,0x2a5fe0c0352ff,0x54c71531f531d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1652 : PLift (G 86814 86870) := ⟨bs [0x54cd153375335,0x54ce9533d533b,0x54d0953455343,0x388dbae35349,0x54d31534f534d,0x54d5153575355] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1653 : PLift (G 86870 86924) := ⟨bs [0x54e29538d538b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1654 : PLift (G 86924 86928) := ⟨bs [0x6104e151538f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1655 : PLift (G 86928 86940) := ⟨bs [0x2a720d5eb5391,0x54e69539d539b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1656 : PLift (G 86940 86952) := ⟨bs [0x87dc96cd53a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1657 : PLift (G 86952 87012) := ⟨bs [0x2a75dc05753af,0x2a770d94153b9,0x54f1153c753c5,0x2a7a2526553d1,0x54f8953e553e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1658 : PLift (G 87012 87014) := ⟨bs [0x9711522153e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1659 : PLift (G 87014 87042) := ⟨bs [0x54ff153ff53fd,0x2a8003e375401] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1660 : PLift (G 87042 87072) := ⟨bs [0xaa04c7c35409,0x2a83d1391541f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1661 : PLift (G 87072 87120) := ⟨bs [0x550a9542d542b,0x2a87df1a7543f,0x5510954455443,0x2a89e2963544f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1662 : PLift (G 87120 87122) := ⟨bs [0x8821f4d55451] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1663 : PLift (G 87122 87182) := ⟨bs [0x1c5d00bdf545d,0x551b1546f546d,0xe2f4e7f3546f,0x55229548d548b,0x55231548f548d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1664 : PLift (G 87182 87212) := ⟨bs [0x7bd82b755493,0xd99d2354ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1665 : PLift (G 87212 87254) := ⟨bs [0x1bd1670554b5,0xe3250a9f54b7,0x5534954d554d3,0x5535154d754d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1666 : PLift (G 87254 87282) := ⟨bs [0x2a9b241af54d9,0xc2d1a38d54ed,0x110d897b54f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1667 : PLift (G 87282 87324) := ⟨bs [0x553f154ff54fd,0x5540955055503,0x1551042355511,0x5545155175515,0x55469551d551b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1668 : PLift (G 87324 87408) := ⟨bs [0x2aa5199b95529,0x2aa7c2f21553f,0x2aaac9f9d5557,0x555a9556d556b,0x2aadd6f2f556f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1669 : PLift (G 87408 87428) := ⟨bs [0x9b09093557d,0x5560955855583] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1670 : PLift (G 87428 87444) := ⟨bs [0x71d97ef55589,0x5564955955593] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1671 : PLift (G 87444 87474) := ⟨bs [0x61a06abf55b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1672 : PLift (G 87474 87518) := ⟨bs [0xe3d25f7555b9,0x5570955c555c3,0x5575155d755d5,0x2abacc01955d7,0x5577155df55dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1673 : PLift (G 87518 87548) := ⟨bs [0x5578955e555e3,0x557c955f555f3,0x1119122a955f5,0x557e955fd55fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1674 : PLift (G 87548 87558) := ⟨bs [0x1560034d35601,0xc3704b415605] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1675 : PLift (G 87558 87614) := ⟨bs [0xe4062eb75607,0x2ac3ca989561f,0x5588956255623,0x5589156275625,0x558f1563f563d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1676 : PLift (G 87614 87642) := ⟨bs [0x2ac8d71795647,0x55931564f564d,0xe436564d564f,0x223d0ed35659] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1677 : PLift (G 87642 87672) := ⟨bs [0x1c878af03565b,0xe44238595661,0x2acee35e35677] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1678 : PLift (G 87672 87692) := ⟨bs [0x2acfe9e75567f,0x55a0956855683,0x11208e01d568b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1679 : PLift (G 87692 87702) := ⟨bs [0x7231d06d5691,0x55a5156975695] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1680 : PLift (G 87702 87740) := ⟨bs [0x2ad4e13bf56a7,0xe4715dc556a9,0x1c8f9518d56bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1681 : PLift (G 87740 87798) := ⟨bs [0x2ad7d9e6356bf,0x2ad8e5f6756c7,0x2adad0b7b56d7,0x2ade15c7f56f1,0x55bd156f756f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1682 : PLift (G 87798 87804) := ⟨bs [0x69887cdd56fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1683 : PLift (G 87804 87854) := ⟨bs [0x55c0957055703,0xab8c439b5719,0x55cb1572f572d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1684 : PLift (G 87854 87888) := ⟨bs [0x55cf1573f573d,0x55d1157475745,0x2ae90c22b5749,0x2ae9dc1b5574f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1685 : PLift (G 87888 87912) := ⟨bs [0x895c33895767] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1686 : PLift (G 87912 87960) := ⟨bs [0x55db1576f576d,0x1c9fa5f59577b,0xe504338f5787,0x2af2dedb95797] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1687 : PLift (G 87960 87974) := ⟨bs [0xabcd0c955799,0x55e9157a757a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1688 : PLift (G 87974 87992) := ⟨bs [0xabd4ea7957a9,0x2af6c1ce757b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1689 : PLift (G 87992 88070) := ⟨bs [0x2af81258757c1,0x55f0957c557c3,0x2af8c045757c7,0x55f4957d557d3,0x55f9157e757e5,0x5601158075805] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1690 : PLift (G 88070 88118) := ⟨bs [0x2b01d7731580f,0x56071581f581d,0xc4b01caf5835] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1691 : PLift (G 88118 88170) := ⟨bs [0x264223b75841,0x15868523f5869] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1692 : PLift (G 88170 88178) := ⟨bs [0x561e39135871] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1693 : PLift (G 88178 88260) := ⟨bs [0x5624958955893,0x2b13c3f47589f,0x562b158af58ad,0x158b094b758b1,0x5630958c558c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1694 : PLift (G 88260 88322) := ⟨bs [0x5631158c758c5,0x2b1c26ab958e1,0x563b158ef58ed,0x2b20089235901] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1695 : PLift (G 88322 88328) := ⟨bs [0xe6046e115907] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1696 : PLift (G 88328 88338) := ⟨bs [0x5645c94b5911] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1697 : PLift (G 88338 88428) := ⟨bs [0x1cc18fa5f5913,0x564e9593d593b,0x56531594f594d,0x56569595d595b,0x2b2cdad2d5967,0x565a9596d596b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1698 : PLift (G 88428 88514) := ⟨bs [0x2b31c81f9598f,0x5665159975995,0x2b32c39175997,0x566b159af59ad,0x566c959b559b3,0x2b3805a2159c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1699 : PLift (G 88514 88610) := ⟨bs [0x5672959cd59cb,0x5678959e559e3,0x568315a0f5a0d,0x2e2699795a0f,0x2b43d68e15a1f,0x2b44196ad5a21] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1700 : PLift (G 88610 88652) := ⟨bs [0x569095a455a43,0x1cdba6ef35a4b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1701 : PLift (G 88652 88662) := ⟨bs [0x7371cf5d5a51,0x569515a575a55] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1702 : PLift (G 88662 88668) := ⟨bs [0xe6e6ac275a57,0x569695a5d5a5b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1703 : PLift (G 88668 88682) := ⟨bs [0xad34b4d15a69] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1704 : PLift (G 88682 88722) := ⟨bs [0x15a9270b75a91] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1705 : PLift (G 88722 88742) := ⟨bs [0xad4de69d5a99,0x56a915aa75aa5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1706 : PLift (G 88742 88790) := ⟨bs [0x1ce39ca035aab,0x1ce59d2675ac3,0x56b515ad75ad5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1707 : PLift (G 88790 88800) := ⟨bs [0xad6d8c2f5ad9,0x17ed5ec95adf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1708 : PLift (G 88800 88812) := ⟨bs [0x2b5c2aa3d5ae1,0x2b5cdc8b55ae7,0x56ba95aed5aeb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1709 : PLift (G 88812 88814) := ⟨bs [0x9a326cf15aed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1710 : PLift (G 88814 88868) := ⟨bs [0x2b5e143ed5af1,0x56bc95af55af3,0x56c295b0d5b0b,0x56c515b175b15,0x56c715b1f5b1d,0x56c895b255b23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1711 : PLift (G 88868 88898) := ⟨bs [0x15b2ab5695b29,0x56cc95b355b33,0xe780e53b5b41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1712 : PLift (G 88898 88952) := ⟨bs [0x2b68e4eaf5b47,0x2b6acfb915b57,0x2b6d0a0035b69,0x2b6ee9fb15b77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1713 : PLift (G 88952 88994) := ⟨bs [0xadc4db095b89,0x19c1fa655ba1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1714 : PLift (G 88994 89010) := ⟨bs [0x56e915ba75ba5,0x56ea95bad5bab,0x15bb267395bb1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1715 : PLift (G 89010 89022) := ⟨bs [0xadde3a4b5bb9,0x56ef15bbf5bbd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1716 : PLift (G 89022 89052) := ⟨bs [0x2b7a2b5fd5bd1,0x56f695bdd5bdb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1717 : PLift (G 89052 89070) := ⟨bs [0xadf135855be1,0x56fb15bef5bed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1718 : PLift (G 89070 89108) := ⟨bs [0xe7f41b8f5bef,0x56fe95bfd5bfb,0x2b7fe01f15bff,0x570315c0f5c0d,0x570495c155c13] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1719 : PLift (G 89108 89120) := ⟨bs [0x15c1935cd5c19,0x2b83c1b275c1f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1720 : PLift (G 89120 89124) := ⟨bs [0x7e9a039d5c23] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1721 : PLift (G 89124 89138) := ⟨bs [0x741272ff5c31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1722 : PLift (G 89138 89214) := ⟨bs [0x15c41523f5c41,0x571915c675c65,0x571c95c755c73,0x2b8f204835c79,0x571f15c7f5c7d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1723 : PLift (G 89214 89270) := ⟨bs [0x1d0b8f00d5c8b,0x2b91da0b15c8f,0x572515c975c95,0x572b15caf5cad,0x572d15cb75cb5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1724 : PLift (G 89270 89318) := ⟨bs [0x15cb906335cb9,0x1d11145575ccd,0x2b9ac95575cd7,0x573915ce75ce5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1725 : PLift (G 89318 89330) := ⟨bs [0xae78715b5cf1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1726 : PLift (G 89330 89364) := ⟨bs [0x6b6a1e5f5d13] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1727 : PLift (G 89364 89400) := ⟨bs [0x574695d1d5d1b,0x574915d275d25,0x574a95d2d5d2b,0x15d3175955d31,0x2ba6d5e635d37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1728 : PLift (G 89400 89460) := ⟨bs [0x575115d475d45,0x2ba9139e15d49,0x2baae35475d57,0x575895d655d63,0x2bad21aa15d69,0x575c95d755d73] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1729 : PLift (G 89460 89520) := ⟨bs [0x576115d875d85,0x576495d955d93,0x576715d9f5d9d,0x2bb52437d5da9,0x2bb5c913d5daf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1730 : PLift (G 89520 89534) := ⟨bs [0xe920ecc75db1,0x2bb6e4ce95db7,0x576f15dbf5dbd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1731 : PLift (G 89534 89592) := ⟨bs [0x15dd8c5775dd9,0x577695ddd5ddb,0x2bbbe9caf5ddf,0x2bbec89b95df7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1732 : PLift (G 89592 89628) := ⟨bs [0x577f15dff5dfd,0xe95670f95dff,0x578095e055e03,0x578295e0d5e0b,0x578695e1d5e1b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1733 : PLift (G 89628 89658) := ⟨bs [0x2bc412e715e21,0x1d2f1fc215e35,0x15e3807c55e39] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1734 : PLift (G 89658 89670) := ⟨bs [0x1d2f808695e3b,0x579115e475e45] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1735 : PLift (G 89670 89672) := ⟨bs [0x8c1c5bdd5e47] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1736 : PLift (G 89672 89760) := ⟨bs [0x24e288375e51,0x2bcb0f0915e59,0x2bd31b1475e99,0x2bd3c41655e9f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1737 : PLift (G 89760 89798) := ⟨bs [0xe9c643135ea7,0x57ac95eb55eb3,0x2bd6c5aa75eb7,0x1d3b2b50b5ec5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1738 : PLift (G 89798 89822) := ⟨bs [0x15ed281715ed1,0x57b695edd5edb,0x57b715edf5edd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1739 : PLift (G 89822 89834) := ⟨bs [0x74f886f15ee9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1740 : PLift (G 89834 89840) := ⟨bs [0xe9f5b0755eef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1741 : PLift (G 89840 89868) := ⟨bs [0xaf7c6c935ef9,0x57c295f0d5f0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1742 : PLift (G 89868 89900) := ⟨bs [0x118e8e83f5f23,0x2be513ae55f29,0x57ca95f2d5f2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1743 : PLift (G 89900 89964) := ⟨bs [0x57cd15f375f35,0x57cf15f3f5f3d,0x1d459e8d95f43,0x57d495f555f53,0x2beccedcf5f67,0x57da95f6d5f6b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1744 : PLift (G 89964 89984) := ⟨bs [0xafbd77f35f79,0x2befe5be35f7f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1745 : PLift (G 89984 90012) := ⟨bs [0x57e115f875f85,0xea60caf95f91,0x2bf2c455b5f97,0x57e695f9d5f9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1746 : PLift (G 90012 90024) := ⟨bs [0x15fa248635fa1,0x1d4d9506f5fa3,0x2bf4c90df5fa7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1747 : PLift (G 90024 90068) := ⟨bs [0x2bf5e12575faf,0x57f115fc75fc5,0x57f295fcd5fcb,0x57f495fd55fd3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1748 : PLift (G 90068 90072) := ⟨bs [0x8cbe992b5fd7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1749 : PLift (G 90072 90122) := ⟨bs [0x2bfb1d2db5fd9,0x2bfd251ed5fe9,0x57fe95ffd5ffb,0x2c010186f6009] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1750 : PLift (G 90122 90188) := ⟨bs [0xeab42c8d600f,0x5809160276025,0x580c960356033,0x580f1603f603d,0x58129604d604b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1751 : PLift (G 90188 90228) := ⟨bs [0x2c09c9811604f,0x5815160576055,0x2c0ac85236057,0x58169605d605b,0x139502096069,0x581c960756073] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1752 : PLift (G 90228 90272) := ⟨bs [0x2c0fd7ef1607f,0x2c10d95216087,0x2c12e036b6097,0x2c13cdc01609f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1753 : PLift (G 90272 90290) := ⟨bs [0xb054089d60a9,0x722243160b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1754 : PLift (G 90290 90354) := ⟨bs [0x2c1917e1760c9,0xb07ab37b60f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1755 : PLift (G 90354 90402) := ⟨bs [0x2c1ec602960f7,0x5840961056103,0x1d6b0a48d6105,0x58429610d610b,0x58471611f611d,0x2c24023336121] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1756 : PLift (G 90402 90440) := ⟨bs [0x1d6d9c14f6123,0x2c24dec696127,0x5851161476145,0xeb85621f6147] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1757 : PLift (G 90440 90474) := ⟨bs [0x5859161676165,0x2c2d1e6176169] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1758 : PLift (G 90474 90482) := ⟨bs [0x8d61077b6171] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1759 : PLift (G 90482 90528) := ⟨bs [0x5860961856183,0xebb55873618f,0x58669619d619b,0x2c33c8551619f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1760 : PLift (G 90528 90600) := ⟨bs [0x2c3403abf61a1,0x5869161a761a5,0x586c961b561b3,0x2c3ac758f61d7,0x2c3cd631561e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1761 : PLift (G 90600 90642) := ⟨bs [0x2c3f1c25d61f9,0x1d7f92d9b61fb,0x2c40e51e96207,0x46d153216211] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1762 : PLift (G 90642 90680) := ⟨bs [0x2c42ebc356217,0x5888962256223,0x588d162376235,0x2c46c5e016237] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1763 : PLift (G 90680 90732) := ⟨bs [0xec3008996249,0x2c49d8019624f,0x1d87075736255,0x589a9626d626b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1764 : PLift (G 90732 90804) := ⟨bs [0x589f1627f627d,0x1d8d8f1d762a3,0x2c5516f8162a9,0x58ac962b562b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1765 : PLift (G 90804 90824) := ⟨bs [0x11bd1719162c5,0x2c58dbf8b62c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1766 : PLift (G 90824 90834) := ⟨bs [0x656129a362d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1767 : PLift (G 90834 90902) := ⟨bs [0x2c5b2347b62d9,0x2c5bd37d362df,0x2c5de0dc562ef,0x2c60d74616307,0x58c5163176315] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1768 : PLift (G 90902 90918) := ⟨bs [0x1d97ab967631b,0x2c63e26c5631f,0x58c9163276325] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1769 : PLift (G 90918 90972) := ⟨bs [0xcaf8c0916333,0x58d0963456343,0x58d69635d635b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1770 : PLift (G 90972 91010) := ⟨bs [0x163624ddd6361,0x58db1636f636d,0x1d9f258556375,0x2c7007c5f6381] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1771 : PLift (G 91010 91080) := ⟨bs [0x58e29638d638b,0x3b4551f76399,0x2c78dad3963c7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1772 : PLift (G 91080 91082) := ⟨bs [0x769a588d63c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1773 : PLift (G 91082 91100) := ⟨bs [0xb1ed043b63d9,0x58f6963dd63db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1774 : PLift (G 91100 91122) := ⟨bs [0x58fd720963f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1775 : PLift (G 91122 91152) := ⟨bs [0x2c7ec9bef63f7,0x3b54fafb63f9,0x5900964056403,0x1dab00f736405,0x2c81db8eb640f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1776 : PLift (G 91152 91160) := ⟨bs [0xb20800856411,0x2c82c1d6b6417] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1777 : PLift (G 91160 91230) := ⟨bs [0x59069641d641b,0x21ed1b03642f,0x2c871f3576439,0x2c87e17ef643f,0x59171645f645d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1778 : PLift (G 91230 91292) := ⟨bs [0x1db31fbdb6465,0x1db39082d646b,0x2c8e12e3b6471,0x591d164776475,0x5924964956493,0x59269649d649b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1779 : PLift (G 91292 91368) := ⟨bs [0x2c9417aff64a1,0x2c94cfba964a7,0x1db925d7764ad,0x5930964c564c3,0x40e54ef764e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1780 : PLift (G 91368 91388) := ⟨bs [0x2c9d1f25d64e9,0x1af1c20564ed,0x1dbf2013764f5,0x593e964fd64fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1781 : PLift (G 91388 91424) := ⟨bs [0xee00b8a36501,0x5941165076505,0x5944965156513,0x2ca3c3713651f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1782 : PLift (G 91424 91454) := ⟨bs [0xb2950b8f6529,0x1dc501111653d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1783 : PLift (G 91454 91460) := ⟨bs [0xb2a081376541,0x5950965456543] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1784 : PLift (G 91460 91514) := ⟨bs [0x2ca8d6d8d6547,0x5959165676565,0x595a9656d656b,0x2caf1c75f6579] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1785 : PLift (G 91514 91572) := ⟨bs [0xb2c4f4936589,0x5965165976595,0x596c965b565b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1786 : PLift (G 91572 91622) := ⟨bs [0x1dcf2176565b5,0x2cb72af6d65b9,0x2cb7ddc7165bf,0x2cb8ec9e365c7,0x5979165e765e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1787 : PLift (G 91622 91692) := ⟨bs [0x2cbdde8d965ef,0x4f8dfe2d65f7,0x16619c9bf6619,0x598a9662d662b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1788 : PLift (G 91692 91772) := ⟨bs [0x2cc6c54c36637,0x2cc7c99b5663f,0x5995166576655,0x2ccd1d1736669,0x599b1666f666d,0x599e9667d667b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1789 : PLift (G 91772 91782) := ⟨bs [0x59a1166876685] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1790 : PLift (G 91782 91802) := ⟨bs [0x8f7264a36699] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1791 : PLift (G 91802 91838) := ⟨bs [0x2cd3d6571669f,0x59a8966a566a3,0x59a9166a766a5,0x2cd5e3bc166af,0x59af166bf66bd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1792 : PLift (G 91838 91910) := ⟨bs [0x166c12d0366c1,0x59b6966dd66db,0x27e07d5766e1,0x59c1167076705] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1793 : PLift (G 91910 91922) := ⟨bs [0x8fa206c96711] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1794 : PLift (G 91922 91958) := ⟨bs [0x59c8967256723,0x2ce4e941d6727,0xef76326f672f,0x1def0341d6735] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1795 : PLift (G 91958 91968) := ⟨bs [0x790e2f36739,0x2ce7d28d3673f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1796 : PLift (G 91968 92004) := ⟨bs [0xb3a0a6ad6741,0x59d71675f675d,0x59d8967656763] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1797 : PLift (G 92004 92042) := ⟨bs [0x167686c076769,0x2cf00e8cf6781,0x3bec6aa36789] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1798 : PLift (G 92042 92120) := ⟨bs [0x838c30d6793,0x59eb167af67ad,0x59ec967b567b3,0x59f2967cd67cb,0x2cf9d0ea567cf,0x2cfac722167d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1799 : PLift (G 92120 92178) := ⟨bs [0xeff5b79d67ef,0x2cff0dff367f9,0x5a031680f680d,0x2d021de9d6811] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1800 : PLift (G 92178 92222) := ⟨bs [0x1e018b7216813,0x5a071681f681d,0x5a0a9682d682b,0x5a0e9683d683b,0x1e0505fa5683d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1801 : PLift (G 92222 92234) := ⟨bs [0x1e05952c96843,0xb42599496849] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1802 : PLift (G 92234 92252) := ⟨bs [0x5a131684f684d,0x5a14968556853,0x5a169685d685b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1803 : PLift (G 92252 92270) := ⟨bs [0xa032b60f686d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1804 : PLift (G 92270 92334) := ⟨bs [0x2d11076496889,0xf065d5416897,0x1e0d071bd689d,0x5a2b168af68ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1805 : PLift (G 92334 92354) := ⟨bs [0x1e0fab11368bb,0xde21fc968c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1806 : PLift (G 92354 92358) := ⟨bs [0x8330016b68c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1807 : PLift (G 92358 92370) := ⟨bs [0x5a32968cd68cb,0x2d1a1911968d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1808 : PLift (G 92370 92382) := ⟨bs [0xb46c78c968d9,0x5a37168df68dd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1809 : PLift (G 92382 92402) := ⟨bs [0xf09603bf68df,0x5a38968e568e3,0x2d1de4c0768ef,0x2d1e0ce7f68f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1810 : PLift (G 92402 92420) := ⟨bs [0x5a3f168ff68fd,0x5a40969056903] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1811 : PLift (G 92420 92432) := ⟨bs [0x906e67bd690f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1812 : PLift (G 92432 92504) := ⟨bs [0x5a4a9692d692b,0x5a4b1692f692d,0x5a4c969356933,0x2d27c373d693f,0x41b0d9436949,0x2d2aece3d6957] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1813 : PLift (G 92504 92568) := ⟨bs [0x5a569695d695b,0x2d30e21256987,0x5a631698f698d,0x2d32cd4036997] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1814 : PLift (G 92568 92570) := ⟨bs [0x1699a030b6999] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1815 : PLift (G 92570 92582) := ⟨bs [0x12152223b69a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1816 : PLift (G 92582 92628) := ⟨bs [0xf121cd6d69b1,0xf1360b4769cf,0x5a74969d569d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1817 : PLift (G 92628 92648) := ⟨bs [0x2d3bd1a0169df,0x12199c4f69e1,0x2d3ce400f69e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1818 : PLift (G 92648 92670) := ⟨bs [0x169f158e369f1,0x5a7f169ff69fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1819 : PLift (G 92670 92672) := ⟨bs [0x90ce749569ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1820 : PLift (G 92672 92682) := ⟨bs [0x486a5b276a09] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1821 : PLift (G 92682 92684) := ⟨bs [0xa0ea12f76a0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1822 : PLift (G 92684 92738) := ⟨bs [0x5a8516a176a15,0x5a8696a1d6a1b,0x5a8896a256a23,0x5a8b16a2f6a2d,0x5a8c96a356a33,0xfe80436a41] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1823 : PLift (G 92738 92754) := ⟨bs [0x5a948a256a51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1824 : PLift (G 92754 92762) := ⟨bs [0x78c842c16a59] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1825 : PLift (G 92762 92790) := ⟨bs [0xf195a7076a5f,0x5a9a96a6d6a6b,0x5a9d16a776a75] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1826 : PLift (G 92790 92792) := ⟨bs [0x90fc9c496a77] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1827 : PLift (G 92792 92822) := ⟨bs [0x2d500349b6a81,0x2d510d7856a89,0xcf3008636a95] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1828 : PLift (G 92822 92862) := ⟨bs [0x2d53c0b8b6a9f,0x2d5607b9f6ab1,0x16ab9c5db6ab9,0x5aaf16abf6abd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1829 : PLift (G 92862 92894) := ⟨bs [0x2d57ead0f6abf,0x5ab096ac56ac3,0x1e3d070056add] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1830 : PLift (G 92894 92900) := ⟨bs [0x6fa97d776ae3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1831 : PLift (G 92900 92958) := ⟨bs [0x2d5f185416af9,0x2d5fd03756aff,0x5ac316b0f6b0d,0x2d62e3d376b17,0x5ac716b1f6b1d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1832 : PLift (G 92958 92988) := ⟨bs [0x2d63c75a76b1f,0x5ace96b3d6b3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1833 : PLift (G 92988 93002) := ⟨bs [0xb5a1f2456b41,0x2d69021516b49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1834 : PLift (G 93002 93084) := ⟨bs [0x2d6ec1dd16b77,0x5adf16b7f6b7d,0x5ae096b856b83,0x5ae516b976b95,0x5ae696b9d6b9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1835 : PLift (G 93084 93098) := ⟨bs [0x16ba1667f6ba1,0x16ba9863f6ba9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1836 : PLift (G 93098 93132) := ⟨bs [0x2d75ce5ef6baf,0x16bb959476bb9,0xa79c5676bcb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1837 : PLift (G 93132 93134) := ⟨bs [0xa1b1950f6bcd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1838 : PLift (G 93134 93180) := ⟨bs [0x5af496bd56bd3,0x2d7be47176bdf,0xf2a03bb16bf1,0x5afe96bfd6bfb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1839 : PLift (G 93180 93188) := ⟨bs [0xa1cacc276c03] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1840 : PLift (G 93188 93240) := ⟨bs [0xf2b63ff76c0f,0x1e59154356c2d,0x2d86e60ab6c37] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1841 : PLift (G 93240 93258) := ⟨bs [0x1a055c716c39,0x5b1096c456c43,0x5b1116c476c45,0x16c4a8b056c49] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1842 : PLift (G 93258 93282) := ⟨bs [0x2d89da0996c4f,0xb63242cb6c61] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1843 : PLift (G 93282 93330) := ⟨bs [0x5b1896c656c63,0x2d8cd23dd6c67,0x5b1e96c7d6c7b,0x2d90db0776c87,0x5b2296c8d6c8b,0x1330b68d6c91] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1844 : PLift (G 93330 93408) := ⟨bs [0x2d932bfff6c99,0x5b2e96cbd6cbb,0x16cdb0456cc1,0x2d98d36396cc7,0x2d9beb05b6cdf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1845 : PLift (G 93408 93480) := ⟨bs [0x5b3a96ced6ceb,0x5b3c96cf56cf3,0xf36500b56d17,0x2da4eac456d27] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1846 : PLift (G 93480 93494) := ⟨bs [0xf3704b196d29,0x2da5c3d656d2f,0x5b4c96d356d33,0x5b4d16d376d35] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1847 : PLift (G 93494 93530) := ⟨bs [0x16d3a23436d39,0x2da7d51c76d3f,0x5b5496d556d53,0x144db3db6d59] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1848 : PLift (G 93530 93558) := ⟨bs [0xb6b9710f6d71,0x5b5d16d776d75] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1849 : PLift (G 93558 93564) := ⟨bs [0x2daeecf1b6d77,0xd0d904396d7b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1850 : PLift (G 93564 93582) := ⟨bs [0x12470ce5f6d8d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1851 : PLift (G 93582 93630) := ⟨bs [0x16da218056da1,0xf3c586796da7,0x5b6f16dbf6dbd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1852 : PLift (G 93630 93720) := ⟨bs [0x1e7b0779b6dc5,0x5b7c96df56df3,0x5b8116e076e05,0xa9c55296e07,0x2dc2cea7b6e17] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1853 : PLift (G 93720 93810) := ⟨bs [0x1e8397cdf6e2b,0x2dc805ebf6e41,0x5b9096e456e43,0x1e8788fb36e5b,0x2dce28d5d6e71] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1854 : PLift (G 93810 93888) := ⟨bs [0x5b9c96e756e73,0x5ba096e856e83,0x5ba696e9d6e9b,0x14f53ed96eaf,0x2dd7cfc576ebf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1855 : PLift (G 93888 93902) := ⟨bs [0xb76110696ec1,0x5bb116ec76ec5,0x5bb316ecf6ecd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1856 : PLift (G 93902 93912) := ⟨bs [0x92bd5d916ed7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1857 : PLift (G 93912 93950) := ⟨bs [0x2ddb161cb6ed9,0x5bb896ee56ee3,0x3d2a9ddb6ef1,0x5bbd16ef76ef5,0x5bbf16eff6efd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1858 : PLift (G 93950 93980) := ⟨bs [0xf4b5bf436f0f,0x5bc496f156f13,0x3fd993f76f1b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1859 : PLift (G 93980 93984) := ⟨bs [0x68e58abd6f1f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1860 : PLift (G 93984 93998) := ⟨bs [0xa3308ea16f2d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1861 : PLift (G 93998 94034) := ⟨bs [0x2de6ebcf16f37,0x2de711a9d6f39,0x51a26e3f6f51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1862 : PLift (G 94034 94050) := ⟨bs [0x5bd8ed676f61] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1863 : PLift (G 94050 94110) := ⟨bs [0x2ded085c36f69,0x2deddf3136f6f,0x2defc57bd6f7f,0x5be496f956f93,0x5be716f9f6f9d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1864 : PLift (G 94110 94112) := ⟨bs [0x930d781f6f9f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1865 : PLift (G 94112 94122) := ⟨bs [0x5be916fa76fa5,0xb7d53ce16fa9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1866 : PLift (G 94122 94152) := ⟨bs [0x6915c9536fc7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1867 : PLift (G 94152 94208) := ⟨bs [0x2df924c1f6fc9,0x2dfb1e9e76fd9,0x2dff018fb6ff9,0x2dffec6ad6fff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1868 : PLift (G 94208 94254) := ⟨bs [0x1eab922b1700b,0x5c05170177015,0x5c0b1702f702d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1869 : PLift (G 94254 94262) := ⟨bs [0x126922e517035] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1870 : PLift (G 94262 94310) := ⟨bs [0x170404f537041,0x5c14970557053,0x5c18970657063,0x1eb317ac37065] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1871 : PLift (G 94310 94344) := ⟨bs [0xf5a1bf477071,0x2e0ee229d7077,0x5c1e9707d707b,0x2e10e9cff7087] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1872 : PLift (G 94344 94422) := ⟨bs [0x5c231708f708d,0x2e11e9c37708f,0x5c2a970ad70ab,0x5c2f170bf70bd,0x2e17ed26970bf,0x5c35170d770d5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1873 : PLift (G 94422 94428) := ⟨bs [0x5c36970dd70db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1874 : PLift (G 94428 94434) := ⟨bs [0x5c38b33d70e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1875 : PLift (G 94434 94448) := ⟨bs [0x2e1ce6fc370e7,0x170e99fcd70e9,0x77569b570ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1876 : PLift (G 94448 94530) := ⟨bs [0x2e1fded7f70ff,0x5c431710f710d,0x5c44971157113,0x1662beed7131,0x34c11edb7141] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1877 : PLift (G 94530 94542) := ⟨bs [0x1ec5a30a17143,0x5c531714f714d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1878 : PLift (G 94542 94544) := ⟨bs [0x698558c7714f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1879 : PLift (G 94544 94584) := ⟨bs [0x5c54971557153,0x2e2bc4c25715f,0x2e2c0fc6f7161,0x5c5b1716f716d,0x2e2ed86b97177] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1880 : PLift (G 94584 94604) := ⟨bs [0x1ecb2c6e77185,0x1ecb993d7718b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1881 : PLift (G 94604 94650) := ⟨bs [0xd330dff37195,0x5c671719f719d,0x2e3720a9b71b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1882 : PLift (G 94650 94728) := ⟨bs [0x5c6e971bd71bb,0x2e3bebcb971df,0x1ed30c90f71e5,0x5c7d171f771f5,0x5c80972057203,0x2e40d6d137207] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1883 : PLift (G 94728 94790) := ⟨bs [0x5c869721d721b,0x1ed980d2d7233,0x17238afc77239,0x5c8f1723f723d,0x5c91172477245] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1884 : PLift (G 94790 94838) := ⟨bs [0x17248c72f7249,0x5c969725d725b,0x5c98972657263,0x2e4ceb3897267,0x5c9d172777275] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1885 : PLift (G 94838 94848) := ⟨bs [0xb93cf73f7279,0x2e4fe0a5f727f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1886 : PLift (G 94848 94890) := ⟨bs [0x9c196517281,0xf712e4bf7299,0x2e5516f7b72a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1887 : PLift (G 94890 94962) := ⟨bs [0x2e56ceff372b7,0x5cae972bd72bb,0x5cb5172d772d5,0x5cb9172e772e5,0x2e5cce03b72e7,0x2e5e2267d72f1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1888 : PLift (G 94962 95004) := ⟨bs [0x1731204157311,0x2e62d3e537317,0x5cc69731d731b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1889 : PLift (G 95004 95028) := ⟨bs [0xb99120397321,0x5ccb1732f732d,0x5ccc973357333] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1890 : PLift (G 95028 95090) := ⟨bs [0x2e6ac688b7357,0x2e6bd6011735f,0x5cda9736d736b,0x2e6ddf79d736f,0x2e6e01a737371] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1891 : PLift (G 95090 95108) := ⟨bs [0x5cdd173777375,0x5cdf1737f737d,0x1ef58046d7383] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1892 : PLift (G 95108 95112) := ⟨bs [0x949cd34b7387] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1893 : PLift (G 95112 95154) := ⟨bs [0x1ef7930ab739b,0xf7c4575573a7,0x2e7626fdf73b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1894 : PLift (G 95154 95204) := ⟨bs [0x2e791382d73c9,0x5cf5173d773d5,0x3194071573d7,0x5cf8973e573e3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1895 : PLift (G 95204 95214) := ⟨bs [0x7270bc4b73ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1896 : PLift (G 95214 95258) := ⟨bs [0x5cfc973f573f3,0x85e829773ff,0x2e8014bf97401,0x2e80c21b77407,0x2e832334d7419] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1897 : PLift (G 95258 95280) := ⟨bs [0x5d071741f741d,0x5d08974257423,0x1742a96c57429,0x2e85c85a7742f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1898 : PLift (G 95280 95340) := ⟨bs [0x2e86dda5f7437,0x2e89d302b744f,0x1f07287757455,0x2e8bd994b745f,0x5d1a9746d746b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1899 : PLift (G 95340 95370) := ⟨bs [0x2e9100e617489] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1900 : PLift (G 95370 95384) := ⟨bs [0x6a7586917497] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1901 : PLift (G 95384 95430) := ⟨bs [0x2e940205574a1,0x2e9509cad74a9,0x5d2d174b774b5,0x126ae25774bb,0x5d31174c774c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1902 : PLift (G 95430 95444) := ⟨bs [0xba682a8974d1,0x1f1184ec574d3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1903 : PLift (G 95444 95480) := ⟨bs [0x5d39174e774e5,0x1f13ac2ad74eb,0x2e9de639174ef,0xf8a6605f74f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1904 : PLift (G 95480 95540) := ⟨bs [0x5d3e974fd74fb,0x5d44975157513,0xf8c6044d7527,0x5d4a9752d752b,0x1f19a0bfd7533] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1905 : PLift (G 95540 95562) := ⟨bs [0x5d4f1753f753d,0xbaa429bb7549] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1906 : PLift (G 95562 95598) := ⟨bs [0x2eaa184ed7551,0x5d571755f755d,0x5d5b1756f756d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1907 : PLift (G 95598 95604) := ⟨bs [0x72ea4f6f7573] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1908 : PLift (G 95604 95622) := ⟨bs [0x1758290817581,0xd572126b7585] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1909 : PLift (G 95622 95708) := ⟨bs [0x5d631758f758d,0x2eb20afb37591,0x5d68975a575a3,0x5d75175d775d5,0x5d76975dd75db] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1910 : PLift (G 95708 95714) := ⟨bs [0x5d7a7ab775e1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1911 : PLift (G 95714 95738) := ⟨bs [0x5d79175e775e5,0x5d7a975ed75eb,0x5d7c975f575f3,0x175f8d2b775f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1912 : PLift (G 95738 95774) := ⟨bs [0xd5b8351f7603,0x1f2d2cd63761d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1913 : PLift (G 95774 95802) := ⟨bs [0x2ec4ee7c97627,0x5d8b1762f762d,0x2ec5d5f79762f,0x1763919457639] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1914 : PLift (G 95802 95858) := ⟨bs [0x474a5799763b,0x5d91176477645,0x5d929764d764b,0x17670c4fb7671] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1915 : PLift (G 95858 95870) := ⟨bs [0xa672a691767d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1916 : PLift (G 95870 95918) := ⟨bs [0x2ed0217417681,0x2ed114f8d7689,0x5da4976957693,0x2ed4caac176a7,0x5dab176af76ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1917 : PLift (G 95918 95924) := ⟨bs [0xa68931d976b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1918 : PLift (G 95924 95960) := ⟨bs [0x2ed712a5f76b9,0x5db2976cd76cb,0x5db5176d776d5,0x2edae52a376d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1919 : PLift (G 95960 95990) := ⟨bs [0xd63a230776e3,0x5dbc976f576f3,0x4ef1eab976f5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1920 : PLift (G 95990 96060) := ⟨bs [0x7d096df7701,0x5dc31770f770d,0x2ee20cd957711,0x5dca9772d772b,0x5dcd177377735,0x5dce9773d773b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1921 : PLift (G 96060 96098) := ⟨bs [0xfa35797b774f,0x2eec0cd2b7761] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1922 : PLift (G 96098 96150) := ⟨bs [0x177895f637789,0x5de5177977795] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1923 : PLift (G 96150 96158) := ⟨bs [0xa6f0f1e3779d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1924 : PLift (G 96158 96182) := ⟨bs [0x2ef4df9f377a7,0x5dec977b577b3,0x12c9110e777b5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1925 : PLift (G 96182 96260) := ⟨bs [0x2ef8c150f77c7,0x5df4977d577d3,0x5df7177df77dd,0x2efbe0f3977df,0x2efd1ac7177e9,0x5e00978057803] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1926 : PLift (G 96260 96324) := ⟨bs [0x2f00d06e77807,0x5e031780f780d,0x2f030e5697819,0x2c42b3057821,0x5e09178277825,0x5e10978457843] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1927 : PLift (G 96324 96338) := ⟨bs [0x2f090f1fd7849,0x4f39cd17784b,0x17850cd977851] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1928 : PLift (G 96338 96354) := ⟨bs [0x2f0c06c8d7861] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1929 : PLift (G 96354 96378) := ⟨bs [0x6b90a4517879] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1930 : PLift (G 96378 96402) := ⟨bs [0x5e2538177891] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1931 : PLift (G 96402 96444) := ⟨bs [0xd7383bcf78a3,0x2f15c0afd78af,0x5e2e978bd78bb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1932 : PLift (G 96444 96480) := ⟨bs [0x5e30978c578c3,0x2f190ac3378c9,0x5e33178cf78cd,0x1f67280c978d5,0x2f1bceff178df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1933 : PLift (G 96480 96488) := ⟨bs [0xfb44312d78e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1934 : PLift (G 96488 96494) := ⟨bs [0x8911bc9378ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1935 : PLift (G 96494 96528) := ⟨bs [0x2f1e1903178f1,0x5e41179077905,0x2f21d7e11790f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1936 : PLift (G 96528 96558) := ⟨bs [0x7db97c337929,0x5e4b1792f792d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1937 : PLift (G 96558 96590) := ⟨bs [0x5e51179477945,0x5e529794d794b,0x1f710597f794d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1938 : PLift (G 96590 96602) := ⟨bs [0x6bd1e9bf7959] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1939 : PLift (G 96602 96698) := ⟨bs [0x5e60979857983,0x1f772dcb57995,0x5e669799d799b,0x2f33c4b49799f,0x2f371de3d79b9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1940 : PLift (G 96698 96750) := ⟨bs [0xfbd693cf79bf,0x5e76979dd79db,0x2f3c0851b79e1,0x5e78979e579e3,0x5e7b179ef79ed] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1941 : PLift (G 96750 96780) := ⟨bs [0x1f7f0badd79f5,0x1f7fab7a379fb,0x17a011ef77a01,0x5e8297a0d7a0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1942 : PLift (G 96780 96828) := ⟨bs [0x5e8497a157a13,0x5e8717a1f7a1d,0x2f43ef2877a1f,0x5e8d17a377a35,0x2f46de6ff7a37,0x5e8e97a3d7a3b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1943 : PLift (G 96828 96852) := ⟨bs [0x2f49cafdb7a4f,0x5e9497a557a53] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1944 : PLift (G 96852 96908) := ⟨bs [0xbd2e1a5d7a59,0x5e9f17a7f7a7d,0x5ea297a8d7a8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1945 : PLift (G 96908 96974) := ⟨bs [0x2f51ea2e17a8f,0x5ea897aa57aa3,0x2f570e07f7ab9,0x2f57d8a2f7abf,0x5eb317acf7acd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1946 : PLift (G 96974 97002) := ⟨bs [0x1f9190f677ad3,0x5eb717adf7add,0x5eb917ae77ae5,0x17ae942297ae9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1947 : PLift (G 97002 97004) := ⟨bs [0xa86882657aeb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1948 : PLift (G 97004 97074) := ⟨bs [0x2f5dc70737aef,0x5ebf17aff7afd,0x2f61ee76b7b0f,0x2f661dbf17b31] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1949 : PLift (G 97074 97104) := ⟨bs [0xbd9d9ccd7b39,0x2f69c5d237b4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1950 : PLift (G 97104 97158) := ⟨bs [0x5ed717b5f7b5d,0x2f6cc8ad77b67,0x2f6fdc90d7b7f,0x5ee117b877b85] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1951 : PLift (G 97158 97170) := ⟨bs [0xfd04fe097b87,0x17b91faf97b91] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1952 : PLift (G 97170 97172) := ⟨bs [0x1fa1a83257b93] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1953 : PLift (G 97172 97188) := ⟨bs [0x7e8aab837b99,0x5ee897ba57ba3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1954 : PLift (G 97188 97242) := ⟨bs [0x1fa51b3bb7bbd,0x2f79cbf857bcf,0x2f7b024197bd9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1955 : PLift (G 97242 97302) := ⟨bs [0xd9183de57beb,0x5f0097c057c03,0x5f0517c177c15] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1956 : PLift (G 97302 97368) := ⟨bs [0x2f82d327d7c17,0xfd76e4777c2f,0x2f8ac7a777c57] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1957 : PLift (G 97368 97398) := ⟨bs [0x3f665afd7c59,0x5f1717c5f7c5d,0x5f1897c657c63,0x5f1917c677c65,0x5f1a97c6d7c6b,0x5f1d17c777c75] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1958 : PLift (G 97398 97454) := ⟨bs [0x13869aa57c8f,0x1fb7037737c95,0xfdc2d3e77ca1,0x5f2b17caf7cad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1959 : PLift (G 97454 97524) := ⟨bs [0x5f2c97cb57cb3,0x2f96e77ed7cb7,0x5f3697cdd7cdb,0x1fbd0944f7cdd,0x2f9ce76157ce7,0x5f3c97cf57cf3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1960 : PLift (G 97524 97554) := ⟨bs [0x5f4297d0d7d0b,0x5f4317d0f7d0d,0xbe88241b7d11] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1961 : PLift (G 97554 97580) := ⟨bs [0x10f076dd7d19,0x5f4897d257d23,0x17d29c1b57d29,0x5f4a97d2d7d2b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1962 : PLift (G 97580 97614) := ⟨bs [0x2fa5d879d7d2f,0x2fa8c49db7d47,0x17d48e5277d49,0x5f5317d4f7d4d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1963 : PLift (G 97614 97712) := ⟨bs [0x2fae2e0337d71,0x5f5c97d757d73,0x2fb11fd4b7d89,0xb660e217d97,0x32e6987b7daf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1964 : PLift (G 97712 97788) := ⟨bs [0xfe81d7bf7dc1,0x1fd397bdd7deb,0x2fbe095037df1,0x5f7e97dfd7dfb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1965 : PLift (G 97788 97844) := ⟨bs [0x5f7f17dff7dfd,0x5f8517e177e15,0x5f8917e277e25,0x17e3211297e31,0x5f8c97e357e33] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1966 : PLift (G 97844 97872) := ⟨bs [0x2fc6e80df7e37,0x2fc71f1ad7e39,0x5f9097e457e43,0x5f9117e477e45,0x2fc9e58f37e4f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1967 : PLift (G 97872 97932) := ⟨bs [0x2fcac33897e57,0x5f9697e5d7e5b,0x2fcfe17417e7f,0x2fd0dfa177e87,0x5fa297e8d7e8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1968 : PLift (G 97932 97988) := ⟨bs [0x2fd2c7a5d7e97,0x4c8ad2837ea9,0x2fd5d7d777eaf,0x5fad17eb77eb5,0x5fb097ec57ec3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1969 : PLift (G 97988 98010) := ⟨bs [0x17eda2ef37ed9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1970 : PLift (G 98010 98018) := ⟨bs [0x132499d417edb,0x2fdc199df7ee1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1971 : PLift (G 98018 98042) := ⟨bs [0x7fa80f3d7ef9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1972 : PLift (G 98042 98058) := ⟨bs [0xff569e497eff,0x17f0a8c417f09] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1973 : PLift (G 98058 98130) := ⟨bs [0x17f2185617f21,0x5fcd17f377f35,0x5fd297f4d7f4b,0x2fea1ba0b7f51] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1974 : PLift (G 98130 98228) := ⟨bs [0x2febcf4bf7f5f,0x5fe097f857f83,0x2ff3dbc1b7f9f,0x5fe917fa77fa5,0x5feb17faf7fad,0xe59dbb77fb3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1975 : PLift (G 98228 98270) := ⟨bs [0x5ff297fcd7fcb,0x17fd10bd97fd1,0x5ff717fdf7fdd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1976 : PLift (G 98270 98318) := ⟨bs [0x17ffa8cf77ff9,0x5ffe97ffd7ffb,0x200121905800d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1977 : PLift (G 98318 98348) := ⟨bs [0x180120e378011,0x492a81b38013,0x3002d88ab8017,0x600a9802d802b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1978 : PLift (G 98348 98390) := ⟨bs [0x30082d1fd8041,0x30091b1c58049,0x6014980558053,0x6015180578055] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1979 : PLift (G 98390 98408) := ⟨bs [0x6dd648b78067] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1980 : PLift (G 98408 98460) := ⟨bs [0x601a9806d806b,0x601c980758073,0x601f1807f807d,0x60229808d808b,0x6025180978095,0x60269809d809b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1981 : PLift (G 98460 98480) := ⟨bs [0x200d80a9b80a3,0x30152d30980a9,0x3015cc34980af] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1982 : PLift (G 98480 98534) := ⟨bs [0x200f904bf80bb,0x6032980cd80cb,0x301acdc2980d7,0x6039180e780e5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1983 : PLift (G 98534 98544) := ⟨bs [0x301dc9a5380ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1984 : PLift (G 98544 98562) := ⟨bs [0x9a0297798101] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1985 : PLift (G 98562 98622) := ⟨bs [0x6040981058103,0x60431810f810d,0x6049181278125,0x13431cf69813d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1986 : PLift (G 98622 98664) := ⟨bs [0x6050981458143,0x3029ed85f814f,0x18152ca858151,0x302cd8e738167] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1987 : PLift (G 98664 98670) := ⟨bs [0x605b1816f816d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1988 : PLift (G 98670 98690) := ⟨bs [0x10101df318181] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1989 : PLift (G 98690 98714) := ⟨bs [0x3032c98cf8197,0xc0ce569f8199] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1990 : PLift (G 98714 98732) := ⟨bs [0x60671819f819d,0xc0d5515d81a9,0x606a981ad81ab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1991 : PLift (G 98732 98808) := ⟨bs [0x30362cd2181b1,0x6075181d781d5,0x6076981dd81db,0x303e0b61d81f1,0x303ecc7af81f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1992 : PLift (G 98808 98850) := ⟨bs [0x181fa7a0b81f9,0x6085182178215,0x182214afd8221] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1993 : PLift (G 98850 98874) := ⟨bs [0x608c982358233,0x608d182378235,0x3047032db8239] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1994 : PLift (G 98874 98888) := ⟨bs [0x101864af78247] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1995 : PLift (G 98888 98928) := ⟨bs [0x60931824f824d,0x304a2e35b8251,0x6094982558253,0x60971825f825d,0x304bcdf6d825f,0x304dd1b0d826f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1996 : PLift (G 98928 98930) := ⟨bs [0x101a1f4bd8271] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1997 : PLift (G 98930 98964) := ⟨bs [0x609e9827d827b,0x20359eeb98283,0x30510bebd8289,0x60a4982958293] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1998 : PLift (G 98964 98982) := ⟨bs [0x1f90cea382a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q1999 : PLift (G 98982 98994) := ⟨bs [0x60ac761f82b1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2000 : PLift (G 98994 99014) := ⟨bs [0x3056c085782b7,0x203b24ceb82c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2001 : PLift (G 99014 99018) := ⟨bs [0x182c8a0fb82c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2002 : PLift (G 99018 99024) := ⟨bs [0x6e8461a382cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2003 : PLift (G 99024 99090) := ⟨bs [0x305ed2bb82e1,0x60bb182ef82ed,0x3060c5b578307,0x60c29830d830b,0x3062164618311] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2004 : PLift (G 99090 99104) := ⟨bs [0x3063d19f7831f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2005 : PLift (G 99104 99110) := ⟨bs [0xac1276a78325] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2006 : PLift (G 99110 99134) := ⟨bs [0x3065e02b7832f,0x135cac219833b,0x60cf1833f833d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2007 : PLift (G 99134 99192) := ⟨bs [0x30681cdc78341,0x60d0983458343,0x60d31834f834d,0x60d9183678365,0x2272a433836d,0x306ec47778377] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2008 : PLift (G 99192 99224) := ⟨bs [0x3072d84d38397] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2009 : PLift (G 99224 99234) := ⟨bs [0x6ec25c1983a1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2010 : PLift (G 99234 99252) := ⟨bs [0x30752c29183a9,0x1362a9dd983b3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2011 : PLift (G 99252 99278) := ⟨bs [0x30771218783b9,0x60ee983bd83bb,0x60f3183cf83cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2012 : PLift (G 99278 99348) := ⟨bs [0xc1eccc0983d9,0x60fd183f783f5,0x6104984158413] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2013 : PLift (G 99348 99350) := ⟨bs [0x20572f04f8415] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2014 : PLift (G 99350 99368) := ⟨bs [0x102c61f2d8427] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2015 : PLift (G 99368 99402) := ⟨bs [0x610a9842d842b,0x308625c0d8431,0x3087d1397843f,0x6111184478445,0x308910ef18449] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2016 : PLift (G 99402 99410) := ⟨bs [0x102e208738451] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2017 : PLift (G 99410 99488) := ⟨bs [0x308cc97ef8467,0x308de369b846f,0x61231848f848d,0x3093c9f41849f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2018 : PLift (G 99488 99498) := ⟨bs [0xc25572c984a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2019 : PLift (G 99498 99524) := ⟨bs [0xacc932cd84c3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2020 : PLift (G 99524 99530) := ⟨bs [0x3098cd64184c7,0xc2653e6f84c9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2021 : PLift (G 99530 99552) := ⟨bs [0x309bdba3784df] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2022 : PLift (G 99552 99560) := ⟨bs [0x10344ee6f84e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2023 : PLift (G 99560 99612) := ⟨bs [0x613a984ed84eb,0x613c984f584f3,0xe681bed84f9,0x613f184ff84fd,0x3bde4bb18517,0x61469851d851b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2024 : PLift (G 99612 99668) := ⟨bs [0x30a4e7a1d8527,0x206fa8fb9853b,0x61531854f854d,0x6154985558553] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2025 : PLift (G 99668 99708) := ⟨bs [0x30abd4c5d855f,0x30ad0fd0f8569,0x615e9857d857b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2026 : PLift (G 99708 99720) := ⟨bs [0xde910eab857d,0x30b000c378581,0x30b0d74658587] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2027 : PLift (G 99720 99734) := ⟨bs [0xc2c55e758589,0x6165185978595] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2028 : PLift (G 99734 99768) := ⟨bs [0xc2d83cf185b1,0x30b6c3d7985b7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2029 : PLift (G 99768 99818) := ⟨bs [0x6172985cd85cb,0x30ba0073385d1,0x30bc18cc185e1,0x185e9017f85e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2030 : PLift (G 99818 99824) := ⟨bs [0x103f68a4585ef] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2031 : PLift (G 99824 99834) := ⟨bs [0x617d185f785f5,0xc2fdfd6f85f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2032 : PLift (G 99834 99902) := ⟨bs [0x30bfeb3f985ff,0x6184986158613,0x30c3d8b37861f,0x6189186278625,0x30c507e978629,0x618f1863f863d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2033 : PLift (G 99902 99990) := ⟨bs [0x6190986458643,0x6194986558653,0x30cb304538659,0x30cf215b18679,0x61a0986858683,0x61a5186978695] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def q2034 : PLift (G 99990 100000) := ⟨bs [0x104650ce38697] (by decide +kernel)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_range : G 3120 100000 :=
  j (j (j (j (j (j (j (j (j (j (q0.down) (j (q1.down) (q2.down))) (j (j (q3.down) (q4.down)) (j (q5.down) (q6.down)))) (j (j (j (q7.down) (q8.down)) (j (q9.down) (q10.down))) (j (j (q11.down) (q12.down)) (j (q13.down) (q14.down))))) (j (j (j (j (q15.down) (q16.down)) (j (q17.down) (q18.down))) (j (j (q19.down) (q20.down)) (j (q21.down) (q22.down)))) (j (j (j (q23.down) (q24.down)) (j (q25.down) (q26.down))) (j (j (q27.down) (q28.down)) (j (q29.down) (q30.down)))))) (j (j (j (j (j (q31.down) (q32.down)) (j (q33.down) (q34.down))) (j (j (q35.down) (q36.down)) (j (q37.down) (q38.down)))) (j (j (j (q39.down) (q40.down)) (j (q41.down) (q42.down))) (j (j (q43.down) (q44.down)) (j (q45.down) (q46.down))))) (j (j (j (j (q47.down) (q48.down)) (j (q49.down) (q50.down))) (j (j (q51.down) (q52.down)) (j (q53.down) (q54.down)))) (j (j (j (q55.down) (q56.down)) (j (q57.down) (q58.down))) (j (j (q59.down) (q60.down)) (j (q61.down) (q62.down))))))) (j (j (j (j (j (j (q63.down) (q64.down)) (j (q65.down) (q66.down))) (j (j (q67.down) (q68.down)) (j (q69.down) (q70.down)))) (j (j (j (q71.down) (q72.down)) (j (q73.down) (q74.down))) (j (j (q75.down) (q76.down)) (j (q77.down) (q78.down))))) (j (j (j (j (q79.down) (q80.down)) (j (q81.down) (q82.down))) (j (j (q83.down) (q84.down)) (j (q85.down) (q86.down)))) (j (j (j (q87.down) (q88.down)) (j (q89.down) (q90.down))) (j (j (q91.down) (q92.down)) (j (q93.down) (q94.down)))))) (j (j (j (j (j (q95.down) (q96.down)) (j (q97.down) (q98.down))) (j (j (q99.down) (q100.down)) (j (q101.down) (q102.down)))) (j (j (j (q103.down) (q104.down)) (j (q105.down) (q106.down))) (j (j (q107.down) (q108.down)) (j (q109.down) (q110.down))))) (j (j (j (j (q111.down) (q112.down)) (j (q113.down) (q114.down))) (j (j (q115.down) (q116.down)) (j (q117.down) (q118.down)))) (j (j (j (q119.down) (q120.down)) (j (q121.down) (q122.down))) (j (j (q123.down) (q124.down)) (j (q125.down) (q126.down)))))))) (j (j (j (j (j (j (q127.down) (j (q128.down) (q129.down))) (j (j (q130.down) (q131.down)) (j (q132.down) (q133.down)))) (j (j (j (q134.down) (q135.down)) (j (q136.down) (q137.down))) (j (j (q138.down) (q139.down)) (j (q140.down) (q141.down))))) (j (j (j (j (q142.down) (q143.down)) (j (q144.down) (q145.down))) (j (j (q146.down) (q147.down)) (j (q148.down) (q149.down)))) (j (j (j (q150.down) (q151.down)) (j (q152.down) (q153.down))) (j (j (q154.down) (q155.down)) (j (q156.down) (q157.down)))))) (j (j (j (j (j (q158.down) (q159.down)) (j (q160.down) (q161.down))) (j (j (q162.down) (q163.down)) (j (q164.down) (q165.down)))) (j (j (j (q166.down) (q167.down)) (j (q168.down) (q169.down))) (j (j (q170.down) (q171.down)) (j (q172.down) (q173.down))))) (j (j (j (j (q174.down) (q175.down)) (j (q176.down) (q177.down))) (j (j (q178.down) (q179.down)) (j (q180.down) (q181.down)))) (j (j (j (q182.down) (q183.down)) (j (q184.down) (q185.down))) (j (j (q186.down) (q187.down)) (j (q188.down) (q189.down))))))) (j (j (j (j (j (j (q190.down) (q191.down)) (j (q192.down) (q193.down))) (j (j (q194.down) (q195.down)) (j (q196.down) (q197.down)))) (j (j (j (q198.down) (q199.down)) (j (q200.down) (q201.down))) (j (j (q202.down) (q203.down)) (j (q204.down) (q205.down))))) (j (j (j (j (q206.down) (q207.down)) (j (q208.down) (q209.down))) (j (j (q210.down) (q211.down)) (j (q212.down) (q213.down)))) (j (j (j (q214.down) (q215.down)) (j (q216.down) (q217.down))) (j (j (q218.down) (q219.down)) (j (q220.down) (q221.down)))))) (j (j (j (j (j (q222.down) (q223.down)) (j (q224.down) (q225.down))) (j (j (q226.down) (q227.down)) (j (q228.down) (q229.down)))) (j (j (j (q230.down) (q231.down)) (j (q232.down) (q233.down))) (j (j (q234.down) (q235.down)) (j (q236.down) (q237.down))))) (j (j (j (j (q238.down) (q239.down)) (j (q240.down) (q241.down))) (j (j (q242.down) (q243.down)) (j (q244.down) (q245.down)))) (j (j (j (q246.down) (q247.down)) (j (q248.down) (q249.down))) (j (j (q250.down) (q251.down)) (j (q252.down) (q253.down))))))))) (j (j (j (j (j (j (j (q254.down) (j (q255.down) (q256.down))) (j (j (q257.down) (q258.down)) (j (q259.down) (q260.down)))) (j (j (j (q261.down) (q262.down)) (j (q263.down) (q264.down))) (j (j (q265.down) (q266.down)) (j (q267.down) (q268.down))))) (j (j (j (j (q269.down) (q270.down)) (j (q271.down) (q272.down))) (j (j (q273.down) (q274.down)) (j (q275.down) (q276.down)))) (j (j (j (q277.down) (q278.down)) (j (q279.down) (q280.down))) (j (j (q281.down) (q282.down)) (j (q283.down) (q284.down)))))) (j (j (j (j (j (q285.down) (q286.down)) (j (q287.down) (q288.down))) (j (j (q289.down) (q290.down)) (j (q291.down) (q292.down)))) (j (j (j (q293.down) (q294.down)) (j (q295.down) (q296.down))) (j (j (q297.down) (q298.down)) (j (q299.down) (q300.down))))) (j (j (j (j (q301.down) (q302.down)) (j (q303.down) (q304.down))) (j (j (q305.down) (q306.down)) (j (q307.down) (q308.down)))) (j (j (j (q309.down) (q310.down)) (j (q311.down) (q312.down))) (j (j (q313.down) (q314.down)) (j (q315.down) (q316.down))))))) (j (j (j (j (j (j (q317.down) (q318.down)) (j (q319.down) (q320.down))) (j (j (q321.down) (q322.down)) (j (q323.down) (q324.down)))) (j (j (j (q325.down) (q326.down)) (j (q327.down) (q328.down))) (j (j (q329.down) (q330.down)) (j (q331.down) (q332.down))))) (j (j (j (j (q333.down) (q334.down)) (j (q335.down) (q336.down))) (j (j (q337.down) (q338.down)) (j (q339.down) (q340.down)))) (j (j (j (q341.down) (q342.down)) (j (q343.down) (q344.down))) (j (j (q345.down) (q346.down)) (j (q347.down) (q348.down)))))) (j (j (j (j (j (q349.down) (q350.down)) (j (q351.down) (q352.down))) (j (j (q353.down) (q354.down)) (j (q355.down) (q356.down)))) (j (j (j (q357.down) (q358.down)) (j (q359.down) (q360.down))) (j (j (q361.down) (q362.down)) (j (q363.down) (q364.down))))) (j (j (j (j (q365.down) (q366.down)) (j (q367.down) (q368.down))) (j (j (q369.down) (q370.down)) (j (q371.down) (q372.down)))) (j (j (j (q373.down) (q374.down)) (j (q375.down) (q376.down))) (j (j (q377.down) (q378.down)) (j (q379.down) (q380.down)))))))) (j (j (j (j (j (j (q381.down) (j (q382.down) (q383.down))) (j (j (q384.down) (q385.down)) (j (q386.down) (q387.down)))) (j (j (j (q388.down) (q389.down)) (j (q390.down) (q391.down))) (j (j (q392.down) (q393.down)) (j (q394.down) (q395.down))))) (j (j (j (j (q396.down) (q397.down)) (j (q398.down) (q399.down))) (j (j (q400.down) (q401.down)) (j (q402.down) (q403.down)))) (j (j (j (q404.down) (q405.down)) (j (q406.down) (q407.down))) (j (j (q408.down) (q409.down)) (j (q410.down) (q411.down)))))) (j (j (j (j (j (q412.down) (q413.down)) (j (q414.down) (q415.down))) (j (j (q416.down) (q417.down)) (j (q418.down) (q419.down)))) (j (j (j (q420.down) (q421.down)) (j (q422.down) (q423.down))) (j (j (q424.down) (q425.down)) (j (q426.down) (q427.down))))) (j (j (j (j (q428.down) (q429.down)) (j (q430.down) (q431.down))) (j (j (q432.down) (q433.down)) (j (q434.down) (q435.down)))) (j (j (j (q436.down) (q437.down)) (j (q438.down) (q439.down))) (j (j (q440.down) (q441.down)) (j (q442.down) (q443.down))))))) (j (j (j (j (j (j (q444.down) (q445.down)) (j (q446.down) (q447.down))) (j (j (q448.down) (q449.down)) (j (q450.down) (q451.down)))) (j (j (j (q452.down) (q453.down)) (j (q454.down) (q455.down))) (j (j (q456.down) (q457.down)) (j (q458.down) (q459.down))))) (j (j (j (j (q460.down) (q461.down)) (j (q462.down) (q463.down))) (j (j (q464.down) (q465.down)) (j (q466.down) (q467.down)))) (j (j (j (q468.down) (q469.down)) (j (q470.down) (q471.down))) (j (j (q472.down) (q473.down)) (j (q474.down) (q475.down)))))) (j (j (j (j (j (q476.down) (q477.down)) (j (q478.down) (q479.down))) (j (j (q480.down) (q481.down)) (j (q482.down) (q483.down)))) (j (j (j (q484.down) (q485.down)) (j (q486.down) (q487.down))) (j (j (q488.down) (q489.down)) (j (q490.down) (q491.down))))) (j (j (j (j (q492.down) (q493.down)) (j (q494.down) (q495.down))) (j (j (q496.down) (q497.down)) (j (q498.down) (q499.down)))) (j (j (j (q500.down) (q501.down)) (j (q502.down) (q503.down))) (j (j (q504.down) (q505.down)) (j (q506.down) (q507.down)))))))))) (j (j (j (j (j (j (j (j (q508.down) (j (q509.down) (q510.down))) (j (j (q511.down) (q512.down)) (j (q513.down) (q514.down)))) (j (j (j (q515.down) (q516.down)) (j (q517.down) (q518.down))) (j (j (q519.down) (q520.down)) (j (q521.down) (q522.down))))) (j (j (j (j (q523.down) (q524.down)) (j (q525.down) (q526.down))) (j (j (q527.down) (q528.down)) (j (q529.down) (q530.down)))) (j (j (j (q531.down) (q532.down)) (j (q533.down) (q534.down))) (j (j (q535.down) (q536.down)) (j (q537.down) (q538.down)))))) (j (j (j (j (j (q539.down) (q540.down)) (j (q541.down) (q542.down))) (j (j (q543.down) (q544.down)) (j (q545.down) (q546.down)))) (j (j (j (q547.down) (q548.down)) (j (q549.down) (q550.down))) (j (j (q551.down) (q552.down)) (j (q553.down) (q554.down))))) (j (j (j (j (q555.down) (q556.down)) (j (q557.down) (q558.down))) (j (j (q559.down) (q560.down)) (j (q561.down) (q562.down)))) (j (j (j (q563.down) (q564.down)) (j (q565.down) (q566.down))) (j (j (q567.down) (q568.down)) (j (q569.down) (q570.down))))))) (j (j (j (j (j (j (q571.down) (q572.down)) (j (q573.down) (q574.down))) (j (j (q575.down) (q576.down)) (j (q577.down) (q578.down)))) (j (j (j (q579.down) (q580.down)) (j (q581.down) (q582.down))) (j (j (q583.down) (q584.down)) (j (q585.down) (q586.down))))) (j (j (j (j (q587.down) (q588.down)) (j (q589.down) (q590.down))) (j (j (q591.down) (q592.down)) (j (q593.down) (q594.down)))) (j (j (j (q595.down) (q596.down)) (j (q597.down) (q598.down))) (j (j (q599.down) (q600.down)) (j (q601.down) (q602.down)))))) (j (j (j (j (j (q603.down) (q604.down)) (j (q605.down) (q606.down))) (j (j (q607.down) (q608.down)) (j (q609.down) (q610.down)))) (j (j (j (q611.down) (q612.down)) (j (q613.down) (q614.down))) (j (j (q615.down) (q616.down)) (j (q617.down) (q618.down))))) (j (j (j (j (q619.down) (q620.down)) (j (q621.down) (q622.down))) (j (j (q623.down) (q624.down)) (j (q625.down) (q626.down)))) (j (j (j (q627.down) (q628.down)) (j (q629.down) (q630.down))) (j (j (q631.down) (q632.down)) (j (q633.down) (q634.down)))))))) (j (j (j (j (j (j (q635.down) (j (q636.down) (q637.down))) (j (j (q638.down) (q639.down)) (j (q640.down) (q641.down)))) (j (j (j (q642.down) (q643.down)) (j (q644.down) (q645.down))) (j (j (q646.down) (q647.down)) (j (q648.down) (q649.down))))) (j (j (j (j (q650.down) (q651.down)) (j (q652.down) (q653.down))) (j (j (q654.down) (q655.down)) (j (q656.down) (q657.down)))) (j (j (j (q658.down) (q659.down)) (j (q660.down) (q661.down))) (j (j (q662.down) (q663.down)) (j (q664.down) (q665.down)))))) (j (j (j (j (j (q666.down) (q667.down)) (j (q668.down) (q669.down))) (j (j (q670.down) (q671.down)) (j (q672.down) (q673.down)))) (j (j (j (q674.down) (q675.down)) (j (q676.down) (q677.down))) (j (j (q678.down) (q679.down)) (j (q680.down) (q681.down))))) (j (j (j (j (q682.down) (q683.down)) (j (q684.down) (q685.down))) (j (j (q686.down) (q687.down)) (j (q688.down) (q689.down)))) (j (j (j (q690.down) (q691.down)) (j (q692.down) (q693.down))) (j (j (q694.down) (q695.down)) (j (q696.down) (q697.down))))))) (j (j (j (j (j (j (q698.down) (q699.down)) (j (q700.down) (q701.down))) (j (j (q702.down) (q703.down)) (j (q704.down) (q705.down)))) (j (j (j (q706.down) (q707.down)) (j (q708.down) (q709.down))) (j (j (q710.down) (q711.down)) (j (q712.down) (q713.down))))) (j (j (j (j (q714.down) (q715.down)) (j (q716.down) (q717.down))) (j (j (q718.down) (q719.down)) (j (q720.down) (q721.down)))) (j (j (j (q722.down) (q723.down)) (j (q724.down) (q725.down))) (j (j (q726.down) (q727.down)) (j (q728.down) (q729.down)))))) (j (j (j (j (j (q730.down) (q731.down)) (j (q732.down) (q733.down))) (j (j (q734.down) (q735.down)) (j (q736.down) (q737.down)))) (j (j (j (q738.down) (q739.down)) (j (q740.down) (q741.down))) (j (j (q742.down) (q743.down)) (j (q744.down) (q745.down))))) (j (j (j (j (q746.down) (q747.down)) (j (q748.down) (q749.down))) (j (j (q750.down) (q751.down)) (j (q752.down) (q753.down)))) (j (j (j (q754.down) (q755.down)) (j (q756.down) (q757.down))) (j (j (q758.down) (q759.down)) (j (q760.down) (q761.down))))))))) (j (j (j (j (j (j (j (q762.down) (j (q763.down) (q764.down))) (j (j (q765.down) (q766.down)) (j (q767.down) (q768.down)))) (j (j (j (q769.down) (q770.down)) (j (q771.down) (q772.down))) (j (j (q773.down) (q774.down)) (j (q775.down) (q776.down))))) (j (j (j (j (q777.down) (q778.down)) (j (q779.down) (q780.down))) (j (j (q781.down) (q782.down)) (j (q783.down) (q784.down)))) (j (j (j (q785.down) (q786.down)) (j (q787.down) (q788.down))) (j (j (q789.down) (q790.down)) (j (q791.down) (q792.down)))))) (j (j (j (j (j (q793.down) (q794.down)) (j (q795.down) (q796.down))) (j (j (q797.down) (q798.down)) (j (q799.down) (q800.down)))) (j (j (j (q801.down) (q802.down)) (j (q803.down) (q804.down))) (j (j (q805.down) (q806.down)) (j (q807.down) (q808.down))))) (j (j (j (j (q809.down) (q810.down)) (j (q811.down) (q812.down))) (j (j (q813.down) (q814.down)) (j (q815.down) (q816.down)))) (j (j (j (q817.down) (q818.down)) (j (q819.down) (q820.down))) (j (j (q821.down) (q822.down)) (j (q823.down) (q824.down))))))) (j (j (j (j (j (j (q825.down) (q826.down)) (j (q827.down) (q828.down))) (j (j (q829.down) (q830.down)) (j (q831.down) (q832.down)))) (j (j (j (q833.down) (q834.down)) (j (q835.down) (q836.down))) (j (j (q837.down) (q838.down)) (j (q839.down) (q840.down))))) (j (j (j (j (q841.down) (q842.down)) (j (q843.down) (q844.down))) (j (j (q845.down) (q846.down)) (j (q847.down) (q848.down)))) (j (j (j (q849.down) (q850.down)) (j (q851.down) (q852.down))) (j (j (q853.down) (q854.down)) (j (q855.down) (q856.down)))))) (j (j (j (j (j (q857.down) (q858.down)) (j (q859.down) (q860.down))) (j (j (q861.down) (q862.down)) (j (q863.down) (q864.down)))) (j (j (j (q865.down) (q866.down)) (j (q867.down) (q868.down))) (j (j (q869.down) (q870.down)) (j (q871.down) (q872.down))))) (j (j (j (j (q873.down) (q874.down)) (j (q875.down) (q876.down))) (j (j (q877.down) (q878.down)) (j (q879.down) (q880.down)))) (j (j (j (q881.down) (q882.down)) (j (q883.down) (q884.down))) (j (j (q885.down) (q886.down)) (j (q887.down) (q888.down)))))))) (j (j (j (j (j (j (j (q889.down) (q890.down)) (j (q891.down) (q892.down))) (j (j (q893.down) (q894.down)) (j (q895.down) (q896.down)))) (j (j (j (q897.down) (q898.down)) (j (q899.down) (q900.down))) (j (j (q901.down) (q902.down)) (j (q903.down) (q904.down))))) (j (j (j (j (q905.down) (q906.down)) (j (q907.down) (q908.down))) (j (j (q909.down) (q910.down)) (j (q911.down) (q912.down)))) (j (j (j (q913.down) (q914.down)) (j (q915.down) (q916.down))) (j (j (q917.down) (q918.down)) (j (q919.down) (q920.down)))))) (j (j (j (j (j (q921.down) (q922.down)) (j (q923.down) (q924.down))) (j (j (q925.down) (q926.down)) (j (q927.down) (q928.down)))) (j (j (j (q929.down) (q930.down)) (j (q931.down) (q932.down))) (j (j (q933.down) (q934.down)) (j (q935.down) (q936.down))))) (j (j (j (j (q937.down) (q938.down)) (j (q939.down) (q940.down))) (j (j (q941.down) (q942.down)) (j (q943.down) (q944.down)))) (j (j (j (q945.down) (q946.down)) (j (q947.down) (q948.down))) (j (j (q949.down) (q950.down)) (j (q951.down) (q952.down))))))) (j (j (j (j (j (j (q953.down) (q954.down)) (j (q955.down) (q956.down))) (j (j (q957.down) (q958.down)) (j (q959.down) (q960.down)))) (j (j (j (q961.down) (q962.down)) (j (q963.down) (q964.down))) (j (j (q965.down) (q966.down)) (j (q967.down) (q968.down))))) (j (j (j (j (q969.down) (q970.down)) (j (q971.down) (q972.down))) (j (j (q973.down) (q974.down)) (j (q975.down) (q976.down)))) (j (j (j (q977.down) (q978.down)) (j (q979.down) (q980.down))) (j (j (q981.down) (q982.down)) (j (q983.down) (q984.down)))))) (j (j (j (j (j (q985.down) (q986.down)) (j (q987.down) (q988.down))) (j (j (q989.down) (q990.down)) (j (q991.down) (q992.down)))) (j (j (j (q993.down) (q994.down)) (j (q995.down) (q996.down))) (j (j (q997.down) (q998.down)) (j (q999.down) (q1000.down))))) (j (j (j (j (q1001.down) (q1002.down)) (j (q1003.down) (q1004.down))) (j (j (q1005.down) (q1006.down)) (j (q1007.down) (q1008.down)))) (j (j (j (q1009.down) (q1010.down)) (j (q1011.down) (q1012.down))) (j (j (q1013.down) (q1014.down)) (j (q1015.down) (q1016.down))))))))))) (j (j (j (j (j (j (j (j (j (q1017.down) (j (q1018.down) (q1019.down))) (j (j (q1020.down) (q1021.down)) (j (q1022.down) (q1023.down)))) (j (j (j (q1024.down) (q1025.down)) (j (q1026.down) (q1027.down))) (j (j (q1028.down) (q1029.down)) (j (q1030.down) (q1031.down))))) (j (j (j (j (q1032.down) (q1033.down)) (j (q1034.down) (q1035.down))) (j (j (q1036.down) (q1037.down)) (j (q1038.down) (q1039.down)))) (j (j (j (q1040.down) (q1041.down)) (j (q1042.down) (q1043.down))) (j (j (q1044.down) (q1045.down)) (j (q1046.down) (q1047.down)))))) (j (j (j (j (j (q1048.down) (q1049.down)) (j (q1050.down) (q1051.down))) (j (j (q1052.down) (q1053.down)) (j (q1054.down) (q1055.down)))) (j (j (j (q1056.down) (q1057.down)) (j (q1058.down) (q1059.down))) (j (j (q1060.down) (q1061.down)) (j (q1062.down) (q1063.down))))) (j (j (j (j (q1064.down) (q1065.down)) (j (q1066.down) (q1067.down))) (j (j (q1068.down) (q1069.down)) (j (q1070.down) (q1071.down)))) (j (j (j (q1072.down) (q1073.down)) (j (q1074.down) (q1075.down))) (j (j (q1076.down) (q1077.down)) (j (q1078.down) (q1079.down))))))) (j (j (j (j (j (j (q1080.down) (q1081.down)) (j (q1082.down) (q1083.down))) (j (j (q1084.down) (q1085.down)) (j (q1086.down) (q1087.down)))) (j (j (j (q1088.down) (q1089.down)) (j (q1090.down) (q1091.down))) (j (j (q1092.down) (q1093.down)) (j (q1094.down) (q1095.down))))) (j (j (j (j (q1096.down) (q1097.down)) (j (q1098.down) (q1099.down))) (j (j (q1100.down) (q1101.down)) (j (q1102.down) (q1103.down)))) (j (j (j (q1104.down) (q1105.down)) (j (q1106.down) (q1107.down))) (j (j (q1108.down) (q1109.down)) (j (q1110.down) (q1111.down)))))) (j (j (j (j (j (q1112.down) (q1113.down)) (j (q1114.down) (q1115.down))) (j (j (q1116.down) (q1117.down)) (j (q1118.down) (q1119.down)))) (j (j (j (q1120.down) (q1121.down)) (j (q1122.down) (q1123.down))) (j (j (q1124.down) (q1125.down)) (j (q1126.down) (q1127.down))))) (j (j (j (j (q1128.down) (q1129.down)) (j (q1130.down) (q1131.down))) (j (j (q1132.down) (q1133.down)) (j (q1134.down) (q1135.down)))) (j (j (j (q1136.down) (q1137.down)) (j (q1138.down) (q1139.down))) (j (j (q1140.down) (q1141.down)) (j (q1142.down) (q1143.down)))))))) (j (j (j (j (j (j (q1144.down) (j (q1145.down) (q1146.down))) (j (j (q1147.down) (q1148.down)) (j (q1149.down) (q1150.down)))) (j (j (j (q1151.down) (q1152.down)) (j (q1153.down) (q1154.down))) (j (j (q1155.down) (q1156.down)) (j (q1157.down) (q1158.down))))) (j (j (j (j (q1159.down) (q1160.down)) (j (q1161.down) (q1162.down))) (j (j (q1163.down) (q1164.down)) (j (q1165.down) (q1166.down)))) (j (j (j (q1167.down) (q1168.down)) (j (q1169.down) (q1170.down))) (j (j (q1171.down) (q1172.down)) (j (q1173.down) (q1174.down)))))) (j (j (j (j (j (q1175.down) (q1176.down)) (j (q1177.down) (q1178.down))) (j (j (q1179.down) (q1180.down)) (j (q1181.down) (q1182.down)))) (j (j (j (q1183.down) (q1184.down)) (j (q1185.down) (q1186.down))) (j (j (q1187.down) (q1188.down)) (j (q1189.down) (q1190.down))))) (j (j (j (j (q1191.down) (q1192.down)) (j (q1193.down) (q1194.down))) (j (j (q1195.down) (q1196.down)) (j (q1197.down) (q1198.down)))) (j (j (j (q1199.down) (q1200.down)) (j (q1201.down) (q1202.down))) (j (j (q1203.down) (q1204.down)) (j (q1205.down) (q1206.down))))))) (j (j (j (j (j (j (q1207.down) (q1208.down)) (j (q1209.down) (q1210.down))) (j (j (q1211.down) (q1212.down)) (j (q1213.down) (q1214.down)))) (j (j (j (q1215.down) (q1216.down)) (j (q1217.down) (q1218.down))) (j (j (q1219.down) (q1220.down)) (j (q1221.down) (q1222.down))))) (j (j (j (j (q1223.down) (q1224.down)) (j (q1225.down) (q1226.down))) (j (j (q1227.down) (q1228.down)) (j (q1229.down) (q1230.down)))) (j (j (j (q1231.down) (q1232.down)) (j (q1233.down) (q1234.down))) (j (j (q1235.down) (q1236.down)) (j (q1237.down) (q1238.down)))))) (j (j (j (j (j (q1239.down) (q1240.down)) (j (q1241.down) (q1242.down))) (j (j (q1243.down) (q1244.down)) (j (q1245.down) (q1246.down)))) (j (j (j (q1247.down) (q1248.down)) (j (q1249.down) (q1250.down))) (j (j (q1251.down) (q1252.down)) (j (q1253.down) (q1254.down))))) (j (j (j (j (q1255.down) (q1256.down)) (j (q1257.down) (q1258.down))) (j (j (q1259.down) (q1260.down)) (j (q1261.down) (q1262.down)))) (j (j (j (q1263.down) (q1264.down)) (j (q1265.down) (q1266.down))) (j (j (q1267.down) (q1268.down)) (j (q1269.down) (q1270.down))))))))) (j (j (j (j (j (j (j (q1271.down) (j (q1272.down) (q1273.down))) (j (j (q1274.down) (q1275.down)) (j (q1276.down) (q1277.down)))) (j (j (j (q1278.down) (q1279.down)) (j (q1280.down) (q1281.down))) (j (j (q1282.down) (q1283.down)) (j (q1284.down) (q1285.down))))) (j (j (j (j (q1286.down) (q1287.down)) (j (q1288.down) (q1289.down))) (j (j (q1290.down) (q1291.down)) (j (q1292.down) (q1293.down)))) (j (j (j (q1294.down) (q1295.down)) (j (q1296.down) (q1297.down))) (j (j (q1298.down) (q1299.down)) (j (q1300.down) (q1301.down)))))) (j (j (j (j (j (q1302.down) (q1303.down)) (j (q1304.down) (q1305.down))) (j (j (q1306.down) (q1307.down)) (j (q1308.down) (q1309.down)))) (j (j (j (q1310.down) (q1311.down)) (j (q1312.down) (q1313.down))) (j (j (q1314.down) (q1315.down)) (j (q1316.down) (q1317.down))))) (j (j (j (j (q1318.down) (q1319.down)) (j (q1320.down) (q1321.down))) (j (j (q1322.down) (q1323.down)) (j (q1324.down) (q1325.down)))) (j (j (j (q1326.down) (q1327.down)) (j (q1328.down) (q1329.down))) (j (j (q1330.down) (q1331.down)) (j (q1332.down) (q1333.down))))))) (j (j (j (j (j (j (q1334.down) (q1335.down)) (j (q1336.down) (q1337.down))) (j (j (q1338.down) (q1339.down)) (j (q1340.down) (q1341.down)))) (j (j (j (q1342.down) (q1343.down)) (j (q1344.down) (q1345.down))) (j (j (q1346.down) (q1347.down)) (j (q1348.down) (q1349.down))))) (j (j (j (j (q1350.down) (q1351.down)) (j (q1352.down) (q1353.down))) (j (j (q1354.down) (q1355.down)) (j (q1356.down) (q1357.down)))) (j (j (j (q1358.down) (q1359.down)) (j (q1360.down) (q1361.down))) (j (j (q1362.down) (q1363.down)) (j (q1364.down) (q1365.down)))))) (j (j (j (j (j (q1366.down) (q1367.down)) (j (q1368.down) (q1369.down))) (j (j (q1370.down) (q1371.down)) (j (q1372.down) (q1373.down)))) (j (j (j (q1374.down) (q1375.down)) (j (q1376.down) (q1377.down))) (j (j (q1378.down) (q1379.down)) (j (q1380.down) (q1381.down))))) (j (j (j (j (q1382.down) (q1383.down)) (j (q1384.down) (q1385.down))) (j (j (q1386.down) (q1387.down)) (j (q1388.down) (q1389.down)))) (j (j (j (q1390.down) (q1391.down)) (j (q1392.down) (q1393.down))) (j (j (q1394.down) (q1395.down)) (j (q1396.down) (q1397.down)))))))) (j (j (j (j (j (j (j (q1398.down) (q1399.down)) (j (q1400.down) (q1401.down))) (j (j (q1402.down) (q1403.down)) (j (q1404.down) (q1405.down)))) (j (j (j (q1406.down) (q1407.down)) (j (q1408.down) (q1409.down))) (j (j (q1410.down) (q1411.down)) (j (q1412.down) (q1413.down))))) (j (j (j (j (q1414.down) (q1415.down)) (j (q1416.down) (q1417.down))) (j (j (q1418.down) (q1419.down)) (j (q1420.down) (q1421.down)))) (j (j (j (q1422.down) (q1423.down)) (j (q1424.down) (q1425.down))) (j (j (q1426.down) (q1427.down)) (j (q1428.down) (q1429.down)))))) (j (j (j (j (j (q1430.down) (q1431.down)) (j (q1432.down) (q1433.down))) (j (j (q1434.down) (q1435.down)) (j (q1436.down) (q1437.down)))) (j (j (j (q1438.down) (q1439.down)) (j (q1440.down) (q1441.down))) (j (j (q1442.down) (q1443.down)) (j (q1444.down) (q1445.down))))) (j (j (j (j (q1446.down) (q1447.down)) (j (q1448.down) (q1449.down))) (j (j (q1450.down) (q1451.down)) (j (q1452.down) (q1453.down)))) (j (j (j (q1454.down) (q1455.down)) (j (q1456.down) (q1457.down))) (j (j (q1458.down) (q1459.down)) (j (q1460.down) (q1461.down))))))) (j (j (j (j (j (j (q1462.down) (q1463.down)) (j (q1464.down) (q1465.down))) (j (j (q1466.down) (q1467.down)) (j (q1468.down) (q1469.down)))) (j (j (j (q1470.down) (q1471.down)) (j (q1472.down) (q1473.down))) (j (j (q1474.down) (q1475.down)) (j (q1476.down) (q1477.down))))) (j (j (j (j (q1478.down) (q1479.down)) (j (q1480.down) (q1481.down))) (j (j (q1482.down) (q1483.down)) (j (q1484.down) (q1485.down)))) (j (j (j (q1486.down) (q1487.down)) (j (q1488.down) (q1489.down))) (j (j (q1490.down) (q1491.down)) (j (q1492.down) (q1493.down)))))) (j (j (j (j (j (q1494.down) (q1495.down)) (j (q1496.down) (q1497.down))) (j (j (q1498.down) (q1499.down)) (j (q1500.down) (q1501.down)))) (j (j (j (q1502.down) (q1503.down)) (j (q1504.down) (q1505.down))) (j (j (q1506.down) (q1507.down)) (j (q1508.down) (q1509.down))))) (j (j (j (j (q1510.down) (q1511.down)) (j (q1512.down) (q1513.down))) (j (j (q1514.down) (q1515.down)) (j (q1516.down) (q1517.down)))) (j (j (j (q1518.down) (q1519.down)) (j (q1520.down) (q1521.down))) (j (j (q1522.down) (q1523.down)) (j (q1524.down) (q1525.down)))))))))) (j (j (j (j (j (j (j (j (q1526.down) (j (q1527.down) (q1528.down))) (j (j (q1529.down) (q1530.down)) (j (q1531.down) (q1532.down)))) (j (j (j (q1533.down) (q1534.down)) (j (q1535.down) (q1536.down))) (j (j (q1537.down) (q1538.down)) (j (q1539.down) (q1540.down))))) (j (j (j (j (q1541.down) (q1542.down)) (j (q1543.down) (q1544.down))) (j (j (q1545.down) (q1546.down)) (j (q1547.down) (q1548.down)))) (j (j (j (q1549.down) (q1550.down)) (j (q1551.down) (q1552.down))) (j (j (q1553.down) (q1554.down)) (j (q1555.down) (q1556.down)))))) (j (j (j (j (j (q1557.down) (q1558.down)) (j (q1559.down) (q1560.down))) (j (j (q1561.down) (q1562.down)) (j (q1563.down) (q1564.down)))) (j (j (j (q1565.down) (q1566.down)) (j (q1567.down) (q1568.down))) (j (j (q1569.down) (q1570.down)) (j (q1571.down) (q1572.down))))) (j (j (j (j (q1573.down) (q1574.down)) (j (q1575.down) (q1576.down))) (j (j (q1577.down) (q1578.down)) (j (q1579.down) (q1580.down)))) (j (j (j (q1581.down) (q1582.down)) (j (q1583.down) (q1584.down))) (j (j (q1585.down) (q1586.down)) (j (q1587.down) (q1588.down))))))) (j (j (j (j (j (j (q1589.down) (q1590.down)) (j (q1591.down) (q1592.down))) (j (j (q1593.down) (q1594.down)) (j (q1595.down) (q1596.down)))) (j (j (j (q1597.down) (q1598.down)) (j (q1599.down) (q1600.down))) (j (j (q1601.down) (q1602.down)) (j (q1603.down) (q1604.down))))) (j (j (j (j (q1605.down) (q1606.down)) (j (q1607.down) (q1608.down))) (j (j (q1609.down) (q1610.down)) (j (q1611.down) (q1612.down)))) (j (j (j (q1613.down) (q1614.down)) (j (q1615.down) (q1616.down))) (j (j (q1617.down) (q1618.down)) (j (q1619.down) (q1620.down)))))) (j (j (j (j (j (q1621.down) (q1622.down)) (j (q1623.down) (q1624.down))) (j (j (q1625.down) (q1626.down)) (j (q1627.down) (q1628.down)))) (j (j (j (q1629.down) (q1630.down)) (j (q1631.down) (q1632.down))) (j (j (q1633.down) (q1634.down)) (j (q1635.down) (q1636.down))))) (j (j (j (j (q1637.down) (q1638.down)) (j (q1639.down) (q1640.down))) (j (j (q1641.down) (q1642.down)) (j (q1643.down) (q1644.down)))) (j (j (j (q1645.down) (q1646.down)) (j (q1647.down) (q1648.down))) (j (j (q1649.down) (q1650.down)) (j (q1651.down) (q1652.down)))))))) (j (j (j (j (j (j (q1653.down) (j (q1654.down) (q1655.down))) (j (j (q1656.down) (q1657.down)) (j (q1658.down) (q1659.down)))) (j (j (j (q1660.down) (q1661.down)) (j (q1662.down) (q1663.down))) (j (j (q1664.down) (q1665.down)) (j (q1666.down) (q1667.down))))) (j (j (j (j (q1668.down) (q1669.down)) (j (q1670.down) (q1671.down))) (j (j (q1672.down) (q1673.down)) (j (q1674.down) (q1675.down)))) (j (j (j (q1676.down) (q1677.down)) (j (q1678.down) (q1679.down))) (j (j (q1680.down) (q1681.down)) (j (q1682.down) (q1683.down)))))) (j (j (j (j (j (q1684.down) (q1685.down)) (j (q1686.down) (q1687.down))) (j (j (q1688.down) (q1689.down)) (j (q1690.down) (q1691.down)))) (j (j (j (q1692.down) (q1693.down)) (j (q1694.down) (q1695.down))) (j (j (q1696.down) (q1697.down)) (j (q1698.down) (q1699.down))))) (j (j (j (j (q1700.down) (q1701.down)) (j (q1702.down) (q1703.down))) (j (j (q1704.down) (q1705.down)) (j (q1706.down) (q1707.down)))) (j (j (j (q1708.down) (q1709.down)) (j (q1710.down) (q1711.down))) (j (j (q1712.down) (q1713.down)) (j (q1714.down) (q1715.down))))))) (j (j (j (j (j (j (q1716.down) (q1717.down)) (j (q1718.down) (q1719.down))) (j (j (q1720.down) (q1721.down)) (j (q1722.down) (q1723.down)))) (j (j (j (q1724.down) (q1725.down)) (j (q1726.down) (q1727.down))) (j (j (q1728.down) (q1729.down)) (j (q1730.down) (q1731.down))))) (j (j (j (j (q1732.down) (q1733.down)) (j (q1734.down) (q1735.down))) (j (j (q1736.down) (q1737.down)) (j (q1738.down) (q1739.down)))) (j (j (j (q1740.down) (q1741.down)) (j (q1742.down) (q1743.down))) (j (j (q1744.down) (q1745.down)) (j (q1746.down) (q1747.down)))))) (j (j (j (j (j (q1748.down) (q1749.down)) (j (q1750.down) (q1751.down))) (j (j (q1752.down) (q1753.down)) (j (q1754.down) (q1755.down)))) (j (j (j (q1756.down) (q1757.down)) (j (q1758.down) (q1759.down))) (j (j (q1760.down) (q1761.down)) (j (q1762.down) (q1763.down))))) (j (j (j (j (q1764.down) (q1765.down)) (j (q1766.down) (q1767.down))) (j (j (q1768.down) (q1769.down)) (j (q1770.down) (q1771.down)))) (j (j (j (q1772.down) (q1773.down)) (j (q1774.down) (q1775.down))) (j (j (q1776.down) (q1777.down)) (j (q1778.down) (q1779.down))))))))) (j (j (j (j (j (j (j (q1780.down) (j (q1781.down) (q1782.down))) (j (j (q1783.down) (q1784.down)) (j (q1785.down) (q1786.down)))) (j (j (j (q1787.down) (q1788.down)) (j (q1789.down) (q1790.down))) (j (j (q1791.down) (q1792.down)) (j (q1793.down) (q1794.down))))) (j (j (j (j (q1795.down) (q1796.down)) (j (q1797.down) (q1798.down))) (j (j (q1799.down) (q1800.down)) (j (q1801.down) (q1802.down)))) (j (j (j (q1803.down) (q1804.down)) (j (q1805.down) (q1806.down))) (j (j (q1807.down) (q1808.down)) (j (q1809.down) (q1810.down)))))) (j (j (j (j (j (q1811.down) (q1812.down)) (j (q1813.down) (q1814.down))) (j (j (q1815.down) (q1816.down)) (j (q1817.down) (q1818.down)))) (j (j (j (q1819.down) (q1820.down)) (j (q1821.down) (q1822.down))) (j (j (q1823.down) (q1824.down)) (j (q1825.down) (q1826.down))))) (j (j (j (j (q1827.down) (q1828.down)) (j (q1829.down) (q1830.down))) (j (j (q1831.down) (q1832.down)) (j (q1833.down) (q1834.down)))) (j (j (j (q1835.down) (q1836.down)) (j (q1837.down) (q1838.down))) (j (j (q1839.down) (q1840.down)) (j (q1841.down) (q1842.down))))))) (j (j (j (j (j (j (q1843.down) (q1844.down)) (j (q1845.down) (q1846.down))) (j (j (q1847.down) (q1848.down)) (j (q1849.down) (q1850.down)))) (j (j (j (q1851.down) (q1852.down)) (j (q1853.down) (q1854.down))) (j (j (q1855.down) (q1856.down)) (j (q1857.down) (q1858.down))))) (j (j (j (j (q1859.down) (q1860.down)) (j (q1861.down) (q1862.down))) (j (j (q1863.down) (q1864.down)) (j (q1865.down) (q1866.down)))) (j (j (j (q1867.down) (q1868.down)) (j (q1869.down) (q1870.down))) (j (j (q1871.down) (q1872.down)) (j (q1873.down) (q1874.down)))))) (j (j (j (j (j (q1875.down) (q1876.down)) (j (q1877.down) (q1878.down))) (j (j (q1879.down) (q1880.down)) (j (q1881.down) (q1882.down)))) (j (j (j (q1883.down) (q1884.down)) (j (q1885.down) (q1886.down))) (j (j (q1887.down) (q1888.down)) (j (q1889.down) (q1890.down))))) (j (j (j (j (q1891.down) (q1892.down)) (j (q1893.down) (q1894.down))) (j (j (q1895.down) (q1896.down)) (j (q1897.down) (q1898.down)))) (j (j (j (q1899.down) (q1900.down)) (j (q1901.down) (q1902.down))) (j (j (q1903.down) (q1904.down)) (j (q1905.down) (q1906.down)))))))) (j (j (j (j (j (j (j (q1907.down) (q1908.down)) (j (q1909.down) (q1910.down))) (j (j (q1911.down) (q1912.down)) (j (q1913.down) (q1914.down)))) (j (j (j (q1915.down) (q1916.down)) (j (q1917.down) (q1918.down))) (j (j (q1919.down) (q1920.down)) (j (q1921.down) (q1922.down))))) (j (j (j (j (q1923.down) (q1924.down)) (j (q1925.down) (q1926.down))) (j (j (q1927.down) (q1928.down)) (j (q1929.down) (q1930.down)))) (j (j (j (q1931.down) (q1932.down)) (j (q1933.down) (q1934.down))) (j (j (q1935.down) (q1936.down)) (j (q1937.down) (q1938.down)))))) (j (j (j (j (j (q1939.down) (q1940.down)) (j (q1941.down) (q1942.down))) (j (j (q1943.down) (q1944.down)) (j (q1945.down) (q1946.down)))) (j (j (j (q1947.down) (q1948.down)) (j (q1949.down) (q1950.down))) (j (j (q1951.down) (q1952.down)) (j (q1953.down) (q1954.down))))) (j (j (j (j (q1955.down) (q1956.down)) (j (q1957.down) (q1958.down))) (j (j (q1959.down) (q1960.down)) (j (q1961.down) (q1962.down)))) (j (j (j (q1963.down) (q1964.down)) (j (q1965.down) (q1966.down))) (j (j (q1967.down) (q1968.down)) (j (q1969.down) (q1970.down))))))) (j (j (j (j (j (j (q1971.down) (q1972.down)) (j (q1973.down) (q1974.down))) (j (j (q1975.down) (q1976.down)) (j (q1977.down) (q1978.down)))) (j (j (j (q1979.down) (q1980.down)) (j (q1981.down) (q1982.down))) (j (j (q1983.down) (q1984.down)) (j (q1985.down) (q1986.down))))) (j (j (j (j (q1987.down) (q1988.down)) (j (q1989.down) (q1990.down))) (j (j (q1991.down) (q1992.down)) (j (q1993.down) (q1994.down)))) (j (j (j (q1995.down) (q1996.down)) (j (q1997.down) (q1998.down))) (j (j (q1999.down) (q2000.down)) (j (q2001.down) (q2002.down)))))) (j (j (j (j (j (q2003.down) (q2004.down)) (j (q2005.down) (q2006.down))) (j (j (q2007.down) (q2008.down)) (j (q2009.down) (q2010.down)))) (j (j (j (q2011.down) (q2012.down)) (j (q2013.down) (q2014.down))) (j (j (q2015.down) (q2016.down)) (j (q2017.down) (q2018.down))))) (j (j (j (j (q2019.down) (q2020.down)) (j (q2021.down) (q2022.down))) (j (j (q2023.down) (q2024.down)) (j (q2025.down) (q2026.down)))) (j (j (j (q2027.down) (q2028.down)) (j (q2029.down) (q2030.down))) (j (j (q2031.down) (q2032.down)) (j (q2033.down) (q2034.down)))))))))))

end ThetaLongHaul.Packed


/-! Own generalized packed bound and small finite companion certificates.
No external proof code. Plans and credits: FINITE_COMPANIONS_SKETCH.md. -/
namespace ThetaLongHaul.Packed
open Finset

def validateBound (bound p g L h X : ℕ) : Bool :=
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
  decide (V < BN - 1) && decide (n ^ 2 + 2 * bound * p < 8 * C)

lemma validateBound_sound (bound p g L h X : ℕ) (hp : p.Prime) (hop : Odd p)
    (hc : validateBound bound p g L h X = true) :
    (bound : ℤ) * (p : ℤ) < Arxiv.«2501.03234».S p := by
  unfold validateBound at hc
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
  have hcount' : (p - 1) ^ 2 + 2 * bound * p < 8 * packedParityCount L (p - 1) X := by
    simpa only [packedParityCount, cyclicFold, pow_mul, pow_two] using hcount
  have hs := two_mul_S_eq_packedParityCount p g L X _ hp hop H hr' hB hfold'
  have hi : ((p - 1) ^ 2 + 2 * bound * p : ℕ) < 8 * packedParityCount L (p - 1) X := hcount'
  have hi' : (((p - 1) ^ 2 + 2 * bound * p : ℕ) : ℤ) <
      8 * (packedParityCount L (p - 1) X : ℤ) := by exact_mod_cast hi
  push_cast at hi'
  nlinarith



def smallThreshold (p : ℕ) : ℕ := if p≤233 then 1 else 2

def smallRecordCheck (record : ℕ) : Bool :=
  let p := recordP record
  let g := (record >>> 17) &&& (powTwo 17 - 1)
  let d := record >>> 34
  let h := p.log2 + 1
  let L := 2*h
  let index := (p-1)/d
  let pad := powTwo ((d-1).log2+1)
  decide (5<p) && validateBound (smallThreshold p) p g L h
    (packedOrbit p g d index L pad)

lemma smallRecordCheck_sound (record : ℕ) (hp : (recordP record).Prime)
    (hc : smallRecordCheck record=true) :
    (smallThreshold (recordP record) : ℤ)*(recordP record : ℤ)<
      Arxiv.«2501.03234».S (recordP record) := by
  unfold smallRecordCheck at hc
  dsimp only at hc
  rw [Bool.and_eq_true,decide_eq_true_eq] at hc
  have hop : Odd (recordP record) := Nat.odd_iff.mpr
    (hp.eq_two_or_odd.resolve_left (by omega))
  exact validateBound_sound (smallThreshold (recordP record))
    (recordP record) _ _ _ _ hp hop hc.2

def smallGoodRange (lo hi : ℕ) : Prop :=
  ∀ p : ℕ, lo≤p → p<hi → p.Prime →
    (smallThreshold p : ℤ)*(p : ℤ)<Arxiv.«2501.03234».S p

lemma smallGoodRange_join {lo mid hi : ℕ}
    (ha : smallGoodRange lo mid) (hb : smallGoodRange mid hi) :
    smallGoodRange lo hi := by
  intro p hlo hhi hp
  by_cases hm : p < mid
  · exact ha p hlo hm hp
  · exact hb p (by omega) hhi hp

def smallBlockCheck (records : List ℕ) (lo hi : ℕ) : Bool :=
  records.all smallRecordCheck && coverageCheck records (hi-lo) lo

lemma smallBlockCheck_sound (records : List ℕ) {lo hi : ℕ}
    (hc : smallBlockCheck records lo hi=true) : smallGoodRange lo hi := by
  rw [smallBlockCheck,Bool.and_eq_true] at hc
  intro p hlo hhi hp
  have hcovered := coverageCheck_sound records (hi-lo) lo hc.2 p hlo (by omega) hp
  rcases covered_sound records p hcovered with ⟨record,hr,he⟩
  have hrecord := List.all_eq_true.mp hc.1 record hr
  subst p
  exact smallRecordCheck_sound record hp hrecord

set_option maxRecDepth 100000 in
def smallBlock0 : PLift (smallGoodRange 6 29) :=
  ⟨smallBlockCheck_sound [0xc000a0007,0x28000c000b,0x30000e000d,0x2000060011,0x4800140013,0x2c001c0017] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock1 : PLift (smallGoodRange 29 53) :=
  ⟨smallBlockCheck_sound [0x70001e001d,0x140006001f,0x9000260025,0x50003a0029,0x380038002b,0x5c0028002f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock2 : PLift (smallGoodRange 53 79) :=
  ⟨smallBlockCheck_sound [0xd000360035,0xe8003c003b,0xf0003e003d,0x10800440043,0x8c00820047,0x2400280049] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock3 : PLift (smallGoodRange 79 107) :=
  ⟨smallBlockCheck_sound [0x9c0046004f,0x14800540053,0x2c001c0059,0xc0000e0061,0x19000660065,0xcc00a80067] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock4 : PLift (smallGoodRange 107 139) :=
  ⟨smallBlockCheck_sound [0x1a8006c006b,0x90005e006d,0x7000180071,0x1c00ac007f,0x20800840083,0x11000a80089] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock5 : PLift (smallGoodRange 139 173) :=
  ⟨smallBlockCheck_sound [0x228008c008b,0x25000960095,0x3c00b20097,0xd0011c009d,0x28800a400a3,0x14c00b400a7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock6 : PLift (smallGoodRange 173 199) :=
  ⟨smallBlockCheck_sound [0x2b000ae00ad,0x2c800b400b3,0x2d000b600b5,0x17c00f800bf,0x180014e00c1,0x31000c600c5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock7 : PLift (smallGoodRange 199 239) :=
  ⟨smallBlockCheck_sound [0x18c017a00c7,0x34800d400d3,0x94016800df,0x38800e400e3,0x130003a00e5,0x7401c800e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock8 : PLift (smallGoodRange 239 271) :=
  ⟨smallBlockCheck_sound [0x1dc008c00ef,0x60011c00f1,0xc801b000fb,0x4001300101,0x20c006e0107,0x430010e010d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock9 : PLift (smallGoodRange 271 311) :=
  ⟨smallBlockCheck_sound [0x21c0060010f,0x17001600115,0x11801c40119,0x17800f6011b,0x49001260125,0x19802140133] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock10 : PLift (smallGoodRange 311 349) :=
  ⟨smallBlockCheck_sound [0x26c00420137,0x27000780139,0x4f0013e013d,0x780274014b,0x5401c80151,0x568015c015b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock11 : PLift (smallGoodRange 349 383) :=
  ⟨smallBlockCheck_sound [0x570015e015d,0x16001c80161,0x2cc017a0167,0x2dc01be016f,0x5d001760175,0x5e8017c017b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock12 : PLift (smallGoodRange 383 421) :=
  ⟨smallBlockCheck_sound [0x2fc00f6017f,0x61001860185,0xb0020e018d,0x32001c60191,0x33001380199,0x68801a401a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock13 : PLift (smallGoodRange 421 457) :=
  ⟨smallBlockCheck_sound [0x69001a601a5,0xac00e001af,0x12002e001b1,0x12401c801b7,0x6e801bc01bb,0x380001e01c1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock14 : PLift (smallGoodRange 457 491) :=
  ⟨smallBlockCheck_sound [0x13000b801c9,0x73001ce01cd,0x39c029a01cf,0x74801d401d3,0x3bc029a01df,0x3cc018c01e7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock15 : PLift (smallGoodRange 491 541) :=
  ⟨smallBlockCheck_sound [0x7a801ec01eb,0x29803ca01f3,0x3ec029401f7,0x7f001fe01fd,0x41001100209,0x828020c020b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock16 : PLift (smallGoodRange 541 577) :=
  ⟨smallBlockCheck_sound [0x870021e021d,0x88802240223,0x8b0022e022d,0x8c802340233,0x47003020239,0x1c8031e023b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock17 : PLift (smallGoodRange 577 613) :=
  ⟨smallBlockCheck_sound [0x24002980241,0x928024c024b,0x25002180251,0x4ac04080257,0x64015a0259,0x4bc03fc025f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock18 : PLift (smallGoodRange 613 647) :=
  ⟨smallBlockCheck_sound [0x99002660265,0x26803ca0269,0x9a8026c026b,0xb4028a0277,0x10003920281,0x358033c0283] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock19 : PLift (smallGoodRange 647 683) :=
  ⟨smallBlockCheck_sound [0x50c04ea0287,0xa30028e028d,0xa4802940293,0xa5002960295,0xc0030e02a1,0xa9002a602a5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock20 : PLift (smallGoodRange 683 733) :=
  ⟨smallBlockCheck_sound [0x5801ee02ab,0x398022002b3,0xaf002be02bd,0xb1002c602c5,0x59c045a02cf,0x1e402a002d7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock21 : PLift (smallGoodRange 733 769) :=
  ⟨smallBlockCheck_sound [0x3d002d402dd,0x3d804e402e3,0x5cc006602e7,0x5dc036002ef,0xbd002f602f5,0x5f002b002f9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock22 : PLift (smallGoodRange 769 821) :=
  ⟨smallBlockCheck_sound [0x600027c0301,0xc1003060305,0xc4803140313,0xc70031e031d,0x65002660329,0x43804ea032b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock23 : PLift (smallGoodRange 821 857) :=
  ⟨smallBlockCheck_sound [0xcd003360335,0x66c05520337,0xce8033c033b,0xcf0033e033d,0x68c03640347,0xd5003560355] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock24 : PLift (smallGoodRange 857 887) :=
  ⟨smallBlockCheck_sound [0x6b002b60359,0xd68035c035b,0x6bc045a035f,0xdb0036e036d,0xdc027e0371,0xdc803740373] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock25 : PLift (smallGoodRange 887 941) :=
  ⟨smallBlockCheck_sound [0x6ec06240377,0xe28038c038b,0x16c00c2038f,0x26405be0397,0x740065203a1,0x1d4050e03a9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock26 : PLift (smallGoodRange 941 983) :=
  ⟨smallBlockCheck_sound [0xeb003ae03ad,0xec803b403b3,0x11001e203b9,0x78c076203c7,0x30804fc03cb,0x7a000d403d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock27 : PLift (smallGoodRange 983 1021) :=
  ⟨smallBlockCheck_sound [0x7ac05ec03d7,0x7bc061a03df,0x530040803e5,0x7e0023a03f1,0x170028c03f5,0xfe803fc03fb] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock28 : PLift (smallGoodRange 1021 1061) :=
  ⟨smallBlockCheck_sound [0x550070603fd,0x80c022e0407,0x40803fa0409,0x81c05a8040f,0x418022c0419,0x5780574041b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock29 : PLift (smallGoodRange 1061 1097) :=
  ⟨smallBlockCheck_sound [0x109004260425,0x84c007a0427,0x59006a4042d,0x87c041e043f,0x110804440443,0x5b002660445] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock30 : PLift (smallGoodRange 1097 1151) :=
  ⟨smallBlockCheck_sound [0x448083c0449,0x7407fa044f,0x115004560455,0x1170045e045d,0x118804640463,0x8d0073c0469] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock31 : PLift (smallGoodRange 1151 1193) :=
  ⟨smallBlockCheck_sound [0x8fc08ce047f,0x480073a0481,0x29805ba048b,0x124804940493,0x3b0030a049d,0x128804a404a3] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock32 : PLift (smallGoodRange 1193 1231) :=
  ⟨smallBlockCheck_sound [0x4a808e204a9,0x4b004c804b1,0x12f004be04bd,0x260074e04c1,0x98c04ea04c7,0x133004ce04cd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock33 : PLift (smallGoodRange 1231 1283) :=
  ⟨smallBlockCheck_sound [0x99c061a04cf,0x135004d604d5,0x27000d404e1,0x13a804ec04eb,0x13f004fe04fd,0x9fc041a04ff] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock34 : PLift (smallGoodRange 1283 1307) :=
  ⟨smallBlockCheck_sound [0x140805040503,0x28409980509,0x1428050c050b,0xa2009500511,0x145005160515,0xa2c02f00517] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock35 : PLift (smallGoodRange 1307 1373) :=
  ⟨smallBlockCheck_sound [0x1468051c051b,0xa4c073e0527,0xf00a280529,0x3740488052f,0xaa0080c0551,0xaac057c0557] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock36 : PLift (smallGoodRange 1373 1429) :=
  ⟨smallBlockCheck_sound [0x1570055e055d,0x159005660565,0x3a402660577,0xb0004b00581,0x3b40300058f,0x164805940593] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock37 : PLift (smallGoodRange 1429 1459) :=
  ⟨smallBlockCheck_sound [0x15005840595,0x2cc01a20599,0xb3c07ae059f,0xb4c010205a7,0x16a805ac05ab,0x16b005ae05ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock38 : PLift (smallGoodRange 1459 1493) :=
  ⟨smallBlockCheck_sound [0x798011c05b3,0x3d401d005bf,0x5c8033205c9,0x172805cc05cb,0xb9c066e05cf,0xba0017e05d1] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock39 : PLift (smallGoodRange 1493 1549) :=
  ⟨smallBlockCheck_sound [0x175005d605d5,0x176805dc05db,0xbcc016005e7,0x17c805f405f3,0x17e805fc05fb,0xc0c09b00607] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock40 : PLift (smallGoodRange 1549 1583) :=
  ⟨smallBlockCheck_sound [0x1830060e060d,0x3080acc0611,0xc2c080c0617,0xc3c0c06061f,0x188806240623,0x838085a062b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock41 : PLift (smallGoodRange 1583 1619) :=
  ⟨smallBlockCheck_sound [0xc5c00e8062f,0x8500700063d,0x64004720641,0xc8c0bf80647,0x324084e0649,0xd00562064d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock42 : PLift (smallGoodRange 1619 1667) :=
  ⟨smallBlockCheck_sound [0x194806540653,0x195006560655,0x8780336065b,0x199006660665,0x17001480679,0xcfc0238067f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock43 : PLift (smallGoodRange 1667 1721) :=
  ⟨smallBlockCheck_sound [0x1a0806840683,0x1a1006860685,0x1a70069e069d,0xd40063406a1,0x8d8013806a3,0x3d0033606ad] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock44 : PLift (smallGoodRange 1721 1759) :=
  ⟨smallBlockCheck_sound [0x35c012406b9,0x8f8045e06bb,0x1b1006c606c5,0x1b3006ce06cd,0x1b4806d406d3,0x248080c06d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock45 : PLift (smallGoodRange 1759 1811) :=
  ⟨smallBlockCheck_sound [0xdbc033806df,0x128053606f1,0xdec009e06f7,0x1be806fc06fb,0x95004d406fd,0x6408980709] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock46 : PLift (smallGoodRange 1811 1871) :=
  ⟨smallBlockCheck_sound [0x5a8036a0713,0xe3c0a76071f,0x4c4007c0727,0xe6c07620737,0x1d1007460745,0x1d28074c074b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock47 : PLift (smallGoodRange 1871 1907) :=
  ⟨smallBlockCheck_sound [0xe9c02cc074f,0xea00c820751,0x1d5007560755,0xeac01260757,0x7600b2c0761,0x1db0076e076d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock48 : PLift (smallGoodRange 1907 1973) :=
  ⟨smallBlockCheck_sound [0x1dc807740773,0x3bc0ae40779,0x1e28078c078b,0xa100cce078d,0x1e70079e079d,0xf3c059a079f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock49 : PLift (smallGoodRange 1973 2003) :=
  ⟨smallBlockCheck_sound [0x1ed007b607b5,0x1ee807bc07bb,0x1f0807c407c3,0xf9005e207c9,0x1f3007ce07cd,0x5340dd607cf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock50 : PLift (smallGoodRange 2003 2053) :=
  ⟨smallBlockCheck_sound [0x478056407d3,0x648028e07db,0x540013607e1,0x1fa807ec07eb,0x1fb007ee07ed,0xfec053a07f7] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock51 : PLift (smallGoodRange 2053 2089) :=
  ⟨smallBlockCheck_sound [0x201008060805,0x101c0a86080f,0x205008160815,0x1040010a0821,0x208808240823,0x104c0e260827] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock52 : PLift (smallGoodRange 2089 2137) :=
  ⟨smallBlockCheck_sound [0x740bfc0829,0x20c808340833,0x107c0cfc083f,0xb00f580841,0x850096e0851,0x214808540853] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock53 : PLift (smallGoodRange 2137 2203) :=
  ⟨smallBlockCheck_sound [0x10b0016c0859,0x2170085e085d,0xcc1034085f,0x10d00d820869,0x10e007f60871,0xb5806e40883] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock54 : PLift (smallGoodRange 2203 2243) :=
  ⟨smallBlockCheck_sound [0xb780c18089b,0x113c0870089f,0x229008a608a5,0x22b008ae08ad,0x22f008be08bd,0x117c06c808bf] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock55 : PLift (smallGoodRange 2243 2287) :=
  ⟨smallBlockCheck_sound [0x230808c408c3,0xbb80ae608cb,0x236808dc08db,0x237008de08dd,0x8e00d4e08e1,0x2f8009408e9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock56 : PLift (smallGoodRange 2287 2339) :=
  ⟨smallBlockCheck_sound [0x5f409b608ef,0x23d008f608f5,0x11f001b208f9,0x241009060905,0x120c11ca0907,0x2470091e091d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock57 : PLift (smallGoodRange 2339 2377) :=
  ⟨smallBlockCheck_sound [0x248809240923,0xc300b1a0925,0xc38015e092b,0xbc0d5e092f,0x24d009360935,0x250809440943] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock58 : PLift (smallGoodRange 2377 2411) :=
  ⟨smallBlockCheck_sound [0x129008c80949,0x7700bf8094d,0x63407c4094f,0x255009560955,0x958017e0959,0x12bc092e095f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock59 : PLift (smallGoodRange 2411 2459) :=
  ⟨smallBlockCheck_sound [0x78809ea096b,0x12e0060e0971,0x12ec100a0977,0x261009860985,0x4c409620989,0x131c074c098f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock60 : PLift (smallGoodRange 2459 2531) :=
  ⟨smallBlockCheck_sound [0x2668099c099b,0x268809a409a3,0x9a8015409a9,0x26b009ae09ad,0x138c0f5609c7,0x13b00f9c09d9] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock61 : PLift (smallGoodRange 2531 2579) :=
  ⟨smallBlockCheck_sound [0x278809e409e3,0x27a809ec09eb,0x13dc088e09ef,0x27d009f609f5,0x13ec11fa09f7,0x27f009fe09fd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock62 : PLift (smallGoodRange 2579 2633) :=
  ⟨smallBlockCheck_sound [0x28480a140a13,0x143c13f60a1f,0x14409020a21,0x146003140a31,0x147007760a39,0x28f00a3e0a3d] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock63 : PLift (smallGoodRange 2633 2677) :=
  ⟨smallBlockCheck_sound [0x149013d20a49,0x14ac012c0a57,0x298054e0a61,0x29880a640a63,0x14cc13700a67,0x6f413ac0a6f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock64 : PLift (smallGoodRange 2677 2707) :=
  ⟨smallBlockCheck_sound [0x29d00a760a75,0x29e80a7c0a7b,0x13c04380a7f,0x3800eb00a81,0x2a100a860a85,0x2a280a8c0a8b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock65 : PLift (smallGoodRange 2707 2741) :=
  ⟨smallBlockCheck_sound [0x2a480a940a93,0x152c0d960a97,0x153010e60a99,0x153c0b760a9f,0x15500e1e0aa9,0x680d940aab] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock66 : PLift (smallGoodRange 2741 2791) :=
  ⟨smallBlockCheck_sound [0x2ad00ab60ab5,0xe50071c0abd,0x15800f2a0ac1,0x7340c860acf,0x15b00d820ad9,0x2b900ae60ae5] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock67 : PLift (smallGoodRange 2791 2837) :=
  ⟨smallBlockCheck_sound [0x74411320ae7,0x2bb00aee0aed,0x15e010840af1,0x2bc80af40af3,0x2c080b040b03,0x1d808040b11] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock68 : PLift (smallGoodRange 2837 2887) :=
  ⟨smallBlockCheck_sound [0x2c500b160b15,0x2c680b1c0b1b,0x2c880b240b23,0x198043a0b29,0x2cb00b2e0b2d,0x167c07660b3f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock69 : PLift (smallGoodRange 2887 2939) :=
  ⟨smallBlockCheck_sound [0x168c16420b47,0x16a00cc20b51,0x16ac0cb00b57,0x2d700b5e0b5d,0xf3001440b65,0x16dc01aa0b6f] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock70 : PLift (smallGoodRange 2939 2999) :=
  ⟨smallBlockCheck_sound [0x2de80b7c0b7b,0x7b007180b89,0x2e300b8e0b8d,0x2e480b940b93,0x5cc10560b99,0x1b800960b9b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock71 : PLift (smallGoodRange 2999 3041) :=
  ⟨smallBlockCheck_sound [0x176c03120bb7,0x177003b80bb9,0x2f080bc40bc3,0x2f280bcc0bcb,0x179c0b980bcf,0x2f700bde0bdd] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock72 : PLift (smallGoodRange 3041 3089) :=
  ⟨smallBlockCheck_sound [0x17c017740be1,0xbe8163a0be9,0x33002300bf5,0x2fe80bfc0bfb,0x180c08b80c07,0x30280c0c0c0b] (by decide +kernel)⟩
set_option maxRecDepth 100000 in
def smallBlock73 : PLift (smallGoodRange 3089 3120) :=
  ⟨smallBlockCheck_sound [0xc1012500c11,0x6f00eb00c25,0x185c15a00c2f] (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem small_companions : smallGoodRange 6 3120 :=
  (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join smallBlock0.down smallBlock1.down) (smallGoodRange_join smallBlock2.down smallBlock3.down)) (smallGoodRange_join (smallGoodRange_join smallBlock4.down smallBlock5.down) (smallGoodRange_join smallBlock6.down (smallGoodRange_join smallBlock7.down smallBlock8.down)))) (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join smallBlock9.down smallBlock10.down) (smallGoodRange_join smallBlock11.down smallBlock12.down)) (smallGoodRange_join (smallGoodRange_join smallBlock13.down smallBlock14.down) (smallGoodRange_join smallBlock15.down (smallGoodRange_join smallBlock16.down smallBlock17.down))))) (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join smallBlock18.down smallBlock19.down) (smallGoodRange_join smallBlock20.down smallBlock21.down)) (smallGoodRange_join (smallGoodRange_join smallBlock22.down smallBlock23.down) (smallGoodRange_join smallBlock24.down (smallGoodRange_join smallBlock25.down smallBlock26.down)))) (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join smallBlock27.down smallBlock28.down) (smallGoodRange_join smallBlock29.down (smallGoodRange_join smallBlock30.down smallBlock31.down))) (smallGoodRange_join (smallGoodRange_join smallBlock32.down smallBlock33.down) (smallGoodRange_join smallBlock34.down (smallGoodRange_join smallBlock35.down smallBlock36.down)))))) (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join smallBlock37.down smallBlock38.down) (smallGoodRange_join smallBlock39.down smallBlock40.down)) (smallGoodRange_join (smallGoodRange_join smallBlock41.down smallBlock42.down) (smallGoodRange_join smallBlock43.down (smallGoodRange_join smallBlock44.down smallBlock45.down)))) (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join smallBlock46.down smallBlock47.down) (smallGoodRange_join smallBlock48.down smallBlock49.down)) (smallGoodRange_join (smallGoodRange_join smallBlock50.down smallBlock51.down) (smallGoodRange_join smallBlock52.down (smallGoodRange_join smallBlock53.down smallBlock54.down))))) (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join smallBlock55.down smallBlock56.down) (smallGoodRange_join smallBlock57.down smallBlock58.down)) (smallGoodRange_join (smallGoodRange_join smallBlock59.down smallBlock60.down) (smallGoodRange_join smallBlock61.down (smallGoodRange_join smallBlock62.down smallBlock63.down)))) (smallGoodRange_join (smallGoodRange_join (smallGoodRange_join smallBlock64.down smallBlock65.down) (smallGoodRange_join smallBlock66.down (smallGoodRange_join smallBlock67.down smallBlock68.down))) (smallGoodRange_join (smallGoodRange_join smallBlock69.down smallBlock70.down) (smallGoodRange_join smallBlock71.down (smallGoodRange_join smallBlock72.down smallBlock73.down)))))))

end ThetaLongHaul.Packed
/-! Own finite-range combination logic. The large-range hypothesis below is
already proved by our merged certificate PR18042; it is explicitly supplied
in the standalone final files, never left as a hypothesis of OMA.solution.
Prospective target definitions: @rickmanelius PR21155/21541. -/
namespace ThetaCompanionFinite
open ThetaLongHaul.Packed

theorem finite_4_1_of_large (large : GoodRange 3120 100000)
    (p : ℕ) (hp : p.Prime) (hlo : 5<p) (hhi : p<100000) :
    (p : ℤ)<Arxiv.«2501.03234».S p := by
  by_cases hs : p<3120
  · have h := small_companions p (by omega) hs hp
    by_cases hsmall : p≤233
    · simpa only [smallThreshold,if_pos hsmall,Nat.cast_one,one_mul] using h
    · simp only [smallThreshold,if_neg hsmall,Nat.cast_ofNat] at h
      have hp0 : (0 : ℤ)≤p := Nat.cast_nonneg p
      linarith
  · have h := large p (by omega) hhi hp
    have hp0 : (0 : ℤ)≤p := Nat.cast_nonneg p
    linarith

theorem finite_4_2_of_large (large : GoodRange 3120 100000)
    (p : ℕ) (hp : p.Prime) (hlo : 233<p) (hhi : p<100000) :
    2*(p : ℤ)<Arxiv.«2501.03234».S p := by
  by_cases hs : p<3120
  · have h := small_companions p (by omega) hs hp
    simpa only [smallThreshold,if_neg (show ¬p≤233 by omega),Nat.cast_ofNat] using h
  · have h := large p (by omega) hhi hp
    have hp0 : (0 : ℤ)≤p := Nat.cast_nonneg p
    linarith

end ThetaCompanionFinite
namespace ThetaCompanionFinite

/-- The large-range premise is instantiated by our own merged certificate.
No undischarged arithmetic hypothesis remains in this finite statement. -/
theorem finite_4_1 : ∀ p : ℕ, p.Prime → 5<p → p<100000 →
    (p : ℤ)<Arxiv.«2501.03234».S p :=
  finite_4_1_of_large ThetaLongHaul.Packed.finite_range

theorem finite_4_2 : ∀ p : ℕ, p.Prime → 233<p → p<100000 →
    2*(p : ℤ)<Arxiv.«2501.03234».S p :=
  finite_4_2_of_large ThetaLongHaul.Packed.finite_range

end ThetaCompanionFinite

 theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_4_1_R1.H1 :=
  ThetaCompanionFinite.finite_4_1
