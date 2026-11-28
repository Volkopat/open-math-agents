import FormalConjectures.OEIS.«180017»

/-!
Every integer occurs infinitely often as the ternary digit sum minus the binary digit sum.

We follow the preparation and rarefaction strategy of Spiegelhofer,
Collisions of digit sums in bases 2 and 3 (arXiv:2105.11173, Sections 2.2–2.3).
Here the shifts occupy disjoint blocks in both bases. Their subset sums
realize a full interval of corrections, so finite second moments suffice.
-/

namespace OMA.A180017

private def s (b n : ℕ) : ℕ := (Nat.digits b n).sum

-- The one-digit case is the argument used for the binary suffixes
-- in the sibling proof of OEIS A037301.
private theorem digit (b : ℕ) (hb : 1 < b) {x : ℕ} (hx : x < b) (y : ℕ) :
    s b (x + b * y) = x + s b y := by
  by_cases h : x ≠ 0 ∨ y ≠ 0
  · simp only [s, Nat.digits_add b hb x y hx h, List.sum_cons]
  · push Not at h
    simp [h.1, h.2, s]

private theorem split (b : ℕ) (hb : 1 < b) {k x : ℕ} (hx : x < b ^ k) (y : ℕ) :
    s b (x + b ^ k * y) = s b x + s b y := by
  induction k generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    simp [this, s]
  | succ k ih =>
    have hm := Nat.mod_lt x (by omega : 0 < b)
    have hq : x / b < b ^ k := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).2
      simpa [pow_succ] using hx
    have he : x % b + b * (x / b) = x := Nat.mod_add_div _ _
    have hs : x + b ^ (k + 1) * y = x % b + b * (x / b + b ^ k * y) := by
      rw [Nat.mul_add, ← add_assoc, he, pow_succ']
      ac_rfl
    rw [hs, digit b hb hm, ih hq, ← add_assoc, ← digit b hb hm, he]

private theorem split_div (b : ℕ) (hb : 1 < b) (k n : ℕ) :
    s b n = s b (n % b ^ k) + s b (n / b ^ k) := by
  simpa only [Nat.mod_add_div] using
    split b hb (Nat.mod_lt n (by positivity : 0 < b ^ k)) (n / b ^ k)

private theorem s_bound (b : ℕ) (hb : 1 < b) {k x : ℕ} (hx : x < b ^ k) :
    s b x ≤ (b - 1) * k := by
  induction k generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    simp [this, s]
  | succ k ih =>
    have hm := Nat.mod_lt x (by omega : 0 < b)
    have hq := (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).2 (by simpa [pow_succ] using hx)
    have h := ih (show x / b < b ^ k from hq)
    have hd := split_div b hb 1 x
    simp only [pow_one] at hd
    have hsmall : s b (x % b) = x % b := by
      simpa [s] using digit b hb hm 0
    rw [Nat.mul_succ, hd, hsmall]
    omega

private theorem s_pow_sub_one (b : ℕ) (hb : 1 < b) (k : ℕ) :
    s b (b ^ k - 1) = (b - 1) * k := by
  induction k with
  | zero => simp [s]
  | succ k ih =>
    have hp : 0 < b ^ k := by positivity
    have he : b ^ (k + 1) - 1 = b - 1 + b * (b ^ k - 1) := by
      rw [pow_succ', Nat.mul_sub_left_distrib, mul_one]
      have : b ≤ b * b ^ k := by nlinarith
      omega
    rw [he, digit b hb (by omega), ih, Nat.mul_succ, add_comm]

/-- Start a carry at the top digit of the increment and prescribe its length. -/
private theorem carry (b : ℕ) (hb : 1 < b) {d k l : ℕ}
    (hd : 0 < d) (hk : d < b ^ k) (hl : b ^ l ∣ d) (r : ℕ) :
    ∃ x, b ^ l ∣ x ∧ x + d < b ^ (k + r) ∧
      (s b (x + d) : ℤ) - s b x = s b d - ((b - 1 : ℕ) : ℤ) * r := by
  rcases r with _ | r
  · exact ⟨0, dvd_zero _, by simpa using hk, by simp [s]⟩
  let j := Nat.log b d
  let p := b ^ j
  let c := d / p
  let m := d % p
  have hp : 0 < p := by dsimp [p]; positivity
  have hj : j < k := Nat.log_lt_of_lt_pow (by omega : d ≠ 0) hk
  have hpd : p ≤ d := Nat.pow_log_le_self b (by omega)
  have hc : 0 < c := Nat.div_pos hpd hp
  have hcb : c < b := (Nat.div_lt_iff_lt_mul hp).2 (by
    simpa only [p, j, pow_succ'] using Nat.lt_pow_succ_log_self hb d)
  have hm : m < p := Nat.mod_lt _ hp
  have hdec : d = m + p * c := (Nat.mod_add_div d p).symm
  have hl' : l ≤ j := Nat.le_log_of_pow_le hb (Nat.le_of_dvd hd hl)
  let y := (b - c) + b * (b ^ r - 1)
  have hy : y + c = b ^ (r + 1) := by
    dsimp [y]
    rw [pow_succ', Nat.mul_sub_left_distrib, mul_one]
    have hpow : 0 < b ^ r := by positivity
    have : b ≤ b * b ^ r := by nlinarith
    omega
  let x := p * y
  have hx : b ^ l ∣ x := dvd_mul_of_dvd_left (pow_dvd_pow b hl') _
  have hxd : x + d = m + p * b ^ (r + 1) := by
    rw [hdec]
    calc
      x + (m + p * c) = m + p * (y + c) := by dsimp [x]; ring
      _ = _ := by rw [hy]
  have hbound : x + d < b ^ (k + (r + 1)) := by
    rw [hxd]
    have hpow : 0 < b ^ (r + 1) := by positivity
    have hlt : b ^ (r + 1) + 1 ≤ b ^ ((r + 1) + 1) := by
      rw [pow_succ b (r + 1)]
      nlinarith
    calc
      m + p * b ^ (r + 1) < p * (b ^ (r + 1) + 1) := by rw [mul_add, mul_one]; omega
      _ ≤ p * b ^ ((r + 1) + 1) := Nat.mul_le_mul_left _ hlt
      _ ≤ _ := by
        dsimp only [p]
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by omega)
  have hsx : s b x = s b y := by
    simpa [x, p, s] using split b hb (by positivity : 0 < b ^ j) y
  have hsy : s b y = (b - c) + (b - 1) * r := by
    rw [show y = (b - c) + b * (b ^ r - 1) from rfl, digit b hb (by omega),
      s_pow_sub_one b hb]
  have hsc : s b c = c := by simpa [s] using digit b hb hcb 0
  have hsp : s b (b ^ (r + 1)) = 1 := by
    have hsone : s b 1 = 1 := by simpa [s] using digit b hb hb 0
    have hszero : s b 0 = 0 := by simp [s]
    simpa [hszero, hsone] using split b hb (by positivity : 0 < b ^ (r + 1)) 1
  refine ⟨x, hx, hbound, ?_⟩
  rw [hxd, split b hb hm, hsp, hsx, hsy]
  have hsd : s b d = s b m + c := by rw [hdec, split b hb hm, hsc]
  rw [hsd]
  push_cast [Nat.cast_sub (show c ≤ b by omega), Nat.cast_sub (show 1 ≤ b by omega)]
  ring

private theorem clog_bound (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    b ^ Nat.clog b n < b * n := by
  rcases eq_or_lt_of_le (show 1 ≤ n by omega) with rfl | h
  · simpa using hb
  · have hp := Nat.pow_pred_clog_lt_self hb h
    have hc := Nat.clog_pos hb h
    simp only [Nat.pred_eq_sub_one] at hp
    have he : Nat.clog b n = (Nat.clog b n - 1) + 1 := by omega
    calc
      _ = b ^ (Nat.clog b n - 1) * b := he ▸ (pow_succ _ _)
      _ < _ := by simpa [mul_comm] using Nat.mul_lt_mul_of_pos_right hp (show 0 < b by omega)

private theorem two_le_three_pow (w : ℕ) : 2 ^ w ≤ 3 ^ w :=
  Nat.pow_le_pow_left (by decide) _

/-- Use one common increment and fit its effect into fresh blocks in both bases. -/
private theorem newBlock (b w : ℕ) (hw : 0 < w) :
    let a := Nat.clog 2 (3 ^ b)
    let b' := 3 * b + w + 3
    let a' := Nat.clog 2 (3 ^ b')
    let d := 2 ^ a * 3 ^ b
    ∃ x y, 2 ^ a ∣ x ∧ 3 ^ b ∣ y ∧ x + d < 2 ^ a' ∧ y + d < 3 ^ b' ∧
      (s 3 (y + d) : ℤ) - s 3 y - ((s 2 (x + d) : ℤ) - s 2 x) = w := by
  dsimp only
  set a := Nat.clog 2 (3 ^ b)
  set b' := 3 * b + w + 3
  set a' := Nat.clog 2 (3 ^ b')
  set p := (2 : ℕ) ^ a
  set q := (3 : ℕ) ^ b
  set d := p * q
  have hpq : q ≤ p := Nat.le_pow_clog (by decide) _
  have hpq' : p < 2 * q := clog_bound 2 q (by decide) (by positivity)
  have hp3 : p < 3 ^ (b + 1) := by
    rw [pow_succ]
    have : 0 < q := by positivity
    omega
  have hd2 : d < 2 ^ (2 * a + 1) := by
    rw [pow_succ, show 2 * a = a * 2 by omega, pow_mul, pow_two]
    have : 0 < p := by positivity
    change p * q < p * p * 2
    nlinarith [Nat.mul_le_mul_left p hpq]
  have hd3 : d < 3 ^ (2 * b + 1) := by
    have h := Nat.mul_lt_mul_of_pos_right hp3 (show 0 < q by positivity)
    simpa only [d, q, ← pow_add, show b + 1 + b = 2 * b + 1 by omega] using h
  have hd : 0 < d := by positivity
  have hsd2 : s 2 d = s 2 q := by
    have h := split 2 (by decide) (show 0 < p by positivity) q
    simpa [d, s] using h
  have hsd3 : s 3 d = s 3 p := by
    have h := split 3 (by decide) (show 0 < q by positivity) p
    simpa [d, s, mul_comm] using h
  have hq2 : q < 2 ^ (a + 1) := by
    rw [pow_succ]
    have : 0 < p := by positivity
    omega
  have hA : s 2 d ≤ a + 1 := by simpa [hsd2] using s_bound 2 (by decide) hq2
  have hB : s 3 d ≤ 2 * (b + 1) := by simpa [hsd3] using s_bound 3 (by decide) hp3
  let r3 := (((s 3 d : ℤ) - s 2 d - w).toNat + 1) / 2
  let r2 := ((w : ℤ) + s 2 d + 2 * r3 - s 3 d).toNat
  have hr3 : r3 ≤ b + 1 := by dsimp [r3]; omega
  have hr2 : r2 ≤ a + w + 1 := by dsimp [r2, r3]; omega
  have he : (s 3 d : ℤ) - 2 * r3 - ((s 2 d : ℤ) - r2) = w := by
    dsimp [r2, r3]
    omega
  obtain ⟨x, hx, hxd, hsx⟩ :=
    carry 2 (by decide) hd hd2 (show p ∣ d by exact dvd_mul_right _ _) r2
  obtain ⟨y, hy, hyd, hsy⟩ :=
    carry 3 (by decide) hd hd3 (show q ∣ d by exact dvd_mul_left _ _) r3
  refine ⟨x, y, hx, hy, hxd.trans_le ?_, hyd.trans_le ?_, ?_⟩
  · apply (Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 * a + 1 + r2 ≤
        3 * a + w + 2 by omega)).trans
    apply le_trans _ (Nat.le_pow_clog (by decide : 1 < 2) (3 ^ b'))
    have hcube : p ^ 3 ≤ (2 * q) ^ 3 := Nat.pow_le_pow_left hpq'.le _
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show w ≠ 0 by omega)
    have hv := two_le_three_pow v
    have hpw : (2 : ℕ) ^ (3 * a + (v + 1) + 2) = p ^ 3 * 2 ^ v * 8 := by
      rw [show 3 * a + (v + 1) + 2 = (a * 3 + v) + 3 by omega,
        pow_add, pow_add, pow_mul]
      rfl
    have hqw : (3 : ℕ) ^ b' = q ^ 3 * 3 ^ v * 81 := by
      rw [show b' = (b * 3 + v) + 4 by omega, pow_add, pow_add, pow_mul]
      rfl
    rw [hpw, hqw]
    have hc : p ^ 3 ≤ 8 * q ^ 3 := by simpa [mul_pow] using hcube
    calc
      _ ≤ (8 * q ^ 3) * 3 ^ v * 8 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hc hv)
      _ ≤ _ := by
        have h := Nat.mul_le_mul_left (q ^ 3 * 3 ^ v) (show 64 ≤ 81 by decide)
        nlinarith
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · norm_num at hsx hsy
    rw [hsx, hsy, he]

private theorem pack (b : ℕ) (hb : 1 < b) {lo hi x y : ℕ} (hle : lo ≤ hi)
    (hx : x < b ^ lo) (hy : b ^ lo ∣ y) (hbound : y < b ^ hi) :
    x + y < b ^ hi ∧ s b (x + y) = s b x + s b y := by
  obtain ⟨q, rfl⟩ := hy
  have hp : 0 < b ^ lo := by positivity
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  refine ⟨?_, ?_⟩
  · rw [pow_add] at hbound ⊢
    have hlt := Nat.lt_of_mul_lt_mul_left hbound
    calc
      x + b ^ lo * q < b ^ lo * (q + 1) := by rw [mul_add, mul_one]; omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  · rw [split b hb hx]
    have h := split b hb hp q
    simpa [s] using congrArg (s b x + ·) h.symm

private def width : ℕ → ℕ
  | 0 => 0
  | i + 1 => 3 * width i + 2 ^ i + 3

private def binaryWidth (i : ℕ) : ℕ := Nat.clog 2 (3 ^ width i)

private theorem width_bound (i : ℕ) : width i + 2 ^ i + 2 ≤ 3 * 3 ^ i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [width, pow_succ 2 i, pow_succ 3 i]
    omega

/-- Choosing which blocks to shift gives all the binary subset sums of the effects. -/
private theorem allShifts (i : ℕ) :
    ∃ r₂ r₃, r₂ < 2 ^ binaryWidth i ∧ r₃ < 3 ^ width i ∧
      ∀ (j : ℕ), j < 2 ^ i → ∃ d, r₂ + d < 2 ^ binaryWidth i ∧ r₃ + d < 3 ^ width i ∧
        (s 3 (r₃ + d) : ℤ) - s 3 r₃ - ((s 2 (r₂ + d) : ℤ) - s 2 r₂) = j := by
  induction i with
  | zero =>
    refine ⟨0, 0, by positivity, by positivity, fun j hj => ⟨0, by positivity, by positivity, ?_⟩⟩
    have : j = 0 := by omega
    simp [this]
  | succ i ih =>
    obtain ⟨r₂, r₃, hr₂, hr₃, shifts⟩ := ih
    let D := (2 : ℕ) ^ binaryWidth i * 3 ^ width i
    obtain ⟨x, y, hx, hy, hxD, hyD, hxy⟩ := newBlock (width i) (2 ^ i) (by positivity)
    change 2 ^ binaryWidth i ∣ x at hx
    change 3 ^ width i ∣ y at hy
    change x + D < 2 ^ binaryWidth (i + 1) at hxD
    change y + D < 3 ^ width (i + 1) at hyD
    change (s 3 (y + D) : ℤ) - s 3 y - ((s 2 (x + D) : ℤ) - s 2 x) = 2 ^ i at hxy
    have hb : width i ≤ width (i + 1) := by
      rw [width]
      have : 0 ≤ (2 : ℕ) ^ i := Nat.zero_le _
      omega
    have ha : binaryWidth i ≤ binaryWidth (i + 1) :=
      Nat.clog_mono_right _ (Nat.pow_le_pow_right (by decide) hb)
    have h₂ := pack 2 (by decide) ha hr₂ hx (show x < 2 ^ binaryWidth (i + 1) by omega)
    have h₃ := pack 3 (by decide) hb hr₃ hy (show y < 3 ^ width (i + 1) by omega)
    refine ⟨r₂ + x, r₃ + y, h₂.1, h₃.1, ?_⟩
    intro j hj
    rw [pow_succ] at hj
    have finish (e : ℕ) (he : e < 2 ^ i) (v : ℕ) (hv₂ : 2 ^ binaryWidth i ∣ x + v)
        (hv₃ : 3 ^ width i ∣ y + v) (hb₂ : x + v < 2 ^ binaryWidth (i + 1))
        (hb₃ : y + v < 3 ^ width (i + 1))
        (hs : (s 3 (y + v) : ℤ) - s 3 y - ((s 2 (x + v) : ℤ) - s 2 x) = (j : ℤ) - e) :
        ∃ d, r₂ + x + d < 2 ^ binaryWidth (i + 1) ∧ r₃ + y + d < 3 ^ width (i + 1) ∧
          (s 3 (r₃ + y + d) : ℤ) - s 3 (r₃ + y) -
            ((s 2 (r₂ + x + d) : ℤ) - s 2 (r₂ + x)) = j := by
      obtain ⟨e', he₂, he₃, hse⟩ := shifts e he
      have g₂ := pack 2 (by decide) ha he₂ hv₂ hb₂
      have g₃ := pack 3 (by decide) hb he₃ hv₃ hb₃
      refine ⟨e' + v, by simpa [add_assoc, add_left_comm, add_comm] using g₂.1,
        by simpa [add_assoc, add_left_comm, add_comm] using g₃.1, ?_⟩
      rw [show r₂ + x + (e' + v) = (r₂ + e') + (x + v) by ac_rfl,
        show r₃ + y + (e' + v) = (r₃ + e') + (y + v) by ac_rfl,
        g₂.2, g₃.2, h₂.2, h₃.2]
      push_cast
      linarith
    by_cases h : j < 2 ^ i
    · exact finish j h 0 (by simpa using hx) (by simpa using hy)
        (by omega) (by omega) (by simp)
    · refine finish (j - 2 ^ i) (by omega) D (dvd_add hx (dvd_mul_right _ _))
        (dvd_add hy (dvd_mul_left _ _)) hxD hyD ?_
      rw [hxy, Nat.cast_sub (show 2 ^ i ≤ j by omega), Nat.cast_pow]
      norm_num


open Finset
open scoped BigOperators

private def err (b l n : ℕ) : ℤ := 2 * s b n - ((b - 1 : ℕ) : ℤ) * l

private theorem sum_grid (b m : ℕ) (F : ℕ → ℤ) :
    ∑ n ∈ range (b * m), F n = ∑ x ∈ range b, ∑ y ∈ range m, F (x + b * y) := by
  by_cases hb : b = 0
  · simp [hb]
  have hp : 0 < b := by omega
  rw [← Finset.sum_product']
  apply Finset.sum_nbij (fun n => (n % b, n / b))
  · intro n hn
    simp only [mem_product, mem_range] at hn ⊢
    exact ⟨Nat.mod_lt _ hp, (Nat.div_lt_iff_lt_mul hp).2 (by simpa [mul_comm] using hn)⟩
  · intro x _ y _ he
    have hm := congrArg Prod.fst he
    have hd := congrArg Prod.snd he
    dsimp at hm hd
    calc
      x = x % b + b * (x / b) := (Nat.mod_add_div _ _).symm
      _ = y % b + b * (y / b) := by rw [hm, hd]
      _ = y := Nat.mod_add_div _ _
  · rintro ⟨x, y⟩ hxy
    have hh : x < b ∧ y < m := by simpa using hxy
    refine ⟨x + b * y, mem_range.mpr ?_, ?_⟩
    · calc
        x + b * y < b * (y + 1) := by rw [mul_add, mul_one]; omega
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    · simp [Nat.add_mul_div_left _ _ hp, Nat.mod_eq_of_lt hh.1, Nat.div_eq_of_lt hh.1]
  · intro n _
    rw [Nat.mod_add_div]

private theorem err_zero_mean (b : ℕ) (hb : 1 < b) (l : ℕ) :
    ∑ n ∈ range (b ^ l), err b l n = 0 := by
  induction l with
  | zero => simp [err, s]
  | succ l ih =>
    rw [pow_succ', sum_grid]
    have hr : ∀ x ∈ range b, ∀ y : ℕ,
        err b (l + 1) (x + b * y) = (2 * (x : ℤ) - ((b - 1 : ℕ) : ℤ)) + err b l y := by
      intro x hx y
      unfold err
      rw [digit b hb (mem_range.mp hx)]
      push_cast
      ring
    calc
      _ = ∑ x ∈ range b, (∑ y ∈ range (b ^ l), ((2 * (x : ℤ) - ((b - 1 : ℕ) : ℤ)) + err b l y)) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y _
        exact hr x hx y
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ih, add_zero,
          nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib]
        have hs := Finset.sum_range_id_mul_two b
        have hs' : (∑ x ∈ range b, (x : ℤ)) * 2 = (b : ℤ) * ((b - 1 : ℕ) : ℤ) := by
          simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using
            congrArg (fun n : ℕ => (n : ℤ)) hs
        rw [mul_comm (2 : ℤ), hs', sub_self, mul_zero]

private theorem moment_bound (b : ℕ) (hb : 1 < b) (hb' : b ≤ 3) (l : ℕ) :
    ∑ n ∈ range (b ^ l), (err b l n) ^ 2 ≤ (4 : ℤ) * l * (b ^ l : ℕ) := by
  induction l with
  | zero => simp [err, s]
  | succ l ih =>
    let C := fun x : ℕ => 2 * (x : ℤ) - ((b - 1 : ℕ) : ℤ)
    have hC (x : ℕ) (hx : x ∈ range b) : C x ^ 2 ≤ 4 := by
      have hx' := mem_range.mp hx
      have hl : -2 ≤ C x := by dsimp [C]; omega
      have hu : C x ≤ 2 := by dsimp [C]; omega
      nlinarith
    have hr (x : ℕ) (hx : x ∈ range b) (y : ℕ) :
        (err b (l + 1) (x + b * y)) ^ 2 =
          C x ^ 2 + (2 * C x) * err b l y + (err b l y) ^ 2 := by
      unfold err C
      rw [digit b hb (mem_range.mp hx)]
      push_cast
      ring
    have hrow (x : ℕ) (hx : x ∈ range b) :
        ∑ y ∈ range (b ^ l), err b (l + 1) (x + b * y) ^ 2 ≤
          (4 : ℤ) * (l + 1) * (b ^ l : ℕ) := by
      calc
        _ = ∑ y ∈ range (b ^ l), (C x ^ 2 + (2 * C x) * err b l y + (err b l y) ^ 2) :=
          Finset.sum_congr rfl (fun y _ => hr x hx y)
        _ = (b ^ l : ℕ) * C x ^ 2 + ∑ y ∈ range (b ^ l), (err b l y) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            err_zero_mean b hb, mul_zero, add_zero, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
        _ ≤ _ := by
          have h := mul_le_mul_of_nonneg_left (hC x hx) (show (0 : ℤ) ≤ (b ^ l : ℕ) by positivity)
          linarith
    rw [pow_succ' b l, sum_grid]
    calc
      _ ≤ ∑ _x ∈ range b, (4 : ℤ) * (l + 1) * (b ^ l : ℕ) :=
        Finset.sum_le_sum hrow
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

private theorem sum_embed {M B D : ℕ} {f g : ℕ → ℕ}
    (hf : ∀ k < M, f k < B) (hg : ∀ k < M, g k < D)
    (hi : Set.InjOn (fun k => (f k, g k)) (↑(range M)))
    (F : ℕ → ℤ) (hF : ∀ n, 0 ≤ F n) :
    ∑ k ∈ range M, F (f k) ≤ (D : ℤ) * ∑ n ∈ range B, F n := by
  rw [← Finset.sum_image (f := fun p : ℕ × ℕ => F p.1) hi]
  calc
    _ ≤ ∑ p ∈ (range B) ×ˢ (range D), F p.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => hF p.1)
      intro p hp
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hp
      exact mem_product.mpr ⟨mem_range.mpr (hf k (mem_range.mp hk)),
        mem_range.mpr (hg k (mem_range.mp hk))⟩
    _ = _ := by
      rw [Finset.sum_product]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]

/-- Split the progression into low and high digit blocks. The remainders are
injective within each period, and each quotient occurs at most three times. -/
private theorem affineMoment (b u v q c M : ℕ) (hb : 1 < b) (hb' : b ≤ 3)
    (hc : c < q) (hq : q ≤ b ^ u) (hB : b ^ u < 3 * q) (hM : b ^ u ≤ M)
    (hcop : (b ^ u).Coprime q) (hv : 2 * M ≤ b ^ v) (hv' : b ^ v ≤ 9 * M) :
    ∑ k ∈ range M, (err b (u + v) (q * (M + k) + c)) ^ 2 ≤
      (216 : ℤ) * (u + v : ℕ) * M := by
  set B := b ^ u
  let X := fun k : ℕ => q * (M + k) + c
  have hBp : 0 < B := by positivity
  have hlo_range (k : ℕ) : X k % B < B := Nat.mod_lt _ hBp
  have hhi_range (k : ℕ) (hk : k < M) : X k / B < b ^ v := by
    apply (Nat.div_lt_iff_lt_mul hBp).2
    have h1 := Nat.mul_le_mul_left q (show M + k + 1 ≤ 2 * M by omega)
    have h2 := Nat.mul_le_mul_left (2 * M) hq
    have h3 := Nat.mul_le_mul_right B hv
    dsimp [X]
    nlinarith
  have hilo : Set.InjOn (fun k => (X k % B, k / B)) (↑(range M)) := by
    intro k _ l _ he
    have hre := congrArg Prod.fst he
    have hdiv := congrArg Prod.snd he
    change X k ≡ X l [MOD B] at hre
    change k / B = l / B at hdiv
    have hx (i : ℕ) : X i = q * M + c + q * i := by dsimp [X]; ring
    rw [hx, hx] at hre
    have hmod : k % B = l % B :=
      Nat.ModEq.cancel_left_of_coprime hcop (Nat.ModEq.add_left_cancel (Nat.ModEq.refl _) hre)
    calc
      k = k % B + B * (k / B) := (Nat.mod_add_div _ _).symm
      _ = l % B + B * (l / B) := by rw [hmod, hdiv]
      _ = l := Nat.mod_add_div _ _
  have hi_hi : Set.InjOn (fun k => (X k / B, k % 3)) (↑(range M)) := by
    have closer (k l : ℕ) (hh : X k / B = X l / B) : l < k + 3 := by
      have h₁ := Nat.mod_add_div (X k) B
      have h₂ := Nat.mod_add_div (X l) B
      rw [← hh] at h₂
      have h₃ : X l < X k + B := by
        have := hlo_range l
        omega
      by_contra! h
      have hm := Nat.mul_le_mul_left q (show M + k + 3 ≤ M + l by omega)
      dsimp [X] at h₃
      nlinarith
    intro k _ l _ he
    have hh : X k / B = X l / B := congrArg Prod.fst he
    have hh' : k % 3 = l % 3 := congrArg Prod.snd he
    have h₁ := closer k l hh
    have h₂ := closer l k hh.symm
    omega
  have hlo := sum_embed (M := M) (B := B) (D := M / B + 1)
    (fun k _ => hlo_range k)
    (fun k hk => Nat.lt_succ_of_le (Nat.div_le_div_right hk.le)) hilo
    (fun n => err b u n ^ 2) (fun _ => sq_nonneg _)
  have hhi := sum_embed hhi_range (fun k (_ : k < M) => Nat.mod_lt k (by decide : 0 < 3))
    hi_hi (fun n => err b v n ^ 2) (fun _ => sq_nonneg _)
  have hlo' : ∑ k ∈ range M, err b u (X k % B) ^ 2 ≤ (8 : ℤ) * u * M := by
    have hd₁ : B * (M / B + 1) ≤ 2 * M := by
      rw [mul_add, mul_one]
      have h := Nat.mul_div_le M B
      omega
    have hd₂ : (B : ℤ) * ((M / B + 1 : ℕ) : ℤ) ≤ 2 * M := by exact_mod_cast hd₁
    calc
      _ ≤ _ := hlo
      _ ≤ ((M / B + 1 : ℕ) : ℤ) * (4 * u * B) :=
        mul_le_mul_of_nonneg_left (moment_bound b hb hb' u) (by positivity)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hd₂ (show (0 : ℤ) ≤ 4 * u by positivity)
        nlinarith only [h]
  have hhi' : ∑ k ∈ range M, err b v (X k / B) ^ 2 ≤ (108 : ℤ) * v * M := by
    have hh := mul_le_mul_of_nonneg_left (moment_bound b hb hb' v)
      (show (0 : ℤ) ≤ (3 : ℕ) by decide)
    have hh' : ((b ^ v : ℕ) : ℤ) ≤ 9 * M := by exact_mod_cast hv'
    have hh'' := mul_le_mul_of_nonneg_left hh' (show (0 : ℤ) ≤ 12 * v by positivity)
    have h := hhi.trans hh
    norm_num at h
    push_cast at hh''
    linarith only [h, hh'']
  have hsplit (k : ℕ) : err b (u + v) (X k) =
      err b u (X k % B) + err b v (X k / B) := by
    unfold err
    rw [split_div b hb u (X k)]
    push_cast
    ring
  change ∑ k ∈ range M, (err b (u + v) (X k)) ^ 2 ≤ _
  calc
    _ ≤ ∑ k ∈ range M, (2 * err b u (X k % B) ^ 2 +
        2 * err b v (X k / B) ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      rw [hsplit]
      nlinarith only [sq_nonneg (err b u (X k % B) - err b v (X k / B))]
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      push_cast
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ u by positivity) (show (0 : ℤ) ≤ M by positivity)]


private theorem log_range (h : ℕ) :
    9 * h ≤ Nat.clog 2 (3 ^ (6 * h)) ∧ Nat.clog 2 (3 ^ (6 * h)) ≤ 10 * h := by
  have hlo : (2 : ℕ) ^ (9 * h) ≤ 3 ^ (6 * h) := by
    simp only [pow_mul]
    exact Nat.pow_le_pow_left (by decide) _
  have hhi : (3 : ℕ) ^ (6 * h) ≤ 2 ^ (10 * h) := by
    simp only [pow_mul]
    exact Nat.pow_le_pow_left (by decide) _
  exact ⟨(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (hlo.trans (Nat.le_pow_clog (by decide) _)), Nat.clog_le_of_le_pow hhi⟩

private theorem three_le_four_pow (b : ℕ) : (3 : ℕ) ^ b ≤ 2 ^ (2 * b) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by decide) _

private theorem exponential_gap (i : ℕ) : (i + 3) * 3 ^ i ≤ 3 * 4 ^ i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [pow_succ 3 i, pow_succ 4 i]
    have h := Nat.mul_le_mul_right 4 ih
    have h' := Nat.mul_le_mul_right (3 ^ i) (show 3 * (i + 1 + 3) ≤ 4 * (i + 3) by omega)
    nlinarith only [h, h']

private theorem shift_transfer (b : ℕ) (hb : 1 < b) {k n d r : ℕ}
    (hr : n % b ^ k = r) (hd : r + d < b ^ k) :
    (s b (n + d) : ℤ) - s b n = s b (r + d) - (s b r : ℤ) := by
  have hn : n = r + b ^ k * (n / b ^ k) := by
    rw [← hr, Nat.mod_add_div]
  have hnd : n + d = (r + d) + b ^ k * (n / b ^ k) := by omega
  rw [hnd, split b hb hd, split_div b hb k n, hr]
  push_cast
  ring

private theorem large_value (z : ℤ) (N : ℕ) : ∃ n > N, OeisA180017.a n = z := by
  -- The correction interval has width 2^i and the variance is O(3^i).
  let i := 3000000 + N + z.natAbs
  let K := (2 : ℕ) ^ i
  let half := K / 2
  let h := 100 * (3 : ℕ) ^ i
  let t := 6 * h
  let M := (3 : ℕ) ^ t
  let b := width i
  let a := binaryWidth i
  let P := (2 : ℕ) ^ a
  have hi : 0 < i := by dsimp [i]; omega
  have hK : K = 2 * half := by
    have he : i = (i - 1) + 1 := by omega
    have hk : K = 2 ^ (i - 1) * 2 := by
      change 2 ^ i = _
      exact he ▸ (pow_succ _ _)
    dsimp [half]
    omega
  have hpow : i < (3 : ℕ) ^ i := Nat.lt_pow_self (by decide)
  have hN : N < i := by dsimp [i]; omega
  have hz : z.natAbs ≤ i := by dsimp [i]; omega
  have hM : N < M := by
    have h₁ : t < M := Nat.lt_pow_self (by decide)
    dsimp [t, h] at h₁
    omega
  have hMp : 0 < M := by positivity
  have hPp : 0 < P := by positivity
  have hh : 0 < h := by positivity
  have hgap : (10000 : ℤ) * h < (K : ℤ) ^ 2 := by
    have h₁ := exponential_gap i
    have h₂ : 3000000 < i + 3 := by dsimp [i]; omega
    have h₃ := Nat.mul_lt_mul_of_pos_right h₂ (show 0 < (3 : ℕ) ^ i by positivity)
    have h₄ : K ^ 2 = 4 ^ i := by
      dsimp [K]
      rw [← pow_mul, mul_comm i, pow_mul]
      rfl
    have h₅ : 10000 * h < K ^ 2 := by
      rw [h₄]
      dsimp [h]
      omega
    exact_mod_cast h₅
  have hb : b ≤ 3 * 3 ^ i := by
    have h₁ := width_bound i
    change b + 2 ^ i + 2 ≤ 3 * 3 ^ i at h₁
    omega
  have ha : a ≤ 2 * b := Nat.clog_le_of_le_pow (three_le_four_pow b)
  have hKh : K ≤ 3 ^ i := two_le_three_pow i
  obtain ⟨r₂, r₃, hr₂, hr₃, shifts⟩ := allShifts i
  change r₂ < P at hr₂
  change r₃ < 3 ^ b at hr₃
  have hco : P.Coprime (3 ^ b) := (show Nat.Coprime 2 3 by decide).pow a b
  let L : ℕ := Nat.chineseRemainder hco r₂ r₃
  have hL : L < P * 3 ^ b :=
    Nat.chineseRemainder_lt_mul hco r₂ r₃ (by positivity) (by positivity)
  have hL₂ : L % P = r₂ := by
    have he := (Nat.chineseRemainder hco r₂ r₃).2.1
    simpa [Nat.ModEq, L, Nat.mod_eq_of_lt hr₂] using he
  have hL₃ : L % 3 ^ b = r₃ := by
    have he := (Nat.chineseRemainder hco r₂ r₃).2.2
    simpa [Nat.ModEq, L, Nat.mod_eq_of_lt hr₃] using he
  have hL' : L < 3 ^ (a + b) := by
    rw [pow_add]
    exact hL.trans_le (Nat.mul_le_mul_right _ (two_le_three_pow a))
  have hc₂ : s 2 r₂ ≤ a := by simpa using s_bound 2 (by decide) hr₂
  have hc₃ : s 3 L ≤ 2 * (a + b) := by simpa using s_bound 3 (by decide) hL'
  let u₃ := Nat.clog 3 P
  let v₃ := t + 1
  let v₂ := Nat.clog 2 M + 1
  let mid := z - half
  -- E is the binary contribution needed to center the difference at mid.
  let E : ℤ := (u₃ + v₃ : ℕ) + s 3 L - s 2 r₂ - mid
  let u₂ := (2 * E - v₂).toNat
  have hu₃ : u₃ ≤ a := Nat.clog_le_of_le_pow (two_le_three_pow a)
  have hv₂ := log_range h
  change 9 * h ≤ Nat.clog 2 M ∧ Nat.clog 2 M ≤ 10 * h at hv₂
  have hz₁ : z ≤ (z.natAbs : ℤ) := Int.le_natAbs
  have hz₂ : -z ≤ (z.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -z))
  have hsmall₁ : 11 * (a + b) ≤ h := by dsimp [h]; omega
  have hsmall₂ : 20 * K ≤ h := by dsimp [h]; omega
  have hsmall₃ : 20 * z.natAbs ≤ h := by dsimp [h]; omega
  have hEu : (h : ℤ) ≤ 2 * E - v₂ := by
    dsimp [E, mid, v₂, v₃, t]
    omega
  have hEl : 2 * E - v₂ ≤ (4 : ℤ) * h := by
    dsimp [E, mid, v₂, v₃, t]
    omega
  have hu₂_cast : (u₂ : ℤ) = 2 * E - v₂ := Int.toNat_of_nonneg (by omega)
  have hu₂lo : h ≤ u₂ := by omega
  have hu₂hi : u₂ ≤ 4 * h := by omega
  -- Make the ternary step comparable to the chosen binary low-block size.
  let alpha := Nat.log 3 (2 ^ u₂)
  let Q := (3 : ℕ) ^ alpha
  have hQlo : Q ≤ 2 ^ u₂ := Nat.pow_log_le_self 3 (by positivity)
  have hQhi : 2 ^ u₂ < 3 * Q := by
    simpa only [Q, alpha, pow_succ'] using Nat.lt_pow_succ_log_self (by decide : 1 < 3) (2 ^ u₂)
  have hα : a + b ≤ alpha := by
    apply Nat.le_log_of_pow_le (by decide)
    refine (three_le_four_pow (a + b)).trans (Nat.pow_le_pow_right (by decide) ?_)
    dsimp [h] at hu₂lo
    omega
  have hLQ : L < Q := hL'.trans_le (Nat.pow_le_pow_right (by decide) hα)
  have hLdiv : L / P < Q := (Nat.div_le_self _ _).trans_lt hLQ
  have hB₂M : 2 ^ u₂ ≤ M := by
    have hpos : u₂ ≤ 9 * h := by omega
    have h₁ : (2 : ℕ) ^ (9 * h) ≤ M := by
      dsimp [M, t]
      simp only [pow_mul]
      exact Nat.pow_le_pow_left (by decide) _
    exact (Nat.pow_le_pow_right (by decide) hpos).trans h₁
  have hB₃M : 3 ^ u₃ ≤ M := by
    apply Nat.pow_le_pow_right (by decide)
    dsimp [t, h]
    omega
  have hB₃lo : P ≤ 3 ^ u₃ := Nat.le_pow_clog (by decide) _
  have hB₃hi : 3 ^ u₃ < 3 * P := clog_bound 3 P (by decide) hPp
  have hv₂lo : 2 * M ≤ 2 ^ v₂ := by
    dsimp [v₂]
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)
  have hv₂hi : 2 ^ v₂ ≤ 9 * M := by
    dsimp [v₂]
    rw [pow_succ']
    have hh' := clog_bound 2 M (by decide) hMp
    omega
  have hv₃eq : (3 : ℕ) ^ v₃ = 3 * M := by simp only [v₃, M, pow_succ']
  have hs₂ := affineMoment 2 u₂ v₂ Q (L / P) M (by decide) (by decide)
    hLdiv hQlo hQhi hB₂M ((show Nat.Coprime 2 3 by decide).pow u₂ alpha) hv₂lo hv₂hi
  have hs₃ := affineMoment 3 u₃ v₃ P 0 M (by decide) (by decide)
    hPp hB₃lo hB₃hi hB₃M ((show Nat.Coprime 3 2 by decide).pow u₃ a)
    (by omega) (by omega)
  let X₂ := fun k : ℕ => Q * (M + k) + L / P
  let X₃ := fun k : ℕ => P * (M + k)
  let n := fun k : ℕ => L + Q * X₃ k
  let score := fun k : ℕ => (err 3 (u₃ + v₃) (X₃ k) - err 2 (u₂ + v₂) (X₂ k)) ^ 2
  have hsc : ∑ k ∈ range M, score k ≤ (10000 : ℤ) * h * M := by
    change ∑ k ∈ range M, err 2 (u₂ + v₂) (X₂ k) ^ 2 ≤ _ at hs₂
    simp only [add_zero] at hs₃
    change ∑ k ∈ range M, err 3 (u₃ + v₃) (X₃ k) ^ 2 ≤ _ at hs₃
    have hlen : u₂ + v₂ + u₃ + v₃ ≤ 23 * h := by
      dsimp [v₂, v₃, t]
      have haux : u₃ ≤ h := by dsimp [h]; omega
      omega
    have hlen' : ((u₂ + v₂ + u₃ + v₃ : ℕ) : ℤ) ≤ 23 * h := by exact_mod_cast hlen
    have hlen'' := mul_le_mul_of_nonneg_right hlen' (show (0 : ℤ) ≤ M by positivity)
    calc
      _ ≤ ∑ k ∈ range M,
          (2 * err 3 (u₃ + v₃) (X₃ k) ^ 2 + 2 * err 2 (u₂ + v₂) (X₂ k) ^ 2) := by
        apply Finset.sum_le_sum
        intro k _
        dsimp [score]
        nlinarith only [sq_nonneg (err 3 (u₃ + v₃) (X₃ k) + err 2 (u₂ + v₂) (X₂ k))]
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        push_cast at hs₂ hs₃ hlen''
        nlinarith only [hs₂, hs₃, hlen'', mul_nonneg (show (0 : ℤ) ≤ h by positivity)
          (show (0 : ℤ) ≤ M by positivity)]
  have hex : ∑ k ∈ range M, score k < ∑ _k ∈ range M, (K : ℤ) ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have := mul_lt_mul_of_pos_right hgap (show (0 : ℤ) < M by exact_mod_cast hMp)
    linarith
  obtain ⟨k, _, hk⟩ := Finset.exists_lt_of_sum_lt hex
  have hn₂ : n k = r₂ + P * X₂ k := by
    have hdecomp : L % P + P * (L / P) = L := Nat.mod_add_div _ _
    rw [hL₂] at hdecomp
    dsimp only [n, X₂, X₃]
    nth_rewrite 1 [← hdecomp]
    rw [mul_add P (Q * (M + k)) (L / P)]
    ac_rfl
  have hn₃ : n k = L + Q * X₃ k := rfl
  have hd₂ : s 2 (n k) = s 2 r₂ + s 2 (X₂ k) := by
    rw [hn₂, split 2 (by decide) hr₂]
  have hd₃ : s 3 (n k) = s 3 L + s 3 (X₃ k) := by
    rw [hn₃, split 3 (by decide) hLQ]
  have hcent : err 3 (u₃ + v₃) (X₃ k) - err 2 (u₂ + v₂) (X₂ k) =
      2 * (OeisA180017.a (n k) - mid) := by
    change _ = 2 * ((s 3 (n k) : ℤ) - s 2 (n k) - mid)
    rw [hd₂, hd₃]
    unfold err
    push_cast
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one, one_mul]
    dsimp [E] at hu₂_cast
    linarith only [hu₂_cast]
  have hnear : -(K : ℤ) < 2 * (OeisA180017.a (n k) - mid) ∧
      2 * (OeisA180017.a (n k) - mid) < K := by
    change (err 3 (u₃ + v₃) (X₃ k) - err 2 (u₂ + v₂) (X₂ k)) ^ 2 < (K : ℤ) ^ 2 at hk
    rw [hcent] at hk
    have hKp : (0 : ℤ) ≤ K := by positivity
    constructor <;> by_contra! hh'
    · have hg := mul_nonneg (show 0 ≤ -(2 * (OeisA180017.a (n k) - mid)) - K by linarith)
        (show 0 ≤ -(2 * (OeisA180017.a (n k) - mid)) + K by linarith)
      nlinarith only [hg, hk]
    · have hg := mul_nonneg (show 0 ≤ (2 * (OeisA180017.a (n k) - mid)) - K by linarith)
        (show 0 ≤ (2 * (OeisA180017.a (n k) - mid)) + K by linarith)
      nlinarith only [hg, hk]
  let j := (z - OeisA180017.a (n k)).toNat
  have hj : (j : ℤ) = z - OeisA180017.a (n k) := by
    apply Int.toNat_of_nonneg
    dsimp [mid] at hnear
    omega
  have hj' : j < K := by dsimp [mid] at hnear; omega
  obtain ⟨d, hd₂', hd₃', hd⟩ := shifts j hj'
  have hm₂ : n k % P = r₂ := by rw [hn₂, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr₂]
  have hm₃ : n k % 3 ^ b = r₃ := by
    have hdvd : (3 : ℕ) ^ b ∣ Q * X₃ k :=
      dvd_mul_of_dvd_left (Nat.pow_dvd_pow _ (by omega : b ≤ alpha)) _
    rw [hn₃, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, add_zero, Nat.mod_mod, hL₃]
  have hdif₂ := shift_transfer 2 (by decide) hm₂ hd₂'
  have hdif₃ := shift_transfer 3 (by decide) hm₃ hd₃'
  refine ⟨n k + d, ?_, ?_⟩
  · have h₁ : M ≤ M + k := by omega
    have h₂ : M + k ≤ X₃ k := by
      simpa only [one_mul] using Nat.mul_le_mul_right (M + k) (show 1 ≤ P by omega)
    have hq₁ : 1 ≤ Q := Nat.one_le_pow alpha 3 (by decide)
    have h₃ : X₃ k ≤ Q * X₃ k := by
      simpa only [one_mul] using Nat.mul_le_mul_right (X₃ k) hq₁
    change N < L + Q * X₃ k + d
    omega
  · change (s 3 (n k + d) : ℤ) - s 2 (n k + d) = z
    change (j : ℤ) = z - ((s 3 (n k) : ℤ) - s 2 (n k)) at hj
    linarith only [hdif₂, hdif₃, hd, hj]

end OMA.A180017

-- Credit: @MrSeizy
theorem OMA.solution : type_of% @OeisA180017.conjecture := by
  intro z
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hz⟩ := OMA.A180017.large_value z N
  exact ⟨n, hz, hn⟩
