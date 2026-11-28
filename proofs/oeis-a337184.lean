import OMAStatements.S_oeis_a337184

/-!
# Bounds on the numbers divisible by their first and last digits

On an interval with fixed leading digit, membership is periodic modulo 2520.
A checked prefix of one period bounds the discrepancy between the actual
count and its mean on any subinterval. This controls the count on each
decimal decade. A separate finite check covers the stated starting index.
-/

namespace Digit337184

/-- Test the two digit divisibilities when the leading digit is fixed. -/
def good (d m : ℕ) : Bool := decide (m % 10 ≠ 0 ∧ m % 10 ∣ m ∧ d ∣ m)

/-- Number of qualifying residues in a full period for leading digit d. -/
def weight (d : ℕ) : ℕ := ((Finset.range 2520).filter fun i => good d i).card

def weightValue : ℕ → ℕ
  | 1 => 1177 | 2 => 525 | 3 => 523 | 4 => 357 | 5 => 252
  | 6 => 231 | 7 => 199 | 8 => 210 | 9 => 193 | _ => 0

set_option maxRecDepth 20000 in
theorem weight_eq (d : ℕ) (hd : d ≤ 9) : weight d = weightValue d := by
  have table : ∀ j : Fin 10, weight j.val = weightValue j.val := by decide +kernel
  exact table ⟨d,by omega⟩

theorem good_periodic (d : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 9) : Function.Periodic (good d) 2520 := by
  have divisors (u : ℕ) (h₁ : 1 ≤ u) (h₂ : u ≤ 9) : u ∣ 2520 := by
    interval_cases u <;> decide
  intro m
  have he : (m+2520)%10 = m%10 := by omega
  by_cases hz : m%10 = 0
  · simp [good, he, hz]
  have hm := Nat.mod_lt m (by decide : 0 < 10)
  simp only [good, he, ← Nat.dvd_add_iff_left (divisors d hd hd'),
    ← Nat.dvd_add_iff_left (divisors (m%10) (by omega) (by omega))]

private def discrepancy (d m : ℕ) : ℤ :=
  2520 * (Nat.count (fun i => good d i) m : ℤ) - (m : ℤ) * (weight d : ℤ)

private theorem discrepancy_succ (d m : ℕ) :
    discrepancy d (m+1) = discrepancy d m + (if good d m then 2520 else 0) - weight d := by
  rw [discrepancy, Nat.count_succ, discrepancy]
  split_ifs <;> push_cast <;> ring

private def check (d : ℕ) (w : ℤ) : ℕ → ℕ → ℤ → Bool
  | 0, _, a => decide (-8118 ≤ a ∧ a ≤ 12419)
  | fuel+1, pos, a => decide (-8118 ≤ a ∧ a ≤ 12419) &&
      check d w fuel (pos+1) (a + (if good d pos then 2520 else 0) - w)

private theorem check_sound (d : ℕ) (fuel pos i : ℕ) (hi : i ≤ fuel)
    (h : check d (weight d) fuel pos (discrepancy d pos) = true) :
    -8118 ≤ discrepancy d (pos+i) ∧ discrepancy d (pos+i) ≤ 12419 := by
  induction fuel generalizing pos i with
  | zero =>
    obtain rfl : i=0 := by omega
    simpa [check] using h
  | succ fuel ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, ← discrepancy_succ] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (pos+1) i (by omega) h.2

set_option maxRecDepth 40000 in
set_option maxHeartbeats 3000000 in
private theorem discrepancy_bounds (d : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 9) (m : ℕ) :
    -8118 ≤ discrepancy d m ∧ discrepancy d m ≤ 12419 := by
  have periodic : Function.Periodic (discrepancy d) 2520 := by
    intro i
    have hcount : Nat.count (fun j => good d j) (i+2520) =
        Nat.count (fun j => good d j) i + weight d := by
      rw [Nat.count_add']
      simp_rw [good_periodic d hd hd' _]
      simp only [Nat.count_eq_card_filter_range, weight]
    unfold discrepancy
    rw [hcount]
    push_cast
    ring
  rw [← periodic.map_mod_nat m]
  have verified : ∀ u : Fin 10, u.val = 0 ∨ check u.val (weightValue u.val) 2520 0 0 = true := by
    decide +kernel
  have ok : check d (weightValue d) 2520 0 0 = true :=
    (verified ⟨d,by omega⟩).resolve_left (show d ≠ 0 by omega)
  rw [← weight_eq d hd'] at ok
  simpa using check_sound d 2520 0 (m%2520) (by omega) (by simpa [discrepancy] using ok)

/-- The periodic mean approximates the count on any interval with uniform error. -/
theorem block_bound (d L t : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 9) :
    |2520 * (Nat.count (fun i => good d (L+i)) t : ℤ) - (t : ℤ) * (weight d : ℤ)| ≤ 21000 := by
  have eq : 2520 * (Nat.count (fun i => good d (L+i)) t : ℤ) - (t : ℤ) * (weight d : ℤ) =
      discrepancy d (L+t) - discrepancy d L := by
    unfold discrepancy
    rw [Nat.count_add]
    push_cast
    ring
  rw [eq,abs_le]
  have h₁ := discrepancy_bounds d hd hd' (L+t)
  have h₂ := discrepancy_bounds d hd hd' L
  omega

theorem block_bound_card (d L t : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 9) :
    |2520 * ((((Finset.range t).filter (fun i => good d (L+i))).card : ℕ) : ℤ)
      - (t : ℤ) * (weight d : ℤ)| ≤ 21000 := by
  simpa only [Nat.count_eq_card_filter_range] using block_bound d L t hd hd'

end Digit337184

namespace Digit337184
open OMA.S_oeis_a337184

instance decIsTerm : DecidablePred IsTerm := fun m => by
  unfold IsTerm
  infer_instance

/-- Number of terms strictly less than x. -/
def termCount (x : ℕ) : ℕ := Nat.count IsTerm x

theorem leading_digit {d k x : ℕ} (hd : 1 ≤ d) (hd9 : d ≤ 9)
    (hl : d * 10 ^ k ≤ x) (hu : x < (d+1) * 10 ^ k) :
    (Nat.digits 10 x).getLastD 0 = d := by
  let r := x - d * 10 ^ k
  rw [Nat.add_mul, Nat.one_mul] at hu
  have hr : r < 10 ^ k := by dsimp [r]; omega
  have heq : r + 10 ^ k * d = x := by rw [Nat.mul_comm]; exact Nat.sub_add_cancel hl
  have hlen := (Nat.digits_length_le_iff (by decide : 1 < 10) r).mpr hr
  have hlen' : (Nat.digits 10 r).length + (k - (Nat.digits 10 r).length) = k := by omega
  have h := Nat.digits_append_zeroes_append_digits
    (k := k - (Nat.digits 10 r).length) (n := r) (by decide : 1 < 10) hd
  rw [hlen', heq, Nat.digits_of_lt 10 d (by omega) (by omega)] at h
  rw [← h, List.getLastD_concat]

theorem isTerm_iff_good {d k x : ℕ} (hd : 1 ≤ d) (hd9 : d ≤ 9)
    (hl : d * 10 ^ k ≤ x) (hu : x < (d+1) * 10 ^ k) :
    IsTerm x ↔ good d x := by
  have hpos : 0 < d * 10 ^ k := Nat.mul_pos hd (by positivity)
  simp only [IsTerm, Nat.lt_of_lt_of_le hpos hl, true_and, leading_digit hd hd9 hl hu,
    good, decide_eq_true_eq]

theorem termCount_block_add (d k t : ℕ) (hd : 1 ≤ d) (hd9 : d ≤ 9) (ht : t ≤ 10 ^ k) :
    termCount (d * 10 ^ k + t) = termCount (d * 10 ^ k) +
      Nat.count (fun j => good d (d * 10 ^ k + j)) t := by
  rw [termCount, Nat.count_add, termCount]
  congr 1
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  exact isTerm_iff_good (k := k) hd hd9 (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)

theorem termCount_block_sub (d k t : ℕ) (hd : 1 ≤ d) (hd9 : d ≤ 9) (ht : t ≤ 10 ^ k) :
    termCount (d * 10 ^ k + t) - termCount (d * 10 ^ k) =
      Nat.count (fun j => good d (d * 10 ^ k + j)) t := by
  rw [termCount_block_add d k t hd hd9 ht, Nat.add_sub_cancel_left]

theorem bounds_of_counts (n : ℕ) (hn : 0 < n)
    (hlo : termCount (3*n+1) < n) (hhi : n ≤ termCount (7*n)) :
    3*n < a n ∧ a n < 7*n := by
  change Nat.count IsTerm (3*n+1) < n at hlo
  change n ≤ Nat.count IsTerm (7*n) at hhi
  change 3*n < Nat.nth IsTerm (n-1) ∧ Nat.nth IsTerm (n-1) < 7*n
  have hj : n-1 < Nat.count IsTerm (7*n) := by omega
  refine ⟨?_, Nat.nth_lt_of_lt_count hj⟩
  have hcnt : Nat.count IsTerm (Nat.nth IsTerm (n-1) + 1) = n-1+1 :=
    Nat.count_nth_succ (fun hf => hj.trans_le (Nat.count_le_card hf _))
  by_contra! hle
  have hmono := Nat.count_monotone IsTerm (Nat.add_le_add_right hle 1)
  omega

end Digit337184

/-! Linear bounds for prefix counts from the nine residue densities. -/
namespace Digit337184

def rowWeight : ℕ → ℤ
  | 1 => 1177 | 2 => 525 | 3 => 523 | 4 => 357 | 5 => 252
  | 6 => 231 | 7 => 199 | 8 => 210 | 9 => 193 | _ => 0

private def weightSum : ℕ → ℤ
  | 0 => 0
  | j+1 => weightSum j + rowWeight (j+1)

def RowEstimate (F : ℕ → ℕ) (B : ℕ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → d ≤ 9 → ∀ t : ℕ, t ≤ B →
    |2520*((F (d*B+t):ℤ)-F (d*B))-(t:ℤ)*rowWeight d| ≤ 21000

private lemma complete_prefix {F B} (h : RowEstimate F B) (j : ℕ) (hj : j ≤ 9) :
    |2520*((F ((j+1)*B):ℤ)-F B) - (B:ℤ)*weightSum j| ≤ 21000*(j:ℤ) := by
  induction j with
  | zero => simp [weightSum]
  | succ j ih =>
    have prev := ih (by omega)
    have step := h (j+1) (by omega) hj B le_rfl
    rw [show (j+1+1)*B = (j+1)*B+B by ring, weightSum]
    calc _ = |(2520*((F ((j+1)*B):ℤ)-F B) - (B:ℤ)*weightSum j) +
          (2520*((F ((j+1)*B+B):ℤ)-F ((j+1)*B)) - (B:ℤ)*rowWeight (j+1))| := by
            congr 1; ring
         _ ≤ _ := by
           apply (abs_add_le ..).trans
           push_cast
           linarith

private def BaseBounds (F : ℕ → ℕ) (B : ℕ) : Prop :=
  385*(B:ℤ) ≤ 2520*(F B:ℤ) ∧ 2520*(F B:ℤ) ≤ 430*(B:ℤ)

private lemma next_base {F B} (hb : 1000 ≤ B) (base : BaseBounds F B)
    (h : RowEstimate F B) : BaseBounds F (10*B) := by
  obtain ⟨hl,hu⟩ := base
  have hh := abs_le.mp (complete_prefix h 9 (by decide))
  norm_num [weightSum, rowWeight] at hh
  have hB : (1000:ℤ) ≤ B := by exact_mod_cast hb
  unfold BaseBounds
  push_cast
  constructor <;> linarith [hh.1,hh.2]

private lemma between {F B} (hb : 1000 ≤ B) (base : BaseBounds F B)
    (h : RowEstimate F B) (j t : ℕ) (hj : j ≤ 8) (ht : t ≤ B) :
    3*(F ((j+1)*B+t):ℤ)+2 ≤ (((j+1)*B+t:ℕ):ℤ) ∧
      (((j+1)*B+t:ℕ):ℤ) ≤ 7*(F ((j+1)*B+t):ℤ) := by
  obtain ⟨hl,hu⟩ := base
  obtain ⟨pl,pu⟩ := abs_le.mp (complete_prefix h j (by omega))
  obtain ⟨rl,ru⟩ := abs_le.mp (h (j+1) (by omega) (by omega) t ht)
  have hB : (1000:ℤ) ≤ B := by exact_mod_cast hb
  have htB : (t:ℤ) ≤ B := by exact_mod_cast ht
  have htz : (0:ℤ) ≤ t := by positivity
  interval_cases j <;> norm_num [weightSum,rowWeight] at pl pu rl ru ⊢ <;>
    constructor <;> linarith

theorem decade_bounds (F : ℕ → ℕ) (first : F 1000 = 168)
    (rows : ∀ k : ℕ, RowEstimate F (10^k)) (x : ℕ) (hx : 1000 ≤ x) :
    3*F x+2 ≤ x ∧ x ≤ 7*F x := by
  have bases : ∀ k : ℕ, BaseBounds F (10^(3+k)) := by
    intro k
    induction k with
    | zero =>
      norm_num [BaseBounds, first]
    | succ k ih =>
      have hm : 1000 ≤ 10^(3+k) := by
        calc 1000 = 10^3 := by decide
             _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
      rw [show 3+(k+1) = (3+k)+1 by omega, pow_succ, Nat.mul_comm]
      exact next_base hm ih (rows _)
  let k := Nat.log 10 x
  let B := 10^k
  have hx0 : x ≠ 0 := by omega
  have hle : B ≤ x := Nat.pow_log_le_self 10 hx0
  have hlt : x < B * 10 := by simpa only [B,k,pow_succ] using
    (Nat.lt_pow_succ_log_self (b:=10) (by decide) x)
  have hk : 3 ≤ k := (Nat.le_log_iff_pow_le (by decide : 1 < 10) hx0).mpr hx
  have hb : 1000 ≤ B := Nat.pow_le_pow_right (by decide : 0 < 10) hk
  have hB0 : 0 < B := by omega
  have base : BaseBounds F B := by
    simpa only [B, show 3+(k-3)=k by omega] using bases (k-3)
  have d1 : 1 ≤ x/B := (Nat.le_div_iff_mul_le hB0).mpr (by simpa using hle)
  have d9 : x/B < 10 := (Nat.div_lt_iff_lt_mul hB0).mpr (by simpa [mul_comm] using hlt)
  have tB := Nat.mod_lt x hB0
  have eqx : x/B * B + x%B = x := by simpa [mul_comm,add_comm] using Nat.mod_add_div x B
  have rr := between hb base (rows k) (x/B-1) (x%B) (by omega) tB.le
  rw [show x/B-1+1=x/B by omega,eqx] at rr
  exact_mod_cast rr

end Digit337184

open OMA.S_oeis_a337184

namespace Digit337184

private def prefixTest (x c : ℕ) : Bool :=
  decide ((x % 3 = 1 → 75 < (x-1)/3 → c < (x-1)/3) ∧
    (x % 7 = 0 → 75 < x/7 → x/7 ≤ c) ∧ (x = 1000 → c = 168))

/-- The first coordinate counts terms below x. The second records the
endpoint tests through x, including the offset at 1000. -/
private def prefixScan : ℕ → ℕ × Bool
  | 0 => (0, true)
  | x+1 =>
    let prev := prefixScan x
    let c := prev.1 + if IsTerm x then 1 else 0
    (c, prev.2 && prefixTest (x+1) c)

private lemma prefixScan_spec (t : ℕ) :
    (prefixScan t).1 = termCount t ∧
    ((prefixScan t).2 = true → ∀ x ≤ t, prefixTest x (termCount x) = true) := by
  induction t with
  | zero =>
    refine ⟨by simp [prefixScan, termCount], ?_⟩
    intro _ x hx
    obtain rfl : x = 0 := by omega
    decide
  | succ t ih =>
    have hc : (prefixScan (t+1)).1 = termCount (t+1) := by
      simp only [prefixScan, ih.1, termCount, Nat.count_succ]
    refine ⟨hc, ?_⟩
    intro h x hx
    have hh : (prefixScan t).2 = true ∧ prefixTest (t+1) ((prefixScan (t+1)).1) = true :=
      Bool.and_eq_true_iff.mp h
    rcases Nat.lt_or_eq_of_le hx with hlt | rfl
    · exact ih.2 hh.1 x (by omega)
    · simpa only [hc] using hh.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private lemma prefix_certificate : (prefixScan 2331).2 = true := by decide +kernel

theorem count_1000 : termCount 1000 = 168 := by
  have hh := (prefixScan_spec 2331).2 prefix_certificate 1000 (by decide)
  exact (of_decide_eq_true hh).2.2 rfl

theorem finite_bounds (n : ℕ) (hn : 75 < n) (hle : n ≤ 333) :
    3*n < a n ∧ a n < 7*n := by
  have hs := (prefixScan_spec 2331).2 prefix_certificate
  have hlo := (of_decide_eq_true (hs (3*n+1) (by omega))).1 (by omega) (by omega)
  have hhi := (of_decide_eq_true (hs (7*n) (by omega))).2.1 (by omega) (by omega)
  exact bounds_of_counts n (by omega) (by omega) (by omega)

end Digit337184

namespace Digit337184

private theorem decimal_rows (k : ℕ) : RowEstimate termCount (10^k) := by
  intro d hd hd' t ht
  have hw : (weight d : ℤ) = rowWeight d := by
    rw [weight_eq d hd']
    interval_cases d <;> rfl
  have h := block_bound d (d*10^k) t hd hd'
  rw [termCount_block_add d k t hd hd' ht, Nat.cast_add, add_sub_cancel_left, ← hw]
  exact h

end Digit337184

open Digit337184 in
theorem OMA.solution : type_of% @OMA.S_oeis_a337184.main := by
  intro n hn
  by_cases h : n ≤ 333
  · exact finite_bounds n hn h
  have lower := (decade_bounds termCount count_1000 decimal_rows (3*n+1) (by omega)).1
  have upper := (decade_bounds termCount count_1000 decimal_rows (7*n) (by omega)).2
  exact bounds_of_counts n (by omega) (by omega) (by omega)
