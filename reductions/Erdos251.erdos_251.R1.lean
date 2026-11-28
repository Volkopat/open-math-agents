import FormalConjectures.ErdosProblems.«251»

/-!
Two finite arithmetic problems concerning the primes. The first asks for arbitrarily
accurate dyadic shifts near an integer. The second asks for shifts near an integer
plus one third. A rational doubling orbit cannot meet both requirements.

The bounds in each hypothesis use only the first n primes. They include the error
from later terms. The prime-growth estimates are from OrangeHeadz's open-math-agents proof
of Erdos983.erdos_983.parts.i. The unconditional theorem classical_denominator_gt
uses the first 725 primes to exclude every positive denominator up to 10^104.
-/

namespace OMA.R_Erdos251_erdos_251_R1

def H1 : Prop :=
  ∀ B : ℕ, 0 < B → ∃ n s z : ℕ,
    let P := ∑ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℝ) / 2 ^ i
    let E := 34 * (((n : ℝ) + 2)^2 + 2 * (n + 2) + 3) / 2 ^ n
    let w := (B : ℝ) * 2 ^ s
    let v := (B : ℝ) * z
    v < w * P + 1 ∧ w * (P + E) < v + 1

def H2 : Prop :=
  ∀ B : ℕ, 0 < B → ∃ n s z : ℕ,
    let P := ∑ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℝ) / 2 ^ i
    let E := 34 * (((n : ℝ) + 2)^2 + 2 * (n + 2) + 3) / 2 ^ n
    let w := (B : ℝ) * 3 * 2 ^ s
    let v := (B : ℝ) * (3 * (z : ℝ) + 1)
    v < w * P + 1 ∧ w * (P + E) < v + 1

/-- `π (p_n) = n + 1` for the `n`-th prime (zero indexed). -/
theorem pi_nth (n : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, if_pos (Nat.prime_nth_prime n)]
  have := Nat.primeCounting'_nth_eq n
  rw [Nat.primeCounting'] at this
  rw [this]

theorem log_le_two_sqrt (x : ℝ) (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  linarith

/-- A polynomial bound for the `n`-th prime, from Chebyshev's lower bound for `π`. -/
theorem nth_prime_le (n : ℕ) : (Nat.nth Nat.Prime n : ℝ) ≤ 17 * ((n : ℝ) + 2) ^ 2 := by
  set p : ℕ := Nat.nth Nat.Prime n with hp
  have hp2 : 2 ≤ p := by
    have := Nat.add_two_le_nth_prime n
    omega
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hpi := Chebyshev.pi_ge p
  rw [pi_nth n] at hpi
  rw [div_le_iff₀ hlogp] at hpi
  push_cast at hpi
  have hL : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog1 : Real.log (p : ℝ) ≤ Real.log ((p : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log ((p : ℝ) + 1) ≤ 2 * Real.sqrt ((p : ℝ) + 1) :=
    log_le_two_sqrt _ (by linarith)
  set s : ℝ := Real.sqrt ((p : ℝ) + 1) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (p : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- p * log 2 ≤ 2 * (n + 2) * s
  have h1 : (p : ℝ) * Real.log 2 ≤ 2 * ((n : ℝ) + 2) * s := by
    have h2 : ((n : ℝ) + 1) * Real.log (p : ℝ) ≤ ((n : ℝ) + 1) * (2 * s) :=
      mul_le_mul_of_nonneg_left (hlog1.trans hlog2) (by linarith)
    nlinarith
  -- hence 0.69 * p ≤ 2 * (n + 2) * s
  have h3 : 0.69 * (p : ℝ) ≤ 2 * ((n : ℝ) + 2) * s := by
    have : 0.69 * (p : ℝ) ≤ (p : ℝ) * Real.log 2 := by nlinarith
    linarith
  -- square
  have h4 : (0.69 * (p : ℝ)) ^ 2 ≤ (2 * ((n : ℝ) + 2) * s) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have h5 : (2 * ((n : ℝ) + 2) * s) ^ 2 = 4 * ((n : ℝ) + 2) ^ 2 * ((p : ℝ) + 1) := by
    rw [← hs2]; ring
  rw [h5] at h4
  by_contra hcon
  rw [not_le] at hcon
  have hm : 0 < ((n : ℝ) + 2) ^ 2 := by positivity
  -- 4 (n+2)^2 (p+1) < (4/17) p (p+1) ≤ (6/17) p^2 < 0.4761 p^2
  have h6 : 4 * ((n : ℝ) + 2) ^ 2 * ((p : ℝ) + 1) ≤ 4 / 17 * (p : ℝ) * ((p : ℝ) + 1) := by
    have : 4 * ((n : ℝ) + 2) ^ 2 ≤ 4 / 17 * (p : ℝ) := by linarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  nlinarith

theorem enclosure (n : ℕ) :
    let f := fun i : ℕ => (Nat.nth Nat.Prime i : ℝ) / 2 ^ i
    let e := 34 * (((n : ℝ) + 2)^2 + 2 * (n + 2) + 3) / 2 ^ n
    (∑ i ∈ Finset.range n, f i) ≤ ∑' i, f i ∧
      (∑' i, f i) ≤ (∑ i ∈ Finset.range n, f i) + e := by
  let f := fun i : ℕ => (Nat.nth Nat.Prime i : ℝ) / 2 ^ i
  let E := fun i : ℕ => 34 * (((i : ℝ) + 2)^2 + 2 * (i + 2) + 3) / 2 ^ i
  change _ ≤ ∑' i, f i ∧ (∑' i, f i) ≤ _ + E n
  have step (i : ℕ) : f i + E (i + 1) ≤ E i := by
    have hp := nth_prime_le i
    dsimp [f, E]
    push_cast
    rw [pow_succ (2 : ℝ) i, ← div_div, div_right_comm, ← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have bound (a k : ℕ) :
      (∑ i ∈ Finset.range k, f (i + a)) + E (k + a) ≤ E a := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Nat.succ_add]
      rw [add_assoc]
      exact (add_le_add (le_refl _) (step (k + a))).trans ih
  have blocks (a k : ℕ) : (∑ i ∈ Finset.range k, f (i + a)) ≤ E a := by
    have : 0 ≤ E (k + a) := by dsimp [E]; positivity
    linarith [bound a k]
  have nonneg (i : ℕ) : 0 ≤ f i := by dsimp [f]; positivity
  have conv : Summable f := by
    apply summable_of_sum_range_le (c := E 0) nonneg
    simpa using blocks 0
  have split := conv.sum_add_tsum_nat_add n
  have lo : 0 ≤ ∑' i, f (i + n) := tsum_nonneg fun i => nonneg (i + n)
  have hi := Real.tsum_le_of_sum_range_le (fun i => nonneg (i + n)) (blocks n)
  constructor <;> linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Exact value of the first 725 terms in the zero-indexed normalization. -/
theorem partial_sum_725 :
    (∑ i ∈ Finset.range 725, (Nat.nth Nat.Prime i : ℝ) / 2 ^ i) =
      2 * (648577865831182325612411035880719417722646599476150973757179182467579233878131949712432035876500897490813322977310952878917556348734096745880672585602508137131136577261204414606402740585015832859877341227558038026065269 : ℕ) / (2 : ℝ) ^ 725 := by
  let trialPrime (k : ℕ) : Bool :=
    decide (2 ≤ k) && (List.range 75).all (fun d => decide (d < 2 ∨ k ≤ d ∨ k % d ≠ 0))
  have trialPrime_iff {k : ℕ} (hsmall : k < 5500) : trialPrime k = true ↔ k.Prime := by
    simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
    constructor
    · rintro ⟨hk, h⟩
      by_contra hn
      have hsq := Nat.minFac_sq_le_self (by omega : 0 < k) hn
      have hs : k.minFac < 75 := by
        by_contra! hge
        have := Nat.pow_le_pow_left hge 2
        omega
      have hf := h k.minFac hs
      have hlt := (Nat.not_prime_iff_minFac_lt hk).mp hn
      have htwo := Nat.minFac_prime (by omega : k ≠ 1) |>.two_le
      have hd := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd k)
      omega
    · intro hk
      refine ⟨hk.two_le, fun d hd => ?_⟩
      by_cases h : d < 2
      · exact Or.inl h
      · by_cases hkd : k ≤ d
        · exact Or.inr (Or.inl hkd)
        refine Or.inr (Or.inr (fun hm => ?_))
        exact (Nat.prime_def_lt'.mp hk).2 d (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hm)
  let scan : ℕ → ℕ × ℕ := Nat.rec (0, 0) (fun k state =>
    if trialPrime k then (state.1 + 1, 2 * state.2 + k) else state)
  have scan_succ (k : ℕ) : scan (k + 1) =
      (if trialPrime k then ((scan k).1 + 1, 2 * (scan k).2 + k) else scan k) := rfl
  have spec (k : ℕ) (hk : k ≤ 5500) :
      (scan k).1 = Nat.count Nat.Prime k ∧
      (∑ i ∈ Finset.range (scan k).1, (Nat.nth Nat.Prime i : ℝ) / 2 ^ i) =
        2 * ((scan k).2 : ℝ) / 2 ^ (scan k).1 := by
    induction k with
    | zero => simp [scan]
    | succ k ih =>
      obtain ⟨hc, hv⟩ := ih (by omega)
      rw [scan_succ, Nat.count_succ]
      by_cases hp : k.Prime
      · rw [if_pos hp, if_pos ((trialPrime_iff (by omega)).mpr hp)]
        simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat, pow_succ]
        constructor
        · omega
        · rw [hv, hc, Nat.nth_count hp]
          ring
      · rw [if_neg hp, if_neg (fun h => hp ((trialPrime_iff (by omega)).mp h))]
        simpa using And.intro hc hv
  have value : scan 5500 = (725, 648577865831182325612411035880719417722646599476150973757179182467579233878131949712432035876500897490813322977310952878917556348734096745880672585602508137131136577261204414606402740585015832859877341227558038026065269) := by decide +kernel
  simpa only [value] using (spec 5500 (by decide)).2

/-- A finite interval between Farey neighbours excludes every denominator below b+d. -/
theorem farey_denominator {x : ℝ} {a b c d : ℕ}
    (hb : 0 < b) (hd : 0 < d) (hdet : b * c = a * d + 1)
    (hl : (a : ℝ) / b < x) (hr : x < (c : ℝ) / d)
    (u : ℤ) (q : ℕ) (hq : 0 < q) (hx : x = (u : ℝ) / q) : b + d ≤ q := by
  rw [hx, div_lt_div_iff₀ (by positivity) (by positivity)] at hl
  rw [hx, div_lt_div_iff₀ (by positivity) (by positivity)] at hr
  have h₁ : (a : ℤ) * q < u * b := by exact_mod_cast hl
  have h₂ : u * d < (c : ℤ) * q := by exact_mod_cast hr
  have h₃ : (b : ℤ) * c = a * d + 1 := by exact_mod_cast hdet
  have left : (1 : ℤ) ≤ u * b - a * q := by omega
  have right : (1 : ℤ) ≤ c * q - u * d := by omega
  have identity : (d : ℤ) * (u * b - a * q) + b * (c * q - u * d) = q := by
    linear_combination (q : ℤ) * h₃
  have hb' := mul_le_mul_of_nonneg_left right (show (0 : ℤ) ≤ b by positivity)
  have hd' := mul_le_mul_of_nonneg_left left (show (0 : ℤ) ≤ d by positivity)
  exact_mod_cast (show (b : ℤ) + d ≤ q by linarith)

/-- Apply a Farey interval to the enclosure of the prime series. -/
theorem denominator_certificate {n A a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c = a * d + 1)
    (hsum : (∑ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℝ) / 2 ^ i) =
      2 * (A : ℝ) / 2 ^ n)
    (hl : a * 2 ^ n < 2 * A * b)
    (hr : (2 * A + 34 * ((n + 2)^2 + 2 * (n + 2) + 3)) * d < c * 2 ^ n)
    (u : ℤ) (q : ℕ) (hq : 0 < q)
    (hx : (∑' i : ℕ, (Nat.nth Nat.Prime i : ℝ) / 2 ^ i) = (u : ℝ) / q) : b + d ≤ q := by
  obtain ⟨h₁, h₂⟩ := enclosure n
  dsimp only at h₁ h₂
  rw [hsum] at h₁ h₂
  apply farey_denominator hb hd hdet _ _ u q hq hx
  · apply lt_of_lt_of_le _ h₁
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast hl
  · apply lt_of_le_of_lt h₂
    rw [← add_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast hr

set_option maxRecDepth 8192 in
/-- Every positive denominator of the zero-indexed series exceeds 10^104. -/
theorem denominator_gt (u : ℤ) (q : ℕ) (hq : 0 < q)
    (hx : (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / 2 ^ n) = (u : ℝ) / q) :
    10 ^ 104 < q := by
  let a : ℕ := 1757236415597530362876219850458509132543397912654127452329658909700580713373479173028954852310611808483743
  let b : ℕ := 239102948727973837391014383175501022009980255188236697671730881837698029252847741536070165075330362268157
  let c : ℕ := 101708598157994592551614656036114145268256843318035975540935349317687510628545566507549782709731930665580
  let d : ℕ := 13839245257329649695052954391586737351389581750027543839377129534625755435180785354122657378660188371813
  have h := denominator_certificate (a := a) (b := b) (c := c) (d := d)
    (by decide) (by decide) (by decide +kernel) partial_sum_725
    (by decide +kernel) (by decide +kernel) u q hq hx
  exact lt_of_lt_of_le (by decide +kernel : 10 ^ 104 < b + d) h

/-- The same bound for Erdős's one-indexed normalization. -/
theorem classical_denominator_gt (u : ℤ) (q : ℕ) (hq : 0 < q)
    (hx : (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / 2 ^ (n + 1)) = (u : ℝ) / q) :
    10 ^ 104 < q := by
  apply denominator_gt (2 * u) q hq
  calc (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / 2 ^ n)
      = ∑' n : ℕ, 2 * ((Nat.nth Nat.Prime n : ℝ) / 2 ^ (n + 1)) := by
        apply tsum_congr
        intro n
        rw [pow_succ]
        ring
    _ = _ := by rw [tsum_mul_left, hx]; push_cast; ring

theorem exact_phase {x : ℝ} {u : ℤ} {q : ℕ} (hq : 0 < q)
    (hx : x = (u : ℝ) / q) {s t v : ℕ} {P E : ℝ}
    (lo : P ≤ x) (hi : x ≤ P + E)
    (hl : (q : ℝ) * v < q * t * 2 ^ s * P + 1)
    (hr : (q : ℝ) * t * 2 ^ s * (P + E) < q * v + 1) :
    (t : ℤ) * 2 ^ s * u = (q : ℤ) * v := by
  have hcoef : 0 ≤ (q : ℝ) * t * 2 ^ s := by positivity
  have hmul : (q : ℝ) * t * 2 ^ s * x = t * 2 ^ s * (u : ℝ) := by
    rw [hx]
    field_simp
  have lower := mul_le_mul_of_nonneg_left lo hcoef
  have upper := mul_le_mul_of_nonneg_left hi hcoef
  rw [hmul] at lower upper
  have hl' : (q : ℤ) * v < t * 2 ^ s * u + 1 := by
    exact_mod_cast (show (q : ℝ) * v < t * 2 ^ s * (u : ℝ) + 1 by linarith)
  have hr' : (t : ℤ) * 2 ^ s * u < q * v + 1 := by
    exact_mod_cast (show (t : ℝ) * 2 ^ s * (u : ℝ) < q * v + 1 by linarith)
  omega

theorem main : H1 → H2 → type_of% @Erdos251.erdos_251 := by
  intro h₀ h₁
  rintro ⟨r, heq⟩
  let x := ∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / 2 ^ n
  have hx : x = (r.num : ℝ) / r.den := by
    change (r : ℝ) = x at heq
    rw [← heq, Rat.cast_def]
  obtain ⟨n, s, z, hzlo, hzhi⟩ := h₀ r.den r.den_pos
  obtain ⟨m, j, y, hylo, hyhi⟩ := h₁ r.den r.den_pos
  have zero := exact_phase r.den_pos hx (s := s) (t := 1) (v := z)
    (enclosure n).1 (enclosure n).2 (by simpa using hzlo) (by simpa using hzhi)
  have third := exact_phase r.den_pos hx (s := j) (t := 3) (v := 3*y+1)
    (enclosure m).1 (enclosure m).2 (by simpa using hylo) (by simpa using hyhi)
  simp only [Int.natCast_one, one_mul] at zero
  push_cast at third
  have cancel : (r.den : ℤ) * (3 * 2 ^ j * z) =
      r.den * (2 ^ s * (3 * (y : ℤ) + 1)) := by
    linear_combination (2 : ℤ)^s * third - (3 * (2 : ℤ)^j) * zero
  have hd : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_nz
  have eq := mul_left_cancel₀ hd cancel
  have hdiv : (3 : ℤ) ∣ 2 ^ s * (3 * (y : ℤ) + 1) :=
    ⟨2 ^ j * z, by rw [← eq]; ring⟩
  have hprime : Prime (3 : ℤ) := by norm_num
  rcases hprime.dvd_mul.mp hdiv with h | h
  · have := hprime.dvd_of_dvd_pow h
    norm_num at this
  · omega

end OMA.R_Erdos251_erdos_251_R1
