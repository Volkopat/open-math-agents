import OMAStatements.S_oeis_a131576

-- Problem: A131576, the number of ways to write n as a sum of an even number of consecutive
-- positive integers. Pol's conjectures: a(n) = (A001227(n) - A067742(n))/2 = A082647(n) - A067742(n).
-- Upstream: statements/oeis-a131576.lean (declaration OMA.S_oeis_a131576.main)
--
-- Proof outline. Write n = 2^k * m with m odd. A representation (s, j) of n satisfies
-- j * (2s + j - 1) = 2n, and exactly one of the two factors is odd.
-- * Even j: (s, j) |-> 2s + j - 1 is a bijection onto Sgt, the odd divisors d of n with 2n < d^2.
-- * Odd j (the same as j | n): (s, j) |-> j is a bijection onto Slt, the odd divisors d with
--   d^2 < 2n. So a(n) = #Sgt, A082647(n) = #Slt, and A001227(n) = #Sgt + #Slt because d^2 = 2n
--   is impossible for odd d.
-- * d |-> m / d maps Sgt onto T = {e | m : 2^(k+1) e^2 < m}, which lies inside Slt. The rest W of
--   Slt maps onto the middle divisors by e |-> 2^i e, where i <= k is the largest index with
--   (2^i e)^2 < 2n. Hence #Slt = #Sgt + A067742(n), and both identities follow.

namespace OMA.P131576

open OMA.S_oeis_a131576

/-! ### Representations as sums of consecutive integers -/

lemma sum_formula (s j : ℕ) : (∑ i ∈ Finset.range j, (s + i)) * 2 + j = j * (2 * s + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    nlinarith [ih]

lemma sum_formula' (s j : ℕ) : (∑ i ∈ Finset.range j, (s + i)) * 2 = j * (2 * s + j - 1) := by
  have h := sum_formula s j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · obtain ⟨q, hq⟩ : ∃ q, 2 * s + j = q + 1 := ⟨2 * s + j - 1, by omega⟩
    rw [hq, Nat.add_sub_cancel]
    rw [hq, mul_add, mul_one] at h
    omega

/-- `(s, j)` represents `n` iff `s, j ≥ 1` and `j * (2 * s + j - 1) = 2 * n`. -/
lemma mem_reps {n s j : ℕ} :
    (s, j) ∈ reps n ↔ 1 ≤ s ∧ 1 ≤ j ∧ j * (2 * s + j - 1) = 2 * n := by
  unfold reps
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  have hf := sum_formula' s j
  constructor
  · rintro ⟨⟨⟨hs, -⟩, hj, -⟩, hsum⟩
    refine ⟨hs, hj, ?_⟩
    rw [← hf, hsum, mul_comm]
  · rintro ⟨hs, hj, h⟩
    generalize hq : 2 * s + j - 1 = q at hf h
    have hq2 : 2 ≤ q := by omega
    have hqs : 2 * s ≤ q := by omega
    have h1 : q ≤ j * q := Nat.le_mul_of_pos_left q hj
    have h2 : j * 2 ≤ j * q := Nat.mul_le_mul_left j hq2
    refine ⟨⟨⟨hs, by omega⟩, hj, by omega⟩, by omega⟩

/-! ### Odd divisors -/

lemma odd_dvd_of_dvd_two_mul {n k m d : ℕ} (hn : n = 2 ^ k * m) (hd : Odd d)
    (h : d ∣ 2 * n) : d ∣ m := by
  have h2 : 2 * n = 2 ^ (k + 1) * m := by rw [hn]; ring
  rw [h2] at h
  exact (Nat.Coprime.pow_right (k + 1) (Nat.coprime_two_right.mpr hd)).dvd_of_dvd_mul_left h

lemma div_facts {n k m d : ℕ} (hm : Odd m) (hn : n = 2 ^ k * m) (hdm : d ∣ m) :
    d % 2 = 1 ∧ 0 < d ∧ d * (2 * n / d) = 2 * n ∧ (2 * n / d) % 2 = 0 ∧ 0 < 2 * n / d := by
  have hm0 : 0 < m := hm.pos
  have hdn : d ∣ n := hdm.trans ⟨2 ^ k, by rw [hn]; ring⟩
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm hm0
  have hn0 : 0 < n := by rw [hn]; positivity
  have hdiv : 2 * n / d = 2 * (n / d) := Nat.mul_div_assoc 2 hdn
  have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn0 hdn) hdpos
  refine ⟨Nat.odd_iff.mp (hm.of_dvd_nat hdm), hdpos,
    Nat.mul_div_cancel' (Dvd.dvd.mul_left hdn 2), ?_, ?_⟩
  · rw [hdiv]; omega
  · rw [hdiv]; omega

/-- Odd divisors `d` of `n` (that is, divisors of the odd part `m`) with `2n < d²`. -/
def Sgt (n m : ℕ) : Finset ℕ := m.divisors.filter (fun d => 2 * n < d ^ 2)

/-- Odd divisors `d` of `n` with `d² < 2n`. -/
def Slt (n m : ℕ) : Finset ℕ := m.divisors.filter (fun d => d ^ 2 < 2 * n)

/-- The image of `Sgt` under `d ↦ m / d`. -/
def T (k m : ℕ) : Finset ℕ := m.divisors.filter (fun e => 2 * 2 ^ k * e ^ 2 < m)

/-- The rest of `Slt`. -/
def W (n k m : ℕ) : Finset ℕ := (Slt n m).filter (fun e => ¬ 2 * 2 ^ k * e ^ 2 < m)

/-- Middle divisors, with the square roots cleared. -/
def Mset (n : ℕ) : Finset ℕ := n.divisors.filter (fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n)

/-- Even-length representations correspond to `Sgt` via `(s, j) ↦ 2s + j - 1`. -/
theorem card_even {n k m : ℕ} (hm : Odd m) (hn : n = 2 ^ k * m) : a n = (Sgt n m).card := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  unfold a Sgt
  apply Finset.card_nbij' (fun p => 2 * p.1 + p.2 - 1)
    (fun d => ((d + 1 - 2 * n / d) / 2, 2 * n / d))
  · rintro ⟨s, j⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, mem_reps, Nat.even_iff] at hp
    obtain ⟨⟨hs, hj, h⟩, hev⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
    have hdodd : Odd (2 * s + j - 1) := Nat.odd_iff.mpr (by omega)
    refine ⟨⟨odd_dvd_of_dvd_two_mul hn hdodd ⟨j, by rw [← h]; ring⟩, hm0⟩, ?_⟩
    have hlt : j * (2 * s + j - 1) < (2 * s + j - 1) * (2 * s + j - 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    rw [pow_two, ← h]
    exact hlt
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdm, -⟩, hlt⟩ := hd
    obtain ⟨hd1, hdpos, hdj, hj2, hj1⟩ := div_facts hm hn hdm
    have hjd : 2 * n / d < d := by
      apply Nat.lt_of_mul_lt_mul_left (a := d)
      rw [hdj, ← pow_two]
      exact hlt
    simp only [Finset.mem_coe, Finset.mem_filter, mem_reps, Nat.even_iff]
    generalize 2 * n / d = j at *
    refine ⟨⟨by omega, hj1, ?_⟩, hj2⟩
    have : 2 * ((d + 1 - j) / 2) + j - 1 = d := by omega
    rw [this, mul_comm]
    exact hdj
  · rintro ⟨s, j⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, mem_reps, Nat.even_iff] at hp
    obtain ⟨⟨hs, hj, h⟩, hev⟩ := hp
    have hq : 2 * n / (2 * s + j - 1) = j := Nat.div_eq_of_eq_mul_left (by omega) h.symm
    simp only [hq, Prod.mk.injEq, and_true]
    omega
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdm, -⟩, hlt⟩ := hd
    obtain ⟨hd1, hdpos, hdj, hj2, hj1⟩ := div_facts hm hn hdm
    have hjd : 2 * n / d < d := by
      apply Nat.lt_of_mul_lt_mul_left (a := d)
      rw [hdj, ← pow_two]
      exact hlt
    show 2 * ((d + 1 - 2 * n / d) / 2) + 2 * n / d - 1 = d
    generalize 2 * n / d = j at *
    omega

/-- Representations whose length divides `n` correspond to `Slt` via `(s, j) ↦ j`. -/
theorem card_div {n k m : ℕ} (hm : Odd m) (hn : n = 2 ^ k * m) :
    A082647 n = (Slt n m).card := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hmn : m ∣ n := ⟨2 ^ k, by rw [hn]; ring⟩
  unfold A082647 Slt
  apply Finset.card_nbij' (fun p => p.2) (fun d => ((2 * n / d + 1 - d) / 2, d))
  · rintro ⟨s, j⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, mem_reps] at hp
    obtain ⟨⟨hs, hj, h⟩, r, hr⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
    have hq : 2 * s + j - 1 = 2 * r := by
      apply Nat.eq_of_mul_eq_mul_left (n := j) (by omega)
      rw [h, hr]
      ring
    have hjodd : Odd j := Nat.odd_iff.mpr (by omega)
    refine ⟨⟨odd_dvd_of_dvd_two_mul hn hjodd ⟨_, h.symm⟩, hm0⟩, ?_⟩
    have hlt : j * j < j * (2 * s + j - 1) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    rw [pow_two, ← h]
    exact hlt
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdm, -⟩, hlt⟩ := hd
    obtain ⟨hd1, hdpos, hdq, hq2, hq1⟩ := div_facts hm hn hdm
    have hdq' : d < 2 * n / d := by
      apply Nat.lt_of_mul_lt_mul_left (a := d)
      rw [hdq, ← pow_two]
      exact hlt
    simp only [Finset.mem_coe, Finset.mem_filter, mem_reps]
    refine ⟨⟨by omega, hdpos, ?_⟩, hdm.trans hmn⟩
    generalize 2 * n / d = q at *
    have : 2 * ((q + 1 - d) / 2) + d - 1 = q := by omega
    rw [this]
    exact hdq
  · rintro ⟨s, j⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, mem_reps] at hp
    obtain ⟨⟨hs, hj, h⟩, -⟩ := hp
    have hq : 2 * n / j = 2 * s + j - 1 := Nat.div_eq_of_eq_mul_right (by omega) h.symm
    simp only [hq, Prod.mk.injEq, and_true]
    omega
  · intro d _
    rfl

lemma odd_divisors {n k m : ℕ} (hm : Odd m) (hn : n = 2 ^ k * m) :
    n.divisors.filter Odd = m.divisors := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hn0 : n ≠ 0 := by rw [hn]; exact Nat.mul_ne_zero (by positivity) hm0
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hodd⟩
    refine ⟨?_, hm0⟩
    rw [hn] at hd
    exact (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_left hd
  · rintro ⟨hd, -⟩
    exact ⟨⟨hd.trans ⟨2 ^ k, by rw [hn]; ring⟩, hn0⟩, hm.of_dvd_nat hd⟩

/-- Every odd divisor lies in `Sgt` or `Slt`, since `d² = 2n` is impossible for odd `d`. -/
theorem card_odd {n k m : ℕ} (hm : Odd m) (hn : n = 2 ^ k * m) :
    A001227 n = (Sgt n m).card + (Slt n m).card := by
  have hfc : m.divisors.filter (fun d => ¬ 2 * n < d ^ 2) =
      m.divisors.filter (fun d => d ^ 2 < 2 * n) := by
    apply Finset.filter_congr
    intro d hd
    have h1 : d ^ 2 % 2 = 1 :=
      Nat.odd_iff.mp ((hm.of_dvd_nat (Nat.dvd_of_mem_divisors hd)).pow)
    omega
  unfold A001227 Sgt Slt
  rw [odd_divisors hm hn, ← Finset.card_filter_add_card_filter_not (s := m.divisors)
    (fun d => 2 * n < d ^ 2), hfc]

/-! ### The middle divisors -/

lemma swap_lt {m c d e : ℕ} (hde : d * e = m) (hm : 0 < m) : c * m < d ^ 2 ↔ c * e ^ 2 < m := by
  have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hde; omega)
  have h2 : d ^ 2 * e ^ 2 = m * m := by rw [← hde]; ring
  constructor
  · intro h
    have h1 : c * m * e ^ 2 < d ^ 2 * e ^ 2 := Nat.mul_lt_mul_of_pos_right h (by positivity)
    have h3 : c * e ^ 2 * m < m * m := by
      calc c * e ^ 2 * m = c * m * e ^ 2 := by ring
        _ < d ^ 2 * e ^ 2 := h1
        _ = m * m := h2
    exact Nat.lt_of_mul_lt_mul_right h3
  · intro h
    have h1 : c * e ^ 2 * m < m * m := Nat.mul_lt_mul_of_pos_right h hm
    have h3 : c * m * e ^ 2 < d ^ 2 * e ^ 2 := by
      calc c * m * e ^ 2 = c * e ^ 2 * m := by ring
        _ < m * m := h1
        _ = d ^ 2 * e ^ 2 := h2.symm
    exact Nat.lt_of_mul_lt_mul_right h3

/-- `d ↦ m / d` maps `Sgt` onto `T`. -/
theorem card_Sgt_T {n k m : ℕ} (hm : Odd m) (hn : n = 2 ^ k * m) :
    (Sgt n m).card = (T k m).card := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hmpos : 0 < m := hm.pos
  have h2n : 2 * n = 2 * 2 ^ k * m := by rw [hn]; ring
  unfold Sgt T
  apply Finset.card_nbij' (fun d => m / d) (fun e => m / e)
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    obtain ⟨⟨hdm, -⟩, hlt⟩ := hd
    refine ⟨⟨Nat.div_dvd_of_dvd hdm, hm0⟩, ?_⟩
    rw [h2n] at hlt
    exact (swap_lt (Nat.mul_div_cancel' hdm) hmpos).mp hlt
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at he ⊢
    obtain ⟨⟨hem, -⟩, hlt⟩ := he
    refine ⟨⟨Nat.div_dvd_of_dvd hem, hm0⟩, ?_⟩
    rw [h2n]
    exact (swap_lt (Nat.div_mul_cancel hem) hmpos).mpr hlt
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
    exact Nat.div_div_self hd.1.1 hm0
  · intro e he
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at he
    exact Nat.div_div_self he.1.1 hm0

/-- `Slt` splits into `T` and `W`. -/
theorem card_Slt_split {n k m : ℕ} (hn : n = 2 ^ k * m) :
    (Slt n m).card = (T k m).card + (W n k m).card := by
  have hfil : (Slt n m).filter (fun e => 2 * 2 ^ k * e ^ 2 < m) = T k m := by
    ext e
    simp only [Slt, T, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, h⟩
      exact ⟨hd, h⟩
    · rintro ⟨hd, h⟩
      refine ⟨⟨hd, ?_⟩, h⟩
      have h1 : e ^ 2 ≤ 2 * 2 ^ k * e ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
      have h2 : m ≤ 2 * 2 ^ k * m := Nat.le_mul_of_pos_left _ (by positivity)
      have h3 : 2 * n = 2 * 2 ^ k * m := by rw [hn]; ring
      omega
  rw [← hfil, W]
  exact (Finset.card_filter_add_card_filter_not (s := Slt n m) _).symm

lemma odd_part_unique {e e' : ℕ} (he : Odd e) (he' : Odd e') :
    ∀ i j : ℕ, 2 ^ i * e = 2 ^ j * e' → e = e' := by
  intro i
  induction i with
  | zero =>
    intro j h
    cases j with
    | zero => simpa using h
    | succ j =>
      exfalso
      rw [pow_zero, one_mul, pow_succ] at h
      exact (Nat.not_even_iff_odd.mpr he) ⟨2 ^ j * e', by rw [h]; ring⟩
  | succ i ih =>
    intro j h
    cases j with
    | zero =>
      exfalso
      rw [pow_zero, one_mul, pow_succ] at h
      exact (Nat.not_even_iff_odd.mpr he') ⟨2 ^ i * e, by rw [← h]; ring⟩
    | succ j =>
      apply ih j
      rw [pow_succ, pow_succ] at h
      have h' : 2 * (2 ^ i * e) = 2 * (2 ^ j * e') := by
        calc 2 * (2 ^ i * e) = 2 ^ i * 2 * e := by ring
          _ = 2 ^ j * 2 * e' := h
          _ = 2 * (2 ^ j * e') := by ring
      omega

lemma decomp {d k m : ℕ} (hd : d ∣ 2 ^ k * m) : ∃ i ≤ k, ∃ e, e ∣ m ∧ d = 2 ^ i * e := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp hd
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  exact ⟨i, hi, z, hz, rfl⟩

/-- `e ↦ 2^i * e`, with the unique `i ≤ k` putting `2 (2^i e)²` in `[n, 4n)`, maps `W` onto the
middle divisors. -/
theorem card_W {n k m : ℕ} (hm : Odd m) (hn : n = 2 ^ k * m) :
    (W n k m).card = (Mset n).card := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  apply Finset.card_bij
    (fun e _ => 2 ^ Nat.findGreatest (fun i => (2 ^ i * e) ^ 2 < 2 * n) k * e)
  · intro e he
    simp only [W, Slt, Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨⟨hem, -⟩, hlt⟩, hge⟩ := he
    have hge' := Nat.not_lt.mp hge
    have hP0 : (2 ^ 0 * e) ^ 2 < 2 * n := by simpa using hlt
    have hPi := Nat.findGreatest_spec (P := fun i => (2 ^ i * e) ^ 2 < 2 * n) (Nat.zero_le k) hP0
    have hik := Nat.findGreatest_le (P := fun i => (2 ^ i * e) ^ 2 < 2 * n) k
    set i := Nat.findGreatest (fun i => (2 ^ i * e) ^ 2 < 2 * n) k with hi
    simp only [Mset, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, by rw [hn]; exact Nat.mul_ne_zero (by positivity) hm0⟩, ?_, hPi⟩
    · rw [hn]
      exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 hik) hem
    · rcases Nat.lt_or_ge i k with hik' | hik'
      · have hlt1 : i < i + 1 := by omega
        have hle1 : i + 1 ≤ k := by omega
        have hnot : ¬ (2 ^ (i + 1) * e) ^ 2 < 2 * n :=
          Nat.findGreatest_is_greatest (P := fun i => (2 ^ i * e) ^ 2 < 2 * n) hlt1 hle1
        have h4 : (2 ^ (i + 1) * e) ^ 2 = 4 * (2 ^ i * e) ^ 2 := by ring
        omega
      · have hik'' : i = k := le_antisymm hik hik'
        rw [hik'', hn]
        calc 2 ^ k * m ≤ 2 ^ k * (2 * 2 ^ k * e ^ 2) := Nat.mul_le_mul_left _ hge'
          _ = 2 * (2 ^ k * e) ^ 2 := by ring
  · intro e₁ he₁ e₂ he₂ heq
    simp only [W, Slt, Finset.mem_filter, Nat.mem_divisors] at he₁ he₂
    exact odd_part_unique (hm.of_dvd_nat he₁.1.1.1) (hm.of_dvd_nat he₂.1.1.1) _ _ heq
  · intro d hd
    simp only [Mset, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdn, -⟩, hle, hlt⟩ := hd
    rw [hn] at hdn
    obtain ⟨i, hik, e, hem, rfl⟩ := decomp hdn
    have h1 : e ^ 2 ≤ (2 ^ i * e) ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_left e (by positivity)) 2
    have hfg : Nat.findGreatest (fun i => (2 ^ i * e) ^ 2 < 2 * n) k = i := by
      rw [Nat.findGreatest_eq_iff]
      refine ⟨hik, fun _ => hlt, ?_⟩
      intro j hij hjk hPj
      have h4 : (2 ^ (i + 1) * e) ^ 2 ≤ (2 ^ j * e) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right e (Nat.pow_le_pow_right (by norm_num) hij)) 2
      have h5 : (2 ^ (i + 1) * e) ^ 2 = 4 * (2 ^ i * e) ^ 2 := by ring
      omega
    refine ⟨e, ?_, ?_⟩
    · simp only [W, Slt, Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨⟨hem, hm0⟩, by omega⟩, Nat.not_lt.mpr ?_⟩
      have h2 : (2 ^ i * e) ^ 2 ≤ (2 ^ k * e) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right e (Nat.pow_le_pow_right (by norm_num) hik)) 2
      have h3 : 2 ^ k * m ≤ 2 ^ k * (2 * 2 ^ k * e ^ 2) := by
        calc 2 ^ k * m = n := hn.symm
          _ ≤ 2 * (2 ^ i * e) ^ 2 := hle
          _ ≤ 2 * (2 ^ k * e) ^ 2 := Nat.mul_le_mul_left 2 h2
          _ = 2 ^ k * (2 * 2 ^ k * e ^ 2) := by ring
      exact Nat.le_of_mul_le_mul_left h3 (by positivity)
    · show 2 ^ Nat.findGreatest (fun i => (2 ^ i * e) ^ 2 < 2 * n) k * e = 2 ^ i * e
      rw [hfg]

lemma real_cond (n d : ℕ) :
    (Real.sqrt ((n : ℝ) / 2) ≤ (d : ℝ) ∧ (d : ℝ) < Real.sqrt ((n : ℝ) * 2)) ↔
      (n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n) := by
  rw [Real.sqrt_le_left (Nat.cast_nonneg d), Real.lt_sqrt (Nat.cast_nonneg d)]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have h : (n : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by linarith
      exact_mod_cast h
    · have h : (d : ℝ) ^ 2 < 2 * (n : ℝ) := by linarith
      exact_mod_cast h
  · rintro ⟨h1, h2⟩
    have h1' : (n : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by exact_mod_cast h1
    have h2' : (d : ℝ) ^ 2 < 2 * (n : ℝ) := by exact_mod_cast h2
    constructor <;> linarith

lemma A067742_eq (n : ℕ) : A067742 n = (Mset n).card := by
  unfold A067742 Mset
  congr 1
  ext d
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ => real_cond n d)

theorem card_middle {n k m : ℕ} (hm : Odd m) (hn : n = 2 ^ k * m) :
    (Slt n m).card = (Sgt n m).card + A067742 n := by
  rw [card_Slt_split hn, card_Sgt_T hm hn, card_W hm hn, A067742_eq]

/-! ### Assembly -/

theorem main_proof : ∀ n : ℕ, 1 ≤ n →
    a n = (A001227 n - A067742 n) / 2 ∧ a n = A082647 n - A067742 n := by
  intro n hn
  obtain ⟨k, m, hm, hnkm⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have h1 := card_even hm hnkm
  have h2 := card_div hm hnkm
  have h3 := card_odd hm hnkm
  have h4 := card_middle hm hnkm
  constructor <;> omega

end OMA.P131576

theorem OMA.solution : type_of% @OMA.S_oeis_a131576.main := OMA.P131576.main_proof
