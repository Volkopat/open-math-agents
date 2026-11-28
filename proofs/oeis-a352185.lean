import OMAStatements.S_oeis_a352185

/-! A bit-packed sieve certifies the finite search for Branicky's counterexample. -/

open OMA.S_oeis_a352185

/-- The first `len` bits spaced `d` positions apart, starting at zero. -/
private def stride (d len : ℕ) : ℕ := ((2 ^ d) ^ len - 1) / (2 ^ d - 1)

private theorem stride_sum {d : ℕ} (hd : 0 < d) (len : ℕ) :
    stride d len = ∑ j ∈ Finset.range len, (2 ^ d) ^ j := by
  unfold stride
  rw [← geom_sum_mul_of_one_le (Nat.one_le_two_pow (n := d)) len,
    Nat.mul_div_cancel _ (by have := Nat.one_lt_two_pow (n := d) (by omega); omega)]

private theorem stride_succ {d : ℕ} (hd : 0 < d) (len : ℕ) :
    stride d (len + 1) = 2 ^ d * stride d len + 1 := by
  rw [stride_sum hd, stride_sum hd, Finset.sum_range_succ']
  simp [pow_succ', Finset.mul_sum]

private theorem stride_bit {d : ℕ} (hd : 0 < d) (len i : ℕ) :
    (stride d len).testBit i = true ↔ d ∣ i ∧ i / d < len := by
  induction len generalizing i with
  | zero => simp [stride]
  | succ len ih =>
      rw [stride_succ hd, Nat.testBit_two_pow_mul_add _ (Nat.one_lt_two_pow hd.ne')]
      by_cases h : i < d
      · rw [if_pos h, show (1 : ℕ).testBit i = (2 ^ 0 : ℕ).testBit i by rfl,
          Nat.testBit_two_pow]
        simp only [decide_eq_true_eq, Nat.div_eq_of_lt h, Nat.zero_lt_succ, and_true]
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt h]
        exact eq_comm
      · rw [if_neg h, ih]
        have hi : (i - d) + d = i := Nat.sub_add_cancel (by omega)
        have hm : (i - d) % d = i % d := by
          calc
            (i - d) % d = ((i - d) + d) % d := by simp
            _ = i % d := by rw [hi]
        have hq : (i - d) / d + 1 = i / d := by
          calc
            (i - d) / d + 1 = ((i - d) + d) / d := (Nat.add_div_right _ hd).symm
            _ = i / d := by rw [hi]
        simp only [Nat.dvd_iff_mod_eq_zero, hm]
        omega

/-- A mask for multiples of `d` from `2*d` up to the sieve limit. -/
private def properMultiples (N d : ℕ) : ℕ := stride d (N / d - 1) <<< (2 * d)

private theorem properMultiples_bit {N d n : ℕ} (hd : 0 < d) (hN : n ≤ N) :
    (properMultiples N d).testBit n = true ↔ 2 * d ≤ n ∧ d ∣ n := by
  unfold properMultiples
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, stride_bit hd]
  by_cases h : 2 * d ≤ n
  · have hs := Nat.sub_add_cancel h
    have hdv : d ∣ (2 * d) := dvd_mul_left _ _
    have he : d ∣ (n - 2 * d) ↔ d ∣ n := by
      constructor
      · intro h
        exact hs ▸ Nat.dvd_add h hdv
      · intro h
        exact Nat.dvd_sub h hdv
    have hq : (n - 2 * d) / d + 2 = n / d := by
      calc
        (n - 2 * d) / d + 2 = ((n - 2 * d) + 2 * d) / d := by
          rw [mul_comm 2 d, Nat.add_mul_div_left _ _ hd]
        _ = n / d := by rw [hs]
    have hbound := Nat.div_le_div_right (c := d) hN
    simp [h, he, show (n - 2 * d) / d < N / d - 1 by omega]
  · simp [h]

private theorem union_bit (l : List ℕ) (mask : ℕ → ℕ) (i : ℕ) :
    (l.foldr (fun d s => mask d ||| s) 0).testBit i = true ↔
      ∃ d ∈ l, (mask d).testBit i = true := by
  induction l with
  | nil => simp
  | cons d l ih => simp [Bool.or_eq_true, ih]

private def composites (N : ℕ) : ℕ :=
  (List.range' 2 (N.sqrt - 1)).foldr (fun d m => properMultiples N d ||| m) 0

private theorem composite_bit {n N : ℕ} (hn : 2 ≤ n) (hN : n ≤ N) :
    (composites N).testBit n = true ↔ ¬ n.Prime := by
  rw [composites, union_bit]
  constructor
  · rintro ⟨d, hd, hb⟩ hp
    have hd2 : 2 ≤ d := (List.mem_range'_1.mp hd).1
    obtain ⟨hlt, hdvd⟩ := (properMultiples_bit (by omega) hN).mp hb
    have he := (Nat.dvd_prime_two_le hp hd2).mp hdvd
    omega
  · intro hp
    let d := n.minFac
    have hd : d.Prime := Nat.minFac_prime (by omega : n ≠ 1)
    have hsq : d * d ≤ n := by
      simpa [d, pow_two] using Nat.minFac_sq_le_self (by omega : 0 < n) hp
    have hds : d ≤ N.sqrt := Nat.le_sqrt.mpr (hsq.trans hN)
    have hdn : d ∣ n := Nat.minFac_dvd n
    have hlt : 2 * d ≤ n := by
      obtain ⟨q, hq⟩ := hdn
      have hq2 : 2 ≤ q := by
        by_contra! hq2
        interval_cases q
        · simp at hq; omega
        · simp at hq; exact hp (hq ▸ hd)
      rw [hq, mul_comm 2]
      exact Nat.mul_le_mul_left _ hq2
    exact ⟨d, List.mem_range'_1.mpr (by have := hd.two_le; omega),
      (properMultiples_bit hd.pos hN).mpr ⟨hlt, hdn⟩⟩

/-- Bit `n` is set precisely when `n` is prime and at most `N`. -/
private def sieve (N : ℕ) : ℕ :=
  (((2 ^ (N - 1) - 1) <<< 2) &&& ((2 ^ (N + 1) - 1) ^^^ composites N))

private theorem sieve_bit {N n : ℕ} (hN : n ≤ N) :
    (sieve N).testBit n = true ↔ n.Prime := by
  by_cases hn : 2 ≤ n
  · have cb := composite_bit hn hN
    by_cases hp : n.Prime
    · have hb : (composites N).testBit n = false := by
        cases he : (composites N).testBit n <;> simp_all
      simp [sieve, hn, show n - 2 < N - 1 by omega, show n < N + 1 by omega, hb, hp]
    · have hb := cb.mpr hp
      simp [sieve, hn, show n - 2 < N - 1 by omega, show n < N + 1 by omega, hb, hp]
  · simp [sieve, hn, show ¬ n.Prime from fun hp => hn hp.two_le]

private def table : ℕ := sieve (136 * 8207)

private def row (bits p i : ℕ) : ℕ := (bits >>> (i * p)) % 2 ^ p

/-- The union of the 135 rows marks residues which encounter a prime. -/
private def coveredResidues (bits p : ℕ) : ℕ :=
  (List.range' 1 135).foldr (fun i mask => row bits p i ||| mask) 0

private def verifiedSteps (lo count : ℕ) : Bool :=
  (List.range' lo count).all (fun p => !table.testBit p ||
    decide (coveredResidues table p = 2 ^ p - 1))

private theorem witness_hits {p k : ℕ} (hp : p ≤ 8207) (hk : k < p)
    (hc : coveredResidues table p = 2 ^ p - 1) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ 135 ∧ (i * p + k).Prime := by
  have bit : (coveredResidues table p).testBit k = true := by simp [hc, hk]
  rw [coveredResidues, union_bit] at bit
  obtain ⟨i, hi, hb⟩ := bit
  have hi' := List.mem_range'_1.mp hi
  have hN : i * p + k ≤ 136 * 8207 := by
    have hm := Nat.mul_le_mul (show i ≤ 135 by omega) hp
    omega
  exact ⟨i, hi'.1, by omega, sieve_bit hN |>.mp (by simpa [row, hk, table] using hb)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem verifiedBlocks (b : Fin 33) :
    verifiedSteps (b.val * 256) (min 256 (8207 - b.val * 256)) = true := by
  fin_cases b <;> decide +kernel

private theorem prime_step_hits {p k : ℕ} (hp : p.Prime) (hp' : p < 8207) (hk : k < p) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ 135 ∧ (i * p + k).Prime := by
  let b : Fin 33 := ⟨p / 256, by omega⟩
  have hm : p ∈ List.range' (b.val * 256) (min 256 (8207 - b.val * 256)) :=
    List.mem_range'_1.mpr (by dsimp [b]; omega)
  have hb := List.all_eq_true.mp (verifiedBlocks b) p hm
  have ht : table.testBit p = true := sieve_bit (by omega : p ≤ 136 * 8207) |>.mpr hp
  exact witness_hits hp'.le hk (by simpa only [ht, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem compositeProgression :
    (List.range' 1 135).all (fun i => !table.testBit (i * 8207 + 3251)) = true := by
  decide +kernel

private theorem admissible : Admissible 135 8207 := by
  refine ⟨3251, by decide, by decide, by decide, ?_⟩
  intro i hi hlo hp
  have hb := List.all_eq_true.mp compositeProgression i (List.mem_range'_1.mpr (by omega))
  have hd : table.testBit (i * 8207 + 3251) = true :=
    (sieve_bit (by omega : i * 8207 + 3251 ≤ 136 * 8207)).mpr hp
  simp [hd] at hb

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a352185.main) := by
  intro h
  let S : Set ℕ := {m | Admissible 135 m}
  let p := sInf S
  have hm : p ∈ S := Nat.sInf_mem ⟨8207, admissible⟩
  have hu : p ≤ 8207 := Nat.sInf_le admissible
  have hmin : IsLeast S p := ⟨hm, fun _ hx => Nat.sInf_le hx⟩
  have hp : p.Prime := h 135 (by decide) p hmin
  have hcomp : ¬ (8207 : ℕ).Prime := by norm_num
  have hlt : p < 8207 := lt_of_le_of_ne hu (fun he => hcomp (he ▸ hp))
  obtain ⟨k, _, hk, _, hnone⟩ := hm
  obtain ⟨i, hi, hi', hprime⟩ := prime_step_hits hp hlt hk
  exact hnone i hi hi' hprime
