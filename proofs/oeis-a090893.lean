import OMAStatements.S_oeis_a090893

/-!
For x ≥ 2 the floor equation tests whether the fractional part of x/√3
lies in [0, 1/3). Powers of 2 − √3 produce arbitrarily accurate returns
with an index shift prime to 3. If the integer counting discrepancy were
bounded, we could repeat a finite block containing both its global minimum
and its global maximum. Its displacement would have to be zero, although
it is nonzero modulo 3.
-/

namespace FloorDiscrepancy

open Real OMA.S_oeis_a090893

private theorem floor_test (t : ℝ) (ht : 1 ≤ t) :
    ⌊3 * t * ⌊t⌋⌋ = ⌊t * ⌊3 * t⌋⌋ ↔ ⌊3 * t⌋ = 3 * ⌊t⌋ := by
  have hle : 3 * ⌊t⌋ ≤ ⌊3 * t⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith [Int.floor_le t]
  constructor
  · intro he
    by_contra hne
    have hi : 3 * ⌊t⌋ + 1 ≤ ⌊3 * t⌋ := by omega
    have hr : 3 * (⌊t⌋ : ℝ) + 1 ≤ (⌊3 * t⌋ : ℝ) := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ t)
    have hx : 3 * t * (⌊t⌋ : ℝ) + 1 ≤ t * (⌊3 * t⌋ : ℝ) := by nlinarith
    have hy := Int.floor_le_floor hx
    rw [Int.floor_add_one] at hy
    omega
  · intro h
    rw [h]
    push_cast
    ring_nf

private theorem criterion (n : ℕ) (hn : 2 ≤ n) :
    P n ↔ ⌊3 * ((n : ℝ) / √3)⌋ = 3 * ⌊(n : ℝ) / √3⌋ := by
  have hs : 0 < √(3 : ℝ) := by positivity
  have hs₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have he : (n : ℝ) * √3 = 3 * ((n : ℝ) / √3) := by
    rw [← mul_div_assoc, eq_div_iff hs.ne', mul_assoc, ← sq, hs₂, mul_comm]
  unfold P
  rw [he]
  apply floor_test
  apply (le_div_iff₀ hs).2
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

private def pell : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 => let (u, v) := pell n; (2 * u + 3 * v, u + 2 * v)

private theorem pell_mod (n : ℕ) : (pell n).1 % 3 ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih => simp only [pell]; omega

private theorem pell_error (n : ℕ) :
    ((pell n).1 : ℝ) - √3 * (pell n).2 = (2 - √3) ^ n := by
  induction n with
  | zero => norm_num [pell]
  | succ n ih =>
    simp only [pell, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ, ← ih]
    linear_combination -((pell n).2 : ℝ) * Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

private theorem near_return (ε : ℝ) (he : 0 < ε) :
    ∃ q b : ℕ, q % 3 ≠ 0 ∧ 0 ≤ (q : ℝ) / √3 - b ∧ (q : ℝ) / √3 - b < ε := by
  have hs : 0 < √(3 : ℝ) := by positivity
  have hs₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hpos : 0 < 2 - √(3 : ℝ) := by nlinarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos he hs) (show 2 - √(3 : ℝ) < 1 by nlinarith)
  refine ⟨(pell n).1, (pell n).2, pell_mod n, ?_, ?_⟩
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hs).2
    linarith [pell_error n, pow_nonneg hpos.le n]
  · apply sub_lt_iff_lt_add.mpr
    apply (div_lt_iff₀ hs).2
    nlinarith [pell_error n]

private theorem stable_floor (x : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ < ε →
    ⌊x + δ⌋ = ⌊x⌋ ∧ ⌊3 * (x + δ)⌋ = ⌊3 * x⌋ := by
  let u : ℝ := (⌊x⌋ : ℝ) + 1 - x
  let v : ℝ := ((⌊3 * x⌋ : ℝ) + 1 - 3 * x) / 3
  have hu : 0 < u := by dsimp [u]; linarith [Int.lt_floor_add_one x]
  have hv : 0 < v := by dsimp [v]; linarith [Int.lt_floor_add_one (3 * x)]
  refine ⟨min u v, lt_min hu hv, ?_⟩
  intro δ hδ he
  have h₁ := he.trans_le (min_le_left u v)
  have h₂ := he.trans_le (min_le_right u v)
  dsimp [u, v] at h₁ h₂
  constructor
  · exact Int.floor_eq_iff.mpr ⟨by linarith [Int.floor_le x], by linarith⟩
  · exact Int.floor_eq_iff.mpr ⟨by linarith [Int.floor_le (3 * x)], by linarith⟩

private theorem stable_block (N : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i ≤ N, ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      ⌊(i : ℝ) / √3 + δ⌋ = ⌊(i : ℝ) / √3⌋ ∧
      ⌊3 * ((i : ℝ) / √3 + δ)⌋ = ⌊3 * ((i : ℝ) / √3)⌋ := by
  induction N with
  | zero =>
    obtain ⟨ε, he, h⟩ := stable_floor ((0 : ℝ) / √3)
    refine ⟨ε, he, ?_⟩
    intro i hi
    obtain rfl : i = 0 := by omega
    simpa using h
  | succ N ih =>
    obtain ⟨ε, he, h⟩ := ih
    obtain ⟨η, hη, h'⟩ := stable_floor (((N + 1 : ℕ) : ℝ) / √3)
    refine ⟨min ε η, lt_min he hη, ?_⟩
    intro i hi δ hδ hsmall
    rcases show i ≤ N ∨ i = N + 1 by omega with hle | rfl
    · exact h i hle δ hδ (hsmall.trans_le (min_le_left _ _))
    · exact h' δ hδ (hsmall.trans_le (min_le_right _ _))

private theorem repeat_block (N : ℕ) :
    ∃ q : ℕ, q % 3 ≠ 0 ∧ ∀ i, 2 ≤ i → i ≤ N → (P (q + i) ↔ P i) := by
  obtain ⟨ε, he, h⟩ := stable_block N
  obtain ⟨q, b, hq, hδ, hsmall⟩ := near_return ε he
  refine ⟨q, hq, ?_⟩
  intro i h₂ hN
  let x : ℝ := (i : ℝ) / √3
  let δ : ℝ := (q : ℝ) / √3 - b
  obtain ⟨h₁, h₃⟩ := h i hN δ hδ hsmall
  change ⌊x + δ⌋ = ⌊x⌋ at h₁
  change ⌊3 * (x + δ)⌋ = ⌊3 * x⌋ at h₃
  have hsum : ((q + i : ℕ) : ℝ) / √3 = (x + δ) + (b : ℤ) := by
    push_cast
    dsimp [x, δ]
    ring
  have hthree : 3 * (x + δ + (b : ℤ)) = 3 * (x + δ) + ((3 * (b : ℤ) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [criterion _ (by omega), criterion _ h₂, hsum]
  change (⌊3 * (x + δ + (b : ℤ))⌋ = 3 * ⌊x + δ + (b : ℤ)⌋) ↔ ⌊3 * x⌋ = 3 * ⌊x⌋
  rw [hthree, Int.floor_add_intCast, Int.floor_add_intCast, h₁, h₃]
  omega

noncomputable local instance : DecidablePred P := Classical.decPred _

private noncomputable def discrepancy (n : ℕ) : ℤ :=
  3 * (Nat.count P (n + 2) : ℤ) - n

private theorem discrepancy_step (n : ℕ) :
    discrepancy (n + 1) - discrepancy n = 3 * (if P (n + 2) then 1 else 0) - 1 := by
  unfold discrepancy
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.count_succ (p := P) (n + 2)]
  split_ifs <;> push_cast <;> ring

private theorem discrepancy_unbounded :
    ¬ (BddBelow (Set.range discrepancy) ∧ BddAbove (Set.range discrepancy)) := by
  rintro ⟨hlo, hhi⟩
  obtain ⟨a, ha⟩ := Int.csInf_mem (Set.range_nonempty discrepancy) hlo
  obtain ⟨b, hb⟩ := Int.csSup_mem (Set.range_nonempty discrepancy) hhi
  let N := max a b
  obtain ⟨q, hq, hblock⟩ := repeat_block (N + 2)
  have shift (i : ℕ) (hi : i ≤ N) :
      discrepancy (q + i) - discrepancy i = discrepancy q - discrepancy 0 := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hp := hblock (i + 2) (by omega) (by omega)
      have h₁ := discrepancy_step i
      have h₂ := discrepancy_step (q + i)
      rw [show q + i + 2 = q + (i + 2) by omega, if_congr hp rfl rfl] at h₂
      have hprev := ih (by omega)
      rw [show q + (i + 1) = q + i + 1 by omega]
      omega
  have hmin := csInf_le hlo (Set.mem_range_self (q + a))
  have hmax := le_csSup hhi (Set.mem_range_self (q + b))
  rw [← ha] at hmin
  rw [← hb] at hmax
  have h₁ := shift a (le_max_left _ _)
  have h₂ := shift b (le_max_right _ _)
  have heq : discrepancy q = discrepancy 0 := by omega
  unfold discrepancy at heq
  push_cast at heq
  omega

theorem disprove : ¬ (type_of% @OMA.S_oeis_a090893.main) := by
  rintro ⟨C, hC⟩
  obtain ⟨K, hK⟩ := exists_nat_gt C
  have estimates (i : ℕ) : 3 * i ≤ Nat.nth P i + K ∧ Nat.nth P i ≤ 3 * i + K := by
    have hc := abs_le.mp (hC i)
    constructor
    · exact_mod_cast (show (3 : ℝ) * i ≤ (Nat.nth P i : ℝ) + K by linarith)
    · exact_mod_cast (show (Nat.nth P i : ℝ) ≤ 3 * i + K by linarith)
  have hinf : (Set.ofPred P).Infinite := by
    intro hf
    let j := hf.toFinset.card + K + 1
    have hzero := Nat.nth_of_card_le hf (show hf.toFinset.card ≤ j by dsimp [j]; omega)
    have h := (estimates j).1
    rw [hzero] at h
    dsimp [j] at h
    omega
  have bounds (i : ℕ) : -(K : ℤ) ≤ discrepancy i ∧ discrepancy i ≤ (K : ℤ) + 5 := by
    let j := Nat.count P (i + 2)
    have hn : i + 2 ≤ Nat.nth P j := Nat.le_nth_count hinf (i + 2)
    have hh := (estimates j).2
    change -(K : ℤ) ≤ 3 * (j : ℤ) - i ∧ 3 * (j : ℤ) - i ≤ (K : ℤ) + 5
    by_cases hz : j = 0
    · omega
    · have hlt := Nat.nth_lt_of_lt_count (p := P) (n := i + 2)
          (show j - 1 < j by omega)
      have hl := (estimates (j - 1)).1
      omega
  apply discrepancy_unbounded
  constructor
  · refine ⟨-(K : ℤ), ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (bounds i).1
  · refine ⟨(K : ℤ) + 5, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (bounds i).2

end FloorDiscrepancy

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a090893.main) :=
  FloorDiscrepancy.disprove
