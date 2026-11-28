import OMAStatements.S_oeis_a035513
import Mathlib

-- Problem: oeis-a035513 (Kimberling: (T(n,1), T(n,2)) mod m takes all m^2 values)
-- Credit: @Aijy0264561
-- T n 1 = A + (n - 1) and T n 2 = 2A + (n - 1) with A = floor(n phi), an invertible change of
-- coordinates mod m, so it suffices that (n - 1, floor(n phi)) mod m hits every pair. Take
-- n = r + 1 + m t: by Dirichlet approximation some k phi is within 1/(m+1) of an integer, and
-- walking along multiples of k puts frac((r+1) phi / m + t phi) in any interval of length 1/m.

open Finset

namespace OMA.A035513proof

open OMA.S_oeis_a035513

/-- Some `c + t ξ` (`t : ℕ`) lands in `[q + s/m, q + (s+1)/m)` for an integer `q`. -/
lemma hit {ξ : ℝ} (hξ : Irrational ξ) (c : ℝ) {m s : ℕ} (hm : 0 < m) :
    ∃ t : ℕ, ∃ q : ℤ, (q : ℝ) + s / m ≤ c + t * ξ ∧ c + t * ξ < q + (s + 1) / m := by
  obtain ⟨j, k, hk, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le ξ hm
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  set δ : ℝ := (k : ℝ) * ξ - j with hδ
  have hδ0 : δ ≠ 0 := by
    intro h
    apply hξ
    refine ⟨(j : ℚ) / k, ?_⟩
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast
    field_simp
    linarith
  have hsmall : |δ| < 1 / m := by
    refine lt_of_le_of_lt hjk ?_
    apply one_div_lt_one_div_of_lt hmr; linarith
  have hk0 : (0 : ℤ) ≤ k := hk.le
  -- c + i * k * ξ = c + i * δ + i * j
  have shift : ∀ i : ℕ, c + ((i * k.toNat : ℕ) : ℝ) * ξ = c + i * δ + ((i * j : ℤ) : ℝ) := by
    intro i
    have : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0
    push_cast [this]
    rw [hδ]; ring
  rcases lt_or_gt_of_ne hδ0 with hneg | hpos
  · -- δ < 0: walk down from c
    set T : ℝ := (⌊c - (s + 1) / m⌋ : ℝ) + (s + 1) / m with hT
    have hTc : T ≤ c := by
      have := Int.floor_le (c - (s + 1) / m); rw [hT]; linarith
    set i : ℕ := ⌊(c - T) / (-δ)⌋₊ + 1 with hi
    have hpos' : 0 < -δ := by linarith
    have h1 : (c - T) / (-δ) < i := by rw [hi]; push_cast; exact Nat.lt_floor_add_one _
    have h2 : ((i : ℝ) - 1) ≤ (c - T) / (-δ) := by
      rw [hi]; push_cast; simp only [add_sub_cancel_right]
      exact Nat.floor_le (div_nonneg (by linarith) hpos'.le)
    rw [div_lt_iff₀ hpos'] at h1
    rw [le_div_iff₀ hpos'] at h2
    rw [abs_of_neg hneg] at hsmall
    refine ⟨i * k.toNat, ⌊c - (s + 1) / m⌋ + i * j, ?_, ?_⟩
    · rw [shift]; push_cast
      have : T - (s + 1) / m + s / m ≤ c + i * δ := by
        have e : (s + 1 : ℝ) / m = s / m + 1 / m := by ring
        rw [e] at hT ⊢
        nlinarith
      rw [hT] at this; linarith
    · rw [shift]; push_cast
      have : c + i * δ < T := by nlinarith
      rw [hT] at this; linarith
  · -- δ > 0: walk up from c
    set B : ℝ := (⌈c - s / m⌉ : ℝ) + s / m with hB
    have hBc : c ≤ B := by
      have := Int.le_ceil (c - s / m); rw [hB]; linarith
    set i : ℕ := ⌈(B - c) / δ⌉₊ with hi
    have h1 : (B - c) / δ ≤ i := Nat.le_ceil _
    have h2 : (i : ℝ) < (B - c) / δ + 1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) hpos.le)
    rw [div_le_iff₀ hpos] at h1
    have h2' : (i : ℝ) * δ < B - c + δ := by
      have := mul_lt_mul_of_pos_right h2 hpos
      rw [add_mul, div_mul_cancel₀ _ hpos.ne', one_mul] at this
      exact this
    rw [abs_of_pos hpos] at hsmall
    refine ⟨i * k.toNat, ⌈c - s / m⌉ + i * j, ?_, ?_⟩
    · rw [shift]; push_cast
      rw [hB] at h1; linarith
    · rw [shift]; push_cast
      have e : (s + 1 : ℝ) / m = s / m + 1 / m := by ring
      rw [e]; rw [hB] at h2'; linarith

/-- For every pair of residues `(r, s)` mod `m` there is a row `n ≥ 1` with
`n - 1 ≡ r` and `⌊nφ⌋ ≡ s`. -/
lemma exists_row {m r s : ℕ} (hm : 0 < m) (hr : r < m) (hs : s < m) :
    ∃ n : ℕ, 1 ≤ n ∧ (n - 1) % m = r ∧ ⌊(n : ℝ) * Real.goldenRatio⌋₊ % m = s := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨t, q, h1, h2⟩ := hit Real.goldenRatio_irrational ((r + 1 : ℝ) * Real.goldenRatio / m)
    (s := s) hm
  refine ⟨r + 1 + m * t, by omega, ?_, ?_⟩
  · rw [show r + 1 + m * t - 1 = r + m * t by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hr]
  · have hn : ((r + 1 + m * t : ℕ) : ℝ) * Real.goldenRatio =
        m * ((r + 1 : ℝ) * Real.goldenRatio / m + t * Real.goldenRatio) := by
      push_cast; field_simp
    have lo : (m : ℝ) * q + s ≤ ((r + 1 + m * t : ℕ) : ℝ) * Real.goldenRatio := by
      rw [hn]
      have := mul_le_mul_of_nonneg_left h1 hmr.le
      rw [mul_add, mul_div_cancel₀ _ hmr.ne'] at this
      linarith
    have hi : ((r + 1 + m * t : ℕ) : ℝ) * Real.goldenRatio < m * q + s + 1 := by
      rw [hn]
      have := mul_lt_mul_of_pos_left h2 hmr
      have e1 : (m : ℝ) * ((r + 1 : ℝ) * Real.goldenRatio / m + t * Real.goldenRatio) =
          (r + 1) * Real.goldenRatio + m * (t * Real.goldenRatio) := by field_simp
      have e2 : (m : ℝ) * (q + (s + 1) / m) = m * q + s + 1 := by field_simp; ring
      linarith
    have hpos : (0 : ℝ) ≤ ((r + 1 + m * t : ℕ) : ℝ) * Real.goldenRatio :=
      mul_nonneg (Nat.cast_nonneg _) Real.goldenRatio_pos.le
    have hq : 0 ≤ q := by
      by_contra hq
      push Not at hq
      have : (q : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hq
      have hs' : (s : ℝ) + 1 ≤ m := by exact_mod_cast hs
      nlinarith
    have hfl : ⌊((r + 1 + m * t : ℕ) : ℝ) * Real.goldenRatio⌋₊ = m * q.toNat + s := by
      rw [Nat.floor_eq_iff hpos]
      have e : ((m * q.toNat + s : ℕ) : ℝ) = m * q + s := by
        push_cast; rw [show ((q.toNat : ℕ) : ℝ) = (q : ℝ) by exact_mod_cast Int.toNat_of_nonneg hq]
      rw [e]
      exact ⟨lo, hi⟩
    rw [hfl, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]

lemma mod_eq_iff {m x y : ℕ} (hy : y < m) : x % m = y ↔ (x : ZMod m) = y := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hy]

theorem a035513 : ∀ m : ℕ, 2 ≤ m →
    {p : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ p = (T n 1 % m, T n 2 % m)}.ncard = m ^ 2 := by
  intro m hm
  have hm0 : 0 < m := by omega
  have hset : {p : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ p = (T n 1 % m, T n 2 % m)} =
      ↑(range m ×ˢ range m) := by
    ext ⟨u, v⟩
    simp only [Set.mem_ofPred_eq, coe_product, coe_range, Set.mem_prod, Set.mem_Iio,
      Prod.mk.injEq]
    constructor
    · rintro ⟨n, -, rfl, rfl⟩
      exact ⟨Nat.mod_lt _ hm0, Nat.mod_lt _ hm0⟩
    · rintro ⟨hu, hv⟩
      obtain ⟨s, hs⟩ : ∃ s, s = (v + m - u) % m := ⟨_, rfl⟩
      obtain ⟨r, hr⟩ : ∃ r, r = (u + m - s) % m := ⟨_, rfl⟩
      have hs' : s < m := by rw [hs]; exact Nat.mod_lt _ hm0
      have hr' : r < m := by rw [hr]; exact Nat.mod_lt _ hm0
      obtain ⟨n, hn, hn1, hA⟩ := exists_row hm0 hr' hs'
      refine ⟨n, hn, ?_, ?_⟩
      · rw [eq_comm, mod_eq_iff hu]
        unfold T
        rw [show Nat.fib (1 + 1) = 1 from rfl, show Nat.fib 1 = 1 from rfl, one_mul, one_mul]
        rw [mod_eq_iff hs'] at hA
        rw [mod_eq_iff hr'] at hn1
        push_cast
        rw [hA, hn1, hr, ZMod.natCast_mod, Nat.cast_sub (by omega)]
        push_cast; rw [ZMod.natCast_self]; ring
      · rw [eq_comm, mod_eq_iff hv]
        unfold T
        rw [show Nat.fib (2 + 1) = 2 from rfl, show Nat.fib 2 = 1 from rfl, one_mul]
        rw [mod_eq_iff hs'] at hA
        rw [mod_eq_iff hr'] at hn1
        push_cast
        rw [hA, hn1, hr, ZMod.natCast_mod, Nat.cast_sub (by omega), hs, ZMod.natCast_mod,
          Nat.cast_sub (by omega)]
        push_cast; rw [ZMod.natCast_self]; ring
  rw [hset, Set.ncard_coe_finset, card_product, card_range, sq]

end OMA.A035513proof

theorem OMA.solution : type_of% @OMA.S_oeis_a035513.main := OMA.A035513proof.a035513
