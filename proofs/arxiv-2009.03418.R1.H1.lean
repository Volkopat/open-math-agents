import OMAReductions.R_arxiv_2009_03418_R1
import Mathlib
/- Adapted from OpenAI, openai/math 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
open OMA.S_arxiv_2009_03418
namespace OAI

/-! Harary–Hill arithmetic, residue-page definitions, and the even-order deletion inequality. -/

section

/-! The Harary–Hill formula and two-page crossing counts.

-/

open scoped BigOperators
noncomputable section
namespace Paper170



/-- The two contiguous residue blocks used by the explicit drawing. -/
def residueColor (n r : ℕ) : Bool := decide (r % n < n / 2)

/-- Increasing four-tuples whose alternating edges occupy the same page. -/
def crossingTuples (n : ℕ) : Finset (Fin 4 → Fin n) := by
  classical
  exact Finset.univ.filter (fun v => StrictMono v ∧
    residueColor n ((v 0).val + (v 2).val) =
      residueColor n ((v 1).val + (v 3).val))

/-- Residues with the same color after a cyclic shift by k. -/
def sameColorResidues (n k : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun r => residueColor n r = residueColor n (r + k))

/-- Cyclic starting points and the first two positive gaps in the source count. -/
def sameColorGapTuples (n k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range n) ×ˢ ((Finset.Icc 1 (k - 1)) ×ˢ (Finset.Icc 1 (n - k - 1)))).filter
    (fun v => residueColor n (2 * v.1 + v.2.1 + v.2.2) =
      residueColor n (2 * v.1 + v.2.1 + v.2.2 + k))

/-- Starting labels producing a prescribed diagonal-sum residue. -/
def residueFiber (n b r : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun a => (2 * a + b) % n = r)

/-- One parity class of the same-color residues. -/
def sameColorResiduesParity (n k p : ℕ) : Finset ℕ :=
  (sameColorResidues n k).filter (fun r => r % 2 = p)

/-- One parity class of the first-gap choices after a fixed offset. -/
def firstGapParity (k b p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (k - 1)).filter (fun g => (g + b) % 2 = p)

/-- The polynomial whose finite difference evaluates the crossing sum. -/
def crossingAntiderivative (n k : ℤ) : ℤ :=
  k * (k - 1) * (n - k - 1) * (n - k - 2)

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem crossingAntiderivative_sub (n k : ℤ) :
    crossingAntiderivative n k - crossingAntiderivative n (k - 1) =
      2 * (k - 1) * (n - k - 1) * (n - 2 * k) := by
  unfold crossingAntiderivative
  ring

theorem hill_numerator_dvd (n : ℕ) :
    4 ∣ n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) := by
  have h₂ : (n - 2) / 2 = n / 2 - 1 := by omega
  have h₃ : (n - 3) / 2 = (n - 1) / 2 - 1 := by omega
  rw [h₂, h₃]
  convert Nat.mul_dvd_mul (Nat.two_dvd_mul_sub_one (n / 2))
    (Nat.two_dvd_mul_sub_one ((n - 1) / 2)) using 1
  ring

theorem hill_even (s : ℕ) : hill (2 * s) = s * (s - 1) ^ 2 * (s - 2) / 4 := by
  have h₁ : (2 * s - 1) / 2 = s - 1 := by omega
  have h₂ : (2 * s - 2) / 2 = s - 1 := by omega
  have h₃ : (2 * s - 3) / 2 = s - 2 := by omega
  simp only [hill, Nat.mul_div_right s (by decide : 0 < 2), h₁, h₂, h₃]
  congr 1
  ring

theorem hill_odd (s : ℕ) : hill (2 * s + 1) = (s.choose 2) ^ 2 := by
  have h₀ : (2 * s + 1) / 2 = s := by omega
  have h₁ : (2 * s + 1 - 1) / 2 = s := by omega
  have h₂ : (2 * s + 1 - 2) / 2 = s - 1 := by omega
  have h₃ : (2 * s + 1 - 3) / 2 = s - 1 := by omega
  have hdiv := Nat.two_dvd_mul_sub_one s
  obtain ⟨a, ha⟩ := hdiv
  rw [hill, h₀, h₁, h₂, h₃, Nat.choose_two_right]
  have hp : s * s * (s - 1) * (s - 1) = 4 * a ^ 2 := by nlinarith [ha]
  rw [hp, ha]
  simp

theorem hill_eq_floor_product {n : ℕ} (hn : 1 ≤ n) :
    (hill n : ℝ) = (1 / 4 : ℝ) * (⌊(n : ℝ) / 2⌋ : ℝ) *
      (⌊((n : ℝ) - 1) / 2⌋ : ℝ) * (⌊((n : ℝ) - 2) / 2⌋ : ℝ) *
      (⌊((n : ℝ) - 3) / 2⌋ : ℝ) := by
  by_cases hsmall : n < 3
  · interval_cases n <;> norm_num [hill]
  have hf (j : ℕ) (hj : j ≤ n) :
      (⌊((n : ℝ) - j) / 2⌋ : ℝ) = ((n - j) / 2 : ℕ) := by
    rw [← Nat.cast_sub hj, show (2 : ℝ) = ((2 : ℕ) : ℝ) by rfl,
      Int.floor_div_natCast, Int.floor_natCast]
    norm_cast
  rw [hill, Nat.cast_div (hill_numerator_dvd n) (by norm_num : (4 : ℝ) ≠ 0)]
  have hf₀ := hf 0 (by omega)
  have hf₁ := hf 1 (by omega)
  have hf₂ := hf 2 (by omega)
  have hf₃ := hf 3 (by omega)
  simp only [Nat.cast_zero, sub_zero, Nat.sub_zero] at hf₀
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at hf₁ hf₂ hf₃
  rw [hf₀, hf₁, hf₂, hf₃]
  push_cast
  ring

theorem crossing_sum_partial {n m : ℕ} (hn : 3 ≤ n) (hm : 2 * m ≤ n) :
    2 * ∑ k ∈ Finset.Icc 1 m, (k - 1) * (n - k - 1) * (n - 2 * k) =
      m * (m - 1) * (n - m - 1) * (n - m - 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), mul_add,
      ih (by omega)]
    by_cases hzero : m = 0
    · subst m; simp
    have hm₁ : 1 ≤ m := by omega
    zify
    simp (disch := omega) only [Nat.cast_sub, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat]
    ring

theorem crossing_sum_telescope {n : ℕ} (hn : 3 ≤ n) :
    (2 * ∑ k ∈ Finset.Icc 1 (n / 2), (k - 1) * (n - k - 1) * (n - 2 * k)) =
      (n / 2) * (n / 2 - 1) * (n - n / 2 - 1) * (n - n / 2 - 2) :=
  crossing_sum_partial hn (by omega)

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem cyclic_count_pairing {n : ℕ} (hn : 3 ≤ n) :
    (∑ k ∈ Finset.Icc 2 (n - 2),
      (k - 1) * (n - k - 1) * (n - 2 * min k (n - k))) =
      2 * ∑ k ∈ Finset.Icc 1 (n / 2), (k - 1) * (n - k - 1) * (n - 2 * k) := by
  let F : ℕ → ℕ := fun k => (k - 1) * (n - k - 1) * (n - 2 * min k (n - k))
  have hsym (k : ℕ) (hk : k ≤ n) : F (n - k) = F k := by
    dsimp [F]
    rw [Nat.sub_sub_self hk, min_comm]
    ring
  have hfull : (∑ k ∈ Finset.Icc 2 (n - 2), F k) = ∑ k ∈ Finset.Ico 1 n, F k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk hnot
      simp only [Finset.mem_Ico, Finset.mem_Icc, not_and] at hk hnot
      have he : k = 1 ∨ k = n - 1 := by omega
      rcases he with rfl | rfl
      · simp [F]
      · have he : n - (n - 1) - 1 = 0 := by omega
        simp [F, he]
  have hsplit := Finset.sum_Ico_consecutive F (show 1 ≤ n / 2 + 1 by omega)
    (show n / 2 + 1 ≤ n by omega)
  have htail : (∑ k ∈ Finset.Ico (n / 2 + 1) n, F k) =
      ∑ k ∈ Finset.Ico 1 (n - n / 2), F k := by
    calc
      _ = ∑ k ∈ Finset.Ico (n / 2 + 1) n, F (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (hsym k (by have := (Finset.mem_Ico.mp hk).2; omega)).symm
      _ = _ := by
        simpa only [Nat.add_sub_cancel_left, Nat.add_sub_add_right] using
          (Finset.sum_Ico_reflect F (n / 2 + 1) (m := n) (n := n) (by omega))
  have hlow : (∑ k ∈ Finset.Ico 1 (n - n / 2), F k) =
      ∑ k ∈ Finset.Ico 1 (n / 2 + 1), F k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro k hk hnot
      simp only [Finset.mem_Ico, not_and] at hk hnot
      have he : n = 2 * k := by omega
      subst n
      simp [F, show 2 * k - k = k by omega]
  have hterm : (∑ k ∈ Finset.Ico 1 (n / 2 + 1), F k) =
      ∑ k ∈ Finset.Icc 1 (n / 2), (k - 1) * (n - k - 1) * (n - 2 * k) := by
    rw [Finset.Ico_add_one_right_eq_Icc]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [F]
    rw [min_eq_left (by have := (Finset.mem_Icc.mp hk).2; omega)]
  change (∑ k ∈ Finset.Icc 2 (n - 2), F k) = _
  rw [hfull, ← hsplit, htail, hlow, hterm]
  omega

end Paper170

end
end

section

noncomputable section
namespace Paper170

lemma four_mul_hill (n : ℕ) :
    4 * hill n = n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) := by
  exact Nat.mul_div_cancel' (hill_numerator_dvd n)

lemma four_mul_hill_even (s : ℕ) :
    4 * hill (2 * s) = s * (s - 1) ^ 2 * (s - 2) := by
  rw [four_mul_hill]
  have h0 : 2 * s / 2 = s := by omega
  have h1 : (2 * s - 1) / 2 = s - 1 := by omega
  have h2 : (2 * s - 2) / 2 = s - 1 := by omega
  have h3 : (2 * s - 3) / 2 = s - 2 := by omega
  rw [h0, h1, h2, h3]
  ring

lemma four_mul_hill_preceding (s : ℕ) :
    4 * hill (2 * s - 1) = (s - 1) ^ 2 * (s - 2) ^ 2 := by
  rw [four_mul_hill]
  have h0 : (2 * s - 1) / 2 = s - 1 := by omega
  have h1 : (2 * s - 1 - 1) / 2 = s - 1 := by omega
  have h2 : (2 * s - 1 - 2) / 2 = s - 2 := by omega
  have h3 : (2 * s - 1 - 3) / 2 = s - 2 := by omega
  rw [h0, h1, h2, h3]
  ring

lemma hill_deletion_relation (s : ℕ) :
    (2 * s - 4) * hill (2 * s) = 2 * s * hill (2 * s - 1) := by
  have hs : 2 * s - 4 = 2 * (s - 2) := by omega
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4)
  calc
    4 * ((2 * s - 4) * hill (2 * s)) =
        (2 * s - 4) * (4 * hill (2 * s)) := by ring
    _ = (2 * s - 4) * (s * (s - 1) ^ 2 * (s - 2)) := by rw [four_mul_hill_even]
    _ = 2 * s * ((s - 1) ^ 2 * (s - 2) ^ 2) := by rw [hs]; ring
    _ = 4 * (2 * s * hill (2 * s - 1)) := by rw [← four_mul_hill_preceding]; ring

lemma even_lower_bound_of_deletion (s c : ℕ) (hs : 3 ≤ s)
    (h : 2 * s * hill (2 * s - 1) ≤ (2 * s - 4) * c) : hill (2 * s) ≤ c := by
  rw [← hill_deletion_relation] at h
  have hp : 0 < 2 * s - 4 := by omega
  nlinarith

end Paper170

end
end

end OAI

namespace OAI

/-! Residue fibers, same-page residues, and parity counts. -/

section

noncomputable section
namespace Paper170

theorem sameColorResidues_eq_intervals {n k : ℕ} (hn : 3 ≤ n)
    (hk : k ≤ n / 2) :
    sameColorResidues n k =
      Finset.Ico 0 (n / 2 - k) ∪ Finset.Ico (n / 2) (n - k) := by
  ext r
  simp only [sameColorResidues, Finset.mem_filter, Finset.mem_range,
    residueColor, decide_eq_decide, Finset.mem_union, Finset.mem_Ico]
  by_cases hr : r < n
  · rw [Nat.mod_eq_of_lt hr]
    by_cases hrs : r + k < n
    · rw [Nat.mod_eq_of_lt hrs]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n ≤ r + k),
        Nat.mod_eq_of_lt (by omega : r + k - n < n)]
      omega
  · omega

theorem sameColorResidues_eq_intervals_large {n k : ℕ} (hn : 3 ≤ n)
    (hk : n / 2 < k) (hkn : k < n) :
    sameColorResidues n k =
      Finset.Ico (n - k) (n / 2) ∪ Finset.Ico (n + n / 2 - k) n := by
  ext r
  simp only [sameColorResidues, Finset.mem_filter, Finset.mem_range,
    residueColor, decide_eq_decide, Finset.mem_union, Finset.mem_Ico]
  by_cases hr : r < n
  · rw [Nat.mod_eq_of_lt hr]
    by_cases hrs : r + k < n
    · rw [Nat.mod_eq_of_lt hrs]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n ≤ r + k),
        Nat.mod_eq_of_lt (by omega : r + k - n < n)]
      omega
  · omega

theorem sameColorResidues_card {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n - 2) :
    (sameColorResidues n k).card = n - 2 * min k (n - k) := by
  by_cases hh : k ≤ n / 2
  · rw [sameColorResidues_eq_intervals hn hh]
    have hd : Disjoint (Finset.Ico 0 (n / 2 - k)) (Finset.Ico (n / 2) (n - k)) := by
      apply Finset.disjoint_left.mpr
      simp only [Finset.mem_Ico]
      omega
    rw [Finset.card_union_of_disjoint hd, Nat.card_Ico, Nat.card_Ico,
      min_eq_left (by omega : k ≤ n - k)]
    omega
  · rw [sameColorResidues_eq_intervals_large hn (by omega) (by omega)]
    have hd : Disjoint (Finset.Ico (n - k) (n / 2)) (Finset.Ico (n + n / 2 - k) n) := by
      apply Finset.disjoint_left.mpr
      simp only [Finset.mem_Ico]
      omega
    rw [Finset.card_union_of_disjoint hd, Nat.card_Ico, Nat.card_Ico,
      min_eq_right (by omega : n - k ≤ k)]
    omega

@[simp] theorem residueColor_mod (n r : ℕ) : residueColor n (r % n) = residueColor n r := by
  simp [residueColor]

theorem residueColor_add_half {m : ℕ} (hm : 0 < m) (r : ℕ) :
    residueColor (2 * m) (r + m) = !residueColor (2 * m) r := by
  have hr := Nat.mod_lt r (by omega : 0 < 2 * m)
  simp only [residueColor, Nat.mul_div_right m (by decide : 0 < 2)]
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : m < 2 * m)]
  by_cases hh : r % (2 * m) < m
  · rw [Nat.mod_eq_of_lt (by omega : r % (2 * m) + m < 2 * m)]
    simp [hh, show ¬r % (2 * m) + m < m by omega]
  · rw [Nat.mod_eq_sub_mod (by omega : 2 * m ≤ r % (2 * m) + m),
      Nat.mod_eq_of_lt (by omega : r % (2 * m) + m - 2 * m < 2 * m)]
    simp [hh, show r % (2 * m) + m - 2 * m < m by omega]

theorem sameColorResidues_half_shift {m k r : ℕ} (hm : 0 < m)
    (hr : r < 2 * m) :
    r ∈ sameColorResidues (2 * m) k ↔
      (r + m) % (2 * m) ∈ sameColorResidues (2 * m) k := by
  simp only [sameColorResidues, Finset.mem_filter, Finset.mem_range, hr,
    Nat.mod_lt _ (by omega : 0 < 2 * m), true_and, residueColor_mod]
  rw [show residueColor (2 * m) ((r + m) % (2 * m) + k) =
      residueColor (2 * m) (r + k + m) by simp [residueColor, Nat.add_mod, Nat.add_right_comm]]
  rw [residueColor_add_half hm, residueColor_add_half hm]
  simp

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem residueFiber_card_odd {n b r : ℕ} (hn : Odd n) (hr : r < n) :
    (residueFiber n b r).card = 1 := by
  let f : Fin n → Fin n := fun a => ⟨(2 * a.val + b) % n, Nat.mod_lt _ (by omega)⟩
  have hi : Function.Injective f := by
    intro a c h
    have hmod : Nat.ModEq n (2 * a.val + b) (2 * c.val + b) := congrArg Fin.val h
    have he := (hmod.add_right_cancel' b).cancel_left_of_coprime hn.coprime_two_right
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt c.isLt] using he
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hi) ⟨r, hr⟩
  have hset : residueFiber n b r = {a.val} := by
    ext c
    simp only [residueFiber, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hcr⟩
      have he : f ⟨c, hc⟩ = f a := by
        rw [ha]
        exact Fin.ext hcr
      exact congrArg Fin.val (hi he)
    · rintro rfl
      exact ⟨a.isLt, congrArg Fin.val ha⟩
  rw [hset, Finset.card_singleton]

theorem add_mod_inj {n a c b : ℕ} (ha : a < n) (hc : c < n)
    (h : (a + b) % n = (c + b) % n) : a = c := by
  have he := Nat.ModEq.add_right_cancel' b h
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] using he

theorem add_mod_surj {n r : ℕ} (hr : r < n) (b : ℕ) :
    ∃ a < n, (a + b) % n = r := by
  let f : Fin n → Fin n := fun a => ⟨(a.val + b) % n, Nat.mod_lt _ (by omega)⟩
  have hi : Function.Injective f := by
    intro a c h
    exact Fin.ext (add_mod_inj a.isLt c.isLt (congrArg Fin.val h))
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hi) ⟨r, hr⟩
  exact ⟨a.val, a.isLt, congrArg Fin.val ha⟩

theorem doubled_residue {m a b r : ℕ} :
    (2 * a + b) % (2 * m) = r ↔
      (a + b / 2) % m = r / 2 ∧ b % 2 = r % 2 := by
  have hh : (2 * a + b) % (2 * m) = b % 2 + 2 * ((a + b / 2) % m) := by
    rw [Nat.mod_mul]
    congr 1
    · omega
    · rw [show (2 * a + b) / 2 = a + b / 2 by omega]
  rw [hh]
  omega

theorem residueFiber_card_even {m b r : ℕ} (hm : 0 < m) (hr : r < 2 * m) :
    (residueFiber (2 * m) b r).card = if r % 2 = b % 2 then 2 else 0 := by
  by_cases hp : r % 2 = b % 2
  · rw [if_pos hp]
    obtain ⟨a, ha, har⟩ := add_mod_surj (show r / 2 < m by omega) (b / 2)
    have hset : residueFiber (2 * m) b r = {a, a + m} := by
      ext c
      simp only [residueFiber, Finset.mem_filter, Finset.mem_range,
        Finset.mem_insert, Finset.mem_singleton, doubled_residue]
      constructor
      · rintro ⟨hc, hcr, _⟩
        have he : c % m = a := add_mod_inj (Nat.mod_lt _ hm) ha
          (by simpa only [Nat.add_mod, Nat.mod_mod] using hcr.trans har.symm)
        by_cases hcm : c < m
        · left
          simpa only [Nat.mod_eq_of_lt hcm] using he
        · right
          rw [Nat.mod_eq_sub_mod (by omega : m ≤ c),
            Nat.mod_eq_of_lt (by omega : c - m < m)] at he
          omega
      · rintro (rfl | rfl)
        · exact ⟨by omega, har, hp.symm⟩
        · refine ⟨by omega, ?_, hp.symm⟩
          simpa only [Nat.add_right_comm a m (b / 2), Nat.add_mod_right] using har
    rw [hset, Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  · rw [if_neg hp]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a
    simp only [residueFiber, Finset.mem_filter, Finset.mem_range, doubled_residue]
    rintro ⟨_, _, he⟩
    exact hp he.symm

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem parity_balance_of_involution (s : Finset ℕ) (f : ℕ → ℕ) (c : ℕ)
    (hmap : ∀ r ∈ s, f r ∈ s) (hinv : ∀ r ∈ s, f (f r) = r)
    (hpar : ∀ r ∈ s, (f r + c) % 2 ≠ (r + c) % 2) :
    (s.filter (fun r => (r + c) % 2 = 0)).card =
      (s.filter (fun r => (r + c) % 2 = 1)).card := by
  apply Finset.card_nbij' f f
  · intro r hr
    obtain ⟨hs, he⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hmap r hs, by have := hpar r hs; omega⟩
  · intro r hr
    obtain ⟨hs, he⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hmap r hs, by have := hpar r hs; omega⟩
  · intro r hr
    exact hinv r (Finset.mem_filter.mp hr).1
  · intro r hr
    exact hinv r (Finset.mem_filter.mp hr).1

theorem interval_parity_balance {a b : ℕ} (heven : Even (b - a)) (c : ℕ) :
    ((Finset.Ico a b).filter (fun r => (r + c) % 2 = 0)).card =
      ((Finset.Ico a b).filter (fun r => (r + c) % 2 = 1)).card := by
  obtain ⟨t, ht⟩ := heven
  let f : ℕ → ℕ := fun r => if (r - a) % 2 = 0 then r + 1 else r - 1
  apply parity_balance_of_involution (Finset.Ico a b) f c
  · intro r hr
    simp only [Finset.mem_Ico] at hr ⊢
    dsimp [f]
    split_ifs <;> omega
  · intro r hr
    simp only [Finset.mem_Ico] at hr
    dsimp [f]
    split_ifs <;> omega
  · intro r hr
    simp only [Finset.mem_Ico] at hr
    dsimp [f]
    split_ifs <;> omega

theorem firstGapParity_balance {k : ℕ} (hk : Odd k) (b : ℕ) :
    (firstGapParity k b 0).card = (firstGapParity k b 1).card := by
  have heven : Even (k - 1) := by
    rw [Nat.even_iff]
    obtain ⟨t, ht⟩ := hk
    omega
  have heq : Finset.Icc 1 (k - 1) = Finset.Ico 1 k := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    obtain ⟨t, ht⟩ := hk
    omega
  simpa only [firstGapParity, heq] using interval_parity_balance heven b

theorem parity_balance_union (s t : Finset ℕ) (hd : Disjoint s t)
    (hs : (s.filter (fun r => r % 2 = 0)).card = (s.filter (fun r => r % 2 = 1)).card)
    (ht : (t.filter (fun r => r % 2 = 0)).card = (t.filter (fun r => r % 2 = 1)).card) :
    ((s ∪ t).filter (fun r => r % 2 = 0)).card =
      ((s ∪ t).filter (fun r => r % 2 = 1)).card := by
  have hdis (p : ℕ) : Disjoint (s.filter (fun r => r % 2 = p))
      (t.filter (fun r => r % 2 = p)) := hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  simp only [Finset.filter_union, Finset.card_union_of_disjoint (hdis 0),
    Finset.card_union_of_disjoint (hdis 1), hs, ht]

theorem sameColorResidues_parity_balance {m k : ℕ} (hm : 0 < m)
    (hk : 2 ≤ k) (hkn : k ≤ 2 * m - 2) (hparity : Odd m ∨ Even k) :
    (sameColorResiduesParity (2 * m) k 0).card =
      (sameColorResiduesParity (2 * m) k 1).card := by
  by_cases hmo : Odd m
  · obtain ⟨t, ht⟩ := hmo
    let f : ℕ → ℕ := fun r => if r < m then r + m else r - m
    have hform (r : ℕ) (hr : r < 2 * m) : f r = (r + m) % (2 * m) := by
      dsimp [f]
      split_ifs with h
      · rw [Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    apply parity_balance_of_involution (sameColorResidues (2 * m) k) f 0
    · intro r hr
      have hrl : r < 2 * m := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
      rw [hform r hrl]
      exact (sameColorResidues_half_shift hm hrl).mp hr
    · intro r hr
      have hrl : r < 2 * m := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
      dsimp [f]
      split_ifs <;> omega
    · intro r hr
      have hrl : r < 2 * m := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
      dsimp [f]
      split_ifs <;> omega
  · have hme : Even m := Nat.not_odd_iff_even.mp hmo
    have hke : Even k := hparity.resolve_left hmo
    have hm₂ : 3 ≤ 2 * m := by omega
    have even_diff (a b : ℕ) (ha : Even a) (hb : Even b) : Even (a - b) := by
      rw [Nat.even_iff] at *
      omega
    unfold sameColorResiduesParity
    by_cases hhalf : k ≤ m
    · rw [sameColorResidues_eq_intervals hm₂ (by simpa using hhalf)]
      simp only [Nat.mul_div_right m (by decide : 0 < 2)]
      apply parity_balance_union
      · apply Finset.disjoint_left.mpr
        simp only [Finset.mem_Ico]
        omega
      · simpa using interval_parity_balance (a := 0) (b := m - k)
          (by simpa using even_diff m k hme hke) 0
      · have he : Even (2 * m - k - m) := by
          apply even_diff _ _ (even_diff _ _ (by simp) hke) hme
        simpa using interval_parity_balance he 0
    · rw [sameColorResidues_eq_intervals_large hm₂ (by simpa using Nat.lt_of_not_ge hhalf) (by omega)]
      simp only [Nat.mul_div_right m (by decide : 0 < 2)]
      apply parity_balance_union
      · apply Finset.disjoint_left.mpr
        simp only [Finset.mem_Ico]
        omega
      · have he : Even (m - (2 * m - k)) := even_diff _ _ hme (even_diff _ _ (by simp) hke)
        simpa using interval_parity_balance he 0
      · have he : Even (2 * m - (2 * m + m - k)) :=
          even_diff _ _ (by simp) (even_diff _ _
            (by simpa only [two_mul, add_assoc] using hme.add hme |>.add hme) hke)
        simpa using interval_parity_balance he 0

end Paper170

end
end

end OAI

namespace OAI

/-! Cyclic gap enumeration and the exact Harary–Hill crossing-tuple count. -/

section

noncomputable section
open scoped BigOperators
namespace Paper170

def naturalCrossingTuples (n : ℕ) : Finset (Fin 4 → ℕ) :=
  (crossingTuples n).image (fun v i => (v i).val)

theorem mem_naturalCrossingTuples {n : ℕ} {v : Fin 4 → ℕ} :
    v ∈ naturalCrossingTuples n ↔
      v 0 < v 1 ∧ v 1 < v 2 ∧ v 2 < v 3 ∧ v 3 < n ∧
        residueColor n (v 0 + v 2) = residueColor n (v 1 + v 3) := by
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨_, hw, hc⟩ := Finset.mem_filter.mp hw
    exact ⟨hw (by decide : (0 : Fin 4) < 1), hw (by decide : (1 : Fin 4) < 2),
      hw (by decide : (2 : Fin 4) < 3), (w 3).isLt, hc⟩
  · rintro ⟨h₀, h₁, h₂, h₃, hc⟩
    have hb (i : Fin 4) : v i < n := by fin_cases i <;> dsimp <;> omega
    let w : Fin 4 → Fin n := fun i => ⟨v i, hb i⟩
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hc⟩, rfl⟩
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simp only [w, Fin.mk_lt_mk] <;> assumption

theorem naturalCrossingTuples_card (n : ℕ) :
    (naturalCrossingTuples n).card = (crossingTuples n).card := by
  apply Finset.card_image_of_injective
  intro v w h
  funext i
  exact Fin.ext (congrFun h i)

abbrev CyclicRecord := Σ _ : ℕ, ℕ × ℕ × ℕ

def cyclicRecords (n : ℕ) : Finset CyclicRecord :=
  (Finset.Icc 2 (n - 2)).sigma (fun k => sameColorGapTuples n k)

theorem mem_cyclicRecords {n k a g h : ℕ} :
    (⟨k, a, g, h⟩ : CyclicRecord) ∈ cyclicRecords n ↔
      2 ≤ k ∧ k ≤ n - 2 ∧ a < n ∧ 1 ≤ g ∧ g ≤ k - 1 ∧
        1 ≤ h ∧ h ≤ n - k - 1 ∧
          residueColor n (2 * a + g + h) = residueColor n (2 * a + g + h + k) := by
  simp [cyclicRecords, sameColorGapTuples, and_assoc]

def cyclicToOrdered (n : ℕ) (p : CyclicRecord) : Fin 4 × (Fin 4 → ℕ) :=
  let k := p.1
  let a := p.2.1
  let b := a + p.2.2.1
  let c := b + p.2.2.2
  let d := a + k + p.2.2.2
  if d < n then (0, ![a, b, c, d])
  else if c < n then (1, ![d - n, a, b, c])
  else if b < n then (2, ![c - n, d - n, a, b])
  else (3, ![b - n, c - n, d - n, a])

def orderedToCyclic (n : ℕ) (q : Fin 4 × (Fin 4 → ℕ)) : CyclicRecord :=
  let v := q.2
  match q.1.val with
  | 0 => ⟨(v 1 - v 0) + (v 3 - v 2), v 0, v 1 - v 0, v 2 - v 1⟩
  | 1 => ⟨(v 2 - v 1) + (v 0 + n - v 3), v 1, v 2 - v 1, v 3 - v 2⟩
  | 2 => ⟨(v 3 - v 2) + (v 1 - v 0), v 2, v 3 - v 2, v 0 + n - v 3⟩
  | _ => ⟨(v 0 + n - v 3) + (v 2 - v 1), v 3, v 0 + n - v 3, v 1 - v 0⟩

theorem residueColor_shift_eq {n x y : ℕ} (t : ℕ) (h : x + t * n = y) :
    residueColor n x = residueColor n y := by
  rw [← h]
  simp [residueColor, Nat.add_mod]

theorem cyclicToOrdered_spec {n k a g h : ℕ} (hk : 2 ≤ k) (_hkn : k ≤ n - 2)
    (ha : a < n) (hg : 1 ≤ g) (hgk : g ≤ k - 1)
    (hh : 1 ≤ h) (hhn : h ≤ n - k - 1) :
    let v := (cyclicToOrdered n ⟨k, a, g, h⟩).2
    v 0 < v 1 ∧ v 1 < v 2 ∧ v 2 < v 3 ∧ v 3 < n ∧
      (residueColor n (v 0 + v 2) = residueColor n (v 1 + v 3) ↔
        residueColor n (2 * a + g + h) = residueColor n (2 * a + g + h + k)) := by
  by_cases hd : a + k + h < n
  · simp only [cyclicToOrdered, hd, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨by omega, by omega, by omega, by trivial, ?_⟩
    rw [show a + (a + g + h) = 2 * a + g + h by omega,
      show a + g + (a + k + h) = 2 * a + g + h + k by omega]
  · by_cases hc : a + g + h < n
    · simp only [cyclicToOrdered, hd, hc, ↓reduceIte, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      refine ⟨by omega, by omega, by omega, by trivial, ?_⟩
      rw [residueColor_shift_eq 1 (show (a + k + h - n + (a + g)) + 1 * n =
        2 * a + g + h + k by omega)]
      have he : a + (a + g + h) = 2 * a + g + h := by omega
      rw [he, eq_comm]
    · by_cases hb : a + g < n
      · simp only [cyclicToOrdered, hd, hc, hb, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        refine ⟨by omega, by omega, by omega, by trivial, ?_⟩
        rw [residueColor_shift_eq 1 (show (a + g + h - n + a) + 1 * n =
          2 * a + g + h by omega),
          residueColor_shift_eq 1 (show (a + k + h - n + (a + g)) + 1 * n =
          2 * a + g + h + k by omega)]
      · simp only [cyclicToOrdered, hd, hc, hb, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        refine ⟨by omega, by omega, by omega, ha, ?_⟩
        rw [residueColor_shift_eq 2 (show (a + g - n + (a + k + h - n)) + 2 * n =
          2 * a + g + h + k by omega),
          residueColor_shift_eq 1 (show (a + g + h - n + a) + 1 * n =
          2 * a + g + h by omega), eq_comm]

theorem orderedToCyclic_bounds {n : ℕ} (j : Fin 4) (v : Fin 4 → ℕ)
    (h₀ : v 0 < v 1) (h₁ : v 1 < v 2) (h₂ : v 2 < v 3) (h₃ : v 3 < n) :
    let p := orderedToCyclic n (j, v)
    2 ≤ p.1 ∧ p.1 ≤ n - 2 ∧ p.2.1 < n ∧ 1 ≤ p.2.2.1 ∧
      p.2.2.1 ≤ p.1 - 1 ∧ 1 ≤ p.2.2.2 ∧ p.2.2.2 ≤ n - p.1 - 1 := by
  fin_cases j <;> simp [orderedToCyclic] <;> omega

theorem orderedToCyclic_inverse {n : ℕ} (j : Fin 4) (v : Fin 4 → ℕ)
    (h₀ : v 0 < v 1) (h₁ : v 1 < v 2) (h₂ : v 2 < v 3) (h₃ : v 3 < n) :
    cyclicToOrdered n (orderedToCyclic n (j, v)) = (j, v) := by
  fin_cases j <;> simp (disch := omega) [orderedToCyclic, cyclicToOrdered]
  all_goals split_ifs <;> try omega
  all_goals
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp <;> omega

theorem cyclicToOrdered_inverse {n k a g h : ℕ} (hk : 2 ≤ k) (_hkn : k ≤ n - 2)
    (ha : a < n) (hg : 1 ≤ g) (hgk : g ≤ k - 1)
    (hh : 1 ≤ h) (hhn : h ≤ n - k - 1) :
    orderedToCyclic n (cyclicToOrdered n ⟨k, a, g, h⟩) = ⟨k, a, g, h⟩ := by
  unfold cyclicToOrdered
  dsimp only
  split_ifs <;> simp [orderedToCyclic] <;> omega

theorem cyclicToOrdered_mem {n : ℕ} {p : CyclicRecord} (hp : p ∈ cyclicRecords n) :
    cyclicToOrdered n p ∈ (Finset.univ : Finset (Fin 4)) ×ˢ naturalCrossingTuples n := by
  rcases p with ⟨k, a, g, h⟩
  obtain ⟨hk, hkn, ha, hg, hgk, hh, hhn, hc⟩ := mem_cyclicRecords.mp hp
  obtain ⟨h₀, h₁, h₂, h₃, he⟩ := cyclicToOrdered_spec hk hkn ha hg hgk hh hhn
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
    mem_naturalCrossingTuples.mpr ⟨h₀, h₁, h₂, h₃, he.mpr hc⟩⟩

theorem orderedToCyclic_mem {n : ℕ} {q : Fin 4 × (Fin 4 → ℕ)}
    (hq : q ∈ (Finset.univ : Finset (Fin 4)) ×ˢ naturalCrossingTuples n) :
    orderedToCyclic n q ∈ cyclicRecords n := by
  rcases q with ⟨j, v⟩
  obtain ⟨h₀, h₁, h₂, h₃, hc⟩ := mem_naturalCrossingTuples.mp (Finset.mem_product.mp hq).2
  obtain ⟨hk, hkn, ha, hg, hgk, hh, hhn⟩ := orderedToCyclic_bounds j v h₀ h₁ h₂ h₃
  apply mem_cyclicRecords.mpr
  refine ⟨hk, hkn, ha, hg, hgk, hh, hhn, ?_⟩
  have he := (cyclicToOrdered_spec hk hkn ha hg hgk hh hhn).2.2.2.2
  rw [show (⟨(orderedToCyclic n (j, v)).1, (orderedToCyclic n (j, v)).2.1,
      (orderedToCyclic n (j, v)).2.2.1, (orderedToCyclic n (j, v)).2.2.2⟩ : CyclicRecord) =
      orderedToCyclic n (j, v) from rfl, orderedToCyclic_inverse j v h₀ h₁ h₂ h₃] at he
  exact he.mp hc

theorem crossingTuples_cyclic_count {n : ℕ} (_hn : 3 ≤ n) :
    4 * (crossingTuples n).card =
      ∑ k ∈ Finset.Icc 2 (n - 2), (sameColorGapTuples n k).card := by
  have hcard : (cyclicRecords n).card =
      ((Finset.univ : Finset (Fin 4)) ×ˢ naturalCrossingTuples n).card := by
    apply Finset.card_nbij' (cyclicToOrdered n) (orderedToCyclic n)
    · exact fun _ hp => cyclicToOrdered_mem hp
    · exact fun _ hq => orderedToCyclic_mem hq
    · rintro ⟨k, a, g, h⟩ hp
      obtain ⟨hk, hkn, ha, hg, hgk, hh, hhn, _⟩ := mem_cyclicRecords.mp hp
      exact cyclicToOrdered_inverse hk hkn ha hg hgk hh hhn
    · rintro ⟨j, v⟩ hq
      obtain ⟨h₀, h₁, h₂, h₃, _⟩ := mem_naturalCrossingTuples.mp (Finset.mem_product.mp hq).2
      exact orderedToCyclic_inverse j v h₀ h₁ h₂ h₃
  simpa only [cyclicRecords, Finset.card_sigma, Finset.card_product,
    Finset.card_univ, Fintype.card_fin, naturalCrossingTuples_card] using hcard.symm

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

def startingLabels (n k b : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun a =>
    residueColor n (2 * a + b) = residueColor n (2 * a + b + k))

theorem startingLabels_card_eq_sum {n : ℕ} (hn : 0 < n) (k b : ℕ) :
    (startingLabels n k b).card =
      ∑ r ∈ sameColorResidues n k, (residueFiber n b r).card := by
  unfold residueFiber
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext a
  simp [startingLabels, sameColorResidues, residueColor,
    Nat.mod_lt _ hn, Nat.add_mod]

theorem startingLabels_card_odd {n : ℕ} (hn : Odd n) (k b : ℕ) :
    (startingLabels n k b).card = (sameColorResidues n k).card := by
  have hpos : 0 < n := by obtain ⟨t, ht⟩ := hn; omega
  rw [startingLabels_card_eq_sum hpos]
  calc
    (∑ r ∈ sameColorResidues n k, (residueFiber n b r).card) =
        ∑ _r ∈ sameColorResidues n k, 1 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact residueFiber_card_odd hn (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    _ = _ := by simp

theorem startingLabels_card_even {m : ℕ} (hm : 0 < m) (k b : ℕ) :
    (startingLabels (2 * m) k b).card = 2 * (sameColorResiduesParity (2 * m) k (b % 2)).card := by
  rw [startingLabels_card_eq_sum (by omega)]
  calc
    (∑ r ∈ sameColorResidues (2 * m) k, (residueFiber (2 * m) b r).card) =
        ∑ r ∈ sameColorResidues (2 * m) k, if r % 2 = b % 2 then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact residueFiber_card_even hm (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    _ = _ := by rw [← Finset.sum_filter]; simp [sameColorResiduesParity, mul_comm]

theorem parity_partition (s : Finset ℕ) (b : ℕ) :
    (s.filter (fun r => (r + b) % 2 = 0)).card +
      (s.filter (fun r => (r + b) % 2 = 1)).card = s.card := by
  have he : s.filter (fun r => ¬(r + b) % 2 = 0) = s.filter (fun r => (r + b) % 2 = 1) := by
    ext r
    rcases Nat.mod_two_eq_zero_or_one (r + b) with h | h <;> simp [h]
  rw [← he]
  exact Finset.card_filter_add_card_filter_not (s := s) _

theorem startingLabels_card_even_balanced {m k : ℕ} (hm : 0 < m)
    (hk : 2 ≤ k) (hkn : k ≤ 2 * m - 2) (hparity : Odd m ∨ Even k) (b : ℕ) :
    (startingLabels (2 * m) k b).card = (sameColorResidues (2 * m) k).card := by
  rw [startingLabels_card_even hm]
  have hbal := sameColorResidues_parity_balance hm hk hkn hparity
  have htotal := parity_partition (sameColorResidues (2 * m) k) 0
  simp only [Nat.add_zero] at htotal
  change (sameColorResiduesParity (2 * m) k 0).card +
    (sameColorResiduesParity (2 * m) k 1).card = _ at htotal
  have hb : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
  rcases hb with hb | hb <;> rw [hb] <;> omega

theorem sum_parity_weights (s : Finset ℕ) (b x y : ℕ)
    (hbal : (s.filter (fun r => (r + b) % 2 = 0)).card =
      (s.filter (fun r => (r + b) % 2 = 1)).card) :
    (∑ r ∈ s, 2 * (if (r + b) % 2 = 0 then x else y)) = s.card * (x + y) := by
  have he : s.filter (fun r => ¬(r + b) % 2 = 0) = s.filter (fun r => (r + b) % 2 = 1) := by
    ext r
    rcases Nat.mod_two_eq_zero_or_one (r + b) with h | h <;> simp [h]
  rw [← Finset.mul_sum, Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul, he]
  rw [← parity_partition s b, hbal]
  ring

theorem startingLabels_sum_odd_gap {m k : ℕ} (hm : 0 < m) (hk : Odd k) (b : ℕ) :
    (∑ g ∈ Finset.Icc 1 (k - 1), (startingLabels (2 * m) k (g + b)).card) =
      (k - 1) * (sameColorResidues (2 * m) k).card := by
  simp_rw [startingLabels_card_even hm]
  have hfun (g : ℕ) : (sameColorResiduesParity (2 * m) k ((g + b) % 2)).card =
      if (g + b) % 2 = 0 then (sameColorResiduesParity (2 * m) k 0).card
      else (sameColorResiduesParity (2 * m) k 1).card := by
    rcases Nat.mod_two_eq_zero_or_one (g + b) with h | h <;> simp [h]
  simp_rw [hfun]
  rw [sum_parity_weights _ _ _ _ (firstGapParity_balance hk b)]
  have htotal := parity_partition (sameColorResidues (2 * m) k) 0
  simp only [Nat.add_zero] at htotal
  change (sameColorResiduesParity (2 * m) k 0).card +
    (sameColorResiduesParity (2 * m) k 1).card = _ at htotal
  rw [htotal, Nat.card_Icc]
  congr 1

theorem sameColorGapTuples_card_eq_sum (n k : ℕ) :
    (sameColorGapTuples n k).card =
      ∑ g₂ ∈ Finset.Icc 1 (n - k - 1), ∑ g₁ ∈ Finset.Icc 1 (k - 1),
        (startingLabels n k (g₁ + g₂)).card := by
  simp only [sameColorGapTuples, startingLabels, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product, Nat.add_assoc]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext g₁; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem sameColorGapTuples_card {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n - 2) :
    (sameColorGapTuples n k).card = (k - 1) * (n - k - 1) *
      (sameColorResidues n k).card := by
  rw [sameColorGapTuples_card_eq_sum]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    have heq : n = 2 * m := by omega
    clear hm
    subst n
    have hmp : 0 < m := by omega
    by_cases hpar : Odd m ∨ Even k
    · simp_rw [startingLabels_card_even_balanced hmp hk hkn hpar]
      simp only [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
      have h₁ : k - 1 + 1 - 1 = k - 1 := by omega
      have h₂ : 2 * m - k - 1 + 1 - 1 = 2 * m - k - 1 := by omega
      rw [h₁, h₂]
      ring
    · have hko : Odd k := Nat.not_even_iff_odd.mp (fun h => hpar (Or.inr h))
      simp_rw [startingLabels_sum_odd_gap hmp hko]
      simp only [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
      have h₂ : 2 * m - k - 1 + 1 - 1 = 2 * m - k - 1 := by omega
      rw [h₂]
      ring
  · simp_rw [startingLabels_card_odd ho]
    simp only [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
    have h₁ : k - 1 + 1 - 1 = k - 1 := by omega
    have h₂ : n - k - 1 + 1 - 1 = n - k - 1 := by omega
    rw [h₁, h₂]
    ring

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem crossingTuples_card {n : ℕ} (hn : 3 ≤ n) :
    (crossingTuples n).card = hill n := by
  have hcount : 4 * (crossingTuples n).card =
      (n / 2) * (n / 2 - 1) * (n - n / 2 - 1) * (n - n / 2 - 2) := by
    rw [crossingTuples_cyclic_count hn]
    calc
      (∑ k ∈ Finset.Icc 2 (n - 2), (sameColorGapTuples n k).card) =
          ∑ k ∈ Finset.Icc 2 (n - 2),
            (k - 1) * (n - k - 1) * (n - 2 * min k (n - k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk₁ := (Finset.mem_Icc.mp hk).1
        have hk₂ := (Finset.mem_Icc.mp hk).2
        rw [sameColorGapTuples_card hn hk₁ hk₂, sameColorResidues_card hn hk₁ hk₂]
      _ = _ := by rw [cyclic_count_pairing hn, crossing_sum_telescope hn]
  have h₁ : n - n / 2 - 1 = (n - 1) / 2 := by omega
  have h₂ : n / 2 - 1 = (n - 2) / 2 := by omega
  have h₃ : n - n / 2 - 2 = (n - 3) / 2 := by omega
  rw [h₁, h₂, h₃] at hcount
  have hp : n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) =
      4 * (crossingTuples n).card := by rw [hcount]; ring
  rw [hill, hp]
  omega

end Paper170

end
end

end OAI



-- OAI.Combinatorics.Crossing.DrawingDefinition
namespace OAI

noncomputable section

namespace Zarankiewicz

abbrev Plane := ℝ × ℝ

def ProperCrossing (A B : Set Plane) (x : Plane) : Prop :=
  ∃ chart : OpenPartialHomeomorph Plane Plane,
    x ∈ chart.source ∧ chart x = (0,0) ∧
    chart '' (chart.source ∩ A) = chart.target ∩ {y | y.2 = 0} ∧
    chart '' (chart.source ∩ B) = chart.target ∩ {y | y.1 = 0}

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.CompleteCrossing.Drawing
namespace OAI

section

noncomputable section

open Set

open scoped BigOperators Classical

namespace Paper170

def squaredLength (x : Plane) : ℝ := x.1 ^ 2 + x.2 ^ 2

def det2 (x y : Plane) : ℝ := x.1 * y.2 - x.2 * y.1

def segmentPoint (a b : Plane) (t : ℝ) : Plane := (1 - t) • a + t • b

variable {V E : Type} (G : OMA.S_arxiv_2009_03418.Graph V E)

variable {G}

structure PolygonalParametrization {a b : Plane} (γ : Path a b) where
  pieces : ℕ
  positive : 0 < pieces
  knot : Fin (pieces + 1) → unitInterval
  increasing : StrictMono knot
  first : knot 0 = 0
  last : knot (Fin.last pieces) = 1
  affine : ∀ i : Fin pieces, ∀ t : unitInterval,
    knot i.castSucc ≤ t → t ≤ knot i.succ →
    γ t = segmentPoint (γ (knot i.castSucc)) (γ (knot i.succ))
      (((t : ℝ) - knot i.castSucc) / ((knot i.succ : ℝ) - knot i.castSucc))

variable [Fintype V] [Fintype E]

def inversion (z : Plane) : Plane := (z.1 / squaredLength z, z.2 / squaredLength z)

end Paper170

end

end

section

noncomputable section

variable {Vertex Edge : Type} {graph : OMA.S_arxiv_2009_03418.Graph Vertex Edge}

namespace Paper170Geometry

open scoped BigOperators Classical

theorem crossing_incident_iff (D : OMA.S_arxiv_2009_03418.AdmissibleDrawing graph) (x : Plane)
    (e f : Edge) (hef : e ≠ f)
    (he : x ∈ OMA.S_arxiv_2009_03418.edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ OMA.S_arxiv_2009_03418.edgeInterior D.toContinuousDrawing f) (g : Edge) :
    x ∈ OMA.S_arxiv_2009_03418.edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  constructor
  · intro hg
    by_contra hh
    have hge : e ≠ g := by tauto
    have hgf : f ≠ g := by tauto
    have hmem : x ∈ OMA.S_arxiv_2009_03418.edgeInterior D.toContinuousDrawing e ∩ OMA.S_arxiv_2009_03418.edgeInterior D.toContinuousDrawing f ∩
        OMA.S_arxiv_2009_03418.edgeInterior D.toContinuousDrawing g := ⟨⟨he,hf⟩,hg⟩
    rw [D.no_triples e f g hef hge hgf] at hmem
    exact hmem
  · rintro (rfl | rfl) <;> assumption

variable [Fintype Edge]

end Paper170Geometry

end

end

end OAI


-- OAI.Combinatorics.Crossing.PlanarSegments
namespace OAI

noncomputable section

namespace Zarankiewicz

open scoped Classical

def det2 (u v : Plane) : ℝ := u.1*v.2-u.2*v.1

def segmentPoint (a b : Plane) (t : ℝ) : Plane := (1-t) • a+t • b

def openSegmentTrace (a b : Plane) : Set Plane := segmentPoint a b '' Set.Ioo 0 1

def SegmentsCrossProperly (a b c d : Plane) : Prop :=
  det2 (b-a) (d-c) ≠ 0 ∧
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ u ∈ Set.Ioo (0 : ℝ) 1,
      segmentPoint a b t = segmentPoint c d u

def segmentCrossingSign (a b c d : Plane) : ℝ :=
  if SegmentsCrossProperly a b c d then
    (if 0 < det2 (b-a) (d-c) then 1 else -1) else 0

@[simp] theorem segmentPoint_zero (a b : Plane) : segmentPoint a b 0 = a := by
  simp [segmentPoint]

@[simp] theorem segmentPoint_one (a b : Plane) : segmentPoint a b 1 = b := by
  simp [segmentPoint]

theorem segmentPoint_reverse (a b : Plane) (t : ℝ) :
    segmentPoint b a (1-t) = segmentPoint a b t := by
  simp [segmentPoint, add_comm]

theorem det2_swap (u v : Plane) : det2 v u = -det2 u v := by
  simp only [det2]
  ring

theorem segment_intersection_parameters_unique (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) (t u t' u' : ℝ)
    (h : segmentPoint a b t = segmentPoint c d u)
    (h' : segmentPoint a b t' = segmentPoint c d u') : t = t' ∧ u = u' := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  have h₁' := congrArg Prod.fst h'
  have h₂' := congrArg Prod.snd h'
  change (1-t)*a.1+t*b.1 = (1-u)*c.1+u*d.1 at h₁
  change (1-t)*a.2+t*b.2 = (1-u)*c.2+u*d.2 at h₂
  change (1-t')*a.1+t'*b.1 = (1-u')*c.1+u'*d.1 at h₁'
  change (1-t')*a.2+t'*b.2 = (1-u')*c.2+u'*d.2 at h₂'
  have ht : (t-t') * det2 (b-a) (d-c) = 0 := by
    dsimp [det2]
    linear_combination (d.2-c.2)*h₁ - (d.1-c.1)*h₂ - (d.2-c.2)*h₁' + (d.1-c.1)*h₂'
  have hu : (u-u') * det2 (b-a) (d-c) = 0 := by
    dsimp [det2]
    linear_combination (b.2-a.2)*h₁ - (b.1-a.1)*h₂ - (b.2-a.2)*h₁' + (b.1-a.1)*h₂'
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hn),
    sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right hn)⟩

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.SegmentSymmetries
namespace OAI

noncomputable section

namespace Zarankiewicz

open scoped Classical

theorem segmentsCrossProperly_swap (a b c d : Plane) :
    SegmentsCrossProperly c d a b ↔ SegmentsCrossProperly a b c d := by
  constructor
  · rintro ⟨hn,t,ht,u,hu,he⟩
    refine ⟨?_,u,hu,t,ht,he.symm⟩
    rw [det2_swap] at hn
    exact neg_ne_zero.mp hn
  · rintro ⟨hn,t,ht,u,hu,he⟩
    refine ⟨?_,u,hu,t,ht,he.symm⟩
    rw [det2_swap]
    exact neg_ne_zero.mpr hn

theorem openSegment_intersection_subsingleton (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) : (openSegmentTrace a b ∩ openSegmentTrace c d).Subsingleton := by
  rintro x ⟨⟨t,ht,htx⟩,⟨u,hu,hux⟩⟩ y ⟨⟨t',ht',hty⟩,⟨u',hu',huy⟩⟩
  have hh := segment_intersection_parameters_unique a b c d hn t u t' u'
    (htx.trans hux.symm) (hty.trans huy.symm)
  rw [← htx, ← hty, hh.1]

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.SegmentParameters
namespace OAI

noncomputable section

namespace Zarankiewicz

def firstIntersectionParameter (a b c d : Plane) : ℝ :=
  det2 (d-c) (a-c) / det2 (b-a) (d-c)

def secondIntersectionParameter (a b c d : Plane) : ℝ :=
  -det2 (b-a) (c-a) / det2 (b-a) (d-c)

theorem intersection_parameters_eq (a b c d : Plane) (hn : det2 (b-a) (d-c) ≠ 0) :
    segmentPoint a b (firstIntersectionParameter a b c d) =
      segmentPoint c d (secondIntersectionParameter a b c d) := by
  apply Prod.ext
  · change (1-firstIntersectionParameter a b c d)*a.1+firstIntersectionParameter a b c d*b.1 =
      (1-secondIntersectionParameter a b c d)*c.1+secondIntersectionParameter a b c d*d.1
    unfold firstIntersectionParameter secondIntersectionParameter
    field_simp
    dsimp [det2]
    ring
  · change (1-firstIntersectionParameter a b c d)*a.2+firstIntersectionParameter a b c d*b.2 =
      (1-secondIntersectionParameter a b c d)*c.2+secondIntersectionParameter a b c d*d.2
    unfold firstIntersectionParameter secondIntersectionParameter
    field_simp
    dsimp [det2]
    ring

theorem segmentsCrossProperly_iff_parameters (a b c d : Plane) (hn : det2 (b-a) (d-c) ≠ 0) :
    SegmentsCrossProperly a b c d ↔
      firstIntersectionParameter a b c d ∈ Set.Ioo (0 : ℝ) 1 ∧
      secondIntersectionParameter a b c d ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · rintro ⟨_,t,ht,u,hu,he⟩
    have hh := segment_intersection_parameters_unique a b c d hn t u
      (firstIntersectionParameter a b c d) (secondIntersectionParameter a b c d)
      he (intersection_parameters_eq a b c d hn)
    exact ⟨hh.1 ▸ ht,hh.2 ▸ hu⟩
  · rintro ⟨ht,hu⟩
    exact ⟨hn,_,ht,_,hu,intersection_parameters_eq a b c d hn⟩

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.SegmentSides
namespace OAI

noncomputable section

namespace Zarankiewicz

def orient2 (a b c : Plane) : ℝ := det2 (b-a) (c-a)

theorem orient2_self_segment (a b : Plane) (t : ℝ) : orient2 a b (segmentPoint a b t) = 0 := by
  dsimp [orient2, det2, segmentPoint]
  ring

theorem orient2_segment (a b c d : Plane) (u : ℝ) :
    orient2 a b (segmentPoint c d u) = (1-u)*orient2 a b c+u*orient2 a b d := by
  dsimp [orient2,det2,segmentPoint]
  ring

theorem orient2_difference (a b c d : Plane) :
    orient2 a b d-orient2 a b c = det2 (b-a) (d-c) := by
  dsimp [orient2,det2]
  ring

theorem orient2_other_difference (a b c d : Plane) :
    orient2 c d a-orient2 c d b = det2 (b-a) (d-c) := by
  dsimp [orient2,det2]
  ring

theorem segmentCrossingSign_of_positive_sides (a b c d : Plane)
    (hc : orient2 a b c < 0) (hd : 0 < orient2 a b d)
    (ha : 0 < orient2 c d a) (hb : orient2 c d b < 0) :
    segmentCrossingSign a b c d = 1 := by
  have hdiff := orient2_difference a b c d
  have hother := orient2_other_difference a b c d
  have hdet : 0 < det2 (b-a) (d-c) := by linarith
  have hcros : SegmentsCrossProperly a b c d := by
    apply (segmentsCrossProperly_iff_parameters a b c d (ne_of_gt hdet)).mpr
    constructor
    · change 0 < orient2 c d a / det2 (b-a) (d-c) ∧ orient2 c d a / det2 (b-a) (d-c) < 1
      exact ⟨div_pos ha hdet, (div_lt_one hdet).mpr (by linarith)⟩
    · change 0 < -orient2 a b c / det2 (b-a) (d-c) ∧ -orient2 a b c / det2 (b-a) (d-c) < 1
      exact ⟨div_pos (neg_pos.mpr hc) hdet, (div_lt_one hdet).mpr (by linarith)⟩
  simp [segmentCrossingSign,hcros,hdet]

theorem not_segmentsCrossProperly_of_same_side (a b c d : Plane)
    (hside : (0 < orient2 a b c ∧ 0 < orient2 a b d) ∨
      (orient2 a b c < 0 ∧ orient2 a b d < 0)) : ¬ SegmentsCrossProperly a b c d := by
  rintro ⟨_,t,ht,u,hu,he⟩
  have hzero := congrArg (orient2 a b) he
  rw [orient2_self_segment,orient2_segment] at hzero
  have hpos : 0 < 1-u := by linarith [hu.2]
  rcases hside with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · have := add_pos (mul_pos hpos hc) (mul_pos hu.1 hd)
    linarith
  · have := add_neg (mul_neg_of_pos_of_neg hpos hc) (mul_neg_of_pos_of_neg hu.1 hd)
    linarith

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.SegmentContinuity
namespace OAI

noncomputable section

namespace Zarankiewicz

open scoped Topology Classical

def SegmentPairTransverse (a b c d : Plane) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
    segmentPoint a b t = segmentPoint c d u →
      det2 (b-a) (d-c) ≠ 0 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∈ Set.Ioo (0 : ℝ) 1

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.IntervalSegments
namespace OAI

namespace Zarankiewicz

def intervalSegment (a b t : unitInterval) : unitInterval :=
  ⟨(1-t.val)*a.val+t.val*b.val,by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
        (mul_nonneg t.property.1 b.property.1)
    · have h₀ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
      have h₁ := mul_le_mul_of_nonneg_left b.property.2 t.property.1
      linarith⟩

end Zarankiewicz

end OAI


-- OAI.Combinatorics.Crossing.PathSubarc
namespace OAI

noncomputable section

namespace Zarankiewicz

theorem intervalSegment_surjective_interval (a b : unitInterval) (hab : a < b)
    (t : unitInterval) (ht : a ≤ t ∧ t ≤ b) : ∃ u : unitInterval, intervalSegment a b u=t := by
  have hd : 0 < b.val-a.val := sub_pos.mpr hab
  have ht0 : 0 ≤ (t.val-a.val)/(b.val-a.val) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have ht1 : (t.val-a.val)/(b.val-a.val) ≤ 1 :=
    (div_le_one hd).mpr (sub_le_sub_right (show t.val ≤ b.val from ht.2) a.val)
  refine ⟨⟨(t.val-a.val)/(b.val-a.val),ht0,ht1⟩,?_⟩
  apply Subtype.ext
  change (1-(t.val-a.val)/(b.val-a.val))*a.val+((t.val-a.val)/(b.val-a.val))*b.val=t.val
  field_simp
  ring

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.IntervalSegmentStrict
namespace OAI

namespace Zarankiewicz

theorem intervalSegment_strict_between (a b t : unitInterval) (hab : a < b)
    (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    a < intervalSegment a b t ∧ intervalSegment a b t < b := by
  have hab' : a.val < b.val := hab
  have ht0 : 0 < t.val := ht.1
  have ht1 : t.val < 1 := ht.2
  have h₀ := mul_pos ht0 (sub_pos.mpr hab')
  have h₁ := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hab')
  change a.val < (1-t.val)*a.val+t.val*b.val ∧ (1-t.val)*a.val+t.val*b.val < b.val
  constructor <;> nlinarith

end Zarankiewicz

end OAI


-- OAI.Combinatorics.Crossing.AffinePathHalves
namespace OAI

noncomputable section

namespace Zarankiewicz

def intervalLeft (t : unitInterval) : unitInterval := ⟨t.val/2,by constructor <;> linarith [t.property.1,t.property.2]⟩

def intervalRight (t : unitInterval) : unitInterval := ⟨(1+t.val)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩

theorem intervalLeft_strictMono : StrictMono intervalLeft := by
  intro s t hst
  change s.val/2 < t.val/2
  exact div_lt_div_of_pos_right hst (by norm_num)

theorem intervalRight_strictMono : StrictMono intervalRight := by
  intro s t hst
  change (1+s.val)/2 < (1+t.val)/2
  have hh : s.val < t.val := hst
  linarith

theorem intervalSegment_left (a b t : unitInterval) :
    intervalSegment (intervalLeft a) (intervalLeft b) t=intervalLeft (intervalSegment a b t) := by
  apply Subtype.ext
  change (1-t.val)*(a.val/2)+t.val*(b.val/2)=((1-t.val)*a.val+t.val*b.val)/2
  ring

theorem intervalSegment_right (a b t : unitInterval) :
    intervalSegment (intervalRight a) (intervalRight b) t=intervalRight (intervalSegment a b t) := by
  apply Subtype.ext
  change (1-t.val)*((1+a.val)/2)+t.val*((1+b.val)/2)=(1+((1-t.val)*a.val+t.val*b.val))/2
  ring

theorem path_trans_intervalLeft {a b c : Plane} (γ : Path a b) (η : Path b c) (t : unitInterval) :
    (γ.trans η) (intervalLeft t)=γ t := by
  rw [← (γ.trans η).extend_extends' (intervalLeft t)]
  rw [Path.extend_trans_of_le_half γ η (show (intervalLeft t).val ≤ 1/2 by
    change t.val/2 ≤ 1/2
    linarith [t.property.2])]
  have he : 2*(intervalLeft t).val=t.val := by change 2*(t.val/2)=t.val; ring
  rw [he,γ.extend_extends']

theorem path_trans_intervalRight {a b c : Plane} (γ : Path a b) (η : Path b c) (t : unitInterval) :
    (γ.trans η) (intervalRight t)=η t := by
  rw [← (γ.trans η).extend_extends' (intervalRight t)]
  rw [Path.extend_trans_of_half_le γ η (show 1/2 ≤ (intervalRight t).val by
    change 1/2 ≤ (1+t.val)/2
    linarith [t.property.1])]
  have he : 2*(intervalRight t).val-1=t.val := by change 2*((1+t.val)/2)-1=t.val; ring
  rw [he,η.extend_extends']

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.FiniteAffineCover
namespace OAI

noncomputable section

namespace Zarankiewicz

def HasFiniteAffineCover {a b : Plane} (γ : Path a b) : Prop :=
  ∃ S : Finset (unitInterval × unitInterval),
    (∀ ab ∈ S, ab.1 < ab.2) ∧
    (∀ t : unitInterval, ∃ ab ∈ S, ab.1 ≤ t ∧ t ≤ ab.2) ∧
    (∀ ab ∈ S, ∀ t : unitInterval,
      γ (intervalSegment ab.1 ab.2 t)=segmentPoint (γ ab.1) (γ ab.2) t.val)

theorem HasFiniteAffineCover.trans {a b c : Plane} {γ : Path a b} {η : Path b c}
    (hγ : HasFiniteAffineCover γ) (hη : HasFiniteAffineCover η) : HasFiniteAffineCover (γ.trans η) := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  obtain ⟨T,hTlt,hTcov,hTaff⟩ := hη
  let L : unitInterval × unitInterval → unitInterval × unitInterval := fun ab => (intervalLeft ab.1,intervalLeft ab.2)
  let R : unitInterval × unitInterval → unitInterval × unitInterval := fun ab => (intervalRight ab.1,intervalRight ab.2)
  refine ⟨S.image L ∪ T.image R,?_,?_,?_⟩
  · intro ab hab
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalLeft_strictMono (hSlt cd hcd)
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalRight_strictMono (hTlt cd hcd)
  · intro t
    by_cases ht : t.val ≤ 1/2
    · let u : unitInterval := ⟨2*t.val,by constructor <;> linarith [t.property.1]⟩
      obtain ⟨ab,hab,ha,hb⟩ := hScov u
      have hu : intervalLeft u=t := by apply Subtype.ext; change (2*t.val)/2=t.val; ring
      refine ⟨L ab,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩),?_,?_⟩
      · change intervalLeft ab.1 ≤ t
        rw [← hu]
        exact intervalLeft_strictMono.monotone ha
      · change t ≤ intervalLeft ab.2
        rw [← hu]
        exact intervalLeft_strictMono.monotone hb
    · let u : unitInterval := ⟨2*t.val-1,by constructor <;> linarith [t.property.2]⟩
      obtain ⟨ab,hab,ha,hb⟩ := hTcov u
      have hu : intervalRight u=t := by apply Subtype.ext; change (1+(2*t.val-1))/2=t.val; ring
      refine ⟨R ab,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩),?_,?_⟩
      · change intervalRight ab.1 ≤ t
        rw [← hu]
        exact intervalRight_strictMono.monotone ha
      · change t ≤ intervalRight ab.2
        rw [← hu]
        exact intervalRight_strictMono.monotone hb
  · intro ab hab t
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      change (γ.trans η) (intervalSegment (intervalLeft cd.1) (intervalLeft cd.2) t)=_
      rw [intervalSegment_left,path_trans_intervalLeft]
      exact (hSaff cd hcd t).trans (by simp only [L,path_trans_intervalLeft])
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      change (γ.trans η) (intervalSegment (intervalRight cd.1) (intervalRight cd.2) t)=_
      rw [intervalSegment_right,path_trans_intervalRight]
      exact (hTaff cd hcd t).trans (by simp only [R,path_trans_intervalRight])

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.AffineIntervalRestriction
namespace OAI

noncomputable section

namespace Zarankiewicz

theorem intervalSegment_interpolate (a b u v t : unitInterval) :
    intervalSegment (intervalSegment a b u) (intervalSegment a b v) t=
      intervalSegment a b (intervalSegment u v t) := by
  apply Subtype.ext
  dsimp [intervalSegment]
  ring

theorem segmentPoint_interpolate (a b : Plane) (u v t : ℝ) :
    segmentPoint (segmentPoint a b u) (segmentPoint a b v) t=
      segmentPoint a b ((1-t)*u+t*v) := by
  ext <;> dsimp [segmentPoint] <;> ring

theorem path_affine_restrict {a b : Plane} (γ : Path a b) (l r : unitInterval) (hlr : l < r)
    (haff : ∀ t : unitInterval, γ (intervalSegment l r t)=segmentPoint (γ l) (γ r) t.val)
    (u v : unitInterval) (hu : l ≤ u ∧ u ≤ r) (hv : l ≤ v ∧ v ≤ r) (t : unitInterval) :
    γ (intervalSegment u v t)=segmentPoint (γ u) (γ v) t.val := by
  obtain ⟨u',rfl⟩ := intervalSegment_surjective_interval l r hlr u hu
  obtain ⟨v',rfl⟩ := intervalSegment_surjective_interval l r hlr v hv
  rw [intervalSegment_interpolate,haff,haff,haff,segmentPoint_interpolate]
  rfl

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.SortedMarkedParameters
namespace OAI

noncomputable section

namespace Zarankiewicz

theorem exists_sorted_unitInterval_finset (S : Finset unitInterval)
    (h0 : (0 : unitInterval) ∈ S) (h1 : (1 : unitInterval) ∈ S) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧ Set.range t=(S : Set unitInterval) := by
  have hc : 1 < S.card := Finset.one_lt_card.mpr ⟨0,h0,1,h1,zero_ne_one⟩
  let k := S.card-1
  have hk : 0 < k := by dsimp [k]; omega
  have hcard : S.card=k+1 := by dsimp [k]; omega
  let e := S.orderEmbOfFin hcard
  have hrange : Set.range e=(S : Set unitInterval) := Finset.range_orderEmbOfFin S hcard
  obtain ⟨i,hi⟩ : ∃ i, e i=0 := by
    have hm : (0 : unitInterval) ∈ Set.range e := hrange.symm ▸ h0
    exact hm
  obtain ⟨j,hj⟩ : ∃ j, e j=1 := by
    have hm : (1 : unitInterval) ∈ Set.range e := hrange.symm ▸ h1
    exact hm
  have he0 : e 0=0 := by
    apply le_antisymm
    · exact (e.monotone (Fin.zero_le i)).trans_eq hi
    · exact (e 0).property.1
  have he1 : e (Fin.last k)=1 := by
    apply le_antisymm
    · exact (e (Fin.last k)).property.2
    · exact hj.symm.trans_le (e.monotone (Fin.le_last j))
  exact ⟨k,hk,e,e.strictMono,he0,he1,hrange⟩

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.OffsetVectors
namespace OAI

noncomputable section

namespace Zarankiewicz

def rotateQuarter (v : Plane) : Plane := (-v.2,v.1)

def squaredLength (v : Plane) : ℝ := v.1^2+v.2^2

theorem squaredLength_pos (v : Plane) (hv : v ≠ 0) : 0 < squaredLength v := by
  have hx := sq_nonneg v.1
  have hy := sq_nonneg v.2
  have hnon : 0 ≤ squaredLength v := by dsimp [squaredLength]; linarith
  rcases eq_or_lt_of_le hnon with hzero | hpos
  · have h₁ : v.1=0 := by dsimp [squaredLength] at hzero; nlinarith
    have h₂ : v.2=0 := by dsimp [squaredLength] at hzero; nlinarith
    exact False.elim (hv (Prod.ext h₁ h₂))
  · exact hpos

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.ParallelDirection
namespace OAI

noncomputable section

namespace Zarankiewicz

open scoped Topology

def dot2 (u v : Plane) : ℝ := u.1*v.1+u.2*v.2

theorem planar_vector_decomposition (u v : Plane) :
    squaredLength u • v = dot2 u v • u+det2 u v • rotateQuarter u := by
  apply Prod.ext <;> dsimp [squaredLength,dot2,det2,rotateQuarter] <;> ring

theorem vector_parallel_of_det_zero (u v : Plane) (hu : u ≠ 0) (h : det2 u v=0) :
    v = (dot2 u v/squaredLength u) • u := by
  have hs := ne_of_gt (squaredLength_pos u hu)
  have hh := planar_vector_decomposition u v
  rw [h,zero_smul,add_zero] at hh
  calc
    v = (squaredLength u)⁻¹ • (squaredLength u • v) := by rw [smul_smul,inv_mul_cancel₀ hs,one_smul]
    _ = (squaredLength u)⁻¹ • (dot2 u v • u) := by rw [hh]
    _ = _ := by rw [smul_smul,div_eq_mul_inv,mul_comm]

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.PolygonalParametrization
namespace OAI

noncomputable section

namespace Zarankiewicz

structure PolygonalParametrization {a b : Plane} (γ : Path a b) where
  pieces : ℕ
  knot : Fin (pieces+1) → unitInterval
  increasing : StrictMono knot
  first : knot 0=0
  last : knot (Fin.last pieces)=1
  affine : ∀ i : Fin pieces, ∀ t : unitInterval,
    γ (intervalSegment (knot i.castSucc) (knot i.succ) t) =
      segmentPoint (γ (knot i.castSucc)) (γ (knot i.succ)) t.val

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.OrderedAffineSubdivision
namespace OAI

noncomputable section

namespace Zarankiewicz

theorem strictMono_no_between_successors {k : ℕ} (t : Fin (k+1) → unitInterval)
    (ht : StrictMono t) (i : Fin k) (j : Fin (k+1)) :
    ¬ (t i.castSucc < t j ∧ t j < t i.succ) := by
  intro h
  have hlo : i.castSucc < j := by
    by_contra hn
    exact h.1.not_ge (ht.monotone (le_of_not_gt hn))
  have hhi : j < i.succ := by
    by_contra hn
    exact h.2.not_ge (ht.monotone (le_of_not_gt hn))
  change i.val < j.val at hlo
  change j.val < i.val+1 at hhi
  omega

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.CompleteCrossing.Plane
namespace OAI

section

noncomputable section

open Set

open scoped BigOperators Classical

namespace Paper170

theorem segmentPoint_eq (a b : Plane) (t : ℝ) :
    segmentPoint a b t = Zarankiewicz.segmentPoint a b t := rfl

theorem squaredLength_pos {x : Plane} (hx : x ≠ 0) : 0 < squaredLength x := by
  have h0 : 0 ≤ x.1^2 := sq_nonneg x.1
  have h1 : 0 ≤ x.2^2 := sq_nonneg x.2
  change 0 < x.1^2 + x.2^2
  by_contra hh
  have ha : x.1 = 0 := by nlinarith
  have hb : x.2 = 0 := by nlinarith
  exact hx (Prod.ext ha hb)

theorem inversion_involutive : Function.Involutive inversion := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [inversion, squaredLength]
  · have hq : squaredLength x ≠ 0 := ne_of_gt (squaredLength_pos hx)
    have hlen : squaredLength (inversion x) = (squaredLength x)⁻¹ := by
      change (x.1 / squaredLength x)^2 + (x.2 / squaredLength x)^2 = _
      rw [div_pow, div_pow, ← add_div]
      change squaredLength x / squaredLength x ^ 2 = (squaredLength x)⁻¹
      field_simp [hq]
    rw [inversion, hlen]
    apply Prod.ext <;> simp [inversion, hq]

theorem inversion_fixes_circle (x : Plane) (hx : squaredLength x = 1) : inversion x = x := by
  simp [inversion, hx]

end Paper170

end

end

end OAI


-- OAI.Combinatorics.Crossing.CircleChords
namespace OAI

noncomputable section

namespace Zarankiewicz

def circlePoint (t : ℝ) : Plane := ((1-t^2)/(1+t^2), 2*t/(1+t^2))

theorem circle_denominator_pos (t : ℝ) : 0 < 1+t^2 := by nlinarith [sq_nonneg t]

theorem circlePoint_on_unit_circle (t : ℝ) : (circlePoint t).1^2+(circlePoint t).2^2 = 1 := by
  have h := ne_of_gt (circle_denominator_pos t)
  dsimp [circlePoint]
  field_simp
  ring

theorem circlePoint_parameter (t : ℝ) : (circlePoint t).2/(1+(circlePoint t).1) = t := by
  have h := ne_of_gt (circle_denominator_pos t)
  have hden : 1+(circlePoint t).1 = 2/(1+t^2) := by
    dsimp [circlePoint]
    field_simp
    ring
  rw [hden]
  dsimp [circlePoint]
  field_simp

theorem circlePoint_injective : Function.Injective circlePoint := by
  intro a b hab
  have hh := congrArg (fun z : Plane => z.2/(1+z.1)) hab
  simpa only [circlePoint_parameter] using hh

theorem circle_orient_formula (a b c : ℝ) :
    orient2 (circlePoint a) (circlePoint b) (circlePoint c) =
      4*(b-a)*(c-a)*(c-b)/((1+a^2)*(1+b^2)*(1+c^2)) := by
  have ha := ne_of_gt (circle_denominator_pos a)
  have hb := ne_of_gt (circle_denominator_pos b)
  have hc := ne_of_gt (circle_denominator_pos c)
  dsimp [orient2,det2,circlePoint]
  field_simp
  ring

theorem circle_orient_pos (a b c : ℝ) (hab : a<b) (hbc : b<c) :
    0 < orient2 (circlePoint a) (circlePoint b) (circlePoint c) := by
  rw [circle_orient_formula]
  exact div_pos
    (mul_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hab))
      (sub_pos.mpr (hab.trans hbc))) (sub_pos.mpr hbc))
    (mul_pos (mul_pos (circle_denominator_pos a) (circle_denominator_pos b)) (circle_denominator_pos c))

theorem orient2_cycle (a b c : Plane) : orient2 b c a = orient2 a b c := by
  dsimp [orient2,det2]
  ring

theorem orient2_swap_ends (a b c : Plane) : orient2 a c b = -orient2 a b c := by
  exact det2_swap (b-a) (c-a)

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.ProperCrossingLocality
namespace OAI

noncomputable section

namespace Zarankiewicz

theorem chart_image_mem_iff (e : OpenPartialHomeomorph Plane Plane) (A L : Set Plane)
    (h : e '' (e.source ∩ A)=e.target ∩ L) (x : Plane) (hx : x ∈ e.source) :
    x ∈ A ↔ e x ∈ L := by
  constructor
  · intro ha
    have hh : e x ∈ e '' (e.source ∩ A) := ⟨x,⟨hx,ha⟩,rfl⟩
    rw [h] at hh
    exact hh.2
  · intro hl
    have hh : e x ∈ e '' (e.source ∩ A) := h.symm ▸ ⟨e.map_source hx,hl⟩
    obtain ⟨y,hy,he⟩ := hh
    have hyx : y=x := e.injOn hy.1 hx he
    exact hyx ▸ hy.2

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.CrossingCoordinates
namespace OAI

noncomputable section

namespace Zarankiewicz

def crossingCoordinates (o u v x : Plane) : Plane :=
  (det2 (x-o) v/det2 u v,det2 u (x-o)/det2 u v)

def crossingCoordinateInverse (o u v s : Plane) : Plane := o+s.1 • u+s.2 • v

theorem crossingCoordinates_left_inverse (o u v : Plane) (h : det2 u v ≠ 0) (x : Plane) :
    crossingCoordinateInverse o u v (crossingCoordinates o u v x)=x := by
  have hc := mul_inv_cancel₀ h
  apply Prod.ext
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination (x.1-o.1)*hc
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination (x.2-o.2)*hc

theorem crossingCoordinates_right_inverse (o u v : Plane) (h : det2 u v ≠ 0) (s : Plane) :
    crossingCoordinates o u v (crossingCoordinateInverse o u v s)=s := by
  have hc := mul_inv_cancel₀ h
  apply Prod.ext
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination s.1*hc
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination s.2*hc

theorem crossingCoordinates_continuous (o u v : Plane) : Continuous (crossingCoordinates o u v) := by
  unfold crossingCoordinates det2
  fun_prop

theorem crossingCoordinateInverse_continuous (o u v : Plane) : Continuous (crossingCoordinateInverse o u v) := by
  unfold crossingCoordinateInverse
  fun_prop

def crossingCoordinateChart (o u v : Plane) (h : det2 u v ≠ 0)
    (U : Set Plane) (hU : IsOpen U) : OpenPartialHomeomorph Plane Plane where
  toFun := crossingCoordinates o u v
  invFun := crossingCoordinateInverse o u v
  source := crossingCoordinates o u v ⁻¹' U
  target := U
  map_source' := fun {_} hx => hx
  map_target' := fun {s} hs => by
    change crossingCoordinates o u v (crossingCoordinateInverse o u v s) ∈ U
    rw [crossingCoordinates_right_inverse o u v h]
    exact hs
  left_inv' := fun {x} _ => crossingCoordinates_left_inverse o u v h x
  right_inv' := fun {s} _ => crossingCoordinates_right_inverse o u v h s
  continuousOn_toFun := (crossingCoordinates_continuous o u v).continuousOn
  continuousOn_invFun := (crossingCoordinateInverse_continuous o u v).continuousOn
  open_source := hU.preimage (crossingCoordinates_continuous o u v)
  open_target := hU

@[simp] theorem crossingCoordinates_origin (o u v : Plane) : crossingCoordinates o u v o=(0,0) := by
  simp [crossingCoordinates, det2]

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.SegmentCrossingCoordinates
namespace OAI

namespace Zarankiewicz

theorem inverseCoordinates_first_segment (a b c d o : Plane) (t s : ℝ)
    (ho : o=segmentPoint a b t) :
    crossingCoordinateInverse o (b-a) (d-c) (s-t,0)=segmentPoint a b s := by
  rw [ho]
  apply Prod.ext <;> dsimp [crossingCoordinateInverse,segmentPoint] <;> ring

theorem inverseCoordinates_second_segment (a b c d o : Plane) (t s : ℝ)
    (ho : o=segmentPoint c d t) :
    crossingCoordinateInverse o (b-a) (d-c) (0,s-t)=segmentPoint c d s := by
  rw [ho]
  apply Prod.ext <;> dsimp [crossingCoordinateInverse,segmentPoint] <;> ring

theorem crossingCoordinates_first_segment (a b c d o : Plane) (t s : ℝ)
    (hd : det2 (b-a) (d-c) ≠ 0) (ho : o=segmentPoint a b t) :
    crossingCoordinates o (b-a) (d-c) (segmentPoint a b s)=(s-t,0) := by
  rw [← inverseCoordinates_first_segment a b c d o t s ho]
  exact crossingCoordinates_right_inverse o (b-a) (d-c) hd _

theorem crossingCoordinates_second_segment (a b c d o : Plane) (t s : ℝ)
    (hd : det2 (b-a) (d-c) ≠ 0) (ho : o=segmentPoint c d t) :
    crossingCoordinates o (b-a) (d-c) (segmentPoint c d s)=(0,s-t) := by
  rw [← inverseCoordinates_second_segment a b c d o t s ho]
  exact crossingCoordinates_right_inverse o (b-a) (d-c) hd _

end Zarankiewicz

end OAI


-- OAI.Combinatorics.Crossing.ProperSegmentCrossing
namespace OAI

noncomputable section

namespace Zarankiewicz

theorem properCrossing_openSegments (a b c d x : Plane) (hd : det2 (b-a) (d-c) ≠ 0)
    (hx : x ∈ openSegmentTrace a b) (hy : x ∈ openSegmentTrace c d) :
    ProperCrossing (openSegmentTrace a b) (openSegmentTrace c d) x := by
  obtain ⟨t,ht,hxt⟩ := hx
  obtain ⟨u,hu,hxu⟩ := hy
  let U : Set Plane := Set.Ioo (-t) (1-t) ×ˢ Set.Ioo (-u) (1-u)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  let chart := crossingCoordinateChart x (b-a) (d-c) hd U hU
  have hzero : (0,0) ∈ U := ⟨⟨by linarith [ht.1],by linarith [ht.2]⟩,
    ⟨by linarith [hu.1],by linarith [hu.2]⟩⟩
  have hsource : x ∈ chart.source := by
    change crossingCoordinates x (b-a) (d-c) x ∈ U
    rw [crossingCoordinates_origin]
    exact hzero
  refine ⟨chart,hsource,crossingCoordinates_origin x (b-a) (d-c),?_,?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      refine ⟨chart.map_source hz.1,?_⟩
      obtain ⟨s,hs,he⟩ := hz.2
      rw [← he]
      change (crossingCoordinates x (b-a) (d-c) (segmentPoint a b s)).2=0
      rw [crossingCoordinates_first_segment a b c d x t s hd hxt.symm]
    · rintro y ⟨hy,hy0⟩
      have hs : t+y.1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1.1],by linarith [hy.1.2]⟩
      have he : chart (segmentPoint a b (t+y.1))=y := by
        change crossingCoordinates x (b-a) (d-c) (segmentPoint a b (t+y.1))=y
        rw [crossingCoordinates_first_segment a b c d x t (t+y.1) hd hxt.symm]
        apply Prod.ext
        · dsimp
          ring
        · exact hy0.symm
      refine ⟨segmentPoint a b (t+y.1),⟨?_,⟨t+y.1,hs,rfl⟩⟩,he⟩
      change chart (segmentPoint a b (t+y.1)) ∈ U
      rw [he]
      exact hy
  · apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      refine ⟨chart.map_source hz.1,?_⟩
      obtain ⟨s,hs,he⟩ := hz.2
      rw [← he]
      change (crossingCoordinates x (b-a) (d-c) (segmentPoint c d s)).1=0
      rw [crossingCoordinates_second_segment a b c d x u s hd hxu.symm]
    · rintro y ⟨hy,hy0⟩
      have hs : u+y.2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hy.2.1],by linarith [hy.2.2]⟩
      have he : chart (segmentPoint c d (u+y.2))=y := by
        change crossingCoordinates x (b-a) (d-c) (segmentPoint c d (u+y.2))=y
        rw [crossingCoordinates_second_segment a b c d x u (u+y.2) hd hxu.symm]
        apply Prod.ext
        · exact hy0.symm
        · dsimp
          ring
      refine ⟨segmentPoint c d (u+y.2),⟨?_,⟨u+y.2,hs,rfl⟩⟩,he⟩
      change chart (segmentPoint c d (u+y.2)) ∈ U
      rw [he]
      exact hy

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.RadialExterior
namespace OAI

noncomputable section

namespace Zarankiewicz

theorem squaredLength_add_smul (u v : Plane) (t : ℝ) :
    squaredLength (u+t • v)=squaredLength u+2*t*dot2 u v+t^2*squaredLength v := by
  dsimp [squaredLength,dot2]
  ring

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.ChordTransversality
namespace OAI

noncomputable section

namespace Zarankiewicz

theorem segmentPairTransverse_of_noncollinear_endpoints (a b c d : Plane)
    (ha : orient2 c d a ≠ 0) (hb : orient2 c d b ≠ 0)
    (hc : orient2 a b c ≠ 0) (hd : orient2 a b d ≠ 0) :
    SegmentPairTransverse a b c d := by
  intro t ht u hu he
  have hdet : det2 (b-a) (d-c) ≠ 0 := by
    intro hz
    have hdiff := orient2_difference a b c d
    have heq : orient2 a b c=orient2 a b d := by linarith
    have hh := congrArg (orient2 a b) he
    rw [orient2_self_segment,orient2_segment,← heq] at hh
    apply hc
    nlinarith
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    rw [segmentPoint_zero] at he
    exact ha (by rw [he,orient2_self_segment])
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    rw [segmentPoint_one] at he
    exact hb (by rw [he,orient2_self_segment])
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    rw [segmentPoint_zero] at he
    exact hc (by rw [← he,orient2_self_segment])
  have hu1 : u ≠ 1 := by
    intro h
    subst u
    rw [segmentPoint_one] at he
    exact hd (by rw [← he,orient2_self_segment])
  exact ⟨hdet,⟨lt_of_le_of_ne ht.1 ht0.symm,lt_of_le_of_ne ht.2 ht1⟩,
    ⟨lt_of_le_of_ne hu.1 hu0.symm,lt_of_le_of_ne hu.2 hu1⟩⟩

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.RoundCircleChords
namespace OAI

noncomputable section

namespace Zarankiewicz

theorem round_circle_line_two_points (z a b c : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hab : a ≠ b)
    (hd : det2 (b-a) (c-a)=0) : c=a ∨ c=b := by
  have hlen := squaredLength_pos (b-a) (sub_ne_zero.mpr (Ne.symm hab))
  let t := dot2 (b-a) (c-a)/squaredLength (b-a)
  have hp : c-a=t • (b-a) := vector_parallel_of_det_zero (b-a) (c-a)
    (sub_ne_zero.mpr (Ne.symm hab)) hd
  have hba : (a-z)+(b-a)=b-z := by abel
  have hca : c-z=(a-z)+t • (b-a) := by rw [← hp]; abel
  have h₁ := squaredLength_add_smul (a-z) (b-a) 1
  simp only [one_smul,hba,ha,hb,one_pow,one_mul] at h₁
  rw [hca,squaredLength_add_smul,ha] at hc
  have hh : t*(t-1)*squaredLength (b-a)=0 := by linear_combination hc+t*h₁
  have ht := (mul_eq_zero.mp hh).resolve_right (ne_of_gt hlen)
  rcases mul_eq_zero.mp ht with ht | ht
  · left
    rw [ht,zero_smul] at hp
    exact sub_eq_zero.mp hp
  · right
    have ht1 : t=1 := sub_eq_zero.mp ht
    rw [ht1,one_smul] at hp
    exact sub_left_injective hp

theorem round_circle_orient_ne_zero (z a b c : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient2 a b c ≠ 0 := by
  intro hd
  exact (round_circle_line_two_points z a b c r ha hb hc hab hd).elim
    (fun h => hac h.symm) (fun h => hbc h.symm)

theorem round_circle_chords_transverse (z a b c d : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hd : squaredLength (d-z)=r^2)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    SegmentPairTransverse a b c d := by
  exact segmentPairTransverse_of_noncollinear_endpoints a b c d
    (round_circle_orient_ne_zero z c d a r hc hd ha hcd hac.symm had.symm)
    (round_circle_orient_ne_zero z c d b r hc hd hb hcd hbc.symm hbd.symm)
    (round_circle_orient_ne_zero z a b c r ha hb hc hab hac hbc)
    (round_circle_orient_ne_zero z a b d r ha hb hd hab had hbd)

theorem round_chord_in_open_disk (z a b : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hab : a ≠ b) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    squaredLength (segmentPoint a b t-z) < r^2 := by
  have he : squaredLength (segmentPoint a b t-z)=
      (1-t)*squaredLength (a-z)+t*squaredLength (b-z)-t*(1-t)*squaredLength (b-a) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hp := mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2))
    (squaredLength_pos (b-a) (sub_ne_zero.mpr hab.symm))
  rw [he,ha,hb]
  linarith

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.CompleteCrossing.CircleArcs
namespace OAI

section

noncomputable section

open Set

open scoped Classical

namespace Paper170

def chordInterior {n : ℕ} (p : Fin n → Plane) (e : CompleteEdge n) : Set Plane :=
  (segmentPoint (p e.val.1) (p e.val.2)) '' Ioo (0 : ℝ) 1

structure CircleConfiguration (n : ℕ) where
  point : Fin n → Plane
  injective : Function.Injective point
  on_circle : ∀ i, squaredLength (point i) = 1
  cyclic_order : ∀ i j k, i < j → j < k →
    0 < det2 (point j - point i) (point k - point i)
  no_antipodal : ∀ i j, i ≠ j → point i + point j ≠ 0
  no_triple_chords : ∀ e f g : CompleteEdge n, e ≠ f → e ≠ g → f ≠ g →
    chordInterior point e ∩ chordInterior point f ∩ chordInterior point g = ∅

def twoPageRoute {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n)
    (t : unitInterval) : Plane :=
  let x := segmentPoint (C.point e.val.1) (C.point e.val.2) t.val
  if residueColor n (e.val.1.val + e.val.2.val) then x else inversion x

structure TwoPageDrawing {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) : Prop where
  vertex_eq : D.vertex = C.point
  edge_eq : ∀ e t, D.edge e t = twoPageRoute C e t

def lineIntersectionPoint (a b c d : Plane) : Plane :=
  a + (det2 (c - a) (d - c) / det2 (b - a) (d - c)) • (b - a)

def crossingTuplePoint {n : ℕ} (C : CircleConfiguration n) (v : Fin 4 → Fin n) : Plane :=
  let x := lineIntersectionPoint (C.point (v 0)) (C.point (v 2))
    (C.point (v 1)) (C.point (v 3))
  if residueColor n ((v 0).val + (v 2).val) then x else inversion x

end Paper170

end

end

section

noncomputable section

open Set

namespace Paper170

theorem chordInterior_eq_unitIntervalImage {n : ℕ} (p : Fin n → Plane) (e : CompleteEdge n) :
    chordInterior p e =
      (fun t : unitInterval => segmentPoint (p e.val.1) (p e.val.2) t.val) ''
        Ioo (0 : unitInterval) 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht.1.le, ht.2.le⟩, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.val, ht, rfl⟩

theorem twoPageRoute_image {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    twoPageRoute C e '' Ioo (0 : unitInterval) 1 =
      if residueColor n (e.val.1.val + e.val.2.val) then chordInterior C.point e
      else inversion '' chordInterior C.point e := by
  change (fun t => twoPageRoute C e t) '' _ = _
  cases hc : residueColor n (e.val.1.val + e.val.2.val) <;>
    simp [twoPageRoute, hc, chordInterior_eq_unitIntervalImage, Set.image_image]

theorem twoPage_edgeInterior {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e : CompleteEdge n) :
    edgeInterior D.toContinuousDrawing e =
      if residueColor n (e.val.1.val + e.val.2.val) then chordInterior C.point e
      else inversion '' chordInterior C.point e := by
  change (D.edge e : unitInterval → Plane) '' _ = _
  rw [show (D.edge e : unitInterval → Plane) = twoPageRoute C e from funext (hD.edge_eq e)]
  exact twoPageRoute_image C e

end Paper170

end

end

section

noncomputable section

open Set

open scoped Classical

namespace Paper170

theorem circle_points_noncollinear {n : ℕ} (p : Fin n → Plane)
    (hp : Function.Injective p) (hc : ∀ i, squaredLength (p i) = 1)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Zarankiewicz.orient2 (p i) (p j) (p k) ≠ 0 := by
  apply Zarankiewicz.round_circle_orient_ne_zero 0 (p i) (p j) (p k) 1
  · simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using hc i
  · simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using hc j
  · simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using hc k
  · exact hp.ne hij
  · exact hp.ne hik
  · exact hp.ne hjk

theorem open_chord_reverse {a b x : Plane} (hx : x ∈ Zarankiewicz.openSegmentTrace a b) :
    x ∈ Zarankiewicz.openSegmentTrace b a := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    Zarankiewicz.segmentPoint_reverse a b t⟩

theorem open_chords_common_start {a b c x : Plane}
    (hn : Zarankiewicz.orient2 a b c ≠ 0)
    (hx : x ∈ Zarankiewicz.openSegmentTrace a b)
    (hy : x ∈ Zarankiewicz.openSegmentTrace a c) : False := by
  obtain ⟨t, ht, he⟩ := hx
  obtain ⟨u, hu, hf⟩ := hy
  have hz := congrArg (Zarankiewicz.orient2 a b) (he.trans hf.symm)
  rw [Zarankiewicz.orient2_self_segment, Zarankiewicz.orient2_segment] at hz
  have ha : Zarankiewicz.orient2 a b a = 0 := by simp [Zarankiewicz.orient2, Zarankiewicz.det2]
  rw [ha, mul_zero, zero_add] at hz
  exact hn ((mul_eq_zero.mp hz.symm).resolve_left (ne_of_gt hu.1))

theorem circle_chord_endpoints_distinct {n : ℕ} (p : Fin n → Plane)
    (hp : Function.Injective p) (hc : ∀ i, squaredLength (p i) = 1)
    (e f : CompleteEdge n) (hef : e ≠ f) (x : Plane)
    (he : x ∈ chordInterior p e) (hf : x ∈ chordInterior p f) :
    e.val.1 ≠ f.val.1 ∧ e.val.1 ≠ f.val.2 ∧ e.val.2 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2 := by
  have he' : x ∈ Zarankiewicz.openSegmentTrace (p e.val.1) (p e.val.2) := he
  have hf' : x ∈ Zarankiewicz.openSegmentTrace (p f.val.1) (p f.val.2) := hf
  have hei : e.val.1 < e.val.2 := e.property
  have hfi : f.val.1 < f.val.2 := f.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hother : e.val.2 ≠ f.val.2 := by
      intro hh
      exact hef (Subtype.ext (Prod.ext h hh))
    have hn := circle_points_noncollinear p hp hc (ne_of_lt hei)
      (show e.val.1 ≠ f.val.2 by rw [h]; exact ne_of_lt hfi) hother
    rw [← h] at hf'
    exact open_chords_common_start hn he' hf'
  · intro h
    have hn := circle_points_noncollinear p hp hc (ne_of_lt hei)
      (show e.val.1 ≠ f.val.1 by rw [h]; exact ne_of_gt hfi) (by omega)
    have hf'' := open_chord_reverse hf'
    rw [← h] at hf''
    exact open_chords_common_start hn he' hf''
  · intro h
    have hn := circle_points_noncollinear p hp hc (ne_of_gt hei)
      (show e.val.2 ≠ f.val.2 by rw [h]; exact ne_of_lt hfi) (by omega)
    have he'' := open_chord_reverse he'
    rw [← h] at hf'
    exact open_chords_common_start hn he'' hf'
  · intro h
    have hother : e.val.1 ≠ f.val.1 := by
      intro hh
      exact hef (Subtype.ext (Prod.ext hh h))
    have hn := circle_points_noncollinear p hp hc (ne_of_gt hei)
      (show e.val.2 ≠ f.val.1 by rw [h]; exact ne_of_gt hfi) hother
    have he'' := open_chord_reverse he'
    have hf'' := open_chord_reverse hf'
    rw [← h] at hf''
    exact open_chords_common_start hn he'' hf''

end Paper170

end

end

section

noncomputable section

open Set

open scoped Classical

namespace Paper170

theorem CircleConfiguration.orient_inside {n : ℕ} (C : CircleConfiguration n)
    {i j k : Fin n} (hik : i < k) (hkj : k < j) :
    Zarankiewicz.orient2 (C.point i) (C.point j) (C.point k) < 0 := by
  rw [Zarankiewicz.orient2_swap_ends]
  exact neg_neg_of_pos (C.cyclic_order i k j hik hkj)

theorem CircleConfiguration.orient_outside {n : ℕ} (C : CircleConfiguration n)
    {i j k : Fin n} (hij : i < j) (hk : k < i ∨ j < k) :
    0 < Zarankiewicz.orient2 (C.point i) (C.point j) (C.point k) := by
  rcases hk with hk | hk
  · rw [Zarankiewicz.orient2_cycle (C.point k) (C.point i) (C.point j)]
    exact C.cyclic_order k i j hk hij
  · exact C.cyclic_order i j k hij hk

theorem CircleConfiguration.alternating_cross {n : ℕ} (C : CircleConfiguration n)
    {i k j l : Fin n} (hik : i < k) (hkj : k < j) (hjl : j < l) :
    Zarankiewicz.SegmentsCrossProperly (C.point i) (C.point j) (C.point k) (C.point l) := by
  have hsign := Zarankiewicz.segmentCrossingSign_of_positive_sides
    (C.point i) (C.point j) (C.point k) (C.point l)
    (C.orient_inside hik hkj) (C.orient_outside (hik.trans hkj) (Or.inr hjl))
    (C.orient_outside (hkj.trans hjl) (Or.inl hik)) (C.orient_inside hkj hjl)
  by_contra h
  simp [Zarankiewicz.segmentCrossingSign, h] at hsign

theorem lineIntersectionPoint_eq_parameter (a b c d : Plane) :
    lineIntersectionPoint a b c d =
      Zarankiewicz.segmentPoint a b (Zarankiewicz.firstIntersectionParameter a b c d) := by
  have hnum : det2 (c - a) (d - c) = Zarankiewicz.det2 (d - c) (a - c) := by
    dsimp [det2, Zarankiewicz.det2]
    ring
  unfold lineIntersectionPoint
  rw [hnum]
  change a + Zarankiewicz.firstIntersectionParameter a b c d • (b - a) = _
  ext <;> simp [Zarankiewicz.segmentPoint] <;> ring

theorem open_chords_intersection_singleton (a b c d : Plane)
    (h : Zarankiewicz.SegmentsCrossProperly a b c d) :
    Zarankiewicz.openSegmentTrace a b ∩ Zarankiewicz.openSegmentTrace c d =
      {lineIntersectionPoint a b c d} := by
  have ht := (Zarankiewicz.segmentsCrossProperly_iff_parameters a b c d h.1).mp h
  have hp : lineIntersectionPoint a b c d ∈
      Zarankiewicz.openSegmentTrace a b ∩ Zarankiewicz.openSegmentTrace c d := by
    rw [lineIntersectionPoint_eq_parameter]
    exact ⟨⟨_, ht.1, rfl⟩, ⟨_, ht.2, (Zarankiewicz.intersection_parameters_eq a b c d h.1).symm⟩⟩
  ext x
  constructor
  · intro hx
    exact (Zarankiewicz.openSegment_intersection_subsingleton a b c d h.1 hx hp)
  · rintro rfl
    exact hp

theorem circle_chord_intersection {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) :
    chordInterior C.point e ∩ chordInterior C.point f =
      if (e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
         (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2) then
        {lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
          (C.point f.val.1) (C.point f.val.2)}
      else ∅ := by
  by_cases halt : (e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
      (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2)
  · rw [if_pos halt]
    apply open_chords_intersection_singleton
    rcases halt with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
    · exact C.alternating_cross h₁ h₂ h₃
    · exact (Zarankiewicz.segmentsCrossProperly_swap _ _ _ _).mp
        (C.alternating_cross h₁ h₂ h₃)
  · rw [if_neg halt]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨h02, h03, h12, h13⟩ := circle_chord_endpoints_distinct C.point C.injective
      C.on_circle e f hef x hx.1 hx.2
    have hei := e.property
    have hfi := f.property
    have htrans := Zarankiewicz.round_circle_chords_transverse 0
      (C.point e.val.1) (C.point e.val.2) (C.point f.val.1) (C.point f.val.2) 1
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle e.val.1)
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle e.val.2)
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle f.val.1)
      (by simpa only [sub_zero, one_pow, squaredLength, Zarankiewicz.squaredLength] using C.on_circle f.val.2)
      (C.injective.ne (ne_of_lt hei)) (C.injective.ne (ne_of_lt hfi))
      (C.injective.ne h02) (C.injective.ne h03) (C.injective.ne h12) (C.injective.ne h13)
    obtain ⟨t, ht, he⟩ := hx.1
    obtain ⟨u, hu, hf⟩ := hx.2
    have heq := he.trans hf.symm
    have hcross : Zarankiewicz.SegmentsCrossProperly (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2) :=
      ⟨(htrans t ⟨ht.1.le, ht.2.le⟩ u ⟨hu.1.le, hu.2.le⟩ heq).1, t, ht, u, hu, heq⟩
    apply Zarankiewicz.not_segmentsCrossProperly_of_same_side _ _ _ _ _ hcross
    by_cases hinside : e.val.1 < f.val.1 ∧ f.val.1 < e.val.2
    · exact Or.inr ⟨C.orient_inside hinside.1 hinside.2,
        C.orient_inside (by omega) (by omega)⟩
    · exact Or.inl ⟨C.orient_outside hei (by omega), C.orient_outside hei (by omega)⟩

end Paper170

end

end

section

noncomputable section

open Set

open scoped Classical

namespace Paper170

@[simp] theorem inversion_zero : inversion 0 = 0 := by
  simp [inversion, squaredLength]

theorem inversion_ne_zero {x : Plane} (hx : x ≠ 0) : inversion x ≠ 0 := by
  intro h
  exact hx ((inversion_involutive x).symm.trans ((congrArg inversion h).trans inversion_zero))

theorem continuous_squaredLength : Continuous squaredLength := by
  unfold squaredLength
  fun_prop

theorem continuousAt_inversion {x : Plane} (hx : x ≠ 0) : ContinuousAt inversion x := by
  have hq := ne_of_gt (squaredLength_pos hx)
  exact (continuous_fst.continuousAt.div continuous_squaredLength.continuousAt hq).prodMk
    (continuous_snd.continuousAt.div continuous_squaredLength.continuousAt hq)

def inversionChart : OpenPartialHomeomorph Plane Plane where
  toFun := inversion
  invFun := inversion
  source := {x | x ≠ 0}
  target := {x | x ≠ 0}
  map_source' := fun _ hx => inversion_ne_zero hx
  map_target' := fun _ hx => inversion_ne_zero hx
  left_inv' := fun x _ => inversion_involutive x
  right_inv' := fun x _ => inversion_involutive x
  continuousOn_toFun := fun _ hx => (continuousAt_inversion hx).continuousWithinAt
  continuousOn_invFun := fun _ hx => (continuousAt_inversion hx).continuousWithinAt
  open_source := isClosed_singleton.isOpen_compl
  open_target := isClosed_singleton.isOpen_compl

theorem inversion_chart_image (c : OpenPartialHomeomorph Plane Plane) (A L : Set Plane)
    (h : c '' (c.source ∩ A) = c.target ∩ L) :
    (inversionChart.trans c) '' ((inversionChart.trans c).source ∩ inversion '' A) =
      (inversionChart.trans c).target ∩ L := by
  let e := inversionChart.trans c
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    have hs : z ≠ 0 ∧ inversion z ∈ c.source := hz.1
    obtain ⟨a, ha, rfl⟩ := hz.2
    have hi : inversion (inversion a) ∈ A := (inversion_involutive a).symm ▸ ha
    exact ⟨e.map_source hz.1,
      (Zarankiewicz.chart_image_mem_iff c A L h _ hs.2).mp hi⟩
  · rintro y ⟨hy, hL⟩
    have hz := e.map_target hy
    have hs : e.symm y ≠ 0 ∧ inversion (e.symm y) ∈ c.source := hz
    have he : c (inversion (e.symm y)) = y := e.right_inv hy
    have ha : inversion (e.symm y) ∈ A :=
      (Zarankiewicz.chart_image_mem_iff c A L h _ hs.2).mpr (he.symm ▸ hL)
    exact ⟨e.symm y, ⟨hz, ⟨inversion (e.symm y), ha, inversion_involutive _⟩⟩,
      e.right_inv hy⟩

theorem ProperCrossing.inverted {A B : Set Plane} {x : Plane}
    (h : ProperCrossing A B x) (hx : x ≠ 0) :
    ProperCrossing (inversion '' A) (inversion '' B) (inversion x) := by
  obtain ⟨c, hs, he, hA, hB⟩ := h.chart_exists
  refine ⟨inversionChart.trans c, ⟨inversion_ne_zero hx, ?_⟩, ?_,
    inversion_chart_image c A _ hA, inversion_chart_image c B _ hB⟩
  · change inversion (inversion x) ∈ c.source
    rwa [inversion_involutive]
  · change c (inversion (inversion x)) = (0, 0)
    rwa [inversion_involutive]

theorem squaredLength_inversion {x : Plane} (hx : x ≠ 0) :
    squaredLength (inversion x) = (squaredLength x)⁻¹ := by
  have hq := ne_of_gt (squaredLength_pos hx)
  change (x.1 / squaredLength x)^2 + (x.2 / squaredLength x)^2 = _
  rw [div_pow, div_pow, ← add_div]
  change squaredLength x / squaredLength x ^ 2 = _
  field_simp

theorem chord_ne_zero {a b : Plane} (ha : squaredLength a = 1)
    (hb : squaredLength b = 1) (hab : a + b ≠ 0) (t : ℝ) :
    segmentPoint a b t ≠ 0 := by
  intro h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  change (1-t)*a.1+t*b.1=0 at h0
  change (1-t)*a.2+t*b.2=0 at h1
  have ht : t = 1/2 := by
    have he : (1-t)^2 * squaredLength a = t^2 * squaredLength b := by
      unfold squaredLength
      linear_combination ((1-t)*a.1-t*b.1)*h0 + ((1-t)*a.2-t*b.2)*h1
    rw [ha, hb] at he
    nlinarith
  apply hab
  ext <;> dsimp <;> rw [ht] at h0 h1 <;> linarith

theorem CircleConfiguration.chord_ne_zero {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) (t : ℝ) :
    segmentPoint (C.point e.val.1) (C.point e.val.2) t ≠ 0 :=
  Paper170.chord_ne_zero (C.on_circle _) (C.on_circle _)
    (C.no_antipodal _ _ (ne_of_lt e.property)) t

theorem CircleConfiguration.chord_inside {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) {x : Plane} (hx : x ∈ chordInterior C.point e) :
    squaredLength x < 1 := by
  obtain ⟨t, ht, rfl⟩ := hx
  simpa only [squaredLength, Zarankiewicz.squaredLength, sub_zero, one_pow, segmentPoint_eq] using
    Zarankiewicz.round_chord_in_open_disk 0 (C.point e.val.1) (C.point e.val.2) 1
      (by simpa only [squaredLength, Zarankiewicz.squaredLength, sub_zero, one_pow] using C.on_circle e.val.1)
      (by simpa only [squaredLength, Zarankiewicz.squaredLength, sub_zero, one_pow] using C.on_circle e.val.2)
      (C.injective.ne (ne_of_lt e.property)) t ht

theorem CircleConfiguration.chord_mem_ne_zero {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) {x : Plane} (hx : x ∈ chordInterior C.point e) : x ≠ 0 := by
  obtain ⟨t, _, rfl⟩ := hx
  exact C.chord_ne_zero e t

theorem CircleConfiguration.inverted_chord_outside {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) {x : Plane} (hx : x ∈ inversion '' chordInterior C.point e) :
    1 < squaredLength x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [squaredLength_inversion (C.chord_mem_ne_zero e hy)]
  exact (one_lt_inv₀ (squaredLength_pos (C.chord_mem_ne_zero e hy))).mpr (C.chord_inside e hy)

end Paper170

end

end

section

noncomputable section

open Set

open scoped Classical

namespace Paper170

theorem segmentPoint_injective {a b : Plane} (hab : a ≠ b) :
    Function.Injective (segmentPoint a b) := by
  intro s t h
  apply AffineMap.lineMap_injective ℝ hab
  simpa only [AffineMap.lineMap_apply_module, segmentPoint] using h

theorem continuous_segmentPoint (a b : Plane) : Continuous (segmentPoint a b) := by
  unfold segmentPoint
  fun_prop

theorem continuous_twoPageRoute {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    Continuous (twoPageRoute C e) := by
  have hseg : Continuous (fun t : unitInterval => segmentPoint (C.point e.val.1) (C.point e.val.2) t.val) :=
    (continuous_segmentPoint _ _).comp continuous_subtype_val
  change Continuous (fun t => twoPageRoute C e t)
  cases hc : residueColor n (e.val.1.val + e.val.2.val)
  ·
    simp only [twoPageRoute, hc, Bool.false_eq_true, ↓reduceIte]
    exact continuous_iff_continuousAt.mpr (fun t =>
      (continuousAt_inversion (C.chord_ne_zero e t.val)).comp
        (f := fun u : unitInterval => segmentPoint (C.point e.val.1) (C.point e.val.2) u.val)
        hseg.continuousAt)
  · simpa only [twoPageRoute, hc, ↓reduceIte] using hseg

def twoPagePath {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    Path (C.point e.val.1) (C.point e.val.2) where
  toFun := twoPageRoute C e
  continuous_toFun := continuous_twoPageRoute C e
  source' := by
    simp [twoPageRoute, segmentPoint, inversion_fixes_circle _ (C.on_circle _)]
  target' := by
    simp [twoPageRoute, segmentPoint, inversion_fixes_circle _ (C.on_circle _)]

theorem twoPageRoute_injective {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    Function.Injective (twoPageRoute C e) := by
  have hseg := (segmentPoint_injective (C.injective.ne (ne_of_lt e.property))).comp
    (show Function.Injective (fun t : unitInterval => t.val) from Subtype.val_injective)
  cases hc : residueColor n (e.val.1.val + e.val.2.val)
  · intro s t h
    apply hseg
    change segmentPoint (C.point e.val.1) (C.point e.val.2) s.val =
      segmentPoint (C.point e.val.1) (C.point e.val.2) t.val
    exact inversion_involutive.injective (by simpa only [twoPageRoute, hc, Bool.false_eq_true, ↓reduceIte] using h)
  · intro s t h
    apply hseg
    change segmentPoint (C.point e.val.1) (C.point e.val.2) s.val =
      segmentPoint (C.point e.val.1) (C.point e.val.2) t.val
    simpa only [twoPageRoute, hc, ↓reduceIte] using h

theorem twoPageRoute_avoids_vertices {n : ℕ} (C : CircleConfiguration n)
    (e : CompleteEdge n) (t : unitInterval) (ht : t ∈ Ioo (0 : unitInterval) 1) (v : Fin n) :
    twoPageRoute C e t ≠ C.point v := by
  have hmem : twoPageRoute C e t ∈ twoPageRoute C e '' Ioo (0 : unitInterval) 1 := ⟨t, ht, rfl⟩
  rw [twoPageRoute_image] at hmem
  intro he
  rw [he] at hmem
  cases hc : residueColor n (e.val.1.val + e.val.2.val)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
    have h := C.inverted_chord_outside e hmem
    rw [C.on_circle] at h
    exact (lt_irrefl _ h)
  · simp only [hc, ↓reduceIte] at hmem
    have h := C.chord_inside e hmem
    rw [C.on_circle] at h
    exact (lt_irrefl _ h)

def twoPageContinuous {n : ℕ} (C : CircleConfiguration n) :
    ContinuousDrawing (completeGraph n) where
  vertex := C.point
  vertex_injective := C.injective
  edge := twoPagePath C
  edge_injective := twoPageRoute_injective C
  interior_avoids_vertices := twoPageRoute_avoids_vertices C

theorem twoPageContinuous_edgeInterior {n : ℕ} (C : CircleConfiguration n) (e : CompleteEdge n) :
    edgeInterior (twoPageContinuous C) e =
      if residueColor n (e.val.1.val + e.val.2.val) then chordInterior C.point e
      else inversion '' chordInterior C.point e :=
  twoPageRoute_image C e

end Paper170

end

end

section

noncomputable section

open Set

open scoped Classical

namespace Paper170

theorem CircleConfiguration.chord_proper {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) {x : Plane}
    (hx : x ∈ chordInterior C.point e) (hy : x ∈ chordInterior C.point f) :
    ProperCrossing (chordInterior C.point e) (chordInterior C.point f) x := by
  have hp : x ∈ chordInterior C.point e ∩ chordInterior C.point f := ⟨hx, hy⟩
  rw [circle_chord_intersection C e f hef] at hp
  split_ifs at hp with halt
  · have hcross : Zarankiewicz.SegmentsCrossProperly (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2) := by
      rcases halt with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
      · exact C.alternating_cross h₁ h₂ h₃
      · exact (Zarankiewicz.segmentsCrossProperly_swap _ _ _ _).mp (C.alternating_cross h₁ h₂ h₃)
    exact ⟨Zarankiewicz.properCrossing_openSegments _ _ _ _ x hcross.1 hx hy⟩
  · exact hp.elim

theorem CircleConfiguration.chord_inter_finite {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) :
    (chordInterior C.point e ∩ chordInterior C.point f).Finite := by
  rw [circle_chord_intersection C e f hef]
  split_ifs <;> simp

theorem CircleConfiguration.chord_inverted_disjoint {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) :
    Disjoint (chordInterior C.point e) (inversion '' chordInterior C.point f) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact lt_asymm (C.chord_inside e hx) (C.inverted_chord_outside f hy)

theorem twoPageContinuous_same_color {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) {x : Plane}
    (hx : x ∈ edgeInterior (twoPageContinuous C) e)
    (hy : x ∈ edgeInterior (twoPageContinuous C) f) :
    residueColor n (e.val.1.val + e.val.2.val) =
      residueColor n (f.val.1.val + f.val.2.val) := by
  rw [twoPageContinuous_edgeInterior] at hx hy
  cases he : residueColor n (e.val.1.val + e.val.2.val) <;>
    cases hf : residueColor n (f.val.1.val + f.val.2.val) <;>
    simp only [he, hf, Bool.false_eq_true, ↓reduceIte] at hx hy ⊢
  · exact (lt_asymm (C.inverted_chord_outside e hx) (C.chord_inside f hy)).elim
  · exact (lt_asymm (C.chord_inside e hx) (C.inverted_chord_outside f hy)).elim

theorem twoPageContinuous_inter_finite {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) :
    (edgeInterior (twoPageContinuous C) e ∩ edgeInterior (twoPageContinuous C) f).Finite := by
  rw [twoPageContinuous_edgeInterior, twoPageContinuous_edgeInterior]
  cases he : residueColor n (e.val.1.val + e.val.2.val) <;>
    cases hf : residueColor n (f.val.1.val + f.val.2.val) <;>
    simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [← Set.image_inter inversion_involutive.injective]
    exact (C.chord_inter_finite e f hef).image _
  · rw [(C.chord_inverted_disjoint f e).symm.inter_eq]
    exact Set.finite_empty
  · rw [(C.chord_inverted_disjoint e f).inter_eq]
    exact Set.finite_empty
  · exact C.chord_inter_finite e f hef

theorem twoPageContinuous_crossings_finite {n : ℕ} (C : CircleConfiguration n) :
    (crossingPoints (twoPageContinuous C)).Finite := by
  have heq : crossingPoints (twoPageContinuous C) =
      ⋃ e : CompleteEdge n, ⋃ f : CompleteEdge n,
        if e = f then ∅ else edgeInterior (twoPageContinuous C) e ∩
          edgeInterior (twoPageContinuous C) f := by
    ext x
    simp only [crossingPoints, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨e, f, hef, hx, hy⟩
      exact ⟨e, f, by rw [if_neg hef]; exact ⟨hx, hy⟩⟩
    · rintro ⟨e, f, hx⟩
      split_ifs at hx with hef
      · exact hx.elim
      · exact ⟨e, f, hef, hx.1, hx.2⟩
  rw [heq]
  apply Set.finite_iUnion
  intro e
  apply Set.finite_iUnion
  intro f
  split_ifs with hef
  · exact Set.finite_empty
  · exact twoPageContinuous_inter_finite C e f hef

theorem twoPageContinuous_proper {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) (x : Plane)
    (hx : x ∈ edgeInterior (twoPageContinuous C) e)
    (hy : x ∈ edgeInterior (twoPageContinuous C) f) :
    ProperCrossing (edgeInterior (twoPageContinuous C) e)
      (edgeInterior (twoPageContinuous C) f) x := by
  have hc := twoPageContinuous_same_color C e f hx hy
  simp only [twoPageContinuous_edgeInterior] at hx hy ⊢
  rw [hc] at hx ⊢
  cases hf : residueColor n (f.val.1.val + f.val.2.val) <;>
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at hx hy ⊢
  · obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, he⟩ := hy
    have hba : b = a := inversion_involutive.injective he
    subst b
    exact ProperCrossing.inverted (C.chord_proper e f hef ha hb) (C.chord_mem_ne_zero e ha)
  · exact C.chord_proper e f hef hx hy

theorem twoPageContinuous_no_triples {n : ℕ} (C : CircleConfiguration n)
    (e f g : CompleteEdge n) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    edgeInterior (twoPageContinuous C) e ∩ edgeInterior (twoPageContinuous C) f ∩
      edgeInterior (twoPageContinuous C) g = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hcf := twoPageContinuous_same_color C e f hx.1.1 hx.1.2
  have hcg := twoPageContinuous_same_color C e g hx.1.1 hx.2
  simp only [twoPageContinuous_edgeInterior, ← hcf, ← hcg] at hx
  cases he : residueColor n (e.val.1.val + e.val.2.val) <;>
    simp only [he, Bool.false_eq_true, ↓reduceIte] at hx
  · have hm : x ∈ inversion ''
        (chordInterior C.point e ∩ chordInterior C.point f ∩ chordInterior C.point g) := by
      rw [Set.image_inter inversion_involutive.injective,
        Set.image_inter inversion_involutive.injective]
      exact hx
    rw [C.no_triple_chords e f g hef heg hfg, Set.image_empty] at hm
    exact hm.elim
  · rw [C.no_triple_chords e f g hef heg hfg] at hx
    exact hx.elim

def twoPageAdmissible {n : ℕ} (C : CircleConfiguration n) :
    AdmissibleDrawing (completeGraph n) where
  toContinuousDrawing := twoPageContinuous C
  crossings_finite := twoPageContinuous_crossings_finite C
  crossings_proper := twoPageContinuous_proper C
  no_triples := twoPageContinuous_no_triples C

theorem two_page_drawing_exists {n : ℕ} (C : CircleConfiguration n) :
    ∃ D : AdmissibleDrawing (completeGraph n), TwoPageDrawing C D :=
  ⟨twoPageAdmissible C, rfl, fun _ _ => rfl⟩

end Paper170

end

end

end OAI


-- OAI.Combinatorics.Crossing.AffineSubdivisionRefinement
namespace OAI

noncomputable section

namespace Zarankiewicz

theorem HasFiniteAffineCover.refine {a b : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) (R : Finset unitInterval) :
    ∃ P : PolygonalParametrization γ, (R : Set unitInterval) ⊆ Set.range P.knot := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  let T : Finset unitInterval := insert 0 (insert 1 ((S.image Prod.fst ∪ S.image Prod.snd) ∪ R))
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset T (by simp [T]) (by simp [T])
  have hleft (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.1 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩))))
  have hright (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.2 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩))))
  have haff : ∀ i : Fin k, ∀ u : unitInterval,
      γ (intervalSegment (t i.castSucc) (t i.succ) u)=segmentPoint (γ (t i.castSucc)) (γ (t i.succ)) u.val := by
    intro i u
    let mid : unitInterval := ⟨1/2,by norm_num⟩
    let z := intervalSegment (t i.castSucc) (t i.succ) mid
    have hz : t i.castSucc < z ∧ z < t i.succ :=
      intervalSegment_strict_between _ _ mid (ht (by change i.val < i.val+1; omega)) (by
        constructor <;> change (_ : ℝ) < _ <;> norm_num [mid])
    obtain ⟨ab,hab,ha,hb⟩ := hScov z
    have hlo : ab.1 ≤ t i.castSucc := by
      by_contra hn
      obtain ⟨j,hj⟩ := hleft ab hab
      exact strictMono_no_between_successors t ht i j
        ⟨by rw [hj]; exact lt_of_not_ge hn,by rw [hj]; exact ha.trans_lt hz.2⟩
    have hhi : t i.succ ≤ ab.2 := by
      by_contra hn
      obtain ⟨j,hj⟩ := hright ab hab
      exact strictMono_no_between_successors t ht i j
        ⟨by rw [hj]; exact hz.1.trans_le hb,by rw [hj]; exact lt_of_not_ge hn⟩
    have hle : t i.castSucc ≤ t i.succ := ht.monotone (by change i.val ≤ i.val+1; omega)
    exact path_affine_restrict γ ab.1 ab.2 (hSlt ab hab) (hSaff ab hab)
      (t i.castSucc) (t i.succ) ⟨hlo,hle.trans hhi⟩ ⟨hlo.trans hle,hhi⟩ u
  refine ⟨{pieces:=k,knot:=t,increasing:=ht,first:=h0,last:=h1,affine:=haff},?_⟩
  intro u hu
  change u ∈ Set.range t
  rw [hR]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hu))

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.Crossing.GenericPolynomialBox
namespace OAI

noncomputable section

namespace Zarankiewicz

open scoped BigOperators

theorem exists_box_avoiding_polynomials {σ κ : Type*} [Fintype κ]
    (P : κ → MvPolynomial σ ℝ) (hP : ∀ k, P k ≠ 0)
    (lo hi : σ → ℝ) (hinterval : ∀ i, lo i < hi i) :
    ∃ x : σ → ℝ, (∀ i, x i ∈ Set.Ioo (lo i) (hi i)) ∧ ∀ k, MvPolynomial.eval x (P k) ≠ 0 := by
  classical
  let Q := ∏ k, P k
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hP k)
  have hex : ∃ x : σ → ℝ, (∀ i, x i ∈ Set.Ioo (lo i) (hi i)) ∧ MvPolynomial.eval x Q ≠ 0 := by
    by_contra hh
    apply hQ
    apply MvPolynomial.funext_set (fun i => Set.Ioo (lo i) (hi i)) (fun i => Set.Ioo_infinite (hinterval i))
    intro x hx
    rw [map_zero]
    by_contra hz
    exact hh ⟨x,fun i => hx i (Set.mem_univ i),hz⟩
  obtain ⟨x,hx,hval⟩ := hex
  refine ⟨x,hx,?_⟩
  have he : (∏ k, MvPolynomial.eval x (P k)) ≠ 0 := by simpa only [Q,map_prod] using hval
  exact fun k => (Finset.prod_ne_zero_iff.mp he) k (Finset.mem_univ k)

end Zarankiewicz

end

end OAI


-- OAI.Combinatorics.CompleteCrossing.CirclePlacement
namespace OAI

section

noncomputable section

open Set

open scoped Classical

namespace Paper170

def circleConcurrency {R : Type*} [CommRing R] (a b c d e f : R) : R :=
  (c + d) * e * f - c * d * (e + f) - (a + b) * (e * f - c * d) +
    a * b * (e + f - c - d)

def circleLine (a b : ℝ) (z : Plane) : ℝ :=
  (1 - a * b) * z.1 + (a + b) * z.2 - (1 + a * b)

theorem circleLine_param (a b : ℝ) : circleLine a b (Zarankiewicz.circlePoint a) = 0 := by
  have ha := ne_of_gt (Zarankiewicz.circle_denominator_pos a)
  unfold circleLine Zarankiewicz.circlePoint
  field_simp
  ring

theorem circleLine_chord (a b t : ℝ) :
    circleLine a b (segmentPoint (Zarankiewicz.circlePoint a) (Zarankiewicz.circlePoint b) t) = 0 := by
  have ha := circleLine_param a b
  have hb := circleLine_param b a
  unfold circleLine at *
  change (1 - a * b) * ((1 - t) * (Zarankiewicz.circlePoint a).1 + t * (Zarankiewicz.circlePoint b).1) +
    (a + b) * ((1 - t) * (Zarankiewicz.circlePoint a).2 + t * (Zarankiewicz.circlePoint b).2) -
      (1 + a * b) = 0
  linear_combination (1 - t) * ha + t * hb

theorem circleConcurrency_of_lines (a b c d e f : ℝ) (z : Plane)
    (h₁ : circleLine a b z = 0) (h₂ : circleLine c d z = 0) (h₃ : circleLine e f z = 0) :
    circleConcurrency a b c d e f = 0 := by
  have he : 2 * circleConcurrency a b c d e f = 0 := by
    unfold circleConcurrency circleLine at *
    linear_combination
      -((1 - c * d) * (e + f) - (1 - e * f) * (c + d)) * h₁ -
      ((1 - e * f) * (a + b) - (1 - a * b) * (e + f)) * h₂ -
      ((1 - a * b) * (c + d) - (1 - c * d) * (a + b)) * h₃
  linarith

def circleConcurrencyPolynomial {n : ℕ} (v : Fin 6 → Fin n) : MvPolynomial (Fin n) ℝ :=
  circleConcurrency (MvPolynomial.X (v 0)) (MvPolynomial.X (v 1))
    (MvPolynomial.X (v 2)) (MvPolynomial.X (v 3))
    (MvPolynomial.X (v 4)) (MvPolynomial.X (v 5))

theorem circleConcurrencyPolynomial_eval {n : ℕ} (v : Fin 6 → Fin n) (t : Fin n → ℝ) :
    MvPolynomial.eval t (circleConcurrencyPolynomial v) =
      circleConcurrency (t (v 0)) (t (v 1)) (t (v 2)) (t (v 3)) (t (v 4)) (t (v 5)) := by
  simp [circleConcurrencyPolynomial, circleConcurrency]

theorem circleConcurrencyPolynomial_ne_zero {n : ℕ} (v : Fin 6 → Fin n)
    (hv : Function.Injective v) : circleConcurrencyPolynomial v ≠ 0 := by
  let t : Fin n → ℝ := fun i => if i = v 2 ∨ i = v 4 ∨ i = v 5 then 1 else 0
  have he : MvPolynomial.eval t (circleConcurrencyPolynomial v) = 1 := by
    rw [circleConcurrencyPolynomial_eval]
    simp only [t, hv.eq_iff]
    norm_num [circleConcurrency, Fin.ext_iff]
  intro hz
  rw [hz, map_zero] at he
  exact zero_ne_one he

theorem circle_configuration_exists (n : ℕ) : Nonempty (CircleConfiguration n) := by
  let I := {v : Fin 6 → Fin n // Function.Injective v}
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨t, ht, havoid⟩ := Zarankiewicz.exists_box_avoiding_polynomials
    (fun v : I => circleConcurrencyPolynomial v.val)
    (fun v => circleConcurrencyPolynomial_ne_zero v.val v.property)
    (fun i : Fin n => 2 * (i.val : ℝ) + 1) (fun i : Fin n => 2 * (i.val : ℝ) + 2)
    (by intro i; linarith)
  have htmono : StrictMono t := by
    intro i j hij
    have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
    linarith [(ht i).2, (ht j).1]
  have htpos (i : Fin n) : 0 < t i := by
    have hnonneg : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    linarith [(ht i).1]
  let p := Zarankiewicz.circlePoint ∘ t
  have hp : Function.Injective p := Zarankiewicz.circlePoint_injective.comp htmono.injective
  have hcircle (i : Fin n) : squaredLength (p i) = 1 := Zarankiewicz.circlePoint_on_unit_circle (t i)
  refine ⟨{
    point := p
    injective := hp
    on_circle := hcircle
    cyclic_order := ?_
    no_antipodal := ?_
    no_triple_chords := ?_ }⟩
  · intro i j k hij hjk
    exact Zarankiewicz.circle_orient_pos (t i) (t j) (t k) (htmono hij) (htmono hjk)
  · intro i j _ he
    have hi : 0 < (p i).2 := div_pos (by linarith [htpos i]) (Zarankiewicz.circle_denominator_pos _)
    have hj : 0 < (p j).2 := div_pos (by linarith [htpos j]) (Zarankiewicz.circle_denominator_pos _)
    have hz := congrArg Prod.snd he
    change (p i).2 + (p j).2 = 0 at hz
    linarith
  · intro e f g hef heg hfg
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hEF := circle_chord_endpoints_distinct p hp hcircle e f hef z hz.1.1 hz.1.2
    have hEG := circle_chord_endpoints_distinct p hp hcircle e g heg z hz.1.1 hz.2
    have hFG := circle_chord_endpoints_distinct p hp hcircle f g hfg z hz.1.2 hz.2
    let v : Fin 6 → Fin n := ![e.val.1, e.val.2, f.val.1, f.val.2, g.val.1, g.val.2]
    have hv : Function.Injective v := by
      intro i j heq
      have he' := e.property
      have hf' := f.property
      have hg' := g.property
      fin_cases i <;> fin_cases j <;> norm_num [v, Fin.ext_iff] at heq ⊢ <;> omega
    have hne := havoid (⟨v, hv⟩ : I)
    rw [circleConcurrencyPolynomial_eval] at hne
    have hline (a : CompleteEdge n) (ha : z ∈ chordInterior p a) :
        circleLine (t a.val.1) (t a.val.2) z = 0 := by
      obtain ⟨u, _, rfl⟩ := ha
      exact circleLine_chord _ _ u
    apply hne
    exact circleConcurrency_of_lines _ _ _ _ _ _ z
      (hline e hz.1.1) (hline f hz.1.2) (hline g hz.2)

end Paper170

end

end

end OAI


-- OAI.Combinatorics.CompleteCrossing.TwoPage
namespace OAI

section

noncomputable section

open Set

open scoped Classical

namespace Paper170

lemma twoPage_meeting_chords {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e f : CompleteEdge n) (x : Plane)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    residueColor n (e.val.1.val + e.val.2.val) = residueColor n (f.val.1.val + f.val.2.val) ∧
      ∃ y, y ∈ chordInterior C.point e ∩ chordInterior C.point f ∧
        x = if residueColor n (e.val.1.val + e.val.2.val) then y else inversion y := by
  rw [twoPage_edgeInterior C D hD e] at he
  rw [twoPage_edgeInterior C D hD f] at hf
  cases hec : residueColor n (e.val.1.val + e.val.2.val) <;>
    cases hfc : residueColor n (f.val.1.val + f.val.2.val)
  · simp only [hec, Bool.false_eq_true, ↓reduceIte] at he
    simp only [hfc, Bool.false_eq_true, ↓reduceIte] at hf
    obtain ⟨y, hy, rfl⟩ := he
    obtain ⟨z, hz, hzy⟩ := hf
    have hzy' : z = y := inversion_involutive.injective hzy
    subst z
    exact ⟨rfl, y, ⟨hy, hz⟩, rfl⟩
  · simp only [hec, Bool.false_eq_true, ↓reduceIte] at he
    simp only [hfc, ↓reduceIte] at hf
    have h1 := C.inverted_chord_outside e he
    have h2 := C.chord_inside f hf
    linarith
  · simp only [hec, ↓reduceIte] at he
    simp only [hfc, Bool.false_eq_true, ↓reduceIte] at hf
    have h1 := C.chord_inside e he
    have h2 := C.inverted_chord_outside f hf
    linarith
  · simp only [hec, ↓reduceIte] at he
    simp only [hfc, ↓reduceIte] at hf
    exact ⟨rfl, x, ⟨he, hf⟩, rfl⟩

lemma chord_meeting_alternates {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n) (hef : e ≠ f) (y : Plane)
    (hy : y ∈ chordInterior C.point e ∩ chordInterior C.point f) :
    ((e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
      (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2)) ∧
      y = lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2) := by
  rw [circle_chord_intersection C e f hef] at hy
  split_ifs at hy with h
  · exact ⟨h, hy⟩
  · exact hy.elim

lemma twoPage_meeting_alternates {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e f : CompleteEdge n) (hef : e ≠ f) (x : Plane)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    residueColor n (e.val.1.val + e.val.2.val) = residueColor n (f.val.1.val + f.val.2.val) ∧
    ((e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) ∨
      (f.val.1 < e.val.1 ∧ e.val.1 < f.val.2 ∧ f.val.2 < e.val.2)) ∧
    x = if residueColor n (e.val.1.val + e.val.2.val) then
      lineIntersectionPoint (C.point e.val.1) (C.point e.val.2) (C.point f.val.1) (C.point f.val.2)
      else inversion (lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2)) := by
  obtain ⟨hc, y, hy, hx⟩ := twoPage_meeting_chords C D hD e f x he hf
  obtain ⟨ho, rfl⟩ := chord_meeting_alternates C e f hef y hy
  exact ⟨hc, ho, hx⟩

lemma pagePoint_mem_edge {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (e : CompleteEdge n) (y : Plane) (hy : y ∈ chordInterior C.point e) :
    (if residueColor n (e.val.1.val + e.val.2.val) then y else inversion y) ∈
      edgeInterior D.toContinuousDrawing e := by
  rw [twoPage_edgeInterior C D hD]
  cases h : residueColor n (e.val.1.val + e.val.2.val)
  · exact ⟨y, hy, rfl⟩
  · exact hy

lemma ordered_chord_meeting {n : ℕ} (C : CircleConfiguration n)
    (e f : CompleteEdge n)
    (ho : e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2) :
    lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
      (C.point f.val.1) (C.point f.val.2) ∈ chordInterior C.point e ∩ chordInterior C.point f := by
  have hef : e ≠ f := by intro h; subst f; exact (lt_irrefl _ ho.1)
  rw [circle_chord_intersection C e f hef, if_pos (Or.inl ho)]
  exact Set.mem_singleton _

end Paper170

end

end

section

noncomputable section

open Set

open scoped Classical

namespace Paper170

def tupleFirstEdge {n : ℕ} (v : Fin 4 → Fin n) (hv : StrictMono v) : CompleteEdge n :=
  ⟨(v 0, v 2), hv (by decide)⟩

def tupleSecondEdge {n : ℕ} (v : Fin 4 → Fin n) (hv : StrictMono v) : CompleteEdge n :=
  ⟨(v 1, v 3), hv (by decide)⟩

lemma tuple_edges_ne {n : ℕ} (v : Fin 4 → Fin n) (hv : StrictMono v) :
    tupleFirstEdge v hv ≠ tupleSecondEdge v hv := by
  intro h
  exact (ne_of_lt (hv (by decide : (0 : Fin 4) < 1)))
    (congrArg (fun e => e.val.1) h)

lemma tuple_point_membership {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D)
    (v : Fin 4 → Fin n) (hv : v ∈ crossingTuples n) :
    let hm := (Finset.mem_filter.mp hv).2.1
    crossingTuplePoint C v ∈ edgeInterior D.toContinuousDrawing (tupleFirstEdge v hm) ∧
      crossingTuplePoint C v ∈ edgeInterior D.toContinuousDrawing (tupleSecondEdge v hm) := by
  let hm := (Finset.mem_filter.mp hv).2.1
  have hc := (Finset.mem_filter.mp hv).2.2
  have hy := ordered_chord_meeting C (tupleFirstEdge v hm) (tupleSecondEdge v hm)
    ⟨hm (by decide : (0 : Fin 4) < 1), hm (by decide : (1 : Fin 4) < 2),
      hm (by decide : (2 : Fin 4) < 3)⟩
  constructor
  · exact pagePoint_mem_edge C D hD (tupleFirstEdge v hm) _ hy.1
  · have h := pagePoint_mem_edge C D hD (tupleSecondEdge v hm) _ hy.2
    change (if residueColor n ((v 1).val + (v 3).val) then _ else _) ∈ _ at h
    rw [← hc] at h
    exact h

lemma ordered_pair_tuple {n : ℕ} (C : CircleConfiguration n) (e f : CompleteEdge n)
    (ho : e.val.1 < f.val.1 ∧ f.val.1 < e.val.2 ∧ e.val.2 < f.val.2)
    (hc : residueColor n (e.val.1.val + e.val.2.val) = residueColor n (f.val.1.val + f.val.2.val)) :
    ∃ v ∈ crossingTuples n, crossingTuplePoint C v =
      if residueColor n (e.val.1.val + e.val.2.val) then
        lineIntersectionPoint (C.point e.val.1) (C.point e.val.2) (C.point f.val.1) (C.point f.val.2)
      else inversion (lineIntersectionPoint (C.point e.val.1) (C.point e.val.2)
        (C.point f.val.1) (C.point f.val.2)) := by
  let v : Fin 4 → Fin n := ![e.val.1, f.val.1, e.val.2, f.val.2]
  refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, rfl⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact ho.1
    · exact ho.2.1
    · exact ho.2.2
  · exact hc

lemma crossingTuplePoint_surjOn {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    SurjOn (crossingTuplePoint C) (crossingTuples n : Set (Fin 4 → Fin n))
      (crossingPoints D.toContinuousDrawing) := by
  rintro x ⟨e, f, hef, he, hf⟩
  obtain ⟨hc, ho, hx⟩ := twoPage_meeting_alternates C D hD e f hef x he hf
  rcases ho with ho | ho
  · obtain ⟨v, hv, hp⟩ := ordered_pair_tuple C e f ho hc
    exact ⟨v, hv, hp.trans hx.symm⟩
  · obtain ⟨_, _, hx'⟩ := twoPage_meeting_alternates C D hD f e hef.symm x hf he
    obtain ⟨v, hv, hp⟩ := ordered_pair_tuple C f e ho hc.symm
    exact ⟨v, hv, hp.trans hx'.symm⟩

lemma crossingTuplePoint_injOn {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    InjOn (crossingTuplePoint C) (crossingTuples n : Set (Fin 4 → Fin n)) := by
  intro v hv w hw hpoint
  let hv' := (Finset.mem_filter.mp hv).2.1
  let hw' := (Finset.mem_filter.mp hw).2.1
  have hpv := tuple_point_membership C D hD v hv
  have hpw := tuple_point_membership C D hD w hw
  rw [← hpoint] at hpw
  have hinc := Paper170Geometry.crossing_incident_iff D (crossingTuplePoint C v)
    (tupleFirstEdge v hv') (tupleSecondEdge v hv') (tuple_edges_ne v hv') hpv.1 hpv.2
  have he := (hinc (tupleFirstEdge w hw')).mp hpw.1
  have hf := (hinc (tupleSecondEdge w hw')).mp hpw.2
  rcases he with he | he <;> rcases hf with hf | hf
  · exact (tuple_edges_ne w hw' (he.trans hf.symm)).elim
  · have h0 := congrArg (fun e => e.val.1) he
    have h2 := congrArg (fun e => e.val.2) he
    have h1 := congrArg (fun e => e.val.1) hf
    have h3 := congrArg (fun e => e.val.2) hf
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  · have h0 : w 0 = v 1 := congrArg (fun e => e.val.1) he
    have h1 : w 1 = v 0 := congrArg (fun e => e.val.1) hf
    have hlt := hw' (by decide : (0 : Fin 4) < 1)
    rw [h0, h1] at hlt
    exact (lt_asymm (hv' (by decide : (0 : Fin 4) < 1)) hlt).elim
  · exact (tuple_edges_ne w hw' (he.trans hf.symm)).elim

theorem two_page_crossing_bijection {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    BijOn (crossingTuplePoint C) (crossingTuples n : Set (Fin 4 → Fin n))
      (crossingPoints D.toContinuousDrawing) := by
  refine ⟨?_, crossingTuplePoint_injOn C D hD, crossingTuplePoint_surjOn C D hD⟩
  intro v hv
  have hp := tuple_point_membership C D hD v hv
  exact ⟨_, _, tuple_edges_ne _ _, hp.1, hp.2⟩

end Paper170

end

end

section

noncomputable section

namespace Paper170

theorem two_page_crossing_count {n : ℕ} (C : CircleConfiguration n)
    (D : AdmissibleDrawing (completeGraph n)) (hD : TwoPageDrawing C D) :
    crossingCount D = (crossingTuples n).card := by
  have h := (two_page_crossing_bijection C D hD).ncard_eq
  simpa [crossingCount, Set.ncard_eq_toFinset_card _ D.crossings_finite] using h.symm

end Paper170

end

end

section

noncomputable section

namespace Paper170

theorem complete_graph_upper_drawing (n : ℕ) :
    ∃ D : AdmissibleDrawing (completeGraph n), crossingCount D = (crossingTuples n).card := by
  obtain ⟨C⟩ := circle_configuration_exists n
  obtain ⟨D, hD⟩ := two_page_drawing_exists C
  exact ⟨D, two_page_crossing_count C D hD⟩

end Paper170

end

end

end OAI


open OAI.Paper170
theorem OMA.solution : OMA.R_arxiv_2009_03418_R1.H1 := by
  intro n hn
  obtain ⟨D, hD⟩ := complete_graph_upper_drawing n
  exact ⟨D, hD.trans (crossingTuples_card hn)⟩
