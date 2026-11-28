import OMAStatements.S_oeis_a340138
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pigeonhole

-- Problem: A340138: digital root greedy permutation conjecture
-- Credit: @Luckylamb666

open OMA.S_oeis_a340138

namespace OMA_A340138_Proof

lemma root_le_nine (x : ℕ) : root x ≤ 9 := by
  unfold root
  split <;> omega

lemma ten_pow_mod_nine (m : ℕ) : 10 ^ m % 9 = 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [pow_succ, Nat.mul_mod, ih]

lemma list_mem_le_sum {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.mem_cons] at hx
    simp only [List.sum_cons]
    rcases hx with rfl | ht
    · omega
    · have := ih ht; omega

lemma hasDigit_unit {k d : ℕ} (hd : d ≤ 9) : hasDigit (10 ^ (k + 1) + d) d := by
  refine ⟨0, ?_, ?_⟩
  · have h1 : 1 ≤ 10 ^ (k + 1) := Nat.one_le_pow (k + 1) 10 (by decide)
    omega
  · rw [pow_zero, Nat.div_one, pow_succ]
    omega

lemma cand_nonempty (used : List ℕ) :
    {y : ℕ | y ∉ used ∧ 0 < y ∧ hasDigit y (root (used.headD 0))}.Nonempty := by
  let d := root (used.headD 0)
  have hd : d ≤ 9 := root_le_nine _
  let k := used.sum + 1
  let y := 10 ^ (k + 1) + d
  refine ⟨y, ?_, ?_, hasDigit_unit hd⟩
  · intro hmem
    have hle : y ≤ used.sum := list_mem_le_sum hmem
    have hpow : k + 1 < 10 ^ (k + 1) := Nat.lt_pow_self (by decide : 1 < 10)
    dsimp only [y, k] at hle hpow
    omega
  · have h1 : 1 ≤ 10 ^ (k + 1) := Nat.one_le_pow (k + 1) 10 (by decide)
    dsimp only [y]
    omega

lemma term_succ_mem_cand (n : ℕ) :
    term (n + 1) ∉ history n ∧ 0 < term (n + 1) ∧ hasDigit (term (n + 1)) (root (term n)) := by
  exact Nat.sInf_mem (cand_nonempty (history n))

lemma term_mem_history : ∀ {i n : ℕ}, i ≤ n → term i ∈ history n := by
  intro i n hin
  induction n with
  | zero =>
    have hi : i = 0 := by omega
    subst hi
    simp [term, history]
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hin with rfl | hlt
    · simp [term, history]
    · have : term i ∈ history n := ih (by omega)
      simp [history, this]

lemma mem_history_iff (n x : ℕ) : x ∈ history n ↔ ∃ i ≤ n, term i = x := by
  induction n with
  | zero =>
    constructor
    · intro h
      simp only [history, List.mem_singleton] at h
      exact ⟨0, le_rfl, by simp [term, history, h]⟩
    · rintro ⟨i, hi, rfl⟩
      have : i = 0 := by omega
      subst this
      simp [term, history]
  | succ n ih =>
    constructor
    · intro h
      simp only [history, List.mem_cons] at h
      rcases h with rfl | ht
      · exact ⟨n + 1, le_rfl, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := ih.mp ht
        exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact term_mem_history hi

lemma term_injective : Function.Injective term := by
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : term i ∈ history (j - 1) := term_mem_history (by omega)
    rw [hij] at hmem
    have hnot : term j ∉ history (j - 1) := by
      have hj : j = (j - 1) + 1 := by omega
      rw [hj]
      exact (term_succ_mem_cand (j - 1)).1
    exact hnot hmem
  · have hmem : term j ∈ history (i - 1) := term_mem_history (by omega)
    rw [← hij] at hmem
    have hnot : term i ∉ history (i - 1) := by
      have hi : i = (i - 1) + 1 := by omega
      rw [hi]
      exact (term_succ_mem_cand (i - 1)).1
    exact hnot hmem

lemma term_succ_le_of_cand {n y : ℕ} (hnot : y ∉ history n) (hpos : 0 < y)
    (hdig : hasDigit y (root (term n))) : term (n + 1) ≤ y := by
  exact Nat.sInf_le ⟨hnot, hpos, hdig⟩

lemma mem_range_of_infinite_root {d m : ℕ}
    (hinf : {n : ℕ | root (term n) = d}.Infinite)
    (hm_pos : 0 < m)
    (hm_dig : hasDigit m d) :
    ∃ n : ℕ, term n = m := by
  by_contra hnot
  push Not at hnot
  have hle : ∀ n ∈ {n : ℕ | root (term n) = d}, term (n + 1) ≤ m := by
    intro n hn
    have hmem_not : m ∉ history n := by
      intro hmem
      obtain ⟨i, _, hi⟩ := (mem_history_iff n m).mp hmem
      exact hnot i hi
    have hdig : hasDigit m (root (term n)) := by
      rw [hn]
      exact hm_dig
    exact term_succ_le_of_cand hmem_not hm_pos hdig
  have hinj : Function.Injective (fun n : ℕ => term (n + 1)) :=
    term_injective.comp (fun _ _ h => by omega)
  have himg_inf : ((fun n : ℕ => term (n + 1)) '' {n : ℕ | root (term n) = d}).Infinite :=
    hinf.image hinj.injOn
  have himg_sub : ((fun n : ℕ => term (n + 1)) '' {n : ℕ | root (term n) = d}) ⊆
      (Finset.range (m + 1) : Set ℕ) := by
    rintro y ⟨n, hn, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    have := hle n hn
    omega
  exact himg_inf ((Finset.finite_toSet _).subset himg_sub)

lemma exists_infinite_root :
    ∃ d : ℕ, d ≤ 9 ∧ {n : ℕ | root (term n) = d}.Infinite := by
  have hunion : (Set.univ : Set ℕ) ⊆ ⋃ d ∈ (Finset.range 10 : Finset ℕ), {n : ℕ | root (term n) = d} := by
    intro n _
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range]
    have hle := root_le_nine (term n)
    exact ⟨root (term n), by omega, rfl⟩
  by_contra hall
  push Not at hall
  have hfin : (⋃ d ∈ (Finset.range 10 : Finset ℕ), {n : ℕ | root (term n) = d}).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
    intro d hd
    simp only [Finset.mem_coe, Finset.mem_range] at hd
    exact hall d (by omega)
  exact Set.infinite_univ (hfin.subset hunion)

lemma all_pos_roots_infinite {r : ℕ} (hr1 : 1 ≤ r) (hr9 : r ≤ 9) :
    {n : ℕ | root (term n) = r}.Infinite := by
  obtain ⟨d0, hd0, hd_inf⟩ := exists_infinite_root
  let c := (r + 17 - d0) % 9
  have hc : c ≤ 8 := by omega
  have hex : ∀ k : ℕ, ∃ n : ℕ, term n = 10 ^ (k + 2) + d0 * 10 + c := by
    intro k
    have hpow1 : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by decide)
    have h100 : 10 ^ (k + 2) = 100 * 10 ^ k := by
      rw [pow_succ, pow_succ]
      omega
    have hpos : 0 < 10 ^ (k + 2) + d0 * 10 + c := by omega
    have hdig : hasDigit (10 ^ (k + 2) + d0 * 10 + c) d0 := by
      refine ⟨1, ?_, ?_⟩
      · rw [pow_one]; omega
      · rw [pow_one, h100]
        omega
    exact mem_range_of_infinite_root hd_inf hpos hdig
  choose g hg using hex
  have hg_inj : Function.Injective g := by
    intro k1 k2 h
    have hval : 10 ^ (k1 + 2) + d0 * 10 + c = 10 ^ (k2 + 2) + d0 * 10 + c := by
      rw [← hg k1, ← hg k2, h]
    have hpow : 10 ^ (k1 + 2) = 10 ^ (k2 + 2) := by omega
    have hk : k1 + 2 = k2 + 2 := Nat.pow_right_injective (by decide : 2 ≤ 10) hpow
    omega
  have hg_mem : ∀ k : ℕ, g k ∈ {n : ℕ | root (term n) = r} := by
    intro k
    simp only [Set.mem_ofPred_eq, hg k]
    have hpow_mod : 10 ^ (k + 2) % 9 = 1 := ten_pow_mod_nine (k + 2)
    have hpos : 0 < 10 ^ (k + 2) + d0 * 10 + c := by
      have : 1 ≤ 10 ^ (k + 2) := Nat.one_le_pow (k + 2) 10 (by decide)
      omega
    unfold root
    rw [if_neg (by omega)]
    omega
  exact (Set.infinite_range_of_injective hg_inj).mono (by
    rintro n ⟨k, rfl⟩
    exact hg_mem k)

lemma exists_nonzero_digit {m : ℕ} (hm : 0 < m) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ 9 ∧ hasDigit m d := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h10 : m < 10
    · refine ⟨m, by omega, by omega, 0, ?_, ?_⟩
      · rw [pow_zero]; omega
      · rw [pow_zero, Nat.div_one]; omega
    · obtain ⟨d, hd1, hd9, j, hj_le, hj_dig⟩ := ih (m / 10) (by omega) (by omega)
      refine ⟨d, hd1, hd9, j + 1, ?_, ?_⟩
      · rw [pow_succ']
        have := Nat.mul_le_mul_left 10 hj_le
        omega
      · rw [pow_succ', ← Nat.div_div_eq_div_mul]
        exact hj_dig

end OMA_A340138_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a340138.main := by
  refine ⟨OMA_A340138_Proof.term_injective, ?_⟩
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · exact ⟨0, rfl⟩
  · obtain ⟨d, hd1, hd9, hdig⟩ := OMA_A340138_Proof.exists_nonzero_digit hm_pos
    have hd_inf := OMA_A340138_Proof.all_pos_roots_infinite hd1 hd9
    exact OMA_A340138_Proof.mem_range_of_infinite_root hd_inf hm_pos hdig
