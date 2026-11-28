import OMAStatements.S_oeis_a350831
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pigeonhole

-- Problem: A350831: a(n) is the least positive integer not listed earlier such that its first digit together with a(n-1)'s last digit can form a prime
-- Credit: @Luckylamb666

open OMA.S_oeis_a350831

namespace OMA_A350831_Proof

lemma paired_symm {d f : ℕ} (h : paired d f) : paired f d := by
  unfold paired at h ⊢
  exact h.symm

lemma exists_paired_1_or_3 {d : ℕ} (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    ∃ f : ℕ, (f = 1 ∨ f = 3) ∧ paired d f := by
  have hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, Or.inl rfl, Or.inl (by decide)⟩
  · exact ⟨3, Or.inr rfl, Or.inl (by decide)⟩
  · exact ⟨1, Or.inl rfl, Or.inl (by decide)⟩
  · exact ⟨1, Or.inl rfl, Or.inl (by decide)⟩
  · exact ⟨3, Or.inr rfl, Or.inl (by decide)⟩
  · exact ⟨1, Or.inl rfl, Or.inl (by decide)⟩
  · exact ⟨1, Or.inl rfl, Or.inl (by decide)⟩
  · exact ⟨3, Or.inr rfl, Or.inl (by decide)⟩
  · exact ⟨1, Or.inl rfl, Or.inr (by decide)⟩

lemma digits_ne_nil_of_pos {n : ℕ} (hn : 0 < n) : Nat.digits 10 n ≠ [] := by
  intro h
  have := Nat.digits_eq_nil_iff_eq_zero.mp h
  omega

lemma digits_getLastD_div {n : ℕ} (hn : 10 ≤ n) :
    (Nat.digits 10 n).getLastD 0 = (Nat.digits 10 (n / 10)).getLastD 0 := by
  rw [Nat.digits_def' (by decide) (by omega)]
  have hne : Nat.digits 10 (n / 10) ≠ [] := digits_ne_nil_of_pos (by omega)
  cases h : Nat.digits 10 (n / 10) with
  | nil => exact (hne h).elim
  | cons a t => rfl

lemma digits_getLastD_small {f : ℕ} (hf1 : 1 ≤ f) (hf9 : f ≤ 9) :
    (Nat.digits 10 f).getLastD 0 = f := by
  rw [Nat.digits_of_lt 10 f (by omega) (by omega)]
  rfl

lemma digits_getLastD_bounds {n : ℕ} (hn : 0 < n) :
    1 ≤ (Nat.digits 10 n).getLastD 0 ∧ (Nat.digits 10 n).getLastD 0 ≤ 9 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h10 : n < 10
    · rw [digits_getLastD_small (by omega) (by omega)]
      omega
    · rw [digits_getLastD_div (by omega)]
      exact ih (n / 10) (by omega) (by omega)

lemma digits_getLastD_mul_pow {f : ℕ} (hf1 : 1 ≤ f) (hf9 : f ≤ 9) :
    ∀ k : ℕ, (Nat.digits 10 (f * 10 ^ k)).getLastD 0 = f
  | 0 => by simpa using digits_getLastD_small hf1 hf9
  | k + 1 => by
    have h10 : 10 ≤ f * 10 ^ (k + 1) := by
      have hp : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by decide)
      calc 10 = 1 * (1 * 10) := by omega
        _ ≤ f * (10 ^ k * 10) := Nat.mul_le_mul hf1 (Nat.mul_le_mul_right 10 hp)
        _ = f * 10 ^ (k + 1) := by rw [pow_succ]
    rw [digits_getLastD_div h10]
    have hdiv : f * 10 ^ (k + 1) / 10 = f * 10 ^ k := by
      rw [pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by decide)]
    rw [hdiv]
    exact digits_getLastD_mul_pow hf1 hf9 k

lemma digits_getLastD_mul_pow_add {f e k : ℕ} (hf1 : 1 ≤ f) (hf9 : f ≤ 9)
    (he9 : e ≤ 9) (hk : 1 ≤ k) :
    (Nat.digits 10 (f * 10 ^ k + e)).getLastD 0 = f := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h10 : 10 ≤ f * 10 ^ (m + 1) + e := by
    have hp : 1 ≤ 10 ^ m := Nat.one_le_pow m 10 (by decide)
    have h1 : 10 ≤ f * 10 ^ (m + 1) := by
      calc 10 = 1 * (1 * 10) := by omega
        _ ≤ f * (10 ^ m * 10) := Nat.mul_le_mul hf1 (Nat.mul_le_mul_right 10 hp)
        _ = f * 10 ^ (m + 1) := by rw [pow_succ]
    omega
  rw [digits_getLastD_div h10]
  have hdiv : (f * 10 ^ (m + 1) + e) / 10 = f * 10 ^ m := by
    rw [pow_succ, ← mul_assoc]
    omega
  rw [hdiv]
  exact digits_getLastD_mul_pow hf1 hf9 m

lemma list_mem_le_sum {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.mem_cons] at hx
    simp only [List.sum_cons]
    rcases hx with rfl | ht
    · omega
    · have := ih ht; omega

lemma cand_nonempty (used : List ℕ) (hmod : used.headD 1 % 10 ≠ 0) :
    {y : ℕ | y ∉ used ∧ 0 < y ∧ allowed (used.headD 1) y}.Nonempty := by
  have hd1 : 1 ≤ used.headD 1 % 10 := by omega
  have hd9 : used.headD 1 % 10 ≤ 9 := by omega
  obtain ⟨f, hf, hpf⟩ := exists_paired_1_or_3 hd1 hd9
  have hf1 : 1 ≤ f := by rcases hf with rfl | rfl <;> omega
  have hf9 : f ≤ 9 := by rcases hf with rfl | rfl <;> omega
  let k := used.sum + 1
  let y := f * 10 ^ k + 1
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · intro hmem
    have hle : y ≤ used.sum := list_mem_le_sum hmem
    have hpow : k < 10 ^ k := Nat.lt_pow_self (by decide : 1 < 10)
    have hy : k < y := by
      have : 10 ^ k ≤ f * 10 ^ k := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega
  · omega
  · have hmul : 10 ∣ f * 10 ^ k := by
      have hk : 1 ≤ k := by omega
      obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [hm, pow_succ, ← mul_assoc]
      exact dvd_mul_left 10 _
    obtain ⟨q, hq⟩ := hmul
    show (f * 10 ^ k + 1) % 10 ≠ 0
    rw [hq]
    omega
  · rw [digits_getLastD_mul_pow_add hf1 hf9 (by omega) (by omega)]
    exact hpf

lemma history_headD_mod (n : ℕ) :
    (history n).headD 1 % 10 ≠ 0 ∧ 0 < (history n).headD 1 := by
  induction n with
  | zero =>
    simp [history]
  | succ n ih =>
    have hne := cand_nonempty (history n) ih.1
    have hmem : next (history n) ∈ {y : ℕ | y ∉ history n ∧ 0 < y ∧ allowed ((history n).headD 1) y} :=
      Nat.sInf_mem hne
    have hhead : (history (n + 1)).headD 1 = next (history n) := rfl
    rw [hhead]
    exact ⟨hmem.2.2.1, hmem.2.1⟩

lemma term_pos (n : ℕ) : 0 < term n := (history_headD_mod n).2

lemma term_mod_ne_zero (n : ℕ) : term n % 10 ≠ 0 := (history_headD_mod n).1

lemma term_succ_mem_cand (n : ℕ) :
    term (n + 1) ∉ history n ∧ 0 < term (n + 1) ∧ allowed (term n) (term (n + 1)) := by
  have hne := cand_nonempty (history n) (history_headD_mod n).1
  have hmem := Nat.sInf_mem hne
  exact hmem

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
    (hallow : allowed (term n) y) : term (n + 1) ≤ y := by
  exact Nat.sInf_le ⟨hnot, hpos, hallow⟩

lemma mem_range_of_infinite_lastDigit {d f m : ℕ}
    (hinf : {n : ℕ | term n % 10 = d}.Infinite)
    (hpf : paired d f)
    (hm_pos : 0 < m)
    (hm_mod : m % 10 ≠ 0)
    (hm_first : (Nat.digits 10 m).getLastD 0 = f) :
    ∃ n : ℕ, term n = m := by
  by_contra hnot
  push Not at hnot
  have hle : ∀ n ∈ {n : ℕ | term n % 10 = d}, term (n + 1) ≤ m := by
    intro n hn
    have hmem_not : m ∉ history n := by
      intro hmem
      obtain ⟨i, _, hi⟩ := (mem_history_iff n m).mp hmem
      exact hnot i hi
    have hallow : allowed (term n) m := by
      refine ⟨hm_mod, ?_⟩
      rw [hn, hm_first]
      exact hpf
    exact term_succ_le_of_cand hmem_not hm_pos hallow
  have hinj : Function.Injective (fun n : ℕ => term (n + 1)) :=
    term_injective.comp (fun _ _ h => by omega)
  have himg_inf : ((fun n : ℕ => term (n + 1)) '' {n : ℕ | term n % 10 = d}).Infinite :=
    hinf.image (hinj.injOn)
  have himg_sub : ((fun n : ℕ => term (n + 1)) '' {n : ℕ | term n % 10 = d}) ⊆
      (Finset.range (m + 1) : Set ℕ) := by
    rintro y ⟨n, hn, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    have := hle n hn
    omega
  exact himg_inf ((Finset.finite_toSet _).subset himg_sub)

lemma exists_infinite_lastDigit :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ 9 ∧ {n : ℕ | term n % 10 = d}.Infinite := by
  have hunion : (Set.univ : Set ℕ) ⊆ ⋃ d ∈ (Finset.Icc 1 9 : Finset ℕ), {n : ℕ | term n % 10 = d} := by
    intro n _
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_Icc]
    have hmod := term_mod_ne_zero n
    exact ⟨term n % 10, ⟨by omega, by omega⟩, rfl⟩
  by_contra hall
  push Not at hall
  have hfin : (⋃ d ∈ (Finset.Icc 1 9 : Finset ℕ), {n : ℕ | term n % 10 = d}).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
    intro d hd
    simp only [Finset.mem_coe, Finset.mem_Icc] at hd
    exact hall d hd.1 hd.2
  exact Set.infinite_univ (hfin.subset hunion)

lemma all_lastDigits_infinite {e : ℕ} (he1 : 1 ≤ e) (he9 : e ≤ 9) :
    {n : ℕ | term n % 10 = e}.Infinite := by
  obtain ⟨d0, hd1, hd9, hd_inf⟩ := exists_infinite_lastDigit
  obtain ⟨f0, hf0, hpf0⟩ := exists_paired_1_or_3 hd1 hd9
  have hf1 : 1 ≤ f0 := by rcases hf0 with rfl | rfl <;> omega
  have hf9 : f0 ≤ 9 := by rcases hf0 with rfl | rfl <;> omega
  have hex : ∀ k : ℕ, ∃ n : ℕ, term n = f0 * 10 ^ (k + 1) + e := by
    intro k
    have hpos : 0 < f0 * 10 ^ (k + 1) + e := by omega
    have hmod : (f0 * 10 ^ (k + 1) + e) % 10 = e := by
      rw [pow_succ, ← mul_assoc, Nat.mul_add_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    have hmod_ne : (f0 * 10 ^ (k + 1) + e) % 10 ≠ 0 := by omega
    have hfirst : (Nat.digits 10 (f0 * 10 ^ (k + 1) + e)).getLastD 0 = f0 :=
      digits_getLastD_mul_pow_add hf1 hf9 he9 (by omega)
    exact mem_range_of_infinite_lastDigit hd_inf hpf0 hpos hmod_ne hfirst
  choose g hg using hex
  have hg_inj : Function.Injective g := by
    intro k1 k2 h
    have hval : f0 * 10 ^ (k1 + 1) + e = f0 * 10 ^ (k2 + 1) + e := by
      rw [← hg k1, ← hg k2, h]
    have hpow : 10 ^ (k1 + 1) = 10 ^ (k2 + 1) := by
      have : f0 * 10 ^ (k1 + 1) = f0 * 10 ^ (k2 + 1) := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    have hk : k1 + 1 = k2 + 1 := Nat.pow_right_injective (by decide : 2 ≤ 10) hpow
    omega
  have hg_mem : ∀ k : ℕ, g k ∈ {n : ℕ | term n % 10 = e} := by
    intro k
    simp only [Set.mem_ofPred_eq, hg k]
    rw [pow_succ, ← mul_assoc, Nat.mul_add_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)
  exact (Set.infinite_range_of_injective hg_inj).mono (by
    rintro n ⟨k, rfl⟩
    exact hg_mem k)

end OMA_A350831_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a350831.main := by
  intro m hm_pos hm_mod
  let f := (Nat.digits 10 m).getLastD 0
  have ⟨hf1, hf9⟩ := OMA_A350831_Proof.digits_getLastD_bounds hm_pos
  obtain ⟨d, hd, hpd⟩ := OMA_A350831_Proof.exists_paired_1_or_3 hf1 hf9
  have hd1 : 1 ≤ d := by rcases hd with rfl | rfl <;> omega
  have hd9 : d ≤ 9 := by rcases hd with rfl | rfl <;> omega
  have hd_inf := OMA_A350831_Proof.all_lastDigits_infinite hd1 hd9
  exact OMA_A350831_Proof.mem_range_of_infinite_lastDigit hd_inf
    (OMA_A350831_Proof.paired_symm hpd) hm_pos hm_mod rfl
