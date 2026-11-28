import OMAStatements.S_oeis_a361074

/-!
# The asymptotic binary-weight diagonal sum in OEIS A361074

The first `k+1` numbers of binary weight `k` have exactly one missing bit among
positions `0,…,k`. These initial entries yield `8/3` after normalization.
Weight one gives an extra `1/2`. For larger ranks a two-variable-bit family
bounds each summand by a uniform summable geometric sequence.

Source: https://oeis.org/A361074
Credit: @gdyan2022
-/


namespace A361074
open Finset OMA.S_oeis_a361074

def code (s : Finset ℕ) : ℕ := ∑ p ∈ s, 2^p
def bits (x : ℕ) := x.bitIndices.toFinset

lemma code_bits (x : ℕ) : code (bits x) = x := by
  rw [code,bits,List.sum_toFinset _ Nat.bitIndices_nodup,Nat.sum_map_two_pow_bitIndices]

lemma code_list (s : Finset ℕ) : (code s).bitIndices = s.sort (· ≤ ·) := by
  have h := List.sum_toFinset (fun i : ℕ => 2^i) (s.sort_nodup (· ≤ ·))
  rw [s.sort_toFinset] at h
  rw [code,h,Nat.bitIndices_sum_map_two_pow s.sortedLT_sort]

lemma bits_code (s : Finset ℕ) : bits (code s) = s := by rw [bits,code_list,sort_toFinset]
lemma code_inj : Function.Injective code := Function.LeftInverse.injective bits_code
lemma code_weight (s : Finset ℕ) : (code s).bitIndices.length = s.card := by rw [code_list,length_sort]
lemma bits_card (x : ℕ) : (bits x).card = x.bitIndices.length := List.toFinset_card_of_nodup Nat.bitIndices_nodup
lemma code_range (k : ℕ) : code (range k) + 1 = 2^k := by
  induction k with
  | zero => simp [code]
  | succ k ih =>
    change (∑ p ∈ range (k+1), 2^p)+1 = _
    rw [sum_range_succ,pow_succ]; change code (range k) + 2^k + 1 = 2^k*2; omega

lemma bits_subset {x s : ℕ} (hx : x<2^s) : bits x ⊆ range s := by
  intro p hp
  have hm : p ∈ x.bitIndices := by simpa [bits] using hp
  have hi := (Nat.two_pow_le_of_mem_bitIndices hm).trans_lt hx
  apply mem_range.mpr; exact lt_of_not_ge (fun h => hi.not_ge (Nat.pow_le_pow_right (by decide) h))

def word (k i : ℕ) : ℕ := code ((range (k+1)).erase (k-i))

lemma word_weight (k i : ℕ) : (word k i).bitIndices.length = k := by
  rw [word,code_weight,card_erase_of_mem (by simp),card_range]; omega

lemma word_formula (k i : ℕ) : word k i + 1 + 2^(k-i) = 2^(k+1) := by
  have h := (range (k+1)).sum_erase_add (fun p : ℕ => 2^p) (a:=k-i) (by simp)
  change word k i + 2^(k-i) = code (range (k+1)) at h
  have hk := code_range (k+1)
  omega

lemma word_lt (k i : ℕ) : word k i < 2^(k+1) := by
  calc
    word k i < word k i+1+2^(k-i) := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
    _ = _ := word_formula k i
lemma word_lt_iff {k i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) : word k i < word k j ↔ i<j := by
  have a := word_formula k i; have b := word_formula k j
  have e : 2^(k-j) < 2^(k-i) ↔ k-j < k-i := Nat.pow_lt_pow_iff_right (by decide)
  omega

lemma words_complete {k x : ℕ} (hx : x < 2^(k+1)) (hw : x.bitIndices.length = k) :
    ∃ i ≤ k, x = word k i := by
  have hs := bits_subset hx
  have hc : ((range (k+1)) \ bits x).card = 1 := by rw [card_sdiff_of_subset hs,card_range,bits_card,hw]; omega
  obtain ⟨d, hd⟩ := card_eq_one.mp hc
  have hmem : d ∈ (range (k+1)) \ bits x := by rw [hd]; simp
  have hdle : d ≤ k := by simpa using (mem_sdiff.mp hmem).1
  have hsub := Finset.sdiff_sdiff_eq_self hs
  rw [hd,sdiff_singleton_eq_erase] at hsub
  refine ⟨k-d,by omega,?_⟩
  rw [word,show k-(k-d)=d by omega,hsub,code_bits]

lemma entry_word {k i : ℕ} (hi : i ≤ k) : weightEntry k i = word k i := by
  let pred := fun x : ℕ => x.bitIndices.length = k
  have hset : ((range (word k i)).filter pred) = (range i).image (word k) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hr,hw⟩ := mem_filter.mp hx
      have hxi := mem_range.mp hr
      obtain ⟨j,hj,rfl⟩ := words_complete (hxi.trans (word_lt k i)) hw
      exact mem_image.mpr ⟨j,mem_range.mpr ((word_lt_iff hj hi).mp hxi),rfl⟩
    · intro hx
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
      have hji := mem_range.mp hj
      exact mem_filter.mpr ⟨mem_range.mpr ((word_lt_iff (by omega) hi).mpr hji),word_weight ..⟩
  have hcount : Nat.count pred (word k i) = i := by
    rw [Nat.count_eq_card_filter_range,hset,card_image_of_injOn,card_range]
    intro x hx y hy hxy
    have hx' := mem_range.mp hx; have hy' := mem_range.mp hy
    have a := word_lt_iff (k:=k) (i:=x) (j:=y) (by omega) (by omega)
    have b := word_lt_iff (k:=k) (i:=y) (j:=x) (by omega) (by omega)
    omega
  calc
    weightEntry k i = Nat.nth pred (Nat.count pred (word k i)) := congrArg (Nat.nth pred) hcount.symm
    _ = _ := Nat.nth_count (p:=pred) (word_weight k i)

theorem initialLayer (k i : ℕ) (hi : i≤k) : weightEntry k i + 1 + 2^(k-i) = 2^(k+1) := by
  rw [entry_word hi,word_formula]

end A361074
namespace A361074
open Finset OMA.S_oeis_a361074

theorem weightOne (i : ℕ) : weightEntry 1 i = 2^i := by
  let pred := fun x : ℕ => x.bitIndices.length = 1
  have hset : (range (2^i)).filter pred = (range i).image ((2:ℕ)^·) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hr,hw⟩ := mem_filter.mp hx
      have hc : (bits x).card=1 := (bits_card x).trans hw
      obtain ⟨d,hd⟩ := card_eq_one.mp hc
      have hx' := code_bits x
      rw [hd,code,sum_singleton] at hx'
      apply mem_image.mpr
      exact ⟨d,mem_range.mpr ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hx' ▸ mem_range.mp hr)),hx'⟩
    · intro hx
      obtain ⟨d,hd,rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_range.mpr ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (mem_range.mp hd)),by simp [pred]⟩
  have hc : Nat.count pred (2^i) = i := by
    rw [Nat.count_eq_card_filter_range,hset,card_image_of_injective,card_range]
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2))
  calc
    weightEntry 1 i = Nat.nth pred (Nat.count pred (2^i)) := congrArg (Nat.nth pred) hc.symm
    _ = _ := Nat.nth_count (p:=pred) (by simp [pred])

def candidate (k r : ℕ) : Finset ℕ := insert (k+r/2) (insert (k-2+r%2) (range (k-2)))

lemma candidate_card {k : ℕ} (hk : 2≤k) (r : ℕ) : (candidate k r).card = k := by
  have h1 : k-2+r%2 ∉ range (k-2) := by simp
  have h2 : k+r/2 ∉ insert (k-2+r%2) (range (k-2)) := by simp only [mem_insert,mem_range]; omega
  rw [candidate,card_insert_of_notMem h2,card_insert_of_notMem h1,card_range]; omega

lemma candidate_injective {k : ℕ} (hk : 2≤k) : Function.Injective (candidate k) := by
  intro r t h
  have hm (r t : ℕ) (hh : candidate k r = candidate k t) :
      k+r/2 ∈ candidate k t ∧ k-2+r%2 ∈ candidate k t := by rw [← hh]; simp [candidate]
  have ⟨hr,hl⟩ := hm r t h
  simp only [candidate,mem_insert,mem_range] at hr hl
  omega

lemma candidate_lt {k r i : ℕ} (hk : 2≤k) (hr : r ≤ i) : code (candidate k r) < 2^(k+i/2+1) := by
  have hs : candidate k r ⊆ range (k+i/2+1) := by
    intro d hd; simp only [candidate,mem_insert,mem_range] at *; omega
  have hc : code (candidate k r) ≤ code (range (k+i/2+1)) := by
    unfold code; exact sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
  have hh := code_range (k+i/2+1)
  omega

theorem tailBound (k i : ℕ) (hk : 2 ≤ k) : weightEntry k i < 2^(k+i/2+1) := by
  let pred := fun x : ℕ => x.bitIndices.length = k
  apply Nat.nth_lt_of_lt_count (p:=pred)
  rw [Nat.count_eq_card_filter_range]
  have hs := Finset.card_le_card_of_injOn (s:=range (i+1)) (t:=(range (2^(k+i/2+1))).filter pred)
    (fun r => code (candidate k r)) (by
      intro r hr
      exact mem_filter.mpr ⟨mem_range.mpr (candidate_lt hk (by simpa using mem_range.mp hr)),(code_weight _).trans (candidate_card hk _)⟩)
    ((code_inj.comp (candidate_injective hk)).injOn)
  rw [card_range] at hs
  simpa using Nat.lt_of_succ_le hs

end A361074

namespace BinaryDiagonal
open Filter Finset OMA.S_oeis_a361074
open scoped Topology BigOperators

private noncomputable def cell (n i : ℕ) : ℝ :=
  if i+2 ≤ n then (weightEntry (n-i) i : ℝ) / 2^n else 0

private noncomputable def limitCell (i : ℕ) : ℝ := 2 * (1/2:ℝ)^i - (1/4:ℝ)^i

private lemma half_pow (i : ℕ) : (2:ℝ)^(i/2) ≤ (3/2:ℝ)^i := by
  induction i using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n h _ =>
    rw [show (n+2)/2=n/2+1 by omega, pow_succ, pow_add]
    have hp : 0 ≤ (3/2:ℝ)^n := by positivity
    nlinarith

private theorem cell_bound
    (tail : ∀ k i, 2 ≤ k → weightEntry k i < 2^(k+i/2+1)) (n i : ℕ) :
    ‖cell n i‖ ≤ 2*(3/4:ℝ)^i := by
  unfold cell
  split_ifs with hh
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    let k := n-i
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hn : n=k+i := by dsimp [k]; omega
    have bound : (weightEntry k i : ℝ) ≤ (2:ℝ)^(k+i/2+1) := by exact_mod_cast (tail k i hk).le
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^n)).mpr
    apply bound.trans
    rw [hn, pow_succ, pow_add, pow_add]
    calc
      _ ≤ (2:ℝ)^k * (3/2:ℝ)^i * 2 := by gcongr; exact half_pow i
      _ = _ := by rw [show (3/2:ℝ)^i = (3/4:ℝ)^i * 2^i by rw [← mul_pow]; norm_num]; ring
  · simp only [norm_zero]
    positivity

private theorem cell_limit
    (near : ∀ k i, i ≤ k → weightEntry k i + 1 + 2^(k-i) = 2^(k+1)) (i : ℕ) :
    Tendsto (fun n => cell n i) atTop (𝓝 (limitCell i)) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have hl := (tendsto_const_nhds (x := limitCell i)).sub hpow
  rw [sub_zero] at hl
  refine hl.congr' ?_
  filter_upwards [eventually_ge_atTop (i+i+2)] with n hn
  let t := n-i-i
  have hn' : n=t+i+i := by dsimp [t]; omega
  have hw : (weightEntry (t+i) i:ℝ) + 1 + 2^t = (2:ℝ)^(t+i+1) := by
    exact_mod_cast (show weightEntry (t+i) i + 1 + 2^t = 2^(t+i+1) by simpa using near (t+i) i (by omega))
  have hc : i+2 ≤ n := by omega
  simp only [cell, if_pos hc, limitCell]
  rw [hn']
  simp only [Nat.add_sub_cancel]
  have h4 : (1/4:ℝ)^i = (1/2:ℝ)^i * (1/2:ℝ)^i := by rw [← mul_pow]; norm_num
  rw [h4]
  simp only [one_div, inv_pow, pow_add, pow_one] at hw ⊢
  field_simp
  linarith

private theorem sum_limitCell : ∑' i, limitCell i = 8/3 := by
  have h1 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have h2 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)
  convert ((h1.mul_left 2).sub h2).tsum_eq using 1 <;> norm_num [limitCell]

theorem from_entries
    (near : ∀ k i, i ≤ k → weightEntry k i + 1 + 2^(k-i) = 2^(k+1))
    (one : ∀ i, weightEntry 1 i = 2^i)
    (tail : ∀ k i, 2 ≤ k → weightEntry k i < 2^(k+i/2+1)) :
    type_of% @OMA.S_oeis_a361074.main := by
  have hbound := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖ < 1)).summable.mul_left 2
  have hs := tendsto_tsum_of_dominated_convergence hbound (cell_limit near)
    (Eventually.of_forall (cell_bound tail))
  rw [sum_limitCell] at hs
  have hh := hs.add (tendsto_const_nhds (x := (1/2:ℝ)))
  norm_num at hh
  refine hh.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  change (∑' i, cell (m+1) i) + 1/2 = (a (m+1):ℝ) / 2^(m+1)
  rw [tsum_eq_sum (s := range m) (fun j hj => by
    have : ¬j+2 ≤ m+1 := by simp only [mem_range, not_lt] at hj; omega
    simp [cell, this])]
  have he (j : ℕ) (hj : j ∈ range m) : cell (m+1) j = (weightEntry (m+1-j) j:ℝ)/2^(m+1) := by
    have := mem_range.mp hj
    simp [cell, show j+2 ≤ m+1 by omega]
  rw [sum_congr rfl he, ← sum_div, a, sum_range_succ]
  push_cast
  simp only [Nat.add_sub_cancel_left, one, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring
end BinaryDiagonal

theorem OMA.solution : type_of% @OMA.S_oeis_a361074.main :=
  BinaryDiagonal.from_entries A361074.initialLayer A361074.weightOne A361074.tailBound
