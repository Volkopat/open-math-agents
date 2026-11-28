import OMAStatements.S_oeis_a342591

/-!
Six coprime integers in the interval `(k / 3, 2 * k / 5]` suffice because each
contributes at least `k / 5` to the sum. For large `k`, Möbius inversion bounds
the count in this interval below by `φ(k) / 15 - 2^ω(k)`. The finite ranges are
checked with Boolean computations whose reductions are verified by Lean's kernel.
-/

namespace A342591Remainders

open Finset

lemma interval_remainder (k j : ℕ) (h₁ : k < 3*j) (h₂ : 5*j ≤ 2*k) :
    k ≤ 5 * (k % j) := by
  have hj : 0 < j := by omega
  have hdiv : k / j = 2 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have heq := Nat.mod_add_div k j
  rw [hdiv] at heq
  omega

lemma reduction_six (k : ℕ) (hk : 0 < k)
    (s : Finset ℕ)
    (hcard : 6 ≤ s.card)
    (hmem : ∀ j ∈ s, 1 ≤ j ∧ j ≤ k / 2 ∧ Nat.Coprime j k ∧ k < 3*j ∧ 5*j ≤ 2*k) :
    k < OMA.S_oeis_a342591.a340740 k := by
  let t := (Icc 1 (k / 2)).filter (fun j => Nat.Coprime j k)
  have hsub : s ⊆ t := by
    intro j hj
    obtain ⟨h1, h2, h3, _, _⟩ := hmem j hj
    simp only [t, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨h1, h2⟩, h3⟩
  have hsum : (∑ j ∈ s, k) ≤ ∑ j ∈ s, 5 * (k % j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact interval_remainder k j (hmem j hj).2.2.2.1 (hmem j hj).2.2.2.2
  have hbound : (∑ j ∈ s, k % j) ≤ ∑ j ∈ t, k % j := Finset.sum_le_sum_of_subset hsub
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  unfold OMA.S_oeis_a342591.a340740
  change k < ∑ j ∈ t, k % j
  nlinarith


open Finset

def window (k : ℕ) : List ℕ := (List.range 31).map (fun i => k / 3 + 1 + i)
def good (k j : ℕ) : Bool := (k < 3*j) && (5*j ≤ 2*k) && (Nat.gcd j k == 1)
def wins (k : ℕ) : Bool := 6 ≤ ((window k).filter (good k)).length

lemma window_nodup (k : ℕ) : (window k).Nodup := by
  unfold window
  apply List.Nodup.map
  · intro a b h
    dsimp at h
    omega
  · exact List.nodup_range

lemma wins_reduction (k : ℕ) (hk : 0 < k) (h : wins k = true) :
    k < OMA.S_oeis_a342591.a340740 k := by
  let l := (window k).filter (good k)
  let s := l.toFinset
  have hcard : 6 ≤ s.card := by
    have hn : l.Nodup := (window_nodup k).filter _
    rw [show s = l.toFinset from rfl, List.toFinset_card_of_nodup hn]
    simpa [wins, l] using h
  apply reduction_six k hk s hcard
  intro j hj
  have hj' : j ∈ l := by simpa [s] using hj
  have hg : good k j = true := (List.mem_filter.mp hj').2
  have hh : k < 3*j ∧ 5*j ≤ 2*k ∧ Nat.gcd j k = 1 := by
    simpa [good, and_assoc] using hg
  refine ⟨?_, ?_, hh.2.2, hh.1, hh.2.1⟩ <;> omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma batch0 : ((List.range 500).map (· + 331)).all wins = true := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma batch1 : ((List.range 500).map (· + 831)).all wins = true := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma batch2 : ((List.range 500).map (· + 1331)).all wins = true := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma batch3 : ((List.range 500).map (· + 1831)).all wins = true := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma batch4 : ((List.range 500).map (· + 2331)).all wins = true := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma batch5 : ((List.range 169).map (· + 2831)).all wins = true := by decide

lemma batch_elim (a n k : ℕ) (h : ((List.range n).map (· + a)).all wins = true)
    (h1 : a ≤ k) (h2 : k < a + n) : wins k = true := by
  apply (List.all_eq_true.mp h) k
  apply List.mem_map.mpr
  refine ⟨k-a, List.mem_range.mpr (by omega), ?_⟩
  omega

theorem wins_finite (k : ℕ) (h1 : 331 ≤ k) (h2 : k < 3000) : wins k = true := by
  by_cases h : k < 831
  · exact batch_elim 331 500 k batch0 (by omega) (by omega)
  by_cases h' : k < 1331
  · exact batch_elim 831 500 k batch1 (by omega) (by omega)
  by_cases h'' : k < 1831
  · exact batch_elim 1331 500 k batch2 (by omega) (by omega)
  by_cases h''' : k < 2331
  · exact batch_elim 1831 500 k batch3 (by omega) (by omega)
  by_cases h'''' : k < 2831
  · exact batch_elim 2331 500 k batch4 (by omega) (by omega)
  · exact batch_elim 2831 169 k batch5 (by omega) (by omega)

end A342591Remainders

namespace A342591Small

open Finset

def sumRemainders (k : ℕ) : ℕ :=
  ∑ j ∈ (Icc 1 (k / 2)).filter (fun j => Nat.Coprime j k), k % j

private def scan (start length : ℕ) : Bool :=
  (List.range length).all fun j => decide (start + j < sumRemainders (start + j))

private lemma scan_spec (start length k : ℕ) (h : scan start length = true)
    (hstart : start ≤ k) (hstop : k < start + length) :
    k < sumRemainders k := by
  unfold scan at h
  have hx := List.all_eq_true.mp h (k - start) (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_of_le hstart] at hx
  exact of_decide_eq_true hx

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked79 : scan 79 24 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked103 : scan 103 24 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked127 : scan 127 24 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked151 : scan 151 24 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked175 : scan 175 24 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked199 : scan 199 24 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked223 : scan 223 24 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked247 : scan 247 24 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked271 : scan 271 24 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked295 : scan 295 24 = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma checked319 : scan 319 12 = true := by decide

lemma low (k : ℕ) (hk : 78 < k) (hmax : k ≤ 330) : k < sumRemainders k := by
  by_cases h79 : k < 103
  · exact scan_spec 79 24 k checked79 (by omega) (by omega)
  by_cases h103 : k < 127
  · exact scan_spec 103 24 k checked103 (by omega) (by omega)
  by_cases h127 : k < 151
  · exact scan_spec 127 24 k checked127 (by omega) (by omega)
  by_cases h151 : k < 175
  · exact scan_spec 151 24 k checked151 (by omega) (by omega)
  by_cases h175 : k < 199
  · exact scan_spec 175 24 k checked175 (by omega) (by omega)
  by_cases h199 : k < 223
  · exact scan_spec 199 24 k checked199 (by omega) (by omega)
  by_cases h223 : k < 247
  · exact scan_spec 223 24 k checked223 (by omega) (by omega)
  by_cases h247 : k < 271
  · exact scan_spec 247 24 k checked247 (by omega) (by omega)
  by_cases h271 : k < 295
  · exact scan_spec 271 24 k checked271 (by omega) (by omega)
  by_cases h295 : k < 319
  · exact scan_spec 295 24 k checked295 (by omega) (by omega)
  exact scan_spec 319 12 k checked319 (by omega) (by omega)

end A342591Small

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace A342591IntervalCount

open Finset Nat

private lemma card_multiples (a b d : ℕ) (hab : a ≤ b) :
    ((Ioc a b).filter fun j => d ∣ j).card = b/d - a/d := by
  have hsplit : (Ioc 0 b).filter (fun j => d ∣ j) =
      (Ioc 0 a).filter (fun j => d ∣ j) ∪ (Ioc a b).filter (fun j => d ∣ j) := by
    ext j
    simp only [mem_filter, mem_Ioc, mem_union]
    omega
  have hd : Disjoint ((Ioc 0 a).filter fun j => d ∣ j)
      ((Ioc a b).filter fun j => d ∣ j) := by
    refine disjoint_left.mpr fun j hj hj' => ?_
    simp only [mem_filter, mem_Ioc] at hj hj'
    omega
  have h := congrArg card hsplit
  rw [card_union_of_disjoint hd, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at h
  omega

private lemma moebius_coprime (n j : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, if d ∣ j then (μ d : ℚ) else 0) =
      if j.Coprime n then 1 else 0 := by
  have hg : j.gcd n ≠ 0 := by
    intro h
    have hd := Nat.gcd_dvd_right j n
    rw [h, zero_dvd_iff] at hd
    exact hn hd
  have hs : n.divisors.filter (fun d => d ∣ j) = (j.gcd n).divisors := by
    ext d
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hn, hg, and_comm]
  rw [← sum_filter, hs]
  have hμ : (∑ d ∈ (j.gcd n).divisors, μ d) =
      (1 : ArithmeticFunction ℤ) (j.gcd n) := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta]
  rw [← Int.cast_sum, hμ, ArithmeticFunction.one_apply]
  by_cases h : j.gcd n = 1
  · have h' : j.Coprime n := h
    simp [h, h']
  · have h' : ¬ j.Coprime n := h
    simp [h, h']

private lemma card_coprime_Ioc (n a b : ℕ) (hn : n ≠ 0) (hab : a ≤ b) :
    (((Ioc a b).filter fun j => j.Coprime n).card : ℚ) =
      ∑ d ∈ n.divisors, (μ d : ℚ) * ((b/d : ℕ) - (a/d : ℕ) : ℚ) := by
  rw [card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one]
  rw [sum_filter]
  simp_rw [← moebius_coprime n _ hn]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter, sum_const, nsmul_eq_mul, card_multiples a b d hab, mul_comm]
  have hdiv := Nat.div_le_div_right (c := d) hab
  rw [Nat.cast_sub hdiv]

private lemma whole_interval (n : ℕ) (hn : n ≠ 0) :
    (n.totient : ℚ) = ∑ d ∈ n.divisors, (μ d : ℚ) * (n/d : ℕ) := by
  have h := card_coprime_Ioc n 0 n hn (Nat.zero_le n)
  rw [show Ioc 0 n = Ico 1 (1 + n) by ext x; simp [mem_Ioc, mem_Ico]; omega] at h
  have hs : (Ico 1 (1+n)).filter (fun j => j.Coprime n) =
      (Ico 1 (1+n)).filter (fun j => n.Coprime j) := by
    ext j
    simp only [mem_filter]
    exact and_congr_right fun _ => Nat.coprime_comm
  rw [hs, Nat.filter_coprime_Ico_eq_totient] at h
  simpa using h

private lemma cast_floor_bounds (n d : ℕ) (hd : 0 < d) :
    ((n/d : ℕ) : ℚ) ≤ (n : ℚ)/d ∧ (n : ℚ)/d < ((n/d : ℕ) : ℚ) + 1 := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  constructor
  · rw [le_div_iff₀ hd']
    exact_mod_cast Nat.div_mul_le_self n d
  · rw [div_lt_iff₀ hd']
    exact_mod_cast (Nat.div_lt_iff_lt_mul hd).1 (Nat.lt_succ_self (n/d))

private lemma approximate_multiples (n d : ℕ) (hd : d ∈ n.divisors) :
    |(((2*n/5/d : ℕ) : ℚ) - ((n/3/d : ℕ) : ℚ)) - ((n/d : ℕ) : ℚ)/15| ≤ 1 := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have ha := cast_floor_bounds n (3*d) (by positivity)
  have hb := cast_floor_bounds (2*n) (5*d) (by positivity)
  have hcast : ((n/d : ℕ) : ℚ) = (n : ℚ)/d :=
    Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast hdpos.ne')
  rw [hcast, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  push_cast at ha hb
  have hdiff : (2 * (n : ℚ)) / (5 * d) - (n : ℚ)/(3*d) = (n : ℚ)/d/15 := by
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
    field_simp
    ring
  rw [← hdiff, abs_le]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

private lemma moebius_error_count (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, |(μ d : ℚ)|) = (2 : ℚ)^n.primeFactors.card := by
  open UniqueFactorizationMonoid in
    have hset : n.divisors.filter (fun d => Squarefree d) = (radical n).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd, _⟩, hs⟩
        exact ⟨(dvd_radical_iff hs.isRadical hn).2 hd, radical_ne_zero⟩
      · rintro ⟨hd, _⟩
        exact ⟨⟨hd.trans radical_dvd_self, hn⟩, squarefree_radical.squarefree_of_dvd hd⟩
    have hc : ((radical n).divisors.card : ℚ) = (2 : ℚ)^n.primeFactors.card := by
      rw [Nat.card_divisors radical_ne_zero, Nat.cast_prod]
      have hs : Squarefree (radical n) := squarefree_radical
      have hfact p (hp : p ∈ (radical n).primeFactors) : (radical n).factorization p = 1 := by
        have hsupport : p ∈ (radical n).factorization.support := by
          rwa [Nat.support_factorization]
        have hp0 : 0 < (radical n).factorization p :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hsupport)
        have hp1 := (Nat.squarefree_iff_factorization_le_one radical_ne_zero).1 hs p
        omega
      trans ∏ p ∈ (radical n).primeFactors, (2 : ℚ)
      · refine prod_congr rfl fun p hp => ?_
        norm_num [hfact p hp]
      · rw [prod_const, Nat.primeFactors_radical]
    have hμ d : |(μ d : ℚ)| = if Squarefree d then 1 else 0 := by
      rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
      split_ifs <;> norm_num
    simp_rw [hμ]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, hset, hc]

theorem six_residues (n : ℕ) (hn : n ≠ 0)
    (hphi : 15*(2^n.primeFactors.card + 6) ≤ n.totient) :
    6 ≤ ((Ioc (n/3) (2*n/5)).filter fun j => j.Coprime n).card := by
  have hab : n/3 ≤ 2*n/5 := by omega
  have hcard := card_coprime_Ioc n (n/3) (2*n/5) hn hab
  have hmain := whole_interval n hn
  have herr := moebius_error_count n hn
  have hs :
      (∑ d ∈ n.divisors, ((μ d : ℚ) * ((n/d : ℕ) : ℚ)/15 - |(μ d : ℚ)|)) ≤
        ∑ d ∈ n.divisors, (μ d : ℚ) * ((2*n/5/d : ℕ) - (n/3/d : ℕ) : ℚ) := by
    refine sum_le_sum fun d hd => ?_
    have h := abs_le.mp (approximate_multiples n d hd)
    rcases ArithmeticFunction.moebius_eq_or d with hμ | hμ | hμ <;>
      rw [hμ] <;> norm_num <;> linarith
  simp_rw [sum_sub_distrib, div_eq_mul_inv, ← sum_mul] at hs
  rw [← hmain, herr, ← hcard] at hs
  have hphi' : (15 : ℚ)*((2 : ℚ)^n.primeFactors.card + 6) ≤ n.totient := by
    exact_mod_cast hphi
  have ht : (6 : ℚ) ≤ (((Ioc (n/3) (2*n/5)).filter fun j => j.Coprime n).card : ℚ) := by
    linarith
  exact_mod_cast ht

end A342591IntervalCount

namespace A342591Many

open scoped BigOperators

private def w (p : ℕ) : ℚ := ((p - 1 : ℕ) : ℚ) / 10
private def small : Finset ℕ := {2, 3, 5, 7}

private lemma large_prime (p : ℕ) (hp : p.Prime) (h : p ∉ small) : 11 ≤ p := by
  have h2 := hp.two_le
  by_contra hn
  have hp' : p < 11 := by omega
  interval_cases p <;> norm_num [small, Nat.prime_def_lt] at *

private lemma w_nonneg (p : ℕ) : 0 ≤ w p := by
  unfold w
  positivity

private lemma prod_bound (n : ℕ) : (3/625 : ℚ) ≤ ∏ p ∈ n.primeFactors, w p := by
  let s := n.primeFactors
  have h1 : (∏ p ∈ small, w p) ≤ ∏ p ∈ small ∪ s, w p := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_union_left) (fun i hi => w_nonneg i)
    intro i hi his
    have hip : i ∈ s := (Finset.mem_union.mp hi).resolve_left his
    have hp : i.Prime := Nat.prime_of_mem_primeFactors hip
    have h11 := large_prime i hp his
    unfold w
    have : 10 ≤ i - 1 := by omega
    have hc : (10:ℚ) ≤ ((i-1:ℕ):ℚ) := by exact_mod_cast this
    exact (le_div_iff₀ (by norm_num : (0:ℚ) < 10)).2 (by simpa using hc)
  have h2 : (∏ p ∈ small ∪ s, w p) ≤ ∏ p ∈ s, w p := by
    apply Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_union_right) (fun i hi => w_nonneg i)
    intro i hi his
    have him : i ∈ small := (Finset.mem_union.mp hi).resolve_right his
    simp only [small, Finset.mem_insert, Finset.mem_singleton] at him
    rcases him with rfl | rfl | rfl | rfl <;> norm_num [w]
  have h3 : (∏ p ∈ small, w p) = (3/625 : ℚ) := by norm_num [small, w, Finset.prod_insert]
  rw [h3] at h1
  exact h1.trans h2

private lemma totient_product (n : ℕ) (hn : 0 < n) :
    (∏ p ∈ n.primeFactors, (p - 1)) ≤ n.totient := by
  rw [Nat.totient_eq_div_primeFactors_mul]
  have hdiv : 1 ≤ n / ∏ p ∈ n.primeFactors, p := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
    · apply Finset.prod_pos
      intro p hp
      exact Nat.pos_of_mem_primeFactors hp
  exact Nat.le_mul_of_pos_left _ hdiv

private lemma pow_bound (m : ℕ) (hm : 6 ≤ m) :
    (15 * (2^m + 6) : ℚ) ≤ (3/625 : ℚ) * 10^m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hp : (2:ℚ)^t ≤ 10^t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
  have hp1 : (1:ℚ) ≤ 2^t := one_le_pow₀ (by norm_num)
  rw [pow_add, pow_add]
  norm_num at *
  nlinarith

theorem totient_many (n : ℕ) (hn : 0 < n) (h : 6 ≤ n.primeFactors.card) :
    15 * (2^n.primeFactors.card + 6) ≤ n.totient := by
  have hp := prod_bound n
  have hprod : (∏ p ∈ n.primeFactors, w p) =
      ((∏ p ∈ n.primeFactors, (p-1) : ℕ) : ℚ) / 10^n.primeFactors.card := by
    rw [Nat.cast_prod]
    simp [w, Finset.prod_div_distrib, Finset.prod_const]
  rw [hprod] at hp
  have hpow : (0:ℚ) < 10^n.primeFactors.card := by positivity
  have hp' := (le_div_iff₀ hpow).mp hp
  have ht : ((∏ p ∈ n.primeFactors, (p-1) : ℕ) : ℚ) ≤ n.totient := by
    exact_mod_cast totient_product n hn
  have hb := pow_bound n.primeFactors.card h
  exact_mod_cast hb.trans (hp'.trans ht)

end A342591Many

namespace A342591Few

open scoped BigOperators
private def small : Finset ℕ := {2, 3, 5, 7, 11}
private def w (p : ℕ) : ℚ := (1 - (p : ℚ)⁻¹) / (12/13)

private lemma large_prime (p : ℕ) (hp : p.Prime) (h : p ∉ small) : 13 ≤ p := by
  have h2 := hp.two_le
  by_contra hn
  have hp' : p < 13 := by omega
  interval_cases p <;> norm_num [small, Nat.prime_def_lt] at *

private lemma prime_small (p : ℕ) (hp : p ∈ small) : p.Prime := by
  simp only [small, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma w_nonneg (p : ℕ) (hp : p.Prime) : 0 ≤ w p := by
  have hp' : (1:ℚ) ≤ p := by exact_mod_cast (show 1 ≤ p by have := hp.two_le; omega)
  have hp0 : (0:ℚ) < p := by positivity
  have hi : (p:ℚ)⁻¹ ≤ 1 := (inv_le_one₀ hp0).2 hp'
  unfold w
  positivity

private lemma prod_bound (n : ℕ) : (∏ p ∈ small, w p) ≤ ∏ p ∈ n.primeFactors, w p := by
  let s := n.primeFactors
  have h1 : (∏ p ∈ small, w p) ≤ ∏ p ∈ small ∪ s, w p := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_union_left) (fun i hi => w_nonneg i (prime_small i hi))
    intro i hi his
    have hip : i ∈ s := (Finset.mem_union.mp hi).resolve_left his
    have hp : i.Prime := Nat.prime_of_mem_primeFactors hip
    have h13 := large_prime i hp his
    have hpq : (13:ℚ) ≤ i := by exact_mod_cast h13
    have hp0 : (0:ℚ) < i := by positivity
    have hinv : (i:ℚ)⁻¹ ≤ (13:ℚ)⁻¹ := (inv_le_inv₀ hp0 (by norm_num)).2 hpq
    unfold w
    norm_num at *
    linarith
  have h2 : (∏ p ∈ small ∪ s, w p) ≤ ∏ p ∈ s, w p := by
    apply Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_union_right)
    · intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact w_nonneg i (prime_small i hi)
      · exact w_nonneg i (Nat.prime_of_mem_primeFactors hi)
    · intro i hi his
      have him : i ∈ small := (Finset.mem_union.mp hi).resolve_right his
      simp only [small, Finset.mem_insert, Finset.mem_singleton] at him
      rcases him with rfl | rfl | rfl | rfl | rfl <;> norm_num [w]
  exact h1.trans h2

private lemma factor_bound (n : ℕ) (h : n.primeFactors.card ≤ 5) :
    (16/77:ℚ) ≤ ∏ p ∈ n.primeFactors, (1 - (p:ℚ)⁻¹) := by
  have hb := prod_bound n
  have hc : (∏ p ∈ small, w p) = (16/77:ℚ) / ((12/13:ℚ)^5) := by norm_num [small, w, Finset.prod_insert]
  rw [hc] at hb
  have he : ((12/13:ℚ)^5) ≤ (12/13:ℚ)^n.primeFactors.card :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have hp : (0:ℚ) < (12/13:ℚ)^n.primeFactors.card := by positivity
  have hf : (∏ p ∈ n.primeFactors, w p) =
      (∏ p ∈ n.primeFactors, (1 - (p:ℚ)⁻¹)) / (12/13:ℚ)^n.primeFactors.card := by
    simp [w, Finset.prod_div_distrib, Finset.prod_const, div_pow]
  rw [hf] at hb
  have hmul := (le_div_iff₀ hp).mp hb
  have hpos : (0:ℚ) < (16/77:ℚ) / ((12/13:ℚ)^5) := by norm_num
  have := mul_le_mul_of_nonneg_left he (le_of_lt hpos)
  norm_num at *
  nlinarith

theorem totient_few (n : ℕ) (hn : 3000 ≤ n) (h : n.primeFactors.card ≤ 5) :
    15*(2^n.primeFactors.card+6) ≤ n.totient := by
  have hpow : 2^n.primeFactors.card ≤ 32 := by
    have := pow_le_pow_right₀ (show (1:ℕ) ≤ 2 by decide) h
    norm_num at this ⊢
    exact this
  have hfactor := factor_bound n h
  have htot := Nat.totient_eq_mul_prod_factors n
  have hnq : (3000:ℚ) ≤ n := by exact_mod_cast hn
  have hpq : ((2^n.primeFactors.card : ℕ):ℚ) ≤ 32 := by exact_mod_cast hpow
  have hn0 : (0:ℚ) ≤ n := by positivity
  have h := mul_le_mul_of_nonneg_left hfactor hn0
  rw [← htot] at h
  have hfpos : (0:ℚ) < 16/77 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hnq (le_of_lt hfpos)
  have hr : (15:ℚ) * ((2^n.primeFactors.card:ℕ) + 6) ≤ n.totient := by nlinarith
  exact_mod_cast hr

end A342591Few

theorem OMA.solution : type_of% @OMA.S_oeis_a342591.main := by
  intro k hk
  by_cases hl : k ≤ 330
  · exact A342591Small.low k hk hl
  by_cases hm : k < 3000
  · exact A342591Remainders.wins_reduction k (by omega)
      (A342591Remainders.wins_finite k (by omega) hm)
  have ht : 15 * (2 ^ k.primeFactors.card + 6) ≤ k.totient := by
    by_cases h : 6 ≤ k.primeFactors.card
    · exact A342591Many.totient_many k (by omega) h
    · exact A342591Few.totient_few k (by omega) (by omega)
  let s := (Finset.Ioc (k / 3) (2 * k / 5)).filter fun j => j.Coprime k
  apply A342591Remainders.reduction_six k (by omega) s
    (A342591IntervalCount.six_residues k (by omega) ht)
  intro j hj
  simp only [s, Finset.mem_filter, Finset.mem_Ioc] at hj
  exact ⟨by omega, by omega, hj.2, by omega, by omega⟩
