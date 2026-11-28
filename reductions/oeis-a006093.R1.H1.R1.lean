import OMAReductions.R_oeis_a006093_R1

/-!
A collision between two distinct intervals yields a collision between disjoint
blocks. Each denominator base must divide the least common multiple of the
other bases. Comparing the first term on the left with the entire block on
the right bounds the exponent. Comparing all the terms with their endpoint
values gives a second bound.
-/

open OMA.S_oeis_a006093
open Finset
open scoped BigOperators

namespace OMA.R_oeis_a006093_R1_H1_R1

private lemma base_pos (k : ℕ) : 0 < Nat.nth Nat.Prime (k-1)-1 := by
  have hp := (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (k-1)).two_le
  change 2 ≤ Nat.nth Nat.Prime (k-1) at hp
  omega

private lemma base_strict {k l : ℕ} (hk : 0 < k) (hkl : k < l) :
    Nat.nth Nat.Prime (k-1)-1 < Nat.nth Nat.Prime (l-1)-1 := by
  have h := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    (show k-1 < l-1 by omega)
  change Nat.nth Nat.Prime (k-1) < Nat.nth Nat.Prime (l-1) at h
  have hp := base_pos k
  omega

private lemma intervalSum_eq_sum (m i j : ℕ) :
    intervalSum (-1) m i j =
      ∑ k ∈ Icc i j, (1 : ℚ) / ((Nat.nth Nat.Prime (k-1)-1 : ℕ) : ℚ)^m := by
  unfold intervalSum
  apply sum_congr rfl
  intro k _
  have h : 1 ≤ Nat.nth Nat.Prime (k-1) := by have := base_pos k; omega
  rw [Nat.cast_sub h]
  simp [sub_eq_add_neg]

private lemma denom_lcm {m : ℕ} (hm : 0 < m) (a : ℕ → ℕ) (ha : ∀ k, 0 < a k)
    {A B : Finset ℕ} (hAB : Disjoint A B)
    (he : (∑ k ∈ A, (1 : ℚ)/(a k : ℚ)^m) = ∑ k ∈ B, (1 : ℚ)/(a k : ℚ)^m)
    {k : ℕ} (hk : k ∈ A) :
    a k ∣ ((A ∪ B).erase k).lcm a := by
  let f (r : ℕ) := (1 : ℚ)/(a r : ℚ)^m
  let L := ((A ∪ B).erase k).lcm a
  have hden (r : ℕ) : (f r).den = a r ^ m := by
    dsimp [f]
    rw [one_div, ← Nat.cast_pow]
    exact Rat.inv_natCast_den_of_pos (pow_pos (ha r) m)
  have hs (S : Finset ℕ) (hS : S ⊆ (A ∪ B).erase k) :
      (∑ r ∈ S, f r).den ∣ L^m := by
    apply (Rat.den_sum_dvd_lcm_den S f).trans
    apply Finset.lcm_dvd
    intro r hr
    rw [hden]
    exact (Nat.pow_dvd_pow_iff hm.ne').2 (dvd_lcm (hS hr))
  have hkB : k ∉ B := fun h => Finset.disjoint_left.mp hAB hk h
  have hSB : B ⊆ (A ∪ B).erase k := by
    intro r hr
    exact mem_erase.mpr ⟨fun e => hkB (e ▸ hr), mem_union_right _ hr⟩
  have hSA : A.erase k ⊆ (A ∪ B).erase k := by
    intro r hr
    obtain ⟨hn, hA⟩ := mem_erase.mp hr
    exact mem_erase.mpr ⟨hn, mem_union_left _ hA⟩
  have hf : f k = (∑ r ∈ B, f r) - ∑ r ∈ A.erase k, f r := by
    have h := sum_erase_add A f hk
    change ∑ r ∈ A, f r = ∑ r ∈ B, f r at he
    linarith
  have hd := Rat.sub_den_dvd_lcm (∑ r ∈ B, f r) (∑ r ∈ A.erase k, f r)
  rw [← hf, hden] at hd
  exact (Nat.pow_dvd_pow_iff hm.ne').1 (hd.trans
    (Nat.lcm_dvd (hs B hSB) (hs (A.erase k) hSA)))

private lemma disjoint_lcm_test {m i j s t : ℕ} (hm : 0 < m) (hj : j < s)
    (he : intervalSum (-1) m i j = intervalSum (-1) m s t) :
    let a (k : ℕ) := Nat.nth Nat.Prime (k-1)-1
    ∀ k ∈ Icc i j ∪ Icc s t, a k ∣ ((Icc i j ∪ Icc s t).erase k).lcm a := by
  dsimp only
  rw [intervalSum_eq_sum, intervalSum_eq_sum] at he
  have hdis : Disjoint (Icc i j) (Icc s t) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    exact (not_le_of_gt hj) ((mem_Icc.mp hl).1.trans (mem_Icc.mp hk).2)
  intro k hk
  rcases mem_union.mp hk with h | h
  · exact denom_lcm hm _ base_pos hdis he h
  · rw [union_comm]
    exact denom_lcm hm _ base_pos hdis.symm he.symm h

private lemma disjoint_size_tests {m i j s t : ℕ} (hi : 0 < i) (hij : i ≤ j)
    (hj : j < s) (he : intervalSum (-1) m i j = intervalSum (-1) m s t) :
    let a (k : ℕ) := Nat.nth Nat.Prime (k-1)-1
    a s ^ m ≤ (t+1-s)*a i ^ m ∧ (j+1-i)*a s ^ m ≤ (t+1-s)*a j ^ m := by
  let a (k : ℕ) := Nat.nth Nat.Prime (k-1)-1
  let f (k : ℕ) := (1 : ℚ) / (a k : ℚ)^m
  have ha (k : ℕ) : 0 < (a k : ℚ) := Nat.cast_pos.mpr (base_pos k)
  have hf (k : ℕ) : 0 ≤ f k := one_div_nonneg.mpr (pow_nonneg (ha k).le _)
  have hanti {k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) : f l ≤ f k := by
    refine one_div_le_one_div_of_le (pow_pos (ha k) m) (pow_le_pow_left₀ (ha k).le ?_ _)
    apply Nat.cast_le.mpr
    rcases eq_or_lt_of_le hkl with rfl | h
    · exact le_rfl
    · exact (base_strict hk h).le
  have hlo : f i ≤ ∑ k ∈ Icc i j, f k :=
    single_le_sum (fun k _ => hf k) (left_mem_Icc.mpr hij)
  have hhi : (∑ k ∈ Icc s t, f k) ≤ (t+1-s : ℕ) * f s := by
    calc
      _ ≤ ∑ _k ∈ Icc s t, f s := sum_le_sum fun k hk => hanti (by omega) (mem_Icc.mp hk).1
      _ = _ := by rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
  have hlo' : (j+1-i : ℕ) * f j ≤ ∑ k ∈ Icc i j, f k := by
    calc
      _ = ∑ _k ∈ Icc i j, f j := by rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
      _ ≤ _ := sum_le_sum fun k hk => hanti (hi.trans_le (mem_Icc.mp hk).1) (mem_Icc.mp hk).2
  rw [intervalSum_eq_sum, intervalSum_eq_sum] at he
  change (∑ k ∈ Icc i j, f k) = ∑ k ∈ Icc s t, f k at he
  have hright := he.le.trans hhi
  have h := hlo.trans hright
  change (1 : ℚ) / (a i : ℚ)^m ≤ ((t+1-s : ℕ) : ℚ) * (1 / (a s : ℚ)^m) at h
  rw [mul_one_div] at h
  have hp := (div_le_div_iff₀ (pow_pos (ha i) m) (pow_pos (ha s) m)).mp h
  rw [one_mul] at hp
  have h' := hlo'.trans hright
  change ((j+1-i : ℕ) : ℚ) * (1 / (a j : ℚ)^m) ≤
    ((t+1-s : ℕ) : ℚ) * (1 / (a s : ℚ)^m) at h'
  rw [mul_one_div, mul_one_div] at h'
  have hp' := (div_le_div_iff₀ (pow_pos (ha j) m) (pow_pos (ha s) m)).mp h'
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hp'⟩

/-- A collision of distinct intervals has a disjoint collision after
cancelling the overlap. Positivity rules out containment. -/
private lemma of_disjoint {m : ℕ}
    (sep : ∀ i j s t : ℕ, 0 < i → i ≤ j → j < s → s ≤ t →
      intervalSum (-1) m i j ≠ intervalSum (-1) m s t)
    {i j s t : ℕ} (hi : 0 < i) (hij : i ≤ j) (hs : 0 < s) (hst : s ≤ t)
    (he : intervalSum (-1) m i j = intervalSum (-1) m s t) : (i,j) = (s,t) := by
  let f (k : ℕ) := (1 : ℚ) / ((Nat.nth Nat.Prime (k-1)-1 : ℕ) : ℚ)^m
  let P (n : ℕ) := ∑ k ∈ range n, f k
  have hP : StrictMono P := by
    apply strictMono_nat_of_lt_succ
    intro n
    change P n < ∑ k ∈ range (n+1), f k
    rw [sum_range_succ]
    exact lt_add_of_pos_right _ (one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr (base_pos n)) m))
  have form {a b : ℕ} (hab : a ≤ b) : intervalSum (-1) m a b = P (b+1)-P a := by
    rw [intervalSum_eq_sum, show Icc a b = Ico a (b+1) by ext k; simp]
    exact sum_Ico_eq_sub f (by omega)
  have ordered {a b c d : ℕ} (ha : 0 < a) (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c)
      (e : intervalSum (-1) m a b = intervalSum (-1) m c d) : (a,b) = (c,d) := by
    have e' := e
    rw [form hab, form hcd] at e'
    by_cases hac' : a = c
    · have h := hP.injective (show P (b+1) = P (d+1) by rw [hac'] at e'; linarith)
      exact Prod.ext hac' (by omega)
    · have hlt := hP (lt_of_le_of_ne hac hac')
      have hbd : b < d := by
        by_contra! h
        have h' := hP.monotone (show d+1 ≤ b+1 by omega)
        linarith
      by_cases hbc : b < c
      · exact (sep a b c d ha hab hbc hcd e).elim
      · have hleft : a ≤ c-1 := by omega
        have hright : b+1 ≤ d := by omega
        have hcancel : intervalSum (-1) m a (c-1) = intervalSum (-1) m (b+1) d := by
          rw [form hleft, form hright, show c-1+1 = c by omega]
          linarith
        exact (sep a (c-1) (b+1) d ha hleft (by omega) hright hcancel).elim
  rcases le_total i s with h | h
  · exact ordered hi hij hst h he
  · exact (ordered hs hst hij h he.symm).symm

/-- The reciprocal case, restricted to pairs that pass both necessary tests. -/
def H1 : Prop :=
  ∀ i j s t : ℕ, 0 < i → i ≤ j → j < s → s ≤ t →
    let a (k : ℕ) := Nat.nth Nat.Prime (k-1)-1
    (∀ k ∈ Icc i j ∪ Icc s t, a k ∣ ((Icc i j ∪ Icc s t).erase k).lcm a) →
    a s ≤ (t+1-s)*a i →
    (j+1-i)*a s ≤ (t+1-s)*a j →
    intervalSum (-1) 1 i j ≠ intervalSum (-1) 1 s t

/-- The higher powers, with an exponent bound for each pair of blocks. -/
def H2 : Prop :=
  ∀ m i j s t : ℕ, 2 ≤ m → 0 < i → i ≤ j → j < s → s ≤ t →
    let a (k : ℕ) := Nat.nth Nat.Prime (k-1)-1
    (∀ k ∈ Icc i j ∪ Icc s t, a k ∣ ((Icc i j ∪ Icc s t).erase k).lcm a) →
    a s ^ m ≤ (t+1-s)*a i ^ m →
    (j+1-i)*a s ^ m ≤ (t+1-s)*a j ^ m →
    intervalSum (-1) m i j ≠ intervalSum (-1) m s t

theorem main : H1 → H2 → OMA.R_oeis_a006093_R1.H1 := by
  intro h1 h2 m i j s t hm hi hij hs hst he
  apply of_disjoint _ hi hij hs hst he
  intro a b c d ha hab hbc hcd e
  have hL := disjoint_lcm_test hm hbc e
  obtain ⟨hsize, hsize'⟩ := disjoint_size_tests ha hab hbc e
  by_cases h : m = 1
  · subst m
    exact h1 a b c d ha hab hbc hcd hL
      (by simpa only [pow_one] using hsize) (by simpa only [pow_one] using hsize') e
  · exact h2 m a b c d (by omega) ha hab hbc hcd hL hsize hsize' e

end OMA.R_oeis_a006093_R1_H1_R1
