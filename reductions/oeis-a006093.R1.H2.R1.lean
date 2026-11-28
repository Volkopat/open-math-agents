import OMAReductions.R_oeis_a006093_R1

/-!
# Necessary divisibility and exponent bounds for shifted-prime collisions

For each term of a separated collision, its shifted denominator divides the
least common multiple of the gaps from that prime to the other primes in the
two intervals. The later interval must have more terms, and the exponent is bounded by
its length and the gap between the first primes of the two intervals.
-/

namespace OMA.R_oeis_a006093_R1_H2_R1

open scoped BigOperators
open Finset OMA.S_oeis_a006093

/-- The linear case under the necessary length, exponent, and divisibility bounds. -/
def H1 : Prop :=
  let p (k : ℕ) := Nat.nth Nat.Prime (k - 1)
  ∀ d i j s t : ℕ, 0 < d → 0 < i → i ≤ j → j < s → s ≤ t →
    j - i < t - s → p s - p i ≤ (t - s) * (p i + d) →
    (∀ k ∈ Icc i j ∪ Icc s t, p k + d ∣ ((Icc i j ∪ Icc s t).erase k).lcm
      (fun l => p l - p k + (p k - p l))) →
    intervalSum d 1 i j = intervalSum d 1 s t →
    d = 1 ∧ i = 4 ∧ j = 4 ∧ s = 8 ∧ t = 10

/-- Higher exponents under the necessary length, exponent, and divisibility bounds. -/
def H2 : Prop :=
  let p (k : ℕ) := Nat.nth Nat.Prime (k - 1)
  ∀ d m i j s t : ℕ, 0 < d → 1 < m → 0 < i → i ≤ j → j < s → s ≤ t →
    j - i < t - s → m * (p s - p i) ≤ (t - s) * (p i + d) →
    (∀ k ∈ Icc i j ∪ Icc s t, p k + d ∣ ((Icc i j ∪ Icc s t).erase k).lcm
      (fun l => p l - p k + (p k - p l))) →
    intervalSum d m i j ≠ intervalSum d m s t

section

private theorem prime_power_dvd_some {A : Finset ℕ} {f : ℕ → ℕ}
    (hf : ∀ a ∈ A, f a ≠ 0) {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hd : p ^ k ∣ A.lcm f) : ∃ a ∈ A, p ^ k ∣ f a := by
  have nonzero : A.lcm f ≠ 0 := by simpa [Finset.lcm_eq_zero_iff] using hf
  have h := (hp.pow_dvd_iff_le_factorization nonzero).mp hd
  rw [Finset.factorization_lcm hf p] at h
  by_contra! hn
  apply (not_lt_of_ge h)
  exact (Finset.sup_lt_iff hk).mpr fun a ha =>
    lt_of_not_ge (fun ge => hn a ha ((hp.pow_dvd_iff_le_factorization (hf a ha)).mpr ge))

private theorem den_dvd_lcm {A : Finset ℕ} (base : ℕ → ℕ) (hb : ∀ k, base k ≠ 0)
    (m : ℕ) (U : Finset ℕ) (hA : A ⊆ U) :
    (∑ k ∈ A, (1 : ℚ) / (base k : ℚ)^m).den ∣ U.lcm (fun k => base k ^ m) := by
  refine (Rat.den_sum_dvd_lcm_den A _).trans (Finset.lcm_dvd fun k hk => ?_)
  rw [← Nat.cast_pow]
  simpa [hb k] using Finset.dvd_lcm (f := fun k => base k ^ m) (hA hk)

private theorem unit_dvd_other_bases {A B : Finset ℕ} (hAB : Disjoint A B)
    (base : ℕ → ℕ) (hb : ∀ k, base k ≠ 0) (m : ℕ)
    (heq : (∑ k ∈ A, (1 : ℚ) / (base k : ℚ)^m) = ∑ k ∈ B, (1 : ℚ) / (base k : ℚ)^m)
    {a : ℕ} (ha : a ∈ A) :
    base a ^ m ∣ ((A ∪ B).erase a).lcm (fun k => base k ^ m) := by
  let f (k : ℕ) := (1 : ℚ) / (base k : ℚ)^m
  let U := (A ∪ B).erase a
  have haB : a ∉ B := fun h => Finset.disjoint_left.mp hAB ha h
  have hsubB : B ⊆ U := fun k hk =>
    Finset.mem_erase.mpr ⟨fun h => haB (h ▸ hk), Finset.mem_union_right _ hk⟩
  have hsubA : A.erase a ⊆ U := fun k hk =>
    Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hk).1,
      Finset.mem_union_left _ (Finset.mem_erase.mp hk).2⟩
  have hsplit : f a = (∑ k ∈ B, f k) - ∑ k ∈ A.erase a, f k := by
    have hs := Finset.sum_erase_add A f ha
    change (∑ k ∈ A, f k) = ∑ k ∈ B, f k at heq
    rw [heq] at hs
    linarith
  have h₁ := den_dvd_lcm base hb m U hsubB
  have h₂ := den_dvd_lcm base hb m U hsubA
  have hd := (Rat.sub_den_dvd_lcm (∑ k ∈ B, f k) (∑ k ∈ A.erase a, f k)).trans
    (Nat.lcm_dvd h₁ h₂)
  rw [← hsplit] at hd
  change ((1 : ℚ) / (base a : ℚ) ^ m).den ∣ _ at hd
  rw [← Nat.cast_pow] at hd
  simpa [hb a, U] using hd

private theorem shifted_dvd_gap_lcm {A B : Finset ℕ} (hAB : Disjoint A B)
    (v : ℕ → ℕ) (d m : ℕ) (hm : 0 < m) (hd : 0 < d)
    (heq : (∑ k ∈ A, (1 : ℚ) / ((v k : ℚ) + d)^m) =
      ∑ k ∈ B, (1 : ℚ) / ((v k : ℚ) + d)^m) :
    ∀ a ∈ A ∪ B, v a + d ∣ ((A ∪ B).erase a).lcm
      (fun k => v k - v a + (v a - v k)) := by
  have heq' : (∑ k ∈ A, (1 : ℚ) / ((v k + d : ℕ) : ℚ)^m) =
      ∑ k ∈ B, (1 : ℚ) / ((v k + d : ℕ) : ℚ)^m := by
    simpa using heq
  intro a ha
  let base (k : ℕ) := v k + d
  have hb (k : ℕ) : base k ≠ 0 := by dsimp [base]; omega
  have hdiv : base a ^ m ∣ ((A ∪ B).erase a).lcm (fun k => base k ^ m) := by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact unit_dvd_other_bases hAB base hb m heq' ha
    · rw [Finset.union_comm]
      exact unit_dvd_other_bases hAB.symm base hb m heq'.symm ha
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e hp hae
  by_cases he : e = 0
  · simp [he]
  have hepos : 0 < e := Nat.pos_of_ne_zero he
  have hprimary : p ^ (e * m) ∣ ((A ∪ B).erase a).lcm (fun k => base k ^ m) := by
    rw [pow_mul]
    exact (pow_dvd_pow_of_dvd hae m).trans hdiv
  obtain ⟨b, hbu, hpb⟩ := prime_power_dvd_some (fun k _ => pow_ne_zero _ (hb k)) hp
    (Nat.mul_pos hepos hm) hprimary
  rw [pow_mul, Nat.pow_dvd_pow_iff hm.ne'] at hpb
  have hgap : p ^ e ∣ v b - v a + (v a - v b) := by
    rcases le_total (v a) (v b) with hab | hba
    · have h := Nat.dvd_sub hpb hae
      simp only [base, Nat.add_sub_add_right] at h
      simpa [Nat.sub_eq_zero_of_le hab] using h
    · have h := Nat.dvd_sub hae hpb
      simp only [base, Nat.add_sub_add_right] at h
      simpa [Nat.sub_eq_zero_of_le hba] using h
  exact hgap.trans (Finset.dvd_lcm hbu)


private theorem exponent_bound {v : ℕ → ℕ} {d m i j s t : ℕ}
    (hv : Monotone v) (hd : 0 < d) (hi : i ≤ j) (hs : s ≤ t)
    (his : v i < v s)
    (heq : (∑ k ∈ Icc i j, (1 : ℚ) / ((v k : ℚ) + d)^m) =
      ∑ k ∈ Icc s t, (1 : ℚ) / ((v k : ℚ) + d)^m) :
    m * (v s - v i) ≤ (t - s) * (v i + d) := by
  let x : ℚ := v i + d
  let y : ℚ := v s + d
  have hx : 0 < x := by dsimp [x]; positivity
  have hxy : x < y := by
    have h : (v i : ℚ) < v s := by exact_mod_cast his
    exact add_lt_add_left h (d : ℚ)
  have hy : 0 < y := hx.trans hxy
  have left : 1 / x ^ m ≤ ∑ k ∈ Icc i j, (1 : ℚ) / ((v k : ℚ) + d)^m := by
    exact Finset.single_le_sum
      (f := fun k => (1 : ℚ) / ((v k : ℚ) + d)^m)
      (fun k _ => by positivity) (Finset.left_mem_Icc.mpr hi)
  have right : (∑ k ∈ Icc s t, (1 : ℚ) / ((v k : ℚ) + d)^m) ≤
      ((t - s : ℕ) + 1 : ℚ) * (1 / y ^ m) := by
    have hcard : (Icc s t).card = (t - s) + 1 := by rw [Nat.card_Icc]; omega
    rw [← Nat.cast_one, ← Nat.cast_add, ← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro k hk
    apply one_div_le_one_div_of_le (pow_pos hy _)
    have h : (v s : ℚ) ≤ v k := by exact_mod_cast hv (Finset.mem_Icc.mp hk).1
    exact pow_le_pow_left₀ hy.le (add_le_add_left h (d : ℚ)) _
  have ratio : (y / x) ^ m ≤ ((t - s : ℕ) + 1 : ℚ) := by
    have h := (left.trans_eq heq).trans right
    rw [div_pow, div_le_iff₀ (pow_pos hx _)]
    rw [mul_one_div, div_le_div_iff₀ (pow_pos hx _) (pow_pos hy _), one_mul] at h
    exact h
  have diff : y / x = 1 + (y - x) / x := by field_simp; ring
  have hnn : 0 ≤ (y - x) / x := div_nonneg (sub_nonneg.mpr hxy.le) hx.le
  have hbern := one_add_mul_le_pow (by linarith : -2 ≤ (y - x) / x) m
  rw [diff] at ratio
  have hmultip : (m : ℚ) * (y - x) ≤ (t - s : ℕ) * x := by
    apply (div_le_iff₀ hx).mp
    rw [mul_div_assoc]
    linarith [hbern.trans ratio]
  have heqdiff : y - x = (v s - v i : ℕ) := by
    rw [Nat.cast_sub his.le]
    dsimp [x, y]
    ring
  rw [heqdiff] at hmultip
  dsimp [x] at hmultip
  exact_mod_cast hmultip

private theorem later_has_more_terms {v : ℕ → ℕ} {d m i j s t : ℕ}
    (hv : Monotone v) (hd : 0 < d) (hm : 0 < m)
    (hij : i ≤ j) (hst : s ≤ t) (hjs : v j < v s)
    (heq : (∑ k ∈ Icc i j, (1 : ℚ) / ((v k : ℚ) + d)^m) =
      ∑ k ∈ Icc s t, (1 : ℚ) / ((v k : ℚ) + d)^m) :
    j - i < t - s := by
  let f (k : ℕ) : ℚ := 1 / ((v k : ℚ) + d)^m
  have hpos (k : ℕ) : 0 < (v k : ℚ) + d := by positivity
  have hle {a b : ℕ} (hab : v a ≤ v b) : f b ≤ f a := by
    have h : (v a : ℚ) ≤ v b := by exact_mod_cast hab
    exact one_div_le_one_div_of_le (pow_pos (hpos a) _)
      (pow_le_pow_left₀ (hpos a).le (add_le_add_left h (d : ℚ)) _)
  have hlt {a b : ℕ} (hab : v a < v b) : f b < f a := by
    have h : (v a : ℚ) < v b := by exact_mod_cast hab
    exact one_div_lt_one_div_of_lt (pow_pos (hpos a) _)
      (pow_lt_pow_left₀ (add_lt_add_left h (d : ℚ)) (hpos a).le hm.ne')
  change (∑ k ∈ Icc i j, f k) = ∑ k ∈ Icc s t, f k at heq
  have hleft : (∑ _ ∈ Icc i j, f s) < ∑ k ∈ Icc i j, f k := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_Icc.mpr hij)
    intro k hk
    exact hlt ((hv (Finset.mem_Icc.mp hk).2).trans_lt hjs)
  have hright : (∑ k ∈ Icc s t, f k) ≤ ∑ _ ∈ Icc s t, f s :=
    Finset.sum_le_sum fun k hk => hle (hv (Finset.mem_Icc.mp hk).1)
  have h := (hleft.trans_eq heq).trans_le hright
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc] at h
  have hfs : 0 < f s := one_div_pos.mpr (pow_pos (hpos s) _)
  have hcard : j + 1 - i < t + 1 - s := by
    exact_mod_cast (lt_of_mul_lt_mul_right h hfs.le)
  omega


-- Cancellation argument from @physbuzz's merged second reduction (PR #12665).
private theorem ordered {d : ℤ} {m i j s t : ℕ} (hd : -1 ≤ d) (hi : 0 < i) (hij : i ≤ j)
    (isle : i ≤ s) (hst : s ≤ t)
    (sep : ∀ a b c e : ℕ, 0 < a → a ≤ b → b < c → c ≤ e →
      intervalSum d m a b = intervalSum d m c e → d=1 ∧ m=1 ∧ a=4 ∧ b=4 ∧ c=8 ∧ e=10)
    (he : intervalSum d m i j = intervalSum d m s t) :
    (i,j)=(s,t) ∨ (d=1 ∧ m=1 ∧ ExceptionalIntervals (i,j) (s,t)) := by
  let f := fun k : ℕ => (1 : ℚ)/((Nat.nth Nat.Prime (k-1) : ℚ)+(d:ℚ))^m
  let P := fun k : ℕ => ∑ a ∈ range k, f a
  have sm : StrictMono P := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hp := (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (k-1)).two_le
    have hbase : (0:ℚ) < (Nat.nth Nat.Prime (k-1) : ℚ)+(d:ℚ) := by
      have h1 : (2:ℚ) ≤ (Nat.nth Nat.Prime (k-1) : ℚ) := by exact_mod_cast hp
      have h2 : (-1:ℚ) ≤ (d:ℚ) := by exact_mod_cast hd
      linarith
    change P k < ∑ a ∈ range (k+1), f a
    rw [sum_range_succ]
    change P k < P k + 1/_^m
    have hpos := one_div_pos.mpr (pow_pos hbase m)
    linarith
  have form {a b : ℕ} (h : a ≤ b) : intervalSum d m a b = P (b+1)-P a := by
    have eqi : Icc a b = Ico a (b+1) := by ext k; simp
    unfold intervalSum
    rw [eqi]
    exact sum_Ico_eq_sub f (by omega)
  have he' := he
  rw [form hij,form hst] at he'
  rcases eq_or_lt_of_le isle with h|h
  · subst s
    have hp : P (j+1)=P (t+1) := by linarith
    have ht := sm.injective hp
    exact Or.inl (Prod.ext rfl (by omega))
  have jt : j < t := by
    by_contra! hg
    have ht := sm.monotone (Nat.succ_le_succ hg)
    have hlt := sm h
    linarith
  right
  by_cases gap : j < s
  · obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := sep i j s t hi hij gap hst he
    exact ⟨rfl,rfl,Or.inl rfl⟩
  · have ha : i ≤ s-1 := by omega
    have hb : j+1 ≤ t := by omega
    have hh : intervalSum d m i (s-1) = intervalSum d m (j+1) t := by
      rw [form ha,form hb,show s-1+1=s by omega]
      linarith
    obtain ⟨rfl,rfl,ia,sb,jc,td⟩ := sep i (s-1) (j+1) t hi ha (by omega) hb hh
    have si : s=5 := by omega
    have ji : j=7 := by omega
    subst_vars
    exact ⟨rfl,rfl,Or.inr rfl⟩

end

theorem main : H1 → H2 → OMA.R_oeis_a006093_R1.H2 := by
  intro h1 h2 d m i j s t hd hm hi hij hs hst heq
  have sep : ∀ a b c e : ℕ, 0 < a → a ≤ b → b < c → c ≤ e →
      intervalSum d m a b = intervalSum d m c e →
      d = 1 ∧ m = 1 ∧ a = 4 ∧ b = 4 ∧ c = 8 ∧ e = 10 := by
    intro a b c e ha hab hbc hce h
    let p (k : ℕ) := Nat.nth Nat.Prime (k - 1)
    let shift := d.toNat
    have hcast : (shift : ℤ) = d := Int.toNat_of_nonneg hd.le
    have hshift : 0 < shift := by omega
    have hp : Monotone p := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone.comp
      (fun _ _ h => Nat.sub_le_sub_right h 1)
    have hac : p a < p c :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (show a - 1 < c - 1 by omega)
    have hdis : Disjoint (Icc a b) (Icc c e) := by
      apply Finset.disjoint_left.mpr
      intro k hk hk'
      exact (not_le_of_gt hbc) ((Finset.mem_Icc.mp hk').1.trans (Finset.mem_Icc.mp hk).2)
    have hsum : (∑ k ∈ Icc a b, (1 : ℚ) / ((p k : ℚ) + shift)^m) =
        ∑ k ∈ Icc c e, (1 : ℚ) / ((p k : ℚ) + shift)^m := by
      rw [← hcast] at h
      simpa [intervalSum, p] using h
    have hdiv := shifted_dvd_gap_lcm hdis p shift m hm hshift hsum
    have hbound := exponent_bound hp hshift hab hce hac hsum
    have hlength := later_has_more_terms hp hshift hm hab hce
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime (show b - 1 < c - 1 by omega)) hsum
    rcases eq_or_lt_of_le (show 1 ≤ m by omega) with hm1 | hm1
    · have hlin : m = 1 := hm1.symm
      subst m
      obtain ⟨hd1, ha1, hb1, hc1, he1⟩ :=
        h1 shift a b c e hshift ha hab hbc hce hlength (by simpa using hbound) hdiv
          (hcast.symm ▸ h)
      exact ⟨by omega, rfl, ha1, hb1, hc1, he1⟩
    · exact (h2 shift m a b c e hshift hm1 ha hab hbc hce hlength hbound hdiv
        (hcast.symm ▸ h)).elim
  have hd' : -1 ≤ d := by omega
  rcases le_total i s with his | hsi
  · exact ordered hd' hi hij his hst sep heq
  · rcases ordered hd' hs hst hsi hij sep heq.symm with eqn | ⟨e1, e2, exceptions⟩
    · exact Or.inl eqn.symm
    · exact Or.inr ⟨e1, e2, by simpa [ExceptionalIntervals, Finset.pair_comm] using exceptions⟩

end OMA.R_oeis_a006093_R1_H2_R1
