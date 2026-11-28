import OMAReductions.R_oeis_a006093_R2

-- Credit: @Alewawa

/-!
For two disjoint ordered intervals of positive shifted primes, clear denominators with
their least common multiple. Any equality forces strict endpoint inequalities and repeated
occurrences of every prime power dividing a denominator. Modulo two, the number of odd
quotients of the least common multiple by the denominators must be even. The remaining
integer equalities split into reciprocals and higher reciprocal powers.
-/

open Finset OMA.S_oeis_a006093

namespace OMA.R_oeis_a006093_R2_H2_R2

/-- Multiply an equality of reciprocal power sums by the common denominator to the same power. -/
private theorem clear_denominators {m : ℕ} {A B : Finset ℕ} {a : ℕ → ℕ}
    (ha : ∀ k ∈ A ∪ B, a k ≠ 0)
    (he : (∑ k ∈ A, (1 : ℚ) / (a k : ℚ)^m) = ∑ k ∈ B, (1 : ℚ) / (a k : ℚ)^m) :
    let L := (A ∪ B).lcm a
    (∑ k ∈ A, (L / a k)^m) = ∑ k ∈ B, (L / a k)^m := by
  let L := (A ∪ B).lcm a
  have hsum (S : Finset ℕ) (hS : S ⊆ A ∪ B) :
      (L : ℚ)^m * (∑ k ∈ S, (1 : ℚ) / (a k : ℚ)^m) =
        ((∑ k ∈ S, (L / a k)^m : ℕ) : ℚ) := by
    rw [mul_sum, Nat.cast_sum]
    apply sum_congr rfl
    intro k hk
    have ha0 : (a k : ℚ) ≠ 0 := by exact_mod_cast ha k (hS hk)
    have hd : a k ∣ L := dvd_lcm (hS hk)
    rw [Nat.cast_pow, Nat.cast_div hd (by exact_mod_cast ha0), div_pow]
    ring
  have hA := hsum A subset_union_left
  have hB := hsum B subset_union_right
  rw [he, hB] at hA
  exact_mod_cast hA.symm

/-- A prime power that occurs in exactly one denominator obstructs an equality. -/
private theorem prime_powers_repeat {m : ℕ} {A B : Finset ℕ} {a : ℕ → ℕ} (hm : 0 < m)
    (hAB : Disjoint A B) (ha : ∀ k ∈ A ∪ B, a k ≠ 0)
    (he : let L := (A ∪ B).lcm a
      (∑ k ∈ A, (L / a k)^m) = ∑ k ∈ B, (L / a k)^m) :
    ∀ q : ℕ, q.Prime → ∀ e k : ℕ, k ∈ A ∪ B → 0 < e → q^e ∣ a k →
      ∃ l ∈ A ∪ B, l ≠ k ∧ q^e ∣ a l := by
  classical
  intro q hq e k hk hepos hdiv
  by_contra! hu
  let U := A ∪ B
  let L := U.lcm a
  let f (j : ℕ) := L / a j
  have hL : L ≠ 0 := lcm_ne_zero_iff.mpr ha
  have hdivL (l : ℕ) (hl : l ∈ U) : a l ∣ L := dvd_lcm hl
  have hf (l : ℕ) (hl : l ∈ U) : f l ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL) (hdivL l hl))
      (Nat.pos_of_ne_zero (ha l hl))).ne'
  have hv := (hq.pow_dvd_iff_le_factorization (ha k hk)).mp hdiv
  have hlt (l : ℕ) (hl : l ∈ U) (hlk : l ≠ k) :
      (a l).factorization q < e :=
    lt_of_not_ge (fun h => hu l hl hlk ((hq.pow_dvd_iff_le_factorization (ha l hl)).mpr h))
  have hLeq : L.factorization q = (a k).factorization q := by
    rw [Finset.factorization_lcm ha]
    apply le_antisymm
    · apply Finset.sup_le
      intro l hl
      by_cases hlk : l = k
      · rw [hlk]
      · exact (hlt l hl hlk).le.trans hv
    · exact le_sup (f := fun l => (a l).factorization q) hk
  have hfk : ¬ q ∣ f k := by
    rw [hq.dvd_iff_one_le_factorization (hf k hk)]
    dsimp only [f]
    rw [Nat.factorization_div (hdivL k hk),
      Finsupp.coe_tsub, Pi.sub_apply, hLeq, Nat.sub_self]
    omega
  have hfl (l : ℕ) (hl : l ∈ U) (hlk : l ≠ k) : q ∣ f l := by
    rw [hq.dvd_iff_one_le_factorization (hf l hl)]
    dsimp only [f]
    rw [Nat.factorization_div (hdivL l hl),
      Finsupp.coe_tsub, Pi.sub_apply, hLeq]
    have := hlt l hl hlk
    omega
  have hz := congrArg (fun n : ℕ => (n : ZMod q)) he
  push_cast at hz
  rw [show (A ∪ B).lcm a = L from rfl] at hz
  change (∑ j ∈ A, (f j : ZMod q)^m) = ∑ j ∈ B, (f j : ZMod q)^m at hz
  have hnonzero : (f k : ZMod q)^m ≠ 0 := by
    let : Fact q.Prime := ⟨hq⟩
    exact pow_ne_zero _ (fun h => hfk ((ZMod.natCast_eq_zero_iff _ _).mp h))
  have hzero (S : Finset ℕ) (hS : S ⊆ U) (hkS : k ∉ S) :
      (∑ j ∈ S, (f j : ZMod q)^m) = 0 := by
    apply sum_eq_zero
    intro l hl
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr (hfl l (hS hl) (fun h => hkS (h ▸ hl))),
      zero_pow hm.ne']
  have hsingle (S : Finset ℕ) (hS : S ⊆ U) (hkS : k ∈ S) :
      (∑ j ∈ S, (f j : ZMod q)^m) = (f k : ZMod q)^m := by
    apply sum_eq_single_of_mem k hkS
    intro l hl hlk
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr (hfl l (hS hl) hlk), zero_pow hm.ne']
  rcases mem_union.mp hk with hkA | hkB
  · rw [hsingle A subset_union_left hkA,
      hzero B subset_union_right (fun hkB => disjoint_left.mp hAB hkA hkB)] at hz
    exact hnonzero hz
  · rw [hzero A subset_union_left (fun hkA => disjoint_left.mp hAB hkA hkB),
      hsingle B subset_union_right hkB] at hz
    exact hnonzero hz.symm

/-- The number of denominators with odd quotient in the common denominator is even. -/
private theorem odd_quotient_count_even {m : ℕ} {A B : Finset ℕ} {a : ℕ → ℕ}
    (hm : 0 < m) (hAB : Disjoint A B)
    (he : let L := (A ∪ B).lcm a
      (∑ k ∈ A, (L / a k)^m) = ∑ k ∈ B, (L / a k)^m) :
    Even ((A ∪ B).filter fun k => Odd ((A ∪ B).lcm a / a k)).card := by
  let f (k : ℕ) := (A ∪ B).lcm a / a k
  have hsum (S : Finset ℕ) :
      (∑ k ∈ S, (f k : ZMod 2)^m) = ((S.filter fun k => Odd (f k)).card : ZMod 2) := by
    rw [natCast_card_filter]
    apply sum_congr rfl
    intro k _
    by_cases h : Odd (f k)
    · rw [if_pos h, ZMod.natCast_eq_one_iff_odd.mpr h, one_pow]
    · rw [if_neg h, ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp h), zero_pow hm.ne']
  have h := congrArg (fun n : ℕ => (n : ZMod 2)) he
  push_cast at h
  change (∑ k ∈ A, (f k : ZMod 2)^m) = ∑ k ∈ B, (f k : ZMod 2)^m at h
  rw [hsum A, hsum B] at h
  change Even ((A ∪ B).filter fun k => Odd (f k)).card
  have hd : Disjoint (A.filter fun k => Odd (f k)) (B.filter fun k => Odd (f k)) :=
    hAB.mono (filter_subset _ _) (filter_subset _ _)
  rw [← ZMod.natCast_eq_zero_iff_even, filter_union, card_union_of_disjoint hd, Nat.cast_add, h]
  rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

private theorem size_constraints {m i j s t : ℕ} {a : ℕ → ℕ}
    (hm : 0 < m) (hij : i ≤ j) (hjs : j < s) (hst : s ≤ t)
    (ha : ∀ k, a k ≠ 0) (haMono : StrictMonoOn a (Set.Icc i t))
    (he : (∑ k ∈ Icc i j, (1 : ℚ) / (a k : ℚ)^m) =
      ∑ k ∈ Icc s t, (1 : ℚ) / (a k : ℚ)^m) :
    j-i < t-s ∧
      (t-s+1) * (a i)^m < (j-i+1) * (a t)^m ∧
      (j-i+1) * (a s)^m < (t-s+1) * (a j)^m := by
  let F (k : ℕ) := (1 : ℚ) / (a k : ℚ)^m
  have hpos (k : ℕ) : (0 : ℚ) < (a k : ℚ)^m := by
    exact pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (ha k)) _
  have hFpos (k : ℕ) : 0 < F k := one_div_pos.mpr (hpos k)
  have hF : StrictAntiOn F (Set.Icc i t) := by
    intro x hx y hy hxy
    exact one_div_lt_one_div_of_lt (hpos x)
      (pow_lt_pow_left₀ (by exact_mod_cast haMono hx hy hxy) (by positivity) hm.ne')
  have hconst (x y : ℕ) (hxy : x ≤ y) (c : ℚ) :
      ∑ _ ∈ Icc x y, c = (↑(y-x+1) : ℚ) * c := by
    have hc : (Icc x y).card = y - x + 1 := by rw [Nat.card_Icc]; omega
    simp only [sum_const, nsmul_eq_mul, hc]
  have hlower (x y : ℕ) (hx : i ≤ x) (hxy : x ≤ y) (hy : y ≤ t) :
      (↑(y-x+1) : ℚ) * F y ≤ ∑ k ∈ Icc x y, F k := by
    calc _ = ∑ _ ∈ Icc x y, F y := (hconst x y hxy _).symm
      _ ≤ _ := sum_le_sum fun k hk => by
        have hk' := mem_Icc.mp hk
        exact hF.antitoneOn ⟨hx.trans hk'.1, hk'.2.trans hy⟩ ⟨hx.trans hxy, hy⟩ hk'.2
  have hupper (x y : ℕ) (hx : i ≤ x) (hxy : x ≤ y) (hy : y ≤ t) :
      (∑ k ∈ Icc x y, F k) ≤ (↑(y-x+1) : ℚ) * F x := by
    calc _ ≤ ∑ _ ∈ Icc x y, F x := sum_le_sum fun k hk => by
          have hk' := mem_Icc.mp hk
          exact hF.antitoneOn ⟨hx, hxy.trans hy⟩ ⟨hx.trans hk'.1, hk'.2.trans hy⟩ hk'.1
      _ = _ := hconst x y hxy _
  change (∑ k ∈ Icc i j, F k) = ∑ k ∈ Icc s t, F k at he
  have hlen : j-i < t-s := by
    by_contra! h
    have h1 := hlower i j le_rfl hij (by omega)
    have h2 := hupper s t (by omega) hst le_rfl
    have h3 := hF (a := j) (b := s) ⟨hij, by omega⟩ ⟨by omega, hst⟩ hjs
    have h4 : (↑(t-s+1) : ℚ) ≤ (↑(j-i+1) : ℚ) := by exact_mod_cast (by omega : t-s+1 ≤ j-i+1)
    have h5 : (↑(t-s+1) : ℚ) * F s < (↑(j-i+1) : ℚ) * F j :=
      (mul_lt_mul_of_pos_left h3 (by positivity)).trans_le
        (mul_le_mul_of_nonneg_right h4 (hFpos j).le)
    linarith
  refine ⟨hlen, ?_, ?_⟩
  · have h1 : (↑(t-s+1) : ℚ) * F t < ∑ k ∈ Icc s t, F k := by
      calc _ = ∑ _ ∈ Icc s t, F t := (hconst s t hst _).symm
        _ < _ := by
          refine sum_lt_sum (fun k hk => ?_) ⟨s, left_mem_Icc.mpr hst, ?_⟩
          · have hk' := mem_Icc.mp hk
            exact hF.antitoneOn ⟨by omega, hk'.2⟩ ⟨by omega, le_rfl⟩ hk'.2
          · exact hF ⟨by omega, hst⟩ ⟨by omega, le_rfl⟩ (by omega)
    rw [← he] at h1
    have h := h1.trans_le (hupper i j le_rfl hij (by omega))
    dsimp [F] at h
    rw [mul_one_div, mul_one_div, div_lt_div_iff₀ (hpos t) (hpos i)] at h
    exact_mod_cast h
  · have h1 : (∑ k ∈ Icc s t, F k) < (↑(t-s+1) : ℚ) * F s := by
      calc _ < ∑ _ ∈ Icc s t, F s := by
            refine sum_lt_sum (fun k hk => ?_) ⟨t, right_mem_Icc.mpr hst, ?_⟩
            · have hk' := mem_Icc.mp hk
              exact hF.antitoneOn ⟨by omega, hst⟩ ⟨by omega, hk'.2⟩ hk'.1
            · exact hF ⟨by omega, hst⟩ ⟨by omega, le_rfl⟩ (by omega)
        _ = _ := hconst s t hst _
    rw [← he] at h1
    have h := (hlower i j le_rfl hij (by omega)).trans_lt h1
    dsimp [F] at h
    rw [mul_one_div, mul_one_div, div_lt_div_iff₀ (hpos j) (hpos s)] at h
    exact_mod_cast h

/-- The reciprocal case, restricted to candidates passing the size and divisibility tests. -/
def H1 : Prop :=
  ∀ d i j s t : ℕ, 0 < d → 0 < i → i ≤ j → j < s → s ≤ t → j-i < t-s →
  let a (k : ℕ) := Nat.nth Nat.Prime (k-1) + d
  let U := Icc i j ∪ Icc s t
  let L := U.lcm a
  (t-s+1) * a i < (j-i+1) * a t →
  (j-i+1) * a s < (t-s+1) * a j →
  (∀ q : ℕ, q.Prime → ∀ e k : ℕ, k ∈ U → 0 < e → q^e ∣ a k →
    ∃ l ∈ U, l ≠ k ∧ q^e ∣ a l) →
  Even (U.filter fun k => Odd (L / a k)).card →
  (∑ k ∈ Icc i j, L / a k) = ∑ k ∈ Icc s t, L / a k →
  d = 1 ∧ i = 4 ∧ j = 4 ∧ s = 8 ∧ t = 10

/-- For powers greater than one, the same tests leave no listed exception. -/
def H2 : Prop :=
  ∀ d m i j s t : ℕ, 0 < d → 2 ≤ m → 0 < i → i ≤ j → j < s → s ≤ t → j-i < t-s →
  let a (k : ℕ) := Nat.nth Nat.Prime (k-1) + d
  let U := Icc i j ∪ Icc s t
  let L := U.lcm a
  (t-s+1) * (a i)^m < (j-i+1) * (a t)^m →
  (j-i+1) * (a s)^m < (t-s+1) * (a j)^m →
  (∀ q : ℕ, q.Prime → ∀ e k : ℕ, k ∈ U → 0 < e → q^e ∣ a k →
    ∃ l ∈ U, l ≠ k ∧ q^e ∣ a l) →
  Even (U.filter fun k => Odd (L / a k)).card →
  (∑ k ∈ Icc i j, (L / a k)^m) ≠ ∑ k ∈ Icc s t, (L / a k)^m

theorem main : H1 → H2 → OMA.R_oeis_a006093_R2.H2 := by
  intro h1 h2 d m i j s t hd hm hi hij hjs hst he
  let a (k : ℕ) := Nat.nth Nat.Prime (k-1) + d.toNat
  have hdpos : 0 < d.toNat := by omega
  have ha (k : ℕ) : a k ≠ 0 := by
    dsimp [a]
    omega
  have hmono : StrictMonoOn a (Set.Icc i t) := by
    intro k hk l hl hkl
    change i ≤ k ∧ k ≤ t at hk
    change i ≤ l ∧ l ≤ t at hl
    exact Nat.add_lt_add_right (Nat.nth_strictMono Nat.infinite_setOfPred_prime
      (show k-1 < l-1 by omega)) _
  have hcast (k : ℕ) : (a k : ℚ) = (Nat.nth Nat.Prime (k-1) : ℚ) + (d : ℚ) := by
    have hnat : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.le
    have hrat : (d.toNat : ℚ) = (d : ℚ) := by exact_mod_cast hnat
    simp only [a, Nat.cast_add, hrat]
  unfold intervalSum at he
  simp only [← hcast] at he
  have hdisj : Disjoint (Icc i j) (Icc s t) := by
    rw [disjoint_left]
    intro k hk hl
    have hkj := (mem_Icc.mp hk).2
    have hsk := (mem_Icc.mp hl).1
    omega
  obtain ⟨hlen, hmin, hmax⟩ := size_constraints hm hij hjs hst ha hmono he
  have hclear := clear_denominators (fun k _ => ha k) he
  have hrep := prime_powers_repeat hm hdisj (fun k _ => ha k) hclear
  have hparity := odd_quotient_count_even hm hdisj hclear
  rcases eq_or_lt_of_le (show 1 ≤ m from hm) with heq | hlt
  · subst m
    obtain ⟨hd', hii, hjj, hss, htt⟩ :=
      h1 d.toNat i j s t hdpos hi hij hjs hst hlen
        (by simpa only [pow_one] using hmin) (by simpa only [pow_one] using hmax)
        hrep hparity (by simpa only [pow_one] using hclear)
    exact ⟨by omega, rfl, hii, hjj, hss, htt⟩
  · exact (h2 d.toNat m i j s t hdpos hlt hi hij hjs hst hlen
      hmin hmax hrep hparity hclear).elim

end OMA.R_oeis_a006093_R2_H2_R2
