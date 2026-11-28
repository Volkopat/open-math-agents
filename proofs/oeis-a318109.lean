import OMAStatements.S_oeis_a318109

/-! The proof uses paired factors to scale binomial coefficients modulo prime powers.
Vandermonde’s identity rewrites the diagonal as a double binomial sum, whose
terms can then be grouped by their common prime-power divisibility. -/

open Finset

namespace ChooseScaling

private def interval (n : ℕ) : Finset ℕ := Ico 1 (n + 1)

private lemma mem_interval {n i : ℕ} : i ∈ interval n ↔ 1 ≤ i ∧ i ≤ n := by
  simp [interval]

private lemma prod_shift (c b : ℕ) :
    (∏ i ∈ interval b, (c + i)) = (c + b).choose b * b.factorial := by
  rw [mul_comm ((c + b).choose b), ← Nat.ascFactorial_eq_factorial_mul_choose]
  rw [Nat.ascFactorial_eq_prod_range, ← Nat.Ico_zero_eq_range]
  simpa [interval, Nat.add_assoc] using
    (Finset.prod_Ico_add (fun i : ℕ => c + i) 0 b 1).symm

private lemma prod_divisible {p : ℕ} (hp : 0 < p) (b : ℕ) (f : ℕ → ℕ) :
    (∏ i ∈ (interval (p * b)).filter (fun i => p ∣ i), f i) =
      ∏ i ∈ interval b, f (p * i) := by
  symm
  refine Finset.prod_bij' (fun i _ => p * i) (fun j _ => j / p) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_interval.mp hi with ⟨hi0, hib⟩
    exact mem_filter.mpr ⟨mem_interval.mpr
      ⟨Nat.succ_le_of_lt (Nat.mul_pos hp (by omega)), Nat.mul_le_mul_left p hib⟩, dvd_mul_right _ _⟩
  · intro j hj
    obtain ⟨hj, k, rfl⟩ := mem_filter.mp hj
    rw [Nat.mul_div_cancel_left _ hp]
    rcases mem_interval.mp hj with ⟨hj0, hjb⟩
    refine mem_interval.mpr ⟨?_, Nat.le_of_mul_le_mul_left hjb hp⟩
    by_contra! hz
    interval_cases k
    simp at hj0
  · intro i _
    exact Nat.mul_div_cancel_left i hp
  · intro j hj
    simpa only [Nat.mul_comm] using (Nat.div_mul_cancel (mem_filter.mp hj).2)
  · intro i _
    rfl

private def offMultiples (p b : ℕ) : Finset ℕ :=
  (interval (p * b)).filter (fun i => ¬ p ∣ i)

private lemma product_relation {p : ℕ} (hp : 0 < p) (b c : ℕ) :
    (∏ i ∈ offMultiples p b, i) * (p * (c + b)).choose (p * b) =
      (∏ i ∈ offMultiples p b, (p * c + i)) * (c + b).choose b := by
  have hcompare (d : ℕ) :
      (p * (d + b)).choose (p * b) * (p * b).factorial =
        p ^ b * ((d + b).choose b * b.factorial) *
          (∏ i ∈ offMultiples p b, (p * d + i)) := by
    rw [Nat.mul_add, ← prod_shift, ← Finset.prod_filter_mul_prod_filter_not _ (p ∣ ·),
      prod_divisible hp]
    simp_rw [← Nat.mul_add]
    rw [Finset.prod_mul_distrib, Finset.prod_const, prod_shift]
    simp [interval, offMultiples]
  have hfactor := hcompare 0
  simp at hfactor
  have hd := hcompare c
  rw [hfactor] at hd
  have hcancel : 0 < p ^ b * b.factorial := by positivity
  apply Nat.mul_left_cancel hcancel
  calc
    p ^ b * b.factorial *
        ((∏ i ∈ offMultiples p b, i) * (p * (c + b)).choose (p * b)) =
          (p * (c + b)).choose (p * b) *
            (p ^ b * b.factorial * (∏ i ∈ offMultiples p b, i)) := by ring
    _ = p ^ b * b.factorial *
          ((∏ i ∈ offMultiples p b, (p * c + i)) * (c + b).choose b) := hd.trans (by ring)

private lemma reflect_mem {p b i : ℕ} (hi : i ∈ offMultiples p b) :
    p * b - i ∈ offMultiples p b := by
  rcases mem_filter.mp hi with ⟨hi, hnd⟩
  rcases mem_interval.mp hi with ⟨hi0, hib⟩
  have hin : i ≠ p * b := by aesop
  refine mem_filter.mpr ⟨mem_interval.mpr ⟨by omega, by omega⟩, ?_⟩
  exact fun hs => hnd ((Nat.dvd_sub_iff_right hib (dvd_mul_right p b)).mp hs)

private lemma no_fixed {p b i : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hi : i ∈ offMultiples p b) : i ≠ p * b - i := by
  intro h
  have hib := (mem_interval.mp (mem_filter.mp hi).1).2
  have hpdiv : p ∣ 2 * i := by rw [show 2 * i = p * b by omega]; exact dvd_mul_right p b
  rcases hp.dvd_mul.mp hpdiv with ht | ht
  · exact hp2 ((Nat.dvd_prime Nat.prime_two).mp ht |>.resolve_left hp.ne_one)
  · exact (mem_filter.mp hi).2 ht

private lemma prod_pairs {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (b : ℕ) (f : ℕ → ℕ) :
    (∏ i ∈ offMultiples p b, f i) =
      ∏ i ∈ (offMultiples p b).filter (fun i => i < p * b - i), f i * f (p * b - i) := by
  let S := offMultiples p b
  have hreflect {i : ℕ} (hi : i ∈ S) : p * b - (p * b - i) = i := by
    have := (mem_interval.mp (mem_filter.mp hi).1).2
    omega
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun i => i < p * b - i)]
  rw [Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_bij' (fun i _ => p * b - i) (fun i _ => p * b - i) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨hi, hn⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨reflect_mem hi, ?_⟩
    rw [hreflect hi]
    have := no_fixed hp hp2 hi
    omega
  · intro i hi
    obtain ⟨hi, hn⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨reflect_mem hi, by rw [hreflect hi]; omega⟩
  · intro i hi
    exact hreflect (mem_filter.mp hi).1
  · intro i hi
    exact hreflect (mem_filter.mp hi).1
  · intro i hi
    rw [hreflect (mem_filter.mp hi).1]

private theorem paired_congruence {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (b c : ℕ) :
    (∏ i ∈ offMultiples p b, (p * c + i)) ≡
      (∏ i ∈ offMultiples p b, i) [MOD p ^ 2 * (c + b) * c] := by
  rw [prod_pairs hp hp2, prod_pairs hp hp2]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  have hib := (mem_interval.mp (mem_filter.mp (mem_filter.mp hi).1).1).2
  have hei : i + (p * b - i) = p * b := by omega
  have hpair : (p * c + i) * (p * c + (p * b - i)) =
      p ^ 2 * (c + b) * c + i * (p * b - i) := by
    calc
      _ = (p * c) ^ 2 + p * c * (i + (p * b - i)) + i * (p * b - i) := by ring
      _ = _ := by rw [hei]; ring
  have hmod : (p*c+i)*(p*c+(p*b-i)) ≡ i*(p*b-i) [MOD p^2*(c+b)*c] := by
    rw [hpair]
    simpa only [mul_one] using (Nat.ModEq.modulus_mul_add (a := 1)
      (m := p ^ 2 * (c + b) * c) (b := i * (p * b - i)))
  simpa only [Nat.cast_mul, Nat.cast_add] using
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

theorem scaled_choose_mod {p A B r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hA : p ^ r ∣ A) :
    (p * A).choose (p * B) ≡ A.choose B [MOD p ^ (2 * (r + 1))] := by
  by_cases hBA : B ≤ A
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hBA
    rw [add_comm B c] at hA ⊢
    have hrel := product_relation hp.pos B c
    have hmod := (paired_congruence hp hp2 B c).mul_right' ((c + B).choose B)
    rw [← hrel] at hmod
    have hdvd : p ^ (2 * (r + 1)) ∣
        (c + B).choose B * (p ^ 2 * (c + B) * c) := by
      have hpow : p ^ (2 * r) ∣ (c + B) ^ 2 := by
        rw [Nat.mul_comm 2 r, pow_mul]
        exact pow_dvd_pow_of_dvd hA 2
      have hp2dvd : p ^ 2 * (c + B) ^ 2 ∣
          (c + B).choose B * (p ^ 2 * (c + B) * c) := by
        cases c with
        | zero => simp
        | succ c =>
          have hc := Nat.choose_mul_succ_eq (c+B) B
          rw [show c + B + 1 - B = c + 1 by omega] at hc
          have hc' : (c+1+B).choose B * (c+1) = (c+B).choose B * (c+1+B) := by
            simpa [Nat.add_right_comm] using hc.symm
          refine ⟨(c+B).choose B, ?_⟩
          calc
            _ = ((c+1+B).choose B * (c+1)) * (p ^ 2 * (c+1+B)) := by ring
            _ = _ := by rw [hc']; ring
      rw [show 2 * (r+1) = 2 + 2*r by omega, pow_add]
      exact (Nat.mul_dvd_mul_left (p ^ 2) hpow).trans hp2dvd
    have hpD : p.Coprime (∏ i ∈ offMultiples p B, i) :=
      Nat.Coprime.prod_right (fun i hi => hp.coprime_iff_not_dvd.mpr (mem_filter.mp hi).2)
    refine Nat.ModEq.cancel_left_of_coprime (hpD.pow_left _) ?_
    rw [mul_comm ((c+B).choose B) (p^2*(c+B)*c)] at hdvd
    exact hmod.of_dvd hdvd
  · rw [Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hBA) hp.pos),
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hBA)]

end ChooseScaling

open Finset
open ChooseScaling

namespace ConvolutionScaling

/-- A coefficient of `(1+X)^a * (1+X^d)^b`. -/
def inner (d a b n : ℕ) : ℕ :=
  ∑ i ∈ range (b + 1), if d * i ≤ n then a.choose (n - d * i) * b.choose i else 0

/-- The binomial expression for the two rational diagonals. -/
def outer (d n : ℕ) : ℕ :=
  ∑ j ∈ range (n + 1), n.choose j ^ 2 * inner d (3 * n - d * j) j n

private lemma mul_choose (A j : ℕ) (hj : 0 < j) :
    j * A.choose j = A * (A - 1).choose (j - 1) := by
  cases A with
  | zero => simp [Nat.choose_eq_zero_of_lt hj]
  | succ A =>
    cases j with
    | zero => omega
    | succ j => simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq A j).symm

private lemma choose_dvd_of_index {p A j e r t : ℕ} (hp : p.Prime) (hA : p ^ r ∣ A)
    (hj : 0 < j) (hj' : j = p ^ e * t) (hte : ¬ p ∣ t) (her : e ≤ r) :
    p ^ (r - e) ∣ A.choose j := by
  have hdv : p ^ r ∣ j * A.choose j := by
    rw [mul_choose A j hj]
    exact hA.trans (dvd_mul_right _ _)
  rw [hj', mul_assoc, ← Nat.pow_sub_mul_pow p her, mul_comm (p^(r-e)), ← hj'] at hdv
  exact ((hp.coprime_iff_not_dvd.mpr hte).pow_left _).dvd_of_dvd_mul_left
    ((Nat.mul_dvd_mul_iff_left (pow_pos hp.pos _)).mp hdv)

private lemma choose_dvd_unit {p A j r : ℕ} (hp : p.Prime) (hA : p ^ r ∣ A)
    (hj : ¬ p ∣ j) : p ^ r ∣ A.choose j := by
  have hj0 : 0 < j := by
    have : j ≠ 0 := fun h => hj (h ▸ dvd_zero _)
    omega
  simpa using choose_dvd_of_index (e := 0) (t := j) hp hA hj0 (by simp) hj (by omega)

private lemma sum_strip {p n m : ℕ} (hp : 0 < p) (f g : ℕ → ℕ)
    (hzero : ∀ j ≤ p*n, ¬p ∣ j → f j ≡ 0 [MOD m])
    (hkeep : ∀ j ≤ n, f (p*j) ≡ g j [MOD m]) :
    (∑ j ∈ range (p*n + 1), f j) ≡ (∑ j ∈ range (n + 1), g j) [MOD m] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not _ (p ∣ ·)]
  have hz : (∑ j ∈ (range (p*n+1)).filter (fun j => ¬p ∣ j), (f j : ZMod m)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨hj, hnd⟩ := mem_filter.mp hj
    have hj' : j ≤ p*n := Nat.le_of_lt_succ (mem_range.mp hj)
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hzero j hj' hnd)
  rw [hz, add_zero]
  symm
  refine Finset.sum_bij' (fun j _ => p*j) (fun j _ => j/p) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hj' : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.mul_le_mul_left p hj')),
      dvd_mul_right _ _⟩
  · intro j hj
    obtain ⟨hj, k, rfl⟩ := mem_filter.mp hj
    rw [Nat.mul_div_cancel_left _ hp]
    exact mem_range.mpr (Nat.lt_succ_of_le
      (Nat.le_of_mul_le_mul_left (Nat.le_of_lt_succ (mem_range.mp hj)) hp))
  · intro j _
    exact Nat.mul_div_cancel_left j hp
  · intro j hj
    simpa only [Nat.mul_comm] using (Nat.div_mul_cancel (mem_filter.mp hj).2)
  · intro j hj
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (hkeep j (Nat.le_of_lt_succ (mem_range.mp hj)))).symm

private lemma inner_mod {p d A B n r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : ¬p ∣ d)
    (hA : p ^ r ∣ A) (hB : p ^ r ∣ B) :
    inner d (p*A) (p*B) (p*n) ≡ inner d A B n [MOD p ^ (2 * (r+1))] := by
  unfold inner
  apply sum_strip hp.pos
  · intro i _ hi
    by_cases hdni : d*i ≤ p*n
    · simp only [if_pos hdni]
      have hni : ¬p ∣ p*n-d*i := by
        intro h
        exact (hp.dvd_mul.mp ((Nat.dvd_sub_iff_right hdni (dvd_mul_right p n)).mp h)).elim hd hi
      have hgA : p^(r+1) ∣ p*A := by
        rw [pow_succ']
        exact Nat.mul_dvd_mul_left _ hA
      have hgB : p^(r+1) ∣ p*B := by
        rw [pow_succ']
        exact Nat.mul_dvd_mul_left _ hB
      rw [Nat.modEq_zero_iff_dvd, Nat.mul_comm 2, pow_mul, pow_two]
      exact Nat.mul_dvd_mul (choose_dvd_unit hp hgA hni) (choose_dvd_unit hp hgB hi)
    · simp [hdni, Nat.ModEq]
  · intro i _
    have hmul : d*(p*i)=p*(d*i) := by ac_rfl
    have hsub : p*n-d*(p*i)=p*(n-d*i) := by rw [hmul, Nat.mul_sub]
    by_cases h : d*i ≤ n
    · have h' : d*(p*i) ≤ p*n := by rw [hmul]; exact Nat.mul_le_mul_left _ h
      simp only [if_pos h, if_pos h', hsub]
      exact (scaled_choose_mod hp hp2 hA).mul (scaled_choose_mod hp hp2 hB)
    · have h' : ¬ d*(p*i) ≤ p*n := by
        rw [hmul]
        exact fun hi => h (Nat.le_of_mul_le_mul_left hi hp.pos)
      simp [h, h', Nat.ModEq]

private lemma index_exponent {p j r : ℕ} (hp : p.Prime) :
    ∃ e ≤ r, p ^ e ∣ j ∧
      (e = r ∨ ∃ t, j = p ^ e * t ∧ ¬p ∣ t) := by
  let _ : Fact p.Prime := ⟨hp⟩
  by_cases h : p^r ∣ j
  · exact ⟨r, le_rfl, h, Or.inl rfl⟩
  · have hj : j ≠ 0 := fun hj => h (hj ▸ dvd_zero _)
    let e := padicValNat p j
    have hel : e < r := lt_of_not_ge (fun hle => h ((padicValNat_dvd_iff_le hj).2 hle))
    have he : p^e ∣ j := pow_padicValNat_dvd
    obtain ⟨t, ht⟩ := he
    refine ⟨e, hel.le, ⟨t, ht⟩, Or.inr ⟨t, ht, ?_⟩⟩
    intro hpt
    have hnext : p^(e+1) ∣ j := by rw [ht, pow_succ]; exact Nat.mul_dvd_mul_left _ hpt
    have := (padicValNat_dvd_iff_le hj).1 hnext
    change e + 1 ≤ e at this
    omega

theorem outer_mod {p d n r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : ¬p ∣ d)
    (hn : p ^ r ∣ n) :
    outer d (p*n) ≡ outer d n [MOD p ^ (2 * (r+1))] := by
  unfold outer
  apply sum_strip hp.pos
  · intro j _ hj
    have hpn : p^(r+1) ∣ p*n := by
      rw [pow_succ']
      exact Nat.mul_dvd_mul_left _ hn
    rw [Nat.modEq_zero_iff_dvd]
    apply dvd_mul_of_dvd_left
    rw [Nat.mul_comm 2, pow_mul]
    exact pow_dvd_pow_of_dvd (choose_dvd_unit hp hpn hj) 2
  · intro j _
    have htop : 3*(p*n)-d*(p*j)=p*(3*n-d*j) := by rw [Nat.mul_sub]; congr 1 <;> ac_rfl
    rw [htop]
    have hweight := (scaled_choose_mod (B := j) hp hp2 hn).pow 2
    obtain ⟨e, her, hj, hex⟩ := index_exponent (j := j) (r := r) hp
    have hn' : p^e ∣ n := (pow_dvd_pow p her).trans hn
    have hab : p^e ∣ 3*n-d*j :=
      Nat.dvd_sub (dvd_mul_of_dvd_right hn' _) (dvd_mul_of_dvd_right hj _)
    have hinner := inner_mod hp hp2 hd hab hj (n := n)
    have hlow : p^(r-e) ∣ (p*n).choose (p*j) := by
      rcases hex with he | ⟨t, ht, hpt⟩
      · simp [he]
      · have hpos : 0 < p*j := by
          have ht0 : 0 < t := Nat.pos_of_ne_zero (fun hx => hpt (hx ▸ dvd_zero _))
          rw [ht]
          exact Nat.mul_pos hp.pos (Nat.mul_pos (pow_pos hp.pos _) ht0)
        have hidx : p*j=p^(e+1)*t := by rw [ht, pow_succ', mul_assoc]
        have hpn : p^(r+1) ∣ p*n := by
          rw [pow_succ']
          exact Nat.mul_dvd_mul_left _ hn
        have h := choose_dvd_of_index hp hpn hpos hidx hpt (show e+1 ≤ r+1 by omega)
        rwa [show r+1-(e+1)=r-e by omega] at h
    have hscaled := hinner.mul_left' ((p*n).choose (p*j) ^ 2)
    have hdiv : p^(2*(r+1)) ∣ (p*n).choose (p*j)^2 * p^(2*(e+1)) := by
      rw [show 2*(r+1)=2*(r-e)+2*(e+1) by omega, pow_add, Nat.mul_comm 2 (r-e), pow_mul]
      exact Nat.mul_dvd_mul (pow_dvd_pow_of_dvd hlow 2) (dvd_refl _)
    exact (hscaled.of_dvd hdiv).trans (hweight.mul_right _)

end ConvolutionScaling

open Finset Polynomial

namespace DiagonalFormula

open ConvolutionScaling

private noncomputable abbrev Xz : Polynomial ℤ := X

private lemma sum_vandermonde (n k : ℕ) (hk : k ≤ n) :
    (∑ j ∈ range (n+1), n.choose j ^ 2 * j.choose k) =
      n.choose k * (2*n-k).choose (n-k) := by
  have h := Nat.add_choose_eq (n-k) n (n-k)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  rw [show 2*n-k = n-k+n by omega, h, Finset.mul_sum]
  calc
    _ = ∑ j ∈ (range (n+1)).filter (k ≤ ·), n.choose j ^ 2 * j.choose k := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hn
      have : j < k := by simp only [mem_filter, hj, true_and] at hn; omega
      simp [Nat.choose_eq_zero_of_lt this]
    _ = _ := by
      refine Finset.sum_bij' (fun j _ => j-k) (fun i _ => i+k) ?_ ?_ ?_ ?_ ?_
      · intro j hj
        simp only [mem_filter, mem_range] at hj
        apply mem_range.mpr
        omega
      · intro i hi
        simp only [mem_range] at hi
        simp only [mem_filter, mem_range]
        omega
      · intro j hj
        have := (mem_filter.mp hj).2
        omega
      · intro i _
        omega
      · intro j hj
        obtain ⟨hj, hkj⟩ := mem_filter.mp hj
        have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
        have hmul := Nat.choose_mul (n := n) hkj
        rw [pow_two, mul_assoc, hmul, show n-k-(j-k)=n-j by omega,
          Nat.choose_symm hjn]
        ring

private lemma factorial_term (n k : ℕ) (hk : k ≤ n) :
    (3*n-2*k).factorial / ((n-k).factorial ^ 3 * k.factorial) =
      n.choose k * (2*n-k).choose (n-k) * (3*n-2*k).choose (n-k) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hk
  have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : n-k ≤ 2*n-k)
  have h3 := Nat.choose_mul_factorial_mul_factorial (by omega : n-k ≤ 3*n-2*k)
  rw [show 2*n-k-(n-k)=n by omega] at h2
  rw [show 3*n-2*k-(n-k)=2*n-k by omega] at h3
  symm
  apply Nat.eq_div_of_mul_eq_right (by positivity)
  calc
    _ = ((3*n-2*k).choose (n-k) * (n-k).factorial) *
      (((2*n-k).choose (n-k) * (n-k).factorial) *
        ((n.choose k) * k.factorial * (n-k).factorial)) := by ring
    _ = _ := by rw [h1, h2, h3]

private lemma coeff_term (n j c : ℕ) (hj : j ≤ n) :
    (((1+Xz)^(3*n-2*j)) * ((1+Xz)^2 + C (-(c:ℤ))*Xz)^j).coeff n =
      ∑ k ∈ range (n+1), (j.choose k : ℤ) * (-(c:ℤ))^k *
        ((3*n-2*k).choose (n-k) : ℤ) := by
  rw [add_comm ((1+Xz)^2), add_pow (C (-(c:ℤ))*Xz) ((1+Xz)^2) j,
    Finset.mul_sum, Polynomial.finsetSum_coeff]
  calc
    _ = ∑ k ∈ range (j+1), (j.choose k : ℤ) * (-(c:ℤ))^k *
          ((3*n-2*k).choose (n-k) : ℤ) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : k ≤ j := Nat.le_of_lt_succ (mem_range.mp hk)
      have hkn : k ≤ n := hkj.trans hj
      rw [mul_pow, ← pow_mul, ← Polynomial.C_pow]
      have hpoly :
          (1+Xz)^(3*n-2*j) *
            (C ((-(c:ℤ))^k) * Xz^k * (1+Xz)^(2*(j-k)) * (j.choose k : Polynomial ℤ)) =
          (C ((j.choose k : ℤ) * (-(c:ℤ))^k) * (1+Xz)^(3*n-2*k)) * Xz^k := by
        rw [Polynomial.C_mul, ← Polynomial.C_eq_natCast, ← show (3*n-2*j)+2*(j-k)=3*n-2*k by omega,
          pow_add]
        ring
      rw [hpoly, Polynomial.coeff_mul_X_pow', if_pos hkn, Polynomial.coeff_C_mul,
        Polynomial.coeff_one_add_X_pow]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hkj
      have hz : j < k := by simp only [mem_range] at hkj; omega
      simp [Nat.choose_eq_zero_of_lt hz]

private def diagonal (c n : ℕ) : ℤ :=
    ∑ k ∈ range (n+1),
      (((3*n-2*k).factorial / ((n-k).factorial^3*k.factorial) : ℕ) : ℤ) * (-(c:ℤ))^k

private lemma diagonal_coeff (c n : ℕ) :
    diagonal c n =
      ∑ j ∈ range (n+1), (n.choose j : ℤ)^2 *
        (((1+Xz)^(3*n-2*j)) * ((1+Xz)^2 + C (-(c:ℤ))*Xz)^j).coeff n := by
  unfold diagonal
  symm
  calc
    _ = ∑ j ∈ range (n+1), ∑ k ∈ range (n+1),
        (n.choose j : ℤ)^2 * ((j.choose k : ℤ) * (-(c:ℤ))^k *
          ((3*n-2*k).choose (n-k) : ℤ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [coeff_term n j c (Nat.le_of_lt_succ (mem_range.mp hj)), Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
      rw [factorial_term n k hkn]
      have hf : (∑ j ∈ range (n+1), (n.choose j : ℤ)^2 * (j.choose k : ℤ)) =
          (n.choose k : ℤ) * ((2*n-k).choose (n-k) : ℤ) := by
        exact_mod_cast sum_vandermonde n k hkn
      calc
        _ = (∑ j ∈ range (n+1), (n.choose j : ℤ)^2 * (j.choose k : ℤ)) *
              ((-(c:ℤ))^k * ((3*n-2*k).choose (n-k) : ℤ)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [hf]; push_cast; ring

private lemma inner_coeff (d a b n : ℕ) :
    (((1+Xz)^a) * ((1+Xz^d)^b)).coeff n = (inner d a b n : ℤ) := by
  rw [add_comm (1 : Polynomial ℤ) (Xz^d), add_pow (Xz^d) 1 b, Finset.mul_sum,
    Polynomial.finsetSum_coeff]
  unfold ConvolutionScaling.inner
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [one_pow, mul_one, ← pow_mul]
  rw [show (1+Xz)^a * (Xz^(d*i) * (b.choose i : Polynomial ℤ)) =
        C (b.choose i : ℤ) * (1+Xz)^a * Xz^(d*i) by
        rw [Polynomial.C_eq_natCast]
        ring]
  rw [Polynomial.coeff_mul_X_pow']
  split_ifs with hd
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
    ring
  · rfl

theorem diagonal_two (n : ℕ) : diagonal 2 n = (outer 2 n : ℤ) := by
  rw [diagonal_coeff]
  unfold outer
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have hB : (1+Xz)^2 + C (-(2:ℤ))*Xz = 1 + Xz^2 := by
    norm_num [Polynomial.C_neg, Polynomial.C_ofNat]
    ring
  rw [hB, inner_coeff]

theorem diagonal_three (n : ℕ) : diagonal 3 n = (outer 3 n : ℤ) := by
  rw [diagonal_coeff]
  unfold outer
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
  have hB : (1+Xz) * ((1+Xz)^2 + C (-(3:ℤ))*Xz) = 1 + Xz^3 := by
    norm_num [Polynomial.C_neg, Polynomial.C_ofNat]
    ring
  rw [show 3*n-2*j = (3*n-3*j)+j by omega, pow_add, mul_assoc, ← mul_pow, hB, inner_coeff]

end DiagonalFormula

theorem OMA.solution : type_of% @OMA.S_oeis_a318109.main := by
  intro p n r hp hp5 _ hr
  change DiagonalFormula.diagonal 2 (n*p^r) ≡
    DiagonalFormula.diagonal 2 (n*p^(r-1)) [ZMOD (p:ℤ)^(2*r)]
  rw [DiagonalFormula.diagonal_two, DiagonalFormula.diagonal_two]
  have hp2 : p ≠ 2 := by omega
  have hnd : ¬p ∣ 2 := by
    intro hd
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have h := ConvolutionScaling.outer_mod (d := 2) (n := n*p^(r-1)) hp hp2 hnd
    (dvd_mul_left _ _)
  have hre : r - 1 + 1 = r := by omega
  have hscale : p * (n * p^(r-1)) = n * p^r := by
    calc
      _ = n * (p^(r-1)*p) := by ac_rfl
      _ = n * p^r := by rw [← pow_succ, hre]
  rw [hscale, hre] at h
  exact_mod_cast h
