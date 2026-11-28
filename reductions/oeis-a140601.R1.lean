import OMAStatements.S_oeis_a140601
import Mathlib

/-!
# Finite searches and local obstructions for the Pascal-triangle divisibility problem

Stefan Steinerberger asks whether infinitely many rows have distinct columns a,b
with C(m,a)+C(m,b) dividing C(m,a+b). On OEIS A140601, Max Alekseyev observed
that a fixed pair of columns contributes only finitely many rows. Here even the
smaller column alone gives an effective bound for all rows and partner columns.
For smaller column at most three, the only triples (a,b,m) are (3,5,19) and
(3,4,104). Mersenne rows never contribute. With odd index sum, m+1 must divide
the least common multiple of the integers 1 through a+b.

Fixing the positive excess m-a-2b also bounds all rows, uniformly in both
columns. The proof combines a logarithmic upper bound for the column gap, a
linear bound on the larger column in the large-gap case, and a fixed divisor
for the sum of the larger column and the excess. Thus both the smaller column
and the complementary-column excess must grow along any infinite sequence
of distinct witnessing rows.

A fixed-column divisor sieve and the prime-power divisibility conditions for any
bounded list of primes and exponents admit arbitrarily large adjacent-column
candidates. Infinitude is equivalent to bounding the smaller index and its row
window uniformly as the precision of these local tests increases. The final
criterion gives an alternative finite decision for each prescribed smaller index.
On the single ray m=4a+3 there are arbitrarily large candidates satisfying all
these finite tests and the lcm condition whose quotient has an obstructing prime.
Nagura's 1952 short-prime-interval theorem, DOI 10.3792/pja/1195570997,
excludes every point on this ray. The implication from that external theorem
and the finite initial range are checked below.

Sources: https://oeis.org/A140601 and its gap-one and gap-two subsequences
https://oeis.org/A140602 and https://oeis.org/A140603.
-/

namespace Pascal140

lemma choose_ratio_step (m a b : ℕ) (hab : a ≤ b) :
    m.choose b * b.descFactorial (b-a) = m.choose a * (m-a).descFactorial (b-a) := by
  simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_symm hab]
  simpa only [mul_left_comm, mul_assoc, mul_comm] using
    congrArg ((b-a).factorial * ·) (Nat.choose_mul (n := m) hab)

lemma asc_congr {g x y : ℕ} (h : Nat.ModEq g x y) (d : ℕ) :
    Nat.ModEq g (x.ascFactorial d) (y.ascFactorial d) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [Nat.ascFactorial_succ]
    exact (h.add_right d).mul ih

/-- Each denominator factor common to the falling factorial can be transferred
to a fixed offset. This retains divisibility, as well as bounding the size. -/
lemma gcd_desc_dvd (E d t a : ℕ) (ht : a ≤ t) :
    (E + (t+1).ascFactorial d).gcd (t.descFactorial a) ∣
      ∏ i ∈ Finset.range a, (E + (i+1).ascFactorial d) := by
  let D := E + (t+1).ascFactorial d
  change D.gcd _ ∣ _
  induction a with
  | zero => simp
  | succ i ih =>
    rw [Nat.descFactorial_succ, Finset.prod_range_succ]
    have hg : D.gcd (t-i) ∣ E + (i+1).ascFactorial d := by
      have hti := Nat.modEq_sub (show i ≤ t by omega)
      have hc := (asc_congr (hti.add_right 1) d).add_left E
      exact (hc.dvd_iff (Nat.gcd_dvd_right D (t-i))).mp (Nat.gcd_dvd_left D (t-i))
    exact (gcd_mul_dvd_mul_gcd D (t-i) (t.descFactorial i)).trans (by
      rw [mul_comm]
      exact Nat.mul_dvd_mul (ih (by omega)) hg)

lemma fixed_index_divisor {a b m : ℕ} (hab : a < b) (hm : a+b ≤ m)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) :
    b.descFactorial (b-a) + (m-b+1).ascFactorial (b-a) ∣
      b.descFactorial (b-a) *
      ∏ i ∈ Finset.range a, (b.descFactorial (b-a) + (i+1).ascFactorial (b-a)) := by
  let E := b.descFactorial (b-a)
  let F := (m-b+1).ascFactorial (b-a)
  let T := (m-b).descFactorial a
  let U := (a+b).descFactorial a
  have ratio : m.choose b * E = m.choose a * F := by
    dsimp only [E,F]
    have rr := choose_ratio_step m a b hab.le
    rw [show m-a = (m-b)+(b-a) by omega, Nat.add_descFactorial_eq_ascFactorial] at rr
    exact rr
  have step : m.choose (a+b) * U = m.choose b * T := by
    simpa [U,T] using choose_ratio_step m b (a+b) (by omega)
  obtain ⟨w, hw⟩ := h
  have hF : E+F ∣ F*T := by
    refine ⟨w*U, ?_⟩
    apply Nat.mul_left_cancel (Nat.choose_pos (n:=m) (k:=a) (by omega))
    calc
      m.choose a * (F * T) = (m.choose b * T) * E := by rw [← mul_assoc, ← ratio]; ring
      _ = ((m.choose a + m.choose b) * w * U) * E := by rw [←step, hw]
      _ = m.choose a * (E+F) * (w*U) := by
        calc
          _ = ((m.choose a * E) + m.choose b * E) * (w*U) := by ring
          _ = _ := by rw [ratio]; ring
      _ = _ := by ring
  have hE : E+F ∣ E*T := by
    have sumD : E+F ∣ E*T + F*T := by rw [←add_mul]; exact dvd_mul_right _ _
    exact (Nat.dvd_add_iff_left hF).mpr sumD
  have hG : E+F ∣ (E+F).gcd T * E := dvd_gcd_mul_of_dvd_mul (by simpa only [mul_comm] using hE)
  change E+F ∣ E*_
  rw [mul_comm E]
  exact hG.trans (Nat.mul_dvd_mul (gcd_desc_dvd E (b-a) (m-b) a (by omega)) (dvd_refl E))


/-- An effective, degree-sensitive bound for the row index of any witness
with fixed columns. -/
lemma fixed_index_bound {a b m : ℕ} (hab : a < b) (hm : a+b ≤ m)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) :
    (m-b+1)^(b-a) < b.descFactorial (b-a) * (2*b.descFactorial (b-a))^a := by
  let E := b.descFactorial (b-a)
  have pos : 0 < E := Nat.descFactorial_pos.mpr (Nat.sub_le _ _)
  have desc : E = (a+1).ascFactorial (b-a) := by
    dsimp only [E]
    calc
      b.descFactorial (b-a) = (a+(b-a)).descFactorial (b-a) := by congr 1; omega
      _ = _ := Nat.add_descFactorial_eq_ascFactorial _ _
  have boundprod : (∏ i ∈ Finset.range a, (E + (i+1).ascFactorial (b-a))) ≤ (2*E)^a := by
    calc
      _ ≤ ∏ _i ∈ Finset.range a, 2*E := by
        apply Finset.prod_le_prod'
        intro i hi
        have leA := Nat.ascFactorial_le (b-a) (show i+1 ≤ a+1 by
          have := Finset.mem_range.mp hi; omega)
        rw [←desc] at leA
        omega
      _ = _ := by simp
  have hD := fixed_index_divisor hab hm h
  change E + (m-b+1).ascFactorial (b-a) ∣
    E * ∏ i ∈ Finset.range a, (E + (i+1).ascFactorial (b-a)) at hD
  have hprod : 0 < ∏ i ∈ Finset.range a, (E + (i+1).ascFactorial (b-a)) :=
    Finset.prod_pos (fun _ _ => by omega)
  have hbound := Nat.le_of_dvd (Nat.mul_pos pos hprod) hD
  have hx := Nat.pow_succ_le_ascFactorial (m-b+1) (b-a)
  have hmax := Nat.mul_le_mul_left E boundprod
  change _ < E * (2*E)^a
  omega

/-- All witnesses whose larger column is at most B occur in a computably
bounded finite interval, independent of the smaller column. -/
lemma bounded_columns {a b m B : ℕ} (hab : a < b) (hb : b ≤ B) (hm : a+b ≤ m)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) :
    m < B + (2*B.factorial)^(B+1) := by
  have hd := fixed_index_bound hab hm h
  have hbase : m-b+1 ≤ (m-b+1)^(b-a) := by
    simpa using Nat.pow_le_pow_right (show 0 < m-b+1 by omega) (show 1 ≤ b-a by omega)
  have hE : b.descFactorial (b-a) ≤ B.factorial :=
    (Nat.le_of_dvd (Nat.factorial_pos b) ⟨(b-(b-a)).factorial, by
      rw [mul_comm, Nat.factorial_mul_descFactorial (Nat.sub_le _ _)]⟩).trans
      (Nat.factorial_le hb)
  have ha : a ≤ B := by omega
  have hpow : (2 * b.descFactorial (b-a))^a ≤ (2*B.factorial)^B :=
    (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hE) a).trans
      (Nat.pow_le_pow_right (by have := Nat.factorial_pos B; omega) ha)
  have hfin := Nat.mul_le_mul (show b.descFactorial (b-a) ≤ 2*B.factorial by omega) hpow
  rw [←pow_succ'] at hfin
  omega

end Pascal140

namespace Pascal140

theorem choose_lt_small_column {a b m : ℕ} (hm : a+b ≤ m)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) :
    m.choose b < m.choose a * (m-b).descFactorial a := by
  have hT : m.choose (a+b) * (a+b).descFactorial a
        = m.choose b * (m-b).descFactorial a := by
    simpa using choose_ratio_step m b (a+b) (by omega)
  have hB : m.choose a + m.choose b ∣ m.choose b * (m-b).descFactorial a :=
    hT ▸ h.trans (dvd_mul_right _ _)
  have hA : m.choose a + m.choose b ∣ m.choose a * (m-b).descFactorial a := by
    apply (Nat.dvd_add_iff_left hB).mpr
    rw [←add_mul]
    exact dvd_mul_right _ _
  have ca : 0 < m.choose a := Nat.choose_pos (by omega)
  have pos : 0 < m.choose a * (m-b).descFactorial a :=
    Nat.mul_pos ca (Nat.descFactorial_pos.mpr (by omega))
  have := Nat.le_of_dvd pos hA
  omega

/-- Taking the gap-th root before bounding the columns improves the
uniform row cutoff. -/
theorem fixed_index_power_bound {a b m : ℕ} (hab : a < b) (hm : a+b ≤ m)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) :
    m-b+1 < (2*b)^(a+1) := by
  let d := b-a
  let E := b.descFactorial d
  have hE : E ≤ b^d := Nat.descFactorial_le_pow b d
  have h2 : 2 ≤ 2^d := by
    have hd : 1 ≤ d := by dsimp [d]; omega
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) hd)
  have h2E : 2*E ≤ (2*b)^d := by
    rw [mul_pow]
    exact Nat.mul_le_mul h2 hE
  have hD := fixed_index_bound hab hm h
  change (m-b+1)^d < E*(2*E)^a at hD
  apply lt_of_pow_lt_pow_left₀ d (Nat.zero_le _)
  calc
    (m-b+1)^d < E*(2*E)^a := hD
    _ ≤ (2*b)^d * ((2*b)^d)^a := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h2E a)
    _ = ((2*b)^(a+1))^d := by rw [←pow_succ', ←pow_mul, ←pow_mul, Nat.mul_comm d (a+1)]

theorem uniform_column_bound {a b m B : ℕ} (hab : a < b) (hb : b ≤ B) (hm : a+b ≤ m)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) :
    m < B + (2*B)^B := by
  have hbnd := fixed_index_power_bound hab hm h
  have hp := (Nat.pow_le_pow_left (show 2*b ≤ 2*B by omega) (a+1)).trans
    (Nat.pow_le_pow_right (show 0 < 2*B by omega) (show a+1 ≤ B by omega))
  omega

end Pascal140

namespace Pascal140

/-- An exact witness criterion using only falling or rising factorials of
the column sizes. -/
theorem witness_iff {a b m : ℕ} (hab : a < b) (hm : a+b ≤ m) :
    (m.choose a + m.choose b ∣ m.choose (a+b)) ↔
    (b.descFactorial (b-a) + (m-b+1).ascFactorial (b-a)) * (a+b).descFactorial a ∣
      (m-b+1).ascFactorial (b-a) * (m-b).descFactorial a := by
  let E := b.descFactorial (b-a)
  let F := (m-b+1).ascFactorial (b-a)
  let T := (m-b).descFactorial a
  let U := (a+b).descFactorial a
  have ratio : m.choose b * E = m.choose a * F := by
    dsimp only [E,F]
    have rr := choose_ratio_step m a b hab.le
    rw [show m-a = (m-b)+(b-a) by omega, Nat.add_descFactorial_eq_ascFactorial] at rr
    exact rr
  have step : m.choose (a+b) * U = m.choose b * T := by
    simpa [U,T] using choose_ratio_step m b (a+b) (by omega)
  have left : m.choose a * ((E+F)*U) = (m.choose a + m.choose b)*(U*E) := by
    calc
      _ = (m.choose a * E + m.choose a * F)*U := by ring
      _ = _ := by rw [←ratio]; ring
  have right : m.choose a * (F*T) = m.choose (a+b)*(U*E) := by
    calc
      _ = (m.choose b*T)*E := by rw [← mul_assoc, ← ratio]; ring
      _ = _ := by rw [←step]; ring
  have hp : 0 < U*E := Nat.mul_pos (Nat.descFactorial_pos.mpr (by omega))
    (Nat.descFactorial_pos.mpr (Nat.sub_le _ _))
  have hc : 0 < m.choose a := Nat.choose_pos (by omega)
  change _ ↔ (E+F)*U ∣ F*T
  calc
    _ ↔ (m.choose a + m.choose b)*(U*E) ∣ m.choose (a+b)*(U*E) :=
      (mul_dvd_mul_iff_right hp.ne').symm
    _ ↔ m.choose a * ((E+F)*U) ∣ m.choose a * (F*T) := by rw [left,right]
    _ ↔ _ := mul_dvd_mul_iff_left hc.ne'

end Pascal140

namespace Pascal140

lemma choose_left_half {m x y : ℕ} (hxy : x ≤ y) (hy : y ≤ m/2) :
    m.choose x ≤ m.choose y := by
  induction hxy with
  | refl => rfl
  | step h ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma witness_in_left_half {a b m : ℕ} (hm : a+b ≤ m)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) : b ≤ m/2 := by
  by_contra! hright
  have cmp : m.choose (a+b) ≤ m.choose b := by
    rw [←Nat.choose_symm hm, ←Nat.choose_symm (show b ≤ m by omega)]
    exact choose_left_half (by omega) (by omega)
  have hlo := Nat.le_of_dvd (Nat.choose_pos hm) h
  have hp : 0 < m.choose a := Nat.choose_pos (by omega)
  omega

private lemma few_low {a b m r : ℕ} (ha : a ≤ 3) (hm : a+b ≤ m) (hr : 3 ≤ r)
    (hrb : r ≤ b) (h : m.choose a + m.choose b ∣ m.choose (a+b)) :
    (m+1-r)^(r-3) < r.descFactorial (r-3) * m^3 := by
  have hhalf := witness_in_left_half hm h
  have ha3 := choose_left_half ha (show 3 ≤ m/2 by omega)
  have hrb' := choose_left_half hrb hhalf
  have hm1 : 0 < m := by omega
  have ht : (m-b).descFactorial a ≤ m^3 :=
    ((Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) a)).trans
      (Nat.pow_le_pow_right hm1 ha)
  have hi : m.choose r < m.choose 3 * m^3 :=
    lt_of_le_of_lt hrb' ((choose_lt_small_column hm h).trans_le (Nat.mul_le_mul ha3 ht))
  have hd := Nat.mul_lt_mul_of_pos_right hi (Nat.descFactorial_pos.mpr (Nat.sub_le r 3))
  rw [choose_ratio_step m 3 r hr] at hd
  rw [mul_assoc, mul_comm (m^3)] at hd
  have hdd := Nat.lt_of_mul_lt_mul_left hd
  have hpow := Nat.pow_sub_le_descFactorial (m-3) (r-3)
  rw [show m-3+1-(r-3)=m+1-r by omega] at hpow
  exact hpow.trans_lt hdd

private lemma row_bound_seven {a b m : ℕ} (ha : a ≤ 3) (hm : a+b ≤ m) (hb : 7 ≤ b)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) : m < 1024 := by
  have hi := few_low ha hm (by decide : 3 ≤ 7) hb h
  by_contra! hn
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  norm_num [Nat.descFactorial, show 1024+t+1-7=1018+t by omega] at hi
  ring_nf at hi
  omega

private lemma row_bound_ten {a b m : ℕ} (ha : a ≤ 3) (hm : a+b ≤ m) (hb : 10 ≤ b)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) : m < 64 := by
  have hi := few_low ha hm (by decide : 3 ≤ 10) hb h
  by_contra! hn
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  norm_num [Nat.descFactorial, show 64+t+1-10=55+t by omega] at hi
  ring_nf at hi
  omega

private lemma small_index_cut {a b m : ℕ} (ha : a ≤ 3) (hab : a < b) (hb : b ≤ 6)
    (hm : a+b ≤ m) (h : m.choose a + m.choose b ∣ m.choose (a+b)) : m < 1024 := by
  have hn : b.descFactorial (b-a) *
      (∏ i ∈ Finset.range a, (b.descFactorial (b-a) + (i+1).ascFactorial (b-a))) <
      b.descFactorial (b-a) + (1024-b+1).ascFactorial (b-a) := by
    interval_cases a <;> interval_cases b <;> first | omega | decide
  have hd := fixed_index_divisor hab hm h
  have hE : 0 < b.descFactorial (b-a) := Nat.descFactorial_pos.mpr (Nat.sub_le _ _)
  have hpos : 0 < ∏ i ∈ Finset.range a, (b.descFactorial (b-a) + (i+1).ascFactorial (b-a)) :=
    Finset.prod_pos (fun _ _ => by omega)
  have hle := Nat.le_of_dvd (Nat.mul_pos hE hpos) hd
  by_contra! hopp
  have hle' := Nat.ascFactorial_le (b-a) (show 1024-b+1 ≤ m-b+1 by omega)
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem classify_small {a b m : ℕ} (ha : a ≤ 3) (hab : a < b) (hm : a+b ≤ m)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) :
    a = 3 ∧ ((m = 19 ∧ b = 5) ∨ (m = 104 ∧ b = 4)) := by
  have hc : m < (if b < 10 then 1024 else 64) := by
    split_ifs with hten
    · by_cases hseven : 7 ≤ b
      · exact row_bound_seven ha hm hseven h
      · exact small_index_cut ha hab (by omega) hm h
    · exact row_bound_ten ha hm (by omega) h
  have hb : b < 32 := by
    have := witness_in_left_half hm h
    split_ifs at hc <;> omega
  let check := fun (i j n : ℕ) => decide (i < j → i+j ≤ n →
    (j.descFactorial (j-i) + (n-j+1).ascFactorial (j-i)) * (i+j).descFactorial i ∣
      (n-j+1).ascFactorial (j-i) * (n-j).descFactorial i →
    i = 3 ∧ ((n = 19 ∧ j = 5) ∨ (n = 104 ∧ j = 4)))
  have checked : (List.range 4).all (fun i => (List.range 32).all (fun j =>
    (List.range (if j < 10 then 1024 else 64)).all (fun n => check i j n))) = true := by
    decide +kernel
  have c₁ := List.all_eq_true.mp checked a (List.mem_range.mpr (by omega))
  have c₂ := List.all_eq_true.mp c₁ b (List.mem_range.mpr hb)
  have c₃ := List.all_eq_true.mp c₂ m (List.mem_range.mpr hc)
  exact (of_decide_eq_true c₃) hab hm ((witness_iff hab hm).mp h)

/-- All witnesses with smaller column at most three, including both directions. -/
theorem small_columns_iff {a b m : ℕ} (ha : a ≤ 3) (hab : a < b) (hm : a+b ≤ m) :
    (m.choose a + m.choose b ∣ m.choose (a+b)) ↔
      a = 3 ∧ ((m = 19 ∧ b = 5) ∨ (m = 104 ∧ b = 4)) := by
  refine ⟨classify_small ha hab hm, ?_⟩
  rintro ⟨rfl, hpair⟩
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> apply (witness_iff hab hm).mpr <;> decide +kernel

end Pascal140

namespace Pascal140

/-- An admissible target lies strictly above the larger chosen entry, so reflection
places that entry strictly to the left of the reflected target. -/
theorem row_lower_bound {m a b : ℕ} (hm : a+b ≤ m)
    (hw : m.choose a + m.choose b ∣ m.choose (a+b)) : a + 2*b < m := by
  have hc := Nat.le_of_dvd (Nat.choose_pos hm) hw
  have hpos := Nat.choose_pos (show a ≤ m by omega)
  by_contra! hs
  have hr : m.choose (a+b) ≤ m.choose b := by
    rw [← Nat.choose_symm hm]
    by_cases hb : b ≤ m/2
    · exact choose_left_half (by omega) hb
    · rw [← Nat.choose_symm (show b ≤ m by omega)]
      exact choose_left_half (by omega) (by omega)
  omega

/-- Even the *smaller* index bounds every possible row effectively. If b exceeds
twice the small-index cutoff, comparison with column 2A+1 beats the growth of
the numerator left after subtracting the integer quotient. -/
theorem small_index_bound {m a b A : ℕ} (hab : a < b) (ha : a ≤ A)
    (hm : a+b ≤ m) (hw : m.choose a + m.choose b ∣ m.choose (a+b)) :
    m < max (2*A+(4*A)^(2*A)) (2^(2*A+1)*(2*A+1).factorial) := by
  rcases le_or_gt b (2*A) with hb | hb
  · apply lt_of_lt_of_le _ (le_max_left _ _)
    simpa only [← Nat.mul_assoc, show 2*2 = 4 by decide] using uniform_column_bound hab hb hm hw
  · apply lt_of_lt_of_le _ (le_max_right _ _)
    let k := 2*A+1
    have hrow := row_lower_bound hm hw
    have hk : k ≤ b := by dsimp [k]; omega
    have hhalf : b ≤ m/2 := by omega
    have hpos : 0 < m := by omega
    have hfm : (m+1-k)^k ≤ k.factorial * m.choose k := by
      simpa only [← Nat.descFactorial_eq_factorial_mul_choose] using m.pow_sub_le_descFactorial k
    have hlow : m^k ≤ 2^k * (k.factorial * m.choose k) := by
      calc
        m^k ≤ (2*(m+1-k))^k := Nat.pow_le_pow_left (by omega) _
        _ = 2^k*(m+1-k)^k := mul_pow _ _ _
        _ ≤ _ := Nat.mul_le_mul_left _ hfm
    have hca := (Nat.choose_le_pow m a).trans (Nat.pow_le_pow_right hpos ha)
    have ht := ((m-b).descFactorial_le_pow a).trans
      ((Nat.pow_le_pow_left (Nat.sub_le m b) a).trans (Nat.pow_le_pow_right hpos ha))
    have hless : m.choose k < m^(2*A) := by
      rw [two_mul, pow_add]
      exact (choose_left_half hk hhalf).trans_lt
        ((choose_lt_small_column hm hw).trans_le (Nat.mul_le_mul hca ht))
    have hstrict : m^k < (2^k*k.factorial)*m^(2*A) := by
      rw [mul_assoc]
      exact hlow.trans_lt (Nat.mul_lt_mul_of_pos_left
        (Nat.mul_lt_mul_of_pos_left hless (Nat.factorial_pos k)) (pow_pos (by decide) _))
    dsimp [k] at hstrict
    rw [pow_succ, mul_comm (m^(2*A)) m] at hstrict
    exact lt_of_mul_lt_mul_right hstrict (Nat.zero_le _)

end Pascal140

namespace Pascal140

/-- The low entries in a row immediately preceding a multiple of a prime power
alternate modulo its prime. -/
theorem alternating_low {p e m : ℕ} (hp : p.Prime) (hd : p^e ∣ m+1)
    (k : ℕ) (hk : k < p^e) : (m.choose k : ZMod p) = (-1)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hz : p ∣ (m+1).choose (k+1) := by
      by_contra h
      have hmul : p^e ∣ (m+1).choose (k+1)*(k+1) := by
        rw [← Nat.add_one_mul_choose_eq]
        exact dvd_mul_of_dvd_left hd _
      have hc := (hp.coprime_iff_not_dvd.mpr h).pow_left e
      exact hk.not_ge (Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left hmul))
    have hz' := (ZMod.natCast_eq_zero_iff _ _).mpr hz
    rw [Nat.choose_succ_succ, Nat.cast_add] at hz'
    rw [pow_succ, ← ih (by omega)]
    linear_combination hz'

private theorem two_units (a b : ℕ) : (-1 : ZMod 2)^a + (-1)^b = 0 := by
  have h : (-1 : ZMod 2) = 1 := by decide
  rw [h, one_pow, one_pow]
  decide

/-- For an odd index sum, every prime power dividing the row number plus one is bounded
by the index sum. At the prime two the same bound holds for every witness. -/
theorem prime_power_bound {p e m a b : ℕ} (hp : p.Prime) (hd : p^e ∣ m+1)
    (hw : m.choose a + m.choose b ∣ m.choose (a+b)) (hs : Odd (a+b) ∨ p=2) :
    p^e ≤ a+b := by
  by_contra! h
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨q,hq⟩ := hw
  have hq' := congrArg (fun n : ℕ => (n : ZMod p)) hq
  push_cast at hq'
  rw [alternating_low hp hd _ h, alternating_low hp hd _ (by omega : a < p^e),
    alternating_low hp hd _ (by omega : b < p^e)] at hq'
  have hcancel : (-1 : ZMod p)^a + (-1)^b = 0 := by
    rcases hs with hodd | rfl
    · rcases Nat.even_or_odd a with ha | ha <;> rcases Nat.even_or_odd b with hb | hb
      · exact False.elim (Nat.not_even_iff_odd.mpr hodd (ha.add hb))
      · simp [ha.neg_one_pow, hb.neg_one_pow]
      · simp [ha.neg_one_pow, hb.neg_one_pow]
      · exact False.elim (Nat.not_even_iff_odd.mpr hodd (ha.add_odd hb))
    · exact two_units a b
  rw [hcancel, zero_mul] at hq'
  exact (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hq'

theorem odd_sum_lcm {m a b : ℕ} (hw : m.choose a + m.choose b ∣ m.choose (a+b))
    (hs : Odd (a+b)) : m+1 ∣ (Finset.Icc 1 (a+b)).lcm id := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e hp hd
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr
    ⟨Nat.one_le_pow _ _ hp.pos, prime_power_bound hp hd hw (Or.inl hs)⟩)

theorem mersenne_not_term (e : ℕ) : ¬ OMA.S_oeis_a140601.IsTerm (2^e-1) := by
  rintro ⟨a,b,_,hle,hw⟩
  have hpos : 0 < 2^e := pow_pos (by decide) _
  have hd : 2^e ∣ (2^e-1)+1 := by rw [Nat.sub_add_cancel (by omega)]
  have := prime_power_bound Nat.prime_two hd hw (Or.inr rfl)
  omega

end Pascal140

namespace Pascal140

/-- In a row divisible by M, every column congruent to one modulo M is
itself divisible by M. -/
lemma choose_succ_multiple {M m j : ℕ} (hm : M ∣ m) (hj : M ∣ j) :
    M ∣ m.choose (j+1) := by
  cases m with
  | zero => simp
  | succ n =>
    have tot : M ∣ (n+1).choose (j+1) * (j+1) := by
      rw [←Nat.add_one_mul_choose_eq]
      exact dvd_mul_of_dvd_left hm _
    rw [mul_add, mul_one] at tot
    exact (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hj _)).mpr tot

/-- The fixed-index resultant, the adjacent-column prime-power restriction,
and the divisibility test modulo any t! have simultaneous solutions with
arbitrarily large smaller column. -/
theorem local_points_full (K t : ℕ) : ∃ a b m : ℕ,
    K < a ∧ b = a+1 ∧ a+2*b < m ∧
    (b.descFactorial (b-a)+(m-b+1).ascFactorial (b-a) ∣ b.descFactorial (b-a)*
      (∏ i ∈ Finset.range a, (b.descFactorial (b-a)+(i+1).ascFactorial (b-a)))) ∧
    m+1 ∣ (Finset.Icc 1 (a+b)).lcm id ∧
    (m.choose a+m.choose b).gcd t.factorial ∣ m.choose (a+b) := by
  let M := t.factorial
  let c := 4*M+1
  let a := 4*M*(2+(K+1)*c)
  let m := c*a+4*M
  have pos : 0 < M := Nat.factorial_pos t
  have hc : 5 ≤ c := by dsimp only [c]; omega
  have hmul : K+1 ≤ (K+1)*c := Nat.le_mul_of_pos_right _ (by omega)
  have hmul' : 2+(K+1)*c ≤ a := Nat.le_mul_of_pos_left _ (by omega)
  have hk : K < a := by omega
  have hca : c ≤ a := by
    have := Nat.le_mul_of_pos_left c (by omega : 0 < K+1)
    omega
  have hquad : 5*a ≤ c*a := Nat.mul_le_mul_right a hc
  have hsep : a+2*(a+1) < m := by dsimp only [m]; omega
  have hfac : m+1 = c*(a+1) := by dsimp only [m,c]; ring
  have hcdiv : c ∣ a+2 := ⟨2+4*M*(K+1), by dsimp only [a,c]; ring⟩
  have hhalf : a+1 ≤ m := by omega
  refine ⟨a, a+1, m, hk, rfl, hsep, ?_, ?_, ?_⟩
  · simp only [Nat.add_sub_cancel_left, Nat.descFactorial_one, Nat.ascFactorial_succ,
      Nat.ascFactorial_zero, Nat.add_zero, Nat.mul_one]
    rw [show a+1+(m-(a+1)+1)=m+1 by omega, hfac]
    have hz : 0 ∈ Finset.range a := Finset.mem_range.mpr (by omega)
    have hfactor := Finset.dvd_prod_of_mem (fun i : ℕ => a+1+(i+1)) hz
    have hcprod : c ∣ ∏ i ∈ Finset.range a, (a+1+(i+1)) := hcdiv.trans hfactor
    rw [mul_comm c]
    exact Nat.mul_dvd_mul (dvd_refl _) hcprod
  · have hcop : Nat.Coprime c (a+1) := Nat.Coprime.of_dvd_left hcdiv
      (Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _))
    rw [hfac]
    apply hcop.mul_dvd_of_dvd_of_dvd
    · exact Finset.dvd_lcm (f:=id) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    · exact Finset.dvd_lcm (f:=id) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  · have hA : M ∣ a := ⟨4*(2+(K+1)*c), by dsimp only [a]; ring⟩
    have hM : M ∣ m := dvd_add (dvd_mul_of_dvd_right hA _) (dvd_mul_left _ _)
    have hJ : M ∣ a+a := dvd_add hA hA
    rw [show a+(a+1)=(a+a)+1 by omega]
    exact (Nat.gcd_dvd_right _ _).trans (choose_succ_multiple hM hJ)

theorem local_points (K t : ℕ) : ∃ a b m : ℕ,
    K < a ∧ a < b ∧ a+2*b < m ∧
    (b.descFactorial (b-a)+(m-b+1).ascFactorial (b-a) ∣ b.descFactorial (b-a)*
      (∏ i ∈ Finset.range a, (b.descFactorial (b-a)+(i+1).ascFactorial (b-a)))) ∧
    (m.choose a+m.choose b).gcd t.factorial ∣ m.choose (a+b) := by
  obtain ⟨a,b,m,hk,hb,hm,hd,_,hg⟩ := local_points_full K t
  exact ⟨a,b,m,hk,by omega,hm,hd,hg⟩

end Pascal140

namespace Pascal140

/-- Every prime divisor of the quadratic denominator in a gap-two witness is
at most the square of one more than the smaller column. -/
theorem gap_two_prime_bound {a m p : ℕ} (ha : 0 < a) (hm : a+(a+2) ≤ m)
    (h : m.choose a + m.choose (a+2) ∣ m.choose (a+(a+2))) (hp : p.Prime)
    (hd : p ∣ (a+1)*(a+2) + (m-a)*(m-a-1)) : p ≤ (a+1)^2 := by
  have hD := fixed_index_divisor (show a < a+2 by omega) hm h
  rw [show a+2-a=2 by omega] at hD
  have desc : (a+2).descFactorial 2 = (a+1)*(a+2) := by
    rw [Nat.descFactorial_succ,Nat.descFactorial_one]; congr 1
  have asc (x : ℕ) : (x+1).ascFactorial 2 = (x+1)*(x+2) := by
    simp [Nat.ascFactorial_succ,mul_comm]
  rw [desc,asc,show m-(a+2)+1=m-a-1 by omega,show m-(a+2)+2=m-a by omega,
    Nat.mul_comm (m-a-1) (m-a)] at hD
  rcases hp.dvd_mul.mp (hd.trans hD) with hq | hprod
  · rcases hp.dvd_mul.mp hq with h1 | h2
    · have := Nat.le_of_dvd (by omega : 0<a+1) h1
      nlinarith
    · have := Nat.le_of_dvd (by omega : 0<a+2) h2
      nlinarith [Nat.mul_self_le_mul_self (show 1≤a by omega)]
  · obtain ⟨i, hi, hf⟩ := (hp.prime.dvd_finsetProd_iff _).mp hprod
    rw [Finset.mem_range] at hi
    rw [asc] at hf
    have even : 2 ∣ (a+1)*(a+2)+(i+1)*(i+2) :=
      dvd_add (Nat.two_dvd_mul_add_one (a+1)) (Nat.two_dvd_mul_add_one (i+1))
    obtain ⟨u, hu⟩ := even
    rw [hu] at hf
    rcases hp.dvd_mul.mp hf with ht | hu'
    · have := Nat.le_of_dvd (by decide : 0<2) ht
      nlinarith
    · have hu0 : 0 < u := by nlinarith
      have hp' := Nat.le_of_dvd hu0 hu'
      have hprodle := Nat.mul_le_mul (show i+1 ≤ a by omega) (show i+2 ≤ a+1 by omega)
      nlinarith

end Pascal140

namespace Pascal140

lemma reflected_desc (l u v t : ℕ) (hs : u+v=l+l) (ht : t≤u+1) :
    ((u.descFactorial t : ℕ) : ZMod l) = (-1)^t * (v.ascFactorial t : ℕ) := by
  have hz : (l : ZMod l) = 0 := ZMod.natCast_self l
  have reflect (i : ℕ) (hi : i ∈ Finset.range t) :
      ((u-i:ℕ):ZMod l) = -((v+i:ℕ):ZMod l) := by
    have hi' := Finset.mem_range.mp hi
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_add, show u-i+(v+i)=l+l by omega, Nat.cast_add, hz, zero_add]
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_congr rfl reflect,
    Finset.prod_neg, Finset.card_range, Nat.ascFactorial_eq_prod_range, Nat.cast_prod]

/-- For a witness in row `m=a+2*b+c`, reflection bounds the distance from the last
chosen column `b` to the reflected target `b+c` by a rising-factorial divisor. -/
theorem general_excess_divisor {a b m c : ℕ} (hab : a<b) (hc : 0<c) (hm : m=a+2*b+c)
    (hw : m.choose a + m.choose b ∣ m.choose (a+b)) :
    b+c ∣ c.ascFactorial (b-a+c) := by
  let d := b-a
  let l := b+c
  let U := b.descFactorial d
  let V := (m-a).descFactorial d
  have hpos := Nat.choose_pos (show a ≤ m by omega)
  have r1 : m.choose b * U = m.choose a * V := choose_ratio_step m a b hab.le
  have r2 := choose_ratio_step m b l (by dsimp [l]; omega)
  rw [show l-b=c by dsimp [l]; omega] at r2
  have hchoose : m.choose l = m.choose (a+b) := by
    rw [show l=m-(a+b) by dsimp [l]; omega]
    exact Nat.choose_symm (by omega)
  obtain ⟨v,hv⟩ := hw
  rw [hchoose,hv] at r2
  have eq : v*(U+V)*l.descFactorial c=V*(m-b).descFactorial c := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc
      _ = v*(m.choose a*U + m.choose a*V)*l.descFactorial c := by ring
      _ = _ := by rw [← r1]; nlinarith [congrArg (· * U) r2]
  have hul : l ∣ l.descFactorial c := by
    obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
    change b+(u+1) ∣ (b+(u+1)).descFactorial (u+1)
    rw [← Nat.add_assoc, Nat.succ_descFactorial_succ]
    exact dvd_mul_right _ _
  have hh : l ∣ V * (m-b).descFactorial c := eq ▸ dvd_mul_of_dvd_right hul _
  have zz := (ZMod.natCast_eq_zero_iff _ l).mpr hh
  change ((V*(m-b).descFactorial c : ℕ) : ZMod l) = 0 at zz
  rw [Nat.cast_mul, show V=(m-a).descFactorial d from rfl,
    reflected_desc l (m-a) c d (by dsimp [l];omega) (by dsimp [d];omega),
    reflected_desc l (m-b) (c+d) c (by dsimp [l,d];omega) (by omega)] at zz
  apply (ZMod.natCast_eq_zero_iff _ l).mp
  change ((c.ascFactorial (d+c) : ℕ):ZMod l)=0
  have concat (e : ℕ) : c.ascFactorial (d+e) = c.ascFactorial d * (c+d).ascFactorial e := by
    induction e with
    | zero => simp
    | succ e ih => rw [← Nat.add_assoc,Nat.ascFactorial_succ,ih,Nat.ascFactorial_succ]; ring
  rw [concat, Nat.cast_mul]
  have hu : IsUnit ((-1:ZMod l)^d * (-1)^c) := (isUnit_neg_one.pow d).mul (isUnit_neg_one.pow c)
  apply hu.mul_right_eq_zero.mp
  linear_combination zz

end Pascal140

namespace Pascal140

private theorem double_choose_growth (m a s : ℕ) (hs : 3*(a+s) ≤ m+1) :
    2^s * m.choose a ≤ m.choose (a+s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hstep : 2 * m.choose (a+s) ≤ m.choose (a+s+1) := by
      apply Nat.le_of_mul_le_mul_right (c:=a+s+1) _ (by omega)
      rw [Nat.choose_succ_right_eq]
      have h := Nat.mul_le_mul_left (m.choose (a+s)) (show 2*(a+s+1) ≤ m-(a+s) by omega)
      nlinarith only [h]
    have h := Nat.mul_le_mul_left 2 (ih (by omega))
    rw [pow_succ,←Nat.add_assoc]
    nlinarith only [h,hstep]

private theorem choose_on_left {m r b : ℕ} (h : r ≤ b) (hb : 2*b ≤ m) :
    m.choose r ≤ m.choose b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b h ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem two_pow_gap_le_choose {m a b e : ℕ} (hab : a < b) (hm : m=a+2*b+e) :
    2^(2*(b-a)/3) * m.choose a ≤ m.choose b :=
  (double_choose_growth m a _ (by omega)).trans (choose_on_left (by omega) (by omega))

/-- If the gap `e` between the complementary target column and `b` is fixed,
the column gap `b-a` is at most logarithmic in the row number. -/
theorem gap_bound_of_target_excess {m a b e : ℕ} (hab : a < b) (hm : m = a+2*b+e)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) :
    2^(2*(b-a)/3) < (m-b)^e := by
  let A := m.choose a
  let B := m.choose b
  let P := (m-b).descFactorial e
  let Q := (b+e).descFactorial e
  obtain ⟨u, hu⟩ := h
  have hA : 0 < A := Nat.choose_pos (by omega)
  have hB : 0 < B := Nat.choose_pos (by omega)
  have hu0 : 0 < u := by
    have hpos := Nat.choose_pos (n:=m) (k:=a+b) (by omega)
    rw [hu] at hpos
    exact Nat.pos_of_mul_pos_left hpos
  let V := u*Q
  have hV : 0 < V := Nat.mul_pos hu0 (Nat.descFactorial_pos.mpr (by omega))
  have hratio : B*P = (A+B)*V := by
    have hcross := choose_ratio_step m b (b+e) (by omega)
    rw [show b+e-b=e by omega] at hcross
    rw [← Nat.choose_symm (n:=m) (k:=a+b) (by omega)] at hu
    rw [show m-(a+b)=b+e by omega] at hu
    rw [hu] at hcross
    unfold B P A V Q
    simpa [mul_assoc] using hcross.symm
  have hlt : V < P := by
    by_contra! hbad
    have h1 := Nat.mul_le_mul_left B hbad
    have h2 := Nat.mul_pos hA hV
    nlinarith only [hratio,h1,h2]
  have hBA : B ≤ A*V := by
    have h1 := Nat.mul_le_mul_left B (Nat.succ_le_of_lt hlt)
    nlinarith only [hratio,h1]
  let s := 2*(b-a)/3
  have lower : 2^s*A ≤ B := two_pow_gap_le_choose hab hm
  calc
    2^(2*(b-a)/3) ≤ V := Nat.le_of_mul_le_mul_right (by simpa [mul_comm V A] using lower.trans hBA) hA
    _ < P := hlt
    _ ≤ (m-b)^e := Nat.descFactorial_le_pow ..

end Pascal140

namespace Pascal140

/-- The first row beyond the reflected-column cutoff never contributes a witness. -/
theorem no_first_excess {a b m : ℕ} (hab : a < b) (hm : m=a+2*b+1) :
    ¬m.choose a + m.choose b ∣ m.choose (a+b) := by
  intro hw
  have ht : a+b ≤ m := by omega
  let A := m.choose a
  let B := m.choose b
  let Z := m.choose (a+b)
  have hA : 0 < A := Nat.choose_pos (by omega)
  have hB : 0 < B := Nat.choose_pos (by omega)
  have hZ : 0 < Z := Nat.choose_pos ht
  have hratio : Z*(b+1) = B*(a+b+1) := by
    have hr := Nat.choose_succ_right_eq m b
    rw [show m-b = a+b+1 by omega] at hr
    dsimp only [Z,B]
    rw [←Nat.choose_symm ht,show m-(a+b)=b+1 by omega]
    exact hr
  have hsmall : Z < 2*B := by
    suffices Z*(b+1) < (2*B)*(b+1) from Nat.lt_of_mul_lt_mul_right this
    rw [hratio]
    have h1 := Nat.mul_lt_mul_of_pos_left (show a+b+1 < 2*(b+1) by omega) hB
    nlinarith only [h1]
  obtain ⟨q,hq⟩ := hw
  change Z=(A+B)*q at hq
  have hq1 : q=1 := by
    by_cases hq0 : q=0
    · simp [hq0] at hq
      omega
    by_contra! hh
    have hc := Nat.mul_le_mul_left (A+B) (show 2≤q by omega)
    omega
  rw [hq1,mul_one] at hq
  have heq : B*a=A*(b+1) := by nlinarith only [hratio,congrArg (fun x : ℕ => x*(b+1)) hq]
  by_cases ha0 : a=0
  · simp [ha0] at heq
    omega
  by_cases ha1 : a=1
  · subst a
    by_cases hbs : b≤2
    · have hbe : b=2 := by omega
      subst b; subst m
      change (6:ℕ).choose 2 * 1 = (6:ℕ).choose 1 * (2+1) at heq
      exact (by decide : ¬(6:ℕ).choose 2 * 1 = (6:ℕ).choose 1 * (2+1)) heq
    have hle := choose_left_half (show 3 ≤ b by omega) (show b ≤ m/2 by omega)
    change m.choose 3 ≤ B at hle
    have hfact := Nat.descFactorial_eq_factorial_mul_choose m 3
    simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero,mul_one] at hfact
    norm_num [Nat.factorial] at hfact
    have hflat : B=m*(b+1) := by simpa [A] using heq
    have hchoose := Nat.mul_le_mul_left 6 hle
    rw [hflat] at hchoose
    have hm1 : m-1=2*b+1 := by omega
    have hm2 : m-2=2*b := by omega
    rw [hm1,hm2] at hfact
    have hbb := Nat.mul_le_mul_right b (show 3≤b by omega)
    have hgt : 6*(b+1) < 2*b*(2*b+1) := by nlinarith only [hbb,show 3≤b by omega]
    have hcontra := Nat.mul_lt_mul_of_pos_left hgt (show 0 < m by omega)
    nlinarith only [hchoose,hfact,hcontra]
  have hs : 2≤a := by omega
  have hg := choose_left_half (show a+1 ≤ b by omega) (show b ≤ m/2 by omega)
  have hh := Nat.mul_le_mul_right (a+1) hg
  rw [Nat.choose_succ_right_eq,show m-a=2*b+1 by omega] at hh
  change A*(2*b+1) ≤ B*(a+1) at hh
  have h2 := Nat.mul_le_mul_right a hh
  have h3 := congrArg (fun x : ℕ => x*(a+1)) heq
  have hab2 := Nat.mul_le_mul_right b (show 2≤a by omega)
  have h4 := Nat.mul_lt_mul_of_pos_left (show (a+1)*(b+1) < (2*b+1)*a by nlinarith only [hab2,hab,hs]) hA
  nlinarith only [h2,h3,h4]

end Pascal140

namespace Pascal140

/-- A single prime in the indicated short interval separates the two
binomial coefficients in the adjacent-column ray. -/
theorem ray_prime_excludes {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime)
    (hlo : 3*n < 2*p) (hhi : p ≤ 2*n) :
    ¬ ((4*n-1).choose (n-1) + (4*n-1).choose n ∣ (4*n-1).choose (n-1+n)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := by omega
  have hne : p ≠ 2*n := by
    intro he
    have hx : 2 ∣ p := he ▸ dvd_mul_right 2 n
    rcases (Nat.dvd_prime hp).mp hx with h | h <;> omega
  have dig {x r q : ℕ} (hr : r < p) (hx : x = r+p*q) :
      x%p = r ∧ x/p = q := by
    rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr,
      Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hr, zero_add]
    exact ⟨rfl,rfl⟩
  have d₀ := dig (x:=4*n) (r:=4*n-2*p) (q:=2) (by omega) (by omega)
  have hd : p ∣ (4*n).choose n := by
    have hc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=p) (n:=4*n) (k:=n)
    rw [d₀.1, Nat.mod_eq_of_lt (by omega : n < p),
      Nat.choose_eq_zero_of_lt (by omega : 4*n-2*p < n), zero_mul] at hc
    exact Nat.modEq_zero_iff_dvd.mp hc
  have d₁ := dig (x:=4*n-1) (r:=4*n-1-2*p) (q:=2) (by omega) (by omega)
  have d₂ := dig (x:=n-1+n) (r:=n-1+n-p) (q:=1) (by omega) (by omega)
  have hnd : ¬p ∣ (4*n-1).choose (n-1+n) := by
    have hc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=p) (n:=4*n-1) (k:=n-1+n)
    rw [d₁.1, d₁.2, d₂.1, d₂.2, Nat.choose_one_right] at hc
    intro h
    rcases hp.dvd_mul.mp ((hc.dvd_iff (dvd_refl p)).mp h) with h' | h'
    · exact (hp.coprime_iff_not_dvd.mp (hp.coprime_choose_of_lt (by omega) (by omega))) h'
    · exact (Nat.not_dvd_of_pos_of_lt (by omega) hp2) h'
  have hsum : (4*n-1).choose (n-1) + (4*n-1).choose n = (4*n).choose n := by
    have h := Nat.choose_succ_succ (4*n-1) (n-1)
    rw [show (4*n-1).succ=4*n by omega, show (n-1).succ=n by omega] at h
    exact h.symm
  rw [hsum]
  exact fun h => hnd (hd.trans h)

end Pascal140

namespace Pascal140

/-- A shifted Catalan divisibility. -/
theorem shifted_central (v : ℕ) : v+2 ∣ 6*v.centralBinom := by
  have h : v+2 ∣ 2*(2*v+1)*v.centralBinom := by
    rw [← Nat.succ_mul_centralBinom_succ]
    exact dvd_mul_of_dvd_right (Nat.succ_dvd_centralBinom (v+1)) _
  have h' : v+2 ∣ 2*(2*v+1)*v.centralBinom + 6*v.centralBinom := by
    exact ⟨4*v.centralBinom, by ring⟩
  exact (Nat.dvd_add_iff_right h).mpr h'

theorem ray_divisibility (a : ℕ) : a+2 ∣ 6*(4*a+3).choose (2*a+1) := by
  have hc : (2*a+2).centralBinom = 2*(4*a+3).choose (2*a+1) := by
    rw [Nat.centralBinom_eq_two_mul_choose, show 2*(2*a+2)=(4*a+3)+1 by omega,
      show 2*a+2=(2*a+1)+1 by omega, Nat.choose_succ_succ]
    rw [show (4*a+3).choose (2*a+1+1) = (4*a+3).choose (2*a+1) from
      Nat.choose_symm_of_eq_add (by omega)]
    omega
  have hd := shifted_central (2*a+2)
  rw [hc,show 2*a+2+2=2*(a+2) by omega,
    show 6*(2*(4*a+3).choose (2*a+1))=2*(6*(4*a+3).choose (2*a+1)) by ring] at hd
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) hd

/-- An arbitrary finite precision can be passed on the single ray m=4a+3, in
a region controlled by a prime strictly between 3(a+1)/2 and 2(a+1). -/
theorem ray_parameters (K t : ℕ) : ∃ a p : ℕ, K < a ∧ p.Prime ∧
    3*(a+1) < 2*p ∧ p ≤ 2*(a+1) ∧ 4 ∣ a+2 ∧
    t.factorial ∣ (4*a+3).choose (2*a+1) := by
  let S := 2*t.factorial
  have hS : 0 < S := Nat.mul_pos (by decide) (Nat.factorial_pos _)
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (10*S*(K+10))
  let j := p/(10*S)
  have hden : 0 < 10*S := by omega
  have hj : K+10 ≤ j := (Nat.le_div_iff_mul_le hden).mpr (by simpa [mul_comm] using hp)
  have hjp : 10*S*j ≤ p := by simpa [j,mul_comm] using (Nat.div_mul_le_self p (10*S))
  have hup : p < 10*S*(j+1) := by
    have := Nat.mod_lt p hden
    have := Nat.mod_add_div p (10*S)
    dsimp [j]
    nlinarith
  let a := 6*S*j-2
  have hSj : j ≤ S*j := Nat.le_mul_of_pos_left _ hS
  have hprod : 2 ≤ 6*S*j := by nlinarith only [hSj,hj]
  have ha : a+2=6*S*j := Nat.sub_add_cancel hprod
  have hjs : 10*S ≤ S*j := by have := Nat.mul_le_mul_left S (show 10 ≤ j by omega); omega
  have h4 : 4 ∣ a+2 := ⟨3*t.factorial*j,by rw [ha]; dsimp only [S]; ring⟩
  have h6 : 6*t.factorial ∣ a+2 := ⟨2*j,by rw [ha]; dsimp only [S]; ring⟩
  exact ⟨a,p,by nlinarith only [ha,hSj,hj],hprime,by nlinarith only [ha,hjp,hS,hSj,hj],
    by nlinarith only [ha,hup,hS,hjs],h4,
    Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 6) (h6.trans (ray_divisibility a))⟩

end Pascal140

namespace Pascal140

/-- A whole ray of adjacent-column candidates can pass the fixed divisor sieve,
the lcm restriction, and any specified finite set of prime-power tests and still
have a strictly nonintegral quotient, at arbitrarily large indices. -/
theorem ray_false_positives (K t : ℕ) : ∃ a : ℕ, K < a ∧
    (4*a+4 ∣ (a+1)*∏ i ∈ Finset.range a, (a+2+i)) ∧
    (4*a+4 ∣ (Finset.Icc 1 (2*a+1)).lcm id) ∧
    t.factorial ∣ (4*a+3).choose (2*a+1) ∧
    ¬ (4*a+3).choose a + (4*a+3).choose (a+1) ∣ (4*a+3).choose (2*a+1) := by
  obtain ⟨a,p,hK,hp,hlo,hhi,h4,ht⟩ := ray_parameters (K+4) t
  have hfac : 4*a+4=4*(a+1) := by ring
  have hcop : Nat.Coprime 4 (a+1) := Nat.Coprime.of_dvd_left h4
    (Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _))
  refine ⟨a,by omega,?_,?_,ht,?_⟩
  · rw [hfac,mul_comm 4]
    have hprod := Finset.dvd_prod_of_mem (fun i : ℕ => a+2+i)
      (Finset.mem_range.mpr (by omega : 0 < a))
    exact Nat.mul_dvd_mul (dvd_refl _) (h4.trans hprod)
  · rw [hfac]
    exact hcop.mul_dvd_of_dvd_of_dvd
      (Finset.dvd_lcm (f:=id) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
      (Finset.dvd_lcm (f:=id) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
  · have he := ray_prime_excludes (n:=a+1) (p:=p) (by omega) hp hlo hhi
    simpa only [Nat.add_sub_cancel, show 4*(a+1)-1=4*a+3 by omega,
      show a+(a+1)=2*a+1 by omega] using he

end Pascal140

namespace Pascal140

/-- Nagura's short-prime-interval theorem (1952, DOI 10.3792/pja/1195570997)
implies that no point of this adjacent-column ray is an actual witness.
The finite initial segment is checked using the factorial ratio. -/
theorem ray_exclusion_of_short_primes
    (short_primes : ∀ x : ℕ, 25 < x → ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ 5*p ≤ 6*x)
    (a : ℕ) : ¬ (4*a+3).choose a + (4*a+3).choose (a+1) ∣ (4*a+3).choose (2*a+1) := by
  by_cases small : a < 17
  · intro hw
    have hw' : (4*a+3).choose a + (4*a+3).choose (a+1) ∣ (4*a+3).choose (a+(a+1)) := by
      simpa only [show a+(a+1)=2*a+1 by omega] using hw
    have hn := (witness_iff (show a < a+1 by omega) (show a+(a+1) ≤ 4*a+3 by omega)).mp hw'
    have finite_test : ∀ i : Fin 17, let k := i.val
      ¬ ((k+1).descFactorial (k+1-k)+(4*k+3-(k+1)+1).ascFactorial (k+1-k)) *
        (k+(k+1)).descFactorial k ∣ (4*k+3-(k+1)+1).ascFactorial (k+1-k) *
        (4*k+3-(k+1)).descFactorial k := by decide +kernel
    exact finite_test ⟨a,small⟩ hn
  · let x := 3*(a+1)/2+1
    obtain ⟨p,hp,hlo,hhi⟩ := short_primes x (by dsimp [x]; omega)
    dsimp [x] at hlo hhi
    have he := ray_prime_excludes (n:=a+1) (p:=p) (by omega) hp (by omega) (by omega)
    simpa only [Nat.add_sub_cancel,show 4*(a+1)-1=4*a+3 by omega,
      show a+(a+1)=2*a+1 by omega] using he

end Pascal140

namespace Pascal140

theorem ordered_term {m : ℕ} (hm : OMA.S_oeis_a140601.IsTerm m) :
    ∃ a b : ℕ, a < b ∧ a+b ≤ m ∧ m.choose a + m.choose b ∣ m.choose (a+b) := by
  obtain ⟨a,b,hd,hle,hw⟩ := hm
  rcases lt_or_gt_of_ne hd with hl | hr
  · exact ⟨a,b,hl,hle,hw⟩
  · exact ⟨b,a,hr,by omega,by simpa only [Nat.add_comm b a, Nat.add_comm (m.choose b) (m.choose a)] using hw⟩

theorem large_small_column (h : {m : ℕ | OMA.S_oeis_a140601.IsTerm m}.Infinite) (K : ℕ) :
    ∃ a b m : ℕ, K < a ∧ a < b ∧ a+b ≤ m ∧ m.choose a+m.choose b ∣ m.choose (a+b) := by
  obtain ⟨m,hm,hK⟩ := h.exists_gt (max (2*K+(4*K)^(2*K)) (2^(2*K+1)*(2*K+1).factorial))
  obtain ⟨a,b,hab,hle,hw⟩ := ordered_term hm
  exact ⟨a,b,m, by by_contra! ha; have := small_index_bound hab ha hle hw; omega,hab,hle,hw⟩

end Pascal140

namespace OMA.R_oeis_a140601_R1
open Pascal140
open OMA.S_oeis_a140601

/-- Every finite collection of prime-power tests can be passed, even after imposing
the exact fixed-column divisor sieve and the geometric lower bound on the row. -/
def H1 : Prop := ∀ K t : ℕ, ∃ a b m : ℕ, K < a ∧ a < b ∧ a+2*b < m ∧
    (b.descFactorial (b-a)+(m-b+1).ascFactorial (b-a) ∣ b.descFactorial (b-a)*
      ∏ i ∈ Finset.range a, (b.descFactorial (b-a)+(i+1).ascFactorial (b-a))) ∧
    (m.choose a + m.choose b).gcd t.factorial ∣ m.choose (a+b)

/-- Can the smaller column of a successful finite test be kept in a bounded window
above each prescribed lower limit, at arbitrarily high precision? The row ceiling
is the explicit cutoff proved for a true witness with smaller column at most A. -/
def H2 : Prop := ∀ K : ℕ, ∃ A : ℕ, ∀ t : ℕ,
    (∃ a b m : ℕ, K < a ∧ a < b ∧ a+2*b < m ∧
      (b.descFactorial (b-a)+(m-b+1).ascFactorial (b-a) ∣ b.descFactorial (b-a)*
        ∏ i ∈ Finset.range a, (b.descFactorial (b-a)+(i+1).ascFactorial (b-a))) ∧
      (m.choose a + m.choose b).gcd t.factorial ∣ m.choose (a+b)) →
    ∃ a b m : ℕ, K < a ∧ a ≤ A ∧ a < b ∧ a+b ≤ m ∧
      m < max (2*A+(4*A)^(2*A)) (2^(2*A+1)*(2*A+1).factorial) ∧
      (m.choose a + m.choose b).gcd t.factorial ∣ m.choose (a+b)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a140601.main := by
  intro h₁ h₂
  apply Set.infinite_iff_exists_gt.mpr
  intro K
  obtain ⟨A,hA⟩ := h₂ K
  let C := max (2*A+(4*A)^(2*A)) (2^(2*A+1)*(2*A+1).factorial)
  let t := 2*2^C
  obtain ⟨a,b,m,hKa,_,hab,hm,hC,hw⟩ := hA t (h₁ K t)
  have hpos := Nat.choose_pos (n:=m) (show a ≤ m by omega)
  have hle : m.choose a+m.choose b ≤ t := by
    have h1 := Nat.choose_le_two_pow m a
    have h2 := Nat.choose_le_two_pow m b
    have h3 := Nat.pow_le_pow_right (by decide : 0 < 2) (le_of_lt (show m < C from hC))
    dsimp [t]
    omega
  rw [Nat.gcd_eq_left (Nat.dvd_factorial (by omega) hle)] at hw
  exact ⟨m,⟨a,b,hab.ne,hm,hw⟩,by omega⟩

theorem stabilization_necessary (h : type_of% @OMA.S_oeis_a140601.main) : H2 := by
  intro K
  obtain ⟨a,b,m,hKa,hab,hm,hw⟩ := large_small_column h K
  exact ⟨a,fun t _ => ⟨a,b,m,hKa,le_rfl,hab,hm,small_index_bound hab le_rfl hm hw,
    (Nat.gcd_dvd_left _ _).trans hw⟩⟩

end OMA.R_oeis_a140601_R1

namespace OMA.R_oeis_a140601_R1
open Pascal140

theorem finite_tests_solvable : H1 := local_points

theorem infinitude_iff_stabilization : (type_of% @OMA.S_oeis_a140601.main) ↔ H2 :=
  ⟨stabilization_necessary, main finite_tests_solvable⟩

/-- For each smaller index the two inner quantifiers range over explicit finite
types and test a falling-factorial divisibility condition. -/
theorem infinitude_iff_finite_search : (type_of% @OMA.S_oeis_a140601.main) ↔
    ∀ K : ℕ, ∃ a > K, ∃ m : Fin (max (2*a+(4*a)^(2*a)) (2^(2*a+1)*(2*a+1).factorial)),
      ∃ b : Fin (m.val+1), a < b.val ∧ a+b.val ≤ m.val ∧
      (b.val.descFactorial (b.val-a) + (m.val-b.val+1).ascFactorial (b.val-a)) *
        (a+b.val).descFactorial a ∣
        (m.val-b.val+1).ascFactorial (b.val-a) * (m.val-b.val).descFactorial a := by
  constructor
  · intro h K
    obtain ⟨a,b,m,ha,hab,hm,hw⟩ := large_small_column h K
    exact ⟨a,ha,⟨m,small_index_bound hab le_rfl hm hw⟩,⟨b,by change b < m+1; omega⟩,hab,hm,
      (witness_iff hab hm).mp hw⟩
  · intro h
    apply Set.infinite_iff_exists_gt.mpr
    intro K
    obtain ⟨a,ha,m,b,hab,hm,hw⟩ := h K
    exact ⟨m.val,⟨a,b.val,hab.ne,hm,(witness_iff hab hm).mpr hw⟩,by omega⟩

end OMA.R_oeis_a140601_R1

namespace Pascal140

private lemma pow_le_scaled_falling (s k : ℕ) (hk : 2*k ≤ s+1) :
    (s+1)^k ≤ 3^k * s.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Nat.mul_le_mul (ih (by omega)) (show s+1 ≤ 3*(s-k) by omega)
    simp only [pow_succ, Nat.descFactorial_succ]
    nlinarith only [h]

/-- An explicit elementary exponential-versus-polynomial cutoff, valid even at degree zero. -/
theorem exponential_cutoff (e K s : ℕ) (h : 2^s < (K*(s+1))^e) :
    s ≤ 2*(e+1)+3^(e+1)*(e+1).factorial*K^e := by
  by_cases hs : 2*(e+1) ≤ s+1
  · have h0 := pow_le_scaled_falling s (e+1) hs
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h0
    have h1 := Nat.mul_le_mul_left (3^(e+1)*(e+1).factorial) (Nat.choose_le_two_pow s (e+1))
    have hp : 0 < 3^(e+1)*(e+1).factorial := Nat.mul_pos (by positivity) (Nat.factorial_pos _)
    have h2 := Nat.mul_lt_mul_of_pos_left h hp
    rw [mul_pow] at h2
    have h3 : (s+1)*(s+1)^e <
        (3^(e+1)*(e+1).factorial*K^e)*(s+1)^e := by
      rw [pow_succ] at h0
      nlinarith only [h0,h1,h2]
    have := Nat.lt_of_mul_lt_mul_right h3
    omega
  · omega

end Pascal140

namespace Pascal140

/-- Compare two rising products factor by factor. The scaled error is additive in
the number of factors, even when the base of the two products is large. -/
lemma rising_product_defect (a b e k : ℕ) (hab : a ≤ b) (hk : k≤e) :
    let P := (a+b+1).ascFactorial k
    let Q := (b+1).ascFactorial k
    P ≤ 2^k*Q ∧ b*(2^k*Q) ≤ b*P + k*2^k*(b-a+e)*Q := by
  let P (t : ℕ) := (a+b+1).ascFactorial t
  let Q (t : ℕ) := (b+1).ascFactorial t
  let C := b-a+e
  change P k ≤ 2^k*Q k ∧ b*(2^k*Q k) ≤ b*P k+k*2^k*C*Q k
  induction k with
  | zero => simp [P,Q]
  | succ k ih =>
    obtain ⟨hu,hdef⟩ := ih (by omega)
    let q := b+1+k
    let p := a+b+1+k
    let g := b-a+1+k
    have stepQ : Q (k+1)=q*Q k := Nat.ascFactorial_succ
    have stepP : P (k+1)=p*P k := Nat.ascFactorial_succ
    have pg : 2*q=p+g := by dsimp [p,q,g]; omega
    have hgap : g≤C := by dsimp [g,C]; omega
    have hq : b≤q := by dsimp [q]; omega
    rw [stepQ,stepP,pow_succ]
    constructor
    · calc
        p * P k ≤ (2*q) * (2^k*Q k) := Nat.mul_le_mul (by omega) hu
        _ = _ := by ring
    · have scaled := Nat.mul_le_mul_left (2*q) hdef
      have err := Nat.mul_le_mul (Nat.mul_le_mul hq hu) hgap
      calc
        _ = 2*q*(b*(2^k*Q k)) := by ring
        _ ≤ 2*q*(b*P k+k*2^k*C*Q k) := scaled
        _ = b*(p*P k) + b*P k*g + 2*q*(k*2^k*C*Q k) := by nlinarith only [congrArg (·*(b*P k)) pg]
        _ ≤ b*(p*P k) + (q*(2^k*Q k))*C + 2*q*(k*2^k*C*Q k) := by omega
        _ ≤ _ := by nlinarith only [Nat.zero_le (q*2^k*C*Q k)]

/-- In the large column-gap regime any possible row stays in a linear strip,
with a constant depending only on the complementary-column excess. -/
theorem large_gap_forces_linear {a b e m : ℕ} (hab : a<b) (hm : m=a+2*b+e)
    (h : m.choose a + m.choose b ∣ m.choose (a+b)) (hs : e+1 ≤ 2*(b-a)/3) :
    b ≤ (2*e*2^e)*(b-a+e) := by
  let A := m.choose a
  let B := m.choose b
  let P := (a+b+1).ascFactorial e
  let Q := (b+1).ascFactorial e
  let W := 2^e
  have posA : 0<A := Nat.choose_pos (by omega)
  have posB : 0<B := Nat.choose_pos (by omega)
  have posQ : 0<Q := Nat.ascFactorial_pos b e
  obtain ⟨u,hu⟩ := h
  have posu : 0<u := by
    have hz := Nat.choose_pos (n:=m) (k:=a+b) (by omega)
    rw [hu] at hz
    exact Nat.pos_of_mul_pos_left hz
  have ratio : B*P = (A+B)*u*Q := by
    have hr := choose_ratio_step m b (b+e) (by omega)
    rw [show b+e-b=e by omega,Nat.add_descFactorial_eq_ascFactorial,
      show m-b=(a+b)+e by omega,Nat.add_descFactorial_eq_ascFactorial] at hr
    rw [← Nat.choose_symm (show a+b ≤ m by omega), show m-(a+b)=b+e by omega] at hu
    rw [hu] at hr
    exact hr.symm
  obtain ⟨upper,defect⟩ := rising_product_defect a b e e hab.le le_rfl
  change P ≤ W*Q at upper
  change b*(W*Q) ≤ b*P + e*W*(b-a+e)*Q at defect
  have uW : u<W := by
    have hpos := Nat.mul_pos (Nat.mul_pos posA posu) posQ
    by_contra! hbad
    have hb := Nat.mul_le_mul_left B (Nat.mul_le_mul_right Q hbad)
    have hmax := Nat.mul_le_mul_left B upper
    nlinarith only [hpos,hb,hmax,ratio]
  have small : (2*W)*A ≤ B := by
    have hw : 2*W ≤ 2^(2*(b-a)/3) := by simpa [W,pow_succ,Nat.mul_comm] using (Nat.pow_le_pow_right (by decide : 0<2) hs)
    exact (Nat.mul_le_mul_right A hw).trans (two_pow_gap_le_choose hab hm)
  have half : 2*P+Q ≤ 2*(W*Q) := by
    have sl : 2*A*u ≤ B := by
      have := Nat.mul_le_mul_left (2*A) uW.le
      nlinarith only [this,small]
    have err := Nat.mul_le_mul_right Q sl
    have cut := Nat.mul_le_mul_left (B*Q) (Nat.succ_le_of_lt uW)
    apply Nat.le_of_mul_le_mul_left (c:=B) _ posB
    nlinarith only [ratio,err,cut]
  have hh := Nat.mul_le_mul_left b half
  apply Nat.le_of_mul_le_mul_right (c:=Q) _ posQ
  change b*Q ≤ (2*e*W)*(b-a+e)*Q
  nlinarith only [hh,defect]

end Pascal140

namespace Pascal140

/-- A logarithmic column-gap estimate and a linear near-central row estimate bound every row
with the same positive complementary-column excess. All constants are effective. -/
theorem fixed_excess_bound_from_linear (e : ℕ) (he : 0 < e) (C : ℕ)
    (hlin : ∀ {m a b : ℕ}, a < b → m=a+2*b+e →
      m.choose a + m.choose b ∣ m.choose (a+b) →
      e+1 ≤ 2*(b-a)/3 → b ≤ C*(b-a+e)) :
    ∃ M : ℕ, ∀ {a b m : ℕ}, a < b → m=a+2*b+e →
      m.choose a + m.choose b ∣ m.choose (a+b) → m ≤ M := by
  let K := 2*C*(e+2)+e+1
  let L := 2*(e+1)+3^(e+1)*(e+1).factorial*K^e
  let D := 2*(e+L+2)
  let H := ∑ i ∈ Finset.range (D+1), e.ascFactorial (i+e)
  refine ⟨3*H+e, ?_⟩
  intro a b m hab hm h
  let s := 2*(b-a)/3
  have hd : b-a ≤ 2*(s+1) := by dsimp [s]; omega
  have hs : s ≤ e+L := by
    by_cases hl : e+1 ≤ s
    · have hb := hlin hab hm h hl
      have h1 : b-a+e ≤ (e+2)*(s+1) := by nlinarith only [hd, Nat.zero_le (e*s)]
      have h2 := Nat.mul_le_mul_left C h1
      have h3 : m-b ≤ K*(s+1) := by
        dsimp [K]
        nlinarith only [show m-b ≤ 2*b+e by omega,hb,h2,Nat.zero_le (e*s)]
      have hx := (gap_bound_of_target_excess hab hm h).trans_le (Nat.pow_le_pow_left h3 e)
      have h4 : s ≤ L := exponential_cutoff e K s hx
      omega
    · omega
  have hdD : b-a ≤ D := by dsimp [D]; omega
  have hdvd := general_excess_divisor hab he hm h
  have hpos : 0 < e.ascFactorial (b-a+e) := by
    obtain ⟨f,ef⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    rw [ef]
    exact Nat.ascFactorial_pos _ _
  have hle := Nat.le_of_dvd hpos hdvd
  have hH : e.ascFactorial (b-a+e) ≤ H :=
    Finset.single_le_sum (f:=fun i => e.ascFactorial (i+e)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : b-a < D+1))
  omega

end Pascal140

namespace Pascal140

theorem uniform_excess_from_fixed
    (fixed : ∀ e : ℕ, 0 < e → ∃ M : ℕ, ∀ {a b m : ℕ}, a < b →
      m=a+2*b+e → m.choose a + m.choose b ∣ m.choose (a+b) → m ≤ M)
    (E : ℕ) : ∃ M : ℕ, ∀ {a b m : ℕ}, a < b → a+b ≤ m → m ≤ a+2*b+E →
      m.choose a + m.choose b ∣ m.choose (a+b) → m ≤ M := by
  induction E with
  | zero =>
    refine ⟨0, fun hab hm he hw => ?_⟩
    have hlt := row_lower_bound hm hw
    omega
  | succ E ih =>
    obtain ⟨N,hN⟩ := ih
    obtain ⟨M,hM⟩ := fixed (E+1) (by omega)
    refine ⟨max N M, ?_⟩
    intro a b m hab hm he hw
    by_cases hle : m ≤ a+2*b+E
    · exact (hN hab hm hle hw).trans (le_max_left _ _)
    · exact (hM hab (by omega) hw).trans (le_max_right _ _)

end Pascal140

namespace Pascal140

theorem two_parameters_escape
    (fixed : ∀ e : ℕ, 0 < e → ∃ M : ℕ, ∀ {a b m : ℕ}, a < b →
      m=a+2*b+e → m.choose a + m.choose b ∣ m.choose (a+b) → m ≤ M)
    (h : {m : ℕ | OMA.S_oeis_a140601.IsTerm m}.Infinite) (K E : ℕ) :
    ∃ a b m : ℕ, K < a ∧ a < b ∧ a+2*b+E < m ∧
      m.choose a + m.choose b ∣ m.choose (a+b) := by
  obtain ⟨M,hM⟩ := uniform_excess_from_fixed fixed E
  obtain ⟨a,b,m,ha,hab,hm,hw⟩ := large_small_column h (max K M)
  refine ⟨a,b,m,by omega,hab,?_,hw⟩
  by_contra! hc
  have := hM hab hm hc hw
  omega

end Pascal140

namespace Pascal140

/-- Every fixed positive complementary-column excess permits only finitely many rows. -/
theorem fixed_excess_finite (e : ℕ) (he : 0 < e) :
    ∃ M : ℕ, ∀ {a b m : ℕ}, a < b → m=a+2*b+e →
      m.choose a + m.choose b ∣ m.choose (a+b) → m ≤ M := by
  apply fixed_excess_bound_from_linear e he (2*e*2^e)
  intro m a b hab hm hw hs
  exact large_gap_forces_linear hab hm hw hs

/-- If the sequence is infinite, its witnesses escape simultaneously in the smaller
column and the excess over the reflected-column cutoff. -/
theorem column_and_excess_unbounded (h : {m : ℕ | OMA.S_oeis_a140601.IsTerm m}.Infinite) (K E : ℕ) :
    ∃ a b m : ℕ, K < a ∧ a < b ∧ a+2*b+E < m ∧
      m.choose a + m.choose b ∣ m.choose (a+b) :=
  two_parameters_escape fixed_excess_finite h K E

end Pascal140
