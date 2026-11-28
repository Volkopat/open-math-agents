import OMAStatements.S_oeis_a333562
import Mathlib

/-! Proof of A333562: a(n) = sum C(4n,i) C(n+j-1,j) over i+j=3n, symmetrize, unit terms vanish mod p^(3s), p-divisible terms compared via the Jacobsthal ratio R. -/

/-! Jacobsthal-Kazandzidis type congruence C(a p^r, b p^r) = C(a p^(r-1), b p^(r-1)) mod p^(3r), p >= 5. Base lemmas adapted from proofs/oeis-a375180.R1.H4.lean. -/

namespace LtsJacobsthal
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `D p e x` : the rational `x` lies in `p^e * ℤ_(p)`. -/
def D (p e : ℕ) (x : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, ¬ p ∣ b ∧ x * (b : ℚ) = (p : ℚ) ^ e * (a : ℚ)

lemma D.zero (e : ℕ) : D p e 0 := ⟨0, 1, hp.out.not_dvd_one, by simp⟩

omit hp in
lemma D.neg {e : ℕ} {x : ℚ} (hx : D p e x) : D p e (-x) := by
  obtain ⟨a, b, hb, h⟩ := hx
  exact ⟨-a, b, hb, by push_cast; linear_combination -h⟩

lemma D.add {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x + y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * b' + a' * b, b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    linear_combination (b' : ℚ) * h + (b : ℚ) * h'

lemma D.sub {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

lemma D.mul {e f : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p f y) : D p (e + f) (x * y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * a', b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    rw [pow_add]
    linear_combination (y * (b' : ℚ)) * h + ((p : ℚ) ^ e * (a : ℚ)) * h'

omit hp in
lemma D.le {e f : ℕ} {x : ℚ} (hx : D p e x) (hfe : f ≤ e) : D p f x := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hfe
  exact ⟨(p : ℤ) ^ c * a, b, hb, by push_cast; rw [h, pow_add]; ring⟩

lemma D.int (z : ℤ) : D p 0 (z : ℚ) := ⟨z, 1, hp.out.not_dvd_one, by simp⟩

lemma D.nat (n : ℕ) : D p 0 (n : ℚ) := ⟨(n : ℤ), 1, hp.out.not_dvd_one, by simp⟩

lemma D.one : D p 0 (1 : ℚ) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

lemma D.ppow (e : ℕ) : D p e ((p : ℚ) ^ e) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

lemma D.mul0 {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p 0 y) : D p e (x * y) :=
  (hx.mul hy).le (by omega)

lemma D.mul0' {e : ℕ} {x y : ℚ} (hy : D p 0 y) (hx : D p e x) : D p e (y * x) :=
  (hy.mul hx).le (by omega)

omit hp in
lemma D.inv {u : ℕ} (hu : ¬ p ∣ u) : D p 0 ((u : ℚ)⁻¹) := by
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h
    apply hu
    have h0 : u = 0 := by exact_mod_cast h
    rw [h0]; exact dvd_zero p
  exact ⟨1, u, hu, by rw [inv_mul_cancel₀ hu0]; simp⟩

lemma D.sum {ι : Type*} {e : ℕ} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p e (f i)) :
    D p e (∑ i ∈ s, f i) :=
  Finset.sum_induction f (D p e) (fun _ _ ha hb => ha.add hb) (D.zero e) h

lemma D.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p 0 (f i)) :
    D p 0 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (D p 0) (fun _ _ ha hb => (ha.mul hb).le (by omega)) D.one h

lemma D.pow {e : ℕ} {x : ℚ} (hx : D p e x) (n : ℕ) : D p (e * n) (x ^ n) := by
  induction n with
  | zero => simpa using (D.one (p := p))
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hx

lemma D.cancel {e c : ℕ} {x : ℚ} (h : D p (e + c) ((p : ℚ) ^ c * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, b, hb, ?_⟩
  have hpc : ((p : ℚ) ^ c) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  apply mul_left_cancel₀ hpc
  rw [pow_add] at h
  linear_combination h

lemma D.ucancel {e u : ℕ} {x : ℚ} (hu : ¬ p ∣ u) (h : D p e ((u : ℚ) * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, u * b, ?_, by push_cast; linear_combination h⟩
  intro hd
  rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
  · exact hu h1
  · exact hb h1

lemma D.dvd {e : ℕ} {z : ℤ} (h : D p e (z : ℚ)) : (p : ℤ) ^ e ∣ z := by
  obtain ⟨a, b, hb, h⟩ := h
  have h2 : z * (b : ℤ) = (p : ℤ) ^ e * a := by exact_mod_cast h
  have hc : IsCoprime ((p : ℤ) ^ e) (b : ℤ) := by
    have h3 : Nat.Coprime (p ^ e) b :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hb)
    have h4 := Nat.isCoprime_iff_coprime.mpr h3
    simpa using h4
  exact hc.dvd_of_dvd_mul_right ⟨a, h2⟩

/-! ### index sets -/

/-- the integers `0 < i < L` prime to `p` -/
def U (p L : ℕ) : Finset ℕ := (Finset.range L).filter (fun i => ¬ p ∣ i)

lemma mem_U {p L i : ℕ} : i ∈ U p L ↔ i < L ∧ ¬ p ∣ i := by
  simp [U]

omit hp in
lemma sum_U_blocks {q : ℕ} (hpq : p ∣ q) (f : ℕ → ℚ) (t : ℕ) :
    ∑ i ∈ U p (t * q), f i = ∑ h ∈ Finset.range t, ∑ u ∈ U p q, f (h * q + u) := by
  induction t with
  | zero => simp [U]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold U
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, add_one_mul,
      Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : p ∣ t * q + x ↔ p ∣ x := Nat.dvd_add_right (dvd_mul_of_dvd_right hpq t)
    simp only [h1]

lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (m n : ℕ) (hm : 0 < m)
    (f : ℕ → M) :
    ∑ k ∈ Finset.range (m * n), f k =
      ∑ k ∈ (Finset.range (m * n)).filter (fun k => ¬ m ∣ k), f k +
        ∑ c ∈ Finset.range n, f (m * c) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m * n)) (fun k => m ∣ k), add_comm]
  congr 1
  have h1 : (Finset.range (m * n)).filter (fun k => m ∣ k) =
      (Finset.range n).image (fun c => m * c) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, lt_of_mul_lt_mul_left hk (Nat.zero_le m), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right m c⟩
  rw [h1, Finset.sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hm h

lemma prod_range_mul_split {M : Type*} [CommMonoid M] (m n : ℕ) (hm : 0 < m)
    (f : ℕ → M) :
    ∏ k ∈ Finset.range (m * n), f k =
      (∏ k ∈ (Finset.range (m * n)).filter (fun k => ¬ m ∣ k), f k) *
        ∏ c ∈ Finset.range n, f (m * c) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range (m * n)) (fun k => m ∣ k), mul_comm]
  congr 1
  have h1 : (Finset.range (m * n)).filter (fun k => m ∣ k) =
      (Finset.range n).image (fun c => m * c) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, lt_of_mul_lt_mul_left hk (Nat.zero_le m), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right m c⟩
  rw [h1, Finset.prod_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hm h

/-! ### binomials as products -/

/-- `Gp n m = ∏_{0 < i < m} (1 - n / i)` (the factor `i = 0` is `1`). -/
def Gp (n : ℚ) (m : ℕ) : ℚ := ∏ i ∈ Finset.range m, (1 - n / (i : ℚ))

omit hp in
lemma choose_mul_eq (n k : ℕ) :
    (n.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = (n : ℚ) * (-1) ^ k * Gp n (k + 1) := by
  induction k with
  | zero => simp [Gp]
  | succ k ih =>
    have h1 : (n.choose (k + 1 + 1) : ℚ) * ((k : ℚ) + 1 + 1) =
        (n.choose (k + 1) : ℚ) * ((n : ℚ) - ((k : ℚ) + 1)) := by
      rcases le_or_gt (k + 1) n with h | h
      · have h2 := congrArg (Nat.cast (R := ℚ)) (Nat.choose_succ_right_eq n (k + 1))
        push_cast [Nat.cast_sub h] at h2
        linarith
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < k + 1 + 1), Nat.choose_eq_zero_of_lt h]
        simp
    have hG : Gp n (k + 1 + 1) = Gp n (k + 1) * (1 - (n : ℚ) / ((k : ℚ) + 1)) := by
      unfold Gp
      rw [Finset.prod_range_succ]
      push_cast
      ring
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h3 : (n : ℚ) * (-1) ^ (k + 1) * (Gp n (k + 1) * (1 - (n : ℚ) / ((k : ℚ) + 1))) =
        ((n : ℚ) * (-1) ^ k * Gp n (k + 1)) * (((n : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) := by
      field_simp
      ring
    have h4 : ((n.choose (k + 1) : ℚ) * ((k : ℚ) + 1)) * (((n : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) =
        (n.choose (k + 1) : ℚ) * ((n : ℚ) - ((k : ℚ) + 1)) := by
      field_simp
    push_cast
    rw [hG, h3, ← ih, h4, ← h1]

omit hp in
lemma choose_mul_eq' (n k : ℕ) (hk : 1 ≤ k) :
    (n.choose k : ℚ) * (k : ℚ) = -((n : ℚ) * (-1) ^ k * Gp n k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := choose_mul_eq n k'
  push_cast
  rw [h, pow_succ]
  ring

/-- `R p x L = ∏_{0 < i < L, p ∤ i} (1 - x / i)` -/
def R (p : ℕ) (x : ℚ) (L : ℕ) : ℚ := ∏ i ∈ U p L, (1 - x / (i : ℚ))

omit hp in
lemma Gp_split (hp0 : 0 < p) (x : ℚ) (j : ℕ) :
    Gp x (p * j) = R p x (p * j) * Gp (x / p) j := by
  unfold Gp R U
  rw [prod_range_mul_split p j hp0]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  push_cast
  rw [div_div]

lemma choose_ratio (hp2 : p ≠ 2) (n j : ℕ) :
    ((p * n).choose (p * j) : ℚ) = (n.choose j : ℚ) * R p ((p * n : ℕ) : ℚ) (p * j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [R, U]
  have hp0 : 0 < p := hp.out.pos
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h1 := choose_mul_eq' (p * n) (p * j) (by nlinarith)
  have h2 := choose_mul_eq' n j hj
  have h3 := Gp_split hp0 ((p * n : ℕ) : ℚ) j
  have h4 : ((p * n : ℕ) : ℚ) / (p : ℚ) = (n : ℚ) := by
    push_cast
    field_simp
  have h5 : (-1 : ℚ) ^ (p * j) = (-1) ^ j := by
    rw [pow_mul, hodd.neg_one_pow]
  rw [h3, h4, h5] at h1
  have hpj : ((p * j : ℕ) : ℚ) ≠ 0 := by
    have : 0 < p * j := Nat.mul_pos hp0 hj
    positivity
  have hj0 : (j : ℚ) ≠ 0 := by positivity
  have hpq : (p : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hpj
  rw [h1]
  push_cast
  have h6 : (n : ℚ) * (-1) ^ j * Gp n j = -((n.choose j : ℚ) * (j : ℚ)) := by rw [h2]; ring
  linear_combination (-(p : ℚ) * R p ((p : ℚ) * (n : ℚ)) (p * j)) * h6

/-! ### expansions of `1/(u+a)^j` -/

lemma D.pow0 {x : ℚ} (hx : D p 0 x) (n : ℕ) : D p 0 (x ^ n) :=
  (hx.pow n).le (Nat.zero_le _)

lemma D.two : D p 0 (2 : ℚ) := by simpa using D.nat (p := p) 2

lemma D.three : D p 0 (3 : ℚ) := by simpa using D.nat (p := p) 3

lemma exp1_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (4 * s) (v⁻¹ - (u⁻¹ - a * u⁻¹ ^ 2 + a ^ 2 * u⁻¹ ^ 3 - a ^ 3 * u⁻¹ ^ 4)) := by
  have h1 : v⁻¹ - (u⁻¹ - a * u⁻¹ ^ 2 + a ^ 2 * u⁻¹ ^ 3 - a ^ 3 * u⁻¹ ^ 4) =
      a ^ 4 * u⁻¹ ^ 4 * v⁻¹ := by
    subst h
    field_simp
    ring
  rw [h1]
  exact (((ha.pow 4).mul0 (hu.pow0 4)).mul0 hv).le (by omega)

lemma exp2_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hu' : D p 0 u) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (2 * s) (v⁻¹ ^ 2 - (u⁻¹ ^ 2 - 2 * a * u⁻¹ ^ 3)) := by
  have h1 : v⁻¹ ^ 2 - (u⁻¹ ^ 2 - 2 * a * u⁻¹ ^ 3) =
      a ^ 2 * ((3 * u + 2 * a) * u⁻¹ ^ 3 * v⁻¹ ^ 2) := by
    subst h
    field_simp
    ring
  rw [h1]
  have ha0 : D p 0 a := ha.le (Nat.zero_le _)
  have h2 : D p 0 (3 * u + 2 * a) := (D.three.mul0 hu').add (D.two.mul0 ha0)
  exact ((ha.pow 2).mul0 ((h2.mul0 (hu.pow0 3)).mul0 (hv.pow0 2))).le (by omega)

lemma exp3_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hu' : D p 0 u) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (2 * s) (v⁻¹ ^ 3 - (u⁻¹ ^ 3 - 3 * a * u⁻¹ ^ 4)) := by
  have h1 : v⁻¹ ^ 3 - (u⁻¹ ^ 3 - 3 * a * u⁻¹ ^ 4) =
      a ^ 2 * ((2 * (3 * u ^ 2) + 2 * (2 * (2 * (u * a))) + 3 * a ^ 2) * u⁻¹ ^ 4 * v⁻¹ ^ 3) := by
    subst h
    field_simp
    ring
  rw [h1]
  have ha0 : D p 0 a := ha.le (Nat.zero_le _)
  have h2 : D p 0 (2 * (3 * u ^ 2) + 2 * (2 * (2 * (u * a))) + 3 * a ^ 2) :=
    ((D.two.mul0 (D.three.mul0 (hu'.pow0 2))).add
      (D.two.mul0 (D.two.mul0 (D.two.mul0 (hu'.mul0 ha0))))).add (D.three.mul0 (ha0.pow0 2))
  exact ((ha.pow 2).mul0 ((h2.mul0 (hu.pow0 4)).mul0 (hv.pow0 3))).le (by omega)

/-! ### products -/

lemma prod_congr_D {ι : Type*} [DecidableEq ι] {e : ℕ} (s : Finset ι) (f g : ι → ℚ)
    (hf : ∀ i ∈ s, D p 0 (f i)) (hg : ∀ i ∈ s, D p 0 (g i)) (h : ∀ i ∈ s, D p e (f i - g i)) :
    D p e (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using D.zero (p := p) e
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        (f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    rw [h1]
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    exact ((h a (Finset.mem_insert_self a s)).mul0 (D.prod s f fun i hi => hf i (hs i hi))).add
      ((hg a (Finset.mem_insert_self a s)).mul0'
        (ih (fun i hi => hf i (hs i hi)) (fun i hi => hg i (hs i hi)) (fun i hi => h i (hs i hi))))

lemma prod_expand2 {ι : Type*} [DecidableEq ι] (hp2 : ¬ p ∣ 2) (s : Finset ι)
    (a : ι → ℚ) (x : ℚ) (hx : D p 0 x) (ha : ∀ i ∈ s, D p 0 (a i)) :
    ∃ W : ℚ, D p 0 W ∧ ∏ i ∈ s, (1 - x * a i) =
      1 - x * (∑ i ∈ s, a i) + x ^ 2 * (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) +
        x ^ 3 * W := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, D.zero 0, by simp⟩
  | insert b s hb ih =>
    obtain ⟨W, hW, hprod⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have hab := ha b (Finset.mem_insert_self b s)
    have hS1 : D p 0 (∑ i ∈ s, a i) :=
      D.sum s a fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hS2 : D p 0 (∑ i ∈ s, a i ^ 2) :=
      D.sum s _ fun i hi => (ha i (Finset.mem_insert_of_mem hi)).pow0 2
    have h2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
    have hE : D p 0 (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) := by
      rw [div_eq_mul_inv]
      exact ((hS1.pow0 2).sub hS2).mul0 h2
    refine ⟨W - a b * (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) - x * a b * W, ?_, ?_⟩
    · exact (hW.sub (hab.mul0 hE)).sub ((hx.mul0 hab).mul0 hW)
    · rw [Finset.prod_insert hb, Finset.sum_insert hb, Finset.sum_insert hb, hprod]
      ring

/-! ### symmetries of `U p q` -/

omit hp in
lemma sum_U_reflect {q : ℕ} (hpq : p ∣ q) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f u = ∑ u ∈ U p q, f (q - u) := by
  symm
  have hmem : ∀ u ∈ U p q, q - u ∈ U p q := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero p)
    refine mem_U.mpr ⟨by omega, ?_⟩
    intro hd
    have h1 : q - u + u = q := Nat.sub_add_cancel (le_of_lt hlt)
    have h2 : p ∣ q - u + u := by rw [h1]; exact hpq
    exact hnd ((Nat.dvd_add_right hd).mp h2)
  have hinv : ∀ u ∈ U p q, q - (q - u) = u := by
    intro u hu
    obtain ⟨hlt, _⟩ := mem_U.mp hu
    omega
  exact Finset.sum_nbij' (fun u => q - u) (fun u => q - u) hmem hmem hinv hinv
    (fun u _ => rfl)

omit hp in
lemma sum_U_double {q : ℕ} (hp' : p.Prime) (hp2 : ¬ p ∣ 2) (hpq : p ∣ q)
    (hq : Nat.Coprime q 2) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f (2 * u % q) = ∑ u ∈ U p q, f u := by
  have hinj : Set.InjOn (fun u => 2 * u % q) (U p q : Set ℕ) := by
    intro u hu v hv h
    have hu' := mem_U.mp (Finset.mem_coe.mp hu)
    have hv' := mem_U.mp (Finset.mem_coe.mp hv)
    have h1 : 2 * u ≡ 2 * v [MOD q] := h
    have h2 : u ≡ v [MOD q] := Nat.ModEq.cancel_left_of_coprime hq h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hu'.1 hv'.1
  have himg : (U p q).image (fun u => 2 * u % q) = U p q := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have hu' := mem_U.mp hu
      have hq0 : 0 < q := by omega
      refine mem_U.mpr ⟨Nat.mod_lt _ hq0, ?_⟩
      intro hd
      have h3 : p ∣ 2 * u := (Nat.dvd_mod_iff hpq).mp hd
      rcases (Nat.Prime.dvd_mul hp').mp h3 with h4 | h4
      · exact hp2 h4
      · exact hu'.2 h4
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ u ∈ U p q, f (2 * u % q)
      = ∑ w ∈ (U p q).image (fun u => 2 * u % q), f w := by
        rw [Finset.sum_image hinj]
    _ = ∑ u ∈ U p q, f u := by rw [himg]

lemma D_inv_pow_congr {s x y : ℕ} (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : D p s ((x : ℚ) - (y : ℚ))) (j : ℕ) :
    D p s (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) := by
  have hx0 : (x : ℚ) ≠ 0 := by
    intro h0
    apply hx
    have h1 : x = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hy0 : (y : ℚ) ≠ 0 := by
    intro h0
    apply hy
    have h1 : y = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hxx : (x : ℚ) * (x : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hyy : (y : ℚ) * (y : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hy0
  have h1 : D p s ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) := by
    have h2 : (x : ℚ)⁻¹ - (y : ℚ)⁻¹ = -(((x : ℚ) - (y : ℚ)) * ((x : ℚ)⁻¹ * (y : ℚ)⁻¹)) := by
      linear_combination (y : ℚ)⁻¹ * hxx - (x : ℚ)⁻¹ * hyy
    rw [h2]
    exact (h.mul0 (((D.inv hx).mul (D.inv hy)).le (by omega))).neg
  induction j with
  | zero => simpa using D.zero (p := p) s
  | succ j ih =>
    have h3 : ((x : ℚ)⁻¹) ^ (j + 1) - ((y : ℚ)⁻¹) ^ (j + 1) =
        (x : ℚ)⁻¹ * (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) +
          ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) * ((y : ℚ)⁻¹) ^ j := by ring
    rw [h3]
    exact ((D.inv hx).mul0' ih).add (h1.mul0 ((D.inv hy).pow0 j))

/-! ### power sums over the units below `p^s` -/

/-- `sg p q j = ∑_{0<u<q, p ∤ u} u^(-j)` -/
def sg (p q j : ℕ) : ℚ := ∑ u ∈ U p q, ((u : ℚ)⁻¹) ^ j

lemma sg_scale (hp2 : ¬ p ∣ 2) {s : ℕ} (hs : 1 ≤ s) (j : ℕ) :
    D p s (((2 : ℚ) ^ j - 1) * sg p (p ^ s) j) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hq2 : Nat.Coprime (p ^ s) 2 :=
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hp2)
  have h1 : sg p (p ^ s) j = ∑ u ∈ U p (p ^ s), (((2 * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j := by
    unfold sg
    exact (sum_U_double hp.out hp2 hpq hq2 (fun w => ((w : ℚ)⁻¹) ^ j)).symm
  have h2 : D p s (∑ u ∈ U p (p ^ s),
      ((((2 * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j - (((2 * u : ℕ) : ℚ)⁻¹) ^ j)) := by
    apply D.sum
    intro u hu
    have hu' := mem_U.mp hu
    have h2u : ¬ p ∣ 2 * u := by
      intro hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h4 | h4
      · exact hp2 h4
      · exact hu'.2 h4
    have hmod : ¬ p ∣ 2 * u % p ^ s := fun hd => h2u ((Nat.dvd_mod_iff hpq).mp hd)
    apply D_inv_pow_congr hmod h2u
    have h5 : ((2 * u % p ^ s : ℕ) : ℚ) - ((2 * u : ℕ) : ℚ) =
        -((p : ℚ) ^ s * ((2 * u / p ^ s : ℕ) : ℚ)) := by
      have h6 := Nat.div_add_mod (2 * u) (p ^ s)
      have h7 : ((p ^ s * (2 * u / p ^ s) + 2 * u % p ^ s : ℕ) : ℚ) = ((2 * u : ℕ) : ℚ) := by
        rw [h6]
      push_cast at h7 ⊢
      linarith
    rw [h5]
    exact ((D.ppow s).mul0 (D.nat _)).neg
  rw [Finset.sum_sub_distrib, ← h1] at h2
  have h3 : ∑ u ∈ U p (p ^ s), (((2 * u : ℕ) : ℚ)⁻¹) ^ j = ((2 : ℚ)⁻¹) ^ j * sg p (p ^ s) j := by
    unfold sg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    push_cast
    rw [mul_inv, mul_pow]
  rw [h3] at h2
  have h4 : ((2 : ℚ) ^ j - 1) * sg p (p ^ s) j =
      (2 : ℚ) ^ j * (sg p (p ^ s) j - ((2 : ℚ)⁻¹) ^ j * sg p (p ^ s) j) := by
    have h5 : (2 : ℚ) ^ j * ((2 : ℚ)⁻¹) ^ j = 1 := by
      rw [← mul_pow]; norm_num
    linear_combination (sg p (p ^ s) j) * h5
  rw [h4]
  exact (D.two.pow0 j).mul0' h2

/-- generic shifted sums: `v = u + a` with `a ∈ p^s ℤ_(p)` -/
lemma shift_sums {s : ℕ} (a : ℚ) (ha : D p s a) (v : ℕ → ℚ)
    (hv : ∀ u ∈ U p (p ^ s), v u = (u : ℚ) + a ∧ v u ≠ 0 ∧ D p 0 (v u)⁻¹) :
    D p (4 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ -
      (sg p (p ^ s) 1 - a * sg p (p ^ s) 2 + a ^ 2 * sg p (p ^ s) 3 - a ^ 3 * sg p (p ^ s) 4)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 2 -
      (sg p (p ^ s) 2 - 2 * a * sg p (p ^ s) 3)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 3 -
      (sg p (p ^ s) 3 - 3 * a * sg p (p ^ s) 4)) := by
  have hu : ∀ u ∈ U p (p ^ s), (u : ℚ) ≠ 0 ∧ D p 0 ((u : ℚ)⁻¹) := by
    intro u hu
    obtain ⟨_, hnd⟩ := mem_U.mp hu
    refine ⟨?_, D.inv hnd⟩
    intro h0
    apply hnd
    have h1 : u = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ -
        (sg p (p ^ s) 1 - a * sg p (p ^ s) 2 + a ^ 2 * sg p (p ^ s) 3 - a ^ 3 * sg p (p ^ s) 4) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ - ((u : ℚ)⁻¹ - a * (u : ℚ)⁻¹ ^ 2 + a ^ 2 * (u : ℚ)⁻¹ ^ 3 -
          a ^ 3 * (u : ℚ)⁻¹ ^ 4)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, pow_one]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp1_D (hu u hmem).1 h3 h2 (hu u hmem).2 h4 ha
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 2 - (sg p (p ^ s) 2 - 2 * a * sg p (p ^ s) 3) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ ^ 2 - ((u : ℚ)⁻¹ ^ 2 - 2 * a * (u : ℚ)⁻¹ ^ 3)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp2_D (hu u hmem).1 h3 h2 (hu u hmem).2 (D.nat u) h4 ha
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 3 - (sg p (p ^ s) 3 - 3 * a * sg p (p ^ s) 4) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ ^ 3 - ((u : ℚ)⁻¹ ^ 3 - 3 * a * (u : ℚ)⁻¹ ^ 4)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp3_D (hu u hmem).1 h3 h2 (hu u hmem).2 (D.nat u) h4 ha
/-! ### derived power sum facts -/

omit hp in
lemma D.congr {e : ℕ} {x y : ℚ} (h : D p e x) (hxy : x = y) : D p e y := hxy ▸ h

lemma sg_D0 (q j : ℕ) : D p 0 (sg p q j) :=
  D.sum _ _ fun _ hu => (D.inv (mem_U.mp hu).2).pow0 j

/-- `Eps p ε`: `ε = 0` and `p ∤ 15`, or `ε = 1` and `p = 5`. -/
def Eps (p ε : ℕ) : Prop := (ε = 0 ∧ ¬ p ∣ 15) ∨ (ε = 1 ∧ p = 5)

omit hp in
lemma Eps.le_one {ε : ℕ} (h : Eps p ε) : ε ≤ 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

lemma sg2 (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) : D p s (sg p (p ^ s) 2) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hp3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h := sg_scale hp2 hs 2
  exact D.ucancel hp3 (h.congr (by push_cast; ring))

lemma sg4 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p s ((p : ℚ) ^ ε * sg p (p ^ s) 4) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hp3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h := sg_scale hp2 hs 4
  rcases hε with ⟨rfl, h15⟩ | ⟨rfl, h55⟩
  · have h6 : D p s (sg p (p ^ s) 4) := D.ucancel h15 (h.congr (by push_cast; ring))
    exact h6.congr (by ring)
  · have h6 : D p s (((3 : ℕ) : ℚ) * ((p : ℚ) ^ 1 * sg p (p ^ s) 4)) := by
      refine h.congr ?_
      rw [h55]
      push_cast
      ring
    exact D.ucancel hp3 h6

lemma refl_sums {s : ℕ} (hs : 1 ≤ s) :
    D p (4 * s) (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2 +
      ((p : ℚ) ^ s) ^ 2 * sg p (p ^ s) 3 + ((p : ℚ) ^ s) ^ 3 * sg p (p ^ s) 4) ∧
    D p (2 * s) (2 * sg p (p ^ s) 3 + 3 * (p : ℚ) ^ s * sg p (p ^ s) 4) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hv : ∀ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ))) = (u : ℚ) + (-(p : ℚ) ^ s) ∧
      (-(((p ^ s - u : ℕ) : ℚ))) ≠ 0 ∧ D p 0 (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hw : ¬ p ∣ p ^ s - u := by
      intro hd
      have h1 : p ^ s - u + u = p ^ s := Nat.sub_add_cancel (le_of_lt hlt)
      have h2 : p ∣ p ^ s - u + u := by rw [h1]; exact hpq
      exact hnd ((Nat.dvd_add_right hd).mp h2)
    have hw0 : ((p ^ s - u : ℕ) : ℚ) ≠ 0 := by
      have h1 : p ^ s - u ≠ 0 := by omega
      exact_mod_cast h1
    refine ⟨?_, neg_ne_zero.mpr hw0, ?_⟩
    · rw [Nat.cast_sub (le_of_lt hlt)]
      push_cast
      ring
    · rw [inv_neg]
      exact (D.inv hw).neg
  obtain ⟨h1, _, h3⟩ :=
    shift_sums (-(p : ℚ) ^ s) (D.ppow s).neg (fun u => -(((p ^ s - u : ℕ) : ℚ))) hv
  have hr1 : ∑ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ = -sg p (p ^ s) 1 := by
    have h := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ 1)
    simp only [sg]
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [inv_neg, pow_one]
  have hr3 : ∑ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ ^ 3 = -sg p (p ^ s) 3 := by
    have h := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ 3)
    simp only [sg]
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [inv_neg]
    ring
  rw [hr1] at h1
  rw [hr3] at h3
  exact ⟨h1.neg.congr (by ring), h3.neg.congr (by ring)⟩

lemma sg3 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p s (sg p (p ^ s) 3) ∧ D p (2 * s) ((p : ℚ) ^ ε * sg p (p ^ s) 3) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨_, h3⟩ := refl_sums (p := p) hs
  have h4 := sg4 h5 hε hs
  have hσ4 : D p 0 (sg p (p ^ s) 4) := sg_D0 _ _
  constructor
  · have h6 : D p s (((2 : ℕ) : ℚ) * sg p (p ^ s) 3) := by
      have h7 := (h3.le (by omega : s ≤ 2 * s)).sub (D.three.mul0' ((D.ppow s).mul0 hσ4))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6
  · have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * ((p : ℚ) ^ ε * sg p (p ^ s) 3)) := by
      have h7 := (((D.ppow (p := p) ε).le (Nat.zero_le _)).mul0' h3).sub
        (D.three.mul0' (((D.ppow s).mul h4).le (by omega : 2 * s ≤ s + s)))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6

lemma sg1 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p (4 * s) ((p : ℚ) ^ ε * (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2)) := by
  obtain ⟨h1, _⟩ := refl_sums (p := p) hs
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have h7 := ((((D.ppow (p := p) ε).le (Nat.zero_le _)).mul0' h1).sub
    ((((D.ppow s).pow 2).mul h3).le (by omega : 4 * s ≤ s * 2 + 2 * s))).sub
    ((((D.ppow s).pow 3).mul h4).le (by omega : 4 * s ≤ s * 3 + s))
  exact h7.congr (by ring)

lemma trans_sums {s : ℕ} (hs : 1 ≤ s) (h : ℕ) :
    D p (4 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ -
      (sg p (p ^ s) 1 - ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 2 +
        ((h : ℚ) * (p : ℚ) ^ s) ^ 2 * sg p (p ^ s) 3 -
        ((h : ℚ) * (p : ℚ) ^ s) ^ 3 * sg p (p ^ s) 4)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 2 -
      (sg p (p ^ s) 2 - 2 * ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 3)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 -
      (sg p (p ^ s) 3 - 3 * ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 4)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  apply shift_sums ((h : ℚ) * (p : ℚ) ^ s) ((D.nat h).mul0' (D.ppow s))
    (fun u => ((h * p ^ s + u : ℕ) : ℚ))
  intro u hu
  obtain ⟨hlt, hnd⟩ := mem_U.mp hu
  have hw : ¬ p ∣ h * p ^ s + u :=
    fun hd => hnd ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpq h)).mp hd)
  refine ⟨by push_cast; ring, ?_, D.inv hw⟩
  intro h0
  have h1 : h * p ^ s + u = 0 := by exact_mod_cast h0
  apply hw
  rw [h1]
  exact dvd_zero p

/-- `h_1(t q) = -(q t^2 / 2) H_2(q)` to precision `4s - ε` -/
lemma hs1_blocks (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    D p (4 * s) ((p : ℚ) ^ ε *
      (2 * sg p (t * p ^ s) 1 + (p : ℚ) ^ s * (t : ℚ) ^ 2 * sg p (p ^ s) 2)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have h1 := sg1 h5 hε hs
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have hb : sg p (t * p ^ s) 1 =
      ∑ h ∈ Finset.range t, ∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ := by
    unfold sg
    rw [sum_U_blocks hpq]
    simp only [pow_one]
  rw [hb]
  clear hb
  induction t with
  | zero => exact (D.zero _).congr (by simp)
  | succ t ih =>
    obtain ⟨hT, _, _⟩ := trans_sums (p := p) hs t
    have hpe : D p 0 ((p : ℚ) ^ ε) := (D.ppow ε).le (Nat.zero_le _)
    have htq : D p s ((t : ℚ) * (p : ℚ) ^ s) := (D.nat t).mul0' (D.ppow s)
    have h7 := ih.add ((((D.two.mul0' (hpe.mul0' hT)).add h1).add
      (D.two.mul0' (((htq.pow 2).mul h3).le (by omega : 4 * s ≤ s * 2 + 2 * s)))).sub
      (D.two.mul0' (((htq.pow 3).mul h4).le (by omega : 4 * s ≤ s * 3 + s))))
    refine h7.congr ?_
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-- `h_2(t q) = t H_2(q)` to precision `2s` -/
lemma hs2_blocks (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    D p (2 * s) (sg p (t * p ^ s) 2 - (t : ℚ) * sg p (p ^ s) 2) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hε : Eps p (if p = 5 then 1 else 0) := by
    by_cases h : p = 5
    · right; simp [h]
    · left
      refine ⟨by simp [h], ?_⟩
      intro hd
      have h15 : (15 : ℕ) = 3 * 5 := by norm_num
      rw [h15] at hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
      · have := Nat.le_of_dvd (by norm_num) h1; omega
      · have := Nat.le_of_dvd (by norm_num) h1; omega
  obtain ⟨h3, _⟩ := sg3 h5 hε hs
  have hb : sg p (t * p ^ s) 2 =
      ∑ h ∈ Finset.range t, ∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 2 := by
    unfold sg
    rw [sum_U_blocks hpq]
  rw [hb]
  clear hb
  induction t with
  | zero => exact (D.zero _).congr (by simp)
  | succ t ih =>
    obtain ⟨_, hT, _⟩ := trans_sums (p := p) hs t
    have h7 := ih.add (hT.sub (D.two.mul0' (((D.nat t).mul0' ((D.ppow s).mul h3)).le
      (by omega : 2 * s ≤ s + s))))
    refine h7.congr ?_
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-! ### the non-unit part: auxiliary sums -/

lemma exists_eps (h5 : 5 ≤ p) : ∃ ε, Eps p ε := by
  by_cases h : p = 5
  · exact ⟨1, Or.inr ⟨rfl, h⟩⟩
  · refine ⟨0, Or.inl ⟨rfl, ?_⟩⟩
    intro hd
    have h15 : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h15] at hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
    · have := Nat.le_of_dvd (by norm_num) h1
      omega

lemma sg1' (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) : D p (2 * s) (sg p (p ^ s) 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨ε, hε⟩ := exists_eps (p := p) h5
  have hε1 := hε.le_one
  have h1 := sg1 h5 hε hs
  have h2 : D p (4 * s - ε) (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2) := by
    apply D.cancel (c := ε)
    rw [show 4 * s - ε + ε = 4 * s by omega]
    exact h1
  have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * sg p (p ^ s) 1) := by
    have h7 := (h2.le (by omega : 2 * s ≤ 4 * s - ε)).sub
      (((D.ppow s).mul (sg2 h5 hs)).le (by omega : 2 * s ≤ s + s))
    exact h7.congr (by push_cast; ring)
  exact D.ucancel hp2 h6
/-! ### Wolstenholme type sums below `t p^s` -/

lemma S1_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) : D p (2 * s) (sg p (t * p ^ s) 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨ε, hε⟩ := exists_eps (p := p) h5
  have hε1 := hε.le_one
  have h1 := hs1_blocks h5 hε hs t
  have h2 : D p (4 * s - ε)
      (2 * sg p (t * p ^ s) 1 + (p : ℚ) ^ s * (t : ℚ) ^ 2 * sg p (p ^ s) 2) := by
    apply D.cancel (c := ε)
    rw [show 4 * s - ε + ε = 4 * s by omega]
    exact h1
  have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * sg p (t * p ^ s) 1) := by
    have h7 := (h2.le (by omega : 2 * s ≤ 4 * s - ε)).sub
      ((((D.ppow s).mul0 ((D.nat t).pow0 2)).mul (sg2 h5 hs)).le (by omega : 2 * s ≤ s + s))
    exact h7.congr (by push_cast; ring)
  exact D.ucancel hp2 h6

lemma S2_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) : D p s (sg p (t * p ^ s) 2) := by
  have h := (hs2_blocks h5 hs t).le (by omega : s ≤ 2 * s)
  exact (h.add ((D.nat t).mul0' (sg2 h5 hs))).congr (by ring)

/-- `∏_{0<i<t p^s, p ∤ i} (1 - A p^s / i) ≡ 1 mod p^(3s)` -/
lemma R_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (A t : ℕ) :
    D p (3 * s) (R p ((A : ℚ) * (p : ℚ) ^ s) (t * p ^ s) - 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨W, hW, hprod⟩ := prod_expand2 hp2 (U p (t * p ^ s)) (fun i => (A : ℚ) * ((i : ℚ)⁻¹))
    ((p : ℚ) ^ s) ((D.ppow s).le (Nat.zero_le _))
    (fun i hi => (D.nat A).mul0 (D.inv (mem_U.mp hi).2))
  have hR : R p ((A : ℚ) * (p : ℚ) ^ s) (t * p ^ s) =
      ∏ i ∈ U p (t * p ^ s), (1 - (p : ℚ) ^ s * ((A : ℚ) * ((i : ℚ)⁻¹))) := by
    unfold R
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_eq_mul_inv]; ring
  have h1 : ∑ i ∈ U p (t * p ^ s), (A : ℚ) * ((i : ℚ)⁻¹) = (A : ℚ) * sg p (t * p ^ s) 1 := by
    unfold sg; rw [Finset.mul_sum]; simp only [pow_one]
  have h2 : ∑ i ∈ U p (t * p ^ s), ((A : ℚ) * ((i : ℚ)⁻¹)) ^ 2 =
      (A : ℚ) ^ 2 * sg p (t * p ^ s) 2 := by
    unfold sg; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR, hprod, h1, h2]
  have hS1 := S1_D h5 hs t
  have hS2 := S2_D h5 hs t
  have hi2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have e1 : D p (3 * s) ((p : ℚ) ^ s * ((A : ℚ) * sg p (t * p ^ s) 1)) :=
    ((D.ppow s).mul ((D.nat A).mul0' hS1)).le (by omega)
  have e2 : D p (3 * s) (((p : ℚ) ^ s) ^ 2 *
      (((A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2)) := by
    have hin : D p s (((A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2) :=
      ((((D.nat A).mul0' hS1).pow 2).le (by omega)).sub (((D.nat A).pow0 2).mul0' hS2)
    exact (((D.ppow s).pow 2).mul hin).le (by omega)
  have e3 : D p (3 * s) (((p : ℚ) ^ s) ^ 3 * W) :=
    (((D.ppow s).pow 3).mul0 hW).le (by omega)
  exact ((e1.neg.add (e2.mul0 hi2)).add e3).congr (by ring)

/-! ### the main theorem -/

/-- Jacobsthal-Kazandzidis type: `C(a p^r, b p^r) ≡ C(a p^(r-1), b p^(r-1)) mod p^(3r)`. -/
theorem jacobsthal (h5 : 5 ≤ p) (a b r : ℕ) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ (Nat.choose (a * p ^ r) (b * p ^ r) : ℤ) -
      (Nat.choose (a * p ^ (r - 1)) (b * p ^ (r - 1)) : ℤ) := by
  have hp2 : p ≠ 2 := by omega
  have hc := choose_ratio (p := p) hp2 (a * p ^ (r - 1)) (b * p ^ (r - 1))
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hc ⊢
  have e1 : p * (a * p ^ k) = a * p ^ (k + 1) := by ring
  have e2 : p * (b * p ^ k) = b * p ^ (k + 1) := by ring
  rw [e1, e2] at hc
  have e3 : ((a * p ^ (k + 1) : ℕ) : ℚ) = (a : ℚ) * (p : ℚ) ^ (k + 1) := by push_cast; ring
  rw [e3] at hc
  apply D.dvd
  have hR := R_D h5 (by omega : 1 ≤ k + 1) a b
  refine ((D.nat ((a * p ^ k).choose (b * p ^ k))).mul0' hR).congr ?_
  push_cast
  rw [hc]
  ring

/-- the same with an explicit primality hypothesis -/
theorem jacobsthal' {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (a b r : ℕ) (hr : 1 ≤ r) :
    (q : ℤ) ^ (3 * r) ∣ (Nat.choose (a * q ^ r) (b * q ^ r) : ℤ) -
      (Nat.choose (a * q ^ (r - 1)) (b * q ^ (r - 1)) : ℤ) := by
  have : Fact q.Prime := ⟨hq⟩
  exact jacobsthal h5 a b r hr

end LtsJacobsthal

namespace A333562P
open Finset LtsJacobsthal OMA.S_oeis_a333562

/-- `H d j = C(d+j-1, j)` (coefficients of `(1-X)^(-d)`). -/
def H (d j : ℕ) : ℕ := (d + j - 1).choose j

/-- `G m k = [X^k] (1+X)^m (1-X)^(-(m-k))`. -/
def G (m k : ℕ) : ℕ := ∑ x ∈ antidiagonal k, m.choose x.1 * H (m - k) x.2

private lemma H_zero (d : ℕ) : H d 0 = 1 := by simp [H]

private lemma H_step (d j : ℕ) : H (d + 1) (j + 1) = H d (j + 1) + H (d + 1) j := by
  unfold H
  rw [show d + 1 + (j + 1) - 1 = (d + j) + 1 by omega, show d + (j + 1) - 1 = d + j by omega,
    show d + 1 + j - 1 = d + j by omega, Nat.choose_succ_succ']
  ring

private lemma H_zero_succ (j : ℕ) : H 0 (j + 1) = 0 := by
  unfold H
  rw [show 0 + (j + 1) - 1 = j by omega]
  exact Nat.choose_succ_self j

private lemma G_diag (m : ℕ) : G m m = 1 := by
  cases m with
  | zero => simp [G, H]
  | succ m =>
    unfold G
    rw [Nat.sub_self, Finset.Nat.sum_antidiagonal_succ']
    simp [H_zero_succ, H_zero]

private lemma G_rec (m k : ℕ) (hk : k < m) : G (m + 1) (k + 1) = 2 * G m k + G m (k + 1) := by
  obtain ⟨d, hd⟩ : ∃ d, m - k = d + 1 := ⟨m - k - 1, by omega⟩
  have h1 : m + 1 - (k + 1) = d + 1 := by omega
  have h2 : m - (k + 1) = d := by omega
  unfold G
  rw [h1, h2, hd]
  have hA : ∑ x ∈ antidiagonal (k + 1), (m + 1).choose x.1 * H (d + 1) x.2
      = ∑ x ∈ antidiagonal k, m.choose x.1 * H (d + 1) x.2
        + ∑ x ∈ antidiagonal (k + 1), m.choose x.1 * H (d + 1) x.2 := by
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
    simp only [Nat.choose_succ_succ', add_mul, Finset.sum_add_distrib, Nat.choose_zero_right]
    ring
  have hB : ∑ x ∈ antidiagonal (k + 1), m.choose x.1 * H (d + 1) x.2
      = ∑ x ∈ antidiagonal k, m.choose x.1 * H (d + 1) x.2
        + ∑ x ∈ antidiagonal (k + 1), m.choose x.1 * H d x.2 := by
    rw [Finset.Nat.sum_antidiagonal_succ', Finset.Nat.sum_antidiagonal_succ']
    simp only [H_step, H_zero, mul_add, Finset.sum_add_distrib]
    ring
  rw [hA, hB]
  ring

/-- the defining sum with the upper limit `m` -/
def S (d m : ℕ) : ℕ := ∑ j ∈ range (m + 1), H d j * 2 ^ j

private lemma S_zero_right (d : ℕ) : S d 0 = 1 := by simp [S, H_zero]

private lemma S_zero_left (m : ℕ) : S 0 m = 1 := by
  induction m with
  | zero => simp [S, H_zero]
  | succ m ih =>
    unfold S at *
    rw [Finset.sum_range_succ, ih, H_zero_succ]
    simp

private lemma S_step (d m : ℕ) : S (d + 1) (m + 1) = S d (m + 1) + 2 * S (d + 1) m := by
  unfold S
  rw [Finset.sum_range_succ' (fun j => H (d + 1) j * 2 ^ j),
    Finset.sum_range_succ' (fun j => H d j * 2 ^ j)]
  have h : ∑ j ∈ range (m + 1), H (d + 1) (j + 1) * 2 ^ (j + 1) =
      ∑ j ∈ range (m + 1), H d (j + 1) * 2 ^ (j + 1) +
        2 * ∑ j ∈ range (m + 1), H (d + 1) j * 2 ^ j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H_step, pow_succ]
    ring
  rw [h, H_zero, H_zero]
  ring

private lemma S_eq : ∀ m d : ℕ, S d m = G (d + m) m
  | 0, d => by
    rw [S_zero_right]
    simp [G, H]
  | m + 1, 0 => by
    rw [S_zero_left, Nat.zero_add, G_diag]
  | m + 1, d + 1 => by
    rw [S_step, S_eq (m + 1) d, S_eq m (d + 1), show d + 1 + (m + 1) = (d + 1 + m) + 1 by ring,
      G_rec (d + 1 + m) m (by omega), show d + (m + 1) = d + 1 + m by ring]
    ring

private lemma a_eq (n : ℕ) :
    a n = ((∑ x ∈ antidiagonal (3 * n), (4 * n).choose x.1 * H n x.2 : ℕ) : ℤ) := by
  have h1 : a n = (S n (3 * n) : ℤ) := by
    unfold a S H
    push_cast
    rfl
  rw [h1, S_eq, show n + 3 * n = 4 * n by ring]
  unfold G
  rw [show 4 * n - 3 * n = n by omega]

private lemma H_mul (n j : ℕ) (hn : 1 ≤ n) : H n j * (n + j) = (n + j).choose j * n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  unfold H
  rw [show n' + 1 + j - 1 = n' + j by omega]
  have s1 := Nat.add_one_mul_choose_eq (n' + j) j
  have s2 := Nat.choose_succ_right_eq (n' + j + 1) j
  rw [show n' + j + 1 - j = n' + 1 by omega] at s2
  rw [show n' + 1 + j = n' + j + 1 by ring]
  linarith

private lemma choose_prod (n i j : ℕ) (h : i + j = 3 * n) :
    (4 * n).choose i * (n + j).choose j = (4 * n).choose n * (3 * n).choose i := by
  have c1 := Nat.choose_mul (n := 4 * n) (k := n + j) (s := n) (by omega)
  rw [show 4 * n - n = 3 * n by omega, show n + j - n = j by omega] at c1
  have c2 : (4 * n).choose (n + j) = (4 * n).choose i := Nat.choose_symm_of_eq_add (by omega)
  have c3 : (n + j).choose n = (n + j).choose j := Nat.choose_symm_of_eq_add (by omega)
  have c4 : (3 * n).choose j = (3 * n).choose i := Nat.choose_symm_of_eq_add (by omega)
  rw [c2, c3, c4] at c1
  exact c1

private lemma term (n i j : ℕ) (hn : 1 ≤ n) (h : i + j = 3 * n) :
    (((4 * n).choose i * H n j : ℕ) : ℚ) =
      ((4 * n).choose n : ℚ) * ((3 * n).choose i : ℚ) * (n : ℚ) / ((n : ℚ) + j) := by
  have hn' : (4 * n).choose i * H n j * (n + j) = (4 * n).choose n * (3 * n).choose i * n := by
    rw [mul_assoc, H_mul n j hn, ← mul_assoc, choose_prod n i j h]
  have h1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have h2 : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
  have hpos : ((n : ℚ) + j) ≠ 0 := by
    have : (0 : ℚ) < (n : ℚ) + j := by linarith
    exact this.ne'
  rw [eq_div_iff hpos]
  exact_mod_cast hn'

/-- the symmetrized summand -/
def Bq (n i j : ℕ) : ℚ :=
  5 * ((4 * n).choose n : ℚ) * ((3 * n).choose i : ℚ) * (n : ℚ) ^ 2 / (((n : ℚ) + i) * ((n : ℚ) + j))

private lemma pair (n i j : ℕ) (hn : 1 ≤ n) (h : i + j = 3 * n) :
    (((4 * n).choose i * H n j : ℕ) : ℚ) + (((4 * n).choose j * H n i : ℕ) : ℚ) = Bq n i j := by
  have c : (3 * n).choose j = (3 * n).choose i := Nat.choose_symm_of_eq_add (by omega)
  rw [term n i j hn h, term n j i hn (by omega), c]
  unfold Bq
  have h1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hi : (0 : ℚ) ≤ (i : ℚ) := Nat.cast_nonneg i
  have hj : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
  have hq : (j : ℚ) = 3 * n - i := by
    have : ((i + j : ℕ) : ℚ) = ((3 * n : ℕ) : ℚ) := by rw [h]
    push_cast at this
    linarith
  have d1 : (n : ℚ) + j ≠ 0 := by linarith
  have d2 : (n : ℚ) + i ≠ 0 := by linarith
  rw [hq] at d1 ⊢
  rw [div_add_div _ _ d1 d2, div_eq_div_iff (mul_ne_zero d1 d2) (mul_ne_zero d2 d1)]
  ring

private lemma two_a (n : ℕ) (hn : 1 ≤ n) :
    2 * (a n : ℚ) = ∑ x ∈ antidiagonal (3 * n), Bq n x.1 x.2 := by
  have h1 : (a n : ℚ) = ∑ x ∈ antidiagonal (3 * n), ((((4 * n).choose x.1 * H n x.2 : ℕ)) : ℚ) := by
    rw [a_eq, Int.cast_natCast, Nat.cast_sum]
  have h2 : ∑ x ∈ antidiagonal (3 * n), ((((4 * n).choose x.1 * H n x.2 : ℕ)) : ℚ)
      = ∑ x ∈ antidiagonal (3 * n), ((((4 * n).choose x.2 * H n x.1 : ℕ)) : ℚ) := by
    have := Finset.Nat.sum_antidiagonal_swap (n := 3 * n)
      (f := fun x : ℕ × ℕ => ((((4 * n).choose x.1 * H n x.2 : ℕ)) : ℚ))
    simp only [Prod.fst_swap, Prod.snd_swap] at this
    exact this.symm
  have h3 : 2 * (a n : ℚ) = ∑ x ∈ antidiagonal (3 * n), ((((4 * n).choose x.1 * H n x.2 : ℕ)) : ℚ)
      + ∑ x ∈ antidiagonal (3 * n), ((((4 * n).choose x.2 * H n x.1 : ℕ)) : ℚ) := by
    rw [← h2, ← h1]; ring
  rw [h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  exact pair n x.1 x.2 hn hx'

private lemma Bq_D0 {p : ℕ} [Fact p.Prime] (n i j : ℕ) (hn : 1 ≤ n) (h : i + j = 3 * n) :
    D p 0 (Bq n i j) := by
  rw [← pair n i j hn h]
  exact (D.nat _).add (D.nat _)

private lemma D5 {p : ℕ} [Fact p.Prime] : D p 0 (5 : ℚ) := by simpa using D.nat (p := p) 5

private lemma D3 {p : ℕ} [Fact p.Prime] : D p 0 (3 : ℚ) := by simpa using D.nat (p := p) 3

private lemma split_sum (p M : ℕ) (hp : 0 < p) (F : ℕ × ℕ → ℚ) :
    ∑ x ∈ antidiagonal (p * M), F x =
      ∑ y ∈ antidiagonal M, F (p * y.1, p * y.2) +
      ∑ x ∈ (antidiagonal (p * M)).filter (fun x => ¬ p ∣ x.1), F x := by
  rw [← Finset.sum_filter_add_sum_filter_not (antidiagonal (p * M)) (fun x => p ∣ x.1)]
  congr 1
  symm
  apply Finset.sum_nbij' (fun y => (p * y.1, p * y.2)) (fun x => (x.1 / p, x.2 / p))
  · intro y hy
    simp only [Finset.HasAntidiagonal.mem_antidiagonal, mem_filter] at hy ⊢
    exact ⟨by rw [← hy]; ring, dvd_mul_right _ _⟩
  · intro x hx
    simp only [Finset.HasAntidiagonal.mem_antidiagonal, mem_filter] at hx ⊢
    obtain ⟨hs, ⟨c, hc⟩⟩ := hx
    have hx2 : p ∣ x.2 := by
      have : p ∣ x.1 + x.2 := by rw [hs]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_right ⟨c, hc⟩).mp this
    obtain ⟨d, hd⟩ := hx2
    rw [hc, hd, Nat.mul_div_cancel_left c hp, Nat.mul_div_cancel_left d hp]
    apply Nat.eq_of_mul_eq_mul_left hp
    rw [mul_add, ← hc, ← hd, hs]
  · intro y _
    simp only [Nat.mul_div_cancel_left _ hp]
  · intro x hx
    simp only [Finset.HasAntidiagonal.mem_antidiagonal, mem_filter] at hx
    obtain ⟨hs, h1⟩ := hx
    have h2 : p ∣ x.2 := by
      have : p ∣ x.1 + x.2 := by rw [hs]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_right h1).mp this
    ext
    · exact Nat.mul_div_cancel' h1
    · exact Nat.mul_div_cancel' h2
  · intro y _
    rfl

private lemma bq_D {p : ℕ} [Fact p.Prime] (N i j g i0 j0 m s : ℕ) (hg : 1 ≤ g)
    (hi : i = g * i0) (hj : j = g * j0) (hN : N = g * (m * p ^ s)) (hij : i + j = 3 * N)
    (hi0 : ¬ p ∣ i0) (hu1 : ¬ p ∣ m * p ^ s + i0) (hu2 : ¬ p ∣ m * p ^ s + j0) :
    D p (3 * s) (Bq N i j) := by
  have hi0pos : 1 ≤ i0 := by
    rcases Nat.eq_zero_or_pos i0 with h | h
    · exact absurd (h ▸ dvd_zero p) hi0
    · exact h
  have hipos : 1 ≤ i := by rw [hi]; exact Nat.mul_pos hg hi0pos
  have hNpos : 1 ≤ 3 * N := by omega
  have hC : ((3 * N).choose i : ℚ) * i = ((3 * N : ℕ) : ℚ) * ((3 * N - 1).choose (i - 1) : ℚ) := by
    have h := Nat.add_one_mul_choose_eq (3 * N - 1) (i - 1)
    rw [Nat.sub_add_cancel hNpos, Nat.sub_add_cancel hipos] at h
    exact_mod_cast h.symm
  have hiq : (i : ℚ) ≠ 0 := by
    have : (1 : ℚ) ≤ i := by exact_mod_cast hipos
    linarith
  have hCq : ((3 * N).choose i : ℚ) = ((3 * N : ℕ) : ℚ) * ((3 * N - 1).choose (i - 1) : ℚ) / i := by
    rw [eq_div_iff hiq]; exact hC
  have key : Bq N i j = (p : ℚ) ^ (3 * s) * (5 * ((4 * N).choose N : ℚ) *
      ((3 * N - 1).choose (i - 1) : ℚ) * 3 * (m : ℚ) ^ 3 * ((i0 : ℕ) : ℚ)⁻¹ *
      (((m * p ^ s + i0 : ℕ)) : ℚ)⁻¹ * (((m * p ^ s + j0 : ℕ)) : ℚ)⁻¹) := by
    unfold Bq
    rw [hCq]
    subst hi hj hN
    have hg0 : (g : ℚ) ≠ 0 := by
      have : (1 : ℚ) ≤ g := by exact_mod_cast hg
      linarith
    have hi0' : (i0 : ℚ) ≠ 0 := by
      have : (1 : ℚ) ≤ i0 := by exact_mod_cast hi0pos
      linarith
    have hU1 : (m : ℚ) * (p : ℚ) ^ s + i0 ≠ 0 := by
      have : m * p ^ s + i0 ≠ 0 := fun h => hu1 (h ▸ dvd_zero p)
      exact_mod_cast this
    have hU2 : (m : ℚ) * (p : ℚ) ^ s + j0 ≠ 0 := by
      have : m * p ^ s + j0 ≠ 0 := fun h => hu2 (h ▸ dvd_zero p)
      exact_mod_cast this
    have hD1 : (g : ℚ) * ((m : ℚ) * (p : ℚ) ^ s) + g * i0 ≠ 0 := by
      rw [← mul_add]; exact mul_ne_zero hg0 hU1
    have hD2 : (g : ℚ) * ((m : ℚ) * (p : ℚ) ^ s) + g * j0 ≠ 0 := by
      rw [← mul_add]; exact mul_ne_zero hg0 hU2
    push_cast
    field_simp
    ring
  rw [key]
  have h0 : D p 0 (5 * ((4 * N).choose N : ℚ) *
      ((3 * N - 1).choose (i - 1) : ℚ) * 3 * (m : ℚ) ^ 3 * ((i0 : ℕ) : ℚ)⁻¹ *
      (((m * p ^ s + i0 : ℕ)) : ℚ)⁻¹ * (((m * p ^ s + j0 : ℕ)) : ℚ)⁻¹) :=
    ((((((D5.mul0 (D.nat _)).mul0 (D.nat _)).mul0 D3).mul0 ((D.nat m).pow0 3)).mul0
      (D.inv hi0)).mul0 (D.inv hu1)).mul0 (D.inv hu2)
  exact (D.ppow (3 * s)).mul0 h0

private lemma alg (c1 c2 r1 r2 P M x y : ℚ) (hP : P ≠ 0) (hx : M + x ≠ 0) (hy : M + y ≠ 0) :
    5 * (c1 * r1) * (c2 * r2) * (P * M) ^ 2 / ((P * M + P * x) * (P * M + P * y)) =
      5 * c1 * c2 * M ^ 2 / ((M + x) * (M + y)) * r1 * r2 := by
  have e1 : P * M + P * x = P * (M + x) := by ring
  have e2 : P * M + P * y = P * (M + y) := by ring
  rw [e1, e2]
  field_simp

private lemma div_term {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (e m M l1 l2 : ℕ) (hm : 1 ≤ m)
    (hM : M = m * p ^ e) (hl : l1 + l2 = 3 * M) :
    D p (3 * (e + 1)) (Bq (p * M) (p * l1) (p * l2) - Bq M l1 l2) := by
  have hp2 : p ≠ 2 := by omega
  have hp0 : 0 < p := by omega
  have hMpos : 1 ≤ M := by rw [hM]; exact Nat.mul_pos hm (pow_pos hp0 e)
  have hR1 := choose_ratio (p := p) hp2 (4 * M) M
  have hR2 := choose_ratio (p := p) hp2 (3 * M) l1
  have hB : Bq (p * M) (p * l1) (p * l2) =
      Bq M l1 l2 * R p ((p * (4 * M) : ℕ) : ℚ) (p * M) * R p ((p * (3 * M) : ℕ) : ℚ) (p * l1) := by
    unfold Bq
    rw [show 4 * (p * M) = p * (4 * M) by ring, show 3 * (p * M) = p * (3 * M) by ring, hR1, hR2]
    have hP : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    have h1 : (1 : ℚ) ≤ M := by exact_mod_cast hMpos
    have hx : (M : ℚ) + l1 ≠ 0 := by
      have : (0 : ℚ) ≤ l1 := Nat.cast_nonneg l1
      linarith
    have hy : (M : ℚ) + l2 ≠ 0 := by
      have : (0 : ℚ) ≤ l2 := Nat.cast_nonneg l2
      linarith
    push_cast
    exact alg _ _ _ _ _ _ _ _ hP hx hy
  have hBq0 : D p 0 (Bq M l1 l2) := Bq_D0 M l1 l2 hMpos hl
  have hR1D : D p (3 * (e + 1)) (R p ((p * (4 * M) : ℕ) : ℚ) (p * M) - 1) := by
    have h := R_D h5 (s := e + 1) (by omega) (4 * m) m
    have ex1 : ((p * (4 * M) : ℕ) : ℚ) = ((4 * m : ℕ) : ℚ) * (p : ℚ) ^ (e + 1) := by
      rw [hM]; push_cast; ring
    have ex2 : p * M = m * p ^ (e + 1) := by rw [hM]; ring
    rw [ex1, ex2]; exact h
  have main : ∃ c1 c2 : ℕ, 3 * (e + 1) ≤ c1 + c2 ∧ D p c1 (Bq M l1 l2) ∧
      D p c2 (R p ((p * (3 * M) : ℕ) : ℚ) (p * l1) - 1) := by
    by_cases hdiv : p ^ e ∣ l1
    · obtain ⟨t, ht⟩ := hdiv
      refine ⟨0, 3 * (e + 1), by omega, hBq0, ?_⟩
      have h := R_D h5 (s := e + 1) (by omega) (3 * m) t
      have ex1 : ((p * (3 * M) : ℕ) : ℚ) = ((3 * m : ℕ) : ℚ) * (p : ℚ) ^ (e + 1) := by
        rw [hM]; push_cast; ring
      have ex2 : p * l1 = t * p ^ (e + 1) := by rw [ht]; ring
      rw [ex1, ex2]; exact h
    · have hl1ne : l1 ≠ 0 := by
        intro h0; apply hdiv; rw [h0]; exact dvd_zero _
      obtain ⟨β, u, hu, hl1⟩ := Nat.exists_eq_pow_mul_and_not_dvd hl1ne p (by omega)
      have hβ : β < e := by
        by_contra hc
        apply hdiv
        rw [hl1]
        exact Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) u
      obtain ⟨c, hc⟩ : ∃ c, e = β + c + 1 := ⟨e - β - 1, by omega⟩
      have hM' : M = p ^ β * (m * p ^ (c + 1)) := by rw [hM, hc]; ring
      have hdl2 : p ^ β ∣ l2 := by
        have h1 : p ^ β ∣ l1 + l2 := by
          rw [hl, hM']; exact Dvd.dvd.mul_left (dvd_mul_right _ _) 3
        exact (Nat.dvd_add_right ⟨u, hl1⟩).mp h1
      obtain ⟨u2, hu2⟩ := hdl2
      have hsum : u + u2 = 3 * (m * p ^ (c + 1)) := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hp0 β)
        rw [mul_add, ← hl1, ← hu2, hl, hM']
        ring
      have hpd : p ∣ 3 * (m * p ^ (c + 1)) := ⟨3 * m * p ^ c, by ring⟩
      have hpd' : p ∣ m * p ^ (c + 1) := ⟨m * p ^ c, by ring⟩
      have hu2' : ¬ p ∣ u2 := by
        intro h
        apply hu
        have h1 : p ∣ u + u2 := by rw [hsum]; exact hpd
        exact (Nat.dvd_add_left h).mp h1
      refine ⟨3 * (c + 1), 3 * (β + 1), by omega, ?_, ?_⟩
      · exact bq_D M l1 l2 (p ^ β) u u2 m (c + 1) (Nat.one_le_pow _ _ hp0) hl1 hu2 hM' hl hu
          (fun h => hu ((Nat.dvd_add_right hpd').mp h))
          (fun h => hu2' ((Nat.dvd_add_right hpd').mp h))
      · have h := R_D h5 (s := β + 1) (by omega) (3 * (m * p ^ (c + 1))) u
        have ex1 : ((p * (3 * M) : ℕ) : ℚ) =
            ((3 * (m * p ^ (c + 1)) : ℕ) : ℚ) * (p : ℚ) ^ (β + 1) := by
          rw [hM, hc]; push_cast; ring
        have ex2 : p * l1 = u * p ^ (β + 1) := by rw [hl1]; ring
        rw [ex1, ex2]; exact h
  obtain ⟨c1, c2, hc12, hB1, hR2D⟩ := main
  have hR2_0 : D p 0 (R p ((p * (3 * M) : ℕ) : ℚ) (p * l1)) :=
    ((hR2D.le (Nat.zero_le _)).add D.one).congr (by ring)
  have t1 : D p (3 * (e + 1)) (Bq M l1 l2 * R p ((p * (3 * M) : ℕ) : ℚ) (p * l1) *
      (R p ((p * (4 * M) : ℕ) : ℚ) (p * M) - 1)) := D.mul0' (hBq0.mul0 hR2_0) hR1D
  have t2 : D p (3 * (e + 1)) (Bq M l1 l2 * (R p ((p * (3 * M) : ℕ) : ℚ) (p * l1) - 1)) :=
    (hB1.mul hR2D).le hc12
  rw [hB]
  exact (t1.add t2).congr (by ring)

private lemma one_step {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (e m : ℕ) (hm : 1 ≤ m) :
    (p : ℤ) ^ (3 * (e + 1)) ∣ a (p * (m * p ^ e)) - a (m * p ^ e) := by
  have hp0 : 0 < p := by omega
  have hMpos : 1 ≤ m * p ^ e := Nat.mul_pos hm (pow_pos hp0 e)
  have hNpos : 1 ≤ p * (m * p ^ e) := Nat.mul_pos hp0 hMpos
  have hU : D p (3 * (e + 1)) (∑ x ∈ (antidiagonal (p * (3 * (m * p ^ e)))).filter
      (fun x => ¬ p ∣ x.1), Bq (p * (m * p ^ e)) x.1 x.2) := by
    apply D.sum
    intro x hx
    rw [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    obtain ⟨hs, hx1⟩ := hx
    have hpN : p ∣ m * p ^ (e + 1) := ⟨m * p ^ e, by ring⟩
    have hx2 : ¬ p ∣ x.2 := by
      intro h
      apply hx1
      have : p ∣ x.1 + x.2 := by rw [hs]; exact dvd_mul_right p _
      exact (Nat.dvd_add_left h).mp this
    exact bq_D (p * (m * p ^ e)) x.1 x.2 1 x.1 x.2 m (e + 1) le_rfl (by ring) (by ring)
      (by ring) (by rw [hs]; ring) hx1 (fun h => hx1 ((Nat.dvd_add_right hpN).mp h))
      (fun h => hx2 ((Nat.dvd_add_right hpN).mp h))
  have hP : D p (3 * (e + 1)) (∑ y ∈ antidiagonal (3 * (m * p ^ e)),
      (Bq (p * (m * p ^ e)) (p * y.1) (p * y.2) - Bq (m * p ^ e) y.1 y.2)) := by
    apply D.sum
    intro y hy
    exact div_term h5 e m (m * p ^ e) y.1 y.2 hm rfl (Finset.HasAntidiagonal.mem_antidiagonal.mp hy)
  have h2 : D p (3 * (e + 1)) (2 * ((a (p * (m * p ^ e)) : ℚ) - a (m * p ^ e))) := by
    rw [mul_sub, two_a _ hNpos, two_a _ hMpos,
      show 3 * (p * (m * p ^ e)) = p * (3 * (m * p ^ e)) by ring,
      split_sum p (3 * (m * p ^ e)) hp0 (fun x => Bq (p * (m * p ^ e)) x.1 x.2)]
    refine (hP.add hU).congr ?_
    rw [Finset.sum_sub_distrib]
    ring
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h3 : D p (3 * (e + 1)) (((a (p * (m * p ^ e)) - a (m * p ^ e) : ℤ) : ℚ)) :=
    D.ucancel hp2 (h2.congr (by push_cast; ring))
  exact D.dvd h3

theorem final :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 1 ≤ n → 1 ≤ k →
      ((p : ℤ) ^ (3 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  intro p n k hp h5 hn hk
  have := Fact.mk hp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := one_step h5 k' n hn
  rw [show p * (n * p ^ k') = n * p ^ (k' + 1) by ring] at h
  rw [Nat.add_sub_cancel]
  exact h

end A333562P

theorem OMA.solution : type_of% @OMA.S_oeis_a333562.main := A333562P.final
