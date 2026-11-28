import OMAStatements.S_oeis_a144750

namespace A144750Proof

/-- Hurwitz series over ZMod 9 with binomial convolution product. -/
structure HSeq where
  coeff : ℕ → ZMod 9

namespace HSeq

lemma ext {f g : HSeq} (h : ∀ n, f.coeff n = g.coeff n) : f = g := by
  cases f; cases g; congr; funext n; exact h n

instance : Zero HSeq := ⟨⟨fun _ => 0⟩⟩
instance : One HSeq := ⟨⟨fun n => if n = 0 then 1 else 0⟩⟩
instance : Add HSeq := ⟨fun f g => ⟨fun n => f.coeff n + g.coeff n⟩⟩
instance : Neg HSeq := ⟨fun f => ⟨fun n => -f.coeff n⟩⟩
instance : Sub HSeq := ⟨fun f g => ⟨fun n => f.coeff n - g.coeff n⟩⟩
instance : Mul HSeq :=
  ⟨fun f g => ⟨fun n =>
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * f.coeff k * g.coeff (n - k)⟩⟩

@[simp] lemma zero_coeff (n : ℕ) : (0 : HSeq).coeff n = 0 := rfl
@[simp] lemma one_coeff (n : ℕ) : (1 : HSeq).coeff n = if n = 0 then 1 else 0 := rfl
@[simp] lemma add_coeff (f g : HSeq) (n : ℕ) : (f + g).coeff n = f.coeff n + g.coeff n := rfl
@[simp] lemma neg_coeff (f : HSeq) (n : ℕ) : (-f).coeff n = -f.coeff n := rfl
@[simp] lemma sub_coeff (f g : HSeq) (n : ℕ) : (f - g).coeff n = f.coeff n - g.coeff n := rfl
@[simp] lemma mul_coeff (f g : HSeq) (n : ℕ) :
    (f * g).coeff n =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * f.coeff k * g.coeff (n - k) := rfl

lemma hMul_comm (f g : HSeq) : f * g = g * f := by
  apply ext; intro n
  simp only [mul_coeff]
  rw [← Finset.sum_range_reflect
    (fun k => (n.choose k : ZMod 9) * g.coeff k * f.coeff (n - k)) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : n + 1 - 1 - k = n - k := by omega
  rw [h1, Nat.choose_symm hkn, Nat.sub_sub_self hkn]
  ring

lemma hOne_mul (f : HSeq) : 1 * f = f := by
  apply ext; intro n
  simp only [mul_coeff, one_coeff]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk; simp [hk]
  · intro h0; exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ n)) h0

lemma hMul_assoc (f g h : HSeq) : f * g * h = f * (g * h) := by
  apply ext; intro n
  simp only [mul_coeff, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => ⟨x.2, x.1 - x.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨k, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨k1, j1⟩ hx1 ⟨k2, j2⟩ hx2 heq
    simp only [Finset.mem_sigma, Finset.mem_range] at hx1 hx2
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
    obtain ⟨hj, hk⟩ := heq
    have hk' : k1 = k2 := by omega
    subst hj; subst hk'; rfl
  · rintro ⟨j, i⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    refine ⟨⟨j + i, j⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]; omega
    · simp
  · rintro ⟨k, j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have hjk : j ≤ k := by omega
    have hsub : n - j - (k - j) = n - k := by omega
    have hch : (n.choose k : ZMod 9) * (k.choose j : ZMod 9) =
        (n.choose j : ZMod 9) * ((n - j).choose (k - j) : ZMod 9) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul hjk]
    rw [hsub]
    calc
      (n.choose k : ZMod 9) * ((k.choose j : ZMod 9) * f.coeff j * g.coeff (k - j)) *
          h.coeff (n - k)
        = ((n.choose k : ZMod 9) * (k.choose j : ZMod 9)) *
          f.coeff j * g.coeff (k - j) * h.coeff (n - k) := by ring
      _ = ((n.choose j : ZMod 9) * ((n - j).choose (k - j) : ZMod 9)) *
          f.coeff j * g.coeff (k - j) * h.coeff (n - k) := by rw [hch]
      _ = (n.choose j : ZMod 9) * f.coeff j *
          (((n - j).choose (k - j) : ZMod 9) * g.coeff (k - j) * h.coeff (n - k)) := by ring

instance : CommRing HSeq where
  add_assoc f g h := by apply ext; intro n; exact add_assoc _ _ _
  zero_add f := by apply ext; intro n; exact zero_add _
  add_zero f := by apply ext; intro n; exact add_zero _
  add_comm f g := by apply ext; intro n; exact add_comm _ _
  neg_add_cancel f := by apply ext; intro n; exact neg_add_cancel _
  sub_eq_add_neg f g := by apply ext; intro n; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec
  zero_mul f := by apply ext; intro n; simp
  mul_zero f := by apply ext; intro n; simp
  left_distrib f g h := by
    apply ext; intro n
    simp only [mul_coeff, add_coeff, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  right_distrib f g h := by
    apply ext; intro n
    simp only [mul_coeff, add_coeff, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  one_mul := hOne_mul
  mul_one f := by rw [hMul_comm, hOne_mul]
  mul_assoc := hMul_assoc
  mul_comm := hMul_comm

lemma natCast_coeff (c n : ℕ) : ((c : HSeq)).coeff n = if n = 0 then (c : ZMod 9) else 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.cast_succ, add_coeff, one_coeff, ih]
    split_ifs <;> simp

lemma nine_eq_zero : (9 : HSeq) = 0 := by
  apply ext; intro n
  rw [show (9 : HSeq) = ((9 : ℕ) : HSeq) by norm_num, natCast_coeff, zero_coeff]
  split_ifs <;> decide

/-- Shift derivation on Hurwitz series. -/
def D (f : HSeq) : HSeq := ⟨fun n => f.coeff (n + 1)⟩

@[simp] lemma D_coeff (f : HSeq) (n : ℕ) : (D f).coeff n = f.coeff (n + 1) := rfl

lemma D_add (f g : HSeq) : D (f + g) = D f + D g := by apply ext; intro n; simp
lemma D_neg (f : HSeq) : D (-f) = -D f := by apply ext; intro n; simp
lemma D_one : D (1 : HSeq) = 0 := by apply ext; intro n; simp
lemma D_two : D (2 : HSeq) = 0 := by
  rw [show (2 : HSeq) = 1 + 1 by norm_num, D_add, D_one, add_zero]
lemma D_three : D (3 : HSeq) = 0 := by
  rw [show (3 : HSeq) = 2 + 1 by norm_num, D_add, D_two, D_one, add_zero]

lemma D_mul (f g : HSeq) : D (f * g) = D f * g + f * D g := by
  apply ext; intro n
  simp only [D_coeff, add_coeff, mul_coeff]
  rw [Finset.sum_range_succ']
  have h1 : ∀ k ∈ Finset.range (n + 1),
      ((n + 1).choose (k + 1) : ZMod 9) * f.coeff (k + 1) * g.coeff (n + 1 - (k + 1)) =
      (n.choose k : ZMod 9) * f.coeff (k + 1) * g.coeff (n - k) +
      (n.choose (k + 1) : ZMod 9) * f.coeff (k + 1) * g.coeff (n - k) := by
    intro k _
    rw [Nat.choose_succ_succ, Nat.add_sub_add_right]
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, add_assoc]
  congr 1
  rw [Finset.sum_range_succ
    (fun k => (n.choose (k + 1) : ZMod 9) * f.coeff (k + 1) * g.coeff (n - k)) n]
  rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [Finset.sum_range_succ']
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k < n := Finset.mem_range.mp hk
    have hsub : n - (k + 1) + 1 = n - k := by omega
    rw [hsub]
  · simp

lemma D_pow (f : HSeq) : ∀ k : ℕ, D (f ^ (k + 1)) = ((k + 1 : ℕ) : HSeq) * f ^ k * D f
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, D_mul, D_pow f k]
    push_cast
    ring

lemma eq_two_of_D_eq_zero {f : HSeq} (hD : D f = 0) (h0 : f.coeff 0 = 2) : f = 2 := by
  apply ext; intro n
  cases n with
  | zero =>
    rw [h0, show (2 : HSeq) = 1 + 1 by norm_num, add_coeff, one_coeff]
    decide
  | succ n =>
    have hn : (D f).coeff n = 0 := congrArg (fun g => g.coeff n) hD
    rw [D_coeff] at hn
    rw [hn, show (2 : HSeq) = 1 + 1 by norm_num, add_coeff, one_coeff]
    simp

end HSeq

def u : HSeq := ⟨fun n => (OMA.S_oeis_a144750.pseudoFactorial n : ZMod 9)⟩
def v : HSeq := ⟨fun n => (-1 : ZMod 9) ^ n * (OMA.S_oeis_a144750.pseudoFactorial n : ZMod 9)⟩

lemma u_coeff_succ (n : ℕ) :
    u.coeff (n + 1) = (-1 : ZMod 9) ^ (n + 1) *
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * u.coeff k * u.coeff (n - k) := by
  dsimp [u]
  conv_lhs => rw [OMA.S_oeis_a144750.pseudoFactorial]
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ZMod 9) *
    (OMA.S_oeis_a144750.pseudoFactorial k : ZMod 9) *
    (OMA.S_oeis_a144750.pseudoFactorial (n - k) : ZMod 9))]

lemma hDu : HSeq.D u = -(v ^ 2) := by
  apply HSeq.ext; intro n
  rw [HSeq.D_coeff, u_coeff_succ, pow_two, HSeq.neg_coeff, HSeq.mul_coeff, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (-1 : ZMod 9) ^ (n + 1) = -((-1 : ZMod 9) ^ k * (-1 : ZMod 9) ^ (n - k)) := by
    rw [← pow_add, Nat.add_sub_of_le hkn, pow_succ]
    ring
  dsimp [v, u]
  rw [hpow]
  ring

lemma hDv : HSeq.D v = u ^ 2 := by
  apply HSeq.ext; intro n
  rw [HSeq.D_coeff, pow_two, HSeq.mul_coeff]
  change (-1 : ZMod 9) ^ (n + 1) * u.coeff (n + 1) = _
  rw [u_coeff_succ, ← mul_assoc, ← mul_pow]
  have h1 : ((-1 : ZMod 9) * (-1 : ZMod 9)) ^ (n + 1) = 1 := by
    rw [show (-1 : ZMod 9) * (-1 : ZMod 9) = 1 by decide, one_pow]
  rw [h1, one_mul]

lemma u0 : u.coeff 0 = 1 := by
  dsimp [u]; rw [OMA.S_oeis_a144750.pseudoFactorial]; rfl

lemma hv3 : v ^ 3 = 2 - u ^ 3 := by
  have hD : HSeq.D (u ^ 3 + v ^ 3) = 0 := by
    rw [HSeq.D_add, HSeq.D_pow u 2, HSeq.D_pow v 2, hDu, hDv]
    ring
  have h0 : (u ^ 3 + v ^ 3).coeff 0 = 2 := by
    have hv0 : v.coeff 0 = 1 := by
      dsimp [v]; rw [OMA.S_oeis_a144750.pseudoFactorial]; simp
    have hp3 : ∀ f : HSeq, (f ^ 3).coeff 0 = (f.coeff 0) ^ 3 := fun f => by
      rw [pow_succ, pow_two, HSeq.mul_coeff]
      simp [pow_succ]
    rw [HSeq.add_coeff, hp3 u, hp3 v, u0, hv0]
    decide
  have hsum : u ^ 3 + v ^ 3 = 2 := HSeq.eq_two_of_D_eq_zero hD h0
  linear_combination hsum

def D3 (f : HSeq) : HSeq := HSeq.D (HSeq.D (HSeq.D f))

lemma D3_add (f g : HSeq) : D3 (f + g) = D3 f + D3 g := by
  simp only [D3, HSeq.D_add]

lemma D3_neg (f : HSeq) : D3 (-f) = -D3 f := by
  simp only [D3, HSeq.D_neg]

lemma hD9 : D3 (D3 (D3 u)) = -u := by
  have hD2 : HSeq.D (HSeq.D u) = -2 * u ^ 2 * v := by
    rw [hDu, HSeq.D_neg, HSeq.D_pow v 1, hDv]
    push_cast
    ring
  have hD3 : D3 u = -u + 3 * u ^ 4 := by
    dsimp [D3]
    rw [hD2, HSeq.D_mul, HSeq.D_mul, HSeq.D_neg, HSeq.D_two, HSeq.D_pow u 1, hDu, hDv]
    push_cast
    linear_combination 4 * u * hv3 + (u - u ^ 4) * HSeq.nine_eq_zero
  have hDw1 : HSeq.D (3 * u ^ 4) = -3 * u ^ 3 * v ^ 2 := by
    rw [HSeq.D_mul, HSeq.D_three, HSeq.D_pow u 3, hDu]
    push_cast
    linear_combination -(u ^ 3 * v ^ 2) * HSeq.nine_eq_zero
  have hDw2 : HSeq.D (-3 * u ^ 3 * v ^ 2) = 3 * u ^ 5 * v := by
    rw [HSeq.D_mul, HSeq.D_mul, HSeq.D_neg, HSeq.D_three, HSeq.D_pow u 2, HSeq.D_pow v 1,
      hDu, hDv]
    push_cast
    linear_combination (u ^ 2 * v ^ 4 - u ^ 5 * v) * HSeq.nine_eq_zero
  have hDw3 : D3 (3 * u ^ 4) = -(3 * u ^ 4) := by
    dsimp [D3]
    rw [hDw1, hDw2, HSeq.D_mul, HSeq.D_mul, HSeq.D_three, HSeq.D_pow u 4, hDu, hDv]
    push_cast
    linear_combination -15 * u ^ 4 * hv3 + (2 * u ^ 7 - 3 * u ^ 4) * HSeq.nine_eq_zero
  have hD6 : D3 (D3 u) = u + 3 * u ^ 4 := by
    rw [hD3, D3_add, D3_neg, hD3, hDw3]
    linear_combination -(u ^ 4) * HSeq.nine_eq_zero
  rw [hD6, D3_add, hD3, hDw3]
  ring

lemma u_coeff_add_9 (n : ℕ) : u.coeff (n + 9) = -u.coeff n := by
  have h := congrArg (fun f : HSeq => f.coeff n) hD9
  simpa only [D3, HSeq.D_coeff, HSeq.neg_coeff] using h

lemma u_coeff_add_18 (n : ℕ) : u.coeff (n + 18) = u.coeff n := by
  rw [show n + 18 = (n + 9) + 9 by omega, u_coeff_add_9, u_coeff_add_9, neg_neg]

lemma a_eq_val (n : ℕ) : OMA.S_oeis_a144750.a n = ((u.coeff n).val : ℤ) := by
  dsimp [OMA.S_oeis_a144750.a, u]
  exact (ZMod.val_intCast (OMA.S_oeis_a144750.pseudoFactorial n)).symm

lemma a_add_18 (n : ℕ) : OMA.S_oeis_a144750.a (n + 18) = OMA.S_oeis_a144750.a n := by
  rw [a_eq_val, a_eq_val, u_coeff_add_18]

lemma u1 : u.coeff 1 = 8 := by
  rw [u_coeff_succ 0]; simp [u0]; decide
lemma u2 : u.coeff 2 = 7 := by
  rw [u_coeff_succ 1]; simp [Finset.sum_range_succ, u0, u1]; decide
lemma u3 : u.coeff 3 = 2 := by
  rw [u_coeff_succ 2]; simp [Finset.sum_range_succ, u0, u1, u2]; decide
lemma u4 : u.coeff 4 = 7 := by
  rw [u_coeff_succ 3]; simp [Finset.sum_range_succ, u0, u1, u2, u3]; decide
lemma u5 : u.coeff 5 = 5 := by
  rw [u_coeff_succ 4]; simp [Finset.sum_range_succ, u0, u1, u2, u3, u4]; decide
lemma u6 : u.coeff 6 = 4 := by
  rw [u_coeff_succ 5]; simp [Finset.sum_range_succ, u0, u1, u2, u3, u4, u5]; decide
lemma u7 : u.coeff 7 = 5 := by
  rw [u_coeff_succ 6]; simp [Finset.sum_range_succ, u0, u1, u2, u3, u4, u5, u6]; decide
lemma u8 : u.coeff 8 = 1 := by
  rw [u_coeff_succ 7]; simp [Finset.sum_range_succ, u0, u1, u2, u3, u4, u5, u6, u7]; decide

def tbl : ℕ → ℤ
  | 0 => 1 | 1 => 8 | 2 => 7 | 3 => 2 | 4 => 7 | 5 => 5
  | 6 => 4 | 7 => 5 | 8 => 1 | 9 => 8 | 10 => 1 | 11 => 2
  | 12 => 7 | 13 => 2 | 14 => 4 | 15 => 5 | 16 => 4 | 17 => 8
  | _ => 0

lemma a_eq_tbl_lt (n : ℕ) (hn : n < 18) : OMA.S_oeis_a144750.a n = tbl n := by
  rw [a_eq_val]
  interval_cases n
  · rw [u0]; rfl
  · rw [u1]; rfl
  · rw [u2]; rfl
  · rw [u3]; rfl
  · rw [u4]; rfl
  · rw [u5]; rfl
  · rw [u6]; rfl
  · rw [u7]; rfl
  · rw [u8]; rfl
  · rw [show u.coeff 9 = -u.coeff 0 from u_coeff_add_9 0, u0]; rfl
  · rw [show u.coeff 10 = -u.coeff 1 from u_coeff_add_9 1, u1]; rfl
  · rw [show u.coeff 11 = -u.coeff 2 from u_coeff_add_9 2, u2]; rfl
  · rw [show u.coeff 12 = -u.coeff 3 from u_coeff_add_9 3, u3]; rfl
  · rw [show u.coeff 13 = -u.coeff 4 from u_coeff_add_9 4, u4]; rfl
  · rw [show u.coeff 14 = -u.coeff 5 from u_coeff_add_9 5, u5]; rfl
  · rw [show u.coeff 15 = -u.coeff 6 from u_coeff_add_9 6, u6]; rfl
  · rw [show u.coeff 16 = -u.coeff 7 from u_coeff_add_9 7, u7]; rfl
  · rw [show u.coeff 17 = -u.coeff 8 from u_coeff_add_9 8, u8]; rfl

lemma a_eq_mod (n : ℕ) : OMA.S_oeis_a144750.a n = OMA.S_oeis_a144750.a (n % 18) := by
  have h : ∀ q r, OMA.S_oeis_a144750.a (r + 18 * q) = OMA.S_oeis_a144750.a r := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show r + 18 * (q + 1) = (r + 18 * q) + 18 by omega, a_add_18, ih]
  conv_lhs => rw [← Nat.mod_add_div n 18]
  exact h (n / 18) (n % 18)

lemma a_eq_tbl (n : ℕ) : OMA.S_oeis_a144750.a n = tbl (n % 18) := by
  rw [a_eq_mod]
  exact a_eq_tbl_lt (n % 18) (Nat.mod_lt n (by decide))

lemma a_rec (n : ℕ) (hn : 7 < n) :
    OMA.S_oeis_a144750.a n =
      OMA.S_oeis_a144750.a (n - 2) + OMA.S_oeis_a144750.a (n - 3) -
      OMA.S_oeis_a144750.a (n - 5) - OMA.S_oeis_a144750.a (n - 6) +
      OMA.S_oeis_a144750.a (n - 8) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  simp only [show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega,
    show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega,
    show m + 8 - 8 = m by omega, a_eq_tbl]
  have hmod : ∀ k, (m + k) % 18 = (m % 18 + k) % 18 := fun k => by omega
  rw [hmod 8, hmod 6, hmod 5, hmod 3, hmod 2]
  set r := m % 18
  have hr : r < 18 := Nat.mod_lt m (by decide)
  interval_cases r <;> rfl

lemma a_gf :
    let X : PowerSeries ℤ := PowerSeries.X
    PowerSeries.mk OMA.S_oeis_a144750.a * ((X - 1) * (X + 1) * (X ^ 6 - X ^ 3 + 1)) =
      -8 * X ^ 7 - 4 * X ^ 6 + 3 * X ^ 5 + 8 * X ^ 4 + 7 * X ^ 3 -
        6 * X ^ 2 - 8 * X - 1 := by
  intro X
  have hlhs : PowerSeries.mk OMA.S_oeis_a144750.a * ((X - 1) * (X + 1) * (X ^ 6 - X ^ 3 + 1)) =
      PowerSeries.mk OMA.S_oeis_a144750.a * X ^ 8 -
      PowerSeries.mk OMA.S_oeis_a144750.a * X ^ 6 -
      PowerSeries.mk OMA.S_oeis_a144750.a * X ^ 5 +
      PowerSeries.mk OMA.S_oeis_a144750.a * X ^ 3 +
      PowerSeries.mk OMA.S_oeis_a144750.a * X ^ 2 -
      PowerSeries.mk OMA.S_oeis_a144750.a := by ring
  have hrhs : (-8 : PowerSeries ℤ) * X ^ 7 - 4 * X ^ 6 + 3 * X ^ 5 + 8 * X ^ 4 +
      7 * X ^ 3 - 6 * X ^ 2 - 8 * X - 1 =
      PowerSeries.C (-8) * X ^ 7 + PowerSeries.C (-4) * X ^ 6 + PowerSeries.C 3 * X ^ 5 +
      PowerSeries.C 8 * X ^ 4 + PowerSeries.C 7 * X ^ 3 + PowerSeries.C (-6) * X ^ 2 +
      PowerSeries.C (-8) * X + PowerSeries.C (-1) := by
    simp only [map_neg, map_ofNat, map_one]
    ring
  rw [hlhs, hrhs]
  ext n
  simp only [X, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C,
    PowerSeries.coeff_X, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
  by_cases hn : 7 < n
  · simp only [show 8 ≤ n by omega, show 7 ≤ n by omega, show 6 ≤ n by omega,
      show 5 ≤ n by omega, show 4 ≤ n by omega, show 3 ≤ n by omega, show 2 ≤ n by omega,
      show n - 7 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n ≠ 1 by omega, show n ≠ 0 by omega, ↓reduceIte]
    linarith [a_rec n hn]
  · interval_cases n <;> simp [a_eq_tbl, tbl]

end A144750Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a144750.main :=
  ⟨A144750Proof.a_rec, A144750Proof.a_gf⟩
