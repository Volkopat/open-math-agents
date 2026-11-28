import OMAStatements.S_oeis_a027087

/-!
OEIS A027087 (Clark Kimberling): a(n) = A027082(n, 2n).
Conjecture: D-finite with recurrence +3*n*a(n) +3*(-5*n+3)*a(n-1) +(7*n-4)*a(n-2) +(25*n-67)*a(n-3) +(17*n-44)*a(n-4) +(19*n-97)*a(n-5) +(5*n-32)*a(n-6) +3*(n-7)*a(n-7)=0.

Proof (kernel method). With u(n, d) = T(n, 2n - d), the row polynomials E_n(y) = sum_d u(n, d) y^d
satisfy y E_n = (1 + y + y^2) E_(n-1) - (u(n-1, 0) + y^(2n-1) - y^(2n+1)) for n >= 2 (`row_poly`).
At the kernel root y = X M, M the Motzkin series, the left side cancels after telescoping
(`telescope`, `kernel`), which gives the edge diagonal F_0 = sum_n u(n, 0) X^n as R F_0 = P_0 + Q_0
M with R = 1 - 3X - X^2 - X^3 (`hF0`). The array recursion along the diagonals (`vert`) gives R F_d
= P_d + Q_d M for the other diagonals (`hF`). Mathar's recurrence is the differential equation L F_d
= B in θ = X d/dX, an identity linear in M once θ M is replaced by its value from the Motzkin
equation (`θM`, `ode`); the coefficient of X^n is the recurrence (`recur`).
-/

namespace OMA.S_oeis_a027087

open Finset PowerSeries


/-! ### The operator θ = X d/dX on rational power series -/

/-- θ multiplies the n-th coefficient by n. -/
noncomputable def θ (F : ℚ⟦X⟧) : ℚ⟦X⟧ := PowerSeries.mk fun n => (n : ℚ) * coeff n F

lemma coeff_θ (F : ℚ⟦X⟧) (n : ℕ) : coeff n (θ F) = n * coeff n F := coeff_mk _ _

lemma θ_add (F G : ℚ⟦X⟧) : θ (F + G) = θ F + θ G := by
  ext n
  simp [coeff_θ, mul_add]

lemma θ_sub (F G : ℚ⟦X⟧) : θ (F - G) = θ F - θ G := by
  ext n
  simp [coeff_θ, mul_sub]

lemma θ_mul (F G : ℚ⟦X⟧) : θ (F * G) = θ F * G + F * θ G := by
  ext n
  simp only [coeff_θ, map_add, coeff_mul, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun p hp => ?_)
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp]
  push_cast
  ring

lemma θ_C (c : ℚ) : θ (C c) = 0 := by
  ext n
  rw [coeff_θ, coeff_C]
  split_ifs with h <;> simp [h]

lemma θ_one : θ 1 = 0 := by
  rw [← map_one C, θ_C]

lemma θ_ofNat (c : ℕ) [c.AtLeastTwo] : θ (no_index (OfNat.ofNat c : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C c, θ_C]

lemma θ_X : θ X = X := by
  ext n
  rw [coeff_θ, coeff_X]
  split_ifs with h <;> simp [h]

lemma θ_X_pow (k : ℕ) : θ (X ^ k) = (k : ℚ⟦X⟧) * X ^ k := by
  ext n
  rw [coeff_θ, coeff_X_pow, ← map_natCast C, coeff_C_mul, coeff_X_pow]
  split_ifs with h <;> simp [h]

/-! ### The Motzkin series -/

/-- The Motzkin numbers: m(n+1) = m(n) + sum_(k<n) m(k) m(n-1-k). -/
def mz : ℕ → ℚ
  | 0 => 1
  | n + 1 => mz n + ∑ k : Fin n, mz k * mz (n - 1 - k)

/-- The Motzkin series M = 1 + X M + X^2 M^2. -/
noncomputable def M : ℚ⟦X⟧ := PowerSeries.mk mz

lemma M_quad : M = 1 + X * M + X ^ 2 * M ^ 2 := by
  ext n
  rcases n with _ | _ | m
  · simp [M, mz]
  · simp [M, mz, coeff_X_pow_mul', coeff_one]
  · have h1 : coeff (m + 1 + 1) (X * M) = mz (m + 1) := by
      rw [coeff_succ_X_mul]
      simp [M]
    have h2 : coeff (m + 1 + 1) (X ^ 2 * M ^ 2) = ∑ p ∈ antidiagonal m, mz p.1 * mz p.2 := by
      rw [coeff_X_pow_mul', if_pos (by omega), show m + 1 + 1 - 2 = m by omega, pow_two, coeff_mul]
      simp [M]
    rw [map_add, map_add, h1, h2, coeff_one, if_neg (by omega), zero_add]
    simp only [M, coeff_mk]
    rw [mz, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
    simp

lemma M_const : constantCoeff M = 1 := by
  simp [M, ← coeff_zero_eq_constantCoeff_apply, mz]

/-- θ M from the quadratic: (1 - 2X - 3X^2) θ M = (3X^2 + 3X - 2) M + 2. -/
lemma θM : (1 - 2 * X - 3 * X ^ 2) * θ M = (3 * X ^ 2 + 3 * X - 2) * M + 2 := by
  have hq := M_quad
  have h := congrArg θ hq
  rw [θ_add, θ_add, θ_one, θ_mul, θ_mul, θ_X, θ_X_pow, pow_two M, θ_mul] at h
  push_cast at h
  linear_combination (1 - X - 2 * X ^ 2 * M) * h + (2 + 4 * X ^ 2 * M + 4 * X ^ 2 * θ M) * hq

lemma M_ne_zero : M ≠ 0 := by
  intro h
  have := M_const
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- The coefficients of A * B up to K only see those of B up to K. -/
lemma coeff_mul_low (A B : ℚ⟦X⟧) (K : ℕ) (h : ∀ j ≤ K, coeff j B = 0) : coeff K (A * B) = 0 := by
  rw [coeff_mul]
  refine sum_eq_zero (fun p hp => ?_)
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [h p.2 (by omega), mul_zero]

lemma coeff_X_pow_mul_low (W : ℚ⟦X⟧) (K : ℕ) : coeff K (X ^ (K + 1) * W) = 0 := by
  rw [coeff_X_pow_mul', if_neg (by omega)]

/-- Telescoping X M E(m+2) = M E(m+1) - c(m). -/
lemma telescope (E c : ℕ → ℚ⟦X⟧) (h : ∀ m, X * M * E (m + 2) = M * E (m + 1) - c m) (N : ℕ) :
    X * M * E 1 = ∑ m ∈ range N, X ^ (m + 1) * c m + X ^ (N + 1) * (M * E (N + 1)) := by
  induction N with
  | zero =>
    simp only [range_zero, sum_empty, zero_add, pow_one]
    ring
  | succ N ih =>
    rw [ih, sum_range_succ]
    linear_combination (-X ^ (N + 1)) * h N

lemma θ_neg (F : ℚ⟦X⟧) : θ (-F) = -θ F := by
  ext n
  simp [coeff_θ]

lemma ne_zero_of_constantCoeff {G : ℚ⟦X⟧} (h : constantCoeff G ≠ 0) : G ≠ 0 := by
  intro hG
  rw [hG, map_zero] at h
  exact h rfl

/-- The polynomial sum_i cs_i X^i. -/
noncomputable def pl (cs : List ℚ) : ℚ⟦X⟧ := ∑ i ∈ range cs.length, C (cs.getD i 0) * X ^ i

lemma coeff_pl_mul (cs : List ℚ) (G : ℚ⟦X⟧) (n : ℕ) (h : cs.length ≤ n + 1) :
    coeff n (pl cs * G) = ∑ i ∈ range cs.length, cs.getD i 0 * coeff (n - i) G := by
  unfold pl
  rw [sum_mul, map_sum]
  refine sum_congr rfl (fun i hi => ?_)
  rw [mem_range] at hi
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega)]

lemma coeff_pl_big (cs : List ℚ) (n : ℕ) (h : cs.length ≤ n) : coeff n (pl cs) = 0 := by
  unfold pl
  rw [map_sum]
  refine sum_eq_zero (fun i hi => ?_)
  rw [mem_range] at hi
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

/-! ### The array A027082 -/

lemma T_big (n k : ℕ) (h : 2 * n < k) : T n k = 0 := by
  cases n with
  | zero => simp only [T]; rw [if_neg (by omega)]
  | succ n => rw [T, if_pos h]

lemma T_low (n k : ℕ) (h1 : 1 ≤ n) (h2 : k < 3) : T n k = 1 := by
  cases n with
  | zero => omega
  | succ n => rw [T, if_neg (by omega), if_pos h2]

lemma T_edge (n : ℕ) (hn : 1 ≤ n) : T (n + 1) (2 * (n + 1)) = T n (2 * n - 1) + T n (2 * n) := by
  rw [T, if_neg (by omega), if_neg (by omega), if_pos rfl, show 2 * (n + 1) - 3 = 2 * n - 1 by omega,
    show 2 * (n + 1) - 2 = 2 * n by omega]

lemma T_rec (n k : ℕ) (h1 : 3 ≤ k) (h2 : k < 2 * (n + 1)) :
    T (n + 1) k = T n (k - 3) + T n (k - 2) + T n (k - 1) := by
  rw [T, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- u(n, d) = T(n, 2n - d): the d-th diagonal from the right edge (0 for d > 2n). -/
def u (n d : ℕ) : ℕ := if d ≤ 2 * n then T n (2 * n - d) else 0

lemma u_big (n d : ℕ) (h : 2 * n < d) : u n d = 0 := by
  rw [u, if_neg (by omega)]

lemma u_eqT (n d : ℕ) (h : d ≤ 2 * n) : u n d = T n (2 * n - d) := by
  rw [u, if_pos h]

lemma u_low (n d : ℕ) (hn : 1 ≤ n) (h1 : d ≤ 2 * n) (h2 : 2 * n < d + 3) : u n d = 1 := by
  rw [u_eqT n d h1]
  exact T_low n _ hn (by omega)

/-- The right edge: u(n+1, 0) = u(n, 0) + u(n, 1). -/
lemma u_edge (n : ℕ) : u (n + 1) 0 = u n 0 + u n 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · rw [u_eqT (n + 1) 0 (by omega), Nat.sub_zero, T_edge n hn, u_eqT n 0 (by omega),
      u_eqT n 1 (by omega), Nat.sub_zero, add_comm]

lemma u_rec (n d : ℕ) (h1 : 1 ≤ d) (h2 : d + 1 ≤ 2 * n) :
    u (n + 1) d = u n (d - 1) + u n d + u n (d + 1) := by
  rw [u, if_pos (by omega), T_rec n _ (by omega) (by omega), u, u, u, if_pos (by omega),
    if_pos (by omega), if_pos (by omega), show 2 * (n + 1) - d - 3 = 2 * n - (d + 1) by omega,
    show 2 * (n + 1) - d - 2 = 2 * n - d by omega, show 2 * (n + 1) - d - 1 = 2 * n - (d - 1) by omega]
  ring

/-- The row polynomial sum_d u(n, d) y^d. -/
noncomputable def rowP (n : ℕ) : Polynomial ℚ :=
  ∑ d ∈ range (2 * n + 1), Polynomial.C (u n d : ℚ) * Polynomial.X ^ d

lemma coeff_rowP (n e : ℕ) : (rowP n).coeff e = (u n e : ℚ) := by
  unfold rowP
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range] at h
    rw [u_big n e (by omega)]
    simp

/-- The row recursion as a polynomial identity. -/
lemma row_poly (n : ℕ) (hn : 1 ≤ n) :
    Polynomial.X ^ 1 * rowP (n + 1) + (Polynomial.C (u n 0 : ℚ) +
      Polynomial.X ^ (2 * n + 1) - Polynomial.X ^ (2 * n + 3)) =
      rowP n + Polynomial.X ^ 1 * rowP n + Polynomial.X ^ 2 * rowP n := by
  ext e
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C,
    Polynomial.coeff_X_pow, Polynomial.coeff_X_pow_mul', coeff_rowP]
  rcases (show e = 0 ∨ e = 1 ∨ (2 ≤ e ∧ e ≤ 2 * n) ∨ e = 2 * n + 1 ∨ e = 2 * n + 2 ∨
      e = 2 * n + 3 ∨ 2 * n + 3 < e by omega) with h | h | h | h | h | h | h
  · subst h
    simp
  · subst h
    simp only [if_pos (show 1 ≤ 1 by omega), if_neg (show ¬ (1 : ℕ) = 0 by omega),
      if_neg (show ¬ 1 = 2 * n + 1 by omega), if_neg (show ¬ 1 = 2 * n + 3 by omega),
      if_neg (show ¬ 2 ≤ 1 by omega)]
    rw [show 1 - 1 = 0 by rfl, u_edge n]
    push_cast
    ring
  · simp only [if_pos (show 1 ≤ e by omega), if_neg (show ¬ e = 0 by omega),
      if_neg (show ¬ e = 2 * n + 1 by omega), if_neg (show ¬ e = 2 * n + 3 by omega),
      if_pos (show 2 ≤ e by omega)]
    rw [u_rec n (e - 1) (by omega) (by omega), show e - 1 - 1 = e - 2 by omega,
      show e - 1 + 1 = e by omega]
    push_cast
    ring
  · subst h
    simp only [if_pos (show 1 ≤ 2 * n + 1 by omega), if_neg (show ¬ 2 * n + 1 = 0 by omega),
      if_true, if_neg (show ¬ 2 * n + 1 = 2 * n + 3 by omega), if_pos (show 2 ≤ 2 * n + 1 by omega)]
    rw [u_low (n + 1) _ (by omega) (by omega) (by omega), u_big n (2 * n + 1) (by omega),
      u_low n _ hn (by omega) (by omega), u_low n (2 * n + 1 - 2) hn (by omega) (by omega)]
    norm_num
  · subst h
    simp only [if_pos (show 1 ≤ 2 * n + 2 by omega), if_neg (show ¬ 2 * n + 2 = 0 by omega),
      if_neg (show ¬ 2 * n + 2 = 2 * n + 1 by omega), if_neg (show ¬ 2 * n + 2 = 2 * n + 3 by omega),
      if_pos (show 2 ≤ 2 * n + 2 by omega)]
    rw [u_low (n + 1) _ (by omega) (by omega) (by omega), u_big n (2 * n + 2) (by omega),
      u_big n (2 * n + 2 - 1) (by omega), u_low n (2 * n + 2 - 2) hn (by omega) (by omega)]
    norm_num
  · subst h
    simp only [if_pos (show 1 ≤ 2 * n + 3 by omega), if_neg (show ¬ 2 * n + 3 = 0 by omega),
      if_neg (show ¬ 2 * n + 3 = 2 * n + 1 by omega), if_true, if_pos (show 2 ≤ 2 * n + 3 by omega)]
    rw [u_low (n + 1) _ (by omega) (by omega) (by omega), u_big n (2 * n + 3) (by omega),
      u_big n (2 * n + 3 - 1) (by omega), u_big n (2 * n + 3 - 2) (by omega)]
    norm_num
  · simp only [if_pos (show 1 ≤ e by omega), if_neg (show ¬ e = 0 by omega),
      if_neg (show ¬ e = 2 * n + 1 by omega), if_neg (show ¬ e = 2 * n + 3 by omega),
      if_pos (show 2 ≤ e by omega)]
    rw [u_big (n + 1) _ (by omega), u_big n e (by omega), u_big n (e - 1) (by omega),
      u_big n (e - 2) (by omega)]
    norm_num

/-- The row polynomial at the kernel root X M. -/
noncomputable def E (n : ℕ) : ℚ⟦X⟧ := Polynomial.aeval (X * M) (rowP n)

lemma XM_eq : X * M = X * (1 + X * M + (X * M) ^ 2) := by
  linear_combination X * M_quad

/-- The row recursion at the kernel root. -/
lemma row_ps (m : ℕ) : X * M * E (m + 2) = M * E (m + 1) -
    ((u (m + 1) 0 : ℚ⟦X⟧) + (X * M) ^ (2 * m + 3) - (X * M) ^ (2 * m + 5)) := by
  have h := congrArg (Polynomial.aeval (X * M)) (row_poly (m + 1) (by omega))
  simp only [map_add, map_sub, map_mul, map_pow, map_one, Polynomial.aeval_X,
    Polynomial.aeval_C, map_natCast] at h
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) + 3 = 2 * m + 5 by ring] at h
  apply mul_left_cancel₀ (X_ne_zero (R := ℚ))
  unfold E
  linear_combination X * h - Polynomial.aeval (X * M) (rowP (m + 1)) * XM_eq

/-- The diagonal series F_d = sum_n u(n, d) X^n. -/
noncomputable def F (d : ℕ) : ℚ⟦X⟧ := PowerSeries.mk fun n => (u n d : ℚ)

lemma E_one : E 1 = M := by
  have h0 : u 1 0 = 1 := by decide
  have h1 : u 1 1 = 1 := by decide
  have h2 : u 1 2 = 1 := by decide
  unfold E rowP
  simp only [show 2 * 1 + 1 = 3 by rfl, sum_range_succ, range_zero, sum_empty, zero_add, h0, h1, h2]
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, Nat.cast_one,
    map_one, pow_zero, one_mul, pow_one]
  linear_combination -M_quad

lemma geom3 (N : ℕ) : (1 - X * (X * M) ^ 2) *
    ∑ m ∈ range N, X ^ (m + 1) * ((X * M) ^ (2 * m + 3) - (X * M) ^ (2 * m + 5)) =
      X * ((X * M) ^ 3 - (X * M) ^ 5) -
        X ^ (N + 1) * ((X * M) ^ (2 * N + 3) - (X * M) ^ (2 * N + 5)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih]
    ring

lemma low0 (N j : ℕ) (hj : j ≤ N) :
    coeff j (∑ m ∈ range N, X ^ (m + 1) * ((u (m + 1) 0 : ℕ) : ℚ⟦X⟧)) = coeff j (F 0 - 1) := by
  rw [map_sum, map_sub]
  simp only [F, coeff_mk, coeff_one]
  rcases j with _ | j
  · rw [sum_eq_zero (fun m _ => by rw [coeff_X_pow_mul', if_neg (by omega)])]
    have : u 0 0 = 1 := by decide
    simp [this]
  · rw [sum_eq_single j]
    · rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, ← map_natCast C, coeff_zero_C]
      simp
    · intro m _ hm
      rw [coeff_X_pow_mul']
      split_ifs with h
      · rw [← map_natCast C, coeff_C, if_neg (by omega)]
      · rfl
    · intro h
      rw [mem_range] at h
      omega

/-- The kernel identity: the boundary terms of the row recursion, summed. -/
lemma kernel : (1 - X * (X * M) ^ 2) * (X * M * M) =
    (1 - X * (X * M) ^ 2) * (F 0 - 1) + X * ((X * M) ^ 3 - (X * M) ^ 5) := by
  ext K
  have ht := telescope E (fun m => (u (m + 1) 0 : ℚ⟦X⟧) + (X * M) ^ (2 * m + 3) -
    (X * M) ^ (2 * m + 5)) row_ps K
  rw [E_one] at ht
  have hs : ∑ m ∈ range K, X ^ (m + 1) * ((u (m + 1) 0 : ℚ⟦X⟧) +
      (X * M) ^ (2 * m + 3) - (X * M) ^ (2 * m + 5)) =
      ∑ m ∈ range K, X ^ (m + 1) * ((u (m + 1) 0 : ℕ) : ℚ⟦X⟧) +
        ∑ m ∈ range K, X ^ (m + 1) * ((X * M) ^ (2 * m + 3) - (X * M) ^ (2 * m + 5)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl (fun m _ => ?_)
    ring
  have hd : (1 - X * (X * M) ^ 2) * (X * M * M) -
      ((1 - X * (X * M) ^ 2) * (F 0 - 1) + X * ((X * M) ^ 3 - (X * M) ^ 5)) =
      (1 - X * (X * M) ^ 2) *
          (∑ m ∈ range K, X ^ (m + 1) * ((u (m + 1) 0 : ℕ) : ℚ⟦X⟧) - (F 0 - 1)) +
        X ^ (K + 1) * (-((X * M) ^ (2 * K + 3) - (X * M) ^ (2 * K + 5)) +
          (1 - X * (X * M) ^ 2) * (M * E (K + 1))) := by
    linear_combination (1 - X * (X * M) ^ 2) * ht + (1 - X * (X * M) ^ 2) * hs + geom3 K
  have h0 : coeff K ((1 - X * (X * M) ^ 2) * (X * M * M) -
      ((1 - X * (X * M) ^ 2) * (F 0 - 1) + X * ((X * M) ^ 3 - (X * M) ^ 5))) = 0 := by
    rw [hd, map_add, coeff_X_pow_mul_low, add_zero]
    apply coeff_mul_low
    intro j hj
    rw [map_sub, low0 K j hj, sub_self]
  rwa [map_sub, sub_eq_zero] at h0

/-- The right edge along the diagonals: F_0 = 1 + X (F_0 + F_1). -/
lemma vert0 : F 0 = 1 + X * (F 0 + F 1) := by
  ext n
  rcases n with _ | m
  · have : u 0 0 = 1 := by decide
    simp [F, this]
  · simp only [map_add, coeff_succ_X_mul, F, coeff_mk, coeff_one, u_edge m]
    simp

/-! ### The diagonals -/

/-- The edge diagonal from the kernel identity: R F_0 = P_0 + Q_0 M. -/
lemma hF0 : (1 - 3 * X - X ^ 2 - X ^ 3) * F 0 = (1 - 2 * X + X ^ 2) + (-3 * X ^ 2 - X ^ 4) * M := by
  have hk := kernel
  have hA : (1 - X * (X * M) ^ 2) ≠ 0 := by
    apply ne_zero_of_constantCoeff
    simp
  apply mul_left_cancel₀ hA
  linear_combination (-(1 - 3 * X - X ^ 2 - X ^ 3)) * hk + ((X + 2 * X ^ 2 + X ^ 3) + (X - 2 * X ^ 2 - X ^ 3 - 2 * X ^ 4) * M + (X ^ 3 - 3 * X ^ 4 - X ^ 5 - X ^ 6) * M ^ 2 + (-X ^ 4 + 3 * X ^ 5 + X ^ 6 + X ^ 7) * M ^ 3) * M_quad

/-! ### The differential equation and the recurrence -/

lemma θR : θ (1 - 3 * X - X ^ 2 - X ^ 3) = (-3 * X - 2 * X ^ 2 - 3 * X ^ 3) := by
  simp only [θ_add, θ_sub, θ_mul, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg]
  push_cast
  ring

lemma θP : θ (1 - 2 * X + X ^ 2) = (-2 * X + 2 * X ^ 2) := by
  simp only [θ_add, θ_sub, θ_mul, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg]
  push_cast
  ring

lemma θQ : θ (-3 * X ^ 2 - X ^ 4) = (-6 * X ^ 2 - 4 * X ^ 4) := by
  simp only [θ_add, θ_sub, θ_mul, θ_X_pow, θ_X, θ_ofNat, θ_one, θ_neg]
  push_cast
  ring

/-- Mathar's recurrence as a differential equation: L F_0 = B. -/
lemma ode : pl [3, -15, 7, 25, 17, 19, 5, 3] * θ (F 0) + pl [0, -6, 10, 8, 24, -2, -2] * F 0 = pl [0, -3, 1, -2, -18, -11, 1] := by
  have e1 : (1 - 3 * X - X ^ 2 - X ^ 3) * F 0 = (1 - 2 * X + X ^ 2) + (-3 * X ^ 2 - X ^ 4) * M := hF0
  have e2 : (-3 * X - 2 * X ^ 2 - 3 * X ^ 3) * F 0 + (1 - 3 * X - X ^ 2 - X ^ 3) * θ (F 0) =
      (-2 * X + 2 * X ^ 2) + (-6 * X ^ 2 - 4 * X ^ 4) * M + (-3 * X ^ 2 - X ^ 4) * θ M := by
    have h := congrArg θ e1
    rw [θ_mul (1 - 3 * X - X ^ 2 - X ^ 3) (F 0), θ_add (1 - 2 * X + X ^ 2) ((-3 * X ^ 2 - X ^ 4) * M), θ_mul (-3 * X ^ 2 - X ^ 4) M, θR, θP, θQ] at h
    linear_combination h
  have e4 := θM
  have hK : ((1 - 8 * X + 16 * X ^ 2 + 8 * X ^ 3 - 22 * X ^ 4 - 24 * X ^ 5 - 24 * X ^ 6 - 8 * X ^ 7 - 3 * X ^ 8) : ℚ⟦X⟧) ≠ 0 := by
    apply ne_zero_of_constantCoeff
    simp
  have h : (1 - 8 * X + 16 * X ^ 2 + 8 * X ^ 3 - 22 * X ^ 4 - 24 * X ^ 5 - 24 * X ^ 6 - 8 * X ^ 7 - 3 * X ^ 8) * ((3 - 15 * X + 7 * X ^ 2 + 25 * X ^ 3 + 17 * X ^ 4 + 19 * X ^ 5 + 5 * X ^ 6 + 3 * X ^ 7) * θ (F 0) + (-6 * X + 10 * X ^ 2 + 8 * X ^ 3 + 24 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6) * F 0) = (1 - 8 * X + 16 * X ^ 2 + 8 * X ^ 3 - 22 * X ^ 4 - 24 * X ^ 5 - 24 * X ^ 6 - 8 * X ^ 7 - 3 * X ^ 8) * (-3 * X + X ^ 2 - 2 * X ^ 3 - 18 * X ^ 4 - 11 * X ^ 5 + X ^ 6) := by
    linear_combination (3 * X - 17 * X ^ 2 - 3 * X ^ 3 + 105 * X ^ 4 - 2 * X ^ 5 - 42 * X ^ 6 - 278 * X ^ 7 - 510 * X ^ 8 - 401 * X ^ 9 - 277 * X ^ 10 - 87 * X ^ 11 - 27 * X ^ 12) * e1 + (3 - 30 * X + 88 * X ^ 2 - 10 * X ^ 3 - 229 * X ^ 4 - 12 * X ^ 5 + 184 * X ^ 6 + 332 * X ^ 7 + 345 * X ^ 8 + 202 * X ^ 9 + 112 * X ^ 10 + 30 * X ^ 11 + 9 * X ^ 12) * e2 + (-9 * X ^ 2 + 72 * X ^ 3 - 150 * X ^ 4 - 24 * X ^ 5 + 101 * X ^ 6 + 176 * X ^ 7 + 332 * X ^ 8 + 208 * X ^ 9 + 193 * X ^ 10 + 72 * X ^ 11 + 42 * X ^ 12 + 8 * X ^ 13 + 3 * X ^ 14) * e4
  have ha1 : pl [3, -15, 7, 25, 17, 19, 5, 3] = (3 - 15 * X + 7 * X ^ 2 + 25 * X ^ 3 + 17 * X ^ 4 + 19 * X ^ 5 + 5 * X ^ 6 + 3 * X ^ 7) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have ha0 : pl [0, -6, 10, 8, 24, -2, -2] = (-6 * X + 10 * X ^ 2 + 8 * X ^ 3 + 24 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  have hB : pl [0, -3, 1, -2, -18, -11, 1] = (-3 * X + X ^ 2 - 2 * X ^ 3 - 18 * X ^ 4 - 11 * X ^ 5 + X ^ 6) := by
    simp only [pl, sum_range_succ, range_zero, sum_empty, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, map_neg, map_ofNat C, map_one, map_zero]
    ring
  rw [ha1, ha0, hB]
  exact mul_left_cancel₀ hK h

lemma u_a (m : ℕ) : u m 0 = a m := by
  rw [u, if_pos (by omega), a, Nat.sub_zero]

/-- Mathar's recurrence. -/
theorem recur : ∀ n : ℕ, 7 ≤ n →
    3 * (n : ℤ) * (a n : ℤ) + 3 * (-5 * (n : ℤ) + 3) * (a (n - 1) : ℤ) + (7 * (n : ℤ) - 4) * (a (n - 2) : ℤ) + (25 * (n : ℤ) - 67) * (a (n - 3) : ℤ) + (17 * (n : ℤ) - 44) * (a (n - 4) : ℤ) + (19 * (n : ℤ) - 97) * (a (n - 5) : ℤ) + (5 * (n : ℤ) - 32) * (a (n - 6) : ℤ) + 3 * ((n : ℤ) - 7) * (a (n - 7) : ℤ) = 0 := by
  intro n hn
  have h := congrArg (coeff n) ode
  rw [map_add, coeff_pl_mul _ _ _ (by norm_num; omega), coeff_pl_mul _ _ _ (by norm_num; omega), coeff_pl_big _ _ (by norm_num; omega)] at h
  simp only [coeff_θ, F, coeff_mk, sum_range_succ, sum_range_zero, zero_add, List.getD_cons_zero,
    List.getD_cons_succ, List.length_cons, List.length_nil, Nat.sub_zero] at h
  have c1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c4 : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c5 : ((n - 5 : ℕ) : ℚ) = (n : ℚ) - 5 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c6 : ((n - 6 : ℕ) : ℚ) = (n : ℚ) - 6 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have c7 : ((n - 7 : ℕ) : ℚ) = (n : ℚ) - 7 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have u1 : (u (n - 1) 0 : ℚ) = (a (n - 1) : ℚ) := by rw [u_a]
  have u2 : (u (n - 2) 0 : ℚ) = (a (n - 2) : ℚ) := by rw [u_a]
  have u3 : (u (n - 3) 0 : ℚ) = (a (n - 3) : ℚ) := by rw [u_a]
  have u4 : (u (n - 4) 0 : ℚ) = (a (n - 4) : ℚ) := by rw [u_a]
  have u5 : (u (n - 5) 0 : ℚ) = (a (n - 5) : ℚ) := by rw [u_a]
  have u6 : (u (n - 6) 0 : ℚ) = (a (n - 6) : ℚ) := by rw [u_a]
  have u7 : (u (n - 7) 0 : ℚ) = (a (n - 7) : ℚ) := by rw [u_a]
  have u0 : (u n 0 : ℚ) = (a n : ℚ) := by rw [u_a]
  rw [u0, u1, u2, u3, u4, u5, u6, u7, c1, c2, c3, c4, c5, c6, c7] at h
  have goal : 3 * (n : ℚ) * (a n : ℚ) + 3 * (-5 * (n : ℚ) + 3) * (a (n - 1) : ℚ) + (7 * (n : ℚ) - 4) * (a (n - 2) : ℚ) + (25 * (n : ℚ) - 67) * (a (n - 3) : ℚ) + (17 * (n : ℚ) - 44) * (a (n - 4) : ℚ) + (19 * (n : ℚ) - 97) * (a (n - 5) : ℚ) + (5 * (n : ℚ) - 32) * (a (n - 6) : ℚ) + 3 * ((n : ℚ) - 7) * (a (n - 7) : ℚ) = 0 := by
    linear_combination h
  exact_mod_cast goal

/-- Controls: the entry's listed terms, a(0) to a(28). -/
theorem controls :
    a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 5 ∧
    a 4 = 11 ∧ a 5 = 27 ∧ a 6 = 68 ∧ a 7 = 175 ∧
    a 8 = 458 ∧ a 9 = 1215 ∧ a 10 = 3258 ∧ a 11 = 8815 ∧
    a 12 = 24031 ∧ a 13 = 65937 ∧ a 14 = 181936 ∧ a 15 = 504473 ∧
    a 16 = 1404879 ∧ a 17 = 3927495 ∧ a 18 = 11017802 ∧ a 19 = 31004871 ∧
    a 20 = 87497297 ∧ a 21 = 247559933 ∧ a 22 = 702089528 ∧ a 23 = 1995483853 ∧
    a 24 = 5682959332 ∧ a 25 = 16214622573 ∧ a 26 = 46343364290 ∧ a 27 = 132667706857 ∧
    a 28 = 380358924209 := by
  have v0 : a 0 = 1 := by decide +kernel
  have v1 : a 1 = 1 := by decide +kernel
  have v2 : a 2 = 2 := by decide +kernel
  have v3 : a 3 = 5 := by decide +kernel
  have v4 : a 4 = 11 := by decide +kernel
  have v5 : a 5 = 27 := by decide +kernel
  have v6 : a 6 = 68 := by decide +kernel
  have v7 : a 7 = 175 := by
    have h := recur 7 (by norm_num)
    rw [show (7 : ℕ) - 1 = 6 from rfl, show (7 : ℕ) - 2 = 5 from rfl, show (7 : ℕ) - 3 = 4 from rfl, show (7 : ℕ) - 4 = 3 from rfl, show (7 : ℕ) - 5 = 2 from rfl, show (7 : ℕ) - 6 = 1 from rfl, show (7 : ℕ) - 7 = 0 from rfl, v6, v5, v4, v3, v2, v1, v0] at h
    generalize a 7 = x at h ⊢
    push_cast at h
    omega
  have v8 : a 8 = 458 := by
    have h := recur 8 (by norm_num)
    rw [show (8 : ℕ) - 1 = 7 from rfl, show (8 : ℕ) - 2 = 6 from rfl, show (8 : ℕ) - 3 = 5 from rfl, show (8 : ℕ) - 4 = 4 from rfl, show (8 : ℕ) - 5 = 3 from rfl, show (8 : ℕ) - 6 = 2 from rfl, show (8 : ℕ) - 7 = 1 from rfl, v7, v6, v5, v4, v3, v2, v1] at h
    generalize a 8 = x at h ⊢
    push_cast at h
    omega
  have v9 : a 9 = 1215 := by
    have h := recur 9 (by norm_num)
    rw [show (9 : ℕ) - 1 = 8 from rfl, show (9 : ℕ) - 2 = 7 from rfl, show (9 : ℕ) - 3 = 6 from rfl, show (9 : ℕ) - 4 = 5 from rfl, show (9 : ℕ) - 5 = 4 from rfl, show (9 : ℕ) - 6 = 3 from rfl, show (9 : ℕ) - 7 = 2 from rfl, v8, v7, v6, v5, v4, v3, v2] at h
    generalize a 9 = x at h ⊢
    push_cast at h
    omega
  have v10 : a 10 = 3258 := by
    have h := recur 10 (by norm_num)
    rw [show (10 : ℕ) - 1 = 9 from rfl, show (10 : ℕ) - 2 = 8 from rfl, show (10 : ℕ) - 3 = 7 from rfl, show (10 : ℕ) - 4 = 6 from rfl, show (10 : ℕ) - 5 = 5 from rfl, show (10 : ℕ) - 6 = 4 from rfl, show (10 : ℕ) - 7 = 3 from rfl, v9, v8, v7, v6, v5, v4, v3] at h
    generalize a 10 = x at h ⊢
    push_cast at h
    omega
  have v11 : a 11 = 8815 := by
    have h := recur 11 (by norm_num)
    rw [show (11 : ℕ) - 1 = 10 from rfl, show (11 : ℕ) - 2 = 9 from rfl, show (11 : ℕ) - 3 = 8 from rfl, show (11 : ℕ) - 4 = 7 from rfl, show (11 : ℕ) - 5 = 6 from rfl, show (11 : ℕ) - 6 = 5 from rfl, show (11 : ℕ) - 7 = 4 from rfl, v10, v9, v8, v7, v6, v5, v4] at h
    generalize a 11 = x at h ⊢
    push_cast at h
    omega
  have v12 : a 12 = 24031 := by
    have h := recur 12 (by norm_num)
    rw [show (12 : ℕ) - 1 = 11 from rfl, show (12 : ℕ) - 2 = 10 from rfl, show (12 : ℕ) - 3 = 9 from rfl, show (12 : ℕ) - 4 = 8 from rfl, show (12 : ℕ) - 5 = 7 from rfl, show (12 : ℕ) - 6 = 6 from rfl, show (12 : ℕ) - 7 = 5 from rfl, v11, v10, v9, v8, v7, v6, v5] at h
    generalize a 12 = x at h ⊢
    push_cast at h
    omega
  have v13 : a 13 = 65937 := by
    have h := recur 13 (by norm_num)
    rw [show (13 : ℕ) - 1 = 12 from rfl, show (13 : ℕ) - 2 = 11 from rfl, show (13 : ℕ) - 3 = 10 from rfl, show (13 : ℕ) - 4 = 9 from rfl, show (13 : ℕ) - 5 = 8 from rfl, show (13 : ℕ) - 6 = 7 from rfl, show (13 : ℕ) - 7 = 6 from rfl, v12, v11, v10, v9, v8, v7, v6] at h
    generalize a 13 = x at h ⊢
    push_cast at h
    omega
  have v14 : a 14 = 181936 := by
    have h := recur 14 (by norm_num)
    rw [show (14 : ℕ) - 1 = 13 from rfl, show (14 : ℕ) - 2 = 12 from rfl, show (14 : ℕ) - 3 = 11 from rfl, show (14 : ℕ) - 4 = 10 from rfl, show (14 : ℕ) - 5 = 9 from rfl, show (14 : ℕ) - 6 = 8 from rfl, show (14 : ℕ) - 7 = 7 from rfl, v13, v12, v11, v10, v9, v8, v7] at h
    generalize a 14 = x at h ⊢
    push_cast at h
    omega
  have v15 : a 15 = 504473 := by
    have h := recur 15 (by norm_num)
    rw [show (15 : ℕ) - 1 = 14 from rfl, show (15 : ℕ) - 2 = 13 from rfl, show (15 : ℕ) - 3 = 12 from rfl, show (15 : ℕ) - 4 = 11 from rfl, show (15 : ℕ) - 5 = 10 from rfl, show (15 : ℕ) - 6 = 9 from rfl, show (15 : ℕ) - 7 = 8 from rfl, v14, v13, v12, v11, v10, v9, v8] at h
    generalize a 15 = x at h ⊢
    push_cast at h
    omega
  have v16 : a 16 = 1404879 := by
    have h := recur 16 (by norm_num)
    rw [show (16 : ℕ) - 1 = 15 from rfl, show (16 : ℕ) - 2 = 14 from rfl, show (16 : ℕ) - 3 = 13 from rfl, show (16 : ℕ) - 4 = 12 from rfl, show (16 : ℕ) - 5 = 11 from rfl, show (16 : ℕ) - 6 = 10 from rfl, show (16 : ℕ) - 7 = 9 from rfl, v15, v14, v13, v12, v11, v10, v9] at h
    generalize a 16 = x at h ⊢
    push_cast at h
    omega
  have v17 : a 17 = 3927495 := by
    have h := recur 17 (by norm_num)
    rw [show (17 : ℕ) - 1 = 16 from rfl, show (17 : ℕ) - 2 = 15 from rfl, show (17 : ℕ) - 3 = 14 from rfl, show (17 : ℕ) - 4 = 13 from rfl, show (17 : ℕ) - 5 = 12 from rfl, show (17 : ℕ) - 6 = 11 from rfl, show (17 : ℕ) - 7 = 10 from rfl, v16, v15, v14, v13, v12, v11, v10] at h
    generalize a 17 = x at h ⊢
    push_cast at h
    omega
  have v18 : a 18 = 11017802 := by
    have h := recur 18 (by norm_num)
    rw [show (18 : ℕ) - 1 = 17 from rfl, show (18 : ℕ) - 2 = 16 from rfl, show (18 : ℕ) - 3 = 15 from rfl, show (18 : ℕ) - 4 = 14 from rfl, show (18 : ℕ) - 5 = 13 from rfl, show (18 : ℕ) - 6 = 12 from rfl, show (18 : ℕ) - 7 = 11 from rfl, v17, v16, v15, v14, v13, v12, v11] at h
    generalize a 18 = x at h ⊢
    push_cast at h
    omega
  have v19 : a 19 = 31004871 := by
    have h := recur 19 (by norm_num)
    rw [show (19 : ℕ) - 1 = 18 from rfl, show (19 : ℕ) - 2 = 17 from rfl, show (19 : ℕ) - 3 = 16 from rfl, show (19 : ℕ) - 4 = 15 from rfl, show (19 : ℕ) - 5 = 14 from rfl, show (19 : ℕ) - 6 = 13 from rfl, show (19 : ℕ) - 7 = 12 from rfl, v18, v17, v16, v15, v14, v13, v12] at h
    generalize a 19 = x at h ⊢
    push_cast at h
    omega
  have v20 : a 20 = 87497297 := by
    have h := recur 20 (by norm_num)
    rw [show (20 : ℕ) - 1 = 19 from rfl, show (20 : ℕ) - 2 = 18 from rfl, show (20 : ℕ) - 3 = 17 from rfl, show (20 : ℕ) - 4 = 16 from rfl, show (20 : ℕ) - 5 = 15 from rfl, show (20 : ℕ) - 6 = 14 from rfl, show (20 : ℕ) - 7 = 13 from rfl, v19, v18, v17, v16, v15, v14, v13] at h
    generalize a 20 = x at h ⊢
    push_cast at h
    omega
  have v21 : a 21 = 247559933 := by
    have h := recur 21 (by norm_num)
    rw [show (21 : ℕ) - 1 = 20 from rfl, show (21 : ℕ) - 2 = 19 from rfl, show (21 : ℕ) - 3 = 18 from rfl, show (21 : ℕ) - 4 = 17 from rfl, show (21 : ℕ) - 5 = 16 from rfl, show (21 : ℕ) - 6 = 15 from rfl, show (21 : ℕ) - 7 = 14 from rfl, v20, v19, v18, v17, v16, v15, v14] at h
    generalize a 21 = x at h ⊢
    push_cast at h
    omega
  have v22 : a 22 = 702089528 := by
    have h := recur 22 (by norm_num)
    rw [show (22 : ℕ) - 1 = 21 from rfl, show (22 : ℕ) - 2 = 20 from rfl, show (22 : ℕ) - 3 = 19 from rfl, show (22 : ℕ) - 4 = 18 from rfl, show (22 : ℕ) - 5 = 17 from rfl, show (22 : ℕ) - 6 = 16 from rfl, show (22 : ℕ) - 7 = 15 from rfl, v21, v20, v19, v18, v17, v16, v15] at h
    generalize a 22 = x at h ⊢
    push_cast at h
    omega
  have v23 : a 23 = 1995483853 := by
    have h := recur 23 (by norm_num)
    rw [show (23 : ℕ) - 1 = 22 from rfl, show (23 : ℕ) - 2 = 21 from rfl, show (23 : ℕ) - 3 = 20 from rfl, show (23 : ℕ) - 4 = 19 from rfl, show (23 : ℕ) - 5 = 18 from rfl, show (23 : ℕ) - 6 = 17 from rfl, show (23 : ℕ) - 7 = 16 from rfl, v22, v21, v20, v19, v18, v17, v16] at h
    generalize a 23 = x at h ⊢
    push_cast at h
    omega
  have v24 : a 24 = 5682959332 := by
    have h := recur 24 (by norm_num)
    rw [show (24 : ℕ) - 1 = 23 from rfl, show (24 : ℕ) - 2 = 22 from rfl, show (24 : ℕ) - 3 = 21 from rfl, show (24 : ℕ) - 4 = 20 from rfl, show (24 : ℕ) - 5 = 19 from rfl, show (24 : ℕ) - 6 = 18 from rfl, show (24 : ℕ) - 7 = 17 from rfl, v23, v22, v21, v20, v19, v18, v17] at h
    generalize a 24 = x at h ⊢
    push_cast at h
    omega
  have v25 : a 25 = 16214622573 := by
    have h := recur 25 (by norm_num)
    rw [show (25 : ℕ) - 1 = 24 from rfl, show (25 : ℕ) - 2 = 23 from rfl, show (25 : ℕ) - 3 = 22 from rfl, show (25 : ℕ) - 4 = 21 from rfl, show (25 : ℕ) - 5 = 20 from rfl, show (25 : ℕ) - 6 = 19 from rfl, show (25 : ℕ) - 7 = 18 from rfl, v24, v23, v22, v21, v20, v19, v18] at h
    generalize a 25 = x at h ⊢
    push_cast at h
    omega
  have v26 : a 26 = 46343364290 := by
    have h := recur 26 (by norm_num)
    rw [show (26 : ℕ) - 1 = 25 from rfl, show (26 : ℕ) - 2 = 24 from rfl, show (26 : ℕ) - 3 = 23 from rfl, show (26 : ℕ) - 4 = 22 from rfl, show (26 : ℕ) - 5 = 21 from rfl, show (26 : ℕ) - 6 = 20 from rfl, show (26 : ℕ) - 7 = 19 from rfl, v25, v24, v23, v22, v21, v20, v19] at h
    generalize a 26 = x at h ⊢
    push_cast at h
    omega
  have v27 : a 27 = 132667706857 := by
    have h := recur 27 (by norm_num)
    rw [show (27 : ℕ) - 1 = 26 from rfl, show (27 : ℕ) - 2 = 25 from rfl, show (27 : ℕ) - 3 = 24 from rfl, show (27 : ℕ) - 4 = 23 from rfl, show (27 : ℕ) - 5 = 22 from rfl, show (27 : ℕ) - 6 = 21 from rfl, show (27 : ℕ) - 7 = 20 from rfl, v26, v25, v24, v23, v22, v21, v20] at h
    generalize a 27 = x at h ⊢
    push_cast at h
    omega
  have v28 : a 28 = 380358924209 := by
    have h := recur 28 (by norm_num)
    rw [show (28 : ℕ) - 1 = 27 from rfl, show (28 : ℕ) - 2 = 26 from rfl, show (28 : ℕ) - 3 = 25 from rfl, show (28 : ℕ) - 4 = 24 from rfl, show (28 : ℕ) - 5 = 23 from rfl, show (28 : ℕ) - 6 = 22 from rfl, show (28 : ℕ) - 7 = 21 from rfl, v27, v26, v25, v24, v23, v22, v21] at h
    generalize a 28 = x at h ⊢
    push_cast at h
    omega
  exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28⟩

/-- Mathar's conjecture. -/
theorem conjecture : ∀ n : ℕ, 7 ≤ n →
      3 * (n : ℤ) * (a n : ℤ) + 3 * (-5 * (n : ℤ) + 3) * (a (n - 1) : ℤ) + (7 * (n : ℤ) - 4) * (a (n - 2) : ℤ) + (25 * (n : ℤ) - 67) * (a (n - 3) : ℤ) + (17 * (n : ℤ) - 44) * (a (n - 4) : ℤ) + (19 * (n : ℤ) - 97) * (a (n - 5) : ℤ) + (5 * (n : ℤ) - 32) * (a (n - 6) : ℤ) + 3 * ((n : ℤ) - 7) * (a (n - 7) : ℤ) = 0 :=
  recur

end OMA.S_oeis_a027087

theorem OMA.solution : type_of% @OMA.S_oeis_a027087.main :=
  OMA.S_oeis_a027087.conjecture
