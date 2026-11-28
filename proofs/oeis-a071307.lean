import OMAStatements.S_oeis_a071307
import Mathlib

-- Problem: OEIS A071307, conjecture of Marcus: the number of n X n matrices M over Z/9 with
-- M M' = I is 3^(n(n-1)/2) times the number of such matrices over Z/3 (both halved).
-- Statement: statements/oeis-a071307.lean (declaration OMA.S_oeis_a071307.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let red : Z/9 -> Z/3 be the reduction and tau : Z/3 -> Z/9 the additive injection
-- y -> 3 y, with z tau(y) = tau(red(z) y) and tau(x) tau(y) = 0. For N over Z/3 with
-- N N' = I, let L be its entrywise lift. Then L L' = I + 3 S with S symmetric. For a matrix W
-- over Z/3, G = L + 3 W N satisfies G G' = I + 3 (S + W' + W). With W = S + Y and Y
-- antisymmetric this is I + 9 S = I. The map (N, Y) -> L + 3 (S + Y) N is a bijection from
-- pairs (orthogonal N, antisymmetric Y) to the orthogonal matrices over Z/9: reduction gives
-- back N, the factor 3 is injective, and N is invertible; each orthogonal M over Z/9 is
-- L + 3 X with X = W N, and M M' = I gives S + W' + W = 0, so W - S is antisymmetric.
-- Antisymmetric matrices over Z/3 have zero diagonal and are functions on the n(n-1)/2
-- pairs i < j. The count over Z/3 is even for n >= 1 (the involution M -> -M has no fixed
-- point), so the halves agree too.

namespace OMA.A071307

open OMA.S_oeis_a071307 Matrix

/-- Reduction modulo 3. -/
def red : ZMod 9 →+* ZMod 3 := ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)

/-- The standard lift of a residue modulo 3. -/
def lift (x : ZMod 3) : ZMod 9 := (x.val : ZMod 9)

/-- Multiplication by 3, as a map from Z/3 to Z/9. -/
def tau (x : ZMod 3) : ZMod 9 := 3 * lift x

/-- Division by 3 of the standard representative. -/
def sig (z : ZMod 9) : ZMod 3 := ((z.val / 3 : ℕ) : ZMod 3)

lemma red_lift : ∀ x : ZMod 3, red (lift x) = x := by decide
lemma tau_add : ∀ x y : ZMod 3, tau (x + y) = tau x + tau y := by decide
lemma tau_inj : ∀ x y : ZMod 3, tau x = tau y → x = y := by decide
lemma tau_sig : ∀ z : ZMod 9, red z = 0 → tau (sig z) = z := by decide
lemma mul_tau : ∀ (z : ZMod 9) (y : ZMod 3), z * tau y = tau (red z * y) := by decide
lemma tau_mul_tau : ∀ x y : ZMod 3, tau x * tau y = 0 := by decide
lemma red_tau : ∀ y : ZMod 3, red (tau y) = 0 := by decide
lemma three_zero : ∀ x : ZMod 3, x + x + x = 0 := by decide
lemma eq_neg_zero : ∀ x : ZMod 3, x = -x → x = 0 := by decide

/-- tau as an additive homomorphism. -/
def tauh : ZMod 3 →+ ZMod 9 := AddMonoidHom.mk' tau tau_add

variable {n : ℕ}

/-- Reduction of a matrix. -/
def P (M : Matrix (Fin n) (Fin n) (ZMod 9)) : Matrix (Fin n) (Fin n) (ZMod 3) := M.map red

/-- Multiplication of a matrix by 3. -/
def T (X : Matrix (Fin n) (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 9) := X.map tau

lemma P_mul (M M' : Matrix (Fin n) (Fin n) (ZMod 9)) : P (M * M') = P M * P M' := by
  ext i j
  simp [P, Matrix.mul_apply, map_sum]

lemma P_add (M M' : Matrix (Fin n) (Fin n) (ZMod 9)) : P (M + M') = P M + P M' := by
  ext i j
  simp [P]

lemma P_sub (M M' : Matrix (Fin n) (Fin n) (ZMod 9)) : P (M - M') = P M - P M' := by
  ext i j
  simp [P]

lemma P_one : P (1 : Matrix (Fin n) (Fin n) (ZMod 9)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [P, Matrix.one_apply, h]

lemma P_transpose (M : Matrix (Fin n) (Fin n) (ZMod 9)) : P Mᵀ = (P M)ᵀ := by
  ext i j
  simp [P]

lemma P_T (X : Matrix (Fin n) (Fin n) (ZMod 3)) : P (T X) = 0 := by
  ext i j
  simp [P, T, red_tau]

lemma T_add (X Y : Matrix (Fin n) (Fin n) (ZMod 3)) : T (X + Y) = T X + T Y := by
  ext i j
  simp [T, tau_add]

lemma T_zero : T (0 : Matrix (Fin n) (Fin n) (ZMod 3)) = 0 := by
  ext i j
  simp [T]
  decide

lemma T_inj (X Y : Matrix (Fin n) (Fin n) (ZMod 3)) (h : T X = T Y) : X = Y := by
  ext i j
  apply tau_inj
  have := congrFun (congrFun h i) j
  simpa [T] using this

lemma T_transpose (X : Matrix (Fin n) (Fin n) (ZMod 3)) : T Xᵀ = (T X)ᵀ := by
  ext i j
  simp [T]

lemma tau_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 3) :
    tau (∑ k ∈ s, f k) = ∑ k ∈ s, tau (f k) := map_sum tauh f s

lemma mul_T (M : Matrix (Fin n) (Fin n) (ZMod 9)) (X : Matrix (Fin n) (Fin n) (ZMod 3)) :
    M * T X = T (P M * X) := by
  ext i j
  simp only [T, P, Matrix.mul_apply, Matrix.map_apply, tau_sum]
  exact Finset.sum_congr rfl (fun k _ => mul_tau _ _)

lemma T_mul (X : Matrix (Fin n) (Fin n) (ZMod 3)) (M : Matrix (Fin n) (Fin n) (ZMod 9)) :
    T X * M = T (X * P M) := by
  ext i j
  simp only [T, P, Matrix.mul_apply, Matrix.map_apply, tau_sum]
  exact Finset.sum_congr rfl (fun k _ => by rw [mul_comm, mul_tau, mul_comm])

lemma T_mul_T (X Y : Matrix (Fin n) (Fin n) (ZMod 3)) : T X * T Y = 0 := by
  ext i j
  simp only [T, Matrix.mul_apply, Matrix.map_apply, tau_mul_tau, Finset.sum_const_zero]
  rfl

lemma T_sig (Z : Matrix (Fin n) (Fin n) (ZMod 9)) (h : P Z = 0) : T (Z.map sig) = Z := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [P, Matrix.map_apply] at this
  simp only [T, Matrix.map_apply]
  exact tau_sig _ this

/-- The entrywise standard lift of a matrix. -/
def L (N : Matrix (Fin n) (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 9) := N.map lift

lemma P_L (N : Matrix (Fin n) (Fin n) (ZMod 3)) : P (L N) = N := by
  ext i j
  simp [P, L, red_lift]

/-- The defect of the lift: L N * (L N)' = 1 + 3 S. -/
def S (N : Matrix (Fin n) (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3) :=
  (L N * (L N)ᵀ - 1).map sig

lemma S_spec (N : Matrix (Fin n) (Fin n) (ZMod 3)) (hN : N * Nᵀ = 1) :
    T (S N) = L N * (L N)ᵀ - 1 := by
  apply T_sig
  rw [P_sub, P_mul, P_transpose, P_L, P_one, hN, sub_self]

lemma S_symm (N : Matrix (Fin n) (Fin n) (ZMod 3)) (hN : N * Nᵀ = 1) : (S N)ᵀ = S N := by
  apply T_inj
  rw [T_transpose, S_spec N hN, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_one]

/-- The lift of N, moved by 3 W N. -/
def G (N W : Matrix (Fin n) (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 9) :=
  L N + T (W * N)

lemma P_G (N W : Matrix (Fin n) (Fin n) (ZMod 3)) : P (G N W) = N := by
  rw [G, P_add, P_L, P_T, add_zero]

lemma G_mul (N W : Matrix (Fin n) (Fin n) (ZMod 3)) (hN : N * Nᵀ = 1) :
    G N W * (G N W)ᵀ = 1 + T (S N + Wᵀ + W) := by
  have hN' : Nᵀ * N = 1 := mul_eq_one_comm.mp hN
  have e1 : L N * (L N)ᵀ = 1 + T (S N) := by rw [S_spec N hN]; abel
  have e2 : L N * (T (W * N))ᵀ = T Wᵀ := by
    rw [← T_transpose, mul_T, P_L, Matrix.transpose_mul, ← Matrix.mul_assoc, hN, Matrix.one_mul]
  have e3 : T (W * N) * (L N)ᵀ = T W := by
    rw [T_mul, P_transpose, P_L, Matrix.mul_assoc, hN, Matrix.mul_one]
  have e4 : T (W * N) * (T (W * N))ᵀ = 0 := by rw [← T_transpose, T_mul_T]
  rw [G, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, e1, e2, e3, e4,
    T_add, T_add]
  abel

lemma three_zero_mat (X : Matrix (Fin n) (Fin n) (ZMod 3)) : X + X + X = 0 := by
  ext i j
  simp [three_zero]

/-- The three finite sets. -/
def O9 (n : ℕ) : Finset (Matrix (Fin n) (Fin n) (ZMod 9)) :=
  Finset.univ.filter (fun M => M * Mᵀ = 1)

def O3 (n : ℕ) : Finset (Matrix (Fin n) (Fin n) (ZMod 3)) :=
  Finset.univ.filter (fun M => M * Mᵀ = 1)

def A (n : ℕ) : Finset (Matrix (Fin n) (Fin n) (ZMod 3)) :=
  Finset.univ.filter (fun Y => Yᵀ = -Y)

lemma card_O9 (n : ℕ) : (O9 n).card = (O3 n).card * (A n).card := by
  rw [← Finset.card_product]
  symm
  apply Finset.card_bij (fun p _ => G p.1 (S p.1 + p.2))
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    have hN : p.1 * p.1ᵀ = 1 := (Finset.mem_filter.mp h1).2
    have hY : p.2ᵀ = -p.2 := (Finset.mem_filter.mp h2).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [G_mul _ _ hN, Matrix.transpose_add, S_symm _ hN, hY]
    have : S p.1 + (S p.1 + -p.2) + (S p.1 + p.2) = 0 := by
      rw [← three_zero_mat (S p.1)]; abel
    rw [this, T_zero, add_zero]
  · intro p hp q hq heq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    have hN : p.1 * p.1ᵀ = 1 := (Finset.mem_filter.mp h1).2
    have e1 : p.1 = q.1 := by
      have := congrArg P heq
      rwa [P_G, P_G] at this
    obtain ⟨N, Y⟩ := p
    obtain ⟨N', Y'⟩ := q
    simp only at e1 hN heq
    subst e1
    have e2 : (S N + Y) * N = (S N + Y') * N := by
      apply T_inj
      exact add_left_cancel (a := L N) heq
    have e3 := congrArg (fun X => X * Nᵀ) e2
    simp only [Matrix.mul_assoc, hN, Matrix.mul_one] at e3
    rw [add_left_cancel e3]
  · intro M hM
    have hMM : M * Mᵀ = 1 := (Finset.mem_filter.mp hM).2
    have hN : P M * (P M)ᵀ = 1 := by rw [← P_transpose, ← P_mul, hMM, P_one]
    have hN' : (P M)ᵀ * P M = 1 := mul_eq_one_comm.mp hN
    have hZ : P (M - L (P M)) = 0 := by rw [P_sub, P_L, sub_self]
    have hX := T_sig _ hZ
    set X := (M - L (P M)).map sig with hXdef
    have hG : G (P M) (X * (P M)ᵀ) = M := by
      rw [G, Matrix.mul_assoc, hN', Matrix.mul_one, hX]
      abel
    have hrel : S (P M) + (X * (P M)ᵀ)ᵀ + X * (P M)ᵀ = 0 := by
      apply T_inj
      have := G_mul (P M) (X * (P M)ᵀ) hN
      rw [hG, hMM] at this
      rw [T_zero]
      exact (add_left_cancel (a := (1 : Matrix (Fin n) (Fin n) (ZMod 9)))
        (by rw [add_zero]; exact this)).symm
    refine ⟨(P M, X * (P M)ᵀ - S (P M)), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      show (X * (P M)ᵀ - S (P M))ᵀ = -(X * (P M)ᵀ - S (P M))
      rw [Matrix.transpose_sub, S_symm _ hN]
      have h3 := three_zero_mat (S (P M))
      have : (X * (P M)ᵀ)ᵀ = -(S (P M)) - X * (P M)ᵀ := by
        rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero]
        rw [← hrel]; abel
      rw [this]
      have : -(S (P M)) - X * (P M)ᵀ - S (P M) + (X * (P M)ᵀ - S (P M))
          = -(S (P M) + S (P M) + S (P M)) := by abel
      rw [← add_eq_zero_iff_eq_neg, this, h3, neg_zero]
    · show G (P M) (S (P M) + (X * (P M)ᵀ - S (P M))) = M
      rw [show S (P M) + (X * (P M)ᵀ - S (P M)) = X * (P M)ᵀ by abel, hG]

/-- The number of pairs i < j. -/
lemma card_pairs (n : ℕ) :
    Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i < j then 1 else 0) = n - 1 - (i : ℕ) := by
    intro i
    rw [← Finset.card_filter, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n,
    Finset.sum_range_reflect (fun i => i) n]
  have := Finset.sum_range_id_mul_two n
  omega

/-- Antisymmetric matrices over Z/3 are functions on the pairs i < j. -/
def antiEquiv (n : ℕ) : {Y : Matrix (Fin n) (Fin n) (ZMod 3) // Yᵀ = -Y} ≃
    ({p : Fin n × Fin n // p.1 < p.2} → ZMod 3) where
  toFun Y := fun p => Y.1 p.1.1 p.1.2
  invFun f := ⟨Matrix.of (fun i j => if h : i < j then f ⟨(i, j), h⟩
      else if h' : j < i then -f ⟨(j, i), h'⟩ else 0), by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [dif_neg (not_lt.mpr h.le), dif_pos h, dif_pos h]
    · subst h
      simp
    · rw [dif_pos h, dif_neg (not_lt.mpr h.le), dif_pos h, neg_neg]⟩
  left_inv := by
    rintro ⟨Y, hY⟩
    apply Subtype.ext
    ext i j
    have hji : Y j i = -Y i j := by
      have := congrFun (congrFun hY i) j
      simpa using this
    simp only [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [dif_pos h]
    · subst h
      rw [dif_neg (lt_irrefl _), dif_neg (lt_irrefl _)]
      exact (eq_neg_zero _ hji).symm
    · rw [dif_neg (not_lt.mpr h.le), dif_pos h]
      have := congrFun (congrFun hY j) i
      simp at this
      rw [this]
  right_inv := by
    intro f
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    simp only [Matrix.of_apply]
    rw [dif_pos h]

lemma card_A (n : ℕ) : (A n).card = 3 ^ (n * (n - 1) / 2) := by
  have h1 : (A n).card = Fintype.card {Y : Matrix (Fin n) (Fin n) (ZMod 3) // Yᵀ = -Y} := by
    rw [Fintype.card_subtype]; rfl
  rw [h1, Fintype.card_congr (antiEquiv n), Fintype.card_fun, ZMod.card, card_pairs]

/-- The count over Z/3 is even for n >= 1: M -> -M is an involution without fixed points. -/
lemma even_O3 (n : ℕ) (hn : 1 ≤ n) : 2 ∣ (O3 n).card := by
  have hsum : ∑ _M ∈ O3 n, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun M _ => -M) (fun M _ => by decide) ?_ ?_
      (fun M _ => neg_neg M)
    · intro M hM _ heq
      have hMM : M * Mᵀ = 1 := (Finset.mem_filter.mp hM).2
      have h0 : M = 0 := by
        ext i j
        exact eq_neg_zero _ (congrFun (congrFun heq i) j).symm
      rw [h0, Matrix.zero_mul] at hMM
      have := congrFun (congrFun hMM ⟨0, by omega⟩) ⟨0, by omega⟩
      simp at this
    · intro M hM
      have hMM : M * Mᵀ = 1 := (Finset.mem_filter.mp hM).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [Matrix.transpose_neg, neg_mul_neg, hMM]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact (ZMod.natCast_eq_zero_iff _ _).mp hsum

theorem main' : ∀ n : ℕ, 1 ≤ n → a n = 3 ^ (n * (n - 1) / 2) * b n := by
  intro n hn
  have h9 : Fintype.card {M : Matrix (Fin n) (Fin n) (ZMod 9) // M * M.transpose = 1}
      = (O9 n).card := by rw [Fintype.card_subtype]; rfl
  have h3 : Fintype.card {M : Matrix (Fin n) (Fin n) (ZMod 3) // M * M.transpose = 1}
      = (O3 n).card := by rw [Fintype.card_subtype]; rfl
  unfold a b
  rw [h9, h3, card_O9, card_A]
  obtain ⟨k, hk⟩ := even_O3 n hn
  rw [hk, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num),
    Nat.mul_div_cancel_left _ (by norm_num), mul_comm]

end OMA.A071307

theorem OMA.solution : type_of% @OMA.S_oeis_a071307.main :=
  OMA.A071307.main'
